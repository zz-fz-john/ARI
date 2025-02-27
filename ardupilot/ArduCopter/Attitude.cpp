#include "Copter.h"
#include <time.h>
#include <chrono>

namespace {

unsigned long long update_throttle_hover_total = 0;
unsigned long long update_throttle_hover_count = 0;
std::chrono::high_resolution_clock::time_point update_throttle_hover_t1;
std::chrono::high_resolution_clock::time_point update_throttle_hover_t2;

}

// get_pilot_desired_heading - transform pilot's yaw input into a
// desired yaw rate
// returns desired yaw rate in centi-degrees per second
float Copter::get_pilot_desired_yaw_rate(int16_t stick_angle)
{
    float yaw_request;

    // calculate yaw rate request
    if (g2.acro_y_expo <= 0) {
        yaw_request = stick_angle * g.acro_yaw_p;
    } else {
        // expo variables
        float y_in, y_in3, y_out;

        // range check expo
        if (g2.acro_y_expo > 1.0f || g2.acro_y_expo < 0.5f) {
            g2.acro_y_expo = 1.0f;
        }

        // yaw expo
        y_in = float(stick_angle)/ROLL_PITCH_YAW_INPUT_MAX;
        y_in3 = y_in*y_in*y_in;
        y_out = (g2.acro_y_expo * y_in3) + ((1.0f - g2.acro_y_expo) * y_in);
        yaw_request = ROLL_PITCH_YAW_INPUT_MAX * y_out * g.acro_yaw_p;
    }
    // convert pilot input to the desired yaw rate
    return yaw_request;
}

/*************************************************************
 *  throttle control
 ****************************************************************/

// update estimated throttle required to hover (if necessary)
//  called at 100hz
void Copter::update_throttle_hover()
{

    update_throttle_hover_t1 = std::chrono::high_resolution_clock::now();

#if FRAME_CONFIG != HELI_FRAME
    // if not armed or landed exit
    if (!motors->armed() || ap.land_complete) {
        return;
    }

    // do not update in manual throttle modes or Drift
    if (flightmode->has_manual_throttle() || (control_mode == DRIFT)) {
        return;
    }

    // do not update while climbing or descending
    if (!is_zero(pos_control->get_desired_velocity().z)) {
        return;
    }

    // get throttle output
    float throttle = motors->get_throttle();

    // calc average throttle if we are in a level hover
    if (throttle > 0.0f && abs(climb_rate) < 60 && labs(ahrs.roll_sensor) < 500 && labs(ahrs.pitch_sensor) < 500) {
        // Can we set the time constant automatically
        motors->update_throttle_hover(0.01f);
    }
#endif

    update_throttle_hover_t2 = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(update_throttle_hover_t2 -update_throttle_hover_t1).count();
    update_throttle_hover_total += duration;
    update_throttle_hover_count += 1;
    if (update_throttle_hover_count % 1000 == 0){
        printf("average update_throttle_hover measure time microseconds is %llu!\n",update_throttle_hover_total/1000);
        update_throttle_hover_total = 0;
    }

}

// set_throttle_takeoff - allows parents to tell throttle controller we are taking off so I terms can be cleared
void Copter::set_throttle_takeoff()
{
    // tell position controller to reset alt target and reset I terms
    pos_control->init_takeoff();
}

// transform pilot's manual throttle input to make hover throttle mid stick
// used only for manual throttle modes
// thr_mid should be in the range 0 to 1
// returns throttle output 0 to 1
float Copter::get_pilot_desired_throttle(int16_t throttle_control, float thr_mid)
{
    if (thr_mid <= 0.0f) {
        thr_mid = motors->get_throttle_hover();
    }

    int16_t mid_stick = get_throttle_mid();
    // protect against unlikely divide by zero
    if (mid_stick <= 0) {
        mid_stick = 500;
    }

    // ensure reasonable throttle values
    throttle_control = constrain_int16(throttle_control,0,1000);

    // calculate normalised throttle input
    float throttle_in;
    if (throttle_control < mid_stick) {
        // below the deadband
        throttle_in = ((float)throttle_control)*0.5f/(float)mid_stick;
    }else if(throttle_control > mid_stick) {
        // above the deadband
        throttle_in = 0.5f + ((float)(throttle_control-mid_stick)) * 0.5f / (float)(1000-mid_stick);
    }else{
        // must be in the deadband
        throttle_in = 0.5f;
    }

    float expo = constrain_float(-(thr_mid-0.5)/0.375, -0.5f, 1.0f);
    // calculate the output throttle using the given expo function
    float throttle_out = throttle_in*(1.0f-expo) + expo*throttle_in*throttle_in*throttle_in;
    return throttle_out;
}

// get_pilot_desired_climb_rate - transform pilot's throttle input to climb rate in cm/s
// without any deadzone at the bottom
float Copter::get_pilot_desired_climb_rate(float throttle_control)
{
    // throttle failsafe check
    if( failsafe.radio ) {
        return 0.0f;
    }

#if TOY_MODE_ENABLED == ENABLED
    if (g2.toy_mode.enabled()) {
        // allow throttle to be reduced after throttle arming and for
        // slower descent close to the ground
        g2.toy_mode.throttle_adjust(throttle_control);
    }
#endif
    
    float desired_rate = 0.0f;
    float mid_stick = get_throttle_mid();
    float deadband_top = mid_stick + g.throttle_deadzone;
    float deadband_bottom = mid_stick - g.throttle_deadzone;

    // ensure a reasonable throttle value
    throttle_control = constrain_float(throttle_control,0.0f,1000.0f);

    // ensure a reasonable deadzone
    g.throttle_deadzone = constrain_int16(g.throttle_deadzone, 0, 400);

    // check throttle is above, below or in the deadband
    if (throttle_control < deadband_bottom) {
        // below the deadband
        desired_rate = get_pilot_speed_dn() * (throttle_control-deadband_bottom) / deadband_bottom;
    }else if (throttle_control > deadband_top) {
        // above the deadband
        desired_rate = g.pilot_speed_up * (throttle_control-deadband_top) / (1000.0f-deadband_top);
    }else{
        // must be in the deadband
        desired_rate = 0.0f;
    }

    return desired_rate;
}

// get_non_takeoff_throttle - a throttle somewhere between min and mid throttle which should not lead to a takeoff
float Copter::get_non_takeoff_throttle()
{
    return MAX(0,motors->get_throttle_hover()/2.0f);
}

// get_surface_tracking_climb_rate - hold copter at the desired distance above the ground
//      returns climb rate (in cm/s) which should be passed to the position controller
float Copter::get_surface_tracking_climb_rate(int16_t target_rate, float current_alt_target, float dt)
{
#if RANGEFINDER_ENABLED == ENABLED
    if (!copter.rangefinder_alt_ok()) {
        // if rangefinder is not ok, do not use surface tracking
        return target_rate;
    }

    static uint32_t last_call_ms = 0;
    float distance_error;
    float velocity_correction;
    float current_alt = inertial_nav.get_altitude();

    uint32_t now = millis();

    target_rangefinder_alt_used = true;

    // reset target altitude if this controller has just been engaged
    if (now - last_call_ms > RANGEFINDER_TIMEOUT_MS) {
        target_rangefinder_alt = rangefinder_state.alt_cm + current_alt_target - current_alt;
    }
    last_call_ms = now;

    // adjust rangefinder target alt if motors have not hit their limits
    if ((target_rate<0 && !motors->limit.throttle_lower) || (target_rate>0 && !motors->limit.throttle_upper)) {
        target_rangefinder_alt += target_rate * dt;
    }

    /*
      handle rangefinder glitches. When we get a rangefinder reading
      more than RANGEFINDER_GLITCH_ALT_CM different from the current
      rangefinder reading then we consider it a glitch and reject
      until we get RANGEFINDER_GLITCH_NUM_SAMPLES samples in a
      row. When that happens we reset the target altitude to the new
      reading
     */
    int32_t glitch_cm = rangefinder_state.alt_cm - target_rangefinder_alt;
    if (glitch_cm >= RANGEFINDER_GLITCH_ALT_CM) {
        rangefinder_state.glitch_count = MAX(rangefinder_state.glitch_count+1,1);
    } else if (glitch_cm <= -RANGEFINDER_GLITCH_ALT_CM) {
        rangefinder_state.glitch_count = MIN(rangefinder_state.glitch_count-1,-1);
    } else {
        rangefinder_state.glitch_count = 0;
    }
    if (abs(rangefinder_state.glitch_count) >= RANGEFINDER_GLITCH_NUM_SAMPLES) {
        // shift to the new rangefinder reading
        target_rangefinder_alt = rangefinder_state.alt_cm;
        rangefinder_state.glitch_count = 0;
    }
    if (rangefinder_state.glitch_count != 0) {
        // we are currently glitching, just use the target rate
        return target_rate;
    }

    // calc desired velocity correction from target rangefinder alt vs actual rangefinder alt (remove the error already passed to Altitude controller to avoid oscillations)
    distance_error = (target_rangefinder_alt - rangefinder_state.alt_cm) - (current_alt_target - current_alt);
    velocity_correction = distance_error * g.rangefinder_gain;
    velocity_correction = constrain_float(velocity_correction, -THR_SURFACE_TRACKING_VELZ_MAX, THR_SURFACE_TRACKING_VELZ_MAX);

    // return combined pilot climb rate + rate to correct rangefinder alt error
    return (target_rate + velocity_correction);
#else
    return (float)target_rate;
#endif
}

// get target climb rate reduced to avoid obstacles and altitude fence
float Copter::get_avoidance_adjusted_climbrate(float target_rate)
{
#if AC_AVOID_ENABLED == ENABLED
    avoid.adjust_velocity_z(pos_control->get_pos_z_p().kP(), pos_control->get_accel_z(), target_rate, G_Dt);
    return target_rate;
#else
    return target_rate;
#endif
}

// set_accel_throttle_I_from_pilot_throttle - smoothes transition from pilot controlled throttle to autopilot throttle
void Copter::set_accel_throttle_I_from_pilot_throttle()
{
    // get last throttle input sent to attitude controller
    float pilot_throttle = constrain_float(attitude_control->get_throttle_in(), 0.0f, 1.0f);
    // shift difference between pilot's throttle and hover throttle into accelerometer I
    pos_control->get_accel_z_pid().set_integrator((pilot_throttle-motors->get_throttle_hover()) * 1000.0f);
}

// rotate vector from vehicle's perspective to North-East frame
void Copter::rotate_body_frame_to_NE(float &x, float &y)
{
    float ne_x = x*ahrs.cos_yaw() - y*ahrs.sin_yaw();
    float ne_y = x*ahrs.sin_yaw() + y*ahrs.cos_yaw();
    x = ne_x;
    y = ne_y;
}

// It will return the PILOT_SPEED_DN value if non zero, otherwise if zero it returns the PILOT_SPEED_UP value.
uint16_t Copter::get_pilot_speed_dn()
{
    if (g2.pilot_speed_dn == 0) {
        return abs(g.pilot_speed_up);
    } else {
        return abs(g2.pilot_speed_dn);
    }
}
