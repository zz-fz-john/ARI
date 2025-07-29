// Gabriel Waltrip
// Rover.cpp : Defines the entry point for the console application.
// gcc -o rover.out -lwiringPi -lm -pthread rover.c Compass.h gps.h
#include <stdio.h>
//#include <wiringPi.h>
//#include <pthread.h>
#include "tcp.h"
#include "lib/util.h"
//#include "cfv_bellman.h"

#define MOTOR_RIGHT_A	0
#define MOTOR_RIGHT_B	2
#define MOTOR_LEFT_A	3
#define MOTOR_LEFT_B	4
enum{PUSH,PULL}; //syringe movement direction
enum{MAIN, BOLUS_MENU}; //UI states

enum{INPUT, OUTPUT}; //GPIO directions
enum{HIGH, LOW}; //GPIO states
#define Stop_All_Motors()	digitalWrite(MOTOR_RIGHT_A,0);\
				digitalWrite(MOTOR_RIGHT_B,0);\
				digitalWrite(MOTOR_LEFT_A,0);\
				digitalWrite(MOTOR_LEFT_B,0);
extern void create_files(const char* filename1, const char* filename2, const char* filename3,\
	const char* filename4, const char* filename5);//ari need
int main(int argc, char **argv)
{
	mode = 0xff;
	char __attribute__((annotate("sensitive"))) last = mode;
    int count = 0;
    unsigned long start, end;
	create_files("./ARI_branch.txt", "./ARI_ind_jmp.txt", "./ARI_ret_hash.txt", \
	"./ARI_tsf.txt", "./ARI_tsf_cond.txt");
	printf("What port do you want to open?\n");
	scanf("%d",&portno);

	//pthread_t tcp;
	//pthread_create(&tcp, NULL,tcpListener,"");

	//wiringPiSetup();
	pinMode(MOTOR_LEFT_A,OUTPUT);
	pinMode(MOTOR_LEFT_B,OUTPUT);
	pinMode(MOTOR_RIGHT_A,OUTPUT);
	pinMode(MOTOR_RIGHT_B,OUTPUT);
	/*Starts Main Loop*/
	printf("Starting Mainloop!\n");
    start = usecs();
    //cfv_init(1024);
    
       printf("%s %d\n",__func__, __LINE__);
	while (count++ < 1) {
       printf("%s %d\n",__func__, __LINE__);
		tcpListener(NULL);
       printf("%s %d\n",__func__, __LINE__);
		if(last == mode){
			Stop_All_Motors();
			last = mode;
		}
		//Fordward
		else
		if(mode == 0x1+'0'){
			printf("Forward\n");
			digitalWrite(MOTOR_RIGHT_A,1);
			digitalWrite(MOTOR_LEFT_A,1);
		}
		//Backwards
		else if(mode == 0x2 + '0'){
			printf("Backward\n");
			digitalWrite(MOTOR_RIGHT_B,1);
			digitalWrite(MOTOR_LEFT_B,1);
		}
		//Left
		else if (mode == 0x3 + '0'){
			printf("Left\n");
			digitalWrite(MOTOR_RIGHT_A,1);
			digitalWrite(MOTOR_LEFT_B,1);
		}
		//Right
		else if (mode == 0x4 + '0'){
			printf("Right\n");
			digitalWrite(MOTOR_RIGHT_B,1);
			digitalWrite(MOTOR_LEFT_A,1);
		}
		//delay(500);
		usleep(500 * 1000);
	}
    //cfv_quote();
    end = usecs();
    printf("round with attestation time usecs: %lu\n", end - start);

	Stop_All_Motors();
	return 0;
}
