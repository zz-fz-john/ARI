; ModuleID = 'after_compartment_test_combo.bc'
source_filename = "llvm-link"
target datalayout = "e-m:e-p:32:32-i64:64-v128:64:128-a:0:32-n32-S64"
target triple = "armv6kz--linux-gnueabihf"

%struct.in_addr = type { i32 }
%struct._IO_FILE = type { i32, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, %struct._IO_marker*, %struct._IO_FILE*, i32, i32, i32, i16, i8, [1 x i8], i8*, i64, i8*, i8*, i8*, i8*, i32, i32, [40 x i8] }
%struct._IO_marker = type { %struct._IO_marker*, %struct._IO_FILE*, i32 }
%struct.timeval = type { i32, i32 }
%struct.sigaction = type { %union.anon, %struct.__sigset_t, i32, void ()* }
%union.anon = type { void (i32)* }
%struct.__sigset_t = type { [32 x i32] }
%struct.sockaddr_in = type { i16, i16, %struct.in_addr, [8 x i8] }
%struct.sockaddr = type { i16, [14 x i8] }
%struct.addrinfo = type { i32, i32, i32, i32, i32, %struct.sockaddr*, i8*, %struct.addrinfo* }
%struct.__res_state = type { i32, i32, i32, i32, [3 x %struct.sockaddr_in], i16, [7 x i8*], [256 x i8], i32, i32, [10 x %struct.anon], i32 (%struct.sockaddr_in**, i8**, i32*, i8*, i32, i32*)*, i32 (%struct.sockaddr_in*, i8*, i32, i8*, i32, i32*)*, i32, i32, i32, %union.anon.9 }
%struct.anon = type { %struct.in_addr, i32 }
%union.anon.9 = type { %struct.anon.0, [8 x i8] }
%struct.anon.0 = type { i16, [3 x i16], [3 x i32], i16, i16, [3 x %struct.sockaddr_in6*], [2 x i32] }
%struct.sockaddr_in6 = type { i16, i16, i32, %struct.in6_addr, i32 }
%struct.in6_addr = type { %union.anon.1 }
%union.anon.1 = type { [4 x i32] }
%union.anon.2 = type { [512 x i8] }
%struct.__ns_msg = type { i8*, i8*, i16, i16, [4 x i16], [4 x i8*], i32, i32, i8* }
%struct.__ns_rr = type { [1025 x i8], i16, i16, i32, i16, i8* }
%struct.itimerval = type { %struct.timeval, %struct.timeval }
%struct.tm = type { i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i8* }
%struct.__va_list = type { i8* }

@Child_process_id = global [2 x i32] [i32 -1, i32 -1], section ".DATA_REGION_2__data", align 4
@Capture_exec_args = constant [7 x i8*] [i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str, i32 0, i32 0), i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.1, i32 0, i32 0), i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.2, i32 0, i32 0), i8* getelementptr inbounds ([5 x i8], [5 x i8]* @.str.3, i32 0, i32 0), i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.4, i32 0, i32 0), i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.4, i32 0, i32 0), i8* null], section ".DATA_REGION_2__data", align 4
@.str = private unnamed_addr constant [3 x i8] c"nc\00", align 1
@.str.1 = private unnamed_addr constant [3 x i8] c"-l\00", align 1
@.str.2 = private unnamed_addr constant [3 x i8] c"-p\00", align 1
@.str.3 = private unnamed_addr constant [5 x i8] c"8080\00", align 1
@.str.4 = private unnamed_addr constant [3 x i8] c"-v\00", align 1
@Web_server_exec_args = constant [7 x i8*] [i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str, i32 0, i32 0), i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.1, i32 0, i32 0), i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.2, i32 0, i32 0), i8* getelementptr inbounds ([5 x i8], [5 x i8]* @.str.5, i32 0, i32 0), i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.4, i32 0, i32 0), i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.4, i32 0, i32 0), i8* null], section ".DATA_REGION_2__data", align 4
@.str.5 = private unnamed_addr constant [5 x i8] c"8008\00", align 1
@Exit_daemon_loop = global i32 0, section ".DATA_REGION_2__bss", align 4
@timer_handler.count = internal global i32 0, section ".DATA_REGION_2__bss", align 4
@.str.6 = private unnamed_addr constant [52 x i8] c"Error setting termination signal handler. errno=%d\0A\00", align 1
@.str.18 = private unnamed_addr constant [54 x i8] c"Signal %i received: Sending TERM signal to children.\0A\00", align 1
@.str.17 = private unnamed_addr constant [24 x i8] c"timer expired %d times\0A\00", align 1
@.str.7 = private unnamed_addr constant [23 x i8] c"iAlarm daemon started.\00", align 1
@.str.8 = private unnamed_addr constant [26 x i8] c"Error creating log files.\00", align 1
@.str.9 = private unnamed_addr constant [16 x i8] c"LD_LIBRARY_PATH\00", align 1
@.str.10 = private unnamed_addr constant [15 x i8] c"/usr/local/lib\00", align 1
@.str.11 = private unnamed_addr constant [64 x i8] c"Error setting envoronment variable for child process. Errno=%i\0A\00", align 1
@.str.12 = private unnamed_addr constant [27 x i8] c"Child process %s executed\0A\00", align 1
@.str.13 = private unnamed_addr constant [23 x i8] c"Server: http://%s:8008\00", align 1
@.str.14 = private unnamed_addr constant [14 x i8] c"main_err: %d\0A\00", align 1
@.str.15 = private unnamed_addr constant [38 x i8] c"Polling thread has not been created.\0A\00", align 1
@.str.16 = private unnamed_addr constant [39 x i8] c"Waiting for child processes to finish\0A\00", align 1
@Msg_info_str = common global [146 x i8] zeroinitializer, section ".DATA_REGION_0__bss", align 1
@recording_flag = global i32 0, section ".DATA_REGION_1__bss", align 4
@recording_cnt = global i32 0, align 4
@Polling_thread_id = common global i32 0, section ".DATA_REGION_2__bss", align 4
@.str.19 = private unnamed_addr constant [7 x i8] c"%s. %s\00", align 1
@.str.1.20 = private unnamed_addr constant [23 x i8] c"Public IP address: %s\0A\00", align 1
@.str.2.21 = private unnamed_addr constant [37 x i8] c"Alarm4pi running. Public IP obtained\00", align 1
@.str.3.22 = private unnamed_addr constant [3 x i8] c"-2\00", align 1
@.str.4.23 = private unnamed_addr constant [10 x i8] c"sensitive\00", section "llvm.metadata"
@.str.5.24 = private unnamed_addr constant [15 x i8] c"gpio_polling.c\00", section "llvm.metadata"
@.str.6.25 = private unnamed_addr constant [23 x i8] c"GPIO server initiated\0A\00", align 1
@.str.7.26 = private unnamed_addr constant [25 x i8] c"GPIO PIR (%i) value: %i\0A\00", align 1
@.str.8.27 = private unnamed_addr constant [21 x i8] c"PIR sensor activated\00", align 1
@.str.9.28 = private unnamed_addr constant [2 x i8] c"2\00", align 1
@.str.10.29 = private unnamed_addr constant [36 x i8] c"Error %i while reading GPIO %i: %s\0A\00", align 1
@.str.11.30 = private unnamed_addr constant [44 x i8] c"GPIO server terminated with error code: %i\0A\00", align 1
@.str.12.33 = private unnamed_addr constant [17 x i8] c"./ARI_branch.txt\00", align 1
@.str.13.34 = private unnamed_addr constant [18 x i8] c"./ARI_ind_jmp.txt\00", align 1
@.str.14.35 = private unnamed_addr constant [19 x i8] c"./ARI_ret_hash.txt\00", align 1
@.str.15.36 = private unnamed_addr constant [14 x i8] c"./ARI_tsf.txt\00", align 1
@.str.16.37 = private unnamed_addr constant [19 x i8] c"./ARI_tsf_cond.txt\00", align 1
@.str.17.38 = private unnamed_addr constant [26 x i8] c"export_gpios ret_err: %d\0A\00", align 1
@.str.18.39 = private unnamed_addr constant [26 x i8] c"Polling thread initiated\0A\00", align 1
@.str.19.40 = private unnamed_addr constant [38 x i8] c"Error %i creating polling thread: %s\0A\00", align 1
@ret_recording_finish = external global i32, align 4
@.str.20 = private unnamed_addr constant [40 x i8] c"round with attestation time usecs: %lu\0A\00", align 1
@.str.21 = private unnamed_addr constant [37 x i8] c"Polling thread terminated correctly\0A\00", align 1
@.str.22 = private unnamed_addr constant [48 x i8] c"Error waiting for the polling thread to finish\0A\00", align 1
@Token_id = common global [81 x i8] zeroinitializer, section ".DATA_REGION_0__bss", align 1
@User_id = common global [81 x i8] zeroinitializer, section ".DATA_REGION_0__bss", align 1
@Server_path = common global [65 x i8] zeroinitializer, section ".DATA_REGION_0__bss", align 1
@Server_port = common global i32 0, section ".DATA_REGION_0__bss", align 4
@Server_name = common global [65 x i8] zeroinitializer, section ".DATA_REGION_0__bss", align 1
@Server_ip = common global %struct.in_addr zeroinitializer, section ".DATA_REGION_0__bss", align 4
@.str.43 = private unnamed_addr constant [80 x i8] c"Error obtaining the directory of the current-process executable file: errno=%d\0A\00", align 1
@.str.1.44 = private unnamed_addr constant [3 x i8] c"rt\00", align 1
@.str.2.45 = private unnamed_addr constant [2 x i8] c"/\00", align 1
@.str.3.46 = private unnamed_addr constant [21 x i8] c" server_url= %2083s\0A\00", align 1
@.str.4.47 = private unnamed_addr constant [14 x i8] c" token= %80s\0A\00", align 1
@.str.5.48 = private unnamed_addr constant [13 x i8] c" user= %80s\0A\00", align 1
@.str.6.49 = private unnamed_addr constant [73 x i8] c"Error loading Pushover config file: unknown variable name found in file\0A\00", align 1
@.str.7.50 = private unnamed_addr constant [8 x i8] c"http://\00", align 1
@.str.8.51 = private unnamed_addr constant [3 x i8] c"%i\00", align 1
@.str.9.52 = private unnamed_addr constant [44 x i8] c"Using Pushover server %s for notifications\0A\00", align 1
@.str.10.53 = private unnamed_addr constant [86 x i8] c"Error loading Pushover config file: server URL is too long (more than 64 characters)\0A\00", align 1
@.str.11.54 = private unnamed_addr constant [69 x i8] c"Error loading Pushover config file: server URL start is not http://\0A\00", align 1
@.str.12.55 = private unnamed_addr constant [55 x i8] c"Error loading Pushover config file: user id not found\0A\00", align 1
@.str.13.56 = private unnamed_addr constant [56 x i8] c"Error loading Pushover config file: token id not found\0A\00", align 1
@.str.14.57 = private unnamed_addr constant [58 x i8] c"Error loading Pushover config file: server URL not found\0A\00", align 1
@.str.15.58 = private unnamed_addr constant [49 x i8] c"Error opening Pushover config file %s: errno=%d\0A\00", align 1
@.str.16.61 = private unnamed_addr constant [4 x i8] c"r+b\00", align 1
@.str.17.62 = private unnamed_addr constant [2 x i8] c"2\00", align 1
@.str.18.63 = private unnamed_addr constant [19 x i8] c"POST %s HTTP/1.0\0D\0A\00", align 1
@.str.19.64 = private unnamed_addr constant [11 x i8] c"Host: %s\0D\0A\00", align 1
@.str.20.65 = private unnamed_addr constant [50 x i8] c"Content-Type: application/x-www-form-urlencoded\0D\0A\00", align 1
@.str.21.66 = private unnamed_addr constant [24 x i8] c"Content-Length: %lu\0D\0A\0D\0A\00", align 1
@.str.22.67 = private unnamed_addr constant [40 x i8] c"token=%s&user=%s&message=%s&priority=%s\00", align 1
@.str.23 = private unnamed_addr constant [21 x i8] c"&retry=31&expire=120\00", align 1
@.str.24 = private unnamed_addr constant [23 x i8] c"HTTP/%*[^ ] %u %*[^\0D]\0A\00", align 1
@.str.25 = private unnamed_addr constant [4 x i8] c" { \00", align 1
@.str.26 = private unnamed_addr constant [12 x i8] c" \22%[^\22]\22 : \00", align 1
@.str.27 = private unnamed_addr constant [3 x i8] c" \22\00", align 1
@.str.28 = private unnamed_addr constant [10 x i8] c" %[^,}\22]\22\00", align 1
@.str.29 = private unnamed_addr constant [3 x i8] c" ,\00", align 1
@.str.30 = private unnamed_addr constant [7 x i8] c"status\00", align 1
@.str.31 = private unnamed_addr constant [3 x i8] c" }\00", align 1
@.str.32 = private unnamed_addr constant [52 x i8] c"Error status code %i received from Pushover server\0A\00", align 1
@.str.33 = private unnamed_addr constant [89 x i8] c"Invalid format of response body from Pushover server. Status code could not be obtained\0A\00", align 1
@.str.34 = private unnamed_addr constant [59 x i8] c"Too long response from Pushover server: reception aborted\0A\00", align 1
@.str.35 = private unnamed_addr constant [84 x i8] c"Error receiving response header from Pushover server: truncated response. errno=%d\0A\00", align 1
@.str.36 = private unnamed_addr constant [50 x i8] c"HTTP error code %u received from Pushover server\0A\00", align 1
@.str.37 = private unnamed_addr constant [77 x i8] c"Error receiving response from Pushover server: fscanf returned %i. errno=%d\0A\00", align 1
@.str.38 = private unnamed_addr constant [73 x i8] c"Error opening socket connected to Pushover server as file: errno=%d: %s\0A\00", align 1
@.str.39 = private unnamed_addr constant [51 x i8] c"Error connecting to Pushover server: errno=%d: %s\0A\00", align 1
@.str.40 = private unnamed_addr constant [67 x i8] c"Error creating socket for connecting to Pushover server: errno=%d\0A\00", align 1
@.str.68 = private unnamed_addr constant [23 x i8] c"Unknown specified host\00", align 1
@.str.1.69 = private unnamed_addr constant [35 x i8] c"No NS records for specified domain\00", align 1
@.str.2.70 = private unnamed_addr constant [25 x i8] c"No response for NS query\00", align 1
@.str.3.71 = private unnamed_addr constant [17 x i8] c"Unexpected error\00", align 1
@.str.4.72 = private unnamed_addr constant [17 x i8] c"FORMERR response\00", align 1
@.str.5.73 = private unnamed_addr constant [18 x i8] c"SERVFAIL response\00", align 1
@.str.6.74 = private unnamed_addr constant [18 x i8] c"NXDOMAIN response\00", align 1
@.str.7.75 = private unnamed_addr constant [16 x i8] c"NOTIMP response\00", align 1
@.str.8.76 = private unnamed_addr constant [17 x i8] c"REFUSED response\00", align 1
@.str.9.77 = private unnamed_addr constant [23 x i8] c"unexpected return code\00", align 1
@.str.10.80 = private unnamed_addr constant [46 x i8] c"Error resolving IP of hostname %s. error: %s\0A\00", align 1
@.str.11.81 = private unnamed_addr constant [6 x i8] c"> %s\0A\00", align 1
@.str.12.82 = private unnamed_addr constant [37 x i8] c"%s: expected answer type %d, got %d\0A\00", align 1
@.str.13.83 = private unnamed_addr constant [16 x i8] c"ns_parserr: %s\0A\00", align 1
@.str.14.84 = private unnamed_addr constant [31 x i8] c"%s: expected 1 answer, got %d\0A\00", align 1
@.str.15.85 = private unnamed_addr constant [49 x i8] c"DNS response reported an error (domain: %s): %s\0A\00", align 1
@.str.16.86 = private unnamed_addr constant [18 x i8] c"ns_initparse: %s\0A\00", align 1
@.str.17.87 = private unnamed_addr constant [59 x i8] c"Connection refused: There is no name server running on %s\0A\00", align 1
@.str.18.88 = private unnamed_addr constant [49 x i8] c"There was no response from %s (h_errno: %i: %s)\0A\00", align 1
@.str.19.89 = private unnamed_addr constant [26 x i8] c"res_init error. errno:%i\0A\00", align 1
@.str.20.92 = private unnamed_addr constant [22 x i8] c"resolver1.opendns.com\00", align 1
@.str.21.93 = private unnamed_addr constant [17 x i8] c"myip.opendns.com\00", align 1
@.str.96 = private unnamed_addr constant [15 x i8] c"/proc/self/exe\00", align 1
@.str.1.97 = private unnamed_addr constant [2 x i8] c"/\00", align 1
@.str.2.102 = private unnamed_addr constant [40 x i8] c"Child process with PID: %i terminated.\0A\00", align 1
@.str.3.103 = private unnamed_addr constant [57 x i8] c"Error waiting for child process to finish. errno %i: %s\0A\00", align 1
@.str.4.106 = private unnamed_addr constant [64 x i8] c"Creating process %s: failed redirect standard output. errno=%d\0A\00", align 1
@.str.5.107 = private unnamed_addr constant [70 x i8] c"Creating process %s: failed redirect standard error output. errno=%d\0A\00", align 1
@.str.6.108 = private unnamed_addr constant [10 x i8] c"/dev/null\00", align 1
@.str.7.109 = private unnamed_addr constant [63 x i8] c"Creating process %s: failed redirect standard input. errno=%d\0A\00", align 1
@.str.8.110 = private unnamed_addr constant [71 x i8] c"Creating process %s: could not open null device for reading. errno=%d\0A\00", align 1
@.str.9.111 = private unnamed_addr constant [66 x i8] c"Creating process %s: failed to execute capture program. errno=%d\0A\00", align 1
@.str.10.112 = private unnamed_addr constant [50 x i8] c"Creating process %s: first fork failed. errno=%d\0A\00", align 1
@.str.11.115 = private unnamed_addr constant [46 x i8] c"Sensor polling (timer) set to %lis and %lius\0A\00", align 1
@.str.12.116 = private unnamed_addr constant [35 x i8] c"Error setting timer: errno %i: %s\0A\00", align 1
@.str.13.117 = private unnamed_addr constant [65 x i8] c"iAlarm daemon init error: could not open null device for reading\00", align 1
@.str.14.118 = private unnamed_addr constant [65 x i8] c"iAlarm daemon init error: could not open null device for writing\00", align 1
@stderr = external global %struct._IO_FILE*, align 4
@.str.15.119 = private unnamed_addr constant [56 x i8] c"iAlarm daemon init error: second fork failed. errno=%d\0A\00", align 1
@.str.16.120 = private unnamed_addr constant [79 x i8] c"iAlarm daemon init error: child process could become session leader. errno=%d\0A\00", align 1
@.str.17.121 = private unnamed_addr constant [55 x i8] c"iAlarm daemon init error: first fork failed. errno=%d\0A\00", align 1
@Console_messages = global i32 1, section ".DATA_REGION_1__data", align 4
@Log_file_handle = global %struct._IO_FILE* null, section ".DATA_REGION_0__bss", align 4
@Event_file_handle = global %struct._IO_FILE* null, section ".DATA_REGION_0__bss", align 4
@.str.126 = private unnamed_addr constant [18 x i8] c"%Y-%m-%d %H:%M:%S\00", align 1
@.str.1.129 = private unnamed_addr constant [6 x i8] c"[%s] \00", align 1
@.str.2.130 = private unnamed_addr constant [4 x i8] c"a+t\00", align 1
@.str.3.131 = private unnamed_addr constant [3 x i8] c"wt\00", align 1
@.str.4.132 = private unnamed_addr constant [31 x i8] c"\0A[%s] <Old messages deleted>\0A\0A\00", align 1
@.str.5.133 = private unnamed_addr constant [64 x i8] c"[%s] --------------------- Log initiated ---------------------\0A\00", align 1
@.str.6.134 = private unnamed_addr constant [28 x i8] c"[%s] iAlarm daemon running\0A\00", align 1
@.str.7.135 = private unnamed_addr constant [32 x i8] c"[%s] iAlarm daemon terminated\0A\0A\00", align 1
@.str.8.138 = private unnamed_addr constant [29 x i8] c"/var/log/alarm4pi/daemon.log\00", align 1
@.str.9.139 = private unnamed_addr constant [29 x i8] c"/var/log/alarm4pi/events.log\00", align 1
@.str.142 = private unnamed_addr constant [23 x i8] c"/sys/class/gpio/export\00", align 1
@.str.1.143 = private unnamed_addr constant [3 x i8] c"%d\00", align 1
@.str.2.144 = private unnamed_addr constant [33 x i8] c"/sys/class/gpio/gpio%d/direction\00", align 1
@.str.3.145 = private unnamed_addr constant [25 x i8] c"/sys/class/gpio/unexport\00", align 1
@GPIO_direction.s_directions_str = private unnamed_addr constant [2 x i8*] [i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.4.146, i32 0, i32 0), i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str.5.147, i32 0, i32 0)], section ".DATA_REGION_1__data", align 4
@.str.4.146 = private unnamed_addr constant [3 x i8] c"in\00", align 1
@.str.5.147 = private unnamed_addr constant [4 x i8] c"out\00", align 1
@.str.6.150 = private unnamed_addr constant [29 x i8] c"/sys/class/gpio/gpio%d/value\00", align 1
@GPIO_write.s_values_str = private unnamed_addr constant [2 x i8*] [i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.7.151, i32 0, i32 0), i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.8.152, i32 0, i32 0)], section ".DATA_REGION_1__data", align 4
@.str.7.151 = private unnamed_addr constant [2 x i8] c"0\00", align 1
@.str.8.152 = private unnamed_addr constant [2 x i8] c"1\00", align 1
@.str.9.155 = private unnamed_addr constant [54 x i8] c"While exporting output pin %d (relay 4) error %d: %s\0A\00", align 1
@.str.10.156 = private unnamed_addr constant [54 x i8] c"While exporting output pin %d (relay 3) error %d: %s\0A\00", align 1
@.str.11.157 = private unnamed_addr constant [54 x i8] c"While exporting output pin %d (relay 2) error %d: %s\0A\00", align 1
@.str.12.158 = private unnamed_addr constant [54 x i8] c"While exporting output pin %d (relay 1) error %d: %s\0A\00", align 1
@.str.13.159 = private unnamed_addr constant [49 x i8] c"While exporting input pin %d (PIR) error %d: %s\0A\00", align 1
@.str.14.162 = private unnamed_addr constant [53 x i8] c"While configuring direcction of pin %d error %d: %s\0A\00", align 1
@.str.15.165 = private unnamed_addr constant [42 x i8] c"While unexporting GPIO pins error %d: %s\0A\00", align 1

; Function Attrs: nounwind
define i32 @usecs() #0 section ".CODE_REGION_1_" !dbg !327 {
  %1 = alloca %struct.timeval, align 4
  call void @llvm.dbg.declare(metadata %struct.timeval* %1, metadata !330, metadata !336), !dbg !337
  %2 = call i32 @gettimeofday(%struct.timeval* %1, %struct.timeval* null) #7, !dbg !338
  %3 = getelementptr inbounds %struct.timeval, %struct.timeval* %1, i32 0, i32 0, !dbg !339
  %4 = load i32, i32* %3, align 4, !dbg !339
  %5 = mul nsw i32 %4, 1000, !dbg !340
  %6 = mul nsw i32 %5, 1000, !dbg !341
  %7 = getelementptr inbounds %struct.timeval, %struct.timeval* %1, i32 0, i32 1, !dbg !342
  %8 = load i32, i32* %7, align 4, !dbg !342
  %9 = add nsw i32 %6, %8, !dbg !343
  ret i32 %9, !dbg !344
}

; Function Attrs: nounwind readnone
declare void @llvm.dbg.declare(metadata, metadata, metadata) #1

; Function Attrs: nounwind
declare i32 @gettimeofday(%struct.timeval*, %struct.timeval*) #2 section ".CODE_REGION_1_"

; Function Attrs: nounwind
define i32 @set_signal_handler() #0 section ".CODE_REGION_2_" !dbg !345 {
  %1 = alloca i32, align 4
  %2 = alloca %struct.sigaction, align 4
  call void @llvm.dbg.declare(metadata i32* %1, metadata !348, metadata !336), !dbg !349
  call void @llvm.dbg.declare(metadata %struct.sigaction* %2, metadata !350, metadata !336), !dbg !440
  %3 = bitcast %struct.sigaction* %2 to i8*, !dbg !441
  call void @llvm.memset.p0i8.i32(i8* %3, i8 0, i32 140, i32 4, i1 false), !dbg !441
  %4 = getelementptr inbounds %struct.sigaction, %struct.sigaction* %2, i32 0, i32 0, !dbg !442
  %5 = bitcast %union.anon* %4 to void (i32)**, !dbg !442
  store void (i32)* @timer_handler, void (i32)** %5, align 4, !dbg !443
  %6 = call i32 @sigaction(i32 14, %struct.sigaction* %2, %struct.sigaction* null) #7, !dbg !444
  %7 = getelementptr inbounds %struct.sigaction, %struct.sigaction* %2, i32 0, i32 0, !dbg !445
  %8 = bitcast %union.anon* %7 to void (i32)**, !dbg !445
  store void (i32)* @exit_deamon_handler, void (i32)** %8, align 4, !dbg !446
  %9 = getelementptr inbounds %struct.sigaction, %struct.sigaction* %2, i32 0, i32 2, !dbg !447
  store i32 268435456, i32* %9, align 4, !dbg !448
  %10 = call i32 @sigaction(i32 2, %struct.sigaction* %2, %struct.sigaction* null) #7, !dbg !449
  %11 = call i32 @sigaction(i32 15, %struct.sigaction* %2, %struct.sigaction* null) #7, !dbg !450
  %12 = icmp eq i32 %11, 0, !dbg !452
  br i1 %12, label %13, label %14, !dbg !453

; <label>:13:                                     ; preds = %0
  store i32 0, i32* %1, align 4, !dbg !454
  br label %21, !dbg !455

; <label>:14:                                     ; preds = %0
  %15 = call i32* @__errno_location() #1, !dbg !456
  %16 = load i32, i32* %15, align 4, !dbg !456
  store i32 %16, i32* %1, align 4, !dbg !458
  %17 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !459
  %18 = call i32* @__errno_location() #1, !dbg !459
  %19 = load i32, i32* %18, align 4, !dbg !459
  call void @__AMI_fake_direct_transfer(), !dbg !460
  %20 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %17, i8* getelementptr inbounds ([52 x i8], [52 x i8]* @.str.6, i32 0, i32 0), i32 %19), !dbg !460
  br label %21

; <label>:21:                                     ; preds = %14, %13
  %22 = load i32, i32* %1, align 4, !dbg !462
  ret i32 %22, !dbg !463
}

; Function Attrs: argmemonly nounwind
declare void @llvm.memset.p0i8.i32(i8* nocapture writeonly, i8, i32, i32, i1) #3

; Function Attrs: nounwind
define internal void @timer_handler(i32) #0 section ".CODE_REGION_2_" !dbg !26 {
  %2 = alloca i32, align 4
  store i32 %0, i32* %2, align 4
  call void @llvm.dbg.declare(metadata i32* %2, metadata !464, metadata !336), !dbg !465
  %3 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !466
  %4 = load i32, i32* @timer_handler.count, align 4, !dbg !466
  %5 = add nsw i32 %4, 1, !dbg !466
  call void @__AMI_fake_local_wrt(), !dbg !466
  store i32 %5, i32* @timer_handler.count, align 4, !dbg !466
  call void @__AMI_fake_direct_transfer(), !dbg !466
  %6 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %3, i8* getelementptr inbounds ([24 x i8], [24 x i8]* @.str.17, i32 0, i32 0), i32 %5), !dbg !466
  ret void, !dbg !467
}

; Function Attrs: nounwind
declare i32 @sigaction(i32, %struct.sigaction*, %struct.sigaction*) #2 section ".CODE_REGION_2_"

; Function Attrs: nounwind
define internal void @exit_deamon_handler(i32) #0 section ".CODE_REGION_2_" !dbg !468 {
  %2 = alloca i32, align 4
  store i32 %0, i32* %2, align 4
  call void @llvm.dbg.declare(metadata i32* %2, metadata !469, metadata !336), !dbg !470
  %3 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !471
  %4 = load i32, i32* %2, align 4, !dbg !471
  call void @__AMI_fake_direct_transfer(), !dbg !471
  %5 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %3, i8* getelementptr inbounds ([54 x i8], [54 x i8]* @.str.18, i32 0, i32 0), i32 %4), !dbg !471
  call void @kill_processes(i32* getelementptr inbounds ([2 x i32], [2 x i32]* @Child_process_id, i32 0, i32 0), i32 2), !dbg !472
  call void @__AMI_fake_local_wrt(), !dbg !473
  store volatile i32 1, i32* @Exit_daemon_loop, align 4, !dbg !473
  ret void, !dbg !474
}

; Function Attrs: nounwind readnone
declare i32* @__errno_location() #4 section ".CODE_REGION_1_"

; Function Attrs: nounwind
define i32 @main(i32, i8**) #0 section ".CODE_REGION_2_" !dbg !475 {
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca i8**, align 4
  %6 = alloca i32, align 4
  %7 = alloca i32, align 4
  %8 = alloca i32, align 4
  store i32 0, i32* %3, align 4
  store i32 %0, i32* %4, align 4
  call void @llvm.dbg.declare(metadata i32* %4, metadata !479, metadata !336), !dbg !480
  store i8** %1, i8*** %5, align 4
  call void @llvm.dbg.declare(metadata i8*** %5, metadata !481, metadata !336), !dbg !482
  call void @llvm.dbg.declare(metadata i32* %6, metadata !483, metadata !336), !dbg !484
  call void @llvm.dbg.declare(metadata i32* %7, metadata !485, metadata !336), !dbg !486
  call void @llvm.dbg.declare(metadata i32* %8, metadata !487, metadata !336), !dbg !488
  store i32 0, i32* %6, align 4, !dbg !489
  %9 = load i32, i32* %6, align 4, !dbg !490
  %10 = icmp eq i32 %9, 0, !dbg !492
  br i1 %10, label %11, label %59, !dbg !493

; <label>:11:                                     ; preds = %2
  call void (i32, i8*, ...) @syslog(i32 5, i8* getelementptr inbounds ([23 x i8], [23 x i8]* @.str.7, i32 0, i32 0)), !dbg !494
  %12 = call i32 @open_log_files(), !dbg !496
  %13 = icmp ne i32 %12, 0, !dbg !496
  br i1 %13, label %14, label %15, !dbg !498

; <label>:14:                                     ; preds = %11
  call void (i32, i8*, ...) @syslog(i32 4, i8* getelementptr inbounds ([26 x i8], [26 x i8]* @.str.8, i32 0, i32 0)), !dbg !499
  br label %15, !dbg !499

; <label>:15:                                     ; preds = %14, %11
  %16 = call i32 @set_signal_handler(), !dbg !500
  %17 = call i32 @setenv(i8* getelementptr inbounds ([16 x i8], [16 x i8]* @.str.9, i32 0, i32 0), i8* getelementptr inbounds ([15 x i8], [15 x i8]* @.str.10, i32 0, i32 0), i32 0) #7, !dbg !501
  %18 = icmp ne i32 %17, 0, !dbg !503
  br i1 %18, label %19, label %24, !dbg !504

; <label>:19:                                     ; preds = %15
  %20 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !505
  %21 = call i32* @__errno_location() #1, !dbg !505
  %22 = load i32, i32* %21, align 4, !dbg !505
  call void @__AMI_fake_direct_transfer(), !dbg !506
  %23 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %20, i8* getelementptr inbounds ([64 x i8], [64 x i8]* @.str.11, i32 0, i32 0), i32 %22), !dbg !506
  br label %24, !dbg !505

; <label>:24:                                     ; preds = %19, %15
  %25 = load i8*, i8** getelementptr inbounds ([7 x i8*], [7 x i8*]* @Capture_exec_args, i32 0, i32 0), align 4, !dbg !508
  %26 = call i32 @run_background_command(i32* %7, i8* %25, i8** getelementptr inbounds ([7 x i8*], [7 x i8*]* @Capture_exec_args, i32 0, i32 0)), !dbg !510
  %27 = icmp eq i32 %26, 0, !dbg !511
  br i1 %27, label %28, label %42, !dbg !512

; <label>:28:                                     ; preds = %24
  %29 = load i32, i32* %7, align 4, !dbg !513
  store i32 %29, i32* getelementptr inbounds ([2 x i32], [2 x i32]* @Child_process_id, i32 0, i32 0), align 4, !dbg !515
  %30 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !516
  %31 = load i8*, i8** getelementptr inbounds ([7 x i8*], [7 x i8*]* @Capture_exec_args, i32 0, i32 0), align 4, !dbg !516
  call void @__AMI_fake_direct_transfer(), !dbg !516
  %32 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %30, i8* getelementptr inbounds ([27 x i8], [27 x i8]* @.str.12, i32 0, i32 0), i8* %31), !dbg !516
  %33 = load i8*, i8** getelementptr inbounds ([7 x i8*], [7 x i8*]* @Web_server_exec_args, i32 0, i32 0), align 4, !dbg !517
  %34 = call i32 @run_background_command(i32* %8, i8* %33, i8** getelementptr inbounds ([7 x i8*], [7 x i8*]* @Web_server_exec_args, i32 0, i32 0)), !dbg !519
  %35 = icmp eq i32 %34, 0, !dbg !520
  br i1 %35, label %36, label %41, !dbg !521

; <label>:36:                                     ; preds = %28
  %37 = load i32, i32* %8, align 4, !dbg !522
  store i32 %37, i32* getelementptr inbounds ([2 x i32], [2 x i32]* @Child_process_id, i32 0, i32 1), align 4, !dbg !524
  %38 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !525
  %39 = load i8*, i8** getelementptr inbounds ([7 x i8*], [7 x i8*]* @Web_server_exec_args, i32 0, i32 0), align 4, !dbg !525
  call void @__AMI_fake_direct_transfer(), !dbg !525
  %40 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %38, i8* getelementptr inbounds ([27 x i8], [27 x i8]* @.str.12, i32 0, i32 0), i8* %39), !dbg !525
  br label %41, !dbg !526

; <label>:41:                                     ; preds = %36, %28
  br label %42, !dbg !527

; <label>:42:                                     ; preds = %41, %24
  call void @__AMI_fake_direct_transfer(), !dbg !528
  %43 = call i32 @init_polling(i32* @Exit_daemon_loop, i8* getelementptr inbounds ([23 x i8], [23 x i8]* @.str.13, i32 0, i32 0)), !dbg !528
  store i32 %43, i32* %6, align 4, !dbg !529
  %44 = load i32, i32* %6, align 4, !dbg !530
  %45 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([14 x i8], [14 x i8]* @.str.14, i32 0, i32 0), i32 %44), !dbg !531
  %46 = load i32, i32* %6, align 4, !dbg !532
  %47 = icmp eq i32 %46, 0, !dbg !534
  br i1 %47, label %48, label %50, !dbg !535

; <label>:48:                                     ; preds = %42
  %49 = call i32 @wait_polling_end(), !dbg !536
  br label %53, !dbg !538

; <label>:50:                                     ; preds = %42
  %51 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !539
  call void @__AMI_fake_direct_transfer(), !dbg !539
  %52 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %51, i8* getelementptr inbounds ([38 x i8], [38 x i8]* @.str.15, i32 0, i32 0)), !dbg !539
  br label %53

; <label>:53:                                     ; preds = %50, %48
  %54 = call i32 @sleep(i32 1), !dbg !540
  %55 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !541
  call void @__AMI_fake_direct_transfer(), !dbg !541
  %56 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %55, i8* getelementptr inbounds ([39 x i8], [39 x i8]* @.str.16, i32 0, i32 0)), !dbg !541
  %57 = call i32 @configure_timer(float -1.000000e+00), !dbg !542
  %58 = call i32 @wait_processes(i32* getelementptr inbounds ([2 x i32], [2 x i32]* @Child_process_id, i32 0, i32 0), i32 2, i32 0), !dbg !543
  call void @close_log_files(), !dbg !544
  br label %59, !dbg !545

; <label>:59:                                     ; preds = %53, %2
  %60 = load i32, i32* %6, align 4, !dbg !546
  ret i32 %60, !dbg !547
}

declare void @syslog(i32, i8*, ...) #5 section ".CODE_REGION_2_"

; Function Attrs: nounwind
declare i32 @setenv(i8*, i8*, i32) #2 section ".CODE_REGION_2_"

declare i32 @printf(i8*, ...) #5 section ".CODE_REGION_1_"

declare i32 @sleep(i32) #5 section ".CODE_REGION_2_"

; Function Attrs: nounwind
define i32 @send_info_notif(i8*, i8*) #0 section ".CODE_REGION_1_" !dbg !548 {
  %3 = alloca i8*, align 4
  %4 = alloca i8*, align 4
  %5 = alloca [4096 x i8], align 1
  store i8* %0, i8** %3, align 4
  call void @llvm.dbg.declare(metadata i8** %3, metadata !551, metadata !336), !dbg !552
  store i8* %1, i8** %4, align 4
  call void @llvm.dbg.declare(metadata i8** %4, metadata !553, metadata !336), !dbg !554
  call void @llvm.dbg.declare(metadata [4096 x i8]* %5, metadata !555, metadata !336), !dbg !559
  %6 = getelementptr inbounds [4096 x i8], [4096 x i8]* %5, i32 0, i32 0, !dbg !560
  %7 = load i8*, i8** %3, align 4, !dbg !561
  %8 = call i32 (i8*, i32, i8*, ...) @snprintf(i8* %6, i32 4096, i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.19, i32 0, i32 0), i8* getelementptr inbounds ([146 x i8], [146 x i8]* @Msg_info_str, i32 0, i32 0), i8* %7) #7, !dbg !562
  %9 = getelementptr inbounds [4096 x i8], [4096 x i8]* %5, i32 0, i32 0, !dbg !563
  %10 = load i8*, i8** %4, align 4, !dbg !564
  %11 = call i32 @send_notification(i8* %9, i8* %10), !dbg !565
  call void @__AMI_fake_rt_transfer(), !dbg !566
  ret i32 %11, !dbg !566
}

; Function Attrs: nounwind
declare i32 @snprintf(i8*, i32, i8*, ...) #2 section ".CODE_REGION_1_"

; Function Attrs: nounwind
define i32 @update_ip_msg(i8*) #0 section ".CODE_REGION_2_" !dbg !567 {
  %2 = alloca i8*, align 4
  %3 = alloca i32, align 4
  %4 = alloca [46 x i8], align 1
  %5 = alloca [146 x i8], align 1
  store i8* %0, i8** %2, align 4
  call void @llvm.dbg.declare(metadata i8** %2, metadata !570, metadata !336), !dbg !571
  call void @llvm.dbg.declare(metadata i32* %3, metadata !572, metadata !336), !dbg !573
  call void @llvm.dbg.declare(metadata [46 x i8]* %4, metadata !574, metadata !336), !dbg !578
  call void @llvm.dbg.declare(metadata [146 x i8]* %5, metadata !579, metadata !336), !dbg !580
  %6 = getelementptr inbounds [46 x i8], [46 x i8]* %4, i32 0, i32 0, !dbg !581
  %7 = call i32 @get_public_ip(i8* %6), !dbg !582
  store i32 %7, i32* %3, align 4, !dbg !583
  %8 = load i32, i32* %3, align 4, !dbg !584
  %9 = icmp eq i32 %8, 0, !dbg !586
  br i1 %9, label %10, label %26, !dbg !587

; <label>:10:                                     ; preds = %1
  %11 = getelementptr inbounds [146 x i8], [146 x i8]* %5, i32 0, i32 0, !dbg !588
  %12 = load i8*, i8** %2, align 4, !dbg !590
  %13 = getelementptr inbounds [46 x i8], [46 x i8]* %4, i32 0, i32 0, !dbg !591
  %14 = call i32 (i8*, i32, i8*, ...) @snprintf(i8* %11, i32 146, i8* %12, i8* %13) #7, !dbg !592
  %15 = getelementptr inbounds [146 x i8], [146 x i8]* %5, i32 0, i32 0, !dbg !593
  %16 = call i32 @strcmp(i8* %15, i8* getelementptr inbounds ([146 x i8], [146 x i8]* @Msg_info_str, i32 0, i32 0)) #9, !dbg !595
  %17 = icmp ne i32 %16, 0, !dbg !596
  br i1 %17, label %18, label %25, !dbg !597

; <label>:18:                                     ; preds = %10
  %19 = getelementptr inbounds [146 x i8], [146 x i8]* %5, i32 0, i32 0, !dbg !598
  %20 = call i8* @strcpy(i8* getelementptr inbounds ([146 x i8], [146 x i8]* @Msg_info_str, i32 0, i32 0), i8* %19) #7, !dbg !600
  %21 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !601
  %22 = getelementptr inbounds [46 x i8], [46 x i8]* %4, i32 0, i32 0, !dbg !601
  call void @__AMI_fake_direct_transfer(), !dbg !601
  %23 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %21, i8* getelementptr inbounds ([23 x i8], [23 x i8]* @.str.1.20, i32 0, i32 0), i8* %22), !dbg !601
  call void @__AMI_fake_direct_transfer(), !dbg !602
  %24 = call i32 @send_info_notif(i8* getelementptr inbounds ([37 x i8], [37 x i8]* @.str.2.21, i32 0, i32 0), i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.3.22, i32 0, i32 0)), !dbg !602
  br label %25, !dbg !603

; <label>:25:                                     ; preds = %18, %10
  br label %26, !dbg !604

; <label>:26:                                     ; preds = %25, %1
  %27 = load i32, i32* %3, align 4, !dbg !605
  ret i32 %27, !dbg !606
}

; Function Attrs: nounwind readonly
declare i32 @strcmp(i8*, i8*) #6 section ".CODE_REGION_1_"

; Function Attrs: nounwind
declare i8* @strcpy(i8*, i8*) #2 section ".CODE_REGION_2_"

; Function Attrs: nounwind
define i8* @polling_thread(i32*) #0 section ".CODE_REGION_1_" !dbg !607 {
  %2 = alloca i32*, align 4
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  %7 = alloca i32, align 4
  %8 = alloca i32, align 4
  store i32* %0, i32** %2, align 4
  call void @llvm.dbg.declare(metadata i32** %2, metadata !611, metadata !336), !dbg !612
  call void @llvm.dbg.declare(metadata i32* %3, metadata !613, metadata !336), !dbg !614
  %9 = bitcast i32* %3 to i8*, !dbg !615
  call void @llvm.var.annotation(i8* %9, i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.4.23, i32 0, i32 0), i8* getelementptr inbounds ([15 x i8], [15 x i8]* @.str.5.24, i32 0, i32 0), i32 80), !dbg !615
  call void @llvm.dbg.declare(metadata i32* %4, metadata !616, metadata !336), !dbg !617
  %10 = bitcast i32* %4 to i8*, !dbg !618
  call void @llvm.var.annotation(i8* %10, i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.4.23, i32 0, i32 0), i8* getelementptr inbounds ([15 x i8], [15 x i8]* @.str.5.24, i32 0, i32 0), i32 81), !dbg !618
  call void @llvm.dbg.declare(metadata i32* %5, metadata !619, metadata !336), !dbg !620
  %11 = bitcast i32* %5 to i8*, !dbg !621
  call void @llvm.var.annotation(i8* %11, i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.4.23, i32 0, i32 0), i8* getelementptr inbounds ([15 x i8], [15 x i8]* @.str.5.24, i32 0, i32 0), i32 82), !dbg !621
  call void @llvm.dbg.declare(metadata i32* %6, metadata !622, metadata !336), !dbg !623
  %12 = bitcast i32* %6 to i8*, !dbg !624
  call void @llvm.var.annotation(i8* %12, i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.4.23, i32 0, i32 0), i8* getelementptr inbounds ([15 x i8], [15 x i8]* @.str.5.24, i32 0, i32 0), i32 83), !dbg !624
  call void @llvm.dbg.declare(metadata i32* %7, metadata !625, metadata !336), !dbg !626
  %13 = bitcast i32* %7 to i8*, !dbg !627
  call void @llvm.var.annotation(i8* %13, i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.4.23, i32 0, i32 0), i8* getelementptr inbounds ([15 x i8], [15 x i8]* @.str.5.24, i32 0, i32 0), i32 84), !dbg !627
  %14 = load %struct._IO_FILE*, %struct._IO_FILE** @Event_file_handle, align 4, !dbg !628
  %15 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %14, i8* getelementptr inbounds ([23 x i8], [23 x i8]* @.str.6.25, i32 0, i32 0)), !dbg !628
  store i32 0, i32* %4, align 4, !dbg !629
  store i32 0, i32* %7, align 4, !dbg !630
  store i32 0, i32* %6, align 4, !dbg !631
  call void @llvm.dbg.declare(metadata i32* %8, metadata !632, metadata !336), !dbg !633
  store i32 0, i32* %8, align 4, !dbg !633
  br label %16, !dbg !634

; <label>:16:                                     ; preds = %60, %1
  %17 = load i32, i32* %8, align 4, !dbg !635
  %18 = add nsw i32 %17, 1, !dbg !635
  store i32 %18, i32* %8, align 4, !dbg !635
  %19 = icmp slt i32 %17, 10, !dbg !637
  br i1 %19, label %20, label %61, !dbg !638

; <label>:20:                                     ; preds = %16
  %21 = call i32 @GPIO_read(i32 488, i32* %5), !dbg !639
  store i32 %21, i32* %3, align 4, !dbg !641
  %22 = load i32, i32* %3, align 4, !dbg !642
  %23 = icmp eq i32 %22, 0, !dbg !644
  br i1 %23, label %24, label %43, !dbg !645

; <label>:24:                                     ; preds = %20
  %25 = load i32, i32* %5, align 4, !dbg !646
  %26 = load i32, i32* %6, align 4, !dbg !649
  %27 = icmp ne i32 %25, %26, !dbg !650
  br i1 %27, label %28, label %38, !dbg !651

; <label>:28:                                     ; preds = %24
  %29 = load i32, i32* %5, align 4, !dbg !652
  %30 = icmp ne i32 %29, 0, !dbg !655
  br i1 %30, label %31, label %36, !dbg !656

; <label>:31:                                     ; preds = %28
  %32 = load %struct._IO_FILE*, %struct._IO_FILE** @Event_file_handle, align 4, !dbg !657
  %33 = load i32, i32* %5, align 4, !dbg !657
  %34 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %32, i8* getelementptr inbounds ([25 x i8], [25 x i8]* @.str.7.26, i32 0, i32 0), i32 488, i32 %33), !dbg !657
  %35 = call i32 @send_info_notif(i8* getelementptr inbounds ([21 x i8], [21 x i8]* @.str.8.27, i32 0, i32 0), i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.9.28, i32 0, i32 0)), !dbg !659
  br label %36, !dbg !660

; <label>:36:                                     ; preds = %31, %28
  %37 = load i32, i32* %5, align 4, !dbg !661
  store i32 %37, i32* %6, align 4, !dbg !662
  br label %38, !dbg !663

; <label>:38:                                     ; preds = %36, %24
  %39 = load i32, i32* %5, align 4, !dbg !664
  %40 = icmp ne i32 %39, 0, !dbg !666
  br i1 %40, label %41, label %42, !dbg !667

; <label>:41:                                     ; preds = %38
  store i32 60, i32* %7, align 4, !dbg !668
  br label %42, !dbg !669

; <label>:42:                                     ; preds = %41, %38
  br label %54, !dbg !670

; <label>:43:                                     ; preds = %20
  %44 = load i32, i32* %4, align 4, !dbg !671
  %45 = icmp eq i32 %44, 0, !dbg !674
  br i1 %45, label %46, label %53, !dbg !675

; <label>:46:                                     ; preds = %43
  %47 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !676
  %48 = load i32, i32* %3, align 4, !dbg !676
  %49 = load i32, i32* %3, align 4, !dbg !676
  %50 = call i8* @strerror(i32 %49) #7, !dbg !676
  %51 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %47, i8* getelementptr inbounds ([36 x i8], [36 x i8]* @.str.10.29, i32 0, i32 0), i32 %48, i32 488, i8* %50), !dbg !678
  %52 = load i32, i32* %3, align 4, !dbg !680
  store i32 %52, i32* %4, align 4, !dbg !681
  br label %53, !dbg !682

; <label>:53:                                     ; preds = %46, %43
  br label %54

; <label>:54:                                     ; preds = %53, %42
  %55 = load i32, i32* %7, align 4, !dbg !683
  %56 = icmp sgt i32 %55, 0, !dbg !685
  br i1 %56, label %57, label %60, !dbg !686

; <label>:57:                                     ; preds = %54
  %58 = load i32, i32* %7, align 4, !dbg !687
  %59 = add nsw i32 %58, -1, !dbg !687
  store i32 %59, i32* %7, align 4, !dbg !687
  br label %60, !dbg !688

; <label>:60:                                     ; preds = %57, %54
  br label %16, !dbg !689, !llvm.loop !691

; <label>:61:                                     ; preds = %16
  %62 = load %struct._IO_FILE*, %struct._IO_FILE** @Event_file_handle, align 4, !dbg !692
  %63 = load i32, i32* %4, align 4, !dbg !692
  %64 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %62, i8* getelementptr inbounds ([44 x i8], [44 x i8]* @.str.11.30, i32 0, i32 0), i32 %63), !dbg !692
  %65 = load i32, i32* %4, align 4, !dbg !693
  %66 = inttoptr i32 %65 to i8*, !dbg !694
  ret i8* %66, !dbg !695
}

; Function Attrs: nounwind
declare void @llvm.var.annotation(i8*, i8*, i8*, i32) #7

; Function Attrs: nounwind
declare i8* @strerror(i32) #2 section ".CODE_REGION_1_"

; Function Attrs: nounwind
define i32 @init_polling(i32*, i8*) #0 section ".CODE_REGION_1_" !dbg !696 {
  %3 = alloca i32*, align 4
  %4 = alloca i8*, align 4
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  %7 = alloca i32, align 4
  store i32* %0, i32** %3, align 4
  call void @llvm.dbg.declare(metadata i32** %3, metadata !699, metadata !336), !dbg !700
  store i8* %1, i8** %4, align 4
  call void @llvm.dbg.declare(metadata i8** %4, metadata !701, metadata !336), !dbg !702
  call void @create_files(i8* getelementptr inbounds ([17 x i8], [17 x i8]* @.str.12.33, i32 0, i32 0), i8* getelementptr inbounds ([18 x i8], [18 x i8]* @.str.13.34, i32 0, i32 0), i8* getelementptr inbounds ([19 x i8], [19 x i8]* @.str.14.35, i32 0, i32 0), i8* getelementptr inbounds ([14 x i8], [14 x i8]* @.str.15.36, i32 0, i32 0), i8* getelementptr inbounds ([19 x i8], [19 x i8]* @.str.16.37, i32 0, i32 0)), !dbg !703
  call void @__AMI_fake_local_wrt(), !dbg !704
  store i32 1, i32* @recording_flag, align 4, !dbg !704
  call void @llvm.dbg.declare(metadata i32* %5, metadata !705, metadata !336), !dbg !706
  %8 = bitcast i32* %5 to i8*, !dbg !707
  call void @llvm.var.annotation(i8* %8, i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.4.23, i32 0, i32 0), i8* getelementptr inbounds ([15 x i8], [15 x i8]* @.str.5.24, i32 0, i32 0), i32 159), !dbg !707
  call void @llvm.dbg.declare(metadata i32* %6, metadata !708, metadata !336), !dbg !709
  call void @llvm.dbg.declare(metadata i32* %7, metadata !710, metadata !336), !dbg !711
  %9 = call i32 @usecs(), !dbg !712
  store i32 %9, i32* %6, align 4, !dbg !713
  %10 = call i32 @export_gpios(), !dbg !714
  store i32 %10, i32* %5, align 4, !dbg !715
  %11 = load i32, i32* %5, align 4, !dbg !716
  %12 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([26 x i8], [26 x i8]* @.str.17.38, i32 0, i32 0), i32 %11), !dbg !717
  %13 = load i32, i32* %5, align 4, !dbg !718
  %14 = icmp eq i32 %13, 0, !dbg !720
  br i1 %14, label %15, label %39, !dbg !721

; <label>:15:                                     ; preds = %2
  %16 = call i32 @configure_gpios(), !dbg !722
  store i32 %16, i32* %5, align 4, !dbg !724
  %17 = load i32, i32* %5, align 4, !dbg !725
  %18 = icmp eq i32 %17, 0, !dbg !727
  br i1 %18, label %19, label %38, !dbg !728

; <label>:19:                                     ; preds = %15
  %20 = load i32, i32* %5, align 4, !dbg !729
  %21 = icmp eq i32 %20, 0, !dbg !732
  br i1 %21, label %22, label %37, !dbg !733

; <label>:22:                                     ; preds = %19
  store i8 0, i8* getelementptr inbounds ([146 x i8], [146 x i8]* @Msg_info_str, i32 0, i32 0), align 1, !dbg !734
  %23 = load i32*, i32** %3, align 4, !dbg !736
  %24 = call i8* @polling_thread(i32* %23), !dbg !737
  %25 = load i32, i32* %5, align 4, !dbg !738
  %26 = icmp eq i32 %25, 0, !dbg !740
  br i1 %26, label %27, label %30, !dbg !741

; <label>:27:                                     ; preds = %22
  %28 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !742
  %29 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %28, i8* getelementptr inbounds ([26 x i8], [26 x i8]* @.str.18.39, i32 0, i32 0)), !dbg !742
  br label %36, !dbg !742

; <label>:30:                                     ; preds = %22
  %31 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !743
  %32 = load i32, i32* %5, align 4, !dbg !743
  %33 = load i32, i32* %5, align 4, !dbg !743
  %34 = call i8* @strerror(i32 %33) #7, !dbg !743
  %35 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %31, i8* getelementptr inbounds ([38 x i8], [38 x i8]* @.str.19.40, i32 0, i32 0), i32 %32, i8* %34), !dbg !744
  br label %36

; <label>:36:                                     ; preds = %30, %27
  br label %37, !dbg !746

; <label>:37:                                     ; preds = %36, %19
  br label %38, !dbg !747

; <label>:38:                                     ; preds = %37, %15
  br label %39, !dbg !748

; <label>:39:                                     ; preds = %38, %2
  call void @__AMI_fake_local_wrt(), !dbg !749
  store i32 0, i32* @recording_flag, align 4, !dbg !749
  call void @__AMI_fake_local_wrt(), !dbg !750
  store i32 1, i32* @ret_recording_finish, align 4, !dbg !750
  %40 = call i8* bitcast (i8* (...)* @read_measurement to i8* ()*)(), !dbg !751
  %41 = call i32 @usecs(), !dbg !752
  store i32 %41, i32* %7, align 4, !dbg !753
  %42 = load i32, i32* %7, align 4, !dbg !754
  %43 = load i32, i32* %6, align 4, !dbg !755
  %44 = sub i32 %42, %43, !dbg !756
  %45 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([40 x i8], [40 x i8]* @.str.20, i32 0, i32 0), i32 %44), !dbg !757
  %46 = load i32, i32* %5, align 4, !dbg !758
  call void @__AMI_fake_rt_transfer(), !dbg !759
  ret i32 %46, !dbg !759
}

declare void @create_files(i8*, i8*, i8*, i8*, i8*) #5 section ".CODE_REGION_1_"

declare i8* @read_measurement(...) #5 section ".CODE_REGION_1_"

; Function Attrs: nounwind
define i32 @wait_polling_end() #0 section ".CODE_REGION_2_" !dbg !760 {
  %1 = alloca i32, align 4
  call void @llvm.dbg.declare(metadata i32* %1, metadata !761, metadata !336), !dbg !762
  %2 = load i32, i32* @Polling_thread_id, align 4, !dbg !763
  %3 = call i32 @pthread_join(i32 %2, i8** null), !dbg !764
  store i32 %3, i32* %1, align 4, !dbg !765
  %4 = load i32, i32* %1, align 4, !dbg !766
  %5 = icmp eq i32 %4, 0, !dbg !768
  br i1 %5, label %6, label %9, !dbg !769

; <label>:6:                                      ; preds = %0
  %7 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !770
  call void @__AMI_fake_direct_transfer(), !dbg !770
  %8 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %7, i8* getelementptr inbounds ([37 x i8], [37 x i8]* @.str.21, i32 0, i32 0)), !dbg !770
  br label %12, !dbg !770

; <label>:9:                                      ; preds = %0
  %10 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !771
  call void @__AMI_fake_direct_transfer(), !dbg !771
  %11 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %10, i8* getelementptr inbounds ([48 x i8], [48 x i8]* @.str.22, i32 0, i32 0)), !dbg !771
  br label %12

; <label>:12:                                     ; preds = %9, %6
  %13 = call i32 @unexport_gpios(), !dbg !772
  %14 = load i32, i32* %1, align 4, !dbg !773
  ret i32 %14, !dbg !774
}

declare i32 @pthread_join(i32, i8**) #5 section ".CODE_REGION_2_"

; Function Attrs: nounwind
define i32 @pushover_init(i8*) #0 section ".CODE_REGION_2_" !dbg !775 {
  %2 = alloca i32, align 4
  %3 = alloca i8*, align 4
  %4 = alloca i32, align 4
  %5 = alloca %struct._IO_FILE*, align 4
  %6 = alloca [4097 x i8], align 1
  %7 = alloca [2084 x i8], align 1
  %8 = alloca i8*, align 4
  %9 = alloca i8*, align 4
  %10 = alloca i8*, align 4
  %11 = alloca i32, align 4
  %12 = alloca i32, align 4
  store i8* %0, i8** %3, align 4
  call void @llvm.dbg.declare(metadata i8** %3, metadata !776, metadata !336), !dbg !777
  call void @llvm.dbg.declare(metadata i32* %4, metadata !778, metadata !336), !dbg !779
  call void @llvm.dbg.declare(metadata %struct._IO_FILE** %5, metadata !780, metadata !336), !dbg !821
  call void @llvm.dbg.declare(metadata [4097 x i8]* %6, metadata !822, metadata !336), !dbg !826
  %13 = load i8*, i8** %3, align 4, !dbg !827
  %14 = call i32 @strlen(i8* %13) #9, !dbg !829
  %15 = icmp ugt i32 %14, 4096, !dbg !830
  br i1 %15, label %16, label %17, !dbg !831

; <label>:16:                                     ; preds = %1
  store i32 22, i32* %2, align 4, !dbg !832
  br label %213, !dbg !832

; <label>:17:                                     ; preds = %1
  %18 = load i8*, i8** %3, align 4, !dbg !833
  %19 = getelementptr inbounds i8, i8* %18, i32 0, !dbg !833
  %20 = load i8, i8* %19, align 1, !dbg !833
  %21 = zext i8 %20 to i32, !dbg !833
  %22 = icmp ne i32 %21, 47, !dbg !835
  br i1 %22, label %23, label %52, !dbg !836

; <label>:23:                                     ; preds = %17
  %24 = getelementptr inbounds [4097 x i8], [4097 x i8]* %6, i32 0, i32 0, !dbg !837
  %25 = call i32 @get_current_exec_path(i8* %24, i32 4096), !dbg !839
  store i32 %25, i32* %4, align 4, !dbg !840
  %26 = load i32, i32* %4, align 4, !dbg !841
  %27 = icmp eq i32 %26, 0, !dbg !843
  br i1 %27, label %28, label %44, !dbg !844

; <label>:28:                                     ; preds = %23
  %29 = getelementptr inbounds [4097 x i8], [4097 x i8]* %6, i32 0, i32 0, !dbg !845
  %30 = call i32 @strlen(i8* %29) #9, !dbg !848
  %31 = load i8*, i8** %3, align 4, !dbg !849
  %32 = call i32 @strlen(i8* %31) #9, !dbg !850
  %33 = add i32 %30, %32, !dbg !852
  %34 = icmp ule i32 %33, 4096, !dbg !853
  br i1 %34, label %35, label %39, !dbg !854

; <label>:35:                                     ; preds = %28
  %36 = getelementptr inbounds [4097 x i8], [4097 x i8]* %6, i32 0, i32 0, !dbg !855
  %37 = load i8*, i8** %3, align 4, !dbg !856
  %38 = call i8* @strcat(i8* %36, i8* %37) #7, !dbg !857
  br label %43, !dbg !857

; <label>:39:                                     ; preds = %28
  %40 = getelementptr inbounds [4097 x i8], [4097 x i8]* %6, i32 0, i32 0, !dbg !858
  %41 = load i8*, i8** %3, align 4, !dbg !859
  %42 = call i8* @strcpy(i8* %40, i8* %41) #7, !dbg !860
  br label %43

; <label>:43:                                     ; preds = %39, %35
  br label %51, !dbg !861

; <label>:44:                                     ; preds = %23
  %45 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !862
  %46 = load i32, i32* %4, align 4, !dbg !862
  call void @__AMI_fake_direct_transfer(), !dbg !862
  %47 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %45, i8* getelementptr inbounds ([80 x i8], [80 x i8]* @.str.43, i32 0, i32 0), i32 %46), !dbg !862
  %48 = getelementptr inbounds [4097 x i8], [4097 x i8]* %6, i32 0, i32 0, !dbg !864
  %49 = load i8*, i8** %3, align 4, !dbg !865
  %50 = call i8* @strcpy(i8* %48, i8* %49) #7, !dbg !866
  br label %51

; <label>:51:                                     ; preds = %44, %43
  br label %56, !dbg !867

; <label>:52:                                     ; preds = %17
  %53 = getelementptr inbounds [4097 x i8], [4097 x i8]* %6, i32 0, i32 0, !dbg !868
  %54 = load i8*, i8** %3, align 4, !dbg !869
  %55 = call i8* @strcpy(i8* %53, i8* %54) #7, !dbg !870
  br label %56

; <label>:56:                                     ; preds = %52, %51
  %57 = getelementptr inbounds [4097 x i8], [4097 x i8]* %6, i32 0, i32 0, !dbg !871
  %58 = call %struct._IO_FILE* @fopen(i8* %57, i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.1.44, i32 0, i32 0)), !dbg !872
  store %struct._IO_FILE* %58, %struct._IO_FILE** %5, align 4, !dbg !873
  %59 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !874
  %60 = icmp ne %struct._IO_FILE* %59, null, !dbg !876
  br i1 %60, label %61, label %203, !dbg !877

; <label>:61:                                     ; preds = %56
  call void @llvm.dbg.declare(metadata [2084 x i8]* %7, metadata !878, metadata !336), !dbg !883
  %62 = getelementptr inbounds [2084 x i8], [2084 x i8]* %7, i32 0, i32 0, !dbg !884
  store i8 0, i8* %62, align 1, !dbg !885
  store i8 0, i8* getelementptr inbounds ([81 x i8], [81 x i8]* @Token_id, i32 0, i32 0), align 1, !dbg !886
  store i8 0, i8* getelementptr inbounds ([81 x i8], [81 x i8]* @User_id, i32 0, i32 0), align 1, !dbg !887
  %63 = call i8* @strcpy(i8* getelementptr inbounds ([65 x i8], [65 x i8]* @Server_path, i32 0, i32 0), i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.2.45, i32 0, i32 0)) #7, !dbg !888
  store i32 0, i32* %4, align 4, !dbg !889
  br label %64, !dbg !890

; <label>:64:                                     ; preds = %89, %61
  %65 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !891
  %66 = call i32 @feof(%struct._IO_FILE* %65) #7, !dbg !893
  %67 = icmp ne i32 %66, 0, !dbg !893
  br i1 %67, label %71, label %68, !dbg !894

; <label>:68:                                     ; preds = %64
  %69 = load i32, i32* %4, align 4, !dbg !895
  %70 = icmp eq i32 %69, 0, !dbg !897
  br label %71

; <label>:71:                                     ; preds = %68, %64
  %72 = phi i1 [ false, %64 ], [ %70, %68 ]
  br i1 %72, label %73, label %90, !dbg !898

; <label>:73:                                     ; preds = %71
  %74 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !900
  %75 = getelementptr inbounds [2084 x i8], [2084 x i8]* %7, i32 0, i32 0, !dbg !903
  %76 = call i32 (%struct._IO_FILE*, i8*, ...) @__isoc99_fscanf(%struct._IO_FILE* %74, i8* getelementptr inbounds ([21 x i8], [21 x i8]* @.str.3.46, i32 0, i32 0), i8* %75), !dbg !904
  %77 = icmp eq i32 %76, 0, !dbg !905
  br i1 %77, label %78, label %89, !dbg !906

; <label>:78:                                     ; preds = %73
  %79 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !907
  %80 = call i32 (%struct._IO_FILE*, i8*, ...) @__isoc99_fscanf(%struct._IO_FILE* %79, i8* getelementptr inbounds ([14 x i8], [14 x i8]* @.str.4.47, i32 0, i32 0), i8* getelementptr inbounds ([81 x i8], [81 x i8]* @Token_id, i32 0, i32 0)), !dbg !908
  %81 = icmp eq i32 %80, 0, !dbg !909
  br i1 %81, label %82, label %89, !dbg !910

; <label>:82:                                     ; preds = %78
  %83 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !911
  %84 = call i32 (%struct._IO_FILE*, i8*, ...) @__isoc99_fscanf(%struct._IO_FILE* %83, i8* getelementptr inbounds ([13 x i8], [13 x i8]* @.str.5.48, i32 0, i32 0), i8* getelementptr inbounds ([81 x i8], [81 x i8]* @User_id, i32 0, i32 0)), !dbg !912
  %85 = icmp eq i32 %84, 0, !dbg !913
  br i1 %85, label %86, label %89, !dbg !914

; <label>:86:                                     ; preds = %82
  %87 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !916
  call void @__AMI_fake_direct_transfer(), !dbg !916
  %88 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %87, i8* getelementptr inbounds ([73 x i8], [73 x i8]* @.str.6.49, i32 0, i32 0)), !dbg !916
  store i32 22, i32* %4, align 4, !dbg !918
  br label %89, !dbg !919

; <label>:89:                                     ; preds = %86, %82, %78, %73
  br label %64, !dbg !920, !llvm.loop !922

; <label>:90:                                     ; preds = %71
  %91 = load i32, i32* %4, align 4, !dbg !923
  %92 = icmp eq i32 %91, 0, !dbg !925
  br i1 %92, label %93, label %200, !dbg !926

; <label>:93:                                     ; preds = %90
  %94 = getelementptr inbounds [2084 x i8], [2084 x i8]* %7, i32 0, i32 0, !dbg !927
  %95 = call i32 @strlen(i8* %94) #9, !dbg !930
  %96 = icmp ugt i32 %95, 0, !dbg !931
  br i1 %96, label %97, label %196, !dbg !932

; <label>:97:                                     ; preds = %93
  %98 = call i32 @strlen(i8* getelementptr inbounds ([81 x i8], [81 x i8]* @Token_id, i32 0, i32 0)) #9, !dbg !933
  %99 = icmp ugt i32 %98, 0, !dbg !936
  br i1 %99, label %100, label %192, !dbg !937

; <label>:100:                                    ; preds = %97
  %101 = call i32 @strlen(i8* getelementptr inbounds ([81 x i8], [81 x i8]* @User_id, i32 0, i32 0)) #9, !dbg !938
  %102 = icmp ugt i32 %101, 0, !dbg !941
  br i1 %102, label %103, label %188, !dbg !942

; <label>:103:                                    ; preds = %100
  %104 = getelementptr inbounds [2084 x i8], [2084 x i8]* %7, i32 0, i32 0, !dbg !943
  %105 = call i32 @strncmp(i8* %104, i8* getelementptr inbounds ([8 x i8], [8 x i8]* @.str.7.50, i32 0, i32 0), i32 7) #9, !dbg !946
  %106 = icmp eq i32 %105, 0, !dbg !947
  br i1 %106, label %107, label %184, !dbg !948

; <label>:107:                                    ; preds = %103
  call void @llvm.dbg.declare(metadata i8** %8, metadata !949, metadata !336), !dbg !951
  call void @llvm.dbg.declare(metadata i8** %9, metadata !952, metadata !336), !dbg !953
  call void @llvm.dbg.declare(metadata i8** %10, metadata !954, metadata !336), !dbg !955
  call void @llvm.dbg.declare(metadata i32* %11, metadata !956, metadata !336), !dbg !957
  %108 = getelementptr inbounds [2084 x i8], [2084 x i8]* %7, i32 0, i32 0, !dbg !958
  %109 = getelementptr inbounds i8, i8* %108, i32 7, !dbg !959
  %110 = call i8* @strchr(i8* %109, i32 64) #9, !dbg !960
  store i8* %110, i8** %8, align 4, !dbg !961
  %111 = load i8*, i8** %8, align 4, !dbg !962
  %112 = icmp eq i8* %111, null, !dbg !964
  br i1 %112, label %113, label %116, !dbg !965

; <label>:113:                                    ; preds = %107
  %114 = getelementptr inbounds [2084 x i8], [2084 x i8]* %7, i32 0, i32 0, !dbg !966
  %115 = getelementptr inbounds i8, i8* %114, i32 7, !dbg !967
  store i8* %115, i8** %8, align 4, !dbg !968
  br label %119, !dbg !969

; <label>:116:                                    ; preds = %107
  %117 = load i8*, i8** %8, align 4, !dbg !970
  %118 = getelementptr inbounds i8, i8* %117, i32 1, !dbg !970
  store i8* %118, i8** %8, align 4, !dbg !970
  br label %119

; <label>:119:                                    ; preds = %116, %113
  %120 = load i8*, i8** %8, align 4, !dbg !971
  %121 = call i8* @strchr(i8* %120, i32 58) #9, !dbg !972
  store i8* %121, i8** %9, align 4, !dbg !973
  %122 = load i8*, i8** %9, align 4, !dbg !974
  %123 = icmp eq i8* %122, null, !dbg !976
  br i1 %123, label %124, label %135, !dbg !977

; <label>:124:                                    ; preds = %119
  call void @__AMI_fake_local_wrt(), !dbg !978
  store i32 3000, i32* @Server_port, align 4, !dbg !978
  %125 = load i8*, i8** %8, align 4, !dbg !980
  %126 = call i8* @strchr(i8* %125, i32 47) #9, !dbg !981
  store i8* %126, i8** %9, align 4, !dbg !982
  %127 = load i8*, i8** %9, align 4, !dbg !983
  %128 = icmp eq i8* %127, null, !dbg !985
  br i1 %128, label %129, label %134, !dbg !986

; <label>:129:                                    ; preds = %124
  %130 = load i8*, i8** %8, align 4, !dbg !987
  %131 = load i8*, i8** %8, align 4, !dbg !988
  %132 = call i32 @strlen(i8* %131) #9, !dbg !989
  %133 = getelementptr inbounds i8, i8* %130, i32 %132, !dbg !990
  store i8* %133, i8** %9, align 4, !dbg !991
  br label %134, !dbg !992

; <label>:134:                                    ; preds = %129, %124
  br label %142, !dbg !993

; <label>:135:                                    ; preds = %119
  %136 = load i8*, i8** %9, align 4, !dbg !994
  %137 = getelementptr inbounds i8, i8* %136, i32 1, !dbg !997
  %138 = call i32 (i8*, i8*, ...) @__isoc99_sscanf(i8* %137, i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.8.51, i32 0, i32 0), i32* @Server_port) #7, !dbg !998
  %139 = icmp eq i32 %138, 0, !dbg !999
  br i1 %139, label %140, label %141, !dbg !1000

; <label>:140:                                    ; preds = %135
  call void @__AMI_fake_local_wrt(), !dbg !1001
  store i32 3000, i32* @Server_port, align 4, !dbg !1001
  br label %141, !dbg !1002

; <label>:141:                                    ; preds = %140, %135
  br label %142

; <label>:142:                                    ; preds = %141, %134
  %143 = load i8*, i8** %9, align 4, !dbg !1003
  %144 = call i8* @strchr(i8* %143, i32 47) #9, !dbg !1004
  store i8* %144, i8** %10, align 4, !dbg !1005
  %145 = load i8*, i8** %10, align 4, !dbg !1006
  %146 = icmp ne i8* %145, null, !dbg !1008
  br i1 %146, label %147, label %158, !dbg !1009

; <label>:147:                                    ; preds = %142
  call void @llvm.dbg.declare(metadata i32* %12, metadata !1010, metadata !336), !dbg !1012
  %148 = load i8*, i8** %10, align 4, !dbg !1013
  %149 = call i32 @strlen(i8* %148) #9, !dbg !1014
  store i32 %149, i32* %12, align 4, !dbg !1015
  %150 = load i32, i32* %12, align 4, !dbg !1016
  %151 = icmp ule i32 %150, 2083, !dbg !1018
  br i1 %151, label %152, label %157, !dbg !1019

; <label>:152:                                    ; preds = %147
  %153 = load i8*, i8** %10, align 4, !dbg !1020
  %154 = load i32, i32* %12, align 4, !dbg !1022
  call void @llvm.memcpy.p0i8.p0i8.i32(i8* getelementptr inbounds ([65 x i8], [65 x i8]* @Server_path, i32 0, i32 0), i8* %153, i32 %154, i32 1, i1 false), !dbg !1023
  %155 = load i32, i32* %12, align 4, !dbg !1024
  %156 = getelementptr inbounds [65 x i8], [65 x i8]* @Server_path, i32 0, i32 %155, !dbg !1025
  store i8 0, i8* %156, align 1, !dbg !1026
  br label %157, !dbg !1027

; <label>:157:                                    ; preds = %152, %147
  br label %158, !dbg !1028

; <label>:158:                                    ; preds = %157, %142
  %159 = load i8*, i8** %9, align 4, !dbg !1029
  %160 = load i8*, i8** %8, align 4, !dbg !1030
  %161 = ptrtoint i8* %159 to i32, !dbg !1031
  %162 = ptrtoint i8* %160 to i32, !dbg !1031
  %163 = sub i32 %161, %162, !dbg !1031
  store i32 %163, i32* %11, align 4, !dbg !1032
  %164 = load i32, i32* %11, align 4, !dbg !1033
  %165 = icmp ule i32 %164, 64, !dbg !1035
  br i1 %165, label %166, label %180, !dbg !1036

; <label>:166:                                    ; preds = %158
  %167 = load i8*, i8** %8, align 4, !dbg !1037
  %168 = load i32, i32* %11, align 4, !dbg !1039
  call void @llvm.memcpy.p0i8.p0i8.i32(i8* getelementptr inbounds ([65 x i8], [65 x i8]* @Server_name, i32 0, i32 0), i8* %167, i32 %168, i32 1, i1 false), !dbg !1040
  %169 = load i32, i32* %11, align 4, !dbg !1041
  %170 = getelementptr inbounds [65 x i8], [65 x i8]* @Server_name, i32 0, i32 %169, !dbg !1042
  store i8 0, i8* %170, align 1, !dbg !1043
  %171 = call i32 @hostname_to_ip(i8* getelementptr inbounds ([65 x i8], [65 x i8]* @Server_name, i32 0, i32 0), %struct.in_addr* @Server_ip), !dbg !1044
  store i32 %171, i32* %4, align 4, !dbg !1045
  %172 = load i32, i32* %4, align 4, !dbg !1046
  %173 = icmp eq i32 %172, 0, !dbg !1048
  br i1 %173, label %174, label %179, !dbg !1049

; <label>:174:                                    ; preds = %166
  %175 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1050
  %176 = load [1 x i32], [1 x i32]* bitcast (%struct.in_addr* @Server_ip to [1 x i32]*), align 4, !dbg !1050
  %177 = call i8* @inet_ntoa([1 x i32] %176) #7, !dbg !1050
  call void @__AMI_fake_direct_transfer(), !dbg !1052
  %178 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %175, i8* getelementptr inbounds ([44 x i8], [44 x i8]* @.str.9.52, i32 0, i32 0), i8* %177), !dbg !1052
  br label %179, !dbg !1054

; <label>:179:                                    ; preds = %174, %166
  br label %183, !dbg !1055

; <label>:180:                                    ; preds = %158
  %181 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1056
  call void @__AMI_fake_direct_transfer(), !dbg !1056
  %182 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %181, i8* getelementptr inbounds ([86 x i8], [86 x i8]* @.str.10.53, i32 0, i32 0)), !dbg !1056
  store i32 22, i32* %4, align 4, !dbg !1058
  br label %183

; <label>:183:                                    ; preds = %180, %179
  br label %187, !dbg !1059

; <label>:184:                                    ; preds = %103
  %185 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1060
  call void @__AMI_fake_direct_transfer(), !dbg !1060
  %186 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %185, i8* getelementptr inbounds ([69 x i8], [69 x i8]* @.str.11.54, i32 0, i32 0)), !dbg !1060
  store i32 22, i32* %4, align 4, !dbg !1062
  br label %187

; <label>:187:                                    ; preds = %184, %183
  br label %191, !dbg !1063

; <label>:188:                                    ; preds = %100
  %189 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1064
  call void @__AMI_fake_direct_transfer(), !dbg !1064
  %190 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %189, i8* getelementptr inbounds ([55 x i8], [55 x i8]* @.str.12.55, i32 0, i32 0)), !dbg !1064
  store i32 22, i32* %4, align 4, !dbg !1066
  br label %191

; <label>:191:                                    ; preds = %188, %187
  br label %195, !dbg !1067

; <label>:192:                                    ; preds = %97
  %193 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1068
  call void @__AMI_fake_direct_transfer(), !dbg !1068
  %194 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %193, i8* getelementptr inbounds ([56 x i8], [56 x i8]* @.str.13.56, i32 0, i32 0)), !dbg !1068
  store i32 22, i32* %4, align 4, !dbg !1070
  br label %195

; <label>:195:                                    ; preds = %192, %191
  br label %199, !dbg !1071

; <label>:196:                                    ; preds = %93
  %197 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1072
  call void @__AMI_fake_direct_transfer(), !dbg !1072
  %198 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %197, i8* getelementptr inbounds ([58 x i8], [58 x i8]* @.str.14.57, i32 0, i32 0)), !dbg !1072
  store i32 22, i32* %4, align 4, !dbg !1074
  br label %199

; <label>:199:                                    ; preds = %196, %195
  br label %200, !dbg !1075

; <label>:200:                                    ; preds = %199, %90
  %201 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !1076
  %202 = call i32 @fclose(%struct._IO_FILE* %201), !dbg !1077
  br label %211, !dbg !1078

; <label>:203:                                    ; preds = %56
  %204 = call i32* @__errno_location() #1, !dbg !1079
  %205 = load i32, i32* %204, align 4, !dbg !1079
  store i32 %205, i32* %4, align 4, !dbg !1081
  %206 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1082
  %207 = getelementptr inbounds [4097 x i8], [4097 x i8]* %6, i32 0, i32 0, !dbg !1082
  %208 = call i32* @__errno_location() #1, !dbg !1082
  %209 = load i32, i32* %208, align 4, !dbg !1082
  call void @__AMI_fake_direct_transfer(), !dbg !1083
  %210 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %206, i8* getelementptr inbounds ([49 x i8], [49 x i8]* @.str.15.58, i32 0, i32 0), i8* %207, i32 %209), !dbg !1083
  br label %211

; <label>:211:                                    ; preds = %203, %200
  %212 = load i32, i32* %4, align 4, !dbg !1085
  store i32 %212, i32* %2, align 4, !dbg !1086
  br label %213, !dbg !1086

; <label>:213:                                    ; preds = %211, %16
  %214 = load i32, i32* %2, align 4, !dbg !1087
  ret i32 %214, !dbg !1087
}

; Function Attrs: nounwind readonly
declare i32 @strlen(i8*) #6 section ".CODE_REGION_1_"

; Function Attrs: nounwind
declare i8* @strcat(i8*, i8*) #2 section ".CODE_REGION_2_"

declare %struct._IO_FILE* @fopen(i8*, i8*) #5 section ".CODE_REGION_2_"

; Function Attrs: nounwind
declare i32 @feof(%struct._IO_FILE*) #2 section ".CODE_REGION_2_"

declare i32 @__isoc99_fscanf(%struct._IO_FILE*, i8*, ...) #5 section ".CODE_REGION_1_"

; Function Attrs: nounwind readonly
declare i32 @strncmp(i8*, i8*, i32) #6 section ".CODE_REGION_2_"

; Function Attrs: nounwind readonly
declare i8* @strchr(i8*, i32) #6 section ".CODE_REGION_2_"

; Function Attrs: nounwind
declare i32 @__isoc99_sscanf(i8*, i8*, ...) #2 section ".CODE_REGION_2_"

; Function Attrs: argmemonly nounwind
declare void @llvm.memcpy.p0i8.p0i8.i32(i8* nocapture writeonly, i8* nocapture readonly, i32, i32, i1) #3

; Function Attrs: nounwind
declare i8* @inet_ntoa([1 x i32]) #2 section ".CODE_REGION_2_"

declare i32 @fclose(%struct._IO_FILE*) #5 section ".CODE_REGION_1_"

; Function Attrs: nounwind
define i32 @send_notification(i8*, i8*) #0 section ".CODE_REGION_1_" !dbg !1088 {
  %3 = alloca i8*, align 4
  %4 = alloca i8*, align 4
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  %7 = alloca %struct.sockaddr_in, align 4
  %8 = alloca %struct._IO_FILE*, align 4
  %9 = alloca i32, align 4
  %10 = alloca i32, align 4
  %11 = alloca i32, align 4
  %12 = alloca [2084 x i8], align 1
  %13 = alloca i8*, align 4
  %14 = alloca i32, align 4
  %15 = alloca i32, align 4
  %16 = alloca i32, align 4
  %17 = alloca i32, align 4
  %18 = alloca [2084 x i8], align 1
  %19 = alloca [2084 x i8], align 1
  store i8* %0, i8** %3, align 4
  call void @llvm.dbg.declare(metadata i8** %3, metadata !1089, metadata !336), !dbg !1090
  store i8* %1, i8** %4, align 4
  call void @llvm.dbg.declare(metadata i8** %4, metadata !1091, metadata !336), !dbg !1092
  call void @llvm.dbg.declare(metadata i32* %5, metadata !1093, metadata !336), !dbg !1094
  store i32 0, i32* %5, align 4, !dbg !1094
  call void @llvm.dbg.declare(metadata i32* %6, metadata !1095, metadata !336), !dbg !1096
  call void @llvm.dbg.declare(metadata %struct.sockaddr_in* %7, metadata !1097, metadata !336), !dbg !1104
  %20 = call i32 @socket(i32 2, i32 1, i32 0) #7, !dbg !1105
  store i32 %20, i32* %6, align 4, !dbg !1106
  %21 = load i32, i32* %6, align 4, !dbg !1107
  %22 = icmp ne i32 %21, -1, !dbg !1109
  br i1 %22, label %23, label %214, !dbg !1110

; <label>:23:                                     ; preds = %2
  %24 = bitcast %struct.sockaddr_in* %7 to i8*, !dbg !1111
  call void @llvm.memset.p0i8.i32(i8* %24, i8 0, i32 16, i32 4, i1 false), !dbg !1111
  %25 = getelementptr inbounds %struct.sockaddr_in, %struct.sockaddr_in* %7, i32 0, i32 0, !dbg !1113
  store i16 2, i16* %25, align 4, !dbg !1114
  %26 = load i32, i32* @Server_port, align 4, !dbg !1115
  %27 = trunc i32 %26 to i16, !dbg !1115
  %28 = call zeroext i16 @htons(i16 zeroext %27) #1, !dbg !1116
  %29 = getelementptr inbounds %struct.sockaddr_in, %struct.sockaddr_in* %7, i32 0, i32 1, !dbg !1117
  store i16 %28, i16* %29, align 2, !dbg !1118
  %30 = getelementptr inbounds %struct.sockaddr_in, %struct.sockaddr_in* %7, i32 0, i32 2, !dbg !1119
  %31 = bitcast %struct.in_addr* %30 to i8*, !dbg !1120
  call void @llvm.memcpy.p0i8.p0i8.i32(i8* %31, i8* bitcast (%struct.in_addr* @Server_ip to i8*), i32 4, i32 4, i1 false), !dbg !1120
  %32 = load i32, i32* %6, align 4, !dbg !1121
  %33 = bitcast %struct.sockaddr_in* %7 to %struct.sockaddr*, !dbg !1122
  %34 = call i32 @connect(i32 %32, %struct.sockaddr* %33, i32 16), !dbg !1123
  store i32 %34, i32* %5, align 4, !dbg !1124
  %35 = load i32, i32* %5, align 4, !dbg !1125
  %36 = icmp eq i32 %35, 0, !dbg !1127
  br i1 %36, label %37, label %201, !dbg !1128

; <label>:37:                                     ; preds = %23
  call void @llvm.dbg.declare(metadata %struct._IO_FILE** %8, metadata !1129, metadata !336), !dbg !1131
  %38 = load i32, i32* %6, align 4, !dbg !1132
  %39 = call %struct._IO_FILE* @fdopen(i32 %38, i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str.16.61, i32 0, i32 0)) #7, !dbg !1133
  store %struct._IO_FILE* %39, %struct._IO_FILE** %8, align 4, !dbg !1134
  %40 = load %struct._IO_FILE*, %struct._IO_FILE** %8, align 4, !dbg !1135
  %41 = icmp ne %struct._IO_FILE* %40, null, !dbg !1137
  br i1 %41, label %42, label %190, !dbg !1138

; <label>:42:                                     ; preds = %37
  call void @llvm.dbg.declare(metadata i32* %9, metadata !1139, metadata !336), !dbg !1141
  call void @llvm.dbg.declare(metadata i32* %10, metadata !1142, metadata !336), !dbg !1143
  call void @llvm.dbg.declare(metadata i32* %11, metadata !1144, metadata !336), !dbg !1145
  %43 = call i32 @strlen(i8* getelementptr inbounds ([81 x i8], [81 x i8]* @Token_id, i32 0, i32 0)) #9, !dbg !1146
  %44 = add i32 6, %43, !dbg !1147
  %45 = add i32 %44, 1, !dbg !1148
  %46 = add i32 %45, 5, !dbg !1149
  %47 = call i32 @strlen(i8* getelementptr inbounds ([81 x i8], [81 x i8]* @User_id, i32 0, i32 0)) #9, !dbg !1150
  %48 = add i32 %46, %47, !dbg !1152
  %49 = add i32 %48, 1, !dbg !1153
  %50 = add i32 %49, 8, !dbg !1154
  %51 = load i8*, i8** %3, align 4, !dbg !1155
  %52 = call i32 @strlen(i8* %51) #9, !dbg !1156
  %53 = add i32 %50, %52, !dbg !1158
  %54 = add i32 %53, 1, !dbg !1159
  %55 = add i32 %54, 9, !dbg !1160
  %56 = load i8*, i8** %4, align 4, !dbg !1161
  %57 = call i32 @strlen(i8* %56) #9, !dbg !1162
  %58 = add i32 %55, %57, !dbg !1164
  store i32 %58, i32* %9, align 4, !dbg !1165
  %59 = load i8*, i8** %4, align 4, !dbg !1166
  %60 = call i32 @strcmp(i8* %59, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.17.62, i32 0, i32 0)) #9, !dbg !1168
  %61 = icmp eq i32 %60, 0, !dbg !1169
  br i1 %61, label %62, label %65, !dbg !1170

; <label>:62:                                     ; preds = %42
  %63 = load i32, i32* %9, align 4, !dbg !1171
  %64 = add i32 %63, 20, !dbg !1171
  store i32 %64, i32* %9, align 4, !dbg !1171
  br label %65, !dbg !1172

; <label>:65:                                     ; preds = %62, %42
  %66 = load %struct._IO_FILE*, %struct._IO_FILE** %8, align 4, !dbg !1173
  %67 = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %66, i8* getelementptr inbounds ([19 x i8], [19 x i8]* @.str.18.63, i32 0, i32 0), i8* getelementptr inbounds ([65 x i8], [65 x i8]* @Server_path, i32 0, i32 0)), !dbg !1174
  %68 = load %struct._IO_FILE*, %struct._IO_FILE** %8, align 4, !dbg !1175
  %69 = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %68, i8* getelementptr inbounds ([11 x i8], [11 x i8]* @.str.19.64, i32 0, i32 0), i8* getelementptr inbounds ([65 x i8], [65 x i8]* @Server_name, i32 0, i32 0)), !dbg !1176
  %70 = load %struct._IO_FILE*, %struct._IO_FILE** %8, align 4, !dbg !1177
  %71 = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %70, i8* getelementptr inbounds ([50 x i8], [50 x i8]* @.str.20.65, i32 0, i32 0)), !dbg !1178
  %72 = load %struct._IO_FILE*, %struct._IO_FILE** %8, align 4, !dbg !1179
  %73 = load i32, i32* %9, align 4, !dbg !1180
  %74 = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %72, i8* getelementptr inbounds ([24 x i8], [24 x i8]* @.str.21.66, i32 0, i32 0), i32 %73), !dbg !1181
  %75 = load %struct._IO_FILE*, %struct._IO_FILE** %8, align 4, !dbg !1182
  %76 = load i8*, i8** %3, align 4, !dbg !1183
  %77 = load i8*, i8** %4, align 4, !dbg !1184
  %78 = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %75, i8* getelementptr inbounds ([40 x i8], [40 x i8]* @.str.22.67, i32 0, i32 0), i8* getelementptr inbounds ([81 x i8], [81 x i8]* @Token_id, i32 0, i32 0), i8* getelementptr inbounds ([81 x i8], [81 x i8]* @User_id, i32 0, i32 0), i8* %76, i8* %77), !dbg !1185
  %79 = load i8*, i8** %4, align 4, !dbg !1186
  %80 = call i32 @strcmp(i8* %79, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.17.62, i32 0, i32 0)) #9, !dbg !1188
  %81 = icmp eq i32 %80, 0, !dbg !1189
  br i1 %81, label %82, label %85, !dbg !1190

; <label>:82:                                     ; preds = %65
  %83 = load %struct._IO_FILE*, %struct._IO_FILE** %8, align 4, !dbg !1191
  %84 = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %83, i8* getelementptr inbounds ([21 x i8], [21 x i8]* @.str.23, i32 0, i32 0)), !dbg !1192
  br label %85, !dbg !1192

; <label>:85:                                     ; preds = %82, %65
  %86 = load %struct._IO_FILE*, %struct._IO_FILE** %8, align 4, !dbg !1193
  %87 = call i32 (%struct._IO_FILE*, i8*, ...) @__isoc99_fscanf(%struct._IO_FILE* %86, i8* getelementptr inbounds ([23 x i8], [23 x i8]* @.str.24, i32 0, i32 0), i32* %10), !dbg !1194
  store i32 %87, i32* %11, align 4, !dbg !1195
  %88 = load i32, i32* %11, align 4, !dbg !1196
  %89 = icmp eq i32 %88, 1, !dbg !1198
  br i1 %89, label %90, label %179, !dbg !1199

; <label>:90:                                     ; preds = %85
  %91 = load i32, i32* %10, align 4, !dbg !1200
  %92 = icmp eq i32 %91, 200, !dbg !1203
  br i1 %92, label %93, label %174, !dbg !1204

; <label>:93:                                     ; preds = %90
  call void @llvm.dbg.declare(metadata [2084 x i8]* %12, metadata !1205, metadata !336), !dbg !1207
  call void @llvm.dbg.declare(metadata i8** %13, metadata !1208, metadata !336), !dbg !1209
  call void @llvm.dbg.declare(metadata i32* %14, metadata !1210, metadata !336), !dbg !1211
  call void @llvm.dbg.declare(metadata i32* %15, metadata !1212, metadata !336), !dbg !1213
  store i32 0, i32* %15, align 4, !dbg !1214
  store i32 0, i32* %14, align 4, !dbg !1215
  br label %94, !dbg !1216

; <label>:94:                                     ; preds = %111, %93
  %95 = getelementptr inbounds [2084 x i8], [2084 x i8]* %12, i32 0, i32 0, !dbg !1217
  %96 = load %struct._IO_FILE*, %struct._IO_FILE** %8, align 4, !dbg !1219
  %97 = call i8* @fgets(i8* %95, i32 2083, %struct._IO_FILE* %96), !dbg !1220
  store i8* %97, i8** %13, align 4, !dbg !1221
  %98 = icmp ne i8* %97, null, !dbg !1222
  br i1 %98, label %99, label %112, !dbg !1223

; <label>:99:                                     ; preds = %94
  %100 = getelementptr inbounds [2084 x i8], [2084 x i8]* %12, i32 0, i32 0, !dbg !1224
  %101 = load i8, i8* %100, align 1, !dbg !1224
  %102 = zext i8 %101 to i32, !dbg !1224
  %103 = icmp eq i32 %102, 13, !dbg !1227
  br i1 %103, label %104, label %105, !dbg !1228

; <label>:104:                                    ; preds = %99
  br label %112, !dbg !1229

; <label>:105:                                    ; preds = %99
  %106 = load i32, i32* %14, align 4, !dbg !1230
  %107 = add i32 %106, 1, !dbg !1230
  store i32 %107, i32* %14, align 4, !dbg !1230
  %108 = load i32, i32* %14, align 4, !dbg !1231
  %109 = icmp ugt i32 %108, 1024, !dbg !1233
  br i1 %109, label %110, label %111, !dbg !1234

; <label>:110:                                    ; preds = %105
  store i8* null, i8** %13, align 4, !dbg !1235
  store i32 1, i32* %15, align 4, !dbg !1237
  br label %112, !dbg !1238

; <label>:111:                                    ; preds = %105
  br label %94, !dbg !1239, !llvm.loop !1241

; <label>:112:                                    ; preds = %110, %104, %94
  %113 = load i8*, i8** %13, align 4, !dbg !1242
  %114 = icmp ne i8* %113, null, !dbg !1244
  br i1 %114, label %115, label %161, !dbg !1245

; <label>:115:                                    ; preds = %112
  call void @llvm.dbg.declare(metadata i32* %16, metadata !1246, metadata !336), !dbg !1248
  call void @llvm.dbg.declare(metadata i32* %17, metadata !1249, metadata !336), !dbg !1250
  call void @llvm.dbg.declare(metadata [2084 x i8]* %18, metadata !1251, metadata !336), !dbg !1252
  call void @llvm.dbg.declare(metadata [2084 x i8]* %19, metadata !1253, metadata !336), !dbg !1254
  %116 = load %struct._IO_FILE*, %struct._IO_FILE** %8, align 4, !dbg !1255
  %117 = call i32 (%struct._IO_FILE*, i8*, ...) @__isoc99_fscanf(%struct._IO_FILE* %116, i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str.25, i32 0, i32 0)), !dbg !1256
  store i32 0, i32* %17, align 4, !dbg !1257
  br label %118, !dbg !1258

; <label>:118:                                    ; preds = %142, %115
  %119 = load %struct._IO_FILE*, %struct._IO_FILE** %8, align 4, !dbg !1259
  %120 = getelementptr inbounds [2084 x i8], [2084 x i8]* %18, i32 0, i32 0, !dbg !1261
  %121 = call i32 (%struct._IO_FILE*, i8*, ...) @__isoc99_fscanf(%struct._IO_FILE* %119, i8* getelementptr inbounds ([12 x i8], [12 x i8]* @.str.26, i32 0, i32 0), i8* %120), !dbg !1262
  %122 = icmp eq i32 %121, 1, !dbg !1263
  br i1 %122, label %123, label %143, !dbg !1264

; <label>:123:                                    ; preds = %118
  %124 = load %struct._IO_FILE*, %struct._IO_FILE** %8, align 4, !dbg !1265
  %125 = call i32 (%struct._IO_FILE*, i8*, ...) @__isoc99_fscanf(%struct._IO_FILE* %124, i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.27, i32 0, i32 0)), !dbg !1267
  %126 = load %struct._IO_FILE*, %struct._IO_FILE** %8, align 4, !dbg !1268
  %127 = getelementptr inbounds [2084 x i8], [2084 x i8]* %19, i32 0, i32 0, !dbg !1270
  %128 = call i32 (%struct._IO_FILE*, i8*, ...) @__isoc99_fscanf(%struct._IO_FILE* %126, i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.28, i32 0, i32 0), i8* %127), !dbg !1271
  %129 = icmp eq i32 %128, 1, !dbg !1272
  br i1 %129, label %130, label %142, !dbg !1273

; <label>:130:                                    ; preds = %123
  %131 = load %struct._IO_FILE*, %struct._IO_FILE** %8, align 4, !dbg !1274
  %132 = call i32 (%struct._IO_FILE*, i8*, ...) @__isoc99_fscanf(%struct._IO_FILE* %131, i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.27, i32 0, i32 0)), !dbg !1276
  %133 = load %struct._IO_FILE*, %struct._IO_FILE** %8, align 4, !dbg !1277
  %134 = call i32 (%struct._IO_FILE*, i8*, ...) @__isoc99_fscanf(%struct._IO_FILE* %133, i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.29, i32 0, i32 0)), !dbg !1278
  %135 = getelementptr inbounds [2084 x i8], [2084 x i8]* %18, i32 0, i32 0, !dbg !1279
  %136 = call i32 @strcmp(i8* %135, i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.30, i32 0, i32 0)) #9, !dbg !1281
  %137 = icmp eq i32 %136, 0, !dbg !1282
  br i1 %137, label %138, label %141, !dbg !1283

; <label>:138:                                    ; preds = %130
  %139 = getelementptr inbounds [2084 x i8], [2084 x i8]* %19, i32 0, i32 0, !dbg !1284
  %140 = call i32 @atoi(i8* %139) #9, !dbg !1286
  store i32 %140, i32* %16, align 4, !dbg !1287
  store i32 1, i32* %17, align 4, !dbg !1288
  br label %141, !dbg !1289

; <label>:141:                                    ; preds = %138, %130
  br label %142, !dbg !1290

; <label>:142:                                    ; preds = %141, %123
  br label %118, !dbg !1291, !llvm.loop !1293

; <label>:143:                                    ; preds = %118
  %144 = load %struct._IO_FILE*, %struct._IO_FILE** %8, align 4, !dbg !1294
  %145 = call i32 (%struct._IO_FILE*, i8*, ...) @__isoc99_fscanf(%struct._IO_FILE* %144, i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.31, i32 0, i32 0)), !dbg !1295
  %146 = load i32, i32* %17, align 4, !dbg !1296
  %147 = icmp ne i32 %146, 0, !dbg !1298
  br i1 %147, label %148, label %157, !dbg !1299

; <label>:148:                                    ; preds = %143
  %149 = load i32, i32* %16, align 4, !dbg !1300
  %150 = icmp eq i32 %149, 1, !dbg !1303
  br i1 %150, label %151, label %152, !dbg !1304

; <label>:151:                                    ; preds = %148
  store i32 0, i32* %5, align 4, !dbg !1305
  br label %156, !dbg !1307

; <label>:152:                                    ; preds = %148
  store i32 56, i32* %5, align 4, !dbg !1308
  %153 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1310
  %154 = load i32, i32* %16, align 4, !dbg !1310
  %155 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %153, i8* getelementptr inbounds ([52 x i8], [52 x i8]* @.str.32, i32 0, i32 0), i32 %154), !dbg !1310
  br label %156

; <label>:156:                                    ; preds = %152, %151
  br label %160, !dbg !1311

; <label>:157:                                    ; preds = %143
  store i32 71, i32* %5, align 4, !dbg !1312
  %158 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1314
  %159 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %158, i8* getelementptr inbounds ([89 x i8], [89 x i8]* @.str.33, i32 0, i32 0)), !dbg !1314
  br label %160

; <label>:160:                                    ; preds = %157, %156
  br label %173, !dbg !1315

; <label>:161:                                    ; preds = %112
  %162 = load i32, i32* %15, align 4, !dbg !1316
  %163 = icmp ne i32 %162, 0, !dbg !1319
  br i1 %163, label %164, label %167, !dbg !1320

; <label>:164:                                    ; preds = %161
  store i32 71, i32* %5, align 4, !dbg !1321
  %165 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1323
  %166 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %165, i8* getelementptr inbounds ([59 x i8], [59 x i8]* @.str.34, i32 0, i32 0)), !dbg !1323
  br label %172, !dbg !1324

; <label>:167:                                    ; preds = %161
  store i32 71, i32* %5, align 4, !dbg !1325
  %168 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1327
  %169 = call i32* @__errno_location() #1, !dbg !1327
  %170 = load i32, i32* %169, align 4, !dbg !1327
  %171 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %168, i8* getelementptr inbounds ([84 x i8], [84 x i8]* @.str.35, i32 0, i32 0), i32 %170), !dbg !1328
  br label %172

; <label>:172:                                    ; preds = %167, %164
  br label %173

; <label>:173:                                    ; preds = %172, %160
  br label %178, !dbg !1330

; <label>:174:                                    ; preds = %90
  store i32 56, i32* %5, align 4, !dbg !1331
  %175 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1333
  %176 = load i32, i32* %10, align 4, !dbg !1333
  %177 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %175, i8* getelementptr inbounds ([50 x i8], [50 x i8]* @.str.36, i32 0, i32 0), i32 %176), !dbg !1333
  br label %178

; <label>:178:                                    ; preds = %174, %173
  br label %187, !dbg !1334

; <label>:179:                                    ; preds = %85
  %180 = call i32* @__errno_location() #1, !dbg !1335
  %181 = load i32, i32* %180, align 4, !dbg !1335
  store i32 %181, i32* %5, align 4, !dbg !1337
  %182 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1338
  %183 = load i32, i32* %11, align 4, !dbg !1338
  %184 = call i32* @__errno_location() #1, !dbg !1338
  %185 = load i32, i32* %184, align 4, !dbg !1338
  %186 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %182, i8* getelementptr inbounds ([77 x i8], [77 x i8]* @.str.37, i32 0, i32 0), i32 %183, i32 %185), !dbg !1339
  br label %187

; <label>:187:                                    ; preds = %179, %178
  %188 = load %struct._IO_FILE*, %struct._IO_FILE** %8, align 4, !dbg !1341
  %189 = call i32 @fclose(%struct._IO_FILE* %188), !dbg !1342
  br label %200, !dbg !1343

; <label>:190:                                    ; preds = %37
  %191 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1344
  %192 = call i32* @__errno_location() #1, !dbg !1344
  %193 = load i32, i32* %192, align 4, !dbg !1344
  %194 = call i32* @__errno_location() #1, !dbg !1346
  %195 = load i32, i32* %194, align 4, !dbg !1344
  %196 = call i8* @strerror(i32 %195) #7, !dbg !1348
  %197 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %191, i8* getelementptr inbounds ([73 x i8], [73 x i8]* @.str.38, i32 0, i32 0), i32 %193, i8* %196), !dbg !1350
  %198 = load i32, i32* %6, align 4, !dbg !1352
  %199 = call i32 @close(i32 %198), !dbg !1353
  br label %200

; <label>:200:                                    ; preds = %190, %187
  br label %213, !dbg !1354

; <label>:201:                                    ; preds = %23
  %202 = call i32* @__errno_location() #1, !dbg !1355
  %203 = load i32, i32* %202, align 4, !dbg !1355
  store i32 %203, i32* %5, align 4, !dbg !1357
  %204 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1358
  %205 = call i32* @__errno_location() #1, !dbg !1358
  %206 = load i32, i32* %205, align 4, !dbg !1358
  %207 = call i32* @__errno_location() #1, !dbg !1359
  %208 = load i32, i32* %207, align 4, !dbg !1358
  %209 = call i8* @strerror(i32 %208) #7, !dbg !1361
  %210 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %204, i8* getelementptr inbounds ([51 x i8], [51 x i8]* @.str.39, i32 0, i32 0), i32 %206, i8* %209), !dbg !1363
  %211 = load i32, i32* %6, align 4, !dbg !1365
  %212 = call i32 @close(i32 %211), !dbg !1366
  br label %213

; <label>:213:                                    ; preds = %201, %200
  br label %221, !dbg !1367

; <label>:214:                                    ; preds = %2
  %215 = call i32* @__errno_location() #1, !dbg !1368
  %216 = load i32, i32* %215, align 4, !dbg !1368
  store i32 %216, i32* %5, align 4, !dbg !1370
  %217 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1371
  %218 = call i32* @__errno_location() #1, !dbg !1371
  %219 = load i32, i32* %218, align 4, !dbg !1371
  %220 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %217, i8* getelementptr inbounds ([67 x i8], [67 x i8]* @.str.40, i32 0, i32 0), i32 %219), !dbg !1372
  br label %221

; <label>:221:                                    ; preds = %214, %213
  %222 = load i32, i32* %5, align 4, !dbg !1374
  ret i32 %222, !dbg !1375
}

; Function Attrs: nounwind
declare i32 @socket(i32, i32, i32) #2 section ".CODE_REGION_1_"

; Function Attrs: nounwind readnone
declare zeroext i16 @htons(i16 zeroext) #4 section ".CODE_REGION_1_"

declare i32 @connect(i32, %struct.sockaddr*, i32) #5 section ".CODE_REGION_1_"

; Function Attrs: nounwind
declare %struct._IO_FILE* @fdopen(i32, i8*) #2 section ".CODE_REGION_1_"

declare i32 @fprintf(%struct._IO_FILE*, i8*, ...) #5 section ".CODE_REGION_1_"

declare i8* @fgets(i8*, i32, %struct._IO_FILE*) #5 section ".CODE_REGION_1_"

; Function Attrs: nounwind readonly
declare i32 @atoi(i8*) #6 section ".CODE_REGION_1_"

declare i32 @close(i32) #5 section ".CODE_REGION_1_"

; Function Attrs: nounwind
define i8* @herror_msg(i32) #0 section ".CODE_REGION_2_" !dbg !1376 {
  %2 = alloca i32, align 4
  %3 = alloca i8*, align 4
  store i32 %0, i32* %2, align 4
  call void @llvm.dbg.declare(metadata i32* %2, metadata !1379, metadata !336), !dbg !1380
  call void @llvm.dbg.declare(metadata i8** %3, metadata !1381, metadata !336), !dbg !1382
  %4 = load i32, i32* %2, align 4, !dbg !1383
  switch i32 %4, label %8 [
    i32 1, label %5
    i32 4, label %6
    i32 2, label %7
  ], !dbg !1384

; <label>:5:                                      ; preds = %1
  store i8* getelementptr inbounds ([23 x i8], [23 x i8]* @.str.68, i32 0, i32 0), i8** %3, align 4, !dbg !1385
  br label %9, !dbg !1387

; <label>:6:                                      ; preds = %1
  store i8* getelementptr inbounds ([35 x i8], [35 x i8]* @.str.1.69, i32 0, i32 0), i8** %3, align 4, !dbg !1388
  br label %9, !dbg !1389

; <label>:7:                                      ; preds = %1
  store i8* getelementptr inbounds ([25 x i8], [25 x i8]* @.str.2.70, i32 0, i32 0), i8** %3, align 4, !dbg !1390
  br label %9, !dbg !1391

; <label>:8:                                      ; preds = %1
  store i8* getelementptr inbounds ([17 x i8], [17 x i8]* @.str.3.71, i32 0, i32 0), i8** %3, align 4, !dbg !1392
  br label %9, !dbg !1393

; <label>:9:                                      ; preds = %8, %7, %6, %5
  %10 = load i8*, i8** %3, align 4, !dbg !1394
  ret i8* %10, !dbg !1395
}

; Function Attrs: nounwind
define i8* @resp_code_msg(i32) #0 section ".CODE_REGION_2_" !dbg !1396 {
  %2 = alloca i32, align 4
  %3 = alloca i8*, align 4
  store i32 %0, i32* %2, align 4
  call void @llvm.dbg.declare(metadata i32* %2, metadata !1400, metadata !336), !dbg !1401
  call void @llvm.dbg.declare(metadata i8** %3, metadata !1402, metadata !336), !dbg !1403
  %4 = load i32, i32* %2, align 4, !dbg !1404
  switch i32 %4, label %10 [
    i32 1, label %5
    i32 2, label %6
    i32 3, label %7
    i32 4, label %8
    i32 5, label %9
  ], !dbg !1405

; <label>:5:                                      ; preds = %1
  store i8* getelementptr inbounds ([17 x i8], [17 x i8]* @.str.4.72, i32 0, i32 0), i8** %3, align 4, !dbg !1406
  br label %11, !dbg !1408

; <label>:6:                                      ; preds = %1
  store i8* getelementptr inbounds ([18 x i8], [18 x i8]* @.str.5.73, i32 0, i32 0), i8** %3, align 4, !dbg !1409
  br label %11, !dbg !1410

; <label>:7:                                      ; preds = %1
  store i8* getelementptr inbounds ([18 x i8], [18 x i8]* @.str.6.74, i32 0, i32 0), i8** %3, align 4, !dbg !1411
  br label %11, !dbg !1412

; <label>:8:                                      ; preds = %1
  store i8* getelementptr inbounds ([16 x i8], [16 x i8]* @.str.7.75, i32 0, i32 0), i8** %3, align 4, !dbg !1413
  br label %11, !dbg !1414

; <label>:9:                                      ; preds = %1
  store i8* getelementptr inbounds ([17 x i8], [17 x i8]* @.str.8.76, i32 0, i32 0), i8** %3, align 4, !dbg !1415
  br label %11, !dbg !1416

; <label>:10:                                     ; preds = %1
  store i8* getelementptr inbounds ([23 x i8], [23 x i8]* @.str.9.77, i32 0, i32 0), i8** %3, align 4, !dbg !1417
  br label %11, !dbg !1418

; <label>:11:                                     ; preds = %10, %9, %8, %7, %6, %5
  %12 = load i8*, i8** %3, align 4, !dbg !1419
  ret i8* %12, !dbg !1420
}

; Function Attrs: nounwind
define i32 @hostname_to_ip(i8*, %struct.in_addr*) #0 section ".CODE_REGION_2_" !dbg !1421 {
  %3 = alloca i8*, align 4
  %4 = alloca %struct.in_addr*, align 4
  %5 = alloca i32, align 4
  %6 = alloca %struct.addrinfo, align 4
  %7 = alloca %struct.addrinfo*, align 4
  %8 = alloca i32, align 4
  %9 = alloca %struct.addrinfo*, align 4
  %10 = alloca %struct.sockaddr_in*, align 4
  store i8* %0, i8** %3, align 4
  call void @llvm.dbg.declare(metadata i8** %3, metadata !1424, metadata !336), !dbg !1425
  store %struct.in_addr* %1, %struct.in_addr** %4, align 4
  call void @llvm.dbg.declare(metadata %struct.in_addr** %4, metadata !1426, metadata !336), !dbg !1427
  call void @llvm.dbg.declare(metadata i32* %5, metadata !1428, metadata !336), !dbg !1429
  call void @llvm.dbg.declare(metadata %struct.addrinfo* %6, metadata !1430, metadata !336), !dbg !1450
  call void @llvm.dbg.declare(metadata %struct.addrinfo** %7, metadata !1451, metadata !336), !dbg !1452
  call void @llvm.dbg.declare(metadata i32* %8, metadata !1453, metadata !336), !dbg !1454
  %11 = bitcast %struct.addrinfo* %6 to i8*, !dbg !1455
  call void @llvm.memset.p0i8.i32(i8* %11, i8 0, i32 32, i32 4, i1 false), !dbg !1455
  %12 = getelementptr inbounds %struct.addrinfo, %struct.addrinfo* %6, i32 0, i32 1, !dbg !1456
  store i32 2, i32* %12, align 4, !dbg !1457
  %13 = getelementptr inbounds %struct.addrinfo, %struct.addrinfo* %6, i32 0, i32 2, !dbg !1458
  store i32 0, i32* %13, align 4, !dbg !1459
  %14 = load i8*, i8** %3, align 4, !dbg !1460
  %15 = call i32 @getaddrinfo(i8* %14, i8* null, %struct.addrinfo* %6, %struct.addrinfo** %7), !dbg !1461
  store i32 %15, i32* %8, align 4, !dbg !1462
  %16 = load i32, i32* %8, align 4, !dbg !1463
  %17 = icmp eq i32 %16, 0, !dbg !1465
  br i1 %17, label %18, label %45, !dbg !1466

; <label>:18:                                     ; preds = %2
  call void @llvm.dbg.declare(metadata %struct.addrinfo** %9, metadata !1467, metadata !336), !dbg !1469
  store i32 -1, i32* %5, align 4, !dbg !1470
  %19 = load %struct.addrinfo*, %struct.addrinfo** %7, align 4, !dbg !1471
  store %struct.addrinfo* %19, %struct.addrinfo** %9, align 4, !dbg !1473
  br label %20, !dbg !1474

; <label>:20:                                     ; preds = %39, %18
  %21 = load %struct.addrinfo*, %struct.addrinfo** %9, align 4, !dbg !1475
  %22 = icmp ne %struct.addrinfo* %21, null, !dbg !1478
  br i1 %22, label %23, label %43, !dbg !1479

; <label>:23:                                     ; preds = %20
  call void @llvm.dbg.declare(metadata %struct.sockaddr_in** %10, metadata !1480, metadata !336), !dbg !1482
  %24 = load %struct.addrinfo*, %struct.addrinfo** %9, align 4, !dbg !1483
  %25 = getelementptr inbounds %struct.addrinfo, %struct.addrinfo* %24, i32 0, i32 5, !dbg !1484
  %26 = load %struct.sockaddr*, %struct.sockaddr** %25, align 4, !dbg !1484
  %27 = bitcast %struct.sockaddr* %26 to %struct.sockaddr_in*, !dbg !1485
  store %struct.sockaddr_in* %27, %struct.sockaddr_in** %10, align 4, !dbg !1486
  %28 = load %struct.in_addr*, %struct.in_addr** %4, align 4, !dbg !1487
  %29 = load %struct.sockaddr_in*, %struct.sockaddr_in** %10, align 4, !dbg !1488
  %30 = getelementptr inbounds %struct.sockaddr_in, %struct.sockaddr_in* %29, i32 0, i32 2, !dbg !1489
  %31 = bitcast %struct.in_addr* %28 to i8*, !dbg !1489
  %32 = bitcast %struct.in_addr* %30 to i8*, !dbg !1489
  call void @llvm.memcpy.p0i8.p0i8.i32(i8* %31, i8* %32, i32 4, i32 4, i1 false), !dbg !1489
  %33 = load %struct.in_addr*, %struct.in_addr** %4, align 4, !dbg !1490
  %34 = getelementptr inbounds %struct.in_addr, %struct.in_addr* %33, i32 0, i32 0, !dbg !1492
  %35 = load i32, i32* %34, align 4, !dbg !1492
  %36 = icmp ne i32 %35, 0, !dbg !1493
  br i1 %36, label %37, label %38, !dbg !1494

; <label>:37:                                     ; preds = %23
  store i32 0, i32* %5, align 4, !dbg !1495
  br label %43, !dbg !1497

; <label>:38:                                     ; preds = %23
  br label %39, !dbg !1498

; <label>:39:                                     ; preds = %38
  %40 = load %struct.addrinfo*, %struct.addrinfo** %9, align 4, !dbg !1499
  %41 = getelementptr inbounds %struct.addrinfo, %struct.addrinfo* %40, i32 0, i32 7, !dbg !1501
  %42 = load %struct.addrinfo*, %struct.addrinfo** %41, align 4, !dbg !1501
  store %struct.addrinfo* %42, %struct.addrinfo** %9, align 4, !dbg !1502
  br label %20, !dbg !1503, !llvm.loop !1504

; <label>:43:                                     ; preds = %37, %20
  %44 = load %struct.addrinfo*, %struct.addrinfo** %7, align 4, !dbg !1506
  call void @freeaddrinfo(%struct.addrinfo* %44) #7, !dbg !1507
  br label %52, !dbg !1508

; <label>:45:                                     ; preds = %2
  %46 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1509
  %47 = load i8*, i8** %3, align 4, !dbg !1509
  %48 = load i32, i32* %8, align 4, !dbg !1509
  %49 = call i8* @gai_strerror(i32 %48) #7, !dbg !1509
  call void @__AMI_fake_direct_transfer(), !dbg !1511
  %50 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %46, i8* getelementptr inbounds ([46 x i8], [46 x i8]* @.str.10.80, i32 0, i32 0), i8* %47, i8* %49), !dbg !1511
  %51 = load i32, i32* %8, align 4, !dbg !1513
  store i32 %51, i32* %5, align 4, !dbg !1514
  br label %52

; <label>:52:                                     ; preds = %45, %43
  %53 = load i32, i32* %5, align 4, !dbg !1515
  ret i32 %53, !dbg !1516
}

declare i32 @getaddrinfo(i8*, i8*, %struct.addrinfo*, %struct.addrinfo**) #5 section ".CODE_REGION_2_"

; Function Attrs: nounwind
declare void @freeaddrinfo(%struct.addrinfo*) #2 section ".CODE_REGION_2_"

; Function Attrs: nounwind
declare i8* @gai_strerror(i32) #2 section ".CODE_REGION_2_"

; Function Attrs: nounwind
define i32 @hostname_to_ip_at_dns(i8*, i8*, %struct.in_addr*) #0 section ".CODE_REGION_2_" !dbg !1517 {
  %4 = alloca i8*, align 4
  %5 = alloca i8*, align 4
  %6 = alloca %struct.in_addr*, align 4
  %7 = alloca i32, align 4
  %8 = alloca %struct.__res_state, align 4
  %9 = alloca %struct.in_addr, align 4
  %10 = alloca %union.anon.2, align 4
  %11 = alloca i32, align 4
  %12 = alloca [3 x %struct.in_addr], align 4
  %13 = alloca i32, align 4
  %14 = alloca i32, align 4
  %15 = alloca i32, align 4
  %16 = alloca %struct.__ns_msg, align 4
  %17 = alloca i32, align 4
  %18 = alloca i16, align 2
  %19 = alloca %struct.__ns_rr, align 4
  %20 = alloca i16, align 2
  %21 = alloca i8*, align 4
  %22 = alloca [256 x i8], align 1
  store i8* %0, i8** %4, align 4
  call void @llvm.dbg.declare(metadata i8** %4, metadata !1520, metadata !336), !dbg !1521
  store i8* %1, i8** %5, align 4
  call void @llvm.dbg.declare(metadata i8** %5, metadata !1522, metadata !336), !dbg !1523
  store %struct.in_addr* %2, %struct.in_addr** %6, align 4
  call void @llvm.dbg.declare(metadata %struct.in_addr** %6, metadata !1524, metadata !336), !dbg !1525
  call void @llvm.dbg.declare(metadata i32* %7, metadata !1526, metadata !336), !dbg !1527
  call void @llvm.dbg.declare(metadata %struct.__res_state* %8, metadata !1528, metadata !336), !dbg !1634
  %23 = bitcast %struct.__res_state* %8 to i8*, !dbg !1635
  call void @llvm.memset.p0i8.i32(i8* %23, i8 0, i32 512, i32 4, i1 false), !dbg !1635
  %24 = call i32 @__res_ninit(%struct.__res_state* %8) #7, !dbg !1636
  store i32 %24, i32* %7, align 4, !dbg !1637
  %25 = load i32, i32* %7, align 4, !dbg !1638
  %26 = icmp eq i32 %25, 0, !dbg !1640
  br i1 %26, label %27, label %209, !dbg !1641

; <label>:27:                                     ; preds = %3
  call void @llvm.dbg.declare(metadata %struct.in_addr* %9, metadata !1642, metadata !336), !dbg !1644
  %28 = load i8*, i8** %4, align 4, !dbg !1645
  %29 = call i32 @hostname_to_ip(i8* %28, %struct.in_addr* %9), !dbg !1646
  store i32 %29, i32* %7, align 4, !dbg !1647
  %30 = load i32, i32* %7, align 4, !dbg !1648
  %31 = icmp eq i32 %30, 0, !dbg !1650
  br i1 %31, label %32, label %208, !dbg !1651

; <label>:32:                                     ; preds = %27
  call void @llvm.dbg.declare(metadata %union.anon.2* %10, metadata !1652, metadata !336), !dbg !1680
  call void @llvm.dbg.declare(metadata i32* %11, metadata !1681, metadata !336), !dbg !1682
  call void @llvm.dbg.declare(metadata [3 x %struct.in_addr]* %12, metadata !1683, metadata !336), !dbg !1685
  call void @llvm.dbg.declare(metadata i32* %13, metadata !1686, metadata !336), !dbg !1687
  call void @llvm.dbg.declare(metadata i32* %14, metadata !1688, metadata !336), !dbg !1689
  call void @llvm.dbg.declare(metadata i32* %15, metadata !1690, metadata !336), !dbg !1691
  %33 = getelementptr inbounds %struct.__res_state, %struct.__res_state* %8, i32 0, i32 3, !dbg !1692
  %34 = load i32, i32* %33, align 4, !dbg !1692
  store i32 %34, i32* %13, align 4, !dbg !1693
  store i32 0, i32* %15, align 4, !dbg !1694
  br label %35, !dbg !1696

; <label>:35:                                     ; preds = %48, %32
  %36 = load i32, i32* %15, align 4, !dbg !1697
  %37 = load i32, i32* %13, align 4, !dbg !1700
  %38 = icmp slt i32 %36, %37, !dbg !1701
  br i1 %38, label %39, label %51, !dbg !1702

; <label>:39:                                     ; preds = %35
  %40 = load i32, i32* %15, align 4, !dbg !1703
  %41 = getelementptr inbounds [3 x %struct.in_addr], [3 x %struct.in_addr]* %12, i32 0, i32 %40, !dbg !1704
  %42 = load i32, i32* %15, align 4, !dbg !1705
  %43 = getelementptr inbounds %struct.__res_state, %struct.__res_state* %8, i32 0, i32 4, !dbg !1706
  %44 = getelementptr inbounds [3 x %struct.sockaddr_in], [3 x %struct.sockaddr_in]* %43, i32 0, i32 %42, !dbg !1707
  %45 = getelementptr inbounds %struct.sockaddr_in, %struct.sockaddr_in* %44, i32 0, i32 2, !dbg !1708
  %46 = bitcast %struct.in_addr* %41 to i8*, !dbg !1708
  %47 = bitcast %struct.in_addr* %45 to i8*, !dbg !1708
  call void @llvm.memcpy.p0i8.p0i8.i32(i8* %46, i8* %47, i32 4, i32 4, i1 false), !dbg !1708
  br label %48, !dbg !1704

; <label>:48:                                     ; preds = %39
  %49 = load i32, i32* %15, align 4, !dbg !1709
  %50 = add nsw i32 %49, 1, !dbg !1709
  store i32 %50, i32* %15, align 4, !dbg !1709
  br label %35, !dbg !1711, !llvm.loop !1712

; <label>:51:                                     ; preds = %35
  %52 = getelementptr inbounds %struct.__res_state, %struct.__res_state* %8, i32 0, i32 2, !dbg !1714
  %53 = load i32, i32* %52, align 4, !dbg !1714
  store i32 %53, i32* %14, align 4, !dbg !1715
  %54 = getelementptr inbounds %struct.__res_state, %struct.__res_state* %8, i32 0, i32 2, !dbg !1716
  %55 = load i32, i32* %54, align 4, !dbg !1717
  %56 = and i32 %55, -129, !dbg !1717
  store i32 %56, i32* %54, align 4, !dbg !1717
  %57 = getelementptr inbounds %struct.__res_state, %struct.__res_state* %8, i32 0, i32 4, !dbg !1718
  %58 = getelementptr inbounds [3 x %struct.sockaddr_in], [3 x %struct.sockaddr_in]* %57, i32 0, i32 0, !dbg !1719
  %59 = getelementptr inbounds %struct.sockaddr_in, %struct.sockaddr_in* %58, i32 0, i32 2, !dbg !1720
  %60 = bitcast %struct.in_addr* %59 to i8*, !dbg !1721
  %61 = bitcast %struct.in_addr* %9 to i8*, !dbg !1721
  call void @llvm.memcpy.p0i8.p0i8.i32(i8* %60, i8* %61, i32 4, i32 4, i1 false), !dbg !1721
  %62 = getelementptr inbounds %struct.__res_state, %struct.__res_state* %8, i32 0, i32 3, !dbg !1722
  store i32 1, i32* %62, align 4, !dbg !1723
  %63 = load i8*, i8** %5, align 4, !dbg !1724
  %64 = bitcast %union.anon.2* %10 to i8*, !dbg !1725
  %65 = call i32 @__res_nquery(%struct.__res_state* %8, i8* %63, i32 1, i32 1, i8* %64, i32 512) #7, !dbg !1726
  store i32 %65, i32* %11, align 4, !dbg !1727
  %66 = load i32, i32* %11, align 4, !dbg !1728
  %67 = icmp ne i32 %66, -1, !dbg !1730
  br i1 %67, label %68, label %162, !dbg !1731

; <label>:68:                                     ; preds = %51
  call void @llvm.dbg.declare(metadata %struct.__ns_msg* %16, metadata !1732, metadata !336), !dbg !1749
  %69 = bitcast %union.anon.2* %10 to [512 x i8]*, !dbg !1750
  %70 = getelementptr inbounds [512 x i8], [512 x i8]* %69, i32 0, i32 0, !dbg !1751
  %71 = load i32, i32* %11, align 4, !dbg !1752
  %72 = call i32 @ns_initparse(i8* %70, i32 %71, %struct.__ns_msg* %16) #7, !dbg !1753
  store i32 %72, i32* %7, align 4, !dbg !1754
  %73 = load i32, i32* %7, align 4, !dbg !1755
  %74 = icmp sge i32 %73, 0, !dbg !1757
  br i1 %74, label %75, label %155, !dbg !1758

; <label>:75:                                     ; preds = %68
  call void @llvm.dbg.declare(metadata i32* %17, metadata !1759, metadata !336), !dbg !1761
  %76 = bitcast %struct.__ns_msg* %16 to [12 x i32]*, !dbg !1762
  %77 = load [12 x i32], [12 x i32]* %76, align 4, !dbg !1762
  %78 = call i32 @ns_msg_getflag([12 x i32] %77, i32 9) #7, !dbg !1762
  store i32 %78, i32* %17, align 4, !dbg !1763
  %79 = load i32, i32* %17, align 4, !dbg !1764
  %80 = icmp eq i32 %79, 0, !dbg !1766
  br i1 %80, label %81, label %145, !dbg !1767

; <label>:81:                                     ; preds = %75
  call void @llvm.dbg.declare(metadata i16* %18, metadata !1768, metadata !336), !dbg !1770
  %82 = getelementptr inbounds %struct.__ns_msg, %struct.__ns_msg* %16, i32 0, i32 4, !dbg !1771
  %83 = getelementptr inbounds [4 x i16], [4 x i16]* %82, i32 0, i32 1, !dbg !1771
  %84 = load i16, i16* %83, align 2, !dbg !1771
  %85 = zext i16 %84 to i32, !dbg !1771
  %86 = add nsw i32 %85, 0, !dbg !1771
  %87 = trunc i32 %86 to i16, !dbg !1771
  store i16 %87, i16* %18, align 2, !dbg !1772
  %88 = load i16, i16* %18, align 2, !dbg !1773
  %89 = zext i16 %88 to i32, !dbg !1773
  %90 = icmp eq i32 %89, 1, !dbg !1775
  br i1 %90, label %91, label %135, !dbg !1776

; <label>:91:                                     ; preds = %81
  call void @llvm.dbg.declare(metadata %struct.__ns_rr* %19, metadata !1777, metadata !336), !dbg !1791
  %92 = call i32 @ns_parserr(%struct.__ns_msg* %16, i32 1, i32 0, %struct.__ns_rr* %19) #7, !dbg !1792
  store i32 %92, i32* %7, align 4, !dbg !1793
  %93 = load i32, i32* %7, align 4, !dbg !1794
  %94 = icmp eq i32 %93, 0, !dbg !1796
  br i1 %94, label %95, label %128, !dbg !1797

; <label>:95:                                     ; preds = %91
  call void @llvm.dbg.declare(metadata i16* %20, metadata !1798, metadata !336), !dbg !1800
  %96 = getelementptr inbounds %struct.__ns_rr, %struct.__ns_rr* %19, i32 0, i32 1, !dbg !1801
  %97 = load i16, i16* %96, align 2, !dbg !1801
  %98 = zext i16 %97 to i32, !dbg !1801
  %99 = add nsw i32 %98, 0, !dbg !1801
  %100 = trunc i32 %99 to i16, !dbg !1801
  store i16 %100, i16* %20, align 2, !dbg !1802
  %101 = load i16, i16* %20, align 2, !dbg !1803
  %102 = zext i16 %101 to i32, !dbg !1803
  %103 = icmp eq i32 %102, 1, !dbg !1805
  br i1 %103, label %104, label %118, !dbg !1806

; <label>:104:                                    ; preds = %95
  call void @llvm.dbg.declare(metadata i8** %21, metadata !1807, metadata !336), !dbg !1809
  call void @llvm.dbg.declare(metadata [256 x i8]* %22, metadata !1810, metadata !336), !dbg !1811
  %105 = getelementptr inbounds [256 x i8], [256 x i8]* %22, i32 0, i32 0, !dbg !1812
  %106 = call i32 @ns_sprintrr(%struct.__ns_msg* %16, %struct.__ns_rr* %19, i8* null, i8* null, i8* %105, i32 256) #7, !dbg !1813
  %107 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1814
  %108 = getelementptr inbounds [256 x i8], [256 x i8]* %22, i32 0, i32 0, !dbg !1814
  call void @__AMI_fake_direct_transfer(), !dbg !1814
  %109 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %107, i8* getelementptr inbounds ([6 x i8], [6 x i8]* @.str.11.81, i32 0, i32 0), i8* %108), !dbg !1814
  %110 = getelementptr inbounds %struct.__ns_rr, %struct.__ns_rr* %19, i32 0, i32 5, !dbg !1815
  %111 = load i8*, i8** %110, align 4, !dbg !1815
  %112 = getelementptr inbounds i8, i8* %111, i32 0, !dbg !1815
  store i8* %112, i8** %21, align 4, !dbg !1816
  %113 = load %struct.in_addr*, %struct.in_addr** %6, align 4, !dbg !1817
  %114 = load i8*, i8** %21, align 4, !dbg !1818
  %115 = bitcast i8* %114 to %struct.in_addr*, !dbg !1819
  %116 = bitcast %struct.in_addr* %113 to i8*, !dbg !1819
  %117 = bitcast %struct.in_addr* %115 to i8*, !dbg !1819
  call void @llvm.memcpy.p0i8.p0i8.i32(i8* %116, i8* %117, i32 4, i32 4, i1 false), !dbg !1819
  store i32 0, i32* %7, align 4, !dbg !1820
  br label %127, !dbg !1821

; <label>:118:                                    ; preds = %95
  %119 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1822
  %120 = getelementptr inbounds %struct.in_addr, %struct.in_addr* %9, i32 0, i32 0, !dbg !1822
  %121 = bitcast i32* %120 to [1 x i32]*, !dbg !1822
  %122 = load [1 x i32], [1 x i32]* %121, align 4, !dbg !1822
  %123 = call i8* @inet_ntoa([1 x i32] %122) #7, !dbg !1822
  %124 = load i16, i16* %20, align 2, !dbg !1822
  %125 = zext i16 %124 to i32, !dbg !1822
  call void @__AMI_fake_direct_transfer(), !dbg !1824
  %126 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %119, i8* getelementptr inbounds ([37 x i8], [37 x i8]* @.str.12.82, i32 0, i32 0), i8* %123, i32 1, i32 %125), !dbg !1824
  store i32 -2, i32* %7, align 4, !dbg !1826
  br label %127

; <label>:127:                                    ; preds = %118, %104
  br label %134, !dbg !1827

; <label>:128:                                    ; preds = %91
  %129 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1828
  %130 = call i32* @__errno_location() #1, !dbg !1828
  %131 = load i32, i32* %130, align 4, !dbg !1828
  %132 = call i8* @strerror(i32 %131) #7, !dbg !1830
  call void @__AMI_fake_direct_transfer(), !dbg !1832
  %133 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %129, i8* getelementptr inbounds ([16 x i8], [16 x i8]* @.str.13.83, i32 0, i32 0), i8* %132), !dbg !1832
  br label %134

; <label>:134:                                    ; preds = %128, %127
  br label %144, !dbg !1834

; <label>:135:                                    ; preds = %81
  %136 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1835
  %137 = getelementptr inbounds %struct.in_addr, %struct.in_addr* %9, i32 0, i32 0, !dbg !1835
  %138 = bitcast i32* %137 to [1 x i32]*, !dbg !1835
  %139 = load [1 x i32], [1 x i32]* %138, align 4, !dbg !1835
  %140 = call i8* @inet_ntoa([1 x i32] %139) #7, !dbg !1835
  %141 = load i16, i16* %18, align 2, !dbg !1835
  %142 = zext i16 %141 to i32, !dbg !1835
  call void @__AMI_fake_direct_transfer(), !dbg !1837
  %143 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %136, i8* getelementptr inbounds ([31 x i8], [31 x i8]* @.str.14.84, i32 0, i32 0), i8* %140, i32 %142), !dbg !1837
  store i32 -1, i32* %7, align 4, !dbg !1839
  br label %144

; <label>:144:                                    ; preds = %135, %134
  br label %154, !dbg !1840

; <label>:145:                                    ; preds = %75
  %146 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1841
  %147 = getelementptr inbounds %struct.in_addr, %struct.in_addr* %9, i32 0, i32 0, !dbg !1841
  %148 = bitcast i32* %147 to [1 x i32]*, !dbg !1841
  %149 = load [1 x i32], [1 x i32]* %148, align 4, !dbg !1841
  %150 = call i8* @inet_ntoa([1 x i32] %149) #7, !dbg !1841
  %151 = load i32, i32* %17, align 4, !dbg !1841
  %152 = call i8* @resp_code_msg(i32 %151), !dbg !1843
  call void @__AMI_fake_direct_transfer(), !dbg !1845
  %153 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %146, i8* getelementptr inbounds ([49 x i8], [49 x i8]* @.str.15.85, i32 0, i32 0), i8* %150, i8* %152), !dbg !1845
  store i32 -4, i32* %7, align 4, !dbg !1847
  br label %154

; <label>:154:                                    ; preds = %145, %144
  br label %161, !dbg !1848

; <label>:155:                                    ; preds = %68
  %156 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1849
  %157 = call i32* @__errno_location() #1, !dbg !1849
  %158 = load i32, i32* %157, align 4, !dbg !1849
  %159 = call i8* @strerror(i32 %158) #7, !dbg !1851
  call void @__AMI_fake_direct_transfer(), !dbg !1853
  %160 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %156, i8* getelementptr inbounds ([18 x i8], [18 x i8]* @.str.16.86, i32 0, i32 0), i8* %159), !dbg !1853
  br label %161

; <label>:161:                                    ; preds = %155, %154
  br label %186, !dbg !1855

; <label>:162:                                    ; preds = %51
  %163 = call i32* @__errno_location() #1, !dbg !1856
  %164 = load i32, i32* %163, align 4, !dbg !1856
  %165 = icmp eq i32 %164, 111, !dbg !1859
  br i1 %165, label %166, label %173, !dbg !1860

; <label>:166:                                    ; preds = %162
  %167 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1861
  %168 = getelementptr inbounds %struct.in_addr, %struct.in_addr* %9, i32 0, i32 0, !dbg !1861
  %169 = bitcast i32* %168 to [1 x i32]*, !dbg !1861
  %170 = load [1 x i32], [1 x i32]* %169, align 4, !dbg !1861
  %171 = call i8* @inet_ntoa([1 x i32] %170) #7, !dbg !1861
  call void @__AMI_fake_direct_transfer(), !dbg !1862
  %172 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %167, i8* getelementptr inbounds ([59 x i8], [59 x i8]* @.str.17.87, i32 0, i32 0), i8* %171), !dbg !1862
  br label %185, !dbg !1861

; <label>:173:                                    ; preds = %162
  %174 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1864
  %175 = getelementptr inbounds %struct.in_addr, %struct.in_addr* %9, i32 0, i32 0, !dbg !1864
  %176 = bitcast i32* %175 to [1 x i32]*, !dbg !1864
  %177 = load [1 x i32], [1 x i32]* %176, align 4, !dbg !1864
  %178 = call i8* @inet_ntoa([1 x i32] %177) #7, !dbg !1864
  %179 = call i32* @__h_errno_location() #1, !dbg !1865
  %180 = load i32, i32* %179, align 4, !dbg !1864
  %181 = call i32* @__h_errno_location() #1, !dbg !1866
  %182 = load i32, i32* %181, align 4, !dbg !1864
  %183 = call i8* @herror_msg(i32 %182), !dbg !1868
  call void @__AMI_fake_direct_transfer(), !dbg !1870
  %184 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %174, i8* getelementptr inbounds ([49 x i8], [49 x i8]* @.str.18.88, i32 0, i32 0), i8* %178, i32 %180, i8* %183), !dbg !1870
  br label %185

; <label>:185:                                    ; preds = %173, %166
  store i32 -3, i32* %7, align 4, !dbg !1872
  br label %186

; <label>:186:                                    ; preds = %185, %161
  %187 = load i32, i32* %14, align 4, !dbg !1873
  %188 = getelementptr inbounds %struct.__res_state, %struct.__res_state* %8, i32 0, i32 2, !dbg !1874
  store i32 %187, i32* %188, align 4, !dbg !1875
  %189 = load i32, i32* %13, align 4, !dbg !1876
  %190 = getelementptr inbounds %struct.__res_state, %struct.__res_state* %8, i32 0, i32 3, !dbg !1877
  store i32 %189, i32* %190, align 4, !dbg !1878
  store i32 0, i32* %15, align 4, !dbg !1879
  br label %191, !dbg !1881

; <label>:191:                                    ; preds = %204, %186
  %192 = load i32, i32* %15, align 4, !dbg !1882
  %193 = load i32, i32* %13, align 4, !dbg !1885
  %194 = icmp slt i32 %192, %193, !dbg !1886
  br i1 %194, label %195, label %207, !dbg !1887

; <label>:195:                                    ; preds = %191
  %196 = load i32, i32* %15, align 4, !dbg !1888
  %197 = getelementptr inbounds %struct.__res_state, %struct.__res_state* %8, i32 0, i32 4, !dbg !1889
  %198 = getelementptr inbounds [3 x %struct.sockaddr_in], [3 x %struct.sockaddr_in]* %197, i32 0, i32 %196, !dbg !1890
  %199 = getelementptr inbounds %struct.sockaddr_in, %struct.sockaddr_in* %198, i32 0, i32 2, !dbg !1891
  %200 = load i32, i32* %15, align 4, !dbg !1892
  %201 = getelementptr inbounds [3 x %struct.in_addr], [3 x %struct.in_addr]* %12, i32 0, i32 %200, !dbg !1893
  %202 = bitcast %struct.in_addr* %199 to i8*, !dbg !1893
  %203 = bitcast %struct.in_addr* %201 to i8*, !dbg !1893
  call void @llvm.memcpy.p0i8.p0i8.i32(i8* %202, i8* %203, i32 4, i32 4, i1 false), !dbg !1893
  br label %204, !dbg !1890

; <label>:204:                                    ; preds = %195
  %205 = load i32, i32* %15, align 4, !dbg !1894
  %206 = add nsw i32 %205, 1, !dbg !1894
  store i32 %206, i32* %15, align 4, !dbg !1894
  br label %191, !dbg !1896, !llvm.loop !1897

; <label>:207:                                    ; preds = %191
  br label %208, !dbg !1899

; <label>:208:                                    ; preds = %207, %27
  br label %214, !dbg !1900

; <label>:209:                                    ; preds = %3
  %210 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1901
  %211 = call i32* @__errno_location() #1, !dbg !1901
  %212 = load i32, i32* %211, align 4, !dbg !1901
  call void @__AMI_fake_direct_transfer(), !dbg !1903
  %213 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %210, i8* getelementptr inbounds ([26 x i8], [26 x i8]* @.str.19.89, i32 0, i32 0), i32 %212), !dbg !1903
  br label %214

; <label>:214:                                    ; preds = %209, %208
  %215 = load i32, i32* %7, align 4, !dbg !1905
  ret i32 %215, !dbg !1906
}

; Function Attrs: nounwind
declare i32 @__res_ninit(%struct.__res_state*) #2 section ".CODE_REGION_2_"

; Function Attrs: nounwind
declare i32 @__res_nquery(%struct.__res_state*, i8*, i32, i32, i8*, i32) #2 section ".CODE_REGION_2_"

; Function Attrs: nounwind
declare i32 @ns_initparse(i8*, i32, %struct.__ns_msg*) #2 section ".CODE_REGION_2_"

; Function Attrs: nounwind
declare i32 @ns_msg_getflag([12 x i32], i32) #2 section ".CODE_REGION_2_"

; Function Attrs: nounwind
declare i32 @ns_parserr(%struct.__ns_msg*, i32, i32, %struct.__ns_rr*) #2 section ".CODE_REGION_2_"

; Function Attrs: nounwind
declare i32 @ns_sprintrr(%struct.__ns_msg*, %struct.__ns_rr*, i8*, i8*, i8*, i32) #2 section ".CODE_REGION_2_"

; Function Attrs: nounwind readnone
declare i32* @__h_errno_location() #4 section ".CODE_REGION_2_"

; Function Attrs: nounwind
define i32 @get_public_ip(i8*) #0 section ".CODE_REGION_2_" !dbg !1907 {
  %2 = alloca i8*, align 4
  %3 = alloca i32, align 4
  %4 = alloca %struct.in_addr, align 4
  store i8* %0, i8** %2, align 4
  call void @llvm.dbg.declare(metadata i8** %2, metadata !1908, metadata !336), !dbg !1909
  call void @llvm.dbg.declare(metadata i32* %3, metadata !1910, metadata !336), !dbg !1911
  call void @llvm.dbg.declare(metadata %struct.in_addr* %4, metadata !1912, metadata !336), !dbg !1913
  %5 = call i32 @hostname_to_ip_at_dns(i8* getelementptr inbounds ([22 x i8], [22 x i8]* @.str.20.92, i32 0, i32 0), i8* getelementptr inbounds ([17 x i8], [17 x i8]* @.str.21.93, i32 0, i32 0), %struct.in_addr* %4), !dbg !1914
  store i32 %5, i32* %3, align 4, !dbg !1915
  %6 = load i32, i32* %3, align 4, !dbg !1916
  %7 = icmp eq i32 %6, 0, !dbg !1918
  br i1 %7, label %8, label %15, !dbg !1919

; <label>:8:                                      ; preds = %1
  %9 = load i8*, i8** %2, align 4, !dbg !1920
  %10 = getelementptr inbounds %struct.in_addr, %struct.in_addr* %4, i32 0, i32 0, !dbg !1921
  %11 = bitcast i32* %10 to [1 x i32]*, !dbg !1921
  %12 = load [1 x i32], [1 x i32]* %11, align 4, !dbg !1921
  %13 = call i8* @inet_ntoa([1 x i32] %12) #7, !dbg !1921
  %14 = call i8* @strcpy(i8* %9, i8* %13) #7, !dbg !1922
  br label %15, !dbg !1924

; <label>:15:                                     ; preds = %8, %1
  %16 = load i32, i32* %3, align 4, !dbg !1925
  ret i32 %16, !dbg !1926
}

; Function Attrs: nounwind
define i32 @get_current_exec_path(i8*, i32) #0 section ".CODE_REGION_2_" !dbg !1927 {
  %3 = alloca i8*, align 4
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  %6 = alloca [4097 x i8], align 1
  %7 = alloca i32, align 4
  %8 = alloca i8*, align 4
  store i8* %0, i8** %3, align 4
  call void @llvm.dbg.declare(metadata i8** %3, metadata !1930, metadata !336), !dbg !1931
  store i32 %1, i32* %4, align 4
  call void @llvm.dbg.declare(metadata i32* %4, metadata !1932, metadata !336), !dbg !1933
  call void @llvm.dbg.declare(metadata i32* %5, metadata !1934, metadata !336), !dbg !1935
  %9 = load i32, i32* %4, align 4, !dbg !1936
  %10 = icmp ugt i32 %9, 0, !dbg !1938
  br i1 %10, label %11, label %42, !dbg !1939

; <label>:11:                                     ; preds = %2
  call void @llvm.dbg.declare(metadata [4097 x i8]* %6, metadata !1940, metadata !336), !dbg !1942
  call void @llvm.dbg.declare(metadata i32* %7, metadata !1943, metadata !336), !dbg !1944
  %12 = getelementptr inbounds [4097 x i8], [4097 x i8]* %6, i32 0, i32 0, !dbg !1945
  %13 = call i32 @readlink(i8* getelementptr inbounds ([15 x i8], [15 x i8]* @.str.96, i32 0, i32 0), i8* %12, i32 4096) #7, !dbg !1946
  store i32 %13, i32* %7, align 4, !dbg !1947
  %14 = load i32, i32* %7, align 4, !dbg !1948
  %15 = icmp ne i32 %14, -1, !dbg !1950
  br i1 %15, label %16, label %36, !dbg !1951

; <label>:16:                                     ; preds = %11
  call void @llvm.dbg.declare(metadata i8** %8, metadata !1952, metadata !336), !dbg !1954
  %17 = load i32, i32* %7, align 4, !dbg !1955
  %18 = getelementptr inbounds [4097 x i8], [4097 x i8]* %6, i32 0, i32 %17, !dbg !1956
  store i8 0, i8* %18, align 1, !dbg !1957
  %19 = getelementptr inbounds [4097 x i8], [4097 x i8]* %6, i32 0, i32 0, !dbg !1958
  %20 = call i8* @dirname(i8* %19) #7, !dbg !1959
  store i8* %20, i8** %8, align 4, !dbg !1960
  %21 = load i32, i32* %4, align 4, !dbg !1961
  %22 = load i8*, i8** %8, align 4, !dbg !1963
  %23 = call i32 @strlen(i8* %22) #9, !dbg !1964
  %24 = add i32 %23, 1, !dbg !1965
  %25 = icmp ugt i32 %21, %24, !dbg !1966
  br i1 %25, label %26, label %32, !dbg !1967

; <label>:26:                                     ; preds = %16
  %27 = load i8*, i8** %3, align 4, !dbg !1968
  %28 = load i8*, i8** %8, align 4, !dbg !1970
  %29 = call i8* @strcpy(i8* %27, i8* %28) #7, !dbg !1971
  %30 = load i8*, i8** %3, align 4, !dbg !1972
  %31 = call i8* @strcat(i8* %30, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.1.97, i32 0, i32 0)) #7, !dbg !1973
  store i32 0, i32* %5, align 4, !dbg !1974
  br label %35, !dbg !1975

; <label>:32:                                     ; preds = %16
  %33 = load i8*, i8** %3, align 4, !dbg !1976
  %34 = getelementptr inbounds i8, i8* %33, i32 0, !dbg !1976
  store i8 0, i8* %34, align 1, !dbg !1978
  store i32 22, i32* %5, align 4, !dbg !1979
  br label %35

; <label>:35:                                     ; preds = %32, %26
  br label %41, !dbg !1980

; <label>:36:                                     ; preds = %11
  %37 = load i8*, i8** %3, align 4, !dbg !1981
  %38 = getelementptr inbounds i8, i8* %37, i32 0, !dbg !1981
  store i8 0, i8* %38, align 1, !dbg !1983
  %39 = call i32* @__errno_location() #1, !dbg !1984
  %40 = load i32, i32* %39, align 4, !dbg !1984
  store i32 %40, i32* %5, align 4, !dbg !1985
  br label %41

; <label>:41:                                     ; preds = %36, %35
  br label %43, !dbg !1986

; <label>:42:                                     ; preds = %2
  store i32 22, i32* %5, align 4, !dbg !1987
  br label %43

; <label>:43:                                     ; preds = %42, %41
  %44 = load i32, i32* %5, align 4, !dbg !1988
  ret i32 %44, !dbg !1989
}

; Function Attrs: nounwind
declare i32 @readlink(i8*, i8*, i32) #2 section ".CODE_REGION_2_"

; Function Attrs: nounwind
declare i8* @dirname(i8*) #2 section ".CODE_REGION_2_"

; Function Attrs: nounwind
define void @kill_processes(i32*, i32) #0 section ".CODE_REGION_2_" !dbg !1990 {
  %3 = alloca i32*, align 4
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  store i32* %0, i32** %3, align 4
  call void @llvm.dbg.declare(metadata i32** %3, metadata !1994, metadata !336), !dbg !1995
  store i32 %1, i32* %4, align 4
  call void @llvm.dbg.declare(metadata i32* %4, metadata !1996, metadata !336), !dbg !1997
  call void @llvm.dbg.declare(metadata i32* %5, metadata !1998, metadata !336), !dbg !1999
  store i32 0, i32* %5, align 4, !dbg !2000
  br label %6, !dbg !2002

; <label>:6:                                      ; preds = %23, %2
  %7 = load i32, i32* %5, align 4, !dbg !2003
  %8 = load i32, i32* %4, align 4, !dbg !2006
  %9 = icmp ult i32 %7, %8, !dbg !2007
  br i1 %9, label %10, label %26, !dbg !2008

; <label>:10:                                     ; preds = %6
  %11 = load i32, i32* %5, align 4, !dbg !2009
  %12 = load i32*, i32** %3, align 4, !dbg !2011
  %13 = getelementptr inbounds i32, i32* %12, i32 %11, !dbg !2011
  %14 = load i32, i32* %13, align 4, !dbg !2011
  %15 = icmp ne i32 %14, -1, !dbg !2012
  br i1 %15, label %16, label %22, !dbg !2013

; <label>:16:                                     ; preds = %10
  %17 = load i32, i32* %5, align 4, !dbg !2014
  %18 = load i32*, i32** %3, align 4, !dbg !2015
  %19 = getelementptr inbounds i32, i32* %18, i32 %17, !dbg !2015
  %20 = load i32, i32* %19, align 4, !dbg !2015
  %21 = call i32 @kill(i32 %20, i32 15) #7, !dbg !2016
  br label %22, !dbg !2016

; <label>:22:                                     ; preds = %16, %10
  br label %23, !dbg !2017

; <label>:23:                                     ; preds = %22
  %24 = load i32, i32* %5, align 4, !dbg !2019
  %25 = add nsw i32 %24, 1, !dbg !2019
  store i32 %25, i32* %5, align 4, !dbg !2019
  br label %6, !dbg !2021, !llvm.loop !2022

; <label>:26:                                     ; preds = %6
  ret void, !dbg !2024
}

; Function Attrs: nounwind
declare i32 @kill(i32, i32) #2 section ".CODE_REGION_2_"

; Function Attrs: nounwind
define i32 @wait_processes(i32*, i32, i32) #0 section ".CODE_REGION_2_" !dbg !2025 {
  %4 = alloca i32*, align 4
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  %7 = alloca i32, align 4
  %8 = alloca i32, align 4
  %9 = alloca i32, align 4
  %10 = alloca i32, align 4
  store i32* %0, i32** %4, align 4
  call void @llvm.dbg.declare(metadata i32** %4, metadata !2028, metadata !336), !dbg !2029
  store i32 %1, i32* %5, align 4
  call void @llvm.dbg.declare(metadata i32* %5, metadata !2030, metadata !336), !dbg !2031
  store i32 %2, i32* %6, align 4
  call void @llvm.dbg.declare(metadata i32* %6, metadata !2032, metadata !336), !dbg !2033
  call void @llvm.dbg.declare(metadata i32* %7, metadata !2034, metadata !336), !dbg !2035
  call void @llvm.dbg.declare(metadata i32* %8, metadata !2036, metadata !336), !dbg !2037
  store i32 0, i32* %7, align 4, !dbg !2038
  br label %11, !dbg !2039, !llvm.loop !2040

; <label>:11:                                     ; preds = %62, %3
  call void @llvm.dbg.declare(metadata i32* %9, metadata !2041, metadata !336), !dbg !2043
  store i32 0, i32* %8, align 4, !dbg !2044
  %12 = load i32, i32* %6, align 4, !dbg !2045
  %13 = call i32 @alarm(i32 %12) #7, !dbg !2046
  %14 = call i32 @waitpid(i32 0, i32* null, i32 0), !dbg !2047
  store i32 %14, i32* %9, align 4, !dbg !2048
  %15 = load i32, i32* %9, align 4, !dbg !2049
  %16 = icmp ne i32 %15, -1, !dbg !2051
  br i1 %16, label %17, label %51, !dbg !2052

; <label>:17:                                     ; preds = %11
  call void @llvm.dbg.declare(metadata i32* %10, metadata !2053, metadata !336), !dbg !2055
  store i32 0, i32* %10, align 4, !dbg !2056
  br label %18, !dbg !2058

; <label>:18:                                     ; preds = %47, %17
  %19 = load i32, i32* %10, align 4, !dbg !2059
  %20 = load i32, i32* %5, align 4, !dbg !2062
  %21 = icmp ult i32 %19, %20, !dbg !2063
  br i1 %21, label %22, label %50, !dbg !2064

; <label>:22:                                     ; preds = %18
  %23 = load i32, i32* %10, align 4, !dbg !2065
  %24 = load i32*, i32** %4, align 4, !dbg !2067
  %25 = getelementptr inbounds i32, i32* %24, i32 %23, !dbg !2067
  %26 = load i32, i32* %25, align 4, !dbg !2067
  %27 = icmp ne i32 %26, -1, !dbg !2068
  br i1 %27, label %28, label %46, !dbg !2069

; <label>:28:                                     ; preds = %22
  %29 = load i32, i32* %10, align 4, !dbg !2070
  %30 = load i32*, i32** %4, align 4, !dbg !2073
  %31 = getelementptr inbounds i32, i32* %30, i32 %29, !dbg !2073
  %32 = load i32, i32* %31, align 4, !dbg !2073
  %33 = load i32, i32* %9, align 4, !dbg !2074
  %34 = icmp eq i32 %32, %33, !dbg !2075
  br i1 %34, label %35, label %42, !dbg !2076

; <label>:35:                                     ; preds = %28
  %36 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !2077
  %37 = load i32, i32* %9, align 4, !dbg !2077
  call void @__AMI_fake_direct_transfer(), !dbg !2077
  %38 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %36, i8* getelementptr inbounds ([40 x i8], [40 x i8]* @.str.2.102, i32 0, i32 0), i32 %37), !dbg !2077
  %39 = load i32, i32* %10, align 4, !dbg !2079
  %40 = load i32*, i32** %4, align 4, !dbg !2080
  %41 = getelementptr inbounds i32, i32* %40, i32 %39, !dbg !2080
  store i32 -1, i32* %41, align 4, !dbg !2081
  br label %45, !dbg !2082

; <label>:42:                                     ; preds = %28
  %43 = load i32, i32* %8, align 4, !dbg !2083
  %44 = add nsw i32 %43, 1, !dbg !2083
  store i32 %44, i32* %8, align 4, !dbg !2083
  br label %45

; <label>:45:                                     ; preds = %42, %35
  br label %46, !dbg !2084

; <label>:46:                                     ; preds = %45, %22
  br label %47, !dbg !2085

; <label>:47:                                     ; preds = %46
  %48 = load i32, i32* %10, align 4, !dbg !2087
  %49 = add nsw i32 %48, 1, !dbg !2087
  store i32 %49, i32* %10, align 4, !dbg !2087
  br label %18, !dbg !2089, !llvm.loop !2090

; <label>:50:                                     ; preds = %18
  br label %61, !dbg !2092

; <label>:51:                                     ; preds = %11
  %52 = call i32* @__errno_location() #1, !dbg !2093
  %53 = load i32, i32* %52, align 4, !dbg !2093
  store i32 %53, i32* %7, align 4, !dbg !2095
  %54 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !2096
  %55 = call i32* @__errno_location() #1, !dbg !2096
  %56 = load i32, i32* %55, align 4, !dbg !2096
  %57 = call i32* @__errno_location() #1, !dbg !2097
  %58 = load i32, i32* %57, align 4, !dbg !2096
  %59 = call i8* @strerror(i32 %58) #7, !dbg !2099
  call void @__AMI_fake_direct_transfer(), !dbg !2101
  %60 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %54, i8* getelementptr inbounds ([57 x i8], [57 x i8]* @.str.3.103, i32 0, i32 0), i32 %56, i8* %59), !dbg !2101
  br label %61

; <label>:61:                                     ; preds = %51, %50
  br label %62, !dbg !2103

; <label>:62:                                     ; preds = %61
  %63 = load i32, i32* %8, align 4, !dbg !2104
  %64 = icmp sgt i32 %63, 0, !dbg !2105
  br i1 %64, label %11, label %65, !dbg !2106, !llvm.loop !2040

; <label>:65:                                     ; preds = %62
  %66 = load i32, i32* %7, align 4, !dbg !2108
  ret i32 %66, !dbg !2109
}

; Function Attrs: nounwind
declare i32 @alarm(i32) #2 section ".CODE_REGION_2_"

declare i32 @waitpid(i32, i32*, i32) #5 section ".CODE_REGION_2_"

; Function Attrs: nounwind
define i32 @run_background_command(i32*, i8*, i8**) #0 section ".CODE_REGION_2_" !dbg !2110 {
  %4 = alloca i32*, align 4
  %5 = alloca i8*, align 4
  %6 = alloca i8**, align 4
  %7 = alloca i32, align 4
  %8 = alloca i32, align 4
  store i32* %0, i32** %4, align 4
  call void @llvm.dbg.declare(metadata i32** %4, metadata !2116, metadata !336), !dbg !2117
  store i8* %1, i8** %5, align 4
  call void @llvm.dbg.declare(metadata i8** %5, metadata !2118, metadata !336), !dbg !2119
  store i8** %2, i8*** %6, align 4
  call void @llvm.dbg.declare(metadata i8*** %6, metadata !2120, metadata !336), !dbg !2121
  call void @llvm.dbg.declare(metadata i32* %7, metadata !2122, metadata !336), !dbg !2123
  %9 = call i32 @fork() #7, !dbg !2124
  %10 = load i32*, i32** %4, align 4, !dbg !2125
  store i32 %9, i32* %10, align 4, !dbg !2126
  %11 = load i32*, i32** %4, align 4, !dbg !2127
  %12 = load i32, i32* %11, align 4, !dbg !2129
  %13 = icmp eq i32 %12, 0, !dbg !2130
  br i1 %13, label %14, label %83, !dbg !2131

; <label>:14:                                     ; preds = %3
  call void @llvm.dbg.declare(metadata i32* %8, metadata !2132, metadata !336), !dbg !2134
  %15 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !2135
  %16 = icmp ne %struct._IO_FILE* %15, null, !dbg !2137
  br i1 %16, label %17, label %42, !dbg !2138

; <label>:17:                                     ; preds = %14
  %18 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !2139
  %19 = call i32 @fileno(%struct._IO_FILE* %18) #7, !dbg !2142
  %20 = call i32 @dup2(i32 %19, i32 1) #7, !dbg !2143
  %21 = icmp eq i32 %20, -1, !dbg !2145
  br i1 %21, label %22, label %28, !dbg !2146

; <label>:22:                                     ; preds = %17
  %23 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !2147
  %24 = load i8*, i8** %5, align 4, !dbg !2147
  %25 = call i32* @__errno_location() #1, !dbg !2147
  %26 = load i32, i32* %25, align 4, !dbg !2147
  call void @__AMI_fake_direct_transfer(), !dbg !2148
  %27 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %23, i8* getelementptr inbounds ([64 x i8], [64 x i8]* @.str.4.106, i32 0, i32 0), i8* %24, i32 %26), !dbg !2148
  br label %28, !dbg !2147

; <label>:28:                                     ; preds = %22, %17
  %29 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !2149
  %30 = call i32 @fileno(%struct._IO_FILE* %29) #7, !dbg !2151
  %31 = call i32 @dup2(i32 %30, i32 2) #7, !dbg !2152
  %32 = icmp eq i32 %31, -1, !dbg !2154
  br i1 %32, label %33, label %39, !dbg !2155

; <label>:33:                                     ; preds = %28
  %34 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !2156
  %35 = load i8*, i8** %5, align 4, !dbg !2156
  %36 = call i32* @__errno_location() #1, !dbg !2156
  %37 = load i32, i32* %36, align 4, !dbg !2156
  call void @__AMI_fake_direct_transfer(), !dbg !2157
  %38 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %34, i8* getelementptr inbounds ([70 x i8], [70 x i8]* @.str.5.107, i32 0, i32 0), i8* %35, i32 %37), !dbg !2157
  br label %39, !dbg !2156

; <label>:39:                                     ; preds = %33, %28
  %40 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !2158
  %41 = call i32 @fclose(%struct._IO_FILE* %40), !dbg !2159
  br label %42, !dbg !2160

; <label>:42:                                     ; preds = %39, %14
  %43 = load %struct._IO_FILE*, %struct._IO_FILE** @Event_file_handle, align 4, !dbg !2161
  %44 = icmp ne %struct._IO_FILE* %43, null, !dbg !2163
  br i1 %44, label %45, label %48, !dbg !2164

; <label>:45:                                     ; preds = %42
  %46 = load %struct._IO_FILE*, %struct._IO_FILE** @Event_file_handle, align 4, !dbg !2165
  %47 = call i32 @fclose(%struct._IO_FILE* %46), !dbg !2166
  br label %48, !dbg !2166

; <label>:48:                                     ; preds = %45, %42
  %49 = call i32 (i8*, i32, ...) @open(i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.6.108, i32 0, i32 0), i32 0), !dbg !2167
  store i32 %49, i32* %8, align 4, !dbg !2168
  %50 = load i32, i32* %8, align 4, !dbg !2169
  %51 = icmp ne i32 %50, -1, !dbg !2171
  br i1 %51, label %52, label %65, !dbg !2172

; <label>:52:                                     ; preds = %48
  %53 = load i32, i32* %8, align 4, !dbg !2173
  %54 = call i32 @dup2(i32 %53, i32 0) #7, !dbg !2176
  %55 = icmp eq i32 %54, -1, !dbg !2177
  br i1 %55, label %56, label %62, !dbg !2178

; <label>:56:                                     ; preds = %52
  %57 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !2179
  %58 = load i8*, i8** %5, align 4, !dbg !2179
  %59 = call i32* @__errno_location() #1, !dbg !2179
  %60 = load i32, i32* %59, align 4, !dbg !2179
  call void @__AMI_fake_direct_transfer(), !dbg !2180
  %61 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %57, i8* getelementptr inbounds ([63 x i8], [63 x i8]* @.str.7.109, i32 0, i32 0), i8* %58, i32 %60), !dbg !2180
  br label %62, !dbg !2179

; <label>:62:                                     ; preds = %56, %52
  %63 = load i32, i32* %8, align 4, !dbg !2182
  %64 = call i32 @close(i32 %63), !dbg !2183
  br label %71, !dbg !2184

; <label>:65:                                     ; preds = %48
  %66 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !2185
  %67 = load i8*, i8** %5, align 4, !dbg !2185
  %68 = call i32* @__errno_location() #1, !dbg !2185
  %69 = load i32, i32* %68, align 4, !dbg !2185
  call void @__AMI_fake_direct_transfer(), !dbg !2186
  %70 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %66, i8* getelementptr inbounds ([71 x i8], [71 x i8]* @.str.8.110, i32 0, i32 0), i8* %67, i32 %69), !dbg !2186
  br label %71

; <label>:71:                                     ; preds = %65, %62
  %72 = call i32 @close(i32 0), !dbg !2188
  %73 = load i8*, i8** %5, align 4, !dbg !2189
  %74 = load i8**, i8*** %6, align 4, !dbg !2190
  %75 = call i32 @execvp(i8* %73, i8** %74) #7, !dbg !2191
  %76 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !2192
  %77 = load i8*, i8** %5, align 4, !dbg !2192
  %78 = call i32* @__errno_location() #1, !dbg !2192
  %79 = load i32, i32* %78, align 4, !dbg !2192
  call void @__AMI_fake_direct_transfer(), !dbg !2193
  %80 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %76, i8* getelementptr inbounds ([66 x i8], [66 x i8]* @.str.9.111, i32 0, i32 0), i8* %77, i32 %79), !dbg !2193
  %81 = call i32* @__errno_location() #1, !dbg !2195
  %82 = load i32, i32* %81, align 4, !dbg !2195
  call void @exit(i32 %82) #10, !dbg !2196
  unreachable, !dbg !2197

; <label>:83:                                     ; preds = %3
  %84 = load i32*, i32** %4, align 4, !dbg !2198
  %85 = load i32, i32* %84, align 4, !dbg !2201
  %86 = icmp sgt i32 %85, 0, !dbg !2202
  br i1 %86, label %87, label %88, !dbg !2203

; <label>:87:                                     ; preds = %83
  store i32 0, i32* %7, align 4, !dbg !2204
  br label %96, !dbg !2205

; <label>:88:                                     ; preds = %83
  %89 = call i32* @__errno_location() #1, !dbg !2206
  %90 = load i32, i32* %89, align 4, !dbg !2206
  store i32 %90, i32* %7, align 4, !dbg !2208
  %91 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !2209
  %92 = load i8*, i8** %5, align 4, !dbg !2209
  %93 = call i32* @__errno_location() #1, !dbg !2209
  %94 = load i32, i32* %93, align 4, !dbg !2209
  call void @__AMI_fake_direct_transfer(), !dbg !2210
  %95 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %91, i8* getelementptr inbounds ([50 x i8], [50 x i8]* @.str.10.112, i32 0, i32 0), i8* %92, i32 %94), !dbg !2210
  br label %96

; <label>:96:                                     ; preds = %88, %87
  br label %97

; <label>:97:                                     ; preds = %96
  %98 = load i32, i32* %7, align 4, !dbg !2212
  ret i32 %98, !dbg !2213
}

; Function Attrs: nounwind
declare i32 @fork() #2 section ".CODE_REGION_2_"

; Function Attrs: nounwind
declare i32 @fileno(%struct._IO_FILE*) #2 section ".CODE_REGION_2_"

; Function Attrs: nounwind
declare i32 @dup2(i32, i32) #2 section ".CODE_REGION_2_"

declare i32 @open(i8*, i32, ...) #5 section ".CODE_REGION_1_"

; Function Attrs: nounwind
declare i32 @execvp(i8*, i8**) #2 section ".CODE_REGION_2_"

; Function Attrs: noreturn nounwind
declare void @exit(i32) #8 section ".CODE_REGION_2_"

; Function Attrs: nounwind
define i32 @configure_timer(float) #0 section ".CODE_REGION_2_" !dbg !2214 {
  %2 = alloca float, align 4
  %3 = alloca i32, align 4
  %4 = alloca %struct.itimerval, align 4
  store float %0, float* %2, align 4
  call void @llvm.dbg.declare(metadata float* %2, metadata !2218, metadata !336), !dbg !2219
  call void @llvm.dbg.declare(metadata i32* %3, metadata !2220, metadata !336), !dbg !2221
  call void @llvm.dbg.declare(metadata %struct.itimerval* %4, metadata !2222, metadata !336), !dbg !2231
  %5 = load float, float* %2, align 4, !dbg !2232
  %6 = fcmp olt float %5, 0.000000e+00, !dbg !2234
  br i1 %6, label %7, label %16, !dbg !2235

; <label>:7:                                      ; preds = %1
  %8 = getelementptr inbounds %struct.itimerval, %struct.itimerval* %4, i32 0, i32 1, !dbg !2236
  %9 = getelementptr inbounds %struct.timeval, %struct.timeval* %8, i32 0, i32 0, !dbg !2238
  store i32 0, i32* %9, align 4, !dbg !2239
  %10 = getelementptr inbounds %struct.itimerval, %struct.itimerval* %4, i32 0, i32 1, !dbg !2240
  %11 = getelementptr inbounds %struct.timeval, %struct.timeval* %10, i32 0, i32 1, !dbg !2241
  store i32 0, i32* %11, align 4, !dbg !2242
  %12 = getelementptr inbounds %struct.itimerval, %struct.itimerval* %4, i32 0, i32 0, !dbg !2243
  %13 = getelementptr inbounds %struct.timeval, %struct.timeval* %12, i32 0, i32 0, !dbg !2244
  store i32 0, i32* %13, align 4, !dbg !2245
  %14 = getelementptr inbounds %struct.itimerval, %struct.itimerval* %4, i32 0, i32 0, !dbg !2246
  %15 = getelementptr inbounds %struct.timeval, %struct.timeval* %14, i32 0, i32 1, !dbg !2247
  store i32 0, i32* %15, align 4, !dbg !2248
  br label %36, !dbg !2249

; <label>:16:                                     ; preds = %1
  %17 = getelementptr inbounds %struct.itimerval, %struct.itimerval* %4, i32 0, i32 1, !dbg !2250
  %18 = getelementptr inbounds %struct.timeval, %struct.timeval* %17, i32 0, i32 0, !dbg !2252
  store i32 0, i32* %18, align 4, !dbg !2253
  %19 = getelementptr inbounds %struct.itimerval, %struct.itimerval* %4, i32 0, i32 1, !dbg !2254
  %20 = getelementptr inbounds %struct.timeval, %struct.timeval* %19, i32 0, i32 1, !dbg !2255
  store i32 250000, i32* %20, align 4, !dbg !2256
  %21 = load float, float* %2, align 4, !dbg !2257
  %22 = fptosi float %21 to i32, !dbg !2258
  %23 = getelementptr inbounds %struct.itimerval, %struct.itimerval* %4, i32 0, i32 0, !dbg !2259
  %24 = getelementptr inbounds %struct.timeval, %struct.timeval* %23, i32 0, i32 0, !dbg !2260
  store i32 %22, i32* %24, align 4, !dbg !2261
  %25 = load float, float* %2, align 4, !dbg !2262
  %26 = getelementptr inbounds %struct.itimerval, %struct.itimerval* %4, i32 0, i32 0, !dbg !2263
  %27 = getelementptr inbounds %struct.timeval, %struct.timeval* %26, i32 0, i32 0, !dbg !2264
  %28 = load i32, i32* %27, align 4, !dbg !2264
  %29 = sitofp i32 %28 to float, !dbg !2265
  %30 = fsub float %25, %29, !dbg !2266
  %31 = fpext float %30 to double, !dbg !2267
  %32 = fmul double %31, 1.000000e+06, !dbg !2268
  %33 = fptosi double %32 to i32, !dbg !2269
  %34 = getelementptr inbounds %struct.itimerval, %struct.itimerval* %4, i32 0, i32 0, !dbg !2270
  %35 = getelementptr inbounds %struct.timeval, %struct.timeval* %34, i32 0, i32 1, !dbg !2271
  store i32 %33, i32* %35, align 4, !dbg !2272
  br label %36

; <label>:36:                                     ; preds = %16, %7
  %37 = call i32 @setitimer(i32 0, %struct.itimerval* %4, %struct.itimerval* null) #7, !dbg !2273
  %38 = icmp eq i32 %37, 0, !dbg !2275
  br i1 %38, label %39, label %48, !dbg !2276

; <label>:39:                                     ; preds = %36
  %40 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !2277
  %41 = getelementptr inbounds %struct.itimerval, %struct.itimerval* %4, i32 0, i32 0, !dbg !2277
  %42 = getelementptr inbounds %struct.timeval, %struct.timeval* %41, i32 0, i32 0, !dbg !2277
  %43 = load i32, i32* %42, align 4, !dbg !2277
  %44 = getelementptr inbounds %struct.itimerval, %struct.itimerval* %4, i32 0, i32 0, !dbg !2277
  %45 = getelementptr inbounds %struct.timeval, %struct.timeval* %44, i32 0, i32 1, !dbg !2277
  %46 = load i32, i32* %45, align 4, !dbg !2277
  call void @__AMI_fake_direct_transfer(), !dbg !2277
  %47 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %40, i8* getelementptr inbounds ([46 x i8], [46 x i8]* @.str.11.115, i32 0, i32 0), i32 %43, i32 %46), !dbg !2277
  store i32 0, i32* %3, align 4, !dbg !2279
  br label %58, !dbg !2280

; <label>:48:                                     ; preds = %36
  %49 = call i32* @__errno_location() #1, !dbg !2281
  %50 = load i32, i32* %49, align 4, !dbg !2281
  store i32 %50, i32* %3, align 4, !dbg !2283
  %51 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !2284
  %52 = call i32* @__errno_location() #1, !dbg !2284
  %53 = load i32, i32* %52, align 4, !dbg !2284
  %54 = call i32* @__errno_location() #1, !dbg !2285
  %55 = load i32, i32* %54, align 4, !dbg !2284
  %56 = call i8* @strerror(i32 %55) #7, !dbg !2287
  call void @__AMI_fake_direct_transfer(), !dbg !2289
  %57 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %51, i8* getelementptr inbounds ([35 x i8], [35 x i8]* @.str.12.116, i32 0, i32 0), i32 %53, i8* %56), !dbg !2289
  br label %58

; <label>:58:                                     ; preds = %48, %39
  %59 = load i32, i32* %3, align 4, !dbg !2291
  ret i32 %59, !dbg !2292
}

; Function Attrs: nounwind
declare i32 @setitimer(i32, %struct.itimerval*, %struct.itimerval*) #2 section ".CODE_REGION_2_"

; Function Attrs: nounwind
define i32 @daemonize(i8*) #0 section ".CODE_REGION_2_" !dbg !2293 {
  %2 = alloca i8*, align 4
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  store i8* %0, i8** %2, align 4
  call void @llvm.dbg.declare(metadata i8** %2, metadata !2294, metadata !336), !dbg !2295
  call void @llvm.dbg.declare(metadata i32* %3, metadata !2296, metadata !336), !dbg !2297
  call void @llvm.dbg.declare(metadata i32* %4, metadata !2298, metadata !336), !dbg !2299
  call void @llvm.dbg.declare(metadata i32* %5, metadata !2300, metadata !336), !dbg !2301
  call void @llvm.dbg.declare(metadata i32* %6, metadata !2302, metadata !336), !dbg !2303
  %7 = call i32 @fork() #7, !dbg !2304
  store i32 %7, i32* %4, align 4, !dbg !2305
  %8 = load i32, i32* %4, align 4, !dbg !2306
  %9 = icmp ne i32 %8, -1, !dbg !2308
  br i1 %9, label %10, label %69, !dbg !2309

; <label>:10:                                     ; preds = %1
  %11 = load i32, i32* %4, align 4, !dbg !2310
  %12 = icmp sgt i32 %11, 0, !dbg !2313
  br i1 %12, label %13, label %14, !dbg !2314

; <label>:13:                                     ; preds = %10
  call void @exit(i32 0) #10, !dbg !2315
  unreachable, !dbg !2315

; <label>:14:                                     ; preds = %10
  %15 = call i32 @setsid() #7, !dbg !2316
  %16 = icmp ne i32 %15, -1, !dbg !2318
  br i1 %16, label %17, label %61, !dbg !2319

; <label>:17:                                     ; preds = %14
  %18 = call void (i32)* @signal(i32 17, void (i32)* inttoptr (i32 1 to void (i32)*)) #7, !dbg !2320
  %19 = call void (i32)* @signal(i32 1, void (i32)* inttoptr (i32 1 to void (i32)*)) #7, !dbg !2322
  %20 = call i32 @fork() #7, !dbg !2323
  store i32 %20, i32* %4, align 4, !dbg !2324
  %21 = load i32, i32* %4, align 4, !dbg !2325
  %22 = icmp ne i32 %21, -1, !dbg !2327
  br i1 %22, label %23, label %53, !dbg !2328

; <label>:23:                                     ; preds = %17
  %24 = load i32, i32* %4, align 4, !dbg !2329
  %25 = icmp sgt i32 %24, 0, !dbg !2332
  br i1 %25, label %26, label %27, !dbg !2333

; <label>:26:                                     ; preds = %23
  call void @exit(i32 0) #10, !dbg !2334
  unreachable, !dbg !2334

; <label>:27:                                     ; preds = %23
  %28 = call i32 @umask(i32 0) #7, !dbg !2335
  %29 = load i8*, i8** %2, align 4, !dbg !2336
  %30 = call i32 @chdir(i8* %29) #7, !dbg !2337
  %31 = call i32 (i8*, i32, ...) @open(i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.6.108, i32 0, i32 0), i32 0), !dbg !2338
  store i32 %31, i32* %5, align 4, !dbg !2339
  %32 = load i32, i32* %5, align 4, !dbg !2340
  %33 = icmp ne i32 %32, -1, !dbg !2342
  br i1 %33, label %34, label %39, !dbg !2343

; <label>:34:                                     ; preds = %27
  %35 = load i32, i32* %5, align 4, !dbg !2344
  %36 = call i32 @dup2(i32 %35, i32 0) #7, !dbg !2346
  %37 = load i32, i32* %5, align 4, !dbg !2347
  %38 = call i32 @close(i32 %37), !dbg !2348
  br label %40, !dbg !2349

; <label>:39:                                     ; preds = %27
  call void @perror(i8* getelementptr inbounds ([65 x i8], [65 x i8]* @.str.13.117, i32 0, i32 0)), !dbg !2350
  br label %40

; <label>:40:                                     ; preds = %39, %34
  %41 = call i32 (i8*, i32, ...) @open(i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.6.108, i32 0, i32 0), i32 1), !dbg !2351
  store i32 %41, i32* %6, align 4, !dbg !2352
  %42 = load i32, i32* %6, align 4, !dbg !2353
  %43 = icmp ne i32 %42, -1, !dbg !2355
  br i1 %43, label %44, label %51, !dbg !2356

; <label>:44:                                     ; preds = %40
  %45 = load i32, i32* %6, align 4, !dbg !2357
  %46 = call i32 @dup2(i32 %45, i32 2) #7, !dbg !2359
  %47 = load i32, i32* %6, align 4, !dbg !2360
  %48 = call i32 @dup2(i32 %47, i32 1) #7, !dbg !2361
  %49 = load i32, i32* %6, align 4, !dbg !2362
  %50 = call i32 @close(i32 %49), !dbg !2363
  br label %52, !dbg !2364

; <label>:51:                                     ; preds = %40
  call void @perror(i8* getelementptr inbounds ([65 x i8], [65 x i8]* @.str.14.118, i32 0, i32 0)), !dbg !2365
  br label %52

; <label>:52:                                     ; preds = %51, %44
  br label %60, !dbg !2366

; <label>:53:                                     ; preds = %17
  %54 = call i32* @__errno_location() #1, !dbg !2367
  %55 = load i32, i32* %54, align 4, !dbg !2367
  store i32 %55, i32* %3, align 4, !dbg !2369
  %56 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 4, !dbg !2370
  %57 = call i32* @__errno_location() #1, !dbg !2371
  %58 = load i32, i32* %57, align 4, !dbg !2371
  %59 = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %56, i8* getelementptr inbounds ([56 x i8], [56 x i8]* @.str.15.119, i32 0, i32 0), i32 %58), !dbg !2372
  br label %60

; <label>:60:                                     ; preds = %53, %52
  br label %68, !dbg !2374

; <label>:61:                                     ; preds = %14
  %62 = call i32* @__errno_location() #1, !dbg !2375
  %63 = load i32, i32* %62, align 4, !dbg !2375
  store i32 %63, i32* %3, align 4, !dbg !2377
  %64 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 4, !dbg !2378
  %65 = call i32* @__errno_location() #1, !dbg !2379
  %66 = load i32, i32* %65, align 4, !dbg !2379
  %67 = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %64, i8* getelementptr inbounds ([79 x i8], [79 x i8]* @.str.16.120, i32 0, i32 0), i32 %66), !dbg !2380
  br label %68

; <label>:68:                                     ; preds = %61, %60
  br label %76, !dbg !2382

; <label>:69:                                     ; preds = %1
  %70 = call i32* @__errno_location() #1, !dbg !2383
  %71 = load i32, i32* %70, align 4, !dbg !2383
  store i32 %71, i32* %3, align 4, !dbg !2385
  %72 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 4, !dbg !2386
  %73 = call i32* @__errno_location() #1, !dbg !2387
  %74 = load i32, i32* %73, align 4, !dbg !2387
  %75 = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %72, i8* getelementptr inbounds ([55 x i8], [55 x i8]* @.str.17.121, i32 0, i32 0), i32 %74), !dbg !2388
  br label %76

; <label>:76:                                     ; preds = %69, %68
  %77 = load i32, i32* %3, align 4, !dbg !2390
  ret i32 %77, !dbg !2391
}

; Function Attrs: nounwind
declare i32 @setsid() #2 section ".CODE_REGION_2_"

; Function Attrs: nounwind
declare void (i32)* @signal(i32, void (i32)*) #2 section ".CODE_REGION_2_"

; Function Attrs: nounwind
declare i32 @umask(i32) #2 section ".CODE_REGION_2_"

; Function Attrs: nounwind
declare i32 @chdir(i8*) #2 section ".CODE_REGION_2_"

declare void @perror(i8*) #5 section ".CODE_REGION_2_"

; Function Attrs: nounwind
define void @get_localtime_str(i8*, i32) #0 section ".CODE_REGION_1_" !dbg !2392 {
  %3 = alloca i8*, align 4
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  %6 = alloca %struct.tm*, align 4
  store i8* %0, i8** %3, align 4
  call void @llvm.dbg.declare(metadata i8** %3, metadata !2395, metadata !336), !dbg !2396
  store i32 %1, i32* %4, align 4
  call void @llvm.dbg.declare(metadata i32* %4, metadata !2397, metadata !336), !dbg !2398
  call void @llvm.dbg.declare(metadata i32* %5, metadata !2399, metadata !336), !dbg !2400
  call void @llvm.dbg.declare(metadata %struct.tm** %6, metadata !2401, metadata !336), !dbg !2416
  %7 = call i32 @time(i32* null) #7, !dbg !2417
  store i32 %7, i32* %5, align 4, !dbg !2418
  %8 = load i32, i32* %5, align 4, !dbg !2419
  %9 = icmp ne i32 %8, -1, !dbg !2421
  br i1 %9, label %10, label %25, !dbg !2422

; <label>:10:                                     ; preds = %2
  %11 = call %struct.tm* @localtime(i32* %5) #7, !dbg !2423
  store %struct.tm* %11, %struct.tm** %6, align 4, !dbg !2425
  %12 = load i8*, i8** %3, align 4, !dbg !2426
  %13 = load i32, i32* %4, align 4, !dbg !2428
  %14 = load %struct.tm*, %struct.tm** %6, align 4, !dbg !2429
  %15 = call i32 @strftime(i8* %12, i32 %13, i8* getelementptr inbounds ([18 x i8], [18 x i8]* @.str.126, i32 0, i32 0), %struct.tm* %14) #7, !dbg !2430
  %16 = icmp eq i32 %15, 0, !dbg !2431
  br i1 %16, label %17, label %24, !dbg !2432

; <label>:17:                                     ; preds = %10
  %18 = load i32, i32* %4, align 4, !dbg !2433
  %19 = icmp ugt i32 %18, 0, !dbg !2435
  br i1 %19, label %20, label %23, !dbg !2436

; <label>:20:                                     ; preds = %17
  %21 = load i8*, i8** %3, align 4, !dbg !2437
  %22 = getelementptr inbounds i8, i8* %21, i32 0, !dbg !2437
  store i8 0, i8* %22, align 1, !dbg !2438
  br label %23, !dbg !2437

; <label>:23:                                     ; preds = %20, %17
  br label %24, !dbg !2439

; <label>:24:                                     ; preds = %23, %10
  br label %32, !dbg !2441

; <label>:25:                                     ; preds = %2
  %26 = load i32, i32* %4, align 4, !dbg !2442
  %27 = icmp ugt i32 %26, 0, !dbg !2445
  br i1 %27, label %28, label %31, !dbg !2446

; <label>:28:                                     ; preds = %25
  %29 = load i8*, i8** %3, align 4, !dbg !2447
  %30 = getelementptr inbounds i8, i8* %29, i32 0, !dbg !2447
  store i8 0, i8* %30, align 1, !dbg !2448
  br label %31, !dbg !2447

; <label>:31:                                     ; preds = %28, %25
  br label %32

; <label>:32:                                     ; preds = %31, %24
  call void @__AMI_fake_rt_transfer(), !dbg !2449
  ret void, !dbg !2449
}

; Function Attrs: nounwind
declare i32 @time(i32*) #2 section ".CODE_REGION_1_"

; Function Attrs: nounwind
declare %struct.tm* @localtime(i32*) #2 section ".CODE_REGION_1_"

; Function Attrs: nounwind
declare i32 @strftime(i8*, i32, i8*, %struct.tm*) #2 section ".CODE_REGION_1_"

; Function Attrs: nounwind
define i32 @msg_printf(%struct._IO_FILE*, i8*, ...) #0 section ".CODE_REGION_1_" !dbg !2450 {
  %3 = alloca %struct._IO_FILE*, align 4
  %4 = alloca i8*, align 4
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  %7 = alloca i32, align 4
  %8 = alloca %struct.__va_list, align 4
  %9 = alloca [20 x i8], align 1
  store %struct._IO_FILE* %0, %struct._IO_FILE** %3, align 4
  call void @llvm.dbg.declare(metadata %struct._IO_FILE** %3, metadata !2453, metadata !336), !dbg !2454
  store i8* %1, i8** %4, align 4
  call void @llvm.dbg.declare(metadata i8** %4, metadata !2455, metadata !336), !dbg !2456
  call void @llvm.dbg.declare(metadata i32* %5, metadata !2457, metadata !336), !dbg !2458
  %10 = load i32, i32* @Console_messages, align 4, !dbg !2459
  %11 = icmp ne i32 %10, 0, !dbg !2459
  br i1 %11, label %15, label %12, !dbg !2461

; <label>:12:                                     ; preds = %2
  %13 = load %struct._IO_FILE*, %struct._IO_FILE** %3, align 4, !dbg !2462
  %14 = icmp ne %struct._IO_FILE* %13, null, !dbg !2464
  br i1 %14, label %15, label %49, !dbg !2465

; <label>:15:                                     ; preds = %12, %2
  call void @llvm.dbg.declare(metadata i32* %6, metadata !2466, metadata !336), !dbg !2468
  store i32 0, i32* %6, align 4, !dbg !2468
  call void @llvm.dbg.declare(metadata i32* %7, metadata !2469, metadata !336), !dbg !2470
  store i32 0, i32* %7, align 4, !dbg !2470
  call void @llvm.dbg.declare(metadata %struct.__va_list* %8, metadata !2471, metadata !336), !dbg !2479
  call void @llvm.dbg.declare(metadata [20 x i8]* %9, metadata !2480, metadata !336), !dbg !2484
  %16 = getelementptr inbounds [20 x i8], [20 x i8]* %9, i32 0, i32 0, !dbg !2485
  call void @get_localtime_str(i8* %16, i32 20), !dbg !2486
  %17 = bitcast %struct.__va_list* %8 to i8*, !dbg !2487
  call void @llvm.va_start(i8* %17), !dbg !2487
  %18 = load i32, i32* @Console_messages, align 4, !dbg !2488
  %19 = icmp ne i32 %18, 0, !dbg !2488
  br i1 %19, label %20, label %26, !dbg !2490

; <label>:20:                                     ; preds = %15
  %21 = load i8*, i8** %4, align 4, !dbg !2491
  %22 = getelementptr inbounds %struct.__va_list, %struct.__va_list* %8, i32 0, i32 0, !dbg !2492
  %23 = bitcast i8** %22 to [1 x i32]*, !dbg !2492
  %24 = load [1 x i32], [1 x i32]* %23, align 4, !dbg !2492
  %25 = call i32 @vprintf(i8* %21, [1 x i32] %24), !dbg !2492
  store i32 %25, i32* %6, align 4, !dbg !2493
  br label %26, !dbg !2494

; <label>:26:                                     ; preds = %20, %15
  %27 = load %struct._IO_FILE*, %struct._IO_FILE** %3, align 4, !dbg !2495
  %28 = icmp ne %struct._IO_FILE* %27, null, !dbg !2497
  br i1 %28, label %29, label %39, !dbg !2498

; <label>:29:                                     ; preds = %26
  %30 = load %struct._IO_FILE*, %struct._IO_FILE** %3, align 4, !dbg !2499
  %31 = getelementptr inbounds [20 x i8], [20 x i8]* %9, i32 0, i32 0, !dbg !2501
  %32 = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %30, i8* getelementptr inbounds ([6 x i8], [6 x i8]* @.str.1.129, i32 0, i32 0), i8* %31), !dbg !2502
  %33 = load %struct._IO_FILE*, %struct._IO_FILE** %3, align 4, !dbg !2503
  %34 = load i8*, i8** %4, align 4, !dbg !2504
  %35 = getelementptr inbounds %struct.__va_list, %struct.__va_list* %8, i32 0, i32 0, !dbg !2505
  %36 = bitcast i8** %35 to [1 x i32]*, !dbg !2505
  %37 = load [1 x i32], [1 x i32]* %36, align 4, !dbg !2505
  %38 = call i32 @vfprintf(%struct._IO_FILE* %33, i8* %34, [1 x i32] %37), !dbg !2505
  store i32 %38, i32* %7, align 4, !dbg !2506
  br label %39, !dbg !2507

; <label>:39:                                     ; preds = %29, %26
  %40 = bitcast %struct.__va_list* %8 to i8*, !dbg !2508
  call void @llvm.va_end(i8* %40), !dbg !2508
  %41 = load i32, i32* %6, align 4, !dbg !2509
  %42 = icmp ne i32 %41, 0, !dbg !2510
  br i1 %42, label %43, label %45, !dbg !2511

; <label>:43:                                     ; preds = %39
  %44 = load i32, i32* %6, align 4, !dbg !2512
  br label %47, !dbg !2514

; <label>:45:                                     ; preds = %39
  %46 = load i32, i32* %7, align 4, !dbg !2515
  br label %47, !dbg !2517

; <label>:47:                                     ; preds = %45, %43
  %48 = phi i32 [ %44, %43 ], [ %46, %45 ], !dbg !2518
  store i32 %48, i32* %5, align 4, !dbg !2520
  br label %50, !dbg !2521

; <label>:49:                                     ; preds = %12
  store i32 0, i32* %5, align 4, !dbg !2522
  br label %50

; <label>:50:                                     ; preds = %49, %47
  %51 = load i32, i32* %5, align 4, !dbg !2523
  call void @__AMI_fake_rt_transfer(), !dbg !2524
  ret i32 %51, !dbg !2524
}

; Function Attrs: nounwind
declare void @llvm.va_start(i8*) #7

declare i32 @vprintf(i8*, [1 x i32]) #5 section ".CODE_REGION_1_"

declare i32 @vfprintf(%struct._IO_FILE*, i8*, [1 x i32]) #5 section ".CODE_REGION_1_"

; Function Attrs: nounwind
declare void @llvm.va_end(i8*) #7

; Function Attrs: nounwind
define %struct._IO_FILE* @open_msg_file(i8*, i32) #0 section ".CODE_REGION_2_" !dbg !2525 {
  %3 = alloca i8*, align 4
  %4 = alloca i32, align 4
  %5 = alloca %struct._IO_FILE*, align 4
  %6 = alloca i32, align 4
  %7 = alloca i32, align 4
  %8 = alloca [20 x i8], align 1
  %9 = alloca i8*, align 4
  store i8* %0, i8** %3, align 4
  call void @llvm.dbg.declare(metadata i8** %3, metadata !2528, metadata !336), !dbg !2529
  store i32 %1, i32* %4, align 4
  call void @llvm.dbg.declare(metadata i32* %4, metadata !2530, metadata !336), !dbg !2531
  call void @llvm.dbg.declare(metadata %struct._IO_FILE** %5, metadata !2532, metadata !336), !dbg !2533
  %10 = load i8*, i8** %3, align 4, !dbg !2534
  %11 = call %struct._IO_FILE* @fopen(i8* %10, i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str.2.130, i32 0, i32 0)), !dbg !2535
  store %struct._IO_FILE* %11, %struct._IO_FILE** %5, align 4, !dbg !2536
  %12 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !2537
  %13 = icmp ne %struct._IO_FILE* %12, null, !dbg !2537
  br i1 %13, label %14, label %71, !dbg !2539

; <label>:14:                                     ; preds = %2
  call void @llvm.dbg.declare(metadata i32* %6, metadata !2540, metadata !336), !dbg !2542
  call void @llvm.dbg.declare(metadata i32* %7, metadata !2543, metadata !336), !dbg !2544
  call void @llvm.dbg.declare(metadata [20 x i8]* %8, metadata !2545, metadata !336), !dbg !2546
  %15 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !2547
  %16 = call i32 @fileno(%struct._IO_FILE* %15) #7, !dbg !2548
  %17 = call i32 @flock(i32 %16, i32 8) #7, !dbg !2549
  %18 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !2551
  call void @setbuf(%struct._IO_FILE* %18, i8* null) #7, !dbg !2552
  %19 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !2553
  %20 = call i32 @fseek(%struct._IO_FILE* %19, i32 0, i32 2), !dbg !2554
  %21 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !2555
  %22 = call i32 @ftell(%struct._IO_FILE* %21), !dbg !2556
  store i32 %22, i32* %6, align 4, !dbg !2557
  %23 = load i32, i32* %6, align 4, !dbg !2558
  %24 = load i32, i32* %4, align 4, !dbg !2560
  %25 = icmp sgt i32 %23, %24, !dbg !2561
  br i1 %25, label %26, label %59, !dbg !2562

; <label>:26:                                     ; preds = %14
  call void @llvm.dbg.declare(metadata i8** %9, metadata !2563, metadata !336), !dbg !2565
  %27 = load i32, i32* %4, align 4, !dbg !2566
  %28 = mul i32 %27, 1, !dbg !2567
  %29 = call noalias i8* @malloc(i32 %28) #7, !dbg !2568
  store i8* %29, i8** %9, align 4, !dbg !2569
  %30 = load i8*, i8** %9, align 4, !dbg !2570
  %31 = icmp ne i8* %30, null, !dbg !2570
  br i1 %31, label %32, label %58, !dbg !2572

; <label>:32:                                     ; preds = %26
  %33 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !2573
  %34 = load i32, i32* %4, align 4, !dbg !2575
  %35 = sub nsw i32 0, %34, !dbg !2576
  %36 = call i32 @fseek(%struct._IO_FILE* %33, i32 %35, i32 2), !dbg !2577
  %37 = load i8*, i8** %9, align 4, !dbg !2578
  %38 = load i32, i32* %4, align 4, !dbg !2579
  %39 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !2580
  %40 = call i32 @fread(i8* %37, i32 1, i32 %38, %struct._IO_FILE* %39), !dbg !2581
  store i32 %40, i32* %7, align 4, !dbg !2582
  %41 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !2583
  %42 = call i32 @fclose(%struct._IO_FILE* %41), !dbg !2584
  %43 = load i8*, i8** %9, align 4, !dbg !2585
  call void @free(i8* %43) #7, !dbg !2586
  %44 = load i8*, i8** %3, align 4, !dbg !2587
  %45 = call %struct._IO_FILE* @fopen(i8* %44, i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.3.131, i32 0, i32 0)), !dbg !2588
  store %struct._IO_FILE* %45, %struct._IO_FILE** %5, align 4, !dbg !2589
  %46 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !2590
  %47 = icmp ne %struct._IO_FILE* %46, null, !dbg !2590
  br i1 %47, label %48, label %57, !dbg !2592

; <label>:48:                                     ; preds = %32
  %49 = getelementptr inbounds [20 x i8], [20 x i8]* %8, i32 0, i32 0, !dbg !2593
  call void @__AMI_fake_direct_transfer(), !dbg !2595
  call void @get_localtime_str(i8* %49, i32 20), !dbg !2595
  %50 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !2596
  %51 = getelementptr inbounds [20 x i8], [20 x i8]* %8, i32 0, i32 0, !dbg !2597
  %52 = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %50, i8* getelementptr inbounds ([31 x i8], [31 x i8]* @.str.4.132, i32 0, i32 0), i8* %51), !dbg !2598
  %53 = load i8*, i8** %9, align 4, !dbg !2599
  %54 = load i32, i32* %7, align 4, !dbg !2600
  %55 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !2601
  %56 = call i32 @fwrite(i8* %53, i32 1, i32 %54, %struct._IO_FILE* %55), !dbg !2602
  br label %57, !dbg !2603

; <label>:57:                                     ; preds = %48, %32
  br label %58, !dbg !2604

; <label>:58:                                     ; preds = %57, %26
  br label %59, !dbg !2605

; <label>:59:                                     ; preds = %58, %14
  %60 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !2606
  %61 = icmp ne %struct._IO_FILE* %60, null, !dbg !2606
  br i1 %61, label %62, label %70, !dbg !2608

; <label>:62:                                     ; preds = %59
  %63 = getelementptr inbounds [20 x i8], [20 x i8]* %8, i32 0, i32 0, !dbg !2609
  call void @__AMI_fake_direct_transfer(), !dbg !2611
  call void @get_localtime_str(i8* %63, i32 20), !dbg !2611
  %64 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !2612
  %65 = getelementptr inbounds [20 x i8], [20 x i8]* %8, i32 0, i32 0, !dbg !2613
  %66 = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %64, i8* getelementptr inbounds ([64 x i8], [64 x i8]* @.str.5.133, i32 0, i32 0), i8* %65), !dbg !2614
  %67 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !2615
  %68 = getelementptr inbounds [20 x i8], [20 x i8]* %8, i32 0, i32 0, !dbg !2616
  %69 = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %67, i8* getelementptr inbounds ([28 x i8], [28 x i8]* @.str.6.134, i32 0, i32 0), i8* %68), !dbg !2617
  br label %70, !dbg !2618

; <label>:70:                                     ; preds = %62, %59
  br label %71, !dbg !2619

; <label>:71:                                     ; preds = %70, %2
  %72 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !2620
  ret %struct._IO_FILE* %72, !dbg !2621
}

; Function Attrs: nounwind
declare i32 @flock(i32, i32) #2 section ".CODE_REGION_2_"

; Function Attrs: nounwind
declare void @setbuf(%struct._IO_FILE*, i8*) #2 section ".CODE_REGION_2_"

declare i32 @fseek(%struct._IO_FILE*, i32, i32) #5 section ".CODE_REGION_2_"

declare i32 @ftell(%struct._IO_FILE*) #5 section ".CODE_REGION_2_"

; Function Attrs: nounwind
declare noalias i8* @malloc(i32) #2 section ".CODE_REGION_2_"

declare i32 @fread(i8*, i32, i32, %struct._IO_FILE*) #5 section ".CODE_REGION_2_"

; Function Attrs: nounwind
declare void @free(i8*) #2 section ".CODE_REGION_2_"

declare i32 @fwrite(i8*, i32, i32, %struct._IO_FILE*) #5 section ".CODE_REGION_2_"

; Function Attrs: nounwind
define void @close_log_file(%struct._IO_FILE*) #0 section ".CODE_REGION_2_" !dbg !2622 {
  %2 = alloca %struct._IO_FILE*, align 4
  %3 = alloca [20 x i8], align 1
  store %struct._IO_FILE* %0, %struct._IO_FILE** %2, align 4
  call void @llvm.dbg.declare(metadata %struct._IO_FILE** %2, metadata !2625, metadata !336), !dbg !2626
  %4 = load %struct._IO_FILE*, %struct._IO_FILE** %2, align 4, !dbg !2627
  %5 = icmp ne %struct._IO_FILE* %4, null, !dbg !2627
  br i1 %5, label %6, label %13, !dbg !2629

; <label>:6:                                      ; preds = %1
  call void @llvm.dbg.declare(metadata [20 x i8]* %3, metadata !2630, metadata !336), !dbg !2632
  %7 = getelementptr inbounds [20 x i8], [20 x i8]* %3, i32 0, i32 0, !dbg !2633
  call void @__AMI_fake_direct_transfer(), !dbg !2634
  call void @get_localtime_str(i8* %7, i32 20), !dbg !2634
  %8 = load %struct._IO_FILE*, %struct._IO_FILE** %2, align 4, !dbg !2635
  %9 = getelementptr inbounds [20 x i8], [20 x i8]* %3, i32 0, i32 0, !dbg !2636
  %10 = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %8, i8* getelementptr inbounds ([32 x i8], [32 x i8]* @.str.7.135, i32 0, i32 0), i8* %9), !dbg !2637
  %11 = load %struct._IO_FILE*, %struct._IO_FILE** %2, align 4, !dbg !2638
  %12 = call i32 @fclose(%struct._IO_FILE* %11), !dbg !2639
  br label %13, !dbg !2640

; <label>:13:                                     ; preds = %6, %1
  ret void, !dbg !2641
}

; Function Attrs: nounwind
define i32 @open_log_files() #0 section ".CODE_REGION_2_" !dbg !2642 {
  %1 = call %struct._IO_FILE* @open_msg_file(i8* getelementptr inbounds ([29 x i8], [29 x i8]* @.str.8.138, i32 0, i32 0), i32 52428800), !dbg !2643
  call void @__AMI_fake_local_wrt(), !dbg !2644
  store %struct._IO_FILE* %1, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !2644
  %2 = call %struct._IO_FILE* @open_msg_file(i8* getelementptr inbounds ([29 x i8], [29 x i8]* @.str.9.139, i32 0, i32 0), i32 52428800), !dbg !2645
  call void @__AMI_fake_local_wrt(), !dbg !2646
  store %struct._IO_FILE* %2, %struct._IO_FILE** @Event_file_handle, align 4, !dbg !2646
  %3 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !2647
  %4 = icmp eq %struct._IO_FILE* %3, null, !dbg !2648
  br i1 %4, label %8, label %5, !dbg !2649

; <label>:5:                                      ; preds = %0
  %6 = load %struct._IO_FILE*, %struct._IO_FILE** @Event_file_handle, align 4, !dbg !2650
  %7 = icmp eq %struct._IO_FILE* %6, null, !dbg !2652
  br label %8, !dbg !2653

; <label>:8:                                      ; preds = %5, %0
  %9 = phi i1 [ true, %0 ], [ %7, %5 ]
  %10 = zext i1 %9 to i32, !dbg !2654
  ret i32 %10, !dbg !2656
}

; Function Attrs: nounwind
define void @close_log_files() #0 section ".CODE_REGION_2_" !dbg !2657 {
  %1 = load %struct._IO_FILE*, %struct._IO_FILE** @Event_file_handle, align 4, !dbg !2658
  call void @close_log_file(%struct._IO_FILE* %1), !dbg !2659
  %2 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !2660
  call void @close_log_file(%struct._IO_FILE* %2), !dbg !2661
  ret void, !dbg !2662
}

; Function Attrs: nounwind
define i32 @GPIO_export(i32) #0 section ".CODE_REGION_1_" !dbg !2663 {
  %2 = alloca i32, align 4
  %3 = alloca [4 x i8], align 1
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  %7 = alloca [34 x i8], align 1
  %8 = alloca i32, align 4
  %9 = alloca i32, align 4
  store i32 %0, i32* %2, align 4
  call void @llvm.dbg.declare(metadata i32* %2, metadata !2666, metadata !336), !dbg !2667
  call void @llvm.dbg.declare(metadata [4 x i8]* %3, metadata !2668, metadata !336), !dbg !2670
  call void @llvm.dbg.declare(metadata i32* %4, metadata !2671, metadata !336), !dbg !2674
  call void @llvm.dbg.declare(metadata i32* %5, metadata !2675, metadata !336), !dbg !2676
  call void @llvm.dbg.declare(metadata i32* %6, metadata !2677, metadata !336), !dbg !2678
  %10 = call i32 (i8*, i32, ...) @open(i8* getelementptr inbounds ([23 x i8], [23 x i8]* @.str.142, i32 0, i32 0), i32 1), !dbg !2679
  store i32 %10, i32* %5, align 4, !dbg !2680
  %11 = load i32, i32* %5, align 4, !dbg !2681
  %12 = icmp ne i32 -1, %11, !dbg !2683
  br i1 %12, label %13, label %54, !dbg !2684

; <label>:13:                                     ; preds = %1
  call void @llvm.dbg.declare(metadata [34 x i8]* %7, metadata !2685, metadata !336), !dbg !2690
  call void @llvm.dbg.declare(metadata i32* %8, metadata !2691, metadata !336), !dbg !2692
  call void @llvm.dbg.declare(metadata i32* %9, metadata !2693, metadata !336), !dbg !2694
  %14 = getelementptr inbounds [4 x i8], [4 x i8]* %3, i32 0, i32 0, !dbg !2695
  %15 = load i32, i32* %2, align 4, !dbg !2696
  %16 = call i32 (i8*, i32, i8*, ...) @snprintf(i8* %14, i32 4, i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.1.143, i32 0, i32 0), i32 %15) #7, !dbg !2697
  store i32 %16, i32* %4, align 4, !dbg !2698
  %17 = load i32, i32* %5, align 4, !dbg !2699
  %18 = getelementptr inbounds [4 x i8], [4 x i8]* %3, i32 0, i32 0, !dbg !2700
  %19 = load i32, i32* %4, align 4, !dbg !2701
  %20 = call i32 @write(i32 %17, i8* %18, i32 %19), !dbg !2702
  %21 = load i32, i32* %5, align 4, !dbg !2703
  %22 = call i32 @close(i32 %21), !dbg !2704
  %23 = getelementptr inbounds [34 x i8], [34 x i8]* %7, i32 0, i32 0, !dbg !2705
  %24 = load i32, i32* %2, align 4, !dbg !2706
  %25 = call i32 (i8*, i32, i8*, ...) @snprintf(i8* %23, i32 34, i8* getelementptr inbounds ([33 x i8], [33 x i8]* @.str.2.144, i32 0, i32 0), i32 %24) #7, !dbg !2707
  store i32 0, i32* %8, align 4, !dbg !2708
  store i32 0, i32* %9, align 4, !dbg !2709
  br label %26, !dbg !2710, !llvm.loop !2711

; <label>:26:                                     ; preds = %44, %13
  %27 = call i32 @usleep(i32 50000), !dbg !2712
  %28 = getelementptr inbounds [34 x i8], [34 x i8]* %7, i32 0, i32 0, !dbg !2714
  %29 = call i32 (i8*, i32, ...) @open(i8* %28, i32 1), !dbg !2715
  store i32 %29, i32* %5, align 4, !dbg !2716
  %30 = load i32, i32* %5, align 4, !dbg !2717
  %31 = icmp ne i32 -1, %30, !dbg !2719
  br i1 %31, label %32, label %35, !dbg !2720

; <label>:32:                                     ; preds = %26
  store i32 1, i32* %8, align 4, !dbg !2721
  %33 = load i32, i32* %5, align 4, !dbg !2723
  %34 = call i32 @close(i32 %33), !dbg !2724
  br label %36, !dbg !2725

; <label>:35:                                     ; preds = %26
  store i32 0, i32* %8, align 4, !dbg !2726
  br label %36

; <label>:36:                                     ; preds = %35, %32
  br label %37, !dbg !2727

; <label>:37:                                     ; preds = %36
  %38 = load i32, i32* %8, align 4, !dbg !2728
  %39 = icmp ne i32 %38, 0, !dbg !2728
  br i1 %39, label %44, label %40, !dbg !2729

; <label>:40:                                     ; preds = %37
  %41 = load i32, i32* %9, align 4, !dbg !2730
  %42 = add nsw i32 %41, 1, !dbg !2730
  store i32 %42, i32* %9, align 4, !dbg !2730
  %43 = icmp slt i32 %41, 20, !dbg !2732
  br label %44

; <label>:44:                                     ; preds = %40, %37
  %45 = phi i1 [ false, %37 ], [ %43, %40 ]
  br i1 %45, label %26, label %46, !dbg !2733, !llvm.loop !2711

; <label>:46:                                     ; preds = %44
  %47 = load i32, i32* %8, align 4, !dbg !2735
  %48 = icmp ne i32 %47, 0, !dbg !2735
  br i1 %48, label %49, label %50, !dbg !2737

; <label>:49:                                     ; preds = %46
  store i32 0, i32* %6, align 4, !dbg !2738
  br label %53, !dbg !2739

; <label>:50:                                     ; preds = %46
  %51 = call i32* @__errno_location() #1, !dbg !2740
  %52 = load i32, i32* %51, align 4, !dbg !2740
  store i32 %52, i32* %6, align 4, !dbg !2741
  br label %53

; <label>:53:                                     ; preds = %50, %49
  br label %57, !dbg !2742

; <label>:54:                                     ; preds = %1
  %55 = call i32* @__errno_location() #1, !dbg !2743
  %56 = load i32, i32* %55, align 4, !dbg !2743
  store i32 %56, i32* %6, align 4, !dbg !2744
  br label %57

; <label>:57:                                     ; preds = %54, %53
  %58 = load i32, i32* %6, align 4, !dbg !2745
  ret i32 %58, !dbg !2746
}

declare i32 @write(i32, i8*, i32) #5 section ".CODE_REGION_1_"

declare i32 @usleep(i32) #5 section ".CODE_REGION_1_"

; Function Attrs: nounwind
define i32 @GPIO_unexport(i32) #0 section ".CODE_REGION_1_" !dbg !2747 {
  %2 = alloca i32, align 4
  %3 = alloca [4 x i8], align 1
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  store i32 %0, i32* %2, align 4
  call void @llvm.dbg.declare(metadata i32* %2, metadata !2748, metadata !336), !dbg !2749
  call void @llvm.dbg.declare(metadata [4 x i8]* %3, metadata !2750, metadata !336), !dbg !2751
  call void @llvm.dbg.declare(metadata i32* %4, metadata !2752, metadata !336), !dbg !2753
  call void @llvm.dbg.declare(metadata i32* %5, metadata !2754, metadata !336), !dbg !2755
  call void @llvm.dbg.declare(metadata i32* %6, metadata !2756, metadata !336), !dbg !2757
  %7 = call i32 (i8*, i32, ...) @open(i8* getelementptr inbounds ([25 x i8], [25 x i8]* @.str.3.145, i32 0, i32 0), i32 1), !dbg !2758
  store i32 %7, i32* %5, align 4, !dbg !2759
  %8 = load i32, i32* %5, align 4, !dbg !2760
  %9 = icmp ne i32 -1, %8, !dbg !2762
  br i1 %9, label %10, label %20, !dbg !2763

; <label>:10:                                     ; preds = %1
  %11 = getelementptr inbounds [4 x i8], [4 x i8]* %3, i32 0, i32 0, !dbg !2764
  %12 = load i32, i32* %2, align 4, !dbg !2766
  %13 = call i32 (i8*, i32, i8*, ...) @snprintf(i8* %11, i32 4, i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.1.143, i32 0, i32 0), i32 %12) #7, !dbg !2767
  store i32 %13, i32* %4, align 4, !dbg !2768
  %14 = load i32, i32* %5, align 4, !dbg !2769
  %15 = getelementptr inbounds [4 x i8], [4 x i8]* %3, i32 0, i32 0, !dbg !2770
  %16 = load i32, i32* %4, align 4, !dbg !2771
  %17 = call i32 @write(i32 %14, i8* %15, i32 %16), !dbg !2772
  %18 = load i32, i32* %5, align 4, !dbg !2773
  %19 = call i32 @close(i32 %18), !dbg !2774
  store i32 0, i32* %6, align 4, !dbg !2775
  br label %23, !dbg !2776

; <label>:20:                                     ; preds = %1
  %21 = call i32* @__errno_location() #1, !dbg !2777
  %22 = load i32, i32* %21, align 4, !dbg !2777
  store i32 %22, i32* %6, align 4, !dbg !2778
  br label %23

; <label>:23:                                     ; preds = %20, %10
  %24 = load i32, i32* %6, align 4, !dbg !2779
  call void @__AMI_fake_rt_transfer(), !dbg !2780
  ret i32 %24, !dbg !2780
}

; Function Attrs: nounwind
define i32 @GPIO_direction(i32, i32) #0 section ".CODE_REGION_1_" !dbg !2781 {
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca [2 x i8*], align 4
  %6 = alloca [34 x i8], align 1
  %7 = alloca i32, align 4
  %8 = alloca i32, align 4
  %9 = alloca i8*, align 4
  store i32 %0, i32* %3, align 4
  call void @llvm.dbg.declare(metadata i32* %3, metadata !2784, metadata !336), !dbg !2785
  store i32 %1, i32* %4, align 4
  call void @llvm.dbg.declare(metadata i32* %4, metadata !2786, metadata !336), !dbg !2787
  call void @llvm.dbg.declare(metadata [2 x i8*]* %5, metadata !2788, metadata !336), !dbg !2790
  %10 = bitcast [2 x i8*]* %5 to i8*, !dbg !2790
  call void @llvm.memcpy.p0i8.p0i8.i32(i8* %10, i8* bitcast ([2 x i8*]* @GPIO_direction.s_directions_str to i8*), i32 8, i32 4, i1 false), !dbg !2790
  call void @llvm.dbg.declare(metadata [34 x i8]* %6, metadata !2791, metadata !336), !dbg !2792
  call void @llvm.dbg.declare(metadata i32* %7, metadata !2793, metadata !336), !dbg !2794
  call void @llvm.dbg.declare(metadata i32* %8, metadata !2795, metadata !336), !dbg !2796
  %11 = getelementptr inbounds [34 x i8], [34 x i8]* %6, i32 0, i32 0, !dbg !2797
  %12 = load i32, i32* %3, align 4, !dbg !2798
  %13 = call i32 (i8*, i32, i8*, ...) @snprintf(i8* %11, i32 34, i8* getelementptr inbounds ([33 x i8], [33 x i8]* @.str.2.144, i32 0, i32 0), i32 %12) #7, !dbg !2799
  %14 = getelementptr inbounds [34 x i8], [34 x i8]* %6, i32 0, i32 0, !dbg !2800
  %15 = call i32 (i8*, i32, ...) @open(i8* %14, i32 1), !dbg !2801
  store i32 %15, i32* %7, align 4, !dbg !2802
  %16 = load i32, i32* %7, align 4, !dbg !2803
  %17 = icmp ne i32 -1, %16, !dbg !2805
  br i1 %17, label %18, label %37, !dbg !2806

; <label>:18:                                     ; preds = %2
  call void @llvm.dbg.declare(metadata i8** %9, metadata !2807, metadata !336), !dbg !2809
  %19 = load i32, i32* %4, align 4, !dbg !2810
  %20 = icmp ne i32 0, %19, !dbg !2811
  %21 = zext i1 %20 to i32, !dbg !2811
  %22 = getelementptr inbounds [2 x i8*], [2 x i8*]* %5, i32 0, i32 %21, !dbg !2812
  %23 = load i8*, i8** %22, align 4, !dbg !2812
  store i8* %23, i8** %9, align 4, !dbg !2813
  %24 = load i32, i32* %7, align 4, !dbg !2814
  %25 = load i8*, i8** %9, align 4, !dbg !2816
  %26 = load i8*, i8** %9, align 4, !dbg !2817
  %27 = call i32 @strlen(i8* %26) #9, !dbg !2818
  %28 = call i32 @write(i32 %24, i8* %25, i32 %27), !dbg !2819
  %29 = icmp ne i32 -1, %28, !dbg !2821
  br i1 %29, label %30, label %31, !dbg !2822

; <label>:30:                                     ; preds = %18
  store i32 0, i32* %8, align 4, !dbg !2823
  br label %34, !dbg !2824

; <label>:31:                                     ; preds = %18
  %32 = call i32* @__errno_location() #1, !dbg !2825
  %33 = load i32, i32* %32, align 4, !dbg !2825
  store i32 %33, i32* %8, align 4, !dbg !2826
  br label %34

; <label>:34:                                     ; preds = %31, %30
  %35 = load i32, i32* %7, align 4, !dbg !2827
  %36 = call i32 @close(i32 %35), !dbg !2828
  br label %40, !dbg !2829

; <label>:37:                                     ; preds = %2
  %38 = call i32* @__errno_location() #1, !dbg !2830
  %39 = load i32, i32* %38, align 4, !dbg !2830
  store i32 %39, i32* %8, align 4, !dbg !2831
  br label %40

; <label>:40:                                     ; preds = %37, %34
  %41 = load i32, i32* %8, align 4, !dbg !2832
  ret i32 %41, !dbg !2833
}

; Function Attrs: nounwind
define i32 @GPIO_read(i32, i32*) #0 section ".CODE_REGION_1_" !dbg !2834 {
  %3 = alloca i32, align 4
  %4 = alloca i32*, align 4
  %5 = alloca [30 x i8], align 1
  %6 = alloca [4 x i8], align 1
  %7 = alloca i32, align 4
  %8 = alloca i32, align 4
  store i32 %0, i32* %3, align 4
  call void @llvm.dbg.declare(metadata i32* %3, metadata !2837, metadata !336), !dbg !2838
  store i32* %1, i32** %4, align 4
  call void @llvm.dbg.declare(metadata i32** %4, metadata !2839, metadata !336), !dbg !2840
  call void @llvm.dbg.declare(metadata [30 x i8]* %5, metadata !2841, metadata !336), !dbg !2845
  call void @llvm.dbg.declare(metadata [4 x i8]* %6, metadata !2846, metadata !336), !dbg !2847
  call void @llvm.dbg.declare(metadata i32* %7, metadata !2848, metadata !336), !dbg !2849
  call void @llvm.dbg.declare(metadata i32* %8, metadata !2850, metadata !336), !dbg !2851
  %9 = load i32*, i32** %4, align 4, !dbg !2852
  %10 = icmp ne i32* %9, null, !dbg !2854
  br i1 %10, label %11, label %39, !dbg !2855

; <label>:11:                                     ; preds = %2
  %12 = getelementptr inbounds [30 x i8], [30 x i8]* %5, i32 0, i32 0, !dbg !2856
  %13 = load i32, i32* %3, align 4, !dbg !2858
  %14 = call i32 (i8*, i32, i8*, ...) @snprintf(i8* %12, i32 30, i8* getelementptr inbounds ([29 x i8], [29 x i8]* @.str.6.150, i32 0, i32 0), i32 %13) #7, !dbg !2859
  %15 = getelementptr inbounds [30 x i8], [30 x i8]* %5, i32 0, i32 0, !dbg !2860
  %16 = call i32 (i8*, i32, ...) @open(i8* %15, i32 0), !dbg !2861
  store i32 %16, i32* %7, align 4, !dbg !2862
  %17 = load i32, i32* %7, align 4, !dbg !2863
  %18 = icmp ne i32 -1, %17, !dbg !2865
  br i1 %18, label %19, label %35, !dbg !2866

; <label>:19:                                     ; preds = %11
  %20 = load i32, i32* %7, align 4, !dbg !2867
  %21 = getelementptr inbounds [4 x i8], [4 x i8]* %6, i32 0, i32 0, !dbg !2870
  %22 = call i32 @read(i32 %20, i8* %21, i32 3), !dbg !2871
  %23 = icmp ne i32 -1, %22, !dbg !2872
  br i1 %23, label %24, label %29, !dbg !2873

; <label>:24:                                     ; preds = %19
  %25 = getelementptr inbounds [4 x i8], [4 x i8]* %6, i32 0, i32 3, !dbg !2874
  store i8 0, i8* %25, align 1, !dbg !2876
  %26 = getelementptr inbounds [4 x i8], [4 x i8]* %6, i32 0, i32 0, !dbg !2877
  %27 = call i32 @atoi(i8* %26) #9, !dbg !2878
  %28 = load i32*, i32** %4, align 4, !dbg !2879
  store i32 %27, i32* %28, align 4, !dbg !2880
  store i32 0, i32* %8, align 4, !dbg !2881
  br label %32, !dbg !2882

; <label>:29:                                     ; preds = %19
  %30 = call i32* @__errno_location() #1, !dbg !2883
  %31 = load i32, i32* %30, align 4, !dbg !2883
  store i32 %31, i32* %8, align 4, !dbg !2884
  br label %32

; <label>:32:                                     ; preds = %29, %24
  %33 = load i32, i32* %7, align 4, !dbg !2885
  %34 = call i32 @close(i32 %33), !dbg !2886
  br label %38, !dbg !2887

; <label>:35:                                     ; preds = %11
  %36 = call i32* @__errno_location() #1, !dbg !2888
  %37 = load i32, i32* %36, align 4, !dbg !2888
  store i32 %37, i32* %8, align 4, !dbg !2889
  br label %38

; <label>:38:                                     ; preds = %35, %32
  br label %40, !dbg !2890

; <label>:39:                                     ; preds = %2
  store i32 22, i32* %8, align 4, !dbg !2891
  br label %40

; <label>:40:                                     ; preds = %39, %38
  %41 = load i32, i32* %8, align 4, !dbg !2892
  ret i32 %41, !dbg !2893
}

declare i32 @read(i32, i8*, i32) #5 section ".CODE_REGION_1_"

; Function Attrs: nounwind
define i32 @GPIO_write(i32, i32) #0 section ".CODE_REGION_1_" !dbg !2894 {
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca [2 x i8*], align 4
  %6 = alloca [30 x i8], align 1
  %7 = alloca i32, align 4
  %8 = alloca i32, align 4
  %9 = alloca i8*, align 4
  store i32 %0, i32* %3, align 4
  call void @llvm.dbg.declare(metadata i32* %3, metadata !2895, metadata !336), !dbg !2896
  store i32 %1, i32* %4, align 4
  call void @llvm.dbg.declare(metadata i32* %4, metadata !2897, metadata !336), !dbg !2898
  call void @llvm.dbg.declare(metadata [2 x i8*]* %5, metadata !2899, metadata !336), !dbg !2900
  %10 = bitcast [2 x i8*]* %5 to i8*, !dbg !2900
  call void @llvm.memcpy.p0i8.p0i8.i32(i8* %10, i8* bitcast ([2 x i8*]* @GPIO_write.s_values_str to i8*), i32 8, i32 4, i1 false), !dbg !2900
  call void @llvm.dbg.declare(metadata [30 x i8]* %6, metadata !2901, metadata !336), !dbg !2902
  call void @llvm.dbg.declare(metadata i32* %7, metadata !2903, metadata !336), !dbg !2904
  call void @llvm.dbg.declare(metadata i32* %8, metadata !2905, metadata !336), !dbg !2906
  %11 = getelementptr inbounds [30 x i8], [30 x i8]* %6, i32 0, i32 0, !dbg !2907
  %12 = load i32, i32* %3, align 4, !dbg !2908
  %13 = call i32 (i8*, i32, i8*, ...) @snprintf(i8* %11, i32 30, i8* getelementptr inbounds ([29 x i8], [29 x i8]* @.str.6.150, i32 0, i32 0), i32 %12) #7, !dbg !2909
  %14 = getelementptr inbounds [30 x i8], [30 x i8]* %6, i32 0, i32 0, !dbg !2910
  %15 = call i32 (i8*, i32, ...) @open(i8* %14, i32 1), !dbg !2911
  store i32 %15, i32* %7, align 4, !dbg !2912
  %16 = load i32, i32* %7, align 4, !dbg !2913
  %17 = icmp ne i32 -1, %16, !dbg !2915
  br i1 %17, label %18, label %37, !dbg !2916

; <label>:18:                                     ; preds = %2
  call void @llvm.dbg.declare(metadata i8** %9, metadata !2917, metadata !336), !dbg !2919
  %19 = load i32, i32* %4, align 4, !dbg !2920
  %20 = icmp ne i32 0, %19, !dbg !2921
  %21 = zext i1 %20 to i32, !dbg !2921
  %22 = getelementptr inbounds [2 x i8*], [2 x i8*]* %5, i32 0, i32 %21, !dbg !2922
  %23 = load i8*, i8** %22, align 4, !dbg !2922
  store i8* %23, i8** %9, align 4, !dbg !2923
  %24 = load i32, i32* %7, align 4, !dbg !2924
  %25 = load i8*, i8** %9, align 4, !dbg !2926
  %26 = load i8*, i8** %9, align 4, !dbg !2927
  %27 = call i32 @strlen(i8* %26) #9, !dbg !2928
  %28 = call i32 @write(i32 %24, i8* %25, i32 %27), !dbg !2929
  %29 = icmp ne i32 -1, %28, !dbg !2931
  br i1 %29, label %30, label %31, !dbg !2932

; <label>:30:                                     ; preds = %18
  store i32 0, i32* %8, align 4, !dbg !2933
  br label %34, !dbg !2934

; <label>:31:                                     ; preds = %18
  %32 = call i32* @__errno_location() #1, !dbg !2935
  %33 = load i32, i32* %32, align 4, !dbg !2935
  store i32 %33, i32* %8, align 4, !dbg !2936
  br label %34

; <label>:34:                                     ; preds = %31, %30
  %35 = load i32, i32* %7, align 4, !dbg !2937
  %36 = call i32 @close(i32 %35), !dbg !2938
  br label %40, !dbg !2939

; <label>:37:                                     ; preds = %2
  %38 = call i32* @__errno_location() #1, !dbg !2940
  %39 = load i32, i32* %38, align 4, !dbg !2940
  store i32 %39, i32* %8, align 4, !dbg !2941
  br label %40

; <label>:40:                                     ; preds = %37, %34
  %41 = load i32, i32* %8, align 4, !dbg !2942
  ret i32 %41, !dbg !2943
}

; Function Attrs: nounwind
define i32 @export_gpios() #0 section ".CODE_REGION_1_" !dbg !2944 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  call void @llvm.dbg.declare(metadata i32* %1, metadata !2945, metadata !336), !dbg !2946
  call void @llvm.dbg.declare(metadata i32* %2, metadata !2947, metadata !336), !dbg !2948
  %3 = call i32 @GPIO_export(i32 488), !dbg !2949
  store i32 %3, i32* %2, align 4, !dbg !2950
  %4 = load i32, i32* %2, align 4, !dbg !2951
  %5 = icmp eq i32 0, %4, !dbg !2953
  br i1 %5, label %6, label %65, !dbg !2954

; <label>:6:                                      ; preds = %0
  %7 = call i32 @GPIO_export(i32 489), !dbg !2955
  store i32 %7, i32* %2, align 4, !dbg !2957
  %8 = load i32, i32* %2, align 4, !dbg !2958
  %9 = icmp eq i32 0, %8, !dbg !2960
  br i1 %9, label %10, label %56, !dbg !2961

; <label>:10:                                     ; preds = %6
  %11 = call i32 @GPIO_export(i32 490), !dbg !2962
  store i32 %11, i32* %2, align 4, !dbg !2964
  %12 = load i32, i32* %2, align 4, !dbg !2965
  %13 = icmp eq i32 0, %12, !dbg !2967
  br i1 %13, label %14, label %46, !dbg !2968

; <label>:14:                                     ; preds = %10
  %15 = call i32 @GPIO_export(i32 491), !dbg !2969
  store i32 %15, i32* %2, align 4, !dbg !2971
  %16 = load i32, i32* %2, align 4, !dbg !2972
  %17 = icmp eq i32 0, %16, !dbg !2974
  br i1 %17, label %18, label %35, !dbg !2975

; <label>:18:                                     ; preds = %14
  %19 = call i32 @GPIO_export(i32 492), !dbg !2976
  store i32 %19, i32* %2, align 4, !dbg !2978
  %20 = load i32, i32* %2, align 4, !dbg !2979
  %21 = icmp eq i32 0, %20, !dbg !2981
  br i1 %21, label %22, label %23, !dbg !2982

; <label>:22:                                     ; preds = %18
  store i32 0, i32* %1, align 4, !dbg !2983
  br label %34, !dbg !2985

; <label>:23:                                     ; preds = %18
  %24 = load i32, i32* %2, align 4, !dbg !2986
  store i32 %24, i32* %1, align 4, !dbg !2988
  %25 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !2989
  %26 = load i32, i32* %2, align 4, !dbg !2989
  %27 = load i32, i32* %2, align 4, !dbg !2989
  %28 = call i8* @strerror(i32 %27) #7, !dbg !2989
  %29 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %25, i8* getelementptr inbounds ([54 x i8], [54 x i8]* @.str.9.155, i32 0, i32 0), i32 492, i32 %26, i8* %28), !dbg !2990
  %30 = call i32 @GPIO_unexport(i32 488), !dbg !2992
  %31 = call i32 @GPIO_unexport(i32 489), !dbg !2993
  %32 = call i32 @GPIO_unexport(i32 490), !dbg !2994
  %33 = call i32 @GPIO_unexport(i32 491), !dbg !2995
  br label %34

; <label>:34:                                     ; preds = %23, %22
  br label %45, !dbg !2996

; <label>:35:                                     ; preds = %14
  %36 = load i32, i32* %2, align 4, !dbg !2997
  store i32 %36, i32* %1, align 4, !dbg !2999
  %37 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !3000
  %38 = load i32, i32* %2, align 4, !dbg !3000
  %39 = load i32, i32* %2, align 4, !dbg !3000
  %40 = call i8* @strerror(i32 %39) #7, !dbg !3000
  %41 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %37, i8* getelementptr inbounds ([54 x i8], [54 x i8]* @.str.10.156, i32 0, i32 0), i32 491, i32 %38, i8* %40), !dbg !3001
  %42 = call i32 @GPIO_unexport(i32 488), !dbg !3003
  %43 = call i32 @GPIO_unexport(i32 489), !dbg !3004
  %44 = call i32 @GPIO_unexport(i32 490), !dbg !3005
  br label %45

; <label>:45:                                     ; preds = %35, %34
  br label %55, !dbg !3006

; <label>:46:                                     ; preds = %10
  %47 = load i32, i32* %2, align 4, !dbg !3007
  store i32 %47, i32* %1, align 4, !dbg !3009
  %48 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !3010
  %49 = load i32, i32* %2, align 4, !dbg !3010
  %50 = load i32, i32* %2, align 4, !dbg !3010
  %51 = call i8* @strerror(i32 %50) #7, !dbg !3010
  %52 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %48, i8* getelementptr inbounds ([54 x i8], [54 x i8]* @.str.11.157, i32 0, i32 0), i32 490, i32 %49, i8* %51), !dbg !3011
  %53 = call i32 @GPIO_unexport(i32 488), !dbg !3013
  %54 = call i32 @GPIO_unexport(i32 489), !dbg !3014
  br label %55

; <label>:55:                                     ; preds = %46, %45
  br label %64, !dbg !3015

; <label>:56:                                     ; preds = %6
  %57 = load i32, i32* %2, align 4, !dbg !3016
  store i32 %57, i32* %1, align 4, !dbg !3018
  %58 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !3019
  %59 = load i32, i32* %2, align 4, !dbg !3019
  %60 = load i32, i32* %2, align 4, !dbg !3019
  %61 = call i8* @strerror(i32 %60) #7, !dbg !3019
  %62 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %58, i8* getelementptr inbounds ([54 x i8], [54 x i8]* @.str.12.158, i32 0, i32 0), i32 489, i32 %59, i8* %61), !dbg !3020
  %63 = call i32 @GPIO_unexport(i32 488), !dbg !3022
  br label %64

; <label>:64:                                     ; preds = %56, %55
  br label %72, !dbg !3023

; <label>:65:                                     ; preds = %0
  %66 = load i32, i32* %2, align 4, !dbg !3024
  store i32 %66, i32* %1, align 4, !dbg !3026
  %67 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !3027
  %68 = load i32, i32* %2, align 4, !dbg !3027
  %69 = load i32, i32* %2, align 4, !dbg !3027
  %70 = call i8* @strerror(i32 %69) #7, !dbg !3027
  %71 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %67, i8* getelementptr inbounds ([49 x i8], [49 x i8]* @.str.13.159, i32 0, i32 0), i32 488, i32 %68, i8* %70), !dbg !3028
  br label %72

; <label>:72:                                     ; preds = %65, %64
  %73 = load i32, i32* %1, align 4, !dbg !3030
  ret i32 %73, !dbg !3031
}

; Function Attrs: nounwind
define i32 @configure_gpios() #0 section ".CODE_REGION_1_" !dbg !3032 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  call void @llvm.dbg.declare(metadata i32* %1, metadata !3033, metadata !336), !dbg !3034
  call void @llvm.dbg.declare(metadata i32* %2, metadata !3035, metadata !336), !dbg !3036
  store i32 488, i32* %2, align 4, !dbg !3037
  %3 = load i32, i32* %2, align 4, !dbg !3038
  %4 = call i32 @GPIO_direction(i32 %3, i32 0), !dbg !3039
  store i32 %4, i32* %1, align 4, !dbg !3040
  %5 = load i32, i32* %1, align 4, !dbg !3041
  %6 = icmp eq i32 0, %5, !dbg !3043
  br i1 %6, label %7, label %40, !dbg !3044

; <label>:7:                                      ; preds = %0
  store i32 489, i32* %2, align 4, !dbg !3045
  %8 = load i32, i32* %2, align 4, !dbg !3047
  %9 = call i32 @GPIO_direction(i32 %8, i32 1), !dbg !3048
  store i32 %9, i32* %1, align 4, !dbg !3049
  %10 = load i32, i32* %1, align 4, !dbg !3050
  %11 = icmp eq i32 0, %10, !dbg !3052
  br i1 %11, label %12, label %39, !dbg !3053

; <label>:12:                                     ; preds = %7
  %13 = load i32, i32* %2, align 4, !dbg !3054
  %14 = call i32 @GPIO_write(i32 %13, i32 1), !dbg !3056
  store i32 490, i32* %2, align 4, !dbg !3057
  %15 = load i32, i32* %2, align 4, !dbg !3058
  %16 = call i32 @GPIO_direction(i32 %15, i32 1), !dbg !3059
  store i32 %16, i32* %1, align 4, !dbg !3060
  %17 = load i32, i32* %1, align 4, !dbg !3061
  %18 = icmp eq i32 0, %17, !dbg !3063
  br i1 %18, label %19, label %38, !dbg !3064

; <label>:19:                                     ; preds = %12
  %20 = load i32, i32* %2, align 4, !dbg !3065
  %21 = call i32 @GPIO_write(i32 %20, i32 1), !dbg !3067
  store i32 491, i32* %2, align 4, !dbg !3068
  %22 = load i32, i32* %2, align 4, !dbg !3069
  %23 = call i32 @GPIO_direction(i32 %22, i32 1), !dbg !3070
  store i32 %23, i32* %1, align 4, !dbg !3071
  %24 = load i32, i32* %1, align 4, !dbg !3072
  %25 = icmp eq i32 0, %24, !dbg !3074
  br i1 %25, label %26, label %37, !dbg !3075

; <label>:26:                                     ; preds = %19
  %27 = load i32, i32* %2, align 4, !dbg !3076
  %28 = call i32 @GPIO_write(i32 %27, i32 1), !dbg !3078
  store i32 492, i32* %2, align 4, !dbg !3079
  %29 = load i32, i32* %2, align 4, !dbg !3080
  %30 = call i32 @GPIO_direction(i32 %29, i32 1), !dbg !3081
  store i32 %30, i32* %1, align 4, !dbg !3082
  %31 = load i32, i32* %1, align 4, !dbg !3083
  %32 = icmp eq i32 0, %31, !dbg !3085
  br i1 %32, label %33, label %36, !dbg !3086

; <label>:33:                                     ; preds = %26
  %34 = load i32, i32* %2, align 4, !dbg !3087
  %35 = call i32 @GPIO_write(i32 %34, i32 1), !dbg !3088
  br label %36, !dbg !3088

; <label>:36:                                     ; preds = %33, %26
  br label %37, !dbg !3089

; <label>:37:                                     ; preds = %36, %19
  br label %38, !dbg !3090

; <label>:38:                                     ; preds = %37, %12
  br label %39, !dbg !3091

; <label>:39:                                     ; preds = %38, %7
  br label %40, !dbg !3092

; <label>:40:                                     ; preds = %39, %0
  %41 = load i32, i32* %1, align 4, !dbg !3093
  %42 = icmp ne i32 %41, 0, !dbg !3095
  br i1 %42, label %43, label %50, !dbg !3096

; <label>:43:                                     ; preds = %40
  %44 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !3097
  %45 = load i32, i32* %2, align 4, !dbg !3097
  %46 = load i32, i32* %1, align 4, !dbg !3097
  %47 = load i32, i32* %1, align 4, !dbg !3097
  %48 = call i8* @strerror(i32 %47) #7, !dbg !3097
  %49 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %44, i8* getelementptr inbounds ([53 x i8], [53 x i8]* @.str.14.162, i32 0, i32 0), i32 %45, i32 %46, i8* %48), !dbg !3098
  br label %50, !dbg !3097

; <label>:50:                                     ; preds = %43, %40
  %51 = load i32, i32* %1, align 4, !dbg !3100
  ret i32 %51, !dbg !3101
}

; Function Attrs: nounwind
define i32 @unexport_gpios() #0 section ".CODE_REGION_2_" !dbg !3102 {
  %1 = alloca i32, align 4
  call void @llvm.dbg.declare(metadata i32* %1, metadata !3103, metadata !336), !dbg !3104
  store i32 0, i32* %1, align 4, !dbg !3105
  call void @__AMI_fake_direct_transfer(), !dbg !3106
  %2 = call i32 @GPIO_unexport(i32 488), !dbg !3106
  %3 = load i32, i32* %1, align 4, !dbg !3107
  %4 = or i32 %3, %2, !dbg !3107
  store i32 %4, i32* %1, align 4, !dbg !3107
  call void @__AMI_fake_direct_transfer(), !dbg !3108
  %5 = call i32 @GPIO_unexport(i32 489), !dbg !3108
  %6 = load i32, i32* %1, align 4, !dbg !3109
  %7 = or i32 %6, %5, !dbg !3109
  store i32 %7, i32* %1, align 4, !dbg !3109
  call void @__AMI_fake_direct_transfer(), !dbg !3110
  %8 = call i32 @GPIO_unexport(i32 490), !dbg !3110
  %9 = load i32, i32* %1, align 4, !dbg !3111
  %10 = or i32 %9, %8, !dbg !3111
  store i32 %10, i32* %1, align 4, !dbg !3111
  call void @__AMI_fake_direct_transfer(), !dbg !3112
  %11 = call i32 @GPIO_unexport(i32 491), !dbg !3112
  %12 = load i32, i32* %1, align 4, !dbg !3113
  %13 = or i32 %12, %11, !dbg !3113
  store i32 %13, i32* %1, align 4, !dbg !3113
  call void @__AMI_fake_direct_transfer(), !dbg !3114
  %14 = call i32 @GPIO_unexport(i32 492), !dbg !3114
  %15 = load i32, i32* %1, align 4, !dbg !3115
  %16 = or i32 %15, %14, !dbg !3115
  store i32 %16, i32* %1, align 4, !dbg !3115
  %17 = load i32, i32* %1, align 4, !dbg !3116
  %18 = icmp ne i32 %17, 0, !dbg !3118
  br i1 %18, label %19, label %25, !dbg !3119

; <label>:19:                                     ; preds = %0
  %20 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !3120
  %21 = load i32, i32* %1, align 4, !dbg !3120
  %22 = load i32, i32* %1, align 4, !dbg !3120
  %23 = call i8* @strerror(i32 %22) #7, !dbg !3120
  call void @__AMI_fake_direct_transfer(), !dbg !3121
  %24 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %20, i8* getelementptr inbounds ([42 x i8], [42 x i8]* @.str.15.165, i32 0, i32 0), i32 %21, i8* %23), !dbg !3121
  br label %25, !dbg !3120

; <label>:25:                                     ; preds = %19, %0
  %26 = load i32, i32* %1, align 4, !dbg !3123
  ret i32 %26, !dbg !3124
}

declare void @__AMI_fake_local_wrt()

declare void @__AMI_fake_direct_transfer()

declare void @__AMI_fake_rt_transfer()

attributes #0 = { nounwind "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="arm1176jzf-s" "target-features"="+dsp,+strict-align,+vfp2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind readnone }
attributes #2 = { nounwind "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="arm1176jzf-s" "target-features"="+dsp,+strict-align,+vfp2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { argmemonly nounwind }
attributes #4 = { nounwind readnone "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="arm1176jzf-s" "target-features"="+dsp,+strict-align,+vfp2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #5 = { "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="arm1176jzf-s" "target-features"="+dsp,+strict-align,+vfp2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #6 = { nounwind readonly "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="arm1176jzf-s" "target-features"="+dsp,+strict-align,+vfp2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #7 = { nounwind }
attributes #8 = { noreturn nounwind "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="arm1176jzf-s" "target-features"="+dsp,+strict-align,+vfp2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #9 = { nounwind readonly }
attributes #10 = { noreturn nounwind }

!llvm.dbg.cu = !{!0, !3, !29, !47, !96, !235, !255, !319}
!llvm.ident = !{!322, !322, !322, !322, !322, !322, !322, !322}
!llvm.module.flags = !{!323, !324, !325, !326}

!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "clang version 3.9.0 (tags/RELEASE_390/final)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, enums: !2)
!1 = !DIFile(filename: "util.c", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/alarm4pi-cb")
!2 = !{}
!3 = distinct !DICompileUnit(language: DW_LANG_C99, file: !4, producer: "clang version 3.9.0 (tags/RELEASE_390/final)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, enums: !2, globals: !5)
!4 = !DIFile(filename: "alarm4pi.c", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/alarm4pi-cb")
!5 = !{!6, !15, !22, !23, !25}
!6 = distinct !DIGlobalVariable(name: "Child_process_id", scope: !3, file: !4, line: 44, type: !7, isLocal: false, isDefinition: true, variable: [2 x i32]* @Child_process_id)
!7 = !DICompositeType(tag: DW_TAG_array_type, baseType: !8, size: 64, align: 32, elements: !13)
!8 = !DIDerivedType(tag: DW_TAG_typedef, name: "pid_t", file: !9, line: 98, baseType: !10)
!9 = !DIFile(filename: "/home/zrz0517/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/libc/usr/include/sys/types.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/alarm4pi-cb")
!10 = !DIDerivedType(tag: DW_TAG_typedef, name: "__pid_t", file: !11, line: 133, baseType: !12)
!11 = !DIFile(filename: "/home/zrz0517/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/libc/usr/include/bits/types.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/alarm4pi-cb")
!12 = !DIBasicType(name: "int", size: 32, align: 32, encoding: DW_ATE_signed)
!13 = !{!14}
!14 = !DISubrange(count: 2)
!15 = distinct !DIGlobalVariable(name: "Capture_exec_args", scope: !3, file: !4, line: 45, type: !16, isLocal: false, isDefinition: true, variable: [7 x i8*]* @Capture_exec_args)
!16 = !DICompositeType(tag: DW_TAG_array_type, baseType: !17, size: 224, align: 32, elements: !20)
!17 = !DIDerivedType(tag: DW_TAG_const_type, baseType: !18)
!18 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !19, size: 32, align: 32)
!19 = !DIBasicType(name: "char", size: 8, align: 8, encoding: DW_ATE_unsigned_char)
!20 = !{!21}
!21 = !DISubrange(count: 7)
!22 = distinct !DIGlobalVariable(name: "Web_server_exec_args", scope: !3, file: !4, line: 46, type: !16, isLocal: false, isDefinition: true, variable: [7 x i8*]* @Web_server_exec_args)
!23 = distinct !DIGlobalVariable(name: "Exit_daemon_loop", scope: !3, file: !4, line: 52, type: !24, isLocal: false, isDefinition: true, variable: i32* @Exit_daemon_loop)
!24 = !DIDerivedType(tag: DW_TAG_volatile_type, baseType: !12)
!25 = distinct !DIGlobalVariable(name: "count", scope: !26, file: !4, line: 71, type: !12, isLocal: true, isDefinition: true, variable: i32* @timer_handler.count)
!26 = distinct !DISubprogram(name: "timer_handler", scope: !4, file: !4, line: 69, type: !27, isLocal: true, isDefinition: true, scopeLine: 70, flags: DIFlagPrototyped, isOptimized: false, unit: !3, variables: !2)
!27 = !DISubroutineType(types: !28)
!28 = !{null, !12}
!29 = distinct !DICompileUnit(language: DW_LANG_C99, file: !30, producer: "clang version 3.9.0 (tags/RELEASE_390/final)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, enums: !2, retainedTypes: !31, globals: !36)
!30 = !DIFile(filename: "gpio_polling.c", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/alarm4pi-cb")
!31 = !{!32, !33}
!32 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: null, size: 32, align: 32)
!33 = !DIDerivedType(tag: DW_TAG_typedef, name: "intptr_t", file: !34, line: 270, baseType: !35)
!34 = !DIFile(filename: "/home/zrz0517/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/libc/usr/include/unistd.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/alarm4pi-cb")
!35 = !DIDerivedType(tag: DW_TAG_typedef, name: "__intptr_t", file: !11, line: 186, baseType: !12)
!36 = !{!37, !38, !39, !43}
!37 = distinct !DIGlobalVariable(name: "recording_flag", scope: !29, file: !30, line: 150, type: !12, isLocal: false, isDefinition: true, variable: i32* @recording_flag)
!38 = distinct !DIGlobalVariable(name: "recording_cnt", scope: !29, file: !30, line: 151, type: !12, isLocal: false, isDefinition: true, variable: i32* @recording_cnt)
!39 = distinct !DIGlobalVariable(name: "Polling_thread_id", scope: !29, file: !30, line: 22, type: !40, isLocal: false, isDefinition: true, variable: i32* @Polling_thread_id)
!40 = !DIDerivedType(tag: DW_TAG_typedef, name: "pthread_t", file: !41, line: 37, baseType: !42)
!41 = !DIFile(filename: "/home/zrz0517/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/libc/usr/include/bits/pthreadtypes.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/alarm4pi-cb")
!42 = !DIBasicType(name: "long unsigned int", size: 32, align: 32, encoding: DW_ATE_unsigned)
!43 = distinct !DIGlobalVariable(name: "Msg_info_str", scope: !29, file: !30, line: 24, type: !44, isLocal: false, isDefinition: true, variable: [146 x i8]* @Msg_info_str)
!44 = !DICompositeType(tag: DW_TAG_array_type, baseType: !19, size: 1168, align: 8, elements: !45)
!45 = !{!46}
!46 = !DISubrange(count: 146)
!47 = distinct !DICompileUnit(language: DW_LANG_C99, file: !48, producer: "clang version 3.9.0 (tags/RELEASE_390/final)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, enums: !49, retainedTypes: !62, globals: !75)
!48 = !DIFile(filename: "pushover.c", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/alarm4pi-cb")
!49 = !{!50}
!50 = !DICompositeType(tag: DW_TAG_enumeration_type, name: "__socket_type", file: !51, line: 24, size: 32, align: 32, elements: !52)
!51 = !DIFile(filename: "/home/zrz0517/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/libc/usr/include/bits/socket_type.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/alarm4pi-cb")
!52 = !{!53, !54, !55, !56, !57, !58, !59, !60, !61}
!53 = !DIEnumerator(name: "SOCK_STREAM", value: 1)
!54 = !DIEnumerator(name: "SOCK_DGRAM", value: 2)
!55 = !DIEnumerator(name: "SOCK_RAW", value: 3)
!56 = !DIEnumerator(name: "SOCK_RDM", value: 4)
!57 = !DIEnumerator(name: "SOCK_SEQPACKET", value: 5)
!58 = !DIEnumerator(name: "SOCK_DCCP", value: 6)
!59 = !DIEnumerator(name: "SOCK_PACKET", value: 10)
!60 = !DIEnumerator(name: "SOCK_CLOEXEC", value: 524288)
!61 = !DIEnumerator(name: "SOCK_NONBLOCK", value: 2048)
!62 = !{!32, !63, !42}
!63 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !64, size: 32, align: 32)
!64 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "sockaddr", file: !65, line: 153, size: 128, align: 16, elements: !66)
!65 = !DIFile(filename: "/home/zrz0517/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/libc/usr/include/bits/socket.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/alarm4pi-cb")
!66 = !{!67, !71}
!67 = !DIDerivedType(tag: DW_TAG_member, name: "sa_family", scope: !64, file: !65, line: 155, baseType: !68, size: 16, align: 16)
!68 = !DIDerivedType(tag: DW_TAG_typedef, name: "sa_family_t", file: !69, line: 28, baseType: !70)
!69 = !DIFile(filename: "/home/zrz0517/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/libc/usr/include/bits/sockaddr.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/alarm4pi-cb")
!70 = !DIBasicType(name: "unsigned short", size: 16, align: 16, encoding: DW_ATE_unsigned)
!71 = !DIDerivedType(tag: DW_TAG_member, name: "sa_data", scope: !64, file: !65, line: 156, baseType: !72, size: 112, align: 8, offset: 16)
!72 = !DICompositeType(tag: DW_TAG_array_type, baseType: !19, size: 112, align: 8, elements: !73)
!73 = !{!74}
!74 = !DISubrange(count: 14)
!75 = !{!76, !80, !81, !85, !86, !95}
!76 = distinct !DIGlobalVariable(name: "Token_id", scope: !47, file: !48, line: 43, type: !77, isLocal: false, isDefinition: true, variable: [81 x i8]* @Token_id)
!77 = !DICompositeType(tag: DW_TAG_array_type, baseType: !19, size: 648, align: 8, elements: !78)
!78 = !{!79}
!79 = !DISubrange(count: 81)
!80 = distinct !DIGlobalVariable(name: "User_id", scope: !47, file: !48, line: 44, type: !77, isLocal: false, isDefinition: true, variable: [81 x i8]* @User_id)
!81 = distinct !DIGlobalVariable(name: "Server_name", scope: !47, file: !48, line: 45, type: !82, isLocal: false, isDefinition: true, variable: [65 x i8]* @Server_name)
!82 = !DICompositeType(tag: DW_TAG_array_type, baseType: !19, size: 520, align: 8, elements: !83)
!83 = !{!84}
!84 = !DISubrange(count: 65)
!85 = distinct !DIGlobalVariable(name: "Server_path", scope: !47, file: !48, line: 46, type: !82, isLocal: false, isDefinition: true, variable: [65 x i8]* @Server_path)
!86 = distinct !DIGlobalVariable(name: "Server_ip", scope: !47, file: !48, line: 47, type: !87, isLocal: false, isDefinition: true, variable: %struct.in_addr* @Server_ip)
!87 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "in_addr", file: !88, line: 31, size: 32, align: 32, elements: !89)
!88 = !DIFile(filename: "/home/zrz0517/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/libc/usr/include/netinet/in.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/alarm4pi-cb")
!89 = !{!90}
!90 = !DIDerivedType(tag: DW_TAG_member, name: "s_addr", scope: !87, file: !88, line: 33, baseType: !91, size: 32, align: 32)
!91 = !DIDerivedType(tag: DW_TAG_typedef, name: "in_addr_t", file: !88, line: 30, baseType: !92)
!92 = !DIDerivedType(tag: DW_TAG_typedef, name: "uint32_t", file: !93, line: 51, baseType: !94)
!93 = !DIFile(filename: "/home/zrz0517/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/libc/usr/include/stdint.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/alarm4pi-cb")
!94 = !DIBasicType(name: "unsigned int", size: 32, align: 32, encoding: DW_ATE_unsigned)
!95 = distinct !DIGlobalVariable(name: "Server_port", scope: !47, file: !48, line: 48, type: !12, isLocal: false, isDefinition: true, variable: i32* @Server_port)
!96 = distinct !DICompileUnit(language: DW_LANG_C99, file: !97, producer: "clang version 3.9.0 (tags/RELEASE_390/final)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, enums: !98, retainedTypes: !213)
!97 = !DIFile(filename: "public_ip.c", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/alarm4pi-cb")
!98 = !{!99, !118, !126, !136, !190, !200}
!99 = !DICompositeType(tag: DW_TAG_enumeration_type, name: "__ns_rcode", file: !100, line: 190, size: 32, align: 32, elements: !101)
!100 = !DIFile(filename: "/home/zrz0517/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/libc/usr/include/arpa/nameser.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/alarm4pi-cb")
!101 = !{!102, !103, !104, !105, !106, !107, !108, !109, !110, !111, !112, !113, !114, !115, !116, !117}
!102 = !DIEnumerator(name: "ns_r_noerror", value: 0)
!103 = !DIEnumerator(name: "ns_r_formerr", value: 1)
!104 = !DIEnumerator(name: "ns_r_servfail", value: 2)
!105 = !DIEnumerator(name: "ns_r_nxdomain", value: 3)
!106 = !DIEnumerator(name: "ns_r_notimpl", value: 4)
!107 = !DIEnumerator(name: "ns_r_refused", value: 5)
!108 = !DIEnumerator(name: "ns_r_yxdomain", value: 6)
!109 = !DIEnumerator(name: "ns_r_yxrrset", value: 7)
!110 = !DIEnumerator(name: "ns_r_nxrrset", value: 8)
!111 = !DIEnumerator(name: "ns_r_notauth", value: 9)
!112 = !DIEnumerator(name: "ns_r_notzone", value: 10)
!113 = !DIEnumerator(name: "ns_r_max", value: 11)
!114 = !DIEnumerator(name: "ns_r_badvers", value: 16)
!115 = !DIEnumerator(name: "ns_r_badsig", value: 16)
!116 = !DIEnumerator(name: "ns_r_badkey", value: 17)
!117 = !DIEnumerator(name: "ns_r_badtime", value: 18)
!118 = !DICompositeType(tag: DW_TAG_enumeration_type, file: !119, line: 71, size: 32, align: 32, elements: !120)
!119 = !DIFile(filename: "/home/zrz0517/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/libc/usr/include/resolv.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/alarm4pi-cb")
!120 = !{!121, !122, !123, !124, !125}
!121 = !DIEnumerator(name: "res_goahead", value: 0)
!122 = !DIEnumerator(name: "res_nextns", value: 1)
!123 = !DIEnumerator(name: "res_modified", value: 2)
!124 = !DIEnumerator(name: "res_done", value: 3)
!125 = !DIEnumerator(name: "res_error", value: 4)
!126 = !DICompositeType(tag: DW_TAG_enumeration_type, name: "__ns_class", file: !100, line: 321, size: 32, align: 32, elements: !127)
!127 = !{!128, !129, !130, !131, !132, !133, !134, !135}
!128 = !DIEnumerator(name: "ns_c_invalid", value: 0)
!129 = !DIEnumerator(name: "ns_c_in", value: 1)
!130 = !DIEnumerator(name: "ns_c_2", value: 2)
!131 = !DIEnumerator(name: "ns_c_chaos", value: 3)
!132 = !DIEnumerator(name: "ns_c_hs", value: 4)
!133 = !DIEnumerator(name: "ns_c_none", value: 254)
!134 = !DIEnumerator(name: "ns_c_any", value: 255)
!135 = !DIEnumerator(name: "ns_c_max", value: 65536)
!136 = !DICompositeType(tag: DW_TAG_enumeration_type, name: "__ns_type", file: !100, line: 252, size: 32, align: 32, elements: !137)
!137 = !{!138, !139, !140, !141, !142, !143, !144, !145, !146, !147, !148, !149, !150, !151, !152, !153, !154, !155, !156, !157, !158, !159, !160, !161, !162, !163, !164, !165, !166, !167, !168, !169, !170, !171, !172, !173, !174, !175, !176, !177, !178, !179, !180, !181, !182, !183, !184, !185, !186, !187, !188, !189}
!138 = !DIEnumerator(name: "ns_t_invalid", value: 0)
!139 = !DIEnumerator(name: "ns_t_a", value: 1)
!140 = !DIEnumerator(name: "ns_t_ns", value: 2)
!141 = !DIEnumerator(name: "ns_t_md", value: 3)
!142 = !DIEnumerator(name: "ns_t_mf", value: 4)
!143 = !DIEnumerator(name: "ns_t_cname", value: 5)
!144 = !DIEnumerator(name: "ns_t_soa", value: 6)
!145 = !DIEnumerator(name: "ns_t_mb", value: 7)
!146 = !DIEnumerator(name: "ns_t_mg", value: 8)
!147 = !DIEnumerator(name: "ns_t_mr", value: 9)
!148 = !DIEnumerator(name: "ns_t_null", value: 10)
!149 = !DIEnumerator(name: "ns_t_wks", value: 11)
!150 = !DIEnumerator(name: "ns_t_ptr", value: 12)
!151 = !DIEnumerator(name: "ns_t_hinfo", value: 13)
!152 = !DIEnumerator(name: "ns_t_minfo", value: 14)
!153 = !DIEnumerator(name: "ns_t_mx", value: 15)
!154 = !DIEnumerator(name: "ns_t_txt", value: 16)
!155 = !DIEnumerator(name: "ns_t_rp", value: 17)
!156 = !DIEnumerator(name: "ns_t_afsdb", value: 18)
!157 = !DIEnumerator(name: "ns_t_x25", value: 19)
!158 = !DIEnumerator(name: "ns_t_isdn", value: 20)
!159 = !DIEnumerator(name: "ns_t_rt", value: 21)
!160 = !DIEnumerator(name: "ns_t_nsap", value: 22)
!161 = !DIEnumerator(name: "ns_t_nsap_ptr", value: 23)
!162 = !DIEnumerator(name: "ns_t_sig", value: 24)
!163 = !DIEnumerator(name: "ns_t_key", value: 25)
!164 = !DIEnumerator(name: "ns_t_px", value: 26)
!165 = !DIEnumerator(name: "ns_t_gpos", value: 27)
!166 = !DIEnumerator(name: "ns_t_aaaa", value: 28)
!167 = !DIEnumerator(name: "ns_t_loc", value: 29)
!168 = !DIEnumerator(name: "ns_t_nxt", value: 30)
!169 = !DIEnumerator(name: "ns_t_eid", value: 31)
!170 = !DIEnumerator(name: "ns_t_nimloc", value: 32)
!171 = !DIEnumerator(name: "ns_t_srv", value: 33)
!172 = !DIEnumerator(name: "ns_t_atma", value: 34)
!173 = !DIEnumerator(name: "ns_t_naptr", value: 35)
!174 = !DIEnumerator(name: "ns_t_kx", value: 36)
!175 = !DIEnumerator(name: "ns_t_cert", value: 37)
!176 = !DIEnumerator(name: "ns_t_a6", value: 38)
!177 = !DIEnumerator(name: "ns_t_dname", value: 39)
!178 = !DIEnumerator(name: "ns_t_sink", value: 40)
!179 = !DIEnumerator(name: "ns_t_opt", value: 41)
!180 = !DIEnumerator(name: "ns_t_apl", value: 42)
!181 = !DIEnumerator(name: "ns_t_tkey", value: 249)
!182 = !DIEnumerator(name: "ns_t_tsig", value: 250)
!183 = !DIEnumerator(name: "ns_t_ixfr", value: 251)
!184 = !DIEnumerator(name: "ns_t_axfr", value: 252)
!185 = !DIEnumerator(name: "ns_t_mailb", value: 253)
!186 = !DIEnumerator(name: "ns_t_maila", value: 254)
!187 = !DIEnumerator(name: "ns_t_any", value: 255)
!188 = !DIEnumerator(name: "ns_t_zxfr", value: 256)
!189 = !DIEnumerator(name: "ns_t_max", value: 65536)
!190 = !DICompositeType(tag: DW_TAG_enumeration_type, name: "__ns_sect", file: !100, line: 98, size: 32, align: 32, elements: !191)
!191 = !{!192, !193, !194, !195, !196, !197, !198, !199}
!192 = !DIEnumerator(name: "ns_s_qd", value: 0)
!193 = !DIEnumerator(name: "ns_s_zn", value: 0)
!194 = !DIEnumerator(name: "ns_s_an", value: 1)
!195 = !DIEnumerator(name: "ns_s_pr", value: 1)
!196 = !DIEnumerator(name: "ns_s_ns", value: 2)
!197 = !DIEnumerator(name: "ns_s_ud", value: 2)
!198 = !DIEnumerator(name: "ns_s_ar", value: 3)
!199 = !DIEnumerator(name: "ns_s_max", value: 4)
!200 = !DICompositeType(tag: DW_TAG_enumeration_type, name: "__ns_flag", file: !100, line: 160, size: 32, align: 32, elements: !201)
!201 = !{!202, !203, !204, !205, !206, !207, !208, !209, !210, !211, !212}
!202 = !DIEnumerator(name: "ns_f_qr", value: 0)
!203 = !DIEnumerator(name: "ns_f_opcode", value: 1)
!204 = !DIEnumerator(name: "ns_f_aa", value: 2)
!205 = !DIEnumerator(name: "ns_f_tc", value: 3)
!206 = !DIEnumerator(name: "ns_f_rd", value: 4)
!207 = !DIEnumerator(name: "ns_f_ra", value: 5)
!208 = !DIEnumerator(name: "ns_f_z", value: 6)
!209 = !DIEnumerator(name: "ns_f_ad", value: 7)
!210 = !DIEnumerator(name: "ns_f_cd", value: 8)
!211 = !DIEnumerator(name: "ns_f_rcode", value: 9)
!212 = !DIEnumerator(name: "ns_f_max", value: 10)
!213 = !{!32, !214, !230, !233, !234}
!214 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !215, size: 32, align: 32)
!215 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "sockaddr_in", file: !88, line: 239, size: 128, align: 32, elements: !216)
!216 = !{!217, !218, !221, !225}
!217 = !DIDerivedType(tag: DW_TAG_member, name: "sin_family", scope: !215, file: !88, line: 241, baseType: !68, size: 16, align: 16)
!218 = !DIDerivedType(tag: DW_TAG_member, name: "sin_port", scope: !215, file: !88, line: 242, baseType: !219, size: 16, align: 16, offset: 16)
!219 = !DIDerivedType(tag: DW_TAG_typedef, name: "in_port_t", file: !88, line: 119, baseType: !220)
!220 = !DIDerivedType(tag: DW_TAG_typedef, name: "uint16_t", file: !93, line: 49, baseType: !70)
!221 = !DIDerivedType(tag: DW_TAG_member, name: "sin_addr", scope: !215, file: !88, line: 243, baseType: !222, size: 32, align: 32, offset: 32)
!222 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "in_addr", file: !88, line: 31, size: 32, align: 32, elements: !223)
!223 = !{!224}
!224 = !DIDerivedType(tag: DW_TAG_member, name: "s_addr", scope: !222, file: !88, line: 33, baseType: !91, size: 32, align: 32)
!225 = !DIDerivedType(tag: DW_TAG_member, name: "sin_zero", scope: !215, file: !88, line: 246, baseType: !226, size: 64, align: 8, offset: 64)
!226 = !DICompositeType(tag: DW_TAG_array_type, baseType: !227, size: 64, align: 8, elements: !228)
!227 = !DIBasicType(name: "unsigned char", size: 8, align: 8, encoding: DW_ATE_unsigned_char)
!228 = !{!229}
!229 = !DISubrange(count: 8)
!230 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !231, size: 32, align: 32)
!231 = !DIDerivedType(tag: DW_TAG_typedef, name: "u_char", file: !9, line: 33, baseType: !232)
!232 = !DIDerivedType(tag: DW_TAG_typedef, name: "__u_char", file: !11, line: 30, baseType: !227)
!233 = !DIDerivedType(tag: DW_TAG_typedef, name: "ns_type", file: !100, line: 305, baseType: !136)
!234 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !222, size: 32, align: 32)
!235 = distinct !DICompileUnit(language: DW_LANG_C99, file: !236, producer: "clang version 3.9.0 (tags/RELEASE_390/final)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, enums: !237, retainedTypes: !244)
!236 = !DIFile(filename: "proc_helper.c", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/alarm4pi-cb")
!237 = !{!238}
!238 = !DICompositeType(tag: DW_TAG_enumeration_type, name: "__itimer_which", file: !239, line: 91, size: 32, align: 32, elements: !240)
!239 = !DIFile(filename: "/home/zrz0517/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/libc/usr/include/sys/time.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/alarm4pi-cb")
!240 = !{!241, !242, !243}
!241 = !DIEnumerator(name: "ITIMER_REAL", value: 0)
!242 = !DIEnumerator(name: "ITIMER_VIRTUAL", value: 1)
!243 = !DIEnumerator(name: "ITIMER_PROF", value: 2)
!244 = !{!32, !245, !249, !252}
!245 = !DIDerivedType(tag: DW_TAG_typedef, name: "time_t", file: !246, line: 75, baseType: !247)
!246 = !DIFile(filename: "/home/zrz0517/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/libc/usr/include/time.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/alarm4pi-cb")
!247 = !DIDerivedType(tag: DW_TAG_typedef, name: "__time_t", file: !11, line: 139, baseType: !248)
!248 = !DIBasicType(name: "long int", size: 32, align: 32, encoding: DW_ATE_signed)
!249 = !DIDerivedType(tag: DW_TAG_typedef, name: "suseconds_t", file: !250, line: 48, baseType: !251)
!250 = !DIFile(filename: "/home/zrz0517/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/libc/usr/include/sys/select.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/alarm4pi-cb")
!251 = !DIDerivedType(tag: DW_TAG_typedef, name: "__suseconds_t", file: !11, line: 141, baseType: !248)
!252 = !DIDerivedType(tag: DW_TAG_typedef, name: "__sighandler_t", file: !253, line: 85, baseType: !254)
!253 = !DIFile(filename: "/home/zrz0517/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/libc/usr/include/signal.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/alarm4pi-cb")
!254 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !27, size: 32, align: 32)
!255 = distinct !DICompileUnit(language: DW_LANG_C99, file: !256, producer: "clang version 3.9.0 (tags/RELEASE_390/final)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, enums: !2, retainedTypes: !257, globals: !258)
!256 = !DIFile(filename: "log_msgs.c", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/alarm4pi-cb")
!257 = !{!245, !32, !18}
!258 = !{!259, !260, !318}
!259 = distinct !DIGlobalVariable(name: "Console_messages", scope: !255, file: !256, line: 9, type: !12, isLocal: false, isDefinition: true, variable: i32* @Console_messages)
!260 = distinct !DIGlobalVariable(name: "Log_file_handle", scope: !255, file: !256, line: 11, type: !261, isLocal: false, isDefinition: true, variable: %struct._IO_FILE** @Log_file_handle)
!261 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !262, size: 32, align: 32)
!262 = !DIDerivedType(tag: DW_TAG_typedef, name: "FILE", file: !263, line: 48, baseType: !264)
!263 = !DIFile(filename: "/home/zrz0517/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/libc/usr/include/stdio.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/alarm4pi-cb")
!264 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "_IO_FILE", file: !265, line: 241, size: 1216, align: 64, elements: !266)
!265 = !DIFile(filename: "/home/zrz0517/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/libc/usr/include/libio.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/alarm4pi-cb")
!266 = !{!267, !268, !269, !270, !271, !272, !273, !274, !275, !276, !277, !278, !279, !287, !288, !289, !290, !292, !293, !295, !299, !302, !306, !307, !308, !309, !310, !313, !314}
!267 = !DIDerivedType(tag: DW_TAG_member, name: "_flags", scope: !264, file: !265, line: 242, baseType: !12, size: 32, align: 32)
!268 = !DIDerivedType(tag: DW_TAG_member, name: "_IO_read_ptr", scope: !264, file: !265, line: 247, baseType: !18, size: 32, align: 32, offset: 32)
!269 = !DIDerivedType(tag: DW_TAG_member, name: "_IO_read_end", scope: !264, file: !265, line: 248, baseType: !18, size: 32, align: 32, offset: 64)
!270 = !DIDerivedType(tag: DW_TAG_member, name: "_IO_read_base", scope: !264, file: !265, line: 249, baseType: !18, size: 32, align: 32, offset: 96)
!271 = !DIDerivedType(tag: DW_TAG_member, name: "_IO_write_base", scope: !264, file: !265, line: 250, baseType: !18, size: 32, align: 32, offset: 128)
!272 = !DIDerivedType(tag: DW_TAG_member, name: "_IO_write_ptr", scope: !264, file: !265, line: 251, baseType: !18, size: 32, align: 32, offset: 160)
!273 = !DIDerivedType(tag: DW_TAG_member, name: "_IO_write_end", scope: !264, file: !265, line: 252, baseType: !18, size: 32, align: 32, offset: 192)
!274 = !DIDerivedType(tag: DW_TAG_member, name: "_IO_buf_base", scope: !264, file: !265, line: 253, baseType: !18, size: 32, align: 32, offset: 224)
!275 = !DIDerivedType(tag: DW_TAG_member, name: "_IO_buf_end", scope: !264, file: !265, line: 254, baseType: !18, size: 32, align: 32, offset: 256)
!276 = !DIDerivedType(tag: DW_TAG_member, name: "_IO_save_base", scope: !264, file: !265, line: 256, baseType: !18, size: 32, align: 32, offset: 288)
!277 = !DIDerivedType(tag: DW_TAG_member, name: "_IO_backup_base", scope: !264, file: !265, line: 257, baseType: !18, size: 32, align: 32, offset: 320)
!278 = !DIDerivedType(tag: DW_TAG_member, name: "_IO_save_end", scope: !264, file: !265, line: 258, baseType: !18, size: 32, align: 32, offset: 352)
!279 = !DIDerivedType(tag: DW_TAG_member, name: "_markers", scope: !264, file: !265, line: 260, baseType: !280, size: 32, align: 32, offset: 384)
!280 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !281, size: 32, align: 32)
!281 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "_IO_marker", file: !265, line: 156, size: 96, align: 32, elements: !282)
!282 = !{!283, !284, !286}
!283 = !DIDerivedType(tag: DW_TAG_member, name: "_next", scope: !281, file: !265, line: 157, baseType: !280, size: 32, align: 32)
!284 = !DIDerivedType(tag: DW_TAG_member, name: "_sbuf", scope: !281, file: !265, line: 158, baseType: !285, size: 32, align: 32, offset: 32)
!285 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !264, size: 32, align: 32)
!286 = !DIDerivedType(tag: DW_TAG_member, name: "_pos", scope: !281, file: !265, line: 162, baseType: !12, size: 32, align: 32, offset: 64)
!287 = !DIDerivedType(tag: DW_TAG_member, name: "_chain", scope: !264, file: !265, line: 262, baseType: !285, size: 32, align: 32, offset: 416)
!288 = !DIDerivedType(tag: DW_TAG_member, name: "_fileno", scope: !264, file: !265, line: 264, baseType: !12, size: 32, align: 32, offset: 448)
!289 = !DIDerivedType(tag: DW_TAG_member, name: "_flags2", scope: !264, file: !265, line: 268, baseType: !12, size: 32, align: 32, offset: 480)
!290 = !DIDerivedType(tag: DW_TAG_member, name: "_old_offset", scope: !264, file: !265, line: 270, baseType: !291, size: 32, align: 32, offset: 512)
!291 = !DIDerivedType(tag: DW_TAG_typedef, name: "__off_t", file: !11, line: 131, baseType: !248)
!292 = !DIDerivedType(tag: DW_TAG_member, name: "_cur_column", scope: !264, file: !265, line: 274, baseType: !70, size: 16, align: 16, offset: 544)
!293 = !DIDerivedType(tag: DW_TAG_member, name: "_vtable_offset", scope: !264, file: !265, line: 275, baseType: !294, size: 8, align: 8, offset: 560)
!294 = !DIBasicType(name: "signed char", size: 8, align: 8, encoding: DW_ATE_signed_char)
!295 = !DIDerivedType(tag: DW_TAG_member, name: "_shortbuf", scope: !264, file: !265, line: 276, baseType: !296, size: 8, align: 8, offset: 568)
!296 = !DICompositeType(tag: DW_TAG_array_type, baseType: !19, size: 8, align: 8, elements: !297)
!297 = !{!298}
!298 = !DISubrange(count: 1)
!299 = !DIDerivedType(tag: DW_TAG_member, name: "_lock", scope: !264, file: !265, line: 280, baseType: !300, size: 32, align: 32, offset: 576)
!300 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !301, size: 32, align: 32)
!301 = !DIDerivedType(tag: DW_TAG_typedef, name: "_IO_lock_t", file: !265, line: 150, baseType: null)
!302 = !DIDerivedType(tag: DW_TAG_member, name: "_offset", scope: !264, file: !265, line: 289, baseType: !303, size: 64, align: 64, offset: 640)
!303 = !DIDerivedType(tag: DW_TAG_typedef, name: "__off64_t", file: !11, line: 132, baseType: !304)
!304 = !DIDerivedType(tag: DW_TAG_typedef, name: "__quad_t", file: !11, line: 55, baseType: !305)
!305 = !DIBasicType(name: "long long int", size: 64, align: 64, encoding: DW_ATE_signed)
!306 = !DIDerivedType(tag: DW_TAG_member, name: "__pad1", scope: !264, file: !265, line: 297, baseType: !32, size: 32, align: 32, offset: 704)
!307 = !DIDerivedType(tag: DW_TAG_member, name: "__pad2", scope: !264, file: !265, line: 298, baseType: !32, size: 32, align: 32, offset: 736)
!308 = !DIDerivedType(tag: DW_TAG_member, name: "__pad3", scope: !264, file: !265, line: 299, baseType: !32, size: 32, align: 32, offset: 768)
!309 = !DIDerivedType(tag: DW_TAG_member, name: "__pad4", scope: !264, file: !265, line: 300, baseType: !32, size: 32, align: 32, offset: 800)
!310 = !DIDerivedType(tag: DW_TAG_member, name: "__pad5", scope: !264, file: !265, line: 302, baseType: !311, size: 32, align: 32, offset: 832)
!311 = !DIDerivedType(tag: DW_TAG_typedef, name: "size_t", file: !312, line: 62, baseType: !94)
!312 = !DIFile(filename: "/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/../lib/clang/3.9.0/include/stddef.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/alarm4pi-cb")
!313 = !DIDerivedType(tag: DW_TAG_member, name: "_mode", scope: !264, file: !265, line: 303, baseType: !12, size: 32, align: 32, offset: 864)
!314 = !DIDerivedType(tag: DW_TAG_member, name: "_unused2", scope: !264, file: !265, line: 305, baseType: !315, size: 320, align: 8, offset: 896)
!315 = !DICompositeType(tag: DW_TAG_array_type, baseType: !19, size: 320, align: 8, elements: !316)
!316 = !{!317}
!317 = !DISubrange(count: 40)
!318 = distinct !DIGlobalVariable(name: "Event_file_handle", scope: !255, file: !256, line: 11, type: !261, isLocal: false, isDefinition: true, variable: %struct._IO_FILE** @Event_file_handle)
!319 = distinct !DICompileUnit(language: DW_LANG_C99, file: !320, producer: "clang version 3.9.0 (tags/RELEASE_390/final)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, enums: !2, retainedTypes: !321)
!320 = !DIFile(filename: "bcm_gpio.c", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/alarm4pi-cb")
!321 = !{!32}
!322 = !{!"clang version 3.9.0 (tags/RELEASE_390/final)"}
!323 = !{i32 2, !"Dwarf Version", i32 5}
!324 = !{i32 2, !"Debug Info Version", i32 3}
!325 = !{i32 1, !"wchar_size", i32 4}
!326 = !{i32 1, !"min_enum_size", i32 4}
!327 = distinct !DISubprogram(name: "usecs", scope: !1, file: !1, line: 5, type: !328, isLocal: false, isDefinition: true, scopeLine: 5, isOptimized: false, unit: !0, variables: !2)
!328 = !DISubroutineType(types: !329)
!329 = !{!42}
!330 = !DILocalVariable(name: "start", scope: !327, file: !1, line: 6, type: !331)
!331 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "timeval", file: !332, line: 30, size: 64, align: 32, elements: !333)
!332 = !DIFile(filename: "/home/zrz0517/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/libc/usr/include/bits/time.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/alarm4pi-cb")
!333 = !{!334, !335}
!334 = !DIDerivedType(tag: DW_TAG_member, name: "tv_sec", scope: !331, file: !332, line: 32, baseType: !247, size: 32, align: 32)
!335 = !DIDerivedType(tag: DW_TAG_member, name: "tv_usec", scope: !331, file: !332, line: 33, baseType: !251, size: 32, align: 32, offset: 32)
!336 = !DIExpression()
!337 = !DILocation(line: 6, column: 17, scope: !327)
!338 = !DILocation(line: 8, column: 2, scope: !327)
!339 = !DILocation(line: 10, column: 15, scope: !327)
!340 = !DILocation(line: 10, column: 22, scope: !327)
!341 = !DILocation(line: 10, column: 29, scope: !327)
!342 = !DILocation(line: 10, column: 44, scope: !327)
!343 = !DILocation(line: 10, column: 36, scope: !327)
!344 = !DILocation(line: 10, column: 2, scope: !327)
!345 = distinct !DISubprogram(name: "set_signal_handler", scope: !4, file: !4, line: 76, type: !346, isLocal: false, isDefinition: true, scopeLine: 77, flags: DIFlagPrototyped, isOptimized: false, unit: !3, variables: !2)
!346 = !DISubroutineType(types: !347)
!347 = !{!12}
!348 = !DILocalVariable(name: "ret", scope: !345, file: !4, line: 78, type: !12)
!349 = !DILocation(line: 78, column: 8, scope: !345)
!350 = !DILocalVariable(name: "act", scope: !345, file: !4, line: 79, type: !351)
!351 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "sigaction", file: !352, line: 24, size: 1120, align: 32, elements: !353)
!352 = !DIFile(filename: "/home/zrz0517/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/libc/usr/include/bits/sigaction.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/alarm4pi-cb")
!353 = !{!354, !426, !435, !436}
!354 = !DIDerivedType(tag: DW_TAG_member, name: "__sigaction_handler", scope: !351, file: !352, line: 35, baseType: !355, size: 32, align: 32)
!355 = distinct !DICompositeType(tag: DW_TAG_union_type, scope: !351, file: !352, line: 28, size: 32, align: 32, elements: !356)
!356 = !{!357, !358}
!357 = !DIDerivedType(tag: DW_TAG_member, name: "sa_handler", scope: !355, file: !352, line: 31, baseType: !252, size: 32, align: 32)
!358 = !DIDerivedType(tag: DW_TAG_member, name: "sa_sigaction", scope: !355, file: !352, line: 33, baseType: !359, size: 32, align: 32)
!359 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !360, size: 32, align: 32)
!360 = !DISubroutineType(types: !361)
!361 = !{null, !12, !362, !32}
!362 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !363, size: 32, align: 32)
!363 = !DIDerivedType(tag: DW_TAG_typedef, name: "siginfo_t", file: !364, line: 116, baseType: !365)
!364 = !DIFile(filename: "/home/zrz0517/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/libc/usr/include/bits/siginfo.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/alarm4pi-cb")
!365 = distinct !DICompositeType(tag: DW_TAG_structure_type, file: !364, line: 50, size: 1024, align: 32, elements: !366)
!366 = !{!367, !368, !369, !370}
!367 = !DIDerivedType(tag: DW_TAG_member, name: "si_signo", scope: !365, file: !364, line: 52, baseType: !12, size: 32, align: 32)
!368 = !DIDerivedType(tag: DW_TAG_member, name: "si_errno", scope: !365, file: !364, line: 53, baseType: !12, size: 32, align: 32, offset: 32)
!369 = !DIDerivedType(tag: DW_TAG_member, name: "si_code", scope: !365, file: !364, line: 55, baseType: !12, size: 32, align: 32, offset: 64)
!370 = !DIDerivedType(tag: DW_TAG_member, name: "_sifields", scope: !365, file: !364, line: 115, baseType: !371, size: 928, align: 32, offset: 96)
!371 = distinct !DICompositeType(tag: DW_TAG_union_type, scope: !365, file: !364, line: 57, size: 928, align: 32, elements: !372)
!372 = !{!373, !377, !383, !394, !400, !409, !415, !420}
!373 = !DIDerivedType(tag: DW_TAG_member, name: "_pad", scope: !371, file: !364, line: 59, baseType: !374, size: 928, align: 32)
!374 = !DICompositeType(tag: DW_TAG_array_type, baseType: !12, size: 928, align: 32, elements: !375)
!375 = !{!376}
!376 = !DISubrange(count: 29)
!377 = !DIDerivedType(tag: DW_TAG_member, name: "_kill", scope: !371, file: !364, line: 66, baseType: !378, size: 64, align: 32)
!378 = distinct !DICompositeType(tag: DW_TAG_structure_type, scope: !371, file: !364, line: 62, size: 64, align: 32, elements: !379)
!379 = !{!380, !381}
!380 = !DIDerivedType(tag: DW_TAG_member, name: "si_pid", scope: !378, file: !364, line: 64, baseType: !10, size: 32, align: 32)
!381 = !DIDerivedType(tag: DW_TAG_member, name: "si_uid", scope: !378, file: !364, line: 65, baseType: !382, size: 32, align: 32, offset: 32)
!382 = !DIDerivedType(tag: DW_TAG_typedef, name: "__uid_t", file: !11, line: 125, baseType: !94)
!383 = !DIDerivedType(tag: DW_TAG_member, name: "_timer", scope: !371, file: !364, line: 74, baseType: !384, size: 96, align: 32)
!384 = distinct !DICompositeType(tag: DW_TAG_structure_type, scope: !371, file: !364, line: 69, size: 96, align: 32, elements: !385)
!385 = !{!386, !387, !388}
!386 = !DIDerivedType(tag: DW_TAG_member, name: "si_tid", scope: !384, file: !364, line: 71, baseType: !12, size: 32, align: 32)
!387 = !DIDerivedType(tag: DW_TAG_member, name: "si_overrun", scope: !384, file: !364, line: 72, baseType: !12, size: 32, align: 32, offset: 32)
!388 = !DIDerivedType(tag: DW_TAG_member, name: "si_sigval", scope: !384, file: !364, line: 73, baseType: !389, size: 32, align: 32, offset: 64)
!389 = !DIDerivedType(tag: DW_TAG_typedef, name: "sigval_t", file: !364, line: 36, baseType: !390)
!390 = distinct !DICompositeType(tag: DW_TAG_union_type, name: "sigval", file: !364, line: 32, size: 32, align: 32, elements: !391)
!391 = !{!392, !393}
!392 = !DIDerivedType(tag: DW_TAG_member, name: "sival_int", scope: !390, file: !364, line: 34, baseType: !12, size: 32, align: 32)
!393 = !DIDerivedType(tag: DW_TAG_member, name: "sival_ptr", scope: !390, file: !364, line: 35, baseType: !32, size: 32, align: 32)
!394 = !DIDerivedType(tag: DW_TAG_member, name: "_rt", scope: !371, file: !364, line: 82, baseType: !395, size: 96, align: 32)
!395 = distinct !DICompositeType(tag: DW_TAG_structure_type, scope: !371, file: !364, line: 77, size: 96, align: 32, elements: !396)
!396 = !{!397, !398, !399}
!397 = !DIDerivedType(tag: DW_TAG_member, name: "si_pid", scope: !395, file: !364, line: 79, baseType: !10, size: 32, align: 32)
!398 = !DIDerivedType(tag: DW_TAG_member, name: "si_uid", scope: !395, file: !364, line: 80, baseType: !382, size: 32, align: 32, offset: 32)
!399 = !DIDerivedType(tag: DW_TAG_member, name: "si_sigval", scope: !395, file: !364, line: 81, baseType: !389, size: 32, align: 32, offset: 64)
!400 = !DIDerivedType(tag: DW_TAG_member, name: "_sigchld", scope: !371, file: !364, line: 92, baseType: !401, size: 160, align: 32)
!401 = distinct !DICompositeType(tag: DW_TAG_structure_type, scope: !371, file: !364, line: 85, size: 160, align: 32, elements: !402)
!402 = !{!403, !404, !405, !406, !408}
!403 = !DIDerivedType(tag: DW_TAG_member, name: "si_pid", scope: !401, file: !364, line: 87, baseType: !10, size: 32, align: 32)
!404 = !DIDerivedType(tag: DW_TAG_member, name: "si_uid", scope: !401, file: !364, line: 88, baseType: !382, size: 32, align: 32, offset: 32)
!405 = !DIDerivedType(tag: DW_TAG_member, name: "si_status", scope: !401, file: !364, line: 89, baseType: !12, size: 32, align: 32, offset: 64)
!406 = !DIDerivedType(tag: DW_TAG_member, name: "si_utime", scope: !401, file: !364, line: 90, baseType: !407, size: 32, align: 32, offset: 96)
!407 = !DIDerivedType(tag: DW_TAG_typedef, name: "__clock_t", file: !11, line: 135, baseType: !248)
!408 = !DIDerivedType(tag: DW_TAG_member, name: "si_stime", scope: !401, file: !364, line: 91, baseType: !407, size: 32, align: 32, offset: 128)
!409 = !DIDerivedType(tag: DW_TAG_member, name: "_sigfault", scope: !371, file: !364, line: 99, baseType: !410, size: 64, align: 32)
!410 = distinct !DICompositeType(tag: DW_TAG_structure_type, scope: !371, file: !364, line: 95, size: 64, align: 32, elements: !411)
!411 = !{!412, !413}
!412 = !DIDerivedType(tag: DW_TAG_member, name: "si_addr", scope: !410, file: !364, line: 97, baseType: !32, size: 32, align: 32)
!413 = !DIDerivedType(tag: DW_TAG_member, name: "si_addr_lsb", scope: !410, file: !364, line: 98, baseType: !414, size: 16, align: 16, offset: 32)
!414 = !DIBasicType(name: "short", size: 16, align: 16, encoding: DW_ATE_signed)
!415 = !DIDerivedType(tag: DW_TAG_member, name: "_sigpoll", scope: !371, file: !364, line: 106, baseType: !416, size: 64, align: 32)
!416 = distinct !DICompositeType(tag: DW_TAG_structure_type, scope: !371, file: !364, line: 102, size: 64, align: 32, elements: !417)
!417 = !{!418, !419}
!418 = !DIDerivedType(tag: DW_TAG_member, name: "si_band", scope: !416, file: !364, line: 104, baseType: !248, size: 32, align: 32)
!419 = !DIDerivedType(tag: DW_TAG_member, name: "si_fd", scope: !416, file: !364, line: 105, baseType: !12, size: 32, align: 32, offset: 32)
!420 = !DIDerivedType(tag: DW_TAG_member, name: "_sigsys", scope: !371, file: !364, line: 114, baseType: !421, size: 96, align: 32)
!421 = distinct !DICompositeType(tag: DW_TAG_structure_type, scope: !371, file: !364, line: 109, size: 96, align: 32, elements: !422)
!422 = !{!423, !424, !425}
!423 = !DIDerivedType(tag: DW_TAG_member, name: "_call_addr", scope: !421, file: !364, line: 111, baseType: !32, size: 32, align: 32)
!424 = !DIDerivedType(tag: DW_TAG_member, name: "_syscall", scope: !421, file: !364, line: 112, baseType: !12, size: 32, align: 32, offset: 32)
!425 = !DIDerivedType(tag: DW_TAG_member, name: "_arch", scope: !421, file: !364, line: 113, baseType: !94, size: 32, align: 32, offset: 64)
!426 = !DIDerivedType(tag: DW_TAG_member, name: "sa_mask", scope: !351, file: !352, line: 43, baseType: !427, size: 1024, align: 32, offset: 32)
!427 = !DIDerivedType(tag: DW_TAG_typedef, name: "__sigset_t", file: !428, line: 30, baseType: !429)
!428 = !DIFile(filename: "/home/zrz0517/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/libc/usr/include/bits/sigset.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/alarm4pi-cb")
!429 = distinct !DICompositeType(tag: DW_TAG_structure_type, file: !428, line: 27, size: 1024, align: 32, elements: !430)
!430 = !{!431}
!431 = !DIDerivedType(tag: DW_TAG_member, name: "__val", scope: !429, file: !428, line: 29, baseType: !432, size: 1024, align: 32)
!432 = !DICompositeType(tag: DW_TAG_array_type, baseType: !42, size: 1024, align: 32, elements: !433)
!433 = !{!434}
!434 = !DISubrange(count: 32)
!435 = !DIDerivedType(tag: DW_TAG_member, name: "sa_flags", scope: !351, file: !352, line: 46, baseType: !12, size: 32, align: 32, offset: 1056)
!436 = !DIDerivedType(tag: DW_TAG_member, name: "sa_restorer", scope: !351, file: !352, line: 49, baseType: !437, size: 32, align: 32, offset: 1088)
!437 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !438, size: 32, align: 32)
!438 = !DISubroutineType(types: !439)
!439 = !{null}
!440 = !DILocation(line: 79, column: 21, scope: !345)
!441 = !DILocation(line: 81, column: 4, scope: !345)
!442 = !DILocation(line: 83, column: 8, scope: !345)
!443 = !DILocation(line: 83, column: 19, scope: !345)
!444 = !DILocation(line: 84, column: 4, scope: !345)
!445 = !DILocation(line: 86, column: 8, scope: !345)
!446 = !DILocation(line: 86, column: 19, scope: !345)
!447 = !DILocation(line: 90, column: 8, scope: !345)
!448 = !DILocation(line: 90, column: 16, scope: !345)
!449 = !DILocation(line: 91, column: 4, scope: !345)
!450 = !DILocation(line: 92, column: 7, scope: !451)
!451 = distinct !DILexicalBlock(scope: !345, file: !4, line: 92, column: 7)
!452 = !DILocation(line: 92, column: 38, scope: !451)
!453 = !DILocation(line: 92, column: 7, scope: !345)
!454 = !DILocation(line: 93, column: 10, scope: !451)
!455 = !DILocation(line: 93, column: 7, scope: !451)
!456 = !DILocation(line: 96, column: 11, scope: !457)
!457 = distinct !DILexicalBlock(scope: !451, file: !4, line: 95, column: 6)
!458 = !DILocation(line: 96, column: 10, scope: !457)
!459 = !DILocation(line: 97, column: 7, scope: !457)
!460 = !DILocation(line: 97, column: 7, scope: !461)
!461 = !DILexicalBlockFile(scope: !457, file: !4, discriminator: 1)
!462 = !DILocation(line: 99, column: 11, scope: !345)
!463 = !DILocation(line: 99, column: 4, scope: !345)
!464 = !DILocalVariable(name: "signum", arg: 1, scope: !26, file: !4, line: 69, type: !12)
!465 = !DILocation(line: 69, column: 31, scope: !26)
!466 = !DILocation(line: 72, column: 4, scope: !26)
!467 = !DILocation(line: 73, column: 3, scope: !26)
!468 = distinct !DISubprogram(name: "exit_deamon_handler", scope: !4, file: !4, line: 59, type: !27, isLocal: true, isDefinition: true, scopeLine: 60, flags: DIFlagPrototyped, isOptimized: false, unit: !3, variables: !2)
!469 = !DILocalVariable(name: "sig", arg: 1, scope: !468, file: !4, line: 59, type: !12)
!470 = !DILocation(line: 59, column: 37, scope: !468)
!471 = !DILocation(line: 61, column: 4, scope: !468)
!472 = !DILocation(line: 62, column: 4, scope: !468)
!473 = !DILocation(line: 63, column: 21, scope: !468)
!474 = !DILocation(line: 64, column: 3, scope: !468)
!475 = distinct !DISubprogram(name: "main", scope: !4, file: !4, line: 103, type: !476, isLocal: false, isDefinition: true, scopeLine: 104, flags: DIFlagPrototyped, isOptimized: false, unit: !3, variables: !2)
!476 = !DISubroutineType(types: !477)
!477 = !{!12, !12, !478}
!478 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !18, size: 32, align: 32)
!479 = !DILocalVariable(name: "argc", arg: 1, scope: !475, file: !4, line: 103, type: !12)
!480 = !DILocation(line: 103, column: 14, scope: !475)
!481 = !DILocalVariable(name: "argv", arg: 2, scope: !475, file: !4, line: 103, type: !478)
!482 = !DILocation(line: 103, column: 26, scope: !475)
!483 = !DILocalVariable(name: "main_err", scope: !475, file: !4, line: 105, type: !12)
!484 = !DILocation(line: 105, column: 8, scope: !475)
!485 = !DILocalVariable(name: "capture_proc", scope: !475, file: !4, line: 106, type: !8)
!486 = !DILocation(line: 106, column: 10, scope: !475)
!487 = !DILocalVariable(name: "web_server_proc", scope: !475, file: !4, line: 106, type: !8)
!488 = !DILocation(line: 106, column: 24, scope: !475)
!489 = !DILocation(line: 110, column: 13, scope: !475)
!490 = !DILocation(line: 111, column: 7, scope: !491)
!491 = distinct !DILexicalBlock(scope: !475, file: !4, line: 111, column: 7)
!492 = !DILocation(line: 111, column: 16, scope: !491)
!493 = !DILocation(line: 111, column: 7, scope: !475)
!494 = !DILocation(line: 113, column: 7, scope: !495)
!495 = distinct !DILexicalBlock(scope: !491, file: !4, line: 112, column: 6)
!496 = !DILocation(line: 115, column: 10, scope: !497)
!497 = distinct !DILexicalBlock(scope: !495, file: !4, line: 115, column: 10)
!498 = !DILocation(line: 115, column: 10, scope: !495)
!499 = !DILocation(line: 116, column: 10, scope: !497)
!500 = !DILocation(line: 118, column: 7, scope: !495)
!501 = !DILocation(line: 122, column: 10, scope: !502)
!502 = distinct !DILexicalBlock(scope: !495, file: !4, line: 122, column: 10)
!503 = !DILocation(line: 122, column: 63, scope: !502)
!504 = !DILocation(line: 122, column: 10, scope: !495)
!505 = !DILocation(line: 123, column: 10, scope: !502)
!506 = !DILocation(line: 123, column: 10, scope: !507)
!507 = !DILexicalBlockFile(scope: !502, file: !4, discriminator: 1)
!508 = !DILocation(line: 125, column: 47, scope: !509)
!509 = distinct !DILexicalBlock(scope: !495, file: !4, line: 125, column: 9)
!510 = !DILocation(line: 125, column: 9, scope: !509)
!511 = !DILocation(line: 125, column: 87, scope: !509)
!512 = !DILocation(line: 125, column: 9, scope: !495)
!513 = !DILocation(line: 127, column: 29, scope: !514)
!514 = distinct !DILexicalBlock(scope: !509, file: !4, line: 126, column: 8)
!515 = !DILocation(line: 127, column: 28, scope: !514)
!516 = !DILocation(line: 128, column: 9, scope: !514)
!517 = !DILocation(line: 129, column: 53, scope: !518)
!518 = distinct !DILexicalBlock(scope: !514, file: !4, line: 129, column: 12)
!519 = !DILocation(line: 129, column: 12, scope: !518)
!520 = !DILocation(line: 129, column: 99, scope: !518)
!521 = !DILocation(line: 129, column: 12, scope: !514)
!522 = !DILocation(line: 131, column: 32, scope: !523)
!523 = distinct !DILexicalBlock(scope: !518, file: !4, line: 130, column: 11)
!524 = !DILocation(line: 131, column: 31, scope: !523)
!525 = !DILocation(line: 133, column: 12, scope: !523)
!526 = !DILocation(line: 134, column: 10, scope: !523)
!527 = !DILocation(line: 135, column: 8, scope: !514)
!528 = !DILocation(line: 137, column: 18, scope: !495)
!529 = !DILocation(line: 137, column: 16, scope: !495)
!530 = !DILocation(line: 138, column: 32, scope: !495)
!531 = !DILocation(line: 138, column: 7, scope: !495)
!532 = !DILocation(line: 139, column: 10, scope: !533)
!533 = distinct !DILexicalBlock(scope: !495, file: !4, line: 139, column: 10)
!534 = !DILocation(line: 139, column: 19, scope: !533)
!535 = !DILocation(line: 139, column: 10, scope: !495)
!536 = !DILocation(line: 141, column: 10, scope: !537)
!537 = distinct !DILexicalBlock(scope: !533, file: !4, line: 140, column: 9)
!538 = !DILocation(line: 142, column: 9, scope: !537)
!539 = !DILocation(line: 144, column: 10, scope: !533)
!540 = !DILocation(line: 147, column: 7, scope: !495)
!541 = !DILocation(line: 149, column: 7, scope: !495)
!542 = !DILocation(line: 151, column: 7, scope: !495)
!543 = !DILocation(line: 156, column: 7, scope: !495)
!544 = !DILocation(line: 159, column: 7, scope: !495)
!545 = !DILocation(line: 160, column: 6, scope: !495)
!546 = !DILocation(line: 161, column: 11, scope: !475)
!547 = !DILocation(line: 161, column: 4, scope: !475)
!548 = distinct !DISubprogram(name: "send_info_notif", scope: !30, file: !30, line: 44, type: !549, isLocal: false, isDefinition: true, scopeLine: 45, flags: DIFlagPrototyped, isOptimized: false, unit: !29, variables: !2)
!549 = !DISubroutineType(types: !550)
!550 = !{!12, !18, !18}
!551 = !DILocalVariable(name: "msg_str", arg: 1, scope: !548, file: !30, line: 44, type: !18)
!552 = !DILocation(line: 44, column: 27, scope: !548)
!553 = !DILocalVariable(name: "msg_priority", arg: 2, scope: !548, file: !30, line: 44, type: !18)
!554 = !DILocation(line: 44, column: 42, scope: !548)
!555 = !DILocalVariable(name: "tot_msg_str", scope: !548, file: !30, line: 46, type: !556)
!556 = !DICompositeType(tag: DW_TAG_array_type, baseType: !19, size: 32768, align: 8, elements: !557)
!557 = !{!558}
!558 = !DISubrange(count: 4096)
!559 = !DILocation(line: 46, column: 9, scope: !548)
!560 = !DILocation(line: 48, column: 13, scope: !548)
!561 = !DILocation(line: 48, column: 73, scope: !548)
!562 = !DILocation(line: 48, column: 4, scope: !548)
!563 = !DILocation(line: 50, column: 29, scope: !548)
!564 = !DILocation(line: 50, column: 42, scope: !548)
!565 = !DILocation(line: 50, column: 11, scope: !548)
!566 = !DILocation(line: 50, column: 4, scope: !548)
!567 = distinct !DISubprogram(name: "update_ip_msg", scope: !30, file: !30, line: 54, type: !568, isLocal: false, isDefinition: true, scopeLine: 55, flags: DIFlagPrototyped, isOptimized: false, unit: !29, variables: !2)
!568 = !DISubroutineType(types: !569)
!569 = !{!12, !18}
!570 = !DILocalVariable(name: "msg_info_fmt", arg: 1, scope: !567, file: !30, line: 54, type: !18)
!571 = !DILocation(line: 54, column: 25, scope: !567)
!572 = !DILocalVariable(name: "ret_err", scope: !567, file: !30, line: 56, type: !12)
!573 = !DILocation(line: 56, column: 8, scope: !567)
!574 = !DILocalVariable(name: "wan_address", scope: !567, file: !30, line: 58, type: !575)
!575 = !DICompositeType(tag: DW_TAG_array_type, baseType: !19, size: 368, align: 8, elements: !576)
!576 = !{!577}
!577 = !DISubrange(count: 46)
!578 = !DILocation(line: 58, column: 9, scope: !567)
!579 = !DILocalVariable(name: "curr_msg_info_str", scope: !567, file: !30, line: 59, type: !44)
!580 = !DILocation(line: 59, column: 9, scope: !567)
!581 = !DILocation(line: 61, column: 26, scope: !567)
!582 = !DILocation(line: 61, column: 12, scope: !567)
!583 = !DILocation(line: 61, column: 11, scope: !567)
!584 = !DILocation(line: 62, column: 7, scope: !585)
!585 = distinct !DILexicalBlock(scope: !567, file: !30, line: 62, column: 7)
!586 = !DILocation(line: 62, column: 14, scope: !585)
!587 = !DILocation(line: 62, column: 7, scope: !567)
!588 = !DILocation(line: 65, column: 16, scope: !589)
!589 = distinct !DILexicalBlock(scope: !585, file: !30, line: 63, column: 6)
!590 = !DILocation(line: 65, column: 62, scope: !589)
!591 = !DILocation(line: 65, column: 76, scope: !589)
!592 = !DILocation(line: 65, column: 7, scope: !589)
!593 = !DILocation(line: 66, column: 17, scope: !594)
!594 = distinct !DILexicalBlock(scope: !589, file: !30, line: 66, column: 10)
!595 = !DILocation(line: 66, column: 10, scope: !594)
!596 = !DILocation(line: 66, column: 50, scope: !594)
!597 = !DILocation(line: 66, column: 10, scope: !589)
!598 = !DILocation(line: 68, column: 31, scope: !599)
!599 = distinct !DILexicalBlock(scope: !594, file: !30, line: 67, column: 9)
!600 = !DILocation(line: 68, column: 10, scope: !599)
!601 = !DILocation(line: 70, column: 10, scope: !599)
!602 = !DILocation(line: 72, column: 10, scope: !599)
!603 = !DILocation(line: 73, column: 9, scope: !599)
!604 = !DILocation(line: 74, column: 6, scope: !589)
!605 = !DILocation(line: 75, column: 11, scope: !567)
!606 = !DILocation(line: 75, column: 4, scope: !567)
!607 = distinct !DISubprogram(name: "polling_thread", scope: !30, file: !30, line: 78, type: !608, isLocal: false, isDefinition: true, scopeLine: 79, flags: DIFlagPrototyped, isOptimized: false, unit: !29, variables: !2)
!608 = !DISubroutineType(types: !609)
!609 = !{!32, !610}
!610 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !24, size: 32, align: 32)
!611 = !DILocalVariable(name: "exit_polling", arg: 1, scope: !607, file: !30, line: 78, type: !610)
!612 = !DILocation(line: 78, column: 36, scope: !607)
!613 = !DILocalVariable(name: "ret_err", scope: !607, file: !30, line: 80, type: !12)
!614 = !DILocation(line: 80, column: 47, scope: !607)
!615 = !DILocation(line: 80, column: 4, scope: !607)
!616 = !DILocalVariable(name: "read_err", scope: !607, file: !30, line: 81, type: !12)
!617 = !DILocation(line: 81, column: 47, scope: !607)
!618 = !DILocation(line: 81, column: 4, scope: !607)
!619 = !DILocalVariable(name: "curr_pir_value", scope: !607, file: !30, line: 82, type: !12)
!620 = !DILocation(line: 82, column: 47, scope: !607)
!621 = !DILocation(line: 82, column: 4, scope: !607)
!622 = !DILocalVariable(name: "last_pir_value", scope: !607, file: !30, line: 83, type: !12)
!623 = !DILocation(line: 83, column: 47, scope: !607)
!624 = !DILocation(line: 83, column: 4, scope: !607)
!625 = !DILocalVariable(name: "pir_perman_counter", scope: !607, file: !30, line: 84, type: !12)
!626 = !DILocation(line: 84, column: 47, scope: !607)
!627 = !DILocation(line: 84, column: 4, scope: !607)
!628 = !DILocation(line: 98, column: 4, scope: !607)
!629 = !DILocation(line: 100, column: 13, scope: !607)
!630 = !DILocation(line: 101, column: 23, scope: !607)
!631 = !DILocation(line: 102, column: 19, scope: !607)
!632 = !DILocalVariable(name: "i", scope: !607, file: !30, line: 103, type: !12)
!633 = !DILocation(line: 103, column: 8, scope: !607)
!634 = !DILocation(line: 104, column: 4, scope: !607)
!635 = !DILocation(line: 104, column: 11, scope: !636)
!636 = !DILexicalBlockFile(scope: !607, file: !30, discriminator: 1)
!637 = !DILocation(line: 104, column: 14, scope: !636)
!638 = !DILocation(line: 104, column: 4, scope: !636)
!639 = !DILocation(line: 108, column: 17, scope: !640)
!640 = distinct !DILexicalBlock(scope: !607, file: !30, line: 105, column: 6)
!641 = !DILocation(line: 108, column: 15, scope: !640)
!642 = !DILocation(line: 109, column: 10, scope: !643)
!643 = distinct !DILexicalBlock(scope: !640, file: !30, line: 109, column: 10)
!644 = !DILocation(line: 109, column: 18, scope: !643)
!645 = !DILocation(line: 109, column: 10, scope: !640)
!646 = !DILocation(line: 111, column: 13, scope: !647)
!647 = distinct !DILexicalBlock(scope: !648, file: !30, line: 111, column: 13)
!648 = distinct !DILexicalBlock(scope: !643, file: !30, line: 110, column: 9)
!649 = !DILocation(line: 111, column: 31, scope: !647)
!650 = !DILocation(line: 111, column: 28, scope: !647)
!651 = !DILocation(line: 111, column: 13, scope: !648)
!652 = !DILocation(line: 113, column: 16, scope: !653)
!653 = distinct !DILexicalBlock(scope: !654, file: !30, line: 113, column: 16)
!654 = distinct !DILexicalBlock(scope: !647, file: !30, line: 112, column: 12)
!655 = !DILocation(line: 113, column: 31, scope: !653)
!656 = !DILocation(line: 113, column: 16, scope: !654)
!657 = !DILocation(line: 115, column: 16, scope: !658)
!658 = distinct !DILexicalBlock(scope: !653, file: !30, line: 114, column: 15)
!659 = !DILocation(line: 116, column: 16, scope: !658)
!660 = !DILocation(line: 117, column: 15, scope: !658)
!661 = !DILocation(line: 118, column: 30, scope: !654)
!662 = !DILocation(line: 118, column: 28, scope: !654)
!663 = !DILocation(line: 119, column: 12, scope: !654)
!664 = !DILocation(line: 121, column: 13, scope: !665)
!665 = distinct !DILexicalBlock(scope: !648, file: !30, line: 121, column: 13)
!666 = !DILocation(line: 121, column: 28, scope: !665)
!667 = !DILocation(line: 121, column: 13, scope: !648)
!668 = !DILocation(line: 122, column: 32, scope: !665)
!669 = !DILocation(line: 122, column: 13, scope: !665)
!670 = !DILocation(line: 124, column: 9, scope: !648)
!671 = !DILocation(line: 127, column: 13, scope: !672)
!672 = distinct !DILexicalBlock(scope: !673, file: !30, line: 127, column: 13)
!673 = distinct !DILexicalBlock(scope: !643, file: !30, line: 126, column: 9)
!674 = !DILocation(line: 127, column: 21, scope: !672)
!675 = !DILocation(line: 127, column: 13, scope: !673)
!676 = !DILocation(line: 129, column: 13, scope: !677)
!677 = distinct !DILexicalBlock(scope: !672, file: !30, line: 128, column: 12)
!678 = !DILocation(line: 129, column: 13, scope: !679)
!679 = !DILexicalBlockFile(scope: !677, file: !30, discriminator: 1)
!680 = !DILocation(line: 130, column: 22, scope: !677)
!681 = !DILocation(line: 130, column: 21, scope: !677)
!682 = !DILocation(line: 131, column: 12, scope: !677)
!683 = !DILocation(line: 134, column: 10, scope: !684)
!684 = distinct !DILexicalBlock(scope: !640, file: !30, line: 134, column: 10)
!685 = !DILocation(line: 134, column: 29, scope: !684)
!686 = !DILocation(line: 134, column: 10, scope: !640)
!687 = !DILocation(line: 135, column: 28, scope: !684)
!688 = !DILocation(line: 135, column: 10, scope: !684)
!689 = !DILocation(line: 104, column: 4, scope: !690)
!690 = !DILexicalBlockFile(scope: !607, file: !30, discriminator: 2)
!691 = distinct !{!691, !634}
!692 = !DILocation(line: 142, column: 4, scope: !607)
!693 = !DILocation(line: 143, column: 29, scope: !607)
!694 = !DILocation(line: 143, column: 11, scope: !607)
!695 = !DILocation(line: 143, column: 4, scope: !607)
!696 = distinct !DISubprogram(name: "init_polling", scope: !30, file: !30, line: 154, type: !697, isLocal: false, isDefinition: true, scopeLine: 155, flags: DIFlagPrototyped, isOptimized: false, unit: !29, variables: !2)
!697 = !DISubroutineType(types: !698)
!698 = !{!12, !610, !18}
!699 = !DILocalVariable(name: "exit_polling", arg: 1, scope: !696, file: !30, line: 154, type: !610)
!700 = !DILocation(line: 154, column: 32, scope: !696)
!701 = !DILocalVariable(name: "msg_info_fmt", arg: 2, scope: !696, file: !30, line: 154, type: !18)
!702 = !DILocation(line: 154, column: 52, scope: !696)
!703 = !DILocation(line: 156, column: 3, scope: !696)
!704 = !DILocation(line: 158, column: 17, scope: !696)
!705 = !DILocalVariable(name: "ret_err", scope: !696, file: !30, line: 159, type: !12)
!706 = !DILocation(line: 159, column: 46, scope: !696)
!707 = !DILocation(line: 159, column: 3, scope: !696)
!708 = !DILocalVariable(name: "start", scope: !696, file: !30, line: 160, type: !42)
!709 = !DILocation(line: 160, column: 17, scope: !696)
!710 = !DILocalVariable(name: "end", scope: !696, file: !30, line: 160, type: !42)
!711 = !DILocation(line: 160, column: 24, scope: !696)
!712 = !DILocation(line: 162, column: 11, scope: !696)
!713 = !DILocation(line: 162, column: 9, scope: !696)
!714 = !DILocation(line: 165, column: 12, scope: !696)
!715 = !DILocation(line: 165, column: 11, scope: !696)
!716 = !DILocation(line: 166, column: 41, scope: !696)
!717 = !DILocation(line: 166, column: 4, scope: !696)
!718 = !DILocation(line: 167, column: 7, scope: !719)
!719 = distinct !DILexicalBlock(scope: !696, file: !30, line: 167, column: 7)
!720 = !DILocation(line: 167, column: 14, scope: !719)
!721 = !DILocation(line: 167, column: 7, scope: !696)
!722 = !DILocation(line: 169, column: 15, scope: !723)
!723 = distinct !DILexicalBlock(scope: !719, file: !30, line: 168, column: 6)
!724 = !DILocation(line: 169, column: 14, scope: !723)
!725 = !DILocation(line: 170, column: 10, scope: !726)
!726 = distinct !DILexicalBlock(scope: !723, file: !30, line: 170, column: 10)
!727 = !DILocation(line: 170, column: 17, scope: !726)
!728 = !DILocation(line: 170, column: 10, scope: !723)
!729 = !DILocation(line: 173, column: 13, scope: !730)
!730 = distinct !DILexicalBlock(scope: !731, file: !30, line: 173, column: 13)
!731 = distinct !DILexicalBlock(scope: !726, file: !30, line: 171, column: 9)
!732 = !DILocation(line: 173, column: 21, scope: !730)
!733 = !DILocation(line: 173, column: 13, scope: !731)
!734 = !DILocation(line: 175, column: 28, scope: !735)
!735 = distinct !DILexicalBlock(scope: !730, file: !30, line: 174, column: 12)
!736 = !DILocation(line: 182, column: 28, scope: !735)
!737 = !DILocation(line: 182, column: 13, scope: !735)
!738 = !DILocation(line: 183, column: 16, scope: !739)
!739 = distinct !DILexicalBlock(scope: !735, file: !30, line: 183, column: 16)
!740 = !DILocation(line: 183, column: 24, scope: !739)
!741 = !DILocation(line: 183, column: 16, scope: !735)
!742 = !DILocation(line: 184, column: 16, scope: !739)
!743 = !DILocation(line: 186, column: 16, scope: !739)
!744 = !DILocation(line: 186, column: 16, scope: !745)
!745 = !DILexicalBlockFile(scope: !739, file: !30, discriminator: 1)
!746 = !DILocation(line: 188, column: 12, scope: !735)
!747 = !DILocation(line: 189, column: 9, scope: !731)
!748 = !DILocation(line: 190, column: 6, scope: !723)
!749 = !DILocation(line: 193, column: 19, scope: !696)
!750 = !DILocation(line: 194, column: 24, scope: !696)
!751 = !DILocation(line: 195, column: 4, scope: !696)
!752 = !DILocation(line: 196, column: 11, scope: !696)
!753 = !DILocation(line: 196, column: 9, scope: !696)
!754 = !DILocation(line: 197, column: 56, scope: !696)
!755 = !DILocation(line: 197, column: 62, scope: !696)
!756 = !DILocation(line: 197, column: 60, scope: !696)
!757 = !DILocation(line: 197, column: 5, scope: !696)
!758 = !DILocation(line: 199, column: 11, scope: !696)
!759 = !DILocation(line: 199, column: 4, scope: !696)
!760 = distinct !DISubprogram(name: "wait_polling_end", scope: !30, file: !30, line: 202, type: !346, isLocal: false, isDefinition: true, scopeLine: 203, flags: DIFlagPrototyped, isOptimized: false, unit: !29, variables: !2)
!761 = !DILocalVariable(name: "ret_err", scope: !760, file: !30, line: 204, type: !12)
!762 = !DILocation(line: 204, column: 8, scope: !760)
!763 = !DILocation(line: 205, column: 27, scope: !760)
!764 = !DILocation(line: 205, column: 14, scope: !760)
!765 = !DILocation(line: 205, column: 12, scope: !760)
!766 = !DILocation(line: 206, column: 7, scope: !767)
!767 = distinct !DILexicalBlock(scope: !760, file: !30, line: 206, column: 7)
!768 = !DILocation(line: 206, column: 15, scope: !767)
!769 = !DILocation(line: 206, column: 7, scope: !760)
!770 = !DILocation(line: 207, column: 7, scope: !767)
!771 = !DILocation(line: 209, column: 7, scope: !767)
!772 = !DILocation(line: 210, column: 4, scope: !760)
!773 = !DILocation(line: 211, column: 11, scope: !760)
!774 = !DILocation(line: 211, column: 4, scope: !760)
!775 = distinct !DISubprogram(name: "pushover_init", scope: !48, file: !48, line: 50, type: !568, isLocal: false, isDefinition: true, scopeLine: 51, flags: DIFlagPrototyped, isOptimized: false, unit: !47, variables: !2)
!776 = !DILocalVariable(name: "conf_filename", arg: 1, scope: !775, file: !48, line: 50, type: !18)
!777 = !DILocation(line: 50, column: 25, scope: !775)
!778 = !DILocalVariable(name: "ret_error", scope: !775, file: !48, line: 52, type: !12)
!779 = !DILocation(line: 52, column: 8, scope: !775)
!780 = !DILocalVariable(name: "conf_fd", scope: !775, file: !48, line: 53, type: !781)
!781 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !782, size: 32, align: 32)
!782 = !DIDerivedType(tag: DW_TAG_typedef, name: "FILE", file: !263, line: 48, baseType: !783)
!783 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "_IO_FILE", file: !265, line: 241, size: 1216, align: 64, elements: !784)
!784 = !{!785, !786, !787, !788, !789, !790, !791, !792, !793, !794, !795, !796, !797, !805, !806, !807, !808, !809, !810, !811, !812, !813, !814, !815, !816, !817, !818, !819, !820}
!785 = !DIDerivedType(tag: DW_TAG_member, name: "_flags", scope: !783, file: !265, line: 242, baseType: !12, size: 32, align: 32)
!786 = !DIDerivedType(tag: DW_TAG_member, name: "_IO_read_ptr", scope: !783, file: !265, line: 247, baseType: !18, size: 32, align: 32, offset: 32)
!787 = !DIDerivedType(tag: DW_TAG_member, name: "_IO_read_end", scope: !783, file: !265, line: 248, baseType: !18, size: 32, align: 32, offset: 64)
!788 = !DIDerivedType(tag: DW_TAG_member, name: "_IO_read_base", scope: !783, file: !265, line: 249, baseType: !18, size: 32, align: 32, offset: 96)
!789 = !DIDerivedType(tag: DW_TAG_member, name: "_IO_write_base", scope: !783, file: !265, line: 250, baseType: !18, size: 32, align: 32, offset: 128)
!790 = !DIDerivedType(tag: DW_TAG_member, name: "_IO_write_ptr", scope: !783, file: !265, line: 251, baseType: !18, size: 32, align: 32, offset: 160)
!791 = !DIDerivedType(tag: DW_TAG_member, name: "_IO_write_end", scope: !783, file: !265, line: 252, baseType: !18, size: 32, align: 32, offset: 192)
!792 = !DIDerivedType(tag: DW_TAG_member, name: "_IO_buf_base", scope: !783, file: !265, line: 253, baseType: !18, size: 32, align: 32, offset: 224)
!793 = !DIDerivedType(tag: DW_TAG_member, name: "_IO_buf_end", scope: !783, file: !265, line: 254, baseType: !18, size: 32, align: 32, offset: 256)
!794 = !DIDerivedType(tag: DW_TAG_member, name: "_IO_save_base", scope: !783, file: !265, line: 256, baseType: !18, size: 32, align: 32, offset: 288)
!795 = !DIDerivedType(tag: DW_TAG_member, name: "_IO_backup_base", scope: !783, file: !265, line: 257, baseType: !18, size: 32, align: 32, offset: 320)
!796 = !DIDerivedType(tag: DW_TAG_member, name: "_IO_save_end", scope: !783, file: !265, line: 258, baseType: !18, size: 32, align: 32, offset: 352)
!797 = !DIDerivedType(tag: DW_TAG_member, name: "_markers", scope: !783, file: !265, line: 260, baseType: !798, size: 32, align: 32, offset: 384)
!798 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !799, size: 32, align: 32)
!799 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "_IO_marker", file: !265, line: 156, size: 96, align: 32, elements: !800)
!800 = !{!801, !802, !804}
!801 = !DIDerivedType(tag: DW_TAG_member, name: "_next", scope: !799, file: !265, line: 157, baseType: !798, size: 32, align: 32)
!802 = !DIDerivedType(tag: DW_TAG_member, name: "_sbuf", scope: !799, file: !265, line: 158, baseType: !803, size: 32, align: 32, offset: 32)
!803 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !783, size: 32, align: 32)
!804 = !DIDerivedType(tag: DW_TAG_member, name: "_pos", scope: !799, file: !265, line: 162, baseType: !12, size: 32, align: 32, offset: 64)
!805 = !DIDerivedType(tag: DW_TAG_member, name: "_chain", scope: !783, file: !265, line: 262, baseType: !803, size: 32, align: 32, offset: 416)
!806 = !DIDerivedType(tag: DW_TAG_member, name: "_fileno", scope: !783, file: !265, line: 264, baseType: !12, size: 32, align: 32, offset: 448)
!807 = !DIDerivedType(tag: DW_TAG_member, name: "_flags2", scope: !783, file: !265, line: 268, baseType: !12, size: 32, align: 32, offset: 480)
!808 = !DIDerivedType(tag: DW_TAG_member, name: "_old_offset", scope: !783, file: !265, line: 270, baseType: !291, size: 32, align: 32, offset: 512)
!809 = !DIDerivedType(tag: DW_TAG_member, name: "_cur_column", scope: !783, file: !265, line: 274, baseType: !70, size: 16, align: 16, offset: 544)
!810 = !DIDerivedType(tag: DW_TAG_member, name: "_vtable_offset", scope: !783, file: !265, line: 275, baseType: !294, size: 8, align: 8, offset: 560)
!811 = !DIDerivedType(tag: DW_TAG_member, name: "_shortbuf", scope: !783, file: !265, line: 276, baseType: !296, size: 8, align: 8, offset: 568)
!812 = !DIDerivedType(tag: DW_TAG_member, name: "_lock", scope: !783, file: !265, line: 280, baseType: !300, size: 32, align: 32, offset: 576)
!813 = !DIDerivedType(tag: DW_TAG_member, name: "_offset", scope: !783, file: !265, line: 289, baseType: !303, size: 64, align: 64, offset: 640)
!814 = !DIDerivedType(tag: DW_TAG_member, name: "__pad1", scope: !783, file: !265, line: 297, baseType: !32, size: 32, align: 32, offset: 704)
!815 = !DIDerivedType(tag: DW_TAG_member, name: "__pad2", scope: !783, file: !265, line: 298, baseType: !32, size: 32, align: 32, offset: 736)
!816 = !DIDerivedType(tag: DW_TAG_member, name: "__pad3", scope: !783, file: !265, line: 299, baseType: !32, size: 32, align: 32, offset: 768)
!817 = !DIDerivedType(tag: DW_TAG_member, name: "__pad4", scope: !783, file: !265, line: 300, baseType: !32, size: 32, align: 32, offset: 800)
!818 = !DIDerivedType(tag: DW_TAG_member, name: "__pad5", scope: !783, file: !265, line: 302, baseType: !311, size: 32, align: 32, offset: 832)
!819 = !DIDerivedType(tag: DW_TAG_member, name: "_mode", scope: !783, file: !265, line: 303, baseType: !12, size: 32, align: 32, offset: 864)
!820 = !DIDerivedType(tag: DW_TAG_member, name: "_unused2", scope: !783, file: !265, line: 305, baseType: !315, size: 320, align: 8, offset: 896)
!821 = !DILocation(line: 53, column: 10, scope: !775)
!822 = !DILocalVariable(name: "full_conf_filename", scope: !775, file: !48, line: 54, type: !823)
!823 = !DICompositeType(tag: DW_TAG_array_type, baseType: !19, size: 32776, align: 8, elements: !824)
!824 = !{!825}
!825 = !DISubrange(count: 4097)
!826 = !DILocation(line: 54, column: 9, scope: !775)
!827 = !DILocation(line: 56, column: 14, scope: !828)
!828 = distinct !DILexicalBlock(scope: !775, file: !48, line: 56, column: 7)
!829 = !DILocation(line: 56, column: 7, scope: !828)
!830 = !DILocation(line: 56, column: 28, scope: !828)
!831 = !DILocation(line: 56, column: 7, scope: !775)
!832 = !DILocation(line: 57, column: 7, scope: !828)
!833 = !DILocation(line: 59, column: 7, scope: !834)
!834 = distinct !DILexicalBlock(scope: !775, file: !48, line: 59, column: 7)
!835 = !DILocation(line: 59, column: 24, scope: !834)
!836 = !DILocation(line: 59, column: 7, scope: !775)
!837 = !DILocation(line: 61, column: 41, scope: !838)
!838 = distinct !DILexicalBlock(scope: !834, file: !48, line: 60, column: 6)
!839 = !DILocation(line: 61, column: 19, scope: !838)
!840 = !DILocation(line: 61, column: 17, scope: !838)
!841 = !DILocation(line: 62, column: 10, scope: !842)
!842 = distinct !DILexicalBlock(scope: !838, file: !48, line: 62, column: 10)
!843 = !DILocation(line: 62, column: 20, scope: !842)
!844 = !DILocation(line: 62, column: 10, scope: !838)
!845 = !DILocation(line: 64, column: 20, scope: !846)
!846 = distinct !DILexicalBlock(scope: !847, file: !48, line: 64, column: 13)
!847 = distinct !DILexicalBlock(scope: !842, file: !48, line: 63, column: 9)
!848 = !DILocation(line: 64, column: 13, scope: !846)
!849 = !DILocation(line: 64, column: 47, scope: !846)
!850 = !DILocation(line: 64, column: 40, scope: !851)
!851 = !DILexicalBlockFile(scope: !846, file: !48, discriminator: 1)
!852 = !DILocation(line: 64, column: 39, scope: !846)
!853 = !DILocation(line: 64, column: 62, scope: !846)
!854 = !DILocation(line: 64, column: 13, scope: !847)
!855 = !DILocation(line: 65, column: 20, scope: !846)
!856 = !DILocation(line: 65, column: 40, scope: !846)
!857 = !DILocation(line: 65, column: 13, scope: !846)
!858 = !DILocation(line: 67, column: 20, scope: !846)
!859 = !DILocation(line: 67, column: 40, scope: !846)
!860 = !DILocation(line: 67, column: 13, scope: !846)
!861 = !DILocation(line: 68, column: 9, scope: !847)
!862 = !DILocation(line: 71, column: 10, scope: !863)
!863 = distinct !DILexicalBlock(scope: !842, file: !48, line: 70, column: 9)
!864 = !DILocation(line: 72, column: 17, scope: !863)
!865 = !DILocation(line: 72, column: 37, scope: !863)
!866 = !DILocation(line: 72, column: 10, scope: !863)
!867 = !DILocation(line: 74, column: 6, scope: !838)
!868 = !DILocation(line: 76, column: 14, scope: !834)
!869 = !DILocation(line: 76, column: 34, scope: !834)
!870 = !DILocation(line: 76, column: 7, scope: !834)
!871 = !DILocation(line: 78, column: 18, scope: !775)
!872 = !DILocation(line: 78, column: 12, scope: !775)
!873 = !DILocation(line: 78, column: 11, scope: !775)
!874 = !DILocation(line: 79, column: 7, scope: !875)
!875 = distinct !DILexicalBlock(scope: !775, file: !48, line: 79, column: 7)
!876 = !DILocation(line: 79, column: 15, scope: !875)
!877 = !DILocation(line: 79, column: 7, scope: !775)
!878 = !DILocalVariable(name: "server_url", scope: !879, file: !48, line: 81, type: !880)
!879 = distinct !DILexicalBlock(scope: !875, file: !48, line: 80, column: 6)
!880 = !DICompositeType(tag: DW_TAG_array_type, baseType: !19, size: 16672, align: 8, elements: !881)
!881 = !{!882}
!882 = !DISubrange(count: 2084)
!883 = !DILocation(line: 81, column: 12, scope: !879)
!884 = !DILocation(line: 85, column: 7, scope: !879)
!885 = !DILocation(line: 85, column: 20, scope: !879)
!886 = !DILocation(line: 87, column: 18, scope: !879)
!887 = !DILocation(line: 88, column: 17, scope: !879)
!888 = !DILocation(line: 89, column: 7, scope: !879)
!889 = !DILocation(line: 91, column: 17, scope: !879)
!890 = !DILocation(line: 92, column: 7, scope: !879)
!891 = !DILocation(line: 92, column: 19, scope: !892)
!892 = !DILexicalBlockFile(scope: !879, file: !48, discriminator: 1)
!893 = !DILocation(line: 92, column: 14, scope: !892)
!894 = !DILocation(line: 92, column: 28, scope: !892)
!895 = !DILocation(line: 92, column: 31, scope: !896)
!896 = !DILexicalBlockFile(scope: !879, file: !48, discriminator: 2)
!897 = !DILocation(line: 92, column: 41, scope: !896)
!898 = !DILocation(line: 92, column: 7, scope: !899)
!899 = !DILexicalBlockFile(scope: !879, file: !48, discriminator: 3)
!900 = !DILocation(line: 97, column: 20, scope: !901)
!901 = distinct !DILexicalBlock(scope: !902, file: !48, line: 97, column: 13)
!902 = distinct !DILexicalBlock(scope: !879, file: !48, line: 93, column: 9)
!903 = !DILocation(line: 97, column: 76, scope: !901)
!904 = !DILocation(line: 97, column: 13, scope: !901)
!905 = !DILocation(line: 97, column: 88, scope: !901)
!906 = !DILocation(line: 97, column: 93, scope: !901)
!907 = !DILocation(line: 98, column: 20, scope: !901)
!908 = !DILocation(line: 98, column: 13, scope: !901)
!909 = !DILocation(line: 98, column: 89, scope: !901)
!910 = !DILocation(line: 98, column: 94, scope: !901)
!911 = !DILocation(line: 99, column: 20, scope: !901)
!912 = !DILocation(line: 99, column: 13, scope: !901)
!913 = !DILocation(line: 99, column: 87, scope: !901)
!914 = !DILocation(line: 97, column: 13, scope: !915)
!915 = !DILexicalBlockFile(scope: !902, file: !48, discriminator: 1)
!916 = !DILocation(line: 101, column: 13, scope: !917)
!917 = distinct !DILexicalBlock(scope: !901, file: !48, line: 100, column: 12)
!918 = !DILocation(line: 102, column: 23, scope: !917)
!919 = !DILocation(line: 103, column: 12, scope: !917)
!920 = !DILocation(line: 92, column: 7, scope: !921)
!921 = !DILexicalBlockFile(scope: !879, file: !48, discriminator: 4)
!922 = distinct !{!922, !890}
!923 = !DILocation(line: 105, column: 10, scope: !924)
!924 = distinct !DILexicalBlock(scope: !879, file: !48, line: 105, column: 10)
!925 = !DILocation(line: 105, column: 20, scope: !924)
!926 = !DILocation(line: 105, column: 10, scope: !879)
!927 = !DILocation(line: 107, column: 20, scope: !928)
!928 = distinct !DILexicalBlock(scope: !929, file: !48, line: 107, column: 13)
!929 = distinct !DILexicalBlock(scope: !924, file: !48, line: 106, column: 9)
!930 = !DILocation(line: 107, column: 13, scope: !928)
!931 = !DILocation(line: 107, column: 32, scope: !928)
!932 = !DILocation(line: 107, column: 13, scope: !929)
!933 = !DILocation(line: 109, column: 16, scope: !934)
!934 = distinct !DILexicalBlock(scope: !935, file: !48, line: 109, column: 16)
!935 = distinct !DILexicalBlock(scope: !928, file: !48, line: 108, column: 12)
!936 = !DILocation(line: 109, column: 33, scope: !934)
!937 = !DILocation(line: 109, column: 16, scope: !935)
!938 = !DILocation(line: 111, column: 19, scope: !939)
!939 = distinct !DILexicalBlock(scope: !940, file: !48, line: 111, column: 19)
!940 = distinct !DILexicalBlock(scope: !934, file: !48, line: 110, column: 15)
!941 = !DILocation(line: 111, column: 35, scope: !939)
!942 = !DILocation(line: 111, column: 19, scope: !940)
!943 = !DILocation(line: 113, column: 30, scope: !944)
!944 = distinct !DILexicalBlock(scope: !945, file: !48, line: 113, column: 22)
!945 = distinct !DILexicalBlock(scope: !939, file: !48, line: 112, column: 18)
!946 = !DILocation(line: 113, column: 22, scope: !944)
!947 = !DILocation(line: 113, column: 86, scope: !944)
!948 = !DILocation(line: 113, column: 22, scope: !945)
!949 = !DILocalVariable(name: "hostname_start_ptr", scope: !950, file: !48, line: 115, type: !18)
!950 = distinct !DILexicalBlock(scope: !944, file: !48, line: 114, column: 21)
!951 = !DILocation(line: 115, column: 28, scope: !950)
!952 = !DILocalVariable(name: "hostname_end_ptr", scope: !950, file: !48, line: 115, type: !18)
!953 = !DILocation(line: 115, column: 49, scope: !950)
!954 = !DILocalVariable(name: "path_start_prt", scope: !950, file: !48, line: 115, type: !18)
!955 = !DILocation(line: 115, column: 68, scope: !950)
!956 = !DILocalVariable(name: "server_name_len", scope: !950, file: !48, line: 116, type: !311)
!957 = !DILocation(line: 116, column: 29, scope: !950)
!958 = !DILocation(line: 120, column: 48, scope: !950)
!959 = !DILocation(line: 120, column: 58, scope: !950)
!960 = !DILocation(line: 120, column: 41, scope: !950)
!961 = !DILocation(line: 120, column: 40, scope: !950)
!962 = !DILocation(line: 121, column: 25, scope: !963)
!963 = distinct !DILexicalBlock(scope: !950, file: !48, line: 121, column: 25)
!964 = !DILocation(line: 121, column: 44, scope: !963)
!965 = !DILocation(line: 121, column: 25, scope: !950)
!966 = !DILocation(line: 122, column: 44, scope: !963)
!967 = !DILocation(line: 122, column: 54, scope: !963)
!968 = !DILocation(line: 122, column: 43, scope: !963)
!969 = !DILocation(line: 122, column: 25, scope: !963)
!970 = !DILocation(line: 124, column: 43, scope: !963)
!971 = !DILocation(line: 127, column: 46, scope: !950)
!972 = !DILocation(line: 127, column: 39, scope: !950)
!973 = !DILocation(line: 127, column: 38, scope: !950)
!974 = !DILocation(line: 128, column: 25, scope: !975)
!975 = distinct !DILexicalBlock(scope: !950, file: !48, line: 128, column: 25)
!976 = !DILocation(line: 128, column: 42, scope: !975)
!977 = !DILocation(line: 128, column: 25, scope: !950)
!978 = !DILocation(line: 130, column: 36, scope: !979)
!979 = distinct !DILexicalBlock(scope: !975, file: !48, line: 129, column: 24)
!980 = !DILocation(line: 132, column: 49, scope: !979)
!981 = !DILocation(line: 132, column: 42, scope: !979)
!982 = !DILocation(line: 132, column: 41, scope: !979)
!983 = !DILocation(line: 133, column: 28, scope: !984)
!984 = distinct !DILexicalBlock(scope: !979, file: !48, line: 133, column: 28)
!985 = !DILocation(line: 133, column: 45, scope: !984)
!986 = !DILocation(line: 133, column: 28, scope: !979)
!987 = !DILocation(line: 134, column: 45, scope: !984)
!988 = !DILocation(line: 134, column: 71, scope: !984)
!989 = !DILocation(line: 134, column: 64, scope: !984)
!990 = !DILocation(line: 134, column: 63, scope: !984)
!991 = !DILocation(line: 134, column: 44, scope: !984)
!992 = !DILocation(line: 134, column: 28, scope: !984)
!993 = !DILocation(line: 135, column: 24, scope: !979)
!994 = !DILocation(line: 138, column: 35, scope: !995)
!995 = distinct !DILexicalBlock(scope: !996, file: !48, line: 138, column: 28)
!996 = distinct !DILexicalBlock(scope: !975, file: !48, line: 137, column: 24)
!997 = !DILocation(line: 138, column: 51, scope: !995)
!998 = !DILocation(line: 138, column: 28, scope: !995)
!999 = !DILocation(line: 138, column: 73, scope: !995)
!1000 = !DILocation(line: 138, column: 28, scope: !996)
!1001 = !DILocation(line: 139, column: 39, scope: !995)
!1002 = !DILocation(line: 139, column: 28, scope: !995)
!1003 = !DILocation(line: 143, column: 44, scope: !950)
!1004 = !DILocation(line: 143, column: 37, scope: !950)
!1005 = !DILocation(line: 143, column: 36, scope: !950)
!1006 = !DILocation(line: 144, column: 25, scope: !1007)
!1007 = distinct !DILexicalBlock(scope: !950, file: !48, line: 144, column: 25)
!1008 = !DILocation(line: 144, column: 40, scope: !1007)
!1009 = !DILocation(line: 144, column: 25, scope: !950)
!1010 = !DILocalVariable(name: "path_len", scope: !1011, file: !48, line: 146, type: !311)
!1011 = distinct !DILexicalBlock(scope: !1007, file: !48, line: 145, column: 24)
!1012 = !DILocation(line: 146, column: 32, scope: !1011)
!1013 = !DILocation(line: 148, column: 43, scope: !1011)
!1014 = !DILocation(line: 148, column: 36, scope: !1011)
!1015 = !DILocation(line: 148, column: 34, scope: !1011)
!1016 = !DILocation(line: 149, column: 28, scope: !1017)
!1017 = distinct !DILexicalBlock(scope: !1011, file: !48, line: 149, column: 28)
!1018 = !DILocation(line: 149, column: 37, scope: !1017)
!1019 = !DILocation(line: 149, column: 28, scope: !1011)
!1020 = !DILocation(line: 151, column: 48, scope: !1021)
!1021 = distinct !DILexicalBlock(scope: !1017, file: !48, line: 150, column: 27)
!1022 = !DILocation(line: 151, column: 64, scope: !1021)
!1023 = !DILocation(line: 151, column: 28, scope: !1021)
!1024 = !DILocation(line: 152, column: 40, scope: !1021)
!1025 = !DILocation(line: 152, column: 28, scope: !1021)
!1026 = !DILocation(line: 152, column: 49, scope: !1021)
!1027 = !DILocation(line: 153, column: 27, scope: !1021)
!1028 = !DILocation(line: 154, column: 24, scope: !1011)
!1029 = !DILocation(line: 156, column: 38, scope: !950)
!1030 = !DILocation(line: 156, column: 55, scope: !950)
!1031 = !DILocation(line: 156, column: 54, scope: !950)
!1032 = !DILocation(line: 156, column: 37, scope: !950)
!1033 = !DILocation(line: 157, column: 25, scope: !1034)
!1034 = distinct !DILexicalBlock(scope: !950, file: !48, line: 157, column: 25)
!1035 = !DILocation(line: 157, column: 41, scope: !1034)
!1036 = !DILocation(line: 157, column: 25, scope: !950)
!1037 = !DILocation(line: 159, column: 45, scope: !1038)
!1038 = distinct !DILexicalBlock(scope: !1034, file: !48, line: 158, column: 24)
!1039 = !DILocation(line: 159, column: 65, scope: !1038)
!1040 = !DILocation(line: 159, column: 25, scope: !1038)
!1041 = !DILocation(line: 160, column: 37, scope: !1038)
!1042 = !DILocation(line: 160, column: 25, scope: !1038)
!1043 = !DILocation(line: 160, column: 53, scope: !1038)
!1044 = !DILocation(line: 163, column: 35, scope: !1038)
!1045 = !DILocation(line: 163, column: 34, scope: !1038)
!1046 = !DILocation(line: 164, column: 28, scope: !1047)
!1047 = distinct !DILexicalBlock(scope: !1038, file: !48, line: 164, column: 28)
!1048 = !DILocation(line: 164, column: 37, scope: !1047)
!1049 = !DILocation(line: 164, column: 28, scope: !1038)
!1050 = !DILocation(line: 166, column: 28, scope: !1051)
!1051 = distinct !DILexicalBlock(scope: !1047, file: !48, line: 165, column: 27)
!1052 = !DILocation(line: 166, column: 28, scope: !1053)
!1053 = !DILexicalBlockFile(scope: !1051, file: !48, discriminator: 1)
!1054 = !DILocation(line: 167, column: 27, scope: !1051)
!1055 = !DILocation(line: 168, column: 24, scope: !1038)
!1056 = !DILocation(line: 171, column: 25, scope: !1057)
!1057 = distinct !DILexicalBlock(scope: !1034, file: !48, line: 170, column: 24)
!1058 = !DILocation(line: 172, column: 35, scope: !1057)
!1059 = !DILocation(line: 174, column: 21, scope: !950)
!1060 = !DILocation(line: 177, column: 22, scope: !1061)
!1061 = distinct !DILexicalBlock(scope: !944, file: !48, line: 176, column: 21)
!1062 = !DILocation(line: 178, column: 32, scope: !1061)
!1063 = !DILocation(line: 180, column: 18, scope: !945)
!1064 = !DILocation(line: 183, column: 19, scope: !1065)
!1065 = distinct !DILexicalBlock(scope: !939, file: !48, line: 182, column: 18)
!1066 = !DILocation(line: 184, column: 29, scope: !1065)
!1067 = !DILocation(line: 186, column: 15, scope: !940)
!1068 = !DILocation(line: 189, column: 16, scope: !1069)
!1069 = distinct !DILexicalBlock(scope: !934, file: !48, line: 188, column: 15)
!1070 = !DILocation(line: 190, column: 26, scope: !1069)
!1071 = !DILocation(line: 192, column: 12, scope: !935)
!1072 = !DILocation(line: 195, column: 13, scope: !1073)
!1073 = distinct !DILexicalBlock(scope: !928, file: !48, line: 194, column: 12)
!1074 = !DILocation(line: 196, column: 23, scope: !1073)
!1075 = !DILocation(line: 198, column: 9, scope: !929)
!1076 = !DILocation(line: 199, column: 14, scope: !879)
!1077 = !DILocation(line: 199, column: 7, scope: !879)
!1078 = !DILocation(line: 200, column: 6, scope: !879)
!1079 = !DILocation(line: 203, column: 17, scope: !1080)
!1080 = distinct !DILexicalBlock(scope: !875, file: !48, line: 202, column: 6)
!1081 = !DILocation(line: 203, column: 16, scope: !1080)
!1082 = !DILocation(line: 204, column: 7, scope: !1080)
!1083 = !DILocation(line: 204, column: 7, scope: !1084)
!1084 = !DILexicalBlockFile(scope: !1080, file: !48, discriminator: 1)
!1085 = !DILocation(line: 207, column: 11, scope: !775)
!1086 = !DILocation(line: 207, column: 4, scope: !775)
!1087 = !DILocation(line: 208, column: 3, scope: !775)
!1088 = distinct !DISubprogram(name: "send_notification", scope: !48, file: !48, line: 210, type: !549, isLocal: false, isDefinition: true, scopeLine: 211, flags: DIFlagPrototyped, isOptimized: false, unit: !47, variables: !2)
!1089 = !DILocalVariable(name: "msg_str", arg: 1, scope: !1088, file: !48, line: 210, type: !18)
!1090 = !DILocation(line: 210, column: 29, scope: !1088)
!1091 = !DILocalVariable(name: "msg_priority", arg: 2, scope: !1088, file: !48, line: 210, type: !18)
!1092 = !DILocation(line: 210, column: 44, scope: !1088)
!1093 = !DILocalVariable(name: "ret_error", scope: !1088, file: !48, line: 212, type: !12)
!1094 = !DILocation(line: 212, column: 8, scope: !1088)
!1095 = !DILocalVariable(name: "socket_fd", scope: !1088, file: !48, line: 213, type: !12)
!1096 = !DILocation(line: 213, column: 8, scope: !1088)
!1097 = !DILocalVariable(name: "server_addr", scope: !1088, file: !48, line: 214, type: !1098)
!1098 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "sockaddr_in", file: !88, line: 239, size: 128, align: 32, elements: !1099)
!1099 = !{!1100, !1101, !1102, !1103}
!1100 = !DIDerivedType(tag: DW_TAG_member, name: "sin_family", scope: !1098, file: !88, line: 241, baseType: !68, size: 16, align: 16)
!1101 = !DIDerivedType(tag: DW_TAG_member, name: "sin_port", scope: !1098, file: !88, line: 242, baseType: !219, size: 16, align: 16, offset: 16)
!1102 = !DIDerivedType(tag: DW_TAG_member, name: "sin_addr", scope: !1098, file: !88, line: 243, baseType: !87, size: 32, align: 32, offset: 32)
!1103 = !DIDerivedType(tag: DW_TAG_member, name: "sin_zero", scope: !1098, file: !88, line: 246, baseType: !226, size: 64, align: 8, offset: 64)
!1104 = !DILocation(line: 214, column: 23, scope: !1088)
!1105 = !DILocation(line: 217, column: 16, scope: !1088)
!1106 = !DILocation(line: 217, column: 14, scope: !1088)
!1107 = !DILocation(line: 218, column: 8, scope: !1108)
!1108 = distinct !DILexicalBlock(scope: !1088, file: !48, line: 218, column: 8)
!1109 = !DILocation(line: 218, column: 18, scope: !1108)
!1110 = !DILocation(line: 218, column: 8, scope: !1088)
!1111 = !DILocation(line: 221, column: 7, scope: !1112)
!1112 = distinct !DILexicalBlock(scope: !1108, file: !48, line: 219, column: 6)
!1113 = !DILocation(line: 222, column: 19, scope: !1112)
!1114 = !DILocation(line: 222, column: 30, scope: !1112)
!1115 = !DILocation(line: 223, column: 36, scope: !1112)
!1116 = !DILocation(line: 223, column: 30, scope: !1112)
!1117 = !DILocation(line: 223, column: 19, scope: !1112)
!1118 = !DILocation(line: 223, column: 28, scope: !1112)
!1119 = !DILocation(line: 224, column: 19, scope: !1112)
!1120 = !DILocation(line: 224, column: 30, scope: !1112)
!1121 = !DILocation(line: 227, column: 25, scope: !1112)
!1122 = !DILocation(line: 227, column: 36, scope: !1112)
!1123 = !DILocation(line: 227, column: 17, scope: !1112)
!1124 = !DILocation(line: 227, column: 16, scope: !1112)
!1125 = !DILocation(line: 228, column: 10, scope: !1126)
!1126 = distinct !DILexicalBlock(scope: !1112, file: !48, line: 228, column: 10)
!1127 = !DILocation(line: 228, column: 20, scope: !1126)
!1128 = !DILocation(line: 228, column: 10, scope: !1112)
!1129 = !DILocalVariable(name: "socket_file", scope: !1130, file: !48, line: 230, type: !781)
!1130 = distinct !DILexicalBlock(scope: !1126, file: !48, line: 229, column: 9)
!1131 = !DILocation(line: 230, column: 16, scope: !1130)
!1132 = !DILocation(line: 231, column: 31, scope: !1130)
!1133 = !DILocation(line: 231, column: 24, scope: !1130)
!1134 = !DILocation(line: 231, column: 22, scope: !1130)
!1135 = !DILocation(line: 232, column: 13, scope: !1136)
!1136 = distinct !DILexicalBlock(scope: !1130, file: !48, line: 232, column: 13)
!1137 = !DILocation(line: 232, column: 25, scope: !1136)
!1138 = !DILocation(line: 232, column: 13, scope: !1130)
!1139 = !DILocalVariable(name: "body_len", scope: !1140, file: !48, line: 234, type: !311)
!1140 = distinct !DILexicalBlock(scope: !1136, file: !48, line: 233, column: 12)
!1141 = !DILocation(line: 234, column: 20, scope: !1140)
!1142 = !DILocalVariable(name: "http_error", scope: !1140, file: !48, line: 235, type: !94)
!1143 = !DILocation(line: 235, column: 26, scope: !1140)
!1144 = !DILocalVariable(name: "fscanf_ret", scope: !1140, file: !48, line: 236, type: !12)
!1145 = !DILocation(line: 236, column: 17, scope: !1140)
!1146 = !DILocation(line: 238, column: 41, scope: !1140)
!1147 = !DILocation(line: 238, column: 40, scope: !1140)
!1148 = !DILocation(line: 238, column: 58, scope: !1140)
!1149 = !DILocation(line: 238, column: 61, scope: !1140)
!1150 = !DILocation(line: 238, column: 78, scope: !1151)
!1151 = !DILexicalBlockFile(scope: !1140, file: !48, discriminator: 1)
!1152 = !DILocation(line: 238, column: 77, scope: !1140)
!1153 = !DILocation(line: 238, column: 94, scope: !1140)
!1154 = !DILocation(line: 238, column: 97, scope: !1140)
!1155 = !DILocation(line: 238, column: 124, scope: !1140)
!1156 = !DILocation(line: 238, column: 117, scope: !1157)
!1157 = !DILexicalBlockFile(scope: !1140, file: !48, discriminator: 2)
!1158 = !DILocation(line: 238, column: 116, scope: !1140)
!1159 = !DILocation(line: 238, column: 133, scope: !1140)
!1160 = !DILocation(line: 238, column: 136, scope: !1140)
!1161 = !DILocation(line: 238, column: 164, scope: !1140)
!1162 = !DILocation(line: 238, column: 157, scope: !1163)
!1163 = !DILexicalBlockFile(scope: !1140, file: !48, discriminator: 3)
!1164 = !DILocation(line: 238, column: 156, scope: !1140)
!1165 = !DILocation(line: 238, column: 22, scope: !1140)
!1166 = !DILocation(line: 240, column: 23, scope: !1167)
!1167 = distinct !DILexicalBlock(scope: !1140, file: !48, line: 240, column: 16)
!1168 = !DILocation(line: 240, column: 16, scope: !1167)
!1169 = !DILocation(line: 240, column: 41, scope: !1167)
!1170 = !DILocation(line: 240, column: 16, scope: !1140)
!1171 = !DILocation(line: 241, column: 25, scope: !1167)
!1172 = !DILocation(line: 241, column: 16, scope: !1167)
!1173 = !DILocation(line: 244, column: 21, scope: !1140)
!1174 = !DILocation(line: 244, column: 13, scope: !1140)
!1175 = !DILocation(line: 245, column: 21, scope: !1140)
!1176 = !DILocation(line: 245, column: 13, scope: !1140)
!1177 = !DILocation(line: 246, column: 21, scope: !1140)
!1178 = !DILocation(line: 246, column: 13, scope: !1140)
!1179 = !DILocation(line: 247, column: 21, scope: !1140)
!1180 = !DILocation(line: 247, column: 84, scope: !1140)
!1181 = !DILocation(line: 247, column: 13, scope: !1140)
!1182 = !DILocation(line: 248, column: 21, scope: !1140)
!1183 = !DILocation(line: 248, column: 110, scope: !1140)
!1184 = !DILocation(line: 248, column: 119, scope: !1140)
!1185 = !DILocation(line: 248, column: 13, scope: !1140)
!1186 = !DILocation(line: 249, column: 23, scope: !1187)
!1187 = distinct !DILexicalBlock(scope: !1140, file: !48, line: 249, column: 16)
!1188 = !DILocation(line: 249, column: 16, scope: !1187)
!1189 = !DILocation(line: 249, column: 41, scope: !1187)
!1190 = !DILocation(line: 249, column: 16, scope: !1140)
!1191 = !DILocation(line: 250, column: 24, scope: !1187)
!1192 = !DILocation(line: 250, column: 16, scope: !1187)
!1193 = !DILocation(line: 253, column: 31, scope: !1140)
!1194 = !DILocation(line: 253, column: 24, scope: !1140)
!1195 = !DILocation(line: 253, column: 23, scope: !1140)
!1196 = !DILocation(line: 254, column: 16, scope: !1197)
!1197 = distinct !DILexicalBlock(scope: !1140, file: !48, line: 254, column: 16)
!1198 = !DILocation(line: 254, column: 27, scope: !1197)
!1199 = !DILocation(line: 254, column: 16, scope: !1140)
!1200 = !DILocation(line: 256, column: 19, scope: !1201)
!1201 = distinct !DILexicalBlock(scope: !1202, file: !48, line: 256, column: 19)
!1202 = distinct !DILexicalBlock(scope: !1197, file: !48, line: 255, column: 15)
!1203 = !DILocation(line: 256, column: 30, scope: !1201)
!1204 = !DILocation(line: 256, column: 19, scope: !1202)
!1205 = !DILocalVariable(name: "http_str", scope: !1206, file: !48, line: 258, type: !880)
!1206 = distinct !DILexicalBlock(scope: !1201, file: !48, line: 257, column: 18)
!1207 = !DILocation(line: 258, column: 24, scope: !1206)
!1208 = !DILocalVariable(name: "header_line", scope: !1206, file: !48, line: 259, type: !18)
!1209 = !DILocation(line: 259, column: 25, scope: !1206)
!1210 = !DILocalVariable(name: "header_line_ind", scope: !1206, file: !48, line: 260, type: !94)
!1211 = !DILocation(line: 260, column: 32, scope: !1206)
!1212 = !DILocalVariable(name: "header_abort", scope: !1206, file: !48, line: 261, type: !12)
!1213 = !DILocation(line: 261, column: 23, scope: !1206)
!1214 = !DILocation(line: 264, column: 31, scope: !1206)
!1215 = !DILocation(line: 265, column: 34, scope: !1206)
!1216 = !DILocation(line: 266, column: 19, scope: !1206)
!1217 = !DILocation(line: 266, column: 44, scope: !1218)
!1218 = !DILexicalBlockFile(scope: !1206, file: !48, discriminator: 1)
!1219 = !DILocation(line: 266, column: 67, scope: !1218)
!1220 = !DILocation(line: 266, column: 38, scope: !1218)
!1221 = !DILocation(line: 266, column: 37, scope: !1218)
!1222 = !DILocation(line: 266, column: 81, scope: !1218)
!1223 = !DILocation(line: 266, column: 19, scope: !1218)
!1224 = !DILocation(line: 268, column: 25, scope: !1225)
!1225 = distinct !DILexicalBlock(scope: !1226, file: !48, line: 268, column: 25)
!1226 = distinct !DILexicalBlock(scope: !1206, file: !48, line: 267, column: 21)
!1227 = !DILocation(line: 268, column: 37, scope: !1225)
!1228 = !DILocation(line: 268, column: 25, scope: !1226)
!1229 = !DILocation(line: 269, column: 25, scope: !1225)
!1230 = !DILocation(line: 271, column: 37, scope: !1226)
!1231 = !DILocation(line: 272, column: 25, scope: !1232)
!1232 = distinct !DILexicalBlock(scope: !1226, file: !48, line: 272, column: 25)
!1233 = !DILocation(line: 272, column: 41, scope: !1232)
!1234 = !DILocation(line: 272, column: 25, scope: !1226)
!1235 = !DILocation(line: 274, column: 36, scope: !1236)
!1236 = distinct !DILexicalBlock(scope: !1232, file: !48, line: 273, column: 24)
!1237 = !DILocation(line: 275, column: 37, scope: !1236)
!1238 = !DILocation(line: 276, column: 25, scope: !1236)
!1239 = !DILocation(line: 266, column: 19, scope: !1240)
!1240 = !DILexicalBlockFile(scope: !1206, file: !48, discriminator: 2)
!1241 = distinct !{!1241, !1216}
!1242 = !DILocation(line: 280, column: 22, scope: !1243)
!1243 = distinct !DILexicalBlock(scope: !1206, file: !48, line: 280, column: 22)
!1244 = !DILocation(line: 280, column: 34, scope: !1243)
!1245 = !DILocation(line: 280, column: 22, scope: !1206)
!1246 = !DILocalVariable(name: "notif_state", scope: !1247, file: !48, line: 282, type: !12)
!1247 = distinct !DILexicalBlock(scope: !1243, file: !48, line: 281, column: 21)
!1248 = !DILocation(line: 282, column: 26, scope: !1247)
!1249 = !DILocalVariable(name: "variables_obtined", scope: !1247, file: !48, line: 283, type: !12)
!1250 = !DILocation(line: 283, column: 26, scope: !1247)
!1251 = !DILocalVariable(name: "var_name", scope: !1247, file: !48, line: 284, type: !880)
!1252 = !DILocation(line: 284, column: 27, scope: !1247)
!1253 = !DILocalVariable(name: "var_value", scope: !1247, file: !48, line: 284, type: !880)
!1254 = !DILocation(line: 284, column: 52, scope: !1247)
!1255 = !DILocation(line: 287, column: 29, scope: !1247)
!1256 = !DILocation(line: 287, column: 22, scope: !1247)
!1257 = !DILocation(line: 288, column: 39, scope: !1247)
!1258 = !DILocation(line: 289, column: 22, scope: !1247)
!1259 = !DILocation(line: 289, column: 35, scope: !1260)
!1260 = !DILexicalBlockFile(scope: !1247, file: !48, discriminator: 1)
!1261 = !DILocation(line: 289, column: 66, scope: !1260)
!1262 = !DILocation(line: 289, column: 28, scope: !1260)
!1263 = !DILocation(line: 289, column: 76, scope: !1260)
!1264 = !DILocation(line: 289, column: 22, scope: !1260)
!1265 = !DILocation(line: 291, column: 32, scope: !1266)
!1266 = distinct !DILexicalBlock(scope: !1247, file: !48, line: 290, column: 24)
!1267 = !DILocation(line: 291, column: 25, scope: !1266)
!1268 = !DILocation(line: 292, column: 35, scope: !1269)
!1269 = distinct !DILexicalBlock(scope: !1266, file: !48, line: 292, column: 28)
!1270 = !DILocation(line: 292, column: 63, scope: !1269)
!1271 = !DILocation(line: 292, column: 28, scope: !1269)
!1272 = !DILocation(line: 292, column: 74, scope: !1269)
!1273 = !DILocation(line: 292, column: 28, scope: !1266)
!1274 = !DILocation(line: 294, column: 35, scope: !1275)
!1275 = distinct !DILexicalBlock(scope: !1269, file: !48, line: 293, column: 27)
!1276 = !DILocation(line: 294, column: 28, scope: !1275)
!1277 = !DILocation(line: 295, column: 35, scope: !1275)
!1278 = !DILocation(line: 295, column: 28, scope: !1275)
!1279 = !DILocation(line: 297, column: 38, scope: !1280)
!1280 = distinct !DILexicalBlock(scope: !1275, file: !48, line: 297, column: 31)
!1281 = !DILocation(line: 297, column: 31, scope: !1280)
!1282 = !DILocation(line: 297, column: 57, scope: !1280)
!1283 = !DILocation(line: 297, column: 31, scope: !1275)
!1284 = !DILocation(line: 299, column: 48, scope: !1285)
!1285 = distinct !DILexicalBlock(scope: !1280, file: !48, line: 298, column: 30)
!1286 = !DILocation(line: 299, column: 43, scope: !1285)
!1287 = !DILocation(line: 299, column: 42, scope: !1285)
!1288 = !DILocation(line: 300, column: 48, scope: !1285)
!1289 = !DILocation(line: 301, column: 30, scope: !1285)
!1290 = !DILocation(line: 302, column: 27, scope: !1275)
!1291 = !DILocation(line: 289, column: 22, scope: !1292)
!1292 = !DILexicalBlockFile(scope: !1247, file: !48, discriminator: 2)
!1293 = distinct !{!1293, !1258}
!1294 = !DILocation(line: 304, column: 29, scope: !1247)
!1295 = !DILocation(line: 304, column: 22, scope: !1247)
!1296 = !DILocation(line: 306, column: 25, scope: !1297)
!1297 = distinct !DILexicalBlock(scope: !1247, file: !48, line: 306, column: 25)
!1298 = !DILocation(line: 306, column: 43, scope: !1297)
!1299 = !DILocation(line: 306, column: 25, scope: !1247)
!1300 = !DILocation(line: 308, column: 28, scope: !1301)
!1301 = distinct !DILexicalBlock(scope: !1302, file: !48, line: 308, column: 28)
!1302 = distinct !DILexicalBlock(scope: !1297, file: !48, line: 307, column: 24)
!1303 = !DILocation(line: 308, column: 40, scope: !1301)
!1304 = !DILocation(line: 308, column: 28, scope: !1302)
!1305 = !DILocation(line: 310, column: 37, scope: !1306)
!1306 = distinct !DILexicalBlock(scope: !1301, file: !48, line: 309, column: 27)
!1307 = !DILocation(line: 311, column: 27, scope: !1306)
!1308 = !DILocation(line: 314, column: 37, scope: !1309)
!1309 = distinct !DILexicalBlock(scope: !1301, file: !48, line: 313, column: 27)
!1310 = !DILocation(line: 315, column: 28, scope: !1309)
!1311 = !DILocation(line: 317, column: 24, scope: !1302)
!1312 = !DILocation(line: 320, column: 34, scope: !1313)
!1313 = distinct !DILexicalBlock(scope: !1297, file: !48, line: 319, column: 24)
!1314 = !DILocation(line: 321, column: 25, scope: !1313)
!1315 = !DILocation(line: 323, column: 21, scope: !1247)
!1316 = !DILocation(line: 326, column: 25, scope: !1317)
!1317 = distinct !DILexicalBlock(scope: !1318, file: !48, line: 326, column: 25)
!1318 = distinct !DILexicalBlock(scope: !1243, file: !48, line: 325, column: 21)
!1319 = !DILocation(line: 326, column: 38, scope: !1317)
!1320 = !DILocation(line: 326, column: 25, scope: !1318)
!1321 = !DILocation(line: 328, column: 34, scope: !1322)
!1322 = distinct !DILexicalBlock(scope: !1317, file: !48, line: 327, column: 24)
!1323 = !DILocation(line: 329, column: 25, scope: !1322)
!1324 = !DILocation(line: 330, column: 24, scope: !1322)
!1325 = !DILocation(line: 333, column: 34, scope: !1326)
!1326 = distinct !DILexicalBlock(scope: !1317, file: !48, line: 332, column: 24)
!1327 = !DILocation(line: 334, column: 25, scope: !1326)
!1328 = !DILocation(line: 334, column: 25, scope: !1329)
!1329 = !DILexicalBlockFile(scope: !1326, file: !48, discriminator: 1)
!1330 = !DILocation(line: 337, column: 18, scope: !1206)
!1331 = !DILocation(line: 340, column: 28, scope: !1332)
!1332 = distinct !DILexicalBlock(scope: !1201, file: !48, line: 339, column: 18)
!1333 = !DILocation(line: 341, column: 19, scope: !1332)
!1334 = !DILocation(line: 343, column: 15, scope: !1202)
!1335 = !DILocation(line: 346, column: 26, scope: !1336)
!1336 = distinct !DILexicalBlock(scope: !1197, file: !48, line: 345, column: 15)
!1337 = !DILocation(line: 346, column: 25, scope: !1336)
!1338 = !DILocation(line: 347, column: 16, scope: !1336)
!1339 = !DILocation(line: 347, column: 16, scope: !1340)
!1340 = !DILexicalBlockFile(scope: !1336, file: !48, discriminator: 1)
!1341 = !DILocation(line: 349, column: 20, scope: !1140)
!1342 = !DILocation(line: 349, column: 13, scope: !1140)
!1343 = !DILocation(line: 350, column: 12, scope: !1140)
!1344 = !DILocation(line: 353, column: 13, scope: !1345)
!1345 = distinct !DILexicalBlock(scope: !1136, file: !48, line: 352, column: 12)
!1346 = !DILocation(line: 353, column: 13, scope: !1347)
!1347 = !DILexicalBlockFile(scope: !1345, file: !48, discriminator: 1)
!1348 = !DILocation(line: 353, column: 13, scope: !1349)
!1349 = !DILexicalBlockFile(scope: !1345, file: !48, discriminator: 2)
!1350 = !DILocation(line: 353, column: 13, scope: !1351)
!1351 = !DILexicalBlockFile(scope: !1345, file: !48, discriminator: 3)
!1352 = !DILocation(line: 354, column: 19, scope: !1345)
!1353 = !DILocation(line: 354, column: 13, scope: !1345)
!1354 = !DILocation(line: 356, column: 9, scope: !1130)
!1355 = !DILocation(line: 359, column: 20, scope: !1356)
!1356 = distinct !DILexicalBlock(scope: !1126, file: !48, line: 358, column: 9)
!1357 = !DILocation(line: 359, column: 19, scope: !1356)
!1358 = !DILocation(line: 360, column: 10, scope: !1356)
!1359 = !DILocation(line: 360, column: 10, scope: !1360)
!1360 = !DILexicalBlockFile(scope: !1356, file: !48, discriminator: 1)
!1361 = !DILocation(line: 360, column: 10, scope: !1362)
!1362 = !DILexicalBlockFile(scope: !1356, file: !48, discriminator: 2)
!1363 = !DILocation(line: 360, column: 10, scope: !1364)
!1364 = !DILexicalBlockFile(scope: !1356, file: !48, discriminator: 3)
!1365 = !DILocation(line: 361, column: 16, scope: !1356)
!1366 = !DILocation(line: 361, column: 10, scope: !1356)
!1367 = !DILocation(line: 363, column: 6, scope: !1112)
!1368 = !DILocation(line: 366, column: 17, scope: !1369)
!1369 = distinct !DILexicalBlock(scope: !1108, file: !48, line: 365, column: 6)
!1370 = !DILocation(line: 366, column: 16, scope: !1369)
!1371 = !DILocation(line: 367, column: 7, scope: !1369)
!1372 = !DILocation(line: 367, column: 7, scope: !1373)
!1373 = !DILexicalBlockFile(scope: !1369, file: !48, discriminator: 1)
!1374 = !DILocation(line: 369, column: 11, scope: !1088)
!1375 = !DILocation(line: 369, column: 4, scope: !1088)
!1376 = distinct !DISubprogram(name: "herror_msg", scope: !97, file: !97, line: 23, type: !1377, isLocal: false, isDefinition: true, scopeLine: 24, flags: DIFlagPrototyped, isOptimized: false, unit: !96, variables: !2)
!1377 = !DISubroutineType(types: !1378)
!1378 = !{!18, !12}
!1379 = !DILocalVariable(name: "herror_cod", arg: 1, scope: !1376, file: !97, line: 23, type: !12)
!1380 = !DILocation(line: 23, column: 22, scope: !1376)
!1381 = !DILocalVariable(name: "error_str", scope: !1376, file: !97, line: 25, type: !18)
!1382 = !DILocation(line: 25, column: 10, scope: !1376)
!1383 = !DILocation(line: 26, column: 11, scope: !1376)
!1384 = !DILocation(line: 26, column: 4, scope: !1376)
!1385 = !DILocation(line: 29, column: 19, scope: !1386)
!1386 = distinct !DILexicalBlock(scope: !1376, file: !97, line: 27, column: 6)
!1387 = !DILocation(line: 30, column: 10, scope: !1386)
!1388 = !DILocation(line: 32, column: 19, scope: !1386)
!1389 = !DILocation(line: 33, column: 10, scope: !1386)
!1390 = !DILocation(line: 35, column: 19, scope: !1386)
!1391 = !DILocation(line: 36, column: 10, scope: !1386)
!1392 = !DILocation(line: 38, column: 19, scope: !1386)
!1393 = !DILocation(line: 39, column: 10, scope: !1386)
!1394 = !DILocation(line: 41, column: 11, scope: !1376)
!1395 = !DILocation(line: 41, column: 4, scope: !1376)
!1396 = distinct !DISubprogram(name: "resp_code_msg", scope: !97, file: !97, line: 47, type: !1397, isLocal: false, isDefinition: true, scopeLine: 48, flags: DIFlagPrototyped, isOptimized: false, unit: !96, variables: !2)
!1397 = !DISubroutineType(types: !1398)
!1398 = !{!18, !1399}
!1399 = !DIDerivedType(tag: DW_TAG_typedef, name: "ns_rcode", file: !100, line: 210, baseType: !99)
!1400 = !DILocalVariable(name: "rcode", arg: 1, scope: !1396, file: !97, line: 47, type: !1399)
!1401 = !DILocation(line: 47, column: 30, scope: !1396)
!1402 = !DILocalVariable(name: "code_str", scope: !1396, file: !97, line: 49, type: !18)
!1403 = !DILocation(line: 49, column: 10, scope: !1396)
!1404 = !DILocation(line: 50, column: 11, scope: !1396)
!1405 = !DILocation(line: 50, column: 4, scope: !1396)
!1406 = !DILocation(line: 53, column: 18, scope: !1407)
!1407 = distinct !DILexicalBlock(scope: !1396, file: !97, line: 51, column: 6)
!1408 = !DILocation(line: 54, column: 10, scope: !1407)
!1409 = !DILocation(line: 56, column: 18, scope: !1407)
!1410 = !DILocation(line: 57, column: 10, scope: !1407)
!1411 = !DILocation(line: 59, column: 18, scope: !1407)
!1412 = !DILocation(line: 60, column: 10, scope: !1407)
!1413 = !DILocation(line: 62, column: 18, scope: !1407)
!1414 = !DILocation(line: 63, column: 10, scope: !1407)
!1415 = !DILocation(line: 65, column: 18, scope: !1407)
!1416 = !DILocation(line: 66, column: 10, scope: !1407)
!1417 = !DILocation(line: 68, column: 18, scope: !1407)
!1418 = !DILocation(line: 69, column: 10, scope: !1407)
!1419 = !DILocation(line: 71, column: 11, scope: !1396)
!1420 = !DILocation(line: 71, column: 4, scope: !1396)
!1421 = distinct !DISubprogram(name: "hostname_to_ip", scope: !97, file: !97, line: 74, type: !1422, isLocal: false, isDefinition: true, scopeLine: 75, flags: DIFlagPrototyped, isOptimized: false, unit: !96, variables: !2)
!1422 = !DISubroutineType(types: !1423)
!1423 = !{!12, !18, !234}
!1424 = !DILocalVariable(name: "hostname", arg: 1, scope: !1421, file: !97, line: 74, type: !18)
!1425 = !DILocation(line: 74, column: 26, scope: !1421)
!1426 = !DILocalVariable(name: "ip_addr", arg: 2, scope: !1421, file: !97, line: 74, type: !234)
!1427 = !DILocation(line: 74, column: 52, scope: !1421)
!1428 = !DILocalVariable(name: "ret", scope: !1421, file: !97, line: 76, type: !12)
!1429 = !DILocation(line: 76, column: 8, scope: !1421)
!1430 = !DILocalVariable(name: "hints", scope: !1421, file: !97, line: 77, type: !1431)
!1431 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "addrinfo", file: !1432, line: 567, size: 256, align: 32, elements: !1433)
!1432 = !DIFile(filename: "/home/zrz0517/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/libc/usr/include/netdb.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/alarm4pi-cb")
!1433 = !{!1434, !1435, !1436, !1437, !1438, !1441, !1447, !1448}
!1434 = !DIDerivedType(tag: DW_TAG_member, name: "ai_flags", scope: !1431, file: !1432, line: 569, baseType: !12, size: 32, align: 32)
!1435 = !DIDerivedType(tag: DW_TAG_member, name: "ai_family", scope: !1431, file: !1432, line: 570, baseType: !12, size: 32, align: 32, offset: 32)
!1436 = !DIDerivedType(tag: DW_TAG_member, name: "ai_socktype", scope: !1431, file: !1432, line: 571, baseType: !12, size: 32, align: 32, offset: 64)
!1437 = !DIDerivedType(tag: DW_TAG_member, name: "ai_protocol", scope: !1431, file: !1432, line: 572, baseType: !12, size: 32, align: 32, offset: 96)
!1438 = !DIDerivedType(tag: DW_TAG_member, name: "ai_addrlen", scope: !1431, file: !1432, line: 573, baseType: !1439, size: 32, align: 32, offset: 128)
!1439 = !DIDerivedType(tag: DW_TAG_typedef, name: "socklen_t", file: !65, line: 33, baseType: !1440)
!1440 = !DIDerivedType(tag: DW_TAG_typedef, name: "__socklen_t", file: !11, line: 189, baseType: !94)
!1441 = !DIDerivedType(tag: DW_TAG_member, name: "ai_addr", scope: !1431, file: !1432, line: 574, baseType: !1442, size: 32, align: 32, offset: 160)
!1442 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1443, size: 32, align: 32)
!1443 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "sockaddr", file: !65, line: 153, size: 128, align: 16, elements: !1444)
!1444 = !{!1445, !1446}
!1445 = !DIDerivedType(tag: DW_TAG_member, name: "sa_family", scope: !1443, file: !65, line: 155, baseType: !68, size: 16, align: 16)
!1446 = !DIDerivedType(tag: DW_TAG_member, name: "sa_data", scope: !1443, file: !65, line: 156, baseType: !72, size: 112, align: 8, offset: 16)
!1447 = !DIDerivedType(tag: DW_TAG_member, name: "ai_canonname", scope: !1431, file: !1432, line: 575, baseType: !18, size: 32, align: 32, offset: 192)
!1448 = !DIDerivedType(tag: DW_TAG_member, name: "ai_next", scope: !1431, file: !1432, line: 576, baseType: !1449, size: 32, align: 32, offset: 224)
!1449 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1431, size: 32, align: 32)
!1450 = !DILocation(line: 77, column: 20, scope: !1421)
!1451 = !DILocalVariable(name: "res_addr", scope: !1421, file: !97, line: 77, type: !1449)
!1452 = !DILocation(line: 77, column: 28, scope: !1421)
!1453 = !DILocalVariable(name: "res_error", scope: !1421, file: !97, line: 78, type: !12)
!1454 = !DILocation(line: 78, column: 8, scope: !1421)
!1455 = !DILocation(line: 80, column: 4, scope: !1421)
!1456 = !DILocation(line: 81, column: 10, scope: !1421)
!1457 = !DILocation(line: 81, column: 20, scope: !1421)
!1458 = !DILocation(line: 82, column: 10, scope: !1421)
!1459 = !DILocation(line: 82, column: 22, scope: !1421)
!1460 = !DILocation(line: 84, column: 28, scope: !1421)
!1461 = !DILocation(line: 84, column: 16, scope: !1421)
!1462 = !DILocation(line: 84, column: 14, scope: !1421)
!1463 = !DILocation(line: 85, column: 7, scope: !1464)
!1464 = distinct !DILexicalBlock(scope: !1421, file: !97, line: 85, column: 7)
!1465 = !DILocation(line: 85, column: 17, scope: !1464)
!1466 = !DILocation(line: 85, column: 7, scope: !1421)
!1467 = !DILocalVariable(name: "res_addr_next", scope: !1468, file: !97, line: 87, type: !1449)
!1468 = distinct !DILexicalBlock(scope: !1464, file: !97, line: 86, column: 6)
!1469 = !DILocation(line: 87, column: 24, scope: !1468)
!1470 = !DILocation(line: 89, column: 10, scope: !1468)
!1471 = !DILocation(line: 91, column: 27, scope: !1472)
!1472 = distinct !DILexicalBlock(scope: !1468, file: !97, line: 91, column: 7)
!1473 = !DILocation(line: 91, column: 25, scope: !1472)
!1474 = !DILocation(line: 91, column: 11, scope: !1472)
!1475 = !DILocation(line: 91, column: 37, scope: !1476)
!1476 = !DILexicalBlockFile(scope: !1477, file: !97, discriminator: 1)
!1477 = distinct !DILexicalBlock(scope: !1472, file: !97, line: 91, column: 7)
!1478 = !DILocation(line: 91, column: 51, scope: !1476)
!1479 = !DILocation(line: 91, column: 7, scope: !1476)
!1480 = !DILocalVariable(name: "addr", scope: !1481, file: !97, line: 93, type: !214)
!1481 = distinct !DILexicalBlock(scope: !1477, file: !97, line: 92, column: 9)
!1482 = !DILocation(line: 93, column: 28, scope: !1481)
!1483 = !DILocation(line: 95, column: 39, scope: !1481)
!1484 = !DILocation(line: 95, column: 54, scope: !1481)
!1485 = !DILocation(line: 95, column: 17, scope: !1481)
!1486 = !DILocation(line: 95, column: 15, scope: !1481)
!1487 = !DILocation(line: 96, column: 11, scope: !1481)
!1488 = !DILocation(line: 96, column: 19, scope: !1481)
!1489 = !DILocation(line: 96, column: 25, scope: !1481)
!1490 = !DILocation(line: 97, column: 13, scope: !1491)
!1491 = distinct !DILexicalBlock(scope: !1481, file: !97, line: 97, column: 13)
!1492 = !DILocation(line: 97, column: 22, scope: !1491)
!1493 = !DILocation(line: 97, column: 29, scope: !1491)
!1494 = !DILocation(line: 97, column: 13, scope: !1481)
!1495 = !DILocation(line: 100, column: 16, scope: !1496)
!1496 = distinct !DILexicalBlock(scope: !1491, file: !97, line: 98, column: 12)
!1497 = !DILocation(line: 101, column: 13, scope: !1496)
!1498 = !DILocation(line: 103, column: 9, scope: !1481)
!1499 = !DILocation(line: 91, column: 76, scope: !1500)
!1500 = !DILexicalBlockFile(scope: !1477, file: !97, discriminator: 2)
!1501 = !DILocation(line: 91, column: 91, scope: !1500)
!1502 = !DILocation(line: 91, column: 74, scope: !1500)
!1503 = !DILocation(line: 91, column: 7, scope: !1500)
!1504 = distinct !{!1504, !1505}
!1505 = !DILocation(line: 91, column: 7, scope: !1468)
!1506 = !DILocation(line: 105, column: 20, scope: !1468)
!1507 = !DILocation(line: 105, column: 7, scope: !1468)
!1508 = !DILocation(line: 106, column: 6, scope: !1468)
!1509 = !DILocation(line: 109, column: 7, scope: !1510)
!1510 = distinct !DILexicalBlock(scope: !1464, file: !97, line: 108, column: 6)
!1511 = !DILocation(line: 109, column: 7, scope: !1512)
!1512 = !DILexicalBlockFile(scope: !1510, file: !97, discriminator: 1)
!1513 = !DILocation(line: 110, column: 11, scope: !1510)
!1514 = !DILocation(line: 110, column: 10, scope: !1510)
!1515 = !DILocation(line: 113, column: 11, scope: !1421)
!1516 = !DILocation(line: 113, column: 4, scope: !1421)
!1517 = distinct !DISubprogram(name: "hostname_to_ip_at_dns", scope: !97, file: !97, line: 116, type: !1518, isLocal: false, isDefinition: true, scopeLine: 117, flags: DIFlagPrototyped, isOptimized: false, unit: !96, variables: !2)
!1518 = !DISubroutineType(types: !1519)
!1519 = !{!12, !18, !18, !234}
!1520 = !DILocalVariable(name: "dns_server", arg: 1, scope: !1517, file: !97, line: 116, type: !18)
!1521 = !DILocation(line: 116, column: 33, scope: !1517)
!1522 = !DILocalVariable(name: "domain_name", arg: 2, scope: !1517, file: !97, line: 116, type: !18)
!1523 = !DILocation(line: 116, column: 51, scope: !1517)
!1524 = !DILocalVariable(name: "ip_addr", arg: 3, scope: !1517, file: !97, line: 116, type: !234)
!1525 = !DILocation(line: 116, column: 80, scope: !1517)
!1526 = !DILocalVariable(name: "fn_ret", scope: !1517, file: !97, line: 118, type: !12)
!1527 = !DILocation(line: 118, column: 8, scope: !1517)
!1528 = !DILocalVariable(name: "res_stat", scope: !1517, file: !97, line: 119, type: !1529)
!1529 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "__res_state", file: !119, line: 104, size: 4096, align: 32, elements: !1530)
!1530 = !{!1531, !1532, !1533, !1536, !1537, !1541, !1544, !1546, !1550, !1551, !1552, !1553, !1554, !1555, !1564, !1576, !1583, !1584, !1585, !1588}
!1531 = !DIDerivedType(tag: DW_TAG_member, name: "retrans", scope: !1529, file: !119, line: 105, baseType: !12, size: 32, align: 32)
!1532 = !DIDerivedType(tag: DW_TAG_member, name: "retry", scope: !1529, file: !119, line: 106, baseType: !12, size: 32, align: 32, offset: 32)
!1533 = !DIDerivedType(tag: DW_TAG_member, name: "options", scope: !1529, file: !119, line: 107, baseType: !1534, size: 32, align: 32, offset: 64)
!1534 = !DIDerivedType(tag: DW_TAG_typedef, name: "u_long", file: !9, line: 36, baseType: !1535)
!1535 = !DIDerivedType(tag: DW_TAG_typedef, name: "__u_long", file: !11, line: 33, baseType: !42)
!1536 = !DIDerivedType(tag: DW_TAG_member, name: "nscount", scope: !1529, file: !119, line: 108, baseType: !12, size: 32, align: 32, offset: 96)
!1537 = !DIDerivedType(tag: DW_TAG_member, name: "nsaddr_list", scope: !1529, file: !119, line: 110, baseType: !1538, size: 384, align: 32, offset: 128)
!1538 = !DICompositeType(tag: DW_TAG_array_type, baseType: !215, size: 384, align: 32, elements: !1539)
!1539 = !{!1540}
!1540 = !DISubrange(count: 3)
!1541 = !DIDerivedType(tag: DW_TAG_member, name: "id", scope: !1529, file: !119, line: 112, baseType: !1542, size: 16, align: 16, offset: 512)
!1542 = !DIDerivedType(tag: DW_TAG_typedef, name: "u_short", file: !9, line: 34, baseType: !1543)
!1543 = !DIDerivedType(tag: DW_TAG_typedef, name: "__u_short", file: !11, line: 31, baseType: !70)
!1544 = !DIDerivedType(tag: DW_TAG_member, name: "dnsrch", scope: !1529, file: !119, line: 114, baseType: !1545, size: 224, align: 32, offset: 544)
!1545 = !DICompositeType(tag: DW_TAG_array_type, baseType: !18, size: 224, align: 32, elements: !20)
!1546 = !DIDerivedType(tag: DW_TAG_member, name: "defdname", scope: !1529, file: !119, line: 115, baseType: !1547, size: 2048, align: 8, offset: 768)
!1547 = !DICompositeType(tag: DW_TAG_array_type, baseType: !19, size: 2048, align: 8, elements: !1548)
!1548 = !{!1549}
!1549 = !DISubrange(count: 256)
!1550 = !DIDerivedType(tag: DW_TAG_member, name: "pfcode", scope: !1529, file: !119, line: 116, baseType: !1534, size: 32, align: 32, offset: 2816)
!1551 = !DIDerivedType(tag: DW_TAG_member, name: "ndots", scope: !1529, file: !119, line: 117, baseType: !94, size: 4, align: 32, offset: 2848, flags: DIFlagBitField, extraData: i64 2848)
!1552 = !DIDerivedType(tag: DW_TAG_member, name: "nsort", scope: !1529, file: !119, line: 118, baseType: !94, size: 4, align: 32, offset: 2852, flags: DIFlagBitField, extraData: i64 2848)
!1553 = !DIDerivedType(tag: DW_TAG_member, name: "ipv6_unavail", scope: !1529, file: !119, line: 119, baseType: !94, size: 1, align: 32, offset: 2856, flags: DIFlagBitField, extraData: i64 2848)
!1554 = !DIDerivedType(tag: DW_TAG_member, name: "unused", scope: !1529, file: !119, line: 120, baseType: !94, size: 23, align: 32, offset: 2857, flags: DIFlagBitField, extraData: i64 2848)
!1555 = !DIDerivedType(tag: DW_TAG_member, name: "sort_list", scope: !1529, file: !119, line: 124, baseType: !1556, size: 640, align: 32, offset: 2880)
!1556 = !DICompositeType(tag: DW_TAG_array_type, baseType: !1557, size: 640, align: 32, elements: !1562)
!1557 = distinct !DICompositeType(tag: DW_TAG_structure_type, scope: !1529, file: !119, line: 121, size: 64, align: 32, elements: !1558)
!1558 = !{!1559, !1560}
!1559 = !DIDerivedType(tag: DW_TAG_member, name: "addr", scope: !1557, file: !119, line: 122, baseType: !222, size: 32, align: 32)
!1560 = !DIDerivedType(tag: DW_TAG_member, name: "mask", scope: !1557, file: !119, line: 123, baseType: !1561, size: 32, align: 32, offset: 32)
!1561 = !DIDerivedType(tag: DW_TAG_typedef, name: "u_int32_t", file: !9, line: 202, baseType: !94)
!1562 = !{!1563}
!1563 = !DISubrange(count: 10)
!1564 = !DIDerivedType(tag: DW_TAG_member, name: "qhook", scope: !1529, file: !119, line: 126, baseType: !1565, size: 32, align: 32, offset: 3520)
!1565 = !DIDerivedType(tag: DW_TAG_typedef, name: "res_send_qhook", file: !119, line: 74, baseType: !1566)
!1566 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1567, size: 32, align: 32)
!1567 = !DISubroutineType(types: !1568)
!1568 = !{!1569, !1570, !1572, !1575, !230, !12, !1575}
!1569 = !DIDerivedType(tag: DW_TAG_typedef, name: "res_sendhookact", file: !119, line: 72, baseType: !118)
!1570 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1571, size: 32, align: 32)
!1571 = !DIDerivedType(tag: DW_TAG_const_type, baseType: !214)
!1572 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1573, size: 32, align: 32)
!1573 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1574, size: 32, align: 32)
!1574 = !DIDerivedType(tag: DW_TAG_const_type, baseType: !231)
!1575 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !12, size: 32, align: 32)
!1576 = !DIDerivedType(tag: DW_TAG_member, name: "rhook", scope: !1529, file: !119, line: 127, baseType: !1577, size: 32, align: 32, offset: 3552)
!1577 = !DIDerivedType(tag: DW_TAG_typedef, name: "res_send_rhook", file: !119, line: 81, baseType: !1578)
!1578 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1579, size: 32, align: 32)
!1579 = !DISubroutineType(types: !1580)
!1580 = !{!1569, !1581, !1573, !12, !230, !12, !1575}
!1581 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1582, size: 32, align: 32)
!1582 = !DIDerivedType(tag: DW_TAG_const_type, baseType: !215)
!1583 = !DIDerivedType(tag: DW_TAG_member, name: "res_h_errno", scope: !1529, file: !119, line: 128, baseType: !12, size: 32, align: 32, offset: 3584)
!1584 = !DIDerivedType(tag: DW_TAG_member, name: "_vcsock", scope: !1529, file: !119, line: 129, baseType: !12, size: 32, align: 32, offset: 3616)
!1585 = !DIDerivedType(tag: DW_TAG_member, name: "_flags", scope: !1529, file: !119, line: 130, baseType: !1586, size: 32, align: 32, offset: 3648)
!1586 = !DIDerivedType(tag: DW_TAG_typedef, name: "u_int", file: !9, line: 35, baseType: !1587)
!1587 = !DIDerivedType(tag: DW_TAG_typedef, name: "__u_int", file: !11, line: 32, baseType: !94)
!1588 = !DIDerivedType(tag: DW_TAG_member, name: "_u", scope: !1529, file: !119, line: 148, baseType: !1589, size: 416, align: 32, offset: 3680)
!1589 = distinct !DICompositeType(tag: DW_TAG_union_type, scope: !1529, file: !119, line: 132, size: 416, align: 32, elements: !1590)
!1590 = !{!1591, !1595}
!1591 = !DIDerivedType(tag: DW_TAG_member, name: "pad", scope: !1589, file: !119, line: 133, baseType: !1592, size: 416, align: 8)
!1592 = !DICompositeType(tag: DW_TAG_array_type, baseType: !19, size: 416, align: 8, elements: !1593)
!1593 = !{!1594}
!1594 = !DISubrange(count: 52)
!1595 = !DIDerivedType(tag: DW_TAG_member, name: "_ext", scope: !1589, file: !119, line: 147, baseType: !1596, size: 352, align: 32)
!1596 = distinct !DICompositeType(tag: DW_TAG_structure_type, scope: !1589, file: !119, line: 134, size: 352, align: 32, elements: !1597)
!1597 = !{!1598, !1600, !1602, !1604, !1605, !1606, !1632}
!1598 = !DIDerivedType(tag: DW_TAG_member, name: "nscount", scope: !1596, file: !119, line: 135, baseType: !1599, size: 16, align: 16)
!1599 = !DIDerivedType(tag: DW_TAG_typedef, name: "u_int16_t", file: !9, line: 201, baseType: !70)
!1600 = !DIDerivedType(tag: DW_TAG_member, name: "nsmap", scope: !1596, file: !119, line: 136, baseType: !1601, size: 48, align: 16, offset: 16)
!1601 = !DICompositeType(tag: DW_TAG_array_type, baseType: !1599, size: 48, align: 16, elements: !1539)
!1602 = !DIDerivedType(tag: DW_TAG_member, name: "nssocks", scope: !1596, file: !119, line: 137, baseType: !1603, size: 96, align: 32, offset: 64)
!1603 = !DICompositeType(tag: DW_TAG_array_type, baseType: !12, size: 96, align: 32, elements: !1539)
!1604 = !DIDerivedType(tag: DW_TAG_member, name: "nscount6", scope: !1596, file: !119, line: 138, baseType: !1599, size: 16, align: 16, offset: 160)
!1605 = !DIDerivedType(tag: DW_TAG_member, name: "nsinit", scope: !1596, file: !119, line: 139, baseType: !1599, size: 16, align: 16, offset: 176)
!1606 = !DIDerivedType(tag: DW_TAG_member, name: "nsaddrs", scope: !1596, file: !119, line: 140, baseType: !1607, size: 96, align: 32, offset: 192)
!1607 = !DICompositeType(tag: DW_TAG_array_type, baseType: !1608, size: 96, align: 32, elements: !1539)
!1608 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1609, size: 32, align: 32)
!1609 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "sockaddr_in6", file: !88, line: 254, size: 224, align: 32, elements: !1610)
!1610 = !{!1611, !1612, !1613, !1614, !1631}
!1611 = !DIDerivedType(tag: DW_TAG_member, name: "sin6_family", scope: !1609, file: !88, line: 256, baseType: !68, size: 16, align: 16)
!1612 = !DIDerivedType(tag: DW_TAG_member, name: "sin6_port", scope: !1609, file: !88, line: 257, baseType: !219, size: 16, align: 16, offset: 16)
!1613 = !DIDerivedType(tag: DW_TAG_member, name: "sin6_flowinfo", scope: !1609, file: !88, line: 258, baseType: !92, size: 32, align: 32, offset: 32)
!1614 = !DIDerivedType(tag: DW_TAG_member, name: "sin6_addr", scope: !1609, file: !88, line: 259, baseType: !1615, size: 128, align: 32, offset: 64)
!1615 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "in6_addr", file: !88, line: 211, size: 128, align: 32, elements: !1616)
!1616 = !{!1617}
!1617 = !DIDerivedType(tag: DW_TAG_member, name: "__in6_u", scope: !1615, file: !88, line: 220, baseType: !1618, size: 128, align: 32)
!1618 = distinct !DICompositeType(tag: DW_TAG_union_type, scope: !1615, file: !88, line: 213, size: 128, align: 32, elements: !1619)
!1619 = !{!1620, !1625, !1627}
!1620 = !DIDerivedType(tag: DW_TAG_member, name: "__u6_addr8", scope: !1618, file: !88, line: 215, baseType: !1621, size: 128, align: 8)
!1621 = !DICompositeType(tag: DW_TAG_array_type, baseType: !1622, size: 128, align: 8, elements: !1623)
!1622 = !DIDerivedType(tag: DW_TAG_typedef, name: "uint8_t", file: !93, line: 48, baseType: !227)
!1623 = !{!1624}
!1624 = !DISubrange(count: 16)
!1625 = !DIDerivedType(tag: DW_TAG_member, name: "__u6_addr16", scope: !1618, file: !88, line: 217, baseType: !1626, size: 128, align: 16)
!1626 = !DICompositeType(tag: DW_TAG_array_type, baseType: !220, size: 128, align: 16, elements: !228)
!1627 = !DIDerivedType(tag: DW_TAG_member, name: "__u6_addr32", scope: !1618, file: !88, line: 218, baseType: !1628, size: 128, align: 32)
!1628 = !DICompositeType(tag: DW_TAG_array_type, baseType: !92, size: 128, align: 32, elements: !1629)
!1629 = !{!1630}
!1630 = !DISubrange(count: 4)
!1631 = !DIDerivedType(tag: DW_TAG_member, name: "sin6_scope_id", scope: !1609, file: !88, line: 260, baseType: !92, size: 32, align: 32, offset: 192)
!1632 = !DIDerivedType(tag: DW_TAG_member, name: "_initstamp", scope: !1596, file: !119, line: 145, baseType: !1633, size: 64, align: 32, offset: 288)
!1633 = !DICompositeType(tag: DW_TAG_array_type, baseType: !94, size: 64, align: 32, elements: !13)
!1634 = !DILocation(line: 119, column: 23, scope: !1517)
!1635 = !DILocation(line: 121, column: 4, scope: !1517)
!1636 = !DILocation(line: 122, column: 11, scope: !1517)
!1637 = !DILocation(line: 122, column: 10, scope: !1517)
!1638 = !DILocation(line: 124, column: 7, scope: !1639)
!1639 = distinct !DILexicalBlock(scope: !1517, file: !97, line: 124, column: 7)
!1640 = !DILocation(line: 124, column: 14, scope: !1639)
!1641 = !DILocation(line: 124, column: 7, scope: !1517)
!1642 = !DILocalVariable(name: "dns_ip", scope: !1643, file: !97, line: 126, type: !222)
!1643 = distinct !DILexicalBlock(scope: !1639, file: !97, line: 125, column: 6)
!1644 = !DILocation(line: 126, column: 22, scope: !1643)
!1645 = !DILocation(line: 128, column: 29, scope: !1643)
!1646 = !DILocation(line: 128, column: 14, scope: !1643)
!1647 = !DILocation(line: 128, column: 13, scope: !1643)
!1648 = !DILocation(line: 129, column: 10, scope: !1649)
!1649 = distinct !DILexicalBlock(scope: !1643, file: !97, line: 129, column: 10)
!1650 = !DILocation(line: 129, column: 16, scope: !1649)
!1651 = !DILocation(line: 129, column: 10, scope: !1643)
!1652 = !DILocalVariable(name: "dns_response", scope: !1653, file: !97, line: 135, type: !1654)
!1653 = distinct !DILexicalBlock(scope: !1649, file: !97, line: 130, column: 9)
!1654 = distinct !DICompositeType(tag: DW_TAG_union_type, scope: !1517, file: !97, line: 131, size: 4096, align: 32, elements: !1655)
!1655 = !{!1656, !1676}
!1656 = !DIDerivedType(tag: DW_TAG_member, name: "hdr", scope: !1654, file: !97, line: 133, baseType: !1657, size: 96, align: 32)
!1657 = !DIDerivedType(tag: DW_TAG_typedef, name: "HEADER", file: !1658, line: 83, baseType: !1659)
!1658 = !DIFile(filename: "/home/zrz0517/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/libc/usr/include/arpa/nameser_compat.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/alarm4pi-cb")
!1659 = distinct !DICompositeType(tag: DW_TAG_structure_type, file: !1658, line: 48, size: 96, align: 32, elements: !1660)
!1660 = !{!1661, !1662, !1663, !1664, !1665, !1666, !1667, !1668, !1669, !1670, !1671, !1672, !1673, !1674, !1675}
!1661 = !DIDerivedType(tag: DW_TAG_member, name: "id", scope: !1659, file: !1658, line: 49, baseType: !94, size: 16, align: 32, flags: DIFlagBitField, extraData: i64 0)
!1662 = !DIDerivedType(tag: DW_TAG_member, name: "rd", scope: !1659, file: !1658, line: 66, baseType: !94, size: 1, align: 32, offset: 16, flags: DIFlagBitField, extraData: i64 0)
!1663 = !DIDerivedType(tag: DW_TAG_member, name: "tc", scope: !1659, file: !1658, line: 67, baseType: !94, size: 1, align: 32, offset: 17, flags: DIFlagBitField, extraData: i64 0)
!1664 = !DIDerivedType(tag: DW_TAG_member, name: "aa", scope: !1659, file: !1658, line: 68, baseType: !94, size: 1, align: 32, offset: 18, flags: DIFlagBitField, extraData: i64 0)
!1665 = !DIDerivedType(tag: DW_TAG_member, name: "opcode", scope: !1659, file: !1658, line: 69, baseType: !94, size: 4, align: 32, offset: 19, flags: DIFlagBitField, extraData: i64 0)
!1666 = !DIDerivedType(tag: DW_TAG_member, name: "qr", scope: !1659, file: !1658, line: 70, baseType: !94, size: 1, align: 32, offset: 23, flags: DIFlagBitField, extraData: i64 0)
!1667 = !DIDerivedType(tag: DW_TAG_member, name: "rcode", scope: !1659, file: !1658, line: 72, baseType: !94, size: 4, align: 32, offset: 24, flags: DIFlagBitField, extraData: i64 0)
!1668 = !DIDerivedType(tag: DW_TAG_member, name: "cd", scope: !1659, file: !1658, line: 73, baseType: !94, size: 1, align: 32, offset: 28, flags: DIFlagBitField, extraData: i64 0)
!1669 = !DIDerivedType(tag: DW_TAG_member, name: "ad", scope: !1659, file: !1658, line: 74, baseType: !94, size: 1, align: 32, offset: 29, flags: DIFlagBitField, extraData: i64 0)
!1670 = !DIDerivedType(tag: DW_TAG_member, name: "unused", scope: !1659, file: !1658, line: 75, baseType: !94, size: 1, align: 32, offset: 30, flags: DIFlagBitField, extraData: i64 0)
!1671 = !DIDerivedType(tag: DW_TAG_member, name: "ra", scope: !1659, file: !1658, line: 76, baseType: !94, size: 1, align: 32, offset: 31, flags: DIFlagBitField, extraData: i64 0)
!1672 = !DIDerivedType(tag: DW_TAG_member, name: "qdcount", scope: !1659, file: !1658, line: 79, baseType: !94, size: 16, align: 32, offset: 32, flags: DIFlagBitField, extraData: i64 0)
!1673 = !DIDerivedType(tag: DW_TAG_member, name: "ancount", scope: !1659, file: !1658, line: 80, baseType: !94, size: 16, align: 32, offset: 48, flags: DIFlagBitField, extraData: i64 0)
!1674 = !DIDerivedType(tag: DW_TAG_member, name: "nscount", scope: !1659, file: !1658, line: 81, baseType: !94, size: 16, align: 32, offset: 64, flags: DIFlagBitField, extraData: i64 0)
!1675 = !DIDerivedType(tag: DW_TAG_member, name: "arcount", scope: !1659, file: !1658, line: 82, baseType: !94, size: 16, align: 32, offset: 80, flags: DIFlagBitField, extraData: i64 0)
!1676 = !DIDerivedType(tag: DW_TAG_member, name: "buf", scope: !1654, file: !97, line: 134, baseType: !1677, size: 4096, align: 8)
!1677 = !DICompositeType(tag: DW_TAG_array_type, baseType: !231, size: 4096, align: 8, elements: !1678)
!1678 = !{!1679}
!1679 = !DISubrange(count: 512)
!1680 = !DILocation(line: 135, column: 14, scope: !1653)
!1681 = !DILocalVariable(name: "dns_response_len", scope: !1653, file: !97, line: 136, type: !12)
!1682 = !DILocation(line: 136, column: 14, scope: !1653)
!1683 = !DILocalVariable(name: "saved_dns_addr", scope: !1653, file: !97, line: 138, type: !1684)
!1684 = !DICompositeType(tag: DW_TAG_array_type, baseType: !222, size: 96, align: 32, elements: !1539)
!1685 = !DILocation(line: 138, column: 25, scope: !1653)
!1686 = !DILocalVariable(name: "saved_dns_count", scope: !1653, file: !97, line: 139, type: !12)
!1687 = !DILocation(line: 139, column: 14, scope: !1653)
!1688 = !DILocalVariable(name: "saved_res_options", scope: !1653, file: !97, line: 140, type: !248)
!1689 = !DILocation(line: 140, column: 15, scope: !1653)
!1690 = !DILocalVariable(name: "n_dns_addr", scope: !1653, file: !97, line: 142, type: !12)
!1691 = !DILocation(line: 142, column: 14, scope: !1653)
!1692 = !DILocation(line: 146, column: 37, scope: !1653)
!1693 = !DILocation(line: 146, column: 26, scope: !1653)
!1694 = !DILocation(line: 147, column: 25, scope: !1695)
!1695 = distinct !DILexicalBlock(scope: !1653, file: !97, line: 147, column: 10)
!1696 = !DILocation(line: 147, column: 14, scope: !1695)
!1697 = !DILocation(line: 147, column: 29, scope: !1698)
!1698 = !DILexicalBlockFile(scope: !1699, file: !97, discriminator: 1)
!1699 = distinct !DILexicalBlock(scope: !1695, file: !97, line: 147, column: 10)
!1700 = !DILocation(line: 147, column: 42, scope: !1698)
!1701 = !DILocation(line: 147, column: 40, scope: !1698)
!1702 = !DILocation(line: 147, column: 10, scope: !1698)
!1703 = !DILocation(line: 148, column: 28, scope: !1699)
!1704 = !DILocation(line: 148, column: 13, scope: !1699)
!1705 = !DILocation(line: 148, column: 63, scope: !1699)
!1706 = !DILocation(line: 148, column: 51, scope: !1699)
!1707 = !DILocation(line: 148, column: 42, scope: !1699)
!1708 = !DILocation(line: 148, column: 75, scope: !1699)
!1709 = !DILocation(line: 147, column: 68, scope: !1710)
!1710 = !DILexicalBlockFile(scope: !1699, file: !97, discriminator: 2)
!1711 = !DILocation(line: 147, column: 10, scope: !1710)
!1712 = distinct !{!1712, !1713}
!1713 = !DILocation(line: 147, column: 10, scope: !1653)
!1714 = !DILocation(line: 149, column: 37, scope: !1653)
!1715 = !DILocation(line: 149, column: 27, scope: !1653)
!1716 = !DILocation(line: 152, column: 19, scope: !1653)
!1717 = !DILocation(line: 152, column: 27, scope: !1653)
!1718 = !DILocation(line: 155, column: 19, scope: !1653)
!1719 = !DILocation(line: 155, column: 10, scope: !1653)
!1720 = !DILocation(line: 155, column: 34, scope: !1653)
!1721 = !DILocation(line: 155, column: 43, scope: !1653)
!1722 = !DILocation(line: 156, column: 19, scope: !1653)
!1723 = !DILocation(line: 156, column: 27, scope: !1653)
!1724 = !DILocation(line: 162, column: 51, scope: !1653)
!1725 = !DILocation(line: 162, column: 81, scope: !1653)
!1726 = !DILocation(line: 162, column: 29, scope: !1653)
!1727 = !DILocation(line: 162, column: 27, scope: !1653)
!1728 = !DILocation(line: 163, column: 13, scope: !1729)
!1729 = distinct !DILexicalBlock(scope: !1653, file: !97, line: 163, column: 13)
!1730 = !DILocation(line: 163, column: 30, scope: !1729)
!1731 = !DILocation(line: 163, column: 13, scope: !1653)
!1732 = !DILocalVariable(name: "resp_handle", scope: !1733, file: !97, line: 165, type: !1734)
!1733 = distinct !DILexicalBlock(scope: !1729, file: !97, line: 164, column: 12)
!1734 = !DIDerivedType(tag: DW_TAG_typedef, name: "ns_msg", file: !100, line: 121, baseType: !1735)
!1735 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "__ns_msg", file: !100, line: 114, size: 384, align: 32, elements: !1736)
!1736 = !{!1737, !1738, !1739, !1740, !1741, !1743, !1745, !1747, !1748}
!1737 = !DIDerivedType(tag: DW_TAG_member, name: "_msg", scope: !1735, file: !100, line: 115, baseType: !1573, size: 32, align: 32)
!1738 = !DIDerivedType(tag: DW_TAG_member, name: "_eom", scope: !1735, file: !100, line: 115, baseType: !1573, size: 32, align: 32, offset: 32)
!1739 = !DIDerivedType(tag: DW_TAG_member, name: "_id", scope: !1735, file: !100, line: 116, baseType: !1599, size: 16, align: 16, offset: 64)
!1740 = !DIDerivedType(tag: DW_TAG_member, name: "_flags", scope: !1735, file: !100, line: 116, baseType: !1599, size: 16, align: 16, offset: 80)
!1741 = !DIDerivedType(tag: DW_TAG_member, name: "_counts", scope: !1735, file: !100, line: 116, baseType: !1742, size: 64, align: 16, offset: 96)
!1742 = !DICompositeType(tag: DW_TAG_array_type, baseType: !1599, size: 64, align: 16, elements: !1629)
!1743 = !DIDerivedType(tag: DW_TAG_member, name: "_sections", scope: !1735, file: !100, line: 117, baseType: !1744, size: 128, align: 32, offset: 160)
!1744 = !DICompositeType(tag: DW_TAG_array_type, baseType: !1573, size: 128, align: 32, elements: !1629)
!1745 = !DIDerivedType(tag: DW_TAG_member, name: "_sect", scope: !1735, file: !100, line: 118, baseType: !1746, size: 32, align: 32, offset: 288)
!1746 = !DIDerivedType(tag: DW_TAG_typedef, name: "ns_sect", file: !100, line: 107, baseType: !190)
!1747 = !DIDerivedType(tag: DW_TAG_member, name: "_rrnum", scope: !1735, file: !100, line: 119, baseType: !12, size: 32, align: 32, offset: 320)
!1748 = !DIDerivedType(tag: DW_TAG_member, name: "_msg_ptr", scope: !1735, file: !100, line: 120, baseType: !1573, size: 32, align: 32, offset: 352)
!1749 = !DILocation(line: 165, column: 20, scope: !1733)
!1750 = !DILocation(line: 169, column: 46, scope: !1733)
!1751 = !DILocation(line: 169, column: 33, scope: !1733)
!1752 = !DILocation(line: 169, column: 51, scope: !1733)
!1753 = !DILocation(line: 169, column: 20, scope: !1733)
!1754 = !DILocation(line: 169, column: 19, scope: !1733)
!1755 = !DILocation(line: 170, column: 17, scope: !1756)
!1756 = distinct !DILexicalBlock(scope: !1733, file: !97, line: 170, column: 17)
!1757 = !DILocation(line: 170, column: 24, scope: !1756)
!1758 = !DILocation(line: 170, column: 17, scope: !1733)
!1759 = !DILocalVariable(name: "resp_error_code", scope: !1760, file: !97, line: 172, type: !12)
!1760 = distinct !DILexicalBlock(scope: !1756, file: !97, line: 171, column: 15)
!1761 = !DILocation(line: 172, column: 20, scope: !1760)
!1762 = !DILocation(line: 174, column: 32, scope: !1760)
!1763 = !DILocation(line: 174, column: 31, scope: !1760)
!1764 = !DILocation(line: 175, column: 19, scope: !1765)
!1765 = distinct !DILexicalBlock(scope: !1760, file: !97, line: 175, column: 19)
!1766 = !DILocation(line: 175, column: 35, scope: !1765)
!1767 = !DILocation(line: 175, column: 19, scope: !1760)
!1768 = !DILocalVariable(name: "answer_count", scope: !1769, file: !97, line: 177, type: !220)
!1769 = distinct !DILexicalBlock(scope: !1765, file: !97, line: 176, column: 18)
!1770 = !DILocation(line: 177, column: 28, scope: !1769)
!1771 = !DILocation(line: 181, column: 32, scope: !1769)
!1772 = !DILocation(line: 181, column: 31, scope: !1769)
!1773 = !DILocation(line: 182, column: 22, scope: !1774)
!1774 = distinct !DILexicalBlock(scope: !1769, file: !97, line: 182, column: 22)
!1775 = !DILocation(line: 182, column: 35, scope: !1774)
!1776 = !DILocation(line: 182, column: 22, scope: !1769)
!1777 = !DILocalVariable(name: "resp_record", scope: !1778, file: !97, line: 184, type: !1779)
!1778 = distinct !DILexicalBlock(scope: !1774, file: !97, line: 183, column: 21)
!1779 = !DIDerivedType(tag: DW_TAG_typedef, name: "ns_rr", file: !100, line: 145, baseType: !1780)
!1780 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "__ns_rr", file: !100, line: 138, size: 8352, align: 32, elements: !1781)
!1781 = !{!1782, !1786, !1787, !1788, !1789, !1790}
!1782 = !DIDerivedType(tag: DW_TAG_member, name: "name", scope: !1780, file: !100, line: 139, baseType: !1783, size: 8200, align: 8)
!1783 = !DICompositeType(tag: DW_TAG_array_type, baseType: !19, size: 8200, align: 8, elements: !1784)
!1784 = !{!1785}
!1785 = !DISubrange(count: 1025)
!1786 = !DIDerivedType(tag: DW_TAG_member, name: "type", scope: !1780, file: !100, line: 140, baseType: !1599, size: 16, align: 16, offset: 8208)
!1787 = !DIDerivedType(tag: DW_TAG_member, name: "rr_class", scope: !1780, file: !100, line: 141, baseType: !1599, size: 16, align: 16, offset: 8224)
!1788 = !DIDerivedType(tag: DW_TAG_member, name: "ttl", scope: !1780, file: !100, line: 142, baseType: !1561, size: 32, align: 32, offset: 8256)
!1789 = !DIDerivedType(tag: DW_TAG_member, name: "rdlength", scope: !1780, file: !100, line: 143, baseType: !1599, size: 16, align: 16, offset: 8288)
!1790 = !DIDerivedType(tag: DW_TAG_member, name: "rdata", scope: !1780, file: !100, line: 144, baseType: !1573, size: 32, align: 32, offset: 8320)
!1791 = !DILocation(line: 184, column: 28, scope: !1778)
!1792 = !DILocation(line: 187, column: 29, scope: !1778)
!1793 = !DILocation(line: 187, column: 28, scope: !1778)
!1794 = !DILocation(line: 188, column: 26, scope: !1795)
!1795 = distinct !DILexicalBlock(scope: !1778, file: !97, line: 188, column: 26)
!1796 = !DILocation(line: 188, column: 32, scope: !1795)
!1797 = !DILocation(line: 188, column: 26, scope: !1778)
!1798 = !DILocalVariable(name: "resp_type", scope: !1799, file: !97, line: 190, type: !1599)
!1799 = distinct !DILexicalBlock(scope: !1795, file: !97, line: 189, column: 24)
!1800 = !DILocation(line: 190, column: 35, scope: !1799)
!1801 = !DILocation(line: 192, column: 37, scope: !1799)
!1802 = !DILocation(line: 192, column: 35, scope: !1799)
!1803 = !DILocation(line: 195, column: 29, scope: !1804)
!1804 = distinct !DILexicalBlock(scope: !1799, file: !97, line: 195, column: 29)
!1805 = !DILocation(line: 195, column: 39, scope: !1804)
!1806 = !DILocation(line: 195, column: 29, scope: !1799)
!1807 = !DILocalVariable(name: "record_data", scope: !1808, file: !97, line: 197, type: !230)
!1808 = distinct !DILexicalBlock(scope: !1804, file: !97, line: 196, column: 27)
!1809 = !DILocation(line: 197, column: 36, scope: !1808)
!1810 = !DILocalVariable(name: "rec_disp_buf", scope: !1808, file: !97, line: 198, type: !1547)
!1811 = !DILocation(line: 198, column: 33, scope: !1808)
!1812 = !DILocation(line: 200, column: 80, scope: !1808)
!1813 = !DILocation(line: 200, column: 28, scope: !1808)
!1814 = !DILocation(line: 201, column: 28, scope: !1808)
!1815 = !DILocation(line: 203, column: 52, scope: !1808)
!1816 = !DILocation(line: 203, column: 40, scope: !1808)
!1817 = !DILocation(line: 205, column: 29, scope: !1808)
!1818 = !DILocation(line: 205, column: 58, scope: !1808)
!1819 = !DILocation(line: 205, column: 39, scope: !1808)
!1820 = !DILocation(line: 206, column: 34, scope: !1808)
!1821 = !DILocation(line: 207, column: 27, scope: !1808)
!1822 = !DILocation(line: 210, column: 28, scope: !1823)
!1823 = distinct !DILexicalBlock(scope: !1804, file: !97, line: 209, column: 27)
!1824 = !DILocation(line: 210, column: 28, scope: !1825)
!1825 = !DILexicalBlockFile(scope: !1823, file: !97, discriminator: 1)
!1826 = !DILocation(line: 211, column: 34, scope: !1823)
!1827 = !DILocation(line: 213, column: 24, scope: !1799)
!1828 = !DILocation(line: 216, column: 25, scope: !1829)
!1829 = distinct !DILexicalBlock(scope: !1795, file: !97, line: 215, column: 24)
!1830 = !DILocation(line: 216, column: 25, scope: !1831)
!1831 = !DILexicalBlockFile(scope: !1829, file: !97, discriminator: 1)
!1832 = !DILocation(line: 216, column: 25, scope: !1833)
!1833 = !DILexicalBlockFile(scope: !1829, file: !97, discriminator: 2)
!1834 = !DILocation(line: 218, column: 21, scope: !1778)
!1835 = !DILocation(line: 221, column: 22, scope: !1836)
!1836 = distinct !DILexicalBlock(scope: !1774, file: !97, line: 220, column: 21)
!1837 = !DILocation(line: 221, column: 22, scope: !1838)
!1838 = !DILexicalBlockFile(scope: !1836, file: !97, discriminator: 1)
!1839 = !DILocation(line: 222, column: 28, scope: !1836)
!1840 = !DILocation(line: 224, column: 18, scope: !1769)
!1841 = !DILocation(line: 227, column: 19, scope: !1842)
!1842 = distinct !DILexicalBlock(scope: !1765, file: !97, line: 226, column: 18)
!1843 = !DILocation(line: 227, column: 19, scope: !1844)
!1844 = !DILexicalBlockFile(scope: !1842, file: !97, discriminator: 1)
!1845 = !DILocation(line: 227, column: 19, scope: !1846)
!1846 = !DILexicalBlockFile(scope: !1842, file: !97, discriminator: 2)
!1847 = !DILocation(line: 228, column: 25, scope: !1842)
!1848 = !DILocation(line: 230, column: 15, scope: !1760)
!1849 = !DILocation(line: 233, column: 16, scope: !1850)
!1850 = distinct !DILexicalBlock(scope: !1756, file: !97, line: 232, column: 15)
!1851 = !DILocation(line: 233, column: 16, scope: !1852)
!1852 = !DILexicalBlockFile(scope: !1850, file: !97, discriminator: 1)
!1853 = !DILocation(line: 233, column: 16, scope: !1854)
!1854 = !DILexicalBlockFile(scope: !1850, file: !97, discriminator: 2)
!1855 = !DILocation(line: 235, column: 12, scope: !1733)
!1856 = !DILocation(line: 238, column: 16, scope: !1857)
!1857 = distinct !DILexicalBlock(scope: !1858, file: !97, line: 238, column: 16)
!1858 = distinct !DILexicalBlock(scope: !1729, file: !97, line: 237, column: 12)
!1859 = !DILocation(line: 238, column: 22, scope: !1857)
!1860 = !DILocation(line: 238, column: 16, scope: !1858)
!1861 = !DILocation(line: 239, column: 16, scope: !1857)
!1862 = !DILocation(line: 239, column: 16, scope: !1863)
!1863 = !DILexicalBlockFile(scope: !1857, file: !97, discriminator: 1)
!1864 = !DILocation(line: 241, column: 16, scope: !1857)
!1865 = !DILocation(line: 241, column: 16, scope: !1863)
!1866 = !DILocation(line: 241, column: 16, scope: !1867)
!1867 = !DILexicalBlockFile(scope: !1857, file: !97, discriminator: 2)
!1868 = !DILocation(line: 241, column: 16, scope: !1869)
!1869 = !DILexicalBlockFile(scope: !1857, file: !97, discriminator: 3)
!1870 = !DILocation(line: 241, column: 16, scope: !1871)
!1871 = !DILexicalBlockFile(scope: !1857, file: !97, discriminator: 4)
!1872 = !DILocation(line: 242, column: 19, scope: !1858)
!1873 = !DILocation(line: 245, column: 29, scope: !1653)
!1874 = !DILocation(line: 245, column: 19, scope: !1653)
!1875 = !DILocation(line: 245, column: 27, scope: !1653)
!1876 = !DILocation(line: 246, column: 29, scope: !1653)
!1877 = !DILocation(line: 246, column: 19, scope: !1653)
!1878 = !DILocation(line: 246, column: 27, scope: !1653)
!1879 = !DILocation(line: 247, column: 25, scope: !1880)
!1880 = distinct !DILexicalBlock(scope: !1653, file: !97, line: 247, column: 10)
!1881 = !DILocation(line: 247, column: 14, scope: !1880)
!1882 = !DILocation(line: 247, column: 29, scope: !1883)
!1883 = !DILexicalBlockFile(scope: !1884, file: !97, discriminator: 1)
!1884 = distinct !DILexicalBlock(scope: !1880, file: !97, line: 247, column: 10)
!1885 = !DILocation(line: 247, column: 42, scope: !1883)
!1886 = !DILocation(line: 247, column: 40, scope: !1883)
!1887 = !DILocation(line: 247, column: 10, scope: !1883)
!1888 = !DILocation(line: 248, column: 34, scope: !1884)
!1889 = !DILocation(line: 248, column: 22, scope: !1884)
!1890 = !DILocation(line: 248, column: 13, scope: !1884)
!1891 = !DILocation(line: 248, column: 46, scope: !1884)
!1892 = !DILocation(line: 248, column: 72, scope: !1884)
!1893 = !DILocation(line: 248, column: 57, scope: !1884)
!1894 = !DILocation(line: 247, column: 68, scope: !1895)
!1895 = !DILexicalBlockFile(scope: !1884, file: !97, discriminator: 2)
!1896 = !DILocation(line: 247, column: 10, scope: !1895)
!1897 = distinct !{!1897, !1898}
!1898 = !DILocation(line: 247, column: 10, scope: !1653)
!1899 = !DILocation(line: 249, column: 9, scope: !1653)
!1900 = !DILocation(line: 250, column: 6, scope: !1643)
!1901 = !DILocation(line: 253, column: 7, scope: !1902)
!1902 = distinct !DILexicalBlock(scope: !1639, file: !97, line: 252, column: 6)
!1903 = !DILocation(line: 253, column: 7, scope: !1904)
!1904 = !DILexicalBlockFile(scope: !1902, file: !97, discriminator: 1)
!1905 = !DILocation(line: 255, column: 11, scope: !1517)
!1906 = !DILocation(line: 255, column: 4, scope: !1517)
!1907 = distinct !DISubprogram(name: "get_public_ip", scope: !97, file: !97, line: 259, type: !568, isLocal: false, isDefinition: true, scopeLine: 260, flags: DIFlagPrototyped, isOptimized: false, unit: !96, variables: !2)
!1908 = !DILocalVariable(name: "public_ip", arg: 1, scope: !1907, file: !97, line: 259, type: !18)
!1909 = !DILocation(line: 259, column: 25, scope: !1907)
!1910 = !DILocalVariable(name: "fn_ret", scope: !1907, file: !97, line: 261, type: !12)
!1911 = !DILocation(line: 261, column: 8, scope: !1907)
!1912 = !DILocalVariable(name: "public_ip_addr", scope: !1907, file: !97, line: 262, type: !222)
!1913 = !DILocation(line: 262, column: 19, scope: !1907)
!1914 = !DILocation(line: 264, column: 11, scope: !1907)
!1915 = !DILocation(line: 264, column: 10, scope: !1907)
!1916 = !DILocation(line: 265, column: 7, scope: !1917)
!1917 = distinct !DILexicalBlock(scope: !1907, file: !97, line: 265, column: 7)
!1918 = !DILocation(line: 265, column: 13, scope: !1917)
!1919 = !DILocation(line: 265, column: 7, scope: !1907)
!1920 = !DILocation(line: 266, column: 15, scope: !1917)
!1921 = !DILocation(line: 266, column: 26, scope: !1917)
!1922 = !DILocation(line: 266, column: 8, scope: !1923)
!1923 = !DILexicalBlockFile(scope: !1917, file: !97, discriminator: 1)
!1924 = !DILocation(line: 266, column: 8, scope: !1917)
!1925 = !DILocation(line: 268, column: 12, scope: !1907)
!1926 = !DILocation(line: 268, column: 5, scope: !1907)
!1927 = distinct !DISubprogram(name: "get_current_exec_path", scope: !236, file: !236, line: 19, type: !1928, isLocal: false, isDefinition: true, scopeLine: 20, flags: DIFlagPrototyped, isOptimized: false, unit: !235, variables: !2)
!1928 = !DISubroutineType(types: !1929)
!1929 = !{!12, !18, !311}
!1930 = !DILocalVariable(name: "exec_path", arg: 1, scope: !1927, file: !236, line: 19, type: !18)
!1931 = !DILocation(line: 19, column: 33, scope: !1927)
!1932 = !DILocalVariable(name: "path_buff_len", arg: 2, scope: !1927, file: !236, line: 19, type: !311)
!1933 = !DILocation(line: 19, column: 51, scope: !1927)
!1934 = !DILocalVariable(name: "ret_error", scope: !1927, file: !236, line: 21, type: !12)
!1935 = !DILocation(line: 21, column: 8, scope: !1927)
!1936 = !DILocation(line: 22, column: 7, scope: !1937)
!1937 = distinct !DILexicalBlock(scope: !1927, file: !236, line: 22, column: 7)
!1938 = !DILocation(line: 22, column: 21, scope: !1937)
!1939 = !DILocation(line: 22, column: 7, scope: !1927)
!1940 = !DILocalVariable(name: "exec_path_buff", scope: !1941, file: !236, line: 24, type: !823)
!1941 = distinct !DILexicalBlock(scope: !1937, file: !236, line: 23, column: 6)
!1942 = !DILocation(line: 24, column: 12, scope: !1941)
!1943 = !DILocalVariable(name: "chars_written", scope: !1941, file: !236, line: 25, type: !311)
!1944 = !DILocation(line: 25, column: 14, scope: !1941)
!1945 = !DILocation(line: 27, column: 48, scope: !1941)
!1946 = !DILocation(line: 27, column: 21, scope: !1941)
!1947 = !DILocation(line: 27, column: 20, scope: !1941)
!1948 = !DILocation(line: 28, column: 10, scope: !1949)
!1949 = distinct !DILexicalBlock(scope: !1941, file: !236, line: 28, column: 10)
!1950 = !DILocation(line: 28, column: 24, scope: !1949)
!1951 = !DILocation(line: 28, column: 10, scope: !1941)
!1952 = !DILocalVariable(name: "exec_dir", scope: !1953, file: !236, line: 30, type: !18)
!1953 = distinct !DILexicalBlock(scope: !1949, file: !236, line: 29, column: 9)
!1954 = !DILocation(line: 30, column: 16, scope: !1953)
!1955 = !DILocation(line: 31, column: 25, scope: !1953)
!1956 = !DILocation(line: 31, column: 10, scope: !1953)
!1957 = !DILocation(line: 31, column: 39, scope: !1953)
!1958 = !DILocation(line: 32, column: 27, scope: !1953)
!1959 = !DILocation(line: 32, column: 19, scope: !1953)
!1960 = !DILocation(line: 32, column: 18, scope: !1953)
!1961 = !DILocation(line: 33, column: 13, scope: !1962)
!1962 = distinct !DILexicalBlock(scope: !1953, file: !236, line: 33, column: 13)
!1963 = !DILocation(line: 33, column: 36, scope: !1962)
!1964 = !DILocation(line: 33, column: 29, scope: !1962)
!1965 = !DILocation(line: 33, column: 45, scope: !1962)
!1966 = !DILocation(line: 33, column: 27, scope: !1962)
!1967 = !DILocation(line: 33, column: 13, scope: !1953)
!1968 = !DILocation(line: 35, column: 20, scope: !1969)
!1969 = distinct !DILexicalBlock(scope: !1962, file: !236, line: 34, column: 12)
!1970 = !DILocation(line: 35, column: 30, scope: !1969)
!1971 = !DILocation(line: 35, column: 13, scope: !1969)
!1972 = !DILocation(line: 36, column: 20, scope: !1969)
!1973 = !DILocation(line: 36, column: 13, scope: !1969)
!1974 = !DILocation(line: 37, column: 22, scope: !1969)
!1975 = !DILocation(line: 38, column: 12, scope: !1969)
!1976 = !DILocation(line: 41, column: 13, scope: !1977)
!1977 = distinct !DILexicalBlock(scope: !1962, file: !236, line: 40, column: 12)
!1978 = !DILocation(line: 41, column: 25, scope: !1977)
!1979 = !DILocation(line: 42, column: 22, scope: !1977)
!1980 = !DILocation(line: 44, column: 9, scope: !1953)
!1981 = !DILocation(line: 47, column: 10, scope: !1982)
!1982 = distinct !DILexicalBlock(scope: !1949, file: !236, line: 46, column: 9)
!1983 = !DILocation(line: 47, column: 22, scope: !1982)
!1984 = !DILocation(line: 48, column: 20, scope: !1982)
!1985 = !DILocation(line: 48, column: 19, scope: !1982)
!1986 = !DILocation(line: 50, column: 6, scope: !1941)
!1987 = !DILocation(line: 52, column: 16, scope: !1937)
!1988 = !DILocation(line: 53, column: 11, scope: !1927)
!1989 = !DILocation(line: 53, column: 4, scope: !1927)
!1990 = distinct !DISubprogram(name: "kill_processes", scope: !236, file: !236, line: 56, type: !1991, isLocal: false, isDefinition: true, scopeLine: 57, flags: DIFlagPrototyped, isOptimized: false, unit: !235, variables: !2)
!1991 = !DISubroutineType(types: !1992)
!1992 = !{null, !1993, !311}
!1993 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !8, size: 32, align: 32)
!1994 = !DILocalVariable(name: "process_ids", arg: 1, scope: !1990, file: !236, line: 56, type: !1993)
!1995 = !DILocation(line: 56, column: 28, scope: !1990)
!1996 = !DILocalVariable(name: "n_processes", arg: 2, scope: !1990, file: !236, line: 56, type: !311)
!1997 = !DILocation(line: 56, column: 48, scope: !1990)
!1998 = !DILocalVariable(name: "n_child", scope: !1990, file: !236, line: 58, type: !12)
!1999 = !DILocation(line: 58, column: 8, scope: !1990)
!2000 = !DILocation(line: 59, column: 15, scope: !2001)
!2001 = distinct !DILexicalBlock(scope: !1990, file: !236, line: 59, column: 4)
!2002 = !DILocation(line: 59, column: 8, scope: !2001)
!2003 = !DILocation(line: 59, column: 18, scope: !2004)
!2004 = !DILexicalBlockFile(scope: !2005, file: !236, discriminator: 1)
!2005 = distinct !DILexicalBlock(scope: !2001, file: !236, line: 59, column: 4)
!2006 = !DILocation(line: 59, column: 26, scope: !2004)
!2007 = !DILocation(line: 59, column: 25, scope: !2004)
!2008 = !DILocation(line: 59, column: 4, scope: !2004)
!2009 = !DILocation(line: 60, column: 22, scope: !2010)
!2010 = distinct !DILexicalBlock(scope: !2005, file: !236, line: 60, column: 10)
!2011 = !DILocation(line: 60, column: 10, scope: !2010)
!2012 = !DILocation(line: 60, column: 31, scope: !2010)
!2013 = !DILocation(line: 60, column: 10, scope: !2005)
!2014 = !DILocation(line: 61, column: 27, scope: !2010)
!2015 = !DILocation(line: 61, column: 15, scope: !2010)
!2016 = !DILocation(line: 61, column: 10, scope: !2010)
!2017 = !DILocation(line: 60, column: 35, scope: !2018)
!2018 = !DILexicalBlockFile(scope: !2010, file: !236, discriminator: 1)
!2019 = !DILocation(line: 59, column: 45, scope: !2020)
!2020 = !DILexicalBlockFile(scope: !2005, file: !236, discriminator: 2)
!2021 = !DILocation(line: 59, column: 4, scope: !2020)
!2022 = distinct !{!2022, !2023}
!2023 = !DILocation(line: 59, column: 4, scope: !1990)
!2024 = !DILocation(line: 62, column: 3, scope: !1990)
!2025 = distinct !DISubprogram(name: "wait_processes", scope: !236, file: !236, line: 64, type: !2026, isLocal: false, isDefinition: true, scopeLine: 65, flags: DIFlagPrototyped, isOptimized: false, unit: !235, variables: !2)
!2026 = !DISubroutineType(types: !2027)
!2027 = !{!12, !1993, !311, !12}
!2028 = !DILocalVariable(name: "process_ids", arg: 1, scope: !2025, file: !236, line: 64, type: !1993)
!2029 = !DILocation(line: 64, column: 27, scope: !2025)
!2030 = !DILocalVariable(name: "n_processes", arg: 2, scope: !2025, file: !236, line: 64, type: !311)
!2031 = !DILocation(line: 64, column: 47, scope: !2025)
!2032 = !DILocalVariable(name: "wait_timeout", arg: 3, scope: !2025, file: !236, line: 64, type: !12)
!2033 = !DILocation(line: 64, column: 64, scope: !2025)
!2034 = !DILocalVariable(name: "ret_error", scope: !2025, file: !236, line: 66, type: !12)
!2035 = !DILocation(line: 66, column: 8, scope: !2025)
!2036 = !DILocalVariable(name: "n_remaining_procs", scope: !2025, file: !236, line: 67, type: !12)
!2037 = !DILocation(line: 67, column: 8, scope: !2025)
!2038 = !DILocation(line: 69, column: 13, scope: !2025)
!2039 = !DILocation(line: 70, column: 4, scope: !2025)
!2040 = distinct !{!2040, !2039}
!2041 = !DILocalVariable(name: "wait_ret", scope: !2042, file: !236, line: 72, type: !12)
!2042 = distinct !DILexicalBlock(scope: !2025, file: !236, line: 71, column: 6)
!2043 = !DILocation(line: 72, column: 11, scope: !2042)
!2044 = !DILocation(line: 74, column: 24, scope: !2042)
!2045 = !DILocation(line: 75, column: 13, scope: !2042)
!2046 = !DILocation(line: 75, column: 7, scope: !2042)
!2047 = !DILocation(line: 76, column: 16, scope: !2042)
!2048 = !DILocation(line: 76, column: 15, scope: !2042)
!2049 = !DILocation(line: 77, column: 10, scope: !2050)
!2050 = distinct !DILexicalBlock(scope: !2042, file: !236, line: 77, column: 10)
!2051 = !DILocation(line: 77, column: 19, scope: !2050)
!2052 = !DILocation(line: 77, column: 10, scope: !2042)
!2053 = !DILocalVariable(name: "n_child", scope: !2054, file: !236, line: 79, type: !12)
!2054 = distinct !DILexicalBlock(scope: !2050, file: !236, line: 78, column: 9)
!2055 = !DILocation(line: 79, column: 14, scope: !2054)
!2056 = !DILocation(line: 81, column: 21, scope: !2057)
!2057 = distinct !DILexicalBlock(scope: !2054, file: !236, line: 81, column: 10)
!2058 = !DILocation(line: 81, column: 14, scope: !2057)
!2059 = !DILocation(line: 81, column: 24, scope: !2060)
!2060 = !DILexicalBlockFile(scope: !2061, file: !236, discriminator: 1)
!2061 = distinct !DILexicalBlock(scope: !2057, file: !236, line: 81, column: 10)
!2062 = !DILocation(line: 81, column: 32, scope: !2060)
!2063 = !DILocation(line: 81, column: 31, scope: !2060)
!2064 = !DILocation(line: 81, column: 10, scope: !2060)
!2065 = !DILocation(line: 82, column: 28, scope: !2066)
!2066 = distinct !DILexicalBlock(scope: !2061, file: !236, line: 82, column: 16)
!2067 = !DILocation(line: 82, column: 16, scope: !2066)
!2068 = !DILocation(line: 82, column: 37, scope: !2066)
!2069 = !DILocation(line: 82, column: 16, scope: !2061)
!2070 = !DILocation(line: 84, column: 31, scope: !2071)
!2071 = distinct !DILexicalBlock(scope: !2072, file: !236, line: 84, column: 19)
!2072 = distinct !DILexicalBlock(scope: !2066, file: !236, line: 83, column: 15)
!2073 = !DILocation(line: 84, column: 19, scope: !2071)
!2074 = !DILocation(line: 84, column: 43, scope: !2071)
!2075 = !DILocation(line: 84, column: 40, scope: !2071)
!2076 = !DILocation(line: 84, column: 19, scope: !2072)
!2077 = !DILocation(line: 86, column: 19, scope: !2078)
!2078 = distinct !DILexicalBlock(scope: !2071, file: !236, line: 85, column: 18)
!2079 = !DILocation(line: 87, column: 31, scope: !2078)
!2080 = !DILocation(line: 87, column: 19, scope: !2078)
!2081 = !DILocation(line: 87, column: 40, scope: !2078)
!2082 = !DILocation(line: 88, column: 17, scope: !2078)
!2083 = !DILocation(line: 90, column: 36, scope: !2071)
!2084 = !DILocation(line: 91, column: 15, scope: !2072)
!2085 = !DILocation(line: 82, column: 41, scope: !2086)
!2086 = !DILexicalBlockFile(scope: !2066, file: !236, discriminator: 1)
!2087 = !DILocation(line: 81, column: 51, scope: !2088)
!2088 = !DILexicalBlockFile(scope: !2061, file: !236, discriminator: 2)
!2089 = !DILocation(line: 81, column: 10, scope: !2088)
!2090 = distinct !{!2090, !2091}
!2091 = !DILocation(line: 81, column: 10, scope: !2054)
!2092 = !DILocation(line: 92, column: 9, scope: !2054)
!2093 = !DILocation(line: 95, column: 20, scope: !2094)
!2094 = distinct !DILexicalBlock(scope: !2050, file: !236, line: 94, column: 9)
!2095 = !DILocation(line: 95, column: 19, scope: !2094)
!2096 = !DILocation(line: 96, column: 10, scope: !2094)
!2097 = !DILocation(line: 96, column: 10, scope: !2098)
!2098 = !DILexicalBlockFile(scope: !2094, file: !236, discriminator: 1)
!2099 = !DILocation(line: 96, column: 10, scope: !2100)
!2100 = !DILexicalBlockFile(scope: !2094, file: !236, discriminator: 2)
!2101 = !DILocation(line: 96, column: 10, scope: !2102)
!2102 = !DILexicalBlockFile(scope: !2094, file: !236, discriminator: 3)
!2103 = !DILocation(line: 98, column: 6, scope: !2042)
!2104 = !DILocation(line: 99, column: 10, scope: !2025)
!2105 = !DILocation(line: 99, column: 28, scope: !2025)
!2106 = !DILocation(line: 98, column: 6, scope: !2107)
!2107 = !DILexicalBlockFile(scope: !2042, file: !236, discriminator: 1)
!2108 = !DILocation(line: 100, column: 11, scope: !2025)
!2109 = !DILocation(line: 100, column: 4, scope: !2025)
!2110 = distinct !DISubprogram(name: "run_background_command", scope: !236, file: !236, line: 103, type: !2111, isLocal: false, isDefinition: true, scopeLine: 104, flags: DIFlagPrototyped, isOptimized: false, unit: !235, variables: !2)
!2111 = !DISubroutineType(types: !2112)
!2112 = !{!12, !1993, !2113, !2115}
!2113 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !2114, size: 32, align: 32)
!2114 = !DIDerivedType(tag: DW_TAG_const_type, baseType: !19)
!2115 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !17, size: 32, align: 32)
!2116 = !DILocalVariable(name: "new_proc_id", arg: 1, scope: !2110, file: !236, line: 103, type: !1993)
!2117 = !DILocation(line: 103, column: 35, scope: !2110)
!2118 = !DILocalVariable(name: "exec_filename", arg: 2, scope: !2110, file: !236, line: 103, type: !2113)
!2119 = !DILocation(line: 103, column: 60, scope: !2110)
!2120 = !DILocalVariable(name: "exec_argv", arg: 3, scope: !2110, file: !236, line: 103, type: !2115)
!2121 = !DILocation(line: 103, column: 87, scope: !2110)
!2122 = !DILocalVariable(name: "ret", scope: !2110, file: !236, line: 105, type: !12)
!2123 = !DILocation(line: 105, column: 8, scope: !2110)
!2124 = !DILocation(line: 107, column: 19, scope: !2110)
!2125 = !DILocation(line: 107, column: 5, scope: !2110)
!2126 = !DILocation(line: 107, column: 17, scope: !2110)
!2127 = !DILocation(line: 109, column: 8, scope: !2128)
!2128 = distinct !DILexicalBlock(scope: !2110, file: !236, line: 109, column: 7)
!2129 = !DILocation(line: 109, column: 7, scope: !2128)
!2130 = !DILocation(line: 109, column: 20, scope: !2128)
!2131 = !DILocation(line: 109, column: 7, scope: !2110)
!2132 = !DILocalVariable(name: "null_fd_rd", scope: !2133, file: !236, line: 111, type: !12)
!2133 = distinct !DILexicalBlock(scope: !2128, file: !236, line: 110, column: 6)
!2134 = !DILocation(line: 111, column: 11, scope: !2133)
!2135 = !DILocation(line: 112, column: 10, scope: !2136)
!2136 = distinct !DILexicalBlock(scope: !2133, file: !236, line: 112, column: 10)
!2137 = !DILocation(line: 112, column: 26, scope: !2136)
!2138 = !DILocation(line: 112, column: 10, scope: !2133)
!2139 = !DILocation(line: 114, column: 25, scope: !2140)
!2140 = distinct !DILexicalBlock(scope: !2141, file: !236, line: 114, column: 13)
!2141 = distinct !DILexicalBlock(scope: !2136, file: !236, line: 113, column: 9)
!2142 = !DILocation(line: 114, column: 18, scope: !2140)
!2143 = !DILocation(line: 114, column: 13, scope: !2144)
!2144 = !DILexicalBlockFile(scope: !2140, file: !236, discriminator: 1)
!2145 = !DILocation(line: 114, column: 58, scope: !2140)
!2146 = !DILocation(line: 114, column: 13, scope: !2141)
!2147 = !DILocation(line: 115, column: 13, scope: !2140)
!2148 = !DILocation(line: 115, column: 13, scope: !2144)
!2149 = !DILocation(line: 116, column: 25, scope: !2150)
!2150 = distinct !DILexicalBlock(scope: !2141, file: !236, line: 116, column: 13)
!2151 = !DILocation(line: 116, column: 18, scope: !2150)
!2152 = !DILocation(line: 116, column: 13, scope: !2153)
!2153 = !DILexicalBlockFile(scope: !2150, file: !236, discriminator: 1)
!2154 = !DILocation(line: 116, column: 58, scope: !2150)
!2155 = !DILocation(line: 116, column: 13, scope: !2141)
!2156 = !DILocation(line: 117, column: 13, scope: !2150)
!2157 = !DILocation(line: 117, column: 13, scope: !2153)
!2158 = !DILocation(line: 118, column: 17, scope: !2141)
!2159 = !DILocation(line: 118, column: 10, scope: !2141)
!2160 = !DILocation(line: 119, column: 9, scope: !2141)
!2161 = !DILocation(line: 120, column: 10, scope: !2162)
!2162 = distinct !DILexicalBlock(scope: !2133, file: !236, line: 120, column: 10)
!2163 = !DILocation(line: 120, column: 28, scope: !2162)
!2164 = !DILocation(line: 120, column: 10, scope: !2133)
!2165 = !DILocation(line: 121, column: 17, scope: !2162)
!2166 = !DILocation(line: 121, column: 10, scope: !2162)
!2167 = !DILocation(line: 122, column: 18, scope: !2133)
!2168 = !DILocation(line: 122, column: 17, scope: !2133)
!2169 = !DILocation(line: 123, column: 10, scope: !2170)
!2170 = distinct !DILexicalBlock(scope: !2133, file: !236, line: 123, column: 10)
!2171 = !DILocation(line: 123, column: 21, scope: !2170)
!2172 = !DILocation(line: 123, column: 10, scope: !2133)
!2173 = !DILocation(line: 125, column: 18, scope: !2174)
!2174 = distinct !DILexicalBlock(scope: !2175, file: !236, line: 125, column: 13)
!2175 = distinct !DILexicalBlock(scope: !2170, file: !236, line: 124, column: 9)
!2176 = !DILocation(line: 125, column: 13, scope: !2174)
!2177 = !DILocation(line: 125, column: 44, scope: !2174)
!2178 = !DILocation(line: 125, column: 13, scope: !2175)
!2179 = !DILocation(line: 126, column: 13, scope: !2174)
!2180 = !DILocation(line: 126, column: 13, scope: !2181)
!2181 = !DILexicalBlockFile(scope: !2174, file: !236, discriminator: 1)
!2182 = !DILocation(line: 127, column: 16, scope: !2175)
!2183 = !DILocation(line: 127, column: 10, scope: !2175)
!2184 = !DILocation(line: 128, column: 9, scope: !2175)
!2185 = !DILocation(line: 130, column: 10, scope: !2170)
!2186 = !DILocation(line: 130, column: 10, scope: !2187)
!2187 = !DILexicalBlockFile(scope: !2170, file: !236, discriminator: 1)
!2188 = !DILocation(line: 132, column: 7, scope: !2133)
!2189 = !DILocation(line: 133, column: 14, scope: !2133)
!2190 = !DILocation(line: 133, column: 29, scope: !2133)
!2191 = !DILocation(line: 133, column: 7, scope: !2133)
!2192 = !DILocation(line: 134, column: 7, scope: !2133)
!2193 = !DILocation(line: 134, column: 7, scope: !2194)
!2194 = !DILexicalBlockFile(scope: !2133, file: !236, discriminator: 1)
!2195 = !DILocation(line: 135, column: 12, scope: !2133)
!2196 = !DILocation(line: 135, column: 7, scope: !2194)
!2197 = !DILocation(line: 135, column: 7, scope: !2133)
!2198 = !DILocation(line: 139, column: 11, scope: !2199)
!2199 = distinct !DILexicalBlock(scope: !2200, file: !236, line: 139, column: 10)
!2200 = distinct !DILexicalBlock(scope: !2128, file: !236, line: 138, column: 6)
!2201 = !DILocation(line: 139, column: 10, scope: !2199)
!2202 = !DILocation(line: 139, column: 23, scope: !2199)
!2203 = !DILocation(line: 139, column: 10, scope: !2200)
!2204 = !DILocation(line: 140, column: 13, scope: !2199)
!2205 = !DILocation(line: 140, column: 10, scope: !2199)
!2206 = !DILocation(line: 143, column: 14, scope: !2207)
!2207 = distinct !DILexicalBlock(scope: !2199, file: !236, line: 142, column: 9)
!2208 = !DILocation(line: 143, column: 13, scope: !2207)
!2209 = !DILocation(line: 144, column: 10, scope: !2207)
!2210 = !DILocation(line: 144, column: 10, scope: !2211)
!2211 = !DILexicalBlockFile(scope: !2207, file: !236, discriminator: 1)
!2212 = !DILocation(line: 147, column: 11, scope: !2110)
!2213 = !DILocation(line: 147, column: 4, scope: !2110)
!2214 = distinct !DISubprogram(name: "configure_timer", scope: !236, file: !236, line: 150, type: !2215, isLocal: false, isDefinition: true, scopeLine: 151, flags: DIFlagPrototyped, isOptimized: false, unit: !235, variables: !2)
!2215 = !DISubroutineType(types: !2216)
!2216 = !{!12, !2217}
!2217 = !DIBasicType(name: "float", size: 32, align: 32, encoding: DW_ATE_float)
!2218 = !DILocalVariable(name: "interval_sec", arg: 1, scope: !2214, file: !236, line: 150, type: !2217)
!2219 = !DILocation(line: 150, column: 27, scope: !2214)
!2220 = !DILocalVariable(name: "ret_error", scope: !2214, file: !236, line: 152, type: !12)
!2221 = !DILocation(line: 152, column: 8, scope: !2214)
!2222 = !DILocalVariable(name: "timer_conf", scope: !2214, file: !236, line: 153, type: !2223)
!2223 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "itimerval", file: !239, line: 107, size: 128, align: 32, elements: !2224)
!2224 = !{!2225, !2230}
!2225 = !DIDerivedType(tag: DW_TAG_member, name: "it_interval", scope: !2223, file: !239, line: 110, baseType: !2226, size: 64, align: 32)
!2226 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "timeval", file: !332, line: 30, size: 64, align: 32, elements: !2227)
!2227 = !{!2228, !2229}
!2228 = !DIDerivedType(tag: DW_TAG_member, name: "tv_sec", scope: !2226, file: !332, line: 32, baseType: !247, size: 32, align: 32)
!2229 = !DIDerivedType(tag: DW_TAG_member, name: "tv_usec", scope: !2226, file: !332, line: 33, baseType: !251, size: 32, align: 32, offset: 32)
!2230 = !DIDerivedType(tag: DW_TAG_member, name: "it_value", scope: !2223, file: !239, line: 112, baseType: !2226, size: 64, align: 32, offset: 64)
!2231 = !DILocation(line: 153, column: 21, scope: !2214)
!2232 = !DILocation(line: 155, column: 7, scope: !2233)
!2233 = distinct !DILexicalBlock(scope: !2214, file: !236, line: 155, column: 7)
!2234 = !DILocation(line: 155, column: 20, scope: !2233)
!2235 = !DILocation(line: 155, column: 7, scope: !2214)
!2236 = !DILocation(line: 159, column: 18, scope: !2237)
!2237 = distinct !DILexicalBlock(scope: !2233, file: !236, line: 156, column: 6)
!2238 = !DILocation(line: 159, column: 27, scope: !2237)
!2239 = !DILocation(line: 159, column: 34, scope: !2237)
!2240 = !DILocation(line: 160, column: 18, scope: !2237)
!2241 = !DILocation(line: 160, column: 27, scope: !2237)
!2242 = !DILocation(line: 160, column: 35, scope: !2237)
!2243 = !DILocation(line: 161, column: 18, scope: !2237)
!2244 = !DILocation(line: 161, column: 30, scope: !2237)
!2245 = !DILocation(line: 161, column: 37, scope: !2237)
!2246 = !DILocation(line: 162, column: 18, scope: !2237)
!2247 = !DILocation(line: 162, column: 30, scope: !2237)
!2248 = !DILocation(line: 162, column: 38, scope: !2237)
!2249 = !DILocation(line: 163, column: 6, scope: !2237)
!2250 = !DILocation(line: 167, column: 18, scope: !2251)
!2251 = distinct !DILexicalBlock(scope: !2233, file: !236, line: 165, column: 6)
!2252 = !DILocation(line: 167, column: 27, scope: !2251)
!2253 = !DILocation(line: 167, column: 34, scope: !2251)
!2254 = !DILocation(line: 168, column: 18, scope: !2251)
!2255 = !DILocation(line: 168, column: 27, scope: !2251)
!2256 = !DILocation(line: 168, column: 35, scope: !2251)
!2257 = !DILocation(line: 170, column: 47, scope: !2251)
!2258 = !DILocation(line: 170, column: 39, scope: !2251)
!2259 = !DILocation(line: 170, column: 18, scope: !2251)
!2260 = !DILocation(line: 170, column: 30, scope: !2251)
!2261 = !DILocation(line: 170, column: 37, scope: !2251)
!2262 = !DILocation(line: 171, column: 55, scope: !2251)
!2263 = !DILocation(line: 171, column: 79, scope: !2251)
!2264 = !DILocation(line: 171, column: 91, scope: !2251)
!2265 = !DILocation(line: 171, column: 68, scope: !2251)
!2266 = !DILocation(line: 171, column: 67, scope: !2251)
!2267 = !DILocation(line: 171, column: 54, scope: !2251)
!2268 = !DILocation(line: 171, column: 98, scope: !2251)
!2269 = !DILocation(line: 171, column: 40, scope: !2251)
!2270 = !DILocation(line: 171, column: 18, scope: !2251)
!2271 = !DILocation(line: 171, column: 30, scope: !2251)
!2272 = !DILocation(line: 171, column: 38, scope: !2251)
!2273 = !DILocation(line: 175, column: 7, scope: !2274)
!2274 = distinct !DILexicalBlock(scope: !2214, file: !236, line: 175, column: 7)
!2275 = !DILocation(line: 175, column: 50, scope: !2274)
!2276 = !DILocation(line: 175, column: 7, scope: !2214)
!2277 = !DILocation(line: 177, column: 7, scope: !2278)
!2278 = distinct !DILexicalBlock(scope: !2274, file: !236, line: 176, column: 6)
!2279 = !DILocation(line: 178, column: 16, scope: !2278)
!2280 = !DILocation(line: 179, column: 6, scope: !2278)
!2281 = !DILocation(line: 182, column: 17, scope: !2282)
!2282 = distinct !DILexicalBlock(scope: !2274, file: !236, line: 181, column: 6)
!2283 = !DILocation(line: 182, column: 16, scope: !2282)
!2284 = !DILocation(line: 183, column: 7, scope: !2282)
!2285 = !DILocation(line: 183, column: 7, scope: !2286)
!2286 = !DILexicalBlockFile(scope: !2282, file: !236, discriminator: 1)
!2287 = !DILocation(line: 183, column: 7, scope: !2288)
!2288 = !DILexicalBlockFile(scope: !2282, file: !236, discriminator: 2)
!2289 = !DILocation(line: 183, column: 7, scope: !2290)
!2290 = !DILexicalBlockFile(scope: !2282, file: !236, discriminator: 3)
!2291 = !DILocation(line: 185, column: 11, scope: !2214)
!2292 = !DILocation(line: 185, column: 4, scope: !2214)
!2293 = distinct !DISubprogram(name: "daemonize", scope: !236, file: !236, line: 189, type: !568, isLocal: false, isDefinition: true, scopeLine: 190, flags: DIFlagPrototyped, isOptimized: false, unit: !235, variables: !2)
!2294 = !DILocalVariable(name: "working_dir", arg: 1, scope: !2293, file: !236, line: 189, type: !18)
!2295 = !DILocation(line: 189, column: 21, scope: !2293)
!2296 = !DILocalVariable(name: "ret_error", scope: !2293, file: !236, line: 191, type: !12)
!2297 = !DILocation(line: 191, column: 8, scope: !2293)
!2298 = !DILocalVariable(name: "child_pid", scope: !2293, file: !236, line: 192, type: !8)
!2299 = !DILocation(line: 192, column: 10, scope: !2293)
!2300 = !DILocalVariable(name: "null_fd_rd", scope: !2293, file: !236, line: 193, type: !12)
!2301 = !DILocation(line: 193, column: 8, scope: !2293)
!2302 = !DILocalVariable(name: "null_fd_wr", scope: !2293, file: !236, line: 193, type: !12)
!2303 = !DILocation(line: 193, column: 20, scope: !2293)
!2304 = !DILocation(line: 195, column: 16, scope: !2293)
!2305 = !DILocation(line: 195, column: 14, scope: !2293)
!2306 = !DILocation(line: 196, column: 7, scope: !2307)
!2307 = distinct !DILexicalBlock(scope: !2293, file: !236, line: 196, column: 7)
!2308 = !DILocation(line: 196, column: 17, scope: !2307)
!2309 = !DILocation(line: 196, column: 7, scope: !2293)
!2310 = !DILocation(line: 198, column: 10, scope: !2311)
!2311 = distinct !DILexicalBlock(scope: !2312, file: !236, line: 198, column: 10)
!2312 = distinct !DILexicalBlock(scope: !2307, file: !236, line: 197, column: 6)
!2313 = !DILocation(line: 198, column: 20, scope: !2311)
!2314 = !DILocation(line: 198, column: 10, scope: !2312)
!2315 = !DILocation(line: 199, column: 10, scope: !2311)
!2316 = !DILocation(line: 202, column: 10, scope: !2317)
!2317 = distinct !DILexicalBlock(scope: !2312, file: !236, line: 202, column: 10)
!2318 = !DILocation(line: 202, column: 19, scope: !2317)
!2319 = !DILocation(line: 202, column: 10, scope: !2312)
!2320 = !DILocation(line: 206, column: 10, scope: !2321)
!2321 = distinct !DILexicalBlock(scope: !2317, file: !236, line: 203, column: 9)
!2322 = !DILocation(line: 207, column: 10, scope: !2321)
!2323 = !DILocation(line: 209, column: 22, scope: !2321)
!2324 = !DILocation(line: 209, column: 20, scope: !2321)
!2325 = !DILocation(line: 210, column: 13, scope: !2326)
!2326 = distinct !DILexicalBlock(scope: !2321, file: !236, line: 210, column: 13)
!2327 = !DILocation(line: 210, column: 23, scope: !2326)
!2328 = !DILocation(line: 210, column: 13, scope: !2321)
!2329 = !DILocation(line: 212, column: 16, scope: !2330)
!2330 = distinct !DILexicalBlock(scope: !2331, file: !236, line: 212, column: 16)
!2331 = distinct !DILexicalBlock(scope: !2326, file: !236, line: 211, column: 12)
!2332 = !DILocation(line: 212, column: 26, scope: !2330)
!2333 = !DILocation(line: 212, column: 16, scope: !2331)
!2334 = !DILocation(line: 213, column: 16, scope: !2330)
!2335 = !DILocation(line: 215, column: 13, scope: !2331)
!2336 = !DILocation(line: 217, column: 19, scope: !2331)
!2337 = !DILocation(line: 217, column: 13, scope: !2331)
!2338 = !DILocation(line: 219, column: 24, scope: !2331)
!2339 = !DILocation(line: 219, column: 23, scope: !2331)
!2340 = !DILocation(line: 220, column: 16, scope: !2341)
!2341 = distinct !DILexicalBlock(scope: !2331, file: !236, line: 220, column: 16)
!2342 = !DILocation(line: 220, column: 27, scope: !2341)
!2343 = !DILocation(line: 220, column: 16, scope: !2331)
!2344 = !DILocation(line: 222, column: 21, scope: !2345)
!2345 = distinct !DILexicalBlock(scope: !2341, file: !236, line: 221, column: 15)
!2346 = !DILocation(line: 222, column: 16, scope: !2345)
!2347 = !DILocation(line: 223, column: 22, scope: !2345)
!2348 = !DILocation(line: 223, column: 16, scope: !2345)
!2349 = !DILocation(line: 224, column: 15, scope: !2345)
!2350 = !DILocation(line: 226, column: 16, scope: !2341)
!2351 = !DILocation(line: 227, column: 24, scope: !2331)
!2352 = !DILocation(line: 227, column: 23, scope: !2331)
!2353 = !DILocation(line: 228, column: 16, scope: !2354)
!2354 = distinct !DILexicalBlock(scope: !2331, file: !236, line: 228, column: 16)
!2355 = !DILocation(line: 228, column: 27, scope: !2354)
!2356 = !DILocation(line: 228, column: 16, scope: !2331)
!2357 = !DILocation(line: 230, column: 21, scope: !2358)
!2358 = distinct !DILexicalBlock(scope: !2354, file: !236, line: 229, column: 15)
!2359 = !DILocation(line: 230, column: 16, scope: !2358)
!2360 = !DILocation(line: 231, column: 21, scope: !2358)
!2361 = !DILocation(line: 231, column: 16, scope: !2358)
!2362 = !DILocation(line: 232, column: 22, scope: !2358)
!2363 = !DILocation(line: 232, column: 16, scope: !2358)
!2364 = !DILocation(line: 233, column: 15, scope: !2358)
!2365 = !DILocation(line: 235, column: 16, scope: !2354)
!2366 = !DILocation(line: 237, column: 12, scope: !2331)
!2367 = !DILocation(line: 240, column: 23, scope: !2368)
!2368 = distinct !DILexicalBlock(scope: !2326, file: !236, line: 239, column: 12)
!2369 = !DILocation(line: 240, column: 22, scope: !2368)
!2370 = !DILocation(line: 241, column: 21, scope: !2368)
!2371 = !DILocation(line: 241, column: 87, scope: !2368)
!2372 = !DILocation(line: 241, column: 13, scope: !2373)
!2373 = !DILexicalBlockFile(scope: !2368, file: !236, discriminator: 1)
!2374 = !DILocation(line: 245, column: 9, scope: !2321)
!2375 = !DILocation(line: 248, column: 20, scope: !2376)
!2376 = distinct !DILexicalBlock(scope: !2317, file: !236, line: 247, column: 9)
!2377 = !DILocation(line: 248, column: 19, scope: !2376)
!2378 = !DILocation(line: 249, column: 18, scope: !2376)
!2379 = !DILocation(line: 249, column: 107, scope: !2376)
!2380 = !DILocation(line: 249, column: 10, scope: !2381)
!2381 = !DILexicalBlockFile(scope: !2376, file: !236, discriminator: 1)
!2382 = !DILocation(line: 252, column: 6, scope: !2312)
!2383 = !DILocation(line: 255, column: 17, scope: !2384)
!2384 = distinct !DILexicalBlock(scope: !2307, file: !236, line: 254, column: 6)
!2385 = !DILocation(line: 255, column: 16, scope: !2384)
!2386 = !DILocation(line: 256, column: 15, scope: !2384)
!2387 = !DILocation(line: 256, column: 80, scope: !2384)
!2388 = !DILocation(line: 256, column: 7, scope: !2389)
!2389 = !DILexicalBlockFile(scope: !2384, file: !236, discriminator: 1)
!2390 = !DILocation(line: 260, column: 11, scope: !2293)
!2391 = !DILocation(line: 260, column: 4, scope: !2293)
!2392 = distinct !DISubprogram(name: "get_localtime_str", scope: !256, file: !256, line: 15, type: !2393, isLocal: false, isDefinition: true, scopeLine: 16, flags: DIFlagPrototyped, isOptimized: false, unit: !255, variables: !2)
!2393 = !DISubroutineType(types: !2394)
!2394 = !{null, !18, !311}
!2395 = !DILocalVariable(name: "cur_time_str", arg: 1, scope: !2392, file: !256, line: 15, type: !18)
!2396 = !DILocation(line: 15, column: 30, scope: !2392)
!2397 = !DILocalVariable(name: "cur_time_str_len", arg: 2, scope: !2392, file: !256, line: 15, type: !311)
!2398 = !DILocation(line: 15, column: 51, scope: !2392)
!2399 = !DILocalVariable(name: "cur_time", scope: !2392, file: !256, line: 17, type: !245)
!2400 = !DILocation(line: 17, column: 11, scope: !2392)
!2401 = !DILocalVariable(name: "cur_time_struct", scope: !2392, file: !256, line: 18, type: !2402)
!2402 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !2403, size: 32, align: 32)
!2403 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "tm", file: !246, line: 133, size: 352, align: 32, elements: !2404)
!2404 = !{!2405, !2406, !2407, !2408, !2409, !2410, !2411, !2412, !2413, !2414, !2415}
!2405 = !DIDerivedType(tag: DW_TAG_member, name: "tm_sec", scope: !2403, file: !246, line: 135, baseType: !12, size: 32, align: 32)
!2406 = !DIDerivedType(tag: DW_TAG_member, name: "tm_min", scope: !2403, file: !246, line: 136, baseType: !12, size: 32, align: 32, offset: 32)
!2407 = !DIDerivedType(tag: DW_TAG_member, name: "tm_hour", scope: !2403, file: !246, line: 137, baseType: !12, size: 32, align: 32, offset: 64)
!2408 = !DIDerivedType(tag: DW_TAG_member, name: "tm_mday", scope: !2403, file: !246, line: 138, baseType: !12, size: 32, align: 32, offset: 96)
!2409 = !DIDerivedType(tag: DW_TAG_member, name: "tm_mon", scope: !2403, file: !246, line: 139, baseType: !12, size: 32, align: 32, offset: 128)
!2410 = !DIDerivedType(tag: DW_TAG_member, name: "tm_year", scope: !2403, file: !246, line: 140, baseType: !12, size: 32, align: 32, offset: 160)
!2411 = !DIDerivedType(tag: DW_TAG_member, name: "tm_wday", scope: !2403, file: !246, line: 141, baseType: !12, size: 32, align: 32, offset: 192)
!2412 = !DIDerivedType(tag: DW_TAG_member, name: "tm_yday", scope: !2403, file: !246, line: 142, baseType: !12, size: 32, align: 32, offset: 224)
!2413 = !DIDerivedType(tag: DW_TAG_member, name: "tm_isdst", scope: !2403, file: !246, line: 143, baseType: !12, size: 32, align: 32, offset: 256)
!2414 = !DIDerivedType(tag: DW_TAG_member, name: "tm_gmtoff", scope: !2403, file: !246, line: 146, baseType: !248, size: 32, align: 32, offset: 288)
!2415 = !DIDerivedType(tag: DW_TAG_member, name: "tm_zone", scope: !2403, file: !246, line: 147, baseType: !2113, size: 32, align: 32, offset: 320)
!2416 = !DILocation(line: 18, column: 15, scope: !2392)
!2417 = !DILocation(line: 20, column: 15, scope: !2392)
!2418 = !DILocation(line: 20, column: 13, scope: !2392)
!2419 = !DILocation(line: 21, column: 7, scope: !2420)
!2420 = distinct !DILexicalBlock(scope: !2392, file: !256, line: 21, column: 7)
!2421 = !DILocation(line: 21, column: 16, scope: !2420)
!2422 = !DILocation(line: 21, column: 7, scope: !2392)
!2423 = !DILocation(line: 23, column: 25, scope: !2424)
!2424 = distinct !DILexicalBlock(scope: !2420, file: !256, line: 22, column: 6)
!2425 = !DILocation(line: 23, column: 23, scope: !2424)
!2426 = !DILocation(line: 24, column: 19, scope: !2427)
!2427 = distinct !DILexicalBlock(scope: !2424, file: !256, line: 24, column: 10)
!2428 = !DILocation(line: 24, column: 33, scope: !2427)
!2429 = !DILocation(line: 24, column: 72, scope: !2427)
!2430 = !DILocation(line: 24, column: 10, scope: !2427)
!2431 = !DILocation(line: 24, column: 88, scope: !2427)
!2432 = !DILocation(line: 24, column: 10, scope: !2424)
!2433 = !DILocation(line: 25, column: 13, scope: !2434)
!2434 = distinct !DILexicalBlock(scope: !2427, file: !256, line: 25, column: 13)
!2435 = !DILocation(line: 25, column: 29, scope: !2434)
!2436 = !DILocation(line: 25, column: 13, scope: !2427)
!2437 = !DILocation(line: 26, column: 13, scope: !2434)
!2438 = !DILocation(line: 26, column: 28, scope: !2434)
!2439 = !DILocation(line: 25, column: 30, scope: !2440)
!2440 = !DILexicalBlockFile(scope: !2434, file: !256, discriminator: 1)
!2441 = !DILocation(line: 27, column: 6, scope: !2424)
!2442 = !DILocation(line: 30, column: 10, scope: !2443)
!2443 = distinct !DILexicalBlock(scope: !2444, file: !256, line: 30, column: 10)
!2444 = distinct !DILexicalBlock(scope: !2420, file: !256, line: 29, column: 6)
!2445 = !DILocation(line: 30, column: 26, scope: !2443)
!2446 = !DILocation(line: 30, column: 10, scope: !2444)
!2447 = !DILocation(line: 31, column: 10, scope: !2443)
!2448 = !DILocation(line: 31, column: 25, scope: !2443)
!2449 = !DILocation(line: 34, column: 3, scope: !2392)
!2450 = distinct !DISubprogram(name: "msg_printf", scope: !256, file: !256, line: 39, type: !2451, isLocal: false, isDefinition: true, scopeLine: 40, flags: DIFlagPrototyped, isOptimized: false, unit: !255, variables: !2)
!2451 = !DISubroutineType(types: !2452)
!2452 = !{!12, !261, !2113, null}
!2453 = !DILocalVariable(name: "out_file_handle", arg: 1, scope: !2450, file: !256, line: 39, type: !261)
!2454 = !DILocation(line: 39, column: 22, scope: !2450)
!2455 = !DILocalVariable(name: "format", arg: 2, scope: !2450, file: !256, line: 39, type: !2113)
!2456 = !DILocation(line: 39, column: 51, scope: !2450)
!2457 = !DILocalVariable(name: "ret", scope: !2450, file: !256, line: 41, type: !12)
!2458 = !DILocation(line: 41, column: 8, scope: !2450)
!2459 = !DILocation(line: 42, column: 7, scope: !2460)
!2460 = distinct !DILexicalBlock(scope: !2450, file: !256, line: 42, column: 7)
!2461 = !DILocation(line: 42, column: 24, scope: !2460)
!2462 = !DILocation(line: 42, column: 27, scope: !2463)
!2463 = !DILexicalBlockFile(scope: !2460, file: !256, discriminator: 1)
!2464 = !DILocation(line: 42, column: 43, scope: !2463)
!2465 = !DILocation(line: 42, column: 7, scope: !2463)
!2466 = !DILocalVariable(name: "printf_ret", scope: !2467, file: !256, line: 44, type: !12)
!2467 = distinct !DILexicalBlock(scope: !2460, file: !256, line: 43, column: 6)
!2468 = !DILocation(line: 44, column: 11, scope: !2467)
!2469 = !DILocalVariable(name: "fprintf_ret", scope: !2467, file: !256, line: 44, type: !12)
!2470 = !DILocation(line: 44, column: 24, scope: !2467)
!2471 = !DILocalVariable(name: "arglist", scope: !2467, file: !256, line: 45, type: !2472)
!2472 = !DIDerivedType(tag: DW_TAG_typedef, name: "va_list", file: !263, line: 79, baseType: !2473)
!2473 = !DIDerivedType(tag: DW_TAG_typedef, name: "__gnuc_va_list", file: !2474, line: 50, baseType: !2475)
!2474 = !DIFile(filename: "/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/../lib/clang/3.9.0/include/stdarg.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/alarm4pi-cb")
!2475 = !DIDerivedType(tag: DW_TAG_typedef, name: "__builtin_va_list", file: !256, line: 45, baseType: !2476)
!2476 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "__va_list", file: !256, line: 45, size: 32, align: 32, elements: !2477)
!2477 = !{!2478}
!2478 = !DIDerivedType(tag: DW_TAG_member, name: "__ap", scope: !2476, file: !256, line: 45, baseType: !32, size: 32, align: 32)
!2479 = !DILocation(line: 45, column: 15, scope: !2467)
!2480 = !DILocalVariable(name: "cur_time_str", scope: !2467, file: !256, line: 46, type: !2481)
!2481 = !DICompositeType(tag: DW_TAG_array_type, baseType: !19, size: 160, align: 8, elements: !2482)
!2482 = !{!2483}
!2483 = !DISubrange(count: 20)
!2484 = !DILocation(line: 46, column: 12, scope: !2467)
!2485 = !DILocation(line: 48, column: 24, scope: !2467)
!2486 = !DILocation(line: 48, column: 6, scope: !2467)
!2487 = !DILocation(line: 49, column: 7, scope: !2467)
!2488 = !DILocation(line: 50, column: 10, scope: !2489)
!2489 = distinct !DILexicalBlock(scope: !2467, file: !256, line: 50, column: 10)
!2490 = !DILocation(line: 50, column: 10, scope: !2467)
!2491 = !DILocation(line: 51, column: 29, scope: !2489)
!2492 = !DILocation(line: 51, column: 21, scope: !2489)
!2493 = !DILocation(line: 51, column: 20, scope: !2489)
!2494 = !DILocation(line: 51, column: 10, scope: !2489)
!2495 = !DILocation(line: 52, column: 10, scope: !2496)
!2496 = distinct !DILexicalBlock(scope: !2467, file: !256, line: 52, column: 10)
!2497 = !DILocation(line: 52, column: 26, scope: !2496)
!2498 = !DILocation(line: 52, column: 10, scope: !2467)
!2499 = !DILocation(line: 54, column: 18, scope: !2500)
!2500 = distinct !DILexicalBlock(scope: !2496, file: !256, line: 53, column: 9)
!2501 = !DILocation(line: 54, column: 43, scope: !2500)
!2502 = !DILocation(line: 54, column: 10, scope: !2500)
!2503 = !DILocation(line: 55, column: 31, scope: !2500)
!2504 = !DILocation(line: 55, column: 48, scope: !2500)
!2505 = !DILocation(line: 55, column: 22, scope: !2500)
!2506 = !DILocation(line: 55, column: 21, scope: !2500)
!2507 = !DILocation(line: 56, column: 9, scope: !2500)
!2508 = !DILocation(line: 57, column: 7, scope: !2467)
!2509 = !DILocation(line: 58, column: 12, scope: !2467)
!2510 = !DILocation(line: 58, column: 22, scope: !2467)
!2511 = !DILocation(line: 58, column: 11, scope: !2467)
!2512 = !DILocation(line: 58, column: 27, scope: !2513)
!2513 = !DILexicalBlockFile(scope: !2467, file: !256, discriminator: 1)
!2514 = !DILocation(line: 58, column: 11, scope: !2513)
!2515 = !DILocation(line: 58, column: 38, scope: !2516)
!2516 = !DILexicalBlockFile(scope: !2467, file: !256, discriminator: 2)
!2517 = !DILocation(line: 58, column: 11, scope: !2516)
!2518 = !DILocation(line: 58, column: 11, scope: !2519)
!2519 = !DILexicalBlockFile(scope: !2467, file: !256, discriminator: 3)
!2520 = !DILocation(line: 58, column: 10, scope: !2519)
!2521 = !DILocation(line: 59, column: 6, scope: !2467)
!2522 = !DILocation(line: 61, column: 10, scope: !2460)
!2523 = !DILocation(line: 62, column: 11, scope: !2450)
!2524 = !DILocation(line: 62, column: 4, scope: !2450)
!2525 = distinct !DISubprogram(name: "open_msg_file", scope: !256, file: !256, line: 67, type: !2526, isLocal: false, isDefinition: true, scopeLine: 68, flags: DIFlagPrototyped, isOptimized: false, unit: !255, variables: !2)
!2526 = !DISubroutineType(types: !2527)
!2527 = !{!261, !2113, !248}
!2528 = !DILocalVariable(name: "file_name", arg: 1, scope: !2525, file: !256, line: 67, type: !2113)
!2529 = !DILocation(line: 67, column: 33, scope: !2525)
!2530 = !DILocalVariable(name: "max_file_len", arg: 2, scope: !2525, file: !256, line: 67, type: !248)
!2531 = !DILocation(line: 67, column: 49, scope: !2525)
!2532 = !DILocalVariable(name: "file_handle", scope: !2525, file: !256, line: 69, type: !261)
!2533 = !DILocation(line: 69, column: 10, scope: !2525)
!2534 = !DILocation(line: 70, column: 22, scope: !2525)
!2535 = !DILocation(line: 70, column: 16, scope: !2525)
!2536 = !DILocation(line: 70, column: 15, scope: !2525)
!2537 = !DILocation(line: 71, column: 7, scope: !2538)
!2538 = distinct !DILexicalBlock(scope: !2525, file: !256, line: 71, column: 7)
!2539 = !DILocation(line: 71, column: 7, scope: !2525)
!2540 = !DILocalVariable(name: "log_size", scope: !2541, file: !256, line: 73, type: !248)
!2541 = distinct !DILexicalBlock(scope: !2538, file: !256, line: 72, column: 6)
!2542 = !DILocation(line: 73, column: 12, scope: !2541)
!2543 = !DILocalVariable(name: "log_size_loaded", scope: !2541, file: !256, line: 74, type: !311)
!2544 = !DILocation(line: 74, column: 14, scope: !2541)
!2545 = !DILocalVariable(name: "cur_time_str", scope: !2541, file: !256, line: 75, type: !2481)
!2546 = !DILocation(line: 75, column: 12, scope: !2541)
!2547 = !DILocation(line: 77, column: 20, scope: !2541)
!2548 = !DILocation(line: 77, column: 13, scope: !2541)
!2549 = !DILocation(line: 77, column: 7, scope: !2550)
!2550 = !DILexicalBlockFile(scope: !2541, file: !256, discriminator: 1)
!2551 = !DILocation(line: 78, column: 14, scope: !2541)
!2552 = !DILocation(line: 78, column: 7, scope: !2541)
!2553 = !DILocation(line: 80, column: 13, scope: !2541)
!2554 = !DILocation(line: 80, column: 7, scope: !2541)
!2555 = !DILocation(line: 81, column: 24, scope: !2541)
!2556 = !DILocation(line: 81, column: 18, scope: !2541)
!2557 = !DILocation(line: 81, column: 16, scope: !2541)
!2558 = !DILocation(line: 83, column: 11, scope: !2559)
!2559 = distinct !DILexicalBlock(scope: !2541, file: !256, line: 83, column: 11)
!2560 = !DILocation(line: 83, column: 22, scope: !2559)
!2561 = !DILocation(line: 83, column: 20, scope: !2559)
!2562 = !DILocation(line: 83, column: 11, scope: !2541)
!2563 = !DILocalVariable(name: "log_file_buf", scope: !2564, file: !256, line: 85, type: !18)
!2564 = distinct !DILexicalBlock(scope: !2559, file: !256, line: 84, column: 9)
!2565 = !DILocation(line: 85, column: 16, scope: !2564)
!2566 = !DILocation(line: 87, column: 38, scope: !2564)
!2567 = !DILocation(line: 87, column: 50, scope: !2564)
!2568 = !DILocation(line: 87, column: 31, scope: !2564)
!2569 = !DILocation(line: 87, column: 22, scope: !2564)
!2570 = !DILocation(line: 88, column: 13, scope: !2571)
!2571 = distinct !DILexicalBlock(scope: !2564, file: !256, line: 88, column: 13)
!2572 = !DILocation(line: 88, column: 13, scope: !2564)
!2573 = !DILocation(line: 90, column: 19, scope: !2574)
!2574 = distinct !DILexicalBlock(scope: !2571, file: !256, line: 89, column: 12)
!2575 = !DILocation(line: 90, column: 33, scope: !2574)
!2576 = !DILocation(line: 90, column: 32, scope: !2574)
!2577 = !DILocation(line: 90, column: 13, scope: !2574)
!2578 = !DILocation(line: 91, column: 37, scope: !2574)
!2579 = !DILocation(line: 91, column: 65, scope: !2574)
!2580 = !DILocation(line: 91, column: 79, scope: !2574)
!2581 = !DILocation(line: 91, column: 31, scope: !2574)
!2582 = !DILocation(line: 91, column: 29, scope: !2574)
!2583 = !DILocation(line: 92, column: 20, scope: !2574)
!2584 = !DILocation(line: 92, column: 13, scope: !2574)
!2585 = !DILocation(line: 93, column: 18, scope: !2574)
!2586 = !DILocation(line: 93, column: 13, scope: !2574)
!2587 = !DILocation(line: 94, column: 33, scope: !2574)
!2588 = !DILocation(line: 94, column: 27, scope: !2574)
!2589 = !DILocation(line: 94, column: 25, scope: !2574)
!2590 = !DILocation(line: 95, column: 17, scope: !2591)
!2591 = distinct !DILexicalBlock(scope: !2574, file: !256, line: 95, column: 17)
!2592 = !DILocation(line: 95, column: 17, scope: !2574)
!2593 = !DILocation(line: 97, column: 34, scope: !2594)
!2594 = distinct !DILexicalBlock(scope: !2591, file: !256, line: 96, column: 15)
!2595 = !DILocation(line: 97, column: 16, scope: !2594)
!2596 = !DILocation(line: 99, column: 24, scope: !2594)
!2597 = !DILocation(line: 99, column: 73, scope: !2594)
!2598 = !DILocation(line: 99, column: 16, scope: !2594)
!2599 = !DILocation(line: 100, column: 23, scope: !2594)
!2600 = !DILocation(line: 100, column: 51, scope: !2594)
!2601 = !DILocation(line: 100, column: 68, scope: !2594)
!2602 = !DILocation(line: 100, column: 16, scope: !2594)
!2603 = !DILocation(line: 101, column: 15, scope: !2594)
!2604 = !DILocation(line: 102, column: 12, scope: !2574)
!2605 = !DILocation(line: 103, column: 9, scope: !2564)
!2606 = !DILocation(line: 105, column: 10, scope: !2607)
!2607 = distinct !DILexicalBlock(scope: !2541, file: !256, line: 105, column: 10)
!2608 = !DILocation(line: 105, column: 10, scope: !2541)
!2609 = !DILocation(line: 107, column: 28, scope: !2610)
!2610 = distinct !DILexicalBlock(scope: !2607, file: !256, line: 106, column: 9)
!2611 = !DILocation(line: 107, column: 10, scope: !2610)
!2612 = !DILocation(line: 108, column: 18, scope: !2610)
!2613 = !DILocation(line: 108, column: 99, scope: !2610)
!2614 = !DILocation(line: 108, column: 10, scope: !2610)
!2615 = !DILocation(line: 109, column: 18, scope: !2610)
!2616 = !DILocation(line: 109, column: 63, scope: !2610)
!2617 = !DILocation(line: 109, column: 10, scope: !2610)
!2618 = !DILocation(line: 110, column: 9, scope: !2610)
!2619 = !DILocation(line: 111, column: 6, scope: !2541)
!2620 = !DILocation(line: 112, column: 11, scope: !2525)
!2621 = !DILocation(line: 112, column: 4, scope: !2525)
!2622 = distinct !DISubprogram(name: "close_log_file", scope: !256, file: !256, line: 116, type: !2623, isLocal: false, isDefinition: true, scopeLine: 117, flags: DIFlagPrototyped, isOptimized: false, unit: !255, variables: !2)
!2623 = !DISubroutineType(types: !2624)
!2624 = !{null, !261}
!2625 = !DILocalVariable(name: "file_handle", arg: 1, scope: !2622, file: !256, line: 116, type: !261)
!2626 = !DILocation(line: 116, column: 27, scope: !2622)
!2627 = !DILocation(line: 118, column: 7, scope: !2628)
!2628 = distinct !DILexicalBlock(scope: !2622, file: !256, line: 118, column: 7)
!2629 = !DILocation(line: 118, column: 7, scope: !2622)
!2630 = !DILocalVariable(name: "cur_time_str", scope: !2631, file: !256, line: 120, type: !2481)
!2631 = distinct !DILexicalBlock(scope: !2628, file: !256, line: 119, column: 6)
!2632 = !DILocation(line: 120, column: 12, scope: !2631)
!2633 = !DILocation(line: 122, column: 25, scope: !2631)
!2634 = !DILocation(line: 122, column: 7, scope: !2631)
!2635 = !DILocation(line: 123, column: 15, scope: !2631)
!2636 = !DILocation(line: 123, column: 64, scope: !2631)
!2637 = !DILocation(line: 123, column: 7, scope: !2631)
!2638 = !DILocation(line: 124, column: 14, scope: !2631)
!2639 = !DILocation(line: 124, column: 7, scope: !2631)
!2640 = !DILocation(line: 125, column: 6, scope: !2631)
!2641 = !DILocation(line: 126, column: 3, scope: !2622)
!2642 = distinct !DISubprogram(name: "open_log_files", scope: !256, file: !256, line: 128, type: !346, isLocal: false, isDefinition: true, scopeLine: 129, flags: DIFlagPrototyped, isOptimized: false, unit: !255, variables: !2)
!2643 = !DILocation(line: 130, column: 20, scope: !2642)
!2644 = !DILocation(line: 130, column: 19, scope: !2642)
!2645 = !DILocation(line: 131, column: 22, scope: !2642)
!2646 = !DILocation(line: 131, column: 21, scope: !2642)
!2647 = !DILocation(line: 132, column: 11, scope: !2642)
!2648 = !DILocation(line: 132, column: 27, scope: !2642)
!2649 = !DILocation(line: 132, column: 35, scope: !2642)
!2650 = !DILocation(line: 132, column: 38, scope: !2651)
!2651 = !DILexicalBlockFile(scope: !2642, file: !256, discriminator: 1)
!2652 = !DILocation(line: 132, column: 56, scope: !2651)
!2653 = !DILocation(line: 132, column: 35, scope: !2651)
!2654 = !DILocation(line: 132, column: 35, scope: !2655)
!2655 = !DILexicalBlockFile(scope: !2642, file: !256, discriminator: 2)
!2656 = !DILocation(line: 132, column: 4, scope: !2655)
!2657 = distinct !DISubprogram(name: "close_log_files", scope: !256, file: !256, line: 135, type: !438, isLocal: false, isDefinition: true, scopeLine: 136, flags: DIFlagPrototyped, isOptimized: false, unit: !255, variables: !2)
!2658 = !DILocation(line: 137, column: 19, scope: !2657)
!2659 = !DILocation(line: 137, column: 4, scope: !2657)
!2660 = !DILocation(line: 138, column: 19, scope: !2657)
!2661 = !DILocation(line: 138, column: 4, scope: !2657)
!2662 = !DILocation(line: 139, column: 3, scope: !2657)
!2663 = distinct !DISubprogram(name: "GPIO_export", scope: !320, file: !320, line: 15, type: !2664, isLocal: false, isDefinition: true, scopeLine: 16, flags: DIFlagPrototyped, isOptimized: false, unit: !319, variables: !2)
!2664 = !DISubroutineType(types: !2665)
!2665 = !{!12, !12}
!2666 = !DILocalVariable(name: "pin", arg: 1, scope: !2663, file: !320, line: 15, type: !12)
!2667 = !DILocation(line: 15, column: 21, scope: !2663)
!2668 = !DILocalVariable(name: "name_buffer", scope: !2663, file: !320, line: 17, type: !2669)
!2669 = !DICompositeType(tag: DW_TAG_array_type, baseType: !19, size: 32, align: 8, elements: !1629)
!2670 = !DILocation(line: 17, column: 9, scope: !2663)
!2671 = !DILocalVariable(name: "bytes_written", scope: !2663, file: !320, line: 18, type: !2672)
!2672 = !DIDerivedType(tag: DW_TAG_typedef, name: "ssize_t", file: !9, line: 109, baseType: !2673)
!2673 = !DIDerivedType(tag: DW_TAG_typedef, name: "__ssize_t", file: !11, line: 172, baseType: !12)
!2674 = !DILocation(line: 18, column: 12, scope: !2663)
!2675 = !DILocalVariable(name: "fd", scope: !2663, file: !320, line: 19, type: !12)
!2676 = !DILocation(line: 19, column: 8, scope: !2663)
!2677 = !DILocalVariable(name: "ret_err", scope: !2663, file: !320, line: 20, type: !12)
!2678 = !DILocation(line: 20, column: 8, scope: !2663)
!2679 = !DILocation(line: 22, column: 9, scope: !2663)
!2680 = !DILocation(line: 22, column: 7, scope: !2663)
!2681 = !DILocation(line: 23, column: 13, scope: !2682)
!2682 = distinct !DILexicalBlock(scope: !2663, file: !320, line: 23, column: 7)
!2683 = !DILocation(line: 23, column: 10, scope: !2682)
!2684 = !DILocation(line: 23, column: 7, scope: !2663)
!2685 = !DILocalVariable(name: "path", scope: !2686, file: !320, line: 25, type: !2687)
!2686 = distinct !DILexicalBlock(scope: !2682, file: !320, line: 24, column: 6)
!2687 = !DICompositeType(tag: DW_TAG_array_type, baseType: !19, size: 272, align: 8, elements: !2688)
!2688 = !{!2689}
!2689 = !DISubrange(count: 34)
!2690 = !DILocation(line: 25, column: 12, scope: !2686)
!2691 = !DILocalVariable(name: "fs_struct_created", scope: !2686, file: !320, line: 26, type: !12)
!2692 = !DILocation(line: 26, column: 11, scope: !2686)
!2693 = !DILocalVariable(name: "n_wait_cycle", scope: !2686, file: !320, line: 27, type: !12)
!2694 = !DILocation(line: 27, column: 11, scope: !2686)
!2695 = !DILocation(line: 29, column: 32, scope: !2686)
!2696 = !DILocation(line: 29, column: 74, scope: !2686)
!2697 = !DILocation(line: 29, column: 23, scope: !2686)
!2698 = !DILocation(line: 29, column: 21, scope: !2686)
!2699 = !DILocation(line: 30, column: 13, scope: !2686)
!2700 = !DILocation(line: 30, column: 17, scope: !2686)
!2701 = !DILocation(line: 30, column: 30, scope: !2686)
!2702 = !DILocation(line: 30, column: 7, scope: !2686)
!2703 = !DILocation(line: 31, column: 13, scope: !2686)
!2704 = !DILocation(line: 31, column: 7, scope: !2686)
!2705 = !DILocation(line: 34, column: 16, scope: !2686)
!2706 = !DILocation(line: 34, column: 86, scope: !2686)
!2707 = !DILocation(line: 34, column: 7, scope: !2686)
!2708 = !DILocation(line: 35, column: 24, scope: !2686)
!2709 = !DILocation(line: 36, column: 19, scope: !2686)
!2710 = !DILocation(line: 37, column: 7, scope: !2686)
!2711 = distinct !{!2711, !2710}
!2712 = !DILocation(line: 39, column: 10, scope: !2713)
!2713 = distinct !DILexicalBlock(scope: !2686, file: !320, line: 38, column: 9)
!2714 = !DILocation(line: 41, column: 20, scope: !2713)
!2715 = !DILocation(line: 41, column: 15, scope: !2713)
!2716 = !DILocation(line: 41, column: 13, scope: !2713)
!2717 = !DILocation(line: 42, column: 19, scope: !2718)
!2718 = distinct !DILexicalBlock(scope: !2713, file: !320, line: 42, column: 13)
!2719 = !DILocation(line: 42, column: 16, scope: !2718)
!2720 = !DILocation(line: 42, column: 13, scope: !2713)
!2721 = !DILocation(line: 44, column: 30, scope: !2722)
!2722 = distinct !DILexicalBlock(scope: !2718, file: !320, line: 43, column: 12)
!2723 = !DILocation(line: 45, column: 19, scope: !2722)
!2724 = !DILocation(line: 45, column: 13, scope: !2722)
!2725 = !DILocation(line: 46, column: 12, scope: !2722)
!2726 = !DILocation(line: 48, column: 30, scope: !2718)
!2727 = !DILocation(line: 49, column: 9, scope: !2713)
!2728 = !DILocation(line: 50, column: 14, scope: !2686)
!2729 = !DILocation(line: 50, column: 32, scope: !2686)
!2730 = !DILocation(line: 50, column: 47, scope: !2731)
!2731 = !DILexicalBlockFile(scope: !2686, file: !320, discriminator: 1)
!2732 = !DILocation(line: 50, column: 50, scope: !2731)
!2733 = !DILocation(line: 49, column: 9, scope: !2734)
!2734 = !DILexicalBlockFile(scope: !2713, file: !320, discriminator: 1)
!2735 = !DILocation(line: 51, column: 10, scope: !2736)
!2736 = distinct !DILexicalBlock(scope: !2686, file: !320, line: 51, column: 10)
!2737 = !DILocation(line: 51, column: 10, scope: !2686)
!2738 = !DILocation(line: 52, column: 17, scope: !2736)
!2739 = !DILocation(line: 52, column: 10, scope: !2736)
!2740 = !DILocation(line: 54, column: 18, scope: !2736)
!2741 = !DILocation(line: 54, column: 17, scope: !2736)
!2742 = !DILocation(line: 55, column: 6, scope: !2686)
!2743 = !DILocation(line: 57, column: 15, scope: !2682)
!2744 = !DILocation(line: 57, column: 14, scope: !2682)
!2745 = !DILocation(line: 58, column: 11, scope: !2663)
!2746 = !DILocation(line: 58, column: 4, scope: !2663)
!2747 = distinct !DISubprogram(name: "GPIO_unexport", scope: !320, file: !320, line: 61, type: !2664, isLocal: false, isDefinition: true, scopeLine: 62, flags: DIFlagPrototyped, isOptimized: false, unit: !319, variables: !2)
!2748 = !DILocalVariable(name: "pin", arg: 1, scope: !2747, file: !320, line: 61, type: !12)
!2749 = !DILocation(line: 61, column: 23, scope: !2747)
!2750 = !DILocalVariable(name: "name_buffer", scope: !2747, file: !320, line: 63, type: !2669)
!2751 = !DILocation(line: 63, column: 9, scope: !2747)
!2752 = !DILocalVariable(name: "bytes_written", scope: !2747, file: !320, line: 64, type: !2672)
!2753 = !DILocation(line: 64, column: 12, scope: !2747)
!2754 = !DILocalVariable(name: "fd", scope: !2747, file: !320, line: 65, type: !12)
!2755 = !DILocation(line: 65, column: 8, scope: !2747)
!2756 = !DILocalVariable(name: "ret_err", scope: !2747, file: !320, line: 66, type: !12)
!2757 = !DILocation(line: 66, column: 8, scope: !2747)
!2758 = !DILocation(line: 68, column: 9, scope: !2747)
!2759 = !DILocation(line: 68, column: 7, scope: !2747)
!2760 = !DILocation(line: 69, column: 13, scope: !2761)
!2761 = distinct !DILexicalBlock(scope: !2747, file: !320, line: 69, column: 7)
!2762 = !DILocation(line: 69, column: 10, scope: !2761)
!2763 = !DILocation(line: 69, column: 7, scope: !2747)
!2764 = !DILocation(line: 71, column: 32, scope: !2765)
!2765 = distinct !DILexicalBlock(scope: !2761, file: !320, line: 70, column: 6)
!2766 = !DILocation(line: 71, column: 74, scope: !2765)
!2767 = !DILocation(line: 71, column: 23, scope: !2765)
!2768 = !DILocation(line: 71, column: 21, scope: !2765)
!2769 = !DILocation(line: 72, column: 13, scope: !2765)
!2770 = !DILocation(line: 72, column: 17, scope: !2765)
!2771 = !DILocation(line: 72, column: 30, scope: !2765)
!2772 = !DILocation(line: 72, column: 7, scope: !2765)
!2773 = !DILocation(line: 73, column: 13, scope: !2765)
!2774 = !DILocation(line: 73, column: 7, scope: !2765)
!2775 = !DILocation(line: 74, column: 14, scope: !2765)
!2776 = !DILocation(line: 75, column: 6, scope: !2765)
!2777 = !DILocation(line: 77, column: 16, scope: !2761)
!2778 = !DILocation(line: 77, column: 15, scope: !2761)
!2779 = !DILocation(line: 78, column: 11, scope: !2747)
!2780 = !DILocation(line: 78, column: 4, scope: !2747)
!2781 = distinct !DISubprogram(name: "GPIO_direction", scope: !320, file: !320, line: 81, type: !2782, isLocal: false, isDefinition: true, scopeLine: 82, flags: DIFlagPrototyped, isOptimized: false, unit: !319, variables: !2)
!2782 = !DISubroutineType(types: !2783)
!2783 = !{!12, !12, !12}
!2784 = !DILocalVariable(name: "pin", arg: 1, scope: !2781, file: !320, line: 81, type: !12)
!2785 = !DILocation(line: 81, column: 24, scope: !2781)
!2786 = !DILocalVariable(name: "dir", arg: 2, scope: !2781, file: !320, line: 81, type: !12)
!2787 = !DILocation(line: 81, column: 33, scope: !2781)
!2788 = !DILocalVariable(name: "s_directions_str", scope: !2781, file: !320, line: 83, type: !2789)
!2789 = !DICompositeType(tag: DW_TAG_array_type, baseType: !2113, size: 64, align: 32, elements: !13)
!2790 = !DILocation(line: 83, column: 16, scope: !2781)
!2791 = !DILocalVariable(name: "path", scope: !2781, file: !320, line: 84, type: !2687)
!2792 = !DILocation(line: 84, column: 9, scope: !2781)
!2793 = !DILocalVariable(name: "fd", scope: !2781, file: !320, line: 85, type: !12)
!2794 = !DILocation(line: 85, column: 8, scope: !2781)
!2795 = !DILocalVariable(name: "ret_err", scope: !2781, file: !320, line: 86, type: !12)
!2796 = !DILocation(line: 86, column: 8, scope: !2781)
!2797 = !DILocation(line: 88, column: 13, scope: !2781)
!2798 = !DILocation(line: 88, column: 83, scope: !2781)
!2799 = !DILocation(line: 88, column: 4, scope: !2781)
!2800 = !DILocation(line: 89, column: 14, scope: !2781)
!2801 = !DILocation(line: 89, column: 9, scope: !2781)
!2802 = !DILocation(line: 89, column: 7, scope: !2781)
!2803 = !DILocation(line: 90, column: 13, scope: !2804)
!2804 = distinct !DILexicalBlock(scope: !2781, file: !320, line: 90, column: 7)
!2805 = !DILocation(line: 90, column: 10, scope: !2804)
!2806 = !DILocation(line: 90, column: 7, scope: !2781)
!2807 = !DILocalVariable(name: "curr_dir_str", scope: !2808, file: !320, line: 92, type: !2113)
!2808 = distinct !DILexicalBlock(scope: !2804, file: !320, line: 91, column: 6)
!2809 = !DILocation(line: 92, column: 19, scope: !2808)
!2810 = !DILocation(line: 94, column: 51, scope: !2808)
!2811 = !DILocation(line: 94, column: 48, scope: !2808)
!2812 = !DILocation(line: 94, column: 20, scope: !2808)
!2813 = !DILocation(line: 94, column: 19, scope: !2808)
!2814 = !DILocation(line: 95, column: 23, scope: !2815)
!2815 = distinct !DILexicalBlock(scope: !2808, file: !320, line: 95, column: 11)
!2816 = !DILocation(line: 95, column: 27, scope: !2815)
!2817 = !DILocation(line: 95, column: 48, scope: !2815)
!2818 = !DILocation(line: 95, column: 41, scope: !2815)
!2819 = !DILocation(line: 95, column: 17, scope: !2820)
!2820 = !DILexicalBlockFile(scope: !2815, file: !320, discriminator: 1)
!2821 = !DILocation(line: 95, column: 14, scope: !2815)
!2822 = !DILocation(line: 95, column: 11, scope: !2808)
!2823 = !DILocation(line: 96, column: 17, scope: !2815)
!2824 = !DILocation(line: 96, column: 10, scope: !2815)
!2825 = !DILocation(line: 98, column: 18, scope: !2815)
!2826 = !DILocation(line: 98, column: 17, scope: !2815)
!2827 = !DILocation(line: 99, column: 13, scope: !2808)
!2828 = !DILocation(line: 99, column: 7, scope: !2808)
!2829 = !DILocation(line: 100, column: 6, scope: !2808)
!2830 = !DILocation(line: 102, column: 16, scope: !2804)
!2831 = !DILocation(line: 102, column: 15, scope: !2804)
!2832 = !DILocation(line: 103, column: 11, scope: !2781)
!2833 = !DILocation(line: 103, column: 4, scope: !2781)
!2834 = distinct !DISubprogram(name: "GPIO_read", scope: !320, file: !320, line: 106, type: !2835, isLocal: false, isDefinition: true, scopeLine: 107, flags: DIFlagPrototyped, isOptimized: false, unit: !319, variables: !2)
!2835 = !DISubroutineType(types: !2836)
!2836 = !{!12, !12, !1575}
!2837 = !DILocalVariable(name: "pin", arg: 1, scope: !2834, file: !320, line: 106, type: !12)
!2838 = !DILocation(line: 106, column: 19, scope: !2834)
!2839 = !DILocalVariable(name: "value", arg: 2, scope: !2834, file: !320, line: 106, type: !1575)
!2840 = !DILocation(line: 106, column: 29, scope: !2834)
!2841 = !DILocalVariable(name: "path", scope: !2834, file: !320, line: 108, type: !2842)
!2842 = !DICompositeType(tag: DW_TAG_array_type, baseType: !19, size: 240, align: 8, elements: !2843)
!2843 = !{!2844}
!2844 = !DISubrange(count: 30)
!2845 = !DILocation(line: 108, column: 9, scope: !2834)
!2846 = !DILocalVariable(name: "value_str", scope: !2834, file: !320, line: 109, type: !2669)
!2847 = !DILocation(line: 109, column: 9, scope: !2834)
!2848 = !DILocalVariable(name: "fd", scope: !2834, file: !320, line: 110, type: !12)
!2849 = !DILocation(line: 110, column: 8, scope: !2834)
!2850 = !DILocalVariable(name: "ret_err", scope: !2834, file: !320, line: 111, type: !12)
!2851 = !DILocation(line: 111, column: 8, scope: !2834)
!2852 = !DILocation(line: 113, column: 7, scope: !2853)
!2853 = distinct !DILexicalBlock(scope: !2834, file: !320, line: 113, column: 7)
!2854 = !DILocation(line: 113, column: 13, scope: !2853)
!2855 = !DILocation(line: 113, column: 7, scope: !2834)
!2856 = !DILocation(line: 115, column: 16, scope: !2857)
!2857 = distinct !DILexicalBlock(scope: !2853, file: !320, line: 114, column: 6)
!2858 = !DILocation(line: 115, column: 78, scope: !2857)
!2859 = !DILocation(line: 115, column: 7, scope: !2857)
!2860 = !DILocation(line: 116, column: 17, scope: !2857)
!2861 = !DILocation(line: 116, column: 12, scope: !2857)
!2862 = !DILocation(line: 116, column: 10, scope: !2857)
!2863 = !DILocation(line: 117, column: 16, scope: !2864)
!2864 = distinct !DILexicalBlock(scope: !2857, file: !320, line: 117, column: 10)
!2865 = !DILocation(line: 117, column: 13, scope: !2864)
!2866 = !DILocation(line: 117, column: 10, scope: !2857)
!2867 = !DILocation(line: 119, column: 25, scope: !2868)
!2868 = distinct !DILexicalBlock(scope: !2869, file: !320, line: 119, column: 14)
!2869 = distinct !DILexicalBlock(scope: !2864, file: !320, line: 118, column: 9)
!2870 = !DILocation(line: 119, column: 29, scope: !2868)
!2871 = !DILocation(line: 119, column: 20, scope: !2868)
!2872 = !DILocation(line: 119, column: 17, scope: !2868)
!2873 = !DILocation(line: 119, column: 14, scope: !2869)
!2874 = !DILocation(line: 121, column: 13, scope: !2875)
!2875 = distinct !DILexicalBlock(scope: !2868, file: !320, line: 120, column: 12)
!2876 = !DILocation(line: 121, column: 43, scope: !2875)
!2877 = !DILocation(line: 122, column: 25, scope: !2875)
!2878 = !DILocation(line: 122, column: 20, scope: !2875)
!2879 = !DILocation(line: 122, column: 14, scope: !2875)
!2880 = !DILocation(line: 122, column: 19, scope: !2875)
!2881 = !DILocation(line: 123, column: 20, scope: !2875)
!2882 = !DILocation(line: 124, column: 12, scope: !2875)
!2883 = !DILocation(line: 126, column: 21, scope: !2868)
!2884 = !DILocation(line: 126, column: 20, scope: !2868)
!2885 = !DILocation(line: 127, column: 16, scope: !2869)
!2886 = !DILocation(line: 127, column: 10, scope: !2869)
!2887 = !DILocation(line: 128, column: 9, scope: !2869)
!2888 = !DILocation(line: 130, column: 18, scope: !2864)
!2889 = !DILocation(line: 130, column: 17, scope: !2864)
!2890 = !DILocation(line: 131, column: 6, scope: !2857)
!2891 = !DILocation(line: 133, column: 14, scope: !2853)
!2892 = !DILocation(line: 134, column: 11, scope: !2834)
!2893 = !DILocation(line: 134, column: 4, scope: !2834)
!2894 = distinct !DISubprogram(name: "GPIO_write", scope: !320, file: !320, line: 137, type: !2782, isLocal: false, isDefinition: true, scopeLine: 138, flags: DIFlagPrototyped, isOptimized: false, unit: !319, variables: !2)
!2895 = !DILocalVariable(name: "pin", arg: 1, scope: !2894, file: !320, line: 137, type: !12)
!2896 = !DILocation(line: 137, column: 20, scope: !2894)
!2897 = !DILocalVariable(name: "value", arg: 2, scope: !2894, file: !320, line: 137, type: !12)
!2898 = !DILocation(line: 137, column: 29, scope: !2894)
!2899 = !DILocalVariable(name: "s_values_str", scope: !2894, file: !320, line: 139, type: !2789)
!2900 = !DILocation(line: 139, column: 16, scope: !2894)
!2901 = !DILocalVariable(name: "path", scope: !2894, file: !320, line: 140, type: !2842)
!2902 = !DILocation(line: 140, column: 9, scope: !2894)
!2903 = !DILocalVariable(name: "fd", scope: !2894, file: !320, line: 141, type: !12)
!2904 = !DILocation(line: 141, column: 8, scope: !2894)
!2905 = !DILocalVariable(name: "ret_err", scope: !2894, file: !320, line: 142, type: !12)
!2906 = !DILocation(line: 142, column: 8, scope: !2894)
!2907 = !DILocation(line: 144, column: 13, scope: !2894)
!2908 = !DILocation(line: 144, column: 75, scope: !2894)
!2909 = !DILocation(line: 144, column: 4, scope: !2894)
!2910 = !DILocation(line: 145, column: 14, scope: !2894)
!2911 = !DILocation(line: 145, column: 9, scope: !2894)
!2912 = !DILocation(line: 145, column: 7, scope: !2894)
!2913 = !DILocation(line: 146, column: 13, scope: !2914)
!2914 = distinct !DILexicalBlock(scope: !2894, file: !320, line: 146, column: 7)
!2915 = !DILocation(line: 146, column: 10, scope: !2914)
!2916 = !DILocation(line: 146, column: 7, scope: !2894)
!2917 = !DILocalVariable(name: "curr_dir_str", scope: !2918, file: !320, line: 148, type: !2113)
!2918 = distinct !DILexicalBlock(scope: !2914, file: !320, line: 147, column: 6)
!2919 = !DILocation(line: 148, column: 19, scope: !2918)
!2920 = !DILocation(line: 150, column: 48, scope: !2918)
!2921 = !DILocation(line: 150, column: 45, scope: !2918)
!2922 = !DILocation(line: 150, column: 20, scope: !2918)
!2923 = !DILocation(line: 150, column: 19, scope: !2918)
!2924 = !DILocation(line: 151, column: 22, scope: !2925)
!2925 = distinct !DILexicalBlock(scope: !2918, file: !320, line: 151, column: 10)
!2926 = !DILocation(line: 151, column: 26, scope: !2925)
!2927 = !DILocation(line: 151, column: 47, scope: !2925)
!2928 = !DILocation(line: 151, column: 40, scope: !2925)
!2929 = !DILocation(line: 151, column: 16, scope: !2930)
!2930 = !DILexicalBlockFile(scope: !2925, file: !320, discriminator: 1)
!2931 = !DILocation(line: 151, column: 13, scope: !2925)
!2932 = !DILocation(line: 151, column: 10, scope: !2918)
!2933 = !DILocation(line: 152, column: 17, scope: !2925)
!2934 = !DILocation(line: 152, column: 10, scope: !2925)
!2935 = !DILocation(line: 154, column: 18, scope: !2925)
!2936 = !DILocation(line: 154, column: 17, scope: !2925)
!2937 = !DILocation(line: 155, column: 13, scope: !2918)
!2938 = !DILocation(line: 155, column: 7, scope: !2918)
!2939 = !DILocation(line: 156, column: 6, scope: !2918)
!2940 = !DILocation(line: 158, column: 16, scope: !2914)
!2941 = !DILocation(line: 158, column: 15, scope: !2914)
!2942 = !DILocation(line: 159, column: 11, scope: !2894)
!2943 = !DILocation(line: 159, column: 4, scope: !2894)
!2944 = distinct !DISubprogram(name: "export_gpios", scope: !320, file: !320, line: 162, type: !346, isLocal: false, isDefinition: true, scopeLine: 163, flags: DIFlagPrototyped, isOptimized: false, unit: !319, variables: !2)
!2945 = !DILocalVariable(name: "ret_err", scope: !2944, file: !320, line: 164, type: !12)
!2946 = !DILocation(line: 164, column: 8, scope: !2944)
!2947 = !DILocalVariable(name: "fn_err_num", scope: !2944, file: !320, line: 165, type: !12)
!2948 = !DILocation(line: 165, column: 8, scope: !2944)
!2949 = !DILocation(line: 168, column: 15, scope: !2944)
!2950 = !DILocation(line: 168, column: 14, scope: !2944)
!2951 = !DILocation(line: 169, column: 13, scope: !2952)
!2952 = distinct !DILexicalBlock(scope: !2944, file: !320, line: 169, column: 8)
!2953 = !DILocation(line: 169, column: 10, scope: !2952)
!2954 = !DILocation(line: 169, column: 8, scope: !2944)
!2955 = !DILocation(line: 171, column: 18, scope: !2956)
!2956 = distinct !DILexicalBlock(scope: !2952, file: !320, line: 170, column: 6)
!2957 = !DILocation(line: 171, column: 17, scope: !2956)
!2958 = !DILocation(line: 172, column: 16, scope: !2959)
!2959 = distinct !DILexicalBlock(scope: !2956, file: !320, line: 172, column: 11)
!2960 = !DILocation(line: 172, column: 13, scope: !2959)
!2961 = !DILocation(line: 172, column: 11, scope: !2956)
!2962 = !DILocation(line: 174, column: 21, scope: !2963)
!2963 = distinct !DILexicalBlock(scope: !2959, file: !320, line: 173, column: 9)
!2964 = !DILocation(line: 174, column: 20, scope: !2963)
!2965 = !DILocation(line: 175, column: 19, scope: !2966)
!2966 = distinct !DILexicalBlock(scope: !2963, file: !320, line: 175, column: 14)
!2967 = !DILocation(line: 175, column: 16, scope: !2966)
!2968 = !DILocation(line: 175, column: 14, scope: !2963)
!2969 = !DILocation(line: 177, column: 24, scope: !2970)
!2970 = distinct !DILexicalBlock(scope: !2966, file: !320, line: 176, column: 12)
!2971 = !DILocation(line: 177, column: 23, scope: !2970)
!2972 = !DILocation(line: 178, column: 22, scope: !2973)
!2973 = distinct !DILexicalBlock(scope: !2970, file: !320, line: 178, column: 17)
!2974 = !DILocation(line: 178, column: 19, scope: !2973)
!2975 = !DILocation(line: 178, column: 17, scope: !2970)
!2976 = !DILocation(line: 180, column: 27, scope: !2977)
!2977 = distinct !DILexicalBlock(scope: !2973, file: !320, line: 179, column: 15)
!2978 = !DILocation(line: 180, column: 26, scope: !2977)
!2979 = !DILocation(line: 181, column: 25, scope: !2980)
!2980 = distinct !DILexicalBlock(scope: !2977, file: !320, line: 181, column: 20)
!2981 = !DILocation(line: 181, column: 22, scope: !2980)
!2982 = !DILocation(line: 181, column: 20, scope: !2977)
!2983 = !DILocation(line: 183, column: 26, scope: !2984)
!2984 = distinct !DILexicalBlock(scope: !2980, file: !320, line: 182, column: 18)
!2985 = !DILocation(line: 184, column: 18, scope: !2984)
!2986 = !DILocation(line: 187, column: 27, scope: !2987)
!2987 = distinct !DILexicalBlock(scope: !2980, file: !320, line: 186, column: 18)
!2988 = !DILocation(line: 187, column: 26, scope: !2987)
!2989 = !DILocation(line: 188, column: 19, scope: !2987)
!2990 = !DILocation(line: 188, column: 19, scope: !2991)
!2991 = !DILexicalBlockFile(scope: !2987, file: !320, discriminator: 1)
!2992 = !DILocation(line: 189, column: 19, scope: !2987)
!2993 = !DILocation(line: 190, column: 19, scope: !2987)
!2994 = !DILocation(line: 191, column: 19, scope: !2987)
!2995 = !DILocation(line: 192, column: 19, scope: !2987)
!2996 = !DILocation(line: 194, column: 15, scope: !2977)
!2997 = !DILocation(line: 197, column: 24, scope: !2998)
!2998 = distinct !DILexicalBlock(scope: !2973, file: !320, line: 196, column: 15)
!2999 = !DILocation(line: 197, column: 23, scope: !2998)
!3000 = !DILocation(line: 198, column: 16, scope: !2998)
!3001 = !DILocation(line: 198, column: 16, scope: !3002)
!3002 = !DILexicalBlockFile(scope: !2998, file: !320, discriminator: 1)
!3003 = !DILocation(line: 199, column: 16, scope: !2998)
!3004 = !DILocation(line: 200, column: 16, scope: !2998)
!3005 = !DILocation(line: 201, column: 16, scope: !2998)
!3006 = !DILocation(line: 203, column: 12, scope: !2970)
!3007 = !DILocation(line: 206, column: 21, scope: !3008)
!3008 = distinct !DILexicalBlock(scope: !2966, file: !320, line: 205, column: 12)
!3009 = !DILocation(line: 206, column: 20, scope: !3008)
!3010 = !DILocation(line: 207, column: 13, scope: !3008)
!3011 = !DILocation(line: 207, column: 13, scope: !3012)
!3012 = !DILexicalBlockFile(scope: !3008, file: !320, discriminator: 1)
!3013 = !DILocation(line: 208, column: 13, scope: !3008)
!3014 = !DILocation(line: 209, column: 13, scope: !3008)
!3015 = !DILocation(line: 211, column: 9, scope: !2963)
!3016 = !DILocation(line: 214, column: 18, scope: !3017)
!3017 = distinct !DILexicalBlock(scope: !2959, file: !320, line: 213, column: 9)
!3018 = !DILocation(line: 214, column: 17, scope: !3017)
!3019 = !DILocation(line: 215, column: 10, scope: !3017)
!3020 = !DILocation(line: 215, column: 10, scope: !3021)
!3021 = !DILexicalBlockFile(scope: !3017, file: !320, discriminator: 1)
!3022 = !DILocation(line: 216, column: 10, scope: !3017)
!3023 = !DILocation(line: 218, column: 6, scope: !2956)
!3024 = !DILocation(line: 221, column: 15, scope: !3025)
!3025 = distinct !DILexicalBlock(scope: !2952, file: !320, line: 220, column: 6)
!3026 = !DILocation(line: 221, column: 14, scope: !3025)
!3027 = !DILocation(line: 222, column: 7, scope: !3025)
!3028 = !DILocation(line: 222, column: 7, scope: !3029)
!3029 = !DILexicalBlockFile(scope: !3025, file: !320, discriminator: 1)
!3030 = !DILocation(line: 225, column: 11, scope: !2944)
!3031 = !DILocation(line: 225, column: 4, scope: !2944)
!3032 = distinct !DISubprogram(name: "configure_gpios", scope: !320, file: !320, line: 228, type: !346, isLocal: false, isDefinition: true, scopeLine: 229, flags: DIFlagPrototyped, isOptimized: false, unit: !319, variables: !2)
!3033 = !DILocalVariable(name: "ret_err", scope: !3032, file: !320, line: 230, type: !12)
!3034 = !DILocation(line: 230, column: 8, scope: !3032)
!3035 = !DILocalVariable(name: "curr_gpio", scope: !3032, file: !320, line: 231, type: !12)
!3036 = !DILocation(line: 231, column: 8, scope: !3032)
!3037 = !DILocation(line: 234, column: 13, scope: !3032)
!3038 = !DILocation(line: 235, column: 27, scope: !3032)
!3039 = !DILocation(line: 235, column: 12, scope: !3032)
!3040 = !DILocation(line: 235, column: 11, scope: !3032)
!3041 = !DILocation(line: 236, column: 13, scope: !3042)
!3042 = distinct !DILexicalBlock(scope: !3032, file: !320, line: 236, column: 8)
!3043 = !DILocation(line: 236, column: 10, scope: !3042)
!3044 = !DILocation(line: 236, column: 8, scope: !3032)
!3045 = !DILocation(line: 238, column: 16, scope: !3046)
!3046 = distinct !DILexicalBlock(scope: !3042, file: !320, line: 237, column: 6)
!3047 = !DILocation(line: 239, column: 30, scope: !3046)
!3048 = !DILocation(line: 239, column: 15, scope: !3046)
!3049 = !DILocation(line: 239, column: 14, scope: !3046)
!3050 = !DILocation(line: 240, column: 16, scope: !3051)
!3051 = distinct !DILexicalBlock(scope: !3046, file: !320, line: 240, column: 11)
!3052 = !DILocation(line: 240, column: 13, scope: !3051)
!3053 = !DILocation(line: 240, column: 11, scope: !3046)
!3054 = !DILocation(line: 242, column: 21, scope: !3055)
!3055 = distinct !DILexicalBlock(scope: !3051, file: !320, line: 241, column: 9)
!3056 = !DILocation(line: 242, column: 10, scope: !3055)
!3057 = !DILocation(line: 243, column: 19, scope: !3055)
!3058 = !DILocation(line: 244, column: 33, scope: !3055)
!3059 = !DILocation(line: 244, column: 18, scope: !3055)
!3060 = !DILocation(line: 244, column: 17, scope: !3055)
!3061 = !DILocation(line: 245, column: 19, scope: !3062)
!3062 = distinct !DILexicalBlock(scope: !3055, file: !320, line: 245, column: 14)
!3063 = !DILocation(line: 245, column: 16, scope: !3062)
!3064 = !DILocation(line: 245, column: 14, scope: !3055)
!3065 = !DILocation(line: 247, column: 24, scope: !3066)
!3066 = distinct !DILexicalBlock(scope: !3062, file: !320, line: 246, column: 12)
!3067 = !DILocation(line: 247, column: 13, scope: !3066)
!3068 = !DILocation(line: 248, column: 22, scope: !3066)
!3069 = !DILocation(line: 249, column: 36, scope: !3066)
!3070 = !DILocation(line: 249, column: 21, scope: !3066)
!3071 = !DILocation(line: 249, column: 20, scope: !3066)
!3072 = !DILocation(line: 250, column: 22, scope: !3073)
!3073 = distinct !DILexicalBlock(scope: !3066, file: !320, line: 250, column: 17)
!3074 = !DILocation(line: 250, column: 19, scope: !3073)
!3075 = !DILocation(line: 250, column: 17, scope: !3066)
!3076 = !DILocation(line: 252, column: 27, scope: !3077)
!3077 = distinct !DILexicalBlock(scope: !3073, file: !320, line: 251, column: 15)
!3078 = !DILocation(line: 252, column: 16, scope: !3077)
!3079 = !DILocation(line: 253, column: 25, scope: !3077)
!3080 = !DILocation(line: 254, column: 39, scope: !3077)
!3081 = !DILocation(line: 254, column: 24, scope: !3077)
!3082 = !DILocation(line: 254, column: 23, scope: !3077)
!3083 = !DILocation(line: 255, column: 25, scope: !3084)
!3084 = distinct !DILexicalBlock(scope: !3077, file: !320, line: 255, column: 20)
!3085 = !DILocation(line: 255, column: 22, scope: !3084)
!3086 = !DILocation(line: 255, column: 20, scope: !3077)
!3087 = !DILocation(line: 256, column: 30, scope: !3084)
!3088 = !DILocation(line: 256, column: 19, scope: !3084)
!3089 = !DILocation(line: 257, column: 15, scope: !3077)
!3090 = !DILocation(line: 258, column: 12, scope: !3066)
!3091 = !DILocation(line: 259, column: 9, scope: !3055)
!3092 = !DILocation(line: 260, column: 6, scope: !3046)
!3093 = !DILocation(line: 261, column: 7, scope: !3094)
!3094 = distinct !DILexicalBlock(scope: !3032, file: !320, line: 261, column: 7)
!3095 = !DILocation(line: 261, column: 15, scope: !3094)
!3096 = !DILocation(line: 261, column: 7, scope: !3032)
!3097 = !DILocation(line: 262, column: 7, scope: !3094)
!3098 = !DILocation(line: 262, column: 7, scope: !3099)
!3099 = !DILexicalBlockFile(scope: !3094, file: !320, discriminator: 1)
!3100 = !DILocation(line: 264, column: 11, scope: !3032)
!3101 = !DILocation(line: 264, column: 4, scope: !3032)
!3102 = distinct !DISubprogram(name: "unexport_gpios", scope: !320, file: !320, line: 267, type: !346, isLocal: false, isDefinition: true, scopeLine: 268, flags: DIFlagPrototyped, isOptimized: false, unit: !319, variables: !2)
!3103 = !DILocalVariable(name: "ret_err", scope: !3102, file: !320, line: 269, type: !12)
!3104 = !DILocation(line: 269, column: 8, scope: !3102)
!3105 = !DILocation(line: 271, column: 11, scope: !3102)
!3106 = !DILocation(line: 273, column: 14, scope: !3102)
!3107 = !DILocation(line: 273, column: 11, scope: !3102)
!3108 = !DILocation(line: 274, column: 14, scope: !3102)
!3109 = !DILocation(line: 274, column: 11, scope: !3102)
!3110 = !DILocation(line: 275, column: 14, scope: !3102)
!3111 = !DILocation(line: 275, column: 11, scope: !3102)
!3112 = !DILocation(line: 276, column: 14, scope: !3102)
!3113 = !DILocation(line: 276, column: 11, scope: !3102)
!3114 = !DILocation(line: 277, column: 14, scope: !3102)
!3115 = !DILocation(line: 277, column: 11, scope: !3102)
!3116 = !DILocation(line: 278, column: 7, scope: !3117)
!3117 = distinct !DILexicalBlock(scope: !3102, file: !320, line: 278, column: 7)
!3118 = !DILocation(line: 278, column: 15, scope: !3117)
!3119 = !DILocation(line: 278, column: 7, scope: !3102)
!3120 = !DILocation(line: 279, column: 7, scope: !3117)
!3121 = !DILocation(line: 279, column: 7, scope: !3122)
!3122 = !DILexicalBlockFile(scope: !3117, file: !320, discriminator: 1)
!3123 = !DILocation(line: 281, column: 11, scope: !3102)
!3124 = !DILocation(line: 281, column: 4, scope: !3102)
