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
@.str.2.21 = private unnamed_addr constant [10 x i8] c"sensitive\00", section "llvm.metadata"
@.str.3.22 = private unnamed_addr constant [15 x i8] c"gpio_polling.c\00", section "llvm.metadata"
@.str.4.23 = private unnamed_addr constant [23 x i8] c"GPIO server initiated\0A\00", align 1
@.str.5.24 = private unnamed_addr constant [25 x i8] c"GPIO PIR (%i) value: %i\0A\00", align 1
@.str.6.25 = private unnamed_addr constant [36 x i8] c"Error %i while reading GPIO %i: %s\0A\00", align 1
@.str.7.26 = private unnamed_addr constant [44 x i8] c"GPIO server terminated with error code: %i\0A\00", align 1
@.str.8.29 = private unnamed_addr constant [17 x i8] c"./ARI_branch.txt\00", align 1
@.str.9.30 = private unnamed_addr constant [18 x i8] c"./ARI_ind_jmp.txt\00", align 1
@.str.10.31 = private unnamed_addr constant [19 x i8] c"./ARI_ret_hash.txt\00", align 1
@.str.11.32 = private unnamed_addr constant [14 x i8] c"./ARI_tsf.txt\00", align 1
@.str.12.33 = private unnamed_addr constant [19 x i8] c"./ARI_tsf_cond.txt\00", align 1
@.str.13.34 = private unnamed_addr constant [18 x i8] c"pushover_conf.txt\00", align 1
@.str.14.35 = private unnamed_addr constant [26 x i8] c"Polling thread initiated\0A\00", align 1
@.str.15.36 = private unnamed_addr constant [38 x i8] c"Error %i creating polling thread: %s\0A\00", align 1
@ret_recording_finish = external global i32, align 4
@.str.16.37 = private unnamed_addr constant [40 x i8] c"round with attestation time usecs: %lu\0A\00", align 1
@.str.17.40 = private unnamed_addr constant [37 x i8] c"Polling thread terminated correctly\0A\00", align 1
@.str.18.41 = private unnamed_addr constant [48 x i8] c"Error waiting for the polling thread to finish\0A\00", align 1
@Token_id = common global [81 x i8] zeroinitializer, section ".DATA_REGION_0__bss", align 1
@User_id = common global [81 x i8] zeroinitializer, section ".DATA_REGION_0__bss", align 1
@Server_path = common global [65 x i8] zeroinitializer, section ".DATA_REGION_0__bss", align 1
@Server_port = common global i32 0, section ".DATA_REGION_0__bss", align 4
@Server_name = common global [65 x i8] zeroinitializer, section ".DATA_REGION_0__bss", align 1
@Server_ip = common global %struct.in_addr zeroinitializer, section ".DATA_REGION_0__bss", align 4
@.str.44 = private unnamed_addr constant [80 x i8] c"Error obtaining the directory of the current-process executable file: errno=%d\0A\00", align 1
@.str.1.45 = private unnamed_addr constant [3 x i8] c"rt\00", align 1
@.str.2.46 = private unnamed_addr constant [2 x i8] c"/\00", align 1
@.str.3.47 = private unnamed_addr constant [21 x i8] c" server_url= %2083s\0A\00", align 1
@.str.4.48 = private unnamed_addr constant [14 x i8] c" token= %80s\0A\00", align 1
@.str.5.49 = private unnamed_addr constant [13 x i8] c" user= %80s\0A\00", align 1
@.str.6.50 = private unnamed_addr constant [73 x i8] c"Error loading Pushover config file: unknown variable name found in file\0A\00", align 1
@.str.7.51 = private unnamed_addr constant [8 x i8] c"http://\00", align 1
@.str.8.52 = private unnamed_addr constant [3 x i8] c"%i\00", align 1
@.str.9.53 = private unnamed_addr constant [44 x i8] c"Using Pushover server %s for notifications\0A\00", align 1
@.str.10.54 = private unnamed_addr constant [86 x i8] c"Error loading Pushover config file: server URL is too long (more than 64 characters)\0A\00", align 1
@.str.11.55 = private unnamed_addr constant [69 x i8] c"Error loading Pushover config file: server URL start is not http://\0A\00", align 1
@.str.12.56 = private unnamed_addr constant [55 x i8] c"Error loading Pushover config file: user id not found\0A\00", align 1
@.str.13.57 = private unnamed_addr constant [56 x i8] c"Error loading Pushover config file: token id not found\0A\00", align 1
@.str.14.58 = private unnamed_addr constant [58 x i8] c"Error loading Pushover config file: server URL not found\0A\00", align 1
@.str.15.59 = private unnamed_addr constant [49 x i8] c"Error opening Pushover config file %s: errno=%d\0A\00", align 1
@.str.16.62 = private unnamed_addr constant [4 x i8] c"r+b\00", align 1
@.str.17.63 = private unnamed_addr constant [2 x i8] c"2\00", align 1
@.str.18.64 = private unnamed_addr constant [19 x i8] c"POST %s HTTP/1.0\0D\0A\00", align 1
@.str.19.65 = private unnamed_addr constant [11 x i8] c"Host: %s\0D\0A\00", align 1
@.str.20 = private unnamed_addr constant [50 x i8] c"Content-Type: application/x-www-form-urlencoded\0D\0A\00", align 1
@.str.21 = private unnamed_addr constant [24 x i8] c"Content-Length: %lu\0D\0A\0D\0A\00", align 1
@.str.22 = private unnamed_addr constant [40 x i8] c"token=%s&user=%s&message=%s&priority=%s\00", align 1
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
@.str.66 = private unnamed_addr constant [23 x i8] c"Unknown specified host\00", align 1
@.str.1.67 = private unnamed_addr constant [35 x i8] c"No NS records for specified domain\00", align 1
@.str.2.68 = private unnamed_addr constant [25 x i8] c"No response for NS query\00", align 1
@.str.3.69 = private unnamed_addr constant [17 x i8] c"Unexpected error\00", align 1
@.str.4.70 = private unnamed_addr constant [17 x i8] c"FORMERR response\00", align 1
@.str.5.71 = private unnamed_addr constant [18 x i8] c"SERVFAIL response\00", align 1
@.str.6.72 = private unnamed_addr constant [18 x i8] c"NXDOMAIN response\00", align 1
@.str.7.73 = private unnamed_addr constant [16 x i8] c"NOTIMP response\00", align 1
@.str.8.74 = private unnamed_addr constant [17 x i8] c"REFUSED response\00", align 1
@.str.9.75 = private unnamed_addr constant [23 x i8] c"unexpected return code\00", align 1
@.str.10.78 = private unnamed_addr constant [46 x i8] c"Error resolving IP of hostname %s. error: %s\0A\00", align 1
@.str.11.79 = private unnamed_addr constant [6 x i8] c"> %s\0A\00", align 1
@.str.12.80 = private unnamed_addr constant [37 x i8] c"%s: expected answer type %d, got %d\0A\00", align 1
@.str.13.81 = private unnamed_addr constant [16 x i8] c"ns_parserr: %s\0A\00", align 1
@.str.14.82 = private unnamed_addr constant [31 x i8] c"%s: expected 1 answer, got %d\0A\00", align 1
@.str.15.83 = private unnamed_addr constant [49 x i8] c"DNS response reported an error (domain: %s): %s\0A\00", align 1
@.str.16.84 = private unnamed_addr constant [18 x i8] c"ns_initparse: %s\0A\00", align 1
@.str.17.85 = private unnamed_addr constant [59 x i8] c"Connection refused: There is no name server running on %s\0A\00", align 1
@.str.18.86 = private unnamed_addr constant [49 x i8] c"There was no response from %s (h_errno: %i: %s)\0A\00", align 1
@.str.19.87 = private unnamed_addr constant [26 x i8] c"res_init error. errno:%i\0A\00", align 1
@.str.20.90 = private unnamed_addr constant [22 x i8] c"resolver1.opendns.com\00", align 1
@.str.21.91 = private unnamed_addr constant [17 x i8] c"myip.opendns.com\00", align 1
@.str.94 = private unnamed_addr constant [15 x i8] c"/proc/self/exe\00", align 1
@.str.1.95 = private unnamed_addr constant [2 x i8] c"/\00", align 1
@.str.2.100 = private unnamed_addr constant [40 x i8] c"Child process with PID: %i terminated.\0A\00", align 1
@.str.3.101 = private unnamed_addr constant [57 x i8] c"Error waiting for child process to finish. errno %i: %s\0A\00", align 1
@.str.4.104 = private unnamed_addr constant [64 x i8] c"Creating process %s: failed redirect standard output. errno=%d\0A\00", align 1
@.str.5.105 = private unnamed_addr constant [70 x i8] c"Creating process %s: failed redirect standard error output. errno=%d\0A\00", align 1
@.str.6.106 = private unnamed_addr constant [10 x i8] c"/dev/null\00", align 1
@.str.7.107 = private unnamed_addr constant [63 x i8] c"Creating process %s: failed redirect standard input. errno=%d\0A\00", align 1
@.str.8.108 = private unnamed_addr constant [71 x i8] c"Creating process %s: could not open null device for reading. errno=%d\0A\00", align 1
@.str.9.109 = private unnamed_addr constant [66 x i8] c"Creating process %s: failed to execute capture program. errno=%d\0A\00", align 1
@.str.10.110 = private unnamed_addr constant [50 x i8] c"Creating process %s: first fork failed. errno=%d\0A\00", align 1
@.str.11.113 = private unnamed_addr constant [46 x i8] c"Sensor polling (timer) set to %lis and %lius\0A\00", align 1
@.str.12.114 = private unnamed_addr constant [35 x i8] c"Error setting timer: errno %i: %s\0A\00", align 1
@.str.13.115 = private unnamed_addr constant [65 x i8] c"iAlarm daemon init error: could not open null device for reading\00", align 1
@.str.14.116 = private unnamed_addr constant [65 x i8] c"iAlarm daemon init error: could not open null device for writing\00", align 1
@stderr = external global %struct._IO_FILE*, align 4
@.str.15.117 = private unnamed_addr constant [56 x i8] c"iAlarm daemon init error: second fork failed. errno=%d\0A\00", align 1
@.str.16.118 = private unnamed_addr constant [79 x i8] c"iAlarm daemon init error: child process could become session leader. errno=%d\0A\00", align 1
@.str.17.119 = private unnamed_addr constant [55 x i8] c"iAlarm daemon init error: first fork failed. errno=%d\0A\00", align 1
@Console_messages = global i32 1, section ".DATA_REGION_1__data", align 4
@Log_file_handle = global %struct._IO_FILE* null, section ".DATA_REGION_0__bss", align 4
@Event_file_handle = global %struct._IO_FILE* null, section ".DATA_REGION_0__bss", align 4
@.str.124 = private unnamed_addr constant [18 x i8] c"%Y-%m-%d %H:%M:%S\00", align 1
@.str.1.127 = private unnamed_addr constant [6 x i8] c"[%s] \00", align 1
@.str.2.128 = private unnamed_addr constant [4 x i8] c"a+t\00", align 1
@.str.3.129 = private unnamed_addr constant [3 x i8] c"wt\00", align 1
@.str.4.130 = private unnamed_addr constant [31 x i8] c"\0A[%s] <Old messages deleted>\0A\0A\00", align 1
@.str.5.131 = private unnamed_addr constant [64 x i8] c"[%s] --------------------- Log initiated ---------------------\0A\00", align 1
@.str.6.132 = private unnamed_addr constant [28 x i8] c"[%s] iAlarm daemon running\0A\00", align 1
@.str.7.133 = private unnamed_addr constant [32 x i8] c"[%s] iAlarm daemon terminated\0A\0A\00", align 1
@.str.8.136 = private unnamed_addr constant [29 x i8] c"/var/log/alarm4pi/daemon.log\00", align 1
@.str.9.137 = private unnamed_addr constant [29 x i8] c"/var/log/alarm4pi/events.log\00", align 1
@.str.140 = private unnamed_addr constant [23 x i8] c"/sys/class/gpio/export\00", align 1
@.str.1.141 = private unnamed_addr constant [3 x i8] c"%d\00", align 1
@.str.2.142 = private unnamed_addr constant [33 x i8] c"/sys/class/gpio/gpio%d/direction\00", align 1
@.str.3.143 = private unnamed_addr constant [25 x i8] c"/sys/class/gpio/unexport\00", align 1
@GPIO_direction.s_directions_str = private unnamed_addr constant [2 x i8*] [i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.4.144, i32 0, i32 0), i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str.5.145, i32 0, i32 0)], section ".DATA_REGION_1__data", align 4
@.str.4.144 = private unnamed_addr constant [3 x i8] c"in\00", align 1
@.str.5.145 = private unnamed_addr constant [4 x i8] c"out\00", align 1
@.str.6.148 = private unnamed_addr constant [29 x i8] c"/sys/class/gpio/gpio%d/value\00", align 1
@GPIO_write.s_values_str = private unnamed_addr constant [2 x i8*] [i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.7.149, i32 0, i32 0), i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.8.150, i32 0, i32 0)], section ".DATA_REGION_1__data", align 4
@.str.7.149 = private unnamed_addr constant [2 x i8] c"0\00", align 1
@.str.8.150 = private unnamed_addr constant [2 x i8] c"1\00", align 1
@.str.9.153 = private unnamed_addr constant [54 x i8] c"While exporting output pin %d (relay 4) error %d: %s\0A\00", align 1
@.str.10.154 = private unnamed_addr constant [54 x i8] c"While exporting output pin %d (relay 3) error %d: %s\0A\00", align 1
@.str.11.155 = private unnamed_addr constant [54 x i8] c"While exporting output pin %d (relay 2) error %d: %s\0A\00", align 1
@.str.12.156 = private unnamed_addr constant [54 x i8] c"While exporting output pin %d (relay 1) error %d: %s\0A\00", align 1
@.str.13.157 = private unnamed_addr constant [49 x i8] c"While exporting input pin %d (PIR) error %d: %s\0A\00", align 1
@.str.14.160 = private unnamed_addr constant [53 x i8] c"While configuring direcction of pin %d error %d: %s\0A\00", align 1
@.str.15.163 = private unnamed_addr constant [42 x i8] c"While unexporting GPIO pins error %d: %s\0A\00", align 1

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
define i32 @send_info_notif(i8*, i8*) #0 section ".CODE_REGION_2_" !dbg !548 {
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
  br i1 %9, label %10, label %25, !dbg !587

; <label>:10:                                     ; preds = %1
  %11 = getelementptr inbounds [146 x i8], [146 x i8]* %5, i32 0, i32 0, !dbg !588
  %12 = load i8*, i8** %2, align 4, !dbg !590
  %13 = getelementptr inbounds [46 x i8], [46 x i8]* %4, i32 0, i32 0, !dbg !591
  %14 = call i32 (i8*, i32, i8*, ...) @snprintf(i8* %11, i32 146, i8* %12, i8* %13) #7, !dbg !592
  %15 = getelementptr inbounds [146 x i8], [146 x i8]* %5, i32 0, i32 0, !dbg !593
  %16 = call i32 @strcmp(i8* %15, i8* getelementptr inbounds ([146 x i8], [146 x i8]* @Msg_info_str, i32 0, i32 0)) #9, !dbg !595
  %17 = icmp ne i32 %16, 0, !dbg !596
  br i1 %17, label %18, label %24, !dbg !597

; <label>:18:                                     ; preds = %10
  %19 = getelementptr inbounds [146 x i8], [146 x i8]* %5, i32 0, i32 0, !dbg !598
  %20 = call i8* @strcpy(i8* getelementptr inbounds ([146 x i8], [146 x i8]* @Msg_info_str, i32 0, i32 0), i8* %19) #7, !dbg !600
  %21 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !601
  %22 = getelementptr inbounds [46 x i8], [46 x i8]* %4, i32 0, i32 0, !dbg !601
  call void @__AMI_fake_direct_transfer(), !dbg !601
  %23 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %21, i8* getelementptr inbounds ([23 x i8], [23 x i8]* @.str.1.20, i32 0, i32 0), i8* %22), !dbg !601
  br label %24, !dbg !602

; <label>:24:                                     ; preds = %18, %10
  br label %25, !dbg !603

; <label>:25:                                     ; preds = %24, %1
  %26 = load i32, i32* %3, align 4, !dbg !604
  ret i32 %26, !dbg !605
}

; Function Attrs: nounwind readonly
declare i32 @strcmp(i8*, i8*) #6 section ".CODE_REGION_2_"

; Function Attrs: nounwind
declare i8* @strcpy(i8*, i8*) #2 section ".CODE_REGION_1_"

; Function Attrs: nounwind
define i8* @polling_thread(i32*) #0 section ".CODE_REGION_1_" !dbg !606 {
  %2 = alloca i32*, align 4
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  %7 = alloca i32, align 4
  %8 = alloca i32, align 4
  store i32* %0, i32** %2, align 4
  call void @llvm.dbg.declare(metadata i32** %2, metadata !610, metadata !336), !dbg !611
  call void @llvm.dbg.declare(metadata i32* %3, metadata !612, metadata !336), !dbg !613
  %9 = bitcast i32* %3 to i8*, !dbg !614
  call void @llvm.var.annotation(i8* %9, i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.2.21, i32 0, i32 0), i8* getelementptr inbounds ([15 x i8], [15 x i8]* @.str.3.22, i32 0, i32 0), i32 80), !dbg !614
  call void @llvm.dbg.declare(metadata i32* %4, metadata !615, metadata !336), !dbg !616
  %10 = bitcast i32* %4 to i8*, !dbg !617
  call void @llvm.var.annotation(i8* %10, i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.2.21, i32 0, i32 0), i8* getelementptr inbounds ([15 x i8], [15 x i8]* @.str.3.22, i32 0, i32 0), i32 81), !dbg !617
  call void @llvm.dbg.declare(metadata i32* %5, metadata !618, metadata !336), !dbg !619
  %11 = bitcast i32* %5 to i8*, !dbg !620
  call void @llvm.var.annotation(i8* %11, i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.2.21, i32 0, i32 0), i8* getelementptr inbounds ([15 x i8], [15 x i8]* @.str.3.22, i32 0, i32 0), i32 82), !dbg !620
  call void @llvm.dbg.declare(metadata i32* %6, metadata !621, metadata !336), !dbg !622
  %12 = bitcast i32* %6 to i8*, !dbg !623
  call void @llvm.var.annotation(i8* %12, i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.2.21, i32 0, i32 0), i8* getelementptr inbounds ([15 x i8], [15 x i8]* @.str.3.22, i32 0, i32 0), i32 83), !dbg !623
  call void @llvm.dbg.declare(metadata i32* %7, metadata !624, metadata !336), !dbg !625
  %13 = bitcast i32* %7 to i8*, !dbg !626
  call void @llvm.var.annotation(i8* %13, i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.2.21, i32 0, i32 0), i8* getelementptr inbounds ([15 x i8], [15 x i8]* @.str.3.22, i32 0, i32 0), i32 84), !dbg !626
  %14 = load %struct._IO_FILE*, %struct._IO_FILE** @Event_file_handle, align 4, !dbg !627
  %15 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %14, i8* getelementptr inbounds ([23 x i8], [23 x i8]* @.str.4.23, i32 0, i32 0)), !dbg !627
  store i32 0, i32* %4, align 4, !dbg !628
  store i32 0, i32* %7, align 4, !dbg !629
  store i32 0, i32* %6, align 4, !dbg !630
  call void @llvm.dbg.declare(metadata i32* %8, metadata !631, metadata !336), !dbg !632
  store i32 0, i32* %8, align 4, !dbg !632
  br label %16, !dbg !633

; <label>:16:                                     ; preds = %63, %1
  %17 = load i32, i32* %8, align 4, !dbg !634
  %18 = add nsw i32 %17, 1, !dbg !634
  store i32 %18, i32* %8, align 4, !dbg !634
  %19 = icmp slt i32 %17, 10, !dbg !636
  br i1 %19, label %20, label %64, !dbg !637

; <label>:20:                                     ; preds = %16
  %21 = call i32 @GPIO_read(i32 488, i32* %5), !dbg !638
  store i32 %21, i32* %3, align 4, !dbg !640
  store i32 0, i32* %3, align 4, !dbg !641
  %22 = load i32, i32* %8, align 4, !dbg !642
  %23 = srem i32 %22, 3, !dbg !643
  %24 = icmp eq i32 %23, 0, !dbg !644
  %25 = select i1 %24, i32 1, i32 0, !dbg !645
  store i32 %25, i32* %5, align 4, !dbg !646
  %26 = load i32, i32* %3, align 4, !dbg !647
  %27 = icmp eq i32 %26, 0, !dbg !649
  br i1 %27, label %28, label %46, !dbg !650

; <label>:28:                                     ; preds = %20
  %29 = load i32, i32* %5, align 4, !dbg !651
  %30 = load i32, i32* %6, align 4, !dbg !654
  %31 = icmp ne i32 %29, %30, !dbg !655
  br i1 %31, label %32, label %41, !dbg !656

; <label>:32:                                     ; preds = %28
  %33 = load i32, i32* %5, align 4, !dbg !657
  %34 = icmp ne i32 %33, 0, !dbg !660
  br i1 %34, label %35, label %39, !dbg !661

; <label>:35:                                     ; preds = %32
  %36 = load %struct._IO_FILE*, %struct._IO_FILE** @Event_file_handle, align 4, !dbg !662
  %37 = load i32, i32* %5, align 4, !dbg !662
  %38 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %36, i8* getelementptr inbounds ([25 x i8], [25 x i8]* @.str.5.24, i32 0, i32 0), i32 488, i32 %37), !dbg !662
  br label %39, !dbg !664

; <label>:39:                                     ; preds = %35, %32
  %40 = load i32, i32* %5, align 4, !dbg !665
  store i32 %40, i32* %6, align 4, !dbg !666
  br label %41, !dbg !667

; <label>:41:                                     ; preds = %39, %28
  %42 = load i32, i32* %5, align 4, !dbg !668
  %43 = icmp ne i32 %42, 0, !dbg !670
  br i1 %43, label %44, label %45, !dbg !671

; <label>:44:                                     ; preds = %41
  store i32 60, i32* %7, align 4, !dbg !672
  br label %45, !dbg !673

; <label>:45:                                     ; preds = %44, %41
  br label %57, !dbg !674

; <label>:46:                                     ; preds = %20
  %47 = load i32, i32* %4, align 4, !dbg !675
  %48 = icmp eq i32 %47, 0, !dbg !678
  br i1 %48, label %49, label %56, !dbg !679

; <label>:49:                                     ; preds = %46
  %50 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !680
  %51 = load i32, i32* %3, align 4, !dbg !680
  %52 = load i32, i32* %3, align 4, !dbg !680
  %53 = call i8* @strerror(i32 %52) #7, !dbg !680
  %54 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %50, i8* getelementptr inbounds ([36 x i8], [36 x i8]* @.str.6.25, i32 0, i32 0), i32 %51, i32 488, i8* %53), !dbg !682
  %55 = load i32, i32* %3, align 4, !dbg !684
  store i32 %55, i32* %4, align 4, !dbg !685
  br label %56, !dbg !686

; <label>:56:                                     ; preds = %49, %46
  br label %57

; <label>:57:                                     ; preds = %56, %45
  %58 = load i32, i32* %7, align 4, !dbg !687
  %59 = icmp sgt i32 %58, 0, !dbg !689
  br i1 %59, label %60, label %63, !dbg !690

; <label>:60:                                     ; preds = %57
  %61 = load i32, i32* %7, align 4, !dbg !691
  %62 = add nsw i32 %61, -1, !dbg !691
  store i32 %62, i32* %7, align 4, !dbg !691
  br label %63, !dbg !692

; <label>:63:                                     ; preds = %60, %57
  br label %16, !dbg !693, !llvm.loop !695

; <label>:64:                                     ; preds = %16
  %65 = load %struct._IO_FILE*, %struct._IO_FILE** @Event_file_handle, align 4, !dbg !696
  %66 = load i32, i32* %4, align 4, !dbg !696
  %67 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %65, i8* getelementptr inbounds ([44 x i8], [44 x i8]* @.str.7.26, i32 0, i32 0), i32 %66), !dbg !696
  %68 = load i32, i32* %4, align 4, !dbg !697
  %69 = inttoptr i32 %68 to i8*, !dbg !698
  ret i8* %69, !dbg !699
}

; Function Attrs: nounwind
declare void @llvm.var.annotation(i8*, i8*, i8*, i32) #7

; Function Attrs: nounwind
declare i8* @strerror(i32) #2 section ".CODE_REGION_1_"

; Function Attrs: nounwind
define i32 @init_polling(i32*, i8*) #0 section ".CODE_REGION_1_" !dbg !700 {
  %3 = alloca i32*, align 4
  %4 = alloca i8*, align 4
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  %7 = alloca i32, align 4
  store i32* %0, i32** %3, align 4
  call void @llvm.dbg.declare(metadata i32** %3, metadata !703, metadata !336), !dbg !704
  store i8* %1, i8** %4, align 4
  call void @llvm.dbg.declare(metadata i8** %4, metadata !705, metadata !336), !dbg !706
  call void @create_files(i8* getelementptr inbounds ([17 x i8], [17 x i8]* @.str.8.29, i32 0, i32 0), i8* getelementptr inbounds ([18 x i8], [18 x i8]* @.str.9.30, i32 0, i32 0), i8* getelementptr inbounds ([19 x i8], [19 x i8]* @.str.10.31, i32 0, i32 0), i8* getelementptr inbounds ([14 x i8], [14 x i8]* @.str.11.32, i32 0, i32 0), i8* getelementptr inbounds ([19 x i8], [19 x i8]* @.str.12.33, i32 0, i32 0)), !dbg !707
  call void @__AMI_fake_local_wrt(), !dbg !708
  store i32 1, i32* @recording_flag, align 4, !dbg !708
  call void @llvm.dbg.declare(metadata i32* %5, metadata !709, metadata !336), !dbg !710
  %8 = bitcast i32* %5 to i8*, !dbg !711
  call void @llvm.var.annotation(i8* %8, i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.2.21, i32 0, i32 0), i8* getelementptr inbounds ([15 x i8], [15 x i8]* @.str.3.22, i32 0, i32 0), i32 162), !dbg !711
  call void @llvm.dbg.declare(metadata i32* %6, metadata !712, metadata !336), !dbg !713
  call void @llvm.dbg.declare(metadata i32* %7, metadata !714, metadata !336), !dbg !715
  %9 = call i32 @usecs(), !dbg !716
  store i32 %9, i32* %6, align 4, !dbg !717
  %10 = call i32 @export_gpios(), !dbg !718
  store i32 %10, i32* %5, align 4, !dbg !719
  store i32 0, i32* %5, align 4, !dbg !720
  %11 = load i32, i32* %5, align 4, !dbg !721
  %12 = icmp eq i32 %11, 0, !dbg !723
  br i1 %12, label %13, label %38, !dbg !724

; <label>:13:                                     ; preds = %2
  %14 = call i32 @configure_gpios(), !dbg !725
  store i32 %14, i32* %5, align 4, !dbg !727
  store i32 0, i32* %5, align 4, !dbg !728
  %15 = load i32, i32* %5, align 4, !dbg !729
  %16 = icmp eq i32 %15, 0, !dbg !731
  br i1 %16, label %17, label %37, !dbg !732

; <label>:17:                                     ; preds = %13
  %18 = call i32 @pushover_init(i8* getelementptr inbounds ([18 x i8], [18 x i8]* @.str.13.34, i32 0, i32 0)), !dbg !733
  store i32 %18, i32* %5, align 4, !dbg !735
  store i32 0, i32* %5, align 4, !dbg !736
  %19 = load i32, i32* %5, align 4, !dbg !737
  %20 = icmp eq i32 %19, 0, !dbg !739
  br i1 %20, label %21, label %36, !dbg !740

; <label>:21:                                     ; preds = %17
  store i8 0, i8* getelementptr inbounds ([146 x i8], [146 x i8]* @Msg_info_str, i32 0, i32 0), align 1, !dbg !741
  %22 = load i32*, i32** %3, align 4, !dbg !743
  %23 = call i8* @polling_thread(i32* %22), !dbg !744
  %24 = load i32, i32* %5, align 4, !dbg !745
  %25 = icmp eq i32 %24, 0, !dbg !747
  br i1 %25, label %26, label %29, !dbg !748

; <label>:26:                                     ; preds = %21
  %27 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !749
  %28 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %27, i8* getelementptr inbounds ([26 x i8], [26 x i8]* @.str.14.35, i32 0, i32 0)), !dbg !749
  br label %35, !dbg !749

; <label>:29:                                     ; preds = %21
  %30 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !750
  %31 = load i32, i32* %5, align 4, !dbg !750
  %32 = load i32, i32* %5, align 4, !dbg !750
  %33 = call i8* @strerror(i32 %32) #7, !dbg !750
  %34 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %30, i8* getelementptr inbounds ([38 x i8], [38 x i8]* @.str.15.36, i32 0, i32 0), i32 %31, i8* %33), !dbg !751
  br label %35

; <label>:35:                                     ; preds = %29, %26
  br label %36, !dbg !753

; <label>:36:                                     ; preds = %35, %17
  br label %37, !dbg !754

; <label>:37:                                     ; preds = %36, %13
  br label %38, !dbg !755

; <label>:38:                                     ; preds = %37, %2
  call void @__AMI_fake_local_wrt(), !dbg !756
  store i32 0, i32* @recording_flag, align 4, !dbg !756
  call void @__AMI_fake_local_wrt(), !dbg !757
  store i32 1, i32* @ret_recording_finish, align 4, !dbg !757
  %39 = call i8* bitcast (i8* (...)* @read_measurement to i8* ()*)(), !dbg !758
  %40 = call i32 @usecs(), !dbg !759
  store i32 %40, i32* %7, align 4, !dbg !760
  %41 = load i32, i32* %7, align 4, !dbg !761
  %42 = load i32, i32* %6, align 4, !dbg !762
  %43 = sub i32 %41, %42, !dbg !763
  %44 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([40 x i8], [40 x i8]* @.str.16.37, i32 0, i32 0), i32 %43), !dbg !764
  %45 = load i32, i32* %5, align 4, !dbg !765
  call void @__AMI_fake_rt_transfer(), !dbg !766
  ret i32 %45, !dbg !766
}

declare void @create_files(i8*, i8*, i8*, i8*, i8*) #5 section ".CODE_REGION_1_"

declare i8* @read_measurement(...) #5 section ".CODE_REGION_1_"

; Function Attrs: nounwind
define i32 @wait_polling_end() #0 section ".CODE_REGION_2_" !dbg !767 {
  %1 = alloca i32, align 4
  call void @llvm.dbg.declare(metadata i32* %1, metadata !768, metadata !336), !dbg !769
  %2 = load i32, i32* @Polling_thread_id, align 4, !dbg !770
  %3 = call i32 @pthread_join(i32 %2, i8** null), !dbg !771
  store i32 %3, i32* %1, align 4, !dbg !772
  %4 = load i32, i32* %1, align 4, !dbg !773
  %5 = icmp eq i32 %4, 0, !dbg !775
  br i1 %5, label %6, label %9, !dbg !776

; <label>:6:                                      ; preds = %0
  %7 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !777
  call void @__AMI_fake_direct_transfer(), !dbg !777
  %8 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %7, i8* getelementptr inbounds ([37 x i8], [37 x i8]* @.str.17.40, i32 0, i32 0)), !dbg !777
  br label %12, !dbg !777

; <label>:9:                                      ; preds = %0
  %10 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !778
  call void @__AMI_fake_direct_transfer(), !dbg !778
  %11 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %10, i8* getelementptr inbounds ([48 x i8], [48 x i8]* @.str.18.41, i32 0, i32 0)), !dbg !778
  br label %12

; <label>:12:                                     ; preds = %9, %6
  %13 = call i32 @unexport_gpios(), !dbg !779
  %14 = load i32, i32* %1, align 4, !dbg !780
  ret i32 %14, !dbg !781
}

declare i32 @pthread_join(i32, i8**) #5 section ".CODE_REGION_2_"

; Function Attrs: nounwind
define i32 @pushover_init(i8*) #0 section ".CODE_REGION_1_" !dbg !782 {
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
  call void @llvm.dbg.declare(metadata i8** %3, metadata !783, metadata !336), !dbg !784
  call void @llvm.dbg.declare(metadata i32* %4, metadata !785, metadata !336), !dbg !786
  call void @llvm.dbg.declare(metadata %struct._IO_FILE** %5, metadata !787, metadata !336), !dbg !828
  call void @llvm.dbg.declare(metadata [4097 x i8]* %6, metadata !829, metadata !336), !dbg !833
  %13 = load i8*, i8** %3, align 4, !dbg !834
  %14 = call i32 @strlen(i8* %13) #9, !dbg !836
  %15 = icmp ugt i32 %14, 4096, !dbg !837
  br i1 %15, label %16, label %17, !dbg !838

; <label>:16:                                     ; preds = %1
  store i32 22, i32* %2, align 4, !dbg !839
  br label %213, !dbg !839

; <label>:17:                                     ; preds = %1
  %18 = load i8*, i8** %3, align 4, !dbg !840
  %19 = getelementptr inbounds i8, i8* %18, i32 0, !dbg !840
  %20 = load i8, i8* %19, align 1, !dbg !840
  %21 = zext i8 %20 to i32, !dbg !840
  %22 = icmp ne i32 %21, 47, !dbg !842
  br i1 %22, label %23, label %52, !dbg !843

; <label>:23:                                     ; preds = %17
  %24 = getelementptr inbounds [4097 x i8], [4097 x i8]* %6, i32 0, i32 0, !dbg !844
  %25 = call i32 @get_current_exec_path(i8* %24, i32 4096), !dbg !846
  store i32 %25, i32* %4, align 4, !dbg !847
  %26 = load i32, i32* %4, align 4, !dbg !848
  %27 = icmp eq i32 %26, 0, !dbg !850
  br i1 %27, label %28, label %44, !dbg !851

; <label>:28:                                     ; preds = %23
  %29 = getelementptr inbounds [4097 x i8], [4097 x i8]* %6, i32 0, i32 0, !dbg !852
  %30 = call i32 @strlen(i8* %29) #9, !dbg !855
  %31 = load i8*, i8** %3, align 4, !dbg !856
  %32 = call i32 @strlen(i8* %31) #9, !dbg !857
  %33 = add i32 %30, %32, !dbg !859
  %34 = icmp ule i32 %33, 4096, !dbg !860
  br i1 %34, label %35, label %39, !dbg !861

; <label>:35:                                     ; preds = %28
  %36 = getelementptr inbounds [4097 x i8], [4097 x i8]* %6, i32 0, i32 0, !dbg !862
  %37 = load i8*, i8** %3, align 4, !dbg !863
  %38 = call i8* @strcat(i8* %36, i8* %37) #7, !dbg !864
  br label %43, !dbg !864

; <label>:39:                                     ; preds = %28
  %40 = getelementptr inbounds [4097 x i8], [4097 x i8]* %6, i32 0, i32 0, !dbg !865
  %41 = load i8*, i8** %3, align 4, !dbg !866
  %42 = call i8* @strcpy(i8* %40, i8* %41) #7, !dbg !867
  br label %43

; <label>:43:                                     ; preds = %39, %35
  br label %51, !dbg !868

; <label>:44:                                     ; preds = %23
  %45 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !869
  %46 = load i32, i32* %4, align 4, !dbg !869
  %47 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %45, i8* getelementptr inbounds ([80 x i8], [80 x i8]* @.str.44, i32 0, i32 0), i32 %46), !dbg !869
  %48 = getelementptr inbounds [4097 x i8], [4097 x i8]* %6, i32 0, i32 0, !dbg !871
  %49 = load i8*, i8** %3, align 4, !dbg !872
  %50 = call i8* @strcpy(i8* %48, i8* %49) #7, !dbg !873
  br label %51

; <label>:51:                                     ; preds = %44, %43
  br label %56, !dbg !874

; <label>:52:                                     ; preds = %17
  %53 = getelementptr inbounds [4097 x i8], [4097 x i8]* %6, i32 0, i32 0, !dbg !875
  %54 = load i8*, i8** %3, align 4, !dbg !876
  %55 = call i8* @strcpy(i8* %53, i8* %54) #7, !dbg !877
  br label %56

; <label>:56:                                     ; preds = %52, %51
  %57 = getelementptr inbounds [4097 x i8], [4097 x i8]* %6, i32 0, i32 0, !dbg !878
  %58 = call %struct._IO_FILE* @fopen(i8* %57, i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.1.45, i32 0, i32 0)), !dbg !879
  store %struct._IO_FILE* %58, %struct._IO_FILE** %5, align 4, !dbg !880
  %59 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !881
  %60 = icmp ne %struct._IO_FILE* %59, null, !dbg !883
  br i1 %60, label %61, label %203, !dbg !884

; <label>:61:                                     ; preds = %56
  call void @llvm.dbg.declare(metadata [2084 x i8]* %7, metadata !885, metadata !336), !dbg !890
  %62 = getelementptr inbounds [2084 x i8], [2084 x i8]* %7, i32 0, i32 0, !dbg !891
  store i8 0, i8* %62, align 1, !dbg !892
  store i8 0, i8* getelementptr inbounds ([81 x i8], [81 x i8]* @Token_id, i32 0, i32 0), align 1, !dbg !893
  store i8 0, i8* getelementptr inbounds ([81 x i8], [81 x i8]* @User_id, i32 0, i32 0), align 1, !dbg !894
  %63 = call i8* @strcpy(i8* getelementptr inbounds ([65 x i8], [65 x i8]* @Server_path, i32 0, i32 0), i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.2.46, i32 0, i32 0)) #7, !dbg !895
  store i32 0, i32* %4, align 4, !dbg !896
  br label %64, !dbg !897

; <label>:64:                                     ; preds = %89, %61
  %65 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !898
  %66 = call i32 @feof(%struct._IO_FILE* %65) #7, !dbg !900
  %67 = icmp ne i32 %66, 0, !dbg !900
  br i1 %67, label %71, label %68, !dbg !901

; <label>:68:                                     ; preds = %64
  %69 = load i32, i32* %4, align 4, !dbg !902
  %70 = icmp eq i32 %69, 0, !dbg !904
  br label %71

; <label>:71:                                     ; preds = %68, %64
  %72 = phi i1 [ false, %64 ], [ %70, %68 ]
  br i1 %72, label %73, label %90, !dbg !905

; <label>:73:                                     ; preds = %71
  %74 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !907
  %75 = getelementptr inbounds [2084 x i8], [2084 x i8]* %7, i32 0, i32 0, !dbg !910
  %76 = call i32 (%struct._IO_FILE*, i8*, ...) @__isoc99_fscanf(%struct._IO_FILE* %74, i8* getelementptr inbounds ([21 x i8], [21 x i8]* @.str.3.47, i32 0, i32 0), i8* %75), !dbg !911
  %77 = icmp eq i32 %76, 0, !dbg !912
  br i1 %77, label %78, label %89, !dbg !913

; <label>:78:                                     ; preds = %73
  %79 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !914
  %80 = call i32 (%struct._IO_FILE*, i8*, ...) @__isoc99_fscanf(%struct._IO_FILE* %79, i8* getelementptr inbounds ([14 x i8], [14 x i8]* @.str.4.48, i32 0, i32 0), i8* getelementptr inbounds ([81 x i8], [81 x i8]* @Token_id, i32 0, i32 0)), !dbg !915
  %81 = icmp eq i32 %80, 0, !dbg !916
  br i1 %81, label %82, label %89, !dbg !917

; <label>:82:                                     ; preds = %78
  %83 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !918
  %84 = call i32 (%struct._IO_FILE*, i8*, ...) @__isoc99_fscanf(%struct._IO_FILE* %83, i8* getelementptr inbounds ([13 x i8], [13 x i8]* @.str.5.49, i32 0, i32 0), i8* getelementptr inbounds ([81 x i8], [81 x i8]* @User_id, i32 0, i32 0)), !dbg !919
  %85 = icmp eq i32 %84, 0, !dbg !920
  br i1 %85, label %86, label %89, !dbg !921

; <label>:86:                                     ; preds = %82
  %87 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !923
  %88 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %87, i8* getelementptr inbounds ([73 x i8], [73 x i8]* @.str.6.50, i32 0, i32 0)), !dbg !923
  store i32 22, i32* %4, align 4, !dbg !925
  br label %89, !dbg !926

; <label>:89:                                     ; preds = %86, %82, %78, %73
  br label %64, !dbg !927, !llvm.loop !929

; <label>:90:                                     ; preds = %71
  %91 = load i32, i32* %4, align 4, !dbg !930
  %92 = icmp eq i32 %91, 0, !dbg !932
  br i1 %92, label %93, label %200, !dbg !933

; <label>:93:                                     ; preds = %90
  %94 = getelementptr inbounds [2084 x i8], [2084 x i8]* %7, i32 0, i32 0, !dbg !934
  %95 = call i32 @strlen(i8* %94) #9, !dbg !937
  %96 = icmp ugt i32 %95, 0, !dbg !938
  br i1 %96, label %97, label %196, !dbg !939

; <label>:97:                                     ; preds = %93
  %98 = call i32 @strlen(i8* getelementptr inbounds ([81 x i8], [81 x i8]* @Token_id, i32 0, i32 0)) #9, !dbg !940
  %99 = icmp ugt i32 %98, 0, !dbg !943
  br i1 %99, label %100, label %192, !dbg !944

; <label>:100:                                    ; preds = %97
  %101 = call i32 @strlen(i8* getelementptr inbounds ([81 x i8], [81 x i8]* @User_id, i32 0, i32 0)) #9, !dbg !945
  %102 = icmp ugt i32 %101, 0, !dbg !948
  br i1 %102, label %103, label %188, !dbg !949

; <label>:103:                                    ; preds = %100
  %104 = getelementptr inbounds [2084 x i8], [2084 x i8]* %7, i32 0, i32 0, !dbg !950
  %105 = call i32 @strncmp(i8* %104, i8* getelementptr inbounds ([8 x i8], [8 x i8]* @.str.7.51, i32 0, i32 0), i32 7) #9, !dbg !953
  %106 = icmp eq i32 %105, 0, !dbg !954
  br i1 %106, label %107, label %184, !dbg !955

; <label>:107:                                    ; preds = %103
  call void @llvm.dbg.declare(metadata i8** %8, metadata !956, metadata !336), !dbg !958
  call void @llvm.dbg.declare(metadata i8** %9, metadata !959, metadata !336), !dbg !960
  call void @llvm.dbg.declare(metadata i8** %10, metadata !961, metadata !336), !dbg !962
  call void @llvm.dbg.declare(metadata i32* %11, metadata !963, metadata !336), !dbg !964
  %108 = getelementptr inbounds [2084 x i8], [2084 x i8]* %7, i32 0, i32 0, !dbg !965
  %109 = getelementptr inbounds i8, i8* %108, i32 7, !dbg !966
  %110 = call i8* @strchr(i8* %109, i32 64) #9, !dbg !967
  store i8* %110, i8** %8, align 4, !dbg !968
  %111 = load i8*, i8** %8, align 4, !dbg !969
  %112 = icmp eq i8* %111, null, !dbg !971
  br i1 %112, label %113, label %116, !dbg !972

; <label>:113:                                    ; preds = %107
  %114 = getelementptr inbounds [2084 x i8], [2084 x i8]* %7, i32 0, i32 0, !dbg !973
  %115 = getelementptr inbounds i8, i8* %114, i32 7, !dbg !974
  store i8* %115, i8** %8, align 4, !dbg !975
  br label %119, !dbg !976

; <label>:116:                                    ; preds = %107
  %117 = load i8*, i8** %8, align 4, !dbg !977
  %118 = getelementptr inbounds i8, i8* %117, i32 1, !dbg !977
  store i8* %118, i8** %8, align 4, !dbg !977
  br label %119

; <label>:119:                                    ; preds = %116, %113
  %120 = load i8*, i8** %8, align 4, !dbg !978
  %121 = call i8* @strchr(i8* %120, i32 58) #9, !dbg !979
  store i8* %121, i8** %9, align 4, !dbg !980
  %122 = load i8*, i8** %9, align 4, !dbg !981
  %123 = icmp eq i8* %122, null, !dbg !983
  br i1 %123, label %124, label %135, !dbg !984

; <label>:124:                                    ; preds = %119
  call void @__AMI_fake_local_wrt(), !dbg !985
  store i32 3000, i32* @Server_port, align 4, !dbg !985
  %125 = load i8*, i8** %8, align 4, !dbg !987
  %126 = call i8* @strchr(i8* %125, i32 47) #9, !dbg !988
  store i8* %126, i8** %9, align 4, !dbg !989
  %127 = load i8*, i8** %9, align 4, !dbg !990
  %128 = icmp eq i8* %127, null, !dbg !992
  br i1 %128, label %129, label %134, !dbg !993

; <label>:129:                                    ; preds = %124
  %130 = load i8*, i8** %8, align 4, !dbg !994
  %131 = load i8*, i8** %8, align 4, !dbg !995
  %132 = call i32 @strlen(i8* %131) #9, !dbg !996
  %133 = getelementptr inbounds i8, i8* %130, i32 %132, !dbg !997
  store i8* %133, i8** %9, align 4, !dbg !998
  br label %134, !dbg !999

; <label>:134:                                    ; preds = %129, %124
  br label %142, !dbg !1000

; <label>:135:                                    ; preds = %119
  %136 = load i8*, i8** %9, align 4, !dbg !1001
  %137 = getelementptr inbounds i8, i8* %136, i32 1, !dbg !1004
  %138 = call i32 (i8*, i8*, ...) @__isoc99_sscanf(i8* %137, i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.8.52, i32 0, i32 0), i32* @Server_port) #7, !dbg !1005
  %139 = icmp eq i32 %138, 0, !dbg !1006
  br i1 %139, label %140, label %141, !dbg !1007

; <label>:140:                                    ; preds = %135
  call void @__AMI_fake_local_wrt(), !dbg !1008
  store i32 3000, i32* @Server_port, align 4, !dbg !1008
  br label %141, !dbg !1009

; <label>:141:                                    ; preds = %140, %135
  br label %142

; <label>:142:                                    ; preds = %141, %134
  %143 = load i8*, i8** %9, align 4, !dbg !1010
  %144 = call i8* @strchr(i8* %143, i32 47) #9, !dbg !1011
  store i8* %144, i8** %10, align 4, !dbg !1012
  %145 = load i8*, i8** %10, align 4, !dbg !1013
  %146 = icmp ne i8* %145, null, !dbg !1015
  br i1 %146, label %147, label %158, !dbg !1016

; <label>:147:                                    ; preds = %142
  call void @llvm.dbg.declare(metadata i32* %12, metadata !1017, metadata !336), !dbg !1019
  %148 = load i8*, i8** %10, align 4, !dbg !1020
  %149 = call i32 @strlen(i8* %148) #9, !dbg !1021
  store i32 %149, i32* %12, align 4, !dbg !1022
  %150 = load i32, i32* %12, align 4, !dbg !1023
  %151 = icmp ule i32 %150, 2083, !dbg !1025
  br i1 %151, label %152, label %157, !dbg !1026

; <label>:152:                                    ; preds = %147
  %153 = load i8*, i8** %10, align 4, !dbg !1027
  %154 = load i32, i32* %12, align 4, !dbg !1029
  call void @llvm.memcpy.p0i8.p0i8.i32(i8* getelementptr inbounds ([65 x i8], [65 x i8]* @Server_path, i32 0, i32 0), i8* %153, i32 %154, i32 1, i1 false), !dbg !1030
  %155 = load i32, i32* %12, align 4, !dbg !1031
  %156 = getelementptr inbounds [65 x i8], [65 x i8]* @Server_path, i32 0, i32 %155, !dbg !1032
  store i8 0, i8* %156, align 1, !dbg !1033
  br label %157, !dbg !1034

; <label>:157:                                    ; preds = %152, %147
  br label %158, !dbg !1035

; <label>:158:                                    ; preds = %157, %142
  %159 = load i8*, i8** %9, align 4, !dbg !1036
  %160 = load i8*, i8** %8, align 4, !dbg !1037
  %161 = ptrtoint i8* %159 to i32, !dbg !1038
  %162 = ptrtoint i8* %160 to i32, !dbg !1038
  %163 = sub i32 %161, %162, !dbg !1038
  store i32 %163, i32* %11, align 4, !dbg !1039
  %164 = load i32, i32* %11, align 4, !dbg !1040
  %165 = icmp ule i32 %164, 64, !dbg !1042
  br i1 %165, label %166, label %180, !dbg !1043

; <label>:166:                                    ; preds = %158
  %167 = load i8*, i8** %8, align 4, !dbg !1044
  %168 = load i32, i32* %11, align 4, !dbg !1046
  call void @llvm.memcpy.p0i8.p0i8.i32(i8* getelementptr inbounds ([65 x i8], [65 x i8]* @Server_name, i32 0, i32 0), i8* %167, i32 %168, i32 1, i1 false), !dbg !1047
  %169 = load i32, i32* %11, align 4, !dbg !1048
  %170 = getelementptr inbounds [65 x i8], [65 x i8]* @Server_name, i32 0, i32 %169, !dbg !1049
  store i8 0, i8* %170, align 1, !dbg !1050
  %171 = call i32 @hostname_to_ip(i8* getelementptr inbounds ([65 x i8], [65 x i8]* @Server_name, i32 0, i32 0), %struct.in_addr* @Server_ip), !dbg !1051
  store i32 %171, i32* %4, align 4, !dbg !1052
  %172 = load i32, i32* %4, align 4, !dbg !1053
  %173 = icmp eq i32 %172, 0, !dbg !1055
  br i1 %173, label %174, label %179, !dbg !1056

; <label>:174:                                    ; preds = %166
  %175 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1057
  %176 = load [1 x i32], [1 x i32]* bitcast (%struct.in_addr* @Server_ip to [1 x i32]*), align 4, !dbg !1057
  %177 = call i8* @inet_ntoa([1 x i32] %176) #7, !dbg !1057
  %178 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %175, i8* getelementptr inbounds ([44 x i8], [44 x i8]* @.str.9.53, i32 0, i32 0), i8* %177), !dbg !1059
  br label %179, !dbg !1061

; <label>:179:                                    ; preds = %174, %166
  br label %183, !dbg !1062

; <label>:180:                                    ; preds = %158
  %181 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1063
  %182 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %181, i8* getelementptr inbounds ([86 x i8], [86 x i8]* @.str.10.54, i32 0, i32 0)), !dbg !1063
  store i32 22, i32* %4, align 4, !dbg !1065
  br label %183

; <label>:183:                                    ; preds = %180, %179
  br label %187, !dbg !1066

; <label>:184:                                    ; preds = %103
  %185 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1067
  %186 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %185, i8* getelementptr inbounds ([69 x i8], [69 x i8]* @.str.11.55, i32 0, i32 0)), !dbg !1067
  store i32 22, i32* %4, align 4, !dbg !1069
  br label %187

; <label>:187:                                    ; preds = %184, %183
  br label %191, !dbg !1070

; <label>:188:                                    ; preds = %100
  %189 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1071
  %190 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %189, i8* getelementptr inbounds ([55 x i8], [55 x i8]* @.str.12.56, i32 0, i32 0)), !dbg !1071
  store i32 22, i32* %4, align 4, !dbg !1073
  br label %191

; <label>:191:                                    ; preds = %188, %187
  br label %195, !dbg !1074

; <label>:192:                                    ; preds = %97
  %193 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1075
  %194 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %193, i8* getelementptr inbounds ([56 x i8], [56 x i8]* @.str.13.57, i32 0, i32 0)), !dbg !1075
  store i32 22, i32* %4, align 4, !dbg !1077
  br label %195

; <label>:195:                                    ; preds = %192, %191
  br label %199, !dbg !1078

; <label>:196:                                    ; preds = %93
  %197 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1079
  %198 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %197, i8* getelementptr inbounds ([58 x i8], [58 x i8]* @.str.14.58, i32 0, i32 0)), !dbg !1079
  store i32 22, i32* %4, align 4, !dbg !1081
  br label %199

; <label>:199:                                    ; preds = %196, %195
  br label %200, !dbg !1082

; <label>:200:                                    ; preds = %199, %90
  %201 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !1083
  %202 = call i32 @fclose(%struct._IO_FILE* %201), !dbg !1084
  br label %211, !dbg !1085

; <label>:203:                                    ; preds = %56
  %204 = call i32* @__errno_location() #1, !dbg !1086
  %205 = load i32, i32* %204, align 4, !dbg !1086
  store i32 %205, i32* %4, align 4, !dbg !1088
  %206 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1089
  %207 = getelementptr inbounds [4097 x i8], [4097 x i8]* %6, i32 0, i32 0, !dbg !1089
  %208 = call i32* @__errno_location() #1, !dbg !1089
  %209 = load i32, i32* %208, align 4, !dbg !1089
  %210 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %206, i8* getelementptr inbounds ([49 x i8], [49 x i8]* @.str.15.59, i32 0, i32 0), i8* %207, i32 %209), !dbg !1090
  br label %211

; <label>:211:                                    ; preds = %203, %200
  %212 = load i32, i32* %4, align 4, !dbg !1092
  store i32 %212, i32* %2, align 4, !dbg !1093
  br label %213, !dbg !1093

; <label>:213:                                    ; preds = %211, %16
  %214 = load i32, i32* %2, align 4, !dbg !1094
  ret i32 %214, !dbg !1094
}

; Function Attrs: nounwind readonly
declare i32 @strlen(i8*) #6 section ".CODE_REGION_1_"

; Function Attrs: nounwind
declare i8* @strcat(i8*, i8*) #2 section ".CODE_REGION_1_"

declare %struct._IO_FILE* @fopen(i8*, i8*) #5 section ".CODE_REGION_1_"

; Function Attrs: nounwind
declare i32 @feof(%struct._IO_FILE*) #2 section ".CODE_REGION_1_"

declare i32 @__isoc99_fscanf(%struct._IO_FILE*, i8*, ...) #5 section ".CODE_REGION_1_"

; Function Attrs: nounwind readonly
declare i32 @strncmp(i8*, i8*, i32) #6 section ".CODE_REGION_1_"

; Function Attrs: nounwind readonly
declare i8* @strchr(i8*, i32) #6 section ".CODE_REGION_1_"

; Function Attrs: nounwind
declare i32 @__isoc99_sscanf(i8*, i8*, ...) #2 section ".CODE_REGION_1_"

; Function Attrs: argmemonly nounwind
declare void @llvm.memcpy.p0i8.p0i8.i32(i8* nocapture writeonly, i8* nocapture readonly, i32, i32, i1) #3

; Function Attrs: nounwind
declare i8* @inet_ntoa([1 x i32]) #2 section ".CODE_REGION_1_"

declare i32 @fclose(%struct._IO_FILE*) #5 section ".CODE_REGION_1_"

; Function Attrs: nounwind
define i32 @send_notification(i8*, i8*) #0 section ".CODE_REGION_2_" !dbg !1095 {
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
  call void @llvm.dbg.declare(metadata i8** %3, metadata !1096, metadata !336), !dbg !1097
  store i8* %1, i8** %4, align 4
  call void @llvm.dbg.declare(metadata i8** %4, metadata !1098, metadata !336), !dbg !1099
  call void @llvm.dbg.declare(metadata i32* %5, metadata !1100, metadata !336), !dbg !1101
  store i32 0, i32* %5, align 4, !dbg !1101
  call void @llvm.dbg.declare(metadata i32* %6, metadata !1102, metadata !336), !dbg !1103
  call void @llvm.dbg.declare(metadata %struct.sockaddr_in* %7, metadata !1104, metadata !336), !dbg !1111
  %20 = call i32 @socket(i32 2, i32 1, i32 0) #7, !dbg !1112
  store i32 %20, i32* %6, align 4, !dbg !1113
  %21 = load i32, i32* %6, align 4, !dbg !1114
  %22 = icmp ne i32 %21, -1, !dbg !1116
  br i1 %22, label %23, label %214, !dbg !1117

; <label>:23:                                     ; preds = %2
  %24 = bitcast %struct.sockaddr_in* %7 to i8*, !dbg !1118
  call void @llvm.memset.p0i8.i32(i8* %24, i8 0, i32 16, i32 4, i1 false), !dbg !1118
  %25 = getelementptr inbounds %struct.sockaddr_in, %struct.sockaddr_in* %7, i32 0, i32 0, !dbg !1120
  store i16 2, i16* %25, align 4, !dbg !1121
  %26 = load i32, i32* @Server_port, align 4, !dbg !1122
  %27 = trunc i32 %26 to i16, !dbg !1122
  %28 = call zeroext i16 @htons(i16 zeroext %27) #1, !dbg !1123
  %29 = getelementptr inbounds %struct.sockaddr_in, %struct.sockaddr_in* %7, i32 0, i32 1, !dbg !1124
  store i16 %28, i16* %29, align 2, !dbg !1125
  %30 = getelementptr inbounds %struct.sockaddr_in, %struct.sockaddr_in* %7, i32 0, i32 2, !dbg !1126
  %31 = bitcast %struct.in_addr* %30 to i8*, !dbg !1127
  call void @llvm.memcpy.p0i8.p0i8.i32(i8* %31, i8* bitcast (%struct.in_addr* @Server_ip to i8*), i32 4, i32 4, i1 false), !dbg !1127
  %32 = load i32, i32* %6, align 4, !dbg !1128
  %33 = bitcast %struct.sockaddr_in* %7 to %struct.sockaddr*, !dbg !1129
  %34 = call i32 @connect(i32 %32, %struct.sockaddr* %33, i32 16), !dbg !1130
  store i32 %34, i32* %5, align 4, !dbg !1131
  %35 = load i32, i32* %5, align 4, !dbg !1132
  %36 = icmp eq i32 %35, 0, !dbg !1134
  br i1 %36, label %37, label %201, !dbg !1135

; <label>:37:                                     ; preds = %23
  call void @llvm.dbg.declare(metadata %struct._IO_FILE** %8, metadata !1136, metadata !336), !dbg !1138
  %38 = load i32, i32* %6, align 4, !dbg !1139
  %39 = call %struct._IO_FILE* @fdopen(i32 %38, i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str.16.62, i32 0, i32 0)) #7, !dbg !1140
  store %struct._IO_FILE* %39, %struct._IO_FILE** %8, align 4, !dbg !1141
  %40 = load %struct._IO_FILE*, %struct._IO_FILE** %8, align 4, !dbg !1142
  %41 = icmp ne %struct._IO_FILE* %40, null, !dbg !1144
  br i1 %41, label %42, label %190, !dbg !1145

; <label>:42:                                     ; preds = %37
  call void @llvm.dbg.declare(metadata i32* %9, metadata !1146, metadata !336), !dbg !1148
  call void @llvm.dbg.declare(metadata i32* %10, metadata !1149, metadata !336), !dbg !1150
  call void @llvm.dbg.declare(metadata i32* %11, metadata !1151, metadata !336), !dbg !1152
  %43 = call i32 @strlen(i8* getelementptr inbounds ([81 x i8], [81 x i8]* @Token_id, i32 0, i32 0)) #9, !dbg !1153
  %44 = add i32 6, %43, !dbg !1154
  %45 = add i32 %44, 1, !dbg !1155
  %46 = add i32 %45, 5, !dbg !1156
  %47 = call i32 @strlen(i8* getelementptr inbounds ([81 x i8], [81 x i8]* @User_id, i32 0, i32 0)) #9, !dbg !1157
  %48 = add i32 %46, %47, !dbg !1159
  %49 = add i32 %48, 1, !dbg !1160
  %50 = add i32 %49, 8, !dbg !1161
  %51 = load i8*, i8** %3, align 4, !dbg !1162
  %52 = call i32 @strlen(i8* %51) #9, !dbg !1163
  %53 = add i32 %50, %52, !dbg !1165
  %54 = add i32 %53, 1, !dbg !1166
  %55 = add i32 %54, 9, !dbg !1167
  %56 = load i8*, i8** %4, align 4, !dbg !1168
  %57 = call i32 @strlen(i8* %56) #9, !dbg !1169
  %58 = add i32 %55, %57, !dbg !1171
  store i32 %58, i32* %9, align 4, !dbg !1172
  %59 = load i8*, i8** %4, align 4, !dbg !1173
  %60 = call i32 @strcmp(i8* %59, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.17.63, i32 0, i32 0)) #9, !dbg !1175
  %61 = icmp eq i32 %60, 0, !dbg !1176
  br i1 %61, label %62, label %65, !dbg !1177

; <label>:62:                                     ; preds = %42
  %63 = load i32, i32* %9, align 4, !dbg !1178
  %64 = add i32 %63, 20, !dbg !1178
  store i32 %64, i32* %9, align 4, !dbg !1178
  br label %65, !dbg !1179

; <label>:65:                                     ; preds = %62, %42
  %66 = load %struct._IO_FILE*, %struct._IO_FILE** %8, align 4, !dbg !1180
  %67 = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %66, i8* getelementptr inbounds ([19 x i8], [19 x i8]* @.str.18.64, i32 0, i32 0), i8* getelementptr inbounds ([65 x i8], [65 x i8]* @Server_path, i32 0, i32 0)), !dbg !1181
  %68 = load %struct._IO_FILE*, %struct._IO_FILE** %8, align 4, !dbg !1182
  %69 = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %68, i8* getelementptr inbounds ([11 x i8], [11 x i8]* @.str.19.65, i32 0, i32 0), i8* getelementptr inbounds ([65 x i8], [65 x i8]* @Server_name, i32 0, i32 0)), !dbg !1183
  %70 = load %struct._IO_FILE*, %struct._IO_FILE** %8, align 4, !dbg !1184
  %71 = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %70, i8* getelementptr inbounds ([50 x i8], [50 x i8]* @.str.20, i32 0, i32 0)), !dbg !1185
  %72 = load %struct._IO_FILE*, %struct._IO_FILE** %8, align 4, !dbg !1186
  %73 = load i32, i32* %9, align 4, !dbg !1187
  %74 = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %72, i8* getelementptr inbounds ([24 x i8], [24 x i8]* @.str.21, i32 0, i32 0), i32 %73), !dbg !1188
  %75 = load %struct._IO_FILE*, %struct._IO_FILE** %8, align 4, !dbg !1189
  %76 = load i8*, i8** %3, align 4, !dbg !1190
  %77 = load i8*, i8** %4, align 4, !dbg !1191
  %78 = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %75, i8* getelementptr inbounds ([40 x i8], [40 x i8]* @.str.22, i32 0, i32 0), i8* getelementptr inbounds ([81 x i8], [81 x i8]* @Token_id, i32 0, i32 0), i8* getelementptr inbounds ([81 x i8], [81 x i8]* @User_id, i32 0, i32 0), i8* %76, i8* %77), !dbg !1192
  %79 = load i8*, i8** %4, align 4, !dbg !1193
  %80 = call i32 @strcmp(i8* %79, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.17.63, i32 0, i32 0)) #9, !dbg !1195
  %81 = icmp eq i32 %80, 0, !dbg !1196
  br i1 %81, label %82, label %85, !dbg !1197

; <label>:82:                                     ; preds = %65
  %83 = load %struct._IO_FILE*, %struct._IO_FILE** %8, align 4, !dbg !1198
  %84 = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %83, i8* getelementptr inbounds ([21 x i8], [21 x i8]* @.str.23, i32 0, i32 0)), !dbg !1199
  br label %85, !dbg !1199

; <label>:85:                                     ; preds = %82, %65
  %86 = load %struct._IO_FILE*, %struct._IO_FILE** %8, align 4, !dbg !1200
  %87 = call i32 (%struct._IO_FILE*, i8*, ...) @__isoc99_fscanf(%struct._IO_FILE* %86, i8* getelementptr inbounds ([23 x i8], [23 x i8]* @.str.24, i32 0, i32 0), i32* %10), !dbg !1201
  store i32 %87, i32* %11, align 4, !dbg !1202
  %88 = load i32, i32* %11, align 4, !dbg !1203
  %89 = icmp eq i32 %88, 1, !dbg !1205
  br i1 %89, label %90, label %179, !dbg !1206

; <label>:90:                                     ; preds = %85
  %91 = load i32, i32* %10, align 4, !dbg !1207
  %92 = icmp eq i32 %91, 200, !dbg !1210
  br i1 %92, label %93, label %174, !dbg !1211

; <label>:93:                                     ; preds = %90
  call void @llvm.dbg.declare(metadata [2084 x i8]* %12, metadata !1212, metadata !336), !dbg !1214
  call void @llvm.dbg.declare(metadata i8** %13, metadata !1215, metadata !336), !dbg !1216
  call void @llvm.dbg.declare(metadata i32* %14, metadata !1217, metadata !336), !dbg !1218
  call void @llvm.dbg.declare(metadata i32* %15, metadata !1219, metadata !336), !dbg !1220
  store i32 0, i32* %15, align 4, !dbg !1221
  store i32 0, i32* %14, align 4, !dbg !1222
  br label %94, !dbg !1223

; <label>:94:                                     ; preds = %111, %93
  %95 = getelementptr inbounds [2084 x i8], [2084 x i8]* %12, i32 0, i32 0, !dbg !1224
  %96 = load %struct._IO_FILE*, %struct._IO_FILE** %8, align 4, !dbg !1226
  %97 = call i8* @fgets(i8* %95, i32 2083, %struct._IO_FILE* %96), !dbg !1227
  store i8* %97, i8** %13, align 4, !dbg !1228
  %98 = icmp ne i8* %97, null, !dbg !1229
  br i1 %98, label %99, label %112, !dbg !1230

; <label>:99:                                     ; preds = %94
  %100 = getelementptr inbounds [2084 x i8], [2084 x i8]* %12, i32 0, i32 0, !dbg !1231
  %101 = load i8, i8* %100, align 1, !dbg !1231
  %102 = zext i8 %101 to i32, !dbg !1231
  %103 = icmp eq i32 %102, 13, !dbg !1234
  br i1 %103, label %104, label %105, !dbg !1235

; <label>:104:                                    ; preds = %99
  br label %112, !dbg !1236

; <label>:105:                                    ; preds = %99
  %106 = load i32, i32* %14, align 4, !dbg !1237
  %107 = add i32 %106, 1, !dbg !1237
  store i32 %107, i32* %14, align 4, !dbg !1237
  %108 = load i32, i32* %14, align 4, !dbg !1238
  %109 = icmp ugt i32 %108, 1024, !dbg !1240
  br i1 %109, label %110, label %111, !dbg !1241

; <label>:110:                                    ; preds = %105
  store i8* null, i8** %13, align 4, !dbg !1242
  store i32 1, i32* %15, align 4, !dbg !1244
  br label %112, !dbg !1245

; <label>:111:                                    ; preds = %105
  br label %94, !dbg !1246, !llvm.loop !1248

; <label>:112:                                    ; preds = %110, %104, %94
  %113 = load i8*, i8** %13, align 4, !dbg !1249
  %114 = icmp ne i8* %113, null, !dbg !1251
  br i1 %114, label %115, label %161, !dbg !1252

; <label>:115:                                    ; preds = %112
  call void @llvm.dbg.declare(metadata i32* %16, metadata !1253, metadata !336), !dbg !1255
  call void @llvm.dbg.declare(metadata i32* %17, metadata !1256, metadata !336), !dbg !1257
  call void @llvm.dbg.declare(metadata [2084 x i8]* %18, metadata !1258, metadata !336), !dbg !1259
  call void @llvm.dbg.declare(metadata [2084 x i8]* %19, metadata !1260, metadata !336), !dbg !1261
  %116 = load %struct._IO_FILE*, %struct._IO_FILE** %8, align 4, !dbg !1262
  %117 = call i32 (%struct._IO_FILE*, i8*, ...) @__isoc99_fscanf(%struct._IO_FILE* %116, i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str.25, i32 0, i32 0)), !dbg !1263
  store i32 0, i32* %17, align 4, !dbg !1264
  br label %118, !dbg !1265

; <label>:118:                                    ; preds = %142, %115
  %119 = load %struct._IO_FILE*, %struct._IO_FILE** %8, align 4, !dbg !1266
  %120 = getelementptr inbounds [2084 x i8], [2084 x i8]* %18, i32 0, i32 0, !dbg !1268
  %121 = call i32 (%struct._IO_FILE*, i8*, ...) @__isoc99_fscanf(%struct._IO_FILE* %119, i8* getelementptr inbounds ([12 x i8], [12 x i8]* @.str.26, i32 0, i32 0), i8* %120), !dbg !1269
  %122 = icmp eq i32 %121, 1, !dbg !1270
  br i1 %122, label %123, label %143, !dbg !1271

; <label>:123:                                    ; preds = %118
  %124 = load %struct._IO_FILE*, %struct._IO_FILE** %8, align 4, !dbg !1272
  %125 = call i32 (%struct._IO_FILE*, i8*, ...) @__isoc99_fscanf(%struct._IO_FILE* %124, i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.27, i32 0, i32 0)), !dbg !1274
  %126 = load %struct._IO_FILE*, %struct._IO_FILE** %8, align 4, !dbg !1275
  %127 = getelementptr inbounds [2084 x i8], [2084 x i8]* %19, i32 0, i32 0, !dbg !1277
  %128 = call i32 (%struct._IO_FILE*, i8*, ...) @__isoc99_fscanf(%struct._IO_FILE* %126, i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.28, i32 0, i32 0), i8* %127), !dbg !1278
  %129 = icmp eq i32 %128, 1, !dbg !1279
  br i1 %129, label %130, label %142, !dbg !1280

; <label>:130:                                    ; preds = %123
  %131 = load %struct._IO_FILE*, %struct._IO_FILE** %8, align 4, !dbg !1281
  %132 = call i32 (%struct._IO_FILE*, i8*, ...) @__isoc99_fscanf(%struct._IO_FILE* %131, i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.27, i32 0, i32 0)), !dbg !1283
  %133 = load %struct._IO_FILE*, %struct._IO_FILE** %8, align 4, !dbg !1284
  %134 = call i32 (%struct._IO_FILE*, i8*, ...) @__isoc99_fscanf(%struct._IO_FILE* %133, i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.29, i32 0, i32 0)), !dbg !1285
  %135 = getelementptr inbounds [2084 x i8], [2084 x i8]* %18, i32 0, i32 0, !dbg !1286
  %136 = call i32 @strcmp(i8* %135, i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.30, i32 0, i32 0)) #9, !dbg !1288
  %137 = icmp eq i32 %136, 0, !dbg !1289
  br i1 %137, label %138, label %141, !dbg !1290

; <label>:138:                                    ; preds = %130
  %139 = getelementptr inbounds [2084 x i8], [2084 x i8]* %19, i32 0, i32 0, !dbg !1291
  %140 = call i32 @atoi(i8* %139) #9, !dbg !1293
  store i32 %140, i32* %16, align 4, !dbg !1294
  store i32 1, i32* %17, align 4, !dbg !1295
  br label %141, !dbg !1296

; <label>:141:                                    ; preds = %138, %130
  br label %142, !dbg !1297

; <label>:142:                                    ; preds = %141, %123
  br label %118, !dbg !1298, !llvm.loop !1300

; <label>:143:                                    ; preds = %118
  %144 = load %struct._IO_FILE*, %struct._IO_FILE** %8, align 4, !dbg !1301
  %145 = call i32 (%struct._IO_FILE*, i8*, ...) @__isoc99_fscanf(%struct._IO_FILE* %144, i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.31, i32 0, i32 0)), !dbg !1302
  %146 = load i32, i32* %17, align 4, !dbg !1303
  %147 = icmp ne i32 %146, 0, !dbg !1305
  br i1 %147, label %148, label %157, !dbg !1306

; <label>:148:                                    ; preds = %143
  %149 = load i32, i32* %16, align 4, !dbg !1307
  %150 = icmp eq i32 %149, 1, !dbg !1310
  br i1 %150, label %151, label %152, !dbg !1311

; <label>:151:                                    ; preds = %148
  store i32 0, i32* %5, align 4, !dbg !1312
  br label %156, !dbg !1314

; <label>:152:                                    ; preds = %148
  store i32 56, i32* %5, align 4, !dbg !1315
  %153 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1317
  %154 = load i32, i32* %16, align 4, !dbg !1317
  call void @__AMI_fake_direct_transfer(), !dbg !1317
  %155 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %153, i8* getelementptr inbounds ([52 x i8], [52 x i8]* @.str.32, i32 0, i32 0), i32 %154), !dbg !1317
  br label %156

; <label>:156:                                    ; preds = %152, %151
  br label %160, !dbg !1318

; <label>:157:                                    ; preds = %143
  store i32 71, i32* %5, align 4, !dbg !1319
  %158 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1321
  call void @__AMI_fake_direct_transfer(), !dbg !1321
  %159 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %158, i8* getelementptr inbounds ([89 x i8], [89 x i8]* @.str.33, i32 0, i32 0)), !dbg !1321
  br label %160

; <label>:160:                                    ; preds = %157, %156
  br label %173, !dbg !1322

; <label>:161:                                    ; preds = %112
  %162 = load i32, i32* %15, align 4, !dbg !1323
  %163 = icmp ne i32 %162, 0, !dbg !1326
  br i1 %163, label %164, label %167, !dbg !1327

; <label>:164:                                    ; preds = %161
  store i32 71, i32* %5, align 4, !dbg !1328
  %165 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1330
  call void @__AMI_fake_direct_transfer(), !dbg !1330
  %166 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %165, i8* getelementptr inbounds ([59 x i8], [59 x i8]* @.str.34, i32 0, i32 0)), !dbg !1330
  br label %172, !dbg !1331

; <label>:167:                                    ; preds = %161
  store i32 71, i32* %5, align 4, !dbg !1332
  %168 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1334
  %169 = call i32* @__errno_location() #1, !dbg !1334
  %170 = load i32, i32* %169, align 4, !dbg !1334
  call void @__AMI_fake_direct_transfer(), !dbg !1335
  %171 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %168, i8* getelementptr inbounds ([84 x i8], [84 x i8]* @.str.35, i32 0, i32 0), i32 %170), !dbg !1335
  br label %172

; <label>:172:                                    ; preds = %167, %164
  br label %173

; <label>:173:                                    ; preds = %172, %160
  br label %178, !dbg !1337

; <label>:174:                                    ; preds = %90
  store i32 56, i32* %5, align 4, !dbg !1338
  %175 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1340
  %176 = load i32, i32* %10, align 4, !dbg !1340
  call void @__AMI_fake_direct_transfer(), !dbg !1340
  %177 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %175, i8* getelementptr inbounds ([50 x i8], [50 x i8]* @.str.36, i32 0, i32 0), i32 %176), !dbg !1340
  br label %178

; <label>:178:                                    ; preds = %174, %173
  br label %187, !dbg !1341

; <label>:179:                                    ; preds = %85
  %180 = call i32* @__errno_location() #1, !dbg !1342
  %181 = load i32, i32* %180, align 4, !dbg !1342
  store i32 %181, i32* %5, align 4, !dbg !1344
  %182 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1345
  %183 = load i32, i32* %11, align 4, !dbg !1345
  %184 = call i32* @__errno_location() #1, !dbg !1345
  %185 = load i32, i32* %184, align 4, !dbg !1345
  call void @__AMI_fake_direct_transfer(), !dbg !1346
  %186 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %182, i8* getelementptr inbounds ([77 x i8], [77 x i8]* @.str.37, i32 0, i32 0), i32 %183, i32 %185), !dbg !1346
  br label %187

; <label>:187:                                    ; preds = %179, %178
  %188 = load %struct._IO_FILE*, %struct._IO_FILE** %8, align 4, !dbg !1348
  %189 = call i32 @fclose(%struct._IO_FILE* %188), !dbg !1349
  br label %200, !dbg !1350

; <label>:190:                                    ; preds = %37
  %191 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1351
  %192 = call i32* @__errno_location() #1, !dbg !1351
  %193 = load i32, i32* %192, align 4, !dbg !1351
  %194 = call i32* @__errno_location() #1, !dbg !1353
  %195 = load i32, i32* %194, align 4, !dbg !1351
  %196 = call i8* @strerror(i32 %195) #7, !dbg !1355
  call void @__AMI_fake_direct_transfer(), !dbg !1357
  %197 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %191, i8* getelementptr inbounds ([73 x i8], [73 x i8]* @.str.38, i32 0, i32 0), i32 %193, i8* %196), !dbg !1357
  %198 = load i32, i32* %6, align 4, !dbg !1359
  %199 = call i32 @close(i32 %198), !dbg !1360
  br label %200

; <label>:200:                                    ; preds = %190, %187
  br label %213, !dbg !1361

; <label>:201:                                    ; preds = %23
  %202 = call i32* @__errno_location() #1, !dbg !1362
  %203 = load i32, i32* %202, align 4, !dbg !1362
  store i32 %203, i32* %5, align 4, !dbg !1364
  %204 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1365
  %205 = call i32* @__errno_location() #1, !dbg !1365
  %206 = load i32, i32* %205, align 4, !dbg !1365
  %207 = call i32* @__errno_location() #1, !dbg !1366
  %208 = load i32, i32* %207, align 4, !dbg !1365
  %209 = call i8* @strerror(i32 %208) #7, !dbg !1368
  call void @__AMI_fake_direct_transfer(), !dbg !1370
  %210 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %204, i8* getelementptr inbounds ([51 x i8], [51 x i8]* @.str.39, i32 0, i32 0), i32 %206, i8* %209), !dbg !1370
  %211 = load i32, i32* %6, align 4, !dbg !1372
  %212 = call i32 @close(i32 %211), !dbg !1373
  br label %213

; <label>:213:                                    ; preds = %201, %200
  br label %221, !dbg !1374

; <label>:214:                                    ; preds = %2
  %215 = call i32* @__errno_location() #1, !dbg !1375
  %216 = load i32, i32* %215, align 4, !dbg !1375
  store i32 %216, i32* %5, align 4, !dbg !1377
  %217 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1378
  %218 = call i32* @__errno_location() #1, !dbg !1378
  %219 = load i32, i32* %218, align 4, !dbg !1378
  call void @__AMI_fake_direct_transfer(), !dbg !1379
  %220 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %217, i8* getelementptr inbounds ([67 x i8], [67 x i8]* @.str.40, i32 0, i32 0), i32 %219), !dbg !1379
  br label %221

; <label>:221:                                    ; preds = %214, %213
  %222 = load i32, i32* %5, align 4, !dbg !1381
  ret i32 %222, !dbg !1382
}

; Function Attrs: nounwind
declare i32 @socket(i32, i32, i32) #2 section ".CODE_REGION_2_"

; Function Attrs: nounwind readnone
declare zeroext i16 @htons(i16 zeroext) #4 section ".CODE_REGION_2_"

declare i32 @connect(i32, %struct.sockaddr*, i32) #5 section ".CODE_REGION_2_"

; Function Attrs: nounwind
declare %struct._IO_FILE* @fdopen(i32, i8*) #2 section ".CODE_REGION_2_"

declare i32 @fprintf(%struct._IO_FILE*, i8*, ...) #5 section ".CODE_REGION_1_"

declare i8* @fgets(i8*, i32, %struct._IO_FILE*) #5 section ".CODE_REGION_2_"

; Function Attrs: nounwind readonly
declare i32 @atoi(i8*) #6 section ".CODE_REGION_1_"

declare i32 @close(i32) #5 section ".CODE_REGION_1_"

; Function Attrs: nounwind
define i8* @herror_msg(i32) #0 section ".CODE_REGION_2_" !dbg !1383 {
  %2 = alloca i32, align 4
  %3 = alloca i8*, align 4
  store i32 %0, i32* %2, align 4
  call void @llvm.dbg.declare(metadata i32* %2, metadata !1386, metadata !336), !dbg !1387
  call void @llvm.dbg.declare(metadata i8** %3, metadata !1388, metadata !336), !dbg !1389
  %4 = load i32, i32* %2, align 4, !dbg !1390
  switch i32 %4, label %8 [
    i32 1, label %5
    i32 4, label %6
    i32 2, label %7
  ], !dbg !1391

; <label>:5:                                      ; preds = %1
  store i8* getelementptr inbounds ([23 x i8], [23 x i8]* @.str.66, i32 0, i32 0), i8** %3, align 4, !dbg !1392
  br label %9, !dbg !1394

; <label>:6:                                      ; preds = %1
  store i8* getelementptr inbounds ([35 x i8], [35 x i8]* @.str.1.67, i32 0, i32 0), i8** %3, align 4, !dbg !1395
  br label %9, !dbg !1396

; <label>:7:                                      ; preds = %1
  store i8* getelementptr inbounds ([25 x i8], [25 x i8]* @.str.2.68, i32 0, i32 0), i8** %3, align 4, !dbg !1397
  br label %9, !dbg !1398

; <label>:8:                                      ; preds = %1
  store i8* getelementptr inbounds ([17 x i8], [17 x i8]* @.str.3.69, i32 0, i32 0), i8** %3, align 4, !dbg !1399
  br label %9, !dbg !1400

; <label>:9:                                      ; preds = %8, %7, %6, %5
  %10 = load i8*, i8** %3, align 4, !dbg !1401
  ret i8* %10, !dbg !1402
}

; Function Attrs: nounwind
define i8* @resp_code_msg(i32) #0 section ".CODE_REGION_2_" !dbg !1403 {
  %2 = alloca i32, align 4
  %3 = alloca i8*, align 4
  store i32 %0, i32* %2, align 4
  call void @llvm.dbg.declare(metadata i32* %2, metadata !1407, metadata !336), !dbg !1408
  call void @llvm.dbg.declare(metadata i8** %3, metadata !1409, metadata !336), !dbg !1410
  %4 = load i32, i32* %2, align 4, !dbg !1411
  switch i32 %4, label %10 [
    i32 1, label %5
    i32 2, label %6
    i32 3, label %7
    i32 4, label %8
    i32 5, label %9
  ], !dbg !1412

; <label>:5:                                      ; preds = %1
  store i8* getelementptr inbounds ([17 x i8], [17 x i8]* @.str.4.70, i32 0, i32 0), i8** %3, align 4, !dbg !1413
  br label %11, !dbg !1415

; <label>:6:                                      ; preds = %1
  store i8* getelementptr inbounds ([18 x i8], [18 x i8]* @.str.5.71, i32 0, i32 0), i8** %3, align 4, !dbg !1416
  br label %11, !dbg !1417

; <label>:7:                                      ; preds = %1
  store i8* getelementptr inbounds ([18 x i8], [18 x i8]* @.str.6.72, i32 0, i32 0), i8** %3, align 4, !dbg !1418
  br label %11, !dbg !1419

; <label>:8:                                      ; preds = %1
  store i8* getelementptr inbounds ([16 x i8], [16 x i8]* @.str.7.73, i32 0, i32 0), i8** %3, align 4, !dbg !1420
  br label %11, !dbg !1421

; <label>:9:                                      ; preds = %1
  store i8* getelementptr inbounds ([17 x i8], [17 x i8]* @.str.8.74, i32 0, i32 0), i8** %3, align 4, !dbg !1422
  br label %11, !dbg !1423

; <label>:10:                                     ; preds = %1
  store i8* getelementptr inbounds ([23 x i8], [23 x i8]* @.str.9.75, i32 0, i32 0), i8** %3, align 4, !dbg !1424
  br label %11, !dbg !1425

; <label>:11:                                     ; preds = %10, %9, %8, %7, %6, %5
  %12 = load i8*, i8** %3, align 4, !dbg !1426
  ret i8* %12, !dbg !1427
}

; Function Attrs: nounwind
define i32 @hostname_to_ip(i8*, %struct.in_addr*) #0 section ".CODE_REGION_1_" !dbg !1428 {
  %3 = alloca i8*, align 4
  %4 = alloca %struct.in_addr*, align 4
  %5 = alloca i32, align 4
  %6 = alloca %struct.addrinfo, align 4
  %7 = alloca %struct.addrinfo*, align 4
  %8 = alloca i32, align 4
  %9 = alloca %struct.addrinfo*, align 4
  %10 = alloca %struct.sockaddr_in*, align 4
  store i8* %0, i8** %3, align 4
  call void @llvm.dbg.declare(metadata i8** %3, metadata !1431, metadata !336), !dbg !1432
  store %struct.in_addr* %1, %struct.in_addr** %4, align 4
  call void @llvm.dbg.declare(metadata %struct.in_addr** %4, metadata !1433, metadata !336), !dbg !1434
  call void @llvm.dbg.declare(metadata i32* %5, metadata !1435, metadata !336), !dbg !1436
  call void @llvm.dbg.declare(metadata %struct.addrinfo* %6, metadata !1437, metadata !336), !dbg !1457
  call void @llvm.dbg.declare(metadata %struct.addrinfo** %7, metadata !1458, metadata !336), !dbg !1459
  call void @llvm.dbg.declare(metadata i32* %8, metadata !1460, metadata !336), !dbg !1461
  %11 = bitcast %struct.addrinfo* %6 to i8*, !dbg !1462
  call void @llvm.memset.p0i8.i32(i8* %11, i8 0, i32 32, i32 4, i1 false), !dbg !1462
  %12 = getelementptr inbounds %struct.addrinfo, %struct.addrinfo* %6, i32 0, i32 1, !dbg !1463
  store i32 2, i32* %12, align 4, !dbg !1464
  %13 = getelementptr inbounds %struct.addrinfo, %struct.addrinfo* %6, i32 0, i32 2, !dbg !1465
  store i32 0, i32* %13, align 4, !dbg !1466
  %14 = load i8*, i8** %3, align 4, !dbg !1467
  %15 = call i32 @getaddrinfo(i8* %14, i8* null, %struct.addrinfo* %6, %struct.addrinfo** %7), !dbg !1468
  store i32 %15, i32* %8, align 4, !dbg !1469
  %16 = load i32, i32* %8, align 4, !dbg !1470
  %17 = icmp eq i32 %16, 0, !dbg !1472
  br i1 %17, label %18, label %45, !dbg !1473

; <label>:18:                                     ; preds = %2
  call void @llvm.dbg.declare(metadata %struct.addrinfo** %9, metadata !1474, metadata !336), !dbg !1476
  store i32 -1, i32* %5, align 4, !dbg !1477
  %19 = load %struct.addrinfo*, %struct.addrinfo** %7, align 4, !dbg !1478
  store %struct.addrinfo* %19, %struct.addrinfo** %9, align 4, !dbg !1480
  br label %20, !dbg !1481

; <label>:20:                                     ; preds = %39, %18
  %21 = load %struct.addrinfo*, %struct.addrinfo** %9, align 4, !dbg !1482
  %22 = icmp ne %struct.addrinfo* %21, null, !dbg !1485
  br i1 %22, label %23, label %43, !dbg !1486

; <label>:23:                                     ; preds = %20
  call void @llvm.dbg.declare(metadata %struct.sockaddr_in** %10, metadata !1487, metadata !336), !dbg !1489
  %24 = load %struct.addrinfo*, %struct.addrinfo** %9, align 4, !dbg !1490
  %25 = getelementptr inbounds %struct.addrinfo, %struct.addrinfo* %24, i32 0, i32 5, !dbg !1491
  %26 = load %struct.sockaddr*, %struct.sockaddr** %25, align 4, !dbg !1491
  %27 = bitcast %struct.sockaddr* %26 to %struct.sockaddr_in*, !dbg !1492
  store %struct.sockaddr_in* %27, %struct.sockaddr_in** %10, align 4, !dbg !1493
  %28 = load %struct.in_addr*, %struct.in_addr** %4, align 4, !dbg !1494
  %29 = load %struct.sockaddr_in*, %struct.sockaddr_in** %10, align 4, !dbg !1495
  %30 = getelementptr inbounds %struct.sockaddr_in, %struct.sockaddr_in* %29, i32 0, i32 2, !dbg !1496
  %31 = bitcast %struct.in_addr* %28 to i8*, !dbg !1496
  %32 = bitcast %struct.in_addr* %30 to i8*, !dbg !1496
  call void @llvm.memcpy.p0i8.p0i8.i32(i8* %31, i8* %32, i32 4, i32 4, i1 false), !dbg !1496
  %33 = load %struct.in_addr*, %struct.in_addr** %4, align 4, !dbg !1497
  %34 = getelementptr inbounds %struct.in_addr, %struct.in_addr* %33, i32 0, i32 0, !dbg !1499
  %35 = load i32, i32* %34, align 4, !dbg !1499
  %36 = icmp ne i32 %35, 0, !dbg !1500
  br i1 %36, label %37, label %38, !dbg !1501

; <label>:37:                                     ; preds = %23
  store i32 0, i32* %5, align 4, !dbg !1502
  br label %43, !dbg !1504

; <label>:38:                                     ; preds = %23
  br label %39, !dbg !1505

; <label>:39:                                     ; preds = %38
  %40 = load %struct.addrinfo*, %struct.addrinfo** %9, align 4, !dbg !1506
  %41 = getelementptr inbounds %struct.addrinfo, %struct.addrinfo* %40, i32 0, i32 7, !dbg !1508
  %42 = load %struct.addrinfo*, %struct.addrinfo** %41, align 4, !dbg !1508
  store %struct.addrinfo* %42, %struct.addrinfo** %9, align 4, !dbg !1509
  br label %20, !dbg !1510, !llvm.loop !1511

; <label>:43:                                     ; preds = %37, %20
  %44 = load %struct.addrinfo*, %struct.addrinfo** %7, align 4, !dbg !1513
  call void @freeaddrinfo(%struct.addrinfo* %44) #7, !dbg !1514
  br label %52, !dbg !1515

; <label>:45:                                     ; preds = %2
  %46 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1516
  %47 = load i8*, i8** %3, align 4, !dbg !1516
  %48 = load i32, i32* %8, align 4, !dbg !1516
  %49 = call i8* @gai_strerror(i32 %48) #7, !dbg !1516
  %50 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %46, i8* getelementptr inbounds ([46 x i8], [46 x i8]* @.str.10.78, i32 0, i32 0), i8* %47, i8* %49), !dbg !1518
  %51 = load i32, i32* %8, align 4, !dbg !1520
  store i32 %51, i32* %5, align 4, !dbg !1521
  br label %52

; <label>:52:                                     ; preds = %45, %43
  %53 = load i32, i32* %5, align 4, !dbg !1522
  call void @__AMI_fake_rt_transfer(), !dbg !1523
  ret i32 %53, !dbg !1523
}

declare i32 @getaddrinfo(i8*, i8*, %struct.addrinfo*, %struct.addrinfo**) #5 section ".CODE_REGION_1_"

; Function Attrs: nounwind
declare void @freeaddrinfo(%struct.addrinfo*) #2 section ".CODE_REGION_1_"

; Function Attrs: nounwind
declare i8* @gai_strerror(i32) #2 section ".CODE_REGION_1_"

; Function Attrs: nounwind
define i32 @hostname_to_ip_at_dns(i8*, i8*, %struct.in_addr*) #0 section ".CODE_REGION_2_" !dbg !1524 {
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
  call void @llvm.dbg.declare(metadata i8** %4, metadata !1527, metadata !336), !dbg !1528
  store i8* %1, i8** %5, align 4
  call void @llvm.dbg.declare(metadata i8** %5, metadata !1529, metadata !336), !dbg !1530
  store %struct.in_addr* %2, %struct.in_addr** %6, align 4
  call void @llvm.dbg.declare(metadata %struct.in_addr** %6, metadata !1531, metadata !336), !dbg !1532
  call void @llvm.dbg.declare(metadata i32* %7, metadata !1533, metadata !336), !dbg !1534
  call void @llvm.dbg.declare(metadata %struct.__res_state* %8, metadata !1535, metadata !336), !dbg !1641
  %23 = bitcast %struct.__res_state* %8 to i8*, !dbg !1642
  call void @llvm.memset.p0i8.i32(i8* %23, i8 0, i32 512, i32 4, i1 false), !dbg !1642
  %24 = call i32 @__res_ninit(%struct.__res_state* %8) #7, !dbg !1643
  store i32 %24, i32* %7, align 4, !dbg !1644
  %25 = load i32, i32* %7, align 4, !dbg !1645
  %26 = icmp eq i32 %25, 0, !dbg !1647
  br i1 %26, label %27, label %209, !dbg !1648

; <label>:27:                                     ; preds = %3
  call void @llvm.dbg.declare(metadata %struct.in_addr* %9, metadata !1649, metadata !336), !dbg !1651
  %28 = load i8*, i8** %4, align 4, !dbg !1652
  call void @__AMI_fake_direct_transfer(), !dbg !1653
  %29 = call i32 @hostname_to_ip(i8* %28, %struct.in_addr* %9), !dbg !1653
  store i32 %29, i32* %7, align 4, !dbg !1654
  %30 = load i32, i32* %7, align 4, !dbg !1655
  %31 = icmp eq i32 %30, 0, !dbg !1657
  br i1 %31, label %32, label %208, !dbg !1658

; <label>:32:                                     ; preds = %27
  call void @llvm.dbg.declare(metadata %union.anon.2* %10, metadata !1659, metadata !336), !dbg !1687
  call void @llvm.dbg.declare(metadata i32* %11, metadata !1688, metadata !336), !dbg !1689
  call void @llvm.dbg.declare(metadata [3 x %struct.in_addr]* %12, metadata !1690, metadata !336), !dbg !1692
  call void @llvm.dbg.declare(metadata i32* %13, metadata !1693, metadata !336), !dbg !1694
  call void @llvm.dbg.declare(metadata i32* %14, metadata !1695, metadata !336), !dbg !1696
  call void @llvm.dbg.declare(metadata i32* %15, metadata !1697, metadata !336), !dbg !1698
  %33 = getelementptr inbounds %struct.__res_state, %struct.__res_state* %8, i32 0, i32 3, !dbg !1699
  %34 = load i32, i32* %33, align 4, !dbg !1699
  store i32 %34, i32* %13, align 4, !dbg !1700
  store i32 0, i32* %15, align 4, !dbg !1701
  br label %35, !dbg !1703

; <label>:35:                                     ; preds = %48, %32
  %36 = load i32, i32* %15, align 4, !dbg !1704
  %37 = load i32, i32* %13, align 4, !dbg !1707
  %38 = icmp slt i32 %36, %37, !dbg !1708
  br i1 %38, label %39, label %51, !dbg !1709

; <label>:39:                                     ; preds = %35
  %40 = load i32, i32* %15, align 4, !dbg !1710
  %41 = getelementptr inbounds [3 x %struct.in_addr], [3 x %struct.in_addr]* %12, i32 0, i32 %40, !dbg !1711
  %42 = load i32, i32* %15, align 4, !dbg !1712
  %43 = getelementptr inbounds %struct.__res_state, %struct.__res_state* %8, i32 0, i32 4, !dbg !1713
  %44 = getelementptr inbounds [3 x %struct.sockaddr_in], [3 x %struct.sockaddr_in]* %43, i32 0, i32 %42, !dbg !1714
  %45 = getelementptr inbounds %struct.sockaddr_in, %struct.sockaddr_in* %44, i32 0, i32 2, !dbg !1715
  %46 = bitcast %struct.in_addr* %41 to i8*, !dbg !1715
  %47 = bitcast %struct.in_addr* %45 to i8*, !dbg !1715
  call void @llvm.memcpy.p0i8.p0i8.i32(i8* %46, i8* %47, i32 4, i32 4, i1 false), !dbg !1715
  br label %48, !dbg !1711

; <label>:48:                                     ; preds = %39
  %49 = load i32, i32* %15, align 4, !dbg !1716
  %50 = add nsw i32 %49, 1, !dbg !1716
  store i32 %50, i32* %15, align 4, !dbg !1716
  br label %35, !dbg !1718, !llvm.loop !1719

; <label>:51:                                     ; preds = %35
  %52 = getelementptr inbounds %struct.__res_state, %struct.__res_state* %8, i32 0, i32 2, !dbg !1721
  %53 = load i32, i32* %52, align 4, !dbg !1721
  store i32 %53, i32* %14, align 4, !dbg !1722
  %54 = getelementptr inbounds %struct.__res_state, %struct.__res_state* %8, i32 0, i32 2, !dbg !1723
  %55 = load i32, i32* %54, align 4, !dbg !1724
  %56 = and i32 %55, -129, !dbg !1724
  store i32 %56, i32* %54, align 4, !dbg !1724
  %57 = getelementptr inbounds %struct.__res_state, %struct.__res_state* %8, i32 0, i32 4, !dbg !1725
  %58 = getelementptr inbounds [3 x %struct.sockaddr_in], [3 x %struct.sockaddr_in]* %57, i32 0, i32 0, !dbg !1726
  %59 = getelementptr inbounds %struct.sockaddr_in, %struct.sockaddr_in* %58, i32 0, i32 2, !dbg !1727
  %60 = bitcast %struct.in_addr* %59 to i8*, !dbg !1728
  %61 = bitcast %struct.in_addr* %9 to i8*, !dbg !1728
  call void @llvm.memcpy.p0i8.p0i8.i32(i8* %60, i8* %61, i32 4, i32 4, i1 false), !dbg !1728
  %62 = getelementptr inbounds %struct.__res_state, %struct.__res_state* %8, i32 0, i32 3, !dbg !1729
  store i32 1, i32* %62, align 4, !dbg !1730
  %63 = load i8*, i8** %5, align 4, !dbg !1731
  %64 = bitcast %union.anon.2* %10 to i8*, !dbg !1732
  %65 = call i32 @__res_nquery(%struct.__res_state* %8, i8* %63, i32 1, i32 1, i8* %64, i32 512) #7, !dbg !1733
  store i32 %65, i32* %11, align 4, !dbg !1734
  %66 = load i32, i32* %11, align 4, !dbg !1735
  %67 = icmp ne i32 %66, -1, !dbg !1737
  br i1 %67, label %68, label %162, !dbg !1738

; <label>:68:                                     ; preds = %51
  call void @llvm.dbg.declare(metadata %struct.__ns_msg* %16, metadata !1739, metadata !336), !dbg !1756
  %69 = bitcast %union.anon.2* %10 to [512 x i8]*, !dbg !1757
  %70 = getelementptr inbounds [512 x i8], [512 x i8]* %69, i32 0, i32 0, !dbg !1758
  %71 = load i32, i32* %11, align 4, !dbg !1759
  %72 = call i32 @ns_initparse(i8* %70, i32 %71, %struct.__ns_msg* %16) #7, !dbg !1760
  store i32 %72, i32* %7, align 4, !dbg !1761
  %73 = load i32, i32* %7, align 4, !dbg !1762
  %74 = icmp sge i32 %73, 0, !dbg !1764
  br i1 %74, label %75, label %155, !dbg !1765

; <label>:75:                                     ; preds = %68
  call void @llvm.dbg.declare(metadata i32* %17, metadata !1766, metadata !336), !dbg !1768
  %76 = bitcast %struct.__ns_msg* %16 to [12 x i32]*, !dbg !1769
  %77 = load [12 x i32], [12 x i32]* %76, align 4, !dbg !1769
  %78 = call i32 @ns_msg_getflag([12 x i32] %77, i32 9) #7, !dbg !1769
  store i32 %78, i32* %17, align 4, !dbg !1770
  %79 = load i32, i32* %17, align 4, !dbg !1771
  %80 = icmp eq i32 %79, 0, !dbg !1773
  br i1 %80, label %81, label %145, !dbg !1774

; <label>:81:                                     ; preds = %75
  call void @llvm.dbg.declare(metadata i16* %18, metadata !1775, metadata !336), !dbg !1777
  %82 = getelementptr inbounds %struct.__ns_msg, %struct.__ns_msg* %16, i32 0, i32 4, !dbg !1778
  %83 = getelementptr inbounds [4 x i16], [4 x i16]* %82, i32 0, i32 1, !dbg !1778
  %84 = load i16, i16* %83, align 2, !dbg !1778
  %85 = zext i16 %84 to i32, !dbg !1778
  %86 = add nsw i32 %85, 0, !dbg !1778
  %87 = trunc i32 %86 to i16, !dbg !1778
  store i16 %87, i16* %18, align 2, !dbg !1779
  %88 = load i16, i16* %18, align 2, !dbg !1780
  %89 = zext i16 %88 to i32, !dbg !1780
  %90 = icmp eq i32 %89, 1, !dbg !1782
  br i1 %90, label %91, label %135, !dbg !1783

; <label>:91:                                     ; preds = %81
  call void @llvm.dbg.declare(metadata %struct.__ns_rr* %19, metadata !1784, metadata !336), !dbg !1798
  %92 = call i32 @ns_parserr(%struct.__ns_msg* %16, i32 1, i32 0, %struct.__ns_rr* %19) #7, !dbg !1799
  store i32 %92, i32* %7, align 4, !dbg !1800
  %93 = load i32, i32* %7, align 4, !dbg !1801
  %94 = icmp eq i32 %93, 0, !dbg !1803
  br i1 %94, label %95, label %128, !dbg !1804

; <label>:95:                                     ; preds = %91
  call void @llvm.dbg.declare(metadata i16* %20, metadata !1805, metadata !336), !dbg !1807
  %96 = getelementptr inbounds %struct.__ns_rr, %struct.__ns_rr* %19, i32 0, i32 1, !dbg !1808
  %97 = load i16, i16* %96, align 2, !dbg !1808
  %98 = zext i16 %97 to i32, !dbg !1808
  %99 = add nsw i32 %98, 0, !dbg !1808
  %100 = trunc i32 %99 to i16, !dbg !1808
  store i16 %100, i16* %20, align 2, !dbg !1809
  %101 = load i16, i16* %20, align 2, !dbg !1810
  %102 = zext i16 %101 to i32, !dbg !1810
  %103 = icmp eq i32 %102, 1, !dbg !1812
  br i1 %103, label %104, label %118, !dbg !1813

; <label>:104:                                    ; preds = %95
  call void @llvm.dbg.declare(metadata i8** %21, metadata !1814, metadata !336), !dbg !1816
  call void @llvm.dbg.declare(metadata [256 x i8]* %22, metadata !1817, metadata !336), !dbg !1818
  %105 = getelementptr inbounds [256 x i8], [256 x i8]* %22, i32 0, i32 0, !dbg !1819
  %106 = call i32 @ns_sprintrr(%struct.__ns_msg* %16, %struct.__ns_rr* %19, i8* null, i8* null, i8* %105, i32 256) #7, !dbg !1820
  %107 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1821
  %108 = getelementptr inbounds [256 x i8], [256 x i8]* %22, i32 0, i32 0, !dbg !1821
  call void @__AMI_fake_direct_transfer(), !dbg !1821
  %109 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %107, i8* getelementptr inbounds ([6 x i8], [6 x i8]* @.str.11.79, i32 0, i32 0), i8* %108), !dbg !1821
  %110 = getelementptr inbounds %struct.__ns_rr, %struct.__ns_rr* %19, i32 0, i32 5, !dbg !1822
  %111 = load i8*, i8** %110, align 4, !dbg !1822
  %112 = getelementptr inbounds i8, i8* %111, i32 0, !dbg !1822
  store i8* %112, i8** %21, align 4, !dbg !1823
  %113 = load %struct.in_addr*, %struct.in_addr** %6, align 4, !dbg !1824
  %114 = load i8*, i8** %21, align 4, !dbg !1825
  %115 = bitcast i8* %114 to %struct.in_addr*, !dbg !1826
  %116 = bitcast %struct.in_addr* %113 to i8*, !dbg !1826
  %117 = bitcast %struct.in_addr* %115 to i8*, !dbg !1826
  call void @llvm.memcpy.p0i8.p0i8.i32(i8* %116, i8* %117, i32 4, i32 4, i1 false), !dbg !1826
  store i32 0, i32* %7, align 4, !dbg !1827
  br label %127, !dbg !1828

; <label>:118:                                    ; preds = %95
  %119 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1829
  %120 = getelementptr inbounds %struct.in_addr, %struct.in_addr* %9, i32 0, i32 0, !dbg !1829
  %121 = bitcast i32* %120 to [1 x i32]*, !dbg !1829
  %122 = load [1 x i32], [1 x i32]* %121, align 4, !dbg !1829
  %123 = call i8* @inet_ntoa([1 x i32] %122) #7, !dbg !1829
  %124 = load i16, i16* %20, align 2, !dbg !1829
  %125 = zext i16 %124 to i32, !dbg !1829
  call void @__AMI_fake_direct_transfer(), !dbg !1831
  %126 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %119, i8* getelementptr inbounds ([37 x i8], [37 x i8]* @.str.12.80, i32 0, i32 0), i8* %123, i32 1, i32 %125), !dbg !1831
  store i32 -2, i32* %7, align 4, !dbg !1833
  br label %127

; <label>:127:                                    ; preds = %118, %104
  br label %134, !dbg !1834

; <label>:128:                                    ; preds = %91
  %129 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1835
  %130 = call i32* @__errno_location() #1, !dbg !1835
  %131 = load i32, i32* %130, align 4, !dbg !1835
  %132 = call i8* @strerror(i32 %131) #7, !dbg !1837
  call void @__AMI_fake_direct_transfer(), !dbg !1839
  %133 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %129, i8* getelementptr inbounds ([16 x i8], [16 x i8]* @.str.13.81, i32 0, i32 0), i8* %132), !dbg !1839
  br label %134

; <label>:134:                                    ; preds = %128, %127
  br label %144, !dbg !1841

; <label>:135:                                    ; preds = %81
  %136 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1842
  %137 = getelementptr inbounds %struct.in_addr, %struct.in_addr* %9, i32 0, i32 0, !dbg !1842
  %138 = bitcast i32* %137 to [1 x i32]*, !dbg !1842
  %139 = load [1 x i32], [1 x i32]* %138, align 4, !dbg !1842
  %140 = call i8* @inet_ntoa([1 x i32] %139) #7, !dbg !1842
  %141 = load i16, i16* %18, align 2, !dbg !1842
  %142 = zext i16 %141 to i32, !dbg !1842
  call void @__AMI_fake_direct_transfer(), !dbg !1844
  %143 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %136, i8* getelementptr inbounds ([31 x i8], [31 x i8]* @.str.14.82, i32 0, i32 0), i8* %140, i32 %142), !dbg !1844
  store i32 -1, i32* %7, align 4, !dbg !1846
  br label %144

; <label>:144:                                    ; preds = %135, %134
  br label %154, !dbg !1847

; <label>:145:                                    ; preds = %75
  %146 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1848
  %147 = getelementptr inbounds %struct.in_addr, %struct.in_addr* %9, i32 0, i32 0, !dbg !1848
  %148 = bitcast i32* %147 to [1 x i32]*, !dbg !1848
  %149 = load [1 x i32], [1 x i32]* %148, align 4, !dbg !1848
  %150 = call i8* @inet_ntoa([1 x i32] %149) #7, !dbg !1848
  %151 = load i32, i32* %17, align 4, !dbg !1848
  %152 = call i8* @resp_code_msg(i32 %151), !dbg !1850
  call void @__AMI_fake_direct_transfer(), !dbg !1852
  %153 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %146, i8* getelementptr inbounds ([49 x i8], [49 x i8]* @.str.15.83, i32 0, i32 0), i8* %150, i8* %152), !dbg !1852
  store i32 -4, i32* %7, align 4, !dbg !1854
  br label %154

; <label>:154:                                    ; preds = %145, %144
  br label %161, !dbg !1855

; <label>:155:                                    ; preds = %68
  %156 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1856
  %157 = call i32* @__errno_location() #1, !dbg !1856
  %158 = load i32, i32* %157, align 4, !dbg !1856
  %159 = call i8* @strerror(i32 %158) #7, !dbg !1858
  call void @__AMI_fake_direct_transfer(), !dbg !1860
  %160 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %156, i8* getelementptr inbounds ([18 x i8], [18 x i8]* @.str.16.84, i32 0, i32 0), i8* %159), !dbg !1860
  br label %161

; <label>:161:                                    ; preds = %155, %154
  br label %186, !dbg !1862

; <label>:162:                                    ; preds = %51
  %163 = call i32* @__errno_location() #1, !dbg !1863
  %164 = load i32, i32* %163, align 4, !dbg !1863
  %165 = icmp eq i32 %164, 111, !dbg !1866
  br i1 %165, label %166, label %173, !dbg !1867

; <label>:166:                                    ; preds = %162
  %167 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1868
  %168 = getelementptr inbounds %struct.in_addr, %struct.in_addr* %9, i32 0, i32 0, !dbg !1868
  %169 = bitcast i32* %168 to [1 x i32]*, !dbg !1868
  %170 = load [1 x i32], [1 x i32]* %169, align 4, !dbg !1868
  %171 = call i8* @inet_ntoa([1 x i32] %170) #7, !dbg !1868
  call void @__AMI_fake_direct_transfer(), !dbg !1869
  %172 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %167, i8* getelementptr inbounds ([59 x i8], [59 x i8]* @.str.17.85, i32 0, i32 0), i8* %171), !dbg !1869
  br label %185, !dbg !1868

; <label>:173:                                    ; preds = %162
  %174 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1871
  %175 = getelementptr inbounds %struct.in_addr, %struct.in_addr* %9, i32 0, i32 0, !dbg !1871
  %176 = bitcast i32* %175 to [1 x i32]*, !dbg !1871
  %177 = load [1 x i32], [1 x i32]* %176, align 4, !dbg !1871
  %178 = call i8* @inet_ntoa([1 x i32] %177) #7, !dbg !1871
  %179 = call i32* @__h_errno_location() #1, !dbg !1872
  %180 = load i32, i32* %179, align 4, !dbg !1871
  %181 = call i32* @__h_errno_location() #1, !dbg !1873
  %182 = load i32, i32* %181, align 4, !dbg !1871
  %183 = call i8* @herror_msg(i32 %182), !dbg !1875
  call void @__AMI_fake_direct_transfer(), !dbg !1877
  %184 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %174, i8* getelementptr inbounds ([49 x i8], [49 x i8]* @.str.18.86, i32 0, i32 0), i8* %178, i32 %180, i8* %183), !dbg !1877
  br label %185

; <label>:185:                                    ; preds = %173, %166
  store i32 -3, i32* %7, align 4, !dbg !1879
  br label %186

; <label>:186:                                    ; preds = %185, %161
  %187 = load i32, i32* %14, align 4, !dbg !1880
  %188 = getelementptr inbounds %struct.__res_state, %struct.__res_state* %8, i32 0, i32 2, !dbg !1881
  store i32 %187, i32* %188, align 4, !dbg !1882
  %189 = load i32, i32* %13, align 4, !dbg !1883
  %190 = getelementptr inbounds %struct.__res_state, %struct.__res_state* %8, i32 0, i32 3, !dbg !1884
  store i32 %189, i32* %190, align 4, !dbg !1885
  store i32 0, i32* %15, align 4, !dbg !1886
  br label %191, !dbg !1888

; <label>:191:                                    ; preds = %204, %186
  %192 = load i32, i32* %15, align 4, !dbg !1889
  %193 = load i32, i32* %13, align 4, !dbg !1892
  %194 = icmp slt i32 %192, %193, !dbg !1893
  br i1 %194, label %195, label %207, !dbg !1894

; <label>:195:                                    ; preds = %191
  %196 = load i32, i32* %15, align 4, !dbg !1895
  %197 = getelementptr inbounds %struct.__res_state, %struct.__res_state* %8, i32 0, i32 4, !dbg !1896
  %198 = getelementptr inbounds [3 x %struct.sockaddr_in], [3 x %struct.sockaddr_in]* %197, i32 0, i32 %196, !dbg !1897
  %199 = getelementptr inbounds %struct.sockaddr_in, %struct.sockaddr_in* %198, i32 0, i32 2, !dbg !1898
  %200 = load i32, i32* %15, align 4, !dbg !1899
  %201 = getelementptr inbounds [3 x %struct.in_addr], [3 x %struct.in_addr]* %12, i32 0, i32 %200, !dbg !1900
  %202 = bitcast %struct.in_addr* %199 to i8*, !dbg !1900
  %203 = bitcast %struct.in_addr* %201 to i8*, !dbg !1900
  call void @llvm.memcpy.p0i8.p0i8.i32(i8* %202, i8* %203, i32 4, i32 4, i1 false), !dbg !1900
  br label %204, !dbg !1897

; <label>:204:                                    ; preds = %195
  %205 = load i32, i32* %15, align 4, !dbg !1901
  %206 = add nsw i32 %205, 1, !dbg !1901
  store i32 %206, i32* %15, align 4, !dbg !1901
  br label %191, !dbg !1903, !llvm.loop !1904

; <label>:207:                                    ; preds = %191
  br label %208, !dbg !1906

; <label>:208:                                    ; preds = %207, %27
  br label %214, !dbg !1907

; <label>:209:                                    ; preds = %3
  %210 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !1908
  %211 = call i32* @__errno_location() #1, !dbg !1908
  %212 = load i32, i32* %211, align 4, !dbg !1908
  call void @__AMI_fake_direct_transfer(), !dbg !1910
  %213 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %210, i8* getelementptr inbounds ([26 x i8], [26 x i8]* @.str.19.87, i32 0, i32 0), i32 %212), !dbg !1910
  br label %214

; <label>:214:                                    ; preds = %209, %208
  %215 = load i32, i32* %7, align 4, !dbg !1912
  ret i32 %215, !dbg !1913
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
define i32 @get_public_ip(i8*) #0 section ".CODE_REGION_2_" !dbg !1914 {
  %2 = alloca i8*, align 4
  %3 = alloca i32, align 4
  %4 = alloca %struct.in_addr, align 4
  store i8* %0, i8** %2, align 4
  call void @llvm.dbg.declare(metadata i8** %2, metadata !1915, metadata !336), !dbg !1916
  call void @llvm.dbg.declare(metadata i32* %3, metadata !1917, metadata !336), !dbg !1918
  call void @llvm.dbg.declare(metadata %struct.in_addr* %4, metadata !1919, metadata !336), !dbg !1920
  %5 = call i32 @hostname_to_ip_at_dns(i8* getelementptr inbounds ([22 x i8], [22 x i8]* @.str.20.90, i32 0, i32 0), i8* getelementptr inbounds ([17 x i8], [17 x i8]* @.str.21.91, i32 0, i32 0), %struct.in_addr* %4), !dbg !1921
  store i32 %5, i32* %3, align 4, !dbg !1922
  %6 = load i32, i32* %3, align 4, !dbg !1923
  %7 = icmp eq i32 %6, 0, !dbg !1925
  br i1 %7, label %8, label %15, !dbg !1926

; <label>:8:                                      ; preds = %1
  %9 = load i8*, i8** %2, align 4, !dbg !1927
  %10 = getelementptr inbounds %struct.in_addr, %struct.in_addr* %4, i32 0, i32 0, !dbg !1928
  %11 = bitcast i32* %10 to [1 x i32]*, !dbg !1928
  %12 = load [1 x i32], [1 x i32]* %11, align 4, !dbg !1928
  %13 = call i8* @inet_ntoa([1 x i32] %12) #7, !dbg !1928
  %14 = call i8* @strcpy(i8* %9, i8* %13) #7, !dbg !1929
  br label %15, !dbg !1931

; <label>:15:                                     ; preds = %8, %1
  %16 = load i32, i32* %3, align 4, !dbg !1932
  ret i32 %16, !dbg !1933
}

; Function Attrs: nounwind
define i32 @get_current_exec_path(i8*, i32) #0 section ".CODE_REGION_1_" !dbg !1934 {
  %3 = alloca i8*, align 4
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  %6 = alloca [4097 x i8], align 1
  %7 = alloca i32, align 4
  %8 = alloca i8*, align 4
  store i8* %0, i8** %3, align 4
  call void @llvm.dbg.declare(metadata i8** %3, metadata !1937, metadata !336), !dbg !1938
  store i32 %1, i32* %4, align 4
  call void @llvm.dbg.declare(metadata i32* %4, metadata !1939, metadata !336), !dbg !1940
  call void @llvm.dbg.declare(metadata i32* %5, metadata !1941, metadata !336), !dbg !1942
  %9 = load i32, i32* %4, align 4, !dbg !1943
  %10 = icmp ugt i32 %9, 0, !dbg !1945
  br i1 %10, label %11, label %42, !dbg !1946

; <label>:11:                                     ; preds = %2
  call void @llvm.dbg.declare(metadata [4097 x i8]* %6, metadata !1947, metadata !336), !dbg !1949
  call void @llvm.dbg.declare(metadata i32* %7, metadata !1950, metadata !336), !dbg !1951
  %12 = getelementptr inbounds [4097 x i8], [4097 x i8]* %6, i32 0, i32 0, !dbg !1952
  %13 = call i32 @readlink(i8* getelementptr inbounds ([15 x i8], [15 x i8]* @.str.94, i32 0, i32 0), i8* %12, i32 4096) #7, !dbg !1953
  store i32 %13, i32* %7, align 4, !dbg !1954
  %14 = load i32, i32* %7, align 4, !dbg !1955
  %15 = icmp ne i32 %14, -1, !dbg !1957
  br i1 %15, label %16, label %36, !dbg !1958

; <label>:16:                                     ; preds = %11
  call void @llvm.dbg.declare(metadata i8** %8, metadata !1959, metadata !336), !dbg !1961
  %17 = load i32, i32* %7, align 4, !dbg !1962
  %18 = getelementptr inbounds [4097 x i8], [4097 x i8]* %6, i32 0, i32 %17, !dbg !1963
  store i8 0, i8* %18, align 1, !dbg !1964
  %19 = getelementptr inbounds [4097 x i8], [4097 x i8]* %6, i32 0, i32 0, !dbg !1965
  %20 = call i8* @dirname(i8* %19) #7, !dbg !1966
  store i8* %20, i8** %8, align 4, !dbg !1967
  %21 = load i32, i32* %4, align 4, !dbg !1968
  %22 = load i8*, i8** %8, align 4, !dbg !1970
  %23 = call i32 @strlen(i8* %22) #9, !dbg !1971
  %24 = add i32 %23, 1, !dbg !1972
  %25 = icmp ugt i32 %21, %24, !dbg !1973
  br i1 %25, label %26, label %32, !dbg !1974

; <label>:26:                                     ; preds = %16
  %27 = load i8*, i8** %3, align 4, !dbg !1975
  %28 = load i8*, i8** %8, align 4, !dbg !1977
  %29 = call i8* @strcpy(i8* %27, i8* %28) #7, !dbg !1978
  %30 = load i8*, i8** %3, align 4, !dbg !1979
  %31 = call i8* @strcat(i8* %30, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.1.95, i32 0, i32 0)) #7, !dbg !1980
  store i32 0, i32* %5, align 4, !dbg !1981
  br label %35, !dbg !1982

; <label>:32:                                     ; preds = %16
  %33 = load i8*, i8** %3, align 4, !dbg !1983
  %34 = getelementptr inbounds i8, i8* %33, i32 0, !dbg !1983
  store i8 0, i8* %34, align 1, !dbg !1985
  store i32 22, i32* %5, align 4, !dbg !1986
  br label %35

; <label>:35:                                     ; preds = %32, %26
  br label %41, !dbg !1987

; <label>:36:                                     ; preds = %11
  %37 = load i8*, i8** %3, align 4, !dbg !1988
  %38 = getelementptr inbounds i8, i8* %37, i32 0, !dbg !1988
  store i8 0, i8* %38, align 1, !dbg !1990
  %39 = call i32* @__errno_location() #1, !dbg !1991
  %40 = load i32, i32* %39, align 4, !dbg !1991
  store i32 %40, i32* %5, align 4, !dbg !1992
  br label %41

; <label>:41:                                     ; preds = %36, %35
  br label %43, !dbg !1993

; <label>:42:                                     ; preds = %2
  store i32 22, i32* %5, align 4, !dbg !1994
  br label %43

; <label>:43:                                     ; preds = %42, %41
  %44 = load i32, i32* %5, align 4, !dbg !1995
  ret i32 %44, !dbg !1996
}

; Function Attrs: nounwind
declare i32 @readlink(i8*, i8*, i32) #2 section ".CODE_REGION_1_"

; Function Attrs: nounwind
declare i8* @dirname(i8*) #2 section ".CODE_REGION_1_"

; Function Attrs: nounwind
define void @kill_processes(i32*, i32) #0 section ".CODE_REGION_2_" !dbg !1997 {
  %3 = alloca i32*, align 4
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  store i32* %0, i32** %3, align 4
  call void @llvm.dbg.declare(metadata i32** %3, metadata !2001, metadata !336), !dbg !2002
  store i32 %1, i32* %4, align 4
  call void @llvm.dbg.declare(metadata i32* %4, metadata !2003, metadata !336), !dbg !2004
  call void @llvm.dbg.declare(metadata i32* %5, metadata !2005, metadata !336), !dbg !2006
  store i32 0, i32* %5, align 4, !dbg !2007
  br label %6, !dbg !2009

; <label>:6:                                      ; preds = %23, %2
  %7 = load i32, i32* %5, align 4, !dbg !2010
  %8 = load i32, i32* %4, align 4, !dbg !2013
  %9 = icmp ult i32 %7, %8, !dbg !2014
  br i1 %9, label %10, label %26, !dbg !2015

; <label>:10:                                     ; preds = %6
  %11 = load i32, i32* %5, align 4, !dbg !2016
  %12 = load i32*, i32** %3, align 4, !dbg !2018
  %13 = getelementptr inbounds i32, i32* %12, i32 %11, !dbg !2018
  %14 = load i32, i32* %13, align 4, !dbg !2018
  %15 = icmp ne i32 %14, -1, !dbg !2019
  br i1 %15, label %16, label %22, !dbg !2020

; <label>:16:                                     ; preds = %10
  %17 = load i32, i32* %5, align 4, !dbg !2021
  %18 = load i32*, i32** %3, align 4, !dbg !2022
  %19 = getelementptr inbounds i32, i32* %18, i32 %17, !dbg !2022
  %20 = load i32, i32* %19, align 4, !dbg !2022
  %21 = call i32 @kill(i32 %20, i32 15) #7, !dbg !2023
  br label %22, !dbg !2023

; <label>:22:                                     ; preds = %16, %10
  br label %23, !dbg !2024

; <label>:23:                                     ; preds = %22
  %24 = load i32, i32* %5, align 4, !dbg !2026
  %25 = add nsw i32 %24, 1, !dbg !2026
  store i32 %25, i32* %5, align 4, !dbg !2026
  br label %6, !dbg !2028, !llvm.loop !2029

; <label>:26:                                     ; preds = %6
  ret void, !dbg !2031
}

; Function Attrs: nounwind
declare i32 @kill(i32, i32) #2 section ".CODE_REGION_2_"

; Function Attrs: nounwind
define i32 @wait_processes(i32*, i32, i32) #0 section ".CODE_REGION_2_" !dbg !2032 {
  %4 = alloca i32*, align 4
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  %7 = alloca i32, align 4
  %8 = alloca i32, align 4
  %9 = alloca i32, align 4
  %10 = alloca i32, align 4
  store i32* %0, i32** %4, align 4
  call void @llvm.dbg.declare(metadata i32** %4, metadata !2035, metadata !336), !dbg !2036
  store i32 %1, i32* %5, align 4
  call void @llvm.dbg.declare(metadata i32* %5, metadata !2037, metadata !336), !dbg !2038
  store i32 %2, i32* %6, align 4
  call void @llvm.dbg.declare(metadata i32* %6, metadata !2039, metadata !336), !dbg !2040
  call void @llvm.dbg.declare(metadata i32* %7, metadata !2041, metadata !336), !dbg !2042
  call void @llvm.dbg.declare(metadata i32* %8, metadata !2043, metadata !336), !dbg !2044
  store i32 0, i32* %7, align 4, !dbg !2045
  br label %11, !dbg !2046, !llvm.loop !2047

; <label>:11:                                     ; preds = %62, %3
  call void @llvm.dbg.declare(metadata i32* %9, metadata !2048, metadata !336), !dbg !2050
  store i32 0, i32* %8, align 4, !dbg !2051
  %12 = load i32, i32* %6, align 4, !dbg !2052
  %13 = call i32 @alarm(i32 %12) #7, !dbg !2053
  %14 = call i32 @waitpid(i32 0, i32* null, i32 0), !dbg !2054
  store i32 %14, i32* %9, align 4, !dbg !2055
  %15 = load i32, i32* %9, align 4, !dbg !2056
  %16 = icmp ne i32 %15, -1, !dbg !2058
  br i1 %16, label %17, label %51, !dbg !2059

; <label>:17:                                     ; preds = %11
  call void @llvm.dbg.declare(metadata i32* %10, metadata !2060, metadata !336), !dbg !2062
  store i32 0, i32* %10, align 4, !dbg !2063
  br label %18, !dbg !2065

; <label>:18:                                     ; preds = %47, %17
  %19 = load i32, i32* %10, align 4, !dbg !2066
  %20 = load i32, i32* %5, align 4, !dbg !2069
  %21 = icmp ult i32 %19, %20, !dbg !2070
  br i1 %21, label %22, label %50, !dbg !2071

; <label>:22:                                     ; preds = %18
  %23 = load i32, i32* %10, align 4, !dbg !2072
  %24 = load i32*, i32** %4, align 4, !dbg !2074
  %25 = getelementptr inbounds i32, i32* %24, i32 %23, !dbg !2074
  %26 = load i32, i32* %25, align 4, !dbg !2074
  %27 = icmp ne i32 %26, -1, !dbg !2075
  br i1 %27, label %28, label %46, !dbg !2076

; <label>:28:                                     ; preds = %22
  %29 = load i32, i32* %10, align 4, !dbg !2077
  %30 = load i32*, i32** %4, align 4, !dbg !2080
  %31 = getelementptr inbounds i32, i32* %30, i32 %29, !dbg !2080
  %32 = load i32, i32* %31, align 4, !dbg !2080
  %33 = load i32, i32* %9, align 4, !dbg !2081
  %34 = icmp eq i32 %32, %33, !dbg !2082
  br i1 %34, label %35, label %42, !dbg !2083

; <label>:35:                                     ; preds = %28
  %36 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !2084
  %37 = load i32, i32* %9, align 4, !dbg !2084
  call void @__AMI_fake_direct_transfer(), !dbg !2084
  %38 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %36, i8* getelementptr inbounds ([40 x i8], [40 x i8]* @.str.2.100, i32 0, i32 0), i32 %37), !dbg !2084
  %39 = load i32, i32* %10, align 4, !dbg !2086
  %40 = load i32*, i32** %4, align 4, !dbg !2087
  %41 = getelementptr inbounds i32, i32* %40, i32 %39, !dbg !2087
  store i32 -1, i32* %41, align 4, !dbg !2088
  br label %45, !dbg !2089

; <label>:42:                                     ; preds = %28
  %43 = load i32, i32* %8, align 4, !dbg !2090
  %44 = add nsw i32 %43, 1, !dbg !2090
  store i32 %44, i32* %8, align 4, !dbg !2090
  br label %45

; <label>:45:                                     ; preds = %42, %35
  br label %46, !dbg !2091

; <label>:46:                                     ; preds = %45, %22
  br label %47, !dbg !2092

; <label>:47:                                     ; preds = %46
  %48 = load i32, i32* %10, align 4, !dbg !2094
  %49 = add nsw i32 %48, 1, !dbg !2094
  store i32 %49, i32* %10, align 4, !dbg !2094
  br label %18, !dbg !2096, !llvm.loop !2097

; <label>:50:                                     ; preds = %18
  br label %61, !dbg !2099

; <label>:51:                                     ; preds = %11
  %52 = call i32* @__errno_location() #1, !dbg !2100
  %53 = load i32, i32* %52, align 4, !dbg !2100
  store i32 %53, i32* %7, align 4, !dbg !2102
  %54 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !2103
  %55 = call i32* @__errno_location() #1, !dbg !2103
  %56 = load i32, i32* %55, align 4, !dbg !2103
  %57 = call i32* @__errno_location() #1, !dbg !2104
  %58 = load i32, i32* %57, align 4, !dbg !2103
  %59 = call i8* @strerror(i32 %58) #7, !dbg !2106
  call void @__AMI_fake_direct_transfer(), !dbg !2108
  %60 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %54, i8* getelementptr inbounds ([57 x i8], [57 x i8]* @.str.3.101, i32 0, i32 0), i32 %56, i8* %59), !dbg !2108
  br label %61

; <label>:61:                                     ; preds = %51, %50
  br label %62, !dbg !2110

; <label>:62:                                     ; preds = %61
  %63 = load i32, i32* %8, align 4, !dbg !2111
  %64 = icmp sgt i32 %63, 0, !dbg !2112
  br i1 %64, label %11, label %65, !dbg !2113, !llvm.loop !2047

; <label>:65:                                     ; preds = %62
  %66 = load i32, i32* %7, align 4, !dbg !2115
  ret i32 %66, !dbg !2116
}

; Function Attrs: nounwind
declare i32 @alarm(i32) #2 section ".CODE_REGION_2_"

declare i32 @waitpid(i32, i32*, i32) #5 section ".CODE_REGION_2_"

; Function Attrs: nounwind
define i32 @run_background_command(i32*, i8*, i8**) #0 section ".CODE_REGION_2_" !dbg !2117 {
  %4 = alloca i32*, align 4
  %5 = alloca i8*, align 4
  %6 = alloca i8**, align 4
  %7 = alloca i32, align 4
  %8 = alloca i32, align 4
  store i32* %0, i32** %4, align 4
  call void @llvm.dbg.declare(metadata i32** %4, metadata !2123, metadata !336), !dbg !2124
  store i8* %1, i8** %5, align 4
  call void @llvm.dbg.declare(metadata i8** %5, metadata !2125, metadata !336), !dbg !2126
  store i8** %2, i8*** %6, align 4
  call void @llvm.dbg.declare(metadata i8*** %6, metadata !2127, metadata !336), !dbg !2128
  call void @llvm.dbg.declare(metadata i32* %7, metadata !2129, metadata !336), !dbg !2130
  %9 = call i32 @fork() #7, !dbg !2131
  %10 = load i32*, i32** %4, align 4, !dbg !2132
  store i32 %9, i32* %10, align 4, !dbg !2133
  %11 = load i32*, i32** %4, align 4, !dbg !2134
  %12 = load i32, i32* %11, align 4, !dbg !2136
  %13 = icmp eq i32 %12, 0, !dbg !2137
  br i1 %13, label %14, label %83, !dbg !2138

; <label>:14:                                     ; preds = %3
  call void @llvm.dbg.declare(metadata i32* %8, metadata !2139, metadata !336), !dbg !2141
  %15 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !2142
  %16 = icmp ne %struct._IO_FILE* %15, null, !dbg !2144
  br i1 %16, label %17, label %42, !dbg !2145

; <label>:17:                                     ; preds = %14
  %18 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !2146
  %19 = call i32 @fileno(%struct._IO_FILE* %18) #7, !dbg !2149
  %20 = call i32 @dup2(i32 %19, i32 1) #7, !dbg !2150
  %21 = icmp eq i32 %20, -1, !dbg !2152
  br i1 %21, label %22, label %28, !dbg !2153

; <label>:22:                                     ; preds = %17
  %23 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !2154
  %24 = load i8*, i8** %5, align 4, !dbg !2154
  %25 = call i32* @__errno_location() #1, !dbg !2154
  %26 = load i32, i32* %25, align 4, !dbg !2154
  call void @__AMI_fake_direct_transfer(), !dbg !2155
  %27 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %23, i8* getelementptr inbounds ([64 x i8], [64 x i8]* @.str.4.104, i32 0, i32 0), i8* %24, i32 %26), !dbg !2155
  br label %28, !dbg !2154

; <label>:28:                                     ; preds = %22, %17
  %29 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !2156
  %30 = call i32 @fileno(%struct._IO_FILE* %29) #7, !dbg !2158
  %31 = call i32 @dup2(i32 %30, i32 2) #7, !dbg !2159
  %32 = icmp eq i32 %31, -1, !dbg !2161
  br i1 %32, label %33, label %39, !dbg !2162

; <label>:33:                                     ; preds = %28
  %34 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !2163
  %35 = load i8*, i8** %5, align 4, !dbg !2163
  %36 = call i32* @__errno_location() #1, !dbg !2163
  %37 = load i32, i32* %36, align 4, !dbg !2163
  call void @__AMI_fake_direct_transfer(), !dbg !2164
  %38 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %34, i8* getelementptr inbounds ([70 x i8], [70 x i8]* @.str.5.105, i32 0, i32 0), i8* %35, i32 %37), !dbg !2164
  br label %39, !dbg !2163

; <label>:39:                                     ; preds = %33, %28
  %40 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !2165
  %41 = call i32 @fclose(%struct._IO_FILE* %40), !dbg !2166
  br label %42, !dbg !2167

; <label>:42:                                     ; preds = %39, %14
  %43 = load %struct._IO_FILE*, %struct._IO_FILE** @Event_file_handle, align 4, !dbg !2168
  %44 = icmp ne %struct._IO_FILE* %43, null, !dbg !2170
  br i1 %44, label %45, label %48, !dbg !2171

; <label>:45:                                     ; preds = %42
  %46 = load %struct._IO_FILE*, %struct._IO_FILE** @Event_file_handle, align 4, !dbg !2172
  %47 = call i32 @fclose(%struct._IO_FILE* %46), !dbg !2173
  br label %48, !dbg !2173

; <label>:48:                                     ; preds = %45, %42
  %49 = call i32 (i8*, i32, ...) @open(i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.6.106, i32 0, i32 0), i32 0), !dbg !2174
  store i32 %49, i32* %8, align 4, !dbg !2175
  %50 = load i32, i32* %8, align 4, !dbg !2176
  %51 = icmp ne i32 %50, -1, !dbg !2178
  br i1 %51, label %52, label %65, !dbg !2179

; <label>:52:                                     ; preds = %48
  %53 = load i32, i32* %8, align 4, !dbg !2180
  %54 = call i32 @dup2(i32 %53, i32 0) #7, !dbg !2183
  %55 = icmp eq i32 %54, -1, !dbg !2184
  br i1 %55, label %56, label %62, !dbg !2185

; <label>:56:                                     ; preds = %52
  %57 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !2186
  %58 = load i8*, i8** %5, align 4, !dbg !2186
  %59 = call i32* @__errno_location() #1, !dbg !2186
  %60 = load i32, i32* %59, align 4, !dbg !2186
  call void @__AMI_fake_direct_transfer(), !dbg !2187
  %61 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %57, i8* getelementptr inbounds ([63 x i8], [63 x i8]* @.str.7.107, i32 0, i32 0), i8* %58, i32 %60), !dbg !2187
  br label %62, !dbg !2186

; <label>:62:                                     ; preds = %56, %52
  %63 = load i32, i32* %8, align 4, !dbg !2189
  %64 = call i32 @close(i32 %63), !dbg !2190
  br label %71, !dbg !2191

; <label>:65:                                     ; preds = %48
  %66 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !2192
  %67 = load i8*, i8** %5, align 4, !dbg !2192
  %68 = call i32* @__errno_location() #1, !dbg !2192
  %69 = load i32, i32* %68, align 4, !dbg !2192
  call void @__AMI_fake_direct_transfer(), !dbg !2193
  %70 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %66, i8* getelementptr inbounds ([71 x i8], [71 x i8]* @.str.8.108, i32 0, i32 0), i8* %67, i32 %69), !dbg !2193
  br label %71

; <label>:71:                                     ; preds = %65, %62
  %72 = call i32 @close(i32 0), !dbg !2195
  %73 = load i8*, i8** %5, align 4, !dbg !2196
  %74 = load i8**, i8*** %6, align 4, !dbg !2197
  %75 = call i32 @execvp(i8* %73, i8** %74) #7, !dbg !2198
  %76 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !2199
  %77 = load i8*, i8** %5, align 4, !dbg !2199
  %78 = call i32* @__errno_location() #1, !dbg !2199
  %79 = load i32, i32* %78, align 4, !dbg !2199
  call void @__AMI_fake_direct_transfer(), !dbg !2200
  %80 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %76, i8* getelementptr inbounds ([66 x i8], [66 x i8]* @.str.9.109, i32 0, i32 0), i8* %77, i32 %79), !dbg !2200
  %81 = call i32* @__errno_location() #1, !dbg !2202
  %82 = load i32, i32* %81, align 4, !dbg !2202
  call void @exit(i32 %82) #10, !dbg !2203
  unreachable, !dbg !2204

; <label>:83:                                     ; preds = %3
  %84 = load i32*, i32** %4, align 4, !dbg !2205
  %85 = load i32, i32* %84, align 4, !dbg !2208
  %86 = icmp sgt i32 %85, 0, !dbg !2209
  br i1 %86, label %87, label %88, !dbg !2210

; <label>:87:                                     ; preds = %83
  store i32 0, i32* %7, align 4, !dbg !2211
  br label %96, !dbg !2212

; <label>:88:                                     ; preds = %83
  %89 = call i32* @__errno_location() #1, !dbg !2213
  %90 = load i32, i32* %89, align 4, !dbg !2213
  store i32 %90, i32* %7, align 4, !dbg !2215
  %91 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !2216
  %92 = load i8*, i8** %5, align 4, !dbg !2216
  %93 = call i32* @__errno_location() #1, !dbg !2216
  %94 = load i32, i32* %93, align 4, !dbg !2216
  call void @__AMI_fake_direct_transfer(), !dbg !2217
  %95 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %91, i8* getelementptr inbounds ([50 x i8], [50 x i8]* @.str.10.110, i32 0, i32 0), i8* %92, i32 %94), !dbg !2217
  br label %96

; <label>:96:                                     ; preds = %88, %87
  br label %97

; <label>:97:                                     ; preds = %96
  %98 = load i32, i32* %7, align 4, !dbg !2219
  ret i32 %98, !dbg !2220
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
define i32 @configure_timer(float) #0 section ".CODE_REGION_2_" !dbg !2221 {
  %2 = alloca float, align 4
  %3 = alloca i32, align 4
  %4 = alloca %struct.itimerval, align 4
  store float %0, float* %2, align 4
  call void @llvm.dbg.declare(metadata float* %2, metadata !2225, metadata !336), !dbg !2226
  call void @llvm.dbg.declare(metadata i32* %3, metadata !2227, metadata !336), !dbg !2228
  call void @llvm.dbg.declare(metadata %struct.itimerval* %4, metadata !2229, metadata !336), !dbg !2238
  %5 = load float, float* %2, align 4, !dbg !2239
  %6 = fcmp olt float %5, 0.000000e+00, !dbg !2241
  br i1 %6, label %7, label %16, !dbg !2242

; <label>:7:                                      ; preds = %1
  %8 = getelementptr inbounds %struct.itimerval, %struct.itimerval* %4, i32 0, i32 1, !dbg !2243
  %9 = getelementptr inbounds %struct.timeval, %struct.timeval* %8, i32 0, i32 0, !dbg !2245
  store i32 0, i32* %9, align 4, !dbg !2246
  %10 = getelementptr inbounds %struct.itimerval, %struct.itimerval* %4, i32 0, i32 1, !dbg !2247
  %11 = getelementptr inbounds %struct.timeval, %struct.timeval* %10, i32 0, i32 1, !dbg !2248
  store i32 0, i32* %11, align 4, !dbg !2249
  %12 = getelementptr inbounds %struct.itimerval, %struct.itimerval* %4, i32 0, i32 0, !dbg !2250
  %13 = getelementptr inbounds %struct.timeval, %struct.timeval* %12, i32 0, i32 0, !dbg !2251
  store i32 0, i32* %13, align 4, !dbg !2252
  %14 = getelementptr inbounds %struct.itimerval, %struct.itimerval* %4, i32 0, i32 0, !dbg !2253
  %15 = getelementptr inbounds %struct.timeval, %struct.timeval* %14, i32 0, i32 1, !dbg !2254
  store i32 0, i32* %15, align 4, !dbg !2255
  br label %36, !dbg !2256

; <label>:16:                                     ; preds = %1
  %17 = getelementptr inbounds %struct.itimerval, %struct.itimerval* %4, i32 0, i32 1, !dbg !2257
  %18 = getelementptr inbounds %struct.timeval, %struct.timeval* %17, i32 0, i32 0, !dbg !2259
  store i32 0, i32* %18, align 4, !dbg !2260
  %19 = getelementptr inbounds %struct.itimerval, %struct.itimerval* %4, i32 0, i32 1, !dbg !2261
  %20 = getelementptr inbounds %struct.timeval, %struct.timeval* %19, i32 0, i32 1, !dbg !2262
  store i32 250000, i32* %20, align 4, !dbg !2263
  %21 = load float, float* %2, align 4, !dbg !2264
  %22 = fptosi float %21 to i32, !dbg !2265
  %23 = getelementptr inbounds %struct.itimerval, %struct.itimerval* %4, i32 0, i32 0, !dbg !2266
  %24 = getelementptr inbounds %struct.timeval, %struct.timeval* %23, i32 0, i32 0, !dbg !2267
  store i32 %22, i32* %24, align 4, !dbg !2268
  %25 = load float, float* %2, align 4, !dbg !2269
  %26 = getelementptr inbounds %struct.itimerval, %struct.itimerval* %4, i32 0, i32 0, !dbg !2270
  %27 = getelementptr inbounds %struct.timeval, %struct.timeval* %26, i32 0, i32 0, !dbg !2271
  %28 = load i32, i32* %27, align 4, !dbg !2271
  %29 = sitofp i32 %28 to float, !dbg !2272
  %30 = fsub float %25, %29, !dbg !2273
  %31 = fpext float %30 to double, !dbg !2274
  %32 = fmul double %31, 1.000000e+06, !dbg !2275
  %33 = fptosi double %32 to i32, !dbg !2276
  %34 = getelementptr inbounds %struct.itimerval, %struct.itimerval* %4, i32 0, i32 0, !dbg !2277
  %35 = getelementptr inbounds %struct.timeval, %struct.timeval* %34, i32 0, i32 1, !dbg !2278
  store i32 %33, i32* %35, align 4, !dbg !2279
  br label %36

; <label>:36:                                     ; preds = %16, %7
  %37 = call i32 @setitimer(i32 0, %struct.itimerval* %4, %struct.itimerval* null) #7, !dbg !2280
  %38 = icmp eq i32 %37, 0, !dbg !2282
  br i1 %38, label %39, label %48, !dbg !2283

; <label>:39:                                     ; preds = %36
  %40 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !2284
  %41 = getelementptr inbounds %struct.itimerval, %struct.itimerval* %4, i32 0, i32 0, !dbg !2284
  %42 = getelementptr inbounds %struct.timeval, %struct.timeval* %41, i32 0, i32 0, !dbg !2284
  %43 = load i32, i32* %42, align 4, !dbg !2284
  %44 = getelementptr inbounds %struct.itimerval, %struct.itimerval* %4, i32 0, i32 0, !dbg !2284
  %45 = getelementptr inbounds %struct.timeval, %struct.timeval* %44, i32 0, i32 1, !dbg !2284
  %46 = load i32, i32* %45, align 4, !dbg !2284
  call void @__AMI_fake_direct_transfer(), !dbg !2284
  %47 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %40, i8* getelementptr inbounds ([46 x i8], [46 x i8]* @.str.11.113, i32 0, i32 0), i32 %43, i32 %46), !dbg !2284
  store i32 0, i32* %3, align 4, !dbg !2286
  br label %58, !dbg !2287

; <label>:48:                                     ; preds = %36
  %49 = call i32* @__errno_location() #1, !dbg !2288
  %50 = load i32, i32* %49, align 4, !dbg !2288
  store i32 %50, i32* %3, align 4, !dbg !2290
  %51 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !2291
  %52 = call i32* @__errno_location() #1, !dbg !2291
  %53 = load i32, i32* %52, align 4, !dbg !2291
  %54 = call i32* @__errno_location() #1, !dbg !2292
  %55 = load i32, i32* %54, align 4, !dbg !2291
  %56 = call i8* @strerror(i32 %55) #7, !dbg !2294
  call void @__AMI_fake_direct_transfer(), !dbg !2296
  %57 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %51, i8* getelementptr inbounds ([35 x i8], [35 x i8]* @.str.12.114, i32 0, i32 0), i32 %53, i8* %56), !dbg !2296
  br label %58

; <label>:58:                                     ; preds = %48, %39
  %59 = load i32, i32* %3, align 4, !dbg !2298
  ret i32 %59, !dbg !2299
}

; Function Attrs: nounwind
declare i32 @setitimer(i32, %struct.itimerval*, %struct.itimerval*) #2 section ".CODE_REGION_2_"

; Function Attrs: nounwind
define i32 @daemonize(i8*) #0 section ".CODE_REGION_2_" !dbg !2300 {
  %2 = alloca i8*, align 4
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  store i8* %0, i8** %2, align 4
  call void @llvm.dbg.declare(metadata i8** %2, metadata !2301, metadata !336), !dbg !2302
  call void @llvm.dbg.declare(metadata i32* %3, metadata !2303, metadata !336), !dbg !2304
  call void @llvm.dbg.declare(metadata i32* %4, metadata !2305, metadata !336), !dbg !2306
  call void @llvm.dbg.declare(metadata i32* %5, metadata !2307, metadata !336), !dbg !2308
  call void @llvm.dbg.declare(metadata i32* %6, metadata !2309, metadata !336), !dbg !2310
  %7 = call i32 @fork() #7, !dbg !2311
  store i32 %7, i32* %4, align 4, !dbg !2312
  %8 = load i32, i32* %4, align 4, !dbg !2313
  %9 = icmp ne i32 %8, -1, !dbg !2315
  br i1 %9, label %10, label %69, !dbg !2316

; <label>:10:                                     ; preds = %1
  %11 = load i32, i32* %4, align 4, !dbg !2317
  %12 = icmp sgt i32 %11, 0, !dbg !2320
  br i1 %12, label %13, label %14, !dbg !2321

; <label>:13:                                     ; preds = %10
  call void @exit(i32 0) #10, !dbg !2322
  unreachable, !dbg !2322

; <label>:14:                                     ; preds = %10
  %15 = call i32 @setsid() #7, !dbg !2323
  %16 = icmp ne i32 %15, -1, !dbg !2325
  br i1 %16, label %17, label %61, !dbg !2326

; <label>:17:                                     ; preds = %14
  %18 = call void (i32)* @signal(i32 17, void (i32)* inttoptr (i32 1 to void (i32)*)) #7, !dbg !2327
  %19 = call void (i32)* @signal(i32 1, void (i32)* inttoptr (i32 1 to void (i32)*)) #7, !dbg !2329
  %20 = call i32 @fork() #7, !dbg !2330
  store i32 %20, i32* %4, align 4, !dbg !2331
  %21 = load i32, i32* %4, align 4, !dbg !2332
  %22 = icmp ne i32 %21, -1, !dbg !2334
  br i1 %22, label %23, label %53, !dbg !2335

; <label>:23:                                     ; preds = %17
  %24 = load i32, i32* %4, align 4, !dbg !2336
  %25 = icmp sgt i32 %24, 0, !dbg !2339
  br i1 %25, label %26, label %27, !dbg !2340

; <label>:26:                                     ; preds = %23
  call void @exit(i32 0) #10, !dbg !2341
  unreachable, !dbg !2341

; <label>:27:                                     ; preds = %23
  %28 = call i32 @umask(i32 0) #7, !dbg !2342
  %29 = load i8*, i8** %2, align 4, !dbg !2343
  %30 = call i32 @chdir(i8* %29) #7, !dbg !2344
  %31 = call i32 (i8*, i32, ...) @open(i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.6.106, i32 0, i32 0), i32 0), !dbg !2345
  store i32 %31, i32* %5, align 4, !dbg !2346
  %32 = load i32, i32* %5, align 4, !dbg !2347
  %33 = icmp ne i32 %32, -1, !dbg !2349
  br i1 %33, label %34, label %39, !dbg !2350

; <label>:34:                                     ; preds = %27
  %35 = load i32, i32* %5, align 4, !dbg !2351
  %36 = call i32 @dup2(i32 %35, i32 0) #7, !dbg !2353
  %37 = load i32, i32* %5, align 4, !dbg !2354
  %38 = call i32 @close(i32 %37), !dbg !2355
  br label %40, !dbg !2356

; <label>:39:                                     ; preds = %27
  call void @perror(i8* getelementptr inbounds ([65 x i8], [65 x i8]* @.str.13.115, i32 0, i32 0)), !dbg !2357
  br label %40

; <label>:40:                                     ; preds = %39, %34
  %41 = call i32 (i8*, i32, ...) @open(i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.6.106, i32 0, i32 0), i32 1), !dbg !2358
  store i32 %41, i32* %6, align 4, !dbg !2359
  %42 = load i32, i32* %6, align 4, !dbg !2360
  %43 = icmp ne i32 %42, -1, !dbg !2362
  br i1 %43, label %44, label %51, !dbg !2363

; <label>:44:                                     ; preds = %40
  %45 = load i32, i32* %6, align 4, !dbg !2364
  %46 = call i32 @dup2(i32 %45, i32 2) #7, !dbg !2366
  %47 = load i32, i32* %6, align 4, !dbg !2367
  %48 = call i32 @dup2(i32 %47, i32 1) #7, !dbg !2368
  %49 = load i32, i32* %6, align 4, !dbg !2369
  %50 = call i32 @close(i32 %49), !dbg !2370
  br label %52, !dbg !2371

; <label>:51:                                     ; preds = %40
  call void @perror(i8* getelementptr inbounds ([65 x i8], [65 x i8]* @.str.14.116, i32 0, i32 0)), !dbg !2372
  br label %52

; <label>:52:                                     ; preds = %51, %44
  br label %60, !dbg !2373

; <label>:53:                                     ; preds = %17
  %54 = call i32* @__errno_location() #1, !dbg !2374
  %55 = load i32, i32* %54, align 4, !dbg !2374
  store i32 %55, i32* %3, align 4, !dbg !2376
  %56 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 4, !dbg !2377
  %57 = call i32* @__errno_location() #1, !dbg !2378
  %58 = load i32, i32* %57, align 4, !dbg !2378
  %59 = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %56, i8* getelementptr inbounds ([56 x i8], [56 x i8]* @.str.15.117, i32 0, i32 0), i32 %58), !dbg !2379
  br label %60

; <label>:60:                                     ; preds = %53, %52
  br label %68, !dbg !2381

; <label>:61:                                     ; preds = %14
  %62 = call i32* @__errno_location() #1, !dbg !2382
  %63 = load i32, i32* %62, align 4, !dbg !2382
  store i32 %63, i32* %3, align 4, !dbg !2384
  %64 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 4, !dbg !2385
  %65 = call i32* @__errno_location() #1, !dbg !2386
  %66 = load i32, i32* %65, align 4, !dbg !2386
  %67 = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %64, i8* getelementptr inbounds ([79 x i8], [79 x i8]* @.str.16.118, i32 0, i32 0), i32 %66), !dbg !2387
  br label %68

; <label>:68:                                     ; preds = %61, %60
  br label %76, !dbg !2389

; <label>:69:                                     ; preds = %1
  %70 = call i32* @__errno_location() #1, !dbg !2390
  %71 = load i32, i32* %70, align 4, !dbg !2390
  store i32 %71, i32* %3, align 4, !dbg !2392
  %72 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 4, !dbg !2393
  %73 = call i32* @__errno_location() #1, !dbg !2394
  %74 = load i32, i32* %73, align 4, !dbg !2394
  %75 = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %72, i8* getelementptr inbounds ([55 x i8], [55 x i8]* @.str.17.119, i32 0, i32 0), i32 %74), !dbg !2395
  br label %76

; <label>:76:                                     ; preds = %69, %68
  %77 = load i32, i32* %3, align 4, !dbg !2397
  ret i32 %77, !dbg !2398
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
define void @get_localtime_str(i8*, i32) #0 section ".CODE_REGION_1_" !dbg !2399 {
  %3 = alloca i8*, align 4
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  %6 = alloca %struct.tm*, align 4
  store i8* %0, i8** %3, align 4
  call void @llvm.dbg.declare(metadata i8** %3, metadata !2402, metadata !336), !dbg !2403
  store i32 %1, i32* %4, align 4
  call void @llvm.dbg.declare(metadata i32* %4, metadata !2404, metadata !336), !dbg !2405
  call void @llvm.dbg.declare(metadata i32* %5, metadata !2406, metadata !336), !dbg !2407
  call void @llvm.dbg.declare(metadata %struct.tm** %6, metadata !2408, metadata !336), !dbg !2423
  %7 = call i32 @time(i32* null) #7, !dbg !2424
  store i32 %7, i32* %5, align 4, !dbg !2425
  %8 = load i32, i32* %5, align 4, !dbg !2426
  %9 = icmp ne i32 %8, -1, !dbg !2428
  br i1 %9, label %10, label %25, !dbg !2429

; <label>:10:                                     ; preds = %2
  %11 = call %struct.tm* @localtime(i32* %5) #7, !dbg !2430
  store %struct.tm* %11, %struct.tm** %6, align 4, !dbg !2432
  %12 = load i8*, i8** %3, align 4, !dbg !2433
  %13 = load i32, i32* %4, align 4, !dbg !2435
  %14 = load %struct.tm*, %struct.tm** %6, align 4, !dbg !2436
  %15 = call i32 @strftime(i8* %12, i32 %13, i8* getelementptr inbounds ([18 x i8], [18 x i8]* @.str.124, i32 0, i32 0), %struct.tm* %14) #7, !dbg !2437
  %16 = icmp eq i32 %15, 0, !dbg !2438
  br i1 %16, label %17, label %24, !dbg !2439

; <label>:17:                                     ; preds = %10
  %18 = load i32, i32* %4, align 4, !dbg !2440
  %19 = icmp ugt i32 %18, 0, !dbg !2442
  br i1 %19, label %20, label %23, !dbg !2443

; <label>:20:                                     ; preds = %17
  %21 = load i8*, i8** %3, align 4, !dbg !2444
  %22 = getelementptr inbounds i8, i8* %21, i32 0, !dbg !2444
  store i8 0, i8* %22, align 1, !dbg !2445
  br label %23, !dbg !2444

; <label>:23:                                     ; preds = %20, %17
  br label %24, !dbg !2446

; <label>:24:                                     ; preds = %23, %10
  br label %32, !dbg !2448

; <label>:25:                                     ; preds = %2
  %26 = load i32, i32* %4, align 4, !dbg !2449
  %27 = icmp ugt i32 %26, 0, !dbg !2452
  br i1 %27, label %28, label %31, !dbg !2453

; <label>:28:                                     ; preds = %25
  %29 = load i8*, i8** %3, align 4, !dbg !2454
  %30 = getelementptr inbounds i8, i8* %29, i32 0, !dbg !2454
  store i8 0, i8* %30, align 1, !dbg !2455
  br label %31, !dbg !2454

; <label>:31:                                     ; preds = %28, %25
  br label %32

; <label>:32:                                     ; preds = %31, %24
  call void @__AMI_fake_rt_transfer(), !dbg !2456
  ret void, !dbg !2456
}

; Function Attrs: nounwind
declare i32 @time(i32*) #2 section ".CODE_REGION_1_"

; Function Attrs: nounwind
declare %struct.tm* @localtime(i32*) #2 section ".CODE_REGION_1_"

; Function Attrs: nounwind
declare i32 @strftime(i8*, i32, i8*, %struct.tm*) #2 section ".CODE_REGION_1_"

; Function Attrs: nounwind
define i32 @msg_printf(%struct._IO_FILE*, i8*, ...) #0 section ".CODE_REGION_1_" !dbg !2457 {
  %3 = alloca %struct._IO_FILE*, align 4
  %4 = alloca i8*, align 4
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  %7 = alloca i32, align 4
  %8 = alloca %struct.__va_list, align 4
  %9 = alloca [20 x i8], align 1
  store %struct._IO_FILE* %0, %struct._IO_FILE** %3, align 4
  call void @llvm.dbg.declare(metadata %struct._IO_FILE** %3, metadata !2460, metadata !336), !dbg !2461
  store i8* %1, i8** %4, align 4
  call void @llvm.dbg.declare(metadata i8** %4, metadata !2462, metadata !336), !dbg !2463
  call void @llvm.dbg.declare(metadata i32* %5, metadata !2464, metadata !336), !dbg !2465
  %10 = load i32, i32* @Console_messages, align 4, !dbg !2466
  %11 = icmp ne i32 %10, 0, !dbg !2466
  br i1 %11, label %15, label %12, !dbg !2468

; <label>:12:                                     ; preds = %2
  %13 = load %struct._IO_FILE*, %struct._IO_FILE** %3, align 4, !dbg !2469
  %14 = icmp ne %struct._IO_FILE* %13, null, !dbg !2471
  br i1 %14, label %15, label %49, !dbg !2472

; <label>:15:                                     ; preds = %12, %2
  call void @llvm.dbg.declare(metadata i32* %6, metadata !2473, metadata !336), !dbg !2475
  store i32 0, i32* %6, align 4, !dbg !2475
  call void @llvm.dbg.declare(metadata i32* %7, metadata !2476, metadata !336), !dbg !2477
  store i32 0, i32* %7, align 4, !dbg !2477
  call void @llvm.dbg.declare(metadata %struct.__va_list* %8, metadata !2478, metadata !336), !dbg !2486
  call void @llvm.dbg.declare(metadata [20 x i8]* %9, metadata !2487, metadata !336), !dbg !2491
  %16 = getelementptr inbounds [20 x i8], [20 x i8]* %9, i32 0, i32 0, !dbg !2492
  call void @get_localtime_str(i8* %16, i32 20), !dbg !2493
  %17 = bitcast %struct.__va_list* %8 to i8*, !dbg !2494
  call void @llvm.va_start(i8* %17), !dbg !2494
  %18 = load i32, i32* @Console_messages, align 4, !dbg !2495
  %19 = icmp ne i32 %18, 0, !dbg !2495
  br i1 %19, label %20, label %26, !dbg !2497

; <label>:20:                                     ; preds = %15
  %21 = load i8*, i8** %4, align 4, !dbg !2498
  %22 = getelementptr inbounds %struct.__va_list, %struct.__va_list* %8, i32 0, i32 0, !dbg !2499
  %23 = bitcast i8** %22 to [1 x i32]*, !dbg !2499
  %24 = load [1 x i32], [1 x i32]* %23, align 4, !dbg !2499
  %25 = call i32 @vprintf(i8* %21, [1 x i32] %24), !dbg !2499
  store i32 %25, i32* %6, align 4, !dbg !2500
  br label %26, !dbg !2501

; <label>:26:                                     ; preds = %20, %15
  %27 = load %struct._IO_FILE*, %struct._IO_FILE** %3, align 4, !dbg !2502
  %28 = icmp ne %struct._IO_FILE* %27, null, !dbg !2504
  br i1 %28, label %29, label %39, !dbg !2505

; <label>:29:                                     ; preds = %26
  %30 = load %struct._IO_FILE*, %struct._IO_FILE** %3, align 4, !dbg !2506
  %31 = getelementptr inbounds [20 x i8], [20 x i8]* %9, i32 0, i32 0, !dbg !2508
  %32 = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %30, i8* getelementptr inbounds ([6 x i8], [6 x i8]* @.str.1.127, i32 0, i32 0), i8* %31), !dbg !2509
  %33 = load %struct._IO_FILE*, %struct._IO_FILE** %3, align 4, !dbg !2510
  %34 = load i8*, i8** %4, align 4, !dbg !2511
  %35 = getelementptr inbounds %struct.__va_list, %struct.__va_list* %8, i32 0, i32 0, !dbg !2512
  %36 = bitcast i8** %35 to [1 x i32]*, !dbg !2512
  %37 = load [1 x i32], [1 x i32]* %36, align 4, !dbg !2512
  %38 = call i32 @vfprintf(%struct._IO_FILE* %33, i8* %34, [1 x i32] %37), !dbg !2512
  store i32 %38, i32* %7, align 4, !dbg !2513
  br label %39, !dbg !2514

; <label>:39:                                     ; preds = %29, %26
  %40 = bitcast %struct.__va_list* %8 to i8*, !dbg !2515
  call void @llvm.va_end(i8* %40), !dbg !2515
  %41 = load i32, i32* %6, align 4, !dbg !2516
  %42 = icmp ne i32 %41, 0, !dbg !2517
  br i1 %42, label %43, label %45, !dbg !2518

; <label>:43:                                     ; preds = %39
  %44 = load i32, i32* %6, align 4, !dbg !2519
  br label %47, !dbg !2521

; <label>:45:                                     ; preds = %39
  %46 = load i32, i32* %7, align 4, !dbg !2522
  br label %47, !dbg !2524

; <label>:47:                                     ; preds = %45, %43
  %48 = phi i32 [ %44, %43 ], [ %46, %45 ], !dbg !2525
  store i32 %48, i32* %5, align 4, !dbg !2527
  br label %50, !dbg !2528

; <label>:49:                                     ; preds = %12
  store i32 0, i32* %5, align 4, !dbg !2529
  br label %50

; <label>:50:                                     ; preds = %49, %47
  %51 = load i32, i32* %5, align 4, !dbg !2530
  call void @__AMI_fake_rt_transfer(), !dbg !2531
  ret i32 %51, !dbg !2531
}

; Function Attrs: nounwind
declare void @llvm.va_start(i8*) #7

declare i32 @vprintf(i8*, [1 x i32]) #5 section ".CODE_REGION_1_"

declare i32 @vfprintf(%struct._IO_FILE*, i8*, [1 x i32]) #5 section ".CODE_REGION_1_"

; Function Attrs: nounwind
declare void @llvm.va_end(i8*) #7

; Function Attrs: nounwind
define %struct._IO_FILE* @open_msg_file(i8*, i32) #0 section ".CODE_REGION_2_" !dbg !2532 {
  %3 = alloca i8*, align 4
  %4 = alloca i32, align 4
  %5 = alloca %struct._IO_FILE*, align 4
  %6 = alloca i32, align 4
  %7 = alloca i32, align 4
  %8 = alloca [20 x i8], align 1
  %9 = alloca i8*, align 4
  store i8* %0, i8** %3, align 4
  call void @llvm.dbg.declare(metadata i8** %3, metadata !2535, metadata !336), !dbg !2536
  store i32 %1, i32* %4, align 4
  call void @llvm.dbg.declare(metadata i32* %4, metadata !2537, metadata !336), !dbg !2538
  call void @llvm.dbg.declare(metadata %struct._IO_FILE** %5, metadata !2539, metadata !336), !dbg !2540
  %10 = load i8*, i8** %3, align 4, !dbg !2541
  %11 = call %struct._IO_FILE* @fopen(i8* %10, i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str.2.128, i32 0, i32 0)), !dbg !2542
  store %struct._IO_FILE* %11, %struct._IO_FILE** %5, align 4, !dbg !2543
  %12 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !2544
  %13 = icmp ne %struct._IO_FILE* %12, null, !dbg !2544
  br i1 %13, label %14, label %71, !dbg !2546

; <label>:14:                                     ; preds = %2
  call void @llvm.dbg.declare(metadata i32* %6, metadata !2547, metadata !336), !dbg !2549
  call void @llvm.dbg.declare(metadata i32* %7, metadata !2550, metadata !336), !dbg !2551
  call void @llvm.dbg.declare(metadata [20 x i8]* %8, metadata !2552, metadata !336), !dbg !2553
  %15 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !2554
  %16 = call i32 @fileno(%struct._IO_FILE* %15) #7, !dbg !2555
  %17 = call i32 @flock(i32 %16, i32 8) #7, !dbg !2556
  %18 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !2558
  call void @setbuf(%struct._IO_FILE* %18, i8* null) #7, !dbg !2559
  %19 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !2560
  %20 = call i32 @fseek(%struct._IO_FILE* %19, i32 0, i32 2), !dbg !2561
  %21 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !2562
  %22 = call i32 @ftell(%struct._IO_FILE* %21), !dbg !2563
  store i32 %22, i32* %6, align 4, !dbg !2564
  %23 = load i32, i32* %6, align 4, !dbg !2565
  %24 = load i32, i32* %4, align 4, !dbg !2567
  %25 = icmp sgt i32 %23, %24, !dbg !2568
  br i1 %25, label %26, label %59, !dbg !2569

; <label>:26:                                     ; preds = %14
  call void @llvm.dbg.declare(metadata i8** %9, metadata !2570, metadata !336), !dbg !2572
  %27 = load i32, i32* %4, align 4, !dbg !2573
  %28 = mul i32 %27, 1, !dbg !2574
  %29 = call noalias i8* @malloc(i32 %28) #7, !dbg !2575
  store i8* %29, i8** %9, align 4, !dbg !2576
  %30 = load i8*, i8** %9, align 4, !dbg !2577
  %31 = icmp ne i8* %30, null, !dbg !2577
  br i1 %31, label %32, label %58, !dbg !2579

; <label>:32:                                     ; preds = %26
  %33 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !2580
  %34 = load i32, i32* %4, align 4, !dbg !2582
  %35 = sub nsw i32 0, %34, !dbg !2583
  %36 = call i32 @fseek(%struct._IO_FILE* %33, i32 %35, i32 2), !dbg !2584
  %37 = load i8*, i8** %9, align 4, !dbg !2585
  %38 = load i32, i32* %4, align 4, !dbg !2586
  %39 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !2587
  %40 = call i32 @fread(i8* %37, i32 1, i32 %38, %struct._IO_FILE* %39), !dbg !2588
  store i32 %40, i32* %7, align 4, !dbg !2589
  %41 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !2590
  %42 = call i32 @fclose(%struct._IO_FILE* %41), !dbg !2591
  %43 = load i8*, i8** %9, align 4, !dbg !2592
  call void @free(i8* %43) #7, !dbg !2593
  %44 = load i8*, i8** %3, align 4, !dbg !2594
  %45 = call %struct._IO_FILE* @fopen(i8* %44, i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.3.129, i32 0, i32 0)), !dbg !2595
  store %struct._IO_FILE* %45, %struct._IO_FILE** %5, align 4, !dbg !2596
  %46 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !2597
  %47 = icmp ne %struct._IO_FILE* %46, null, !dbg !2597
  br i1 %47, label %48, label %57, !dbg !2599

; <label>:48:                                     ; preds = %32
  %49 = getelementptr inbounds [20 x i8], [20 x i8]* %8, i32 0, i32 0, !dbg !2600
  call void @__AMI_fake_direct_transfer(), !dbg !2602
  call void @get_localtime_str(i8* %49, i32 20), !dbg !2602
  %50 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !2603
  %51 = getelementptr inbounds [20 x i8], [20 x i8]* %8, i32 0, i32 0, !dbg !2604
  %52 = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %50, i8* getelementptr inbounds ([31 x i8], [31 x i8]* @.str.4.130, i32 0, i32 0), i8* %51), !dbg !2605
  %53 = load i8*, i8** %9, align 4, !dbg !2606
  %54 = load i32, i32* %7, align 4, !dbg !2607
  %55 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !2608
  %56 = call i32 @fwrite(i8* %53, i32 1, i32 %54, %struct._IO_FILE* %55), !dbg !2609
  br label %57, !dbg !2610

; <label>:57:                                     ; preds = %48, %32
  br label %58, !dbg !2611

; <label>:58:                                     ; preds = %57, %26
  br label %59, !dbg !2612

; <label>:59:                                     ; preds = %58, %14
  %60 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !2613
  %61 = icmp ne %struct._IO_FILE* %60, null, !dbg !2613
  br i1 %61, label %62, label %70, !dbg !2615

; <label>:62:                                     ; preds = %59
  %63 = getelementptr inbounds [20 x i8], [20 x i8]* %8, i32 0, i32 0, !dbg !2616
  call void @__AMI_fake_direct_transfer(), !dbg !2618
  call void @get_localtime_str(i8* %63, i32 20), !dbg !2618
  %64 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !2619
  %65 = getelementptr inbounds [20 x i8], [20 x i8]* %8, i32 0, i32 0, !dbg !2620
  %66 = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %64, i8* getelementptr inbounds ([64 x i8], [64 x i8]* @.str.5.131, i32 0, i32 0), i8* %65), !dbg !2621
  %67 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !2622
  %68 = getelementptr inbounds [20 x i8], [20 x i8]* %8, i32 0, i32 0, !dbg !2623
  %69 = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %67, i8* getelementptr inbounds ([28 x i8], [28 x i8]* @.str.6.132, i32 0, i32 0), i8* %68), !dbg !2624
  br label %70, !dbg !2625

; <label>:70:                                     ; preds = %62, %59
  br label %71, !dbg !2626

; <label>:71:                                     ; preds = %70, %2
  %72 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 4, !dbg !2627
  ret %struct._IO_FILE* %72, !dbg !2628
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
define void @close_log_file(%struct._IO_FILE*) #0 section ".CODE_REGION_2_" !dbg !2629 {
  %2 = alloca %struct._IO_FILE*, align 4
  %3 = alloca [20 x i8], align 1
  store %struct._IO_FILE* %0, %struct._IO_FILE** %2, align 4
  call void @llvm.dbg.declare(metadata %struct._IO_FILE** %2, metadata !2632, metadata !336), !dbg !2633
  %4 = load %struct._IO_FILE*, %struct._IO_FILE** %2, align 4, !dbg !2634
  %5 = icmp ne %struct._IO_FILE* %4, null, !dbg !2634
  br i1 %5, label %6, label %13, !dbg !2636

; <label>:6:                                      ; preds = %1
  call void @llvm.dbg.declare(metadata [20 x i8]* %3, metadata !2637, metadata !336), !dbg !2639
  %7 = getelementptr inbounds [20 x i8], [20 x i8]* %3, i32 0, i32 0, !dbg !2640
  call void @__AMI_fake_direct_transfer(), !dbg !2641
  call void @get_localtime_str(i8* %7, i32 20), !dbg !2641
  %8 = load %struct._IO_FILE*, %struct._IO_FILE** %2, align 4, !dbg !2642
  %9 = getelementptr inbounds [20 x i8], [20 x i8]* %3, i32 0, i32 0, !dbg !2643
  %10 = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %8, i8* getelementptr inbounds ([32 x i8], [32 x i8]* @.str.7.133, i32 0, i32 0), i8* %9), !dbg !2644
  %11 = load %struct._IO_FILE*, %struct._IO_FILE** %2, align 4, !dbg !2645
  %12 = call i32 @fclose(%struct._IO_FILE* %11), !dbg !2646
  br label %13, !dbg !2647

; <label>:13:                                     ; preds = %6, %1
  ret void, !dbg !2648
}

; Function Attrs: nounwind
define i32 @open_log_files() #0 section ".CODE_REGION_2_" !dbg !2649 {
  %1 = call %struct._IO_FILE* @open_msg_file(i8* getelementptr inbounds ([29 x i8], [29 x i8]* @.str.8.136, i32 0, i32 0), i32 52428800), !dbg !2650
  call void @__AMI_fake_local_wrt(), !dbg !2651
  store %struct._IO_FILE* %1, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !2651
  %2 = call %struct._IO_FILE* @open_msg_file(i8* getelementptr inbounds ([29 x i8], [29 x i8]* @.str.9.137, i32 0, i32 0), i32 52428800), !dbg !2652
  call void @__AMI_fake_local_wrt(), !dbg !2653
  store %struct._IO_FILE* %2, %struct._IO_FILE** @Event_file_handle, align 4, !dbg !2653
  %3 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !2654
  %4 = icmp eq %struct._IO_FILE* %3, null, !dbg !2655
  br i1 %4, label %8, label %5, !dbg !2656

; <label>:5:                                      ; preds = %0
  %6 = load %struct._IO_FILE*, %struct._IO_FILE** @Event_file_handle, align 4, !dbg !2657
  %7 = icmp eq %struct._IO_FILE* %6, null, !dbg !2659
  br label %8, !dbg !2660

; <label>:8:                                      ; preds = %5, %0
  %9 = phi i1 [ true, %0 ], [ %7, %5 ]
  %10 = zext i1 %9 to i32, !dbg !2661
  ret i32 %10, !dbg !2663
}

; Function Attrs: nounwind
define void @close_log_files() #0 section ".CODE_REGION_2_" !dbg !2664 {
  %1 = load %struct._IO_FILE*, %struct._IO_FILE** @Event_file_handle, align 4, !dbg !2665
  call void @close_log_file(%struct._IO_FILE* %1), !dbg !2666
  %2 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !2667
  call void @close_log_file(%struct._IO_FILE* %2), !dbg !2668
  ret void, !dbg !2669
}

; Function Attrs: nounwind
define i32 @GPIO_export(i32) #0 section ".CODE_REGION_1_" !dbg !2670 {
  %2 = alloca i32, align 4
  %3 = alloca [4 x i8], align 1
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  %7 = alloca [34 x i8], align 1
  %8 = alloca i32, align 4
  %9 = alloca i32, align 4
  store i32 %0, i32* %2, align 4
  call void @llvm.dbg.declare(metadata i32* %2, metadata !2673, metadata !336), !dbg !2674
  call void @llvm.dbg.declare(metadata [4 x i8]* %3, metadata !2675, metadata !336), !dbg !2677
  call void @llvm.dbg.declare(metadata i32* %4, metadata !2678, metadata !336), !dbg !2681
  call void @llvm.dbg.declare(metadata i32* %5, metadata !2682, metadata !336), !dbg !2683
  call void @llvm.dbg.declare(metadata i32* %6, metadata !2684, metadata !336), !dbg !2685
  %10 = call i32 (i8*, i32, ...) @open(i8* getelementptr inbounds ([23 x i8], [23 x i8]* @.str.140, i32 0, i32 0), i32 1), !dbg !2686
  store i32 %10, i32* %5, align 4, !dbg !2687
  %11 = load i32, i32* %5, align 4, !dbg !2688
  %12 = icmp ne i32 -1, %11, !dbg !2690
  br i1 %12, label %13, label %54, !dbg !2691

; <label>:13:                                     ; preds = %1
  call void @llvm.dbg.declare(metadata [34 x i8]* %7, metadata !2692, metadata !336), !dbg !2697
  call void @llvm.dbg.declare(metadata i32* %8, metadata !2698, metadata !336), !dbg !2699
  call void @llvm.dbg.declare(metadata i32* %9, metadata !2700, metadata !336), !dbg !2701
  %14 = getelementptr inbounds [4 x i8], [4 x i8]* %3, i32 0, i32 0, !dbg !2702
  %15 = load i32, i32* %2, align 4, !dbg !2703
  %16 = call i32 (i8*, i32, i8*, ...) @snprintf(i8* %14, i32 4, i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.1.141, i32 0, i32 0), i32 %15) #7, !dbg !2704
  store i32 %16, i32* %4, align 4, !dbg !2705
  %17 = load i32, i32* %5, align 4, !dbg !2706
  %18 = getelementptr inbounds [4 x i8], [4 x i8]* %3, i32 0, i32 0, !dbg !2707
  %19 = load i32, i32* %4, align 4, !dbg !2708
  %20 = call i32 @write(i32 %17, i8* %18, i32 %19), !dbg !2709
  %21 = load i32, i32* %5, align 4, !dbg !2710
  %22 = call i32 @close(i32 %21), !dbg !2711
  %23 = getelementptr inbounds [34 x i8], [34 x i8]* %7, i32 0, i32 0, !dbg !2712
  %24 = load i32, i32* %2, align 4, !dbg !2713
  %25 = call i32 (i8*, i32, i8*, ...) @snprintf(i8* %23, i32 34, i8* getelementptr inbounds ([33 x i8], [33 x i8]* @.str.2.142, i32 0, i32 0), i32 %24) #7, !dbg !2714
  store i32 0, i32* %8, align 4, !dbg !2715
  store i32 0, i32* %9, align 4, !dbg !2716
  br label %26, !dbg !2717, !llvm.loop !2718

; <label>:26:                                     ; preds = %44, %13
  %27 = call i32 @usleep(i32 50000), !dbg !2719
  %28 = getelementptr inbounds [34 x i8], [34 x i8]* %7, i32 0, i32 0, !dbg !2721
  %29 = call i32 (i8*, i32, ...) @open(i8* %28, i32 1), !dbg !2722
  store i32 %29, i32* %5, align 4, !dbg !2723
  %30 = load i32, i32* %5, align 4, !dbg !2724
  %31 = icmp ne i32 -1, %30, !dbg !2726
  br i1 %31, label %32, label %35, !dbg !2727

; <label>:32:                                     ; preds = %26
  store i32 1, i32* %8, align 4, !dbg !2728
  %33 = load i32, i32* %5, align 4, !dbg !2730
  %34 = call i32 @close(i32 %33), !dbg !2731
  br label %36, !dbg !2732

; <label>:35:                                     ; preds = %26
  store i32 0, i32* %8, align 4, !dbg !2733
  br label %36

; <label>:36:                                     ; preds = %35, %32
  br label %37, !dbg !2734

; <label>:37:                                     ; preds = %36
  %38 = load i32, i32* %8, align 4, !dbg !2735
  %39 = icmp ne i32 %38, 0, !dbg !2735
  br i1 %39, label %44, label %40, !dbg !2736

; <label>:40:                                     ; preds = %37
  %41 = load i32, i32* %9, align 4, !dbg !2737
  %42 = add nsw i32 %41, 1, !dbg !2737
  store i32 %42, i32* %9, align 4, !dbg !2737
  %43 = icmp slt i32 %41, 20, !dbg !2739
  br label %44

; <label>:44:                                     ; preds = %40, %37
  %45 = phi i1 [ false, %37 ], [ %43, %40 ]
  br i1 %45, label %26, label %46, !dbg !2740, !llvm.loop !2718

; <label>:46:                                     ; preds = %44
  %47 = load i32, i32* %8, align 4, !dbg !2742
  %48 = icmp ne i32 %47, 0, !dbg !2742
  br i1 %48, label %49, label %50, !dbg !2744

; <label>:49:                                     ; preds = %46
  store i32 0, i32* %6, align 4, !dbg !2745
  br label %53, !dbg !2746

; <label>:50:                                     ; preds = %46
  %51 = call i32* @__errno_location() #1, !dbg !2747
  %52 = load i32, i32* %51, align 4, !dbg !2747
  store i32 %52, i32* %6, align 4, !dbg !2748
  br label %53

; <label>:53:                                     ; preds = %50, %49
  br label %57, !dbg !2749

; <label>:54:                                     ; preds = %1
  %55 = call i32* @__errno_location() #1, !dbg !2750
  %56 = load i32, i32* %55, align 4, !dbg !2750
  store i32 %56, i32* %6, align 4, !dbg !2751
  br label %57

; <label>:57:                                     ; preds = %54, %53
  %58 = load i32, i32* %6, align 4, !dbg !2752
  ret i32 %58, !dbg !2753
}

declare i32 @write(i32, i8*, i32) #5 section ".CODE_REGION_1_"

declare i32 @usleep(i32) #5 section ".CODE_REGION_1_"

; Function Attrs: nounwind
define i32 @GPIO_unexport(i32) #0 section ".CODE_REGION_1_" !dbg !2754 {
  %2 = alloca i32, align 4
  %3 = alloca [4 x i8], align 1
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  store i32 %0, i32* %2, align 4
  call void @llvm.dbg.declare(metadata i32* %2, metadata !2755, metadata !336), !dbg !2756
  call void @llvm.dbg.declare(metadata [4 x i8]* %3, metadata !2757, metadata !336), !dbg !2758
  call void @llvm.dbg.declare(metadata i32* %4, metadata !2759, metadata !336), !dbg !2760
  call void @llvm.dbg.declare(metadata i32* %5, metadata !2761, metadata !336), !dbg !2762
  call void @llvm.dbg.declare(metadata i32* %6, metadata !2763, metadata !336), !dbg !2764
  %7 = call i32 (i8*, i32, ...) @open(i8* getelementptr inbounds ([25 x i8], [25 x i8]* @.str.3.143, i32 0, i32 0), i32 1), !dbg !2765
  store i32 %7, i32* %5, align 4, !dbg !2766
  %8 = load i32, i32* %5, align 4, !dbg !2767
  %9 = icmp ne i32 -1, %8, !dbg !2769
  br i1 %9, label %10, label %20, !dbg !2770

; <label>:10:                                     ; preds = %1
  %11 = getelementptr inbounds [4 x i8], [4 x i8]* %3, i32 0, i32 0, !dbg !2771
  %12 = load i32, i32* %2, align 4, !dbg !2773
  %13 = call i32 (i8*, i32, i8*, ...) @snprintf(i8* %11, i32 4, i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.1.141, i32 0, i32 0), i32 %12) #7, !dbg !2774
  store i32 %13, i32* %4, align 4, !dbg !2775
  %14 = load i32, i32* %5, align 4, !dbg !2776
  %15 = getelementptr inbounds [4 x i8], [4 x i8]* %3, i32 0, i32 0, !dbg !2777
  %16 = load i32, i32* %4, align 4, !dbg !2778
  %17 = call i32 @write(i32 %14, i8* %15, i32 %16), !dbg !2779
  %18 = load i32, i32* %5, align 4, !dbg !2780
  %19 = call i32 @close(i32 %18), !dbg !2781
  store i32 0, i32* %6, align 4, !dbg !2782
  br label %23, !dbg !2783

; <label>:20:                                     ; preds = %1
  %21 = call i32* @__errno_location() #1, !dbg !2784
  %22 = load i32, i32* %21, align 4, !dbg !2784
  store i32 %22, i32* %6, align 4, !dbg !2785
  br label %23

; <label>:23:                                     ; preds = %20, %10
  %24 = load i32, i32* %6, align 4, !dbg !2786
  call void @__AMI_fake_rt_transfer(), !dbg !2787
  ret i32 %24, !dbg !2787
}

; Function Attrs: nounwind
define i32 @GPIO_direction(i32, i32) #0 section ".CODE_REGION_1_" !dbg !2788 {
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca [2 x i8*], align 4
  %6 = alloca [34 x i8], align 1
  %7 = alloca i32, align 4
  %8 = alloca i32, align 4
  %9 = alloca i8*, align 4
  store i32 %0, i32* %3, align 4
  call void @llvm.dbg.declare(metadata i32* %3, metadata !2791, metadata !336), !dbg !2792
  store i32 %1, i32* %4, align 4
  call void @llvm.dbg.declare(metadata i32* %4, metadata !2793, metadata !336), !dbg !2794
  call void @llvm.dbg.declare(metadata [2 x i8*]* %5, metadata !2795, metadata !336), !dbg !2797
  %10 = bitcast [2 x i8*]* %5 to i8*, !dbg !2797
  call void @llvm.memcpy.p0i8.p0i8.i32(i8* %10, i8* bitcast ([2 x i8*]* @GPIO_direction.s_directions_str to i8*), i32 8, i32 4, i1 false), !dbg !2797
  call void @llvm.dbg.declare(metadata [34 x i8]* %6, metadata !2798, metadata !336), !dbg !2799
  call void @llvm.dbg.declare(metadata i32* %7, metadata !2800, metadata !336), !dbg !2801
  call void @llvm.dbg.declare(metadata i32* %8, metadata !2802, metadata !336), !dbg !2803
  %11 = getelementptr inbounds [34 x i8], [34 x i8]* %6, i32 0, i32 0, !dbg !2804
  %12 = load i32, i32* %3, align 4, !dbg !2805
  %13 = call i32 (i8*, i32, i8*, ...) @snprintf(i8* %11, i32 34, i8* getelementptr inbounds ([33 x i8], [33 x i8]* @.str.2.142, i32 0, i32 0), i32 %12) #7, !dbg !2806
  %14 = getelementptr inbounds [34 x i8], [34 x i8]* %6, i32 0, i32 0, !dbg !2807
  %15 = call i32 (i8*, i32, ...) @open(i8* %14, i32 1), !dbg !2808
  store i32 %15, i32* %7, align 4, !dbg !2809
  %16 = load i32, i32* %7, align 4, !dbg !2810
  %17 = icmp ne i32 -1, %16, !dbg !2812
  br i1 %17, label %18, label %37, !dbg !2813

; <label>:18:                                     ; preds = %2
  call void @llvm.dbg.declare(metadata i8** %9, metadata !2814, metadata !336), !dbg !2816
  %19 = load i32, i32* %4, align 4, !dbg !2817
  %20 = icmp ne i32 0, %19, !dbg !2818
  %21 = zext i1 %20 to i32, !dbg !2818
  %22 = getelementptr inbounds [2 x i8*], [2 x i8*]* %5, i32 0, i32 %21, !dbg !2819
  %23 = load i8*, i8** %22, align 4, !dbg !2819
  store i8* %23, i8** %9, align 4, !dbg !2820
  %24 = load i32, i32* %7, align 4, !dbg !2821
  %25 = load i8*, i8** %9, align 4, !dbg !2823
  %26 = load i8*, i8** %9, align 4, !dbg !2824
  %27 = call i32 @strlen(i8* %26) #9, !dbg !2825
  %28 = call i32 @write(i32 %24, i8* %25, i32 %27), !dbg !2826
  %29 = icmp ne i32 -1, %28, !dbg !2828
  br i1 %29, label %30, label %31, !dbg !2829

; <label>:30:                                     ; preds = %18
  store i32 0, i32* %8, align 4, !dbg !2830
  br label %34, !dbg !2831

; <label>:31:                                     ; preds = %18
  %32 = call i32* @__errno_location() #1, !dbg !2832
  %33 = load i32, i32* %32, align 4, !dbg !2832
  store i32 %33, i32* %8, align 4, !dbg !2833
  br label %34

; <label>:34:                                     ; preds = %31, %30
  %35 = load i32, i32* %7, align 4, !dbg !2834
  %36 = call i32 @close(i32 %35), !dbg !2835
  br label %40, !dbg !2836

; <label>:37:                                     ; preds = %2
  %38 = call i32* @__errno_location() #1, !dbg !2837
  %39 = load i32, i32* %38, align 4, !dbg !2837
  store i32 %39, i32* %8, align 4, !dbg !2838
  br label %40

; <label>:40:                                     ; preds = %37, %34
  %41 = load i32, i32* %8, align 4, !dbg !2839
  ret i32 %41, !dbg !2840
}

; Function Attrs: nounwind
define i32 @GPIO_read(i32, i32*) #0 section ".CODE_REGION_1_" !dbg !2841 {
  %3 = alloca i32, align 4
  %4 = alloca i32*, align 4
  %5 = alloca [30 x i8], align 1
  %6 = alloca [4 x i8], align 1
  %7 = alloca i32, align 4
  %8 = alloca i32, align 4
  store i32 %0, i32* %3, align 4
  call void @llvm.dbg.declare(metadata i32* %3, metadata !2844, metadata !336), !dbg !2845
  store i32* %1, i32** %4, align 4
  call void @llvm.dbg.declare(metadata i32** %4, metadata !2846, metadata !336), !dbg !2847
  call void @llvm.dbg.declare(metadata [30 x i8]* %5, metadata !2848, metadata !336), !dbg !2852
  call void @llvm.dbg.declare(metadata [4 x i8]* %6, metadata !2853, metadata !336), !dbg !2854
  call void @llvm.dbg.declare(metadata i32* %7, metadata !2855, metadata !336), !dbg !2856
  call void @llvm.dbg.declare(metadata i32* %8, metadata !2857, metadata !336), !dbg !2858
  %9 = load i32*, i32** %4, align 4, !dbg !2859
  %10 = icmp ne i32* %9, null, !dbg !2861
  br i1 %10, label %11, label %39, !dbg !2862

; <label>:11:                                     ; preds = %2
  %12 = getelementptr inbounds [30 x i8], [30 x i8]* %5, i32 0, i32 0, !dbg !2863
  %13 = load i32, i32* %3, align 4, !dbg !2865
  %14 = call i32 (i8*, i32, i8*, ...) @snprintf(i8* %12, i32 30, i8* getelementptr inbounds ([29 x i8], [29 x i8]* @.str.6.148, i32 0, i32 0), i32 %13) #7, !dbg !2866
  %15 = getelementptr inbounds [30 x i8], [30 x i8]* %5, i32 0, i32 0, !dbg !2867
  %16 = call i32 (i8*, i32, ...) @open(i8* %15, i32 0), !dbg !2868
  store i32 %16, i32* %7, align 4, !dbg !2869
  %17 = load i32, i32* %7, align 4, !dbg !2870
  %18 = icmp ne i32 -1, %17, !dbg !2872
  br i1 %18, label %19, label %35, !dbg !2873

; <label>:19:                                     ; preds = %11
  %20 = load i32, i32* %7, align 4, !dbg !2874
  %21 = getelementptr inbounds [4 x i8], [4 x i8]* %6, i32 0, i32 0, !dbg !2877
  %22 = call i32 @read(i32 %20, i8* %21, i32 3), !dbg !2878
  %23 = icmp ne i32 -1, %22, !dbg !2879
  br i1 %23, label %24, label %29, !dbg !2880

; <label>:24:                                     ; preds = %19
  %25 = getelementptr inbounds [4 x i8], [4 x i8]* %6, i32 0, i32 3, !dbg !2881
  store i8 0, i8* %25, align 1, !dbg !2883
  %26 = getelementptr inbounds [4 x i8], [4 x i8]* %6, i32 0, i32 0, !dbg !2884
  %27 = call i32 @atoi(i8* %26) #9, !dbg !2885
  %28 = load i32*, i32** %4, align 4, !dbg !2886
  store i32 %27, i32* %28, align 4, !dbg !2887
  store i32 0, i32* %8, align 4, !dbg !2888
  br label %32, !dbg !2889

; <label>:29:                                     ; preds = %19
  %30 = call i32* @__errno_location() #1, !dbg !2890
  %31 = load i32, i32* %30, align 4, !dbg !2890
  store i32 %31, i32* %8, align 4, !dbg !2891
  br label %32

; <label>:32:                                     ; preds = %29, %24
  %33 = load i32, i32* %7, align 4, !dbg !2892
  %34 = call i32 @close(i32 %33), !dbg !2893
  br label %38, !dbg !2894

; <label>:35:                                     ; preds = %11
  %36 = call i32* @__errno_location() #1, !dbg !2895
  %37 = load i32, i32* %36, align 4, !dbg !2895
  store i32 %37, i32* %8, align 4, !dbg !2896
  br label %38

; <label>:38:                                     ; preds = %35, %32
  br label %40, !dbg !2897

; <label>:39:                                     ; preds = %2
  store i32 22, i32* %8, align 4, !dbg !2898
  br label %40

; <label>:40:                                     ; preds = %39, %38
  %41 = load i32, i32* %8, align 4, !dbg !2899
  ret i32 %41, !dbg !2900
}

declare i32 @read(i32, i8*, i32) #5 section ".CODE_REGION_1_"

; Function Attrs: nounwind
define i32 @GPIO_write(i32, i32) #0 section ".CODE_REGION_1_" !dbg !2901 {
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca [2 x i8*], align 4
  %6 = alloca [30 x i8], align 1
  %7 = alloca i32, align 4
  %8 = alloca i32, align 4
  %9 = alloca i8*, align 4
  store i32 %0, i32* %3, align 4
  call void @llvm.dbg.declare(metadata i32* %3, metadata !2902, metadata !336), !dbg !2903
  store i32 %1, i32* %4, align 4
  call void @llvm.dbg.declare(metadata i32* %4, metadata !2904, metadata !336), !dbg !2905
  call void @llvm.dbg.declare(metadata [2 x i8*]* %5, metadata !2906, metadata !336), !dbg !2907
  %10 = bitcast [2 x i8*]* %5 to i8*, !dbg !2907
  call void @llvm.memcpy.p0i8.p0i8.i32(i8* %10, i8* bitcast ([2 x i8*]* @GPIO_write.s_values_str to i8*), i32 8, i32 4, i1 false), !dbg !2907
  call void @llvm.dbg.declare(metadata [30 x i8]* %6, metadata !2908, metadata !336), !dbg !2909
  call void @llvm.dbg.declare(metadata i32* %7, metadata !2910, metadata !336), !dbg !2911
  call void @llvm.dbg.declare(metadata i32* %8, metadata !2912, metadata !336), !dbg !2913
  %11 = getelementptr inbounds [30 x i8], [30 x i8]* %6, i32 0, i32 0, !dbg !2914
  %12 = load i32, i32* %3, align 4, !dbg !2915
  %13 = call i32 (i8*, i32, i8*, ...) @snprintf(i8* %11, i32 30, i8* getelementptr inbounds ([29 x i8], [29 x i8]* @.str.6.148, i32 0, i32 0), i32 %12) #7, !dbg !2916
  %14 = getelementptr inbounds [30 x i8], [30 x i8]* %6, i32 0, i32 0, !dbg !2917
  %15 = call i32 (i8*, i32, ...) @open(i8* %14, i32 1), !dbg !2918
  store i32 %15, i32* %7, align 4, !dbg !2919
  %16 = load i32, i32* %7, align 4, !dbg !2920
  %17 = icmp ne i32 -1, %16, !dbg !2922
  br i1 %17, label %18, label %37, !dbg !2923

; <label>:18:                                     ; preds = %2
  call void @llvm.dbg.declare(metadata i8** %9, metadata !2924, metadata !336), !dbg !2926
  %19 = load i32, i32* %4, align 4, !dbg !2927
  %20 = icmp ne i32 0, %19, !dbg !2928
  %21 = zext i1 %20 to i32, !dbg !2928
  %22 = getelementptr inbounds [2 x i8*], [2 x i8*]* %5, i32 0, i32 %21, !dbg !2929
  %23 = load i8*, i8** %22, align 4, !dbg !2929
  store i8* %23, i8** %9, align 4, !dbg !2930
  %24 = load i32, i32* %7, align 4, !dbg !2931
  %25 = load i8*, i8** %9, align 4, !dbg !2933
  %26 = load i8*, i8** %9, align 4, !dbg !2934
  %27 = call i32 @strlen(i8* %26) #9, !dbg !2935
  %28 = call i32 @write(i32 %24, i8* %25, i32 %27), !dbg !2936
  %29 = icmp ne i32 -1, %28, !dbg !2938
  br i1 %29, label %30, label %31, !dbg !2939

; <label>:30:                                     ; preds = %18
  store i32 0, i32* %8, align 4, !dbg !2940
  br label %34, !dbg !2941

; <label>:31:                                     ; preds = %18
  %32 = call i32* @__errno_location() #1, !dbg !2942
  %33 = load i32, i32* %32, align 4, !dbg !2942
  store i32 %33, i32* %8, align 4, !dbg !2943
  br label %34

; <label>:34:                                     ; preds = %31, %30
  %35 = load i32, i32* %7, align 4, !dbg !2944
  %36 = call i32 @close(i32 %35), !dbg !2945
  br label %40, !dbg !2946

; <label>:37:                                     ; preds = %2
  %38 = call i32* @__errno_location() #1, !dbg !2947
  %39 = load i32, i32* %38, align 4, !dbg !2947
  store i32 %39, i32* %8, align 4, !dbg !2948
  br label %40

; <label>:40:                                     ; preds = %37, %34
  %41 = load i32, i32* %8, align 4, !dbg !2949
  ret i32 %41, !dbg !2950
}

; Function Attrs: nounwind
define i32 @export_gpios() #0 section ".CODE_REGION_1_" !dbg !2951 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  call void @llvm.dbg.declare(metadata i32* %1, metadata !2952, metadata !336), !dbg !2953
  call void @llvm.dbg.declare(metadata i32* %2, metadata !2954, metadata !336), !dbg !2955
  %3 = call i32 @GPIO_export(i32 488), !dbg !2956
  store i32 %3, i32* %2, align 4, !dbg !2957
  %4 = load i32, i32* %2, align 4, !dbg !2958
  %5 = icmp eq i32 0, %4, !dbg !2960
  br i1 %5, label %6, label %65, !dbg !2961

; <label>:6:                                      ; preds = %0
  %7 = call i32 @GPIO_export(i32 489), !dbg !2962
  store i32 %7, i32* %2, align 4, !dbg !2964
  %8 = load i32, i32* %2, align 4, !dbg !2965
  %9 = icmp eq i32 0, %8, !dbg !2967
  br i1 %9, label %10, label %56, !dbg !2968

; <label>:10:                                     ; preds = %6
  %11 = call i32 @GPIO_export(i32 490), !dbg !2969
  store i32 %11, i32* %2, align 4, !dbg !2971
  %12 = load i32, i32* %2, align 4, !dbg !2972
  %13 = icmp eq i32 0, %12, !dbg !2974
  br i1 %13, label %14, label %46, !dbg !2975

; <label>:14:                                     ; preds = %10
  %15 = call i32 @GPIO_export(i32 491), !dbg !2976
  store i32 %15, i32* %2, align 4, !dbg !2978
  %16 = load i32, i32* %2, align 4, !dbg !2979
  %17 = icmp eq i32 0, %16, !dbg !2981
  br i1 %17, label %18, label %35, !dbg !2982

; <label>:18:                                     ; preds = %14
  %19 = call i32 @GPIO_export(i32 492), !dbg !2983
  store i32 %19, i32* %2, align 4, !dbg !2985
  %20 = load i32, i32* %2, align 4, !dbg !2986
  %21 = icmp eq i32 0, %20, !dbg !2988
  br i1 %21, label %22, label %23, !dbg !2989

; <label>:22:                                     ; preds = %18
  store i32 0, i32* %1, align 4, !dbg !2990
  br label %34, !dbg !2992

; <label>:23:                                     ; preds = %18
  %24 = load i32, i32* %2, align 4, !dbg !2993
  store i32 %24, i32* %1, align 4, !dbg !2995
  %25 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !2996
  %26 = load i32, i32* %2, align 4, !dbg !2996
  %27 = load i32, i32* %2, align 4, !dbg !2996
  %28 = call i8* @strerror(i32 %27) #7, !dbg !2996
  %29 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %25, i8* getelementptr inbounds ([54 x i8], [54 x i8]* @.str.9.153, i32 0, i32 0), i32 492, i32 %26, i8* %28), !dbg !2997
  %30 = call i32 @GPIO_unexport(i32 488), !dbg !2999
  %31 = call i32 @GPIO_unexport(i32 489), !dbg !3000
  %32 = call i32 @GPIO_unexport(i32 490), !dbg !3001
  %33 = call i32 @GPIO_unexport(i32 491), !dbg !3002
  br label %34

; <label>:34:                                     ; preds = %23, %22
  br label %45, !dbg !3003

; <label>:35:                                     ; preds = %14
  %36 = load i32, i32* %2, align 4, !dbg !3004
  store i32 %36, i32* %1, align 4, !dbg !3006
  %37 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !3007
  %38 = load i32, i32* %2, align 4, !dbg !3007
  %39 = load i32, i32* %2, align 4, !dbg !3007
  %40 = call i8* @strerror(i32 %39) #7, !dbg !3007
  %41 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %37, i8* getelementptr inbounds ([54 x i8], [54 x i8]* @.str.10.154, i32 0, i32 0), i32 491, i32 %38, i8* %40), !dbg !3008
  %42 = call i32 @GPIO_unexport(i32 488), !dbg !3010
  %43 = call i32 @GPIO_unexport(i32 489), !dbg !3011
  %44 = call i32 @GPIO_unexport(i32 490), !dbg !3012
  br label %45

; <label>:45:                                     ; preds = %35, %34
  br label %55, !dbg !3013

; <label>:46:                                     ; preds = %10
  %47 = load i32, i32* %2, align 4, !dbg !3014
  store i32 %47, i32* %1, align 4, !dbg !3016
  %48 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !3017
  %49 = load i32, i32* %2, align 4, !dbg !3017
  %50 = load i32, i32* %2, align 4, !dbg !3017
  %51 = call i8* @strerror(i32 %50) #7, !dbg !3017
  %52 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %48, i8* getelementptr inbounds ([54 x i8], [54 x i8]* @.str.11.155, i32 0, i32 0), i32 490, i32 %49, i8* %51), !dbg !3018
  %53 = call i32 @GPIO_unexport(i32 488), !dbg !3020
  %54 = call i32 @GPIO_unexport(i32 489), !dbg !3021
  br label %55

; <label>:55:                                     ; preds = %46, %45
  br label %64, !dbg !3022

; <label>:56:                                     ; preds = %6
  %57 = load i32, i32* %2, align 4, !dbg !3023
  store i32 %57, i32* %1, align 4, !dbg !3025
  %58 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !3026
  %59 = load i32, i32* %2, align 4, !dbg !3026
  %60 = load i32, i32* %2, align 4, !dbg !3026
  %61 = call i8* @strerror(i32 %60) #7, !dbg !3026
  %62 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %58, i8* getelementptr inbounds ([54 x i8], [54 x i8]* @.str.12.156, i32 0, i32 0), i32 489, i32 %59, i8* %61), !dbg !3027
  %63 = call i32 @GPIO_unexport(i32 488), !dbg !3029
  br label %64

; <label>:64:                                     ; preds = %56, %55
  br label %72, !dbg !3030

; <label>:65:                                     ; preds = %0
  %66 = load i32, i32* %2, align 4, !dbg !3031
  store i32 %66, i32* %1, align 4, !dbg !3033
  %67 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !3034
  %68 = load i32, i32* %2, align 4, !dbg !3034
  %69 = load i32, i32* %2, align 4, !dbg !3034
  %70 = call i8* @strerror(i32 %69) #7, !dbg !3034
  %71 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %67, i8* getelementptr inbounds ([49 x i8], [49 x i8]* @.str.13.157, i32 0, i32 0), i32 488, i32 %68, i8* %70), !dbg !3035
  br label %72

; <label>:72:                                     ; preds = %65, %64
  %73 = load i32, i32* %1, align 4, !dbg !3037
  ret i32 %73, !dbg !3038
}

; Function Attrs: nounwind
define i32 @configure_gpios() #0 section ".CODE_REGION_1_" !dbg !3039 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  call void @llvm.dbg.declare(metadata i32* %1, metadata !3040, metadata !336), !dbg !3041
  call void @llvm.dbg.declare(metadata i32* %2, metadata !3042, metadata !336), !dbg !3043
  store i32 488, i32* %2, align 4, !dbg !3044
  %3 = load i32, i32* %2, align 4, !dbg !3045
  %4 = call i32 @GPIO_direction(i32 %3, i32 0), !dbg !3046
  store i32 %4, i32* %1, align 4, !dbg !3047
  %5 = load i32, i32* %1, align 4, !dbg !3048
  %6 = icmp eq i32 0, %5, !dbg !3050
  br i1 %6, label %7, label %40, !dbg !3051

; <label>:7:                                      ; preds = %0
  store i32 489, i32* %2, align 4, !dbg !3052
  %8 = load i32, i32* %2, align 4, !dbg !3054
  %9 = call i32 @GPIO_direction(i32 %8, i32 1), !dbg !3055
  store i32 %9, i32* %1, align 4, !dbg !3056
  %10 = load i32, i32* %1, align 4, !dbg !3057
  %11 = icmp eq i32 0, %10, !dbg !3059
  br i1 %11, label %12, label %39, !dbg !3060

; <label>:12:                                     ; preds = %7
  %13 = load i32, i32* %2, align 4, !dbg !3061
  %14 = call i32 @GPIO_write(i32 %13, i32 1), !dbg !3063
  store i32 490, i32* %2, align 4, !dbg !3064
  %15 = load i32, i32* %2, align 4, !dbg !3065
  %16 = call i32 @GPIO_direction(i32 %15, i32 1), !dbg !3066
  store i32 %16, i32* %1, align 4, !dbg !3067
  %17 = load i32, i32* %1, align 4, !dbg !3068
  %18 = icmp eq i32 0, %17, !dbg !3070
  br i1 %18, label %19, label %38, !dbg !3071

; <label>:19:                                     ; preds = %12
  %20 = load i32, i32* %2, align 4, !dbg !3072
  %21 = call i32 @GPIO_write(i32 %20, i32 1), !dbg !3074
  store i32 491, i32* %2, align 4, !dbg !3075
  %22 = load i32, i32* %2, align 4, !dbg !3076
  %23 = call i32 @GPIO_direction(i32 %22, i32 1), !dbg !3077
  store i32 %23, i32* %1, align 4, !dbg !3078
  %24 = load i32, i32* %1, align 4, !dbg !3079
  %25 = icmp eq i32 0, %24, !dbg !3081
  br i1 %25, label %26, label %37, !dbg !3082

; <label>:26:                                     ; preds = %19
  %27 = load i32, i32* %2, align 4, !dbg !3083
  %28 = call i32 @GPIO_write(i32 %27, i32 1), !dbg !3085
  store i32 492, i32* %2, align 4, !dbg !3086
  %29 = load i32, i32* %2, align 4, !dbg !3087
  %30 = call i32 @GPIO_direction(i32 %29, i32 1), !dbg !3088
  store i32 %30, i32* %1, align 4, !dbg !3089
  %31 = load i32, i32* %1, align 4, !dbg !3090
  %32 = icmp eq i32 0, %31, !dbg !3092
  br i1 %32, label %33, label %36, !dbg !3093

; <label>:33:                                     ; preds = %26
  %34 = load i32, i32* %2, align 4, !dbg !3094
  %35 = call i32 @GPIO_write(i32 %34, i32 1), !dbg !3095
  br label %36, !dbg !3095

; <label>:36:                                     ; preds = %33, %26
  br label %37, !dbg !3096

; <label>:37:                                     ; preds = %36, %19
  br label %38, !dbg !3097

; <label>:38:                                     ; preds = %37, %12
  br label %39, !dbg !3098

; <label>:39:                                     ; preds = %38, %7
  br label %40, !dbg !3099

; <label>:40:                                     ; preds = %39, %0
  %41 = load i32, i32* %1, align 4, !dbg !3100
  %42 = icmp ne i32 %41, 0, !dbg !3102
  br i1 %42, label %43, label %50, !dbg !3103

; <label>:43:                                     ; preds = %40
  %44 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !3104
  %45 = load i32, i32* %2, align 4, !dbg !3104
  %46 = load i32, i32* %1, align 4, !dbg !3104
  %47 = load i32, i32* %1, align 4, !dbg !3104
  %48 = call i8* @strerror(i32 %47) #7, !dbg !3104
  %49 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %44, i8* getelementptr inbounds ([53 x i8], [53 x i8]* @.str.14.160, i32 0, i32 0), i32 %45, i32 %46, i8* %48), !dbg !3105
  br label %50, !dbg !3104

; <label>:50:                                     ; preds = %43, %40
  %51 = load i32, i32* %1, align 4, !dbg !3107
  ret i32 %51, !dbg !3108
}

; Function Attrs: nounwind
define i32 @unexport_gpios() #0 section ".CODE_REGION_2_" !dbg !3109 {
  %1 = alloca i32, align 4
  call void @llvm.dbg.declare(metadata i32* %1, metadata !3110, metadata !336), !dbg !3111
  store i32 0, i32* %1, align 4, !dbg !3112
  call void @__AMI_fake_direct_transfer(), !dbg !3113
  %2 = call i32 @GPIO_unexport(i32 488), !dbg !3113
  %3 = load i32, i32* %1, align 4, !dbg !3114
  %4 = or i32 %3, %2, !dbg !3114
  store i32 %4, i32* %1, align 4, !dbg !3114
  call void @__AMI_fake_direct_transfer(), !dbg !3115
  %5 = call i32 @GPIO_unexport(i32 489), !dbg !3115
  %6 = load i32, i32* %1, align 4, !dbg !3116
  %7 = or i32 %6, %5, !dbg !3116
  store i32 %7, i32* %1, align 4, !dbg !3116
  call void @__AMI_fake_direct_transfer(), !dbg !3117
  %8 = call i32 @GPIO_unexport(i32 490), !dbg !3117
  %9 = load i32, i32* %1, align 4, !dbg !3118
  %10 = or i32 %9, %8, !dbg !3118
  store i32 %10, i32* %1, align 4, !dbg !3118
  call void @__AMI_fake_direct_transfer(), !dbg !3119
  %11 = call i32 @GPIO_unexport(i32 491), !dbg !3119
  %12 = load i32, i32* %1, align 4, !dbg !3120
  %13 = or i32 %12, %11, !dbg !3120
  store i32 %13, i32* %1, align 4, !dbg !3120
  call void @__AMI_fake_direct_transfer(), !dbg !3121
  %14 = call i32 @GPIO_unexport(i32 492), !dbg !3121
  %15 = load i32, i32* %1, align 4, !dbg !3122
  %16 = or i32 %15, %14, !dbg !3122
  store i32 %16, i32* %1, align 4, !dbg !3122
  %17 = load i32, i32* %1, align 4, !dbg !3123
  %18 = icmp ne i32 %17, 0, !dbg !3125
  br i1 %18, label %19, label %25, !dbg !3126

; <label>:19:                                     ; preds = %0
  %20 = load %struct._IO_FILE*, %struct._IO_FILE** @Log_file_handle, align 4, !dbg !3127
  %21 = load i32, i32* %1, align 4, !dbg !3127
  %22 = load i32, i32* %1, align 4, !dbg !3127
  %23 = call i8* @strerror(i32 %22) #7, !dbg !3127
  call void @__AMI_fake_direct_transfer(), !dbg !3128
  %24 = call i32 (%struct._IO_FILE*, i8*, ...) @msg_printf(%struct._IO_FILE* %20, i8* getelementptr inbounds ([42 x i8], [42 x i8]* @.str.15.163, i32 0, i32 0), i32 %21, i8* %23), !dbg !3128
  br label %25, !dbg !3127

; <label>:25:                                     ; preds = %19, %0
  %26 = load i32, i32* %1, align 4, !dbg !3130
  ret i32 %26, !dbg !3131
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
!37 = distinct !DIGlobalVariable(name: "recording_flag", scope: !29, file: !30, line: 153, type: !12, isLocal: false, isDefinition: true, variable: i32* @recording_flag)
!38 = distinct !DIGlobalVariable(name: "recording_cnt", scope: !29, file: !30, line: 154, type: !12, isLocal: false, isDefinition: true, variable: i32* @recording_cnt)
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
!602 = !DILocation(line: 73, column: 9, scope: !599)
!603 = !DILocation(line: 74, column: 6, scope: !589)
!604 = !DILocation(line: 75, column: 11, scope: !567)
!605 = !DILocation(line: 75, column: 4, scope: !567)
!606 = distinct !DISubprogram(name: "polling_thread", scope: !30, file: !30, line: 78, type: !607, isLocal: false, isDefinition: true, scopeLine: 79, flags: DIFlagPrototyped, isOptimized: false, unit: !29, variables: !2)
!607 = !DISubroutineType(types: !608)
!608 = !{!32, !609}
!609 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !24, size: 32, align: 32)
!610 = !DILocalVariable(name: "exit_polling", arg: 1, scope: !606, file: !30, line: 78, type: !609)
!611 = !DILocation(line: 78, column: 36, scope: !606)
!612 = !DILocalVariable(name: "ret_err", scope: !606, file: !30, line: 80, type: !12)
!613 = !DILocation(line: 80, column: 47, scope: !606)
!614 = !DILocation(line: 80, column: 4, scope: !606)
!615 = !DILocalVariable(name: "read_err", scope: !606, file: !30, line: 81, type: !12)
!616 = !DILocation(line: 81, column: 47, scope: !606)
!617 = !DILocation(line: 81, column: 4, scope: !606)
!618 = !DILocalVariable(name: "curr_pir_value", scope: !606, file: !30, line: 82, type: !12)
!619 = !DILocation(line: 82, column: 47, scope: !606)
!620 = !DILocation(line: 82, column: 4, scope: !606)
!621 = !DILocalVariable(name: "last_pir_value", scope: !606, file: !30, line: 83, type: !12)
!622 = !DILocation(line: 83, column: 47, scope: !606)
!623 = !DILocation(line: 83, column: 4, scope: !606)
!624 = !DILocalVariable(name: "pir_perman_counter", scope: !606, file: !30, line: 84, type: !12)
!625 = !DILocation(line: 84, column: 47, scope: !606)
!626 = !DILocation(line: 84, column: 4, scope: !606)
!627 = !DILocation(line: 98, column: 4, scope: !606)
!628 = !DILocation(line: 100, column: 13, scope: !606)
!629 = !DILocation(line: 101, column: 23, scope: !606)
!630 = !DILocation(line: 102, column: 19, scope: !606)
!631 = !DILocalVariable(name: "i", scope: !606, file: !30, line: 103, type: !12)
!632 = !DILocation(line: 103, column: 8, scope: !606)
!633 = !DILocation(line: 104, column: 4, scope: !606)
!634 = !DILocation(line: 104, column: 11, scope: !635)
!635 = !DILexicalBlockFile(scope: !606, file: !30, discriminator: 1)
!636 = !DILocation(line: 104, column: 14, scope: !635)
!637 = !DILocation(line: 104, column: 4, scope: !635)
!638 = !DILocation(line: 108, column: 17, scope: !639)
!639 = distinct !DILexicalBlock(scope: !606, file: !30, line: 105, column: 6)
!640 = !DILocation(line: 108, column: 15, scope: !639)
!641 = !DILocation(line: 109, column: 15, scope: !639)
!642 = !DILocation(line: 110, column: 25, scope: !639)
!643 = !DILocation(line: 110, column: 27, scope: !639)
!644 = !DILocation(line: 110, column: 31, scope: !639)
!645 = !DILocation(line: 110, column: 24, scope: !639)
!646 = !DILocation(line: 110, column: 22, scope: !639)
!647 = !DILocation(line: 112, column: 10, scope: !648)
!648 = distinct !DILexicalBlock(scope: !639, file: !30, line: 112, column: 10)
!649 = !DILocation(line: 112, column: 18, scope: !648)
!650 = !DILocation(line: 112, column: 10, scope: !639)
!651 = !DILocation(line: 114, column: 13, scope: !652)
!652 = distinct !DILexicalBlock(scope: !653, file: !30, line: 114, column: 13)
!653 = distinct !DILexicalBlock(scope: !648, file: !30, line: 113, column: 9)
!654 = !DILocation(line: 114, column: 31, scope: !652)
!655 = !DILocation(line: 114, column: 28, scope: !652)
!656 = !DILocation(line: 114, column: 13, scope: !653)
!657 = !DILocation(line: 116, column: 16, scope: !658)
!658 = distinct !DILexicalBlock(scope: !659, file: !30, line: 116, column: 16)
!659 = distinct !DILexicalBlock(scope: !652, file: !30, line: 115, column: 12)
!660 = !DILocation(line: 116, column: 31, scope: !658)
!661 = !DILocation(line: 116, column: 16, scope: !659)
!662 = !DILocation(line: 118, column: 16, scope: !663)
!663 = distinct !DILexicalBlock(scope: !658, file: !30, line: 117, column: 15)
!664 = !DILocation(line: 120, column: 15, scope: !663)
!665 = !DILocation(line: 121, column: 30, scope: !659)
!666 = !DILocation(line: 121, column: 28, scope: !659)
!667 = !DILocation(line: 122, column: 12, scope: !659)
!668 = !DILocation(line: 124, column: 13, scope: !669)
!669 = distinct !DILexicalBlock(scope: !653, file: !30, line: 124, column: 13)
!670 = !DILocation(line: 124, column: 28, scope: !669)
!671 = !DILocation(line: 124, column: 13, scope: !653)
!672 = !DILocation(line: 125, column: 32, scope: !669)
!673 = !DILocation(line: 125, column: 13, scope: !669)
!674 = !DILocation(line: 127, column: 9, scope: !653)
!675 = !DILocation(line: 130, column: 13, scope: !676)
!676 = distinct !DILexicalBlock(scope: !677, file: !30, line: 130, column: 13)
!677 = distinct !DILexicalBlock(scope: !648, file: !30, line: 129, column: 9)
!678 = !DILocation(line: 130, column: 21, scope: !676)
!679 = !DILocation(line: 130, column: 13, scope: !677)
!680 = !DILocation(line: 132, column: 13, scope: !681)
!681 = distinct !DILexicalBlock(scope: !676, file: !30, line: 131, column: 12)
!682 = !DILocation(line: 132, column: 13, scope: !683)
!683 = !DILexicalBlockFile(scope: !681, file: !30, discriminator: 1)
!684 = !DILocation(line: 133, column: 22, scope: !681)
!685 = !DILocation(line: 133, column: 21, scope: !681)
!686 = !DILocation(line: 134, column: 12, scope: !681)
!687 = !DILocation(line: 137, column: 10, scope: !688)
!688 = distinct !DILexicalBlock(scope: !639, file: !30, line: 137, column: 10)
!689 = !DILocation(line: 137, column: 29, scope: !688)
!690 = !DILocation(line: 137, column: 10, scope: !639)
!691 = !DILocation(line: 138, column: 28, scope: !688)
!692 = !DILocation(line: 138, column: 10, scope: !688)
!693 = !DILocation(line: 104, column: 4, scope: !694)
!694 = !DILexicalBlockFile(scope: !606, file: !30, discriminator: 2)
!695 = distinct !{!695, !633}
!696 = !DILocation(line: 145, column: 4, scope: !606)
!697 = !DILocation(line: 146, column: 29, scope: !606)
!698 = !DILocation(line: 146, column: 11, scope: !606)
!699 = !DILocation(line: 146, column: 4, scope: !606)
!700 = distinct !DISubprogram(name: "init_polling", scope: !30, file: !30, line: 157, type: !701, isLocal: false, isDefinition: true, scopeLine: 158, flags: DIFlagPrototyped, isOptimized: false, unit: !29, variables: !2)
!701 = !DISubroutineType(types: !702)
!702 = !{!12, !609, !18}
!703 = !DILocalVariable(name: "exit_polling", arg: 1, scope: !700, file: !30, line: 157, type: !609)
!704 = !DILocation(line: 157, column: 32, scope: !700)
!705 = !DILocalVariable(name: "msg_info_fmt", arg: 2, scope: !700, file: !30, line: 157, type: !18)
!706 = !DILocation(line: 157, column: 52, scope: !700)
!707 = !DILocation(line: 159, column: 3, scope: !700)
!708 = !DILocation(line: 161, column: 17, scope: !700)
!709 = !DILocalVariable(name: "ret_err", scope: !700, file: !30, line: 162, type: !12)
!710 = !DILocation(line: 162, column: 46, scope: !700)
!711 = !DILocation(line: 162, column: 3, scope: !700)
!712 = !DILocalVariable(name: "start", scope: !700, file: !30, line: 163, type: !42)
!713 = !DILocation(line: 163, column: 17, scope: !700)
!714 = !DILocalVariable(name: "end", scope: !700, file: !30, line: 163, type: !42)
!715 = !DILocation(line: 163, column: 24, scope: !700)
!716 = !DILocation(line: 165, column: 11, scope: !700)
!717 = !DILocation(line: 165, column: 9, scope: !700)
!718 = !DILocation(line: 168, column: 12, scope: !700)
!719 = !DILocation(line: 168, column: 11, scope: !700)
!720 = !DILocation(line: 169, column: 11, scope: !700)
!721 = !DILocation(line: 170, column: 7, scope: !722)
!722 = distinct !DILexicalBlock(scope: !700, file: !30, line: 170, column: 7)
!723 = !DILocation(line: 170, column: 14, scope: !722)
!724 = !DILocation(line: 170, column: 7, scope: !700)
!725 = !DILocation(line: 172, column: 15, scope: !726)
!726 = distinct !DILexicalBlock(scope: !722, file: !30, line: 171, column: 6)
!727 = !DILocation(line: 172, column: 14, scope: !726)
!728 = !DILocation(line: 173, column: 15, scope: !726)
!729 = !DILocation(line: 174, column: 10, scope: !730)
!730 = distinct !DILexicalBlock(scope: !726, file: !30, line: 174, column: 10)
!731 = !DILocation(line: 174, column: 17, scope: !730)
!732 = !DILocation(line: 174, column: 10, scope: !726)
!733 = !DILocation(line: 176, column: 18, scope: !734)
!734 = distinct !DILexicalBlock(scope: !730, file: !30, line: 175, column: 9)
!735 = !DILocation(line: 176, column: 17, scope: !734)
!736 = !DILocation(line: 177, column: 17, scope: !734)
!737 = !DILocation(line: 178, column: 13, scope: !738)
!738 = distinct !DILexicalBlock(scope: !734, file: !30, line: 178, column: 13)
!739 = !DILocation(line: 178, column: 21, scope: !738)
!740 = !DILocation(line: 178, column: 13, scope: !734)
!741 = !DILocation(line: 180, column: 28, scope: !742)
!742 = distinct !DILexicalBlock(scope: !738, file: !30, line: 179, column: 12)
!743 = !DILocation(line: 187, column: 28, scope: !742)
!744 = !DILocation(line: 187, column: 13, scope: !742)
!745 = !DILocation(line: 188, column: 16, scope: !746)
!746 = distinct !DILexicalBlock(scope: !742, file: !30, line: 188, column: 16)
!747 = !DILocation(line: 188, column: 24, scope: !746)
!748 = !DILocation(line: 188, column: 16, scope: !742)
!749 = !DILocation(line: 189, column: 16, scope: !746)
!750 = !DILocation(line: 191, column: 16, scope: !746)
!751 = !DILocation(line: 191, column: 16, scope: !752)
!752 = !DILexicalBlockFile(scope: !746, file: !30, discriminator: 1)
!753 = !DILocation(line: 193, column: 12, scope: !742)
!754 = !DILocation(line: 194, column: 9, scope: !734)
!755 = !DILocation(line: 195, column: 6, scope: !726)
!756 = !DILocation(line: 198, column: 19, scope: !700)
!757 = !DILocation(line: 199, column: 24, scope: !700)
!758 = !DILocation(line: 200, column: 4, scope: !700)
!759 = !DILocation(line: 201, column: 11, scope: !700)
!760 = !DILocation(line: 201, column: 9, scope: !700)
!761 = !DILocation(line: 202, column: 56, scope: !700)
!762 = !DILocation(line: 202, column: 62, scope: !700)
!763 = !DILocation(line: 202, column: 60, scope: !700)
!764 = !DILocation(line: 202, column: 5, scope: !700)
!765 = !DILocation(line: 204, column: 11, scope: !700)
!766 = !DILocation(line: 204, column: 4, scope: !700)
!767 = distinct !DISubprogram(name: "wait_polling_end", scope: !30, file: !30, line: 207, type: !346, isLocal: false, isDefinition: true, scopeLine: 208, flags: DIFlagPrototyped, isOptimized: false, unit: !29, variables: !2)
!768 = !DILocalVariable(name: "ret_err", scope: !767, file: !30, line: 209, type: !12)
!769 = !DILocation(line: 209, column: 8, scope: !767)
!770 = !DILocation(line: 210, column: 27, scope: !767)
!771 = !DILocation(line: 210, column: 14, scope: !767)
!772 = !DILocation(line: 210, column: 12, scope: !767)
!773 = !DILocation(line: 211, column: 7, scope: !774)
!774 = distinct !DILexicalBlock(scope: !767, file: !30, line: 211, column: 7)
!775 = !DILocation(line: 211, column: 15, scope: !774)
!776 = !DILocation(line: 211, column: 7, scope: !767)
!777 = !DILocation(line: 212, column: 7, scope: !774)
!778 = !DILocation(line: 214, column: 7, scope: !774)
!779 = !DILocation(line: 215, column: 4, scope: !767)
!780 = !DILocation(line: 216, column: 11, scope: !767)
!781 = !DILocation(line: 216, column: 4, scope: !767)
!782 = distinct !DISubprogram(name: "pushover_init", scope: !48, file: !48, line: 50, type: !568, isLocal: false, isDefinition: true, scopeLine: 51, flags: DIFlagPrototyped, isOptimized: false, unit: !47, variables: !2)
!783 = !DILocalVariable(name: "conf_filename", arg: 1, scope: !782, file: !48, line: 50, type: !18)
!784 = !DILocation(line: 50, column: 25, scope: !782)
!785 = !DILocalVariable(name: "ret_error", scope: !782, file: !48, line: 52, type: !12)
!786 = !DILocation(line: 52, column: 8, scope: !782)
!787 = !DILocalVariable(name: "conf_fd", scope: !782, file: !48, line: 53, type: !788)
!788 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !789, size: 32, align: 32)
!789 = !DIDerivedType(tag: DW_TAG_typedef, name: "FILE", file: !263, line: 48, baseType: !790)
!790 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "_IO_FILE", file: !265, line: 241, size: 1216, align: 64, elements: !791)
!791 = !{!792, !793, !794, !795, !796, !797, !798, !799, !800, !801, !802, !803, !804, !812, !813, !814, !815, !816, !817, !818, !819, !820, !821, !822, !823, !824, !825, !826, !827}
!792 = !DIDerivedType(tag: DW_TAG_member, name: "_flags", scope: !790, file: !265, line: 242, baseType: !12, size: 32, align: 32)
!793 = !DIDerivedType(tag: DW_TAG_member, name: "_IO_read_ptr", scope: !790, file: !265, line: 247, baseType: !18, size: 32, align: 32, offset: 32)
!794 = !DIDerivedType(tag: DW_TAG_member, name: "_IO_read_end", scope: !790, file: !265, line: 248, baseType: !18, size: 32, align: 32, offset: 64)
!795 = !DIDerivedType(tag: DW_TAG_member, name: "_IO_read_base", scope: !790, file: !265, line: 249, baseType: !18, size: 32, align: 32, offset: 96)
!796 = !DIDerivedType(tag: DW_TAG_member, name: "_IO_write_base", scope: !790, file: !265, line: 250, baseType: !18, size: 32, align: 32, offset: 128)
!797 = !DIDerivedType(tag: DW_TAG_member, name: "_IO_write_ptr", scope: !790, file: !265, line: 251, baseType: !18, size: 32, align: 32, offset: 160)
!798 = !DIDerivedType(tag: DW_TAG_member, name: "_IO_write_end", scope: !790, file: !265, line: 252, baseType: !18, size: 32, align: 32, offset: 192)
!799 = !DIDerivedType(tag: DW_TAG_member, name: "_IO_buf_base", scope: !790, file: !265, line: 253, baseType: !18, size: 32, align: 32, offset: 224)
!800 = !DIDerivedType(tag: DW_TAG_member, name: "_IO_buf_end", scope: !790, file: !265, line: 254, baseType: !18, size: 32, align: 32, offset: 256)
!801 = !DIDerivedType(tag: DW_TAG_member, name: "_IO_save_base", scope: !790, file: !265, line: 256, baseType: !18, size: 32, align: 32, offset: 288)
!802 = !DIDerivedType(tag: DW_TAG_member, name: "_IO_backup_base", scope: !790, file: !265, line: 257, baseType: !18, size: 32, align: 32, offset: 320)
!803 = !DIDerivedType(tag: DW_TAG_member, name: "_IO_save_end", scope: !790, file: !265, line: 258, baseType: !18, size: 32, align: 32, offset: 352)
!804 = !DIDerivedType(tag: DW_TAG_member, name: "_markers", scope: !790, file: !265, line: 260, baseType: !805, size: 32, align: 32, offset: 384)
!805 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !806, size: 32, align: 32)
!806 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "_IO_marker", file: !265, line: 156, size: 96, align: 32, elements: !807)
!807 = !{!808, !809, !811}
!808 = !DIDerivedType(tag: DW_TAG_member, name: "_next", scope: !806, file: !265, line: 157, baseType: !805, size: 32, align: 32)
!809 = !DIDerivedType(tag: DW_TAG_member, name: "_sbuf", scope: !806, file: !265, line: 158, baseType: !810, size: 32, align: 32, offset: 32)
!810 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !790, size: 32, align: 32)
!811 = !DIDerivedType(tag: DW_TAG_member, name: "_pos", scope: !806, file: !265, line: 162, baseType: !12, size: 32, align: 32, offset: 64)
!812 = !DIDerivedType(tag: DW_TAG_member, name: "_chain", scope: !790, file: !265, line: 262, baseType: !810, size: 32, align: 32, offset: 416)
!813 = !DIDerivedType(tag: DW_TAG_member, name: "_fileno", scope: !790, file: !265, line: 264, baseType: !12, size: 32, align: 32, offset: 448)
!814 = !DIDerivedType(tag: DW_TAG_member, name: "_flags2", scope: !790, file: !265, line: 268, baseType: !12, size: 32, align: 32, offset: 480)
!815 = !DIDerivedType(tag: DW_TAG_member, name: "_old_offset", scope: !790, file: !265, line: 270, baseType: !291, size: 32, align: 32, offset: 512)
!816 = !DIDerivedType(tag: DW_TAG_member, name: "_cur_column", scope: !790, file: !265, line: 274, baseType: !70, size: 16, align: 16, offset: 544)
!817 = !DIDerivedType(tag: DW_TAG_member, name: "_vtable_offset", scope: !790, file: !265, line: 275, baseType: !294, size: 8, align: 8, offset: 560)
!818 = !DIDerivedType(tag: DW_TAG_member, name: "_shortbuf", scope: !790, file: !265, line: 276, baseType: !296, size: 8, align: 8, offset: 568)
!819 = !DIDerivedType(tag: DW_TAG_member, name: "_lock", scope: !790, file: !265, line: 280, baseType: !300, size: 32, align: 32, offset: 576)
!820 = !DIDerivedType(tag: DW_TAG_member, name: "_offset", scope: !790, file: !265, line: 289, baseType: !303, size: 64, align: 64, offset: 640)
!821 = !DIDerivedType(tag: DW_TAG_member, name: "__pad1", scope: !790, file: !265, line: 297, baseType: !32, size: 32, align: 32, offset: 704)
!822 = !DIDerivedType(tag: DW_TAG_member, name: "__pad2", scope: !790, file: !265, line: 298, baseType: !32, size: 32, align: 32, offset: 736)
!823 = !DIDerivedType(tag: DW_TAG_member, name: "__pad3", scope: !790, file: !265, line: 299, baseType: !32, size: 32, align: 32, offset: 768)
!824 = !DIDerivedType(tag: DW_TAG_member, name: "__pad4", scope: !790, file: !265, line: 300, baseType: !32, size: 32, align: 32, offset: 800)
!825 = !DIDerivedType(tag: DW_TAG_member, name: "__pad5", scope: !790, file: !265, line: 302, baseType: !311, size: 32, align: 32, offset: 832)
!826 = !DIDerivedType(tag: DW_TAG_member, name: "_mode", scope: !790, file: !265, line: 303, baseType: !12, size: 32, align: 32, offset: 864)
!827 = !DIDerivedType(tag: DW_TAG_member, name: "_unused2", scope: !790, file: !265, line: 305, baseType: !315, size: 320, align: 8, offset: 896)
!828 = !DILocation(line: 53, column: 10, scope: !782)
!829 = !DILocalVariable(name: "full_conf_filename", scope: !782, file: !48, line: 54, type: !830)
!830 = !DICompositeType(tag: DW_TAG_array_type, baseType: !19, size: 32776, align: 8, elements: !831)
!831 = !{!832}
!832 = !DISubrange(count: 4097)
!833 = !DILocation(line: 54, column: 9, scope: !782)
!834 = !DILocation(line: 56, column: 14, scope: !835)
!835 = distinct !DILexicalBlock(scope: !782, file: !48, line: 56, column: 7)
!836 = !DILocation(line: 56, column: 7, scope: !835)
!837 = !DILocation(line: 56, column: 28, scope: !835)
!838 = !DILocation(line: 56, column: 7, scope: !782)
!839 = !DILocation(line: 57, column: 7, scope: !835)
!840 = !DILocation(line: 59, column: 7, scope: !841)
!841 = distinct !DILexicalBlock(scope: !782, file: !48, line: 59, column: 7)
!842 = !DILocation(line: 59, column: 24, scope: !841)
!843 = !DILocation(line: 59, column: 7, scope: !782)
!844 = !DILocation(line: 61, column: 41, scope: !845)
!845 = distinct !DILexicalBlock(scope: !841, file: !48, line: 60, column: 6)
!846 = !DILocation(line: 61, column: 19, scope: !845)
!847 = !DILocation(line: 61, column: 17, scope: !845)
!848 = !DILocation(line: 62, column: 10, scope: !849)
!849 = distinct !DILexicalBlock(scope: !845, file: !48, line: 62, column: 10)
!850 = !DILocation(line: 62, column: 20, scope: !849)
!851 = !DILocation(line: 62, column: 10, scope: !845)
!852 = !DILocation(line: 64, column: 20, scope: !853)
!853 = distinct !DILexicalBlock(scope: !854, file: !48, line: 64, column: 13)
!854 = distinct !DILexicalBlock(scope: !849, file: !48, line: 63, column: 9)
!855 = !DILocation(line: 64, column: 13, scope: !853)
!856 = !DILocation(line: 64, column: 47, scope: !853)
!857 = !DILocation(line: 64, column: 40, scope: !858)
!858 = !DILexicalBlockFile(scope: !853, file: !48, discriminator: 1)
!859 = !DILocation(line: 64, column: 39, scope: !853)
!860 = !DILocation(line: 64, column: 62, scope: !853)
!861 = !DILocation(line: 64, column: 13, scope: !854)
!862 = !DILocation(line: 65, column: 20, scope: !853)
!863 = !DILocation(line: 65, column: 40, scope: !853)
!864 = !DILocation(line: 65, column: 13, scope: !853)
!865 = !DILocation(line: 67, column: 20, scope: !853)
!866 = !DILocation(line: 67, column: 40, scope: !853)
!867 = !DILocation(line: 67, column: 13, scope: !853)
!868 = !DILocation(line: 68, column: 9, scope: !854)
!869 = !DILocation(line: 71, column: 10, scope: !870)
!870 = distinct !DILexicalBlock(scope: !849, file: !48, line: 70, column: 9)
!871 = !DILocation(line: 72, column: 17, scope: !870)
!872 = !DILocation(line: 72, column: 37, scope: !870)
!873 = !DILocation(line: 72, column: 10, scope: !870)
!874 = !DILocation(line: 74, column: 6, scope: !845)
!875 = !DILocation(line: 76, column: 14, scope: !841)
!876 = !DILocation(line: 76, column: 34, scope: !841)
!877 = !DILocation(line: 76, column: 7, scope: !841)
!878 = !DILocation(line: 78, column: 18, scope: !782)
!879 = !DILocation(line: 78, column: 12, scope: !782)
!880 = !DILocation(line: 78, column: 11, scope: !782)
!881 = !DILocation(line: 79, column: 7, scope: !882)
!882 = distinct !DILexicalBlock(scope: !782, file: !48, line: 79, column: 7)
!883 = !DILocation(line: 79, column: 15, scope: !882)
!884 = !DILocation(line: 79, column: 7, scope: !782)
!885 = !DILocalVariable(name: "server_url", scope: !886, file: !48, line: 81, type: !887)
!886 = distinct !DILexicalBlock(scope: !882, file: !48, line: 80, column: 6)
!887 = !DICompositeType(tag: DW_TAG_array_type, baseType: !19, size: 16672, align: 8, elements: !888)
!888 = !{!889}
!889 = !DISubrange(count: 2084)
!890 = !DILocation(line: 81, column: 12, scope: !886)
!891 = !DILocation(line: 85, column: 7, scope: !886)
!892 = !DILocation(line: 85, column: 20, scope: !886)
!893 = !DILocation(line: 87, column: 18, scope: !886)
!894 = !DILocation(line: 88, column: 17, scope: !886)
!895 = !DILocation(line: 89, column: 7, scope: !886)
!896 = !DILocation(line: 91, column: 17, scope: !886)
!897 = !DILocation(line: 92, column: 7, scope: !886)
!898 = !DILocation(line: 92, column: 19, scope: !899)
!899 = !DILexicalBlockFile(scope: !886, file: !48, discriminator: 1)
!900 = !DILocation(line: 92, column: 14, scope: !899)
!901 = !DILocation(line: 92, column: 28, scope: !899)
!902 = !DILocation(line: 92, column: 31, scope: !903)
!903 = !DILexicalBlockFile(scope: !886, file: !48, discriminator: 2)
!904 = !DILocation(line: 92, column: 41, scope: !903)
!905 = !DILocation(line: 92, column: 7, scope: !906)
!906 = !DILexicalBlockFile(scope: !886, file: !48, discriminator: 3)
!907 = !DILocation(line: 97, column: 20, scope: !908)
!908 = distinct !DILexicalBlock(scope: !909, file: !48, line: 97, column: 13)
!909 = distinct !DILexicalBlock(scope: !886, file: !48, line: 93, column: 9)
!910 = !DILocation(line: 97, column: 76, scope: !908)
!911 = !DILocation(line: 97, column: 13, scope: !908)
!912 = !DILocation(line: 97, column: 88, scope: !908)
!913 = !DILocation(line: 97, column: 93, scope: !908)
!914 = !DILocation(line: 98, column: 20, scope: !908)
!915 = !DILocation(line: 98, column: 13, scope: !908)
!916 = !DILocation(line: 98, column: 89, scope: !908)
!917 = !DILocation(line: 98, column: 94, scope: !908)
!918 = !DILocation(line: 99, column: 20, scope: !908)
!919 = !DILocation(line: 99, column: 13, scope: !908)
!920 = !DILocation(line: 99, column: 87, scope: !908)
!921 = !DILocation(line: 97, column: 13, scope: !922)
!922 = !DILexicalBlockFile(scope: !909, file: !48, discriminator: 1)
!923 = !DILocation(line: 101, column: 13, scope: !924)
!924 = distinct !DILexicalBlock(scope: !908, file: !48, line: 100, column: 12)
!925 = !DILocation(line: 102, column: 23, scope: !924)
!926 = !DILocation(line: 103, column: 12, scope: !924)
!927 = !DILocation(line: 92, column: 7, scope: !928)
!928 = !DILexicalBlockFile(scope: !886, file: !48, discriminator: 4)
!929 = distinct !{!929, !897}
!930 = !DILocation(line: 105, column: 10, scope: !931)
!931 = distinct !DILexicalBlock(scope: !886, file: !48, line: 105, column: 10)
!932 = !DILocation(line: 105, column: 20, scope: !931)
!933 = !DILocation(line: 105, column: 10, scope: !886)
!934 = !DILocation(line: 107, column: 20, scope: !935)
!935 = distinct !DILexicalBlock(scope: !936, file: !48, line: 107, column: 13)
!936 = distinct !DILexicalBlock(scope: !931, file: !48, line: 106, column: 9)
!937 = !DILocation(line: 107, column: 13, scope: !935)
!938 = !DILocation(line: 107, column: 32, scope: !935)
!939 = !DILocation(line: 107, column: 13, scope: !936)
!940 = !DILocation(line: 109, column: 16, scope: !941)
!941 = distinct !DILexicalBlock(scope: !942, file: !48, line: 109, column: 16)
!942 = distinct !DILexicalBlock(scope: !935, file: !48, line: 108, column: 12)
!943 = !DILocation(line: 109, column: 33, scope: !941)
!944 = !DILocation(line: 109, column: 16, scope: !942)
!945 = !DILocation(line: 111, column: 19, scope: !946)
!946 = distinct !DILexicalBlock(scope: !947, file: !48, line: 111, column: 19)
!947 = distinct !DILexicalBlock(scope: !941, file: !48, line: 110, column: 15)
!948 = !DILocation(line: 111, column: 35, scope: !946)
!949 = !DILocation(line: 111, column: 19, scope: !947)
!950 = !DILocation(line: 113, column: 30, scope: !951)
!951 = distinct !DILexicalBlock(scope: !952, file: !48, line: 113, column: 22)
!952 = distinct !DILexicalBlock(scope: !946, file: !48, line: 112, column: 18)
!953 = !DILocation(line: 113, column: 22, scope: !951)
!954 = !DILocation(line: 113, column: 86, scope: !951)
!955 = !DILocation(line: 113, column: 22, scope: !952)
!956 = !DILocalVariable(name: "hostname_start_ptr", scope: !957, file: !48, line: 115, type: !18)
!957 = distinct !DILexicalBlock(scope: !951, file: !48, line: 114, column: 21)
!958 = !DILocation(line: 115, column: 28, scope: !957)
!959 = !DILocalVariable(name: "hostname_end_ptr", scope: !957, file: !48, line: 115, type: !18)
!960 = !DILocation(line: 115, column: 49, scope: !957)
!961 = !DILocalVariable(name: "path_start_prt", scope: !957, file: !48, line: 115, type: !18)
!962 = !DILocation(line: 115, column: 68, scope: !957)
!963 = !DILocalVariable(name: "server_name_len", scope: !957, file: !48, line: 116, type: !311)
!964 = !DILocation(line: 116, column: 29, scope: !957)
!965 = !DILocation(line: 120, column: 48, scope: !957)
!966 = !DILocation(line: 120, column: 58, scope: !957)
!967 = !DILocation(line: 120, column: 41, scope: !957)
!968 = !DILocation(line: 120, column: 40, scope: !957)
!969 = !DILocation(line: 121, column: 25, scope: !970)
!970 = distinct !DILexicalBlock(scope: !957, file: !48, line: 121, column: 25)
!971 = !DILocation(line: 121, column: 44, scope: !970)
!972 = !DILocation(line: 121, column: 25, scope: !957)
!973 = !DILocation(line: 122, column: 44, scope: !970)
!974 = !DILocation(line: 122, column: 54, scope: !970)
!975 = !DILocation(line: 122, column: 43, scope: !970)
!976 = !DILocation(line: 122, column: 25, scope: !970)
!977 = !DILocation(line: 124, column: 43, scope: !970)
!978 = !DILocation(line: 127, column: 46, scope: !957)
!979 = !DILocation(line: 127, column: 39, scope: !957)
!980 = !DILocation(line: 127, column: 38, scope: !957)
!981 = !DILocation(line: 128, column: 25, scope: !982)
!982 = distinct !DILexicalBlock(scope: !957, file: !48, line: 128, column: 25)
!983 = !DILocation(line: 128, column: 42, scope: !982)
!984 = !DILocation(line: 128, column: 25, scope: !957)
!985 = !DILocation(line: 130, column: 36, scope: !986)
!986 = distinct !DILexicalBlock(scope: !982, file: !48, line: 129, column: 24)
!987 = !DILocation(line: 132, column: 49, scope: !986)
!988 = !DILocation(line: 132, column: 42, scope: !986)
!989 = !DILocation(line: 132, column: 41, scope: !986)
!990 = !DILocation(line: 133, column: 28, scope: !991)
!991 = distinct !DILexicalBlock(scope: !986, file: !48, line: 133, column: 28)
!992 = !DILocation(line: 133, column: 45, scope: !991)
!993 = !DILocation(line: 133, column: 28, scope: !986)
!994 = !DILocation(line: 134, column: 45, scope: !991)
!995 = !DILocation(line: 134, column: 71, scope: !991)
!996 = !DILocation(line: 134, column: 64, scope: !991)
!997 = !DILocation(line: 134, column: 63, scope: !991)
!998 = !DILocation(line: 134, column: 44, scope: !991)
!999 = !DILocation(line: 134, column: 28, scope: !991)
!1000 = !DILocation(line: 135, column: 24, scope: !986)
!1001 = !DILocation(line: 138, column: 35, scope: !1002)
!1002 = distinct !DILexicalBlock(scope: !1003, file: !48, line: 138, column: 28)
!1003 = distinct !DILexicalBlock(scope: !982, file: !48, line: 137, column: 24)
!1004 = !DILocation(line: 138, column: 51, scope: !1002)
!1005 = !DILocation(line: 138, column: 28, scope: !1002)
!1006 = !DILocation(line: 138, column: 73, scope: !1002)
!1007 = !DILocation(line: 138, column: 28, scope: !1003)
!1008 = !DILocation(line: 139, column: 39, scope: !1002)
!1009 = !DILocation(line: 139, column: 28, scope: !1002)
!1010 = !DILocation(line: 143, column: 44, scope: !957)
!1011 = !DILocation(line: 143, column: 37, scope: !957)
!1012 = !DILocation(line: 143, column: 36, scope: !957)
!1013 = !DILocation(line: 144, column: 25, scope: !1014)
!1014 = distinct !DILexicalBlock(scope: !957, file: !48, line: 144, column: 25)
!1015 = !DILocation(line: 144, column: 40, scope: !1014)
!1016 = !DILocation(line: 144, column: 25, scope: !957)
!1017 = !DILocalVariable(name: "path_len", scope: !1018, file: !48, line: 146, type: !311)
!1018 = distinct !DILexicalBlock(scope: !1014, file: !48, line: 145, column: 24)
!1019 = !DILocation(line: 146, column: 32, scope: !1018)
!1020 = !DILocation(line: 148, column: 43, scope: !1018)
!1021 = !DILocation(line: 148, column: 36, scope: !1018)
!1022 = !DILocation(line: 148, column: 34, scope: !1018)
!1023 = !DILocation(line: 149, column: 28, scope: !1024)
!1024 = distinct !DILexicalBlock(scope: !1018, file: !48, line: 149, column: 28)
!1025 = !DILocation(line: 149, column: 37, scope: !1024)
!1026 = !DILocation(line: 149, column: 28, scope: !1018)
!1027 = !DILocation(line: 151, column: 48, scope: !1028)
!1028 = distinct !DILexicalBlock(scope: !1024, file: !48, line: 150, column: 27)
!1029 = !DILocation(line: 151, column: 64, scope: !1028)
!1030 = !DILocation(line: 151, column: 28, scope: !1028)
!1031 = !DILocation(line: 152, column: 40, scope: !1028)
!1032 = !DILocation(line: 152, column: 28, scope: !1028)
!1033 = !DILocation(line: 152, column: 49, scope: !1028)
!1034 = !DILocation(line: 153, column: 27, scope: !1028)
!1035 = !DILocation(line: 154, column: 24, scope: !1018)
!1036 = !DILocation(line: 156, column: 38, scope: !957)
!1037 = !DILocation(line: 156, column: 55, scope: !957)
!1038 = !DILocation(line: 156, column: 54, scope: !957)
!1039 = !DILocation(line: 156, column: 37, scope: !957)
!1040 = !DILocation(line: 157, column: 25, scope: !1041)
!1041 = distinct !DILexicalBlock(scope: !957, file: !48, line: 157, column: 25)
!1042 = !DILocation(line: 157, column: 41, scope: !1041)
!1043 = !DILocation(line: 157, column: 25, scope: !957)
!1044 = !DILocation(line: 159, column: 45, scope: !1045)
!1045 = distinct !DILexicalBlock(scope: !1041, file: !48, line: 158, column: 24)
!1046 = !DILocation(line: 159, column: 65, scope: !1045)
!1047 = !DILocation(line: 159, column: 25, scope: !1045)
!1048 = !DILocation(line: 160, column: 37, scope: !1045)
!1049 = !DILocation(line: 160, column: 25, scope: !1045)
!1050 = !DILocation(line: 160, column: 53, scope: !1045)
!1051 = !DILocation(line: 163, column: 35, scope: !1045)
!1052 = !DILocation(line: 163, column: 34, scope: !1045)
!1053 = !DILocation(line: 164, column: 28, scope: !1054)
!1054 = distinct !DILexicalBlock(scope: !1045, file: !48, line: 164, column: 28)
!1055 = !DILocation(line: 164, column: 37, scope: !1054)
!1056 = !DILocation(line: 164, column: 28, scope: !1045)
!1057 = !DILocation(line: 166, column: 28, scope: !1058)
!1058 = distinct !DILexicalBlock(scope: !1054, file: !48, line: 165, column: 27)
!1059 = !DILocation(line: 166, column: 28, scope: !1060)
!1060 = !DILexicalBlockFile(scope: !1058, file: !48, discriminator: 1)
!1061 = !DILocation(line: 167, column: 27, scope: !1058)
!1062 = !DILocation(line: 168, column: 24, scope: !1045)
!1063 = !DILocation(line: 171, column: 25, scope: !1064)
!1064 = distinct !DILexicalBlock(scope: !1041, file: !48, line: 170, column: 24)
!1065 = !DILocation(line: 172, column: 35, scope: !1064)
!1066 = !DILocation(line: 174, column: 21, scope: !957)
!1067 = !DILocation(line: 177, column: 22, scope: !1068)
!1068 = distinct !DILexicalBlock(scope: !951, file: !48, line: 176, column: 21)
!1069 = !DILocation(line: 178, column: 32, scope: !1068)
!1070 = !DILocation(line: 180, column: 18, scope: !952)
!1071 = !DILocation(line: 183, column: 19, scope: !1072)
!1072 = distinct !DILexicalBlock(scope: !946, file: !48, line: 182, column: 18)
!1073 = !DILocation(line: 184, column: 29, scope: !1072)
!1074 = !DILocation(line: 186, column: 15, scope: !947)
!1075 = !DILocation(line: 189, column: 16, scope: !1076)
!1076 = distinct !DILexicalBlock(scope: !941, file: !48, line: 188, column: 15)
!1077 = !DILocation(line: 190, column: 26, scope: !1076)
!1078 = !DILocation(line: 192, column: 12, scope: !942)
!1079 = !DILocation(line: 195, column: 13, scope: !1080)
!1080 = distinct !DILexicalBlock(scope: !935, file: !48, line: 194, column: 12)
!1081 = !DILocation(line: 196, column: 23, scope: !1080)
!1082 = !DILocation(line: 198, column: 9, scope: !936)
!1083 = !DILocation(line: 199, column: 14, scope: !886)
!1084 = !DILocation(line: 199, column: 7, scope: !886)
!1085 = !DILocation(line: 200, column: 6, scope: !886)
!1086 = !DILocation(line: 203, column: 17, scope: !1087)
!1087 = distinct !DILexicalBlock(scope: !882, file: !48, line: 202, column: 6)
!1088 = !DILocation(line: 203, column: 16, scope: !1087)
!1089 = !DILocation(line: 204, column: 7, scope: !1087)
!1090 = !DILocation(line: 204, column: 7, scope: !1091)
!1091 = !DILexicalBlockFile(scope: !1087, file: !48, discriminator: 1)
!1092 = !DILocation(line: 207, column: 11, scope: !782)
!1093 = !DILocation(line: 207, column: 4, scope: !782)
!1094 = !DILocation(line: 208, column: 3, scope: !782)
!1095 = distinct !DISubprogram(name: "send_notification", scope: !48, file: !48, line: 210, type: !549, isLocal: false, isDefinition: true, scopeLine: 211, flags: DIFlagPrototyped, isOptimized: false, unit: !47, variables: !2)
!1096 = !DILocalVariable(name: "msg_str", arg: 1, scope: !1095, file: !48, line: 210, type: !18)
!1097 = !DILocation(line: 210, column: 29, scope: !1095)
!1098 = !DILocalVariable(name: "msg_priority", arg: 2, scope: !1095, file: !48, line: 210, type: !18)
!1099 = !DILocation(line: 210, column: 44, scope: !1095)
!1100 = !DILocalVariable(name: "ret_error", scope: !1095, file: !48, line: 212, type: !12)
!1101 = !DILocation(line: 212, column: 8, scope: !1095)
!1102 = !DILocalVariable(name: "socket_fd", scope: !1095, file: !48, line: 213, type: !12)
!1103 = !DILocation(line: 213, column: 8, scope: !1095)
!1104 = !DILocalVariable(name: "server_addr", scope: !1095, file: !48, line: 214, type: !1105)
!1105 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "sockaddr_in", file: !88, line: 239, size: 128, align: 32, elements: !1106)
!1106 = !{!1107, !1108, !1109, !1110}
!1107 = !DIDerivedType(tag: DW_TAG_member, name: "sin_family", scope: !1105, file: !88, line: 241, baseType: !68, size: 16, align: 16)
!1108 = !DIDerivedType(tag: DW_TAG_member, name: "sin_port", scope: !1105, file: !88, line: 242, baseType: !219, size: 16, align: 16, offset: 16)
!1109 = !DIDerivedType(tag: DW_TAG_member, name: "sin_addr", scope: !1105, file: !88, line: 243, baseType: !87, size: 32, align: 32, offset: 32)
!1110 = !DIDerivedType(tag: DW_TAG_member, name: "sin_zero", scope: !1105, file: !88, line: 246, baseType: !226, size: 64, align: 8, offset: 64)
!1111 = !DILocation(line: 214, column: 23, scope: !1095)
!1112 = !DILocation(line: 217, column: 16, scope: !1095)
!1113 = !DILocation(line: 217, column: 14, scope: !1095)
!1114 = !DILocation(line: 218, column: 8, scope: !1115)
!1115 = distinct !DILexicalBlock(scope: !1095, file: !48, line: 218, column: 8)
!1116 = !DILocation(line: 218, column: 18, scope: !1115)
!1117 = !DILocation(line: 218, column: 8, scope: !1095)
!1118 = !DILocation(line: 221, column: 7, scope: !1119)
!1119 = distinct !DILexicalBlock(scope: !1115, file: !48, line: 219, column: 6)
!1120 = !DILocation(line: 222, column: 19, scope: !1119)
!1121 = !DILocation(line: 222, column: 30, scope: !1119)
!1122 = !DILocation(line: 223, column: 36, scope: !1119)
!1123 = !DILocation(line: 223, column: 30, scope: !1119)
!1124 = !DILocation(line: 223, column: 19, scope: !1119)
!1125 = !DILocation(line: 223, column: 28, scope: !1119)
!1126 = !DILocation(line: 224, column: 19, scope: !1119)
!1127 = !DILocation(line: 224, column: 30, scope: !1119)
!1128 = !DILocation(line: 227, column: 25, scope: !1119)
!1129 = !DILocation(line: 227, column: 36, scope: !1119)
!1130 = !DILocation(line: 227, column: 17, scope: !1119)
!1131 = !DILocation(line: 227, column: 16, scope: !1119)
!1132 = !DILocation(line: 228, column: 10, scope: !1133)
!1133 = distinct !DILexicalBlock(scope: !1119, file: !48, line: 228, column: 10)
!1134 = !DILocation(line: 228, column: 20, scope: !1133)
!1135 = !DILocation(line: 228, column: 10, scope: !1119)
!1136 = !DILocalVariable(name: "socket_file", scope: !1137, file: !48, line: 230, type: !788)
!1137 = distinct !DILexicalBlock(scope: !1133, file: !48, line: 229, column: 9)
!1138 = !DILocation(line: 230, column: 16, scope: !1137)
!1139 = !DILocation(line: 231, column: 31, scope: !1137)
!1140 = !DILocation(line: 231, column: 24, scope: !1137)
!1141 = !DILocation(line: 231, column: 22, scope: !1137)
!1142 = !DILocation(line: 232, column: 13, scope: !1143)
!1143 = distinct !DILexicalBlock(scope: !1137, file: !48, line: 232, column: 13)
!1144 = !DILocation(line: 232, column: 25, scope: !1143)
!1145 = !DILocation(line: 232, column: 13, scope: !1137)
!1146 = !DILocalVariable(name: "body_len", scope: !1147, file: !48, line: 234, type: !311)
!1147 = distinct !DILexicalBlock(scope: !1143, file: !48, line: 233, column: 12)
!1148 = !DILocation(line: 234, column: 20, scope: !1147)
!1149 = !DILocalVariable(name: "http_error", scope: !1147, file: !48, line: 235, type: !94)
!1150 = !DILocation(line: 235, column: 26, scope: !1147)
!1151 = !DILocalVariable(name: "fscanf_ret", scope: !1147, file: !48, line: 236, type: !12)
!1152 = !DILocation(line: 236, column: 17, scope: !1147)
!1153 = !DILocation(line: 238, column: 41, scope: !1147)
!1154 = !DILocation(line: 238, column: 40, scope: !1147)
!1155 = !DILocation(line: 238, column: 58, scope: !1147)
!1156 = !DILocation(line: 238, column: 61, scope: !1147)
!1157 = !DILocation(line: 238, column: 78, scope: !1158)
!1158 = !DILexicalBlockFile(scope: !1147, file: !48, discriminator: 1)
!1159 = !DILocation(line: 238, column: 77, scope: !1147)
!1160 = !DILocation(line: 238, column: 94, scope: !1147)
!1161 = !DILocation(line: 238, column: 97, scope: !1147)
!1162 = !DILocation(line: 238, column: 124, scope: !1147)
!1163 = !DILocation(line: 238, column: 117, scope: !1164)
!1164 = !DILexicalBlockFile(scope: !1147, file: !48, discriminator: 2)
!1165 = !DILocation(line: 238, column: 116, scope: !1147)
!1166 = !DILocation(line: 238, column: 133, scope: !1147)
!1167 = !DILocation(line: 238, column: 136, scope: !1147)
!1168 = !DILocation(line: 238, column: 164, scope: !1147)
!1169 = !DILocation(line: 238, column: 157, scope: !1170)
!1170 = !DILexicalBlockFile(scope: !1147, file: !48, discriminator: 3)
!1171 = !DILocation(line: 238, column: 156, scope: !1147)
!1172 = !DILocation(line: 238, column: 22, scope: !1147)
!1173 = !DILocation(line: 240, column: 23, scope: !1174)
!1174 = distinct !DILexicalBlock(scope: !1147, file: !48, line: 240, column: 16)
!1175 = !DILocation(line: 240, column: 16, scope: !1174)
!1176 = !DILocation(line: 240, column: 41, scope: !1174)
!1177 = !DILocation(line: 240, column: 16, scope: !1147)
!1178 = !DILocation(line: 241, column: 25, scope: !1174)
!1179 = !DILocation(line: 241, column: 16, scope: !1174)
!1180 = !DILocation(line: 244, column: 21, scope: !1147)
!1181 = !DILocation(line: 244, column: 13, scope: !1147)
!1182 = !DILocation(line: 245, column: 21, scope: !1147)
!1183 = !DILocation(line: 245, column: 13, scope: !1147)
!1184 = !DILocation(line: 246, column: 21, scope: !1147)
!1185 = !DILocation(line: 246, column: 13, scope: !1147)
!1186 = !DILocation(line: 247, column: 21, scope: !1147)
!1187 = !DILocation(line: 247, column: 84, scope: !1147)
!1188 = !DILocation(line: 247, column: 13, scope: !1147)
!1189 = !DILocation(line: 248, column: 21, scope: !1147)
!1190 = !DILocation(line: 248, column: 110, scope: !1147)
!1191 = !DILocation(line: 248, column: 119, scope: !1147)
!1192 = !DILocation(line: 248, column: 13, scope: !1147)
!1193 = !DILocation(line: 249, column: 23, scope: !1194)
!1194 = distinct !DILexicalBlock(scope: !1147, file: !48, line: 249, column: 16)
!1195 = !DILocation(line: 249, column: 16, scope: !1194)
!1196 = !DILocation(line: 249, column: 41, scope: !1194)
!1197 = !DILocation(line: 249, column: 16, scope: !1147)
!1198 = !DILocation(line: 250, column: 24, scope: !1194)
!1199 = !DILocation(line: 250, column: 16, scope: !1194)
!1200 = !DILocation(line: 253, column: 31, scope: !1147)
!1201 = !DILocation(line: 253, column: 24, scope: !1147)
!1202 = !DILocation(line: 253, column: 23, scope: !1147)
!1203 = !DILocation(line: 254, column: 16, scope: !1204)
!1204 = distinct !DILexicalBlock(scope: !1147, file: !48, line: 254, column: 16)
!1205 = !DILocation(line: 254, column: 27, scope: !1204)
!1206 = !DILocation(line: 254, column: 16, scope: !1147)
!1207 = !DILocation(line: 256, column: 19, scope: !1208)
!1208 = distinct !DILexicalBlock(scope: !1209, file: !48, line: 256, column: 19)
!1209 = distinct !DILexicalBlock(scope: !1204, file: !48, line: 255, column: 15)
!1210 = !DILocation(line: 256, column: 30, scope: !1208)
!1211 = !DILocation(line: 256, column: 19, scope: !1209)
!1212 = !DILocalVariable(name: "http_str", scope: !1213, file: !48, line: 258, type: !887)
!1213 = distinct !DILexicalBlock(scope: !1208, file: !48, line: 257, column: 18)
!1214 = !DILocation(line: 258, column: 24, scope: !1213)
!1215 = !DILocalVariable(name: "header_line", scope: !1213, file: !48, line: 259, type: !18)
!1216 = !DILocation(line: 259, column: 25, scope: !1213)
!1217 = !DILocalVariable(name: "header_line_ind", scope: !1213, file: !48, line: 260, type: !94)
!1218 = !DILocation(line: 260, column: 32, scope: !1213)
!1219 = !DILocalVariable(name: "header_abort", scope: !1213, file: !48, line: 261, type: !12)
!1220 = !DILocation(line: 261, column: 23, scope: !1213)
!1221 = !DILocation(line: 264, column: 31, scope: !1213)
!1222 = !DILocation(line: 265, column: 34, scope: !1213)
!1223 = !DILocation(line: 266, column: 19, scope: !1213)
!1224 = !DILocation(line: 266, column: 44, scope: !1225)
!1225 = !DILexicalBlockFile(scope: !1213, file: !48, discriminator: 1)
!1226 = !DILocation(line: 266, column: 67, scope: !1225)
!1227 = !DILocation(line: 266, column: 38, scope: !1225)
!1228 = !DILocation(line: 266, column: 37, scope: !1225)
!1229 = !DILocation(line: 266, column: 81, scope: !1225)
!1230 = !DILocation(line: 266, column: 19, scope: !1225)
!1231 = !DILocation(line: 268, column: 25, scope: !1232)
!1232 = distinct !DILexicalBlock(scope: !1233, file: !48, line: 268, column: 25)
!1233 = distinct !DILexicalBlock(scope: !1213, file: !48, line: 267, column: 21)
!1234 = !DILocation(line: 268, column: 37, scope: !1232)
!1235 = !DILocation(line: 268, column: 25, scope: !1233)
!1236 = !DILocation(line: 269, column: 25, scope: !1232)
!1237 = !DILocation(line: 271, column: 37, scope: !1233)
!1238 = !DILocation(line: 272, column: 25, scope: !1239)
!1239 = distinct !DILexicalBlock(scope: !1233, file: !48, line: 272, column: 25)
!1240 = !DILocation(line: 272, column: 41, scope: !1239)
!1241 = !DILocation(line: 272, column: 25, scope: !1233)
!1242 = !DILocation(line: 274, column: 36, scope: !1243)
!1243 = distinct !DILexicalBlock(scope: !1239, file: !48, line: 273, column: 24)
!1244 = !DILocation(line: 275, column: 37, scope: !1243)
!1245 = !DILocation(line: 276, column: 25, scope: !1243)
!1246 = !DILocation(line: 266, column: 19, scope: !1247)
!1247 = !DILexicalBlockFile(scope: !1213, file: !48, discriminator: 2)
!1248 = distinct !{!1248, !1223}
!1249 = !DILocation(line: 280, column: 22, scope: !1250)
!1250 = distinct !DILexicalBlock(scope: !1213, file: !48, line: 280, column: 22)
!1251 = !DILocation(line: 280, column: 34, scope: !1250)
!1252 = !DILocation(line: 280, column: 22, scope: !1213)
!1253 = !DILocalVariable(name: "notif_state", scope: !1254, file: !48, line: 282, type: !12)
!1254 = distinct !DILexicalBlock(scope: !1250, file: !48, line: 281, column: 21)
!1255 = !DILocation(line: 282, column: 26, scope: !1254)
!1256 = !DILocalVariable(name: "variables_obtined", scope: !1254, file: !48, line: 283, type: !12)
!1257 = !DILocation(line: 283, column: 26, scope: !1254)
!1258 = !DILocalVariable(name: "var_name", scope: !1254, file: !48, line: 284, type: !887)
!1259 = !DILocation(line: 284, column: 27, scope: !1254)
!1260 = !DILocalVariable(name: "var_value", scope: !1254, file: !48, line: 284, type: !887)
!1261 = !DILocation(line: 284, column: 52, scope: !1254)
!1262 = !DILocation(line: 287, column: 29, scope: !1254)
!1263 = !DILocation(line: 287, column: 22, scope: !1254)
!1264 = !DILocation(line: 288, column: 39, scope: !1254)
!1265 = !DILocation(line: 289, column: 22, scope: !1254)
!1266 = !DILocation(line: 289, column: 35, scope: !1267)
!1267 = !DILexicalBlockFile(scope: !1254, file: !48, discriminator: 1)
!1268 = !DILocation(line: 289, column: 66, scope: !1267)
!1269 = !DILocation(line: 289, column: 28, scope: !1267)
!1270 = !DILocation(line: 289, column: 76, scope: !1267)
!1271 = !DILocation(line: 289, column: 22, scope: !1267)
!1272 = !DILocation(line: 291, column: 32, scope: !1273)
!1273 = distinct !DILexicalBlock(scope: !1254, file: !48, line: 290, column: 24)
!1274 = !DILocation(line: 291, column: 25, scope: !1273)
!1275 = !DILocation(line: 292, column: 35, scope: !1276)
!1276 = distinct !DILexicalBlock(scope: !1273, file: !48, line: 292, column: 28)
!1277 = !DILocation(line: 292, column: 63, scope: !1276)
!1278 = !DILocation(line: 292, column: 28, scope: !1276)
!1279 = !DILocation(line: 292, column: 74, scope: !1276)
!1280 = !DILocation(line: 292, column: 28, scope: !1273)
!1281 = !DILocation(line: 294, column: 35, scope: !1282)
!1282 = distinct !DILexicalBlock(scope: !1276, file: !48, line: 293, column: 27)
!1283 = !DILocation(line: 294, column: 28, scope: !1282)
!1284 = !DILocation(line: 295, column: 35, scope: !1282)
!1285 = !DILocation(line: 295, column: 28, scope: !1282)
!1286 = !DILocation(line: 297, column: 38, scope: !1287)
!1287 = distinct !DILexicalBlock(scope: !1282, file: !48, line: 297, column: 31)
!1288 = !DILocation(line: 297, column: 31, scope: !1287)
!1289 = !DILocation(line: 297, column: 57, scope: !1287)
!1290 = !DILocation(line: 297, column: 31, scope: !1282)
!1291 = !DILocation(line: 299, column: 48, scope: !1292)
!1292 = distinct !DILexicalBlock(scope: !1287, file: !48, line: 298, column: 30)
!1293 = !DILocation(line: 299, column: 43, scope: !1292)
!1294 = !DILocation(line: 299, column: 42, scope: !1292)
!1295 = !DILocation(line: 300, column: 48, scope: !1292)
!1296 = !DILocation(line: 301, column: 30, scope: !1292)
!1297 = !DILocation(line: 302, column: 27, scope: !1282)
!1298 = !DILocation(line: 289, column: 22, scope: !1299)
!1299 = !DILexicalBlockFile(scope: !1254, file: !48, discriminator: 2)
!1300 = distinct !{!1300, !1265}
!1301 = !DILocation(line: 304, column: 29, scope: !1254)
!1302 = !DILocation(line: 304, column: 22, scope: !1254)
!1303 = !DILocation(line: 306, column: 25, scope: !1304)
!1304 = distinct !DILexicalBlock(scope: !1254, file: !48, line: 306, column: 25)
!1305 = !DILocation(line: 306, column: 43, scope: !1304)
!1306 = !DILocation(line: 306, column: 25, scope: !1254)
!1307 = !DILocation(line: 308, column: 28, scope: !1308)
!1308 = distinct !DILexicalBlock(scope: !1309, file: !48, line: 308, column: 28)
!1309 = distinct !DILexicalBlock(scope: !1304, file: !48, line: 307, column: 24)
!1310 = !DILocation(line: 308, column: 40, scope: !1308)
!1311 = !DILocation(line: 308, column: 28, scope: !1309)
!1312 = !DILocation(line: 310, column: 37, scope: !1313)
!1313 = distinct !DILexicalBlock(scope: !1308, file: !48, line: 309, column: 27)
!1314 = !DILocation(line: 311, column: 27, scope: !1313)
!1315 = !DILocation(line: 314, column: 37, scope: !1316)
!1316 = distinct !DILexicalBlock(scope: !1308, file: !48, line: 313, column: 27)
!1317 = !DILocation(line: 315, column: 28, scope: !1316)
!1318 = !DILocation(line: 317, column: 24, scope: !1309)
!1319 = !DILocation(line: 320, column: 34, scope: !1320)
!1320 = distinct !DILexicalBlock(scope: !1304, file: !48, line: 319, column: 24)
!1321 = !DILocation(line: 321, column: 25, scope: !1320)
!1322 = !DILocation(line: 323, column: 21, scope: !1254)
!1323 = !DILocation(line: 326, column: 25, scope: !1324)
!1324 = distinct !DILexicalBlock(scope: !1325, file: !48, line: 326, column: 25)
!1325 = distinct !DILexicalBlock(scope: !1250, file: !48, line: 325, column: 21)
!1326 = !DILocation(line: 326, column: 38, scope: !1324)
!1327 = !DILocation(line: 326, column: 25, scope: !1325)
!1328 = !DILocation(line: 328, column: 34, scope: !1329)
!1329 = distinct !DILexicalBlock(scope: !1324, file: !48, line: 327, column: 24)
!1330 = !DILocation(line: 329, column: 25, scope: !1329)
!1331 = !DILocation(line: 330, column: 24, scope: !1329)
!1332 = !DILocation(line: 333, column: 34, scope: !1333)
!1333 = distinct !DILexicalBlock(scope: !1324, file: !48, line: 332, column: 24)
!1334 = !DILocation(line: 334, column: 25, scope: !1333)
!1335 = !DILocation(line: 334, column: 25, scope: !1336)
!1336 = !DILexicalBlockFile(scope: !1333, file: !48, discriminator: 1)
!1337 = !DILocation(line: 337, column: 18, scope: !1213)
!1338 = !DILocation(line: 340, column: 28, scope: !1339)
!1339 = distinct !DILexicalBlock(scope: !1208, file: !48, line: 339, column: 18)
!1340 = !DILocation(line: 341, column: 19, scope: !1339)
!1341 = !DILocation(line: 343, column: 15, scope: !1209)
!1342 = !DILocation(line: 346, column: 26, scope: !1343)
!1343 = distinct !DILexicalBlock(scope: !1204, file: !48, line: 345, column: 15)
!1344 = !DILocation(line: 346, column: 25, scope: !1343)
!1345 = !DILocation(line: 347, column: 16, scope: !1343)
!1346 = !DILocation(line: 347, column: 16, scope: !1347)
!1347 = !DILexicalBlockFile(scope: !1343, file: !48, discriminator: 1)
!1348 = !DILocation(line: 349, column: 20, scope: !1147)
!1349 = !DILocation(line: 349, column: 13, scope: !1147)
!1350 = !DILocation(line: 350, column: 12, scope: !1147)
!1351 = !DILocation(line: 353, column: 13, scope: !1352)
!1352 = distinct !DILexicalBlock(scope: !1143, file: !48, line: 352, column: 12)
!1353 = !DILocation(line: 353, column: 13, scope: !1354)
!1354 = !DILexicalBlockFile(scope: !1352, file: !48, discriminator: 1)
!1355 = !DILocation(line: 353, column: 13, scope: !1356)
!1356 = !DILexicalBlockFile(scope: !1352, file: !48, discriminator: 2)
!1357 = !DILocation(line: 353, column: 13, scope: !1358)
!1358 = !DILexicalBlockFile(scope: !1352, file: !48, discriminator: 3)
!1359 = !DILocation(line: 354, column: 19, scope: !1352)
!1360 = !DILocation(line: 354, column: 13, scope: !1352)
!1361 = !DILocation(line: 356, column: 9, scope: !1137)
!1362 = !DILocation(line: 359, column: 20, scope: !1363)
!1363 = distinct !DILexicalBlock(scope: !1133, file: !48, line: 358, column: 9)
!1364 = !DILocation(line: 359, column: 19, scope: !1363)
!1365 = !DILocation(line: 360, column: 10, scope: !1363)
!1366 = !DILocation(line: 360, column: 10, scope: !1367)
!1367 = !DILexicalBlockFile(scope: !1363, file: !48, discriminator: 1)
!1368 = !DILocation(line: 360, column: 10, scope: !1369)
!1369 = !DILexicalBlockFile(scope: !1363, file: !48, discriminator: 2)
!1370 = !DILocation(line: 360, column: 10, scope: !1371)
!1371 = !DILexicalBlockFile(scope: !1363, file: !48, discriminator: 3)
!1372 = !DILocation(line: 361, column: 16, scope: !1363)
!1373 = !DILocation(line: 361, column: 10, scope: !1363)
!1374 = !DILocation(line: 363, column: 6, scope: !1119)
!1375 = !DILocation(line: 366, column: 17, scope: !1376)
!1376 = distinct !DILexicalBlock(scope: !1115, file: !48, line: 365, column: 6)
!1377 = !DILocation(line: 366, column: 16, scope: !1376)
!1378 = !DILocation(line: 367, column: 7, scope: !1376)
!1379 = !DILocation(line: 367, column: 7, scope: !1380)
!1380 = !DILexicalBlockFile(scope: !1376, file: !48, discriminator: 1)
!1381 = !DILocation(line: 369, column: 11, scope: !1095)
!1382 = !DILocation(line: 369, column: 4, scope: !1095)
!1383 = distinct !DISubprogram(name: "herror_msg", scope: !97, file: !97, line: 23, type: !1384, isLocal: false, isDefinition: true, scopeLine: 24, flags: DIFlagPrototyped, isOptimized: false, unit: !96, variables: !2)
!1384 = !DISubroutineType(types: !1385)
!1385 = !{!18, !12}
!1386 = !DILocalVariable(name: "herror_cod", arg: 1, scope: !1383, file: !97, line: 23, type: !12)
!1387 = !DILocation(line: 23, column: 22, scope: !1383)
!1388 = !DILocalVariable(name: "error_str", scope: !1383, file: !97, line: 25, type: !18)
!1389 = !DILocation(line: 25, column: 10, scope: !1383)
!1390 = !DILocation(line: 26, column: 11, scope: !1383)
!1391 = !DILocation(line: 26, column: 4, scope: !1383)
!1392 = !DILocation(line: 29, column: 19, scope: !1393)
!1393 = distinct !DILexicalBlock(scope: !1383, file: !97, line: 27, column: 6)
!1394 = !DILocation(line: 30, column: 10, scope: !1393)
!1395 = !DILocation(line: 32, column: 19, scope: !1393)
!1396 = !DILocation(line: 33, column: 10, scope: !1393)
!1397 = !DILocation(line: 35, column: 19, scope: !1393)
!1398 = !DILocation(line: 36, column: 10, scope: !1393)
!1399 = !DILocation(line: 38, column: 19, scope: !1393)
!1400 = !DILocation(line: 39, column: 10, scope: !1393)
!1401 = !DILocation(line: 41, column: 11, scope: !1383)
!1402 = !DILocation(line: 41, column: 4, scope: !1383)
!1403 = distinct !DISubprogram(name: "resp_code_msg", scope: !97, file: !97, line: 47, type: !1404, isLocal: false, isDefinition: true, scopeLine: 48, flags: DIFlagPrototyped, isOptimized: false, unit: !96, variables: !2)
!1404 = !DISubroutineType(types: !1405)
!1405 = !{!18, !1406}
!1406 = !DIDerivedType(tag: DW_TAG_typedef, name: "ns_rcode", file: !100, line: 210, baseType: !99)
!1407 = !DILocalVariable(name: "rcode", arg: 1, scope: !1403, file: !97, line: 47, type: !1406)
!1408 = !DILocation(line: 47, column: 30, scope: !1403)
!1409 = !DILocalVariable(name: "code_str", scope: !1403, file: !97, line: 49, type: !18)
!1410 = !DILocation(line: 49, column: 10, scope: !1403)
!1411 = !DILocation(line: 50, column: 11, scope: !1403)
!1412 = !DILocation(line: 50, column: 4, scope: !1403)
!1413 = !DILocation(line: 53, column: 18, scope: !1414)
!1414 = distinct !DILexicalBlock(scope: !1403, file: !97, line: 51, column: 6)
!1415 = !DILocation(line: 54, column: 10, scope: !1414)
!1416 = !DILocation(line: 56, column: 18, scope: !1414)
!1417 = !DILocation(line: 57, column: 10, scope: !1414)
!1418 = !DILocation(line: 59, column: 18, scope: !1414)
!1419 = !DILocation(line: 60, column: 10, scope: !1414)
!1420 = !DILocation(line: 62, column: 18, scope: !1414)
!1421 = !DILocation(line: 63, column: 10, scope: !1414)
!1422 = !DILocation(line: 65, column: 18, scope: !1414)
!1423 = !DILocation(line: 66, column: 10, scope: !1414)
!1424 = !DILocation(line: 68, column: 18, scope: !1414)
!1425 = !DILocation(line: 69, column: 10, scope: !1414)
!1426 = !DILocation(line: 71, column: 11, scope: !1403)
!1427 = !DILocation(line: 71, column: 4, scope: !1403)
!1428 = distinct !DISubprogram(name: "hostname_to_ip", scope: !97, file: !97, line: 74, type: !1429, isLocal: false, isDefinition: true, scopeLine: 75, flags: DIFlagPrototyped, isOptimized: false, unit: !96, variables: !2)
!1429 = !DISubroutineType(types: !1430)
!1430 = !{!12, !18, !234}
!1431 = !DILocalVariable(name: "hostname", arg: 1, scope: !1428, file: !97, line: 74, type: !18)
!1432 = !DILocation(line: 74, column: 26, scope: !1428)
!1433 = !DILocalVariable(name: "ip_addr", arg: 2, scope: !1428, file: !97, line: 74, type: !234)
!1434 = !DILocation(line: 74, column: 52, scope: !1428)
!1435 = !DILocalVariable(name: "ret", scope: !1428, file: !97, line: 76, type: !12)
!1436 = !DILocation(line: 76, column: 8, scope: !1428)
!1437 = !DILocalVariable(name: "hints", scope: !1428, file: !97, line: 77, type: !1438)
!1438 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "addrinfo", file: !1439, line: 567, size: 256, align: 32, elements: !1440)
!1439 = !DIFile(filename: "/home/zrz0517/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/libc/usr/include/netdb.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/alarm4pi-cb")
!1440 = !{!1441, !1442, !1443, !1444, !1445, !1448, !1454, !1455}
!1441 = !DIDerivedType(tag: DW_TAG_member, name: "ai_flags", scope: !1438, file: !1439, line: 569, baseType: !12, size: 32, align: 32)
!1442 = !DIDerivedType(tag: DW_TAG_member, name: "ai_family", scope: !1438, file: !1439, line: 570, baseType: !12, size: 32, align: 32, offset: 32)
!1443 = !DIDerivedType(tag: DW_TAG_member, name: "ai_socktype", scope: !1438, file: !1439, line: 571, baseType: !12, size: 32, align: 32, offset: 64)
!1444 = !DIDerivedType(tag: DW_TAG_member, name: "ai_protocol", scope: !1438, file: !1439, line: 572, baseType: !12, size: 32, align: 32, offset: 96)
!1445 = !DIDerivedType(tag: DW_TAG_member, name: "ai_addrlen", scope: !1438, file: !1439, line: 573, baseType: !1446, size: 32, align: 32, offset: 128)
!1446 = !DIDerivedType(tag: DW_TAG_typedef, name: "socklen_t", file: !65, line: 33, baseType: !1447)
!1447 = !DIDerivedType(tag: DW_TAG_typedef, name: "__socklen_t", file: !11, line: 189, baseType: !94)
!1448 = !DIDerivedType(tag: DW_TAG_member, name: "ai_addr", scope: !1438, file: !1439, line: 574, baseType: !1449, size: 32, align: 32, offset: 160)
!1449 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1450, size: 32, align: 32)
!1450 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "sockaddr", file: !65, line: 153, size: 128, align: 16, elements: !1451)
!1451 = !{!1452, !1453}
!1452 = !DIDerivedType(tag: DW_TAG_member, name: "sa_family", scope: !1450, file: !65, line: 155, baseType: !68, size: 16, align: 16)
!1453 = !DIDerivedType(tag: DW_TAG_member, name: "sa_data", scope: !1450, file: !65, line: 156, baseType: !72, size: 112, align: 8, offset: 16)
!1454 = !DIDerivedType(tag: DW_TAG_member, name: "ai_canonname", scope: !1438, file: !1439, line: 575, baseType: !18, size: 32, align: 32, offset: 192)
!1455 = !DIDerivedType(tag: DW_TAG_member, name: "ai_next", scope: !1438, file: !1439, line: 576, baseType: !1456, size: 32, align: 32, offset: 224)
!1456 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1438, size: 32, align: 32)
!1457 = !DILocation(line: 77, column: 20, scope: !1428)
!1458 = !DILocalVariable(name: "res_addr", scope: !1428, file: !97, line: 77, type: !1456)
!1459 = !DILocation(line: 77, column: 28, scope: !1428)
!1460 = !DILocalVariable(name: "res_error", scope: !1428, file: !97, line: 78, type: !12)
!1461 = !DILocation(line: 78, column: 8, scope: !1428)
!1462 = !DILocation(line: 80, column: 4, scope: !1428)
!1463 = !DILocation(line: 81, column: 10, scope: !1428)
!1464 = !DILocation(line: 81, column: 20, scope: !1428)
!1465 = !DILocation(line: 82, column: 10, scope: !1428)
!1466 = !DILocation(line: 82, column: 22, scope: !1428)
!1467 = !DILocation(line: 84, column: 28, scope: !1428)
!1468 = !DILocation(line: 84, column: 16, scope: !1428)
!1469 = !DILocation(line: 84, column: 14, scope: !1428)
!1470 = !DILocation(line: 85, column: 7, scope: !1471)
!1471 = distinct !DILexicalBlock(scope: !1428, file: !97, line: 85, column: 7)
!1472 = !DILocation(line: 85, column: 17, scope: !1471)
!1473 = !DILocation(line: 85, column: 7, scope: !1428)
!1474 = !DILocalVariable(name: "res_addr_next", scope: !1475, file: !97, line: 87, type: !1456)
!1475 = distinct !DILexicalBlock(scope: !1471, file: !97, line: 86, column: 6)
!1476 = !DILocation(line: 87, column: 24, scope: !1475)
!1477 = !DILocation(line: 89, column: 10, scope: !1475)
!1478 = !DILocation(line: 91, column: 27, scope: !1479)
!1479 = distinct !DILexicalBlock(scope: !1475, file: !97, line: 91, column: 7)
!1480 = !DILocation(line: 91, column: 25, scope: !1479)
!1481 = !DILocation(line: 91, column: 11, scope: !1479)
!1482 = !DILocation(line: 91, column: 37, scope: !1483)
!1483 = !DILexicalBlockFile(scope: !1484, file: !97, discriminator: 1)
!1484 = distinct !DILexicalBlock(scope: !1479, file: !97, line: 91, column: 7)
!1485 = !DILocation(line: 91, column: 51, scope: !1483)
!1486 = !DILocation(line: 91, column: 7, scope: !1483)
!1487 = !DILocalVariable(name: "addr", scope: !1488, file: !97, line: 93, type: !214)
!1488 = distinct !DILexicalBlock(scope: !1484, file: !97, line: 92, column: 9)
!1489 = !DILocation(line: 93, column: 28, scope: !1488)
!1490 = !DILocation(line: 95, column: 39, scope: !1488)
!1491 = !DILocation(line: 95, column: 54, scope: !1488)
!1492 = !DILocation(line: 95, column: 17, scope: !1488)
!1493 = !DILocation(line: 95, column: 15, scope: !1488)
!1494 = !DILocation(line: 96, column: 11, scope: !1488)
!1495 = !DILocation(line: 96, column: 19, scope: !1488)
!1496 = !DILocation(line: 96, column: 25, scope: !1488)
!1497 = !DILocation(line: 97, column: 13, scope: !1498)
!1498 = distinct !DILexicalBlock(scope: !1488, file: !97, line: 97, column: 13)
!1499 = !DILocation(line: 97, column: 22, scope: !1498)
!1500 = !DILocation(line: 97, column: 29, scope: !1498)
!1501 = !DILocation(line: 97, column: 13, scope: !1488)
!1502 = !DILocation(line: 100, column: 16, scope: !1503)
!1503 = distinct !DILexicalBlock(scope: !1498, file: !97, line: 98, column: 12)
!1504 = !DILocation(line: 101, column: 13, scope: !1503)
!1505 = !DILocation(line: 103, column: 9, scope: !1488)
!1506 = !DILocation(line: 91, column: 76, scope: !1507)
!1507 = !DILexicalBlockFile(scope: !1484, file: !97, discriminator: 2)
!1508 = !DILocation(line: 91, column: 91, scope: !1507)
!1509 = !DILocation(line: 91, column: 74, scope: !1507)
!1510 = !DILocation(line: 91, column: 7, scope: !1507)
!1511 = distinct !{!1511, !1512}
!1512 = !DILocation(line: 91, column: 7, scope: !1475)
!1513 = !DILocation(line: 105, column: 20, scope: !1475)
!1514 = !DILocation(line: 105, column: 7, scope: !1475)
!1515 = !DILocation(line: 106, column: 6, scope: !1475)
!1516 = !DILocation(line: 109, column: 7, scope: !1517)
!1517 = distinct !DILexicalBlock(scope: !1471, file: !97, line: 108, column: 6)
!1518 = !DILocation(line: 109, column: 7, scope: !1519)
!1519 = !DILexicalBlockFile(scope: !1517, file: !97, discriminator: 1)
!1520 = !DILocation(line: 110, column: 11, scope: !1517)
!1521 = !DILocation(line: 110, column: 10, scope: !1517)
!1522 = !DILocation(line: 113, column: 11, scope: !1428)
!1523 = !DILocation(line: 113, column: 4, scope: !1428)
!1524 = distinct !DISubprogram(name: "hostname_to_ip_at_dns", scope: !97, file: !97, line: 116, type: !1525, isLocal: false, isDefinition: true, scopeLine: 117, flags: DIFlagPrototyped, isOptimized: false, unit: !96, variables: !2)
!1525 = !DISubroutineType(types: !1526)
!1526 = !{!12, !18, !18, !234}
!1527 = !DILocalVariable(name: "dns_server", arg: 1, scope: !1524, file: !97, line: 116, type: !18)
!1528 = !DILocation(line: 116, column: 33, scope: !1524)
!1529 = !DILocalVariable(name: "domain_name", arg: 2, scope: !1524, file: !97, line: 116, type: !18)
!1530 = !DILocation(line: 116, column: 51, scope: !1524)
!1531 = !DILocalVariable(name: "ip_addr", arg: 3, scope: !1524, file: !97, line: 116, type: !234)
!1532 = !DILocation(line: 116, column: 80, scope: !1524)
!1533 = !DILocalVariable(name: "fn_ret", scope: !1524, file: !97, line: 118, type: !12)
!1534 = !DILocation(line: 118, column: 8, scope: !1524)
!1535 = !DILocalVariable(name: "res_stat", scope: !1524, file: !97, line: 119, type: !1536)
!1536 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "__res_state", file: !119, line: 104, size: 4096, align: 32, elements: !1537)
!1537 = !{!1538, !1539, !1540, !1543, !1544, !1548, !1551, !1553, !1557, !1558, !1559, !1560, !1561, !1562, !1571, !1583, !1590, !1591, !1592, !1595}
!1538 = !DIDerivedType(tag: DW_TAG_member, name: "retrans", scope: !1536, file: !119, line: 105, baseType: !12, size: 32, align: 32)
!1539 = !DIDerivedType(tag: DW_TAG_member, name: "retry", scope: !1536, file: !119, line: 106, baseType: !12, size: 32, align: 32, offset: 32)
!1540 = !DIDerivedType(tag: DW_TAG_member, name: "options", scope: !1536, file: !119, line: 107, baseType: !1541, size: 32, align: 32, offset: 64)
!1541 = !DIDerivedType(tag: DW_TAG_typedef, name: "u_long", file: !9, line: 36, baseType: !1542)
!1542 = !DIDerivedType(tag: DW_TAG_typedef, name: "__u_long", file: !11, line: 33, baseType: !42)
!1543 = !DIDerivedType(tag: DW_TAG_member, name: "nscount", scope: !1536, file: !119, line: 108, baseType: !12, size: 32, align: 32, offset: 96)
!1544 = !DIDerivedType(tag: DW_TAG_member, name: "nsaddr_list", scope: !1536, file: !119, line: 110, baseType: !1545, size: 384, align: 32, offset: 128)
!1545 = !DICompositeType(tag: DW_TAG_array_type, baseType: !215, size: 384, align: 32, elements: !1546)
!1546 = !{!1547}
!1547 = !DISubrange(count: 3)
!1548 = !DIDerivedType(tag: DW_TAG_member, name: "id", scope: !1536, file: !119, line: 112, baseType: !1549, size: 16, align: 16, offset: 512)
!1549 = !DIDerivedType(tag: DW_TAG_typedef, name: "u_short", file: !9, line: 34, baseType: !1550)
!1550 = !DIDerivedType(tag: DW_TAG_typedef, name: "__u_short", file: !11, line: 31, baseType: !70)
!1551 = !DIDerivedType(tag: DW_TAG_member, name: "dnsrch", scope: !1536, file: !119, line: 114, baseType: !1552, size: 224, align: 32, offset: 544)
!1552 = !DICompositeType(tag: DW_TAG_array_type, baseType: !18, size: 224, align: 32, elements: !20)
!1553 = !DIDerivedType(tag: DW_TAG_member, name: "defdname", scope: !1536, file: !119, line: 115, baseType: !1554, size: 2048, align: 8, offset: 768)
!1554 = !DICompositeType(tag: DW_TAG_array_type, baseType: !19, size: 2048, align: 8, elements: !1555)
!1555 = !{!1556}
!1556 = !DISubrange(count: 256)
!1557 = !DIDerivedType(tag: DW_TAG_member, name: "pfcode", scope: !1536, file: !119, line: 116, baseType: !1541, size: 32, align: 32, offset: 2816)
!1558 = !DIDerivedType(tag: DW_TAG_member, name: "ndots", scope: !1536, file: !119, line: 117, baseType: !94, size: 4, align: 32, offset: 2848, flags: DIFlagBitField, extraData: i64 2848)
!1559 = !DIDerivedType(tag: DW_TAG_member, name: "nsort", scope: !1536, file: !119, line: 118, baseType: !94, size: 4, align: 32, offset: 2852, flags: DIFlagBitField, extraData: i64 2848)
!1560 = !DIDerivedType(tag: DW_TAG_member, name: "ipv6_unavail", scope: !1536, file: !119, line: 119, baseType: !94, size: 1, align: 32, offset: 2856, flags: DIFlagBitField, extraData: i64 2848)
!1561 = !DIDerivedType(tag: DW_TAG_member, name: "unused", scope: !1536, file: !119, line: 120, baseType: !94, size: 23, align: 32, offset: 2857, flags: DIFlagBitField, extraData: i64 2848)
!1562 = !DIDerivedType(tag: DW_TAG_member, name: "sort_list", scope: !1536, file: !119, line: 124, baseType: !1563, size: 640, align: 32, offset: 2880)
!1563 = !DICompositeType(tag: DW_TAG_array_type, baseType: !1564, size: 640, align: 32, elements: !1569)
!1564 = distinct !DICompositeType(tag: DW_TAG_structure_type, scope: !1536, file: !119, line: 121, size: 64, align: 32, elements: !1565)
!1565 = !{!1566, !1567}
!1566 = !DIDerivedType(tag: DW_TAG_member, name: "addr", scope: !1564, file: !119, line: 122, baseType: !222, size: 32, align: 32)
!1567 = !DIDerivedType(tag: DW_TAG_member, name: "mask", scope: !1564, file: !119, line: 123, baseType: !1568, size: 32, align: 32, offset: 32)
!1568 = !DIDerivedType(tag: DW_TAG_typedef, name: "u_int32_t", file: !9, line: 202, baseType: !94)
!1569 = !{!1570}
!1570 = !DISubrange(count: 10)
!1571 = !DIDerivedType(tag: DW_TAG_member, name: "qhook", scope: !1536, file: !119, line: 126, baseType: !1572, size: 32, align: 32, offset: 3520)
!1572 = !DIDerivedType(tag: DW_TAG_typedef, name: "res_send_qhook", file: !119, line: 74, baseType: !1573)
!1573 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1574, size: 32, align: 32)
!1574 = !DISubroutineType(types: !1575)
!1575 = !{!1576, !1577, !1579, !1582, !230, !12, !1582}
!1576 = !DIDerivedType(tag: DW_TAG_typedef, name: "res_sendhookact", file: !119, line: 72, baseType: !118)
!1577 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1578, size: 32, align: 32)
!1578 = !DIDerivedType(tag: DW_TAG_const_type, baseType: !214)
!1579 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1580, size: 32, align: 32)
!1580 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1581, size: 32, align: 32)
!1581 = !DIDerivedType(tag: DW_TAG_const_type, baseType: !231)
!1582 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !12, size: 32, align: 32)
!1583 = !DIDerivedType(tag: DW_TAG_member, name: "rhook", scope: !1536, file: !119, line: 127, baseType: !1584, size: 32, align: 32, offset: 3552)
!1584 = !DIDerivedType(tag: DW_TAG_typedef, name: "res_send_rhook", file: !119, line: 81, baseType: !1585)
!1585 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1586, size: 32, align: 32)
!1586 = !DISubroutineType(types: !1587)
!1587 = !{!1576, !1588, !1580, !12, !230, !12, !1582}
!1588 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1589, size: 32, align: 32)
!1589 = !DIDerivedType(tag: DW_TAG_const_type, baseType: !215)
!1590 = !DIDerivedType(tag: DW_TAG_member, name: "res_h_errno", scope: !1536, file: !119, line: 128, baseType: !12, size: 32, align: 32, offset: 3584)
!1591 = !DIDerivedType(tag: DW_TAG_member, name: "_vcsock", scope: !1536, file: !119, line: 129, baseType: !12, size: 32, align: 32, offset: 3616)
!1592 = !DIDerivedType(tag: DW_TAG_member, name: "_flags", scope: !1536, file: !119, line: 130, baseType: !1593, size: 32, align: 32, offset: 3648)
!1593 = !DIDerivedType(tag: DW_TAG_typedef, name: "u_int", file: !9, line: 35, baseType: !1594)
!1594 = !DIDerivedType(tag: DW_TAG_typedef, name: "__u_int", file: !11, line: 32, baseType: !94)
!1595 = !DIDerivedType(tag: DW_TAG_member, name: "_u", scope: !1536, file: !119, line: 148, baseType: !1596, size: 416, align: 32, offset: 3680)
!1596 = distinct !DICompositeType(tag: DW_TAG_union_type, scope: !1536, file: !119, line: 132, size: 416, align: 32, elements: !1597)
!1597 = !{!1598, !1602}
!1598 = !DIDerivedType(tag: DW_TAG_member, name: "pad", scope: !1596, file: !119, line: 133, baseType: !1599, size: 416, align: 8)
!1599 = !DICompositeType(tag: DW_TAG_array_type, baseType: !19, size: 416, align: 8, elements: !1600)
!1600 = !{!1601}
!1601 = !DISubrange(count: 52)
!1602 = !DIDerivedType(tag: DW_TAG_member, name: "_ext", scope: !1596, file: !119, line: 147, baseType: !1603, size: 352, align: 32)
!1603 = distinct !DICompositeType(tag: DW_TAG_structure_type, scope: !1596, file: !119, line: 134, size: 352, align: 32, elements: !1604)
!1604 = !{!1605, !1607, !1609, !1611, !1612, !1613, !1639}
!1605 = !DIDerivedType(tag: DW_TAG_member, name: "nscount", scope: !1603, file: !119, line: 135, baseType: !1606, size: 16, align: 16)
!1606 = !DIDerivedType(tag: DW_TAG_typedef, name: "u_int16_t", file: !9, line: 201, baseType: !70)
!1607 = !DIDerivedType(tag: DW_TAG_member, name: "nsmap", scope: !1603, file: !119, line: 136, baseType: !1608, size: 48, align: 16, offset: 16)
!1608 = !DICompositeType(tag: DW_TAG_array_type, baseType: !1606, size: 48, align: 16, elements: !1546)
!1609 = !DIDerivedType(tag: DW_TAG_member, name: "nssocks", scope: !1603, file: !119, line: 137, baseType: !1610, size: 96, align: 32, offset: 64)
!1610 = !DICompositeType(tag: DW_TAG_array_type, baseType: !12, size: 96, align: 32, elements: !1546)
!1611 = !DIDerivedType(tag: DW_TAG_member, name: "nscount6", scope: !1603, file: !119, line: 138, baseType: !1606, size: 16, align: 16, offset: 160)
!1612 = !DIDerivedType(tag: DW_TAG_member, name: "nsinit", scope: !1603, file: !119, line: 139, baseType: !1606, size: 16, align: 16, offset: 176)
!1613 = !DIDerivedType(tag: DW_TAG_member, name: "nsaddrs", scope: !1603, file: !119, line: 140, baseType: !1614, size: 96, align: 32, offset: 192)
!1614 = !DICompositeType(tag: DW_TAG_array_type, baseType: !1615, size: 96, align: 32, elements: !1546)
!1615 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1616, size: 32, align: 32)
!1616 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "sockaddr_in6", file: !88, line: 254, size: 224, align: 32, elements: !1617)
!1617 = !{!1618, !1619, !1620, !1621, !1638}
!1618 = !DIDerivedType(tag: DW_TAG_member, name: "sin6_family", scope: !1616, file: !88, line: 256, baseType: !68, size: 16, align: 16)
!1619 = !DIDerivedType(tag: DW_TAG_member, name: "sin6_port", scope: !1616, file: !88, line: 257, baseType: !219, size: 16, align: 16, offset: 16)
!1620 = !DIDerivedType(tag: DW_TAG_member, name: "sin6_flowinfo", scope: !1616, file: !88, line: 258, baseType: !92, size: 32, align: 32, offset: 32)
!1621 = !DIDerivedType(tag: DW_TAG_member, name: "sin6_addr", scope: !1616, file: !88, line: 259, baseType: !1622, size: 128, align: 32, offset: 64)
!1622 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "in6_addr", file: !88, line: 211, size: 128, align: 32, elements: !1623)
!1623 = !{!1624}
!1624 = !DIDerivedType(tag: DW_TAG_member, name: "__in6_u", scope: !1622, file: !88, line: 220, baseType: !1625, size: 128, align: 32)
!1625 = distinct !DICompositeType(tag: DW_TAG_union_type, scope: !1622, file: !88, line: 213, size: 128, align: 32, elements: !1626)
!1626 = !{!1627, !1632, !1634}
!1627 = !DIDerivedType(tag: DW_TAG_member, name: "__u6_addr8", scope: !1625, file: !88, line: 215, baseType: !1628, size: 128, align: 8)
!1628 = !DICompositeType(tag: DW_TAG_array_type, baseType: !1629, size: 128, align: 8, elements: !1630)
!1629 = !DIDerivedType(tag: DW_TAG_typedef, name: "uint8_t", file: !93, line: 48, baseType: !227)
!1630 = !{!1631}
!1631 = !DISubrange(count: 16)
!1632 = !DIDerivedType(tag: DW_TAG_member, name: "__u6_addr16", scope: !1625, file: !88, line: 217, baseType: !1633, size: 128, align: 16)
!1633 = !DICompositeType(tag: DW_TAG_array_type, baseType: !220, size: 128, align: 16, elements: !228)
!1634 = !DIDerivedType(tag: DW_TAG_member, name: "__u6_addr32", scope: !1625, file: !88, line: 218, baseType: !1635, size: 128, align: 32)
!1635 = !DICompositeType(tag: DW_TAG_array_type, baseType: !92, size: 128, align: 32, elements: !1636)
!1636 = !{!1637}
!1637 = !DISubrange(count: 4)
!1638 = !DIDerivedType(tag: DW_TAG_member, name: "sin6_scope_id", scope: !1616, file: !88, line: 260, baseType: !92, size: 32, align: 32, offset: 192)
!1639 = !DIDerivedType(tag: DW_TAG_member, name: "_initstamp", scope: !1603, file: !119, line: 145, baseType: !1640, size: 64, align: 32, offset: 288)
!1640 = !DICompositeType(tag: DW_TAG_array_type, baseType: !94, size: 64, align: 32, elements: !13)
!1641 = !DILocation(line: 119, column: 23, scope: !1524)
!1642 = !DILocation(line: 121, column: 4, scope: !1524)
!1643 = !DILocation(line: 122, column: 11, scope: !1524)
!1644 = !DILocation(line: 122, column: 10, scope: !1524)
!1645 = !DILocation(line: 124, column: 7, scope: !1646)
!1646 = distinct !DILexicalBlock(scope: !1524, file: !97, line: 124, column: 7)
!1647 = !DILocation(line: 124, column: 14, scope: !1646)
!1648 = !DILocation(line: 124, column: 7, scope: !1524)
!1649 = !DILocalVariable(name: "dns_ip", scope: !1650, file: !97, line: 126, type: !222)
!1650 = distinct !DILexicalBlock(scope: !1646, file: !97, line: 125, column: 6)
!1651 = !DILocation(line: 126, column: 22, scope: !1650)
!1652 = !DILocation(line: 128, column: 29, scope: !1650)
!1653 = !DILocation(line: 128, column: 14, scope: !1650)
!1654 = !DILocation(line: 128, column: 13, scope: !1650)
!1655 = !DILocation(line: 129, column: 10, scope: !1656)
!1656 = distinct !DILexicalBlock(scope: !1650, file: !97, line: 129, column: 10)
!1657 = !DILocation(line: 129, column: 16, scope: !1656)
!1658 = !DILocation(line: 129, column: 10, scope: !1650)
!1659 = !DILocalVariable(name: "dns_response", scope: !1660, file: !97, line: 135, type: !1661)
!1660 = distinct !DILexicalBlock(scope: !1656, file: !97, line: 130, column: 9)
!1661 = distinct !DICompositeType(tag: DW_TAG_union_type, scope: !1524, file: !97, line: 131, size: 4096, align: 32, elements: !1662)
!1662 = !{!1663, !1683}
!1663 = !DIDerivedType(tag: DW_TAG_member, name: "hdr", scope: !1661, file: !97, line: 133, baseType: !1664, size: 96, align: 32)
!1664 = !DIDerivedType(tag: DW_TAG_typedef, name: "HEADER", file: !1665, line: 83, baseType: !1666)
!1665 = !DIFile(filename: "/home/zrz0517/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/libc/usr/include/arpa/nameser_compat.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/alarm4pi-cb")
!1666 = distinct !DICompositeType(tag: DW_TAG_structure_type, file: !1665, line: 48, size: 96, align: 32, elements: !1667)
!1667 = !{!1668, !1669, !1670, !1671, !1672, !1673, !1674, !1675, !1676, !1677, !1678, !1679, !1680, !1681, !1682}
!1668 = !DIDerivedType(tag: DW_TAG_member, name: "id", scope: !1666, file: !1665, line: 49, baseType: !94, size: 16, align: 32, flags: DIFlagBitField, extraData: i64 0)
!1669 = !DIDerivedType(tag: DW_TAG_member, name: "rd", scope: !1666, file: !1665, line: 66, baseType: !94, size: 1, align: 32, offset: 16, flags: DIFlagBitField, extraData: i64 0)
!1670 = !DIDerivedType(tag: DW_TAG_member, name: "tc", scope: !1666, file: !1665, line: 67, baseType: !94, size: 1, align: 32, offset: 17, flags: DIFlagBitField, extraData: i64 0)
!1671 = !DIDerivedType(tag: DW_TAG_member, name: "aa", scope: !1666, file: !1665, line: 68, baseType: !94, size: 1, align: 32, offset: 18, flags: DIFlagBitField, extraData: i64 0)
!1672 = !DIDerivedType(tag: DW_TAG_member, name: "opcode", scope: !1666, file: !1665, line: 69, baseType: !94, size: 4, align: 32, offset: 19, flags: DIFlagBitField, extraData: i64 0)
!1673 = !DIDerivedType(tag: DW_TAG_member, name: "qr", scope: !1666, file: !1665, line: 70, baseType: !94, size: 1, align: 32, offset: 23, flags: DIFlagBitField, extraData: i64 0)
!1674 = !DIDerivedType(tag: DW_TAG_member, name: "rcode", scope: !1666, file: !1665, line: 72, baseType: !94, size: 4, align: 32, offset: 24, flags: DIFlagBitField, extraData: i64 0)
!1675 = !DIDerivedType(tag: DW_TAG_member, name: "cd", scope: !1666, file: !1665, line: 73, baseType: !94, size: 1, align: 32, offset: 28, flags: DIFlagBitField, extraData: i64 0)
!1676 = !DIDerivedType(tag: DW_TAG_member, name: "ad", scope: !1666, file: !1665, line: 74, baseType: !94, size: 1, align: 32, offset: 29, flags: DIFlagBitField, extraData: i64 0)
!1677 = !DIDerivedType(tag: DW_TAG_member, name: "unused", scope: !1666, file: !1665, line: 75, baseType: !94, size: 1, align: 32, offset: 30, flags: DIFlagBitField, extraData: i64 0)
!1678 = !DIDerivedType(tag: DW_TAG_member, name: "ra", scope: !1666, file: !1665, line: 76, baseType: !94, size: 1, align: 32, offset: 31, flags: DIFlagBitField, extraData: i64 0)
!1679 = !DIDerivedType(tag: DW_TAG_member, name: "qdcount", scope: !1666, file: !1665, line: 79, baseType: !94, size: 16, align: 32, offset: 32, flags: DIFlagBitField, extraData: i64 0)
!1680 = !DIDerivedType(tag: DW_TAG_member, name: "ancount", scope: !1666, file: !1665, line: 80, baseType: !94, size: 16, align: 32, offset: 48, flags: DIFlagBitField, extraData: i64 0)
!1681 = !DIDerivedType(tag: DW_TAG_member, name: "nscount", scope: !1666, file: !1665, line: 81, baseType: !94, size: 16, align: 32, offset: 64, flags: DIFlagBitField, extraData: i64 0)
!1682 = !DIDerivedType(tag: DW_TAG_member, name: "arcount", scope: !1666, file: !1665, line: 82, baseType: !94, size: 16, align: 32, offset: 80, flags: DIFlagBitField, extraData: i64 0)
!1683 = !DIDerivedType(tag: DW_TAG_member, name: "buf", scope: !1661, file: !97, line: 134, baseType: !1684, size: 4096, align: 8)
!1684 = !DICompositeType(tag: DW_TAG_array_type, baseType: !231, size: 4096, align: 8, elements: !1685)
!1685 = !{!1686}
!1686 = !DISubrange(count: 512)
!1687 = !DILocation(line: 135, column: 14, scope: !1660)
!1688 = !DILocalVariable(name: "dns_response_len", scope: !1660, file: !97, line: 136, type: !12)
!1689 = !DILocation(line: 136, column: 14, scope: !1660)
!1690 = !DILocalVariable(name: "saved_dns_addr", scope: !1660, file: !97, line: 138, type: !1691)
!1691 = !DICompositeType(tag: DW_TAG_array_type, baseType: !222, size: 96, align: 32, elements: !1546)
!1692 = !DILocation(line: 138, column: 25, scope: !1660)
!1693 = !DILocalVariable(name: "saved_dns_count", scope: !1660, file: !97, line: 139, type: !12)
!1694 = !DILocation(line: 139, column: 14, scope: !1660)
!1695 = !DILocalVariable(name: "saved_res_options", scope: !1660, file: !97, line: 140, type: !248)
!1696 = !DILocation(line: 140, column: 15, scope: !1660)
!1697 = !DILocalVariable(name: "n_dns_addr", scope: !1660, file: !97, line: 142, type: !12)
!1698 = !DILocation(line: 142, column: 14, scope: !1660)
!1699 = !DILocation(line: 146, column: 37, scope: !1660)
!1700 = !DILocation(line: 146, column: 26, scope: !1660)
!1701 = !DILocation(line: 147, column: 25, scope: !1702)
!1702 = distinct !DILexicalBlock(scope: !1660, file: !97, line: 147, column: 10)
!1703 = !DILocation(line: 147, column: 14, scope: !1702)
!1704 = !DILocation(line: 147, column: 29, scope: !1705)
!1705 = !DILexicalBlockFile(scope: !1706, file: !97, discriminator: 1)
!1706 = distinct !DILexicalBlock(scope: !1702, file: !97, line: 147, column: 10)
!1707 = !DILocation(line: 147, column: 42, scope: !1705)
!1708 = !DILocation(line: 147, column: 40, scope: !1705)
!1709 = !DILocation(line: 147, column: 10, scope: !1705)
!1710 = !DILocation(line: 148, column: 28, scope: !1706)
!1711 = !DILocation(line: 148, column: 13, scope: !1706)
!1712 = !DILocation(line: 148, column: 63, scope: !1706)
!1713 = !DILocation(line: 148, column: 51, scope: !1706)
!1714 = !DILocation(line: 148, column: 42, scope: !1706)
!1715 = !DILocation(line: 148, column: 75, scope: !1706)
!1716 = !DILocation(line: 147, column: 68, scope: !1717)
!1717 = !DILexicalBlockFile(scope: !1706, file: !97, discriminator: 2)
!1718 = !DILocation(line: 147, column: 10, scope: !1717)
!1719 = distinct !{!1719, !1720}
!1720 = !DILocation(line: 147, column: 10, scope: !1660)
!1721 = !DILocation(line: 149, column: 37, scope: !1660)
!1722 = !DILocation(line: 149, column: 27, scope: !1660)
!1723 = !DILocation(line: 152, column: 19, scope: !1660)
!1724 = !DILocation(line: 152, column: 27, scope: !1660)
!1725 = !DILocation(line: 155, column: 19, scope: !1660)
!1726 = !DILocation(line: 155, column: 10, scope: !1660)
!1727 = !DILocation(line: 155, column: 34, scope: !1660)
!1728 = !DILocation(line: 155, column: 43, scope: !1660)
!1729 = !DILocation(line: 156, column: 19, scope: !1660)
!1730 = !DILocation(line: 156, column: 27, scope: !1660)
!1731 = !DILocation(line: 162, column: 51, scope: !1660)
!1732 = !DILocation(line: 162, column: 81, scope: !1660)
!1733 = !DILocation(line: 162, column: 29, scope: !1660)
!1734 = !DILocation(line: 162, column: 27, scope: !1660)
!1735 = !DILocation(line: 163, column: 13, scope: !1736)
!1736 = distinct !DILexicalBlock(scope: !1660, file: !97, line: 163, column: 13)
!1737 = !DILocation(line: 163, column: 30, scope: !1736)
!1738 = !DILocation(line: 163, column: 13, scope: !1660)
!1739 = !DILocalVariable(name: "resp_handle", scope: !1740, file: !97, line: 165, type: !1741)
!1740 = distinct !DILexicalBlock(scope: !1736, file: !97, line: 164, column: 12)
!1741 = !DIDerivedType(tag: DW_TAG_typedef, name: "ns_msg", file: !100, line: 121, baseType: !1742)
!1742 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "__ns_msg", file: !100, line: 114, size: 384, align: 32, elements: !1743)
!1743 = !{!1744, !1745, !1746, !1747, !1748, !1750, !1752, !1754, !1755}
!1744 = !DIDerivedType(tag: DW_TAG_member, name: "_msg", scope: !1742, file: !100, line: 115, baseType: !1580, size: 32, align: 32)
!1745 = !DIDerivedType(tag: DW_TAG_member, name: "_eom", scope: !1742, file: !100, line: 115, baseType: !1580, size: 32, align: 32, offset: 32)
!1746 = !DIDerivedType(tag: DW_TAG_member, name: "_id", scope: !1742, file: !100, line: 116, baseType: !1606, size: 16, align: 16, offset: 64)
!1747 = !DIDerivedType(tag: DW_TAG_member, name: "_flags", scope: !1742, file: !100, line: 116, baseType: !1606, size: 16, align: 16, offset: 80)
!1748 = !DIDerivedType(tag: DW_TAG_member, name: "_counts", scope: !1742, file: !100, line: 116, baseType: !1749, size: 64, align: 16, offset: 96)
!1749 = !DICompositeType(tag: DW_TAG_array_type, baseType: !1606, size: 64, align: 16, elements: !1636)
!1750 = !DIDerivedType(tag: DW_TAG_member, name: "_sections", scope: !1742, file: !100, line: 117, baseType: !1751, size: 128, align: 32, offset: 160)
!1751 = !DICompositeType(tag: DW_TAG_array_type, baseType: !1580, size: 128, align: 32, elements: !1636)
!1752 = !DIDerivedType(tag: DW_TAG_member, name: "_sect", scope: !1742, file: !100, line: 118, baseType: !1753, size: 32, align: 32, offset: 288)
!1753 = !DIDerivedType(tag: DW_TAG_typedef, name: "ns_sect", file: !100, line: 107, baseType: !190)
!1754 = !DIDerivedType(tag: DW_TAG_member, name: "_rrnum", scope: !1742, file: !100, line: 119, baseType: !12, size: 32, align: 32, offset: 320)
!1755 = !DIDerivedType(tag: DW_TAG_member, name: "_msg_ptr", scope: !1742, file: !100, line: 120, baseType: !1580, size: 32, align: 32, offset: 352)
!1756 = !DILocation(line: 165, column: 20, scope: !1740)
!1757 = !DILocation(line: 169, column: 46, scope: !1740)
!1758 = !DILocation(line: 169, column: 33, scope: !1740)
!1759 = !DILocation(line: 169, column: 51, scope: !1740)
!1760 = !DILocation(line: 169, column: 20, scope: !1740)
!1761 = !DILocation(line: 169, column: 19, scope: !1740)
!1762 = !DILocation(line: 170, column: 17, scope: !1763)
!1763 = distinct !DILexicalBlock(scope: !1740, file: !97, line: 170, column: 17)
!1764 = !DILocation(line: 170, column: 24, scope: !1763)
!1765 = !DILocation(line: 170, column: 17, scope: !1740)
!1766 = !DILocalVariable(name: "resp_error_code", scope: !1767, file: !97, line: 172, type: !12)
!1767 = distinct !DILexicalBlock(scope: !1763, file: !97, line: 171, column: 15)
!1768 = !DILocation(line: 172, column: 20, scope: !1767)
!1769 = !DILocation(line: 174, column: 32, scope: !1767)
!1770 = !DILocation(line: 174, column: 31, scope: !1767)
!1771 = !DILocation(line: 175, column: 19, scope: !1772)
!1772 = distinct !DILexicalBlock(scope: !1767, file: !97, line: 175, column: 19)
!1773 = !DILocation(line: 175, column: 35, scope: !1772)
!1774 = !DILocation(line: 175, column: 19, scope: !1767)
!1775 = !DILocalVariable(name: "answer_count", scope: !1776, file: !97, line: 177, type: !220)
!1776 = distinct !DILexicalBlock(scope: !1772, file: !97, line: 176, column: 18)
!1777 = !DILocation(line: 177, column: 28, scope: !1776)
!1778 = !DILocation(line: 181, column: 32, scope: !1776)
!1779 = !DILocation(line: 181, column: 31, scope: !1776)
!1780 = !DILocation(line: 182, column: 22, scope: !1781)
!1781 = distinct !DILexicalBlock(scope: !1776, file: !97, line: 182, column: 22)
!1782 = !DILocation(line: 182, column: 35, scope: !1781)
!1783 = !DILocation(line: 182, column: 22, scope: !1776)
!1784 = !DILocalVariable(name: "resp_record", scope: !1785, file: !97, line: 184, type: !1786)
!1785 = distinct !DILexicalBlock(scope: !1781, file: !97, line: 183, column: 21)
!1786 = !DIDerivedType(tag: DW_TAG_typedef, name: "ns_rr", file: !100, line: 145, baseType: !1787)
!1787 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "__ns_rr", file: !100, line: 138, size: 8352, align: 32, elements: !1788)
!1788 = !{!1789, !1793, !1794, !1795, !1796, !1797}
!1789 = !DIDerivedType(tag: DW_TAG_member, name: "name", scope: !1787, file: !100, line: 139, baseType: !1790, size: 8200, align: 8)
!1790 = !DICompositeType(tag: DW_TAG_array_type, baseType: !19, size: 8200, align: 8, elements: !1791)
!1791 = !{!1792}
!1792 = !DISubrange(count: 1025)
!1793 = !DIDerivedType(tag: DW_TAG_member, name: "type", scope: !1787, file: !100, line: 140, baseType: !1606, size: 16, align: 16, offset: 8208)
!1794 = !DIDerivedType(tag: DW_TAG_member, name: "rr_class", scope: !1787, file: !100, line: 141, baseType: !1606, size: 16, align: 16, offset: 8224)
!1795 = !DIDerivedType(tag: DW_TAG_member, name: "ttl", scope: !1787, file: !100, line: 142, baseType: !1568, size: 32, align: 32, offset: 8256)
!1796 = !DIDerivedType(tag: DW_TAG_member, name: "rdlength", scope: !1787, file: !100, line: 143, baseType: !1606, size: 16, align: 16, offset: 8288)
!1797 = !DIDerivedType(tag: DW_TAG_member, name: "rdata", scope: !1787, file: !100, line: 144, baseType: !1580, size: 32, align: 32, offset: 8320)
!1798 = !DILocation(line: 184, column: 28, scope: !1785)
!1799 = !DILocation(line: 187, column: 29, scope: !1785)
!1800 = !DILocation(line: 187, column: 28, scope: !1785)
!1801 = !DILocation(line: 188, column: 26, scope: !1802)
!1802 = distinct !DILexicalBlock(scope: !1785, file: !97, line: 188, column: 26)
!1803 = !DILocation(line: 188, column: 32, scope: !1802)
!1804 = !DILocation(line: 188, column: 26, scope: !1785)
!1805 = !DILocalVariable(name: "resp_type", scope: !1806, file: !97, line: 190, type: !1606)
!1806 = distinct !DILexicalBlock(scope: !1802, file: !97, line: 189, column: 24)
!1807 = !DILocation(line: 190, column: 35, scope: !1806)
!1808 = !DILocation(line: 192, column: 37, scope: !1806)
!1809 = !DILocation(line: 192, column: 35, scope: !1806)
!1810 = !DILocation(line: 195, column: 29, scope: !1811)
!1811 = distinct !DILexicalBlock(scope: !1806, file: !97, line: 195, column: 29)
!1812 = !DILocation(line: 195, column: 39, scope: !1811)
!1813 = !DILocation(line: 195, column: 29, scope: !1806)
!1814 = !DILocalVariable(name: "record_data", scope: !1815, file: !97, line: 197, type: !230)
!1815 = distinct !DILexicalBlock(scope: !1811, file: !97, line: 196, column: 27)
!1816 = !DILocation(line: 197, column: 36, scope: !1815)
!1817 = !DILocalVariable(name: "rec_disp_buf", scope: !1815, file: !97, line: 198, type: !1554)
!1818 = !DILocation(line: 198, column: 33, scope: !1815)
!1819 = !DILocation(line: 200, column: 80, scope: !1815)
!1820 = !DILocation(line: 200, column: 28, scope: !1815)
!1821 = !DILocation(line: 201, column: 28, scope: !1815)
!1822 = !DILocation(line: 203, column: 52, scope: !1815)
!1823 = !DILocation(line: 203, column: 40, scope: !1815)
!1824 = !DILocation(line: 205, column: 29, scope: !1815)
!1825 = !DILocation(line: 205, column: 58, scope: !1815)
!1826 = !DILocation(line: 205, column: 39, scope: !1815)
!1827 = !DILocation(line: 206, column: 34, scope: !1815)
!1828 = !DILocation(line: 207, column: 27, scope: !1815)
!1829 = !DILocation(line: 210, column: 28, scope: !1830)
!1830 = distinct !DILexicalBlock(scope: !1811, file: !97, line: 209, column: 27)
!1831 = !DILocation(line: 210, column: 28, scope: !1832)
!1832 = !DILexicalBlockFile(scope: !1830, file: !97, discriminator: 1)
!1833 = !DILocation(line: 211, column: 34, scope: !1830)
!1834 = !DILocation(line: 213, column: 24, scope: !1806)
!1835 = !DILocation(line: 216, column: 25, scope: !1836)
!1836 = distinct !DILexicalBlock(scope: !1802, file: !97, line: 215, column: 24)
!1837 = !DILocation(line: 216, column: 25, scope: !1838)
!1838 = !DILexicalBlockFile(scope: !1836, file: !97, discriminator: 1)
!1839 = !DILocation(line: 216, column: 25, scope: !1840)
!1840 = !DILexicalBlockFile(scope: !1836, file: !97, discriminator: 2)
!1841 = !DILocation(line: 218, column: 21, scope: !1785)
!1842 = !DILocation(line: 221, column: 22, scope: !1843)
!1843 = distinct !DILexicalBlock(scope: !1781, file: !97, line: 220, column: 21)
!1844 = !DILocation(line: 221, column: 22, scope: !1845)
!1845 = !DILexicalBlockFile(scope: !1843, file: !97, discriminator: 1)
!1846 = !DILocation(line: 222, column: 28, scope: !1843)
!1847 = !DILocation(line: 224, column: 18, scope: !1776)
!1848 = !DILocation(line: 227, column: 19, scope: !1849)
!1849 = distinct !DILexicalBlock(scope: !1772, file: !97, line: 226, column: 18)
!1850 = !DILocation(line: 227, column: 19, scope: !1851)
!1851 = !DILexicalBlockFile(scope: !1849, file: !97, discriminator: 1)
!1852 = !DILocation(line: 227, column: 19, scope: !1853)
!1853 = !DILexicalBlockFile(scope: !1849, file: !97, discriminator: 2)
!1854 = !DILocation(line: 228, column: 25, scope: !1849)
!1855 = !DILocation(line: 230, column: 15, scope: !1767)
!1856 = !DILocation(line: 233, column: 16, scope: !1857)
!1857 = distinct !DILexicalBlock(scope: !1763, file: !97, line: 232, column: 15)
!1858 = !DILocation(line: 233, column: 16, scope: !1859)
!1859 = !DILexicalBlockFile(scope: !1857, file: !97, discriminator: 1)
!1860 = !DILocation(line: 233, column: 16, scope: !1861)
!1861 = !DILexicalBlockFile(scope: !1857, file: !97, discriminator: 2)
!1862 = !DILocation(line: 235, column: 12, scope: !1740)
!1863 = !DILocation(line: 238, column: 16, scope: !1864)
!1864 = distinct !DILexicalBlock(scope: !1865, file: !97, line: 238, column: 16)
!1865 = distinct !DILexicalBlock(scope: !1736, file: !97, line: 237, column: 12)
!1866 = !DILocation(line: 238, column: 22, scope: !1864)
!1867 = !DILocation(line: 238, column: 16, scope: !1865)
!1868 = !DILocation(line: 239, column: 16, scope: !1864)
!1869 = !DILocation(line: 239, column: 16, scope: !1870)
!1870 = !DILexicalBlockFile(scope: !1864, file: !97, discriminator: 1)
!1871 = !DILocation(line: 241, column: 16, scope: !1864)
!1872 = !DILocation(line: 241, column: 16, scope: !1870)
!1873 = !DILocation(line: 241, column: 16, scope: !1874)
!1874 = !DILexicalBlockFile(scope: !1864, file: !97, discriminator: 2)
!1875 = !DILocation(line: 241, column: 16, scope: !1876)
!1876 = !DILexicalBlockFile(scope: !1864, file: !97, discriminator: 3)
!1877 = !DILocation(line: 241, column: 16, scope: !1878)
!1878 = !DILexicalBlockFile(scope: !1864, file: !97, discriminator: 4)
!1879 = !DILocation(line: 242, column: 19, scope: !1865)
!1880 = !DILocation(line: 245, column: 29, scope: !1660)
!1881 = !DILocation(line: 245, column: 19, scope: !1660)
!1882 = !DILocation(line: 245, column: 27, scope: !1660)
!1883 = !DILocation(line: 246, column: 29, scope: !1660)
!1884 = !DILocation(line: 246, column: 19, scope: !1660)
!1885 = !DILocation(line: 246, column: 27, scope: !1660)
!1886 = !DILocation(line: 247, column: 25, scope: !1887)
!1887 = distinct !DILexicalBlock(scope: !1660, file: !97, line: 247, column: 10)
!1888 = !DILocation(line: 247, column: 14, scope: !1887)
!1889 = !DILocation(line: 247, column: 29, scope: !1890)
!1890 = !DILexicalBlockFile(scope: !1891, file: !97, discriminator: 1)
!1891 = distinct !DILexicalBlock(scope: !1887, file: !97, line: 247, column: 10)
!1892 = !DILocation(line: 247, column: 42, scope: !1890)
!1893 = !DILocation(line: 247, column: 40, scope: !1890)
!1894 = !DILocation(line: 247, column: 10, scope: !1890)
!1895 = !DILocation(line: 248, column: 34, scope: !1891)
!1896 = !DILocation(line: 248, column: 22, scope: !1891)
!1897 = !DILocation(line: 248, column: 13, scope: !1891)
!1898 = !DILocation(line: 248, column: 46, scope: !1891)
!1899 = !DILocation(line: 248, column: 72, scope: !1891)
!1900 = !DILocation(line: 248, column: 57, scope: !1891)
!1901 = !DILocation(line: 247, column: 68, scope: !1902)
!1902 = !DILexicalBlockFile(scope: !1891, file: !97, discriminator: 2)
!1903 = !DILocation(line: 247, column: 10, scope: !1902)
!1904 = distinct !{!1904, !1905}
!1905 = !DILocation(line: 247, column: 10, scope: !1660)
!1906 = !DILocation(line: 249, column: 9, scope: !1660)
!1907 = !DILocation(line: 250, column: 6, scope: !1650)
!1908 = !DILocation(line: 253, column: 7, scope: !1909)
!1909 = distinct !DILexicalBlock(scope: !1646, file: !97, line: 252, column: 6)
!1910 = !DILocation(line: 253, column: 7, scope: !1911)
!1911 = !DILexicalBlockFile(scope: !1909, file: !97, discriminator: 1)
!1912 = !DILocation(line: 255, column: 11, scope: !1524)
!1913 = !DILocation(line: 255, column: 4, scope: !1524)
!1914 = distinct !DISubprogram(name: "get_public_ip", scope: !97, file: !97, line: 259, type: !568, isLocal: false, isDefinition: true, scopeLine: 260, flags: DIFlagPrototyped, isOptimized: false, unit: !96, variables: !2)
!1915 = !DILocalVariable(name: "public_ip", arg: 1, scope: !1914, file: !97, line: 259, type: !18)
!1916 = !DILocation(line: 259, column: 25, scope: !1914)
!1917 = !DILocalVariable(name: "fn_ret", scope: !1914, file: !97, line: 261, type: !12)
!1918 = !DILocation(line: 261, column: 8, scope: !1914)
!1919 = !DILocalVariable(name: "public_ip_addr", scope: !1914, file: !97, line: 262, type: !222)
!1920 = !DILocation(line: 262, column: 19, scope: !1914)
!1921 = !DILocation(line: 264, column: 11, scope: !1914)
!1922 = !DILocation(line: 264, column: 10, scope: !1914)
!1923 = !DILocation(line: 265, column: 7, scope: !1924)
!1924 = distinct !DILexicalBlock(scope: !1914, file: !97, line: 265, column: 7)
!1925 = !DILocation(line: 265, column: 13, scope: !1924)
!1926 = !DILocation(line: 265, column: 7, scope: !1914)
!1927 = !DILocation(line: 266, column: 15, scope: !1924)
!1928 = !DILocation(line: 266, column: 26, scope: !1924)
!1929 = !DILocation(line: 266, column: 8, scope: !1930)
!1930 = !DILexicalBlockFile(scope: !1924, file: !97, discriminator: 1)
!1931 = !DILocation(line: 266, column: 8, scope: !1924)
!1932 = !DILocation(line: 268, column: 12, scope: !1914)
!1933 = !DILocation(line: 268, column: 5, scope: !1914)
!1934 = distinct !DISubprogram(name: "get_current_exec_path", scope: !236, file: !236, line: 19, type: !1935, isLocal: false, isDefinition: true, scopeLine: 20, flags: DIFlagPrototyped, isOptimized: false, unit: !235, variables: !2)
!1935 = !DISubroutineType(types: !1936)
!1936 = !{!12, !18, !311}
!1937 = !DILocalVariable(name: "exec_path", arg: 1, scope: !1934, file: !236, line: 19, type: !18)
!1938 = !DILocation(line: 19, column: 33, scope: !1934)
!1939 = !DILocalVariable(name: "path_buff_len", arg: 2, scope: !1934, file: !236, line: 19, type: !311)
!1940 = !DILocation(line: 19, column: 51, scope: !1934)
!1941 = !DILocalVariable(name: "ret_error", scope: !1934, file: !236, line: 21, type: !12)
!1942 = !DILocation(line: 21, column: 8, scope: !1934)
!1943 = !DILocation(line: 22, column: 7, scope: !1944)
!1944 = distinct !DILexicalBlock(scope: !1934, file: !236, line: 22, column: 7)
!1945 = !DILocation(line: 22, column: 21, scope: !1944)
!1946 = !DILocation(line: 22, column: 7, scope: !1934)
!1947 = !DILocalVariable(name: "exec_path_buff", scope: !1948, file: !236, line: 24, type: !830)
!1948 = distinct !DILexicalBlock(scope: !1944, file: !236, line: 23, column: 6)
!1949 = !DILocation(line: 24, column: 12, scope: !1948)
!1950 = !DILocalVariable(name: "chars_written", scope: !1948, file: !236, line: 25, type: !311)
!1951 = !DILocation(line: 25, column: 14, scope: !1948)
!1952 = !DILocation(line: 27, column: 48, scope: !1948)
!1953 = !DILocation(line: 27, column: 21, scope: !1948)
!1954 = !DILocation(line: 27, column: 20, scope: !1948)
!1955 = !DILocation(line: 28, column: 10, scope: !1956)
!1956 = distinct !DILexicalBlock(scope: !1948, file: !236, line: 28, column: 10)
!1957 = !DILocation(line: 28, column: 24, scope: !1956)
!1958 = !DILocation(line: 28, column: 10, scope: !1948)
!1959 = !DILocalVariable(name: "exec_dir", scope: !1960, file: !236, line: 30, type: !18)
!1960 = distinct !DILexicalBlock(scope: !1956, file: !236, line: 29, column: 9)
!1961 = !DILocation(line: 30, column: 16, scope: !1960)
!1962 = !DILocation(line: 31, column: 25, scope: !1960)
!1963 = !DILocation(line: 31, column: 10, scope: !1960)
!1964 = !DILocation(line: 31, column: 39, scope: !1960)
!1965 = !DILocation(line: 32, column: 27, scope: !1960)
!1966 = !DILocation(line: 32, column: 19, scope: !1960)
!1967 = !DILocation(line: 32, column: 18, scope: !1960)
!1968 = !DILocation(line: 33, column: 13, scope: !1969)
!1969 = distinct !DILexicalBlock(scope: !1960, file: !236, line: 33, column: 13)
!1970 = !DILocation(line: 33, column: 36, scope: !1969)
!1971 = !DILocation(line: 33, column: 29, scope: !1969)
!1972 = !DILocation(line: 33, column: 45, scope: !1969)
!1973 = !DILocation(line: 33, column: 27, scope: !1969)
!1974 = !DILocation(line: 33, column: 13, scope: !1960)
!1975 = !DILocation(line: 35, column: 20, scope: !1976)
!1976 = distinct !DILexicalBlock(scope: !1969, file: !236, line: 34, column: 12)
!1977 = !DILocation(line: 35, column: 30, scope: !1976)
!1978 = !DILocation(line: 35, column: 13, scope: !1976)
!1979 = !DILocation(line: 36, column: 20, scope: !1976)
!1980 = !DILocation(line: 36, column: 13, scope: !1976)
!1981 = !DILocation(line: 37, column: 22, scope: !1976)
!1982 = !DILocation(line: 38, column: 12, scope: !1976)
!1983 = !DILocation(line: 41, column: 13, scope: !1984)
!1984 = distinct !DILexicalBlock(scope: !1969, file: !236, line: 40, column: 12)
!1985 = !DILocation(line: 41, column: 25, scope: !1984)
!1986 = !DILocation(line: 42, column: 22, scope: !1984)
!1987 = !DILocation(line: 44, column: 9, scope: !1960)
!1988 = !DILocation(line: 47, column: 10, scope: !1989)
!1989 = distinct !DILexicalBlock(scope: !1956, file: !236, line: 46, column: 9)
!1990 = !DILocation(line: 47, column: 22, scope: !1989)
!1991 = !DILocation(line: 48, column: 20, scope: !1989)
!1992 = !DILocation(line: 48, column: 19, scope: !1989)
!1993 = !DILocation(line: 50, column: 6, scope: !1948)
!1994 = !DILocation(line: 52, column: 16, scope: !1944)
!1995 = !DILocation(line: 53, column: 11, scope: !1934)
!1996 = !DILocation(line: 53, column: 4, scope: !1934)
!1997 = distinct !DISubprogram(name: "kill_processes", scope: !236, file: !236, line: 56, type: !1998, isLocal: false, isDefinition: true, scopeLine: 57, flags: DIFlagPrototyped, isOptimized: false, unit: !235, variables: !2)
!1998 = !DISubroutineType(types: !1999)
!1999 = !{null, !2000, !311}
!2000 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !8, size: 32, align: 32)
!2001 = !DILocalVariable(name: "process_ids", arg: 1, scope: !1997, file: !236, line: 56, type: !2000)
!2002 = !DILocation(line: 56, column: 28, scope: !1997)
!2003 = !DILocalVariable(name: "n_processes", arg: 2, scope: !1997, file: !236, line: 56, type: !311)
!2004 = !DILocation(line: 56, column: 48, scope: !1997)
!2005 = !DILocalVariable(name: "n_child", scope: !1997, file: !236, line: 58, type: !12)
!2006 = !DILocation(line: 58, column: 8, scope: !1997)
!2007 = !DILocation(line: 59, column: 15, scope: !2008)
!2008 = distinct !DILexicalBlock(scope: !1997, file: !236, line: 59, column: 4)
!2009 = !DILocation(line: 59, column: 8, scope: !2008)
!2010 = !DILocation(line: 59, column: 18, scope: !2011)
!2011 = !DILexicalBlockFile(scope: !2012, file: !236, discriminator: 1)
!2012 = distinct !DILexicalBlock(scope: !2008, file: !236, line: 59, column: 4)
!2013 = !DILocation(line: 59, column: 26, scope: !2011)
!2014 = !DILocation(line: 59, column: 25, scope: !2011)
!2015 = !DILocation(line: 59, column: 4, scope: !2011)
!2016 = !DILocation(line: 60, column: 22, scope: !2017)
!2017 = distinct !DILexicalBlock(scope: !2012, file: !236, line: 60, column: 10)
!2018 = !DILocation(line: 60, column: 10, scope: !2017)
!2019 = !DILocation(line: 60, column: 31, scope: !2017)
!2020 = !DILocation(line: 60, column: 10, scope: !2012)
!2021 = !DILocation(line: 61, column: 27, scope: !2017)
!2022 = !DILocation(line: 61, column: 15, scope: !2017)
!2023 = !DILocation(line: 61, column: 10, scope: !2017)
!2024 = !DILocation(line: 60, column: 35, scope: !2025)
!2025 = !DILexicalBlockFile(scope: !2017, file: !236, discriminator: 1)
!2026 = !DILocation(line: 59, column: 45, scope: !2027)
!2027 = !DILexicalBlockFile(scope: !2012, file: !236, discriminator: 2)
!2028 = !DILocation(line: 59, column: 4, scope: !2027)
!2029 = distinct !{!2029, !2030}
!2030 = !DILocation(line: 59, column: 4, scope: !1997)
!2031 = !DILocation(line: 62, column: 3, scope: !1997)
!2032 = distinct !DISubprogram(name: "wait_processes", scope: !236, file: !236, line: 64, type: !2033, isLocal: false, isDefinition: true, scopeLine: 65, flags: DIFlagPrototyped, isOptimized: false, unit: !235, variables: !2)
!2033 = !DISubroutineType(types: !2034)
!2034 = !{!12, !2000, !311, !12}
!2035 = !DILocalVariable(name: "process_ids", arg: 1, scope: !2032, file: !236, line: 64, type: !2000)
!2036 = !DILocation(line: 64, column: 27, scope: !2032)
!2037 = !DILocalVariable(name: "n_processes", arg: 2, scope: !2032, file: !236, line: 64, type: !311)
!2038 = !DILocation(line: 64, column: 47, scope: !2032)
!2039 = !DILocalVariable(name: "wait_timeout", arg: 3, scope: !2032, file: !236, line: 64, type: !12)
!2040 = !DILocation(line: 64, column: 64, scope: !2032)
!2041 = !DILocalVariable(name: "ret_error", scope: !2032, file: !236, line: 66, type: !12)
!2042 = !DILocation(line: 66, column: 8, scope: !2032)
!2043 = !DILocalVariable(name: "n_remaining_procs", scope: !2032, file: !236, line: 67, type: !12)
!2044 = !DILocation(line: 67, column: 8, scope: !2032)
!2045 = !DILocation(line: 69, column: 13, scope: !2032)
!2046 = !DILocation(line: 70, column: 4, scope: !2032)
!2047 = distinct !{!2047, !2046}
!2048 = !DILocalVariable(name: "wait_ret", scope: !2049, file: !236, line: 72, type: !12)
!2049 = distinct !DILexicalBlock(scope: !2032, file: !236, line: 71, column: 6)
!2050 = !DILocation(line: 72, column: 11, scope: !2049)
!2051 = !DILocation(line: 74, column: 24, scope: !2049)
!2052 = !DILocation(line: 75, column: 13, scope: !2049)
!2053 = !DILocation(line: 75, column: 7, scope: !2049)
!2054 = !DILocation(line: 76, column: 16, scope: !2049)
!2055 = !DILocation(line: 76, column: 15, scope: !2049)
!2056 = !DILocation(line: 77, column: 10, scope: !2057)
!2057 = distinct !DILexicalBlock(scope: !2049, file: !236, line: 77, column: 10)
!2058 = !DILocation(line: 77, column: 19, scope: !2057)
!2059 = !DILocation(line: 77, column: 10, scope: !2049)
!2060 = !DILocalVariable(name: "n_child", scope: !2061, file: !236, line: 79, type: !12)
!2061 = distinct !DILexicalBlock(scope: !2057, file: !236, line: 78, column: 9)
!2062 = !DILocation(line: 79, column: 14, scope: !2061)
!2063 = !DILocation(line: 81, column: 21, scope: !2064)
!2064 = distinct !DILexicalBlock(scope: !2061, file: !236, line: 81, column: 10)
!2065 = !DILocation(line: 81, column: 14, scope: !2064)
!2066 = !DILocation(line: 81, column: 24, scope: !2067)
!2067 = !DILexicalBlockFile(scope: !2068, file: !236, discriminator: 1)
!2068 = distinct !DILexicalBlock(scope: !2064, file: !236, line: 81, column: 10)
!2069 = !DILocation(line: 81, column: 32, scope: !2067)
!2070 = !DILocation(line: 81, column: 31, scope: !2067)
!2071 = !DILocation(line: 81, column: 10, scope: !2067)
!2072 = !DILocation(line: 82, column: 28, scope: !2073)
!2073 = distinct !DILexicalBlock(scope: !2068, file: !236, line: 82, column: 16)
!2074 = !DILocation(line: 82, column: 16, scope: !2073)
!2075 = !DILocation(line: 82, column: 37, scope: !2073)
!2076 = !DILocation(line: 82, column: 16, scope: !2068)
!2077 = !DILocation(line: 84, column: 31, scope: !2078)
!2078 = distinct !DILexicalBlock(scope: !2079, file: !236, line: 84, column: 19)
!2079 = distinct !DILexicalBlock(scope: !2073, file: !236, line: 83, column: 15)
!2080 = !DILocation(line: 84, column: 19, scope: !2078)
!2081 = !DILocation(line: 84, column: 43, scope: !2078)
!2082 = !DILocation(line: 84, column: 40, scope: !2078)
!2083 = !DILocation(line: 84, column: 19, scope: !2079)
!2084 = !DILocation(line: 86, column: 19, scope: !2085)
!2085 = distinct !DILexicalBlock(scope: !2078, file: !236, line: 85, column: 18)
!2086 = !DILocation(line: 87, column: 31, scope: !2085)
!2087 = !DILocation(line: 87, column: 19, scope: !2085)
!2088 = !DILocation(line: 87, column: 40, scope: !2085)
!2089 = !DILocation(line: 88, column: 17, scope: !2085)
!2090 = !DILocation(line: 90, column: 36, scope: !2078)
!2091 = !DILocation(line: 91, column: 15, scope: !2079)
!2092 = !DILocation(line: 82, column: 41, scope: !2093)
!2093 = !DILexicalBlockFile(scope: !2073, file: !236, discriminator: 1)
!2094 = !DILocation(line: 81, column: 51, scope: !2095)
!2095 = !DILexicalBlockFile(scope: !2068, file: !236, discriminator: 2)
!2096 = !DILocation(line: 81, column: 10, scope: !2095)
!2097 = distinct !{!2097, !2098}
!2098 = !DILocation(line: 81, column: 10, scope: !2061)
!2099 = !DILocation(line: 92, column: 9, scope: !2061)
!2100 = !DILocation(line: 95, column: 20, scope: !2101)
!2101 = distinct !DILexicalBlock(scope: !2057, file: !236, line: 94, column: 9)
!2102 = !DILocation(line: 95, column: 19, scope: !2101)
!2103 = !DILocation(line: 96, column: 10, scope: !2101)
!2104 = !DILocation(line: 96, column: 10, scope: !2105)
!2105 = !DILexicalBlockFile(scope: !2101, file: !236, discriminator: 1)
!2106 = !DILocation(line: 96, column: 10, scope: !2107)
!2107 = !DILexicalBlockFile(scope: !2101, file: !236, discriminator: 2)
!2108 = !DILocation(line: 96, column: 10, scope: !2109)
!2109 = !DILexicalBlockFile(scope: !2101, file: !236, discriminator: 3)
!2110 = !DILocation(line: 98, column: 6, scope: !2049)
!2111 = !DILocation(line: 99, column: 10, scope: !2032)
!2112 = !DILocation(line: 99, column: 28, scope: !2032)
!2113 = !DILocation(line: 98, column: 6, scope: !2114)
!2114 = !DILexicalBlockFile(scope: !2049, file: !236, discriminator: 1)
!2115 = !DILocation(line: 100, column: 11, scope: !2032)
!2116 = !DILocation(line: 100, column: 4, scope: !2032)
!2117 = distinct !DISubprogram(name: "run_background_command", scope: !236, file: !236, line: 103, type: !2118, isLocal: false, isDefinition: true, scopeLine: 104, flags: DIFlagPrototyped, isOptimized: false, unit: !235, variables: !2)
!2118 = !DISubroutineType(types: !2119)
!2119 = !{!12, !2000, !2120, !2122}
!2120 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !2121, size: 32, align: 32)
!2121 = !DIDerivedType(tag: DW_TAG_const_type, baseType: !19)
!2122 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !17, size: 32, align: 32)
!2123 = !DILocalVariable(name: "new_proc_id", arg: 1, scope: !2117, file: !236, line: 103, type: !2000)
!2124 = !DILocation(line: 103, column: 35, scope: !2117)
!2125 = !DILocalVariable(name: "exec_filename", arg: 2, scope: !2117, file: !236, line: 103, type: !2120)
!2126 = !DILocation(line: 103, column: 60, scope: !2117)
!2127 = !DILocalVariable(name: "exec_argv", arg: 3, scope: !2117, file: !236, line: 103, type: !2122)
!2128 = !DILocation(line: 103, column: 87, scope: !2117)
!2129 = !DILocalVariable(name: "ret", scope: !2117, file: !236, line: 105, type: !12)
!2130 = !DILocation(line: 105, column: 8, scope: !2117)
!2131 = !DILocation(line: 107, column: 19, scope: !2117)
!2132 = !DILocation(line: 107, column: 5, scope: !2117)
!2133 = !DILocation(line: 107, column: 17, scope: !2117)
!2134 = !DILocation(line: 109, column: 8, scope: !2135)
!2135 = distinct !DILexicalBlock(scope: !2117, file: !236, line: 109, column: 7)
!2136 = !DILocation(line: 109, column: 7, scope: !2135)
!2137 = !DILocation(line: 109, column: 20, scope: !2135)
!2138 = !DILocation(line: 109, column: 7, scope: !2117)
!2139 = !DILocalVariable(name: "null_fd_rd", scope: !2140, file: !236, line: 111, type: !12)
!2140 = distinct !DILexicalBlock(scope: !2135, file: !236, line: 110, column: 6)
!2141 = !DILocation(line: 111, column: 11, scope: !2140)
!2142 = !DILocation(line: 112, column: 10, scope: !2143)
!2143 = distinct !DILexicalBlock(scope: !2140, file: !236, line: 112, column: 10)
!2144 = !DILocation(line: 112, column: 26, scope: !2143)
!2145 = !DILocation(line: 112, column: 10, scope: !2140)
!2146 = !DILocation(line: 114, column: 25, scope: !2147)
!2147 = distinct !DILexicalBlock(scope: !2148, file: !236, line: 114, column: 13)
!2148 = distinct !DILexicalBlock(scope: !2143, file: !236, line: 113, column: 9)
!2149 = !DILocation(line: 114, column: 18, scope: !2147)
!2150 = !DILocation(line: 114, column: 13, scope: !2151)
!2151 = !DILexicalBlockFile(scope: !2147, file: !236, discriminator: 1)
!2152 = !DILocation(line: 114, column: 58, scope: !2147)
!2153 = !DILocation(line: 114, column: 13, scope: !2148)
!2154 = !DILocation(line: 115, column: 13, scope: !2147)
!2155 = !DILocation(line: 115, column: 13, scope: !2151)
!2156 = !DILocation(line: 116, column: 25, scope: !2157)
!2157 = distinct !DILexicalBlock(scope: !2148, file: !236, line: 116, column: 13)
!2158 = !DILocation(line: 116, column: 18, scope: !2157)
!2159 = !DILocation(line: 116, column: 13, scope: !2160)
!2160 = !DILexicalBlockFile(scope: !2157, file: !236, discriminator: 1)
!2161 = !DILocation(line: 116, column: 58, scope: !2157)
!2162 = !DILocation(line: 116, column: 13, scope: !2148)
!2163 = !DILocation(line: 117, column: 13, scope: !2157)
!2164 = !DILocation(line: 117, column: 13, scope: !2160)
!2165 = !DILocation(line: 118, column: 17, scope: !2148)
!2166 = !DILocation(line: 118, column: 10, scope: !2148)
!2167 = !DILocation(line: 119, column: 9, scope: !2148)
!2168 = !DILocation(line: 120, column: 10, scope: !2169)
!2169 = distinct !DILexicalBlock(scope: !2140, file: !236, line: 120, column: 10)
!2170 = !DILocation(line: 120, column: 28, scope: !2169)
!2171 = !DILocation(line: 120, column: 10, scope: !2140)
!2172 = !DILocation(line: 121, column: 17, scope: !2169)
!2173 = !DILocation(line: 121, column: 10, scope: !2169)
!2174 = !DILocation(line: 122, column: 18, scope: !2140)
!2175 = !DILocation(line: 122, column: 17, scope: !2140)
!2176 = !DILocation(line: 123, column: 10, scope: !2177)
!2177 = distinct !DILexicalBlock(scope: !2140, file: !236, line: 123, column: 10)
!2178 = !DILocation(line: 123, column: 21, scope: !2177)
!2179 = !DILocation(line: 123, column: 10, scope: !2140)
!2180 = !DILocation(line: 125, column: 18, scope: !2181)
!2181 = distinct !DILexicalBlock(scope: !2182, file: !236, line: 125, column: 13)
!2182 = distinct !DILexicalBlock(scope: !2177, file: !236, line: 124, column: 9)
!2183 = !DILocation(line: 125, column: 13, scope: !2181)
!2184 = !DILocation(line: 125, column: 44, scope: !2181)
!2185 = !DILocation(line: 125, column: 13, scope: !2182)
!2186 = !DILocation(line: 126, column: 13, scope: !2181)
!2187 = !DILocation(line: 126, column: 13, scope: !2188)
!2188 = !DILexicalBlockFile(scope: !2181, file: !236, discriminator: 1)
!2189 = !DILocation(line: 127, column: 16, scope: !2182)
!2190 = !DILocation(line: 127, column: 10, scope: !2182)
!2191 = !DILocation(line: 128, column: 9, scope: !2182)
!2192 = !DILocation(line: 130, column: 10, scope: !2177)
!2193 = !DILocation(line: 130, column: 10, scope: !2194)
!2194 = !DILexicalBlockFile(scope: !2177, file: !236, discriminator: 1)
!2195 = !DILocation(line: 132, column: 7, scope: !2140)
!2196 = !DILocation(line: 133, column: 14, scope: !2140)
!2197 = !DILocation(line: 133, column: 29, scope: !2140)
!2198 = !DILocation(line: 133, column: 7, scope: !2140)
!2199 = !DILocation(line: 134, column: 7, scope: !2140)
!2200 = !DILocation(line: 134, column: 7, scope: !2201)
!2201 = !DILexicalBlockFile(scope: !2140, file: !236, discriminator: 1)
!2202 = !DILocation(line: 135, column: 12, scope: !2140)
!2203 = !DILocation(line: 135, column: 7, scope: !2201)
!2204 = !DILocation(line: 135, column: 7, scope: !2140)
!2205 = !DILocation(line: 139, column: 11, scope: !2206)
!2206 = distinct !DILexicalBlock(scope: !2207, file: !236, line: 139, column: 10)
!2207 = distinct !DILexicalBlock(scope: !2135, file: !236, line: 138, column: 6)
!2208 = !DILocation(line: 139, column: 10, scope: !2206)
!2209 = !DILocation(line: 139, column: 23, scope: !2206)
!2210 = !DILocation(line: 139, column: 10, scope: !2207)
!2211 = !DILocation(line: 140, column: 13, scope: !2206)
!2212 = !DILocation(line: 140, column: 10, scope: !2206)
!2213 = !DILocation(line: 143, column: 14, scope: !2214)
!2214 = distinct !DILexicalBlock(scope: !2206, file: !236, line: 142, column: 9)
!2215 = !DILocation(line: 143, column: 13, scope: !2214)
!2216 = !DILocation(line: 144, column: 10, scope: !2214)
!2217 = !DILocation(line: 144, column: 10, scope: !2218)
!2218 = !DILexicalBlockFile(scope: !2214, file: !236, discriminator: 1)
!2219 = !DILocation(line: 147, column: 11, scope: !2117)
!2220 = !DILocation(line: 147, column: 4, scope: !2117)
!2221 = distinct !DISubprogram(name: "configure_timer", scope: !236, file: !236, line: 150, type: !2222, isLocal: false, isDefinition: true, scopeLine: 151, flags: DIFlagPrototyped, isOptimized: false, unit: !235, variables: !2)
!2222 = !DISubroutineType(types: !2223)
!2223 = !{!12, !2224}
!2224 = !DIBasicType(name: "float", size: 32, align: 32, encoding: DW_ATE_float)
!2225 = !DILocalVariable(name: "interval_sec", arg: 1, scope: !2221, file: !236, line: 150, type: !2224)
!2226 = !DILocation(line: 150, column: 27, scope: !2221)
!2227 = !DILocalVariable(name: "ret_error", scope: !2221, file: !236, line: 152, type: !12)
!2228 = !DILocation(line: 152, column: 8, scope: !2221)
!2229 = !DILocalVariable(name: "timer_conf", scope: !2221, file: !236, line: 153, type: !2230)
!2230 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "itimerval", file: !239, line: 107, size: 128, align: 32, elements: !2231)
!2231 = !{!2232, !2237}
!2232 = !DIDerivedType(tag: DW_TAG_member, name: "it_interval", scope: !2230, file: !239, line: 110, baseType: !2233, size: 64, align: 32)
!2233 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "timeval", file: !332, line: 30, size: 64, align: 32, elements: !2234)
!2234 = !{!2235, !2236}
!2235 = !DIDerivedType(tag: DW_TAG_member, name: "tv_sec", scope: !2233, file: !332, line: 32, baseType: !247, size: 32, align: 32)
!2236 = !DIDerivedType(tag: DW_TAG_member, name: "tv_usec", scope: !2233, file: !332, line: 33, baseType: !251, size: 32, align: 32, offset: 32)
!2237 = !DIDerivedType(tag: DW_TAG_member, name: "it_value", scope: !2230, file: !239, line: 112, baseType: !2233, size: 64, align: 32, offset: 64)
!2238 = !DILocation(line: 153, column: 21, scope: !2221)
!2239 = !DILocation(line: 155, column: 7, scope: !2240)
!2240 = distinct !DILexicalBlock(scope: !2221, file: !236, line: 155, column: 7)
!2241 = !DILocation(line: 155, column: 20, scope: !2240)
!2242 = !DILocation(line: 155, column: 7, scope: !2221)
!2243 = !DILocation(line: 159, column: 18, scope: !2244)
!2244 = distinct !DILexicalBlock(scope: !2240, file: !236, line: 156, column: 6)
!2245 = !DILocation(line: 159, column: 27, scope: !2244)
!2246 = !DILocation(line: 159, column: 34, scope: !2244)
!2247 = !DILocation(line: 160, column: 18, scope: !2244)
!2248 = !DILocation(line: 160, column: 27, scope: !2244)
!2249 = !DILocation(line: 160, column: 35, scope: !2244)
!2250 = !DILocation(line: 161, column: 18, scope: !2244)
!2251 = !DILocation(line: 161, column: 30, scope: !2244)
!2252 = !DILocation(line: 161, column: 37, scope: !2244)
!2253 = !DILocation(line: 162, column: 18, scope: !2244)
!2254 = !DILocation(line: 162, column: 30, scope: !2244)
!2255 = !DILocation(line: 162, column: 38, scope: !2244)
!2256 = !DILocation(line: 163, column: 6, scope: !2244)
!2257 = !DILocation(line: 167, column: 18, scope: !2258)
!2258 = distinct !DILexicalBlock(scope: !2240, file: !236, line: 165, column: 6)
!2259 = !DILocation(line: 167, column: 27, scope: !2258)
!2260 = !DILocation(line: 167, column: 34, scope: !2258)
!2261 = !DILocation(line: 168, column: 18, scope: !2258)
!2262 = !DILocation(line: 168, column: 27, scope: !2258)
!2263 = !DILocation(line: 168, column: 35, scope: !2258)
!2264 = !DILocation(line: 170, column: 47, scope: !2258)
!2265 = !DILocation(line: 170, column: 39, scope: !2258)
!2266 = !DILocation(line: 170, column: 18, scope: !2258)
!2267 = !DILocation(line: 170, column: 30, scope: !2258)
!2268 = !DILocation(line: 170, column: 37, scope: !2258)
!2269 = !DILocation(line: 171, column: 55, scope: !2258)
!2270 = !DILocation(line: 171, column: 79, scope: !2258)
!2271 = !DILocation(line: 171, column: 91, scope: !2258)
!2272 = !DILocation(line: 171, column: 68, scope: !2258)
!2273 = !DILocation(line: 171, column: 67, scope: !2258)
!2274 = !DILocation(line: 171, column: 54, scope: !2258)
!2275 = !DILocation(line: 171, column: 98, scope: !2258)
!2276 = !DILocation(line: 171, column: 40, scope: !2258)
!2277 = !DILocation(line: 171, column: 18, scope: !2258)
!2278 = !DILocation(line: 171, column: 30, scope: !2258)
!2279 = !DILocation(line: 171, column: 38, scope: !2258)
!2280 = !DILocation(line: 175, column: 7, scope: !2281)
!2281 = distinct !DILexicalBlock(scope: !2221, file: !236, line: 175, column: 7)
!2282 = !DILocation(line: 175, column: 50, scope: !2281)
!2283 = !DILocation(line: 175, column: 7, scope: !2221)
!2284 = !DILocation(line: 177, column: 7, scope: !2285)
!2285 = distinct !DILexicalBlock(scope: !2281, file: !236, line: 176, column: 6)
!2286 = !DILocation(line: 178, column: 16, scope: !2285)
!2287 = !DILocation(line: 179, column: 6, scope: !2285)
!2288 = !DILocation(line: 182, column: 17, scope: !2289)
!2289 = distinct !DILexicalBlock(scope: !2281, file: !236, line: 181, column: 6)
!2290 = !DILocation(line: 182, column: 16, scope: !2289)
!2291 = !DILocation(line: 183, column: 7, scope: !2289)
!2292 = !DILocation(line: 183, column: 7, scope: !2293)
!2293 = !DILexicalBlockFile(scope: !2289, file: !236, discriminator: 1)
!2294 = !DILocation(line: 183, column: 7, scope: !2295)
!2295 = !DILexicalBlockFile(scope: !2289, file: !236, discriminator: 2)
!2296 = !DILocation(line: 183, column: 7, scope: !2297)
!2297 = !DILexicalBlockFile(scope: !2289, file: !236, discriminator: 3)
!2298 = !DILocation(line: 185, column: 11, scope: !2221)
!2299 = !DILocation(line: 185, column: 4, scope: !2221)
!2300 = distinct !DISubprogram(name: "daemonize", scope: !236, file: !236, line: 189, type: !568, isLocal: false, isDefinition: true, scopeLine: 190, flags: DIFlagPrototyped, isOptimized: false, unit: !235, variables: !2)
!2301 = !DILocalVariable(name: "working_dir", arg: 1, scope: !2300, file: !236, line: 189, type: !18)
!2302 = !DILocation(line: 189, column: 21, scope: !2300)
!2303 = !DILocalVariable(name: "ret_error", scope: !2300, file: !236, line: 191, type: !12)
!2304 = !DILocation(line: 191, column: 8, scope: !2300)
!2305 = !DILocalVariable(name: "child_pid", scope: !2300, file: !236, line: 192, type: !8)
!2306 = !DILocation(line: 192, column: 10, scope: !2300)
!2307 = !DILocalVariable(name: "null_fd_rd", scope: !2300, file: !236, line: 193, type: !12)
!2308 = !DILocation(line: 193, column: 8, scope: !2300)
!2309 = !DILocalVariable(name: "null_fd_wr", scope: !2300, file: !236, line: 193, type: !12)
!2310 = !DILocation(line: 193, column: 20, scope: !2300)
!2311 = !DILocation(line: 195, column: 16, scope: !2300)
!2312 = !DILocation(line: 195, column: 14, scope: !2300)
!2313 = !DILocation(line: 196, column: 7, scope: !2314)
!2314 = distinct !DILexicalBlock(scope: !2300, file: !236, line: 196, column: 7)
!2315 = !DILocation(line: 196, column: 17, scope: !2314)
!2316 = !DILocation(line: 196, column: 7, scope: !2300)
!2317 = !DILocation(line: 198, column: 10, scope: !2318)
!2318 = distinct !DILexicalBlock(scope: !2319, file: !236, line: 198, column: 10)
!2319 = distinct !DILexicalBlock(scope: !2314, file: !236, line: 197, column: 6)
!2320 = !DILocation(line: 198, column: 20, scope: !2318)
!2321 = !DILocation(line: 198, column: 10, scope: !2319)
!2322 = !DILocation(line: 199, column: 10, scope: !2318)
!2323 = !DILocation(line: 202, column: 10, scope: !2324)
!2324 = distinct !DILexicalBlock(scope: !2319, file: !236, line: 202, column: 10)
!2325 = !DILocation(line: 202, column: 19, scope: !2324)
!2326 = !DILocation(line: 202, column: 10, scope: !2319)
!2327 = !DILocation(line: 206, column: 10, scope: !2328)
!2328 = distinct !DILexicalBlock(scope: !2324, file: !236, line: 203, column: 9)
!2329 = !DILocation(line: 207, column: 10, scope: !2328)
!2330 = !DILocation(line: 209, column: 22, scope: !2328)
!2331 = !DILocation(line: 209, column: 20, scope: !2328)
!2332 = !DILocation(line: 210, column: 13, scope: !2333)
!2333 = distinct !DILexicalBlock(scope: !2328, file: !236, line: 210, column: 13)
!2334 = !DILocation(line: 210, column: 23, scope: !2333)
!2335 = !DILocation(line: 210, column: 13, scope: !2328)
!2336 = !DILocation(line: 212, column: 16, scope: !2337)
!2337 = distinct !DILexicalBlock(scope: !2338, file: !236, line: 212, column: 16)
!2338 = distinct !DILexicalBlock(scope: !2333, file: !236, line: 211, column: 12)
!2339 = !DILocation(line: 212, column: 26, scope: !2337)
!2340 = !DILocation(line: 212, column: 16, scope: !2338)
!2341 = !DILocation(line: 213, column: 16, scope: !2337)
!2342 = !DILocation(line: 215, column: 13, scope: !2338)
!2343 = !DILocation(line: 217, column: 19, scope: !2338)
!2344 = !DILocation(line: 217, column: 13, scope: !2338)
!2345 = !DILocation(line: 219, column: 24, scope: !2338)
!2346 = !DILocation(line: 219, column: 23, scope: !2338)
!2347 = !DILocation(line: 220, column: 16, scope: !2348)
!2348 = distinct !DILexicalBlock(scope: !2338, file: !236, line: 220, column: 16)
!2349 = !DILocation(line: 220, column: 27, scope: !2348)
!2350 = !DILocation(line: 220, column: 16, scope: !2338)
!2351 = !DILocation(line: 222, column: 21, scope: !2352)
!2352 = distinct !DILexicalBlock(scope: !2348, file: !236, line: 221, column: 15)
!2353 = !DILocation(line: 222, column: 16, scope: !2352)
!2354 = !DILocation(line: 223, column: 22, scope: !2352)
!2355 = !DILocation(line: 223, column: 16, scope: !2352)
!2356 = !DILocation(line: 224, column: 15, scope: !2352)
!2357 = !DILocation(line: 226, column: 16, scope: !2348)
!2358 = !DILocation(line: 227, column: 24, scope: !2338)
!2359 = !DILocation(line: 227, column: 23, scope: !2338)
!2360 = !DILocation(line: 228, column: 16, scope: !2361)
!2361 = distinct !DILexicalBlock(scope: !2338, file: !236, line: 228, column: 16)
!2362 = !DILocation(line: 228, column: 27, scope: !2361)
!2363 = !DILocation(line: 228, column: 16, scope: !2338)
!2364 = !DILocation(line: 230, column: 21, scope: !2365)
!2365 = distinct !DILexicalBlock(scope: !2361, file: !236, line: 229, column: 15)
!2366 = !DILocation(line: 230, column: 16, scope: !2365)
!2367 = !DILocation(line: 231, column: 21, scope: !2365)
!2368 = !DILocation(line: 231, column: 16, scope: !2365)
!2369 = !DILocation(line: 232, column: 22, scope: !2365)
!2370 = !DILocation(line: 232, column: 16, scope: !2365)
!2371 = !DILocation(line: 233, column: 15, scope: !2365)
!2372 = !DILocation(line: 235, column: 16, scope: !2361)
!2373 = !DILocation(line: 237, column: 12, scope: !2338)
!2374 = !DILocation(line: 240, column: 23, scope: !2375)
!2375 = distinct !DILexicalBlock(scope: !2333, file: !236, line: 239, column: 12)
!2376 = !DILocation(line: 240, column: 22, scope: !2375)
!2377 = !DILocation(line: 241, column: 21, scope: !2375)
!2378 = !DILocation(line: 241, column: 87, scope: !2375)
!2379 = !DILocation(line: 241, column: 13, scope: !2380)
!2380 = !DILexicalBlockFile(scope: !2375, file: !236, discriminator: 1)
!2381 = !DILocation(line: 245, column: 9, scope: !2328)
!2382 = !DILocation(line: 248, column: 20, scope: !2383)
!2383 = distinct !DILexicalBlock(scope: !2324, file: !236, line: 247, column: 9)
!2384 = !DILocation(line: 248, column: 19, scope: !2383)
!2385 = !DILocation(line: 249, column: 18, scope: !2383)
!2386 = !DILocation(line: 249, column: 107, scope: !2383)
!2387 = !DILocation(line: 249, column: 10, scope: !2388)
!2388 = !DILexicalBlockFile(scope: !2383, file: !236, discriminator: 1)
!2389 = !DILocation(line: 252, column: 6, scope: !2319)
!2390 = !DILocation(line: 255, column: 17, scope: !2391)
!2391 = distinct !DILexicalBlock(scope: !2314, file: !236, line: 254, column: 6)
!2392 = !DILocation(line: 255, column: 16, scope: !2391)
!2393 = !DILocation(line: 256, column: 15, scope: !2391)
!2394 = !DILocation(line: 256, column: 80, scope: !2391)
!2395 = !DILocation(line: 256, column: 7, scope: !2396)
!2396 = !DILexicalBlockFile(scope: !2391, file: !236, discriminator: 1)
!2397 = !DILocation(line: 260, column: 11, scope: !2300)
!2398 = !DILocation(line: 260, column: 4, scope: !2300)
!2399 = distinct !DISubprogram(name: "get_localtime_str", scope: !256, file: !256, line: 15, type: !2400, isLocal: false, isDefinition: true, scopeLine: 16, flags: DIFlagPrototyped, isOptimized: false, unit: !255, variables: !2)
!2400 = !DISubroutineType(types: !2401)
!2401 = !{null, !18, !311}
!2402 = !DILocalVariable(name: "cur_time_str", arg: 1, scope: !2399, file: !256, line: 15, type: !18)
!2403 = !DILocation(line: 15, column: 30, scope: !2399)
!2404 = !DILocalVariable(name: "cur_time_str_len", arg: 2, scope: !2399, file: !256, line: 15, type: !311)
!2405 = !DILocation(line: 15, column: 51, scope: !2399)
!2406 = !DILocalVariable(name: "cur_time", scope: !2399, file: !256, line: 17, type: !245)
!2407 = !DILocation(line: 17, column: 11, scope: !2399)
!2408 = !DILocalVariable(name: "cur_time_struct", scope: !2399, file: !256, line: 18, type: !2409)
!2409 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !2410, size: 32, align: 32)
!2410 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "tm", file: !246, line: 133, size: 352, align: 32, elements: !2411)
!2411 = !{!2412, !2413, !2414, !2415, !2416, !2417, !2418, !2419, !2420, !2421, !2422}
!2412 = !DIDerivedType(tag: DW_TAG_member, name: "tm_sec", scope: !2410, file: !246, line: 135, baseType: !12, size: 32, align: 32)
!2413 = !DIDerivedType(tag: DW_TAG_member, name: "tm_min", scope: !2410, file: !246, line: 136, baseType: !12, size: 32, align: 32, offset: 32)
!2414 = !DIDerivedType(tag: DW_TAG_member, name: "tm_hour", scope: !2410, file: !246, line: 137, baseType: !12, size: 32, align: 32, offset: 64)
!2415 = !DIDerivedType(tag: DW_TAG_member, name: "tm_mday", scope: !2410, file: !246, line: 138, baseType: !12, size: 32, align: 32, offset: 96)
!2416 = !DIDerivedType(tag: DW_TAG_member, name: "tm_mon", scope: !2410, file: !246, line: 139, baseType: !12, size: 32, align: 32, offset: 128)
!2417 = !DIDerivedType(tag: DW_TAG_member, name: "tm_year", scope: !2410, file: !246, line: 140, baseType: !12, size: 32, align: 32, offset: 160)
!2418 = !DIDerivedType(tag: DW_TAG_member, name: "tm_wday", scope: !2410, file: !246, line: 141, baseType: !12, size: 32, align: 32, offset: 192)
!2419 = !DIDerivedType(tag: DW_TAG_member, name: "tm_yday", scope: !2410, file: !246, line: 142, baseType: !12, size: 32, align: 32, offset: 224)
!2420 = !DIDerivedType(tag: DW_TAG_member, name: "tm_isdst", scope: !2410, file: !246, line: 143, baseType: !12, size: 32, align: 32, offset: 256)
!2421 = !DIDerivedType(tag: DW_TAG_member, name: "tm_gmtoff", scope: !2410, file: !246, line: 146, baseType: !248, size: 32, align: 32, offset: 288)
!2422 = !DIDerivedType(tag: DW_TAG_member, name: "tm_zone", scope: !2410, file: !246, line: 147, baseType: !2120, size: 32, align: 32, offset: 320)
!2423 = !DILocation(line: 18, column: 15, scope: !2399)
!2424 = !DILocation(line: 20, column: 15, scope: !2399)
!2425 = !DILocation(line: 20, column: 13, scope: !2399)
!2426 = !DILocation(line: 21, column: 7, scope: !2427)
!2427 = distinct !DILexicalBlock(scope: !2399, file: !256, line: 21, column: 7)
!2428 = !DILocation(line: 21, column: 16, scope: !2427)
!2429 = !DILocation(line: 21, column: 7, scope: !2399)
!2430 = !DILocation(line: 23, column: 25, scope: !2431)
!2431 = distinct !DILexicalBlock(scope: !2427, file: !256, line: 22, column: 6)
!2432 = !DILocation(line: 23, column: 23, scope: !2431)
!2433 = !DILocation(line: 24, column: 19, scope: !2434)
!2434 = distinct !DILexicalBlock(scope: !2431, file: !256, line: 24, column: 10)
!2435 = !DILocation(line: 24, column: 33, scope: !2434)
!2436 = !DILocation(line: 24, column: 72, scope: !2434)
!2437 = !DILocation(line: 24, column: 10, scope: !2434)
!2438 = !DILocation(line: 24, column: 88, scope: !2434)
!2439 = !DILocation(line: 24, column: 10, scope: !2431)
!2440 = !DILocation(line: 25, column: 13, scope: !2441)
!2441 = distinct !DILexicalBlock(scope: !2434, file: !256, line: 25, column: 13)
!2442 = !DILocation(line: 25, column: 29, scope: !2441)
!2443 = !DILocation(line: 25, column: 13, scope: !2434)
!2444 = !DILocation(line: 26, column: 13, scope: !2441)
!2445 = !DILocation(line: 26, column: 28, scope: !2441)
!2446 = !DILocation(line: 25, column: 30, scope: !2447)
!2447 = !DILexicalBlockFile(scope: !2441, file: !256, discriminator: 1)
!2448 = !DILocation(line: 27, column: 6, scope: !2431)
!2449 = !DILocation(line: 30, column: 10, scope: !2450)
!2450 = distinct !DILexicalBlock(scope: !2451, file: !256, line: 30, column: 10)
!2451 = distinct !DILexicalBlock(scope: !2427, file: !256, line: 29, column: 6)
!2452 = !DILocation(line: 30, column: 26, scope: !2450)
!2453 = !DILocation(line: 30, column: 10, scope: !2451)
!2454 = !DILocation(line: 31, column: 10, scope: !2450)
!2455 = !DILocation(line: 31, column: 25, scope: !2450)
!2456 = !DILocation(line: 34, column: 3, scope: !2399)
!2457 = distinct !DISubprogram(name: "msg_printf", scope: !256, file: !256, line: 39, type: !2458, isLocal: false, isDefinition: true, scopeLine: 40, flags: DIFlagPrototyped, isOptimized: false, unit: !255, variables: !2)
!2458 = !DISubroutineType(types: !2459)
!2459 = !{!12, !261, !2120, null}
!2460 = !DILocalVariable(name: "out_file_handle", arg: 1, scope: !2457, file: !256, line: 39, type: !261)
!2461 = !DILocation(line: 39, column: 22, scope: !2457)
!2462 = !DILocalVariable(name: "format", arg: 2, scope: !2457, file: !256, line: 39, type: !2120)
!2463 = !DILocation(line: 39, column: 51, scope: !2457)
!2464 = !DILocalVariable(name: "ret", scope: !2457, file: !256, line: 41, type: !12)
!2465 = !DILocation(line: 41, column: 8, scope: !2457)
!2466 = !DILocation(line: 42, column: 7, scope: !2467)
!2467 = distinct !DILexicalBlock(scope: !2457, file: !256, line: 42, column: 7)
!2468 = !DILocation(line: 42, column: 24, scope: !2467)
!2469 = !DILocation(line: 42, column: 27, scope: !2470)
!2470 = !DILexicalBlockFile(scope: !2467, file: !256, discriminator: 1)
!2471 = !DILocation(line: 42, column: 43, scope: !2470)
!2472 = !DILocation(line: 42, column: 7, scope: !2470)
!2473 = !DILocalVariable(name: "printf_ret", scope: !2474, file: !256, line: 44, type: !12)
!2474 = distinct !DILexicalBlock(scope: !2467, file: !256, line: 43, column: 6)
!2475 = !DILocation(line: 44, column: 11, scope: !2474)
!2476 = !DILocalVariable(name: "fprintf_ret", scope: !2474, file: !256, line: 44, type: !12)
!2477 = !DILocation(line: 44, column: 24, scope: !2474)
!2478 = !DILocalVariable(name: "arglist", scope: !2474, file: !256, line: 45, type: !2479)
!2479 = !DIDerivedType(tag: DW_TAG_typedef, name: "va_list", file: !263, line: 79, baseType: !2480)
!2480 = !DIDerivedType(tag: DW_TAG_typedef, name: "__gnuc_va_list", file: !2481, line: 50, baseType: !2482)
!2481 = !DIFile(filename: "/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/../lib/clang/3.9.0/include/stdarg.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/alarm4pi-cb")
!2482 = !DIDerivedType(tag: DW_TAG_typedef, name: "__builtin_va_list", file: !256, line: 45, baseType: !2483)
!2483 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "__va_list", file: !256, line: 45, size: 32, align: 32, elements: !2484)
!2484 = !{!2485}
!2485 = !DIDerivedType(tag: DW_TAG_member, name: "__ap", scope: !2483, file: !256, line: 45, baseType: !32, size: 32, align: 32)
!2486 = !DILocation(line: 45, column: 15, scope: !2474)
!2487 = !DILocalVariable(name: "cur_time_str", scope: !2474, file: !256, line: 46, type: !2488)
!2488 = !DICompositeType(tag: DW_TAG_array_type, baseType: !19, size: 160, align: 8, elements: !2489)
!2489 = !{!2490}
!2490 = !DISubrange(count: 20)
!2491 = !DILocation(line: 46, column: 12, scope: !2474)
!2492 = !DILocation(line: 48, column: 24, scope: !2474)
!2493 = !DILocation(line: 48, column: 6, scope: !2474)
!2494 = !DILocation(line: 49, column: 7, scope: !2474)
!2495 = !DILocation(line: 50, column: 10, scope: !2496)
!2496 = distinct !DILexicalBlock(scope: !2474, file: !256, line: 50, column: 10)
!2497 = !DILocation(line: 50, column: 10, scope: !2474)
!2498 = !DILocation(line: 51, column: 29, scope: !2496)
!2499 = !DILocation(line: 51, column: 21, scope: !2496)
!2500 = !DILocation(line: 51, column: 20, scope: !2496)
!2501 = !DILocation(line: 51, column: 10, scope: !2496)
!2502 = !DILocation(line: 52, column: 10, scope: !2503)
!2503 = distinct !DILexicalBlock(scope: !2474, file: !256, line: 52, column: 10)
!2504 = !DILocation(line: 52, column: 26, scope: !2503)
!2505 = !DILocation(line: 52, column: 10, scope: !2474)
!2506 = !DILocation(line: 54, column: 18, scope: !2507)
!2507 = distinct !DILexicalBlock(scope: !2503, file: !256, line: 53, column: 9)
!2508 = !DILocation(line: 54, column: 43, scope: !2507)
!2509 = !DILocation(line: 54, column: 10, scope: !2507)
!2510 = !DILocation(line: 55, column: 31, scope: !2507)
!2511 = !DILocation(line: 55, column: 48, scope: !2507)
!2512 = !DILocation(line: 55, column: 22, scope: !2507)
!2513 = !DILocation(line: 55, column: 21, scope: !2507)
!2514 = !DILocation(line: 56, column: 9, scope: !2507)
!2515 = !DILocation(line: 57, column: 7, scope: !2474)
!2516 = !DILocation(line: 58, column: 12, scope: !2474)
!2517 = !DILocation(line: 58, column: 22, scope: !2474)
!2518 = !DILocation(line: 58, column: 11, scope: !2474)
!2519 = !DILocation(line: 58, column: 27, scope: !2520)
!2520 = !DILexicalBlockFile(scope: !2474, file: !256, discriminator: 1)
!2521 = !DILocation(line: 58, column: 11, scope: !2520)
!2522 = !DILocation(line: 58, column: 38, scope: !2523)
!2523 = !DILexicalBlockFile(scope: !2474, file: !256, discriminator: 2)
!2524 = !DILocation(line: 58, column: 11, scope: !2523)
!2525 = !DILocation(line: 58, column: 11, scope: !2526)
!2526 = !DILexicalBlockFile(scope: !2474, file: !256, discriminator: 3)
!2527 = !DILocation(line: 58, column: 10, scope: !2526)
!2528 = !DILocation(line: 59, column: 6, scope: !2474)
!2529 = !DILocation(line: 61, column: 10, scope: !2467)
!2530 = !DILocation(line: 62, column: 11, scope: !2457)
!2531 = !DILocation(line: 62, column: 4, scope: !2457)
!2532 = distinct !DISubprogram(name: "open_msg_file", scope: !256, file: !256, line: 67, type: !2533, isLocal: false, isDefinition: true, scopeLine: 68, flags: DIFlagPrototyped, isOptimized: false, unit: !255, variables: !2)
!2533 = !DISubroutineType(types: !2534)
!2534 = !{!261, !2120, !248}
!2535 = !DILocalVariable(name: "file_name", arg: 1, scope: !2532, file: !256, line: 67, type: !2120)
!2536 = !DILocation(line: 67, column: 33, scope: !2532)
!2537 = !DILocalVariable(name: "max_file_len", arg: 2, scope: !2532, file: !256, line: 67, type: !248)
!2538 = !DILocation(line: 67, column: 49, scope: !2532)
!2539 = !DILocalVariable(name: "file_handle", scope: !2532, file: !256, line: 69, type: !261)
!2540 = !DILocation(line: 69, column: 10, scope: !2532)
!2541 = !DILocation(line: 70, column: 22, scope: !2532)
!2542 = !DILocation(line: 70, column: 16, scope: !2532)
!2543 = !DILocation(line: 70, column: 15, scope: !2532)
!2544 = !DILocation(line: 71, column: 7, scope: !2545)
!2545 = distinct !DILexicalBlock(scope: !2532, file: !256, line: 71, column: 7)
!2546 = !DILocation(line: 71, column: 7, scope: !2532)
!2547 = !DILocalVariable(name: "log_size", scope: !2548, file: !256, line: 73, type: !248)
!2548 = distinct !DILexicalBlock(scope: !2545, file: !256, line: 72, column: 6)
!2549 = !DILocation(line: 73, column: 12, scope: !2548)
!2550 = !DILocalVariable(name: "log_size_loaded", scope: !2548, file: !256, line: 74, type: !311)
!2551 = !DILocation(line: 74, column: 14, scope: !2548)
!2552 = !DILocalVariable(name: "cur_time_str", scope: !2548, file: !256, line: 75, type: !2488)
!2553 = !DILocation(line: 75, column: 12, scope: !2548)
!2554 = !DILocation(line: 77, column: 20, scope: !2548)
!2555 = !DILocation(line: 77, column: 13, scope: !2548)
!2556 = !DILocation(line: 77, column: 7, scope: !2557)
!2557 = !DILexicalBlockFile(scope: !2548, file: !256, discriminator: 1)
!2558 = !DILocation(line: 78, column: 14, scope: !2548)
!2559 = !DILocation(line: 78, column: 7, scope: !2548)
!2560 = !DILocation(line: 80, column: 13, scope: !2548)
!2561 = !DILocation(line: 80, column: 7, scope: !2548)
!2562 = !DILocation(line: 81, column: 24, scope: !2548)
!2563 = !DILocation(line: 81, column: 18, scope: !2548)
!2564 = !DILocation(line: 81, column: 16, scope: !2548)
!2565 = !DILocation(line: 83, column: 11, scope: !2566)
!2566 = distinct !DILexicalBlock(scope: !2548, file: !256, line: 83, column: 11)
!2567 = !DILocation(line: 83, column: 22, scope: !2566)
!2568 = !DILocation(line: 83, column: 20, scope: !2566)
!2569 = !DILocation(line: 83, column: 11, scope: !2548)
!2570 = !DILocalVariable(name: "log_file_buf", scope: !2571, file: !256, line: 85, type: !18)
!2571 = distinct !DILexicalBlock(scope: !2566, file: !256, line: 84, column: 9)
!2572 = !DILocation(line: 85, column: 16, scope: !2571)
!2573 = !DILocation(line: 87, column: 38, scope: !2571)
!2574 = !DILocation(line: 87, column: 50, scope: !2571)
!2575 = !DILocation(line: 87, column: 31, scope: !2571)
!2576 = !DILocation(line: 87, column: 22, scope: !2571)
!2577 = !DILocation(line: 88, column: 13, scope: !2578)
!2578 = distinct !DILexicalBlock(scope: !2571, file: !256, line: 88, column: 13)
!2579 = !DILocation(line: 88, column: 13, scope: !2571)
!2580 = !DILocation(line: 90, column: 19, scope: !2581)
!2581 = distinct !DILexicalBlock(scope: !2578, file: !256, line: 89, column: 12)
!2582 = !DILocation(line: 90, column: 33, scope: !2581)
!2583 = !DILocation(line: 90, column: 32, scope: !2581)
!2584 = !DILocation(line: 90, column: 13, scope: !2581)
!2585 = !DILocation(line: 91, column: 37, scope: !2581)
!2586 = !DILocation(line: 91, column: 65, scope: !2581)
!2587 = !DILocation(line: 91, column: 79, scope: !2581)
!2588 = !DILocation(line: 91, column: 31, scope: !2581)
!2589 = !DILocation(line: 91, column: 29, scope: !2581)
!2590 = !DILocation(line: 92, column: 20, scope: !2581)
!2591 = !DILocation(line: 92, column: 13, scope: !2581)
!2592 = !DILocation(line: 93, column: 18, scope: !2581)
!2593 = !DILocation(line: 93, column: 13, scope: !2581)
!2594 = !DILocation(line: 94, column: 33, scope: !2581)
!2595 = !DILocation(line: 94, column: 27, scope: !2581)
!2596 = !DILocation(line: 94, column: 25, scope: !2581)
!2597 = !DILocation(line: 95, column: 17, scope: !2598)
!2598 = distinct !DILexicalBlock(scope: !2581, file: !256, line: 95, column: 17)
!2599 = !DILocation(line: 95, column: 17, scope: !2581)
!2600 = !DILocation(line: 97, column: 34, scope: !2601)
!2601 = distinct !DILexicalBlock(scope: !2598, file: !256, line: 96, column: 15)
!2602 = !DILocation(line: 97, column: 16, scope: !2601)
!2603 = !DILocation(line: 99, column: 24, scope: !2601)
!2604 = !DILocation(line: 99, column: 73, scope: !2601)
!2605 = !DILocation(line: 99, column: 16, scope: !2601)
!2606 = !DILocation(line: 100, column: 23, scope: !2601)
!2607 = !DILocation(line: 100, column: 51, scope: !2601)
!2608 = !DILocation(line: 100, column: 68, scope: !2601)
!2609 = !DILocation(line: 100, column: 16, scope: !2601)
!2610 = !DILocation(line: 101, column: 15, scope: !2601)
!2611 = !DILocation(line: 102, column: 12, scope: !2581)
!2612 = !DILocation(line: 103, column: 9, scope: !2571)
!2613 = !DILocation(line: 105, column: 10, scope: !2614)
!2614 = distinct !DILexicalBlock(scope: !2548, file: !256, line: 105, column: 10)
!2615 = !DILocation(line: 105, column: 10, scope: !2548)
!2616 = !DILocation(line: 107, column: 28, scope: !2617)
!2617 = distinct !DILexicalBlock(scope: !2614, file: !256, line: 106, column: 9)
!2618 = !DILocation(line: 107, column: 10, scope: !2617)
!2619 = !DILocation(line: 108, column: 18, scope: !2617)
!2620 = !DILocation(line: 108, column: 99, scope: !2617)
!2621 = !DILocation(line: 108, column: 10, scope: !2617)
!2622 = !DILocation(line: 109, column: 18, scope: !2617)
!2623 = !DILocation(line: 109, column: 63, scope: !2617)
!2624 = !DILocation(line: 109, column: 10, scope: !2617)
!2625 = !DILocation(line: 110, column: 9, scope: !2617)
!2626 = !DILocation(line: 111, column: 6, scope: !2548)
!2627 = !DILocation(line: 112, column: 11, scope: !2532)
!2628 = !DILocation(line: 112, column: 4, scope: !2532)
!2629 = distinct !DISubprogram(name: "close_log_file", scope: !256, file: !256, line: 116, type: !2630, isLocal: false, isDefinition: true, scopeLine: 117, flags: DIFlagPrototyped, isOptimized: false, unit: !255, variables: !2)
!2630 = !DISubroutineType(types: !2631)
!2631 = !{null, !261}
!2632 = !DILocalVariable(name: "file_handle", arg: 1, scope: !2629, file: !256, line: 116, type: !261)
!2633 = !DILocation(line: 116, column: 27, scope: !2629)
!2634 = !DILocation(line: 118, column: 7, scope: !2635)
!2635 = distinct !DILexicalBlock(scope: !2629, file: !256, line: 118, column: 7)
!2636 = !DILocation(line: 118, column: 7, scope: !2629)
!2637 = !DILocalVariable(name: "cur_time_str", scope: !2638, file: !256, line: 120, type: !2488)
!2638 = distinct !DILexicalBlock(scope: !2635, file: !256, line: 119, column: 6)
!2639 = !DILocation(line: 120, column: 12, scope: !2638)
!2640 = !DILocation(line: 122, column: 25, scope: !2638)
!2641 = !DILocation(line: 122, column: 7, scope: !2638)
!2642 = !DILocation(line: 123, column: 15, scope: !2638)
!2643 = !DILocation(line: 123, column: 64, scope: !2638)
!2644 = !DILocation(line: 123, column: 7, scope: !2638)
!2645 = !DILocation(line: 124, column: 14, scope: !2638)
!2646 = !DILocation(line: 124, column: 7, scope: !2638)
!2647 = !DILocation(line: 125, column: 6, scope: !2638)
!2648 = !DILocation(line: 126, column: 3, scope: !2629)
!2649 = distinct !DISubprogram(name: "open_log_files", scope: !256, file: !256, line: 128, type: !346, isLocal: false, isDefinition: true, scopeLine: 129, flags: DIFlagPrototyped, isOptimized: false, unit: !255, variables: !2)
!2650 = !DILocation(line: 130, column: 20, scope: !2649)
!2651 = !DILocation(line: 130, column: 19, scope: !2649)
!2652 = !DILocation(line: 131, column: 22, scope: !2649)
!2653 = !DILocation(line: 131, column: 21, scope: !2649)
!2654 = !DILocation(line: 132, column: 11, scope: !2649)
!2655 = !DILocation(line: 132, column: 27, scope: !2649)
!2656 = !DILocation(line: 132, column: 35, scope: !2649)
!2657 = !DILocation(line: 132, column: 38, scope: !2658)
!2658 = !DILexicalBlockFile(scope: !2649, file: !256, discriminator: 1)
!2659 = !DILocation(line: 132, column: 56, scope: !2658)
!2660 = !DILocation(line: 132, column: 35, scope: !2658)
!2661 = !DILocation(line: 132, column: 35, scope: !2662)
!2662 = !DILexicalBlockFile(scope: !2649, file: !256, discriminator: 2)
!2663 = !DILocation(line: 132, column: 4, scope: !2662)
!2664 = distinct !DISubprogram(name: "close_log_files", scope: !256, file: !256, line: 135, type: !438, isLocal: false, isDefinition: true, scopeLine: 136, flags: DIFlagPrototyped, isOptimized: false, unit: !255, variables: !2)
!2665 = !DILocation(line: 137, column: 19, scope: !2664)
!2666 = !DILocation(line: 137, column: 4, scope: !2664)
!2667 = !DILocation(line: 138, column: 19, scope: !2664)
!2668 = !DILocation(line: 138, column: 4, scope: !2664)
!2669 = !DILocation(line: 139, column: 3, scope: !2664)
!2670 = distinct !DISubprogram(name: "GPIO_export", scope: !320, file: !320, line: 15, type: !2671, isLocal: false, isDefinition: true, scopeLine: 16, flags: DIFlagPrototyped, isOptimized: false, unit: !319, variables: !2)
!2671 = !DISubroutineType(types: !2672)
!2672 = !{!12, !12}
!2673 = !DILocalVariable(name: "pin", arg: 1, scope: !2670, file: !320, line: 15, type: !12)
!2674 = !DILocation(line: 15, column: 21, scope: !2670)
!2675 = !DILocalVariable(name: "name_buffer", scope: !2670, file: !320, line: 17, type: !2676)
!2676 = !DICompositeType(tag: DW_TAG_array_type, baseType: !19, size: 32, align: 8, elements: !1636)
!2677 = !DILocation(line: 17, column: 9, scope: !2670)
!2678 = !DILocalVariable(name: "bytes_written", scope: !2670, file: !320, line: 18, type: !2679)
!2679 = !DIDerivedType(tag: DW_TAG_typedef, name: "ssize_t", file: !9, line: 109, baseType: !2680)
!2680 = !DIDerivedType(tag: DW_TAG_typedef, name: "__ssize_t", file: !11, line: 172, baseType: !12)
!2681 = !DILocation(line: 18, column: 12, scope: !2670)
!2682 = !DILocalVariable(name: "fd", scope: !2670, file: !320, line: 19, type: !12)
!2683 = !DILocation(line: 19, column: 8, scope: !2670)
!2684 = !DILocalVariable(name: "ret_err", scope: !2670, file: !320, line: 20, type: !12)
!2685 = !DILocation(line: 20, column: 8, scope: !2670)
!2686 = !DILocation(line: 22, column: 9, scope: !2670)
!2687 = !DILocation(line: 22, column: 7, scope: !2670)
!2688 = !DILocation(line: 23, column: 13, scope: !2689)
!2689 = distinct !DILexicalBlock(scope: !2670, file: !320, line: 23, column: 7)
!2690 = !DILocation(line: 23, column: 10, scope: !2689)
!2691 = !DILocation(line: 23, column: 7, scope: !2670)
!2692 = !DILocalVariable(name: "path", scope: !2693, file: !320, line: 25, type: !2694)
!2693 = distinct !DILexicalBlock(scope: !2689, file: !320, line: 24, column: 6)
!2694 = !DICompositeType(tag: DW_TAG_array_type, baseType: !19, size: 272, align: 8, elements: !2695)
!2695 = !{!2696}
!2696 = !DISubrange(count: 34)
!2697 = !DILocation(line: 25, column: 12, scope: !2693)
!2698 = !DILocalVariable(name: "fs_struct_created", scope: !2693, file: !320, line: 26, type: !12)
!2699 = !DILocation(line: 26, column: 11, scope: !2693)
!2700 = !DILocalVariable(name: "n_wait_cycle", scope: !2693, file: !320, line: 27, type: !12)
!2701 = !DILocation(line: 27, column: 11, scope: !2693)
!2702 = !DILocation(line: 29, column: 32, scope: !2693)
!2703 = !DILocation(line: 29, column: 74, scope: !2693)
!2704 = !DILocation(line: 29, column: 23, scope: !2693)
!2705 = !DILocation(line: 29, column: 21, scope: !2693)
!2706 = !DILocation(line: 30, column: 13, scope: !2693)
!2707 = !DILocation(line: 30, column: 17, scope: !2693)
!2708 = !DILocation(line: 30, column: 30, scope: !2693)
!2709 = !DILocation(line: 30, column: 7, scope: !2693)
!2710 = !DILocation(line: 31, column: 13, scope: !2693)
!2711 = !DILocation(line: 31, column: 7, scope: !2693)
!2712 = !DILocation(line: 34, column: 16, scope: !2693)
!2713 = !DILocation(line: 34, column: 86, scope: !2693)
!2714 = !DILocation(line: 34, column: 7, scope: !2693)
!2715 = !DILocation(line: 35, column: 24, scope: !2693)
!2716 = !DILocation(line: 36, column: 19, scope: !2693)
!2717 = !DILocation(line: 37, column: 7, scope: !2693)
!2718 = distinct !{!2718, !2717}
!2719 = !DILocation(line: 39, column: 10, scope: !2720)
!2720 = distinct !DILexicalBlock(scope: !2693, file: !320, line: 38, column: 9)
!2721 = !DILocation(line: 41, column: 20, scope: !2720)
!2722 = !DILocation(line: 41, column: 15, scope: !2720)
!2723 = !DILocation(line: 41, column: 13, scope: !2720)
!2724 = !DILocation(line: 42, column: 19, scope: !2725)
!2725 = distinct !DILexicalBlock(scope: !2720, file: !320, line: 42, column: 13)
!2726 = !DILocation(line: 42, column: 16, scope: !2725)
!2727 = !DILocation(line: 42, column: 13, scope: !2720)
!2728 = !DILocation(line: 44, column: 30, scope: !2729)
!2729 = distinct !DILexicalBlock(scope: !2725, file: !320, line: 43, column: 12)
!2730 = !DILocation(line: 45, column: 19, scope: !2729)
!2731 = !DILocation(line: 45, column: 13, scope: !2729)
!2732 = !DILocation(line: 46, column: 12, scope: !2729)
!2733 = !DILocation(line: 48, column: 30, scope: !2725)
!2734 = !DILocation(line: 49, column: 9, scope: !2720)
!2735 = !DILocation(line: 50, column: 14, scope: !2693)
!2736 = !DILocation(line: 50, column: 32, scope: !2693)
!2737 = !DILocation(line: 50, column: 47, scope: !2738)
!2738 = !DILexicalBlockFile(scope: !2693, file: !320, discriminator: 1)
!2739 = !DILocation(line: 50, column: 50, scope: !2738)
!2740 = !DILocation(line: 49, column: 9, scope: !2741)
!2741 = !DILexicalBlockFile(scope: !2720, file: !320, discriminator: 1)
!2742 = !DILocation(line: 51, column: 10, scope: !2743)
!2743 = distinct !DILexicalBlock(scope: !2693, file: !320, line: 51, column: 10)
!2744 = !DILocation(line: 51, column: 10, scope: !2693)
!2745 = !DILocation(line: 52, column: 17, scope: !2743)
!2746 = !DILocation(line: 52, column: 10, scope: !2743)
!2747 = !DILocation(line: 54, column: 18, scope: !2743)
!2748 = !DILocation(line: 54, column: 17, scope: !2743)
!2749 = !DILocation(line: 55, column: 6, scope: !2693)
!2750 = !DILocation(line: 57, column: 15, scope: !2689)
!2751 = !DILocation(line: 57, column: 14, scope: !2689)
!2752 = !DILocation(line: 58, column: 11, scope: !2670)
!2753 = !DILocation(line: 58, column: 4, scope: !2670)
!2754 = distinct !DISubprogram(name: "GPIO_unexport", scope: !320, file: !320, line: 61, type: !2671, isLocal: false, isDefinition: true, scopeLine: 62, flags: DIFlagPrototyped, isOptimized: false, unit: !319, variables: !2)
!2755 = !DILocalVariable(name: "pin", arg: 1, scope: !2754, file: !320, line: 61, type: !12)
!2756 = !DILocation(line: 61, column: 23, scope: !2754)
!2757 = !DILocalVariable(name: "name_buffer", scope: !2754, file: !320, line: 63, type: !2676)
!2758 = !DILocation(line: 63, column: 9, scope: !2754)
!2759 = !DILocalVariable(name: "bytes_written", scope: !2754, file: !320, line: 64, type: !2679)
!2760 = !DILocation(line: 64, column: 12, scope: !2754)
!2761 = !DILocalVariable(name: "fd", scope: !2754, file: !320, line: 65, type: !12)
!2762 = !DILocation(line: 65, column: 8, scope: !2754)
!2763 = !DILocalVariable(name: "ret_err", scope: !2754, file: !320, line: 66, type: !12)
!2764 = !DILocation(line: 66, column: 8, scope: !2754)
!2765 = !DILocation(line: 68, column: 9, scope: !2754)
!2766 = !DILocation(line: 68, column: 7, scope: !2754)
!2767 = !DILocation(line: 69, column: 13, scope: !2768)
!2768 = distinct !DILexicalBlock(scope: !2754, file: !320, line: 69, column: 7)
!2769 = !DILocation(line: 69, column: 10, scope: !2768)
!2770 = !DILocation(line: 69, column: 7, scope: !2754)
!2771 = !DILocation(line: 71, column: 32, scope: !2772)
!2772 = distinct !DILexicalBlock(scope: !2768, file: !320, line: 70, column: 6)
!2773 = !DILocation(line: 71, column: 74, scope: !2772)
!2774 = !DILocation(line: 71, column: 23, scope: !2772)
!2775 = !DILocation(line: 71, column: 21, scope: !2772)
!2776 = !DILocation(line: 72, column: 13, scope: !2772)
!2777 = !DILocation(line: 72, column: 17, scope: !2772)
!2778 = !DILocation(line: 72, column: 30, scope: !2772)
!2779 = !DILocation(line: 72, column: 7, scope: !2772)
!2780 = !DILocation(line: 73, column: 13, scope: !2772)
!2781 = !DILocation(line: 73, column: 7, scope: !2772)
!2782 = !DILocation(line: 74, column: 14, scope: !2772)
!2783 = !DILocation(line: 75, column: 6, scope: !2772)
!2784 = !DILocation(line: 77, column: 16, scope: !2768)
!2785 = !DILocation(line: 77, column: 15, scope: !2768)
!2786 = !DILocation(line: 78, column: 11, scope: !2754)
!2787 = !DILocation(line: 78, column: 4, scope: !2754)
!2788 = distinct !DISubprogram(name: "GPIO_direction", scope: !320, file: !320, line: 81, type: !2789, isLocal: false, isDefinition: true, scopeLine: 82, flags: DIFlagPrototyped, isOptimized: false, unit: !319, variables: !2)
!2789 = !DISubroutineType(types: !2790)
!2790 = !{!12, !12, !12}
!2791 = !DILocalVariable(name: "pin", arg: 1, scope: !2788, file: !320, line: 81, type: !12)
!2792 = !DILocation(line: 81, column: 24, scope: !2788)
!2793 = !DILocalVariable(name: "dir", arg: 2, scope: !2788, file: !320, line: 81, type: !12)
!2794 = !DILocation(line: 81, column: 33, scope: !2788)
!2795 = !DILocalVariable(name: "s_directions_str", scope: !2788, file: !320, line: 83, type: !2796)
!2796 = !DICompositeType(tag: DW_TAG_array_type, baseType: !2120, size: 64, align: 32, elements: !13)
!2797 = !DILocation(line: 83, column: 16, scope: !2788)
!2798 = !DILocalVariable(name: "path", scope: !2788, file: !320, line: 84, type: !2694)
!2799 = !DILocation(line: 84, column: 9, scope: !2788)
!2800 = !DILocalVariable(name: "fd", scope: !2788, file: !320, line: 85, type: !12)
!2801 = !DILocation(line: 85, column: 8, scope: !2788)
!2802 = !DILocalVariable(name: "ret_err", scope: !2788, file: !320, line: 86, type: !12)
!2803 = !DILocation(line: 86, column: 8, scope: !2788)
!2804 = !DILocation(line: 88, column: 13, scope: !2788)
!2805 = !DILocation(line: 88, column: 83, scope: !2788)
!2806 = !DILocation(line: 88, column: 4, scope: !2788)
!2807 = !DILocation(line: 89, column: 14, scope: !2788)
!2808 = !DILocation(line: 89, column: 9, scope: !2788)
!2809 = !DILocation(line: 89, column: 7, scope: !2788)
!2810 = !DILocation(line: 90, column: 13, scope: !2811)
!2811 = distinct !DILexicalBlock(scope: !2788, file: !320, line: 90, column: 7)
!2812 = !DILocation(line: 90, column: 10, scope: !2811)
!2813 = !DILocation(line: 90, column: 7, scope: !2788)
!2814 = !DILocalVariable(name: "curr_dir_str", scope: !2815, file: !320, line: 92, type: !2120)
!2815 = distinct !DILexicalBlock(scope: !2811, file: !320, line: 91, column: 6)
!2816 = !DILocation(line: 92, column: 19, scope: !2815)
!2817 = !DILocation(line: 94, column: 51, scope: !2815)
!2818 = !DILocation(line: 94, column: 48, scope: !2815)
!2819 = !DILocation(line: 94, column: 20, scope: !2815)
!2820 = !DILocation(line: 94, column: 19, scope: !2815)
!2821 = !DILocation(line: 95, column: 23, scope: !2822)
!2822 = distinct !DILexicalBlock(scope: !2815, file: !320, line: 95, column: 11)
!2823 = !DILocation(line: 95, column: 27, scope: !2822)
!2824 = !DILocation(line: 95, column: 48, scope: !2822)
!2825 = !DILocation(line: 95, column: 41, scope: !2822)
!2826 = !DILocation(line: 95, column: 17, scope: !2827)
!2827 = !DILexicalBlockFile(scope: !2822, file: !320, discriminator: 1)
!2828 = !DILocation(line: 95, column: 14, scope: !2822)
!2829 = !DILocation(line: 95, column: 11, scope: !2815)
!2830 = !DILocation(line: 96, column: 17, scope: !2822)
!2831 = !DILocation(line: 96, column: 10, scope: !2822)
!2832 = !DILocation(line: 98, column: 18, scope: !2822)
!2833 = !DILocation(line: 98, column: 17, scope: !2822)
!2834 = !DILocation(line: 99, column: 13, scope: !2815)
!2835 = !DILocation(line: 99, column: 7, scope: !2815)
!2836 = !DILocation(line: 100, column: 6, scope: !2815)
!2837 = !DILocation(line: 102, column: 16, scope: !2811)
!2838 = !DILocation(line: 102, column: 15, scope: !2811)
!2839 = !DILocation(line: 103, column: 11, scope: !2788)
!2840 = !DILocation(line: 103, column: 4, scope: !2788)
!2841 = distinct !DISubprogram(name: "GPIO_read", scope: !320, file: !320, line: 106, type: !2842, isLocal: false, isDefinition: true, scopeLine: 107, flags: DIFlagPrototyped, isOptimized: false, unit: !319, variables: !2)
!2842 = !DISubroutineType(types: !2843)
!2843 = !{!12, !12, !1582}
!2844 = !DILocalVariable(name: "pin", arg: 1, scope: !2841, file: !320, line: 106, type: !12)
!2845 = !DILocation(line: 106, column: 19, scope: !2841)
!2846 = !DILocalVariable(name: "value", arg: 2, scope: !2841, file: !320, line: 106, type: !1582)
!2847 = !DILocation(line: 106, column: 29, scope: !2841)
!2848 = !DILocalVariable(name: "path", scope: !2841, file: !320, line: 108, type: !2849)
!2849 = !DICompositeType(tag: DW_TAG_array_type, baseType: !19, size: 240, align: 8, elements: !2850)
!2850 = !{!2851}
!2851 = !DISubrange(count: 30)
!2852 = !DILocation(line: 108, column: 9, scope: !2841)
!2853 = !DILocalVariable(name: "value_str", scope: !2841, file: !320, line: 109, type: !2676)
!2854 = !DILocation(line: 109, column: 9, scope: !2841)
!2855 = !DILocalVariable(name: "fd", scope: !2841, file: !320, line: 110, type: !12)
!2856 = !DILocation(line: 110, column: 8, scope: !2841)
!2857 = !DILocalVariable(name: "ret_err", scope: !2841, file: !320, line: 111, type: !12)
!2858 = !DILocation(line: 111, column: 8, scope: !2841)
!2859 = !DILocation(line: 113, column: 7, scope: !2860)
!2860 = distinct !DILexicalBlock(scope: !2841, file: !320, line: 113, column: 7)
!2861 = !DILocation(line: 113, column: 13, scope: !2860)
!2862 = !DILocation(line: 113, column: 7, scope: !2841)
!2863 = !DILocation(line: 115, column: 16, scope: !2864)
!2864 = distinct !DILexicalBlock(scope: !2860, file: !320, line: 114, column: 6)
!2865 = !DILocation(line: 115, column: 78, scope: !2864)
!2866 = !DILocation(line: 115, column: 7, scope: !2864)
!2867 = !DILocation(line: 116, column: 17, scope: !2864)
!2868 = !DILocation(line: 116, column: 12, scope: !2864)
!2869 = !DILocation(line: 116, column: 10, scope: !2864)
!2870 = !DILocation(line: 117, column: 16, scope: !2871)
!2871 = distinct !DILexicalBlock(scope: !2864, file: !320, line: 117, column: 10)
!2872 = !DILocation(line: 117, column: 13, scope: !2871)
!2873 = !DILocation(line: 117, column: 10, scope: !2864)
!2874 = !DILocation(line: 119, column: 25, scope: !2875)
!2875 = distinct !DILexicalBlock(scope: !2876, file: !320, line: 119, column: 14)
!2876 = distinct !DILexicalBlock(scope: !2871, file: !320, line: 118, column: 9)
!2877 = !DILocation(line: 119, column: 29, scope: !2875)
!2878 = !DILocation(line: 119, column: 20, scope: !2875)
!2879 = !DILocation(line: 119, column: 17, scope: !2875)
!2880 = !DILocation(line: 119, column: 14, scope: !2876)
!2881 = !DILocation(line: 121, column: 13, scope: !2882)
!2882 = distinct !DILexicalBlock(scope: !2875, file: !320, line: 120, column: 12)
!2883 = !DILocation(line: 121, column: 43, scope: !2882)
!2884 = !DILocation(line: 122, column: 25, scope: !2882)
!2885 = !DILocation(line: 122, column: 20, scope: !2882)
!2886 = !DILocation(line: 122, column: 14, scope: !2882)
!2887 = !DILocation(line: 122, column: 19, scope: !2882)
!2888 = !DILocation(line: 123, column: 20, scope: !2882)
!2889 = !DILocation(line: 124, column: 12, scope: !2882)
!2890 = !DILocation(line: 126, column: 21, scope: !2875)
!2891 = !DILocation(line: 126, column: 20, scope: !2875)
!2892 = !DILocation(line: 127, column: 16, scope: !2876)
!2893 = !DILocation(line: 127, column: 10, scope: !2876)
!2894 = !DILocation(line: 128, column: 9, scope: !2876)
!2895 = !DILocation(line: 130, column: 18, scope: !2871)
!2896 = !DILocation(line: 130, column: 17, scope: !2871)
!2897 = !DILocation(line: 131, column: 6, scope: !2864)
!2898 = !DILocation(line: 133, column: 14, scope: !2860)
!2899 = !DILocation(line: 134, column: 11, scope: !2841)
!2900 = !DILocation(line: 134, column: 4, scope: !2841)
!2901 = distinct !DISubprogram(name: "GPIO_write", scope: !320, file: !320, line: 137, type: !2789, isLocal: false, isDefinition: true, scopeLine: 138, flags: DIFlagPrototyped, isOptimized: false, unit: !319, variables: !2)
!2902 = !DILocalVariable(name: "pin", arg: 1, scope: !2901, file: !320, line: 137, type: !12)
!2903 = !DILocation(line: 137, column: 20, scope: !2901)
!2904 = !DILocalVariable(name: "value", arg: 2, scope: !2901, file: !320, line: 137, type: !12)
!2905 = !DILocation(line: 137, column: 29, scope: !2901)
!2906 = !DILocalVariable(name: "s_values_str", scope: !2901, file: !320, line: 139, type: !2796)
!2907 = !DILocation(line: 139, column: 16, scope: !2901)
!2908 = !DILocalVariable(name: "path", scope: !2901, file: !320, line: 140, type: !2849)
!2909 = !DILocation(line: 140, column: 9, scope: !2901)
!2910 = !DILocalVariable(name: "fd", scope: !2901, file: !320, line: 141, type: !12)
!2911 = !DILocation(line: 141, column: 8, scope: !2901)
!2912 = !DILocalVariable(name: "ret_err", scope: !2901, file: !320, line: 142, type: !12)
!2913 = !DILocation(line: 142, column: 8, scope: !2901)
!2914 = !DILocation(line: 144, column: 13, scope: !2901)
!2915 = !DILocation(line: 144, column: 75, scope: !2901)
!2916 = !DILocation(line: 144, column: 4, scope: !2901)
!2917 = !DILocation(line: 145, column: 14, scope: !2901)
!2918 = !DILocation(line: 145, column: 9, scope: !2901)
!2919 = !DILocation(line: 145, column: 7, scope: !2901)
!2920 = !DILocation(line: 146, column: 13, scope: !2921)
!2921 = distinct !DILexicalBlock(scope: !2901, file: !320, line: 146, column: 7)
!2922 = !DILocation(line: 146, column: 10, scope: !2921)
!2923 = !DILocation(line: 146, column: 7, scope: !2901)
!2924 = !DILocalVariable(name: "curr_dir_str", scope: !2925, file: !320, line: 148, type: !2120)
!2925 = distinct !DILexicalBlock(scope: !2921, file: !320, line: 147, column: 6)
!2926 = !DILocation(line: 148, column: 19, scope: !2925)
!2927 = !DILocation(line: 150, column: 48, scope: !2925)
!2928 = !DILocation(line: 150, column: 45, scope: !2925)
!2929 = !DILocation(line: 150, column: 20, scope: !2925)
!2930 = !DILocation(line: 150, column: 19, scope: !2925)
!2931 = !DILocation(line: 151, column: 22, scope: !2932)
!2932 = distinct !DILexicalBlock(scope: !2925, file: !320, line: 151, column: 10)
!2933 = !DILocation(line: 151, column: 26, scope: !2932)
!2934 = !DILocation(line: 151, column: 47, scope: !2932)
!2935 = !DILocation(line: 151, column: 40, scope: !2932)
!2936 = !DILocation(line: 151, column: 16, scope: !2937)
!2937 = !DILexicalBlockFile(scope: !2932, file: !320, discriminator: 1)
!2938 = !DILocation(line: 151, column: 13, scope: !2932)
!2939 = !DILocation(line: 151, column: 10, scope: !2925)
!2940 = !DILocation(line: 152, column: 17, scope: !2932)
!2941 = !DILocation(line: 152, column: 10, scope: !2932)
!2942 = !DILocation(line: 154, column: 18, scope: !2932)
!2943 = !DILocation(line: 154, column: 17, scope: !2932)
!2944 = !DILocation(line: 155, column: 13, scope: !2925)
!2945 = !DILocation(line: 155, column: 7, scope: !2925)
!2946 = !DILocation(line: 156, column: 6, scope: !2925)
!2947 = !DILocation(line: 158, column: 16, scope: !2921)
!2948 = !DILocation(line: 158, column: 15, scope: !2921)
!2949 = !DILocation(line: 159, column: 11, scope: !2901)
!2950 = !DILocation(line: 159, column: 4, scope: !2901)
!2951 = distinct !DISubprogram(name: "export_gpios", scope: !320, file: !320, line: 162, type: !346, isLocal: false, isDefinition: true, scopeLine: 163, flags: DIFlagPrototyped, isOptimized: false, unit: !319, variables: !2)
!2952 = !DILocalVariable(name: "ret_err", scope: !2951, file: !320, line: 164, type: !12)
!2953 = !DILocation(line: 164, column: 8, scope: !2951)
!2954 = !DILocalVariable(name: "fn_err_num", scope: !2951, file: !320, line: 165, type: !12)
!2955 = !DILocation(line: 165, column: 8, scope: !2951)
!2956 = !DILocation(line: 168, column: 15, scope: !2951)
!2957 = !DILocation(line: 168, column: 14, scope: !2951)
!2958 = !DILocation(line: 169, column: 13, scope: !2959)
!2959 = distinct !DILexicalBlock(scope: !2951, file: !320, line: 169, column: 8)
!2960 = !DILocation(line: 169, column: 10, scope: !2959)
!2961 = !DILocation(line: 169, column: 8, scope: !2951)
!2962 = !DILocation(line: 171, column: 18, scope: !2963)
!2963 = distinct !DILexicalBlock(scope: !2959, file: !320, line: 170, column: 6)
!2964 = !DILocation(line: 171, column: 17, scope: !2963)
!2965 = !DILocation(line: 172, column: 16, scope: !2966)
!2966 = distinct !DILexicalBlock(scope: !2963, file: !320, line: 172, column: 11)
!2967 = !DILocation(line: 172, column: 13, scope: !2966)
!2968 = !DILocation(line: 172, column: 11, scope: !2963)
!2969 = !DILocation(line: 174, column: 21, scope: !2970)
!2970 = distinct !DILexicalBlock(scope: !2966, file: !320, line: 173, column: 9)
!2971 = !DILocation(line: 174, column: 20, scope: !2970)
!2972 = !DILocation(line: 175, column: 19, scope: !2973)
!2973 = distinct !DILexicalBlock(scope: !2970, file: !320, line: 175, column: 14)
!2974 = !DILocation(line: 175, column: 16, scope: !2973)
!2975 = !DILocation(line: 175, column: 14, scope: !2970)
!2976 = !DILocation(line: 177, column: 24, scope: !2977)
!2977 = distinct !DILexicalBlock(scope: !2973, file: !320, line: 176, column: 12)
!2978 = !DILocation(line: 177, column: 23, scope: !2977)
!2979 = !DILocation(line: 178, column: 22, scope: !2980)
!2980 = distinct !DILexicalBlock(scope: !2977, file: !320, line: 178, column: 17)
!2981 = !DILocation(line: 178, column: 19, scope: !2980)
!2982 = !DILocation(line: 178, column: 17, scope: !2977)
!2983 = !DILocation(line: 180, column: 27, scope: !2984)
!2984 = distinct !DILexicalBlock(scope: !2980, file: !320, line: 179, column: 15)
!2985 = !DILocation(line: 180, column: 26, scope: !2984)
!2986 = !DILocation(line: 181, column: 25, scope: !2987)
!2987 = distinct !DILexicalBlock(scope: !2984, file: !320, line: 181, column: 20)
!2988 = !DILocation(line: 181, column: 22, scope: !2987)
!2989 = !DILocation(line: 181, column: 20, scope: !2984)
!2990 = !DILocation(line: 183, column: 26, scope: !2991)
!2991 = distinct !DILexicalBlock(scope: !2987, file: !320, line: 182, column: 18)
!2992 = !DILocation(line: 184, column: 18, scope: !2991)
!2993 = !DILocation(line: 187, column: 27, scope: !2994)
!2994 = distinct !DILexicalBlock(scope: !2987, file: !320, line: 186, column: 18)
!2995 = !DILocation(line: 187, column: 26, scope: !2994)
!2996 = !DILocation(line: 188, column: 19, scope: !2994)
!2997 = !DILocation(line: 188, column: 19, scope: !2998)
!2998 = !DILexicalBlockFile(scope: !2994, file: !320, discriminator: 1)
!2999 = !DILocation(line: 189, column: 19, scope: !2994)
!3000 = !DILocation(line: 190, column: 19, scope: !2994)
!3001 = !DILocation(line: 191, column: 19, scope: !2994)
!3002 = !DILocation(line: 192, column: 19, scope: !2994)
!3003 = !DILocation(line: 194, column: 15, scope: !2984)
!3004 = !DILocation(line: 197, column: 24, scope: !3005)
!3005 = distinct !DILexicalBlock(scope: !2980, file: !320, line: 196, column: 15)
!3006 = !DILocation(line: 197, column: 23, scope: !3005)
!3007 = !DILocation(line: 198, column: 16, scope: !3005)
!3008 = !DILocation(line: 198, column: 16, scope: !3009)
!3009 = !DILexicalBlockFile(scope: !3005, file: !320, discriminator: 1)
!3010 = !DILocation(line: 199, column: 16, scope: !3005)
!3011 = !DILocation(line: 200, column: 16, scope: !3005)
!3012 = !DILocation(line: 201, column: 16, scope: !3005)
!3013 = !DILocation(line: 203, column: 12, scope: !2977)
!3014 = !DILocation(line: 206, column: 21, scope: !3015)
!3015 = distinct !DILexicalBlock(scope: !2973, file: !320, line: 205, column: 12)
!3016 = !DILocation(line: 206, column: 20, scope: !3015)
!3017 = !DILocation(line: 207, column: 13, scope: !3015)
!3018 = !DILocation(line: 207, column: 13, scope: !3019)
!3019 = !DILexicalBlockFile(scope: !3015, file: !320, discriminator: 1)
!3020 = !DILocation(line: 208, column: 13, scope: !3015)
!3021 = !DILocation(line: 209, column: 13, scope: !3015)
!3022 = !DILocation(line: 211, column: 9, scope: !2970)
!3023 = !DILocation(line: 214, column: 18, scope: !3024)
!3024 = distinct !DILexicalBlock(scope: !2966, file: !320, line: 213, column: 9)
!3025 = !DILocation(line: 214, column: 17, scope: !3024)
!3026 = !DILocation(line: 215, column: 10, scope: !3024)
!3027 = !DILocation(line: 215, column: 10, scope: !3028)
!3028 = !DILexicalBlockFile(scope: !3024, file: !320, discriminator: 1)
!3029 = !DILocation(line: 216, column: 10, scope: !3024)
!3030 = !DILocation(line: 218, column: 6, scope: !2963)
!3031 = !DILocation(line: 221, column: 15, scope: !3032)
!3032 = distinct !DILexicalBlock(scope: !2959, file: !320, line: 220, column: 6)
!3033 = !DILocation(line: 221, column: 14, scope: !3032)
!3034 = !DILocation(line: 222, column: 7, scope: !3032)
!3035 = !DILocation(line: 222, column: 7, scope: !3036)
!3036 = !DILexicalBlockFile(scope: !3032, file: !320, discriminator: 1)
!3037 = !DILocation(line: 225, column: 11, scope: !2951)
!3038 = !DILocation(line: 225, column: 4, scope: !2951)
!3039 = distinct !DISubprogram(name: "configure_gpios", scope: !320, file: !320, line: 228, type: !346, isLocal: false, isDefinition: true, scopeLine: 229, flags: DIFlagPrototyped, isOptimized: false, unit: !319, variables: !2)
!3040 = !DILocalVariable(name: "ret_err", scope: !3039, file: !320, line: 230, type: !12)
!3041 = !DILocation(line: 230, column: 8, scope: !3039)
!3042 = !DILocalVariable(name: "curr_gpio", scope: !3039, file: !320, line: 231, type: !12)
!3043 = !DILocation(line: 231, column: 8, scope: !3039)
!3044 = !DILocation(line: 234, column: 13, scope: !3039)
!3045 = !DILocation(line: 235, column: 27, scope: !3039)
!3046 = !DILocation(line: 235, column: 12, scope: !3039)
!3047 = !DILocation(line: 235, column: 11, scope: !3039)
!3048 = !DILocation(line: 236, column: 13, scope: !3049)
!3049 = distinct !DILexicalBlock(scope: !3039, file: !320, line: 236, column: 8)
!3050 = !DILocation(line: 236, column: 10, scope: !3049)
!3051 = !DILocation(line: 236, column: 8, scope: !3039)
!3052 = !DILocation(line: 238, column: 16, scope: !3053)
!3053 = distinct !DILexicalBlock(scope: !3049, file: !320, line: 237, column: 6)
!3054 = !DILocation(line: 239, column: 30, scope: !3053)
!3055 = !DILocation(line: 239, column: 15, scope: !3053)
!3056 = !DILocation(line: 239, column: 14, scope: !3053)
!3057 = !DILocation(line: 240, column: 16, scope: !3058)
!3058 = distinct !DILexicalBlock(scope: !3053, file: !320, line: 240, column: 11)
!3059 = !DILocation(line: 240, column: 13, scope: !3058)
!3060 = !DILocation(line: 240, column: 11, scope: !3053)
!3061 = !DILocation(line: 242, column: 21, scope: !3062)
!3062 = distinct !DILexicalBlock(scope: !3058, file: !320, line: 241, column: 9)
!3063 = !DILocation(line: 242, column: 10, scope: !3062)
!3064 = !DILocation(line: 243, column: 19, scope: !3062)
!3065 = !DILocation(line: 244, column: 33, scope: !3062)
!3066 = !DILocation(line: 244, column: 18, scope: !3062)
!3067 = !DILocation(line: 244, column: 17, scope: !3062)
!3068 = !DILocation(line: 245, column: 19, scope: !3069)
!3069 = distinct !DILexicalBlock(scope: !3062, file: !320, line: 245, column: 14)
!3070 = !DILocation(line: 245, column: 16, scope: !3069)
!3071 = !DILocation(line: 245, column: 14, scope: !3062)
!3072 = !DILocation(line: 247, column: 24, scope: !3073)
!3073 = distinct !DILexicalBlock(scope: !3069, file: !320, line: 246, column: 12)
!3074 = !DILocation(line: 247, column: 13, scope: !3073)
!3075 = !DILocation(line: 248, column: 22, scope: !3073)
!3076 = !DILocation(line: 249, column: 36, scope: !3073)
!3077 = !DILocation(line: 249, column: 21, scope: !3073)
!3078 = !DILocation(line: 249, column: 20, scope: !3073)
!3079 = !DILocation(line: 250, column: 22, scope: !3080)
!3080 = distinct !DILexicalBlock(scope: !3073, file: !320, line: 250, column: 17)
!3081 = !DILocation(line: 250, column: 19, scope: !3080)
!3082 = !DILocation(line: 250, column: 17, scope: !3073)
!3083 = !DILocation(line: 252, column: 27, scope: !3084)
!3084 = distinct !DILexicalBlock(scope: !3080, file: !320, line: 251, column: 15)
!3085 = !DILocation(line: 252, column: 16, scope: !3084)
!3086 = !DILocation(line: 253, column: 25, scope: !3084)
!3087 = !DILocation(line: 254, column: 39, scope: !3084)
!3088 = !DILocation(line: 254, column: 24, scope: !3084)
!3089 = !DILocation(line: 254, column: 23, scope: !3084)
!3090 = !DILocation(line: 255, column: 25, scope: !3091)
!3091 = distinct !DILexicalBlock(scope: !3084, file: !320, line: 255, column: 20)
!3092 = !DILocation(line: 255, column: 22, scope: !3091)
!3093 = !DILocation(line: 255, column: 20, scope: !3084)
!3094 = !DILocation(line: 256, column: 30, scope: !3091)
!3095 = !DILocation(line: 256, column: 19, scope: !3091)
!3096 = !DILocation(line: 257, column: 15, scope: !3084)
!3097 = !DILocation(line: 258, column: 12, scope: !3073)
!3098 = !DILocation(line: 259, column: 9, scope: !3062)
!3099 = !DILocation(line: 260, column: 6, scope: !3053)
!3100 = !DILocation(line: 261, column: 7, scope: !3101)
!3101 = distinct !DILexicalBlock(scope: !3039, file: !320, line: 261, column: 7)
!3102 = !DILocation(line: 261, column: 15, scope: !3101)
!3103 = !DILocation(line: 261, column: 7, scope: !3039)
!3104 = !DILocation(line: 262, column: 7, scope: !3101)
!3105 = !DILocation(line: 262, column: 7, scope: !3106)
!3106 = !DILexicalBlockFile(scope: !3101, file: !320, discriminator: 1)
!3107 = !DILocation(line: 264, column: 11, scope: !3039)
!3108 = !DILocation(line: 264, column: 4, scope: !3039)
!3109 = distinct !DISubprogram(name: "unexport_gpios", scope: !320, file: !320, line: 267, type: !346, isLocal: false, isDefinition: true, scopeLine: 268, flags: DIFlagPrototyped, isOptimized: false, unit: !319, variables: !2)
!3110 = !DILocalVariable(name: "ret_err", scope: !3109, file: !320, line: 269, type: !12)
!3111 = !DILocation(line: 269, column: 8, scope: !3109)
!3112 = !DILocation(line: 271, column: 11, scope: !3109)
!3113 = !DILocation(line: 273, column: 14, scope: !3109)
!3114 = !DILocation(line: 273, column: 11, scope: !3109)
!3115 = !DILocation(line: 274, column: 14, scope: !3109)
!3116 = !DILocation(line: 274, column: 11, scope: !3109)
!3117 = !DILocation(line: 275, column: 14, scope: !3109)
!3118 = !DILocation(line: 275, column: 11, scope: !3109)
!3119 = !DILocation(line: 276, column: 14, scope: !3109)
!3120 = !DILocation(line: 276, column: 11, scope: !3109)
!3121 = !DILocation(line: 277, column: 14, scope: !3109)
!3122 = !DILocation(line: 277, column: 11, scope: !3109)
!3123 = !DILocation(line: 278, column: 7, scope: !3124)
!3124 = distinct !DILexicalBlock(scope: !3109, file: !320, line: 278, column: 7)
!3125 = !DILocation(line: 278, column: 15, scope: !3124)
!3126 = !DILocation(line: 278, column: 7, scope: !3109)
!3127 = !DILocation(line: 279, column: 7, scope: !3124)
!3128 = !DILocation(line: 279, column: 7, scope: !3129)
!3129 = !DILexicalBlockFile(scope: !3124, file: !320, discriminator: 1)
!3130 = !DILocation(line: 281, column: 11, scope: !3109)
!3131 = !DILocation(line: 281, column: 4, scope: !3109)
