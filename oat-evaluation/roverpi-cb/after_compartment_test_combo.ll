; ModuleID = 'after_compartment_test_combo.bc'
source_filename = "llvm-link"
target datalayout = "e-m:e-p:32:32-i64:64-v128:64:128-a:0:32-n32-S64"
target triple = "armv6kz--linux-gnueabihf"

%struct.timeval = type { i32, i32 }
%struct.sockaddr_in = type { i16, i16, %struct.in_addr, [8 x i8] }
%struct.in_addr = type { i32 }
%struct.sockaddr = type { i16, [14 x i8] }

@.str = private unnamed_addr constant [34 x i8] c"%s (int pin = %d, int mode = %d)\0A\00", align 1
@__func__.pinMode = private unnamed_addr constant [8 x i8] c"pinMode\00", section ".DATA_REGION_2__data", align 1
@.str.1 = private unnamed_addr constant [19 x i8] c"%s (int pin = %d)\0A\00", align 1
@__func__.digitalRead = private unnamed_addr constant [12 x i8] c"digitalRead\00", section ".DATA_REGION_2__data", align 1
@.str.2 = private unnamed_addr constant [3 x i8] c"%d\00", align 1
@.str.3 = private unnamed_addr constant [20 x i8] c"%s (int baud = %d)\0A\00", align 1
@__func__.Serial_begin = private unnamed_addr constant [13 x i8] c"Serial_begin\00", section ".DATA_REGION_2__data", align 1
@.str.4 = private unnamed_addr constant [11 x i8] c"%s() c:%c\0A\00", align 1
@__func__.Serial_available = private unnamed_addr constant [17 x i8] c"Serial_available\00", section ".DATA_REGION_2__data", align 1
@.str.5 = private unnamed_addr constant [38 x i8] c"%s (char *output = %s, int len = %d)\0A\00", align 1
@__func__.Serial_write = private unnamed_addr constant [13 x i8] c"Serial_write\00", section ".DATA_REGION_2__data", align 1
@.str.6 = private unnamed_addr constant [18 x i8] c"read from pin %d\0A\00", align 1
@recording_flag = global i32 0, section ".DATA_REGION_1__bss", align 4
@recording_cnt = global i32 0, align 4
@portno = common global i32 0, section ".DATA_REGION_0__bss", align 4
@newsockfd = common global i32 0, section ".DATA_REGION_1__bss", align 4
@n = common global i32 0, section ".DATA_REGION_1__bss", align 4
@mode = common global i8 0, section ".DATA_REGION_0__data", align 1
@llvm.global.annotations = appending global [8 x { i8*, i8*, i8*, i32 }] [{ i8*, i8*, i8*, i32 } { i8* bitcast (i32* @n to i8*), i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.5.1, i32 0, i32 0), i8* getelementptr inbounds ([8 x i8], [8 x i8]* @.str.6.2, i32 0, i32 0), i32 7 }, { i8*, i8*, i8*, i32 } { i8* bitcast (i32* @newsockfd to i8*), i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.5.1, i32 0, i32 0), i8* getelementptr inbounds ([8 x i8], [8 x i8]* @.str.6.2, i32 0, i32 0), i32 8 }, { i8*, i8*, i8*, i32 } { i8* bitcast (i32* @portno to i8*), i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.5.1, i32 0, i32 0), i8* getelementptr inbounds ([8 x i8], [8 x i8]* @.str.6.2, i32 0, i32 0), i32 9 }, { i8*, i8*, i8*, i32 } { i8* @mode, i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.5.1, i32 0, i32 0), i8* getelementptr inbounds ([8 x i8], [8 x i8]* @.str.6.2, i32 0, i32 0), i32 10 }, { i8*, i8*, i8*, i32 } { i8* bitcast (i32* @n to i8*), i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.13, i32 0, i32 0), i8* getelementptr inbounds ([8 x i8], [8 x i8]* @.str.16, i32 0, i32 0), i32 7 }, { i8*, i8*, i8*, i32 } { i8* bitcast (i32* @newsockfd to i8*), i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.13, i32 0, i32 0), i8* getelementptr inbounds ([8 x i8], [8 x i8]* @.str.16, i32 0, i32 0), i32 8 }, { i8*, i8*, i8*, i32 } { i8* bitcast (i32* @portno to i8*), i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.13, i32 0, i32 0), i8* getelementptr inbounds ([8 x i8], [8 x i8]* @.str.16, i32 0, i32 0), i32 9 }, { i8*, i8*, i8*, i32 } { i8* @mode, i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.13, i32 0, i32 0), i8* getelementptr inbounds ([8 x i8], [8 x i8]* @.str.16, i32 0, i32 0), i32 10 }], section "llvm.metadata"
@.str.5.1 = private unnamed_addr constant [10 x i8] c"sensitive\00", section "llvm.metadata"
@.str.6.2 = private unnamed_addr constant [8 x i8] c"./tcp.h\00", section "llvm.metadata"
@.str.7 = private unnamed_addr constant [7 x i8] c"%s %d\0A\00", align 1
@__func__.tcpListener = private unnamed_addr constant [12 x i8] c"tcpListener\00", section ".DATA_REGION_1__data", align 1
@.str.1.8 = private unnamed_addr constant [21 x i8] c"ERROR opening socket\00", align 1
@.str.2.9 = private unnamed_addr constant [17 x i8] c"ERROR on binding\00", align 1
@.str.3.10 = private unnamed_addr constant [16 x i8] c"ERROR on accept\00", align 1
@.str.4.11 = private unnamed_addr constant [15 x i8] c"Recieved 0x%x\0A\00", align 1
@ret_recording_finish = external global i32, align 4
@.str.13 = private unnamed_addr constant [10 x i8] c"sensitive\00", section "llvm.metadata"
@.str.16 = private unnamed_addr constant [8 x i8] c"./tcp.h\00", section "llvm.metadata"
@.str.1.14 = private unnamed_addr constant [11 x i8] c"rovertcp.c\00", section "llvm.metadata"
@.str.2.15 = private unnamed_addr constant [17 x i8] c"./ARI_branch.txt\00", align 1
@.str.3.16 = private unnamed_addr constant [18 x i8] c"./ARI_ind_jmp.txt\00", align 1
@.str.4.17 = private unnamed_addr constant [19 x i8] c"./ARI_ret_hash.txt\00", align 1
@.str.5.18 = private unnamed_addr constant [14 x i8] c"./ARI_tsf.txt\00", align 1
@.str.6.19 = private unnamed_addr constant [19 x i8] c"./ARI_tsf_cond.txt\00", align 1
@.str.7.20 = private unnamed_addr constant [32 x i8] c"What port do you want to open?\0A\00", align 1
@.str.8 = private unnamed_addr constant [3 x i8] c"%d\00", align 1
@.str.9 = private unnamed_addr constant [20 x i8] c"Starting Mainloop!\0A\00", align 1
@.str.10 = private unnamed_addr constant [7 x i8] c"%s %d\0A\00", align 1
@__func__.main = private unnamed_addr constant [5 x i8] c"main\00", section ".DATA_REGION_2__data", align 1
@.str.11 = private unnamed_addr constant [9 x i8] c"Forward\0A\00", align 1
@.str.12 = private unnamed_addr constant [10 x i8] c"Backward\0A\00", align 1
@.str.13.21 = private unnamed_addr constant [6 x i8] c"Left\0A\00", align 1
@.str.14 = private unnamed_addr constant [7 x i8] c"Right\0A\00", align 1
@.str.15 = private unnamed_addr constant [40 x i8] c"round with attestation time usecs: %lu\0A\00", align 1

; Function Attrs: nounwind
define void @pinMode(i32, i32) #0 section ".CODE_REGION_2_" !dbg !68 {
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  store i32 %0, i32* %3, align 4
  call void @llvm.dbg.declare(metadata i32* %3, metadata !71, metadata !72), !dbg !73
  store i32 %1, i32* %4, align 4
  call void @llvm.dbg.declare(metadata i32* %4, metadata !74, metadata !72), !dbg !75
  %5 = load i32, i32* %3, align 4, !dbg !76
  %6 = load i32, i32* %4, align 4, !dbg !77
  %7 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([34 x i8], [34 x i8]* @.str, i32 0, i32 0), i8* getelementptr inbounds ([8 x i8], [8 x i8]* @__func__.pinMode, i32 0, i32 0), i32 %5, i32 %6), !dbg !78
  ret void, !dbg !79
}

; Function Attrs: nounwind readnone
declare void @llvm.dbg.declare(metadata, metadata, metadata) #1

declare i32 @printf(i8*, ...) #2 section ".CODE_REGION_1_"

; Function Attrs: nounwind
define i32 @digitalRead(i32) #0 section ".CODE_REGION_2_" !dbg !80 {
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  store i32 %0, i32* %2, align 4
  call void @llvm.dbg.declare(metadata i32* %2, metadata !83, metadata !72), !dbg !84
  call void @llvm.dbg.declare(metadata i32* %3, metadata !85, metadata !72), !dbg !86
  %4 = load i32, i32* %2, align 4, !dbg !87
  %5 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([19 x i8], [19 x i8]* @.str.1, i32 0, i32 0), i8* getelementptr inbounds ([12 x i8], [12 x i8]* @__func__.digitalRead, i32 0, i32 0), i32 %4), !dbg !88
  %6 = call i32 (i8*, ...) @__isoc99_scanf(i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.2, i32 0, i32 0), i32* %3), !dbg !89
  %7 = load i32, i32* %3, align 4, !dbg !90
  ret i32 %7, !dbg !91
}

declare i32 @__isoc99_scanf(i8*, ...) #2 section ".CODE_REGION_2_"

; Function Attrs: nounwind
define void @digitalWrite(i32, i32) #0 section ".CODE_REGION_2_" !dbg !92 {
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  store i32 %0, i32* %3, align 4
  call void @llvm.dbg.declare(metadata i32* %3, metadata !93, metadata !72), !dbg !94
  store i32 %1, i32* %4, align 4
  call void @llvm.dbg.declare(metadata i32* %4, metadata !95, metadata !72), !dbg !96
  ret void, !dbg !97
}

; Function Attrs: nounwind
define void @Serial_begin(i32) #0 section ".CODE_REGION_2_" !dbg !98 {
  %2 = alloca i32, align 4
  store i32 %0, i32* %2, align 4
  call void @llvm.dbg.declare(metadata i32* %2, metadata !101, metadata !72), !dbg !102
  %3 = load i32, i32* %2, align 4, !dbg !103
  %4 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([20 x i8], [20 x i8]* @.str.3, i32 0, i32 0), i8* getelementptr inbounds ([13 x i8], [13 x i8]* @__func__.Serial_begin, i32 0, i32 0), i32 %3), !dbg !104
  ret void, !dbg !105
}

; Function Attrs: nounwind
define i32 @Serial_available() #0 section ".CODE_REGION_2_" !dbg !106 {
  %1 = alloca i32, align 4
  %2 = alloca i8, align 1
  call void @llvm.dbg.declare(metadata i8* %2, metadata !109, metadata !72), !dbg !110
  %3 = call i32 @getchar(), !dbg !111
  %4 = trunc i32 %3 to i8, !dbg !111
  store i8 %4, i8* %2, align 1, !dbg !112
  %5 = load i8, i8* %2, align 1, !dbg !113
  %6 = zext i8 %5 to i32, !dbg !113
  %7 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([11 x i8], [11 x i8]* @.str.4, i32 0, i32 0), i8* getelementptr inbounds ([17 x i8], [17 x i8]* @__func__.Serial_available, i32 0, i32 0), i32 %6), !dbg !114
  %8 = load i8, i8* %2, align 1, !dbg !115
  %9 = zext i8 %8 to i32, !dbg !115
  %10 = icmp eq i32 %9, 121, !dbg !117
  br i1 %10, label %11, label %12, !dbg !118

; <label>:11:                                     ; preds = %0
  store i32 1, i32* %1, align 4, !dbg !119
  br label %13, !dbg !119

; <label>:12:                                     ; preds = %0
  store i32 0, i32* %1, align 4, !dbg !120
  br label %13, !dbg !120

; <label>:13:                                     ; preds = %12, %11
  %14 = load i32, i32* %1, align 4, !dbg !121
  ret i32 %14, !dbg !121
}

declare i32 @getchar() #2 section ".CODE_REGION_2_"

; Function Attrs: nounwind
define i32 @Serial_read() #0 section ".CODE_REGION_2_" !dbg !122 {
  %1 = alloca i8, align 1
  call void @llvm.dbg.declare(metadata i8* %1, metadata !123, metadata !72), !dbg !124
  %2 = call i32 @getchar(), !dbg !125
  %3 = trunc i32 %2 to i8, !dbg !125
  store i8 %3, i8* %1, align 1, !dbg !126
  %4 = load i8, i8* %1, align 1, !dbg !127
  %5 = zext i8 %4 to i32, !dbg !128
  ret i32 %5, !dbg !129
}

; Function Attrs: nounwind
define i32 @Serial_write(i8*, i32) #0 section ".CODE_REGION_2_" !dbg !130 {
  %3 = alloca i8*, align 4
  %4 = alloca i32, align 4
  store i8* %0, i8** %3, align 4
  call void @llvm.dbg.declare(metadata i8** %3, metadata !133, metadata !72), !dbg !134
  store i32 %1, i32* %4, align 4
  call void @llvm.dbg.declare(metadata i32* %4, metadata !135, metadata !72), !dbg !136
  %5 = load i8*, i8** %3, align 4, !dbg !137
  %6 = load i32, i32* %4, align 4, !dbg !138
  %7 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([38 x i8], [38 x i8]* @.str.5, i32 0, i32 0), i8* getelementptr inbounds ([13 x i8], [13 x i8]* @__func__.Serial_write, i32 0, i32 0), i8* %5, i32 %6), !dbg !139
  ret i32 0, !dbg !140
}

; Function Attrs: nounwind
define i32 @analogRead(i32) #0 section ".CODE_REGION_2_" !dbg !141 {
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  store i32 %0, i32* %2, align 4
  call void @llvm.dbg.declare(metadata i32* %2, metadata !142, metadata !72), !dbg !143
  call void @llvm.dbg.declare(metadata i32* %3, metadata !144, metadata !72), !dbg !145
  %4 = load i32, i32* %2, align 4, !dbg !146
  %5 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([18 x i8], [18 x i8]* @.str.6, i32 0, i32 0), i32 %4), !dbg !147
  %6 = call i32 (i8*, ...) @__isoc99_scanf(i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.2, i32 0, i32 0), i32* %3), !dbg !148
  %7 = load i32, i32* %3, align 4, !dbg !149
  ret i32 %7, !dbg !150
}

; Function Attrs: nounwind
define i32 @millis() #0 section ".CODE_REGION_2_" !dbg !151 {
  %1 = alloca %struct.timeval, align 4
  call void @llvm.dbg.declare(metadata %struct.timeval* %1, metadata !155, metadata !72), !dbg !164
  %2 = call i32 @gettimeofday(%struct.timeval* %1, i8* null) #8, !dbg !165
  %3 = getelementptr inbounds %struct.timeval, %struct.timeval* %1, i32 0, i32 0, !dbg !166
  %4 = load i32, i32* %3, align 4, !dbg !166
  %5 = mul nsw i32 %4, 1000, !dbg !167
  %6 = getelementptr inbounds %struct.timeval, %struct.timeval* %1, i32 0, i32 1, !dbg !168
  %7 = load i32, i32* %6, align 4, !dbg !168
  %8 = sdiv i32 %7, 1000, !dbg !169
  %9 = add nsw i32 %5, %8, !dbg !170
  ret i32 %9, !dbg !171
}

; Function Attrs: nounwind
declare i32 @gettimeofday(%struct.timeval*, i8*) #3 section ".CODE_REGION_2_"

; Function Attrs: nounwind
define i32 @usecs() #0 section ".CODE_REGION_2_" !dbg !172 {
  %1 = alloca %struct.timeval, align 4
  call void @llvm.dbg.declare(metadata %struct.timeval* %1, metadata !173, metadata !72), !dbg !174
  %2 = call i32 @gettimeofday(%struct.timeval* %1, i8* null) #8, !dbg !175
  %3 = getelementptr inbounds %struct.timeval, %struct.timeval* %1, i32 0, i32 0, !dbg !176
  %4 = load i32, i32* %3, align 4, !dbg !176
  %5 = mul nsw i32 %4, 1000, !dbg !177
  %6 = mul nsw i32 %5, 1000, !dbg !178
  %7 = getelementptr inbounds %struct.timeval, %struct.timeval* %1, i32 0, i32 1, !dbg !179
  %8 = load i32, i32* %7, align 4, !dbg !179
  %9 = add nsw i32 %6, %8, !dbg !180
  ret i32 %9, !dbg !181
}

; Function Attrs: nounwind
define void @delayMicroseconds(float) #0 section ".CODE_REGION_2_" !dbg !182 {
  %2 = alloca float, align 4
  store float %0, float* %2, align 4
  call void @llvm.dbg.declare(metadata float* %2, metadata !186, metadata !72), !dbg !187
  %3 = load float, float* %2, align 4, !dbg !188
  %4 = fptosi float %3 to i32, !dbg !189
  %5 = call i32 @usleep(i32 %4), !dbg !190
  ret void, !dbg !191
}

declare i32 @usleep(i32) #2 section ".CODE_REGION_1_"

; Function Attrs: nounwind
define i32 @toUInt(i8*, i32) #0 section ".CODE_REGION_2_" !dbg !192 {
  %3 = alloca i8*, align 4
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  store i8* %0, i8** %3, align 4
  call void @llvm.dbg.declare(metadata i8** %3, metadata !193, metadata !72), !dbg !194
  store i32 %1, i32* %4, align 4
  call void @llvm.dbg.declare(metadata i32* %4, metadata !195, metadata !72), !dbg !196
  call void @llvm.dbg.declare(metadata i32* %5, metadata !197, metadata !72), !dbg !198
  %6 = load i8*, i8** %3, align 4, !dbg !199
  %7 = call i32 @atoi(i8* %6) #9, !dbg !200
  store i32 %7, i32* %5, align 4, !dbg !201
  %8 = load i32, i32* %5, align 4, !dbg !202
  ret i32 %8, !dbg !203
}

; Function Attrs: nounwind readonly
declare i32 @atoi(i8*) #4 section ".CODE_REGION_2_"

; Function Attrs: nounwind
define void @tcpError(i8*) #0 section ".CODE_REGION_1_" !dbg !204 {
  %2 = alloca i8*, align 4
  store i8* %0, i8** %2, align 4
  call void @llvm.dbg.declare(metadata i8** %2, metadata !209, metadata !72), !dbg !210
  %3 = load i8*, i8** %2, align 4, !dbg !211
  call void @perror(i8* %3), !dbg !212
  call void @exit(i32 1) #10, !dbg !213
  unreachable, !dbg !213
                                                  ; No predecessors!
  ret void, !dbg !214
}

declare void @perror(i8*) #2 section ".CODE_REGION_1_"

; Function Attrs: noreturn nounwind
declare void @exit(i32) #5 section ".CODE_REGION_1_"

; Function Attrs: nounwind
define i8* @tcpListener(i8*) #0 section ".CODE_REGION_1_" !dbg !215 {
  %2 = alloca i8*, align 4
  %3 = alloca [5 x i8], align 1
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  %7 = alloca %struct.sockaddr_in, align 4
  %8 = alloca %struct.sockaddr_in, align 4
  store i8* %0, i8** %2, align 4
  call void @llvm.dbg.declare(metadata i8** %2, metadata !218, metadata !72), !dbg !219
  call void @__AMI_fake_local_wrt(), !dbg !220
  store i32 1, i32* @recording_flag, align 4, !dbg !220
  call void @llvm.dbg.declare(metadata [5 x i8]* %3, metadata !221, metadata !72), !dbg !225
  call void @llvm.dbg.declare(metadata i32* %4, metadata !226, metadata !72), !dbg !227
  call void @llvm.dbg.declare(metadata i32* %5, metadata !228, metadata !72), !dbg !233
  call void @llvm.dbg.declare(metadata i32* %6, metadata !234, metadata !72), !dbg !235
  call void @llvm.dbg.declare(metadata %struct.sockaddr_in* %7, metadata !236, metadata !72), !dbg !252
  call void @llvm.dbg.declare(metadata %struct.sockaddr_in* %8, metadata !253, metadata !72), !dbg !254
  %9 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.7, i32 0, i32 0), i8* getelementptr inbounds ([12 x i8], [12 x i8]* @__func__.tcpListener, i32 0, i32 0), i32 31), !dbg !255
  %10 = call i32 @socket(i32 2, i32 1, i32 0) #8, !dbg !256
  store i32 %10, i32* %4, align 4, !dbg !257
  %11 = load i32, i32* %4, align 4, !dbg !258
  %12 = icmp slt i32 %11, 0, !dbg !260
  br i1 %12, label %13, label %14, !dbg !261

; <label>:13:                                     ; preds = %1
  call void @tcpError(i8* getelementptr inbounds ([21 x i8], [21 x i8]* @.str.1.8, i32 0, i32 0)), !dbg !262
  br label %14, !dbg !262

; <label>:14:                                     ; preds = %13, %1
  %15 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.7, i32 0, i32 0), i8* getelementptr inbounds ([12 x i8], [12 x i8]* @__func__.tcpListener, i32 0, i32 0), i32 35), !dbg !263
  %16 = bitcast %struct.sockaddr_in* %7 to i8*, !dbg !264
  call void @llvm.memset.p0i8.i32(i8* %16, i8 0, i32 16, i32 4, i1 false), !dbg !264
  %17 = getelementptr inbounds %struct.sockaddr_in, %struct.sockaddr_in* %7, i32 0, i32 0, !dbg !265
  store i16 2, i16* %17, align 4, !dbg !266
  %18 = getelementptr inbounds %struct.sockaddr_in, %struct.sockaddr_in* %7, i32 0, i32 2, !dbg !267
  %19 = getelementptr inbounds %struct.in_addr, %struct.in_addr* %18, i32 0, i32 0, !dbg !268
  store i32 0, i32* %19, align 4, !dbg !269
  %20 = load i32, i32* @portno, align 4, !dbg !270
  %21 = trunc i32 %20 to i16, !dbg !270
  %22 = call zeroext i16 @htons(i16 zeroext %21) #1, !dbg !271
  %23 = getelementptr inbounds %struct.sockaddr_in, %struct.sockaddr_in* %7, i32 0, i32 1, !dbg !272
  store i16 %22, i16* %23, align 2, !dbg !273
  %24 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.7, i32 0, i32 0), i8* getelementptr inbounds ([12 x i8], [12 x i8]* @__func__.tcpListener, i32 0, i32 0), i32 40), !dbg !274
  %25 = load i32, i32* %4, align 4, !dbg !275
  %26 = bitcast %struct.sockaddr_in* %7 to %struct.sockaddr*, !dbg !277
  %27 = call i32 @bind(i32 %25, %struct.sockaddr* %26, i32 16) #8, !dbg !278
  %28 = icmp slt i32 %27, 0, !dbg !279
  br i1 %28, label %29, label %30, !dbg !280

; <label>:29:                                     ; preds = %14
  call void @tcpError(i8* getelementptr inbounds ([17 x i8], [17 x i8]* @.str.2.9, i32 0, i32 0)), !dbg !281
  br label %30, !dbg !281

; <label>:30:                                     ; preds = %29, %14
  %31 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.7, i32 0, i32 0), i8* getelementptr inbounds ([12 x i8], [12 x i8]* @__func__.tcpListener, i32 0, i32 0), i32 43), !dbg !282
  %32 = load i32, i32* %4, align 4, !dbg !283
  %33 = call i32 @listen(i32 %32, i32 5) #8, !dbg !284
  %34 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.7, i32 0, i32 0), i8* getelementptr inbounds ([12 x i8], [12 x i8]* @__func__.tcpListener, i32 0, i32 0), i32 45), !dbg !285
  store i32 16, i32* %5, align 4, !dbg !286
  %35 = call i32 @usleep(i32 200000), !dbg !287
  %36 = load i32, i32* %4, align 4, !dbg !288
  %37 = bitcast %struct.sockaddr_in* %8 to %struct.sockaddr*, !dbg !289
  %38 = call i32 @accept(i32 %36, %struct.sockaddr* %37, i32* %5), !dbg !290
  call void @__AMI_fake_local_wrt(), !dbg !291
  store i32 %38, i32* @newsockfd, align 4, !dbg !291
  %39 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.7, i32 0, i32 0), i8* getelementptr inbounds ([12 x i8], [12 x i8]* @__func__.tcpListener, i32 0, i32 0), i32 50), !dbg !292
  %40 = load i32, i32* @newsockfd, align 4, !dbg !293
  %41 = icmp slt i32 %40, 0, !dbg !295
  br i1 %41, label %42, label %43, !dbg !296

; <label>:42:                                     ; preds = %30
  call void @tcpError(i8* getelementptr inbounds ([16 x i8], [16 x i8]* @.str.3.10, i32 0, i32 0)), !dbg !297
  br label %43, !dbg !297

; <label>:43:                                     ; preds = %42, %30
  %44 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.7, i32 0, i32 0), i8* getelementptr inbounds ([12 x i8], [12 x i8]* @__func__.tcpListener, i32 0, i32 0), i32 53), !dbg !298
  br label %45, !dbg !299

; <label>:45:                                     ; preds = %49, %43
  %46 = load i32, i32* %6, align 4, !dbg !300
  %47 = add nsw i32 %46, 1, !dbg !300
  store i32 %47, i32* %6, align 4, !dbg !300
  %48 = icmp slt i32 %46, 5, !dbg !302
  br i1 %48, label %49, label %60, !dbg !303

; <label>:49:                                     ; preds = %45
  %50 = getelementptr inbounds [5 x i8], [5 x i8]* %3, i32 0, i32 0, !dbg !304
  call void @llvm.memset.p0i8.i32(i8* %50, i8 0, i32 5, i32 1, i1 false), !dbg !304
  %51 = load i32, i32* @newsockfd, align 4, !dbg !306
  %52 = getelementptr inbounds [5 x i8], [5 x i8]* %3, i32 0, i32 0, !dbg !307
  %53 = call i32 @read(i32 %51, i8* %52, i32 4), !dbg !308
  call void @__AMI_fake_local_wrt(), !dbg !309
  store i32 %53, i32* @n, align 4, !dbg !309
  %54 = getelementptr inbounds [5 x i8], [5 x i8]* %3, i32 0, i32 0, !dbg !310
  %55 = load i8, i8* %54, align 1, !dbg !310
  call void @__AMI_fake_shared_wrt(), !dbg !311
  store i8 %55, i8* @mode, align 1, !dbg !311
  %56 = getelementptr inbounds [5 x i8], [5 x i8]* %3, i32 0, i32 0, !dbg !312
  %57 = load i8, i8* %56, align 1, !dbg !312
  %58 = zext i8 %57 to i32, !dbg !312
  %59 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([15 x i8], [15 x i8]* @.str.4.11, i32 0, i32 0), i32 %58), !dbg !313
  br label %45, !dbg !314, !llvm.loop !316

; <label>:60:                                     ; preds = %45
  %61 = load i32, i32* @newsockfd, align 4, !dbg !317
  %62 = call i32 @close(i32 %61), !dbg !318
  %63 = load i32, i32* %4, align 4, !dbg !319
  %64 = call i32 @close(i32 %63), !dbg !320
  call void @__AMI_fake_local_wrt(), !dbg !321
  store i32 0, i32* @recording_flag, align 4, !dbg !321
  call void @__AMI_fake_local_wrt(), !dbg !322
  store i32 1, i32* @ret_recording_finish, align 4, !dbg !322
  %65 = call i8* bitcast (i8* (...)* @read_measurement to i8* ()*)(), !dbg !323
  call void @__AMI_fake_rt_transfer(), !dbg !324
  ret i8* null, !dbg !324
}

; Function Attrs: nounwind
declare i32 @socket(i32, i32, i32) #3 section ".CODE_REGION_1_"

; Function Attrs: argmemonly nounwind
declare void @llvm.memset.p0i8.i32(i8* nocapture writeonly, i8, i32, i32, i1) #6

; Function Attrs: nounwind readnone
declare zeroext i16 @htons(i16 zeroext) #7 section ".CODE_REGION_1_"

; Function Attrs: nounwind
declare i32 @bind(i32, %struct.sockaddr*, i32) #3 section ".CODE_REGION_1_"

; Function Attrs: nounwind
declare i32 @listen(i32, i32) #3 section ".CODE_REGION_1_"

declare i32 @accept(i32, %struct.sockaddr*, i32*) #2 section ".CODE_REGION_1_"

declare i32 @read(i32, i8*, i32) #2 section ".CODE_REGION_1_"

declare i32 @close(i32) #2 section ".CODE_REGION_1_"

declare i8* @read_measurement(...) #2 section ".CODE_REGION_1_"

; Function Attrs: nounwind
define i32 @main(i32, i8**) #0 section ".CODE_REGION_2_" !dbg !325 {
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca i8**, align 4
  %6 = alloca i8, align 1
  %7 = alloca i32, align 4
  %8 = alloca i32, align 4
  %9 = alloca i32, align 4
  store i32 0, i32* %3, align 4
  store i32 %0, i32* %4, align 4
  call void @llvm.dbg.declare(metadata i32* %4, metadata !329, metadata !72), !dbg !330
  store i8** %1, i8*** %5, align 4
  call void @llvm.dbg.declare(metadata i8*** %5, metadata !331, metadata !72), !dbg !332
  call void @__AMI_fake_shared_wrt(), !dbg !333
  store i8 -1, i8* @mode, align 1, !dbg !333
  call void @llvm.dbg.declare(metadata i8* %6, metadata !334, metadata !72), !dbg !335
  call void @llvm.var.annotation(i8* %6, i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.13, i32 0, i32 0), i8* getelementptr inbounds ([11 x i8], [11 x i8]* @.str.1.14, i32 0, i32 0), i32 29), !dbg !336
  %10 = load i8, i8* @mode, align 1, !dbg !337
  store i8 %10, i8* %6, align 1, !dbg !335
  call void @llvm.dbg.declare(metadata i32* %7, metadata !338, metadata !72), !dbg !339
  store i32 0, i32* %7, align 4, !dbg !339
  call void @llvm.dbg.declare(metadata i32* %8, metadata !340, metadata !72), !dbg !341
  call void @llvm.dbg.declare(metadata i32* %9, metadata !342, metadata !72), !dbg !343
  call void @create_files(i8* getelementptr inbounds ([17 x i8], [17 x i8]* @.str.2.15, i32 0, i32 0), i8* getelementptr inbounds ([18 x i8], [18 x i8]* @.str.3.16, i32 0, i32 0), i8* getelementptr inbounds ([19 x i8], [19 x i8]* @.str.4.17, i32 0, i32 0), i8* getelementptr inbounds ([14 x i8], [14 x i8]* @.str.5.18, i32 0, i32 0), i8* getelementptr inbounds ([19 x i8], [19 x i8]* @.str.6.19, i32 0, i32 0)), !dbg !344
  %11 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([32 x i8], [32 x i8]* @.str.7.20, i32 0, i32 0)), !dbg !345
  %12 = call i32 (i8*, ...) @__isoc99_scanf(i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.8, i32 0, i32 0), i32* @portno), !dbg !346
  call void @pinMode(i32 3, i32 1), !dbg !347
  call void @pinMode(i32 4, i32 1), !dbg !348
  call void @pinMode(i32 0, i32 1), !dbg !349
  call void @pinMode(i32 2, i32 1), !dbg !350
  %13 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([20 x i8], [20 x i8]* @.str.9, i32 0, i32 0)), !dbg !351
  %14 = call i32 @usecs(), !dbg !352
  store i32 %14, i32* %8, align 4, !dbg !353
  %15 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.10, i32 0, i32 0), i8* getelementptr inbounds ([5 x i8], [5 x i8]* @__func__.main, i32 0, i32 0), i32 50), !dbg !354
  br label %16, !dbg !355

; <label>:16:                                     ; preds = %59, %2
  %17 = load i32, i32* %7, align 4, !dbg !356
  %18 = add nsw i32 %17, 1, !dbg !356
  store i32 %18, i32* %7, align 4, !dbg !356
  %19 = icmp slt i32 %17, 1, !dbg !358
  br i1 %19, label %20, label %61, !dbg !359

; <label>:20:                                     ; preds = %16
  %21 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.10, i32 0, i32 0), i8* getelementptr inbounds ([5 x i8], [5 x i8]* @__func__.main, i32 0, i32 0), i32 52), !dbg !360
  call void @__AMI_fake_direct_transfer(), !dbg !362
  %22 = call i8* @tcpListener(i8* null), !dbg !362
  %23 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.10, i32 0, i32 0), i8* getelementptr inbounds ([5 x i8], [5 x i8]* @__func__.main, i32 0, i32 0), i32 54), !dbg !363
  %24 = load i8, i8* %6, align 1, !dbg !364
  %25 = zext i8 %24 to i32, !dbg !364
  %26 = load i8, i8* @mode, align 1, !dbg !366
  %27 = zext i8 %26 to i32, !dbg !366
  %28 = icmp eq i32 %25, %27, !dbg !367
  br i1 %28, label %29, label %31, !dbg !368

; <label>:29:                                     ; preds = %20
  call void @digitalWrite(i32 0, i32 0), !dbg !369
  call void @digitalWrite(i32 2, i32 0), !dbg !371
  call void @digitalWrite(i32 3, i32 0), !dbg !373
  call void @digitalWrite(i32 4, i32 0), !dbg !375
  %30 = load i8, i8* @mode, align 1, !dbg !377
  store i8 %30, i8* %6, align 1, !dbg !378
  br label %59, !dbg !379

; <label>:31:                                     ; preds = %20
  %32 = load i8, i8* @mode, align 1, !dbg !380
  %33 = zext i8 %32 to i32, !dbg !380
  %34 = icmp eq i32 %33, 49, !dbg !382
  br i1 %34, label %35, label %37, !dbg !383

; <label>:35:                                     ; preds = %31
  %36 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([9 x i8], [9 x i8]* @.str.11, i32 0, i32 0)), !dbg !384
  call void @digitalWrite(i32 0, i32 1), !dbg !386
  call void @digitalWrite(i32 3, i32 1), !dbg !387
  br label %58, !dbg !388

; <label>:37:                                     ; preds = %31
  %38 = load i8, i8* @mode, align 1, !dbg !389
  %39 = zext i8 %38 to i32, !dbg !389
  %40 = icmp eq i32 %39, 50, !dbg !391
  br i1 %40, label %41, label %43, !dbg !392

; <label>:41:                                     ; preds = %37
  %42 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.12, i32 0, i32 0)), !dbg !393
  call void @digitalWrite(i32 2, i32 1), !dbg !395
  call void @digitalWrite(i32 4, i32 1), !dbg !396
  br label %57, !dbg !397

; <label>:43:                                     ; preds = %37
  %44 = load i8, i8* @mode, align 1, !dbg !398
  %45 = zext i8 %44 to i32, !dbg !398
  %46 = icmp eq i32 %45, 51, !dbg !400
  br i1 %46, label %47, label %49, !dbg !401

; <label>:47:                                     ; preds = %43
  %48 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([6 x i8], [6 x i8]* @.str.13.21, i32 0, i32 0)), !dbg !402
  call void @digitalWrite(i32 0, i32 1), !dbg !404
  call void @digitalWrite(i32 4, i32 1), !dbg !405
  br label %56, !dbg !406

; <label>:49:                                     ; preds = %43
  %50 = load i8, i8* @mode, align 1, !dbg !407
  %51 = zext i8 %50 to i32, !dbg !407
  %52 = icmp eq i32 %51, 52, !dbg !409
  br i1 %52, label %53, label %55, !dbg !410

; <label>:53:                                     ; preds = %49
  %54 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.14, i32 0, i32 0)), !dbg !411
  call void @digitalWrite(i32 2, i32 1), !dbg !413
  call void @digitalWrite(i32 3, i32 1), !dbg !414
  br label %55, !dbg !415

; <label>:55:                                     ; preds = %53, %49
  br label %56

; <label>:56:                                     ; preds = %55, %47
  br label %57

; <label>:57:                                     ; preds = %56, %41
  br label %58

; <label>:58:                                     ; preds = %57, %35
  br label %59

; <label>:59:                                     ; preds = %58, %29
  %60 = call i32 @usleep(i32 500000), !dbg !416
  br label %16, !dbg !417, !llvm.loop !419

; <label>:61:                                     ; preds = %16
  %62 = call i32 @usecs(), !dbg !420
  store i32 %62, i32* %9, align 4, !dbg !421
  %63 = load i32, i32* %9, align 4, !dbg !422
  %64 = load i32, i32* %8, align 4, !dbg !423
  %65 = sub i32 %63, %64, !dbg !424
  %66 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([40 x i8], [40 x i8]* @.str.15, i32 0, i32 0), i32 %65), !dbg !425
  call void @digitalWrite(i32 0, i32 0), !dbg !426
  call void @digitalWrite(i32 2, i32 0), !dbg !427
  call void @digitalWrite(i32 3, i32 0), !dbg !428
  call void @digitalWrite(i32 4, i32 0), !dbg !429
  ret i32 0, !dbg !431
}

; Function Attrs: nounwind
declare void @llvm.var.annotation(i8*, i8*, i8*, i32) #8

declare void @create_files(i8*, i8*, i8*, i8*, i8*) #2 section ".CODE_REGION_2_"

declare void @__AMI_fake_local_wrt()

declare void @__AMI_fake_shared_wrt()

declare void @__AMI_fake_direct_transfer()

declare void @__AMI_fake_rt_transfer()

attributes #0 = { nounwind "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="arm1176jzf-s" "target-features"="+dsp,+strict-align,+vfp2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind readnone }
attributes #2 = { "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="arm1176jzf-s" "target-features"="+dsp,+strict-align,+vfp2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { nounwind "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="arm1176jzf-s" "target-features"="+dsp,+strict-align,+vfp2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #4 = { nounwind readonly "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="arm1176jzf-s" "target-features"="+dsp,+strict-align,+vfp2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #5 = { noreturn nounwind "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="arm1176jzf-s" "target-features"="+dsp,+strict-align,+vfp2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #6 = { argmemonly nounwind }
attributes #7 = { nounwind readnone "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="arm1176jzf-s" "target-features"="+dsp,+strict-align,+vfp2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #8 = { nounwind }
attributes #9 = { nounwind readonly }
attributes #10 = { noreturn nounwind }

!llvm.dbg.cu = !{!0, !7, !50}
!llvm.ident = !{!63, !63, !63}
!llvm.module.flags = !{!64, !65, !66, !67}

!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "clang version 3.9.0 (tags/RELEASE_390/final)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, enums: !2, retainedTypes: !3)
!1 = !DIFile(filename: "util.c", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/roverpi-cb")
!2 = !{}
!3 = !{!4, !5, !6}
!4 = !DIBasicType(name: "int", size: 32, align: 32, encoding: DW_ATE_signed)
!5 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: null, size: 32, align: 32)
!6 = !DIBasicType(name: "long int", size: 32, align: 32, encoding: DW_ATE_signed)
!7 = distinct !DICompileUnit(language: DW_LANG_C99, file: !8, producer: "clang version 3.9.0 (tags/RELEASE_390/final)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, enums: !9, retainedTypes: !22, globals: !42)
!8 = !DIFile(filename: "tcp.c", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/roverpi-cb")
!9 = !{!10}
!10 = !DICompositeType(tag: DW_TAG_enumeration_type, name: "__socket_type", file: !11, line: 24, size: 32, align: 32, elements: !12)
!11 = !DIFile(filename: "/home/zrz0517/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/libc/usr/include/bits/socket_type.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/roverpi-cb")
!12 = !{!13, !14, !15, !16, !17, !18, !19, !20, !21}
!13 = !DIEnumerator(name: "SOCK_STREAM", value: 1)
!14 = !DIEnumerator(name: "SOCK_DGRAM", value: 2)
!15 = !DIEnumerator(name: "SOCK_RAW", value: 3)
!16 = !DIEnumerator(name: "SOCK_RDM", value: 4)
!17 = !DIEnumerator(name: "SOCK_SEQPACKET", value: 5)
!18 = !DIEnumerator(name: "SOCK_DCCP", value: 6)
!19 = !DIEnumerator(name: "SOCK_PACKET", value: 10)
!20 = !DIEnumerator(name: "SOCK_CLOEXEC", value: 524288)
!21 = !DIEnumerator(name: "SOCK_NONBLOCK", value: 2048)
!22 = !{!23, !25, !30, !5}
!23 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !24, size: 32, align: 32)
!24 = !DIBasicType(name: "char", size: 8, align: 8, encoding: DW_ATE_unsigned_char)
!25 = !DIDerivedType(tag: DW_TAG_typedef, name: "in_addr_t", file: !26, line: 30, baseType: !27)
!26 = !DIFile(filename: "/home/zrz0517/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/libc/usr/include/netinet/in.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/roverpi-cb")
!27 = !DIDerivedType(tag: DW_TAG_typedef, name: "uint32_t", file: !28, line: 51, baseType: !29)
!28 = !DIFile(filename: "/home/zrz0517/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/libc/usr/include/stdint.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/roverpi-cb")
!29 = !DIBasicType(name: "unsigned int", size: 32, align: 32, encoding: DW_ATE_unsigned)
!30 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !31, size: 32, align: 32)
!31 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "sockaddr", file: !32, line: 153, size: 128, align: 16, elements: !33)
!32 = !DIFile(filename: "/home/zrz0517/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/libc/usr/include/bits/socket.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/roverpi-cb")
!33 = !{!34, !38}
!34 = !DIDerivedType(tag: DW_TAG_member, name: "sa_family", scope: !31, file: !32, line: 155, baseType: !35, size: 16, align: 16)
!35 = !DIDerivedType(tag: DW_TAG_typedef, name: "sa_family_t", file: !36, line: 28, baseType: !37)
!36 = !DIFile(filename: "/home/zrz0517/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/libc/usr/include/bits/sockaddr.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/roverpi-cb")
!37 = !DIBasicType(name: "unsigned short", size: 16, align: 16, encoding: DW_ATE_unsigned)
!38 = !DIDerivedType(tag: DW_TAG_member, name: "sa_data", scope: !31, file: !32, line: 156, baseType: !39, size: 112, align: 8, offset: 16)
!39 = !DICompositeType(tag: DW_TAG_array_type, baseType: !24, size: 112, align: 8, elements: !40)
!40 = !{!41}
!41 = !DISubrange(count: 14)
!42 = !{!43, !44, !45, !47, !48, !49}
!43 = distinct !DIGlobalVariable(name: "recording_flag", scope: !7, file: !8, line: 13, type: !4, isLocal: false, isDefinition: true, variable: i32* @recording_flag)
!44 = distinct !DIGlobalVariable(name: "recording_cnt", scope: !7, file: !8, line: 14, type: !4, isLocal: false, isDefinition: true, variable: i32* @recording_cnt)
!45 = distinct !DIGlobalVariable(name: "n", scope: !7, file: !46, line: 7, type: !4, isLocal: false, isDefinition: true, variable: i32* @n)
!46 = !DIFile(filename: "./tcp.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/roverpi-cb")
!47 = distinct !DIGlobalVariable(name: "newsockfd", scope: !7, file: !46, line: 8, type: !4, isLocal: false, isDefinition: true, variable: i32* @newsockfd)
!48 = distinct !DIGlobalVariable(name: "portno", scope: !7, file: !46, line: 9, type: !4, isLocal: false, isDefinition: true, variable: i32* @portno)
!49 = distinct !DIGlobalVariable(name: "mode", scope: !7, file: !46, line: 10, type: !24, isLocal: false, isDefinition: true, variable: i8* @mode)
!50 = distinct !DICompileUnit(language: DW_LANG_C99, file: !51, producer: "clang version 3.9.0 (tags/RELEASE_390/final)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, enums: !52, retainedTypes: !57, globals: !58)
!51 = !DIFile(filename: "rovertcp.c", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/roverpi-cb")
!52 = !{!53}
!53 = !DICompositeType(tag: DW_TAG_enumeration_type, file: !51, line: 18, size: 32, align: 32, elements: !54)
!54 = !{!55, !56}
!55 = !DIEnumerator(name: "INPUT", value: 0)
!56 = !DIEnumerator(name: "OUTPUT", value: 1)
!57 = !{!5}
!58 = !{!59, !60, !61, !62}
!59 = distinct !DIGlobalVariable(name: "n", scope: !50, file: !46, line: 7, type: !4, isLocal: false, isDefinition: true, variable: i32* @n)
!60 = distinct !DIGlobalVariable(name: "newsockfd", scope: !50, file: !46, line: 8, type: !4, isLocal: false, isDefinition: true, variable: i32* @newsockfd)
!61 = distinct !DIGlobalVariable(name: "portno", scope: !50, file: !46, line: 9, type: !4, isLocal: false, isDefinition: true, variable: i32* @portno)
!62 = distinct !DIGlobalVariable(name: "mode", scope: !50, file: !46, line: 10, type: !24, isLocal: false, isDefinition: true, variable: i8* @mode)
!63 = !{!"clang version 3.9.0 (tags/RELEASE_390/final)"}
!64 = !{i32 2, !"Dwarf Version", i32 5}
!65 = !{i32 2, !"Debug Info Version", i32 3}
!66 = !{i32 1, !"wchar_size", i32 4}
!67 = !{i32 1, !"min_enum_size", i32 4}
!68 = distinct !DISubprogram(name: "pinMode", scope: !1, file: !1, line: 8, type: !69, isLocal: false, isDefinition: true, scopeLine: 8, flags: DIFlagPrototyped, isOptimized: false, unit: !0, variables: !2)
!69 = !DISubroutineType(types: !70)
!70 = !{null, !4, !4}
!71 = !DILocalVariable(name: "pin", arg: 1, scope: !68, file: !1, line: 8, type: !4)
!72 = !DIExpression()
!73 = !DILocation(line: 8, column: 18, scope: !68)
!74 = !DILocalVariable(name: "mode", arg: 2, scope: !68, file: !1, line: 8, type: !4)
!75 = !DILocation(line: 8, column: 27, scope: !68)
!76 = !DILocation(line: 9, column: 57, scope: !68)
!77 = !DILocation(line: 9, column: 62, scope: !68)
!78 = !DILocation(line: 9, column: 2, scope: !68)
!79 = !DILocation(line: 10, column: 2, scope: !68)
!80 = distinct !DISubprogram(name: "digitalRead", scope: !1, file: !1, line: 13, type: !81, isLocal: false, isDefinition: true, scopeLine: 13, flags: DIFlagPrototyped, isOptimized: false, unit: !0, variables: !2)
!81 = !DISubroutineType(types: !82)
!82 = !{!4, !4}
!83 = !DILocalVariable(name: "pin", arg: 1, scope: !80, file: !1, line: 13, type: !4)
!84 = !DILocation(line: 13, column: 21, scope: !80)
!85 = !DILocalVariable(name: "val", scope: !80, file: !1, line: 14, type: !4)
!86 = !DILocation(line: 14, column: 6, scope: !80)
!87 = !DILocation(line: 15, column: 42, scope: !80)
!88 = !DILocation(line: 15, column: 2, scope: !80)
!89 = !DILocation(line: 16, column: 2, scope: !80)
!90 = !DILocation(line: 17, column: 9, scope: !80)
!91 = !DILocation(line: 17, column: 2, scope: !80)
!92 = distinct !DISubprogram(name: "digitalWrite", scope: !1, file: !1, line: 20, type: !69, isLocal: false, isDefinition: true, scopeLine: 20, flags: DIFlagPrototyped, isOptimized: false, unit: !0, variables: !2)
!93 = !DILocalVariable(name: "pin", arg: 1, scope: !92, file: !1, line: 20, type: !4)
!94 = !DILocation(line: 20, column: 23, scope: !92)
!95 = !DILocalVariable(name: "value", arg: 2, scope: !92, file: !1, line: 20, type: !4)
!96 = !DILocation(line: 20, column: 32, scope: !92)
!97 = !DILocation(line: 22, column: 2, scope: !92)
!98 = distinct !DISubprogram(name: "Serial_begin", scope: !1, file: !1, line: 25, type: !99, isLocal: false, isDefinition: true, scopeLine: 25, flags: DIFlagPrototyped, isOptimized: false, unit: !0, variables: !2)
!99 = !DISubroutineType(types: !100)
!100 = !{null, !4}
!101 = !DILocalVariable(name: "baud", arg: 1, scope: !98, file: !1, line: 25, type: !4)
!102 = !DILocation(line: 25, column: 23, scope: !98)
!103 = !DILocation(line: 26, column: 43, scope: !98)
!104 = !DILocation(line: 26, column: 2, scope: !98)
!105 = !DILocation(line: 27, column: 2, scope: !98)
!106 = distinct !DISubprogram(name: "Serial_available", scope: !1, file: !1, line: 30, type: !107, isLocal: false, isDefinition: true, scopeLine: 30, isOptimized: false, unit: !0, variables: !2)
!107 = !DISubroutineType(types: !108)
!108 = !{!4}
!109 = !DILocalVariable(name: "c", scope: !106, file: !1, line: 31, type: !24)
!110 = !DILocation(line: 31, column: 7, scope: !106)
!111 = !DILocation(line: 33, column: 6, scope: !106)
!112 = !DILocation(line: 33, column: 4, scope: !106)
!113 = !DILocation(line: 35, column: 34, scope: !106)
!114 = !DILocation(line: 35, column: 2, scope: !106)
!115 = !DILocation(line: 37, column: 6, scope: !116)
!116 = distinct !DILexicalBlock(scope: !106, file: !1, line: 37, column: 6)
!117 = !DILocation(line: 37, column: 8, scope: !116)
!118 = !DILocation(line: 37, column: 6, scope: !106)
!119 = !DILocation(line: 38, column: 3, scope: !116)
!120 = !DILocation(line: 40, column: 3, scope: !116)
!121 = !DILocation(line: 41, column: 1, scope: !106)
!122 = distinct !DISubprogram(name: "Serial_read", scope: !1, file: !1, line: 43, type: !107, isLocal: false, isDefinition: true, scopeLine: 43, isOptimized: false, unit: !0, variables: !2)
!123 = !DILocalVariable(name: "c", scope: !122, file: !1, line: 44, type: !24)
!124 = !DILocation(line: 44, column: 7, scope: !122)
!125 = !DILocation(line: 46, column: 6, scope: !122)
!126 = !DILocation(line: 46, column: 4, scope: !122)
!127 = !DILocation(line: 48, column: 14, scope: !122)
!128 = !DILocation(line: 48, column: 9, scope: !122)
!129 = !DILocation(line: 48, column: 2, scope: !122)
!130 = distinct !DISubprogram(name: "Serial_write", scope: !1, file: !1, line: 51, type: !131, isLocal: false, isDefinition: true, scopeLine: 51, flags: DIFlagPrototyped, isOptimized: false, unit: !0, variables: !2)
!131 = !DISubroutineType(types: !132)
!132 = !{!4, !23, !4}
!133 = !DILocalVariable(name: "output", arg: 1, scope: !130, file: !1, line: 51, type: !23)
!134 = !DILocation(line: 51, column: 24, scope: !130)
!135 = !DILocalVariable(name: "len", arg: 2, scope: !130, file: !1, line: 51, type: !4)
!136 = !DILocation(line: 51, column: 36, scope: !130)
!137 = !DILocation(line: 52, column: 61, scope: !130)
!138 = !DILocation(line: 52, column: 69, scope: !130)
!139 = !DILocation(line: 52, column: 2, scope: !130)
!140 = !DILocation(line: 53, column: 2, scope: !130)
!141 = distinct !DISubprogram(name: "analogRead", scope: !1, file: !1, line: 56, type: !81, isLocal: false, isDefinition: true, scopeLine: 56, flags: DIFlagPrototyped, isOptimized: false, unit: !0, variables: !2)
!142 = !DILocalVariable(name: "pin", arg: 1, scope: !141, file: !1, line: 56, type: !4)
!143 = !DILocation(line: 56, column: 20, scope: !141)
!144 = !DILocalVariable(name: "val", scope: !141, file: !1, line: 57, type: !4)
!145 = !DILocation(line: 57, column: 6, scope: !141)
!146 = !DILocation(line: 58, column: 31, scope: !141)
!147 = !DILocation(line: 58, column: 2, scope: !141)
!148 = !DILocation(line: 59, column: 2, scope: !141)
!149 = !DILocation(line: 60, column: 9, scope: !141)
!150 = !DILocation(line: 60, column: 2, scope: !141)
!151 = distinct !DISubprogram(name: "millis", scope: !1, file: !1, line: 63, type: !152, isLocal: false, isDefinition: true, scopeLine: 63, isOptimized: false, unit: !0, variables: !2)
!152 = !DISubroutineType(types: !153)
!153 = !{!154}
!154 = !DIBasicType(name: "long unsigned int", size: 32, align: 32, encoding: DW_ATE_unsigned)
!155 = !DILocalVariable(name: "start", scope: !151, file: !1, line: 64, type: !156)
!156 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "timeval", file: !157, line: 8, size: 64, align: 32, elements: !158)
!157 = !DIFile(filename: "/usr/include/bits/types/struct_timeval.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/roverpi-cb")
!158 = !{!159, !162}
!159 = !DIDerivedType(tag: DW_TAG_member, name: "tv_sec", scope: !156, file: !157, line: 10, baseType: !160, size: 32, align: 32)
!160 = !DIDerivedType(tag: DW_TAG_typedef, name: "__time_t", file: !161, line: 160, baseType: !6)
!161 = !DIFile(filename: "/usr/include/bits/types.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/roverpi-cb")
!162 = !DIDerivedType(tag: DW_TAG_member, name: "tv_usec", scope: !156, file: !157, line: 11, baseType: !163, size: 32, align: 32, offset: 32)
!163 = !DIDerivedType(tag: DW_TAG_typedef, name: "__suseconds_t", file: !161, line: 162, baseType: !6)
!164 = !DILocation(line: 64, column: 17, scope: !151)
!165 = !DILocation(line: 66, column: 2, scope: !151)
!166 = !DILocation(line: 68, column: 15, scope: !151)
!167 = !DILocation(line: 68, column: 22, scope: !151)
!168 = !DILocation(line: 68, column: 37, scope: !151)
!169 = !DILocation(line: 68, column: 44, scope: !151)
!170 = !DILocation(line: 68, column: 29, scope: !151)
!171 = !DILocation(line: 68, column: 2, scope: !151)
!172 = distinct !DISubprogram(name: "usecs", scope: !1, file: !1, line: 72, type: !152, isLocal: false, isDefinition: true, scopeLine: 72, isOptimized: false, unit: !0, variables: !2)
!173 = !DILocalVariable(name: "start", scope: !172, file: !1, line: 73, type: !156)
!174 = !DILocation(line: 73, column: 17, scope: !172)
!175 = !DILocation(line: 75, column: 2, scope: !172)
!176 = !DILocation(line: 77, column: 15, scope: !172)
!177 = !DILocation(line: 77, column: 22, scope: !172)
!178 = !DILocation(line: 77, column: 29, scope: !172)
!179 = !DILocation(line: 77, column: 44, scope: !172)
!180 = !DILocation(line: 77, column: 36, scope: !172)
!181 = !DILocation(line: 77, column: 2, scope: !172)
!182 = distinct !DISubprogram(name: "delayMicroseconds", scope: !1, file: !1, line: 81, type: !183, isLocal: false, isDefinition: true, scopeLine: 81, flags: DIFlagPrototyped, isOptimized: false, unit: !0, variables: !2)
!183 = !DISubroutineType(types: !184)
!184 = !{null, !185}
!185 = !DIBasicType(name: "float", size: 32, align: 32, encoding: DW_ATE_float)
!186 = !DILocalVariable(name: "usecs", arg: 1, scope: !182, file: !1, line: 81, type: !185)
!187 = !DILocation(line: 81, column: 30, scope: !182)
!188 = !DILocation(line: 82, column: 15, scope: !182)
!189 = !DILocation(line: 82, column: 9, scope: !182)
!190 = !DILocation(line: 82, column: 2, scope: !182)
!191 = !DILocation(line: 83, column: 1, scope: !182)
!192 = distinct !DISubprogram(name: "toUInt", scope: !1, file: !1, line: 85, type: !131, isLocal: false, isDefinition: true, scopeLine: 85, flags: DIFlagPrototyped, isOptimized: false, unit: !0, variables: !2)
!193 = !DILocalVariable(name: "input", arg: 1, scope: !192, file: !1, line: 85, type: !23)
!194 = !DILocation(line: 85, column: 18, scope: !192)
!195 = !DILocalVariable(name: "len", arg: 2, scope: !192, file: !1, line: 85, type: !4)
!196 = !DILocation(line: 85, column: 29, scope: !192)
!197 = !DILocalVariable(name: "val", scope: !192, file: !1, line: 86, type: !4)
!198 = !DILocation(line: 86, column: 6, scope: !192)
!199 = !DILocation(line: 87, column: 13, scope: !192)
!200 = !DILocation(line: 87, column: 8, scope: !192)
!201 = !DILocation(line: 87, column: 6, scope: !192)
!202 = !DILocation(line: 88, column: 9, scope: !192)
!203 = !DILocation(line: 88, column: 2, scope: !192)
!204 = distinct !DISubprogram(name: "tcpError", scope: !8, file: !8, line: 19, type: !205, isLocal: false, isDefinition: true, scopeLine: 19, flags: DIFlagPrototyped, isOptimized: false, unit: !7, variables: !2)
!205 = !DISubroutineType(types: !206)
!206 = !{null, !207}
!207 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !208, size: 32, align: 32)
!208 = !DIDerivedType(tag: DW_TAG_const_type, baseType: !24)
!209 = !DILocalVariable(name: "msg", arg: 1, scope: !204, file: !8, line: 19, type: !207)
!210 = !DILocation(line: 19, column: 27, scope: !204)
!211 = !DILocation(line: 20, column: 12, scope: !204)
!212 = !DILocation(line: 20, column: 5, scope: !204)
!213 = !DILocation(line: 21, column: 5, scope: !204)
!214 = !DILocation(line: 22, column: 1, scope: !204)
!215 = distinct !DISubprogram(name: "tcpListener", scope: !8, file: !8, line: 24, type: !216, isLocal: false, isDefinition: true, scopeLine: 24, flags: DIFlagPrototyped, isOptimized: false, unit: !7, variables: !2)
!216 = !DISubroutineType(types: !217)
!217 = !{!5, !5}
!218 = !DILocalVariable(name: "arg", arg: 1, scope: !215, file: !8, line: 24, type: !5)
!219 = !DILocation(line: 24, column: 25, scope: !215)
!220 = !DILocation(line: 25, column: 16, scope: !215)
!221 = !DILocalVariable(name: "buffer", scope: !215, file: !8, line: 26, type: !222)
!222 = !DICompositeType(tag: DW_TAG_array_type, baseType: !24, size: 40, align: 8, elements: !223)
!223 = !{!224}
!224 = !DISubrange(count: 5)
!225 = !DILocation(line: 26, column: 7, scope: !215)
!226 = !DILocalVariable(name: "sockfd", scope: !215, file: !8, line: 27, type: !4)
!227 = !DILocation(line: 27, column: 6, scope: !215)
!228 = !DILocalVariable(name: "clilen", scope: !215, file: !8, line: 28, type: !229)
!229 = !DIDerivedType(tag: DW_TAG_typedef, name: "socklen_t", file: !230, line: 277, baseType: !231)
!230 = !DIFile(filename: "/home/zrz0517/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/libc/usr/include/unistd.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/roverpi-cb")
!231 = !DIDerivedType(tag: DW_TAG_typedef, name: "__socklen_t", file: !232, line: 189, baseType: !29)
!232 = !DIFile(filename: "/home/zrz0517/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/libc/usr/include/bits/types.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/roverpi-cb")
!233 = !DILocation(line: 28, column: 12, scope: !215)
!234 = !DILocalVariable(name: "count", scope: !215, file: !8, line: 29, type: !4)
!235 = !DILocation(line: 29, column: 9, scope: !215)
!236 = !DILocalVariable(name: "serv_addr", scope: !215, file: !8, line: 30, type: !237)
!237 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "sockaddr_in", file: !26, line: 239, size: 128, align: 32, elements: !238)
!238 = !{!239, !240, !243, !247}
!239 = !DIDerivedType(tag: DW_TAG_member, name: "sin_family", scope: !237, file: !26, line: 241, baseType: !35, size: 16, align: 16)
!240 = !DIDerivedType(tag: DW_TAG_member, name: "sin_port", scope: !237, file: !26, line: 242, baseType: !241, size: 16, align: 16, offset: 16)
!241 = !DIDerivedType(tag: DW_TAG_typedef, name: "in_port_t", file: !26, line: 119, baseType: !242)
!242 = !DIDerivedType(tag: DW_TAG_typedef, name: "uint16_t", file: !28, line: 49, baseType: !37)
!243 = !DIDerivedType(tag: DW_TAG_member, name: "sin_addr", scope: !237, file: !26, line: 243, baseType: !244, size: 32, align: 32, offset: 32)
!244 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "in_addr", file: !26, line: 31, size: 32, align: 32, elements: !245)
!245 = !{!246}
!246 = !DIDerivedType(tag: DW_TAG_member, name: "s_addr", scope: !244, file: !26, line: 33, baseType: !25, size: 32, align: 32)
!247 = !DIDerivedType(tag: DW_TAG_member, name: "sin_zero", scope: !237, file: !26, line: 246, baseType: !248, size: 64, align: 8, offset: 64)
!248 = !DICompositeType(tag: DW_TAG_array_type, baseType: !249, size: 64, align: 8, elements: !250)
!249 = !DIBasicType(name: "unsigned char", size: 8, align: 8, encoding: DW_ATE_unsigned_char)
!250 = !{!251}
!251 = !DISubrange(count: 8)
!252 = !DILocation(line: 30, column: 21, scope: !215)
!253 = !DILocalVariable(name: "cli_addr", scope: !215, file: !8, line: 30, type: !237)
!254 = !DILocation(line: 30, column: 32, scope: !215)
!255 = !DILocation(line: 31, column: 8, scope: !215)
!256 = !DILocation(line: 32, column: 11, scope: !215)
!257 = !DILocation(line: 32, column: 9, scope: !215)
!258 = !DILocation(line: 33, column: 6, scope: !259)
!259 = distinct !DILexicalBlock(scope: !215, file: !8, line: 33, column: 6)
!260 = !DILocation(line: 33, column: 13, scope: !259)
!261 = !DILocation(line: 33, column: 6, scope: !215)
!262 = !DILocation(line: 34, column: 3, scope: !259)
!263 = !DILocation(line: 35, column: 8, scope: !215)
!264 = !DILocation(line: 36, column: 2, scope: !215)
!265 = !DILocation(line: 37, column: 12, scope: !215)
!266 = !DILocation(line: 37, column: 23, scope: !215)
!267 = !DILocation(line: 38, column: 12, scope: !215)
!268 = !DILocation(line: 38, column: 21, scope: !215)
!269 = !DILocation(line: 38, column: 28, scope: !215)
!270 = !DILocation(line: 39, column: 29, scope: !215)
!271 = !DILocation(line: 39, column: 23, scope: !215)
!272 = !DILocation(line: 39, column: 12, scope: !215)
!273 = !DILocation(line: 39, column: 21, scope: !215)
!274 = !DILocation(line: 40, column: 8, scope: !215)
!275 = !DILocation(line: 41, column: 11, scope: !276)
!276 = distinct !DILexicalBlock(scope: !215, file: !8, line: 41, column: 6)
!277 = !DILocation(line: 41, column: 19, scope: !276)
!278 = !DILocation(line: 41, column: 6, scope: !276)
!279 = !DILocation(line: 41, column: 70, scope: !276)
!280 = !DILocation(line: 41, column: 6, scope: !215)
!281 = !DILocation(line: 42, column: 3, scope: !276)
!282 = !DILocation(line: 43, column: 8, scope: !215)
!283 = !DILocation(line: 44, column: 9, scope: !215)
!284 = !DILocation(line: 44, column: 2, scope: !215)
!285 = !DILocation(line: 45, column: 8, scope: !215)
!286 = !DILocation(line: 46, column: 9, scope: !215)
!287 = !DILocation(line: 48, column: 2, scope: !215)
!288 = !DILocation(line: 49, column: 21, scope: !215)
!289 = !DILocation(line: 49, column: 28, scope: !215)
!290 = !DILocation(line: 49, column: 14, scope: !215)
!291 = !DILocation(line: 49, column: 12, scope: !215)
!292 = !DILocation(line: 50, column: 8, scope: !215)
!293 = !DILocation(line: 51, column: 6, scope: !294)
!294 = distinct !DILexicalBlock(scope: !215, file: !8, line: 51, column: 6)
!295 = !DILocation(line: 51, column: 16, scope: !294)
!296 = !DILocation(line: 51, column: 6, scope: !215)
!297 = !DILocation(line: 52, column: 3, scope: !294)
!298 = !DILocation(line: 53, column: 8, scope: !215)
!299 = !DILocation(line: 54, column: 2, scope: !215)
!300 = !DILocation(line: 54, column: 13, scope: !301)
!301 = !DILexicalBlockFile(scope: !215, file: !8, discriminator: 1)
!302 = !DILocation(line: 54, column: 16, scope: !301)
!303 = !DILocation(line: 54, column: 2, scope: !301)
!304 = !DILocation(line: 55, column: 3, scope: !305)
!305 = distinct !DILexicalBlock(scope: !215, file: !8, line: 54, column: 20)
!306 = !DILocation(line: 56, column: 12, scope: !305)
!307 = !DILocation(line: 56, column: 22, scope: !305)
!308 = !DILocation(line: 56, column: 7, scope: !305)
!309 = !DILocation(line: 56, column: 5, scope: !305)
!310 = !DILocation(line: 57, column: 10, scope: !305)
!311 = !DILocation(line: 57, column: 8, scope: !305)
!312 = !DILocation(line: 59, column: 29, scope: !305)
!313 = !DILocation(line: 59, column: 4, scope: !305)
!314 = !DILocation(line: 54, column: 2, scope: !315)
!315 = !DILexicalBlockFile(scope: !215, file: !8, discriminator: 2)
!316 = distinct !{!316, !299}
!317 = !DILocation(line: 61, column: 8, scope: !215)
!318 = !DILocation(line: 61, column: 2, scope: !215)
!319 = !DILocation(line: 62, column: 8, scope: !215)
!320 = !DILocation(line: 62, column: 2, scope: !215)
!321 = !DILocation(line: 63, column: 16, scope: !215)
!322 = !DILocation(line: 64, column: 22, scope: !215)
!323 = !DILocation(line: 65, column: 2, scope: !215)
!324 = !DILocation(line: 66, column: 2, scope: !215)
!325 = distinct !DISubprogram(name: "main", scope: !51, file: !51, line: 26, type: !326, isLocal: false, isDefinition: true, scopeLine: 27, flags: DIFlagPrototyped, isOptimized: false, unit: !50, variables: !2)
!326 = !DISubroutineType(types: !327)
!327 = !{!4, !4, !328}
!328 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !23, size: 32, align: 32)
!329 = !DILocalVariable(name: "argc", arg: 1, scope: !325, file: !51, line: 26, type: !4)
!330 = !DILocation(line: 26, column: 14, scope: !325)
!331 = !DILocalVariable(name: "argv", arg: 2, scope: !325, file: !51, line: 26, type: !328)
!332 = !DILocation(line: 26, column: 27, scope: !325)
!333 = !DILocation(line: 28, column: 7, scope: !325)
!334 = !DILocalVariable(name: "last", scope: !325, file: !51, line: 29, type: !24)
!335 = !DILocation(line: 29, column: 46, scope: !325)
!336 = !DILocation(line: 29, column: 2, scope: !325)
!337 = !DILocation(line: 29, column: 53, scope: !325)
!338 = !DILocalVariable(name: "count", scope: !325, file: !51, line: 30, type: !4)
!339 = !DILocation(line: 30, column: 9, scope: !325)
!340 = !DILocalVariable(name: "start", scope: !325, file: !51, line: 31, type: !154)
!341 = !DILocation(line: 31, column: 19, scope: !325)
!342 = !DILocalVariable(name: "end", scope: !325, file: !51, line: 31, type: !154)
!343 = !DILocation(line: 31, column: 26, scope: !325)
!344 = !DILocation(line: 32, column: 2, scope: !325)
!345 = !DILocation(line: 34, column: 2, scope: !325)
!346 = !DILocation(line: 35, column: 2, scope: !325)
!347 = !DILocation(line: 41, column: 2, scope: !325)
!348 = !DILocation(line: 42, column: 2, scope: !325)
!349 = !DILocation(line: 43, column: 2, scope: !325)
!350 = !DILocation(line: 44, column: 2, scope: !325)
!351 = !DILocation(line: 46, column: 2, scope: !325)
!352 = !DILocation(line: 47, column: 13, scope: !325)
!353 = !DILocation(line: 47, column: 11, scope: !325)
!354 = !DILocation(line: 50, column: 8, scope: !325)
!355 = !DILocation(line: 51, column: 2, scope: !325)
!356 = !DILocation(line: 51, column: 14, scope: !357)
!357 = !DILexicalBlockFile(scope: !325, file: !51, discriminator: 1)
!358 = !DILocation(line: 51, column: 17, scope: !357)
!359 = !DILocation(line: 51, column: 2, scope: !357)
!360 = !DILocation(line: 52, column: 8, scope: !361)
!361 = distinct !DILexicalBlock(scope: !325, file: !51, line: 51, column: 22)
!362 = !DILocation(line: 53, column: 3, scope: !361)
!363 = !DILocation(line: 54, column: 8, scope: !361)
!364 = !DILocation(line: 55, column: 6, scope: !365)
!365 = distinct !DILexicalBlock(scope: !361, file: !51, line: 55, column: 6)
!366 = !DILocation(line: 55, column: 14, scope: !365)
!367 = !DILocation(line: 55, column: 11, scope: !365)
!368 = !DILocation(line: 55, column: 6, scope: !361)
!369 = !DILocation(line: 56, column: 4, scope: !370)
!370 = distinct !DILexicalBlock(scope: !365, file: !51, line: 55, column: 19)
!371 = !DILocation(line: 56, column: 4, scope: !372)
!372 = !DILexicalBlockFile(scope: !370, file: !51, discriminator: 1)
!373 = !DILocation(line: 56, column: 4, scope: !374)
!374 = !DILexicalBlockFile(scope: !370, file: !51, discriminator: 2)
!375 = !DILocation(line: 56, column: 4, scope: !376)
!376 = !DILexicalBlockFile(scope: !370, file: !51, discriminator: 3)
!377 = !DILocation(line: 57, column: 11, scope: !370)
!378 = !DILocation(line: 57, column: 9, scope: !370)
!379 = !DILocation(line: 58, column: 3, scope: !370)
!380 = !DILocation(line: 61, column: 6, scope: !381)
!381 = distinct !DILexicalBlock(scope: !365, file: !51, line: 61, column: 6)
!382 = !DILocation(line: 61, column: 11, scope: !381)
!383 = !DILocation(line: 61, column: 6, scope: !365)
!384 = !DILocation(line: 62, column: 4, scope: !385)
!385 = distinct !DILexicalBlock(scope: !381, file: !51, line: 61, column: 22)
!386 = !DILocation(line: 63, column: 4, scope: !385)
!387 = !DILocation(line: 64, column: 4, scope: !385)
!388 = !DILocation(line: 65, column: 3, scope: !385)
!389 = !DILocation(line: 67, column: 11, scope: !390)
!390 = distinct !DILexicalBlock(scope: !381, file: !51, line: 67, column: 11)
!391 = !DILocation(line: 67, column: 16, scope: !390)
!392 = !DILocation(line: 67, column: 11, scope: !381)
!393 = !DILocation(line: 68, column: 4, scope: !394)
!394 = distinct !DILexicalBlock(scope: !390, file: !51, line: 67, column: 29)
!395 = !DILocation(line: 69, column: 4, scope: !394)
!396 = !DILocation(line: 70, column: 4, scope: !394)
!397 = !DILocation(line: 71, column: 3, scope: !394)
!398 = !DILocation(line: 73, column: 12, scope: !399)
!399 = distinct !DILexicalBlock(scope: !390, file: !51, line: 73, column: 12)
!400 = !DILocation(line: 73, column: 17, scope: !399)
!401 = !DILocation(line: 73, column: 12, scope: !390)
!402 = !DILocation(line: 74, column: 4, scope: !403)
!403 = distinct !DILexicalBlock(scope: !399, file: !51, line: 73, column: 30)
!404 = !DILocation(line: 75, column: 4, scope: !403)
!405 = !DILocation(line: 76, column: 4, scope: !403)
!406 = !DILocation(line: 77, column: 3, scope: !403)
!407 = !DILocation(line: 79, column: 12, scope: !408)
!408 = distinct !DILexicalBlock(scope: !399, file: !51, line: 79, column: 12)
!409 = !DILocation(line: 79, column: 17, scope: !408)
!410 = !DILocation(line: 79, column: 12, scope: !399)
!411 = !DILocation(line: 80, column: 4, scope: !412)
!412 = distinct !DILexicalBlock(scope: !408, file: !51, line: 79, column: 30)
!413 = !DILocation(line: 81, column: 4, scope: !412)
!414 = !DILocation(line: 82, column: 4, scope: !412)
!415 = !DILocation(line: 83, column: 3, scope: !412)
!416 = !DILocation(line: 85, column: 3, scope: !361)
!417 = !DILocation(line: 51, column: 2, scope: !418)
!418 = !DILexicalBlockFile(scope: !325, file: !51, discriminator: 2)
!419 = distinct !{!419, !355}
!420 = !DILocation(line: 88, column: 11, scope: !325)
!421 = !DILocation(line: 88, column: 9, scope: !325)
!422 = !DILocation(line: 89, column: 56, scope: !325)
!423 = !DILocation(line: 89, column: 62, scope: !325)
!424 = !DILocation(line: 89, column: 60, scope: !325)
!425 = !DILocation(line: 89, column: 5, scope: !325)
!426 = !DILocation(line: 91, column: 2, scope: !325)
!427 = !DILocation(line: 91, column: 2, scope: !357)
!428 = !DILocation(line: 91, column: 2, scope: !418)
!429 = !DILocation(line: 91, column: 2, scope: !430)
!430 = !DILexicalBlockFile(scope: !325, file: !51, discriminator: 3)
!431 = !DILocation(line: 92, column: 2, scope: !325)
