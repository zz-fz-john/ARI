; ModuleID = 'after_compartment_test_combo.bc'
source_filename = "llvm-link"
target datalayout = "e-m:e-p:32:32-i64:64-v128:64:128-a:0:32-n32-S64"
target triple = "armv6kz--linux-gnueabihf"

%struct.RoutedDevice = type { i32, i32, i8* }
%struct.SwitchPattern = type { i32, i32, i8** }
%struct.SwitchMemoryItem = type { i64, i32, i8* }
%struct.timespec = type { i32, i32 }

@recording_flag = global i32 0, section ".DATA_REGION_2__bss", align 4
@recording_cnt = global i32 0, align 4
@DEVICE_ROUTINGS = constant [20 x %struct.RoutedDevice] [%struct.RoutedDevice { i32 0, i32 0, i8* getelementptr inbounds ([64 x i8], [64 x i8]* @SWITCH_MAKUUHUONE_KIRKAS, i32 0, i32 0) }, %struct.RoutedDevice { i32 0, i32 0, i8* getelementptr inbounds ([64 x i8], [64 x i8]* @SWITCH_OLOHUONE_KIRKAS, i32 0, i32 0) }, %struct.RoutedDevice { i32 0, i32 0, i8* getelementptr inbounds ([64 x i8], [64 x i8]* @SWITCH_MAKUUHUONE_HIMMEA, i32 0, i32 0) }, %struct.RoutedDevice { i32 0, i32 0, i8* getelementptr inbounds ([64 x i8], [64 x i8]* @SWITCH_OLOHUONE_HIMMEA, i32 0, i32 0) }, %struct.RoutedDevice { i32 6, i32 2, i8* getelementptr inbounds ([82 x i8], [82 x i8]* @SWITCH_KAIKKI_KIRKAS, i32 0, i32 0) }, %struct.RoutedDevice { i32 5, i32 2, i8* getelementptr inbounds ([82 x i8], [82 x i8]* @SWITCH_KAIKKI_HIMMEA, i32 0, i32 0) }, %struct.RoutedDevice { i32 2, i32 3, i8* getelementptr inbounds ([82 x i8], [82 x i8]* @.str, i32 0, i32 0) }, %struct.RoutedDevice { i32 4, i32 3, i8* getelementptr inbounds ([82 x i8], [82 x i8]* @.str.1, i32 0, i32 0) }, %struct.RoutedDevice { i32 2, i32 3, i8* getelementptr inbounds ([82 x i8], [82 x i8]* @.str.2, i32 0, i32 0) }, %struct.RoutedDevice { i32 4, i32 3, i8* getelementptr inbounds ([82 x i8], [82 x i8]* @.str.3, i32 0, i32 0) }, %struct.RoutedDevice { i32 2, i32 3, i8* getelementptr inbounds ([82 x i8], [82 x i8]* @.str.4, i32 0, i32 0) }, %struct.RoutedDevice { i32 4, i32 3, i8* getelementptr inbounds ([82 x i8], [82 x i8]* @.str.5, i32 0, i32 0) }, %struct.RoutedDevice { i32 1, i32 3, i8* getelementptr inbounds ([82 x i8], [82 x i8]* @.str.6, i32 0, i32 0) }, %struct.RoutedDevice { i32 3, i32 3, i8* getelementptr inbounds ([82 x i8], [82 x i8]* @.str.7, i32 0, i32 0) }, %struct.RoutedDevice { i32 7, i32 2, i8* getelementptr inbounds ([82 x i8], [82 x i8]* @SWITCH_KAIKKI_KIRKAS, i32 0, i32 0) }, %struct.RoutedDevice { i32 7, i32 2, i8* getelementptr inbounds ([82 x i8], [82 x i8]* @SWITCH_KAIKKI_HIMMEA, i32 0, i32 0) }, %struct.RoutedDevice { i32 7, i32 3, i8* getelementptr inbounds ([64 x i8], [64 x i8]* @SWITCH_KAJARIT_DUMMY_1, i32 0, i32 0) }, %struct.RoutedDevice { i32 7, i32 3, i8* getelementptr inbounds ([64 x i8], [64 x i8]* @SWITCH_KAJARIT_DUMMY_2, i32 0, i32 0) }, %struct.RoutedDevice { i32 7, i32 3, i8* getelementptr inbounds ([64 x i8], [64 x i8]* @SWITCH_KAJARIT_DUMMY_3, i32 0, i32 0) }, %struct.RoutedDevice { i32 7, i32 3, i8* getelementptr inbounds ([64 x i8], [64 x i8]* @SWITCH_KAJARIT_DUMMY_4, i32 0, i32 0) }], section ".DATA_REGION_1__data", align 4
@SWITCH_MAKUUHUONE_KIRKAS = internal constant [64 x i8] c"class:command;protocol:arctech;model:codeswitch;house:D;unit:1;\00", section ".DATA_REGION_1__data", align 1
@SWITCH_OLOHUONE_KIRKAS = internal constant [64 x i8] c"class:command;protocol:arctech;model:codeswitch;house:D;unit:2;\00", section ".DATA_REGION_1__data", align 1
@SWITCH_MAKUUHUONE_HIMMEA = internal constant [64 x i8] c"class:command;protocol:arctech;model:codeswitch;house:D;unit:3;\00", section ".DATA_REGION_1__data", align 1
@SWITCH_OLOHUONE_HIMMEA = internal constant [64 x i8] c"class:command;protocol:arctech;model:codeswitch;house:D;unit:4;\00", section ".DATA_REGION_1__data", align 1
@SWITCH_KAIKKI_KIRKAS = internal constant [82 x i8] c"class:command;protocol:arctech;model:selflearning;house:11799578;unit:12;group:0;\00", section ".DATA_REGION_1__data", align 1
@SWITCH_KAIKKI_HIMMEA = internal constant [82 x i8] c"class:command;protocol:arctech;model:selflearning;house:11799578;unit:11;group:0;\00", section ".DATA_REGION_1__data", align 1
@.str = private unnamed_addr constant [82 x i8] c"class:command;protocol:arctech;model:selflearning;house:19437866;unit:12;group:0;\00", align 1
@.str.1 = private unnamed_addr constant [82 x i8] c"class:command;protocol:arctech;model:selflearning;house:19437866;unit:11;group:0;\00", align 1
@.str.2 = private unnamed_addr constant [82 x i8] c"class:command;protocol:arctech;model:selflearning;house:19413362;unit:12;group:0;\00", align 1
@.str.3 = private unnamed_addr constant [82 x i8] c"class:command;protocol:arctech;model:selflearning;house:19413362;unit:11;group:0;\00", align 1
@.str.4 = private unnamed_addr constant [82 x i8] c"class:command;protocol:arctech;model:selflearning;house:21953510;unit:12;group:0;\00", align 1
@.str.5 = private unnamed_addr constant [82 x i8] c"class:command;protocol:arctech;model:selflearning;house:21953510;unit:11;group:0;\00", align 1
@.str.6 = private unnamed_addr constant [82 x i8] c"class:command;protocol:arctech;model:selflearning;house:20256766;unit:12;group:0;\00", align 1
@.str.7 = private unnamed_addr constant [82 x i8] c"class:command;protocol:arctech;model:selflearning;house:20256766;unit:11;group:0;\00", align 1
@SWITCH_KAJARIT_DUMMY_1 = internal constant [64 x i8] c"class:command;protocol:arctech;model:codeswitch;house:D;unit:5;\00", section ".DATA_REGION_1__data", align 1
@SWITCH_KAJARIT_DUMMY_2 = internal constant [64 x i8] c"class:command;protocol:arctech;model:codeswitch;house:D;unit:6;\00", section ".DATA_REGION_1__data", align 1
@SWITCH_KAJARIT_DUMMY_3 = internal constant [64 x i8] c"class:command;protocol:arctech;model:codeswitch;house:D;unit:7;\00", section ".DATA_REGION_1__data", align 1
@SWITCH_KAJARIT_DUMMY_4 = internal constant [64 x i8] c"class:command;protocol:arctech;model:codeswitch;house:D;unit:8;\00", section ".DATA_REGION_1__data", align 1
@DEVICE_COUNT = constant i32 20, align 4
@PATTERN_KIRKAS_HIMMEA = global [5 x i8*] [i8* getelementptr inbounds ([64 x i8], [64 x i8]* @SWITCH_MAKUUHUONE_KIRKAS, i32 0, i32 0), i8* getelementptr inbounds ([64 x i8], [64 x i8]* @SWITCH_OLOHUONE_KIRKAS, i32 0, i32 0), i8* getelementptr inbounds ([64 x i8], [64 x i8]* @SWITCH_MAKUUHUONE_HIMMEA, i32 0, i32 0), i8* getelementptr inbounds ([64 x i8], [64 x i8]* @SWITCH_OLOHUONE_HIMMEA, i32 0, i32 0), i8* null], section ".DATA_REGION_1__data", align 4
@PATTERN_HIMMEA_KIRKAS = global [5 x i8*] [i8* getelementptr inbounds ([64 x i8], [64 x i8]* @SWITCH_OLOHUONE_HIMMEA, i32 0, i32 0), i8* getelementptr inbounds ([64 x i8], [64 x i8]* @SWITCH_MAKUUHUONE_HIMMEA, i32 0, i32 0), i8* getelementptr inbounds ([64 x i8], [64 x i8]* @SWITCH_OLOHUONE_KIRKAS, i32 0, i32 0), i8* getelementptr inbounds ([64 x i8], [64 x i8]* @SWITCH_MAKUUHUONE_KIRKAS, i32 0, i32 0), i8* null], section ".DATA_REGION_1__data", align 4
@SWITCH_PATTERNS = constant [6 x %struct.SwitchPattern] [%struct.SwitchPattern { i32 7, i32 2, i8** getelementptr inbounds ([5 x i8*], [5 x i8*]* @PATTERN_KIRKAS_HIMMEA, i32 0, i32 0) }, %struct.SwitchPattern { i32 7, i32 2, i8** getelementptr inbounds ([5 x i8*], [5 x i8*]* @PATTERN_HIMMEA_KIRKAS, i32 0, i32 0) }, %struct.SwitchPattern { i32 5, i32 2, i8** getelementptr inbounds ([5 x i8*], [5 x i8*]* @PATTERN_KIRKAS_HIMMEA, i32 0, i32 0) }, %struct.SwitchPattern { i32 5, i32 2, i8** getelementptr inbounds ([5 x i8*], [5 x i8*]* @PATTERN_HIMMEA_KIRKAS, i32 0, i32 0) }, %struct.SwitchPattern { i32 6, i32 2, i8** getelementptr inbounds ([5 x i8*], [5 x i8*]* @PATTERN_KIRKAS_HIMMEA, i32 0, i32 0) }, %struct.SwitchPattern { i32 6, i32 2, i8** getelementptr inbounds ([5 x i8*], [5 x i8*]* @PATTERN_HIMMEA_KIRKAS, i32 0, i32 0) }], section ".DATA_REGION_1__data", align 4
@PATTERN_COUNT = constant i32 6, align 4
@SWITCH_MEMORY_ITEMS = constant i32 4, align 4
@PATTERN_TIMEOUT_MS = constant i64 4000, align 8
@METHOD_TURNON = constant [15 x i8] c"method:turnon;\00", section ".DATA_REGION_1__data", align 1
@METHOD_TURNOFF = constant [16 x i8] c"method:turnoff;\00", section ".DATA_REGION_1__data", align 1
@g_switch_memory = internal global [4 x %struct.SwitchMemoryItem] zeroinitializer, section ".DATA_REGION_1__bss", align 8
@.str.8 = private unnamed_addr constant [10 x i8] c"sensitive\00", section "llvm.metadata"
@.str.9 = private unnamed_addr constant [19 x i8] c"light-controller.c\00", section "llvm.metadata"
@.str.10 = private unnamed_addr constant [6 x i8] c" %s \0A\00", align 1
@__func__.listen_to_events = private unnamed_addr constant [17 x i8] c"listen_to_events\00", section ".DATA_REGION_1__data", align 1
@.str.11 = private unnamed_addr constant [14 x i8] c" device none\0A\00", align 1
@.str.12 = private unnamed_addr constant [12 x i8] c"Turn on %d\0A\00", align 1
@.str.13 = private unnamed_addr constant [13 x i8] c"tdTurnOn %d\0A\00", align 1
@.str.14 = private unnamed_addr constant [9 x i8] c"IGNORED\0A\00", align 1
@.str.15 = private unnamed_addr constant [13 x i8] c"Turn off %d\0A\00", align 1
@.str.16 = private unnamed_addr constant [14 x i8] c"tdTurnOff %d\0A\00", align 1
@.str.17 = private unnamed_addr constant [19 x i8] c"Unknown method %s\0A\00", align 1
@.str.18 = private unnamed_addr constant [13 x i8] c"II %d %d %s\0A\00", align 1
@__func__.react_to_pattern = private unnamed_addr constant [17 x i8] c"react_to_pattern\00", section ".DATA_REGION_1__data", align 1
@.str.25 = private unnamed_addr constant [24 x i8] c"PATTERN %zu Turn on %d\0A\00", align 1
@.str.26 = private unnamed_addr constant [25 x i8] c"PATTERN %zu Turn off %d\0A\00", align 1
@.str.19 = private unnamed_addr constant [17 x i8] c"./ARI_branch.txt\00", align 1
@.str.20 = private unnamed_addr constant [18 x i8] c"./ARI_ind_jmp.txt\00", align 1
@.str.21 = private unnamed_addr constant [19 x i8] c"./ARI_ret_hash.txt\00", align 1
@.str.22 = private unnamed_addr constant [14 x i8] c"./ARI_tsf.txt\00", align 1
@.str.23 = private unnamed_addr constant [19 x i8] c"./ARI_tsf_cond.txt\00", align 1
@main.data = private unnamed_addr constant [96 x i8] c"class:command;protocol:arctech;model:selflearning;house:11799578;unit:12;group:0;method:turnon;\00", section ".DATA_REGION_2__data", align 1
@ret_recording_finish = external global i32, align 4
@.str.24 = private unnamed_addr constant [40 x i8] c"round with attestation time usecs: %lu\0A\00", align 1
@.str.27 = private unnamed_addr constant [34 x i8] c"%s (int pin = %d, int mode = %d)\0A\00", align 1
@__func__.pinMode = private unnamed_addr constant [8 x i8] c"pinMode\00", section ".DATA_REGION_2__data", align 1
@.str.1.28 = private unnamed_addr constant [19 x i8] c"%s (int pin = %d)\0A\00", align 1
@__func__.digitalRead = private unnamed_addr constant [12 x i8] c"digitalRead\00", section ".DATA_REGION_2__data", align 1
@.str.2.29 = private unnamed_addr constant [3 x i8] c"%d\00", align 1
@.str.3.30 = private unnamed_addr constant [20 x i8] c"%s (int baud = %d)\0A\00", align 1
@__func__.Serial_begin = private unnamed_addr constant [13 x i8] c"Serial_begin\00", section ".DATA_REGION_2__data", align 1
@.str.4.31 = private unnamed_addr constant [11 x i8] c"%s() c:%c\0A\00", align 1
@__func__.Serial_available = private unnamed_addr constant [17 x i8] c"Serial_available\00", section ".DATA_REGION_2__data", align 1
@.str.5.32 = private unnamed_addr constant [38 x i8] c"%s (char *output = %s, int len = %d)\0A\00", align 1
@__func__.Serial_write = private unnamed_addr constant [13 x i8] c"Serial_write\00", section ".DATA_REGION_2__data", align 1
@.str.6.33 = private unnamed_addr constant [18 x i8] c"read from pin %d\0A\00", align 1

; Function Attrs: nounwind
define void @listen_to_events(i8*, i32, i32, i8*) #0 section ".CODE_REGION_1_" !dbg !113 {
  %5 = alloca i8*, align 4
  %6 = alloca i32, align 4
  %7 = alloca i32, align 4
  %8 = alloca i8*, align 4
  %9 = alloca %struct.timespec, align 4
  %10 = alloca i64, align 8
  %11 = alloca i8, align 1
  %12 = alloca i32, align 4
  %13 = alloca %struct.RoutedDevice*, align 4
  %14 = alloca i32, align 4
  %15 = alloca i8*, align 4
  %16 = alloca i32, align 4
  %17 = alloca i32, align 4
  %18 = alloca %struct.SwitchMemoryItem, align 8
  %19 = alloca i8*, align 4
  store i8* %0, i8** %5, align 4
  call void @llvm.dbg.declare(metadata i8** %5, metadata !116, metadata !117), !dbg !118
  store i32 %1, i32* %6, align 4
  call void @llvm.dbg.declare(metadata i32* %6, metadata !119, metadata !117), !dbg !120
  store i32 %2, i32* %7, align 4
  call void @llvm.dbg.declare(metadata i32* %7, metadata !121, metadata !117), !dbg !122
  store i8* %3, i8** %8, align 4
  call void @llvm.dbg.declare(metadata i8** %8, metadata !123, metadata !117), !dbg !124
  call void @llvm.dbg.declare(metadata %struct.timespec* %9, metadata !125, metadata !117), !dbg !134
  %20 = call i32 @clock_gettime(i32 1, %struct.timespec* %9) #3, !dbg !135
  call void @llvm.dbg.declare(metadata i64* %10, metadata !136, metadata !117), !dbg !137
  %21 = getelementptr inbounds %struct.timespec, %struct.timespec* %9, i32 0, i32 0, !dbg !138
  %22 = load i32, i32* %21, align 4, !dbg !138
  %23 = mul nsw i32 %22, 1000, !dbg !139
  %24 = getelementptr inbounds %struct.timespec, %struct.timespec* %9, i32 0, i32 1, !dbg !140
  %25 = load i32, i32* %24, align 4, !dbg !140
  %26 = sdiv i32 %25, 1000000, !dbg !141
  %27 = add nsw i32 %23, %26, !dbg !142
  %28 = sext i32 %27 to i64, !dbg !143
  store i64 %28, i64* %10, align 8, !dbg !137
  call void @llvm.dbg.declare(metadata i8* %11, metadata !144, metadata !117), !dbg !146
  call void @llvm.var.annotation(i8* %11, i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.8, i32 0, i32 0), i8* getelementptr inbounds ([19 x i8], [19 x i8]* @.str.9, i32 0, i32 0), i32 210), !dbg !147
  store i8 0, i8* %11, align 1, !dbg !146
  %29 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([6 x i8], [6 x i8]* @.str.10, i32 0, i32 0), i8* getelementptr inbounds ([17 x i8], [17 x i8]* @__func__.listen_to_events, i32 0, i32 0)), !dbg !148
  call void @llvm.dbg.declare(metadata i32* %12, metadata !149, metadata !117), !dbg !151
  store i32 0, i32* %12, align 4, !dbg !151
  br label %30, !dbg !152

; <label>:30:                                     ; preds = %151, %4
  %31 = load i32, i32* %12, align 4, !dbg !153
  %32 = icmp ult i32 %31, 20, !dbg !156
  br i1 %32, label %33, label %154, !dbg !157

; <label>:33:                                     ; preds = %30
  call void @llvm.dbg.declare(metadata %struct.RoutedDevice** %13, metadata !158, metadata !117), !dbg !161
  %34 = bitcast %struct.RoutedDevice** %13 to i8*, !dbg !162
  call void @llvm.var.annotation(i8* %34, i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.8, i32 0, i32 0), i8* getelementptr inbounds ([19 x i8], [19 x i8]* @.str.9, i32 0, i32 0), i32 215), !dbg !162
  %35 = load i32, i32* %12, align 4, !dbg !163
  %36 = getelementptr inbounds [20 x %struct.RoutedDevice], [20 x %struct.RoutedDevice]* @DEVICE_ROUTINGS, i32 0, i32 %35, !dbg !164
  store %struct.RoutedDevice* %36, %struct.RoutedDevice** %13, align 4, !dbg !161
  call void @llvm.dbg.declare(metadata i32* %14, metadata !165, metadata !117), !dbg !166
  %37 = load %struct.RoutedDevice*, %struct.RoutedDevice** %13, align 4, !dbg !167
  %38 = getelementptr inbounds %struct.RoutedDevice, %struct.RoutedDevice* %37, i32 0, i32 2, !dbg !168
  %39 = load i8*, i8** %38, align 4, !dbg !168
  %40 = call i32 @strlen(i8* %39) #7, !dbg !169
  store i32 %40, i32* %14, align 4, !dbg !166
  %41 = load i8*, i8** %5, align 4, !dbg !170
  %42 = load %struct.RoutedDevice*, %struct.RoutedDevice** %13, align 4, !dbg !172
  %43 = getelementptr inbounds %struct.RoutedDevice, %struct.RoutedDevice* %42, i32 0, i32 2, !dbg !173
  %44 = load i8*, i8** %43, align 4, !dbg !173
  %45 = load i32, i32* %14, align 4, !dbg !174
  %46 = call i32 @strncmp(i8* %41, i8* %44, i32 %45) #7, !dbg !175
  %47 = icmp eq i32 %46, 0, !dbg !176
  br i1 %47, label %48, label %82, !dbg !177

; <label>:48:                                     ; preds = %33
  call void @llvm.dbg.declare(metadata i8** %15, metadata !178, metadata !117), !dbg !180
  %49 = load i8*, i8** %5, align 4, !dbg !181
  %50 = load i32, i32* %14, align 4, !dbg !182
  %51 = getelementptr inbounds i8, i8* %49, i32 %50, !dbg !183
  store i8* %51, i8** %15, align 4, !dbg !180
  call void @llvm.dbg.declare(metadata i32* %16, metadata !184, metadata !117), !dbg !186
  store i32 1, i32* %16, align 4, !dbg !186
  br label %52, !dbg !187

; <label>:52:                                     ; preds = %63, %48
  %53 = load i32, i32* %16, align 4, !dbg !188
  %54 = icmp ult i32 %53, 4, !dbg !191
  br i1 %54, label %55, label %66, !dbg !192

; <label>:55:                                     ; preds = %52
  %56 = load i32, i32* %16, align 4, !dbg !193
  %57 = sub i32 %56, 1, !dbg !195
  %58 = getelementptr inbounds [4 x %struct.SwitchMemoryItem], [4 x %struct.SwitchMemoryItem]* @g_switch_memory, i32 0, i32 %57, !dbg !196
  %59 = load i32, i32* %16, align 4, !dbg !197
  %60 = getelementptr inbounds [4 x %struct.SwitchMemoryItem], [4 x %struct.SwitchMemoryItem]* @g_switch_memory, i32 0, i32 %59, !dbg !198
  %61 = bitcast %struct.SwitchMemoryItem* %58 to i8*, !dbg !198
  %62 = bitcast %struct.SwitchMemoryItem* %60 to i8*, !dbg !198
  call void @llvm.memcpy.p0i8.p0i8.i32(i8* %61, i8* %62, i32 16, i32 8, i1 false), !dbg !198
  br label %63, !dbg !199

; <label>:63:                                     ; preds = %55
  %64 = load i32, i32* %16, align 4, !dbg !200
  %65 = add i32 %64, 1, !dbg !200
  store i32 %65, i32* %16, align 4, !dbg !200
  br label %52, !dbg !202, !llvm.loop !203

; <label>:66:                                     ; preds = %52
  call void @llvm.dbg.declare(metadata i32* %17, metadata !205, metadata !117), !dbg !206
  %67 = bitcast i32* %17 to i8*, !dbg !207
  call void @llvm.var.annotation(i8* %67, i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.8, i32 0, i32 0), i8* getelementptr inbounds ([19 x i8], [19 x i8]* @.str.9, i32 0, i32 0), i32 222), !dbg !207
  store i32 1, i32* %17, align 4, !dbg !206
  %68 = load i8*, i8** %15, align 4, !dbg !208
  %69 = call i32 @strcmp(i8* %68, i8* getelementptr inbounds ([16 x i8], [16 x i8]* @METHOD_TURNOFF, i32 0, i32 0)) #7, !dbg !210
  %70 = icmp eq i32 %69, 0, !dbg !211
  br i1 %70, label %71, label %72, !dbg !212

; <label>:71:                                     ; preds = %66
  store i32 2, i32* %17, align 4, !dbg !213
  br label %72, !dbg !215

; <label>:72:                                     ; preds = %71, %66
  call void @llvm.dbg.declare(metadata %struct.SwitchMemoryItem* %18, metadata !216, metadata !117), !dbg !217
  %73 = getelementptr inbounds %struct.SwitchMemoryItem, %struct.SwitchMemoryItem* %18, i32 0, i32 0, !dbg !218
  %74 = load i64, i64* %10, align 8, !dbg !219
  store i64 %74, i64* %73, align 8, !dbg !218
  %75 = getelementptr inbounds %struct.SwitchMemoryItem, %struct.SwitchMemoryItem* %18, i32 0, i32 1, !dbg !218
  %76 = load i32, i32* %17, align 4, !dbg !220
  store i32 %76, i32* %75, align 8, !dbg !218
  %77 = getelementptr inbounds %struct.SwitchMemoryItem, %struct.SwitchMemoryItem* %18, i32 0, i32 2, !dbg !218
  %78 = load %struct.RoutedDevice*, %struct.RoutedDevice** %13, align 4, !dbg !221
  %79 = getelementptr inbounds %struct.RoutedDevice, %struct.RoutedDevice* %78, i32 0, i32 2, !dbg !222
  %80 = load i8*, i8** %79, align 4, !dbg !222
  store i8* %80, i8** %77, align 4, !dbg !218
  %81 = bitcast %struct.SwitchMemoryItem* %18 to i8*, !dbg !223
  call void @llvm.memcpy.p0i8.p0i8.i32(i8* bitcast (%struct.SwitchMemoryItem* getelementptr inbounds ([4 x %struct.SwitchMemoryItem], [4 x %struct.SwitchMemoryItem]* @g_switch_memory, i32 0, i32 3) to i8*), i8* %81, i32 16, i32 8, i1 false), !dbg !223
  store i8 1, i8* %11, align 1, !dbg !224
  br label %82, !dbg !225

; <label>:82:                                     ; preds = %72, %33
  %83 = load %struct.RoutedDevice*, %struct.RoutedDevice** %13, align 4, !dbg !226
  %84 = getelementptr inbounds %struct.RoutedDevice, %struct.RoutedDevice* %83, i32 0, i32 0, !dbg !228
  %85 = load i32, i32* %84, align 4, !dbg !228
  %86 = icmp eq i32 %85, 0, !dbg !229
  br i1 %86, label %87, label %89, !dbg !230

; <label>:87:                                     ; preds = %82
  %88 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([14 x i8], [14 x i8]* @.str.11, i32 0, i32 0)), !dbg !231
  br label %151, !dbg !233

; <label>:89:                                     ; preds = %82
  %90 = load i8*, i8** %5, align 4, !dbg !234
  %91 = load %struct.RoutedDevice*, %struct.RoutedDevice** %13, align 4, !dbg !236
  %92 = getelementptr inbounds %struct.RoutedDevice, %struct.RoutedDevice* %91, i32 0, i32 2, !dbg !237
  %93 = load i8*, i8** %92, align 4, !dbg !237
  %94 = load i32, i32* %14, align 4, !dbg !238
  %95 = call i32 @strncmp(i8* %90, i8* %93, i32 %94) #7, !dbg !239
  %96 = icmp eq i32 %95, 0, !dbg !240
  br i1 %96, label %97, label %150, !dbg !241

; <label>:97:                                     ; preds = %89
  call void @llvm.dbg.declare(metadata i8** %19, metadata !242, metadata !117), !dbg !244
  %98 = bitcast i8** %19 to i8*, !dbg !245
  call void @llvm.var.annotation(i8* %98, i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.8, i32 0, i32 0), i8* getelementptr inbounds ([19 x i8], [19 x i8]* @.str.9, i32 0, i32 0), i32 235), !dbg !245
  %99 = load i8*, i8** %5, align 4, !dbg !246
  %100 = load i32, i32* %14, align 4, !dbg !247
  %101 = getelementptr inbounds i8, i8* %99, i32 %100, !dbg !248
  store i8* %101, i8** %19, align 4, !dbg !244
  %102 = load i8*, i8** %19, align 4, !dbg !249
  %103 = call i32 @strcmp(i8* %102, i8* getelementptr inbounds ([15 x i8], [15 x i8]* @METHOD_TURNON, i32 0, i32 0)) #7, !dbg !251
  %104 = icmp eq i32 %103, 0, !dbg !252
  br i1 %104, label %105, label %123, !dbg !253

; <label>:105:                                    ; preds = %97
  %106 = load %struct.RoutedDevice*, %struct.RoutedDevice** %13, align 4, !dbg !254
  %107 = getelementptr inbounds %struct.RoutedDevice, %struct.RoutedDevice* %106, i32 0, i32 0, !dbg !256
  %108 = load i32, i32* %107, align 4, !dbg !256
  %109 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([12 x i8], [12 x i8]* @.str.12, i32 0, i32 0), i32 %108), !dbg !257
  %110 = load %struct.RoutedDevice*, %struct.RoutedDevice** %13, align 4, !dbg !258
  %111 = getelementptr inbounds %struct.RoutedDevice, %struct.RoutedDevice* %110, i32 0, i32 1, !dbg !260
  %112 = load i32, i32* %111, align 4, !dbg !260
  %113 = and i32 %112, 1, !dbg !261
  %114 = icmp ne i32 %113, 0, !dbg !261
  br i1 %114, label %115, label %120, !dbg !262

; <label>:115:                                    ; preds = %105
  %116 = load %struct.RoutedDevice*, %struct.RoutedDevice** %13, align 4, !dbg !263
  %117 = getelementptr inbounds %struct.RoutedDevice, %struct.RoutedDevice* %116, i32 0, i32 0, !dbg !265
  %118 = load i32, i32* %117, align 4, !dbg !265
  %119 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([13 x i8], [13 x i8]* @.str.13, i32 0, i32 0), i32 %118), !dbg !266
  br label %122, !dbg !267

; <label>:120:                                    ; preds = %105
  %121 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([9 x i8], [9 x i8]* @.str.14, i32 0, i32 0)), !dbg !268
  br label %122

; <label>:122:                                    ; preds = %120, %115
  br label %149, !dbg !270

; <label>:123:                                    ; preds = %97
  %124 = load i8*, i8** %19, align 4, !dbg !271
  %125 = call i32 @strcmp(i8* %124, i8* getelementptr inbounds ([16 x i8], [16 x i8]* @METHOD_TURNOFF, i32 0, i32 0)) #7, !dbg !274
  %126 = icmp eq i32 %125, 0, !dbg !275
  br i1 %126, label %127, label %145, !dbg !274

; <label>:127:                                    ; preds = %123
  %128 = load %struct.RoutedDevice*, %struct.RoutedDevice** %13, align 4, !dbg !276
  %129 = getelementptr inbounds %struct.RoutedDevice, %struct.RoutedDevice* %128, i32 0, i32 0, !dbg !278
  %130 = load i32, i32* %129, align 4, !dbg !278
  %131 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([13 x i8], [13 x i8]* @.str.15, i32 0, i32 0), i32 %130), !dbg !279
  %132 = load %struct.RoutedDevice*, %struct.RoutedDevice** %13, align 4, !dbg !280
  %133 = getelementptr inbounds %struct.RoutedDevice, %struct.RoutedDevice* %132, i32 0, i32 1, !dbg !282
  %134 = load i32, i32* %133, align 4, !dbg !282
  %135 = and i32 %134, 2, !dbg !283
  %136 = icmp ne i32 %135, 0, !dbg !283
  br i1 %136, label %137, label %142, !dbg !284

; <label>:137:                                    ; preds = %127
  %138 = load %struct.RoutedDevice*, %struct.RoutedDevice** %13, align 4, !dbg !285
  %139 = getelementptr inbounds %struct.RoutedDevice, %struct.RoutedDevice* %138, i32 0, i32 0, !dbg !287
  %140 = load i32, i32* %139, align 4, !dbg !287
  %141 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([14 x i8], [14 x i8]* @.str.16, i32 0, i32 0), i32 %140), !dbg !288
  br label %144, !dbg !289

; <label>:142:                                    ; preds = %127
  %143 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([9 x i8], [9 x i8]* @.str.14, i32 0, i32 0)), !dbg !290
  br label %144

; <label>:144:                                    ; preds = %142, %137
  br label %148, !dbg !292

; <label>:145:                                    ; preds = %123
  %146 = load i8*, i8** %5, align 4, !dbg !293
  %147 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([19 x i8], [19 x i8]* @.str.17, i32 0, i32 0), i8* %146), !dbg !295
  br label %148

; <label>:148:                                    ; preds = %145, %144
  br label %149

; <label>:149:                                    ; preds = %148, %122
  br label %150, !dbg !296

; <label>:150:                                    ; preds = %149, %89
  br label %151, !dbg !297

; <label>:151:                                    ; preds = %150, %87
  %152 = load i32, i32* %12, align 4, !dbg !298
  %153 = add i32 %152, 1, !dbg !298
  store i32 %153, i32* %12, align 4, !dbg !298
  br label %30, !dbg !300, !llvm.loop !301

; <label>:154:                                    ; preds = %30
  %155 = load i8, i8* %11, align 1, !dbg !303
  %156 = trunc i8 %155 to i1, !dbg !303
  br i1 %156, label %159, label %157, !dbg !305

; <label>:157:                                    ; preds = %154
  %158 = load i64, i64* %10, align 8, !dbg !306
  call void @react_to_pattern(i64 %158), !dbg !308
  br label %159, !dbg !309

; <label>:159:                                    ; preds = %157, %154
  %160 = load i32, i32* %6, align 4, !dbg !310
  %161 = load i32, i32* %7, align 4, !dbg !311
  %162 = load i8*, i8** %5, align 4, !dbg !312
  %163 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([13 x i8], [13 x i8]* @.str.18, i32 0, i32 0), i32 %160, i32 %161, i8* %162), !dbg !313
  call void @__AMI_fake_rt_transfer(), !dbg !314
  ret void, !dbg !314
}

; Function Attrs: nounwind readnone
declare void @llvm.dbg.declare(metadata, metadata, metadata) #1

; Function Attrs: nounwind
declare i32 @clock_gettime(i32, %struct.timespec*) #2 section ".CODE_REGION_1_"

; Function Attrs: nounwind
declare void @llvm.var.annotation(i8*, i8*, i8*, i32) #3

declare i32 @printf(i8*, ...) #4 section ".CODE_REGION_1_"

; Function Attrs: nounwind readonly
declare i32 @strlen(i8*) #5 section ".CODE_REGION_1_"

; Function Attrs: nounwind readonly
declare i32 @strncmp(i8*, i8*, i32) #5 section ".CODE_REGION_1_"

; Function Attrs: argmemonly nounwind
declare void @llvm.memcpy.p0i8.p0i8.i32(i8* nocapture writeonly, i8* nocapture readonly, i32, i32, i1) #6

; Function Attrs: nounwind readonly
declare i32 @strcmp(i8*, i8*) #5 section ".CODE_REGION_1_"

; Function Attrs: nounwind
define internal void @react_to_pattern(i64) #0 section ".CODE_REGION_1_" !dbg !315 {
  %2 = alloca i64, align 8
  %3 = alloca i64, align 8
  %4 = alloca i32, align 4
  %5 = alloca %struct.SwitchPattern*, align 4
  %6 = alloca i8, align 1
  %7 = alloca i32, align 4
  %8 = alloca %struct.SwitchMemoryItem*, align 4
  store i64 %0, i64* %2, align 8
  call void @llvm.dbg.declare(metadata i64* %2, metadata !318, metadata !117), !dbg !319
  call void @llvm.dbg.declare(metadata i64* %3, metadata !320, metadata !117), !dbg !321
  %9 = load i64, i64* %2, align 8, !dbg !322
  %10 = sub i64 %9, 4000, !dbg !323
  store i64 %10, i64* %3, align 8, !dbg !321
  %11 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([6 x i8], [6 x i8]* @.str.10, i32 0, i32 0), i8* getelementptr inbounds ([17 x i8], [17 x i8]* @__func__.react_to_pattern, i32 0, i32 0)), !dbg !324
  call void @llvm.dbg.declare(metadata i32* %4, metadata !325, metadata !117), !dbg !327
  store i32 0, i32* %4, align 4, !dbg !327
  br label %12, !dbg !328

; <label>:12:                                     ; preds = %95, %1
  %13 = load i32, i32* %4, align 4, !dbg !329
  %14 = icmp ult i32 %13, 6, !dbg !332
  br i1 %14, label %15, label %98, !dbg !333

; <label>:15:                                     ; preds = %12
  call void @llvm.dbg.declare(metadata %struct.SwitchPattern** %5, metadata !334, metadata !117), !dbg !337
  %16 = load i32, i32* %4, align 4, !dbg !338
  %17 = getelementptr inbounds [6 x %struct.SwitchPattern], [6 x %struct.SwitchPattern]* @SWITCH_PATTERNS, i32 0, i32 %16, !dbg !339
  store %struct.SwitchPattern* %17, %struct.SwitchPattern** %5, align 4, !dbg !337
  call void @llvm.dbg.declare(metadata i8* %6, metadata !340, metadata !117), !dbg !341
  store i8 1, i8* %6, align 1, !dbg !341
  call void @llvm.dbg.declare(metadata i32* %7, metadata !342, metadata !117), !dbg !344
  store i32 0, i32* %7, align 4, !dbg !344
  br label %18, !dbg !345

; <label>:18:                                     ; preds = %62, %15
  %19 = load i32, i32* %7, align 4, !dbg !346
  %20 = icmp ult i32 %19, 4, !dbg !348
  br i1 %20, label %21, label %65, !dbg !349

; <label>:21:                                     ; preds = %18
  call void @llvm.dbg.declare(metadata %struct.SwitchMemoryItem** %8, metadata !351, metadata !117), !dbg !355
  %22 = load i32, i32* %7, align 4, !dbg !356
  %23 = getelementptr inbounds [4 x %struct.SwitchMemoryItem], [4 x %struct.SwitchMemoryItem]* @g_switch_memory, i32 0, i32 %22, !dbg !357
  store %struct.SwitchMemoryItem* %23, %struct.SwitchMemoryItem** %8, align 4, !dbg !355
  %24 = load %struct.SwitchMemoryItem*, %struct.SwitchMemoryItem** %8, align 4, !dbg !358
  %25 = getelementptr inbounds %struct.SwitchMemoryItem, %struct.SwitchMemoryItem* %24, i32 0, i32 0, !dbg !360
  %26 = load i64, i64* %25, align 8, !dbg !360
  %27 = load i64, i64* %3, align 8, !dbg !361
  %28 = icmp ult i64 %26, %27, !dbg !362
  br i1 %28, label %29, label %30, !dbg !363

; <label>:29:                                     ; preds = %21
  store i8 0, i8* %6, align 1, !dbg !364
  br label %65, !dbg !366

; <label>:30:                                     ; preds = %21
  %31 = load %struct.SwitchPattern*, %struct.SwitchPattern** %5, align 4, !dbg !367
  %32 = getelementptr inbounds %struct.SwitchPattern, %struct.SwitchPattern* %31, i32 0, i32 1, !dbg !369
  %33 = load i32, i32* %32, align 4, !dbg !369
  %34 = load %struct.SwitchMemoryItem*, %struct.SwitchMemoryItem** %8, align 4, !dbg !370
  %35 = getelementptr inbounds %struct.SwitchMemoryItem, %struct.SwitchMemoryItem* %34, i32 0, i32 1, !dbg !371
  %36 = load i32, i32* %35, align 8, !dbg !371
  %37 = and i32 %33, %36, !dbg !372
  %38 = icmp ne i32 %37, 0, !dbg !372
  br i1 %38, label %40, label %39, !dbg !373

; <label>:39:                                     ; preds = %30
  store i8 0, i8* %6, align 1, !dbg !374
  br label %65, !dbg !376

; <label>:40:                                     ; preds = %30
  %41 = load i32, i32* %7, align 4, !dbg !377
  %42 = load %struct.SwitchPattern*, %struct.SwitchPattern** %5, align 4, !dbg !379
  %43 = getelementptr inbounds %struct.SwitchPattern, %struct.SwitchPattern* %42, i32 0, i32 2, !dbg !380
  %44 = load i8**, i8*** %43, align 4, !dbg !380
  %45 = getelementptr inbounds i8*, i8** %44, i32 %41, !dbg !379
  %46 = load i8*, i8** %45, align 4, !dbg !379
  %47 = icmp eq i8* %46, null, !dbg !381
  br i1 %47, label %48, label %49, !dbg !382

; <label>:48:                                     ; preds = %40
  br label %65, !dbg !383

; <label>:49:                                     ; preds = %40
  %50 = load i32, i32* %7, align 4, !dbg !385
  %51 = load %struct.SwitchPattern*, %struct.SwitchPattern** %5, align 4, !dbg !387
  %52 = getelementptr inbounds %struct.SwitchPattern, %struct.SwitchPattern* %51, i32 0, i32 2, !dbg !388
  %53 = load i8**, i8*** %52, align 4, !dbg !388
  %54 = getelementptr inbounds i8*, i8** %53, i32 %50, !dbg !387
  %55 = load i8*, i8** %54, align 4, !dbg !387
  %56 = load %struct.SwitchMemoryItem*, %struct.SwitchMemoryItem** %8, align 4, !dbg !389
  %57 = getelementptr inbounds %struct.SwitchMemoryItem, %struct.SwitchMemoryItem* %56, i32 0, i32 2, !dbg !390
  %58 = load i8*, i8** %57, align 4, !dbg !390
  %59 = icmp ne i8* %55, %58, !dbg !391
  br i1 %59, label %60, label %61, !dbg !392

; <label>:60:                                     ; preds = %49
  store i8 0, i8* %6, align 1, !dbg !393
  br label %65, !dbg !395

; <label>:61:                                     ; preds = %49
  br label %62, !dbg !396

; <label>:62:                                     ; preds = %61
  %63 = load i32, i32* %7, align 4, !dbg !397
  %64 = add i32 %63, 1, !dbg !397
  store i32 %64, i32* %7, align 4, !dbg !397
  br label %18, !dbg !398, !llvm.loop !400

; <label>:65:                                     ; preds = %60, %48, %39, %29, %18
  %66 = load i8, i8* %6, align 1, !dbg !402
  %67 = trunc i8 %66 to i1, !dbg !402
  br i1 %67, label %68, label %94, !dbg !404

; <label>:68:                                     ; preds = %65
  %69 = load %struct.SwitchPattern*, %struct.SwitchPattern** %5, align 4, !dbg !405
  %70 = getelementptr inbounds %struct.SwitchPattern, %struct.SwitchPattern* %69, i32 0, i32 1, !dbg !408
  %71 = load i32, i32* %70, align 4, !dbg !408
  %72 = and i32 %71, 1, !dbg !409
  %73 = icmp ne i32 %72, 0, !dbg !409
  br i1 %73, label %74, label %80, !dbg !410

; <label>:74:                                     ; preds = %68
  %75 = load i32, i32* %4, align 4, !dbg !411
  %76 = load %struct.SwitchPattern*, %struct.SwitchPattern** %5, align 4, !dbg !413
  %77 = getelementptr inbounds %struct.SwitchPattern, %struct.SwitchPattern* %76, i32 0, i32 0, !dbg !414
  %78 = load i32, i32* %77, align 4, !dbg !414
  %79 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([24 x i8], [24 x i8]* @.str.25, i32 0, i32 0), i32 %75, i32 %78), !dbg !415
  br label %93, !dbg !416

; <label>:80:                                     ; preds = %68
  %81 = load %struct.SwitchPattern*, %struct.SwitchPattern** %5, align 4, !dbg !417
  %82 = getelementptr inbounds %struct.SwitchPattern, %struct.SwitchPattern* %81, i32 0, i32 1, !dbg !420
  %83 = load i32, i32* %82, align 4, !dbg !420
  %84 = and i32 %83, 2, !dbg !421
  %85 = icmp ne i32 %84, 0, !dbg !421
  br i1 %85, label %86, label %92, !dbg !417

; <label>:86:                                     ; preds = %80
  %87 = load i32, i32* %4, align 4, !dbg !422
  %88 = load %struct.SwitchPattern*, %struct.SwitchPattern** %5, align 4, !dbg !424
  %89 = getelementptr inbounds %struct.SwitchPattern, %struct.SwitchPattern* %88, i32 0, i32 0, !dbg !425
  %90 = load i32, i32* %89, align 4, !dbg !425
  %91 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([25 x i8], [25 x i8]* @.str.26, i32 0, i32 0), i32 %87, i32 %90), !dbg !426
  br label %92, !dbg !427

; <label>:92:                                     ; preds = %86, %80
  br label %93

; <label>:93:                                     ; preds = %92, %74
  br label %94, !dbg !428

; <label>:94:                                     ; preds = %93, %65
  br label %95, !dbg !429

; <label>:95:                                     ; preds = %94
  %96 = load i32, i32* %4, align 4, !dbg !430
  %97 = add i32 %96, 1, !dbg !430
  store i32 %97, i32* %4, align 4, !dbg !430
  br label %12, !dbg !432, !llvm.loop !433

; <label>:98:                                     ; preds = %12
  ret void, !dbg !435
}

; Function Attrs: nounwind
define i32 @main() #0 section ".CODE_REGION_2_" !dbg !436 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca [96 x i8], align 1
  store i32 0, i32* %1, align 4
  call void @create_files(i8* getelementptr inbounds ([17 x i8], [17 x i8]* @.str.19, i32 0, i32 0), i8* getelementptr inbounds ([18 x i8], [18 x i8]* @.str.20, i32 0, i32 0), i8* getelementptr inbounds ([19 x i8], [19 x i8]* @.str.21, i32 0, i32 0), i8* getelementptr inbounds ([14 x i8], [14 x i8]* @.str.22, i32 0, i32 0), i8* getelementptr inbounds ([19 x i8], [19 x i8]* @.str.23, i32 0, i32 0)), !dbg !439
  call void @llvm.dbg.declare(metadata i32* %2, metadata !440, metadata !117), !dbg !442
  call void @llvm.dbg.declare(metadata i32* %3, metadata !443, metadata !117), !dbg !444
  call void @llvm.dbg.declare(metadata i32* %4, metadata !445, metadata !117), !dbg !446
  store i32 0, i32* %4, align 4, !dbg !446
  call void @llvm.dbg.declare(metadata [96 x i8]* %5, metadata !447, metadata !117), !dbg !451
  %6 = bitcast [96 x i8]* %5 to i8*, !dbg !451
  call void @llvm.memcpy.p0i8.p0i8.i32(i8* %6, i8* getelementptr inbounds ([96 x i8], [96 x i8]* @main.data, i32 0, i32 0), i32 96, i32 1, i1 false), !dbg !451
  %7 = call i32 @usecs(), !dbg !452
  store i32 %7, i32* %2, align 4, !dbg !453
  call void @__AMI_fake_local_wrt(), !dbg !454
  store i32 1, i32* @recording_flag, align 4, !dbg !454
  store i32 0, i32* %4, align 4, !dbg !455
  br label %8, !dbg !457

; <label>:8:                                      ; preds = %13, %0
  %9 = load i32, i32* %4, align 4, !dbg !458
  %10 = icmp slt i32 %9, 10, !dbg !461
  br i1 %10, label %11, label %16, !dbg !462

; <label>:11:                                     ; preds = %8
  %12 = getelementptr inbounds [96 x i8], [96 x i8]* %5, i32 0, i32 0, !dbg !463
  call void @__AMI_fake_direct_transfer(), !dbg !464
  call void @listen_to_events(i8* %12, i32 0, i32 0, i8* null), !dbg !464
  br label %13, !dbg !464

; <label>:13:                                     ; preds = %11
  %14 = load i32, i32* %4, align 4, !dbg !465
  %15 = add nsw i32 %14, 1, !dbg !465
  store i32 %15, i32* %4, align 4, !dbg !465
  br label %8, !dbg !467, !llvm.loop !468

; <label>:16:                                     ; preds = %8
  call void @__AMI_fake_local_wrt(), !dbg !470
  store i32 0, i32* @recording_flag, align 4, !dbg !470
  call void @__AMI_fake_local_wrt(), !dbg !471
  store i32 1, i32* @ret_recording_finish, align 4, !dbg !471
  %17 = call i8* bitcast (i8* (...)* @read_measurement to i8* ()*)(), !dbg !472
  %18 = call i32 @usecs(), !dbg !473
  store i32 %18, i32* %3, align 4, !dbg !474
  %19 = load i32, i32* %3, align 4, !dbg !475
  %20 = load i32, i32* %2, align 4, !dbg !476
  %21 = sub i32 %19, %20, !dbg !477
  %22 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([40 x i8], [40 x i8]* @.str.24, i32 0, i32 0), i32 %21), !dbg !478
  ret i32 0, !dbg !479
}

declare void @create_files(i8*, i8*, i8*, i8*, i8*) #4 section ".CODE_REGION_2_"

declare i8* @read_measurement(...) #4 section ".CODE_REGION_2_"

; Function Attrs: nounwind
define void @pinMode(i32, i32) #0 section ".CODE_REGION_2_" !dbg !480 {
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  store i32 %0, i32* %3, align 4
  call void @llvm.dbg.declare(metadata i32* %3, metadata !483, metadata !117), !dbg !484
  store i32 %1, i32* %4, align 4
  call void @llvm.dbg.declare(metadata i32* %4, metadata !485, metadata !117), !dbg !486
  %5 = load i32, i32* %3, align 4, !dbg !487
  %6 = load i32, i32* %4, align 4, !dbg !488
  %7 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([34 x i8], [34 x i8]* @.str.27, i32 0, i32 0), i8* getelementptr inbounds ([8 x i8], [8 x i8]* @__func__.pinMode, i32 0, i32 0), i32 %5, i32 %6), !dbg !489
  ret void, !dbg !490
}

; Function Attrs: nounwind
define i32 @digitalRead(i32) #0 section ".CODE_REGION_2_" !dbg !491 {
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  store i32 %0, i32* %2, align 4
  call void @llvm.dbg.declare(metadata i32* %2, metadata !494, metadata !117), !dbg !495
  call void @llvm.dbg.declare(metadata i32* %3, metadata !496, metadata !117), !dbg !497
  %4 = load i32, i32* %2, align 4, !dbg !498
  %5 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([19 x i8], [19 x i8]* @.str.1.28, i32 0, i32 0), i8* getelementptr inbounds ([12 x i8], [12 x i8]* @__func__.digitalRead, i32 0, i32 0), i32 %4), !dbg !499
  %6 = call i32 (i8*, ...) @__isoc99_scanf(i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.2.29, i32 0, i32 0), i32* %3), !dbg !500
  %7 = load i32, i32* %3, align 4, !dbg !501
  ret i32 %7, !dbg !502
}

declare i32 @__isoc99_scanf(i8*, ...) #4 section ".CODE_REGION_2_"

; Function Attrs: nounwind
define void @digitalWrite(i32, i32) #0 section ".CODE_REGION_2_" !dbg !503 {
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  store i32 %0, i32* %3, align 4
  call void @llvm.dbg.declare(metadata i32* %3, metadata !504, metadata !117), !dbg !505
  store i32 %1, i32* %4, align 4
  call void @llvm.dbg.declare(metadata i32* %4, metadata !506, metadata !117), !dbg !507
  ret void, !dbg !508
}

; Function Attrs: nounwind
define void @Serial_begin(i32) #0 section ".CODE_REGION_2_" !dbg !509 {
  %2 = alloca i32, align 4
  store i32 %0, i32* %2, align 4
  call void @llvm.dbg.declare(metadata i32* %2, metadata !512, metadata !117), !dbg !513
  %3 = load i32, i32* %2, align 4, !dbg !514
  %4 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([20 x i8], [20 x i8]* @.str.3.30, i32 0, i32 0), i8* getelementptr inbounds ([13 x i8], [13 x i8]* @__func__.Serial_begin, i32 0, i32 0), i32 %3), !dbg !515
  ret void, !dbg !516
}

; Function Attrs: nounwind
define i32 @Serial_available() #0 section ".CODE_REGION_2_" !dbg !517 {
  %1 = alloca i32, align 4
  %2 = alloca i8, align 1
  call void @llvm.dbg.declare(metadata i8* %2, metadata !518, metadata !117), !dbg !519
  %3 = call i32 @getchar(), !dbg !520
  %4 = trunc i32 %3 to i8, !dbg !520
  store i8 %4, i8* %2, align 1, !dbg !521
  %5 = load i8, i8* %2, align 1, !dbg !522
  %6 = zext i8 %5 to i32, !dbg !522
  %7 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([11 x i8], [11 x i8]* @.str.4.31, i32 0, i32 0), i8* getelementptr inbounds ([17 x i8], [17 x i8]* @__func__.Serial_available, i32 0, i32 0), i32 %6), !dbg !523
  %8 = load i8, i8* %2, align 1, !dbg !524
  %9 = zext i8 %8 to i32, !dbg !524
  %10 = icmp eq i32 %9, 121, !dbg !526
  br i1 %10, label %11, label %12, !dbg !527

; <label>:11:                                     ; preds = %0
  store i32 1, i32* %1, align 4, !dbg !528
  br label %13, !dbg !528

; <label>:12:                                     ; preds = %0
  store i32 0, i32* %1, align 4, !dbg !529
  br label %13, !dbg !529

; <label>:13:                                     ; preds = %12, %11
  %14 = load i32, i32* %1, align 4, !dbg !530
  ret i32 %14, !dbg !530
}

declare i32 @getchar() #4 section ".CODE_REGION_2_"

; Function Attrs: nounwind
define i32 @Serial_read() #0 section ".CODE_REGION_2_" !dbg !531 {
  %1 = alloca i8, align 1
  call void @llvm.dbg.declare(metadata i8* %1, metadata !532, metadata !117), !dbg !533
  %2 = call i32 @getchar(), !dbg !534
  %3 = trunc i32 %2 to i8, !dbg !534
  store i8 %3, i8* %1, align 1, !dbg !535
  %4 = load i8, i8* %1, align 1, !dbg !536
  %5 = zext i8 %4 to i32, !dbg !537
  ret i32 %5, !dbg !538
}

; Function Attrs: nounwind
define i32 @Serial_write(i8*, i32) #0 section ".CODE_REGION_2_" !dbg !539 {
  %3 = alloca i8*, align 4
  %4 = alloca i32, align 4
  store i8* %0, i8** %3, align 4
  call void @llvm.dbg.declare(metadata i8** %3, metadata !543, metadata !117), !dbg !544
  store i32 %1, i32* %4, align 4
  call void @llvm.dbg.declare(metadata i32* %4, metadata !545, metadata !117), !dbg !546
  %5 = load i8*, i8** %3, align 4, !dbg !547
  %6 = load i32, i32* %4, align 4, !dbg !548
  %7 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([38 x i8], [38 x i8]* @.str.5.32, i32 0, i32 0), i8* getelementptr inbounds ([13 x i8], [13 x i8]* @__func__.Serial_write, i32 0, i32 0), i8* %5, i32 %6), !dbg !549
  ret i32 0, !dbg !550
}

; Function Attrs: nounwind
define i32 @analogRead(i32) #0 section ".CODE_REGION_2_" !dbg !551 {
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  store i32 %0, i32* %2, align 4
  call void @llvm.dbg.declare(metadata i32* %2, metadata !552, metadata !117), !dbg !553
  call void @llvm.dbg.declare(metadata i32* %3, metadata !554, metadata !117), !dbg !555
  %4 = load i32, i32* %2, align 4, !dbg !556
  %5 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([18 x i8], [18 x i8]* @.str.6.33, i32 0, i32 0), i32 %4), !dbg !557
  %6 = call i32 (i8*, ...) @__isoc99_scanf(i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.2.29, i32 0, i32 0), i32* %3), !dbg !558
  %7 = load i32, i32* %3, align 4, !dbg !559
  ret i32 %7, !dbg !560
}

; Function Attrs: nounwind
define i32 @millis() #0 section ".CODE_REGION_2_" !dbg !561 {
  %1 = alloca %struct.timespec, align 4
  call void @llvm.dbg.declare(metadata %struct.timespec* %1, metadata !564, metadata !117), !dbg !573
  %2 = call i32 @gettimeofday(%struct.timespec* %1, i8* null) #3, !dbg !574
  %3 = getelementptr inbounds %struct.timespec, %struct.timespec* %1, i32 0, i32 0, !dbg !575
  %4 = load i32, i32* %3, align 4, !dbg !575
  %5 = mul nsw i32 %4, 1000, !dbg !576
  %6 = getelementptr inbounds %struct.timespec, %struct.timespec* %1, i32 0, i32 1, !dbg !577
  %7 = load i32, i32* %6, align 4, !dbg !577
  %8 = sdiv i32 %7, 1000, !dbg !578
  %9 = add nsw i32 %5, %8, !dbg !579
  ret i32 %9, !dbg !580
}

; Function Attrs: nounwind
declare i32 @gettimeofday(%struct.timespec*, i8*) #2 section ".CODE_REGION_2_"

; Function Attrs: nounwind
define i32 @usecs() #0 section ".CODE_REGION_2_" !dbg !581 {
  %1 = alloca %struct.timespec, align 4
  call void @llvm.dbg.declare(metadata %struct.timespec* %1, metadata !582, metadata !117), !dbg !583
  %2 = call i32 @gettimeofday(%struct.timespec* %1, i8* null) #3, !dbg !584
  %3 = getelementptr inbounds %struct.timespec, %struct.timespec* %1, i32 0, i32 0, !dbg !585
  %4 = load i32, i32* %3, align 4, !dbg !585
  %5 = mul nsw i32 %4, 1000, !dbg !586
  %6 = mul nsw i32 %5, 1000, !dbg !587
  %7 = getelementptr inbounds %struct.timespec, %struct.timespec* %1, i32 0, i32 1, !dbg !588
  %8 = load i32, i32* %7, align 4, !dbg !588
  %9 = add nsw i32 %6, %8, !dbg !589
  ret i32 %9, !dbg !590
}

; Function Attrs: nounwind
define void @delayMicroseconds(float) #0 section ".CODE_REGION_2_" !dbg !591 {
  %2 = alloca float, align 4
  store float %0, float* %2, align 4
  call void @llvm.dbg.declare(metadata float* %2, metadata !595, metadata !117), !dbg !596
  %3 = load float, float* %2, align 4, !dbg !597
  %4 = fptosi float %3 to i32, !dbg !598
  %5 = call i32 @usleep(i32 %4), !dbg !599
  ret void, !dbg !600
}

declare i32 @usleep(i32) #4 section ".CODE_REGION_2_"

; Function Attrs: nounwind
define i32 @toUInt(i8*, i32) #0 section ".CODE_REGION_2_" !dbg !601 {
  %3 = alloca i8*, align 4
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  store i8* %0, i8** %3, align 4
  call void @llvm.dbg.declare(metadata i8** %3, metadata !602, metadata !117), !dbg !603
  store i32 %1, i32* %4, align 4
  call void @llvm.dbg.declare(metadata i32* %4, metadata !604, metadata !117), !dbg !605
  call void @llvm.dbg.declare(metadata i32* %5, metadata !606, metadata !117), !dbg !607
  %6 = load i8*, i8** %3, align 4, !dbg !608
  %7 = call i32 @atoi(i8* %6) #7, !dbg !609
  store i32 %7, i32* %5, align 4, !dbg !610
  %8 = load i32, i32* %5, align 4, !dbg !611
  ret i32 %8, !dbg !612
}

; Function Attrs: nounwind readonly
declare i32 @atoi(i8*) #5 section ".CODE_REGION_2_"

declare void @__AMI_fake_local_wrt()

declare void @__AMI_fake_direct_transfer()

declare void @__AMI_fake_rt_transfer()

attributes #0 = { nounwind "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="arm1176jzf-s" "target-features"="+dsp,+strict-align,+vfp2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind readnone }
attributes #2 = { nounwind "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="arm1176jzf-s" "target-features"="+dsp,+strict-align,+vfp2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { nounwind }
attributes #4 = { "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="arm1176jzf-s" "target-features"="+dsp,+strict-align,+vfp2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #5 = { nounwind readonly "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="arm1176jzf-s" "target-features"="+dsp,+strict-align,+vfp2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #6 = { argmemonly nounwind }
attributes #7 = { nounwind readonly }

!llvm.dbg.cu = !{!0, !103}
!llvm.ident = !{!108, !108}
!llvm.module.flags = !{!109, !110, !111, !112}

!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "clang version 3.9.0 (tags/RELEASE_390/final)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, enums: !2, retainedTypes: !18, globals: !20)
!1 = !DIFile(filename: "light-controller.c", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/light-controller-cb")
!2 = !{!3, !13}
!3 = !DICompositeType(tag: DW_TAG_enumeration_type, name: "SwitchDevices", file: !1, line: 37, size: 32, align: 32, elements: !4)
!4 = !{!5, !6, !7, !8, !9, !10, !11, !12}
!5 = !DIEnumerator(name: "DEVICE_NONE", value: 0)
!6 = !DIEnumerator(name: "DEVICE_MAKUUHUONE_KIRKAS", value: 1)
!7 = !DIEnumerator(name: "DEVICE_OLOHUONE_KIRKAS", value: 2)
!8 = !DIEnumerator(name: "DEVICE_MAKUUHUONE_HIMMEA", value: 3)
!9 = !DIEnumerator(name: "DEVICE_OLOHUONE_HIMMEA", value: 4)
!10 = !DIEnumerator(name: "DEVICE_KAIKKI_KIRKAS", value: 5)
!11 = !DIEnumerator(name: "DEVICE_KAIKKI_HIMMEA", value: 6)
!12 = !DIEnumerator(name: "DEVICE_KAJARIT", value: 7)
!13 = !DICompositeType(tag: DW_TAG_enumeration_type, name: "MethodReact", file: !1, line: 48, size: 32, align: 32, elements: !14)
!14 = !{!15, !16, !17}
!15 = !DIEnumerator(name: "REACT_NONE", value: 0)
!16 = !DIEnumerator(name: "REACT_TURNON", value: 1)
!17 = !DIEnumerator(name: "REACT_TURNOFF", value: 2)
!18 = !{!19}
!19 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: null, size: 32, align: 32)
!20 = !{!21, !23, !24, !40, !45, !49, !50, !62, !63, !64, !69, !73, !77, !81, !82, !83, !84, !88, !89, !90, !91, !92, !93}
!21 = distinct !DIGlobalVariable(name: "recording_flag", scope: !0, file: !1, line: 34, type: !22, isLocal: false, isDefinition: true, variable: i32* @recording_flag)
!22 = !DIBasicType(name: "int", size: 32, align: 32, encoding: DW_ATE_signed)
!23 = distinct !DIGlobalVariable(name: "recording_cnt", scope: !0, file: !1, line: 35, type: !22, isLocal: false, isDefinition: true, variable: i32* @recording_cnt)
!24 = distinct !DIGlobalVariable(name: "DEVICE_ROUTINGS", scope: !0, file: !1, line: 87, type: !25, isLocal: false, isDefinition: true, variable: [20 x %struct.RoutedDevice]* @DEVICE_ROUTINGS)
!25 = !DICompositeType(tag: DW_TAG_array_type, baseType: !26, size: 1920, align: 32, elements: !38)
!26 = !DIDerivedType(tag: DW_TAG_const_type, baseType: !27)
!27 = !DIDerivedType(tag: DW_TAG_typedef, name: "RoutedDevice", file: !1, line: 58, baseType: !28)
!28 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "RoutedDevice", file: !1, line: 54, size: 96, align: 32, elements: !29)
!29 = !{!30, !32, !34}
!30 = !DIDerivedType(tag: DW_TAG_member, name: "targetDevice", scope: !28, file: !1, line: 55, baseType: !31, size: 32, align: 32)
!31 = !DIDerivedType(tag: DW_TAG_typedef, name: "SwitchDevices", file: !1, line: 46, baseType: !3)
!32 = !DIDerivedType(tag: DW_TAG_member, name: "react", scope: !28, file: !1, line: 56, baseType: !33, size: 32, align: 32, offset: 32)
!33 = !DIDerivedType(tag: DW_TAG_typedef, name: "MethodReact", file: !1, line: 52, baseType: !13)
!34 = !DIDerivedType(tag: DW_TAG_member, name: "switchPrefix", scope: !28, file: !1, line: 57, baseType: !35, size: 32, align: 32, offset: 64)
!35 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !36, size: 32, align: 32)
!36 = !DIDerivedType(tag: DW_TAG_const_type, baseType: !37)
!37 = !DIBasicType(name: "char", size: 8, align: 8, encoding: DW_ATE_unsigned_char)
!38 = !{!39}
!39 = !DISubrange(count: 20)
!40 = distinct !DIGlobalVariable(name: "DEVICE_COUNT", scope: !0, file: !1, line: 123, type: !41, isLocal: false, isDefinition: true, variable: i32* @DEVICE_COUNT)
!41 = !DIDerivedType(tag: DW_TAG_const_type, baseType: !42)
!42 = !DIDerivedType(tag: DW_TAG_typedef, name: "size_t", file: !43, line: 62, baseType: !44)
!43 = !DIFile(filename: "/home/zrz0517/llvm-3.9/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/bin/../lib/clang/3.9.0/include/stddef.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/light-controller-cb")
!44 = !DIBasicType(name: "unsigned int", size: 32, align: 32, encoding: DW_ATE_unsigned)
!45 = distinct !DIGlobalVariable(name: "PATTERN_KIRKAS_HIMMEA", scope: !0, file: !1, line: 125, type: !46, isLocal: false, isDefinition: true, variable: [5 x i8*]* @PATTERN_KIRKAS_HIMMEA)
!46 = !DICompositeType(tag: DW_TAG_array_type, baseType: !35, size: 160, align: 32, elements: !47)
!47 = !{!48}
!48 = !DISubrange(count: 5)
!49 = distinct !DIGlobalVariable(name: "PATTERN_HIMMEA_KIRKAS", scope: !0, file: !1, line: 132, type: !46, isLocal: false, isDefinition: true, variable: [5 x i8*]* @PATTERN_HIMMEA_KIRKAS)
!50 = distinct !DIGlobalVariable(name: "SWITCH_PATTERNS", scope: !0, file: !1, line: 139, type: !51, isLocal: false, isDefinition: true, variable: [6 x %struct.SwitchPattern]* @SWITCH_PATTERNS)
!51 = !DICompositeType(tag: DW_TAG_array_type, baseType: !52, size: 576, align: 32, elements: !60)
!52 = !DIDerivedType(tag: DW_TAG_const_type, baseType: !53)
!53 = !DIDerivedType(tag: DW_TAG_typedef, name: "SwitchPattern", file: !1, line: 64, baseType: !54)
!54 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "SwitchPattern", file: !1, line: 60, size: 96, align: 32, elements: !55)
!55 = !{!56, !57, !58}
!56 = !DIDerivedType(tag: DW_TAG_member, name: "targetDevice", scope: !54, file: !1, line: 61, baseType: !31, size: 32, align: 32)
!57 = !DIDerivedType(tag: DW_TAG_member, name: "react", scope: !54, file: !1, line: 62, baseType: !33, size: 32, align: 32, offset: 32)
!58 = !DIDerivedType(tag: DW_TAG_member, name: "switchPrefixes", scope: !54, file: !1, line: 63, baseType: !59, size: 32, align: 32, offset: 64)
!59 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !35, size: 32, align: 32)
!60 = !{!61}
!61 = !DISubrange(count: 6)
!62 = distinct !DIGlobalVariable(name: "PATTERN_COUNT", scope: !0, file: !1, line: 148, type: !41, isLocal: false, isDefinition: true, variable: i32* @PATTERN_COUNT)
!63 = distinct !DIGlobalVariable(name: "SWITCH_MEMORY_ITEMS", scope: !0, file: !1, line: 156, type: !41, isLocal: false, isDefinition: true, variable: i32* @SWITCH_MEMORY_ITEMS)
!64 = distinct !DIGlobalVariable(name: "PATTERN_TIMEOUT_MS", scope: !0, file: !1, line: 158, type: !65, isLocal: false, isDefinition: true, variable: i64* @PATTERN_TIMEOUT_MS)
!65 = !DIDerivedType(tag: DW_TAG_const_type, baseType: !66)
!66 = !DIDerivedType(tag: DW_TAG_typedef, name: "uint64_t", file: !67, line: 58, baseType: !68)
!67 = !DIFile(filename: "/home/zrz0517/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/libc/usr/include/stdint.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/light-controller-cb")
!68 = !DIBasicType(name: "long long unsigned int", size: 64, align: 64, encoding: DW_ATE_unsigned)
!69 = distinct !DIGlobalVariable(name: "METHOD_TURNON", scope: !0, file: !1, line: 160, type: !70, isLocal: false, isDefinition: true, variable: [15 x i8]* @METHOD_TURNON)
!70 = !DICompositeType(tag: DW_TAG_array_type, baseType: !36, size: 120, align: 8, elements: !71)
!71 = !{!72}
!72 = !DISubrange(count: 15)
!73 = distinct !DIGlobalVariable(name: "METHOD_TURNOFF", scope: !0, file: !1, line: 161, type: !74, isLocal: false, isDefinition: true, variable: [16 x i8]* @METHOD_TURNOFF)
!74 = !DICompositeType(tag: DW_TAG_array_type, baseType: !36, size: 128, align: 8, elements: !75)
!75 = !{!76}
!76 = !DISubrange(count: 16)
!77 = distinct !DIGlobalVariable(name: "SWITCH_MAKUUHUONE_KIRKAS", scope: !0, file: !1, line: 74, type: !78, isLocal: true, isDefinition: true, variable: [64 x i8]* @SWITCH_MAKUUHUONE_KIRKAS)
!78 = !DICompositeType(tag: DW_TAG_array_type, baseType: !36, size: 512, align: 8, elements: !79)
!79 = !{!80}
!80 = !DISubrange(count: 64)
!81 = distinct !DIGlobalVariable(name: "SWITCH_OLOHUONE_KIRKAS", scope: !0, file: !1, line: 75, type: !78, isLocal: true, isDefinition: true, variable: [64 x i8]* @SWITCH_OLOHUONE_KIRKAS)
!82 = distinct !DIGlobalVariable(name: "SWITCH_MAKUUHUONE_HIMMEA", scope: !0, file: !1, line: 76, type: !78, isLocal: true, isDefinition: true, variable: [64 x i8]* @SWITCH_MAKUUHUONE_HIMMEA)
!83 = distinct !DIGlobalVariable(name: "SWITCH_OLOHUONE_HIMMEA", scope: !0, file: !1, line: 77, type: !78, isLocal: true, isDefinition: true, variable: [64 x i8]* @SWITCH_OLOHUONE_HIMMEA)
!84 = distinct !DIGlobalVariable(name: "SWITCH_KAIKKI_KIRKAS", scope: !0, file: !1, line: 84, type: !85, isLocal: true, isDefinition: true, variable: [82 x i8]* @SWITCH_KAIKKI_KIRKAS)
!85 = !DICompositeType(tag: DW_TAG_array_type, baseType: !36, size: 656, align: 8, elements: !86)
!86 = !{!87}
!87 = !DISubrange(count: 82)
!88 = distinct !DIGlobalVariable(name: "SWITCH_KAIKKI_HIMMEA", scope: !0, file: !1, line: 85, type: !85, isLocal: true, isDefinition: true, variable: [82 x i8]* @SWITCH_KAIKKI_HIMMEA)
!89 = distinct !DIGlobalVariable(name: "SWITCH_KAJARIT_DUMMY_1", scope: !0, file: !1, line: 79, type: !78, isLocal: true, isDefinition: true, variable: [64 x i8]* @SWITCH_KAJARIT_DUMMY_1)
!90 = distinct !DIGlobalVariable(name: "SWITCH_KAJARIT_DUMMY_2", scope: !0, file: !1, line: 80, type: !78, isLocal: true, isDefinition: true, variable: [64 x i8]* @SWITCH_KAJARIT_DUMMY_2)
!91 = distinct !DIGlobalVariable(name: "SWITCH_KAJARIT_DUMMY_3", scope: !0, file: !1, line: 81, type: !78, isLocal: true, isDefinition: true, variable: [64 x i8]* @SWITCH_KAJARIT_DUMMY_3)
!92 = distinct !DIGlobalVariable(name: "SWITCH_KAJARIT_DUMMY_4", scope: !0, file: !1, line: 82, type: !78, isLocal: true, isDefinition: true, variable: [64 x i8]* @SWITCH_KAJARIT_DUMMY_4)
!93 = distinct !DIGlobalVariable(name: "g_switch_memory", scope: !0, file: !1, line: 150, type: !94, isLocal: true, isDefinition: true, variable: [4 x %struct.SwitchMemoryItem]* @g_switch_memory)
!94 = !DICompositeType(tag: DW_TAG_array_type, baseType: !95, size: 512, align: 64, elements: !101)
!95 = !DIDerivedType(tag: DW_TAG_typedef, name: "SwitchMemoryItem", file: !1, line: 70, baseType: !96)
!96 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "SwitchMemoryItem", file: !1, line: 66, size: 128, align: 64, elements: !97)
!97 = !{!98, !99, !100}
!98 = !DIDerivedType(tag: DW_TAG_member, name: "timestamp", scope: !96, file: !1, line: 67, baseType: !66, size: 64, align: 64)
!99 = !DIDerivedType(tag: DW_TAG_member, name: "method", scope: !96, file: !1, line: 68, baseType: !33, size: 32, align: 32, offset: 64)
!100 = !DIDerivedType(tag: DW_TAG_member, name: "switchPrefix", scope: !96, file: !1, line: 69, baseType: !35, size: 32, align: 32, offset: 96)
!101 = !{!102}
!102 = !DISubrange(count: 4)
!103 = distinct !DICompileUnit(language: DW_LANG_C99, file: !104, producer: "clang version 3.9.0 (tags/RELEASE_390/final)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, enums: !105, retainedTypes: !106)
!104 = !DIFile(filename: "util.c", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/light-controller-cb")
!105 = !{}
!106 = !{!22, !19, !107}
!107 = !DIBasicType(name: "long int", size: 32, align: 32, encoding: DW_ATE_signed)
!108 = !{!"clang version 3.9.0 (tags/RELEASE_390/final)"}
!109 = !{i32 2, !"Dwarf Version", i32 5}
!110 = !{i32 2, !"Debug Info Version", i32 3}
!111 = !{i32 1, !"wchar_size", i32 4}
!112 = !{i32 1, !"min_enum_size", i32 4}
!113 = distinct !DISubprogram(name: "listen_to_events", scope: !1, file: !1, line: 205, type: !114, isLocal: false, isDefinition: true, scopeLine: 206, flags: DIFlagPrototyped, isOptimized: false, unit: !0, variables: !105)
!114 = !DISubroutineType(types: !115)
!115 = !{null, !35, !22, !22, !19}
!116 = !DILocalVariable(name: "data", arg: 1, scope: !113, file: !1, line: 205, type: !35)
!117 = !DIExpression()
!118 = !DILocation(line: 205, column: 35, scope: !113)
!119 = !DILocalVariable(name: "controllerId", arg: 2, scope: !113, file: !1, line: 205, type: !22)
!120 = !DILocation(line: 205, column: 45, scope: !113)
!121 = !DILocalVariable(name: "callbackId", arg: 3, scope: !113, file: !1, line: 205, type: !22)
!122 = !DILocation(line: 205, column: 63, scope: !113)
!123 = !DILocalVariable(name: "context", arg: 4, scope: !113, file: !1, line: 205, type: !19)
!124 = !DILocation(line: 205, column: 81, scope: !113)
!125 = !DILocalVariable(name: "now_ts", scope: !113, file: !1, line: 207, type: !126)
!126 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "timespec", file: !127, line: 120, size: 64, align: 32, elements: !128)
!127 = !DIFile(filename: "/home/zrz0517/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/libc/usr/include/time.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/light-controller-cb")
!128 = !{!129, !132}
!129 = !DIDerivedType(tag: DW_TAG_member, name: "tv_sec", scope: !126, file: !127, line: 122, baseType: !130, size: 32, align: 32)
!130 = !DIDerivedType(tag: DW_TAG_typedef, name: "__time_t", file: !131, line: 139, baseType: !107)
!131 = !DIFile(filename: "/home/zrz0517/study/chain_attestation/ARI-zrz/gcc-linaro-6.2.1-2016.11-x86_64_arm-linux-gnueabihf/arm-linux-gnueabihf/libc/usr/include/bits/types.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/light-controller-cb")
!132 = !DIDerivedType(tag: DW_TAG_member, name: "tv_nsec", scope: !126, file: !127, line: 123, baseType: !133, size: 32, align: 32, offset: 32)
!133 = !DIDerivedType(tag: DW_TAG_typedef, name: "__syscall_slong_t", file: !131, line: 175, baseType: !107)
!134 = !DILocation(line: 207, column: 21, scope: !113)
!135 = !DILocation(line: 208, column: 5, scope: !113)
!136 = !DILocalVariable(name: "now", scope: !113, file: !1, line: 209, type: !66)
!137 = !DILocation(line: 209, column: 14, scope: !113)
!138 = !DILocation(line: 209, column: 27, scope: !113)
!139 = !DILocation(line: 209, column: 34, scope: !113)
!140 = !DILocation(line: 209, column: 50, scope: !113)
!141 = !DILocation(line: 209, column: 58, scope: !113)
!142 = !DILocation(line: 209, column: 41, scope: !113)
!143 = !DILocation(line: 209, column: 20, scope: !113)
!144 = !DILocalVariable(name: "memory_added_pattern", scope: !113, file: !1, line: 210, type: !145)
!145 = !DIBasicType(name: "_Bool", size: 8, align: 8, encoding: DW_ATE_boolean)
!146 = !DILocation(line: 210, column: 49, scope: !113)
!147 = !DILocation(line: 210, column: 5, scope: !113)
!148 = !DILocation(line: 212, column: 5, scope: !113)
!149 = !DILocalVariable(name: "device_id", scope: !150, file: !1, line: 214, type: !42)
!150 = distinct !DILexicalBlock(scope: !113, file: !1, line: 214, column: 5)
!151 = !DILocation(line: 214, column: 17, scope: !150)
!152 = !DILocation(line: 214, column: 10, scope: !150)
!153 = !DILocation(line: 214, column: 32, scope: !154)
!154 = !DILexicalBlockFile(scope: !155, file: !1, discriminator: 1)
!155 = distinct !DILexicalBlock(scope: !150, file: !1, line: 214, column: 5)
!156 = !DILocation(line: 214, column: 42, scope: !154)
!157 = !DILocation(line: 214, column: 5, scope: !154)
!158 = !DILocalVariable(name: "device_routing", scope: !159, file: !1, line: 215, type: !160)
!159 = distinct !DILexicalBlock(scope: !155, file: !1, line: 214, column: 71)
!160 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !26, size: 32, align: 32)
!161 = !DILocation(line: 215, column: 68, scope: !159)
!162 = !DILocation(line: 215, column: 9, scope: !159)
!163 = !DILocation(line: 215, column: 102, scope: !159)
!164 = !DILocation(line: 215, column: 86, scope: !159)
!165 = !DILocalVariable(name: "prefix_length", scope: !159, file: !1, line: 216, type: !41)
!166 = !DILocation(line: 216, column: 22, scope: !159)
!167 = !DILocation(line: 216, column: 45, scope: !159)
!168 = !DILocation(line: 216, column: 61, scope: !159)
!169 = !DILocation(line: 216, column: 38, scope: !159)
!170 = !DILocation(line: 217, column: 21, scope: !171)
!171 = distinct !DILexicalBlock(scope: !159, file: !1, line: 217, column: 13)
!172 = !DILocation(line: 217, column: 27, scope: !171)
!173 = !DILocation(line: 217, column: 43, scope: !171)
!174 = !DILocation(line: 217, column: 57, scope: !171)
!175 = !DILocation(line: 217, column: 13, scope: !171)
!176 = !DILocation(line: 217, column: 72, scope: !171)
!177 = !DILocation(line: 217, column: 13, scope: !159)
!178 = !DILocalVariable(name: "method_start", scope: !179, file: !1, line: 218, type: !35)
!179 = distinct !DILexicalBlock(scope: !171, file: !1, line: 217, column: 78)
!180 = !DILocation(line: 218, column: 25, scope: !179)
!181 = !DILocation(line: 218, column: 40, scope: !179)
!182 = !DILocation(line: 218, column: 47, scope: !179)
!183 = !DILocation(line: 218, column: 45, scope: !179)
!184 = !DILocalVariable(name: "i", scope: !185, file: !1, line: 219, type: !42)
!185 = distinct !DILexicalBlock(scope: !179, file: !1, line: 219, column: 13)
!186 = !DILocation(line: 219, column: 25, scope: !185)
!187 = !DILocation(line: 219, column: 18, scope: !185)
!188 = !DILocation(line: 219, column: 32, scope: !189)
!189 = !DILexicalBlockFile(scope: !190, file: !1, discriminator: 1)
!190 = distinct !DILexicalBlock(scope: !185, file: !1, line: 219, column: 13)
!191 = !DILocation(line: 219, column: 34, scope: !189)
!192 = !DILocation(line: 219, column: 13, scope: !189)
!193 = !DILocation(line: 220, column: 33, scope: !194)
!194 = distinct !DILexicalBlock(scope: !190, file: !1, line: 219, column: 63)
!195 = !DILocation(line: 220, column: 35, scope: !194)
!196 = !DILocation(line: 220, column: 17, scope: !194)
!197 = !DILocation(line: 220, column: 58, scope: !194)
!198 = !DILocation(line: 220, column: 42, scope: !194)
!199 = !DILocation(line: 221, column: 13, scope: !194)
!200 = !DILocation(line: 219, column: 59, scope: !201)
!201 = !DILexicalBlockFile(scope: !190, file: !1, discriminator: 2)
!202 = !DILocation(line: 219, column: 13, scope: !201)
!203 = distinct !{!203, !204}
!204 = !DILocation(line: 219, column: 13, scope: !179)
!205 = !DILocalVariable(name: "method", scope: !179, file: !1, line: 222, type: !33)
!206 = !DILocation(line: 222, column: 64, scope: !179)
!207 = !DILocation(line: 222, column: 13, scope: !179)
!208 = !DILocation(line: 223, column: 24, scope: !209)
!209 = distinct !DILexicalBlock(scope: !179, file: !1, line: 223, column: 17)
!210 = !DILocation(line: 223, column: 17, scope: !209)
!211 = !DILocation(line: 223, column: 54, scope: !209)
!212 = !DILocation(line: 223, column: 17, scope: !179)
!213 = !DILocation(line: 224, column: 24, scope: !214)
!214 = distinct !DILexicalBlock(scope: !209, file: !1, line: 223, column: 60)
!215 = !DILocation(line: 225, column: 13, scope: !214)
!216 = !DILocalVariable(name: "new_item", scope: !179, file: !1, line: 226, type: !95)
!217 = !DILocation(line: 226, column: 30, scope: !179)
!218 = !DILocation(line: 226, column: 41, scope: !179)
!219 = !DILocation(line: 226, column: 42, scope: !179)
!220 = !DILocation(line: 226, column: 47, scope: !179)
!221 = !DILocation(line: 226, column: 55, scope: !179)
!222 = !DILocation(line: 226, column: 71, scope: !179)
!223 = !DILocation(line: 227, column: 56, scope: !179)
!224 = !DILocation(line: 228, column: 34, scope: !179)
!225 = !DILocation(line: 229, column: 9, scope: !179)
!226 = !DILocation(line: 230, column: 13, scope: !227)
!227 = distinct !DILexicalBlock(scope: !159, file: !1, line: 230, column: 13)
!228 = !DILocation(line: 230, column: 29, scope: !227)
!229 = !DILocation(line: 230, column: 42, scope: !227)
!230 = !DILocation(line: 230, column: 13, scope: !159)
!231 = !DILocation(line: 231, column: 6, scope: !232)
!232 = distinct !DILexicalBlock(scope: !227, file: !1, line: 230, column: 58)
!233 = !DILocation(line: 232, column: 13, scope: !232)
!234 = !DILocation(line: 234, column: 21, scope: !235)
!235 = distinct !DILexicalBlock(scope: !159, file: !1, line: 234, column: 13)
!236 = !DILocation(line: 234, column: 27, scope: !235)
!237 = !DILocation(line: 234, column: 43, scope: !235)
!238 = !DILocation(line: 234, column: 57, scope: !235)
!239 = !DILocation(line: 234, column: 13, scope: !235)
!240 = !DILocation(line: 234, column: 72, scope: !235)
!241 = !DILocation(line: 234, column: 13, scope: !159)
!242 = !DILocalVariable(name: "method_start", scope: !243, file: !1, line: 235, type: !35)
!243 = distinct !DILexicalBlock(scope: !235, file: !1, line: 234, column: 78)
!244 = !DILocation(line: 235, column: 64, scope: !243)
!245 = !DILocation(line: 235, column: 13, scope: !243)
!246 = !DILocation(line: 235, column: 79, scope: !243)
!247 = !DILocation(line: 235, column: 86, scope: !243)
!248 = !DILocation(line: 235, column: 84, scope: !243)
!249 = !DILocation(line: 236, column: 24, scope: !250)
!250 = distinct !DILexicalBlock(scope: !243, file: !1, line: 236, column: 17)
!251 = !DILocation(line: 236, column: 17, scope: !250)
!252 = !DILocation(line: 236, column: 53, scope: !250)
!253 = !DILocation(line: 236, column: 17, scope: !243)
!254 = !DILocation(line: 237, column: 40, scope: !255)
!255 = distinct !DILexicalBlock(scope: !250, file: !1, line: 236, column: 59)
!256 = !DILocation(line: 237, column: 56, scope: !255)
!257 = !DILocation(line: 237, column: 17, scope: !255)
!258 = !DILocation(line: 238, column: 21, scope: !259)
!259 = distinct !DILexicalBlock(scope: !255, file: !1, line: 238, column: 21)
!260 = !DILocation(line: 238, column: 37, scope: !259)
!261 = !DILocation(line: 238, column: 43, scope: !259)
!262 = !DILocation(line: 238, column: 21, scope: !255)
!263 = !DILocation(line: 240, column: 45, scope: !264)
!264 = distinct !DILexicalBlock(scope: !259, file: !1, line: 238, column: 59)
!265 = !DILocation(line: 240, column: 61, scope: !264)
!266 = !DILocation(line: 240, column: 21, scope: !264)
!267 = !DILocation(line: 241, column: 17, scope: !264)
!268 = !DILocation(line: 242, column: 21, scope: !269)
!269 = distinct !DILexicalBlock(scope: !259, file: !1, line: 241, column: 24)
!270 = !DILocation(line: 244, column: 13, scope: !255)
!271 = !DILocation(line: 244, column: 31, scope: !272)
!272 = !DILexicalBlockFile(scope: !273, file: !1, discriminator: 1)
!273 = distinct !DILexicalBlock(scope: !250, file: !1, line: 244, column: 24)
!274 = !DILocation(line: 244, column: 24, scope: !272)
!275 = !DILocation(line: 244, column: 61, scope: !272)
!276 = !DILocation(line: 245, column: 41, scope: !277)
!277 = distinct !DILexicalBlock(scope: !273, file: !1, line: 244, column: 67)
!278 = !DILocation(line: 245, column: 57, scope: !277)
!279 = !DILocation(line: 245, column: 17, scope: !277)
!280 = !DILocation(line: 246, column: 21, scope: !281)
!281 = distinct !DILexicalBlock(scope: !277, file: !1, line: 246, column: 21)
!282 = !DILocation(line: 246, column: 37, scope: !281)
!283 = !DILocation(line: 246, column: 43, scope: !281)
!284 = !DILocation(line: 246, column: 21, scope: !277)
!285 = !DILocation(line: 248, column: 46, scope: !286)
!286 = distinct !DILexicalBlock(scope: !281, file: !1, line: 246, column: 60)
!287 = !DILocation(line: 248, column: 62, scope: !286)
!288 = !DILocation(line: 248, column: 21, scope: !286)
!289 = !DILocation(line: 249, column: 17, scope: !286)
!290 = !DILocation(line: 250, column: 21, scope: !291)
!291 = distinct !DILexicalBlock(scope: !281, file: !1, line: 249, column: 24)
!292 = !DILocation(line: 252, column: 13, scope: !277)
!293 = !DILocation(line: 253, column: 47, scope: !294)
!294 = distinct !DILexicalBlock(scope: !273, file: !1, line: 252, column: 20)
!295 = !DILocation(line: 253, column: 17, scope: !294)
!296 = !DILocation(line: 255, column: 9, scope: !243)
!297 = !DILocation(line: 256, column: 5, scope: !159)
!298 = !DILocation(line: 214, column: 67, scope: !299)
!299 = !DILexicalBlockFile(scope: !155, file: !1, discriminator: 2)
!300 = !DILocation(line: 214, column: 5, scope: !299)
!301 = distinct !{!301, !302}
!302 = !DILocation(line: 214, column: 5, scope: !113)
!303 = !DILocation(line: 258, column: 10, scope: !304)
!304 = distinct !DILexicalBlock(scope: !113, file: !1, line: 258, column: 9)
!305 = !DILocation(line: 258, column: 9, scope: !113)
!306 = !DILocation(line: 259, column: 26, scope: !307)
!307 = distinct !DILexicalBlock(scope: !304, file: !1, line: 258, column: 32)
!308 = !DILocation(line: 259, column: 9, scope: !307)
!309 = !DILocation(line: 260, column: 5, scope: !307)
!310 = !DILocation(line: 262, column: 29, scope: !113)
!311 = !DILocation(line: 262, column: 43, scope: !113)
!312 = !DILocation(line: 262, column: 55, scope: !113)
!313 = !DILocation(line: 262, column: 5, scope: !113)
!314 = !DILocation(line: 263, column: 1, scope: !113)
!315 = distinct !DISubprogram(name: "react_to_pattern", scope: !1, file: !1, line: 163, type: !316, isLocal: true, isDefinition: true, scopeLine: 164, flags: DIFlagPrototyped, isOptimized: false, unit: !0, variables: !105)
!316 = !DISubroutineType(types: !317)
!317 = !{null, !66}
!318 = !DILocalVariable(name: "now", arg: 1, scope: !315, file: !1, line: 163, type: !66)
!319 = !DILocation(line: 163, column: 39, scope: !315)
!320 = !DILocalVariable(name: "min_timestamp", scope: !315, file: !1, line: 165, type: !66)
!321 = !DILocation(line: 165, column: 14, scope: !315)
!322 = !DILocation(line: 165, column: 30, scope: !315)
!323 = !DILocation(line: 165, column: 34, scope: !315)
!324 = !DILocation(line: 167, column: 5, scope: !315)
!325 = !DILocalVariable(name: "pattern_index", scope: !326, file: !1, line: 169, type: !42)
!326 = distinct !DILexicalBlock(scope: !315, file: !1, line: 169, column: 5)
!327 = !DILocation(line: 169, column: 17, scope: !326)
!328 = !DILocation(line: 169, column: 10, scope: !326)
!329 = !DILocation(line: 169, column: 36, scope: !330)
!330 = !DILexicalBlockFile(scope: !331, file: !1, discriminator: 1)
!331 = distinct !DILexicalBlock(scope: !326, file: !1, line: 169, column: 5)
!332 = !DILocation(line: 169, column: 50, scope: !330)
!333 = !DILocation(line: 169, column: 5, scope: !330)
!334 = !DILocalVariable(name: "pattern", scope: !335, file: !1, line: 170, type: !336)
!335 = distinct !DILexicalBlock(scope: !331, file: !1, line: 169, column: 84)
!336 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !52, size: 32, align: 32)
!337 = !DILocation(line: 170, column: 30, scope: !335)
!338 = !DILocation(line: 170, column: 57, scope: !335)
!339 = !DILocation(line: 170, column: 41, scope: !335)
!340 = !DILocalVariable(name: "has_match", scope: !335, file: !1, line: 171, type: !145)
!341 = !DILocation(line: 171, column: 14, scope: !335)
!342 = !DILocalVariable(name: "switch_memory_index", scope: !343, file: !1, line: 172, type: !42)
!343 = distinct !DILexicalBlock(scope: !335, file: !1, line: 172, column: 9)
!344 = !DILocation(line: 172, column: 21, scope: !343)
!345 = !DILocation(line: 172, column: 14, scope: !343)
!346 = !DILocation(line: 173, column: 14, scope: !347)
!347 = distinct !DILexicalBlock(scope: !343, file: !1, line: 172, column: 9)
!348 = !DILocation(line: 173, column: 34, scope: !347)
!349 = !DILocation(line: 172, column: 9, scope: !350)
!350 = !DILexicalBlockFile(scope: !343, file: !1, discriminator: 1)
!351 = !DILocalVariable(name: "memory_item", scope: !352, file: !1, line: 175, type: !353)
!352 = distinct !DILexicalBlock(scope: !347, file: !1, line: 174, column: 37)
!353 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !354, size: 32, align: 32)
!354 = !DIDerivedType(tag: DW_TAG_const_type, baseType: !95)
!355 = !DILocation(line: 175, column: 37, scope: !352)
!356 = !DILocation(line: 175, column: 68, scope: !352)
!357 = !DILocation(line: 175, column: 52, scope: !352)
!358 = !DILocation(line: 176, column: 17, scope: !359)
!359 = distinct !DILexicalBlock(scope: !352, file: !1, line: 176, column: 17)
!360 = !DILocation(line: 176, column: 30, scope: !359)
!361 = !DILocation(line: 176, column: 42, scope: !359)
!362 = !DILocation(line: 176, column: 40, scope: !359)
!363 = !DILocation(line: 176, column: 17, scope: !352)
!364 = !DILocation(line: 177, column: 27, scope: !365)
!365 = distinct !DILexicalBlock(scope: !359, file: !1, line: 176, column: 57)
!366 = !DILocation(line: 178, column: 17, scope: !365)
!367 = !DILocation(line: 180, column: 19, scope: !368)
!368 = distinct !DILexicalBlock(scope: !352, file: !1, line: 180, column: 17)
!369 = !DILocation(line: 180, column: 28, scope: !368)
!370 = !DILocation(line: 180, column: 36, scope: !368)
!371 = !DILocation(line: 180, column: 49, scope: !368)
!372 = !DILocation(line: 180, column: 34, scope: !368)
!373 = !DILocation(line: 180, column: 17, scope: !352)
!374 = !DILocation(line: 181, column: 27, scope: !375)
!375 = distinct !DILexicalBlock(scope: !368, file: !1, line: 180, column: 58)
!376 = !DILocation(line: 182, column: 17, scope: !375)
!377 = !DILocation(line: 184, column: 41, scope: !378)
!378 = distinct !DILexicalBlock(scope: !352, file: !1, line: 184, column: 17)
!379 = !DILocation(line: 184, column: 17, scope: !378)
!380 = !DILocation(line: 184, column: 26, scope: !378)
!381 = !DILocation(line: 184, column: 62, scope: !378)
!382 = !DILocation(line: 184, column: 17, scope: !352)
!383 = !DILocation(line: 185, column: 17, scope: !384)
!384 = distinct !DILexicalBlock(scope: !378, file: !1, line: 184, column: 71)
!385 = !DILocation(line: 187, column: 41, scope: !386)
!386 = distinct !DILexicalBlock(scope: !352, file: !1, line: 187, column: 17)
!387 = !DILocation(line: 187, column: 17, scope: !386)
!388 = !DILocation(line: 187, column: 26, scope: !386)
!389 = !DILocation(line: 187, column: 65, scope: !386)
!390 = !DILocation(line: 187, column: 78, scope: !386)
!391 = !DILocation(line: 187, column: 62, scope: !386)
!392 = !DILocation(line: 187, column: 17, scope: !352)
!393 = !DILocation(line: 188, column: 27, scope: !394)
!394 = distinct !DILexicalBlock(scope: !386, file: !1, line: 187, column: 92)
!395 = !DILocation(line: 189, column: 17, scope: !394)
!396 = !DILocation(line: 191, column: 9, scope: !352)
!397 = !DILocation(line: 174, column: 33, scope: !347)
!398 = !DILocation(line: 172, column: 9, scope: !399)
!399 = !DILexicalBlockFile(scope: !347, file: !1, discriminator: 2)
!400 = distinct !{!400, !401}
!401 = !DILocation(line: 172, column: 9, scope: !335)
!402 = !DILocation(line: 192, column: 13, scope: !403)
!403 = distinct !DILexicalBlock(scope: !335, file: !1, line: 192, column: 13)
!404 = !DILocation(line: 192, column: 13, scope: !335)
!405 = !DILocation(line: 193, column: 17, scope: !406)
!406 = distinct !DILexicalBlock(scope: !407, file: !1, line: 193, column: 17)
!407 = distinct !DILexicalBlock(scope: !403, file: !1, line: 192, column: 24)
!408 = !DILocation(line: 193, column: 26, scope: !406)
!409 = !DILocation(line: 193, column: 32, scope: !406)
!410 = !DILocation(line: 193, column: 17, scope: !407)
!411 = !DILocation(line: 194, column: 52, scope: !412)
!412 = distinct !DILexicalBlock(scope: !406, file: !1, line: 193, column: 48)
!413 = !DILocation(line: 194, column: 67, scope: !412)
!414 = !DILocation(line: 194, column: 76, scope: !412)
!415 = !DILocation(line: 194, column: 17, scope: !412)
!416 = !DILocation(line: 196, column: 13, scope: !412)
!417 = !DILocation(line: 196, column: 24, scope: !418)
!418 = !DILexicalBlockFile(scope: !419, file: !1, discriminator: 1)
!419 = distinct !DILexicalBlock(scope: !406, file: !1, line: 196, column: 24)
!420 = !DILocation(line: 196, column: 33, scope: !418)
!421 = !DILocation(line: 196, column: 39, scope: !418)
!422 = !DILocation(line: 197, column: 53, scope: !423)
!423 = distinct !DILexicalBlock(scope: !419, file: !1, line: 196, column: 56)
!424 = !DILocation(line: 197, column: 68, scope: !423)
!425 = !DILocation(line: 197, column: 77, scope: !423)
!426 = !DILocation(line: 197, column: 17, scope: !423)
!427 = !DILocation(line: 199, column: 13, scope: !423)
!428 = !DILocation(line: 200, column: 9, scope: !407)
!429 = !DILocation(line: 201, column: 5, scope: !335)
!430 = !DILocation(line: 169, column: 80, scope: !431)
!431 = !DILexicalBlockFile(scope: !331, file: !1, discriminator: 2)
!432 = !DILocation(line: 169, column: 5, scope: !431)
!433 = distinct !{!433, !434}
!434 = !DILocation(line: 169, column: 5, scope: !315)
!435 = !DILocation(line: 202, column: 1, scope: !315)
!436 = distinct !DISubprogram(name: "main", scope: !1, file: !1, line: 265, type: !437, isLocal: false, isDefinition: true, scopeLine: 266, flags: DIFlagPrototyped, isOptimized: false, unit: !0, variables: !105)
!437 = !DISubroutineType(types: !438)
!438 = !{!22}
!439 = !DILocation(line: 270, column: 2, scope: !436)
!440 = !DILocalVariable(name: "start", scope: !436, file: !1, line: 272, type: !441)
!441 = !DIBasicType(name: "long unsigned int", size: 32, align: 32, encoding: DW_ATE_unsigned)
!442 = !DILocation(line: 272, column: 19, scope: !436)
!443 = !DILocalVariable(name: "end", scope: !436, file: !1, line: 272, type: !441)
!444 = !DILocation(line: 272, column: 26, scope: !436)
!445 = !DILocalVariable(name: "count", scope: !436, file: !1, line: 273, type: !22)
!446 = !DILocation(line: 273, column: 9, scope: !436)
!447 = !DILocalVariable(name: "data", scope: !436, file: !1, line: 274, type: !448)
!448 = !DICompositeType(tag: DW_TAG_array_type, baseType: !37, size: 768, align: 8, elements: !449)
!449 = !{!450}
!450 = !DISubrange(count: 96)
!451 = !DILocation(line: 274, column: 10, scope: !436)
!452 = !DILocation(line: 281, column: 13, scope: !436)
!453 = !DILocation(line: 281, column: 11, scope: !436)
!454 = !DILocation(line: 283, column: 19, scope: !436)
!455 = !DILocation(line: 284, column: 16, scope: !456)
!456 = distinct !DILexicalBlock(scope: !436, file: !1, line: 284, column: 5)
!457 = !DILocation(line: 284, column: 10, scope: !456)
!458 = !DILocation(line: 284, column: 22, scope: !459)
!459 = !DILexicalBlockFile(scope: !460, file: !1, discriminator: 1)
!460 = distinct !DILexicalBlock(scope: !456, file: !1, line: 284, column: 5)
!461 = !DILocation(line: 284, column: 28, scope: !459)
!462 = !DILocation(line: 284, column: 5, scope: !459)
!463 = !DILocation(line: 285, column: 26, scope: !460)
!464 = !DILocation(line: 285, column: 9, scope: !460)
!465 = !DILocation(line: 284, column: 39, scope: !466)
!466 = !DILexicalBlockFile(scope: !460, file: !1, discriminator: 2)
!467 = !DILocation(line: 284, column: 5, scope: !466)
!468 = distinct !{!468, !469}
!469 = !DILocation(line: 284, column: 5, scope: !436)
!470 = !DILocation(line: 291, column: 16, scope: !436)
!471 = !DILocation(line: 292, column: 22, scope: !436)
!472 = !DILocation(line: 293, column: 2, scope: !436)
!473 = !DILocation(line: 295, column: 11, scope: !436)
!474 = !DILocation(line: 295, column: 9, scope: !436)
!475 = !DILocation(line: 296, column: 56, scope: !436)
!476 = !DILocation(line: 296, column: 62, scope: !436)
!477 = !DILocation(line: 296, column: 60, scope: !436)
!478 = !DILocation(line: 296, column: 5, scope: !436)
!479 = !DILocation(line: 299, column: 5, scope: !436)
!480 = distinct !DISubprogram(name: "pinMode", scope: !104, file: !104, line: 8, type: !481, isLocal: false, isDefinition: true, scopeLine: 8, flags: DIFlagPrototyped, isOptimized: false, unit: !103, variables: !105)
!481 = !DISubroutineType(types: !482)
!482 = !{null, !22, !22}
!483 = !DILocalVariable(name: "pin", arg: 1, scope: !480, file: !104, line: 8, type: !22)
!484 = !DILocation(line: 8, column: 18, scope: !480)
!485 = !DILocalVariable(name: "mode", arg: 2, scope: !480, file: !104, line: 8, type: !22)
!486 = !DILocation(line: 8, column: 27, scope: !480)
!487 = !DILocation(line: 9, column: 57, scope: !480)
!488 = !DILocation(line: 9, column: 62, scope: !480)
!489 = !DILocation(line: 9, column: 2, scope: !480)
!490 = !DILocation(line: 10, column: 2, scope: !480)
!491 = distinct !DISubprogram(name: "digitalRead", scope: !104, file: !104, line: 13, type: !492, isLocal: false, isDefinition: true, scopeLine: 13, flags: DIFlagPrototyped, isOptimized: false, unit: !103, variables: !105)
!492 = !DISubroutineType(types: !493)
!493 = !{!22, !22}
!494 = !DILocalVariable(name: "pin", arg: 1, scope: !491, file: !104, line: 13, type: !22)
!495 = !DILocation(line: 13, column: 21, scope: !491)
!496 = !DILocalVariable(name: "val", scope: !491, file: !104, line: 14, type: !22)
!497 = !DILocation(line: 14, column: 6, scope: !491)
!498 = !DILocation(line: 15, column: 42, scope: !491)
!499 = !DILocation(line: 15, column: 2, scope: !491)
!500 = !DILocation(line: 16, column: 2, scope: !491)
!501 = !DILocation(line: 17, column: 9, scope: !491)
!502 = !DILocation(line: 17, column: 2, scope: !491)
!503 = distinct !DISubprogram(name: "digitalWrite", scope: !104, file: !104, line: 20, type: !481, isLocal: false, isDefinition: true, scopeLine: 20, flags: DIFlagPrototyped, isOptimized: false, unit: !103, variables: !105)
!504 = !DILocalVariable(name: "pin", arg: 1, scope: !503, file: !104, line: 20, type: !22)
!505 = !DILocation(line: 20, column: 23, scope: !503)
!506 = !DILocalVariable(name: "value", arg: 2, scope: !503, file: !104, line: 20, type: !22)
!507 = !DILocation(line: 20, column: 32, scope: !503)
!508 = !DILocation(line: 22, column: 2, scope: !503)
!509 = distinct !DISubprogram(name: "Serial_begin", scope: !104, file: !104, line: 25, type: !510, isLocal: false, isDefinition: true, scopeLine: 25, flags: DIFlagPrototyped, isOptimized: false, unit: !103, variables: !105)
!510 = !DISubroutineType(types: !511)
!511 = !{null, !22}
!512 = !DILocalVariable(name: "baud", arg: 1, scope: !509, file: !104, line: 25, type: !22)
!513 = !DILocation(line: 25, column: 23, scope: !509)
!514 = !DILocation(line: 26, column: 43, scope: !509)
!515 = !DILocation(line: 26, column: 2, scope: !509)
!516 = !DILocation(line: 27, column: 2, scope: !509)
!517 = distinct !DISubprogram(name: "Serial_available", scope: !104, file: !104, line: 30, type: !437, isLocal: false, isDefinition: true, scopeLine: 30, isOptimized: false, unit: !103, variables: !105)
!518 = !DILocalVariable(name: "c", scope: !517, file: !104, line: 31, type: !37)
!519 = !DILocation(line: 31, column: 7, scope: !517)
!520 = !DILocation(line: 33, column: 6, scope: !517)
!521 = !DILocation(line: 33, column: 4, scope: !517)
!522 = !DILocation(line: 35, column: 34, scope: !517)
!523 = !DILocation(line: 35, column: 2, scope: !517)
!524 = !DILocation(line: 37, column: 6, scope: !525)
!525 = distinct !DILexicalBlock(scope: !517, file: !104, line: 37, column: 6)
!526 = !DILocation(line: 37, column: 8, scope: !525)
!527 = !DILocation(line: 37, column: 6, scope: !517)
!528 = !DILocation(line: 38, column: 3, scope: !525)
!529 = !DILocation(line: 40, column: 3, scope: !525)
!530 = !DILocation(line: 41, column: 1, scope: !517)
!531 = distinct !DISubprogram(name: "Serial_read", scope: !104, file: !104, line: 43, type: !437, isLocal: false, isDefinition: true, scopeLine: 43, isOptimized: false, unit: !103, variables: !105)
!532 = !DILocalVariable(name: "c", scope: !531, file: !104, line: 44, type: !37)
!533 = !DILocation(line: 44, column: 7, scope: !531)
!534 = !DILocation(line: 46, column: 6, scope: !531)
!535 = !DILocation(line: 46, column: 4, scope: !531)
!536 = !DILocation(line: 48, column: 14, scope: !531)
!537 = !DILocation(line: 48, column: 9, scope: !531)
!538 = !DILocation(line: 48, column: 2, scope: !531)
!539 = distinct !DISubprogram(name: "Serial_write", scope: !104, file: !104, line: 51, type: !540, isLocal: false, isDefinition: true, scopeLine: 51, flags: DIFlagPrototyped, isOptimized: false, unit: !103, variables: !105)
!540 = !DISubroutineType(types: !541)
!541 = !{!22, !542, !22}
!542 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !37, size: 32, align: 32)
!543 = !DILocalVariable(name: "output", arg: 1, scope: !539, file: !104, line: 51, type: !542)
!544 = !DILocation(line: 51, column: 24, scope: !539)
!545 = !DILocalVariable(name: "len", arg: 2, scope: !539, file: !104, line: 51, type: !22)
!546 = !DILocation(line: 51, column: 36, scope: !539)
!547 = !DILocation(line: 52, column: 61, scope: !539)
!548 = !DILocation(line: 52, column: 69, scope: !539)
!549 = !DILocation(line: 52, column: 2, scope: !539)
!550 = !DILocation(line: 53, column: 2, scope: !539)
!551 = distinct !DISubprogram(name: "analogRead", scope: !104, file: !104, line: 56, type: !492, isLocal: false, isDefinition: true, scopeLine: 56, flags: DIFlagPrototyped, isOptimized: false, unit: !103, variables: !105)
!552 = !DILocalVariable(name: "pin", arg: 1, scope: !551, file: !104, line: 56, type: !22)
!553 = !DILocation(line: 56, column: 20, scope: !551)
!554 = !DILocalVariable(name: "val", scope: !551, file: !104, line: 57, type: !22)
!555 = !DILocation(line: 57, column: 6, scope: !551)
!556 = !DILocation(line: 58, column: 31, scope: !551)
!557 = !DILocation(line: 58, column: 2, scope: !551)
!558 = !DILocation(line: 59, column: 2, scope: !551)
!559 = !DILocation(line: 60, column: 9, scope: !551)
!560 = !DILocation(line: 60, column: 2, scope: !551)
!561 = distinct !DISubprogram(name: "millis", scope: !104, file: !104, line: 63, type: !562, isLocal: false, isDefinition: true, scopeLine: 63, isOptimized: false, unit: !103, variables: !105)
!562 = !DISubroutineType(types: !563)
!563 = !{!441}
!564 = !DILocalVariable(name: "start", scope: !561, file: !104, line: 64, type: !565)
!565 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "timeval", file: !566, line: 8, size: 64, align: 32, elements: !567)
!566 = !DIFile(filename: "/usr/include/bits/types/struct_timeval.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/light-controller-cb")
!567 = !{!568, !571}
!568 = !DIDerivedType(tag: DW_TAG_member, name: "tv_sec", scope: !565, file: !566, line: 10, baseType: !569, size: 32, align: 32)
!569 = !DIDerivedType(tag: DW_TAG_typedef, name: "__time_t", file: !570, line: 160, baseType: !107)
!570 = !DIFile(filename: "/usr/include/bits/types.h", directory: "/home/zrz0517/study/chain_attestation/ARI-zrz/oat-evaluation/light-controller-cb")
!571 = !DIDerivedType(tag: DW_TAG_member, name: "tv_usec", scope: !565, file: !566, line: 11, baseType: !572, size: 32, align: 32, offset: 32)
!572 = !DIDerivedType(tag: DW_TAG_typedef, name: "__suseconds_t", file: !570, line: 162, baseType: !107)
!573 = !DILocation(line: 64, column: 17, scope: !561)
!574 = !DILocation(line: 66, column: 2, scope: !561)
!575 = !DILocation(line: 68, column: 15, scope: !561)
!576 = !DILocation(line: 68, column: 22, scope: !561)
!577 = !DILocation(line: 68, column: 37, scope: !561)
!578 = !DILocation(line: 68, column: 44, scope: !561)
!579 = !DILocation(line: 68, column: 29, scope: !561)
!580 = !DILocation(line: 68, column: 2, scope: !561)
!581 = distinct !DISubprogram(name: "usecs", scope: !104, file: !104, line: 72, type: !562, isLocal: false, isDefinition: true, scopeLine: 72, isOptimized: false, unit: !103, variables: !105)
!582 = !DILocalVariable(name: "start", scope: !581, file: !104, line: 73, type: !565)
!583 = !DILocation(line: 73, column: 17, scope: !581)
!584 = !DILocation(line: 75, column: 2, scope: !581)
!585 = !DILocation(line: 77, column: 15, scope: !581)
!586 = !DILocation(line: 77, column: 22, scope: !581)
!587 = !DILocation(line: 77, column: 29, scope: !581)
!588 = !DILocation(line: 77, column: 44, scope: !581)
!589 = !DILocation(line: 77, column: 36, scope: !581)
!590 = !DILocation(line: 77, column: 2, scope: !581)
!591 = distinct !DISubprogram(name: "delayMicroseconds", scope: !104, file: !104, line: 81, type: !592, isLocal: false, isDefinition: true, scopeLine: 81, flags: DIFlagPrototyped, isOptimized: false, unit: !103, variables: !105)
!592 = !DISubroutineType(types: !593)
!593 = !{null, !594}
!594 = !DIBasicType(name: "float", size: 32, align: 32, encoding: DW_ATE_float)
!595 = !DILocalVariable(name: "usecs", arg: 1, scope: !591, file: !104, line: 81, type: !594)
!596 = !DILocation(line: 81, column: 30, scope: !591)
!597 = !DILocation(line: 82, column: 15, scope: !591)
!598 = !DILocation(line: 82, column: 9, scope: !591)
!599 = !DILocation(line: 82, column: 2, scope: !591)
!600 = !DILocation(line: 83, column: 1, scope: !591)
!601 = distinct !DISubprogram(name: "toUInt", scope: !104, file: !104, line: 85, type: !540, isLocal: false, isDefinition: true, scopeLine: 85, flags: DIFlagPrototyped, isOptimized: false, unit: !103, variables: !105)
!602 = !DILocalVariable(name: "input", arg: 1, scope: !601, file: !104, line: 85, type: !542)
!603 = !DILocation(line: 85, column: 18, scope: !601)
!604 = !DILocalVariable(name: "len", arg: 2, scope: !601, file: !104, line: 85, type: !22)
!605 = !DILocation(line: 85, column: 29, scope: !601)
!606 = !DILocalVariable(name: "val", scope: !601, file: !104, line: 86, type: !22)
!607 = !DILocation(line: 86, column: 6, scope: !601)
!608 = !DILocation(line: 87, column: 13, scope: !601)
!609 = !DILocation(line: 87, column: 8, scope: !601)
!610 = !DILocation(line: 87, column: 6, scope: !601)
!611 = !DILocation(line: 88, column: 9, scope: !601)
!612 = !DILocation(line: 88, column: 2, scope: !601)
