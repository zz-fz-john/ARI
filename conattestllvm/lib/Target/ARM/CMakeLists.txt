set(LLVM_TARGET_DEFINITIONS ARM.td)

tablegen(LLVM ARMGenRegisterInfo.inc -gen-register-info)
tablegen(LLVM ARMGenInstrInfo.inc -gen-instr-info)
tablegen(LLVM ARMGenMCCodeEmitter.inc -gen-emitter)
tablegen(LLVM ARMGenMCPseudoLowering.inc -gen-pseudo-lowering)
tablegen(LLVM ARMGenAsmWriter.inc -gen-asm-writer)
tablegen(LLVM ARMGenAsmMatcher.inc -gen-asm-matcher)
tablegen(LLVM ARMGenDAGISel.inc -gen-dag-isel)
tablegen(LLVM ARMGenFastISel.inc -gen-fast-isel)
tablegen(LLVM ARMGenCallingConv.inc -gen-callingconv)
tablegen(LLVM ARMGenSubtargetInfo.inc -gen-subtarget)
tablegen(LLVM ARMGenDisassemblerTables.inc -gen-disassembler)
add_public_tablegen_target(ARMCommonTableGen)

add_llvm_target(ARMCodeGen
  SFIPass.cpp
  CFEventsPass.cpp
  A15SDOptimizer.cpp
  ARMAsmPrinter.cpp
  ARMBaseInstrInfo.cpp
  ARMBaseRegisterInfo.cpp
  ARMConstantIslandPass.cpp
  ARMConstantPoolValue.cpp
  ARMExpandPseudoInsts.cpp
  ARMFastISel.cpp
  ARMFrameLowering.cpp
  ARMHazardRecognizer.cpp
  ARMISelDAGToDAG.cpp
  ARMISelLowering.cpp
  ARMInstrInfo.cpp
  ARMLoadStoreOptimizer.cpp
  ARMMCInstLower.cpp
  ARMMachineFunctionInfo.cpp
  ARMRegisterInfo.cpp
  ARMOptimizeBarriersPass.cpp
  ARMSelectionDAGInfo.cpp
  ARMSubtarget.cpp
  ARMTargetMachine.cpp
  ARMTargetObjectFile.cpp
  ARMTargetTransformInfo.cpp
  MLxExpansionPass.cpp
  Thumb1FrameLowering.cpp
  Thumb1InstrInfo.cpp
  ThumbRegisterInfo.cpp
  Thumb2ITBlockPass.cpp
  Thumb2InstrInfo.cpp
  Thumb2SizeReduction.cpp
  MCExperimentPrinter.cpp
  )

add_subdirectory(TargetInfo)
add_subdirectory(AsmParser)
add_subdirectory(Disassembler)
add_subdirectory(InstPrinter)
add_subdirectory(MCTargetDesc)
