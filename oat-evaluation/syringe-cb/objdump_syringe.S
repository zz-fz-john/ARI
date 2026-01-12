
./syringe_baseline_after_compt：     文件格式 elf32-littlearm


Disassembly of section .interp:

00010134 <.interp>:
   10134:	62696c2f 	rsbvs	r6, r9, #12032	; 0x2f00
   10138:	2d646c2f 	stclcs	12, cr6, [r4, #-188]!	; 0xffffff44
   1013c:	756e696c 	strbvc	r6, [lr, #-2412]!	; 0xfffff694
   10140:	72612d78 	rsbvc	r2, r1, #120, 26	; 0x1e00
   10144:	2e66686d 	cdpcs	8, 6, cr6, cr6, cr13, {3}
   10148:	332e6f73 			; <UNDEFINED> instruction: 0x332e6f73
	...

Disassembly of section .note.ABI-tag:

00010150 <.note.ABI-tag>:
   10150:	00000004 	andeq	r0, r0, r4
   10154:	00000010 	andeq	r0, r0, r0, lsl r0
   10158:	00000001 	andeq	r0, r0, r1
   1015c:	00554e47 	subseq	r4, r5, r7, asr #28
   10160:	00000000 	andeq	r0, r0, r0
   10164:	00000002 	andeq	r0, r0, r2
   10168:	00000006 	andeq	r0, r0, r6
   1016c:	00000020 	andeq	r0, r0, r0, lsr #32

Disassembly of section .gnu.hash:

00010170 <.gnu.hash>:
   10170:	00000025 	andeq	r0, r0, r5, lsr #32
   10174:	00000005 	andeq	r0, r0, r5
   10178:	00000010 	andeq	r0, r0, r0, lsl r0
   1017c:	00000009 	andeq	r0, r0, r9
   10180:	0040c16c 	subeq	ip, r0, ip, ror #2
   10184:	1003c080 	andne	ip, r3, r0, lsl #1
   10188:	48082840 	stmdami	r8, {r6, fp, sp}
   1018c:	c40c0080 	strgt	r0, [ip], #-128	; 0xffffff80
   10190:	07882480 	streq	r2, [r8, r0, lsl #9]
   10194:	10a00601 	adcne	r0, r0, r1, lsl #12
   10198:	00000202 	andeq	r0, r0, r2, lsl #4
   1019c:	8a400000 	bhi	10101a4 <ringBuffer+0xfb849c>
   101a0:	30820892 	umullcc	r0, r2, r2, r8
   101a4:	70400082 	subvc	r0, r0, r2, lsl #1
   101a8:	08048049 	stmdaeq	r4, {r0, r3, r6, pc}
   101ac:	39f90820 	ldmibcc	r9!, {r5, fp}^
   101b0:	042950a0 	strteq	r5, [r9], #-160	; 0xffffff60
   101b4:	01a08041 	asreq	r8, r1, #32
   101b8:	00000000 	andeq	r0, r0, r0
   101bc:	00041049 	andeq	r1, r4, r9, asr #32
   101c0:	00000005 	andeq	r0, r0, r5
   101c4:	00000008 	andeq	r0, r0, r8
   101c8:	00000009 	andeq	r0, r0, r9
   101cc:	0000000a 	andeq	r0, r0, sl
   101d0:	00000000 	andeq	r0, r0, r0
   101d4:	00000010 	andeq	r0, r0, r0, lsl r0
   101d8:	00000011 	andeq	r0, r0, r1, lsl r0
   101dc:	00000012 	andeq	r0, r0, r2, lsl r0
   101e0:	00000015 	andeq	r0, r0, r5, lsl r0
   101e4:	00000017 	andeq	r0, r0, r7, lsl r0
	...
   101f0:	00000018 	andeq	r0, r0, r8, lsl r0
   101f4:	0000001b 	andeq	r0, r0, fp, lsl r0
   101f8:	0000001d 	andeq	r0, r0, sp, lsl r0
   101fc:	0000001e 	andeq	r0, r0, lr, lsl r0
   10200:	00000000 	andeq	r0, r0, r0
   10204:	0000001f 	andeq	r0, r0, pc, lsl r0
   10208:	00000020 	andeq	r0, r0, r0, lsr #32
   1020c:	00000022 	andeq	r0, r0, r2, lsr #32
   10210:	00000023 	andeq	r0, r0, r3, lsr #32
   10214:	00000000 	andeq	r0, r0, r0
   10218:	00000025 	andeq	r0, r0, r5, lsr #32
   1021c:	00000026 	andeq	r0, r0, r6, lsr #32
   10220:	00000027 	andeq	r0, r0, r7, lsr #32
   10224:	00000028 	andeq	r0, r0, r8, lsr #32
   10228:	0000002b 	andeq	r0, r0, fp, lsr #32
   1022c:	0000002d 	andeq	r0, r0, sp, lsr #32
   10230:	0000002e 	andeq	r0, r0, lr, lsr #32
   10234:	0000002f 	andeq	r0, r0, pc, lsr #32
   10238:	00000030 	andeq	r0, r0, r0, lsr r0
   1023c:	00000031 	andeq	r0, r0, r1, lsr r0
   10240:	00000000 	andeq	r0, r0, r0
   10244:	00000032 	andeq	r0, r0, r2, lsr r0
   10248:	00000033 	andeq	r0, r0, r3, lsr r0
   1024c:	00000035 	andeq	r0, r0, r5, lsr r0
   10250:	00000039 	andeq	r0, r0, r9, lsr r0
   10254:	bad299e0 	blt	ff4b69dc <__bss_end__+0xf5bc83d8>
   10258:	0d39ad3c 	ldceq	13, cr10, [r9, #-240]!	; 0xffffff10
   1025c:	7c9bd777 	ldcvc	7, cr13, [fp], {119}	; 0x77
   10260:	7c9665e7 	cfldr32vc	mvfx6, [r6], {231}	; 0xe7
   10264:	1c72c747 	ldclne	7, cr12, [r2], #-284	; 0xfffffee4
   10268:	10614a06 	rsbne	r4, r1, r6, lsl #20
   1026c:	e6854b86 	str	r4, [r5], r6, lsl #23
   10270:	e8d81e2e 	ldm	r8, {r1, r2, r3, r5, r9, sl, fp, ip}^
   10274:	a4f92300 	ldrbtge	r2, [r9], #768	; 0x300
   10278:	7c9f377c 	ldcvc	7, cr3, [pc], {124}	; 0x7c
   1027c:	0f742f17 	svceq	0x00742f17
   10280:	0f738b7d 	svceq	0x00738b7d
   10284:	192c7473 	stmdbne	ip!, {r0, r1, r4, r5, r6, sl, ip, sp, lr}
   10288:	156b2bb8 	strbne	r2, [fp, #-3000]!	; 0xfffff448
   1028c:	7c96f086 	ldcvc	0, cr15, [r6], {134}	; 0x86
   10290:	37900e7f 			; <UNDEFINED> instruction: 0x37900e7f
   10294:	2c99efa6 	ldccs	15, cr14, [r9], {166}	; 0xa6
   10298:	0ea4b293 	mcreq	2, 5, fp, cr4, cr3, {4}
   1029c:	f63d4e2f 			; <UNDEFINED> instruction: 0xf63d4e2f
   102a0:	2a29815a 	bcs	a70810 <ringBuffer+0xa18b08>
   102a4:	bac212a0 	blt	ff094d2c <__bss_end__+0xf57a6728>
   102a8:	bcfff93f 			; <UNDEFINED> instruction: 0xbcfff93f
   102ac:	bc44bb74 	mcrrlt	11, 7, fp, r4, cr4
   102b0:	0f11ed7d 	svceq	0x0011ed7d
   102b4:	0f3b9a5b 	svceq	0x003b9a5b
   102b8:	ca90eebd 	bgt	fe44bdb4 <__bss_end__+0xf4b5d7b0>
   102bc:	f07241e3 			; <UNDEFINED> instruction: 0xf07241e3
   102c0:	8ff9ac08 	svchi	0x00f9ac08
   102c4:	77e5ae8b 	strbvc	sl, [r5, fp, lsl #29]!
   102c8:	0d82b831 	stceq	8, cr11, [r2, #196]	; 0xc4
   102cc:	0d827590 	cfstr32eq	mvfx7, [r2, #576]	; 0x240
   102d0:	21288c53 			; <UNDEFINED> instruction: 0x21288c53
   102d4:	0fa99fa1 	svceq	0x00a99fa1
   102d8:	eafe348d 	b	fff9d514 <__bss_end__+0xf66aef10>
   102dc:	7c9ab171 	ldfvcd	f3, [sl], {113}	; 0x71
   102e0:	1487678c 	strne	r6, [r7], #1932	; 0x78c
   102e4:	3345dd94 	movtcc	sp, #23956	; 0x5d94
   102e8:	fd09cf21 	stc2	15, cr12, [r9, #-132]	; 0xffffff7c
   102ec:	1c93965e 	ldcne	6, cr9, [r3], {94}	; 0x5e
   102f0:	a5b50f0b 	ldrge	r0, [r5, #3851]!	; 0xf0b
   102f4:	7c943c73 	ldcvc	12, cr3, [r4], {115}	; 0x73
   102f8:	4f152227 	svcmi	0x00152227
   102fc:	7ea7aab5 			; <UNDEFINED> instruction: 0x7ea7aab5
   10300:	0b88a54f 	bleq	fe239844 <__bss_end__+0xf494b240>
   10304:	0b886775 	bleq	fe22a0e0 <__bss_end__+0xf493badc>
   10308:	7dd7aaab 	vldrvc	s21, [r7, #684]	; 0x2ac
   1030c:	be582cf8 	mrclt	12, 2, r2, cr8, cr8, {7}
   10310:	e61d840f 	ldr	r8, [sp], -pc, lsl #8
   10314:	7c97c2c8 	lfmvc	f4, 1, [r7], {200}	; 0xc8
   10318:	7c9c7b10 	vldmiavc	ip, {d7-d14}
   1031c:	7c9ddc02 	ldcvc	12, cr13, [sp], {2}
   10320:	00597905 	subseq	r7, r9, r5, lsl #18
   10324:	bfd97efb 	svclt	0x00d97efb

Disassembly of section .dynsym:

00010328 <.dynsym>:
	...
   10338:	000000a8 	andeq	r0, r0, r8, lsr #1
	...
   10344:	00000020 	andeq	r0, r0, r0, lsr #32
   10348:	000001ec 	andeq	r0, r0, ip, ror #3
	...
   10354:	00000020 	andeq	r0, r0, r0, lsr #32
   10358:	00000175 	andeq	r0, r0, r5, ror r1
	...
   10364:	00000011 	andeq	r0, r0, r1, lsl r0
   10368:	000000c4 	andeq	r0, r0, r4, asr #1
	...
   10374:	00000020 	andeq	r0, r0, r0, lsr #32
   10378:	000000de 	ldrdeq	r0, [r0], -lr
	...
   10384:	00000012 	andeq	r0, r0, r2, lsl r0
   10388:	00000150 	andeq	r0, r0, r0, asr r1
	...
   10394:	00000012 	andeq	r0, r0, r2, lsl r0
   10398:	00000014 	andeq	r0, r0, r4, lsl r0
	...
   103a4:	00000012 	andeq	r0, r0, r2, lsl r0
   103a8:	00000081 	andeq	r0, r0, r1, lsl #1
	...
   103b4:	00000012 	andeq	r0, r0, r2, lsl r0
   103b8:	00000206 	andeq	r0, r0, r6, lsl #4
   103bc:	00044e4d 	andeq	r4, r4, sp, asr #28
   103c0:	00000174 	andeq	r0, r0, r4, ror r1
   103c4:	00150012 	andseq	r0, r5, r2, lsl r0
   103c8:	000001b8 			; <UNDEFINED> instruction: 0x000001b8
   103cc:	098ee51c 	stmibeq	lr, {r2, r3, r4, r8, sl, sp, lr, pc}
   103d0:	0000007c 	andeq	r0, r0, ip, ror r0
   103d4:	00250011 	eoreq	r0, r5, r1, lsl r0
   103d8:	00000067 	andeq	r0, r0, r7, rrx
	...
   103e4:	00000012 	andeq	r0, r0, r2, lsl r0
   103e8:	000001fb 	strdeq	r0, [r0], -fp
   103ec:	00057d08 	andeq	r7, r5, r8, lsl #26
   103f0:	09896808 	stmibeq	r9, {r3, fp, sp, lr}
   103f4:	00250011 	eoreq	r0, r5, r1, lsl r0
   103f8:	00000131 	andeq	r0, r0, r1, lsr r1
	...
   10404:	00000012 	andeq	r0, r0, r2, lsl r0
   10408:	00000232 	andeq	r0, r0, r2, lsr r2
   1040c:	000570f4 	strdeq	r7, [r5], -r4
   10410:	00000010 	andeq	r0, r0, r0, lsl r0
   10414:	00220011 	eoreq	r0, r2, r1, lsl r0
   10418:	00000045 	andeq	r0, r0, r5, asr #32
	...
   10424:	00000012 	andeq	r0, r0, r2, lsl r0
   10428:	00000013 	andeq	r0, r0, r3, lsl r0
	...
   10434:	00000012 	andeq	r0, r0, r2, lsl r0
   10438:	00000059 	andeq	r0, r0, r9, asr r0
	...
   10444:	00000012 	andeq	r0, r0, r2, lsl r0
   10448:	0000007a 	andeq	r0, r0, sl, ror r0
	...
   10454:	00000012 	andeq	r0, r0, r2, lsl r0
   10458:	00000157 	andeq	r0, r0, r7, asr r1
	...
   10464:	00000012 	andeq	r0, r0, r2, lsl r0
   10468:	000001be 			; <UNDEFINED> instruction: 0x000001be
   1046c:	00057cc8 	andeq	r7, r5, r8, asr #25
   10470:	00000004 	andeq	r0, r0, r4
   10474:	00250011 	eoreq	r0, r5, r1, lsl r0
   10478:	00000191 	muleq	r0, r1, r1
   1047c:	00057cb4 			; <UNDEFINED> instruction: 0x00057cb4
   10480:	00000004 	andeq	r0, r0, r4
   10484:	00250011 	eoreq	r0, r5, r1, lsl r0
   10488:	0000015c 	andeq	r0, r0, ip, asr r1
	...
   10494:	00000012 	andeq	r0, r0, r2, lsl r0
   10498:	00000086 	andeq	r0, r0, r6, lsl #1
	...
   104a4:	00000012 	andeq	r0, r0, r2, lsl r0
   104a8:	000001a3 	andeq	r0, r0, r3, lsr #3
   104ac:	00057cbc 			; <UNDEFINED> instruction: 0x00057cbc
   104b0:	00000004 	andeq	r0, r0, r4
   104b4:	00250011 	eoreq	r0, r5, r1, lsl r0
   104b8:	00000163 	andeq	r0, r0, r3, ror #2
	...
   104c4:	00000012 	andeq	r0, r0, r2, lsl r0
   104c8:	00000079 	andeq	r0, r0, r9, ror r0
	...
   104d4:	00000012 	andeq	r0, r0, r2, lsl r0
   104d8:	000000ed 	andeq	r0, r0, sp, ror #1
	...
   104e4:	00000012 	andeq	r0, r0, r2, lsl r0
   104e8:	00000030 	andeq	r0, r0, r0, lsr r0
	...
   104f4:	00000012 	andeq	r0, r0, r2, lsl r0
   104f8:	00000053 	andeq	r0, r0, r3, asr r0
	...
   10504:	00000012 	andeq	r0, r0, r2, lsl r0
   10508:	00000028 	andeq	r0, r0, r8, lsr #32
	...
   10514:	00000012 	andeq	r0, r0, r2, lsl r0
   10518:	0000003d 	andeq	r0, r0, sp, lsr r0
	...
   10524:	00000012 	andeq	r0, r0, r2, lsl r0
   10528:	00000142 	andeq	r0, r0, r2, asr #2
	...
   10534:	00000012 	andeq	r0, r0, r2, lsl r0
   10538:	00000237 	andeq	r0, r0, r7, lsr r2
   1053c:	00057ccc 	andeq	r7, r5, ip, asr #25
   10540:	00000001 	andeq	r0, r0, r1
   10544:	00250011 	eoreq	r0, r5, r1, lsl r0
   10548:	00000036 	andeq	r0, r0, r6, lsr r0
   1054c:	00010c60 	andeq	r0, r1, r0, ror #24
   10550:	00000000 	andeq	r0, r0, r0
   10554:	00000012 	andeq	r0, r0, r2, lsl r0
   10558:	0000004b 	andeq	r0, r0, fp, asr #32
	...
   10564:	00000012 	andeq	r0, r0, r2, lsl r0
   10568:	00000060 	andeq	r0, r0, r0, rrx
	...
   10574:	00000012 	andeq	r0, r0, r2, lsl r0
   10578:	00000124 	andeq	r0, r0, r4, lsr #2
	...
   10584:	00000012 	andeq	r0, r0, r2, lsl r0
   10588:	00000019 	andeq	r0, r0, r9, lsl r0
	...
   10594:	00000012 	andeq	r0, r0, r2, lsl r0
   10598:	0000014b 	andeq	r0, r0, fp, asr #2
	...
   105a4:	00000012 	andeq	r0, r0, r2, lsl r0
   105a8:	0000017c 	andeq	r0, r0, ip, ror r1
   105ac:	00057cc4 	andeq	r7, r5, r4, asr #25
   105b0:	00000004 	andeq	r0, r0, r4
   105b4:	00250011 	eoreq	r0, r5, r1, lsl r0
   105b8:	000001e1 	andeq	r0, r0, r1, ror #3
   105bc:	00057cd0 	ldrdeq	r7, [r5], -r0
   105c0:	00000004 	andeq	r0, r0, r4
   105c4:	00250011 	eoreq	r0, r5, r1, lsl r0
   105c8:	00000052 	andeq	r0, r0, r2, asr r0
	...
   105d4:	00000012 	andeq	r0, r0, r2, lsl r0
   105d8:	0000012a 	andeq	r0, r0, sl, lsr #2
	...
   105e4:	00000012 	andeq	r0, r0, r2, lsl r0
   105e8:	0000000b 	andeq	r0, r0, fp
	...
   105f4:	00000012 	andeq	r0, r0, r2, lsl r0
   105f8:	00000074 	andeq	r0, r0, r4, ror r0
	...
   10604:	00000012 	andeq	r0, r0, r2, lsl r0
   10608:	000000fc 	strdeq	r0, [r0], -ip
	...
   10614:	00000012 	andeq	r0, r0, r2, lsl r0
   10618:	000001d6 	ldrdeq	r0, [r0], -r6
   1061c:	098ee5b8 	stmibeq	lr, {r3, r4, r5, r7, r8, sl, sp, lr, pc}
   10620:	00000004 	andeq	r0, r0, r4
   10624:	00250011 	eoreq	r0, r5, r1, lsl r0
   10628:	0000022b 	andeq	r0, r0, fp, lsr #4
   1062c:	098ee5c4 	stmibeq	lr, {r2, r6, r7, r8, sl, sp, lr, pc}
   10630:	00000004 	andeq	r0, r0, r4
   10634:	00250011 	eoreq	r0, r5, r1, lsl r0
   10638:	0000019f 	muleq	r0, pc, r1	; <UNPREDICTABLE>
   1063c:	098ee514 	stmibeq	lr, {r2, r4, r8, sl, sp, lr, pc}
   10640:	00000008 	andeq	r0, r0, r8
   10644:	00250011 	eoreq	r0, r5, r1, lsl r0
   10648:	0000010f 	andeq	r0, r0, pc, lsl #2
	...
   10654:	00000012 	andeq	r0, r0, r2, lsl r0
   10658:	0000016c 	andeq	r0, r0, ip, ror #2
	...
   10664:	00000012 	andeq	r0, r0, r2, lsl r0
   10668:	0000016b 	andeq	r0, r0, fp, ror #2
	...
   10674:	00000012 	andeq	r0, r0, r2, lsl r0
   10678:	000001d1 	ldrdeq	r0, [r0], -r1
   1067c:	098ee598 	stmibeq	lr, {r3, r4, r7, r8, sl, sp, lr, pc}
   10680:	00000020 	andeq	r0, r0, r0, lsr #32
   10684:	00250011 	eoreq	r0, r5, r1, lsl r0
   10688:	00000046 	andeq	r0, r0, r6, asr #32
	...
   10694:	00000012 	andeq	r0, r0, r2, lsl r0
   10698:	00000217 	andeq	r0, r0, r7, lsl r2
   1069c:	098ee5bc 	stmibeq	lr, {r2, r3, r4, r5, r7, r8, sl, sp, lr, pc}
   106a0:	00000008 	andeq	r0, r0, r8
   106a4:	00250011 	eoreq	r0, r5, r1, lsl r0
   106a8:	0000022f 	andeq	r0, r0, pc, lsr #4
   106ac:	098ee5c8 	stmibeq	lr, {r3, r6, r7, r8, sl, sp, lr, pc}
   106b0:	0000003c 	andeq	r0, r0, ip, lsr r0
   106b4:	00250011 	eoreq	r0, r5, r1, lsl r0
   106b8:	0000021c 	andeq	r0, r0, ip, lsl r2
   106bc:	00057cb0 			; <UNDEFINED> instruction: 0x00057cb0
   106c0:	00000004 	andeq	r0, r0, r4
   106c4:	00250011 	eoreq	r0, r5, r1, lsl r0

Disassembly of section .dynstr:

000106c8 <.dynstr>:
   106c8:	62696c00 	rsbvs	r6, r9, #0, 24
   106cc:	6f732e63 	svcvs	0x00732e63
   106d0:	7300362e 	movwvc	r3, #1582	; 0x62e
   106d4:	6e697270 	mcrvs	2, 3, r7, cr9, cr0, {3}
   106d8:	66006674 			; <UNDEFINED> instruction: 0x66006674
   106dc:	6e65706f 	cdpvs	0, 6, cr7, cr5, cr15, {3}
   106e0:	695f5f00 	ldmdbvs	pc, {r8, r9, sl, fp, ip, lr}^	; <UNPREDICTABLE>
   106e4:	39636f73 	stmdbcc	r3!, {r0, r1, r4, r5, r6, r8, r9, sl, fp, sp, lr}^
   106e8:	63735f39 	cmnvs	r3, #57, 30	; 0xe4
   106ec:	00666e61 	rsbeq	r6, r6, r1, ror #28
   106f0:	63747570 	cmnvs	r4, #112, 10	; 0x1c000000
   106f4:	00726168 	rsbseq	r6, r2, r8, ror #2
   106f8:	726f6261 	rsbvc	r6, pc, #268435462	; 0x10000006
   106fc:	656d0074 	strbvs	r0, [sp, #-116]!	; 0xffffff8c
   10700:	7465736d 	strbtvc	r7, [r5], #-877	; 0xfffffc93
   10704:	74656700 	strbtvc	r6, [r5], #-1792	; 0xfffff900
   10708:	72616863 	rsbvc	r6, r1, #6488064	; 0x630000
   1070c:	75706600 	ldrbvc	r6, [r0, #-1536]!	; 0xfffffa00
   10710:	6d007374 	stcvs	3, cr7, [r0, #-464]	; 0xfffffe30
   10714:	70636d65 	rsbvc	r6, r3, r5, ror #26
   10718:	63660079 	cmnvs	r6, #121	; 0x79
   1071c:	65736f6c 	ldrbvs	r6, [r3, #-3948]!	; 0xfffff094
   10720:	6d657200 	sfmvs	f7, 2, [r5, #-0]
   10724:	0065766f 	rsbeq	r7, r5, pc, ror #12
   10728:	656c7375 	strbvs	r7, [ip, #-885]!	; 0xfffffc8b
   1072c:	67007065 	strvs	r7, [r0, -r5, rrx]
   10730:	69747465 	ldmdbvs	r4!, {r0, r2, r5, r6, sl, ip, sp, lr}^
   10734:	666f656d 	strbtvs	r6, [pc], -sp, ror #10
   10738:	00796164 	rsbseq	r6, r9, r4, ror #2
   1073c:	696f7461 	stmdbvs	pc!, {r0, r5, r6, sl, ip, sp, lr}^	; <UNPREDICTABLE>
   10740:	72706600 	rsbsvc	r6, r0, #0, 12
   10744:	66746e69 	ldrbtvs	r6, [r4], -r9, ror #28
   10748:	72726500 	rsbsvc	r6, r2, #0, 10
   1074c:	5f5f0078 	svcpl	0x005f0078
   10750:	6362696c 	cmnvs	r2, #108, 18	; 0x1b0000
   10754:	6174735f 	cmnvs	r4, pc, asr r3
   10758:	6d5f7472 	cfldrdvs	mvd7, [pc, #-456]	; 10598 <_init-0x588>
   1075c:	006e6961 	rsbeq	r6, lr, r1, ror #18
   10760:	7062696c 	rsbvc	r6, r2, ip, ror #18
   10764:	65726874 	ldrbvs	r6, [r2, #-2164]!	; 0xfffff78c
   10768:	732e6461 			; <UNDEFINED> instruction: 0x732e6461
   1076c:	00302e6f 	eorseq	r2, r0, pc, ror #28
   10770:	4d54495f 	vldrmi.16	s9, [r4, #-190]	; 0xffffff42	; <UNPREDICTABLE>
   10774:	7265645f 	rsbvc	r6, r5, #1593835520	; 0x5f000000
   10778:	73696765 	cmnvc	r9, #26476544	; 0x1940000
   1077c:	54726574 	ldrbtpl	r6, [r2], #-1396	; 0xfffffa8c
   10780:	6f6c434d 	svcvs	0x006c434d
   10784:	6154656e 	cmpvs	r4, lr, ror #10
   10788:	00656c62 	rsbeq	r6, r5, r2, ror #24
   1078c:	4d54495f 	vldrmi.16	s9, [r4, #-190]	; 0xffffff42	; <UNPREDICTABLE>
   10790:	6765725f 			; <UNDEFINED> instruction: 0x6765725f
   10794:	65747369 	ldrbvs	r7, [r4, #-873]!	; 0xfffffc97
   10798:	434d5472 	movtmi	r5, #54386	; 0xd472
   1079c:	656e6f6c 	strbvs	r6, [lr, #-3948]!	; 0xfffff094
   107a0:	6c626154 	stfvse	f6, [r2], #-336	; 0xfffffeb0
   107a4:	74700065 	ldrbtvc	r0, [r0], #-101	; 0xffffff9b
   107a8:	61657268 	cmnvs	r5, r8, ror #4
   107ac:	72635f64 	rsbvc	r5, r3, #100, 30	; 0x190
   107b0:	65746165 	ldrbvs	r6, [r4, #-357]!	; 0xfffffe9b
   107b4:	68747000 	ldmdavs	r4!, {ip, sp, lr}^
   107b8:	64616572 	strbtvs	r6, [r1], #-1394	; 0xfffffa8e
   107bc:	7465645f 	strbtvc	r6, [r5], #-1119	; 0xfffffba1
   107c0:	00686361 	rsbeq	r6, r8, r1, ror #6
   107c4:	72687470 	rsbvc	r7, r8, #112, 8	; 0x70000000
   107c8:	5f646165 	svcpl	0x00646165
   107cc:	6574756d 	ldrbvs	r7, [r4, #-1389]!	; 0xfffffa93
   107d0:	6f6c5f78 	svcvs	0x006c5f78
   107d4:	70006b63 	andvc	r6, r0, r3, ror #22
   107d8:	65726874 	ldrbvs	r6, [r2, #-2164]!	; 0xfffff78c
   107dc:	6d5f6461 	cfldrdvs	mvd6, [pc, #-388]	; 10660 <_init-0x4c0>
   107e0:	78657475 	stmdavc	r5!, {r0, r2, r4, r5, r6, sl, ip, sp, lr}^
   107e4:	6c6e755f 	cfstr64vs	mvdx7, [lr], #-380	; 0xfffffe84
   107e8:	006b636f 	rsbeq	r6, fp, pc, ror #6
   107ec:	74636f69 	strbtvc	r6, [r3], #-3945	; 0xfffff097
   107f0:	7473006c 	ldrbtvc	r0, [r3], #-108	; 0xffffff94
   107f4:	706d6372 	rsbvc	r6, sp, r2, ror r3
   107f8:	655f5f00 	ldrbvs	r5, [pc, #-3840]	; f900 <_init-0x1220>
   107fc:	6f6e7272 	svcvs	0x006e7272
   10800:	636f6c5f 	cmnvs	pc, #24320	; 0x5f00
   10804:	6f697461 	svcvs	0x00697461
   10808:	7473006e 	ldrbtvc	r0, [r3], #-110	; 0xffffff92
   1080c:	72726572 	rsbsvc	r6, r2, #478150656	; 0x1c800000
   10810:	6d00726f 	sfmvs	f7, 4, [r0, #-444]	; 0xfffffe44
   10814:	0070616d 	rsbseq	r6, r0, sp, ror #2
   10818:	6c6c616d 	stfvse	f6, [ip], #-436	; 0xfffffe4c
   1081c:	6600636f 	strvs	r6, [r0], -pc, ror #6
   10820:	00656572 	rsbeq	r6, r5, r2, ror r5
   10824:	6d6e756d 	cfstr64vs	mvdx7, [lr, #-436]!	; 0xfffffe4c
   10828:	73007061 	movwvc	r7, #97	; 0x61
   1082c:	61637379 	smcvs	14137	; 0x3739
   10830:	76006c6c 	strvc	r6, [r0], -ip, ror #24
   10834:	72706e73 	rsbsvc	r6, r0, #1840	; 0x730
   10838:	66746e69 	ldrbtvs	r6, [r4], -r9, ror #28
   1083c:	64747300 	ldrbtvs	r7, [r4], #-768	; 0xfffffd00
   10840:	0074756f 	rsbseq	r7, r4, pc, ror #10
   10844:	5f746572 	svcpl	0x00746572
   10848:	6f636572 	svcvs	0x00636572
   1084c:	6e696472 	mcrvs	4, 3, r6, cr9, cr2, {3}
   10850:	69665f67 	stmdbvs	r6!, {r0, r1, r2, r5, r6, r8, r9, sl, fp, ip, lr}^
   10854:	6873696e 	ldmdavs	r3!, {r1, r2, r3, r5, r6, r8, fp, sp, lr}^
   10858:	63657200 	cmnvs	r5, #0, 4
   1085c:	6964726f 	stmdbvs	r4!, {r0, r1, r2, r3, r5, r6, r9, ip, sp, lr}^
   10860:	635f676e 	cmpvs	pc, #28835840	; 0x1b80000
   10864:	6300746e 	movwvs	r7, #1134	; 0x46e
   10868:	72007874 	andvc	r7, r0, #116, 16	; 0x740000
   1086c:	62676e69 	rsbvs	r6, r7, #1680	; 0x690
   10870:	65666675 	strbvs	r6, [r6, #-1653]!	; 0xfffff98b
   10874:	6e695f72 	mcrvs	15, 3, r5, cr9, cr2, {3}
   10878:	665f7469 	ldrbvs	r7, [pc], -r9, ror #8
   1087c:	0067616c 	rsbeq	r6, r7, ip, ror #2
   10880:	74617473 	strbtvc	r7, [r1], #-1139	; 0xfffffb8d
   10884:	65720065 	ldrbvs	r0, [r2, #-101]!	; 0xffffff9b
   10888:	61685f74 	smcvs	34292	; 0x85f4
   1088c:	695f6873 	ldmdbvs	pc, {r0, r1, r4, r5, r6, fp, sp, lr}^	; <UNPREDICTABLE>
   10890:	5f74696e 	svcpl	0x0074696e
   10894:	67616c66 	strbvs	r6, [r1, -r6, ror #24]!
   10898:	73616800 	cmnvc	r1, #0, 16
   1089c:	72650068 	rsbvc	r0, r5, #104	; 0x68
   108a0:	726f5f72 	rsbvc	r5, pc, #456	; 0x1c8
   108a4:	6e696769 	cdpvs	7, 6, cr6, cr9, cr9, {3}
   108a8:	766e6900 	strbtvc	r6, [lr], -r0, lsl #18
   108ac:	5f656b6f 	svcpl	0x00656b6f
   108b0:	00746e63 	rsbseq	r6, r4, r3, ror #28
   108b4:	6d675f5f 	stclvs	15, cr5, [r7, #-380]!	; 0xfffffe84
   108b8:	735f6e6f 	cmpvc	pc, #1776	; 0x6f0
   108bc:	74726174 	ldrbtvc	r6, [r2], #-372	; 0xfffffe8c
   108c0:	72005f5f 	andvc	r5, r0, #380	; 0x17c
   108c4:	42676e69 	rsbmi	r6, r7, #1680	; 0x690
   108c8:	65666675 	strbvs	r6, [r6, #-1653]!	; 0xfffff98b
   108cc:	65720072 	ldrbvs	r0, [r2, #-114]!	; 0xffffff8e
   108d0:	6d5f6461 	cfldrdvs	mvd6, [pc, #-388]	; 10754 <_init-0x3cc>
   108d4:	75736165 	ldrbvc	r6, [r3, #-357]!	; 0xfffffe9b
   108d8:	656d6572 	strbvs	r6, [sp, #-1394]!	; 0xfffffa8e
   108dc:	7300746e 	movwvc	r7, #1134	; 0x46e
   108e0:	00737365 	rsbseq	r7, r3, r5, ror #6
   108e4:	6f636572 	svcvs	0x00636572
   108e8:	6e696472 	mcrvs	4, 3, r6, cr9, cr2, {3}
   108ec:	6c665f67 	stclvs	15, cr5, [r6], #-412	; 0xfffffe64
   108f0:	72006761 	andvc	r6, r0, #25427968	; 0x1840000
   108f4:	6f007365 	svcvs	0x00007365
   108f8:	75750070 	ldrbvc	r0, [r5, #-112]!	; 0xffffff90
   108fc:	72006469 	andvc	r6, r0, #1761607680	; 0x69000000
   10900:	706f5f64 	rsbvc	r5, pc, r4, ror #30
   10904:	5f656574 	svcpl	0x00656574
   10908:	74696e69 	strbtvc	r6, [r9], #-3689	; 0xfffff197
   1090c:	494c4700 	stmdbmi	ip, {r8, r9, sl, lr}^
   10910:	325f4342 	subscc	r4, pc, #134217729	; 0x8000001
   10914:	4700342e 	strmi	r3, [r0, -lr, lsr #8]
   10918:	4342494c 	movtmi	r4, #10572	; 0x294c
   1091c:	372e325f 			; <UNDEFINED> instruction: 0x372e325f
	...

Disassembly of section .gnu.version:

00010922 <.gnu.version>:
   10922:	00000000 	andeq	r0, r0, r0
   10926:	00020000 	andeq	r0, r2, r0
   1092a:	00030000 	andeq	r0, r3, r0
   1092e:	00020002 	andeq	r0, r2, r2
   10932:	00010002 	andeq	r0, r1, r2
   10936:	00020001 	andeq	r0, r2, r1
   1093a:	00020001 	andeq	r0, r2, r1
   1093e:	00020001 	andeq	r0, r2, r1
   10942:	00020002 	andeq	r0, r2, r2
   10946:	00020002 	andeq	r0, r2, r2
   1094a:	00010001 	andeq	r0, r1, r1
   1094e:	00020002 	andeq	r0, r2, r2
   10952:	00020001 	andeq	r0, r2, r1
   10956:	00030002 	andeq	r0, r3, r2
   1095a:	00020002 	andeq	r0, r2, r2
   1095e:	00020002 	andeq	r0, r2, r2
   10962:	00010002 	andeq	r0, r1, r2
   10966:	00020002 	andeq	r0, r2, r2
   1096a:	00020002 	andeq	r0, r2, r2
   1096e:	00020004 	andeq	r0, r2, r4
   10972:	00010001 	andeq	r0, r1, r1
   10976:	00020002 	andeq	r0, r2, r2
   1097a:	00020002 	andeq	r0, r2, r2
   1097e:	00010002 	andeq	r0, r1, r2
   10982:	00010001 	andeq	r0, r1, r1
   10986:	00020002 	andeq	r0, r2, r2
   1098a:	00010002 	andeq	r0, r1, r2
   1098e:	00010002 	andeq	r0, r1, r2
   10992:	00010001 	andeq	r0, r1, r1

Disassembly of section .gnu.version_r:

00010998 <.gnu.version_r>:
   10998:	00010001 	andeq	r0, r1, r1
   1099c:	00000098 	muleq	r0, r8, r0
   109a0:	00000010 	andeq	r0, r0, r0, lsl r0
   109a4:	00000020 	andeq	r0, r0, r0, lsr #32
   109a8:	0d696914 			; <UNDEFINED> instruction: 0x0d696914
   109ac:	00030000 	andeq	r0, r3, r0
   109b0:	00000245 	andeq	r0, r0, r5, asr #4
   109b4:	00000000 	andeq	r0, r0, r0
   109b8:	00020001 	andeq	r0, r2, r1
   109bc:	00000001 	andeq	r0, r0, r1
   109c0:	00000010 	andeq	r0, r0, r0, lsl r0
   109c4:	00000000 	andeq	r0, r0, r0
   109c8:	0d696917 			; <UNDEFINED> instruction: 0x0d696917
   109cc:	00040000 	andeq	r0, r4, r0
   109d0:	0000024f 	andeq	r0, r0, pc, asr #4
   109d4:	00000010 	andeq	r0, r0, r0, lsl r0
   109d8:	0d696914 			; <UNDEFINED> instruction: 0x0d696914
   109dc:	00020000 	andeq	r0, r2, r0
   109e0:	00000245 	andeq	r0, r0, r5, asr #4
   109e4:	00000000 	andeq	r0, r0, r0

Disassembly of section .rel.dyn:

000109e8 <.rel.dyn>:
   109e8:	000570c4 	andeq	r7, r5, r4, asr #1
   109ec:	00000215 	andeq	r0, r0, r5, lsl r2
   109f0:	000570d8 	ldrdeq	r7, [r5], -r8
   109f4:	00000315 	andeq	r0, r0, r5, lsl r3

Disassembly of section .rel.plt:

000109f8 <.rel.plt>:
   109f8:	0005700c 	andeq	r7, r5, ip
   109fc:	00003216 	andeq	r3, r0, r6, lsl r2
   10a00:	00057010 	andeq	r7, r5, r0, lsl r0
   10a04:	00002b16 	andeq	r2, r0, r6, lsl fp
   10a08:	00057014 	andeq	r7, r5, r4, lsl r0
   10a0c:	00001216 	andeq	r1, r0, r6, lsl r2
   10a10:	00057018 	andeq	r7, r5, r8, lsl r0
   10a14:	00001016 	andeq	r1, r0, r6, lsl r0
   10a18:	0005701c 	andeq	r7, r5, ip, lsl r0
   10a1c:	00001316 	andeq	r1, r0, r6, lsl r3
   10a20:	00057020 	andeq	r7, r5, r0, lsr #32
   10a24:	00002e16 	andeq	r2, r0, r6, lsl lr
   10a28:	00057024 	andeq	r7, r5, r4, lsr #32
   10a2c:	00001b16 	andeq	r1, r0, r6, lsl fp
   10a30:	00057028 	andeq	r7, r5, r8, lsr #32
   10a34:	00002316 	andeq	r2, r0, r6, lsl r3
   10a38:	0005702c 	andeq	r7, r5, ip, lsr #32
   10a3c:	00001f16 	andeq	r1, r0, r6, lsl pc
   10a40:	00057030 	andeq	r7, r5, r0, lsr r0
   10a44:	00002516 	andeq	r2, r0, r6, lsl r5
   10a48:	00057034 	andeq	r7, r5, r4, lsr r0
   10a4c:	00002416 	andeq	r2, r0, r6, lsl r4
   10a50:	00057038 	andeq	r7, r5, r8, lsr r0
   10a54:	00000b16 	andeq	r0, r0, r6, lsl fp
   10a58:	0005703c 	andeq	r7, r5, ip, lsr r0
   10a5c:	00000516 	andeq	r0, r0, r6, lsl r5
   10a60:	00057040 	andeq	r7, r5, r0, asr #32
   10a64:	00003616 	andeq	r3, r0, r6, lsl r6
   10a68:	00057044 	andeq	r7, r5, r4, asr #32
   10a6c:	00000616 	andeq	r0, r0, r6, lsl r6
   10a70:	00057048 	andeq	r7, r5, r8, asr #32
   10a74:	00001716 	andeq	r1, r0, r6, lsl r7
   10a78:	0005704c 	andeq	r7, r5, ip, asr #32
   10a7c:	00002016 	andeq	r2, r0, r6, lsl r0
   10a80:	00057050 	andeq	r7, r5, r0, asr r0
   10a84:	00000216 	andeq	r0, r0, r6, lsl r2
   10a88:	00057054 	andeq	r7, r5, r4, asr r0
   10a8c:	00000716 	andeq	r0, r0, r6, lsl r7
   10a90:	00057058 	andeq	r7, r5, r8, asr r0
   10a94:	00001916 	andeq	r1, r0, r6, lsl r9
   10a98:	0005705c 	andeq	r7, r5, ip, asr r0
   10a9c:	00002716 	andeq	r2, r0, r6, lsl r7
   10aa0:	00057060 	andeq	r7, r5, r0, rrx
   10aa4:	00001a16 	andeq	r1, r0, r6, lsl sl
   10aa8:	00057064 	andeq	r7, r5, r4, rrx
   10aac:	00000d16 	andeq	r0, r0, r6, lsl sp
   10ab0:	00057068 	andeq	r7, r5, r8, rrx
   10ab4:	00003316 	andeq	r3, r0, r6, lsl r3
   10ab8:	0005706c 	andeq	r7, r5, ip, rrx
   10abc:	00002216 	andeq	r2, r0, r6, lsl r2
   10ac0:	00057070 	andeq	r7, r5, r0, ror r0
   10ac4:	00001e16 	andeq	r1, r0, r6, lsl lr
   10ac8:	00057074 	andeq	r7, r5, r4, ror r0
   10acc:	00002a16 	andeq	r2, r0, r6, lsl sl
   10ad0:	00057078 	andeq	r7, r5, r8, ror r0
   10ad4:	00001616 	andeq	r1, r0, r6, lsl r6
   10ad8:	0005707c 	andeq	r7, r5, ip, ror r0
   10adc:	00000816 	andeq	r0, r0, r6, lsl r8
   10ae0:	00057080 	andeq	r7, r5, r0, lsl #1
   10ae4:	00002c16 	andeq	r2, r0, r6, lsl ip
   10ae8:	00057084 	andeq	r7, r5, r4, lsl #1
   10aec:	00002616 	andeq	r2, r0, r6, lsl r6
   10af0:	00057088 	andeq	r7, r5, r8, lsl #1
   10af4:	00001116 	andeq	r1, r0, r6, lsl r1
   10af8:	0005708c 	andeq	r7, r5, ip, lsl #1
   10afc:	00003416 	andeq	r3, r0, r6, lsl r4
   10b00:	00057090 	muleq	r5, r0, r0
   10b04:	00002d16 	andeq	r2, r0, r6, lsl sp
   10b08:	00057094 	muleq	r5, r4, r0
   10b0c:	00000f16 	andeq	r0, r0, r6, lsl pc
   10b10:	00057098 	muleq	r5, r8, r0
   10b14:	00001c16 	andeq	r1, r0, r6, lsl ip
   10b18:	0005709c 	muleq	r5, ip, r0
   10b1c:	00001d16 	andeq	r1, r0, r6, lsl sp

Disassembly of section .init:

00010b20 <_init>:
   10b20:	e92d4008 	push	{r3, lr}
   10b24:	eb00d186 	bl	45144 <call_weak_fn>
   10b28:	e8bd8008 	pop	{r3, pc}

Disassembly of section .plt:

00010b2c <pthread_mutex_unlock@plt-0x14>:
   10b2c:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   10b30:	e59fe004 	ldr	lr, [pc, #4]	; 10b3c <_init+0x1c>
   10b34:	e08fe00e 	add	lr, pc, lr
   10b38:	e5bef008 	ldr	pc, [lr, #8]!
   10b3c:	000464c4 	andeq	r6, r4, r4, asr #9

00010b40 <pthread_mutex_unlock@plt>:
   10b40:	e28fc600 	add	ip, pc, #0, 12
   10b44:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10b48:	e5bcf4c4 	ldr	pc, [ip, #1220]!	; 0x4c4

00010b4c <strcmp@plt>:
   10b4c:	e28fc600 	add	ip, pc, #0, 12
   10b50:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10b54:	e5bcf4bc 	ldr	pc, [ip, #1212]!	; 0x4bc

00010b58 <printf@plt>:
   10b58:	e28fc600 	add	ip, pc, #0, 12
   10b5c:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10b60:	e5bcf4b4 	ldr	pc, [ip, #1204]!	; 0x4b4

00010b64 <fopen@plt>:
   10b64:	e28fc600 	add	ip, pc, #0, 12
   10b68:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10b6c:	e5bcf4ac 	ldr	pc, [ip, #1196]!	; 0x4ac

00010b70 <free@plt>:
   10b70:	e28fc600 	add	ip, pc, #0, 12
   10b74:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10b78:	e5bcf4a4 	ldr	pc, [ip, #1188]!	; 0x4a4

00010b7c <pthread_mutex_lock@plt>:
   10b7c:	e28fc600 	add	ip, pc, #0, 12
   10b80:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10b84:	e5bcf49c 	ldr	pc, [ip, #1180]!	; 0x49c

00010b88 <pthread_detach@plt>:
   10b88:	e28fc600 	add	ip, pc, #0, 12
   10b8c:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10b90:	e5bcf494 	ldr	pc, [ip, #1172]!	; 0x494

00010b94 <memcpy@plt>:
   10b94:	e28fc600 	add	ip, pc, #0, 12
   10b98:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10b9c:	e5bcf48c 	ldr	pc, [ip, #1164]!	; 0x48c

00010ba0 <getchar@plt>:
   10ba0:	e28fc600 	add	ip, pc, #0, 12
   10ba4:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10ba8:	e5bcf484 	ldr	pc, [ip, #1156]!	; 0x484

00010bac <ioctl@plt>:
   10bac:	e28fc600 	add	ip, pc, #0, 12
   10bb0:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10bb4:	e5bcf47c 	ldr	pc, [ip, #1148]!	; 0x47c

00010bb8 <usleep@plt>:
   10bb8:	e28fc600 	add	ip, pc, #0, 12
   10bbc:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10bc0:	e5bcf474 	ldr	pc, [ip, #1140]!	; 0x474

00010bc4 <gettimeofday@plt>:
   10bc4:	e28fc600 	add	ip, pc, #0, 12
   10bc8:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10bcc:	e5bcf46c 	ldr	pc, [ip, #1132]!	; 0x46c

00010bd0 <pthread_create@plt>:
   10bd0:	e28fc600 	add	ip, pc, #0, 12
   10bd4:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10bd8:	e5bcf464 	ldr	pc, [ip, #1124]!	; 0x464

00010bdc <puts@plt>:
   10bdc:	e28fc600 	add	ip, pc, #0, 12
   10be0:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10be4:	e5bcf45c 	ldr	pc, [ip, #1116]!	; 0x45c

00010be8 <malloc@plt>:
   10be8:	e28fc600 	add	ip, pc, #0, 12
   10bec:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10bf0:	e5bcf454 	ldr	pc, [ip, #1108]!	; 0x454

00010bf4 <__libc_start_main@plt>:
   10bf4:	e28fc600 	add	ip, pc, #0, 12
   10bf8:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10bfc:	e5bcf44c 	ldr	pc, [ip, #1100]!	; 0x44c

00010c00 <strerror@plt>:
   10c00:	e28fc600 	add	ip, pc, #0, 12
   10c04:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10c08:	e5bcf444 	ldr	pc, [ip, #1092]!	; 0x444

00010c0c <__gmon_start__@plt>:
   10c0c:	e28fc600 	add	ip, pc, #0, 12
   10c10:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10c14:	e5bcf43c 	ldr	pc, [ip, #1084]!	; 0x43c

00010c18 <open@plt>:
   10c18:	e28fc600 	add	ip, pc, #0, 12
   10c1c:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10c20:	e5bcf434 	ldr	pc, [ip, #1076]!	; 0x434

00010c24 <syscall@plt>:
   10c24:	e28fc600 	add	ip, pc, #0, 12
   10c28:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10c2c:	e5bcf42c 	ldr	pc, [ip, #1068]!	; 0x42c

00010c30 <mmap@plt>:
   10c30:	e28fc600 	add	ip, pc, #0, 12
   10c34:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10c38:	e5bcf424 	ldr	pc, [ip, #1060]!	; 0x424

00010c3c <fprintf@plt>:
   10c3c:	e28fc600 	add	ip, pc, #0, 12
   10c40:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10c44:	e5bcf41c 	ldr	pc, [ip, #1052]!	; 0x41c

00010c48 <__errno_location@plt>:
   10c48:	e28fc600 	add	ip, pc, #0, 12
   10c4c:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10c50:	e5bcf414 	ldr	pc, [ip, #1044]!	; 0x414

00010c54 <snprintf@plt>:
   10c54:	e28fc600 	add	ip, pc, #0, 12
   10c58:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10c5c:	e5bcf40c 	ldr	pc, [ip, #1036]!	; 0x40c

00010c60 <memset@plt>:
   10c60:	e28fc600 	add	ip, pc, #0, 12
   10c64:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10c68:	e5bcf404 	ldr	pc, [ip, #1028]!	; 0x404

00010c6c <putchar@plt>:
   10c6c:	e28fc600 	add	ip, pc, #0, 12
   10c70:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10c74:	e5bcf3fc 	ldr	pc, [ip, #1020]!	; 0x3fc

00010c78 <fclose@plt>:
   10c78:	e28fc600 	add	ip, pc, #0, 12
   10c7c:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10c80:	e5bcf3f4 	ldr	pc, [ip, #1012]!	; 0x3f4

00010c84 <munmap@plt>:
   10c84:	e28fc600 	add	ip, pc, #0, 12
   10c88:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10c8c:	e5bcf3ec 	ldr	pc, [ip, #1004]!	; 0x3ec

00010c90 <errx@plt>:
   10c90:	e28fc600 	add	ip, pc, #0, 12
   10c94:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10c98:	e5bcf3e4 	ldr	pc, [ip, #996]!	; 0x3e4

00010c9c <sprintf@plt>:
   10c9c:	e28fc600 	add	ip, pc, #0, 12
   10ca0:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10ca4:	e5bcf3dc 	ldr	pc, [ip, #988]!	; 0x3dc

00010ca8 <__isoc99_scanf@plt>:
   10ca8:	e28fc600 	add	ip, pc, #0, 12
   10cac:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10cb0:	e5bcf3d4 	ldr	pc, [ip, #980]!	; 0x3d4

00010cb4 <remove@plt>:
   10cb4:	e28fc600 	add	ip, pc, #0, 12
   10cb8:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10cbc:	e5bcf3cc 	ldr	pc, [ip, #972]!	; 0x3cc

00010cc0 <vsnprintf@plt>:
   10cc0:	e28fc600 	add	ip, pc, #0, 12
   10cc4:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10cc8:	e5bcf3c4 	ldr	pc, [ip, #964]!	; 0x3c4

00010ccc <atoi@plt>:
   10ccc:	e28fc600 	add	ip, pc, #0, 12
   10cd0:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10cd4:	e5bcf3bc 	ldr	pc, [ip, #956]!	; 0x3bc

00010cd8 <fputs@plt>:
   10cd8:	e28fc600 	add	ip, pc, #0, 12
   10cdc:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10ce0:	e5bcf3b4 	ldr	pc, [ip, #948]!	; 0x3b4

00010ce4 <abort@plt>:
   10ce4:	e28fc600 	add	ip, pc, #0, 12
   10ce8:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10cec:	e5bcf3ac 	ldr	pc, [ip, #940]!	; 0x3ac

00010cf0 <close@plt>:
   10cf0:	e28fc600 	add	ip, pc, #0, 12
   10cf4:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10cf8:	e5bcf3a4 	ldr	pc, [ip, #932]!	; 0x3a4

Disassembly of section .DATA_REGION_0__data:

00010cfc <global_data>:
   10cfc:	00000171 	andeq	r0, r0, r1, ror r1

00010d00 <motorDirPin>:
   10d00:	00000002 	andeq	r0, r0, r2

00010d04 <motorStepPin>:
   10d04:	00000003 	andeq	r0, r0, r3

00010d08 <mLBolus>:
   10d08:	3f000000 	svccc	0x00000000

00010d0c <mLBolusStep>:
   10d0c:	3d4ccccd 	stclcc	12, cr12, [ip, #-820]	; 0xfffffccc

00010d10 <serialStrReady>:
   10d10:	00000000 	andeq	r0, r0, r0

00010d14 <serialStrLen>:
   10d14:	00000000 	andeq	r0, r0, r0

Disassembly of section .CODE_REGION_1_:

00020000 <processSerial>:
   20000:	e92d4c10 	push	{r4, sl, fp, lr}
   20004:	e28db008 	add	fp, sp, #8
   20008:	ed2d8b02 	vpush	{d8}
   2000c:	e24dd008 	sub	sp, sp, #8
   20010:	fa009261 	blx	4499c <mission_control>
   20014:	e59f0144 	ldr	r0, [pc, #324]	; 20160 <processSerial+0x160>
   20018:	e5d01000 	ldrb	r1, [r0]
   2001c:	e351002b 	cmp	r1, #43	; 0x2b
   20020:	e3a08064 	mov	r8, #100	; 0x64
   20024:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   20028:	e52d1004 	push	{r1}		; (str r1, [sp, #-4]!)
   2002c:	e52d2004 	push	{r2}		; (str r2, [sp, #-4]!)
   20030:	e10f1000 	mrs	r1, CPSR
   20034:	e3a02001 	mov	r2, #1
   20038:	eb00dd31 	bl	57504 <__tsf_direct_jmp_cc_recording>
   2003c:	e49d2004 	pop	{r2}		; (ldr r2, [sp], #4)
   20040:	e49d1004 	pop	{r1}		; (ldr r1, [sp], #4)
   20044:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   20048:	1a000001 	bne	20054 <processSerial+0x54>
   2004c:	e3a00000 	mov	r0, #0
   20050:	ea00000d 	b	2008c <processSerial+0x8c>
   20054:	e5d00000 	ldrb	r0, [r0]
   20058:	e350002d 	cmp	r0, #45	; 0x2d
   2005c:	e3a08064 	mov	r8, #100	; 0x64
   20060:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   20064:	e52d1004 	push	{r1}		; (str r1, [sp, #-4]!)
   20068:	e52d2004 	push	{r2}		; (str r2, [sp, #-4]!)
   2006c:	e10f1000 	mrs	r1, CPSR
   20070:	e3a02001 	mov	r2, #1
   20074:	eb00dd22 	bl	57504 <__tsf_direct_jmp_cc_recording>
   20078:	e49d2004 	pop	{r2}		; (ldr r2, [sp], #4)
   2007c:	e49d1004 	pop	{r1}		; (ldr r1, [sp], #4)
   20080:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   20084:	1a00000c 	bne	200bc <processSerial+0xbc>
   20088:	e3a00001 	mov	r0, #1
   2008c:	eb000039 	bl	20178 <bolus>
   20090:	eb0000b8 	bl	20378 <updateScreen>
   20094:	e59f00d8 	ldr	r0, [pc, #216]	; 20174 <processSerial+0x174>
   20098:	e3a04000 	mov	r4, #0
   2009c:	e5c04000 	strb	r4, [r0]
   200a0:	e59f00bc 	ldr	r0, [pc, #188]	; 20164 <processSerial+0x164>
   200a4:	e5804000 	str	r4, [r0]
   200a8:	e24bd010 	sub	sp, fp, #16
   200ac:	ecbd8b02 	vpop	{d8}
   200b0:	e8bd0c10 	pop	{r4, sl, fp}
   200b4:	e49d8004 	pop	{r8}		; (ldr r8, [sp], #4)
   200b8:	eb00dd27 	bl	5755c <__tsf_bkwd_pop_pc_recording>
   200bc:	e59f40a0 	ldr	r4, [pc, #160]	; 20164 <processSerial+0x164>
   200c0:	e59f0098 	ldr	r0, [pc, #152]	; 20160 <processSerial+0x160>
   200c4:	e5941000 	ldr	r1, [r4]
   200c8:	eb00014b 	bl	205fc <toUInt>
   200cc:	e3500000 	cmp	r0, #0
   200d0:	e3a08064 	mov	r8, #100	; 0x64
   200d4:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   200d8:	e52d1004 	push	{r1}		; (str r1, [sp, #-4]!)
   200dc:	e52d2004 	push	{r2}		; (str r2, [sp, #-4]!)
   200e0:	e10f1000 	mrs	r1, CPSR
   200e4:	e3a02000 	mov	r2, #0
   200e8:	eb00dd05 	bl	57504 <__tsf_direct_jmp_cc_recording>
   200ec:	e49d2004 	pop	{r2}		; (ldr r2, [sp], #4)
   200f0:	e49d1004 	pop	{r1}		; (ldr r1, [sp], #4)
   200f4:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   200f8:	0a00000c 	beq	20130 <processSerial+0x130>
   200fc:	e59f005c 	ldr	r0, [pc, #92]	; 20160 <processSerial+0x160>
   20100:	e5941000 	ldr	r1, [r4]
   20104:	eb00013c 	bl	205fc <toUInt>
   20108:	ee000a10 	vmov	s0, r0
   2010c:	ed9f1b11 	vldr	d1, [pc, #68]	; 20158 <processSerial+0x158>
   20110:	eeb80ac0 	vcvt.f32.s32	s0, s0
   20114:	e58d0004 	str	r0, [sp, #4]
   20118:	eeb70ac0 	vcvt.f64.f32	d0, s0
   2011c:	ee800b01 	vdiv.f64	d0, d0, d1
   20120:	eeb78bc0 	vcvt.f32.f64	s16, d0
   20124:	e59f0044 	ldr	r0, [pc, #68]	; 20170 <processSerial+0x170>
   20128:	ed808a00 	vstr	s16, [r0]
   2012c:	eaffffd7 	b	20090 <processSerial+0x90>
   20130:	e59f0030 	ldr	r0, [pc, #48]	; 20168 <processSerial+0x168>
   20134:	e3a01012 	mov	r1, #18
   20138:	eb000112 	bl	20588 <Serial_write>
   2013c:	e59f001c 	ldr	r0, [pc, #28]	; 20160 <processSerial+0x160>
   20140:	e5941000 	ldr	r1, [r4]
   20144:	eb00010f 	bl	20588 <Serial_write>
   20148:	e59f001c 	ldr	r0, [pc, #28]	; 2016c <processSerial+0x16c>
   2014c:	e3a01002 	mov	r1, #2
   20150:	eb00010c 	bl	20588 <Serial_write>
   20154:	eaffffce 	b	20094 <processSerial+0x94>
   20158:	00000000 	andeq	r0, r0, r0
   2015c:	408f4000 	addmi	r4, pc, r0
   20160:	00057110 	andeq	r7, r5, r0, lsl r1
   20164:	00010d14 	andeq	r0, r1, r4, lsl sp
   20168:	000466a0 	andeq	r6, r4, r0, lsr #13
   2016c:	000466b3 			; <UNDEFINED> instruction: 0x000466b3
   20170:	00010d08 	andeq	r0, r1, r8, lsl #26
   20174:	00010d10 	andeq	r0, r1, r0, lsl sp

00020178 <bolus>:
   20178:	e92d4830 	push	{r4, r5, fp, lr}
   2017c:	e28db008 	add	fp, sp, #8
   20180:	ed2d8b02 	vpush	{d8}
   20184:	e24dd010 	sub	sp, sp, #16
   20188:	e59f51d4 	ldr	r5, [pc, #468]	; 20364 <bolus+0x1ec>
   2018c:	e58d000c 	str	r0, [sp, #12]
   20190:	e59f41d0 	ldr	r4, [pc, #464]	; 20368 <bolus+0x1f0>
   20194:	ed950a00 	vldr	s0, [r5]
   20198:	eeb80ac0 	vcvt.f32.s32	s0, s0
   2019c:	ed941a00 	vldr	s2, [r4]
   201a0:	ee210a00 	vmul.f32	s0, s2, s0
   201a4:	eebd0ac0 	vcvt.s32.f32	s0, s0
   201a8:	e59d000c 	ldr	r0, [sp, #12]
   201ac:	e3500000 	cmp	r0, #0
   201b0:	ed8d0a02 	vstr	s0, [sp, #8]
   201b4:	e3a08064 	mov	r8, #100	; 0x64
   201b8:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   201bc:	e52d1004 	push	{r1}		; (str r1, [sp, #-4]!)
   201c0:	e52d2004 	push	{r2}		; (str r2, [sp, #-4]!)
   201c4:	e10f1000 	mrs	r1, CPSR
   201c8:	e3a02000 	mov	r2, #0
   201cc:	eb00dccc 	bl	57504 <__tsf_direct_jmp_cc_recording>
   201d0:	e49d2004 	pop	{r2}		; (ldr r2, [sp], #4)
   201d4:	e49d1004 	pop	{r1}		; (ldr r1, [sp], #4)
   201d8:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   201dc:	0a000026 	beq	2027c <bolus+0x104>
   201e0:	e59d000c 	ldr	r0, [sp, #12]
   201e4:	e3500001 	cmp	r0, #1
   201e8:	e3a08064 	mov	r8, #100	; 0x64
   201ec:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   201f0:	e52d1004 	push	{r1}		; (str r1, [sp, #-4]!)
   201f4:	e52d2004 	push	{r2}		; (str r2, [sp, #-4]!)
   201f8:	e10f1000 	mrs	r1, CPSR
   201fc:	e3a02001 	mov	r2, #1
   20200:	eb00dcbf 	bl	57504 <__tsf_direct_jmp_cc_recording>
   20204:	e49d2004 	pop	{r2}		; (ldr r2, [sp], #4)
   20208:	e49d1004 	pop	{r1}		; (ldr r1, [sp], #4)
   2020c:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   20210:	1a00002c 	bne	202c8 <bolus+0x150>
   20214:	eb000115 	bl	20670 <led_off>
   20218:	e59f014c 	ldr	r0, [pc, #332]	; 2036c <bolus+0x1f4>
   2021c:	e3a01001 	mov	r1, #1
   20220:	e5900000 	ldr	r0, [r0]
   20224:	eb0000ce 	bl	20564 <digitalWrite>
   20228:	e59f5140 	ldr	r5, [pc, #320]	; 20370 <bolus+0x1f8>
   2022c:	ed940a00 	vldr	s0, [r4]
   20230:	ed951a00 	vldr	s2, [r5]
   20234:	ee310a40 	vsub.f32	s0, s2, s0
   20238:	eeb50ac0 	vcmpe.f32	s0, #0.0
   2023c:	eef1fa10 	vmrs	APSR_nzcv, fpscr
   20240:	e3a08064 	mov	r8, #100	; 0x64
   20244:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   20248:	e52d1004 	push	{r1}		; (str r1, [sp, #-4]!)
   2024c:	e52d2004 	push	{r2}		; (str r2, [sp, #-4]!)
   20250:	e10f1000 	mrs	r1, CPSR
   20254:	e3a0200d 	mov	r2, #13
   20258:	eb00dca9 	bl	57504 <__tsf_direct_jmp_cc_recording>
   2025c:	e49d2004 	pop	{r2}		; (ldr r2, [sp], #4)
   20260:	e49d1004 	pop	{r1}		; (ldr r1, [sp], #4)
   20264:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   20268:	da000014 	ble	202c0 <bolus+0x148>
   2026c:	ed940a00 	vldr	s0, [r4]
   20270:	ed951a00 	vldr	s2, [r5]
   20274:	ee318a40 	vsub.f32	s16, s2, s0
   20278:	ea00000e 	b	202b8 <bolus+0x140>
   2027c:	eb0000ea 	bl	2062c <led_on>
   20280:	e59f00e4 	ldr	r0, [pc, #228]	; 2036c <bolus+0x1f4>
   20284:	e3a01000 	mov	r1, #0
   20288:	e5900000 	ldr	r0, [r0]
   2028c:	eb0000b4 	bl	20564 <digitalWrite>
   20290:	ed950a00 	vldr	s0, [r5]
   20294:	e59f50d4 	ldr	r5, [pc, #212]	; 20370 <bolus+0x1f8>
   20298:	eeb80ac0 	vcvt.f32.s32	s0, s0
   2029c:	ed941a00 	vldr	s2, [r4]
   202a0:	ee210a00 	vmul.f32	s0, s2, s0
   202a4:	eebd0ac0 	vcvt.s32.f32	s0, s0
   202a8:	ed951a00 	vldr	s2, [r5]
   202ac:	ed8d0a02 	vstr	s0, [sp, #8]
   202b0:	ed940a00 	vldr	s0, [r4]
   202b4:	ee318a00 	vadd.f32	s16, s2, s0
   202b8:	ed858a00 	vstr	s16, [r5]
   202bc:	ea000001 	b	202c8 <bolus+0x150>
   202c0:	e3a00000 	mov	r0, #0
   202c4:	e5850000 	str	r0, [r5]
   202c8:	e59f40a4 	ldr	r4, [pc, #164]	; 20374 <bolus+0x1fc>
   202cc:	e3a007b2 	mov	r0, #46661632	; 0x2c80000
   202d0:	e3800101 	orr	r0, r0, #1073741824	; 0x40000000
   202d4:	e58d0004 	str	r0, [sp, #4]
   202d8:	e3a00000 	mov	r0, #0
   202dc:	e58d0000 	str	r0, [sp]
   202e0:	ea00000c 	b	20318 <bolus+0x1a0>
   202e4:	e5940000 	ldr	r0, [r4]
   202e8:	e3a01000 	mov	r1, #0
   202ec:	eb00009c 	bl	20564 <digitalWrite>
   202f0:	ed9d0a01 	vldr	s0, [sp, #4]
   202f4:	eb0000b5 	bl	205d0 <delayMicroseconds>
   202f8:	e5940000 	ldr	r0, [r4]
   202fc:	e3a01001 	mov	r1, #1
   20300:	eb000097 	bl	20564 <digitalWrite>
   20304:	ed9d0a01 	vldr	s0, [sp, #4]
   20308:	eb0000b0 	bl	205d0 <delayMicroseconds>
   2030c:	e59d0000 	ldr	r0, [sp]
   20310:	e2800001 	add	r0, r0, #1
   20314:	e58d0000 	str	r0, [sp]
   20318:	e59d0008 	ldr	r0, [sp, #8]
   2031c:	e59d1000 	ldr	r1, [sp]
   20320:	e1510000 	cmp	r1, r0
   20324:	e3a08064 	mov	r8, #100	; 0x64
   20328:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   2032c:	e52d1004 	push	{r1}		; (str r1, [sp, #-4]!)
   20330:	e52d2004 	push	{r2}		; (str r2, [sp, #-4]!)
   20334:	e10f1000 	mrs	r1, CPSR
   20338:	e3a0200b 	mov	r2, #11
   2033c:	eb00dc70 	bl	57504 <__tsf_direct_jmp_cc_recording>
   20340:	e49d2004 	pop	{r2}		; (ldr r2, [sp], #4)
   20344:	e49d1004 	pop	{r1}		; (ldr r1, [sp], #4)
   20348:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   2034c:	baffffe4 	blt	202e4 <bolus+0x16c>
   20350:	e24bd010 	sub	sp, fp, #16
   20354:	ecbd8b02 	vpop	{d8}
   20358:	e8bd0830 	pop	{r4, r5, fp}
   2035c:	e49d8004 	pop	{r8}		; (ldr r8, [sp], #4)
   20360:	eb00dc7d 	bl	5755c <__tsf_bkwd_pop_pc_recording>
   20364:	00020770 	andeq	r0, r2, r0, ror r7
   20368:	00010d08 	andeq	r0, r1, r8, lsl #26
   2036c:	00010d00 	andeq	r0, r1, r0, lsl #26
   20370:	000207b4 			; <UNDEFINED> instruction: 0x000207b4
   20374:	00010d04 	andeq	r0, r1, r4, lsl #26

00020378 <updateScreen>:
   20378:	e92d4c10 	push	{r4, sl, fp, lr}
   2037c:	e28db008 	add	fp, sp, #8
   20380:	ed2d8b04 	vpush	{d8-d9}
   20384:	e24dd0a8 	sub	sp, sp, #168	; 0xa8
   20388:	e59f01b0 	ldr	r0, [pc, #432]	; 20540 <updateScreen+0x1c8>
   2038c:	e3a01000 	mov	r1, #0
   20390:	e58d1004 	str	r1, [sp, #4]
   20394:	e58d1000 	str	r1, [sp]
   20398:	e5901000 	ldr	r1, [r0]
   2039c:	e3510000 	cmp	r1, #0
   203a0:	e3a08064 	mov	r8, #100	; 0x64
   203a4:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   203a8:	e52d1004 	push	{r1}		; (str r1, [sp, #-4]!)
   203ac:	e52d2004 	push	{r2}		; (str r2, [sp, #-4]!)
   203b0:	e10f1000 	mrs	r1, CPSR
   203b4:	e3a02000 	mov	r2, #0
   203b8:	eb00dc51 	bl	57504 <__tsf_direct_jmp_cc_recording>
   203bc:	e49d2004 	pop	{r2}		; (ldr r2, [sp], #4)
   203c0:	e49d1004 	pop	{r1}		; (ldr r1, [sp], #4)
   203c4:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   203c8:	0a00001d 	beq	20444 <updateScreen+0xcc>
   203cc:	e5900000 	ldr	r0, [r0]
   203d0:	e3500001 	cmp	r0, #1
   203d4:	e3a08064 	mov	r8, #100	; 0x64
   203d8:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   203dc:	e52d1004 	push	{r1}		; (str r1, [sp, #-4]!)
   203e0:	e52d2004 	push	{r2}		; (str r2, [sp, #-4]!)
   203e4:	e10f1000 	mrs	r1, CPSR
   203e8:	e3a02001 	mov	r2, #1
   203ec:	eb00dc44 	bl	57504 <__tsf_direct_jmp_cc_recording>
   203f0:	e49d2004 	pop	{r2}		; (ldr r2, [sp], #4)
   203f4:	e49d1004 	pop	{r1}		; (ldr r1, [sp], #4)
   203f8:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   203fc:	1a000032 	bne	204cc <updateScreen+0x154>
   20400:	e59f113c 	ldr	r1, [pc, #316]	; 20544 <updateScreen+0x1cc>
   20404:	e28d0058 	add	r0, sp, #88	; 0x58
   20408:	ebffc223 	bl	10c9c <sprintf@plt>
   2040c:	e59f1134 	ldr	r1, [pc, #308]	; 20548 <updateScreen+0x1d0>
   20410:	e58d0004 	str	r0, [sp, #4]
   20414:	ed9f1b45 	vldr	d1, [pc, #276]	; 20530 <updateScreen+0x1b8>
   20418:	ed910a00 	vldr	s0, [r1]
   2041c:	ed9f3b45 	vldr	d3, [pc, #276]	; 20538 <updateScreen+0x1c0>
   20420:	e59f1124 	ldr	r1, [pc, #292]	; 2054c <updateScreen+0x1d4>
   20424:	eeb72ac0 	vcvt.f64.f32	d2, s0
   20428:	eebd0ac0 	vcvt.s32.f32	s0, s0
   2042c:	ee222b01 	vmul.f64	d2, d2, d1
   20430:	ee102a10 	vmov	r2, s0
   20434:	eeb80bc0 	vcvt.f64.s32	d0, s0
   20438:	ee200b01 	vmul.f64	d0, d0, d1
   2043c:	ee321b03 	vadd.f64	d1, d2, d3
   20440:	ea00001b 	b	204b4 <updateScreen+0x13c>
   20444:	e59f0104 	ldr	r0, [pc, #260]	; 20550 <updateScreen+0x1d8>
   20448:	ed9f8b38 	vldr	d8, [pc, #224]	; 20530 <updateScreen+0x1b8>
   2044c:	ed9f9b39 	vldr	d9, [pc, #228]	; 20538 <updateScreen+0x1c0>
   20450:	ed900a00 	vldr	s0, [r0]
   20454:	e59f10f8 	ldr	r1, [pc, #248]	; 20554 <updateScreen+0x1dc>
   20458:	e28d0058 	add	r0, sp, #88	; 0x58
   2045c:	eeb71ac0 	vcvt.f64.f32	d1, s0
   20460:	eebd0ac0 	vcvt.s32.f32	s0, s0
   20464:	ee211b08 	vmul.f64	d1, d1, d8
   20468:	ee102a10 	vmov	r2, s0
   2046c:	eeb80bc0 	vcvt.f64.s32	d0, s0
   20470:	ee311b09 	vadd.f64	d1, d1, d9
   20474:	ee200b08 	vmul.f64	d0, d0, d8
   20478:	ee310b40 	vsub.f64	d0, d1, d0
   2047c:	eebd0bc0 	vcvt.s32.f64	s0, d0
   20480:	ee103a10 	vmov	r3, s0
   20484:	ebffc204 	bl	10c9c <sprintf@plt>
   20488:	e59f10c8 	ldr	r1, [pc, #200]	; 20558 <updateScreen+0x1e0>
   2048c:	e58d0004 	str	r0, [sp, #4]
   20490:	ed910a00 	vldr	s0, [r1]
   20494:	e59f10c0 	ldr	r1, [pc, #192]	; 2055c <updateScreen+0x1e4>
   20498:	eeb71ac0 	vcvt.f64.f32	d1, s0
   2049c:	eebd0ac0 	vcvt.s32.f32	s0, s0
   204a0:	ee211b08 	vmul.f64	d1, d1, d8
   204a4:	ee102a10 	vmov	r2, s0
   204a8:	eeb80bc0 	vcvt.f64.s32	d0, s0
   204ac:	ee311b09 	vadd.f64	d1, d1, d9
   204b0:	ee200b08 	vmul.f64	d0, d0, d8
   204b4:	ee310b40 	vsub.f64	d0, d1, d0
   204b8:	eebd0bc0 	vcvt.s32.f64	s0, d0
   204bc:	ee103a10 	vmov	r3, s0
   204c0:	e28d0008 	add	r0, sp, #8
   204c4:	ebffc1f4 	bl	10c9c <sprintf@plt>
   204c8:	e58d0000 	str	r0, [sp]
   204cc:	e59f408c 	ldr	r4, [pc, #140]	; 20560 <updateScreen+0x1e8>
   204d0:	e1a00004 	mov	r0, r4
   204d4:	eb00006f 	bl	20698 <lcd_clear>
   204d8:	e1a00004 	mov	r0, r4
   204dc:	e3a01000 	mov	r1, #0
   204e0:	e3a02000 	mov	r2, #0
   204e4:	eb00008d 	bl	20720 <lcd_setCursor>
   204e8:	e59d2004 	ldr	r2, [sp, #4]
   204ec:	e28d1058 	add	r1, sp, #88	; 0x58
   204f0:	e1a00004 	mov	r0, r4
   204f4:	eb000075 	bl	206d0 <lcd_print>
   204f8:	e1a00004 	mov	r0, r4
   204fc:	e3a01000 	mov	r1, #0
   20500:	e3a02001 	mov	r2, #1
   20504:	eb000085 	bl	20720 <lcd_setCursor>
   20508:	e59d2000 	ldr	r2, [sp]
   2050c:	e28d1008 	add	r1, sp, #8
   20510:	e1a00004 	mov	r0, r4
   20514:	eb00006d 	bl	206d0 <lcd_print>
   20518:	e24bd018 	sub	sp, fp, #24
   2051c:	ecbd8b04 	vpop	{d8-d9}
   20520:	e8bd0c10 	pop	{r4, sl, fp}
   20524:	e49d8004 	pop	{r8}		; (ldr r8, [sp], #4)
   20528:	eb00dc0b 	bl	5755c <__tsf_bkwd_pop_pc_recording>
   2052c:	e1a00000 	nop			; (mov r0, r0)
   20530:	00000000 	andeq	r0, r0, r0
   20534:	408f4000 	addmi	r4, pc, r0
   20538:	00000000 	andeq	r0, r0, r0
   2053c:	3fe00000 	svccc	0x00e00000
   20540:	0005710c 	andeq	r7, r5, ip, lsl #2
   20544:	000466d3 	ldrdeq	r6, [r4], -r3
   20548:	00010d0c 	andeq	r0, r1, ip, lsl #26
   2054c:	000466e3 	andeq	r6, r4, r3, ror #13
   20550:	000207b4 			; <UNDEFINED> instruction: 0x000207b4
   20554:	000466b6 			; <UNDEFINED> instruction: 0x000466b6
   20558:	00010d08 	andeq	r0, r1, r8, lsl #26
   2055c:	000466c4 	andeq	r6, r4, r4, asr #13
   20560:	00057d04 	andeq	r7, r5, r4, lsl #26

00020564 <digitalWrite>:
   20564:	e92d4800 	push	{fp, lr}
   20568:	e1a0b00d 	mov	fp, sp
   2056c:	e24dd008 	sub	sp, sp, #8
   20570:	e58d0004 	str	r0, [sp, #4]
   20574:	e58d1000 	str	r1, [sp]
   20578:	e1a0d00b 	mov	sp, fp
   2057c:	e8bd0800 	ldmfd	sp!, {fp}
   20580:	e49d8004 	pop	{r8}		; (ldr r8, [sp], #4)
   20584:	eb00dbf4 	bl	5755c <__tsf_bkwd_pop_pc_recording>

00020588 <Serial_write>:
   20588:	e92d4800 	push	{fp, lr}
   2058c:	e1a0b00d 	mov	fp, sp
   20590:	e24dd008 	sub	sp, sp, #8
   20594:	e58d0004 	str	r0, [sp, #4]
   20598:	e59fc028 	ldr	ip, [pc, #40]	; 205c8 <Serial_write+0x40>
   2059c:	e1a03001 	mov	r3, r1
   205a0:	e59f1024 	ldr	r1, [pc, #36]	; 205cc <Serial_write+0x44>
   205a4:	e59d2004 	ldr	r2, [sp, #4]
   205a8:	e1a0000c 	mov	r0, ip
   205ac:	e58d3000 	str	r3, [sp]
   205b0:	ebffc168 	bl	10b58 <printf@plt>
   205b4:	e3a00000 	mov	r0, #0
   205b8:	e1a0d00b 	mov	sp, fp
   205bc:	e8bd0800 	ldmfd	sp!, {fp}
   205c0:	e49d8004 	pop	{r8}		; (ldr r8, [sp], #4)
   205c4:	eb00dbe4 	bl	5755c <__tsf_bkwd_pop_pc_recording>
   205c8:	00046794 	muleq	r4, r4, r7
   205cc:	00020774 	andeq	r0, r2, r4, ror r7

000205d0 <delayMicroseconds>:
   205d0:	e92d4800 	push	{fp, lr}
   205d4:	e1a0b00d 	mov	fp, sp
   205d8:	e24dd008 	sub	sp, sp, #8
   205dc:	ed8d0a01 	vstr	s0, [sp, #4]
   205e0:	eebd0ac0 	vcvt.s32.f32	s0, s0
   205e4:	ee100a10 	vmov	r0, s0
   205e8:	ebffc172 	bl	10bb8 <usleep@plt>
   205ec:	e1a0d00b 	mov	sp, fp
   205f0:	e8bd0800 	ldmfd	sp!, {fp}
   205f4:	e49d8004 	pop	{r8}		; (ldr r8, [sp], #4)
   205f8:	eb00dbd7 	bl	5755c <__tsf_bkwd_pop_pc_recording>

000205fc <toUInt>:
   205fc:	e92d4800 	push	{fp, lr}
   20600:	e1a0b00d 	mov	fp, sp
   20604:	e24dd010 	sub	sp, sp, #16
   20608:	e50b0004 	str	r0, [fp, #-4]
   2060c:	e51b0004 	ldr	r0, [fp, #-4]
   20610:	e58d1008 	str	r1, [sp, #8]
   20614:	ebffc1ac 	bl	10ccc <atoi@plt>
   20618:	e58d0004 	str	r0, [sp, #4]
   2061c:	e1a0d00b 	mov	sp, fp
   20620:	e8bd0800 	ldmfd	sp!, {fp}
   20624:	e49d8004 	pop	{r8}		; (ldr r8, [sp], #4)
   20628:	eb00dbcb 	bl	5755c <__tsf_bkwd_pop_pc_recording>

0002062c <led_on>:
   2062c:	e92d48f0 	push	{r4, r5, r6, r7, fp, lr}
   20630:	e28db010 	add	fp, sp, #16
   20634:	e59f6028 	ldr	r6, [pc, #40]	; 20664 <led_on+0x38>
   20638:	e59f4028 	ldr	r4, [pc, #40]	; 20668 <led_on+0x3c>
   2063c:	e59f5028 	ldr	r5, [pc, #40]	; 2066c <led_on+0x40>
   20640:	e5960000 	ldr	r0, [r6]
   20644:	e2807001 	add	r7, r0, #1
   20648:	e1a00004 	mov	r0, r4
   2064c:	e1a01005 	mov	r1, r5
   20650:	e5867000 	str	r7, [r6]
   20654:	ebffc13f 	bl	10b58 <printf@plt>
   20658:	e8bd08f0 	pop	{r4, r5, r6, r7, fp}
   2065c:	e49d8004 	pop	{r8}		; (ldr r8, [sp], #4)
   20660:	eb00dbbd 	bl	5755c <__tsf_bkwd_pop_pc_recording>
   20664:	00010cfc 	strdeq	r0, [r1], -ip
   20668:	000467cc 	andeq	r6, r4, ip, asr #15
   2066c:	00020781 	andeq	r0, r2, r1, lsl #15

00020670 <led_off>:
   20670:	e92d4800 	push	{fp, lr}
   20674:	e1a0b00d 	mov	fp, sp
   20678:	e59f0010 	ldr	r0, [pc, #16]	; 20690 <led_off+0x20>
   2067c:	e59f1010 	ldr	r1, [pc, #16]	; 20694 <led_off+0x24>
   20680:	ebffc134 	bl	10b58 <printf@plt>
   20684:	e8bd0800 	ldmfd	sp!, {fp}
   20688:	e49d8004 	pop	{r8}		; (ldr r8, [sp], #4)
   2068c:	eb00dbb2 	bl	5755c <__tsf_bkwd_pop_pc_recording>
   20690:	000467cc 	andeq	r6, r4, ip, asr #15
   20694:	00020788 	andeq	r0, r2, r8, lsl #15

00020698 <lcd_clear>:
   20698:	e92d4800 	push	{fp, lr}
   2069c:	e1a0b00d 	mov	fp, sp
   206a0:	e24dd008 	sub	sp, sp, #8
   206a4:	e59f201c 	ldr	r2, [pc, #28]	; 206c8 <lcd_clear+0x30>
   206a8:	e59f101c 	ldr	r1, [pc, #28]	; 206cc <lcd_clear+0x34>
   206ac:	e58d0004 	str	r0, [sp, #4]
   206b0:	e1a00002 	mov	r0, r2
   206b4:	ebffc127 	bl	10b58 <printf@plt>
   206b8:	e1a0d00b 	mov	sp, fp
   206bc:	e8bd0800 	ldmfd	sp!, {fp}
   206c0:	e49d8004 	pop	{r8}		; (ldr r8, [sp], #4)
   206c4:	eb00dba4 	bl	5755c <__tsf_bkwd_pop_pc_recording>
   206c8:	00046821 	andeq	r6, r4, r1, lsr #16
   206cc:	00020790 	muleq	r2, r0, r7

000206d0 <lcd_print>:
   206d0:	e92d4800 	push	{fp, lr}
   206d4:	e1a0b00d 	mov	fp, sp
   206d8:	e24dd010 	sub	sp, sp, #16
   206dc:	e50b0004 	str	r0, [fp, #-4]
   206e0:	e58d1008 	str	r1, [sp, #8]
   206e4:	e59fc02c 	ldr	ip, [pc, #44]	; 20718 <lcd_print+0x48>
   206e8:	e51be004 	ldr	lr, [fp, #-4]
   206ec:	e59d3008 	ldr	r3, [sp, #8]
   206f0:	e59f1024 	ldr	r1, [pc, #36]	; 2071c <lcd_print+0x4c>
   206f4:	e58d2004 	str	r2, [sp, #4]
   206f8:	e58d2000 	str	r2, [sp]
   206fc:	e1a0000c 	mov	r0, ip
   20700:	e1a0200e 	mov	r2, lr
   20704:	ebffc113 	bl	10b58 <printf@plt>
   20708:	e1a0d00b 	mov	sp, fp
   2070c:	e8bd0800 	ldmfd	sp!, {fp}
   20710:	e49d8004 	pop	{r8}		; (ldr r8, [sp], #4)
   20714:	eb00db90 	bl	5755c <__tsf_bkwd_pop_pc_recording>
   20718:	00046841 	andeq	r6, r4, r1, asr #16
   2071c:	0002079a 	muleq	r2, sl, r7

00020720 <lcd_setCursor>:
   20720:	e92d4800 	push	{fp, lr}
   20724:	e1a0b00d 	mov	fp, sp
   20728:	e24dd010 	sub	sp, sp, #16
   2072c:	e59fe030 	ldr	lr, [pc, #48]	; 20764 <lcd_setCursor+0x44>
   20730:	e59fc030 	ldr	ip, [pc, #48]	; 20768 <lcd_setCursor+0x48>
   20734:	e58d1008 	str	r1, [sp, #8]
   20738:	e1a03002 	mov	r3, r2
   2073c:	e59d2008 	ldr	r2, [sp, #8]
   20740:	e50b0004 	str	r0, [fp, #-4]
   20744:	e1a0000e 	mov	r0, lr
   20748:	e1a0100c 	mov	r1, ip
   2074c:	e58d3004 	str	r3, [sp, #4]
   20750:	ebffc100 	bl	10b58 <printf@plt>
   20754:	e1a0d00b 	mov	sp, fp
   20758:	e8bd0800 	ldmfd	sp!, {fp}
   2075c:	e49d8004 	pop	{r8}		; (ldr r8, [sp], #4)
   20760:	eb00db7d 	bl	5755c <__tsf_bkwd_pop_pc_recording>
   20764:	00046883 	andeq	r6, r4, r3, lsl #17
   20768:	000207a4 	andeq	r0, r2, r4, lsr #15

Disassembly of section .DATA_REGION_1__share:

0002076c <.DATA_REGION_1__sdata_start>:
   2076c:	00000000 	andeq	r0, r0, r0

Disassembly of section .DATA_REGION_1__data:

00020770 <ustepsPerML>:
   20770:	00001aaa 	andeq	r1, r0, sl, lsr #21
   20774:	69726553 	ldmdbvs	r2!, {r0, r1, r4, r6, r8, sl, sp, lr}^
   20778:	775f6c61 	ldrbvc	r6, [pc, -r1, ror #24]
   2077c:	65746972 	ldrbvs	r6, [r4, #-2418]!	; 0xfffff68e
   20780:	64656c00 	strbtvs	r6, [r5], #-3072	; 0xfffff400
   20784:	006e6f5f 	rsbeq	r6, lr, pc, asr pc
   20788:	5f64656c 	svcpl	0x0064656c
   2078c:	0066666f 	rsbeq	r6, r6, pc, ror #12
   20790:	5f64636c 	svcpl	0x0064636c
   20794:	61656c63 	cmnvs	r5, r3, ror #24
   20798:	636c0072 	cmnvs	ip, #114	; 0x72
   2079c:	72705f64 	rsbsvc	r5, r0, #100, 30	; 0x190
   207a0:	00746e69 	rsbseq	r6, r4, r9, ror #28
   207a4:	5f64636c 	svcpl	0x0064636c
   207a8:	43746573 	cmnmi	r4, #482344960	; 0x1cc00000
   207ac:	6f737275 	svcvs	0x00737275
   207b0:	00000072 	andeq	r0, r0, r2, ror r0

Disassembly of section .DATA_REGION_1__bss:

000207b4 <mLUsed>:
   207b4:	00000000 	andeq	r0, r0, r0

Disassembly of section .CODE_REGION_2_:

00040000 <setup>:
   40000:	e92d4830 	push	{r4, r5, fp, lr}
   40004:	e28db008 	add	fp, sp, #8
   40008:	e59f40e0 	ldr	r4, [pc, #224]	; 400f0 <setup+0xf0>
   4000c:	e3a01010 	mov	r1, #16
   40010:	e3a02002 	mov	r2, #2
   40014:	e1a00004 	mov	r0, r4
   40018:	eb00026f 	bl	409dc <lcd_begin>
   4001c:	e1a00004 	mov	r0, r4
   40020:	e3008698 	movw	r8, #1688	; 0x698
   40024:	e3408002 	movt	r8, #2
   40028:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   4002c:	eb005d25 	bl	574c8 <__tsf_direct_jmp_link_recording>
   40030:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   40034:	ebff8197 	bl	20698 <lcd_clear>
   40038:	e59f10b4 	ldr	r1, [pc, #180]	; 400f4 <setup+0xf4>
   4003c:	e1a00004 	mov	r0, r4
   40040:	e3a02010 	mov	r2, #16
   40044:	e30086d0 	movw	r8, #1744	; 0x6d0
   40048:	e3408002 	movt	r8, #2
   4004c:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   40050:	eb005d1c 	bl	574c8 <__tsf_direct_jmp_link_recording>
   40054:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   40058:	ebff819c 	bl	206d0 <lcd_print>
   4005c:	e59f4094 	ldr	r4, [pc, #148]	; 400f8 <setup+0xf8>
   40060:	e3a01000 	mov	r1, #0
   40064:	e5940000 	ldr	r0, [r4]
   40068:	eb0001e8 	bl	40810 <pinMode>
   4006c:	e59f5088 	ldr	r5, [pc, #136]	; 400fc <setup+0xfc>
   40070:	e3a01000 	mov	r1, #0
   40074:	e5950000 	ldr	r0, [r5]
   40078:	eb0001e4 	bl	40810 <pinMode>
   4007c:	e5944000 	ldr	r4, [r4]
   40080:	e1a00004 	mov	r0, r4
   40084:	e3a01000 	mov	r1, #0
   40088:	e3008564 	movw	r8, #1380	; 0x564
   4008c:	e3408002 	movt	r8, #2
   40090:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   40094:	eb005d0b 	bl	574c8 <__tsf_direct_jmp_link_recording>
   40098:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   4009c:	ebff8130 	bl	20564 <digitalWrite>
   400a0:	e5954000 	ldr	r4, [r5]
   400a4:	e1a00004 	mov	r0, r4
   400a8:	e3a01000 	mov	r1, #0
   400ac:	e3008564 	movw	r8, #1380	; 0x564
   400b0:	e3408002 	movt	r8, #2
   400b4:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   400b8:	eb005d02 	bl	574c8 <__tsf_direct_jmp_link_recording>
   400bc:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   400c0:	ebff8127 	bl	20564 <digitalWrite>
   400c4:	e59f0034 	ldr	r0, [pc, #52]	; 40100 <setup+0x100>
   400c8:	e3a01001 	mov	r1, #1
   400cc:	e5900000 	ldr	r0, [r0]
   400d0:	eb0001ce 	bl	40810 <pinMode>
   400d4:	e59f0028 	ldr	r0, [pc, #40]	; 40104 <setup+0x104>
   400d8:	e3a01001 	mov	r1, #1
   400dc:	e5900000 	ldr	r0, [r0]
   400e0:	eb0001ca 	bl	40810 <pinMode>
   400e4:	e3a00ce1 	mov	r0, #57600	; 0xe100
   400e8:	eb0001e8 	bl	40890 <Serial_begin>
   400ec:	e8bd8830 	pop	{r4, r5, fp, pc}
   400f0:	00057d04 	andeq	r7, r5, r4, lsl #26
   400f4:	00046670 	andeq	r6, r4, r0, ror r6
   400f8:	00040ac8 	andeq	r0, r4, r8, asr #21
   400fc:	00040acc 	andeq	r0, r4, ip, asr #21
   40100:	00010d00 	andeq	r0, r1, r0, lsl #26
   40104:	00010d04 	andeq	r0, r1, r4, lsl #26

00040108 <loop>:
   40108:	e92d4830 	push	{r4, r5, fp, lr}
   4010c:	e28db008 	add	fp, sp, #8
   40110:	ed2d8b02 	vpush	{d8}
   40114:	e24dd010 	sub	sp, sp, #16
   40118:	ee000a10 	vmov	s0, r0
   4011c:	ed9f1b25 	vldr	d1, [pc, #148]	; 401b8 <loop+0xb0>
   40120:	eeb80bc0 	vcvt.f64.s32	d0, s0
   40124:	e58d000c 	str	r0, [sp, #12]
   40128:	ee200b01 	vmul.f64	d0, d0, d1
   4012c:	eeb78bc0 	vcvt.f32.f64	s16, d0
   40130:	e59f008c 	ldr	r0, [pc, #140]	; 401c4 <loop+0xbc>
   40134:	e59f4084 	ldr	r4, [pc, #132]	; 401c0 <loop+0xb8>
   40138:	e3a0102b 	mov	r1, #43	; 0x2b
   4013c:	ed848a00 	vstr	s16, [r4]
   40140:	e5c01000 	strb	r1, [r0]
   40144:	e59f507c 	ldr	r5, [pc, #124]	; 401c8 <loop+0xc0>
   40148:	e3a00001 	mov	r0, #1
   4014c:	e5c50000 	strb	r0, [r5]
   40150:	eb000215 	bl	409ac <usecs>
   40154:	e58d0008 	str	r0, [sp, #8]
   40158:	e5d50000 	ldrb	r0, [r5]
   4015c:	e3100001 	tst	r0, #1
   40160:	0a000005 	beq	4017c <loop+0x74>
   40164:	e3008000 	movw	r8, #0
   40168:	e3408002 	movt	r8, #2
   4016c:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   40170:	eb005cd4 	bl	574c8 <__tsf_direct_jmp_link_recording>
   40174:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   40178:	ebff7fa0 	bl	20000 <processSerial>
   4017c:	eb00020a 	bl	409ac <usecs>
   40180:	ed940a00 	vldr	s0, [r4]
   40184:	e59d5008 	ldr	r5, [sp, #8]
   40188:	e59f103c 	ldr	r1, [pc, #60]	; 401cc <loop+0xc4>
   4018c:	e58d0004 	str	r0, [sp, #4]
   40190:	eeb70ac0 	vcvt.f64.f32	d0, s0
   40194:	e0400005 	sub	r0, r0, r5
   40198:	e58d0000 	str	r0, [sp]
   4019c:	e1a00001 	mov	r0, r1
   401a0:	ec532b10 	vmov	r2, r3, d0
   401a4:	ebff426b 	bl	10b58 <printf@plt>
   401a8:	e24bd010 	sub	sp, fp, #16
   401ac:	ecbd8b02 	vpop	{d8}
   401b0:	e8bd8830 	pop	{r4, r5, fp, pc}
   401b4:	e1a00000 	nop			; (mov r0, r0)
   401b8:	d2f1a9fc 	rscsle	sl, r1, #252, 18	; 0x3f0000
   401bc:	3f50624d 	svccc	0x0050624d
   401c0:	00010d08 	andeq	r0, r1, r8, lsl #26
   401c4:	00057110 	andeq	r7, r5, r0, lsl r1
   401c8:	00010d10 	andeq	r0, r1, r0, lsl sp
   401cc:	00046681 	andeq	r6, r4, r1, lsl #13

000401d0 <checkTriggers>:
   401d0:	e92d4c10 	push	{r4, sl, fp, lr}
   401d4:	e28db008 	add	fp, sp, #8
   401d8:	ed2d8b02 	vpush	{d8}
   401dc:	e24dd010 	sub	sp, sp, #16
   401e0:	e59f010c 	ldr	r0, [pc, #268]	; 402f4 <checkTriggers+0x124>
   401e4:	e5900000 	ldr	r0, [r0]
   401e8:	eb000197 	bl	4084c <digitalRead>
   401ec:	e58d000c 	str	r0, [sp, #12]
   401f0:	e3500000 	cmp	r0, #0
   401f4:	1a000010 	bne	4023c <checkTriggers+0x6c>
   401f8:	e59f00f8 	ldr	r0, [pc, #248]	; 402f8 <checkTriggers+0x128>
   401fc:	e5900000 	ldr	r0, [r0]
   40200:	e3500001 	cmp	r0, #1
   40204:	1a00000c 	bne	4023c <checkTriggers+0x6c>
   40208:	e3a00000 	mov	r0, #0
   4020c:	e3008178 	movw	r8, #376	; 0x178
   40210:	e3408002 	movt	r8, #2
   40214:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   40218:	eb005caa 	bl	574c8 <__tsf_direct_jmp_link_recording>
   4021c:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   40220:	ebff7fd4 	bl	20178 <bolus>
   40224:	e3008378 	movw	r8, #888	; 0x378
   40228:	e3408002 	movt	r8, #2
   4022c:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   40230:	eb005ca4 	bl	574c8 <__tsf_direct_jmp_link_recording>
   40234:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   40238:	ebff804e 	bl	20378 <updateScreen>
   4023c:	e59d400c 	ldr	r4, [sp, #12]
   40240:	e59f00b0 	ldr	r0, [pc, #176]	; 402f8 <checkTriggers+0x128>
   40244:	e59f10b0 	ldr	r1, [pc, #176]	; 402fc <checkTriggers+0x12c>
   40248:	e3008000 	movw	r8, #0
   4024c:	e3408000 	movt	r8, #0
   40250:	e7d78010 	bfi	r8, r0, #0, #24
   40254:	e5884000 	str	r4, [r8]
   40258:	e5910000 	ldr	r0, [r1]
   4025c:	eb00017a 	bl	4084c <digitalRead>
   40260:	e58d0008 	str	r0, [sp, #8]
   40264:	e3500000 	cmp	r0, #0
   40268:	1a000018 	bne	402d0 <checkTriggers+0x100>
   4026c:	e59f008c 	ldr	r0, [pc, #140]	; 40300 <checkTriggers+0x130>
   40270:	e5900000 	ldr	r0, [r0]
   40274:	e3500001 	cmp	r0, #1
   40278:	1a000014 	bne	402d0 <checkTriggers+0x100>
   4027c:	e59f4080 	ldr	r4, [pc, #128]	; 40304 <checkTriggers+0x134>
   40280:	e59f1080 	ldr	r1, [pc, #128]	; 40308 <checkTriggers+0x138>
   40284:	e5940000 	ldr	r0, [r4]
   40288:	ed918a00 	vldr	s16, [r1]
   4028c:	e58d0004 	str	r0, [sp, #4]
   40290:	ed848a00 	vstr	s16, [r4]
   40294:	e3a00000 	mov	r0, #0
   40298:	e3008178 	movw	r8, #376	; 0x178
   4029c:	e3408002 	movt	r8, #2
   402a0:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   402a4:	eb005c87 	bl	574c8 <__tsf_direct_jmp_link_recording>
   402a8:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   402ac:	ebff7fb1 	bl	20178 <bolus>
   402b0:	ed9d8a01 	vldr	s16, [sp, #4]
   402b4:	ed848a00 	vstr	s16, [r4]
   402b8:	e3008378 	movw	r8, #888	; 0x378
   402bc:	e3408002 	movt	r8, #2
   402c0:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   402c4:	eb005c7f 	bl	574c8 <__tsf_direct_jmp_link_recording>
   402c8:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   402cc:	ebff8029 	bl	20378 <updateScreen>
   402d0:	e59d4008 	ldr	r4, [sp, #8]
   402d4:	e59f0024 	ldr	r0, [pc, #36]	; 40300 <checkTriggers+0x130>
   402d8:	e3008000 	movw	r8, #0
   402dc:	e3408000 	movt	r8, #0
   402e0:	e7d78010 	bfi	r8, r0, #0, #24
   402e4:	e5884000 	str	r4, [r8]
   402e8:	e24bd010 	sub	sp, fp, #16
   402ec:	ecbd8b02 	vpop	{d8}
   402f0:	e8bd8c10 	pop	{r4, sl, fp, pc}
   402f4:	00040ac8 	andeq	r0, r4, r8, asr #21
   402f8:	00040ad8 	ldrdeq	r0, [r4], -r8
   402fc:	00040acc 	andeq	r0, r4, ip, asr #21
   40300:	00040ad4 	ldrdeq	r0, [r4], -r4
   40304:	00010d08 	andeq	r0, r1, r8, lsl #26
   40308:	00040a78 	andeq	r0, r4, r8, ror sl

0004030c <readSerial>:
   4030c:	e92d4ef0 	push	{r4, r5, r6, r7, r9, sl, fp, lr}
   40310:	e28db018 	add	fp, sp, #24
   40314:	e24dd008 	sub	sp, sp, #8
   40318:	e59f905c 	ldr	r9, [pc, #92]	; 4037c <readSerial+0x70>
   4031c:	e59f6050 	ldr	r6, [pc, #80]	; 40374 <readSerial+0x68>
   40320:	e59f7050 	ldr	r7, [pc, #80]	; 40378 <readSerial+0x6c>
   40324:	e3a05001 	mov	r5, #1
   40328:	ea000005 	b	40344 <readSerial+0x38>
   4032c:	e5961000 	ldr	r1, [r6]
   40330:	e5dd0007 	ldrb	r0, [sp, #7]
   40334:	e7c70001 	strb	r0, [r7, r1]
   40338:	e5960000 	ldr	r0, [r6]
   4033c:	e2804001 	add	r4, r0, #1
   40340:	e5864000 	str	r4, [r6]
   40344:	eb00015d 	bl	408c0 <Serial_available>
   40348:	e3500000 	cmp	r0, #0
   4034c:	0a000006 	beq	4036c <readSerial+0x60>
   40350:	eb00016e 	bl	40910 <Serial_read>
   40354:	e5cd0007 	strb	r0, [sp, #7]
   40358:	e5dd0007 	ldrb	r0, [sp, #7]
   4035c:	e350001f 	cmp	r0, #31
   40360:	cafffff1 	bgt	4032c <readSerial+0x20>
   40364:	e5c95000 	strb	r5, [r9]
   40368:	eafffff5 	b	40344 <readSerial+0x38>
   4036c:	e24bd018 	sub	sp, fp, #24
   40370:	e8bd8ef0 	pop	{r4, r5, r6, r7, r9, sl, fp, pc}
   40374:	00010d14 	andeq	r0, r1, r4, lsl sp
   40378:	00057110 	andeq	r7, r5, r0, lsl r1
   4037c:	00010d10 	andeq	r0, r1, r0, lsl sp

00040380 <readKey>:
   40380:	e92d48f0 	push	{r4, r5, r6, r7, fp, lr}
   40384:	e28db010 	add	fp, sp, #16
   40388:	e24dd010 	sub	sp, sp, #16
   4038c:	e3a00000 	mov	r0, #0
   40390:	e3a07000 	mov	r7, #0
   40394:	eb000165 	bl	40930 <analogRead>
   40398:	e1a04000 	mov	r4, r0
   4039c:	e59f00ec 	ldr	r0, [pc, #236]	; 40490 <readKey+0x110>
   403a0:	e3008000 	movw	r8, #0
   403a4:	e3408000 	movt	r8, #0
   403a8:	e7d78010 	bfi	r8, r0, #0, #24
   403ac:	e5884000 	str	r4, [r8]
   403b0:	e1a00004 	mov	r0, r4
   403b4:	eb00003b 	bl	404a8 <get_key>
   403b8:	e1a04000 	mov	r4, r0
   403bc:	e59f50d0 	ldr	r5, [pc, #208]	; 40494 <readKey+0x114>
   403c0:	e3008000 	movw	r8, #0
   403c4:	e3408000 	movt	r8, #0
   403c8:	e7d78015 	bfi	r8, r5, #0, #24
   403cc:	e5884000 	str	r4, [r8]
   403d0:	eb000165 	bl	4096c <millis>
   403d4:	e59f40bc 	ldr	r4, [pc, #188]	; 40498 <readKey+0x118>
   403d8:	e59f60bc 	ldr	r6, [pc, #188]	; 4049c <readKey+0x11c>
   403dc:	e58d000c 	str	r0, [sp, #12]
   403e0:	e5cd7007 	strb	r7, [sp, #7]
   403e4:	e5941000 	ldr	r1, [r4]
   403e8:	e0400001 	sub	r0, r0, r1
   403ec:	e58d0008 	str	r0, [sp, #8]
   403f0:	e5950000 	ldr	r0, [r5]
   403f4:	e5961000 	ldr	r1, [r6]
   403f8:	e1510000 	cmp	r1, r0
   403fc:	1a000005 	bne	40418 <readKey+0x98>
   40400:	e59f0098 	ldr	r0, [pc, #152]	; 404a0 <readKey+0x120>
   40404:	e59d1008 	ldr	r1, [sp, #8]
   40408:	e5900000 	ldr	r0, [r0]
   4040c:	e1510000 	cmp	r1, r0
   40410:	c3a00001 	movgt	r0, #1
   40414:	c5cd0007 	strbgt	r0, [sp, #7]
   40418:	e5960000 	ldr	r0, [r6]
   4041c:	e3500005 	cmp	r0, #5
   40420:	1a000005 	bne	4043c <readKey+0xbc>
   40424:	e59f0078 	ldr	r0, [pc, #120]	; 404a4 <readKey+0x124>
   40428:	e59d1008 	ldr	r1, [sp, #8]
   4042c:	e5900000 	ldr	r0, [r0]
   40430:	e1510000 	cmp	r1, r0
   40434:	c3a00001 	movgt	r0, #1
   40438:	c5cd0007 	strbgt	r0, [sp, #7]
   4043c:	e5950000 	ldr	r0, [r5]
   40440:	e5957000 	ldr	r7, [r5]
   40444:	e3500005 	cmp	r0, #5
   40448:	03a00000 	moveq	r0, #0
   4044c:	05cd0007 	strbeq	r0, [sp, #7]
   40450:	e5dd0007 	ldrb	r0, [sp, #7]
   40454:	e3008000 	movw	r8, #0
   40458:	e3408000 	movt	r8, #0
   4045c:	e7d78016 	bfi	r8, r6, #0, #24
   40460:	e5887000 	str	r7, [r8]
   40464:	e3100001 	tst	r0, #1
   40468:	0a000006 	beq	40488 <readKey+0x108>
   4046c:	e5950000 	ldr	r0, [r5]
   40470:	eb00002c 	bl	40528 <doKeyAction>
   40474:	e59d500c 	ldr	r5, [sp, #12]
   40478:	e3008000 	movw	r8, #0
   4047c:	e3408000 	movt	r8, #0
   40480:	e7d78014 	bfi	r8, r4, #0, #24
   40484:	e5885000 	str	r5, [r8]
   40488:	e24bd010 	sub	sp, fp, #16
   4048c:	e8bd88f0 	pop	{r4, r5, r6, r7, fp, pc}
   40490:	00057d00 	andeq	r7, r5, r0, lsl #26
   40494:	00040a50 	andeq	r0, r4, r0, asr sl
   40498:	00040ad0 	ldrdeq	r0, [r4], -r0	; <UNPREDICTABLE>
   4049c:	00040a88 	andeq	r0, r4, r8, lsl #21
   404a0:	00040a80 	andeq	r0, r4, r0, lsl #21
   404a4:	00040a84 	andeq	r0, r4, r4, lsl #21

000404a8 <get_key>:
   404a8:	e24dd00c 	sub	sp, sp, #12
   404ac:	e58d0004 	str	r0, [sp, #4]
   404b0:	e3a00000 	mov	r0, #0
   404b4:	e58d0000 	str	r0, [sp]
   404b8:	e59f0060 	ldr	r0, [pc, #96]	; 40520 <get_key+0x78>
   404bc:	e59f1060 	ldr	r1, [pc, #96]	; 40524 <get_key+0x7c>
   404c0:	ea000002 	b	404d0 <get_key+0x28>
   404c4:	e59d2000 	ldr	r2, [sp]
   404c8:	e2822001 	add	r2, r2, #1
   404cc:	e58d2000 	str	r2, [sp]
   404d0:	e59d2000 	ldr	r2, [sp]
   404d4:	e5903000 	ldr	r3, [r0]
   404d8:	e1520003 	cmp	r2, r3
   404dc:	aa000005 	bge	404f8 <get_key+0x50>
   404e0:	e59d2000 	ldr	r2, [sp]
   404e4:	e59d3004 	ldr	r3, [sp, #4]
   404e8:	e7912102 	ldr	r2, [r1, r2, lsl #2]
   404ec:	e1530002 	cmp	r3, r2
   404f0:	2afffff3 	bcs	404c4 <get_key+0x1c>
   404f4:	ea000004 	b	4050c <get_key+0x64>
   404f8:	e59d1000 	ldr	r1, [sp]
   404fc:	e5900000 	ldr	r0, [r0]
   40500:	e1510000 	cmp	r1, r0
   40504:	a3a00005 	movge	r0, #5
   40508:	a58d0000 	strge	r0, [sp]
   4050c:	e59d0000 	ldr	r0, [sp]
   40510:	e58d0008 	str	r0, [sp, #8]
   40514:	e59d0008 	ldr	r0, [sp, #8]
   40518:	e28dd00c 	add	sp, sp, #12
   4051c:	e12fff1e 	bx	lr
   40520:	00040a4c 	andeq	r0, r4, ip, asr #20
   40524:	00040a38 	andeq	r0, r4, r8, lsr sl

00040528 <doKeyAction>:
   40528:	e92d4c70 	push	{r4, r5, r6, sl, fp, lr}
   4052c:	e28db010 	add	fp, sp, #16
   40530:	ed2d8b02 	vpush	{d8}
   40534:	e24dd008 	sub	sp, sp, #8
   40538:	e58d0004 	str	r0, [sp, #4]
   4053c:	e3500005 	cmp	r0, #5
   40540:	0a00006e 	beq	40700 <doKeyAction+0x1d8>
   40544:	e59d0004 	ldr	r0, [sp, #4]
   40548:	e3500004 	cmp	r0, #4
   4054c:	1a00000a 	bne	4057c <doKeyAction+0x54>
   40550:	e59f41b4 	ldr	r4, [pc, #436]	; 4070c <doKeyAction+0x1e4>
   40554:	e5940000 	ldr	r0, [r4]
   40558:	e3500000 	cmp	r0, #0
   4055c:	0a000001 	beq	40568 <doKeyAction+0x40>
   40560:	e3a00000 	mov	r0, #0
   40564:	ea000000 	b	4056c <doKeyAction+0x44>
   40568:	e3a00001 	mov	r0, #1
   4056c:	e3008000 	movw	r8, #0
   40570:	e3408000 	movt	r8, #0
   40574:	e7d78014 	bfi	r8, r4, #0, #24
   40578:	e5880000 	str	r0, [r8]
   4057c:	e59f0188 	ldr	r0, [pc, #392]	; 4070c <doKeyAction+0x1e4>
   40580:	e5901000 	ldr	r1, [r0]
   40584:	e3510000 	cmp	r1, #0
   40588:	0a000027 	beq	4062c <doKeyAction+0x104>
   4058c:	e5900000 	ldr	r0, [r0]
   40590:	e3500001 	cmp	r0, #1
   40594:	1a000053 	bne	406e8 <doKeyAction+0x1c0>
   40598:	e59d0004 	ldr	r0, [sp, #4]
   4059c:	e3500001 	cmp	r0, #1
   405a0:	1a00000e 	bne	405e0 <doKeyAction+0xb8>
   405a4:	e59f4164 	ldr	r4, [pc, #356]	; 40710 <doKeyAction+0x1e8>
   405a8:	e5940000 	ldr	r0, [r4]
   405ac:	e3500007 	cmp	r0, #7
   405b0:	ca00000a 	bgt	405e0 <doKeyAction+0xb8>
   405b4:	e5940000 	ldr	r0, [r4]
   405b8:	e59f1154 	ldr	r1, [pc, #340]	; 40714 <doKeyAction+0x1ec>
   405bc:	e2805001 	add	r5, r0, #1
   405c0:	e0816105 	add	r6, r1, r5, lsl #2
   405c4:	e3008000 	movw	r8, #0
   405c8:	e3408000 	movt	r8, #0
   405cc:	e7d78014 	bfi	r8, r4, #0, #24
   405d0:	e5885000 	str	r5, [r8]
   405d4:	ed968a00 	vldr	s16, [r6]
   405d8:	e59f0138 	ldr	r0, [pc, #312]	; 40718 <doKeyAction+0x1f0>
   405dc:	ed808a00 	vstr	s16, [r0]
   405e0:	e59d0004 	ldr	r0, [sp, #4]
   405e4:	e3500002 	cmp	r0, #2
   405e8:	1a00003e 	bne	406e8 <doKeyAction+0x1c0>
   405ec:	e59f411c 	ldr	r4, [pc, #284]	; 40710 <doKeyAction+0x1e8>
   405f0:	e5940000 	ldr	r0, [r4]
   405f4:	e3500001 	cmp	r0, #1
   405f8:	ba00003a 	blt	406e8 <doKeyAction+0x1c0>
   405fc:	e5940000 	ldr	r0, [r4]
   40600:	e59f110c 	ldr	r1, [pc, #268]	; 40714 <doKeyAction+0x1ec>
   40604:	e2405001 	sub	r5, r0, #1
   40608:	e0816105 	add	r6, r1, r5, lsl #2
   4060c:	e3008000 	movw	r8, #0
   40610:	e3408000 	movt	r8, #0
   40614:	e7d78014 	bfi	r8, r4, #0, #24
   40618:	e5885000 	str	r5, [r8]
   4061c:	ed968a00 	vldr	s16, [r6]
   40620:	e59f00f0 	ldr	r0, [pc, #240]	; 40718 <doKeyAction+0x1f0>
   40624:	ed808a00 	vstr	s16, [r0]
   40628:	ea00002e 	b	406e8 <doKeyAction+0x1c0>
   4062c:	e59d0004 	ldr	r0, [sp, #4]
   40630:	e3500003 	cmp	r0, #3
   40634:	1a000006 	bne	40654 <doKeyAction+0x12c>
   40638:	e3a00001 	mov	r0, #1
   4063c:	e3008178 	movw	r8, #376	; 0x178
   40640:	e3408002 	movt	r8, #2
   40644:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   40648:	eb005b9e 	bl	574c8 <__tsf_direct_jmp_link_recording>
   4064c:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   40650:	ebff7ec8 	bl	20178 <bolus>
   40654:	e59d0004 	ldr	r0, [sp, #4]
   40658:	e3500000 	cmp	r0, #0
   4065c:	1a000006 	bne	4067c <doKeyAction+0x154>
   40660:	e3a00000 	mov	r0, #0
   40664:	e3008178 	movw	r8, #376	; 0x178
   40668:	e3408002 	movt	r8, #2
   4066c:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   40670:	eb005b94 	bl	574c8 <__tsf_direct_jmp_link_recording>
   40674:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   40678:	ebff7ebe 	bl	20178 <bolus>
   4067c:	e59d0004 	ldr	r0, [sp, #4]
   40680:	e3500001 	cmp	r0, #1
   40684:	1a000005 	bne	406a0 <doKeyAction+0x178>
   40688:	e59f0088 	ldr	r0, [pc, #136]	; 40718 <doKeyAction+0x1f0>
   4068c:	e59f4088 	ldr	r4, [pc, #136]	; 4071c <doKeyAction+0x1f4>
   40690:	ed900a00 	vldr	s0, [r0]
   40694:	ed941a00 	vldr	s2, [r4]
   40698:	ee318a00 	vadd.f32	s16, s2, s0
   4069c:	ed848a00 	vstr	s16, [r4]
   406a0:	e59d0004 	ldr	r0, [sp, #4]
   406a4:	e3500002 	cmp	r0, #2
   406a8:	1a00000e 	bne	406e8 <doKeyAction+0x1c0>
   406ac:	e59f0064 	ldr	r0, [pc, #100]	; 40718 <doKeyAction+0x1f0>
   406b0:	e59f4064 	ldr	r4, [pc, #100]	; 4071c <doKeyAction+0x1f4>
   406b4:	ed900a00 	vldr	s0, [r0]
   406b8:	ed941a00 	vldr	s2, [r4]
   406bc:	ee310a40 	vsub.f32	s0, s2, s0
   406c0:	eeb50ac0 	vcmpe.f32	s0, #0.0
   406c4:	eef1fa10 	vmrs	APSR_nzcv, fpscr
   406c8:	da000004 	ble	406e0 <doKeyAction+0x1b8>
   406cc:	ed900a00 	vldr	s0, [r0]
   406d0:	ed941a00 	vldr	s2, [r4]
   406d4:	ee318a40 	vsub.f32	s16, s2, s0
   406d8:	ed848a00 	vstr	s16, [r4]
   406dc:	ea000001 	b	406e8 <doKeyAction+0x1c0>
   406e0:	e3a00000 	mov	r0, #0
   406e4:	e5840000 	str	r0, [r4]
   406e8:	e3008378 	movw	r8, #888	; 0x378
   406ec:	e3408002 	movt	r8, #2
   406f0:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   406f4:	eb005b73 	bl	574c8 <__tsf_direct_jmp_link_recording>
   406f8:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   406fc:	ebff7f1d 	bl	20378 <updateScreen>
   40700:	e24bd018 	sub	sp, fp, #24
   40704:	ecbd8b02 	vpop	{d8}
   40708:	e8bd8c70 	pop	{r4, r5, r6, sl, fp, pc}
   4070c:	0005710c 	andeq	r7, r5, ip, lsl #2
   40710:	00040a7c 	andeq	r0, r4, ip, ror sl
   40714:	00040a54 	andeq	r0, r4, r4, asr sl
   40718:	00010d0c 	andeq	r0, r1, ip, lsl #26
   4071c:	00010d08 	andeq	r0, r1, r8, lsl #26

00040720 <forward_target>:
   40720:	e92d4800 	push	{fp, lr}
   40724:	e1a0b00d 	mov	fp, sp
   40728:	e24dd008 	sub	sp, sp, #8
   4072c:	e59f1010 	ldr	r1, [pc, #16]	; 40744 <forward_target+0x24>
   40730:	e58d0004 	str	r0, [sp, #4]
   40734:	e1a00001 	mov	r0, r1
   40738:	ebff4106 	bl	10b58 <printf@plt>
   4073c:	e1a0d00b 	mov	sp, fp
   40740:	e8bd8800 	pop	{fp, pc}
   40744:	000466e9 	andeq	r6, r4, r9, ror #13

00040748 <main>:
   40748:	e92d4800 	push	{fp, lr}
   4074c:	e1a0b00d 	mov	fp, sp
   40750:	e24dd018 	sub	sp, sp, #24
   40754:	e59f209c 	ldr	r2, [pc, #156]	; 407f8 <main+0xb0>
   40758:	e3a03000 	mov	r3, #0
   4075c:	e90b0009 	stmdb	fp, {r0, r3}
   40760:	e1a00002 	mov	r0, r2
   40764:	e58d100c 	str	r1, [sp, #12]
   40768:	ebff40fa 	bl	10b58 <printf@plt>
   4076c:	e59f0088 	ldr	r0, [pc, #136]	; 407fc <main+0xb4>
   40770:	ebff40f8 	bl	10b58 <printf@plt>
   40774:	fa001247 	blx	45098 <start_new_thread>
   40778:	ebfffe20 	bl	40000 <setup>
   4077c:	e59f107c 	ldr	r1, [pc, #124]	; 40800 <main+0xb8>
   40780:	e3a00002 	mov	r0, #2
   40784:	e58d1008 	str	r1, [sp, #8]
   40788:	e1a08001 	mov	r8, r1
   4078c:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   40790:	eb005b64 	bl	57528 <__tsf_indirect_jmp_link_recording>
   40794:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   40798:	e59f3064 	ldr	r3, [pc, #100]	; 40804 <main+0xbc>
   4079c:	e59f0064 	ldr	r0, [pc, #100]	; 40808 <main+0xc0>
   407a0:	e3a01010 	mov	r1, #16
   407a4:	e3a02002 	mov	r2, #2
   407a8:	e58d3004 	str	r3, [sp, #4]
   407ac:	e3008000 	movw	r8, #0
   407b0:	e3408000 	movt	r8, #0
   407b4:	e7d78013 	bfi	r8, r3, #0, #24
   407b8:	e12fff38 	blx	r8
   407bc:	e3a00001 	mov	r0, #1
   407c0:	e58d0000 	str	r0, [sp]
   407c4:	ea000003 	b	407d8 <main+0x90>
   407c8:	e59d0000 	ldr	r0, [sp]
   407cc:	e280000a 	add	r0, r0, #10
   407d0:	e58d0000 	str	r0, [sp]
   407d4:	ebfffe4b 	bl	40108 <loop>
   407d8:	e59d0000 	ldr	r0, [sp]
   407dc:	e350003d 	cmp	r0, #61	; 0x3d
   407e0:	dafffff8 	ble	407c8 <main+0x80>
   407e4:	e59f0020 	ldr	r0, [pc, #32]	; 4080c <main+0xc4>
   407e8:	ebff40da 	bl	10b58 <printf@plt>
   407ec:	e3a00000 	mov	r0, #0
   407f0:	e1a0d00b 	mov	sp, fp
   407f4:	e8bd8800 	pop	{fp, pc}
   407f8:	00046704 	andeq	r6, r4, r4, lsl #14
   407fc:	0004671b 	andeq	r6, r4, fp, lsl r7
   40800:	00040720 	andeq	r0, r4, r0, lsr #14
   40804:	000409dc 	ldrdeq	r0, [r4], -ip
   40808:	00057d04 	andeq	r7, r5, r4, lsl #26
   4080c:	0004672b 	andeq	r6, r4, fp, lsr #14

00040810 <pinMode>:
   40810:	e92d4800 	push	{fp, lr}
   40814:	e1a0b00d 	mov	fp, sp
   40818:	e24dd008 	sub	sp, sp, #8
   4081c:	e58d0004 	str	r0, [sp, #4]
   40820:	e59fc01c 	ldr	ip, [pc, #28]	; 40844 <pinMode+0x34>
   40824:	e1a03001 	mov	r3, r1
   40828:	e59f1018 	ldr	r1, [pc, #24]	; 40848 <pinMode+0x38>
   4082c:	e59d2004 	ldr	r2, [sp, #4]
   40830:	e1a0000c 	mov	r0, ip
   40834:	e58d3000 	str	r3, [sp]
   40838:	ebff40c6 	bl	10b58 <printf@plt>
   4083c:	e1a0d00b 	mov	sp, fp
   40840:	e8bd8800 	pop	{fp, pc}
   40844:	00046740 	andeq	r6, r4, r0, asr #14
   40848:	00040a8c 	andeq	r0, r4, ip, lsl #21

0004084c <digitalRead>:
   4084c:	e92d4800 	push	{fp, lr}
   40850:	e1a0b00d 	mov	fp, sp
   40854:	e24dd008 	sub	sp, sp, #8
   40858:	e1a02000 	mov	r2, r0
   4085c:	e59f0020 	ldr	r0, [pc, #32]	; 40884 <digitalRead+0x38>
   40860:	e59f1020 	ldr	r1, [pc, #32]	; 40888 <digitalRead+0x3c>
   40864:	e58d2004 	str	r2, [sp, #4]
   40868:	ebff40ba 	bl	10b58 <printf@plt>
   4086c:	e59f0018 	ldr	r0, [pc, #24]	; 4088c <digitalRead+0x40>
   40870:	e1a0100d 	mov	r1, sp
   40874:	ebff410b 	bl	10ca8 <__isoc99_scanf@plt>
   40878:	e59d0000 	ldr	r0, [sp]
   4087c:	e1a0d00b 	mov	sp, fp
   40880:	e8bd8800 	pop	{fp, pc}
   40884:	00046762 	andeq	r6, r4, r2, ror #14
   40888:	00040a94 	muleq	r4, r4, sl
   4088c:	000466e6 	andeq	r6, r4, r6, ror #13

00040890 <Serial_begin>:
   40890:	e92d4800 	push	{fp, lr}
   40894:	e1a0b00d 	mov	fp, sp
   40898:	e24dd008 	sub	sp, sp, #8
   4089c:	e1a02000 	mov	r2, r0
   408a0:	e59f0010 	ldr	r0, [pc, #16]	; 408b8 <Serial_begin+0x28>
   408a4:	e59f1010 	ldr	r1, [pc, #16]	; 408bc <Serial_begin+0x2c>
   408a8:	e58d2004 	str	r2, [sp, #4]
   408ac:	ebff40a9 	bl	10b58 <printf@plt>
   408b0:	e1a0d00b 	mov	sp, fp
   408b4:	e8bd8800 	pop	{fp, pc}
   408b8:	00046775 	andeq	r6, r4, r5, ror r7
   408bc:	00040aa0 	andeq	r0, r4, r0, lsr #21

000408c0 <Serial_available>:
   408c0:	e92d4800 	push	{fp, lr}
   408c4:	e1a0b00d 	mov	fp, sp
   408c8:	e24dd008 	sub	sp, sp, #8
   408cc:	ebff40b3 	bl	10ba0 <getchar@plt>
   408d0:	e5cd0003 	strb	r0, [sp, #3]
   408d4:	e59f302c 	ldr	r3, [pc, #44]	; 40908 <Serial_available+0x48>
   408d8:	e59f102c 	ldr	r1, [pc, #44]	; 4090c <Serial_available+0x4c>
   408dc:	e5dd2003 	ldrb	r2, [sp, #3]
   408e0:	e1a00003 	mov	r0, r3
   408e4:	ebff409b 	bl	10b58 <printf@plt>
   408e8:	e5dd0003 	ldrb	r0, [sp, #3]
   408ec:	e3500079 	cmp	r0, #121	; 0x79
   408f0:	13a00000 	movne	r0, #0
   408f4:	03a00001 	moveq	r0, #1
   408f8:	e58d0004 	str	r0, [sp, #4]
   408fc:	e59d0004 	ldr	r0, [sp, #4]
   40900:	e1a0d00b 	mov	sp, fp
   40904:	e8bd8800 	pop	{fp, pc}
   40908:	00046789 	andeq	r6, r4, r9, lsl #15
   4090c:	00040aad 	andeq	r0, r4, sp, lsr #21

00040910 <Serial_read>:
   40910:	e92d4800 	push	{fp, lr}
   40914:	e1a0b00d 	mov	fp, sp
   40918:	e24dd008 	sub	sp, sp, #8
   4091c:	ebff409f 	bl	10ba0 <getchar@plt>
   40920:	e54b0001 	strb	r0, [fp, #-1]
   40924:	e55b0001 	ldrb	r0, [fp, #-1]
   40928:	e1a0d00b 	mov	sp, fp
   4092c:	e8bd8800 	pop	{fp, pc}

00040930 <analogRead>:
   40930:	e92d4800 	push	{fp, lr}
   40934:	e1a0b00d 	mov	fp, sp
   40938:	e24dd008 	sub	sp, sp, #8
   4093c:	e1a01000 	mov	r1, r0
   40940:	e59f001c 	ldr	r0, [pc, #28]	; 40964 <analogRead+0x34>
   40944:	e58d1004 	str	r1, [sp, #4]
   40948:	ebff4082 	bl	10b58 <printf@plt>
   4094c:	e59f0014 	ldr	r0, [pc, #20]	; 40968 <analogRead+0x38>
   40950:	e1a0100d 	mov	r1, sp
   40954:	ebff40d3 	bl	10ca8 <__isoc99_scanf@plt>
   40958:	e59d0000 	ldr	r0, [sp]
   4095c:	e1a0d00b 	mov	sp, fp
   40960:	e8bd8800 	pop	{fp, pc}
   40964:	000467ba 			; <UNDEFINED> instruction: 0x000467ba
   40968:	000466e6 	andeq	r6, r4, r6, ror #13

0004096c <millis>:
   4096c:	e92d4800 	push	{fp, lr}
   40970:	e1a0b00d 	mov	fp, sp
   40974:	e24dd008 	sub	sp, sp, #8
   40978:	e1a0000d 	mov	r0, sp
   4097c:	e3a01000 	mov	r1, #0
   40980:	ebff408f 	bl	10bc4 <gettimeofday@plt>
   40984:	e59f001c 	ldr	r0, [pc, #28]	; 409a8 <millis+0x3c>
   40988:	e89d0006 	ldm	sp, {r1, r2}
   4098c:	e750f012 	smmul	r0, r2, r0
   40990:	e1a02340 	asr	r2, r0, #6
   40994:	e0820fa0 	add	r0, r2, r0, lsr #31
   40998:	e3a02ffa 	mov	r2, #1000	; 0x3e8
   4099c:	e0200291 	mla	r0, r1, r2, r0
   409a0:	e1a0d00b 	mov	sp, fp
   409a4:	e8bd8800 	pop	{fp, pc}
   409a8:	10624dd3 	ldrdne	r4, [r2], #-211	; 0xffffff2d	; <UNPREDICTABLE>

000409ac <usecs>:
   409ac:	e92d4800 	push	{fp, lr}
   409b0:	e1a0b00d 	mov	fp, sp
   409b4:	e24dd008 	sub	sp, sp, #8
   409b8:	e1a0000d 	mov	r0, sp
   409bc:	e3a01000 	mov	r1, #0
   409c0:	ebff407f 	bl	10bc4 <gettimeofday@plt>
   409c4:	e3a02d09 	mov	r2, #576	; 0x240
   409c8:	e89d0003 	ldm	sp, {r0, r1}
   409cc:	e382293d 	orr	r2, r2, #999424	; 0xf4000
   409d0:	e0201290 	mla	r0, r0, r2, r1
   409d4:	e1a0d00b 	mov	sp, fp
   409d8:	e8bd8800 	pop	{fp, pc}

000409dc <lcd_begin>:
   409dc:	e92d4c70 	push	{r4, r5, r6, sl, fp, lr}
   409e0:	e28db010 	add	fp, sp, #16
   409e4:	e24dd010 	sub	sp, sp, #16
   409e8:	e59f5038 	ldr	r5, [pc, #56]	; 40a28 <lcd_begin+0x4c>
   409ec:	e58d000c 	str	r0, [sp, #12]
   409f0:	e58d1008 	str	r1, [sp, #8]
   409f4:	e58d2004 	str	r2, [sp, #4]
   409f8:	e5950000 	ldr	r0, [r5]
   409fc:	e59f4028 	ldr	r4, [pc, #40]	; 40a2c <lcd_begin+0x50>
   40a00:	e2806001 	add	r6, r0, #1
   40a04:	e5856000 	str	r6, [r5]
   40a08:	e59d200c 	ldr	r2, [sp, #12]
   40a0c:	e99d0009 	ldmib	sp, {r0, r3}
   40a10:	e59f1018 	ldr	r1, [pc, #24]	; 40a30 <lcd_begin+0x54>
   40a14:	e58d0000 	str	r0, [sp]
   40a18:	e1a00004 	mov	r0, r4
   40a1c:	ebff404d 	bl	10b58 <printf@plt>
   40a20:	e24bd010 	sub	sp, fp, #16
   40a24:	e8bd8c70 	pop	{r4, r5, r6, sl, fp, pc}
   40a28:	00010cfc 	strdeq	r0, [r1], -ip
   40a2c:	000467d0 	ldrdeq	r6, [r4], -r0
   40a30:	00040abe 			; <UNDEFINED> instruction: 0x00040abe

Disassembly of section .DATA_REGION_2__share:

00040a34 <.DATA_REGION_2__sdata_start>:
   40a34:	00000000 	andeq	r0, r0, r0

Disassembly of section .DATA_REGION_2__data:

00040a38 <adc_key_val>:
   40a38:	0000001e 	andeq	r0, r0, lr, lsl r0
   40a3c:	00000096 	muleq	r0, r6, r0
   40a40:	00000168 	andeq	r0, r0, r8, ror #2
   40a44:	00000217 	andeq	r0, r0, r7, lsl r2
   40a48:	000002f8 	strdeq	r0, [r0], -r8

00040a4c <NUM_KEYS>:
   40a4c:	00000005 	andeq	r0, r0, r5

00040a50 <key>:
   40a50:	00000005 	andeq	r0, r0, r5

00040a54 <mLBolusSteps>:
   40a54:	3a83126f 	bcc	fe105418 <__bss_end__+0xf4816e14>
   40a58:	3ba3d70a 	blcc	fe936688 <__bss_end__+0xf5048084>
   40a5c:	3c23d70a 	stccc	7, cr13, [r3], #-40	; 0xffffffd8
   40a60:	3d4ccccd 	stclcc	12, cr12, [ip, #-820]	; 0xfffffccc
   40a64:	3dcccccd 	stclcc	12, cr12, [ip, #820]	; 0x334
   40a68:	3f000000 	svccc	0x00000000
   40a6c:	3f800000 	svccc	0x00800000
   40a70:	40a00000 	adcmi	r0, r0, r0
   40a74:	41200000 			; <UNDEFINED> instruction: 0x41200000

00040a78 <mLBigBolus>:
   40a78:	3f800000 	svccc	0x00800000

00040a7c <mLBolusStepIdx>:
   40a7c:	00000003 	andeq	r0, r0, r3

00040a80 <keyRepeatDelay>:
   40a80:	00000190 	muleq	r0, r0, r1

00040a84 <keyDebounce>:
   40a84:	0000007d 	andeq	r0, r0, sp, ror r0

00040a88 <prevKey>:
   40a88:	00000005 	andeq	r0, r0, r5
   40a8c:	4d6e6970 			; <UNDEFINED> instruction: 0x4d6e6970
   40a90:	0065646f 	rsbeq	r6, r5, pc, ror #8
   40a94:	69676964 	stmdbvs	r7!, {r2, r5, r6, r8, fp, sp, lr}^
   40a98:	526c6174 	rsbpl	r6, ip, #116, 2
   40a9c:	00646165 	rsbeq	r6, r4, r5, ror #2
   40aa0:	69726553 	ldmdbvs	r2!, {r0, r1, r4, r6, r8, sl, sp, lr}^
   40aa4:	625f6c61 	subsvs	r6, pc, #24832	; 0x6100
   40aa8:	6e696765 	cdpvs	7, 6, cr6, cr9, cr5, {3}
   40aac:	72655300 	rsbvc	r5, r5, #0, 6
   40ab0:	5f6c6169 	svcpl	0x006c6169
   40ab4:	69617661 	stmdbvs	r1!, {r0, r5, r6, r9, sl, ip, sp, lr}^
   40ab8:	6c62616c 	stfvse	f6, [r2], #-432	; 0xfffffe50
   40abc:	636c0065 	cmnvs	ip, #101	; 0x65
   40ac0:	65625f64 	strbvs	r5, [r2, #-3940]!	; 0xfffff09c
   40ac4:	006e6967 	rsbeq	r6, lr, r7, ror #18

Disassembly of section .DATA_REGION_2__bss:

00040ac8 <triggerPin>:
   40ac8:	00000000 	andeq	r0, r0, r0

00040acc <bigTriggerPin>:
   40acc:	00000000 	andeq	r0, r0, r0

00040ad0 <lastKeyRepeatAt>:
   40ad0:	00000000 	andeq	r0, r0, r0

00040ad4 <prevBigTrigger>:
   40ad4:	00000000 	andeq	r0, r0, r0

00040ad8 <prevTrigger>:
   40ad8:	00000000 	andeq	r0, r0, r0

Disassembly of section .text:

00040adc <load32>:
   40adc:	b480      	push	{r7}
   40ade:	b085      	sub	sp, #20
   40ae0:	af00      	add	r7, sp, #0
   40ae2:	6078      	str	r0, [r7, #4]
   40ae4:	687b      	ldr	r3, [r7, #4]
   40ae6:	60fb      	str	r3, [r7, #12]
   40ae8:	68fb      	ldr	r3, [r7, #12]
   40aea:	781b      	ldrb	r3, [r3, #0]
   40aec:	461a      	mov	r2, r3
   40aee:	68fb      	ldr	r3, [r7, #12]
   40af0:	3301      	adds	r3, #1
   40af2:	781b      	ldrb	r3, [r3, #0]
   40af4:	021b      	lsls	r3, r3, #8
   40af6:	431a      	orrs	r2, r3
   40af8:	68fb      	ldr	r3, [r7, #12]
   40afa:	3302      	adds	r3, #2
   40afc:	781b      	ldrb	r3, [r3, #0]
   40afe:	041b      	lsls	r3, r3, #16
   40b00:	431a      	orrs	r2, r3
   40b02:	68fb      	ldr	r3, [r7, #12]
   40b04:	3303      	adds	r3, #3
   40b06:	781b      	ldrb	r3, [r3, #0]
   40b08:	061b      	lsls	r3, r3, #24
   40b0a:	4313      	orrs	r3, r2
   40b0c:	4618      	mov	r0, r3
   40b0e:	3714      	adds	r7, #20
   40b10:	46bd      	mov	sp, r7
   40b12:	f85d 7b04 	ldr.w	r7, [sp], #4
   40b16:	4770      	bx	lr

00040b18 <store16>:
   40b18:	b480      	push	{r7}
   40b1a:	b085      	sub	sp, #20
   40b1c:	af00      	add	r7, sp, #0
   40b1e:	6078      	str	r0, [r7, #4]
   40b20:	460b      	mov	r3, r1
   40b22:	807b      	strh	r3, [r7, #2]
   40b24:	687b      	ldr	r3, [r7, #4]
   40b26:	60fb      	str	r3, [r7, #12]
   40b28:	68fb      	ldr	r3, [r7, #12]
   40b2a:	1c5a      	adds	r2, r3, #1
   40b2c:	60fa      	str	r2, [r7, #12]
   40b2e:	887a      	ldrh	r2, [r7, #2]
   40b30:	b2d2      	uxtb	r2, r2
   40b32:	701a      	strb	r2, [r3, #0]
   40b34:	887b      	ldrh	r3, [r7, #2]
   40b36:	0a1b      	lsrs	r3, r3, #8
   40b38:	807b      	strh	r3, [r7, #2]
   40b3a:	68fb      	ldr	r3, [r7, #12]
   40b3c:	1c5a      	adds	r2, r3, #1
   40b3e:	60fa      	str	r2, [r7, #12]
   40b40:	887a      	ldrh	r2, [r7, #2]
   40b42:	b2d2      	uxtb	r2, r2
   40b44:	701a      	strb	r2, [r3, #0]
   40b46:	bf00      	nop
   40b48:	3714      	adds	r7, #20
   40b4a:	46bd      	mov	sp, r7
   40b4c:	f85d 7b04 	ldr.w	r7, [sp], #4
   40b50:	4770      	bx	lr

00040b52 <store32>:
   40b52:	b480      	push	{r7}
   40b54:	b085      	sub	sp, #20
   40b56:	af00      	add	r7, sp, #0
   40b58:	6078      	str	r0, [r7, #4]
   40b5a:	6039      	str	r1, [r7, #0]
   40b5c:	687b      	ldr	r3, [r7, #4]
   40b5e:	60fb      	str	r3, [r7, #12]
   40b60:	683b      	ldr	r3, [r7, #0]
   40b62:	b2da      	uxtb	r2, r3
   40b64:	68fb      	ldr	r3, [r7, #12]
   40b66:	701a      	strb	r2, [r3, #0]
   40b68:	68fb      	ldr	r3, [r7, #12]
   40b6a:	3301      	adds	r3, #1
   40b6c:	683a      	ldr	r2, [r7, #0]
   40b6e:	0a12      	lsrs	r2, r2, #8
   40b70:	b2d2      	uxtb	r2, r2
   40b72:	701a      	strb	r2, [r3, #0]
   40b74:	68fb      	ldr	r3, [r7, #12]
   40b76:	3302      	adds	r3, #2
   40b78:	683a      	ldr	r2, [r7, #0]
   40b7a:	0c12      	lsrs	r2, r2, #16
   40b7c:	b2d2      	uxtb	r2, r2
   40b7e:	701a      	strb	r2, [r3, #0]
   40b80:	68fb      	ldr	r3, [r7, #12]
   40b82:	3303      	adds	r3, #3
   40b84:	683a      	ldr	r2, [r7, #0]
   40b86:	0e12      	lsrs	r2, r2, #24
   40b88:	b2d2      	uxtb	r2, r2
   40b8a:	701a      	strb	r2, [r3, #0]
   40b8c:	bf00      	nop
   40b8e:	3714      	adds	r7, #20
   40b90:	46bd      	mov	sp, r7
   40b92:	f85d 7b04 	ldr.w	r7, [sp], #4
   40b96:	4770      	bx	lr

00040b98 <rotr32>:
   40b98:	b480      	push	{r7}
   40b9a:	b083      	sub	sp, #12
   40b9c:	af00      	add	r7, sp, #0
   40b9e:	6078      	str	r0, [r7, #4]
   40ba0:	6039      	str	r1, [r7, #0]
   40ba2:	687a      	ldr	r2, [r7, #4]
   40ba4:	683b      	ldr	r3, [r7, #0]
   40ba6:	fa62 f303 	ror.w	r3, r2, r3
   40baa:	4618      	mov	r0, r3
   40bac:	370c      	adds	r7, #12
   40bae:	46bd      	mov	sp, r7
   40bb0:	f85d 7b04 	ldr.w	r7, [sp], #4
   40bb4:	4770      	bx	lr

00040bb6 <secure_zero_memory>:
   40bb6:	b580      	push	{r7, lr}
   40bb8:	b082      	sub	sp, #8
   40bba:	af00      	add	r7, sp, #0
   40bbc:	6078      	str	r0, [r7, #4]
   40bbe:	6039      	str	r1, [r7, #0]
   40bc0:	4b05      	ldr	r3, [pc, #20]	; (40bd8 <secure_zero_memory+0x22>)
   40bc2:	447b      	add	r3, pc
   40bc4:	681b      	ldr	r3, [r3, #0]
   40bc6:	683a      	ldr	r2, [r7, #0]
   40bc8:	2100      	movs	r1, #0
   40bca:	6878      	ldr	r0, [r7, #4]
   40bcc:	4798      	blx	r3
   40bce:	bf00      	nop
   40bd0:	3708      	adds	r7, #8
   40bd2:	46bd      	mov	sp, r7
   40bd4:	bd80      	pop	{r7, pc}
   40bd6:	bf00      	nop
   40bd8:	0001652a 	andeq	r6, r1, sl, lsr #10

00040bdc <blake2s_set_lastnode>:
   40bdc:	b480      	push	{r7}
   40bde:	b083      	sub	sp, #12
   40be0:	af00      	add	r7, sp, #0
   40be2:	6078      	str	r0, [r7, #4]
   40be4:	687b      	ldr	r3, [r7, #4]
   40be6:	f04f 32ff 	mov.w	r2, #4294967295	; 0xffffffff
   40bea:	62da      	str	r2, [r3, #44]	; 0x2c
   40bec:	bf00      	nop
   40bee:	370c      	adds	r7, #12
   40bf0:	46bd      	mov	sp, r7
   40bf2:	f85d 7b04 	ldr.w	r7, [sp], #4
   40bf6:	4770      	bx	lr

00040bf8 <blake2s_is_lastblock>:
   40bf8:	b480      	push	{r7}
   40bfa:	b083      	sub	sp, #12
   40bfc:	af00      	add	r7, sp, #0
   40bfe:	6078      	str	r0, [r7, #4]
   40c00:	687b      	ldr	r3, [r7, #4]
   40c02:	6a9b      	ldr	r3, [r3, #40]	; 0x28
   40c04:	2b00      	cmp	r3, #0
   40c06:	bf14      	ite	ne
   40c08:	2301      	movne	r3, #1
   40c0a:	2300      	moveq	r3, #0
   40c0c:	b2db      	uxtb	r3, r3
   40c0e:	4618      	mov	r0, r3
   40c10:	370c      	adds	r7, #12
   40c12:	46bd      	mov	sp, r7
   40c14:	f85d 7b04 	ldr.w	r7, [sp], #4
   40c18:	4770      	bx	lr

00040c1a <blake2s_set_lastblock>:
   40c1a:	b580      	push	{r7, lr}
   40c1c:	b082      	sub	sp, #8
   40c1e:	af00      	add	r7, sp, #0
   40c20:	6078      	str	r0, [r7, #4]
   40c22:	687b      	ldr	r3, [r7, #4]
   40c24:	f893 3078 	ldrb.w	r3, [r3, #120]	; 0x78
   40c28:	2b00      	cmp	r3, #0
   40c2a:	d002      	beq.n	40c32 <blake2s_set_lastblock+0x18>
   40c2c:	6878      	ldr	r0, [r7, #4]
   40c2e:	f7ff ffd5 	bl	40bdc <blake2s_set_lastnode>
   40c32:	687b      	ldr	r3, [r7, #4]
   40c34:	f04f 32ff 	mov.w	r2, #4294967295	; 0xffffffff
   40c38:	629a      	str	r2, [r3, #40]	; 0x28
   40c3a:	bf00      	nop
   40c3c:	3708      	adds	r7, #8
   40c3e:	46bd      	mov	sp, r7
   40c40:	bd80      	pop	{r7, pc}

00040c42 <blake2s_increment_counter>:
   40c42:	b480      	push	{r7}
   40c44:	b083      	sub	sp, #12
   40c46:	af00      	add	r7, sp, #0
   40c48:	6078      	str	r0, [r7, #4]
   40c4a:	6039      	str	r1, [r7, #0]
   40c4c:	687b      	ldr	r3, [r7, #4]
   40c4e:	6a1a      	ldr	r2, [r3, #32]
   40c50:	683b      	ldr	r3, [r7, #0]
   40c52:	441a      	add	r2, r3
   40c54:	687b      	ldr	r3, [r7, #4]
   40c56:	621a      	str	r2, [r3, #32]
   40c58:	687b      	ldr	r3, [r7, #4]
   40c5a:	6a5b      	ldr	r3, [r3, #36]	; 0x24
   40c5c:	687a      	ldr	r2, [r7, #4]
   40c5e:	6a11      	ldr	r1, [r2, #32]
   40c60:	683a      	ldr	r2, [r7, #0]
   40c62:	4291      	cmp	r1, r2
   40c64:	bf34      	ite	cc
   40c66:	2201      	movcc	r2, #1
   40c68:	2200      	movcs	r2, #0
   40c6a:	b2d2      	uxtb	r2, r2
   40c6c:	441a      	add	r2, r3
   40c6e:	687b      	ldr	r3, [r7, #4]
   40c70:	625a      	str	r2, [r3, #36]	; 0x24
   40c72:	bf00      	nop
   40c74:	370c      	adds	r7, #12
   40c76:	46bd      	mov	sp, r7
   40c78:	f85d 7b04 	ldr.w	r7, [sp], #4
   40c7c:	4770      	bx	lr

00040c7e <blake2s_init0>:
   40c7e:	b580      	push	{r7, lr}
   40c80:	b084      	sub	sp, #16
   40c82:	af00      	add	r7, sp, #0
   40c84:	6078      	str	r0, [r7, #4]
   40c86:	227c      	movs	r2, #124	; 0x7c
   40c88:	2100      	movs	r1, #0
   40c8a:	6878      	ldr	r0, [r7, #4]
   40c8c:	f7cf efe8 	blx	10c60 <memset@plt>
   40c90:	2300      	movs	r3, #0
   40c92:	60fb      	str	r3, [r7, #12]
   40c94:	e00c      	b.n	40cb0 <blake2s_init0+0x32>
   40c96:	4b0a      	ldr	r3, [pc, #40]	; (40cc0 <blake2s_init0+0x42>)
   40c98:	447b      	add	r3, pc
   40c9a:	461a      	mov	r2, r3
   40c9c:	68fb      	ldr	r3, [r7, #12]
   40c9e:	f852 1023 	ldr.w	r1, [r2, r3, lsl #2]
   40ca2:	687b      	ldr	r3, [r7, #4]
   40ca4:	68fa      	ldr	r2, [r7, #12]
   40ca6:	f843 1022 	str.w	r1, [r3, r2, lsl #2]
   40caa:	68fb      	ldr	r3, [r7, #12]
   40cac:	3301      	adds	r3, #1
   40cae:	60fb      	str	r3, [r7, #12]
   40cb0:	68fb      	ldr	r3, [r7, #12]
   40cb2:	2b07      	cmp	r3, #7
   40cb4:	d9ef      	bls.n	40c96 <blake2s_init0+0x18>
   40cb6:	bf00      	nop
   40cb8:	3710      	adds	r7, #16
   40cba:	46bd      	mov	sp, r7
   40cbc:	bd80      	pop	{r7, pc}
   40cbe:	bf00      	nop
   40cc0:	00005c20 	andeq	r5, r0, r0, lsr #24

00040cc4 <blake2s_init_param>:
   40cc4:	b580      	push	{r7, lr}
   40cc6:	b084      	sub	sp, #16
   40cc8:	af00      	add	r7, sp, #0
   40cca:	6078      	str	r0, [r7, #4]
   40ccc:	6039      	str	r1, [r7, #0]
   40cce:	683b      	ldr	r3, [r7, #0]
   40cd0:	60bb      	str	r3, [r7, #8]
   40cd2:	6878      	ldr	r0, [r7, #4]
   40cd4:	f7ff ffd3 	bl	40c7e <blake2s_init0>
   40cd8:	2300      	movs	r3, #0
   40cda:	60fb      	str	r3, [r7, #12]
   40cdc:	e013      	b.n	40d06 <blake2s_init_param+0x42>
   40cde:	68fb      	ldr	r3, [r7, #12]
   40ce0:	009b      	lsls	r3, r3, #2
   40ce2:	68ba      	ldr	r2, [r7, #8]
   40ce4:	4413      	add	r3, r2
   40ce6:	4618      	mov	r0, r3
   40ce8:	f7ff fef8 	bl	40adc <load32>
   40cec:	4601      	mov	r1, r0
   40cee:	687b      	ldr	r3, [r7, #4]
   40cf0:	68fa      	ldr	r2, [r7, #12]
   40cf2:	f853 3022 	ldr.w	r3, [r3, r2, lsl #2]
   40cf6:	4059      	eors	r1, r3
   40cf8:	687b      	ldr	r3, [r7, #4]
   40cfa:	68fa      	ldr	r2, [r7, #12]
   40cfc:	f843 1022 	str.w	r1, [r3, r2, lsl #2]
   40d00:	68fb      	ldr	r3, [r7, #12]
   40d02:	3301      	adds	r3, #1
   40d04:	60fb      	str	r3, [r7, #12]
   40d06:	68fb      	ldr	r3, [r7, #12]
   40d08:	2b07      	cmp	r3, #7
   40d0a:	d9e8      	bls.n	40cde <blake2s_init_param+0x1a>
   40d0c:	683b      	ldr	r3, [r7, #0]
   40d0e:	781b      	ldrb	r3, [r3, #0]
   40d10:	461a      	mov	r2, r3
   40d12:	687b      	ldr	r3, [r7, #4]
   40d14:	675a      	str	r2, [r3, #116]	; 0x74
   40d16:	2300      	movs	r3, #0
   40d18:	4618      	mov	r0, r3
   40d1a:	3710      	adds	r7, #16
   40d1c:	46bd      	mov	sp, r7
   40d1e:	bd80      	pop	{r7, pc}

00040d20 <blake2s_init>:
   40d20:	b580      	push	{r7, lr}
   40d22:	b08a      	sub	sp, #40	; 0x28
   40d24:	af00      	add	r7, sp, #0
   40d26:	6078      	str	r0, [r7, #4]
   40d28:	6039      	str	r1, [r7, #0]
   40d2a:	683b      	ldr	r3, [r7, #0]
   40d2c:	2b00      	cmp	r3, #0
   40d2e:	d002      	beq.n	40d36 <blake2s_init+0x16>
   40d30:	683b      	ldr	r3, [r7, #0]
   40d32:	2b20      	cmp	r3, #32
   40d34:	d902      	bls.n	40d3c <blake2s_init+0x1c>
   40d36:	f04f 33ff 	mov.w	r3, #4294967295	; 0xffffffff
   40d3a:	e038      	b.n	40dae <blake2s_init+0x8e>
   40d3c:	683b      	ldr	r3, [r7, #0]
   40d3e:	b2db      	uxtb	r3, r3
   40d40:	723b      	strb	r3, [r7, #8]
   40d42:	2300      	movs	r3, #0
   40d44:	727b      	strb	r3, [r7, #9]
   40d46:	2301      	movs	r3, #1
   40d48:	72bb      	strb	r3, [r7, #10]
   40d4a:	2301      	movs	r3, #1
   40d4c:	72fb      	strb	r3, [r7, #11]
   40d4e:	f107 0308 	add.w	r3, r7, #8
   40d52:	3304      	adds	r3, #4
   40d54:	2100      	movs	r1, #0
   40d56:	4618      	mov	r0, r3
   40d58:	f7ff fefb 	bl	40b52 <store32>
   40d5c:	f107 0308 	add.w	r3, r7, #8
   40d60:	3308      	adds	r3, #8
   40d62:	2100      	movs	r1, #0
   40d64:	4618      	mov	r0, r3
   40d66:	f7ff fef4 	bl	40b52 <store32>
   40d6a:	f107 0308 	add.w	r3, r7, #8
   40d6e:	330c      	adds	r3, #12
   40d70:	2100      	movs	r1, #0
   40d72:	4618      	mov	r0, r3
   40d74:	f7ff fed0 	bl	40b18 <store16>
   40d78:	2300      	movs	r3, #0
   40d7a:	75bb      	strb	r3, [r7, #22]
   40d7c:	2300      	movs	r3, #0
   40d7e:	75fb      	strb	r3, [r7, #23]
   40d80:	f107 0308 	add.w	r3, r7, #8
   40d84:	3310      	adds	r3, #16
   40d86:	2208      	movs	r2, #8
   40d88:	2100      	movs	r1, #0
   40d8a:	4618      	mov	r0, r3
   40d8c:	f7cf ef68 	blx	10c60 <memset@plt>
   40d90:	f107 0308 	add.w	r3, r7, #8
   40d94:	3318      	adds	r3, #24
   40d96:	2208      	movs	r2, #8
   40d98:	2100      	movs	r1, #0
   40d9a:	4618      	mov	r0, r3
   40d9c:	f7cf ef60 	blx	10c60 <memset@plt>
   40da0:	f107 0308 	add.w	r3, r7, #8
   40da4:	4619      	mov	r1, r3
   40da6:	6878      	ldr	r0, [r7, #4]
   40da8:	f7ff ff8c 	bl	40cc4 <blake2s_init_param>
   40dac:	4603      	mov	r3, r0
   40dae:	4618      	mov	r0, r3
   40db0:	3728      	adds	r7, #40	; 0x28
   40db2:	46bd      	mov	sp, r7
   40db4:	bd80      	pop	{r7, pc}

00040db6 <blake2s_init_key>:
   40db6:	b580      	push	{r7, lr}
   40db8:	b09c      	sub	sp, #112	; 0x70
   40dba:	af00      	add	r7, sp, #0
   40dbc:	60f8      	str	r0, [r7, #12]
   40dbe:	60b9      	str	r1, [r7, #8]
   40dc0:	607a      	str	r2, [r7, #4]
   40dc2:	603b      	str	r3, [r7, #0]
   40dc4:	68bb      	ldr	r3, [r7, #8]
   40dc6:	2b00      	cmp	r3, #0
   40dc8:	d002      	beq.n	40dd0 <blake2s_init_key+0x1a>
   40dca:	68bb      	ldr	r3, [r7, #8]
   40dcc:	2b20      	cmp	r3, #32
   40dce:	d902      	bls.n	40dd6 <blake2s_init_key+0x20>
   40dd0:	f04f 33ff 	mov.w	r3, #4294967295	; 0xffffffff
   40dd4:	e06c      	b.n	40eb0 <blake2s_init_key+0xfa>
   40dd6:	687b      	ldr	r3, [r7, #4]
   40dd8:	2b00      	cmp	r3, #0
   40dda:	d005      	beq.n	40de8 <blake2s_init_key+0x32>
   40ddc:	683b      	ldr	r3, [r7, #0]
   40dde:	2b00      	cmp	r3, #0
   40de0:	d002      	beq.n	40de8 <blake2s_init_key+0x32>
   40de2:	683b      	ldr	r3, [r7, #0]
   40de4:	2b20      	cmp	r3, #32
   40de6:	d902      	bls.n	40dee <blake2s_init_key+0x38>
   40de8:	f04f 33ff 	mov.w	r3, #4294967295	; 0xffffffff
   40dec:	e060      	b.n	40eb0 <blake2s_init_key+0xfa>
   40dee:	68bb      	ldr	r3, [r7, #8]
   40df0:	b2db      	uxtb	r3, r3
   40df2:	f887 3050 	strb.w	r3, [r7, #80]	; 0x50
   40df6:	683b      	ldr	r3, [r7, #0]
   40df8:	b2db      	uxtb	r3, r3
   40dfa:	f887 3051 	strb.w	r3, [r7, #81]	; 0x51
   40dfe:	2301      	movs	r3, #1
   40e00:	f887 3052 	strb.w	r3, [r7, #82]	; 0x52
   40e04:	2301      	movs	r3, #1
   40e06:	f887 3053 	strb.w	r3, [r7, #83]	; 0x53
   40e0a:	f107 0350 	add.w	r3, r7, #80	; 0x50
   40e0e:	3304      	adds	r3, #4
   40e10:	2100      	movs	r1, #0
   40e12:	4618      	mov	r0, r3
   40e14:	f7ff fe9d 	bl	40b52 <store32>
   40e18:	f107 0350 	add.w	r3, r7, #80	; 0x50
   40e1c:	3308      	adds	r3, #8
   40e1e:	2100      	movs	r1, #0
   40e20:	4618      	mov	r0, r3
   40e22:	f7ff fe96 	bl	40b52 <store32>
   40e26:	f107 0350 	add.w	r3, r7, #80	; 0x50
   40e2a:	330c      	adds	r3, #12
   40e2c:	2100      	movs	r1, #0
   40e2e:	4618      	mov	r0, r3
   40e30:	f7ff fe72 	bl	40b18 <store16>
   40e34:	2300      	movs	r3, #0
   40e36:	f887 305e 	strb.w	r3, [r7, #94]	; 0x5e
   40e3a:	2300      	movs	r3, #0
   40e3c:	f887 305f 	strb.w	r3, [r7, #95]	; 0x5f
   40e40:	f107 0350 	add.w	r3, r7, #80	; 0x50
   40e44:	3310      	adds	r3, #16
   40e46:	2208      	movs	r2, #8
   40e48:	2100      	movs	r1, #0
   40e4a:	4618      	mov	r0, r3
   40e4c:	f7cf ef08 	blx	10c60 <memset@plt>
   40e50:	f107 0350 	add.w	r3, r7, #80	; 0x50
   40e54:	3318      	adds	r3, #24
   40e56:	2208      	movs	r2, #8
   40e58:	2100      	movs	r1, #0
   40e5a:	4618      	mov	r0, r3
   40e5c:	f7cf ef00 	blx	10c60 <memset@plt>
   40e60:	f107 0350 	add.w	r3, r7, #80	; 0x50
   40e64:	4619      	mov	r1, r3
   40e66:	68f8      	ldr	r0, [r7, #12]
   40e68:	f7ff ff2c 	bl	40cc4 <blake2s_init_param>
   40e6c:	4603      	mov	r3, r0
   40e6e:	2b00      	cmp	r3, #0
   40e70:	da02      	bge.n	40e78 <blake2s_init_key+0xc2>
   40e72:	f04f 33ff 	mov.w	r3, #4294967295	; 0xffffffff
   40e76:	e01b      	b.n	40eb0 <blake2s_init_key+0xfa>
   40e78:	f107 0310 	add.w	r3, r7, #16
   40e7c:	2240      	movs	r2, #64	; 0x40
   40e7e:	2100      	movs	r1, #0
   40e80:	4618      	mov	r0, r3
   40e82:	f7cf eeee 	blx	10c60 <memset@plt>
   40e86:	f107 0310 	add.w	r3, r7, #16
   40e8a:	683a      	ldr	r2, [r7, #0]
   40e8c:	6879      	ldr	r1, [r7, #4]
   40e8e:	4618      	mov	r0, r3
   40e90:	f7cf ee80 	blx	10b94 <memcpy@plt>
   40e94:	f107 0310 	add.w	r3, r7, #16
   40e98:	2240      	movs	r2, #64	; 0x40
   40e9a:	4619      	mov	r1, r3
   40e9c:	68f8      	ldr	r0, [r7, #12]
   40e9e:	f002 fdeb 	bl	43a78 <blake2s_update>
   40ea2:	f107 0310 	add.w	r3, r7, #16
   40ea6:	2140      	movs	r1, #64	; 0x40
   40ea8:	4618      	mov	r0, r3
   40eaa:	f7ff fe84 	bl	40bb6 <secure_zero_memory>
   40eae:	2300      	movs	r3, #0
   40eb0:	4618      	mov	r0, r3
   40eb2:	3770      	adds	r7, #112	; 0x70
   40eb4:	46bd      	mov	sp, r7
   40eb6:	bd80      	pop	{r7, pc}

00040eb8 <blake2s_compress>:
   40eb8:	b580      	push	{r7, lr}
   40eba:	b0a4      	sub	sp, #144	; 0x90
   40ebc:	af00      	add	r7, sp, #0
   40ebe:	6078      	str	r0, [r7, #4]
   40ec0:	6039      	str	r1, [r7, #0]
   40ec2:	2300      	movs	r3, #0
   40ec4:	f8c7 308c 	str.w	r3, [r7, #140]	; 0x8c
   40ec8:	e015      	b.n	40ef6 <blake2s_compress+0x3e>
   40eca:	f8d7 308c 	ldr.w	r3, [r7, #140]	; 0x8c
   40ece:	009b      	lsls	r3, r3, #2
   40ed0:	683a      	ldr	r2, [r7, #0]
   40ed2:	4413      	add	r3, r2
   40ed4:	4618      	mov	r0, r3
   40ed6:	f7ff fe01 	bl	40adc <load32>
   40eda:	4602      	mov	r2, r0
   40edc:	f8d7 308c 	ldr.w	r3, [r7, #140]	; 0x8c
   40ee0:	009b      	lsls	r3, r3, #2
   40ee2:	f107 0190 	add.w	r1, r7, #144	; 0x90
   40ee6:	440b      	add	r3, r1
   40ee8:	f843 2c44 	str.w	r2, [r3, #-68]
   40eec:	f8d7 308c 	ldr.w	r3, [r7, #140]	; 0x8c
   40ef0:	3301      	adds	r3, #1
   40ef2:	f8c7 308c 	str.w	r3, [r7, #140]	; 0x8c
   40ef6:	f8d7 308c 	ldr.w	r3, [r7, #140]	; 0x8c
   40efa:	2b0f      	cmp	r3, #15
   40efc:	d9e5      	bls.n	40eca <blake2s_compress+0x12>
   40efe:	2300      	movs	r3, #0
   40f00:	f8c7 308c 	str.w	r3, [r7, #140]	; 0x8c
   40f04:	e011      	b.n	40f2a <blake2s_compress+0x72>
   40f06:	687b      	ldr	r3, [r7, #4]
   40f08:	f8d7 208c 	ldr.w	r2, [r7, #140]	; 0x8c
   40f0c:	f853 2022 	ldr.w	r2, [r3, r2, lsl #2]
   40f10:	f8d7 308c 	ldr.w	r3, [r7, #140]	; 0x8c
   40f14:	009b      	lsls	r3, r3, #2
   40f16:	f107 0190 	add.w	r1, r7, #144	; 0x90
   40f1a:	440b      	add	r3, r1
   40f1c:	f843 2c84 	str.w	r2, [r3, #-132]
   40f20:	f8d7 308c 	ldr.w	r3, [r7, #140]	; 0x8c
   40f24:	3301      	adds	r3, #1
   40f26:	f8c7 308c 	str.w	r3, [r7, #140]	; 0x8c
   40f2a:	f8d7 308c 	ldr.w	r3, [r7, #140]	; 0x8c
   40f2e:	2b07      	cmp	r3, #7
   40f30:	d9e9      	bls.n	40f06 <blake2s_compress+0x4e>
   40f32:	f24e 6367 	movw	r3, #58983	; 0xe667
   40f36:	f6c6 2309 	movt	r3, #27145	; 0x6a09
   40f3a:	62fb      	str	r3, [r7, #44]	; 0x2c
   40f3c:	f64a 6385 	movw	r3, #44677	; 0xae85
   40f40:	f6cb 3367 	movt	r3, #47975	; 0xbb67
   40f44:	633b      	str	r3, [r7, #48]	; 0x30
   40f46:	f24f 3372 	movw	r3, #62322	; 0xf372
   40f4a:	f6c3 436e 	movt	r3, #15470	; 0x3c6e
   40f4e:	637b      	str	r3, [r7, #52]	; 0x34
   40f50:	f24f 533a 	movw	r3, #62778	; 0xf53a
   40f54:	f2ca 534f 	movt	r3, #42319	; 0xa54f
   40f58:	63bb      	str	r3, [r7, #56]	; 0x38
   40f5a:	687b      	ldr	r3, [r7, #4]
   40f5c:	6a1a      	ldr	r2, [r3, #32]
   40f5e:	f245 237f 	movw	r3, #21119	; 0x527f
   40f62:	f2c5 130e 	movt	r3, #20750	; 0x510e
   40f66:	4053      	eors	r3, r2
   40f68:	63fb      	str	r3, [r7, #60]	; 0x3c
   40f6a:	687b      	ldr	r3, [r7, #4]
   40f6c:	6a5a      	ldr	r2, [r3, #36]	; 0x24
   40f6e:	f646 038c 	movw	r3, #26764	; 0x688c
   40f72:	f6c9 3305 	movt	r3, #39685	; 0x9b05
   40f76:	4053      	eors	r3, r2
   40f78:	643b      	str	r3, [r7, #64]	; 0x40
   40f7a:	687b      	ldr	r3, [r7, #4]
   40f7c:	6a9a      	ldr	r2, [r3, #40]	; 0x28
   40f7e:	f64d 13ab 	movw	r3, #55723	; 0xd9ab
   40f82:	f6c1 7383 	movt	r3, #8067	; 0x1f83
   40f86:	4053      	eors	r3, r2
   40f88:	647b      	str	r3, [r7, #68]	; 0x44
   40f8a:	687b      	ldr	r3, [r7, #4]
   40f8c:	6ada      	ldr	r2, [r3, #44]	; 0x2c
   40f8e:	f64c 5319 	movw	r3, #52505	; 0xcd19
   40f92:	f6c5 33e0 	movt	r3, #23520	; 0x5be0
   40f96:	4053      	eors	r3, r2
   40f98:	64bb      	str	r3, [r7, #72]	; 0x48
   40f9a:	68fa      	ldr	r2, [r7, #12]
   40f9c:	69fb      	ldr	r3, [r7, #28]
   40f9e:	441a      	add	r2, r3
   40fa0:	2300      	movs	r3, #0
   40fa2:	009b      	lsls	r3, r3, #2
   40fa4:	f107 0190 	add.w	r1, r7, #144	; 0x90
   40fa8:	440b      	add	r3, r1
   40faa:	f853 3c44 	ldr.w	r3, [r3, #-68]
   40fae:	4413      	add	r3, r2
   40fb0:	60fb      	str	r3, [r7, #12]
   40fb2:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   40fb4:	68fb      	ldr	r3, [r7, #12]
   40fb6:	4053      	eors	r3, r2
   40fb8:	2110      	movs	r1, #16
   40fba:	4618      	mov	r0, r3
   40fbc:	f7ff fdec 	bl	40b98 <rotr32>
   40fc0:	4603      	mov	r3, r0
   40fc2:	63fb      	str	r3, [r7, #60]	; 0x3c
   40fc4:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   40fc6:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   40fc8:	4413      	add	r3, r2
   40fca:	62fb      	str	r3, [r7, #44]	; 0x2c
   40fcc:	69fa      	ldr	r2, [r7, #28]
   40fce:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   40fd0:	4053      	eors	r3, r2
   40fd2:	210c      	movs	r1, #12
   40fd4:	4618      	mov	r0, r3
   40fd6:	f7ff fddf 	bl	40b98 <rotr32>
   40fda:	4603      	mov	r3, r0
   40fdc:	61fb      	str	r3, [r7, #28]
   40fde:	68fa      	ldr	r2, [r7, #12]
   40fe0:	69fb      	ldr	r3, [r7, #28]
   40fe2:	441a      	add	r2, r3
   40fe4:	2301      	movs	r3, #1
   40fe6:	009b      	lsls	r3, r3, #2
   40fe8:	f107 0190 	add.w	r1, r7, #144	; 0x90
   40fec:	440b      	add	r3, r1
   40fee:	f853 3c44 	ldr.w	r3, [r3, #-68]
   40ff2:	4413      	add	r3, r2
   40ff4:	60fb      	str	r3, [r7, #12]
   40ff6:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   40ff8:	68fb      	ldr	r3, [r7, #12]
   40ffa:	4053      	eors	r3, r2
   40ffc:	2108      	movs	r1, #8
   40ffe:	4618      	mov	r0, r3
   41000:	f7ff fdca 	bl	40b98 <rotr32>
   41004:	4603      	mov	r3, r0
   41006:	63fb      	str	r3, [r7, #60]	; 0x3c
   41008:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   4100a:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   4100c:	4413      	add	r3, r2
   4100e:	62fb      	str	r3, [r7, #44]	; 0x2c
   41010:	69fa      	ldr	r2, [r7, #28]
   41012:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   41014:	4053      	eors	r3, r2
   41016:	2107      	movs	r1, #7
   41018:	4618      	mov	r0, r3
   4101a:	f7ff fdbd 	bl	40b98 <rotr32>
   4101e:	4603      	mov	r3, r0
   41020:	61fb      	str	r3, [r7, #28]
   41022:	693a      	ldr	r2, [r7, #16]
   41024:	6a3b      	ldr	r3, [r7, #32]
   41026:	441a      	add	r2, r3
   41028:	2302      	movs	r3, #2
   4102a:	009b      	lsls	r3, r3, #2
   4102c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41030:	440b      	add	r3, r1
   41032:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41036:	4413      	add	r3, r2
   41038:	613b      	str	r3, [r7, #16]
   4103a:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   4103c:	693b      	ldr	r3, [r7, #16]
   4103e:	4053      	eors	r3, r2
   41040:	2110      	movs	r1, #16
   41042:	4618      	mov	r0, r3
   41044:	f7ff fda8 	bl	40b98 <rotr32>
   41048:	4603      	mov	r3, r0
   4104a:	643b      	str	r3, [r7, #64]	; 0x40
   4104c:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   4104e:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   41050:	4413      	add	r3, r2
   41052:	633b      	str	r3, [r7, #48]	; 0x30
   41054:	6a3a      	ldr	r2, [r7, #32]
   41056:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   41058:	4053      	eors	r3, r2
   4105a:	210c      	movs	r1, #12
   4105c:	4618      	mov	r0, r3
   4105e:	f7ff fd9b 	bl	40b98 <rotr32>
   41062:	4603      	mov	r3, r0
   41064:	623b      	str	r3, [r7, #32]
   41066:	693a      	ldr	r2, [r7, #16]
   41068:	6a3b      	ldr	r3, [r7, #32]
   4106a:	441a      	add	r2, r3
   4106c:	2303      	movs	r3, #3
   4106e:	009b      	lsls	r3, r3, #2
   41070:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41074:	440b      	add	r3, r1
   41076:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4107a:	4413      	add	r3, r2
   4107c:	613b      	str	r3, [r7, #16]
   4107e:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   41080:	693b      	ldr	r3, [r7, #16]
   41082:	4053      	eors	r3, r2
   41084:	2108      	movs	r1, #8
   41086:	4618      	mov	r0, r3
   41088:	f7ff fd86 	bl	40b98 <rotr32>
   4108c:	4603      	mov	r3, r0
   4108e:	643b      	str	r3, [r7, #64]	; 0x40
   41090:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   41092:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   41094:	4413      	add	r3, r2
   41096:	633b      	str	r3, [r7, #48]	; 0x30
   41098:	6a3a      	ldr	r2, [r7, #32]
   4109a:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   4109c:	4053      	eors	r3, r2
   4109e:	2107      	movs	r1, #7
   410a0:	4618      	mov	r0, r3
   410a2:	f7ff fd79 	bl	40b98 <rotr32>
   410a6:	4603      	mov	r3, r0
   410a8:	623b      	str	r3, [r7, #32]
   410aa:	697a      	ldr	r2, [r7, #20]
   410ac:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   410ae:	441a      	add	r2, r3
   410b0:	2304      	movs	r3, #4
   410b2:	009b      	lsls	r3, r3, #2
   410b4:	f107 0190 	add.w	r1, r7, #144	; 0x90
   410b8:	440b      	add	r3, r1
   410ba:	f853 3c44 	ldr.w	r3, [r3, #-68]
   410be:	4413      	add	r3, r2
   410c0:	617b      	str	r3, [r7, #20]
   410c2:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   410c4:	697b      	ldr	r3, [r7, #20]
   410c6:	4053      	eors	r3, r2
   410c8:	2110      	movs	r1, #16
   410ca:	4618      	mov	r0, r3
   410cc:	f7ff fd64 	bl	40b98 <rotr32>
   410d0:	4603      	mov	r3, r0
   410d2:	647b      	str	r3, [r7, #68]	; 0x44
   410d4:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   410d6:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   410d8:	4413      	add	r3, r2
   410da:	637b      	str	r3, [r7, #52]	; 0x34
   410dc:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   410de:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   410e0:	4053      	eors	r3, r2
   410e2:	210c      	movs	r1, #12
   410e4:	4618      	mov	r0, r3
   410e6:	f7ff fd57 	bl	40b98 <rotr32>
   410ea:	4603      	mov	r3, r0
   410ec:	627b      	str	r3, [r7, #36]	; 0x24
   410ee:	697a      	ldr	r2, [r7, #20]
   410f0:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   410f2:	441a      	add	r2, r3
   410f4:	2305      	movs	r3, #5
   410f6:	009b      	lsls	r3, r3, #2
   410f8:	f107 0190 	add.w	r1, r7, #144	; 0x90
   410fc:	440b      	add	r3, r1
   410fe:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41102:	4413      	add	r3, r2
   41104:	617b      	str	r3, [r7, #20]
   41106:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   41108:	697b      	ldr	r3, [r7, #20]
   4110a:	4053      	eors	r3, r2
   4110c:	2108      	movs	r1, #8
   4110e:	4618      	mov	r0, r3
   41110:	f7ff fd42 	bl	40b98 <rotr32>
   41114:	4603      	mov	r3, r0
   41116:	647b      	str	r3, [r7, #68]	; 0x44
   41118:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   4111a:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   4111c:	4413      	add	r3, r2
   4111e:	637b      	str	r3, [r7, #52]	; 0x34
   41120:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   41122:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   41124:	4053      	eors	r3, r2
   41126:	2107      	movs	r1, #7
   41128:	4618      	mov	r0, r3
   4112a:	f7ff fd35 	bl	40b98 <rotr32>
   4112e:	4603      	mov	r3, r0
   41130:	627b      	str	r3, [r7, #36]	; 0x24
   41132:	69ba      	ldr	r2, [r7, #24]
   41134:	6abb      	ldr	r3, [r7, #40]	; 0x28
   41136:	441a      	add	r2, r3
   41138:	2306      	movs	r3, #6
   4113a:	009b      	lsls	r3, r3, #2
   4113c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41140:	440b      	add	r3, r1
   41142:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41146:	4413      	add	r3, r2
   41148:	61bb      	str	r3, [r7, #24]
   4114a:	6cba      	ldr	r2, [r7, #72]	; 0x48
   4114c:	69bb      	ldr	r3, [r7, #24]
   4114e:	4053      	eors	r3, r2
   41150:	2110      	movs	r1, #16
   41152:	4618      	mov	r0, r3
   41154:	f7ff fd20 	bl	40b98 <rotr32>
   41158:	4603      	mov	r3, r0
   4115a:	64bb      	str	r3, [r7, #72]	; 0x48
   4115c:	6bba      	ldr	r2, [r7, #56]	; 0x38
   4115e:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   41160:	4413      	add	r3, r2
   41162:	63bb      	str	r3, [r7, #56]	; 0x38
   41164:	6aba      	ldr	r2, [r7, #40]	; 0x28
   41166:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   41168:	4053      	eors	r3, r2
   4116a:	210c      	movs	r1, #12
   4116c:	4618      	mov	r0, r3
   4116e:	f7ff fd13 	bl	40b98 <rotr32>
   41172:	4603      	mov	r3, r0
   41174:	62bb      	str	r3, [r7, #40]	; 0x28
   41176:	69ba      	ldr	r2, [r7, #24]
   41178:	6abb      	ldr	r3, [r7, #40]	; 0x28
   4117a:	441a      	add	r2, r3
   4117c:	2307      	movs	r3, #7
   4117e:	009b      	lsls	r3, r3, #2
   41180:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41184:	440b      	add	r3, r1
   41186:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4118a:	4413      	add	r3, r2
   4118c:	61bb      	str	r3, [r7, #24]
   4118e:	6cba      	ldr	r2, [r7, #72]	; 0x48
   41190:	69bb      	ldr	r3, [r7, #24]
   41192:	4053      	eors	r3, r2
   41194:	2108      	movs	r1, #8
   41196:	4618      	mov	r0, r3
   41198:	f7ff fcfe 	bl	40b98 <rotr32>
   4119c:	4603      	mov	r3, r0
   4119e:	64bb      	str	r3, [r7, #72]	; 0x48
   411a0:	6bba      	ldr	r2, [r7, #56]	; 0x38
   411a2:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   411a4:	4413      	add	r3, r2
   411a6:	63bb      	str	r3, [r7, #56]	; 0x38
   411a8:	6aba      	ldr	r2, [r7, #40]	; 0x28
   411aa:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   411ac:	4053      	eors	r3, r2
   411ae:	2107      	movs	r1, #7
   411b0:	4618      	mov	r0, r3
   411b2:	f7ff fcf1 	bl	40b98 <rotr32>
   411b6:	4603      	mov	r3, r0
   411b8:	62bb      	str	r3, [r7, #40]	; 0x28
   411ba:	68fa      	ldr	r2, [r7, #12]
   411bc:	6a3b      	ldr	r3, [r7, #32]
   411be:	441a      	add	r2, r3
   411c0:	2308      	movs	r3, #8
   411c2:	009b      	lsls	r3, r3, #2
   411c4:	f107 0190 	add.w	r1, r7, #144	; 0x90
   411c8:	440b      	add	r3, r1
   411ca:	f853 3c44 	ldr.w	r3, [r3, #-68]
   411ce:	4413      	add	r3, r2
   411d0:	60fb      	str	r3, [r7, #12]
   411d2:	6cba      	ldr	r2, [r7, #72]	; 0x48
   411d4:	68fb      	ldr	r3, [r7, #12]
   411d6:	4053      	eors	r3, r2
   411d8:	2110      	movs	r1, #16
   411da:	4618      	mov	r0, r3
   411dc:	f7ff fcdc 	bl	40b98 <rotr32>
   411e0:	4603      	mov	r3, r0
   411e2:	64bb      	str	r3, [r7, #72]	; 0x48
   411e4:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   411e6:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   411e8:	4413      	add	r3, r2
   411ea:	637b      	str	r3, [r7, #52]	; 0x34
   411ec:	6a3a      	ldr	r2, [r7, #32]
   411ee:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   411f0:	4053      	eors	r3, r2
   411f2:	210c      	movs	r1, #12
   411f4:	4618      	mov	r0, r3
   411f6:	f7ff fccf 	bl	40b98 <rotr32>
   411fa:	4603      	mov	r3, r0
   411fc:	623b      	str	r3, [r7, #32]
   411fe:	68fa      	ldr	r2, [r7, #12]
   41200:	6a3b      	ldr	r3, [r7, #32]
   41202:	441a      	add	r2, r3
   41204:	2309      	movs	r3, #9
   41206:	009b      	lsls	r3, r3, #2
   41208:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4120c:	440b      	add	r3, r1
   4120e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41212:	4413      	add	r3, r2
   41214:	60fb      	str	r3, [r7, #12]
   41216:	6cba      	ldr	r2, [r7, #72]	; 0x48
   41218:	68fb      	ldr	r3, [r7, #12]
   4121a:	4053      	eors	r3, r2
   4121c:	2108      	movs	r1, #8
   4121e:	4618      	mov	r0, r3
   41220:	f7ff fcba 	bl	40b98 <rotr32>
   41224:	4603      	mov	r3, r0
   41226:	64bb      	str	r3, [r7, #72]	; 0x48
   41228:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   4122a:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   4122c:	4413      	add	r3, r2
   4122e:	637b      	str	r3, [r7, #52]	; 0x34
   41230:	6a3a      	ldr	r2, [r7, #32]
   41232:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   41234:	4053      	eors	r3, r2
   41236:	2107      	movs	r1, #7
   41238:	4618      	mov	r0, r3
   4123a:	f7ff fcad 	bl	40b98 <rotr32>
   4123e:	4603      	mov	r3, r0
   41240:	623b      	str	r3, [r7, #32]
   41242:	693a      	ldr	r2, [r7, #16]
   41244:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   41246:	441a      	add	r2, r3
   41248:	230a      	movs	r3, #10
   4124a:	009b      	lsls	r3, r3, #2
   4124c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41250:	440b      	add	r3, r1
   41252:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41256:	4413      	add	r3, r2
   41258:	613b      	str	r3, [r7, #16]
   4125a:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   4125c:	693b      	ldr	r3, [r7, #16]
   4125e:	4053      	eors	r3, r2
   41260:	2110      	movs	r1, #16
   41262:	4618      	mov	r0, r3
   41264:	f7ff fc98 	bl	40b98 <rotr32>
   41268:	4603      	mov	r3, r0
   4126a:	63fb      	str	r3, [r7, #60]	; 0x3c
   4126c:	6bba      	ldr	r2, [r7, #56]	; 0x38
   4126e:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   41270:	4413      	add	r3, r2
   41272:	63bb      	str	r3, [r7, #56]	; 0x38
   41274:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   41276:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   41278:	4053      	eors	r3, r2
   4127a:	210c      	movs	r1, #12
   4127c:	4618      	mov	r0, r3
   4127e:	f7ff fc8b 	bl	40b98 <rotr32>
   41282:	4603      	mov	r3, r0
   41284:	627b      	str	r3, [r7, #36]	; 0x24
   41286:	693a      	ldr	r2, [r7, #16]
   41288:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   4128a:	441a      	add	r2, r3
   4128c:	230b      	movs	r3, #11
   4128e:	009b      	lsls	r3, r3, #2
   41290:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41294:	440b      	add	r3, r1
   41296:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4129a:	4413      	add	r3, r2
   4129c:	613b      	str	r3, [r7, #16]
   4129e:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   412a0:	693b      	ldr	r3, [r7, #16]
   412a2:	4053      	eors	r3, r2
   412a4:	2108      	movs	r1, #8
   412a6:	4618      	mov	r0, r3
   412a8:	f7ff fc76 	bl	40b98 <rotr32>
   412ac:	4603      	mov	r3, r0
   412ae:	63fb      	str	r3, [r7, #60]	; 0x3c
   412b0:	6bba      	ldr	r2, [r7, #56]	; 0x38
   412b2:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   412b4:	4413      	add	r3, r2
   412b6:	63bb      	str	r3, [r7, #56]	; 0x38
   412b8:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   412ba:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   412bc:	4053      	eors	r3, r2
   412be:	2107      	movs	r1, #7
   412c0:	4618      	mov	r0, r3
   412c2:	f7ff fc69 	bl	40b98 <rotr32>
   412c6:	4603      	mov	r3, r0
   412c8:	627b      	str	r3, [r7, #36]	; 0x24
   412ca:	697a      	ldr	r2, [r7, #20]
   412cc:	6abb      	ldr	r3, [r7, #40]	; 0x28
   412ce:	441a      	add	r2, r3
   412d0:	230c      	movs	r3, #12
   412d2:	009b      	lsls	r3, r3, #2
   412d4:	f107 0190 	add.w	r1, r7, #144	; 0x90
   412d8:	440b      	add	r3, r1
   412da:	f853 3c44 	ldr.w	r3, [r3, #-68]
   412de:	4413      	add	r3, r2
   412e0:	617b      	str	r3, [r7, #20]
   412e2:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   412e4:	697b      	ldr	r3, [r7, #20]
   412e6:	4053      	eors	r3, r2
   412e8:	2110      	movs	r1, #16
   412ea:	4618      	mov	r0, r3
   412ec:	f7ff fc54 	bl	40b98 <rotr32>
   412f0:	4603      	mov	r3, r0
   412f2:	643b      	str	r3, [r7, #64]	; 0x40
   412f4:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   412f6:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   412f8:	4413      	add	r3, r2
   412fa:	62fb      	str	r3, [r7, #44]	; 0x2c
   412fc:	6aba      	ldr	r2, [r7, #40]	; 0x28
   412fe:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   41300:	4053      	eors	r3, r2
   41302:	210c      	movs	r1, #12
   41304:	4618      	mov	r0, r3
   41306:	f7ff fc47 	bl	40b98 <rotr32>
   4130a:	4603      	mov	r3, r0
   4130c:	62bb      	str	r3, [r7, #40]	; 0x28
   4130e:	697a      	ldr	r2, [r7, #20]
   41310:	6abb      	ldr	r3, [r7, #40]	; 0x28
   41312:	441a      	add	r2, r3
   41314:	230d      	movs	r3, #13
   41316:	009b      	lsls	r3, r3, #2
   41318:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4131c:	440b      	add	r3, r1
   4131e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41322:	4413      	add	r3, r2
   41324:	617b      	str	r3, [r7, #20]
   41326:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   41328:	697b      	ldr	r3, [r7, #20]
   4132a:	4053      	eors	r3, r2
   4132c:	2108      	movs	r1, #8
   4132e:	4618      	mov	r0, r3
   41330:	f7ff fc32 	bl	40b98 <rotr32>
   41334:	4603      	mov	r3, r0
   41336:	643b      	str	r3, [r7, #64]	; 0x40
   41338:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   4133a:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   4133c:	4413      	add	r3, r2
   4133e:	62fb      	str	r3, [r7, #44]	; 0x2c
   41340:	6aba      	ldr	r2, [r7, #40]	; 0x28
   41342:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   41344:	4053      	eors	r3, r2
   41346:	2107      	movs	r1, #7
   41348:	4618      	mov	r0, r3
   4134a:	f7ff fc25 	bl	40b98 <rotr32>
   4134e:	4603      	mov	r3, r0
   41350:	62bb      	str	r3, [r7, #40]	; 0x28
   41352:	69ba      	ldr	r2, [r7, #24]
   41354:	69fb      	ldr	r3, [r7, #28]
   41356:	441a      	add	r2, r3
   41358:	230e      	movs	r3, #14
   4135a:	009b      	lsls	r3, r3, #2
   4135c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41360:	440b      	add	r3, r1
   41362:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41366:	4413      	add	r3, r2
   41368:	61bb      	str	r3, [r7, #24]
   4136a:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   4136c:	69bb      	ldr	r3, [r7, #24]
   4136e:	4053      	eors	r3, r2
   41370:	2110      	movs	r1, #16
   41372:	4618      	mov	r0, r3
   41374:	f7ff fc10 	bl	40b98 <rotr32>
   41378:	4603      	mov	r3, r0
   4137a:	647b      	str	r3, [r7, #68]	; 0x44
   4137c:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   4137e:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   41380:	4413      	add	r3, r2
   41382:	633b      	str	r3, [r7, #48]	; 0x30
   41384:	69fa      	ldr	r2, [r7, #28]
   41386:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   41388:	4053      	eors	r3, r2
   4138a:	210c      	movs	r1, #12
   4138c:	4618      	mov	r0, r3
   4138e:	f7ff fc03 	bl	40b98 <rotr32>
   41392:	4603      	mov	r3, r0
   41394:	61fb      	str	r3, [r7, #28]
   41396:	69ba      	ldr	r2, [r7, #24]
   41398:	69fb      	ldr	r3, [r7, #28]
   4139a:	441a      	add	r2, r3
   4139c:	230f      	movs	r3, #15
   4139e:	009b      	lsls	r3, r3, #2
   413a0:	f107 0190 	add.w	r1, r7, #144	; 0x90
   413a4:	440b      	add	r3, r1
   413a6:	f853 3c44 	ldr.w	r3, [r3, #-68]
   413aa:	4413      	add	r3, r2
   413ac:	61bb      	str	r3, [r7, #24]
   413ae:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   413b0:	69bb      	ldr	r3, [r7, #24]
   413b2:	4053      	eors	r3, r2
   413b4:	2108      	movs	r1, #8
   413b6:	4618      	mov	r0, r3
   413b8:	f7ff fbee 	bl	40b98 <rotr32>
   413bc:	4603      	mov	r3, r0
   413be:	647b      	str	r3, [r7, #68]	; 0x44
   413c0:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   413c2:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   413c4:	4413      	add	r3, r2
   413c6:	633b      	str	r3, [r7, #48]	; 0x30
   413c8:	69fa      	ldr	r2, [r7, #28]
   413ca:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   413cc:	4053      	eors	r3, r2
   413ce:	2107      	movs	r1, #7
   413d0:	4618      	mov	r0, r3
   413d2:	f7ff fbe1 	bl	40b98 <rotr32>
   413d6:	4603      	mov	r3, r0
   413d8:	61fb      	str	r3, [r7, #28]
   413da:	68fa      	ldr	r2, [r7, #12]
   413dc:	69fb      	ldr	r3, [r7, #28]
   413de:	441a      	add	r2, r3
   413e0:	230e      	movs	r3, #14
   413e2:	009b      	lsls	r3, r3, #2
   413e4:	f107 0190 	add.w	r1, r7, #144	; 0x90
   413e8:	440b      	add	r3, r1
   413ea:	f853 3c44 	ldr.w	r3, [r3, #-68]
   413ee:	4413      	add	r3, r2
   413f0:	60fb      	str	r3, [r7, #12]
   413f2:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   413f4:	68fb      	ldr	r3, [r7, #12]
   413f6:	4053      	eors	r3, r2
   413f8:	2110      	movs	r1, #16
   413fa:	4618      	mov	r0, r3
   413fc:	f7ff fbcc 	bl	40b98 <rotr32>
   41400:	4603      	mov	r3, r0
   41402:	63fb      	str	r3, [r7, #60]	; 0x3c
   41404:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   41406:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   41408:	4413      	add	r3, r2
   4140a:	62fb      	str	r3, [r7, #44]	; 0x2c
   4140c:	69fa      	ldr	r2, [r7, #28]
   4140e:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   41410:	4053      	eors	r3, r2
   41412:	210c      	movs	r1, #12
   41414:	4618      	mov	r0, r3
   41416:	f7ff fbbf 	bl	40b98 <rotr32>
   4141a:	4603      	mov	r3, r0
   4141c:	61fb      	str	r3, [r7, #28]
   4141e:	68fa      	ldr	r2, [r7, #12]
   41420:	69fb      	ldr	r3, [r7, #28]
   41422:	441a      	add	r2, r3
   41424:	230a      	movs	r3, #10
   41426:	009b      	lsls	r3, r3, #2
   41428:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4142c:	440b      	add	r3, r1
   4142e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41432:	4413      	add	r3, r2
   41434:	60fb      	str	r3, [r7, #12]
   41436:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   41438:	68fb      	ldr	r3, [r7, #12]
   4143a:	4053      	eors	r3, r2
   4143c:	2108      	movs	r1, #8
   4143e:	4618      	mov	r0, r3
   41440:	f7ff fbaa 	bl	40b98 <rotr32>
   41444:	4603      	mov	r3, r0
   41446:	63fb      	str	r3, [r7, #60]	; 0x3c
   41448:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   4144a:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   4144c:	4413      	add	r3, r2
   4144e:	62fb      	str	r3, [r7, #44]	; 0x2c
   41450:	69fa      	ldr	r2, [r7, #28]
   41452:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   41454:	4053      	eors	r3, r2
   41456:	2107      	movs	r1, #7
   41458:	4618      	mov	r0, r3
   4145a:	f7ff fb9d 	bl	40b98 <rotr32>
   4145e:	4603      	mov	r3, r0
   41460:	61fb      	str	r3, [r7, #28]
   41462:	693a      	ldr	r2, [r7, #16]
   41464:	6a3b      	ldr	r3, [r7, #32]
   41466:	441a      	add	r2, r3
   41468:	2304      	movs	r3, #4
   4146a:	009b      	lsls	r3, r3, #2
   4146c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41470:	440b      	add	r3, r1
   41472:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41476:	4413      	add	r3, r2
   41478:	613b      	str	r3, [r7, #16]
   4147a:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   4147c:	693b      	ldr	r3, [r7, #16]
   4147e:	4053      	eors	r3, r2
   41480:	2110      	movs	r1, #16
   41482:	4618      	mov	r0, r3
   41484:	f7ff fb88 	bl	40b98 <rotr32>
   41488:	4603      	mov	r3, r0
   4148a:	643b      	str	r3, [r7, #64]	; 0x40
   4148c:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   4148e:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   41490:	4413      	add	r3, r2
   41492:	633b      	str	r3, [r7, #48]	; 0x30
   41494:	6a3a      	ldr	r2, [r7, #32]
   41496:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   41498:	4053      	eors	r3, r2
   4149a:	210c      	movs	r1, #12
   4149c:	4618      	mov	r0, r3
   4149e:	f7ff fb7b 	bl	40b98 <rotr32>
   414a2:	4603      	mov	r3, r0
   414a4:	623b      	str	r3, [r7, #32]
   414a6:	693a      	ldr	r2, [r7, #16]
   414a8:	6a3b      	ldr	r3, [r7, #32]
   414aa:	441a      	add	r2, r3
   414ac:	2308      	movs	r3, #8
   414ae:	009b      	lsls	r3, r3, #2
   414b0:	f107 0190 	add.w	r1, r7, #144	; 0x90
   414b4:	440b      	add	r3, r1
   414b6:	f853 3c44 	ldr.w	r3, [r3, #-68]
   414ba:	4413      	add	r3, r2
   414bc:	613b      	str	r3, [r7, #16]
   414be:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   414c0:	693b      	ldr	r3, [r7, #16]
   414c2:	4053      	eors	r3, r2
   414c4:	2108      	movs	r1, #8
   414c6:	4618      	mov	r0, r3
   414c8:	f7ff fb66 	bl	40b98 <rotr32>
   414cc:	4603      	mov	r3, r0
   414ce:	643b      	str	r3, [r7, #64]	; 0x40
   414d0:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   414d2:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   414d4:	4413      	add	r3, r2
   414d6:	633b      	str	r3, [r7, #48]	; 0x30
   414d8:	6a3a      	ldr	r2, [r7, #32]
   414da:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   414dc:	4053      	eors	r3, r2
   414de:	2107      	movs	r1, #7
   414e0:	4618      	mov	r0, r3
   414e2:	f7ff fb59 	bl	40b98 <rotr32>
   414e6:	4603      	mov	r3, r0
   414e8:	623b      	str	r3, [r7, #32]
   414ea:	697a      	ldr	r2, [r7, #20]
   414ec:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   414ee:	441a      	add	r2, r3
   414f0:	2309      	movs	r3, #9
   414f2:	009b      	lsls	r3, r3, #2
   414f4:	f107 0190 	add.w	r1, r7, #144	; 0x90
   414f8:	440b      	add	r3, r1
   414fa:	f853 3c44 	ldr.w	r3, [r3, #-68]
   414fe:	4413      	add	r3, r2
   41500:	617b      	str	r3, [r7, #20]
   41502:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   41504:	697b      	ldr	r3, [r7, #20]
   41506:	4053      	eors	r3, r2
   41508:	2110      	movs	r1, #16
   4150a:	4618      	mov	r0, r3
   4150c:	f7ff fb44 	bl	40b98 <rotr32>
   41510:	4603      	mov	r3, r0
   41512:	647b      	str	r3, [r7, #68]	; 0x44
   41514:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   41516:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   41518:	4413      	add	r3, r2
   4151a:	637b      	str	r3, [r7, #52]	; 0x34
   4151c:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   4151e:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   41520:	4053      	eors	r3, r2
   41522:	210c      	movs	r1, #12
   41524:	4618      	mov	r0, r3
   41526:	f7ff fb37 	bl	40b98 <rotr32>
   4152a:	4603      	mov	r3, r0
   4152c:	627b      	str	r3, [r7, #36]	; 0x24
   4152e:	697a      	ldr	r2, [r7, #20]
   41530:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   41532:	441a      	add	r2, r3
   41534:	230f      	movs	r3, #15
   41536:	009b      	lsls	r3, r3, #2
   41538:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4153c:	440b      	add	r3, r1
   4153e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41542:	4413      	add	r3, r2
   41544:	617b      	str	r3, [r7, #20]
   41546:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   41548:	697b      	ldr	r3, [r7, #20]
   4154a:	4053      	eors	r3, r2
   4154c:	2108      	movs	r1, #8
   4154e:	4618      	mov	r0, r3
   41550:	f7ff fb22 	bl	40b98 <rotr32>
   41554:	4603      	mov	r3, r0
   41556:	647b      	str	r3, [r7, #68]	; 0x44
   41558:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   4155a:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   4155c:	4413      	add	r3, r2
   4155e:	637b      	str	r3, [r7, #52]	; 0x34
   41560:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   41562:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   41564:	4053      	eors	r3, r2
   41566:	2107      	movs	r1, #7
   41568:	4618      	mov	r0, r3
   4156a:	f7ff fb15 	bl	40b98 <rotr32>
   4156e:	4603      	mov	r3, r0
   41570:	627b      	str	r3, [r7, #36]	; 0x24
   41572:	69ba      	ldr	r2, [r7, #24]
   41574:	6abb      	ldr	r3, [r7, #40]	; 0x28
   41576:	441a      	add	r2, r3
   41578:	230d      	movs	r3, #13
   4157a:	009b      	lsls	r3, r3, #2
   4157c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41580:	440b      	add	r3, r1
   41582:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41586:	4413      	add	r3, r2
   41588:	61bb      	str	r3, [r7, #24]
   4158a:	6cba      	ldr	r2, [r7, #72]	; 0x48
   4158c:	69bb      	ldr	r3, [r7, #24]
   4158e:	4053      	eors	r3, r2
   41590:	2110      	movs	r1, #16
   41592:	4618      	mov	r0, r3
   41594:	f7ff fb00 	bl	40b98 <rotr32>
   41598:	4603      	mov	r3, r0
   4159a:	64bb      	str	r3, [r7, #72]	; 0x48
   4159c:	6bba      	ldr	r2, [r7, #56]	; 0x38
   4159e:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   415a0:	4413      	add	r3, r2
   415a2:	63bb      	str	r3, [r7, #56]	; 0x38
   415a4:	6aba      	ldr	r2, [r7, #40]	; 0x28
   415a6:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   415a8:	4053      	eors	r3, r2
   415aa:	210c      	movs	r1, #12
   415ac:	4618      	mov	r0, r3
   415ae:	f7ff faf3 	bl	40b98 <rotr32>
   415b2:	4603      	mov	r3, r0
   415b4:	62bb      	str	r3, [r7, #40]	; 0x28
   415b6:	69ba      	ldr	r2, [r7, #24]
   415b8:	6abb      	ldr	r3, [r7, #40]	; 0x28
   415ba:	441a      	add	r2, r3
   415bc:	2306      	movs	r3, #6
   415be:	009b      	lsls	r3, r3, #2
   415c0:	f107 0190 	add.w	r1, r7, #144	; 0x90
   415c4:	440b      	add	r3, r1
   415c6:	f853 3c44 	ldr.w	r3, [r3, #-68]
   415ca:	4413      	add	r3, r2
   415cc:	61bb      	str	r3, [r7, #24]
   415ce:	6cba      	ldr	r2, [r7, #72]	; 0x48
   415d0:	69bb      	ldr	r3, [r7, #24]
   415d2:	4053      	eors	r3, r2
   415d4:	2108      	movs	r1, #8
   415d6:	4618      	mov	r0, r3
   415d8:	f7ff fade 	bl	40b98 <rotr32>
   415dc:	4603      	mov	r3, r0
   415de:	64bb      	str	r3, [r7, #72]	; 0x48
   415e0:	6bba      	ldr	r2, [r7, #56]	; 0x38
   415e2:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   415e4:	4413      	add	r3, r2
   415e6:	63bb      	str	r3, [r7, #56]	; 0x38
   415e8:	6aba      	ldr	r2, [r7, #40]	; 0x28
   415ea:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   415ec:	4053      	eors	r3, r2
   415ee:	2107      	movs	r1, #7
   415f0:	4618      	mov	r0, r3
   415f2:	f7ff fad1 	bl	40b98 <rotr32>
   415f6:	4603      	mov	r3, r0
   415f8:	62bb      	str	r3, [r7, #40]	; 0x28
   415fa:	68fa      	ldr	r2, [r7, #12]
   415fc:	6a3b      	ldr	r3, [r7, #32]
   415fe:	441a      	add	r2, r3
   41600:	2301      	movs	r3, #1
   41602:	009b      	lsls	r3, r3, #2
   41604:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41608:	440b      	add	r3, r1
   4160a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4160e:	4413      	add	r3, r2
   41610:	60fb      	str	r3, [r7, #12]
   41612:	6cba      	ldr	r2, [r7, #72]	; 0x48
   41614:	68fb      	ldr	r3, [r7, #12]
   41616:	4053      	eors	r3, r2
   41618:	2110      	movs	r1, #16
   4161a:	4618      	mov	r0, r3
   4161c:	f7ff fabc 	bl	40b98 <rotr32>
   41620:	4603      	mov	r3, r0
   41622:	64bb      	str	r3, [r7, #72]	; 0x48
   41624:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   41626:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   41628:	4413      	add	r3, r2
   4162a:	637b      	str	r3, [r7, #52]	; 0x34
   4162c:	6a3a      	ldr	r2, [r7, #32]
   4162e:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   41630:	4053      	eors	r3, r2
   41632:	210c      	movs	r1, #12
   41634:	4618      	mov	r0, r3
   41636:	f7ff faaf 	bl	40b98 <rotr32>
   4163a:	4603      	mov	r3, r0
   4163c:	623b      	str	r3, [r7, #32]
   4163e:	68fa      	ldr	r2, [r7, #12]
   41640:	6a3b      	ldr	r3, [r7, #32]
   41642:	441a      	add	r2, r3
   41644:	230c      	movs	r3, #12
   41646:	009b      	lsls	r3, r3, #2
   41648:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4164c:	440b      	add	r3, r1
   4164e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41652:	4413      	add	r3, r2
   41654:	60fb      	str	r3, [r7, #12]
   41656:	6cba      	ldr	r2, [r7, #72]	; 0x48
   41658:	68fb      	ldr	r3, [r7, #12]
   4165a:	4053      	eors	r3, r2
   4165c:	2108      	movs	r1, #8
   4165e:	4618      	mov	r0, r3
   41660:	f7ff fa9a 	bl	40b98 <rotr32>
   41664:	4603      	mov	r3, r0
   41666:	64bb      	str	r3, [r7, #72]	; 0x48
   41668:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   4166a:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   4166c:	4413      	add	r3, r2
   4166e:	637b      	str	r3, [r7, #52]	; 0x34
   41670:	6a3a      	ldr	r2, [r7, #32]
   41672:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   41674:	4053      	eors	r3, r2
   41676:	2107      	movs	r1, #7
   41678:	4618      	mov	r0, r3
   4167a:	f7ff fa8d 	bl	40b98 <rotr32>
   4167e:	4603      	mov	r3, r0
   41680:	623b      	str	r3, [r7, #32]
   41682:	693a      	ldr	r2, [r7, #16]
   41684:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   41686:	441a      	add	r2, r3
   41688:	2300      	movs	r3, #0
   4168a:	009b      	lsls	r3, r3, #2
   4168c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41690:	440b      	add	r3, r1
   41692:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41696:	4413      	add	r3, r2
   41698:	613b      	str	r3, [r7, #16]
   4169a:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   4169c:	693b      	ldr	r3, [r7, #16]
   4169e:	4053      	eors	r3, r2
   416a0:	2110      	movs	r1, #16
   416a2:	4618      	mov	r0, r3
   416a4:	f7ff fa78 	bl	40b98 <rotr32>
   416a8:	4603      	mov	r3, r0
   416aa:	63fb      	str	r3, [r7, #60]	; 0x3c
   416ac:	6bba      	ldr	r2, [r7, #56]	; 0x38
   416ae:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   416b0:	4413      	add	r3, r2
   416b2:	63bb      	str	r3, [r7, #56]	; 0x38
   416b4:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   416b6:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   416b8:	4053      	eors	r3, r2
   416ba:	210c      	movs	r1, #12
   416bc:	4618      	mov	r0, r3
   416be:	f7ff fa6b 	bl	40b98 <rotr32>
   416c2:	4603      	mov	r3, r0
   416c4:	627b      	str	r3, [r7, #36]	; 0x24
   416c6:	693a      	ldr	r2, [r7, #16]
   416c8:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   416ca:	441a      	add	r2, r3
   416cc:	2302      	movs	r3, #2
   416ce:	009b      	lsls	r3, r3, #2
   416d0:	f107 0190 	add.w	r1, r7, #144	; 0x90
   416d4:	440b      	add	r3, r1
   416d6:	f853 3c44 	ldr.w	r3, [r3, #-68]
   416da:	4413      	add	r3, r2
   416dc:	613b      	str	r3, [r7, #16]
   416de:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   416e0:	693b      	ldr	r3, [r7, #16]
   416e2:	4053      	eors	r3, r2
   416e4:	2108      	movs	r1, #8
   416e6:	4618      	mov	r0, r3
   416e8:	f7ff fa56 	bl	40b98 <rotr32>
   416ec:	4603      	mov	r3, r0
   416ee:	63fb      	str	r3, [r7, #60]	; 0x3c
   416f0:	6bba      	ldr	r2, [r7, #56]	; 0x38
   416f2:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   416f4:	4413      	add	r3, r2
   416f6:	63bb      	str	r3, [r7, #56]	; 0x38
   416f8:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   416fa:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   416fc:	4053      	eors	r3, r2
   416fe:	2107      	movs	r1, #7
   41700:	4618      	mov	r0, r3
   41702:	f7ff fa49 	bl	40b98 <rotr32>
   41706:	4603      	mov	r3, r0
   41708:	627b      	str	r3, [r7, #36]	; 0x24
   4170a:	697a      	ldr	r2, [r7, #20]
   4170c:	6abb      	ldr	r3, [r7, #40]	; 0x28
   4170e:	441a      	add	r2, r3
   41710:	230b      	movs	r3, #11
   41712:	009b      	lsls	r3, r3, #2
   41714:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41718:	440b      	add	r3, r1
   4171a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4171e:	4413      	add	r3, r2
   41720:	617b      	str	r3, [r7, #20]
   41722:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   41724:	697b      	ldr	r3, [r7, #20]
   41726:	4053      	eors	r3, r2
   41728:	2110      	movs	r1, #16
   4172a:	4618      	mov	r0, r3
   4172c:	f7ff fa34 	bl	40b98 <rotr32>
   41730:	4603      	mov	r3, r0
   41732:	643b      	str	r3, [r7, #64]	; 0x40
   41734:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   41736:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   41738:	4413      	add	r3, r2
   4173a:	62fb      	str	r3, [r7, #44]	; 0x2c
   4173c:	6aba      	ldr	r2, [r7, #40]	; 0x28
   4173e:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   41740:	4053      	eors	r3, r2
   41742:	210c      	movs	r1, #12
   41744:	4618      	mov	r0, r3
   41746:	f7ff fa27 	bl	40b98 <rotr32>
   4174a:	4603      	mov	r3, r0
   4174c:	62bb      	str	r3, [r7, #40]	; 0x28
   4174e:	697a      	ldr	r2, [r7, #20]
   41750:	6abb      	ldr	r3, [r7, #40]	; 0x28
   41752:	441a      	add	r2, r3
   41754:	2307      	movs	r3, #7
   41756:	009b      	lsls	r3, r3, #2
   41758:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4175c:	440b      	add	r3, r1
   4175e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41762:	4413      	add	r3, r2
   41764:	617b      	str	r3, [r7, #20]
   41766:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   41768:	697b      	ldr	r3, [r7, #20]
   4176a:	4053      	eors	r3, r2
   4176c:	2108      	movs	r1, #8
   4176e:	4618      	mov	r0, r3
   41770:	f7ff fa12 	bl	40b98 <rotr32>
   41774:	4603      	mov	r3, r0
   41776:	643b      	str	r3, [r7, #64]	; 0x40
   41778:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   4177a:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   4177c:	4413      	add	r3, r2
   4177e:	62fb      	str	r3, [r7, #44]	; 0x2c
   41780:	6aba      	ldr	r2, [r7, #40]	; 0x28
   41782:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   41784:	4053      	eors	r3, r2
   41786:	2107      	movs	r1, #7
   41788:	4618      	mov	r0, r3
   4178a:	f7ff fa05 	bl	40b98 <rotr32>
   4178e:	4603      	mov	r3, r0
   41790:	62bb      	str	r3, [r7, #40]	; 0x28
   41792:	69ba      	ldr	r2, [r7, #24]
   41794:	69fb      	ldr	r3, [r7, #28]
   41796:	441a      	add	r2, r3
   41798:	2305      	movs	r3, #5
   4179a:	009b      	lsls	r3, r3, #2
   4179c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   417a0:	440b      	add	r3, r1
   417a2:	f853 3c44 	ldr.w	r3, [r3, #-68]
   417a6:	4413      	add	r3, r2
   417a8:	61bb      	str	r3, [r7, #24]
   417aa:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   417ac:	69bb      	ldr	r3, [r7, #24]
   417ae:	4053      	eors	r3, r2
   417b0:	2110      	movs	r1, #16
   417b2:	4618      	mov	r0, r3
   417b4:	f7ff f9f0 	bl	40b98 <rotr32>
   417b8:	4603      	mov	r3, r0
   417ba:	647b      	str	r3, [r7, #68]	; 0x44
   417bc:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   417be:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   417c0:	4413      	add	r3, r2
   417c2:	633b      	str	r3, [r7, #48]	; 0x30
   417c4:	69fa      	ldr	r2, [r7, #28]
   417c6:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   417c8:	4053      	eors	r3, r2
   417ca:	210c      	movs	r1, #12
   417cc:	4618      	mov	r0, r3
   417ce:	f7ff f9e3 	bl	40b98 <rotr32>
   417d2:	4603      	mov	r3, r0
   417d4:	61fb      	str	r3, [r7, #28]
   417d6:	69ba      	ldr	r2, [r7, #24]
   417d8:	69fb      	ldr	r3, [r7, #28]
   417da:	441a      	add	r2, r3
   417dc:	2303      	movs	r3, #3
   417de:	009b      	lsls	r3, r3, #2
   417e0:	f107 0190 	add.w	r1, r7, #144	; 0x90
   417e4:	440b      	add	r3, r1
   417e6:	f853 3c44 	ldr.w	r3, [r3, #-68]
   417ea:	4413      	add	r3, r2
   417ec:	61bb      	str	r3, [r7, #24]
   417ee:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   417f0:	69bb      	ldr	r3, [r7, #24]
   417f2:	4053      	eors	r3, r2
   417f4:	2108      	movs	r1, #8
   417f6:	4618      	mov	r0, r3
   417f8:	f7ff f9ce 	bl	40b98 <rotr32>
   417fc:	4603      	mov	r3, r0
   417fe:	647b      	str	r3, [r7, #68]	; 0x44
   41800:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   41802:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   41804:	4413      	add	r3, r2
   41806:	633b      	str	r3, [r7, #48]	; 0x30
   41808:	69fa      	ldr	r2, [r7, #28]
   4180a:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   4180c:	4053      	eors	r3, r2
   4180e:	2107      	movs	r1, #7
   41810:	4618      	mov	r0, r3
   41812:	f7ff f9c1 	bl	40b98 <rotr32>
   41816:	4603      	mov	r3, r0
   41818:	61fb      	str	r3, [r7, #28]
   4181a:	68fa      	ldr	r2, [r7, #12]
   4181c:	69fb      	ldr	r3, [r7, #28]
   4181e:	441a      	add	r2, r3
   41820:	230b      	movs	r3, #11
   41822:	009b      	lsls	r3, r3, #2
   41824:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41828:	440b      	add	r3, r1
   4182a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4182e:	4413      	add	r3, r2
   41830:	60fb      	str	r3, [r7, #12]
   41832:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   41834:	68fb      	ldr	r3, [r7, #12]
   41836:	4053      	eors	r3, r2
   41838:	2110      	movs	r1, #16
   4183a:	4618      	mov	r0, r3
   4183c:	f7ff f9ac 	bl	40b98 <rotr32>
   41840:	4603      	mov	r3, r0
   41842:	63fb      	str	r3, [r7, #60]	; 0x3c
   41844:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   41846:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   41848:	4413      	add	r3, r2
   4184a:	62fb      	str	r3, [r7, #44]	; 0x2c
   4184c:	69fa      	ldr	r2, [r7, #28]
   4184e:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   41850:	4053      	eors	r3, r2
   41852:	210c      	movs	r1, #12
   41854:	4618      	mov	r0, r3
   41856:	f7ff f99f 	bl	40b98 <rotr32>
   4185a:	4603      	mov	r3, r0
   4185c:	61fb      	str	r3, [r7, #28]
   4185e:	68fa      	ldr	r2, [r7, #12]
   41860:	69fb      	ldr	r3, [r7, #28]
   41862:	441a      	add	r2, r3
   41864:	2308      	movs	r3, #8
   41866:	009b      	lsls	r3, r3, #2
   41868:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4186c:	440b      	add	r3, r1
   4186e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41872:	4413      	add	r3, r2
   41874:	60fb      	str	r3, [r7, #12]
   41876:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   41878:	68fb      	ldr	r3, [r7, #12]
   4187a:	4053      	eors	r3, r2
   4187c:	2108      	movs	r1, #8
   4187e:	4618      	mov	r0, r3
   41880:	f7ff f98a 	bl	40b98 <rotr32>
   41884:	4603      	mov	r3, r0
   41886:	63fb      	str	r3, [r7, #60]	; 0x3c
   41888:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   4188a:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   4188c:	4413      	add	r3, r2
   4188e:	62fb      	str	r3, [r7, #44]	; 0x2c
   41890:	69fa      	ldr	r2, [r7, #28]
   41892:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   41894:	4053      	eors	r3, r2
   41896:	2107      	movs	r1, #7
   41898:	4618      	mov	r0, r3
   4189a:	f7ff f97d 	bl	40b98 <rotr32>
   4189e:	4603      	mov	r3, r0
   418a0:	61fb      	str	r3, [r7, #28]
   418a2:	693a      	ldr	r2, [r7, #16]
   418a4:	6a3b      	ldr	r3, [r7, #32]
   418a6:	441a      	add	r2, r3
   418a8:	230c      	movs	r3, #12
   418aa:	009b      	lsls	r3, r3, #2
   418ac:	f107 0190 	add.w	r1, r7, #144	; 0x90
   418b0:	440b      	add	r3, r1
   418b2:	f853 3c44 	ldr.w	r3, [r3, #-68]
   418b6:	4413      	add	r3, r2
   418b8:	613b      	str	r3, [r7, #16]
   418ba:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   418bc:	693b      	ldr	r3, [r7, #16]
   418be:	4053      	eors	r3, r2
   418c0:	2110      	movs	r1, #16
   418c2:	4618      	mov	r0, r3
   418c4:	f7ff f968 	bl	40b98 <rotr32>
   418c8:	4603      	mov	r3, r0
   418ca:	643b      	str	r3, [r7, #64]	; 0x40
   418cc:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   418ce:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   418d0:	4413      	add	r3, r2
   418d2:	633b      	str	r3, [r7, #48]	; 0x30
   418d4:	6a3a      	ldr	r2, [r7, #32]
   418d6:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   418d8:	4053      	eors	r3, r2
   418da:	210c      	movs	r1, #12
   418dc:	4618      	mov	r0, r3
   418de:	f7ff f95b 	bl	40b98 <rotr32>
   418e2:	4603      	mov	r3, r0
   418e4:	623b      	str	r3, [r7, #32]
   418e6:	693a      	ldr	r2, [r7, #16]
   418e8:	6a3b      	ldr	r3, [r7, #32]
   418ea:	441a      	add	r2, r3
   418ec:	2300      	movs	r3, #0
   418ee:	009b      	lsls	r3, r3, #2
   418f0:	f107 0190 	add.w	r1, r7, #144	; 0x90
   418f4:	440b      	add	r3, r1
   418f6:	f853 3c44 	ldr.w	r3, [r3, #-68]
   418fa:	4413      	add	r3, r2
   418fc:	613b      	str	r3, [r7, #16]
   418fe:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   41900:	693b      	ldr	r3, [r7, #16]
   41902:	4053      	eors	r3, r2
   41904:	2108      	movs	r1, #8
   41906:	4618      	mov	r0, r3
   41908:	f7ff f946 	bl	40b98 <rotr32>
   4190c:	4603      	mov	r3, r0
   4190e:	643b      	str	r3, [r7, #64]	; 0x40
   41910:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   41912:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   41914:	4413      	add	r3, r2
   41916:	633b      	str	r3, [r7, #48]	; 0x30
   41918:	6a3a      	ldr	r2, [r7, #32]
   4191a:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   4191c:	4053      	eors	r3, r2
   4191e:	2107      	movs	r1, #7
   41920:	4618      	mov	r0, r3
   41922:	f7ff f939 	bl	40b98 <rotr32>
   41926:	4603      	mov	r3, r0
   41928:	623b      	str	r3, [r7, #32]
   4192a:	697a      	ldr	r2, [r7, #20]
   4192c:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   4192e:	441a      	add	r2, r3
   41930:	2305      	movs	r3, #5
   41932:	009b      	lsls	r3, r3, #2
   41934:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41938:	440b      	add	r3, r1
   4193a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4193e:	4413      	add	r3, r2
   41940:	617b      	str	r3, [r7, #20]
   41942:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   41944:	697b      	ldr	r3, [r7, #20]
   41946:	4053      	eors	r3, r2
   41948:	2110      	movs	r1, #16
   4194a:	4618      	mov	r0, r3
   4194c:	f7ff f924 	bl	40b98 <rotr32>
   41950:	4603      	mov	r3, r0
   41952:	647b      	str	r3, [r7, #68]	; 0x44
   41954:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   41956:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   41958:	4413      	add	r3, r2
   4195a:	637b      	str	r3, [r7, #52]	; 0x34
   4195c:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   4195e:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   41960:	4053      	eors	r3, r2
   41962:	210c      	movs	r1, #12
   41964:	4618      	mov	r0, r3
   41966:	f7ff f917 	bl	40b98 <rotr32>
   4196a:	4603      	mov	r3, r0
   4196c:	627b      	str	r3, [r7, #36]	; 0x24
   4196e:	697a      	ldr	r2, [r7, #20]
   41970:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   41972:	441a      	add	r2, r3
   41974:	2302      	movs	r3, #2
   41976:	009b      	lsls	r3, r3, #2
   41978:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4197c:	440b      	add	r3, r1
   4197e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41982:	4413      	add	r3, r2
   41984:	617b      	str	r3, [r7, #20]
   41986:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   41988:	697b      	ldr	r3, [r7, #20]
   4198a:	4053      	eors	r3, r2
   4198c:	2108      	movs	r1, #8
   4198e:	4618      	mov	r0, r3
   41990:	f7ff f902 	bl	40b98 <rotr32>
   41994:	4603      	mov	r3, r0
   41996:	647b      	str	r3, [r7, #68]	; 0x44
   41998:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   4199a:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   4199c:	4413      	add	r3, r2
   4199e:	637b      	str	r3, [r7, #52]	; 0x34
   419a0:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   419a2:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   419a4:	4053      	eors	r3, r2
   419a6:	2107      	movs	r1, #7
   419a8:	4618      	mov	r0, r3
   419aa:	f7ff f8f5 	bl	40b98 <rotr32>
   419ae:	4603      	mov	r3, r0
   419b0:	627b      	str	r3, [r7, #36]	; 0x24
   419b2:	69ba      	ldr	r2, [r7, #24]
   419b4:	6abb      	ldr	r3, [r7, #40]	; 0x28
   419b6:	441a      	add	r2, r3
   419b8:	230f      	movs	r3, #15
   419ba:	009b      	lsls	r3, r3, #2
   419bc:	f107 0190 	add.w	r1, r7, #144	; 0x90
   419c0:	440b      	add	r3, r1
   419c2:	f853 3c44 	ldr.w	r3, [r3, #-68]
   419c6:	4413      	add	r3, r2
   419c8:	61bb      	str	r3, [r7, #24]
   419ca:	6cba      	ldr	r2, [r7, #72]	; 0x48
   419cc:	69bb      	ldr	r3, [r7, #24]
   419ce:	4053      	eors	r3, r2
   419d0:	2110      	movs	r1, #16
   419d2:	4618      	mov	r0, r3
   419d4:	f7ff f8e0 	bl	40b98 <rotr32>
   419d8:	4603      	mov	r3, r0
   419da:	64bb      	str	r3, [r7, #72]	; 0x48
   419dc:	6bba      	ldr	r2, [r7, #56]	; 0x38
   419de:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   419e0:	4413      	add	r3, r2
   419e2:	63bb      	str	r3, [r7, #56]	; 0x38
   419e4:	6aba      	ldr	r2, [r7, #40]	; 0x28
   419e6:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   419e8:	4053      	eors	r3, r2
   419ea:	210c      	movs	r1, #12
   419ec:	4618      	mov	r0, r3
   419ee:	f7ff f8d3 	bl	40b98 <rotr32>
   419f2:	4603      	mov	r3, r0
   419f4:	62bb      	str	r3, [r7, #40]	; 0x28
   419f6:	69ba      	ldr	r2, [r7, #24]
   419f8:	6abb      	ldr	r3, [r7, #40]	; 0x28
   419fa:	441a      	add	r2, r3
   419fc:	230d      	movs	r3, #13
   419fe:	009b      	lsls	r3, r3, #2
   41a00:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41a04:	440b      	add	r3, r1
   41a06:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41a0a:	4413      	add	r3, r2
   41a0c:	61bb      	str	r3, [r7, #24]
   41a0e:	6cba      	ldr	r2, [r7, #72]	; 0x48
   41a10:	69bb      	ldr	r3, [r7, #24]
   41a12:	4053      	eors	r3, r2
   41a14:	2108      	movs	r1, #8
   41a16:	4618      	mov	r0, r3
   41a18:	f7ff f8be 	bl	40b98 <rotr32>
   41a1c:	4603      	mov	r3, r0
   41a1e:	64bb      	str	r3, [r7, #72]	; 0x48
   41a20:	6bba      	ldr	r2, [r7, #56]	; 0x38
   41a22:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   41a24:	4413      	add	r3, r2
   41a26:	63bb      	str	r3, [r7, #56]	; 0x38
   41a28:	6aba      	ldr	r2, [r7, #40]	; 0x28
   41a2a:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   41a2c:	4053      	eors	r3, r2
   41a2e:	2107      	movs	r1, #7
   41a30:	4618      	mov	r0, r3
   41a32:	f7ff f8b1 	bl	40b98 <rotr32>
   41a36:	4603      	mov	r3, r0
   41a38:	62bb      	str	r3, [r7, #40]	; 0x28
   41a3a:	68fa      	ldr	r2, [r7, #12]
   41a3c:	6a3b      	ldr	r3, [r7, #32]
   41a3e:	441a      	add	r2, r3
   41a40:	230a      	movs	r3, #10
   41a42:	009b      	lsls	r3, r3, #2
   41a44:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41a48:	440b      	add	r3, r1
   41a4a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41a4e:	4413      	add	r3, r2
   41a50:	60fb      	str	r3, [r7, #12]
   41a52:	6cba      	ldr	r2, [r7, #72]	; 0x48
   41a54:	68fb      	ldr	r3, [r7, #12]
   41a56:	4053      	eors	r3, r2
   41a58:	2110      	movs	r1, #16
   41a5a:	4618      	mov	r0, r3
   41a5c:	f7ff f89c 	bl	40b98 <rotr32>
   41a60:	4603      	mov	r3, r0
   41a62:	64bb      	str	r3, [r7, #72]	; 0x48
   41a64:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   41a66:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   41a68:	4413      	add	r3, r2
   41a6a:	637b      	str	r3, [r7, #52]	; 0x34
   41a6c:	6a3a      	ldr	r2, [r7, #32]
   41a6e:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   41a70:	4053      	eors	r3, r2
   41a72:	210c      	movs	r1, #12
   41a74:	4618      	mov	r0, r3
   41a76:	f7ff f88f 	bl	40b98 <rotr32>
   41a7a:	4603      	mov	r3, r0
   41a7c:	623b      	str	r3, [r7, #32]
   41a7e:	68fa      	ldr	r2, [r7, #12]
   41a80:	6a3b      	ldr	r3, [r7, #32]
   41a82:	441a      	add	r2, r3
   41a84:	230e      	movs	r3, #14
   41a86:	009b      	lsls	r3, r3, #2
   41a88:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41a8c:	440b      	add	r3, r1
   41a8e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41a92:	4413      	add	r3, r2
   41a94:	60fb      	str	r3, [r7, #12]
   41a96:	6cba      	ldr	r2, [r7, #72]	; 0x48
   41a98:	68fb      	ldr	r3, [r7, #12]
   41a9a:	4053      	eors	r3, r2
   41a9c:	2108      	movs	r1, #8
   41a9e:	4618      	mov	r0, r3
   41aa0:	f7ff f87a 	bl	40b98 <rotr32>
   41aa4:	4603      	mov	r3, r0
   41aa6:	64bb      	str	r3, [r7, #72]	; 0x48
   41aa8:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   41aaa:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   41aac:	4413      	add	r3, r2
   41aae:	637b      	str	r3, [r7, #52]	; 0x34
   41ab0:	6a3a      	ldr	r2, [r7, #32]
   41ab2:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   41ab4:	4053      	eors	r3, r2
   41ab6:	2107      	movs	r1, #7
   41ab8:	4618      	mov	r0, r3
   41aba:	f7ff f86d 	bl	40b98 <rotr32>
   41abe:	4603      	mov	r3, r0
   41ac0:	623b      	str	r3, [r7, #32]
   41ac2:	693a      	ldr	r2, [r7, #16]
   41ac4:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   41ac6:	441a      	add	r2, r3
   41ac8:	2303      	movs	r3, #3
   41aca:	009b      	lsls	r3, r3, #2
   41acc:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41ad0:	440b      	add	r3, r1
   41ad2:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41ad6:	4413      	add	r3, r2
   41ad8:	613b      	str	r3, [r7, #16]
   41ada:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   41adc:	693b      	ldr	r3, [r7, #16]
   41ade:	4053      	eors	r3, r2
   41ae0:	2110      	movs	r1, #16
   41ae2:	4618      	mov	r0, r3
   41ae4:	f7ff f858 	bl	40b98 <rotr32>
   41ae8:	4603      	mov	r3, r0
   41aea:	63fb      	str	r3, [r7, #60]	; 0x3c
   41aec:	6bba      	ldr	r2, [r7, #56]	; 0x38
   41aee:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   41af0:	4413      	add	r3, r2
   41af2:	63bb      	str	r3, [r7, #56]	; 0x38
   41af4:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   41af6:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   41af8:	4053      	eors	r3, r2
   41afa:	210c      	movs	r1, #12
   41afc:	4618      	mov	r0, r3
   41afe:	f7ff f84b 	bl	40b98 <rotr32>
   41b02:	4603      	mov	r3, r0
   41b04:	627b      	str	r3, [r7, #36]	; 0x24
   41b06:	693a      	ldr	r2, [r7, #16]
   41b08:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   41b0a:	441a      	add	r2, r3
   41b0c:	2306      	movs	r3, #6
   41b0e:	009b      	lsls	r3, r3, #2
   41b10:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41b14:	440b      	add	r3, r1
   41b16:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41b1a:	4413      	add	r3, r2
   41b1c:	613b      	str	r3, [r7, #16]
   41b1e:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   41b20:	693b      	ldr	r3, [r7, #16]
   41b22:	4053      	eors	r3, r2
   41b24:	2108      	movs	r1, #8
   41b26:	4618      	mov	r0, r3
   41b28:	f7ff f836 	bl	40b98 <rotr32>
   41b2c:	4603      	mov	r3, r0
   41b2e:	63fb      	str	r3, [r7, #60]	; 0x3c
   41b30:	6bba      	ldr	r2, [r7, #56]	; 0x38
   41b32:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   41b34:	4413      	add	r3, r2
   41b36:	63bb      	str	r3, [r7, #56]	; 0x38
   41b38:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   41b3a:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   41b3c:	4053      	eors	r3, r2
   41b3e:	2107      	movs	r1, #7
   41b40:	4618      	mov	r0, r3
   41b42:	f7ff f829 	bl	40b98 <rotr32>
   41b46:	4603      	mov	r3, r0
   41b48:	627b      	str	r3, [r7, #36]	; 0x24
   41b4a:	697a      	ldr	r2, [r7, #20]
   41b4c:	6abb      	ldr	r3, [r7, #40]	; 0x28
   41b4e:	441a      	add	r2, r3
   41b50:	2307      	movs	r3, #7
   41b52:	009b      	lsls	r3, r3, #2
   41b54:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41b58:	440b      	add	r3, r1
   41b5a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41b5e:	4413      	add	r3, r2
   41b60:	617b      	str	r3, [r7, #20]
   41b62:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   41b64:	697b      	ldr	r3, [r7, #20]
   41b66:	4053      	eors	r3, r2
   41b68:	2110      	movs	r1, #16
   41b6a:	4618      	mov	r0, r3
   41b6c:	f7ff f814 	bl	40b98 <rotr32>
   41b70:	4603      	mov	r3, r0
   41b72:	643b      	str	r3, [r7, #64]	; 0x40
   41b74:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   41b76:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   41b78:	4413      	add	r3, r2
   41b7a:	62fb      	str	r3, [r7, #44]	; 0x2c
   41b7c:	6aba      	ldr	r2, [r7, #40]	; 0x28
   41b7e:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   41b80:	4053      	eors	r3, r2
   41b82:	210c      	movs	r1, #12
   41b84:	4618      	mov	r0, r3
   41b86:	f7ff f807 	bl	40b98 <rotr32>
   41b8a:	4603      	mov	r3, r0
   41b8c:	62bb      	str	r3, [r7, #40]	; 0x28
   41b8e:	697a      	ldr	r2, [r7, #20]
   41b90:	6abb      	ldr	r3, [r7, #40]	; 0x28
   41b92:	441a      	add	r2, r3
   41b94:	2301      	movs	r3, #1
   41b96:	009b      	lsls	r3, r3, #2
   41b98:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41b9c:	440b      	add	r3, r1
   41b9e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41ba2:	4413      	add	r3, r2
   41ba4:	617b      	str	r3, [r7, #20]
   41ba6:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   41ba8:	697b      	ldr	r3, [r7, #20]
   41baa:	4053      	eors	r3, r2
   41bac:	2108      	movs	r1, #8
   41bae:	4618      	mov	r0, r3
   41bb0:	f7fe fff2 	bl	40b98 <rotr32>
   41bb4:	4603      	mov	r3, r0
   41bb6:	643b      	str	r3, [r7, #64]	; 0x40
   41bb8:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   41bba:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   41bbc:	4413      	add	r3, r2
   41bbe:	62fb      	str	r3, [r7, #44]	; 0x2c
   41bc0:	6aba      	ldr	r2, [r7, #40]	; 0x28
   41bc2:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   41bc4:	4053      	eors	r3, r2
   41bc6:	2107      	movs	r1, #7
   41bc8:	4618      	mov	r0, r3
   41bca:	f7fe ffe5 	bl	40b98 <rotr32>
   41bce:	4603      	mov	r3, r0
   41bd0:	62bb      	str	r3, [r7, #40]	; 0x28
   41bd2:	69ba      	ldr	r2, [r7, #24]
   41bd4:	69fb      	ldr	r3, [r7, #28]
   41bd6:	441a      	add	r2, r3
   41bd8:	2309      	movs	r3, #9
   41bda:	009b      	lsls	r3, r3, #2
   41bdc:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41be0:	440b      	add	r3, r1
   41be2:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41be6:	4413      	add	r3, r2
   41be8:	61bb      	str	r3, [r7, #24]
   41bea:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   41bec:	69bb      	ldr	r3, [r7, #24]
   41bee:	4053      	eors	r3, r2
   41bf0:	2110      	movs	r1, #16
   41bf2:	4618      	mov	r0, r3
   41bf4:	f7fe ffd0 	bl	40b98 <rotr32>
   41bf8:	4603      	mov	r3, r0
   41bfa:	647b      	str	r3, [r7, #68]	; 0x44
   41bfc:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   41bfe:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   41c00:	4413      	add	r3, r2
   41c02:	633b      	str	r3, [r7, #48]	; 0x30
   41c04:	69fa      	ldr	r2, [r7, #28]
   41c06:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   41c08:	4053      	eors	r3, r2
   41c0a:	210c      	movs	r1, #12
   41c0c:	4618      	mov	r0, r3
   41c0e:	f7fe ffc3 	bl	40b98 <rotr32>
   41c12:	4603      	mov	r3, r0
   41c14:	61fb      	str	r3, [r7, #28]
   41c16:	69ba      	ldr	r2, [r7, #24]
   41c18:	69fb      	ldr	r3, [r7, #28]
   41c1a:	441a      	add	r2, r3
   41c1c:	2304      	movs	r3, #4
   41c1e:	009b      	lsls	r3, r3, #2
   41c20:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41c24:	440b      	add	r3, r1
   41c26:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41c2a:	4413      	add	r3, r2
   41c2c:	61bb      	str	r3, [r7, #24]
   41c2e:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   41c30:	69bb      	ldr	r3, [r7, #24]
   41c32:	4053      	eors	r3, r2
   41c34:	2108      	movs	r1, #8
   41c36:	4618      	mov	r0, r3
   41c38:	f7fe ffae 	bl	40b98 <rotr32>
   41c3c:	4603      	mov	r3, r0
   41c3e:	647b      	str	r3, [r7, #68]	; 0x44
   41c40:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   41c42:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   41c44:	4413      	add	r3, r2
   41c46:	633b      	str	r3, [r7, #48]	; 0x30
   41c48:	69fa      	ldr	r2, [r7, #28]
   41c4a:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   41c4c:	4053      	eors	r3, r2
   41c4e:	2107      	movs	r1, #7
   41c50:	4618      	mov	r0, r3
   41c52:	f7fe ffa1 	bl	40b98 <rotr32>
   41c56:	4603      	mov	r3, r0
   41c58:	61fb      	str	r3, [r7, #28]
   41c5a:	68fa      	ldr	r2, [r7, #12]
   41c5c:	69fb      	ldr	r3, [r7, #28]
   41c5e:	441a      	add	r2, r3
   41c60:	2307      	movs	r3, #7
   41c62:	009b      	lsls	r3, r3, #2
   41c64:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41c68:	440b      	add	r3, r1
   41c6a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41c6e:	4413      	add	r3, r2
   41c70:	60fb      	str	r3, [r7, #12]
   41c72:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   41c74:	68fb      	ldr	r3, [r7, #12]
   41c76:	4053      	eors	r3, r2
   41c78:	2110      	movs	r1, #16
   41c7a:	4618      	mov	r0, r3
   41c7c:	f7fe ff8c 	bl	40b98 <rotr32>
   41c80:	4603      	mov	r3, r0
   41c82:	63fb      	str	r3, [r7, #60]	; 0x3c
   41c84:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   41c86:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   41c88:	4413      	add	r3, r2
   41c8a:	62fb      	str	r3, [r7, #44]	; 0x2c
   41c8c:	69fa      	ldr	r2, [r7, #28]
   41c8e:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   41c90:	4053      	eors	r3, r2
   41c92:	210c      	movs	r1, #12
   41c94:	4618      	mov	r0, r3
   41c96:	f7fe ff7f 	bl	40b98 <rotr32>
   41c9a:	4603      	mov	r3, r0
   41c9c:	61fb      	str	r3, [r7, #28]
   41c9e:	68fa      	ldr	r2, [r7, #12]
   41ca0:	69fb      	ldr	r3, [r7, #28]
   41ca2:	441a      	add	r2, r3
   41ca4:	2309      	movs	r3, #9
   41ca6:	009b      	lsls	r3, r3, #2
   41ca8:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41cac:	440b      	add	r3, r1
   41cae:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41cb2:	4413      	add	r3, r2
   41cb4:	60fb      	str	r3, [r7, #12]
   41cb6:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   41cb8:	68fb      	ldr	r3, [r7, #12]
   41cba:	4053      	eors	r3, r2
   41cbc:	2108      	movs	r1, #8
   41cbe:	4618      	mov	r0, r3
   41cc0:	f7fe ff6a 	bl	40b98 <rotr32>
   41cc4:	4603      	mov	r3, r0
   41cc6:	63fb      	str	r3, [r7, #60]	; 0x3c
   41cc8:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   41cca:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   41ccc:	4413      	add	r3, r2
   41cce:	62fb      	str	r3, [r7, #44]	; 0x2c
   41cd0:	69fa      	ldr	r2, [r7, #28]
   41cd2:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   41cd4:	4053      	eors	r3, r2
   41cd6:	2107      	movs	r1, #7
   41cd8:	4618      	mov	r0, r3
   41cda:	f7fe ff5d 	bl	40b98 <rotr32>
   41cde:	4603      	mov	r3, r0
   41ce0:	61fb      	str	r3, [r7, #28]
   41ce2:	693a      	ldr	r2, [r7, #16]
   41ce4:	6a3b      	ldr	r3, [r7, #32]
   41ce6:	441a      	add	r2, r3
   41ce8:	2303      	movs	r3, #3
   41cea:	009b      	lsls	r3, r3, #2
   41cec:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41cf0:	440b      	add	r3, r1
   41cf2:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41cf6:	4413      	add	r3, r2
   41cf8:	613b      	str	r3, [r7, #16]
   41cfa:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   41cfc:	693b      	ldr	r3, [r7, #16]
   41cfe:	4053      	eors	r3, r2
   41d00:	2110      	movs	r1, #16
   41d02:	4618      	mov	r0, r3
   41d04:	f7fe ff48 	bl	40b98 <rotr32>
   41d08:	4603      	mov	r3, r0
   41d0a:	643b      	str	r3, [r7, #64]	; 0x40
   41d0c:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   41d0e:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   41d10:	4413      	add	r3, r2
   41d12:	633b      	str	r3, [r7, #48]	; 0x30
   41d14:	6a3a      	ldr	r2, [r7, #32]
   41d16:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   41d18:	4053      	eors	r3, r2
   41d1a:	210c      	movs	r1, #12
   41d1c:	4618      	mov	r0, r3
   41d1e:	f7fe ff3b 	bl	40b98 <rotr32>
   41d22:	4603      	mov	r3, r0
   41d24:	623b      	str	r3, [r7, #32]
   41d26:	693a      	ldr	r2, [r7, #16]
   41d28:	6a3b      	ldr	r3, [r7, #32]
   41d2a:	441a      	add	r2, r3
   41d2c:	2301      	movs	r3, #1
   41d2e:	009b      	lsls	r3, r3, #2
   41d30:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41d34:	440b      	add	r3, r1
   41d36:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41d3a:	4413      	add	r3, r2
   41d3c:	613b      	str	r3, [r7, #16]
   41d3e:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   41d40:	693b      	ldr	r3, [r7, #16]
   41d42:	4053      	eors	r3, r2
   41d44:	2108      	movs	r1, #8
   41d46:	4618      	mov	r0, r3
   41d48:	f7fe ff26 	bl	40b98 <rotr32>
   41d4c:	4603      	mov	r3, r0
   41d4e:	643b      	str	r3, [r7, #64]	; 0x40
   41d50:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   41d52:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   41d54:	4413      	add	r3, r2
   41d56:	633b      	str	r3, [r7, #48]	; 0x30
   41d58:	6a3a      	ldr	r2, [r7, #32]
   41d5a:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   41d5c:	4053      	eors	r3, r2
   41d5e:	2107      	movs	r1, #7
   41d60:	4618      	mov	r0, r3
   41d62:	f7fe ff19 	bl	40b98 <rotr32>
   41d66:	4603      	mov	r3, r0
   41d68:	623b      	str	r3, [r7, #32]
   41d6a:	697a      	ldr	r2, [r7, #20]
   41d6c:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   41d6e:	441a      	add	r2, r3
   41d70:	230d      	movs	r3, #13
   41d72:	009b      	lsls	r3, r3, #2
   41d74:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41d78:	440b      	add	r3, r1
   41d7a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41d7e:	4413      	add	r3, r2
   41d80:	617b      	str	r3, [r7, #20]
   41d82:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   41d84:	697b      	ldr	r3, [r7, #20]
   41d86:	4053      	eors	r3, r2
   41d88:	2110      	movs	r1, #16
   41d8a:	4618      	mov	r0, r3
   41d8c:	f7fe ff04 	bl	40b98 <rotr32>
   41d90:	4603      	mov	r3, r0
   41d92:	647b      	str	r3, [r7, #68]	; 0x44
   41d94:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   41d96:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   41d98:	4413      	add	r3, r2
   41d9a:	637b      	str	r3, [r7, #52]	; 0x34
   41d9c:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   41d9e:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   41da0:	4053      	eors	r3, r2
   41da2:	210c      	movs	r1, #12
   41da4:	4618      	mov	r0, r3
   41da6:	f7fe fef7 	bl	40b98 <rotr32>
   41daa:	4603      	mov	r3, r0
   41dac:	627b      	str	r3, [r7, #36]	; 0x24
   41dae:	697a      	ldr	r2, [r7, #20]
   41db0:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   41db2:	441a      	add	r2, r3
   41db4:	230c      	movs	r3, #12
   41db6:	009b      	lsls	r3, r3, #2
   41db8:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41dbc:	440b      	add	r3, r1
   41dbe:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41dc2:	4413      	add	r3, r2
   41dc4:	617b      	str	r3, [r7, #20]
   41dc6:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   41dc8:	697b      	ldr	r3, [r7, #20]
   41dca:	4053      	eors	r3, r2
   41dcc:	2108      	movs	r1, #8
   41dce:	4618      	mov	r0, r3
   41dd0:	f7fe fee2 	bl	40b98 <rotr32>
   41dd4:	4603      	mov	r3, r0
   41dd6:	647b      	str	r3, [r7, #68]	; 0x44
   41dd8:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   41dda:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   41ddc:	4413      	add	r3, r2
   41dde:	637b      	str	r3, [r7, #52]	; 0x34
   41de0:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   41de2:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   41de4:	4053      	eors	r3, r2
   41de6:	2107      	movs	r1, #7
   41de8:	4618      	mov	r0, r3
   41dea:	f7fe fed5 	bl	40b98 <rotr32>
   41dee:	4603      	mov	r3, r0
   41df0:	627b      	str	r3, [r7, #36]	; 0x24
   41df2:	69ba      	ldr	r2, [r7, #24]
   41df4:	6abb      	ldr	r3, [r7, #40]	; 0x28
   41df6:	441a      	add	r2, r3
   41df8:	230b      	movs	r3, #11
   41dfa:	009b      	lsls	r3, r3, #2
   41dfc:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41e00:	440b      	add	r3, r1
   41e02:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41e06:	4413      	add	r3, r2
   41e08:	61bb      	str	r3, [r7, #24]
   41e0a:	6cba      	ldr	r2, [r7, #72]	; 0x48
   41e0c:	69bb      	ldr	r3, [r7, #24]
   41e0e:	4053      	eors	r3, r2
   41e10:	2110      	movs	r1, #16
   41e12:	4618      	mov	r0, r3
   41e14:	f7fe fec0 	bl	40b98 <rotr32>
   41e18:	4603      	mov	r3, r0
   41e1a:	64bb      	str	r3, [r7, #72]	; 0x48
   41e1c:	6bba      	ldr	r2, [r7, #56]	; 0x38
   41e1e:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   41e20:	4413      	add	r3, r2
   41e22:	63bb      	str	r3, [r7, #56]	; 0x38
   41e24:	6aba      	ldr	r2, [r7, #40]	; 0x28
   41e26:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   41e28:	4053      	eors	r3, r2
   41e2a:	210c      	movs	r1, #12
   41e2c:	4618      	mov	r0, r3
   41e2e:	f7fe feb3 	bl	40b98 <rotr32>
   41e32:	4603      	mov	r3, r0
   41e34:	62bb      	str	r3, [r7, #40]	; 0x28
   41e36:	69ba      	ldr	r2, [r7, #24]
   41e38:	6abb      	ldr	r3, [r7, #40]	; 0x28
   41e3a:	441a      	add	r2, r3
   41e3c:	230e      	movs	r3, #14
   41e3e:	009b      	lsls	r3, r3, #2
   41e40:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41e44:	440b      	add	r3, r1
   41e46:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41e4a:	4413      	add	r3, r2
   41e4c:	61bb      	str	r3, [r7, #24]
   41e4e:	6cba      	ldr	r2, [r7, #72]	; 0x48
   41e50:	69bb      	ldr	r3, [r7, #24]
   41e52:	4053      	eors	r3, r2
   41e54:	2108      	movs	r1, #8
   41e56:	4618      	mov	r0, r3
   41e58:	f7fe fe9e 	bl	40b98 <rotr32>
   41e5c:	4603      	mov	r3, r0
   41e5e:	64bb      	str	r3, [r7, #72]	; 0x48
   41e60:	6bba      	ldr	r2, [r7, #56]	; 0x38
   41e62:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   41e64:	4413      	add	r3, r2
   41e66:	63bb      	str	r3, [r7, #56]	; 0x38
   41e68:	6aba      	ldr	r2, [r7, #40]	; 0x28
   41e6a:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   41e6c:	4053      	eors	r3, r2
   41e6e:	2107      	movs	r1, #7
   41e70:	4618      	mov	r0, r3
   41e72:	f7fe fe91 	bl	40b98 <rotr32>
   41e76:	4603      	mov	r3, r0
   41e78:	62bb      	str	r3, [r7, #40]	; 0x28
   41e7a:	68fa      	ldr	r2, [r7, #12]
   41e7c:	6a3b      	ldr	r3, [r7, #32]
   41e7e:	441a      	add	r2, r3
   41e80:	2302      	movs	r3, #2
   41e82:	009b      	lsls	r3, r3, #2
   41e84:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41e88:	440b      	add	r3, r1
   41e8a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41e8e:	4413      	add	r3, r2
   41e90:	60fb      	str	r3, [r7, #12]
   41e92:	6cba      	ldr	r2, [r7, #72]	; 0x48
   41e94:	68fb      	ldr	r3, [r7, #12]
   41e96:	4053      	eors	r3, r2
   41e98:	2110      	movs	r1, #16
   41e9a:	4618      	mov	r0, r3
   41e9c:	f7fe fe7c 	bl	40b98 <rotr32>
   41ea0:	4603      	mov	r3, r0
   41ea2:	64bb      	str	r3, [r7, #72]	; 0x48
   41ea4:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   41ea6:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   41ea8:	4413      	add	r3, r2
   41eaa:	637b      	str	r3, [r7, #52]	; 0x34
   41eac:	6a3a      	ldr	r2, [r7, #32]
   41eae:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   41eb0:	4053      	eors	r3, r2
   41eb2:	210c      	movs	r1, #12
   41eb4:	4618      	mov	r0, r3
   41eb6:	f7fe fe6f 	bl	40b98 <rotr32>
   41eba:	4603      	mov	r3, r0
   41ebc:	623b      	str	r3, [r7, #32]
   41ebe:	68fa      	ldr	r2, [r7, #12]
   41ec0:	6a3b      	ldr	r3, [r7, #32]
   41ec2:	441a      	add	r2, r3
   41ec4:	2306      	movs	r3, #6
   41ec6:	009b      	lsls	r3, r3, #2
   41ec8:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41ecc:	440b      	add	r3, r1
   41ece:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41ed2:	4413      	add	r3, r2
   41ed4:	60fb      	str	r3, [r7, #12]
   41ed6:	6cba      	ldr	r2, [r7, #72]	; 0x48
   41ed8:	68fb      	ldr	r3, [r7, #12]
   41eda:	4053      	eors	r3, r2
   41edc:	2108      	movs	r1, #8
   41ede:	4618      	mov	r0, r3
   41ee0:	f7fe fe5a 	bl	40b98 <rotr32>
   41ee4:	4603      	mov	r3, r0
   41ee6:	64bb      	str	r3, [r7, #72]	; 0x48
   41ee8:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   41eea:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   41eec:	4413      	add	r3, r2
   41eee:	637b      	str	r3, [r7, #52]	; 0x34
   41ef0:	6a3a      	ldr	r2, [r7, #32]
   41ef2:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   41ef4:	4053      	eors	r3, r2
   41ef6:	2107      	movs	r1, #7
   41ef8:	4618      	mov	r0, r3
   41efa:	f7fe fe4d 	bl	40b98 <rotr32>
   41efe:	4603      	mov	r3, r0
   41f00:	623b      	str	r3, [r7, #32]
   41f02:	693a      	ldr	r2, [r7, #16]
   41f04:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   41f06:	441a      	add	r2, r3
   41f08:	2305      	movs	r3, #5
   41f0a:	009b      	lsls	r3, r3, #2
   41f0c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41f10:	440b      	add	r3, r1
   41f12:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41f16:	4413      	add	r3, r2
   41f18:	613b      	str	r3, [r7, #16]
   41f1a:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   41f1c:	693b      	ldr	r3, [r7, #16]
   41f1e:	4053      	eors	r3, r2
   41f20:	2110      	movs	r1, #16
   41f22:	4618      	mov	r0, r3
   41f24:	f7fe fe38 	bl	40b98 <rotr32>
   41f28:	4603      	mov	r3, r0
   41f2a:	63fb      	str	r3, [r7, #60]	; 0x3c
   41f2c:	6bba      	ldr	r2, [r7, #56]	; 0x38
   41f2e:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   41f30:	4413      	add	r3, r2
   41f32:	63bb      	str	r3, [r7, #56]	; 0x38
   41f34:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   41f36:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   41f38:	4053      	eors	r3, r2
   41f3a:	210c      	movs	r1, #12
   41f3c:	4618      	mov	r0, r3
   41f3e:	f7fe fe2b 	bl	40b98 <rotr32>
   41f42:	4603      	mov	r3, r0
   41f44:	627b      	str	r3, [r7, #36]	; 0x24
   41f46:	693a      	ldr	r2, [r7, #16]
   41f48:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   41f4a:	441a      	add	r2, r3
   41f4c:	230a      	movs	r3, #10
   41f4e:	009b      	lsls	r3, r3, #2
   41f50:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41f54:	440b      	add	r3, r1
   41f56:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41f5a:	4413      	add	r3, r2
   41f5c:	613b      	str	r3, [r7, #16]
   41f5e:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   41f60:	693b      	ldr	r3, [r7, #16]
   41f62:	4053      	eors	r3, r2
   41f64:	2108      	movs	r1, #8
   41f66:	4618      	mov	r0, r3
   41f68:	f7fe fe16 	bl	40b98 <rotr32>
   41f6c:	4603      	mov	r3, r0
   41f6e:	63fb      	str	r3, [r7, #60]	; 0x3c
   41f70:	6bba      	ldr	r2, [r7, #56]	; 0x38
   41f72:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   41f74:	4413      	add	r3, r2
   41f76:	63bb      	str	r3, [r7, #56]	; 0x38
   41f78:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   41f7a:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   41f7c:	4053      	eors	r3, r2
   41f7e:	2107      	movs	r1, #7
   41f80:	4618      	mov	r0, r3
   41f82:	f7fe fe09 	bl	40b98 <rotr32>
   41f86:	4603      	mov	r3, r0
   41f88:	627b      	str	r3, [r7, #36]	; 0x24
   41f8a:	697a      	ldr	r2, [r7, #20]
   41f8c:	6abb      	ldr	r3, [r7, #40]	; 0x28
   41f8e:	441a      	add	r2, r3
   41f90:	2304      	movs	r3, #4
   41f92:	009b      	lsls	r3, r3, #2
   41f94:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41f98:	440b      	add	r3, r1
   41f9a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41f9e:	4413      	add	r3, r2
   41fa0:	617b      	str	r3, [r7, #20]
   41fa2:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   41fa4:	697b      	ldr	r3, [r7, #20]
   41fa6:	4053      	eors	r3, r2
   41fa8:	2110      	movs	r1, #16
   41faa:	4618      	mov	r0, r3
   41fac:	f7fe fdf4 	bl	40b98 <rotr32>
   41fb0:	4603      	mov	r3, r0
   41fb2:	643b      	str	r3, [r7, #64]	; 0x40
   41fb4:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   41fb6:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   41fb8:	4413      	add	r3, r2
   41fba:	62fb      	str	r3, [r7, #44]	; 0x2c
   41fbc:	6aba      	ldr	r2, [r7, #40]	; 0x28
   41fbe:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   41fc0:	4053      	eors	r3, r2
   41fc2:	210c      	movs	r1, #12
   41fc4:	4618      	mov	r0, r3
   41fc6:	f7fe fde7 	bl	40b98 <rotr32>
   41fca:	4603      	mov	r3, r0
   41fcc:	62bb      	str	r3, [r7, #40]	; 0x28
   41fce:	697a      	ldr	r2, [r7, #20]
   41fd0:	6abb      	ldr	r3, [r7, #40]	; 0x28
   41fd2:	441a      	add	r2, r3
   41fd4:	2300      	movs	r3, #0
   41fd6:	009b      	lsls	r3, r3, #2
   41fd8:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41fdc:	440b      	add	r3, r1
   41fde:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41fe2:	4413      	add	r3, r2
   41fe4:	617b      	str	r3, [r7, #20]
   41fe6:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   41fe8:	697b      	ldr	r3, [r7, #20]
   41fea:	4053      	eors	r3, r2
   41fec:	2108      	movs	r1, #8
   41fee:	4618      	mov	r0, r3
   41ff0:	f7fe fdd2 	bl	40b98 <rotr32>
   41ff4:	4603      	mov	r3, r0
   41ff6:	643b      	str	r3, [r7, #64]	; 0x40
   41ff8:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   41ffa:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   41ffc:	4413      	add	r3, r2
   41ffe:	62fb      	str	r3, [r7, #44]	; 0x2c
   42000:	6aba      	ldr	r2, [r7, #40]	; 0x28
   42002:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   42004:	4053      	eors	r3, r2
   42006:	2107      	movs	r1, #7
   42008:	4618      	mov	r0, r3
   4200a:	f7fe fdc5 	bl	40b98 <rotr32>
   4200e:	4603      	mov	r3, r0
   42010:	62bb      	str	r3, [r7, #40]	; 0x28
   42012:	69ba      	ldr	r2, [r7, #24]
   42014:	69fb      	ldr	r3, [r7, #28]
   42016:	441a      	add	r2, r3
   42018:	230f      	movs	r3, #15
   4201a:	009b      	lsls	r3, r3, #2
   4201c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42020:	440b      	add	r3, r1
   42022:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42026:	4413      	add	r3, r2
   42028:	61bb      	str	r3, [r7, #24]
   4202a:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   4202c:	69bb      	ldr	r3, [r7, #24]
   4202e:	4053      	eors	r3, r2
   42030:	2110      	movs	r1, #16
   42032:	4618      	mov	r0, r3
   42034:	f7fe fdb0 	bl	40b98 <rotr32>
   42038:	4603      	mov	r3, r0
   4203a:	647b      	str	r3, [r7, #68]	; 0x44
   4203c:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   4203e:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   42040:	4413      	add	r3, r2
   42042:	633b      	str	r3, [r7, #48]	; 0x30
   42044:	69fa      	ldr	r2, [r7, #28]
   42046:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   42048:	4053      	eors	r3, r2
   4204a:	210c      	movs	r1, #12
   4204c:	4618      	mov	r0, r3
   4204e:	f7fe fda3 	bl	40b98 <rotr32>
   42052:	4603      	mov	r3, r0
   42054:	61fb      	str	r3, [r7, #28]
   42056:	69ba      	ldr	r2, [r7, #24]
   42058:	69fb      	ldr	r3, [r7, #28]
   4205a:	441a      	add	r2, r3
   4205c:	2308      	movs	r3, #8
   4205e:	009b      	lsls	r3, r3, #2
   42060:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42064:	440b      	add	r3, r1
   42066:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4206a:	4413      	add	r3, r2
   4206c:	61bb      	str	r3, [r7, #24]
   4206e:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   42070:	69bb      	ldr	r3, [r7, #24]
   42072:	4053      	eors	r3, r2
   42074:	2108      	movs	r1, #8
   42076:	4618      	mov	r0, r3
   42078:	f7fe fd8e 	bl	40b98 <rotr32>
   4207c:	4603      	mov	r3, r0
   4207e:	647b      	str	r3, [r7, #68]	; 0x44
   42080:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   42082:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   42084:	4413      	add	r3, r2
   42086:	633b      	str	r3, [r7, #48]	; 0x30
   42088:	69fa      	ldr	r2, [r7, #28]
   4208a:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   4208c:	4053      	eors	r3, r2
   4208e:	2107      	movs	r1, #7
   42090:	4618      	mov	r0, r3
   42092:	f7fe fd81 	bl	40b98 <rotr32>
   42096:	4603      	mov	r3, r0
   42098:	61fb      	str	r3, [r7, #28]
   4209a:	68fa      	ldr	r2, [r7, #12]
   4209c:	69fb      	ldr	r3, [r7, #28]
   4209e:	441a      	add	r2, r3
   420a0:	2309      	movs	r3, #9
   420a2:	009b      	lsls	r3, r3, #2
   420a4:	f107 0190 	add.w	r1, r7, #144	; 0x90
   420a8:	440b      	add	r3, r1
   420aa:	f853 3c44 	ldr.w	r3, [r3, #-68]
   420ae:	4413      	add	r3, r2
   420b0:	60fb      	str	r3, [r7, #12]
   420b2:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   420b4:	68fb      	ldr	r3, [r7, #12]
   420b6:	4053      	eors	r3, r2
   420b8:	2110      	movs	r1, #16
   420ba:	4618      	mov	r0, r3
   420bc:	f7fe fd6c 	bl	40b98 <rotr32>
   420c0:	4603      	mov	r3, r0
   420c2:	63fb      	str	r3, [r7, #60]	; 0x3c
   420c4:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   420c6:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   420c8:	4413      	add	r3, r2
   420ca:	62fb      	str	r3, [r7, #44]	; 0x2c
   420cc:	69fa      	ldr	r2, [r7, #28]
   420ce:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   420d0:	4053      	eors	r3, r2
   420d2:	210c      	movs	r1, #12
   420d4:	4618      	mov	r0, r3
   420d6:	f7fe fd5f 	bl	40b98 <rotr32>
   420da:	4603      	mov	r3, r0
   420dc:	61fb      	str	r3, [r7, #28]
   420de:	68fa      	ldr	r2, [r7, #12]
   420e0:	69fb      	ldr	r3, [r7, #28]
   420e2:	441a      	add	r2, r3
   420e4:	2300      	movs	r3, #0
   420e6:	009b      	lsls	r3, r3, #2
   420e8:	f107 0190 	add.w	r1, r7, #144	; 0x90
   420ec:	440b      	add	r3, r1
   420ee:	f853 3c44 	ldr.w	r3, [r3, #-68]
   420f2:	4413      	add	r3, r2
   420f4:	60fb      	str	r3, [r7, #12]
   420f6:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   420f8:	68fb      	ldr	r3, [r7, #12]
   420fa:	4053      	eors	r3, r2
   420fc:	2108      	movs	r1, #8
   420fe:	4618      	mov	r0, r3
   42100:	f7fe fd4a 	bl	40b98 <rotr32>
   42104:	4603      	mov	r3, r0
   42106:	63fb      	str	r3, [r7, #60]	; 0x3c
   42108:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   4210a:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   4210c:	4413      	add	r3, r2
   4210e:	62fb      	str	r3, [r7, #44]	; 0x2c
   42110:	69fa      	ldr	r2, [r7, #28]
   42112:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   42114:	4053      	eors	r3, r2
   42116:	2107      	movs	r1, #7
   42118:	4618      	mov	r0, r3
   4211a:	f7fe fd3d 	bl	40b98 <rotr32>
   4211e:	4603      	mov	r3, r0
   42120:	61fb      	str	r3, [r7, #28]
   42122:	693a      	ldr	r2, [r7, #16]
   42124:	6a3b      	ldr	r3, [r7, #32]
   42126:	441a      	add	r2, r3
   42128:	2305      	movs	r3, #5
   4212a:	009b      	lsls	r3, r3, #2
   4212c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42130:	440b      	add	r3, r1
   42132:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42136:	4413      	add	r3, r2
   42138:	613b      	str	r3, [r7, #16]
   4213a:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   4213c:	693b      	ldr	r3, [r7, #16]
   4213e:	4053      	eors	r3, r2
   42140:	2110      	movs	r1, #16
   42142:	4618      	mov	r0, r3
   42144:	f7fe fd28 	bl	40b98 <rotr32>
   42148:	4603      	mov	r3, r0
   4214a:	643b      	str	r3, [r7, #64]	; 0x40
   4214c:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   4214e:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   42150:	4413      	add	r3, r2
   42152:	633b      	str	r3, [r7, #48]	; 0x30
   42154:	6a3a      	ldr	r2, [r7, #32]
   42156:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   42158:	4053      	eors	r3, r2
   4215a:	210c      	movs	r1, #12
   4215c:	4618      	mov	r0, r3
   4215e:	f7fe fd1b 	bl	40b98 <rotr32>
   42162:	4603      	mov	r3, r0
   42164:	623b      	str	r3, [r7, #32]
   42166:	693a      	ldr	r2, [r7, #16]
   42168:	6a3b      	ldr	r3, [r7, #32]
   4216a:	441a      	add	r2, r3
   4216c:	2307      	movs	r3, #7
   4216e:	009b      	lsls	r3, r3, #2
   42170:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42174:	440b      	add	r3, r1
   42176:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4217a:	4413      	add	r3, r2
   4217c:	613b      	str	r3, [r7, #16]
   4217e:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   42180:	693b      	ldr	r3, [r7, #16]
   42182:	4053      	eors	r3, r2
   42184:	2108      	movs	r1, #8
   42186:	4618      	mov	r0, r3
   42188:	f7fe fd06 	bl	40b98 <rotr32>
   4218c:	4603      	mov	r3, r0
   4218e:	643b      	str	r3, [r7, #64]	; 0x40
   42190:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   42192:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   42194:	4413      	add	r3, r2
   42196:	633b      	str	r3, [r7, #48]	; 0x30
   42198:	6a3a      	ldr	r2, [r7, #32]
   4219a:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   4219c:	4053      	eors	r3, r2
   4219e:	2107      	movs	r1, #7
   421a0:	4618      	mov	r0, r3
   421a2:	f7fe fcf9 	bl	40b98 <rotr32>
   421a6:	4603      	mov	r3, r0
   421a8:	623b      	str	r3, [r7, #32]
   421aa:	697a      	ldr	r2, [r7, #20]
   421ac:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   421ae:	441a      	add	r2, r3
   421b0:	2302      	movs	r3, #2
   421b2:	009b      	lsls	r3, r3, #2
   421b4:	f107 0190 	add.w	r1, r7, #144	; 0x90
   421b8:	440b      	add	r3, r1
   421ba:	f853 3c44 	ldr.w	r3, [r3, #-68]
   421be:	4413      	add	r3, r2
   421c0:	617b      	str	r3, [r7, #20]
   421c2:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   421c4:	697b      	ldr	r3, [r7, #20]
   421c6:	4053      	eors	r3, r2
   421c8:	2110      	movs	r1, #16
   421ca:	4618      	mov	r0, r3
   421cc:	f7fe fce4 	bl	40b98 <rotr32>
   421d0:	4603      	mov	r3, r0
   421d2:	647b      	str	r3, [r7, #68]	; 0x44
   421d4:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   421d6:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   421d8:	4413      	add	r3, r2
   421da:	637b      	str	r3, [r7, #52]	; 0x34
   421dc:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   421de:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   421e0:	4053      	eors	r3, r2
   421e2:	210c      	movs	r1, #12
   421e4:	4618      	mov	r0, r3
   421e6:	f7fe fcd7 	bl	40b98 <rotr32>
   421ea:	4603      	mov	r3, r0
   421ec:	627b      	str	r3, [r7, #36]	; 0x24
   421ee:	697a      	ldr	r2, [r7, #20]
   421f0:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   421f2:	441a      	add	r2, r3
   421f4:	2304      	movs	r3, #4
   421f6:	009b      	lsls	r3, r3, #2
   421f8:	f107 0190 	add.w	r1, r7, #144	; 0x90
   421fc:	440b      	add	r3, r1
   421fe:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42202:	4413      	add	r3, r2
   42204:	617b      	str	r3, [r7, #20]
   42206:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   42208:	697b      	ldr	r3, [r7, #20]
   4220a:	4053      	eors	r3, r2
   4220c:	2108      	movs	r1, #8
   4220e:	4618      	mov	r0, r3
   42210:	f7fe fcc2 	bl	40b98 <rotr32>
   42214:	4603      	mov	r3, r0
   42216:	647b      	str	r3, [r7, #68]	; 0x44
   42218:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   4221a:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   4221c:	4413      	add	r3, r2
   4221e:	637b      	str	r3, [r7, #52]	; 0x34
   42220:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   42222:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   42224:	4053      	eors	r3, r2
   42226:	2107      	movs	r1, #7
   42228:	4618      	mov	r0, r3
   4222a:	f7fe fcb5 	bl	40b98 <rotr32>
   4222e:	4603      	mov	r3, r0
   42230:	627b      	str	r3, [r7, #36]	; 0x24
   42232:	69ba      	ldr	r2, [r7, #24]
   42234:	6abb      	ldr	r3, [r7, #40]	; 0x28
   42236:	441a      	add	r2, r3
   42238:	230a      	movs	r3, #10
   4223a:	009b      	lsls	r3, r3, #2
   4223c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42240:	440b      	add	r3, r1
   42242:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42246:	4413      	add	r3, r2
   42248:	61bb      	str	r3, [r7, #24]
   4224a:	6cba      	ldr	r2, [r7, #72]	; 0x48
   4224c:	69bb      	ldr	r3, [r7, #24]
   4224e:	4053      	eors	r3, r2
   42250:	2110      	movs	r1, #16
   42252:	4618      	mov	r0, r3
   42254:	f7fe fca0 	bl	40b98 <rotr32>
   42258:	4603      	mov	r3, r0
   4225a:	64bb      	str	r3, [r7, #72]	; 0x48
   4225c:	6bba      	ldr	r2, [r7, #56]	; 0x38
   4225e:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   42260:	4413      	add	r3, r2
   42262:	63bb      	str	r3, [r7, #56]	; 0x38
   42264:	6aba      	ldr	r2, [r7, #40]	; 0x28
   42266:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   42268:	4053      	eors	r3, r2
   4226a:	210c      	movs	r1, #12
   4226c:	4618      	mov	r0, r3
   4226e:	f7fe fc93 	bl	40b98 <rotr32>
   42272:	4603      	mov	r3, r0
   42274:	62bb      	str	r3, [r7, #40]	; 0x28
   42276:	69ba      	ldr	r2, [r7, #24]
   42278:	6abb      	ldr	r3, [r7, #40]	; 0x28
   4227a:	441a      	add	r2, r3
   4227c:	230f      	movs	r3, #15
   4227e:	009b      	lsls	r3, r3, #2
   42280:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42284:	440b      	add	r3, r1
   42286:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4228a:	4413      	add	r3, r2
   4228c:	61bb      	str	r3, [r7, #24]
   4228e:	6cba      	ldr	r2, [r7, #72]	; 0x48
   42290:	69bb      	ldr	r3, [r7, #24]
   42292:	4053      	eors	r3, r2
   42294:	2108      	movs	r1, #8
   42296:	4618      	mov	r0, r3
   42298:	f7fe fc7e 	bl	40b98 <rotr32>
   4229c:	4603      	mov	r3, r0
   4229e:	64bb      	str	r3, [r7, #72]	; 0x48
   422a0:	6bba      	ldr	r2, [r7, #56]	; 0x38
   422a2:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   422a4:	4413      	add	r3, r2
   422a6:	63bb      	str	r3, [r7, #56]	; 0x38
   422a8:	6aba      	ldr	r2, [r7, #40]	; 0x28
   422aa:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   422ac:	4053      	eors	r3, r2
   422ae:	2107      	movs	r1, #7
   422b0:	4618      	mov	r0, r3
   422b2:	f7fe fc71 	bl	40b98 <rotr32>
   422b6:	4603      	mov	r3, r0
   422b8:	62bb      	str	r3, [r7, #40]	; 0x28
   422ba:	68fa      	ldr	r2, [r7, #12]
   422bc:	6a3b      	ldr	r3, [r7, #32]
   422be:	441a      	add	r2, r3
   422c0:	230e      	movs	r3, #14
   422c2:	009b      	lsls	r3, r3, #2
   422c4:	f107 0190 	add.w	r1, r7, #144	; 0x90
   422c8:	440b      	add	r3, r1
   422ca:	f853 3c44 	ldr.w	r3, [r3, #-68]
   422ce:	4413      	add	r3, r2
   422d0:	60fb      	str	r3, [r7, #12]
   422d2:	6cba      	ldr	r2, [r7, #72]	; 0x48
   422d4:	68fb      	ldr	r3, [r7, #12]
   422d6:	4053      	eors	r3, r2
   422d8:	2110      	movs	r1, #16
   422da:	4618      	mov	r0, r3
   422dc:	f7fe fc5c 	bl	40b98 <rotr32>
   422e0:	4603      	mov	r3, r0
   422e2:	64bb      	str	r3, [r7, #72]	; 0x48
   422e4:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   422e6:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   422e8:	4413      	add	r3, r2
   422ea:	637b      	str	r3, [r7, #52]	; 0x34
   422ec:	6a3a      	ldr	r2, [r7, #32]
   422ee:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   422f0:	4053      	eors	r3, r2
   422f2:	210c      	movs	r1, #12
   422f4:	4618      	mov	r0, r3
   422f6:	f7fe fc4f 	bl	40b98 <rotr32>
   422fa:	4603      	mov	r3, r0
   422fc:	623b      	str	r3, [r7, #32]
   422fe:	68fa      	ldr	r2, [r7, #12]
   42300:	6a3b      	ldr	r3, [r7, #32]
   42302:	441a      	add	r2, r3
   42304:	2301      	movs	r3, #1
   42306:	009b      	lsls	r3, r3, #2
   42308:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4230c:	440b      	add	r3, r1
   4230e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42312:	4413      	add	r3, r2
   42314:	60fb      	str	r3, [r7, #12]
   42316:	6cba      	ldr	r2, [r7, #72]	; 0x48
   42318:	68fb      	ldr	r3, [r7, #12]
   4231a:	4053      	eors	r3, r2
   4231c:	2108      	movs	r1, #8
   4231e:	4618      	mov	r0, r3
   42320:	f7fe fc3a 	bl	40b98 <rotr32>
   42324:	4603      	mov	r3, r0
   42326:	64bb      	str	r3, [r7, #72]	; 0x48
   42328:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   4232a:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   4232c:	4413      	add	r3, r2
   4232e:	637b      	str	r3, [r7, #52]	; 0x34
   42330:	6a3a      	ldr	r2, [r7, #32]
   42332:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   42334:	4053      	eors	r3, r2
   42336:	2107      	movs	r1, #7
   42338:	4618      	mov	r0, r3
   4233a:	f7fe fc2d 	bl	40b98 <rotr32>
   4233e:	4603      	mov	r3, r0
   42340:	623b      	str	r3, [r7, #32]
   42342:	693a      	ldr	r2, [r7, #16]
   42344:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   42346:	441a      	add	r2, r3
   42348:	230b      	movs	r3, #11
   4234a:	009b      	lsls	r3, r3, #2
   4234c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42350:	440b      	add	r3, r1
   42352:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42356:	4413      	add	r3, r2
   42358:	613b      	str	r3, [r7, #16]
   4235a:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   4235c:	693b      	ldr	r3, [r7, #16]
   4235e:	4053      	eors	r3, r2
   42360:	2110      	movs	r1, #16
   42362:	4618      	mov	r0, r3
   42364:	f7fe fc18 	bl	40b98 <rotr32>
   42368:	4603      	mov	r3, r0
   4236a:	63fb      	str	r3, [r7, #60]	; 0x3c
   4236c:	6bba      	ldr	r2, [r7, #56]	; 0x38
   4236e:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   42370:	4413      	add	r3, r2
   42372:	63bb      	str	r3, [r7, #56]	; 0x38
   42374:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   42376:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   42378:	4053      	eors	r3, r2
   4237a:	210c      	movs	r1, #12
   4237c:	4618      	mov	r0, r3
   4237e:	f7fe fc0b 	bl	40b98 <rotr32>
   42382:	4603      	mov	r3, r0
   42384:	627b      	str	r3, [r7, #36]	; 0x24
   42386:	693a      	ldr	r2, [r7, #16]
   42388:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   4238a:	441a      	add	r2, r3
   4238c:	230c      	movs	r3, #12
   4238e:	009b      	lsls	r3, r3, #2
   42390:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42394:	440b      	add	r3, r1
   42396:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4239a:	4413      	add	r3, r2
   4239c:	613b      	str	r3, [r7, #16]
   4239e:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   423a0:	693b      	ldr	r3, [r7, #16]
   423a2:	4053      	eors	r3, r2
   423a4:	2108      	movs	r1, #8
   423a6:	4618      	mov	r0, r3
   423a8:	f7fe fbf6 	bl	40b98 <rotr32>
   423ac:	4603      	mov	r3, r0
   423ae:	63fb      	str	r3, [r7, #60]	; 0x3c
   423b0:	6bba      	ldr	r2, [r7, #56]	; 0x38
   423b2:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   423b4:	4413      	add	r3, r2
   423b6:	63bb      	str	r3, [r7, #56]	; 0x38
   423b8:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   423ba:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   423bc:	4053      	eors	r3, r2
   423be:	2107      	movs	r1, #7
   423c0:	4618      	mov	r0, r3
   423c2:	f7fe fbe9 	bl	40b98 <rotr32>
   423c6:	4603      	mov	r3, r0
   423c8:	627b      	str	r3, [r7, #36]	; 0x24
   423ca:	697a      	ldr	r2, [r7, #20]
   423cc:	6abb      	ldr	r3, [r7, #40]	; 0x28
   423ce:	441a      	add	r2, r3
   423d0:	2306      	movs	r3, #6
   423d2:	009b      	lsls	r3, r3, #2
   423d4:	f107 0190 	add.w	r1, r7, #144	; 0x90
   423d8:	440b      	add	r3, r1
   423da:	f853 3c44 	ldr.w	r3, [r3, #-68]
   423de:	4413      	add	r3, r2
   423e0:	617b      	str	r3, [r7, #20]
   423e2:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   423e4:	697b      	ldr	r3, [r7, #20]
   423e6:	4053      	eors	r3, r2
   423e8:	2110      	movs	r1, #16
   423ea:	4618      	mov	r0, r3
   423ec:	f7fe fbd4 	bl	40b98 <rotr32>
   423f0:	4603      	mov	r3, r0
   423f2:	643b      	str	r3, [r7, #64]	; 0x40
   423f4:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   423f6:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   423f8:	4413      	add	r3, r2
   423fa:	62fb      	str	r3, [r7, #44]	; 0x2c
   423fc:	6aba      	ldr	r2, [r7, #40]	; 0x28
   423fe:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   42400:	4053      	eors	r3, r2
   42402:	210c      	movs	r1, #12
   42404:	4618      	mov	r0, r3
   42406:	f7fe fbc7 	bl	40b98 <rotr32>
   4240a:	4603      	mov	r3, r0
   4240c:	62bb      	str	r3, [r7, #40]	; 0x28
   4240e:	697a      	ldr	r2, [r7, #20]
   42410:	6abb      	ldr	r3, [r7, #40]	; 0x28
   42412:	441a      	add	r2, r3
   42414:	2308      	movs	r3, #8
   42416:	009b      	lsls	r3, r3, #2
   42418:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4241c:	440b      	add	r3, r1
   4241e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42422:	4413      	add	r3, r2
   42424:	617b      	str	r3, [r7, #20]
   42426:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   42428:	697b      	ldr	r3, [r7, #20]
   4242a:	4053      	eors	r3, r2
   4242c:	2108      	movs	r1, #8
   4242e:	4618      	mov	r0, r3
   42430:	f7fe fbb2 	bl	40b98 <rotr32>
   42434:	4603      	mov	r3, r0
   42436:	643b      	str	r3, [r7, #64]	; 0x40
   42438:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   4243a:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   4243c:	4413      	add	r3, r2
   4243e:	62fb      	str	r3, [r7, #44]	; 0x2c
   42440:	6aba      	ldr	r2, [r7, #40]	; 0x28
   42442:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   42444:	4053      	eors	r3, r2
   42446:	2107      	movs	r1, #7
   42448:	4618      	mov	r0, r3
   4244a:	f7fe fba5 	bl	40b98 <rotr32>
   4244e:	4603      	mov	r3, r0
   42450:	62bb      	str	r3, [r7, #40]	; 0x28
   42452:	69ba      	ldr	r2, [r7, #24]
   42454:	69fb      	ldr	r3, [r7, #28]
   42456:	441a      	add	r2, r3
   42458:	2303      	movs	r3, #3
   4245a:	009b      	lsls	r3, r3, #2
   4245c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42460:	440b      	add	r3, r1
   42462:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42466:	4413      	add	r3, r2
   42468:	61bb      	str	r3, [r7, #24]
   4246a:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   4246c:	69bb      	ldr	r3, [r7, #24]
   4246e:	4053      	eors	r3, r2
   42470:	2110      	movs	r1, #16
   42472:	4618      	mov	r0, r3
   42474:	f7fe fb90 	bl	40b98 <rotr32>
   42478:	4603      	mov	r3, r0
   4247a:	647b      	str	r3, [r7, #68]	; 0x44
   4247c:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   4247e:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   42480:	4413      	add	r3, r2
   42482:	633b      	str	r3, [r7, #48]	; 0x30
   42484:	69fa      	ldr	r2, [r7, #28]
   42486:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   42488:	4053      	eors	r3, r2
   4248a:	210c      	movs	r1, #12
   4248c:	4618      	mov	r0, r3
   4248e:	f7fe fb83 	bl	40b98 <rotr32>
   42492:	4603      	mov	r3, r0
   42494:	61fb      	str	r3, [r7, #28]
   42496:	69ba      	ldr	r2, [r7, #24]
   42498:	69fb      	ldr	r3, [r7, #28]
   4249a:	441a      	add	r2, r3
   4249c:	230d      	movs	r3, #13
   4249e:	009b      	lsls	r3, r3, #2
   424a0:	f107 0190 	add.w	r1, r7, #144	; 0x90
   424a4:	440b      	add	r3, r1
   424a6:	f853 3c44 	ldr.w	r3, [r3, #-68]
   424aa:	4413      	add	r3, r2
   424ac:	61bb      	str	r3, [r7, #24]
   424ae:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   424b0:	69bb      	ldr	r3, [r7, #24]
   424b2:	4053      	eors	r3, r2
   424b4:	2108      	movs	r1, #8
   424b6:	4618      	mov	r0, r3
   424b8:	f7fe fb6e 	bl	40b98 <rotr32>
   424bc:	4603      	mov	r3, r0
   424be:	647b      	str	r3, [r7, #68]	; 0x44
   424c0:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   424c2:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   424c4:	4413      	add	r3, r2
   424c6:	633b      	str	r3, [r7, #48]	; 0x30
   424c8:	69fa      	ldr	r2, [r7, #28]
   424ca:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   424cc:	4053      	eors	r3, r2
   424ce:	2107      	movs	r1, #7
   424d0:	4618      	mov	r0, r3
   424d2:	f7fe fb61 	bl	40b98 <rotr32>
   424d6:	4603      	mov	r3, r0
   424d8:	61fb      	str	r3, [r7, #28]
   424da:	68fa      	ldr	r2, [r7, #12]
   424dc:	69fb      	ldr	r3, [r7, #28]
   424de:	441a      	add	r2, r3
   424e0:	2302      	movs	r3, #2
   424e2:	009b      	lsls	r3, r3, #2
   424e4:	f107 0190 	add.w	r1, r7, #144	; 0x90
   424e8:	440b      	add	r3, r1
   424ea:	f853 3c44 	ldr.w	r3, [r3, #-68]
   424ee:	4413      	add	r3, r2
   424f0:	60fb      	str	r3, [r7, #12]
   424f2:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   424f4:	68fb      	ldr	r3, [r7, #12]
   424f6:	4053      	eors	r3, r2
   424f8:	2110      	movs	r1, #16
   424fa:	4618      	mov	r0, r3
   424fc:	f7fe fb4c 	bl	40b98 <rotr32>
   42500:	4603      	mov	r3, r0
   42502:	63fb      	str	r3, [r7, #60]	; 0x3c
   42504:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   42506:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   42508:	4413      	add	r3, r2
   4250a:	62fb      	str	r3, [r7, #44]	; 0x2c
   4250c:	69fa      	ldr	r2, [r7, #28]
   4250e:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   42510:	4053      	eors	r3, r2
   42512:	210c      	movs	r1, #12
   42514:	4618      	mov	r0, r3
   42516:	f7fe fb3f 	bl	40b98 <rotr32>
   4251a:	4603      	mov	r3, r0
   4251c:	61fb      	str	r3, [r7, #28]
   4251e:	68fa      	ldr	r2, [r7, #12]
   42520:	69fb      	ldr	r3, [r7, #28]
   42522:	441a      	add	r2, r3
   42524:	230c      	movs	r3, #12
   42526:	009b      	lsls	r3, r3, #2
   42528:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4252c:	440b      	add	r3, r1
   4252e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42532:	4413      	add	r3, r2
   42534:	60fb      	str	r3, [r7, #12]
   42536:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   42538:	68fb      	ldr	r3, [r7, #12]
   4253a:	4053      	eors	r3, r2
   4253c:	2108      	movs	r1, #8
   4253e:	4618      	mov	r0, r3
   42540:	f7fe fb2a 	bl	40b98 <rotr32>
   42544:	4603      	mov	r3, r0
   42546:	63fb      	str	r3, [r7, #60]	; 0x3c
   42548:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   4254a:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   4254c:	4413      	add	r3, r2
   4254e:	62fb      	str	r3, [r7, #44]	; 0x2c
   42550:	69fa      	ldr	r2, [r7, #28]
   42552:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   42554:	4053      	eors	r3, r2
   42556:	2107      	movs	r1, #7
   42558:	4618      	mov	r0, r3
   4255a:	f7fe fb1d 	bl	40b98 <rotr32>
   4255e:	4603      	mov	r3, r0
   42560:	61fb      	str	r3, [r7, #28]
   42562:	693a      	ldr	r2, [r7, #16]
   42564:	6a3b      	ldr	r3, [r7, #32]
   42566:	441a      	add	r2, r3
   42568:	2306      	movs	r3, #6
   4256a:	009b      	lsls	r3, r3, #2
   4256c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42570:	440b      	add	r3, r1
   42572:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42576:	4413      	add	r3, r2
   42578:	613b      	str	r3, [r7, #16]
   4257a:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   4257c:	693b      	ldr	r3, [r7, #16]
   4257e:	4053      	eors	r3, r2
   42580:	2110      	movs	r1, #16
   42582:	4618      	mov	r0, r3
   42584:	f7fe fb08 	bl	40b98 <rotr32>
   42588:	4603      	mov	r3, r0
   4258a:	643b      	str	r3, [r7, #64]	; 0x40
   4258c:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   4258e:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   42590:	4413      	add	r3, r2
   42592:	633b      	str	r3, [r7, #48]	; 0x30
   42594:	6a3a      	ldr	r2, [r7, #32]
   42596:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   42598:	4053      	eors	r3, r2
   4259a:	210c      	movs	r1, #12
   4259c:	4618      	mov	r0, r3
   4259e:	f7fe fafb 	bl	40b98 <rotr32>
   425a2:	4603      	mov	r3, r0
   425a4:	623b      	str	r3, [r7, #32]
   425a6:	693a      	ldr	r2, [r7, #16]
   425a8:	6a3b      	ldr	r3, [r7, #32]
   425aa:	441a      	add	r2, r3
   425ac:	230a      	movs	r3, #10
   425ae:	009b      	lsls	r3, r3, #2
   425b0:	f107 0190 	add.w	r1, r7, #144	; 0x90
   425b4:	440b      	add	r3, r1
   425b6:	f853 3c44 	ldr.w	r3, [r3, #-68]
   425ba:	4413      	add	r3, r2
   425bc:	613b      	str	r3, [r7, #16]
   425be:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   425c0:	693b      	ldr	r3, [r7, #16]
   425c2:	4053      	eors	r3, r2
   425c4:	2108      	movs	r1, #8
   425c6:	4618      	mov	r0, r3
   425c8:	f7fe fae6 	bl	40b98 <rotr32>
   425cc:	4603      	mov	r3, r0
   425ce:	643b      	str	r3, [r7, #64]	; 0x40
   425d0:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   425d2:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   425d4:	4413      	add	r3, r2
   425d6:	633b      	str	r3, [r7, #48]	; 0x30
   425d8:	6a3a      	ldr	r2, [r7, #32]
   425da:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   425dc:	4053      	eors	r3, r2
   425de:	2107      	movs	r1, #7
   425e0:	4618      	mov	r0, r3
   425e2:	f7fe fad9 	bl	40b98 <rotr32>
   425e6:	4603      	mov	r3, r0
   425e8:	623b      	str	r3, [r7, #32]
   425ea:	697a      	ldr	r2, [r7, #20]
   425ec:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   425ee:	441a      	add	r2, r3
   425f0:	2300      	movs	r3, #0
   425f2:	009b      	lsls	r3, r3, #2
   425f4:	f107 0190 	add.w	r1, r7, #144	; 0x90
   425f8:	440b      	add	r3, r1
   425fa:	f853 3c44 	ldr.w	r3, [r3, #-68]
   425fe:	4413      	add	r3, r2
   42600:	617b      	str	r3, [r7, #20]
   42602:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   42604:	697b      	ldr	r3, [r7, #20]
   42606:	4053      	eors	r3, r2
   42608:	2110      	movs	r1, #16
   4260a:	4618      	mov	r0, r3
   4260c:	f7fe fac4 	bl	40b98 <rotr32>
   42610:	4603      	mov	r3, r0
   42612:	647b      	str	r3, [r7, #68]	; 0x44
   42614:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   42616:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   42618:	4413      	add	r3, r2
   4261a:	637b      	str	r3, [r7, #52]	; 0x34
   4261c:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   4261e:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   42620:	4053      	eors	r3, r2
   42622:	210c      	movs	r1, #12
   42624:	4618      	mov	r0, r3
   42626:	f7fe fab7 	bl	40b98 <rotr32>
   4262a:	4603      	mov	r3, r0
   4262c:	627b      	str	r3, [r7, #36]	; 0x24
   4262e:	697a      	ldr	r2, [r7, #20]
   42630:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   42632:	441a      	add	r2, r3
   42634:	230b      	movs	r3, #11
   42636:	009b      	lsls	r3, r3, #2
   42638:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4263c:	440b      	add	r3, r1
   4263e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42642:	4413      	add	r3, r2
   42644:	617b      	str	r3, [r7, #20]
   42646:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   42648:	697b      	ldr	r3, [r7, #20]
   4264a:	4053      	eors	r3, r2
   4264c:	2108      	movs	r1, #8
   4264e:	4618      	mov	r0, r3
   42650:	f7fe faa2 	bl	40b98 <rotr32>
   42654:	4603      	mov	r3, r0
   42656:	647b      	str	r3, [r7, #68]	; 0x44
   42658:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   4265a:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   4265c:	4413      	add	r3, r2
   4265e:	637b      	str	r3, [r7, #52]	; 0x34
   42660:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   42662:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   42664:	4053      	eors	r3, r2
   42666:	2107      	movs	r1, #7
   42668:	4618      	mov	r0, r3
   4266a:	f7fe fa95 	bl	40b98 <rotr32>
   4266e:	4603      	mov	r3, r0
   42670:	627b      	str	r3, [r7, #36]	; 0x24
   42672:	69ba      	ldr	r2, [r7, #24]
   42674:	6abb      	ldr	r3, [r7, #40]	; 0x28
   42676:	441a      	add	r2, r3
   42678:	2308      	movs	r3, #8
   4267a:	009b      	lsls	r3, r3, #2
   4267c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42680:	440b      	add	r3, r1
   42682:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42686:	4413      	add	r3, r2
   42688:	61bb      	str	r3, [r7, #24]
   4268a:	6cba      	ldr	r2, [r7, #72]	; 0x48
   4268c:	69bb      	ldr	r3, [r7, #24]
   4268e:	4053      	eors	r3, r2
   42690:	2110      	movs	r1, #16
   42692:	4618      	mov	r0, r3
   42694:	f7fe fa80 	bl	40b98 <rotr32>
   42698:	4603      	mov	r3, r0
   4269a:	64bb      	str	r3, [r7, #72]	; 0x48
   4269c:	6bba      	ldr	r2, [r7, #56]	; 0x38
   4269e:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   426a0:	4413      	add	r3, r2
   426a2:	63bb      	str	r3, [r7, #56]	; 0x38
   426a4:	6aba      	ldr	r2, [r7, #40]	; 0x28
   426a6:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   426a8:	4053      	eors	r3, r2
   426aa:	210c      	movs	r1, #12
   426ac:	4618      	mov	r0, r3
   426ae:	f7fe fa73 	bl	40b98 <rotr32>
   426b2:	4603      	mov	r3, r0
   426b4:	62bb      	str	r3, [r7, #40]	; 0x28
   426b6:	69ba      	ldr	r2, [r7, #24]
   426b8:	6abb      	ldr	r3, [r7, #40]	; 0x28
   426ba:	441a      	add	r2, r3
   426bc:	2303      	movs	r3, #3
   426be:	009b      	lsls	r3, r3, #2
   426c0:	f107 0190 	add.w	r1, r7, #144	; 0x90
   426c4:	440b      	add	r3, r1
   426c6:	f853 3c44 	ldr.w	r3, [r3, #-68]
   426ca:	4413      	add	r3, r2
   426cc:	61bb      	str	r3, [r7, #24]
   426ce:	6cba      	ldr	r2, [r7, #72]	; 0x48
   426d0:	69bb      	ldr	r3, [r7, #24]
   426d2:	4053      	eors	r3, r2
   426d4:	2108      	movs	r1, #8
   426d6:	4618      	mov	r0, r3
   426d8:	f7fe fa5e 	bl	40b98 <rotr32>
   426dc:	4603      	mov	r3, r0
   426de:	64bb      	str	r3, [r7, #72]	; 0x48
   426e0:	6bba      	ldr	r2, [r7, #56]	; 0x38
   426e2:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   426e4:	4413      	add	r3, r2
   426e6:	63bb      	str	r3, [r7, #56]	; 0x38
   426e8:	6aba      	ldr	r2, [r7, #40]	; 0x28
   426ea:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   426ec:	4053      	eors	r3, r2
   426ee:	2107      	movs	r1, #7
   426f0:	4618      	mov	r0, r3
   426f2:	f7fe fa51 	bl	40b98 <rotr32>
   426f6:	4603      	mov	r3, r0
   426f8:	62bb      	str	r3, [r7, #40]	; 0x28
   426fa:	68fa      	ldr	r2, [r7, #12]
   426fc:	6a3b      	ldr	r3, [r7, #32]
   426fe:	441a      	add	r2, r3
   42700:	2304      	movs	r3, #4
   42702:	009b      	lsls	r3, r3, #2
   42704:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42708:	440b      	add	r3, r1
   4270a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4270e:	4413      	add	r3, r2
   42710:	60fb      	str	r3, [r7, #12]
   42712:	6cba      	ldr	r2, [r7, #72]	; 0x48
   42714:	68fb      	ldr	r3, [r7, #12]
   42716:	4053      	eors	r3, r2
   42718:	2110      	movs	r1, #16
   4271a:	4618      	mov	r0, r3
   4271c:	f7fe fa3c 	bl	40b98 <rotr32>
   42720:	4603      	mov	r3, r0
   42722:	64bb      	str	r3, [r7, #72]	; 0x48
   42724:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   42726:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   42728:	4413      	add	r3, r2
   4272a:	637b      	str	r3, [r7, #52]	; 0x34
   4272c:	6a3a      	ldr	r2, [r7, #32]
   4272e:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   42730:	4053      	eors	r3, r2
   42732:	210c      	movs	r1, #12
   42734:	4618      	mov	r0, r3
   42736:	f7fe fa2f 	bl	40b98 <rotr32>
   4273a:	4603      	mov	r3, r0
   4273c:	623b      	str	r3, [r7, #32]
   4273e:	68fa      	ldr	r2, [r7, #12]
   42740:	6a3b      	ldr	r3, [r7, #32]
   42742:	441a      	add	r2, r3
   42744:	230d      	movs	r3, #13
   42746:	009b      	lsls	r3, r3, #2
   42748:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4274c:	440b      	add	r3, r1
   4274e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42752:	4413      	add	r3, r2
   42754:	60fb      	str	r3, [r7, #12]
   42756:	6cba      	ldr	r2, [r7, #72]	; 0x48
   42758:	68fb      	ldr	r3, [r7, #12]
   4275a:	4053      	eors	r3, r2
   4275c:	2108      	movs	r1, #8
   4275e:	4618      	mov	r0, r3
   42760:	f7fe fa1a 	bl	40b98 <rotr32>
   42764:	4603      	mov	r3, r0
   42766:	64bb      	str	r3, [r7, #72]	; 0x48
   42768:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   4276a:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   4276c:	4413      	add	r3, r2
   4276e:	637b      	str	r3, [r7, #52]	; 0x34
   42770:	6a3a      	ldr	r2, [r7, #32]
   42772:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   42774:	4053      	eors	r3, r2
   42776:	2107      	movs	r1, #7
   42778:	4618      	mov	r0, r3
   4277a:	f7fe fa0d 	bl	40b98 <rotr32>
   4277e:	4603      	mov	r3, r0
   42780:	623b      	str	r3, [r7, #32]
   42782:	693a      	ldr	r2, [r7, #16]
   42784:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   42786:	441a      	add	r2, r3
   42788:	2307      	movs	r3, #7
   4278a:	009b      	lsls	r3, r3, #2
   4278c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42790:	440b      	add	r3, r1
   42792:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42796:	4413      	add	r3, r2
   42798:	613b      	str	r3, [r7, #16]
   4279a:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   4279c:	693b      	ldr	r3, [r7, #16]
   4279e:	4053      	eors	r3, r2
   427a0:	2110      	movs	r1, #16
   427a2:	4618      	mov	r0, r3
   427a4:	f7fe f9f8 	bl	40b98 <rotr32>
   427a8:	4603      	mov	r3, r0
   427aa:	63fb      	str	r3, [r7, #60]	; 0x3c
   427ac:	6bba      	ldr	r2, [r7, #56]	; 0x38
   427ae:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   427b0:	4413      	add	r3, r2
   427b2:	63bb      	str	r3, [r7, #56]	; 0x38
   427b4:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   427b6:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   427b8:	4053      	eors	r3, r2
   427ba:	210c      	movs	r1, #12
   427bc:	4618      	mov	r0, r3
   427be:	f7fe f9eb 	bl	40b98 <rotr32>
   427c2:	4603      	mov	r3, r0
   427c4:	627b      	str	r3, [r7, #36]	; 0x24
   427c6:	693a      	ldr	r2, [r7, #16]
   427c8:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   427ca:	441a      	add	r2, r3
   427cc:	2305      	movs	r3, #5
   427ce:	009b      	lsls	r3, r3, #2
   427d0:	f107 0190 	add.w	r1, r7, #144	; 0x90
   427d4:	440b      	add	r3, r1
   427d6:	f853 3c44 	ldr.w	r3, [r3, #-68]
   427da:	4413      	add	r3, r2
   427dc:	613b      	str	r3, [r7, #16]
   427de:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   427e0:	693b      	ldr	r3, [r7, #16]
   427e2:	4053      	eors	r3, r2
   427e4:	2108      	movs	r1, #8
   427e6:	4618      	mov	r0, r3
   427e8:	f7fe f9d6 	bl	40b98 <rotr32>
   427ec:	4603      	mov	r3, r0
   427ee:	63fb      	str	r3, [r7, #60]	; 0x3c
   427f0:	6bba      	ldr	r2, [r7, #56]	; 0x38
   427f2:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   427f4:	4413      	add	r3, r2
   427f6:	63bb      	str	r3, [r7, #56]	; 0x38
   427f8:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   427fa:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   427fc:	4053      	eors	r3, r2
   427fe:	2107      	movs	r1, #7
   42800:	4618      	mov	r0, r3
   42802:	f7fe f9c9 	bl	40b98 <rotr32>
   42806:	4603      	mov	r3, r0
   42808:	627b      	str	r3, [r7, #36]	; 0x24
   4280a:	697a      	ldr	r2, [r7, #20]
   4280c:	6abb      	ldr	r3, [r7, #40]	; 0x28
   4280e:	441a      	add	r2, r3
   42810:	230f      	movs	r3, #15
   42812:	009b      	lsls	r3, r3, #2
   42814:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42818:	440b      	add	r3, r1
   4281a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4281e:	4413      	add	r3, r2
   42820:	617b      	str	r3, [r7, #20]
   42822:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   42824:	697b      	ldr	r3, [r7, #20]
   42826:	4053      	eors	r3, r2
   42828:	2110      	movs	r1, #16
   4282a:	4618      	mov	r0, r3
   4282c:	f7fe f9b4 	bl	40b98 <rotr32>
   42830:	4603      	mov	r3, r0
   42832:	643b      	str	r3, [r7, #64]	; 0x40
   42834:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   42836:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   42838:	4413      	add	r3, r2
   4283a:	62fb      	str	r3, [r7, #44]	; 0x2c
   4283c:	6aba      	ldr	r2, [r7, #40]	; 0x28
   4283e:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   42840:	4053      	eors	r3, r2
   42842:	210c      	movs	r1, #12
   42844:	4618      	mov	r0, r3
   42846:	f7fe f9a7 	bl	40b98 <rotr32>
   4284a:	4603      	mov	r3, r0
   4284c:	62bb      	str	r3, [r7, #40]	; 0x28
   4284e:	697a      	ldr	r2, [r7, #20]
   42850:	6abb      	ldr	r3, [r7, #40]	; 0x28
   42852:	441a      	add	r2, r3
   42854:	230e      	movs	r3, #14
   42856:	009b      	lsls	r3, r3, #2
   42858:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4285c:	440b      	add	r3, r1
   4285e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42862:	4413      	add	r3, r2
   42864:	617b      	str	r3, [r7, #20]
   42866:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   42868:	697b      	ldr	r3, [r7, #20]
   4286a:	4053      	eors	r3, r2
   4286c:	2108      	movs	r1, #8
   4286e:	4618      	mov	r0, r3
   42870:	f7fe f992 	bl	40b98 <rotr32>
   42874:	4603      	mov	r3, r0
   42876:	643b      	str	r3, [r7, #64]	; 0x40
   42878:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   4287a:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   4287c:	4413      	add	r3, r2
   4287e:	62fb      	str	r3, [r7, #44]	; 0x2c
   42880:	6aba      	ldr	r2, [r7, #40]	; 0x28
   42882:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   42884:	4053      	eors	r3, r2
   42886:	2107      	movs	r1, #7
   42888:	4618      	mov	r0, r3
   4288a:	f7fe f985 	bl	40b98 <rotr32>
   4288e:	4603      	mov	r3, r0
   42890:	62bb      	str	r3, [r7, #40]	; 0x28
   42892:	69ba      	ldr	r2, [r7, #24]
   42894:	69fb      	ldr	r3, [r7, #28]
   42896:	441a      	add	r2, r3
   42898:	2301      	movs	r3, #1
   4289a:	009b      	lsls	r3, r3, #2
   4289c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   428a0:	440b      	add	r3, r1
   428a2:	f853 3c44 	ldr.w	r3, [r3, #-68]
   428a6:	4413      	add	r3, r2
   428a8:	61bb      	str	r3, [r7, #24]
   428aa:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   428ac:	69bb      	ldr	r3, [r7, #24]
   428ae:	4053      	eors	r3, r2
   428b0:	2110      	movs	r1, #16
   428b2:	4618      	mov	r0, r3
   428b4:	f7fe f970 	bl	40b98 <rotr32>
   428b8:	4603      	mov	r3, r0
   428ba:	647b      	str	r3, [r7, #68]	; 0x44
   428bc:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   428be:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   428c0:	4413      	add	r3, r2
   428c2:	633b      	str	r3, [r7, #48]	; 0x30
   428c4:	69fa      	ldr	r2, [r7, #28]
   428c6:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   428c8:	4053      	eors	r3, r2
   428ca:	210c      	movs	r1, #12
   428cc:	4618      	mov	r0, r3
   428ce:	f7fe f963 	bl	40b98 <rotr32>
   428d2:	4603      	mov	r3, r0
   428d4:	61fb      	str	r3, [r7, #28]
   428d6:	69ba      	ldr	r2, [r7, #24]
   428d8:	69fb      	ldr	r3, [r7, #28]
   428da:	441a      	add	r2, r3
   428dc:	2309      	movs	r3, #9
   428de:	009b      	lsls	r3, r3, #2
   428e0:	f107 0190 	add.w	r1, r7, #144	; 0x90
   428e4:	440b      	add	r3, r1
   428e6:	f853 3c44 	ldr.w	r3, [r3, #-68]
   428ea:	4413      	add	r3, r2
   428ec:	61bb      	str	r3, [r7, #24]
   428ee:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   428f0:	69bb      	ldr	r3, [r7, #24]
   428f2:	4053      	eors	r3, r2
   428f4:	2108      	movs	r1, #8
   428f6:	4618      	mov	r0, r3
   428f8:	f7fe f94e 	bl	40b98 <rotr32>
   428fc:	4603      	mov	r3, r0
   428fe:	647b      	str	r3, [r7, #68]	; 0x44
   42900:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   42902:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   42904:	4413      	add	r3, r2
   42906:	633b      	str	r3, [r7, #48]	; 0x30
   42908:	69fa      	ldr	r2, [r7, #28]
   4290a:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   4290c:	4053      	eors	r3, r2
   4290e:	2107      	movs	r1, #7
   42910:	4618      	mov	r0, r3
   42912:	f7fe f941 	bl	40b98 <rotr32>
   42916:	4603      	mov	r3, r0
   42918:	61fb      	str	r3, [r7, #28]
   4291a:	68fa      	ldr	r2, [r7, #12]
   4291c:	69fb      	ldr	r3, [r7, #28]
   4291e:	441a      	add	r2, r3
   42920:	230c      	movs	r3, #12
   42922:	009b      	lsls	r3, r3, #2
   42924:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42928:	440b      	add	r3, r1
   4292a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4292e:	4413      	add	r3, r2
   42930:	60fb      	str	r3, [r7, #12]
   42932:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   42934:	68fb      	ldr	r3, [r7, #12]
   42936:	4053      	eors	r3, r2
   42938:	2110      	movs	r1, #16
   4293a:	4618      	mov	r0, r3
   4293c:	f7fe f92c 	bl	40b98 <rotr32>
   42940:	4603      	mov	r3, r0
   42942:	63fb      	str	r3, [r7, #60]	; 0x3c
   42944:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   42946:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   42948:	4413      	add	r3, r2
   4294a:	62fb      	str	r3, [r7, #44]	; 0x2c
   4294c:	69fa      	ldr	r2, [r7, #28]
   4294e:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   42950:	4053      	eors	r3, r2
   42952:	210c      	movs	r1, #12
   42954:	4618      	mov	r0, r3
   42956:	f7fe f91f 	bl	40b98 <rotr32>
   4295a:	4603      	mov	r3, r0
   4295c:	61fb      	str	r3, [r7, #28]
   4295e:	68fa      	ldr	r2, [r7, #12]
   42960:	69fb      	ldr	r3, [r7, #28]
   42962:	441a      	add	r2, r3
   42964:	2305      	movs	r3, #5
   42966:	009b      	lsls	r3, r3, #2
   42968:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4296c:	440b      	add	r3, r1
   4296e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42972:	4413      	add	r3, r2
   42974:	60fb      	str	r3, [r7, #12]
   42976:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   42978:	68fb      	ldr	r3, [r7, #12]
   4297a:	4053      	eors	r3, r2
   4297c:	2108      	movs	r1, #8
   4297e:	4618      	mov	r0, r3
   42980:	f7fe f90a 	bl	40b98 <rotr32>
   42984:	4603      	mov	r3, r0
   42986:	63fb      	str	r3, [r7, #60]	; 0x3c
   42988:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   4298a:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   4298c:	4413      	add	r3, r2
   4298e:	62fb      	str	r3, [r7, #44]	; 0x2c
   42990:	69fa      	ldr	r2, [r7, #28]
   42992:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   42994:	4053      	eors	r3, r2
   42996:	2107      	movs	r1, #7
   42998:	4618      	mov	r0, r3
   4299a:	f7fe f8fd 	bl	40b98 <rotr32>
   4299e:	4603      	mov	r3, r0
   429a0:	61fb      	str	r3, [r7, #28]
   429a2:	693a      	ldr	r2, [r7, #16]
   429a4:	6a3b      	ldr	r3, [r7, #32]
   429a6:	441a      	add	r2, r3
   429a8:	2301      	movs	r3, #1
   429aa:	009b      	lsls	r3, r3, #2
   429ac:	f107 0190 	add.w	r1, r7, #144	; 0x90
   429b0:	440b      	add	r3, r1
   429b2:	f853 3c44 	ldr.w	r3, [r3, #-68]
   429b6:	4413      	add	r3, r2
   429b8:	613b      	str	r3, [r7, #16]
   429ba:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   429bc:	693b      	ldr	r3, [r7, #16]
   429be:	4053      	eors	r3, r2
   429c0:	2110      	movs	r1, #16
   429c2:	4618      	mov	r0, r3
   429c4:	f7fe f8e8 	bl	40b98 <rotr32>
   429c8:	4603      	mov	r3, r0
   429ca:	643b      	str	r3, [r7, #64]	; 0x40
   429cc:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   429ce:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   429d0:	4413      	add	r3, r2
   429d2:	633b      	str	r3, [r7, #48]	; 0x30
   429d4:	6a3a      	ldr	r2, [r7, #32]
   429d6:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   429d8:	4053      	eors	r3, r2
   429da:	210c      	movs	r1, #12
   429dc:	4618      	mov	r0, r3
   429de:	f7fe f8db 	bl	40b98 <rotr32>
   429e2:	4603      	mov	r3, r0
   429e4:	623b      	str	r3, [r7, #32]
   429e6:	693a      	ldr	r2, [r7, #16]
   429e8:	6a3b      	ldr	r3, [r7, #32]
   429ea:	441a      	add	r2, r3
   429ec:	230f      	movs	r3, #15
   429ee:	009b      	lsls	r3, r3, #2
   429f0:	f107 0190 	add.w	r1, r7, #144	; 0x90
   429f4:	440b      	add	r3, r1
   429f6:	f853 3c44 	ldr.w	r3, [r3, #-68]
   429fa:	4413      	add	r3, r2
   429fc:	613b      	str	r3, [r7, #16]
   429fe:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   42a00:	693b      	ldr	r3, [r7, #16]
   42a02:	4053      	eors	r3, r2
   42a04:	2108      	movs	r1, #8
   42a06:	4618      	mov	r0, r3
   42a08:	f7fe f8c6 	bl	40b98 <rotr32>
   42a0c:	4603      	mov	r3, r0
   42a0e:	643b      	str	r3, [r7, #64]	; 0x40
   42a10:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   42a12:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   42a14:	4413      	add	r3, r2
   42a16:	633b      	str	r3, [r7, #48]	; 0x30
   42a18:	6a3a      	ldr	r2, [r7, #32]
   42a1a:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   42a1c:	4053      	eors	r3, r2
   42a1e:	2107      	movs	r1, #7
   42a20:	4618      	mov	r0, r3
   42a22:	f7fe f8b9 	bl	40b98 <rotr32>
   42a26:	4603      	mov	r3, r0
   42a28:	623b      	str	r3, [r7, #32]
   42a2a:	697a      	ldr	r2, [r7, #20]
   42a2c:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   42a2e:	441a      	add	r2, r3
   42a30:	230e      	movs	r3, #14
   42a32:	009b      	lsls	r3, r3, #2
   42a34:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42a38:	440b      	add	r3, r1
   42a3a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42a3e:	4413      	add	r3, r2
   42a40:	617b      	str	r3, [r7, #20]
   42a42:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   42a44:	697b      	ldr	r3, [r7, #20]
   42a46:	4053      	eors	r3, r2
   42a48:	2110      	movs	r1, #16
   42a4a:	4618      	mov	r0, r3
   42a4c:	f7fe f8a4 	bl	40b98 <rotr32>
   42a50:	4603      	mov	r3, r0
   42a52:	647b      	str	r3, [r7, #68]	; 0x44
   42a54:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   42a56:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   42a58:	4413      	add	r3, r2
   42a5a:	637b      	str	r3, [r7, #52]	; 0x34
   42a5c:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   42a5e:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   42a60:	4053      	eors	r3, r2
   42a62:	210c      	movs	r1, #12
   42a64:	4618      	mov	r0, r3
   42a66:	f7fe f897 	bl	40b98 <rotr32>
   42a6a:	4603      	mov	r3, r0
   42a6c:	627b      	str	r3, [r7, #36]	; 0x24
   42a6e:	697a      	ldr	r2, [r7, #20]
   42a70:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   42a72:	441a      	add	r2, r3
   42a74:	230d      	movs	r3, #13
   42a76:	009b      	lsls	r3, r3, #2
   42a78:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42a7c:	440b      	add	r3, r1
   42a7e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42a82:	4413      	add	r3, r2
   42a84:	617b      	str	r3, [r7, #20]
   42a86:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   42a88:	697b      	ldr	r3, [r7, #20]
   42a8a:	4053      	eors	r3, r2
   42a8c:	2108      	movs	r1, #8
   42a8e:	4618      	mov	r0, r3
   42a90:	f7fe f882 	bl	40b98 <rotr32>
   42a94:	4603      	mov	r3, r0
   42a96:	647b      	str	r3, [r7, #68]	; 0x44
   42a98:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   42a9a:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   42a9c:	4413      	add	r3, r2
   42a9e:	637b      	str	r3, [r7, #52]	; 0x34
   42aa0:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   42aa2:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   42aa4:	4053      	eors	r3, r2
   42aa6:	2107      	movs	r1, #7
   42aa8:	4618      	mov	r0, r3
   42aaa:	f7fe f875 	bl	40b98 <rotr32>
   42aae:	4603      	mov	r3, r0
   42ab0:	627b      	str	r3, [r7, #36]	; 0x24
   42ab2:	69ba      	ldr	r2, [r7, #24]
   42ab4:	6abb      	ldr	r3, [r7, #40]	; 0x28
   42ab6:	441a      	add	r2, r3
   42ab8:	2304      	movs	r3, #4
   42aba:	009b      	lsls	r3, r3, #2
   42abc:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42ac0:	440b      	add	r3, r1
   42ac2:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42ac6:	4413      	add	r3, r2
   42ac8:	61bb      	str	r3, [r7, #24]
   42aca:	6cba      	ldr	r2, [r7, #72]	; 0x48
   42acc:	69bb      	ldr	r3, [r7, #24]
   42ace:	4053      	eors	r3, r2
   42ad0:	2110      	movs	r1, #16
   42ad2:	4618      	mov	r0, r3
   42ad4:	f7fe f860 	bl	40b98 <rotr32>
   42ad8:	4603      	mov	r3, r0
   42ada:	64bb      	str	r3, [r7, #72]	; 0x48
   42adc:	6bba      	ldr	r2, [r7, #56]	; 0x38
   42ade:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   42ae0:	4413      	add	r3, r2
   42ae2:	63bb      	str	r3, [r7, #56]	; 0x38
   42ae4:	6aba      	ldr	r2, [r7, #40]	; 0x28
   42ae6:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   42ae8:	4053      	eors	r3, r2
   42aea:	210c      	movs	r1, #12
   42aec:	4618      	mov	r0, r3
   42aee:	f7fe f853 	bl	40b98 <rotr32>
   42af2:	4603      	mov	r3, r0
   42af4:	62bb      	str	r3, [r7, #40]	; 0x28
   42af6:	69ba      	ldr	r2, [r7, #24]
   42af8:	6abb      	ldr	r3, [r7, #40]	; 0x28
   42afa:	441a      	add	r2, r3
   42afc:	230a      	movs	r3, #10
   42afe:	009b      	lsls	r3, r3, #2
   42b00:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42b04:	440b      	add	r3, r1
   42b06:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42b0a:	4413      	add	r3, r2
   42b0c:	61bb      	str	r3, [r7, #24]
   42b0e:	6cba      	ldr	r2, [r7, #72]	; 0x48
   42b10:	69bb      	ldr	r3, [r7, #24]
   42b12:	4053      	eors	r3, r2
   42b14:	2108      	movs	r1, #8
   42b16:	4618      	mov	r0, r3
   42b18:	f7fe f83e 	bl	40b98 <rotr32>
   42b1c:	4603      	mov	r3, r0
   42b1e:	64bb      	str	r3, [r7, #72]	; 0x48
   42b20:	6bba      	ldr	r2, [r7, #56]	; 0x38
   42b22:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   42b24:	4413      	add	r3, r2
   42b26:	63bb      	str	r3, [r7, #56]	; 0x38
   42b28:	6aba      	ldr	r2, [r7, #40]	; 0x28
   42b2a:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   42b2c:	4053      	eors	r3, r2
   42b2e:	2107      	movs	r1, #7
   42b30:	4618      	mov	r0, r3
   42b32:	f7fe f831 	bl	40b98 <rotr32>
   42b36:	4603      	mov	r3, r0
   42b38:	62bb      	str	r3, [r7, #40]	; 0x28
   42b3a:	68fa      	ldr	r2, [r7, #12]
   42b3c:	6a3b      	ldr	r3, [r7, #32]
   42b3e:	441a      	add	r2, r3
   42b40:	2300      	movs	r3, #0
   42b42:	009b      	lsls	r3, r3, #2
   42b44:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42b48:	440b      	add	r3, r1
   42b4a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42b4e:	4413      	add	r3, r2
   42b50:	60fb      	str	r3, [r7, #12]
   42b52:	6cba      	ldr	r2, [r7, #72]	; 0x48
   42b54:	68fb      	ldr	r3, [r7, #12]
   42b56:	4053      	eors	r3, r2
   42b58:	2110      	movs	r1, #16
   42b5a:	4618      	mov	r0, r3
   42b5c:	f7fe f81c 	bl	40b98 <rotr32>
   42b60:	4603      	mov	r3, r0
   42b62:	64bb      	str	r3, [r7, #72]	; 0x48
   42b64:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   42b66:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   42b68:	4413      	add	r3, r2
   42b6a:	637b      	str	r3, [r7, #52]	; 0x34
   42b6c:	6a3a      	ldr	r2, [r7, #32]
   42b6e:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   42b70:	4053      	eors	r3, r2
   42b72:	210c      	movs	r1, #12
   42b74:	4618      	mov	r0, r3
   42b76:	f7fe f80f 	bl	40b98 <rotr32>
   42b7a:	4603      	mov	r3, r0
   42b7c:	623b      	str	r3, [r7, #32]
   42b7e:	68fa      	ldr	r2, [r7, #12]
   42b80:	6a3b      	ldr	r3, [r7, #32]
   42b82:	441a      	add	r2, r3
   42b84:	2307      	movs	r3, #7
   42b86:	009b      	lsls	r3, r3, #2
   42b88:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42b8c:	440b      	add	r3, r1
   42b8e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42b92:	4413      	add	r3, r2
   42b94:	60fb      	str	r3, [r7, #12]
   42b96:	6cba      	ldr	r2, [r7, #72]	; 0x48
   42b98:	68fb      	ldr	r3, [r7, #12]
   42b9a:	4053      	eors	r3, r2
   42b9c:	2108      	movs	r1, #8
   42b9e:	4618      	mov	r0, r3
   42ba0:	f7fd fffa 	bl	40b98 <rotr32>
   42ba4:	4603      	mov	r3, r0
   42ba6:	64bb      	str	r3, [r7, #72]	; 0x48
   42ba8:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   42baa:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   42bac:	4413      	add	r3, r2
   42bae:	637b      	str	r3, [r7, #52]	; 0x34
   42bb0:	6a3a      	ldr	r2, [r7, #32]
   42bb2:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   42bb4:	4053      	eors	r3, r2
   42bb6:	2107      	movs	r1, #7
   42bb8:	4618      	mov	r0, r3
   42bba:	f7fd ffed 	bl	40b98 <rotr32>
   42bbe:	4603      	mov	r3, r0
   42bc0:	623b      	str	r3, [r7, #32]
   42bc2:	693a      	ldr	r2, [r7, #16]
   42bc4:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   42bc6:	441a      	add	r2, r3
   42bc8:	2306      	movs	r3, #6
   42bca:	009b      	lsls	r3, r3, #2
   42bcc:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42bd0:	440b      	add	r3, r1
   42bd2:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42bd6:	4413      	add	r3, r2
   42bd8:	613b      	str	r3, [r7, #16]
   42bda:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   42bdc:	693b      	ldr	r3, [r7, #16]
   42bde:	4053      	eors	r3, r2
   42be0:	2110      	movs	r1, #16
   42be2:	4618      	mov	r0, r3
   42be4:	f7fd ffd8 	bl	40b98 <rotr32>
   42be8:	4603      	mov	r3, r0
   42bea:	63fb      	str	r3, [r7, #60]	; 0x3c
   42bec:	6bba      	ldr	r2, [r7, #56]	; 0x38
   42bee:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   42bf0:	4413      	add	r3, r2
   42bf2:	63bb      	str	r3, [r7, #56]	; 0x38
   42bf4:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   42bf6:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   42bf8:	4053      	eors	r3, r2
   42bfa:	210c      	movs	r1, #12
   42bfc:	4618      	mov	r0, r3
   42bfe:	f7fd ffcb 	bl	40b98 <rotr32>
   42c02:	4603      	mov	r3, r0
   42c04:	627b      	str	r3, [r7, #36]	; 0x24
   42c06:	693a      	ldr	r2, [r7, #16]
   42c08:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   42c0a:	441a      	add	r2, r3
   42c0c:	2303      	movs	r3, #3
   42c0e:	009b      	lsls	r3, r3, #2
   42c10:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42c14:	440b      	add	r3, r1
   42c16:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42c1a:	4413      	add	r3, r2
   42c1c:	613b      	str	r3, [r7, #16]
   42c1e:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   42c20:	693b      	ldr	r3, [r7, #16]
   42c22:	4053      	eors	r3, r2
   42c24:	2108      	movs	r1, #8
   42c26:	4618      	mov	r0, r3
   42c28:	f7fd ffb6 	bl	40b98 <rotr32>
   42c2c:	4603      	mov	r3, r0
   42c2e:	63fb      	str	r3, [r7, #60]	; 0x3c
   42c30:	6bba      	ldr	r2, [r7, #56]	; 0x38
   42c32:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   42c34:	4413      	add	r3, r2
   42c36:	63bb      	str	r3, [r7, #56]	; 0x38
   42c38:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   42c3a:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   42c3c:	4053      	eors	r3, r2
   42c3e:	2107      	movs	r1, #7
   42c40:	4618      	mov	r0, r3
   42c42:	f7fd ffa9 	bl	40b98 <rotr32>
   42c46:	4603      	mov	r3, r0
   42c48:	627b      	str	r3, [r7, #36]	; 0x24
   42c4a:	697a      	ldr	r2, [r7, #20]
   42c4c:	6abb      	ldr	r3, [r7, #40]	; 0x28
   42c4e:	441a      	add	r2, r3
   42c50:	2309      	movs	r3, #9
   42c52:	009b      	lsls	r3, r3, #2
   42c54:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42c58:	440b      	add	r3, r1
   42c5a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42c5e:	4413      	add	r3, r2
   42c60:	617b      	str	r3, [r7, #20]
   42c62:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   42c64:	697b      	ldr	r3, [r7, #20]
   42c66:	4053      	eors	r3, r2
   42c68:	2110      	movs	r1, #16
   42c6a:	4618      	mov	r0, r3
   42c6c:	f7fd ff94 	bl	40b98 <rotr32>
   42c70:	4603      	mov	r3, r0
   42c72:	643b      	str	r3, [r7, #64]	; 0x40
   42c74:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   42c76:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   42c78:	4413      	add	r3, r2
   42c7a:	62fb      	str	r3, [r7, #44]	; 0x2c
   42c7c:	6aba      	ldr	r2, [r7, #40]	; 0x28
   42c7e:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   42c80:	4053      	eors	r3, r2
   42c82:	210c      	movs	r1, #12
   42c84:	4618      	mov	r0, r3
   42c86:	f7fd ff87 	bl	40b98 <rotr32>
   42c8a:	4603      	mov	r3, r0
   42c8c:	62bb      	str	r3, [r7, #40]	; 0x28
   42c8e:	697a      	ldr	r2, [r7, #20]
   42c90:	6abb      	ldr	r3, [r7, #40]	; 0x28
   42c92:	441a      	add	r2, r3
   42c94:	2302      	movs	r3, #2
   42c96:	009b      	lsls	r3, r3, #2
   42c98:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42c9c:	440b      	add	r3, r1
   42c9e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42ca2:	4413      	add	r3, r2
   42ca4:	617b      	str	r3, [r7, #20]
   42ca6:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   42ca8:	697b      	ldr	r3, [r7, #20]
   42caa:	4053      	eors	r3, r2
   42cac:	2108      	movs	r1, #8
   42cae:	4618      	mov	r0, r3
   42cb0:	f7fd ff72 	bl	40b98 <rotr32>
   42cb4:	4603      	mov	r3, r0
   42cb6:	643b      	str	r3, [r7, #64]	; 0x40
   42cb8:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   42cba:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   42cbc:	4413      	add	r3, r2
   42cbe:	62fb      	str	r3, [r7, #44]	; 0x2c
   42cc0:	6aba      	ldr	r2, [r7, #40]	; 0x28
   42cc2:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   42cc4:	4053      	eors	r3, r2
   42cc6:	2107      	movs	r1, #7
   42cc8:	4618      	mov	r0, r3
   42cca:	f7fd ff65 	bl	40b98 <rotr32>
   42cce:	4603      	mov	r3, r0
   42cd0:	62bb      	str	r3, [r7, #40]	; 0x28
   42cd2:	69ba      	ldr	r2, [r7, #24]
   42cd4:	69fb      	ldr	r3, [r7, #28]
   42cd6:	441a      	add	r2, r3
   42cd8:	2308      	movs	r3, #8
   42cda:	009b      	lsls	r3, r3, #2
   42cdc:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42ce0:	440b      	add	r3, r1
   42ce2:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42ce6:	4413      	add	r3, r2
   42ce8:	61bb      	str	r3, [r7, #24]
   42cea:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   42cec:	69bb      	ldr	r3, [r7, #24]
   42cee:	4053      	eors	r3, r2
   42cf0:	2110      	movs	r1, #16
   42cf2:	4618      	mov	r0, r3
   42cf4:	f7fd ff50 	bl	40b98 <rotr32>
   42cf8:	4603      	mov	r3, r0
   42cfa:	647b      	str	r3, [r7, #68]	; 0x44
   42cfc:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   42cfe:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   42d00:	4413      	add	r3, r2
   42d02:	633b      	str	r3, [r7, #48]	; 0x30
   42d04:	69fa      	ldr	r2, [r7, #28]
   42d06:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   42d08:	4053      	eors	r3, r2
   42d0a:	210c      	movs	r1, #12
   42d0c:	4618      	mov	r0, r3
   42d0e:	f7fd ff43 	bl	40b98 <rotr32>
   42d12:	4603      	mov	r3, r0
   42d14:	61fb      	str	r3, [r7, #28]
   42d16:	69ba      	ldr	r2, [r7, #24]
   42d18:	69fb      	ldr	r3, [r7, #28]
   42d1a:	441a      	add	r2, r3
   42d1c:	230b      	movs	r3, #11
   42d1e:	009b      	lsls	r3, r3, #2
   42d20:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42d24:	440b      	add	r3, r1
   42d26:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42d2a:	4413      	add	r3, r2
   42d2c:	61bb      	str	r3, [r7, #24]
   42d2e:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   42d30:	69bb      	ldr	r3, [r7, #24]
   42d32:	4053      	eors	r3, r2
   42d34:	2108      	movs	r1, #8
   42d36:	4618      	mov	r0, r3
   42d38:	f7fd ff2e 	bl	40b98 <rotr32>
   42d3c:	4603      	mov	r3, r0
   42d3e:	647b      	str	r3, [r7, #68]	; 0x44
   42d40:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   42d42:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   42d44:	4413      	add	r3, r2
   42d46:	633b      	str	r3, [r7, #48]	; 0x30
   42d48:	69fa      	ldr	r2, [r7, #28]
   42d4a:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   42d4c:	4053      	eors	r3, r2
   42d4e:	2107      	movs	r1, #7
   42d50:	4618      	mov	r0, r3
   42d52:	f7fd ff21 	bl	40b98 <rotr32>
   42d56:	4603      	mov	r3, r0
   42d58:	61fb      	str	r3, [r7, #28]
   42d5a:	68fa      	ldr	r2, [r7, #12]
   42d5c:	69fb      	ldr	r3, [r7, #28]
   42d5e:	441a      	add	r2, r3
   42d60:	230d      	movs	r3, #13
   42d62:	009b      	lsls	r3, r3, #2
   42d64:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42d68:	440b      	add	r3, r1
   42d6a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42d6e:	4413      	add	r3, r2
   42d70:	60fb      	str	r3, [r7, #12]
   42d72:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   42d74:	68fb      	ldr	r3, [r7, #12]
   42d76:	4053      	eors	r3, r2
   42d78:	2110      	movs	r1, #16
   42d7a:	4618      	mov	r0, r3
   42d7c:	f7fd ff0c 	bl	40b98 <rotr32>
   42d80:	4603      	mov	r3, r0
   42d82:	63fb      	str	r3, [r7, #60]	; 0x3c
   42d84:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   42d86:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   42d88:	4413      	add	r3, r2
   42d8a:	62fb      	str	r3, [r7, #44]	; 0x2c
   42d8c:	69fa      	ldr	r2, [r7, #28]
   42d8e:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   42d90:	4053      	eors	r3, r2
   42d92:	210c      	movs	r1, #12
   42d94:	4618      	mov	r0, r3
   42d96:	f7fd feff 	bl	40b98 <rotr32>
   42d9a:	4603      	mov	r3, r0
   42d9c:	61fb      	str	r3, [r7, #28]
   42d9e:	68fa      	ldr	r2, [r7, #12]
   42da0:	69fb      	ldr	r3, [r7, #28]
   42da2:	441a      	add	r2, r3
   42da4:	230b      	movs	r3, #11
   42da6:	009b      	lsls	r3, r3, #2
   42da8:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42dac:	440b      	add	r3, r1
   42dae:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42db2:	4413      	add	r3, r2
   42db4:	60fb      	str	r3, [r7, #12]
   42db6:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   42db8:	68fb      	ldr	r3, [r7, #12]
   42dba:	4053      	eors	r3, r2
   42dbc:	2108      	movs	r1, #8
   42dbe:	4618      	mov	r0, r3
   42dc0:	f7fd feea 	bl	40b98 <rotr32>
   42dc4:	4603      	mov	r3, r0
   42dc6:	63fb      	str	r3, [r7, #60]	; 0x3c
   42dc8:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   42dca:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   42dcc:	4413      	add	r3, r2
   42dce:	62fb      	str	r3, [r7, #44]	; 0x2c
   42dd0:	69fa      	ldr	r2, [r7, #28]
   42dd2:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   42dd4:	4053      	eors	r3, r2
   42dd6:	2107      	movs	r1, #7
   42dd8:	4618      	mov	r0, r3
   42dda:	f7fd fedd 	bl	40b98 <rotr32>
   42dde:	4603      	mov	r3, r0
   42de0:	61fb      	str	r3, [r7, #28]
   42de2:	693a      	ldr	r2, [r7, #16]
   42de4:	6a3b      	ldr	r3, [r7, #32]
   42de6:	441a      	add	r2, r3
   42de8:	2307      	movs	r3, #7
   42dea:	009b      	lsls	r3, r3, #2
   42dec:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42df0:	440b      	add	r3, r1
   42df2:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42df6:	4413      	add	r3, r2
   42df8:	613b      	str	r3, [r7, #16]
   42dfa:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   42dfc:	693b      	ldr	r3, [r7, #16]
   42dfe:	4053      	eors	r3, r2
   42e00:	2110      	movs	r1, #16
   42e02:	4618      	mov	r0, r3
   42e04:	f7fd fec8 	bl	40b98 <rotr32>
   42e08:	4603      	mov	r3, r0
   42e0a:	643b      	str	r3, [r7, #64]	; 0x40
   42e0c:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   42e0e:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   42e10:	4413      	add	r3, r2
   42e12:	633b      	str	r3, [r7, #48]	; 0x30
   42e14:	6a3a      	ldr	r2, [r7, #32]
   42e16:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   42e18:	4053      	eors	r3, r2
   42e1a:	210c      	movs	r1, #12
   42e1c:	4618      	mov	r0, r3
   42e1e:	f7fd febb 	bl	40b98 <rotr32>
   42e22:	4603      	mov	r3, r0
   42e24:	623b      	str	r3, [r7, #32]
   42e26:	693a      	ldr	r2, [r7, #16]
   42e28:	6a3b      	ldr	r3, [r7, #32]
   42e2a:	441a      	add	r2, r3
   42e2c:	230e      	movs	r3, #14
   42e2e:	009b      	lsls	r3, r3, #2
   42e30:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42e34:	440b      	add	r3, r1
   42e36:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42e3a:	4413      	add	r3, r2
   42e3c:	613b      	str	r3, [r7, #16]
   42e3e:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   42e40:	693b      	ldr	r3, [r7, #16]
   42e42:	4053      	eors	r3, r2
   42e44:	2108      	movs	r1, #8
   42e46:	4618      	mov	r0, r3
   42e48:	f7fd fea6 	bl	40b98 <rotr32>
   42e4c:	4603      	mov	r3, r0
   42e4e:	643b      	str	r3, [r7, #64]	; 0x40
   42e50:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   42e52:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   42e54:	4413      	add	r3, r2
   42e56:	633b      	str	r3, [r7, #48]	; 0x30
   42e58:	6a3a      	ldr	r2, [r7, #32]
   42e5a:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   42e5c:	4053      	eors	r3, r2
   42e5e:	2107      	movs	r1, #7
   42e60:	4618      	mov	r0, r3
   42e62:	f7fd fe99 	bl	40b98 <rotr32>
   42e66:	4603      	mov	r3, r0
   42e68:	623b      	str	r3, [r7, #32]
   42e6a:	697a      	ldr	r2, [r7, #20]
   42e6c:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   42e6e:	441a      	add	r2, r3
   42e70:	230c      	movs	r3, #12
   42e72:	009b      	lsls	r3, r3, #2
   42e74:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42e78:	440b      	add	r3, r1
   42e7a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42e7e:	4413      	add	r3, r2
   42e80:	617b      	str	r3, [r7, #20]
   42e82:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   42e84:	697b      	ldr	r3, [r7, #20]
   42e86:	4053      	eors	r3, r2
   42e88:	2110      	movs	r1, #16
   42e8a:	4618      	mov	r0, r3
   42e8c:	f7fd fe84 	bl	40b98 <rotr32>
   42e90:	4603      	mov	r3, r0
   42e92:	647b      	str	r3, [r7, #68]	; 0x44
   42e94:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   42e96:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   42e98:	4413      	add	r3, r2
   42e9a:	637b      	str	r3, [r7, #52]	; 0x34
   42e9c:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   42e9e:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   42ea0:	4053      	eors	r3, r2
   42ea2:	210c      	movs	r1, #12
   42ea4:	4618      	mov	r0, r3
   42ea6:	f7fd fe77 	bl	40b98 <rotr32>
   42eaa:	4603      	mov	r3, r0
   42eac:	627b      	str	r3, [r7, #36]	; 0x24
   42eae:	697a      	ldr	r2, [r7, #20]
   42eb0:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   42eb2:	441a      	add	r2, r3
   42eb4:	2301      	movs	r3, #1
   42eb6:	009b      	lsls	r3, r3, #2
   42eb8:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42ebc:	440b      	add	r3, r1
   42ebe:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42ec2:	4413      	add	r3, r2
   42ec4:	617b      	str	r3, [r7, #20]
   42ec6:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   42ec8:	697b      	ldr	r3, [r7, #20]
   42eca:	4053      	eors	r3, r2
   42ecc:	2108      	movs	r1, #8
   42ece:	4618      	mov	r0, r3
   42ed0:	f7fd fe62 	bl	40b98 <rotr32>
   42ed4:	4603      	mov	r3, r0
   42ed6:	647b      	str	r3, [r7, #68]	; 0x44
   42ed8:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   42eda:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   42edc:	4413      	add	r3, r2
   42ede:	637b      	str	r3, [r7, #52]	; 0x34
   42ee0:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   42ee2:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   42ee4:	4053      	eors	r3, r2
   42ee6:	2107      	movs	r1, #7
   42ee8:	4618      	mov	r0, r3
   42eea:	f7fd fe55 	bl	40b98 <rotr32>
   42eee:	4603      	mov	r3, r0
   42ef0:	627b      	str	r3, [r7, #36]	; 0x24
   42ef2:	69ba      	ldr	r2, [r7, #24]
   42ef4:	6abb      	ldr	r3, [r7, #40]	; 0x28
   42ef6:	441a      	add	r2, r3
   42ef8:	2303      	movs	r3, #3
   42efa:	009b      	lsls	r3, r3, #2
   42efc:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42f00:	440b      	add	r3, r1
   42f02:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42f06:	4413      	add	r3, r2
   42f08:	61bb      	str	r3, [r7, #24]
   42f0a:	6cba      	ldr	r2, [r7, #72]	; 0x48
   42f0c:	69bb      	ldr	r3, [r7, #24]
   42f0e:	4053      	eors	r3, r2
   42f10:	2110      	movs	r1, #16
   42f12:	4618      	mov	r0, r3
   42f14:	f7fd fe40 	bl	40b98 <rotr32>
   42f18:	4603      	mov	r3, r0
   42f1a:	64bb      	str	r3, [r7, #72]	; 0x48
   42f1c:	6bba      	ldr	r2, [r7, #56]	; 0x38
   42f1e:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   42f20:	4413      	add	r3, r2
   42f22:	63bb      	str	r3, [r7, #56]	; 0x38
   42f24:	6aba      	ldr	r2, [r7, #40]	; 0x28
   42f26:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   42f28:	4053      	eors	r3, r2
   42f2a:	210c      	movs	r1, #12
   42f2c:	4618      	mov	r0, r3
   42f2e:	f7fd fe33 	bl	40b98 <rotr32>
   42f32:	4603      	mov	r3, r0
   42f34:	62bb      	str	r3, [r7, #40]	; 0x28
   42f36:	69ba      	ldr	r2, [r7, #24]
   42f38:	6abb      	ldr	r3, [r7, #40]	; 0x28
   42f3a:	441a      	add	r2, r3
   42f3c:	2309      	movs	r3, #9
   42f3e:	009b      	lsls	r3, r3, #2
   42f40:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42f44:	440b      	add	r3, r1
   42f46:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42f4a:	4413      	add	r3, r2
   42f4c:	61bb      	str	r3, [r7, #24]
   42f4e:	6cba      	ldr	r2, [r7, #72]	; 0x48
   42f50:	69bb      	ldr	r3, [r7, #24]
   42f52:	4053      	eors	r3, r2
   42f54:	2108      	movs	r1, #8
   42f56:	4618      	mov	r0, r3
   42f58:	f7fd fe1e 	bl	40b98 <rotr32>
   42f5c:	4603      	mov	r3, r0
   42f5e:	64bb      	str	r3, [r7, #72]	; 0x48
   42f60:	6bba      	ldr	r2, [r7, #56]	; 0x38
   42f62:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   42f64:	4413      	add	r3, r2
   42f66:	63bb      	str	r3, [r7, #56]	; 0x38
   42f68:	6aba      	ldr	r2, [r7, #40]	; 0x28
   42f6a:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   42f6c:	4053      	eors	r3, r2
   42f6e:	2107      	movs	r1, #7
   42f70:	4618      	mov	r0, r3
   42f72:	f7fd fe11 	bl	40b98 <rotr32>
   42f76:	4603      	mov	r3, r0
   42f78:	62bb      	str	r3, [r7, #40]	; 0x28
   42f7a:	68fa      	ldr	r2, [r7, #12]
   42f7c:	6a3b      	ldr	r3, [r7, #32]
   42f7e:	441a      	add	r2, r3
   42f80:	2305      	movs	r3, #5
   42f82:	009b      	lsls	r3, r3, #2
   42f84:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42f88:	440b      	add	r3, r1
   42f8a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42f8e:	4413      	add	r3, r2
   42f90:	60fb      	str	r3, [r7, #12]
   42f92:	6cba      	ldr	r2, [r7, #72]	; 0x48
   42f94:	68fb      	ldr	r3, [r7, #12]
   42f96:	4053      	eors	r3, r2
   42f98:	2110      	movs	r1, #16
   42f9a:	4618      	mov	r0, r3
   42f9c:	f7fd fdfc 	bl	40b98 <rotr32>
   42fa0:	4603      	mov	r3, r0
   42fa2:	64bb      	str	r3, [r7, #72]	; 0x48
   42fa4:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   42fa6:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   42fa8:	4413      	add	r3, r2
   42faa:	637b      	str	r3, [r7, #52]	; 0x34
   42fac:	6a3a      	ldr	r2, [r7, #32]
   42fae:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   42fb0:	4053      	eors	r3, r2
   42fb2:	210c      	movs	r1, #12
   42fb4:	4618      	mov	r0, r3
   42fb6:	f7fd fdef 	bl	40b98 <rotr32>
   42fba:	4603      	mov	r3, r0
   42fbc:	623b      	str	r3, [r7, #32]
   42fbe:	68fa      	ldr	r2, [r7, #12]
   42fc0:	6a3b      	ldr	r3, [r7, #32]
   42fc2:	441a      	add	r2, r3
   42fc4:	2300      	movs	r3, #0
   42fc6:	009b      	lsls	r3, r3, #2
   42fc8:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42fcc:	440b      	add	r3, r1
   42fce:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42fd2:	4413      	add	r3, r2
   42fd4:	60fb      	str	r3, [r7, #12]
   42fd6:	6cba      	ldr	r2, [r7, #72]	; 0x48
   42fd8:	68fb      	ldr	r3, [r7, #12]
   42fda:	4053      	eors	r3, r2
   42fdc:	2108      	movs	r1, #8
   42fde:	4618      	mov	r0, r3
   42fe0:	f7fd fdda 	bl	40b98 <rotr32>
   42fe4:	4603      	mov	r3, r0
   42fe6:	64bb      	str	r3, [r7, #72]	; 0x48
   42fe8:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   42fea:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   42fec:	4413      	add	r3, r2
   42fee:	637b      	str	r3, [r7, #52]	; 0x34
   42ff0:	6a3a      	ldr	r2, [r7, #32]
   42ff2:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   42ff4:	4053      	eors	r3, r2
   42ff6:	2107      	movs	r1, #7
   42ff8:	4618      	mov	r0, r3
   42ffa:	f7fd fdcd 	bl	40b98 <rotr32>
   42ffe:	4603      	mov	r3, r0
   43000:	623b      	str	r3, [r7, #32]
   43002:	693a      	ldr	r2, [r7, #16]
   43004:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   43006:	441a      	add	r2, r3
   43008:	230f      	movs	r3, #15
   4300a:	009b      	lsls	r3, r3, #2
   4300c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   43010:	440b      	add	r3, r1
   43012:	f853 3c44 	ldr.w	r3, [r3, #-68]
   43016:	4413      	add	r3, r2
   43018:	613b      	str	r3, [r7, #16]
   4301a:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   4301c:	693b      	ldr	r3, [r7, #16]
   4301e:	4053      	eors	r3, r2
   43020:	2110      	movs	r1, #16
   43022:	4618      	mov	r0, r3
   43024:	f7fd fdb8 	bl	40b98 <rotr32>
   43028:	4603      	mov	r3, r0
   4302a:	63fb      	str	r3, [r7, #60]	; 0x3c
   4302c:	6bba      	ldr	r2, [r7, #56]	; 0x38
   4302e:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   43030:	4413      	add	r3, r2
   43032:	63bb      	str	r3, [r7, #56]	; 0x38
   43034:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   43036:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   43038:	4053      	eors	r3, r2
   4303a:	210c      	movs	r1, #12
   4303c:	4618      	mov	r0, r3
   4303e:	f7fd fdab 	bl	40b98 <rotr32>
   43042:	4603      	mov	r3, r0
   43044:	627b      	str	r3, [r7, #36]	; 0x24
   43046:	693a      	ldr	r2, [r7, #16]
   43048:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   4304a:	441a      	add	r2, r3
   4304c:	2304      	movs	r3, #4
   4304e:	009b      	lsls	r3, r3, #2
   43050:	f107 0190 	add.w	r1, r7, #144	; 0x90
   43054:	440b      	add	r3, r1
   43056:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4305a:	4413      	add	r3, r2
   4305c:	613b      	str	r3, [r7, #16]
   4305e:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   43060:	693b      	ldr	r3, [r7, #16]
   43062:	4053      	eors	r3, r2
   43064:	2108      	movs	r1, #8
   43066:	4618      	mov	r0, r3
   43068:	f7fd fd96 	bl	40b98 <rotr32>
   4306c:	4603      	mov	r3, r0
   4306e:	63fb      	str	r3, [r7, #60]	; 0x3c
   43070:	6bba      	ldr	r2, [r7, #56]	; 0x38
   43072:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   43074:	4413      	add	r3, r2
   43076:	63bb      	str	r3, [r7, #56]	; 0x38
   43078:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   4307a:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   4307c:	4053      	eors	r3, r2
   4307e:	2107      	movs	r1, #7
   43080:	4618      	mov	r0, r3
   43082:	f7fd fd89 	bl	40b98 <rotr32>
   43086:	4603      	mov	r3, r0
   43088:	627b      	str	r3, [r7, #36]	; 0x24
   4308a:	697a      	ldr	r2, [r7, #20]
   4308c:	6abb      	ldr	r3, [r7, #40]	; 0x28
   4308e:	441a      	add	r2, r3
   43090:	2308      	movs	r3, #8
   43092:	009b      	lsls	r3, r3, #2
   43094:	f107 0190 	add.w	r1, r7, #144	; 0x90
   43098:	440b      	add	r3, r1
   4309a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4309e:	4413      	add	r3, r2
   430a0:	617b      	str	r3, [r7, #20]
   430a2:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   430a4:	697b      	ldr	r3, [r7, #20]
   430a6:	4053      	eors	r3, r2
   430a8:	2110      	movs	r1, #16
   430aa:	4618      	mov	r0, r3
   430ac:	f7fd fd74 	bl	40b98 <rotr32>
   430b0:	4603      	mov	r3, r0
   430b2:	643b      	str	r3, [r7, #64]	; 0x40
   430b4:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   430b6:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   430b8:	4413      	add	r3, r2
   430ba:	62fb      	str	r3, [r7, #44]	; 0x2c
   430bc:	6aba      	ldr	r2, [r7, #40]	; 0x28
   430be:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   430c0:	4053      	eors	r3, r2
   430c2:	210c      	movs	r1, #12
   430c4:	4618      	mov	r0, r3
   430c6:	f7fd fd67 	bl	40b98 <rotr32>
   430ca:	4603      	mov	r3, r0
   430cc:	62bb      	str	r3, [r7, #40]	; 0x28
   430ce:	697a      	ldr	r2, [r7, #20]
   430d0:	6abb      	ldr	r3, [r7, #40]	; 0x28
   430d2:	441a      	add	r2, r3
   430d4:	2306      	movs	r3, #6
   430d6:	009b      	lsls	r3, r3, #2
   430d8:	f107 0190 	add.w	r1, r7, #144	; 0x90
   430dc:	440b      	add	r3, r1
   430de:	f853 3c44 	ldr.w	r3, [r3, #-68]
   430e2:	4413      	add	r3, r2
   430e4:	617b      	str	r3, [r7, #20]
   430e6:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   430e8:	697b      	ldr	r3, [r7, #20]
   430ea:	4053      	eors	r3, r2
   430ec:	2108      	movs	r1, #8
   430ee:	4618      	mov	r0, r3
   430f0:	f7fd fd52 	bl	40b98 <rotr32>
   430f4:	4603      	mov	r3, r0
   430f6:	643b      	str	r3, [r7, #64]	; 0x40
   430f8:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   430fa:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   430fc:	4413      	add	r3, r2
   430fe:	62fb      	str	r3, [r7, #44]	; 0x2c
   43100:	6aba      	ldr	r2, [r7, #40]	; 0x28
   43102:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   43104:	4053      	eors	r3, r2
   43106:	2107      	movs	r1, #7
   43108:	4618      	mov	r0, r3
   4310a:	f7fd fd45 	bl	40b98 <rotr32>
   4310e:	4603      	mov	r3, r0
   43110:	62bb      	str	r3, [r7, #40]	; 0x28
   43112:	69ba      	ldr	r2, [r7, #24]
   43114:	69fb      	ldr	r3, [r7, #28]
   43116:	441a      	add	r2, r3
   43118:	2302      	movs	r3, #2
   4311a:	009b      	lsls	r3, r3, #2
   4311c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   43120:	440b      	add	r3, r1
   43122:	f853 3c44 	ldr.w	r3, [r3, #-68]
   43126:	4413      	add	r3, r2
   43128:	61bb      	str	r3, [r7, #24]
   4312a:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   4312c:	69bb      	ldr	r3, [r7, #24]
   4312e:	4053      	eors	r3, r2
   43130:	2110      	movs	r1, #16
   43132:	4618      	mov	r0, r3
   43134:	f7fd fd30 	bl	40b98 <rotr32>
   43138:	4603      	mov	r3, r0
   4313a:	647b      	str	r3, [r7, #68]	; 0x44
   4313c:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   4313e:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   43140:	4413      	add	r3, r2
   43142:	633b      	str	r3, [r7, #48]	; 0x30
   43144:	69fa      	ldr	r2, [r7, #28]
   43146:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   43148:	4053      	eors	r3, r2
   4314a:	210c      	movs	r1, #12
   4314c:	4618      	mov	r0, r3
   4314e:	f7fd fd23 	bl	40b98 <rotr32>
   43152:	4603      	mov	r3, r0
   43154:	61fb      	str	r3, [r7, #28]
   43156:	69ba      	ldr	r2, [r7, #24]
   43158:	69fb      	ldr	r3, [r7, #28]
   4315a:	441a      	add	r2, r3
   4315c:	230a      	movs	r3, #10
   4315e:	009b      	lsls	r3, r3, #2
   43160:	f107 0190 	add.w	r1, r7, #144	; 0x90
   43164:	440b      	add	r3, r1
   43166:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4316a:	4413      	add	r3, r2
   4316c:	61bb      	str	r3, [r7, #24]
   4316e:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   43170:	69bb      	ldr	r3, [r7, #24]
   43172:	4053      	eors	r3, r2
   43174:	2108      	movs	r1, #8
   43176:	4618      	mov	r0, r3
   43178:	f7fd fd0e 	bl	40b98 <rotr32>
   4317c:	4603      	mov	r3, r0
   4317e:	647b      	str	r3, [r7, #68]	; 0x44
   43180:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   43182:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   43184:	4413      	add	r3, r2
   43186:	633b      	str	r3, [r7, #48]	; 0x30
   43188:	69fa      	ldr	r2, [r7, #28]
   4318a:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   4318c:	4053      	eors	r3, r2
   4318e:	2107      	movs	r1, #7
   43190:	4618      	mov	r0, r3
   43192:	f7fd fd01 	bl	40b98 <rotr32>
   43196:	4603      	mov	r3, r0
   43198:	61fb      	str	r3, [r7, #28]
   4319a:	68fa      	ldr	r2, [r7, #12]
   4319c:	69fb      	ldr	r3, [r7, #28]
   4319e:	441a      	add	r2, r3
   431a0:	2306      	movs	r3, #6
   431a2:	009b      	lsls	r3, r3, #2
   431a4:	f107 0190 	add.w	r1, r7, #144	; 0x90
   431a8:	440b      	add	r3, r1
   431aa:	f853 3c44 	ldr.w	r3, [r3, #-68]
   431ae:	4413      	add	r3, r2
   431b0:	60fb      	str	r3, [r7, #12]
   431b2:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   431b4:	68fb      	ldr	r3, [r7, #12]
   431b6:	4053      	eors	r3, r2
   431b8:	2110      	movs	r1, #16
   431ba:	4618      	mov	r0, r3
   431bc:	f7fd fcec 	bl	40b98 <rotr32>
   431c0:	4603      	mov	r3, r0
   431c2:	63fb      	str	r3, [r7, #60]	; 0x3c
   431c4:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   431c6:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   431c8:	4413      	add	r3, r2
   431ca:	62fb      	str	r3, [r7, #44]	; 0x2c
   431cc:	69fa      	ldr	r2, [r7, #28]
   431ce:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   431d0:	4053      	eors	r3, r2
   431d2:	210c      	movs	r1, #12
   431d4:	4618      	mov	r0, r3
   431d6:	f7fd fcdf 	bl	40b98 <rotr32>
   431da:	4603      	mov	r3, r0
   431dc:	61fb      	str	r3, [r7, #28]
   431de:	68fa      	ldr	r2, [r7, #12]
   431e0:	69fb      	ldr	r3, [r7, #28]
   431e2:	441a      	add	r2, r3
   431e4:	230f      	movs	r3, #15
   431e6:	009b      	lsls	r3, r3, #2
   431e8:	f107 0190 	add.w	r1, r7, #144	; 0x90
   431ec:	440b      	add	r3, r1
   431ee:	f853 3c44 	ldr.w	r3, [r3, #-68]
   431f2:	4413      	add	r3, r2
   431f4:	60fb      	str	r3, [r7, #12]
   431f6:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   431f8:	68fb      	ldr	r3, [r7, #12]
   431fa:	4053      	eors	r3, r2
   431fc:	2108      	movs	r1, #8
   431fe:	4618      	mov	r0, r3
   43200:	f7fd fcca 	bl	40b98 <rotr32>
   43204:	4603      	mov	r3, r0
   43206:	63fb      	str	r3, [r7, #60]	; 0x3c
   43208:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   4320a:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   4320c:	4413      	add	r3, r2
   4320e:	62fb      	str	r3, [r7, #44]	; 0x2c
   43210:	69fa      	ldr	r2, [r7, #28]
   43212:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   43214:	4053      	eors	r3, r2
   43216:	2107      	movs	r1, #7
   43218:	4618      	mov	r0, r3
   4321a:	f7fd fcbd 	bl	40b98 <rotr32>
   4321e:	4603      	mov	r3, r0
   43220:	61fb      	str	r3, [r7, #28]
   43222:	693a      	ldr	r2, [r7, #16]
   43224:	6a3b      	ldr	r3, [r7, #32]
   43226:	441a      	add	r2, r3
   43228:	230e      	movs	r3, #14
   4322a:	009b      	lsls	r3, r3, #2
   4322c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   43230:	440b      	add	r3, r1
   43232:	f853 3c44 	ldr.w	r3, [r3, #-68]
   43236:	4413      	add	r3, r2
   43238:	613b      	str	r3, [r7, #16]
   4323a:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   4323c:	693b      	ldr	r3, [r7, #16]
   4323e:	4053      	eors	r3, r2
   43240:	2110      	movs	r1, #16
   43242:	4618      	mov	r0, r3
   43244:	f7fd fca8 	bl	40b98 <rotr32>
   43248:	4603      	mov	r3, r0
   4324a:	643b      	str	r3, [r7, #64]	; 0x40
   4324c:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   4324e:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   43250:	4413      	add	r3, r2
   43252:	633b      	str	r3, [r7, #48]	; 0x30
   43254:	6a3a      	ldr	r2, [r7, #32]
   43256:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   43258:	4053      	eors	r3, r2
   4325a:	210c      	movs	r1, #12
   4325c:	4618      	mov	r0, r3
   4325e:	f7fd fc9b 	bl	40b98 <rotr32>
   43262:	4603      	mov	r3, r0
   43264:	623b      	str	r3, [r7, #32]
   43266:	693a      	ldr	r2, [r7, #16]
   43268:	6a3b      	ldr	r3, [r7, #32]
   4326a:	441a      	add	r2, r3
   4326c:	2309      	movs	r3, #9
   4326e:	009b      	lsls	r3, r3, #2
   43270:	f107 0190 	add.w	r1, r7, #144	; 0x90
   43274:	440b      	add	r3, r1
   43276:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4327a:	4413      	add	r3, r2
   4327c:	613b      	str	r3, [r7, #16]
   4327e:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   43280:	693b      	ldr	r3, [r7, #16]
   43282:	4053      	eors	r3, r2
   43284:	2108      	movs	r1, #8
   43286:	4618      	mov	r0, r3
   43288:	f7fd fc86 	bl	40b98 <rotr32>
   4328c:	4603      	mov	r3, r0
   4328e:	643b      	str	r3, [r7, #64]	; 0x40
   43290:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   43292:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   43294:	4413      	add	r3, r2
   43296:	633b      	str	r3, [r7, #48]	; 0x30
   43298:	6a3a      	ldr	r2, [r7, #32]
   4329a:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   4329c:	4053      	eors	r3, r2
   4329e:	2107      	movs	r1, #7
   432a0:	4618      	mov	r0, r3
   432a2:	f7fd fc79 	bl	40b98 <rotr32>
   432a6:	4603      	mov	r3, r0
   432a8:	623b      	str	r3, [r7, #32]
   432aa:	697a      	ldr	r2, [r7, #20]
   432ac:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   432ae:	441a      	add	r2, r3
   432b0:	230b      	movs	r3, #11
   432b2:	009b      	lsls	r3, r3, #2
   432b4:	f107 0190 	add.w	r1, r7, #144	; 0x90
   432b8:	440b      	add	r3, r1
   432ba:	f853 3c44 	ldr.w	r3, [r3, #-68]
   432be:	4413      	add	r3, r2
   432c0:	617b      	str	r3, [r7, #20]
   432c2:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   432c4:	697b      	ldr	r3, [r7, #20]
   432c6:	4053      	eors	r3, r2
   432c8:	2110      	movs	r1, #16
   432ca:	4618      	mov	r0, r3
   432cc:	f7fd fc64 	bl	40b98 <rotr32>
   432d0:	4603      	mov	r3, r0
   432d2:	647b      	str	r3, [r7, #68]	; 0x44
   432d4:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   432d6:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   432d8:	4413      	add	r3, r2
   432da:	637b      	str	r3, [r7, #52]	; 0x34
   432dc:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   432de:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   432e0:	4053      	eors	r3, r2
   432e2:	210c      	movs	r1, #12
   432e4:	4618      	mov	r0, r3
   432e6:	f7fd fc57 	bl	40b98 <rotr32>
   432ea:	4603      	mov	r3, r0
   432ec:	627b      	str	r3, [r7, #36]	; 0x24
   432ee:	697a      	ldr	r2, [r7, #20]
   432f0:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   432f2:	441a      	add	r2, r3
   432f4:	2303      	movs	r3, #3
   432f6:	009b      	lsls	r3, r3, #2
   432f8:	f107 0190 	add.w	r1, r7, #144	; 0x90
   432fc:	440b      	add	r3, r1
   432fe:	f853 3c44 	ldr.w	r3, [r3, #-68]
   43302:	4413      	add	r3, r2
   43304:	617b      	str	r3, [r7, #20]
   43306:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   43308:	697b      	ldr	r3, [r7, #20]
   4330a:	4053      	eors	r3, r2
   4330c:	2108      	movs	r1, #8
   4330e:	4618      	mov	r0, r3
   43310:	f7fd fc42 	bl	40b98 <rotr32>
   43314:	4603      	mov	r3, r0
   43316:	647b      	str	r3, [r7, #68]	; 0x44
   43318:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   4331a:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   4331c:	4413      	add	r3, r2
   4331e:	637b      	str	r3, [r7, #52]	; 0x34
   43320:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   43322:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   43324:	4053      	eors	r3, r2
   43326:	2107      	movs	r1, #7
   43328:	4618      	mov	r0, r3
   4332a:	f7fd fc35 	bl	40b98 <rotr32>
   4332e:	4603      	mov	r3, r0
   43330:	627b      	str	r3, [r7, #36]	; 0x24
   43332:	69ba      	ldr	r2, [r7, #24]
   43334:	6abb      	ldr	r3, [r7, #40]	; 0x28
   43336:	441a      	add	r2, r3
   43338:	2300      	movs	r3, #0
   4333a:	009b      	lsls	r3, r3, #2
   4333c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   43340:	440b      	add	r3, r1
   43342:	f853 3c44 	ldr.w	r3, [r3, #-68]
   43346:	4413      	add	r3, r2
   43348:	61bb      	str	r3, [r7, #24]
   4334a:	6cba      	ldr	r2, [r7, #72]	; 0x48
   4334c:	69bb      	ldr	r3, [r7, #24]
   4334e:	4053      	eors	r3, r2
   43350:	2110      	movs	r1, #16
   43352:	4618      	mov	r0, r3
   43354:	f7fd fc20 	bl	40b98 <rotr32>
   43358:	4603      	mov	r3, r0
   4335a:	64bb      	str	r3, [r7, #72]	; 0x48
   4335c:	6bba      	ldr	r2, [r7, #56]	; 0x38
   4335e:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   43360:	4413      	add	r3, r2
   43362:	63bb      	str	r3, [r7, #56]	; 0x38
   43364:	6aba      	ldr	r2, [r7, #40]	; 0x28
   43366:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   43368:	4053      	eors	r3, r2
   4336a:	210c      	movs	r1, #12
   4336c:	4618      	mov	r0, r3
   4336e:	f7fd fc13 	bl	40b98 <rotr32>
   43372:	4603      	mov	r3, r0
   43374:	62bb      	str	r3, [r7, #40]	; 0x28
   43376:	69ba      	ldr	r2, [r7, #24]
   43378:	6abb      	ldr	r3, [r7, #40]	; 0x28
   4337a:	441a      	add	r2, r3
   4337c:	2308      	movs	r3, #8
   4337e:	009b      	lsls	r3, r3, #2
   43380:	f107 0190 	add.w	r1, r7, #144	; 0x90
   43384:	440b      	add	r3, r1
   43386:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4338a:	4413      	add	r3, r2
   4338c:	61bb      	str	r3, [r7, #24]
   4338e:	6cba      	ldr	r2, [r7, #72]	; 0x48
   43390:	69bb      	ldr	r3, [r7, #24]
   43392:	4053      	eors	r3, r2
   43394:	2108      	movs	r1, #8
   43396:	4618      	mov	r0, r3
   43398:	f7fd fbfe 	bl	40b98 <rotr32>
   4339c:	4603      	mov	r3, r0
   4339e:	64bb      	str	r3, [r7, #72]	; 0x48
   433a0:	6bba      	ldr	r2, [r7, #56]	; 0x38
   433a2:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   433a4:	4413      	add	r3, r2
   433a6:	63bb      	str	r3, [r7, #56]	; 0x38
   433a8:	6aba      	ldr	r2, [r7, #40]	; 0x28
   433aa:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   433ac:	4053      	eors	r3, r2
   433ae:	2107      	movs	r1, #7
   433b0:	4618      	mov	r0, r3
   433b2:	f7fd fbf1 	bl	40b98 <rotr32>
   433b6:	4603      	mov	r3, r0
   433b8:	62bb      	str	r3, [r7, #40]	; 0x28
   433ba:	68fa      	ldr	r2, [r7, #12]
   433bc:	6a3b      	ldr	r3, [r7, #32]
   433be:	441a      	add	r2, r3
   433c0:	230c      	movs	r3, #12
   433c2:	009b      	lsls	r3, r3, #2
   433c4:	f107 0190 	add.w	r1, r7, #144	; 0x90
   433c8:	440b      	add	r3, r1
   433ca:	f853 3c44 	ldr.w	r3, [r3, #-68]
   433ce:	4413      	add	r3, r2
   433d0:	60fb      	str	r3, [r7, #12]
   433d2:	6cba      	ldr	r2, [r7, #72]	; 0x48
   433d4:	68fb      	ldr	r3, [r7, #12]
   433d6:	4053      	eors	r3, r2
   433d8:	2110      	movs	r1, #16
   433da:	4618      	mov	r0, r3
   433dc:	f7fd fbdc 	bl	40b98 <rotr32>
   433e0:	4603      	mov	r3, r0
   433e2:	64bb      	str	r3, [r7, #72]	; 0x48
   433e4:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   433e6:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   433e8:	4413      	add	r3, r2
   433ea:	637b      	str	r3, [r7, #52]	; 0x34
   433ec:	6a3a      	ldr	r2, [r7, #32]
   433ee:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   433f0:	4053      	eors	r3, r2
   433f2:	210c      	movs	r1, #12
   433f4:	4618      	mov	r0, r3
   433f6:	f7fd fbcf 	bl	40b98 <rotr32>
   433fa:	4603      	mov	r3, r0
   433fc:	623b      	str	r3, [r7, #32]
   433fe:	68fa      	ldr	r2, [r7, #12]
   43400:	6a3b      	ldr	r3, [r7, #32]
   43402:	441a      	add	r2, r3
   43404:	2302      	movs	r3, #2
   43406:	009b      	lsls	r3, r3, #2
   43408:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4340c:	440b      	add	r3, r1
   4340e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   43412:	4413      	add	r3, r2
   43414:	60fb      	str	r3, [r7, #12]
   43416:	6cba      	ldr	r2, [r7, #72]	; 0x48
   43418:	68fb      	ldr	r3, [r7, #12]
   4341a:	4053      	eors	r3, r2
   4341c:	2108      	movs	r1, #8
   4341e:	4618      	mov	r0, r3
   43420:	f7fd fbba 	bl	40b98 <rotr32>
   43424:	4603      	mov	r3, r0
   43426:	64bb      	str	r3, [r7, #72]	; 0x48
   43428:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   4342a:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   4342c:	4413      	add	r3, r2
   4342e:	637b      	str	r3, [r7, #52]	; 0x34
   43430:	6a3a      	ldr	r2, [r7, #32]
   43432:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   43434:	4053      	eors	r3, r2
   43436:	2107      	movs	r1, #7
   43438:	4618      	mov	r0, r3
   4343a:	f7fd fbad 	bl	40b98 <rotr32>
   4343e:	4603      	mov	r3, r0
   43440:	623b      	str	r3, [r7, #32]
   43442:	693a      	ldr	r2, [r7, #16]
   43444:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   43446:	441a      	add	r2, r3
   43448:	230d      	movs	r3, #13
   4344a:	009b      	lsls	r3, r3, #2
   4344c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   43450:	440b      	add	r3, r1
   43452:	f853 3c44 	ldr.w	r3, [r3, #-68]
   43456:	4413      	add	r3, r2
   43458:	613b      	str	r3, [r7, #16]
   4345a:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   4345c:	693b      	ldr	r3, [r7, #16]
   4345e:	4053      	eors	r3, r2
   43460:	2110      	movs	r1, #16
   43462:	4618      	mov	r0, r3
   43464:	f7fd fb98 	bl	40b98 <rotr32>
   43468:	4603      	mov	r3, r0
   4346a:	63fb      	str	r3, [r7, #60]	; 0x3c
   4346c:	6bba      	ldr	r2, [r7, #56]	; 0x38
   4346e:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   43470:	4413      	add	r3, r2
   43472:	63bb      	str	r3, [r7, #56]	; 0x38
   43474:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   43476:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   43478:	4053      	eors	r3, r2
   4347a:	210c      	movs	r1, #12
   4347c:	4618      	mov	r0, r3
   4347e:	f7fd fb8b 	bl	40b98 <rotr32>
   43482:	4603      	mov	r3, r0
   43484:	627b      	str	r3, [r7, #36]	; 0x24
   43486:	693a      	ldr	r2, [r7, #16]
   43488:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   4348a:	441a      	add	r2, r3
   4348c:	2307      	movs	r3, #7
   4348e:	009b      	lsls	r3, r3, #2
   43490:	f107 0190 	add.w	r1, r7, #144	; 0x90
   43494:	440b      	add	r3, r1
   43496:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4349a:	4413      	add	r3, r2
   4349c:	613b      	str	r3, [r7, #16]
   4349e:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   434a0:	693b      	ldr	r3, [r7, #16]
   434a2:	4053      	eors	r3, r2
   434a4:	2108      	movs	r1, #8
   434a6:	4618      	mov	r0, r3
   434a8:	f7fd fb76 	bl	40b98 <rotr32>
   434ac:	4603      	mov	r3, r0
   434ae:	63fb      	str	r3, [r7, #60]	; 0x3c
   434b0:	6bba      	ldr	r2, [r7, #56]	; 0x38
   434b2:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   434b4:	4413      	add	r3, r2
   434b6:	63bb      	str	r3, [r7, #56]	; 0x38
   434b8:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   434ba:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   434bc:	4053      	eors	r3, r2
   434be:	2107      	movs	r1, #7
   434c0:	4618      	mov	r0, r3
   434c2:	f7fd fb69 	bl	40b98 <rotr32>
   434c6:	4603      	mov	r3, r0
   434c8:	627b      	str	r3, [r7, #36]	; 0x24
   434ca:	697a      	ldr	r2, [r7, #20]
   434cc:	6abb      	ldr	r3, [r7, #40]	; 0x28
   434ce:	441a      	add	r2, r3
   434d0:	2301      	movs	r3, #1
   434d2:	009b      	lsls	r3, r3, #2
   434d4:	f107 0190 	add.w	r1, r7, #144	; 0x90
   434d8:	440b      	add	r3, r1
   434da:	f853 3c44 	ldr.w	r3, [r3, #-68]
   434de:	4413      	add	r3, r2
   434e0:	617b      	str	r3, [r7, #20]
   434e2:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   434e4:	697b      	ldr	r3, [r7, #20]
   434e6:	4053      	eors	r3, r2
   434e8:	2110      	movs	r1, #16
   434ea:	4618      	mov	r0, r3
   434ec:	f7fd fb54 	bl	40b98 <rotr32>
   434f0:	4603      	mov	r3, r0
   434f2:	643b      	str	r3, [r7, #64]	; 0x40
   434f4:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   434f6:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   434f8:	4413      	add	r3, r2
   434fa:	62fb      	str	r3, [r7, #44]	; 0x2c
   434fc:	6aba      	ldr	r2, [r7, #40]	; 0x28
   434fe:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   43500:	4053      	eors	r3, r2
   43502:	210c      	movs	r1, #12
   43504:	4618      	mov	r0, r3
   43506:	f7fd fb47 	bl	40b98 <rotr32>
   4350a:	4603      	mov	r3, r0
   4350c:	62bb      	str	r3, [r7, #40]	; 0x28
   4350e:	697a      	ldr	r2, [r7, #20]
   43510:	6abb      	ldr	r3, [r7, #40]	; 0x28
   43512:	441a      	add	r2, r3
   43514:	2304      	movs	r3, #4
   43516:	009b      	lsls	r3, r3, #2
   43518:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4351c:	440b      	add	r3, r1
   4351e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   43522:	4413      	add	r3, r2
   43524:	617b      	str	r3, [r7, #20]
   43526:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   43528:	697b      	ldr	r3, [r7, #20]
   4352a:	4053      	eors	r3, r2
   4352c:	2108      	movs	r1, #8
   4352e:	4618      	mov	r0, r3
   43530:	f7fd fb32 	bl	40b98 <rotr32>
   43534:	4603      	mov	r3, r0
   43536:	643b      	str	r3, [r7, #64]	; 0x40
   43538:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   4353a:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   4353c:	4413      	add	r3, r2
   4353e:	62fb      	str	r3, [r7, #44]	; 0x2c
   43540:	6aba      	ldr	r2, [r7, #40]	; 0x28
   43542:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   43544:	4053      	eors	r3, r2
   43546:	2107      	movs	r1, #7
   43548:	4618      	mov	r0, r3
   4354a:	f7fd fb25 	bl	40b98 <rotr32>
   4354e:	4603      	mov	r3, r0
   43550:	62bb      	str	r3, [r7, #40]	; 0x28
   43552:	69ba      	ldr	r2, [r7, #24]
   43554:	69fb      	ldr	r3, [r7, #28]
   43556:	441a      	add	r2, r3
   43558:	230a      	movs	r3, #10
   4355a:	009b      	lsls	r3, r3, #2
   4355c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   43560:	440b      	add	r3, r1
   43562:	f853 3c44 	ldr.w	r3, [r3, #-68]
   43566:	4413      	add	r3, r2
   43568:	61bb      	str	r3, [r7, #24]
   4356a:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   4356c:	69bb      	ldr	r3, [r7, #24]
   4356e:	4053      	eors	r3, r2
   43570:	2110      	movs	r1, #16
   43572:	4618      	mov	r0, r3
   43574:	f7fd fb10 	bl	40b98 <rotr32>
   43578:	4603      	mov	r3, r0
   4357a:	647b      	str	r3, [r7, #68]	; 0x44
   4357c:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   4357e:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   43580:	4413      	add	r3, r2
   43582:	633b      	str	r3, [r7, #48]	; 0x30
   43584:	69fa      	ldr	r2, [r7, #28]
   43586:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   43588:	4053      	eors	r3, r2
   4358a:	210c      	movs	r1, #12
   4358c:	4618      	mov	r0, r3
   4358e:	f7fd fb03 	bl	40b98 <rotr32>
   43592:	4603      	mov	r3, r0
   43594:	61fb      	str	r3, [r7, #28]
   43596:	69ba      	ldr	r2, [r7, #24]
   43598:	69fb      	ldr	r3, [r7, #28]
   4359a:	441a      	add	r2, r3
   4359c:	2305      	movs	r3, #5
   4359e:	009b      	lsls	r3, r3, #2
   435a0:	f107 0190 	add.w	r1, r7, #144	; 0x90
   435a4:	440b      	add	r3, r1
   435a6:	f853 3c44 	ldr.w	r3, [r3, #-68]
   435aa:	4413      	add	r3, r2
   435ac:	61bb      	str	r3, [r7, #24]
   435ae:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   435b0:	69bb      	ldr	r3, [r7, #24]
   435b2:	4053      	eors	r3, r2
   435b4:	2108      	movs	r1, #8
   435b6:	4618      	mov	r0, r3
   435b8:	f7fd faee 	bl	40b98 <rotr32>
   435bc:	4603      	mov	r3, r0
   435be:	647b      	str	r3, [r7, #68]	; 0x44
   435c0:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   435c2:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   435c4:	4413      	add	r3, r2
   435c6:	633b      	str	r3, [r7, #48]	; 0x30
   435c8:	69fa      	ldr	r2, [r7, #28]
   435ca:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   435cc:	4053      	eors	r3, r2
   435ce:	2107      	movs	r1, #7
   435d0:	4618      	mov	r0, r3
   435d2:	f7fd fae1 	bl	40b98 <rotr32>
   435d6:	4603      	mov	r3, r0
   435d8:	61fb      	str	r3, [r7, #28]
   435da:	68fa      	ldr	r2, [r7, #12]
   435dc:	69fb      	ldr	r3, [r7, #28]
   435de:	441a      	add	r2, r3
   435e0:	230a      	movs	r3, #10
   435e2:	009b      	lsls	r3, r3, #2
   435e4:	f107 0190 	add.w	r1, r7, #144	; 0x90
   435e8:	440b      	add	r3, r1
   435ea:	f853 3c44 	ldr.w	r3, [r3, #-68]
   435ee:	4413      	add	r3, r2
   435f0:	60fb      	str	r3, [r7, #12]
   435f2:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   435f4:	68fb      	ldr	r3, [r7, #12]
   435f6:	4053      	eors	r3, r2
   435f8:	2110      	movs	r1, #16
   435fa:	4618      	mov	r0, r3
   435fc:	f7fd facc 	bl	40b98 <rotr32>
   43600:	4603      	mov	r3, r0
   43602:	63fb      	str	r3, [r7, #60]	; 0x3c
   43604:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   43606:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   43608:	4413      	add	r3, r2
   4360a:	62fb      	str	r3, [r7, #44]	; 0x2c
   4360c:	69fa      	ldr	r2, [r7, #28]
   4360e:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   43610:	4053      	eors	r3, r2
   43612:	210c      	movs	r1, #12
   43614:	4618      	mov	r0, r3
   43616:	f7fd fabf 	bl	40b98 <rotr32>
   4361a:	4603      	mov	r3, r0
   4361c:	61fb      	str	r3, [r7, #28]
   4361e:	68fa      	ldr	r2, [r7, #12]
   43620:	69fb      	ldr	r3, [r7, #28]
   43622:	441a      	add	r2, r3
   43624:	2302      	movs	r3, #2
   43626:	009b      	lsls	r3, r3, #2
   43628:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4362c:	440b      	add	r3, r1
   4362e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   43632:	4413      	add	r3, r2
   43634:	60fb      	str	r3, [r7, #12]
   43636:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   43638:	68fb      	ldr	r3, [r7, #12]
   4363a:	4053      	eors	r3, r2
   4363c:	2108      	movs	r1, #8
   4363e:	4618      	mov	r0, r3
   43640:	f7fd faaa 	bl	40b98 <rotr32>
   43644:	4603      	mov	r3, r0
   43646:	63fb      	str	r3, [r7, #60]	; 0x3c
   43648:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   4364a:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   4364c:	4413      	add	r3, r2
   4364e:	62fb      	str	r3, [r7, #44]	; 0x2c
   43650:	69fa      	ldr	r2, [r7, #28]
   43652:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   43654:	4053      	eors	r3, r2
   43656:	2107      	movs	r1, #7
   43658:	4618      	mov	r0, r3
   4365a:	f7fd fa9d 	bl	40b98 <rotr32>
   4365e:	4603      	mov	r3, r0
   43660:	61fb      	str	r3, [r7, #28]
   43662:	693a      	ldr	r2, [r7, #16]
   43664:	6a3b      	ldr	r3, [r7, #32]
   43666:	441a      	add	r2, r3
   43668:	2308      	movs	r3, #8
   4366a:	009b      	lsls	r3, r3, #2
   4366c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   43670:	440b      	add	r3, r1
   43672:	f853 3c44 	ldr.w	r3, [r3, #-68]
   43676:	4413      	add	r3, r2
   43678:	613b      	str	r3, [r7, #16]
   4367a:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   4367c:	693b      	ldr	r3, [r7, #16]
   4367e:	4053      	eors	r3, r2
   43680:	2110      	movs	r1, #16
   43682:	4618      	mov	r0, r3
   43684:	f7fd fa88 	bl	40b98 <rotr32>
   43688:	4603      	mov	r3, r0
   4368a:	643b      	str	r3, [r7, #64]	; 0x40
   4368c:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   4368e:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   43690:	4413      	add	r3, r2
   43692:	633b      	str	r3, [r7, #48]	; 0x30
   43694:	6a3a      	ldr	r2, [r7, #32]
   43696:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   43698:	4053      	eors	r3, r2
   4369a:	210c      	movs	r1, #12
   4369c:	4618      	mov	r0, r3
   4369e:	f7fd fa7b 	bl	40b98 <rotr32>
   436a2:	4603      	mov	r3, r0
   436a4:	623b      	str	r3, [r7, #32]
   436a6:	693a      	ldr	r2, [r7, #16]
   436a8:	6a3b      	ldr	r3, [r7, #32]
   436aa:	441a      	add	r2, r3
   436ac:	2304      	movs	r3, #4
   436ae:	009b      	lsls	r3, r3, #2
   436b0:	f107 0190 	add.w	r1, r7, #144	; 0x90
   436b4:	440b      	add	r3, r1
   436b6:	f853 3c44 	ldr.w	r3, [r3, #-68]
   436ba:	4413      	add	r3, r2
   436bc:	613b      	str	r3, [r7, #16]
   436be:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   436c0:	693b      	ldr	r3, [r7, #16]
   436c2:	4053      	eors	r3, r2
   436c4:	2108      	movs	r1, #8
   436c6:	4618      	mov	r0, r3
   436c8:	f7fd fa66 	bl	40b98 <rotr32>
   436cc:	4603      	mov	r3, r0
   436ce:	643b      	str	r3, [r7, #64]	; 0x40
   436d0:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   436d2:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   436d4:	4413      	add	r3, r2
   436d6:	633b      	str	r3, [r7, #48]	; 0x30
   436d8:	6a3a      	ldr	r2, [r7, #32]
   436da:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   436dc:	4053      	eors	r3, r2
   436de:	2107      	movs	r1, #7
   436e0:	4618      	mov	r0, r3
   436e2:	f7fd fa59 	bl	40b98 <rotr32>
   436e6:	4603      	mov	r3, r0
   436e8:	623b      	str	r3, [r7, #32]
   436ea:	697a      	ldr	r2, [r7, #20]
   436ec:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   436ee:	441a      	add	r2, r3
   436f0:	2307      	movs	r3, #7
   436f2:	009b      	lsls	r3, r3, #2
   436f4:	f107 0190 	add.w	r1, r7, #144	; 0x90
   436f8:	440b      	add	r3, r1
   436fa:	f853 3c44 	ldr.w	r3, [r3, #-68]
   436fe:	4413      	add	r3, r2
   43700:	617b      	str	r3, [r7, #20]
   43702:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   43704:	697b      	ldr	r3, [r7, #20]
   43706:	4053      	eors	r3, r2
   43708:	2110      	movs	r1, #16
   4370a:	4618      	mov	r0, r3
   4370c:	f7fd fa44 	bl	40b98 <rotr32>
   43710:	4603      	mov	r3, r0
   43712:	647b      	str	r3, [r7, #68]	; 0x44
   43714:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   43716:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   43718:	4413      	add	r3, r2
   4371a:	637b      	str	r3, [r7, #52]	; 0x34
   4371c:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   4371e:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   43720:	4053      	eors	r3, r2
   43722:	210c      	movs	r1, #12
   43724:	4618      	mov	r0, r3
   43726:	f7fd fa37 	bl	40b98 <rotr32>
   4372a:	4603      	mov	r3, r0
   4372c:	627b      	str	r3, [r7, #36]	; 0x24
   4372e:	697a      	ldr	r2, [r7, #20]
   43730:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   43732:	441a      	add	r2, r3
   43734:	2306      	movs	r3, #6
   43736:	009b      	lsls	r3, r3, #2
   43738:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4373c:	440b      	add	r3, r1
   4373e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   43742:	4413      	add	r3, r2
   43744:	617b      	str	r3, [r7, #20]
   43746:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   43748:	697b      	ldr	r3, [r7, #20]
   4374a:	4053      	eors	r3, r2
   4374c:	2108      	movs	r1, #8
   4374e:	4618      	mov	r0, r3
   43750:	f7fd fa22 	bl	40b98 <rotr32>
   43754:	4603      	mov	r3, r0
   43756:	647b      	str	r3, [r7, #68]	; 0x44
   43758:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   4375a:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   4375c:	4413      	add	r3, r2
   4375e:	637b      	str	r3, [r7, #52]	; 0x34
   43760:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   43762:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   43764:	4053      	eors	r3, r2
   43766:	2107      	movs	r1, #7
   43768:	4618      	mov	r0, r3
   4376a:	f7fd fa15 	bl	40b98 <rotr32>
   4376e:	4603      	mov	r3, r0
   43770:	627b      	str	r3, [r7, #36]	; 0x24
   43772:	69ba      	ldr	r2, [r7, #24]
   43774:	6abb      	ldr	r3, [r7, #40]	; 0x28
   43776:	441a      	add	r2, r3
   43778:	2301      	movs	r3, #1
   4377a:	009b      	lsls	r3, r3, #2
   4377c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   43780:	440b      	add	r3, r1
   43782:	f853 3c44 	ldr.w	r3, [r3, #-68]
   43786:	4413      	add	r3, r2
   43788:	61bb      	str	r3, [r7, #24]
   4378a:	6cba      	ldr	r2, [r7, #72]	; 0x48
   4378c:	69bb      	ldr	r3, [r7, #24]
   4378e:	4053      	eors	r3, r2
   43790:	2110      	movs	r1, #16
   43792:	4618      	mov	r0, r3
   43794:	f7fd fa00 	bl	40b98 <rotr32>
   43798:	4603      	mov	r3, r0
   4379a:	64bb      	str	r3, [r7, #72]	; 0x48
   4379c:	6bba      	ldr	r2, [r7, #56]	; 0x38
   4379e:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   437a0:	4413      	add	r3, r2
   437a2:	63bb      	str	r3, [r7, #56]	; 0x38
   437a4:	6aba      	ldr	r2, [r7, #40]	; 0x28
   437a6:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   437a8:	4053      	eors	r3, r2
   437aa:	210c      	movs	r1, #12
   437ac:	4618      	mov	r0, r3
   437ae:	f7fd f9f3 	bl	40b98 <rotr32>
   437b2:	4603      	mov	r3, r0
   437b4:	62bb      	str	r3, [r7, #40]	; 0x28
   437b6:	69ba      	ldr	r2, [r7, #24]
   437b8:	6abb      	ldr	r3, [r7, #40]	; 0x28
   437ba:	441a      	add	r2, r3
   437bc:	2305      	movs	r3, #5
   437be:	009b      	lsls	r3, r3, #2
   437c0:	f107 0190 	add.w	r1, r7, #144	; 0x90
   437c4:	440b      	add	r3, r1
   437c6:	f853 3c44 	ldr.w	r3, [r3, #-68]
   437ca:	4413      	add	r3, r2
   437cc:	61bb      	str	r3, [r7, #24]
   437ce:	6cba      	ldr	r2, [r7, #72]	; 0x48
   437d0:	69bb      	ldr	r3, [r7, #24]
   437d2:	4053      	eors	r3, r2
   437d4:	2108      	movs	r1, #8
   437d6:	4618      	mov	r0, r3
   437d8:	f7fd f9de 	bl	40b98 <rotr32>
   437dc:	4603      	mov	r3, r0
   437de:	64bb      	str	r3, [r7, #72]	; 0x48
   437e0:	6bba      	ldr	r2, [r7, #56]	; 0x38
   437e2:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   437e4:	4413      	add	r3, r2
   437e6:	63bb      	str	r3, [r7, #56]	; 0x38
   437e8:	6aba      	ldr	r2, [r7, #40]	; 0x28
   437ea:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   437ec:	4053      	eors	r3, r2
   437ee:	2107      	movs	r1, #7
   437f0:	4618      	mov	r0, r3
   437f2:	f7fd f9d1 	bl	40b98 <rotr32>
   437f6:	4603      	mov	r3, r0
   437f8:	62bb      	str	r3, [r7, #40]	; 0x28
   437fa:	68fa      	ldr	r2, [r7, #12]
   437fc:	6a3b      	ldr	r3, [r7, #32]
   437fe:	441a      	add	r2, r3
   43800:	230f      	movs	r3, #15
   43802:	009b      	lsls	r3, r3, #2
   43804:	f107 0190 	add.w	r1, r7, #144	; 0x90
   43808:	440b      	add	r3, r1
   4380a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4380e:	4413      	add	r3, r2
   43810:	60fb      	str	r3, [r7, #12]
   43812:	6cba      	ldr	r2, [r7, #72]	; 0x48
   43814:	68fb      	ldr	r3, [r7, #12]
   43816:	4053      	eors	r3, r2
   43818:	2110      	movs	r1, #16
   4381a:	4618      	mov	r0, r3
   4381c:	f7fd f9bc 	bl	40b98 <rotr32>
   43820:	4603      	mov	r3, r0
   43822:	64bb      	str	r3, [r7, #72]	; 0x48
   43824:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   43826:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   43828:	4413      	add	r3, r2
   4382a:	637b      	str	r3, [r7, #52]	; 0x34
   4382c:	6a3a      	ldr	r2, [r7, #32]
   4382e:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   43830:	4053      	eors	r3, r2
   43832:	210c      	movs	r1, #12
   43834:	4618      	mov	r0, r3
   43836:	f7fd f9af 	bl	40b98 <rotr32>
   4383a:	4603      	mov	r3, r0
   4383c:	623b      	str	r3, [r7, #32]
   4383e:	68fa      	ldr	r2, [r7, #12]
   43840:	6a3b      	ldr	r3, [r7, #32]
   43842:	441a      	add	r2, r3
   43844:	230b      	movs	r3, #11
   43846:	009b      	lsls	r3, r3, #2
   43848:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4384c:	440b      	add	r3, r1
   4384e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   43852:	4413      	add	r3, r2
   43854:	60fb      	str	r3, [r7, #12]
   43856:	6cba      	ldr	r2, [r7, #72]	; 0x48
   43858:	68fb      	ldr	r3, [r7, #12]
   4385a:	4053      	eors	r3, r2
   4385c:	2108      	movs	r1, #8
   4385e:	4618      	mov	r0, r3
   43860:	f7fd f99a 	bl	40b98 <rotr32>
   43864:	4603      	mov	r3, r0
   43866:	64bb      	str	r3, [r7, #72]	; 0x48
   43868:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   4386a:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   4386c:	4413      	add	r3, r2
   4386e:	637b      	str	r3, [r7, #52]	; 0x34
   43870:	6a3a      	ldr	r2, [r7, #32]
   43872:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   43874:	4053      	eors	r3, r2
   43876:	2107      	movs	r1, #7
   43878:	4618      	mov	r0, r3
   4387a:	f7fd f98d 	bl	40b98 <rotr32>
   4387e:	4603      	mov	r3, r0
   43880:	623b      	str	r3, [r7, #32]
   43882:	693a      	ldr	r2, [r7, #16]
   43884:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   43886:	441a      	add	r2, r3
   43888:	2309      	movs	r3, #9
   4388a:	009b      	lsls	r3, r3, #2
   4388c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   43890:	440b      	add	r3, r1
   43892:	f853 3c44 	ldr.w	r3, [r3, #-68]
   43896:	4413      	add	r3, r2
   43898:	613b      	str	r3, [r7, #16]
   4389a:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   4389c:	693b      	ldr	r3, [r7, #16]
   4389e:	4053      	eors	r3, r2
   438a0:	2110      	movs	r1, #16
   438a2:	4618      	mov	r0, r3
   438a4:	f7fd f978 	bl	40b98 <rotr32>
   438a8:	4603      	mov	r3, r0
   438aa:	63fb      	str	r3, [r7, #60]	; 0x3c
   438ac:	6bba      	ldr	r2, [r7, #56]	; 0x38
   438ae:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   438b0:	4413      	add	r3, r2
   438b2:	63bb      	str	r3, [r7, #56]	; 0x38
   438b4:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   438b6:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   438b8:	4053      	eors	r3, r2
   438ba:	210c      	movs	r1, #12
   438bc:	4618      	mov	r0, r3
   438be:	f7fd f96b 	bl	40b98 <rotr32>
   438c2:	4603      	mov	r3, r0
   438c4:	627b      	str	r3, [r7, #36]	; 0x24
   438c6:	693a      	ldr	r2, [r7, #16]
   438c8:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   438ca:	441a      	add	r2, r3
   438cc:	230e      	movs	r3, #14
   438ce:	009b      	lsls	r3, r3, #2
   438d0:	f107 0190 	add.w	r1, r7, #144	; 0x90
   438d4:	440b      	add	r3, r1
   438d6:	f853 3c44 	ldr.w	r3, [r3, #-68]
   438da:	4413      	add	r3, r2
   438dc:	613b      	str	r3, [r7, #16]
   438de:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   438e0:	693b      	ldr	r3, [r7, #16]
   438e2:	4053      	eors	r3, r2
   438e4:	2108      	movs	r1, #8
   438e6:	4618      	mov	r0, r3
   438e8:	f7fd f956 	bl	40b98 <rotr32>
   438ec:	4603      	mov	r3, r0
   438ee:	63fb      	str	r3, [r7, #60]	; 0x3c
   438f0:	6bba      	ldr	r2, [r7, #56]	; 0x38
   438f2:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   438f4:	4413      	add	r3, r2
   438f6:	63bb      	str	r3, [r7, #56]	; 0x38
   438f8:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   438fa:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   438fc:	4053      	eors	r3, r2
   438fe:	2107      	movs	r1, #7
   43900:	4618      	mov	r0, r3
   43902:	f7fd f949 	bl	40b98 <rotr32>
   43906:	4603      	mov	r3, r0
   43908:	627b      	str	r3, [r7, #36]	; 0x24
   4390a:	697a      	ldr	r2, [r7, #20]
   4390c:	6abb      	ldr	r3, [r7, #40]	; 0x28
   4390e:	441a      	add	r2, r3
   43910:	2303      	movs	r3, #3
   43912:	009b      	lsls	r3, r3, #2
   43914:	f107 0190 	add.w	r1, r7, #144	; 0x90
   43918:	440b      	add	r3, r1
   4391a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4391e:	4413      	add	r3, r2
   43920:	617b      	str	r3, [r7, #20]
   43922:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   43924:	697b      	ldr	r3, [r7, #20]
   43926:	4053      	eors	r3, r2
   43928:	2110      	movs	r1, #16
   4392a:	4618      	mov	r0, r3
   4392c:	f7fd f934 	bl	40b98 <rotr32>
   43930:	4603      	mov	r3, r0
   43932:	643b      	str	r3, [r7, #64]	; 0x40
   43934:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   43936:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   43938:	4413      	add	r3, r2
   4393a:	62fb      	str	r3, [r7, #44]	; 0x2c
   4393c:	6aba      	ldr	r2, [r7, #40]	; 0x28
   4393e:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   43940:	4053      	eors	r3, r2
   43942:	210c      	movs	r1, #12
   43944:	4618      	mov	r0, r3
   43946:	f7fd f927 	bl	40b98 <rotr32>
   4394a:	4603      	mov	r3, r0
   4394c:	62bb      	str	r3, [r7, #40]	; 0x28
   4394e:	697a      	ldr	r2, [r7, #20]
   43950:	6abb      	ldr	r3, [r7, #40]	; 0x28
   43952:	441a      	add	r2, r3
   43954:	230c      	movs	r3, #12
   43956:	009b      	lsls	r3, r3, #2
   43958:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4395c:	440b      	add	r3, r1
   4395e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   43962:	4413      	add	r3, r2
   43964:	617b      	str	r3, [r7, #20]
   43966:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   43968:	697b      	ldr	r3, [r7, #20]
   4396a:	4053      	eors	r3, r2
   4396c:	2108      	movs	r1, #8
   4396e:	4618      	mov	r0, r3
   43970:	f7fd f912 	bl	40b98 <rotr32>
   43974:	4603      	mov	r3, r0
   43976:	643b      	str	r3, [r7, #64]	; 0x40
   43978:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   4397a:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   4397c:	4413      	add	r3, r2
   4397e:	62fb      	str	r3, [r7, #44]	; 0x2c
   43980:	6aba      	ldr	r2, [r7, #40]	; 0x28
   43982:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   43984:	4053      	eors	r3, r2
   43986:	2107      	movs	r1, #7
   43988:	4618      	mov	r0, r3
   4398a:	f7fd f905 	bl	40b98 <rotr32>
   4398e:	4603      	mov	r3, r0
   43990:	62bb      	str	r3, [r7, #40]	; 0x28
   43992:	69ba      	ldr	r2, [r7, #24]
   43994:	69fb      	ldr	r3, [r7, #28]
   43996:	441a      	add	r2, r3
   43998:	230d      	movs	r3, #13
   4399a:	009b      	lsls	r3, r3, #2
   4399c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   439a0:	440b      	add	r3, r1
   439a2:	f853 3c44 	ldr.w	r3, [r3, #-68]
   439a6:	4413      	add	r3, r2
   439a8:	61bb      	str	r3, [r7, #24]
   439aa:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   439ac:	69bb      	ldr	r3, [r7, #24]
   439ae:	4053      	eors	r3, r2
   439b0:	2110      	movs	r1, #16
   439b2:	4618      	mov	r0, r3
   439b4:	f7fd f8f0 	bl	40b98 <rotr32>
   439b8:	4603      	mov	r3, r0
   439ba:	647b      	str	r3, [r7, #68]	; 0x44
   439bc:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   439be:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   439c0:	4413      	add	r3, r2
   439c2:	633b      	str	r3, [r7, #48]	; 0x30
   439c4:	69fa      	ldr	r2, [r7, #28]
   439c6:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   439c8:	4053      	eors	r3, r2
   439ca:	210c      	movs	r1, #12
   439cc:	4618      	mov	r0, r3
   439ce:	f7fd f8e3 	bl	40b98 <rotr32>
   439d2:	4603      	mov	r3, r0
   439d4:	61fb      	str	r3, [r7, #28]
   439d6:	69ba      	ldr	r2, [r7, #24]
   439d8:	69fb      	ldr	r3, [r7, #28]
   439da:	441a      	add	r2, r3
   439dc:	2300      	movs	r3, #0
   439de:	009b      	lsls	r3, r3, #2
   439e0:	f107 0190 	add.w	r1, r7, #144	; 0x90
   439e4:	440b      	add	r3, r1
   439e6:	f853 3c44 	ldr.w	r3, [r3, #-68]
   439ea:	4413      	add	r3, r2
   439ec:	61bb      	str	r3, [r7, #24]
   439ee:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   439f0:	69bb      	ldr	r3, [r7, #24]
   439f2:	4053      	eors	r3, r2
   439f4:	2108      	movs	r1, #8
   439f6:	4618      	mov	r0, r3
   439f8:	f7fd f8ce 	bl	40b98 <rotr32>
   439fc:	4603      	mov	r3, r0
   439fe:	647b      	str	r3, [r7, #68]	; 0x44
   43a00:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   43a02:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   43a04:	4413      	add	r3, r2
   43a06:	633b      	str	r3, [r7, #48]	; 0x30
   43a08:	69fa      	ldr	r2, [r7, #28]
   43a0a:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   43a0c:	4053      	eors	r3, r2
   43a0e:	2107      	movs	r1, #7
   43a10:	4618      	mov	r0, r3
   43a12:	f7fd f8c1 	bl	40b98 <rotr32>
   43a16:	4603      	mov	r3, r0
   43a18:	61fb      	str	r3, [r7, #28]
   43a1a:	2300      	movs	r3, #0
   43a1c:	f8c7 308c 	str.w	r3, [r7, #140]	; 0x8c
   43a20:	e022      	b.n	43a68 <blake2s_compress+0x2bb0>
   43a22:	687b      	ldr	r3, [r7, #4]
   43a24:	f8d7 208c 	ldr.w	r2, [r7, #140]	; 0x8c
   43a28:	f853 2022 	ldr.w	r2, [r3, r2, lsl #2]
   43a2c:	f8d7 308c 	ldr.w	r3, [r7, #140]	; 0x8c
   43a30:	009b      	lsls	r3, r3, #2
   43a32:	f107 0190 	add.w	r1, r7, #144	; 0x90
   43a36:	440b      	add	r3, r1
   43a38:	f853 3c84 	ldr.w	r3, [r3, #-132]
   43a3c:	405a      	eors	r2, r3
   43a3e:	f8d7 308c 	ldr.w	r3, [r7, #140]	; 0x8c
   43a42:	3308      	adds	r3, #8
   43a44:	009b      	lsls	r3, r3, #2
   43a46:	f107 0190 	add.w	r1, r7, #144	; 0x90
   43a4a:	440b      	add	r3, r1
   43a4c:	f853 3c84 	ldr.w	r3, [r3, #-132]
   43a50:	ea82 0103 	eor.w	r1, r2, r3
   43a54:	687b      	ldr	r3, [r7, #4]
   43a56:	f8d7 208c 	ldr.w	r2, [r7, #140]	; 0x8c
   43a5a:	f843 1022 	str.w	r1, [r3, r2, lsl #2]
   43a5e:	f8d7 308c 	ldr.w	r3, [r7, #140]	; 0x8c
   43a62:	3301      	adds	r3, #1
   43a64:	f8c7 308c 	str.w	r3, [r7, #140]	; 0x8c
   43a68:	f8d7 308c 	ldr.w	r3, [r7, #140]	; 0x8c
   43a6c:	2b07      	cmp	r3, #7
   43a6e:	d9d8      	bls.n	43a22 <blake2s_compress+0x2b6a>
   43a70:	bf00      	nop
   43a72:	3790      	adds	r7, #144	; 0x90
   43a74:	46bd      	mov	sp, r7
   43a76:	bd80      	pop	{r7, pc}

00043a78 <blake2s_update>:
   43a78:	b580      	push	{r7, lr}
   43a7a:	b088      	sub	sp, #32
   43a7c:	af00      	add	r7, sp, #0
   43a7e:	60f8      	str	r0, [r7, #12]
   43a80:	60b9      	str	r1, [r7, #8]
   43a82:	607a      	str	r2, [r7, #4]
   43a84:	68bb      	ldr	r3, [r7, #8]
   43a86:	61fb      	str	r3, [r7, #28]
   43a88:	687b      	ldr	r3, [r7, #4]
   43a8a:	2b00      	cmp	r3, #0
   43a8c:	d04c      	beq.n	43b28 <blake2s_update+0xb0>
   43a8e:	68fb      	ldr	r3, [r7, #12]
   43a90:	6f1b      	ldr	r3, [r3, #112]	; 0x70
   43a92:	61bb      	str	r3, [r7, #24]
   43a94:	69bb      	ldr	r3, [r7, #24]
   43a96:	f1c3 0340 	rsb	r3, r3, #64	; 0x40
   43a9a:	617b      	str	r3, [r7, #20]
   43a9c:	687a      	ldr	r2, [r7, #4]
   43a9e:	697b      	ldr	r3, [r7, #20]
   43aa0:	429a      	cmp	r2, r3
   43aa2:	d930      	bls.n	43b06 <blake2s_update+0x8e>
   43aa4:	68fb      	ldr	r3, [r7, #12]
   43aa6:	2200      	movs	r2, #0
   43aa8:	671a      	str	r2, [r3, #112]	; 0x70
   43aaa:	68fb      	ldr	r3, [r7, #12]
   43aac:	f103 0230 	add.w	r2, r3, #48	; 0x30
   43ab0:	69bb      	ldr	r3, [r7, #24]
   43ab2:	4413      	add	r3, r2
   43ab4:	697a      	ldr	r2, [r7, #20]
   43ab6:	69f9      	ldr	r1, [r7, #28]
   43ab8:	4618      	mov	r0, r3
   43aba:	f7cd e86c 	blx	10b94 <memcpy@plt>
   43abe:	2140      	movs	r1, #64	; 0x40
   43ac0:	68f8      	ldr	r0, [r7, #12]
   43ac2:	f7fd f8be 	bl	40c42 <blake2s_increment_counter>
   43ac6:	68fb      	ldr	r3, [r7, #12]
   43ac8:	3330      	adds	r3, #48	; 0x30
   43aca:	4619      	mov	r1, r3
   43acc:	68f8      	ldr	r0, [r7, #12]
   43ace:	f7fd f9f3 	bl	40eb8 <blake2s_compress>
   43ad2:	69fa      	ldr	r2, [r7, #28]
   43ad4:	697b      	ldr	r3, [r7, #20]
   43ad6:	4413      	add	r3, r2
   43ad8:	61fb      	str	r3, [r7, #28]
   43ada:	687a      	ldr	r2, [r7, #4]
   43adc:	697b      	ldr	r3, [r7, #20]
   43ade:	1ad3      	subs	r3, r2, r3
   43ae0:	607b      	str	r3, [r7, #4]
   43ae2:	e00d      	b.n	43b00 <blake2s_update+0x88>
   43ae4:	2140      	movs	r1, #64	; 0x40
   43ae6:	68f8      	ldr	r0, [r7, #12]
   43ae8:	f7fd f8ab 	bl	40c42 <blake2s_increment_counter>
   43aec:	69f9      	ldr	r1, [r7, #28]
   43aee:	68f8      	ldr	r0, [r7, #12]
   43af0:	f7fd f9e2 	bl	40eb8 <blake2s_compress>
   43af4:	69fb      	ldr	r3, [r7, #28]
   43af6:	3340      	adds	r3, #64	; 0x40
   43af8:	61fb      	str	r3, [r7, #28]
   43afa:	687b      	ldr	r3, [r7, #4]
   43afc:	3b40      	subs	r3, #64	; 0x40
   43afe:	607b      	str	r3, [r7, #4]
   43b00:	687b      	ldr	r3, [r7, #4]
   43b02:	2b40      	cmp	r3, #64	; 0x40
   43b04:	d8ee      	bhi.n	43ae4 <blake2s_update+0x6c>
   43b06:	68fb      	ldr	r3, [r7, #12]
   43b08:	f103 0230 	add.w	r2, r3, #48	; 0x30
   43b0c:	68fb      	ldr	r3, [r7, #12]
   43b0e:	6f1b      	ldr	r3, [r3, #112]	; 0x70
   43b10:	4413      	add	r3, r2
   43b12:	687a      	ldr	r2, [r7, #4]
   43b14:	69f9      	ldr	r1, [r7, #28]
   43b16:	4618      	mov	r0, r3
   43b18:	f7cd e83c 	blx	10b94 <memcpy@plt>
   43b1c:	68fb      	ldr	r3, [r7, #12]
   43b1e:	6f1a      	ldr	r2, [r3, #112]	; 0x70
   43b20:	687b      	ldr	r3, [r7, #4]
   43b22:	441a      	add	r2, r3
   43b24:	68fb      	ldr	r3, [r7, #12]
   43b26:	671a      	str	r2, [r3, #112]	; 0x70
   43b28:	2300      	movs	r3, #0
   43b2a:	4618      	mov	r0, r3
   43b2c:	3720      	adds	r7, #32
   43b2e:	46bd      	mov	sp, r7
   43b30:	bd80      	pop	{r7, pc}

00043b32 <blake2s_final>:
   43b32:	b580      	push	{r7, lr}
   43b34:	b08e      	sub	sp, #56	; 0x38
   43b36:	af00      	add	r7, sp, #0
   43b38:	60f8      	str	r0, [r7, #12]
   43b3a:	60b9      	str	r1, [r7, #8]
   43b3c:	607a      	str	r2, [r7, #4]
   43b3e:	f107 0314 	add.w	r3, r7, #20
   43b42:	2220      	movs	r2, #32
   43b44:	2100      	movs	r1, #0
   43b46:	4618      	mov	r0, r3
   43b48:	f7cd e88a 	blx	10c60 <memset@plt>
   43b4c:	68bb      	ldr	r3, [r7, #8]
   43b4e:	2b00      	cmp	r3, #0
   43b50:	d004      	beq.n	43b5c <blake2s_final+0x2a>
   43b52:	68fb      	ldr	r3, [r7, #12]
   43b54:	6f5a      	ldr	r2, [r3, #116]	; 0x74
   43b56:	687b      	ldr	r3, [r7, #4]
   43b58:	429a      	cmp	r2, r3
   43b5a:	d902      	bls.n	43b62 <blake2s_final+0x30>
   43b5c:	f04f 33ff 	mov.w	r3, #4294967295	; 0xffffffff
   43b60:	e048      	b.n	43bf4 <blake2s_final+0xc2>
   43b62:	68f8      	ldr	r0, [r7, #12]
   43b64:	f7fd f848 	bl	40bf8 <blake2s_is_lastblock>
   43b68:	4603      	mov	r3, r0
   43b6a:	2b00      	cmp	r3, #0
   43b6c:	d002      	beq.n	43b74 <blake2s_final+0x42>
   43b6e:	f04f 33ff 	mov.w	r3, #4294967295	; 0xffffffff
   43b72:	e03f      	b.n	43bf4 <blake2s_final+0xc2>
   43b74:	68fb      	ldr	r3, [r7, #12]
   43b76:	6f1b      	ldr	r3, [r3, #112]	; 0x70
   43b78:	4619      	mov	r1, r3
   43b7a:	68f8      	ldr	r0, [r7, #12]
   43b7c:	f7fd f861 	bl	40c42 <blake2s_increment_counter>
   43b80:	68f8      	ldr	r0, [r7, #12]
   43b82:	f7fd f84a 	bl	40c1a <blake2s_set_lastblock>
   43b86:	68fb      	ldr	r3, [r7, #12]
   43b88:	f103 0230 	add.w	r2, r3, #48	; 0x30
   43b8c:	68fb      	ldr	r3, [r7, #12]
   43b8e:	6f1b      	ldr	r3, [r3, #112]	; 0x70
   43b90:	18d0      	adds	r0, r2, r3
   43b92:	68fb      	ldr	r3, [r7, #12]
   43b94:	6f1b      	ldr	r3, [r3, #112]	; 0x70
   43b96:	f1c3 0340 	rsb	r3, r3, #64	; 0x40
   43b9a:	461a      	mov	r2, r3
   43b9c:	2100      	movs	r1, #0
   43b9e:	f7cd e860 	blx	10c60 <memset@plt>
   43ba2:	68fb      	ldr	r3, [r7, #12]
   43ba4:	3330      	adds	r3, #48	; 0x30
   43ba6:	4619      	mov	r1, r3
   43ba8:	68f8      	ldr	r0, [r7, #12]
   43baa:	f7fd f985 	bl	40eb8 <blake2s_compress>
   43bae:	2300      	movs	r3, #0
   43bb0:	637b      	str	r3, [r7, #52]	; 0x34
   43bb2:	e00e      	b.n	43bd2 <blake2s_final+0xa0>
   43bb4:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   43bb6:	009b      	lsls	r3, r3, #2
   43bb8:	f107 0214 	add.w	r2, r7, #20
   43bbc:	18d0      	adds	r0, r2, r3
   43bbe:	68fb      	ldr	r3, [r7, #12]
   43bc0:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   43bc2:	f853 3022 	ldr.w	r3, [r3, r2, lsl #2]
   43bc6:	4619      	mov	r1, r3
   43bc8:	f7fc ffc3 	bl	40b52 <store32>
   43bcc:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   43bce:	3301      	adds	r3, #1
   43bd0:	637b      	str	r3, [r7, #52]	; 0x34
   43bd2:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   43bd4:	2b07      	cmp	r3, #7
   43bd6:	d9ed      	bls.n	43bb4 <blake2s_final+0x82>
   43bd8:	f107 0314 	add.w	r3, r7, #20
   43bdc:	687a      	ldr	r2, [r7, #4]
   43bde:	4619      	mov	r1, r3
   43be0:	68b8      	ldr	r0, [r7, #8]
   43be2:	f7cc efd8 	blx	10b94 <memcpy@plt>
   43be6:	f107 0314 	add.w	r3, r7, #20
   43bea:	2120      	movs	r1, #32
   43bec:	4618      	mov	r0, r3
   43bee:	f7fc ffe2 	bl	40bb6 <secure_zero_memory>
   43bf2:	2300      	movs	r3, #0
   43bf4:	4618      	mov	r0, r3
   43bf6:	3738      	adds	r7, #56	; 0x38
   43bf8:	46bd      	mov	sp, r7
   43bfa:	bd80      	pop	{r7, pc}

00043bfc <blake2s>:
   43bfc:	b580      	push	{r7, lr}
   43bfe:	b0a4      	sub	sp, #144	; 0x90
   43c00:	af00      	add	r7, sp, #0
   43c02:	60f8      	str	r0, [r7, #12]
   43c04:	60b9      	str	r1, [r7, #8]
   43c06:	607a      	str	r2, [r7, #4]
   43c08:	603b      	str	r3, [r7, #0]
   43c0a:	687b      	ldr	r3, [r7, #4]
   43c0c:	2b00      	cmp	r3, #0
   43c0e:	d105      	bne.n	43c1c <blake2s+0x20>
   43c10:	683b      	ldr	r3, [r7, #0]
   43c12:	2b00      	cmp	r3, #0
   43c14:	d002      	beq.n	43c1c <blake2s+0x20>
   43c16:	f04f 33ff 	mov.w	r3, #4294967295	; 0xffffffff
   43c1a:	e04e      	b.n	43cba <blake2s+0xbe>
   43c1c:	68fb      	ldr	r3, [r7, #12]
   43c1e:	2b00      	cmp	r3, #0
   43c20:	d102      	bne.n	43c28 <blake2s+0x2c>
   43c22:	f04f 33ff 	mov.w	r3, #4294967295	; 0xffffffff
   43c26:	e048      	b.n	43cba <blake2s+0xbe>
   43c28:	f8d7 3098 	ldr.w	r3, [r7, #152]	; 0x98
   43c2c:	2b00      	cmp	r3, #0
   43c2e:	d106      	bne.n	43c3e <blake2s+0x42>
   43c30:	f8d7 309c 	ldr.w	r3, [r7, #156]	; 0x9c
   43c34:	2b00      	cmp	r3, #0
   43c36:	d002      	beq.n	43c3e <blake2s+0x42>
   43c38:	f04f 33ff 	mov.w	r3, #4294967295	; 0xffffffff
   43c3c:	e03d      	b.n	43cba <blake2s+0xbe>
   43c3e:	68bb      	ldr	r3, [r7, #8]
   43c40:	2b00      	cmp	r3, #0
   43c42:	d002      	beq.n	43c4a <blake2s+0x4e>
   43c44:	68bb      	ldr	r3, [r7, #8]
   43c46:	2b20      	cmp	r3, #32
   43c48:	d902      	bls.n	43c50 <blake2s+0x54>
   43c4a:	f04f 33ff 	mov.w	r3, #4294967295	; 0xffffffff
   43c4e:	e034      	b.n	43cba <blake2s+0xbe>
   43c50:	f8d7 309c 	ldr.w	r3, [r7, #156]	; 0x9c
   43c54:	2b20      	cmp	r3, #32
   43c56:	d902      	bls.n	43c5e <blake2s+0x62>
   43c58:	f04f 33ff 	mov.w	r3, #4294967295	; 0xffffffff
   43c5c:	e02d      	b.n	43cba <blake2s+0xbe>
   43c5e:	f8d7 309c 	ldr.w	r3, [r7, #156]	; 0x9c
   43c62:	2b00      	cmp	r3, #0
   43c64:	d00e      	beq.n	43c84 <blake2s+0x88>
   43c66:	f107 0014 	add.w	r0, r7, #20
   43c6a:	f8d7 309c 	ldr.w	r3, [r7, #156]	; 0x9c
   43c6e:	f8d7 2098 	ldr.w	r2, [r7, #152]	; 0x98
   43c72:	68b9      	ldr	r1, [r7, #8]
   43c74:	f7fd f89f 	bl	40db6 <blake2s_init_key>
   43c78:	4603      	mov	r3, r0
   43c7a:	2b00      	cmp	r3, #0
   43c7c:	da0e      	bge.n	43c9c <blake2s+0xa0>
   43c7e:	f04f 33ff 	mov.w	r3, #4294967295	; 0xffffffff
   43c82:	e01a      	b.n	43cba <blake2s+0xbe>
   43c84:	f107 0314 	add.w	r3, r7, #20
   43c88:	68b9      	ldr	r1, [r7, #8]
   43c8a:	4618      	mov	r0, r3
   43c8c:	f7fd f848 	bl	40d20 <blake2s_init>
   43c90:	4603      	mov	r3, r0
   43c92:	2b00      	cmp	r3, #0
   43c94:	da02      	bge.n	43c9c <blake2s+0xa0>
   43c96:	f04f 33ff 	mov.w	r3, #4294967295	; 0xffffffff
   43c9a:	e00e      	b.n	43cba <blake2s+0xbe>
   43c9c:	f107 0314 	add.w	r3, r7, #20
   43ca0:	683a      	ldr	r2, [r7, #0]
   43ca2:	6879      	ldr	r1, [r7, #4]
   43ca4:	4618      	mov	r0, r3
   43ca6:	f7ff fee7 	bl	43a78 <blake2s_update>
   43caa:	f107 0314 	add.w	r3, r7, #20
   43cae:	68ba      	ldr	r2, [r7, #8]
   43cb0:	68f9      	ldr	r1, [r7, #12]
   43cb2:	4618      	mov	r0, r3
   43cb4:	f7ff ff3d 	bl	43b32 <blake2s_final>
   43cb8:	2300      	movs	r3, #0
   43cba:	4618      	mov	r0, r3
   43cbc:	3790      	adds	r7, #144	; 0x90
   43cbe:	46bd      	mov	sp, r7
   43cc0:	bd80      	pop	{r7, pc}
   43cc2:	bf00      	nop

00043cc4 <push>:
   43cc4:	b084      	sub	sp, #16
   43cc6:	b490      	push	{r4, r7}
   43cc8:	b088      	sub	sp, #32
   43cca:	af00      	add	r7, sp, #0
   43ccc:	6078      	str	r0, [r7, #4]
   43cce:	f107 002c 	add.w	r0, r7, #44	; 0x2c
   43cd2:	e880 000e 	stmia.w	r0, {r1, r2, r3}
   43cd6:	687a      	ldr	r2, [r7, #4]
   43cd8:	f44f 43d0 	mov.w	r3, #26624	; 0x6800
   43cdc:	f6c0 1389 	movt	r3, #2441	; 0x989
   43ce0:	4413      	add	r3, r2
   43ce2:	f3bf 8f5b 	dmb	ish
   43ce6:	681b      	ldr	r3, [r3, #0]
   43ce8:	f3bf 8f5b 	dmb	ish
   43cec:	613b      	str	r3, [r7, #16]
   43cee:	693b      	ldr	r3, [r7, #16]
   43cf0:	1c5a      	adds	r2, r3, #1
   43cf2:	f64c 236b 	movw	r3, #51819	; 0xca6b
   43cf6:	f6c6 335f 	movt	r3, #27487	; 0x6b5f
   43cfa:	fba2 3403 	umull	r3, r4, r2, r3
   43cfe:	0da1      	lsrs	r1, r4, #22
   43d00:	f249 6380 	movw	r3, #38528	; 0x9680
   43d04:	f2c0 0398 	movt	r3, #152	; 0x98
   43d08:	fb03 f301 	mul.w	r3, r3, r1
   43d0c:	1ad3      	subs	r3, r2, r3
   43d0e:	61fb      	str	r3, [r7, #28]
   43d10:	687a      	ldr	r2, [r7, #4]
   43d12:	f646 0304 	movw	r3, #26628	; 0x6804
   43d16:	f6c0 1389 	movt	r3, #2441	; 0x989
   43d1a:	4413      	add	r3, r2
   43d1c:	61bb      	str	r3, [r7, #24]
   43d1e:	69bb      	ldr	r3, [r7, #24]
   43d20:	f3bf 8f5b 	dmb	ish
   43d24:	681b      	ldr	r3, [r3, #0]
   43d26:	f3bf 8f5b 	dmb	ish
   43d2a:	60fb      	str	r3, [r7, #12]
   43d2c:	68fa      	ldr	r2, [r7, #12]
   43d2e:	69fb      	ldr	r3, [r7, #28]
   43d30:	429a      	cmp	r2, r3
   43d32:	d021      	beq.n	43d78 <push+0xb4>
   43d34:	687a      	ldr	r2, [r7, #4]
   43d36:	f44f 43d0 	mov.w	r3, #26624	; 0x6800
   43d3a:	f6c0 1389 	movt	r3, #2441	; 0x989
   43d3e:	4413      	add	r3, r2
   43d40:	681b      	ldr	r3, [r3, #0]
   43d42:	687a      	ldr	r2, [r7, #4]
   43d44:	011b      	lsls	r3, r3, #4
   43d46:	4413      	add	r3, r2
   43d48:	461c      	mov	r4, r3
   43d4a:	f107 032c 	add.w	r3, r7, #44	; 0x2c
   43d4e:	cb0f      	ldmia	r3, {r0, r1, r2, r3}
   43d50:	e884 000f 	stmia.w	r4, {r0, r1, r2, r3}
   43d54:	687a      	ldr	r2, [r7, #4]
   43d56:	f44f 43d0 	mov.w	r3, #26624	; 0x6800
   43d5a:	f6c0 1389 	movt	r3, #2441	; 0x989
   43d5e:	4413      	add	r3, r2
   43d60:	617b      	str	r3, [r7, #20]
   43d62:	69fb      	ldr	r3, [r7, #28]
   43d64:	60bb      	str	r3, [r7, #8]
   43d66:	68ba      	ldr	r2, [r7, #8]
   43d68:	697b      	ldr	r3, [r7, #20]
   43d6a:	f3bf 8f5b 	dmb	ish
   43d6e:	601a      	str	r2, [r3, #0]
   43d70:	f3bf 8f5b 	dmb	ish
   43d74:	2301      	movs	r3, #1
   43d76:	e000      	b.n	43d7a <push+0xb6>
   43d78:	2300      	movs	r3, #0
   43d7a:	4618      	mov	r0, r3
   43d7c:	3720      	adds	r7, #32
   43d7e:	46bd      	mov	sp, r7
   43d80:	bc90      	pop	{r4, r7}
   43d82:	b004      	add	sp, #16
   43d84:	4770      	bx	lr

00043d86 <pop>:
   43d86:	b490      	push	{r4, r7}
   43d88:	b08a      	sub	sp, #40	; 0x28
   43d8a:	af00      	add	r7, sp, #0
   43d8c:	6078      	str	r0, [r7, #4]
   43d8e:	6039      	str	r1, [r7, #0]
   43d90:	687a      	ldr	r2, [r7, #4]
   43d92:	f44f 43d0 	mov.w	r3, #26624	; 0x6800
   43d96:	f6c0 1389 	movt	r3, #2441	; 0x989
   43d9a:	4413      	add	r3, r2
   43d9c:	627b      	str	r3, [r7, #36]	; 0x24
   43d9e:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   43da0:	f3bf 8f5b 	dmb	ish
   43da4:	681b      	ldr	r3, [r3, #0]
   43da6:	f3bf 8f5b 	dmb	ish
   43daa:	617b      	str	r3, [r7, #20]
   43dac:	697a      	ldr	r2, [r7, #20]
   43dae:	6879      	ldr	r1, [r7, #4]
   43db0:	f646 0304 	movw	r3, #26628	; 0x6804
   43db4:	f6c0 1389 	movt	r3, #2441	; 0x989
   43db8:	440b      	add	r3, r1
   43dba:	623b      	str	r3, [r7, #32]
   43dbc:	6a3b      	ldr	r3, [r7, #32]
   43dbe:	f3bf 8f5b 	dmb	ish
   43dc2:	681b      	ldr	r3, [r3, #0]
   43dc4:	f3bf 8f5b 	dmb	ish
   43dc8:	613b      	str	r3, [r7, #16]
   43dca:	693b      	ldr	r3, [r7, #16]
   43dcc:	429a      	cmp	r2, r3
   43dce:	d101      	bne.n	43dd4 <pop+0x4e>
   43dd0:	2300      	movs	r3, #0
   43dd2:	e03a      	b.n	43e4a <pop+0xc4>
   43dd4:	687a      	ldr	r2, [r7, #4]
   43dd6:	f646 0304 	movw	r3, #26628	; 0x6804
   43dda:	f6c0 1389 	movt	r3, #2441	; 0x989
   43dde:	4413      	add	r3, r2
   43de0:	681b      	ldr	r3, [r3, #0]
   43de2:	6839      	ldr	r1, [r7, #0]
   43de4:	687a      	ldr	r2, [r7, #4]
   43de6:	011b      	lsls	r3, r3, #4
   43de8:	4413      	add	r3, r2
   43dea:	460c      	mov	r4, r1
   43dec:	cb0f      	ldmia	r3, {r0, r1, r2, r3}
   43dee:	e884 000f 	stmia.w	r4, {r0, r1, r2, r3}
   43df2:	687a      	ldr	r2, [r7, #4]
   43df4:	f646 0304 	movw	r3, #26628	; 0x6804
   43df8:	f6c0 1389 	movt	r3, #2441	; 0x989
   43dfc:	4413      	add	r3, r2
   43dfe:	61fb      	str	r3, [r7, #28]
   43e00:	687a      	ldr	r2, [r7, #4]
   43e02:	f646 0304 	movw	r3, #26628	; 0x6804
   43e06:	f6c0 1389 	movt	r3, #2441	; 0x989
   43e0a:	4413      	add	r3, r2
   43e0c:	f3bf 8f5b 	dmb	ish
   43e10:	681b      	ldr	r3, [r3, #0]
   43e12:	f3bf 8f5b 	dmb	ish
   43e16:	61bb      	str	r3, [r7, #24]
   43e18:	69bb      	ldr	r3, [r7, #24]
   43e1a:	1c59      	adds	r1, r3, #1
   43e1c:	f64c 236b 	movw	r3, #51819	; 0xca6b
   43e20:	f6c6 335f 	movt	r3, #27487	; 0x6b5f
   43e24:	fba1 3403 	umull	r3, r4, r1, r3
   43e28:	0da3      	lsrs	r3, r4, #22
   43e2a:	f249 6280 	movw	r2, #38528	; 0x9680
   43e2e:	f2c0 0298 	movt	r2, #152	; 0x98
   43e32:	fb02 f303 	mul.w	r3, r2, r3
   43e36:	1acb      	subs	r3, r1, r3
   43e38:	60fb      	str	r3, [r7, #12]
   43e3a:	68fa      	ldr	r2, [r7, #12]
   43e3c:	69fb      	ldr	r3, [r7, #28]
   43e3e:	f3bf 8f5b 	dmb	ish
   43e42:	601a      	str	r2, [r3, #0]
   43e44:	f3bf 8f5b 	dmb	ish
   43e48:	2301      	movs	r3, #1
   43e4a:	4618      	mov	r0, r3
   43e4c:	3728      	adds	r7, #40	; 0x28
   43e4e:	46bd      	mov	sp, r7
   43e50:	bc90      	pop	{r4, r7}
   43e52:	4770      	bx	lr

00043e54 <is_empty>:
   43e54:	b480      	push	{r7}
   43e56:	b085      	sub	sp, #20
   43e58:	af00      	add	r7, sp, #0
   43e5a:	6078      	str	r0, [r7, #4]
   43e5c:	687a      	ldr	r2, [r7, #4]
   43e5e:	f44f 43d0 	mov.w	r3, #26624	; 0x6800
   43e62:	f6c0 1389 	movt	r3, #2441	; 0x989
   43e66:	4413      	add	r3, r2
   43e68:	f3bf 8f5b 	dmb	ish
   43e6c:	681b      	ldr	r3, [r3, #0]
   43e6e:	f3bf 8f5b 	dmb	ish
   43e72:	60bb      	str	r3, [r7, #8]
   43e74:	68ba      	ldr	r2, [r7, #8]
   43e76:	6879      	ldr	r1, [r7, #4]
   43e78:	f646 0304 	movw	r3, #26628	; 0x6804
   43e7c:	f6c0 1389 	movt	r3, #2441	; 0x989
   43e80:	440b      	add	r3, r1
   43e82:	f3bf 8f5b 	dmb	ish
   43e86:	681b      	ldr	r3, [r3, #0]
   43e88:	f3bf 8f5b 	dmb	ish
   43e8c:	60fb      	str	r3, [r7, #12]
   43e8e:	68fb      	ldr	r3, [r7, #12]
   43e90:	429a      	cmp	r2, r3
   43e92:	bf0c      	ite	eq
   43e94:	2301      	moveq	r3, #1
   43e96:	2300      	movne	r3, #0
   43e98:	b2db      	uxtb	r3, r3
   43e9a:	4618      	mov	r0, r3
   43e9c:	3714      	adds	r7, #20
   43e9e:	46bd      	mov	sp, r7
   43ea0:	f85d 7b04 	ldr.w	r7, [sp], #4
   43ea4:	4770      	bx	lr

00043ea6 <ringbuffer_init>:
   43ea6:	b480      	push	{r7}
   43ea8:	b087      	sub	sp, #28
   43eaa:	af00      	add	r7, sp, #0
   43eac:	6078      	str	r0, [r7, #4]
   43eae:	687a      	ldr	r2, [r7, #4]
   43eb0:	f44f 43d0 	mov.w	r3, #26624	; 0x6800
   43eb4:	f6c0 1389 	movt	r3, #2441	; 0x989
   43eb8:	4413      	add	r3, r2
   43eba:	617b      	str	r3, [r7, #20]
   43ebc:	2300      	movs	r3, #0
   43ebe:	60fb      	str	r3, [r7, #12]
   43ec0:	68fa      	ldr	r2, [r7, #12]
   43ec2:	697b      	ldr	r3, [r7, #20]
   43ec4:	601a      	str	r2, [r3, #0]
   43ec6:	687a      	ldr	r2, [r7, #4]
   43ec8:	f646 0304 	movw	r3, #26628	; 0x6804
   43ecc:	f6c0 1389 	movt	r3, #2441	; 0x989
   43ed0:	4413      	add	r3, r2
   43ed2:	613b      	str	r3, [r7, #16]
   43ed4:	2300      	movs	r3, #0
   43ed6:	60bb      	str	r3, [r7, #8]
   43ed8:	68ba      	ldr	r2, [r7, #8]
   43eda:	693b      	ldr	r3, [r7, #16]
   43edc:	601a      	str	r2, [r3, #0]
   43ede:	2301      	movs	r3, #1
   43ee0:	4618      	mov	r0, r3
   43ee2:	371c      	adds	r7, #28
   43ee4:	46bd      	mov	sp, r7
   43ee6:	f85d 7b04 	ldr.w	r7, [sp], #4
   43eea:	4770      	bx	lr

00043eec <read_r8>:
   43eec:	b480      	push	{r7}
   43eee:	b083      	sub	sp, #12
   43ef0:	af00      	add	r7, sp, #0
   43ef2:	4643      	mov	r3, r8
   43ef4:	607b      	str	r3, [r7, #4]
   43ef6:	687b      	ldr	r3, [r7, #4]
   43ef8:	4618      	mov	r0, r3
   43efa:	370c      	adds	r7, #12
   43efc:	46bd      	mov	sp, r7
   43efe:	f85d 7b04 	ldr.w	r7, [sp], #4
   43f02:	4770      	bx	lr

00043f04 <c_direct_tsf_recording>:
   43f04:	b590      	push	{r4, r7, lr}
   43f06:	b08b      	sub	sp, #44	; 0x2c
   43f08:	af02      	add	r7, sp, #8
   43f0a:	6078      	str	r0, [r7, #4]
   43f0c:	4c20      	ldr	r4, [pc, #128]	; (43f90 <c_direct_tsf_recording+0x8c>)
   43f0e:	447c      	add	r4, pc
   43f10:	4b20      	ldr	r3, [pc, #128]	; (43f94 <c_direct_tsf_recording+0x90>)
   43f12:	58e3      	ldr	r3, [r4, r3]
   43f14:	681b      	ldr	r3, [r3, #0]
   43f16:	2b00      	cmp	r3, #0
   43f18:	d109      	bne.n	43f2e <c_direct_tsf_recording+0x2a>
   43f1a:	4b1e      	ldr	r3, [pc, #120]	; (43f94 <c_direct_tsf_recording+0x90>)
   43f1c:	58e3      	ldr	r3, [r4, r3]
   43f1e:	461a      	mov	r2, r3
   43f20:	2301      	movs	r3, #1
   43f22:	6013      	str	r3, [r2, #0]
   43f24:	4b1c      	ldr	r3, [pc, #112]	; (43f98 <c_direct_tsf_recording+0x94>)
   43f26:	58e3      	ldr	r3, [r4, r3]
   43f28:	4618      	mov	r0, r3
   43f2a:	f7ff ffbc 	bl	43ea6 <ringbuffer_init>
   43f2e:	f7ff ffdd 	bl	43eec <read_r8>
   43f32:	61f8      	str	r0, [r7, #28]
   43f34:	687b      	ldr	r3, [r7, #4]
   43f36:	3308      	adds	r3, #8
   43f38:	60fb      	str	r3, [r7, #12]
   43f3a:	69fb      	ldr	r3, [r7, #28]
   43f3c:	613b      	str	r3, [r7, #16]
   43f3e:	230a      	movs	r3, #10
   43f40:	763b      	strb	r3, [r7, #24]
   43f42:	4b16      	ldr	r3, [pc, #88]	; (43f9c <c_direct_tsf_recording+0x98>)
   43f44:	58e3      	ldr	r3, [r4, r3]
   43f46:	681b      	ldr	r3, [r3, #0]
   43f48:	2b00      	cmp	r3, #0
   43f4a:	d01c      	beq.n	43f86 <c_direct_tsf_recording+0x82>
   43f4c:	69fb      	ldr	r3, [r7, #28]
   43f4e:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   43f52:	d903      	bls.n	43f5c <c_direct_tsf_recording+0x58>
   43f54:	687b      	ldr	r3, [r7, #4]
   43f56:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   43f5a:	d814      	bhi.n	43f86 <c_direct_tsf_recording+0x82>
   43f5c:	69bb      	ldr	r3, [r7, #24]
   43f5e:	9300      	str	r3, [sp, #0]
   43f60:	f107 030c 	add.w	r3, r7, #12
   43f64:	cb0e      	ldmia	r3, {r1, r2, r3}
   43f66:	480c      	ldr	r0, [pc, #48]	; (43f98 <c_direct_tsf_recording+0x94>)
   43f68:	5820      	ldr	r0, [r4, r0]
   43f6a:	f7ff feab 	bl	43cc4 <push>
   43f6e:	4603      	mov	r3, r0
   43f70:	f083 0301 	eor.w	r3, r3, #1
   43f74:	b2db      	uxtb	r3, r3
   43f76:	2b00      	cmp	r3, #0
   43f78:	d005      	beq.n	43f86 <c_direct_tsf_recording+0x82>
   43f7a:	4b09      	ldr	r3, [pc, #36]	; (43fa0 <c_direct_tsf_recording+0x9c>)
   43f7c:	447b      	add	r3, pc
   43f7e:	4618      	mov	r0, r3
   43f80:	f7cc ee2c 	blx	10bdc <puts@plt>
   43f84:	bf00      	nop
   43f86:	bf00      	nop
   43f88:	3724      	adds	r7, #36	; 0x24
   43f8a:	46bd      	mov	sp, r7
   43f8c:	bd90      	pop	{r4, r7, pc}
   43f8e:	bf00      	nop
   43f90:	000130ee 	andeq	r3, r1, lr, ror #1
   43f94:	000000ac 	andeq	r0, r0, ip, lsr #1
   43f98:	000000c8 	andeq	r0, r0, r8, asr #1
   43f9c:	000000d4 	ldrdeq	r0, [r0], -r4
   43fa0:	000029fc 	strdeq	r2, [r0], -ip

00043fa4 <isBranchTaken>:
   43fa4:	b480      	push	{r7}
   43fa6:	b085      	sub	sp, #20
   43fa8:	af00      	add	r7, sp, #0
   43faa:	6078      	str	r0, [r7, #4]
   43fac:	6039      	str	r1, [r7, #0]
   43fae:	683b      	ldr	r3, [r7, #0]
   43fb0:	f003 4300 	and.w	r3, r3, #2147483648	; 0x80000000
   43fb4:	2b00      	cmp	r3, #0
   43fb6:	bf14      	ite	ne
   43fb8:	2301      	movne	r3, #1
   43fba:	2300      	moveq	r3, #0
   43fbc:	73fb      	strb	r3, [r7, #15]
   43fbe:	683b      	ldr	r3, [r7, #0]
   43fc0:	f003 4380 	and.w	r3, r3, #1073741824	; 0x40000000
   43fc4:	2b00      	cmp	r3, #0
   43fc6:	bf14      	ite	ne
   43fc8:	2301      	movne	r3, #1
   43fca:	2300      	moveq	r3, #0
   43fcc:	73bb      	strb	r3, [r7, #14]
   43fce:	683b      	ldr	r3, [r7, #0]
   43fd0:	f003 5300 	and.w	r3, r3, #536870912	; 0x20000000
   43fd4:	2b00      	cmp	r3, #0
   43fd6:	bf14      	ite	ne
   43fd8:	2301      	movne	r3, #1
   43fda:	2300      	moveq	r3, #0
   43fdc:	737b      	strb	r3, [r7, #13]
   43fde:	683b      	ldr	r3, [r7, #0]
   43fe0:	f003 5380 	and.w	r3, r3, #268435456	; 0x10000000
   43fe4:	2b00      	cmp	r3, #0
   43fe6:	bf14      	ite	ne
   43fe8:	2301      	movne	r3, #1
   43fea:	2300      	moveq	r3, #0
   43fec:	733b      	strb	r3, [r7, #12]
   43fee:	687b      	ldr	r3, [r7, #4]
   43ff0:	2b0e      	cmp	r3, #14
   43ff2:	f200 80b0 	bhi.w	44156 <isBranchTaken+0x1b2>
   43ff6:	a202      	add	r2, pc, #8	; (adr r2, 44000 <isBranchTaken+0x5c>)
   43ff8:	f852 3023 	ldr.w	r3, [r2, r3, lsl #2]
   43ffc:	441a      	add	r2, r3
   43ffe:	4710      	bx	r2
   44000:	0000003d 	andeq	r0, r0, sp, lsr r0
   44004:	00000041 	andeq	r0, r0, r1, asr #32
   44008:	0000005b 	andeq	r0, r0, fp, asr r0
   4400c:	0000005f 	andeq	r0, r0, pc, asr r0
   44010:	00000079 	andeq	r0, r0, r9, ror r0
   44014:	0000007d 	andeq	r0, r0, sp, ror r0
   44018:	00000097 	muleq	r0, r7, r0
   4401c:	0000009b 	muleq	r0, fp, r0
   44020:	000000b5 	strheq	r0, [r0], -r5
   44024:	000000d5 	ldrdeq	r0, [r0], -r5
   44028:	000000f5 	strdeq	r0, [r0], -r5
   4402c:	00000105 	andeq	r0, r0, r5, lsl #2
   44030:	00000115 	andeq	r0, r0, r5, lsl r1
   44034:	00000137 	andeq	r0, r0, r7, lsr r1
   44038:	00000153 	andeq	r0, r0, r3, asr r1
   4403c:	7bbb      	ldrb	r3, [r7, #14]
   4403e:	e08b      	b.n	44158 <isBranchTaken+0x1b4>
   44040:	7bbb      	ldrb	r3, [r7, #14]
   44042:	2b00      	cmp	r3, #0
   44044:	bf14      	ite	ne
   44046:	2301      	movne	r3, #1
   44048:	2300      	moveq	r3, #0
   4404a:	b2db      	uxtb	r3, r3
   4404c:	f083 0301 	eor.w	r3, r3, #1
   44050:	b2db      	uxtb	r3, r3
   44052:	f003 0301 	and.w	r3, r3, #1
   44056:	b2db      	uxtb	r3, r3
   44058:	e07e      	b.n	44158 <isBranchTaken+0x1b4>
   4405a:	7b7b      	ldrb	r3, [r7, #13]
   4405c:	e07c      	b.n	44158 <isBranchTaken+0x1b4>
   4405e:	7b7b      	ldrb	r3, [r7, #13]
   44060:	2b00      	cmp	r3, #0
   44062:	bf14      	ite	ne
   44064:	2301      	movne	r3, #1
   44066:	2300      	moveq	r3, #0
   44068:	b2db      	uxtb	r3, r3
   4406a:	f083 0301 	eor.w	r3, r3, #1
   4406e:	b2db      	uxtb	r3, r3
   44070:	f003 0301 	and.w	r3, r3, #1
   44074:	b2db      	uxtb	r3, r3
   44076:	e06f      	b.n	44158 <isBranchTaken+0x1b4>
   44078:	7bfb      	ldrb	r3, [r7, #15]
   4407a:	e06d      	b.n	44158 <isBranchTaken+0x1b4>
   4407c:	7bfb      	ldrb	r3, [r7, #15]
   4407e:	2b00      	cmp	r3, #0
   44080:	bf14      	ite	ne
   44082:	2301      	movne	r3, #1
   44084:	2300      	moveq	r3, #0
   44086:	b2db      	uxtb	r3, r3
   44088:	f083 0301 	eor.w	r3, r3, #1
   4408c:	b2db      	uxtb	r3, r3
   4408e:	f003 0301 	and.w	r3, r3, #1
   44092:	b2db      	uxtb	r3, r3
   44094:	e060      	b.n	44158 <isBranchTaken+0x1b4>
   44096:	7b3b      	ldrb	r3, [r7, #12]
   44098:	e05e      	b.n	44158 <isBranchTaken+0x1b4>
   4409a:	7b3b      	ldrb	r3, [r7, #12]
   4409c:	2b00      	cmp	r3, #0
   4409e:	bf14      	ite	ne
   440a0:	2301      	movne	r3, #1
   440a2:	2300      	moveq	r3, #0
   440a4:	b2db      	uxtb	r3, r3
   440a6:	f083 0301 	eor.w	r3, r3, #1
   440aa:	b2db      	uxtb	r3, r3
   440ac:	f003 0301 	and.w	r3, r3, #1
   440b0:	b2db      	uxtb	r3, r3
   440b2:	e051      	b.n	44158 <isBranchTaken+0x1b4>
   440b4:	7b7b      	ldrb	r3, [r7, #13]
   440b6:	2b00      	cmp	r3, #0
   440b8:	d007      	beq.n	440ca <isBranchTaken+0x126>
   440ba:	7bbb      	ldrb	r3, [r7, #14]
   440bc:	f083 0301 	eor.w	r3, r3, #1
   440c0:	b2db      	uxtb	r3, r3
   440c2:	2b00      	cmp	r3, #0
   440c4:	d001      	beq.n	440ca <isBranchTaken+0x126>
   440c6:	2301      	movs	r3, #1
   440c8:	e000      	b.n	440cc <isBranchTaken+0x128>
   440ca:	2300      	movs	r3, #0
   440cc:	f003 0301 	and.w	r3, r3, #1
   440d0:	b2db      	uxtb	r3, r3
   440d2:	e041      	b.n	44158 <isBranchTaken+0x1b4>
   440d4:	7b7b      	ldrb	r3, [r7, #13]
   440d6:	f083 0301 	eor.w	r3, r3, #1
   440da:	b2db      	uxtb	r3, r3
   440dc:	2b00      	cmp	r3, #0
   440de:	d102      	bne.n	440e6 <isBranchTaken+0x142>
   440e0:	7bbb      	ldrb	r3, [r7, #14]
   440e2:	2b00      	cmp	r3, #0
   440e4:	d001      	beq.n	440ea <isBranchTaken+0x146>
   440e6:	2301      	movs	r3, #1
   440e8:	e000      	b.n	440ec <isBranchTaken+0x148>
   440ea:	2300      	movs	r3, #0
   440ec:	f003 0301 	and.w	r3, r3, #1
   440f0:	b2db      	uxtb	r3, r3
   440f2:	e031      	b.n	44158 <isBranchTaken+0x1b4>
   440f4:	7bfa      	ldrb	r2, [r7, #15]
   440f6:	7b3b      	ldrb	r3, [r7, #12]
   440f8:	429a      	cmp	r2, r3
   440fa:	bf0c      	ite	eq
   440fc:	2301      	moveq	r3, #1
   440fe:	2300      	movne	r3, #0
   44100:	b2db      	uxtb	r3, r3
   44102:	e029      	b.n	44158 <isBranchTaken+0x1b4>
   44104:	7bfa      	ldrb	r2, [r7, #15]
   44106:	7b3b      	ldrb	r3, [r7, #12]
   44108:	429a      	cmp	r2, r3
   4410a:	bf14      	ite	ne
   4410c:	2301      	movne	r3, #1
   4410e:	2300      	moveq	r3, #0
   44110:	b2db      	uxtb	r3, r3
   44112:	e021      	b.n	44158 <isBranchTaken+0x1b4>
   44114:	7bbb      	ldrb	r3, [r7, #14]
   44116:	f083 0301 	eor.w	r3, r3, #1
   4411a:	b2db      	uxtb	r3, r3
   4411c:	2b00      	cmp	r3, #0
   4411e:	d005      	beq.n	4412c <isBranchTaken+0x188>
   44120:	7bfa      	ldrb	r2, [r7, #15]
   44122:	7b3b      	ldrb	r3, [r7, #12]
   44124:	429a      	cmp	r2, r3
   44126:	d101      	bne.n	4412c <isBranchTaken+0x188>
   44128:	2301      	movs	r3, #1
   4412a:	e000      	b.n	4412e <isBranchTaken+0x18a>
   4412c:	2300      	movs	r3, #0
   4412e:	f003 0301 	and.w	r3, r3, #1
   44132:	b2db      	uxtb	r3, r3
   44134:	e010      	b.n	44158 <isBranchTaken+0x1b4>
   44136:	7bbb      	ldrb	r3, [r7, #14]
   44138:	2b00      	cmp	r3, #0
   4413a:	d103      	bne.n	44144 <isBranchTaken+0x1a0>
   4413c:	7bfa      	ldrb	r2, [r7, #15]
   4413e:	7b3b      	ldrb	r3, [r7, #12]
   44140:	429a      	cmp	r2, r3
   44142:	d001      	beq.n	44148 <isBranchTaken+0x1a4>
   44144:	2301      	movs	r3, #1
   44146:	e000      	b.n	4414a <isBranchTaken+0x1a6>
   44148:	2300      	movs	r3, #0
   4414a:	f003 0301 	and.w	r3, r3, #1
   4414e:	b2db      	uxtb	r3, r3
   44150:	e002      	b.n	44158 <isBranchTaken+0x1b4>
   44152:	2301      	movs	r3, #1
   44154:	e000      	b.n	44158 <isBranchTaken+0x1b4>
   44156:	2300      	movs	r3, #0
   44158:	4618      	mov	r0, r3
   4415a:	3714      	adds	r7, #20
   4415c:	46bd      	mov	sp, r7
   4415e:	f85d 7b04 	ldr.w	r7, [sp], #4
   44162:	4770      	bx	lr

00044164 <c_direct_tsf_cc_recording>:
   44164:	b590      	push	{r4, r7, lr}
   44166:	b091      	sub	sp, #68	; 0x44
   44168:	af02      	add	r7, sp, #8
   4416a:	60f8      	str	r0, [r7, #12]
   4416c:	60b9      	str	r1, [r7, #8]
   4416e:	607a      	str	r2, [r7, #4]
   44170:	4c3d      	ldr	r4, [pc, #244]	; (44268 <c_direct_tsf_cc_recording+0x104>)
   44172:	447c      	add	r4, pc
   44174:	4b3d      	ldr	r3, [pc, #244]	; (4426c <c_direct_tsf_cc_recording+0x108>)
   44176:	58e3      	ldr	r3, [r4, r3]
   44178:	681b      	ldr	r3, [r3, #0]
   4417a:	2b00      	cmp	r3, #0
   4417c:	d109      	bne.n	44192 <c_direct_tsf_cc_recording+0x2e>
   4417e:	4b3b      	ldr	r3, [pc, #236]	; (4426c <c_direct_tsf_cc_recording+0x108>)
   44180:	58e3      	ldr	r3, [r4, r3]
   44182:	461a      	mov	r2, r3
   44184:	2301      	movs	r3, #1
   44186:	6013      	str	r3, [r2, #0]
   44188:	4b39      	ldr	r3, [pc, #228]	; (44270 <c_direct_tsf_cc_recording+0x10c>)
   4418a:	58e3      	ldr	r3, [r4, r3]
   4418c:	4618      	mov	r0, r3
   4418e:	f7ff fe8a 	bl	43ea6 <ringbuffer_init>
   44192:	68b9      	ldr	r1, [r7, #8]
   44194:	6878      	ldr	r0, [r7, #4]
   44196:	f7ff ff05 	bl	43fa4 <isBranchTaken>
   4419a:	4603      	mov	r3, r0
   4419c:	f887 3037 	strb.w	r3, [r7, #55]	; 0x37
   441a0:	f7ff fea4 	bl	43eec <read_r8>
   441a4:	6338      	str	r0, [r7, #48]	; 0x30
   441a6:	68fb      	ldr	r3, [r7, #12]
   441a8:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   441ac:	d822      	bhi.n	441f4 <c_direct_tsf_cc_recording+0x90>
   441ae:	68fb      	ldr	r3, [r7, #12]
   441b0:	613b      	str	r3, [r7, #16]
   441b2:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   441b4:	617b      	str	r3, [r7, #20]
   441b6:	f897 3037 	ldrb.w	r3, [r7, #55]	; 0x37
   441ba:	61bb      	str	r3, [r7, #24]
   441bc:	2304      	movs	r3, #4
   441be:	773b      	strb	r3, [r7, #28]
   441c0:	4b2c      	ldr	r3, [pc, #176]	; (44274 <c_direct_tsf_cc_recording+0x110>)
   441c2:	58e3      	ldr	r3, [r4, r3]
   441c4:	681b      	ldr	r3, [r3, #0]
   441c6:	2b00      	cmp	r3, #0
   441c8:	d01b      	beq.n	44202 <c_direct_tsf_cc_recording+0x9e>
   441ca:	69fb      	ldr	r3, [r7, #28]
   441cc:	9300      	str	r3, [sp, #0]
   441ce:	f107 0310 	add.w	r3, r7, #16
   441d2:	cb0e      	ldmia	r3, {r1, r2, r3}
   441d4:	4826      	ldr	r0, [pc, #152]	; (44270 <c_direct_tsf_cc_recording+0x10c>)
   441d6:	5820      	ldr	r0, [r4, r0]
   441d8:	f7ff fd74 	bl	43cc4 <push>
   441dc:	4603      	mov	r3, r0
   441de:	f083 0301 	eor.w	r3, r3, #1
   441e2:	b2db      	uxtb	r3, r3
   441e4:	2b00      	cmp	r3, #0
   441e6:	d00c      	beq.n	44202 <c_direct_tsf_cc_recording+0x9e>
   441e8:	4b23      	ldr	r3, [pc, #140]	; (44278 <c_direct_tsf_cc_recording+0x114>)
   441ea:	447b      	add	r3, pc
   441ec:	4618      	mov	r0, r3
   441ee:	f7cc ecf6 	blx	10bdc <puts@plt>
   441f2:	e006      	b.n	44202 <c_direct_tsf_cc_recording+0x9e>
   441f4:	f897 3037 	ldrb.w	r3, [r7, #55]	; 0x37
   441f8:	f083 0301 	eor.w	r3, r3, #1
   441fc:	b2db      	uxtb	r3, r3
   441fe:	2b00      	cmp	r3, #0
   44200:	d12b      	bne.n	4425a <c_direct_tsf_cc_recording+0xf6>
   44202:	68fb      	ldr	r3, [r7, #12]
   44204:	623b      	str	r3, [r7, #32]
   44206:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   44208:	627b      	str	r3, [r7, #36]	; 0x24
   4420a:	68bb      	ldr	r3, [r7, #8]
   4420c:	62bb      	str	r3, [r7, #40]	; 0x28
   4420e:	230a      	movs	r3, #10
   44210:	f887 302c 	strb.w	r3, [r7, #44]	; 0x2c
   44214:	4b17      	ldr	r3, [pc, #92]	; (44274 <c_direct_tsf_cc_recording+0x110>)
   44216:	58e3      	ldr	r3, [r4, r3]
   44218:	681b      	ldr	r3, [r3, #0]
   4421a:	2b00      	cmp	r3, #0
   4421c:	d01f      	beq.n	4425e <c_direct_tsf_cc_recording+0xfa>
   4421e:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   44220:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   44224:	d903      	bls.n	4422e <c_direct_tsf_cc_recording+0xca>
   44226:	68fb      	ldr	r3, [r7, #12]
   44228:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   4422c:	d817      	bhi.n	4425e <c_direct_tsf_cc_recording+0xfa>
   4422e:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   44230:	9300      	str	r3, [sp, #0]
   44232:	f107 0320 	add.w	r3, r7, #32
   44236:	cb0e      	ldmia	r3, {r1, r2, r3}
   44238:	480d      	ldr	r0, [pc, #52]	; (44270 <c_direct_tsf_cc_recording+0x10c>)
   4423a:	5820      	ldr	r0, [r4, r0]
   4423c:	f7ff fd42 	bl	43cc4 <push>
   44240:	4603      	mov	r3, r0
   44242:	f083 0301 	eor.w	r3, r3, #1
   44246:	b2db      	uxtb	r3, r3
   44248:	2b00      	cmp	r3, #0
   4424a:	d008      	beq.n	4425e <c_direct_tsf_cc_recording+0xfa>
   4424c:	4b0b      	ldr	r3, [pc, #44]	; (4427c <c_direct_tsf_cc_recording+0x118>)
   4424e:	447b      	add	r3, pc
   44250:	4618      	mov	r0, r3
   44252:	f7cc ecc4 	blx	10bdc <puts@plt>
   44256:	bf00      	nop
   44258:	e001      	b.n	4425e <c_direct_tsf_cc_recording+0xfa>
   4425a:	bf00      	nop
   4425c:	e000      	b.n	44260 <c_direct_tsf_cc_recording+0xfc>
   4425e:	bf00      	nop
   44260:	373c      	adds	r7, #60	; 0x3c
   44262:	46bd      	mov	sp, r7
   44264:	bd90      	pop	{r4, r7, pc}
   44266:	bf00      	nop
   44268:	00012e8a 	andeq	r2, r1, sl, lsl #29
   4426c:	000000ac 	andeq	r0, r0, ip, lsr #1
   44270:	000000c8 	andeq	r0, r0, r8, asr #1
   44274:	000000d4 	ldrdeq	r0, [r0], -r4
   44278:	0000278e 	andeq	r2, r0, lr, lsl #15
   4427c:	0000272a 	andeq	r2, r0, sl, lsr #14

00044280 <c_direct_tsf_bcc_recording>:
   44280:	b590      	push	{r4, r7, lr}
   44282:	b091      	sub	sp, #68	; 0x44
   44284:	af02      	add	r7, sp, #8
   44286:	60f8      	str	r0, [r7, #12]
   44288:	60b9      	str	r1, [r7, #8]
   4428a:	607a      	str	r2, [r7, #4]
   4428c:	4c3f      	ldr	r4, [pc, #252]	; (4438c <c_direct_tsf_bcc_recording+0x10c>)
   4428e:	447c      	add	r4, pc
   44290:	4b3f      	ldr	r3, [pc, #252]	; (44390 <c_direct_tsf_bcc_recording+0x110>)
   44292:	58e3      	ldr	r3, [r4, r3]
   44294:	681b      	ldr	r3, [r3, #0]
   44296:	2b00      	cmp	r3, #0
   44298:	d109      	bne.n	442ae <c_direct_tsf_bcc_recording+0x2e>
   4429a:	4b3d      	ldr	r3, [pc, #244]	; (44390 <c_direct_tsf_bcc_recording+0x110>)
   4429c:	58e3      	ldr	r3, [r4, r3]
   4429e:	461a      	mov	r2, r3
   442a0:	2301      	movs	r3, #1
   442a2:	6013      	str	r3, [r2, #0]
   442a4:	4b3b      	ldr	r3, [pc, #236]	; (44394 <c_direct_tsf_bcc_recording+0x114>)
   442a6:	58e3      	ldr	r3, [r4, r3]
   442a8:	4618      	mov	r0, r3
   442aa:	f7ff fdfc 	bl	43ea6 <ringbuffer_init>
   442ae:	68b9      	ldr	r1, [r7, #8]
   442b0:	6878      	ldr	r0, [r7, #4]
   442b2:	f7ff fe77 	bl	43fa4 <isBranchTaken>
   442b6:	4603      	mov	r3, r0
   442b8:	f887 3037 	strb.w	r3, [r7, #55]	; 0x37
   442bc:	f7ff fe16 	bl	43eec <read_r8>
   442c0:	6338      	str	r0, [r7, #48]	; 0x30
   442c2:	68fb      	ldr	r3, [r7, #12]
   442c4:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   442c8:	d825      	bhi.n	44316 <c_direct_tsf_bcc_recording+0x96>
   442ca:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   442cc:	2b64      	cmp	r3, #100	; 0x64
   442ce:	d122      	bne.n	44316 <c_direct_tsf_bcc_recording+0x96>
   442d0:	68fb      	ldr	r3, [r7, #12]
   442d2:	613b      	str	r3, [r7, #16]
   442d4:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   442d6:	617b      	str	r3, [r7, #20]
   442d8:	f897 3037 	ldrb.w	r3, [r7, #55]	; 0x37
   442dc:	61bb      	str	r3, [r7, #24]
   442de:	2304      	movs	r3, #4
   442e0:	773b      	strb	r3, [r7, #28]
   442e2:	4b2d      	ldr	r3, [pc, #180]	; (44398 <c_direct_tsf_bcc_recording+0x118>)
   442e4:	58e3      	ldr	r3, [r4, r3]
   442e6:	681b      	ldr	r3, [r3, #0]
   442e8:	2b00      	cmp	r3, #0
   442ea:	d01c      	beq.n	44326 <c_direct_tsf_bcc_recording+0xa6>
   442ec:	69fb      	ldr	r3, [r7, #28]
   442ee:	9300      	str	r3, [sp, #0]
   442f0:	f107 0310 	add.w	r3, r7, #16
   442f4:	cb0e      	ldmia	r3, {r1, r2, r3}
   442f6:	4827      	ldr	r0, [pc, #156]	; (44394 <c_direct_tsf_bcc_recording+0x114>)
   442f8:	5820      	ldr	r0, [r4, r0]
   442fa:	f7ff fce3 	bl	43cc4 <push>
   442fe:	4603      	mov	r3, r0
   44300:	f083 0301 	eor.w	r3, r3, #1
   44304:	b2db      	uxtb	r3, r3
   44306:	2b00      	cmp	r3, #0
   44308:	d00d      	beq.n	44326 <c_direct_tsf_bcc_recording+0xa6>
   4430a:	4b24      	ldr	r3, [pc, #144]	; (4439c <c_direct_tsf_bcc_recording+0x11c>)
   4430c:	447b      	add	r3, pc
   4430e:	4618      	mov	r0, r3
   44310:	f7cc ec64 	blx	10bdc <puts@plt>
   44314:	e007      	b.n	44326 <c_direct_tsf_bcc_recording+0xa6>
   44316:	f897 3037 	ldrb.w	r3, [r7, #55]	; 0x37
   4431a:	f083 0301 	eor.w	r3, r3, #1
   4431e:	b2db      	uxtb	r3, r3
   44320:	2b00      	cmp	r3, #0
   44322:	d12d      	bne.n	44380 <c_direct_tsf_bcc_recording+0x100>
   44324:	e000      	b.n	44328 <c_direct_tsf_bcc_recording+0xa8>
   44326:	bf00      	nop
   44328:	68fb      	ldr	r3, [r7, #12]
   4432a:	623b      	str	r3, [r7, #32]
   4432c:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   4432e:	627b      	str	r3, [r7, #36]	; 0x24
   44330:	68bb      	ldr	r3, [r7, #8]
   44332:	62bb      	str	r3, [r7, #40]	; 0x28
   44334:	230a      	movs	r3, #10
   44336:	f887 302c 	strb.w	r3, [r7, #44]	; 0x2c
   4433a:	4b17      	ldr	r3, [pc, #92]	; (44398 <c_direct_tsf_bcc_recording+0x118>)
   4433c:	58e3      	ldr	r3, [r4, r3]
   4433e:	681b      	ldr	r3, [r3, #0]
   44340:	2b00      	cmp	r3, #0
   44342:	d01f      	beq.n	44384 <c_direct_tsf_bcc_recording+0x104>
   44344:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   44346:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   4434a:	d903      	bls.n	44354 <c_direct_tsf_bcc_recording+0xd4>
   4434c:	68fb      	ldr	r3, [r7, #12]
   4434e:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   44352:	d817      	bhi.n	44384 <c_direct_tsf_bcc_recording+0x104>
   44354:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   44356:	9300      	str	r3, [sp, #0]
   44358:	f107 0320 	add.w	r3, r7, #32
   4435c:	cb0e      	ldmia	r3, {r1, r2, r3}
   4435e:	480d      	ldr	r0, [pc, #52]	; (44394 <c_direct_tsf_bcc_recording+0x114>)
   44360:	5820      	ldr	r0, [r4, r0]
   44362:	f7ff fcaf 	bl	43cc4 <push>
   44366:	4603      	mov	r3, r0
   44368:	f083 0301 	eor.w	r3, r3, #1
   4436c:	b2db      	uxtb	r3, r3
   4436e:	2b00      	cmp	r3, #0
   44370:	d008      	beq.n	44384 <c_direct_tsf_bcc_recording+0x104>
   44372:	4b0b      	ldr	r3, [pc, #44]	; (443a0 <c_direct_tsf_bcc_recording+0x120>)
   44374:	447b      	add	r3, pc
   44376:	4618      	mov	r0, r3
   44378:	f7cc ec30 	blx	10bdc <puts@plt>
   4437c:	bf00      	nop
   4437e:	e001      	b.n	44384 <c_direct_tsf_bcc_recording+0x104>
   44380:	bf00      	nop
   44382:	e000      	b.n	44386 <c_direct_tsf_bcc_recording+0x106>
   44384:	bf00      	nop
   44386:	373c      	adds	r7, #60	; 0x3c
   44388:	46bd      	mov	sp, r7
   4438a:	bd90      	pop	{r4, r7, pc}
   4438c:	00012d6e 	andeq	r2, r1, lr, ror #26
   44390:	000000ac 	andeq	r0, r0, ip, lsr #1
   44394:	000000c8 	andeq	r0, r0, r8, asr #1
   44398:	000000d4 	ldrdeq	r0, [r0], -r4
   4439c:	0000266c 	andeq	r2, r0, ip, ror #12
   443a0:	00002604 	andeq	r2, r0, r4, lsl #12

000443a4 <c_indirect_tsf_recording>:
   443a4:	b590      	push	{r4, r7, lr}
   443a6:	b08b      	sub	sp, #44	; 0x2c
   443a8:	af02      	add	r7, sp, #8
   443aa:	6078      	str	r0, [r7, #4]
   443ac:	4c23      	ldr	r4, [pc, #140]	; (4443c <c_indirect_tsf_recording+0x98>)
   443ae:	447c      	add	r4, pc
   443b0:	4b23      	ldr	r3, [pc, #140]	; (44440 <c_indirect_tsf_recording+0x9c>)
   443b2:	58e3      	ldr	r3, [r4, r3]
   443b4:	681b      	ldr	r3, [r3, #0]
   443b6:	2b00      	cmp	r3, #0
   443b8:	d109      	bne.n	443ce <c_indirect_tsf_recording+0x2a>
   443ba:	4b21      	ldr	r3, [pc, #132]	; (44440 <c_indirect_tsf_recording+0x9c>)
   443bc:	58e3      	ldr	r3, [r4, r3]
   443be:	461a      	mov	r2, r3
   443c0:	2301      	movs	r3, #1
   443c2:	6013      	str	r3, [r2, #0]
   443c4:	4b1f      	ldr	r3, [pc, #124]	; (44444 <c_indirect_tsf_recording+0xa0>)
   443c6:	58e3      	ldr	r3, [r4, r3]
   443c8:	4618      	mov	r0, r3
   443ca:	f7ff fd6c 	bl	43ea6 <ringbuffer_init>
   443ce:	f7ff fd8d 	bl	43eec <read_r8>
   443d2:	61f8      	str	r0, [r7, #28]
   443d4:	687b      	ldr	r3, [r7, #4]
   443d6:	60fb      	str	r3, [r7, #12]
   443d8:	69fb      	ldr	r3, [r7, #28]
   443da:	613b      	str	r3, [r7, #16]
   443dc:	230a      	movs	r3, #10
   443de:	763b      	strb	r3, [r7, #24]
   443e0:	4b19      	ldr	r3, [pc, #100]	; (44448 <c_indirect_tsf_recording+0xa4>)
   443e2:	58e3      	ldr	r3, [r4, r3]
   443e4:	681b      	ldr	r3, [r3, #0]
   443e6:	2b00      	cmp	r3, #0
   443e8:	d024      	beq.n	44434 <c_indirect_tsf_recording+0x90>
   443ea:	69fb      	ldr	r3, [r7, #28]
   443ec:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   443f0:	d803      	bhi.n	443fa <c_indirect_tsf_recording+0x56>
   443f2:	687b      	ldr	r3, [r7, #4]
   443f4:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   443f8:	d807      	bhi.n	4440a <c_indirect_tsf_recording+0x66>
   443fa:	69fb      	ldr	r3, [r7, #28]
   443fc:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   44400:	d918      	bls.n	44434 <c_indirect_tsf_recording+0x90>
   44402:	687b      	ldr	r3, [r7, #4]
   44404:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   44408:	d814      	bhi.n	44434 <c_indirect_tsf_recording+0x90>
   4440a:	69bb      	ldr	r3, [r7, #24]
   4440c:	9300      	str	r3, [sp, #0]
   4440e:	f107 030c 	add.w	r3, r7, #12
   44412:	cb0e      	ldmia	r3, {r1, r2, r3}
   44414:	480b      	ldr	r0, [pc, #44]	; (44444 <c_indirect_tsf_recording+0xa0>)
   44416:	5820      	ldr	r0, [r4, r0]
   44418:	f7ff fc54 	bl	43cc4 <push>
   4441c:	4603      	mov	r3, r0
   4441e:	f083 0301 	eor.w	r3, r3, #1
   44422:	b2db      	uxtb	r3, r3
   44424:	2b00      	cmp	r3, #0
   44426:	d005      	beq.n	44434 <c_indirect_tsf_recording+0x90>
   44428:	4b08      	ldr	r3, [pc, #32]	; (4444c <c_indirect_tsf_recording+0xa8>)
   4442a:	447b      	add	r3, pc
   4442c:	4618      	mov	r0, r3
   4442e:	f7cc ebd6 	blx	10bdc <puts@plt>
   44432:	bf00      	nop
   44434:	bf00      	nop
   44436:	3724      	adds	r7, #36	; 0x24
   44438:	46bd      	mov	sp, r7
   4443a:	bd90      	pop	{r4, r7, pc}
   4443c:	00012c4e 	andeq	r2, r1, lr, asr #24
   44440:	000000ac 	andeq	r0, r0, ip, lsr #1
   44444:	000000c8 	andeq	r0, r0, r8, asr #1
   44448:	000000d4 	ldrdeq	r0, [r0], -r4
   4444c:	0000254e 	andeq	r2, r0, lr, asr #10

00044450 <c_tsf_bx_lr_recording>:
   44450:	b590      	push	{r4, r7, lr}
   44452:	b08b      	sub	sp, #44	; 0x2c
   44454:	af02      	add	r7, sp, #8
   44456:	6078      	str	r0, [r7, #4]
   44458:	4c2e      	ldr	r4, [pc, #184]	; (44514 <c_tsf_bx_lr_recording+0xc4>)
   4445a:	447c      	add	r4, pc
   4445c:	4b2e      	ldr	r3, [pc, #184]	; (44518 <c_tsf_bx_lr_recording+0xc8>)
   4445e:	58e3      	ldr	r3, [r4, r3]
   44460:	681b      	ldr	r3, [r3, #0]
   44462:	2b00      	cmp	r3, #0
   44464:	d109      	bne.n	4447a <c_tsf_bx_lr_recording+0x2a>
   44466:	4b2c      	ldr	r3, [pc, #176]	; (44518 <c_tsf_bx_lr_recording+0xc8>)
   44468:	58e3      	ldr	r3, [r4, r3]
   4446a:	461a      	mov	r2, r3
   4446c:	2301      	movs	r3, #1
   4446e:	6013      	str	r3, [r2, #0]
   44470:	4b2a      	ldr	r3, [pc, #168]	; (4451c <c_tsf_bx_lr_recording+0xcc>)
   44472:	58e3      	ldr	r3, [r4, r3]
   44474:	4618      	mov	r0, r3
   44476:	f7ff fd16 	bl	43ea6 <ringbuffer_init>
   4447a:	f7ff fd37 	bl	43eec <read_r8>
   4447e:	61f8      	str	r0, [r7, #28]
   44480:	687b      	ldr	r3, [r7, #4]
   44482:	60fb      	str	r3, [r7, #12]
   44484:	69fb      	ldr	r3, [r7, #28]
   44486:	613b      	str	r3, [r7, #16]
   44488:	4b25      	ldr	r3, [pc, #148]	; (44520 <c_tsf_bx_lr_recording+0xd0>)
   4448a:	58e3      	ldr	r3, [r4, r3]
   4448c:	681b      	ldr	r3, [r3, #0]
   4448e:	2b00      	cmp	r3, #0
   44490:	d03c      	beq.n	4450c <c_tsf_bx_lr_recording+0xbc>
   44492:	69fb      	ldr	r3, [r7, #28]
   44494:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   44498:	d919      	bls.n	444ce <c_tsf_bx_lr_recording+0x7e>
   4449a:	687b      	ldr	r3, [r7, #4]
   4449c:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   444a0:	d815      	bhi.n	444ce <c_tsf_bx_lr_recording+0x7e>
   444a2:	2303      	movs	r3, #3
   444a4:	763b      	strb	r3, [r7, #24]
   444a6:	69bb      	ldr	r3, [r7, #24]
   444a8:	9300      	str	r3, [sp, #0]
   444aa:	f107 030c 	add.w	r3, r7, #12
   444ae:	cb0e      	ldmia	r3, {r1, r2, r3}
   444b0:	481a      	ldr	r0, [pc, #104]	; (4451c <c_tsf_bx_lr_recording+0xcc>)
   444b2:	5820      	ldr	r0, [r4, r0]
   444b4:	f7ff fc06 	bl	43cc4 <push>
   444b8:	4603      	mov	r3, r0
   444ba:	f083 0301 	eor.w	r3, r3, #1
   444be:	b2db      	uxtb	r3, r3
   444c0:	2b00      	cmp	r3, #0
   444c2:	d004      	beq.n	444ce <c_tsf_bx_lr_recording+0x7e>
   444c4:	4b17      	ldr	r3, [pc, #92]	; (44524 <c_tsf_bx_lr_recording+0xd4>)
   444c6:	447b      	add	r3, pc
   444c8:	4618      	mov	r0, r3
   444ca:	f7cc eb88 	blx	10bdc <puts@plt>
   444ce:	69fb      	ldr	r3, [r7, #28]
   444d0:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   444d4:	d81a      	bhi.n	4450c <c_tsf_bx_lr_recording+0xbc>
   444d6:	687b      	ldr	r3, [r7, #4]
   444d8:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   444dc:	d916      	bls.n	4450c <c_tsf_bx_lr_recording+0xbc>
   444de:	230a      	movs	r3, #10
   444e0:	763b      	strb	r3, [r7, #24]
   444e2:	69bb      	ldr	r3, [r7, #24]
   444e4:	9300      	str	r3, [sp, #0]
   444e6:	f107 030c 	add.w	r3, r7, #12
   444ea:	cb0e      	ldmia	r3, {r1, r2, r3}
   444ec:	480b      	ldr	r0, [pc, #44]	; (4451c <c_tsf_bx_lr_recording+0xcc>)
   444ee:	5820      	ldr	r0, [r4, r0]
   444f0:	f7ff fbe8 	bl	43cc4 <push>
   444f4:	4603      	mov	r3, r0
   444f6:	f083 0301 	eor.w	r3, r3, #1
   444fa:	b2db      	uxtb	r3, r3
   444fc:	2b00      	cmp	r3, #0
   444fe:	d005      	beq.n	4450c <c_tsf_bx_lr_recording+0xbc>
   44500:	4b09      	ldr	r3, [pc, #36]	; (44528 <c_tsf_bx_lr_recording+0xd8>)
   44502:	447b      	add	r3, pc
   44504:	4618      	mov	r0, r3
   44506:	f7cc eb6a 	blx	10bdc <puts@plt>
   4450a:	bf00      	nop
   4450c:	bf00      	nop
   4450e:	3724      	adds	r7, #36	; 0x24
   44510:	46bd      	mov	sp, r7
   44512:	bd90      	pop	{r4, r7, pc}
   44514:	00012ba2 	andeq	r2, r1, r2, lsr #23
   44518:	000000ac 	andeq	r0, r0, ip, lsr #1
   4451c:	000000c8 	andeq	r0, r0, r8, asr #1
   44520:	000000d4 	ldrdeq	r0, [r0], -r4
   44524:	000024b2 			; <UNDEFINED> instruction: 0x000024b2
   44528:	00002476 	andeq	r2, r0, r6, ror r4

0004452c <c_tsf_pop_pc_recording>:
   4452c:	b590      	push	{r4, r7, lr}
   4452e:	b08b      	sub	sp, #44	; 0x2c
   44530:	af02      	add	r7, sp, #8
   44532:	6078      	str	r0, [r7, #4]
   44534:	4c3d      	ldr	r4, [pc, #244]	; (4462c <c_tsf_pop_pc_recording+0x100>)
   44536:	447c      	add	r4, pc
   44538:	4b3d      	ldr	r3, [pc, #244]	; (44630 <c_tsf_pop_pc_recording+0x104>)
   4453a:	58e3      	ldr	r3, [r4, r3]
   4453c:	681b      	ldr	r3, [r3, #0]
   4453e:	2b00      	cmp	r3, #0
   44540:	d109      	bne.n	44556 <c_tsf_pop_pc_recording+0x2a>
   44542:	4b3b      	ldr	r3, [pc, #236]	; (44630 <c_tsf_pop_pc_recording+0x104>)
   44544:	58e3      	ldr	r3, [r4, r3]
   44546:	461a      	mov	r2, r3
   44548:	2301      	movs	r3, #1
   4454a:	6013      	str	r3, [r2, #0]
   4454c:	4b39      	ldr	r3, [pc, #228]	; (44634 <c_tsf_pop_pc_recording+0x108>)
   4454e:	58e3      	ldr	r3, [r4, r3]
   44550:	4618      	mov	r0, r3
   44552:	f7ff fca8 	bl	43ea6 <ringbuffer_init>
   44556:	f7ff fcc9 	bl	43eec <read_r8>
   4455a:	61f8      	str	r0, [r7, #28]
   4455c:	687b      	ldr	r3, [r7, #4]
   4455e:	60fb      	str	r3, [r7, #12]
   44560:	69fb      	ldr	r3, [r7, #28]
   44562:	613b      	str	r3, [r7, #16]
   44564:	4b34      	ldr	r3, [pc, #208]	; (44638 <c_tsf_pop_pc_recording+0x10c>)
   44566:	58e3      	ldr	r3, [r4, r3]
   44568:	681b      	ldr	r3, [r3, #0]
   4456a:	2b00      	cmp	r3, #0
   4456c:	d05a      	beq.n	44624 <c_tsf_pop_pc_recording+0xf8>
   4456e:	69fb      	ldr	r3, [r7, #28]
   44570:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   44574:	d219      	bcs.n	445aa <c_tsf_pop_pc_recording+0x7e>
   44576:	687b      	ldr	r3, [r7, #4]
   44578:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   4457c:	d315      	bcc.n	445aa <c_tsf_pop_pc_recording+0x7e>
   4457e:	2303      	movs	r3, #3
   44580:	763b      	strb	r3, [r7, #24]
   44582:	69bb      	ldr	r3, [r7, #24]
   44584:	9300      	str	r3, [sp, #0]
   44586:	f107 030c 	add.w	r3, r7, #12
   4458a:	cb0e      	ldmia	r3, {r1, r2, r3}
   4458c:	4829      	ldr	r0, [pc, #164]	; (44634 <c_tsf_pop_pc_recording+0x108>)
   4458e:	5820      	ldr	r0, [r4, r0]
   44590:	f7ff fb98 	bl	43cc4 <push>
   44594:	4603      	mov	r3, r0
   44596:	f083 0301 	eor.w	r3, r3, #1
   4459a:	b2db      	uxtb	r3, r3
   4459c:	2b00      	cmp	r3, #0
   4459e:	d004      	beq.n	445aa <c_tsf_pop_pc_recording+0x7e>
   445a0:	4b26      	ldr	r3, [pc, #152]	; (4463c <c_tsf_pop_pc_recording+0x110>)
   445a2:	447b      	add	r3, pc
   445a4:	4618      	mov	r0, r3
   445a6:	f7cc eb1a 	blx	10bdc <puts@plt>
   445aa:	69fb      	ldr	r3, [r7, #28]
   445ac:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   445b0:	d319      	bcc.n	445e6 <c_tsf_pop_pc_recording+0xba>
   445b2:	687b      	ldr	r3, [r7, #4]
   445b4:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   445b8:	d215      	bcs.n	445e6 <c_tsf_pop_pc_recording+0xba>
   445ba:	230a      	movs	r3, #10
   445bc:	763b      	strb	r3, [r7, #24]
   445be:	69bb      	ldr	r3, [r7, #24]
   445c0:	9300      	str	r3, [sp, #0]
   445c2:	f107 030c 	add.w	r3, r7, #12
   445c6:	cb0e      	ldmia	r3, {r1, r2, r3}
   445c8:	481a      	ldr	r0, [pc, #104]	; (44634 <c_tsf_pop_pc_recording+0x108>)
   445ca:	5820      	ldr	r0, [r4, r0]
   445cc:	f7ff fb7a 	bl	43cc4 <push>
   445d0:	4603      	mov	r3, r0
   445d2:	f083 0301 	eor.w	r3, r3, #1
   445d6:	b2db      	uxtb	r3, r3
   445d8:	2b00      	cmp	r3, #0
   445da:	d004      	beq.n	445e6 <c_tsf_pop_pc_recording+0xba>
   445dc:	4b18      	ldr	r3, [pc, #96]	; (44640 <c_tsf_pop_pc_recording+0x114>)
   445de:	447b      	add	r3, pc
   445e0:	4618      	mov	r0, r3
   445e2:	f7cc eafc 	blx	10bdc <puts@plt>
   445e6:	69fb      	ldr	r3, [r7, #28]
   445e8:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   445ec:	d81a      	bhi.n	44624 <c_tsf_pop_pc_recording+0xf8>
   445ee:	687b      	ldr	r3, [r7, #4]
   445f0:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   445f4:	d316      	bcc.n	44624 <c_tsf_pop_pc_recording+0xf8>
   445f6:	2303      	movs	r3, #3
   445f8:	763b      	strb	r3, [r7, #24]
   445fa:	69bb      	ldr	r3, [r7, #24]
   445fc:	9300      	str	r3, [sp, #0]
   445fe:	f107 030c 	add.w	r3, r7, #12
   44602:	cb0e      	ldmia	r3, {r1, r2, r3}
   44604:	480b      	ldr	r0, [pc, #44]	; (44634 <c_tsf_pop_pc_recording+0x108>)
   44606:	5820      	ldr	r0, [r4, r0]
   44608:	f7ff fb5c 	bl	43cc4 <push>
   4460c:	4603      	mov	r3, r0
   4460e:	f083 0301 	eor.w	r3, r3, #1
   44612:	b2db      	uxtb	r3, r3
   44614:	2b00      	cmp	r3, #0
   44616:	d005      	beq.n	44624 <c_tsf_pop_pc_recording+0xf8>
   44618:	4b0a      	ldr	r3, [pc, #40]	; (44644 <c_tsf_pop_pc_recording+0x118>)
   4461a:	447b      	add	r3, pc
   4461c:	4618      	mov	r0, r3
   4461e:	f7cc eade 	blx	10bdc <puts@plt>
   44622:	bf00      	nop
   44624:	bf00      	nop
   44626:	3724      	adds	r7, #36	; 0x24
   44628:	46bd      	mov	sp, r7
   4462a:	bd90      	pop	{r4, r7, pc}
   4462c:	00012ac6 	andeq	r2, r1, r6, asr #21
   44630:	000000ac 	andeq	r0, r0, ip, lsr #1
   44634:	000000c8 	andeq	r0, r0, r8, asr #1
   44638:	000000d4 	ldrdeq	r0, [r0], -r4
   4463c:	000023d6 	ldrdeq	r2, [r0], -r6
   44640:	0000239a 	muleq	r0, sl, r3
   44644:	0000235e 	andeq	r2, r0, lr, asr r3

00044648 <cfv_icall_blx>:
   44648:	b590      	push	{r4, r7, lr}
   4464a:	b08b      	sub	sp, #44	; 0x2c
   4464c:	af02      	add	r7, sp, #8
   4464e:	6078      	str	r0, [r7, #4]
   44650:	4c21      	ldr	r4, [pc, #132]	; (446d8 <cfv_icall_blx+0x90>)
   44652:	447c      	add	r4, pc
   44654:	4b21      	ldr	r3, [pc, #132]	; (446dc <cfv_icall_blx+0x94>)
   44656:	58e3      	ldr	r3, [r4, r3]
   44658:	681b      	ldr	r3, [r3, #0]
   4465a:	2b00      	cmp	r3, #0
   4465c:	d109      	bne.n	44672 <cfv_icall_blx+0x2a>
   4465e:	4b1f      	ldr	r3, [pc, #124]	; (446dc <cfv_icall_blx+0x94>)
   44660:	58e3      	ldr	r3, [r4, r3]
   44662:	461a      	mov	r2, r3
   44664:	2301      	movs	r3, #1
   44666:	6013      	str	r3, [r2, #0]
   44668:	4b1d      	ldr	r3, [pc, #116]	; (446e0 <cfv_icall_blx+0x98>)
   4466a:	58e3      	ldr	r3, [r4, r3]
   4466c:	4618      	mov	r0, r3
   4466e:	f7ff fc1a 	bl	43ea6 <ringbuffer_init>
   44672:	f7ff fc3b 	bl	43eec <read_r8>
   44676:	61f8      	str	r0, [r7, #28]
   44678:	687b      	ldr	r3, [r7, #4]
   4467a:	60fb      	str	r3, [r7, #12]
   4467c:	69fb      	ldr	r3, [r7, #28]
   4467e:	613b      	str	r3, [r7, #16]
   44680:	4b18      	ldr	r3, [pc, #96]	; (446e4 <cfv_icall_blx+0x9c>)
   44682:	58e3      	ldr	r3, [r4, r3]
   44684:	681b      	ldr	r3, [r3, #0]
   44686:	2b00      	cmp	r3, #0
   44688:	d021      	beq.n	446ce <cfv_icall_blx+0x86>
   4468a:	69fb      	ldr	r3, [r7, #28]
   4468c:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   44690:	d906      	bls.n	446a0 <cfv_icall_blx+0x58>
   44692:	687b      	ldr	r3, [r7, #4]
   44694:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   44698:	d802      	bhi.n	446a0 <cfv_icall_blx+0x58>
   4469a:	230a      	movs	r3, #10
   4469c:	763b      	strb	r3, [r7, #24]
   4469e:	e001      	b.n	446a4 <cfv_icall_blx+0x5c>
   446a0:	2301      	movs	r3, #1
   446a2:	763b      	strb	r3, [r7, #24]
   446a4:	69bb      	ldr	r3, [r7, #24]
   446a6:	9300      	str	r3, [sp, #0]
   446a8:	f107 030c 	add.w	r3, r7, #12
   446ac:	cb0e      	ldmia	r3, {r1, r2, r3}
   446ae:	480c      	ldr	r0, [pc, #48]	; (446e0 <cfv_icall_blx+0x98>)
   446b0:	5820      	ldr	r0, [r4, r0]
   446b2:	f7ff fb07 	bl	43cc4 <push>
   446b6:	4603      	mov	r3, r0
   446b8:	f083 0301 	eor.w	r3, r3, #1
   446bc:	b2db      	uxtb	r3, r3
   446be:	2b00      	cmp	r3, #0
   446c0:	d005      	beq.n	446ce <cfv_icall_blx+0x86>
   446c2:	4b09      	ldr	r3, [pc, #36]	; (446e8 <cfv_icall_blx+0xa0>)
   446c4:	447b      	add	r3, pc
   446c6:	4618      	mov	r0, r3
   446c8:	f7cc ea88 	blx	10bdc <puts@plt>
   446cc:	bf00      	nop
   446ce:	bf00      	nop
   446d0:	3724      	adds	r7, #36	; 0x24
   446d2:	46bd      	mov	sp, r7
   446d4:	bd90      	pop	{r4, r7, pc}
   446d6:	bf00      	nop
   446d8:	000129aa 	andeq	r2, r1, sl, lsr #19
   446dc:	000000ac 	andeq	r0, r0, ip, lsr #1
   446e0:	000000c8 	andeq	r0, r0, r8, asr #1
   446e4:	000000d4 	ldrdeq	r0, [r0], -r4
   446e8:	000022b4 			; <UNDEFINED> instruction: 0x000022b4

000446ec <cfv_icall_blx_pre>:
   446ec:	b590      	push	{r4, r7, lr}
   446ee:	b08d      	sub	sp, #52	; 0x34
   446f0:	af02      	add	r7, sp, #8
   446f2:	60f8      	str	r0, [r7, #12]
   446f4:	60b9      	str	r1, [r7, #8]
   446f6:	607a      	str	r2, [r7, #4]
   446f8:	4c3e      	ldr	r4, [pc, #248]	; (447f4 <cfv_icall_blx_pre+0x108>)
   446fa:	447c      	add	r4, pc
   446fc:	68b9      	ldr	r1, [r7, #8]
   446fe:	6878      	ldr	r0, [r7, #4]
   44700:	f7ff fc50 	bl	43fa4 <isBranchTaken>
   44704:	4603      	mov	r3, r0
   44706:	f887 3027 	strb.w	r3, [r7, #39]	; 0x27
   4470a:	f7ff fbef 	bl	43eec <read_r8>
   4470e:	6238      	str	r0, [r7, #32]
   44710:	68fb      	ldr	r3, [r7, #12]
   44712:	613b      	str	r3, [r7, #16]
   44714:	f897 3027 	ldrb.w	r3, [r7, #39]	; 0x27
   44718:	617b      	str	r3, [r7, #20]
   4471a:	68bb      	ldr	r3, [r7, #8]
   4471c:	61bb      	str	r3, [r7, #24]
   4471e:	2304      	movs	r3, #4
   44720:	773b      	strb	r3, [r7, #28]
   44722:	4b35      	ldr	r3, [pc, #212]	; (447f8 <cfv_icall_blx_pre+0x10c>)
   44724:	58e3      	ldr	r3, [r4, r3]
   44726:	681b      	ldr	r3, [r3, #0]
   44728:	2b00      	cmp	r3, #0
   4472a:	d05f      	beq.n	447ec <cfv_icall_blx_pre+0x100>
   4472c:	69fb      	ldr	r3, [r7, #28]
   4472e:	9300      	str	r3, [sp, #0]
   44730:	f107 0310 	add.w	r3, r7, #16
   44734:	cb0e      	ldmia	r3, {r1, r2, r3}
   44736:	4831      	ldr	r0, [pc, #196]	; (447fc <cfv_icall_blx_pre+0x110>)
   44738:	5820      	ldr	r0, [r4, r0]
   4473a:	f7ff fac3 	bl	43cc4 <push>
   4473e:	4603      	mov	r3, r0
   44740:	f083 0301 	eor.w	r3, r3, #1
   44744:	b2db      	uxtb	r3, r3
   44746:	2b00      	cmp	r3, #0
   44748:	d004      	beq.n	44754 <cfv_icall_blx_pre+0x68>
   4474a:	4b2d      	ldr	r3, [pc, #180]	; (44800 <cfv_icall_blx_pre+0x114>)
   4474c:	447b      	add	r3, pc
   4474e:	4618      	mov	r0, r3
   44750:	f7cc ea44 	blx	10bdc <puts@plt>
   44754:	6a3b      	ldr	r3, [r7, #32]
   44756:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   4475a:	d91f      	bls.n	4479c <cfv_icall_blx_pre+0xb0>
   4475c:	68fb      	ldr	r3, [r7, #12]
   4475e:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   44762:	d81b      	bhi.n	4479c <cfv_icall_blx_pre+0xb0>
   44764:	f897 3027 	ldrb.w	r3, [r7, #39]	; 0x27
   44768:	2b00      	cmp	r3, #0
   4476a:	d03c      	beq.n	447e6 <cfv_icall_blx_pre+0xfa>
   4476c:	230a      	movs	r3, #10
   4476e:	773b      	strb	r3, [r7, #28]
   44770:	6a3b      	ldr	r3, [r7, #32]
   44772:	617b      	str	r3, [r7, #20]
   44774:	69fb      	ldr	r3, [r7, #28]
   44776:	9300      	str	r3, [sp, #0]
   44778:	f107 0310 	add.w	r3, r7, #16
   4477c:	cb0e      	ldmia	r3, {r1, r2, r3}
   4477e:	481f      	ldr	r0, [pc, #124]	; (447fc <cfv_icall_blx_pre+0x110>)
   44780:	5820      	ldr	r0, [r4, r0]
   44782:	f7ff fa9f 	bl	43cc4 <push>
   44786:	4603      	mov	r3, r0
   44788:	f083 0301 	eor.w	r3, r3, #1
   4478c:	b2db      	uxtb	r3, r3
   4478e:	2b00      	cmp	r3, #0
   44790:	d004      	beq.n	4479c <cfv_icall_blx_pre+0xb0>
   44792:	4b1c      	ldr	r3, [pc, #112]	; (44804 <cfv_icall_blx_pre+0x118>)
   44794:	447b      	add	r3, pc
   44796:	4618      	mov	r0, r3
   44798:	f7cc ea20 	blx	10bdc <puts@plt>
   4479c:	6a3b      	ldr	r3, [r7, #32]
   4479e:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   447a2:	d903      	bls.n	447ac <cfv_icall_blx_pre+0xc0>
   447a4:	68fb      	ldr	r3, [r7, #12]
   447a6:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   447aa:	d81f      	bhi.n	447ec <cfv_icall_blx_pre+0x100>
   447ac:	f897 3027 	ldrb.w	r3, [r7, #39]	; 0x27
   447b0:	2b00      	cmp	r3, #0
   447b2:	d01a      	beq.n	447ea <cfv_icall_blx_pre+0xfe>
   447b4:	2301      	movs	r3, #1
   447b6:	773b      	strb	r3, [r7, #28]
   447b8:	6a3b      	ldr	r3, [r7, #32]
   447ba:	617b      	str	r3, [r7, #20]
   447bc:	69fb      	ldr	r3, [r7, #28]
   447be:	9300      	str	r3, [sp, #0]
   447c0:	f107 0310 	add.w	r3, r7, #16
   447c4:	cb0e      	ldmia	r3, {r1, r2, r3}
   447c6:	480d      	ldr	r0, [pc, #52]	; (447fc <cfv_icall_blx_pre+0x110>)
   447c8:	5820      	ldr	r0, [r4, r0]
   447ca:	f7ff fa7b 	bl	43cc4 <push>
   447ce:	4603      	mov	r3, r0
   447d0:	f083 0301 	eor.w	r3, r3, #1
   447d4:	b2db      	uxtb	r3, r3
   447d6:	2b00      	cmp	r3, #0
   447d8:	d008      	beq.n	447ec <cfv_icall_blx_pre+0x100>
   447da:	4b0b      	ldr	r3, [pc, #44]	; (44808 <cfv_icall_blx_pre+0x11c>)
   447dc:	447b      	add	r3, pc
   447de:	4618      	mov	r0, r3
   447e0:	f7cc e9fc 	blx	10bdc <puts@plt>
   447e4:	e002      	b.n	447ec <cfv_icall_blx_pre+0x100>
   447e6:	bf00      	nop
   447e8:	e000      	b.n	447ec <cfv_icall_blx_pre+0x100>
   447ea:	bf00      	nop
   447ec:	372c      	adds	r7, #44	; 0x2c
   447ee:	46bd      	mov	sp, r7
   447f0:	bd90      	pop	{r4, r7, pc}
   447f2:	bf00      	nop
   447f4:	00012902 	andeq	r2, r1, r2, lsl #18
   447f8:	000000d4 	ldrdeq	r0, [r0], -r4
   447fc:	000000c8 	andeq	r0, r0, r8, asr #1
   44800:	0000222c 	andeq	r2, r0, ip, lsr #4
   44804:	000021e4 	andeq	r2, r0, r4, ror #3
   44808:	0000219c 	muleq	r0, ip, r1

0004480c <cfv_icall_bc_blc>:
   4480c:	b590      	push	{r4, r7, lr}
   4480e:	b08d      	sub	sp, #52	; 0x34
   44810:	af02      	add	r7, sp, #8
   44812:	60f8      	str	r0, [r7, #12]
   44814:	60b9      	str	r1, [r7, #8]
   44816:	607a      	str	r2, [r7, #4]
   44818:	4c1f      	ldr	r4, [pc, #124]	; (44898 <cfv_icall_bc_blc+0x8c>)
   4481a:	447c      	add	r4, pc
   4481c:	4b1f      	ldr	r3, [pc, #124]	; (4489c <cfv_icall_bc_blc+0x90>)
   4481e:	58e3      	ldr	r3, [r4, r3]
   44820:	681b      	ldr	r3, [r3, #0]
   44822:	2b00      	cmp	r3, #0
   44824:	d109      	bne.n	4483a <cfv_icall_bc_blc+0x2e>
   44826:	4b1d      	ldr	r3, [pc, #116]	; (4489c <cfv_icall_bc_blc+0x90>)
   44828:	58e3      	ldr	r3, [r4, r3]
   4482a:	461a      	mov	r2, r3
   4482c:	2301      	movs	r3, #1
   4482e:	6013      	str	r3, [r2, #0]
   44830:	4b1b      	ldr	r3, [pc, #108]	; (448a0 <cfv_icall_bc_blc+0x94>)
   44832:	58e3      	ldr	r3, [r4, r3]
   44834:	4618      	mov	r0, r3
   44836:	f7ff fb36 	bl	43ea6 <ringbuffer_init>
   4483a:	68b9      	ldr	r1, [r7, #8]
   4483c:	6878      	ldr	r0, [r7, #4]
   4483e:	f7ff fbb1 	bl	43fa4 <isBranchTaken>
   44842:	4603      	mov	r3, r0
   44844:	f887 3027 	strb.w	r3, [r7, #39]	; 0x27
   44848:	68fb      	ldr	r3, [r7, #12]
   4484a:	617b      	str	r3, [r7, #20]
   4484c:	f897 3027 	ldrb.w	r3, [r7, #39]	; 0x27
   44850:	61bb      	str	r3, [r7, #24]
   44852:	68bb      	ldr	r3, [r7, #8]
   44854:	61fb      	str	r3, [r7, #28]
   44856:	2304      	movs	r3, #4
   44858:	f887 3020 	strb.w	r3, [r7, #32]
   4485c:	4b11      	ldr	r3, [pc, #68]	; (448a4 <cfv_icall_bc_blc+0x98>)
   4485e:	58e3      	ldr	r3, [r4, r3]
   44860:	681b      	ldr	r3, [r3, #0]
   44862:	2b00      	cmp	r3, #0
   44864:	d014      	beq.n	44890 <cfv_icall_bc_blc+0x84>
   44866:	6a3b      	ldr	r3, [r7, #32]
   44868:	9300      	str	r3, [sp, #0]
   4486a:	f107 0314 	add.w	r3, r7, #20
   4486e:	cb0e      	ldmia	r3, {r1, r2, r3}
   44870:	480b      	ldr	r0, [pc, #44]	; (448a0 <cfv_icall_bc_blc+0x94>)
   44872:	5820      	ldr	r0, [r4, r0]
   44874:	f7ff fa26 	bl	43cc4 <push>
   44878:	4603      	mov	r3, r0
   4487a:	f083 0301 	eor.w	r3, r3, #1
   4487e:	b2db      	uxtb	r3, r3
   44880:	2b00      	cmp	r3, #0
   44882:	d005      	beq.n	44890 <cfv_icall_bc_blc+0x84>
   44884:	4b08      	ldr	r3, [pc, #32]	; (448a8 <cfv_icall_bc_blc+0x9c>)
   44886:	447b      	add	r3, pc
   44888:	4618      	mov	r0, r3
   4488a:	f7cc e9a8 	blx	10bdc <puts@plt>
   4488e:	bf00      	nop
   44890:	bf00      	nop
   44892:	372c      	adds	r7, #44	; 0x2c
   44894:	46bd      	mov	sp, r7
   44896:	bd90      	pop	{r4, r7, pc}
   44898:	000127e2 	andeq	r2, r1, r2, ror #15
   4489c:	000000ac 	andeq	r0, r0, ip, lsr #1
   448a0:	000000c8 	andeq	r0, r0, r8, asr #1
   448a4:	000000d4 	ldrdeq	r0, [r0], -r4
   448a8:	000020f2 	strdeq	r2, [r0], -r2	; <UNPREDICTABLE>

000448ac <cfv_icall_ldmia_ret>:
   448ac:	b590      	push	{r4, r7, lr}
   448ae:	b08d      	sub	sp, #52	; 0x34
   448b0:	af02      	add	r7, sp, #8
   448b2:	60f8      	str	r0, [r7, #12]
   448b4:	60b9      	str	r1, [r7, #8]
   448b6:	607a      	str	r2, [r7, #4]
   448b8:	4c1d      	ldr	r4, [pc, #116]	; (44930 <cfv_icall_ldmia_ret+0x84>)
   448ba:	447c      	add	r4, pc
   448bc:	4b1d      	ldr	r3, [pc, #116]	; (44934 <cfv_icall_ldmia_ret+0x88>)
   448be:	58e3      	ldr	r3, [r4, r3]
   448c0:	681b      	ldr	r3, [r3, #0]
   448c2:	2b00      	cmp	r3, #0
   448c4:	d109      	bne.n	448da <cfv_icall_ldmia_ret+0x2e>
   448c6:	4b1b      	ldr	r3, [pc, #108]	; (44934 <cfv_icall_ldmia_ret+0x88>)
   448c8:	58e3      	ldr	r3, [r4, r3]
   448ca:	461a      	mov	r2, r3
   448cc:	2301      	movs	r3, #1
   448ce:	6013      	str	r3, [r2, #0]
   448d0:	4b19      	ldr	r3, [pc, #100]	; (44938 <cfv_icall_ldmia_ret+0x8c>)
   448d2:	58e3      	ldr	r3, [r4, r3]
   448d4:	4618      	mov	r0, r3
   448d6:	f7ff fae6 	bl	43ea6 <ringbuffer_init>
   448da:	f7ff fb07 	bl	43eec <read_r8>
   448de:	6278      	str	r0, [r7, #36]	; 0x24
   448e0:	68fb      	ldr	r3, [r7, #12]
   448e2:	617b      	str	r3, [r7, #20]
   448e4:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   448e6:	61bb      	str	r3, [r7, #24]
   448e8:	68bb      	ldr	r3, [r7, #8]
   448ea:	61fb      	str	r3, [r7, #28]
   448ec:	2303      	movs	r3, #3
   448ee:	f887 3020 	strb.w	r3, [r7, #32]
   448f2:	4b12      	ldr	r3, [pc, #72]	; (4493c <cfv_icall_ldmia_ret+0x90>)
   448f4:	58e3      	ldr	r3, [r4, r3]
   448f6:	681b      	ldr	r3, [r3, #0]
   448f8:	2b00      	cmp	r3, #0
   448fa:	d014      	beq.n	44926 <cfv_icall_ldmia_ret+0x7a>
   448fc:	6a3b      	ldr	r3, [r7, #32]
   448fe:	9300      	str	r3, [sp, #0]
   44900:	f107 0314 	add.w	r3, r7, #20
   44904:	cb0e      	ldmia	r3, {r1, r2, r3}
   44906:	480c      	ldr	r0, [pc, #48]	; (44938 <cfv_icall_ldmia_ret+0x8c>)
   44908:	5820      	ldr	r0, [r4, r0]
   4490a:	f7ff f9db 	bl	43cc4 <push>
   4490e:	4603      	mov	r3, r0
   44910:	f083 0301 	eor.w	r3, r3, #1
   44914:	b2db      	uxtb	r3, r3
   44916:	2b00      	cmp	r3, #0
   44918:	d005      	beq.n	44926 <cfv_icall_ldmia_ret+0x7a>
   4491a:	4b09      	ldr	r3, [pc, #36]	; (44940 <cfv_icall_ldmia_ret+0x94>)
   4491c:	447b      	add	r3, pc
   4491e:	4618      	mov	r0, r3
   44920:	f7cc e95c 	blx	10bdc <puts@plt>
   44924:	bf00      	nop
   44926:	bf00      	nop
   44928:	372c      	adds	r7, #44	; 0x2c
   4492a:	46bd      	mov	sp, r7
   4492c:	bd90      	pop	{r4, r7, pc}
   4492e:	bf00      	nop
   44930:	00012742 	andeq	r2, r1, r2, asr #14
   44934:	000000ac 	andeq	r0, r0, ip, lsr #1
   44938:	000000c8 	andeq	r0, r0, r8, asr #1
   4493c:	000000d4 	ldrdeq	r0, [r0], -r4
   44940:	0000205c 	andeq	r2, r0, ip, asr r0

00044944 <ict_checking>:
   44944:	b480      	push	{r7}
   44946:	b083      	sub	sp, #12
   44948:	af00      	add	r7, sp, #0
   4494a:	6078      	str	r0, [r7, #4]
   4494c:	2300      	movs	r3, #0
   4494e:	4618      	mov	r0, r3
   44950:	370c      	adds	r7, #12
   44952:	46bd      	mov	sp, r7
   44954:	f85d 7b04 	ldr.w	r7, [sp], #4
   44958:	4770      	bx	lr

0004495a <error_found>:
   4495a:	b580      	push	{r7, lr}
   4495c:	af00      	add	r7, sp, #0
   4495e:	4b03      	ldr	r3, [pc, #12]	; (4496c <error_found+0x12>)
   44960:	447b      	add	r3, pc
   44962:	4618      	mov	r0, r3
   44964:	f7cc e93a 	blx	10bdc <puts@plt>
   44968:	bf00      	nop
   4496a:	bd80      	pop	{r7, pc}
   4496c:	00002028 	andeq	r2, r0, r8, lsr #32

00044970 <test_fwd_indirect_tsf>:
   44970:	b580      	push	{r7, lr}
   44972:	af00      	add	r7, sp, #0
   44974:	4a06      	ldr	r2, [pc, #24]	; (44990 <test_fwd_indirect_tsf+0x20>)
   44976:	447a      	add	r2, pc
   44978:	4b06      	ldr	r3, [pc, #24]	; (44994 <test_fwd_indirect_tsf+0x24>)
   4497a:	58d3      	ldr	r3, [r2, r3]
   4497c:	681b      	ldr	r3, [r3, #0]
   4497e:	2b00      	cmp	r3, #0
   44980:	d004      	beq.n	4498c <test_fwd_indirect_tsf+0x1c>
   44982:	4b05      	ldr	r3, [pc, #20]	; (44998 <test_fwd_indirect_tsf+0x28>)
   44984:	447b      	add	r3, pc
   44986:	4618      	mov	r0, r3
   44988:	f7cc e928 	blx	10bdc <puts@plt>
   4498c:	bf00      	nop
   4498e:	bd80      	pop	{r7, pc}
   44990:	00012686 	andeq	r2, r1, r6, lsl #13
   44994:	000000d4 	ldrdeq	r0, [r0], -r4
   44998:	0000202c 	andeq	r2, r0, ip, lsr #32

0004499c <mission_control>:
   4499c:	b598      	push	{r3, r4, r7, lr}
   4499e:	af00      	add	r7, sp, #0
   449a0:	4c1c      	ldr	r4, [pc, #112]	; (44a14 <mission_control+0x78>)
   449a2:	447c      	add	r4, pc
   449a4:	4b1c      	ldr	r3, [pc, #112]	; (44a18 <mission_control+0x7c>)
   449a6:	58e3      	ldr	r3, [r4, r3]
   449a8:	681b      	ldr	r3, [r3, #0]
   449aa:	2b00      	cmp	r3, #0
   449ac:	d104      	bne.n	449b8 <mission_control+0x1c>
   449ae:	4b1b      	ldr	r3, [pc, #108]	; (44a1c <mission_control+0x80>)
   449b0:	58e3      	ldr	r3, [r4, r3]
   449b2:	461a      	mov	r2, r3
   449b4:	2301      	movs	r3, #1
   449b6:	6013      	str	r3, [r2, #0]
   449b8:	4b17      	ldr	r3, [pc, #92]	; (44a18 <mission_control+0x7c>)
   449ba:	58e3      	ldr	r3, [r4, r3]
   449bc:	681b      	ldr	r3, [r3, #0]
   449be:	2b04      	cmp	r3, #4
   449c0:	d104      	bne.n	449cc <mission_control+0x30>
   449c2:	4b17      	ldr	r3, [pc, #92]	; (44a20 <mission_control+0x84>)
   449c4:	58e3      	ldr	r3, [r4, r3]
   449c6:	461a      	mov	r2, r3
   449c8:	2301      	movs	r3, #1
   449ca:	6013      	str	r3, [r2, #0]
   449cc:	4b12      	ldr	r3, [pc, #72]	; (44a18 <mission_control+0x7c>)
   449ce:	58e3      	ldr	r3, [r4, r3]
   449d0:	681b      	ldr	r3, [r3, #0]
   449d2:	2b05      	cmp	r3, #5
   449d4:	d105      	bne.n	449e2 <mission_control+0x46>
   449d6:	4b11      	ldr	r3, [pc, #68]	; (44a1c <mission_control+0x80>)
   449d8:	58e3      	ldr	r3, [r4, r3]
   449da:	461a      	mov	r2, r3
   449dc:	2300      	movs	r3, #0
   449de:	6013      	str	r3, [r2, #0]
   449e0:	e015      	b.n	44a0e <mission_control+0x72>
   449e2:	4b0d      	ldr	r3, [pc, #52]	; (44a18 <mission_control+0x7c>)
   449e4:	58e3      	ldr	r3, [r4, r3]
   449e6:	681b      	ldr	r3, [r3, #0]
   449e8:	2b04      	cmp	r3, #4
   449ea:	dc10      	bgt.n	44a0e <mission_control+0x72>
   449ec:	4b0a      	ldr	r3, [pc, #40]	; (44a18 <mission_control+0x7c>)
   449ee:	58e3      	ldr	r3, [r4, r3]
   449f0:	681b      	ldr	r3, [r3, #0]
   449f2:	4619      	mov	r1, r3
   449f4:	4b0b      	ldr	r3, [pc, #44]	; (44a24 <mission_control+0x88>)
   449f6:	447b      	add	r3, pc
   449f8:	4618      	mov	r0, r3
   449fa:	f7cc e8ae 	blx	10b58 <printf@plt>
   449fe:	4b06      	ldr	r3, [pc, #24]	; (44a18 <mission_control+0x7c>)
   44a00:	58e3      	ldr	r3, [r4, r3]
   44a02:	681b      	ldr	r3, [r3, #0]
   44a04:	3301      	adds	r3, #1
   44a06:	4a04      	ldr	r2, [pc, #16]	; (44a18 <mission_control+0x7c>)
   44a08:	58a2      	ldr	r2, [r4, r2]
   44a0a:	6013      	str	r3, [r2, #0]
   44a0c:	bf00      	nop
   44a0e:	bf00      	nop
   44a10:	bd98      	pop	{r3, r4, r7, pc}
   44a12:	bf00      	nop
   44a14:	0001265a 	andeq	r2, r1, sl, asr r6
   44a18:	000000a4 	andeq	r0, r0, r4, lsr #1
   44a1c:	000000d4 	ldrdeq	r0, [r0], -r4
   44a20:	000000a0 	andeq	r0, r0, r0, lsr #1
   44a24:	00001fe2 	andeq	r1, r0, r2, ror #31

00044a28 <view_switch_to_rd_and_log>:
   44a28:	b590      	push	{r4, r7, lr}
   44a2a:	b089      	sub	sp, #36	; 0x24
   44a2c:	af04      	add	r7, sp, #16
   44a2e:	60f8      	str	r0, [r7, #12]
   44a30:	60b9      	str	r1, [r7, #8]
   44a32:	607a      	str	r2, [r7, #4]
   44a34:	4c54      	ldr	r4, [pc, #336]	; (44b88 <view_switch_to_rd_and_log+0x160>)
   44a36:	447c      	add	r4, pc
   44a38:	4b54      	ldr	r3, [pc, #336]	; (44b8c <view_switch_to_rd_and_log+0x164>)
   44a3a:	58e3      	ldr	r3, [r4, r3]
   44a3c:	681b      	ldr	r3, [r3, #0]
   44a3e:	3301      	adds	r3, #1
   44a40:	4a52      	ldr	r2, [pc, #328]	; (44b8c <view_switch_to_rd_and_log+0x164>)
   44a42:	58a2      	ldr	r2, [r4, r2]
   44a44:	6013      	str	r3, [r2, #0]
   44a46:	4b51      	ldr	r3, [pc, #324]	; (44b8c <view_switch_to_rd_and_log+0x164>)
   44a48:	58e3      	ldr	r3, [r4, r3]
   44a4a:	6819      	ldr	r1, [r3, #0]
   44a4c:	f246 6367 	movw	r3, #26215	; 0x6667
   44a50:	f2c6 6366 	movt	r3, #26214	; 0x6666
   44a54:	fb81 2303 	smull	r2, r3, r1, r3
   44a58:	109a      	asrs	r2, r3, #2
   44a5a:	17cb      	asrs	r3, r1, #31
   44a5c:	1ad2      	subs	r2, r2, r3
   44a5e:	4613      	mov	r3, r2
   44a60:	009b      	lsls	r3, r3, #2
   44a62:	4413      	add	r3, r2
   44a64:	005b      	lsls	r3, r3, #1
   44a66:	1aca      	subs	r2, r1, r3
   44a68:	2a00      	cmp	r2, #0
   44a6a:	f040 8089 	bne.w	44b80 <view_switch_to_rd_and_log+0x158>
   44a6e:	4b48      	ldr	r3, [pc, #288]	; (44b90 <view_switch_to_rd_and_log+0x168>)
   44a70:	58e3      	ldr	r3, [r4, r3]
   44a72:	781b      	ldrb	r3, [r3, #0]
   44a74:	f083 0301 	eor.w	r3, r3, #1
   44a78:	b2db      	uxtb	r3, r3
   44a7a:	2b00      	cmp	r3, #0
   44a7c:	d045      	beq.n	44b0a <view_switch_to_rd_and_log+0xe2>
   44a7e:	4b44      	ldr	r3, [pc, #272]	; (44b90 <view_switch_to_rd_and_log+0x168>)
   44a80:	58e3      	ldr	r3, [r4, r3]
   44a82:	2201      	movs	r2, #1
   44a84:	701a      	strb	r2, [r3, #0]
   44a86:	4b43      	ldr	r3, [pc, #268]	; (44b94 <view_switch_to_rd_and_log+0x16c>)
   44a88:	447b      	add	r3, pc
   44a8a:	4618      	mov	r0, r3
   44a8c:	f7cc e8a6 	blx	10bdc <puts@plt>
   44a90:	4b41      	ldr	r3, [pc, #260]	; (44b98 <view_switch_to_rd_and_log+0x170>)
   44a92:	58e3      	ldr	r3, [r4, r3]
   44a94:	4619      	mov	r1, r3
   44a96:	2000      	movs	r0, #0
   44a98:	f000 fca8 	bl	453ec <TEEC_InitializeContext>
   44a9c:	4602      	mov	r2, r0
   44a9e:	4b3f      	ldr	r3, [pc, #252]	; (44b9c <view_switch_to_rd_and_log+0x174>)
   44aa0:	58e3      	ldr	r3, [r4, r3]
   44aa2:	601a      	str	r2, [r3, #0]
   44aa4:	4b3d      	ldr	r3, [pc, #244]	; (44b9c <view_switch_to_rd_and_log+0x174>)
   44aa6:	58e3      	ldr	r3, [r4, r3]
   44aa8:	681b      	ldr	r3, [r3, #0]
   44aaa:	2b00      	cmp	r3, #0
   44aac:	d009      	beq.n	44ac2 <view_switch_to_rd_and_log+0x9a>
   44aae:	4b3b      	ldr	r3, [pc, #236]	; (44b9c <view_switch_to_rd_and_log+0x174>)
   44ab0:	58e3      	ldr	r3, [r4, r3]
   44ab2:	681b      	ldr	r3, [r3, #0]
   44ab4:	461a      	mov	r2, r3
   44ab6:	4b3a      	ldr	r3, [pc, #232]	; (44ba0 <view_switch_to_rd_and_log+0x178>)
   44ab8:	447b      	add	r3, pc
   44aba:	4619      	mov	r1, r3
   44abc:	2001      	movs	r0, #1
   44abe:	f7cc e8e8 	blx	10c90 <errx@plt>
   44ac2:	4b38      	ldr	r3, [pc, #224]	; (44ba4 <view_switch_to_rd_and_log+0x17c>)
   44ac4:	58e3      	ldr	r3, [r4, r3]
   44ac6:	9302      	str	r3, [sp, #8]
   44ac8:	2300      	movs	r3, #0
   44aca:	9301      	str	r3, [sp, #4]
   44acc:	2300      	movs	r3, #0
   44ace:	9300      	str	r3, [sp, #0]
   44ad0:	2300      	movs	r3, #0
   44ad2:	4a35      	ldr	r2, [pc, #212]	; (44ba8 <view_switch_to_rd_and_log+0x180>)
   44ad4:	58a2      	ldr	r2, [r4, r2]
   44ad6:	4935      	ldr	r1, [pc, #212]	; (44bac <view_switch_to_rd_and_log+0x184>)
   44ad8:	5861      	ldr	r1, [r4, r1]
   44ada:	482f      	ldr	r0, [pc, #188]	; (44b98 <view_switch_to_rd_and_log+0x170>)
   44adc:	5820      	ldr	r0, [r4, r0]
   44ade:	f001 f8d6 	bl	45c8e <TEEC_OpenSession>
   44ae2:	4602      	mov	r2, r0
   44ae4:	4b2d      	ldr	r3, [pc, #180]	; (44b9c <view_switch_to_rd_and_log+0x174>)
   44ae6:	58e3      	ldr	r3, [r4, r3]
   44ae8:	601a      	str	r2, [r3, #0]
   44aea:	4b2c      	ldr	r3, [pc, #176]	; (44b9c <view_switch_to_rd_and_log+0x174>)
   44aec:	58e3      	ldr	r3, [r4, r3]
   44aee:	681b      	ldr	r3, [r3, #0]
   44af0:	2b00      	cmp	r3, #0
   44af2:	d00a      	beq.n	44b0a <view_switch_to_rd_and_log+0xe2>
   44af4:	4b29      	ldr	r3, [pc, #164]	; (44b9c <view_switch_to_rd_and_log+0x174>)
   44af6:	58e3      	ldr	r3, [r4, r3]
   44af8:	681a      	ldr	r2, [r3, #0]
   44afa:	4b2a      	ldr	r3, [pc, #168]	; (44ba4 <view_switch_to_rd_and_log+0x17c>)
   44afc:	58e3      	ldr	r3, [r4, r3]
   44afe:	681b      	ldr	r3, [r3, #0]
   44b00:	492b      	ldr	r1, [pc, #172]	; (44bb0 <view_switch_to_rd_and_log+0x188>)
   44b02:	4479      	add	r1, pc
   44b04:	2001      	movs	r0, #1
   44b06:	f7cc e8c4 	blx	10c90 <errx@plt>
   44b0a:	223c      	movs	r2, #60	; 0x3c
   44b0c:	2100      	movs	r1, #0
   44b0e:	4b29      	ldr	r3, [pc, #164]	; (44bb4 <view_switch_to_rd_and_log+0x18c>)
   44b10:	58e3      	ldr	r3, [r4, r3]
   44b12:	4618      	mov	r0, r3
   44b14:	f7cc e8a4 	blx	10c60 <memset@plt>
   44b18:	4b26      	ldr	r3, [pc, #152]	; (44bb4 <view_switch_to_rd_and_log+0x18c>)
   44b1a:	58e3      	ldr	r3, [r4, r3]
   44b1c:	461a      	mov	r2, r3
   44b1e:	2333      	movs	r3, #51	; 0x33
   44b20:	6053      	str	r3, [r2, #4]
   44b22:	68fb      	ldr	r3, [r7, #12]
   44b24:	4a23      	ldr	r2, [pc, #140]	; (44bb4 <view_switch_to_rd_and_log+0x18c>)
   44b26:	58a2      	ldr	r2, [r4, r2]
   44b28:	6093      	str	r3, [r2, #8]
   44b2a:	68bb      	ldr	r3, [r7, #8]
   44b2c:	4a21      	ldr	r2, [pc, #132]	; (44bb4 <view_switch_to_rd_and_log+0x18c>)
   44b2e:	58a2      	ldr	r2, [r4, r2]
   44b30:	60d3      	str	r3, [r2, #12]
   44b32:	687b      	ldr	r3, [r7, #4]
   44b34:	4a1f      	ldr	r2, [pc, #124]	; (44bb4 <view_switch_to_rd_and_log+0x18c>)
   44b36:	58a2      	ldr	r2, [r4, r2]
   44b38:	6153      	str	r3, [r2, #20]
   44b3a:	4b1e      	ldr	r3, [pc, #120]	; (44bb4 <view_switch_to_rd_and_log+0x18c>)
   44b3c:	58e3      	ldr	r3, [r4, r3]
   44b3e:	461a      	mov	r2, r3
   44b40:	f44f 73de 	mov.w	r3, #444	; 0x1bc
   44b44:	6193      	str	r3, [r2, #24]
   44b46:	4b17      	ldr	r3, [pc, #92]	; (44ba4 <view_switch_to_rd_and_log+0x17c>)
   44b48:	58e3      	ldr	r3, [r4, r3]
   44b4a:	4a1a      	ldr	r2, [pc, #104]	; (44bb4 <view_switch_to_rd_and_log+0x18c>)
   44b4c:	58a2      	ldr	r2, [r4, r2]
   44b4e:	2100      	movs	r1, #0
   44b50:	4816      	ldr	r0, [pc, #88]	; (44bac <view_switch_to_rd_and_log+0x184>)
   44b52:	5820      	ldr	r0, [r4, r0]
   44b54:	f001 f99e 	bl	45e94 <TEEC_InvokeCommand>
   44b58:	4602      	mov	r2, r0
   44b5a:	4b10      	ldr	r3, [pc, #64]	; (44b9c <view_switch_to_rd_and_log+0x174>)
   44b5c:	58e3      	ldr	r3, [r4, r3]
   44b5e:	601a      	str	r2, [r3, #0]
   44b60:	4b0e      	ldr	r3, [pc, #56]	; (44b9c <view_switch_to_rd_and_log+0x174>)
   44b62:	58e3      	ldr	r3, [r4, r3]
   44b64:	681b      	ldr	r3, [r3, #0]
   44b66:	2b00      	cmp	r3, #0
   44b68:	d00b      	beq.n	44b82 <view_switch_to_rd_and_log+0x15a>
   44b6a:	4b0c      	ldr	r3, [pc, #48]	; (44b9c <view_switch_to_rd_and_log+0x174>)
   44b6c:	58e3      	ldr	r3, [r4, r3]
   44b6e:	681a      	ldr	r2, [r3, #0]
   44b70:	4b0c      	ldr	r3, [pc, #48]	; (44ba4 <view_switch_to_rd_and_log+0x17c>)
   44b72:	58e3      	ldr	r3, [r4, r3]
   44b74:	681b      	ldr	r3, [r3, #0]
   44b76:	4910      	ldr	r1, [pc, #64]	; (44bb8 <view_switch_to_rd_and_log+0x190>)
   44b78:	4479      	add	r1, pc
   44b7a:	2001      	movs	r0, #1
   44b7c:	f7cc e888 	blx	10c90 <errx@plt>
   44b80:	bf00      	nop
   44b82:	3714      	adds	r7, #20
   44b84:	46bd      	mov	sp, r7
   44b86:	bd90      	pop	{r4, r7, pc}
   44b88:	000125c6 	andeq	r2, r1, r6, asr #11
   44b8c:	000000c0 	andeq	r0, r0, r0, asr #1
   44b90:	000000e8 	andeq	r0, r0, r8, ror #1
   44b94:	00001f6c 	andeq	r1, r0, ip, ror #30
   44b98:	000000a8 	andeq	r0, r0, r8, lsr #1
   44b9c:	000000dc 	ldrdeq	r0, [r0], -ip
   44ba0:	00001f64 	andeq	r1, r0, r4, ror #30
   44ba4:	000000bc 	strheq	r0, [r0], -ip
   44ba8:	000000e4 	andeq	r0, r0, r4, ror #1
   44bac:	000000d0 	ldrdeq	r0, [r0], -r0	; <UNPREDICTABLE>
   44bb0:	00001f4a 	andeq	r1, r0, sl, asr #30
   44bb4:	000000e0 	andeq	r0, r0, r0, ror #1
   44bb8:	00001f08 	andeq	r1, r0, r8, lsl #30

00044bbc <view_switch_to_text_and_log>:
   44bbc:	b598      	push	{r3, r4, r7, lr}
   44bbe:	af00      	add	r7, sp, #0
   44bc0:	4c19      	ldr	r4, [pc, #100]	; (44c28 <view_switch_to_text_and_log+0x6c>)
   44bc2:	447c      	add	r4, pc
   44bc4:	223c      	movs	r2, #60	; 0x3c
   44bc6:	2100      	movs	r1, #0
   44bc8:	4b18      	ldr	r3, [pc, #96]	; (44c2c <view_switch_to_text_and_log+0x70>)
   44bca:	58e3      	ldr	r3, [r4, r3]
   44bcc:	4618      	mov	r0, r3
   44bce:	f7cc e848 	blx	10c60 <memset@plt>
   44bd2:	4b16      	ldr	r3, [pc, #88]	; (44c2c <view_switch_to_text_and_log+0x70>)
   44bd4:	58e3      	ldr	r3, [r4, r3]
   44bd6:	461a      	mov	r2, r3
   44bd8:	2303      	movs	r3, #3
   44bda:	6053      	str	r3, [r2, #4]
   44bdc:	4b13      	ldr	r3, [pc, #76]	; (44c2c <view_switch_to_text_and_log+0x70>)
   44bde:	58e3      	ldr	r3, [r4, r3]
   44be0:	461a      	mov	r2, r3
   44be2:	f64f 73fa 	movw	r3, #65530	; 0xfffa
   44be6:	6093      	str	r3, [r2, #8]
   44be8:	4b11      	ldr	r3, [pc, #68]	; (44c30 <view_switch_to_text_and_log+0x74>)
   44bea:	58e3      	ldr	r3, [r4, r3]
   44bec:	4a0f      	ldr	r2, [pc, #60]	; (44c2c <view_switch_to_text_and_log+0x70>)
   44bee:	58a2      	ldr	r2, [r4, r2]
   44bf0:	2100      	movs	r1, #0
   44bf2:	4810      	ldr	r0, [pc, #64]	; (44c34 <view_switch_to_text_and_log+0x78>)
   44bf4:	5820      	ldr	r0, [r4, r0]
   44bf6:	f001 f94d 	bl	45e94 <TEEC_InvokeCommand>
   44bfa:	4602      	mov	r2, r0
   44bfc:	4b0e      	ldr	r3, [pc, #56]	; (44c38 <view_switch_to_text_and_log+0x7c>)
   44bfe:	58e3      	ldr	r3, [r4, r3]
   44c00:	601a      	str	r2, [r3, #0]
   44c02:	4b0d      	ldr	r3, [pc, #52]	; (44c38 <view_switch_to_text_and_log+0x7c>)
   44c04:	58e3      	ldr	r3, [r4, r3]
   44c06:	681b      	ldr	r3, [r3, #0]
   44c08:	2b00      	cmp	r3, #0
   44c0a:	d00a      	beq.n	44c22 <view_switch_to_text_and_log+0x66>
   44c0c:	4b0a      	ldr	r3, [pc, #40]	; (44c38 <view_switch_to_text_and_log+0x7c>)
   44c0e:	58e3      	ldr	r3, [r4, r3]
   44c10:	681a      	ldr	r2, [r3, #0]
   44c12:	4b07      	ldr	r3, [pc, #28]	; (44c30 <view_switch_to_text_and_log+0x74>)
   44c14:	58e3      	ldr	r3, [r4, r3]
   44c16:	681b      	ldr	r3, [r3, #0]
   44c18:	4908      	ldr	r1, [pc, #32]	; (44c3c <view_switch_to_text_and_log+0x80>)
   44c1a:	4479      	add	r1, pc
   44c1c:	2001      	movs	r0, #1
   44c1e:	f7cc e838 	blx	10c90 <errx@plt>
   44c22:	bf00      	nop
   44c24:	bd98      	pop	{r3, r4, r7, pc}
   44c26:	bf00      	nop
   44c28:	0001243a 	andeq	r2, r1, sl, lsr r4
   44c2c:	000000e0 	andeq	r0, r0, r0, ror #1
   44c30:	000000bc 	strheq	r0, [r0], -ip
   44c34:	000000d0 	ldrdeq	r0, [r0], -r0	; <UNPREDICTABLE>
   44c38:	000000dc 	ldrdeq	r0, [r0], -ip
   44c3c:	00001e66 	andeq	r1, r0, r6, ror #28

00044c40 <__test>:
   44c40:	b480      	push	{r7}
   44c42:	b085      	sub	sp, #20
   44c44:	af00      	add	r7, sp, #0
   44c46:	e9c7 0102 	strd	r0, r1, [r7, #8]
   44c4a:	e9c7 2300 	strd	r2, r3, [r7]
   44c4e:	bf00      	nop
   44c50:	3714      	adds	r7, #20
   44c52:	46bd      	mov	sp, r7
   44c54:	f85d 7b04 	ldr.w	r7, [sp], #4
   44c58:	4770      	bx	lr

00044c5a <__conditional_branch_recording>:
   44c5a:	b480      	push	{r7}
   44c5c:	b083      	sub	sp, #12
   44c5e:	af00      	add	r7, sp, #0
   44c60:	4603      	mov	r3, r0
   44c62:	71fb      	strb	r3, [r7, #7]
   44c64:	bf00      	nop
   44c66:	370c      	adds	r7, #12
   44c68:	46bd      	mov	sp, r7
   44c6a:	f85d 7b04 	ldr.w	r7, [sp], #4
   44c6e:	4770      	bx	lr

00044c70 <__tsf_recording>:
   44c70:	b480      	push	{r7}
   44c72:	b083      	sub	sp, #12
   44c74:	af00      	add	r7, sp, #0
   44c76:	6078      	str	r0, [r7, #4]
   44c78:	6039      	str	r1, [r7, #0]
   44c7a:	bf00      	nop
   44c7c:	370c      	adds	r7, #12
   44c7e:	46bd      	mov	sp, r7
   44c80:	f85d 7b04 	ldr.w	r7, [sp], #4
   44c84:	4770      	bx	lr

00044c86 <write_two_numbers_to_file>:
   44c86:	b580      	push	{r7, lr}
   44c88:	b086      	sub	sp, #24
   44c8a:	af00      	add	r7, sp, #0
   44c8c:	60f8      	str	r0, [r7, #12]
   44c8e:	60b9      	str	r1, [r7, #8]
   44c90:	607a      	str	r2, [r7, #4]
   44c92:	4b0f      	ldr	r3, [pc, #60]	; (44cd0 <write_two_numbers_to_file+0x4a>)
   44c94:	447b      	add	r3, pc
   44c96:	4619      	mov	r1, r3
   44c98:	6878      	ldr	r0, [r7, #4]
   44c9a:	f7cb ef64 	blx	10b64 <fopen@plt>
   44c9e:	6178      	str	r0, [r7, #20]
   44ca0:	697b      	ldr	r3, [r7, #20]
   44ca2:	2b00      	cmp	r3, #0
   44ca4:	d00a      	beq.n	44cbc <write_two_numbers_to_file+0x36>
   44ca6:	68bb      	ldr	r3, [r7, #8]
   44ca8:	68fa      	ldr	r2, [r7, #12]
   44caa:	490a      	ldr	r1, [pc, #40]	; (44cd4 <write_two_numbers_to_file+0x4e>)
   44cac:	4479      	add	r1, pc
   44cae:	6978      	ldr	r0, [r7, #20]
   44cb0:	f7cb efc4 	blx	10c3c <fprintf@plt>
   44cb4:	6978      	ldr	r0, [r7, #20]
   44cb6:	f7cb efe0 	blx	10c78 <fclose@plt>
   44cba:	e005      	b.n	44cc8 <write_two_numbers_to_file+0x42>
   44cbc:	6879      	ldr	r1, [r7, #4]
   44cbe:	4b06      	ldr	r3, [pc, #24]	; (44cd8 <write_two_numbers_to_file+0x52>)
   44cc0:	447b      	add	r3, pc
   44cc2:	4618      	mov	r0, r3
   44cc4:	f7cb ef48 	blx	10b58 <printf@plt>
   44cc8:	bf00      	nop
   44cca:	3718      	adds	r7, #24
   44ccc:	46bd      	mov	sp, r7
   44cce:	bd80      	pop	{r7, pc}
   44cd0:	00001e24 	andeq	r1, r0, r4, lsr #28
   44cd4:	00001e10 	andeq	r1, r0, r0, lsl lr
   44cd8:	00001e04 	andeq	r1, r0, r4, lsl #28

00044cdc <print_hash>:
   44cdc:	b580      	push	{r7, lr}
   44cde:	b084      	sub	sp, #16
   44ce0:	af00      	add	r7, sp, #0
   44ce2:	6078      	str	r0, [r7, #4]
   44ce4:	6039      	str	r1, [r7, #0]
   44ce6:	2300      	movs	r3, #0
   44ce8:	60fb      	str	r3, [r7, #12]
   44cea:	e00c      	b.n	44d06 <print_hash+0x2a>
   44cec:	687a      	ldr	r2, [r7, #4]
   44cee:	68fb      	ldr	r3, [r7, #12]
   44cf0:	4413      	add	r3, r2
   44cf2:	781b      	ldrb	r3, [r3, #0]
   44cf4:	4619      	mov	r1, r3
   44cf6:	4b09      	ldr	r3, [pc, #36]	; (44d1c <print_hash+0x40>)
   44cf8:	447b      	add	r3, pc
   44cfa:	4618      	mov	r0, r3
   44cfc:	f7cb ef2c 	blx	10b58 <printf@plt>
   44d00:	68fb      	ldr	r3, [r7, #12]
   44d02:	3301      	adds	r3, #1
   44d04:	60fb      	str	r3, [r7, #12]
   44d06:	68fa      	ldr	r2, [r7, #12]
   44d08:	683b      	ldr	r3, [r7, #0]
   44d0a:	429a      	cmp	r2, r3
   44d0c:	d3ee      	bcc.n	44cec <print_hash+0x10>
   44d0e:	200a      	movs	r0, #10
   44d10:	f7cb efac 	blx	10c6c <putchar@plt>
   44d14:	bf00      	nop
   44d16:	3710      	adds	r7, #16
   44d18:	46bd      	mov	sp, r7
   44d1a:	bd80      	pop	{r7, pc}
   44d1c:	00001de8 	andeq	r1, r0, r8, ror #27

00044d20 <create_files>:
   44d20:	b580      	push	{r7, lr}
   44d22:	b08c      	sub	sp, #48	; 0x30
   44d24:	af00      	add	r7, sp, #0
   44d26:	60f8      	str	r0, [r7, #12]
   44d28:	60b9      	str	r1, [r7, #8]
   44d2a:	607a      	str	r2, [r7, #4]
   44d2c:	603b      	str	r3, [r7, #0]
   44d2e:	68fb      	ldr	r3, [r7, #12]
   44d30:	617b      	str	r3, [r7, #20]
   44d32:	68bb      	ldr	r3, [r7, #8]
   44d34:	61bb      	str	r3, [r7, #24]
   44d36:	687b      	ldr	r3, [r7, #4]
   44d38:	61fb      	str	r3, [r7, #28]
   44d3a:	683b      	ldr	r3, [r7, #0]
   44d3c:	623b      	str	r3, [r7, #32]
   44d3e:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   44d40:	627b      	str	r3, [r7, #36]	; 0x24
   44d42:	2300      	movs	r3, #0
   44d44:	62fb      	str	r3, [r7, #44]	; 0x2c
   44d46:	e06d      	b.n	44e24 <create_files+0x104>
   44d48:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   44d4a:	009b      	lsls	r3, r3, #2
   44d4c:	f107 0230 	add.w	r2, r7, #48	; 0x30
   44d50:	4413      	add	r3, r2
   44d52:	f853 3c1c 	ldr.w	r3, [r3, #-28]
   44d56:	4a37      	ldr	r2, [pc, #220]	; (44e34 <create_files+0x114>)
   44d58:	447a      	add	r2, pc
   44d5a:	4611      	mov	r1, r2
   44d5c:	4618      	mov	r0, r3
   44d5e:	f7cb ef02 	blx	10b64 <fopen@plt>
   44d62:	62b8      	str	r0, [r7, #40]	; 0x28
   44d64:	6abb      	ldr	r3, [r7, #40]	; 0x28
   44d66:	2b00      	cmp	r3, #0
   44d68:	d02a      	beq.n	44dc0 <create_files+0xa0>
   44d6a:	6ab8      	ldr	r0, [r7, #40]	; 0x28
   44d6c:	f7cb ef84 	blx	10c78 <fclose@plt>
   44d70:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   44d72:	009b      	lsls	r3, r3, #2
   44d74:	f107 0230 	add.w	r2, r7, #48	; 0x30
   44d78:	4413      	add	r3, r2
   44d7a:	f853 3c1c 	ldr.w	r3, [r3, #-28]
   44d7e:	4618      	mov	r0, r3
   44d80:	f7cb ef98 	blx	10cb4 <remove@plt>
   44d84:	4603      	mov	r3, r0
   44d86:	2b00      	cmp	r3, #0
   44d88:	d10d      	bne.n	44da6 <create_files+0x86>
   44d8a:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   44d8c:	009b      	lsls	r3, r3, #2
   44d8e:	f107 0230 	add.w	r2, r7, #48	; 0x30
   44d92:	4413      	add	r3, r2
   44d94:	f853 3c1c 	ldr.w	r3, [r3, #-28]
   44d98:	4619      	mov	r1, r3
   44d9a:	4b27      	ldr	r3, [pc, #156]	; (44e38 <create_files+0x118>)
   44d9c:	447b      	add	r3, pc
   44d9e:	4618      	mov	r0, r3
   44da0:	f7cb eeda 	blx	10b58 <printf@plt>
   44da4:	e00c      	b.n	44dc0 <create_files+0xa0>
   44da6:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   44da8:	009b      	lsls	r3, r3, #2
   44daa:	f107 0230 	add.w	r2, r7, #48	; 0x30
   44dae:	4413      	add	r3, r2
   44db0:	f853 3c1c 	ldr.w	r3, [r3, #-28]
   44db4:	4619      	mov	r1, r3
   44db6:	4b21      	ldr	r3, [pc, #132]	; (44e3c <create_files+0x11c>)
   44db8:	447b      	add	r3, pc
   44dba:	4618      	mov	r0, r3
   44dbc:	f7cb eecc 	blx	10b58 <printf@plt>
   44dc0:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   44dc2:	009b      	lsls	r3, r3, #2
   44dc4:	f107 0230 	add.w	r2, r7, #48	; 0x30
   44dc8:	4413      	add	r3, r2
   44dca:	f853 3c1c 	ldr.w	r3, [r3, #-28]
   44dce:	4a1c      	ldr	r2, [pc, #112]	; (44e40 <create_files+0x120>)
   44dd0:	447a      	add	r2, pc
   44dd2:	4611      	mov	r1, r2
   44dd4:	4618      	mov	r0, r3
   44dd6:	f7cb eec6 	blx	10b64 <fopen@plt>
   44dda:	62b8      	str	r0, [r7, #40]	; 0x28
   44ddc:	6abb      	ldr	r3, [r7, #40]	; 0x28
   44dde:	2b00      	cmp	r3, #0
   44de0:	d010      	beq.n	44e04 <create_files+0xe4>
   44de2:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   44de4:	009b      	lsls	r3, r3, #2
   44de6:	f107 0230 	add.w	r2, r7, #48	; 0x30
   44dea:	4413      	add	r3, r2
   44dec:	f853 3c1c 	ldr.w	r3, [r3, #-28]
   44df0:	4619      	mov	r1, r3
   44df2:	4b14      	ldr	r3, [pc, #80]	; (44e44 <create_files+0x124>)
   44df4:	447b      	add	r3, pc
   44df6:	4618      	mov	r0, r3
   44df8:	f7cb eeae 	blx	10b58 <printf@plt>
   44dfc:	6ab8      	ldr	r0, [r7, #40]	; 0x28
   44dfe:	f7cb ef3c 	blx	10c78 <fclose@plt>
   44e02:	e00c      	b.n	44e1e <create_files+0xfe>
   44e04:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   44e06:	009b      	lsls	r3, r3, #2
   44e08:	f107 0230 	add.w	r2, r7, #48	; 0x30
   44e0c:	4413      	add	r3, r2
   44e0e:	f853 3c1c 	ldr.w	r3, [r3, #-28]
   44e12:	4619      	mov	r1, r3
   44e14:	4b0c      	ldr	r3, [pc, #48]	; (44e48 <create_files+0x128>)
   44e16:	447b      	add	r3, pc
   44e18:	4618      	mov	r0, r3
   44e1a:	f7cb ee9e 	blx	10b58 <printf@plt>
   44e1e:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   44e20:	3301      	adds	r3, #1
   44e22:	62fb      	str	r3, [r7, #44]	; 0x2c
   44e24:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   44e26:	2b04      	cmp	r3, #4
   44e28:	dd8e      	ble.n	44d48 <create_files+0x28>
   44e2a:	bf00      	nop
   44e2c:	3730      	adds	r7, #48	; 0x30
   44e2e:	46bd      	mov	sp, r7
   44e30:	bd80      	pop	{r7, pc}
   44e32:	bf00      	nop
   44e34:	00001d90 	muleq	r0, r0, sp
   44e38:	00001d50 	andeq	r1, r0, r0, asr sp
   44e3c:	00001d58 	andeq	r1, r0, r8, asr sp
   44e40:	00001d60 	andeq	r1, r0, r0, ror #26
   44e44:	00001d40 	andeq	r1, r0, r0, asr #26
   44e48:	00001d42 	andeq	r1, r0, r2, asr #26

00044e4c <read_measurement>:
   44e4c:	b590      	push	{r4, r7, lr}
   44e4e:	b085      	sub	sp, #20
   44e50:	af00      	add	r7, sp, #0
   44e52:	4c4c      	ldr	r4, [pc, #304]	; (44f84 <read_measurement+0x138>)
   44e54:	447c      	add	r4, pc
   44e56:	463b      	mov	r3, r7
   44e58:	4619      	mov	r1, r3
   44e5a:	4b4b      	ldr	r3, [pc, #300]	; (44f88 <read_measurement+0x13c>)
   44e5c:	58e3      	ldr	r3, [r4, r3]
   44e5e:	4618      	mov	r0, r3
   44e60:	f7fe ff91 	bl	43d86 <pop>
   44e64:	4603      	mov	r3, r0
   44e66:	2b00      	cmp	r3, #0
   44e68:	d0f5      	beq.n	44e56 <read_measurement+0xa>
   44e6a:	7b3b      	ldrb	r3, [r7, #12]
   44e6c:	2b01      	cmp	r3, #1
   44e6e:	d807      	bhi.n	44e80 <read_measurement+0x34>
   44e70:	687b      	ldr	r3, [r7, #4]
   44e72:	4a46      	ldr	r2, [pc, #280]	; (44f8c <read_measurement+0x140>)
   44e74:	447a      	add	r2, pc
   44e76:	4611      	mov	r1, r2
   44e78:	4618      	mov	r0, r3
   44e7a:	f000 f8a1 	bl	44fc0 <write_number_to_file>
   44e7e:	e048      	b.n	44f12 <read_measurement+0xc6>
   44e80:	7b3b      	ldrb	r3, [r7, #12]
   44e82:	2b03      	cmp	r3, #3
   44e84:	d830      	bhi.n	44ee8 <read_measurement+0x9c>
   44e86:	4b42      	ldr	r3, [pc, #264]	; (44f90 <read_measurement+0x144>)
   44e88:	58e3      	ldr	r3, [r4, r3]
   44e8a:	681b      	ldr	r3, [r3, #0]
   44e8c:	2b00      	cmp	r3, #0
   44e8e:	d112      	bne.n	44eb6 <read_measurement+0x6a>
   44e90:	4b3f      	ldr	r3, [pc, #252]	; (44f90 <read_measurement+0x144>)
   44e92:	58e3      	ldr	r3, [r4, r3]
   44e94:	461a      	mov	r2, r3
   44e96:	2301      	movs	r3, #1
   44e98:	6013      	str	r3, [r2, #0]
   44e9a:	2120      	movs	r1, #32
   44e9c:	4b3d      	ldr	r3, [pc, #244]	; (44f94 <read_measurement+0x148>)
   44e9e:	58e3      	ldr	r3, [r4, r3]
   44ea0:	4618      	mov	r0, r3
   44ea2:	f7fb ff3d 	bl	40d20 <blake2s_init>
   44ea6:	4603      	mov	r3, r0
   44ea8:	2b00      	cmp	r3, #0
   44eaa:	d004      	beq.n	44eb6 <read_measurement+0x6a>
   44eac:	4b3a      	ldr	r3, [pc, #232]	; (44f98 <read_measurement+0x14c>)
   44eae:	447b      	add	r3, pc
   44eb0:	4618      	mov	r0, r3
   44eb2:	f7cb ee94 	blx	10bdc <puts@plt>
   44eb6:	463b      	mov	r3, r7
   44eb8:	3304      	adds	r3, #4
   44eba:	2204      	movs	r2, #4
   44ebc:	4619      	mov	r1, r3
   44ebe:	4b35      	ldr	r3, [pc, #212]	; (44f94 <read_measurement+0x148>)
   44ec0:	58e3      	ldr	r3, [r4, r3]
   44ec2:	4618      	mov	r0, r3
   44ec4:	f7fe fdd8 	bl	43a78 <blake2s_update>
   44ec8:	4603      	mov	r3, r0
   44eca:	2b00      	cmp	r3, #0
   44ecc:	d004      	beq.n	44ed8 <read_measurement+0x8c>
   44ece:	4b33      	ldr	r3, [pc, #204]	; (44f9c <read_measurement+0x150>)
   44ed0:	447b      	add	r3, pc
   44ed2:	4618      	mov	r0, r3
   44ed4:	f7cb ee82 	blx	10bdc <puts@plt>
   44ed8:	687b      	ldr	r3, [r7, #4]
   44eda:	4619      	mov	r1, r3
   44edc:	4b30      	ldr	r3, [pc, #192]	; (44fa0 <read_measurement+0x154>)
   44ede:	447b      	add	r3, pc
   44ee0:	4618      	mov	r0, r3
   44ee2:	f7cb ee3a 	blx	10b58 <printf@plt>
   44ee6:	e014      	b.n	44f12 <read_measurement+0xc6>
   44ee8:	7b3b      	ldrb	r3, [r7, #12]
   44eea:	2b04      	cmp	r3, #4
   44eec:	d107      	bne.n	44efe <read_measurement+0xb2>
   44eee:	68bb      	ldr	r3, [r7, #8]
   44ef0:	4a2c      	ldr	r2, [pc, #176]	; (44fa4 <read_measurement+0x158>)
   44ef2:	447a      	add	r2, pc
   44ef4:	4611      	mov	r1, r2
   44ef6:	4618      	mov	r0, r3
   44ef8:	f000 f862 	bl	44fc0 <write_number_to_file>
   44efc:	e009      	b.n	44f12 <read_measurement+0xc6>
   44efe:	7b3b      	ldrb	r3, [r7, #12]
   44f00:	2b0a      	cmp	r3, #10
   44f02:	d106      	bne.n	44f12 <read_measurement+0xc6>
   44f04:	683b      	ldr	r3, [r7, #0]
   44f06:	6879      	ldr	r1, [r7, #4]
   44f08:	4a27      	ldr	r2, [pc, #156]	; (44fa8 <read_measurement+0x15c>)
   44f0a:	447a      	add	r2, pc
   44f0c:	4618      	mov	r0, r3
   44f0e:	f7ff feba 	bl	44c86 <write_two_numbers_to_file>
   44f12:	4b1d      	ldr	r3, [pc, #116]	; (44f88 <read_measurement+0x13c>)
   44f14:	58e3      	ldr	r3, [r4, r3]
   44f16:	4618      	mov	r0, r3
   44f18:	f7fe ff9c 	bl	43e54 <is_empty>
   44f1c:	4603      	mov	r3, r0
   44f1e:	2b00      	cmp	r3, #0
   44f20:	d099      	beq.n	44e56 <read_measurement+0xa>
   44f22:	4b22      	ldr	r3, [pc, #136]	; (44fac <read_measurement+0x160>)
   44f24:	58e3      	ldr	r3, [r4, r3]
   44f26:	681b      	ldr	r3, [r3, #0]
   44f28:	2b00      	cmp	r3, #0
   44f2a:	d194      	bne.n	44e56 <read_measurement+0xa>
   44f2c:	4b20      	ldr	r3, [pc, #128]	; (44fb0 <read_measurement+0x164>)
   44f2e:	58e3      	ldr	r3, [r4, r3]
   44f30:	681b      	ldr	r3, [r3, #0]
   44f32:	2b00      	cmp	r3, #0
   44f34:	d08f      	beq.n	44e56 <read_measurement+0xa>
   44f36:	2220      	movs	r2, #32
   44f38:	4b1e      	ldr	r3, [pc, #120]	; (44fb4 <read_measurement+0x168>)
   44f3a:	58e3      	ldr	r3, [r4, r3]
   44f3c:	4619      	mov	r1, r3
   44f3e:	4b15      	ldr	r3, [pc, #84]	; (44f94 <read_measurement+0x148>)
   44f40:	58e3      	ldr	r3, [r4, r3]
   44f42:	4618      	mov	r0, r3
   44f44:	f7fe fdf5 	bl	43b32 <blake2s_final>
   44f48:	4603      	mov	r3, r0
   44f4a:	2b00      	cmp	r3, #0
   44f4c:	d004      	beq.n	44f58 <read_measurement+0x10c>
   44f4e:	4b1a      	ldr	r3, [pc, #104]	; (44fb8 <read_measurement+0x16c>)
   44f50:	447b      	add	r3, pc
   44f52:	4618      	mov	r0, r3
   44f54:	f7cb ee42 	blx	10bdc <puts@plt>
   44f58:	4b18      	ldr	r3, [pc, #96]	; (44fbc <read_measurement+0x170>)
   44f5a:	447b      	add	r3, pc
   44f5c:	461a      	mov	r2, r3
   44f5e:	2120      	movs	r1, #32
   44f60:	4b14      	ldr	r3, [pc, #80]	; (44fb4 <read_measurement+0x168>)
   44f62:	58e3      	ldr	r3, [r4, r3]
   44f64:	4618      	mov	r0, r3
   44f66:	f000 f85d 	bl	45024 <write_array_to_file>
   44f6a:	2120      	movs	r1, #32
   44f6c:	4b11      	ldr	r3, [pc, #68]	; (44fb4 <read_measurement+0x168>)
   44f6e:	58e3      	ldr	r3, [r4, r3]
   44f70:	4618      	mov	r0, r3
   44f72:	f7ff feb3 	bl	44cdc <print_hash>
   44f76:	bf00      	nop
   44f78:	2300      	movs	r3, #0
   44f7a:	4618      	mov	r0, r3
   44f7c:	3714      	adds	r7, #20
   44f7e:	46bd      	mov	sp, r7
   44f80:	bd90      	pop	{r4, r7, pc}
   44f82:	bf00      	nop
   44f84:	000121a8 	andeq	r2, r1, r8, lsr #3
   44f88:	000000c8 	andeq	r0, r0, r8, asr #1
   44f8c:	00001d04 	andeq	r1, r0, r4, lsl #26
   44f90:	000000b4 	strheq	r0, [r0], -r4
   44f94:	000000b0 	strheq	r0, [r0], -r0	; <UNPREDICTABLE>
   44f98:	00001cde 	ldrdeq	r1, [r0], -lr
   44f9c:	00001cdc 	ldrdeq	r1, [r0], -ip
   44fa0:	00001cee 	andeq	r1, r0, lr, ror #25
   44fa4:	00001cf2 	strdeq	r1, [r0], -r2
   44fa8:	00001cee 	andeq	r1, r0, lr, ror #25
   44fac:	000000d4 	ldrdeq	r0, [r0], -r4
   44fb0:	000000a0 	andeq	r0, r0, r0, lsr #1
   44fb4:	000000b8 	strheq	r0, [r0], -r8
   44fb8:	00001cb8 			; <UNDEFINED> instruction: 0x00001cb8
   44fbc:	00001cd2 	ldrdeq	r1, [r0], -r2

00044fc0 <write_number_to_file>:
   44fc0:	b580      	push	{r7, lr}
   44fc2:	b086      	sub	sp, #24
   44fc4:	af00      	add	r7, sp, #0
   44fc6:	6078      	str	r0, [r7, #4]
   44fc8:	6039      	str	r1, [r7, #0]
   44fca:	4b13      	ldr	r3, [pc, #76]	; (45018 <write_number_to_file+0x58>)
   44fcc:	447b      	add	r3, pc
   44fce:	4619      	mov	r1, r3
   44fd0:	6838      	ldr	r0, [r7, #0]
   44fd2:	f7cb edc8 	blx	10b64 <fopen@plt>
   44fd6:	6178      	str	r0, [r7, #20]
   44fd8:	697b      	ldr	r3, [r7, #20]
   44fda:	2b00      	cmp	r3, #0
   44fdc:	d011      	beq.n	45002 <write_number_to_file+0x42>
   44fde:	f107 0308 	add.w	r3, r7, #8
   44fe2:	687a      	ldr	r2, [r7, #4]
   44fe4:	490d      	ldr	r1, [pc, #52]	; (4501c <write_number_to_file+0x5c>)
   44fe6:	4479      	add	r1, pc
   44fe8:	4618      	mov	r0, r3
   44fea:	f7cb ee58 	blx	10c9c <sprintf@plt>
   44fee:	f107 0308 	add.w	r3, r7, #8
   44ff2:	6979      	ldr	r1, [r7, #20]
   44ff4:	4618      	mov	r0, r3
   44ff6:	f7cb ee70 	blx	10cd8 <fputs@plt>
   44ffa:	6978      	ldr	r0, [r7, #20]
   44ffc:	f7cb ee3c 	blx	10c78 <fclose@plt>
   45000:	e005      	b.n	4500e <write_number_to_file+0x4e>
   45002:	6839      	ldr	r1, [r7, #0]
   45004:	4b06      	ldr	r3, [pc, #24]	; (45020 <write_number_to_file+0x60>)
   45006:	447b      	add	r3, pc
   45008:	4618      	mov	r0, r3
   4500a:	f7cb eda6 	blx	10b58 <printf@plt>
   4500e:	bf00      	nop
   45010:	3718      	adds	r7, #24
   45012:	46bd      	mov	sp, r7
   45014:	bd80      	pop	{r7, pc}
   45016:	bf00      	nop
   45018:	00001aec 	andeq	r1, r0, ip, ror #21
   4501c:	00001c5a 	andeq	r1, r0, sl, asr ip
   45020:	00001abe 			; <UNDEFINED> instruction: 0x00001abe

00045024 <write_array_to_file>:
   45024:	b580      	push	{r7, lr}
   45026:	b086      	sub	sp, #24
   45028:	af00      	add	r7, sp, #0
   4502a:	60f8      	str	r0, [r7, #12]
   4502c:	60b9      	str	r1, [r7, #8]
   4502e:	607a      	str	r2, [r7, #4]
   45030:	4b16      	ldr	r3, [pc, #88]	; (4508c <write_array_to_file+0x68>)
   45032:	447b      	add	r3, pc
   45034:	4619      	mov	r1, r3
   45036:	6878      	ldr	r0, [r7, #4]
   45038:	f7cb ed94 	blx	10b64 <fopen@plt>
   4503c:	6138      	str	r0, [r7, #16]
   4503e:	693b      	ldr	r3, [r7, #16]
   45040:	2b00      	cmp	r3, #0
   45042:	d018      	beq.n	45076 <write_array_to_file+0x52>
   45044:	2300      	movs	r3, #0
   45046:	617b      	str	r3, [r7, #20]
   45048:	e00d      	b.n	45066 <write_array_to_file+0x42>
   4504a:	68fa      	ldr	r2, [r7, #12]
   4504c:	697b      	ldr	r3, [r7, #20]
   4504e:	4413      	add	r3, r2
   45050:	781b      	ldrb	r3, [r3, #0]
   45052:	461a      	mov	r2, r3
   45054:	4b0e      	ldr	r3, [pc, #56]	; (45090 <write_array_to_file+0x6c>)
   45056:	447b      	add	r3, pc
   45058:	4619      	mov	r1, r3
   4505a:	6938      	ldr	r0, [r7, #16]
   4505c:	f7cb edee 	blx	10c3c <fprintf@plt>
   45060:	697b      	ldr	r3, [r7, #20]
   45062:	3301      	adds	r3, #1
   45064:	617b      	str	r3, [r7, #20]
   45066:	697a      	ldr	r2, [r7, #20]
   45068:	68bb      	ldr	r3, [r7, #8]
   4506a:	429a      	cmp	r2, r3
   4506c:	d3ed      	bcc.n	4504a <write_array_to_file+0x26>
   4506e:	6938      	ldr	r0, [r7, #16]
   45070:	f7cb ee02 	blx	10c78 <fclose@plt>
   45074:	e005      	b.n	45082 <write_array_to_file+0x5e>
   45076:	6879      	ldr	r1, [r7, #4]
   45078:	4b06      	ldr	r3, [pc, #24]	; (45094 <write_array_to_file+0x70>)
   4507a:	447b      	add	r3, pc
   4507c:	4618      	mov	r0, r3
   4507e:	f7cb ed6c 	blx	10b58 <printf@plt>
   45082:	bf00      	nop
   45084:	3718      	adds	r7, #24
   45086:	46bd      	mov	sp, r7
   45088:	bd80      	pop	{r7, pc}
   4508a:	bf00      	nop
   4508c:	00001c12 	andeq	r1, r0, r2, lsl ip
   45090:	00001bea 	andeq	r1, r0, sl, ror #23
   45094:	00001a4a 	andeq	r1, r0, sl, asr #20

00045098 <start_new_thread>:
   45098:	b590      	push	{r4, r7, lr}
   4509a:	b083      	sub	sp, #12
   4509c:	af02      	add	r7, sp, #8
   4509e:	4c0c      	ldr	r4, [pc, #48]	; (450d0 <start_new_thread+0x38>)
   450a0:	447c      	add	r4, pc
   450a2:	4b0c      	ldr	r3, [pc, #48]	; (450d4 <start_new_thread+0x3c>)
   450a4:	447b      	add	r3, pc
   450a6:	9300      	str	r3, [sp, #0]
   450a8:	4b0b      	ldr	r3, [pc, #44]	; (450d8 <start_new_thread+0x40>)
   450aa:	447b      	add	r3, pc
   450ac:	4a0b      	ldr	r2, [pc, #44]	; (450dc <start_new_thread+0x44>)
   450ae:	447a      	add	r2, pc
   450b0:	490b      	ldr	r1, [pc, #44]	; (450e0 <start_new_thread+0x48>)
   450b2:	4479      	add	r1, pc
   450b4:	480b      	ldr	r0, [pc, #44]	; (450e4 <start_new_thread+0x4c>)
   450b6:	4478      	add	r0, pc
   450b8:	f7ff fe32 	bl	44d20 <create_files>
   450bc:	4b0a      	ldr	r3, [pc, #40]	; (450e8 <start_new_thread+0x50>)
   450be:	58e3      	ldr	r3, [r4, r3]
   450c0:	4618      	mov	r0, r3
   450c2:	f000 f813 	bl	450ec <run_thread>
   450c6:	bf00      	nop
   450c8:	3704      	adds	r7, #4
   450ca:	46bd      	mov	sp, r7
   450cc:	bd90      	pop	{r4, r7, pc}
   450ce:	bf00      	nop
   450d0:	00011f5c 	andeq	r1, r1, ip, asr pc
   450d4:	00001ba4 	andeq	r1, r0, r4, lsr #23
   450d8:	00001b4e 	andeq	r1, r0, lr, asr #22
   450dc:	00001b7e 	andeq	r1, r0, lr, ror fp
   450e0:	00001ac6 	andeq	r1, r0, r6, asr #21
   450e4:	00001b2e 	andeq	r1, r0, lr, lsr #22
   450e8:	000000cc 	andeq	r0, r0, ip, asr #1

000450ec <run_thread>:
   450ec:	b580      	push	{r7, lr}
   450ee:	b084      	sub	sp, #16
   450f0:	af00      	add	r7, sp, #0
   450f2:	6078      	str	r0, [r7, #4]
   450f4:	f107 000c 	add.w	r0, r7, #12
   450f8:	2300      	movs	r3, #0
   450fa:	687a      	ldr	r2, [r7, #4]
   450fc:	2100      	movs	r1, #0
   450fe:	f7cb ed68 	blx	10bd0 <pthread_create@plt>
   45102:	68fb      	ldr	r3, [r7, #12]
   45104:	4618      	mov	r0, r3
   45106:	f7cb ed40 	blx	10b88 <pthread_detach@plt>
   4510a:	bf00      	nop
   4510c:	3710      	adds	r7, #16
   4510e:	46bd      	mov	sp, r7
   45110:	bd80      	pop	{r7, pc}
   45112:	bf00      	nop

00045114 <_start>:
   45114:	f04f 0b00 	mov.w	fp, #0
   45118:	f04f 0e00 	mov.w	lr, #0
   4511c:	bc02      	pop	{r1}
   4511e:	466a      	mov	r2, sp
   45120:	b404      	push	{r2}
   45122:	b401      	push	{r0}
   45124:	f8df c010 	ldr.w	ip, [pc, #16]	; 45138 <_start+0x24>
   45128:	f84d cd04 	str.w	ip, [sp, #-4]!
   4512c:	4803      	ldr	r0, [pc, #12]	; (4513c <_start+0x28>)
   4512e:	4b04      	ldr	r3, [pc, #16]	; (45140 <_start+0x2c>)
   45130:	f7cb ed60 	blx	10bf4 <__libc_start_main@plt>
   45134:	f7cb edd6 	blx	10ce4 <abort@plt>
   45138:	00045235 	andeq	r5, r4, r5, lsr r2
   4513c:	00040748 	andeq	r0, r4, r8, asr #14
   45140:	000451f5 	strdeq	r5, [r4], -r5	; <UNPREDICTABLE>

00045144 <call_weak_fn>:
   45144:	e59f3014 	ldr	r3, [pc, #20]	; 45160 <call_weak_fn+0x1c>
   45148:	e59f2014 	ldr	r2, [pc, #20]	; 45164 <call_weak_fn+0x20>
   4514c:	e08f3003 	add	r3, pc, r3
   45150:	e7932002 	ldr	r2, [r3, r2]
   45154:	e3520000 	cmp	r2, #0
   45158:	012fff1e 	bxeq	lr
   4515c:	eaff2eaa 	b	10c0c <__gmon_start__@plt>
   45160:	00011eac 	andeq	r1, r1, ip, lsr #29
   45164:	000000c4 	andeq	r0, r0, r4, asr #1

00045168 <deregister_tm_clones>:
   45168:	4b07      	ldr	r3, [pc, #28]	; (45188 <deregister_tm_clones+0x20>)
   4516a:	f647 40b0 	movw	r0, #31920	; 0x7cb0
   4516e:	f2c0 0005 	movt	r0, #5
   45172:	1a1b      	subs	r3, r3, r0
   45174:	2b06      	cmp	r3, #6
   45176:	d905      	bls.n	45184 <deregister_tm_clones+0x1c>
   45178:	f240 0300 	movw	r3, #0
   4517c:	f2c0 0300 	movt	r3, #0
   45180:	b103      	cbz	r3, 45184 <deregister_tm_clones+0x1c>
   45182:	4718      	bx	r3
   45184:	4770      	bx	lr
   45186:	bf00      	nop
   45188:	00057cb3 			; <UNDEFINED> instruction: 0x00057cb3

0004518c <register_tm_clones>:
   4518c:	f647 43b0 	movw	r3, #31920	; 0x7cb0
   45190:	f647 40b0 	movw	r0, #31920	; 0x7cb0
   45194:	f2c0 0305 	movt	r3, #5
   45198:	f2c0 0005 	movt	r0, #5
   4519c:	1a19      	subs	r1, r3, r0
   4519e:	1089      	asrs	r1, r1, #2
   451a0:	eb01 71d1 	add.w	r1, r1, r1, lsr #31
   451a4:	1049      	asrs	r1, r1, #1
   451a6:	d005      	beq.n	451b4 <register_tm_clones+0x28>
   451a8:	f240 0300 	movw	r3, #0
   451ac:	f2c0 0300 	movt	r3, #0
   451b0:	b103      	cbz	r3, 451b4 <register_tm_clones+0x28>
   451b2:	4718      	bx	r3
   451b4:	4770      	bx	lr
   451b6:	bf00      	nop

000451b8 <__do_global_dtors_aux>:
   451b8:	b510      	push	{r4, lr}
   451ba:	f647 44d4 	movw	r4, #31956	; 0x7cd4
   451be:	f2c0 0405 	movt	r4, #5
   451c2:	7823      	ldrb	r3, [r4, #0]
   451c4:	b91b      	cbnz	r3, 451ce <__do_global_dtors_aux+0x16>
   451c6:	f7ff ffcf 	bl	45168 <deregister_tm_clones>
   451ca:	2301      	movs	r3, #1
   451cc:	7023      	strb	r3, [r4, #0]
   451ce:	bd10      	pop	{r4, pc}

000451d0 <frame_dummy>:
   451d0:	f646 60fc 	movw	r0, #28412	; 0x6efc
   451d4:	b508      	push	{r3, lr}
   451d6:	f2c0 0005 	movt	r0, #5
   451da:	6803      	ldr	r3, [r0, #0]
   451dc:	b913      	cbnz	r3, 451e4 <frame_dummy+0x14>
   451de:	e8bd 4008 	ldmia.w	sp!, {r3, lr}
   451e2:	e7d3      	b.n	4518c <register_tm_clones>
   451e4:	f240 0300 	movw	r3, #0
   451e8:	f2c0 0300 	movt	r3, #0
   451ec:	2b00      	cmp	r3, #0
   451ee:	d0f6      	beq.n	451de <frame_dummy+0xe>
   451f0:	4798      	blx	r3
   451f2:	e7f4      	b.n	451de <frame_dummy+0xe>

000451f4 <__libc_csu_init>:
   451f4:	e92d 43f8 	stmdb	sp!, {r3, r4, r5, r6, r7, r8, r9, lr}
   451f8:	4607      	mov	r7, r0
   451fa:	4e0c      	ldr	r6, [pc, #48]	; (4522c <__libc_csu_init+0x38>)
   451fc:	4688      	mov	r8, r1
   451fe:	4d0c      	ldr	r5, [pc, #48]	; (45230 <__libc_csu_init+0x3c>)
   45200:	4691      	mov	r9, r2
   45202:	447e      	add	r6, pc
   45204:	f7cb ec8c 	blx	10b20 <_init>
   45208:	447d      	add	r5, pc
   4520a:	1b76      	subs	r6, r6, r5
   4520c:	10b6      	asrs	r6, r6, #2
   4520e:	d00a      	beq.n	45226 <__libc_csu_init+0x32>
   45210:	3d04      	subs	r5, #4
   45212:	2400      	movs	r4, #0
   45214:	f855 3f04 	ldr.w	r3, [r5, #4]!
   45218:	3401      	adds	r4, #1
   4521a:	464a      	mov	r2, r9
   4521c:	4641      	mov	r1, r8
   4521e:	4638      	mov	r0, r7
   45220:	4798      	blx	r3
   45222:	42a6      	cmp	r6, r4
   45224:	d1f6      	bne.n	45214 <__libc_csu_init+0x20>
   45226:	e8bd 83f8 	ldmia.w	sp!, {r3, r4, r5, r6, r7, r8, r9, pc}
   4522a:	bf00      	nop
   4522c:	00011cf2 	strdeq	r1, [r1], -r2
   45230:	00011ce8 	andeq	r1, r1, r8, ror #25

00045234 <__libc_csu_fini>:
   45234:	4770      	bx	lr
   45236:	bf00      	nop

00045238 <bm_timestamp>:
   45238:	b480      	push	{r7}
   4523a:	af00      	add	r7, sp, #0
   4523c:	bf00      	nop
   4523e:	46bd      	mov	sp, r7
   45240:	f85d 7b04 	ldr.w	r7, [sp], #4
   45244:	4770      	bx	lr

00045246 <teec_mutex_lock>:
   45246:	b580      	push	{r7, lr}
   45248:	b082      	sub	sp, #8
   4524a:	af00      	add	r7, sp, #0
   4524c:	6078      	str	r0, [r7, #4]
   4524e:	6878      	ldr	r0, [r7, #4]
   45250:	f7cb ec94 	blx	10b7c <pthread_mutex_lock@plt>
   45254:	bf00      	nop
   45256:	3708      	adds	r7, #8
   45258:	46bd      	mov	sp, r7
   4525a:	bd80      	pop	{r7, pc}

0004525c <teec_mutex_unlock>:
   4525c:	b580      	push	{r7, lr}
   4525e:	b082      	sub	sp, #8
   45260:	af00      	add	r7, sp, #0
   45262:	6078      	str	r0, [r7, #4]
   45264:	6878      	ldr	r0, [r7, #4]
   45266:	f7cb ec6c 	blx	10b40 <pthread_mutex_unlock@plt>
   4526a:	bf00      	nop
   4526c:	3708      	adds	r7, #8
   4526e:	46bd      	mov	sp, r7
   45270:	bd80      	pop	{r7, pc}

00045272 <teec_open_dev>:
   45272:	b580      	push	{r7, lr}
   45274:	b08a      	sub	sp, #40	; 0x28
   45276:	af02      	add	r7, sp, #8
   45278:	60f8      	str	r0, [r7, #12]
   4527a:	60b9      	str	r1, [r7, #8]
   4527c:	607a      	str	r2, [r7, #4]
   4527e:	2102      	movs	r1, #2
   45280:	68f8      	ldr	r0, [r7, #12]
   45282:	f7cb ecca 	blx	10c18 <open@plt>
   45286:	61f8      	str	r0, [r7, #28]
   45288:	69fb      	ldr	r3, [r7, #28]
   4528a:	2b00      	cmp	r3, #0
   4528c:	da02      	bge.n	45294 <teec_open_dev+0x22>
   4528e:	f04f 33ff 	mov.w	r3, #4294967295	; 0xffffffff
   45292:	e042      	b.n	4531a <teec_open_dev+0xa8>
   45294:	f107 0310 	add.w	r3, r7, #16
   45298:	461a      	mov	r2, r3
   4529a:	f44f 4124 	mov.w	r1, #41984	; 0xa400
   4529e:	f2c8 010c 	movt	r1, #32780	; 0x800c
   452a2:	69f8      	ldr	r0, [r7, #28]
   452a4:	f7cb ec82 	blx	10bac <ioctl@plt>
   452a8:	4603      	mov	r3, r0
   452aa:	2b00      	cmp	r3, #0
   452ac:	d00b      	beq.n	452c6 <teec_open_dev+0x54>
   452ae:	4b1d      	ldr	r3, [pc, #116]	; (45324 <teec_open_dev+0xb2>)
   452b0:	447b      	add	r3, pc
   452b2:	9300      	str	r3, [sp, #0]
   452b4:	4b1c      	ldr	r3, [pc, #112]	; (45328 <teec_open_dev+0xb6>)
   452b6:	447b      	add	r3, pc
   452b8:	2201      	movs	r2, #1
   452ba:	214d      	movs	r1, #77	; 0x4d
   452bc:	481b      	ldr	r0, [pc, #108]	; (4532c <teec_open_dev+0xba>)
   452be:	4478      	add	r0, pc
   452c0:	f001 f8d0 	bl	46464 <_dprintf>
   452c4:	e024      	b.n	45310 <teec_open_dev+0x9e>
   452c6:	69bb      	ldr	r3, [r7, #24]
   452c8:	f003 0301 	and.w	r3, r3, #1
   452cc:	2b00      	cmp	r3, #0
   452ce:	d018      	beq.n	45302 <teec_open_dev+0x90>
   452d0:	68bb      	ldr	r3, [r7, #8]
   452d2:	2b00      	cmp	r3, #0
   452d4:	d010      	beq.n	452f8 <teec_open_dev+0x86>
   452d6:	4b16      	ldr	r3, [pc, #88]	; (45330 <teec_open_dev+0xbe>)
   452d8:	447b      	add	r3, pc
   452da:	4619      	mov	r1, r3
   452dc:	68b8      	ldr	r0, [r7, #8]
   452de:	f7cb ec36 	blx	10b4c <strcmp@plt>
   452e2:	4603      	mov	r3, r0
   452e4:	2b00      	cmp	r3, #0
   452e6:	d10e      	bne.n	45306 <teec_open_dev+0x94>
   452e8:	693b      	ldr	r3, [r7, #16]
   452ea:	2b01      	cmp	r3, #1
   452ec:	d10d      	bne.n	4530a <teec_open_dev+0x98>
   452ee:	697b      	ldr	r3, [r7, #20]
   452f0:	f003 0301 	and.w	r3, r3, #1
   452f4:	2b00      	cmp	r3, #0
   452f6:	d00a      	beq.n	4530e <teec_open_dev+0x9c>
   452f8:	69ba      	ldr	r2, [r7, #24]
   452fa:	687b      	ldr	r3, [r7, #4]
   452fc:	601a      	str	r2, [r3, #0]
   452fe:	69fb      	ldr	r3, [r7, #28]
   45300:	e00b      	b.n	4531a <teec_open_dev+0xa8>
   45302:	bf00      	nop
   45304:	e004      	b.n	45310 <teec_open_dev+0x9e>
   45306:	bf00      	nop
   45308:	e002      	b.n	45310 <teec_open_dev+0x9e>
   4530a:	bf00      	nop
   4530c:	e000      	b.n	45310 <teec_open_dev+0x9e>
   4530e:	bf00      	nop
   45310:	69f8      	ldr	r0, [r7, #28]
   45312:	f7cb ecee 	blx	10cf0 <close@plt>
   45316:	f04f 33ff 	mov.w	r3, #4294967295	; 0xffffffff
   4531a:	4618      	mov	r0, r3
   4531c:	3720      	adds	r7, #32
   4531e:	46bd      	mov	sp, r7
   45320:	bd80      	pop	{r7, pc}
   45322:	bf00      	nop
   45324:	000019b8 			; <UNDEFINED> instruction: 0x000019b8
   45328:	000019aa 	andeq	r1, r0, sl, lsr #19
   4532c:	00001a46 	andeq	r1, r0, r6, asr #20
   45330:	000019a8 	andeq	r1, r0, r8, lsr #19

00045334 <teec_shm_alloc>:
   45334:	b590      	push	{r4, r7, lr}
   45336:	b08b      	sub	sp, #44	; 0x2c
   45338:	af00      	add	r7, sp, #0
   4533a:	60f8      	str	r0, [r7, #12]
   4533c:	60b9      	str	r1, [r7, #8]
   4533e:	607a      	str	r2, [r7, #4]
   45340:	f107 0310 	add.w	r3, r7, #16
   45344:	2210      	movs	r2, #16
   45346:	2100      	movs	r1, #0
   45348:	4618      	mov	r0, r3
   4534a:	f7cb ec8a 	blx	10c60 <memset@plt>
   4534e:	68bb      	ldr	r3, [r7, #8]
   45350:	f04f 0400 	mov.w	r4, #0
   45354:	e9c7 3404 	strd	r3, r4, [r7, #16]
   45358:	f107 0310 	add.w	r3, r7, #16
   4535c:	461a      	mov	r2, r3
   4535e:	f24a 4101 	movw	r1, #41985	; 0xa401
   45362:	f2cc 0110 	movt	r1, #49168	; 0xc010
   45366:	68f8      	ldr	r0, [r7, #12]
   45368:	f7cb ec20 	blx	10bac <ioctl@plt>
   4536c:	6278      	str	r0, [r7, #36]	; 0x24
   4536e:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   45370:	2b00      	cmp	r3, #0
   45372:	da02      	bge.n	4537a <teec_shm_alloc+0x46>
   45374:	f04f 33ff 	mov.w	r3, #4294967295	; 0xffffffff
   45378:	e003      	b.n	45382 <teec_shm_alloc+0x4e>
   4537a:	69fa      	ldr	r2, [r7, #28]
   4537c:	687b      	ldr	r3, [r7, #4]
   4537e:	601a      	str	r2, [r3, #0]
   45380:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   45382:	4618      	mov	r0, r3
   45384:	372c      	adds	r7, #44	; 0x2c
   45386:	46bd      	mov	sp, r7
   45388:	bd90      	pop	{r4, r7, pc}

0004538a <teec_shm_register>:
   4538a:	b590      	push	{r4, r7, lr}
   4538c:	b08d      	sub	sp, #52	; 0x34
   4538e:	af00      	add	r7, sp, #0
   45390:	60f8      	str	r0, [r7, #12]
   45392:	60b9      	str	r1, [r7, #8]
   45394:	607a      	str	r2, [r7, #4]
   45396:	603b      	str	r3, [r7, #0]
   45398:	f107 0310 	add.w	r3, r7, #16
   4539c:	2218      	movs	r2, #24
   4539e:	2100      	movs	r1, #0
   453a0:	4618      	mov	r0, r3
   453a2:	f7cb ec5e 	blx	10c60 <memset@plt>
   453a6:	68bb      	ldr	r3, [r7, #8]
   453a8:	f04f 0400 	mov.w	r4, #0
   453ac:	e9c7 3404 	strd	r3, r4, [r7, #16]
   453b0:	687b      	ldr	r3, [r7, #4]
   453b2:	f04f 0400 	mov.w	r4, #0
   453b6:	e9c7 3406 	strd	r3, r4, [r7, #24]
   453ba:	f107 0310 	add.w	r3, r7, #16
   453be:	461a      	mov	r2, r3
   453c0:	f24a 4109 	movw	r1, #41993	; 0xa409
   453c4:	f2cc 0118 	movt	r1, #49176	; 0xc018
   453c8:	68f8      	ldr	r0, [r7, #12]
   453ca:	f7cb ebf0 	blx	10bac <ioctl@plt>
   453ce:	62f8      	str	r0, [r7, #44]	; 0x2c
   453d0:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   453d2:	2b00      	cmp	r3, #0
   453d4:	da02      	bge.n	453dc <teec_shm_register+0x52>
   453d6:	f04f 33ff 	mov.w	r3, #4294967295	; 0xffffffff
   453da:	e003      	b.n	453e4 <teec_shm_register+0x5a>
   453dc:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   453de:	683b      	ldr	r3, [r7, #0]
   453e0:	601a      	str	r2, [r3, #0]
   453e2:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   453e4:	4618      	mov	r0, r3
   453e6:	3734      	adds	r7, #52	; 0x34
   453e8:	46bd      	mov	sp, r7
   453ea:	bd90      	pop	{r4, r7, pc}

000453ec <TEEC_InitializeContext>:
   453ec:	b580      	push	{r7, lr}
   453ee:	f5ad 5d80 	sub.w	sp, sp, #4096	; 0x1000
   453f2:	b086      	sub	sp, #24
   453f4:	af00      	add	r7, sp, #0
   453f6:	f107 0318 	add.w	r3, r7, #24
   453fa:	3b14      	subs	r3, #20
   453fc:	6018      	str	r0, [r3, #0]
   453fe:	f107 0318 	add.w	r3, r7, #24
   45402:	3b18      	subs	r3, #24
   45404:	6019      	str	r1, [r3, #0]
   45406:	f107 0318 	add.w	r3, r7, #24
   4540a:	3b18      	subs	r3, #24
   4540c:	681b      	ldr	r3, [r3, #0]
   4540e:	2b00      	cmp	r3, #0
   45410:	d103      	bne.n	4541a <TEEC_InitializeContext+0x2e>
   45412:	2306      	movs	r3, #6
   45414:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   45418:	e05d      	b.n	454d6 <TEEC_InitializeContext+0xea>
   4541a:	2300      	movs	r3, #0
   4541c:	f507 5280 	add.w	r2, r7, #4096	; 0x1000
   45420:	f102 0214 	add.w	r2, r2, #20
   45424:	6013      	str	r3, [r2, #0]
   45426:	e04c      	b.n	454c2 <TEEC_InitializeContext+0xd6>
   45428:	f107 0018 	add.w	r0, r7, #24
   4542c:	3808      	subs	r0, #8
   4542e:	f507 5380 	add.w	r3, r7, #4096	; 0x1000
   45432:	f103 0314 	add.w	r3, r3, #20
   45436:	681b      	ldr	r3, [r3, #0]
   45438:	4a2a      	ldr	r2, [pc, #168]	; (454e4 <TEEC_InitializeContext+0xf8>)
   4543a:	447a      	add	r2, pc
   4543c:	f44f 5180 	mov.w	r1, #4096	; 0x1000
   45440:	f7cb ec08 	blx	10c54 <snprintf@plt>
   45444:	f107 0218 	add.w	r2, r7, #24
   45448:	3a0c      	subs	r2, #12
   4544a:	f107 0318 	add.w	r3, r7, #24
   4544e:	3b14      	subs	r3, #20
   45450:	f107 0018 	add.w	r0, r7, #24
   45454:	3808      	subs	r0, #8
   45456:	6819      	ldr	r1, [r3, #0]
   45458:	f7ff ff0b 	bl	45272 <teec_open_dev>
   4545c:	f507 5380 	add.w	r3, r7, #4096	; 0x1000
   45460:	f103 0310 	add.w	r3, r3, #16
   45464:	6018      	str	r0, [r3, #0]
   45466:	f507 5380 	add.w	r3, r7, #4096	; 0x1000
   4546a:	f103 0310 	add.w	r3, r3, #16
   4546e:	681b      	ldr	r3, [r3, #0]
   45470:	2b00      	cmp	r3, #0
   45472:	db1b      	blt.n	454ac <TEEC_InitializeContext+0xc0>
   45474:	f107 0318 	add.w	r3, r7, #24
   45478:	3b18      	subs	r3, #24
   4547a:	681b      	ldr	r3, [r3, #0]
   4547c:	f507 5280 	add.w	r2, r7, #4096	; 0x1000
   45480:	f102 0210 	add.w	r2, r2, #16
   45484:	6812      	ldr	r2, [r2, #0]
   45486:	601a      	str	r2, [r3, #0]
   45488:	f107 0318 	add.w	r3, r7, #24
   4548c:	3b0c      	subs	r3, #12
   4548e:	681b      	ldr	r3, [r3, #0]
   45490:	f003 0304 	and.w	r3, r3, #4
   45494:	2b00      	cmp	r3, #0
   45496:	bf14      	ite	ne
   45498:	2301      	movne	r3, #1
   4549a:	2300      	moveq	r3, #0
   4549c:	b2da      	uxtb	r2, r3
   4549e:	f107 0318 	add.w	r3, r7, #24
   454a2:	3b18      	subs	r3, #24
   454a4:	681b      	ldr	r3, [r3, #0]
   454a6:	711a      	strb	r2, [r3, #4]
   454a8:	2300      	movs	r3, #0
   454aa:	e014      	b.n	454d6 <TEEC_InitializeContext+0xea>
   454ac:	f507 5380 	add.w	r3, r7, #4096	; 0x1000
   454b0:	f103 0314 	add.w	r3, r3, #20
   454b4:	681b      	ldr	r3, [r3, #0]
   454b6:	3301      	adds	r3, #1
   454b8:	f507 5280 	add.w	r2, r7, #4096	; 0x1000
   454bc:	f102 0214 	add.w	r2, r2, #20
   454c0:	6013      	str	r3, [r2, #0]
   454c2:	f507 5380 	add.w	r3, r7, #4096	; 0x1000
   454c6:	f103 0314 	add.w	r3, r3, #20
   454ca:	681b      	ldr	r3, [r3, #0]
   454cc:	2b09      	cmp	r3, #9
   454ce:	d9ab      	bls.n	45428 <TEEC_InitializeContext+0x3c>
   454d0:	2308      	movs	r3, #8
   454d2:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   454d6:	4618      	mov	r0, r3
   454d8:	f507 5780 	add.w	r7, r7, #4096	; 0x1000
   454dc:	3718      	adds	r7, #24
   454de:	46bd      	mov	sp, r7
   454e0:	bd80      	pop	{r7, pc}
   454e2:	bf00      	nop
   454e4:	00001852 	andeq	r1, r0, r2, asr r8

000454e8 <TEEC_FinalizeContext>:
   454e8:	b580      	push	{r7, lr}
   454ea:	b082      	sub	sp, #8
   454ec:	af00      	add	r7, sp, #0
   454ee:	6078      	str	r0, [r7, #4]
   454f0:	687b      	ldr	r3, [r7, #4]
   454f2:	2b00      	cmp	r3, #0
   454f4:	d004      	beq.n	45500 <TEEC_FinalizeContext+0x18>
   454f6:	687b      	ldr	r3, [r7, #4]
   454f8:	681b      	ldr	r3, [r3, #0]
   454fa:	4618      	mov	r0, r3
   454fc:	f7cb ebf8 	blx	10cf0 <close@plt>
   45500:	bf00      	nop
   45502:	3708      	adds	r7, #8
   45504:	46bd      	mov	sp, r7
   45506:	bd80      	pop	{r7, pc}

00045508 <teec_pre_process_tmpref>:
   45508:	b590      	push	{r4, r7, lr}
   4550a:	b087      	sub	sp, #28
   4550c:	af00      	add	r7, sp, #0
   4550e:	60f8      	str	r0, [r7, #12]
   45510:	60b9      	str	r1, [r7, #8]
   45512:	607a      	str	r2, [r7, #4]
   45514:	603b      	str	r3, [r7, #0]
   45516:	68bb      	ldr	r3, [r7, #8]
   45518:	2b06      	cmp	r3, #6
   4551a:	d00e      	beq.n	4553a <teec_pre_process_tmpref+0x32>
   4551c:	2b07      	cmp	r3, #7
   4551e:	d017      	beq.n	45550 <teec_pre_process_tmpref+0x48>
   45520:	2b05      	cmp	r3, #5
   45522:	d120      	bne.n	45566 <teec_pre_process_tmpref+0x5e>
   45524:	683a      	ldr	r2, [r7, #0]
   45526:	f04f 0305 	mov.w	r3, #5
   4552a:	f04f 0400 	mov.w	r4, #0
   4552e:	e9c2 3400 	strd	r3, r4, [r2]
   45532:	6abb      	ldr	r3, [r7, #40]	; 0x28
   45534:	2201      	movs	r2, #1
   45536:	609a      	str	r2, [r3, #8]
   45538:	e019      	b.n	4556e <teec_pre_process_tmpref+0x66>
   4553a:	683a      	ldr	r2, [r7, #0]
   4553c:	f04f 0306 	mov.w	r3, #6
   45540:	f04f 0400 	mov.w	r4, #0
   45544:	e9c2 3400 	strd	r3, r4, [r2]
   45548:	6abb      	ldr	r3, [r7, #40]	; 0x28
   4554a:	2202      	movs	r2, #2
   4554c:	609a      	str	r2, [r3, #8]
   4554e:	e00e      	b.n	4556e <teec_pre_process_tmpref+0x66>
   45550:	683a      	ldr	r2, [r7, #0]
   45552:	f04f 0307 	mov.w	r3, #7
   45556:	f04f 0400 	mov.w	r4, #0
   4555a:	e9c2 3400 	strd	r3, r4, [r2]
   4555e:	6abb      	ldr	r3, [r7, #40]	; 0x28
   45560:	2203      	movs	r2, #3
   45562:	609a      	str	r2, [r3, #8]
   45564:	e003      	b.n	4556e <teec_pre_process_tmpref+0x66>
   45566:	2306      	movs	r3, #6
   45568:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   4556c:	e025      	b.n	455ba <teec_pre_process_tmpref+0xb2>
   4556e:	687b      	ldr	r3, [r7, #4]
   45570:	685a      	ldr	r2, [r3, #4]
   45572:	6abb      	ldr	r3, [r7, #40]	; 0x28
   45574:	605a      	str	r2, [r3, #4]
   45576:	6ab9      	ldr	r1, [r7, #40]	; 0x28
   45578:	68f8      	ldr	r0, [r7, #12]
   4557a:	f000 fe86 	bl	4628a <TEEC_AllocateSharedMemory>
   4557e:	6178      	str	r0, [r7, #20]
   45580:	697b      	ldr	r3, [r7, #20]
   45582:	2b00      	cmp	r3, #0
   45584:	d001      	beq.n	4558a <teec_pre_process_tmpref+0x82>
   45586:	697b      	ldr	r3, [r7, #20]
   45588:	e017      	b.n	455ba <teec_pre_process_tmpref+0xb2>
   4558a:	6abb      	ldr	r3, [r7, #40]	; 0x28
   4558c:	6818      	ldr	r0, [r3, #0]
   4558e:	687b      	ldr	r3, [r7, #4]
   45590:	6819      	ldr	r1, [r3, #0]
   45592:	687b      	ldr	r3, [r7, #4]
   45594:	685b      	ldr	r3, [r3, #4]
   45596:	461a      	mov	r2, r3
   45598:	f7cb eafc 	blx	10b94 <memcpy@plt>
   4559c:	687b      	ldr	r3, [r7, #4]
   4559e:	685b      	ldr	r3, [r3, #4]
   455a0:	f04f 0400 	mov.w	r4, #0
   455a4:	683a      	ldr	r2, [r7, #0]
   455a6:	e9c2 3404 	strd	r3, r4, [r2, #16]
   455aa:	6abb      	ldr	r3, [r7, #40]	; 0x28
   455ac:	68db      	ldr	r3, [r3, #12]
   455ae:	ea4f 74e3 	mov.w	r4, r3, asr #31
   455b2:	683a      	ldr	r2, [r7, #0]
   455b4:	e9c2 3406 	strd	r3, r4, [r2, #24]
   455b8:	2300      	movs	r3, #0
   455ba:	4618      	mov	r0, r3
   455bc:	371c      	adds	r7, #28
   455be:	46bd      	mov	sp, r7
   455c0:	bd90      	pop	{r4, r7, pc}

000455c2 <teec_pre_process_whole>:
   455c2:	b590      	push	{r4, r7, lr}
   455c4:	b087      	sub	sp, #28
   455c6:	af00      	add	r7, sp, #0
   455c8:	6078      	str	r0, [r7, #4]
   455ca:	6039      	str	r1, [r7, #0]
   455cc:	2303      	movs	r3, #3
   455ce:	617b      	str	r3, [r7, #20]
   455d0:	687b      	ldr	r3, [r7, #4]
   455d2:	681b      	ldr	r3, [r3, #0]
   455d4:	689a      	ldr	r2, [r3, #8]
   455d6:	697b      	ldr	r3, [r7, #20]
   455d8:	4013      	ands	r3, r2
   455da:	613b      	str	r3, [r7, #16]
   455dc:	693a      	ldr	r2, [r7, #16]
   455de:	697b      	ldr	r3, [r7, #20]
   455e0:	429a      	cmp	r2, r3
   455e2:	d107      	bne.n	455f4 <teec_pre_process_whole+0x32>
   455e4:	683a      	ldr	r2, [r7, #0]
   455e6:	f04f 0307 	mov.w	r3, #7
   455ea:	f04f 0400 	mov.w	r4, #0
   455ee:	e9c2 3400 	strd	r3, r4, [r2]
   455f2:	e01d      	b.n	45630 <teec_pre_process_whole+0x6e>
   455f4:	693b      	ldr	r3, [r7, #16]
   455f6:	f003 0301 	and.w	r3, r3, #1
   455fa:	2b00      	cmp	r3, #0
   455fc:	d007      	beq.n	4560e <teec_pre_process_whole+0x4c>
   455fe:	683a      	ldr	r2, [r7, #0]
   45600:	f04f 0305 	mov.w	r3, #5
   45604:	f04f 0400 	mov.w	r4, #0
   45608:	e9c2 3400 	strd	r3, r4, [r2]
   4560c:	e010      	b.n	45630 <teec_pre_process_whole+0x6e>
   4560e:	693b      	ldr	r3, [r7, #16]
   45610:	f003 0302 	and.w	r3, r3, #2
   45614:	2b00      	cmp	r3, #0
   45616:	d007      	beq.n	45628 <teec_pre_process_whole+0x66>
   45618:	683a      	ldr	r2, [r7, #0]
   4561a:	f04f 0306 	mov.w	r3, #6
   4561e:	f04f 0400 	mov.w	r4, #0
   45622:	e9c2 3400 	strd	r3, r4, [r2]
   45626:	e003      	b.n	45630 <teec_pre_process_whole+0x6e>
   45628:	2306      	movs	r3, #6
   4562a:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   4562e:	e023      	b.n	45678 <teec_pre_process_whole+0xb6>
   45630:	687b      	ldr	r3, [r7, #4]
   45632:	681b      	ldr	r3, [r3, #0]
   45634:	60fb      	str	r3, [r7, #12]
   45636:	68fb      	ldr	r3, [r7, #12]
   45638:	695b      	ldr	r3, [r3, #20]
   4563a:	2b00      	cmp	r3, #0
   4563c:	d00d      	beq.n	4565a <teec_pre_process_whole+0x98>
   4563e:	693b      	ldr	r3, [r7, #16]
   45640:	f003 0301 	and.w	r3, r3, #1
   45644:	2b00      	cmp	r3, #0
   45646:	d008      	beq.n	4565a <teec_pre_process_whole+0x98>
   45648:	68fb      	ldr	r3, [r7, #12]
   4564a:	6958      	ldr	r0, [r3, #20]
   4564c:	68fb      	ldr	r3, [r7, #12]
   4564e:	6819      	ldr	r1, [r3, #0]
   45650:	68fb      	ldr	r3, [r7, #12]
   45652:	685b      	ldr	r3, [r3, #4]
   45654:	461a      	mov	r2, r3
   45656:	f7cb ea9e 	blx	10b94 <memcpy@plt>
   4565a:	68fb      	ldr	r3, [r7, #12]
   4565c:	68db      	ldr	r3, [r3, #12]
   4565e:	ea4f 74e3 	mov.w	r4, r3, asr #31
   45662:	683a      	ldr	r2, [r7, #0]
   45664:	e9c2 3406 	strd	r3, r4, [r2, #24]
   45668:	68fb      	ldr	r3, [r7, #12]
   4566a:	685b      	ldr	r3, [r3, #4]
   4566c:	f04f 0400 	mov.w	r4, #0
   45670:	683a      	ldr	r2, [r7, #0]
   45672:	e9c2 3404 	strd	r3, r4, [r2, #16]
   45676:	2300      	movs	r3, #0
   45678:	4618      	mov	r0, r3
   4567a:	371c      	adds	r7, #28
   4567c:	46bd      	mov	sp, r7
   4567e:	bd90      	pop	{r4, r7, pc}

00045680 <teec_pre_process_partial>:
   45680:	b590      	push	{r4, r7, lr}
   45682:	b087      	sub	sp, #28
   45684:	af00      	add	r7, sp, #0
   45686:	60f8      	str	r0, [r7, #12]
   45688:	60b9      	str	r1, [r7, #8]
   4568a:	607a      	str	r2, [r7, #4]
   4568c:	68fb      	ldr	r3, [r7, #12]
   4568e:	2b0e      	cmp	r3, #14
   45690:	d00d      	beq.n	456ae <teec_pre_process_partial+0x2e>
   45692:	2b0f      	cmp	r3, #15
   45694:	d015      	beq.n	456c2 <teec_pre_process_partial+0x42>
   45696:	2b0d      	cmp	r3, #13
   45698:	d11d      	bne.n	456d6 <teec_pre_process_partial+0x56>
   4569a:	2301      	movs	r3, #1
   4569c:	617b      	str	r3, [r7, #20]
   4569e:	687a      	ldr	r2, [r7, #4]
   456a0:	f04f 0305 	mov.w	r3, #5
   456a4:	f04f 0400 	mov.w	r4, #0
   456a8:	e9c2 3400 	strd	r3, r4, [r2]
   456ac:	e017      	b.n	456de <teec_pre_process_partial+0x5e>
   456ae:	2302      	movs	r3, #2
   456b0:	617b      	str	r3, [r7, #20]
   456b2:	687a      	ldr	r2, [r7, #4]
   456b4:	f04f 0306 	mov.w	r3, #6
   456b8:	f04f 0400 	mov.w	r4, #0
   456bc:	e9c2 3400 	strd	r3, r4, [r2]
   456c0:	e00d      	b.n	456de <teec_pre_process_partial+0x5e>
   456c2:	2303      	movs	r3, #3
   456c4:	617b      	str	r3, [r7, #20]
   456c6:	687a      	ldr	r2, [r7, #4]
   456c8:	f04f 0307 	mov.w	r3, #7
   456cc:	f04f 0400 	mov.w	r4, #0
   456d0:	e9c2 3400 	strd	r3, r4, [r2]
   456d4:	e003      	b.n	456de <teec_pre_process_partial+0x5e>
   456d6:	2306      	movs	r3, #6
   456d8:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   456dc:	e039      	b.n	45752 <teec_pre_process_partial+0xd2>
   456de:	68bb      	ldr	r3, [r7, #8]
   456e0:	681b      	ldr	r3, [r3, #0]
   456e2:	613b      	str	r3, [r7, #16]
   456e4:	693b      	ldr	r3, [r7, #16]
   456e6:	689a      	ldr	r2, [r3, #8]
   456e8:	697b      	ldr	r3, [r7, #20]
   456ea:	401a      	ands	r2, r3
   456ec:	697b      	ldr	r3, [r7, #20]
   456ee:	429a      	cmp	r2, r3
   456f0:	d003      	beq.n	456fa <teec_pre_process_partial+0x7a>
   456f2:	2306      	movs	r3, #6
   456f4:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   456f8:	e02b      	b.n	45752 <teec_pre_process_partial+0xd2>
   456fa:	693b      	ldr	r3, [r7, #16]
   456fc:	695b      	ldr	r3, [r3, #20]
   456fe:	2b00      	cmp	r3, #0
   45700:	d011      	beq.n	45726 <teec_pre_process_partial+0xa6>
   45702:	68fb      	ldr	r3, [r7, #12]
   45704:	2b0e      	cmp	r3, #14
   45706:	d00e      	beq.n	45726 <teec_pre_process_partial+0xa6>
   45708:	693b      	ldr	r3, [r7, #16]
   4570a:	695a      	ldr	r2, [r3, #20]
   4570c:	68bb      	ldr	r3, [r7, #8]
   4570e:	689b      	ldr	r3, [r3, #8]
   45710:	18d0      	adds	r0, r2, r3
   45712:	693b      	ldr	r3, [r7, #16]
   45714:	681a      	ldr	r2, [r3, #0]
   45716:	68bb      	ldr	r3, [r7, #8]
   45718:	689b      	ldr	r3, [r3, #8]
   4571a:	18d1      	adds	r1, r2, r3
   4571c:	68bb      	ldr	r3, [r7, #8]
   4571e:	685b      	ldr	r3, [r3, #4]
   45720:	461a      	mov	r2, r3
   45722:	f7cb ea38 	blx	10b94 <memcpy@plt>
   45726:	693b      	ldr	r3, [r7, #16]
   45728:	68db      	ldr	r3, [r3, #12]
   4572a:	ea4f 74e3 	mov.w	r4, r3, asr #31
   4572e:	687a      	ldr	r2, [r7, #4]
   45730:	e9c2 3406 	strd	r3, r4, [r2, #24]
   45734:	68bb      	ldr	r3, [r7, #8]
   45736:	689b      	ldr	r3, [r3, #8]
   45738:	f04f 0400 	mov.w	r4, #0
   4573c:	687a      	ldr	r2, [r7, #4]
   4573e:	e9c2 3402 	strd	r3, r4, [r2, #8]
   45742:	68bb      	ldr	r3, [r7, #8]
   45744:	685b      	ldr	r3, [r3, #4]
   45746:	f04f 0400 	mov.w	r4, #0
   4574a:	687a      	ldr	r2, [r7, #4]
   4574c:	e9c2 3404 	strd	r3, r4, [r2, #16]
   45750:	2300      	movs	r3, #0
   45752:	4618      	mov	r0, r3
   45754:	371c      	adds	r7, #28
   45756:	46bd      	mov	sp, r7
   45758:	bd90      	pop	{r4, r7, pc}

0004575a <teec_pre_process_operation>:
   4575a:	b590      	push	{r4, r7, lr}
   4575c:	b08b      	sub	sp, #44	; 0x2c
   4575e:	af02      	add	r7, sp, #8
   45760:	60f8      	str	r0, [r7, #12]
   45762:	60b9      	str	r1, [r7, #8]
   45764:	607a      	str	r2, [r7, #4]
   45766:	603b      	str	r3, [r7, #0]
   45768:	2280      	movs	r2, #128	; 0x80
   4576a:	2100      	movs	r1, #0
   4576c:	6838      	ldr	r0, [r7, #0]
   4576e:	f7cb ea78 	blx	10c60 <memset@plt>
   45772:	68bb      	ldr	r3, [r7, #8]
   45774:	2b00      	cmp	r3, #0
   45776:	d106      	bne.n	45786 <teec_pre_process_operation+0x2c>
   45778:	2280      	movs	r2, #128	; 0x80
   4577a:	2100      	movs	r1, #0
   4577c:	6878      	ldr	r0, [r7, #4]
   4577e:	f7cb ea70 	blx	10c60 <memset@plt>
   45782:	2300      	movs	r3, #0
   45784:	e0c3      	b.n	4590e <teec_pre_process_operation+0x1b4>
   45786:	2300      	movs	r3, #0
   45788:	61fb      	str	r3, [r7, #28]
   4578a:	e0bb      	b.n	45904 <teec_pre_process_operation+0x1aa>
   4578c:	68bb      	ldr	r3, [r7, #8]
   4578e:	685a      	ldr	r2, [r3, #4]
   45790:	69fb      	ldr	r3, [r7, #28]
   45792:	009b      	lsls	r3, r3, #2
   45794:	fa22 f303 	lsr.w	r3, r2, r3
   45798:	f003 030f 	and.w	r3, r3, #15
   4579c:	61bb      	str	r3, [r7, #24]
   4579e:	69bb      	ldr	r3, [r7, #24]
   457a0:	2b0f      	cmp	r3, #15
   457a2:	f200 80a3 	bhi.w	458ec <teec_pre_process_operation+0x192>
   457a6:	a202      	add	r2, pc, #8	; (adr r2, 457b0 <teec_pre_process_operation+0x56>)
   457a8:	f852 3023 	ldr.w	r3, [r2, r3, lsl #2]
   457ac:	441a      	add	r2, r3
   457ae:	4710      	bx	r2
   457b0:	00000041 	andeq	r0, r0, r1, asr #32
   457b4:	00000055 	andeq	r0, r0, r5, asr r0
   457b8:	00000055 	andeq	r0, r0, r5, asr r0
   457bc:	00000055 	andeq	r0, r0, r5, asr r0
   457c0:	0000013d 	andeq	r0, r0, sp, lsr r1
   457c4:	000000ad 	andeq	r0, r0, sp, lsr #1
   457c8:	000000ad 	andeq	r0, r0, sp, lsr #1
   457cc:	000000ad 	andeq	r0, r0, sp, lsr #1
   457d0:	0000013d 	andeq	r0, r0, sp, lsr r1
   457d4:	0000013d 	andeq	r0, r0, sp, lsr r1
   457d8:	0000013d 	andeq	r0, r0, sp, lsr r1
   457dc:	0000013d 	andeq	r0, r0, sp, lsr r1
   457e0:	000000e7 	andeq	r0, r0, r7, ror #1
   457e4:	00000111 	andeq	r0, r0, r1, lsl r1
   457e8:	00000111 	andeq	r0, r0, r1, lsl r1
   457ec:	00000111 	andeq	r0, r0, r1, lsl r1
   457f0:	69fb      	ldr	r3, [r7, #28]
   457f2:	015b      	lsls	r3, r3, #5
   457f4:	687a      	ldr	r2, [r7, #4]
   457f6:	441a      	add	r2, r3
   457f8:	69bb      	ldr	r3, [r7, #24]
   457fa:	f04f 0400 	mov.w	r4, #0
   457fe:	e9c2 3400 	strd	r3, r4, [r2]
   45802:	e07c      	b.n	458fe <teec_pre_process_operation+0x1a4>
   45804:	69fb      	ldr	r3, [r7, #28]
   45806:	015b      	lsls	r3, r3, #5
   45808:	687a      	ldr	r2, [r7, #4]
   4580a:	441a      	add	r2, r3
   4580c:	69bb      	ldr	r3, [r7, #24]
   4580e:	f04f 0400 	mov.w	r4, #0
   45812:	e9c2 3400 	strd	r3, r4, [r2]
   45816:	69fb      	ldr	r3, [r7, #28]
   45818:	015b      	lsls	r3, r3, #5
   4581a:	687a      	ldr	r2, [r7, #4]
   4581c:	18d1      	adds	r1, r2, r3
   4581e:	68b8      	ldr	r0, [r7, #8]
   45820:	69fa      	ldr	r2, [r7, #28]
   45822:	4613      	mov	r3, r2
   45824:	005b      	lsls	r3, r3, #1
   45826:	4413      	add	r3, r2
   45828:	009b      	lsls	r3, r3, #2
   4582a:	4403      	add	r3, r0
   4582c:	3308      	adds	r3, #8
   4582e:	681b      	ldr	r3, [r3, #0]
   45830:	f04f 0400 	mov.w	r4, #0
   45834:	e9c1 3402 	strd	r3, r4, [r1, #8]
   45838:	69fb      	ldr	r3, [r7, #28]
   4583a:	015b      	lsls	r3, r3, #5
   4583c:	687a      	ldr	r2, [r7, #4]
   4583e:	18d1      	adds	r1, r2, r3
   45840:	68b8      	ldr	r0, [r7, #8]
   45842:	69fa      	ldr	r2, [r7, #28]
   45844:	4613      	mov	r3, r2
   45846:	005b      	lsls	r3, r3, #1
   45848:	4413      	add	r3, r2
   4584a:	009b      	lsls	r3, r3, #2
   4584c:	4403      	add	r3, r0
   4584e:	330c      	adds	r3, #12
   45850:	681b      	ldr	r3, [r3, #0]
   45852:	f04f 0400 	mov.w	r4, #0
   45856:	e9c1 3404 	strd	r3, r4, [r1, #16]
   4585a:	e050      	b.n	458fe <teec_pre_process_operation+0x1a4>
   4585c:	69fa      	ldr	r2, [r7, #28]
   4585e:	4613      	mov	r3, r2
   45860:	005b      	lsls	r3, r3, #1
   45862:	4413      	add	r3, r2
   45864:	009b      	lsls	r3, r3, #2
   45866:	3308      	adds	r3, #8
   45868:	68ba      	ldr	r2, [r7, #8]
   4586a:	18d1      	adds	r1, r2, r3
   4586c:	69fb      	ldr	r3, [r7, #28]
   4586e:	015b      	lsls	r3, r3, #5
   45870:	687a      	ldr	r2, [r7, #4]
   45872:	18d0      	adds	r0, r2, r3
   45874:	69fb      	ldr	r3, [r7, #28]
   45876:	015b      	lsls	r3, r3, #5
   45878:	683a      	ldr	r2, [r7, #0]
   4587a:	4413      	add	r3, r2
   4587c:	9300      	str	r3, [sp, #0]
   4587e:	4603      	mov	r3, r0
   45880:	460a      	mov	r2, r1
   45882:	69b9      	ldr	r1, [r7, #24]
   45884:	68f8      	ldr	r0, [r7, #12]
   45886:	f7ff fe3f 	bl	45508 <teec_pre_process_tmpref>
   4588a:	6178      	str	r0, [r7, #20]
   4588c:	697b      	ldr	r3, [r7, #20]
   4588e:	2b00      	cmp	r3, #0
   45890:	d030      	beq.n	458f4 <teec_pre_process_operation+0x19a>
   45892:	697b      	ldr	r3, [r7, #20]
   45894:	e03b      	b.n	4590e <teec_pre_process_operation+0x1b4>
   45896:	69fa      	ldr	r2, [r7, #28]
   45898:	4613      	mov	r3, r2
   4589a:	005b      	lsls	r3, r3, #1
   4589c:	4413      	add	r3, r2
   4589e:	009b      	lsls	r3, r3, #2
   458a0:	3308      	adds	r3, #8
   458a2:	68ba      	ldr	r2, [r7, #8]
   458a4:	18d0      	adds	r0, r2, r3
   458a6:	69fb      	ldr	r3, [r7, #28]
   458a8:	015b      	lsls	r3, r3, #5
   458aa:	687a      	ldr	r2, [r7, #4]
   458ac:	4413      	add	r3, r2
   458ae:	4619      	mov	r1, r3
   458b0:	f7ff fe87 	bl	455c2 <teec_pre_process_whole>
   458b4:	6178      	str	r0, [r7, #20]
   458b6:	697b      	ldr	r3, [r7, #20]
   458b8:	2b00      	cmp	r3, #0
   458ba:	d01d      	beq.n	458f8 <teec_pre_process_operation+0x19e>
   458bc:	697b      	ldr	r3, [r7, #20]
   458be:	e026      	b.n	4590e <teec_pre_process_operation+0x1b4>
   458c0:	69fa      	ldr	r2, [r7, #28]
   458c2:	4613      	mov	r3, r2
   458c4:	005b      	lsls	r3, r3, #1
   458c6:	4413      	add	r3, r2
   458c8:	009b      	lsls	r3, r3, #2
   458ca:	3308      	adds	r3, #8
   458cc:	68ba      	ldr	r2, [r7, #8]
   458ce:	18d1      	adds	r1, r2, r3
   458d0:	69fb      	ldr	r3, [r7, #28]
   458d2:	015b      	lsls	r3, r3, #5
   458d4:	687a      	ldr	r2, [r7, #4]
   458d6:	4413      	add	r3, r2
   458d8:	461a      	mov	r2, r3
   458da:	69b8      	ldr	r0, [r7, #24]
   458dc:	f7ff fed0 	bl	45680 <teec_pre_process_partial>
   458e0:	6178      	str	r0, [r7, #20]
   458e2:	697b      	ldr	r3, [r7, #20]
   458e4:	2b00      	cmp	r3, #0
   458e6:	d009      	beq.n	458fc <teec_pre_process_operation+0x1a2>
   458e8:	697b      	ldr	r3, [r7, #20]
   458ea:	e010      	b.n	4590e <teec_pre_process_operation+0x1b4>
   458ec:	2306      	movs	r3, #6
   458ee:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   458f2:	e00c      	b.n	4590e <teec_pre_process_operation+0x1b4>
   458f4:	bf00      	nop
   458f6:	e002      	b.n	458fe <teec_pre_process_operation+0x1a4>
   458f8:	bf00      	nop
   458fa:	e000      	b.n	458fe <teec_pre_process_operation+0x1a4>
   458fc:	bf00      	nop
   458fe:	69fb      	ldr	r3, [r7, #28]
   45900:	3301      	adds	r3, #1
   45902:	61fb      	str	r3, [r7, #28]
   45904:	69fb      	ldr	r3, [r7, #28]
   45906:	2b03      	cmp	r3, #3
   45908:	f67f af40 	bls.w	4578c <teec_pre_process_operation+0x32>
   4590c:	2300      	movs	r3, #0
   4590e:	4618      	mov	r0, r3
   45910:	3724      	adds	r7, #36	; 0x24
   45912:	46bd      	mov	sp, r7
   45914:	bd90      	pop	{r4, r7, pc}

00045916 <teec_post_process_tmpref>:
   45916:	b590      	push	{r4, r7, lr}
   45918:	b085      	sub	sp, #20
   4591a:	af00      	add	r7, sp, #0
   4591c:	60f8      	str	r0, [r7, #12]
   4591e:	60b9      	str	r1, [r7, #8]
   45920:	607a      	str	r2, [r7, #4]
   45922:	603b      	str	r3, [r7, #0]
   45924:	68fb      	ldr	r3, [r7, #12]
   45926:	2b05      	cmp	r3, #5
   45928:	d01f      	beq.n	4596a <teec_post_process_tmpref+0x54>
   4592a:	687b      	ldr	r3, [r7, #4]
   4592c:	e9d3 3404 	ldrd	r3, r4, [r3, #16]
   45930:	68ba      	ldr	r2, [r7, #8]
   45932:	6852      	ldr	r2, [r2, #4]
   45934:	4611      	mov	r1, r2
   45936:	f04f 0200 	mov.w	r2, #0
   4593a:	42a2      	cmp	r2, r4
   4593c:	bf08      	it	eq
   4593e:	4299      	cmpeq	r1, r3
   45940:	d30d      	bcc.n	4595e <teec_post_process_tmpref+0x48>
   45942:	68bb      	ldr	r3, [r7, #8]
   45944:	681b      	ldr	r3, [r3, #0]
   45946:	2b00      	cmp	r3, #0
   45948:	d009      	beq.n	4595e <teec_post_process_tmpref+0x48>
   4594a:	68bb      	ldr	r3, [r7, #8]
   4594c:	6818      	ldr	r0, [r3, #0]
   4594e:	683b      	ldr	r3, [r7, #0]
   45950:	6819      	ldr	r1, [r3, #0]
   45952:	687b      	ldr	r3, [r7, #4]
   45954:	e9d3 3404 	ldrd	r3, r4, [r3, #16]
   45958:	461a      	mov	r2, r3
   4595a:	f7cb e91c 	blx	10b94 <memcpy@plt>
   4595e:	687b      	ldr	r3, [r7, #4]
   45960:	e9d3 3404 	ldrd	r3, r4, [r3, #16]
   45964:	461a      	mov	r2, r3
   45966:	68bb      	ldr	r3, [r7, #8]
   45968:	605a      	str	r2, [r3, #4]
   4596a:	bf00      	nop
   4596c:	3714      	adds	r7, #20
   4596e:	46bd      	mov	sp, r7
   45970:	bd90      	pop	{r4, r7, pc}

00045972 <teec_post_process_whole>:
   45972:	b590      	push	{r4, r7, lr}
   45974:	b085      	sub	sp, #20
   45976:	af00      	add	r7, sp, #0
   45978:	6078      	str	r0, [r7, #4]
   4597a:	6039      	str	r1, [r7, #0]
   4597c:	687b      	ldr	r3, [r7, #4]
   4597e:	681b      	ldr	r3, [r3, #0]
   45980:	60fb      	str	r3, [r7, #12]
   45982:	68fb      	ldr	r3, [r7, #12]
   45984:	689b      	ldr	r3, [r3, #8]
   45986:	f003 0302 	and.w	r3, r3, #2
   4598a:	2b00      	cmp	r3, #0
   4598c:	d01f      	beq.n	459ce <teec_post_process_whole+0x5c>
   4598e:	68fb      	ldr	r3, [r7, #12]
   45990:	695b      	ldr	r3, [r3, #20]
   45992:	2b00      	cmp	r3, #0
   45994:	d015      	beq.n	459c2 <teec_post_process_whole+0x50>
   45996:	683b      	ldr	r3, [r7, #0]
   45998:	e9d3 3404 	ldrd	r3, r4, [r3, #16]
   4599c:	68fa      	ldr	r2, [r7, #12]
   4599e:	6852      	ldr	r2, [r2, #4]
   459a0:	4611      	mov	r1, r2
   459a2:	f04f 0200 	mov.w	r2, #0
   459a6:	42a2      	cmp	r2, r4
   459a8:	bf08      	it	eq
   459aa:	4299      	cmpeq	r1, r3
   459ac:	d309      	bcc.n	459c2 <teec_post_process_whole+0x50>
   459ae:	68fb      	ldr	r3, [r7, #12]
   459b0:	6818      	ldr	r0, [r3, #0]
   459b2:	68fb      	ldr	r3, [r7, #12]
   459b4:	6959      	ldr	r1, [r3, #20]
   459b6:	683b      	ldr	r3, [r7, #0]
   459b8:	e9d3 3404 	ldrd	r3, r4, [r3, #16]
   459bc:	461a      	mov	r2, r3
   459be:	f7cb e8ea 	blx	10b94 <memcpy@plt>
   459c2:	683b      	ldr	r3, [r7, #0]
   459c4:	e9d3 3404 	ldrd	r3, r4, [r3, #16]
   459c8:	461a      	mov	r2, r3
   459ca:	687b      	ldr	r3, [r7, #4]
   459cc:	605a      	str	r2, [r3, #4]
   459ce:	bf00      	nop
   459d0:	3714      	adds	r7, #20
   459d2:	46bd      	mov	sp, r7
   459d4:	bd90      	pop	{r4, r7, pc}

000459d6 <teec_post_process_partial>:
   459d6:	b590      	push	{r4, r7, lr}
   459d8:	b087      	sub	sp, #28
   459da:	af00      	add	r7, sp, #0
   459dc:	60f8      	str	r0, [r7, #12]
   459de:	60b9      	str	r1, [r7, #8]
   459e0:	607a      	str	r2, [r7, #4]
   459e2:	68fb      	ldr	r3, [r7, #12]
   459e4:	2b0d      	cmp	r3, #13
   459e6:	d028      	beq.n	45a3a <teec_post_process_partial+0x64>
   459e8:	68bb      	ldr	r3, [r7, #8]
   459ea:	681b      	ldr	r3, [r3, #0]
   459ec:	617b      	str	r3, [r7, #20]
   459ee:	697b      	ldr	r3, [r7, #20]
   459f0:	695b      	ldr	r3, [r3, #20]
   459f2:	2b00      	cmp	r3, #0
   459f4:	d01b      	beq.n	45a2e <teec_post_process_partial+0x58>
   459f6:	687b      	ldr	r3, [r7, #4]
   459f8:	e9d3 3404 	ldrd	r3, r4, [r3, #16]
   459fc:	68ba      	ldr	r2, [r7, #8]
   459fe:	6852      	ldr	r2, [r2, #4]
   45a00:	4611      	mov	r1, r2
   45a02:	f04f 0200 	mov.w	r2, #0
   45a06:	42a2      	cmp	r2, r4
   45a08:	bf08      	it	eq
   45a0a:	4299      	cmpeq	r1, r3
   45a0c:	d30f      	bcc.n	45a2e <teec_post_process_partial+0x58>
   45a0e:	697b      	ldr	r3, [r7, #20]
   45a10:	681a      	ldr	r2, [r3, #0]
   45a12:	68bb      	ldr	r3, [r7, #8]
   45a14:	689b      	ldr	r3, [r3, #8]
   45a16:	18d0      	adds	r0, r2, r3
   45a18:	697b      	ldr	r3, [r7, #20]
   45a1a:	695a      	ldr	r2, [r3, #20]
   45a1c:	68bb      	ldr	r3, [r7, #8]
   45a1e:	689b      	ldr	r3, [r3, #8]
   45a20:	18d1      	adds	r1, r2, r3
   45a22:	687b      	ldr	r3, [r7, #4]
   45a24:	e9d3 3404 	ldrd	r3, r4, [r3, #16]
   45a28:	461a      	mov	r2, r3
   45a2a:	f7cb e8b4 	blx	10b94 <memcpy@plt>
   45a2e:	687b      	ldr	r3, [r7, #4]
   45a30:	e9d3 3404 	ldrd	r3, r4, [r3, #16]
   45a34:	461a      	mov	r2, r3
   45a36:	68bb      	ldr	r3, [r7, #8]
   45a38:	605a      	str	r2, [r3, #4]
   45a3a:	bf00      	nop
   45a3c:	371c      	adds	r7, #28
   45a3e:	46bd      	mov	sp, r7
   45a40:	bd90      	pop	{r4, r7, pc}

00045a42 <teec_post_process_operation>:
   45a42:	b590      	push	{r4, r7, lr}
   45a44:	b087      	sub	sp, #28
   45a46:	af00      	add	r7, sp, #0
   45a48:	60f8      	str	r0, [r7, #12]
   45a4a:	60b9      	str	r1, [r7, #8]
   45a4c:	607a      	str	r2, [r7, #4]
   45a4e:	68fb      	ldr	r3, [r7, #12]
   45a50:	2b00      	cmp	r3, #0
   45a52:	f000 8092 	beq.w	45b7a <teec_post_process_operation+0x138>
   45a56:	2300      	movs	r3, #0
   45a58:	617b      	str	r3, [r7, #20]
   45a5a:	e089      	b.n	45b70 <teec_post_process_operation+0x12e>
   45a5c:	68fb      	ldr	r3, [r7, #12]
   45a5e:	685a      	ldr	r2, [r3, #4]
   45a60:	697b      	ldr	r3, [r7, #20]
   45a62:	009b      	lsls	r3, r3, #2
   45a64:	fa22 f303 	lsr.w	r3, r2, r3
   45a68:	f003 030f 	and.w	r3, r3, #15
   45a6c:	613b      	str	r3, [r7, #16]
   45a6e:	693b      	ldr	r3, [r7, #16]
   45a70:	3b01      	subs	r3, #1
   45a72:	2b0e      	cmp	r3, #14
   45a74:	d878      	bhi.n	45b68 <teec_post_process_operation+0x126>
   45a76:	a202      	add	r2, pc, #8	; (adr r2, 45a80 <teec_post_process_operation+0x3e>)
   45a78:	f852 3023 	ldr.w	r3, [r2, r3, lsl #2]
   45a7c:	441a      	add	r2, r3
   45a7e:	4710      	bx	r2
   45a80:	000000e9 	andeq	r0, r0, r9, ror #1
   45a84:	0000003d 	andeq	r0, r0, sp, lsr r0
   45a88:	0000003d 	andeq	r0, r0, sp, lsr r0
   45a8c:	000000e9 	andeq	r0, r0, r9, ror #1
   45a90:	0000007f 	andeq	r0, r0, pc, ror r0
   45a94:	0000007f 	andeq	r0, r0, pc, ror r0
   45a98:	0000007f 	andeq	r0, r0, pc, ror r0
   45a9c:	000000e9 	andeq	r0, r0, r9, ror #1
   45aa0:	000000e9 	andeq	r0, r0, r9, ror #1
   45aa4:	000000e9 	andeq	r0, r0, r9, ror #1
   45aa8:	000000e9 	andeq	r0, r0, r9, ror #1
   45aac:	000000a9 	andeq	r0, r0, r9, lsr #1
   45ab0:	000000c9 	andeq	r0, r0, r9, asr #1
   45ab4:	000000c9 	andeq	r0, r0, r9, asr #1
   45ab8:	000000c9 	andeq	r0, r0, r9, asr #1
   45abc:	697b      	ldr	r3, [r7, #20]
   45abe:	015b      	lsls	r3, r3, #5
   45ac0:	68ba      	ldr	r2, [r7, #8]
   45ac2:	4413      	add	r3, r2
   45ac4:	e9d3 3402 	ldrd	r3, r4, [r3, #8]
   45ac8:	4618      	mov	r0, r3
   45aca:	68f9      	ldr	r1, [r7, #12]
   45acc:	697a      	ldr	r2, [r7, #20]
   45ace:	4613      	mov	r3, r2
   45ad0:	005b      	lsls	r3, r3, #1
   45ad2:	4413      	add	r3, r2
   45ad4:	009b      	lsls	r3, r3, #2
   45ad6:	440b      	add	r3, r1
   45ad8:	3308      	adds	r3, #8
   45ada:	6018      	str	r0, [r3, #0]
   45adc:	697b      	ldr	r3, [r7, #20]
   45ade:	015b      	lsls	r3, r3, #5
   45ae0:	68ba      	ldr	r2, [r7, #8]
   45ae2:	4413      	add	r3, r2
   45ae4:	e9d3 3404 	ldrd	r3, r4, [r3, #16]
   45ae8:	4618      	mov	r0, r3
   45aea:	68f9      	ldr	r1, [r7, #12]
   45aec:	697a      	ldr	r2, [r7, #20]
   45aee:	4613      	mov	r3, r2
   45af0:	005b      	lsls	r3, r3, #1
   45af2:	4413      	add	r3, r2
   45af4:	009b      	lsls	r3, r3, #2
   45af6:	440b      	add	r3, r1
   45af8:	330c      	adds	r3, #12
   45afa:	6018      	str	r0, [r3, #0]
   45afc:	e035      	b.n	45b6a <teec_post_process_operation+0x128>
   45afe:	697a      	ldr	r2, [r7, #20]
   45b00:	4613      	mov	r3, r2
   45b02:	005b      	lsls	r3, r3, #1
   45b04:	4413      	add	r3, r2
   45b06:	009b      	lsls	r3, r3, #2
   45b08:	3308      	adds	r3, #8
   45b0a:	68fa      	ldr	r2, [r7, #12]
   45b0c:	18d1      	adds	r1, r2, r3
   45b0e:	697b      	ldr	r3, [r7, #20]
   45b10:	015b      	lsls	r3, r3, #5
   45b12:	68ba      	ldr	r2, [r7, #8]
   45b14:	18d0      	adds	r0, r2, r3
   45b16:	697b      	ldr	r3, [r7, #20]
   45b18:	015b      	lsls	r3, r3, #5
   45b1a:	687a      	ldr	r2, [r7, #4]
   45b1c:	4413      	add	r3, r2
   45b1e:	4602      	mov	r2, r0
   45b20:	6938      	ldr	r0, [r7, #16]
   45b22:	f7ff fef8 	bl	45916 <teec_post_process_tmpref>
   45b26:	e020      	b.n	45b6a <teec_post_process_operation+0x128>
   45b28:	697a      	ldr	r2, [r7, #20]
   45b2a:	4613      	mov	r3, r2
   45b2c:	005b      	lsls	r3, r3, #1
   45b2e:	4413      	add	r3, r2
   45b30:	009b      	lsls	r3, r3, #2
   45b32:	3308      	adds	r3, #8
   45b34:	68fa      	ldr	r2, [r7, #12]
   45b36:	18d0      	adds	r0, r2, r3
   45b38:	697b      	ldr	r3, [r7, #20]
   45b3a:	015b      	lsls	r3, r3, #5
   45b3c:	68ba      	ldr	r2, [r7, #8]
   45b3e:	4413      	add	r3, r2
   45b40:	4619      	mov	r1, r3
   45b42:	f7ff ff16 	bl	45972 <teec_post_process_whole>
   45b46:	e010      	b.n	45b6a <teec_post_process_operation+0x128>
   45b48:	697a      	ldr	r2, [r7, #20]
   45b4a:	4613      	mov	r3, r2
   45b4c:	005b      	lsls	r3, r3, #1
   45b4e:	4413      	add	r3, r2
   45b50:	009b      	lsls	r3, r3, #2
   45b52:	3308      	adds	r3, #8
   45b54:	68fa      	ldr	r2, [r7, #12]
   45b56:	18d1      	adds	r1, r2, r3
   45b58:	697b      	ldr	r3, [r7, #20]
   45b5a:	015b      	lsls	r3, r3, #5
   45b5c:	68ba      	ldr	r2, [r7, #8]
   45b5e:	4413      	add	r3, r2
   45b60:	461a      	mov	r2, r3
   45b62:	6938      	ldr	r0, [r7, #16]
   45b64:	f7ff ff37 	bl	459d6 <teec_post_process_partial>
   45b68:	bf00      	nop
   45b6a:	697b      	ldr	r3, [r7, #20]
   45b6c:	3301      	adds	r3, #1
   45b6e:	617b      	str	r3, [r7, #20]
   45b70:	697b      	ldr	r3, [r7, #20]
   45b72:	2b03      	cmp	r3, #3
   45b74:	f67f af72 	bls.w	45a5c <teec_post_process_operation+0x1a>
   45b78:	e000      	b.n	45b7c <teec_post_process_operation+0x13a>
   45b7a:	bf00      	nop
   45b7c:	371c      	adds	r7, #28
   45b7e:	46bd      	mov	sp, r7
   45b80:	bd90      	pop	{r4, r7, pc}

00045b82 <teec_free_temp_refs>:
   45b82:	b580      	push	{r7, lr}
   45b84:	b084      	sub	sp, #16
   45b86:	af00      	add	r7, sp, #0
   45b88:	6078      	str	r0, [r7, #4]
   45b8a:	6039      	str	r1, [r7, #0]
   45b8c:	687b      	ldr	r3, [r7, #4]
   45b8e:	2b00      	cmp	r3, #0
   45b90:	d01d      	beq.n	45bce <teec_free_temp_refs+0x4c>
   45b92:	2300      	movs	r3, #0
   45b94:	60fb      	str	r3, [r7, #12]
   45b96:	e016      	b.n	45bc6 <teec_free_temp_refs+0x44>
   45b98:	687b      	ldr	r3, [r7, #4]
   45b9a:	685a      	ldr	r2, [r3, #4]
   45b9c:	68fb      	ldr	r3, [r7, #12]
   45b9e:	009b      	lsls	r3, r3, #2
   45ba0:	fa22 f303 	lsr.w	r3, r2, r3
   45ba4:	f003 030f 	and.w	r3, r3, #15
   45ba8:	3b05      	subs	r3, #5
   45baa:	2b02      	cmp	r3, #2
   45bac:	d807      	bhi.n	45bbe <teec_free_temp_refs+0x3c>
   45bae:	68fb      	ldr	r3, [r7, #12]
   45bb0:	015b      	lsls	r3, r3, #5
   45bb2:	683a      	ldr	r2, [r7, #0]
   45bb4:	4413      	add	r3, r2
   45bb6:	4618      	mov	r0, r3
   45bb8:	f000 fbfb 	bl	463b2 <TEEC_ReleaseSharedMemory>
   45bbc:	e000      	b.n	45bc0 <teec_free_temp_refs+0x3e>
   45bbe:	bf00      	nop
   45bc0:	68fb      	ldr	r3, [r7, #12]
   45bc2:	3301      	adds	r3, #1
   45bc4:	60fb      	str	r3, [r7, #12]
   45bc6:	68fb      	ldr	r3, [r7, #12]
   45bc8:	2b03      	cmp	r3, #3
   45bca:	d9e5      	bls.n	45b98 <teec_free_temp_refs+0x16>
   45bcc:	e000      	b.n	45bd0 <teec_free_temp_refs+0x4e>
   45bce:	bf00      	nop
   45bd0:	3710      	adds	r7, #16
   45bd2:	46bd      	mov	sp, r7
   45bd4:	bd80      	pop	{r7, pc}

00045bd6 <ioctl_errno_to_res>:
   45bd6:	b480      	push	{r7}
   45bd8:	b083      	sub	sp, #12
   45bda:	af00      	add	r7, sp, #0
   45bdc:	6078      	str	r0, [r7, #4]
   45bde:	687b      	ldr	r3, [r7, #4]
   45be0:	2b0c      	cmp	r3, #12
   45be2:	d103      	bne.n	45bec <ioctl_errno_to_res+0x16>
   45be4:	230c      	movs	r3, #12
   45be6:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   45bea:	e002      	b.n	45bf2 <ioctl_errno_to_res+0x1c>
   45bec:	2300      	movs	r3, #0
   45bee:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   45bf2:	4618      	mov	r0, r3
   45bf4:	370c      	adds	r7, #12
   45bf6:	46bd      	mov	sp, r7
   45bf8:	f85d 7b04 	ldr.w	r7, [sp], #4
   45bfc:	4770      	bx	lr

00045bfe <uuid_to_octets>:
   45bfe:	b580      	push	{r7, lr}
   45c00:	b082      	sub	sp, #8
   45c02:	af00      	add	r7, sp, #0
   45c04:	6078      	str	r0, [r7, #4]
   45c06:	6039      	str	r1, [r7, #0]
   45c08:	683b      	ldr	r3, [r7, #0]
   45c0a:	681b      	ldr	r3, [r3, #0]
   45c0c:	0e1b      	lsrs	r3, r3, #24
   45c0e:	b2da      	uxtb	r2, r3
   45c10:	687b      	ldr	r3, [r7, #4]
   45c12:	701a      	strb	r2, [r3, #0]
   45c14:	687b      	ldr	r3, [r7, #4]
   45c16:	3301      	adds	r3, #1
   45c18:	683a      	ldr	r2, [r7, #0]
   45c1a:	6812      	ldr	r2, [r2, #0]
   45c1c:	0c12      	lsrs	r2, r2, #16
   45c1e:	b2d2      	uxtb	r2, r2
   45c20:	701a      	strb	r2, [r3, #0]
   45c22:	687b      	ldr	r3, [r7, #4]
   45c24:	3302      	adds	r3, #2
   45c26:	683a      	ldr	r2, [r7, #0]
   45c28:	6812      	ldr	r2, [r2, #0]
   45c2a:	0a12      	lsrs	r2, r2, #8
   45c2c:	b2d2      	uxtb	r2, r2
   45c2e:	701a      	strb	r2, [r3, #0]
   45c30:	687b      	ldr	r3, [r7, #4]
   45c32:	3303      	adds	r3, #3
   45c34:	683a      	ldr	r2, [r7, #0]
   45c36:	6812      	ldr	r2, [r2, #0]
   45c38:	b2d2      	uxtb	r2, r2
   45c3a:	701a      	strb	r2, [r3, #0]
   45c3c:	687b      	ldr	r3, [r7, #4]
   45c3e:	3304      	adds	r3, #4
   45c40:	683a      	ldr	r2, [r7, #0]
   45c42:	8892      	ldrh	r2, [r2, #4]
   45c44:	0a12      	lsrs	r2, r2, #8
   45c46:	b292      	uxth	r2, r2
   45c48:	b2d2      	uxtb	r2, r2
   45c4a:	701a      	strb	r2, [r3, #0]
   45c4c:	687b      	ldr	r3, [r7, #4]
   45c4e:	3305      	adds	r3, #5
   45c50:	683a      	ldr	r2, [r7, #0]
   45c52:	8892      	ldrh	r2, [r2, #4]
   45c54:	b2d2      	uxtb	r2, r2
   45c56:	701a      	strb	r2, [r3, #0]
   45c58:	687b      	ldr	r3, [r7, #4]
   45c5a:	3306      	adds	r3, #6
   45c5c:	683a      	ldr	r2, [r7, #0]
   45c5e:	88d2      	ldrh	r2, [r2, #6]
   45c60:	0a12      	lsrs	r2, r2, #8
   45c62:	b292      	uxth	r2, r2
   45c64:	b2d2      	uxtb	r2, r2
   45c66:	701a      	strb	r2, [r3, #0]
   45c68:	687b      	ldr	r3, [r7, #4]
   45c6a:	3307      	adds	r3, #7
   45c6c:	683a      	ldr	r2, [r7, #0]
   45c6e:	88d2      	ldrh	r2, [r2, #6]
   45c70:	b2d2      	uxtb	r2, r2
   45c72:	701a      	strb	r2, [r3, #0]
   45c74:	687b      	ldr	r3, [r7, #4]
   45c76:	f103 0008 	add.w	r0, r3, #8
   45c7a:	683b      	ldr	r3, [r7, #0]
   45c7c:	3308      	adds	r3, #8
   45c7e:	2208      	movs	r2, #8
   45c80:	4619      	mov	r1, r3
   45c82:	f7ca ef88 	blx	10b94 <memcpy@plt>
   45c86:	bf00      	nop
   45c88:	3708      	adds	r7, #8
   45c8a:	46bd      	mov	sp, r7
   45c8c:	bd80      	pop	{r7, pc}

00045c8e <TEEC_OpenSession>:
   45c8e:	b590      	push	{r4, r7, lr}
   45c90:	b0df      	sub	sp, #380	; 0x17c
   45c92:	af02      	add	r7, sp, #8
   45c94:	f107 040c 	add.w	r4, r7, #12
   45c98:	6020      	str	r0, [r4, #0]
   45c9a:	f107 0008 	add.w	r0, r7, #8
   45c9e:	6001      	str	r1, [r0, #0]
   45ca0:	1d39      	adds	r1, r7, #4
   45ca2:	600a      	str	r2, [r1, #0]
   45ca4:	463a      	mov	r2, r7
   45ca6:	6013      	str	r3, [r2, #0]
   45ca8:	f107 03a0 	add.w	r3, r7, #160	; 0xa0
   45cac:	22b8      	movs	r2, #184	; 0xb8
   45cae:	2100      	movs	r1, #0
   45cb0:	4618      	mov	r0, r3
   45cb2:	f7ca efd6 	blx	10c60 <memset@plt>
   45cb6:	f107 030c 	add.w	r3, r7, #12
   45cba:	681b      	ldr	r3, [r3, #0]
   45cbc:	2b00      	cmp	r3, #0
   45cbe:	d004      	beq.n	45cca <TEEC_OpenSession+0x3c>
   45cc0:	f107 0308 	add.w	r3, r7, #8
   45cc4:	681b      	ldr	r3, [r3, #0]
   45cc6:	2b00      	cmp	r3, #0
   45cc8:	d108      	bne.n	45cdc <TEEC_OpenSession+0x4e>
   45cca:	2301      	movs	r3, #1
   45ccc:	f8c7 3168 	str.w	r3, [r7, #360]	; 0x168
   45cd0:	2306      	movs	r3, #6
   45cd2:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   45cd6:	f8c7 316c 	str.w	r3, [r7, #364]	; 0x16c
   45cda:	e091      	b.n	45e00 <TEEC_OpenSession+0x172>
   45cdc:	f107 03a0 	add.w	r3, r7, #160	; 0xa0
   45ce0:	f04f 0400 	mov.w	r4, #0
   45ce4:	e9c7 3424 	strd	r3, r4, [r7, #144]	; 0x90
   45ce8:	f04f 03b8 	mov.w	r3, #184	; 0xb8
   45cec:	f04f 0400 	mov.w	r4, #0
   45cf0:	e9c7 3426 	strd	r3, r4, [r7, #152]	; 0x98
   45cf4:	f107 03a0 	add.w	r3, r7, #160	; 0xa0
   45cf8:	f8c7 3164 	str.w	r3, [r7, #356]	; 0x164
   45cfc:	f8d7 3164 	ldr.w	r3, [r7, #356]	; 0x164
   45d00:	2204      	movs	r2, #4
   45d02:	635a      	str	r2, [r3, #52]	; 0x34
   45d04:	f8d7 3164 	ldr.w	r3, [r7, #356]	; 0x164
   45d08:	3338      	adds	r3, #56	; 0x38
   45d0a:	f8c7 3160 	str.w	r3, [r7, #352]	; 0x160
   45d0e:	f8d7 2164 	ldr.w	r2, [r7, #356]	; 0x164
   45d12:	1d3b      	adds	r3, r7, #4
   45d14:	6819      	ldr	r1, [r3, #0]
   45d16:	4610      	mov	r0, r2
   45d18:	f7ff ff71 	bl	45bfe <uuid_to_octets>
   45d1c:	f8d7 3164 	ldr.w	r3, [r7, #356]	; 0x164
   45d20:	463a      	mov	r2, r7
   45d22:	6812      	ldr	r2, [r2, #0]
   45d24:	621a      	str	r2, [r3, #32]
   45d26:	f107 0310 	add.w	r3, r7, #16
   45d2a:	f107 000c 	add.w	r0, r7, #12
   45d2e:	f8d7 2160 	ldr.w	r2, [r7, #352]	; 0x160
   45d32:	f8d7 1184 	ldr.w	r1, [r7, #388]	; 0x184
   45d36:	6800      	ldr	r0, [r0, #0]
   45d38:	f7ff fd0f 	bl	4575a <teec_pre_process_operation>
   45d3c:	f8c7 016c 	str.w	r0, [r7, #364]	; 0x16c
   45d40:	f8d7 316c 	ldr.w	r3, [r7, #364]	; 0x16c
   45d44:	2b00      	cmp	r3, #0
   45d46:	d003      	beq.n	45d50 <TEEC_OpenSession+0xc2>
   45d48:	2301      	movs	r3, #1
   45d4a:	f8c7 3168 	str.w	r3, [r7, #360]	; 0x168
   45d4e:	e050      	b.n	45df2 <TEEC_OpenSession+0x164>
   45d50:	f107 030c 	add.w	r3, r7, #12
   45d54:	681b      	ldr	r3, [r3, #0]
   45d56:	681b      	ldr	r3, [r3, #0]
   45d58:	f107 0290 	add.w	r2, r7, #144	; 0x90
   45d5c:	f24a 4102 	movw	r1, #41986	; 0xa402
   45d60:	f2c8 0110 	movt	r1, #32784	; 0x8010
   45d64:	4618      	mov	r0, r3
   45d66:	f7ca ef22 	blx	10bac <ioctl@plt>
   45d6a:	f8c7 015c 	str.w	r0, [r7, #348]	; 0x15c
   45d6e:	f8d7 315c 	ldr.w	r3, [r7, #348]	; 0x15c
   45d72:	2b00      	cmp	r3, #0
   45d74:	d018      	beq.n	45da8 <TEEC_OpenSession+0x11a>
   45d76:	4b2a      	ldr	r3, [pc, #168]	; (45e20 <TEEC_OpenSession+0x192>)
   45d78:	447b      	add	r3, pc
   45d7a:	9300      	str	r3, [sp, #0]
   45d7c:	4b29      	ldr	r3, [pc, #164]	; (45e24 <TEEC_OpenSession+0x196>)
   45d7e:	447b      	add	r3, pc
   45d80:	2201      	movs	r2, #1
   45d82:	f240 210a 	movw	r1, #522	; 0x20a
   45d86:	4828      	ldr	r0, [pc, #160]	; (45e28 <TEEC_OpenSession+0x19a>)
   45d88:	4478      	add	r0, pc
   45d8a:	f000 fb6b 	bl	46464 <_dprintf>
   45d8e:	2302      	movs	r3, #2
   45d90:	f8c7 3168 	str.w	r3, [r7, #360]	; 0x168
   45d94:	f7ca ef58 	blx	10c48 <__errno_location@plt>
   45d98:	4603      	mov	r3, r0
   45d9a:	681b      	ldr	r3, [r3, #0]
   45d9c:	4618      	mov	r0, r3
   45d9e:	f7ff ff1a 	bl	45bd6 <ioctl_errno_to_res>
   45da2:	f8c7 016c 	str.w	r0, [r7, #364]	; 0x16c
   45da6:	e024      	b.n	45df2 <TEEC_OpenSession+0x164>
   45da8:	f8d7 3164 	ldr.w	r3, [r7, #356]	; 0x164
   45dac:	6adb      	ldr	r3, [r3, #44]	; 0x2c
   45dae:	f8c7 316c 	str.w	r3, [r7, #364]	; 0x16c
   45db2:	f8d7 3164 	ldr.w	r3, [r7, #356]	; 0x164
   45db6:	6b1b      	ldr	r3, [r3, #48]	; 0x30
   45db8:	f8c7 3168 	str.w	r3, [r7, #360]	; 0x168
   45dbc:	f8d7 316c 	ldr.w	r3, [r7, #364]	; 0x16c
   45dc0:	2b00      	cmp	r3, #0
   45dc2:	d10d      	bne.n	45de0 <TEEC_OpenSession+0x152>
   45dc4:	f107 0308 	add.w	r3, r7, #8
   45dc8:	681b      	ldr	r3, [r3, #0]
   45dca:	f107 020c 	add.w	r2, r7, #12
   45dce:	6812      	ldr	r2, [r2, #0]
   45dd0:	601a      	str	r2, [r3, #0]
   45dd2:	f8d7 3164 	ldr.w	r3, [r7, #356]	; 0x164
   45dd6:	6a9a      	ldr	r2, [r3, #40]	; 0x28
   45dd8:	f107 0308 	add.w	r3, r7, #8
   45ddc:	681b      	ldr	r3, [r3, #0]
   45dde:	605a      	str	r2, [r3, #4]
   45de0:	f107 0310 	add.w	r3, r7, #16
   45de4:	461a      	mov	r2, r3
   45de6:	f8d7 1160 	ldr.w	r1, [r7, #352]	; 0x160
   45dea:	f8d7 0184 	ldr.w	r0, [r7, #388]	; 0x184
   45dee:	f7ff fe28 	bl	45a42 <teec_post_process_operation>
   45df2:	f107 0310 	add.w	r3, r7, #16
   45df6:	4619      	mov	r1, r3
   45df8:	f8d7 0184 	ldr.w	r0, [r7, #388]	; 0x184
   45dfc:	f7ff fec1 	bl	45b82 <teec_free_temp_refs>
   45e00:	f8d7 3188 	ldr.w	r3, [r7, #392]	; 0x188
   45e04:	2b00      	cmp	r3, #0
   45e06:	d004      	beq.n	45e12 <TEEC_OpenSession+0x184>
   45e08:	f8d7 3188 	ldr.w	r3, [r7, #392]	; 0x188
   45e0c:	f8d7 2168 	ldr.w	r2, [r7, #360]	; 0x168
   45e10:	601a      	str	r2, [r3, #0]
   45e12:	f8d7 316c 	ldr.w	r3, [r7, #364]	; 0x16c
   45e16:	4618      	mov	r0, r3
   45e18:	f507 77ba 	add.w	r7, r7, #372	; 0x174
   45e1c:	46bd      	mov	sp, r7
   45e1e:	bd90      	pop	{r4, r7, pc}
   45e20:	00000f20 	andeq	r0, r0, r0, lsr #30
   45e24:	00000ee2 	andeq	r0, r0, r2, ror #29
   45e28:	00000f8c 	andeq	r0, r0, ip, lsl #31

00045e2c <TEEC_CloseSession>:
   45e2c:	b580      	push	{r7, lr}
   45e2e:	b086      	sub	sp, #24
   45e30:	af02      	add	r7, sp, #8
   45e32:	6078      	str	r0, [r7, #4]
   45e34:	687b      	ldr	r3, [r7, #4]
   45e36:	2b00      	cmp	r3, #0
   45e38:	d021      	beq.n	45e7e <TEEC_CloseSession+0x52>
   45e3a:	687b      	ldr	r3, [r7, #4]
   45e3c:	685b      	ldr	r3, [r3, #4]
   45e3e:	60fb      	str	r3, [r7, #12]
   45e40:	687b      	ldr	r3, [r7, #4]
   45e42:	681b      	ldr	r3, [r3, #0]
   45e44:	681b      	ldr	r3, [r3, #0]
   45e46:	f107 020c 	add.w	r2, r7, #12
   45e4a:	f24a 4105 	movw	r1, #41989	; 0xa405
   45e4e:	f2c8 0104 	movt	r1, #32772	; 0x8004
   45e52:	4618      	mov	r0, r3
   45e54:	f7ca eeaa 	blx	10bac <ioctl@plt>
   45e58:	4603      	mov	r3, r0
   45e5a:	2b00      	cmp	r3, #0
   45e5c:	d010      	beq.n	45e80 <TEEC_CloseSession+0x54>
   45e5e:	687b      	ldr	r3, [r7, #4]
   45e60:	685b      	ldr	r3, [r3, #4]
   45e62:	9301      	str	r3, [sp, #4]
   45e64:	4b08      	ldr	r3, [pc, #32]	; (45e88 <TEEC_CloseSession+0x5c>)
   45e66:	447b      	add	r3, pc
   45e68:	9300      	str	r3, [sp, #0]
   45e6a:	4b08      	ldr	r3, [pc, #32]	; (45e8c <TEEC_CloseSession+0x60>)
   45e6c:	447b      	add	r3, pc
   45e6e:	2201      	movs	r2, #1
   45e70:	f44f 710a 	mov.w	r1, #552	; 0x228
   45e74:	4806      	ldr	r0, [pc, #24]	; (45e90 <TEEC_CloseSession+0x64>)
   45e76:	4478      	add	r0, pc
   45e78:	f000 faf4 	bl	46464 <_dprintf>
   45e7c:	e000      	b.n	45e80 <TEEC_CloseSession+0x54>
   45e7e:	bf00      	nop
   45e80:	3710      	adds	r7, #16
   45e82:	46bd      	mov	sp, r7
   45e84:	bd80      	pop	{r7, pc}
   45e86:	bf00      	nop
   45e88:	00000e52 	andeq	r0, r0, r2, asr lr
   45e8c:	00000df4 	strdeq	r0, [r0], -r4
   45e90:	00000eb2 			; <UNDEFINED> instruction: 0x00000eb2

00045e94 <TEEC_InvokeCommand>:
   45e94:	b590      	push	{r4, r7, lr}
   45e96:	b0d7      	sub	sp, #348	; 0x15c
   45e98:	af02      	add	r7, sp, #8
   45e9a:	f107 040c 	add.w	r4, r7, #12
   45e9e:	6020      	str	r0, [r4, #0]
   45ea0:	f107 0008 	add.w	r0, r7, #8
   45ea4:	6001      	str	r1, [r0, #0]
   45ea6:	1d39      	adds	r1, r7, #4
   45ea8:	600a      	str	r2, [r1, #0]
   45eaa:	463a      	mov	r2, r7
   45eac:	6013      	str	r3, [r2, #0]
   45eae:	f107 03a0 	add.w	r3, r7, #160	; 0xa0
   45eb2:	2298      	movs	r2, #152	; 0x98
   45eb4:	2100      	movs	r1, #0
   45eb6:	4618      	mov	r0, r3
   45eb8:	f7ca eed2 	blx	10c60 <memset@plt>
   45ebc:	f107 030c 	add.w	r3, r7, #12
   45ec0:	681b      	ldr	r3, [r3, #0]
   45ec2:	2b00      	cmp	r3, #0
   45ec4:	d108      	bne.n	45ed8 <TEEC_InvokeCommand+0x44>
   45ec6:	2301      	movs	r3, #1
   45ec8:	f8c7 3148 	str.w	r3, [r7, #328]	; 0x148
   45ecc:	2306      	movs	r3, #6
   45ece:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   45ed2:	f8c7 314c 	str.w	r3, [r7, #332]	; 0x14c
   45ed6:	e099      	b.n	4600c <TEEC_InvokeCommand+0x178>
   45ed8:	f7ff f9ae 	bl	45238 <bm_timestamp>
   45edc:	f107 03a0 	add.w	r3, r7, #160	; 0xa0
   45ee0:	f04f 0400 	mov.w	r4, #0
   45ee4:	e9c7 3424 	strd	r3, r4, [r7, #144]	; 0x90
   45ee8:	f04f 0398 	mov.w	r3, #152	; 0x98
   45eec:	f04f 0400 	mov.w	r4, #0
   45ef0:	e9c7 3426 	strd	r3, r4, [r7, #152]	; 0x98
   45ef4:	f107 03a0 	add.w	r3, r7, #160	; 0xa0
   45ef8:	f8c7 3144 	str.w	r3, [r7, #324]	; 0x144
   45efc:	f8d7 3144 	ldr.w	r3, [r7, #324]	; 0x144
   45f00:	2204      	movs	r2, #4
   45f02:	615a      	str	r2, [r3, #20]
   45f04:	f8d7 3144 	ldr.w	r3, [r7, #324]	; 0x144
   45f08:	3318      	adds	r3, #24
   45f0a:	f8c7 3140 	str.w	r3, [r7, #320]	; 0x140
   45f0e:	f107 030c 	add.w	r3, r7, #12
   45f12:	681b      	ldr	r3, [r3, #0]
   45f14:	685a      	ldr	r2, [r3, #4]
   45f16:	f8d7 3144 	ldr.w	r3, [r7, #324]	; 0x144
   45f1a:	605a      	str	r2, [r3, #4]
   45f1c:	f8d7 3144 	ldr.w	r3, [r7, #324]	; 0x144
   45f20:	f107 0208 	add.w	r2, r7, #8
   45f24:	6812      	ldr	r2, [r2, #0]
   45f26:	601a      	str	r2, [r3, #0]
   45f28:	1d3b      	adds	r3, r7, #4
   45f2a:	681b      	ldr	r3, [r3, #0]
   45f2c:	2b00      	cmp	r3, #0
   45f2e:	d00f      	beq.n	45f50 <TEEC_InvokeCommand+0xbc>
   45f30:	4b3e      	ldr	r3, [pc, #248]	; (4602c <TEEC_InvokeCommand+0x198>)
   45f32:	447b      	add	r3, pc
   45f34:	4618      	mov	r0, r3
   45f36:	f7ff f986 	bl	45246 <teec_mutex_lock>
   45f3a:	1d3b      	adds	r3, r7, #4
   45f3c:	681b      	ldr	r3, [r3, #0]
   45f3e:	f107 020c 	add.w	r2, r7, #12
   45f42:	6812      	ldr	r2, [r2, #0]
   45f44:	639a      	str	r2, [r3, #56]	; 0x38
   45f46:	4b3a      	ldr	r3, [pc, #232]	; (46030 <TEEC_InvokeCommand+0x19c>)
   45f48:	447b      	add	r3, pc
   45f4a:	4618      	mov	r0, r3
   45f4c:	f7ff f986 	bl	4525c <teec_mutex_unlock>
   45f50:	f107 030c 	add.w	r3, r7, #12
   45f54:	681b      	ldr	r3, [r3, #0]
   45f56:	6818      	ldr	r0, [r3, #0]
   45f58:	f107 0310 	add.w	r3, r7, #16
   45f5c:	1d39      	adds	r1, r7, #4
   45f5e:	f8d7 2140 	ldr.w	r2, [r7, #320]	; 0x140
   45f62:	6809      	ldr	r1, [r1, #0]
   45f64:	f7ff fbf9 	bl	4575a <teec_pre_process_operation>
   45f68:	f8c7 014c 	str.w	r0, [r7, #332]	; 0x14c
   45f6c:	f8d7 314c 	ldr.w	r3, [r7, #332]	; 0x14c
   45f70:	2b00      	cmp	r3, #0
   45f72:	d003      	beq.n	45f7c <TEEC_InvokeCommand+0xe8>
   45f74:	2301      	movs	r3, #1
   45f76:	f8c7 3148 	str.w	r3, [r7, #328]	; 0x148
   45f7a:	e040      	b.n	45ffe <TEEC_InvokeCommand+0x16a>
   45f7c:	f107 030c 	add.w	r3, r7, #12
   45f80:	681b      	ldr	r3, [r3, #0]
   45f82:	681b      	ldr	r3, [r3, #0]
   45f84:	681b      	ldr	r3, [r3, #0]
   45f86:	f107 0290 	add.w	r2, r7, #144	; 0x90
   45f8a:	f24a 4103 	movw	r1, #41987	; 0xa403
   45f8e:	f2c8 0110 	movt	r1, #32784	; 0x8010
   45f92:	4618      	mov	r0, r3
   45f94:	f7ca ee0a 	blx	10bac <ioctl@plt>
   45f98:	f8c7 013c 	str.w	r0, [r7, #316]	; 0x13c
   45f9c:	f8d7 313c 	ldr.w	r3, [r7, #316]	; 0x13c
   45fa0:	2b00      	cmp	r3, #0
   45fa2:	d018      	beq.n	45fd6 <TEEC_InvokeCommand+0x142>
   45fa4:	4b23      	ldr	r3, [pc, #140]	; (46034 <TEEC_InvokeCommand+0x1a0>)
   45fa6:	447b      	add	r3, pc
   45fa8:	9300      	str	r3, [sp, #0]
   45faa:	4b23      	ldr	r3, [pc, #140]	; (46038 <TEEC_InvokeCommand+0x1a4>)
   45fac:	447b      	add	r3, pc
   45fae:	2201      	movs	r2, #1
   45fb0:	f240 215a 	movw	r1, #602	; 0x25a
   45fb4:	4821      	ldr	r0, [pc, #132]	; (4603c <TEEC_InvokeCommand+0x1a8>)
   45fb6:	4478      	add	r0, pc
   45fb8:	f000 fa54 	bl	46464 <_dprintf>
   45fbc:	2302      	movs	r3, #2
   45fbe:	f8c7 3148 	str.w	r3, [r7, #328]	; 0x148
   45fc2:	f7ca ee42 	blx	10c48 <__errno_location@plt>
   45fc6:	4603      	mov	r3, r0
   45fc8:	681b      	ldr	r3, [r3, #0]
   45fca:	4618      	mov	r0, r3
   45fcc:	f7ff fe03 	bl	45bd6 <ioctl_errno_to_res>
   45fd0:	f8c7 014c 	str.w	r0, [r7, #332]	; 0x14c
   45fd4:	e013      	b.n	45ffe <TEEC_InvokeCommand+0x16a>
   45fd6:	f8d7 3144 	ldr.w	r3, [r7, #324]	; 0x144
   45fda:	68db      	ldr	r3, [r3, #12]
   45fdc:	f8c7 314c 	str.w	r3, [r7, #332]	; 0x14c
   45fe0:	f8d7 3144 	ldr.w	r3, [r7, #324]	; 0x144
   45fe4:	691b      	ldr	r3, [r3, #16]
   45fe6:	f8c7 3148 	str.w	r3, [r7, #328]	; 0x148
   45fea:	f107 0210 	add.w	r2, r7, #16
   45fee:	1d3b      	adds	r3, r7, #4
   45ff0:	f8d7 1140 	ldr.w	r1, [r7, #320]	; 0x140
   45ff4:	6818      	ldr	r0, [r3, #0]
   45ff6:	f7ff fd24 	bl	45a42 <teec_post_process_operation>
   45ffa:	f7ff f91d 	bl	45238 <bm_timestamp>
   45ffe:	f107 0210 	add.w	r2, r7, #16
   46002:	1d3b      	adds	r3, r7, #4
   46004:	4611      	mov	r1, r2
   46006:	6818      	ldr	r0, [r3, #0]
   46008:	f7ff fdbb 	bl	45b82 <teec_free_temp_refs>
   4600c:	463b      	mov	r3, r7
   4600e:	681b      	ldr	r3, [r3, #0]
   46010:	2b00      	cmp	r3, #0
   46012:	d004      	beq.n	4601e <TEEC_InvokeCommand+0x18a>
   46014:	463b      	mov	r3, r7
   46016:	681b      	ldr	r3, [r3, #0]
   46018:	f8d7 2148 	ldr.w	r2, [r7, #328]	; 0x148
   4601c:	601a      	str	r2, [r3, #0]
   4601e:	f8d7 314c 	ldr.w	r3, [r7, #332]	; 0x14c
   46022:	4618      	mov	r0, r3
   46024:	f507 77aa 	add.w	r7, r7, #340	; 0x154
   46028:	46bd      	mov	sp, r7
   4602a:	bd90      	pop	{r4, r7, pc}
   4602c:	00011da2 	andeq	r1, r1, r2, lsr #27
   46030:	00011d8c 	andeq	r1, r1, ip, lsl #27
   46034:	00000d32 	andeq	r0, r0, r2, lsr sp
   46038:	00000cb4 			; <UNDEFINED> instruction: 0x00000cb4
   4603c:	00000d86 	andeq	r0, r0, r6, lsl #27

00046040 <TEEC_RequestCancellation>:
   46040:	b580      	push	{r7, lr}
   46042:	b088      	sub	sp, #32
   46044:	af02      	add	r7, sp, #8
   46046:	6078      	str	r0, [r7, #4]
   46048:	687b      	ldr	r3, [r7, #4]
   4604a:	2b00      	cmp	r3, #0
   4604c:	d039      	beq.n	460c2 <TEEC_RequestCancellation+0x82>
   4604e:	4b20      	ldr	r3, [pc, #128]	; (460d0 <TEEC_RequestCancellation+0x90>)
   46050:	447b      	add	r3, pc
   46052:	4618      	mov	r0, r3
   46054:	f7ff f8f7 	bl	45246 <teec_mutex_lock>
   46058:	687b      	ldr	r3, [r7, #4]
   4605a:	6b9b      	ldr	r3, [r3, #56]	; 0x38
   4605c:	617b      	str	r3, [r7, #20]
   4605e:	4b1d      	ldr	r3, [pc, #116]	; (460d4 <TEEC_RequestCancellation+0x94>)
   46060:	447b      	add	r3, pc
   46062:	4618      	mov	r0, r3
   46064:	f7ff f8fa 	bl	4525c <teec_mutex_unlock>
   46068:	697b      	ldr	r3, [r7, #20]
   4606a:	2b00      	cmp	r3, #0
   4606c:	d02b      	beq.n	460c6 <TEEC_RequestCancellation+0x86>
   4606e:	697b      	ldr	r3, [r7, #20]
   46070:	685b      	ldr	r3, [r3, #4]
   46072:	613b      	str	r3, [r7, #16]
   46074:	2300      	movs	r3, #0
   46076:	60fb      	str	r3, [r7, #12]
   46078:	697b      	ldr	r3, [r7, #20]
   4607a:	681b      	ldr	r3, [r3, #0]
   4607c:	681b      	ldr	r3, [r3, #0]
   4607e:	f107 020c 	add.w	r2, r7, #12
   46082:	f24a 4104 	movw	r1, #41988	; 0xa404
   46086:	f2c8 0108 	movt	r1, #32776	; 0x8008
   4608a:	4618      	mov	r0, r3
   4608c:	f7ca ed8e 	blx	10bac <ioctl@plt>
   46090:	4603      	mov	r3, r0
   46092:	2b00      	cmp	r3, #0
   46094:	d018      	beq.n	460c8 <TEEC_RequestCancellation+0x88>
   46096:	f7ca edd8 	blx	10c48 <__errno_location@plt>
   4609a:	4603      	mov	r3, r0
   4609c:	681b      	ldr	r3, [r3, #0]
   4609e:	4618      	mov	r0, r3
   460a0:	f7ca edae 	blx	10c00 <strerror@plt>
   460a4:	4603      	mov	r3, r0
   460a6:	9301      	str	r3, [sp, #4]
   460a8:	4b0b      	ldr	r3, [pc, #44]	; (460d8 <TEEC_RequestCancellation+0x98>)
   460aa:	447b      	add	r3, pc
   460ac:	9300      	str	r3, [sp, #0]
   460ae:	4b0b      	ldr	r3, [pc, #44]	; (460dc <TEEC_RequestCancellation+0x9c>)
   460b0:	447b      	add	r3, pc
   460b2:	2201      	movs	r2, #1
   460b4:	f240 2181 	movw	r1, #641	; 0x281
   460b8:	4809      	ldr	r0, [pc, #36]	; (460e0 <TEEC_RequestCancellation+0xa0>)
   460ba:	4478      	add	r0, pc
   460bc:	f000 f9d2 	bl	46464 <_dprintf>
   460c0:	e002      	b.n	460c8 <TEEC_RequestCancellation+0x88>
   460c2:	bf00      	nop
   460c4:	e000      	b.n	460c8 <TEEC_RequestCancellation+0x88>
   460c6:	bf00      	nop
   460c8:	3718      	adds	r7, #24
   460ca:	46bd      	mov	sp, r7
   460cc:	bd80      	pop	{r7, pc}
   460ce:	bf00      	nop
   460d0:	00011c84 	andeq	r1, r1, r4, lsl #25
   460d4:	00011c74 	andeq	r1, r1, r4, ror ip
   460d8:	00000c46 	andeq	r0, r0, r6, asr #24
   460dc:	00000bb0 			; <UNDEFINED> instruction: 0x00000bb0
   460e0:	00000c96 	muleq	r0, r6, ip

000460e4 <TEEC_RegisterSharedMemory>:
   460e4:	b580      	push	{r7, lr}
   460e6:	b086      	sub	sp, #24
   460e8:	af02      	add	r7, sp, #8
   460ea:	6078      	str	r0, [r7, #4]
   460ec:	6039      	str	r1, [r7, #0]
   460ee:	687b      	ldr	r3, [r7, #4]
   460f0:	2b00      	cmp	r3, #0
   460f2:	d002      	beq.n	460fa <TEEC_RegisterSharedMemory+0x16>
   460f4:	683b      	ldr	r3, [r7, #0]
   460f6:	2b00      	cmp	r3, #0
   460f8:	d103      	bne.n	46102 <TEEC_RegisterSharedMemory+0x1e>
   460fa:	2306      	movs	r3, #6
   460fc:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   46100:	e069      	b.n	461d6 <TEEC_RegisterSharedMemory+0xf2>
   46102:	683b      	ldr	r3, [r7, #0]
   46104:	689b      	ldr	r3, [r3, #8]
   46106:	2b00      	cmp	r3, #0
   46108:	d005      	beq.n	46116 <TEEC_RegisterSharedMemory+0x32>
   4610a:	683b      	ldr	r3, [r7, #0]
   4610c:	689b      	ldr	r3, [r3, #8]
   4610e:	f023 0303 	bic.w	r3, r3, #3
   46112:	2b00      	cmp	r3, #0
   46114:	d003      	beq.n	4611e <TEEC_RegisterSharedMemory+0x3a>
   46116:	2306      	movs	r3, #6
   46118:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   4611c:	e05b      	b.n	461d6 <TEEC_RegisterSharedMemory+0xf2>
   4611e:	683b      	ldr	r3, [r7, #0]
   46120:	685b      	ldr	r3, [r3, #4]
   46122:	60fb      	str	r3, [r7, #12]
   46124:	68fb      	ldr	r3, [r7, #12]
   46126:	2b00      	cmp	r3, #0
   46128:	d101      	bne.n	4612e <TEEC_RegisterSharedMemory+0x4a>
   4612a:	2308      	movs	r3, #8
   4612c:	60fb      	str	r3, [r7, #12]
   4612e:	687b      	ldr	r3, [r7, #4]
   46130:	791b      	ldrb	r3, [r3, #4]
   46132:	2b00      	cmp	r3, #0
   46134:	d017      	beq.n	46166 <TEEC_RegisterSharedMemory+0x82>
   46136:	687b      	ldr	r3, [r7, #4]
   46138:	6818      	ldr	r0, [r3, #0]
   4613a:	683b      	ldr	r3, [r7, #0]
   4613c:	6819      	ldr	r1, [r3, #0]
   4613e:	683b      	ldr	r3, [r7, #0]
   46140:	330c      	adds	r3, #12
   46142:	68fa      	ldr	r2, [r7, #12]
   46144:	f7ff f921 	bl	4538a <teec_shm_register>
   46148:	60b8      	str	r0, [r7, #8]
   4614a:	68bb      	ldr	r3, [r7, #8]
   4614c:	2b00      	cmp	r3, #0
   4614e:	da03      	bge.n	46158 <TEEC_RegisterSharedMemory+0x74>
   46150:	230c      	movs	r3, #12
   46152:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   46156:	e03e      	b.n	461d6 <TEEC_RegisterSharedMemory+0xf2>
   46158:	683b      	ldr	r3, [r7, #0]
   4615a:	68ba      	ldr	r2, [r7, #8]
   4615c:	619a      	str	r2, [r3, #24]
   4615e:	683b      	ldr	r3, [r7, #0]
   46160:	2200      	movs	r2, #0
   46162:	615a      	str	r2, [r3, #20]
   46164:	e030      	b.n	461c8 <TEEC_RegisterSharedMemory+0xe4>
   46166:	687b      	ldr	r3, [r7, #4]
   46168:	6818      	ldr	r0, [r3, #0]
   4616a:	683b      	ldr	r3, [r7, #0]
   4616c:	330c      	adds	r3, #12
   4616e:	461a      	mov	r2, r3
   46170:	68f9      	ldr	r1, [r7, #12]
   46172:	f7ff f8df 	bl	45334 <teec_shm_alloc>
   46176:	60b8      	str	r0, [r7, #8]
   46178:	68bb      	ldr	r3, [r7, #8]
   4617a:	2b00      	cmp	r3, #0
   4617c:	da03      	bge.n	46186 <TEEC_RegisterSharedMemory+0xa2>
   4617e:	230c      	movs	r3, #12
   46180:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   46184:	e027      	b.n	461d6 <TEEC_RegisterSharedMemory+0xf2>
   46186:	2300      	movs	r3, #0
   46188:	9301      	str	r3, [sp, #4]
   4618a:	68bb      	ldr	r3, [r7, #8]
   4618c:	9300      	str	r3, [sp, #0]
   4618e:	2301      	movs	r3, #1
   46190:	2203      	movs	r2, #3
   46192:	68f9      	ldr	r1, [r7, #12]
   46194:	2000      	movs	r0, #0
   46196:	f7ca ed4c 	blx	10c30 <mmap@plt>
   4619a:	4602      	mov	r2, r0
   4619c:	683b      	ldr	r3, [r7, #0]
   4619e:	615a      	str	r2, [r3, #20]
   461a0:	68b8      	ldr	r0, [r7, #8]
   461a2:	f7ca eda6 	blx	10cf0 <close@plt>
   461a6:	683b      	ldr	r3, [r7, #0]
   461a8:	695b      	ldr	r3, [r3, #20]
   461aa:	f1b3 3fff 	cmp.w	r3, #4294967295	; 0xffffffff
   461ae:	d107      	bne.n	461c0 <TEEC_RegisterSharedMemory+0xdc>
   461b0:	683b      	ldr	r3, [r7, #0]
   461b2:	f04f 32ff 	mov.w	r2, #4294967295	; 0xffffffff
   461b6:	60da      	str	r2, [r3, #12]
   461b8:	230c      	movs	r3, #12
   461ba:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   461be:	e00a      	b.n	461d6 <TEEC_RegisterSharedMemory+0xf2>
   461c0:	683b      	ldr	r3, [r7, #0]
   461c2:	f04f 32ff 	mov.w	r2, #4294967295	; 0xffffffff
   461c6:	619a      	str	r2, [r3, #24]
   461c8:	683b      	ldr	r3, [r7, #0]
   461ca:	68fa      	ldr	r2, [r7, #12]
   461cc:	611a      	str	r2, [r3, #16]
   461ce:	683b      	ldr	r3, [r7, #0]
   461d0:	2200      	movs	r2, #0
   461d2:	771a      	strb	r2, [r3, #28]
   461d4:	2300      	movs	r3, #0
   461d6:	4618      	mov	r0, r3
   461d8:	3710      	adds	r7, #16
   461da:	46bd      	mov	sp, r7
   461dc:	bd80      	pop	{r7, pc}

000461de <TEEC_RegisterSharedMemoryFileDescriptor>:
   461de:	b590      	push	{r4, r7, lr}
   461e0:	b08d      	sub	sp, #52	; 0x34
   461e2:	af00      	add	r7, sp, #0
   461e4:	60f8      	str	r0, [r7, #12]
   461e6:	60b9      	str	r1, [r7, #8]
   461e8:	607a      	str	r2, [r7, #4]
   461ea:	68fb      	ldr	r3, [r7, #12]
   461ec:	2b00      	cmp	r3, #0
   461ee:	d005      	beq.n	461fc <TEEC_RegisterSharedMemoryFileDescriptor+0x1e>
   461f0:	68bb      	ldr	r3, [r7, #8]
   461f2:	2b00      	cmp	r3, #0
   461f4:	d002      	beq.n	461fc <TEEC_RegisterSharedMemoryFileDescriptor+0x1e>
   461f6:	687b      	ldr	r3, [r7, #4]
   461f8:	2b00      	cmp	r3, #0
   461fa:	da03      	bge.n	46204 <TEEC_RegisterSharedMemoryFileDescriptor+0x26>
   461fc:	2306      	movs	r3, #6
   461fe:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   46202:	e03e      	b.n	46282 <TEEC_RegisterSharedMemoryFileDescriptor+0xa4>
   46204:	68bb      	ldr	r3, [r7, #8]
   46206:	689b      	ldr	r3, [r3, #8]
   46208:	2b00      	cmp	r3, #0
   4620a:	d005      	beq.n	46218 <TEEC_RegisterSharedMemoryFileDescriptor+0x3a>
   4620c:	68bb      	ldr	r3, [r7, #8]
   4620e:	689b      	ldr	r3, [r3, #8]
   46210:	f023 0303 	bic.w	r3, r3, #3
   46214:	2b00      	cmp	r3, #0
   46216:	d003      	beq.n	46220 <TEEC_RegisterSharedMemoryFileDescriptor+0x42>
   46218:	2306      	movs	r3, #6
   4621a:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   4621e:	e030      	b.n	46282 <TEEC_RegisterSharedMemoryFileDescriptor+0xa4>
   46220:	f107 0310 	add.w	r3, r7, #16
   46224:	2218      	movs	r2, #24
   46226:	2100      	movs	r1, #0
   46228:	4618      	mov	r0, r3
   4622a:	f7ca ed1a 	blx	10c60 <memset@plt>
   4622e:	687b      	ldr	r3, [r7, #4]
   46230:	ea4f 74e3 	mov.w	r4, r3, asr #31
   46234:	e9c7 3404 	strd	r3, r4, [r7, #16]
   46238:	68fb      	ldr	r3, [r7, #12]
   4623a:	681b      	ldr	r3, [r3, #0]
   4623c:	f107 0210 	add.w	r2, r7, #16
   46240:	f24a 4108 	movw	r1, #41992	; 0xa408
   46244:	f2cc 0118 	movt	r1, #49176	; 0xc018
   46248:	4618      	mov	r0, r3
   4624a:	f7ca ecb0 	blx	10bac <ioctl@plt>
   4624e:	62f8      	str	r0, [r7, #44]	; 0x2c
   46250:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   46252:	2b00      	cmp	r3, #0
   46254:	da03      	bge.n	4625e <TEEC_RegisterSharedMemoryFileDescriptor+0x80>
   46256:	2306      	movs	r3, #6
   46258:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   4625c:	e011      	b.n	46282 <TEEC_RegisterSharedMemoryFileDescriptor+0xa4>
   4625e:	68bb      	ldr	r3, [r7, #8]
   46260:	2200      	movs	r2, #0
   46262:	601a      	str	r2, [r3, #0]
   46264:	68bb      	ldr	r3, [r7, #8]
   46266:	2200      	movs	r2, #0
   46268:	615a      	str	r2, [r3, #20]
   4626a:	68bb      	ldr	r3, [r7, #8]
   4626c:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   4626e:	619a      	str	r2, [r3, #24]
   46270:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   46272:	68bb      	ldr	r3, [r7, #8]
   46274:	60da      	str	r2, [r3, #12]
   46276:	e9d7 3406 	ldrd	r3, r4, [r7, #24]
   4627a:	461a      	mov	r2, r3
   4627c:	68bb      	ldr	r3, [r7, #8]
   4627e:	605a      	str	r2, [r3, #4]
   46280:	2300      	movs	r3, #0
   46282:	4618      	mov	r0, r3
   46284:	3734      	adds	r7, #52	; 0x34
   46286:	46bd      	mov	sp, r7
   46288:	bd90      	pop	{r4, r7, pc}

0004628a <TEEC_AllocateSharedMemory>:
   4628a:	b580      	push	{r7, lr}
   4628c:	b086      	sub	sp, #24
   4628e:	af02      	add	r7, sp, #8
   46290:	6078      	str	r0, [r7, #4]
   46292:	6039      	str	r1, [r7, #0]
   46294:	687b      	ldr	r3, [r7, #4]
   46296:	2b00      	cmp	r3, #0
   46298:	d002      	beq.n	462a0 <TEEC_AllocateSharedMemory+0x16>
   4629a:	683b      	ldr	r3, [r7, #0]
   4629c:	2b00      	cmp	r3, #0
   4629e:	d103      	bne.n	462a8 <TEEC_AllocateSharedMemory+0x1e>
   462a0:	2306      	movs	r3, #6
   462a2:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   462a6:	e080      	b.n	463aa <TEEC_AllocateSharedMemory+0x120>
   462a8:	683b      	ldr	r3, [r7, #0]
   462aa:	689b      	ldr	r3, [r3, #8]
   462ac:	2b00      	cmp	r3, #0
   462ae:	d005      	beq.n	462bc <TEEC_AllocateSharedMemory+0x32>
   462b0:	683b      	ldr	r3, [r7, #0]
   462b2:	689b      	ldr	r3, [r3, #8]
   462b4:	f023 0303 	bic.w	r3, r3, #3
   462b8:	2b00      	cmp	r3, #0
   462ba:	d003      	beq.n	462c4 <TEEC_AllocateSharedMemory+0x3a>
   462bc:	2306      	movs	r3, #6
   462be:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   462c2:	e072      	b.n	463aa <TEEC_AllocateSharedMemory+0x120>
   462c4:	683b      	ldr	r3, [r7, #0]
   462c6:	685b      	ldr	r3, [r3, #4]
   462c8:	60fb      	str	r3, [r7, #12]
   462ca:	68fb      	ldr	r3, [r7, #12]
   462cc:	2b00      	cmp	r3, #0
   462ce:	d101      	bne.n	462d4 <TEEC_AllocateSharedMemory+0x4a>
   462d0:	2308      	movs	r3, #8
   462d2:	60fb      	str	r3, [r7, #12]
   462d4:	687b      	ldr	r3, [r7, #4]
   462d6:	791b      	ldrb	r3, [r3, #4]
   462d8:	2b00      	cmp	r3, #0
   462da:	d02b      	beq.n	46334 <TEEC_AllocateSharedMemory+0xaa>
   462dc:	68f8      	ldr	r0, [r7, #12]
   462de:	f7ca ec84 	blx	10be8 <malloc@plt>
   462e2:	4603      	mov	r3, r0
   462e4:	461a      	mov	r2, r3
   462e6:	683b      	ldr	r3, [r7, #0]
   462e8:	601a      	str	r2, [r3, #0]
   462ea:	683b      	ldr	r3, [r7, #0]
   462ec:	681b      	ldr	r3, [r3, #0]
   462ee:	2b00      	cmp	r3, #0
   462f0:	d103      	bne.n	462fa <TEEC_AllocateSharedMemory+0x70>
   462f2:	230c      	movs	r3, #12
   462f4:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   462f8:	e057      	b.n	463aa <TEEC_AllocateSharedMemory+0x120>
   462fa:	687b      	ldr	r3, [r7, #4]
   462fc:	6818      	ldr	r0, [r3, #0]
   462fe:	683b      	ldr	r3, [r7, #0]
   46300:	6819      	ldr	r1, [r3, #0]
   46302:	683b      	ldr	r3, [r7, #0]
   46304:	330c      	adds	r3, #12
   46306:	68fa      	ldr	r2, [r7, #12]
   46308:	f7ff f83f 	bl	4538a <teec_shm_register>
   4630c:	60b8      	str	r0, [r7, #8]
   4630e:	68bb      	ldr	r3, [r7, #8]
   46310:	2b00      	cmp	r3, #0
   46312:	da0b      	bge.n	4632c <TEEC_AllocateSharedMemory+0xa2>
   46314:	683b      	ldr	r3, [r7, #0]
   46316:	681b      	ldr	r3, [r3, #0]
   46318:	4618      	mov	r0, r3
   4631a:	f7ca ec2a 	blx	10b70 <free@plt>
   4631e:	683b      	ldr	r3, [r7, #0]
   46320:	2200      	movs	r2, #0
   46322:	601a      	str	r2, [r3, #0]
   46324:	230c      	movs	r3, #12
   46326:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   4632a:	e03e      	b.n	463aa <TEEC_AllocateSharedMemory+0x120>
   4632c:	683b      	ldr	r3, [r7, #0]
   4632e:	68ba      	ldr	r2, [r7, #8]
   46330:	619a      	str	r2, [r3, #24]
   46332:	e030      	b.n	46396 <TEEC_AllocateSharedMemory+0x10c>
   46334:	687b      	ldr	r3, [r7, #4]
   46336:	6818      	ldr	r0, [r3, #0]
   46338:	683b      	ldr	r3, [r7, #0]
   4633a:	330c      	adds	r3, #12
   4633c:	461a      	mov	r2, r3
   4633e:	68f9      	ldr	r1, [r7, #12]
   46340:	f7fe fff8 	bl	45334 <teec_shm_alloc>
   46344:	60b8      	str	r0, [r7, #8]
   46346:	68bb      	ldr	r3, [r7, #8]
   46348:	2b00      	cmp	r3, #0
   4634a:	da03      	bge.n	46354 <TEEC_AllocateSharedMemory+0xca>
   4634c:	230c      	movs	r3, #12
   4634e:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   46352:	e02a      	b.n	463aa <TEEC_AllocateSharedMemory+0x120>
   46354:	2300      	movs	r3, #0
   46356:	9301      	str	r3, [sp, #4]
   46358:	68bb      	ldr	r3, [r7, #8]
   4635a:	9300      	str	r3, [sp, #0]
   4635c:	2301      	movs	r3, #1
   4635e:	2203      	movs	r2, #3
   46360:	68f9      	ldr	r1, [r7, #12]
   46362:	2000      	movs	r0, #0
   46364:	f7ca ec64 	blx	10c30 <mmap@plt>
   46368:	4602      	mov	r2, r0
   4636a:	683b      	ldr	r3, [r7, #0]
   4636c:	601a      	str	r2, [r3, #0]
   4636e:	68b8      	ldr	r0, [r7, #8]
   46370:	f7ca ecbe 	blx	10cf0 <close@plt>
   46374:	683b      	ldr	r3, [r7, #0]
   46376:	681b      	ldr	r3, [r3, #0]
   46378:	f1b3 3fff 	cmp.w	r3, #4294967295	; 0xffffffff
   4637c:	d107      	bne.n	4638e <TEEC_AllocateSharedMemory+0x104>
   4637e:	683b      	ldr	r3, [r7, #0]
   46380:	f04f 32ff 	mov.w	r2, #4294967295	; 0xffffffff
   46384:	60da      	str	r2, [r3, #12]
   46386:	230c      	movs	r3, #12
   46388:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   4638c:	e00d      	b.n	463aa <TEEC_AllocateSharedMemory+0x120>
   4638e:	683b      	ldr	r3, [r7, #0]
   46390:	f04f 32ff 	mov.w	r2, #4294967295	; 0xffffffff
   46394:	619a      	str	r2, [r3, #24]
   46396:	683b      	ldr	r3, [r7, #0]
   46398:	2200      	movs	r2, #0
   4639a:	615a      	str	r2, [r3, #20]
   4639c:	683b      	ldr	r3, [r7, #0]
   4639e:	68fa      	ldr	r2, [r7, #12]
   463a0:	611a      	str	r2, [r3, #16]
   463a2:	683b      	ldr	r3, [r7, #0]
   463a4:	2201      	movs	r2, #1
   463a6:	771a      	strb	r2, [r3, #28]
   463a8:	2300      	movs	r3, #0
   463aa:	4618      	mov	r0, r3
   463ac:	3710      	adds	r7, #16
   463ae:	46bd      	mov	sp, r7
   463b0:	bd80      	pop	{r7, pc}

000463b2 <TEEC_ReleaseSharedMemory>:
   463b2:	b580      	push	{r7, lr}
   463b4:	b082      	sub	sp, #8
   463b6:	af00      	add	r7, sp, #0
   463b8:	6078      	str	r0, [r7, #4]
   463ba:	687b      	ldr	r3, [r7, #4]
   463bc:	2b00      	cmp	r3, #0
   463be:	d04c      	beq.n	4645a <TEEC_ReleaseSharedMemory+0xa8>
   463c0:	687b      	ldr	r3, [r7, #4]
   463c2:	68db      	ldr	r3, [r3, #12]
   463c4:	f1b3 3fff 	cmp.w	r3, #4294967295	; 0xffffffff
   463c8:	d047      	beq.n	4645a <TEEC_ReleaseSharedMemory+0xa8>
   463ca:	687b      	ldr	r3, [r7, #4]
   463cc:	695b      	ldr	r3, [r3, #20]
   463ce:	2b00      	cmp	r3, #0
   463d0:	d008      	beq.n	463e4 <TEEC_ReleaseSharedMemory+0x32>
   463d2:	687b      	ldr	r3, [r7, #4]
   463d4:	695a      	ldr	r2, [r3, #20]
   463d6:	687b      	ldr	r3, [r7, #4]
   463d8:	691b      	ldr	r3, [r3, #16]
   463da:	4619      	mov	r1, r3
   463dc:	4610      	mov	r0, r2
   463de:	f7ca ec52 	blx	10c84 <munmap@plt>
   463e2:	e028      	b.n	46436 <TEEC_ReleaseSharedMemory+0x84>
   463e4:	687b      	ldr	r3, [r7, #4]
   463e6:	681b      	ldr	r3, [r3, #0]
   463e8:	2b00      	cmp	r3, #0
   463ea:	d01b      	beq.n	46424 <TEEC_ReleaseSharedMemory+0x72>
   463ec:	687b      	ldr	r3, [r7, #4]
   463ee:	699b      	ldr	r3, [r3, #24]
   463f0:	2b00      	cmp	r3, #0
   463f2:	db0e      	blt.n	46412 <TEEC_ReleaseSharedMemory+0x60>
   463f4:	687b      	ldr	r3, [r7, #4]
   463f6:	7f1b      	ldrb	r3, [r3, #28]
   463f8:	2b00      	cmp	r3, #0
   463fa:	d004      	beq.n	46406 <TEEC_ReleaseSharedMemory+0x54>
   463fc:	687b      	ldr	r3, [r7, #4]
   463fe:	681b      	ldr	r3, [r3, #0]
   46400:	4618      	mov	r0, r3
   46402:	f7ca ebb6 	blx	10b70 <free@plt>
   46406:	687b      	ldr	r3, [r7, #4]
   46408:	699b      	ldr	r3, [r3, #24]
   4640a:	4618      	mov	r0, r3
   4640c:	f7ca ec70 	blx	10cf0 <close@plt>
   46410:	e011      	b.n	46436 <TEEC_ReleaseSharedMemory+0x84>
   46412:	687b      	ldr	r3, [r7, #4]
   46414:	681a      	ldr	r2, [r3, #0]
   46416:	687b      	ldr	r3, [r7, #4]
   46418:	691b      	ldr	r3, [r3, #16]
   4641a:	4619      	mov	r1, r3
   4641c:	4610      	mov	r0, r2
   4641e:	f7ca ec32 	blx	10c84 <munmap@plt>
   46422:	e008      	b.n	46436 <TEEC_ReleaseSharedMemory+0x84>
   46424:	687b      	ldr	r3, [r7, #4]
   46426:	699b      	ldr	r3, [r3, #24]
   46428:	2b00      	cmp	r3, #0
   4642a:	db04      	blt.n	46436 <TEEC_ReleaseSharedMemory+0x84>
   4642c:	687b      	ldr	r3, [r7, #4]
   4642e:	699b      	ldr	r3, [r3, #24]
   46430:	4618      	mov	r0, r3
   46432:	f7ca ec5e 	blx	10cf0 <close@plt>
   46436:	687b      	ldr	r3, [r7, #4]
   46438:	f04f 32ff 	mov.w	r2, #4294967295	; 0xffffffff
   4643c:	60da      	str	r2, [r3, #12]
   4643e:	687b      	ldr	r3, [r7, #4]
   46440:	2200      	movs	r2, #0
   46442:	615a      	str	r2, [r3, #20]
   46444:	687b      	ldr	r3, [r7, #4]
   46446:	2200      	movs	r2, #0
   46448:	601a      	str	r2, [r3, #0]
   4644a:	687b      	ldr	r3, [r7, #4]
   4644c:	f04f 32ff 	mov.w	r2, #4294967295	; 0xffffffff
   46450:	619a      	str	r2, [r3, #24]
   46452:	687b      	ldr	r3, [r7, #4]
   46454:	2200      	movs	r2, #0
   46456:	771a      	strb	r2, [r3, #28]
   46458:	e000      	b.n	4645c <TEEC_ReleaseSharedMemory+0xaa>
   4645a:	bf00      	nop
   4645c:	3708      	adds	r7, #8
   4645e:	46bd      	mov	sp, r7
   46460:	bd80      	pop	{r7, pc}
   46462:	bf00      	nop

00046464 <_dprintf>:
   46464:	b590      	push	{r4, r7, lr}
   46466:	b0cd      	sub	sp, #308	; 0x134
   46468:	af04      	add	r7, sp, #16
   4646a:	f107 040c 	add.w	r4, r7, #12
   4646e:	6020      	str	r0, [r4, #0]
   46470:	f107 0008 	add.w	r0, r7, #8
   46474:	6001      	str	r1, [r0, #0]
   46476:	1d39      	adds	r1, r7, #4
   46478:	600a      	str	r2, [r1, #0]
   4647a:	463a      	mov	r2, r7
   4647c:	6013      	str	r3, [r2, #0]
   4647e:	4c31      	ldr	r4, [pc, #196]	; (46544 <_dprintf+0xe0>)
   46480:	447c      	add	r4, pc
   46482:	2300      	movs	r3, #0
   46484:	f8c7 311c 	str.w	r3, [r7, #284]	; 0x11c
   46488:	f107 030c 	add.w	r3, r7, #12
   4648c:	681b      	ldr	r3, [r3, #0]
   4648e:	2b00      	cmp	r3, #0
   46490:	d028      	beq.n	464e4 <_dprintf+0x80>
   46492:	20e0      	movs	r0, #224	; 0xe0
   46494:	f7ca ebc6 	blx	10c24 <syscall@plt>
   46498:	f8c7 0118 	str.w	r0, [r7, #280]	; 0x118
   4649c:	4b2a      	ldr	r3, [pc, #168]	; (46548 <_dprintf+0xe4>)
   4649e:	447b      	add	r3, pc
   464a0:	461a      	mov	r2, r3
   464a2:	1d3b      	adds	r3, r7, #4
   464a4:	681b      	ldr	r3, [r3, #0]
   464a6:	f852 2023 	ldr.w	r2, [r2, r3, lsl #2]
   464aa:	f107 0018 	add.w	r0, r7, #24
   464ae:	f107 0308 	add.w	r3, r7, #8
   464b2:	681b      	ldr	r3, [r3, #0]
   464b4:	9303      	str	r3, [sp, #12]
   464b6:	f107 030c 	add.w	r3, r7, #12
   464ba:	681b      	ldr	r3, [r3, #0]
   464bc:	9302      	str	r3, [sp, #8]
   464be:	463b      	mov	r3, r7
   464c0:	681b      	ldr	r3, [r3, #0]
   464c2:	9301      	str	r3, [sp, #4]
   464c4:	f8d7 3118 	ldr.w	r3, [r7, #280]	; 0x118
   464c8:	9300      	str	r3, [sp, #0]
   464ca:	4613      	mov	r3, r2
   464cc:	4a1f      	ldr	r2, [pc, #124]	; (4654c <_dprintf+0xe8>)
   464ce:	447a      	add	r2, pc
   464d0:	f44f 7180 	mov.w	r1, #256	; 0x100
   464d4:	f7ca ebbe 	blx	10c54 <snprintf@plt>
   464d8:	f8c7 011c 	str.w	r0, [r7, #284]	; 0x11c
   464dc:	f8d7 311c 	ldr.w	r3, [r7, #284]	; 0x11c
   464e0:	2b00      	cmp	r3, #0
   464e2:	db28      	blt.n	46536 <_dprintf+0xd2>
   464e4:	f8d7 311c 	ldr.w	r3, [r7, #284]	; 0x11c
   464e8:	2bff      	cmp	r3, #255	; 0xff
   464ea:	d81a      	bhi.n	46522 <_dprintf+0xbe>
   464ec:	f507 729a 	add.w	r2, r7, #308	; 0x134
   464f0:	f107 0314 	add.w	r3, r7, #20
   464f4:	601a      	str	r2, [r3, #0]
   464f6:	f8d7 311c 	ldr.w	r3, [r7, #284]	; 0x11c
   464fa:	f107 0218 	add.w	r2, r7, #24
   464fe:	18d0      	adds	r0, r2, r3
   46500:	f8d7 311c 	ldr.w	r3, [r7, #284]	; 0x11c
   46504:	f5c3 7180 	rsb	r1, r3, #256	; 0x100
   46508:	f107 0314 	add.w	r3, r7, #20
   4650c:	681b      	ldr	r3, [r3, #0]
   4650e:	f8d7 2130 	ldr.w	r2, [r7, #304]	; 0x130
   46512:	f7ca ebd6 	blx	10cc0 <vsnprintf@plt>
   46516:	f8c7 011c 	str.w	r0, [r7, #284]	; 0x11c
   4651a:	f8d7 311c 	ldr.w	r3, [r7, #284]	; 0x11c
   4651e:	2b00      	cmp	r3, #0
   46520:	db0b      	blt.n	4653a <_dprintf+0xd6>
   46522:	4b0b      	ldr	r3, [pc, #44]	; (46550 <_dprintf+0xec>)
   46524:	58e3      	ldr	r3, [r4, r3]
   46526:	681a      	ldr	r2, [r3, #0]
   46528:	f107 0318 	add.w	r3, r7, #24
   4652c:	4611      	mov	r1, r2
   4652e:	4618      	mov	r0, r3
   46530:	f7ca ebd2 	blx	10cd8 <fputs@plt>
   46534:	e002      	b.n	4653c <_dprintf+0xd8>
   46536:	bf00      	nop
   46538:	e000      	b.n	4653c <_dprintf+0xd8>
   4653a:	bf00      	nop
   4653c:	f507 7792 	add.w	r7, r7, #292	; 0x124
   46540:	46bd      	mov	sp, r7
   46542:	bd90      	pop	{r4, r7, pc}
   46544:	00010b7c 	andeq	r0, r1, ip, ror fp
   46548:	00010a5a 	andeq	r0, r1, sl, asr sl
   4654c:	000008b2 			; <UNDEFINED> instruction: 0x000008b2
   46550:	000000d8 	ldrdeq	r0, [r0], -r8

00046554 <dump_buffer>:
   46554:	b480      	push	{r7}
   46556:	b085      	sub	sp, #20
   46558:	af00      	add	r7, sp, #0
   4655a:	60f8      	str	r0, [r7, #12]
   4655c:	60b9      	str	r1, [r7, #8]
   4655e:	607a      	str	r2, [r7, #4]
   46560:	bf00      	nop
   46562:	3714      	adds	r7, #20
   46564:	46bd      	mov	sp, r7
   46566:	f85d 7b04 	ldr.w	r7, [sp], #4
   4656a:	4770      	bx	lr

Disassembly of section .trampoline:

0004656c <__cfv_icall>:
   4656c:	e24dd080 	sub	sp, sp, #128	; 0x80
   46570:	e58d0000 	str	r0, [sp]
   46574:	e58d1008 	str	r1, [sp, #8]
   46578:	e58d2010 	str	r2, [sp, #16]
   4657c:	e58d3018 	str	r3, [sp, #24]
   46580:	e58d4020 	str	r4, [sp, #32]
   46584:	e58d5028 	str	r5, [sp, #40]	; 0x28
   46588:	e58d6030 	str	r6, [sp, #48]	; 0x30
   4658c:	e58d7038 	str	r7, [sp, #56]	; 0x38
   46590:	e58d8040 	str	r8, [sp, #64]	; 0x40
   46594:	e58d9048 	str	r9, [sp, #72]	; 0x48
   46598:	e58da050 	str	sl, [sp, #80]	; 0x50
   4659c:	e58db058 	str	fp, [sp, #88]	; 0x58
   465a0:	e58dc060 	str	ip, [sp, #96]	; 0x60
   465a4:	e58dd068 	str	sp, [sp, #104]	; 0x68
   465a8:	e58de070 	str	lr, [sp, #112]	; 0x70
   465ac:	e10f4000 	mrs	r4, CPSR
   465b0:	e58d4078 	str	r4, [sp, #120]	; 0x78
   465b4:	fafff91b 	blx	44a28 <view_switch_to_rd_and_log>
   465b8:	e59d4078 	ldr	r4, [sp, #120]	; 0x78
   465bc:	e129f004 	msr	CPSR_fc, r4
   465c0:	e59d0000 	ldr	r0, [sp]
   465c4:	e59d1008 	ldr	r1, [sp, #8]
   465c8:	e59d2010 	ldr	r2, [sp, #16]
   465cc:	e59d3018 	ldr	r3, [sp, #24]
   465d0:	e59d4020 	ldr	r4, [sp, #32]
   465d4:	e59d5028 	ldr	r5, [sp, #40]	; 0x28
   465d8:	e59d6030 	ldr	r6, [sp, #48]	; 0x30
   465dc:	e59d7038 	ldr	r7, [sp, #56]	; 0x38
   465e0:	e59d8040 	ldr	r8, [sp, #64]	; 0x40
   465e4:	e59d9048 	ldr	r9, [sp, #72]	; 0x48
   465e8:	e59da050 	ldr	sl, [sp, #80]	; 0x50
   465ec:	e59db058 	ldr	fp, [sp, #88]	; 0x58
   465f0:	e59dc060 	ldr	ip, [sp, #96]	; 0x60
   465f4:	e59dd068 	ldr	sp, [sp, #104]	; 0x68
   465f8:	e59de070 	ldr	lr, [sp, #112]	; 0x70
   465fc:	e28dd080 	add	sp, sp, #128	; 0x80
   46600:	e1a0f00e 	mov	pc, lr

00046604 <__cfv_icall_blx>:
   46604:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   46608:	e52d0004 	push	{r0}		; (str r0, [sp, #-4]!)
   4660c:	e52d1004 	push	{r1}		; (str r1, [sp, #-4]!)
   46610:	e52d2004 	push	{r2}		; (str r2, [sp, #-4]!)
   46614:	e52d3004 	push	{r3}		; (str r3, [sp, #-4]!)
   46618:	e1a0000e 	mov	r0, lr
   4661c:	fafff809 	blx	44648 <cfv_icall_blx>
   46620:	e49d3004 	pop	{r3}		; (ldr r3, [sp], #4)
   46624:	e49d2004 	pop	{r2}		; (ldr r2, [sp], #4)
   46628:	e49d1004 	pop	{r1}		; (ldr r1, [sp], #4)
   4662c:	e49d0004 	pop	{r0}		; (ldr r0, [sp], #4)
   46630:	e49df004 	pop	{pc}		; (ldr pc, [sp], #4)

00046634 <__cfv_icall_blx_pre>:
   46634:	e92d400f 	push	{r0, r1, r2, r3, lr}
   46638:	e1a0000e 	mov	r0, lr
   4663c:	fafff82a 	blx	446ec <cfv_icall_blx_pre>
   46640:	e8bd800f 	pop	{r0, r1, r2, r3, pc}

00046644 <__cfv_icall_cond_dirbranch>:
   46644:	e92d400f 	push	{r0, r1, r2, r3, lr}
   46648:	e1a0000e 	mov	r0, lr
   4664c:	fafff86e 	blx	4480c <cfv_icall_bc_blc>
   46650:	e8bd800f 	pop	{r0, r1, r2, r3, pc}

00046654 <__cfv_icall_ldmia_ret>:
   46654:	e92d400f 	push	{r0, r1, r2, r3, lr}
   46658:	e1a0000e 	mov	r0, lr
   4665c:	fafff892 	blx	448ac <cfv_icall_ldmia_ret>
   46660:	e8bd400f 	pop	{r0, r1, r2, r3, lr}

Disassembly of section .fini:

00046664 <_fini>:
   46664:	e92d4008 	push	{r3, lr}
   46668:	e8bd8008 	pop	{r3, pc}

Disassembly of section .rodata:

0004666c <mLBolusStepsLength>:
   4666c:	00000009 	andeq	r0, r0, r9
   46670:	69727953 	ldmdbvs	r2!, {r0, r1, r4, r6, r8, fp, ip, sp, lr}^
   46674:	5065676e 	rsbpl	r6, r5, lr, ror #14
   46678:	20706d75 	rsbscs	r6, r0, r5, ror sp
   4667c:	302e3276 	eorcc	r3, lr, r6, ror r2
   46680:	424c6d00 	submi	r6, ip, #0, 26
   46684:	73756c6f 	cmnvc	r5, #28416	; 0x6f00
   46688:	25203d20 	strcs	r3, [r0, #-3360]!	; 0xfffff2e0
   4668c:	74202c66 	strtvc	r2, [r0], #-3174	; 0xfffff39a
   46690:	20656d69 	rsbcs	r6, r5, r9, ror #26
   46694:	63657375 	cmnvs	r5, #-738197503	; 0xd4000001
   46698:	25203a73 	strcs	r3, [r0, #-2675]!	; 0xfffff58d
   4669c:	000a756c 	andeq	r7, sl, ip, ror #10
   466a0:	61766e49 	cmnvs	r6, r9, asr #28
   466a4:	2064696c 	rsbcs	r6, r4, ip, ror #18
   466a8:	6d6d6f63 	stclvs	15, cr6, [sp, #-396]!	; 0xfffffe74
   466ac:	3a646e61 	bcc	1962038 <ringBuffer+0x190a330>
   466b0:	5d005b20 	vstrpl	d5, [r0, #-128]	; 0xffffff80
   466b4:	7355000a 	cmpvc	r5, #10
   466b8:	25206465 	strcs	r6, [r0, #-1125]!	; 0xfffffb9b
   466bc:	64252e64 	strtvs	r2, [r5], #-3684	; 0xfffff19c
   466c0:	004c6d20 	subeq	r6, ip, r0, lsr #26
   466c4:	756c6f42 	strbvc	r6, [ip, #-3906]!	; 0xfffff0be
   466c8:	64252073 	strtvs	r2, [r5], #-115	; 0xffffff8d
   466cc:	2064252e 	rsbcs	r2, r4, lr, lsr #10
   466d0:	4d004c6d 	stcmi	12, cr4, [r0, #-436]	; 0xfffffe4c
   466d4:	3e756e65 	cdpcc	14, 7, cr6, cr5, cr5, {3}
   466d8:	6c6f4220 	sfmvs	f4, 2, [pc], #-128	; 46660 <__cfv_icall_ldmia_ret+0xc>
   466dc:	74537375 	ldrbvc	r7, [r3], #-885	; 0xfffffc8b
   466e0:	25007065 	strcs	r7, [r0, #-101]	; 0xffffff9b
   466e4:	64252e64 	strtvs	r2, [r5], #-3684	; 0xfffff19c
   466e8:	726f6600 	rsbvc	r6, pc, #0, 12
   466ec:	64726177 	ldrbtvs	r6, [r2], #-375	; 0xfffffe89
   466f0:	7261745f 	rsbvc	r7, r1, #1593835520	; 0x5f000000
   466f4:	20746567 	rsbscs	r6, r4, r7, ror #10
   466f8:	63657865 	cmnvs	r5, #6619136	; 0x650000
   466fc:	6e697475 	mcrvs	4, 3, r7, cr9, cr5, {3}
   46700:	000a2067 	andeq	r2, sl, r7, rrx
   46704:	72617453 	rsbvc	r7, r1, #1392508928	; 0x53000000
   46708:	676e6974 			; <UNDEFINED> instruction: 0x676e6974
   4670c:	72797320 	rsbsvc	r7, r9, #32, 6	; 0x80000000
   46710:	65676e69 	strbvs	r6, [r7, #-3689]!	; 0xfffff197
   46714:	6d757020 	ldclvs	0, cr7, [r5, #-128]!	; 0xffffff80
   46718:	68000a70 	stmdavs	r0, {r4, r5, r6, r9, fp}
   4671c:	68686868 	stmdavs	r8!, {r3, r5, r6, fp, sp, lr}^
   46720:	68686868 	stmdavs	r8!, {r3, r5, r6, fp, sp, lr}^
   46724:	68686868 	stmdavs	r8!, {r3, r5, r6, fp, sp, lr}^
   46728:	45000a68 	strmi	r0, [r0, #-2664]	; 0xfffff598
   4672c:	6e69646e 	cdpvs	4, 6, cr6, cr9, cr14, {3}
   46730:	79732067 	ldmdbvc	r3!, {r0, r1, r2, r5, r6, sp}^
   46734:	676e6972 			; <UNDEFINED> instruction: 0x676e6972
   46738:	75702065 	ldrbvc	r2, [r0, #-101]!	; 0xffffff9b
   4673c:	000a706d 	andeq	r7, sl, sp, rrx
   46740:	28207325 	stmdacs	r0!, {r0, r2, r5, r8, r9, ip, sp, lr}
   46744:	20746e69 	rsbscs	r6, r4, r9, ror #28
   46748:	206e6970 	rsbcs	r6, lr, r0, ror r9
   4674c:	6425203d 	strtvs	r2, [r5], #-61	; 0xffffffc3
   46750:	6e69202c 	cdpvs	0, 6, cr2, cr9, cr12, {1}
   46754:	6f6d2074 	svcvs	0x006d2074
   46758:	3d206564 	cfstr32cc	mvfx6, [r0, #-400]!	; 0xfffffe70
   4675c:	29642520 	stmdbcs	r4!, {r5, r8, sl, sp}^
   46760:	7325000a 			; <UNDEFINED> instruction: 0x7325000a
   46764:	6e692820 	cdpvs	8, 6, cr2, cr9, cr0, {1}
   46768:	69702074 	ldmdbvs	r0!, {r2, r4, r5, r6, sp}^
   4676c:	203d206e 	eorscs	r2, sp, lr, rrx
   46770:	0a296425 	beq	a9f80c <ringBuffer+0xa47b04>
   46774:	20732500 	rsbscs	r2, r3, r0, lsl #10
   46778:	746e6928 	strbtvc	r6, [lr], #-2344	; 0xfffff6d8
   4677c:	75616220 	strbvc	r6, [r1, #-544]!	; 0xfffffde0
   46780:	203d2064 	eorscs	r2, sp, r4, rrx
   46784:	0a296425 	beq	a9f820 <ringBuffer+0xa47b18>
   46788:	28732500 	ldmdacs	r3!, {r8, sl, sp}^
   4678c:	3a632029 	bcc	190e838 <ringBuffer+0x18b6b30>
   46790:	000a6325 	andeq	r6, sl, r5, lsr #6
   46794:	28207325 	stmdacs	r0!, {r0, r2, r5, r8, r9, ip, sp, lr}
   46798:	72616863 	rsbvc	r6, r1, #6488064	; 0x630000
   4679c:	756f2a20 	strbvc	r2, [pc, #-2592]!	; 45d84 <TEEC_OpenSession+0xf6>
   467a0:	74757074 	ldrbtvc	r7, [r5], #-116	; 0xffffff8c
   467a4:	25203d20 	strcs	r3, [r0, #-3360]!	; 0xfffff2e0
   467a8:	69202c73 	stmdbvs	r0!, {r0, r1, r4, r5, r6, sl, fp, sp}
   467ac:	6c20746e 	cfstrsvs	mvf7, [r0], #-440	; 0xfffffe48
   467b0:	3d206e65 	stccc	14, cr6, [r0, #-404]!	; 0xfffffe6c
   467b4:	29642520 	stmdbcs	r4!, {r5, r8, sl, sp}^
   467b8:	6572000a 	ldrbvs	r0, [r2, #-10]!
   467bc:	66206461 	strtvs	r6, [r0], -r1, ror #8
   467c0:	206d6f72 	rsbcs	r6, sp, r2, ror pc
   467c4:	206e6970 	rsbcs	r6, lr, r0, ror r9
   467c8:	000a6425 	andeq	r6, sl, r5, lsr #8
   467cc:	000a7325 	andeq	r7, sl, r5, lsr #6
   467d0:	28207325 	stmdacs	r0!, {r0, r2, r5, r8, r9, ip, sp, lr}
   467d4:	7571694c 	ldrbvc	r6, [r1, #-2380]!	; 0xfffff6b4
   467d8:	72436469 	subvc	r6, r3, #1761607680	; 0x69000000
   467dc:	61747379 	cmnvs	r4, r9, ror r3
   467e0:	202a206c 	eorcs	r2, sl, ip, rrx
   467e4:	2064636c 	rsbcs	r6, r4, ip, ror #6
   467e8:	7830203d 	ldmdavc	r0!, {r0, r2, r3, r4, r5, sp}
   467ec:	202c7825 	eorcs	r7, ip, r5, lsr #16
   467f0:	69736e75 	ldmdbvs	r3!, {r0, r2, r4, r5, r6, r9, sl, fp, sp, lr}^
   467f4:	64656e67 	strbtvs	r6, [r5], #-3687	; 0xfffff199
   467f8:	746e6920 	strbtvc	r6, [lr], #-2336	; 0xfffff6e0
   467fc:	6c6f6320 	stclvs	3, cr6, [pc], #-128	; 46784 <mLBolusStepsLength+0x118>
   46800:	203d2073 	eorscs	r2, sp, r3, ror r0
   46804:	202c7525 	eorcs	r7, ip, r5, lsr #10
   46808:	69736e75 	ldmdbvs	r3!, {r0, r2, r4, r5, r6, r9, sl, fp, sp, lr}^
   4680c:	64656e67 	strbtvs	r6, [r5], #-3687	; 0xfffff199
   46810:	746e6920 	strbtvc	r6, [lr], #-2336	; 0xfffff6e0
   46814:	776f7220 	strbvc	r7, [pc, -r0, lsr #4]!
   46818:	203d2073 	eorscs	r2, sp, r3, ror r0
   4681c:	0a297525 	beq	aa3cb8 <ringBuffer+0xa4bfb0>
   46820:	20732500 	rsbscs	r2, r3, r0, lsl #10
   46824:	71694c28 	cmnvc	r9, r8, lsr #24
   46828:	43646975 	cmnmi	r4, #1916928	; 0x1d4000
   4682c:	74737972 	ldrbtvc	r7, [r3], #-2418	; 0xfffff68e
   46830:	2a206c61 	bcs	8619bc <ringBuffer+0x809cb4>
   46834:	64636c20 	strbtvs	r6, [r3], #-3104	; 0xfffff3e0
   46838:	30203d20 	eorcc	r3, r0, r0, lsr #26
   4683c:	0a782578 	beq	1e4fe24 <ringBuffer+0x1df811c>
   46840:	20732500 	rsbscs	r2, r3, r0, lsl #10
   46844:	71694c28 	cmnvc	r9, r8, lsr #24
   46848:	43646975 	cmnmi	r4, #1916928	; 0x1d4000
   4684c:	74737972 	ldrbtvc	r7, [r3], #-2418	; 0xfffff68e
   46850:	2a206c61 	bcs	8619dc <ringBuffer+0x809cd4>
   46854:	64636c20 	strbtvs	r6, [r3], #-3104	; 0xfffff3e0
   46858:	30203d20 	eorcc	r3, r0, r0, lsr #26
   4685c:	2c782578 	cfldr64cs	mvdx2, [r8], #-480	; 0xfffffe20
   46860:	61686320 	cmnvs	r8, r0, lsr #6
   46864:	6f202a72 	svcvs	0x00202a72
   46868:	75707475 	ldrbvc	r7, [r0, #-1141]!	; 0xfffffb8b
   4686c:	203d2074 	eorscs	r2, sp, r4, ror r0
   46870:	202c7325 	eorcs	r7, ip, r5, lsr #6
   46874:	20746e69 	rsbscs	r6, r4, r9, ror #28
   46878:	206e656c 	rsbcs	r6, lr, ip, ror #10
   4687c:	6425203d 	strtvs	r2, [r5], #-61	; 0xffffffc3
   46880:	25000a29 	strcs	r0, [r0, #-2601]	; 0xfffff5d7
   46884:	4c282073 	stcmi	0, cr2, [r8], #-460	; 0xfffffe34
   46888:	69757169 	ldmdbvs	r5!, {r0, r3, r5, r6, r8, ip, sp, lr}^
   4688c:	79724364 	ldmdbvc	r2!, {r2, r5, r6, r8, r9, lr}^
   46890:	6c617473 	cfstrdvs	mvd7, [r1], #-460	; 0xfffffe34
   46894:	6c202a20 			; <UNDEFINED> instruction: 0x6c202a20
   46898:	3d206463 	cfstrscc	mvf6, [r0, #-396]!	; 0xfffffe74
   4689c:	25783020 	ldrbcs	r3, [r8, #-32]!	; 0xffffffe0
   468a0:	69202c78 	stmdbvs	r0!, {r3, r4, r5, r6, sl, fp, sp}
   468a4:	7820746e 	stmdavc	r0!, {r1, r2, r3, r5, r6, sl, ip, sp, lr}
   468a8:	25203d20 	strcs	r3, [r0, #-3360]!	; 0xfffff2e0
   468ac:	69202c64 	stmdbvs	r0!, {r2, r5, r6, sl, fp, sp}
   468b0:	7920746e 	stmdbvc	r0!, {r1, r2, r3, r5, r6, sl, ip, sp, lr}
   468b4:	25203d20 	strcs	r3, [r0, #-3360]!	; 0xfffff2e0
   468b8:	00000a64 	andeq	r0, r0, r4, ror #20

000468bc <blake2s_IV>:
   468bc:	6a09e667 	bvs	2c0260 <ringBuffer+0x268558>
   468c0:	bb67ae85 	bllt	1a322dc <ringBuffer+0x19da5d4>
   468c4:	3c6ef372 	stclcc	3, cr15, [lr], #-456	; 0xfffffe38
   468c8:	a54ff53a 	strbge	pc, [pc, #-1338]	; 46396 <TEEC_AllocateSharedMemory+0x10c>	; <UNPREDICTABLE>
   468cc:	510e527f 	tstpl	lr, pc, ror r2
   468d0:	9b05688c 	blls	1a0b08 <ringBuffer+0x148e00>
   468d4:	1f83d9ab 	svcne	0x0083d9ab
   468d8:	5be0cd19 	blpl	ff879d44 <__bss_end__+0xf5f8b740>

000468dc <blake2s_sigma>:
   468dc:	03020100 	movweq	r0, #8448	; 0x2100
   468e0:	07060504 	streq	r0, [r6, -r4, lsl #10]
   468e4:	0b0a0908 	bleq	2c8d0c <ringBuffer+0x271004>
   468e8:	0f0e0d0c 	svceq	0x000e0d0c
   468ec:	08040a0e 	stmdaeq	r4, {r1, r2, r3, r9, fp}
   468f0:	060d0f09 	streq	r0, [sp], -r9, lsl #30
   468f4:	02000c01 	andeq	r0, r0, #256	; 0x100
   468f8:	0305070b 	movweq	r0, #22283	; 0x570b
   468fc:	000c080b 	andeq	r0, ip, fp, lsl #16
   46900:	0d0f0205 	sfmeq	f0, 4, [pc, #-20]	; 468f4 <blake2s_sigma+0x18>
   46904:	06030e0a 	streq	r0, [r3], -sl, lsl #28
   46908:	04090107 	streq	r0, [r9], #-263	; 0xfffffef9
   4690c:	01030907 	tsteq	r3, r7, lsl #18
   46910:	0e0b0c0d 	cdpeq	12, 0, cr0, cr11, cr13, {0}
   46914:	0a050602 	beq	188124 <ringBuffer+0x13041c>
   46918:	080f0004 	stmdaeq	pc, {r2}	; <UNPREDICTABLE>
   4691c:	07050009 	streq	r0, [r5, -r9]
   46920:	0f0a0402 	svceq	0x000a0402
   46924:	0c0b010e 	stfeqs	f0, [fp], {14}
   46928:	0d030806 	stceq	8, cr0, [r3, #-24]	; 0xffffffe8
   4692c:	0a060c02 	beq	1c993c <ringBuffer+0x171c34>
   46930:	03080b00 	movweq	r0, #35584	; 0x8b00
   46934:	05070d04 	streq	r0, [r7, #-3332]	; 0xfffff2fc
   46938:	09010e0f 	stmdbeq	r1, {r0, r1, r2, r3, r9, sl, fp}
   4693c:	0f01050c 	svceq	0x0001050c
   46940:	0a040d0e 	beq	149d80 <ringBuffer+0xf2078>
   46944:	03060700 	movweq	r0, #26368	; 0x6700
   46948:	0b080209 	bleq	247174 <ringBuffer+0x1ef46c>
   4694c:	0e070b0d 	vmlaeq.f64	d0, d7, d13
   46950:	0903010c 	stmdbeq	r3, {r2, r3, r8}
   46954:	040f0005 	streq	r0, [pc], #-5	; 4695c <blake2s_sigma+0x80>
   46958:	0a020608 	beq	c8180 <ringBuffer+0x70478>
   4695c:	090e0f06 	stmdbeq	lr, {r1, r2, r8, r9, sl, fp}
   46960:	0800030b 	stmdaeq	r0, {r0, r1, r3, r8, r9}
   46964:	070d020c 	streq	r0, [sp, -ip, lsl #4]
   46968:	050a0401 	streq	r0, [sl, #-1025]	; 0xfffffbff
   4696c:	0408020a 	streq	r0, [r8], #-522	; 0xfffffdf6
   46970:	05010607 	streq	r0, [r1, #-1543]	; 0xfffff9f9
   46974:	0e090b0f 	vmlaeq.f64	d0, d9, d15
   46978:	000d0c03 	andeq	r0, sp, r3, lsl #24
   4697c:	66667562 	strbtvs	r7, [r6], -r2, ror #10
   46980:	69207265 	stmdbvs	r0!, {r0, r2, r5, r6, r9, ip, sp, lr}
   46984:	75662073 	strbvc	r2, [r6, #-115]!	; 0xffffff8d
   46988:	00006c6c 	andeq	r6, r0, ip, ror #24
   4698c:	21212121 			; <UNDEFINED> instruction: 0x21212121
   46990:	21212121 			; <UNDEFINED> instruction: 0x21212121
   46994:	21212121 			; <UNDEFINED> instruction: 0x21212121
   46998:	21212121 			; <UNDEFINED> instruction: 0x21212121
   4699c:	494e4150 	stmdbmi	lr, {r4, r6, r8, lr}^
   469a0:	21212143 			; <UNDEFINED> instruction: 0x21212143
   469a4:	21212121 			; <UNDEFINED> instruction: 0x21212121
   469a8:	21212121 			; <UNDEFINED> instruction: 0x21212121
   469ac:	21212121 			; <UNDEFINED> instruction: 0x21212121
   469b0:	00000021 	andeq	r0, r0, r1, lsr #32
   469b4:	21212121 			; <UNDEFINED> instruction: 0x21212121
   469b8:	21212121 			; <UNDEFINED> instruction: 0x21212121
   469bc:	21212121 			; <UNDEFINED> instruction: 0x21212121
   469c0:	21212121 			; <UNDEFINED> instruction: 0x21212121
   469c4:	5f647766 	svcpl	0x00647766
   469c8:	69646e69 	stmdbvs	r4!, {r0, r3, r5, r6, r9, sl, fp, sp, lr}^
   469cc:	74636572 	strbtvc	r6, [r3], #-1394	; 0xfffffa8e
   469d0:	6673745f 			; <UNDEFINED> instruction: 0x6673745f
   469d4:	726f7720 	rsbvc	r7, pc, #32, 14	; 0x800000
   469d8:	0000736b 	andeq	r7, r0, fp, ror #6
   469dc:	2b2b2b2b 	blcs	b11690 <ringBuffer+0xab9988>
   469e0:	2b2b2b2b 	blcs	b11694 <ringBuffer+0xab998c>
   469e4:	746e632b 	strbtvc	r6, [lr], #-811	; 0xfffffcd5
   469e8:	2b64253a 	blcs	194fed8 <ringBuffer+0x18f81d0>
   469ec:	2b2b2b2b 	blcs	b116a0 <ringBuffer+0xab9998>
   469f0:	2b2b2b2b 	blcs	b116a4 <ringBuffer+0xab999c>
   469f4:	00000a2b 	andeq	r0, r0, fp, lsr #20
   469f8:	74696e49 	strbtvc	r6, [r9], #-3657	; 0xfffff1b7
   469fc:	696c6169 	stmdbvs	ip!, {r0, r3, r5, r6, r8, sp, lr}^
   46a00:	6120657a 			; <UNDEFINED> instruction: 0x6120657a
   46a04:	6e6f6320 	cdpvs	3, 6, cr6, cr15, cr0, {1}
   46a08:	74786574 	ldrbtvc	r6, [r8], #-1396	; 0xfffffa8c
   46a0c:	6f726620 	svcvs	0x00726620
   46a10:	7375206d 	cmnvc	r5, #109	; 0x6d
   46a14:	73207265 			; <UNDEFINED> instruction: 0x73207265
   46a18:	65636170 	strbvs	r6, [r3, #-368]!	; 0xfffffe90
   46a1c:	00000021 	andeq	r0, r0, r1, lsr #32
   46a20:	43454554 	movtmi	r4, #21844	; 0x5554
   46a24:	696e495f 	stmdbvs	lr!, {r0, r1, r2, r3, r4, r6, r8, fp, lr}^
   46a28:	6c616974 			; <UNDEFINED> instruction: 0x6c616974
   46a2c:	43657a69 	cmnmi	r5, #430080	; 0x69000
   46a30:	65746e6f 	ldrbvs	r6, [r4, #-3695]!	; 0xfffff191
   46a34:	66207478 			; <UNDEFINED> instruction: 0x66207478
   46a38:	656c6961 	strbvs	r6, [ip, #-2401]!	; 0xfffff69f
   46a3c:	69772064 	ldmdbvs	r7!, {r2, r5, r6, sp}^
   46a40:	63206874 			; <UNDEFINED> instruction: 0x63206874
   46a44:	2065646f 	rsbcs	r6, r5, pc, ror #8
   46a48:	78257830 	stmdavc	r5!, {r4, r5, fp, ip, sp, lr}
   46a4c:	00000000 	andeq	r0, r0, r0
   46a50:	43454554 	movtmi	r4, #21844	; 0x5554
   46a54:	65704f5f 	ldrbvs	r4, [r0, #-3935]!	; 0xfffff0a1
   46a58:	7365736e 	cmnvc	r5, #-1207959551	; 0xb8000001
   46a5c:	6e6f6973 			; <UNDEFINED> instruction: 0x6e6f6973
   46a60:	69616620 	stmdbvs	r1!, {r5, r9, sl, sp, lr}^
   46a64:	2064656c 	rsbcs	r6, r4, ip, ror #10
   46a68:	68746977 	ldmdavs	r4!, {r0, r1, r2, r4, r5, r6, r8, fp, sp, lr}^
   46a6c:	646f6320 	strbtvs	r6, [pc], #-800	; 46a74 <blake2s_sigma+0x198>
   46a70:	78302065 	ldmdavc	r0!, {r0, r2, r5, r6, sp}
   46a74:	6f207825 	svcvs	0x00207825
   46a78:	69676972 	stmdbvs	r7!, {r1, r4, r5, r6, r8, fp, sp, lr}^
   46a7c:	7830206e 	ldmdavc	r0!, {r1, r2, r3, r5, r6, sp}
   46a80:	00007825 	andeq	r7, r0, r5, lsr #16
   46a84:	43454554 	movtmi	r4, #21844	; 0x5554
   46a88:	766e495f 			; <UNDEFINED> instruction: 0x766e495f
   46a8c:	43656b6f 	cmnmi	r5, #113664	; 0x1bc00
   46a90:	616d6d6f 	cmnvs	sp, pc, ror #26
   46a94:	6620646e 	strtvs	r6, [r0], -lr, ror #8
   46a98:	656c6961 	strbvs	r6, [ip, #-2401]!	; 0xfffff69f
   46a9c:	69772064 	ldmdbvs	r7!, {r2, r5, r6, sp}^
   46aa0:	63206874 			; <UNDEFINED> instruction: 0x63206874
   46aa4:	2065646f 	rsbcs	r6, r5, pc, ror #8
   46aa8:	78257830 	stmdavc	r5!, {r4, r5, fp, ip, sp, lr}
   46aac:	69726f20 	ldmdbvs	r2!, {r5, r8, r9, sl, fp, sp, lr}^
   46ab0:	206e6967 	rsbcs	r6, lr, r7, ror #18
   46ab4:	78257830 	stmdavc	r5!, {r4, r5, fp, ip, sp, lr}
   46ab8:	00000000 	andeq	r0, r0, r0
   46abc:	00000061 	andeq	r0, r0, r1, rrx
   46ac0:	25207825 	strcs	r7, [r0, #-2085]!	; 0xfffff7db
   46ac4:	00000a78 	andeq	r0, r0, r8, ror sl
   46ac8:	6c696146 	stfvse	f6, [r9], #-280	; 0xfffffee8
   46acc:	74206465 	strtvc	r6, [r0], #-1125	; 0xfffffb9b
   46ad0:	706f206f 	rsbvc	r2, pc, pc, rrx
   46ad4:	74206e65 	strtvc	r6, [r0], #-3685	; 0xfffff19b
   46ad8:	66206568 	strtvs	r6, [r0], -r8, ror #10
   46adc:	20656c69 	rsbcs	r6, r5, r9, ror #24
   46ae0:	000a7325 	andeq	r7, sl, r5, lsr #6
   46ae4:	78323025 	ldmdavc	r2!, {r0, r2, r5, ip, sp}
   46ae8:	00000000 	andeq	r0, r0, r0
   46aec:	00000072 	andeq	r0, r0, r2, ror r0
   46af0:	656c6544 	strbvs	r6, [ip, #-1348]!	; 0xfffffabc
   46af4:	20646574 	rsbcs	r6, r4, r4, ror r5
   46af8:	63637573 	cmnvs	r3, #482344960	; 0x1cc00000
   46afc:	66737365 	ldrbtvs	r7, [r3], -r5, ror #6
   46b00:	796c6c75 	stmdbvc	ip!, {r0, r2, r4, r5, r6, sl, fp, sp, lr}^
   46b04:	65687420 	strbvs	r7, [r8, #-1056]!	; 0xfffffbe0
   46b08:	6c696620 	stclvs	6, cr6, [r9], #-128	; 0xffffff80
   46b0c:	73252065 			; <UNDEFINED> instruction: 0x73252065
   46b10:	0000000a 	andeq	r0, r0, sl
   46b14:	62616e55 	rsbvs	r6, r1, #1360	; 0x550
   46b18:	7420656c 	strtvc	r6, [r0], #-1388	; 0xfffffa94
   46b1c:	6564206f 	strbvs	r2, [r4, #-111]!	; 0xffffff91
   46b20:	6574656c 	ldrbvs	r6, [r4, #-1388]!	; 0xfffffa94
   46b24:	65687420 	strbvs	r7, [r8, #-1056]!	; 0xfffffbe0
   46b28:	6c696620 	stclvs	6, cr6, [r9], #-128	; 0xffffff80
   46b2c:	73252065 			; <UNDEFINED> instruction: 0x73252065
   46b30:	0000000a 	andeq	r0, r0, sl
   46b34:	00000077 	andeq	r0, r0, r7, ror r0
   46b38:	63637553 	cmnvs	r3, #348127232	; 0x14c00000
   46b3c:	66737365 	ldrbtvs	r7, [r3], -r5, ror #6
   46b40:	796c6c75 	stmdbvc	ip!, {r0, r2, r4, r5, r6, sl, fp, sp, lr}^
   46b44:	65726320 	ldrbvs	r6, [r2, #-800]!	; 0xfffffce0
   46b48:	64657461 	strbtvs	r7, [r5], #-1121	; 0xfffffb9f
   46b4c:	65687420 	strbvs	r7, [r8, #-1056]!	; 0xfffffbe0
   46b50:	6c696620 	stclvs	6, cr6, [r9], #-128	; 0xffffff80
   46b54:	73252065 			; <UNDEFINED> instruction: 0x73252065
   46b58:	0000000a 	andeq	r0, r0, sl
   46b5c:	6c696146 	stfvse	f6, [r9], #-280	; 0xfffffee8
   46b60:	74206465 	strtvc	r6, [r0], #-1125	; 0xfffffb9b
   46b64:	7263206f 	rsbvc	r2, r3, #111	; 0x6f
   46b68:	65746165 	ldrbvs	r6, [r4, #-357]!	; 0xfffffe9b
   46b6c:	65687420 	strbvs	r7, [r8, #-1056]!	; 0xfffffbe0
   46b70:	6c696620 	stclvs	6, cr6, [r9], #-128	; 0xffffff80
   46b74:	73252065 			; <UNDEFINED> instruction: 0x73252065
   46b78:	0000000a 	andeq	r0, r0, sl
   46b7c:	52412f2e 	subpl	r2, r1, #46, 30	; 0xb8
   46b80:	6e695f49 	cdpvs	15, 6, cr5, cr9, cr9, {2}
   46b84:	6d6a5f64 	stclvs	15, cr5, [sl, #-400]!	; 0xfffffe70
   46b88:	78742e70 	ldmdavc	r4!, {r4, r5, r6, r9, sl, fp, sp}^
   46b8c:	00000074 	andeq	r0, r0, r4, ror r0
   46b90:	6c696146 	stfvse	f6, [r9], #-280	; 0xfffffee8
   46b94:	74206465 	strtvc	r6, [r0], #-1125	; 0xfffffb9b
   46b98:	6e69206f 	cdpvs	0, 6, cr2, cr9, cr15, {3}
   46b9c:	6c617469 	cfstrdvs	mvd7, [r1], #-420	; 0xfffffe5c
   46ba0:	65617a69 	strbvs	r7, [r1, #-2665]!	; 0xfffff597
   46ba4:	414c4220 	cmpmi	ip, r0, lsr #4
   46ba8:	7332454b 	teqvc	r2, #314572800	; 0x12c00000
   46bac:	00000000 	andeq	r0, r0, r0
   46bb0:	6c696146 	stfvse	f6, [r9], #-280	; 0xfffffee8
   46bb4:	74206465 	strtvc	r6, [r0], #-1125	; 0xfffffb9b
   46bb8:	7075206f 	rsbsvc	r2, r5, pc, rrx
   46bbc:	65746164 	ldrbvs	r6, [r4, #-356]!	; 0xfffffe9c
   46bc0:	414c4220 	cmpmi	ip, r0, lsr #4
   46bc4:	7332454b 	teqvc	r2, #314572800	; 0x12c00000
   46bc8:	73616820 	cmnvc	r1, #32, 16	; 0x200000
   46bcc:	00000a68 	andeq	r0, r0, r8, ror #20
   46bd0:	75746572 	ldrbvc	r6, [r4, #-1394]!	; 0xfffffa8e
   46bd4:	75206e72 	strvc	r6, [r0, #-3698]!	; 0xfffff18e
   46bd8:	74616470 	strbtvc	r6, [r1], #-1136	; 0xfffffb90
   46bdc:	30203a65 	eorcc	r3, r0, r5, ror #20
   46be0:	0a782578 	beq	1e501c8 <ringBuffer+0x1df84c0>
   46be4:	00000000 	andeq	r0, r0, r0
   46be8:	52412f2e 	subpl	r2, r1, #46, 30	; 0xb8
   46bec:	72625f49 	rsbvc	r5, r2, #292	; 0x124
   46bf0:	68636e61 	stmdavs	r3!, {r0, r5, r6, r9, sl, fp, sp, lr}^
   46bf4:	7478742e 	ldrbtvc	r7, [r8], #-1070	; 0xfffffbd2
   46bf8:	00000000 	andeq	r0, r0, r0
   46bfc:	52412f2e 	subpl	r2, r1, #46, 30	; 0xb8
   46c00:	73745f49 	cmnvc	r4, #292	; 0x124
   46c04:	78742e66 	ldmdavc	r4!, {r1, r2, r5, r6, r9, sl, fp, sp}^
   46c08:	00000074 	andeq	r0, r0, r4, ror r0
   46c0c:	6c696146 	stfvse	f6, [r9], #-280	; 0xfffffee8
   46c10:	74206465 	strtvc	r6, [r0], #-1125	; 0xfffffb9b
   46c14:	6966206f 	stmdbvs	r6!, {r0, r1, r2, r3, r5, r6, sp}^
   46c18:	696c616e 	stmdbvs	ip!, {r1, r2, r3, r5, r6, r8, sp, lr}^
   46c1c:	2064657a 	rsbcs	r6, r4, sl, ror r5
   46c20:	4b414c42 	blmi	1099d30 <ringBuffer+0x1042028>
   46c24:	20733245 	rsbscs	r3, r3, r5, asr #4
   46c28:	68736168 	ldmdavs	r3!, {r3, r5, r6, r8, sp, lr}^
   46c2c:	00000000 	andeq	r0, r0, r0
   46c30:	52412f2e 	subpl	r2, r1, #46, 30	; 0xb8
   46c34:	65725f49 	ldrbvs	r5, [r2, #-3913]!	; 0xfffff0b7
   46c38:	61685f74 	smcvs	34292	; 0x85f4
   46c3c:	742e6873 	strtvc	r6, [lr], #-2163	; 0xfffff78d
   46c40:	00007478 	andeq	r7, r0, r8, ror r4
   46c44:	000a7825 	andeq	r7, sl, r5, lsr #16
   46c48:	00006277 	andeq	r6, r0, r7, ror r2
   46c4c:	52412f2e 	subpl	r2, r1, #46, 30	; 0xb8
   46c50:	73745f49 	cmnvc	r4, #292	; 0x124
   46c54:	6f635f66 	svcvs	0x00635f66
   46c58:	742e646e 	strtvc	r6, [lr], #-1134	; 0xfffffb92
   46c5c:	00007478 	andeq	r7, r0, r8, ror r4

00046c60 <_IO_stdin_used>:
   46c60:	00020001 	andeq	r0, r2, r1
   46c64:	43454554 	movtmi	r4, #21844	; 0x5554
   46c68:	00000000 	andeq	r0, r0, r0
   46c6c:	5f454554 	svcpl	0x00454554
   46c70:	5f434f49 	svcpl	0x00434f49
   46c74:	53524556 	cmppl	r2, #360710144	; 0x15800000
   46c78:	204e4f49 	subcs	r4, lr, r9, asr #30
   46c7c:	6c696166 	stfvse	f6, [r9], #-408	; 0xfffffe68
   46c80:	000a6465 	andeq	r6, sl, r5, ror #8
   46c84:	6574706f 	ldrbvs	r7, [r4, #-111]!	; 0xffffff91
   46c88:	7a742d65 	bvc	1d52224 <ringBuffer+0x1cfa51c>
   46c8c:	00000000 	andeq	r0, r0, r0
   46c90:	7665642f 	strbtvc	r6, [r5], -pc, lsr #8
   46c94:	6565742f 	strbvs	r7, [r5, #-1071]!	; 0xfffffbd1
   46c98:	00757a25 	rsbseq	r7, r5, r5, lsr #20
   46c9c:	5f454554 	svcpl	0x00454554
   46ca0:	5f434f49 	svcpl	0x00434f49
   46ca4:	4e45504f 	cdpmi	0, 4, cr5, cr5, cr15, {2}
   46ca8:	5345535f 	movtpl	r5, #21343	; 0x535f
   46cac:	4e4f4953 			; <UNDEFINED> instruction: 0x4e4f4953
   46cb0:	69616620 	stmdbvs	r1!, {r5, r9, sl, sp, lr}^
   46cb4:	0a64656c 	beq	196026c <ringBuffer+0x1908564>
   46cb8:	00000000 	andeq	r0, r0, r0
   46cbc:	6c696146 	stfvse	f6, [r9], #-280	; 0xfffffee8
   46cc0:	74206465 	strtvc	r6, [r0], #-1125	; 0xfffffb9b
   46cc4:	6c63206f 	stclvs	0, cr2, [r3], #-444	; 0xfffffe44
   46cc8:	2065736f 	rsbcs	r7, r5, pc, ror #6
   46ccc:	73736573 	cmnvc	r3, #482344960	; 0x1cc00000
   46cd0:	206e6f69 	rsbcs	r6, lr, r9, ror #30
   46cd4:	78257830 	stmdavc	r5!, {r4, r5, fp, ip, sp, lr}
   46cd8:	0000000a 	andeq	r0, r0, sl
   46cdc:	5f454554 	svcpl	0x00454554
   46ce0:	5f434f49 	svcpl	0x00434f49
   46ce4:	4f564e49 	svcmi	0x00564e49
   46ce8:	6620454b 	strtvs	r4, [r0], -fp, asr #10
   46cec:	656c6961 	strbvs	r6, [ip, #-2401]!	; 0xfffff69f
   46cf0:	00000a64 	andeq	r0, r0, r4, ror #20
   46cf4:	5f454554 	svcpl	0x00454554
   46cf8:	5f434f49 	svcpl	0x00434f49
   46cfc:	434e4143 	movtmi	r4, #57667	; 0xe143
   46d00:	203a4c45 	eorscs	r4, sl, r5, asr #24
   46d04:	000a7325 	andeq	r7, sl, r5, lsr #6

00046d08 <__func__.8646>:
   46d08:	63656574 	cmnvs	r5, #116, 10	; 0x1d000000
   46d0c:	65706f5f 	ldrbvs	r6, [r0, #-3935]!	; 0xfffff0a1
   46d10:	65645f6e 	strbvs	r5, [r4, #-3950]!	; 0xfffff092
   46d14:	00000076 	andeq	r0, r0, r6, ror r0

00046d18 <__func__.8814>:
   46d18:	43454554 	movtmi	r4, #21844	; 0x5554
   46d1c:	65704f5f 	ldrbvs	r4, [r0, #-3935]!	; 0xfffff0a1
   46d20:	7365536e 	cmnvc	r5, #-1207959551	; 0xb8000001
   46d24:	6e6f6973 			; <UNDEFINED> instruction: 0x6e6f6973
   46d28:	00000000 	andeq	r0, r0, r0

00046d2c <__func__.8819>:
   46d2c:	43454554 	movtmi	r4, #21844	; 0x5554
   46d30:	6f6c435f 	svcvs	0x006c435f
   46d34:	65536573 	ldrbvs	r6, [r3, #-1395]	; 0xfffffa8d
   46d38:	6f697373 	svcvs	0x00697373
   46d3c:	0000006e 	andeq	r0, r0, lr, rrx

00046d40 <__func__.8836>:
   46d40:	43454554 	movtmi	r4, #21844	; 0x5554
   46d44:	766e495f 			; <UNDEFINED> instruction: 0x766e495f
   46d48:	43656b6f 	cmnmi	r5, #113664	; 0x1bc00
   46d4c:	616d6d6f 	cmnvs	sp, pc, ror #26
   46d50:	0000646e 	andeq	r6, r0, lr, ror #8

00046d54 <__func__.8842>:
   46d54:	43454554 	movtmi	r4, #21844	; 0x5554
   46d58:	7165525f 	cmnvc	r5, pc, asr r2
   46d5c:	74736575 	ldrbtvc	r6, [r3], #-1397	; 0xfffffa8b
   46d60:	636e6143 	cmnvs	lr, #-1073741808	; 0xc0000010
   46d64:	616c6c65 	cmnvs	ip, r5, ror #24
   46d68:	6e6f6974 			; <UNDEFINED> instruction: 0x6e6f6974
	...
   46d74:	00525245 	subseq	r5, r2, r5, asr #4
   46d78:	00464e49 	subeq	r4, r6, r9, asr #28
   46d7c:	00474244 	subeq	r4, r7, r4, asr #4
   46d80:	00574c46 	subseq	r4, r7, r6, asr #24
   46d84:	5b207325 	blpl	863a20 <ringBuffer+0x80bd18>
   46d88:	205d6425 	subscs	r6, sp, r5, lsr #8
   46d8c:	253a7325 	ldrcs	r7, [sl, #-805]!	; 0xfffffcdb
   46d90:	64253a73 	strtvs	r3, [r5], #-2675	; 0xfffff58d
   46d94:	地址 0x0000000000046d94 越界。


Disassembly of section .AMI_SFI_Metadata:

00046d97 <.cpt_tb>:
   46d97:	00000000 	andeq	r0, r0, r0
   46d9b:	ffffffff 			; <UNDEFINED> instruction: 0xffffffff
   46d9f:	00000000 	andeq	r0, r0, r0
   46da3:	ffffffff 			; <UNDEFINED> instruction: 0xffffffff
   46da7:	00000000 	andeq	r0, r0, r0
   46dab:	ffffffff 			; <UNDEFINED> instruction: 0xffffffff
   46daf:	00000000 	andeq	r0, r0, r0
   46db3:	ffffffff 			; <UNDEFINED> instruction: 0xffffffff

00046db7 <.cpt_direct_transfer_tb>:
   46db7:	00000000 	andeq	r0, r0, r0
   46dbb:	00000004 	andeq	r0, r0, r4
   46dbf:	00000020 	andeq	r0, r0, r0, lsr #32
   46dc3:	00000004 	andeq	r0, r0, r4
   46dc7:	00000040 	andeq	r0, r0, r0, asr #32
   46dcb:	00000004 	andeq	r0, r0, r4
	...
   46dd7:	00000001 	andeq	r0, r0, r1
   46ddb:	00000000 	andeq	r0, r0, r0
   46ddf:	00000002 	andeq	r0, r0, r2
   46de3:	00000000 	andeq	r0, r0, r0
   46de7:	00000003 	andeq	r0, r0, r3
   46deb:	00000000 	andeq	r0, r0, r0

00046def <.cpt_indirect_transfer_tb>:
   46def:	00000000 	andeq	r0, r0, r0
   46df3:	00000004 	andeq	r0, r0, r4
   46df7:	00000020 	andeq	r0, r0, r0, lsr #32
   46dfb:	00000004 	andeq	r0, r0, r4
   46dff:	00000040 	andeq	r0, r0, r0, asr #32
   46e03:	00000004 	andeq	r0, r0, r4
	...
   46e0f:	00000001 	andeq	r0, r0, r1
   46e13:	00000000 	andeq	r0, r0, r0
   46e17:	00000002 	andeq	r0, r0, r2
   46e1b:	00000000 	andeq	r0, r0, r0
   46e1f:	00000003 	andeq	r0, r0, r3
   46e23:	00000000 	andeq	r0, r0, r0

00046e27 <.cpt_dt_wt_access_tb>:
   46e27:	00000000 	andeq	r0, r0, r0
   46e2b:	00000004 	andeq	r0, r0, r4
   46e2f:	00000020 	andeq	r0, r0, r0, lsr #32
   46e33:	00000004 	andeq	r0, r0, r4
   46e37:	00000040 	andeq	r0, r0, r0, asr #32
   46e3b:	00000004 	andeq	r0, r0, r4
   46e3f:	00000000 	andeq	r0, r0, r0
   46e43:	ffffffff 			; <UNDEFINED> instruction: 0xffffffff
   46e47:	00000001 	andeq	r0, r0, r1
   46e4b:	ffffffff 			; <UNDEFINED> instruction: 0xffffffff
   46e4f:	00000002 	andeq	r0, r0, r2
   46e53:	ffffffff 			; <UNDEFINED> instruction: 0xffffffff
   46e57:	00000003 	andeq	r0, r0, r3
   46e5b:	ffffffff 			; <UNDEFINED> instruction: 0xffffffff

Disassembly of section .ARM.exidx:

00046e60 <.ARM.exidx>:
   46e60:	7ffd91a0 	svcvc	0x00fd91a0
   46e64:	00000001 	andeq	r0, r0, r1

Disassembly of section .eh_frame:

00046e68 <__FRAME_END__>:
   46e68:	00000000 	andeq	r0, r0, r0

Disassembly of section .init_array:

00056ef4 <__frame_dummy_init_array_entry>:
   56ef4:	000451d1 	ldrdeq	r5, [r4], -r1

Disassembly of section .fini_array:

00056ef8 <__do_global_dtors_aux_fini_array_entry>:
   56ef8:	000451b9 			; <UNDEFINED> instruction: 0x000451b9

Disassembly of section .data.rel.ro:

00056efc <trace_level_strings>:
   56efc:	00046d70 	andeq	r6, r4, r0, ror sp
   56f00:	00046d74 	andeq	r6, r4, r4, ror sp
   56f04:	00046d78 	andeq	r6, r4, r8, ror sp
   56f08:	00046d7c 	andeq	r6, r4, ip, ror sp
   56f0c:	00046d80 	andeq	r6, r4, r0, lsl #27

Disassembly of section .dynamic:

00056f10 <_DYNAMIC>:
   56f10:	00000001 	andeq	r0, r0, r1
   56f14:	00000001 	andeq	r0, r0, r1
   56f18:	00000001 	andeq	r0, r0, r1
   56f1c:	00000098 	muleq	r0, r8, r0
   56f20:	0000000c 	andeq	r0, r0, ip
   56f24:	00010b20 	andeq	r0, r1, r0, lsr #22
   56f28:	0000000d 	andeq	r0, r0, sp
   56f2c:	00046664 	andeq	r6, r4, r4, ror #12
   56f30:	00000019 	andeq	r0, r0, r9, lsl r0
   56f34:	00056ef4 	strdeq	r6, [r5], -r4
   56f38:	0000001b 	andeq	r0, r0, fp, lsl r0
   56f3c:	00000004 	andeq	r0, r0, r4
   56f40:	0000001a 	andeq	r0, r0, sl, lsl r0
   56f44:	00056ef8 	strdeq	r6, [r5], -r8
   56f48:	0000001c 	andeq	r0, r0, ip, lsl r0
   56f4c:	00000004 	andeq	r0, r0, r4
   56f50:	6ffffef5 	svcvs	0x00fffef5
   56f54:	00010170 	andeq	r0, r1, r0, ror r1
   56f58:	00000005 	andeq	r0, r0, r5
   56f5c:	000106c8 	andeq	r0, r1, r8, asr #13
   56f60:	00000006 	andeq	r0, r0, r6
   56f64:	00010328 	andeq	r0, r1, r8, lsr #6
   56f68:	0000000a 	andeq	r0, r0, sl
   56f6c:	00000259 	andeq	r0, r0, r9, asr r2
   56f70:	0000000b 	andeq	r0, r0, fp
   56f74:	00000010 	andeq	r0, r0, r0, lsl r0
   56f78:	00000015 	andeq	r0, r0, r5, lsl r0
   56f7c:	00000000 	andeq	r0, r0, r0
   56f80:	00000003 	andeq	r0, r0, r3
   56f84:	00057000 	andeq	r7, r5, r0
   56f88:	00000002 	andeq	r0, r0, r2
   56f8c:	00000128 	andeq	r0, r0, r8, lsr #2
   56f90:	00000014 	andeq	r0, r0, r4, lsl r0
   56f94:	00000011 	andeq	r0, r0, r1, lsl r0
   56f98:	00000017 	andeq	r0, r0, r7, lsl r0
   56f9c:	000109f8 	strdeq	r0, [r1], -r8
   56fa0:	00000011 	andeq	r0, r0, r1, lsl r0
   56fa4:	000109e8 	andeq	r0, r1, r8, ror #19
   56fa8:	00000012 	andeq	r0, r0, r2, lsl r0
   56fac:	00000010 	andeq	r0, r0, r0, lsl r0
   56fb0:	00000013 	andeq	r0, r0, r3, lsl r0
   56fb4:	00000008 	andeq	r0, r0, r8
   56fb8:	6ffffffe 	svcvs	0x00fffffe
   56fbc:	00010998 	muleq	r1, r8, r9
   56fc0:	6fffffff 	svcvs	0x00ffffff
   56fc4:	00000002 	andeq	r0, r0, r2
   56fc8:	6ffffff0 	svcvs	0x00fffff0
   56fcc:	00010922 	andeq	r0, r1, r2, lsr #18
	...

Disassembly of section .got:

00057000 <_GLOBAL_OFFSET_TABLE_>:
   57000:	00056f10 	andeq	r6, r5, r0, lsl pc
	...
   5700c:	00010b2c 	andeq	r0, r1, ip, lsr #22
   57010:	00010b2c 	andeq	r0, r1, ip, lsr #22
   57014:	00010b2c 	andeq	r0, r1, ip, lsr #22
   57018:	00010b2c 	andeq	r0, r1, ip, lsr #22
   5701c:	00010b2c 	andeq	r0, r1, ip, lsr #22
   57020:	00010b2c 	andeq	r0, r1, ip, lsr #22
   57024:	00010b2c 	andeq	r0, r1, ip, lsr #22
   57028:	00010b2c 	andeq	r0, r1, ip, lsr #22
   5702c:	00010b2c 	andeq	r0, r1, ip, lsr #22
   57030:	00010b2c 	andeq	r0, r1, ip, lsr #22
   57034:	00010b2c 	andeq	r0, r1, ip, lsr #22
   57038:	00010b2c 	andeq	r0, r1, ip, lsr #22
   5703c:	00010b2c 	andeq	r0, r1, ip, lsr #22
   57040:	00010b2c 	andeq	r0, r1, ip, lsr #22
   57044:	00010b2c 	andeq	r0, r1, ip, lsr #22
   57048:	00010b2c 	andeq	r0, r1, ip, lsr #22
   5704c:	00010b2c 	andeq	r0, r1, ip, lsr #22
   57050:	00010b2c 	andeq	r0, r1, ip, lsr #22
   57054:	00010b2c 	andeq	r0, r1, ip, lsr #22
   57058:	00010b2c 	andeq	r0, r1, ip, lsr #22
   5705c:	00010b2c 	andeq	r0, r1, ip, lsr #22
   57060:	00010b2c 	andeq	r0, r1, ip, lsr #22
   57064:	00010b2c 	andeq	r0, r1, ip, lsr #22
   57068:	00010b2c 	andeq	r0, r1, ip, lsr #22
   5706c:	00010b2c 	andeq	r0, r1, ip, lsr #22
   57070:	00010b2c 	andeq	r0, r1, ip, lsr #22
   57074:	00010b2c 	andeq	r0, r1, ip, lsr #22
   57078:	00010b2c 	andeq	r0, r1, ip, lsr #22
   5707c:	00010b2c 	andeq	r0, r1, ip, lsr #22
   57080:	00010b2c 	andeq	r0, r1, ip, lsr #22
   57084:	00010b2c 	andeq	r0, r1, ip, lsr #22
   57088:	00010b2c 	andeq	r0, r1, ip, lsr #22
   5708c:	00010b2c 	andeq	r0, r1, ip, lsr #22
   57090:	00010b2c 	andeq	r0, r1, ip, lsr #22
   57094:	00010b2c 	andeq	r0, r1, ip, lsr #22
   57098:	00010b2c 	andeq	r0, r1, ip, lsr #22
   5709c:	00010b2c 	andeq	r0, r1, ip, lsr #22
   570a0:	00057cc4 	andeq	r7, r5, r4, asr #25
   570a4:	00057cb4 			; <UNDEFINED> instruction: 0x00057cb4
   570a8:	098ee514 	stmibeq	lr, {r2, r4, r8, sl, sp, lr, pc}
   570ac:	00057cbc 			; <UNDEFINED> instruction: 0x00057cbc
   570b0:	098ee51c 	stmibeq	lr, {r2, r3, r4, r8, sl, sp, lr, pc}
   570b4:	00057cc8 	andeq	r7, r5, r8, asr #25
   570b8:	098ee598 	stmibeq	lr, {r3, r4, r7, r8, sl, sp, lr, pc}
   570bc:	098ee5b8 	stmibeq	lr, {r3, r4, r5, r7, r8, sl, sp, lr, pc}
   570c0:	00057cd0 	ldrdeq	r7, [r5], -r0
   570c4:	00000000 	andeq	r0, r0, r0
   570c8:	00057d08 	andeq	r7, r5, r8, lsl #26
   570cc:	00044e4d 	andeq	r4, r4, sp, asr #28
   570d0:	098ee5bc 	stmibeq	lr, {r2, r3, r4, r5, r7, r8, sl, sp, lr, pc}
   570d4:	00057cb0 			; <UNDEFINED> instruction: 0x00057cb0
   570d8:	00000000 	andeq	r0, r0, r0
   570dc:	098ee5c4 	stmibeq	lr, {r2, r6, r7, r8, sl, sp, lr, pc}
   570e0:	098ee5c8 	stmibeq	lr, {r3, r6, r7, r8, sl, sp, lr, pc}
   570e4:	000570f4 	strdeq	r7, [r5], -r4
   570e8:	00057ccc 	andeq	r7, r5, ip, asr #25

Disassembly of section .data:

000570ec <ustepsPerMM>:
   570ec:	00000a00 	andeq	r0, r0, r0, lsl #20

000570f0 <memset_v.6351>:
   570f0:	00010c60 	andeq	r0, r1, r0, ror #24

000570f4 <uuid>:
   570f4:	d96a5b40 	stmdble	sl!, {r6, r8, r9, fp, ip, lr}^
   570f8:	21e3c3e5 	mvncs	ip, r5, ror #7
   570fc:	02109487 	andseq	r9, r0, #-2030043136	; 0x87000000
   57100:	1bc6d5a5 	blne	ff20c79c <__bss_end__+0xf591e198>

00057104 <__data_start>:
   57104:	00000000 	andeq	r0, r0, r0

00057108 <__dso_handle>:
   57108:	00000000 	andeq	r0, r0, r0

Disassembly of section .DATA_REGION_0__bss:

0005710c <uiState>:
   5710c:	00000000 	andeq	r0, r0, r0

00057110 <serialStr>:
	...

Disassembly of section .trampoline_fw:

00057160 <__trampoline_fw_blx>:
   57160:	e24dd00c 	sub	sp, sp, #12
   57164:	e58d0000 	str	r0, [sp]
   57168:	e58d1004 	str	r1, [sp, #4]
   5716c:	e10f0000 	mrs	r0, CPSR
   57170:	e58d0008 	str	r0, [sp, #8]
   57174:	e59f0970 	ldr	r0, [pc, #2416]	; 57aec <.curr_cpt_id>
   57178:	e3a01004 	mov	r1, #4
   5717c:	e0000190 	mul	r0, r0, r1
   57180:	e59f1b00 	ldr	r1, [pc, #2816]	; 57c88 <.cpt_stack+0x190>
   57184:	e0811000 	add	r1, r1, r0
   57188:	e5911000 	ldr	r1, [r1]
   5718c:	e1580001 	cmp	r8, r1
   57190:	3a000062 	bcc	57320 <__error>
   57194:	e2800004 	add	r0, r0, #4
   57198:	e59f1ae8 	ldr	r1, [pc, #2792]	; 57c88 <.cpt_stack+0x190>
   5719c:	e0811000 	add	r1, r1, r0
   571a0:	e5911000 	ldr	r1, [r1]
   571a4:	e1510008 	cmp	r1, r8
   571a8:	3a00005c 	bcc	57320 <__error>
   571ac:	e59d0008 	ldr	r0, [sp, #8]
   571b0:	e128f000 	msr	CPSR_f, r0
   571b4:	e59d0000 	ldr	r0, [sp]
   571b8:	e59d1004 	ldr	r1, [sp, #4]
   571bc:	e28dd00c 	add	sp, sp, #12
   571c0:	e12fff18 	bx	r8

000571c4 <__trampoline_fw_bx>:
   571c4:	e24dd00c 	sub	sp, sp, #12
   571c8:	e58d0000 	str	r0, [sp]
   571cc:	e58d1004 	str	r1, [sp, #4]
   571d0:	e10f0000 	mrs	r0, CPSR
   571d4:	e58d0008 	str	r0, [sp, #8]
   571d8:	e59f090c 	ldr	r0, [pc, #2316]	; 57aec <.curr_cpt_id>
   571dc:	e3a01004 	mov	r1, #4
   571e0:	e0000190 	mul	r0, r0, r1
   571e4:	e59f1a9c 	ldr	r1, [pc, #2716]	; 57c88 <.cpt_stack+0x190>
   571e8:	e0811000 	add	r1, r1, r0
   571ec:	e5911000 	ldr	r1, [r1]
   571f0:	e1580001 	cmp	r8, r1
   571f4:	3a000049 	bcc	57320 <__error>
   571f8:	e2800004 	add	r0, r0, #4
   571fc:	e59f1a84 	ldr	r1, [pc, #2692]	; 57c88 <.cpt_stack+0x190>
   57200:	e0811000 	add	r1, r1, r0
   57204:	e5911000 	ldr	r1, [r1]
   57208:	e1510008 	cmp	r1, r8
   5720c:	3a000043 	bcc	57320 <__error>
   57210:	e59d0008 	ldr	r0, [sp, #8]
   57214:	e128f000 	msr	CPSR_f, r0
   57218:	e59d0000 	ldr	r0, [sp]
   5721c:	e59d1004 	ldr	r1, [sp, #4]
   57220:	e28dd00c 	add	sp, sp, #12
   57224:	e12fff18 	bx	r8

00057228 <__trampoline_bkwd_bx_t>:
   57228:	e24dd00c 	sub	sp, sp, #12
   5722c:	e58d0000 	str	r0, [sp]
   57230:	e58d1004 	str	r1, [sp, #4]
   57234:	e10f0000 	mrs	r0, CPSR
   57238:	e58d0008 	str	r0, [sp, #8]
   5723c:	e59f08a8 	ldr	r0, [pc, #2216]	; 57aec <.curr_cpt_id>
   57240:	e3a01004 	mov	r1, #4
   57244:	e0000190 	mul	r0, r0, r1
   57248:	e59f1a38 	ldr	r1, [pc, #2616]	; 57c88 <.cpt_stack+0x190>
   5724c:	e0811000 	add	r1, r1, r0
   57250:	e5911000 	ldr	r1, [r1]
   57254:	e1580001 	cmp	r8, r1
   57258:	3a000030 	bcc	57320 <__error>
   5725c:	e2800004 	add	r0, r0, #4
   57260:	e59f1a20 	ldr	r1, [pc, #2592]	; 57c88 <.cpt_stack+0x190>
   57264:	e0811000 	add	r1, r1, r0
   57268:	e5911000 	ldr	r1, [r1]
   5726c:	e1510008 	cmp	r1, r8
   57270:	3a00002a 	bcc	57320 <__error>
   57274:	e59d0008 	ldr	r0, [sp, #8]
   57278:	e128f000 	msr	CPSR_f, r0
   5727c:	e59d0000 	ldr	r0, [sp]
   57280:	e59d1004 	ldr	r1, [sp, #4]
   57284:	e28dd00c 	add	sp, sp, #12
   57288:	e1a0e008 	mov	lr, r8
   5728c:	e12fff18 	bx	r8

00057290 <__trampoline_bkwd_bx>:
   57290:	e1a0e008 	mov	lr, r8
   57294:	e12fff18 	bx	r8

00057298 <__trampoline_bkwd_pop>:
   57298:	e59d8000 	ldr	r8, [sp]
   5729c:	e1a0e008 	mov	lr, r8
   572a0:	e59d8004 	ldr	r8, [sp, #4]
   572a4:	e24dd00c 	sub	sp, sp, #12
   572a8:	e58d0000 	str	r0, [sp]
   572ac:	e58d1004 	str	r1, [sp, #4]
   572b0:	e10f0000 	mrs	r0, CPSR
   572b4:	e58d0008 	str	r0, [sp, #8]
   572b8:	e59f082c 	ldr	r0, [pc, #2092]	; 57aec <.curr_cpt_id>
   572bc:	e3a01004 	mov	r1, #4
   572c0:	e0000190 	mul	r0, r0, r1
   572c4:	e59f19bc 	ldr	r1, [pc, #2492]	; 57c88 <.cpt_stack+0x190>
   572c8:	e0811000 	add	r1, r1, r0
   572cc:	e5911000 	ldr	r1, [r1]
   572d0:	e1580001 	cmp	r8, r1
   572d4:	3a000011 	bcc	57320 <__error>
   572d8:	e2800004 	add	r0, r0, #4
   572dc:	e59f19a4 	ldr	r1, [pc, #2468]	; 57c88 <.cpt_stack+0x190>
   572e0:	e0811000 	add	r1, r1, r0
   572e4:	e5911000 	ldr	r1, [r1]
   572e8:	e1510008 	cmp	r1, r8
   572ec:	3a00000b 	bcc	57320 <__error>
   572f0:	e59d0008 	ldr	r0, [sp, #8]
   572f4:	e128f000 	msr	CPSR_f, r0
   572f8:	e59d0000 	ldr	r0, [sp]
   572fc:	e59d1004 	ldr	r1, [sp, #4]
   57300:	e28dd014 	add	sp, sp, #20
   57304:	e12fff18 	bx	r8

00057308 <__AMI_fake_direct_transfer>:
   57308:	e320f000 	nop	{0}

0005730c <__AMI_fake_indirect_transfer>:
   5730c:	e320f000 	nop	{0}

00057310 <__AMI_fake_rt_transfer>:
   57310:	e320f000 	nop	{0}

00057314 <__AMI_fake_local_wrt>:
   57314:	e320f000 	nop	{0}

00057318 <__AMI_fake_shared_wrt>:
   57318:	e320f000 	nop	{0}

0005731c <__AMI_fake_pop_pc_transfer>:
   5731c:	e320f000 	nop	{0}

00057320 <__error>:
   57320:	ea000260 	b	57ca8 <__error_found_from_arm>

00057324 <__tsf_direct_jmp_link_checking>:
   57324:	e24dd014 	sub	sp, sp, #20
   57328:	e58d0000 	str	r0, [sp]
   5732c:	e58d1004 	str	r1, [sp, #4]
   57330:	e58d2008 	str	r2, [sp, #8]
   57334:	e58d300c 	str	r3, [sp, #12]
   57338:	e10f0000 	mrs	r0, CPSR
   5733c:	e58d0010 	str	r0, [sp, #16]
   57340:	e59f07a4 	ldr	r0, [pc, #1956]	; 57aec <.curr_cpt_id>
   57344:	e3a01008 	mov	r1, #8
   57348:	e0010190 	mul	r1, r0, r1
   5734c:	e59f2938 	ldr	r2, [pc, #2360]	; 57c8c <.cpt_stack+0x194>
   57350:	e0811002 	add	r1, r1, r2
   57354:	e59f0794 	ldr	r0, [pc, #1940]	; 57af0 <.total_cpt_cnt>
   57358:	e3a02008 	mov	r2, #8
   5735c:	e0000290 	mul	r0, r0, r2
   57360:	e59f2924 	ldr	r2, [pc, #2340]	; 57c8c <.cpt_stack+0x194>
   57364:	e0820000 	add	r0, r2, r0
   57368:	e5912000 	ldr	r2, [r1]
   5736c:	e0822000 	add	r2, r2, r0
   57370:	e5911004 	ldr	r1, [r1, #4]
   57374:	e3a03000 	mov	r3, #0

00057378 <direct_link_cpt_ck_loop>:
   57378:	e1530001 	cmp	r3, r1
   5737c:	aa000007 	bge	573a0 <direct_link_cpt_ck_fail>
   57380:	e3a00008 	mov	r0, #8
   57384:	e0000093 	mul	r0, r3, r0
   57388:	e0800002 	add	r0, r0, r2
   5738c:	e5900000 	ldr	r0, [r0]
   57390:	e1580000 	cmp	r8, r0
   57394:	0a000003 	beq	573a8 <direct_link_cpt_ck_pass>
   57398:	e2833001 	add	r3, r3, #1
   5739c:	eafffff5 	b	57378 <direct_link_cpt_ck_loop>

000573a0 <direct_link_cpt_ck_fail>:
   573a0:	ea000000 	b	573a8 <direct_link_cpt_ck_pass>
   573a4:	eaffffdd 	b	57320 <__error>

000573a8 <direct_link_cpt_ck_pass>:
   573a8:	e3a00008 	mov	r0, #8
   573ac:	e2433001 	sub	r3, r3, #1
   573b0:	e0000093 	mul	r0, r3, r0
   573b4:	e0800002 	add	r0, r0, r2
   573b8:	e5900004 	ldr	r0, [r0, #4]
   573bc:	e59f18cc 	ldr	r1, [pc, #2252]	; 57c90 <.cpt_stack+0x198>
   573c0:	e5810000 	str	r0, [r1]
   573c4:	e59f08c8 	ldr	r0, [pc, #2248]	; 57c94 <.cpt_stack+0x19c>
   573c8:	e59f1724 	ldr	r1, [pc, #1828]	; 57af4 <.curr_cpt_stack_pointer_offset>
   573cc:	e0800001 	add	r0, r0, r1
   573d0:	e2811008 	add	r1, r1, #8
   573d4:	e58f1718 	str	r1, [pc, #1816]	; 57af4 <.curr_cpt_stack_pointer_offset>
   573d8:	e59f170c 	ldr	r1, [pc, #1804]	; 57aec <.curr_cpt_id>
   573dc:	e5801000 	str	r1, [r0]
   573e0:	e2800004 	add	r0, r0, #4
   573e4:	e580e000 	str	lr, [r0]
   573e8:	e59d0010 	ldr	r0, [sp, #16]
   573ec:	e128f000 	msr	CPSR_f, r0
   573f0:	e59d0000 	ldr	r0, [sp]
   573f4:	e59d1004 	ldr	r1, [sp, #4]
   573f8:	e59d2008 	ldr	r2, [sp, #8]
   573fc:	e59d300c 	ldr	r3, [sp, #12]
   57400:	e28dd014 	add	sp, sp, #20
   57404:	e12fff18 	bx	r8

00057408 <__tsf_direct_jmp_checking>:
   57408:	e24dd014 	sub	sp, sp, #20
   5740c:	e58d0000 	str	r0, [sp]
   57410:	e58d1004 	str	r1, [sp, #4]
   57414:	e58d2008 	str	r2, [sp, #8]
   57418:	e58d300c 	str	r3, [sp, #12]
   5741c:	e10f0000 	mrs	r0, CPSR
   57420:	e58d0010 	str	r0, [sp, #16]
   57424:	e59f06c0 	ldr	r0, [pc, #1728]	; 57aec <.curr_cpt_id>
   57428:	e3a01008 	mov	r1, #8
   5742c:	e0010190 	mul	r1, r0, r1
   57430:	e59f2854 	ldr	r2, [pc, #2132]	; 57c8c <.cpt_stack+0x194>
   57434:	e0811002 	add	r1, r1, r2
   57438:	e59f06b0 	ldr	r0, [pc, #1712]	; 57af0 <.total_cpt_cnt>
   5743c:	e3a02008 	mov	r2, #8
   57440:	e0000290 	mul	r0, r0, r2
   57444:	e59f2840 	ldr	r2, [pc, #2112]	; 57c8c <.cpt_stack+0x194>
   57448:	e0820000 	add	r0, r2, r0
   5744c:	e5912000 	ldr	r2, [r1]
   57450:	e0822000 	add	r2, r2, r0
   57454:	e5911004 	ldr	r1, [r1, #4]
   57458:	e3a03000 	mov	r3, #0

0005745c <direct_cpt_ck_loop>:
   5745c:	e1530001 	cmp	r3, r1
   57460:	aa000007 	bge	57484 <direct_cpt_ck_fail>
   57464:	e3a00008 	mov	r0, #8
   57468:	e0000093 	mul	r0, r3, r0
   5746c:	e0800002 	add	r0, r0, r2
   57470:	e5900000 	ldr	r0, [r0]
   57474:	e1580000 	cmp	r8, r0
   57478:	0a000003 	beq	5748c <direct_cpt_ck_pass>
   5747c:	e2833001 	add	r3, r3, #1
   57480:	eafffff5 	b	5745c <direct_cpt_ck_loop>

00057484 <direct_cpt_ck_fail>:
   57484:	eaffffc7 	b	573a8 <direct_link_cpt_ck_pass>
   57488:	eaffffa4 	b	57320 <__error>

0005748c <direct_cpt_ck_pass>:
   5748c:	e3a00008 	mov	r0, #8
   57490:	e2433001 	sub	r3, r3, #1
   57494:	e0000093 	mul	r0, r3, r0
   57498:	e0800002 	add	r0, r0, r2
   5749c:	e5900004 	ldr	r0, [r0, #4]
   574a0:	e59f17e8 	ldr	r1, [pc, #2024]	; 57c90 <.cpt_stack+0x198>
   574a4:	e5810000 	str	r0, [r1]
   574a8:	e59d0010 	ldr	r0, [sp, #16]
   574ac:	e128f000 	msr	CPSR_f, r0
   574b0:	e59d0000 	ldr	r0, [sp]
   574b4:	e59d1004 	ldr	r1, [sp, #4]
   574b8:	e59d2008 	ldr	r2, [sp, #8]
   574bc:	e59d300c 	ldr	r3, [sp, #12]
   574c0:	e28dd014 	add	sp, sp, #20
   574c4:	e12fff18 	bx	r8

000574c8 <__tsf_direct_jmp_link_recording>:
   574c8:	e92d400f 	push	{r0, r1, r2, r3, lr}
   574cc:	e1a0000e 	mov	r0, lr
   574d0:	faffb28b 	blx	43f04 <c_direct_tsf_recording>
   574d4:	e8bd400f 	pop	{r0, r1, r2, r3, lr}
   574d8:	e12fff1e 	bx	lr

000574dc <__tsf_direct_jmp_link_cc_recording>:
   574dc:	e92d400f 	push	{r0, r1, r2, r3, lr}
   574e0:	e10f0000 	mrs	r0, CPSR
   574e4:	e52d0004 	push	{r0}		; (str r0, [sp, #-4]!)
   574e8:	e1a0000e 	mov	r0, lr
   574ec:	faffb31c 	blx	44164 <c_direct_tsf_cc_recording>
   574f0:	e49d0004 	pop	{r0}		; (ldr r0, [sp], #4)
   574f4:	e129f000 	msr	CPSR_fc, r0
   574f8:	e8bd400f 	pop	{r0, r1, r2, r3, lr}
   574fc:	e12fff1e 	bx	lr

00057500 <__tsf_direct_jmp_recording>:
   57500:	e12fff1e 	bx	lr

00057504 <__tsf_direct_jmp_cc_recording>:
   57504:	e92d400f 	push	{r0, r1, r2, r3, lr}
   57508:	e10f0000 	mrs	r0, CPSR
   5750c:	e52d0004 	push	{r0}		; (str r0, [sp, #-4]!)
   57510:	e1a0000e 	mov	r0, lr
   57514:	faffb359 	blx	44280 <c_direct_tsf_bcc_recording>
   57518:	e49d0004 	pop	{r0}		; (ldr r0, [sp], #4)
   5751c:	e129f000 	msr	CPSR_fc, r0
   57520:	e8bd400f 	pop	{r0, r1, r2, r3, lr}
   57524:	e12fff1e 	bx	lr

00057528 <__tsf_indirect_jmp_link_recording>:
   57528:	e92d400f 	push	{r0, r1, r2, r3, lr}
   5752c:	e1a0000e 	mov	r0, lr
   57530:	faffb39b 	blx	443a4 <c_indirect_tsf_recording>
   57534:	e8bd400f 	pop	{r0, r1, r2, r3, lr}
   57538:	e12fff18 	bx	r8

0005753c <__tsf_indirect_jmp_link_cc_recording>:
   5753c:	e12fff1e 	bx	lr

00057540 <__tsf_indirect_jmp_recording>:
   57540:	e12fff18 	bx	r8

00057544 <__tsf_indirect_jmp_cc_recording>:
   57544:	e12fff1e 	bx	lr

00057548 <__tsf_bkwd_bx_lr_recording>:
   57548:	e92d400f 	push	{r0, r1, r2, r3, lr}
   5754c:	e1a0000e 	mov	r0, lr
   57550:	faffb3be 	blx	44450 <c_tsf_bx_lr_recording>
   57554:	e8bd400f 	pop	{r0, r1, r2, r3, lr}
   57558:	e12fff18 	bx	r8

0005755c <__tsf_bkwd_pop_pc_recording>:
   5755c:	e92d400f 	push	{r0, r1, r2, r3, lr}
   57560:	e1a0000e 	mov	r0, lr
   57564:	faffb3f0 	blx	4452c <c_tsf_pop_pc_recording>
   57568:	e8bd400f 	pop	{r0, r1, r2, r3, lr}
   5756c:	e12fff18 	bx	r8

00057570 <__tsf_test>:
   57570:	e12fff1e 	bx	lr

00057574 <__tsf_indirect_jmp_link_checking>:
   57574:	e24dd014 	sub	sp, sp, #20
   57578:	e58d0000 	str	r0, [sp]
   5757c:	e58d1004 	str	r1, [sp, #4]
   57580:	e58d2008 	str	r2, [sp, #8]
   57584:	e58d300c 	str	r3, [sp, #12]
   57588:	e10f0000 	mrs	r0, CPSR
   5758c:	e58d0010 	str	r0, [sp, #16]
   57590:	e59f0554 	ldr	r0, [pc, #1364]	; 57aec <.curr_cpt_id>
   57594:	e3a01008 	mov	r1, #8
   57598:	e0010190 	mul	r1, r0, r1
   5759c:	e59f26f4 	ldr	r2, [pc, #1780]	; 57c98 <.cpt_stack+0x1a0>
   575a0:	e0811002 	add	r1, r1, r2
   575a4:	e59f0544 	ldr	r0, [pc, #1348]	; 57af0 <.total_cpt_cnt>
   575a8:	e3a02008 	mov	r2, #8
   575ac:	e0000290 	mul	r0, r0, r2
   575b0:	e59f26e0 	ldr	r2, [pc, #1760]	; 57c98 <.cpt_stack+0x1a0>
   575b4:	e0820000 	add	r0, r2, r0
   575b8:	e5912000 	ldr	r2, [r1]
   575bc:	e0822000 	add	r2, r2, r0
   575c0:	e5911004 	ldr	r1, [r1, #4]
   575c4:	e3a03000 	mov	r3, #0

000575c8 <indirect_link_cpt_ck_loop>:
   575c8:	e1530001 	cmp	r3, r1
   575cc:	aa000007 	bge	575f0 <indirect_link_cpt_ck_fail>
   575d0:	e3a00008 	mov	r0, #8
   575d4:	e0000093 	mul	r0, r3, r0
   575d8:	e0800002 	add	r0, r0, r2
   575dc:	e5900000 	ldr	r0, [r0]
   575e0:	e1580000 	cmp	r8, r0
   575e4:	0a000009 	beq	57610 <indirect_link_cpt_ck_pass>
   575e8:	e2833001 	add	r3, r3, #1
   575ec:	eafffff5 	b	575c8 <indirect_link_cpt_ck_loop>

000575f0 <indirect_link_cpt_ck_fail>:
   575f0:	e59f1698 	ldr	r1, [pc, #1688]	; 57c90 <.cpt_stack+0x198>
   575f4:	e5912000 	ldr	r2, [r1]
   575f8:	e1a01002 	mov	r1, r2
   575fc:	e3a02006 	mov	r2, #6
   57600:	e92d4100 	push	{r8, lr}
   57604:	faffb507 	blx	44a28 <view_switch_to_rd_and_log>
   57608:	e8bd4100 	pop	{r8, lr}
   5760c:	ea00001d 	b	57688 <indirect_link_internal_sfi>

00057610 <indirect_link_cpt_ck_pass>:
   57610:	e3a00008 	mov	r0, #8
   57614:	e2433001 	sub	r3, r3, #1
   57618:	e0000093 	mul	r0, r3, r0
   5761c:	e0800002 	add	r0, r0, r2
   57620:	e5900004 	ldr	r0, [r0, #4]
   57624:	e59f1664 	ldr	r1, [pc, #1636]	; 57c90 <.cpt_stack+0x198>
   57628:	e5912000 	ldr	r2, [r1]
   5762c:	e5810000 	str	r0, [r1]
   57630:	e1a01002 	mov	r1, r2
   57634:	e3a02006 	mov	r2, #6
   57638:	e92d4100 	push	{r8, lr}
   5763c:	faffb4f9 	blx	44a28 <view_switch_to_rd_and_log>
   57640:	e8bd4100 	pop	{r8, lr}
   57644:	e59f0648 	ldr	r0, [pc, #1608]	; 57c94 <.cpt_stack+0x19c>
   57648:	e59f14a4 	ldr	r1, [pc, #1188]	; 57af4 <.curr_cpt_stack_pointer_offset>
   5764c:	e0800001 	add	r0, r0, r1
   57650:	e2811008 	add	r1, r1, #8
   57654:	e58f1498 	str	r1, [pc, #1176]	; 57af4 <.curr_cpt_stack_pointer_offset>
   57658:	e59f148c 	ldr	r1, [pc, #1164]	; 57aec <.curr_cpt_id>
   5765c:	e5801000 	str	r1, [r0]
   57660:	e2800004 	add	r0, r0, #4
   57664:	e580e000 	str	lr, [r0]
   57668:	e59d0010 	ldr	r0, [sp, #16]
   5766c:	e128f000 	msr	CPSR_f, r0
   57670:	e59d0000 	ldr	r0, [sp]
   57674:	e59d1004 	ldr	r1, [sp, #4]
   57678:	e59d2008 	ldr	r2, [sp, #8]
   5767c:	e59d300c 	ldr	r3, [sp, #12]
   57680:	e28dd014 	add	sp, sp, #20
   57684:	e12fff18 	bx	r8

00057688 <indirect_link_internal_sfi>:
   57688:	e59f045c 	ldr	r0, [pc, #1116]	; 57aec <.curr_cpt_id>
   5768c:	e3a01004 	mov	r1, #4
   57690:	e0000190 	mul	r0, r0, r1
   57694:	e59f15ec 	ldr	r1, [pc, #1516]	; 57c88 <.cpt_stack+0x190>
   57698:	e0811000 	add	r1, r1, r0
   5769c:	e5911000 	ldr	r1, [r1]
   576a0:	e1580001 	cmp	r8, r1
   576a4:	3affff1d 	bcc	57320 <__error>
   576a8:	e2800004 	add	r0, r0, #4
   576ac:	e59f15d4 	ldr	r1, [pc, #1492]	; 57c88 <.cpt_stack+0x190>
   576b0:	e0811000 	add	r1, r1, r0
   576b4:	e5911000 	ldr	r1, [r1]
   576b8:	e1510008 	cmp	r1, r8
   576bc:	3affff17 	bcc	57320 <__error>
   576c0:	e59d0010 	ldr	r0, [sp, #16]
   576c4:	e128f000 	msr	CPSR_f, r0
   576c8:	e59d0000 	ldr	r0, [sp]
   576cc:	e59d1004 	ldr	r1, [sp, #4]
   576d0:	e59d2008 	ldr	r2, [sp, #8]
   576d4:	e59d300c 	ldr	r3, [sp, #12]
   576d8:	e28dd014 	add	sp, sp, #20
   576dc:	e12fff18 	bx	r8

000576e0 <__tsf_indirect_jmp_checking>:
   576e0:	e24dd014 	sub	sp, sp, #20
   576e4:	e58d0000 	str	r0, [sp]
   576e8:	e58d1004 	str	r1, [sp, #4]
   576ec:	e58d2008 	str	r2, [sp, #8]
   576f0:	e58d300c 	str	r3, [sp, #12]
   576f4:	e10f0000 	mrs	r0, CPSR
   576f8:	e58d0010 	str	r0, [sp, #16]
   576fc:	e59f03e8 	ldr	r0, [pc, #1000]	; 57aec <.curr_cpt_id>
   57700:	e3a01008 	mov	r1, #8
   57704:	e0010190 	mul	r1, r0, r1
   57708:	e59f2588 	ldr	r2, [pc, #1416]	; 57c98 <.cpt_stack+0x1a0>
   5770c:	e0811002 	add	r1, r1, r2
   57710:	e59f03d8 	ldr	r0, [pc, #984]	; 57af0 <.total_cpt_cnt>
   57714:	e3a02008 	mov	r2, #8
   57718:	e0000290 	mul	r0, r0, r2
   5771c:	e59f2574 	ldr	r2, [pc, #1396]	; 57c98 <.cpt_stack+0x1a0>
   57720:	e0820000 	add	r0, r2, r0
   57724:	e5912000 	ldr	r2, [r1]
   57728:	e0822000 	add	r2, r2, r0
   5772c:	e5911004 	ldr	r1, [r1, #4]
   57730:	e3a03000 	mov	r3, #0

00057734 <indirect_cpt_ck_loop>:
   57734:	e1530001 	cmp	r3, r1
   57738:	aa000007 	bge	5775c <indirect_cpt_ck_fail>
   5773c:	e3a00008 	mov	r0, #8
   57740:	e0000093 	mul	r0, r3, r0
   57744:	e0800002 	add	r0, r0, r2
   57748:	e5900000 	ldr	r0, [r0]
   5774c:	e1580000 	cmp	r8, r0
   57750:	0a000003 	beq	57764 <indirect_cpt_ck_pass>
   57754:	e2833001 	add	r3, r3, #1
   57758:	eafffff5 	b	57734 <indirect_cpt_ck_loop>

0005775c <indirect_cpt_ck_fail>:
   5775c:	ea000000 	b	57764 <indirect_cpt_ck_pass>
   57760:	ea00000e 	b	577a0 <indirect_internal_sfi>

00057764 <indirect_cpt_ck_pass>:
   57764:	e3a00008 	mov	r0, #8
   57768:	e2433001 	sub	r3, r3, #1
   5776c:	e0000093 	mul	r0, r3, r0
   57770:	e0800002 	add	r0, r0, r2
   57774:	e5900004 	ldr	r0, [r0, #4]
   57778:	e59f1510 	ldr	r1, [pc, #1296]	; 57c90 <.cpt_stack+0x198>
   5777c:	e5810000 	str	r0, [r1]
   57780:	e59d0010 	ldr	r0, [sp, #16]
   57784:	e128f000 	msr	CPSR_f, r0
   57788:	e59d0000 	ldr	r0, [sp]
   5778c:	e59d1004 	ldr	r1, [sp, #4]
   57790:	e59d2008 	ldr	r2, [sp, #8]
   57794:	e59d300c 	ldr	r3, [sp, #12]
   57798:	e28dd014 	add	sp, sp, #20
   5779c:	e12fff18 	bx	r8

000577a0 <indirect_internal_sfi>:
   577a0:	e59f0344 	ldr	r0, [pc, #836]	; 57aec <.curr_cpt_id>
   577a4:	e3a01004 	mov	r1, #4
   577a8:	e0000190 	mul	r0, r0, r1
   577ac:	e59f14d4 	ldr	r1, [pc, #1236]	; 57c88 <.cpt_stack+0x190>
   577b0:	e0811000 	add	r1, r1, r0
   577b4:	e5911000 	ldr	r1, [r1]
   577b8:	e1580001 	cmp	r8, r1
   577bc:	3afffed7 	bcc	57320 <__error>
   577c0:	e2800004 	add	r0, r0, #4
   577c4:	e59f14bc 	ldr	r1, [pc, #1212]	; 57c88 <.cpt_stack+0x190>
   577c8:	e0811000 	add	r1, r1, r0
   577cc:	e5911000 	ldr	r1, [r1]
   577d0:	e1510008 	cmp	r1, r8
   577d4:	3afffed1 	bcc	57320 <__error>
   577d8:	e59d0010 	ldr	r0, [sp, #16]
   577dc:	e128f000 	msr	CPSR_f, r0
   577e0:	e59d0000 	ldr	r0, [sp]
   577e4:	e59d1004 	ldr	r1, [sp, #4]
   577e8:	e59d2008 	ldr	r2, [sp, #8]
   577ec:	e59d300c 	ldr	r3, [sp, #12]
   577f0:	e28dd014 	add	sp, sp, #20
   577f4:	e12fff18 	bx	r8

000577f8 <__tsf_bkwd_bx_lr_checking>:
   577f8:	e24dd00c 	sub	sp, sp, #12
   577fc:	e58d0000 	str	r0, [sp]
   57800:	e58d1004 	str	r1, [sp, #4]
   57804:	e10f0000 	mrs	r0, CPSR
   57808:	e58d0008 	str	r0, [sp, #8]
   5780c:	e59f0480 	ldr	r0, [pc, #1152]	; 57c94 <.cpt_stack+0x19c>
   57810:	e59f12dc 	ldr	r1, [pc, #732]	; 57af4 <.curr_cpt_stack_pointer_offset>
   57814:	e0810000 	add	r0, r1, r0
   57818:	e2400004 	sub	r0, r0, #4
   5781c:	e5900000 	ldr	r0, [r0]
   57820:	e1580000 	cmp	r8, r0
   57824:	0a000006 	beq	57844 <__tsf_bkwd_bx_lr_pass>
   57828:	e59d0008 	ldr	r0, [sp, #8]
   5782c:	e128f000 	msr	CPSR_f, r0
   57830:	e59d0000 	ldr	r0, [sp]
   57834:	e59d1004 	ldr	r1, [sp, #4]
   57838:	e59de00c 	ldr	lr, [sp, #12]
   5783c:	e28dd010 	add	sp, sp, #16
   57840:	ea00000e 	b	57880 <__tsf_trampoline_bkwd_bx>

00057844 <__tsf_bkwd_bx_lr_pass>:
   57844:	e2411008 	sub	r1, r1, #8
   57848:	e59f044c 	ldr	r0, [pc, #1100]	; 57c9c <.cpt_stack+0x1a4>
   5784c:	e5801000 	str	r1, [r0]
   57850:	e59f043c 	ldr	r0, [pc, #1084]	; 57c94 <.cpt_stack+0x19c>
   57854:	e0811000 	add	r1, r1, r0
   57858:	e5910000 	ldr	r0, [r1]
   5785c:	e59f142c 	ldr	r1, [pc, #1068]	; 57c90 <.cpt_stack+0x198>
   57860:	e5810000 	str	r0, [r1]
   57864:	e59d0008 	ldr	r0, [sp, #8]
   57868:	e128f000 	msr	CPSR_f, r0
   5786c:	e59d0000 	ldr	r0, [sp]
   57870:	e59d1004 	ldr	r1, [sp, #4]
   57874:	e59de00c 	ldr	lr, [sp, #12]
   57878:	e28dd010 	add	sp, sp, #16
   5787c:	e12fff18 	bx	r8

00057880 <__tsf_trampoline_bkwd_bx>:
   57880:	e24dd00c 	sub	sp, sp, #12
   57884:	e58d0000 	str	r0, [sp]
   57888:	e58d1004 	str	r1, [sp, #4]
   5788c:	e10f0000 	mrs	r0, CPSR
   57890:	e58d0008 	str	r0, [sp, #8]
   57894:	e59f0250 	ldr	r0, [pc, #592]	; 57aec <.curr_cpt_id>
   57898:	e3a01004 	mov	r1, #4
   5789c:	e0000190 	mul	r0, r0, r1
   578a0:	e59f13e0 	ldr	r1, [pc, #992]	; 57c88 <.cpt_stack+0x190>
   578a4:	e0811000 	add	r1, r1, r0
   578a8:	e5911000 	ldr	r1, [r1]
   578ac:	e1580001 	cmp	r8, r1
   578b0:	3afffe9a 	bcc	57320 <__error>
   578b4:	e2800004 	add	r0, r0, #4
   578b8:	e59f13c8 	ldr	r1, [pc, #968]	; 57c88 <.cpt_stack+0x190>
   578bc:	e0811000 	add	r1, r1, r0
   578c0:	e5911000 	ldr	r1, [r1]
   578c4:	e1510008 	cmp	r1, r8
   578c8:	3afffe94 	bcc	57320 <__error>
   578cc:	e59d0008 	ldr	r0, [sp, #8]
   578d0:	e128f000 	msr	CPSR_f, r0
   578d4:	e59d0000 	ldr	r0, [sp]
   578d8:	e59d1004 	ldr	r1, [sp, #4]
   578dc:	e28dd00c 	add	sp, sp, #12
   578e0:	e12fff18 	bx	r8

000578e4 <__tsf_bkwd_pop_pc_checking>:
   578e4:	e59d8004 	ldr	r8, [sp, #4]
   578e8:	e24dd00c 	sub	sp, sp, #12
   578ec:	e58d0000 	str	r0, [sp]
   578f0:	e58d1004 	str	r1, [sp, #4]
   578f4:	e10f0000 	mrs	r0, CPSR
   578f8:	e58d0008 	str	r0, [sp, #8]
   578fc:	e59f0390 	ldr	r0, [pc, #912]	; 57c94 <.cpt_stack+0x19c>
   57900:	e59f11ec 	ldr	r1, [pc, #492]	; 57af4 <.curr_cpt_stack_pointer_offset>
   57904:	e0810000 	add	r0, r1, r0
   57908:	e2400004 	sub	r0, r0, #4
   5790c:	e5900000 	ldr	r0, [r0]
   57910:	e1580000 	cmp	r8, r0
   57914:	0a000006 	beq	57934 <__tsf_bkwd_pop_pc_pass>
   57918:	e59d0008 	ldr	r0, [sp, #8]
   5791c:	e128f000 	msr	CPSR_f, r0
   57920:	e59d0000 	ldr	r0, [sp]
   57924:	e59d1004 	ldr	r1, [sp, #4]
   57928:	e28dd00c 	add	sp, sp, #12
   5792c:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   57930:	ea00000f 	b	57974 <__tsf_trampoline_bkwd_pop>

00057934 <__tsf_bkwd_pop_pc_pass>:
   57934:	e2411008 	sub	r1, r1, #8
   57938:	e59f035c 	ldr	r0, [pc, #860]	; 57c9c <.cpt_stack+0x1a4>
   5793c:	e5801000 	str	r1, [r0]
   57940:	e59f034c 	ldr	r0, [pc, #844]	; 57c94 <.cpt_stack+0x19c>
   57944:	e0811000 	add	r1, r1, r0
   57948:	e5910000 	ldr	r0, [r1]
   5794c:	e59f133c 	ldr	r1, [pc, #828]	; 57c90 <.cpt_stack+0x198>
   57950:	e5810000 	str	r0, [r1]
   57954:	e59d0008 	ldr	r0, [sp, #8]
   57958:	e128f000 	msr	CPSR_f, r0
   5795c:	e59d0000 	ldr	r0, [sp]
   57960:	e59d1004 	ldr	r1, [sp, #4]
   57964:	e28dd00c 	add	sp, sp, #12
   57968:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   5796c:	e28dd004 	add	sp, sp, #4
   57970:	e12fff18 	bx	r8

00057974 <__tsf_trampoline_bkwd_pop>:
   57974:	e49d8004 	pop	{r8}		; (ldr r8, [sp], #4)
   57978:	e24dd00c 	sub	sp, sp, #12
   5797c:	e58d0000 	str	r0, [sp]
   57980:	e58d1004 	str	r1, [sp, #4]
   57984:	e10f0000 	mrs	r0, CPSR
   57988:	e58d0008 	str	r0, [sp, #8]
   5798c:	e59f0158 	ldr	r0, [pc, #344]	; 57aec <.curr_cpt_id>
   57990:	e3a01004 	mov	r1, #4
   57994:	e0000190 	mul	r0, r0, r1
   57998:	e59f12e8 	ldr	r1, [pc, #744]	; 57c88 <.cpt_stack+0x190>
   5799c:	e0811000 	add	r1, r1, r0
   579a0:	e5911000 	ldr	r1, [r1]
   579a4:	e1580001 	cmp	r8, r1
   579a8:	3afffe5c 	bcc	57320 <__error>
   579ac:	e2800004 	add	r0, r0, #4
   579b0:	e59f12d0 	ldr	r1, [pc, #720]	; 57c88 <.cpt_stack+0x190>
   579b4:	e0811000 	add	r1, r1, r0
   579b8:	e5911000 	ldr	r1, [r1]
   579bc:	e1510008 	cmp	r1, r8
   579c0:	3afffe56 	bcc	57320 <__error>
   579c4:	e59d0008 	ldr	r0, [sp, #8]
   579c8:	e128f000 	msr	CPSR_f, r0
   579cc:	e59d0000 	ldr	r0, [sp]
   579d0:	e59d1004 	ldr	r1, [sp, #4]
   579d4:	e28dd00c 	add	sp, sp, #12
   579d8:	e12fff18 	bx	r8

000579dc <__storing_checking>:
   579dc:	e24dd018 	sub	sp, sp, #24
   579e0:	e58d0000 	str	r0, [sp]
   579e4:	e58d1004 	str	r1, [sp, #4]
   579e8:	e58d2008 	str	r2, [sp, #8]
   579ec:	e58d300c 	str	r3, [sp, #12]
   579f0:	e58d4010 	str	r4, [sp, #16]
   579f4:	e10f0000 	mrs	r0, CPSR
   579f8:	e58d0014 	str	r0, [sp, #20]
   579fc:	e59f00e8 	ldr	r0, [pc, #232]	; 57aec <.curr_cpt_id>
   57a00:	e3a01008 	mov	r1, #8
   57a04:	e0010190 	mul	r1, r0, r1
   57a08:	e59f2290 	ldr	r2, [pc, #656]	; 57ca0 <.cpt_stack+0x1a8>
   57a0c:	e0811002 	add	r1, r1, r2
   57a10:	e59f00d8 	ldr	r0, [pc, #216]	; 57af0 <.total_cpt_cnt>
   57a14:	e3a02008 	mov	r2, #8
   57a18:	e0000290 	mul	r0, r0, r2
   57a1c:	e59f227c 	ldr	r2, [pc, #636]	; 57ca0 <.cpt_stack+0x1a8>
   57a20:	e0820000 	add	r0, r2, r0
   57a24:	e5912000 	ldr	r2, [r1]
   57a28:	e0822000 	add	r2, r2, r0
   57a2c:	e5911004 	ldr	r1, [r1, #4]
   57a30:	e3a03000 	mov	r3, #0
   57a34:	e3a04000 	mov	r4, #0

00057a38 <storing_ck_loop>:
   57a38:	e1530001 	cmp	r3, r1
   57a3c:	aa000010 	bge	57a84 <storing_ck_valid>
   57a40:	e3a00008 	mov	r0, #8
   57a44:	e0000093 	mul	r0, r3, r0
   57a48:	e0800002 	add	r0, r0, r2
   57a4c:	e5900000 	ldr	r0, [r0]
   57a50:	e1580000 	cmp	r8, r0
   57a54:	3a000008 	bcc	57a7c <storing_loop_next>
   57a58:	e3a00008 	mov	r0, #8
   57a5c:	e0000093 	mul	r0, r3, r0
   57a60:	e0800002 	add	r0, r0, r2
   57a64:	e2800004 	add	r0, r0, #4
   57a68:	e5900000 	ldr	r0, [r0]
   57a6c:	e1580000 	cmp	r8, r0
   57a70:	8a000001 	bhi	57a7c <storing_loop_next>
   57a74:	e3a04001 	mov	r4, #1
   57a78:	ea000006 	b	57a98 <storing_ck_pass>

00057a7c <storing_loop_next>:
   57a7c:	e2833001 	add	r3, r3, #1
   57a80:	eaffffec 	b	57a38 <storing_ck_loop>

00057a84 <storing_ck_valid>:
   57a84:	e3540000 	cmp	r4, #0
   57a88:	0a000000 	beq	57a90 <storing_ck_fail>
   57a8c:	ea000001 	b	57a98 <storing_ck_pass>

00057a90 <storing_ck_fail>:
   57a90:	ea000000 	b	57a98 <storing_ck_pass>
   57a94:	eafffe21 	b	57320 <__error>

00057a98 <storing_ck_pass>:
   57a98:	e59d0020 	ldr	r0, [sp, #32]
   57a9c:	e59d101c 	ldr	r1, [sp, #28]
   57aa0:	e30021bf 	movw	r2, #447	; 0x1bf
   57aa4:	e1500002 	cmp	r0, r2
   57aa8:	0a00000b 	beq	57adc <STRBi12>
   57aac:	e30021d7 	movw	r2, #471	; 0x1d7
   57ab0:	e1500002 	cmp	r0, r2
   57ab4:	0a00000a 	beq	57ae4 <STRi12>

00057ab8 <storing_ctx_restoring>:
   57ab8:	e59d0014 	ldr	r0, [sp, #20]
   57abc:	e128f000 	msr	CPSR_f, r0
   57ac0:	e59d0000 	ldr	r0, [sp]
   57ac4:	e59d1004 	ldr	r1, [sp, #4]
   57ac8:	e59d2008 	ldr	r2, [sp, #8]
   57acc:	e59d300c 	ldr	r3, [sp, #12]
   57ad0:	e59d4010 	ldr	r4, [sp, #16]
   57ad4:	e28dd018 	add	sp, sp, #24
   57ad8:	e12fff1e 	bx	lr

00057adc <STRBi12>:
   57adc:	e5c81000 	strb	r1, [r8]
   57ae0:	eafffff4 	b	57ab8 <storing_ctx_restoring>

00057ae4 <STRi12>:
   57ae4:	e5881000 	str	r1, [r8]
   57ae8:	eafffff2 	b	57ab8 <storing_ctx_restoring>

00057aec <.curr_cpt_id>:
   57aec:	00000000 	andeq	r0, r0, r0

00057af0 <.total_cpt_cnt>:
   57af0:	00000003 	andeq	r0, r0, r3

00057af4 <.curr_cpt_stack_pointer_offset>:
   57af4:	00000000 	andeq	r0, r0, r0

00057af8 <.cpt_stack>:
	...
   57c88:	00046d97 	muleq	r4, r7, sp
   57c8c:	00046db7 			; <UNDEFINED> instruction: 0x00046db7
   57c90:	00057aec 	andeq	r7, r5, ip, ror #21
   57c94:	00057af8 	strdeq	r7, [r5], -r8
   57c98:	00046def 	andeq	r6, r4, pc, ror #27
   57c9c:	00057af4 	strdeq	r7, [r5], -r4
   57ca0:	00046e27 	andeq	r6, r4, r7, lsr #28
   57ca4:	00000000 	andeq	r0, r0, r0

00057ca8 <__error_found_from_arm>:
   57ca8:	e51ff004 	ldr	pc, [pc, #-4]	; 57cac <__error_found_from_arm+0x4>
   57cac:	0004495b 	andeq	r4, r4, fp, asr r9

Disassembly of section .bss:

00057cb0 <__bss_start>:
   57cb0:	00000000 	andeq	r0, r0, r0

00057cb4 <recording_cnt>:
   57cb4:	00000000 	andeq	r0, r0, r0

00057cb8 <stepperPos>:
   57cb8:	00000000 	andeq	r0, r0, r0

00057cbc <ringbuffer_init_flag>:
   57cbc:	00000000 	andeq	r0, r0, r0

00057cc0 <cnt>:
   57cc0:	00000000 	andeq	r0, r0, r0

00057cc4 <ret_recording_finish>:
   57cc4:	00000000 	andeq	r0, r0, r0

00057cc8 <ret_hash_init_flag>:
   57cc8:	00000000 	andeq	r0, r0, r0

00057ccc <rd_optee_init>:
   57ccc:	00000000 	andeq	r0, r0, r0

00057cd0 <invoke_cnt>:
   57cd0:	00000000 	andeq	r0, r0, r0

00057cd4 <completed.10554>:
   57cd4:	00000000 	andeq	r0, r0, r0

00057cd8 <teec_mutex>:
	...

00057cf0 <charBuf>:
	...

00057d00 <adc_key_in>:
   57d00:	00000000 	andeq	r0, r0, r0

00057d04 <lcd>:
   57d04:	00000000 	andeq	r0, r0, r0

00057d08 <ringBuffer>:
	...

098ee510 <current_cpt_id>:
 98ee510:	00000000 	andeq	r0, r0, r0

098ee514 <ctx>:
	...

098ee51c <state>:
	...

098ee598 <hash>:
	...

098ee5b8 <err_origin>:
 98ee5b8:	00000000 	andeq	r0, r0, r0

098ee5bc <sess>:
	...

098ee5c4 <res>:
 98ee5c4:	00000000 	andeq	r0, r0, r0

098ee5c8 <op>:
	...

Disassembly of section .comment:

00000000 <.comment>:
   0:	6e616c63 	cdpvs	12, 6, cr6, cr1, cr3, {3}
   4:	65762067 	ldrbvs	r2, [r6, #-103]!	; 0xffffff99
   8:	6f697372 	svcvs	0x00697372
   c:	2e33206e 	cdpcs	0, 3, cr2, cr3, cr14, {3}
  10:	20302e39 	eorscs	r2, r0, r9, lsr lr
  14:	67617428 	strbvs	r7, [r1, -r8, lsr #8]!
  18:	45522f73 	ldrbmi	r2, [r2, #-3955]	; 0xfffff08d
  1c:	5341454c 	movtpl	r4, #5452	; 0x154c
  20:	39335f45 	ldmdbcc	r3!, {r0, r2, r6, r8, r9, sl, fp, ip, lr}
  24:	69662f30 	stmdbvs	r6!, {r4, r5, r8, r9, sl, fp, sp}^
  28:	296c616e 	stmdbcs	ip!, {r1, r2, r3, r5, r6, r8, sp, lr}^
  2c:	43434700 	movtmi	r4, #14080	; 0x3700
  30:	4c28203a 	stcmi	0, cr2, [r8], #-232	; 0xffffff18
  34:	72616e69 	rsbvc	r6, r1, #1680	; 0x690
  38:	4347206f 	movtmi	r2, #28783	; 0x706f
  3c:	2e362043 	cdpcs	0, 3, cr2, cr6, cr3, {2}
  40:	30322d32 	eorscc	r2, r2, r2, lsr sp
  44:	312e3631 			; <UNDEFINED> instruction: 0x312e3631
  48:	36202931 			; <UNDEFINED> instruction: 0x36202931
  4c:	312e322e 			; <UNDEFINED> instruction: 0x312e322e
  50:	31303220 	teqcc	r0, r0, lsr #4
  54:	31303136 	teqcc	r0, r6, lsr r1
  58:	43470036 	movtmi	r0, #28726	; 0x7036
  5c:	28203a43 	stmdacs	r0!, {r0, r1, r6, r9, fp, ip, sp}
  60:	6e756255 	mrcvs	2, 3, r6, cr5, cr5, {2}
  64:	39207574 	stmdbcc	r0!, {r2, r4, r5, r6, r8, sl, ip, sp, lr}
  68:	302e342e 	eorcc	r3, lr, lr, lsr #8
  6c:	6275312d 	rsbsvs	r3, r5, #1073741835	; 0x4000000b
  70:	75746e75 	ldrbvc	r6, [r4, #-3701]!	; 0xfffff18b
  74:	30327e31 	eorscc	r7, r2, r1, lsr lr
  78:	2e34302e 	cdpcs	0, 3, cr3, cr4, cr14, {1}
  7c:	39202932 	stmdbcc	r0!, {r1, r4, r5, r8, fp, sp}
  80:	302e342e 	eorcc	r3, lr, lr, lsr #8
	...

Disassembly of section .ARM.attributes:

00000000 <.ARM.attributes>:
   0:	00003841 	andeq	r3, r0, r1, asr #16
   4:	61656100 	cmnvs	r5, r0, lsl #2
   8:	01006962 	tsteq	r0, r2, ror #18
   c:	0000002e 	andeq	r0, r0, lr, lsr #32
  10:	412d3705 			; <UNDEFINED> instruction: 0x412d3705
  14:	070a0600 	streq	r0, [sl, -r0, lsl #12]
  18:	09010841 	stmdbeq	r1, {r0, r6, fp}
  1c:	11040a02 	tstne	r4, r2, lsl #20
  20:	13041201 	movwne	r1, #16897	; 0x4201
  24:	15011401 	strne	r1, [r1, #-1025]	; 0xfffffbff
  28:	18031701 	stmdane	r3, {r0, r8, r9, sl, ip}
  2c:	1c021a01 			; <UNDEFINED> instruction: 0x1c021a01
  30:	22011e01 	andcs	r1, r1, #1, 28
  34:	44012601 	strmi	r2, [r1], #-1537	; 0xfffff9ff
  38:	地址 0x0000000000000038 越界。


Disassembly of section .debug_aranges:

00000000 <.debug_aranges>:
   0:	0000001c 	andeq	r0, r0, ip, lsl r0
   4:	09ed0002 	stmibeq	sp!, {r1}^
   8:	00040000 	andeq	r0, r4, r0
   c:	00000000 	andeq	r0, r0, r0
  10:	00040adc 	ldrdeq	r0, [r4], -ip
  14:	000031e6 	andeq	r3, r0, r6, ror #3
	...
  20:	0000001c 	andeq	r0, r0, ip, lsl r0
  24:	14600002 	strbtne	r0, [r0], #-2
  28:	00040000 	andeq	r0, r4, r0
  2c:	00000000 	andeq	r0, r0, r0
  30:	00043cc4 	andeq	r3, r4, r4, asr #25
  34:	00000cd8 	ldrdeq	r0, [r0], -r8
	...
  40:	0000001c 	andeq	r0, r0, ip, lsl r0
  44:	1f3e0002 	svcne	0x003e0002
  48:	00040000 	andeq	r0, r4, r0
  4c:	00000000 	andeq	r0, r0, r0
  50:	00057160 	andeq	r7, r5, r0, ror #2
  54:	00000b44 	andeq	r0, r0, r4, asr #22
	...
  60:	0000001c 	andeq	r0, r0, ip, lsl r0
  64:	1fd30002 	svcne	0x00d30002
  68:	00040000 	andeq	r0, r4, r0
  6c:	00000000 	andeq	r0, r0, r0
  70:	0004656c 	andeq	r6, r4, ip, ror #10
  74:	000000f8 	strdeq	r0, [r0], -r8
	...
  80:	0000001c 	andeq	r0, r0, ip, lsl r0
  84:	20650002 	rsbcs	r0, r5, r2
  88:	00040000 	andeq	r0, r4, r0
  8c:	00000000 	andeq	r0, r0, r0
  90:	0004499c 	muleq	r4, ip, r9
  94:	00000776 	andeq	r0, r0, r6, ror r7
	...
  a0:	0000001c 	andeq	r0, r0, ip, lsl r0
  a4:	2ebb0002 	cdpcs	0, 11, cr0, cr11, cr2, {0}
  a8:	00040000 	andeq	r0, r4, r0
  ac:	00000000 	andeq	r0, r0, r0
  b0:	00045114 	andeq	r5, r4, r4, lsl r1
  b4:	00000030 	andeq	r0, r0, r0, lsr r0
	...
  c0:	00000014 	andeq	r0, r0, r4, lsl r0
  c4:	2f970002 	svccs	0x00970002
  c8:	00040000 	andeq	r0, r4, r0
	...
  d8:	0000002c 	andeq	r0, r0, ip, lsr #32
  dc:	301f0002 	andscc	r0, pc, r2
  e0:	00040000 	andeq	r0, r4, r0
  e4:	00000000 	andeq	r0, r0, r0
  e8:	00045144 	andeq	r5, r4, r4, asr #2
  ec:	00000024 	andeq	r0, r0, r4, lsr #32
  f0:	00010b20 	andeq	r0, r1, r0, lsr #22
  f4:	00000008 	andeq	r0, r0, r8
  f8:	00046664 	andeq	r6, r4, r4, ror #12
  fc:	00000004 	andeq	r0, r0, r4
	...
 108:	00000024 	andeq	r0, r0, r4, lsr #32
 10c:	30f60002 	rscscc	r0, r6, r2
 110:	00040000 	andeq	r0, r4, r0
 114:	00000000 	andeq	r0, r0, r0
 118:	00010b28 	andeq	r0, r1, r8, lsr #22
 11c:	00000004 	andeq	r0, r0, r4
 120:	00046668 	andeq	r6, r4, r8, ror #12
 124:	00000004 	andeq	r0, r0, r4
	...

Disassembly of section .debug_pubnames:

00000000 <.debug_pubnames>:
   0:	000002b6 			; <UNDEFINED> instruction: 0x000002b6
   4:	00000002 	andeq	r0, r0, r2
   8:	061c0000 	ldreq	r0, [ip], -r0
   c:	01800000 	orreq	r0, r0, r0
  10:	4c6d0000 	stclmi	0, cr0, [sp], #-0
  14:	756c6f42 	strbvc	r6, [ip, #-3906]!	; 0xfffff0be
  18:	65745373 	ldrbvs	r5, [r4, #-883]!	; 0xfffffc8d
  1c:	78644970 	stmdavc	r4!, {r4, r5, r6, r8, fp, lr}^
  20:	00003e00 	andeq	r3, r0, r0, lsl #28
  24:	63657200 	cmnvs	r5, #0, 4
  28:	6964726f 	stmdbvs	r4!, {r0, r1, r2, r3, r5, r6, r9, ip, sp, lr}^
  2c:	635f676e 	cmpvs	pc, #28835840	; 0x1b80000
  30:	1300746e 	movwne	r7, #1134	; 0x46e
  34:	75000004 	strvc	r0, [r0, #-4]
  38:	74616470 	strbtvc	r6, [r1], #-1136	; 0xfffffb90
  3c:	72635365 	rsbvc	r5, r3, #-1811939327	; 0x94000001
  40:	006e6565 	rsbeq	r6, lr, r5, ror #10
  44:	00000078 	andeq	r0, r0, r8, ror r0
  48:	65747375 	ldrbvs	r7, [r4, #-885]!	; 0xfffffc8b
  4c:	65507370 	ldrbvs	r7, [r0, #-880]	; 0xfffffc90
  50:	004c4d72 	subeq	r4, ip, r2, ror sp
  54:	00000060 	andeq	r0, r0, r0, rrx
  58:	65747375 	ldrbvs	r7, [r4, #-885]!	; 0xfffffc8b
  5c:	65507370 	ldrbvs	r7, [r0, #-880]	; 0xfffffc90
  60:	004d4d72 	subeq	r4, sp, r2, ror sp
  64:	000001e6 	andeq	r0, r0, r6, ror #3
  68:	76657270 			; <UNDEFINED> instruction: 0x76657270
  6c:	0079654b 	rsbseq	r6, r9, fp, asr #10
  70:	000004cf 	andeq	r0, r0, pc, asr #9
  74:	64616572 	strbtvs	r6, [r1], #-1394	; 0xfffffa8e
  78:	0079654b 	rsbseq	r6, r9, fp, asr #10
  7c:	0000050f 	andeq	r0, r0, pc, lsl #10
  80:	5f746567 	svcpl	0x00746567
  84:	0079656b 	rsbseq	r6, r9, fp, ror #10
  88:	00000129 	andeq	r0, r0, r9, lsr #2
  8c:	6f424c6d 	svcvs	0x00424c6d
  90:	5373756c 	cmnpl	r3, #108, 10	; 0x1b000000
  94:	73706574 	cmnvc	r0, #116, 10	; 0x1d000000
  98:	0001d500 	andeq	sp, r1, r0, lsl #10
  9c:	79656b00 	stmdbvc	r5!, {r8, r9, fp, sp, lr}^
  a0:	6f626544 	svcvs	0x00626544
  a4:	65636e75 	strbvs	r6, [r3, #-3701]!	; 0xfffff18b
  a8:	00015e00 	andeq	r5, r1, r0, lsl #28
  ac:	424c6d00 	submi	r6, ip, #0, 26
  b0:	6f426769 	svcvs	0x00426769
  b4:	0073756c 	rsbseq	r7, r3, ip, ror #10
  b8:	00000219 	andeq	r0, r0, r9, lsl r2
  bc:	76657270 			; <UNDEFINED> instruction: 0x76657270
  c0:	67697254 			; <UNDEFINED> instruction: 0x67697254
  c4:	00726567 	rsbseq	r6, r2, r7, ror #10
  c8:	000002a5 	andeq	r0, r0, r5, lsr #5
  cc:	0064636c 	rsbeq	r6, r4, ip, ror #6
  d0:	000001a2 	andeq	r0, r0, r2, lsr #3
  d4:	70657473 	rsbvc	r7, r5, r3, ror r4
  d8:	50726570 	rsbspl	r6, r2, r0, ror r5
  dc:	8900736f 	stmdbhi	r0, {r0, r1, r2, r3, r5, r6, r8, r9, ip, sp, lr}
  e0:	6d000000 	stcvs	0, cr0, [r0, #-0]
  e4:	726f746f 	rsbvc	r7, pc, #1862270976	; 0x6f000000
  e8:	50726944 	rsbspl	r6, r2, r4, asr #18
  ec:	66006e69 	strvs	r6, [r0], -r9, ror #28
  f0:	73000002 	movwvc	r0, #2
  f4:	61697265 	cmnvs	r9, r5, ror #4
  f8:	7274536c 	rsbsvc	r5, r4, #108, 6	; 0xb0000001
  fc:	006e654c 	rsbeq	r6, lr, ip, asr #10
 100:	000001c4 	andeq	r0, r0, r4, asr #3
 104:	5279656b 	rsbspl	r6, r9, #448790528	; 0x1ac00000
 108:	61657065 	cmnvs	r5, r5, rrx
 10c:	6c654474 	cfstrdvs	mvd4, [r5], #-464	; 0xfffffe30
 110:	91007961 	tstls	r0, r1, ror #18
 114:	6d000001 	stcvs	0, cr0, [r0, #-4]
 118:	6c6f424c 	sfmvs	f4, 2, [pc], #-304	; fffffff0 <__bss_end__+0xf67119ec>
 11c:	74537375 	ldrbvc	r7, [r3], #-885	; 0xfffffc8b
 120:	88007065 	stmdahi	r0, {r0, r2, r5, r6, ip, sp, lr}
 124:	63000002 	movwvs	r0, #2
 128:	42726168 	rsbsmi	r6, r2, #104, 2
 12c:	a9006675 	stmdbge	r0, {r0, r2, r4, r5, r6, r9, sl, sp, lr}
 130:	72000004 	andvc	r0, r0, #4
 134:	53646165 	cmnpl	r4, #1073741849	; 0x40000019
 138:	61697265 	cmnvs	r9, r5, ror #4
 13c:	035b006c 	cmpeq	fp, #108	; 0x6c
 140:	6f6c0000 	svcvs	0x006c0000
 144:	6600706f 	strvs	r7, [r0], -pc, rrx
 148:	66000005 	strvs	r0, [r0], -r5
 14c:	6177726f 	cmnvs	r7, pc, ror #4
 150:	745f6472 	ldrbvc	r6, [pc], #-1138	; 158 <_init-0x109c8>
 154:	65677261 	strbvs	r7, [r7, #-609]!	; 0xfffffd9f
 158:	03970074 	orrseq	r0, r7, #116	; 0x74
 15c:	72700000 	rsbsvc	r0, r0, #0
 160:	7365636f 	cmnvc	r5, #-1140850687	; 0xbc000001
 164:	72655373 	rsbvc	r5, r5, #-872415231	; 0xcc000001
 168:	006c6169 	rsbeq	r6, ip, r9, ror #2
 16c:	00000544 	andeq	r0, r0, r4, asr #10
 170:	654b6f64 	strbvs	r6, [fp, #-3940]	; 0xfffff09c
 174:	74634179 	strbtvc	r4, [r3], #-377	; 0xfffffe87
 178:	006e6f69 	rsbeq	r6, lr, r9, ror #30
 17c:	00000208 	andeq	r0, r0, r8, lsl #4
 180:	76657270 			; <UNDEFINED> instruction: 0x76657270
 184:	54676942 	strbtpl	r6, [r7], #-2370	; 0xfffff6be
 188:	67676972 			; <UNDEFINED> instruction: 0x67676972
 18c:	c1007265 	tstgt	r0, r5, ror #4
 190:	62000003 	andvs	r0, r0, #3
 194:	73756c6f 	cmnvc	r5, #28416	; 0x6f00
 198:	00027700 	andeq	r7, r2, r0, lsl #14
 19c:	63646100 	cmnvs	r4, #0, 2
 1a0:	79656b5f 	stmdbvc	r5!, {r0, r1, r2, r3, r4, r6, r8, r9, fp, sp, lr}^
 1a4:	006e695f 	rsbeq	r6, lr, pc, asr r9
 1a8:	00000463 	andeq	r0, r0, r3, ror #8
 1ac:	63656863 	cmnvs	r5, #6488064	; 0x630000
 1b0:	6972546b 	ldmdbvs	r2!, {r0, r1, r3, r5, r6, sl, ip, lr}^
 1b4:	72656767 	rsbvc	r6, r5, #27000832	; 0x19c0000
 1b8:	01020073 	tsteq	r2, r3, ror r0
 1bc:	656b0000 	strbvs	r0, [fp, #-0]!
 1c0:	004f0079 	subeq	r0, pc, r9, ror r0	; <UNPREDICTABLE>
 1c4:	6c670000 	stclvs	0, cr0, [r7], #-0
 1c8:	6c61626f 	sfmvs	f6, 2, [r1], #-444	; 0xfffffe44
 1cc:	7461645f 	strbtvc	r6, [r1], #-1119	; 0xfffffba1
 1d0:	00f10061 	rscseq	r0, r1, r1, rrx
 1d4:	554e0000 	strbpl	r0, [lr, #-0]
 1d8:	454b5f4d 	strbmi	r5, [fp, #-3917]	; 0xfffff0b3
 1dc:	bc005359 	stclt	3, cr5, [r0], {89}	; 0x59
 1e0:	62000000 	andvs	r0, r0, #0
 1e4:	72546769 	subsvc	r6, r4, #27525120	; 0x1a40000
 1e8:	65676769 	strbvs	r6, [r7, #-1897]!	; 0xfffff897
 1ec:	6e695072 	mcrvs	0, 3, r5, cr9, cr2, {3}
 1f0:	00024e00 	andeq	r4, r2, r0, lsl #28
 1f4:	72657300 	rsbvc	r7, r5, #0, 6
 1f8:	536c6169 	cmnpl	ip, #1073741850	; 0x4000001a
 1fc:	65527274 	ldrbvs	r7, [r2, #-628]	; 0xfffffd8c
 200:	00796461 	rsbseq	r6, r9, r1, ror #8
 204:	00000113 	andeq	r0, r0, r3, lsl r1
 208:	6f424c6d 	svcvs	0x00424c6d
 20c:	5373756c 	cmnpl	r3, #108, 10	; 0x1b000000
 210:	73706574 	cmnvc	r0, #116, 10	; 0x1d000000
 214:	676e654c 	strbvs	r6, [lr, -ip, asr #10]!
 218:	6f006874 	svcvs	0x00006874
 21c:	6d000001 	stcvs	0, cr0, [r0, #-4]
 220:	6573554c 	ldrbvs	r5, [r3, #-1356]!	; 0xfffffab4
 224:	034a0064 	movteq	r0, #41060	; 0xa064
 228:	65730000 	ldrbvs	r0, [r3, #-0]!
 22c:	00707574 	rsbseq	r7, r0, r4, ror r5
 230:	000000cd 	andeq	r0, r0, sp, asr #1
 234:	5f636461 	svcpl	0x00636461
 238:	5f79656b 	svcpl	0x0079656b
 23c:	006c6176 	rsbeq	r6, ip, r6, ror r1
 240:	000001b3 			; <UNDEFINED> instruction: 0x000001b3
 244:	7473616c 	ldrbtvc	r6, [r3], #-364	; 0xfffffe94
 248:	5279654b 	rsbspl	r6, r9, #314572800	; 0x12c00000
 24c:	61657065 	cmnvs	r5, r5, rrx
 250:	00744174 	rsbseq	r4, r4, r4, ror r1
 254:	0000009a 	muleq	r0, sl, r0
 258:	6f746f6d 	svcvs	0x00746f6d
 25c:	65745372 	ldrbvs	r5, [r4, #-882]!	; 0xfffffc8e
 260:	6e695070 	mcrvs	0, 3, r5, cr9, cr0, {3}
 264:	00002600 	andeq	r2, r0, r0, lsl #12
 268:	63657200 	cmnvs	r5, #0, 4
 26c:	6964726f 	stmdbvs	r4!, {r0, r1, r2, r3, r5, r6, r9, ip, sp, lr}^
 270:	665f676e 	ldrbvs	r6, [pc], -lr, ror #14
 274:	0067616c 	rsbeq	r6, r7, ip, ror #2
 278:	0000022a 	andeq	r0, r0, sl, lsr #4
 27c:	69726573 	ldmdbvs	r2!, {r0, r1, r4, r5, r6, r8, sl, sp, lr}^
 280:	74536c61 	ldrbvc	r6, [r3], #-3169	; 0xfffff39f
 284:	05880072 	streq	r0, [r8, #114]	; 0x72
 288:	616d0000 	cmnvs	sp, r0
 28c:	ab006e69 	blge	1bc38 <.DATA_REGION_0__data_end+0xaf20>
 290:	74000000 	strvc	r0, [r0], #-0
 294:	67676972 			; <UNDEFINED> instruction: 0x67676972
 298:	69507265 	ldmdbvs	r0, {r0, r2, r5, r6, r9, ip, sp, lr}^
 29c:	014d006e 	cmpeq	sp, lr, rrx
 2a0:	4c6d0000 	stclmi	0, cr0, [sp], #-0
 2a4:	756c6f42 	strbvc	r6, [ip, #-3906]!	; 0xfffff0be
 2a8:	01f70073 	mvnseq	r0, r3, ror r0
 2ac:	69750000 	ldmdbvs	r5!, {}^	; <UNPREDICTABLE>
 2b0:	74617453 	strbtvc	r7, [r1], #-1107	; 0xfffffbad
 2b4:	00000065 	andeq	r0, r0, r5, rrx
 2b8:	00c70000 	sbceq	r0, r7, r0
 2bc:	00020000 	andeq	r0, r2, r0
 2c0:	0000061c 	andeq	r0, r0, ip, lsl r6
 2c4:	00000268 	andeq	r0, r0, r8, ror #4
 2c8:	000000d5 	ldrdeq	r0, [r0], -r5
 2cc:	69726553 	ldmdbvs	r2!, {r0, r1, r4, r6, r8, sl, sp, lr}^
 2d0:	615f6c61 	cmpvs	pc, r1, ror #24
 2d4:	6c696176 	stfvse	f6, [r9], #-472	; 0xfffffe28
 2d8:	656c6261 	strbvs	r6, [ip, #-609]!	; 0xfffffd9f
 2dc:	0001a500 	andeq	sl, r1, r0, lsl #10
 2e0:	65737500 	ldrbvs	r7, [r3, #-1280]!	; 0xfffffb00
 2e4:	b5007363 	strlt	r7, [r0, #-867]	; 0xfffffc9d
 2e8:	53000000 	movwpl	r0, #0
 2ec:	61697265 	cmnvs	r9, r5, ror #4
 2f0:	65625f6c 	strbvs	r5, [r2, #-3948]!	; 0xfffff094
 2f4:	006e6967 	rsbeq	r6, lr, r7, ror #18
 2f8:	000001e9 	andeq	r0, r0, r9, ror #3
 2fc:	49556f74 	ldmdbmi	r5, {r2, r4, r5, r6, r8, r9, sl, fp, sp, lr}^
 300:	c900746e 	stmdbgt	r0, {r1, r2, r3, r5, r6, sl, ip, sp, lr}
 304:	64000001 	strvs	r0, [r0], #-1
 308:	79616c65 	stmdbvc	r1!, {r0, r2, r5, r6, sl, fp, sp, lr}^
 30c:	7263694d 	rsbvc	r6, r3, #1261568	; 0x134000
 310:	6365736f 	cmnvs	r5, #-1140850687	; 0xbc000001
 314:	73646e6f 	cmnvc	r4, #1776	; 0x6f0
 318:	00008700 	andeq	r8, r0, r0, lsl #14
 31c:	67696400 	strbvs	r6, [r9, -r0, lsl #8]!
 320:	6c617469 	cfstrdvs	mvd7, [r1], #-420	; 0xfffffe5c
 324:	74697257 	strbtvc	r7, [r9], #-599	; 0xfffffda9
 328:	00550065 	subseq	r0, r5, r5, rrx
 32c:	69640000 	stmdbvs	r4!, {}^	; <UNPREDICTABLE>
 330:	61746967 	cmnvs	r4, r7, ror #18
 334:	6165526c 	cmnvs	r5, ip, ror #4
 338:	00f90064 	rscseq	r0, r9, r4, rrx
 33c:	65530000 	ldrbvs	r0, [r3, #-0]
 340:	6c616972 			; <UNDEFINED> instruction: 0x6c616972
 344:	6165725f 	cmnvs	r5, pc, asr r2
 348:	00270064 	eoreq	r0, r7, r4, rrx
 34c:	69700000 	ldmdbvs	r0!, {}^	; <UNPREDICTABLE>
 350:	646f4d6e 	strbtvs	r4, [pc], #-3438	; 358 <_init-0x107c8>
 354:	011d0065 	tsteq	sp, r5, rrx
 358:	65530000 	ldrbvs	r0, [r3, #-0]
 35c:	6c616972 			; <UNDEFINED> instruction: 0x6c616972
 360:	6972775f 	ldmdbvs	r2!, {r0, r1, r2, r3, r4, r6, r8, r9, sl, ip, sp, lr}^
 364:	4f006574 	svcmi	0x00006574
 368:	61000001 	tstvs	r0, r1
 36c:	6f6c616e 	svcvs	0x006c616e
 370:	61655267 	cmnvs	r5, r7, ror #4
 374:	01810064 	orreq	r0, r1, r4, rrx
 378:	696d0000 	stmdbvs	sp!, {}^	; <UNPREDICTABLE>
 37c:	73696c6c 	cmnvc	r9, #108, 24	; 0x6c00
 380:	00000000 	andeq	r0, r0, r0
 384:	00002500 	andeq	r2, r0, r0, lsl #10
 388:	84000200 	strhi	r0, [r0], #-512	; 0xfffffe00
 38c:	49000008 	stmdbmi	r0, {r3}
 390:	26000000 	strcs	r0, [r0], -r0
 394:	6c000000 	stcvs	0, cr0, [r0], {-0}
 398:	6f5f6465 	svcvs	0x005f6465
 39c:	0037006e 	eorseq	r0, r7, lr, rrx
 3a0:	656c0000 	strbvs	r0, [ip, #-0]!
 3a4:	666f5f64 	strbtvs	r5, [pc], -r4, ror #30
 3a8:	00000066 	andeq	r0, r0, r6, rrx
 3ac:	004a0000 	subeq	r0, sl, r0
 3b0:	00020000 	andeq	r0, r2, r0
 3b4:	000008cd 	andeq	r0, r0, sp, asr #17
 3b8:	00000120 	andeq	r0, r0, r0, lsr #2
 3bc:	00000026 	andeq	r0, r0, r6, lsr #32
 3c0:	5f64636c 	svcpl	0x0064636c
 3c4:	69676562 	stmdbvs	r7!, {r1, r5, r6, r8, sl, sp, lr}^
 3c8:	0062006e 	rsbeq	r0, r2, lr, rrx
 3cc:	636c0000 	cmnvs	ip, #0
 3d0:	6c635f64 	stclvs	15, cr5, [r3], #-400	; 0xfffffe70
 3d4:	00726165 	rsbseq	r6, r2, r5, ror #2
 3d8:	000000be 	strheq	r0, [r0], -lr
 3dc:	5f64636c 	svcpl	0x0064636c
 3e0:	43746573 	cmnmi	r4, #482344960	; 0x1cc00000
 3e4:	6f737275 	svcvs	0x00737275
 3e8:	00820072 	addeq	r0, r2, r2, ror r0
 3ec:	636c0000 	cmnvs	ip, #0
 3f0:	72705f64 	rsbsvc	r5, r0, #100, 30	; 0x190
 3f4:	00746e69 	rsbseq	r6, r4, r9, ror #28
 3f8:	00000000 	andeq	r0, r0, r0

Disassembly of section .debug_info:

00000000 <.debug_info>:
       0:	00000618 	andeq	r0, r0, r8, lsl r6
       4:	00000005 	andeq	r0, r0, r5
       8:	01040000 	mrseq	r0, (UNDEF: 4)
       c:	00000000 	andeq	r0, r0, r0
      10:	002d000c 	eoreq	r0, sp, ip
      14:	00000000 	andeq	r0, r0, r0
      18:	003b0000 	eorseq	r0, fp, r0
      1c:	00000000 	andeq	r0, r0, r0
      20:	00300000 	eorseq	r0, r0, r0
      24:	83020000 	movwhi	r0, #8192	; 0x2000
      28:	37000000 	strcc	r0, [r0, -r0]
      2c:	01000000 	mrseq	r0, (UNDEF: 0)
      30:	b003052c 	andlt	r0, r3, ip, lsr #10
      34:	0300057c 	movweq	r0, #1404	; 0x57c
      38:	0000058c 	andeq	r0, r0, ip, lsl #11
      3c:	92020405 	andls	r0, r2, #83886080	; 0x5000000
      40:	37000000 	strcc	r0, [r0, -r0]
      44:	01000000 	mrseq	r0, (UNDEF: 0)
      48:	b403052d 	strlt	r0, [r3], #-1325	; 0xfffffad3
      4c:	0200057c 	andeq	r0, r0, #124, 10	; 0x1f000000
      50:	000000a0 	andeq	r0, r0, r0, lsr #1
      54:	00000037 	andeq	r0, r0, r7, lsr r0
      58:	03052e01 	movweq	r2, #24065	; 0x5e01
      5c:	00010cfc 	strdeq	r0, [r1], -ip
      60:	0000ac02 	andeq	sl, r0, r2, lsl #24
      64:	00007100 	andeq	r7, r0, r0, lsl #2
      68:	05310100 	ldreq	r0, [r1, #-256]!	; 0xffffff00
      6c:	0570ec03 	ldrbeq	lr, [r0, #-3075]!	; 0xfffff3fd
      70:	05be0300 	ldreq	r0, [lr, #768]!	; 0x300
      74:	04050000 	streq	r0, [r5], #-0
      78:	0000b802 	andeq	fp, r0, r2, lsl #16
      7c:	00007100 	andeq	r7, r0, r0, lsl #2
      80:	05320100 	ldreq	r0, [r2, #-256]!	; 0xffffff00
      84:	02077003 	andeq	r7, r7, #3
      88:	00c40200 	sbceq	r0, r4, r0, lsl #4
      8c:	00370000 	eorseq	r0, r7, r0
      90:	37010000 	strcc	r0, [r1, -r0]
      94:	0d000305 	stceq	3, cr0, [r0, #-20]	; 0xffffffec
      98:	d0020001 	andle	r0, r2, r1
      9c:	37000000 	strcc	r0, [r0, -r0]
      a0:	01000000 	mrseq	r0, (UNDEF: 0)
      a4:	04030538 	streq	r0, [r3], #-1336	; 0xfffffac8
      a8:	0200010d 	andeq	r0, r0, #1073741827	; 0x40000003
      ac:	000000dd 	ldrdeq	r0, [r0], -sp
      b0:	00000037 	andeq	r0, r0, r7, lsr r0
      b4:	03053a01 	movweq	r3, #23041	; 0x5a01
      b8:	00040ac8 	andeq	r0, r4, r8, asr #21
      bc:	0000e802 	andeq	lr, r0, r2, lsl #16
      c0:	00003700 	andeq	r3, r0, r0, lsl #14
      c4:	053b0100 	ldreq	r0, [fp, #-256]!	; 0xffffff00
      c8:	040acc03 	streq	ip, [sl], #-3075	; 0xfffff3fd
      cc:	00f60200 	rscseq	r0, r6, r0, lsl #4
      d0:	00de0000 	sbcseq	r0, lr, r0
      d4:	3e010000 	cdpcc	0, 0, cr0, cr1, cr0, {0}
      d8:	0a380305 	beq	e00cf4 <ringBuffer+0xda8fec>
      dc:	37040004 	strcc	r0, [r4, -r4]
      e0:	05000000 	streq	r0, [r0, #-0]
      e4:	000000ea 	andeq	r0, r0, sl, ror #1
      e8:	02060005 	andeq	r0, r6, #5
      ec:	08000001 	stmdaeq	r0, {r0}
      f0:	010b0207 	tsteq	fp, r7, lsl #4
      f4:	00370000 	eorseq	r0, r7, r0
      f8:	41010000 	mrsmi	r0, (UNDEF: 1)
      fc:	0a4c0305 	beq	1300d18 <ringBuffer+0x12a9010>
     100:	04020004 	streq	r0, [r2], #-4
     104:	37000003 	strcc	r0, [r0, -r3]
     108:	01000000 	mrseq	r0, (UNDEF: 0)
     10c:	50030543 	andpl	r0, r3, r3, asr #10
     110:	0200040a 	andeq	r0, r0, #167772160	; 0xa000000
     114:	00000114 	andeq	r0, r0, r4, lsl r1
     118:	00000124 	andeq	r0, r0, r4, lsr #2
     11c:	03054c01 	movweq	r4, #23553	; 0x5c01
     120:	0004666c 	andeq	r6, r4, ip, ror #12
     124:	00003707 	andeq	r3, r0, r7, lsl #14
     128:	01270200 			; <UNDEFINED> instruction: 0x01270200
     12c:	013a0000 	teqeq	sl, r0
     130:	4d010000 	stcmi	0, cr0, [r1, #-0]
     134:	0a540305 	beq	1500d50 <ringBuffer+0x14a9048>
     138:	46040004 	strmi	r0, [r4], -r4
     13c:	05000001 	streq	r0, [r0, #-1]
     140:	000000ea 	andeq	r0, r0, sl, ror #1
     144:	34030009 	strcc	r0, [r3], #-9
     148:	04000001 	streq	r0, [r0], #-1
     14c:	013a0204 	teqeq	sl, r4, lsl #4
     150:	01460000 	mrseq	r0, (UNDEF: 70)
     154:	50010000 	andpl	r0, r1, r0
     158:	0d080305 	stceq	3, cr0, [r8, #-20]	; 0xffffffec
     15c:	42020001 	andmi	r0, r2, #1
     160:	46000001 	strmi	r0, [r0], -r1
     164:	01000001 	tsteq	r0, r1
     168:	78030551 	stmdavc	r3, {r0, r4, r6, r8, sl}
     16c:	0200040a 	andeq	r0, r0, #167772160	; 0xa000000
     170:	0000014d 	andeq	r0, r0, sp, asr #2
     174:	00000146 	andeq	r0, r0, r6, asr #2
     178:	03055201 	movweq	r5, #20993	; 0x5201
     17c:	000207b4 			; <UNDEFINED> instruction: 0x000207b4
     180:	00015402 	andeq	r5, r1, r2, lsl #8
     184:	00003700 	andeq	r3, r0, r0, lsl #14
     188:	05530100 	ldrbeq	r0, [r3, #-256]	; 0xffffff00
     18c:	040a7c03 	streq	r7, [sl], #-3075	; 0xfffff3fd
     190:	01630200 	cmneq	r3, r0, lsl #4
     194:	01460000 	mrseq	r0, (UNDEF: 70)
     198:	55010000 	strpl	r0, [r1, #-0]
     19c:	0d0c0305 	stceq	3, cr0, [ip, #-20]	; 0xffffffec
     1a0:	6f020001 	svcvs	0x00020001
     1a4:	71000001 	tstvc	r0, r1
     1a8:	01000000 	mrseq	r0, (UNDEF: 0)
     1ac:	b8030557 	stmdalt	r3, {r0, r1, r2, r4, r6, r8, sl}
     1b0:	0200057c 	andeq	r0, r0, #124, 10	; 0x1f000000
     1b4:	0000017a 	andeq	r0, r0, sl, ror r1
     1b8:	00000071 	andeq	r0, r0, r1, ror r0
     1bc:	03055b01 	movweq	r5, #23297	; 0x5b01
     1c0:	00040ad0 	ldrdeq	r0, [r4], -r0	; <UNPREDICTABLE>
     1c4:	00018a02 	andeq	r8, r1, r2, lsl #20
     1c8:	00007100 	andeq	r7, r0, r0, lsl #2
     1cc:	055c0100 	ldrbeq	r0, [ip, #-256]	; 0xffffff00
     1d0:	040a8003 	streq	r8, [sl], #-3
     1d4:	01990200 	orrseq	r0, r9, r0, lsl #4
     1d8:	00710000 	rsbseq	r0, r1, r0
     1dc:	5d010000 	stcpl	0, cr0, [r1, #-0]
     1e0:	0a840305 	beq	fe100dfc <__bss_end__+0xf48127f8>
     1e4:	a5020004 	strge	r0, [r2, #-4]
     1e8:	37000001 	strcc	r0, [r0, -r1]
     1ec:	01000000 	mrseq	r0, (UNDEF: 0)
     1f0:	8803055e 	stmdahi	r3, {r1, r2, r3, r4, r6, r8, sl}
     1f4:	0200040a 	andeq	r0, r0, #167772160	; 0xa000000
     1f8:	000001ad 	andeq	r0, r0, sp, lsr #3
     1fc:	00000037 	andeq	r0, r0, r7, lsr r0
     200:	03056101 	movweq	r6, #20737	; 0x5101
     204:	0005710c 	andeq	r7, r5, ip, lsl #2
     208:	0001b502 	andeq	fp, r1, r2, lsl #10
     20c:	00003700 	andeq	r3, r0, r0, lsl #14
     210:	05640100 	strbeq	r0, [r4, #-256]!	; 0xffffff00
     214:	040ad403 	streq	sp, [sl], #-1027	; 0xfffffbfd
     218:	01c40200 	biceq	r0, r4, r0, lsl #4
     21c:	00370000 	eorseq	r0, r7, r0
     220:	65010000 	strvs	r0, [r1, #-0]
     224:	0ad80305 	beq	ff600e40 <__bss_end__+0xf5d1283c>
     228:	d0020004 	andle	r0, r2, r4
     22c:	3b000001 	blcc	238 <_init-0x108e8>
     230:	01000002 	tsteq	r0, r2
     234:	10030568 	andne	r0, r3, r8, ror #10
     238:	04000571 	streq	r0, [r0], #-1393	; 0xfffffa8f
     23c:	00000247 	andeq	r0, r0, r7, asr #4
     240:	0000ea05 	andeq	lr, r0, r5, lsl #20
     244:	03005000 	movweq	r5, #0
     248:	00000877 	andeq	r0, r0, r7, ror r8
     24c:	da020108 	ble	80674 <ringBuffer+0x2896c>
     250:	5f000001 	svcpl	0x00000001
     254:	01000002 	tsteq	r0, r2
     258:	10030569 	andne	r0, r3, r9, ror #10
     25c:	0300010d 	movweq	r0, #269	; 0x10d
     260:	000001e9 	andeq	r0, r0, r9, ror #3
     264:	ef020102 	svc	0x00020102
     268:	37000001 	strcc	r0, [r0, -r1]
     26c:	01000000 	mrseq	r0, (UNDEF: 0)
     270:	1403056a 	strne	r0, [r3], #-1386	; 0xfffffa96
     274:	0200010d 	andeq	r0, r0, #1073741827	; 0x40000003
     278:	000001fc 	strdeq	r0, [r0], -ip
     27c:	00000037 	andeq	r0, r0, r7, lsr r0
     280:	03054201 	movweq	r4, #20993	; 0x5201
     284:	00057d00 	andeq	r7, r5, r0, lsl #26
     288:	00020702 	andeq	r0, r2, r2, lsl #14
     28c:	00029900 	andeq	r9, r2, r0, lsl #18
     290:	05580100 	ldrbeq	r0, [r8, #-256]	; 0xffffff00
     294:	057cf003 	ldrbeq	pc, [ip, #-3]!	; <UNPREDICTABLE>
     298:	02470400 	subeq	r0, r7, #0, 8
     29c:	ea050000 	b	1402a4 <ringBuffer+0xe859c>
     2a0:	10000000 	andne	r0, r0, r0
     2a4:	020f0200 	andeq	r0, pc, #0, 4
     2a8:	02b60000 	adcseq	r0, r6, #0
     2ac:	6d010000 	stcvs	0, cr0, [r1, #-0]
     2b0:	7d040305 	stcvc	3, cr0, [r4, #-20]	; 0xffffffec
     2b4:	c1080005 	tstgt	r8, r5
     2b8:	27000002 	strcs	r0, [r0, -r2]
     2bc:	02000002 	andeq	r0, r0, #2
     2c0:	0213090a 	andseq	r0, r3, #163840	; 0x28000
     2c4:	02040000 	andeq	r0, r4, #0
     2c8:	12550a08 	subsne	r0, r5, #8, 20	; 0x8000
     2cc:	02d60000 	sbcseq	r0, r6, #0
     2d0:	09020000 	stmdbeq	r2, {}	; <UNPREDICTABLE>
     2d4:	83030000 	movwhi	r0, #12288	; 0x3000
     2d8:	07000005 	streq	r0, [r0, -r5]
     2dc:	01040b04 	tsteq	r4, r4, lsl #22
     2e0:	02350c49 	eorseq	r0, r5, #18688	; 0x4900
     2e4:	0c000000 	stceq	0, cr0, [r0], {-0}
     2e8:	0000023b 	andeq	r0, r0, fp, lsr r2
     2ec:	040b0001 	streq	r0, [fp], #-1
     2f0:	420c4a01 	andmi	r4, ip, #4096	; 0x1000
     2f4:	00000002 	andeq	r0, r0, r2
     2f8:	0002470c 	andeq	r4, r2, ip, lsl #14
     2fc:	0b000100 	bleq	704 <_init-0x1041c>
     300:	0c460104 	stfeqe	f0, [r6], {4}
     304:	0000024b 	andeq	r0, r0, fp, asr #4
     308:	02500c00 	subseq	r0, r0, #0, 24
     30c:	00010000 	andeq	r0, r1, r0
     310:	4001040b 	andmi	r0, r1, fp, lsl #8
     314:	0002550c 	andeq	r5, r2, ip, lsl #10
     318:	5f0c0000 	svcpl	0x000c0000
     31c:	01000002 	tsteq	r0, r2
     320:	0002660c 	andeq	r6, r2, ip, lsl #12
     324:	6f0c0200 	svcvs	0x000c0200
     328:	03000002 	movweq	r0, #2
     32c:	0002780c 	andeq	r7, r2, ip, lsl #16
     330:	830c0400 	movwhi	r0, #50176	; 0xc400
     334:	05000002 	streq	r0, [r0, #-2]
     338:	01040b00 	tsteq	r4, r0, lsl #22
     33c:	028c0c47 	addeq	r0, ip, #18176	; 0x4700
     340:	0c000000 	stceq	0, cr0, [r0], {-0}
     344:	00000291 	muleq	r0, r1, r2
     348:	000d0001 	andeq	r0, sp, r1
     34c:	08000400 	stmdaeq	r0, {sl}
     350:	01000001 	tsteq	r0, r1
     354:	0002b95b 	andeq	fp, r2, fp, asr r9
     358:	0e6f0100 	poweqe	f0, f7, f0
     35c:	00040108 	andeq	r0, r4, r8, lsl #2
     360:	000000c8 	andeq	r0, r0, r8, asr #1
     364:	02bf5b01 	adcseq	r5, pc, #1024	; 0x400
     368:	90010000 	andls	r0, r1, r0
     36c:	0c7d020f 	lfmeq	f0, 2, [sp], #-60	; 0xffffffc4
     370:	000003ec 	andeq	r0, r0, ip, ror #7
     374:	00379001 	eorseq	r9, r7, r1
     378:	02100000 	andseq	r0, r0, #0
     37c:	03f2087d 	mvnseq	r0, #8192000	; 0x7d0000
     380:	a1010000 	mrsge	r0, (UNDEF: 1)
     384:	00000845 	andeq	r0, r0, r5, asr #16
     388:	047d0210 	ldrbteq	r0, [sp], #-528	; 0xfffffdf0
     38c:	000005ff 	strdeq	r0, [r0], -pc	; <UNPREDICTABLE>
     390:	0845a101 	stmdaeq	r5, {r0, r8, sp, pc}^
     394:	11000000 	mrsne	r0, (UNDEF: 0)
     398:	00020000 	andeq	r0, r2, r0
     39c:	00000178 	andeq	r0, r0, r8, ror r1
     3a0:	02c45b01 	sbceq	r5, r4, #1024	; 0x400
     3a4:	d7010000 	strle	r0, [r1, -r0]
     3a8:	0200fc12 	andeq	pc, r0, #4608	; 0x1200
     3ac:	00003400 	andeq	r3, r0, r0, lsl #8
     3b0:	7d021300 	stcvc	3, cr1, [r2, #-0]
     3b4:	0003f804 	andeq	pc, r3, r4, lsl #16
     3b8:	37e40100 	strbcc	r0, [r4, r0, lsl #2]!
     3bc:	00000000 	andeq	r0, r0, r0
     3c0:	01780e00 	cmneq	r8, r0, lsl #28
     3c4:	02000002 	andeq	r0, r0, #2
     3c8:	5b010000 	blpl	403d0 <readKey+0x50>
     3cc:	000003fa 	strdeq	r0, [r0], -sl
     3d0:	020ff401 	andeq	pc, pc, #16777216	; 0x1000000
     3d4:	04000c7d 	streq	r0, [r0], #-3197	; 0xfffff383
     3d8:	f4010000 	vst4.8	{d0-d3}, [r1], r0
     3dc:	00000037 	andeq	r0, r0, r7, lsr r0
     3e0:	087d0213 	ldmdaeq	sp!, {r0, r1, r4, r9}^
     3e4:	0000040a 	andeq	r0, r0, sl, lsl #8
     3e8:	0071f801 	rsbseq	pc, r1, r1, lsl #16
     3ec:	02140000 	andseq	r0, r4, #0
     3f0:	0410047d 	ldreq	r0, [r0], #-1149	; 0xfffffb83
     3f4:	0a010000 	beq	403fc <readKey+0x7c>
     3f8:	00014601 	andeq	r4, r1, r1, lsl #12
     3fc:	00001500 	andeq	r1, r0, r0, lsl #10
     400:	02140000 	andseq	r0, r4, #0
     404:	0418007d 	ldreq	r0, [r8], #-125	; 0xffffff83
     408:	0c010000 	stceq	0, cr0, [r1], {-0}
     40c:	00007101 	andeq	r7, r0, r1, lsl #2
     410:	16000000 	strne	r0, [r0], -r0
     414:	00020378 	andeq	r0, r2, r8, ror r3
     418:	000001ec 	andeq	r0, r0, ip, ror #3
     41c:	02d25b01 	sbcseq	r5, r2, #1024	; 0x400
     420:	6e010000 	cdpvs	0, 0, cr0, cr1, cr0, {0}
     424:	7d031401 	cfstrsvc	mvf1, [r3, #-4]
     428:	041a00d8 	ldreq	r0, [sl], #-216	; 0xffffff28
     42c:	70010000 	andvc	r0, r1, r0
     430:	00023b01 	andeq	r3, r2, r1, lsl #22
     434:	7d021400 	cfstrsvc	mvf1, [r2, #-0]
     438:	0007a008 	andeq	sl, r7, r8
     43c:	01710100 	cmneq	r1, r0, lsl #2
     440:	0000023b 	andeq	r0, r0, fp, lsr r2
     444:	047d0214 	ldrbteq	r0, [sp], #-532	; 0xfffffdec
     448:	0000041d 	andeq	r0, r0, sp, lsl r4
     44c:	37017201 	strcc	r7, [r1, -r1, lsl #4]
     450:	14000000 	strne	r0, [r0], #-0
     454:	23007d02 	movwcs	r7, #3330	; 0xd02
     458:	01000004 	tsteq	r0, r4
     45c:	00370173 	eorseq	r0, r7, r3, ror r1
     460:	11000000 	mrsne	r0, (UNDEF: 0)
     464:	000401d0 	ldrdeq	r0, [r4], -r0	; <UNPREDICTABLE>
     468:	0000013c 	andeq	r0, r0, ip, lsr r1
     46c:	02df5b01 	sbcseq	r5, pc, #1024	; 0x400
     470:	b1010000 	mrslt	r0, (UNDEF: 1)
     474:	0c7d0213 	lfmeq	f0, 2, [sp], #-76	; 0xffffffb4
     478:	00000429 	andeq	r0, r0, r9, lsr #8
     47c:	0037b301 	eorseq	fp, r7, r1, lsl #6
     480:	02130000 	andseq	r0, r3, #0
     484:	043a087d 	ldrteq	r0, [sl], #-2173	; 0xfffff783
     488:	bb010000 	bllt	40490 <readKey+0x110>
     48c:	00000037 	andeq	r0, r0, r7, lsr r0
     490:	04027c12 	streq	r7, [r2], #-3090	; 0xfffff3ee
     494:	00005400 	andeq	r5, r0, r0, lsl #8
     498:	7d021300 	stcvc	3, cr1, [r2, #-0]
     49c:	00044a04 	andeq	r4, r4, r4, lsl #20
     4a0:	46be0100 	ldrtmi	r0, [lr], r0, lsl #2
     4a4:	00000001 	andeq	r0, r0, r1
     4a8:	030c1100 	movweq	r1, #49408	; 0xc100
     4ac:	00740004 	rsbseq	r0, r4, r4
     4b0:	5b010000 	blpl	404b8 <get_key+0x10>
     4b4:	000002ed 	andeq	r0, r0, sp, ror #5
     4b8:	1815c801 	ldmdane	r5, {r0, fp, lr, pc}
     4bc:	13000000 	movwne	r0, #0
     4c0:	56077d02 	strpl	r7, [r7], -r2, lsl #26
     4c4:	01000004 	tsteq	r0, r4
     4c8:	000247cc 	andeq	r4, r2, ip, asr #15
     4cc:	16000000 	strne	r0, [r0], -r0
     4d0:	00040380 	andeq	r0, r4, r0, lsl #7
     4d4:	00000128 	andeq	r0, r0, r8, lsr #2
     4d8:	02f85b01 	rscseq	r5, r8, #1024	; 0x400
     4dc:	16010000 	strne	r0, [r1], -r0
     4e0:	7d021401 	cfstrsvc	mvf1, [r2, #-4]
     4e4:	00045d0c 	andeq	r5, r4, ip, lsl #26
     4e8:	011f0100 	tsteq	pc, r0, lsl #2
     4ec:	00000071 	andeq	r0, r0, r1, ror r0
     4f0:	087d0214 	ldmdaeq	sp!, {r2, r4, r9}^
     4f4:	00000469 	andeq	r0, r0, r9, ror #8
     4f8:	71012001 	tstvc	r1, r1
     4fc:	14000000 	strne	r0, [r0], #-0
     500:	7c077d02 	stcvc	13, cr7, [r7], {2}
     504:	01000004 	tsteq	r0, r4
     508:	025f0122 	subseq	r0, pc, #-2147483640	; 0x80000008
     50c:	17000000 	strne	r0, [r0, -r0]
     510:	000404a8 	andeq	r0, r4, r8, lsr #9
     514:	00000080 	andeq	r0, r0, r0, lsl #1
     518:	03005d01 	movweq	r5, #3329	; 0xd01
     51c:	8a010000 	bhi	40524 <get_key+0x7c>
     520:	00003701 	andeq	r3, r0, r1, lsl #14
     524:	91021800 	tstls	r2, r0, lsl #16
     528:	00048b04 	andeq	r8, r4, r4, lsl #22
     52c:	018a0100 	orreq	r0, sl, r0, lsl #2
     530:	000002d6 	ldrdeq	r0, [r0], -r6
     534:	00910214 	addseq	r0, r1, r4, lsl r2
     538:	00000799 	muleq	r0, r9, r7
     53c:	37018b01 	strcc	r8, [r1, -r1, lsl #22]
     540:	00000000 	andeq	r0, r0, r0
     544:	04052819 	streq	r2, [r5], #-2073	; 0xfffff7e7
     548:	0001f800 	andeq	pc, r1, r0, lsl #16
     54c:	085b0100 	ldmdaeq	fp, {r8}^
     550:	01000003 	tsteq	r0, r3
     554:	02180135 	andseq	r0, r8, #1073741837	; 0x4000000d
     558:	0304047d 	movweq	r0, #17533	; 0x447d
     55c:	35010000 	strcc	r0, [r1, #-0]
     560:	0002d601 	andeq	sp, r2, r1, lsl #12
     564:	20190000 	andscs	r0, r9, r0
     568:	28000407 	stmdacs	r0, {r0, r1, r2, sl}
     56c:	01000000 	mrseq	r0, (UNDEF: 0)
     570:	0003145b 	andeq	r1, r3, fp, asr r4
     574:	01a90100 			; <UNDEFINED> instruction: 0x01a90100
     578:	047d0218 	ldrbteq	r0, [sp], #-536	; 0xfffffde8
     57c:	00000418 	andeq	r0, r0, r8, lsl r4
     580:	3701a901 	strcc	sl, [r1, -r1, lsl #18]
     584:	00000000 	andeq	r0, r0, r0
     588:	04074817 	streq	r4, [r7], #-2071	; 0xfffff7e9
     58c:	0000c800 	andeq	ip, r0, r0, lsl #16
     590:	235b0100 	cmpcs	fp, #0, 2
     594:	01000003 	tsteq	r0, r3
     598:	003701b0 	ldrhteq	r0, [r7], -r0
     59c:	02180000 	andseq	r0, r8, #0
     5a0:	04917891 	ldreq	r7, [r1], #2193	; 0x891
     5a4:	b0010000 	andlt	r0, r1, r0
     5a8:	00003701 	andeq	r3, r0, r1, lsl #14
     5ac:	7d021800 	stcvc	8, cr1, [r2, #-0]
     5b0:	0004960c 	andeq	r9, r4, ip, lsl #12
     5b4:	01b00100 	lslseq	r0, r0, #2
     5b8:	000005ea 	andeq	r0, r0, sl, ror #11
     5bc:	087d0214 	ldmdaeq	sp!, {r2, r4, r9}^
     5c0:	0000049b 	muleq	r0, fp, r4
     5c4:	f401b701 	vst1.8	{d11}, [r1], r1
     5c8:	14000005 	strne	r0, [r0], #-5
     5cc:	a2047d02 	andge	r7, r4, #2, 26	; 0x80
     5d0:	01000004 	tsteq	r0, r4
     5d4:	060001bb 			; <UNDEFINED> instruction: 0x060001bb
     5d8:	02140000 	andseq	r0, r4, #0
     5dc:	03ec007d 	mvneq	r0, #125	; 0x7d
     5e0:	bf010000 	svclt	0x00010000
     5e4:	00003701 	andeq	r3, r0, r1, lsl #14
     5e8:	ef1a0000 	svc	0x001a0000
     5ec:	1a000005 	bne	608 <_init-0x10518>
     5f0:	00000247 	andeq	r0, r0, r7, asr #4
     5f4:	0005f91a 	andeq	pc, r5, sl, lsl r9	; <UNPREDICTABLE>
     5f8:	371c1b00 	ldrcc	r1, [ip, -r0, lsl #22]
     5fc:	00000000 	andeq	r0, r0, r0
     600:	0006051a 	andeq	r0, r6, sl, lsl r5
     604:	161c1b00 	ldrne	r1, [ip], -r0, lsl #22
     608:	1c000006 	stcne	0, cr0, [r0], {6}
     60c:	000002d6 	ldrdeq	r0, [r0], -r6
     610:	0002d61c 	andeq	sp, r2, ip, lsl r6
     614:	b61a0000 	ldrlt	r0, [sl], -r0
     618:	00000002 	andeq	r0, r0, r2
     61c:	00000264 	andeq	r0, r0, r4, ror #4
     620:	00000005 	andeq	r0, r0, r5
     624:	01040000 	mrseq	r0, (UNDEF: 4)
     628:	00000000 	andeq	r0, r0, r0
     62c:	029c000c 	addseq	r0, ip, #12
     630:	05d70000 	ldrbeq	r0, [r7]
     634:	003b0000 	eorseq	r0, fp, r0
     638:	00000000 	andeq	r0, r0, r0
     63c:	00500000 	subseq	r0, r0, r0
     640:	0e1d0000 	cdpeq	0, 1, cr0, cr13, cr0, {0}
     644:	00040810 	andeq	r0, r4, r0, lsl r8
     648:	0000003c 	andeq	r0, r0, ip, lsr r0
     64c:	03285b01 			; <UNDEFINED> instruction: 0x03285b01
     650:	08010000 	stmdaeq	r1, {}	; <UNPREDICTABLE>
     654:	047d021e 	ldrbteq	r0, [sp], #-542	; 0xfffffde2
     658:	000004b0 			; <UNDEFINED> instruction: 0x000004b0
     65c:	00370801 	eorseq	r0, r7, r1, lsl #16
     660:	021e0000 	andseq	r0, lr, #0
     664:	07a4007d 			; <UNDEFINED> instruction: 0x07a4007d
     668:	08010000 	stmdaeq	r1, {}	; <UNPREDICTABLE>
     66c:	00000037 	andeq	r0, r0, r7, lsr r0
     670:	084c1f00 	stmdaeq	ip, {r8, r9, sl, fp, ip}^
     674:	00440004 	subeq	r0, r4, r4
     678:	5b010000 	blpl	40680 <doKeyAction+0x158>
     67c:	00000330 	andeq	r0, r0, r0, lsr r3
     680:	00370d01 	eorseq	r0, r7, r1, lsl #26
     684:	021e0000 	andseq	r0, lr, #0
     688:	04b0047d 	ldrteq	r0, [r0], #1149	; 0x47d
     68c:	0d010000 	stceq	0, cr0, [r1, #-0]
     690:	00000037 	andeq	r0, r0, r7, lsr r0
     694:	007d0210 	rsbseq	r0, sp, r0, lsl r2
     698:	000000fe 	strdeq	r0, [r0], -lr
     69c:	00370e01 	eorseq	r0, r7, r1, lsl #28
     6a0:	0e000000 	cdpeq	0, 0, cr0, cr0, cr0, {0}
     6a4:	00020564 	andeq	r0, r2, r4, ror #10
     6a8:	00000024 	andeq	r0, r0, r4, lsr #32
     6ac:	033c5b01 	teqeq	ip, #1024	; 0x400
     6b0:	14010000 	strne	r0, [r1], #-0
     6b4:	047d021e 	ldrbteq	r0, [sp], #-542	; 0xfffffde2
     6b8:	000004b0 			; <UNDEFINED> instruction: 0x000004b0
     6bc:	00371401 	eorseq	r1, r7, r1, lsl #8
     6c0:	021e0000 	andseq	r0, lr, #0
     6c4:	0d6c007d 	stcleq	0, cr0, [ip, #-500]!	; 0xfffffe0c
     6c8:	14010000 	strne	r0, [r1], #-0
     6cc:	00000037 	andeq	r0, r0, r7, lsr r0
     6d0:	08900e00 	ldmeq	r0, {r9, sl, fp}
     6d4:	00300004 	eorseq	r0, r0, r4
     6d8:	5b010000 	blpl	406e0 <doKeyAction+0x1b8>
     6dc:	00000349 	andeq	r0, r0, r9, asr #6
     6e0:	021e1901 	andseq	r1, lr, #16384	; 0x4000
     6e4:	04b4047d 	ldrteq	r0, [r4], #1149	; 0x47d
     6e8:	19010000 	stmdbne	r1, {}	; <UNPREDICTABLE>
     6ec:	00000037 	andeq	r0, r0, r7, lsr r0
     6f0:	08c02000 	stmiaeq	r0, {sp}^
     6f4:	00500004 	subseq	r0, r0, r4
     6f8:	5b010000 	blpl	40700 <doKeyAction+0x1d8>
     6fc:	00000356 	andeq	r0, r0, r6, asr r3
     700:	00371e01 	eorseq	r1, r7, r1, lsl #28
     704:	02100000 	andseq	r0, r0, #0
     708:	02a7037d 	adceq	r0, r7, #-201326591	; 0xf4000001
     70c:	1f010000 	svcne	0x00010000
     710:	00000247 	andeq	r0, r0, r7, asr #4
     714:	09102000 	ldmdbeq	r0, {sp}
     718:	00200004 	eoreq	r0, r0, r4
     71c:	5b010000 	blpl	40724 <forward_target+0x4>
     720:	00000367 	andeq	r0, r0, r7, ror #6
     724:	00372b01 	eorseq	r2, r7, r1, lsl #22
     728:	02100000 	andseq	r0, r0, #0
     72c:	02a77f91 	adceq	r7, r7, #580	; 0x244
     730:	2c010000 	stccs	0, cr0, [r1], {-0}
     734:	00000247 	andeq	r0, r0, r7, asr #4
     738:	05881f00 	streq	r1, [r8, #3840]	; 0xf00
     73c:	00480002 	subeq	r0, r8, r2
     740:	5b010000 	blpl	40748 <main>
     744:	00000373 	andeq	r0, r0, r3, ror r3
     748:	00373301 	eorseq	r3, r7, r1, lsl #6
     74c:	021e0000 	andseq	r0, lr, #0
     750:	04b9047d 	ldrteq	r0, [r9], #1149	; 0x47d
     754:	33010000 	movwcc	r0, #4096	; 0x1000
     758:	000005ef 	andeq	r0, r0, pc, ror #11
     75c:	007d021e 	rsbseq	r0, sp, lr, lsl r2
     760:	000008d0 	ldrdeq	r0, [r0], -r0	; <UNPREDICTABLE>
     764:	00373301 	eorseq	r3, r7, r1, lsl #6
     768:	1f000000 	svcne	0x00000000
     76c:	00040930 	andeq	r0, r4, r0, lsr r9
     770:	0000003c 	andeq	r0, r0, ip, lsr r0
     774:	03805b01 	orreq	r5, r0, #1024	; 0x400
     778:	38010000 	stmdacc	r1, {}	; <UNPREDICTABLE>
     77c:	00000037 	andeq	r0, r0, r7, lsr r0
     780:	047d021e 	ldrbteq	r0, [sp], #-542	; 0xfffffde2
     784:	000004b0 			; <UNDEFINED> instruction: 0x000004b0
     788:	00373801 	eorseq	r3, r7, r1, lsl #16
     78c:	02100000 	andseq	r0, r0, #0
     790:	00fe007d 	rscseq	r0, lr, sp, ror r0
     794:	39010000 	stmdbcc	r1, {}	; <UNPREDICTABLE>
     798:	00000037 	andeq	r0, r0, r7, lsr r0
     79c:	096c2100 	stmdbeq	ip!, {r8, sp}^
     7a0:	00400004 	subeq	r0, r0, r4
     7a4:	5b010000 	blpl	407ac <main+0x64>
     7a8:	0000038b 	andeq	r0, r0, fp, lsl #7
     7ac:	02293f01 	eoreq	r3, r9, #1, 30
     7b0:	02130000 	andseq	r0, r3, #0
     7b4:	03f2007d 	mvnseq	r0, #125	; 0x7d
     7b8:	40010000 	andmi	r0, r1, r0
     7bc:	00000230 	andeq	r0, r0, r0, lsr r2
     7c0:	09ac2100 	stmibeq	ip!, {r8, sp}
     7c4:	00300004 	eorseq	r0, r0, r4
     7c8:	5b010000 	blpl	407d0 <main+0x88>
     7cc:	00000392 	muleq	r0, r2, r3
     7d0:	02294801 	eoreq	r4, r9, #65536	; 0x10000
     7d4:	02130000 	andseq	r0, r3, #0
     7d8:	03f2007d 	mvnseq	r0, #125	; 0x7d
     7dc:	49010000 	stmdbmi	r1, {}	; <UNPREDICTABLE>
     7e0:	00000230 	andeq	r0, r0, r0, lsr r2
     7e4:	05d00e00 	ldrbeq	r0, [r0, #3584]	; 0xe00
     7e8:	002c0002 	eoreq	r0, ip, r2
     7ec:	5b010000 	blpl	407f4 <main+0xac>
     7f0:	00000398 	muleq	r0, r8, r3
     7f4:	021e5101 	andseq	r5, lr, #1073741824	; 0x40000000
     7f8:	0392047d 	orrseq	r0, r2, #2097152000	; 0x7d000000
     7fc:	51010000 	mrspl	r0, (UNDEF: 1)
     800:	00000146 	andeq	r0, r0, r6, asr #2
     804:	05fc1f00 	ldrbeq	r1, [ip, #3840]!	; 0xf00
     808:	00300002 	eorseq	r0, r0, r2
     80c:	5b010000 	blpl	40814 <pinMode+0x4>
     810:	000003aa 	andeq	r0, r0, sl, lsr #7
     814:	00375501 	eorseq	r5, r7, r1, lsl #10
     818:	021e0000 	andseq	r0, lr, #0
     81c:	048b7c91 	streq	r7, [fp], #3217	; 0xc91
     820:	55010000 	strpl	r0, [r1, #-0]
     824:	000005ef 	andeq	r0, r0, pc, ror #11
     828:	087d021e 	ldmdaeq	sp!, {r1, r2, r3, r4, r9}^
     82c:	000008d0 	ldrdeq	r0, [r0], -r0	; <UNPREDICTABLE>
     830:	00375501 	eorseq	r5, r7, r1, lsl #10
     834:	02100000 	andseq	r0, r0, #0
     838:	00fe047d 	rscseq	r0, lr, sp, ror r4
     83c:	56010000 	strpl	r0, [r1], -r0
     840:	00000037 	andeq	r0, r0, r7, lsr r0
     844:	057e0300 	ldrbeq	r0, [lr, #-768]!	; 0xfffffd00
     848:	04070000 	streq	r0, [r7], #-0
     84c:	0004e609 	andeq	lr, r4, r9, lsl #12
     850:	08030800 	stmdaeq	r3, {fp}
     854:	0004c00a 	andeq	ip, r4, sl
     858:	00025100 	andeq	r5, r2, r0, lsl #2
     85c:	000a0300 	andeq	r0, sl, r0, lsl #6
     860:	0004d00a 	andeq	sp, r4, sl
     864:	00025c00 	andeq	r5, r2, r0, lsl #24
     868:	040b0300 	streq	r0, [fp], #-768	; 0xfffffd00
     86c:	00712200 	rsbseq	r2, r1, r0, lsl #4
     870:	04c70000 	strbeq	r0, [r7], #0
     874:	a0020000 	andge	r0, r2, r0
     878:	00007122 	andeq	r7, r0, r2, lsr #2
     87c:	0004d800 	andeq	sp, r4, r0, lsl #16
     880:	00a20200 	adceq	r0, r2, r0, lsl #4
     884:	00000045 	andeq	r0, r0, r5, asr #32
     888:	00000005 	andeq	r0, r0, r5
     88c:	23040000 	movwcs	r0, #16384	; 0x4000
     890:	00000000 	andeq	r0, r0, r0
     894:	02a3000c 	adceq	r0, r3, #12
     898:	07410000 	strbeq	r0, [r1, -r0]
     89c:	003b0000 	eorseq	r0, fp, r0
     8a0:	062c0000 	strteq	r0, [ip], -r0
     8a4:	006c0002 	rsbeq	r0, ip, r2
     8a8:	2c240000 	stccs	0, cr0, [r4], #-0
     8ac:	44000206 	strmi	r0, [r0], #-518	; 0xfffffdfa
     8b0:	01000000 	mrseq	r0, (UNDEF: 0)
     8b4:	0003b15b 	andeq	fp, r3, fp, asr r1
     8b8:	24070100 	strcs	r0, [r7], #-256	; 0xffffff00
     8bc:	00020670 	andeq	r0, r2, r0, ror r6
     8c0:	00000028 	andeq	r0, r0, r8, lsr #32
     8c4:	03b85b01 			; <UNDEFINED> instruction: 0x03b85b01
     8c8:	0d010000 	stceq	0, cr0, [r1, #-0]
     8cc:	00011c00 	andeq	r1, r1, r0, lsl #24
     8d0:	00000500 	andeq	r0, r0, r0, lsl #10
     8d4:	04000000 	streq	r0, [r0], #-0
     8d8:	00000001 	andeq	r0, r0, r1
     8dc:	a9000c00 	stmdbge	r0, {sl, fp}
     8e0:	92000002 	andls	r0, r0, #2
     8e4:	3b000007 	blcc	908 <_init-0x10218>
     8e8:	00000000 	andeq	r0, r0, r0
     8ec:	88000000 	stmdahi	r0, {}	; <UNPREDICTABLE>
     8f0:	0e000000 	cdpeq	0, 0, cr0, cr0, cr0, {0}
     8f4:	000409dc 	ldrdeq	r0, [r4], -ip
     8f8:	00000058 	andeq	r0, r0, r8, asr r0
     8fc:	03c05b01 	biceq	r5, r0, #1024	; 0x400
     900:	06010000 	streq	r0, [r1], -r0
     904:	0c7d020f 	lfmeq	f0, 2, [sp], #-60	; 0xffffffc4
     908:	0000020f 	andeq	r0, r0, pc, lsl #4
     90c:	00fa0601 	rscseq	r0, sl, r1, lsl #12
     910:	021e0000 	andseq	r0, lr, #0
     914:	04ee087d 	strbteq	r0, [lr], #2173	; 0x87d
     918:	06010000 	streq	r0, [r1], -r0
     91c:	000002d6 	ldrdeq	r0, [r0], -r6
     920:	047d021e 	ldrbteq	r0, [sp], #-542	; 0xfffffde2
     924:	000004f3 	strdeq	r0, [r0], -r3
     928:	02d60601 	sbcseq	r0, r6, #1048576	; 0x100000
     92c:	0e000000 	cdpeq	0, 0, cr0, cr0, cr0, {0}
     930:	00020698 	muleq	r2, r8, r6
     934:	00000038 	andeq	r0, r0, r8, lsr r0
     938:	03ca5b01 	biceq	r5, sl, #1024	; 0x400
     93c:	0e010000 	cdpeq	0, 0, cr0, cr1, cr0, {0}
     940:	047d020f 	ldrbteq	r0, [sp], #-527	; 0xfffffdf1
     944:	0000020f 	andeq	r0, r0, pc, lsl #4
     948:	00fa0e01 	rscseq	r0, sl, r1, lsl #28
     94c:	0e000000 	cdpeq	0, 0, cr0, cr0, cr0, {0}
     950:	000206d0 	ldrdeq	r0, [r2], -r0	; <UNPREDICTABLE>
     954:	00000050 	andeq	r0, r0, r0, asr r0
     958:	03d45b01 	bicseq	r5, r4, #1024	; 0x400
     95c:	13010000 	movwne	r0, #4096	; 0x1000
     960:	7c91020f 	lfmvc	f0, 4, [r1], {15}
     964:	0000020f 	andeq	r0, r0, pc, lsl #4
     968:	00fa1301 	rscseq	r1, sl, r1, lsl #6
     96c:	021e0000 	andseq	r0, lr, #0
     970:	04b9087d 	ldrteq	r0, [r9], #2173	; 0x87d
     974:	13010000 	movwne	r0, #4096	; 0x1000
     978:	000005ef 	andeq	r0, r0, pc, ror #11
     97c:	047d021e 	ldrbteq	r0, [sp], #-542	; 0xfffffde2
     980:	000008d0 	ldrdeq	r0, [r0], -r0	; <UNPREDICTABLE>
     984:	00371301 	eorseq	r1, r7, r1, lsl #6
     988:	0e000000 	cdpeq	0, 0, cr0, cr0, cr0, {0}
     98c:	00020720 	andeq	r0, r2, r0, lsr #14
     990:	0000004c 	andeq	r0, r0, ip, asr #32
     994:	03de5b01 	bicseq	r5, lr, #1024	; 0x400
     998:	18010000 	stmdane	r1, {}	; <UNPREDICTABLE>
     99c:	7c91020f 	lfmvc	f0, 4, [r1], {15}
     9a0:	0000020f 	andeq	r0, r0, pc, lsl #4
     9a4:	00fa1801 	rscseq	r1, sl, r1, lsl #16
     9a8:	021e0000 	andseq	r0, lr, #0
     9ac:	0161087d 	smceq	4237	; 0x108d
     9b0:	18010000 	stmdane	r1, {}	; <UNPREDICTABLE>
     9b4:	00000037 	andeq	r0, r0, r7, lsr r0
     9b8:	047d021e 	ldrbteq	r0, [sp], #-542	; 0xfffffde2
     9bc:	00000416 	andeq	r0, r0, r6, lsl r4
     9c0:	00371801 	eorseq	r1, r7, r1, lsl #16
     9c4:	1a000000 	bne	9cc <_init-0x10154>
     9c8:	000000ff 	strdeq	r0, [r0], -pc	; <UNPREDICTABLE>
     9cc:	00010a08 	andeq	r0, r1, r8, lsl #20
     9d0:	00022700 	andeq	r2, r2, r0, lsl #14
     9d4:	090a0200 	stmdbeq	sl, {r9}
     9d8:	00000213 	andeq	r0, r0, r3, lsl r2
     9dc:	25080204 	strcs	r0, [r8, #-516]	; 0xfffffdfc
     9e0:	00001255 	andeq	r1, r0, r5, asr r2
     9e4:	000002d6 	ldrdeq	r0, [r0], -r6
     9e8:	00000902 	andeq	r0, r0, r2, lsl #18
     9ec:	000a6f00 	andeq	r6, sl, r0, lsl #30
     9f0:	12000400 	andne	r0, r0, #0, 8
     9f4:	04000002 	streq	r0, [r0], #-2
     9f8:	000a3d01 	andeq	r3, sl, r1, lsl #26
     9fc:	09b00c00 	ldmibeq	r0!, {sl, fp}
     a00:	06f60000 	ldrbteq	r0, [r6], r0
     a04:	0adc0000 	beq	ff700a0c <__bss_end__+0xf5e12408>
     a08:	31e60004 	mvncc	r0, r4
     a0c:	083b0000 	ldmdaeq	fp!, {}	; <UNPREDICTABLE>
     a10:	01020000 	mrseq	r0, (UNDEF: 2)
     a14:	00087006 	andeq	r7, r8, r6
     a18:	05020200 	streq	r0, [r2, #-512]	; 0xfffffe00
     a1c:	0000087c 	andeq	r0, r0, ip, ror r8
     a20:	69050403 	stmdbvs	r5, {r0, r1, sl}
     a24:	0200746e 	andeq	r7, r0, #1845493760	; 0x6e000000
     a28:	05b90508 	ldreq	r0, [r9, #1288]!	; 0x508
     a2c:	be040000 	cdplt	0, 0, cr0, cr4, cr0, {0}
     a30:	03000009 	movweq	r0, #9
     a34:	00005130 	andeq	r5, r0, r0, lsr r1
     a38:	00410500 	subeq	r0, r1, r0, lsl #10
     a3c:	01020000 	mrseq	r0, (UNDEF: 2)
     a40:	00086e08 	andeq	r6, r8, r8, lsl #28
     a44:	00510500 	subseq	r0, r1, r0, lsl #10
     a48:	67040000 	strvs	r0, [r4, -r0]
     a4c:	03000006 	movweq	r0, #6
     a50:	00006831 	andeq	r6, r0, r1, lsr r8
     a54:	07020200 	streq	r0, [r2, -r0, lsl #4]
     a58:	00000753 	andeq	r0, r0, r3, asr r7
     a5c:	0008e904 	andeq	lr, r8, r4, lsl #18
     a60:	7f330300 	svcvc	0x00330300
     a64:	05000000 	streq	r0, [r0, #-0]
     a68:	0000006f 	andeq	r0, r0, pc, rrx
     a6c:	83070402 	movwhi	r0, #29698	; 0x7402
     a70:	05000005 	streq	r0, [r0, #-5]
     a74:	0000007f 	andeq	r0, r0, pc, ror r0
     a78:	79070802 	stmdbvc	r7, {r1, fp}
     a7c:	04000005 	streq	r0, [r0], #-5
     a80:	00000531 	andeq	r0, r0, r1, lsr r5
     a84:	007fd804 	rsbseq	sp, pc, r4, lsl #16
     a88:	04020000 	streq	r0, [r2], #-0
     a8c:	00010207 	andeq	r0, r1, r7, lsl #4
     a90:	b6040600 	strlt	r0, [r4], -r0, lsl #12
     a94:	05000000 	streq	r0, [r0, #-0]
     a98:	000000a4 	andeq	r0, r0, r4, lsr #1
     a9c:	77080102 	strvc	r0, [r8, -r2, lsl #2]
     aa0:	05000008 	streq	r0, [r0, #-8]
     aa4:	000000af 	andeq	r0, r0, pc, lsr #1
     aa8:	7e070402 	cdpvc	4, 0, cr0, cr7, cr2, {0}
     aac:	04000005 	streq	r0, [r0], #-5
     ab0:	00000603 	andeq	r0, r0, r3, lsl #12
     ab4:	003a3705 	eorseq	r3, sl, r5, lsl #14
     ab8:	f8040000 			; <UNDEFINED> instruction: 0xf8040000
     abc:	05000004 	streq	r0, [r0, #-4]
     ac0:	0000d883 	andeq	sp, r0, r3, lsl #17
     ac4:	05040200 	streq	r0, [r4, #-512]	; 0xfffffe00
     ac8:	000005be 			; <UNDEFINED> instruction: 0x000005be
     acc:	00093d04 	andeq	r3, r9, r4, lsl #26
     ad0:	c2840500 	addgt	r0, r4, #0, 10
     ad4:	07000000 	streq	r0, [r0, -r0]
     ad8:	af040604 	svcge	0x00040604
     adc:	08000000 	stmdaeq	r0, {}	; <UNPREDICTABLE>
     ae0:	00000812 	andeq	r0, r0, r2, lsl r8
     ae4:	6ff10698 	svcvs	0x00f10698
     ae8:	09000002 	stmdbeq	r0, {r1}
     aec:	00000633 	andeq	r0, r0, r3, lsr r6
     af0:	0033f206 	eorseq	pc, r3, r6, lsl #4
     af4:	09000000 	stmdbeq	r0, {}	; <UNPREDICTABLE>
     af8:	00000500 	andeq	r0, r0, r0, lsl #10
     afc:	00ecf706 	rsceq	pc, ip, r6, lsl #14
     b00:	09040000 	stmdbeq	r4, {}	; <UNPREDICTABLE>
     b04:	000005f6 	strdeq	r0, [r0], -r6
     b08:	00ecf806 	rsceq	pc, ip, r6, lsl #16
     b0c:	09080000 	stmdbeq	r8, {}	; <UNPREDICTABLE>
     b10:	00000947 	andeq	r0, r0, r7, asr #18
     b14:	00ecf906 	rsceq	pc, ip, r6, lsl #18
     b18:	090c0000 	stmdbeq	ip, {}	; <UNPREDICTABLE>
     b1c:	00000a29 	andeq	r0, r0, r9, lsr #20
     b20:	00ecfa06 	rsceq	pc, ip, r6, lsl #20
     b24:	09100000 	ldmdbeq	r0, {}	; <UNPREDICTABLE>
     b28:	00000725 	andeq	r0, r0, r5, lsr #14
     b2c:	00ecfb06 	rsceq	pc, ip, r6, lsl #22
     b30:	09140000 	ldmdbeq	r4, {}	; <UNPREDICTABLE>
     b34:	000007e0 	andeq	r0, r0, r0, ror #15
     b38:	00ecfc06 	rsceq	pc, ip, r6, lsl #24
     b3c:	09180000 	ldmdbeq	r8, {}	; <UNPREDICTABLE>
     b40:	0000056c 	andeq	r0, r0, ip, ror #10
     b44:	00ecfd06 	rsceq	pc, ip, r6, lsl #26
     b48:	091c0000 	ldmdbeq	ip, {}	; <UNPREDICTABLE>
     b4c:	00000642 	andeq	r0, r0, r2, asr #12
     b50:	00ecfe06 	rsceq	pc, ip, r6, lsl #28
     b54:	0a200000 	beq	800b5c <ringBuffer+0x7a8e54>
     b58:	00000787 	andeq	r0, r0, r7, lsl #15
     b5c:	ec010006 	stc	0, cr0, [r1], {6}
     b60:	24000000 	strcs	r0, [r0], #-0
     b64:	0009c60a 	andeq	ip, r9, sl, lsl #12
     b68:	01010600 	tsteq	r1, r0, lsl #12
     b6c:	000000ec 	andeq	r0, r0, ip, ror #1
     b70:	09550a28 	ldmdbeq	r5, {r3, r5, r9, fp}^
     b74:	02060000 	andeq	r0, r6, #0
     b78:	0000ec01 	andeq	lr, r0, r1, lsl #24
     b7c:	410a2c00 	tstmi	sl, r0, lsl #24
     b80:	06000008 	streq	r0, [r0], -r8
     b84:	02a70104 	adceq	r0, r7, #4, 2
     b88:	0a300000 	beq	c00b90 <ringBuffer+0xba8e88>
     b8c:	0000050d 	andeq	r0, r0, sp, lsl #10
     b90:	ad010606 	stcge	6, cr0, [r1, #-24]	; 0xffffffe8
     b94:	34000002 	strcc	r0, [r0], #-2
     b98:	0005ee0a 	andeq	lr, r5, sl, lsl #28
     b9c:	01080600 	tsteq	r8, r0, lsl #12
     ba0:	00000033 	andeq	r0, r0, r3, lsr r0
     ba4:	079b0a38 			; <UNDEFINED> instruction: 0x079b0a38
     ba8:	0c060000 	stceq	0, cr0, [r6], {-0}
     bac:	00003301 	andeq	r3, r0, r1, lsl #6
     bb0:	960a3c00 	strls	r3, [sl], -r0, lsl #24
     bb4:	06000006 	streq	r0, [r0], -r6
     bb8:	00cd010e 	sbceq	r0, sp, lr, lsl #2
     bbc:	0a400000 	beq	1000bc4 <ringBuffer+0xfa8ebc>
     bc0:	0000064e 	andeq	r0, r0, lr, asr #12
     bc4:	68011206 	stmdavs	r1, {r1, r2, r9, ip}
     bc8:	44000000 	strmi	r0, [r0], #-0
     bcc:	0008ae0a 	andeq	sl, r8, sl, lsl #28
     bd0:	01130600 	tsteq	r3, r0, lsl #12
     bd4:	00000025 	andeq	r0, r0, r5, lsr #32
     bd8:	05380a46 	ldreq	r0, [r8, #-2630]!	; 0xfffff5ba
     bdc:	14060000 	strne	r0, [r6], #-0
     be0:	0002b301 	andeq	fp, r2, r1, lsl #6
     be4:	950a4700 	strls	r4, [sl, #-1792]	; 0xfffff900
     be8:	06000007 	streq	r0, [r0], -r7
     bec:	02c30118 	sbceq	r0, r3, #24, 2
     bf0:	0a480000 	beq	1200bf8 <ringBuffer+0x11a8ef0>
     bf4:	0000069a 	muleq	r0, sl, r6
     bf8:	df012106 	svcle	0x00012106
     bfc:	50000000 	andpl	r0, r0, r0
     c00:	00096c0a 	andeq	r6, r9, sl, lsl #24
     c04:	01290600 			; <UNDEFINED> instruction: 0x01290600
     c08:	000000ea 	andeq	r0, r0, sl, ror #1
     c0c:	09730a58 	ldmdbeq	r3!, {r3, r4, r6, r9, fp}^
     c10:	2a060000 	bcs	180c18 <ringBuffer+0x128f10>
     c14:	0000ea01 	andeq	lr, r0, r1, lsl #20
     c18:	7a0a5c00 	bvc	297c20 <ringBuffer+0x23ff18>
     c1c:	06000009 	streq	r0, [r0], -r9
     c20:	00ea012b 	rsceq	r0, sl, fp, lsr #2
     c24:	0a600000 	beq	1800c2c <ringBuffer+0x17a8f24>
     c28:	00000981 	andeq	r0, r0, r1, lsl #19
     c2c:	ea012c06 	b	4bc4c <__FRAME_END__+0x4de4>
     c30:	64000000 	strvs	r0, [r0], #-0
     c34:	0009880a 	andeq	r8, r9, sl, lsl #16
     c38:	012e0600 			; <UNDEFINED> instruction: 0x012e0600
     c3c:	00000092 	muleq	r0, r2, r0
     c40:	07a30a68 	streq	r0, [r3, r8, ror #20]!
     c44:	2f060000 	svccs	0x00060000
     c48:	00003301 	andeq	r3, r0, r1, lsl #6
     c4c:	8f0a6c00 	svchi	0x000a6c00
     c50:	06000009 	streq	r0, [r0], -r9
     c54:	02c90131 	sbceq	r0, r9, #1073741836	; 0x4000000c
     c58:	00700000 	rsbseq	r0, r0, r0
     c5c:	0008070b 	andeq	r0, r8, fp, lsl #14
     c60:	08960600 	ldmeq	r6, {r9, sl}
     c64:	000006d4 	ldrdeq	r0, [r0], -r4
     c68:	a79c060c 	ldrge	r0, [ip, ip, lsl #12]
     c6c:	09000002 	stmdbeq	r0, {r1}
     c70:	00000937 	andeq	r0, r0, r7, lsr r9
     c74:	02a79d06 	adceq	r9, r7, #384	; 0x180
     c78:	09000000 	stmdbeq	r0, {}	; <UNPREDICTABLE>
     c7c:	0000074d 	andeq	r0, r0, sp, asr #14
     c80:	02ad9e06 	adceq	r9, sp, #6, 28	; 0x60
     c84:	09040000 	stmdbeq	r4, {}	; <UNPREDICTABLE>
     c88:	00000830 	andeq	r0, r0, r0, lsr r8
     c8c:	0033a206 	eorseq	sl, r3, r6, lsl #4
     c90:	00080000 	andeq	r0, r8, r0
     c94:	02760406 	rsbseq	r0, r6, #100663296	; 0x6000000
     c98:	04060000 	streq	r0, [r6], #-0
     c9c:	000000f2 	strdeq	r0, [r0], -r2
     ca0:	0000af0c 	andeq	sl, r0, ip, lsl #30
     ca4:	0002c300 	andeq	ip, r2, r0, lsl #6
     ca8:	009d0d00 	addseq	r0, sp, r0, lsl #26
     cac:	00000000 	andeq	r0, r0, r0
     cb0:	026f0406 	rsbeq	r0, pc, #100663296	; 0x6000000
     cb4:	af0c0000 	svcge	0x000c0000
     cb8:	d9000000 	stmdble	r0, {}	; <UNPREDICTABLE>
     cbc:	0d000002 	stceq	0, cr0, [r0, #-8]
     cc0:	0000009d 	muleq	r0, sp, r0
     cc4:	170e0027 	strne	r0, [lr, -r7, lsr #32]
     cc8:	0f000007 	svceq	0x00000007
     ccc:	000007b0 			; <UNDEFINED> instruction: 0x000007b0
     cd0:	d9013b06 	stmdble	r1, {r1, r2, r8, r9, fp, ip, sp}
     cd4:	0f000002 	svceq	0x00000002
     cd8:	000008bd 			; <UNDEFINED> instruction: 0x000008bd
     cdc:	d9013c06 	stmdble	r1, {r1, r2, sl, fp, ip, sp}
     ce0:	0f000002 	svceq	0x00000002
     ce4:	0000055c 	andeq	r0, r0, ip, asr r5
     ce8:	d9013d06 	stmdble	r1, {r1, r2, r8, sl, fp, ip, sp}
     cec:	10000002 	andne	r0, r0, r2
     cf0:	000006df 	ldrdeq	r0, [r0], -pc	; <UNPREDICTABLE>
     cf4:	02ada807 	adceq	sl, sp, #458752	; 0x70000
     cf8:	a9100000 	ldmdbge	r0, {}	; <UNPREDICTABLE>
     cfc:	07000007 	streq	r0, [r0, -r7]
     d00:	0002ada9 	andeq	sl, r2, r9, lsr #27
     d04:	09981000 	ldmibeq	r8, {ip}
     d08:	aa070000 	bge	1c0d10 <ringBuffer+0x169008>
     d0c:	000002ad 	andeq	r0, r0, sp, lsr #5
     d10:	00074410 	andeq	r4, r7, r0, lsl r4
     d14:	331a0800 	tstcc	sl, #0, 16
     d18:	0c000000 	stceq	0, cr0, [r0], {-0}
     d1c:	000000aa 	andeq	r0, r0, sl, lsr #1
     d20:	00000339 	andeq	r0, r0, r9, lsr r3
     d24:	2e050011 	mcrcs	0, 0, r0, cr5, cr1, {0}
     d28:	10000003 	andne	r0, r0, r3
     d2c:	00000835 	andeq	r0, r0, r5, lsr r8
     d30:	03391b08 	teqeq	r9, #8, 22	; 0x2000
     d34:	08020000 	stmdaeq	r2, {}	; <UNPREDICTABLE>
     d38:	0007bf04 	andeq	fp, r7, r4, lsl #30
     d3c:	09fa1200 	ldmibeq	sl!, {r9, ip}^
     d40:	7f040000 	svcvc	0x00040000
     d44:	09000000 	stmdbeq	r0, {}	; <UNPREDICTABLE>
     d48:	00037f1f 	andeq	r7, r3, pc, lsl pc
     d4c:	07661300 	strbeq	r1, [r6, -r0, lsl #6]!
     d50:	13400000 	movtne	r0, #0
     d54:	00000733 	andeq	r0, r0, r3, lsr r7
     d58:	06e51320 	strbteq	r1, [r5], r0, lsr #6
     d5c:	13200000 	nopne	{0}	; <UNPREDICTABLE>
     d60:	00000851 	andeq	r0, r0, r1, asr r8
     d64:	09051308 	stmdbeq	r5, {r3, r8, r9, ip}
     d68:	00080000 	andeq	r0, r8, r0
     d6c:	0005dd12 	andeq	sp, r5, r2, lsl sp
     d70:	007f0400 	rsbseq	r0, pc, r0, lsl #8
     d74:	28090000 	stmdacs	r9, {}	; <UNPREDICTABLE>
     d78:	000003ae 	andeq	r0, r0, lr, lsr #7
     d7c:	00088613 	andeq	r8, r8, r3, lsl r6
     d80:	d1138000 	tstle	r3, r0
     d84:	4000000a 	andmi	r0, r0, sl
     d88:	00099f13 	andeq	r9, r9, r3, lsl pc
     d8c:	21134000 	tstcs	r3, r0
     d90:	10000006 	andne	r0, r0, r6
     d94:	0009e413 	andeq	lr, r9, r3, lsl r4
     d98:	08001000 	stmdaeq	r0, {ip}
     d9c:	00000521 	andeq	r0, r0, r1, lsr #10
     da0:	0931097c 	ldmdbeq	r1!, {r2, r3, r4, r5, r6, r8, fp}
     da4:	14000004 	strne	r0, [r0], #-4
     da8:	33090068 	movwcc	r0, #36968	; 0x9068
     dac:	00000409 	andeq	r0, r0, r9, lsl #8
     db0:	00741400 	rsbseq	r1, r4, r0, lsl #8
     db4:	04193409 	ldreq	r3, [r9], #-1033	; 0xfffffbf7
     db8:	14200000 	strtne	r0, [r0], #-0
     dbc:	35090066 	strcc	r0, [r9, #-102]	; 0xffffff9a
     dc0:	00000419 	andeq	r0, r0, r9, lsl r4
     dc4:	75621428 	strbvc	r1, [r2, #-1064]!	; 0xfffffbd8
     dc8:	36090066 	strcc	r0, [r9], -r6, rrx
     dcc:	00000429 	andeq	r0, r0, r9, lsr #8
     dd0:	08cd0930 	stmiaeq	sp, {r4, r5, r8, fp}^
     dd4:	37090000 	strcc	r0, [r9, -r0]
     dd8:	00000092 	muleq	r0, r2, r0
     ddc:	0a0b0970 	beq	2c33a4 <ringBuffer+0x26b69c>
     de0:	38090000 	stmdacc	r9, {}	; <UNPREDICTABLE>
     de4:	00000092 	muleq	r0, r2, r0
     de8:	09620974 	stmdbeq	r2!, {r2, r4, r5, r6, r8, fp}^
     dec:	39090000 	stmdbcc	r9, {}	; <UNPREDICTABLE>
     df0:	00000041 	andeq	r0, r0, r1, asr #32
     df4:	6f0c0078 	svcvs	0x000c0078
     df8:	19000000 	stmdbne	r0, {}	; <UNPREDICTABLE>
     dfc:	0d000004 	stceq	0, cr0, [r0, #-16]
     e00:	0000009d 	muleq	r0, sp, r0
     e04:	6f0c0007 	svcvs	0x000c0007
     e08:	29000000 	stmdbcs	r0, {}	; <UNPREDICTABLE>
     e0c:	0d000004 	stceq	0, cr0, [r0, #-16]
     e10:	0000009d 	muleq	r0, sp, r0
     e14:	410c0001 	tstmi	ip, r1
     e18:	39000000 	stmdbcc	r0, {}	; <UNPREDICTABLE>
     e1c:	0d000004 	stceq	0, cr0, [r0, #-16]
     e20:	0000009d 	muleq	r0, sp, r0
     e24:	d604003f 			; <UNDEFINED> instruction: 0xd604003f
     e28:	09000009 	stmdbeq	r0, {r0, r3}
     e2c:	0003ae3a 	andeq	sl, r3, sl, lsr lr
     e30:	04390500 	ldrteq	r0, [r9], #-1280	; 0xfffffb00
     e34:	390c0000 	stmdbcc	ip, {}	; <UNPREDICTABLE>
     e38:	59000004 	stmdbpl	r0, {r2}
     e3c:	0d000004 	stceq	0, cr0, [r0, #-16]
     e40:	0000009d 	muleq	r0, sp, r0
     e44:	99080000 	stmdbls	r8, {}	; <UNPREDICTABLE>
     e48:	20000008 	andcs	r0, r0, r8
     e4c:	04ea5a09 	strbteq	r5, [sl], #2569	; 0xa09
     e50:	79090000 	stmdbvc	r9, {}	; <UNPREDICTABLE>
     e54:	09000007 	stmdbeq	r0, {r0, r1, r2}
     e58:	0000415a 	andeq	r4, r0, sl, asr r1
     e5c:	a2090000 	andge	r0, r9, #0
     e60:	09000006 	stmdbeq	r0, {r1, r2}
     e64:	0000415a 	andeq	r4, r0, sl, asr r1
     e68:	4a090100 	bmi	241270 <ringBuffer+0x1e9568>
     e6c:	09000008 	stmdbeq	r0, {r3}
     e70:	0000415a 	andeq	r4, r0, sl, asr r1
     e74:	f3090200 	vhsub.u8	d0, d9, d0
     e78:	09000007 	stmdbeq	r0, {r0, r1, r2}
     e7c:	0000415a 	andeq	r4, r0, sl, asr r1
     e80:	70090300 	andvc	r0, r9, r0, lsl #6
     e84:	09000006 	stmdbeq	r0, {r1, r2}
     e88:	00006f5a 	andeq	r6, r0, sl, asr pc
     e8c:	1b090400 	blne	241e94 <ringBuffer+0x1ea18c>
     e90:	09000008 	stmdbeq	r0, {r3}
     e94:	00006f5a 	andeq	r6, r0, sl, asr pc
     e98:	63090800 	movwvs	r0, #38912	; 0x9800
     e9c:	09000008 	stmdbeq	r0, {r3}
     ea0:	00005d5a 	andeq	r5, r0, sl, asr sp
     ea4:	ee090c00 	cdp	12, 0, cr0, cr9, cr0, {0}
     ea8:	09000007 	stmdbeq	r0, {r0, r1, r2}
     eac:	0000415a 	andeq	r4, r0, sl, asr r1
     eb0:	ac090e00 	stcge	14, cr0, [r9], {-0}
     eb4:	09000005 	stmdbeq	r0, {r0, r2}
     eb8:	0000415a 	andeq	r4, r0, sl, asr r1
     ebc:	14090f00 	strne	r0, [r9], #-3840	; 0xfffff100
     ec0:	09000005 	stmdbeq	r0, {r0, r2}
     ec4:	0004ea5a 	andeq	lr, r4, sl, asr sl
     ec8:	27091000 	strcs	r1, [r9, -r0]
     ecc:	09000008 	stmdbeq	r0, {r3}
     ed0:	0004ea5a 	andeq	lr, r4, sl, asr sl
     ed4:	0c001800 	stceq	8, cr1, [r0], {-0}
     ed8:	00000041 	andeq	r0, r0, r1, asr #32
     edc:	000004fa 	strdeq	r0, [r0], -sl
     ee0:	00009d0d 	andeq	r9, r0, sp, lsl #26
     ee4:	04000700 	streq	r0, [r0], #-1792	; 0xfffff900
     ee8:	000007f9 	strdeq	r0, [r0], -r9
     eec:	04596a09 	ldrbeq	r6, [r9], #-2569	; 0xfffff5f7
     ef0:	fa050000 	blx	140ef8 <ringBuffer+0xe91f0>
     ef4:	0c000004 	stceq	0, cr0, [r0], {4}
     ef8:	000004fa 	strdeq	r0, [r0], -sl
     efc:	0000051a 	andeq	r0, r0, sl, lsl r5
     f00:	00009d0d 	andeq	r9, r0, sp, lsl #26
     f04:	0c000000 	stceq	0, cr0, [r0], {-0}
     f08:	0000007a 	andeq	r0, r0, sl, ror r0
     f0c:	0000052a 	andeq	r0, r0, sl, lsr #10
     f10:	00009d0d 	andeq	r9, r0, sp, lsl #26
     f14:	05000700 	streq	r0, [r0, #-1792]	; 0xfffff900
     f18:	0000051a 	andeq	r0, r0, sl, lsl r5
     f1c:	00092c15 	andeq	r2, r9, r5, lsl ip
     f20:	2a170200 	bcs	5c1728 <ringBuffer+0x569a20>
     f24:	05000005 	streq	r0, [r0, #-5]
     f28:	0468bc03 	strbteq	fp, [r8], #-3075	; 0xfffff3fd
     f2c:	004c0c00 	subeq	r0, ip, r0, lsl #24
     f30:	05560000 	ldrbeq	r0, [r6, #-0]
     f34:	9d0d0000 	stcls	0, cr0, [sp, #-0]
     f38:	09000000 	stmdbeq	r0, {}	; <UNPREDICTABLE>
     f3c:	00009d0d 	andeq	r9, r0, sp, lsl #26
     f40:	05000f00 	streq	r0, [r0, #-3840]	; 0xfffff100
     f44:	00000540 	andeq	r0, r0, r0, asr #10
     f48:	00059015 	andeq	r9, r5, r5, lsl r0
     f4c:	561d0200 	ldrpl	r0, [sp], -r0, lsl #4
     f50:	05000005 	streq	r0, [r0, #-5]
     f54:	0468dc03 	strbteq	sp, [r8], #-3075	; 0xfffff3fd
     f58:	05191600 	ldreq	r1, [r9, #-1536]	; 0xfffffa00
     f5c:	09020000 	stmdbeq	r2, {}	; <UNPREDICTABLE>
     f60:	00003301 	andeq	r3, r0, r1, lsl #6
     f64:	043bfc00 	ldrteq	pc, [fp], #-3072	; 0xfffff400	; <UNPREDICTABLE>
     f68:	0000c600 	andeq	ip, r0, r0, lsl #12
     f6c:	f29c0100 	vaddw.s16	q0, q6, d0
     f70:	17000005 	strne	r0, [r0, -r5]
     f74:	0074756f 	rsbseq	r7, r4, pc, ror #10
     f78:	ea010902 	b	43388 <blake2s_compress+0x24d0>
     f7c:	03000000 	movweq	r0, #0
     f80:	187ef491 	ldmdane	lr!, {r0, r4, r7, sl, ip, sp, lr, pc}^
     f84:	00000a0b 	andeq	r0, r0, fp, lsl #20
     f88:	92010902 	andls	r0, r1, #32768	; 0x8000
     f8c:	03000000 	movweq	r0, #0
     f90:	177ef091 			; <UNDEFINED> instruction: 0x177ef091
     f94:	02006e69 	andeq	r6, r0, #1680	; 0x690
     f98:	05f20109 	ldrbeq	r0, [r2, #265]!	; 0x109
     f9c:	91030000 	mrsls	r0, (UNDEF: 3)
     fa0:	ad187eec 	ldcge	14, cr7, [r8, #-944]	; 0xfffffc50
     fa4:	02000006 	andeq	r0, r0, #6
     fa8:	00920109 	addseq	r0, r2, r9, lsl #2
     fac:	91030000 	mrsls	r0, (UNDEF: 3)
     fb0:	6b177ee8 	blvs	5e0b58 <ringBuffer+0x588e50>
     fb4:	02007965 	andeq	r7, r0, #1654784	; 0x194000
     fb8:	05f20109 	ldrbeq	r0, [r2, #265]!	; 0x109
     fbc:	91020000 	mrsls	r0, (UNDEF: 2)
     fc0:	08d41800 	ldmeq	r4, {fp, ip}^
     fc4:	09020000 	stmdbeq	r2, {}	; <UNPREDICTABLE>
     fc8:	00009201 	andeq	r9, r0, r1, lsl #4
     fcc:	04910200 	ldreq	r0, [r1], #512	; 0x200
     fd0:	02005319 	andeq	r5, r0, #1677721600	; 0x64000000
     fd4:	0449010b 	strbeq	r0, [r9], #-267	; 0xfffffef5
     fd8:	91030000 	mrsls	r0, (UNDEF: 3)
     fdc:	06007efc 			; <UNDEFINED> instruction: 0x06007efc
     fe0:	0005f804 	andeq	pc, r5, r4, lsl #16
     fe4:	9e1b1a00 	vnmlsls.f32	s2, s22, s0
     fe8:	02000005 	andeq	r0, r0, #5
     fec:	000033f1 	strdeq	r3, [r0], -r1
     ff0:	043b3200 	ldrteq	r3, [fp], #-512	; 0xfffffe00
     ff4:	0000ca00 	andeq	ip, r0, r0, lsl #20
     ff8:	559c0100 	ldrpl	r0, [ip, #256]	; 0x100
     ffc:	1c000006 	stcne	0, cr0, [r0], {6}
    1000:	f1020053 	cps	#19
    1004:	00000655 	andeq	r0, r0, r5, asr r6
    1008:	1c4c9102 	stfnep	f1, [ip], {2}
    100c:	0074756f 	rsbseq	r7, r4, pc, ror #10
    1010:	00eaf102 	rsceq	pc, sl, r2, lsl #2
    1014:	91020000 	mrsls	r0, (UNDEF: 2)
    1018:	0a0b1d48 	beq	2c8540 <ringBuffer+0x270838>
    101c:	f1020000 	cps	#0
    1020:	00000092 	muleq	r0, r2, r0
    1024:	15449102 	strbne	r9, [r4, #-258]	; 0xfffffefe
    1028:	00001208 	andeq	r1, r0, r8, lsl #4
    102c:	065bf302 	ldrbeq	pc, [fp], -r2, lsl #6	; <UNPREDICTABLE>
    1030:	91020000 	mrsls	r0, (UNDEF: 2)
    1034:	00691e54 	rsbeq	r1, r9, r4, asr lr
    1038:	0092f402 	addseq	pc, r2, r2, lsl #8
    103c:	91020000 	mrsls	r0, (UNDEF: 2)
    1040:	04060074 	streq	r0, [r6], #-116	; 0xffffff8c
    1044:	00000439 	andeq	r0, r0, r9, lsr r4
    1048:	0000410c 	andeq	r4, r0, ip, lsl #2
    104c:	00066b00 	andeq	r6, r6, r0, lsl #22
    1050:	009d0d00 	addseq	r0, sp, r0, lsl #26
    1054:	001f0000 	andseq	r0, pc, r0
    1058:	000a1a1b 	andeq	r1, sl, fp, lsl sl
    105c:	33d60200 	bicscc	r0, r6, #0, 4
    1060:	78000000 	stmdavc	r0, {}	; <UNPREDICTABLE>
    1064:	ba00043a 	blt	2154 <_init-0xe9cc>
    1068:	01000000 	mrseq	r0, (UNDEF: 0)
    106c:	0006e09c 	muleq	r6, ip, r0
    1070:	00531c00 	subseq	r1, r3, r0, lsl #24
    1074:	0655d602 	ldrbeq	sp, [r5], -r2, lsl #12
    1078:	91020000 	mrsls	r0, (UNDEF: 2)
    107c:	69701c64 	ldmdbvs	r0!, {r2, r5, r6, sl, fp, ip}^
    1080:	d602006e 	strle	r0, [r2], -lr, rrx
    1084:	000005f2 	strdeq	r0, [r0], -r2
    1088:	1d609102 	stfnep	f1, [r0, #-8]!
    108c:	000006ad 	andeq	r0, r0, sp, lsr #13
    1090:	0092d602 	addseq	sp, r2, r2, lsl #12
    1094:	91020000 	mrsls	r0, (UNDEF: 2)
    1098:	6e691e5c 	mcrvs	14, 3, r1, cr9, cr12, {2}
    109c:	e0d80200 	sbcs	r0, r8, r0, lsl #4
    10a0:	02000006 	andeq	r0, r0, #6
    10a4:	8e1f7491 	cfcmpshi	r7, mvf15, mvf1
    10a8:	9a00043a 	bls	2198 <_init-0xe988>
    10ac:	15000000 	strne	r0, [r0, #-0]
    10b0:	00000a38 	andeq	r0, r0, r8, lsr sl
    10b4:	0092db02 	addseq	sp, r2, r2, lsl #22
    10b8:	91020000 	mrsls	r0, (UNDEF: 2)
    10bc:	08a91570 	stmiaeq	r9!, {r4, r5, r6, r8, sl, ip}
    10c0:	dc020000 	stcle	0, cr0, [r2], {-0}
    10c4:	00000092 	muleq	r0, r2, r0
    10c8:	006c9102 	rsbeq	r9, ip, r2, lsl #2
    10cc:	58040600 	stmdapl	r4, {r9, sl}
    10d0:	20000000 	andcs	r0, r0, r0
    10d4:	0000091b 	andeq	r0, r0, fp, lsl r9
    10d8:	0eb8ac02 	cdpeq	12, 11, cr10, cr8, cr2, {0}
    10dc:	2bc00004 	blcs	ff0010f4 <__bss_end__+0xf5712af0>
    10e0:	9c010000 	stcls	0, cr0, [r1], {-0}
    10e4:	0000073d 	andeq	r0, r0, sp, lsr r7
    10e8:	0200531c 	andeq	r5, r0, #28, 6	; 0x70000000
    10ec:	000655ac 	andeq	r5, r6, ip, lsr #11
    10f0:	ec910300 	ldc	3, cr0, [r1], {0}
    10f4:	6e691c7e 	mcrvs	12, 3, r1, cr9, cr14, {3}
    10f8:	3dac0200 	sfmcc	f0, 4, [ip]
    10fc:	03000007 	movweq	r0, #7
    1100:	1e7ee891 	mrcne	8, 3, lr, cr14, cr1, {4}
    1104:	ae02006d 	cdpge	0, 0, cr0, cr2, cr13, {3}
    1108:	00000743 	andeq	r0, r0, r3, asr #14
    110c:	7fb49103 	svcvc	0x00b49103
    1110:	0200761e 	andeq	r7, r0, #31457280	; 0x1e00000
    1114:	000743af 	andeq	r4, r7, pc, lsr #7
    1118:	f4910300 			; <UNDEFINED> instruction: 0xf4910300
    111c:	00691e7e 	rsbeq	r1, r9, lr, ror lr
    1120:	0092b002 	addseq	fp, r2, r2
    1124:	91020000 	mrsls	r0, (UNDEF: 2)
    1128:	04060074 	streq	r0, [r6], #-116	; 0xffffff8c
    112c:	0000004c 	andeq	r0, r0, ip, asr #32
    1130:	00006f0c 	andeq	r6, r0, ip, lsl #30
    1134:	00075300 	andeq	r5, r7, r0, lsl #6
    1138:	009d0d00 	addseq	r0, sp, r0, lsl #26
    113c:	000f0000 	andeq	r0, pc, r0
    1140:	0006ba1b 	andeq	fp, r6, fp, lsl sl
    1144:	33730200 	cmncc	r3, #0, 4
    1148:	b6000000 	strlt	r0, [r0], -r0
    114c:	0200040d 	andeq	r0, r0, #218103808	; 0xd000000
    1150:	01000001 	tsteq	r0, r1
    1154:	0007cc9c 	muleq	r7, ip, ip
    1158:	00531c00 	subseq	r1, r3, r0, lsl #24
    115c:	06557302 	ldrbeq	r7, [r5], -r2, lsl #6
    1160:	91030000 	mrsls	r0, (UNDEF: 3)
    1164:	0b1d7f94 	bleq	760fbc <ringBuffer+0x7092b4>
    1168:	0200000a 	andeq	r0, r0, #10
    116c:	00009273 	andeq	r9, r0, r3, ror r2
    1170:	90910300 	addsls	r0, r1, r0, lsl #6
    1174:	656b1c7f 	strbvs	r1, [fp, #-3199]!	; 0xfffff381
    1178:	73020079 	movwvc	r0, #8313	; 0x2079
    117c:	000005f2 	strdeq	r0, [r0], -r2
    1180:	7f8c9103 	svcvc	0x008c9103
    1184:	0008d41d 	andeq	sp, r8, sp, lsl r4
    1188:	92730200 	rsbsls	r0, r3, #0, 4
    118c:	03000000 	movweq	r0, #0
    1190:	1e7f8891 	mrcne	8, 3, r8, cr15, cr1, {4}
    1194:	75020050 	strvc	r0, [r2, #-80]	; 0xffffffb0
    1198:	0000050a 	andeq	r0, r0, sl, lsl #10
    119c:	1f589102 	svcne	0x00589102
    11a0:	00040e78 	andeq	r0, r4, r8, ror lr
    11a4:	00000036 	andeq	r0, r0, r6, lsr r0
    11a8:	00061b15 	andeq	r1, r6, r5, lsl fp
    11ac:	298b0200 	stmibcs	fp, {r9}
    11b0:	03000004 	movweq	r0, #4
    11b4:	007f9891 			; <UNDEFINED> instruction: 0x007f9891
    11b8:	065a1b00 	ldrbeq	r1, [sl], -r0, lsl #22
    11bc:	5d020000 	stcpl	0, cr0, [r2, #-0]
    11c0:	00000033 	andeq	r0, r0, r3, lsr r0
    11c4:	00040d20 	andeq	r0, r4, r0, lsr #26
    11c8:	00000096 	muleq	r0, r6, r0
    11cc:	080c9c01 	stmdaeq	ip, {r0, sl, fp, ip, pc}
    11d0:	531c0000 	tstpl	ip, #0
    11d4:	555d0200 	ldrbpl	r0, [sp, #-512]	; 0xfffffe00
    11d8:	02000006 	andeq	r0, r0, #6
    11dc:	0b1d5491 	bleq	756428 <ringBuffer+0x6fe720>
    11e0:	0200000a 	andeq	r0, r0, #10
    11e4:	0000925d 	andeq	r9, r0, sp, asr r2
    11e8:	50910200 	addspl	r0, r1, r0, lsl #4
    11ec:	0200501e 	andeq	r5, r0, #30
    11f0:	00050a5f 	andeq	r0, r5, pc, asr sl
    11f4:	58910200 	ldmpl	r1, {r9}
    11f8:	08f21b00 	ldmeq	r2!, {r8, r9, fp, ip}^
    11fc:	4c020000 	stcmi	0, cr0, [r2], {-0}
    1200:	00000033 	andeq	r0, r0, r3, lsr r0
    1204:	00040cc4 	andeq	r0, r4, r4, asr #25
    1208:	0000005c 	andeq	r0, r0, ip, asr r0
    120c:	08569c01 	ldmdaeq	r6, {r0, sl, fp, ip, pc}^
    1210:	531c0000 	tstpl	ip, #0
    1214:	554c0200 	strbpl	r0, [ip, #-512]	; 0xfffffe00
    1218:	02000006 	andeq	r0, r0, #6
    121c:	501c6c91 	mulspl	ip, r1, ip
    1220:	564c0200 	strbpl	r0, [ip], -r0, lsl #4
    1224:	02000008 	andeq	r0, r0, #8
    1228:	701e6891 	mulsvc	lr, r1, r8
    122c:	e04e0200 	sub	r0, lr, r0, lsl #4
    1230:	02000006 	andeq	r0, r0, #6
    1234:	691e7091 	ldmdbvs	lr, {r0, r4, r7, ip, sp, lr}
    1238:	924f0200 	subls	r0, pc, #0, 4
    123c:	02000000 	andeq	r0, r0, #0
    1240:	06007491 			; <UNDEFINED> instruction: 0x06007491
    1244:	00050504 	andeq	r0, r5, r4, lsl #10
    1248:	08db2000 	ldmeq	fp, {sp}^
    124c:	43020000 	movwmi	r0, #8192	; 0x2000
    1250:	00040c7e 	andeq	r0, r4, lr, ror ip
    1254:	00000046 	andeq	r0, r0, r6, asr #32
    1258:	088a9c01 	stmeq	sl, {r0, sl, fp, ip, pc}
    125c:	531c0000 	tstpl	ip, #0
    1260:	55430200 	strbpl	r0, [r3, #-512]	; 0xfffffe00
    1264:	02000006 	andeq	r0, r0, #6
    1268:	691e6c91 	ldmdbvs	lr, {r0, r4, r7, sl, fp, sp, lr}
    126c:	92450200 	subls	r0, r5, #0, 4
    1270:	02000000 	andeq	r0, r0, #0
    1274:	21007491 			; <UNDEFINED> instruction: 0x21007491
    1278:	0000067c 	andeq	r0, r0, ip, ror r6
    127c:	0c423d02 	mcrreq	13, 0, r3, r2, cr2
    1280:	003c0004 	eorseq	r0, ip, r4
    1284:	9c010000 	stcls	0, cr0, [r1], {-0}
    1288:	000008ba 			; <UNDEFINED> instruction: 0x000008ba
    128c:	0200531c 	andeq	r5, r0, #28, 6	; 0x70000000
    1290:	0006553d 	andeq	r5, r6, sp, lsr r5
    1294:	74910200 	ldrvc	r0, [r1], #512	; 0x200
    1298:	636e691c 	cmnvs	lr, #28, 18	; 0x70000
    129c:	7a3d0200 	bvc	f41aa4 <ringBuffer+0xee9d9c>
    12a0:	02000000 	andeq	r0, r0, #0
    12a4:	20007091 	mulcs	r0, r1, r0
    12a8:	000005c7 	andeq	r0, r0, r7, asr #11
    12ac:	0c1a3602 	ldceq	6, cr3, [sl], {2}
    12b0:	00280004 	eoreq	r0, r8, r4
    12b4:	9c010000 	stcls	0, cr0, [r1], {-0}
    12b8:	000008dc 	ldrdeq	r0, [r0], -ip
    12bc:	0200531c 	andeq	r5, r0, #28, 6	; 0x70000000
    12c0:	00065536 	andeq	r5, r6, r6, lsr r5
    12c4:	74910200 	ldrvc	r0, [r1], #512	; 0x200
    12c8:	060c2200 	streq	r2, [ip], -r0, lsl #4
    12cc:	31020000 	mrscc	r0, (UNDEF: 2)
    12d0:	00000033 	andeq	r0, r0, r3, lsr r0
    12d4:	00040bf8 	strdeq	r0, [r4], -r8
    12d8:	00000022 	andeq	r0, r0, r2, lsr #32
    12dc:	09029c01 	stmdbeq	r2, {r0, sl, fp, ip, pc}
    12e0:	531c0000 	tstpl	ip, #0
    12e4:	02310200 	eorseq	r0, r1, #0, 4
    12e8:	02000009 	andeq	r0, r0, #9
    12ec:	06007491 			; <UNDEFINED> instruction: 0x06007491
    12f0:	00044404 	andeq	r4, r4, r4, lsl #8
    12f4:	07cb2100 	strbeq	r2, [fp, r0, lsl #2]
    12f8:	2b020000 	blcs	81300 <ringBuffer+0x295f8>
    12fc:	00040bdc 	ldrdeq	r0, [r4], -ip
    1300:	0000001c 	andeq	r0, r0, ip, lsl r0
    1304:	092a9c01 	stmdbeq	sl!, {r0, sl, fp, ip, pc}
    1308:	531c0000 	tstpl	ip, #0
    130c:	552b0200 	strpl	r0, [fp, #-512]!	; 0xfffffe00
    1310:	02000006 	andeq	r0, r0, #6
    1314:	20007491 	mulcs	r0, r1, r4
    1318:	00000542 	andeq	r0, r0, r2, asr #10
    131c:	0bb69a01 	bleq	feda7b28 <__bss_end__+0xf54b9524>
    1320:	00260004 	eoreq	r0, r6, r4
    1324:	9c010000 	stcls	0, cr0, [r1], {-0}
    1328:	00000969 	andeq	r0, r0, r9, ror #18
    132c:	0100761c 	tsteq	r0, ip, lsl r6
    1330:	0000ea9a 	muleq	r0, sl, sl
    1334:	74910200 	ldrvc	r0, [r1], #512	; 0x200
    1338:	01006e1c 	tsteq	r0, ip, lsl lr
    133c:	0000929a 	muleq	r0, sl, r2
    1340:	70910200 	addsvc	r0, r1, r0, lsl #4
    1344:	0006cb15 	andeq	ip, r6, r5, lsl fp
    1348:	8d9c0100 	ldfhis	f0, [ip]
    134c:	05000009 	streq	r0, [r0, #-9]
    1350:	0570f003 	ldrbeq	pc, [r0, #-3]!	; <UNPREDICTABLE>
    1354:	ea230000 	b	8c135c <ringBuffer+0x869654>
    1358:	82000000 	andhi	r0, r0, #0
    135c:	24000009 	strcs	r0, [r0], #-9
    1360:	000000ea 	andeq	r0, r0, sl, ror #1
    1364:	00003324 	andeq	r3, r0, r4, lsr #6
    1368:	00922400 	addseq	r2, r2, r0, lsl #8
    136c:	06000000 	streq	r0, [r0], -r0
    1370:	00096904 	andeq	r6, r9, r4, lsl #18
    1374:	09820500 	stmibeq	r2, {r8, sl}
    1378:	88250000 	stmdahi	r5!, {}	; <UNPREDICTABLE>
    137c:	22000009 	andcs	r0, r0, #9
    1380:	00000555 	andeq	r0, r0, r5, asr r5
    1384:	006f8f01 	rsbeq	r8, pc, r1, lsl #30
    1388:	0b980000 	bleq	fe601390 <__bss_end__+0xf4d12d8c>
    138c:	001e0004 	andseq	r0, lr, r4
    1390:	9c010000 	stcls	0, cr0, [r1], {-0}
    1394:	000009c4 	andeq	r0, r0, r4, asr #19
    1398:	0100771c 	tsteq	r0, ip, lsl r7
    139c:	00007a8f 	andeq	r7, r0, pc, lsl #21
    13a0:	74910200 	ldrvc	r0, [r1], #512	; 0x200
    13a4:	0100631c 	tsteq	r0, ip, lsl r3
    13a8:	0000868f 	andeq	r8, r0, pc, lsl #13
    13ac:	70910200 	addsvc	r0, r1, r0, lsl #4
    13b0:	063a2100 	ldrteq	r2, [sl], -r0, lsl #2
    13b4:	5b010000 	blpl	413bc <blake2s_compress+0x504>
    13b8:	00040b52 	andeq	r0, r4, r2, asr fp
    13bc:	00000046 	andeq	r0, r0, r6, asr #32
    13c0:	0a009c01 	beq	283cc <.DATA_REGION_1__bss_end+0x7c14>
    13c4:	641c0000 	ldrvs	r0, [ip], #-0
    13c8:	01007473 	tsteq	r0, r3, ror r4
    13cc:	0000ea5b 	andeq	lr, r0, fp, asr sl
    13d0:	6c910200 	lfmvs	f0, 4, [r1], {0}
    13d4:	0100771c 	tsteq	r0, ip, lsl r7
    13d8:	00006f5b 	andeq	r6, r0, fp, asr pc
    13dc:	68910200 	ldmvs	r1, {r9}
    13e0:	0100701e 	tsteq	r0, lr, lsl r0
    13e4:	000a0060 	andeq	r0, sl, r0, rrx
    13e8:	74910200 	ldrvc	r0, [r1], #512	; 0x200
    13ec:	41040600 	tstmi	r4, r0, lsl #12
    13f0:	21000000 	mrscs	r0, (UNDEF: 0)
    13f4:	00000a12 	andeq	r0, r0, r2, lsl sl
    13f8:	0b185001 	bleq	615404 <ringBuffer+0x5bd6fc>
    13fc:	003a0004 	eorseq	r0, sl, r4
    1400:	9c010000 	stcls	0, cr0, [r1], {-0}
    1404:	00000a42 	andeq	r0, r0, r2, asr #20
    1408:	7473641c 	ldrbtvc	r6, [r3], #-1052	; 0xfffffbe4
    140c:	ea500100 	b	1401814 <ringBuffer+0x13a9b0c>
    1410:	02000000 	andeq	r0, r0, #0
    1414:	771c6c91 			; <UNDEFINED> instruction: 0x771c6c91
    1418:	5d500100 	ldfple	f0, [r0, #-0]
    141c:	02000000 	andeq	r0, r0, #0
    1420:	701e6a91 	mulsvc	lr, r1, sl
    1424:	00550100 	subseq	r0, r5, r0, lsl #2
    1428:	0200000a 	andeq	r0, r0, #10
    142c:	26007491 			; <UNDEFINED> instruction: 0x26007491
    1430:	000006b3 			; <UNDEFINED> instruction: 0x000006b3
    1434:	006f2101 	rsbeq	r2, pc, r1, lsl #2
    1438:	0adc0000 	beq	ff701440 <__bss_end__+0xf5e12e3c>
    143c:	003c0004 	eorseq	r0, ip, r4
    1440:	9c010000 	stcls	0, cr0, [r1], {-0}
    1444:	6372731c 	cmnvs	r2, #28, 6	; 0x70000000
    1448:	f2210100 	vrhadd.s32	d0, d1, d0
    144c:	02000005 	andeq	r0, r0, #5
    1450:	701e6c91 	mulsvc	lr, r1, ip
    1454:	3d280100 	stfccs	f0, [r8, #-0]
    1458:	02000007 	andeq	r0, r0, #7
    145c:	00007491 	muleq	r0, r1, r4
    1460:	00000ada 	ldrdeq	r0, [r0], -sl
    1464:	042d0004 	strteq	r0, [sp], #-4
    1468:	01040000 	mrseq	r0, (UNDEF: 4)
    146c:	00000af4 	strdeq	r0, [r0], -r4
    1470:	000d3b0c 	andeq	r3, sp, ip, lsl #22
    1474:	00003b00 	andeq	r3, r0, r0, lsl #22
    1478:	043cc400 	ldrteq	ip, [ip], #-1024	; 0xfffffc00
    147c:	000cd800 	andeq	sp, ip, r0, lsl #16
    1480:	000b7300 	andeq	r7, fp, r0, lsl #6
    1484:	05310200 	ldreq	r0, [r1, #-512]!	; 0xfffffe00
    1488:	d8020000 	stmdale	r2, {}	; <UNPREDICTABLE>
    148c:	00000030 	andeq	r0, r0, r0, lsr r0
    1490:	83070403 	movwhi	r0, #29699	; 0x7403
    1494:	03000005 	movweq	r0, #5
    1498:	086e0801 	stmdaeq	lr!, {r0, fp}^
    149c:	02030000 	andeq	r0, r3, #0
    14a0:	00075307 	andeq	r5, r7, r7, lsl #6
    14a4:	07040300 	streq	r0, [r4, -r0, lsl #6]
    14a8:	0000057e 	andeq	r0, r0, lr, ror r5
    14ac:	70060103 	andvc	r0, r6, r3, lsl #2
    14b0:	03000008 	movweq	r0, #8
    14b4:	087c0502 	ldmdaeq	ip!, {r1, r8, sl}^
    14b8:	04040000 	streq	r0, [r4], #-0
    14bc:	746e6905 	strbtvc	r6, [lr], #-2309	; 0xfffff6fb
    14c0:	05080300 	streq	r0, [r8, #-768]	; 0xfffffd00
    14c4:	000005b9 			; <UNDEFINED> instruction: 0x000005b9
    14c8:	79070803 	stmdbvc	r7, {r0, r1, fp}
    14cc:	02000005 	andeq	r0, r0, #5
    14d0:	00000603 	andeq	r0, r0, r3, lsl #12
    14d4:	00613703 	rsbeq	r3, r1, r3, lsl #14
    14d8:	f8020000 			; <UNDEFINED> instruction: 0xf8020000
    14dc:	03000004 	movweq	r0, #4
    14e0:	00008583 	andeq	r8, r0, r3, lsl #11
    14e4:	05040300 	streq	r0, [r4, #-768]	; 0xfffffd00
    14e8:	000005be 			; <UNDEFINED> instruction: 0x000005be
    14ec:	00093d02 	andeq	r3, r9, r2, lsl #26
    14f0:	6f840300 	svcvs	0x00840300
    14f4:	03000000 	movweq	r0, #0
    14f8:	01020704 	tsteq	r2, r4, lsl #14
    14fc:	04050000 	streq	r0, [r5], #-0
    1500:	00a60406 	adceq	r0, r6, r6, lsl #8
    1504:	01030000 	mrseq	r0, (UNDEF: 3)
    1508:	00087708 	andeq	r7, r8, r8, lsl #14
    150c:	00a60700 	adceq	r0, r6, r0, lsl #14
    1510:	12080000 	andne	r0, r8, #0
    1514:	98000008 	stmdals	r0, {r3}
    1518:	022ff104 	eoreq	pc, pc, #4, 2
    151c:	33090000 	movwcc	r0, #36864	; 0x9000
    1520:	04000006 	streq	r0, [r0], #-6
    1524:	00005af2 	strdeq	r5, [r0], -r2
    1528:	00090000 	andeq	r0, r9, r0
    152c:	04000005 	streq	r0, [r0], #-5
    1530:	0000a0f7 	strdeq	sl, [r0], -r7
    1534:	f6090400 			; <UNDEFINED> instruction: 0xf6090400
    1538:	04000005 	streq	r0, [r0], #-5
    153c:	0000a0f8 	strdeq	sl, [r0], -r8
    1540:	47090800 	strmi	r0, [r9, -r0, lsl #16]
    1544:	04000009 	streq	r0, [r0], #-9
    1548:	0000a0f9 	strdeq	sl, [r0], -r9
    154c:	29090c00 	stmdbcs	r9, {sl, fp}
    1550:	0400000a 	streq	r0, [r0], #-10
    1554:	0000a0fa 	strdeq	sl, [r0], -sl	; <UNPREDICTABLE>
    1558:	25091000 	strcs	r1, [r9, #-0]
    155c:	04000007 	streq	r0, [r0], #-7
    1560:	0000a0fb 	strdeq	sl, [r0], -fp
    1564:	e0091400 	and	r1, r9, r0, lsl #8
    1568:	04000007 	streq	r0, [r0], #-7
    156c:	0000a0fc 	strdeq	sl, [r0], -ip
    1570:	6c091800 	stcvs	8, cr1, [r9], {-0}
    1574:	04000005 	streq	r0, [r0], #-5
    1578:	0000a0fd 	strdeq	sl, [r0], -sp
    157c:	42091c00 	andmi	r1, r9, #0, 24
    1580:	04000006 	streq	r0, [r0], #-6
    1584:	0000a0fe 	strdeq	sl, [r0], -lr
    1588:	870a2000 	strhi	r2, [sl, -r0]
    158c:	04000007 	streq	r0, [r0], #-7
    1590:	00a00100 	adceq	r0, r0, r0, lsl #2
    1594:	0a240000 	beq	90159c <ringBuffer+0x8a9894>
    1598:	000009c6 	andeq	r0, r0, r6, asr #19
    159c:	a0010104 	andge	r0, r1, r4, lsl #2
    15a0:	28000000 	stmdacs	r0, {}	; <UNPREDICTABLE>
    15a4:	0009550a 	andeq	r5, r9, sl, lsl #10
    15a8:	01020400 	tsteq	r2, r0, lsl #8
    15ac:	000000a0 	andeq	r0, r0, r0, lsr #1
    15b0:	08410a2c 	stmdaeq	r1, {r2, r3, r5, r9, fp}^
    15b4:	04040000 	streq	r0, [r4], #-0
    15b8:	00026701 	andeq	r6, r2, r1, lsl #14
    15bc:	0d0a3000 	stceq	0, cr3, [sl, #-0]
    15c0:	04000005 	streq	r0, [r0], #-5
    15c4:	026d0106 	rsbeq	r0, sp, #-2147483647	; 0x80000001
    15c8:	0a340000 	beq	d015d0 <ringBuffer+0xca98c8>
    15cc:	000005ee 	andeq	r0, r0, lr, ror #11
    15d0:	5a010804 	bpl	435e8 <blake2s_compress+0x2730>
    15d4:	38000000 	stmdacc	r0, {}	; <UNPREDICTABLE>
    15d8:	00079b0a 	andeq	r9, r7, sl, lsl #22
    15dc:	010c0400 	tsteq	ip, r0, lsl #8
    15e0:	0000005a 	andeq	r0, r0, sl, asr r0
    15e4:	06960a3c 			; <UNDEFINED> instruction: 0x06960a3c
    15e8:	0e040000 	cdpeq	0, 0, cr0, cr4, cr0, {0}
    15ec:	00007a01 	andeq	r7, r0, r1, lsl #20
    15f0:	4e0a4000 	cdpmi	0, 0, cr4, cr10, cr0, {0}
    15f4:	04000006 	streq	r0, [r0], #-6
    15f8:	003e0112 	eorseq	r0, lr, r2, lsl r1
    15fc:	0a440000 	beq	1101604 <ringBuffer+0x10a98fc>
    1600:	000008ae 	andeq	r0, r0, lr, lsr #17
    1604:	4c011304 	stcmi	3, cr1, [r1], {4}
    1608:	46000000 	strmi	r0, [r0], -r0
    160c:	0005380a 	andeq	r3, r5, sl, lsl #16
    1610:	01140400 	tsteq	r4, r0, lsl #8
    1614:	00000273 	andeq	r0, r0, r3, ror r2
    1618:	07950a47 	ldreq	r0, [r5, r7, asr #20]
    161c:	18040000 	stmdane	r4, {}	; <UNPREDICTABLE>
    1620:	00028301 	andeq	r8, r2, r1, lsl #6
    1624:	9a0a4800 	bls	29362c <ringBuffer+0x23b924>
    1628:	04000006 	streq	r0, [r0], #-6
    162c:	008c0121 	addeq	r0, ip, r1, lsr #2
    1630:	0a500000 	beq	1401638 <ringBuffer+0x13a9930>
    1634:	0000096c 	andeq	r0, r0, ip, ror #18
    1638:	9e012904 	vmlals.f16	s4, s2, s8	; <UNPREDICTABLE>
    163c:	58000000 	stmdapl	r0, {}	; <UNPREDICTABLE>
    1640:	0009730a 	andeq	r7, r9, sl, lsl #6
    1644:	012a0400 			; <UNDEFINED> instruction: 0x012a0400
    1648:	0000009e 	muleq	r0, lr, r0
    164c:	097a0a5c 	ldmdbeq	sl!, {r2, r3, r4, r6, r9, fp}^
    1650:	2b040000 	blcs	101658 <ringBuffer+0xa9950>
    1654:	00009e01 	andeq	r9, r0, r1, lsl #28
    1658:	810a6000 	mrshi	r6, (UNDEF: 10)
    165c:	04000009 	streq	r0, [r0], #-9
    1660:	009e012c 	addseq	r0, lr, ip, lsr #2
    1664:	0a640000 	beq	190166c <ringBuffer+0x18a9964>
    1668:	00000988 	andeq	r0, r0, r8, lsl #19
    166c:	25012e04 	strcs	r2, [r1, #-3588]	; 0xfffff1fc
    1670:	68000000 	stmdavs	r0, {}	; <UNPREDICTABLE>
    1674:	0007a30a 	andeq	sl, r7, sl, lsl #6
    1678:	012f0400 			; <UNDEFINED> instruction: 0x012f0400
    167c:	0000005a 	andeq	r0, r0, sl, asr r0
    1680:	098f0a6c 	stmibeq	pc, {r2, r3, r5, r6, r9, fp}	; <UNPREDICTABLE>
    1684:	31040000 	mrscc	r0, (UNDEF: 4)
    1688:	00028901 	andeq	r8, r2, r1, lsl #18
    168c:	0b007000 	bleq	1d694 <.DATA_REGION_0__data_end+0xc97c>
    1690:	00000807 	andeq	r0, r0, r7, lsl #16
    1694:	d4089604 	strle	r9, [r8], #-1540	; 0xfffff9fc
    1698:	0c000006 	stceq	0, cr0, [r0], {6}
    169c:	02679c04 	rsbeq	r9, r7, #4, 24	; 0x400
    16a0:	37090000 	strcc	r0, [r9, -r0]
    16a4:	04000009 	streq	r0, [r0], #-9
    16a8:	0002679d 	muleq	r2, sp, r7
    16ac:	4d090000 	stcmi	0, cr0, [r9, #-0]
    16b0:	04000007 	streq	r0, [r0], #-7
    16b4:	00026d9e 	muleq	r2, lr, sp
    16b8:	30090400 	andcc	r0, r9, r0, lsl #8
    16bc:	04000008 	streq	r0, [r0], #-8
    16c0:	00005aa2 	andeq	r5, r0, r2, lsr #21
    16c4:	06000800 	streq	r0, [r0], -r0, lsl #16
    16c8:	00023604 	andeq	r3, r2, r4, lsl #12
    16cc:	b2040600 	andlt	r0, r4, #0, 12
    16d0:	0c000000 	stceq	0, cr0, [r0], {-0}
    16d4:	000000a6 	andeq	r0, r0, r6, lsr #1
    16d8:	00000283 	andeq	r0, r0, r3, lsl #5
    16dc:	0000970d 	andeq	r9, r0, sp, lsl #14
    16e0:	06000000 	streq	r0, [r0], -r0
    16e4:	00022f04 	andeq	r2, r2, r4, lsl #30
    16e8:	00a60c00 	adceq	r0, r6, r0, lsl #24
    16ec:	02990000 	addseq	r0, r9, #0
    16f0:	970d0000 	strls	r0, [sp, -r0]
    16f4:	27000000 	strcs	r0, [r0, -r0]
    16f8:	07170e00 	ldreq	r0, [r7, -r0, lsl #28]
    16fc:	b00f0000 	andlt	r0, pc, r0
    1700:	04000007 	streq	r0, [r0], #-7
    1704:	0299013b 	addseq	r0, r9, #-1073741810	; 0xc000000e
    1708:	bd0f0000 	stclt	0, cr0, [pc, #-0]	; 1710 <_init-0xf410>
    170c:	04000008 	streq	r0, [r0], #-8
    1710:	0299013c 	addseq	r0, r9, #60, 2
    1714:	5c0f0000 	stcpl	0, cr0, [pc], {-0}
    1718:	04000005 	streq	r0, [r0], #-5
    171c:	0299013d 	addseq	r0, r9, #1073741839	; 0x4000000f
    1720:	04060000 	streq	r0, [r6], #-0
    1724:	000000ad 	andeq	r0, r0, sp, lsr #1
    1728:	0002c207 	andeq	ip, r2, r7, lsl #4
    172c:	06df1000 	ldrbeq	r1, [pc], r0
    1730:	a8050000 	stmdage	r5, {}	; <UNPREDICTABLE>
    1734:	0000026d 	andeq	r0, r0, sp, ror #4
    1738:	0007a910 	andeq	sl, r7, r0, lsl r9
    173c:	6da90500 	cfstr32vs	mvfx0, [r9]
    1740:	10000002 	andne	r0, r0, r2
    1744:	00000998 	muleq	r0, r8, r9
    1748:	026daa05 	rsbeq	sl, sp, #20480	; 0x5000
    174c:	44100000 	ldrmi	r0, [r0], #-0
    1750:	06000007 	streq	r0, [r0], -r7
    1754:	00005a1a 	andeq	r5, r0, sl, lsl sl
    1758:	02c80c00 	sbceq	r0, r8, #0, 24
    175c:	03040000 	movweq	r0, #16384	; 0x4000
    1760:	00110000 	andseq	r0, r1, r0
    1764:	0002f907 	andeq	pc, r2, r7, lsl #18
    1768:	08351000 	ldmdaeq	r5!, {ip}
    176c:	1b060000 	blne	181774 <ringBuffer+0x129a6c>
    1770:	00000304 	andeq	r0, r0, r4, lsl #6
    1774:	e9020103 	stmdb	r2, {r0, r1, r8}
    1778:	02000001 	andeq	r0, r0, #1
    177c:	000009be 			; <UNDEFINED> instruction: 0x000009be
    1780:	00373007 	eorseq	r3, r7, r7
    1784:	e9020000 	stmdb	r2, {}	; <UNPREDICTABLE>
    1788:	07000008 	streq	r0, [r0, -r8]
    178c:	00003033 	andeq	r3, r0, r3, lsr r0
    1790:	01101200 	tsteq	r0, r0, lsl #4
    1794:	00036a10 	andeq	r6, r3, r0, lsl sl
    1798:	0d920900 	vldreq.16	s0, [r2]	; <UNPREDICTABLE>
    179c:	11010000 	mrsne	r0, (UNDEF: 1)
    17a0:	00000326 	andeq	r0, r0, r6, lsr #6
    17a4:	0be00900 	bleq	ff803bac <__bss_end__+0xf5f155a8>
    17a8:	12010000 	andne	r0, r1, #0
    17ac:	00000326 	andeq	r0, r0, r6, lsr #6
    17b0:	0c420904 	mcrreq	9, 0, r0, r2, cr4	; <UNPREDICTABLE>
    17b4:	13010000 	movwne	r0, #4096	; 0x1000
    17b8:	00000326 	andeq	r0, r0, r6, lsr #6
    17bc:	0ca80908 			; <UNDEFINED> instruction: 0x0ca80908
    17c0:	14010000 	strne	r0, [r1], #-0
    17c4:	0000031b 	andeq	r0, r0, fp, lsl r3
    17c8:	8d02000c 	stchi	0, cr0, [r2, #-48]	; 0xffffffd0
    17cc:	0100000c 	tsteq	r0, ip
    17d0:	00033115 	andeq	r3, r3, r5, lsl r1
    17d4:	68081300 	stmdavs	r8, {r8, r9, ip}
    17d8:	17010989 	strne	r0, [r1, -r9, lsl #19]
    17dc:	000003ab 	andeq	r0, r0, fp, lsr #7
    17e0:	00120809 	andseq	r0, r2, r9, lsl #16
    17e4:	ab180100 	blge	601bec <ringBuffer+0x5a9ee4>
    17e8:	00000003 	andeq	r0, r0, r3
    17ec:	000c5f14 	andeq	r5, ip, r4, lsl pc
    17f0:	25190100 	ldrcs	r0, [r9, #-256]	; 0xffffff00
    17f4:	00000000 	andeq	r0, r0, r0
    17f8:	14098968 	strne	r8, [r9], #-2408	; 0xfffff698
    17fc:	00000d36 	andeq	r0, r0, r6, lsr sp
    1800:	00251a01 	eoreq	r1, r5, r1, lsl #20
    1804:	68040000 	stmdavs	r4, {}	; <UNPREDICTABLE>
    1808:	0c000989 			; <UNDEFINED> instruction: 0x0c000989
    180c:	0000036a 	andeq	r0, r0, sl, ror #6
    1810:	000003be 			; <UNDEFINED> instruction: 0x000003be
    1814:	00009715 	andeq	r9, r0, r5, lsl r7
    1818:	98967f00 	ldmls	r6, {r8, r9, sl, fp, ip, sp, lr}
    181c:	9d020000 	stcls	0, cr0, [r2, #-0]
    1820:	0100000c 	tsteq	r0, ip
    1824:	0003751b 	andeq	r7, r3, fp, lsl r5
    1828:	0d9a1600 	ldceq	6, cr1, [sl]
    182c:	1d010000 	stcne	0, cr0, [r1, #-0]
    1830:	000003be 			; <UNDEFINED> instruction: 0x000003be
    1834:	7d080305 	stcvc	3, cr0, [r8, #-20]	; 0xffffffec
    1838:	83100005 	tsthi	r0, #5
    183c:	01000000 	mrseq	r0, (UNDEF: 0)
    1840:	00005a4c 	andeq	r5, r0, ip, asr #20
    1844:	00921000 	addseq	r1, r2, r0
    1848:	4d010000 	stcmi	0, cr0, [r1, #-0]
    184c:	0000005a 	andeq	r0, r0, sl, asr r0
    1850:	000d0216 	andeq	r0, sp, r6, lsl r2
    1854:	5a500100 	bpl	1401c5c <ringBuffer+0x13a9f54>
    1858:	05000000 	streq	r0, [r0, #-0]
    185c:	057cbc03 	ldrbeq	fp, [ip, #-3075]!	; 0xfffff3fd
    1860:	0cec1700 	stcleq	7, cr1, [ip]
    1864:	30040000 	andcc	r0, r4, r0
    1868:	01000000 	mrseq	r0, (UNDEF: 0)
    186c:	00045d87 	andeq	r5, r4, r7, lsl #27
    1870:	51451800 	cmppl	r5, r0, lsl #16
    1874:	4e180000 	cdpmi	0, 1, cr0, cr8, cr0, {0}
    1878:	18010045 	stmdane	r1, {r0, r2, r6}
    187c:	02005348 	andeq	r5, r0, #72, 6	; 0x20000001
    1880:	004f4c18 	subeq	r4, pc, r8, lsl ip	; <UNPREDICTABLE>
    1884:	494d1803 	stmdbmi	sp, {r0, r1, fp, ip}^
    1888:	50180400 	andspl	r0, r8, r0, lsl #8
    188c:	1805004c 	stmdane	r5, {r2, r3, r6}
    1890:	06005356 			; <UNDEFINED> instruction: 0x06005356
    1894:	00435618 	subeq	r5, r3, r8, lsl r6
    1898:	49481807 	stmdbmi	r8, {r0, r1, r2, fp, ip}^
    189c:	4c180800 	ldcmi	8, cr0, [r8], {-0}
    18a0:	18090053 	stmdane	r9, {r0, r1, r4, r6}
    18a4:	0a004547 	beq	12dc8 <.DATA_REGION_0__data_end+0x20b0>
    18a8:	00544c18 	subseq	r4, r4, r8, lsl ip
    18ac:	5447180b 	strbpl	r1, [r7], #-2059	; 0xfffff7f5
    18b0:	4c180c00 	ldcmi	12, cr0, [r8], {-0}
    18b4:	180d0045 	stmdane	sp, {r0, r2, r6}
    18b8:	0e004c41 	cdpeq	12, 0, cr4, cr0, cr1, {2}
    18bc:	0cdd1900 			; <UNDEFINED> instruction: 0x0cdd1900
    18c0:	9d010000 	stcls	0, cr0, [r1, #-0]
    18c4:	00005a02 	andeq	r5, r0, r2, lsl #20
    18c8:	10030500 	andne	r0, r3, r0, lsl #10
    18cc:	1a098ee5 	bne	265468 <ringBuffer+0x20d760>
    18d0:	00746e63 	rsbseq	r6, r4, r3, ror #28
    18d4:	5a02ab01 	bpl	ac4e0 <ringBuffer+0x547d8>
    18d8:	05000000 	streq	r0, [r0, #-0]
    18dc:	057cc003 	ldrbeq	ip, [ip, #-3]!
    18e0:	0bfb1b00 	bleq	ffec84e8 <__bss_end__+0xf65d9ee4>
    18e4:	ae010000 	cdpge	0, 0, cr0, cr1, cr0, {0}
    18e8:	04497002 	strbeq	r7, [r9], #-2
    18ec:	00002c00 	andeq	r2, r0, r0, lsl #24
    18f0:	1b9c0100 	blne	fe701cf8 <__bss_end__+0xf4e136f4>
    18f4:	00000cf6 	strdeq	r0, [r0], -r6
    18f8:	5a02a601 	bpl	ab104 <ringBuffer+0x533fc>
    18fc:	16000449 	strne	r0, [r0], -r9, asr #8
    1900:	01000000 	mrseq	r0, (UNDEF: 0)
    1904:	0dc01c9c 	stcleq	12, cr1, [r0, #624]	; 0x270
    1908:	9f010000 	svcls	0x00010000
    190c:	00005a02 	andeq	r5, r0, r2, lsl #20
    1910:	04494400 	strbeq	r4, [r9], #-1024	; 0xfffffc00
    1914:	00001600 	andeq	r1, r0, r0, lsl #12
    1918:	cf9c0100 	svcgt	0x009c0100
    191c:	1d000004 	stcne	0, cr0, [r0, #-16]
    1920:	0000031c 	andeq	r0, r0, ip, lsl r3
    1924:	5a029f01 	bpl	a9530 <ringBuffer+0x51828>
    1928:	02000000 	andeq	r0, r0, #0
    192c:	1e007491 	mcrne	4, 0, r7, cr0, cr1, {4}
    1930:	00000c64 	andeq	r0, r0, r4, ror #24
    1934:	ac027c01 	stcge	12, cr7, [r2], {1}
    1938:	98000448 	stmdals	r0, {r3, r6, sl}
    193c:	01000000 	mrseq	r0, (UNDEF: 0)
    1940:	0005319c 	muleq	r5, ip, r1
    1944:	0c171d00 	ldceq	13, cr1, [r7], {-0}
    1948:	7c010000 	stcvc	0, cr0, [r1], {-0}
    194c:	00032602 	andeq	r2, r3, r2, lsl #12
    1950:	54910200 	ldrpl	r0, [r1], #512	; 0x200
    1954:	000d171d 	andeq	r1, sp, sp, lsl r7
    1958:	027c0100 	rsbseq	r0, ip, #0, 2
    195c:	00000326 	andeq	r0, r0, r6, lsr #6
    1960:	1d509102 	ldfnep	f1, [r0, #-8]
    1964:	00000d5f 	andeq	r0, r0, pc, asr sp
    1968:	26027c01 	strcs	r7, [r2], -r1, lsl #24
    196c:	02000003 	andeq	r0, r0, #3
    1970:	691f4c91 	ldmdbvs	pc, {r0, r4, r7, sl, fp, lr}	; <UNPREDICTABLE>
    1974:	0100000d 	tsteq	r0, sp
    1978:	03260285 			; <UNDEFINED> instruction: 0x03260285
    197c:	91020000 	mrsls	r0, (UNDEF: 2)
    1980:	0c881f6c 	stceq	15, cr1, [r8], {108}	; 0x6c
    1984:	87010000 	strhi	r0, [r1, -r0]
    1988:	00036a02 	andeq	r6, r3, r2, lsl #20
    198c:	5c910200 	lfmpl	f0, 4, [r1], {0}
    1990:	0bac1e00 	bleq	feb09198 <__bss_end__+0xf521ab94>
    1994:	5a010000 	bpl	4199c <blake2s_compress+0xae4>
    1998:	04480c02 	strbeq	r0, [r8], #-3074	; 0xfffff3fe
    199c:	0000a000 	andeq	sl, r0, r0
    19a0:	939c0100 	orrsls	r0, ip, #0, 2
    19a4:	1d000005 	stcne	0, cr0, [r0, #-20]	; 0xffffffec
    19a8:	00000c17 	andeq	r0, r0, r7, lsl ip
    19ac:	26025a01 	strcs	r5, [r2], -r1, lsl #20
    19b0:	02000003 	andeq	r0, r0, #3
    19b4:	171d5491 			; <UNDEFINED> instruction: 0x171d5491
    19b8:	0100000d 	tsteq	r0, sp
    19bc:	0326025a 			; <UNDEFINED> instruction: 0x0326025a
    19c0:	91020000 	mrsls	r0, (UNDEF: 2)
    19c4:	0d5f1d50 	ldcleq	13, cr1, [pc, #-320]	; 188c <_init-0xf294>
    19c8:	5a010000 	bpl	419d0 <blake2s_compress+0xb18>
    19cc:	00032602 	andeq	r2, r3, r2, lsl #12
    19d0:	4c910200 	lfmmi	f0, 4, [r1], {0}
    19d4:	000bbd1f 	andeq	fp, fp, pc, lsl sp
    19d8:	02630100 	rsbeq	r0, r3, #0, 2
    19dc:	00000314 	andeq	r0, r0, r4, lsl r3
    19e0:	1f6f9102 	svcne	0x006f9102
    19e4:	00000c88 	andeq	r0, r0, r8, lsl #25
    19e8:	6a026501 	bvs	9adf4 <ringBuffer+0x430ec>
    19ec:	02000003 	andeq	r0, r0, #3
    19f0:	1e005c91 	mcrne	12, 0, r5, cr0, cr1, {4}
    19f4:	00000be9 	andeq	r0, r0, r9, ror #23
    19f8:	ec021801 	stc	8, cr1, [r2], {1}
    19fc:	20000446 	andcs	r0, r0, r6, asr #8
    1a00:	01000001 	tsteq	r0, r1
    1a04:	0006049c 	muleq	r6, ip, r4
    1a08:	0c171d00 	ldceq	13, cr1, [r7], {-0}
    1a0c:	18010000 	stmdane	r1, {}	; <UNPREDICTABLE>
    1a10:	00032602 	andeq	r2, r3, r2, lsl #12
    1a14:	54910200 	ldrpl	r0, [r1], #512	; 0x200
    1a18:	000d171d 	andeq	r1, sp, sp, lsl r7
    1a1c:	02180100 	andseq	r0, r8, #0, 2
    1a20:	00000326 	andeq	r0, r0, r6, lsr #6
    1a24:	1d509102 	ldfnep	f1, [r0, #-8]
    1a28:	00000d5f 	andeq	r0, r0, pc, asr sp
    1a2c:	26021801 	strcs	r1, [r2], -r1, lsl #16
    1a30:	02000003 	andeq	r0, r0, #3
    1a34:	bd1f4c91 	ldclt	12, cr4, [pc, #-580]	; 17f8 <_init-0xf328>
    1a38:	0100000b 	tsteq	r0, fp
    1a3c:	0314021b 	tsteq	r4, #-1342177279	; 0xb0000001
    1a40:	91020000 	mrsls	r0, (UNDEF: 2)
    1a44:	0d691f6f 	stcleq	15, cr1, [r9, #-444]!	; 0xfffffe44
    1a48:	1e010000 	cdpne	0, 0, cr0, cr1, cr0, {0}
    1a4c:	00032602 	andeq	r2, r3, r2, lsl #12
    1a50:	68910200 	ldmvs	r1, {r9}
    1a54:	000c881f 	andeq	r8, ip, pc, lsl r8
    1a58:	02210100 	eoreq	r0, r1, #0, 2
    1a5c:	0000036a 	andeq	r0, r0, sl, ror #6
    1a60:	00589102 	subseq	r9, r8, r2, lsl #2
    1a64:	000d841e 	andeq	r8, sp, lr, lsl r4
    1a68:	01e60100 	mvneq	r0, r0, lsl #2
    1a6c:	00044648 	andeq	r4, r4, r8, asr #12
    1a70:	000000a4 	andeq	r0, r0, r4, lsr #1
    1a74:	06489c01 	strbeq	r9, [r8], -r1, lsl #24
    1a78:	171d0000 	ldrne	r0, [sp, -r0]
    1a7c:	0100000c 	tsteq	r0, ip
    1a80:	032601e6 			; <UNDEFINED> instruction: 0x032601e6
    1a84:	91020000 	mrsls	r0, (UNDEF: 2)
    1a88:	0d691f54 	stcleq	15, cr1, [r9, #-336]!	; 0xfffffeb0
    1a8c:	f1010000 	setend	le
    1a90:	00032601 	andeq	r2, r3, r1, lsl #12
    1a94:	6c910200 	lfmvs	f0, 4, [r1], {0}
    1a98:	000c881f 	andeq	r8, ip, pc, lsl r8
    1a9c:	01f40100 	mvnseq	r0, r0, lsl #2
    1aa0:	0000036a 	andeq	r0, r0, sl, ror #6
    1aa4:	005c9102 	subseq	r9, ip, r2, lsl #2
    1aa8:	000cad1e 	andeq	sl, ip, lr, lsl sp
    1aac:	01a30100 			; <UNDEFINED> instruction: 0x01a30100
    1ab0:	0004452c 	andeq	r4, r4, ip, lsr #10
    1ab4:	0000011c 	andeq	r0, r0, ip, lsl r1
    1ab8:	068c9c01 	streq	r9, [ip], r1, lsl #24
    1abc:	171d0000 	ldrne	r0, [sp, -r0]
    1ac0:	0100000c 	tsteq	r0, ip
    1ac4:	032601a3 			; <UNDEFINED> instruction: 0x032601a3
    1ac8:	91020000 	mrsls	r0, (UNDEF: 2)
    1acc:	0d691f54 	stcleq	15, cr1, [r9, #-336]!	; 0xfffffeb0
    1ad0:	ad010000 	stcge	0, cr0, [r1, #-0]
    1ad4:	00032601 	andeq	r2, r3, r1, lsl #12
    1ad8:	6c910200 	lfmvs	f0, 4, [r1], {0}
    1adc:	000c881f 	andeq	r8, ip, pc, lsl r8
    1ae0:	01b00100 	lslseq	r0, r0, #2
    1ae4:	0000036a 	andeq	r0, r0, sl, ror #6
    1ae8:	005c9102 	subseq	r9, ip, r2, lsl #2
    1aec:	000bca1e 	andeq	ip, fp, lr, lsl sl
    1af0:	01700100 	cmneq	r0, r0, lsl #2
    1af4:	00044450 	andeq	r4, r4, r0, asr r4
    1af8:	000000dc 	ldrdeq	r0, [r0], -ip
    1afc:	06d09c01 	ldrbeq	r9, [r0], r1, lsl #24
    1b00:	171d0000 	ldrne	r0, [sp, -r0]
    1b04:	0100000c 	tsteq	r0, ip
    1b08:	03260170 			; <UNDEFINED> instruction: 0x03260170
    1b0c:	91020000 	mrsls	r0, (UNDEF: 2)
    1b10:	0d691f54 	stcleq	15, cr1, [r9, #-336]!	; 0xfffffeb0
    1b14:	7b010000 	blvc	41b1c <blake2s_compress+0xc64>
    1b18:	00032601 	andeq	r2, r3, r1, lsl #12
    1b1c:	6c910200 	lfmvs	f0, 4, [r1], {0}
    1b20:	000c881f 	andeq	r8, ip, pc, lsl r8
    1b24:	017e0100 	cmneq	lr, r0, lsl #2
    1b28:	0000036a 	andeq	r0, r0, sl, ror #6
    1b2c:	005c9102 	subseq	r9, ip, r2, lsl #2
    1b30:	000cc41e 	andeq	ip, ip, lr, lsl r4
    1b34:	013f0100 	teqeq	pc, r0, lsl #2
    1b38:	000443a4 	andeq	r4, r4, r4, lsr #7
    1b3c:	000000ac 	andeq	r0, r0, ip, lsr #1
    1b40:	07149c01 	ldreq	r9, [r4, -r1, lsl #24]
    1b44:	171d0000 	ldrne	r0, [sp, -r0]
    1b48:	0100000c 	tsteq	r0, ip
    1b4c:	0326013f 			; <UNDEFINED> instruction: 0x0326013f
    1b50:	91020000 	mrsls	r0, (UNDEF: 2)
    1b54:	0d691f54 	stcleq	15, cr1, [r9, #-336]!	; 0xfffffeb0
    1b58:	49010000 	stmdbmi	r1, {}	; <UNPREDICTABLE>
    1b5c:	00032601 	andeq	r2, r3, r1, lsl #12
    1b60:	6c910200 	lfmvs	f0, 4, [r1], {0}
    1b64:	000c881f 	andeq	r8, ip, pc, lsl r8
    1b68:	014c0100 	mrseq	r0, (UNDEF: 92)
    1b6c:	0000036a 	andeq	r0, r0, sl, ror #6
    1b70:	005c9102 	subseq	r9, ip, r2, lsl #2
    1b74:	000da520 	andeq	sl, sp, r0, lsr #10
    1b78:	80f50100 	rscshi	r0, r5, r0, lsl #2
    1b7c:	24000442 	strcs	r0, [r0], #-1090	; 0xfffffbbe
    1b80:	01000001 	tsteq	r0, r1
    1b84:	00079a9c 	muleq	r7, ip, sl
    1b88:	0c172100 	ldfeqs	f2, [r7], {-0}
    1b8c:	f5010000 			; <UNDEFINED> instruction: 0xf5010000
    1b90:	00000326 	andeq	r0, r0, r6, lsr #6
    1b94:	21449102 	cmpcs	r4, r2, lsl #2
    1b98:	00000d17 	andeq	r0, r0, r7, lsl sp
    1b9c:	0326f501 	msreq	CPSR_sx, #4194304	; 0x400000
    1ba0:	91020000 	mrsls	r0, (UNDEF: 2)
    1ba4:	0d5f2140 	ldfeqe	f2, [pc, #-256]	; 1aac <_init-0xf074>
    1ba8:	f5010000 			; <UNDEFINED> instruction: 0xf5010000
    1bac:	00000326 	andeq	r0, r0, r6, lsr #6
    1bb0:	7fbc9103 	svcvc	0x00bc9103
    1bb4:	000bbd22 	andeq	fp, fp, r2, lsr #26
    1bb8:	14ff0100 	ldrbtne	r0, [pc], #256	; 1bc0 <_init-0xef60>
    1bbc:	02000003 	andeq	r0, r0, #3
    1bc0:	691f6f91 	ldmdbvs	pc, {r0, r4, r7, r8, r9, sl, fp, sp, lr}	; <UNPREDICTABLE>
    1bc4:	0100000d 	tsteq	r0, sp
    1bc8:	03260103 			; <UNDEFINED> instruction: 0x03260103
    1bcc:	91020000 	mrsls	r0, (UNDEF: 2)
    1bd0:	0c881f68 	stceq	15, cr1, [r8], {104}	; 0x68
    1bd4:	25010000 	strcs	r0, [r1, #-0]
    1bd8:	00036a01 	andeq	r6, r3, r1, lsl #20
    1bdc:	58910200 	ldmpl	r1, {r9}
    1be0:	0442d023 	strbeq	sp, [r2], #-35	; 0xffffffdd
    1be4:	00004400 	andeq	r4, r0, r0, lsl #8
    1be8:	0c111f00 	ldceq	15, cr1, [r1], {-0}
    1bec:	0a010000 	beq	41bf4 <blake2s_compress+0xd3c>
    1bf0:	00036a01 	andeq	r6, r3, r1, lsl #20
    1bf4:	48910200 	ldmmi	r1, {r9}
    1bf8:	1c200000 	stcne	0, cr0, [r0], #-0
    1bfc:	0100000d 	tsteq	r0, sp
    1c00:	044164a7 	strbeq	r6, [r1], #-1191	; 0xfffffb59
    1c04:	00011c00 	andeq	r1, r1, r0, lsl #24
    1c08:	1d9c0100 	ldfnes	f0, [ip]
    1c0c:	21000008 	tstcs	r0, r8
    1c10:	00000c17 	andeq	r0, r0, r7, lsl ip
    1c14:	0326a701 			; <UNDEFINED> instruction: 0x0326a701
    1c18:	91020000 	mrsls	r0, (UNDEF: 2)
    1c1c:	0d172144 	ldfeqs	f2, [r7, #-272]	; 0xfffffef0
    1c20:	a7010000 	strge	r0, [r1, -r0]
    1c24:	00000326 	andeq	r0, r0, r6, lsr #6
    1c28:	21409102 	cmpcs	r0, r2, lsl #2
    1c2c:	00000d5f 	andeq	r0, r0, pc, asr sp
    1c30:	0326a701 			; <UNDEFINED> instruction: 0x0326a701
    1c34:	91030000 	mrsls	r0, (UNDEF: 3)
    1c38:	bd227fbc 	stclt	15, cr7, [r2, #-752]!	; 0xfffffd10
    1c3c:	0100000b 	tsteq	r0, fp
    1c40:	000314b1 			; <UNDEFINED> instruction: 0x000314b1
    1c44:	6f910200 	svcvs	0x00910200
    1c48:	000d6922 	andeq	r6, sp, r2, lsr #18
    1c4c:	26b60100 	ldrtcs	r0, [r6], r0, lsl #2
    1c50:	02000003 	andeq	r0, r0, #3
    1c54:	88226891 	stmdahi	r2!, {r0, r4, r7, fp, sp, lr}
    1c58:	0100000c 	tsteq	r0, ip
    1c5c:	00036adc 	ldrdeq	r6, [r3], -ip
    1c60:	58910200 	ldmpl	r1, {r9}
    1c64:	0441ae23 	strbeq	sl, [r1], #-3619	; 0xfffff1dd
    1c68:	00004600 	andeq	r4, r0, r0, lsl #12
    1c6c:	0c112200 	lfmeq	f2, 4, [r1], {-0}
    1c70:	bf010000 	svclt	0x00010000
    1c74:	0000036a 	andeq	r0, r0, sl, ror #6
    1c78:	00489102 	subeq	r9, r8, r2, lsl #2
    1c7c:	0b952400 	bleq	fe54ac84 <__bss_end__+0xf4c5c680>
    1c80:	8b010000 	blhi	41c88 <blake2s_compress+0xdd0>
    1c84:	00000314 	andeq	r0, r0, r4, lsl r3
    1c88:	00043fa4 	andeq	r3, r4, r4, lsr #31
    1c8c:	000001c0 	andeq	r0, r0, r0, asr #3
    1c90:	08839c01 	stmeq	r3, {r0, sl, fp, ip, pc}
    1c94:	42210000 	eormi	r0, r1, #0
    1c98:	0100000c 	tsteq	r0, ip
    1c9c:	0004018b 	andeq	r0, r4, fp, lsl #3
    1ca0:	6c910200 	lfmvs	f0, 4, [r1], {0}
    1ca4:	000d1721 	andeq	r1, sp, r1, lsr #14
    1ca8:	268b0100 	strcs	r0, [fp], r0, lsl #2
    1cac:	02000003 	andeq	r0, r0, #3
    1cb0:	4e256891 	mcrmi	8, 1, r6, cr5, cr1, {4}
    1cb4:	148c0100 	strne	r0, [ip], #256	; 0x100
    1cb8:	02000003 	andeq	r0, r0, #3
    1cbc:	5a257791 	bpl	95fb08 <ringBuffer+0x907e00>
    1cc0:	148d0100 	strne	r0, [sp], #256	; 0x100
    1cc4:	02000003 	andeq	r0, r0, #3
    1cc8:	43257691 			; <UNDEFINED> instruction: 0x43257691
    1ccc:	148e0100 	strne	r0, [lr], #256	; 0x100
    1cd0:	02000003 	andeq	r0, r0, #3
    1cd4:	56257591 			; <UNDEFINED> instruction: 0x56257591
    1cd8:	148f0100 	strne	r0, [pc], #256	; 1ce0 <_init-0xee40>
    1cdc:	02000003 	andeq	r0, r0, #3
    1ce0:	20007491 	mulcs	r0, r1, r4
    1ce4:	00000b7e 	andeq	r0, r0, lr, ror fp
    1ce8:	3f045601 	svccc	0x00045601
    1cec:	00a00004 	adceq	r0, r0, r4
    1cf0:	9c010000 	stcls	0, cr0, [r1], {-0}
    1cf4:	000008c3 	andeq	r0, r0, r3, asr #17
    1cf8:	000c1721 	andeq	r1, ip, r1, lsr #14
    1cfc:	26560100 	ldrbcs	r0, [r6], -r0, lsl #2
    1d00:	02000003 	andeq	r0, r0, #3
    1d04:	69225491 	stmdbvs	r2!, {r0, r4, r7, sl, ip, lr}
    1d08:	0100000d 	tsteq	r0, sp
    1d0c:	00032660 	andeq	r2, r3, r0, ror #12
    1d10:	6c910200 	lfmvs	f0, 4, [r1], {0}
    1d14:	000c8822 	andeq	r8, ip, r2, lsr #16
    1d18:	6a630100 	bvs	18c2120 <ringBuffer+0x186a418>
    1d1c:	02000003 	andeq	r0, r0, #3
    1d20:	26005c91 			; <UNDEFINED> instruction: 0x26005c91
    1d24:	00000c95 	muleq	r0, r5, ip
    1d28:	03264501 			; <UNDEFINED> instruction: 0x03264501
    1d2c:	3eec0000 	cdpcc	0, 14, cr0, cr12, cr0, {0}
    1d30:	00180004 	andseq	r0, r8, r4
    1d34:	9c010000 	stcls	0, cr0, [r1], {-0}
    1d38:	000008eb 	andeq	r0, r0, fp, ror #17
    1d3c:	000d6c22 	andeq	r6, sp, r2, lsr #24
    1d40:	26460100 	strbcs	r0, [r6], -r0, lsl #2
    1d44:	02000003 	andeq	r0, r0, #3
    1d48:	24007491 	strcs	r7, [r0], #-1169	; 0xfffffb6f
    1d4c:	00000c78 	andeq	r0, r0, r8, ror ip
    1d50:	03143d01 	tsteq	r4, #1, 26	; 0x40
    1d54:	3ea60000 	cdpcc	0, 10, cr0, cr6, cr0, {0}
    1d58:	00460004 	subeq	r0, r6, r4
    1d5c:	9c010000 	stcls	0, cr0, [r1], {-0}
    1d60:	00000963 	andeq	r0, r0, r3, ror #18
    1d64:	000d9a21 	andeq	r9, sp, r1, lsr #20
    1d68:	633d0100 	teqvs	sp, #0, 2
    1d6c:	02000009 	andeq	r0, r0, #9
    1d70:	ae276491 	mcrge	4, 1, r6, cr7, cr1, {4}
    1d74:	1800043e 	stmdane	r0, {r1, r2, r3, r4, r5, sl}
    1d78:	3c000000 	stccc	0, cr0, [r0], {-0}
    1d7c:	22000009 	andcs	r0, r0, #9
    1d80:	00000c2a 	andeq	r0, r0, sl, lsr #24
    1d84:	09693f01 	stmdbeq	r9!, {r0, r8, r9, sl, fp, ip, sp}^
    1d88:	91020000 	mrsls	r0, (UNDEF: 2)
    1d8c:	0c472274 	sfmeq	f2, 2, [r7], {116}	; 0x74
    1d90:	3f010000 	svccc	0x00010000
    1d94:	00000025 	andeq	r0, r0, r5, lsr #32
    1d98:	006c9102 	rsbeq	r9, ip, r2, lsl #2
    1d9c:	043ec623 	ldrteq	ip, [lr], #-1571	; 0xfffff9dd
    1da0:	00001800 	andeq	r1, r0, r0, lsl #16
    1da4:	0c2a2200 	sfmeq	f2, 4, [sl], #-0
    1da8:	40010000 	andmi	r0, r1, r0
    1dac:	00000969 	andeq	r0, r0, r9, ror #18
    1db0:	22709102 	rsbscs	r9, r0, #-2147483648	; 0x80000000
    1db4:	00000c47 	andeq	r0, r0, r7, asr #24
    1db8:	00254001 	eoreq	r4, r5, r1
    1dbc:	91020000 	mrsls	r0, (UNDEF: 2)
    1dc0:	06000068 	streq	r0, [r0], -r8, rrx
    1dc4:	0003be04 	andeq	fp, r3, r4, lsl #28
    1dc8:	25040600 	strcs	r0, [r4, #-1536]	; 0xfffffa00
    1dcc:	24000000 	strcs	r0, [r0], #-0
    1dd0:	00000ba3 	andeq	r0, r0, r3, lsr #23
    1dd4:	03143801 	tsteq	r4, #65536	; 0x10000
    1dd8:	3e540000 	cdpcc	0, 5, cr0, cr4, cr0, {0}
    1ddc:	00520004 	subseq	r0, r2, r4
    1de0:	9c010000 	stcls	0, cr0, [r1], {-0}
    1de4:	00000997 	muleq	r0, r7, r9
    1de8:	000d9a21 	andeq	r9, sp, r1, lsr #20
    1dec:	63380100 	teqvs	r8, #0, 2
    1df0:	02000009 	andeq	r0, r0, #9
    1df4:	28006c91 	stmdacs	r0, {r0, r4, r7, sl, fp, sp, lr}
    1df8:	00706f70 	rsbseq	r6, r0, r0, ror pc
    1dfc:	03142c01 	tsteq	r4, #256	; 0x100
    1e00:	3d860000 	stccc	0, cr0, [r6]
    1e04:	00ce0004 	sbceq	r0, lr, r4
    1e08:	9c010000 	stcls	0, cr0, [r1], {-0}
    1e0c:	00000a47 	andeq	r0, r0, r7, asr #20
    1e10:	000d9a21 	andeq	r9, sp, r1, lsr #20
    1e14:	632c0100 			; <UNDEFINED> instruction: 0x632c0100
    1e18:	02000009 	andeq	r0, r0, #9
    1e1c:	6c215491 	cfstrsvs	mvf5, [r1], #-580	; 0xfffffdbc
    1e20:	0100000d 	tsteq	r0, sp
    1e24:	000a472c 	andeq	r4, sl, ip, lsr #14
    1e28:	50910200 	addspl	r0, r1, r0, lsl #4
    1e2c:	043d9027 	ldrteq	r9, [sp], #-39	; 0xffffffd9
    1e30:	00001e00 	andeq	r1, r0, r0, lsl #28
    1e34:	0009f600 	andeq	pc, r9, r0, lsl #12
    1e38:	0d722200 	lfmeq	f2, 2, [r2, #-0]
    1e3c:	2d010000 	stccs	0, cr0, [r1, #-0]
    1e40:	00000969 	andeq	r0, r0, r9, ror #18
    1e44:	22749102 	rsbscs	r9, r4, #-2147483648	; 0x80000000
    1e48:	00000ae2 	andeq	r0, r0, r2, ror #21
    1e4c:	00252d01 	eoreq	r2, r5, r1, lsl #26
    1e50:	91020000 	mrsls	r0, (UNDEF: 2)
    1e54:	ae270064 	cdpge	0, 2, cr0, cr7, cr4, {3}
    1e58:	1e00043d 	cfmvdhrne	mvd0, r0
    1e5c:	20000000 	andcs	r0, r0, r0
    1e60:	2200000a 	andcs	r0, r0, #10
    1e64:	00000d72 	andeq	r0, r0, r2, ror sp
    1e68:	09692d01 	stmdbeq	r9!, {r0, r8, sl, fp, sp}^
    1e6c:	91020000 	mrsls	r0, (UNDEF: 2)
    1e70:	0ae22270 	beq	ff88a838 <__bss_end__+0xf5f9c234>
    1e74:	2d010000 	stccs	0, cr0, [r1, #-0]
    1e78:	00000025 	andeq	r0, r0, r5, lsr #32
    1e7c:	00609102 	rsbeq	r9, r0, r2, lsl #2
    1e80:	043df223 	ldrteq	pc, [sp], #-547	; 0xfffffddd	; <UNPREDICTABLE>
    1e84:	00005600 	andeq	r5, r0, r0, lsl #12
    1e88:	0c2a2200 	sfmeq	f2, 4, [sl], #-0
    1e8c:	32010000 	andcc	r0, r1, #0
    1e90:	00000969 	andeq	r0, r0, r9, ror #18
    1e94:	226c9102 	rsbcs	r9, ip, #-2147483648	; 0x80000000
    1e98:	00000c47 	andeq	r0, r0, r7, asr #24
    1e9c:	00253201 	eoreq	r3, r5, r1, lsl #4
    1ea0:	91020000 	mrsls	r0, (UNDEF: 2)
    1ea4:	0600005c 			; <UNDEFINED> instruction: 0x0600005c
    1ea8:	00036a04 	andeq	r6, r3, r4, lsl #20
    1eac:	0c3d2900 			; <UNDEFINED> instruction: 0x0c3d2900
    1eb0:	20010000 	andcs	r0, r1, r0
    1eb4:	00000314 	andeq	r0, r0, r4, lsl r3
    1eb8:	00043cc4 	andeq	r3, r4, r4, asr #25
    1ebc:	000000c2 	andeq	r0, r0, r2, asr #1
    1ec0:	9a219c01 	bls	868ecc <ringBuffer+0x8111c4>
    1ec4:	0100000d 	tsteq	r0, sp
    1ec8:	00096320 	andeq	r6, r9, r0, lsr #6
    1ecc:	4c910200 	lfmmi	f0, 4, [r1], {0}
    1ed0:	000d6c21 	andeq	r6, sp, r1, lsr #24
    1ed4:	6a200100 	bvs	8022dc <ringBuffer+0x7aa5d4>
    1ed8:	02000003 	andeq	r0, r0, #3
    1edc:	5a227491 	bpl	89f128 <ringBuffer+0x847420>
    1ee0:	0100000c 	tsteq	r0, ip
    1ee4:	00002521 	andeq	r2, r0, r1, lsr #10
    1ee8:	64910200 	ldrvs	r0, [r1], #512	; 0x200
    1eec:	043d1027 	ldrteq	r1, [sp], #-39	; 0xffffffd9
    1ef0:	00001e00 	andeq	r1, r0, r0, lsl #28
    1ef4:	000ab600 	andeq	fp, sl, r0, lsl #12
    1ef8:	0d722200 	lfmeq	f2, 2, [r2, #-0]
    1efc:	22010000 	andcs	r0, r1, #0
    1f00:	00000969 	andeq	r0, r0, r9, ror #18
    1f04:	22609102 	rsbcs	r9, r0, #-2147483648	; 0x80000000
    1f08:	00000ae2 	andeq	r0, r0, r2, ror #21
    1f0c:	00252201 	eoreq	r2, r5, r1, lsl #4
    1f10:	91020000 	mrsls	r0, (UNDEF: 2)
    1f14:	54230054 	strtpl	r0, [r3], #-84	; 0xffffffac
    1f18:	2000043d 	andcs	r0, r0, sp, lsr r4
    1f1c:	22000000 	andcs	r0, r0, #0
    1f20:	00000c2a 	andeq	r0, r0, sl, lsr #24
    1f24:	09692401 	stmdbeq	r9!, {r0, sl, sp}^
    1f28:	91020000 	mrsls	r0, (UNDEF: 2)
    1f2c:	0c47225c 	sfmeq	f2, 2, [r7], {92}	; 0x5c
    1f30:	24010000 	strcs	r0, [r1], #-0
    1f34:	00000025 	andeq	r0, r0, r5, lsr #32
    1f38:	00509102 	subseq	r9, r0, r2, lsl #2
    1f3c:	00910000 	addseq	r0, r1, r0
    1f40:	00020000 	andeq	r0, r2, r0
    1f44:	000006a5 	andeq	r0, r0, r5, lsr #13
    1f48:	0f8a0104 	svceq	0x008a0104
    1f4c:	71600000 	cmnvc	r0, r0
    1f50:	7ca40005 	stcvc	0, cr0, [r4], #20
    1f54:	2e2e0005 	cdpcs	0, 2, cr0, cr14, cr5, {0}
    1f58:	2f2e2e2f 	svccs	0x002e2e2f
    1f5c:	6d617274 	sfmvs	f7, 2, [r1, #-464]!	; 0xfffffe30
    1f60:	696c6f70 	stmdbvs	ip!, {r4, r5, r6, r8, r9, sl, fp, sp, lr}^
    1f64:	6c5f656e 	cfldr64vs	mvdx6, [pc], {110}	; 0x6e
    1f68:	742f6269 	strtvc	r6, [pc], #-617	; 1f70 <_init-0xebb0>
    1f6c:	706d6172 	rsbvc	r6, sp, r2, ror r1
    1f70:	6e696c6f 	cdpvs	12, 6, cr6, cr9, cr15, {3}
    1f74:	77665f65 	strbvc	r5, [r6, -r5, ror #30]!
    1f78:	2f00532e 	svccs	0x0000532e
    1f7c:	656d6f68 	strbvs	r6, [sp, #-3944]!	; 0xfffff098
    1f80:	7a727a2f 	bvc	1ca0844 <ringBuffer+0x1c48b3c>
    1f84:	37313530 			; <UNDEFINED> instruction: 0x37313530
    1f88:	7574732f 	ldrbvc	r7, [r4, #-815]!	; 0xfffffcd1
    1f8c:	632f7964 			; <UNDEFINED> instruction: 0x632f7964
    1f90:	6e696168 	powvsez	f6, f1, #0.0
    1f94:	7474615f 	ldrbtvc	r6, [r4], #-351	; 0xfffffea1
    1f98:	61747365 	cmnvs	r4, r5, ror #6
    1f9c:	6e6f6974 			; <UNDEFINED> instruction: 0x6e6f6974
    1fa0:	4952412f 	ldmdbmi	r2, {r0, r1, r2, r3, r5, r8, lr}^
    1fa4:	7a727a2d 	bvc	1ca0860 <ringBuffer+0x1c48b58>
    1fa8:	74616f2f 	strbtvc	r6, [r1], #-3887	; 0xfffff0d1
    1fac:	6176652d 	cmnvs	r6, sp, lsr #10
    1fb0:	7461756c 	strbtvc	r7, [r1], #-1388	; 0xfffffa94
    1fb4:	2f6e6f69 	svccs	0x006e6f69
    1fb8:	69727973 	ldmdbvs	r2!, {r0, r1, r4, r5, r6, r8, fp, ip, sp, lr}^
    1fbc:	2d65676e 	stclcs	7, cr6, [r5, #-440]!	; 0xfffffe48
    1fc0:	47006263 	strmi	r6, [r0, -r3, ror #4]
    1fc4:	4120554e 			; <UNDEFINED> instruction: 0x4120554e
    1fc8:	2e322053 	mrccs	0, 1, r2, cr2, cr3, {2}
    1fcc:	302e3732 	eorcc	r3, lr, r2, lsr r7
    1fd0:	8e800100 	rmfhis	f0, f0, f0
    1fd4:	02000000 	andeq	r0, r0, #0
    1fd8:	0006b900 	andeq	fp, r6, r0, lsl #18
    1fdc:	5b010400 	blpl	42fe4 <blake2s_compress+0x212c>
    1fe0:	6c000012 	stcvs	0, cr0, [r0], {18}
    1fe4:	64000465 	strvs	r0, [r0], #-1125	; 0xfffffb9b
    1fe8:	2e000466 	cdpcs	4, 0, cr0, cr0, cr6, {3}
    1fec:	2e2e2f2e 	cdpcs	15, 2, cr2, cr14, cr14, {1}
    1ff0:	6172742f 	cmnvs	r2, pc, lsr #8
    1ff4:	6c6f706d 	stclvs	0, cr7, [pc], #-436	; 1e48 <_init-0xecd8>
    1ff8:	5f656e69 	svcpl	0x00656e69
    1ffc:	2f62696c 	svccs	0x0062696c
    2000:	6d617274 	sfmvs	f7, 2, [r1, #-464]!	; 0xfffffe30
    2004:	696c6f70 	stmdbvs	ip!, {r4, r5, r6, r8, r9, sl, fp, sp, lr}^
    2008:	532e656e 			; <UNDEFINED> instruction: 0x532e656e
    200c:	6f682f00 	svcvs	0x00682f00
    2010:	7a2f656d 	bvc	bdb5cc <ringBuffer+0xb838c4>
    2014:	35307a72 	ldrcc	r7, [r0, #-2674]!	; 0xfffff58e
    2018:	732f3731 			; <UNDEFINED> instruction: 0x732f3731
    201c:	79647574 	stmdbvc	r4!, {r2, r4, r5, r6, r8, sl, ip, sp, lr}^
    2020:	6168632f 	cmnvs	r8, pc, lsr #6
    2024:	615f6e69 	cmpvs	pc, r9, ror #28
    2028:	73657474 	cmnvc	r5, #116, 8	; 0x74000000
    202c:	69746174 	ldmdbvs	r4!, {r2, r4, r5, r6, r8, sp, lr}^
    2030:	412f6e6f 			; <UNDEFINED> instruction: 0x412f6e6f
    2034:	7a2d4952 	bvc	b54584 <ringBuffer+0xafc87c>
    2038:	6f2f7a72 	svcvs	0x002f7a72
    203c:	652d7461 	strvs	r7, [sp, #-1121]!	; 0xfffffb9f
    2040:	756c6176 	strbvc	r6, [ip, #-374]!	; 0xfffffe8a
    2044:	6f697461 	svcvs	0x00697461
    2048:	79732f6e 	ldmdbvc	r3!, {r1, r2, r3, r5, r6, r8, r9, sl, fp, sp}^
    204c:	676e6972 			; <UNDEFINED> instruction: 0x676e6972
    2050:	62632d65 	rsbvs	r2, r3, #6464	; 0x1940
    2054:	554e4700 	strbpl	r4, [lr, #-1792]	; 0xfffff900
    2058:	20534120 	subscs	r4, r3, r0, lsr #2
    205c:	37322e32 			; <UNDEFINED> instruction: 0x37322e32
    2060:	0100302e 	tsteq	r0, lr, lsr #32
    2064:	000e5280 	andeq	r5, lr, r0, lsl #5
    2068:	cd000400 	cfstrsgt	mvf0, [r0, #-0]
    206c:	04000006 	streq	r0, [r0], #-6
    2070:	00103d01 	andseq	r3, r0, r1, lsl #26
    2074:	0eb41d00 	cdpeq	13, 11, cr1, cr4, cr0, {0}
    2078:	003b0000 	eorseq	r0, fp, r0
    207c:	499c0000 	ldmibmi	ip, {}	; <UNPREDICTABLE>
    2080:	07760004 	ldrbeq	r0, [r6, -r4]!
    2084:	12e90000 	rscne	r0, r9, #0
    2088:	01020000 	mrseq	r0, (UNDEF: 2)
    208c:	00086e08 	andeq	r6, r8, r8, lsl #28
    2090:	07020200 	streq	r0, [r2, -r0, lsl #4]
    2094:	00000753 	andeq	r0, r0, r3, asr r7
    2098:	83070402 	movwhi	r0, #29698	; 0x7402
    209c:	02000005 	andeq	r0, r0, #5
    20a0:	057e0704 	ldrbeq	r0, [lr, #-1796]!	; 0xfffff8fc
    20a4:	01020000 	mrseq	r0, (UNDEF: 2)
    20a8:	00087006 	andeq	r7, r8, r6
    20ac:	05020200 	streq	r0, [r2, #-512]	; 0xfffffe00
    20b0:	0000087c 	andeq	r0, r0, ip, ror r8
    20b4:	69050403 	stmdbvs	r5, {r0, r1, sl}
    20b8:	0200746e 	andeq	r7, r0, #1845493760	; 0x6e000000
    20bc:	05b90508 	ldreq	r0, [r9, #1288]!	; 0x508
    20c0:	08020000 	stmdaeq	r2, {}	; <UNPREDICTABLE>
    20c4:	00057907 	andeq	r7, r5, r7, lsl #18
    20c8:	06030400 	streq	r0, [r3], -r0, lsl #8
    20cc:	37020000 	strcc	r0, [r2, -r0]
    20d0:	00000056 	andeq	r0, r0, r6, asr r0
    20d4:	0004f804 	andeq	pc, r4, r4, lsl #16
    20d8:	7a830200 	bvc	fe0c28e0 <__bss_end__+0xf47d42dc>
    20dc:	02000000 	andeq	r0, r0, #0
    20e0:	05be0504 	ldreq	r0, [lr, #1284]!	; 0x504
    20e4:	3d040000 	stccc	0, cr0, [r4, #-0]
    20e8:	02000009 	andeq	r0, r0, #9
    20ec:	00006484 	andeq	r6, r0, r4, lsl #9
    20f0:	07040200 	streq	r0, [r4, -r0, lsl #4]
    20f4:	00000102 	andeq	r0, r0, r2, lsl #2
    20f8:	04060405 	streq	r0, [r6], #-1029	; 0xfffffbfb
    20fc:	0000009b 	muleq	r0, fp, r0
    2100:	77080102 	strvc	r0, [r8, -r2, lsl #2]
    2104:	07000008 	streq	r0, [r0, -r8]
    2108:	0000009b 	muleq	r0, fp, r0
    210c:	00053104 	andeq	r3, r5, r4, lsl #2
    2110:	33d80300 	bicscc	r0, r8, #0, 6
    2114:	08000000 	stmdaeq	r0, {}	; <UNPREDICTABLE>
    2118:	000010d9 	ldrdeq	r1, [r0], -r9
    211c:	be022204 	cdplt	2, 0, cr2, cr2, cr4, {0}
    2120:	06000000 	streq	r0, [r0], -r0
    2124:	00009504 	andeq	r9, r0, r4, lsl #10
    2128:	0f090900 	svceq	0x00090900
    212c:	39050000 	stmdbcc	r5, {}	; <UNPREDICTABLE>
    2130:	00000095 	muleq	r0, r5, r0
    2134:	00100609 	andseq	r0, r0, r9, lsl #12
    2138:	4f470500 	svcmi	0x00470500
    213c:	09000000 	stmdbeq	r0, {}	; <UNPREDICTABLE>
    2140:	000011fa 	strdeq	r1, [r0], -sl
    2144:	004f4c05 	subeq	r4, pc, r5, lsl #24
    2148:	9e090000 	cdpls	0, 0, cr0, cr9, cr0, {0}
    214c:	05000011 	streq	r0, [r0, #-17]	; 0xffffffef
    2150:	00004f50 	andeq	r4, r0, r0, asr pc
    2154:	04060a00 	streq	r0, [r6], #-2560	; 0xfffff600
    2158:	000000f0 	strdeq	r0, [r0], -r0	; <UNPREDICTABLE>
    215c:	0000f10b 	andeq	pc, r0, fp, lsl #2
    2160:	01170c00 	tsteq	r7, r0, lsl #24
    2164:	010c0000 	mrseq	r0, (UNDEF: 12)
    2168:	8c0d0000 	stchi	0, cr0, [sp], {-0}
    216c:	40000000 	andmi	r0, r0, r0
    2170:	00fc0700 	rscseq	r0, ip, r0, lsl #14
    2174:	04060000 	streq	r0, [r6], #-0
    2178:	000000a2 	andeq	r0, r0, r2, lsr #1
    217c:	00011107 	andeq	r1, r1, r7, lsl #2
    2180:	10200800 	eorne	r0, r0, r0, lsl #16
    2184:	2d060000 	stccs	0, cr0, [r6, #-0]
    2188:	00010c01 	andeq	r0, r1, r1, lsl #24
    218c:	10210800 	eorne	r0, r1, r0, lsl #16
    2190:	2e060000 	cdpcs	0, 0, cr0, cr6, cr0, {0}
    2194:	00010c01 	andeq	r0, r1, r1, lsl #24
    2198:	11220400 			; <UNDEFINED> instruction: 0x11220400
    219c:	25070000 	strcs	r0, [r7, #-0]
    21a0:	0000003a 	andeq	r0, r0, sl, lsr r0
    21a4:	00081604 	andeq	r1, r8, r4, lsl #12
    21a8:	4a300800 	bmi	c041b0 <ringBuffer+0xbac4a8>
    21ac:	0e000001 	cdpeq	0, 0, cr0, cr0, cr1, {0}
    21b0:	00000812 	andeq	r0, r0, r2, lsl r8
    21b4:	c7f10998 			; <UNDEFINED> instruction: 0xc7f10998
    21b8:	0f000002 	svceq	0x00000002
    21bc:	00000633 	andeq	r0, r0, r3, lsr r6
    21c0:	004ff209 	subeq	pc, pc, r9, lsl #4
    21c4:	0f000000 	svceq	0x00000000
    21c8:	00000500 	andeq	r0, r0, r0, lsl #10
    21cc:	0095f709 	addseq	pc, r5, r9, lsl #14
    21d0:	0f040000 	svceq	0x00040000
    21d4:	000005f6 	strdeq	r0, [r0], -r6
    21d8:	0095f809 	addseq	pc, r5, r9, lsl #16
    21dc:	0f080000 	svceq	0x00080000
    21e0:	00000947 	andeq	r0, r0, r7, asr #18
    21e4:	0095f909 	addseq	pc, r5, r9, lsl #18
    21e8:	0f0c0000 	svceq	0x000c0000
    21ec:	00000a29 	andeq	r0, r0, r9, lsr #20
    21f0:	0095fa09 	addseq	pc, r5, r9, lsl #20
    21f4:	0f100000 	svceq	0x00100000
    21f8:	00000725 	andeq	r0, r0, r5, lsr #14
    21fc:	0095fb09 	addseq	pc, r5, r9, lsl #22
    2200:	0f140000 	svceq	0x00140000
    2204:	000007e0 	andeq	r0, r0, r0, ror #15
    2208:	0095fc09 	addseq	pc, r5, r9, lsl #24
    220c:	0f180000 	svceq	0x00180000
    2210:	0000056c 	andeq	r0, r0, ip, ror #10
    2214:	0095fd09 	addseq	pc, r5, r9, lsl #26
    2218:	0f1c0000 	svceq	0x001c0000
    221c:	00000642 	andeq	r0, r0, r2, asr #12
    2220:	0095fe09 	addseq	pc, r5, r9, lsl #28
    2224:	10200000 	eorne	r0, r0, r0
    2228:	00000787 	andeq	r0, r0, r7, lsl #15
    222c:	95010009 	strls	r0, [r1, #-9]
    2230:	24000000 	strcs	r0, [r0], #-0
    2234:	0009c610 	andeq	ip, r9, r0, lsl r6
    2238:	01010900 	tsteq	r1, r0, lsl #18
    223c:	00000095 	muleq	r0, r5, r0
    2240:	09551028 	ldmdbeq	r5, {r3, r5, ip}^
    2244:	02090000 	andeq	r0, r9, #0
    2248:	00009501 	andeq	r9, r0, r1, lsl #10
    224c:	41102c00 	tstmi	r0, r0, lsl #24
    2250:	09000008 	stmdbeq	r0, {r3}
    2254:	02ff0104 	rscseq	r0, pc, #4, 2
    2258:	10300000 	eorsne	r0, r0, r0
    225c:	0000050d 	andeq	r0, r0, sp, lsl #10
    2260:	05010609 	streq	r0, [r1, #-1545]	; 0xfffff9f7
    2264:	34000003 	strcc	r0, [r0], #-3
    2268:	0005ee10 	andeq	lr, r5, r0, lsl lr
    226c:	01080900 	tsteq	r8, r0, lsl #18
    2270:	0000004f 	andeq	r0, r0, pc, asr #32
    2274:	079b1038 			; <UNDEFINED> instruction: 0x079b1038
    2278:	0c090000 	stceq	0, cr0, [r9], {-0}
    227c:	00004f01 	andeq	r4, r0, r1, lsl #30
    2280:	96103c00 	ldrls	r3, [r0], -r0, lsl #24
    2284:	09000006 	stmdbeq	r0, {r1, r2}
    2288:	006f010e 	rsbeq	r0, pc, lr, lsl #2
    228c:	10400000 	subne	r0, r0, r0
    2290:	0000064e 	andeq	r0, r0, lr, asr #12
    2294:	2c011209 	sfmcs	f1, 4, [r1], {9}
    2298:	44000000 	strmi	r0, [r0], #-0
    229c:	0008ae10 	andeq	sl, r8, r0, lsl lr
    22a0:	01130900 	tsteq	r3, r0, lsl #18
    22a4:	00000041 	andeq	r0, r0, r1, asr #32
    22a8:	05381046 	ldreq	r1, [r8, #-70]!	; 0xffffffba
    22ac:	14090000 	strne	r0, [r9], #-0
    22b0:	00030b01 	andeq	r0, r3, r1, lsl #22
    22b4:	95104700 	ldrls	r4, [r0, #-1792]	; 0xfffff900
    22b8:	09000007 	stmdbeq	r0, {r0, r1, r2}
    22bc:	031b0118 	tsteq	fp, #24, 2
    22c0:	10480000 	subne	r0, r8, r0
    22c4:	0000069a 	muleq	r0, sl, r6
    22c8:	81012109 	tsthi	r1, r9, lsl #2
    22cc:	50000000 	andpl	r0, r0, r0
    22d0:	00096c10 	andeq	r6, r9, r0, lsl ip
    22d4:	01290900 			; <UNDEFINED> instruction: 0x01290900
    22d8:	00000093 	muleq	r0, r3, r0
    22dc:	09731058 	ldmdbeq	r3!, {r3, r4, r6, ip}^
    22e0:	2a090000 	bcs	2422e8 <ringBuffer+0x1ea5e0>
    22e4:	00009301 	andeq	r9, r0, r1, lsl #6
    22e8:	7a105c00 	bvc	4192f0 <ringBuffer+0x3c15e8>
    22ec:	09000009 	stmdbeq	r0, {r0, r3}
    22f0:	0093012b 	addseq	r0, r3, fp, lsr #2
    22f4:	10600000 	rsbne	r0, r0, r0
    22f8:	00000981 	andeq	r0, r0, r1, lsl #19
    22fc:	93012c09 	movwls	r2, #7177	; 0x1c09
    2300:	64000000 	strvs	r0, [r0], #-0
    2304:	00098810 	andeq	r8, r9, r0, lsl r8
    2308:	012e0900 			; <UNDEFINED> instruction: 0x012e0900
    230c:	000000a7 	andeq	r0, r0, r7, lsr #1
    2310:	07a31068 	streq	r1, [r3, r8, rrx]!
    2314:	2f090000 	svccs	0x00090000
    2318:	00004f01 	andeq	r4, r0, r1, lsl #30
    231c:	8f106c00 	svchi	0x00106c00
    2320:	09000009 	stmdbeq	r0, {r0, r3}
    2324:	03210131 			; <UNDEFINED> instruction: 0x03210131
    2328:	00700000 	rsbseq	r0, r0, r0
    232c:	00080711 	andeq	r0, r8, r1, lsl r7
    2330:	0e960900 	vfnmseq.f16	s0, s12, s0	; <UNPREDICTABLE>
    2334:	000006d4 	ldrdeq	r0, [r0], -r4
    2338:	ff9c090c 			; <UNDEFINED> instruction: 0xff9c090c
    233c:	0f000002 	svceq	0x00000002
    2340:	00000937 	andeq	r0, r0, r7, lsr r9
    2344:	02ff9d09 	rscseq	r9, pc, #576	; 0x240
    2348:	0f000000 	svceq	0x00000000
    234c:	0000074d 	andeq	r0, r0, sp, asr #14
    2350:	03059e09 	movweq	r9, #24073	; 0x5e09
    2354:	0f040000 	svceq	0x00040000
    2358:	00000830 	andeq	r0, r0, r0, lsr r8
    235c:	004fa209 	subeq	sl, pc, r9, lsl #4
    2360:	00080000 	andeq	r0, r8, r0
    2364:	02ce0406 	sbceq	r0, lr, #100663296	; 0x6000000
    2368:	04060000 	streq	r0, [r6], #-0
    236c:	0000014a 	andeq	r0, r0, sl, asr #2
    2370:	00009b0c 	andeq	r9, r0, ip, lsl #22
    2374:	00031b00 	andeq	r1, r3, r0, lsl #22
    2378:	008c0d00 	addeq	r0, ip, r0, lsl #26
    237c:	00000000 	andeq	r0, r0, r0
    2380:	02c70406 	sbceq	r0, r7, #100663296	; 0x6000000
    2384:	9b0c0000 	blls	30238c <ringBuffer+0x2aa684>
    2388:	31000000 	mrscc	r0, (UNDEF: 0)
    238c:	0d000003 	stceq	0, cr0, [r0, #-12]
    2390:	0000008c 	andeq	r0, r0, ip, lsl #1
    2394:	17120027 	ldrne	r0, [r2, -r7, lsr #32]
    2398:	08000007 	stmdaeq	r0, {r0, r1, r2}
    239c:	000007b0 			; <UNDEFINED> instruction: 0x000007b0
    23a0:	31013b09 	tstcc	r1, r9, lsl #22
    23a4:	08000003 	stmdaeq	r0, {r0, r1}
    23a8:	000008bd 			; <UNDEFINED> instruction: 0x000008bd
    23ac:	31013c09 	tstcc	r1, r9, lsl #24
    23b0:	08000003 	stmdaeq	r0, {r0, r1}
    23b4:	0000055c 	andeq	r0, r0, ip, asr r5
    23b8:	31013d09 	tstcc	r1, r9, lsl #26
    23bc:	09000003 	stmdbeq	r0, {r0, r1}
    23c0:	000006df 	ldrdeq	r0, [r0], -pc	; <UNPREDICTABLE>
    23c4:	0305a808 	movweq	sl, #22536	; 0x5808
    23c8:	a9090000 	stmdbge	r9, {}	; <UNPREDICTABLE>
    23cc:	08000007 	stmdaeq	r0, {r0, r1, r2}
    23d0:	000305a9 	andeq	r0, r3, r9, lsr #11
    23d4:	09980900 	ldmibeq	r8, {r8, fp}
    23d8:	aa080000 	bge	2023e0 <ringBuffer+0x1aa6d8>
    23dc:	00000305 	andeq	r0, r0, r5, lsl #6
    23e0:	00074409 	andeq	r4, r7, r9, lsl #8
    23e4:	4f1a0a00 	svcmi	0x001a0a00
    23e8:	0c000000 	stceq	0, cr0, [r0], {-0}
    23ec:	00000117 	andeq	r0, r0, r7, lsl r1
    23f0:	00000391 	muleq	r0, r1, r3
    23f4:	86070013 			; <UNDEFINED> instruction: 0x86070013
    23f8:	09000003 	stmdbeq	r0, {r0, r1}
    23fc:	00000835 	andeq	r0, r0, r5, lsr r8
    2400:	03911b0a 	orrseq	r1, r1, #10240	; 0x2800
    2404:	d4040000 	strle	r0, [r4], #-0
    2408:	0300000f 	movweq	r0, #15
    240c:	00004f95 	muleq	r0, r5, pc	; <UNPREDICTABLE>
    2410:	04080200 	streq	r0, [r8], #-512	; 0xfffffe00
    2414:	000007bf 			; <UNDEFINED> instruction: 0x000007bf
    2418:	00009314 	andeq	r9, r0, r4, lsl r3
    241c:	0003c200 	andeq	ip, r3, r0, lsl #4
    2420:	03a11500 			; <UNDEFINED> instruction: 0x03a11500
    2424:	09000000 	stmdbeq	r0, {}	; <UNPREDICTABLE>
    2428:	000011e8 	andeq	r1, r0, r8, ror #3
    242c:	03cd470b 	biceq	r4, sp, #2883584	; 0x2c0000
    2430:	04060000 	streq	r0, [r6], #-0
    2434:	000003b3 			; <UNDEFINED> instruction: 0x000003b3
    2438:	00128f09 	andseq	r8, r2, r9, lsl #30
    243c:	f7930b00 			; <UNDEFINED> instruction: 0xf7930b00
    2440:	16000000 	strne	r0, [r0], -r0
    2444:	000003ee 	andeq	r0, r0, lr, ror #7
    2448:	00009315 	andeq	r9, r0, r5, lsl r3
    244c:	03ee1500 	mvneq	r1, #0, 10
    2450:	06000000 	streq	r0, [r0], -r0
    2454:	0003f404 	andeq	pc, r3, r4, lsl #8
    2458:	35091700 	strcc	r1, [r9, #-1792]	; 0xfffff900
    245c:	0b00000f 	bleq	24a0 <_init-0xe680>
    2460:	00040696 	muleq	r4, r6, r6
    2464:	de040600 	cfmadd32le	mvax0, mvfx0, mvfx4, mvfx0
    2468:	0b000003 	bleq	247c <_init-0xe6a4>
    246c:	00000400 	andeq	r0, r0, r0, lsl #8
    2470:	00009314 	andeq	r9, r0, r4, lsl r3
    2474:	00041f00 	andeq	r1, r4, r0, lsl #30
    2478:	00a71500 	adceq	r1, r7, r0, lsl #10
    247c:	ee150000 	cdp	0, 1, cr0, cr5, cr0, {0}
    2480:	00000003 	andeq	r0, r0, r3
    2484:	000fef09 	andeq	lr, pc, r9, lsl #30
    2488:	30990b00 	addscc	r0, r9, r0, lsl #22
    248c:	06000004 	streq	r0, [r0], -r4
    2490:	00040b04 	andeq	r0, r4, r4, lsl #22
    2494:	042a0b00 	strteq	r0, [sl], #-2816	; 0xfffff500
    2498:	93140000 	tstls	r4, #0
    249c:	4e000000 	cdpmi	0, 0, cr0, cr0, cr0, {0}
    24a0:	15000004 	strne	r0, [r0, #-4]
    24a4:	00000093 	muleq	r0, r3, r0
    24a8:	0000a715 	andeq	sl, r0, r5, lsl r7
    24ac:	03ee1500 	mvneq	r1, #0, 10
    24b0:	09000000 	stmdbeq	r0, {}	; <UNPREDICTABLE>
    24b4:	00001165 	andeq	r1, r0, r5, ror #2
    24b8:	045f9c0b 	ldrbeq	r9, [pc], #-3083	; 24c0 <_init-0xe660>
    24bc:	04060000 	streq	r0, [r6], #-0
    24c0:	00000435 	andeq	r0, r0, r5, lsr r4
    24c4:	0004590b 	andeq	r5, r4, fp, lsl #18
    24c8:	00931400 	addseq	r1, r3, r0, lsl #8
    24cc:	047d0000 	ldrbteq	r0, [sp], #-0
    24d0:	a7150000 	ldrge	r0, [r5, -r0]
    24d4:	15000000 	strne	r0, [r0, #-0]
    24d8:	000000a7 	andeq	r0, r0, r7, lsr #1
    24dc:	0003ee15 	andeq	lr, r3, r5, lsl lr
    24e0:	4b090000 	blmi	2424e8 <ringBuffer+0x1ea7e0>
    24e4:	0b000011 	bleq	2530 <_init-0xe5f0>
    24e8:	00048ea0 	andeq	r8, r4, r0, lsr #29
    24ec:	64040600 	strvs	r0, [r4], #-1536	; 0xfffffa00
    24f0:	0b000004 	bleq	2508 <_init-0xe618>
    24f4:	00000488 	andeq	r0, r0, r8, lsl #9
    24f8:	0011be09 	andseq	fp, r1, r9, lsl #28
    24fc:	f7a40b00 			; <UNDEFINED> instruction: 0xf7a40b00
    2500:	0c000000 	stceq	0, cr0, [r0], {-0}
    2504:	00000095 	muleq	r0, r5, r0
    2508:	000004ae 	andeq	r0, r0, lr, lsr #9
    250c:	00008c0d 	andeq	r8, r0, sp, lsl #24
    2510:	08000100 	stmdaeq	r0, {r8}
    2514:	000012b9 			; <UNDEFINED> instruction: 0x000012b9
    2518:	9e011a0c 	vmlals.f32	s2, s2, s24
    251c:	08000004 	stmdaeq	r0, {r2}
    2520:	00001193 	muleq	r0, r3, r1
    2524:	4f011b0c 	svcmi	0x00011b0c
    2528:	08000000 	stmdaeq	r0, {}	; <UNPREDICTABLE>
    252c:	00000e64 	andeq	r0, r0, r4, ror #28
    2530:	7a011c0c 	bvc	49568 <__FRAME_END__+0x2700>
    2534:	08000000 	stmdaeq	r0, {}	; <UNPREDICTABLE>
    2538:	000012bb 			; <UNDEFINED> instruction: 0x000012bb
    253c:	9e01210c 	adflss	f2, f1, #4.0
    2540:	08000004 	stmdaeq	r0, {r2}
    2544:	00001195 	muleq	r0, r5, r1
    2548:	4f01290c 	svcmi	0x0001290c
    254c:	08000000 	stmdaeq	r0, {}	; <UNPREDICTABLE>
    2550:	00000e66 	andeq	r0, r0, r6, ror #28
    2554:	7a012a0c 	bvc	4cd8c <__FRAME_END__+0x5f24>
    2558:	04000000 	streq	r0, [r0], #-0
    255c:	000009be 			; <UNDEFINED> instruction: 0x000009be
    2560:	0025300d 	eoreq	r3, r5, sp
    2564:	67040000 	strvs	r0, [r4, -r0]
    2568:	0d000006 	stceq	0, cr0, [r0, #-24]	; 0xffffffe8
    256c:	00002c31 	andeq	r2, r0, r1, lsr ip
    2570:	08e90400 	stmiaeq	r9!, {sl}^
    2574:	330d0000 	movwcc	r0, #53248	; 0xd000
    2578:	00000033 	andeq	r0, r0, r3, lsr r0
    257c:	000df104 	andeq	pc, sp, r4, lsl #2
    2580:	5d3a0d00 	ldcpl	13, cr0, [sl, #-0]
    2584:	04000000 	streq	r0, [r0], #-0
    2588:	000012c2 	andeq	r1, r0, r2, asr #5
    258c:	050cf80e 	streq	pc, [ip, #-2062]	; 0xfffff7f2
    2590:	08180000 	ldmdaeq	r8, {}	; <UNPREDICTABLE>
    2594:	054ffe0e 	strbeq	pc, [pc, #-3598]	; 178e <_init-0xf392>	; <UNPREDICTABLE>
    2598:	66190000 	ldrvs	r0, [r9], -r0
    259c:	000e0064 	andeq	r0, lr, r4, rrx
    25a0:	00004f01 	andeq	r4, r0, r1, lsl #30
    25a4:	cc100000 	ldcgt	0, cr0, [r0], {-0}
    25a8:	0e00000f 	cdpeq	0, 0, cr0, cr0, cr15, {0}
    25ac:	054f0101 	strbeq	r0, [pc, #-257]	; 24b3 <_init-0xe66d>
    25b0:	00040000 	andeq	r0, r4, r0
    25b4:	e9020102 	stmdb	r2, {r1, r8}
    25b8:	1a000001 	bne	25c4 <_init-0xe55c>
    25bc:	00000de4 	andeq	r0, r0, r4, ror #27
    25c0:	2d01020e 	sfmcs	f0, 4, [r1, #-56]	; 0xffffffc8
    25c4:	1b000005 	blne	25e0 <_init-0xe540>
    25c8:	01090e10 	tsteq	r9, r0, lsl lr
    25cc:	000005a0 	andeq	r0, r0, r0, lsr #11
    25d0:	00125810 	andseq	r5, r2, r0, lsl r8
    25d4:	010a0e00 	tsteq	sl, r0, lsl #28
    25d8:	0000050c 	andeq	r0, r0, ip, lsl #10
    25dc:	12501000 	subsne	r1, r0, #0
    25e0:	0b0e0000 	bleq	3825e8 <ringBuffer+0x32a8e0>
    25e4:	00050101 	andeq	r0, r5, r1, lsl #2
    25e8:	53100400 	tstpl	r0, #0, 8
    25ec:	0e00000e 	cdpeq	0, 0, cr0, cr0, cr14, {0}
    25f0:	0501010c 	streq	r0, [r1, #-268]	; 0xfffffef4
    25f4:	10060000 	andne	r0, r6, r0
    25f8:	00000dcd 	andeq	r0, r0, sp, asr #27
    25fc:	a0010d0e 	andge	r0, r1, lr, lsl #26
    2600:	08000005 	stmdaeq	r0, {r0, r2}
    2604:	04f60c00 	ldrbteq	r0, [r6], #3072	; 0xc00
    2608:	05b00000 	ldreq	r0, [r0, #0]!
    260c:	8c0d0000 	stchi	0, cr0, [sp], {-0}
    2610:	07000000 	streq	r0, [r0, -r0]
    2614:	0ed91a00 	vfnmseq.f32	s3, s18, s0
    2618:	0e0e0000 	cdpeq	0, 0, cr0, cr14, cr0, {0}
    261c:	00056201 	andeq	r6, r5, r1, lsl #4
    2620:	0e201b00 	vmuleq.f64	d1, d0, d0
    2624:	062d0120 	strteq	r0, [sp], -r0, lsr #2
    2628:	08100000 	ldmdaeq	r0, {}	; <UNPREDICTABLE>
    262c:	0e000012 	mcreq	0, 0, r0, cr0, cr2, {0}
    2630:	00930121 	addseq	r0, r3, r1, lsr #2
    2634:	10000000 	andne	r0, r0, r0
    2638:	0000111d 	andeq	r1, r0, sp, lsl r1
    263c:	a701220e 	strge	r2, [r1, -lr, lsl #4]
    2640:	04000000 	streq	r0, [r0], #-0
    2644:	00063410 	andeq	r3, r6, r0, lsl r4
    2648:	01230e00 			; <UNDEFINED> instruction: 0x01230e00
    264c:	0000050c 	andeq	r0, r0, ip, lsl #10
    2650:	64691908 	strbtvs	r1, [r9], #-2312	; 0xfffff6f8
    2654:	01270e00 			; <UNDEFINED> instruction: 0x01270e00
    2658:	0000004f 	andeq	r0, r0, pc, asr #32
    265c:	1115100c 	tstne	r5, ip
    2660:	280e0000 	stmdacs	lr, {}	; <UNPREDICTABLE>
    2664:	0000a701 	andeq	sl, r0, r1, lsl #14
    2668:	01101000 	tsteq	r0, r0
    266c:	0e000012 	mcreq	0, 0, r0, cr0, cr2, {0}
    2670:	00930129 	addseq	r0, r3, r9, lsr #2
    2674:	10140000 	andsne	r0, r4, r0
    2678:	00000f75 	andeq	r0, r0, r5, ror pc
    267c:	4f012a0e 	svcmi	0x00012a0e
    2680:	18000000 	stmdane	r0, {}	; <UNPREDICTABLE>
    2684:	000fde10 	andeq	sp, pc, r0, lsl lr	; <UNPREDICTABLE>
    2688:	012b0e00 			; <UNDEFINED> instruction: 0x012b0e00
    268c:	0000054f 	andeq	r0, r0, pc, asr #10
    2690:	f41a001c 			; <UNDEFINED> instruction: 0xf41a001c
    2694:	0e000010 	mcreq	0, 0, r0, cr0, cr0, {0}
    2698:	05bc012c 	ldreq	r0, [ip, #300]!	; 0x12c
    269c:	081b0000 	ldmdaeq	fp, {}	; <UNPREDICTABLE>
    26a0:	5d013a0e 	vstrpl	s6, [r1, #-56]	; 0xffffffc8
    26a4:	10000006 	andne	r0, r0, r6
    26a8:	00001208 	andeq	r1, r0, r8, lsl #4
    26ac:	93013b0e 	movwls	r3, #6926	; 0x1b0e
    26b0:	00000000 	andeq	r0, r0, r0
    26b4:	00111d10 	andseq	r1, r1, r0, lsl sp
    26b8:	013c0e00 	teqeq	ip, r0, lsl #28
    26bc:	000000a7 	andeq	r0, r0, r7, lsr #1
    26c0:	371a0004 	ldrcc	r0, [sl, -r4]
    26c4:	0e000012 	mcreq	0, 0, r0, cr0, cr2, {0}
    26c8:	0639013d 			; <UNDEFINED> instruction: 0x0639013d
    26cc:	0c1b0000 	ldceq	0, cr0, [fp], {-0}
    26d0:	9a014e0e 	bls	55f10 <__FRAME_END__+0xf0a8>
    26d4:	10000006 	andne	r0, r0, r6
    26d8:	00000e9d 	muleq	r0, sp, lr
    26dc:	9a014f0e 	bls	5631c <__FRAME_END__+0xf4b4>
    26e0:	00000006 	andeq	r0, r0, r6
    26e4:	00111d10 	andseq	r1, r1, r0, lsl sp
    26e8:	01500e00 	cmpeq	r0, r0, lsl #28
    26ec:	000000a7 	andeq	r0, r0, r7, lsr #1
    26f0:	069b1004 	ldreq	r1, [fp], r4
    26f4:	510e0000 	mrspl	r0, (UNDEF: 14)
    26f8:	0000a701 	andeq	sl, r0, r1, lsl #14
    26fc:	06000800 	streq	r0, [r0], -r0, lsl #16
    2700:	00062d04 	andeq	r2, r6, r4, lsl #26
    2704:	12601a00 	rsbne	r1, r0, #0, 20
    2708:	520e0000 	andpl	r0, lr, #0
    270c:	00066901 	andeq	r6, r6, r1, lsl #18
    2710:	0e081b00 	vmlaeq.f64	d1, d8, d0
    2714:	06cc015e 			; <UNDEFINED> instruction: 0x06cc015e
    2718:	61190000 	tstvs	r9, r0
    271c:	015f0e00 	cmpeq	pc, r0, lsl #28
    2720:	0000050c 	andeq	r0, r0, ip, lsl #10
    2724:	00621900 	rsbeq	r1, r2, r0, lsl #18
    2728:	0c01600e 	stceq	0, cr6, [r1], {14}
    272c:	04000005 	streq	r0, [r0], #-5
    2730:	0f5a1a00 	svceq	0x005a1a00
    2734:	610e0000 	mrsvs	r0, (UNDEF: 14)
    2738:	0006ac01 	andeq	sl, r6, r1, lsl #24
    273c:	0e0c1c00 	cdpeq	12, 0, cr1, cr12, cr0, {0}
    2740:	07060171 	smlsdxeq	r6, r1, r1, r0
    2744:	b21d0000 	andslt	r0, sp, #0
    2748:	0e000012 	mcreq	0, 0, r0, cr0, cr2, {0}
    274c:	065d0172 			; <UNDEFINED> instruction: 0x065d0172
    2750:	dd1d0000 	ldcle	0, cr0, [sp, #-0]
    2754:	0e00000d 	cdpeq	0, 0, cr0, cr0, cr13, {0}
    2758:	06a00173 			; <UNDEFINED> instruction: 0x06a00173
    275c:	6c1d0000 	ldcvs	0, cr0, [sp], {-0}
    2760:	0e00000d 	cdpeq	0, 0, cr0, cr0, cr13, {0}
    2764:	06cc0174 			; <UNDEFINED> instruction: 0x06cc0174
    2768:	1a000000 	bne	2770 <_init-0xe3b0>
    276c:	00001106 	andeq	r1, r0, r6, lsl #2
    2770:	d801750e 	stmdale	r1, {r1, r2, r3, r8, sl, ip, sp, lr}
    2774:	1b000006 	blne	2794 <_init-0xe38c>
    2778:	017b0e08 	cmneq	fp, r8, lsl #28
    277c:	00000736 	andeq	r0, r0, r6, lsr r7
    2780:	78746319 	ldmdavc	r4!, {r0, r3, r4, r8, r9, sp, lr}^
    2784:	017d0e00 	cmneq	sp, r0, lsl #28
    2788:	00000736 	andeq	r0, r0, r6, lsr r7
    278c:	0e481000 	cdpeq	0, 4, cr1, cr8, cr0, {0}
    2790:	7e0e0000 	cdpvc	0, 0, cr0, cr14, cr0, {0}
    2794:	00050c01 	andeq	r0, r5, r1, lsl #24
    2798:	06000400 	streq	r0, [r0], -r0, lsl #8
    279c:	00055604 	andeq	r5, r5, r4, lsl #12
    27a0:	11db1a00 	bicsne	r1, fp, r0, lsl #20
    27a4:	7f0e0000 	svcvc	0x000e0000
    27a8:	00071201 	andeq	r1, r7, r1, lsl #4
    27ac:	0e3c1b00 	vaddeq.f64	d1, d12, d0
    27b0:	0786018f 	streq	r0, [r6, pc, lsl #3]
    27b4:	36100000 	ldrcc	r0, [r0], -r0
    27b8:	0e00000e 	cdpeq	0, 0, cr0, cr0, cr14, {0}
    27bc:	050c0190 	streq	r0, [ip, #-400]	; 0xfffffe70
    27c0:	10000000 	andne	r0, r0, r0
    27c4:	00000e92 	muleq	r0, r2, lr
    27c8:	0c01910e 	stfeqd	f1, [r1], {14}
    27cc:	04000005 	streq	r0, [r0], #-5
    27d0:	0011d410 	andseq	sp, r1, r0, lsl r4
    27d4:	01920e00 	orrseq	r0, r2, r0, lsl #28
    27d8:	00000786 	andeq	r0, r0, r6, lsl #15
    27dc:	10c61008 	sbcne	r1, r6, r8
    27e0:	940e0000 	strls	r0, [lr], #-0
    27e4:	00079601 	andeq	r9, r7, r1, lsl #12
    27e8:	0c003800 	stceq	8, cr3, [r0], {-0}
    27ec:	00000706 	andeq	r0, r0, r6, lsl #14
    27f0:	00000796 	muleq	r0, r6, r7
    27f4:	00008c0d 	andeq	r8, r0, sp, lsl #24
    27f8:	06000300 	streq	r0, [r0], -r0, lsl #6
    27fc:	00073c04 	andeq	r3, r7, r4, lsl #24
    2800:	0f9d1a00 	svceq	0x009d1a00
    2804:	950e0000 	strls	r0, [lr, #-0]
    2808:	00074801 	andeq	r4, r7, r1, lsl #16
    280c:	09fa1e00 	ldmibeq	sl!, {r9, sl, fp, ip}^
    2810:	33040000 	movwcc	r0, #16384	; 0x4000
    2814:	0f000000 	svceq	0x00000000
    2818:	0007d71f 	andeq	sp, r7, pc, lsl r7
    281c:	07661f00 	strbeq	r1, [r6, -r0, lsl #30]!
    2820:	1f400000 	svcne	0x00400000
    2824:	00000733 	andeq	r0, r0, r3, lsr r7
    2828:	06e51f20 	strbteq	r1, [r5], r0, lsr #30
    282c:	1f200000 	svcne	0x00200000
    2830:	00000851 	andeq	r0, r0, r1, asr r8
    2834:	09051f08 	stmdbeq	r5, {r3, r8, r9, sl, fp, ip}
    2838:	00080000 	andeq	r0, r8, r0
    283c:	0005dd1e 	andeq	sp, r5, lr, lsl sp
    2840:	00330400 	eorseq	r0, r3, r0, lsl #8
    2844:	280f0000 	stmdacs	pc, {}	; <UNPREDICTABLE>
    2848:	00000806 	andeq	r0, r0, r6, lsl #16
    284c:	0008861f 	andeq	r8, r8, pc, lsl r6
    2850:	d11f8000 	tstle	pc, r0
    2854:	4000000a 	andmi	r0, r0, sl
    2858:	00099f1f 	andeq	r9, r9, pc, lsl pc
    285c:	211f4000 	tstcs	pc, r0
    2860:	10000006 	andne	r0, r0, r6
    2864:	0009e41f 	andeq	lr, r9, pc, lsl r4
    2868:	0e001000 	cdpeq	0, 0, cr1, cr0, cr0, {0}
    286c:	00000521 	andeq	r0, r0, r1, lsr #10
    2870:	61310f7c 	teqvs	r1, ip, ror pc
    2874:	20000008 	andcs	r0, r0, r8
    2878:	330f0068 	movwcc	r0, #61544	; 0xf068
    287c:	00000861 	andeq	r0, r0, r1, ror #16
    2880:	00742000 	rsbseq	r2, r4, r0
    2884:	0871340f 	ldmdaeq	r1!, {r0, r1, r2, r3, sl, ip, sp}^
    2888:	20200000 	eorcs	r0, r0, r0
    288c:	350f0066 	strcc	r0, [pc, #-102]	; 282e <_init-0xe2f2>
    2890:	00000871 	andeq	r0, r0, r1, ror r8
    2894:	75622028 	strbvc	r2, [r2, #-40]!	; 0xffffffd8
    2898:	360f0066 	strcc	r0, [pc], -r6, rrx
    289c:	00000881 	andeq	r0, r0, r1, lsl #17
    28a0:	08cd0f30 	stmiaeq	sp, {r4, r5, r8, r9, sl, fp}^
    28a4:	370f0000 	strcc	r0, [pc, -r0]
    28a8:	000000a7 	andeq	r0, r0, r7, lsr #1
    28ac:	0a0b0f70 	beq	2c6674 <ringBuffer+0x26e96c>
    28b0:	380f0000 	stmdacc	pc, {}	; <UNPREDICTABLE>
    28b4:	000000a7 	andeq	r0, r0, r7, lsr #1
    28b8:	09620f74 	stmdbeq	r2!, {r2, r4, r5, r6, r8, r9, sl, fp}^
    28bc:	390f0000 	stmdbcc	pc, {}	; <UNPREDICTABLE>
    28c0:	000004f6 	strdeq	r0, [r0], -r6
    28c4:	0c0c0078 	stceq	0, cr0, [ip], {120}	; 0x78
    28c8:	71000005 	tstvc	r0, r5
    28cc:	0d000008 	stceq	0, cr0, [r0, #-32]	; 0xffffffe0
    28d0:	0000008c 	andeq	r0, r0, ip, lsl #1
    28d4:	0c0c0007 	stceq	0, cr0, [ip], {7}
    28d8:	81000005 	tsthi	r0, r5
    28dc:	0d000008 	stceq	0, cr0, [r0, #-32]	; 0xffffffe0
    28e0:	0000008c 	andeq	r0, r0, ip, lsl #1
    28e4:	f60c0001 			; <UNDEFINED> instruction: 0xf60c0001
    28e8:	91000004 	tstls	r0, r4
    28ec:	0d000008 	stceq	0, cr0, [r0, #-32]	; 0xffffffe0
    28f0:	0000008c 	andeq	r0, r0, ip, lsl #1
    28f4:	d604003f 			; <UNDEFINED> instruction: 0xd604003f
    28f8:	0f000009 	svceq	0x00000009
    28fc:	0008063a 	andeq	r0, r8, sl, lsr r6
    2900:	01101800 	tsteq	r0, r0, lsl #16
    2904:	0008d517 	andeq	sp, r8, r7, lsl r5
    2908:	0d920f00 	ldceq	15, cr0, [r2]
    290c:	18010000 	stmdane	r1, {}	; <UNPREDICTABLE>
    2910:	0000050c 	andeq	r0, r0, ip, lsl #10
    2914:	0be00f00 	bleq	ff80651c <__bss_end__+0xf5f17f18>
    2918:	19010000 	stmdbne	r1, {}	; <UNPREDICTABLE>
    291c:	0000050c 	andeq	r0, r0, ip, lsl #10
    2920:	0c420f04 	mcrreq	15, 0, r0, r2, cr4
    2924:	1a010000 	bne	4292c <blake2s_compress+0x1a74>
    2928:	0000050c 	andeq	r0, r0, ip, lsl #10
    292c:	0ca80f08 	stceq	15, cr0, [r8], #32
    2930:	1b010000 	blne	42938 <blake2s_compress+0x1a80>
    2934:	000004f6 	strdeq	r0, [r0], -r6
    2938:	8d04000c 	stchi	0, cr0, [r4, #-48]	; 0xffffffd0
    293c:	0100000c 	tsteq	r0, ip
    2940:	00089c1c 	andeq	r9, r8, ip, lsl ip
    2944:	68082100 	stmdavs	r8, {r8, sp}
    2948:	1e010989 	vmlane.f16	s0, s3, s18	; <UNPREDICTABLE>
    294c:	00000916 	andeq	r0, r0, r6, lsl r9
    2950:	0012080f 	andseq	r0, r2, pc, lsl #16
    2954:	161f0100 	ldrne	r0, [pc], -r0, lsl #2
    2958:	00000009 	andeq	r0, r0, r9
    295c:	000c5f22 	andeq	r5, ip, r2, lsr #30
    2960:	a7200100 	strge	r0, [r0, -r0, lsl #2]!
    2964:	00000000 	andeq	r0, r0, r0
    2968:	22098968 	andcs	r8, r9, #104, 18	; 0x1a0000
    296c:	00000d36 	andeq	r0, r0, r6, lsr sp
    2970:	00a72101 	adceq	r2, r7, r1, lsl #2
    2974:	68040000 	stmdavs	r4, {}	; <UNPREDICTABLE>
    2978:	0c000989 			; <UNDEFINED> instruction: 0x0c000989
    297c:	000008d5 	ldrdeq	r0, [r0], -r5
    2980:	00000929 	andeq	r0, r0, r9, lsr #18
    2984:	00008c23 	andeq	r8, r0, r3, lsr #24
    2988:	98967f00 	ldmls	r6, {r8, r9, sl, fp, ip, sp, lr}
    298c:	9d040000 	stcls	0, cr0, [r4, #-0]
    2990:	0100000c 	tsteq	r0, ip
    2994:	0008e022 	andeq	lr, r8, r2, lsr #32
    2998:	0e052400 	cfcpyseq	mvf2, mvf5
    299c:	23010000 	movwcs	r0, #4096	; 0x1000
    29a0:	0000004f 	andeq	r0, r0, pc, asr #32
    29a4:	7cc40305 	stclvc	3, cr0, [r4], {5}
    29a8:	de240005 	cdple	0, 2, cr0, cr4, cr5, {0}
    29ac:	01000009 	tsteq	r0, r9
    29b0:	00089124 	andeq	r9, r8, r4, lsr #2
    29b4:	1c030500 	cfstr32ne	mvfx0, [r3], {-0}
    29b8:	0c098ee5 	stceq	14, cr8, [r9], {229}	; 0xe5
    29bc:	000004f6 	strdeq	r0, [r0], -r6
    29c0:	00000966 	andeq	r0, r0, r6, ror #18
    29c4:	00008c0d 	andeq	r8, r0, sp, lsl #24
    29c8:	24001f00 	strcs	r1, [r0], #-3840	; 0xfffff100
    29cc:	00000e00 	andeq	r0, r0, r0, lsl #28
    29d0:	09562501 	ldmdbeq	r6, {r0, r8, sl, sp}^
    29d4:	03050000 	movweq	r0, #20480	; 0x5000
    29d8:	098ee598 	stmibeq	lr, {r3, r4, r7, r8, sl, sp, lr, pc}
    29dc:	00100d24 	andseq	r0, r0, r4, lsr #26
    29e0:	4f260100 	svcmi	0x00260100
    29e4:	05000000 	streq	r0, [r0, #-0]
    29e8:	057cc803 	ldrbeq	ip, [ip, #-2051]!	; 0xfffff7fd
    29ec:	00830900 	addeq	r0, r3, r0, lsl #18
    29f0:	27010000 	strcs	r0, [r1, -r0]
    29f4:	0000004f 	andeq	r0, r0, pc, asr #32
    29f8:	00009209 	andeq	r9, r0, r9, lsl #4
    29fc:	4f280100 	svcmi	0x00280100
    2a00:	09000000 	stmdbeq	r0, {}	; <UNPREDICTABLE>
    2a04:	00000d02 	andeq	r0, r0, r2, lsl #26
    2a08:	004f2901 	subeq	r2, pc, r1, lsl #18
    2a0c:	9a090000 	bls	242a14 <ringBuffer+0x1ead0c>
    2a10:	0100000d 	tsteq	r0, sp
    2a14:	0009292a 	andeq	r2, r9, sl, lsr #18
    2a18:	65722500 	ldrbvs	r2, [r2, #-1280]!	; 0xfffffb00
    2a1c:	3a010073 	bcc	42bf0 <blake2s_compress+0x1d38>
    2a20:	00000522 	andeq	r0, r0, r2, lsr #10
    2a24:	e5c40305 	strb	r0, [r4, #773]	; 0x305
    2a28:	6325098e 			; <UNDEFINED> instruction: 0x6325098e
    2a2c:	01007874 	tsteq	r0, r4, ror r8
    2a30:	0005563b 	andeq	r5, r5, fp, lsr r6
    2a34:	14030500 	strne	r0, [r3], #-1280	; 0xfffffb00
    2a38:	24098ee5 	strcs	r8, [r9], #-3813	; 0xfffff11b
    2a3c:	00000eaf 	andeq	r0, r0, pc, lsr #29
    2a40:	073c3c01 	ldreq	r3, [ip, -r1, lsl #24]!
    2a44:	03050000 	movweq	r0, #20480	; 0x5000
    2a48:	098ee5bc 	stmibeq	lr, {r2, r3, r4, r5, r7, r8, sl, sp, lr, pc}
    2a4c:	00706f25 	rsbseq	r6, r0, r5, lsr #30
    2a50:	079c3d01 	ldreq	r3, [ip, r1, lsl #26]
    2a54:	03050000 	movweq	r0, #20480	; 0x5000
    2a58:	098ee5c8 	stmibeq	lr, {r3, r6, r7, r8, sl, sp, lr, pc}
    2a5c:	0011b924 	andseq	fp, r1, r4, lsr #18
    2a60:	b03e0100 	eorslt	r0, lr, r0, lsl #2
    2a64:	05000005 	streq	r0, [r0, #-5]
    2a68:	0570f403 	ldrbeq	pc, [r0, #-1027]!	; 0xfffffbfd	; <UNPREDICTABLE>
    2a6c:	0ee32400 	cdpeq	4, 14, cr2, cr3, cr0, {0}
    2a70:	3f010000 	svccc	0x00010000
    2a74:	0000050c 	andeq	r0, r0, ip, lsl #10
    2a78:	e5b80305 	ldr	r0, [r8, #773]!	; 0x305
    2a7c:	f424098e 	vld2.32	{d0,d2}, [r4], lr
    2a80:	0100000e 	tsteq	r0, lr
    2a84:	00054f41 	andeq	r4, r5, r1, asr #30
    2a88:	cc030500 	cfstr32gt	mvfx0, [r3], {-0}
    2a8c:	2400057c 	strcs	r0, [r0], #-1404	; 0xfffffa84
    2a90:	00000fac 	andeq	r0, r0, ip, lsr #31
    2a94:	004f5e01 	subeq	r5, pc, r1, lsl #28
    2a98:	03050000 	movweq	r0, #20480	; 0x5000
    2a9c:	00057cd0 	ldrdeq	r7, [r5], -r0
    2aa0:	0010ce26 	andseq	ip, r0, r6, lsr #28
    2aa4:	01a10100 			; <UNDEFINED> instruction: 0x01a10100
    2aa8:	000450ec 	andeq	r5, r4, ip, ror #1
    2aac:	00000026 	andeq	r0, r0, r6, lsr #32
    2ab0:	0a709c01 	beq	1c29abc <ringBuffer+0x1bd1db4>
    2ab4:	89270000 	stmdbhi	r7!, {}	; <UNPREDICTABLE>
    2ab8:	0100000e 	tsteq	r0, lr
    2abc:	0a7f01a1 	beq	1fc3148 <ringBuffer+0x1f6b440>
    2ac0:	91020000 	mrsls	r0, (UNDEF: 2)
    2ac4:	10d2286c 	sbcsne	r2, r2, ip, ror #16
    2ac8:	a2010000 	andge	r0, r1, #0
    2acc:	00013401 	andeq	r3, r1, r1, lsl #8
    2ad0:	74910200 	ldrvc	r0, [r1], #512	; 0x200
    2ad4:	00931400 	addseq	r1, r3, r0, lsl #8
    2ad8:	0a7f0000 	beq	1fc2ae0 <ringBuffer+0x1f6add8>
    2adc:	93150000 	tstls	r5, #0
    2ae0:	00000000 	andeq	r0, r0, r0
    2ae4:	0a700406 	beq	1c03b04 <ringBuffer+0x1babdfc>
    2ae8:	24290000 	strtcs	r0, [r9], #-0
    2aec:	0100000f 	tsteq	r0, pc
    2af0:	50980197 	umullspl	r0, r8, r7, r1
    2af4:	00540004 	subseq	r0, r4, r4
    2af8:	9c010000 	stcls	0, cr0, [r1], {-0}
    2afc:	00000aaa 	andeq	r0, r0, sl, lsr #21
    2b00:	0010ce2a 	andseq	ip, r0, sl, lsr #28
    2b04:	019e0100 	orrseq	r0, lr, r0, lsl #2
    2b08:	0000004f 	andeq	r0, r0, pc, asr #32
    2b0c:	2600002b 	strcs	r0, [r0], -fp, lsr #32
    2b10:	00000f10 	andeq	r0, r0, r0, lsl pc
    2b14:	24018301 	strcs	r8, [r1], #-769	; 0xfffffcff
    2b18:	74000450 	strvc	r0, [r0], #-1104	; 0xfffffbb0
    2b1c:	01000000 	mrseq	r0, (UNDEF: 0)
    2b20:	000b149c 	muleq	fp, ip, r4
    2b24:	0eee2700 	cdpeq	7, 14, cr2, cr14, cr0, {0}
    2b28:	83010000 	movwhi	r0, #4096	; 0x1000
    2b2c:	000b1401 	andeq	r1, fp, r1, lsl #8
    2b30:	6c910200 	lfmvs	f0, 4, [r1], {0}
    2b34:	000ea427 	andeq	sl, lr, r7, lsr #8
    2b38:	01830100 	orreq	r0, r3, r0, lsl #2
    2b3c:	000000a7 	andeq	r0, r0, r7, lsr #1
    2b40:	27689102 	strbcs	r9, [r8, -r2, lsl #2]!
    2b44:	00000ffd 	strdeq	r0, [r0], -sp
    2b48:	11018301 	tstne	r1, r1, lsl #6
    2b4c:	02000001 	andeq	r0, r0, #1
    2b50:	c7286491 			; <UNDEFINED> instruction: 0xc7286491
    2b54:	0100000f 	tsteq	r0, pc
    2b58:	0b1a0184 	bleq	683170 <ringBuffer+0x62b468>
    2b5c:	91020000 	mrsls	r0, (UNDEF: 2)
    2b60:	50442c70 	subpl	r2, r4, r0, ror ip
    2b64:	002a0004 	eoreq	r0, sl, r4
    2b68:	692d0000 	pushvs	{}	; <UNPREDICTABLE>
    2b6c:	01870100 	orreq	r0, r7, r0, lsl #2
    2b70:	000000a7 	andeq	r0, r0, r7, lsr #1
    2b74:	00749102 	rsbseq	r9, r4, r2, lsl #2
    2b78:	f6040600 			; <UNDEFINED> instruction: 0xf6040600
    2b7c:	06000004 	streq	r0, [r0], -r4
    2b80:	00013f04 	andeq	r3, r1, r4, lsl #30
    2b84:	0fb72600 	svceq	0x00b72600
    2b88:	76010000 	strvc	r0, [r1], -r0
    2b8c:	044fc001 	strbeq	ip, [pc], #-1	; 2b94 <_init-0xdf8c>
    2b90:	00006400 	andeq	r6, r0, r0, lsl #8
    2b94:	7d9c0100 	ldfvcs	f0, [ip]
    2b98:	2700000b 	strcs	r0, [r0, -fp]
    2b9c:	00000f02 	andeq	r0, r0, r2, lsl #30
    2ba0:	0c017601 	stceq	6, cr7, [r1], {1}
    2ba4:	02000005 	andeq	r0, r0, #5
    2ba8:	fd276491 	stc2	4, cr6, [r7, #-580]!	; 0xfffffdbc
    2bac:	0100000f 	tsteq	r0, pc
    2bb0:	01110176 	tsteq	r1, r6, ror r1
    2bb4:	91020000 	mrsls	r0, (UNDEF: 2)
    2bb8:	0fc72860 	svceq	0x00c72860
    2bbc:	77010000 	strvc	r0, [r1, -r0]
    2bc0:	000b1a01 	andeq	r1, fp, r1, lsl #20
    2bc4:	74910200 	ldrvc	r0, [r1], #512	; 0x200
    2bc8:	044fde2c 	strbeq	sp, [pc], #-3628	; 2bd0 <_init-0xdf50>
    2bcc:	00002200 	andeq	r2, r0, r0, lsl #4
    2bd0:	11a52800 			; <UNDEFINED> instruction: 0x11a52800
    2bd4:	79010000 	stmdbvc	r1, {}	; <UNPREDICTABLE>
    2bd8:	000b7d01 	andeq	r7, fp, r1, lsl #26
    2bdc:	68910200 	ldmvs	r1, {r9}
    2be0:	9b0c0000 	blls	302be8 <ringBuffer+0x2aaee0>
    2be4:	8d000000 	stchi	0, cr0, [r0, #-0]
    2be8:	0d00000b 	stceq	0, cr0, [r0, #-44]	; 0xffffffd4
    2bec:	0000008c 	andeq	r0, r0, ip, lsl #1
    2bf0:	e32e000b 			; <UNDEFINED> instruction: 0xe32e000b
    2bf4:	01000010 	tsteq	r0, r0, lsl r0
    2bf8:	000093f7 	strdeq	r9, [r0], -r7
    2bfc:	044e4c00 	strbeq	r4, [lr], #-3072	; 0xfffff400
    2c00:	00017400 	andeq	r7, r1, r0, lsl #8
    2c04:	3c9c0100 	ldfccs	f0, [ip], {0}
    2c08:	2f00000c 	svccs	0x0000000c
    2c0c:	00001137 	andeq	r1, r0, r7, lsr r1
    2c10:	08d5fa01 	ldmeq	r5, {r0, r9, fp, ip, sp, lr, pc}^
    2c14:	91020000 	mrsls	r0, (UNDEF: 2)
    2c18:	4e562c60 	cdpmi	12, 5, cr2, cr6, cr0, {3}
    2c1c:	01220004 			; <UNDEFINED> instruction: 0x01220004
    2c20:	70300000 	eorsvc	r0, r0, r0
    2c24:	0100706f 	tsteq	r0, pc, rrx
    2c28:	00004ffe 	strdeq	r4, [r0], -lr
    2c2c:	000bce00 	andeq	ip, fp, r0, lsl #28
    2c30:	31002b00 	tstcc	r0, r0, lsl #22
    2c34:	00044e70 	andeq	r4, r4, r0, ror lr
    2c38:	0000000e 	andeq	r0, r0, lr
    2c3c:	00000bea 	andeq	r0, r0, sl, ror #23
    2c40:	000fb72a 	andeq	fp, pc, sl, lsr #14
    2c44:	01070100 	mrseq	r0, (UNDEF: 23)
    2c48:	0000004f 	andeq	r0, r0, pc, asr #32
    2c4c:	3100002b 	tstcc	r0, fp, lsr #32
    2c50:	00044eee 	andeq	r4, r4, lr, ror #29
    2c54:	0000000e 	andeq	r0, r0, lr
    2c58:	00000c06 	andeq	r0, r0, r6, lsl #24
    2c5c:	000fb72a 	andeq	fp, pc, sl, lsr #14
    2c60:	01070100 	mrseq	r0, (UNDEF: 23)
    2c64:	0000004f 	andeq	r0, r0, pc, asr #32
    2c68:	2c00002b 	stccs	0, cr0, [r0], {43}	; 0x2b
    2c6c:	00044f12 	andeq	r4, r4, r2, lsl pc
    2c70:	00000066 	andeq	r0, r0, r6, rrx
    2c74:	000ba332 	andeq	sl, fp, r2, lsr r3
    2c78:	01420100 	mrseq	r0, (UNDEF: 82)
    2c7c:	0000004f 	andeq	r0, r0, pc, asr #32
    2c80:	00000c21 	andeq	r0, r0, r1, lsr #24
    2c84:	362c002b 	strtcc	r0, [ip], -fp, lsr #32
    2c88:	4200044f 	andmi	r0, r0, #1325400064	; 0x4f000000
    2c8c:	2a000000 	bcs	2c94 <_init-0xde8c>
    2c90:	00000f10 	andeq	r0, r0, r0, lsl pc
    2c94:	4f014701 	svcmi	0x00014701
    2c98:	2b000000 	blcs	2ca0 <_init-0xde80>
    2c9c:	00000000 	andeq	r0, r0, r0
    2ca0:	0f413300 	svceq	0x00413300
    2ca4:	db010000 	blle	42cac <blake2s_compress+0x1df4>
    2ca8:	00044d20 	andeq	r4, r4, r0, lsr #26
    2cac:	0000012c 	andeq	r0, r0, ip, lsr #2
    2cb0:	0cca9c01 	stcleq	12, cr9, [sl], {1}
    2cb4:	0f340000 	svceq	0x00340000
    2cb8:	01000012 	tsteq	r0, r2, lsl r0
    2cbc:	000111db 	ldrdeq	r1, [r1], -fp
    2cc0:	54910200 	ldrpl	r0, [r1], #512	; 0x200
    2cc4:	000e3e34 	andeq	r3, lr, r4, lsr lr
    2cc8:	11db0100 	bicsne	r0, fp, r0, lsl #2
    2ccc:	02000001 	andeq	r0, r0, #1
    2cd0:	19345091 	ldmdbne	r4!, {r0, r4, r7, ip, lr}
    2cd4:	01000012 	tsteq	r0, r2, lsl r0
    2cd8:	000111db 	ldrdeq	r1, [r1], -fp
    2cdc:	4c910200 	lfmmi	f0, 4, [r1], {0}
    2ce0:	00122334 	andseq	r2, r2, r4, lsr r3
    2ce4:	11dc0100 	bicsne	r0, ip, r0, lsl #2
    2ce8:	02000001 	andeq	r0, r0, #1
    2cec:	2d344891 	ldccs	8, cr4, [r4, #-580]!	; 0xfffffdbc
    2cf0:	01000012 	tsteq	r0, r2, lsl r0
    2cf4:	000111dc 	ldrdeq	r1, [r1], -ip
    2cf8:	00910200 	addseq	r0, r1, r0, lsl #4
    2cfc:	0012a82f 	andseq	sl, r2, pc, lsr #16
    2d00:	cade0100 	bgt	ff783108 <__bss_end__+0xf5e94b04>
    2d04:	0200000c 	andeq	r0, r0, #12
    2d08:	c72f5c91 			; <UNDEFINED> instruction: 0xc72f5c91
    2d0c:	0100000f 	tsteq	r0, pc
    2d10:	000b1adf 	ldrdeq	r1, [fp], -pc	; <UNPREDICTABLE>
    2d14:	70910200 	addsvc	r0, r1, r0, lsl #4
    2d18:	044d422c 	strbeq	r4, [sp], #-556	; 0xfffffdd4
    2d1c:	0000e800 	andeq	lr, r0, r0, lsl #16
    2d20:	00693500 	rsbeq	r3, r9, r0, lsl #10
    2d24:	004fe101 	subeq	lr, pc, r1, lsl #2
    2d28:	91020000 	mrsls	r0, (UNDEF: 2)
    2d2c:	0c000074 	stceq	0, cr0, [r0], {116}	; 0x74
    2d30:	00000111 	andeq	r0, r0, r1, lsl r1
    2d34:	00000cda 	ldrdeq	r0, [r0], -sl
    2d38:	00008c0d 	andeq	r8, r0, sp, lsl #24
    2d3c:	33000400 	movwcc	r0, #1024	; 0x400
    2d40:	00000dfa 	strdeq	r0, [r0], -sl
    2d44:	4cdcd401 	cfldrdmi	mvd13, [ip], {1}
    2d48:	00440004 	subeq	r0, r4, r4
    2d4c:	9c010000 	stcls	0, cr0, [r1], {-0}
    2d50:	00000d22 	andeq	r0, r0, r2, lsr #26
    2d54:	000e0034 	andeq	r0, lr, r4, lsr r0
    2d58:	14d40100 	ldrbne	r0, [r4], #256	; 0x100
    2d5c:	0200000b 	andeq	r0, r0, #11
    2d60:	75346c91 	ldrvc	r6, [r4, #-3217]!	; 0xfffff36f
    2d64:	01000006 	tsteq	r0, r6
    2d68:	0000a7d4 	ldrdeq	sl, [r0], -r4
    2d6c:	68910200 	ldmvs	r1, {r9}
    2d70:	044ce62c 	strbeq	lr, [ip], #-1580	; 0xfffff9d4
    2d74:	00002800 	andeq	r2, r0, r0, lsl #16
    2d78:	00693500 	rsbeq	r3, r9, r0, lsl #10
    2d7c:	00a7d501 	adceq	sp, r7, r1, lsl #10
    2d80:	91020000 	mrsls	r0, (UNDEF: 2)
    2d84:	33000074 	movwcc	r0, #116	; 0x74
    2d88:	00000f83 	andeq	r0, r0, r3, lsl #31
    2d8c:	4c86ca01 	vstmiami	r6, {s24}
    2d90:	00560004 	subseq	r0, r6, r4
    2d94:	9c010000 	stcls	0, cr0, [r1], {-0}
    2d98:	00000d70 	andeq	r0, r0, r0, ror sp
    2d9c:	00102d34 	andseq	r2, r0, r4, lsr sp
    2da0:	0cca0100 	stfeqe	f0, [sl], {0}
    2da4:	02000005 	andeq	r0, r0, #5
    2da8:	35346c91 	ldrcc	r6, [r4, #-3217]!	; 0xfffff36f
    2dac:	01000010 	tsteq	r0, r0, lsl r0
    2db0:	00050cca 	andeq	r0, r5, sl, asr #25
    2db4:	68910200 	ldmvs	r1, {r9}
    2db8:	000ffd34 	andeq	pc, pc, r4, lsr sp	; <UNPREDICTABLE>
    2dbc:	11ca0100 	bicne	r0, sl, r0, lsl #2
    2dc0:	02000001 	andeq	r0, r0, #1
    2dc4:	c72f6491 			; <UNDEFINED> instruction: 0xc72f6491
    2dc8:	0100000f 	tsteq	r0, pc
    2dcc:	000b1acb 	andeq	r1, fp, fp, asr #21
    2dd0:	74910200 	ldrvc	r0, [r1], #512	; 0x200
    2dd4:	0f653600 	svceq	0x00653600
    2dd8:	c6010000 	strgt	r0, [r1], -r0
    2ddc:	00044c70 	andeq	r4, r4, r0, ror ip
    2de0:	00000016 	andeq	r0, r0, r6, lsl r0
    2de4:	0da29c01 	stceq	12, cr9, [r2, #4]!
    2de8:	2c340000 	ldccs	0, cr0, [r4], #-0
    2dec:	01000011 	tsteq	r0, r1, lsl r0
    2df0:	00004fc6 	andeq	r4, r0, r6, asr #31
    2df4:	74910200 	ldrvc	r0, [r1], #512	; 0x200
    2df8:	00114234 	andseq	r4, r1, r4, lsr r2
    2dfc:	4fc60100 	svcmi	0x00c60100
    2e00:	02000000 	andeq	r0, r0, #0
    2e04:	36007091 			; <UNDEFINED> instruction: 0x36007091
    2e08:	00001174 	andeq	r1, r0, r4, ror r1
    2e0c:	4c5ac201 	lfmmi	f4, 3, [sl], {1}
    2e10:	00160004 	andseq	r0, r6, r4
    2e14:	9c010000 	stcls	0, cr0, [r1], {-0}
    2e18:	00000dc6 	andeq	r0, r0, r6, asr #27
    2e1c:	00115b34 	andseq	r5, r1, r4, lsr fp
    2e20:	4fc20100 	svcmi	0x00c20100
    2e24:	02000005 	andeq	r0, r0, #5
    2e28:	36007791 			; <UNDEFINED> instruction: 0x36007791
    2e2c:	000011f3 	strdeq	r1, [r0], -r3
    2e30:	4c40be01 	mcrrmi	14, 0, fp, r0, cr1
    2e34:	001a0004 	andseq	r0, sl, r4
    2e38:	9c010000 	stcls	0, cr0, [r1], {-0}
    2e3c:	00000df4 	strdeq	r0, [r0], -r4
    2e40:	01006137 	tsteq	r0, r7, lsr r1
    2e44:	000517be 			; <UNDEFINED> instruction: 0x000517be
    2e48:	70910200 	addsvc	r0, r1, r0, lsl #4
    2e4c:	01006237 	tsteq	r0, r7, lsr r2
    2e50:	000517be 			; <UNDEFINED> instruction: 0x000517be
    2e54:	68910200 	ldmvs	r1, {r9}
    2e58:	0e1a3800 	cdpeq	8, 1, cr3, cr10, cr0, {0}
    2e5c:	a8010000 	stmdage	r1, {}	; <UNPREDICTABLE>
    2e60:	00044bbc 			; <UNDEFINED> instruction: 0x00044bbc
    2e64:	00000084 	andeq	r0, r0, r4, lsl #1
    2e68:	6f339c01 	svcvs	0x00339c01
    2e6c:	0100000e 	tsteq	r0, lr
    2e70:	044a285f 	strbeq	r2, [sl], #-2143	; 0xfffff7a1
    2e74:	00019400 	andeq	r9, r1, r0, lsl #8
    2e78:	449c0100 	ldrmi	r0, [ip], #256	; 0x100
    2e7c:	3400000e 	strcc	r0, [r0], #-14
    2e80:	00000f4e 	andeq	r0, r0, lr, asr #30
    2e84:	004f5f01 	subeq	r5, pc, r1, lsl #30
    2e88:	91020000 	mrsls	r0, (UNDEF: 2)
    2e8c:	6370376c 	cmnvs	r0, #108, 14	; 0x1b00000
    2e90:	4f5f0100 	svcmi	0x005f0100
    2e94:	02000000 	andeq	r0, r0, #0
    2e98:	b0346891 	mlaslt	r4, r1, r8, r6
    2e9c:	01000011 	tsteq	r0, r1, lsl r0
    2ea0:	00004f5f 	andeq	r4, r0, pc, asr pc
    2ea4:	64910200 	ldrvs	r0, [r1], #512	; 0x200
    2ea8:	127f3800 	rsbsne	r3, pc, #0, 16
    2eac:	46010000 	strmi	r0, [r1], -r0
    2eb0:	0004499c 	muleq	r4, ip, r9
    2eb4:	0000008c 	andeq	r0, r0, ip, lsl #1
    2eb8:	d8009c01 	stmdale	r0, {r0, sl, fp, ip, pc}
    2ebc:	02000000 	andeq	r0, r0, #0
    2ec0:	0009d200 	andeq	sp, r9, r0, lsl #4
    2ec4:	8d010400 	cfstrshi	mvf0, [r1, #-0]
    2ec8:	14000016 	strne	r0, [r0], #-22	; 0xffffffea
    2ecc:	44000451 	strmi	r0, [r0], #-1105	; 0xfffffbaf
    2ed0:	2e000451 	cfmvsrcs	mvf0, r0
    2ed4:	79732f2e 	ldmdbvc	r3!, {r1, r2, r3, r5, r8, r9, sl, fp, sp}^
    2ed8:	70656473 	rsbvc	r6, r5, r3, ror r4
    2edc:	72612f73 	rsbvc	r2, r1, #460	; 0x1cc
    2ee0:	74732f6d 	ldrbtvc	r2, [r3], #-3949	; 0xfffff093
    2ee4:	2e747261 	cdpcs	2, 7, cr7, cr4, cr1, {3}
    2ee8:	682f0053 	stmdavs	pc!, {r0, r1, r4, r6}	; <UNPREDICTABLE>
    2eec:	2f656d6f 	svccs	0x00656d6f
    2ef0:	67776374 			; <UNDEFINED> instruction: 0x67776374
    2ef4:	6975622d 	ldmdbvs	r5!, {r0, r2, r3, r5, r9, sp, lr}^
    2ef8:	6c73646c 	cfldrdvs	mvd6, [r3], #-432	; 0xfffffe50
    2efc:	2f657661 	svccs	0x00657661
    2f00:	6b726f77 	blvs	1c9ece4 <ringBuffer+0x1c46fdc>
    2f04:	63617073 	cmnvs	r1, #115	; 0x73
    2f08:	63742f65 	cmnvs	r4, #404	; 0x194
    2f0c:	6d2d6777 	stcvs	7, cr6, [sp, #-476]!	; 0xfffffe24
    2f10:	2d656b61 	fstmdbxcs	r5!, {d22-d69}	;@ Deprecated
    2f14:	656c6572 	strbvs	r6, [ip, #-1394]!	; 0xfffffa8e
    2f18:	2f657361 	svccs	0x00657361
    2f1c:	6562616c 	strbvs	r6, [r2, #-364]!	; 0xfffffe94
    2f20:	6f642f6c 	svcvs	0x00642f6c
    2f24:	72656b63 	rsbvc	r6, r5, #101376	; 0x18c00
    2f28:	7572742d 	ldrbvc	r7, [r2, #-1069]!	; 0xfffffbd3
    2f2c:	2d797473 	cfldrdcs	mvd7, [r9, #-460]!	; 0xfffffe34
    2f30:	36646d61 	strbtcc	r6, [r4], -r1, ror #26
    2f34:	63742d34 	cmnvs	r4, #52, 26	; 0xd00
    2f38:	622d6777 	eorvs	r6, sp, #31195136	; 0x1dc0000
    2f3c:	646c6975 	strbtvs	r6, [ip], #-2421	; 0xfffff68b
    2f40:	7261742f 	rsbvc	r7, r1, #788529152	; 0x2f000000
    2f44:	2f746567 	svccs	0x00746567
    2f48:	2d6d7261 	sfmcs	f7, 2, [sp, #-388]!	; 0xfffffe7c
    2f4c:	756e696c 	strbvc	r6, [lr, #-2412]!	; 0xfffff694
    2f50:	6e672d78 	mcrvs	13, 3, r2, cr7, cr8, {3}
    2f54:	62616575 	rsbvs	r6, r1, #490733568	; 0x1d400000
    2f58:	2f666869 	svccs	0x00666869
    2f5c:	70616e73 	rsbvc	r6, r1, r3, ror lr
    2f60:	746f6873 	strbtvc	r6, [pc], #-2163	; 2f68 <_init-0xdbb8>
    2f64:	6c672f73 	stclvs	15, cr2, [r7], #-460	; 0xfffffe34
    2f68:	2e636269 	cdpcs	2, 6, cr6, cr3, cr9, {3}
    2f6c:	7e746967 	vsubvc.f16	s13, s8, s15	; <UNPREDICTABLE>
    2f70:	616e696c 	cmnvs	lr, ip, ror #18
    2f74:	327e6f72 	rsbscc	r6, lr, #456	; 0x1c8
    2f78:	7e33322e 	cdpvc	2, 3, cr3, cr3, cr14, {1}
    2f7c:	7473616d 	ldrbtvc	r6, [r3], #-365	; 0xfffffe93
    2f80:	632f7265 			; <UNDEFINED> instruction: 0x632f7265
    2f84:	47007573 	smlsdxmi	r0, r3, r5, r7
    2f88:	4120554e 			; <UNDEFINED> instruction: 0x4120554e
    2f8c:	2e322053 	mrccs	0, 1, r2, cr2, cr3, {2}
    2f90:	302e3732 	eorcc	r3, lr, r2, lsr r7
    2f94:	84800100 	strhi	r0, [r0], #256	; 0x100
    2f98:	04000000 	streq	r0, [r0], #-0
    2f9c:	0009e600 	andeq	lr, r9, r0, lsl #12
    2fa0:	ce010400 	cfcpysgt	mvf0, mvf1
    2fa4:	0c000012 	stceq	0, cr0, [r0], {18}
    2fa8:	0000144c 	andeq	r1, r0, ip, asr #8
    2fac:	000013a0 	andeq	r1, r0, r0, lsr #7
    2fb0:	000016e6 	andeq	r1, r0, r6, ror #13
    2fb4:	6e080102 	adfvse	f0, f0, f2
    2fb8:	02000008 	andeq	r0, r0, #8
    2fbc:	07530702 	ldrbeq	r0, [r3, -r2, lsl #14]
    2fc0:	04020000 	streq	r0, [r2], #-0
    2fc4:	00058307 	andeq	r8, r5, r7, lsl #6
    2fc8:	07040200 	streq	r0, [r4, -r0, lsl #4]
    2fcc:	0000057e 	andeq	r0, r0, lr, ror r5
    2fd0:	70060102 	andvc	r0, r6, r2, lsl #2
    2fd4:	02000008 	andeq	r0, r0, #8
    2fd8:	087c0502 	ldmdaeq	ip!, {r1, r8, sl}^
    2fdc:	04030000 	streq	r0, [r3], #-0
    2fe0:	746e6905 	strbtvc	r6, [lr], #-2309	; 0xfffff6fb
    2fe4:	00470400 	subeq	r0, r7, r0, lsl #8
    2fe8:	08020000 	stmdaeq	r2, {}	; <UNPREDICTABLE>
    2fec:	0005b905 	andeq	fp, r5, r5, lsl #18
    2ff0:	07080200 	streq	r0, [r8, -r0, lsl #4]
    2ff4:	00000579 	andeq	r0, r0, r9, ror r5
    2ff8:	be050402 	cdplt	4, 0, cr0, cr5, cr2, {0}
    2ffc:	02000005 	andeq	r0, r0, #5
    3000:	01020704 	tsteq	r2, r4, lsl #14
    3004:	01020000 	mrseq	r0, (UNDEF: 2)
    3008:	00087708 	andeq	r7, r8, r8, lsl #14
    300c:	143d0500 	ldrtne	r0, [sp], #-1280	; 0xfffffb00
    3010:	18010000 	stmdane	r1, {}	; <UNPREDICTABLE>
    3014:	0000004e 	andeq	r0, r0, lr, asr #32
    3018:	6c600305 	stclvs	3, cr0, [r0], #-20	; 0xffffffec
    301c:	d3000004 	movwle	r0, #4
    3020:	02000000 	andeq	r0, r0, #0
    3024:	000a2400 	andeq	r2, sl, r0, lsl #8
    3028:	0d010400 	cfstrseq	mvf0, [r1, #-0]
    302c:	a0000017 	andge	r0, r0, r7, lsl r0
    3030:	2e000000 	cdpcs	0, 0, cr0, cr0, cr0, {0}
    3034:	79732f2e 	ldmdbvc	r3!, {r1, r2, r3, r5, r8, r9, sl, fp, sp}^
    3038:	70656473 	rsbvc	r6, r5, r3, ror r4
    303c:	72612f73 	rsbvc	r2, r1, #460	; 0x1cc
    3040:	72632f6d 	rsbvc	r2, r3, #436	; 0x1b4
    3044:	532e6974 			; <UNDEFINED> instruction: 0x532e6974
    3048:	6f682f00 	svcvs	0x00682f00
    304c:	742f656d 	strtvc	r6, [pc], #-1389	; 3054 <_init-0xdacc>
    3050:	2d677763 	stclcs	7, cr7, [r7, #-396]!	; 0xfffffe74
    3054:	6c697562 	cfstr64vs	mvdx7, [r9], #-392	; 0xfffffe78
    3058:	616c7364 	cmnvs	ip, r4, ror #6
    305c:	772f6576 			; <UNDEFINED> instruction: 0x772f6576
    3060:	736b726f 	cmnvc	fp, #-268435450	; 0xf0000006
    3064:	65636170 	strbvs	r6, [r3, #-368]!	; 0xfffffe90
    3068:	7763742f 	strbvc	r7, [r3, -pc, lsr #8]!
    306c:	616d2d67 	cmnvs	sp, r7, ror #26
    3070:	722d656b 	eorvc	r6, sp, #448790528	; 0x1ac00000
    3074:	61656c65 	cmnvs	r5, r5, ror #24
    3078:	6c2f6573 	cfstr32vs	mvfx6, [pc], #-460	; 2eb4 <_init-0xdc6c>
    307c:	6c656261 	sfmvs	f6, 2, [r5], #-388	; 0xfffffe7c
    3080:	636f642f 	cmnvs	pc, #788529152	; 0x2f000000
    3084:	2d72656b 	cfldr64cs	mvdx6, [r2, #-428]!	; 0xfffffe54
    3088:	73757274 	cmnvc	r5, #116, 4	; 0x40000007
    308c:	612d7974 			; <UNDEFINED> instruction: 0x612d7974
    3090:	3436646d 	ldrtcc	r6, [r6], #-1133	; 0xfffffb93
    3094:	7763742d 	strbvc	r7, [r3, -sp, lsr #8]!
    3098:	75622d67 	strbvc	r2, [r2, #-3431]!	; 0xfffff299
    309c:	2f646c69 	svccs	0x00646c69
    30a0:	67726174 			; <UNDEFINED> instruction: 0x67726174
    30a4:	612f7465 			; <UNDEFINED> instruction: 0x612f7465
    30a8:	6c2d6d72 	stcvs	13, cr6, [sp], #-456	; 0xfffffe38
    30ac:	78756e69 	ldmdavc	r5!, {r0, r3, r5, r6, r9, sl, fp, sp, lr}^
    30b0:	756e672d 	strbvc	r6, [lr, #-1837]!	; 0xfffff8d3
    30b4:	69626165 	stmdbvs	r2!, {r0, r2, r5, r6, r8, sp, lr}^
    30b8:	732f6668 			; <UNDEFINED> instruction: 0x732f6668
    30bc:	7370616e 	cmnvc	r0, #-2147483621	; 0x8000001b
    30c0:	73746f68 	cmnvc	r4, #104, 30	; 0x1a0
    30c4:	696c672f 	stmdbvs	ip!, {r0, r1, r2, r3, r5, r8, r9, sl, sp, lr}^
    30c8:	672e6362 	strvs	r6, [lr, -r2, ror #6]!
    30cc:	6c7e7469 	cfldrdvs	mvd7, [lr], #-420	; 0xfffffe5c
    30d0:	72616e69 	rsbvc	r6, r1, #1680	; 0x690
    30d4:	2e327e6f 	cdpcs	14, 3, cr7, cr2, cr15, {3}
    30d8:	6d7e3332 	ldclvs	3, cr3, [lr, #-200]!	; 0xffffff38
    30dc:	65747361 	ldrbvs	r7, [r4, #-865]!	; 0xfffffc9f
    30e0:	73632f72 	cmnvc	r3, #456	; 0x1c8
    30e4:	4e470075 	mcrmi	0, 2, r0, cr7, cr5, {3}
    30e8:	53412055 	movtpl	r2, #4181	; 0x1055
    30ec:	322e3220 	eorcc	r3, lr, #32, 4
    30f0:	00302e37 	eorseq	r2, r0, r7, lsr lr
    30f4:	00d38001 	sbcseq	r8, r3, r1
    30f8:	00020000 	andeq	r0, r2, r0
    30fc:	00000a36 	andeq	r0, r0, r6, lsr sl
    3100:	17790104 	ldrbne	r0, [r9, -r4, lsl #2]!
    3104:	00c80000 	sbceq	r0, r8, r0
    3108:	2e2e0000 	cdpcs	0, 2, cr0, cr14, cr0, {0}
    310c:	7379732f 	cmnvc	r9, #-1140850688	; 0xbc000000
    3110:	73706564 	cmnvc	r0, #100, 10	; 0x19000000
    3114:	6d72612f 	ldfvse	f6, [r2, #-188]!	; 0xffffff44
    3118:	7472632f 	ldrbtvc	r6, [r2], #-815	; 0xfffffcd1
    311c:	00532e6e 	subseq	r2, r3, lr, ror #28
    3120:	6d6f682f 	stclvs	8, cr6, [pc, #-188]!	; 306c <_init-0xdab4>
    3124:	63742f65 	cmnvs	r4, #404	; 0x194
    3128:	622d6777 	eorvs	r6, sp, #31195136	; 0x1dc0000
    312c:	646c6975 	strbtvs	r6, [ip], #-2421	; 0xfffff68b
    3130:	76616c73 			; <UNDEFINED> instruction: 0x76616c73
    3134:	6f772f65 	svcvs	0x00772f65
    3138:	70736b72 	rsbsvc	r6, r3, r2, ror fp
    313c:	2f656361 	svccs	0x00656361
    3140:	67776374 			; <UNDEFINED> instruction: 0x67776374
    3144:	6b616d2d 	blvs	185e600 <ringBuffer+0x18068f8>
    3148:	65722d65 	ldrbvs	r2, [r2, #-3429]!	; 0xfffff29b
    314c:	7361656c 	cmnvc	r1, #108, 10	; 0x1b000000
    3150:	616c2f65 	cmnvs	ip, r5, ror #30
    3154:	2f6c6562 	svccs	0x006c6562
    3158:	6b636f64 	blvs	18deef0 <ringBuffer+0x18871e8>
    315c:	742d7265 	strtvc	r7, [sp], #-613	; 0xfffffd9b
    3160:	74737572 	ldrbtvc	r7, [r3], #-1394	; 0xfffffa8e
    3164:	6d612d79 	stclvs	13, cr2, [r1, #-484]!	; 0xfffffe1c
    3168:	2d343664 	ldccs	6, cr3, [r4, #-400]!	; 0xfffffe70
    316c:	67776374 			; <UNDEFINED> instruction: 0x67776374
    3170:	6975622d 	ldmdbvs	r5!, {r0, r2, r3, r5, r9, sp, lr}^
    3174:	742f646c 	strtvc	r6, [pc], #-1132	; 317c <_init-0xd9a4>
    3178:	65677261 	strbvs	r7, [r7, #-609]!	; 0xfffffd9f
    317c:	72612f74 	rsbvc	r2, r1, #116, 30	; 0x1d0
    3180:	696c2d6d 	stmdbvs	ip!, {r0, r2, r3, r5, r6, r8, sl, fp, sp}^
    3184:	2d78756e 	cfldr64cs	mvdx7, [r8, #-440]!	; 0xfffffe48
    3188:	65756e67 	ldrbvs	r6, [r5, #-3687]!	; 0xfffff199
    318c:	68696261 	stmdavs	r9!, {r0, r5, r6, r9, sp, lr}^
    3190:	6e732f66 	cdpvs	15, 7, cr2, cr3, cr6, {3}
    3194:	68737061 	ldmdavs	r3!, {r0, r5, r6, ip, sp, lr}^
    3198:	2f73746f 	svccs	0x0073746f
    319c:	62696c67 	rsbvs	r6, r9, #26368	; 0x6700
    31a0:	69672e63 	stmdbvs	r7!, {r0, r1, r5, r6, r9, sl, fp, sp}^
    31a4:	696c7e74 	stmdbvs	ip!, {r2, r4, r5, r6, r9, sl, fp, ip, sp, lr}^
    31a8:	6f72616e 	svcvs	0x0072616e
    31ac:	322e327e 	eorcc	r3, lr, #-536870905	; 0xe0000007
    31b0:	616d7e33 	cmnvs	sp, r3, lsr lr
    31b4:	72657473 	rsbvc	r7, r5, #1929379840	; 0x73000000
    31b8:	7573632f 	ldrbvc	r6, [r3, #-815]!	; 0xfffffcd1
    31bc:	554e4700 	strbpl	r4, [lr, #-1792]	; 0xfffff900
    31c0:	20534120 	subscs	r4, r3, r0, lsr #2
    31c4:	37322e32 			; <UNDEFINED> instruction: 0x37322e32
    31c8:	0100302e 	tsteq	r0, lr, lsr #32
    31cc:	地址 0x00000000000031cc 越界。


Disassembly of section .debug_abbrev:

00000000 <.debug_abbrev>:
   0:	25011101 	strcs	r1, [r1, #-257]	; 0xfffffeff
   4:	0305130e 	movweq	r1, #21262	; 0x530e
   8:	1b17100e 	blne	5c4048 <ringBuffer+0x56c340>
   c:	5501110e 	strpl	r1, [r1, #-270]	; 0xfffffef2
  10:	02000017 	andeq	r0, r0, #23
  14:	0e030034 	mcreq	0, 0, r0, cr3, cr4, {1}
  18:	193f1349 	ldmdbne	pc!, {r0, r3, r6, r8, r9, ip}	; <UNPREDICTABLE>
  1c:	0b3b0b3a 	bleq	ec2d0c <ringBuffer+0xe6b004>
  20:	00001802 	andeq	r1, r0, r2, lsl #16
  24:	03002403 	movweq	r2, #1027	; 0x403
  28:	0b0b3e0e 	bleq	2cf868 <ringBuffer+0x277b60>
  2c:	0400000b 	streq	r0, [r0], #-11
  30:	13490101 	movtne	r0, #37121	; 0x9101
  34:	21050000 	mrscs	r0, (UNDEF: 5)
  38:	37134900 	ldrcc	r4, [r3, -r0, lsl #18]
  3c:	0600000b 	streq	r0, [r0], -fp
  40:	0e030024 	cdpeq	0, 0, cr0, cr3, cr4, {1}
  44:	0b3e0b0b 	bleq	f82c78 <ringBuffer+0xf2af70>
  48:	26070000 	strcs	r0, [r7], -r0
  4c:	00134900 	andseq	r4, r3, r0, lsl #18
  50:	00160800 	andseq	r0, r6, r0, lsl #16
  54:	0e031349 	cdpeq	3, 0, cr1, cr3, cr9, {2}
  58:	0b3b0b3a 	bleq	ec2d48 <ringBuffer+0xe6b040>
  5c:	13090000 	movwne	r0, #36864	; 0x9000
  60:	0b0e0301 	bleq	380c6c <ringBuffer+0x328f64>
  64:	3b0b3a0b 	blcc	2ce898 <ringBuffer+0x276b90>
  68:	0a00000b 	beq	9c <_init-0x10a84>
  6c:	0e03000d 	cdpeq	0, 0, cr0, cr3, cr13, {0}
  70:	0b3a1349 	bleq	e84d9c <ringBuffer+0xe2d094>
  74:	0b380b3b 	bleq	e02d68 <ringBuffer+0xdab060>
  78:	040b0000 	streq	r0, [fp], #-0
  7c:	3a0b0b01 	bcc	2c2c88 <ringBuffer+0x26af80>
  80:	000b3b0b 	andeq	r3, fp, fp, lsl #22
  84:	00280c00 	eoreq	r0, r8, r0, lsl #24
  88:	0d1c0e03 	ldceq	14, cr0, [ip, #-12]
  8c:	2e0d0000 	cdpcs	0, 0, cr0, cr13, cr0, {0}
  90:	12011100 	andne	r1, r1, #0, 2
  94:	03184006 	tsteq	r8, #6
  98:	3b0b3a0e 	blcc	2ce8d8 <ringBuffer+0x276bd0>
  9c:	00193f0b 	andseq	r3, r9, fp, lsl #30
  a0:	012e0e00 			; <UNDEFINED> instruction: 0x012e0e00
  a4:	06120111 			; <UNDEFINED> instruction: 0x06120111
  a8:	0e031840 	cdpeq	8, 0, cr1, cr3, cr0, {2}
  ac:	0b3b0b3a 	bleq	ec2d9c <ringBuffer+0xe6b094>
  b0:	193f1927 	ldmdbne	pc!, {r0, r1, r2, r5, r8, fp, ip}	; <UNPREDICTABLE>
  b4:	050f0000 	streq	r0, [pc, #-0]	; bc <_init-0x10a64>
  b8:	03180200 	tsteq	r8, #0, 4
  bc:	3b0b3a0e 	blcc	2ce8fc <ringBuffer+0x276bf4>
  c0:	0013490b 	andseq	r4, r3, fp, lsl #18
  c4:	00341000 	eorseq	r1, r4, r0
  c8:	0e031802 	cdpeq	8, 0, cr1, cr3, cr2, {0}
  cc:	0b3b0b3a 	bleq	ec2dbc <ringBuffer+0xe6b0b4>
  d0:	00001049 	andeq	r1, r0, r9, asr #32
  d4:	11012e11 	tstne	r1, r1, lsl lr
  d8:	40061201 	andmi	r1, r6, r1, lsl #4
  dc:	3a0e0318 	bcc	380d44 <ringBuffer+0x32903c>
  e0:	3f0b3b0b 	svccc	0x000b3b0b
  e4:	12000019 	andne	r0, r0, #25
  e8:	0111010b 	tsteq	r1, fp, lsl #2
  ec:	00000612 	andeq	r0, r0, r2, lsl r6
  f0:	02003413 	andeq	r3, r0, #318767104	; 0x13000000
  f4:	3a0e0318 	bcc	380d5c <ringBuffer+0x329054>
  f8:	490b3b0b 	stmdbmi	fp, {r0, r1, r3, r8, r9, fp, ip, sp}
  fc:	14000013 	strne	r0, [r0], #-19	; 0xffffffed
 100:	18020034 	stmdane	r2, {r2, r4, r5}
 104:	0b3a0e03 	bleq	e83918 <ringBuffer+0xe2bc10>
 108:	1349053b 	movtne	r0, #38203	; 0x953b
 10c:	0b150000 	bleq	540114 <ringBuffer+0x4e840c>
 110:	00175501 	andseq	r5, r7, r1, lsl #10
 114:	012e1600 			; <UNDEFINED> instruction: 0x012e1600
 118:	06120111 			; <UNDEFINED> instruction: 0x06120111
 11c:	0e031840 	cdpeq	8, 0, cr1, cr3, cr0, {2}
 120:	053b0b3a 	ldreq	r0, [fp, #-2874]!	; 0xfffff4c6
 124:	0000193f 	andeq	r1, r0, pc, lsr r9
 128:	11012e17 	tstne	r1, r7, lsl lr
 12c:	40061201 	andmi	r1, r6, r1, lsl #4
 130:	3a0e0318 	bcc	380d98 <ringBuffer+0x329090>
 134:	27053b0b 	strcs	r3, [r5, -fp, lsl #22]
 138:	3f134919 	svccc	0x00134919
 13c:	18000019 	stmdane	r0, {r0, r3, r4}
 140:	18020005 	stmdane	r2, {r0, r2}
 144:	0b3a0e03 	bleq	e83958 <ringBuffer+0xe2bc50>
 148:	1349053b 	movtne	r0, #38203	; 0x953b
 14c:	2e190000 	cdpcs	0, 1, cr0, cr9, cr0, {0}
 150:	12011101 	andne	r1, r1, #1073741824	; 0x40000000
 154:	03184006 	tsteq	r8, #6
 158:	3b0b3a0e 	blcc	2ce998 <ringBuffer+0x276c90>
 15c:	3f192705 	svccc	0x00192705
 160:	1a000019 	bne	1cc <_init-0x10954>
 164:	1349000f 	movtne	r0, #36879	; 0x900f
 168:	151b0000 	ldrne	r0, [fp, #-0]
 16c:	00192701 	andseq	r2, r9, r1, lsl #14
 170:	00051c00 	andeq	r1, r5, r0, lsl #24
 174:	00001349 	andeq	r1, r0, r9, asr #6
 178:	00000f1d 	andeq	r0, r0, sp, lsl pc
 17c:	00051e00 	andeq	r1, r5, r0, lsl #28
 180:	0e031802 	cdpeq	8, 0, cr1, cr3, cr2, {0}
 184:	0b3b0b3a 	bleq	ec2e74 <ringBuffer+0xe6b16c>
 188:	00001049 	andeq	r1, r0, r9, asr #32
 18c:	11012e1f 	tstne	r1, pc, lsl lr
 190:	40061201 	andmi	r1, r6, r1, lsl #4
 194:	3a0e0318 	bcc	380dfc <ringBuffer+0x3290f4>
 198:	270b3b0b 	strcs	r3, [fp, -fp, lsl #22]
 19c:	3f104919 	svccc	0x00104919
 1a0:	20000019 	andcs	r0, r0, r9, lsl r0
 1a4:	0111012e 	tsteq	r1, lr, lsr #2
 1a8:	18400612 	stmdane	r0, {r1, r4, r9, sl}^
 1ac:	0b3a0e03 	bleq	e839c0 <ringBuffer+0xe2bcb8>
 1b0:	10490b3b 	subne	r0, r9, fp, lsr fp
 1b4:	0000193f 	andeq	r1, r0, pc, lsr r9
 1b8:	11012e21 	tstne	r1, r1, lsr #28
 1bc:	40061201 	andmi	r1, r6, r1, lsl #4
 1c0:	3a0e0318 	bcc	380e28 <ringBuffer+0x329120>
 1c4:	490b3b0b 	stmdbmi	fp, {r0, r1, r3, r8, r9, fp, ip, sp}
 1c8:	00193f13 	andseq	r3, r9, r3, lsl pc
 1cc:	00162200 	andseq	r2, r6, r0, lsl #4
 1d0:	0e031049 	cdpeq	0, 0, cr1, cr3, cr9, {2}
 1d4:	0b3b0b3a 	bleq	ec2ec4 <ringBuffer+0xe6b1bc>
 1d8:	11230000 			; <UNDEFINED> instruction: 0x11230000
 1dc:	130e2501 	movwne	r2, #58625	; 0xe501
 1e0:	100e0305 	andne	r0, lr, r5, lsl #6
 1e4:	110e1b17 	tstne	lr, r7, lsl fp
 1e8:	00061201 	andeq	r1, r6, r1, lsl #4
 1ec:	002e2400 	eoreq	r2, lr, r0, lsl #8
 1f0:	06120111 			; <UNDEFINED> instruction: 0x06120111
 1f4:	0e031840 	cdpeq	8, 0, cr1, cr3, cr0, {2}
 1f8:	0b3b0b3a 	bleq	ec2ee8 <ringBuffer+0xe6b1e0>
 1fc:	193f1927 	ldmdbne	pc!, {r0, r1, r2, r5, r8, fp, ip}	; <UNPREDICTABLE>
 200:	0d250000 	stceq	0, cr0, [r5, #-0]
 204:	490e0300 	stmdbmi	lr, {r8, r9}
 208:	3b0b3a10 	blcc	2cea50 <ringBuffer+0x276d48>
 20c:	000b380b 	andeq	r3, fp, fp, lsl #16
 210:	11010000 	mrsne	r0, (UNDEF: 1)
 214:	130e2501 	movwne	r2, #58625	; 0xe501
 218:	1b0e030b 	blne	380e4c <ringBuffer+0x329144>
 21c:	1201110e 	andne	r1, r1, #-2147483645	; 0x80000003
 220:	00171006 	andseq	r1, r7, r6
 224:	00240200 	eoreq	r0, r4, r0, lsl #4
 228:	0b3e0b0b 	bleq	f82e5c <ringBuffer+0xf2b154>
 22c:	00000e03 	andeq	r0, r0, r3, lsl #28
 230:	0b002403 	bleq	9244 <_init-0x78dc>
 234:	030b3e0b 	movweq	r3, #48651	; 0xbe0b
 238:	04000008 	streq	r0, [r0], #-8
 23c:	0e030016 	mcreq	0, 0, r0, cr3, cr6, {0}
 240:	0b3b0b3a 	bleq	ec2f30 <ringBuffer+0xe6b228>
 244:	00001349 	andeq	r1, r0, r9, asr #6
 248:	49002605 	stmdbmi	r0, {r0, r2, r9, sl, sp}
 24c:	06000013 			; <UNDEFINED> instruction: 0x06000013
 250:	0b0b000f 	bleq	2c0294 <ringBuffer+0x26858c>
 254:	00001349 	andeq	r1, r0, r9, asr #6
 258:	0b000f07 	bleq	3e7c <_init-0xcca4>
 25c:	0800000b 	stmdaeq	r0, {r0, r1, r3}
 260:	0e030113 	mcreq	1, 0, r0, cr3, cr3, {0}
 264:	0b3a0b0b 	bleq	e82e98 <ringBuffer+0xe2b190>
 268:	13010b3b 	movwne	r0, #6971	; 0x1b3b
 26c:	0d090000 	stceq	0, cr0, [r9, #-0]
 270:	3a0e0300 	bcc	380e78 <ringBuffer+0x329170>
 274:	490b3b0b 	stmdbmi	fp, {r0, r1, r3, r8, r9, fp, ip, sp}
 278:	000b3813 	andeq	r3, fp, r3, lsl r8
 27c:	000d0a00 	andeq	r0, sp, r0, lsl #20
 280:	0b3a0e03 	bleq	e83a94 <ringBuffer+0xe2bd8c>
 284:	1349053b 	movtne	r0, #38203	; 0x953b
 288:	00000b38 	andeq	r0, r0, r8, lsr fp
 28c:	0300160b 	movweq	r1, #1547	; 0x60b
 290:	3b0b3a0e 	blcc	2cead0 <ringBuffer+0x276dc8>
 294:	0c00000b 	stceq	0, cr0, [r0], {11}
 298:	13490101 	movtne	r0, #37121	; 0x9101
 29c:	00001301 	andeq	r1, r0, r1, lsl #6
 2a0:	4900210d 	stmdbmi	r0, {r0, r2, r3, r8, sp}
 2a4:	000b2f13 	andeq	r2, fp, r3, lsl pc
 2a8:	00130e00 	andseq	r0, r3, r0, lsl #28
 2ac:	193c0e03 	ldmdbne	ip!, {r0, r1, r9, sl, fp}
 2b0:	340f0000 	strcc	r0, [pc], #-0	; 2b8 <_init-0x10868>
 2b4:	3a0e0300 	bcc	380ebc <ringBuffer+0x3291b4>
 2b8:	49053b0b 	stmdbmi	r5, {r0, r1, r3, r8, r9, fp, ip, sp}
 2bc:	3c193f13 	ldccc	15, cr3, [r9], {19}
 2c0:	10000019 	andne	r0, r0, r9, lsl r0
 2c4:	0e030034 	mcreq	0, 0, r0, cr3, cr4, {1}
 2c8:	0b3b0b3a 	bleq	ec2fb8 <ringBuffer+0xe6b2b0>
 2cc:	193f1349 	ldmdbne	pc!, {r0, r3, r6, r8, r9, ip}	; <UNPREDICTABLE>
 2d0:	0000193c 	andeq	r1, r0, ip, lsr r9
 2d4:	00002111 	andeq	r2, r0, r1, lsl r1
 2d8:	01041200 	mrseq	r1, R12_usr
 2dc:	0b0b0e03 	bleq	2c3af0 <ringBuffer+0x26bde8>
 2e0:	0b3a1349 	bleq	e8500c <ringBuffer+0xe2d304>
 2e4:	13010b3b 	movwne	r0, #6971	; 0x1b3b
 2e8:	28130000 	ldmdacs	r3, {}	; <UNPREDICTABLE>
 2ec:	1c0e0300 	stcne	3, cr0, [lr], {-0}
 2f0:	1400000b 	strne	r0, [r0], #-11
 2f4:	0803000d 	stmdaeq	r3, {r0, r2, r3}
 2f8:	0b3b0b3a 	bleq	ec2fe8 <ringBuffer+0xe6b2e0>
 2fc:	0b381349 	bleq	e05028 <ringBuffer+0xdad320>
 300:	34150000 	ldrcc	r0, [r5], #-0
 304:	3a0e0300 	bcc	380f0c <ringBuffer+0x329204>
 308:	490b3b0b 	stmdbmi	fp, {r0, r1, r3, r8, r9, fp, ip, sp}
 30c:	00180213 	andseq	r0, r8, r3, lsl r2
 310:	012e1600 			; <UNDEFINED> instruction: 0x012e1600
 314:	0e03193f 			; <UNDEFINED> instruction: 0x0e03193f
 318:	053b0b3a 	ldreq	r0, [fp, #-2874]!	; 0xfffff4c6
 31c:	13491927 	movtne	r1, #39207	; 0x9927
 320:	06120111 			; <UNDEFINED> instruction: 0x06120111
 324:	42961840 	addsmi	r1, r6, #64, 16	; 0x400000
 328:	00130119 	andseq	r0, r3, r9, lsl r1
 32c:	00051700 	andeq	r1, r5, r0, lsl #14
 330:	0b3a0803 	bleq	e82344 <ringBuffer+0xe2a63c>
 334:	1349053b 	movtne	r0, #38203	; 0x953b
 338:	00001802 	andeq	r1, r0, r2, lsl #16
 33c:	03000518 	movweq	r0, #1304	; 0x518
 340:	3b0b3a0e 	blcc	2ceb80 <ringBuffer+0x276e78>
 344:	02134905 	andseq	r4, r3, #81920	; 0x14000
 348:	19000018 	stmdbne	r0, {r3, r4}
 34c:	08030034 	stmdaeq	r3, {r2, r4, r5}
 350:	053b0b3a 	ldreq	r0, [fp, #-2874]!	; 0xfffff4c6
 354:	18021349 	stmdane	r2, {r0, r3, r6, r8, r9, ip}
 358:	261a0000 	ldrcs	r0, [sl], -r0
 35c:	1b000000 	blne	364 <_init-0x107bc>
 360:	193f012e 	ldmdbne	pc!, {r1, r2, r3, r5, r8}	; <UNPREDICTABLE>
 364:	0b3a0e03 	bleq	e83b78 <ringBuffer+0xe2be70>
 368:	19270b3b 	stmdbne	r7!, {r0, r1, r3, r4, r5, r8, r9, fp}
 36c:	01111349 	tsteq	r1, r9, asr #6
 370:	18400612 	stmdane	r0, {r1, r4, r9, sl}^
 374:	01194296 			; <UNDEFINED> instruction: 0x01194296
 378:	1c000013 	stcne	0, cr0, [r0], {19}
 37c:	08030005 	stmdaeq	r3, {r0, r2}
 380:	0b3b0b3a 	bleq	ec3070 <ringBuffer+0xe6b368>
 384:	18021349 	stmdane	r2, {r0, r3, r6, r8, r9, ip}
 388:	051d0000 	ldreq	r0, [sp, #-0]
 38c:	3a0e0300 	bcc	380f94 <ringBuffer+0x32928c>
 390:	490b3b0b 	stmdbmi	fp, {r0, r1, r3, r8, r9, fp, ip, sp}
 394:	00180213 	andseq	r0, r8, r3, lsl r2
 398:	00341e00 	eorseq	r1, r4, r0, lsl #28
 39c:	0b3a0803 	bleq	e823b0 <ringBuffer+0xe2a6a8>
 3a0:	13490b3b 	movtne	r0, #39739	; 0x9b3b
 3a4:	00001802 	andeq	r1, r0, r2, lsl #16
 3a8:	11010b1f 	tstne	r1, pc, lsl fp
 3ac:	00061201 	andeq	r1, r6, r1, lsl #4
 3b0:	012e2000 			; <UNDEFINED> instruction: 0x012e2000
 3b4:	0b3a0e03 	bleq	e83bc8 <ringBuffer+0xe2bec0>
 3b8:	19270b3b 	stmdbne	r7!, {r0, r1, r3, r4, r5, r8, r9, fp}
 3bc:	06120111 			; <UNDEFINED> instruction: 0x06120111
 3c0:	42961840 	addsmi	r1, r6, #64, 16	; 0x400000
 3c4:	00130119 	andseq	r0, r3, r9, lsl r1
 3c8:	012e2100 			; <UNDEFINED> instruction: 0x012e2100
 3cc:	0b3a0e03 	bleq	e83be0 <ringBuffer+0xe2bed8>
 3d0:	19270b3b 	stmdbne	r7!, {r0, r1, r3, r4, r5, r8, r9, fp}
 3d4:	06120111 			; <UNDEFINED> instruction: 0x06120111
 3d8:	42971840 	addsmi	r1, r7, #64, 16	; 0x400000
 3dc:	00130119 	andseq	r0, r3, r9, lsl r1
 3e0:	012e2200 			; <UNDEFINED> instruction: 0x012e2200
 3e4:	0b3a0e03 	bleq	e83bf8 <ringBuffer+0xe2bef0>
 3e8:	19270b3b 	stmdbne	r7!, {r0, r1, r3, r4, r5, r8, r9, fp}
 3ec:	01111349 	tsteq	r1, r9, asr #6
 3f0:	18400612 	stmdane	r0, {r1, r4, r9, sl}^
 3f4:	01194297 			; <UNDEFINED> instruction: 0x01194297
 3f8:	23000013 	movwcs	r0, #19
 3fc:	19270115 	stmdbne	r7!, {r0, r2, r4, r8}
 400:	13011349 	movwne	r1, #4937	; 0x1349
 404:	05240000 	streq	r0, [r4, #-0]!
 408:	00134900 	andseq	r4, r3, r0, lsl #18
 40c:	00352500 	eorseq	r2, r5, r0, lsl #10
 410:	00001349 	andeq	r1, r0, r9, asr #6
 414:	03012e26 	movweq	r2, #7718	; 0x1e26
 418:	3b0b3a0e 	blcc	2cec58 <ringBuffer+0x276f50>
 41c:	4919270b 	ldmdbmi	r9, {r0, r1, r3, r8, r9, sl, sp}
 420:	12011113 	andne	r1, r1, #-1073741820	; 0xc0000004
 424:	97184006 	ldrls	r4, [r8, -r6]
 428:	00001942 	andeq	r1, r0, r2, asr #18
 42c:	01110100 	tsteq	r1, r0, lsl #2
 430:	0b130e25 	bleq	4c3ccc <ringBuffer+0x46bfc4>
 434:	0e1b0e03 	cdpeq	14, 1, cr0, cr11, cr3, {0}
 438:	06120111 			; <UNDEFINED> instruction: 0x06120111
 43c:	00001710 	andeq	r1, r0, r0, lsl r7
 440:	03001602 	movweq	r1, #1538	; 0x602
 444:	3b0b3a0e 	blcc	2cec84 <ringBuffer+0x276f7c>
 448:	0013490b 	andseq	r4, r3, fp, lsl #18
 44c:	00240300 	eoreq	r0, r4, r0, lsl #6
 450:	0b3e0b0b 	bleq	f83084 <ringBuffer+0xf2b37c>
 454:	00000e03 	andeq	r0, r0, r3, lsl #28
 458:	0b002404 	bleq	9470 <_init-0x76b0>
 45c:	030b3e0b 	movweq	r3, #48651	; 0xbe0b
 460:	05000008 	streq	r0, [r0, #-8]
 464:	0b0b000f 	bleq	2c04a8 <ringBuffer+0x2687a0>
 468:	0f060000 	svceq	0x00060000
 46c:	490b0b00 	stmdbmi	fp, {r8, r9, fp}
 470:	07000013 	smladeq	r0, r3, r0, r0
 474:	13490026 	movtne	r0, #36902	; 0x9026
 478:	13080000 	movwne	r0, #32768	; 0x8000
 47c:	0b0e0301 	bleq	381088 <ringBuffer+0x329380>
 480:	3b0b3a0b 	blcc	2cecb4 <ringBuffer+0x276fac>
 484:	0013010b 	andseq	r0, r3, fp, lsl #2
 488:	000d0900 	andeq	r0, sp, r0, lsl #18
 48c:	0b3a0e03 	bleq	e83ca0 <ringBuffer+0xe2bf98>
 490:	13490b3b 	movtne	r0, #39739	; 0x9b3b
 494:	00000b38 	andeq	r0, r0, r8, lsr fp
 498:	03000d0a 	movweq	r0, #3338	; 0xd0a
 49c:	3b0b3a0e 	blcc	2cecdc <ringBuffer+0x276fd4>
 4a0:	38134905 	ldmdacc	r3, {r0, r2, r8, fp, lr}
 4a4:	0b00000b 	bleq	4d8 <_init-0x10648>
 4a8:	0e030016 	mcreq	0, 0, r0, cr3, cr6, {0}
 4ac:	0b3b0b3a 	bleq	ec319c <ringBuffer+0xe6b494>
 4b0:	010c0000 	mrseq	r0, (UNDEF: 12)
 4b4:	01134901 	tsteq	r3, r1, lsl #18
 4b8:	0d000013 	stceq	0, cr0, [r0, #-76]	; 0xffffffb4
 4bc:	13490021 	movtne	r0, #36897	; 0x9021
 4c0:	00000b2f 	andeq	r0, r0, pc, lsr #22
 4c4:	0300130e 	movweq	r1, #782	; 0x30e
 4c8:	00193c0e 	andseq	r3, r9, lr, lsl #24
 4cc:	00340f00 	eorseq	r0, r4, r0, lsl #30
 4d0:	0b3a0e03 	bleq	e83ce4 <ringBuffer+0xe2bfdc>
 4d4:	1349053b 	movtne	r0, #38203	; 0x953b
 4d8:	193c193f 	ldmdbne	ip!, {r0, r1, r2, r3, r4, r5, r8, fp, ip}
 4dc:	34100000 	ldrcc	r0, [r0], #-0
 4e0:	3a0e0300 	bcc	3810e8 <ringBuffer+0x3293e0>
 4e4:	490b3b0b 	stmdbmi	fp, {r0, r1, r3, r8, r9, fp, ip, sp}
 4e8:	3c193f13 	ldccc	15, cr3, [r9], {19}
 4ec:	11000019 	tstne	r0, r9, lsl r0
 4f0:	00000021 	andeq	r0, r0, r1, lsr #32
 4f4:	0b011312 	bleq	45144 <call_weak_fn>
 4f8:	3b0b3a0b 	blcc	2ced2c <ringBuffer+0x277024>
 4fc:	0013010b 	andseq	r0, r3, fp, lsl #2
 500:	01131300 	tsteq	r3, r0, lsl #6
 504:	0b3a060b 	bleq	e81d38 <ringBuffer+0xe2a030>
 508:	13010b3b 	movwne	r0, #6971	; 0x1b3b
 50c:	0d140000 	ldceq	0, cr0, [r4, #-0]
 510:	3a0e0300 	bcc	381118 <ringBuffer+0x329410>
 514:	490b3b0b 	stmdbmi	fp, {r0, r1, r3, r8, r9, fp, ip, sp}
 518:	00063813 	andeq	r3, r6, r3, lsl r8
 51c:	00211500 	eoreq	r1, r1, r0, lsl #10
 520:	062f1349 	strteq	r1, [pc], -r9, asr #6
 524:	34160000 	ldrcc	r0, [r6], #-0
 528:	3a0e0300 	bcc	381130 <ringBuffer+0x329428>
 52c:	490b3b0b 	stmdbmi	fp, {r0, r1, r3, r8, r9, fp, ip, sp}
 530:	02193f13 	andseq	r3, r9, #19, 30	; 0x4c
 534:	17000018 	smladne	r0, r8, r0, r0
 538:	0e030104 	adfeqs	f0, f3, f4
 53c:	13490b0b 	movtne	r0, #39691	; 0x9b0b
 540:	0b3b0b3a 	bleq	ec3230 <ringBuffer+0xe6b528>
 544:	00001301 	andeq	r1, r0, r1, lsl #6
 548:	03002818 	movweq	r2, #2072	; 0x818
 54c:	000b1c08 	andeq	r1, fp, r8, lsl #24
 550:	00341900 	eorseq	r1, r4, r0, lsl #18
 554:	0b3a0e03 	bleq	e83d68 <ringBuffer+0xe2c060>
 558:	1349053b 	movtne	r0, #38203	; 0x953b
 55c:	1802193f 	stmdane	r2, {r0, r1, r2, r3, r4, r5, r8, fp, ip}
 560:	341a0000 	ldrcc	r0, [sl], #-0
 564:	3a080300 	bcc	20116c <ringBuffer+0x1a9464>
 568:	49053b0b 	stmdbmi	r5, {r0, r1, r3, r8, r9, fp, ip, sp}
 56c:	02193f13 	andseq	r3, r9, #19, 30	; 0x4c
 570:	1b000018 	blne	5d8 <_init-0x10548>
 574:	193f002e 	ldmdbne	pc!, {r1, r2, r3, r5}	; <UNPREDICTABLE>
 578:	0b3a0e03 	bleq	e83d8c <ringBuffer+0xe2c084>
 57c:	0111053b 	tsteq	r1, fp, lsr r5
 580:	18400612 	stmdane	r0, {r1, r4, r9, sl}^
 584:	00194296 	mulseq	r9, r6, r2
 588:	012e1c00 			; <UNDEFINED> instruction: 0x012e1c00
 58c:	0e03193f 			; <UNDEFINED> instruction: 0x0e03193f
 590:	053b0b3a 	ldreq	r0, [fp, #-2874]!	; 0xfffff4c6
 594:	13491927 	movtne	r1, #39207	; 0x9927
 598:	06120111 			; <UNDEFINED> instruction: 0x06120111
 59c:	42971840 	addsmi	r1, r7, #64, 16	; 0x400000
 5a0:	00130119 	andseq	r0, r3, r9, lsl r1
 5a4:	00051d00 	andeq	r1, r5, r0, lsl #26
 5a8:	0b3a0e03 	bleq	e83dbc <ringBuffer+0xe2c0b4>
 5ac:	1349053b 	movtne	r0, #38203	; 0x953b
 5b0:	00001802 	andeq	r1, r0, r2, lsl #16
 5b4:	3f012e1e 	svccc	0x00012e1e
 5b8:	3a0e0319 	bcc	381224 <ringBuffer+0x32951c>
 5bc:	27053b0b 	strcs	r3, [r5, -fp, lsl #22]
 5c0:	12011119 	andne	r1, r1, #1073741830	; 0x40000006
 5c4:	96184006 	ldrls	r4, [r8], -r6
 5c8:	13011942 	movwne	r1, #6466	; 0x1942
 5cc:	341f0000 	ldrcc	r0, [pc], #-0	; 5d4 <_init-0x1054c>
 5d0:	3a0e0300 	bcc	3811d8 <ringBuffer+0x3294d0>
 5d4:	49053b0b 	stmdbmi	r5, {r0, r1, r3, r8, r9, fp, ip, sp}
 5d8:	00180213 	andseq	r0, r8, r3, lsl r2
 5dc:	012e2000 			; <UNDEFINED> instruction: 0x012e2000
 5e0:	0e03193f 			; <UNDEFINED> instruction: 0x0e03193f
 5e4:	0b3b0b3a 	bleq	ec32d4 <ringBuffer+0xe6b5cc>
 5e8:	01111927 	tsteq	r1, r7, lsr #18
 5ec:	18400612 	stmdane	r0, {r1, r4, r9, sl}^
 5f0:	01194296 			; <UNDEFINED> instruction: 0x01194296
 5f4:	21000013 	tstcs	r0, r3, lsl r0
 5f8:	0e030005 	cdpeq	0, 0, cr0, cr3, cr5, {0}
 5fc:	0b3b0b3a 	bleq	ec32ec <ringBuffer+0xe6b5e4>
 600:	18021349 	stmdane	r2, {r0, r3, r6, r8, r9, ip}
 604:	34220000 	strtcc	r0, [r2], #-0
 608:	3a0e0300 	bcc	381210 <ringBuffer+0x329508>
 60c:	490b3b0b 	stmdbmi	fp, {r0, r1, r3, r8, r9, fp, ip, sp}
 610:	00180213 	andseq	r0, r8, r3, lsl r2
 614:	010b2300 	mrseq	r2, (UNDEF: 59)
 618:	06120111 			; <UNDEFINED> instruction: 0x06120111
 61c:	2e240000 	cdpcs	0, 2, cr0, cr4, cr0, {0}
 620:	03193f01 	tsteq	r9, #1, 30
 624:	3b0b3a0e 	blcc	2cee64 <ringBuffer+0x27715c>
 628:	4919270b 	ldmdbmi	r9, {r0, r1, r3, r8, r9, sl, sp}
 62c:	12011113 	andne	r1, r1, #-1073741820	; 0xc0000004
 630:	97184006 	ldrls	r4, [r8, -r6]
 634:	13011942 	movwne	r1, #6466	; 0x1942
 638:	34250000 	strtcc	r0, [r5], #-0
 63c:	3a080300 	bcc	201244 <ringBuffer+0x1a953c>
 640:	490b3b0b 	stmdbmi	fp, {r0, r1, r3, r8, r9, fp, ip, sp}
 644:	00180213 	andseq	r0, r8, r3, lsl r2
 648:	012e2600 			; <UNDEFINED> instruction: 0x012e2600
 64c:	0e03193f 			; <UNDEFINED> instruction: 0x0e03193f
 650:	0b3b0b3a 	bleq	ec3340 <ringBuffer+0xe6b638>
 654:	01111349 	tsteq	r1, r9, asr #6
 658:	18400612 	stmdane	r0, {r1, r4, r9, sl}^
 65c:	01194297 			; <UNDEFINED> instruction: 0x01194297
 660:	27000013 	smladcs	r0, r3, r0, r0
 664:	0111010b 	tsteq	r1, fp, lsl #2
 668:	13010612 	movwne	r0, #5650	; 0x1612
 66c:	2e280000 	cdpcs	0, 2, cr0, cr8, cr0, {0}
 670:	03193f01 	tsteq	r9, #1, 30
 674:	3b0b3a08 	blcc	2cee9c <ringBuffer+0x277194>
 678:	4919270b 	ldmdbmi	r9, {r0, r1, r3, r8, r9, sl, sp}
 67c:	12011113 	andne	r1, r1, #-1073741820	; 0xc0000004
 680:	97184006 	ldrls	r4, [r8, -r6]
 684:	13011942 	movwne	r1, #6466	; 0x1942
 688:	2e290000 	cdpcs	0, 2, cr0, cr9, cr0, {0}
 68c:	03193f01 	tsteq	r9, #1, 30
 690:	3b0b3a0e 	blcc	2ceed0 <ringBuffer+0x2771c8>
 694:	4919270b 	ldmdbmi	r9, {r0, r1, r3, r8, r9, sl, sp}
 698:	12011113 	andne	r1, r1, #-1073741820	; 0xc0000004
 69c:	97184006 	ldrls	r4, [r8, -r6]
 6a0:	00001942 	andeq	r1, r0, r2, asr #18
 6a4:	00110100 	andseq	r0, r1, r0, lsl #2
 6a8:	01110610 	tsteq	r1, r0, lsl r6
 6ac:	08030112 	stmdaeq	r3, {r1, r4, r8}
 6b0:	0825081b 	stmdaeq	r5!, {r0, r1, r3, r4, fp}
 6b4:	00000513 	andeq	r0, r0, r3, lsl r5
 6b8:	00110100 	andseq	r0, r1, r0, lsl #2
 6bc:	01110610 	tsteq	r1, r0, lsl r6
 6c0:	08030112 	stmdaeq	r3, {r1, r4, r8}
 6c4:	0825081b 	stmdaeq	r5!, {r0, r1, r3, r4, fp}
 6c8:	00000513 	andeq	r0, r0, r3, lsl r5
 6cc:	01110100 	tsteq	r1, r0, lsl #2
 6d0:	0b130e25 	bleq	4c3f6c <ringBuffer+0x46c264>
 6d4:	0e1b0e03 	cdpeq	14, 1, cr0, cr11, cr3, {0}
 6d8:	06120111 			; <UNDEFINED> instruction: 0x06120111
 6dc:	00001710 	andeq	r1, r0, r0, lsl r7
 6e0:	0b002402 	bleq	96f0 <_init-0x7430>
 6e4:	030b3e0b 	movweq	r3, #48651	; 0xbe0b
 6e8:	0300000e 	movweq	r0, #14
 6ec:	0b0b0024 	bleq	2c0784 <ringBuffer+0x268a7c>
 6f0:	08030b3e 	stmdaeq	r3, {r1, r2, r3, r4, r5, r8, r9, fp}
 6f4:	16040000 	strne	r0, [r4], -r0
 6f8:	3a0e0300 	bcc	381300 <ringBuffer+0x3295f8>
 6fc:	490b3b0b 	stmdbmi	fp, {r0, r1, r3, r8, r9, fp, ip, sp}
 700:	05000013 	streq	r0, [r0, #-19]	; 0xffffffed
 704:	0b0b000f 	bleq	2c0748 <ringBuffer+0x268a40>
 708:	0f060000 	svceq	0x00060000
 70c:	490b0b00 	stmdbmi	fp, {r8, r9, fp}
 710:	07000013 	smladeq	r0, r3, r0, r0
 714:	13490026 	movtne	r0, #36902	; 0x9026
 718:	34080000 	strcc	r0, [r8], #-0
 71c:	3a0e0300 	bcc	381324 <ringBuffer+0x32961c>
 720:	49053b0b 	stmdbmi	r5, {r0, r1, r3, r8, r9, fp, ip, sp}
 724:	3c193f13 	ldccc	15, cr3, [r9], {19}
 728:	09000019 	stmdbeq	r0, {r0, r3, r4}
 72c:	0e030034 	mcreq	0, 0, r0, cr3, cr4, {1}
 730:	0b3b0b3a 	bleq	ec3420 <ringBuffer+0xe6b718>
 734:	193f1349 	ldmdbne	pc!, {r0, r3, r6, r8, r9, ip}	; <UNPREDICTABLE>
 738:	0000193c 	andeq	r1, r0, ip, lsr r9
 73c:	2700150a 	strcs	r1, [r0, -sl, lsl #10]
 740:	0b000019 	bleq	7ac <_init-0x10374>
 744:	13490035 	movtne	r0, #36917	; 0x9035
 748:	010c0000 	mrseq	r0, (UNDEF: 12)
 74c:	01134901 	tsteq	r3, r1, lsl #18
 750:	0d000013 	stceq	0, cr0, [r0, #-76]	; 0xffffffb4
 754:	13490021 	movtne	r0, #36897	; 0x9021
 758:	00000b2f 	andeq	r0, r0, pc, lsr #22
 75c:	0301130e 	movweq	r1, #4878	; 0x130e
 760:	3a0b0b0e 	bcc	2c33a0 <ringBuffer+0x26b698>
 764:	010b3b0b 	tsteq	fp, fp, lsl #22
 768:	0f000013 	svceq	0x00000013
 76c:	0e03000d 	cdpeq	0, 0, cr0, cr3, cr13, {0}
 770:	0b3b0b3a 	bleq	ec3460 <ringBuffer+0xe6b758>
 774:	0b381349 	bleq	e054a0 <ringBuffer+0xdad798>
 778:	0d100000 	ldceq	0, cr0, [r0, #-0]
 77c:	3a0e0300 	bcc	381384 <ringBuffer+0x32967c>
 780:	49053b0b 	stmdbmi	r5, {r0, r1, r3, r8, r9, fp, ip, sp}
 784:	000b3813 	andeq	r3, fp, r3, lsl r8
 788:	00161100 	andseq	r1, r6, r0, lsl #2
 78c:	0b3a0e03 	bleq	e83fa0 <ringBuffer+0xe2c298>
 790:	00000b3b 	andeq	r0, r0, fp, lsr fp
 794:	03001312 	movweq	r1, #786	; 0x312
 798:	00193c0e 	andseq	r3, r9, lr, lsl #24
 79c:	00211300 	eoreq	r1, r1, r0, lsl #6
 7a0:	15140000 	ldrne	r0, [r4, #-0]
 7a4:	49192701 	ldmdbmi	r9, {r0, r8, r9, sl, sp}
 7a8:	00130113 	andseq	r0, r3, r3, lsl r1
 7ac:	00051500 	andeq	r1, r5, r0, lsl #10
 7b0:	00001349 	andeq	r1, r0, r9, asr #6
 7b4:	27011516 	smladcs	r1, r6, r5, r1
 7b8:	00130119 	andseq	r0, r3, r9, lsl r1
 7bc:	00261700 	eoreq	r1, r6, r0, lsl #14
 7c0:	13180000 	tstne	r8, #0
 7c4:	3a0b0b01 	bcc	2c33d0 <ringBuffer+0x26b6c8>
 7c8:	010b3b0b 	tsteq	fp, fp, lsl #22
 7cc:	19000013 	stmdbne	r0, {r0, r1, r4}
 7d0:	0803000d 	stmdaeq	r3, {r0, r2, r3}
 7d4:	053b0b3a 	ldreq	r0, [fp, #-2874]!	; 0xfffff4c6
 7d8:	0b381349 	bleq	e05504 <ringBuffer+0xdad7fc>
 7dc:	161a0000 	ldrne	r0, [sl], -r0
 7e0:	3a0e0300 	bcc	3813e8 <ringBuffer+0x3296e0>
 7e4:	49053b0b 	stmdbmi	r5, {r0, r1, r3, r8, r9, fp, ip, sp}
 7e8:	1b000013 	blne	83c <_init-0x102e4>
 7ec:	0b0b0113 	bleq	2c0c40 <ringBuffer+0x268f38>
 7f0:	053b0b3a 	ldreq	r0, [fp, #-2874]!	; 0xfffff4c6
 7f4:	00001301 	andeq	r1, r0, r1, lsl #6
 7f8:	0b01171c 	bleq	46470 <_dprintf+0xc>
 7fc:	3b0b3a0b 	blcc	2cf030 <ringBuffer+0x277328>
 800:	00130105 	andseq	r0, r3, r5, lsl #2
 804:	000d1d00 	andeq	r1, sp, r0, lsl #26
 808:	0b3a0e03 	bleq	e8401c <ringBuffer+0xe2c314>
 80c:	1349053b 	movtne	r0, #38203	; 0x953b
 810:	041e0000 	ldreq	r0, [lr], #-0
 814:	0b0e0301 	bleq	381420 <ringBuffer+0x329718>
 818:	3a13490b 	bcc	4d2c4c <ringBuffer+0x47af44>
 81c:	010b3b0b 	tsteq	fp, fp, lsl #22
 820:	1f000013 	svcne	0x00000013
 824:	0e030028 	cdpeq	0, 0, cr0, cr3, cr8, {1}
 828:	00000b1c 	andeq	r0, r0, ip, lsl fp
 82c:	03000d20 	movweq	r0, #3360	; 0xd20
 830:	3b0b3a08 	blcc	2cf058 <ringBuffer+0x277350>
 834:	3813490b 	ldmdacc	r3, {r0, r1, r3, r8, fp, lr}
 838:	2100000b 	tstcs	r0, fp
 83c:	060b0113 			; <UNDEFINED> instruction: 0x060b0113
 840:	0b3b0b3a 	bleq	ec3530 <ringBuffer+0xe6b828>
 844:	00001301 	andeq	r1, r0, r1, lsl #6
 848:	03000d22 	movweq	r0, #3362	; 0xd22
 84c:	3b0b3a0e 	blcc	2cf08c <ringBuffer+0x277384>
 850:	3813490b 	ldmdacc	r3, {r0, r1, r3, r8, fp, lr}
 854:	23000006 	movwcs	r0, #6
 858:	13490021 	movtne	r0, #36897	; 0x9021
 85c:	0000062f 	andeq	r0, r0, pc, lsr #12
 860:	03003424 	movweq	r3, #1060	; 0x424
 864:	3b0b3a0e 	blcc	2cf0a4 <ringBuffer+0x27739c>
 868:	3f13490b 	svccc	0x0013490b
 86c:	00180219 	andseq	r0, r8, r9, lsl r2
 870:	00342500 	eorseq	r2, r4, r0, lsl #10
 874:	0b3a0803 	bleq	e82888 <ringBuffer+0xe2ab80>
 878:	13490b3b 	movtne	r0, #39739	; 0x9b3b
 87c:	1802193f 	stmdane	r2, {r0, r1, r2, r3, r4, r5, r8, fp, ip}
 880:	2e260000 	cdpcs	0, 2, cr0, cr6, cr0, {0}
 884:	03193f01 	tsteq	r9, #1, 30
 888:	3b0b3a0e 	blcc	2cf0c8 <ringBuffer+0x2773c0>
 88c:	11192705 	tstne	r9, r5, lsl #14
 890:	40061201 	andmi	r1, r6, r1, lsl #4
 894:	19429618 	stmdbne	r2, {r3, r4, r9, sl, ip, pc}^
 898:	00001301 	andeq	r1, r0, r1, lsl #6
 89c:	03000527 	movweq	r0, #1319	; 0x527
 8a0:	3b0b3a0e 	blcc	2cf0e0 <ringBuffer+0x2773d8>
 8a4:	02134905 	andseq	r4, r3, #81920	; 0x14000
 8a8:	28000018 	stmdacs	r0, {r3, r4}
 8ac:	0e030034 	mcreq	0, 0, r0, cr3, cr4, {1}
 8b0:	053b0b3a 	ldreq	r0, [fp, #-2874]!	; 0xfffff4c6
 8b4:	18021349 	stmdane	r2, {r0, r3, r6, r8, r9, ip}
 8b8:	2e290000 	cdpcs	0, 2, cr0, cr9, cr0, {0}
 8bc:	03193f01 	tsteq	r9, #1, 30
 8c0:	3b0b3a0e 	blcc	2cf100 <ringBuffer+0x2773f8>
 8c4:	12011105 	andne	r1, r1, #1073741825	; 0x40000001
 8c8:	96184006 	ldrls	r4, [r8], -r6
 8cc:	13011942 	movwne	r1, #6466	; 0x1942
 8d0:	2e2a0000 	cdpcs	0, 2, cr0, cr10, cr0, {0}
 8d4:	03193f01 	tsteq	r9, #1, 30
 8d8:	3b0b3a0e 	blcc	2cf118 <ringBuffer+0x277410>
 8dc:	3c134905 			; <UNDEFINED> instruction: 0x3c134905
 8e0:	2b000019 	blcs	94c <_init-0x101d4>
 8e4:	00000018 	andeq	r0, r0, r8, lsl r0
 8e8:	11010b2c 	tstne	r1, ip, lsr #22
 8ec:	00061201 	andeq	r1, r6, r1, lsl #4
 8f0:	00342d00 	eorseq	r2, r4, r0, lsl #26
 8f4:	0b3a0803 	bleq	e82908 <ringBuffer+0xe2ac00>
 8f8:	1349053b 	movtne	r0, #38203	; 0x953b
 8fc:	00001802 	andeq	r1, r0, r2, lsl #16
 900:	3f012e2e 	svccc	0x00012e2e
 904:	3a0e0319 	bcc	381570 <ringBuffer+0x329868>
 908:	490b3b0b 	stmdbmi	fp, {r0, r1, r3, r8, r9, fp, ip, sp}
 90c:	12011113 	andne	r1, r1, #-1073741820	; 0xc0000004
 910:	96184006 	ldrls	r4, [r8], -r6
 914:	13011942 	movwne	r1, #6466	; 0x1942
 918:	342f0000 	strtcc	r0, [pc], #-0	; 920 <_init-0x10200>
 91c:	3a0e0300 	bcc	381524 <ringBuffer+0x32981c>
 920:	490b3b0b 	stmdbmi	fp, {r0, r1, r3, r8, r9, fp, ip, sp}
 924:	00180213 	andseq	r0, r8, r3, lsl r2
 928:	012e3000 			; <UNDEFINED> instruction: 0x012e3000
 92c:	0803193f 	stmdaeq	r3, {r0, r1, r2, r3, r4, r5, r8, fp, ip}
 930:	0b3b0b3a 	bleq	ec3620 <ringBuffer+0xe6b918>
 934:	193c1349 	ldmdbne	ip!, {r0, r3, r6, r8, r9, ip}
 938:	00001301 	andeq	r1, r0, r1, lsl #6
 93c:	11010b31 	tstne	r1, r1, lsr fp
 940:	01061201 	tsteq	r6, r1, lsl #4
 944:	32000013 	andcc	r0, r0, #19
 948:	193f012e 	ldmdbne	pc!, {r1, r2, r3, r5, r8}	; <UNPREDICTABLE>
 94c:	0b3a0e03 	bleq	e84160 <ringBuffer+0xe2c458>
 950:	1349053b 	movtne	r0, #38203	; 0x953b
 954:	1301193c 	movwne	r1, #6460	; 0x193c
 958:	2e330000 	cdpcs	0, 3, cr0, cr3, cr0, {0}
 95c:	03193f01 	tsteq	r9, #1, 30
 960:	3b0b3a0e 	blcc	2cf1a0 <ringBuffer+0x277498>
 964:	1119270b 	tstne	r9, fp, lsl #14
 968:	40061201 	andmi	r1, r6, r1, lsl #4
 96c:	19429618 	stmdbne	r2, {r3, r4, r9, sl, ip, pc}^
 970:	00001301 	andeq	r1, r0, r1, lsl #6
 974:	03000534 	movweq	r0, #1332	; 0x534
 978:	3b0b3a0e 	blcc	2cf1b8 <ringBuffer+0x2774b0>
 97c:	0213490b 	andseq	r4, r3, #180224	; 0x2c000
 980:	35000018 	strcc	r0, [r0, #-24]	; 0xffffffe8
 984:	08030034 	stmdaeq	r3, {r2, r4, r5}
 988:	0b3b0b3a 	bleq	ec3678 <ringBuffer+0xe6b970>
 98c:	18021349 	stmdane	r2, {r0, r3, r6, r8, r9, ip}
 990:	2e360000 	cdpcs	0, 3, cr0, cr6, cr0, {0}
 994:	03193f01 	tsteq	r9, #1, 30
 998:	3b0b3a0e 	blcc	2cf1d8 <ringBuffer+0x2774d0>
 99c:	1119270b 	tstne	r9, fp, lsl #14
 9a0:	40061201 	andmi	r1, r6, r1, lsl #4
 9a4:	19429718 	stmdbne	r2, {r3, r4, r8, r9, sl, ip, pc}^
 9a8:	00001301 	andeq	r1, r0, r1, lsl #6
 9ac:	03000537 	movweq	r0, #1335	; 0x537
 9b0:	3b0b3a08 	blcc	2cf1d8 <ringBuffer+0x2774d0>
 9b4:	0213490b 	andseq	r4, r3, #180224	; 0x2c000
 9b8:	38000018 	stmdacc	r0, {r3, r4}
 9bc:	193f002e 	ldmdbne	pc!, {r1, r2, r3, r5}	; <UNPREDICTABLE>
 9c0:	0b3a0e03 	bleq	e841d4 <ringBuffer+0xe2c4cc>
 9c4:	01110b3b 	tsteq	r1, fp, lsr fp
 9c8:	18400612 	stmdane	r0, {r1, r4, r9, sl}^
 9cc:	00194296 	mulseq	r9, r6, r2
 9d0:	11010000 	mrsne	r0, (UNDEF: 1)
 9d4:	11061000 	mrsne	r1, (UNDEF: 6)
 9d8:	03011201 	movweq	r1, #4609	; 0x1201
 9dc:	25081b08 	strcs	r1, [r8, #-2824]	; 0xfffff4f8
 9e0:	00051308 	andeq	r1, r5, r8, lsl #6
 9e4:	11010000 	mrsne	r0, (UNDEF: 1)
 9e8:	130e2501 	movwne	r2, #58625	; 0xe501
 9ec:	1b0e030b 	blne	381620 <ringBuffer+0x329918>
 9f0:	0017100e 	andseq	r1, r7, lr
 9f4:	00240200 	eoreq	r0, r4, r0, lsl #4
 9f8:	0b3e0b0b 	bleq	f8362c <ringBuffer+0xf2b924>
 9fc:	00000e03 	andeq	r0, r0, r3, lsl #28
 a00:	0b002403 	bleq	9a14 <_init-0x710c>
 a04:	030b3e0b 	movweq	r3, #48651	; 0xbe0b
 a08:	04000008 	streq	r0, [r0], #-8
 a0c:	13490026 	movtne	r0, #36902	; 0x9026
 a10:	34050000 	strcc	r0, [r5], #-0
 a14:	3a0e0300 	bcc	38161c <ringBuffer+0x329914>
 a18:	490b3b0b 	stmdbmi	fp, {r0, r1, r3, r8, r9, fp, ip, sp}
 a1c:	02193f13 	andseq	r3, r9, #19, 30	; 0x4c
 a20:	00000018 	andeq	r0, r0, r8, lsl r0
 a24:	10001101 	andne	r1, r0, r1, lsl #2
 a28:	03065506 	movweq	r5, #25862	; 0x6506
 a2c:	25081b08 	strcs	r1, [r8, #-2824]	; 0xfffff4f8
 a30:	00051308 	andeq	r1, r5, r8, lsl #6
 a34:	11010000 	mrsne	r0, (UNDEF: 1)
 a38:	55061000 	strpl	r1, [r6, #-0]
 a3c:	1b080306 	blne	20165c <ringBuffer+0x1a9954>
 a40:	13082508 	movwne	r2, #34056	; 0x8508
 a44:	00000005 	andeq	r0, r0, r5

Disassembly of section .debug_line:

00000000 <.debug_line>:
       0:	000005d3 	ldrdeq	r0, [r0], -r3
       4:	003d0002 	eorseq	r0, sp, r2
       8:	01010000 	mrseq	r0, (UNDEF: 1)
       c:	000d0efb 	strdeq	r0, [sp], -fp
      10:	01010101 	tsteq	r1, r1, lsl #2
      14:	01000000 	mrseq	r0, (UNDEF: 0)
      18:	2e010000 	cdpcs	0, 0, cr0, cr1, cr0, {0}
      1c:	62696c2f 	rsbvs	r6, r9, #12032	; 0x2f00
      20:	79730000 	ldmdbvc	r3!, {}^	; <UNPREDICTABLE>
      24:	676e6972 			; <UNDEFINED> instruction: 0x676e6972
      28:	6d755065 	ldclvs	0, cr5, [r5, #-404]!	; 0xfffffe6c
      2c:	00632e70 	rsbeq	r2, r3, r0, ror lr
      30:	4c000000 	stcmi	0, cr0, [r0], {-0}
      34:	69757169 	ldmdbvs	r5!, {r0, r3, r5, r6, r8, ip, sp, lr}^
      38:	79724364 	ldmdbvc	r2!, {r2, r5, r6, r8, r9, lr}^
      3c:	6c617473 	cfstrdvs	mvd7, [r1], #-460	; 0xfffffe34
      40:	0100682e 	tsteq	r0, lr, lsr #16
      44:	00000000 	andeq	r0, r0, r0
      48:	00000205 	andeq	r0, r0, r5, lsl #4
      4c:	ee030004 	cdp	0, 0, cr0, cr3, cr4, {0}
      50:	02050100 	andeq	r0, r5, #0, 2
      54:	3d08840a 	cfstrscc	mvf8, [r8, #-40]	; 0xffffffd8
      58:	0a05ae08 	beq	16b880 <ringBuffer+0x113b78>
      5c:	05152402 	ldreq	r2, [r5, #-1026]	; 0xfffffbfe
      60:	054a0602 	strbeq	r0, [sl, #-1538]	; 0xfffff9fe
      64:	02054a0a 	andeq	r4, r5, #40960	; 0xa000
      68:	060a054a 	streq	r0, [sl], -sl, asr #10
      6c:	0602054b 	streq	r0, [r2], -fp, asr #10
      70:	4a0a054a 	bmi	2815a0 <ringBuffer+0x229898>
      74:	054a0205 	strbeq	r0, [sl, #-517]	; 0xfffffdfb
      78:	054b060f 	strbeq	r0, [fp, #-1551]	; 0xfffff9f1
      7c:	054a0602 	strbeq	r0, [sl, #-1538]	; 0xfffff9fe
      80:	e508060f 	str	r0, [r8, #-1551]	; 0xfffff9f1
      84:	4a060205 	bmi	1808a0 <ringBuffer+0x128b98>
      88:	08060a05 	stmdaeq	r6, {r0, r2, r9, fp}
      8c:	060205e7 	streq	r0, [r2], -r7, ror #11
      90:	4a0a054a 	bmi	2815c0 <ringBuffer+0x2298b8>
      94:	054a0205 	strbeq	r0, [sl, #-517]	; 0xfffffdfb
      98:	054b060a 	strbeq	r0, [fp, #-1546]	; 0xfffff9f6
      9c:	054a0602 	strbeq	r0, [sl, #-1538]	; 0xfffff9fe
      a0:	02054a0a 	andeq	r4, r5, #40960	; 0xa000
      a4:	0550064a 	ldrbeq	r0, [r0, #-1610]	; 0xfffff9b6
      a8:	00058301 	andeq	r8, r5, r1, lsl #6
      ac:	ac080b03 			; <UNDEFINED> instruction: 0xac080b03
      b0:	030a1405 	movweq	r1, #41989	; 0xa405
      b4:	1205f20d 	andne	pc, r5, #-805306368	; 0xd0000000
      b8:	14054a06 	strne	r4, [r5], #-2566	; 0xfffff5fa
      bc:	8212054a 	andshi	r0, r2, #310378496	; 0x12800000
      c0:	054a0c05 	strbeq	r0, [sl, #-3077]	; 0xfffff3fb
      c4:	054b060f 	strbeq	r0, [fp, #-1551]	; 0xfffff9f1
      c8:	0f05490a 	svceq	0x0005490a
      cc:	490a054b 	stmdbmi	sl, {r0, r1, r3, r6, r8, sl}
      d0:	054b0f05 	strbeq	r0, [fp, #-3845]	; 0xfffff0fb
      d4:	05be4b11 	ldreq	r4, [lr, #2833]!	; 0xb11
      d8:	054a060f 	strbeq	r0, [sl, #-1551]	; 0xfffff9f1
      dc:	064b0605 	strbeq	r0, [fp], -r5, lsl #12
      e0:	0603054a 	streq	r0, [r3], -sl, asr #10
      e4:	0f05af08 	svceq	0x0005af08
      e8:	4b2c054f 	blmi	b0162c <ringBuffer+0xaa9924>
      ec:	4a063b05 	bmi	18ed08 <ringBuffer+0x137000>
      f0:	054a0205 	strbeq	r0, [sl, #-517]	; 0xfffffdfb
      f4:	0549060d 	strbeq	r0, [r9, #-1549]	; 0xfffff9f3
      f8:	39054b2c 	stmdbcc	r5, {r2, r3, r5, r8, r9, fp, lr}
      fc:	02054a06 	andeq	r4, r5, #24576	; 0x6000
     100:	0601054a 	streq	r0, [r1], -sl, asr #10
     104:	020005f4 	andeq	r0, r0, #244, 10	; 0x3d000000
     108:	25051428 	strcs	r1, [r5, #-1064]	; 0xfffffbd8
     10c:	1905f40a 	stmdbne	r5, {r1, r3, sl, ip, sp, lr, pc}
     110:	06058206 	streq	r8, [r5], -r6, lsl #4
     114:	061e054a 	ldreq	r0, [lr], -sl, asr #10
     118:	0021054b 	eoreq	r0, r1, fp, asr #10
     11c:	06010402 	streq	r0, [r1], -r2, lsl #8
     120:	00050582 	andeq	r0, r5, r2, lsl #11
     124:	82010402 	andhi	r0, r1, #33554432	; 0x2000000
     128:	83060305 	movwhi	r0, #25349	; 0x6305
     12c:	05133002 	ldreq	r3, [r3, #-2]
     130:	0e054c10 	mcreq	12, 0, r4, cr5, cr0, {0}
     134:	24054a06 	strcs	r4, [r5], #-2566	; 0xfffff5fa
     138:	18054d06 	stmdane	r5, {r1, r2, r8, sl, fp, lr}
     13c:	05740806 	ldrbeq	r0, [r4, #-2054]!	; 0xfffff7fa
     140:	1d054a06 	vstrne	s8, [r5, #-24]	; 0xffffffe8
     144:	20054b06 	andcs	r4, r5, r6, lsl #22
     148:	01040200 	mrseq	r0, R12_usr
     14c:	05058206 	streq	r8, [r5, #-518]	; 0xfffffdfa
     150:	01040200 	mrseq	r0, R12_usr
     154:	06170582 	ldreq	r0, [r7], -r2, lsl #11
     158:	4b0d0584 	blmi	341770 <ringBuffer+0x2e9a68>
     15c:	05491705 	strbeq	r1, [r9, #-1797]	; 0xfffff8fb
     160:	09054b0d 	stmdbeq	r5, {r0, r2, r3, r8, r9, fp, lr}
     164:	4b0b0549 	blmi	2c1690 <ringBuffer+0x269988>
     168:	054b0305 	strbeq	r0, [fp, #-773]	; 0xfffffcfb
     16c:	05ad080d 	streq	r0, [sp, #2061]!	; 0x80d
     170:	054a060b 	strbeq	r0, [sl, #-1547]	; 0xfffff9f5
     174:	76080603 	strvc	r0, [r8], -r3, lsl #12
     178:	054c1305 	strbeq	r1, [ip, #-773]	; 0xfffffcfb
     17c:	054a0611 	strbeq	r0, [sl, #-1553]	; 0xfffff9ef
     180:	3d080601 	stccc	6, cr0, [r8, #-4]
     184:	24020005 	strcs	r0, [r2], #-5
     188:	0a130514 	beq	4c15e0 <ringBuffer+0x4698d8>
     18c:	4d0e05c0 	cfstr32mi	mvfx0, [lr, #-768]	; 0xfffffd00
     190:	4a060405 	bmi	1811ac <ringBuffer+0x1294a4>
     194:	47061305 	strmi	r1, [r6, -r5, lsl #6]
     198:	05850e05 	streq	r0, [r5, #3589]	; 0xe05
     19c:	054a061e 	strbeq	r0, [sl, #-1566]	; 0xfffff9e2
     1a0:	10054a1c 	andne	r4, r5, ip, lsl sl
     1a4:	09054b06 	stmdbeq	r5, {r1, r2, r8, r9, fp, lr}
     1a8:	01040200 	mrseq	r0, R12_usr
     1ac:	05ba7903 	ldreq	r7, [sl, #2307]!	; 0x903
     1b0:	04020002 	streq	r0, [r2], #-2
     1b4:	054a0601 	strbeq	r0, [sl, #-1537]	; 0xfffff9ff
     1b8:	05830617 	streq	r0, [r3, #1559]	; 0x617
     1bc:	054a0608 	strbeq	r0, [sl, #-1544]	; 0xfffff9f8
     1c0:	064b0607 	strbeq	r0, [fp], -r7, lsl #12
     1c4:	0613054a 	ldreq	r0, [r3], -sl, asr #10
     1c8:	89010583 	stmdbhi	r1, {r0, r1, r7, r8, sl}
     1cc:	c1030005 	tstgt	r3, r5
     1d0:	053c0800 	ldreq	r0, [ip, #-2048]!	; 0xfffff800
     1d4:	05c00a0f 	strbeq	r0, [r0, #2575]	; 0xa0f
     1d8:	05f2060d 	ldrbeq	r0, [r2, #1549]!	; 0x60d
     1dc:	3d080608 	stccc	6, cr0, [r8, #-32]	; 0xffffffe0
     1e0:	ba060605 	blt	1819fc <ringBuffer+0x129cf4>
     1e4:	08061505 	stmdaeq	r6, {r0, r2, r8, sl, ip}
     1e8:	4b29053e 	blmi	a416e8 <ringBuffer+0x9e99e0>
     1ec:	054d0605 	strbeq	r0, [sp, #-1541]	; 0xfffff9fb
     1f0:	0a054607 	beq	151a14 <ringBuffer+0xf9d0c>
     1f4:	4829054d 	stmdami	r9!, {r0, r2, r3, r6, r8, sl}
     1f8:	4a062805 	bmi	18a214 <ringBuffer+0x13250c>
     1fc:	054a0705 	strbeq	r0, [sl, #-1797]	; 0xfffff8fb
     200:	054d0611 	strbeq	r0, [sp, #-1553]	; 0xfffff9ef
     204:	054a0606 	strbeq	r0, [sl, #-1542]	; 0xfffff9fa
     208:	2d054a15 	vstrcs	s8, [r5, #-84]	; 0xffffffac
     20c:	01040200 	mrseq	r0, R12_usr
     210:	00180582 	andseq	r0, r8, r2, lsl #11
     214:	4a010402 	bmi	41224 <blake2s_compress+0x36c>
     218:	02002d05 	andeq	r2, r0, #320	; 0x140
     21c:	054a0104 	strbeq	r0, [sl, #-260]	; 0xfffffefc
     220:	04020006 	streq	r0, [r2], #-6
     224:	12054a01 	andne	r4, r5, #4096	; 0x1000
     228:	05054b06 	streq	r4, [r5, #-2822]	; 0xfffff4fa
     22c:	06190584 	ldreq	r0, [r9], -r4, lsl #11
     230:	0031054a 	eorseq	r0, r1, sl, asr #10
     234:	82010402 	andhi	r0, r1, #33554432	; 0x2000000
     238:	02001c05 	andeq	r1, r0, #1280	; 0x500
     23c:	054a0104 	strbeq	r0, [sl, #-260]	; 0xfffffefc
     240:	04020031 	streq	r0, [r2], #-49	; 0xffffffcf
     244:	05054a01 	streq	r4, [r5, #-2561]	; 0xfffff5ff
     248:	01040200 	mrseq	r0, R12_usr
     24c:	0612054a 	ldreq	r0, [r2], -sl, asr #10
     250:	8405054b 	strhi	r0, [r5], #-1355	; 0xfffffab5
     254:	054e0c05 	strbeq	r0, [lr, #-3077]	; 0xfffff3fb
     258:	12054605 	andne	r4, r5, #5242880	; 0x500000
     25c:	8705054b 	strhi	r0, [r5, -fp, asr #10]
     260:	053c0806 	ldreq	r0, [ip, #-2054]!	; 0xfffff7fa
     264:	0583060f 	streq	r0, [r3, #1551]	; 0x60f
     268:	054a0603 	strbeq	r0, [sl, #-1539]	; 0xfffff9fd
     26c:	054b0615 	strbeq	r0, [fp, #-1557]	; 0xfffff9eb
     270:	053e0801 	ldreq	r0, [lr, #-2049]!	; 0xfffff7ff
     274:	00d70300 	sbcseq	r0, r7, r0, lsl #6
     278:	0905e408 	stmdbeq	r5, {r3, sl, sp, lr, pc}
     27c:	1205bc0a 	andne	fp, r5, #2560	; 0xa00
     280:	01040200 	mrseq	r0, R12_usr
     284:	1d054a06 	vstrne	s8, [r5, #-24]	; 0xffffffe8
     288:	02004b06 	andeq	r4, r0, #6144	; 0x1800
     28c:	05810204 	streq	r0, [r1, #516]	; 0x204
     290:	0402000e 	streq	r0, [r2], #-14
     294:	05ba0601 	ldreq	r0, [sl, #1537]!	; 0x601
     298:	04020012 	streq	r0, [r2], #-18	; 0xffffffee
     29c:	02054a01 	andeq	r4, r5, #4096	; 0x1000
     2a0:	01040200 	mrseq	r0, R12_usr
     2a4:	0629054a 	strteq	r0, [r9], -sl, asr #10
     2a8:	06070583 	streq	r0, [r7], -r3, lsl #11
     2ac:	4a1d054a 	bmi	7417dc <ringBuffer+0x6e9ad4>
     2b0:	054a0705 	strbeq	r0, [sl, #-1797]	; 0xfffff8fb
     2b4:	05be0606 	ldreq	r0, [lr, #1542]!	; 0x606
     2b8:	054a060b 	strbeq	r0, [sl, #-1547]	; 0xfffff9f5
     2bc:	4b064a06 	blmi	192adc <ringBuffer+0x13add4>
     2c0:	05840905 	streq	r0, [r4, #2309]	; 0x905
     2c4:	054a0602 	strbeq	r0, [sl, #-1538]	; 0xfffff9fe
     2c8:	054b0601 	strbeq	r0, [fp, #-1537]	; 0xfffff9ff
     2cc:	7fa00300 	svcvc	0x00a00300
     2d0:	05053c08 	streq	r3, [r5, #-3080]	; 0xfffff3f8
     2d4:	863d080a 	ldrthi	r0, [sp], -sl, lsl #16
     2d8:	06054a06 	streq	r4, [r5], -r6, lsl #20
     2dc:	82068306 	andhi	r8, r6, #402653184	; 0x18000000
     2e0:	86060c05 	strhi	r0, [r6], -r5, lsl #24
     2e4:	0805057f 	stmdaeq	r5, {r0, r1, r2, r3, r4, r5, r6, r8, sl}
     2e8:	05820643 	streq	r0, [r2, #1603]	; 0x643
     2ec:	1303060a 	movwne	r0, #13834	; 0x360a
     2f0:	054a0682 	strbeq	r0, [sl, #-1666]	; 0xfffff97e
     2f4:	06890606 	streq	r0, [r9], r6, lsl #12
     2f8:	0607054a 	streq	r0, [r7], -sl, asr #10
     2fc:	05820683 	streq	r0, [r2, #1667]	; 0x683
     300:	4b830613 	blmi	fe0c1b54 <__bss_end__+0xf47d3550>
     304:	11054b49 	tstne	r5, r9, asr #22
     308:	05740806 	ldrbeq	r0, [r4, #-2054]!	; 0xfffff7fa
     30c:	06850606 	streq	r0, [r5], r6, lsl #12
     310:	0607054a 	streq	r0, [r7], -sl, asr #10
     314:	05820683 	streq	r0, [r2, #1667]	; 0x683
     318:	05830614 	streq	r0, [r3, #1556]	; 0x614
     31c:	14054b13 	strne	r4, [r5], #-2835	; 0xfffff4ed
     320:	4b130549 	blmi	4c184c <ringBuffer+0x469b44>
     324:	08061105 	stmdaeq	r6, {r0, r2, r8, ip}
     328:	06060574 			; <UNDEFINED> instruction: 0x06060574
     32c:	06ba5e03 	ldrteq	r5, [sl], r3, lsl #28
     330:	0604054a 	streq	r0, [r4], -sl, asr #10
     334:	08060583 	stmdaeq	r6, {r0, r1, r7, r8, sl}
     338:	054a06ae 	strbeq	r0, [sl, #-1710]	; 0xfffff952
     33c:	05830604 	streq	r0, [r3, #1540]	; 0x604
     340:	06ae0806 	strteq	r0, [lr], r6, lsl #16
     344:	060f054a 	streq	r0, [pc], -sl, asr #10
     348:	060c0583 	streq	r0, [ip], -r3, lsl #11
     34c:	4a0f054a 	bmi	3c187c <ringBuffer+0x369b74>
     350:	054a0c05 	strbeq	r0, [sl, #-3077]	; 0xfffff3fb
     354:	06bc0606 	ldrteq	r0, [ip], r6, lsl #12
     358:	0612054a 	ldreq	r0, [r2], -sl, asr #10
     35c:	06080583 	streq	r0, [r8], -r3, lsl #11
     360:	4a12054a 	bmi	481890 <ringBuffer+0x429b88>
     364:	054a0805 	strbeq	r0, [sl, #-2053]	; 0xfffff7fb
     368:	07054a10 	smladeq	r5, r0, sl, r4
     36c:	0610054a 	ldreq	r0, [r0], -sl, asr #10
     370:	060d05bb 			; <UNDEFINED> instruction: 0x060d05bb
     374:	05f5064a 	ldrbeq	r0, [r5, #1610]!	; 0x64a
     378:	08190302 	ldmdaeq	r9, {r1, r8, r9}
     37c:	000105ac 	andeq	r0, r1, ip, lsr #11
     380:	4b010402 	blmi	41390 <blake2s_compress+0x4d8>
     384:	3d030005 	stccc	0, cr0, [r3, #-20]	; 0xffffffec
     388:	0205e408 	andeq	lr, r5, #8, 8	; 0x8000000
     38c:	05f3bb0a 	ldrbeq	fp, [r3, #2826]!	; 0xb0a
     390:	0205bf00 	andeq	fp, r5, #0, 30
     394:	7508bb0a 	strvc	fp, [r8, #-2826]	; 0xfffff4f6
     398:	09054b85 	stmdbeq	r5, {r0, r2, r7, r8, r9, fp, lr}
     39c:	4b02054c 	blmi	818d4 <ringBuffer+0x29bcc>
     3a0:	05490905 	strbeq	r0, [r9, #-2309]	; 0xfffff6fb
     3a4:	05400810 	strbeq	r0, [r0, #-2064]	; 0xfffff7f0
     3a8:	10054b02 	andne	r4, r5, r2, lsl #22
     3ac:	080605b9 	stmdaeq	r6, {r0, r3, r4, r5, r7, r8, sl}
     3b0:	bc09053f 	cfstr32lt	mvfx0, [r9], {63}	; 0x3f
     3b4:	05bb0305 	ldreq	r0, [fp, #773]!	; 0x305
     3b8:	04020008 	streq	r0, [r2], #-8
     3bc:	02054801 	andeq	r4, r5, #65536	; 0x10000
     3c0:	01040200 	mrseq	r0, R12_usr
     3c4:	86064a06 	strhi	r4, [r6], -r6, lsl #20
     3c8:	04c80284 	strbeq	r0, [r8], #644	; 0x284
     3cc:	00010100 	andeq	r0, r1, r0, lsl #2
     3d0:	00000205 	andeq	r0, r0, r5, lsl #4
     3d4:	d6030002 	strle	r0, [r3], -r2
     3d8:	02050101 	andeq	r0, r5, #1073741824	; 0x40000000
     3dc:	0505f40a 	streq	pc, [r5, #-1034]	; 0xfffffbf6
     3e0:	0582064c 	streq	r0, [r2, #1612]	; 0x64c
     3e4:	30020603 	andcc	r0, r2, r3, lsl #12
     3e8:	850a0513 	strhi	r0, [sl, #-1299]	; 0xfffffaed
     3ec:	03054a06 	movweq	r4, #23046	; 0x5a06
     3f0:	13300206 	teqne	r0, #1610612736	; 0x60000000
     3f4:	11054b46 	tstne	r5, r6, asr #22
     3f8:	054a1003 	strbeq	r1, [sl, #-3]
     3fc:	0105bb0f 	tsteq	r5, pc, lsl #22
     400:	031c0586 	tsteq	ip, #562036736	; 0x21800000
     404:	053c0871 	ldreq	r0, [ip, #-2161]!	; 0xfffff78f
     408:	054a060a 	strbeq	r0, [sl, #-1546]	; 0xfffff9f6
     40c:	0a054a1c 	beq	152c84 <ringBuffer+0xfaf7c>
     410:	11054a4a 	tstne	r5, sl, asr #20
     414:	13300206 	teqne	r0, #1610612736	; 0x60000000
     418:	4a062305 	bmi	189034 <ringBuffer+0x13132c>
     41c:	054a1105 	strbeq	r1, [sl, #-261]	; 0xfffffefb
     420:	054b060d 	strbeq	r0, [fp, #-1549]	; 0xfffff9f3
     424:	054a061c 	strbeq	r0, [sl, #-1564]	; 0xfffff9e4
     428:	07054a0d 	streq	r4, [r5, -sp, lsl #20]
     42c:	0d054906 	vstreq.16	s8, [r5, #-12]	; <UNPREDICTABLE>
     430:	061c054b 	ldreq	r0, [ip], -fp, asr #10
     434:	4a0d054a 	bmi	341964 <ringBuffer+0x2e9c5c>
     438:	054a0b05 	strbeq	r0, [sl, #-2821]	; 0xfffff4fb
     43c:	bbbe0603 	bllt	fef81c50 <__bss_end__+0xf569364c>
     440:	4a061b05 	bmi	18705c <ringBuffer+0x12f354>
     444:	064a0305 	strbeq	r0, [sl], -r5, lsl #6
     448:	0300054b 	movweq	r0, #1355	; 0x54b
     44c:	01300209 	teqeq	r0, r9, lsl #4
     450:	f60a1a05 			; <UNDEFINED> instruction: 0xf60a1a05
     454:	82061005 	andhi	r1, r6, #5
     458:	054a1a05 	strbeq	r1, [sl, #-2565]	; 0xfffff5fb
     45c:	18058210 	stmdane	r5, {r4, r9, pc}
     460:	4a07054a 	bmi	1c1990 <ringBuffer+0x169c88>
     464:	4b060505 	blmi	181880 <ringBuffer+0x129b78>
     468:	07054a06 	streq	r4, [r5, -r6, lsl #20]
     46c:	0a054906 	beq	15288c <ringBuffer+0xfab84>
     470:	06193002 	ldreq	r3, [r9], -r2
     474:	0603054a 	streq	r0, [r3], -sl, asr #10
     478:	05133002 	ldreq	r3, [r3, #-2]
     47c:	03054b10 	movweq	r4, #23312	; 0x5b10
     480:	10054a06 	andne	r4, r5, r6, lsl #20
     484:	4a03054a 	bmi	c19b4 <ringBuffer+0x69cac>
     488:	4b060705 	blmi	1820a4 <ringBuffer+0x12a39c>
     48c:	4a060e05 	bmi	183ca8 <ringBuffer+0x12bfa0>
     490:	054a0705 	strbeq	r0, [sl, #-1797]	; 0xfffff8fb
     494:	06054a0d 	streq	r4, [r5], -sp, lsl #20
     498:	060e054a 	streq	r0, [lr], -sl, asr #10
     49c:	05133402 	ldreq	r3, [r3, #-1026]	; 0xfffffbfe
     4a0:	054a060b 	strbeq	r0, [sl, #-1547]	; 0xfffff9f5
     4a4:	77030603 	strvc	r0, [r3, -r3, lsl #12]
     4a8:	4b1005ba 	blmi	401b98 <ringBuffer+0x3a9e90>
     4ac:	4a060305 	bmi	1810c8 <ringBuffer+0x1293c0>
     4b0:	054a1005 	strbeq	r1, [sl, #-5]
     4b4:	15054a03 	strne	r4, [r5, #-2563]	; 0xfffff5fd
     4b8:	0a054b06 	beq	1530d8 <ringBuffer+0xfb3d0>
     4bc:	4915054b 	ldmdbmi	r5, {r0, r1, r3, r6, r8, sl}
     4c0:	4a060b05 	bmi	1830dc <ringBuffer+0x12b3d4>
     4c4:	054a1305 	strbeq	r1, [sl, #-773]	; 0xfffffcfb
     4c8:	0a054a09 	beq	152cf4 <ringBuffer+0xfafec>
     4cc:	09054b06 	stmdbeq	r5, {r1, r2, r8, r9, fp, lr}
     4d0:	4b0d0549 	blmi	3419fc <ringBuffer+0x2e9cf4>
     4d4:	4a060a05 	bmi	182cf0 <ringBuffer+0x12afe8>
     4d8:	50060b05 	andpl	r0, r6, r5, lsl #22
     4dc:	89100585 	ldmdbhi	r0, {r0, r2, r7, r8, sl}
     4e0:	05470805 	strbeq	r0, [r7, #-2053]	; 0xfffff7fb
     4e4:	1005f40b 	andne	pc, r5, fp, lsl #8
     4e8:	06030583 	streq	r0, [r3], -r3, lsl #11
     4ec:	0615054a 	ldreq	r0, [r5], -sl, asr #10
     4f0:	06030583 	streq	r0, [r3], -r3, lsl #11
     4f4:	0610054a 	ldreq	r0, [r0], -sl, asr #10
     4f8:	0603054c 	streq	r0, [r3], -ip, asr #10
     4fc:	0615054a 	ldreq	r0, [r5], -sl, asr #10
     500:	06030583 	streq	r0, [r3], -r3, lsl #11
     504:	001c054a 	andseq	r0, ip, sl, asr #10
     508:	06020402 	streq	r0, [r2], -r2, lsl #8
     50c:	00140545 	andseq	r0, r4, r5, asr #10
     510:	06010402 	streq	r0, [r1], -r2, lsl #8
     514:	001005ba 			; <UNDEFINED> instruction: 0x001005ba
     518:	4a010402 	bmi	41528 <blake2s_compress+0x670>
     51c:	02000205 	andeq	r0, r0, #1342177280	; 0x50000000
     520:	054a0104 	strbeq	r0, [sl, #-260]	; 0xfffffefc
     524:	30020601 	andcc	r0, r2, r1, lsl #12
     528:	0300051a 	movweq	r0, #1306	; 0x51a
     52c:	280200da 	stmdacs	r2, {r1, r3, r4, r6, r7}
     530:	0a050501 	beq	14193c <ringBuffer+0xe9c34>
     534:	7f0605f9 	svcvc	0x000605f9
     538:	4c05054b 	cfstr32mi	mvfx0, [r5], {75}	; 0x4b
     53c:	0a054a06 	beq	152d5c <ringBuffer+0xfb054>
     540:	16300206 	ldrtne	r0, [r0], -r6, lsl #4
     544:	0b054a06 	bleq	152d64 <ringBuffer+0xfb05c>
     548:	13300206 	teqne	r0, #1610612736	; 0x60000000
     54c:	05bb2505 	ldreq	r2, [fp, #1285]!	; 0x505
     550:	32054909 	andcc	r4, r5, #147456	; 0x24000
     554:	0625054b 	strteq	r0, [r5], -fp, asr #10
     558:	4a32054a 	bmi	c81a88 <ringBuffer+0xc29d80>
     55c:	054a0b05 	strbeq	r0, [sl, #-2821]	; 0xfffff4fb
     560:	20054a32 	andcs	r4, r5, r2, lsr sl
     564:	4a32054a 	bmi	c81a94 <ringBuffer+0xc29d8c>
     568:	054a2005 	strbeq	r2, [sl, #-5]
     56c:	2d054a32 	vstrcs	s8, [r5, #-200]	; 0xffffff38
     570:	3505ed06 	strcc	lr, [r5, #-3334]	; 0xfffff2fa
     574:	2d054a06 	vstrcs	s8, [r5, #-24]	; 0xffffffe8
     578:	4a0b0582 	bmi	2c1b88 <ringBuffer+0x269e80>
     57c:	05823505 	streq	r3, [r2, #1285]	; 0x505
     580:	35054a28 	strcc	r4, [r5, #-2600]	; 0xfffff5d8
     584:	4a28054a 	bmi	a01ab4 <ringBuffer+0x9a9dac>
     588:	054a3505 	strbeq	r3, [sl, #-1285]	; 0xfffffafb
     58c:	0574080b 	ldrbeq	r0, [r4, #-2059]!	; 0xfffff7f5
     590:	054b062e 	strbeq	r0, [fp, #-1582]	; 0xfffff9d2
     594:	2e054909 	vmlacs.f16	s8, s10, s18	; <UNPREDICTABLE>
     598:	060b054b 	streq	r0, [fp], -fp, asr #10
     59c:	4a37054a 	bmi	dc1acc <ringBuffer+0xd69dc4>
     5a0:	054a2905 	strbeq	r2, [sl, #-2309]	; 0xfffff6fb
     5a4:	29054a37 	stmdbcs	r5, {r0, r1, r2, r4, r5, r9, fp, lr}
     5a8:	4a37054a 	bmi	dc1ad8 <ringBuffer+0xd69dd0>
     5ac:	08063205 	stmdaeq	r6, {r0, r2, r9, ip, sp}
     5b0:	060b0540 	streq	r0, [fp], -r0, asr #10
     5b4:	4a090582 	bmi	241bc4 <ringBuffer+0x1e9ebc>
     5b8:	4e060205 	cdpmi	2, 0, cr0, cr6, cr5, {0}
     5bc:	f31605bc 	vqrshl.u16	d0, d28, d22
     5c0:	82060205 	andhi	r0, r6, #1342177280	; 0x50000000
     5c4:	16058406 	strne	r8, [r5], -r6, lsl #8
     5c8:	060205f3 			; <UNDEFINED> instruction: 0x060205f3
     5cc:	06010582 	streq	r0, [r1], -r2, lsl #11
     5d0:	04d40283 	ldrbeq	r0, [r4], #643	; 0x283
     5d4:	66010100 	strvs	r0, [r1], -r0, lsl #2
     5d8:	02000001 	andeq	r0, r0, #1
     5dc:	00006600 	andeq	r6, r0, r0, lsl #12
     5e0:	fb010100 	blx	409ea <lcd_begin+0xe>
     5e4:	01000d0e 	tsteq	r0, lr, lsl #26
     5e8:	00010101 	andeq	r0, r1, r1, lsl #2
     5ec:	00010000 	andeq	r0, r1, r0
     5f0:	752f0100 	strvc	r0, [pc, #-256]!	; 4f8 <_init-0x10628>
     5f4:	692f7273 	stmdbvs	pc!, {r0, r1, r4, r5, r6, r9, ip, sp, lr}	; <UNPREDICTABLE>
     5f8:	756c636e 	strbvc	r6, [ip, #-878]!	; 0xfffffc92
     5fc:	622f6564 	eorvs	r6, pc, #100, 10	; 0x19000000
     600:	00737469 	rsbseq	r7, r3, r9, ror #8
     604:	7273752f 	rsbsvc	r7, r3, #197132288	; 0xbc00000
     608:	636e692f 	cmnvs	lr, #770048	; 0xbc000
     60c:	6564756c 	strbvs	r7, [r4, #-1388]!	; 0xfffffa94
     610:	7469622f 	strbtvc	r6, [r9], #-559	; 0xfffffdd1
     614:	79742f73 	ldmdbvc	r4!, {r0, r1, r4, r5, r6, r8, r9, sl, fp, sp}^
     618:	00736570 	rsbseq	r6, r3, r0, ror r5
     61c:	69747500 	ldmdbvs	r4!, {r8, sl, ip, sp, lr}^
     620:	00632e6c 	rsbeq	r2, r3, ip, ror #28
     624:	74000000 	strvc	r0, [r0], #-0
     628:	73657079 	cmnvc	r5, #121	; 0x79
     62c:	0100682e 	tsteq	r0, lr, lsr #16
     630:	74730000 	ldrbtvc	r0, [r3], #-0
     634:	74637572 	strbtvc	r7, [r3], #-1394	; 0xfffffa8e
     638:	6d69745f 	cfstrdvs	mvd7, [r9, #-380]!	; 0xfffffe84
     63c:	6c617665 	stclvs	6, cr7, [r1], #-404	; 0xfffffe6c
     640:	0200682e 	andeq	r6, r0, #3014656	; 0x2e0000
     644:	00000000 	andeq	r0, r0, r0
     648:	08100205 	ldmdaeq	r0, {r0, r2, r9}
     64c:	05190004 	ldreq	r0, [r9, #-4]
     650:	05f30a02 	ldrbeq	r0, [r3, #2562]!	; 0xa02
     654:	05ba0639 	ldreq	r0, [sl, #1593]!	; 0x639
     658:	bb064a02 	bllt	192e68 <ringBuffer+0x13b160>
     65c:	05f50005 	ldrbeq	r0, [r5, #5]!
     660:	f3f40a02 	vtbl.8	d16, {d4-d6}, d2
     664:	05bb0905 	ldreq	r0, [fp, #2309]!	; 0x905
     668:	054a0602 	strbeq	r0, [sl, #-1538]	; 0xfffff9fe
     66c:	44080600 	strmi	r0, [r8], #-1536	; 0xfffffa00
     670:	f30a0205 	vhsub.u8	d0, d10, d5
     674:	f50005f3 			; <UNDEFINED> instruction: 0xf50005f3
     678:	bd0a0605 	stclt	6, cr0, [sl, #-20]	; 0xffffffec
     67c:	4a060405 	bmi	181698 <ringBuffer+0x129990>
     680:	4c060205 	sfmmi	f0, 4, [r6], {5}
     684:	82062205 	andhi	r2, r6, #1342177280	; 0x50000000
     688:	054a0205 	strbeq	r0, [sl, #-517]	; 0xfffffdfb
     68c:	06840606 	streq	r0, [r4], r6, lsl #12
     690:	0603054a 	streq	r0, [r3], -sl, asr #10
     694:	054c484d 	strbeq	r4, [ip, #-2125]	; 0xfffff7b3
     698:	00054b01 	andeq	r4, r5, r1, lsl #22
     69c:	06053e08 	streq	r3, [r5], -r8, lsl #28
     6a0:	0405bd0a 	streq	fp, [r5], #-3338	; 0xfffff2f6
     6a4:	09054a06 	stmdbeq	r5, {r1, r2, r9, fp, lr}
     6a8:	02054c06 	andeq	r4, r5, #1536	; 0x600
     6ac:	00054a06 	andeq	r4, r5, r6, lsl #20
     6b0:	02058a06 	andeq	r8, r5, #24576	; 0x6000
     6b4:	05bbf40a 	ldreq	pc, [fp, #1034]!	; 0x40a
     6b8:	0205bb09 	andeq	fp, r5, #9216	; 0x2400
     6bc:	00054a06 	andeq	r4, r5, r6, lsl #20
     6c0:	0205f506 	andeq	pc, r5, #25165824	; 0x1800000
     6c4:	2c05f50a 	cfstr32cs	mvfx15, [r5], {10}
     6c8:	060f0584 	streq	r0, [pc], -r4, lsl #11
     6cc:	4a2c054a 	bmi	b01bfc <ringBuffer+0xaa9ef4>
     6d0:	05ba1605 	ldreq	r1, [sl, #1541]!	; 0x605
     6d4:	02054a1d 	andeq	r4, r5, #118784	; 0x1d000
     6d8:	0600054a 	streq	r0, [r0], -sl, asr #10
     6dc:	0a0205be 	beq	81ddc <ringBuffer+0x2a0d4>
     6e0:	841d05f5 	ldrhi	r0, [sp], #-1525	; 0xfffffa0b
     6e4:	4a060f05 	bmi	184300 <ringBuffer+0x12c5f8>
     6e8:	054a1d05 	strbeq	r1, [sl, #-3333]	; 0xfffff2fb
     6ec:	02054a24 	andeq	r4, r5, #36, 20	; 0x24000
     6f0:	0060024a 	rsbeq	r0, r0, sl, asr #4
     6f4:	05000101 	streq	r0, [r0, #-257]	; 0xfffffeff
     6f8:	02056402 	andeq	r6, r5, #33554432	; 0x2000000
     6fc:	01130300 	tsteq	r3, r0, lsl #6
     700:	080a0205 	stmdaeq	sl, {r0, r2, r9}
     704:	0300053e 	movweq	r0, #1342	; 0x53e
     708:	0205f21d 	andeq	pc, r5, #-805306367	; 0xd0000001
     70c:	3d05f30a 	stccc	3, cr15, [r5, #-40]	; 0xffffffd8
     710:	0205ba06 	andeq	fp, r5, #24576	; 0x6000
     714:	05bb064a 	ldreq	r0, [fp, #1610]!	; 0x64a
     718:	081c0300 	ldmdaeq	ip, {r8, r9}
     71c:	0a0905ac 	beq	241dd4 <ringBuffer+0x1ea0cc>
     720:	060205f3 			; <UNDEFINED> instruction: 0x060205f3
     724:	06010582 	streq	r0, [r1], -r2, lsl #11
     728:	f400054b 	vst3.16	{d0,d2,d4}, [r0], fp
     72c:	f40a0d05 			; <UNDEFINED> instruction: 0xf40a0d05
     730:	82060805 	andhi	r0, r6, #327680	; 0x50000
     734:	054a0605 	strbeq	r0, [sl, #-1541]	; 0xfffff9fb
     738:	024b0602 	subeq	r0, fp, #2097152	; 0x200000
     73c:	010002d0 	ldrdeq	r0, [r0, -r0]
     740:	00004d01 	andeq	r4, r0, r1, lsl #26
     744:	1c000200 	sfmne	f0, 4, [r0], {-0}
     748:	01000000 	mrseq	r0, (UNDEF: 0)
     74c:	0d0efb01 	vstreq	d15, [lr, #-4]
     750:	01010100 	mrseq	r0, (UNDEF: 17)
     754:	00000001 	andeq	r0, r0, r1
     758:	01000001 	tsteq	r0, r1
     75c:	64656c00 	strbtvs	r6, [r5], #-3072	; 0xfffff400
     760:	0000632e 	andeq	r6, r0, lr, lsr #6
     764:	00000000 	andeq	r0, r0, r0
     768:	062c0205 	strteq	r0, [ip], -r5, lsl #4
     76c:	05180002 	ldreq	r0, [r8, #-2]
     770:	05830a0e 	streq	r0, [r3, #2574]	; 0xa0e
     774:	0e054b02 	vmlaeq.f64	d4, d5, d2
     778:	83020581 	movwhi	r0, #9601	; 0x2581
     77c:	05810e05 	streq	r0, [r1, #3589]	; 0xe05
     780:	054b4b02 	strbeq	r4, [fp, #-2818]	; 0xfffff4fe
     784:	05770800 	ldrbeq	r0, [r7, #-2048]!	; 0xfffff800
     788:	bb830a02 	bllt	fe0c2f98 <__bss_end__+0xf47d4994>
     78c:	0001e802 	andeq	lr, r1, r2, lsl #16
     790:	00a50101 	adceq	r0, r5, r1, lsl #2
     794:	00020000 	andeq	r0, r2, r0
     798:	0000003f 	andeq	r0, r0, pc, lsr r0
     79c:	0efb0101 	cdpeq	1, 15, cr0, cr11, cr1, {0}
     7a0:	0101000d 	tsteq	r1, sp
     7a4:	00000101 	andeq	r0, r0, r1, lsl #2
     7a8:	00000100 	andeq	r0, r0, r0, lsl #2
     7ac:	6c2f2e01 	stcvs	14, cr2, [pc], #-4	; 7b0 <_init-0x10370>
     7b0:	00006269 	andeq	r6, r0, r9, ror #4
     7b4:	7571694c 	ldrbvc	r6, [r1, #-2380]!	; 0xfffff6b4
     7b8:	72436469 	subvc	r6, r3, #1761607680	; 0x69000000
     7bc:	61747379 	cmnvs	r4, r9, ror r3
     7c0:	00632e6c 	rsbeq	r2, r3, ip, ror #28
     7c4:	4c000000 	stcmi	0, cr0, [r0], {-0}
     7c8:	69757169 	ldmdbvs	r5!, {r0, r3, r5, r6, r8, ip, sp, lr}^
     7cc:	79724364 	ldmdbvc	r2!, {r2, r5, r6, r8, r9, lr}^
     7d0:	6c617473 	cfstrdvs	mvd7, [r1], #-460	; 0xfffffe34
     7d4:	0100682e 	tsteq	r0, lr, lsr #16
     7d8:	00000000 	andeq	r0, r0, r0
     7dc:	09dc0205 	ldmibeq	ip, {r0, r2, r9}^
     7e0:	05170004 	ldreq	r0, [r7, #-4]
     7e4:	05bc0a0e 	ldreq	r0, [ip, #2574]!	; 0xa0e
     7e8:	053e0802 	ldreq	r0, [lr, #-2050]!	; 0xfffff7fe
     7ec:	6805480e 	stmdavs	r5, {r1, r2, r3, fp, lr}
     7f0:	06730584 	ldrbteq	r0, [r3], -r4, lsl #11
     7f4:	4a02054a 	bmi	81d24 <ringBuffer+0x2a01c>
     7f8:	1402f306 	strne	pc, [r2], #-774	; 0xfffffcfa
     7fc:	00010100 	andeq	r0, r1, r0, lsl #2
     800:	06980205 	ldreq	r0, [r8], r5, lsl #4
     804:	0d030002 	stceq	0, cr0, [r3, #-8]
     808:	0a020501 	beq	81c14 <ringBuffer+0x29f0c>
     80c:	053d08bb 	ldreq	r0, [sp, #-2235]!	; 0xfffff745
     810:	05770800 	ldrbeq	r0, [r7, #-2048]!	; 0xfffff800
     814:	3d080a02 	vstrcc	s0, [r8, #-8]
     818:	4a065905 	bmi	196c34 <ringBuffer+0x13ef2c>
     81c:	054a5e05 	strbeq	r5, [sl, #-3589]	; 0xfffff1fb
     820:	08064a02 	stmdaeq	r6, {r1, r9, fp, lr}
     824:	08000575 	stmdaeq	r0, {r0, r2, r4, r5, r6, r8, sl}
     828:	0a020577 	beq	81e0c <ringBuffer+0x2a104>
     82c:	064f05bb 			; <UNDEFINED> instruction: 0x064f05bb
     830:	820205f2 	andhi	r0, r2, #1015021568	; 0x3c800000
     834:	1802f306 	stmdane	r2, {r1, r2, r8, r9, ip, sp, lr, pc}
     838:	34010100 	strcc	r0, [r1], #-256	; 0xffffff00
     83c:	02000003 	andeq	r0, r0, #3
     840:	00016400 	andeq	r6, r1, r0, lsl #8
     844:	fb010200 	blx	4104e <blake2s_compress+0x196>
     848:	01000d0e 	tsteq	r0, lr, lsl #26
     84c:	00010101 	andeq	r0, r1, r1, lsl #2
     850:	00010000 	andeq	r0, r1, r0
     854:	682f0100 	stmdavs	pc!, {r8}	; <UNPREDICTABLE>
     858:	2f656d6f 	svccs	0x00656d6f
     85c:	6f62736f 	svcvs	0x0062736f
     860:	2f736578 	svccs	0x00736578
     864:	65766564 	ldrbvs	r6, [r6, #-1380]!	; 0xfffffa9c
     868:	706f2f6c 	rsbvc	r2, pc, ip, ror #30
     86c:	2f656574 	svccs	0x00656574
     870:	6c6f6f74 	stclvs	15, cr6, [pc], #-464	; 6a8 <_init-0x10478>
     874:	69616863 	stmdbvs	r1!, {r0, r1, r5, r6, fp, sp, lr}^
     878:	612f736e 			; <UNDEFINED> instruction: 0x612f736e
     87c:	68637261 	stmdavs	r3!, {r0, r5, r6, r9, ip, sp, lr}^
     880:	612f3233 			; <UNDEFINED> instruction: 0x612f3233
     884:	6c2d6d72 	stcvs	13, cr6, [sp], #-456	; 0xfffffe38
     888:	78756e69 	ldmdavc	r5!, {r0, r3, r5, r6, r9, sl, fp, sp, lr}^
     88c:	756e672d 	strbvc	r6, [lr, #-1837]!	; 0xfffff8d3
     890:	69626165 	stmdbvs	r2!, {r0, r2, r5, r6, r8, sp, lr}^
     894:	6c2f6668 	stcvs	6, cr6, [pc], #-416	; 6fc <_init-0x10424>
     898:	2f636269 	svccs	0x00636269
     89c:	2f727375 	svccs	0x00727375
     8a0:	6c636e69 	stclvs	14, cr6, [r3], #-420	; 0xfffffe5c
     8a4:	00656475 	rsbeq	r6, r5, r5, ror r4
     8a8:	6d6f682f 	stclvs	8, cr6, [pc, #-188]!	; 7f4 <_init-0x1032c>
     8ac:	736f2f65 	cmnvc	pc, #404	; 0x194
     8b0:	65786f62 	ldrbvs	r6, [r8, #-3938]!	; 0xfffff09e
     8b4:	65642f73 	strbvs	r2, [r4, #-3955]!	; 0xfffff08d
     8b8:	2f6c6576 	svccs	0x006c6576
     8bc:	6574706f 	ldrbvs	r7, [r4, #-111]!	; 0xffffff91
     8c0:	6f742f65 	svcvs	0x00742f65
     8c4:	68636c6f 	stmdavs	r3!, {r0, r1, r2, r3, r5, r6, sl, fp, sp, lr}^
     8c8:	736e6961 	cmnvc	lr, #1589248	; 0x184000
     8cc:	7261612f 	rsbvc	r6, r1, #-1073741813	; 0xc000000b
     8d0:	32336863 	eorscc	r6, r3, #6488064	; 0x630000
     8d4:	62696c2f 	rsbvs	r6, r9, #12032	; 0x2f00
     8d8:	6363672f 	cmnvs	r3, #12320768	; 0xbc0000
     8dc:	6d72612f 	ldfvse	f6, [r2, #-188]!	; 0xffffff44
     8e0:	6e696c2d 	cdpvs	12, 6, cr6, cr9, cr13, {1}
     8e4:	672d7875 			; <UNDEFINED> instruction: 0x672d7875
     8e8:	6165756e 	cmnvs	r5, lr, ror #10
     8ec:	66686962 	strbtvs	r6, [r8], -r2, ror #18
     8f0:	322e362f 	eorcc	r3, lr, #49283072	; 0x2f00000
     8f4:	692f312e 	stmdbvs	pc!, {r1, r2, r3, r5, r8, ip, sp}	; <UNPREDICTABLE>
     8f8:	756c636e 	strbvc	r6, [ip, #-878]!	; 0xfffffc92
     8fc:	2f006564 	svccs	0x00006564
     900:	6964656d 	stmdbvs	r4!, {r0, r2, r3, r5, r6, r8, sl, sp, lr}^
     904:	70722f61 	rsbsvc	r2, r2, r1, ror #30
     908:	73752f69 	cmnvc	r5, #420	; 0x1a4
     90c:	6e692f72 	mcrvs	15, 3, r2, cr9, cr2, {3}
     910:	64756c63 	ldrbtvs	r6, [r5], #-3171	; 0xfffff39d
     914:	72612f65 	rsbvc	r2, r1, #404	; 0x194
     918:	696c2d6d 	stmdbvs	ip!, {r0, r2, r3, r5, r6, r8, sl, fp, sp}^
     91c:	2d78756e 	cfldr64cs	mvdx7, [r8, #-440]!	; 0xfffffe48
     920:	65756e67 	ldrbvs	r6, [r5, #-3687]!	; 0xfffff199
     924:	68696261 	stmdavs	r9!, {r0, r5, r6, r9, sp, lr}^
     928:	69622f66 	stmdbvs	r2!, {r1, r2, r5, r6, r8, r9, sl, fp, sp}^
     92c:	00007374 	andeq	r7, r0, r4, ror r3
     930:	6b616c62 	blvs	185bac0 <ringBuffer+0x1803db8>
     934:	692d3265 	pushvs	{r0, r2, r5, r6, r9, ip, sp}
     938:	2e6c706d 	cdpcs	0, 6, cr7, cr12, cr13, {3}
     93c:	00000068 	andeq	r0, r0, r8, rrx
     940:	616c6200 	cmnvs	ip, r0, lsl #4
     944:	7332656b 	teqvc	r2, #448790528	; 0x1ac00000
     948:	6665722d 	strbtvs	r7, [r5], -sp, lsr #4
     94c:	0000632e 	andeq	r6, r0, lr, lsr #6
     950:	74730000 	ldrbtvc	r0, [r3], #-0
     954:	746e6964 	strbtvc	r6, [lr], #-2404	; 0xfffff69c
     958:	0100682e 	tsteq	r0, lr, lsr #16
     95c:	74730000 	ldrbtvc	r0, [r3], #-0
     960:	66656464 	strbtvs	r6, [r5], -r4, ror #8
     964:	0200682e 	andeq	r6, r0, #3014656	; 0x2e0000
     968:	79740000 	ldmdbvc	r4!, {}^	; <UNPREDICTABLE>
     96c:	2e736570 	mrccs	5, 3, r6, cr3, cr0, {3}
     970:	00030068 	andeq	r0, r3, r8, rrx
     974:	62696c00 	rsbvs	r6, r9, #0, 24
     978:	682e6f69 	stmdavs	lr!, {r0, r3, r5, r6, r8, r9, sl, fp, sp, lr}
     97c:	00000100 	andeq	r0, r0, r0, lsl #2
     980:	69647473 	stmdbvs	r4!, {r0, r1, r4, r5, r6, sl, ip, sp, lr}^
     984:	00682e6f 	rsbeq	r2, r8, pc, ror #28
     988:	73000001 	movwvc	r0, #1
     98c:	655f7379 	ldrbvs	r7, [pc, #-889]	; 61b <_init-0x10505>
     990:	696c7272 	stmdbvs	ip!, {r1, r4, r5, r6, r9, ip, sp, lr}^
     994:	682e7473 	stmdavs	lr!, {r0, r1, r4, r5, r6, sl, ip, sp, lr}
     998:	00000300 	andeq	r0, r0, r0, lsl #6
     99c:	6b616c62 	blvs	185bb2c <ringBuffer+0x1803e24>
     9a0:	682e3265 	stmdavs	lr!, {r0, r2, r5, r6, r9, ip, sp}
     9a4:	00000000 	andeq	r0, r0, r0
     9a8:	02050000 	andeq	r0, r5, #0
     9ac:	00040adc 	ldrdeq	r0, [r4], -ip
     9b0:	50012103 	andpl	r2, r1, r3, lsl #2
     9b4:	22493d2f 	subcs	r3, r9, #3008	; 0xbc0
     9b8:	23492249 	movtcs	r2, #37449	; 0x9249
     9bc:	6a662303 	bvs	19895d0 <ringBuffer+0x19318c8>
     9c0:	6968912f 	stmdbvs	r8!, {r0, r1, r2, r3, r5, r8, ip, pc}^
     9c4:	674b2f5c 	smlsldvs	r2, fp, ip, pc	; <UNPREDICTABLE>
     9c8:	2a036867 	bcs	dab6c <ringBuffer+0x82e64>
     9cc:	034b5966 	movteq	r5, #47462	; 0xb966
     9d0:	755a6609 	ldrbvc	r6, [sl, #-1545]	; 0xfffff9f7
     9d4:	8e030204 	cdphi	2, 0, cr0, cr3, cr4, {0}
     9d8:	4b4b747f 	blmi	12ddbdc <ringBuffer+0x1285ed4>
     9dc:	69754b6a 	ldmdbvs	r5!, {r1, r3, r5, r6, r8, r9, fp, lr}^
     9e0:	0402004b 	streq	r0, [r2], #-75	; 0xffffffb5
     9e4:	06580601 	ldrbeq	r0, [r8], -r1, lsl #12
     9e8:	594d4b3e 	stmdbpl	sp, {r1, r2, r3, r4, r5, r8, r9, fp, lr}^
     9ec:	4c69c967 			; <UNDEFINED> instruction: 0x4c69c967
     9f0:	0402005a 	streq	r0, [r2], #-90	; 0xffffffa6
     9f4:	003c0603 	eorseq	r0, ip, r3, lsl #12
     9f8:	c8010402 	stmdagt	r1, {r1, sl}
     9fc:	59783d06 	ldmdbpl	r8!, {r1, r2, r8, sl, fp, ip, sp}^
     a00:	02003f31 	andeq	r3, r0, #49, 30	; 0xc4
     a04:	003d0304 	eorseq	r0, sp, r4, lsl #6
     a08:	ff030402 			; <UNDEFINED> instruction: 0xff030402
     a0c:	01040200 	mrseq	r0, R12_usr
     a10:	3f063c06 	svccc	0x00063c06
     a14:	5c4f2159 	stfple	f2, [pc], {89}	; 0x59
     a18:	02040200 	andeq	r0, r4, #0, 4
     a1c:	02003c06 	andeq	r3, r0, #1536	; 0x600
     a20:	063c0304 	ldrteq	r0, [ip], -r4, lsl #6
     a24:	2f2f3d3e 	svccs	0x002f3d3e
     a28:	7575752f 	ldrbvc	r7, [r5, #-1327]!	; 0xfffffad1
     a2c:	8383302f 	orrhi	r3, r3, #47	; 0x2f
     a30:	01040200 	mrseq	r0, R12_usr
     a34:	00774d75 	rsbseq	r4, r7, r5, ror sp
     a38:	06020402 	streq	r0, [r2], -r2, lsl #8
     a3c:	0402003c 	streq	r0, [r2], #-60	; 0xffffffc4
     a40:	3e063c03 	cdpcc	12, 0, cr3, cr6, cr3, {0}
     a44:	02040200 	andeq	r0, r4, #0, 4
     a48:	02003c06 	andeq	r3, r0, #1536	; 0x600
     a4c:	003c0404 	eorseq	r0, ip, r4, lsl #8
     a50:	3c050402 	cfstrscc	mvf0, [r5], {2}
     a54:	4b4b3e06 	blmi	12d0274 <ringBuffer+0x127856c>
     a58:	75753d3d 	ldrbvc	r3, [r5, #-3389]!	; 0xfffff2c3
     a5c:	833e3d75 	teqhi	lr, #7488	; 0x1d40
     a60:	04020084 	streq	r0, [r2], #-132	; 0xffffff7c
     a64:	06900601 	ldreq	r0, [r0], r1, lsl #12
     a68:	75757540 	ldrbvc	r7, [r5, #-1344]!	; 0xfffffac0
     a6c:	04020068 	streq	r0, [r2], #-104	; 0xffffff98
     a70:	1b032101 	blne	c8e7c <ringBuffer+0x71174>
     a74:	02005d4a 	andeq	r5, r0, #4736	; 0x1280
     a78:	004b0304 	subeq	r0, fp, r4, lsl #6
     a7c:	ff030402 			; <UNDEFINED> instruction: 0xff030402
     a80:	01040200 	mrseq	r0, R12_usr
     a84:	4e065806 	cdpmi	8, 0, cr5, cr6, cr6, {0}
     a88:	03040200 	movweq	r0, #16896	; 0x4200
     a8c:	0402004b 	streq	r0, [r2], #-75	; 0xffffffb5
     a90:	0200c703 	andeq	ip, r0, #786432	; 0xc0000
     a94:	58060104 	stmdapl	r6, {r2, r8}
     a98:	59594e06 	ldmdbpl	r9, {r1, r2, r9, sl, fp, lr}^
     a9c:	83835959 	orrhi	r5, r3, #1458176	; 0x164000
     aa0:	a0028483 	andge	r8, r2, r3, lsl #9
     aa4:	a0021304 	andge	r1, r2, r4, lsl #6
     aa8:	a0021304 	andge	r1, r2, r4, lsl #6
     aac:	a0021304 	andge	r1, r2, r4, lsl #6
     ab0:	a0021304 	andge	r1, r2, r4, lsl #6
     ab4:	a0021304 	andge	r1, r2, r4, lsl #6
     ab8:	a0021304 	andge	r1, r2, r4, lsl #6
     abc:	a0021304 	andge	r1, r2, r4, lsl #6
     ac0:	a0021304 	andge	r1, r2, r4, lsl #6
     ac4:	a0021304 	andge	r1, r2, r4, lsl #6
     ac8:	02001404 	andeq	r1, r0, #4, 8	; 0x4000000
     acc:	004b0304 	subeq	r0, fp, r4, lsl #6
     ad0:	08030402 	stmdaeq	r3, {r1, sl}
     ad4:	040200c7 	streq	r0, [r2], #-199	; 0xffffff39
     ad8:	06580601 	ldrbeq	r0, [r8], -r1, lsl #12
     adc:	2f67504d 	svccs	0x0067504d
     ae0:	4c4b3d3e 	mcrrmi	13, 3, r3, fp, cr14
     ae4:	674b9f3d 	smlaldxvs	r9, fp, sp, pc	; <UNPREDICTABLE>
     ae8:	4b4b2183 	blmi	12c90fc <ringBuffer+0x12713f4>
     aec:	ad43383d 	stclge	8, cr3, [r3, #-244]	; 0xffffff0c
     af0:	674d2168 	strbvs	r2, [sp, -r8, ror #2]
     af4:	04020077 	streq	r0, [r2], #-119	; 0xffffff89
     af8:	063c0601 	ldrteq	r0, [ip], -r1, lsl #12
     afc:	3e673e59 	mcrcc	14, 3, r3, cr7, cr9, {2}
     b00:	68d73d67 	ldmvs	r7, {r0, r1, r2, r5, r6, r8, sl, fp, ip, sp}^
     b04:	03040200 	movweq	r0, #16896	; 0x4200
     b08:	0402003d 	streq	r0, [r2], #-61	; 0xffffffc3
     b0c:	0200b903 	andeq	fp, r0, #49152	; 0xc000
     b10:	3c060104 	stfccs	f0, [r6], {4}
     b14:	67753f06 	ldrbvs	r3, [r5, -r6, lsl #30]!
     b18:	01040200 	mrseq	r0, R12_usr
     b1c:	00784d21 	rsbseq	r4, r8, r1, lsr #26
     b20:	06010402 	streq	r0, [r1], -r2, lsl #8
     b24:	0402003c 	streq	r0, [r2], #-60	; 0xffffffc4
     b28:	3e063c02 	cdpcc	12, 0, cr3, cr6, cr2, {0}
     b2c:	01040200 	mrseq	r0, R12_usr
     b30:	3e063c06 	cdpcc	12, 0, cr3, cr6, cr6, {0}
     b34:	01040200 	mrseq	r0, R12_usr
     b38:	02004a06 	andeq	r4, r0, #24576	; 0x6000
     b3c:	064a0204 	strbeq	r0, [sl], -r4, lsl #4
     b40:	0402003e 	streq	r0, [r2], #-62	; 0xffffffc2
     b44:	003c0602 	eorseq	r0, ip, r2, lsl #12
     b48:	3c030402 	cfstrscc	mvf0, [r3], {2}
     b4c:	02003e06 	andeq	r3, r0, #6, 28	; 0x60
     b50:	4a060104 	bmi	180f68 <ringBuffer+0x129260>
     b54:	004c3e06 	subeq	r3, ip, r6, lsl #28
     b58:	06010402 	streq	r0, [r1], -r2, lsl #8
     b5c:	004006ba 	strheq	r0, [r0], #-106	; 0xffffff96
     b60:	06010402 	streq	r0, [r1], -r2, lsl #8
     b64:	753f0690 	ldrvc	r0, [pc, #-1680]!	; 4dc <_init-0x10644>
     b68:	04020075 	streq	r0, [r2], #-117	; 0xffffff8b
     b6c:	04022101 	streq	r2, [r2], #-257	; 0xfffffeff
     b70:	13010100 	movwne	r0, #4352	; 0x1100
     b74:	02000004 	andeq	r0, r0, #4
     b78:	00022300 	andeq	r2, r2, r0, lsl #6
     b7c:	fb010200 	blx	41386 <blake2s_compress+0x4ce>
     b80:	01000d0e 	tsteq	r0, lr, lsl #26
     b84:	00010101 	andeq	r0, r1, r1, lsl #2
     b88:	00010000 	andeq	r0, r1, r0
     b8c:	2e2e0100 	sufcse	f0, f6, f0
     b90:	2f2e2e2f 	svccs	0x002e2e2f
     b94:	6d617274 	sfmvs	f7, 2, [r1, #-464]!	; 0xfffffe30
     b98:	696c6f70 	stmdbvs	ip!, {r4, r5, r6, r8, r9, sl, fp, sp, lr}^
     b9c:	6c5f656e 	cfldr64vs	mvdx6, [pc], {110}	; 0x6e
     ba0:	2f006269 	svccs	0x00006269
     ba4:	656d6f68 	strbvs	r6, [sp, #-3944]!	; 0xfffff098
     ba8:	7a727a2f 	bvc	1c9f46c <ringBuffer+0x1c47764>
     bac:	37313530 			; <UNDEFINED> instruction: 0x37313530
     bb0:	7574732f 	ldrbvc	r7, [r4, #-815]!	; 0xfffffcd1
     bb4:	632f7964 			; <UNDEFINED> instruction: 0x632f7964
     bb8:	6e696168 	powvsez	f6, f1, #0.0
     bbc:	7474615f 	ldrbtvc	r6, [r4], #-351	; 0xfffffea1
     bc0:	61747365 	cmnvs	r4, r5, ror #6
     bc4:	6e6f6974 			; <UNDEFINED> instruction: 0x6e6f6974
     bc8:	4952412f 	ldmdbmi	r2, {r0, r1, r2, r3, r5, r8, lr}^
     bcc:	7a727a2d 	bvc	1c9f488 <ringBuffer+0x1c47780>
     bd0:	6363672f 	cmnvs	r3, #12320768	; 0xbc0000
     bd4:	6e696c2d 	cdpvs	12, 6, cr6, cr9, cr13, {1}
     bd8:	2d6f7261 	sfmcs	f7, 2, [pc, #-388]!	; a5c <_init-0x100c4>
     bdc:	2e322e36 	mrccs	14, 1, r2, cr2, cr6, {1}
     be0:	30322d31 	eorscc	r2, r2, r1, lsr sp
     be4:	312e3631 			; <UNDEFINED> instruction: 0x312e3631
     be8:	38782d31 	ldmdacc	r8!, {r0, r4, r5, r8, sl, fp, sp}^
     bec:	34365f36 	ldrtcc	r5, [r6], #-3894	; 0xfffff0ca
     bf0:	6d72615f 	ldfvse	f6, [r2, #-380]!	; 0xfffffe84
     bf4:	6e696c2d 	cdpvs	12, 6, cr6, cr9, cr13, {1}
     bf8:	672d7875 			; <UNDEFINED> instruction: 0x672d7875
     bfc:	6165756e 	cmnvs	r5, lr, ror #10
     c00:	66686962 	strbtvs	r6, [r8], -r2, ror #18
     c04:	62696c2f 	rsbvs	r6, r9, #12032	; 0x2f00
     c08:	6363672f 	cmnvs	r3, #12320768	; 0xbc0000
     c0c:	6d72612f 	ldfvse	f6, [r2, #-188]!	; 0xffffff44
     c10:	6e696c2d 	cdpvs	12, 6, cr6, cr9, cr13, {1}
     c14:	672d7875 			; <UNDEFINED> instruction: 0x672d7875
     c18:	6165756e 	cmnvs	r5, lr, ror #10
     c1c:	66686962 	strbtvs	r6, [r8], -r2, ror #18
     c20:	322e362f 	eorcc	r3, lr, #49283072	; 0x2f00000
     c24:	692f312e 	stmdbvs	pc!, {r1, r2, r3, r5, r8, ip, sp}	; <UNPREDICTABLE>
     c28:	756c636e 	strbvc	r6, [ip, #-878]!	; 0xfffffc92
     c2c:	2f006564 	svccs	0x00006564
     c30:	656d6f68 	strbvs	r6, [sp, #-3944]!	; 0xfffff098
     c34:	7a727a2f 	bvc	1c9f4f8 <ringBuffer+0x1c477f0>
     c38:	37313530 			; <UNDEFINED> instruction: 0x37313530
     c3c:	7574732f 	ldrbvc	r7, [r4, #-815]!	; 0xfffffcd1
     c40:	632f7964 			; <UNDEFINED> instruction: 0x632f7964
     c44:	6e696168 	powvsez	f6, f1, #0.0
     c48:	7474615f 	ldrbtvc	r6, [r4], #-351	; 0xfffffea1
     c4c:	61747365 	cmnvs	r4, r5, ror #6
     c50:	6e6f6974 			; <UNDEFINED> instruction: 0x6e6f6974
     c54:	4952412f 	ldmdbmi	r2, {r0, r1, r2, r3, r5, r8, lr}^
     c58:	7a727a2d 	bvc	1c9f514 <ringBuffer+0x1c4780c>
     c5c:	6363672f 	cmnvs	r3, #12320768	; 0xbc0000
     c60:	6e696c2d 	cdpvs	12, 6, cr6, cr9, cr13, {1}
     c64:	2d6f7261 	sfmcs	f7, 2, [pc, #-388]!	; ae8 <_init-0x10038>
     c68:	2e322e36 	mrccs	14, 1, r2, cr2, cr6, {1}
     c6c:	30322d31 	eorscc	r2, r2, r1, lsr sp
     c70:	312e3631 			; <UNDEFINED> instruction: 0x312e3631
     c74:	38782d31 	ldmdacc	r8!, {r0, r4, r5, r8, sl, fp, sp}^
     c78:	34365f36 	ldrtcc	r5, [r6], #-3894	; 0xfffff0ca
     c7c:	6d72615f 	ldfvse	f6, [r2, #-380]!	; 0xfffffe84
     c80:	6e696c2d 	cdpvs	12, 6, cr6, cr9, cr13, {1}
     c84:	672d7875 			; <UNDEFINED> instruction: 0x672d7875
     c88:	6165756e 	cmnvs	r5, lr, ror #10
     c8c:	66686962 	strbtvs	r6, [r8], -r2, ror #18
     c90:	6d72612f 	ldfvse	f6, [r2, #-188]!	; 0xffffff44
     c94:	6e696c2d 	cdpvs	12, 6, cr6, cr9, cr13, {1}
     c98:	672d7875 			; <UNDEFINED> instruction: 0x672d7875
     c9c:	6165756e 	cmnvs	r5, lr, ror #10
     ca0:	66686962 	strbtvs	r6, [r8], -r2, ror #18
     ca4:	62696c2f 	rsbvs	r6, r9, #12032	; 0x2f00
     ca8:	73752f63 	cmnvc	r5, #396	; 0x18c
     cac:	6e692f72 	mcrvs	15, 3, r2, cr9, cr2, {3}
     cb0:	64756c63 	ldrbtvs	r6, [r5], #-3171	; 0xfffff39d
     cb4:	69622f65 	stmdbvs	r2!, {r0, r2, r5, r6, r8, r9, sl, fp, sp}^
     cb8:	2f007374 	svccs	0x00007374
     cbc:	656d6f68 	strbvs	r6, [sp, #-3944]!	; 0xfffff098
     cc0:	7a727a2f 	bvc	1c9f584 <ringBuffer+0x1c4787c>
     cc4:	37313530 			; <UNDEFINED> instruction: 0x37313530
     cc8:	7574732f 	ldrbvc	r7, [r4, #-815]!	; 0xfffffcd1
     ccc:	632f7964 			; <UNDEFINED> instruction: 0x632f7964
     cd0:	6e696168 	powvsez	f6, f1, #0.0
     cd4:	7474615f 	ldrbtvc	r6, [r4], #-351	; 0xfffffea1
     cd8:	61747365 	cmnvs	r4, r5, ror #6
     cdc:	6e6f6974 			; <UNDEFINED> instruction: 0x6e6f6974
     ce0:	4952412f 	ldmdbmi	r2, {r0, r1, r2, r3, r5, r8, lr}^
     ce4:	7a727a2d 	bvc	1c9f5a0 <ringBuffer+0x1c47898>
     ce8:	6363672f 	cmnvs	r3, #12320768	; 0xbc0000
     cec:	6e696c2d 	cdpvs	12, 6, cr6, cr9, cr13, {1}
     cf0:	2d6f7261 	sfmcs	f7, 2, [pc, #-388]!	; b74 <_init-0xffac>
     cf4:	2e322e36 	mrccs	14, 1, r2, cr2, cr6, {1}
     cf8:	30322d31 	eorscc	r2, r2, r1, lsr sp
     cfc:	312e3631 			; <UNDEFINED> instruction: 0x312e3631
     d00:	38782d31 	ldmdacc	r8!, {r0, r4, r5, r8, sl, fp, sp}^
     d04:	34365f36 	ldrtcc	r5, [r6], #-3894	; 0xfffff0ca
     d08:	6d72615f 	ldfvse	f6, [r2, #-380]!	; 0xfffffe84
     d0c:	6e696c2d 	cdpvs	12, 6, cr6, cr9, cr13, {1}
     d10:	672d7875 			; <UNDEFINED> instruction: 0x672d7875
     d14:	6165756e 	cmnvs	r5, lr, ror #10
     d18:	66686962 	strbtvs	r6, [r8], -r2, ror #18
     d1c:	6d72612f 	ldfvse	f6, [r2, #-188]!	; 0xffffff44
     d20:	6e696c2d 	cdpvs	12, 6, cr6, cr9, cr13, {1}
     d24:	672d7875 			; <UNDEFINED> instruction: 0x672d7875
     d28:	6165756e 	cmnvs	r5, lr, ror #10
     d2c:	66686962 	strbtvs	r6, [r8], -r2, ror #18
     d30:	62696c2f 	rsbvs	r6, r9, #12032	; 0x2f00
     d34:	73752f63 	cmnvc	r5, #396	; 0x18c
     d38:	6e692f72 	mcrvs	15, 3, r2, cr9, cr2, {3}
     d3c:	64756c63 	ldrbtvs	r6, [r5], #-3171	; 0xfffff39d
     d40:	69000065 	stmdbvs	r0, {r0, r2, r5, r6}
     d44:	635f7463 	cmpvs	pc, #1660944384	; 0x63000000
     d48:	6b636568 	blvs	18da2f0 <ringBuffer+0x18825e8>
     d4c:	2e676e69 	cdpcs	14, 6, cr6, cr7, cr9, {3}
     d50:	00010063 	andeq	r0, r1, r3, rrx
     d54:	64747300 	ldrbtvs	r7, [r4], #-768	; 0xfffffd00
     d58:	2e666564 	cdpcs	5, 6, cr6, cr6, cr4, {3}
     d5c:	00020068 	andeq	r0, r2, r8, rrx
     d60:	70797400 	rsbsvc	r7, r9, r0, lsl #8
     d64:	682e7365 	stmdavs	lr!, {r0, r2, r5, r6, r8, r9, ip, sp, lr}
     d68:	00000300 	andeq	r0, r0, r0, lsl #6
     d6c:	6962696c 	stmdbvs	r2!, {r2, r3, r5, r6, r8, fp, sp, lr}^
     d70:	00682e6f 	rsbeq	r2, r8, pc, ror #28
     d74:	73000004 	movwvc	r0, #4
     d78:	6f696474 	svcvs	0x00696474
     d7c:	0400682e 	streq	r6, [r0], #-2094	; 0xfffff7d2
     d80:	79730000 	ldmdbvc	r3!, {}^	; <UNPREDICTABLE>
     d84:	72655f73 	rsbvc	r5, r5, #460	; 0x1cc
     d88:	73696c72 	cmnvc	r9, #29184	; 0x7200
     d8c:	00682e74 	rsbeq	r2, r8, r4, ror lr
     d90:	73000003 	movwvc	r0, #3
     d94:	6e696474 	mcrvs	4, 3, r6, cr9, cr4, {3}
     d98:	00682e74 	rsbeq	r2, r8, r4, ror lr
     d9c:	00000004 	andeq	r0, r0, r4
     da0:	c4020500 	strgt	r0, [r2], #-1280	; 0xfffffb00
     da4:	0300043c 	movweq	r0, #1084	; 0x43c
     da8:	0891011f 	ldmeq	r1, {r0, r1, r2, r3, r4, r8}
     dac:	f32108bb 	vceq.i32	d0, d17, d27
     db0:	682231f3 	stmdavs	r2!, {r0, r1, r4, r5, r6, r7, r8, ip, sp}
     db4:	30e60859 	rsccc	r0, r6, r9, asr r8
     db8:	132b02e5 			; <UNDEFINED> instruction: 0x132b02e5
     dbc:	084b5b22 	stmdaeq	fp, {r1, r5, r8, r9, fp, ip, lr}^
     dc0:	bb4c69d7 	bllt	131b524 <ringBuffer+0x12c381c>
     dc4:	3e6921bb 	mcrcc	1, 3, r2, cr9, cr11, {5}
     dc8:	0d03212f 	stfeqs	f2, [r3, #-188]	; 0xffffff44
     dcc:	5b596866 	blpl	165af6c <ringBuffer+0x1603264>
     dd0:	2f3d405c 	svccs	0x003d405c
     dd4:	02005c31 	andeq	r5, r0, #12544	; 0x3100
     dd8:	4a060104 	bmi	1811f0 <ringBuffer+0x1294e8>
     ddc:	5ee54e06 	cdppl	14, 14, cr4, cr5, cr6, {0}
     de0:	d60c0335 			; <UNDEFINED> instruction: 0xd60c0335
     de4:	83838359 	orrhi	r8, r3, #1677721601	; 0x64000001
     de8:	13270284 			; <UNDEFINED> instruction: 0x13270284
     dec:	c92fc92f 	stmdbgt	pc!, {r0, r1, r2, r3, r5, r8, fp, lr, pc}	; <UNPREDICTABLE>
     df0:	c92fc92f 	stmdbgt	pc!, {r0, r1, r2, r3, r5, r8, fp, lr, pc}	; <UNPREDICTABLE>
     df4:	01040200 	mrseq	r0, R12_usr
     df8:	02003c06 	andeq	r3, r0, #1536	; 0x600
     dfc:	00660304 	rsbeq	r0, r6, r4, lsl #6
     e00:	2e040402 	cdpcs	4, 0, cr0, cr4, cr2, {0}
     e04:	06040200 	streq	r0, [r4], -r0, lsl #4
     e08:	004b0620 	subeq	r0, fp, r0, lsr #12
     e0c:	06020402 	streq	r0, [r2], -r2, lsl #8
     e10:	04020066 	streq	r0, [r2], #-102	; 0xffffff9a
     e14:	02003c03 	andeq	r3, r0, #768	; 0x300
     e18:	002e0404 	eoreq	r0, lr, r4, lsl #8
     e1c:	20060402 	andcs	r0, r6, r2, lsl #8
     e20:	83834b06 	orrhi	r4, r3, #6144	; 0x1800
     e24:	01040200 	mrseq	r0, R12_usr
     e28:	02006606 	andeq	r6, r0, #6291456	; 0x600000
     e2c:	004a0304 	subeq	r0, sl, r4, lsl #6
     e30:	2e040402 	cdpcs	4, 0, cr0, cr4, cr2, {0}
     e34:	06040200 	streq	r0, [r4], -r0, lsl #4
     e38:	004b0620 	subeq	r0, fp, r0, lsr #12
     e3c:	06020402 	streq	r0, [r2], -r2, lsl #8
     e40:	0402003c 	streq	r0, [r2], #-60	; 0xffffffc4
     e44:	02004a03 	andeq	r4, r0, #12288	; 0x3000
     e48:	002e0404 	eoreq	r0, lr, r4, lsl #8
     e4c:	20060402 	andcs	r0, r6, r2, lsl #8
     e50:	222f4b06 	eorcs	r4, pc, #6144	; 0x1800
     e54:	5b59846a 	blpl	1662004 <ringBuffer+0x160a2fc>
     e58:	4e42795c 			; <UNDEFINED> instruction: 0x4e42795c
     e5c:	2f3d2f2f 	svccs	0x003d2f2f
     e60:	036ee55c 	cmneq	lr, #92, 10	; 0x17000000
     e64:	2f2f740c 	svccs	0x002f740c
     e68:	005c3f2f 	subseq	r3, ip, pc, lsr #30
     e6c:	06010402 	streq	r0, [r1], -r2, lsl #8
     e70:	e54e064a 	strb	r0, [lr, #-1610]	; 0xfffff9b6
     e74:	2e62035d 	mcrcs	3, 3, r0, cr2, cr13, {2}
     e78:	212e1e03 			; <UNDEFINED> instruction: 0x212e1e03
     e7c:	5b5984f5 	blpl	1662258 <ringBuffer+0x160a550>
     e80:	0040785c 	subeq	r7, r0, ip, asr r8
     e84:	06010402 	streq	r0, [r1], -r2, lsl #8
     e88:	2f40064a 	svccs	0x0040064a
     e8c:	5c2f3d2f 	stcpl	13, cr3, [pc], #-188	; dd8 <_init-0xfd48>
     e90:	587303e5 	ldmdapl	r3!, {r0, r2, r5, r6, r7, r8, r9}^
     e94:	03201503 			; <UNDEFINED> instruction: 0x03201503
     e98:	1f03826b 	svcne	0x0003826b
     e9c:	2f2f2f20 	svccs	0x002f2f20
     ea0:	02005c3f 	andeq	r5, r0, #16128	; 0x3f00
     ea4:	4a060104 	bmi	1812bc <ringBuffer+0x1295b4>
     ea8:	5de54e06 	stclpl	14, cr4, [r5, #24]!
     eac:	032e6403 			; <UNDEFINED> instruction: 0x032e6403
     eb0:	e8212e1c 	stmda	r1!, {r2, r3, r4, r9, sl, fp, sp}
     eb4:	5c5b5968 	mrrcpl	9, 6, r5, fp, cr8	; <UNPREDICTABLE>
     eb8:	312f2f40 			; <UNDEFINED> instruction: 0x312f2f40
     ebc:	0402005c 	streq	r0, [r2], #-92	; 0xffffffa4
     ec0:	004a0601 	subeq	r0, sl, r1, lsl #12
     ec4:	4a030402 	bmi	c1ed4 <ringBuffer+0x6a1cc>
     ec8:	e54e4b06 	strb	r4, [lr, #-2822]	; 0xfffff4fa
     ecc:	69cc3660 	stmibvs	ip, {r5, r6, r9, sl, ip, sp}^
     ed0:	405c5b59 	subsmi	r5, ip, r9, asr fp
     ed4:	005d322f 	subseq	r3, sp, pc, lsr #4
     ed8:	06010402 	streq	r0, [r1], -r2, lsl #8
     edc:	324b064a 	subcc	r0, fp, #77594624	; 0x4a00000
     ee0:	02005de5 	andeq	r5, r0, #14656	; 0x3940
     ee4:	4a060104 	bmi	1812fc <ringBuffer+0x1295f4>
     ee8:	e5324b06 	ldr	r4, [r2, #-2822]!	; 0xfffff4fa
     eec:	68e72f5d 	stmiavs	r7!, {r0, r2, r3, r4, r6, r8, r9, sl, fp, sp}^
     ef0:	405c5b59 	subsmi	r5, ip, r9, asr fp
     ef4:	005d322f 	subseq	r3, sp, pc, lsr #4
     ef8:	06010402 	streq	r0, [r1], -r2, lsl #8
     efc:	324b064a 	subcc	r0, fp, #77594624	; 0x4a00000
     f00:	580903e5 	stmdapl	r9, {r0, r2, r5, r6, r7, r8, r9}
     f04:	01040200 	mrseq	r0, R12_usr
     f08:	4b064a06 	blmi	193728 <ringBuffer+0x13ba20>
     f0c:	005de532 	subseq	lr, sp, r2, lsr r5
     f10:	06010402 	streq	r0, [r1], -r2, lsl #8
     f14:	324b064a 	subcc	r0, fp, #77594624	; 0x4a00000
     f18:	082f5fe5 	stmdaeq	pc!, {r0, r2, r5, r6, r7, r8, r9, sl, fp, ip, lr}	; <UNPREDICTABLE>
     f1c:	5b596915 	blpl	165b378 <ringBuffer+0x1603670>
     f20:	322f405c 	eorcc	r4, pc, #92	; 0x5c
     f24:	0402005d 	streq	r0, [r2], #-93	; 0xffffffa3
     f28:	064a0601 	strbeq	r0, [sl], -r1, lsl #12
     f2c:	e534434c 	ldr	r4, [r4, #-844]!	; 0xfffffcb4
     f30:	85da2f5c 	ldrbhi	r2, [sl, #3932]	; 0xf5c
     f34:	3d2f4077 	stccc	0, cr4, [pc, #-476]!	; d60 <_init-0xfdc0>
     f38:	e55b302f 	ldrb	r3, [fp, #-47]	; 0xffffffd1
     f3c:	0402005c 	streq	r0, [r2], #-92	; 0xffffffa4
     f40:	064a0601 	strbeq	r0, [sl], -r1, lsl #12
     f44:	322f4b4d 	eorcc	r4, pc, #78848	; 0x13400
     f48:	580b03e5 	stmdapl	fp, {r0, r2, r5, r6, r7, r8, r9}
     f4c:	01040200 	mrseq	r0, R12_usr
     f50:	4d064a06 	vstrmi	s8, [r6, #-24]	; 0xffffffe8
     f54:	e5322f4b 	ldr	r2, [r2, #-3915]!	; 0xfffff0b5
     f58:	03667003 	cmneq	r6, #3
     f5c:	f4262e14 			; <UNDEFINED> instruction: 0xf4262e14
     f60:	5b5b5984 	blpl	16d7578 <ringBuffer+0x167f870>
     f64:	2f3d2f77 	svccs	0x003d2f77
     f68:	5ee55d3e 	mcrpl	13, 7, r5, cr5, cr14, {1}
     f6c:	5984cb30 	stmibpl	r4, {r4, r5, r8, r9, fp, lr, pc}
     f70:	2f3f5b5b 	svccs	0x003f5b5b
     f74:	5e3e2f2f 	cdppl	15, 3, cr2, cr14, cr15, {1}
     f78:	db2f5de5 	blle	bd8714 <ringBuffer+0xb80a0c>
     f7c:	2f68214e 	svccs	0x0068214e
     f80:	594d4f5a 	stmdbpl	sp, {r1, r3, r4, r6, r8, r9, sl, fp, lr}^
     f84:	0008025c 	andeq	r0, r8, ip, asr r2
     f88:	02cd0101 	sbceq	r0, sp, #1073741824	; 0x40000000
     f8c:	00020000 	andeq	r0, r2, r0
     f90:	0000003b 	andeq	r0, r0, fp, lsr r0
     f94:	0efb0102 	cdpeq	1, 15, cr0, cr11, cr2, {0}
     f98:	0101000d 	tsteq	r1, sp
     f9c:	00000101 	andeq	r0, r0, r1, lsl #2
     fa0:	00000100 	andeq	r0, r0, r0, lsl #2
     fa4:	2f2e2e01 	svccs	0x002e2e01
     fa8:	742f2e2e 	strtvc	r2, [pc], #-3630	; fb0 <_init-0xfb70>
     fac:	706d6172 	rsbvc	r6, sp, r2, ror r1
     fb0:	6e696c6f 	cdpvs	12, 6, cr6, cr9, cr15, {3}
     fb4:	696c5f65 	stmdbvs	ip!, {r0, r2, r5, r6, r8, r9, sl, fp, ip, lr}^
     fb8:	74000062 	strvc	r0, [r0], #-98	; 0xffffff9e
     fbc:	706d6172 	rsbvc	r6, sp, r2, ror r1
     fc0:	6e696c6f 	cdpvs	12, 6, cr6, cr9, cr15, {3}
     fc4:	77665f65 	strbvc	r5, [r6, -r5, ror #30]!
     fc8:	0100532e 	tsteq	r0, lr, lsr #6
     fcc:	00000000 	andeq	r0, r0, r0
     fd0:	71600205 	cmnvc	r0, r5, lsl #4
     fd4:	21030005 	tstcs	r3, r5
     fd8:	2f2f2f01 	svccs	0x002f2f01
     fdc:	2f2f2f2f 	svccs	0x002f2f2f
     fe0:	2f2f2f2f 	svccs	0x002f2f2f
     fe4:	2f2f2f2f 	svccs	0x002f2f2f
     fe8:	2f2f2f2f 	svccs	0x002f2f2f
     fec:	2f2f2f2f 	svccs	0x002f2f2f
     ff0:	2f2f322f 	svccs	0x002f322f
     ff4:	2f2f2f2f 	svccs	0x002f2f2f
     ff8:	2f2f2f2f 	svccs	0x002f2f2f
     ffc:	2f2f2f2f 	svccs	0x002f2f2f
    1000:	2f2f2f2f 	svccs	0x002f2f2f
    1004:	2f2f2f2f 	svccs	0x002f2f2f
    1008:	2f312f2f 	svccs	0x00312f2f
    100c:	2f2f2f2f 	svccs	0x002f2f2f
    1010:	2f2f2f2f 	svccs	0x002f2f2f
    1014:	2f2f2f2f 	svccs	0x002f2f2f
    1018:	2f2f2f2f 	svccs	0x002f2f2f
    101c:	2f2f2f2f 	svccs	0x002f2f2f
    1020:	2f302f2f 	svccs	0x00302f2f
    1024:	2f332f31 	svccs	0x00332f31
    1028:	2f2f322f 	svccs	0x002f322f
    102c:	2f2f2f2f 	svccs	0x002f2f2f
    1030:	2f2f2f2f 	svccs	0x002f2f2f
    1034:	2f2f2f2f 	svccs	0x002f2f2f
    1038:	2f2f2f2f 	svccs	0x002f2f2f
    103c:	2f2f2f2f 	svccs	0x002f2f2f
    1040:	31312f2f 	teqcc	r1, pc, lsr #30
    1044:	31313131 	teqcc	r1, r1, lsr r1
    1048:	2f2f3431 	svccs	0x002f3431
    104c:	2f2f2f2f 	svccs	0x002f2f2f
    1050:	2f2f2f30 	svccs	0x002f2f30
    1054:	2f2f302f 	svccs	0x002f302f
    1058:	2f302f2f 	svccs	0x00302f2f
    105c:	2f313030 	svccs	0x00313030
    1060:	2f2f2f30 	svccs	0x002f2f30
    1064:	2f302f30 	svccs	0x00302f30
    1068:	2f312f33 	svccs	0x00312f33
    106c:	2f2f2f2f 	svccs	0x002f2f2f
    1070:	2f2f312f 	svccs	0x002f312f
    1074:	2f302f30 	svccs	0x00302f30
    1078:	2f302f30 	svccs	0x00302f30
    107c:	2f2f2f2f 	svccs	0x002f2f2f
    1080:	2f352f2f 	svccs	0x00352f2f
    1084:	2f2f2f2f 	svccs	0x002f2f2f
    1088:	2f2f312f 	svccs	0x002f312f
    108c:	2f302f2f 	svccs	0x00302f2f
    1090:	302f2f2f 	eorcc	r2, pc, pc, lsr #30
    1094:	3130302f 	teqcc	r0, pc, lsr #32
    1098:	2f2f302f 	svccs	0x002f302f
    109c:	302f302f 	eorcc	r3, pc, pc, lsr #32
    10a0:	312f332f 			; <UNDEFINED> instruction: 0x312f332f
    10a4:	2f2f2f2f 	svccs	0x002f2f2f
    10a8:	2f302f2f 	svccs	0x00302f2f
    10ac:	2f2f2f2f 	svccs	0x002f2f2f
    10b0:	2f352f2f 	svccs	0x00352f2f
    10b4:	312f2f2f 			; <UNDEFINED> instruction: 0x312f2f2f
    10b8:	2f2f2f2f 	svccs	0x002f2f2f
    10bc:	2f2f2f2f 	svccs	0x002f2f2f
    10c0:	2f2f3131 	svccs	0x002f3131
    10c4:	2f2f2f2f 	svccs	0x002f2f2f
    10c8:	2f312f2f 	svccs	0x00312f2f
    10cc:	312f2f2f 			; <UNDEFINED> instruction: 0x312f2f2f
    10d0:	2f323132 	svccs	0x00323132
    10d4:	322f2f2f 	eorcc	r2, pc, #47, 30	; 0xbc
    10d8:	2f2f2f2f 	svccs	0x002f2f2f
    10dc:	2f2f3531 	svccs	0x002f3531
    10e0:	2f2f2f2f 	svccs	0x002f2f2f
    10e4:	2f2f2f32 	svccs	0x002f2f32
    10e8:	2f2f302f 	svccs	0x002f302f
    10ec:	2f302f2f 	svccs	0x00302f2f
    10f0:	2f313030 	svccs	0x00313030
    10f4:	2f2f2f30 	svccs	0x002f2f30
    10f8:	2f302f30 	svccs	0x00302f30
    10fc:	2f312f32 	svccs	0x00312f32
    1100:	332f2f31 			; <UNDEFINED> instruction: 0x332f2f31
    1104:	2f2f2f32 	svccs	0x002f2f32
    1108:	2f342f2f 	svccs	0x00342f2f
    110c:	30302f30 	eorscc	r2, r0, r0, lsr pc
    1110:	2f2f352f 	svccs	0x002f352f
    1114:	2f302f31 	svccs	0x00302f31
    1118:	2f302f30 	svccs	0x00302f30
    111c:	2f2f2f2f 	svccs	0x002f2f2f
    1120:	2f342f2f 	svccs	0x00342f2f
    1124:	2f2f2f2f 	svccs	0x002f2f2f
    1128:	2f2f2f2f 	svccs	0x002f2f2f
    112c:	2f2f2f2f 	svccs	0x002f2f2f
    1130:	2f2f2f2f 	svccs	0x002f2f2f
    1134:	302f2f2f 	eorcc	r2, pc, pc, lsr #30
    1138:	2f2f2f36 	svccs	0x002f2f36
    113c:	322f2f2f 	eorcc	r2, pc, #47, 30	; 0xbc
    1140:	2f2f2f2f 	svccs	0x002f2f2f
    1144:	2f2f2f30 	svccs	0x002f2f30
    1148:	302f302f 	eorcc	r3, pc, pc, lsr #32
    114c:	302f3130 	eorcc	r3, pc, r0, lsr r1	; <UNPREDICTABLE>
    1150:	302f2f2f 	eorcc	r2, pc, pc, lsr #30
    1154:	322f302f 	eorcc	r3, pc, #47	; 0x2f
    1158:	2f2f322f 	svccs	0x002f322f
    115c:	2f2f2f2f 	svccs	0x002f2f2f
    1160:	2f2f2f30 	svccs	0x002f2f30
    1164:	2f2f2f2f 	svccs	0x002f2f2f
    1168:	2f2f2f31 	svccs	0x002f2f31
    116c:	2f2f2f2f 	svccs	0x002f2f2f
    1170:	2f2f2f2f 	svccs	0x002f2f2f
    1174:	2f2f2f2f 	svccs	0x002f2f2f
    1178:	2f2f2f2f 	svccs	0x002f2f2f
    117c:	2f35302f 	svccs	0x0035302f
    1180:	302f2f2f 	eorcc	r2, pc, pc, lsr #30
    1184:	2f2f2f2f 	svccs	0x002f2f2f
    1188:	2f302f2f 	svccs	0x00302f2f
    118c:	2f2f2f2f 	svccs	0x002f2f2f
    1190:	2f2f3131 	svccs	0x002f3131
    1194:	2f2f2f2f 	svccs	0x002f2f2f
    1198:	2f2f302f 	svccs	0x002f302f
    119c:	2f2f2f2f 	svccs	0x002f2f2f
    11a0:	2f2f2f31 	svccs	0x002f2f31
    11a4:	2f2f2f2f 	svccs	0x002f2f2f
    11a8:	2f2f2f2f 	svccs	0x002f2f2f
    11ac:	2f2f2f2f 	svccs	0x002f2f2f
    11b0:	2f2f2f2f 	svccs	0x002f2f2f
    11b4:	2f2f2f2f 	svccs	0x002f2f2f
    11b8:	2f31352f 	svccs	0x0031352f
    11bc:	302f2f2f 	eorcc	r2, pc, pc, lsr #30
    11c0:	2f2f2f2f 	svccs	0x002f2f2f
    11c4:	2f302f2f 	svccs	0x00302f2f
    11c8:	2f2f2f2f 	svccs	0x002f2f2f
    11cc:	2f2f3132 	svccs	0x002f3132
    11d0:	2f2f2f2f 	svccs	0x002f2f2f
    11d4:	2f2f302f 	svccs	0x002f302f
    11d8:	2f2f2f2f 	svccs	0x002f2f2f
    11dc:	2f2f312f 	svccs	0x002f312f
    11e0:	2f2f2f2f 	svccs	0x002f2f2f
    11e4:	2f2f2f2f 	svccs	0x002f2f2f
    11e8:	2f2f2f2f 	svccs	0x002f2f2f
    11ec:	2f2f2f2f 	svccs	0x002f2f2f
    11f0:	2f2f2f2f 	svccs	0x002f2f2f
    11f4:	362f2f2f 	strtcc	r2, [pc], -pc, lsr #30
    11f8:	2f2f2f2f 	svccs	0x002f2f2f
    11fc:	312f2f2f 			; <UNDEFINED> instruction: 0x312f2f2f
    1200:	2f2f2f2f 	svccs	0x002f2f2f
    1204:	2f2f2f30 	svccs	0x002f2f30
    1208:	302f302f 	eorcc	r3, pc, pc, lsr #32
    120c:	30313030 	eorscc	r3, r1, r0, lsr r0
    1210:	2f2f2f30 	svccs	0x002f2f30
    1214:	2f302f2f 	svccs	0x00302f2f
    1218:	2f2f2f2f 	svccs	0x002f2f2f
    121c:	322f2f2f 	eorcc	r2, pc, #47, 30	; 0xbc
    1220:	2f2f312f 	svccs	0x002f312f
    1224:	2f312f32 	svccs	0x00312f32
    1228:	2f2f2f2f 	svccs	0x002f2f2f
    122c:	2f312f2f 	svccs	0x00312f2f
    1230:	2f2f2f2f 	svccs	0x002f2f2f
    1234:	31302f2f 	teqcc	r0, pc, lsr #30
    1238:	032f312f 			; <UNDEFINED> instruction: 0x032f312f
    123c:	d002799e 	mulle	r2, lr, r9
    1240:	96030101 	strls	r0, [r3], -r1, lsl #2
    1244:	2b032e01 	blcs	cca50 <ringBuffer+0x74d48>
    1248:	b803322e 	stmdalt	r3, {r1, r2, r3, r5, r9, ip, sp}
    124c:	84032e01 	strhi	r2, [r3], #-3585	; 0xfffff1ff
    1250:	8e032e02 	cdphi	14, 0, cr2, cr3, cr2, {0}
    1254:	02022e01 	andeq	r2, r2, #1, 28
    1258:	8a010100 	bhi	41660 <blake2s_compress+0x7a8>
    125c:	02000000 	andeq	r0, r0, #0
    1260:	00003800 	andeq	r3, r0, r0, lsl #16
    1264:	fb010200 	blx	41a6e <blake2s_compress+0xbb6>
    1268:	01000d0e 	tsteq	r0, lr, lsl #26
    126c:	00010101 	andeq	r0, r1, r1, lsl #2
    1270:	00010000 	andeq	r0, r1, r0
    1274:	2e2e0100 	sufcse	f0, f6, f0
    1278:	2f2e2e2f 	svccs	0x002e2e2f
    127c:	6d617274 	sfmvs	f7, 2, [r1, #-464]!	; 0xfffffe30
    1280:	696c6f70 	stmdbvs	ip!, {r4, r5, r6, r8, r9, sl, fp, sp, lr}^
    1284:	6c5f656e 	cfldr64vs	mvdx6, [pc], {110}	; 0x6e
    1288:	00006269 	andeq	r6, r0, r9, ror #4
    128c:	6d617274 	sfmvs	f7, 2, [r1, #-464]!	; 0xfffffe30
    1290:	696c6f70 	stmdbvs	ip!, {r4, r5, r6, r8, r9, sl, fp, sp, lr}^
    1294:	532e656e 			; <UNDEFINED> instruction: 0x532e656e
    1298:	00000100 	andeq	r0, r0, r0, lsl #2
    129c:	02050000 	andeq	r0, r5, #0
    12a0:	0004656c 	andeq	r6, r4, ip, ror #10
    12a4:	2f010d03 	svccs	0x00010d03
    12a8:	2f2f2f2f 	svccs	0x002f2f2f
    12ac:	2f2f2f2f 	svccs	0x002f2f2f
    12b0:	2f2f2f2f 	svccs	0x002f2f2f
    12b4:	2f2f2f2f 	svccs	0x002f2f2f
    12b8:	2f2f2f2f 	svccs	0x002f2f2f
    12bc:	2f2f2f2f 	svccs	0x002f2f2f
    12c0:	2f2f2f2f 	svccs	0x002f2f2f
    12c4:	2f2f2f2f 	svccs	0x002f2f2f
    12c8:	2f2f2f2f 	svccs	0x002f2f2f
    12cc:	2f2f2f32 	svccs	0x002f2f32
    12d0:	2f2f2f2f 	svccs	0x002f2f2f
    12d4:	2f2f2f2f 	svccs	0x002f2f2f
    12d8:	2f2f2f32 	svccs	0x002f2f32
    12dc:	2f2f2f32 	svccs	0x002f2f32
    12e0:	2f2f2f32 	svccs	0x002f2f32
    12e4:	01000202 	tsteq	r0, r2, lsl #4
    12e8:	0003a001 	andeq	sl, r3, r1
    12ec:	bd000200 	sfmlt	f0, 4, [r0, #-0]
    12f0:	02000002 	andeq	r0, r0, #2
    12f4:	0d0efb01 	vstreq	d15, [lr, #-4]
    12f8:	01010100 	mrseq	r0, (UNDEF: 17)
    12fc:	00000001 	andeq	r0, r0, r1
    1300:	01000001 	tsteq	r0, r1
    1304:	2e2f2e2e 	cdpcs	14, 2, cr2, cr15, cr14, {1}
    1308:	72742f2e 	rsbsvc	r2, r4, #46, 30	; 0xb8
    130c:	6f706d61 	svcvs	0x00706d61
    1310:	656e696c 	strbvs	r6, [lr, #-2412]!	; 0xfffff694
    1314:	62696c5f 	rsbvs	r6, r9, #24320	; 0x5f00
    1318:	6f682f00 	svcvs	0x00682f00
    131c:	7a2f656d 	bvc	bda8d8 <ringBuffer+0xb82bd0>
    1320:	35307a72 	ldrcc	r7, [r0, #-2674]!	; 0xfffff58e
    1324:	732f3731 			; <UNDEFINED> instruction: 0x732f3731
    1328:	79647574 	stmdbvc	r4!, {r2, r4, r5, r6, r8, sl, ip, sp, lr}^
    132c:	6168632f 	cmnvs	r8, pc, lsr #6
    1330:	615f6e69 	cmpvs	pc, r9, ror #28
    1334:	73657474 	cmnvc	r5, #116, 8	; 0x74000000
    1338:	69746174 	ldmdbvs	r4!, {r2, r4, r5, r6, r8, sp, lr}^
    133c:	412f6e6f 			; <UNDEFINED> instruction: 0x412f6e6f
    1340:	7a2d4952 	bvc	b53890 <ringBuffer+0xafbb88>
    1344:	672f7a72 			; <UNDEFINED> instruction: 0x672f7a72
    1348:	6c2d6363 	stcvs	3, cr6, [sp], #-396	; 0xfffffe74
    134c:	72616e69 	rsbvc	r6, r1, #1680	; 0x690
    1350:	2e362d6f 	cdpcs	13, 3, cr2, cr6, cr15, {3}
    1354:	2d312e32 	ldccs	14, cr2, [r1, #-200]!	; 0xffffff38
    1358:	36313032 			; <UNDEFINED> instruction: 0x36313032
    135c:	2d31312e 	ldfcss	f3, [r1, #-184]!	; 0xffffff48
    1360:	5f363878 	svcpl	0x00363878
    1364:	615f3436 	cmpvs	pc, r6, lsr r4	; <UNPREDICTABLE>
    1368:	6c2d6d72 	stcvs	13, cr6, [sp], #-456	; 0xfffffe38
    136c:	78756e69 	ldmdavc	r5!, {r0, r3, r5, r6, r9, sl, fp, sp, lr}^
    1370:	756e672d 	strbvc	r6, [lr, #-1837]!	; 0xfffff8d3
    1374:	69626165 	stmdbvs	r2!, {r0, r2, r5, r6, r8, sp, lr}^
    1378:	612f6668 			; <UNDEFINED> instruction: 0x612f6668
    137c:	6c2d6d72 	stcvs	13, cr6, [sp], #-456	; 0xfffffe38
    1380:	78756e69 	ldmdavc	r5!, {r0, r3, r5, r6, r9, sl, fp, sp, lr}^
    1384:	756e672d 	strbvc	r6, [lr, #-1837]!	; 0xfffff8d3
    1388:	69626165 	stmdbvs	r2!, {r0, r2, r5, r6, r8, sp, lr}^
    138c:	6c2f6668 	stcvs	6, cr6, [pc], #-416	; 11f4 <_init-0xf92c>
    1390:	2f636269 	svccs	0x00636269
    1394:	2f727375 	svccs	0x00727375
    1398:	6c636e69 	stclvs	14, cr6, [r3], #-420	; 0xfffffe5c
    139c:	2f656475 	svccs	0x00656475
    13a0:	73746962 	cmnvc	r4, #1605632	; 0x188000
    13a4:	6f682f00 	svcvs	0x00682f00
    13a8:	7a2f656d 	bvc	bda964 <ringBuffer+0xb82c5c>
    13ac:	35307a72 	ldrcc	r7, [r0, #-2674]!	; 0xfffff58e
    13b0:	732f3731 			; <UNDEFINED> instruction: 0x732f3731
    13b4:	79647574 	stmdbvc	r4!, {r2, r4, r5, r6, r8, sl, ip, sp, lr}^
    13b8:	6168632f 	cmnvs	r8, pc, lsr #6
    13bc:	615f6e69 	cmpvs	pc, r9, ror #28
    13c0:	73657474 	cmnvc	r5, #116, 8	; 0x74000000
    13c4:	69746174 	ldmdbvs	r4!, {r2, r4, r5, r6, r8, sp, lr}^
    13c8:	412f6e6f 			; <UNDEFINED> instruction: 0x412f6e6f
    13cc:	7a2d4952 	bvc	b5391c <ringBuffer+0xafbc14>
    13d0:	672f7a72 			; <UNDEFINED> instruction: 0x672f7a72
    13d4:	6c2d6363 	stcvs	3, cr6, [sp], #-396	; 0xfffffe74
    13d8:	72616e69 	rsbvc	r6, r1, #1680	; 0x690
    13dc:	2e362d6f 	cdpcs	13, 3, cr2, cr6, cr15, {3}
    13e0:	2d312e32 	ldccs	14, cr2, [r1, #-200]!	; 0xffffff38
    13e4:	36313032 			; <UNDEFINED> instruction: 0x36313032
    13e8:	2d31312e 	ldfcss	f3, [r1, #-184]!	; 0xffffff48
    13ec:	5f363878 	svcpl	0x00363878
    13f0:	615f3436 	cmpvs	pc, r6, lsr r4	; <UNPREDICTABLE>
    13f4:	6c2d6d72 	stcvs	13, cr6, [sp], #-456	; 0xfffffe38
    13f8:	78756e69 	ldmdavc	r5!, {r0, r3, r5, r6, r9, sl, fp, sp, lr}^
    13fc:	756e672d 	strbvc	r6, [lr, #-1837]!	; 0xfffff8d3
    1400:	69626165 	stmdbvs	r2!, {r0, r2, r5, r6, r8, sp, lr}^
    1404:	6c2f6668 	stcvs	6, cr6, [pc], #-416	; 126c <_init-0xf8b4>
    1408:	672f6269 	strvs	r6, [pc, -r9, ror #4]!
    140c:	612f6363 			; <UNDEFINED> instruction: 0x612f6363
    1410:	6c2d6d72 	stcvs	13, cr6, [sp], #-456	; 0xfffffe38
    1414:	78756e69 	ldmdavc	r5!, {r0, r3, r5, r6, r9, sl, fp, sp, lr}^
    1418:	756e672d 	strbvc	r6, [lr, #-1837]!	; 0xfffff8d3
    141c:	69626165 	stmdbvs	r2!, {r0, r2, r5, r6, r8, sp, lr}^
    1420:	362f6668 	strtcc	r6, [pc], -r8, ror #12
    1424:	312e322e 			; <UNDEFINED> instruction: 0x312e322e
    1428:	636e692f 	cmnvs	lr, #770048	; 0xbc000
    142c:	6564756c 	strbvs	r7, [r4, #-1388]!	; 0xfffffa94
    1430:	6f682f00 	svcvs	0x00682f00
    1434:	7a2f656d 	bvc	bda9f0 <ringBuffer+0xb82ce8>
    1438:	35307a72 	ldrcc	r7, [r0, #-2674]!	; 0xfffff58e
    143c:	732f3731 			; <UNDEFINED> instruction: 0x732f3731
    1440:	79647574 	stmdbvc	r4!, {r2, r4, r5, r6, r8, sl, ip, sp, lr}^
    1444:	6168632f 	cmnvs	r8, pc, lsr #6
    1448:	615f6e69 	cmpvs	pc, r9, ror #28
    144c:	73657474 	cmnvc	r5, #116, 8	; 0x74000000
    1450:	69746174 	ldmdbvs	r4!, {r2, r4, r5, r6, r8, sp, lr}^
    1454:	412f6e6f 			; <UNDEFINED> instruction: 0x412f6e6f
    1458:	7a2d4952 	bvc	b539a8 <ringBuffer+0xafbca0>
    145c:	672f7a72 			; <UNDEFINED> instruction: 0x672f7a72
    1460:	6c2d6363 	stcvs	3, cr6, [sp], #-396	; 0xfffffe74
    1464:	72616e69 	rsbvc	r6, r1, #1680	; 0x690
    1468:	2e362d6f 	cdpcs	13, 3, cr2, cr6, cr15, {3}
    146c:	2d312e32 	ldccs	14, cr2, [r1, #-200]!	; 0xffffff38
    1470:	36313032 			; <UNDEFINED> instruction: 0x36313032
    1474:	2d31312e 	ldfcss	f3, [r1, #-184]!	; 0xffffff48
    1478:	5f363878 	svcpl	0x00363878
    147c:	615f3436 	cmpvs	pc, r6, lsr r4	; <UNPREDICTABLE>
    1480:	6c2d6d72 	stcvs	13, cr6, [sp], #-456	; 0xfffffe38
    1484:	78756e69 	ldmdavc	r5!, {r0, r3, r5, r6, r9, sl, fp, sp, lr}^
    1488:	756e672d 	strbvc	r6, [lr, #-1837]!	; 0xfffff8d3
    148c:	69626165 	stmdbvs	r2!, {r0, r2, r5, r6, r8, sp, lr}^
    1490:	612f6668 			; <UNDEFINED> instruction: 0x612f6668
    1494:	6c2d6d72 	stcvs	13, cr6, [sp], #-456	; 0xfffffe38
    1498:	78756e69 	ldmdavc	r5!, {r0, r3, r5, r6, r9, sl, fp, sp, lr}^
    149c:	756e672d 	strbvc	r6, [lr, #-1837]!	; 0xfffff8d3
    14a0:	69626165 	stmdbvs	r2!, {r0, r2, r5, r6, r8, sp, lr}^
    14a4:	6c2f6668 	stcvs	6, cr6, [pc], #-416	; 130c <_init-0xf814>
    14a8:	2f636269 	svccs	0x00636269
    14ac:	2f727375 	svccs	0x00727375
    14b0:	6c636e69 	stclvs	14, cr6, [r3], #-420	; 0xfffffe5c
    14b4:	00656475 	rsbeq	r6, r5, r5, ror r4
    14b8:	2e2f2e2e 	cdpcs	14, 2, cr2, cr15, cr14, {1}
    14bc:	706f2f2e 	rsbvc	r2, pc, lr, lsr #30
    14c0:	5f656574 	svcpl	0x00656574
    14c4:	65696c63 	strbvs	r6, [r9, #-3171]!	; 0xfffff39d
    14c8:	6d2d746e 	cfstrsvs	mvf7, [sp, #-440]!	; 0xfffffe48
    14cc:	65747361 	ldrbvs	r7, [r4, #-865]!	; 0xfffffc9f
    14d0:	756f2f72 	strbvc	r2, [pc, #-3954]!	; 566 <_init-0x105ba>
    14d4:	78652f74 	stmdavc	r5!, {r2, r4, r5, r6, r8, r9, sl, fp, sp}^
    14d8:	74726f70 	ldrbtvc	r6, [r2], #-3952	; 0xfffff090
    14dc:	636e692f 	cmnvs	lr, #770048	; 0xbc000
    14e0:	6564756c 	strbvs	r7, [r4, #-1388]!	; 0xfffffa94
    14e4:	61740000 	cmnvs	r4, r0
    14e8:	6172745f 	cmnvs	r2, pc, asr r4
    14ec:	6c6f706d 	stclvs	0, cr7, [pc], #-436	; 1340 <_init-0xf7e0>
    14f0:	2e656e69 	cdpcs	14, 6, cr6, cr5, cr9, {3}
    14f4:	00010063 	andeq	r0, r1, r3, rrx
    14f8:	70797400 	rsbsvc	r7, r9, r0, lsl #8
    14fc:	682e7365 	stmdavs	lr!, {r0, r2, r5, r6, r8, r9, ip, sp, lr}
    1500:	00000200 	andeq	r0, r0, r0, lsl #4
    1504:	64647473 	strbtvs	r7, [r4], #-1139	; 0xfffffb8d
    1508:	682e6665 	stmdavs	lr!, {r0, r2, r5, r6, r9, sl, sp, lr}
    150c:	00000300 	andeq	r0, r0, r0, lsl #6
    1510:	73696e75 	cmnvc	r9, #1872	; 0x750
    1514:	682e6474 	stmdavs	lr!, {r2, r4, r5, r6, sl, sp, lr}
    1518:	00000400 	andeq	r0, r0, r0, lsl #8
    151c:	6f746567 	svcvs	0x00746567
    1520:	682e7470 	stmdavs	lr!, {r4, r5, r6, sl, ip, sp, lr}
    1524:	00000400 	andeq	r0, r0, r0, lsl #8
    1528:	6e676973 			; <UNDEFINED> instruction: 0x6e676973
    152c:	682e6c61 	stmdavs	lr!, {r0, r5, r6, sl, fp, sp, lr}
    1530:	00000400 	andeq	r0, r0, r0, lsl #8
    1534:	72687470 	rsbvc	r7, r8, #112, 8	; 0x70000000
    1538:	74646165 	strbtvc	r6, [r4], #-357	; 0xfffffe9b
    153c:	73657079 	cmnvc	r5, #121	; 0x79
    1540:	0200682e 	andeq	r6, r0, #3014656	; 0x2e0000
    1544:	74730000 	ldrbtvc	r0, [r3], #-0
    1548:	2e6f6964 	vnmulcs.f16	s13, s30, s9	; <UNPREDICTABLE>
    154c:	00040068 	andeq	r0, r4, r8, rrx
    1550:	62696c00 	rsbvs	r6, r9, #0, 24
    1554:	682e6f69 	stmdavs	lr!, {r0, r3, r5, r6, r8, r9, sl, fp, sp, lr}
    1558:	00000400 	andeq	r0, r0, r0, lsl #8
    155c:	5f737973 	svcpl	0x00737973
    1560:	6c727265 	lfmvs	f7, 2, [r2], #-404	; 0xfffffe6c
    1564:	2e747369 	cdpcs	3, 7, cr7, cr4, cr9, {3}
    1568:	00020068 	andeq	r0, r2, r8, rrx
    156c:	6c616d00 	stclvs	13, cr6, [r1], #-0
    1570:	2e636f6c 	cdpcs	15, 6, cr6, cr3, cr12, {3}
    1574:	00040068 	andeq	r0, r4, r8, rrx
    1578:	6d697400 	cfstrdvs	mvd7, [r9, #-0]
    157c:	00682e65 	rsbeq	r2, r8, r5, ror #28
    1580:	73000004 	movwvc	r0, #4
    1584:	6e696474 	mcrvs	4, 3, r6, cr9, cr4, {3}
    1588:	00682e74 	rsbeq	r2, r8, r4, ror lr
    158c:	74000004 	strvc	r0, [r0], #-4
    1590:	635f6565 	cmpvs	pc, #423624704	; 0x19400000
    1594:	6e65696c 	vnmulvs.f16	s13, s10, s25	; <UNPREDICTABLE>
    1598:	70615f74 	rsbvc	r5, r1, r4, ror pc
    159c:	00682e69 	rsbeq	r2, r8, r9, ror #28
    15a0:	62000005 	andvs	r0, r0, #5
    15a4:	656b616c 	strbvs	r6, [fp, #-364]!	; 0xfffffe94
    15a8:	00682e32 	rsbeq	r2, r8, r2, lsr lr
    15ac:	00000001 	andeq	r0, r0, r1
    15b0:	9c020500 	cfstr32ls	mvfx0, [r2], {-0}
    15b4:	03000449 	movweq	r0, #1097	; 0x449
    15b8:	4c0100c5 	stcmi	0, cr0, [r1], {197}	; 0xc5
    15bc:	5b595b59 	blpl	1658328 <ringBuffer+0x1600620>
    15c0:	591b6059 	ldmdbpl	fp, {r0, r3, r4, r6, sp, lr}
    15c4:	bf307791 	svclt	0x00307791
    15c8:	44087a86 	strmi	r7, [r8], #-2694	; 0xfffff57a
    15cc:	9f594d84 	svcls	0x00594d84
    15d0:	3e08a559 	cfrshl32cc	mvfx8, mvfx9, sl
    15d4:	5e75b159 	mrcpl	1, 3, fp, cr5, cr9, {2}
    15d8:	694b4b4b 	stmdbvs	fp, {r0, r1, r3, r6, r8, r9, fp, lr}^
    15dc:	550359ca 	strpl	r5, [r3, #-2506]	; 0xfffff636
    15e0:	203703ac 	eorscs	r0, r7, ip, lsr #7
    15e4:	7550be08 	ldrbvc	fp, [r0, #-3592]	; 0xfffff1f8
    15e8:	59ca695a 	stmibpl	sl, {r1, r3, r4, r6, r8, fp, sp, lr}^
    15ec:	6876e6b0 	ldmdavs	r6!, {r4, r5, r7, r9, sl, sp, lr, pc}^
    15f0:	675b685a 			; <UNDEFINED> instruction: 0x675b685a
    15f4:	753e7567 	ldrvc	r7, [lr, #-1383]!	; 0xfffffa99
    15f8:	9f681e40 	svcls	0x00681e40
    15fc:	04020059 	streq	r0, [r2], #-89	; 0xffffffa7
    1600:	02003d03 	andeq	r3, r0, #3, 26	; 0xc0
    1604:	009d0304 	addseq	r0, sp, r4, lsl #6
    1608:	06010402 	streq	r0, [r1], -r2, lsl #8
    160c:	3d4d063c 	stclcc	6, cr0, [sp, #-240]	; 0xffffff10
    1610:	3da1756a 	cfstr32cc	mvfx7, [r1, #424]!	; 0x1a8
    1614:	c93d3ed7 	ldmdbgt	sp!, {r0, r1, r2, r4, r6, r7, r9, sl, fp, ip, sp}
    1618:	3dd7cdd8 	ldclcc	13, cr12, [r7, #864]	; 0x360
    161c:	02004cc9 	andeq	r4, r0, #51456	; 0xc900
    1620:	6e030204 	cdpvs	2, 0, cr0, cr3, cr4, {0}
    1624:	040200c8 	streq	r0, [r2], #-200	; 0xffffff38
    1628:	063c0601 	ldrteq	r0, [ip], -r1, lsl #12
    162c:	083c1503 	ldmdaeq	ip!, {r0, r1, r8, sl, ip}
    1630:	41a25f13 			; <UNDEFINED> instruction: 0x41a25f13
    1634:	59593e86 	ldmdbpl	r9, {r1, r2, r7, r9, sl, fp, ip, sp}^
    1638:	5bbb5c91 	blpl	feed8884 <__bss_end__+0xf55ea280>
    163c:	41821903 	orrmi	r1, r2, r3, lsl #18
    1640:	00794085 	rsbseq	r4, r9, r5, lsl #1
    1644:	06010402 	streq	r0, [r1], -r2, lsl #8
    1648:	59590682 	ldmdbpl	r9, {r1, r7, r9, sl}^
    164c:	67915abb 			; <UNDEFINED> instruction: 0x67915abb
    1650:	21202803 			; <UNDEFINED> instruction: 0x21202803
    1654:	59162302 	ldmdbpl	r6, {r1, r8, r9, sp}
    1658:	67833e75 			; <UNDEFINED> instruction: 0x67833e75
    165c:	af681e40 	svcge	0x00681e40
    1660:	003d7667 	eorseq	r7, sp, r7, ror #12
    1664:	3d030402 	cfstrscc	mvf0, [r3, #-8]
    1668:	03040200 	movweq	r0, #16896	; 0x4200
    166c:	040200ab 	streq	r0, [r2], #-171	; 0xffffff55
    1670:	063c0601 	ldrteq	r0, [ip], -r1, lsl #12
    1674:	3c0c034d 	stccc	3, cr0, [ip], {77}	; 0x4d
    1678:	03207703 			; <UNDEFINED> instruction: 0x03207703
    167c:	5cad6609 	stcpl	6, cr6, [sp], #36	; 0x24
    1680:	082159cb 	stmdaeq	r1!, {r0, r1, r3, r6, r7, r8, fp, ip, lr}
    1684:	4b754c21 	blmi	1d54710 <ringBuffer+0x1cfca08>
    1688:	01000402 	tsteq	r0, r2, lsl #8
    168c:	00005501 	andeq	r5, r0, r1, lsl #10
    1690:	2d000200 	sfmcs	f0, 4, [r0, #-0]
    1694:	02000000 	andeq	r0, r0, #0
    1698:	0d0efb01 	vstreq	d15, [lr, #-4]
    169c:	01010100 	mrseq	r0, (UNDEF: 17)
    16a0:	00000001 	andeq	r0, r0, r1
    16a4:	01000001 	tsteq	r0, r1
    16a8:	732f2e2e 			; <UNDEFINED> instruction: 0x732f2e2e
    16ac:	65647379 	strbvs	r7, [r4, #-889]!	; 0xfffffc87
    16b0:	612f7370 			; <UNDEFINED> instruction: 0x612f7370
    16b4:	00006d72 	andeq	r6, r0, r2, ror sp
    16b8:	72617473 	rsbvc	r7, r1, #1929379840	; 0x73000000
    16bc:	00532e74 	subseq	r2, r3, r4, ror lr
    16c0:	00000001 	andeq	r0, r0, r1
    16c4:	14020500 	strne	r0, [r2], #-1280	; 0xfffffb00
    16c8:	03000451 	movweq	r0, #1105	; 0x451
    16cc:	2f0100ce 	svccs	0x000100ce
    16d0:	23232131 			; <UNDEFINED> instruction: 0x23232131
    16d4:	31201703 			; <UNDEFINED> instruction: 0x31201703
    16d8:	32242131 	eorcc	r2, r4, #1073741836	; 0x4000000c
    16dc:	342e7103 	strtcc	r7, [lr], #-259	; 0xfffffefd
    16e0:	0002022f 	andeq	r0, r2, pc, lsr #4
    16e4:	00230101 	eoreq	r0, r3, r1, lsl #2
    16e8:	00020000 	andeq	r0, r2, r0
    16ec:	0000001d 	andeq	r0, r0, sp, lsl r0
    16f0:	0efb0102 	cdpeq	1, 15, cr0, cr11, cr2, {0}
    16f4:	0101000d 	tsteq	r1, sp
    16f8:	00000101 	andeq	r0, r0, r1, lsl #2
    16fc:	00000100 	andeq	r0, r0, r0, lsl #2
    1700:	6e690001 	cdpvs	0, 6, cr0, cr9, cr1, {0}
    1704:	632e7469 			; <UNDEFINED> instruction: 0x632e7469
    1708:	00000000 	andeq	r0, r0, r0
    170c:	00006800 	andeq	r6, r0, r0, lsl #16
    1710:	2c000200 	sfmcs	f0, 4, [r0], {-0}
    1714:	02000000 	andeq	r0, r0, #0
    1718:	0d0efb01 	vstreq	d15, [lr, #-4]
    171c:	01010100 	mrseq	r0, (UNDEF: 17)
    1720:	00000001 	andeq	r0, r0, r1
    1724:	01000001 	tsteq	r0, r1
    1728:	732f2e2e 			; <UNDEFINED> instruction: 0x732f2e2e
    172c:	65647379 	strbvs	r7, [r4, #-889]!	; 0xfffffc87
    1730:	612f7370 			; <UNDEFINED> instruction: 0x612f7370
    1734:	00006d72 	andeq	r6, r0, r2, ror sp
    1738:	69747263 	ldmdbvs	r4!, {r0, r1, r5, r6, r9, ip, sp, lr}^
    173c:	0100532e 	tsteq	r0, lr, lsr #6
    1740:	00000000 	andeq	r0, r0, r0
    1744:	51440205 	cmppl	r4, r5, lsl #4
    1748:	3f030004 	svccc	0x00030004
    174c:	2f302f01 	svccs	0x00302f01
    1750:	022f2f2f 	eoreq	r2, pc, #47, 30	; 0xbc
    1754:	01010006 	tsteq	r1, r6
    1758:	20020500 	andcs	r0, r2, r0, lsl #10
    175c:	0300010b 	movweq	r0, #267	; 0x10b
    1760:	300100d2 	ldrdcc	r0, [r1], -r2
    1764:	01000202 	tsteq	r0, r2, lsl #4
    1768:	02050001 	andeq	r0, r5, #1
    176c:	00046664 	andeq	r6, r4, r4, ror #12
    1770:	0100de03 	tsteq	r0, r3, lsl #28
    1774:	01000202 	tsteq	r0, r2, lsl #4
    1778:	00005001 	andeq	r5, r0, r1
    177c:	2c000200 	sfmcs	f0, 4, [r0], {-0}
    1780:	02000000 	andeq	r0, r0, #0
    1784:	0d0efb01 	vstreq	d15, [lr, #-4]
    1788:	01010100 	mrseq	r0, (UNDEF: 17)
    178c:	00000001 	andeq	r0, r0, r1
    1790:	01000001 	tsteq	r0, r1
    1794:	732f2e2e 			; <UNDEFINED> instruction: 0x732f2e2e
    1798:	65647379 	strbvs	r7, [r4, #-889]!	; 0xfffffc87
    179c:	612f7370 			; <UNDEFINED> instruction: 0x612f7370
    17a0:	00006d72 	andeq	r6, r0, r2, ror sp
    17a4:	6e747263 	cdpvs	2, 7, cr7, cr4, cr3, {3}
    17a8:	0100532e 	tsteq	r0, lr, lsr #6
    17ac:	00000000 	andeq	r0, r0, r0
    17b0:	0b280205 	bleq	a01fcc <ringBuffer+0x9aa2c4>
    17b4:	2f030001 	svccs	0x00030001
    17b8:	00020201 	andeq	r0, r2, r1, lsl #4
    17bc:	05000101 	streq	r0, [r0, #-257]	; 0xfffffeff
    17c0:	04666802 	strbteq	r6, [r6], #-2050	; 0xfffff7fe
    17c4:	01370300 	teqeq	r7, r0, lsl #6
    17c8:	01000202 	tsteq	r0, r2, lsl #4
    17cc:	地址 0x00000000000017cc 越界。


Disassembly of section .debug_frame:

00000000 <.debug_frame>:
   0:	00000010 	andeq	r0, r0, r0, lsl r0
   4:	ffffffff 			; <UNDEFINED> instruction: 0xffffffff
   8:	00040004 	andeq	r0, r4, r4
   c:	0c0e7c01 	stceq	12, cr7, [lr], {1}
  10:	0000000d 	andeq	r0, r0, sp
  14:	0000001c 	andeq	r0, r0, ip, lsl r0
  18:	00000000 	andeq	r0, r0, r0
  1c:	00040000 	andeq	r0, r4, r0
  20:	00000108 	andeq	r0, r0, r8, lsl #2
  24:	8e100e44 	cdphi	14, 1, cr0, cr0, cr4, {2}
  28:	85028b01 	strhi	r8, [r2, #-2817]	; 0xfffff4ff
  2c:	44048403 	strmi	r8, [r4], #-1027	; 0xfffffbfd
  30:	00080b0c 	andeq	r0, r8, ip, lsl #22
  34:	00000020 	andeq	r0, r0, r0, lsr #32
  38:	00000000 	andeq	r0, r0, r0
  3c:	00040108 	andeq	r0, r4, r8, lsl #2
  40:	000000c8 	andeq	r0, r0, r8, asr #1
  44:	8e100e44 	cdphi	14, 1, cr0, cr0, cr4, {2}
  48:	85028b01 	strhi	r8, [r2, #-2817]	; 0xfffff4ff
  4c:	44048403 	strmi	r8, [r4], #-1027	; 0xfffffbfd
  50:	44080b0c 	strmi	r0, [r8], #-2828	; 0xfffff4f4
  54:	06028805 	streq	r8, [r2], -r5, lsl #16
  58:	00000020 	andeq	r0, r0, r0, lsr #32
  5c:	00000000 	andeq	r0, r0, r0
  60:	00020000 	andeq	r0, r2, r0
  64:	00000178 	andeq	r0, r0, r8, ror r1
  68:	8e100e44 	cdphi	14, 1, cr0, cr0, cr4, {2}
  6c:	8a028b01 	bhi	a2c78 <ringBuffer+0x4af70>
  70:	44048403 	strmi	r8, [r4], #-1027	; 0xfffffbfd
  74:	44080b0c 	strmi	r0, [r8], #-2828	; 0xfffff4f4
  78:	06028805 	streq	r8, [r2], -r5, lsl #16
  7c:	00000020 	andeq	r0, r0, r0, lsr #32
  80:	00000000 	andeq	r0, r0, r0
  84:	00020178 	andeq	r0, r2, r8, ror r1
  88:	00000200 	andeq	r0, r0, r0, lsl #4
  8c:	8e100e44 	cdphi	14, 1, cr0, cr0, cr4, {2}
  90:	85028b01 	strhi	r8, [r2, #-2817]	; 0xfffff4ff
  94:	44048403 	strmi	r8, [r4], #-1027	; 0xfffffbfd
  98:	44080b0c 	strmi	r0, [r8], #-2828	; 0xfffff4f4
  9c:	06028805 	streq	r8, [r2], -r5, lsl #16
  a0:	00000024 	andeq	r0, r0, r4, lsr #32
  a4:	00000000 	andeq	r0, r0, r0
  a8:	00020378 	andeq	r0, r2, r8, ror r3
  ac:	000001ec 	andeq	r0, r0, ip, ror #3
  b0:	8e100e44 	cdphi	14, 1, cr0, cr0, cr4, {2}
  b4:	8a028b01 	bhi	a2cc0 <ringBuffer+0x4afb8>
  b8:	44048403 	strmi	r8, [r4], #-1027	; 0xfffffbfd
  bc:	44080b0c 	strmi	r0, [r8], #-2828	; 0xfffff4f4
  c0:	06028905 	streq	r8, [r2], -r5, lsl #18
  c4:	08028805 	stmdaeq	r2, {r0, r2, fp, pc}
  c8:	00000020 	andeq	r0, r0, r0, lsr #32
  cc:	00000000 	andeq	r0, r0, r0
  d0:	000401d0 	ldrdeq	r0, [r4], -r0	; <UNPREDICTABLE>
  d4:	0000013c 	andeq	r0, r0, ip, lsr r1
  d8:	8e100e44 	cdphi	14, 1, cr0, cr0, cr4, {2}
  dc:	8a028b01 	bhi	a2ce8 <ringBuffer+0x4afe0>
  e0:	44048403 	strmi	r8, [r4], #-1027	; 0xfffffbfd
  e4:	44080b0c 	strmi	r0, [r8], #-2828	; 0xfffff4f4
  e8:	06028805 	streq	r8, [r2], -r5, lsl #16
  ec:	00000024 	andeq	r0, r0, r4, lsr #32
  f0:	00000000 	andeq	r0, r0, r0
  f4:	0004030c 	andeq	r0, r4, ip, lsl #6
  f8:	00000074 	andeq	r0, r0, r4, ror r0
  fc:	8e200e44 	cdphi	14, 2, cr0, cr0, cr4, {2}
 100:	8a028b01 	bhi	a2d0c <ringBuffer+0x4b004>
 104:	87048903 	strhi	r8, [r4, -r3, lsl #18]
 108:	85068605 	strhi	r8, [r6, #-1541]	; 0xfffff9fb
 10c:	44088407 	strmi	r8, [r8], #-1031	; 0xfffffbf9
 110:	00080b0c 	andeq	r0, r8, ip, lsl #22
 114:	00000020 	andeq	r0, r0, r0, lsr #32
 118:	00000000 	andeq	r0, r0, r0
 11c:	00040380 	andeq	r0, r4, r0, lsl #7
 120:	00000128 	andeq	r0, r0, r8, lsr #2
 124:	8e180e44 	cdphi	14, 1, cr0, cr8, cr4, {2}
 128:	87028b01 	strhi	r8, [r2, -r1, lsl #22]
 12c:	85048603 	strhi	r8, [r4, #-1539]	; 0xfffff9fd
 130:	44068405 	strmi	r8, [r6], #-1029	; 0xfffffbfb
 134:	00080b0c 	andeq	r0, r8, ip, lsl #22
 138:	00000010 	andeq	r0, r0, r0, lsl r0
 13c:	00000000 	andeq	r0, r0, r0
 140:	000404a8 	andeq	r0, r4, r8, lsr #9
 144:	00000080 	andeq	r0, r0, r0, lsl #1
 148:	000c0e44 	andeq	r0, ip, r4, asr #28
 14c:	00000024 	andeq	r0, r0, r4, lsr #32
 150:	00000000 	andeq	r0, r0, r0
 154:	00040528 	andeq	r0, r4, r8, lsr #10
 158:	000001f8 	strdeq	r0, [r0], -r8
 15c:	8e180e44 	cdphi	14, 1, cr0, cr8, cr4, {2}
 160:	8a028b01 	bhi	a2d6c <ringBuffer+0x4b064>
 164:	85048603 	strhi	r8, [r4, #-1539]	; 0xfffff9fd
 168:	44068405 	strmi	r8, [r6], #-1029	; 0xfffffbfb
 16c:	44080b0c 	strmi	r0, [r8], #-2828	; 0xfffff4f4
 170:	08028805 	stmdaeq	r2, {r0, r2, fp, pc}
 174:	00000018 	andeq	r0, r0, r8, lsl r0
 178:	00000000 	andeq	r0, r0, r0
 17c:	00040720 	andeq	r0, r4, r0, lsr #14
 180:	00000028 	andeq	r0, r0, r8, lsr #32
 184:	8e080e44 	cdphi	14, 0, cr0, cr8, cr4, {2}
 188:	44028b01 	strmi	r8, [r2], #-2817	; 0xfffff4ff
 18c:	00000b0d 	andeq	r0, r0, sp, lsl #22
 190:	00000018 	andeq	r0, r0, r8, lsl r0
 194:	00000000 	andeq	r0, r0, r0
 198:	00040748 	andeq	r0, r4, r8, asr #14
 19c:	000000c8 	andeq	r0, r0, r8, asr #1
 1a0:	8e080e44 	cdphi	14, 0, cr0, cr8, cr4, {2}
 1a4:	44028b01 	strmi	r8, [r2], #-2817	; 0xfffff4ff
 1a8:	00000b0d 	andeq	r0, r0, sp, lsl #22
 1ac:	00000018 	andeq	r0, r0, r8, lsl r0
 1b0:	00000000 	andeq	r0, r0, r0
 1b4:	00040810 	andeq	r0, r4, r0, lsl r8
 1b8:	0000003c 	andeq	r0, r0, ip, lsr r0
 1bc:	8e080e44 	cdphi	14, 0, cr0, cr8, cr4, {2}
 1c0:	44028b01 	strmi	r8, [r2], #-2817	; 0xfffff4ff
 1c4:	00000b0d 	andeq	r0, r0, sp, lsl #22
 1c8:	00000018 	andeq	r0, r0, r8, lsl r0
 1cc:	00000000 	andeq	r0, r0, r0
 1d0:	0004084c 	andeq	r0, r4, ip, asr #16
 1d4:	00000044 	andeq	r0, r0, r4, asr #32
 1d8:	8e080e44 	cdphi	14, 0, cr0, cr8, cr4, {2}
 1dc:	44028b01 	strmi	r8, [r2], #-2817	; 0xfffff4ff
 1e0:	00000b0d 	andeq	r0, r0, sp, lsl #22
 1e4:	00000018 	andeq	r0, r0, r8, lsl r0
 1e8:	00000000 	andeq	r0, r0, r0
 1ec:	00020564 	andeq	r0, r2, r4, ror #10
 1f0:	00000024 	andeq	r0, r0, r4, lsr #32
 1f4:	8e080e44 	cdphi	14, 0, cr0, cr8, cr4, {2}
 1f8:	44028b01 	strmi	r8, [r2], #-2817	; 0xfffff4ff
 1fc:	00000b0d 	andeq	r0, r0, sp, lsl #22
 200:	00000018 	andeq	r0, r0, r8, lsl r0
 204:	00000000 	andeq	r0, r0, r0
 208:	00040890 	muleq	r4, r0, r8
 20c:	00000030 	andeq	r0, r0, r0, lsr r0
 210:	8e080e44 	cdphi	14, 0, cr0, cr8, cr4, {2}
 214:	44028b01 	strmi	r8, [r2], #-2817	; 0xfffff4ff
 218:	00000b0d 	andeq	r0, r0, sp, lsl #22
 21c:	00000018 	andeq	r0, r0, r8, lsl r0
 220:	00000000 	andeq	r0, r0, r0
 224:	000408c0 	andeq	r0, r4, r0, asr #17
 228:	00000050 	andeq	r0, r0, r0, asr r0
 22c:	8e080e44 	cdphi	14, 0, cr0, cr8, cr4, {2}
 230:	44028b01 	strmi	r8, [r2], #-2817	; 0xfffff4ff
 234:	00000b0d 	andeq	r0, r0, sp, lsl #22
 238:	00000018 	andeq	r0, r0, r8, lsl r0
 23c:	00000000 	andeq	r0, r0, r0
 240:	00040910 	andeq	r0, r4, r0, lsl r9
 244:	00000020 	andeq	r0, r0, r0, lsr #32
 248:	8e080e44 	cdphi	14, 0, cr0, cr8, cr4, {2}
 24c:	44028b01 	strmi	r8, [r2], #-2817	; 0xfffff4ff
 250:	00000b0d 	andeq	r0, r0, sp, lsl #22
 254:	00000018 	andeq	r0, r0, r8, lsl r0
 258:	00000000 	andeq	r0, r0, r0
 25c:	00020588 	andeq	r0, r2, r8, lsl #11
 260:	00000048 	andeq	r0, r0, r8, asr #32
 264:	8e080e44 	cdphi	14, 0, cr0, cr8, cr4, {2}
 268:	44028b01 	strmi	r8, [r2], #-2817	; 0xfffff4ff
 26c:	00000b0d 	andeq	r0, r0, sp, lsl #22
 270:	00000018 	andeq	r0, r0, r8, lsl r0
 274:	00000000 	andeq	r0, r0, r0
 278:	00040930 	andeq	r0, r4, r0, lsr r9
 27c:	0000003c 	andeq	r0, r0, ip, lsr r0
 280:	8e080e44 	cdphi	14, 0, cr0, cr8, cr4, {2}
 284:	44028b01 	strmi	r8, [r2], #-2817	; 0xfffff4ff
 288:	00000b0d 	andeq	r0, r0, sp, lsl #22
 28c:	00000018 	andeq	r0, r0, r8, lsl r0
 290:	00000000 	andeq	r0, r0, r0
 294:	0004096c 	andeq	r0, r4, ip, ror #18
 298:	00000040 	andeq	r0, r0, r0, asr #32
 29c:	8e080e44 	cdphi	14, 0, cr0, cr8, cr4, {2}
 2a0:	44028b01 	strmi	r8, [r2], #-2817	; 0xfffff4ff
 2a4:	00000b0d 	andeq	r0, r0, sp, lsl #22
 2a8:	00000018 	andeq	r0, r0, r8, lsl r0
 2ac:	00000000 	andeq	r0, r0, r0
 2b0:	000409ac 	andeq	r0, r4, ip, lsr #19
 2b4:	00000030 	andeq	r0, r0, r0, lsr r0
 2b8:	8e080e44 	cdphi	14, 0, cr0, cr8, cr4, {2}
 2bc:	44028b01 	strmi	r8, [r2], #-2817	; 0xfffff4ff
 2c0:	00000b0d 	andeq	r0, r0, sp, lsl #22
 2c4:	00000018 	andeq	r0, r0, r8, lsl r0
 2c8:	00000000 	andeq	r0, r0, r0
 2cc:	000205d0 	ldrdeq	r0, [r2], -r0	; <UNPREDICTABLE>
 2d0:	0000002c 	andeq	r0, r0, ip, lsr #32
 2d4:	8e080e44 	cdphi	14, 0, cr0, cr8, cr4, {2}
 2d8:	44028b01 	strmi	r8, [r2], #-2817	; 0xfffff4ff
 2dc:	00000b0d 	andeq	r0, r0, sp, lsl #22
 2e0:	00000018 	andeq	r0, r0, r8, lsl r0
 2e4:	00000000 	andeq	r0, r0, r0
 2e8:	000205fc 	strdeq	r0, [r2], -ip
 2ec:	00000030 	andeq	r0, r0, r0, lsr r0
 2f0:	8e080e44 	cdphi	14, 0, cr0, cr8, cr4, {2}
 2f4:	44028b01 	strmi	r8, [r2], #-2817	; 0xfffff4ff
 2f8:	00000b0d 	andeq	r0, r0, sp, lsl #22
 2fc:	00000020 	andeq	r0, r0, r0, lsr #32
 300:	00000000 	andeq	r0, r0, r0
 304:	0002062c 	andeq	r0, r2, ip, lsr #12
 308:	00000044 	andeq	r0, r0, r4, asr #32
 30c:	8e180e44 	cdphi	14, 1, cr0, cr8, cr4, {2}
 310:	87028b01 	strhi	r8, [r2, -r1, lsl #22]
 314:	85048603 	strhi	r8, [r4, #-1539]	; 0xfffff9fd
 318:	44068405 	strmi	r8, [r6], #-1029	; 0xfffffbfb
 31c:	00080b0c 	andeq	r0, r8, ip, lsl #22
 320:	00000018 	andeq	r0, r0, r8, lsl r0
 324:	00000000 	andeq	r0, r0, r0
 328:	00020670 	andeq	r0, r2, r0, ror r6
 32c:	00000028 	andeq	r0, r0, r8, lsr #32
 330:	8e080e44 	cdphi	14, 0, cr0, cr8, cr4, {2}
 334:	44028b01 	strmi	r8, [r2], #-2817	; 0xfffff4ff
 338:	00000b0d 	andeq	r0, r0, sp, lsl #22
 33c:	00000020 	andeq	r0, r0, r0, lsr #32
 340:	00000000 	andeq	r0, r0, r0
 344:	000409dc 	ldrdeq	r0, [r4], -ip
 348:	00000058 	andeq	r0, r0, r8, asr r0
 34c:	8e180e44 	cdphi	14, 1, cr0, cr8, cr4, {2}
 350:	8a028b01 	bhi	a2f5c <ringBuffer+0x4b254>
 354:	85048603 	strhi	r8, [r4, #-1539]	; 0xfffff9fd
 358:	44068405 	strmi	r8, [r6], #-1029	; 0xfffffbfb
 35c:	00080b0c 	andeq	r0, r8, ip, lsl #22
 360:	00000018 	andeq	r0, r0, r8, lsl r0
 364:	00000000 	andeq	r0, r0, r0
 368:	00020698 	muleq	r2, r8, r6
 36c:	00000038 	andeq	r0, r0, r8, lsr r0
 370:	8e080e44 	cdphi	14, 0, cr0, cr8, cr4, {2}
 374:	44028b01 	strmi	r8, [r2], #-2817	; 0xfffff4ff
 378:	00000b0d 	andeq	r0, r0, sp, lsl #22
 37c:	00000018 	andeq	r0, r0, r8, lsl r0
 380:	00000000 	andeq	r0, r0, r0
 384:	000206d0 	ldrdeq	r0, [r2], -r0	; <UNPREDICTABLE>
 388:	00000050 	andeq	r0, r0, r0, asr r0
 38c:	8e080e44 	cdphi	14, 0, cr0, cr8, cr4, {2}
 390:	44028b01 	strmi	r8, [r2], #-2817	; 0xfffff4ff
 394:	00000b0d 	andeq	r0, r0, sp, lsl #22
 398:	00000018 	andeq	r0, r0, r8, lsl r0
 39c:	00000000 	andeq	r0, r0, r0
 3a0:	00020720 	andeq	r0, r2, r0, lsr #14
 3a4:	0000004c 	andeq	r0, r0, ip, asr #32
 3a8:	8e080e44 	cdphi	14, 0, cr0, cr8, cr4, {2}
 3ac:	44028b01 	strmi	r8, [r2], #-2817	; 0xfffff4ff
 3b0:	00000b0d 	andeq	r0, r0, sp, lsl #22
 3b4:	0000000c 	andeq	r0, r0, ip
 3b8:	ffffffff 			; <UNDEFINED> instruction: 0xffffffff
 3bc:	7c020001 	stcvc	0, cr0, [r2], {1}
 3c0:	000d0c0e 	andeq	r0, sp, lr, lsl #24
 3c4:	00000024 	andeq	r0, r0, r4, lsr #32
 3c8:	000003b4 			; <UNDEFINED> instruction: 0x000003b4
 3cc:	00040adc 	ldrdeq	r0, [r4], -ip
 3d0:	0000003c 	andeq	r0, r0, ip, lsr r0
 3d4:	87040e41 	strhi	r0, [r4, -r1, asr #28]
 3d8:	180e4101 	stmdane	lr, {r0, r8, lr}
 3dc:	57070d41 	strpl	r0, [r7, -r1, asr #26]
 3e0:	0d41040e 	cfstrdeq	mvd0, [r1, #-56]	; 0xffffffc8
 3e4:	0ec7420d 	cdpeq	2, 12, cr4, cr7, cr13, {0}
 3e8:	00000000 	andeq	r0, r0, r0
 3ec:	00000024 	andeq	r0, r0, r4, lsr #32
 3f0:	000003b4 			; <UNDEFINED> instruction: 0x000003b4
 3f4:	00040b18 	andeq	r0, r4, r8, lsl fp
 3f8:	0000003a 	andeq	r0, r0, sl, lsr r0
 3fc:	87040e41 	strhi	r0, [r4, -r1, asr #28]
 400:	180e4101 	stmdane	lr, {r0, r8, lr}
 404:	56070d41 	strpl	r0, [r7], -r1, asr #26
 408:	0d41040e 	cfstrdeq	mvd0, [r1, #-56]	; 0xffffffc8
 40c:	0ec7420d 	cdpeq	2, 12, cr4, cr7, cr13, {0}
 410:	00000000 	andeq	r0, r0, r0
 414:	00000024 	andeq	r0, r0, r4, lsr #32
 418:	000003b4 			; <UNDEFINED> instruction: 0x000003b4
 41c:	00040b52 	andeq	r0, r4, r2, asr fp
 420:	00000046 	andeq	r0, r0, r6, asr #32
 424:	87040e41 	strhi	r0, [r4, -r1, asr #28]
 428:	180e4101 	stmdane	lr, {r0, r8, lr}
 42c:	5c070d41 	stcpl	13, cr0, [r7], {65}	; 0x41
 430:	0d41040e 	cfstrdeq	mvd0, [r1, #-56]	; 0xffffffc8
 434:	0ec7420d 	cdpeq	2, 12, cr4, cr7, cr13, {0}
 438:	00000000 	andeq	r0, r0, r0
 43c:	00000024 	andeq	r0, r0, r4, lsr #32
 440:	000003b4 			; <UNDEFINED> instruction: 0x000003b4
 444:	00040b98 	muleq	r4, r8, fp
 448:	0000001e 	andeq	r0, r0, lr, lsl r0
 44c:	87040e41 	strhi	r0, [r4, -r1, asr #28]
 450:	100e4101 	andne	r4, lr, r1, lsl #2
 454:	48070d41 	stmdami	r7, {r0, r6, r8, sl, fp}
 458:	0d41040e 	cfstrdeq	mvd0, [r1, #-56]	; 0xffffffc8
 45c:	0ec7420d 	cdpeq	2, 12, cr4, cr7, cr13, {0}
 460:	00000000 	andeq	r0, r0, r0
 464:	00000020 	andeq	r0, r0, r0, lsr #32
 468:	000003b4 			; <UNDEFINED> instruction: 0x000003b4
 46c:	00040bb6 			; <UNDEFINED> instruction: 0x00040bb6
 470:	00000026 	andeq	r0, r0, r6, lsr #32
 474:	87080e41 	strhi	r0, [r8, -r1, asr #28]
 478:	41018e02 	tstmi	r1, r2, lsl #28
 47c:	0d41100e 	stcleq	0, cr1, [r1, #-56]	; 0xffffffc8
 480:	080e4b07 	stmdaeq	lr, {r0, r1, r2, r8, r9, fp, lr}
 484:	000d0d41 	andeq	r0, sp, r1, asr #26
 488:	00000024 	andeq	r0, r0, r4, lsr #32
 48c:	000003b4 			; <UNDEFINED> instruction: 0x000003b4
 490:	00040bdc 	ldrdeq	r0, [r4], -ip
 494:	0000001c 	andeq	r0, r0, ip, lsl r0
 498:	87040e41 	strhi	r0, [r4, -r1, asr #28]
 49c:	100e4101 	andne	r4, lr, r1, lsl #2
 4a0:	47070d41 	strmi	r0, [r7, -r1, asr #26]
 4a4:	0d41040e 	cfstrdeq	mvd0, [r1, #-56]	; 0xffffffc8
 4a8:	0ec7420d 	cdpeq	2, 12, cr4, cr7, cr13, {0}
 4ac:	00000000 	andeq	r0, r0, r0
 4b0:	00000024 	andeq	r0, r0, r4, lsr #32
 4b4:	000003b4 			; <UNDEFINED> instruction: 0x000003b4
 4b8:	00040bf8 	strdeq	r0, [r4], -r8
 4bc:	00000022 	andeq	r0, r0, r2, lsr #32
 4c0:	87040e41 	strhi	r0, [r4, -r1, asr #28]
 4c4:	100e4101 	andne	r4, lr, r1, lsl #2
 4c8:	4a070d41 	bmi	1c39d4 <ringBuffer+0x16bccc>
 4cc:	0d41040e 	cfstrdeq	mvd0, [r1, #-56]	; 0xffffffc8
 4d0:	0ec7420d 	cdpeq	2, 12, cr4, cr7, cr13, {0}
 4d4:	00000000 	andeq	r0, r0, r0
 4d8:	00000020 	andeq	r0, r0, r0, lsr #32
 4dc:	000003b4 			; <UNDEFINED> instruction: 0x000003b4
 4e0:	00040c1a 	andeq	r0, r4, sl, lsl ip
 4e4:	00000028 	andeq	r0, r0, r8, lsr #32
 4e8:	87080e41 	strhi	r0, [r8, -r1, asr #28]
 4ec:	41018e02 	tstmi	r1, r2, lsl #28
 4f0:	0d41100e 	stcleq	0, cr1, [r1, #-56]	; 0xffffffc8
 4f4:	080e4f07 	stmdaeq	lr, {r0, r1, r2, r8, r9, sl, fp, lr}
 4f8:	000d0d41 	andeq	r0, sp, r1, asr #26
 4fc:	00000024 	andeq	r0, r0, r4, lsr #32
 500:	000003b4 			; <UNDEFINED> instruction: 0x000003b4
 504:	00040c42 	andeq	r0, r4, r2, asr #24
 508:	0000003c 	andeq	r0, r0, ip, lsr r0
 50c:	87040e41 	strhi	r0, [r4, -r1, asr #28]
 510:	100e4101 	andne	r4, lr, r1, lsl #2
 514:	57070d41 	strpl	r0, [r7, -r1, asr #26]
 518:	0d41040e 	cfstrdeq	mvd0, [r1, #-56]	; 0xffffffc8
 51c:	0ec7420d 	cdpeq	2, 12, cr4, cr7, cr13, {0}
 520:	00000000 	andeq	r0, r0, r0
 524:	00000020 	andeq	r0, r0, r0, lsr #32
 528:	000003b4 			; <UNDEFINED> instruction: 0x000003b4
 52c:	00040c7e 	andeq	r0, r4, lr, ror ip
 530:	00000046 	andeq	r0, r0, r6, asr #32
 534:	87080e41 	strhi	r0, [r8, -r1, asr #28]
 538:	41018e02 	tstmi	r1, r2, lsl #28
 53c:	0d41180e 	stcleq	8, cr1, [r1, #-56]	; 0xffffffc8
 540:	080e5b07 	stmdaeq	lr, {r0, r1, r2, r8, r9, fp, ip, lr}
 544:	000d0d41 	andeq	r0, sp, r1, asr #26
 548:	00000020 	andeq	r0, r0, r0, lsr #32
 54c:	000003b4 			; <UNDEFINED> instruction: 0x000003b4
 550:	00040cc4 	andeq	r0, r4, r4, asr #25
 554:	0000005c 	andeq	r0, r0, ip, asr r0
 558:	87080e41 	strhi	r0, [r8, -r1, asr #28]
 55c:	41018e02 	tstmi	r1, r2, lsl #28
 560:	0d41180e 	stcleq	8, cr1, [r1, #-56]	; 0xffffffc8
 564:	080e6907 	stmdaeq	lr, {r0, r1, r2, r8, fp, sp, lr}
 568:	000d0d41 	andeq	r0, sp, r1, asr #26
 56c:	00000020 	andeq	r0, r0, r0, lsr #32
 570:	000003b4 			; <UNDEFINED> instruction: 0x000003b4
 574:	00040d20 	andeq	r0, r4, r0, lsr #26
 578:	00000096 	muleq	r0, r6, r0
 57c:	87080e41 	strhi	r0, [r8, -r1, asr #28]
 580:	41018e02 	tstmi	r1, r2, lsl #28
 584:	0d41300e 	stcleq	0, cr3, [r1, #-56]	; 0xffffffc8
 588:	0e460207 	cdpeq	2, 4, cr0, cr6, cr7, {0}
 58c:	0d0d4108 	stfeqs	f4, [sp, #-32]	; 0xffffffe0
 590:	00000020 	andeq	r0, r0, r0, lsr #32
 594:	000003b4 			; <UNDEFINED> instruction: 0x000003b4
 598:	00040db6 			; <UNDEFINED> instruction: 0x00040db6
 59c:	00000102 	andeq	r0, r0, r2, lsl #2
 5a0:	87080e41 	strhi	r0, [r8, -r1, asr #28]
 5a4:	41018e02 	tstmi	r1, r2, lsl #28
 5a8:	0d41780e 	stcleq	8, cr7, [r1, #-56]	; 0xffffffc8
 5ac:	0e7c0207 	cdpeq	2, 7, cr0, cr12, cr7, {0}
 5b0:	0d0d4108 	stfeqs	f4, [sp, #-32]	; 0xffffffe0
 5b4:	00000024 	andeq	r0, r0, r4, lsr #32
 5b8:	000003b4 			; <UNDEFINED> instruction: 0x000003b4
 5bc:	00040eb8 			; <UNDEFINED> instruction: 0x00040eb8
 5c0:	00002bc0 	andeq	r2, r0, r0, asr #23
 5c4:	87080e41 	strhi	r0, [r8, -r1, asr #28]
 5c8:	41018e02 	tstmi	r1, r2, lsl #28
 5cc:	4101980e 	tstmi	r1, lr, lsl #16
 5d0:	db03070d 	blle	c220c <ringBuffer+0x6a504>
 5d4:	41080e15 	tstmi	r8, r5, lsl lr
 5d8:	00000d0d 	andeq	r0, r0, sp, lsl #26
 5dc:	00000020 	andeq	r0, r0, r0, lsr #32
 5e0:	000003b4 			; <UNDEFINED> instruction: 0x000003b4
 5e4:	00043a78 	andeq	r3, r4, r8, ror sl
 5e8:	000000ba 	strheq	r0, [r0], -sl
 5ec:	87080e41 	strhi	r0, [r8, -r1, asr #28]
 5f0:	41018e02 	tstmi	r1, r2, lsl #28
 5f4:	0d41280e 	stcleq	8, cr2, [r1, #-56]	; 0xffffffc8
 5f8:	0e580207 	cdpeq	2, 5, cr0, cr8, cr7, {0}
 5fc:	0d0d4108 	stfeqs	f4, [sp, #-32]	; 0xffffffe0
 600:	00000020 	andeq	r0, r0, r0, lsr #32
 604:	000003b4 			; <UNDEFINED> instruction: 0x000003b4
 608:	00043b32 	andeq	r3, r4, r2, lsr fp
 60c:	000000ca 	andeq	r0, r0, sl, asr #1
 610:	87080e41 	strhi	r0, [r8, -r1, asr #28]
 614:	41018e02 	tstmi	r1, r2, lsl #28
 618:	0d41400e 	stcleq	0, cr4, [r1, #-56]	; 0xffffffc8
 61c:	0e600207 	cdpeq	2, 6, cr0, cr0, cr7, {0}
 620:	0d0d4108 	stfeqs	f4, [sp, #-32]	; 0xffffffe0
 624:	00000024 	andeq	r0, r0, r4, lsr #32
 628:	000003b4 			; <UNDEFINED> instruction: 0x000003b4
 62c:	00043bfc 	strdeq	r3, [r4], -ip
 630:	000000c6 	andeq	r0, r0, r6, asr #1
 634:	87080e41 	strhi	r0, [r8, -r1, asr #28]
 638:	41018e02 	tstmi	r1, r2, lsl #28
 63c:	4101980e 	tstmi	r1, lr, lsl #16
 640:	5e02070d 	cdppl	7, 0, cr0, cr2, cr13, {0}
 644:	0d41080e 	stcleq	8, cr0, [r1, #-56]	; 0xffffffc8
 648:	0000000d 	andeq	r0, r0, sp
 64c:	0000000c 	andeq	r0, r0, ip
 650:	ffffffff 			; <UNDEFINED> instruction: 0xffffffff
 654:	7c020001 	stcvc	0, cr0, [r2], {1}
 658:	000d0c0e 	andeq	r0, sp, lr, lsl #24
 65c:	0000002c 	andeq	r0, r0, ip, lsr #32
 660:	0000064c 	andeq	r0, r0, ip, asr #12
 664:	00043cc4 	andeq	r3, r4, r4, asr #25
 668:	000000c2 	andeq	r0, r0, r2, asr #1
 66c:	41100e41 	tstmi	r0, r1, asr #28
 670:	0684180e 	streq	r1, [r4], lr, lsl #16
 674:	0e410587 	cdpeq	5, 4, cr0, cr1, cr7, {4}
 678:	070d4138 	smladxeq	sp, r8, r1, r4
 67c:	180e5902 	stmdane	lr, {r1, r8, fp, ip, lr}
 680:	410d0d41 	tstmi	sp, r1, asr #26
 684:	100ec4c7 	andne	ip, lr, r7, asr #9
 688:	00000e41 	andeq	r0, r0, r1, asr #28
 68c:	00000028 	andeq	r0, r0, r8, lsr #32
 690:	0000064c 	andeq	r0, r0, ip, asr #12
 694:	00043d86 	andeq	r3, r4, r6, lsl #27
 698:	000000ce 	andeq	r0, r0, lr, asr #1
 69c:	84080e41 	strhi	r0, [r8], #-3649	; 0xfffff1bf
 6a0:	41018702 	tstmi	r1, r2, lsl #14
 6a4:	0d41300e 	stcleq	0, cr3, [r1, #-56]	; 0xffffffc8
 6a8:	0e610207 	cdpeq	2, 6, cr0, cr1, cr7, {0}
 6ac:	0d0d4108 	stfeqs	f4, [sp, #-32]	; 0xffffffe0
 6b0:	0ec4c741 	cdpeq	7, 12, cr12, cr4, cr1, {2}
 6b4:	00000000 	andeq	r0, r0, r0
 6b8:	00000024 	andeq	r0, r0, r4, lsr #32
 6bc:	0000064c 	andeq	r0, r0, ip, asr #12
 6c0:	00043e54 	andeq	r3, r4, r4, asr lr
 6c4:	00000052 	andeq	r0, r0, r2, asr r0
 6c8:	87040e41 	strhi	r0, [r4, -r1, asr #28]
 6cc:	180e4101 	stmdane	lr, {r0, r8, lr}
 6d0:	62070d41 	andvs	r0, r7, #4160	; 0x1040
 6d4:	0d41040e 	cfstrdeq	mvd0, [r1, #-56]	; 0xffffffc8
 6d8:	0ec7420d 	cdpeq	2, 12, cr4, cr7, cr13, {0}
 6dc:	00000000 	andeq	r0, r0, r0
 6e0:	00000024 	andeq	r0, r0, r4, lsr #32
 6e4:	0000064c 	andeq	r0, r0, ip, asr #12
 6e8:	00043ea6 	andeq	r3, r4, r6, lsr #29
 6ec:	00000046 	andeq	r0, r0, r6, asr #32
 6f0:	87040e41 	strhi	r0, [r4, -r1, asr #28]
 6f4:	200e4101 	andcs	r4, lr, r1, lsl #2
 6f8:	5c070d41 	stcpl	13, cr0, [r7], {65}	; 0x41
 6fc:	0d41040e 	cfstrdeq	mvd0, [r1, #-56]	; 0xffffffc8
 700:	0ec7420d 	cdpeq	2, 12, cr4, cr7, cr13, {0}
 704:	00000000 	andeq	r0, r0, r0
 708:	00000024 	andeq	r0, r0, r4, lsr #32
 70c:	0000064c 	andeq	r0, r0, ip, asr #12
 710:	00043eec 	andeq	r3, r4, ip, ror #29
 714:	00000018 	andeq	r0, r0, r8, lsl r0
 718:	87040e41 	strhi	r0, [r4, -r1, asr #28]
 71c:	100e4101 	andne	r4, lr, r1, lsl #2
 720:	45070d41 	strmi	r0, [r7, #-3393]	; 0xfffff2bf
 724:	0d41040e 	cfstrdeq	mvd0, [r1, #-56]	; 0xffffffc8
 728:	0ec7420d 	cdpeq	2, 12, cr4, cr7, cr13, {0}
 72c:	00000000 	andeq	r0, r0, r0
 730:	00000024 	andeq	r0, r0, r4, lsr #32
 734:	0000064c 	andeq	r0, r0, ip, asr #12
 738:	00043f04 	andeq	r3, r4, r4, lsl #30
 73c:	000000a0 	andeq	r0, r0, r0, lsr #1
 740:	840c0e41 	strhi	r0, [ip], #-3649	; 0xfffff1bf
 744:	8e028703 	cdphi	7, 0, cr8, cr2, cr3, {0}
 748:	380e4101 	stmdacc	lr, {r0, r8, lr}
 74c:	30070c41 	andcc	r0, r7, r1, asr #24
 750:	0c0e4002 	stceq	0, cr4, [lr], {2}
 754:	000d0d41 	andeq	r0, sp, r1, asr #26
 758:	00000024 	andeq	r0, r0, r4, lsr #32
 75c:	0000064c 	andeq	r0, r0, ip, asr #12
 760:	00043fa4 	andeq	r3, r4, r4, lsr #31
 764:	000001c0 	andeq	r0, r0, r0, asr #3
 768:	87040e41 	strhi	r0, [r4, -r1, asr #28]
 76c:	180e4101 	stmdane	lr, {r0, r8, lr}
 770:	02070d41 	andeq	r0, r7, #4160	; 0x1040
 774:	41040ed9 	ldrdmi	r0, [r4, -r9]
 778:	c7420d0d 	strbgt	r0, [r2, -sp, lsl #26]
 77c:	0000000e 	andeq	r0, r0, lr
 780:	00000024 	andeq	r0, r0, r4, lsr #32
 784:	0000064c 	andeq	r0, r0, ip, asr #12
 788:	00044164 	andeq	r4, r4, r4, ror #2
 78c:	0000011c 	andeq	r0, r0, ip, lsl r1
 790:	840c0e41 	strhi	r0, [ip], #-3649	; 0xfffff1bf
 794:	8e028703 	cdphi	7, 0, cr8, cr2, cr3, {0}
 798:	500e4101 	andpl	r4, lr, r1, lsl #2
 79c:	48070c41 	stmdami	r7, {r0, r6, sl, fp}
 7a0:	0c0e7c02 	stceq	12, cr7, [lr], {2}
 7a4:	000d0d41 	andeq	r0, sp, r1, asr #26
 7a8:	00000024 	andeq	r0, r0, r4, lsr #32
 7ac:	0000064c 	andeq	r0, r0, ip, asr #12
 7b0:	00044280 	andeq	r4, r4, r0, lsl #5
 7b4:	00000124 	andeq	r0, r0, r4, lsr #2
 7b8:	840c0e41 	strhi	r0, [ip], #-3649	; 0xfffff1bf
 7bc:	8e028703 	cdphi	7, 0, cr8, cr2, cr3, {0}
 7c0:	500e4101 	andpl	r4, lr, r1, lsl #2
 7c4:	48070c41 	stmdami	r7, {r0, r6, sl, fp}
 7c8:	0c0e8102 	stfeqd	f0, [lr], {2}
 7cc:	000d0d41 	andeq	r0, sp, r1, asr #26
 7d0:	00000024 	andeq	r0, r0, r4, lsr #32
 7d4:	0000064c 	andeq	r0, r0, ip, asr #12
 7d8:	000443a4 	andeq	r4, r4, r4, lsr #7
 7dc:	000000ac 	andeq	r0, r0, ip, lsr #1
 7e0:	840c0e41 	strhi	r0, [ip], #-3649	; 0xfffff1bf
 7e4:	8e028703 	cdphi	7, 0, cr8, cr2, cr3, {0}
 7e8:	380e4101 	stmdacc	lr, {r0, r8, lr}
 7ec:	30070c41 	andcc	r0, r7, r1, asr #24
 7f0:	0c0e4702 	stceq	7, cr4, [lr], {2}
 7f4:	000d0d41 	andeq	r0, sp, r1, asr #26
 7f8:	00000024 	andeq	r0, r0, r4, lsr #32
 7fc:	0000064c 	andeq	r0, r0, ip, asr #12
 800:	00044450 	andeq	r4, r4, r0, asr r4
 804:	000000dc 	ldrdeq	r0, [r0], -ip
 808:	840c0e41 	strhi	r0, [ip], #-3649	; 0xfffff1bf
 80c:	8e028703 	cdphi	7, 0, cr8, cr2, cr3, {0}
 810:	380e4101 	stmdacc	lr, {r0, r8, lr}
 814:	30070c41 	andcc	r0, r7, r1, asr #24
 818:	0c0e5d02 	stceq	13, cr5, [lr], {2}
 81c:	000d0d41 	andeq	r0, sp, r1, asr #26
 820:	00000024 	andeq	r0, r0, r4, lsr #32
 824:	0000064c 	andeq	r0, r0, ip, asr #12
 828:	0004452c 	andeq	r4, r4, ip, lsr #10
 82c:	0000011c 	andeq	r0, r0, ip, lsl r1
 830:	840c0e41 	strhi	r0, [ip], #-3649	; 0xfffff1bf
 834:	8e028703 	cdphi	7, 0, cr8, cr2, cr3, {0}
 838:	380e4101 	stmdacc	lr, {r0, r8, lr}
 83c:	30070c41 	andcc	r0, r7, r1, asr #24
 840:	0c0e7b02 			; <UNDEFINED> instruction: 0x0c0e7b02
 844:	000d0d41 	andeq	r0, sp, r1, asr #26
 848:	00000024 	andeq	r0, r0, r4, lsr #32
 84c:	0000064c 	andeq	r0, r0, ip, asr #12
 850:	00044648 	andeq	r4, r4, r8, asr #12
 854:	000000a4 	andeq	r0, r0, r4, lsr #1
 858:	840c0e41 	strhi	r0, [ip], #-3649	; 0xfffff1bf
 85c:	8e028703 	cdphi	7, 0, cr8, cr2, cr3, {0}
 860:	380e4101 	stmdacc	lr, {r0, r8, lr}
 864:	30070c41 	andcc	r0, r7, r1, asr #24
 868:	0c0e4202 	sfmeq	f4, 4, [lr], {2}
 86c:	000d0d41 	andeq	r0, sp, r1, asr #26
 870:	00000024 	andeq	r0, r0, r4, lsr #32
 874:	0000064c 	andeq	r0, r0, ip, asr #12
 878:	000446ec 	andeq	r4, r4, ip, ror #13
 87c:	00000120 	andeq	r0, r0, r0, lsr #2
 880:	840c0e41 	strhi	r0, [ip], #-3649	; 0xfffff1bf
 884:	8e028703 	cdphi	7, 0, cr8, cr2, cr3, {0}
 888:	400e4101 	andmi	r4, lr, r1, lsl #2
 88c:	38070c41 	stmdacc	r7, {r0, r6, sl, fp}
 890:	0c0e7e02 	stceq	14, cr7, [lr], {2}
 894:	000d0d41 	andeq	r0, sp, r1, asr #26
 898:	00000024 	andeq	r0, r0, r4, lsr #32
 89c:	0000064c 	andeq	r0, r0, ip, asr #12
 8a0:	0004480c 	andeq	r4, r4, ip, lsl #16
 8a4:	000000a0 	andeq	r0, r0, r0, lsr #1
 8a8:	840c0e41 	strhi	r0, [ip], #-3649	; 0xfffff1bf
 8ac:	8e028703 	cdphi	7, 0, cr8, cr2, cr3, {0}
 8b0:	400e4101 	andmi	r4, lr, r1, lsl #2
 8b4:	38070c41 	stmdacc	r7, {r0, r6, sl, fp}
 8b8:	0c0e4102 	stfeqs	f4, [lr], {2}
 8bc:	000d0d41 	andeq	r0, sp, r1, asr #26
 8c0:	00000024 	andeq	r0, r0, r4, lsr #32
 8c4:	0000064c 	andeq	r0, r0, ip, asr #12
 8c8:	000448ac 	andeq	r4, r4, ip, lsr #17
 8cc:	00000098 	muleq	r0, r8, r0
 8d0:	840c0e41 	strhi	r0, [ip], #-3649	; 0xfffff1bf
 8d4:	8e028703 	cdphi	7, 0, cr8, cr2, cr3, {0}
 8d8:	400e4101 	andmi	r4, lr, r1, lsl #2
 8dc:	38070c41 	stmdacc	r7, {r0, r6, sl, fp}
 8e0:	410c0e7c 	tstmi	ip, ip, ror lr
 8e4:	00000d0d 	andeq	r0, r0, sp, lsl #26
 8e8:	00000024 	andeq	r0, r0, r4, lsr #32
 8ec:	0000064c 	andeq	r0, r0, ip, asr #12
 8f0:	00044944 	andeq	r4, r4, r4, asr #18
 8f4:	00000016 	andeq	r0, r0, r6, lsl r0
 8f8:	87040e41 	strhi	r0, [r4, -r1, asr #28]
 8fc:	100e4101 	andne	r4, lr, r1, lsl #2
 900:	44070d41 	strmi	r0, [r7], #-3393	; 0xfffff2bf
 904:	0d41040e 	cfstrdeq	mvd0, [r1, #-56]	; 0xffffffc8
 908:	0ec7420d 	cdpeq	2, 12, cr4, cr7, cr13, {0}
 90c:	00000000 	andeq	r0, r0, r0
 910:	00000018 	andeq	r0, r0, r8, lsl r0
 914:	0000064c 	andeq	r0, r0, ip, asr #12
 918:	0004495a 	andeq	r4, r4, sl, asr r9
 91c:	00000016 	andeq	r0, r0, r6, lsl r0
 920:	87080e41 	strhi	r0, [r8, -r1, asr #28]
 924:	41018e02 	tstmi	r1, r2, lsl #28
 928:	0000070d 	andeq	r0, r0, sp, lsl #14
 92c:	00000018 	andeq	r0, r0, r8, lsl r0
 930:	0000064c 	andeq	r0, r0, ip, asr #12
 934:	00044970 	andeq	r4, r4, r0, ror r9
 938:	0000002c 	andeq	r0, r0, ip, lsr #32
 93c:	87080e41 	strhi	r0, [r8, -r1, asr #28]
 940:	41018e02 	tstmi	r1, r2, lsl #28
 944:	0000070d 	andeq	r0, r0, sp, lsl #14
 948:	0000000c 	andeq	r0, r0, ip
 94c:	ffffffff 			; <UNDEFINED> instruction: 0xffffffff
 950:	7c020001 	stcvc	0, cr0, [r2], {1}
 954:	000d0c0e 	andeq	r0, sp, lr, lsl #24
 958:	0000001c 	andeq	r0, r0, ip, lsl r0
 95c:	00000948 	andeq	r0, r0, r8, asr #18
 960:	0004499c 	muleq	r4, ip, r9
 964:	0000008c 	andeq	r0, r0, ip, lsl #1
 968:	83100e41 	tsthi	r0, #1040	; 0x410
 96c:	87038404 	strhi	r8, [r3, -r4, lsl #8]
 970:	41018e02 	tstmi	r1, r2, lsl #28
 974:	0000070d 	andeq	r0, r0, sp, lsl #14
 978:	00000024 	andeq	r0, r0, r4, lsr #32
 97c:	00000948 	andeq	r0, r0, r8, asr #18
 980:	00044a28 	andeq	r4, r4, r8, lsr #20
 984:	00000194 	muleq	r0, r4, r1
 988:	840c0e41 	strhi	r0, [ip], #-3649	; 0xfffff1bf
 98c:	8e028703 	cdphi	7, 0, cr8, cr2, cr3, {0}
 990:	300e4101 	andcc	r4, lr, r1, lsl #2
 994:	20070c41 	andcs	r0, r7, r1, asr #24
 998:	0c0eab02 			; <UNDEFINED> instruction: 0x0c0eab02
 99c:	000d0d41 	andeq	r0, sp, r1, asr #26
 9a0:	0000001c 	andeq	r0, r0, ip, lsl r0
 9a4:	00000948 	andeq	r0, r0, r8, asr #18
 9a8:	00044bbc 			; <UNDEFINED> instruction: 0x00044bbc
 9ac:	00000084 	andeq	r0, r0, r4, lsl #1
 9b0:	83100e41 	tsthi	r0, #1040	; 0x410
 9b4:	87038404 	strhi	r8, [r3, -r4, lsl #8]
 9b8:	41018e02 	tstmi	r1, r2, lsl #28
 9bc:	0000070d 	andeq	r0, r0, sp, lsl #14
 9c0:	00000024 	andeq	r0, r0, r4, lsr #32
 9c4:	00000948 	andeq	r0, r0, r8, asr #18
 9c8:	00044c40 	andeq	r4, r4, r0, asr #24
 9cc:	0000001a 	andeq	r0, r0, sl, lsl r0
 9d0:	87040e41 	strhi	r0, [r4, -r1, asr #28]
 9d4:	180e4101 	stmdane	lr, {r0, r8, lr}
 9d8:	46070d41 	strmi	r0, [r7], -r1, asr #26
 9dc:	0d41040e 	cfstrdeq	mvd0, [r1, #-56]	; 0xffffffc8
 9e0:	0ec7420d 	cdpeq	2, 12, cr4, cr7, cr13, {0}
 9e4:	00000000 	andeq	r0, r0, r0
 9e8:	00000024 	andeq	r0, r0, r4, lsr #32
 9ec:	00000948 	andeq	r0, r0, r8, asr #18
 9f0:	00044c5a 	andeq	r4, r4, sl, asr ip
 9f4:	00000016 	andeq	r0, r0, r6, lsl r0
 9f8:	87040e41 	strhi	r0, [r4, -r1, asr #28]
 9fc:	100e4101 	andne	r4, lr, r1, lsl #2
 a00:	44070d41 	strmi	r0, [r7], #-3393	; 0xfffff2bf
 a04:	0d41040e 	cfstrdeq	mvd0, [r1, #-56]	; 0xffffffc8
 a08:	0ec7420d 	cdpeq	2, 12, cr4, cr7, cr13, {0}
 a0c:	00000000 	andeq	r0, r0, r0
 a10:	00000024 	andeq	r0, r0, r4, lsr #32
 a14:	00000948 	andeq	r0, r0, r8, asr #18
 a18:	00044c70 	andeq	r4, r4, r0, ror ip
 a1c:	00000016 	andeq	r0, r0, r6, lsl r0
 a20:	87040e41 	strhi	r0, [r4, -r1, asr #28]
 a24:	100e4101 	andne	r4, lr, r1, lsl #2
 a28:	44070d41 	strmi	r0, [r7], #-3393	; 0xfffff2bf
 a2c:	0d41040e 	cfstrdeq	mvd0, [r1, #-56]	; 0xffffffc8
 a30:	0ec7420d 	cdpeq	2, 12, cr4, cr7, cr13, {0}
 a34:	00000000 	andeq	r0, r0, r0
 a38:	00000020 	andeq	r0, r0, r0, lsr #32
 a3c:	00000948 	andeq	r0, r0, r8, asr #18
 a40:	00044c86 	andeq	r4, r4, r6, lsl #25
 a44:	00000056 	andeq	r0, r0, r6, asr r0
 a48:	87080e41 	strhi	r0, [r8, -r1, asr #28]
 a4c:	41018e02 	tstmi	r1, r2, lsl #28
 a50:	0d41200e 	stcleq	0, cr2, [r1, #-56]	; 0xffffffc8
 a54:	080e6007 	stmdaeq	lr, {r0, r1, r2, sp, lr}
 a58:	000d0d41 	andeq	r0, sp, r1, asr #26
 a5c:	00000020 	andeq	r0, r0, r0, lsr #32
 a60:	00000948 	andeq	r0, r0, r8, asr #18
 a64:	00044cdc 	ldrdeq	r4, [r4], -ip
 a68:	00000044 	andeq	r0, r0, r4, asr #32
 a6c:	87080e41 	strhi	r0, [r8, -r1, asr #28]
 a70:	41018e02 	tstmi	r1, r2, lsl #28
 a74:	0d41180e 	stcleq	8, cr1, [r1, #-56]	; 0xffffffc8
 a78:	080e5b07 	stmdaeq	lr, {r0, r1, r2, r8, r9, fp, ip, lr}
 a7c:	000d0d41 	andeq	r0, sp, r1, asr #26
 a80:	00000020 	andeq	r0, r0, r0, lsr #32
 a84:	00000948 	andeq	r0, r0, r8, asr #18
 a88:	00044d20 	andeq	r4, r4, r0, lsr #26
 a8c:	0000012c 	andeq	r0, r0, ip, lsr #2
 a90:	87080e41 	strhi	r0, [r8, -r1, asr #28]
 a94:	41018e02 	tstmi	r1, r2, lsl #28
 a98:	0d41380e 	stcleq	8, cr3, [r1, #-56]	; 0xffffffc8
 a9c:	0e840207 	cdpeq	2, 8, cr0, cr4, cr7, {0}
 aa0:	0d0d4108 	stfeqs	f4, [sp, #-32]	; 0xffffffe0
 aa4:	00000024 	andeq	r0, r0, r4, lsr #32
 aa8:	00000948 	andeq	r0, r0, r8, asr #18
 aac:	00044e4c 	andeq	r4, r4, ip, asr #28
 ab0:	00000174 	andeq	r0, r0, r4, ror r1
 ab4:	840c0e41 	strhi	r0, [ip], #-3649	; 0xfffff1bf
 ab8:	8e028703 	cdphi	7, 0, cr8, cr2, cr3, {0}
 abc:	200e4101 	andcs	r4, lr, r1, lsl #2
 ac0:	02070d41 	andeq	r0, r7, #4160	; 0x1040
 ac4:	410c0e96 			; <UNDEFINED> instruction: 0x410c0e96
 ac8:	00000d0d 	andeq	r0, r0, sp, lsl #26
 acc:	00000020 	andeq	r0, r0, r0, lsr #32
 ad0:	00000948 	andeq	r0, r0, r8, asr #18
 ad4:	00044fc0 	andeq	r4, r4, r0, asr #31
 ad8:	00000064 	andeq	r0, r0, r4, rrx
 adc:	87080e41 	strhi	r0, [r8, -r1, asr #28]
 ae0:	41018e02 	tstmi	r1, r2, lsl #28
 ae4:	0d41200e 	stcleq	0, cr2, [r1, #-56]	; 0xffffffc8
 ae8:	080e6607 	stmdaeq	lr, {r0, r1, r2, r9, sl, sp, lr}
 aec:	000d0d41 	andeq	r0, sp, r1, asr #26
 af0:	00000020 	andeq	r0, r0, r0, lsr #32
 af4:	00000948 	andeq	r0, r0, r8, asr #18
 af8:	00045024 	andeq	r5, r4, r4, lsr #32
 afc:	00000074 	andeq	r0, r0, r4, ror r0
 b00:	87080e41 	strhi	r0, [r8, -r1, asr #28]
 b04:	41018e02 	tstmi	r1, r2, lsl #28
 b08:	0d41200e 	stcleq	0, cr2, [r1, #-56]	; 0xffffffc8
 b0c:	080e6e07 	stmdaeq	lr, {r0, r1, r2, r9, sl, fp, sp, lr}
 b10:	000d0d41 	andeq	r0, sp, r1, asr #26
 b14:	00000024 	andeq	r0, r0, r4, lsr #32
 b18:	00000948 	andeq	r0, r0, r8, asr #18
 b1c:	00045098 	muleq	r4, r8, r0
 b20:	00000054 	andeq	r0, r0, r4, asr r0
 b24:	840c0e41 	strhi	r0, [ip], #-3649	; 0xfffff1bf
 b28:	8e028703 	cdphi	7, 0, cr8, cr2, cr3, {0}
 b2c:	180e4101 	stmdane	lr, {r0, r8, lr}
 b30:	10070c41 	andne	r0, r7, r1, asr #24
 b34:	410c0e56 	tstmi	ip, r6, asr lr
 b38:	00000d0d 	andeq	r0, r0, sp, lsl #26
 b3c:	00000020 	andeq	r0, r0, r0, lsr #32
 b40:	00000948 	andeq	r0, r0, r8, asr #18
 b44:	000450ec 	andeq	r5, r4, ip, ror #1
 b48:	00000026 	andeq	r0, r0, r6, lsr #32
 b4c:	87080e41 	strhi	r0, [r8, -r1, asr #28]
 b50:	41018e02 	tstmi	r1, r2, lsl #28
 b54:	0d41180e 	stcleq	8, cr1, [r1, #-56]	; 0xffffffc8
 b58:	080e4e07 	stmdaeq	lr, {r0, r1, r2, r9, sl, fp, lr}
 b5c:	000d0d41 	andeq	r0, sp, r1, asr #26

Disassembly of section .debug_str:

00000000 <.debug_str>:
       0:	6e616c63 	cdpvs	12, 6, cr6, cr1, cr3, {3}
       4:	65762067 	ldrbvs	r2, [r6, #-103]!	; 0xffffff99
       8:	6f697372 	svcvs	0x00697372
       c:	2e33206e 	cdpcs	0, 3, cr2, cr3, cr14, {3}
      10:	20302e39 	eorscs	r2, r0, r9, lsr lr
      14:	67617428 	strbvs	r7, [r1, -r8, lsr #8]!
      18:	45522f73 	ldrbmi	r2, [r2, #-3955]	; 0xfffff08d
      1c:	5341454c 	movtpl	r4, #5452	; 0x154c
      20:	39335f45 	ldmdbcc	r3!, {r0, r2, r6, r8, r9, sl, fp, ip, lr}
      24:	69662f30 	stmdbvs	r6!, {r4, r5, r8, r9, sl, fp, sp}^
      28:	296c616e 	stmdbcs	ip!, {r1, r2, r3, r5, r6, r8, sp, lr}^
      2c:	72797300 	rsbsvc	r7, r9, #0, 6
      30:	65676e69 	strbvs	r6, [r7, #-3689]!	; 0xfffff197
      34:	706d7550 	rsbvc	r7, sp, r0, asr r5
      38:	2f00632e 	svccs	0x0000632e
      3c:	656d6f68 	strbvs	r6, [sp, #-3944]!	; 0xfffff098
      40:	7a727a2f 	bvc	1c9e904 <ringBuffer+0x1c46bfc>
      44:	37313530 			; <UNDEFINED> instruction: 0x37313530
      48:	7574732f 	ldrbvc	r7, [r4, #-815]!	; 0xfffffcd1
      4c:	632f7964 			; <UNDEFINED> instruction: 0x632f7964
      50:	6e696168 	powvsez	f6, f1, #0.0
      54:	7474615f 	ldrbtvc	r6, [r4], #-351	; 0xfffffea1
      58:	61747365 	cmnvs	r4, r5, ror #6
      5c:	6e6f6974 			; <UNDEFINED> instruction: 0x6e6f6974
      60:	4952412f 	ldmdbmi	r2, {r0, r1, r2, r3, r5, r8, lr}^
      64:	7a727a2d 	bvc	1c9e920 <ringBuffer+0x1c46c18>
      68:	74616f2f 	strbtvc	r6, [r1], #-3887	; 0xfffff0d1
      6c:	6176652d 	cmnvs	r6, sp, lsr #10
      70:	7461756c 	strbtvc	r7, [r1], #-1388	; 0xfffffa94
      74:	2f6e6f69 	svccs	0x006e6f69
      78:	69727973 	ldmdbvs	r2!, {r0, r1, r4, r5, r6, r8, fp, ip, sp, lr}^
      7c:	2d65676e 	stclcs	7, cr6, [r5, #-440]!	; 0xfffffe48
      80:	72006263 	andvc	r6, r0, #805306374	; 0x30000006
      84:	726f6365 	rsbvc	r6, pc, #-1811939327	; 0x94000001
      88:	676e6964 	strbvs	r6, [lr, -r4, ror #18]!
      8c:	616c665f 	cmnvs	ip, pc, asr r6
      90:	65720067 	ldrbvs	r0, [r2, #-103]!	; 0xffffff99
      94:	64726f63 	ldrbtvs	r6, [r2], #-3939	; 0xfffff09d
      98:	5f676e69 	svcpl	0x00676e69
      9c:	00746e63 	rsbseq	r6, r4, r3, ror #28
      a0:	626f6c67 	rsbvs	r6, pc, #26368	; 0x6700
      a4:	645f6c61 	ldrbvs	r6, [pc], #-3169	; ac <_init-0x10a74>
      a8:	00617461 	rsbeq	r7, r1, r1, ror #8
      ac:	65747375 	ldrbvs	r7, [r4, #-885]!	; 0xfffffc8b
      b0:	65507370 	ldrbvs	r7, [r0, #-880]	; 0xfffffc90
      b4:	004d4d72 	subeq	r4, sp, r2, ror sp
      b8:	65747375 	ldrbvs	r7, [r4, #-885]!	; 0xfffffc8b
      bc:	65507370 	ldrbvs	r7, [r0, #-880]	; 0xfffffc90
      c0:	004c4d72 	subeq	r4, ip, r2, ror sp
      c4:	6f746f6d 	svcvs	0x00746f6d
      c8:	72694472 	rsbvc	r4, r9, #1912602624	; 0x72000000
      cc:	006e6950 	rsbeq	r6, lr, r0, asr r9
      d0:	6f746f6d 	svcvs	0x00746f6d
      d4:	65745372 	ldrbvs	r5, [r4, #-882]!	; 0xfffffc8e
      d8:	6e695070 	mcrvs	0, 3, r5, cr9, cr0, {3}
      dc:	69727400 	ldmdbvs	r2!, {sl, ip, sp, lr}^
      e0:	72656767 	rsbvc	r6, r5, #27000832	; 0x19c0000
      e4:	006e6950 	rsbeq	r6, lr, r0, asr r9
      e8:	54676962 	strbtpl	r6, [r7], #-2402	; 0xfffff69e
      ec:	67676972 			; <UNDEFINED> instruction: 0x67676972
      f0:	69507265 	ldmdbvs	r0, {r0, r2, r5, r6, r9, ip, sp, lr}^
      f4:	6461006e 	strbtvs	r0, [r1], #-110	; 0xffffff92
      f8:	656b5f63 	strbvs	r5, [fp, #-3939]!	; 0xfffff09d
      fc:	61765f79 	cmnvs	r6, r9, ror pc
     100:	6973006c 	ldmdbvs	r3!, {r2, r3, r5, r6}^
     104:	7974657a 	ldmdbvc	r4!, {r1, r3, r4, r5, r6, r8, sl, sp, lr}^
     108:	4e006570 	cfrshl64mi	mvdx0, mvdx0, r6
     10c:	4b5f4d55 	blmi	17d3668 <ringBuffer+0x177b960>
     110:	00535945 	subseq	r5, r3, r5, asr #18
     114:	6f424c6d 	svcvs	0x00424c6d
     118:	5373756c 	cmnpl	r3, #108, 10	; 0x1b000000
     11c:	73706574 	cmnvc	r0, #116, 10	; 0x1d000000
     120:	676e654c 	strbvs	r6, [lr, -ip, asr #10]!
     124:	6d006874 	stcvs	8, cr6, [r0, #-464]	; 0xfffffe30
     128:	6c6f424c 	sfmvs	f4, 2, [pc], #-304	; 0 <_init-0x10b20>
     12c:	74537375 	ldrbvc	r7, [r3], #-885	; 0xfffffc8b
     130:	00737065 	rsbseq	r7, r3, r5, rrx
     134:	616f6c66 	cmnvs	pc, r6, ror #24
     138:	4c6d0074 	stclmi	0, cr0, [sp], #-464	; 0xfffffe30
     13c:	756c6f42 	strbvc	r6, [ip, #-3906]!	; 0xfffff0be
     140:	4c6d0073 	stclmi	0, cr0, [sp], #-460	; 0xfffffe34
     144:	42676942 	rsbmi	r6, r7, #1081344	; 0x108000
     148:	73756c6f 	cmnvc	r5, #28416	; 0x6f00
     14c:	554c6d00 	strbpl	r6, [ip, #-3328]	; 0xfffff300
     150:	00646573 	rsbeq	r6, r4, r3, ror r5
     154:	6f424c6d 	svcvs	0x00424c6d
     158:	5373756c 	cmnpl	r3, #108, 10	; 0x1b000000
     15c:	49706574 	ldmdbmi	r0!, {r2, r4, r5, r6, r8, sl, sp, lr}^
     160:	6d007864 	stcvs	8, cr7, [r0, #-400]	; 0xfffffe70
     164:	6c6f424c 	sfmvs	f4, 2, [pc], #-304	; 3c <_init-0x10ae4>
     168:	74537375 	ldrbvc	r7, [r3], #-885	; 0xfffffc8b
     16c:	73007065 	movwvc	r7, #101	; 0x65
     170:	70706574 	rsbsvc	r6, r0, r4, ror r5
     174:	6f507265 	svcvs	0x00507265
     178:	616c0073 	smcvs	49155	; 0xc003
     17c:	654b7473 	strbvs	r7, [fp, #-1139]	; 0xfffffb8d
     180:	70655279 	rsbvc	r5, r5, r9, ror r2
     184:	41746165 	cmnmi	r4, r5, ror #2
     188:	656b0074 	strbvs	r0, [fp, #-116]!	; 0xffffff8c
     18c:	70655279 	rsbvc	r5, r5, r9, ror r2
     190:	44746165 	ldrbtmi	r6, [r4], #-357	; 0xfffffe9b
     194:	79616c65 	stmdbvc	r1!, {r0, r2, r5, r6, sl, fp, sp, lr}^
     198:	79656b00 	stmdbvc	r5!, {r8, r9, fp, sp, lr}^
     19c:	6f626544 	svcvs	0x00626544
     1a0:	65636e75 	strbvs	r6, [r3, #-3701]!	; 0xfffff18b
     1a4:	65727000 	ldrbvs	r7, [r2, #-0]!
     1a8:	79654b76 	stmdbvc	r5!, {r1, r2, r4, r5, r6, r8, r9, fp, lr}^
     1ac:	53697500 	cmnpl	r9, #0, 10
     1b0:	65746174 	ldrbvs	r6, [r4, #-372]!	; 0xfffffe8c
     1b4:	65727000 	ldrbvs	r7, [r2, #-0]!
     1b8:	67694276 			; <UNDEFINED> instruction: 0x67694276
     1bc:	67697254 			; <UNDEFINED> instruction: 0x67697254
     1c0:	00726567 	rsbseq	r6, r2, r7, ror #10
     1c4:	76657270 			; <UNDEFINED> instruction: 0x76657270
     1c8:	67697254 			; <UNDEFINED> instruction: 0x67697254
     1cc:	00726567 	rsbseq	r6, r2, r7, ror #10
     1d0:	69726573 	ldmdbvs	r2!, {r0, r1, r4, r5, r6, r8, sl, sp, lr}^
     1d4:	74536c61 	ldrbvc	r6, [r3], #-3169	; 0xfffff39f
     1d8:	65730072 	ldrbvs	r0, [r3, #-114]!	; 0xffffff8e
     1dc:	6c616972 			; <UNDEFINED> instruction: 0x6c616972
     1e0:	52727453 	rsbspl	r7, r2, #1392508928	; 0x53000000
     1e4:	79646165 	stmdbvc	r4!, {r0, r2, r5, r6, r8, sp, lr}^
     1e8:	6f425f00 	svcvs	0x00425f00
     1ec:	73006c6f 	movwvc	r6, #3183	; 0xc6f
     1f0:	61697265 	cmnvs	r9, r5, ror #4
     1f4:	7274536c 	rsbsvc	r5, r4, #108, 6	; 0xb0000001
     1f8:	006e654c 	rsbeq	r6, lr, ip, asr #10
     1fc:	5f636461 	svcpl	0x00636461
     200:	5f79656b 	svcpl	0x0079656b
     204:	63006e69 	movwvs	r6, #3689	; 0xe69
     208:	42726168 	rsbsmi	r6, r2, #104, 2
     20c:	6c006675 	stcvs	6, cr6, [r0], {117}	; 0x75
     210:	4c006463 	cfstrsmi	mvf6, [r0], {99}	; 0x63
     214:	69757169 	ldmdbvs	r5!, {r0, r3, r5, r6, r8, ip, sp, lr}^
     218:	79724364 	ldmdbvc	r2!, {r2, r5, r6, r8, r9, lr}^
     21c:	6c617473 	cfstrdvs	mvd7, [r1], #-460	; 0xfffffe34
     220:	75727453 	ldrbvc	r7, [r2, #-1107]!	; 0xfffffbad
     224:	4c007463 	cfstrsmi	mvf7, [r0], {99}	; 0x63
     228:	69757169 	ldmdbvs	r5!, {r0, r3, r5, r6, r8, ip, sp, lr}^
     22c:	79724364 	ldmdbvc	r2!, {r2, r5, r6, r8, r9, lr}^
     230:	6c617473 	cfstrdvs	mvd7, [r1], #-460	; 0xfffffe34
     234:	504e4900 	subpl	r4, lr, r0, lsl #18
     238:	4f005455 	svcmi	0x00005455
     23c:	55505455 	ldrbpl	r5, [r0, #-1109]	; 0xfffffbab
     240:	49480054 	stmdbmi	r8, {r2, r4, r6}^
     244:	4c004847 	stcmi	8, cr4, [r0], {71}	; 0x47
     248:	5000574f 	andpl	r5, r0, pc, asr #14
     24c:	00485355 	subeq	r5, r8, r5, asr r3
     250:	4c4c5550 	cfstr64mi	mvdx5, [ip], {80}	; 0x50
     254:	59454b00 	stmdbpl	r5, {r8, r9, fp, lr}^
     258:	4749525f 	smlsldmi	r5, r9, pc, r2	; <UNPREDICTABLE>
     25c:	4b005448 	blmi	15384 <.DATA_REGION_0__data_end+0x466c>
     260:	555f5945 	ldrbpl	r5, [pc, #-2373]	; fffff923 <__bss_end__+0xf671131f>
     264:	454b0050 	strbmi	r0, [fp, #-80]	; 0xffffffb0
     268:	4f445f59 	svcmi	0x00445f59
     26c:	4b004e57 	blmi	13bd0 <.DATA_REGION_0__data_end+0x2eb8>
     270:	4c5f5945 	mrrcmi	9, 4, r5, pc, cr5	; <UNPREDICTABLE>
     274:	00544645 	subseq	r4, r4, r5, asr #12
     278:	5f59454b 	svcpl	0x0059454b
     27c:	454c4553 	strbmi	r4, [ip, #-1363]	; 0xfffffaad
     280:	4b005443 	blmi	15394 <.DATA_REGION_0__data_end+0x467c>
     284:	4e5f5945 	vnmlami.f16	s11, s30, s10	; <UNPREDICTABLE>
     288:	00454e4f 	subeq	r4, r5, pc, asr #28
     28c:	4e49414d 	dvfmiem	f4, f1, #5.0
     290:	4c4f4200 	sfmmi	f4, 2, [pc], {-0}
     294:	4d5f5355 	ldclmi	3, cr5, [pc, #-340]	; 148 <_init-0x109d8>
     298:	00554e45 	subseq	r4, r5, r5, asr #28
     29c:	6c697475 	cfstrdvs	mvd7, [r9], #-468	; 0xfffffe2c
     2a0:	6c00632e 	stcvs	3, cr6, [r0], {46}	; 0x2e
     2a4:	632e6465 			; <UNDEFINED> instruction: 0x632e6465
     2a8:	71694c00 	cmnvc	r9, r0, lsl #24
     2ac:	43646975 	cmnmi	r4, #1916928	; 0x1d4000
     2b0:	74737972 	ldrbtvc	r7, [r3], #-2418	; 0xfffff68e
     2b4:	632e6c61 			; <UNDEFINED> instruction: 0x632e6c61
     2b8:	74657300 	strbtvc	r7, [r5], #-768	; 0xfffffd00
     2bc:	6c007075 	stcvs	0, cr7, [r0], {117}	; 0x75
     2c0:	00706f6f 	rsbseq	r6, r0, pc, ror #30
     2c4:	636f7270 	cmnvs	pc, #112, 4
     2c8:	53737365 	cmnpl	r3, #-1811939327	; 0x94000001
     2cc:	61697265 	cmnvs	r9, r5, ror #4
     2d0:	7075006c 	rsbsvc	r0, r5, ip, rrx
     2d4:	65746164 	ldrbvs	r6, [r4, #-356]!	; 0xfffffe9c
     2d8:	65726353 	ldrbvs	r6, [r2, #-851]!	; 0xfffffcad
     2dc:	63006e65 	movwvs	r6, #3685	; 0xe65
     2e0:	6b636568 	blvs	18d9888 <ringBuffer+0x1881b80>
     2e4:	67697254 			; <UNDEFINED> instruction: 0x67697254
     2e8:	73726567 	cmnvc	r2, #432013312	; 0x19c00000
     2ec:	61657200 	cmnvs	r5, r0, lsl #4
     2f0:	72655364 	rsbvc	r5, r5, #100, 6	; 0x90000001
     2f4:	006c6169 	rsbeq	r6, ip, r9, ror #2
     2f8:	64616572 	strbtvs	r6, [r1], #-1394	; 0xfffffa8e
     2fc:	0079654b 	rsbseq	r6, r9, fp, asr #10
     300:	5f746567 	svcpl	0x00746567
     304:	0079656b 	rsbseq	r6, r9, fp, ror #10
     308:	654b6f64 	strbvs	r6, [fp, #-3940]	; 0xfffff09c
     30c:	74634179 	strbtvc	r4, [r3], #-377	; 0xfffffe87
     310:	006e6f69 	rsbeq	r6, lr, r9, ror #30
     314:	77726f66 	ldrbvc	r6, [r2, -r6, ror #30]!
     318:	5f647261 	svcpl	0x00647261
     31c:	67726174 			; <UNDEFINED> instruction: 0x67726174
     320:	6d007465 	cfstrsvs	mvf7, [r0, #-404]	; 0xfffffe6c
     324:	006e6961 	rsbeq	r6, lr, r1, ror #18
     328:	4d6e6970 			; <UNDEFINED> instruction: 0x4d6e6970
     32c:	0065646f 	rsbeq	r6, r5, pc, ror #8
     330:	69676964 	stmdbvs	r7!, {r2, r5, r6, r8, fp, sp, lr}^
     334:	526c6174 	rsbpl	r6, ip, #116, 2
     338:	00646165 	rsbeq	r6, r4, r5, ror #2
     33c:	69676964 	stmdbvs	r7!, {r2, r5, r6, r8, fp, sp, lr}^
     340:	576c6174 			; <UNDEFINED> instruction: 0x576c6174
     344:	65746972 	ldrbvs	r6, [r4, #-2418]!	; 0xfffff68e
     348:	72655300 	rsbvc	r5, r5, #0, 6
     34c:	5f6c6169 	svcpl	0x006c6169
     350:	69676562 	stmdbvs	r7!, {r1, r5, r6, r8, sl, sp, lr}^
     354:	6553006e 	ldrbvs	r0, [r3, #-110]	; 0xffffff92
     358:	6c616972 			; <UNDEFINED> instruction: 0x6c616972
     35c:	6176615f 	cmnvs	r6, pc, asr r1
     360:	62616c69 	rsbvs	r6, r1, #26880	; 0x6900
     364:	5300656c 	movwpl	r6, #1388	; 0x56c
     368:	61697265 	cmnvs	r9, r5, ror #4
     36c:	65725f6c 	ldrbvs	r5, [r2, #-3948]!	; 0xfffff094
     370:	53006461 	movwpl	r6, #1121	; 0x461
     374:	61697265 	cmnvs	r9, r5, ror #4
     378:	72775f6c 	rsbsvc	r5, r7, #108, 30	; 0x1b0
     37c:	00657469 	rsbeq	r7, r5, r9, ror #8
     380:	6c616e61 	stclvs	14, cr6, [r1], #-388	; 0xfffffe7c
     384:	6552676f 	ldrbvs	r6, [r2, #-1903]	; 0xfffff891
     388:	6d006461 	cfstrsvs	mvf6, [r0, #-388]	; 0xfffffe7c
     38c:	696c6c69 	stmdbvs	ip!, {r0, r3, r5, r6, sl, fp, sp, lr}^
     390:	73750073 	cmnvc	r5, #115	; 0x73
     394:	00736365 	rsbseq	r6, r3, r5, ror #6
     398:	616c6564 	cmnvs	ip, r4, ror #10
     39c:	63694d79 	cmnvs	r9, #7744	; 0x1e40
     3a0:	65736f72 	ldrbvs	r6, [r3, #-3954]!	; 0xfffff08e
     3a4:	646e6f63 	strbtvs	r6, [lr], #-3939	; 0xfffff09d
     3a8:	6f740073 	svcvs	0x00740073
     3ac:	746e4955 	strbtvc	r4, [lr], #-2389	; 0xfffff6ab
     3b0:	64656c00 	strbtvs	r6, [r5], #-3072	; 0xfffff400
     3b4:	006e6f5f 	rsbeq	r6, lr, pc, asr pc
     3b8:	5f64656c 	svcpl	0x0064656c
     3bc:	0066666f 	rsbeq	r6, r6, pc, ror #12
     3c0:	5f64636c 	svcpl	0x0064636c
     3c4:	69676562 	stmdbvs	r7!, {r1, r5, r6, r8, sl, sp, lr}^
     3c8:	636c006e 	cmnvs	ip, #110	; 0x6e
     3cc:	6c635f64 	stclvs	15, cr5, [r3], #-400	; 0xfffffe70
     3d0:	00726165 	rsbseq	r6, r2, r5, ror #2
     3d4:	5f64636c 	svcpl	0x0064636c
     3d8:	6e697270 	mcrvs	2, 3, r7, cr9, cr0, {3}
     3dc:	636c0074 	cmnvs	ip, #116	; 0x74
     3e0:	65735f64 	ldrbvs	r5, [r3, #-3940]!	; 0xfffff09c
     3e4:	72754374 	rsbsvc	r4, r5, #116, 6	; 0xd0000001
     3e8:	00726f73 	rsbseq	r6, r2, r3, ror pc
     3ec:	6e756f63 	cdpvs	15, 7, cr6, cr5, cr3, {3}
     3f0:	74730074 	ldrbtvc	r0, [r3], #-116	; 0xffffff8c
     3f4:	00747261 	rsbseq	r7, r4, r1, ror #4
     3f8:	6f624c75 	svcvs	0x00624c75
     3fc:	0073756c 	rsbseq	r7, r3, ip, ror #10
     400:	65726964 	ldrbvs	r6, [r2, #-2404]!	; 0xfffff69c
     404:	6f697463 	svcvs	0x00697463
     408:	7473006e 	ldrbtvc	r0, [r3], #-110	; 0xffffff92
     40c:	00737065 	rsbseq	r7, r3, r5, rrx
     410:	65447375 	strbvs	r7, [r4, #-885]	; 0xfffffc8b
     414:	0079616c 	rsbseq	r6, r9, ip, ror #2
     418:	31730069 	cmncc	r3, r9, rrx
     41c:	4c317300 	ldcmi	3, cr7, [r1], #-0
     420:	73006e65 	movwvc	r6, #3685	; 0xe65
     424:	6e654c32 	mcrvs	12, 3, r4, cr5, cr2, {1}
     428:	73757000 	cmnvc	r5, #0
     42c:	69725468 	ldmdbvs	r2!, {r3, r5, r6, sl, ip, lr}^
     430:	72656767 	rsbvc	r6, r5, #27000832	; 0x19c0000
     434:	756c6156 	strbvc	r6, [ip, #-342]!	; 0xfffffeaa
     438:	69620065 	stmdbvs	r2!, {r0, r2, r5, r6}^
     43c:	69725467 	ldmdbvs	r2!, {r0, r1, r2, r5, r6, sl, ip, lr}^
     440:	72656767 	rsbvc	r6, r5, #27000832	; 0x19c0000
     444:	756c6156 	strbvc	r6, [ip, #-342]!	; 0xfffffeaa
     448:	4c6d0065 	stclmi	0, cr0, [sp], #-404	; 0xfffffe6c
     44c:	756c6f42 	strbvc	r6, [ip, #-3906]!	; 0xfffff0be
     450:	6d655473 	cfstrdvs	mvd5, [r5, #-460]!	; 0xfffffe34
     454:	6e690070 	mcrvs	0, 3, r0, cr9, cr0, {3}
     458:	72616843 	rsbvc	r6, r1, #4390912	; 0x430000
     45c:	72756300 	rsbsvc	r6, r5, #0, 6
     460:	746e6572 	strbtvc	r6, [lr], #-1394	; 0xfffffa8e
     464:	656d6954 	strbvs	r6, [sp, #-2388]!	; 0xfffff6ac
     468:	6d697400 	cfstrdvs	mvd7, [r9, #-0]
     46c:	6e695365 	cdpvs	3, 6, cr5, cr9, cr5, {3}
     470:	614c6563 	cmpvs	ip, r3, ror #10
     474:	72507473 	subsvc	r7, r0, #1929379840	; 0x73000000
     478:	00737365 	rsbseq	r7, r3, r5, ror #6
     47c:	636f7270 	cmnvs	pc, #112, 4
     480:	54737365 	ldrbtpl	r7, [r3], #-869	; 0xfffffc9b
     484:	4b736968 	blmi	1cdaa2c <ringBuffer+0x1c82d24>
     488:	69007965 	stmdbvs	r0, {r0, r2, r5, r6, r8, fp, ip, sp, lr}
     48c:	7475706e 	ldrbtvc	r7, [r5], #-110	; 0xffffff92
     490:	67726100 	ldrbvs	r6, [r2, -r0, lsl #2]!
     494:	72610063 	rsbvc	r0, r1, #99	; 0x63
     498:	66007367 	strvs	r7, [r0], -r7, ror #6
     49c:	74706e75 	ldrbtvc	r6, [r0], #-3701	; 0xfffff18b
     4a0:	6e690072 	mcrvs	0, 3, r0, cr9, cr2, {3}
     4a4:	65726964 	ldrbvs	r6, [r2, #-2404]!	; 0xfffff69c
     4a8:	665f7463 	ldrbvs	r7, [pc], -r3, ror #8
     4ac:	00636e75 	rsbeq	r6, r3, r5, ror lr
     4b0:	006e6970 	rsbeq	r6, lr, r0, ror r9
     4b4:	64756162 	ldrbtvs	r6, [r5], #-354	; 0xfffffe9e
     4b8:	74756f00 	ldrbtvc	r6, [r5], #-3840	; 0xfffff100
     4bc:	00747570 	rsbseq	r7, r4, r0, ror r5
     4c0:	735f7674 	cmpvc	pc, #116, 12	; 0x7400000
     4c4:	5f006365 	svcpl	0x00006365
     4c8:	6d69745f 	cfstrdvs	mvd7, [r9, #-380]!	; 0xfffffe84
     4cc:	00745f65 	rsbseq	r5, r4, r5, ror #30
     4d0:	755f7674 	ldrbvc	r7, [pc, #-1652]	; fffffe64 <__bss_end__+0xf6711860>
     4d4:	00636573 	rsbeq	r6, r3, r3, ror r5
     4d8:	75735f5f 	ldrbvc	r5, [r3, #-3935]!	; 0xfffff0a1
     4dc:	6f636573 	svcvs	0x00636573
     4e0:	5f73646e 	svcpl	0x0073646e
     4e4:	69740074 	ldmdbvs	r4!, {r2, r4, r5, r6}^
     4e8:	6176656d 	cmnvs	r6, sp, ror #10
     4ec:	6f63006c 	svcvs	0x0063006c
     4f0:	7200736c 	andvc	r7, r0, #108, 6	; 0xb0000001
     4f4:	0073776f 	rsbseq	r7, r3, pc, ror #14
     4f8:	666f5f5f 	uqsaxvs	r5, pc, pc	; <UNPREDICTABLE>
     4fc:	00745f66 	rsbseq	r5, r4, r6, ror #30
     500:	5f4f495f 	svcpl	0x004f495f
     504:	64616572 	strbtvs	r6, [r1], #-1394	; 0xfffffa8e
     508:	7274705f 	rsbsvc	r7, r4, #95	; 0x5f
     50c:	68635f00 	stmdavs	r3!, {r8, r9, sl, fp, ip, lr}^
     510:	006e6961 	rsbeq	r6, lr, r1, ror #18
     514:	746c6173 	strbtvc	r6, [ip], #-371	; 0xfffffe8d
     518:	616c6200 	cmnvs	ip, r0, lsl #4
     51c:	7332656b 	teqvc	r2, #448790528	; 0x1ac00000
     520:	616c6200 	cmnvs	ip, r0, lsl #4
     524:	7332656b 	teqvc	r2, #448790528	; 0x1ac00000
     528:	6174735f 	cmnvs	r4, pc, asr r3
     52c:	5f5f6574 	svcpl	0x005f6574
     530:	7a697300 	bvc	1a5d138 <ringBuffer+0x1a05430>
     534:	00745f65 	rsbseq	r5, r4, r5, ror #30
     538:	6f68735f 	svcvs	0x0068735f
     53c:	75627472 	strbvc	r7, [r2, #-1138]!	; 0xfffffb8e
     540:	65730066 	ldrbvs	r0, [r3, #-102]!	; 0xffffff9a
     544:	65727563 	ldrbvs	r7, [r2, #-1379]!	; 0xfffffa9d
     548:	72657a5f 	rsbvc	r7, r5, #389120	; 0x5f000
     54c:	656d5f6f 	strbvs	r5, [sp, #-3951]!	; 0xfffff091
     550:	79726f6d 	ldmdbvc	r2!, {r0, r2, r3, r5, r6, r8, r9, sl, fp, sp, lr}^
     554:	746f7200 	strbtvc	r7, [pc], #-512	; 55c <_init-0x105c4>
     558:	00323372 	eorseq	r3, r2, r2, ror r3
     55c:	5f4f495f 	svcpl	0x004f495f
     560:	5f315f32 	svcpl	0x00315f32
     564:	65647473 	strbvs	r7, [r4, #-1139]!	; 0xfffffb8d
     568:	005f7272 	subseq	r7, pc, r2, ror r2	; <UNPREDICTABLE>
     56c:	5f4f495f 	svcpl	0x004f495f
     570:	5f667562 	svcpl	0x00667562
     574:	65736162 	ldrbvs	r6, [r3, #-354]!	; 0xfffffe9e
     578:	6e6f6c00 	cdpvs	12, 6, cr6, cr15, cr0, {0}
     57c:	6f6c2067 	svcvs	0x006c2067
     580:	7520676e 	strvc	r6, [r0, #-1902]!	; 0xfffff892
     584:	6769736e 	strbvs	r7, [r9, -lr, ror #6]!
     588:	2064656e 	rsbcs	r6, r4, lr, ror #10
     58c:	00746e69 	rsbseq	r6, r4, r9, ror #28
     590:	6b616c62 	blvs	185b720 <ringBuffer+0x1803a18>
     594:	5f733265 	svcpl	0x00733265
     598:	6d676973 			; <UNDEFINED> instruction: 0x6d676973
     59c:	6c620061 	stclvs	0, cr0, [r2], #-388	; 0xfffffe7c
     5a0:	32656b61 	rsbcc	r6, r5, #99328	; 0x18400
     5a4:	69665f73 	stmdbvs	r6!, {r0, r1, r4, r5, r6, r8, r9, sl, fp, ip, lr}^
     5a8:	006c616e 	rsbeq	r6, ip, lr, ror #2
     5ac:	656e6e69 	strbvs	r6, [lr, #-3689]!	; 0xfffff197
     5b0:	656c5f72 	strbvs	r5, [ip, #-3954]!	; 0xfffff08e
     5b4:	6874676e 	ldmdavs	r4!, {r1, r2, r3, r5, r6, r8, r9, sl, sp, lr}^
     5b8:	6e6f6c00 	cdpvs	12, 6, cr6, cr15, cr0, {0}
     5bc:	6f6c2067 	svcvs	0x006c2067
     5c0:	6920676e 	stmdbvs	r0!, {r1, r2, r3, r5, r6, r8, r9, sl, sp, lr}
     5c4:	6200746e 	andvs	r7, r0, #1845493760	; 0x6e000000
     5c8:	656b616c 	strbvs	r6, [fp, #-364]!	; 0xfffffe94
     5cc:	735f7332 	cmpvc	pc, #-939524096	; 0xc8000000
     5d0:	6c5f7465 	cfldrdvs	mvd7, [pc], {101}	; 0x65
     5d4:	62747361 	rsbsvs	r7, r4, #-2080374783	; 0x84000001
     5d8:	6b636f6c 	blvs	18dc390 <ringBuffer+0x1884688>
     5dc:	616c6200 	cmnvs	ip, r0, lsl #4
     5e0:	6232656b 	eorsvs	r6, r2, #448790528	; 0x1ac00000
     5e4:	6e6f635f 	mcrvs	3, 3, r6, cr15, cr15, {2}
     5e8:	6e617473 	mcrvs	4, 3, r7, cr1, cr3, {3}
     5ec:	665f0074 			; <UNDEFINED> instruction: 0x665f0074
     5f0:	6e656c69 	cdpvs	12, 6, cr6, cr5, cr9, {3}
     5f4:	495f006f 	ldmdbmi	pc, {r0, r1, r2, r3, r5, r6}^	; <UNPREDICTABLE>
     5f8:	65725f4f 	ldrbvs	r5, [r2, #-3919]!	; 0xfffff0b1
     5fc:	655f6461 	ldrbvs	r6, [pc, #-1121]	; 1a3 <_init-0x1097d>
     600:	5f00646e 	svcpl	0x0000646e
     604:	6175715f 	cmnvs	r5, pc, asr r1
     608:	00745f64 	rsbseq	r5, r4, r4, ror #30
     60c:	6b616c62 	blvs	185b79c <ringBuffer+0x1803a94>
     610:	5f733265 	svcpl	0x00733265
     614:	6c5f7369 	mrrcvs	3, 6, r7, pc, cr9	; <UNPREDICTABLE>
     618:	62747361 	rsbsvs	r7, r4, #-2080374783	; 0x84000001
     61c:	6b636f6c 	blvs	18dc3d4 <ringBuffer+0x18846cc>
     620:	414c4200 	mrsmi	r4, (UNDEF: 108)
     624:	4232454b 	eorsmi	r4, r2, #314572800	; 0x12c00000
     628:	4c41535f 	mcrrmi	3, 5, r5, r1, cr15
     62c:	54594254 	ldrbpl	r4, [r9], #-596	; 0xfffffdac
     630:	5f005345 	svcpl	0x00005345
     634:	67616c66 	strbvs	r6, [r1, -r6, ror #24]!
     638:	74730073 	ldrbtvc	r0, [r3], #-115	; 0xffffff8d
     63c:	3365726f 	cmncc	r5, #-268435450	; 0xf0000006
     640:	495f0032 	ldmdbmi	pc, {r1, r4, r5}^	; <UNPREDICTABLE>
     644:	75625f4f 	strbvc	r5, [r2, #-3919]!	; 0xfffff0b1
     648:	6e655f66 	cdpvs	15, 6, cr5, cr5, cr6, {3}
     64c:	635f0064 	cmpvs	pc, #100	; 0x64
     650:	635f7275 	cmpvs	pc, #1342177287	; 0x50000007
     654:	6d756c6f 	ldclvs	12, cr6, [r5, #-444]!	; 0xfffffe44
     658:	6c62006e 	stclvs	0, cr0, [r2], #-440	; 0xfffffe48
     65c:	32656b61 	rsbcc	r6, r5, #99328	; 0x18400
     660:	6e695f73 	mcrvs	15, 3, r5, cr9, cr3, {3}
     664:	75007469 	strvc	r7, [r0, #-1129]	; 0xfffffb97
     668:	31746e69 	cmncc	r4, r9, ror #28
     66c:	00745f36 	rsbseq	r5, r4, r6, lsr pc
     670:	6661656c 	strbtvs	r6, [r1], -ip, ror #10
     674:	6e656c5f 	mcrvs	12, 3, r6, cr5, cr15, {2}
     678:	00687467 	rsbeq	r7, r8, r7, ror #8
     67c:	6b616c62 	blvs	185b80c <ringBuffer+0x1803b04>
     680:	5f733265 	svcpl	0x00733265
     684:	72636e69 	rsbvc	r6, r3, #1680	; 0x690
     688:	6e656d65 	cdpvs	13, 6, cr6, cr5, cr5, {3}
     68c:	6f635f74 	svcvs	0x00635f74
     690:	65746e75 	ldrbvs	r6, [r4, #-3701]!	; 0xfffff18b
     694:	6f5f0072 	svcvs	0x005f0072
     698:	6f5f646c 	svcvs	0x005f646c
     69c:	65736666 	ldrbvs	r6, [r3, #-1638]!	; 0xfffff99a
     6a0:	656b0074 	strbvs	r0, [fp, #-116]!	; 0xffffff8c
     6a4:	656c5f79 	strbvs	r5, [ip, #-3961]!	; 0xfffff087
     6a8:	6874676e 	ldmdavs	r4!, {r1, r2, r3, r5, r6, r8, r9, sl, sp, lr}^
     6ac:	6c6e6900 			; <UNDEFINED> instruction: 0x6c6e6900
     6b0:	6c006e65 	stcvs	14, cr6, [r0], {101}	; 0x65
     6b4:	3364616f 	cmncc	r4, #-1073741797	; 0xc000001b
     6b8:	6c620032 	stclvs	0, cr0, [r2], #-200	; 0xffffff38
     6bc:	32656b61 	rsbcc	r6, r5, #99328	; 0x18400
     6c0:	6e695f73 	mcrvs	15, 3, r5, cr9, cr3, {3}
     6c4:	6b5f7469 	blvs	17dd870 <ringBuffer+0x1785b68>
     6c8:	6d007965 	vstrvs.16	s14, [r0, #-202]	; 0xffffff36	; <UNPREDICTABLE>
     6cc:	65736d65 	ldrbvs	r6, [r3, #-3429]!	; 0xfffff29b
     6d0:	00765f74 	rsbseq	r5, r6, r4, ror pc
     6d4:	5f4f495f 	svcpl	0x004f495f
     6d8:	6b72616d 	blvs	1c98c94 <ringBuffer+0x1c40f8c>
     6dc:	73007265 	movwvc	r7, #613	; 0x265
     6e0:	6e696474 	mcrvs	4, 3, r6, cr9, cr4, {3}
     6e4:	414c4200 	mrsmi	r4, (UNDEF: 108)
     6e8:	5332454b 	teqpl	r2, #314572800	; 0x12c00000
     6ec:	59454b5f 	stmdbpl	r5, {r0, r1, r2, r3, r4, r6, r8, r9, fp, lr}^
     6f0:	45545942 	ldrbmi	r5, [r4, #-2370]	; 0xfffff6be
     6f4:	682f0053 	stmdavs	pc!, {r0, r1, r4, r6}	; <UNPREDICTABLE>
     6f8:	2f656d6f 	svccs	0x00656d6f
     6fc:	6f62736f 	svcvs	0x0062736f
     700:	2f736578 	svccs	0x00736578
     704:	6b736544 	blvs	1cd9c1c <ringBuffer+0x1c81f14>
     708:	2f706f74 	svccs	0x00706f74
     70c:	4b414c42 	blmi	105381c <ringBuffer+0xffbb14>
     710:	722f3245 	eorvc	r3, pc, #1342177284	; 0x50000004
     714:	5f006665 	svcpl	0x00006665
     718:	465f4f49 	ldrbmi	r4, [pc], -r9, asr #30
     71c:	5f454c49 	svcpl	0x00454c49
     720:	73756c70 	cmnvc	r5, #112, 24	; 0x7000
     724:	4f495f00 	svcmi	0x00495f00
     728:	6972775f 	ldmdbvs	r2!, {r0, r1, r2, r3, r4, r6, r8, r9, sl, ip, sp, lr}^
     72c:	705f6574 	subsvc	r6, pc, r4, ror r5	; <UNPREDICTABLE>
     730:	42007274 	andmi	r7, r0, #116, 4	; 0x40000007
     734:	454b414c 	strbmi	r4, [fp, #-332]	; 0xfffffeb4
     738:	4f5f5332 	svcmi	0x005f5332
     73c:	59425455 	stmdbpl	r2, {r0, r2, r4, r6, sl, ip, lr}^
     740:	00534554 	subseq	r4, r3, r4, asr r5
     744:	5f737973 	svcpl	0x00737973
     748:	7272656e 	rsbsvc	r6, r2, #461373440	; 0x1b800000
     74c:	62735f00 	rsbsvs	r5, r3, #0, 30
     750:	73006675 	movwvc	r6, #1653	; 0x675
     754:	74726f68 	ldrbtvc	r6, [r2], #-3944	; 0xfffff098
     758:	736e7520 	cmnvc	lr, #32, 10	; 0x8000000
     75c:	656e6769 	strbvs	r6, [lr, #-1897]!	; 0xfffff897
     760:	6e692064 	cdpvs	0, 6, cr2, cr9, cr4, {3}
     764:	4c420074 	mcrrmi	0, 7, r0, r2, cr4
     768:	32454b41 	subcc	r4, r5, #66560	; 0x10400
     76c:	4c425f53 	mcrrmi	15, 5, r5, r2, cr3
     770:	424b434f 	submi	r4, fp, #1006632961	; 0x3c000001
     774:	53455459 	movtpl	r5, #21593	; 0x5459
     778:	67696400 	strbvs	r6, [r9, -r0, lsl #8]!
     77c:	5f747365 	svcpl	0x00747365
     780:	676e656c 	strbvs	r6, [lr, -ip, ror #10]!
     784:	5f006874 	svcpl	0x00006874
     788:	735f4f49 	cmpvc	pc, #292	; 0x124
     78c:	5f657661 	svcpl	0x00657661
     790:	65736162 	ldrbvs	r6, [r3, #-354]!	; 0xfffffe9e
     794:	6f6c5f00 	svcvs	0x006c5f00
     798:	5f006b63 	svcpl	0x00006b63
     79c:	67616c66 	strbvs	r6, [r1, -r6, ror #24]!
     7a0:	5f003273 	svcpl	0x00003273
     7a4:	65646f6d 	strbvs	r6, [r4, #-3949]!	; 0xfffff093
     7a8:	64747300 	ldrbtvs	r7, [r4], #-768	; 0xfffffd00
     7ac:	0074756f 	rsbseq	r7, r4, pc, ror #10
     7b0:	5f4f495f 	svcpl	0x004f495f
     7b4:	5f315f32 	svcpl	0x00315f32
     7b8:	69647473 	stmdbvs	r4!, {r0, r1, r4, r5, r6, sl, ip, sp, lr}^
     7bc:	6c005f6e 	stcvs	15, cr5, [r0], {110}	; 0x6e
     7c0:	20676e6f 	rsbcs	r6, r7, pc, ror #28
     7c4:	62756f64 	rsbsvs	r6, r5, #100, 30	; 0x190
     7c8:	6200656c 	andvs	r6, r0, #108, 10	; 0x1b000000
     7cc:	656b616c 	strbvs	r6, [fp, #-364]!	; 0xfffffe94
     7d0:	735f7332 	cmpvc	pc, #-939524096	; 0xc8000000
     7d4:	6c5f7465 	cfldrdvs	mvd7, [pc], {101}	; 0x65
     7d8:	6e747361 	cdpvs	3, 7, cr7, cr4, cr1, {3}
     7dc:	0065646f 	rsbeq	r6, r5, pc, ror #8
     7e0:	5f4f495f 	svcpl	0x004f495f
     7e4:	74697277 	strbtvc	r7, [r9], #-631	; 0xfffffd89
     7e8:	6e655f65 	cdpvs	15, 6, cr5, cr5, cr5, {3}
     7ec:	6f6e0064 	svcvs	0x006e0064
     7f0:	645f6564 	ldrbvs	r6, [pc], #-1380	; 7f8 <_init-0x10328>
     7f4:	68747065 	ldmdavs	r4!, {r0, r2, r5, r6, ip, sp, lr}^
     7f8:	616c6200 	cmnvs	ip, r0, lsl #4
     7fc:	7332656b 	teqvc	r2, #448790528	; 0x1ac00000
     800:	7261705f 	rsbvc	r7, r1, #95	; 0x5f
     804:	5f006d61 	svcpl	0x00006d61
     808:	6c5f4f49 	mrrcvs	15, 4, r4, pc, cr9	; <UNPREDICTABLE>
     80c:	5f6b636f 	svcpl	0x006b636f
     810:	495f0074 	ldmdbmi	pc, {r2, r4, r5, r6}^	; <UNPREDICTABLE>
     814:	49465f4f 	stmdbmi	r6, {r0, r1, r2, r3, r6, r8, r9, sl, fp, ip, lr}^
     818:	6e00454c 	cfsh32vs	mvfx4, mvfx0, #44
     81c:	5f65646f 	svcpl	0x0065646f
     820:	7366666f 	cmnvc	r6, #116391936	; 0x6f00000
     824:	70007465 	andvc	r7, r0, r5, ror #8
     828:	6f737265 	svcvs	0x00737265
     82c:	006c616e 	rsbeq	r6, ip, lr, ror #2
     830:	736f705f 	cmnvc	pc, #95	; 0x5f
     834:	73797300 	cmnvc	r9, #0, 6
     838:	7272655f 	rsbsvc	r6, r2, #398458880	; 0x17c00000
     83c:	7473696c 	ldrbtvc	r6, [r3], #-2412	; 0xfffff694
     840:	616d5f00 	cmnvs	sp, r0, lsl #30
     844:	72656b72 	rsbvc	r6, r5, #116736	; 0x1c800
     848:	61660073 	smcvs	24579	; 0x6003
     84c:	74756f6e 	ldrbtvc	r6, [r5], #-3950	; 0xfffff092
     850:	414c4200 	mrsmi	r4, (UNDEF: 108)
     854:	5332454b 	teqpl	r2, #314572800	; 0x12c00000
     858:	4c41535f 	mcrrmi	3, 5, r5, r1, cr15
     85c:	54594254 	ldrbpl	r4, [r9], #-596	; 0xfffffdac
     860:	78005345 	stmdavc	r0, {r0, r2, r6, r8, r9, ip, lr}
     864:	6c5f666f 	mrrcvs	6, 6, r6, pc, cr15	; <UNPREDICTABLE>
     868:	74676e65 	strbtvc	r6, [r7], #-3685	; 0xfffff19b
     86c:	6e750068 	cdpvs	0, 7, cr0, cr5, cr8, {3}
     870:	6e676973 			; <UNDEFINED> instruction: 0x6e676973
     874:	63206465 			; <UNDEFINED> instruction: 0x63206465
     878:	00726168 	rsbseq	r6, r2, r8, ror #2
     87c:	726f6873 	rsbvc	r6, pc, #7536640	; 0x730000
     880:	6e692074 	mcrvs	0, 3, r2, cr9, cr4, {3}
     884:	4c420074 	mcrrmi	0, 7, r0, r2, cr4
     888:	32454b41 	subcc	r4, r5, #66560	; 0x10400
     88c:	4c425f42 	mcrrmi	15, 4, r5, r2, cr2
     890:	424b434f 	submi	r4, fp, #1006632961	; 0x3c000001
     894:	53455459 	movtpl	r5, #21593	; 0x5459
     898:	616c6200 	cmnvs	ip, r0, lsl #4
     89c:	7332656b 	teqvc	r2, #448790528	; 0x1ac00000
     8a0:	7261705f 	rsbvc	r7, r1, #95	; 0x5f
     8a4:	5f5f6d61 	svcpl	0x005f6d61
     8a8:	6c696600 	stclvs	6, cr6, [r9], #-0
     8ac:	765f006c 	ldrbvc	r0, [pc], -ip, rrx
     8b0:	6c626174 	stfvse	f6, [r2], #-464	; 0xfffffe30
     8b4:	666f5f65 	strbtvs	r5, [pc], -r5, ror #30
     8b8:	74657366 	strbtvc	r7, [r5], #-870	; 0xfffffc9a
     8bc:	4f495f00 	svcmi	0x00495f00
     8c0:	315f325f 	cmpcc	pc, pc, asr r2	; <UNPREDICTABLE>
     8c4:	6474735f 	ldrbtvs	r7, [r4], #-863	; 0xfffffca1
     8c8:	5f74756f 	svcpl	0x0074756f
     8cc:	66756200 	ldrbtvs	r6, [r5], -r0, lsl #4
     8d0:	006e656c 	rsbeq	r6, lr, ip, ror #10
     8d4:	6c79656b 	cfldr64vs	mvdx6, [r9], #-428	; 0xfffffe54
     8d8:	62006e65 	andvs	r6, r0, #1616	; 0x650
     8dc:	656b616c 	strbvs	r6, [fp, #-364]!	; 0xfffffe94
     8e0:	695f7332 	ldmdbvs	pc, {r1, r4, r5, r8, r9, ip, sp, lr}^	; <UNPREDICTABLE>
     8e4:	3074696e 	rsbscc	r6, r4, lr, ror #18
     8e8:	6e697500 	cdpvs	5, 6, cr7, cr9, cr0, {0}
     8ec:	5f323374 	svcpl	0x00323374
     8f0:	6c620074 	stclvs	0, cr0, [r2], #-464	; 0xfffffe30
     8f4:	32656b61 	rsbcc	r6, r5, #99328	; 0x18400
     8f8:	6e695f73 	mcrvs	15, 3, r5, cr9, cr3, {3}
     8fc:	705f7469 	subsvc	r7, pc, r9, ror #8
     900:	6d617261 	sfmvs	f7, 2, [r1, #-388]!	; 0xfffffe7c
     904:	414c4200 	mrsmi	r4, (UNDEF: 108)
     908:	5332454b 	teqpl	r2, #314572800	; 0x12c00000
     90c:	5245505f 	subpl	r5, r5, #95	; 0x5f
     910:	414e4f53 	cmpmi	lr, r3, asr pc
     914:	5459424c 	ldrbpl	r4, [r9], #-588	; 0xfffffdb4
     918:	62005345 	andvs	r5, r0, #335544321	; 0x14000001
     91c:	656b616c 	strbvs	r6, [fp, #-364]!	; 0xfffffe94
     920:	635f7332 	cmpvs	pc, #-939524096	; 0xc8000000
     924:	72706d6f 	rsbsvc	r6, r0, #7104	; 0x1bc0
     928:	00737365 	rsbseq	r7, r3, r5, ror #6
     92c:	6b616c62 	blvs	185babc <ringBuffer+0x1803db4>
     930:	5f733265 	svcpl	0x00733265
     934:	5f005649 	svcpl	0x00005649
     938:	7478656e 	ldrbtvc	r6, [r8], #-1390	; 0xfffffa92
     93c:	6f5f5f00 	svcvs	0x005f5f00
     940:	34366666 	ldrtcc	r6, [r6], #-1638	; 0xfffff99a
     944:	5f00745f 	svcpl	0x0000745f
     948:	725f4f49 	subsvc	r4, pc, #292	; 0x124
     94c:	5f646165 	svcpl	0x00646165
     950:	65736162 	ldrbvs	r6, [r3, #-354]!	; 0xfffffe9e
     954:	4f495f00 	svcmi	0x00495f00
     958:	7661735f 			; <UNDEFINED> instruction: 0x7661735f
     95c:	6e655f65 	cdpvs	15, 6, cr5, cr5, cr5, {3}
     960:	616c0064 	cmnvs	ip, r4, rrx
     964:	6e5f7473 	mrcvs	4, 2, r7, cr15, cr3, {3}
     968:	0065646f 	rsbeq	r6, r5, pc, ror #8
     96c:	61705f5f 	cmnvs	r0, pc, asr pc
     970:	5f003164 	svcpl	0x00003164
     974:	6461705f 	strbtvs	r7, [r1], #-95	; 0xffffffa1
     978:	5f5f0032 	svcpl	0x005f0032
     97c:	33646170 	cmncc	r4, #112, 2
     980:	705f5f00 	subsvc	r5, pc, r0, lsl #30
     984:	00346461 	eorseq	r6, r4, r1, ror #8
     988:	61705f5f 	cmnvs	r0, pc, asr pc
     98c:	5f003564 	svcpl	0x00003564
     990:	73756e75 	cmnvc	r5, #1872	; 0x750
     994:	00326465 	eorseq	r6, r2, r5, ror #8
     998:	65647473 	strbvs	r7, [r4, #-1139]!	; 0xfffffb8d
     99c:	42007272 	andmi	r7, r0, #536870919	; 0x20000007
     9a0:	454b414c 	strbmi	r4, [fp, #-332]	; 0xfffffeb4
     9a4:	4b5f4232 	blmi	17d1274 <ringBuffer+0x177956c>
     9a8:	59425945 	stmdbpl	r2, {r0, r2, r6, r8, fp, ip, lr}^
     9ac:	00534554 	subseq	r4, r3, r4, asr r5
     9b0:	6b616c62 	blvs	185bb40 <ringBuffer+0x1803e38>
     9b4:	2d733265 	lfmcs	f3, 2, [r3, #-404]!	; 0xfffffe6c
     9b8:	2e666572 	mcrcs	5, 3, r6, cr6, cr2, {3}
     9bc:	69750063 	ldmdbvs	r5!, {r0, r1, r5, r6}^
     9c0:	5f38746e 	svcpl	0x0038746e
     9c4:	495f0074 	ldmdbmi	pc, {r2, r4, r5, r6}^	; <UNPREDICTABLE>
     9c8:	61625f4f 	cmnvs	r2, pc, asr #30
     9cc:	70756b63 	rsbsvc	r6, r5, r3, ror #22
     9d0:	7361625f 	cmnvc	r1, #-268435451	; 0xf0000005
     9d4:	6c620065 	stclvs	0, cr0, [r2], #-404	; 0xfffffe6c
     9d8:	32656b61 	rsbcc	r6, r5, #99328	; 0x18400
     9dc:	74735f73 	ldrbtvc	r5, [r3], #-3955	; 0xfffff08d
     9e0:	00657461 	rsbeq	r7, r5, r1, ror #8
     9e4:	4b414c42 	blmi	1053af4 <ringBuffer+0xffbdec>
     9e8:	5f423245 	svcpl	0x00423245
     9ec:	53524550 	cmppl	r2, #80, 10	; 0x14000000
     9f0:	4c414e4f 	mcrrmi	14, 4, r4, r1, cr15
     9f4:	45545942 	ldrbmi	r5, [r4, #-2370]	; 0xfffff6be
     9f8:	6c620053 	stclvs	0, cr0, [r2], #-332	; 0xfffffeb4
     9fc:	32656b61 	rsbcc	r6, r5, #99328	; 0x18400
     a00:	6f635f73 	svcvs	0x00635f73
     a04:	6174736e 	cmnvs	r4, lr, ror #6
     a08:	6f00746e 	svcvs	0x0000746e
     a0c:	656c7475 	strbvs	r7, [ip, #-1141]!	; 0xfffffb8b
     a10:	7473006e 	ldrbtvc	r0, [r3], #-110	; 0xffffff92
     a14:	3165726f 	cmncc	r5, pc, ror #4
     a18:	6c620036 	stclvs	0, cr0, [r2], #-216	; 0xffffff28
     a1c:	32656b61 	rsbcc	r6, r5, #99328	; 0x18400
     a20:	70755f73 	rsbsvc	r5, r5, r3, ror pc
     a24:	65746164 	ldrbvs	r6, [r4, #-356]!	; 0xfffffe9c
     a28:	4f495f00 	svcmi	0x00495f00
     a2c:	6972775f 	ldmdbvs	r2!, {r0, r1, r2, r3, r4, r6, r8, r9, sl, ip, sp, lr}^
     a30:	625f6574 	subsvs	r6, pc, #116, 10	; 0x1d000000
     a34:	00657361 	rsbeq	r7, r5, r1, ror #6
     a38:	7466656c 	strbtvc	r6, [r6], #-1388	; 0xfffffa94
     a3c:	554e4700 	strbpl	r4, [lr, #-1792]	; 0xfffff900
     a40:	31314320 	teqcc	r1, r0, lsr #6
     a44:	322e3620 	eorcc	r3, lr, #32, 12	; 0x2000000
     a48:	3220312e 	eorcc	r3, r0, #-2147483637	; 0x8000000b
     a4c:	31363130 	teqcc	r6, r0, lsr r1
     a50:	20363130 	eorscs	r3, r6, r0, lsr r1
     a54:	6c666d2d 	stclvs	13, cr6, [r6], #-180	; 0xffffff4c
     a58:	2d74616f 	ldfcse	f6, [r4, #-444]!	; 0xfffffe44
     a5c:	3d696261 	sfmcc	f6, 2, [r9, #-388]!	; 0xfffffe7c
     a60:	64726168 	ldrbtvs	r6, [r2], #-360	; 0xfffffe98
     a64:	666d2d20 	strbtvs	r2, [sp], -r0, lsr #26
     a68:	74616f6c 	strbtvc	r6, [r1], #-3948	; 0xfffff094
     a6c:	6962612d 	stmdbvs	r2!, {r0, r2, r3, r5, r8, sp, lr}^
     a70:	7261683d 	rsbvc	r6, r1, #3997696	; 0x3d0000
     a74:	6d2d2064 	stcvs	0, cr2, [sp, #-400]!	; 0xfffffe70
     a78:	68637261 	stmdavs	r3!, {r0, r5, r6, r9, ip, sp, lr}^
     a7c:	6d72613d 	ldfvse	f6, [r2, #-244]!	; 0xffffff0c
     a80:	612d3776 			; <UNDEFINED> instruction: 0x612d3776
     a84:	746d2d20 	strbtvc	r2, [sp], #-3360	; 0xfffff2e0
     a88:	3d656e75 	stclcc	14, cr6, [r5, #-468]!	; 0xfffffe2c
     a8c:	74726f63 	ldrbtvc	r6, [r2], #-3939	; 0xfffff09d
     a90:	612d7865 			; <UNDEFINED> instruction: 0x612d7865
     a94:	6d2d2039 	stcvs	0, cr2, [sp, #-228]!	; 0xffffff1c
     a98:	3d757066 	ldclcc	0, cr7, [r5, #-408]!	; 0xfffffe68
     a9c:	76706676 			; <UNDEFINED> instruction: 0x76706676
     aa0:	31642d33 	cmncc	r4, r3, lsr sp
     aa4:	6d2d2036 	stcvs	0, cr2, [sp, #-216]!	; 0xffffff28
     aa8:	6d756874 	ldclvs	8, cr6, [r5, #-464]!	; 0xfffffe30
     aac:	6d2d2062 	stcvs	0, cr2, [sp, #-392]!	; 0xfffffe78
     ab0:	2d736c74 	ldclcs	12, cr6, [r3, #-464]!	; 0xfffffe30
     ab4:	6c616964 			; <UNDEFINED> instruction: 0x6c616964
     ab8:	3d746365 	ldclcc	3, cr6, [r4, #-404]!	; 0xfffffe6c
     abc:	20756e67 	rsbscs	r6, r5, r7, ror #28
     ac0:	2d20672d 	stccs	7, cr6, [r0, #-180]!	; 0xffffff4c
     ac4:	2d20304f 	stccs	0, cr3, [r0, #-316]!	; 0xfffffec4
     ac8:	2d20304f 	stccs	0, cr3, [r0, #-316]!	; 0xfffffec4
     acc:	43495066 	movtmi	r5, #36966	; 0x9066
     ad0:	414c4200 	mrsmi	r4, (UNDEF: 108)
     ad4:	4232454b 	eorsmi	r4, r2, #314572800	; 0x12c00000
     ad8:	54554f5f 	ldrbpl	r4, [r5], #-3935	; 0xfffff0a1
     adc:	45545942 	ldrbmi	r5, [r4, #-2370]	; 0xfffff6be
     ae0:	5f5f0053 	svcpl	0x005f0053
     ae4:	6d6f7461 	cfstrdvs	mvd7, [pc, #-388]!	; 968 <_init-0x101b8>
     ae8:	6c5f6369 	mrrcvs	3, 6, r6, pc, cr9	; <UNPREDICTABLE>
     aec:	5f64616f 	svcpl	0x0064616f
     af0:	00706d74 	rsbseq	r6, r0, r4, ror sp
     af4:	20554e47 	subscs	r4, r5, r7, asr #28
     af8:	20313143 	eorscs	r3, r1, r3, asr #2
     afc:	2e322e36 	mrccs	14, 1, r2, cr2, cr6, {1}
     b00:	30322031 	eorscc	r2, r2, r1, lsr r0
     b04:	30313631 	eorscc	r3, r1, r1, lsr r6
     b08:	2d203631 	stccs	6, cr3, [r0, #-196]!	; 0xffffff3c
     b0c:	6f6c666d 	svcvs	0x006c666d
     b10:	612d7461 			; <UNDEFINED> instruction: 0x612d7461
     b14:	683d6962 	ldmdavs	sp!, {r1, r5, r6, r8, fp, sp, lr}
     b18:	20647261 	rsbcs	r7, r4, r1, ror #4
     b1c:	72616d2d 	rsbvc	r6, r1, #2880	; 0xb40
     b20:	613d6863 	teqvs	sp, r3, ror #16
     b24:	37766d72 			; <UNDEFINED> instruction: 0x37766d72
     b28:	2d20612d 	stfcss	f6, [r0, #-180]!	; 0xffffff4c
     b2c:	6e75746d 	cdpvs	4, 7, cr7, cr5, cr13, {3}
     b30:	6f633d65 	svcvs	0x00633d65
     b34:	78657472 	stmdavc	r5!, {r1, r4, r5, r6, sl, ip, sp, lr}^
     b38:	2039612d 	eorscs	r6, r9, sp, lsr #2
     b3c:	70666d2d 	rsbvc	r6, r6, sp, lsr #26
     b40:	66763d75 			; <UNDEFINED> instruction: 0x66763d75
     b44:	2d337670 	ldccs	6, cr7, [r3, #-448]!	; 0xfffffe40
     b48:	20363164 	eorscs	r3, r6, r4, ror #2
     b4c:	68746d2d 	ldmdavs	r4!, {r0, r2, r3, r5, r8, sl, fp, sp, lr}^
     b50:	20626d75 	rsbcs	r6, r2, r5, ror sp
     b54:	6c746d2d 	ldclvs	13, cr6, [r4], #-180	; 0xffffff4c
     b58:	69642d73 	stmdbvs	r4!, {r0, r1, r4, r5, r6, r8, sl, fp, sp}^
     b5c:	63656c61 	cmnvs	r5, #24832	; 0x6100
     b60:	6e673d74 	mcrvs	13, 3, r3, cr7, cr4, {3}
     b64:	672d2075 			; <UNDEFINED> instruction: 0x672d2075
     b68:	304f2d20 	subcc	r2, pc, r0, lsr #26
     b6c:	50662d20 	rsbpl	r2, r6, r0, lsr #26
     b70:	2d204349 	stccs	3, cr4, [r0, #-292]!	; 0xfffffedc
     b74:	78696666 	stmdavc	r9!, {r1, r2, r5, r6, r9, sl, sp, lr}^
     b78:	722d6465 	eorvc	r6, sp, #1694498816	; 0x65000000
     b7c:	5f630038 	svcpl	0x00630038
     b80:	65726964 	ldrbvs	r6, [r2, #-2404]!	; 0xfffff69c
     b84:	745f7463 	ldrbvc	r7, [pc], #-1123	; b8c <_init-0xff94>
     b88:	725f6673 	subsvc	r6, pc, #120586240	; 0x7300000
     b8c:	726f6365 	rsbvc	r6, pc, #-1811939327	; 0x94000001
     b90:	676e6964 	strbvs	r6, [lr, -r4, ror #18]!
     b94:	42736900 	rsbsmi	r6, r3, #0, 18
     b98:	636e6172 	cmnvs	lr, #-2147483620	; 0x8000001c
     b9c:	6b615468 	blvs	1855d44 <ringBuffer+0x17fe03c>
     ba0:	69006e65 	stmdbvs	r0, {r0, r2, r5, r6, r9, sl, fp, sp, lr}
     ba4:	6d655f73 	stclvs	15, cr5, [r5, #-460]!	; 0xfffffe34
     ba8:	00797470 	rsbseq	r7, r9, r0, ror r4
     bac:	5f766663 	svcpl	0x00766663
     bb0:	6c616369 	stclvs	3, cr6, [r1], #-420	; 0xfffffe5c
     bb4:	63625f6c 	cmnvs	r2, #108, 30	; 0x1b0
     bb8:	636c625f 	cmnvs	ip, #-268435451	; 0xf0000005
     bbc:	61726200 	cmnvs	r2, r0, lsl #4
     bc0:	5f68636e 	svcpl	0x0068636e
     bc4:	656b6174 	strbvs	r6, [fp, #-372]!	; 0xfffffe8c
     bc8:	5f63006e 	svcpl	0x0063006e
     bcc:	5f667374 	svcpl	0x00667374
     bd0:	6c5f7862 	mrrcvs	8, 6, r7, pc, cr2	; <UNPREDICTABLE>
     bd4:	65725f72 	ldrbvs	r5, [r2, #-3954]!	; 0xfffff08e
     bd8:	64726f63 	ldrbtvs	r6, [r2], #-3939	; 0xfffff09d
     bdc:	00676e69 	rsbeq	r6, r7, r9, ror #28
     be0:	74736564 	ldrbtvc	r6, [r3], #-1380	; 0xfffffa9c
     be4:	72646441 	rsbvc	r6, r4, #1090519040	; 0x41000000
     be8:	76666300 	strbtvc	r6, [r6], -r0, lsl #6
     bec:	6163695f 	cmnvs	r3, pc, asr r9
     bf0:	625f6c6c 	subsvs	r6, pc, #108, 24	; 0x6c00
     bf4:	705f786c 	subsvc	r7, pc, ip, ror #16
     bf8:	74006572 	strvc	r6, [r0], #-1394	; 0xfffffa8e
     bfc:	5f747365 	svcpl	0x00747365
     c00:	5f647766 	svcpl	0x00647766
     c04:	69646e69 	stmdbvs	r4!, {r0, r3, r5, r6, r9, sl, fp, sp, lr}^
     c08:	74636572 	strbtvc	r6, [r3], #-1394	; 0xfffffa8e
     c0c:	6673745f 			; <UNDEFINED> instruction: 0x6673745f
     c10:	656c6500 	strbvs	r6, [ip, #-1280]!	; 0xfffffb00
     c14:	6e00316d 	adfvssz	f3, f0, #5.0
     c18:	5f747865 	svcpl	0x00747865
     c1c:	5f747369 	svcpl	0x00747369
     c20:	735f6f74 	cmpvc	pc, #116, 30	; 0x1d0
     c24:	6372756f 	cmnvs	r2, #465567744	; 0x1bc00000
     c28:	5f5f0065 	svcpl	0x005f0065
     c2c:	6d6f7461 	cfstrdvs	mvd7, [pc, #-388]!	; ab0 <_init-0x10070>
     c30:	735f6369 	cmpvc	pc, #-1543503871	; 0xa4000001
     c34:	65726f74 	ldrbvs	r6, [r2, #-3956]!	; 0xfffff08c
     c38:	7274705f 	rsbsvc	r7, r4, #95	; 0x5f
     c3c:	73757000 	cmnvc	r5, #0
     c40:	6f630068 	svcvs	0x00630068
     c44:	5f00646e 	svcpl	0x0000646e
     c48:	6f74615f 	svcvs	0x0074615f
     c4c:	5f63696d 	svcpl	0x0063696d
     c50:	726f7473 	rsbvc	r7, pc, #1929379840	; 0x73000000
     c54:	6d745f65 	ldclvs	15, cr5, [r4, #-404]!	; 0xfffffe6c
     c58:	656e0070 	strbvs	r0, [lr, #-112]!	; 0xffffff90
     c5c:	685f7478 	ldmdavs	pc, {r3, r4, r5, r6, sl, ip, sp, lr}^	; <UNPREDICTABLE>
     c60:	00646165 	rsbeq	r6, r4, r5, ror #2
     c64:	5f766663 	svcpl	0x00766663
     c68:	6c616369 	stclvs	3, cr6, [r1], #-420	; 0xfffffe5c
     c6c:	646c5f6c 	strbtvs	r5, [ip], #-3948	; 0xfffff094
     c70:	5f61696d 	svcpl	0x0061696d
     c74:	00746572 	rsbseq	r6, r4, r2, ror r5
     c78:	676e6972 			; <UNDEFINED> instruction: 0x676e6972
     c7c:	66667562 	strbtvs	r7, [r6], -r2, ror #10
     c80:	695f7265 	ldmdbvs	pc, {r0, r2, r5, r6, r9, ip, sp, lr}^	; <UNPREDICTABLE>
     c84:	0074696e 	rsbseq	r6, r4, lr, ror #18
     c88:	6d656c65 	stclvs	12, cr6, [r5, #-404]!	; 0xfffffe6c
     c8c:	656c4500 	strbvs	r4, [ip, #-1280]!	; 0xfffffb00
     c90:	746e656d 	strbtvc	r6, [lr], #-1389	; 0xfffffa93
     c94:	61657200 	cmnvs	r5, r0, lsl #4
     c98:	38725f64 	ldmdacc	r2!, {r2, r5, r6, r8, r9, sl, fp, ip, lr}^
     c9c:	6e695200 	cdpvs	2, 6, cr5, cr9, cr0, {0}
     ca0:	66754267 	ldrbtvs	r4, [r5], -r7, ror #4
     ca4:	00726566 	rsbseq	r6, r2, r6, ror #10
     ca8:	65707954 	ldrbvs	r7, [r0, #-2388]!	; 0xfffff6ac
     cac:	745f6300 	ldrbvc	r6, [pc], #-768	; cb4 <_init-0xfe6c>
     cb0:	705f6673 	subsvc	r6, pc, r3, ror r6	; <UNPREDICTABLE>
     cb4:	705f706f 	subsvc	r7, pc, pc, rrx
     cb8:	65725f63 	ldrbvs	r5, [r2, #-3939]!	; 0xfffff09d
     cbc:	64726f63 	ldrbtvs	r6, [r2], #-3939	; 0xfffff09d
     cc0:	00676e69 	rsbeq	r6, r7, r9, ror #28
     cc4:	6e695f63 	cdpvs	15, 6, cr5, cr9, cr3, {3}
     cc8:	65726964 	ldrbvs	r6, [r2, #-2404]!	; 0xfffff69c
     ccc:	745f7463 	ldrbvc	r7, [pc], #-1123	; cd4 <_init-0xfe4c>
     cd0:	725f6673 	subsvc	r6, pc, #120586240	; 0x7300000
     cd4:	726f6365 	rsbvc	r6, pc, #-1811939327	; 0x94000001
     cd8:	676e6964 	strbvs	r6, [lr, -r4, ror #18]!
     cdc:	72756300 	rsbsvc	r6, r5, #0, 6
     ce0:	746e6572 	strbtvc	r6, [lr], #-1394	; 0xfffffa8e
     ce4:	7470635f 	ldrbtvc	r6, [r0], #-863	; 0xfffffca1
     ce8:	0064695f 	rsbeq	r6, r4, pc, asr r9
     cec:	646e6f43 	strbtvs	r6, [lr], #-3907	; 0xfffff0bd
     cf0:	65646f43 	strbvs	r6, [r4, #-3907]!	; 0xfffff0bd
     cf4:	72650073 	rsbvc	r0, r5, #115	; 0x73
     cf8:	5f726f72 	svcpl	0x00726f72
     cfc:	6e756f66 	cdpvs	15, 7, cr6, cr5, cr6, {3}
     d00:	69720064 	ldmdbvs	r2!, {r2, r5, r6}^
     d04:	7562676e 	strbvc	r6, [r2, #-1902]!	; 0xfffff892
     d08:	72656666 	rsbvc	r6, r5, #106954752	; 0x6600000
     d0c:	696e695f 	stmdbvs	lr!, {r0, r1, r2, r3, r4, r6, r8, fp, sp, lr}^
     d10:	6c665f74 	stclvs	15, cr5, [r6], #-464	; 0xfffffe30
     d14:	63006761 	movwvs	r6, #1889	; 0x761
     d18:	00727370 	rsbseq	r7, r2, r0, ror r3
     d1c:	69645f63 	stmdbvs	r4!, {r0, r1, r5, r6, r8, r9, sl, fp, ip, lr}^
     d20:	74636572 	strbtvc	r6, [r3], #-1394	; 0xfffffa8e
     d24:	6673745f 			; <UNDEFINED> instruction: 0x6673745f
     d28:	5f63635f 	svcpl	0x0063635f
     d2c:	6f636572 	svcvs	0x00636572
     d30:	6e696472 	mcrvs	4, 3, r6, cr9, cr2, {3}
     d34:	61740067 	cmnvs	r4, r7, rrx
     d38:	2e006c69 	cdpcs	12, 0, cr6, cr0, cr9, {3}
     d3c:	2e2e2f2e 	cdpcs	15, 2, cr2, cr14, cr14, {1}
     d40:	6172742f 	cmnvs	r2, pc, lsr #8
     d44:	6c6f706d 	stclvs	0, cr7, [pc], #-436	; b98 <_init-0xff88>
     d48:	5f656e69 	svcpl	0x00656e69
     d4c:	2f62696c 	svccs	0x0062696c
     d50:	5f746369 	svcpl	0x00746369
     d54:	63656863 	cmnvs	r5, #6488064	; 0x630000
     d58:	676e696b 	strbvs	r6, [lr, -fp, ror #18]!
     d5c:	6300632e 	movwvs	r6, #814	; 0x32e
     d60:	5f646e6f 	svcpl	0x00646e6f
     d64:	65707974 	ldrbvs	r7, [r0, #-2420]!	; 0xfffff68c
     d68:	5f387200 	svcpl	0x00387200
     d6c:	756c6176 	strbvc	r6, [ip, #-374]!	; 0xfffffe8a
     d70:	5f5f0065 	svcpl	0x005f0065
     d74:	6d6f7461 	cfstrdvs	mvd7, [pc, #-388]!	; bf8 <_init-0xff28>
     d78:	6c5f6369 	mrrcvs	3, 6, r6, pc, cr9	; <UNPREDICTABLE>
     d7c:	5f64616f 	svcpl	0x0064616f
     d80:	00727470 	rsbseq	r7, r2, r0, ror r4
     d84:	5f766663 	svcpl	0x00766663
     d88:	6c616369 	stclvs	3, cr6, [r1], #-420	; 0xfffffe5c
     d8c:	6c625f6c 	stclvs	15, cr5, [r2], #-432	; 0xfffffe50
     d90:	72730078 	rsbsvc	r0, r3, #120	; 0x78
     d94:	64644163 	strbtvs	r4, [r4], #-355	; 0xfffffe9d
     d98:	69720072 	ldmdbvs	r2!, {r1, r4, r5, r6}^
     d9c:	7542676e 	strbvc	r6, [r2, #-1902]	; 0xfffff892
     da0:	72656666 	rsbvc	r6, r5, #106954752	; 0x6600000
     da4:	645f6300 	ldrbvs	r6, [pc], #-768	; dac <_init-0xfd74>
     da8:	63657269 	cmnvs	r5, #-1879048186	; 0x90000006
     dac:	73745f74 	cmnvc	r4, #116, 30	; 0x1d0
     db0:	63625f66 	cmnvs	r2, #408	; 0x198
     db4:	65725f63 	ldrbvs	r5, [r2, #-3939]!	; 0xfffff09d
     db8:	64726f63 	ldrbtvs	r6, [r2], #-3939	; 0xfffff09d
     dbc:	00676e69 	rsbeq	r6, r7, r9, ror #28
     dc0:	5f746369 	svcpl	0x00746369
     dc4:	63656863 	cmnvs	r5, #6488064	; 0x630000
     dc8:	676e696b 	strbvs	r6, [lr, -fp, ror #18]!
     dcc:	6f6c6300 	svcvs	0x006c6300
     dd0:	65536b63 	ldrbvs	r6, [r3, #-2915]	; 0xfffff49d
     dd4:	646e4171 	strbtvs	r4, [lr], #-369	; 0xfffffe8f
     dd8:	65646f4e 	strbvs	r6, [r4, #-3918]!	; 0xfffff0b2
     ddc:	6d656d00 	stclvs	13, cr6, [r5, #-0]
     de0:	00666572 	rsbeq	r6, r6, r2, ror r5
     de4:	43454554 	movtmi	r4, #21844	; 0x5554
     de8:	6e6f435f 	mcrvs	3, 3, r4, cr15, cr15, {2}
     dec:	74786574 	ldrbtvc	r6, [r8], #-1396	; 0xfffffa8c
     df0:	6e697500 	cdpvs	5, 6, cr7, cr9, cr0, {0}
     df4:	5f343674 	svcpl	0x00343674
     df8:	72700074 	rsbsvc	r0, r0, #116	; 0x74
     dfc:	5f746e69 	svcpl	0x00746e69
     e00:	68736168 	ldmdavs	r3!, {r3, r5, r6, r8, sp, lr}^
     e04:	74657200 	strbtvc	r7, [r5], #-512	; 0xfffffe00
     e08:	6365725f 	cmnvs	r5, #-268435451	; 0xf0000005
     e0c:	6964726f 	stmdbvs	r4!, {r0, r1, r2, r3, r5, r6, r9, ip, sp, lr}^
     e10:	665f676e 	ldrbvs	r6, [pc], -lr, ror #14
     e14:	73696e69 	cmnvc	r9, #1680	; 0x690
     e18:	69760068 	ldmdbvs	r6!, {r3, r5, r6}^
     e1c:	735f7765 	cmpvc	pc, #26476544	; 0x1940000
     e20:	63746977 	cmnvs	r4, #1949696	; 0x1dc000
     e24:	6f745f68 	svcvs	0x00745f68
     e28:	7865745f 	stmdavc	r5!, {r0, r1, r2, r3, r4, r6, sl, ip, sp, lr}^
     e2c:	6e615f74 	mcrvs	15, 3, r5, cr1, cr4, {3}
     e30:	6f6c5f64 	svcvs	0x006c5f64
     e34:	74730067 	ldrbtvc	r0, [r3], #-103	; 0xffffff99
     e38:	65747261 	ldrbvs	r7, [r4, #-609]!	; 0xfffffd9f
     e3c:	69660064 	stmdbvs	r6!, {r2, r5, r6}^
     e40:	616e656c 	cmnvs	lr, ip, ror #10
     e44:	0032656d 	eorseq	r6, r2, sp, ror #10
     e48:	73736573 	cmnvc	r3, #482344960	; 0x1cc00000
     e4c:	5f6e6f69 	svcpl	0x006e6f69
     e50:	74006469 	strvc	r6, [r0], #-1129	; 0xfffffb97
     e54:	48656d69 	stmdami	r5!, {r0, r3, r5, r6, r8, sl, fp, sp, lr}^
     e58:	646e4169 	strbtvs	r4, [lr], #-361	; 0xfffffe97
     e5c:	73726556 	cmnvc	r2, #360710144	; 0x15800000
     e60:	006e6f69 	rsbeq	r6, lr, r9, ror #30
     e64:	69745f5f 	ldmdbvs	r4!, {r0, r1, r2, r3, r4, r6, r8, r9, sl, fp, ip, lr}^
     e68:	6f7a656d 	svcvs	0x007a656d
     e6c:	7600656e 	strvc	r6, [r0], -lr, ror #10
     e70:	5f776569 	svcpl	0x00776569
     e74:	74697773 	strbtvc	r7, [r9], #-1907	; 0xfffff88d
     e78:	745f6863 	ldrbvc	r6, [pc], #-2147	; e80 <_init-0xfca0>
     e7c:	64725f6f 	ldrbtvs	r5, [r2], #-3951	; 0xfffff091
     e80:	646e615f 	strbtvs	r6, [lr], #-351	; 0xfffffea1
     e84:	676f6c5f 			; <UNDEFINED> instruction: 0x676f6c5f
     e88:	6e756600 	cdpvs	6, 7, cr6, cr5, cr0, {0}
     e8c:	6f697463 	svcvs	0x00697463
     e90:	6170006e 	cmnvs	r0, lr, rrx
     e94:	546d6172 	strbtpl	r6, [sp], #-370	; 0xfffffe8e
     e98:	73657079 	cmnvc	r5, #121	; 0x79
     e9c:	72617000 	rsbvc	r7, r1, #0
     ea0:	00746e65 	rsbseq	r6, r4, r5, ror #28
     ea4:	61727261 	cmnvs	r2, r1, ror #4
     ea8:	69735f79 	ldmdbvs	r3!, {r0, r3, r4, r5, r6, r8, r9, sl, fp, ip, lr}^
     eac:	7300657a 	movwvc	r6, #1402	; 0x57a
     eb0:	00737365 	rsbseq	r7, r3, r5, ror #6
     eb4:	2e2f2e2e 	cdpcs	14, 2, cr2, cr15, cr14, {1}
     eb8:	72742f2e 	rsbsvc	r2, r4, #46, 30	; 0xb8
     ebc:	6f706d61 	svcvs	0x00706d61
     ec0:	656e696c 	strbvs	r6, [lr, #-2412]!	; 0xfffff694
     ec4:	62696c5f 	rsbvs	r6, r9, #24320	; 0x5f00
     ec8:	5f61742f 	svcpl	0x0061742f
     ecc:	6d617274 	sfmvs	f7, 2, [r1, #-464]!	; 0xfffffe30
     ed0:	696c6f70 	stmdbvs	ip!, {r4, r5, r6, r8, r9, sl, fp, sp, lr}^
     ed4:	632e656e 			; <UNDEFINED> instruction: 0x632e656e
     ed8:	45455400 	strbmi	r5, [r5, #-1024]	; 0xfffffc00
     edc:	55555f43 	ldrbpl	r5, [r5, #-3907]	; 0xfffff0bd
     ee0:	65004449 	strvs	r4, [r0, #-1097]	; 0xfffffbb7
     ee4:	6f5f7272 	svcvs	0x005f7272
     ee8:	69676972 	stmdbvs	r7!, {r1, r4, r5, r6, r8, fp, sp, lr}^
     eec:	7261006e 	rsbvc	r0, r1, #110	; 0x6e
     ef0:	00796172 	rsbseq	r6, r9, r2, ror r1
     ef4:	6f5f6472 	svcvs	0x005f6472
     ef8:	65657470 	strbvs	r7, [r5, #-1136]!	; 0xfffffb90
     efc:	696e695f 	stmdbvs	lr!, {r0, r1, r2, r3, r4, r6, r8, fp, sp, lr}^
     f00:	756e0074 	strbvc	r0, [lr, #-116]!	; 0xffffff8c
     f04:	7265626d 	rsbvc	r6, r5, #-805306362	; 0xd0000006
     f08:	74706f00 	ldrbtvc	r6, [r0], #-3840	; 0xfffff100
     f0c:	00677261 	rsbeq	r7, r7, r1, ror #4
     f10:	74697277 	strbtvc	r7, [r9], #-631	; 0xfffffd89
     f14:	72615f65 	rsbvc	r5, r1, #404	; 0x194
     f18:	5f796172 	svcpl	0x00796172
     f1c:	665f6f74 	usub16vs	r6, pc, r4	; <UNPREDICTABLE>
     f20:	00656c69 	rsbeq	r6, r5, r9, ror #24
     f24:	72617473 	rsbvc	r7, r1, #1929379840	; 0x73000000
     f28:	656e5f74 	strbvs	r5, [lr, #-3956]!	; 0xfffff08c
     f2c:	68745f77 	ldmdavs	r4!, {r0, r1, r2, r4, r5, r6, r8, r9, sl, fp, ip, lr}^
     f30:	64616572 	strbtvs	r6, [r1], #-1394	; 0xfffffa8e
     f34:	665f5f00 	ldrbvs	r5, [pc], -r0, lsl #30
     f38:	5f656572 	svcpl	0x00656572
     f3c:	6b6f6f68 	blvs	1bdcce4 <ringBuffer+0x1b84fdc>
     f40:	65726300 	ldrbvs	r6, [r2, #-768]!	; 0xfffffd00
     f44:	5f657461 	svcpl	0x00657461
     f48:	656c6966 	strbvs	r6, [ip, #-2406]!	; 0xfffff69a
     f4c:	65640073 	strbvs	r0, [r4, #-115]!	; 0xffffff8d
     f50:	6e697473 	mcrvs	4, 3, r7, cr9, cr3, {3}
     f54:	6f697461 	svcvs	0x00697461
     f58:	4554006e 	ldrbmi	r0, [r4, #-110]	; 0xffffff92
     f5c:	565f4345 	ldrbpl	r4, [pc], -r5, asr #6
     f60:	65756c61 	ldrbvs	r6, [r5, #-3169]!	; 0xfffff39f
     f64:	745f5f00 	ldrbvc	r5, [pc], #-3840	; f6c <_init-0xfbb4>
     f68:	725f6673 	subsvc	r6, pc, #120586240	; 0x7300000
     f6c:	726f6365 	rsbvc	r6, pc, #-1811939327	; 0x94000001
     f70:	676e6964 	strbvs	r6, [lr, -r4, ror #18]!
     f74:	67657200 	strbvs	r7, [r5, -r0, lsl #4]!
     f78:	65747369 	ldrbvs	r7, [r4, #-873]!	; 0xfffffc97
     f7c:	5f646572 	svcpl	0x00646572
     f80:	77006466 	strvc	r6, [r0, -r6, ror #8]
     f84:	65746972 	ldrbvs	r6, [r4, #-2418]!	; 0xfffff68e
     f88:	6f77745f 	svcvs	0x0077745f
     f8c:	6d756e5f 	ldclvs	14, cr6, [r5, #-380]!	; 0xfffffe84
     f90:	73726562 	cmnvc	r2, #411041792	; 0x18800000
     f94:	5f6f745f 	svcpl	0x006f745f
     f98:	656c6966 	strbvs	r6, [ip, #-2406]!	; 0xfffff69a
     f9c:	45455400 	strbmi	r5, [r5, #-1024]	; 0xfffffc00
     fa0:	704f5f43 	subvc	r5, pc, r3, asr #30
     fa4:	74617265 	strbtvc	r7, [r1], #-613	; 0xfffffd9b
     fa8:	006e6f69 	rsbeq	r6, lr, r9, ror #30
     fac:	6f766e69 	svcvs	0x00766e69
     fb0:	635f656b 	cmpvs	pc, #448790528	; 0x1ac00000
     fb4:	7700746e 	strvc	r7, [r0, -lr, ror #8]
     fb8:	65746972 	ldrbvs	r6, [r4, #-2418]!	; 0xfffff68e
     fbc:	6d756e5f 	ldclvs	14, cr6, [r5, #-380]!	; 0xfffffe84
     fc0:	5f726562 	svcpl	0x00726562
     fc4:	665f6f74 	usub16vs	r6, pc, r4	; <UNPREDICTABLE>
     fc8:	00656c69 	rsbeq	r6, r5, r9, ror #24
     fcc:	5f676572 	svcpl	0x00676572
     fd0:	006d656d 	rsbeq	r6, sp, sp, ror #10
     fd4:	64727470 	ldrbtvs	r7, [r2], #-1136	; 0xfffffb90
     fd8:	5f666669 	svcpl	0x00666669
     fdc:	75620074 	strbvc	r0, [r2, #-116]!	; 0xffffff8c
     fe0:	72656666 	rsbvc	r6, r5, #106954752	; 0x6600000
     fe4:	6c6c615f 	stfvse	f6, [ip], #-380	; 0xfffffe84
     fe8:	7461636f 	strbtvc	r6, [r1], #-879	; 0xfffffc91
     fec:	5f006465 	svcpl	0x00006465
     ff0:	6c616d5f 	stclvs	13, cr6, [r1], #-380	; 0xfffffe84
     ff4:	5f636f6c 	svcpl	0x00636f6c
     ff8:	6b6f6f68 	blvs	1bdcda0 <ringBuffer+0x1b85098>
     ffc:	6c696600 	stclvs	6, cr6, [r9], #-0
    1000:	6d616e65 	stclvs	14, cr6, [r1, #-404]!	; 0xfffffe6c
    1004:	706f0065 	rsbvc	r0, pc, r5, rrx
    1008:	646e6974 	strbtvs	r6, [lr], #-2420	; 0xfffff68c
    100c:	74657200 	strbtvc	r7, [r5], #-512	; 0xfffffe00
    1010:	7361685f 	cmnvc	r1, #6225920	; 0x5f0000
    1014:	6e695f68 	cdpvs	15, 6, cr5, cr9, cr8, {3}
    1018:	665f7469 	ldrbvs	r7, [pc], -r9, ror #8
    101c:	0067616c 	rsbeq	r6, r7, ip, ror #2
    1020:	7379735f 	cmnvc	r9, #2080374785	; 0x7c000001
    1024:	6769735f 			; <UNDEFINED> instruction: 0x6769735f
    1028:	7473696c 	ldrbtvc	r6, [r3], #-2412	; 0xfffff694
    102c:	6d756e00 	ldclvs	14, cr6, [r5, #-0]
    1030:	31726562 	cmncc	r2, r2, ror #10
    1034:	6d756e00 	ldclvs	14, cr6, [r5, #-0]
    1038:	32726562 	rsbscc	r6, r2, #411041792	; 0x18800000
    103c:	554e4700 	strbpl	r4, [lr, #-1792]	; 0xfffff900
    1040:	31314320 	teqcc	r1, r0, lsr #6
    1044:	322e3620 	eorcc	r3, lr, #32, 12	; 0x2000000
    1048:	3220312e 	eorcc	r3, r0, #-2147483637	; 0x8000000b
    104c:	31363130 	teqcc	r6, r0, lsr r1
    1050:	20363130 	eorscs	r3, r6, r0, lsr r1
    1054:	6c666d2d 	stclvs	13, cr6, [r6], #-180	; 0xffffff4c
    1058:	2d74616f 	ldfcse	f6, [r4, #-444]!	; 0xfffffe44
    105c:	3d696261 	sfmcc	f6, 2, [r9, #-388]!	; 0xfffffe7c
    1060:	64726168 	ldrbtvs	r6, [r2], #-360	; 0xfffffe98
    1064:	616d2d20 	cmnvs	sp, r0, lsr #26
    1068:	3d686372 	stclcc	3, cr6, [r8, #-456]!	; 0xfffffe38
    106c:	766d7261 	strbtvc	r7, [sp], -r1, ror #4
    1070:	20612d37 	rsbcs	r2, r1, r7, lsr sp
    1074:	75746d2d 	ldrbvc	r6, [r4, #-3373]!	; 0xfffff2d3
    1078:	633d656e 	teqvs	sp, #461373440	; 0x1b800000
    107c:	6574726f 	ldrbvs	r7, [r4, #-623]!	; 0xfffffd91
    1080:	39612d78 	stmdbcc	r1!, {r3, r4, r5, r6, r8, sl, fp, sp}^
    1084:	666d2d20 	strbtvs	r2, [sp], -r0, lsr #26
    1088:	763d7570 			; <UNDEFINED> instruction: 0x763d7570
    108c:	33767066 	cmncc	r6, #102	; 0x66
    1090:	3631642d 	ldrtcc	r6, [r1], -sp, lsr #8
    1094:	746d2d20 	strbtvc	r2, [sp], #-3360	; 0xfffff2e0
    1098:	626d7568 	rsbvs	r7, sp, #104, 10	; 0x1a000000
    109c:	746d2d20 	strbtvc	r2, [sp], #-3360	; 0xfffff2e0
    10a0:	642d736c 	strtvs	r7, [sp], #-876	; 0xfffffc94
    10a4:	656c6169 	strbvs	r6, [ip, #-361]!	; 0xfffffe97
    10a8:	673d7463 	ldrvs	r7, [sp, -r3, ror #8]!
    10ac:	2d20756e 	cfstr32cs	mvfx7, [r0, #-440]!	; 0xfffffe48
    10b0:	672d2067 	strvs	r2, [sp, -r7, rrx]!
    10b4:	72617764 	rsbvc	r7, r1, #100, 14	; 0x1900000
    10b8:	20352d66 	eorscs	r2, r5, r6, ror #26
    10bc:	20304f2d 	eorscs	r4, r0, sp, lsr #30
    10c0:	4950662d 	ldmdbmi	r0, {r0, r2, r3, r5, r9, sl, sp, lr}^
    10c4:	65730043 	ldrbvs	r0, [r3, #-67]!	; 0xffffffbd
    10c8:	6f697373 	svcvs	0x00697373
    10cc:	7572006e 	ldrbvc	r0, [r2, #-110]!	; 0xffffff92
    10d0:	68745f6e 	ldmdavs	r4!, {r1, r2, r3, r5, r6, r8, r9, sl, fp, ip, lr}^
    10d4:	64616572 	strbtvs	r6, [r1], #-1394	; 0xfffffa8e
    10d8:	655f5f00 	ldrbvs	r5, [pc, #-3840]	; 1e0 <_init-0x10940>
    10dc:	7269766e 	rsbvc	r7, r9, #115343360	; 0x6e00000
    10e0:	72006e6f 	andvc	r6, r0, #1776	; 0x6f0
    10e4:	5f646165 	svcpl	0x00646165
    10e8:	7361656d 	cmnvc	r1, #457179136	; 0x1b400000
    10ec:	6d657275 	sfmvs	f7, 2, [r5, #-468]!	; 0xfffffe2c
    10f0:	00746e65 	rsbseq	r6, r4, r5, ror #28
    10f4:	43454554 	movtmi	r4, #21844	; 0x5554
    10f8:	6168535f 	cmnvs	r8, pc, asr r3
    10fc:	4d646572 	cfstr64mi	mvdx6, [r4, #-456]!	; 0xfffffe38
    1100:	726f6d65 	rsbvc	r6, pc, #6464	; 0x1940
    1104:	45540079 	ldrbmi	r0, [r4, #-121]	; 0xffffff87
    1108:	505f4345 	subspl	r4, pc, r5, asr #6
    110c:	6d617261 	sfmvs	f7, 2, [r1, #-388]!	; 0xfffffe7c
    1110:	72657465 	rsbvc	r7, r5, #1694498816	; 0x65000000
    1114:	6c6c6100 	stfvse	f6, [ip], #-0
    1118:	6465636f 	strbtvs	r6, [r5], #-879	; 0xfffffc91
    111c:	7a69735f 	bvc	1a5dea0 <ringBuffer+0x1a06198>
    1120:	74700065 	ldrbtvc	r0, [r0], #-101	; 0xffffff9b
    1124:	61657268 	cmnvs	r5, r8, ror #4
    1128:	00745f64 	rsbseq	r5, r4, r4, ror #30
    112c:	72756f73 	rsbsvc	r6, r5, #460	; 0x1cc
    1130:	635f6563 	cmpvs	pc, #415236096	; 0x18c00000
    1134:	70007470 	andvc	r7, r0, r0, ror r4
    1138:	6570706f 	ldrbvs	r7, [r0, #-111]!	; 0xffffff91
    113c:	656c4564 	strbvs	r4, [ip, #-1380]!	; 0xfffffa9c
    1140:	6564006d 	strbvs	r0, [r4, #-109]!	; 0xffffff93
    1144:	635f7473 	cmpvs	pc, #1929379840	; 0x73000000
    1148:	5f007470 	svcpl	0x00007470
    114c:	6d656d5f 	stclvs	13, cr6, [r5, #-380]!	; 0xfffffe84
    1150:	67696c61 	strbvs	r6, [r9, -r1, ror #24]!
    1154:	6f685f6e 	svcvs	0x00685f6e
    1158:	63006b6f 	movwvs	r6, #2927	; 0xb6f
    115c:	69646e6f 	stmdbvs	r4!, {r0, r1, r2, r3, r5, r6, r9, sl, fp, sp, lr}^
    1160:	6e6f6974 			; <UNDEFINED> instruction: 0x6e6f6974
    1164:	725f5f00 	subsvc	r5, pc, #0, 30
    1168:	6c6c6165 	stfvse	f6, [ip], #-404	; 0xfffffe6c
    116c:	685f636f 	ldmdavs	pc, {r0, r1, r2, r3, r5, r6, r8, r9, sp, lr}^	; <UNPREDICTABLE>
    1170:	006b6f6f 	rsbeq	r6, fp, pc, ror #30
    1174:	6f635f5f 	svcvs	0x00635f5f
    1178:	7469646e 	strbtvc	r6, [r9], #-1134	; 0xfffffb92
    117c:	616e6f69 	cmnvs	lr, r9, ror #30
    1180:	72625f6c 	rsbvc	r5, r2, #108, 30	; 0x1b0
    1184:	68636e61 	stmdavs	r3!, {r0, r5, r6, r9, sl, fp, sp, lr}^
    1188:	6365725f 	cmnvs	r5, #-268435451	; 0xf0000005
    118c:	6964726f 	stmdbvs	r4!, {r0, r1, r2, r3, r5, r6, r9, ip, sp, lr}^
    1190:	5f00676e 	svcpl	0x0000676e
    1194:	7961645f 	stmdbvc	r1!, {r0, r1, r2, r3, r4, r6, sl, sp, lr}^
    1198:	6867696c 	stmdavs	r7!, {r2, r3, r5, r6, r8, fp, sp, lr}^
    119c:	706f0074 	rsbvc	r0, pc, r4, ror r0	; <UNPREDICTABLE>
    11a0:	74706f74 	ldrbtvc	r6, [r0], #-3956	; 0xfffff08c
    11a4:	6d756e00 	ldclvs	14, cr6, [r5, #-0]
    11a8:	5f726562 	svcpl	0x00726562
    11ac:	00727473 	rsbseq	r7, r2, r3, ror r4
    11b0:	5f656663 	svcpl	0x00656663
    11b4:	65707974 	ldrbvs	r7, [r0, #-2420]!	; 0xfffff68c
    11b8:	69757500 	ldmdbvs	r5!, {r8, sl, ip, sp, lr}^
    11bc:	5f5f0064 	svcpl	0x005f0064
    11c0:	65746661 	ldrbvs	r6, [r4, #-1633]!	; 0xfffff99f
    11c4:	6f6d5f72 	svcvs	0x006d5f72
    11c8:	6f636572 	svcvs	0x00636572
    11cc:	685f6572 	ldmdavs	pc, {r1, r4, r5, r6, r8, sl, sp, lr}^	; <UNPREDICTABLE>
    11d0:	006b6f6f 	rsbeq	r6, fp, pc, ror #30
    11d4:	61726170 	cmnvs	r2, r0, ror r1
    11d8:	5400736d 	strpl	r7, [r0], #-877	; 0xfffffc93
    11dc:	5f434545 	svcpl	0x00434545
    11e0:	73736553 	cmnvc	r3, #348127232	; 0x14c00000
    11e4:	006e6f69 	rsbeq	r6, lr, r9, ror #30
    11e8:	6f6d5f5f 	svcvs	0x006d5f5f
    11ec:	6f636572 	svcvs	0x00636572
    11f0:	5f006572 	svcpl	0x00006572
    11f4:	7365745f 	cmnvc	r5, #1593835520	; 0x5f000000
    11f8:	706f0074 	rsbvc	r0, pc, r4, ror r0	; <UNPREDICTABLE>
    11fc:	72726574 	rsbsvc	r6, r2, #116, 10	; 0x1d000000
    1200:	61687300 	cmnvs	r8, r0, lsl #6
    1204:	5f776f64 	svcpl	0x00776f64
    1208:	66667562 	strbtvs	r7, [r6], -r2, ror #10
    120c:	66007265 	strvs	r7, [r0], -r5, ror #4
    1210:	6e656c69 	cdpvs	12, 6, cr6, cr5, cr9, {3}
    1214:	31656d61 	cmncc	r5, r1, ror #26
    1218:	6c696600 	stclvs	6, cr6, [r9], #-0
    121c:	6d616e65 	stclvs	14, cr6, [r1, #-404]!	; 0xfffffe6c
    1220:	66003365 	strvs	r3, [r0], -r5, ror #6
    1224:	6e656c69 	cdpvs	12, 6, cr6, cr5, cr9, {3}
    1228:	34656d61 	strbtcc	r6, [r5], #-3425	; 0xfffff29f
    122c:	6c696600 	stclvs	6, cr6, [r9], #-0
    1230:	6d616e65 	stclvs	14, cr6, [r1, #-404]!	; 0xfffffe6c
    1234:	54003565 	strpl	r3, [r0], #-1381	; 0xfffffa9b
    1238:	5f434545 	svcpl	0x00434545
    123c:	706d6554 	rsbvc	r6, sp, r4, asr r5
    1240:	6f6d654d 	svcvs	0x006d654d
    1244:	65527972 	ldrbvs	r7, [r2, #-2418]	; 0xfffff68e
    1248:	65726566 	ldrbvs	r6, [r2, #-1382]!	; 0xfffffa9a
    124c:	0065636e 	rsbeq	r6, r5, lr, ror #6
    1250:	656d6974 	strbvs	r6, [sp, #-2420]!	; 0xfffff68c
    1254:	0064694d 	rsbeq	r6, r4, sp, asr #18
    1258:	656d6974 	strbvs	r6, [sp, #-2420]!	; 0xfffff68c
    125c:	00776f4c 	rsbseq	r6, r7, ip, asr #30
    1260:	43454554 	movtmi	r4, #21844	; 0x5554
    1264:	6765525f 			; <UNDEFINED> instruction: 0x6765525f
    1268:	65747369 	ldrbvs	r7, [r4, #-873]!	; 0xfffffc97
    126c:	4d646572 	cfstr64mi	mvdx6, [r4, #-456]!	; 0xfffffe38
    1270:	726f6d65 	rsbvc	r6, pc, #6464	; 0x1940
    1274:	66655279 			; <UNDEFINED> instruction: 0x66655279
    1278:	6e657265 	cdpvs	2, 6, cr7, cr5, cr5, {3}
    127c:	6d006563 	cfstr32vs	mvfx6, [r0, #-396]	; 0xfffffe74
    1280:	69737369 	ldmdbvs	r3!, {r0, r3, r5, r6, r8, r9, ip, sp, lr}^
    1284:	635f6e6f 	cmpvs	pc, #1776	; 0x6f0
    1288:	72746e6f 	rsbsvc	r6, r4, #1776	; 0x6f0
    128c:	5f006c6f 	svcpl	0x00006c6f
    1290:	6c616d5f 	stclvs	13, cr6, [r1], #-380	; 0xfffffe84
    1294:	5f636f6c 	svcpl	0x00636f6c
    1298:	74696e69 	strbtvc	r6, [r9], #-3689	; 0xfffff197
    129c:	696c6169 	stmdbvs	ip!, {r0, r3, r5, r6, r8, sp, lr}^
    12a0:	685f657a 	ldmdavs	pc, {r1, r3, r4, r5, r6, r8, sl, sp, lr}^	; <UNPREDICTABLE>
    12a4:	006b6f6f 	rsbeq	r6, fp, pc, ror #30
    12a8:	656c6966 	strbvs	r6, [ip, #-2406]!	; 0xfffff69a
    12ac:	656d616e 	strbvs	r6, [sp, #-366]!	; 0xfffffe92
    12b0:	6d740073 	ldclvs	0, cr0, [r4, #-460]!	; 0xfffffe34
    12b4:	66657270 			; <UNDEFINED> instruction: 0x66657270
    12b8:	745f5f00 	ldrbvc	r5, [pc], #-3840	; 12c0 <_init-0xf860>
    12bc:	6d616e7a 	stclvs	14, cr6, [r1, #-488]!	; 0xfffffe18
    12c0:	45540065 	ldrbmi	r0, [r4, #-101]	; 0xffffff9b
    12c4:	525f4345 	subspl	r4, pc, #335544321	; 0x14000001
    12c8:	6c757365 	ldclvs	3, cr7, [r5], #-404	; 0xfffffe6c
    12cc:	4e470074 	mcrmi	0, 2, r0, cr7, cr4, {3}
    12d0:	31432055 	qdaddcc	r2, r5, r3
    12d4:	2e362031 	mrccs	0, 1, r2, cr6, cr1, {1}
    12d8:	20312e32 	eorscs	r2, r1, r2, lsr lr
    12dc:	36313032 			; <UNDEFINED> instruction: 0x36313032
    12e0:	36313031 			; <UNDEFINED> instruction: 0x36313031
    12e4:	616d2d20 	cmnvs	sp, r0, lsr #26
    12e8:	3d686372 	stclcc	3, cr6, [r8, #-456]!	; 0xfffffe38
    12ec:	766d7261 	strbtvc	r7, [sp], -r1, ror #4
    12f0:	20612d37 	rsbcs	r2, r1, r7, lsr sp
    12f4:	75746d2d 	ldrbvc	r6, [r4, #-3373]!	; 0xfffff2d3
    12f8:	633d656e 	teqvs	sp, #461373440	; 0x1b800000
    12fc:	6574726f 	ldrbvs	r7, [r4, #-623]!	; 0xfffffd91
    1300:	39612d78 	stmdbcc	r1!, {r3, r4, r5, r6, r8, sl, fp, sp}^
    1304:	666d2d20 	strbtvs	r2, [sp], -r0, lsr #26
    1308:	74616f6c 	strbtvc	r6, [r1], #-3948	; 0xfffff094
    130c:	6962612d 	stmdbvs	r2!, {r0, r2, r3, r5, r8, sp, lr}^
    1310:	7261683d 	rsbvc	r6, r1, #3997696	; 0x3d0000
    1314:	6d2d2064 	stcvs	0, cr2, [sp, #-400]!	; 0xfffffe70
    1318:	3d757066 	ldclcc	0, cr7, [r5, #-408]!	; 0xfffffe68
    131c:	76706676 			; <UNDEFINED> instruction: 0x76706676
    1320:	31642d33 	cmncc	r4, r3, lsr sp
    1324:	6d2d2036 	stcvs	0, cr2, [sp, #-216]!	; 0xffffff28
    1328:	6d756874 	ldclvs	8, cr6, [r5, #-464]!	; 0xfffffe30
    132c:	6d2d2062 	stcvs	0, cr2, [sp, #-392]!	; 0xfffffe78
    1330:	2d736c74 	ldclcs	12, cr6, [r3, #-464]!	; 0xfffffe30
    1334:	6c616964 			; <UNDEFINED> instruction: 0x6c616964
    1338:	3d746365 	ldclcc	3, cr6, [r4, #-404]!	; 0xfffffe6c
    133c:	20756e67 	rsbscs	r6, r5, r7, ror #28
    1340:	2d20672d 	stccs	7, cr6, [r0, #-180]!	; 0xffffff4c
    1344:	2d20324f 	sfmcs	f3, 4, [r0, #-316]!	; 0xfffffec4
    1348:	3d647473 	cfstrdcc	mvd7, [r4, #-460]!	; 0xfffffe34
    134c:	31756e67 	cmncc	r5, r7, ror #28
    1350:	662d2031 			; <UNDEFINED> instruction: 0x662d2031
    1354:	38756e67 	ldmdacc	r5!, {r0, r1, r2, r5, r6, r9, sl, fp, sp, lr}^
    1358:	6e692d39 	mcrvs	13, 3, r2, cr9, cr9, {1}
    135c:	656e696c 	strbvs	r6, [lr, #-2412]!	; 0xfffff694
    1360:	6d662d20 	stclvs	13, cr2, [r6, #-128]!	; 0xffffff80
    1364:	65677265 	strbvs	r7, [r7, #-613]!	; 0xfffffd9b
    1368:	6c6c612d 	stfvse	f6, [ip], #-180	; 0xffffff4c
    136c:	6e6f632d 	cdpvs	3, 6, cr6, cr15, cr13, {1}
    1370:	6e617473 	mcrvs	4, 3, r7, cr1, cr3, {3}
    1374:	2d207374 	stccs	3, cr7, [r0, #-464]!	; 0xfffffe30
    1378:	756f7266 	strbvc	r7, [pc, #-614]!	; 111a <_init-0xfa06>
    137c:	6e69646e 	cdpvs	4, 6, cr6, cr9, cr14, {3}
    1380:	616d2d67 	cmnvs	sp, r7, ror #26
    1384:	2d206874 	stccs	8, cr6, [r0, #-464]!	; 0xfffffe30
    1388:	736c7466 	cmnvc	ip, #1711276032	; 0x66000000
    138c:	646f6d2d 	strbtvs	r6, [pc], #-3373	; 1394 <_init-0xf78c>
    1390:	693d6c65 	ldmdbvs	sp!, {r0, r2, r5, r6, sl, fp, sp, lr}
    1394:	6974696e 	ldmdbvs	r4!, {r1, r2, r3, r5, r6, r8, fp, sp, lr}^
    1398:	652d6c61 	strvs	r6, [sp, #-3169]!	; 0xfffff39f
    139c:	00636578 	rsbeq	r6, r3, r8, ror r5
    13a0:	6d6f682f 	stclvs	8, cr6, [pc, #-188]!	; 12ec <_init-0xf834>
    13a4:	63742f65 	cmnvs	r4, #404	; 0x194
    13a8:	622d6777 	eorvs	r6, sp, #31195136	; 0x1dc0000
    13ac:	646c6975 	strbtvs	r6, [ip], #-2421	; 0xfffff68b
    13b0:	76616c73 			; <UNDEFINED> instruction: 0x76616c73
    13b4:	6f772f65 	svcvs	0x00772f65
    13b8:	70736b72 	rsbsvc	r6, r3, r2, ror fp
    13bc:	2f656361 	svccs	0x00656361
    13c0:	67776374 			; <UNDEFINED> instruction: 0x67776374
    13c4:	6b616d2d 	blvs	185c880 <ringBuffer+0x1804b78>
    13c8:	65722d65 	ldrbvs	r2, [r2, #-3429]!	; 0xfffff29b
    13cc:	7361656c 	cmnvc	r1, #108, 10	; 0x1b000000
    13d0:	616c2f65 	cmnvs	ip, r5, ror #30
    13d4:	2f6c6562 	svccs	0x006c6562
    13d8:	6b636f64 	blvs	18dd170 <ringBuffer+0x1885468>
    13dc:	742d7265 	strtvc	r7, [sp], #-613	; 0xfffffd9b
    13e0:	74737572 	ldrbtvc	r7, [r3], #-1394	; 0xfffffa8e
    13e4:	6d612d79 	stclvs	13, cr2, [r1, #-484]!	; 0xfffffe1c
    13e8:	2d343664 	ldccs	6, cr3, [r4, #-400]!	; 0xfffffe70
    13ec:	67776374 			; <UNDEFINED> instruction: 0x67776374
    13f0:	6975622d 	ldmdbvs	r5!, {r0, r2, r3, r5, r9, sp, lr}^
    13f4:	742f646c 	strtvc	r6, [pc], #-1132	; 13fc <_init-0xf724>
    13f8:	65677261 	strbvs	r7, [r7, #-609]!	; 0xfffffd9f
    13fc:	72612f74 	rsbvc	r2, r1, #116, 30	; 0x1d0
    1400:	696c2d6d 	stmdbvs	ip!, {r0, r2, r3, r5, r6, r8, sl, fp, sp}^
    1404:	2d78756e 	cfldr64cs	mvdx7, [r8, #-440]!	; 0xfffffe48
    1408:	65756e67 	ldrbvs	r6, [r5, #-3687]!	; 0xfffff199
    140c:	68696261 	stmdavs	r9!, {r0, r5, r6, r9, sp, lr}^
    1410:	6e732f66 	cdpvs	15, 7, cr2, cr3, cr6, {3}
    1414:	68737061 	ldmdavs	r3!, {r0, r5, r6, ip, sp, lr}^
    1418:	2f73746f 	svccs	0x0073746f
    141c:	62696c67 	rsbvs	r6, r9, #26368	; 0x6700
    1420:	69672e63 	stmdbvs	r7!, {r0, r1, r5, r6, r9, sl, fp, sp}^
    1424:	696c7e74 	stmdbvs	ip!, {r2, r4, r5, r6, r9, sl, fp, ip, sp, lr}^
    1428:	6f72616e 	svcvs	0x0072616e
    142c:	322e327e 	eorcc	r3, lr, #-536870905	; 0xe0000007
    1430:	616d7e33 	cmnvs	sp, r3, lsr lr
    1434:	72657473 	rsbvc	r7, r5, #1929379840	; 0x73000000
    1438:	7573632f 	ldrbvc	r6, [r3, #-815]!	; 0xfffffcd1
    143c:	4f495f00 	svcmi	0x00495f00
    1440:	6474735f 	ldrbtvs	r7, [r4], #-863	; 0xfffffca1
    1444:	755f6e69 	ldrbvc	r6, [pc, #-3689]	; 5e3 <_init-0x1053d>
    1448:	00646573 	rsbeq	r6, r4, r3, ror r5
    144c:	74696e69 	strbtvc	r6, [r9], #-3689	; 0xfffff197
    1450:	地址 0x0000000000001450 越界。


Disassembly of section .debug_macinfo:

00000000 <.debug_macinfo>:
	...

Disassembly of section .debug_pubtypes:

00000000 <.debug_pubtypes>:
   0:	0000007b 	andeq	r0, r0, fp, ror r0
   4:	00000002 	andeq	r0, r0, r2
   8:	061c0000 	ldreq	r0, [ip], -r0
   c:	025f0000 	subseq	r0, pc, #0
  10:	425f0000 	subsmi	r0, pc, #0
  14:	006c6f6f 	rsbeq	r6, ip, pc, ror #30
  18:	00000146 	andeq	r0, r0, r6, asr #2
  1c:	616f6c66 	cmnvs	pc, r6, ror #24
  20:	02d60074 	sbcseq	r0, r6, #116	; 0x74
  24:	6e750000 	cdpvs	0, 7, cr0, cr5, cr0, {0}
  28:	6e676973 			; <UNDEFINED> instruction: 0x6e676973
  2c:	69206465 	stmdbvs	r0!, {r0, r2, r5, r6, sl, sp, lr}
  30:	b600746e 	strlt	r7, [r0], -lr, ror #8
  34:	4c000002 	stcmi	0, cr0, [r0], {2}
  38:	69757169 	ldmdbvs	r5!, {r0, r3, r5, r6, r8, ip, sp, lr}^
  3c:	79724364 	ldmdbvc	r2!, {r2, r5, r6, r8, r9, lr}^
  40:	6c617473 	cfstrdvs	mvd7, [r1], #-460	; 0xfffffe34
  44:	00003700 	andeq	r3, r0, r0, lsl #14
  48:	746e6900 	strbtvc	r6, [lr], #-2304	; 0xfffff700
  4c:	00007100 	andeq	r7, r0, r0, lsl #2
  50:	6e6f6c00 	cdpvs	12, 6, cr6, cr15, cr0, {0}
  54:	6e692067 	cdpvs	0, 6, cr2, cr9, cr7, {3}
  58:	02470074 	subeq	r0, r7, #116	; 0x74
  5c:	68630000 	stmdavs	r3!, {}^	; <UNPREDICTABLE>
  60:	c1007261 	tstgt	r0, r1, ror #4
  64:	4c000002 	stcmi	0, cr0, [r0], {2}
  68:	69757169 	ldmdbvs	r5!, {r0, r3, r5, r6, r8, ip, sp, lr}^
  6c:	79724364 	ldmdbvc	r2!, {r2, r5, r6, r8, r9, lr}^
  70:	6c617473 	cfstrdvs	mvd7, [r1], #-460	; 0xfffffe34
  74:	75727453 	ldrbvc	r7, [r2, #-1107]!	; 0xfffffbad
  78:	00007463 	andeq	r7, r0, r3, ror #8
  7c:	4f000000 	svcmi	0x00000000
  80:	02000000 	andeq	r0, r0, #0
  84:	00061c00 	andeq	r1, r6, r0, lsl #24
  88:	00026800 	andeq	r6, r2, r0, lsl #16
  8c:	00025100 	andeq	r5, r2, r0, lsl #2
  90:	745f5f00 	ldrbvc	r5, [pc], #-3840	; 98 <_init-0x10a88>
  94:	5f656d69 	svcpl	0x00656d69
  98:	02300074 	eorseq	r0, r0, #116	; 0x74
  9c:	69740000 	ldmdbvs	r4!, {}^	; <UNPREDICTABLE>
  a0:	6176656d 	cmnvs	r6, sp, ror #10
  a4:	0229006c 	eoreq	r0, r9, #108	; 0x6c
  a8:	6f6c0000 	svcvs	0x006c0000
  ac:	7520676e 	strvc	r6, [r0, #-1902]!	; 0xfffff892
  b0:	6769736e 	strbvs	r7, [r9, -lr, ror #6]!
  b4:	2064656e 	rsbcs	r6, r4, lr, ror #10
  b8:	00746e69 	rsbseq	r6, r4, r9, ror #28
  bc:	0000025c 	andeq	r0, r0, ip, asr r2
  c0:	75735f5f 	ldrbvc	r5, [r3, #-3935]!	; 0xfffff0a1
  c4:	6f636573 	svcvs	0x00636573
  c8:	5f73646e 	svcpl	0x0073646e
  cc:	00000074 	andeq	r0, r0, r4, ror r0
  d0:	00380000 	eorseq	r0, r8, r0
  d4:	00020000 	andeq	r0, r2, r0
  d8:	000008cd 	andeq	r0, r0, sp, asr #17
  dc:	00000120 	andeq	r0, r0, r0, lsr #2
  e0:	000000ff 	strdeq	r0, [r0], -pc	; <UNPREDICTABLE>
  e4:	7571694c 	ldrbvc	r6, [r1, #-2380]!	; 0xfffff6b4
  e8:	72436469 	subvc	r6, r3, #1761607680	; 0x69000000
  ec:	61747379 	cmnvs	r4, r9, ror r3
  f0:	010a006c 	tsteq	sl, ip, rrx
  f4:	694c0000 	stmdbvs	ip, {}^	; <UNPREDICTABLE>
  f8:	64697571 	strbtvs	r7, [r9], #-1393	; 0xfffffa8f
  fc:	73797243 	cmnvc	r9, #805306372	; 0x30000004
 100:	536c6174 	cmnpl	ip, #116, 2
 104:	63757274 	cmnvs	r5, #116, 4	; 0x40000007
 108:	00000074 	andeq	r0, r0, r4, ror r0
	...

Disassembly of section .debug_ranges:

00000000 <.debug_ranges>:
   0:	000202c8 	andeq	r0, r2, r8, asr #5
   4:	000202cc 	andeq	r0, r2, ip, asr #5
   8:	000202dc 	ldrdeq	r0, [r2], -ip
   c:	00020350 	andeq	r0, r2, r0, asr r3
	...
  18:	00040318 	andeq	r0, r4, r8, lsl r3
  1c:	00040344 	andeq	r0, r4, r4, asr #6
  20:	00040350 	andeq	r0, r4, r0, asr r3
  24:	0004036c 	andeq	r0, r4, ip, ror #6
	...
  30:	00040000 	andeq	r0, r4, r0
  34:	000401d0 	ldrdeq	r0, [r4], -r0	; <UNPREDICTABLE>
  38:	00020000 	andeq	r0, r2, r0
  3c:	00020564 	andeq	r0, r2, r4, ror #10
  40:	000401d0 	ldrdeq	r0, [r4], -r0	; <UNPREDICTABLE>
  44:	00040810 	andeq	r0, r4, r0, lsl r8
	...
  50:	00040810 	andeq	r0, r4, r0, lsl r8
  54:	00040890 	muleq	r4, r0, r8
  58:	00020564 	andeq	r0, r2, r4, ror #10
  5c:	00020588 	andeq	r0, r2, r8, lsl #11
  60:	00040890 	muleq	r4, r0, r8
  64:	00040930 	andeq	r0, r4, r0, lsr r9
  68:	00020588 	andeq	r0, r2, r8, lsl #11
  6c:	000205d0 	ldrdeq	r0, [r2], -r0	; <UNPREDICTABLE>
  70:	00040930 	andeq	r0, r4, r0, lsr r9
  74:	000409dc 	ldrdeq	r0, [r4], -ip
  78:	000205d0 	ldrdeq	r0, [r2], -r0	; <UNPREDICTABLE>
  7c:	0002062c 	andeq	r0, r2, ip, lsr #12
	...
  88:	000409dc 	ldrdeq	r0, [r4], -ip
  8c:	00040a34 	andeq	r0, r4, r4, lsr sl
  90:	00020698 	muleq	r2, r8, r6
  94:	0002076c 	andeq	r0, r2, ip, ror #14
	...
  a0:	ffffffff 			; <UNDEFINED> instruction: 0xffffffff
  a4:	00000000 	andeq	r0, r0, r0
  a8:	00045144 	andeq	r5, r4, r4, asr #2
  ac:	00045168 	andeq	r5, r4, r8, ror #2
  b0:	00010b20 	andeq	r0, r1, r0, lsr #22
  b4:	00010b28 	andeq	r0, r1, r8, lsr #22
  b8:	00046664 	andeq	r6, r4, r4, ror #12
  bc:	00046668 	andeq	r6, r4, r8, ror #12
	...
  c8:	ffffffff 			; <UNDEFINED> instruction: 0xffffffff
  cc:	00000000 	andeq	r0, r0, r0
  d0:	00010b28 	andeq	r0, r1, r8, lsr #22
  d4:	00010b2c 	andeq	r0, r1, ip, lsr #22
  d8:	00046668 	andeq	r6, r4, r8, ror #12
  dc:	0004666c 	andeq	r6, r4, ip, ror #12
	...
