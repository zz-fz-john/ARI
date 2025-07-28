
./syringe_baseline_after_compt：     文件格式 elf32-littlearm


Disassembly of section .interp:

00010114 <.interp>:
   10114:	62696c2f 	rsbvs	r6, r9, #12032	; 0x2f00
   10118:	2d646c2f 	stclcs	12, cr6, [r4, #-188]!	; 0xffffff44
   1011c:	756e696c 	strbvc	r6, [lr, #-2412]!	; 0xfffff694
   10120:	72612d78 	rsbvc	r2, r1, #120, 26	; 0x1e00
   10124:	2e66686d 	cdpcs	8, 6, cr6, cr6, cr13, {3}
   10128:	332e6f73 			; <UNDEFINED> instruction: 0x332e6f73
	...

Disassembly of section .gnu.hash:

00010130 <.gnu.hash>:
   10130:	00000025 	andeq	r0, r0, r5, lsr #32
   10134:	00000002 	andeq	r0, r0, r2
   10138:	00000008 	andeq	r0, r0, r8
   1013c:	00000008 	andeq	r0, r0, r8
   10140:	1a829d5a 	bne	fe0b76b0 <__bss_end__+0xf47c90dc>
   10144:	6301a086 	movwvs	sl, #4230	; 0x1086
   10148:	4c489022 	mcrrmi	0, 2, r9, r8, cr2
   1014c:	b09f4880 	addslt	r4, pc, r0, lsl #17
   10150:	203d7c80 	eorscs	r7, sp, r0, lsl #25
   10154:	91244c01 			; <UNDEFINED> instruction: 0x91244c01
   10158:	00000204 	andeq	r0, r0, r4, lsl #4
   1015c:	4a00106a 	bmi	1430c <.DATA_REGION_0__data_end+0x3840>
   10160:	00000002 	andeq	r0, r0, r2
   10164:	00000004 	andeq	r0, r0, r4
   10168:	00000000 	andeq	r0, r0, r0
   1016c:	00000005 	andeq	r0, r0, r5
   10170:	00000000 	andeq	r0, r0, r0
   10174:	0000000b 	andeq	r0, r0, fp
   10178:	0000000c 	andeq	r0, r0, ip
   1017c:	0000000d 	andeq	r0, r0, sp
   10180:	00000010 	andeq	r0, r0, r0, lsl r0
	...
   10190:	00000011 	andeq	r0, r0, r1, lsl r0
   10194:	00000000 	andeq	r0, r0, r0
   10198:	00000014 	andeq	r0, r0, r4, lsl r0
   1019c:	00000015 	andeq	r0, r0, r5, lsl r0
   101a0:	00000000 	andeq	r0, r0, r0
   101a4:	00000016 	andeq	r0, r0, r6, lsl r0
   101a8:	00000017 	andeq	r0, r0, r7, lsl r0
   101ac:	00000019 	andeq	r0, r0, r9, lsl r0
   101b0:	0000001a 	andeq	r0, r0, sl, lsl r0
   101b4:	00000000 	andeq	r0, r0, r0
   101b8:	0000001c 	andeq	r0, r0, ip, lsl r0
   101bc:	0000001d 	andeq	r0, r0, sp, lsl r0
   101c0:	0000001e 	andeq	r0, r0, lr, lsl r0
   101c4:	0000001f 	andeq	r0, r0, pc, lsl r0
   101c8:	00000022 	andeq	r0, r0, r2, lsr #32
   101cc:	00000024 	andeq	r0, r0, r4, lsr #32
   101d0:	00000025 	andeq	r0, r0, r5, lsr #32
   101d4:	00000026 	andeq	r0, r0, r6, lsr #32
   101d8:	00000027 	andeq	r0, r0, r7, lsr #32
   101dc:	00000028 	andeq	r0, r0, r8, lsr #32
   101e0:	00000000 	andeq	r0, r0, r0
   101e4:	00000029 	andeq	r0, r0, r9, lsr #32
   101e8:	0000002a 	andeq	r0, r0, sl, lsr #32
   101ec:	0000002c 	andeq	r0, r0, ip, lsr #32
   101f0:	00000030 	andeq	r0, r0, r0, lsr r0
   101f4:	0d39ad3c 	ldceq	13, cr10, [r9, #-240]!	; 0xffffff10
   101f8:	7c9bd777 	ldcvc	7, cr13, [fp], {119}	; 0x77
   101fc:	7c9665e7 	cfldr32vc	mvfx6, [r6], {231}	; 0xe7
   10200:	10614a06 	rsbne	r4, r1, r6, lsl #20
   10204:	e6854b86 	str	r4, [r5], r6, lsl #23
   10208:	e8d81e2e 	ldm	r8, {r1, r2, r3, r5, r9, sl, fp, ip}^
   1020c:	a4f92300 	ldrbtge	r2, [r9], #768	; 0x300
   10210:	7c9f377c 	ldcvc	7, cr3, [pc], {124}	; 0x7c
   10214:	0f742f17 	svceq	0x00742f17
   10218:	0f738b7d 	svceq	0x00738b7d
   1021c:	192c7473 	stmdbne	ip!, {r0, r1, r4, r5, r6, sl, ip, sp, lr}
   10220:	156b2bb8 	strbne	r2, [fp, #-3000]!	; 0xfffff448
   10224:	7c96f086 	ldcvc	0, cr15, [r6], {134}	; 0x86
   10228:	37900e7f 			; <UNDEFINED> instruction: 0x37900e7f
   1022c:	0ea4b293 	mcreq	2, 5, fp, cr4, cr3, {4}
   10230:	2a29815a 	bcs	a707a0 <ringBuffer+0xa18ac8>
   10234:	bac212a0 	blt	ff094cbc <__bss_end__+0xf57a66e8>
   10238:	bcfff93f 			; <UNDEFINED> instruction: 0xbcfff93f
   1023c:	0f3b9a5b 	svceq	0x003b9a5b
   10240:	ca90eebd 	bgt	fe44bd3c <__bss_end__+0xf4b5d768>
   10244:	f07241e3 			; <UNDEFINED> instruction: 0xf07241e3
   10248:	8ff9ac08 	svchi	0x00f9ac08
   1024c:	77e5ae8b 	strbvc	sl, [r5, fp, lsl #29]!
   10250:	0d82b831 	stceq	8, cr11, [r2, #196]	; 0xc4
   10254:	0d827590 	cfstr32eq	mvfx7, [r2, #576]	; 0x240
   10258:	21288c53 			; <UNDEFINED> instruction: 0x21288c53
   1025c:	0fa99fa1 	svceq	0x00a99fa1
   10260:	eafe348d 	b	fff9d49c <__bss_end__+0xf66aeec8>
   10264:	7c9ab171 	ldfvcd	f3, [sl], {113}	; 0x71
   10268:	1487678c 	strne	r6, [r7], #1932	; 0x78c
   1026c:	3345dd94 	movtcc	sp, #23956	; 0x5d94
   10270:	fd09cf21 	stc2	15, cr12, [r9, #-132]	; 0xffffff7c
   10274:	1c93965e 	ldcne	6, cr9, [r3], {94}	; 0x5e
   10278:	a5b50f0b 	ldrge	r0, [r5, #3851]!	; 0xf0b
   1027c:	7c943c73 	ldcvc	12, cr3, [r4], {115}	; 0x73
   10280:	4f152227 	svcmi	0x00152227
   10284:	7ea7aab5 			; <UNDEFINED> instruction: 0x7ea7aab5
   10288:	0b88a54f 	bleq	fe2397cc <__bss_end__+0xf494b1f8>
   1028c:	0b886775 	bleq	fe22a068 <__bss_end__+0xf493ba94>
   10290:	7dd7aaab 	vldrvc	s21, [r7, #684]	; 0x2ac
   10294:	be582cf8 	mrclt	12, 2, r2, cr8, cr8, {7}
   10298:	e61d840f 	ldr	r8, [sp], -pc, lsl #8
   1029c:	7c97c2c8 	lfmvc	f4, 1, [r7], {200}	; 0xc8
   102a0:	7c9c7b10 	vldmiavc	ip, {d7-d14}
   102a4:	7c9ddc02 	ldcvc	12, cr13, [sp], {2}
   102a8:	00597905 	subseq	r7, r9, r5, lsl #18
   102ac:	bfd97efb 	svclt	0x00d97efb

Disassembly of section .dynsym:

000102b0 <.dynsym>:
	...
   102c0:	00000109 	andeq	r0, r0, r9, lsl #2
	...
   102cc:	00000011 	andeq	r0, r0, r1, lsl r0
   102d0:	000000e4 	andeq	r0, r0, r4, ror #1
	...
   102dc:	00000012 	andeq	r0, r0, r2, lsl r0
   102e0:	00000014 	andeq	r0, r0, r4, lsl r0
	...
   102ec:	00000012 	andeq	r0, r0, r2, lsl r0
   102f0:	0000007b 	andeq	r0, r0, fp, ror r0
	...
   102fc:	00000012 	andeq	r0, r0, r2, lsl r0
   10300:	0000013e 	andeq	r0, r0, lr, lsr r1
   10304:	098ee4ec 	stmibeq	lr, {r2, r3, r5, r6, r7, sl, sp, lr, pc}
   10308:	0000007c 	andeq	r0, r0, ip, ror r0
   1030c:	001e0011 	andseq	r0, lr, r1, lsl r0
   10310:	00000061 	andeq	r0, r0, r1, rrx
	...
   1031c:	00000012 	andeq	r0, r0, r2, lsl r0
   10320:	00000172 	andeq	r0, r0, r2, ror r1
   10324:	00057cd8 	ldrdeq	r7, [r5], -r8
   10328:	09896808 	stmibeq	r9, {r3, fp, sp, lr}
   1032c:	001e0011 	andseq	r0, lr, r1, lsl r0
   10330:	000000c5 	andeq	r0, r0, r5, asr #1
	...
   1033c:	00000012 	andeq	r0, r0, r2, lsl r0
   10340:	00000198 	muleq	r0, r8, r1
   10344:	000570d4 	ldrdeq	r7, [r5], -r4
   10348:	00000010 	andeq	r0, r0, r0, lsl r0
   1034c:	001b0011 	andseq	r0, fp, r1, lsl r0
   10350:	0000003f 	andeq	r0, r0, pc, lsr r0
	...
   1035c:	00000012 	andeq	r0, r0, r2, lsl r0
   10360:	00000013 	andeq	r0, r0, r3, lsl r0
	...
   1036c:	00000012 	andeq	r0, r0, r2, lsl r0
   10370:	00000053 	andeq	r0, r0, r3, asr r0
	...
   1037c:	00000012 	andeq	r0, r0, r2, lsl r0
   10380:	00000074 	andeq	r0, r0, r4, ror r0
	...
   1038c:	00000012 	andeq	r0, r0, r2, lsl r0
   10390:	000000eb 	andeq	r0, r0, fp, ror #1
	...
   1039c:	00000012 	andeq	r0, r0, r2, lsl r0
   103a0:	00000144 	andeq	r0, r0, r4, asr #2
   103a4:	00057c9c 	muleq	r5, ip, ip
   103a8:	00000004 	andeq	r0, r0, r4
   103ac:	001e0011 	andseq	r0, lr, r1, lsl r0
   103b0:	000000f0 	strdeq	r0, [r0], -r0	; <UNPREDICTABLE>
	...
   103bc:	00000012 	andeq	r0, r0, r2, lsl r0
   103c0:	00000129 	andeq	r0, r0, r9, lsr #2
   103c4:	00057c90 	muleq	r5, r0, ip
   103c8:	00000004 	andeq	r0, r0, r4
   103cc:	001e0011 	andseq	r0, lr, r1, lsl r0
   103d0:	000000f7 	strdeq	r0, [r0], -r7
	...
   103dc:	00000012 	andeq	r0, r0, r2, lsl r0
   103e0:	00000073 	andeq	r0, r0, r3, ror r0
	...
   103ec:	00000012 	andeq	r0, r0, r2, lsl r0
   103f0:	0000004d 	andeq	r0, r0, sp, asr #32
	...
   103fc:	00000012 	andeq	r0, r0, r2, lsl r0
   10400:	00000028 	andeq	r0, r0, r8, lsr #32
	...
   1040c:	00000012 	andeq	r0, r0, r2, lsl r0
   10410:	00000037 	andeq	r0, r0, r7, lsr r0
	...
   1041c:	00000012 	andeq	r0, r0, r2, lsl r0
   10420:	000000d6 	ldrdeq	r0, [r0], -r6
	...
   1042c:	00000012 	andeq	r0, r0, r2, lsl r0
   10430:	0000019d 	muleq	r0, sp, r1
   10434:	00057ca0 	andeq	r7, r5, r0, lsr #25
   10438:	00000001 	andeq	r0, r0, r1
   1043c:	001e0011 	andseq	r0, lr, r1, lsl r0
   10440:	00000030 	andeq	r0, r0, r0, lsr r0
   10444:	00010a20 	andeq	r0, r1, r0, lsr #20
   10448:	00000000 	andeq	r0, r0, r0
   1044c:	00000012 	andeq	r0, r0, r2, lsl r0
   10450:	00000045 	andeq	r0, r0, r5, asr #32
	...
   1045c:	00000012 	andeq	r0, r0, r2, lsl r0
   10460:	0000005a 	andeq	r0, r0, sl, asr r0
	...
   1046c:	00000012 	andeq	r0, r0, r2, lsl r0
   10470:	000000b8 	strheq	r0, [r0], -r8
	...
   1047c:	00000012 	andeq	r0, r0, r2, lsl r0
   10480:	00000019 	andeq	r0, r0, r9, lsl r0
	...
   1048c:	00000012 	andeq	r0, r0, r2, lsl r0
   10490:	000000df 	ldrdeq	r0, [r0], -pc	; <UNPREDICTABLE>
	...
   1049c:	00000012 	andeq	r0, r0, r2, lsl r0
   104a0:	00000110 	andeq	r0, r0, r0, lsl r1
   104a4:	00057c98 	muleq	r5, r8, ip
   104a8:	00000004 	andeq	r0, r0, r4
   104ac:	001e0011 	andseq	r0, lr, r1, lsl r0
   104b0:	00000167 	andeq	r0, r0, r7, ror #2
   104b4:	00057ca4 	andeq	r7, r5, r4, lsr #25
   104b8:	00000004 	andeq	r0, r0, r4
   104bc:	001e0011 	andseq	r0, lr, r1, lsl r0
   104c0:	0000004c 	andeq	r0, r0, ip, asr #32
	...
   104cc:	00000012 	andeq	r0, r0, r2, lsl r0
   104d0:	000000be 	strheq	r0, [r0], -lr
	...
   104dc:	00000012 	andeq	r0, r0, r2, lsl r0
   104e0:	0000000b 	andeq	r0, r0, fp
	...
   104ec:	00000012 	andeq	r0, r0, r2, lsl r0
   104f0:	0000006e 	andeq	r0, r0, lr, rrx
	...
   104fc:	00000012 	andeq	r0, r0, r2, lsl r0
   10500:	00000090 	muleq	r0, r0, r0
	...
   1050c:	00000012 	andeq	r0, r0, r2, lsl r0
   10510:	0000015c 	andeq	r0, r0, ip, asr r1
   10514:	098ee588 	stmibeq	lr, {r3, r7, r8, sl, sp, lr, pc}
   10518:	00000004 	andeq	r0, r0, r4
   1051c:	001e0011 	andseq	r0, lr, r1, lsl r0
   10520:	00000191 	muleq	r0, r1, r1
   10524:	098ee594 	stmibeq	lr, {r2, r4, r7, r8, sl, sp, lr, pc}
   10528:	00000004 	andeq	r0, r0, r4
   1052c:	001e0011 	andseq	r0, lr, r1, lsl r0
   10530:	00000125 	andeq	r0, r0, r5, lsr #2
   10534:	098ee4e4 	stmibeq	lr, {r2, r5, r6, r7, sl, sp, lr, pc}
   10538:	00000008 	andeq	r0, r0, r8
   1053c:	001e0011 	andseq	r0, lr, r1, lsl r0
   10540:	000000a3 	andeq	r0, r0, r3, lsr #1
	...
   1054c:	00000012 	andeq	r0, r0, r2, lsl r0
   10550:	00000100 	andeq	r0, r0, r0, lsl #2
	...
   1055c:	00000012 	andeq	r0, r0, r2, lsl r0
   10560:	000000ff 	strdeq	r0, [r0], -pc	; <UNPREDICTABLE>
	...
   1056c:	00000012 	andeq	r0, r0, r2, lsl r0
   10570:	00000157 	andeq	r0, r0, r7, asr r1
   10574:	098ee568 	stmibeq	lr, {r3, r5, r6, r8, sl, sp, lr, pc}
   10578:	00000020 	andeq	r0, r0, r0, lsr #32
   1057c:	001e0011 	andseq	r0, lr, r1, lsl r0
   10580:	00000040 	andeq	r0, r0, r0, asr #32
	...
   1058c:	00000012 	andeq	r0, r0, r2, lsl r0
   10590:	0000017d 	andeq	r0, r0, sp, ror r1
   10594:	098ee58c 	stmibeq	lr, {r2, r3, r7, r8, sl, sp, lr, pc}
   10598:	00000008 	andeq	r0, r0, r8
   1059c:	001e0011 	andseq	r0, lr, r1, lsl r0
   105a0:	00000195 	muleq	r0, r5, r1
   105a4:	098ee598 	stmibeq	lr, {r3, r4, r7, r8, sl, sp, lr, pc}
   105a8:	0000003c 	andeq	r0, r0, ip, lsr r0
   105ac:	001e0011 	andseq	r0, lr, r1, lsl r0
   105b0:	00000182 	andeq	r0, r0, r2, lsl #3
   105b4:	000207fc 	strdeq	r0, [r2], -ip
   105b8:	00000004 	andeq	r0, r0, r4
   105bc:	000e0011 	andeq	r0, lr, r1, lsl r0

Disassembly of section .dynstr:

000105c0 <.dynstr>:
   105c0:	62696c00 	rsbvs	r6, r9, #0, 24
   105c4:	6f732e63 	svcvs	0x00732e63
   105c8:	7300362e 	movwvc	r3, #1582	; 0x62e
   105cc:	6e697270 	mcrvs	2, 3, r7, cr9, cr0, {3}
   105d0:	66006674 			; <UNDEFINED> instruction: 0x66006674
   105d4:	6e65706f 	cdpvs	0, 6, cr7, cr5, cr15, {3}
   105d8:	695f5f00 	ldmdbvs	pc, {r8, r9, sl, fp, ip, lr}^	; <UNPREDICTABLE>
   105dc:	39636f73 	stmdbcc	r3!, {r0, r1, r4, r5, r6, r8, r9, sl, fp, sp, lr}^
   105e0:	63735f39 	cmnvs	r3, #57, 30	; 0xe4
   105e4:	00666e61 	rsbeq	r6, r6, r1, ror #28
   105e8:	63747570 	cmnvs	r4, #112, 10	; 0x1c000000
   105ec:	00726168 	rsbseq	r6, r2, r8, ror #2
   105f0:	736d656d 	cmnvc	sp, #457179136	; 0x1b400000
   105f4:	67007465 	strvs	r7, [r0, -r5, ror #8]
   105f8:	68637465 	stmdavs	r3!, {r0, r2, r5, r6, sl, ip, sp, lr}^
   105fc:	66007261 	strvs	r7, [r0], -r1, ror #4
   10600:	73747570 	cmnvc	r4, #112, 10	; 0x1c000000
   10604:	6d656d00 	stclvs	13, cr6, [r5, #-0]
   10608:	00797063 	rsbseq	r7, r9, r3, rrx
   1060c:	6f6c6366 	svcvs	0x006c6366
   10610:	72006573 	andvc	r6, r0, #482344960	; 0x1cc00000
   10614:	766f6d65 	strbtvc	r6, [pc], -r5, ror #26
   10618:	73750065 	cmnvc	r5, #101	; 0x65
   1061c:	7065656c 	rsbvc	r6, r5, ip, ror #10
   10620:	74656700 	strbtvc	r6, [r5], #-1792	; 0xfffff900
   10624:	656d6974 	strbvs	r6, [sp, #-2420]!	; 0xfffff68c
   10628:	6164666f 	cmnvs	r4, pc, ror #12
   1062c:	74610079 	strbtvc	r0, [r1], #-121	; 0xffffff87
   10630:	6600696f 	strvs	r6, [r0], -pc, ror #18
   10634:	6e697270 	mcrvs	2, 3, r7, cr9, cr0, {3}
   10638:	65006674 	strvs	r6, [r0, #-1652]	; 0xfffff98c
   1063c:	00787272 	rsbseq	r7, r8, r2, ror r2
   10640:	7062696c 	rsbvc	r6, r2, ip, ror #18
   10644:	65726874 	ldrbvs	r6, [r2, #-2164]!	; 0xfffff78c
   10648:	732e6461 			; <UNDEFINED> instruction: 0x732e6461
   1064c:	00302e6f 	eorseq	r2, r0, pc, ror #28
   10650:	72687470 	rsbvc	r7, r8, #112, 8	; 0x70000000
   10654:	5f646165 	svcpl	0x00646165
   10658:	6574756d 	ldrbvs	r7, [r4, #-1389]!	; 0xfffffa93
   1065c:	6f6c5f78 	svcvs	0x006c5f78
   10660:	70006b63 	andvc	r6, r0, r3, ror #22
   10664:	65726874 	ldrbvs	r6, [r2, #-2164]!	; 0xfffff78c
   10668:	6d5f6461 	cfldrdvs	mvd6, [pc, #-388]	; 104ec <pthread_mutex_unlock@plt-0x444>
   1066c:	78657475 	stmdavc	r5!, {r0, r2, r4, r5, r6, sl, ip, sp, lr}^
   10670:	6c6e755f 	cfstr64vs	mvdx7, [lr], #-380	; 0xfffffe84
   10674:	006b636f 	rsbeq	r6, fp, pc, ror #6
   10678:	74636f69 	strbtvc	r6, [r3], #-3945	; 0xfffff097
   1067c:	7473006c 	ldrbtvc	r0, [r3], #-108	; 0xffffff94
   10680:	706d6372 	rsbvc	r6, sp, r2, ror r3
   10684:	655f5f00 	ldrbvs	r5, [pc, #-3840]	; f78c <pthread_mutex_unlock@plt-0x11a4>
   10688:	6f6e7272 	svcvs	0x006e7272
   1068c:	636f6c5f 	cmnvs	pc, #24320	; 0x5f00
   10690:	6f697461 	svcvs	0x00697461
   10694:	7473006e 	ldrbtvc	r0, [r3], #-110	; 0xffffff92
   10698:	72726572 	rsbsvc	r6, r2, #478150656	; 0x1c800000
   1069c:	6d00726f 	sfmvs	f7, 4, [r0, #-444]	; 0xfffffe44
   106a0:	0070616d 	rsbseq	r6, r0, sp, ror #2
   106a4:	6c6c616d 	stfvse	f6, [ip], #-436	; 0xfffffe4c
   106a8:	6600636f 	strvs	r6, [r0], -pc, ror #6
   106ac:	00656572 	rsbeq	r6, r5, r2, ror r5
   106b0:	6d6e756d 	cfstr64vs	mvdx7, [lr, #-436]!	; 0xfffffe4c
   106b4:	73007061 	movwvc	r7, #97	; 0x61
   106b8:	61637379 	smcvs	14137	; 0x3739
   106bc:	76006c6c 	strvc	r6, [r0], -ip, ror #24
   106c0:	72706e73 	rsbsvc	r6, r0, #1840	; 0x730
   106c4:	66746e69 	ldrbtvs	r6, [r4], -r9, ror #28
   106c8:	64747300 	ldrbtvs	r7, [r4], #-768	; 0xfffffd00
   106cc:	0074756f 	rsbseq	r7, r4, pc, ror #10
   106d0:	5f746572 	svcpl	0x00746572
   106d4:	6f636572 	svcvs	0x00636572
   106d8:	6e696472 	mcrvs	4, 3, r6, cr9, cr2, {3}
   106dc:	69665f67 	stmdbvs	r6!, {r0, r1, r2, r5, r6, r8, r9, sl, fp, ip, lr}^
   106e0:	6873696e 	ldmdavs	r3!, {r1, r2, r3, r5, r6, r8, fp, sp, lr}^
   106e4:	78746300 	ldmdavc	r4!, {r8, r9, sp, lr}^
   106e8:	6e697200 	cdpvs	2, 6, cr7, cr9, cr0, {0}
   106ec:	66756267 	ldrbtvs	r6, [r5], -r7, ror #4
   106f0:	5f726566 	svcpl	0x00726566
   106f4:	74696e69 	strbtvc	r6, [r9], #-3689	; 0xfffff197
   106f8:	616c665f 	cmnvs	ip, pc, asr r6
   106fc:	74730067 	ldrbtvc	r0, [r3], #-103	; 0xffffff99
   10700:	00657461 	rsbeq	r7, r5, r1, ror #8
   10704:	5f746572 	svcpl	0x00746572
   10708:	68736168 	ldmdavs	r3!, {r3, r5, r6, r8, sp, lr}^
   1070c:	696e695f 	stmdbvs	lr!, {r0, r1, r2, r3, r4, r6, r8, fp, sp, lr}^
   10710:	6c665f74 	stclvs	15, cr5, [r6], #-464	; 0xfffffe30
   10714:	68006761 	stmdavs	r0, {r0, r5, r6, r8, r9, sl, sp, lr}
   10718:	00687361 	rsbeq	r7, r8, r1, ror #6
   1071c:	5f727265 	svcpl	0x00727265
   10720:	6769726f 	strbvs	r7, [r9, -pc, ror #4]!
   10724:	69006e69 	stmdbvs	r0, {r0, r3, r5, r6, r9, sl, fp, sp, lr}
   10728:	6b6f766e 	blvs	1bee0e8 <ringBuffer+0x1b96410>
   1072c:	6e635f65 	cdpvs	15, 6, cr5, cr3, cr5, {3}
   10730:	69720074 	ldmdbvs	r2!, {r2, r4, r5, r6}^
   10734:	7542676e 	strbvc	r6, [r2, #-1902]	; 0xfffff892
   10738:	72656666 	rsbvc	r6, r5, #106954752	; 0x6600000
   1073c:	73657300 	cmnvc	r5, #0, 6
   10740:	65720073 	ldrbvs	r0, [r2, #-115]!	; 0xffffff8d
   10744:	64726f63 	ldrbtvs	r6, [r2], #-3939	; 0xfffff09d
   10748:	5f676e69 	svcpl	0x00676e69
   1074c:	67616c66 	strbvs	r6, [r1, -r6, ror #24]!
   10750:	73657200 	cmnvc	r5, #0, 4
   10754:	00706f00 	rsbseq	r6, r0, r0, lsl #30
   10758:	64697575 	strbtvs	r7, [r9], #-1397	; 0xfffffa8b
   1075c:	5f647200 	svcpl	0x00647200
   10760:	6574706f 	ldrbvs	r7, [r4, #-111]!	; 0xffffff91
   10764:	6e695f65 	cdpvs	15, 6, cr5, cr9, cr5, {3}
   10768:	47007469 	strmi	r7, [r0, -r9, ror #8]
   1076c:	4342494c 	movtmi	r4, #10572	; 0x294c
   10770:	372e325f 			; <UNDEFINED> instruction: 0x372e325f
   10774:	494c4700 	stmdbmi	ip, {r8, r9, sl, lr}^
   10778:	325f4342 	subscc	r4, pc, #134217729	; 0x8000001
   1077c:	地址 0x000000000001077c 越界。


Disassembly of section .gnu.version:

00010780 <.gnu.version>:
   10780:	00020000 	andeq	r0, r2, r0
   10784:	00020002 	andeq	r0, r2, r2
   10788:	00010002 	andeq	r0, r1, r2
   1078c:	00010002 	andeq	r0, r1, r2
   10790:	00010002 	andeq	r0, r1, r2
   10794:	00020002 	andeq	r0, r2, r2
   10798:	00020002 	andeq	r0, r2, r2
   1079c:	00010002 	andeq	r0, r1, r2
   107a0:	00010002 	andeq	r0, r1, r2
   107a4:	00020002 	andeq	r0, r2, r2
   107a8:	00020002 	andeq	r0, r2, r2
   107ac:	00020002 	andeq	r0, r2, r2
   107b0:	00020001 	andeq	r0, r2, r1
   107b4:	00020002 	andeq	r0, r2, r2
   107b8:	00030002 	andeq	r0, r3, r2
   107bc:	00010002 	andeq	r0, r1, r2
   107c0:	00020001 	andeq	r0, r2, r1
   107c4:	00020002 	andeq	r0, r2, r2
   107c8:	00020002 	andeq	r0, r2, r2
   107cc:	00010001 	andeq	r0, r1, r1
   107d0:	00020001 	andeq	r0, r2, r1
   107d4:	00020002 	andeq	r0, r2, r2
   107d8:	00020001 	andeq	r0, r2, r1
   107dc:	00010001 	andeq	r0, r1, r1
   107e0:	地址 0x00000000000107e0 越界。


Disassembly of section .gnu.version_r:

000107e4 <.gnu.version_r>:
   107e4:	00020001 	andeq	r0, r2, r1
   107e8:	00000001 	andeq	r0, r0, r1
   107ec:	00000010 	andeq	r0, r0, r0, lsl r0
   107f0:	00000000 	andeq	r0, r0, r0
   107f4:	0d696917 			; <UNDEFINED> instruction: 0x0d696917
   107f8:	00030000 	andeq	r0, r3, r0
   107fc:	000001ab 	andeq	r0, r0, fp, lsr #3
   10800:	00000010 	andeq	r0, r0, r0, lsl r0
   10804:	0d696914 			; <UNDEFINED> instruction: 0x0d696914
   10808:	00020000 	andeq	r0, r2, r0
   1080c:	000001b5 			; <UNDEFINED> instruction: 0x000001b5
   10810:	00000000 	andeq	r0, r0, r0

Disassembly of section .rel.dyn:

00010814 <.rel.dyn>:
   10814:	000570b8 	strheq	r7, [r5], -r8
   10818:	00000115 	andeq	r0, r0, r5, lsl r1

Disassembly of section .rel.plt:

0001081c <.rel.plt>:
   1081c:	0005700c 	andeq	r7, r5, ip
   10820:	00002916 	andeq	r2, r0, r6, lsl r9
   10824:	00057010 	andeq	r7, r5, r0, lsl r0
   10828:	00002216 	andeq	r2, r0, r6, lsl r2
   1082c:	00057014 	andeq	r7, r5, r4, lsl r0
   10830:	00000d16 	andeq	r0, r0, r6, lsl sp
   10834:	00057018 	andeq	r7, r5, r8, lsl r0
   10838:	00000b16 	andeq	r0, r0, r6, lsl fp
   1083c:	0005701c 	andeq	r7, r5, ip, lsl r0
   10840:	00000e16 	andeq	r0, r0, r6, lsl lr
   10844:	00057020 	andeq	r7, r5, r0, lsr #32
   10848:	00002516 	andeq	r2, r0, r6, lsl r5
   1084c:	00057024 	andeq	r7, r5, r4, lsr #32
   10850:	00001a16 	andeq	r1, r0, r6, lsl sl
   10854:	00057028 	andeq	r7, r5, r8, lsr #32
   10858:	00001616 	andeq	r1, r0, r6, lsl r6
   1085c:	0005702c 	andeq	r7, r5, ip, lsr #32
   10860:	00001c16 	andeq	r1, r0, r6, lsl ip
   10864:	00057030 	andeq	r7, r5, r0, lsr r0
   10868:	00001b16 	andeq	r1, r0, r6, lsl fp
   1086c:	00057034 	andeq	r7, r5, r4, lsr r0
   10870:	00000616 	andeq	r0, r0, r6, lsl r6
   10874:	00057038 	andeq	r7, r5, r8, lsr r0
   10878:	00002d16 	andeq	r2, r0, r6, lsl sp
   1087c:	0005703c 	andeq	r7, r5, ip, lsr r0
   10880:	00000216 	andeq	r0, r0, r6, lsl r2
   10884:	00057040 	andeq	r7, r5, r0, asr #32
   10888:	00001716 	andeq	r1, r0, r6, lsl r7
   1088c:	00057044 	andeq	r7, r5, r4, asr #32
   10890:	00000316 	andeq	r0, r0, r6, lsl r3
   10894:	00057048 	andeq	r7, r5, r8, asr #32
   10898:	00001216 	andeq	r1, r0, r6, lsl r2
   1089c:	0005704c 	andeq	r7, r5, ip, asr #32
   108a0:	00001e16 	andeq	r1, r0, r6, lsl lr
   108a4:	00057050 	andeq	r7, r5, r0, asr r0
   108a8:	00001316 	andeq	r1, r0, r6, lsl r3
   108ac:	00057054 	andeq	r7, r5, r4, asr r0
   108b0:	00000816 	andeq	r0, r0, r6, lsl r8
   108b4:	00057058 	andeq	r7, r5, r8, asr r0
   108b8:	00002a16 	andeq	r2, r0, r6, lsl sl
   108bc:	0005705c 	andeq	r7, r5, ip, asr r0
   108c0:	00001916 	andeq	r1, r0, r6, lsl r9
   108c4:	00057060 	andeq	r7, r5, r0, rrx
   108c8:	00001516 	andeq	r1, r0, r6, lsl r5
   108cc:	00057064 	andeq	r7, r5, r4, rrx
   108d0:	00002116 	andeq	r2, r0, r6, lsl r1
   108d4:	00057068 	andeq	r7, r5, r8, rrx
   108d8:	00001016 	andeq	r1, r0, r6, lsl r0
   108dc:	0005706c 	andeq	r7, r5, ip, rrx
   108e0:	00000416 	andeq	r0, r0, r6, lsl r4
   108e4:	00057070 	andeq	r7, r5, r0, ror r0
   108e8:	00002316 	andeq	r2, r0, r6, lsl r3
   108ec:	00057074 	andeq	r7, r5, r4, ror r0
   108f0:	00001d16 	andeq	r1, r0, r6, lsl sp
   108f4:	00057078 	andeq	r7, r5, r8, ror r0
   108f8:	00000c16 	andeq	r0, r0, r6, lsl ip
   108fc:	0005707c 	andeq	r7, r5, ip, ror r0
   10900:	00002b16 	andeq	r2, r0, r6, lsl fp
   10904:	00057080 	andeq	r7, r5, r0, lsl #1
   10908:	00002416 	andeq	r2, r0, r6, lsl r4
   1090c:	00057084 	andeq	r7, r5, r4, lsl #1
   10910:	00000a16 	andeq	r0, r0, r6, lsl sl
   10914:	00057088 	andeq	r7, r5, r8, lsl #1
   10918:	00001416 	andeq	r1, r0, r6, lsl r4

Disassembly of section .plt:

0001091c <pthread_mutex_unlock@plt-0x14>:
   1091c:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   10920:	e59fe004 	ldr	lr, [pc, #4]	; 1092c <pthread_mutex_unlock@plt-0x4>
   10924:	e08fe00e 	add	lr, pc, lr
   10928:	e5bef008 	ldr	pc, [lr, #8]!
   1092c:	000466d4 	ldrdeq	r6, [r4], -r4

00010930 <pthread_mutex_unlock@plt>:
   10930:	e28fc600 	add	ip, pc, #0, 12
   10934:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10938:	e5bcf6d4 	ldr	pc, [ip, #1748]!	; 0x6d4

0001093c <strcmp@plt>:
   1093c:	e28fc600 	add	ip, pc, #0, 12
   10940:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10944:	e5bcf6cc 	ldr	pc, [ip, #1740]!	; 0x6cc

00010948 <printf@plt>:
   10948:	e28fc600 	add	ip, pc, #0, 12
   1094c:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10950:	e5bcf6c4 	ldr	pc, [ip, #1732]!	; 0x6c4

00010954 <fopen@plt>:
   10954:	e28fc600 	add	ip, pc, #0, 12
   10958:	e28cca46 	add	ip, ip, #286720	; 0x46000
   1095c:	e5bcf6bc 	ldr	pc, [ip, #1724]!	; 0x6bc

00010960 <free@plt>:
   10960:	e28fc600 	add	ip, pc, #0, 12
   10964:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10968:	e5bcf6b4 	ldr	pc, [ip, #1716]!	; 0x6b4

0001096c <pthread_mutex_lock@plt>:
   1096c:	e28fc600 	add	ip, pc, #0, 12
   10970:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10974:	e5bcf6ac 	ldr	pc, [ip, #1708]!	; 0x6ac

00010978 <memcpy@plt>:
   10978:	e28fc600 	add	ip, pc, #0, 12
   1097c:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10980:	e5bcf6a4 	ldr	pc, [ip, #1700]!	; 0x6a4

00010984 <getchar@plt>:
   10984:	e28fc600 	add	ip, pc, #0, 12
   10988:	e28cca46 	add	ip, ip, #286720	; 0x46000
   1098c:	e5bcf69c 	ldr	pc, [ip, #1692]!	; 0x69c

00010990 <ioctl@plt>:
   10990:	e28fc600 	add	ip, pc, #0, 12
   10994:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10998:	e5bcf694 	ldr	pc, [ip, #1684]!	; 0x694

0001099c <usleep@plt>:
   1099c:	e28fc600 	add	ip, pc, #0, 12
   109a0:	e28cca46 	add	ip, ip, #286720	; 0x46000
   109a4:	e5bcf68c 	ldr	pc, [ip, #1676]!	; 0x68c

000109a8 <gettimeofday@plt>:
   109a8:	e28fc600 	add	ip, pc, #0, 12
   109ac:	e28cca46 	add	ip, ip, #286720	; 0x46000
   109b0:	e5bcf684 	ldr	pc, [ip, #1668]!	; 0x684

000109b4 <puts@plt>:
   109b4:	e28fc600 	add	ip, pc, #0, 12
   109b8:	e28cca46 	add	ip, ip, #286720	; 0x46000
   109bc:	e5bcf67c 	ldr	pc, [ip, #1660]!	; 0x67c

000109c0 <malloc@plt>:
   109c0:	e28fc600 	add	ip, pc, #0, 12
   109c4:	e28cca46 	add	ip, ip, #286720	; 0x46000
   109c8:	e5bcf674 	ldr	pc, [ip, #1652]!	; 0x674

000109cc <strerror@plt>:
   109cc:	e28fc600 	add	ip, pc, #0, 12
   109d0:	e28cca46 	add	ip, ip, #286720	; 0x46000
   109d4:	e5bcf66c 	ldr	pc, [ip, #1644]!	; 0x66c

000109d8 <open@plt>:
   109d8:	e28fc600 	add	ip, pc, #0, 12
   109dc:	e28cca46 	add	ip, ip, #286720	; 0x46000
   109e0:	e5bcf664 	ldr	pc, [ip, #1636]!	; 0x664

000109e4 <syscall@plt>:
   109e4:	e28fc600 	add	ip, pc, #0, 12
   109e8:	e28cca46 	add	ip, ip, #286720	; 0x46000
   109ec:	e5bcf65c 	ldr	pc, [ip, #1628]!	; 0x65c

000109f0 <mmap@plt>:
   109f0:	e28fc600 	add	ip, pc, #0, 12
   109f4:	e28cca46 	add	ip, ip, #286720	; 0x46000
   109f8:	e5bcf654 	ldr	pc, [ip, #1620]!	; 0x654

000109fc <fprintf@plt>:
   109fc:	e28fc600 	add	ip, pc, #0, 12
   10a00:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10a04:	e5bcf64c 	ldr	pc, [ip, #1612]!	; 0x64c

00010a08 <__errno_location@plt>:
   10a08:	e28fc600 	add	ip, pc, #0, 12
   10a0c:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10a10:	e5bcf644 	ldr	pc, [ip, #1604]!	; 0x644

00010a14 <snprintf@plt>:
   10a14:	e28fc600 	add	ip, pc, #0, 12
   10a18:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10a1c:	e5bcf63c 	ldr	pc, [ip, #1596]!	; 0x63c

00010a20 <memset@plt>:
   10a20:	e28fc600 	add	ip, pc, #0, 12
   10a24:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10a28:	e5bcf634 	ldr	pc, [ip, #1588]!	; 0x634

00010a2c <putchar@plt>:
   10a2c:	e28fc600 	add	ip, pc, #0, 12
   10a30:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10a34:	e5bcf62c 	ldr	pc, [ip, #1580]!	; 0x62c

00010a38 <fclose@plt>:
   10a38:	e28fc600 	add	ip, pc, #0, 12
   10a3c:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10a40:	e5bcf624 	ldr	pc, [ip, #1572]!	; 0x624

00010a44 <munmap@plt>:
   10a44:	e28fc600 	add	ip, pc, #0, 12
   10a48:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10a4c:	e5bcf61c 	ldr	pc, [ip, #1564]!	; 0x61c

00010a50 <errx@plt>:
   10a50:	e28fc600 	add	ip, pc, #0, 12
   10a54:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10a58:	e5bcf614 	ldr	pc, [ip, #1556]!	; 0x614

00010a5c <sprintf@plt>:
   10a5c:	e28fc600 	add	ip, pc, #0, 12
   10a60:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10a64:	e5bcf60c 	ldr	pc, [ip, #1548]!	; 0x60c

00010a68 <__isoc99_scanf@plt>:
   10a68:	e28fc600 	add	ip, pc, #0, 12
   10a6c:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10a70:	e5bcf604 	ldr	pc, [ip, #1540]!	; 0x604

00010a74 <remove@plt>:
   10a74:	e28fc600 	add	ip, pc, #0, 12
   10a78:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10a7c:	e5bcf5fc 	ldr	pc, [ip, #1532]!	; 0x5fc

00010a80 <vsnprintf@plt>:
   10a80:	e28fc600 	add	ip, pc, #0, 12
   10a84:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10a88:	e5bcf5f4 	ldr	pc, [ip, #1524]!	; 0x5f4

00010a8c <atoi@plt>:
   10a8c:	e28fc600 	add	ip, pc, #0, 12
   10a90:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10a94:	e5bcf5ec 	ldr	pc, [ip, #1516]!	; 0x5ec

00010a98 <fputs@plt>:
   10a98:	e28fc600 	add	ip, pc, #0, 12
   10a9c:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10aa0:	e5bcf5e4 	ldr	pc, [ip, #1508]!	; 0x5e4

00010aa4 <close@plt>:
   10aa4:	e28fc600 	add	ip, pc, #0, 12
   10aa8:	e28cca46 	add	ip, ip, #286720	; 0x46000
   10aac:	e5bcf5dc 	ldr	pc, [ip, #1500]!	; 0x5dc

Disassembly of section .DATA_REGION_0__data:

00010ab0 <global_data>:
   10ab0:	00000171 	andeq	r0, r0, r1, ror r1

00010ab4 <motorDirPin>:
   10ab4:	00000002 	andeq	r0, r0, r2

00010ab8 <motorStepPin>:
   10ab8:	00000003 	andeq	r0, r0, r3

00010abc <mLBolus>:
   10abc:	3f000000 	svccc	0x00000000

00010ac0 <mLBolusStep>:
   10ac0:	3d4ccccd 	stclcc	12, cr12, [ip, #-820]	; 0xfffffccc

00010ac4 <serialStrReady>:
   10ac4:	00000000 	andeq	r0, r0, r0

00010ac8 <serialStrLen>:
   10ac8:	00000000 	andeq	r0, r0, r0

Disassembly of section .CODE_REGION_1_:

00020000 <processSerial>:
   20000:	e92d4830 	push	{r4, r5, fp, lr}
   20004:	e28db008 	add	fp, sp, #8
   20008:	ed2d8b02 	vpush	{d8}
   2000c:	e24dd008 	sub	sp, sp, #8
   20010:	e59f0178 	ldr	r0, [pc, #376]	; 20190 <processSerial+0x190>
   20014:	e59f1178 	ldr	r1, [pc, #376]	; 20194 <processSerial+0x194>
   20018:	e59f2178 	ldr	r2, [pc, #376]	; 20198 <processSerial+0x198>
   2001c:	e59f3178 	ldr	r3, [pc, #376]	; 2019c <processSerial+0x19c>
   20020:	e59f5178 	ldr	r5, [pc, #376]	; 201a0 <processSerial+0x1a0>
   20024:	e58d5000 	str	r5, [sp]
   20028:	fa009318 	blx	44c90 <create_files>
   2002c:	e59f4170 	ldr	r4, [pc, #368]	; 201a4 <processSerial+0x1a4>
   20030:	e59f0170 	ldr	r0, [pc, #368]	; 201a8 <processSerial+0x1a8>
   20034:	e3a01001 	mov	r1, #1
   20038:	e5841000 	str	r1, [r4]
   2003c:	e5d01000 	ldrb	r1, [r0]
   20040:	e351002b 	cmp	r1, #43	; 0x2b
   20044:	e3a08064 	mov	r8, #100	; 0x64
   20048:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   2004c:	e52d1004 	push	{r1}		; (str r1, [sp, #-4]!)
   20050:	e52d2004 	push	{r2}		; (str r2, [sp, #-4]!)
   20054:	e10f1000 	mrs	r1, CPSR
   20058:	e3a02001 	mov	r2, #1
   2005c:	eb00dd1e 	bl	574dc <__tsf_direct_jmp_cc_recording>
   20060:	e49d2004 	pop	{r2}		; (ldr r2, [sp], #4)
   20064:	e49d1004 	pop	{r1}		; (ldr r1, [sp], #4)
   20068:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   2006c:	1a000001 	bne	20078 <processSerial+0x78>
   20070:	e3a00000 	mov	r0, #0
   20074:	ea00000d 	b	200b0 <processSerial+0xb0>
   20078:	e5d00000 	ldrb	r0, [r0]
   2007c:	e350002d 	cmp	r0, #45	; 0x2d
   20080:	e3a08064 	mov	r8, #100	; 0x64
   20084:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   20088:	e52d1004 	push	{r1}		; (str r1, [sp, #-4]!)
   2008c:	e52d2004 	push	{r2}		; (str r2, [sp, #-4]!)
   20090:	e10f1000 	mrs	r1, CPSR
   20094:	e3a02001 	mov	r2, #1
   20098:	eb00dd0f 	bl	574dc <__tsf_direct_jmp_cc_recording>
   2009c:	e49d2004 	pop	{r2}		; (ldr r2, [sp], #4)
   200a0:	e49d1004 	pop	{r1}		; (ldr r1, [sp], #4)
   200a4:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   200a8:	1a00000e 	bne	200e8 <processSerial+0xe8>
   200ac:	e3a00001 	mov	r0, #1
   200b0:	eb000042 	bl	201c0 <bolus>
   200b4:	eb0000c1 	bl	203c0 <updateScreen>
   200b8:	e59f00fc 	ldr	r0, [pc, #252]	; 201bc <processSerial+0x1bc>
   200bc:	e3a05000 	mov	r5, #0
   200c0:	e5c05000 	strb	r5, [r0]
   200c4:	e59f00e0 	ldr	r0, [pc, #224]	; 201ac <processSerial+0x1ac>
   200c8:	e5805000 	str	r5, [r0]
   200cc:	fa00933a 	blx	44dbc <read_measurement>
   200d0:	e5845000 	str	r5, [r4]
   200d4:	e24bd010 	sub	sp, fp, #16
   200d8:	ecbd8b02 	vpop	{d8}
   200dc:	e8bd0830 	pop	{r4, r5, fp}
   200e0:	e49d8004 	pop	{r8}		; (ldr r8, [sp], #4)
   200e4:	eb00dd12 	bl	57534 <__tsf_bkwd_pop_pc_recording>
   200e8:	e59f50bc 	ldr	r5, [pc, #188]	; 201ac <processSerial+0x1ac>
   200ec:	e59f00b4 	ldr	r0, [pc, #180]	; 201a8 <processSerial+0x1a8>
   200f0:	e5951000 	ldr	r1, [r5]
   200f4:	eb000152 	bl	20644 <toUInt>
   200f8:	e3500000 	cmp	r0, #0
   200fc:	e3a08064 	mov	r8, #100	; 0x64
   20100:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   20104:	e52d1004 	push	{r1}		; (str r1, [sp, #-4]!)
   20108:	e52d2004 	push	{r2}		; (str r2, [sp, #-4]!)
   2010c:	e10f1000 	mrs	r1, CPSR
   20110:	e3a02000 	mov	r2, #0
   20114:	eb00dcf0 	bl	574dc <__tsf_direct_jmp_cc_recording>
   20118:	e49d2004 	pop	{r2}		; (ldr r2, [sp], #4)
   2011c:	e49d1004 	pop	{r1}		; (ldr r1, [sp], #4)
   20120:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   20124:	0a00000c 	beq	2015c <processSerial+0x15c>
   20128:	e59f0078 	ldr	r0, [pc, #120]	; 201a8 <processSerial+0x1a8>
   2012c:	e5951000 	ldr	r1, [r5]
   20130:	eb000143 	bl	20644 <toUInt>
   20134:	ee000a10 	vmov	s0, r0
   20138:	ed9f1b12 	vldr	d1, [pc, #72]	; 20188 <processSerial+0x188>
   2013c:	eeb80ac0 	vcvt.f32.s32	s0, s0
   20140:	e58d0004 	str	r0, [sp, #4]
   20144:	eeb70ac0 	vcvt.f64.f32	d0, s0
   20148:	ee800b01 	vdiv.f64	d0, d0, d1
   2014c:	eeb78bc0 	vcvt.f32.f64	s16, d0
   20150:	e59f0060 	ldr	r0, [pc, #96]	; 201b8 <processSerial+0x1b8>
   20154:	ed808a00 	vstr	s16, [r0]
   20158:	eaffffd5 	b	200b4 <processSerial+0xb4>
   2015c:	e59f004c 	ldr	r0, [pc, #76]	; 201b0 <processSerial+0x1b0>
   20160:	e3a01012 	mov	r1, #18
   20164:	eb000119 	bl	205d0 <Serial_write>
   20168:	e59f0038 	ldr	r0, [pc, #56]	; 201a8 <processSerial+0x1a8>
   2016c:	e5951000 	ldr	r1, [r5]
   20170:	eb000116 	bl	205d0 <Serial_write>
   20174:	e59f0038 	ldr	r0, [pc, #56]	; 201b4 <processSerial+0x1b4>
   20178:	e3a01002 	mov	r1, #2
   2017c:	eb000113 	bl	205d0 <Serial_write>
   20180:	eaffffcc 	b	200b8 <processSerial+0xb8>
   20184:	e1a00000 	nop			; (mov r0, r0)
   20188:	00000000 	andeq	r0, r0, r0
   2018c:	408f4000 	addmi	r4, pc, r0
   20190:	0004645c 	andeq	r6, r4, ip, asr r4
   20194:	0004646d 	andeq	r6, r4, sp, ror #8
   20198:	0004647f 	andeq	r6, r4, pc, ror r4
   2019c:	00046492 	muleq	r4, r2, r4
   201a0:	000464a0 	andeq	r6, r4, r0, lsr #9
   201a4:	000207fc 	strdeq	r0, [r2], -ip
   201a8:	000570e8 	andeq	r7, r5, r8, ror #1
   201ac:	00010ac8 	andeq	r0, r1, r8, asr #21
   201b0:	000464b3 			; <UNDEFINED> instruction: 0x000464b3
   201b4:	000464c6 	andeq	r6, r4, r6, asr #9
   201b8:	00010abc 			; <UNDEFINED> instruction: 0x00010abc
   201bc:	00010ac4 	andeq	r0, r1, r4, asr #21

000201c0 <bolus>:
   201c0:	e92d4830 	push	{r4, r5, fp, lr}
   201c4:	e28db008 	add	fp, sp, #8
   201c8:	ed2d8b02 	vpush	{d8}
   201cc:	e24dd010 	sub	sp, sp, #16
   201d0:	e59f51d4 	ldr	r5, [pc, #468]	; 203ac <bolus+0x1ec>
   201d4:	e58d000c 	str	r0, [sp, #12]
   201d8:	e59f41d0 	ldr	r4, [pc, #464]	; 203b0 <bolus+0x1f0>
   201dc:	ed950a00 	vldr	s0, [r5]
   201e0:	eeb80ac0 	vcvt.f32.s32	s0, s0
   201e4:	ed941a00 	vldr	s2, [r4]
   201e8:	ee210a00 	vmul.f32	s0, s2, s0
   201ec:	eebd0ac0 	vcvt.s32.f32	s0, s0
   201f0:	e59d000c 	ldr	r0, [sp, #12]
   201f4:	e3500000 	cmp	r0, #0
   201f8:	ed8d0a02 	vstr	s0, [sp, #8]
   201fc:	e3a08064 	mov	r8, #100	; 0x64
   20200:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   20204:	e52d1004 	push	{r1}		; (str r1, [sp, #-4]!)
   20208:	e52d2004 	push	{r2}		; (str r2, [sp, #-4]!)
   2020c:	e10f1000 	mrs	r1, CPSR
   20210:	e3a02000 	mov	r2, #0
   20214:	eb00dcb0 	bl	574dc <__tsf_direct_jmp_cc_recording>
   20218:	e49d2004 	pop	{r2}		; (ldr r2, [sp], #4)
   2021c:	e49d1004 	pop	{r1}		; (ldr r1, [sp], #4)
   20220:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   20224:	0a000026 	beq	202c4 <bolus+0x104>
   20228:	e59d000c 	ldr	r0, [sp, #12]
   2022c:	e3500001 	cmp	r0, #1
   20230:	e3a08064 	mov	r8, #100	; 0x64
   20234:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   20238:	e52d1004 	push	{r1}		; (str r1, [sp, #-4]!)
   2023c:	e52d2004 	push	{r2}		; (str r2, [sp, #-4]!)
   20240:	e10f1000 	mrs	r1, CPSR
   20244:	e3a02001 	mov	r2, #1
   20248:	eb00dca3 	bl	574dc <__tsf_direct_jmp_cc_recording>
   2024c:	e49d2004 	pop	{r2}		; (ldr r2, [sp], #4)
   20250:	e49d1004 	pop	{r1}		; (ldr r1, [sp], #4)
   20254:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   20258:	1a00002c 	bne	20310 <bolus+0x150>
   2025c:	eb000115 	bl	206b8 <led_off>
   20260:	e59f014c 	ldr	r0, [pc, #332]	; 203b4 <bolus+0x1f4>
   20264:	e3a01001 	mov	r1, #1
   20268:	e5900000 	ldr	r0, [r0]
   2026c:	eb0000ce 	bl	205ac <digitalWrite>
   20270:	e59f5140 	ldr	r5, [pc, #320]	; 203b8 <bolus+0x1f8>
   20274:	ed940a00 	vldr	s0, [r4]
   20278:	ed951a00 	vldr	s2, [r5]
   2027c:	ee310a40 	vsub.f32	s0, s2, s0
   20280:	eeb50ac0 	vcmpe.f32	s0, #0.0
   20284:	eef1fa10 	vmrs	APSR_nzcv, fpscr
   20288:	e3a08064 	mov	r8, #100	; 0x64
   2028c:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   20290:	e52d1004 	push	{r1}		; (str r1, [sp, #-4]!)
   20294:	e52d2004 	push	{r2}		; (str r2, [sp, #-4]!)
   20298:	e10f1000 	mrs	r1, CPSR
   2029c:	e3a0200d 	mov	r2, #13
   202a0:	eb00dc8d 	bl	574dc <__tsf_direct_jmp_cc_recording>
   202a4:	e49d2004 	pop	{r2}		; (ldr r2, [sp], #4)
   202a8:	e49d1004 	pop	{r1}		; (ldr r1, [sp], #4)
   202ac:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   202b0:	da000014 	ble	20308 <bolus+0x148>
   202b4:	ed940a00 	vldr	s0, [r4]
   202b8:	ed951a00 	vldr	s2, [r5]
   202bc:	ee318a40 	vsub.f32	s16, s2, s0
   202c0:	ea00000e 	b	20300 <bolus+0x140>
   202c4:	eb0000ea 	bl	20674 <led_on>
   202c8:	e59f00e4 	ldr	r0, [pc, #228]	; 203b4 <bolus+0x1f4>
   202cc:	e3a01000 	mov	r1, #0
   202d0:	e5900000 	ldr	r0, [r0]
   202d4:	eb0000b4 	bl	205ac <digitalWrite>
   202d8:	ed950a00 	vldr	s0, [r5]
   202dc:	e59f50d4 	ldr	r5, [pc, #212]	; 203b8 <bolus+0x1f8>
   202e0:	eeb80ac0 	vcvt.f32.s32	s0, s0
   202e4:	ed941a00 	vldr	s2, [r4]
   202e8:	ee210a00 	vmul.f32	s0, s2, s0
   202ec:	eebd0ac0 	vcvt.s32.f32	s0, s0
   202f0:	ed951a00 	vldr	s2, [r5]
   202f4:	ed8d0a02 	vstr	s0, [sp, #8]
   202f8:	ed940a00 	vldr	s0, [r4]
   202fc:	ee318a00 	vadd.f32	s16, s2, s0
   20300:	ed858a00 	vstr	s16, [r5]
   20304:	ea000001 	b	20310 <bolus+0x150>
   20308:	e3a00000 	mov	r0, #0
   2030c:	e5850000 	str	r0, [r5]
   20310:	e59f40a4 	ldr	r4, [pc, #164]	; 203bc <bolus+0x1fc>
   20314:	e3a007b2 	mov	r0, #46661632	; 0x2c80000
   20318:	e3800101 	orr	r0, r0, #1073741824	; 0x40000000
   2031c:	e58d0004 	str	r0, [sp, #4]
   20320:	e3a00000 	mov	r0, #0
   20324:	e58d0000 	str	r0, [sp]
   20328:	ea00000c 	b	20360 <bolus+0x1a0>
   2032c:	e5940000 	ldr	r0, [r4]
   20330:	e3a01000 	mov	r1, #0
   20334:	eb00009c 	bl	205ac <digitalWrite>
   20338:	ed9d0a01 	vldr	s0, [sp, #4]
   2033c:	eb0000b5 	bl	20618 <delayMicroseconds>
   20340:	e5940000 	ldr	r0, [r4]
   20344:	e3a01001 	mov	r1, #1
   20348:	eb000097 	bl	205ac <digitalWrite>
   2034c:	ed9d0a01 	vldr	s0, [sp, #4]
   20350:	eb0000b0 	bl	20618 <delayMicroseconds>
   20354:	e59d0000 	ldr	r0, [sp]
   20358:	e2800001 	add	r0, r0, #1
   2035c:	e58d0000 	str	r0, [sp]
   20360:	e59d0008 	ldr	r0, [sp, #8]
   20364:	e59d1000 	ldr	r1, [sp]
   20368:	e1510000 	cmp	r1, r0
   2036c:	e3a08064 	mov	r8, #100	; 0x64
   20370:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   20374:	e52d1004 	push	{r1}		; (str r1, [sp, #-4]!)
   20378:	e52d2004 	push	{r2}		; (str r2, [sp, #-4]!)
   2037c:	e10f1000 	mrs	r1, CPSR
   20380:	e3a0200b 	mov	r2, #11
   20384:	eb00dc54 	bl	574dc <__tsf_direct_jmp_cc_recording>
   20388:	e49d2004 	pop	{r2}		; (ldr r2, [sp], #4)
   2038c:	e49d1004 	pop	{r1}		; (ldr r1, [sp], #4)
   20390:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   20394:	baffffe4 	blt	2032c <bolus+0x16c>
   20398:	e24bd010 	sub	sp, fp, #16
   2039c:	ecbd8b02 	vpop	{d8}
   203a0:	e8bd0830 	pop	{r4, r5, fp}
   203a4:	e49d8004 	pop	{r8}		; (ldr r8, [sp], #4)
   203a8:	eb00dc61 	bl	57534 <__tsf_bkwd_pop_pc_recording>
   203ac:	000207b8 			; <UNDEFINED> instruction: 0x000207b8
   203b0:	00010abc 			; <UNDEFINED> instruction: 0x00010abc
   203b4:	00010ab4 			; <UNDEFINED> instruction: 0x00010ab4
   203b8:	00020800 	andeq	r0, r2, r0, lsl #16
   203bc:	00010ab8 			; <UNDEFINED> instruction: 0x00010ab8

000203c0 <updateScreen>:
   203c0:	e92d4c10 	push	{r4, sl, fp, lr}
   203c4:	e28db008 	add	fp, sp, #8
   203c8:	ed2d8b04 	vpush	{d8-d9}
   203cc:	e24dd0a8 	sub	sp, sp, #168	; 0xa8
   203d0:	e59f01b0 	ldr	r0, [pc, #432]	; 20588 <updateScreen+0x1c8>
   203d4:	e3a01000 	mov	r1, #0
   203d8:	e58d1004 	str	r1, [sp, #4]
   203dc:	e58d1000 	str	r1, [sp]
   203e0:	e5901000 	ldr	r1, [r0]
   203e4:	e3510000 	cmp	r1, #0
   203e8:	e3a08064 	mov	r8, #100	; 0x64
   203ec:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   203f0:	e52d1004 	push	{r1}		; (str r1, [sp, #-4]!)
   203f4:	e52d2004 	push	{r2}		; (str r2, [sp, #-4]!)
   203f8:	e10f1000 	mrs	r1, CPSR
   203fc:	e3a02000 	mov	r2, #0
   20400:	eb00dc35 	bl	574dc <__tsf_direct_jmp_cc_recording>
   20404:	e49d2004 	pop	{r2}		; (ldr r2, [sp], #4)
   20408:	e49d1004 	pop	{r1}		; (ldr r1, [sp], #4)
   2040c:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   20410:	0a00001d 	beq	2048c <updateScreen+0xcc>
   20414:	e5900000 	ldr	r0, [r0]
   20418:	e3500001 	cmp	r0, #1
   2041c:	e3a08064 	mov	r8, #100	; 0x64
   20420:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   20424:	e52d1004 	push	{r1}		; (str r1, [sp, #-4]!)
   20428:	e52d2004 	push	{r2}		; (str r2, [sp, #-4]!)
   2042c:	e10f1000 	mrs	r1, CPSR
   20430:	e3a02001 	mov	r2, #1
   20434:	eb00dc28 	bl	574dc <__tsf_direct_jmp_cc_recording>
   20438:	e49d2004 	pop	{r2}		; (ldr r2, [sp], #4)
   2043c:	e49d1004 	pop	{r1}		; (ldr r1, [sp], #4)
   20440:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   20444:	1a000032 	bne	20514 <updateScreen+0x154>
   20448:	e59f113c 	ldr	r1, [pc, #316]	; 2058c <updateScreen+0x1cc>
   2044c:	e28d0058 	add	r0, sp, #88	; 0x58
   20450:	ebffc181 	bl	10a5c <sprintf@plt>
   20454:	e59f1134 	ldr	r1, [pc, #308]	; 20590 <updateScreen+0x1d0>
   20458:	e58d0004 	str	r0, [sp, #4]
   2045c:	ed9f1b45 	vldr	d1, [pc, #276]	; 20578 <updateScreen+0x1b8>
   20460:	ed910a00 	vldr	s0, [r1]
   20464:	ed9f3b45 	vldr	d3, [pc, #276]	; 20580 <updateScreen+0x1c0>
   20468:	e59f1124 	ldr	r1, [pc, #292]	; 20594 <updateScreen+0x1d4>
   2046c:	eeb72ac0 	vcvt.f64.f32	d2, s0
   20470:	eebd0ac0 	vcvt.s32.f32	s0, s0
   20474:	ee222b01 	vmul.f64	d2, d2, d1
   20478:	ee102a10 	vmov	r2, s0
   2047c:	eeb80bc0 	vcvt.f64.s32	d0, s0
   20480:	ee200b01 	vmul.f64	d0, d0, d1
   20484:	ee321b03 	vadd.f64	d1, d2, d3
   20488:	ea00001b 	b	204fc <updateScreen+0x13c>
   2048c:	e59f0104 	ldr	r0, [pc, #260]	; 20598 <updateScreen+0x1d8>
   20490:	ed9f8b38 	vldr	d8, [pc, #224]	; 20578 <updateScreen+0x1b8>
   20494:	ed9f9b39 	vldr	d9, [pc, #228]	; 20580 <updateScreen+0x1c0>
   20498:	ed900a00 	vldr	s0, [r0]
   2049c:	e59f10f8 	ldr	r1, [pc, #248]	; 2059c <updateScreen+0x1dc>
   204a0:	e28d0058 	add	r0, sp, #88	; 0x58
   204a4:	eeb71ac0 	vcvt.f64.f32	d1, s0
   204a8:	eebd0ac0 	vcvt.s32.f32	s0, s0
   204ac:	ee211b08 	vmul.f64	d1, d1, d8
   204b0:	ee102a10 	vmov	r2, s0
   204b4:	eeb80bc0 	vcvt.f64.s32	d0, s0
   204b8:	ee311b09 	vadd.f64	d1, d1, d9
   204bc:	ee200b08 	vmul.f64	d0, d0, d8
   204c0:	ee310b40 	vsub.f64	d0, d1, d0
   204c4:	eebd0bc0 	vcvt.s32.f64	s0, d0
   204c8:	ee103a10 	vmov	r3, s0
   204cc:	ebffc162 	bl	10a5c <sprintf@plt>
   204d0:	e59f10c8 	ldr	r1, [pc, #200]	; 205a0 <updateScreen+0x1e0>
   204d4:	e58d0004 	str	r0, [sp, #4]
   204d8:	ed910a00 	vldr	s0, [r1]
   204dc:	e59f10c0 	ldr	r1, [pc, #192]	; 205a4 <updateScreen+0x1e4>
   204e0:	eeb71ac0 	vcvt.f64.f32	d1, s0
   204e4:	eebd0ac0 	vcvt.s32.f32	s0, s0
   204e8:	ee211b08 	vmul.f64	d1, d1, d8
   204ec:	ee102a10 	vmov	r2, s0
   204f0:	eeb80bc0 	vcvt.f64.s32	d0, s0
   204f4:	ee311b09 	vadd.f64	d1, d1, d9
   204f8:	ee200b08 	vmul.f64	d0, d0, d8
   204fc:	ee310b40 	vsub.f64	d0, d1, d0
   20500:	eebd0bc0 	vcvt.s32.f64	s0, d0
   20504:	ee103a10 	vmov	r3, s0
   20508:	e28d0008 	add	r0, sp, #8
   2050c:	ebffc152 	bl	10a5c <sprintf@plt>
   20510:	e58d0000 	str	r0, [sp]
   20514:	e59f408c 	ldr	r4, [pc, #140]	; 205a8 <updateScreen+0x1e8>
   20518:	e1a00004 	mov	r0, r4
   2051c:	eb00006f 	bl	206e0 <lcd_clear>
   20520:	e1a00004 	mov	r0, r4
   20524:	e3a01000 	mov	r1, #0
   20528:	e3a02000 	mov	r2, #0
   2052c:	eb00008d 	bl	20768 <lcd_setCursor>
   20530:	e59d2004 	ldr	r2, [sp, #4]
   20534:	e28d1058 	add	r1, sp, #88	; 0x58
   20538:	e1a00004 	mov	r0, r4
   2053c:	eb000075 	bl	20718 <lcd_print>
   20540:	e1a00004 	mov	r0, r4
   20544:	e3a01000 	mov	r1, #0
   20548:	e3a02001 	mov	r2, #1
   2054c:	eb000085 	bl	20768 <lcd_setCursor>
   20550:	e59d2000 	ldr	r2, [sp]
   20554:	e28d1008 	add	r1, sp, #8
   20558:	e1a00004 	mov	r0, r4
   2055c:	eb00006d 	bl	20718 <lcd_print>
   20560:	e24bd018 	sub	sp, fp, #24
   20564:	ecbd8b04 	vpop	{d8-d9}
   20568:	e8bd0c10 	pop	{r4, sl, fp}
   2056c:	e49d8004 	pop	{r8}		; (ldr r8, [sp], #4)
   20570:	eb00dbef 	bl	57534 <__tsf_bkwd_pop_pc_recording>
   20574:	e1a00000 	nop			; (mov r0, r0)
   20578:	00000000 	andeq	r0, r0, r0
   2057c:	408f4000 	addmi	r4, pc, r0
   20580:	00000000 	andeq	r0, r0, r0
   20584:	3fe00000 	svccc	0x00e00000
   20588:	000570e4 	andeq	r7, r5, r4, ror #1
   2058c:	000464e6 	andeq	r6, r4, r6, ror #9
   20590:	00010ac0 	andeq	r0, r1, r0, asr #21
   20594:	000464f6 	strdeq	r6, [r4], -r6	; <UNPREDICTABLE>
   20598:	00020800 	andeq	r0, r2, r0, lsl #16
   2059c:	000464c9 	andeq	r6, r4, r9, asr #9
   205a0:	00010abc 			; <UNDEFINED> instruction: 0x00010abc
   205a4:	000464d7 	ldrdeq	r6, [r4], -r7
   205a8:	00057cd4 	ldrdeq	r7, [r5], -r4

000205ac <digitalWrite>:
   205ac:	e92d4800 	push	{fp, lr}
   205b0:	e1a0b00d 	mov	fp, sp
   205b4:	e24dd008 	sub	sp, sp, #8
   205b8:	e58d0004 	str	r0, [sp, #4]
   205bc:	e58d1000 	str	r1, [sp]
   205c0:	e1a0d00b 	mov	sp, fp
   205c4:	e8bd0800 	ldmfd	sp!, {fp}
   205c8:	e49d8004 	pop	{r8}		; (ldr r8, [sp], #4)
   205cc:	eb00dbd8 	bl	57534 <__tsf_bkwd_pop_pc_recording>

000205d0 <Serial_write>:
   205d0:	e92d4800 	push	{fp, lr}
   205d4:	e1a0b00d 	mov	fp, sp
   205d8:	e24dd008 	sub	sp, sp, #8
   205dc:	e58d0004 	str	r0, [sp, #4]
   205e0:	e59fc028 	ldr	ip, [pc, #40]	; 20610 <Serial_write+0x40>
   205e4:	e1a03001 	mov	r3, r1
   205e8:	e59f1024 	ldr	r1, [pc, #36]	; 20614 <Serial_write+0x44>
   205ec:	e59d2004 	ldr	r2, [sp, #4]
   205f0:	e1a0000c 	mov	r0, ip
   205f4:	e58d3000 	str	r3, [sp]
   205f8:	ebffc0d2 	bl	10948 <printf@plt>
   205fc:	e3a00000 	mov	r0, #0
   20600:	e1a0d00b 	mov	sp, fp
   20604:	e8bd0800 	ldmfd	sp!, {fp}
   20608:	e49d8004 	pop	{r8}		; (ldr r8, [sp], #4)
   2060c:	eb00dbc8 	bl	57534 <__tsf_bkwd_pop_pc_recording>
   20610:	000465a7 	andeq	r6, r4, r7, lsr #11
   20614:	000207bc 			; <UNDEFINED> instruction: 0x000207bc

00020618 <delayMicroseconds>:
   20618:	e92d4800 	push	{fp, lr}
   2061c:	e1a0b00d 	mov	fp, sp
   20620:	e24dd008 	sub	sp, sp, #8
   20624:	ed8d0a01 	vstr	s0, [sp, #4]
   20628:	eebd0ac0 	vcvt.s32.f32	s0, s0
   2062c:	ee100a10 	vmov	r0, s0
   20630:	ebffc0d9 	bl	1099c <usleep@plt>
   20634:	e1a0d00b 	mov	sp, fp
   20638:	e8bd0800 	ldmfd	sp!, {fp}
   2063c:	e49d8004 	pop	{r8}		; (ldr r8, [sp], #4)
   20640:	eb00dbbb 	bl	57534 <__tsf_bkwd_pop_pc_recording>

00020644 <toUInt>:
   20644:	e92d4800 	push	{fp, lr}
   20648:	e1a0b00d 	mov	fp, sp
   2064c:	e24dd010 	sub	sp, sp, #16
   20650:	e50b0004 	str	r0, [fp, #-4]
   20654:	e51b0004 	ldr	r0, [fp, #-4]
   20658:	e58d1008 	str	r1, [sp, #8]
   2065c:	ebffc10a 	bl	10a8c <atoi@plt>
   20660:	e58d0004 	str	r0, [sp, #4]
   20664:	e1a0d00b 	mov	sp, fp
   20668:	e8bd0800 	ldmfd	sp!, {fp}
   2066c:	e49d8004 	pop	{r8}		; (ldr r8, [sp], #4)
   20670:	eb00dbaf 	bl	57534 <__tsf_bkwd_pop_pc_recording>

00020674 <led_on>:
   20674:	e92d48f0 	push	{r4, r5, r6, r7, fp, lr}
   20678:	e28db010 	add	fp, sp, #16
   2067c:	e59f6028 	ldr	r6, [pc, #40]	; 206ac <led_on+0x38>
   20680:	e59f4028 	ldr	r4, [pc, #40]	; 206b0 <led_on+0x3c>
   20684:	e59f5028 	ldr	r5, [pc, #40]	; 206b4 <led_on+0x40>
   20688:	e5960000 	ldr	r0, [r6]
   2068c:	e2807001 	add	r7, r0, #1
   20690:	e1a00004 	mov	r0, r4
   20694:	e1a01005 	mov	r1, r5
   20698:	e5867000 	str	r7, [r6]
   2069c:	ebffc0a9 	bl	10948 <printf@plt>
   206a0:	e8bd08f0 	pop	{r4, r5, r6, r7, fp}
   206a4:	e49d8004 	pop	{r8}		; (ldr r8, [sp], #4)
   206a8:	eb00dba1 	bl	57534 <__tsf_bkwd_pop_pc_recording>
   206ac:	00010ab0 			; <UNDEFINED> instruction: 0x00010ab0
   206b0:	000465df 	ldrdeq	r6, [r4], -pc	; <UNPREDICTABLE>
   206b4:	000207c9 	andeq	r0, r2, r9, asr #15

000206b8 <led_off>:
   206b8:	e92d4800 	push	{fp, lr}
   206bc:	e1a0b00d 	mov	fp, sp
   206c0:	e59f0010 	ldr	r0, [pc, #16]	; 206d8 <led_off+0x20>
   206c4:	e59f1010 	ldr	r1, [pc, #16]	; 206dc <led_off+0x24>
   206c8:	ebffc09e 	bl	10948 <printf@plt>
   206cc:	e8bd0800 	ldmfd	sp!, {fp}
   206d0:	e49d8004 	pop	{r8}		; (ldr r8, [sp], #4)
   206d4:	eb00db96 	bl	57534 <__tsf_bkwd_pop_pc_recording>
   206d8:	000465df 	ldrdeq	r6, [r4], -pc	; <UNPREDICTABLE>
   206dc:	000207d0 	ldrdeq	r0, [r2], -r0	; <UNPREDICTABLE>

000206e0 <lcd_clear>:
   206e0:	e92d4800 	push	{fp, lr}
   206e4:	e1a0b00d 	mov	fp, sp
   206e8:	e24dd008 	sub	sp, sp, #8
   206ec:	e59f201c 	ldr	r2, [pc, #28]	; 20710 <lcd_clear+0x30>
   206f0:	e59f101c 	ldr	r1, [pc, #28]	; 20714 <lcd_clear+0x34>
   206f4:	e58d0004 	str	r0, [sp, #4]
   206f8:	e1a00002 	mov	r0, r2
   206fc:	ebffc091 	bl	10948 <printf@plt>
   20700:	e1a0d00b 	mov	sp, fp
   20704:	e8bd0800 	ldmfd	sp!, {fp}
   20708:	e49d8004 	pop	{r8}		; (ldr r8, [sp], #4)
   2070c:	eb00db88 	bl	57534 <__tsf_bkwd_pop_pc_recording>
   20710:	00046634 	andeq	r6, r4, r4, lsr r6
   20714:	000207d8 	ldrdeq	r0, [r2], -r8

00020718 <lcd_print>:
   20718:	e92d4800 	push	{fp, lr}
   2071c:	e1a0b00d 	mov	fp, sp
   20720:	e24dd010 	sub	sp, sp, #16
   20724:	e50b0004 	str	r0, [fp, #-4]
   20728:	e58d1008 	str	r1, [sp, #8]
   2072c:	e59fc02c 	ldr	ip, [pc, #44]	; 20760 <lcd_print+0x48>
   20730:	e51be004 	ldr	lr, [fp, #-4]
   20734:	e59d3008 	ldr	r3, [sp, #8]
   20738:	e59f1024 	ldr	r1, [pc, #36]	; 20764 <lcd_print+0x4c>
   2073c:	e58d2004 	str	r2, [sp, #4]
   20740:	e58d2000 	str	r2, [sp]
   20744:	e1a0000c 	mov	r0, ip
   20748:	e1a0200e 	mov	r2, lr
   2074c:	ebffc07d 	bl	10948 <printf@plt>
   20750:	e1a0d00b 	mov	sp, fp
   20754:	e8bd0800 	ldmfd	sp!, {fp}
   20758:	e49d8004 	pop	{r8}		; (ldr r8, [sp], #4)
   2075c:	eb00db74 	bl	57534 <__tsf_bkwd_pop_pc_recording>
   20760:	00046654 	andeq	r6, r4, r4, asr r6
   20764:	000207e2 	andeq	r0, r2, r2, ror #15

00020768 <lcd_setCursor>:
   20768:	e92d4800 	push	{fp, lr}
   2076c:	e1a0b00d 	mov	fp, sp
   20770:	e24dd010 	sub	sp, sp, #16
   20774:	e59fe030 	ldr	lr, [pc, #48]	; 207ac <lcd_setCursor+0x44>
   20778:	e59fc030 	ldr	ip, [pc, #48]	; 207b0 <lcd_setCursor+0x48>
   2077c:	e58d1008 	str	r1, [sp, #8]
   20780:	e1a03002 	mov	r3, r2
   20784:	e59d2008 	ldr	r2, [sp, #8]
   20788:	e50b0004 	str	r0, [fp, #-4]
   2078c:	e1a0000e 	mov	r0, lr
   20790:	e1a0100c 	mov	r1, ip
   20794:	e58d3004 	str	r3, [sp, #4]
   20798:	ebffc06a 	bl	10948 <printf@plt>
   2079c:	e1a0d00b 	mov	sp, fp
   207a0:	e8bd0800 	ldmfd	sp!, {fp}
   207a4:	e49d8004 	pop	{r8}		; (ldr r8, [sp], #4)
   207a8:	eb00db61 	bl	57534 <__tsf_bkwd_pop_pc_recording>
   207ac:	00046696 	muleq	r4, r6, r6
   207b0:	000207ec 	andeq	r0, r2, ip, ror #15

Disassembly of section .DATA_REGION_1__share:

000207b4 <.DATA_REGION_1__sdata_start>:
   207b4:	00000000 	andeq	r0, r0, r0

Disassembly of section .DATA_REGION_1__data:

000207b8 <ustepsPerML>:
   207b8:	00001aaa 	andeq	r1, r0, sl, lsr #21
   207bc:	69726553 	ldmdbvs	r2!, {r0, r1, r4, r6, r8, sl, sp, lr}^
   207c0:	775f6c61 	ldrbvc	r6, [pc, -r1, ror #24]
   207c4:	65746972 	ldrbvs	r6, [r4, #-2418]!	; 0xfffff68e
   207c8:	64656c00 	strbtvs	r6, [r5], #-3072	; 0xfffff400
   207cc:	006e6f5f 	rsbeq	r6, lr, pc, asr pc
   207d0:	5f64656c 	svcpl	0x0064656c
   207d4:	0066666f 	rsbeq	r6, r6, pc, ror #12
   207d8:	5f64636c 	svcpl	0x0064636c
   207dc:	61656c63 	cmnvs	r5, r3, ror #24
   207e0:	636c0072 	cmnvs	ip, #114	; 0x72
   207e4:	72705f64 	rsbsvc	r5, r0, #100, 30	; 0x190
   207e8:	00746e69 	rsbseq	r6, r4, r9, ror #28
   207ec:	5f64636c 	svcpl	0x0064636c
   207f0:	43746573 	cmnmi	r4, #482344960	; 0x1cc00000
   207f4:	6f737275 	svcvs	0x00737275
   207f8:	00000072 	andeq	r0, r0, r2, ror r0

Disassembly of section .DATA_REGION_1__bss:

000207fc <recording_flag>:
   207fc:	00000000 	andeq	r0, r0, r0

00020800 <mLUsed>:
   20800:	00000000 	andeq	r0, r0, r0

Disassembly of section .CODE_REGION_2_:

00040000 <setup>:
   40000:	e92d4830 	push	{r4, r5, fp, lr}
   40004:	e28db008 	add	fp, sp, #8
   40008:	e59f40e0 	ldr	r4, [pc, #224]	; 400f0 <setup+0xf0>
   4000c:	e3a01010 	mov	r1, #16
   40010:	e3a02002 	mov	r2, #2
   40014:	e1a00004 	mov	r0, r4
   40018:	eb00026e 	bl	409d8 <lcd_begin>
   4001c:	e1a00004 	mov	r0, r4
   40020:	e30086e0 	movw	r8, #1760	; 0x6e0
   40024:	e3408002 	movt	r8, #2
   40028:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   4002c:	eb005d1b 	bl	574a0 <__tsf_direct_jmp_link_recording>
   40030:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   40034:	ebff81a9 	bl	206e0 <lcd_clear>
   40038:	e59f10b4 	ldr	r1, [pc, #180]	; 400f4 <setup+0xf4>
   4003c:	e1a00004 	mov	r0, r4
   40040:	e3a02010 	mov	r2, #16
   40044:	e3008718 	movw	r8, #1816	; 0x718
   40048:	e3408002 	movt	r8, #2
   4004c:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   40050:	eb005d12 	bl	574a0 <__tsf_direct_jmp_link_recording>
   40054:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   40058:	ebff81ae 	bl	20718 <lcd_print>
   4005c:	e59f4094 	ldr	r4, [pc, #148]	; 400f8 <setup+0xf8>
   40060:	e3a01000 	mov	r1, #0
   40064:	e5940000 	ldr	r0, [r4]
   40068:	eb0001e7 	bl	4080c <pinMode>
   4006c:	e59f5088 	ldr	r5, [pc, #136]	; 400fc <setup+0xfc>
   40070:	e3a01000 	mov	r1, #0
   40074:	e5950000 	ldr	r0, [r5]
   40078:	eb0001e3 	bl	4080c <pinMode>
   4007c:	e5944000 	ldr	r4, [r4]
   40080:	e1a00004 	mov	r0, r4
   40084:	e3a01000 	mov	r1, #0
   40088:	e30085ac 	movw	r8, #1452	; 0x5ac
   4008c:	e3408002 	movt	r8, #2
   40090:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   40094:	eb005d01 	bl	574a0 <__tsf_direct_jmp_link_recording>
   40098:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   4009c:	ebff8142 	bl	205ac <digitalWrite>
   400a0:	e5954000 	ldr	r4, [r5]
   400a4:	e1a00004 	mov	r0, r4
   400a8:	e3a01000 	mov	r1, #0
   400ac:	e30085ac 	movw	r8, #1452	; 0x5ac
   400b0:	e3408002 	movt	r8, #2
   400b4:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   400b8:	eb005cf8 	bl	574a0 <__tsf_direct_jmp_link_recording>
   400bc:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   400c0:	ebff8139 	bl	205ac <digitalWrite>
   400c4:	e59f0034 	ldr	r0, [pc, #52]	; 40100 <setup+0x100>
   400c8:	e3a01001 	mov	r1, #1
   400cc:	e5900000 	ldr	r0, [r0]
   400d0:	eb0001cd 	bl	4080c <pinMode>
   400d4:	e59f0028 	ldr	r0, [pc, #40]	; 40104 <setup+0x104>
   400d8:	e3a01001 	mov	r1, #1
   400dc:	e5900000 	ldr	r0, [r0]
   400e0:	eb0001c9 	bl	4080c <pinMode>
   400e4:	e3a00ce1 	mov	r0, #57600	; 0xe100
   400e8:	eb0001e7 	bl	4088c <Serial_begin>
   400ec:	e8bd8830 	pop	{r4, r5, fp, pc}
   400f0:	00057cd4 	ldrdeq	r7, [r5], -r4
   400f4:	0004642c 	andeq	r6, r4, ip, lsr #8
   400f8:	00040ac4 	andeq	r0, r4, r4, asr #21
   400fc:	00040ac8 	andeq	r0, r4, r8, asr #21
   40100:	00010ab4 			; <UNDEFINED> instruction: 0x00010ab4
   40104:	00010ab8 			; <UNDEFINED> instruction: 0x00010ab8

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
   40150:	eb000214 	bl	409a8 <usecs>
   40154:	e58d0008 	str	r0, [sp, #8]
   40158:	e5d50000 	ldrb	r0, [r5]
   4015c:	e3100001 	tst	r0, #1
   40160:	0a000005 	beq	4017c <loop+0x74>
   40164:	e3008000 	movw	r8, #0
   40168:	e3408002 	movt	r8, #2
   4016c:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   40170:	eb005cca 	bl	574a0 <__tsf_direct_jmp_link_recording>
   40174:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   40178:	ebff7fa0 	bl	20000 <processSerial>
   4017c:	eb000209 	bl	409a8 <usecs>
   40180:	ed940a00 	vldr	s0, [r4]
   40184:	e59d5008 	ldr	r5, [sp, #8]
   40188:	e59f103c 	ldr	r1, [pc, #60]	; 401cc <loop+0xc4>
   4018c:	e58d0004 	str	r0, [sp, #4]
   40190:	eeb70ac0 	vcvt.f64.f32	d0, s0
   40194:	e0400005 	sub	r0, r0, r5
   40198:	e58d0000 	str	r0, [sp]
   4019c:	e1a00001 	mov	r0, r1
   401a0:	ec532b10 	vmov	r2, r3, d0
   401a4:	ebff41e7 	bl	10948 <printf@plt>
   401a8:	e24bd010 	sub	sp, fp, #16
   401ac:	ecbd8b02 	vpop	{d8}
   401b0:	e8bd8830 	pop	{r4, r5, fp, pc}
   401b4:	e1a00000 	nop			; (mov r0, r0)
   401b8:	d2f1a9fc 	rscsle	sl, r1, #252, 18	; 0x3f0000
   401bc:	3f50624d 	svccc	0x0050624d
   401c0:	00010abc 			; <UNDEFINED> instruction: 0x00010abc
   401c4:	000570e8 	andeq	r7, r5, r8, ror #1
   401c8:	00010ac4 	andeq	r0, r1, r4, asr #21
   401cc:	0004643d 	andeq	r6, r4, sp, lsr r4

000401d0 <checkTriggers>:
   401d0:	e92d4c10 	push	{r4, sl, fp, lr}
   401d4:	e28db008 	add	fp, sp, #8
   401d8:	ed2d8b02 	vpush	{d8}
   401dc:	e24dd010 	sub	sp, sp, #16
   401e0:	e59f010c 	ldr	r0, [pc, #268]	; 402f4 <checkTriggers+0x124>
   401e4:	e5900000 	ldr	r0, [r0]
   401e8:	eb000196 	bl	40848 <digitalRead>
   401ec:	e58d000c 	str	r0, [sp, #12]
   401f0:	e3500000 	cmp	r0, #0
   401f4:	1a000010 	bne	4023c <checkTriggers+0x6c>
   401f8:	e59f00f8 	ldr	r0, [pc, #248]	; 402f8 <checkTriggers+0x128>
   401fc:	e5900000 	ldr	r0, [r0]
   40200:	e3500001 	cmp	r0, #1
   40204:	1a00000c 	bne	4023c <checkTriggers+0x6c>
   40208:	e3a00000 	mov	r0, #0
   4020c:	e30081c0 	movw	r8, #448	; 0x1c0
   40210:	e3408002 	movt	r8, #2
   40214:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   40218:	eb005ca0 	bl	574a0 <__tsf_direct_jmp_link_recording>
   4021c:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   40220:	ebff7fe6 	bl	201c0 <bolus>
   40224:	e30083c0 	movw	r8, #960	; 0x3c0
   40228:	e3408002 	movt	r8, #2
   4022c:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   40230:	eb005c9a 	bl	574a0 <__tsf_direct_jmp_link_recording>
   40234:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   40238:	ebff8060 	bl	203c0 <updateScreen>
   4023c:	e59d400c 	ldr	r4, [sp, #12]
   40240:	e59f00b0 	ldr	r0, [pc, #176]	; 402f8 <checkTriggers+0x128>
   40244:	e59f10b0 	ldr	r1, [pc, #176]	; 402fc <checkTriggers+0x12c>
   40248:	e3008000 	movw	r8, #0
   4024c:	e3408000 	movt	r8, #0
   40250:	e7d78010 	bfi	r8, r0, #0, #24
   40254:	e5884000 	str	r4, [r8]
   40258:	e5910000 	ldr	r0, [r1]
   4025c:	eb000179 	bl	40848 <digitalRead>
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
   40298:	e30081c0 	movw	r8, #448	; 0x1c0
   4029c:	e3408002 	movt	r8, #2
   402a0:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   402a4:	eb005c7d 	bl	574a0 <__tsf_direct_jmp_link_recording>
   402a8:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   402ac:	ebff7fc3 	bl	201c0 <bolus>
   402b0:	ed9d8a01 	vldr	s16, [sp, #4]
   402b4:	ed848a00 	vstr	s16, [r4]
   402b8:	e30083c0 	movw	r8, #960	; 0x3c0
   402bc:	e3408002 	movt	r8, #2
   402c0:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   402c4:	eb005c75 	bl	574a0 <__tsf_direct_jmp_link_recording>
   402c8:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   402cc:	ebff803b 	bl	203c0 <updateScreen>
   402d0:	e59d4008 	ldr	r4, [sp, #8]
   402d4:	e59f0024 	ldr	r0, [pc, #36]	; 40300 <checkTriggers+0x130>
   402d8:	e3008000 	movw	r8, #0
   402dc:	e3408000 	movt	r8, #0
   402e0:	e7d78010 	bfi	r8, r0, #0, #24
   402e4:	e5884000 	str	r4, [r8]
   402e8:	e24bd010 	sub	sp, fp, #16
   402ec:	ecbd8b02 	vpop	{d8}
   402f0:	e8bd8c10 	pop	{r4, sl, fp, pc}
   402f4:	00040ac4 	andeq	r0, r4, r4, asr #21
   402f8:	00040ad4 	ldrdeq	r0, [r4], -r4
   402fc:	00040ac8 	andeq	r0, r4, r8, asr #21
   40300:	00040ad0 	ldrdeq	r0, [r4], -r0	; <UNPREDICTABLE>
   40304:	00010abc 			; <UNDEFINED> instruction: 0x00010abc
   40308:	00040a74 	andeq	r0, r4, r4, ror sl

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
   40344:	eb00015c 	bl	408bc <Serial_available>
   40348:	e3500000 	cmp	r0, #0
   4034c:	0a000006 	beq	4036c <readSerial+0x60>
   40350:	eb00016d 	bl	4090c <Serial_read>
   40354:	e5cd0007 	strb	r0, [sp, #7]
   40358:	e5dd0007 	ldrb	r0, [sp, #7]
   4035c:	e350001f 	cmp	r0, #31
   40360:	cafffff1 	bgt	4032c <readSerial+0x20>
   40364:	e5c95000 	strb	r5, [r9]
   40368:	eafffff5 	b	40344 <readSerial+0x38>
   4036c:	e24bd018 	sub	sp, fp, #24
   40370:	e8bd8ef0 	pop	{r4, r5, r6, r7, r9, sl, fp, pc}
   40374:	00010ac8 	andeq	r0, r1, r8, asr #21
   40378:	000570e8 	andeq	r7, r5, r8, ror #1
   4037c:	00010ac4 	andeq	r0, r1, r4, asr #21

00040380 <readKey>:
   40380:	e92d48f0 	push	{r4, r5, r6, r7, fp, lr}
   40384:	e28db010 	add	fp, sp, #16
   40388:	e24dd010 	sub	sp, sp, #16
   4038c:	e3a00000 	mov	r0, #0
   40390:	e3a07000 	mov	r7, #0
   40394:	eb000164 	bl	4092c <analogRead>
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
   403d0:	eb000164 	bl	40968 <millis>
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
   40490:	00057cd0 	ldrdeq	r7, [r5], -r0
   40494:	00040a4c 	andeq	r0, r4, ip, asr #20
   40498:	00040acc 	andeq	r0, r4, ip, asr #21
   4049c:	00040a84 	andeq	r0, r4, r4, lsl #21
   404a0:	00040a7c 	andeq	r0, r4, ip, ror sl
   404a4:	00040a80 	andeq	r0, r4, r0, lsl #21

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
   40520:	00040a48 	andeq	r0, r4, r8, asr #20
   40524:	00040a34 	andeq	r0, r4, r4, lsr sl

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
   4063c:	e30081c0 	movw	r8, #448	; 0x1c0
   40640:	e3408002 	movt	r8, #2
   40644:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   40648:	eb005b94 	bl	574a0 <__tsf_direct_jmp_link_recording>
   4064c:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   40650:	ebff7eda 	bl	201c0 <bolus>
   40654:	e59d0004 	ldr	r0, [sp, #4]
   40658:	e3500000 	cmp	r0, #0
   4065c:	1a000006 	bne	4067c <doKeyAction+0x154>
   40660:	e3a00000 	mov	r0, #0
   40664:	e30081c0 	movw	r8, #448	; 0x1c0
   40668:	e3408002 	movt	r8, #2
   4066c:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   40670:	eb005b8a 	bl	574a0 <__tsf_direct_jmp_link_recording>
   40674:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   40678:	ebff7ed0 	bl	201c0 <bolus>
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
   406e8:	e30083c0 	movw	r8, #960	; 0x3c0
   406ec:	e3408002 	movt	r8, #2
   406f0:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   406f4:	eb005b69 	bl	574a0 <__tsf_direct_jmp_link_recording>
   406f8:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   406fc:	ebff7f2f 	bl	203c0 <updateScreen>
   40700:	e24bd018 	sub	sp, fp, #24
   40704:	ecbd8b02 	vpop	{d8}
   40708:	e8bd8c70 	pop	{r4, r5, r6, sl, fp, pc}
   4070c:	000570e4 	andeq	r7, r5, r4, ror #1
   40710:	00040a78 	andeq	r0, r4, r8, ror sl
   40714:	00040a50 	andeq	r0, r4, r0, asr sl
   40718:	00010ac0 	andeq	r0, r1, r0, asr #21
   4071c:	00010abc 			; <UNDEFINED> instruction: 0x00010abc

00040720 <forward_target>:
   40720:	e92d4800 	push	{fp, lr}
   40724:	e1a0b00d 	mov	fp, sp
   40728:	e24dd008 	sub	sp, sp, #8
   4072c:	e59f1010 	ldr	r1, [pc, #16]	; 40744 <forward_target+0x24>
   40730:	e58d0004 	str	r0, [sp, #4]
   40734:	e1a00001 	mov	r0, r1
   40738:	ebff4082 	bl	10948 <printf@plt>
   4073c:	e1a0d00b 	mov	sp, fp
   40740:	e8bd8800 	pop	{fp, pc}
   40744:	000464fc 	strdeq	r6, [r4], -ip

00040748 <main>:
   40748:	e92d4800 	push	{fp, lr}
   4074c:	e1a0b00d 	mov	fp, sp
   40750:	e24dd018 	sub	sp, sp, #24
   40754:	e59f2098 	ldr	r2, [pc, #152]	; 407f4 <main+0xac>
   40758:	e3a03000 	mov	r3, #0
   4075c:	e90b0009 	stmdb	fp, {r0, r3}
   40760:	e1a00002 	mov	r0, r2
   40764:	e58d100c 	str	r1, [sp, #12]
   40768:	ebff4076 	bl	10948 <printf@plt>
   4076c:	e59f0084 	ldr	r0, [pc, #132]	; 407f8 <main+0xb0>
   40770:	ebff4074 	bl	10948 <printf@plt>
   40774:	ebfffe21 	bl	40000 <setup>
   40778:	e59f107c 	ldr	r1, [pc, #124]	; 407fc <main+0xb4>
   4077c:	e3a00002 	mov	r0, #2
   40780:	e58d1008 	str	r1, [sp, #8]
   40784:	e3008000 	movw	r8, #0
   40788:	e3408000 	movt	r8, #0
   4078c:	e7d78011 	bfi	r8, r1, #0, #24
   40790:	e12fff38 	blx	r8
   40794:	e59f3064 	ldr	r3, [pc, #100]	; 40800 <main+0xb8>
   40798:	e59f0064 	ldr	r0, [pc, #100]	; 40804 <main+0xbc>
   4079c:	e3a01010 	mov	r1, #16
   407a0:	e3a02002 	mov	r2, #2
   407a4:	e58d3004 	str	r3, [sp, #4]
   407a8:	e3008000 	movw	r8, #0
   407ac:	e3408000 	movt	r8, #0
   407b0:	e7d78013 	bfi	r8, r3, #0, #24
   407b4:	e12fff38 	blx	r8
   407b8:	e3a00001 	mov	r0, #1
   407bc:	e58d0000 	str	r0, [sp]
   407c0:	ea000003 	b	407d4 <main+0x8c>
   407c4:	e59d0000 	ldr	r0, [sp]
   407c8:	e280000a 	add	r0, r0, #10
   407cc:	e58d0000 	str	r0, [sp]
   407d0:	ebfffe4c 	bl	40108 <loop>
   407d4:	e59d0000 	ldr	r0, [sp]
   407d8:	e350003d 	cmp	r0, #61	; 0x3d
   407dc:	dafffff8 	ble	407c4 <main+0x7c>
   407e0:	e59f0020 	ldr	r0, [pc, #32]	; 40808 <main+0xc0>
   407e4:	ebff4057 	bl	10948 <printf@plt>
   407e8:	e3a00000 	mov	r0, #0
   407ec:	e1a0d00b 	mov	sp, fp
   407f0:	e8bd8800 	pop	{fp, pc}
   407f4:	00046517 	andeq	r6, r4, r7, lsl r5
   407f8:	0004652e 	andeq	r6, r4, lr, lsr #10
   407fc:	00040720 	andeq	r0, r4, r0, lsr #14
   40800:	000409d8 	ldrdeq	r0, [r4], -r8
   40804:	00057cd4 	ldrdeq	r7, [r5], -r4
   40808:	0004653e 	andeq	r6, r4, lr, lsr r5

0004080c <pinMode>:
   4080c:	e92d4800 	push	{fp, lr}
   40810:	e1a0b00d 	mov	fp, sp
   40814:	e24dd008 	sub	sp, sp, #8
   40818:	e58d0004 	str	r0, [sp, #4]
   4081c:	e59fc01c 	ldr	ip, [pc, #28]	; 40840 <pinMode+0x34>
   40820:	e1a03001 	mov	r3, r1
   40824:	e59f1018 	ldr	r1, [pc, #24]	; 40844 <pinMode+0x38>
   40828:	e59d2004 	ldr	r2, [sp, #4]
   4082c:	e1a0000c 	mov	r0, ip
   40830:	e58d3000 	str	r3, [sp]
   40834:	ebff4043 	bl	10948 <printf@plt>
   40838:	e1a0d00b 	mov	sp, fp
   4083c:	e8bd8800 	pop	{fp, pc}
   40840:	00046553 	andeq	r6, r4, r3, asr r5
   40844:	00040a88 	andeq	r0, r4, r8, lsl #21

00040848 <digitalRead>:
   40848:	e92d4800 	push	{fp, lr}
   4084c:	e1a0b00d 	mov	fp, sp
   40850:	e24dd008 	sub	sp, sp, #8
   40854:	e1a02000 	mov	r2, r0
   40858:	e59f0020 	ldr	r0, [pc, #32]	; 40880 <digitalRead+0x38>
   4085c:	e59f1020 	ldr	r1, [pc, #32]	; 40884 <digitalRead+0x3c>
   40860:	e58d2004 	str	r2, [sp, #4]
   40864:	ebff4037 	bl	10948 <printf@plt>
   40868:	e59f0018 	ldr	r0, [pc, #24]	; 40888 <digitalRead+0x40>
   4086c:	e1a0100d 	mov	r1, sp
   40870:	ebff407c 	bl	10a68 <__isoc99_scanf@plt>
   40874:	e59d0000 	ldr	r0, [sp]
   40878:	e1a0d00b 	mov	sp, fp
   4087c:	e8bd8800 	pop	{fp, pc}
   40880:	00046575 	andeq	r6, r4, r5, ror r5
   40884:	00040a90 	muleq	r4, r0, sl
   40888:	000464f9 	strdeq	r6, [r4], -r9

0004088c <Serial_begin>:
   4088c:	e92d4800 	push	{fp, lr}
   40890:	e1a0b00d 	mov	fp, sp
   40894:	e24dd008 	sub	sp, sp, #8
   40898:	e1a02000 	mov	r2, r0
   4089c:	e59f0010 	ldr	r0, [pc, #16]	; 408b4 <Serial_begin+0x28>
   408a0:	e59f1010 	ldr	r1, [pc, #16]	; 408b8 <Serial_begin+0x2c>
   408a4:	e58d2004 	str	r2, [sp, #4]
   408a8:	ebff4026 	bl	10948 <printf@plt>
   408ac:	e1a0d00b 	mov	sp, fp
   408b0:	e8bd8800 	pop	{fp, pc}
   408b4:	00046588 	andeq	r6, r4, r8, lsl #11
   408b8:	00040a9c 	muleq	r4, ip, sl

000408bc <Serial_available>:
   408bc:	e92d4800 	push	{fp, lr}
   408c0:	e1a0b00d 	mov	fp, sp
   408c4:	e24dd008 	sub	sp, sp, #8
   408c8:	ebff402d 	bl	10984 <getchar@plt>
   408cc:	e5cd0003 	strb	r0, [sp, #3]
   408d0:	e59f302c 	ldr	r3, [pc, #44]	; 40904 <Serial_available+0x48>
   408d4:	e59f102c 	ldr	r1, [pc, #44]	; 40908 <Serial_available+0x4c>
   408d8:	e5dd2003 	ldrb	r2, [sp, #3]
   408dc:	e1a00003 	mov	r0, r3
   408e0:	ebff4018 	bl	10948 <printf@plt>
   408e4:	e5dd0003 	ldrb	r0, [sp, #3]
   408e8:	e3500079 	cmp	r0, #121	; 0x79
   408ec:	13a00000 	movne	r0, #0
   408f0:	03a00001 	moveq	r0, #1
   408f4:	e58d0004 	str	r0, [sp, #4]
   408f8:	e59d0004 	ldr	r0, [sp, #4]
   408fc:	e1a0d00b 	mov	sp, fp
   40900:	e8bd8800 	pop	{fp, pc}
   40904:	0004659c 	muleq	r4, ip, r5
   40908:	00040aa9 	andeq	r0, r4, r9, lsr #21

0004090c <Serial_read>:
   4090c:	e92d4800 	push	{fp, lr}
   40910:	e1a0b00d 	mov	fp, sp
   40914:	e24dd008 	sub	sp, sp, #8
   40918:	ebff4019 	bl	10984 <getchar@plt>
   4091c:	e54b0001 	strb	r0, [fp, #-1]
   40920:	e55b0001 	ldrb	r0, [fp, #-1]
   40924:	e1a0d00b 	mov	sp, fp
   40928:	e8bd8800 	pop	{fp, pc}

0004092c <analogRead>:
   4092c:	e92d4800 	push	{fp, lr}
   40930:	e1a0b00d 	mov	fp, sp
   40934:	e24dd008 	sub	sp, sp, #8
   40938:	e1a01000 	mov	r1, r0
   4093c:	e59f001c 	ldr	r0, [pc, #28]	; 40960 <analogRead+0x34>
   40940:	e58d1004 	str	r1, [sp, #4]
   40944:	ebff3fff 	bl	10948 <printf@plt>
   40948:	e59f0014 	ldr	r0, [pc, #20]	; 40964 <analogRead+0x38>
   4094c:	e1a0100d 	mov	r1, sp
   40950:	ebff4044 	bl	10a68 <__isoc99_scanf@plt>
   40954:	e59d0000 	ldr	r0, [sp]
   40958:	e1a0d00b 	mov	sp, fp
   4095c:	e8bd8800 	pop	{fp, pc}
   40960:	000465cd 	andeq	r6, r4, sp, asr #11
   40964:	000464f9 	strdeq	r6, [r4], -r9

00040968 <millis>:
   40968:	e92d4800 	push	{fp, lr}
   4096c:	e1a0b00d 	mov	fp, sp
   40970:	e24dd008 	sub	sp, sp, #8
   40974:	e1a0000d 	mov	r0, sp
   40978:	e3a01000 	mov	r1, #0
   4097c:	ebff4009 	bl	109a8 <gettimeofday@plt>
   40980:	e59f001c 	ldr	r0, [pc, #28]	; 409a4 <millis+0x3c>
   40984:	e89d0006 	ldm	sp, {r1, r2}
   40988:	e750f012 	smmul	r0, r2, r0
   4098c:	e1a02340 	asr	r2, r0, #6
   40990:	e0820fa0 	add	r0, r2, r0, lsr #31
   40994:	e3a02ffa 	mov	r2, #1000	; 0x3e8
   40998:	e0200291 	mla	r0, r1, r2, r0
   4099c:	e1a0d00b 	mov	sp, fp
   409a0:	e8bd8800 	pop	{fp, pc}
   409a4:	10624dd3 	ldrdne	r4, [r2], #-211	; 0xffffff2d	; <UNPREDICTABLE>

000409a8 <usecs>:
   409a8:	e92d4800 	push	{fp, lr}
   409ac:	e1a0b00d 	mov	fp, sp
   409b0:	e24dd008 	sub	sp, sp, #8
   409b4:	e1a0000d 	mov	r0, sp
   409b8:	e3a01000 	mov	r1, #0
   409bc:	ebff3ff9 	bl	109a8 <gettimeofday@plt>
   409c0:	e3a02d09 	mov	r2, #576	; 0x240
   409c4:	e89d0003 	ldm	sp, {r0, r1}
   409c8:	e382293d 	orr	r2, r2, #999424	; 0xf4000
   409cc:	e0201290 	mla	r0, r0, r2, r1
   409d0:	e1a0d00b 	mov	sp, fp
   409d4:	e8bd8800 	pop	{fp, pc}

000409d8 <lcd_begin>:
   409d8:	e92d4c70 	push	{r4, r5, r6, sl, fp, lr}
   409dc:	e28db010 	add	fp, sp, #16
   409e0:	e24dd010 	sub	sp, sp, #16
   409e4:	e59f5038 	ldr	r5, [pc, #56]	; 40a24 <lcd_begin+0x4c>
   409e8:	e58d000c 	str	r0, [sp, #12]
   409ec:	e58d1008 	str	r1, [sp, #8]
   409f0:	e58d2004 	str	r2, [sp, #4]
   409f4:	e5950000 	ldr	r0, [r5]
   409f8:	e59f4028 	ldr	r4, [pc, #40]	; 40a28 <lcd_begin+0x50>
   409fc:	e2806001 	add	r6, r0, #1
   40a00:	e5856000 	str	r6, [r5]
   40a04:	e59d200c 	ldr	r2, [sp, #12]
   40a08:	e99d0009 	ldmib	sp, {r0, r3}
   40a0c:	e59f1018 	ldr	r1, [pc, #24]	; 40a2c <lcd_begin+0x54>
   40a10:	e58d0000 	str	r0, [sp]
   40a14:	e1a00004 	mov	r0, r4
   40a18:	ebff3fca 	bl	10948 <printf@plt>
   40a1c:	e24bd010 	sub	sp, fp, #16
   40a20:	e8bd8c70 	pop	{r4, r5, r6, sl, fp, pc}
   40a24:	00010ab0 			; <UNDEFINED> instruction: 0x00010ab0
   40a28:	000465e3 	andeq	r6, r4, r3, ror #11
   40a2c:	00040aba 			; <UNDEFINED> instruction: 0x00040aba

Disassembly of section .DATA_REGION_2__share:

00040a30 <.DATA_REGION_2__sdata_start>:
   40a30:	00000000 	andeq	r0, r0, r0

Disassembly of section .DATA_REGION_2__data:

00040a34 <adc_key_val>:
   40a34:	0000001e 	andeq	r0, r0, lr, lsl r0
   40a38:	00000096 	muleq	r0, r6, r0
   40a3c:	00000168 	andeq	r0, r0, r8, ror #2
   40a40:	00000217 	andeq	r0, r0, r7, lsl r2
   40a44:	000002f8 	strdeq	r0, [r0], -r8

00040a48 <NUM_KEYS>:
   40a48:	00000005 	andeq	r0, r0, r5

00040a4c <key>:
   40a4c:	00000005 	andeq	r0, r0, r5

00040a50 <mLBolusSteps>:
   40a50:	3a83126f 	bcc	fe105414 <__bss_end__+0xf4816e40>
   40a54:	3ba3d70a 	blcc	fe936684 <__bss_end__+0xf50480b0>
   40a58:	3c23d70a 	stccc	7, cr13, [r3], #-40	; 0xffffffd8
   40a5c:	3d4ccccd 	stclcc	12, cr12, [ip, #-820]	; 0xfffffccc
   40a60:	3dcccccd 	stclcc	12, cr12, [ip, #820]	; 0x334
   40a64:	3f000000 	svccc	0x00000000
   40a68:	3f800000 	svccc	0x00800000
   40a6c:	40a00000 	adcmi	r0, r0, r0
   40a70:	41200000 			; <UNDEFINED> instruction: 0x41200000

00040a74 <mLBigBolus>:
   40a74:	3f800000 	svccc	0x00800000

00040a78 <mLBolusStepIdx>:
   40a78:	00000003 	andeq	r0, r0, r3

00040a7c <keyRepeatDelay>:
   40a7c:	00000190 	muleq	r0, r0, r1

00040a80 <keyDebounce>:
   40a80:	0000007d 	andeq	r0, r0, sp, ror r0

00040a84 <prevKey>:
   40a84:	00000005 	andeq	r0, r0, r5
   40a88:	4d6e6970 			; <UNDEFINED> instruction: 0x4d6e6970
   40a8c:	0065646f 	rsbeq	r6, r5, pc, ror #8
   40a90:	69676964 	stmdbvs	r7!, {r2, r5, r6, r8, fp, sp, lr}^
   40a94:	526c6174 	rsbpl	r6, ip, #116, 2
   40a98:	00646165 	rsbeq	r6, r4, r5, ror #2
   40a9c:	69726553 	ldmdbvs	r2!, {r0, r1, r4, r6, r8, sl, sp, lr}^
   40aa0:	625f6c61 	subsvs	r6, pc, #24832	; 0x6100
   40aa4:	6e696765 	cdpvs	7, 6, cr6, cr9, cr5, {3}
   40aa8:	72655300 	rsbvc	r5, r5, #0, 6
   40aac:	5f6c6169 	svcpl	0x006c6169
   40ab0:	69617661 	stmdbvs	r1!, {r0, r5, r6, r9, sl, ip, sp, lr}^
   40ab4:	6c62616c 	stfvse	f6, [r2], #-432	; 0xfffffe50
   40ab8:	636c0065 	cmnvs	ip, #101	; 0x65
   40abc:	65625f64 	strbvs	r5, [r2, #-3940]!	; 0xfffff09c
   40ac0:	006e6967 	rsbeq	r6, lr, r7, ror #18

Disassembly of section .DATA_REGION_2__bss:

00040ac4 <triggerPin>:
   40ac4:	00000000 	andeq	r0, r0, r0

00040ac8 <bigTriggerPin>:
   40ac8:	00000000 	andeq	r0, r0, r0

00040acc <lastKeyRepeatAt>:
   40acc:	00000000 	andeq	r0, r0, r0

00040ad0 <prevBigTrigger>:
   40ad0:	00000000 	andeq	r0, r0, r0

00040ad4 <prevTrigger>:
   40ad4:	00000000 	andeq	r0, r0, r0

Disassembly of section .text:

00040ad8 <load32>:
   40ad8:	b480      	push	{r7}
   40ada:	b085      	sub	sp, #20
   40adc:	af00      	add	r7, sp, #0
   40ade:	6078      	str	r0, [r7, #4]
   40ae0:	687b      	ldr	r3, [r7, #4]
   40ae2:	60fb      	str	r3, [r7, #12]
   40ae4:	68fb      	ldr	r3, [r7, #12]
   40ae6:	781b      	ldrb	r3, [r3, #0]
   40ae8:	461a      	mov	r2, r3
   40aea:	68fb      	ldr	r3, [r7, #12]
   40aec:	3301      	adds	r3, #1
   40aee:	781b      	ldrb	r3, [r3, #0]
   40af0:	021b      	lsls	r3, r3, #8
   40af2:	431a      	orrs	r2, r3
   40af4:	68fb      	ldr	r3, [r7, #12]
   40af6:	3302      	adds	r3, #2
   40af8:	781b      	ldrb	r3, [r3, #0]
   40afa:	041b      	lsls	r3, r3, #16
   40afc:	431a      	orrs	r2, r3
   40afe:	68fb      	ldr	r3, [r7, #12]
   40b00:	3303      	adds	r3, #3
   40b02:	781b      	ldrb	r3, [r3, #0]
   40b04:	061b      	lsls	r3, r3, #24
   40b06:	4313      	orrs	r3, r2
   40b08:	4618      	mov	r0, r3
   40b0a:	3714      	adds	r7, #20
   40b0c:	46bd      	mov	sp, r7
   40b0e:	f85d 7b04 	ldr.w	r7, [sp], #4
   40b12:	4770      	bx	lr

00040b14 <store16>:
   40b14:	b480      	push	{r7}
   40b16:	b085      	sub	sp, #20
   40b18:	af00      	add	r7, sp, #0
   40b1a:	6078      	str	r0, [r7, #4]
   40b1c:	460b      	mov	r3, r1
   40b1e:	807b      	strh	r3, [r7, #2]
   40b20:	687b      	ldr	r3, [r7, #4]
   40b22:	60fb      	str	r3, [r7, #12]
   40b24:	68fb      	ldr	r3, [r7, #12]
   40b26:	1c5a      	adds	r2, r3, #1
   40b28:	60fa      	str	r2, [r7, #12]
   40b2a:	887a      	ldrh	r2, [r7, #2]
   40b2c:	b2d2      	uxtb	r2, r2
   40b2e:	701a      	strb	r2, [r3, #0]
   40b30:	887b      	ldrh	r3, [r7, #2]
   40b32:	0a1b      	lsrs	r3, r3, #8
   40b34:	807b      	strh	r3, [r7, #2]
   40b36:	68fb      	ldr	r3, [r7, #12]
   40b38:	1c5a      	adds	r2, r3, #1
   40b3a:	60fa      	str	r2, [r7, #12]
   40b3c:	887a      	ldrh	r2, [r7, #2]
   40b3e:	b2d2      	uxtb	r2, r2
   40b40:	701a      	strb	r2, [r3, #0]
   40b42:	bf00      	nop
   40b44:	3714      	adds	r7, #20
   40b46:	46bd      	mov	sp, r7
   40b48:	f85d 7b04 	ldr.w	r7, [sp], #4
   40b4c:	4770      	bx	lr

00040b4e <store32>:
   40b4e:	b480      	push	{r7}
   40b50:	b085      	sub	sp, #20
   40b52:	af00      	add	r7, sp, #0
   40b54:	6078      	str	r0, [r7, #4]
   40b56:	6039      	str	r1, [r7, #0]
   40b58:	687b      	ldr	r3, [r7, #4]
   40b5a:	60fb      	str	r3, [r7, #12]
   40b5c:	683b      	ldr	r3, [r7, #0]
   40b5e:	b2da      	uxtb	r2, r3
   40b60:	68fb      	ldr	r3, [r7, #12]
   40b62:	701a      	strb	r2, [r3, #0]
   40b64:	68fb      	ldr	r3, [r7, #12]
   40b66:	3301      	adds	r3, #1
   40b68:	683a      	ldr	r2, [r7, #0]
   40b6a:	0a12      	lsrs	r2, r2, #8
   40b6c:	b2d2      	uxtb	r2, r2
   40b6e:	701a      	strb	r2, [r3, #0]
   40b70:	68fb      	ldr	r3, [r7, #12]
   40b72:	3302      	adds	r3, #2
   40b74:	683a      	ldr	r2, [r7, #0]
   40b76:	0c12      	lsrs	r2, r2, #16
   40b78:	b2d2      	uxtb	r2, r2
   40b7a:	701a      	strb	r2, [r3, #0]
   40b7c:	68fb      	ldr	r3, [r7, #12]
   40b7e:	3303      	adds	r3, #3
   40b80:	683a      	ldr	r2, [r7, #0]
   40b82:	0e12      	lsrs	r2, r2, #24
   40b84:	b2d2      	uxtb	r2, r2
   40b86:	701a      	strb	r2, [r3, #0]
   40b88:	bf00      	nop
   40b8a:	3714      	adds	r7, #20
   40b8c:	46bd      	mov	sp, r7
   40b8e:	f85d 7b04 	ldr.w	r7, [sp], #4
   40b92:	4770      	bx	lr

00040b94 <rotr32>:
   40b94:	b480      	push	{r7}
   40b96:	b083      	sub	sp, #12
   40b98:	af00      	add	r7, sp, #0
   40b9a:	6078      	str	r0, [r7, #4]
   40b9c:	6039      	str	r1, [r7, #0]
   40b9e:	687a      	ldr	r2, [r7, #4]
   40ba0:	683b      	ldr	r3, [r7, #0]
   40ba2:	fa62 f303 	ror.w	r3, r2, r3
   40ba6:	4618      	mov	r0, r3
   40ba8:	370c      	adds	r7, #12
   40baa:	46bd      	mov	sp, r7
   40bac:	f85d 7b04 	ldr.w	r7, [sp], #4
   40bb0:	4770      	bx	lr

00040bb2 <secure_zero_memory>:
   40bb2:	b580      	push	{r7, lr}
   40bb4:	b082      	sub	sp, #8
   40bb6:	af00      	add	r7, sp, #0
   40bb8:	6078      	str	r0, [r7, #4]
   40bba:	6039      	str	r1, [r7, #0]
   40bbc:	4b05      	ldr	r3, [pc, #20]	; (40bd4 <secure_zero_memory+0x22>)
   40bbe:	447b      	add	r3, pc
   40bc0:	681b      	ldr	r3, [r3, #0]
   40bc2:	683a      	ldr	r2, [r7, #0]
   40bc4:	2100      	movs	r1, #0
   40bc6:	6878      	ldr	r0, [r7, #4]
   40bc8:	4798      	blx	r3
   40bca:	bf00      	nop
   40bcc:	3708      	adds	r7, #8
   40bce:	46bd      	mov	sp, r7
   40bd0:	bd80      	pop	{r7, pc}
   40bd2:	bf00      	nop
   40bd4:	0001650e 	andeq	r6, r1, lr, lsl #10

00040bd8 <blake2s_set_lastnode>:
   40bd8:	b480      	push	{r7}
   40bda:	b083      	sub	sp, #12
   40bdc:	af00      	add	r7, sp, #0
   40bde:	6078      	str	r0, [r7, #4]
   40be0:	687b      	ldr	r3, [r7, #4]
   40be2:	f04f 32ff 	mov.w	r2, #4294967295	; 0xffffffff
   40be6:	62da      	str	r2, [r3, #44]	; 0x2c
   40be8:	bf00      	nop
   40bea:	370c      	adds	r7, #12
   40bec:	46bd      	mov	sp, r7
   40bee:	f85d 7b04 	ldr.w	r7, [sp], #4
   40bf2:	4770      	bx	lr

00040bf4 <blake2s_is_lastblock>:
   40bf4:	b480      	push	{r7}
   40bf6:	b083      	sub	sp, #12
   40bf8:	af00      	add	r7, sp, #0
   40bfa:	6078      	str	r0, [r7, #4]
   40bfc:	687b      	ldr	r3, [r7, #4]
   40bfe:	6a9b      	ldr	r3, [r3, #40]	; 0x28
   40c00:	2b00      	cmp	r3, #0
   40c02:	bf14      	ite	ne
   40c04:	2301      	movne	r3, #1
   40c06:	2300      	moveq	r3, #0
   40c08:	b2db      	uxtb	r3, r3
   40c0a:	4618      	mov	r0, r3
   40c0c:	370c      	adds	r7, #12
   40c0e:	46bd      	mov	sp, r7
   40c10:	f85d 7b04 	ldr.w	r7, [sp], #4
   40c14:	4770      	bx	lr

00040c16 <blake2s_set_lastblock>:
   40c16:	b580      	push	{r7, lr}
   40c18:	b082      	sub	sp, #8
   40c1a:	af00      	add	r7, sp, #0
   40c1c:	6078      	str	r0, [r7, #4]
   40c1e:	687b      	ldr	r3, [r7, #4]
   40c20:	f893 3078 	ldrb.w	r3, [r3, #120]	; 0x78
   40c24:	2b00      	cmp	r3, #0
   40c26:	d002      	beq.n	40c2e <blake2s_set_lastblock+0x18>
   40c28:	6878      	ldr	r0, [r7, #4]
   40c2a:	f7ff ffd5 	bl	40bd8 <blake2s_set_lastnode>
   40c2e:	687b      	ldr	r3, [r7, #4]
   40c30:	f04f 32ff 	mov.w	r2, #4294967295	; 0xffffffff
   40c34:	629a      	str	r2, [r3, #40]	; 0x28
   40c36:	bf00      	nop
   40c38:	3708      	adds	r7, #8
   40c3a:	46bd      	mov	sp, r7
   40c3c:	bd80      	pop	{r7, pc}

00040c3e <blake2s_increment_counter>:
   40c3e:	b480      	push	{r7}
   40c40:	b083      	sub	sp, #12
   40c42:	af00      	add	r7, sp, #0
   40c44:	6078      	str	r0, [r7, #4]
   40c46:	6039      	str	r1, [r7, #0]
   40c48:	687b      	ldr	r3, [r7, #4]
   40c4a:	6a1a      	ldr	r2, [r3, #32]
   40c4c:	683b      	ldr	r3, [r7, #0]
   40c4e:	441a      	add	r2, r3
   40c50:	687b      	ldr	r3, [r7, #4]
   40c52:	621a      	str	r2, [r3, #32]
   40c54:	687b      	ldr	r3, [r7, #4]
   40c56:	6a5b      	ldr	r3, [r3, #36]	; 0x24
   40c58:	687a      	ldr	r2, [r7, #4]
   40c5a:	6a11      	ldr	r1, [r2, #32]
   40c5c:	683a      	ldr	r2, [r7, #0]
   40c5e:	4291      	cmp	r1, r2
   40c60:	bf34      	ite	cc
   40c62:	2201      	movcc	r2, #1
   40c64:	2200      	movcs	r2, #0
   40c66:	b2d2      	uxtb	r2, r2
   40c68:	441a      	add	r2, r3
   40c6a:	687b      	ldr	r3, [r7, #4]
   40c6c:	625a      	str	r2, [r3, #36]	; 0x24
   40c6e:	bf00      	nop
   40c70:	370c      	adds	r7, #12
   40c72:	46bd      	mov	sp, r7
   40c74:	f85d 7b04 	ldr.w	r7, [sp], #4
   40c78:	4770      	bx	lr

00040c7a <blake2s_init0>:
   40c7a:	b580      	push	{r7, lr}
   40c7c:	b084      	sub	sp, #16
   40c7e:	af00      	add	r7, sp, #0
   40c80:	6078      	str	r0, [r7, #4]
   40c82:	227c      	movs	r2, #124	; 0x7c
   40c84:	2100      	movs	r1, #0
   40c86:	6878      	ldr	r0, [r7, #4]
   40c88:	f7cf eeca 	blx	10a20 <memset@plt>
   40c8c:	2300      	movs	r3, #0
   40c8e:	60fb      	str	r3, [r7, #12]
   40c90:	e00c      	b.n	40cac <blake2s_init0+0x32>
   40c92:	4b0a      	ldr	r3, [pc, #40]	; (40cbc <blake2s_init0+0x42>)
   40c94:	447b      	add	r3, pc
   40c96:	461a      	mov	r2, r3
   40c98:	68fb      	ldr	r3, [r7, #12]
   40c9a:	f852 1023 	ldr.w	r1, [r2, r3, lsl #2]
   40c9e:	687b      	ldr	r3, [r7, #4]
   40ca0:	68fa      	ldr	r2, [r7, #12]
   40ca2:	f843 1022 	str.w	r1, [r3, r2, lsl #2]
   40ca6:	68fb      	ldr	r3, [r7, #12]
   40ca8:	3301      	adds	r3, #1
   40caa:	60fb      	str	r3, [r7, #12]
   40cac:	68fb      	ldr	r3, [r7, #12]
   40cae:	2b07      	cmp	r3, #7
   40cb0:	d9ef      	bls.n	40c92 <blake2s_init0+0x18>
   40cb2:	bf00      	nop
   40cb4:	3710      	adds	r7, #16
   40cb6:	46bd      	mov	sp, r7
   40cb8:	bd80      	pop	{r7, pc}
   40cba:	bf00      	nop
   40cbc:	00005a38 	andeq	r5, r0, r8, lsr sl

00040cc0 <blake2s_init_param>:
   40cc0:	b580      	push	{r7, lr}
   40cc2:	b084      	sub	sp, #16
   40cc4:	af00      	add	r7, sp, #0
   40cc6:	6078      	str	r0, [r7, #4]
   40cc8:	6039      	str	r1, [r7, #0]
   40cca:	683b      	ldr	r3, [r7, #0]
   40ccc:	60bb      	str	r3, [r7, #8]
   40cce:	6878      	ldr	r0, [r7, #4]
   40cd0:	f7ff ffd3 	bl	40c7a <blake2s_init0>
   40cd4:	2300      	movs	r3, #0
   40cd6:	60fb      	str	r3, [r7, #12]
   40cd8:	e013      	b.n	40d02 <blake2s_init_param+0x42>
   40cda:	68fb      	ldr	r3, [r7, #12]
   40cdc:	009b      	lsls	r3, r3, #2
   40cde:	68ba      	ldr	r2, [r7, #8]
   40ce0:	4413      	add	r3, r2
   40ce2:	4618      	mov	r0, r3
   40ce4:	f7ff fef8 	bl	40ad8 <load32>
   40ce8:	4601      	mov	r1, r0
   40cea:	687b      	ldr	r3, [r7, #4]
   40cec:	68fa      	ldr	r2, [r7, #12]
   40cee:	f853 3022 	ldr.w	r3, [r3, r2, lsl #2]
   40cf2:	4059      	eors	r1, r3
   40cf4:	687b      	ldr	r3, [r7, #4]
   40cf6:	68fa      	ldr	r2, [r7, #12]
   40cf8:	f843 1022 	str.w	r1, [r3, r2, lsl #2]
   40cfc:	68fb      	ldr	r3, [r7, #12]
   40cfe:	3301      	adds	r3, #1
   40d00:	60fb      	str	r3, [r7, #12]
   40d02:	68fb      	ldr	r3, [r7, #12]
   40d04:	2b07      	cmp	r3, #7
   40d06:	d9e8      	bls.n	40cda <blake2s_init_param+0x1a>
   40d08:	683b      	ldr	r3, [r7, #0]
   40d0a:	781b      	ldrb	r3, [r3, #0]
   40d0c:	461a      	mov	r2, r3
   40d0e:	687b      	ldr	r3, [r7, #4]
   40d10:	675a      	str	r2, [r3, #116]	; 0x74
   40d12:	2300      	movs	r3, #0
   40d14:	4618      	mov	r0, r3
   40d16:	3710      	adds	r7, #16
   40d18:	46bd      	mov	sp, r7
   40d1a:	bd80      	pop	{r7, pc}

00040d1c <blake2s_init>:
   40d1c:	b580      	push	{r7, lr}
   40d1e:	b08a      	sub	sp, #40	; 0x28
   40d20:	af00      	add	r7, sp, #0
   40d22:	6078      	str	r0, [r7, #4]
   40d24:	6039      	str	r1, [r7, #0]
   40d26:	683b      	ldr	r3, [r7, #0]
   40d28:	2b00      	cmp	r3, #0
   40d2a:	d002      	beq.n	40d32 <blake2s_init+0x16>
   40d2c:	683b      	ldr	r3, [r7, #0]
   40d2e:	2b20      	cmp	r3, #32
   40d30:	d902      	bls.n	40d38 <blake2s_init+0x1c>
   40d32:	f04f 33ff 	mov.w	r3, #4294967295	; 0xffffffff
   40d36:	e038      	b.n	40daa <blake2s_init+0x8e>
   40d38:	683b      	ldr	r3, [r7, #0]
   40d3a:	b2db      	uxtb	r3, r3
   40d3c:	723b      	strb	r3, [r7, #8]
   40d3e:	2300      	movs	r3, #0
   40d40:	727b      	strb	r3, [r7, #9]
   40d42:	2301      	movs	r3, #1
   40d44:	72bb      	strb	r3, [r7, #10]
   40d46:	2301      	movs	r3, #1
   40d48:	72fb      	strb	r3, [r7, #11]
   40d4a:	f107 0308 	add.w	r3, r7, #8
   40d4e:	3304      	adds	r3, #4
   40d50:	2100      	movs	r1, #0
   40d52:	4618      	mov	r0, r3
   40d54:	f7ff fefb 	bl	40b4e <store32>
   40d58:	f107 0308 	add.w	r3, r7, #8
   40d5c:	3308      	adds	r3, #8
   40d5e:	2100      	movs	r1, #0
   40d60:	4618      	mov	r0, r3
   40d62:	f7ff fef4 	bl	40b4e <store32>
   40d66:	f107 0308 	add.w	r3, r7, #8
   40d6a:	330c      	adds	r3, #12
   40d6c:	2100      	movs	r1, #0
   40d6e:	4618      	mov	r0, r3
   40d70:	f7ff fed0 	bl	40b14 <store16>
   40d74:	2300      	movs	r3, #0
   40d76:	75bb      	strb	r3, [r7, #22]
   40d78:	2300      	movs	r3, #0
   40d7a:	75fb      	strb	r3, [r7, #23]
   40d7c:	f107 0308 	add.w	r3, r7, #8
   40d80:	3310      	adds	r3, #16
   40d82:	2208      	movs	r2, #8
   40d84:	2100      	movs	r1, #0
   40d86:	4618      	mov	r0, r3
   40d88:	f7cf ee4a 	blx	10a20 <memset@plt>
   40d8c:	f107 0308 	add.w	r3, r7, #8
   40d90:	3318      	adds	r3, #24
   40d92:	2208      	movs	r2, #8
   40d94:	2100      	movs	r1, #0
   40d96:	4618      	mov	r0, r3
   40d98:	f7cf ee42 	blx	10a20 <memset@plt>
   40d9c:	f107 0308 	add.w	r3, r7, #8
   40da0:	4619      	mov	r1, r3
   40da2:	6878      	ldr	r0, [r7, #4]
   40da4:	f7ff ff8c 	bl	40cc0 <blake2s_init_param>
   40da8:	4603      	mov	r3, r0
   40daa:	4618      	mov	r0, r3
   40dac:	3728      	adds	r7, #40	; 0x28
   40dae:	46bd      	mov	sp, r7
   40db0:	bd80      	pop	{r7, pc}

00040db2 <blake2s_init_key>:
   40db2:	b580      	push	{r7, lr}
   40db4:	b09c      	sub	sp, #112	; 0x70
   40db6:	af00      	add	r7, sp, #0
   40db8:	60f8      	str	r0, [r7, #12]
   40dba:	60b9      	str	r1, [r7, #8]
   40dbc:	607a      	str	r2, [r7, #4]
   40dbe:	603b      	str	r3, [r7, #0]
   40dc0:	68bb      	ldr	r3, [r7, #8]
   40dc2:	2b00      	cmp	r3, #0
   40dc4:	d002      	beq.n	40dcc <blake2s_init_key+0x1a>
   40dc6:	68bb      	ldr	r3, [r7, #8]
   40dc8:	2b20      	cmp	r3, #32
   40dca:	d902      	bls.n	40dd2 <blake2s_init_key+0x20>
   40dcc:	f04f 33ff 	mov.w	r3, #4294967295	; 0xffffffff
   40dd0:	e06c      	b.n	40eac <blake2s_init_key+0xfa>
   40dd2:	687b      	ldr	r3, [r7, #4]
   40dd4:	2b00      	cmp	r3, #0
   40dd6:	d005      	beq.n	40de4 <blake2s_init_key+0x32>
   40dd8:	683b      	ldr	r3, [r7, #0]
   40dda:	2b00      	cmp	r3, #0
   40ddc:	d002      	beq.n	40de4 <blake2s_init_key+0x32>
   40dde:	683b      	ldr	r3, [r7, #0]
   40de0:	2b20      	cmp	r3, #32
   40de2:	d902      	bls.n	40dea <blake2s_init_key+0x38>
   40de4:	f04f 33ff 	mov.w	r3, #4294967295	; 0xffffffff
   40de8:	e060      	b.n	40eac <blake2s_init_key+0xfa>
   40dea:	68bb      	ldr	r3, [r7, #8]
   40dec:	b2db      	uxtb	r3, r3
   40dee:	f887 3050 	strb.w	r3, [r7, #80]	; 0x50
   40df2:	683b      	ldr	r3, [r7, #0]
   40df4:	b2db      	uxtb	r3, r3
   40df6:	f887 3051 	strb.w	r3, [r7, #81]	; 0x51
   40dfa:	2301      	movs	r3, #1
   40dfc:	f887 3052 	strb.w	r3, [r7, #82]	; 0x52
   40e00:	2301      	movs	r3, #1
   40e02:	f887 3053 	strb.w	r3, [r7, #83]	; 0x53
   40e06:	f107 0350 	add.w	r3, r7, #80	; 0x50
   40e0a:	3304      	adds	r3, #4
   40e0c:	2100      	movs	r1, #0
   40e0e:	4618      	mov	r0, r3
   40e10:	f7ff fe9d 	bl	40b4e <store32>
   40e14:	f107 0350 	add.w	r3, r7, #80	; 0x50
   40e18:	3308      	adds	r3, #8
   40e1a:	2100      	movs	r1, #0
   40e1c:	4618      	mov	r0, r3
   40e1e:	f7ff fe96 	bl	40b4e <store32>
   40e22:	f107 0350 	add.w	r3, r7, #80	; 0x50
   40e26:	330c      	adds	r3, #12
   40e28:	2100      	movs	r1, #0
   40e2a:	4618      	mov	r0, r3
   40e2c:	f7ff fe72 	bl	40b14 <store16>
   40e30:	2300      	movs	r3, #0
   40e32:	f887 305e 	strb.w	r3, [r7, #94]	; 0x5e
   40e36:	2300      	movs	r3, #0
   40e38:	f887 305f 	strb.w	r3, [r7, #95]	; 0x5f
   40e3c:	f107 0350 	add.w	r3, r7, #80	; 0x50
   40e40:	3310      	adds	r3, #16
   40e42:	2208      	movs	r2, #8
   40e44:	2100      	movs	r1, #0
   40e46:	4618      	mov	r0, r3
   40e48:	f7cf edea 	blx	10a20 <memset@plt>
   40e4c:	f107 0350 	add.w	r3, r7, #80	; 0x50
   40e50:	3318      	adds	r3, #24
   40e52:	2208      	movs	r2, #8
   40e54:	2100      	movs	r1, #0
   40e56:	4618      	mov	r0, r3
   40e58:	f7cf ede2 	blx	10a20 <memset@plt>
   40e5c:	f107 0350 	add.w	r3, r7, #80	; 0x50
   40e60:	4619      	mov	r1, r3
   40e62:	68f8      	ldr	r0, [r7, #12]
   40e64:	f7ff ff2c 	bl	40cc0 <blake2s_init_param>
   40e68:	4603      	mov	r3, r0
   40e6a:	2b00      	cmp	r3, #0
   40e6c:	da02      	bge.n	40e74 <blake2s_init_key+0xc2>
   40e6e:	f04f 33ff 	mov.w	r3, #4294967295	; 0xffffffff
   40e72:	e01b      	b.n	40eac <blake2s_init_key+0xfa>
   40e74:	f107 0310 	add.w	r3, r7, #16
   40e78:	2240      	movs	r2, #64	; 0x40
   40e7a:	2100      	movs	r1, #0
   40e7c:	4618      	mov	r0, r3
   40e7e:	f7cf edd0 	blx	10a20 <memset@plt>
   40e82:	f107 0310 	add.w	r3, r7, #16
   40e86:	683a      	ldr	r2, [r7, #0]
   40e88:	6879      	ldr	r1, [r7, #4]
   40e8a:	4618      	mov	r0, r3
   40e8c:	f7cf ed74 	blx	10978 <memcpy@plt>
   40e90:	f107 0310 	add.w	r3, r7, #16
   40e94:	2240      	movs	r2, #64	; 0x40
   40e96:	4619      	mov	r1, r3
   40e98:	68f8      	ldr	r0, [r7, #12]
   40e9a:	f002 fdeb 	bl	43a74 <blake2s_update>
   40e9e:	f107 0310 	add.w	r3, r7, #16
   40ea2:	2140      	movs	r1, #64	; 0x40
   40ea4:	4618      	mov	r0, r3
   40ea6:	f7ff fe84 	bl	40bb2 <secure_zero_memory>
   40eaa:	2300      	movs	r3, #0
   40eac:	4618      	mov	r0, r3
   40eae:	3770      	adds	r7, #112	; 0x70
   40eb0:	46bd      	mov	sp, r7
   40eb2:	bd80      	pop	{r7, pc}

00040eb4 <blake2s_compress>:
   40eb4:	b580      	push	{r7, lr}
   40eb6:	b0a4      	sub	sp, #144	; 0x90
   40eb8:	af00      	add	r7, sp, #0
   40eba:	6078      	str	r0, [r7, #4]
   40ebc:	6039      	str	r1, [r7, #0]
   40ebe:	2300      	movs	r3, #0
   40ec0:	f8c7 308c 	str.w	r3, [r7, #140]	; 0x8c
   40ec4:	e015      	b.n	40ef2 <blake2s_compress+0x3e>
   40ec6:	f8d7 308c 	ldr.w	r3, [r7, #140]	; 0x8c
   40eca:	009b      	lsls	r3, r3, #2
   40ecc:	683a      	ldr	r2, [r7, #0]
   40ece:	4413      	add	r3, r2
   40ed0:	4618      	mov	r0, r3
   40ed2:	f7ff fe01 	bl	40ad8 <load32>
   40ed6:	4602      	mov	r2, r0
   40ed8:	f8d7 308c 	ldr.w	r3, [r7, #140]	; 0x8c
   40edc:	009b      	lsls	r3, r3, #2
   40ede:	f107 0190 	add.w	r1, r7, #144	; 0x90
   40ee2:	440b      	add	r3, r1
   40ee4:	f843 2c44 	str.w	r2, [r3, #-68]
   40ee8:	f8d7 308c 	ldr.w	r3, [r7, #140]	; 0x8c
   40eec:	3301      	adds	r3, #1
   40eee:	f8c7 308c 	str.w	r3, [r7, #140]	; 0x8c
   40ef2:	f8d7 308c 	ldr.w	r3, [r7, #140]	; 0x8c
   40ef6:	2b0f      	cmp	r3, #15
   40ef8:	d9e5      	bls.n	40ec6 <blake2s_compress+0x12>
   40efa:	2300      	movs	r3, #0
   40efc:	f8c7 308c 	str.w	r3, [r7, #140]	; 0x8c
   40f00:	e011      	b.n	40f26 <blake2s_compress+0x72>
   40f02:	687b      	ldr	r3, [r7, #4]
   40f04:	f8d7 208c 	ldr.w	r2, [r7, #140]	; 0x8c
   40f08:	f853 2022 	ldr.w	r2, [r3, r2, lsl #2]
   40f0c:	f8d7 308c 	ldr.w	r3, [r7, #140]	; 0x8c
   40f10:	009b      	lsls	r3, r3, #2
   40f12:	f107 0190 	add.w	r1, r7, #144	; 0x90
   40f16:	440b      	add	r3, r1
   40f18:	f843 2c84 	str.w	r2, [r3, #-132]
   40f1c:	f8d7 308c 	ldr.w	r3, [r7, #140]	; 0x8c
   40f20:	3301      	adds	r3, #1
   40f22:	f8c7 308c 	str.w	r3, [r7, #140]	; 0x8c
   40f26:	f8d7 308c 	ldr.w	r3, [r7, #140]	; 0x8c
   40f2a:	2b07      	cmp	r3, #7
   40f2c:	d9e9      	bls.n	40f02 <blake2s_compress+0x4e>
   40f2e:	f24e 6367 	movw	r3, #58983	; 0xe667
   40f32:	f6c6 2309 	movt	r3, #27145	; 0x6a09
   40f36:	62fb      	str	r3, [r7, #44]	; 0x2c
   40f38:	f64a 6385 	movw	r3, #44677	; 0xae85
   40f3c:	f6cb 3367 	movt	r3, #47975	; 0xbb67
   40f40:	633b      	str	r3, [r7, #48]	; 0x30
   40f42:	f24f 3372 	movw	r3, #62322	; 0xf372
   40f46:	f6c3 436e 	movt	r3, #15470	; 0x3c6e
   40f4a:	637b      	str	r3, [r7, #52]	; 0x34
   40f4c:	f24f 533a 	movw	r3, #62778	; 0xf53a
   40f50:	f2ca 534f 	movt	r3, #42319	; 0xa54f
   40f54:	63bb      	str	r3, [r7, #56]	; 0x38
   40f56:	687b      	ldr	r3, [r7, #4]
   40f58:	6a1a      	ldr	r2, [r3, #32]
   40f5a:	f245 237f 	movw	r3, #21119	; 0x527f
   40f5e:	f2c5 130e 	movt	r3, #20750	; 0x510e
   40f62:	4053      	eors	r3, r2
   40f64:	63fb      	str	r3, [r7, #60]	; 0x3c
   40f66:	687b      	ldr	r3, [r7, #4]
   40f68:	6a5a      	ldr	r2, [r3, #36]	; 0x24
   40f6a:	f646 038c 	movw	r3, #26764	; 0x688c
   40f6e:	f6c9 3305 	movt	r3, #39685	; 0x9b05
   40f72:	4053      	eors	r3, r2
   40f74:	643b      	str	r3, [r7, #64]	; 0x40
   40f76:	687b      	ldr	r3, [r7, #4]
   40f78:	6a9a      	ldr	r2, [r3, #40]	; 0x28
   40f7a:	f64d 13ab 	movw	r3, #55723	; 0xd9ab
   40f7e:	f6c1 7383 	movt	r3, #8067	; 0x1f83
   40f82:	4053      	eors	r3, r2
   40f84:	647b      	str	r3, [r7, #68]	; 0x44
   40f86:	687b      	ldr	r3, [r7, #4]
   40f88:	6ada      	ldr	r2, [r3, #44]	; 0x2c
   40f8a:	f64c 5319 	movw	r3, #52505	; 0xcd19
   40f8e:	f6c5 33e0 	movt	r3, #23520	; 0x5be0
   40f92:	4053      	eors	r3, r2
   40f94:	64bb      	str	r3, [r7, #72]	; 0x48
   40f96:	68fa      	ldr	r2, [r7, #12]
   40f98:	69fb      	ldr	r3, [r7, #28]
   40f9a:	441a      	add	r2, r3
   40f9c:	2300      	movs	r3, #0
   40f9e:	009b      	lsls	r3, r3, #2
   40fa0:	f107 0190 	add.w	r1, r7, #144	; 0x90
   40fa4:	440b      	add	r3, r1
   40fa6:	f853 3c44 	ldr.w	r3, [r3, #-68]
   40faa:	4413      	add	r3, r2
   40fac:	60fb      	str	r3, [r7, #12]
   40fae:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   40fb0:	68fb      	ldr	r3, [r7, #12]
   40fb2:	4053      	eors	r3, r2
   40fb4:	2110      	movs	r1, #16
   40fb6:	4618      	mov	r0, r3
   40fb8:	f7ff fdec 	bl	40b94 <rotr32>
   40fbc:	4603      	mov	r3, r0
   40fbe:	63fb      	str	r3, [r7, #60]	; 0x3c
   40fc0:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   40fc2:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   40fc4:	4413      	add	r3, r2
   40fc6:	62fb      	str	r3, [r7, #44]	; 0x2c
   40fc8:	69fa      	ldr	r2, [r7, #28]
   40fca:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   40fcc:	4053      	eors	r3, r2
   40fce:	210c      	movs	r1, #12
   40fd0:	4618      	mov	r0, r3
   40fd2:	f7ff fddf 	bl	40b94 <rotr32>
   40fd6:	4603      	mov	r3, r0
   40fd8:	61fb      	str	r3, [r7, #28]
   40fda:	68fa      	ldr	r2, [r7, #12]
   40fdc:	69fb      	ldr	r3, [r7, #28]
   40fde:	441a      	add	r2, r3
   40fe0:	2301      	movs	r3, #1
   40fe2:	009b      	lsls	r3, r3, #2
   40fe4:	f107 0190 	add.w	r1, r7, #144	; 0x90
   40fe8:	440b      	add	r3, r1
   40fea:	f853 3c44 	ldr.w	r3, [r3, #-68]
   40fee:	4413      	add	r3, r2
   40ff0:	60fb      	str	r3, [r7, #12]
   40ff2:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   40ff4:	68fb      	ldr	r3, [r7, #12]
   40ff6:	4053      	eors	r3, r2
   40ff8:	2108      	movs	r1, #8
   40ffa:	4618      	mov	r0, r3
   40ffc:	f7ff fdca 	bl	40b94 <rotr32>
   41000:	4603      	mov	r3, r0
   41002:	63fb      	str	r3, [r7, #60]	; 0x3c
   41004:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   41006:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   41008:	4413      	add	r3, r2
   4100a:	62fb      	str	r3, [r7, #44]	; 0x2c
   4100c:	69fa      	ldr	r2, [r7, #28]
   4100e:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   41010:	4053      	eors	r3, r2
   41012:	2107      	movs	r1, #7
   41014:	4618      	mov	r0, r3
   41016:	f7ff fdbd 	bl	40b94 <rotr32>
   4101a:	4603      	mov	r3, r0
   4101c:	61fb      	str	r3, [r7, #28]
   4101e:	693a      	ldr	r2, [r7, #16]
   41020:	6a3b      	ldr	r3, [r7, #32]
   41022:	441a      	add	r2, r3
   41024:	2302      	movs	r3, #2
   41026:	009b      	lsls	r3, r3, #2
   41028:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4102c:	440b      	add	r3, r1
   4102e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41032:	4413      	add	r3, r2
   41034:	613b      	str	r3, [r7, #16]
   41036:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   41038:	693b      	ldr	r3, [r7, #16]
   4103a:	4053      	eors	r3, r2
   4103c:	2110      	movs	r1, #16
   4103e:	4618      	mov	r0, r3
   41040:	f7ff fda8 	bl	40b94 <rotr32>
   41044:	4603      	mov	r3, r0
   41046:	643b      	str	r3, [r7, #64]	; 0x40
   41048:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   4104a:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   4104c:	4413      	add	r3, r2
   4104e:	633b      	str	r3, [r7, #48]	; 0x30
   41050:	6a3a      	ldr	r2, [r7, #32]
   41052:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   41054:	4053      	eors	r3, r2
   41056:	210c      	movs	r1, #12
   41058:	4618      	mov	r0, r3
   4105a:	f7ff fd9b 	bl	40b94 <rotr32>
   4105e:	4603      	mov	r3, r0
   41060:	623b      	str	r3, [r7, #32]
   41062:	693a      	ldr	r2, [r7, #16]
   41064:	6a3b      	ldr	r3, [r7, #32]
   41066:	441a      	add	r2, r3
   41068:	2303      	movs	r3, #3
   4106a:	009b      	lsls	r3, r3, #2
   4106c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41070:	440b      	add	r3, r1
   41072:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41076:	4413      	add	r3, r2
   41078:	613b      	str	r3, [r7, #16]
   4107a:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   4107c:	693b      	ldr	r3, [r7, #16]
   4107e:	4053      	eors	r3, r2
   41080:	2108      	movs	r1, #8
   41082:	4618      	mov	r0, r3
   41084:	f7ff fd86 	bl	40b94 <rotr32>
   41088:	4603      	mov	r3, r0
   4108a:	643b      	str	r3, [r7, #64]	; 0x40
   4108c:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   4108e:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   41090:	4413      	add	r3, r2
   41092:	633b      	str	r3, [r7, #48]	; 0x30
   41094:	6a3a      	ldr	r2, [r7, #32]
   41096:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   41098:	4053      	eors	r3, r2
   4109a:	2107      	movs	r1, #7
   4109c:	4618      	mov	r0, r3
   4109e:	f7ff fd79 	bl	40b94 <rotr32>
   410a2:	4603      	mov	r3, r0
   410a4:	623b      	str	r3, [r7, #32]
   410a6:	697a      	ldr	r2, [r7, #20]
   410a8:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   410aa:	441a      	add	r2, r3
   410ac:	2304      	movs	r3, #4
   410ae:	009b      	lsls	r3, r3, #2
   410b0:	f107 0190 	add.w	r1, r7, #144	; 0x90
   410b4:	440b      	add	r3, r1
   410b6:	f853 3c44 	ldr.w	r3, [r3, #-68]
   410ba:	4413      	add	r3, r2
   410bc:	617b      	str	r3, [r7, #20]
   410be:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   410c0:	697b      	ldr	r3, [r7, #20]
   410c2:	4053      	eors	r3, r2
   410c4:	2110      	movs	r1, #16
   410c6:	4618      	mov	r0, r3
   410c8:	f7ff fd64 	bl	40b94 <rotr32>
   410cc:	4603      	mov	r3, r0
   410ce:	647b      	str	r3, [r7, #68]	; 0x44
   410d0:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   410d2:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   410d4:	4413      	add	r3, r2
   410d6:	637b      	str	r3, [r7, #52]	; 0x34
   410d8:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   410da:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   410dc:	4053      	eors	r3, r2
   410de:	210c      	movs	r1, #12
   410e0:	4618      	mov	r0, r3
   410e2:	f7ff fd57 	bl	40b94 <rotr32>
   410e6:	4603      	mov	r3, r0
   410e8:	627b      	str	r3, [r7, #36]	; 0x24
   410ea:	697a      	ldr	r2, [r7, #20]
   410ec:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   410ee:	441a      	add	r2, r3
   410f0:	2305      	movs	r3, #5
   410f2:	009b      	lsls	r3, r3, #2
   410f4:	f107 0190 	add.w	r1, r7, #144	; 0x90
   410f8:	440b      	add	r3, r1
   410fa:	f853 3c44 	ldr.w	r3, [r3, #-68]
   410fe:	4413      	add	r3, r2
   41100:	617b      	str	r3, [r7, #20]
   41102:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   41104:	697b      	ldr	r3, [r7, #20]
   41106:	4053      	eors	r3, r2
   41108:	2108      	movs	r1, #8
   4110a:	4618      	mov	r0, r3
   4110c:	f7ff fd42 	bl	40b94 <rotr32>
   41110:	4603      	mov	r3, r0
   41112:	647b      	str	r3, [r7, #68]	; 0x44
   41114:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   41116:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   41118:	4413      	add	r3, r2
   4111a:	637b      	str	r3, [r7, #52]	; 0x34
   4111c:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   4111e:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   41120:	4053      	eors	r3, r2
   41122:	2107      	movs	r1, #7
   41124:	4618      	mov	r0, r3
   41126:	f7ff fd35 	bl	40b94 <rotr32>
   4112a:	4603      	mov	r3, r0
   4112c:	627b      	str	r3, [r7, #36]	; 0x24
   4112e:	69ba      	ldr	r2, [r7, #24]
   41130:	6abb      	ldr	r3, [r7, #40]	; 0x28
   41132:	441a      	add	r2, r3
   41134:	2306      	movs	r3, #6
   41136:	009b      	lsls	r3, r3, #2
   41138:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4113c:	440b      	add	r3, r1
   4113e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41142:	4413      	add	r3, r2
   41144:	61bb      	str	r3, [r7, #24]
   41146:	6cba      	ldr	r2, [r7, #72]	; 0x48
   41148:	69bb      	ldr	r3, [r7, #24]
   4114a:	4053      	eors	r3, r2
   4114c:	2110      	movs	r1, #16
   4114e:	4618      	mov	r0, r3
   41150:	f7ff fd20 	bl	40b94 <rotr32>
   41154:	4603      	mov	r3, r0
   41156:	64bb      	str	r3, [r7, #72]	; 0x48
   41158:	6bba      	ldr	r2, [r7, #56]	; 0x38
   4115a:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   4115c:	4413      	add	r3, r2
   4115e:	63bb      	str	r3, [r7, #56]	; 0x38
   41160:	6aba      	ldr	r2, [r7, #40]	; 0x28
   41162:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   41164:	4053      	eors	r3, r2
   41166:	210c      	movs	r1, #12
   41168:	4618      	mov	r0, r3
   4116a:	f7ff fd13 	bl	40b94 <rotr32>
   4116e:	4603      	mov	r3, r0
   41170:	62bb      	str	r3, [r7, #40]	; 0x28
   41172:	69ba      	ldr	r2, [r7, #24]
   41174:	6abb      	ldr	r3, [r7, #40]	; 0x28
   41176:	441a      	add	r2, r3
   41178:	2307      	movs	r3, #7
   4117a:	009b      	lsls	r3, r3, #2
   4117c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41180:	440b      	add	r3, r1
   41182:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41186:	4413      	add	r3, r2
   41188:	61bb      	str	r3, [r7, #24]
   4118a:	6cba      	ldr	r2, [r7, #72]	; 0x48
   4118c:	69bb      	ldr	r3, [r7, #24]
   4118e:	4053      	eors	r3, r2
   41190:	2108      	movs	r1, #8
   41192:	4618      	mov	r0, r3
   41194:	f7ff fcfe 	bl	40b94 <rotr32>
   41198:	4603      	mov	r3, r0
   4119a:	64bb      	str	r3, [r7, #72]	; 0x48
   4119c:	6bba      	ldr	r2, [r7, #56]	; 0x38
   4119e:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   411a0:	4413      	add	r3, r2
   411a2:	63bb      	str	r3, [r7, #56]	; 0x38
   411a4:	6aba      	ldr	r2, [r7, #40]	; 0x28
   411a6:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   411a8:	4053      	eors	r3, r2
   411aa:	2107      	movs	r1, #7
   411ac:	4618      	mov	r0, r3
   411ae:	f7ff fcf1 	bl	40b94 <rotr32>
   411b2:	4603      	mov	r3, r0
   411b4:	62bb      	str	r3, [r7, #40]	; 0x28
   411b6:	68fa      	ldr	r2, [r7, #12]
   411b8:	6a3b      	ldr	r3, [r7, #32]
   411ba:	441a      	add	r2, r3
   411bc:	2308      	movs	r3, #8
   411be:	009b      	lsls	r3, r3, #2
   411c0:	f107 0190 	add.w	r1, r7, #144	; 0x90
   411c4:	440b      	add	r3, r1
   411c6:	f853 3c44 	ldr.w	r3, [r3, #-68]
   411ca:	4413      	add	r3, r2
   411cc:	60fb      	str	r3, [r7, #12]
   411ce:	6cba      	ldr	r2, [r7, #72]	; 0x48
   411d0:	68fb      	ldr	r3, [r7, #12]
   411d2:	4053      	eors	r3, r2
   411d4:	2110      	movs	r1, #16
   411d6:	4618      	mov	r0, r3
   411d8:	f7ff fcdc 	bl	40b94 <rotr32>
   411dc:	4603      	mov	r3, r0
   411de:	64bb      	str	r3, [r7, #72]	; 0x48
   411e0:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   411e2:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   411e4:	4413      	add	r3, r2
   411e6:	637b      	str	r3, [r7, #52]	; 0x34
   411e8:	6a3a      	ldr	r2, [r7, #32]
   411ea:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   411ec:	4053      	eors	r3, r2
   411ee:	210c      	movs	r1, #12
   411f0:	4618      	mov	r0, r3
   411f2:	f7ff fccf 	bl	40b94 <rotr32>
   411f6:	4603      	mov	r3, r0
   411f8:	623b      	str	r3, [r7, #32]
   411fa:	68fa      	ldr	r2, [r7, #12]
   411fc:	6a3b      	ldr	r3, [r7, #32]
   411fe:	441a      	add	r2, r3
   41200:	2309      	movs	r3, #9
   41202:	009b      	lsls	r3, r3, #2
   41204:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41208:	440b      	add	r3, r1
   4120a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4120e:	4413      	add	r3, r2
   41210:	60fb      	str	r3, [r7, #12]
   41212:	6cba      	ldr	r2, [r7, #72]	; 0x48
   41214:	68fb      	ldr	r3, [r7, #12]
   41216:	4053      	eors	r3, r2
   41218:	2108      	movs	r1, #8
   4121a:	4618      	mov	r0, r3
   4121c:	f7ff fcba 	bl	40b94 <rotr32>
   41220:	4603      	mov	r3, r0
   41222:	64bb      	str	r3, [r7, #72]	; 0x48
   41224:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   41226:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   41228:	4413      	add	r3, r2
   4122a:	637b      	str	r3, [r7, #52]	; 0x34
   4122c:	6a3a      	ldr	r2, [r7, #32]
   4122e:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   41230:	4053      	eors	r3, r2
   41232:	2107      	movs	r1, #7
   41234:	4618      	mov	r0, r3
   41236:	f7ff fcad 	bl	40b94 <rotr32>
   4123a:	4603      	mov	r3, r0
   4123c:	623b      	str	r3, [r7, #32]
   4123e:	693a      	ldr	r2, [r7, #16]
   41240:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   41242:	441a      	add	r2, r3
   41244:	230a      	movs	r3, #10
   41246:	009b      	lsls	r3, r3, #2
   41248:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4124c:	440b      	add	r3, r1
   4124e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41252:	4413      	add	r3, r2
   41254:	613b      	str	r3, [r7, #16]
   41256:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   41258:	693b      	ldr	r3, [r7, #16]
   4125a:	4053      	eors	r3, r2
   4125c:	2110      	movs	r1, #16
   4125e:	4618      	mov	r0, r3
   41260:	f7ff fc98 	bl	40b94 <rotr32>
   41264:	4603      	mov	r3, r0
   41266:	63fb      	str	r3, [r7, #60]	; 0x3c
   41268:	6bba      	ldr	r2, [r7, #56]	; 0x38
   4126a:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   4126c:	4413      	add	r3, r2
   4126e:	63bb      	str	r3, [r7, #56]	; 0x38
   41270:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   41272:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   41274:	4053      	eors	r3, r2
   41276:	210c      	movs	r1, #12
   41278:	4618      	mov	r0, r3
   4127a:	f7ff fc8b 	bl	40b94 <rotr32>
   4127e:	4603      	mov	r3, r0
   41280:	627b      	str	r3, [r7, #36]	; 0x24
   41282:	693a      	ldr	r2, [r7, #16]
   41284:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   41286:	441a      	add	r2, r3
   41288:	230b      	movs	r3, #11
   4128a:	009b      	lsls	r3, r3, #2
   4128c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41290:	440b      	add	r3, r1
   41292:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41296:	4413      	add	r3, r2
   41298:	613b      	str	r3, [r7, #16]
   4129a:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   4129c:	693b      	ldr	r3, [r7, #16]
   4129e:	4053      	eors	r3, r2
   412a0:	2108      	movs	r1, #8
   412a2:	4618      	mov	r0, r3
   412a4:	f7ff fc76 	bl	40b94 <rotr32>
   412a8:	4603      	mov	r3, r0
   412aa:	63fb      	str	r3, [r7, #60]	; 0x3c
   412ac:	6bba      	ldr	r2, [r7, #56]	; 0x38
   412ae:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   412b0:	4413      	add	r3, r2
   412b2:	63bb      	str	r3, [r7, #56]	; 0x38
   412b4:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   412b6:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   412b8:	4053      	eors	r3, r2
   412ba:	2107      	movs	r1, #7
   412bc:	4618      	mov	r0, r3
   412be:	f7ff fc69 	bl	40b94 <rotr32>
   412c2:	4603      	mov	r3, r0
   412c4:	627b      	str	r3, [r7, #36]	; 0x24
   412c6:	697a      	ldr	r2, [r7, #20]
   412c8:	6abb      	ldr	r3, [r7, #40]	; 0x28
   412ca:	441a      	add	r2, r3
   412cc:	230c      	movs	r3, #12
   412ce:	009b      	lsls	r3, r3, #2
   412d0:	f107 0190 	add.w	r1, r7, #144	; 0x90
   412d4:	440b      	add	r3, r1
   412d6:	f853 3c44 	ldr.w	r3, [r3, #-68]
   412da:	4413      	add	r3, r2
   412dc:	617b      	str	r3, [r7, #20]
   412de:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   412e0:	697b      	ldr	r3, [r7, #20]
   412e2:	4053      	eors	r3, r2
   412e4:	2110      	movs	r1, #16
   412e6:	4618      	mov	r0, r3
   412e8:	f7ff fc54 	bl	40b94 <rotr32>
   412ec:	4603      	mov	r3, r0
   412ee:	643b      	str	r3, [r7, #64]	; 0x40
   412f0:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   412f2:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   412f4:	4413      	add	r3, r2
   412f6:	62fb      	str	r3, [r7, #44]	; 0x2c
   412f8:	6aba      	ldr	r2, [r7, #40]	; 0x28
   412fa:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   412fc:	4053      	eors	r3, r2
   412fe:	210c      	movs	r1, #12
   41300:	4618      	mov	r0, r3
   41302:	f7ff fc47 	bl	40b94 <rotr32>
   41306:	4603      	mov	r3, r0
   41308:	62bb      	str	r3, [r7, #40]	; 0x28
   4130a:	697a      	ldr	r2, [r7, #20]
   4130c:	6abb      	ldr	r3, [r7, #40]	; 0x28
   4130e:	441a      	add	r2, r3
   41310:	230d      	movs	r3, #13
   41312:	009b      	lsls	r3, r3, #2
   41314:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41318:	440b      	add	r3, r1
   4131a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4131e:	4413      	add	r3, r2
   41320:	617b      	str	r3, [r7, #20]
   41322:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   41324:	697b      	ldr	r3, [r7, #20]
   41326:	4053      	eors	r3, r2
   41328:	2108      	movs	r1, #8
   4132a:	4618      	mov	r0, r3
   4132c:	f7ff fc32 	bl	40b94 <rotr32>
   41330:	4603      	mov	r3, r0
   41332:	643b      	str	r3, [r7, #64]	; 0x40
   41334:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   41336:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   41338:	4413      	add	r3, r2
   4133a:	62fb      	str	r3, [r7, #44]	; 0x2c
   4133c:	6aba      	ldr	r2, [r7, #40]	; 0x28
   4133e:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   41340:	4053      	eors	r3, r2
   41342:	2107      	movs	r1, #7
   41344:	4618      	mov	r0, r3
   41346:	f7ff fc25 	bl	40b94 <rotr32>
   4134a:	4603      	mov	r3, r0
   4134c:	62bb      	str	r3, [r7, #40]	; 0x28
   4134e:	69ba      	ldr	r2, [r7, #24]
   41350:	69fb      	ldr	r3, [r7, #28]
   41352:	441a      	add	r2, r3
   41354:	230e      	movs	r3, #14
   41356:	009b      	lsls	r3, r3, #2
   41358:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4135c:	440b      	add	r3, r1
   4135e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41362:	4413      	add	r3, r2
   41364:	61bb      	str	r3, [r7, #24]
   41366:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   41368:	69bb      	ldr	r3, [r7, #24]
   4136a:	4053      	eors	r3, r2
   4136c:	2110      	movs	r1, #16
   4136e:	4618      	mov	r0, r3
   41370:	f7ff fc10 	bl	40b94 <rotr32>
   41374:	4603      	mov	r3, r0
   41376:	647b      	str	r3, [r7, #68]	; 0x44
   41378:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   4137a:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   4137c:	4413      	add	r3, r2
   4137e:	633b      	str	r3, [r7, #48]	; 0x30
   41380:	69fa      	ldr	r2, [r7, #28]
   41382:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   41384:	4053      	eors	r3, r2
   41386:	210c      	movs	r1, #12
   41388:	4618      	mov	r0, r3
   4138a:	f7ff fc03 	bl	40b94 <rotr32>
   4138e:	4603      	mov	r3, r0
   41390:	61fb      	str	r3, [r7, #28]
   41392:	69ba      	ldr	r2, [r7, #24]
   41394:	69fb      	ldr	r3, [r7, #28]
   41396:	441a      	add	r2, r3
   41398:	230f      	movs	r3, #15
   4139a:	009b      	lsls	r3, r3, #2
   4139c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   413a0:	440b      	add	r3, r1
   413a2:	f853 3c44 	ldr.w	r3, [r3, #-68]
   413a6:	4413      	add	r3, r2
   413a8:	61bb      	str	r3, [r7, #24]
   413aa:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   413ac:	69bb      	ldr	r3, [r7, #24]
   413ae:	4053      	eors	r3, r2
   413b0:	2108      	movs	r1, #8
   413b2:	4618      	mov	r0, r3
   413b4:	f7ff fbee 	bl	40b94 <rotr32>
   413b8:	4603      	mov	r3, r0
   413ba:	647b      	str	r3, [r7, #68]	; 0x44
   413bc:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   413be:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   413c0:	4413      	add	r3, r2
   413c2:	633b      	str	r3, [r7, #48]	; 0x30
   413c4:	69fa      	ldr	r2, [r7, #28]
   413c6:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   413c8:	4053      	eors	r3, r2
   413ca:	2107      	movs	r1, #7
   413cc:	4618      	mov	r0, r3
   413ce:	f7ff fbe1 	bl	40b94 <rotr32>
   413d2:	4603      	mov	r3, r0
   413d4:	61fb      	str	r3, [r7, #28]
   413d6:	68fa      	ldr	r2, [r7, #12]
   413d8:	69fb      	ldr	r3, [r7, #28]
   413da:	441a      	add	r2, r3
   413dc:	230e      	movs	r3, #14
   413de:	009b      	lsls	r3, r3, #2
   413e0:	f107 0190 	add.w	r1, r7, #144	; 0x90
   413e4:	440b      	add	r3, r1
   413e6:	f853 3c44 	ldr.w	r3, [r3, #-68]
   413ea:	4413      	add	r3, r2
   413ec:	60fb      	str	r3, [r7, #12]
   413ee:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   413f0:	68fb      	ldr	r3, [r7, #12]
   413f2:	4053      	eors	r3, r2
   413f4:	2110      	movs	r1, #16
   413f6:	4618      	mov	r0, r3
   413f8:	f7ff fbcc 	bl	40b94 <rotr32>
   413fc:	4603      	mov	r3, r0
   413fe:	63fb      	str	r3, [r7, #60]	; 0x3c
   41400:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   41402:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   41404:	4413      	add	r3, r2
   41406:	62fb      	str	r3, [r7, #44]	; 0x2c
   41408:	69fa      	ldr	r2, [r7, #28]
   4140a:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   4140c:	4053      	eors	r3, r2
   4140e:	210c      	movs	r1, #12
   41410:	4618      	mov	r0, r3
   41412:	f7ff fbbf 	bl	40b94 <rotr32>
   41416:	4603      	mov	r3, r0
   41418:	61fb      	str	r3, [r7, #28]
   4141a:	68fa      	ldr	r2, [r7, #12]
   4141c:	69fb      	ldr	r3, [r7, #28]
   4141e:	441a      	add	r2, r3
   41420:	230a      	movs	r3, #10
   41422:	009b      	lsls	r3, r3, #2
   41424:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41428:	440b      	add	r3, r1
   4142a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4142e:	4413      	add	r3, r2
   41430:	60fb      	str	r3, [r7, #12]
   41432:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   41434:	68fb      	ldr	r3, [r7, #12]
   41436:	4053      	eors	r3, r2
   41438:	2108      	movs	r1, #8
   4143a:	4618      	mov	r0, r3
   4143c:	f7ff fbaa 	bl	40b94 <rotr32>
   41440:	4603      	mov	r3, r0
   41442:	63fb      	str	r3, [r7, #60]	; 0x3c
   41444:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   41446:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   41448:	4413      	add	r3, r2
   4144a:	62fb      	str	r3, [r7, #44]	; 0x2c
   4144c:	69fa      	ldr	r2, [r7, #28]
   4144e:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   41450:	4053      	eors	r3, r2
   41452:	2107      	movs	r1, #7
   41454:	4618      	mov	r0, r3
   41456:	f7ff fb9d 	bl	40b94 <rotr32>
   4145a:	4603      	mov	r3, r0
   4145c:	61fb      	str	r3, [r7, #28]
   4145e:	693a      	ldr	r2, [r7, #16]
   41460:	6a3b      	ldr	r3, [r7, #32]
   41462:	441a      	add	r2, r3
   41464:	2304      	movs	r3, #4
   41466:	009b      	lsls	r3, r3, #2
   41468:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4146c:	440b      	add	r3, r1
   4146e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41472:	4413      	add	r3, r2
   41474:	613b      	str	r3, [r7, #16]
   41476:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   41478:	693b      	ldr	r3, [r7, #16]
   4147a:	4053      	eors	r3, r2
   4147c:	2110      	movs	r1, #16
   4147e:	4618      	mov	r0, r3
   41480:	f7ff fb88 	bl	40b94 <rotr32>
   41484:	4603      	mov	r3, r0
   41486:	643b      	str	r3, [r7, #64]	; 0x40
   41488:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   4148a:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   4148c:	4413      	add	r3, r2
   4148e:	633b      	str	r3, [r7, #48]	; 0x30
   41490:	6a3a      	ldr	r2, [r7, #32]
   41492:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   41494:	4053      	eors	r3, r2
   41496:	210c      	movs	r1, #12
   41498:	4618      	mov	r0, r3
   4149a:	f7ff fb7b 	bl	40b94 <rotr32>
   4149e:	4603      	mov	r3, r0
   414a0:	623b      	str	r3, [r7, #32]
   414a2:	693a      	ldr	r2, [r7, #16]
   414a4:	6a3b      	ldr	r3, [r7, #32]
   414a6:	441a      	add	r2, r3
   414a8:	2308      	movs	r3, #8
   414aa:	009b      	lsls	r3, r3, #2
   414ac:	f107 0190 	add.w	r1, r7, #144	; 0x90
   414b0:	440b      	add	r3, r1
   414b2:	f853 3c44 	ldr.w	r3, [r3, #-68]
   414b6:	4413      	add	r3, r2
   414b8:	613b      	str	r3, [r7, #16]
   414ba:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   414bc:	693b      	ldr	r3, [r7, #16]
   414be:	4053      	eors	r3, r2
   414c0:	2108      	movs	r1, #8
   414c2:	4618      	mov	r0, r3
   414c4:	f7ff fb66 	bl	40b94 <rotr32>
   414c8:	4603      	mov	r3, r0
   414ca:	643b      	str	r3, [r7, #64]	; 0x40
   414cc:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   414ce:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   414d0:	4413      	add	r3, r2
   414d2:	633b      	str	r3, [r7, #48]	; 0x30
   414d4:	6a3a      	ldr	r2, [r7, #32]
   414d6:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   414d8:	4053      	eors	r3, r2
   414da:	2107      	movs	r1, #7
   414dc:	4618      	mov	r0, r3
   414de:	f7ff fb59 	bl	40b94 <rotr32>
   414e2:	4603      	mov	r3, r0
   414e4:	623b      	str	r3, [r7, #32]
   414e6:	697a      	ldr	r2, [r7, #20]
   414e8:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   414ea:	441a      	add	r2, r3
   414ec:	2309      	movs	r3, #9
   414ee:	009b      	lsls	r3, r3, #2
   414f0:	f107 0190 	add.w	r1, r7, #144	; 0x90
   414f4:	440b      	add	r3, r1
   414f6:	f853 3c44 	ldr.w	r3, [r3, #-68]
   414fa:	4413      	add	r3, r2
   414fc:	617b      	str	r3, [r7, #20]
   414fe:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   41500:	697b      	ldr	r3, [r7, #20]
   41502:	4053      	eors	r3, r2
   41504:	2110      	movs	r1, #16
   41506:	4618      	mov	r0, r3
   41508:	f7ff fb44 	bl	40b94 <rotr32>
   4150c:	4603      	mov	r3, r0
   4150e:	647b      	str	r3, [r7, #68]	; 0x44
   41510:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   41512:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   41514:	4413      	add	r3, r2
   41516:	637b      	str	r3, [r7, #52]	; 0x34
   41518:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   4151a:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   4151c:	4053      	eors	r3, r2
   4151e:	210c      	movs	r1, #12
   41520:	4618      	mov	r0, r3
   41522:	f7ff fb37 	bl	40b94 <rotr32>
   41526:	4603      	mov	r3, r0
   41528:	627b      	str	r3, [r7, #36]	; 0x24
   4152a:	697a      	ldr	r2, [r7, #20]
   4152c:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   4152e:	441a      	add	r2, r3
   41530:	230f      	movs	r3, #15
   41532:	009b      	lsls	r3, r3, #2
   41534:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41538:	440b      	add	r3, r1
   4153a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4153e:	4413      	add	r3, r2
   41540:	617b      	str	r3, [r7, #20]
   41542:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   41544:	697b      	ldr	r3, [r7, #20]
   41546:	4053      	eors	r3, r2
   41548:	2108      	movs	r1, #8
   4154a:	4618      	mov	r0, r3
   4154c:	f7ff fb22 	bl	40b94 <rotr32>
   41550:	4603      	mov	r3, r0
   41552:	647b      	str	r3, [r7, #68]	; 0x44
   41554:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   41556:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   41558:	4413      	add	r3, r2
   4155a:	637b      	str	r3, [r7, #52]	; 0x34
   4155c:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   4155e:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   41560:	4053      	eors	r3, r2
   41562:	2107      	movs	r1, #7
   41564:	4618      	mov	r0, r3
   41566:	f7ff fb15 	bl	40b94 <rotr32>
   4156a:	4603      	mov	r3, r0
   4156c:	627b      	str	r3, [r7, #36]	; 0x24
   4156e:	69ba      	ldr	r2, [r7, #24]
   41570:	6abb      	ldr	r3, [r7, #40]	; 0x28
   41572:	441a      	add	r2, r3
   41574:	230d      	movs	r3, #13
   41576:	009b      	lsls	r3, r3, #2
   41578:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4157c:	440b      	add	r3, r1
   4157e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41582:	4413      	add	r3, r2
   41584:	61bb      	str	r3, [r7, #24]
   41586:	6cba      	ldr	r2, [r7, #72]	; 0x48
   41588:	69bb      	ldr	r3, [r7, #24]
   4158a:	4053      	eors	r3, r2
   4158c:	2110      	movs	r1, #16
   4158e:	4618      	mov	r0, r3
   41590:	f7ff fb00 	bl	40b94 <rotr32>
   41594:	4603      	mov	r3, r0
   41596:	64bb      	str	r3, [r7, #72]	; 0x48
   41598:	6bba      	ldr	r2, [r7, #56]	; 0x38
   4159a:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   4159c:	4413      	add	r3, r2
   4159e:	63bb      	str	r3, [r7, #56]	; 0x38
   415a0:	6aba      	ldr	r2, [r7, #40]	; 0x28
   415a2:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   415a4:	4053      	eors	r3, r2
   415a6:	210c      	movs	r1, #12
   415a8:	4618      	mov	r0, r3
   415aa:	f7ff faf3 	bl	40b94 <rotr32>
   415ae:	4603      	mov	r3, r0
   415b0:	62bb      	str	r3, [r7, #40]	; 0x28
   415b2:	69ba      	ldr	r2, [r7, #24]
   415b4:	6abb      	ldr	r3, [r7, #40]	; 0x28
   415b6:	441a      	add	r2, r3
   415b8:	2306      	movs	r3, #6
   415ba:	009b      	lsls	r3, r3, #2
   415bc:	f107 0190 	add.w	r1, r7, #144	; 0x90
   415c0:	440b      	add	r3, r1
   415c2:	f853 3c44 	ldr.w	r3, [r3, #-68]
   415c6:	4413      	add	r3, r2
   415c8:	61bb      	str	r3, [r7, #24]
   415ca:	6cba      	ldr	r2, [r7, #72]	; 0x48
   415cc:	69bb      	ldr	r3, [r7, #24]
   415ce:	4053      	eors	r3, r2
   415d0:	2108      	movs	r1, #8
   415d2:	4618      	mov	r0, r3
   415d4:	f7ff fade 	bl	40b94 <rotr32>
   415d8:	4603      	mov	r3, r0
   415da:	64bb      	str	r3, [r7, #72]	; 0x48
   415dc:	6bba      	ldr	r2, [r7, #56]	; 0x38
   415de:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   415e0:	4413      	add	r3, r2
   415e2:	63bb      	str	r3, [r7, #56]	; 0x38
   415e4:	6aba      	ldr	r2, [r7, #40]	; 0x28
   415e6:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   415e8:	4053      	eors	r3, r2
   415ea:	2107      	movs	r1, #7
   415ec:	4618      	mov	r0, r3
   415ee:	f7ff fad1 	bl	40b94 <rotr32>
   415f2:	4603      	mov	r3, r0
   415f4:	62bb      	str	r3, [r7, #40]	; 0x28
   415f6:	68fa      	ldr	r2, [r7, #12]
   415f8:	6a3b      	ldr	r3, [r7, #32]
   415fa:	441a      	add	r2, r3
   415fc:	2301      	movs	r3, #1
   415fe:	009b      	lsls	r3, r3, #2
   41600:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41604:	440b      	add	r3, r1
   41606:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4160a:	4413      	add	r3, r2
   4160c:	60fb      	str	r3, [r7, #12]
   4160e:	6cba      	ldr	r2, [r7, #72]	; 0x48
   41610:	68fb      	ldr	r3, [r7, #12]
   41612:	4053      	eors	r3, r2
   41614:	2110      	movs	r1, #16
   41616:	4618      	mov	r0, r3
   41618:	f7ff fabc 	bl	40b94 <rotr32>
   4161c:	4603      	mov	r3, r0
   4161e:	64bb      	str	r3, [r7, #72]	; 0x48
   41620:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   41622:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   41624:	4413      	add	r3, r2
   41626:	637b      	str	r3, [r7, #52]	; 0x34
   41628:	6a3a      	ldr	r2, [r7, #32]
   4162a:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   4162c:	4053      	eors	r3, r2
   4162e:	210c      	movs	r1, #12
   41630:	4618      	mov	r0, r3
   41632:	f7ff faaf 	bl	40b94 <rotr32>
   41636:	4603      	mov	r3, r0
   41638:	623b      	str	r3, [r7, #32]
   4163a:	68fa      	ldr	r2, [r7, #12]
   4163c:	6a3b      	ldr	r3, [r7, #32]
   4163e:	441a      	add	r2, r3
   41640:	230c      	movs	r3, #12
   41642:	009b      	lsls	r3, r3, #2
   41644:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41648:	440b      	add	r3, r1
   4164a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4164e:	4413      	add	r3, r2
   41650:	60fb      	str	r3, [r7, #12]
   41652:	6cba      	ldr	r2, [r7, #72]	; 0x48
   41654:	68fb      	ldr	r3, [r7, #12]
   41656:	4053      	eors	r3, r2
   41658:	2108      	movs	r1, #8
   4165a:	4618      	mov	r0, r3
   4165c:	f7ff fa9a 	bl	40b94 <rotr32>
   41660:	4603      	mov	r3, r0
   41662:	64bb      	str	r3, [r7, #72]	; 0x48
   41664:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   41666:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   41668:	4413      	add	r3, r2
   4166a:	637b      	str	r3, [r7, #52]	; 0x34
   4166c:	6a3a      	ldr	r2, [r7, #32]
   4166e:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   41670:	4053      	eors	r3, r2
   41672:	2107      	movs	r1, #7
   41674:	4618      	mov	r0, r3
   41676:	f7ff fa8d 	bl	40b94 <rotr32>
   4167a:	4603      	mov	r3, r0
   4167c:	623b      	str	r3, [r7, #32]
   4167e:	693a      	ldr	r2, [r7, #16]
   41680:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   41682:	441a      	add	r2, r3
   41684:	2300      	movs	r3, #0
   41686:	009b      	lsls	r3, r3, #2
   41688:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4168c:	440b      	add	r3, r1
   4168e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41692:	4413      	add	r3, r2
   41694:	613b      	str	r3, [r7, #16]
   41696:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   41698:	693b      	ldr	r3, [r7, #16]
   4169a:	4053      	eors	r3, r2
   4169c:	2110      	movs	r1, #16
   4169e:	4618      	mov	r0, r3
   416a0:	f7ff fa78 	bl	40b94 <rotr32>
   416a4:	4603      	mov	r3, r0
   416a6:	63fb      	str	r3, [r7, #60]	; 0x3c
   416a8:	6bba      	ldr	r2, [r7, #56]	; 0x38
   416aa:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   416ac:	4413      	add	r3, r2
   416ae:	63bb      	str	r3, [r7, #56]	; 0x38
   416b0:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   416b2:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   416b4:	4053      	eors	r3, r2
   416b6:	210c      	movs	r1, #12
   416b8:	4618      	mov	r0, r3
   416ba:	f7ff fa6b 	bl	40b94 <rotr32>
   416be:	4603      	mov	r3, r0
   416c0:	627b      	str	r3, [r7, #36]	; 0x24
   416c2:	693a      	ldr	r2, [r7, #16]
   416c4:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   416c6:	441a      	add	r2, r3
   416c8:	2302      	movs	r3, #2
   416ca:	009b      	lsls	r3, r3, #2
   416cc:	f107 0190 	add.w	r1, r7, #144	; 0x90
   416d0:	440b      	add	r3, r1
   416d2:	f853 3c44 	ldr.w	r3, [r3, #-68]
   416d6:	4413      	add	r3, r2
   416d8:	613b      	str	r3, [r7, #16]
   416da:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   416dc:	693b      	ldr	r3, [r7, #16]
   416de:	4053      	eors	r3, r2
   416e0:	2108      	movs	r1, #8
   416e2:	4618      	mov	r0, r3
   416e4:	f7ff fa56 	bl	40b94 <rotr32>
   416e8:	4603      	mov	r3, r0
   416ea:	63fb      	str	r3, [r7, #60]	; 0x3c
   416ec:	6bba      	ldr	r2, [r7, #56]	; 0x38
   416ee:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   416f0:	4413      	add	r3, r2
   416f2:	63bb      	str	r3, [r7, #56]	; 0x38
   416f4:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   416f6:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   416f8:	4053      	eors	r3, r2
   416fa:	2107      	movs	r1, #7
   416fc:	4618      	mov	r0, r3
   416fe:	f7ff fa49 	bl	40b94 <rotr32>
   41702:	4603      	mov	r3, r0
   41704:	627b      	str	r3, [r7, #36]	; 0x24
   41706:	697a      	ldr	r2, [r7, #20]
   41708:	6abb      	ldr	r3, [r7, #40]	; 0x28
   4170a:	441a      	add	r2, r3
   4170c:	230b      	movs	r3, #11
   4170e:	009b      	lsls	r3, r3, #2
   41710:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41714:	440b      	add	r3, r1
   41716:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4171a:	4413      	add	r3, r2
   4171c:	617b      	str	r3, [r7, #20]
   4171e:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   41720:	697b      	ldr	r3, [r7, #20]
   41722:	4053      	eors	r3, r2
   41724:	2110      	movs	r1, #16
   41726:	4618      	mov	r0, r3
   41728:	f7ff fa34 	bl	40b94 <rotr32>
   4172c:	4603      	mov	r3, r0
   4172e:	643b      	str	r3, [r7, #64]	; 0x40
   41730:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   41732:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   41734:	4413      	add	r3, r2
   41736:	62fb      	str	r3, [r7, #44]	; 0x2c
   41738:	6aba      	ldr	r2, [r7, #40]	; 0x28
   4173a:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   4173c:	4053      	eors	r3, r2
   4173e:	210c      	movs	r1, #12
   41740:	4618      	mov	r0, r3
   41742:	f7ff fa27 	bl	40b94 <rotr32>
   41746:	4603      	mov	r3, r0
   41748:	62bb      	str	r3, [r7, #40]	; 0x28
   4174a:	697a      	ldr	r2, [r7, #20]
   4174c:	6abb      	ldr	r3, [r7, #40]	; 0x28
   4174e:	441a      	add	r2, r3
   41750:	2307      	movs	r3, #7
   41752:	009b      	lsls	r3, r3, #2
   41754:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41758:	440b      	add	r3, r1
   4175a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4175e:	4413      	add	r3, r2
   41760:	617b      	str	r3, [r7, #20]
   41762:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   41764:	697b      	ldr	r3, [r7, #20]
   41766:	4053      	eors	r3, r2
   41768:	2108      	movs	r1, #8
   4176a:	4618      	mov	r0, r3
   4176c:	f7ff fa12 	bl	40b94 <rotr32>
   41770:	4603      	mov	r3, r0
   41772:	643b      	str	r3, [r7, #64]	; 0x40
   41774:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   41776:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   41778:	4413      	add	r3, r2
   4177a:	62fb      	str	r3, [r7, #44]	; 0x2c
   4177c:	6aba      	ldr	r2, [r7, #40]	; 0x28
   4177e:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   41780:	4053      	eors	r3, r2
   41782:	2107      	movs	r1, #7
   41784:	4618      	mov	r0, r3
   41786:	f7ff fa05 	bl	40b94 <rotr32>
   4178a:	4603      	mov	r3, r0
   4178c:	62bb      	str	r3, [r7, #40]	; 0x28
   4178e:	69ba      	ldr	r2, [r7, #24]
   41790:	69fb      	ldr	r3, [r7, #28]
   41792:	441a      	add	r2, r3
   41794:	2305      	movs	r3, #5
   41796:	009b      	lsls	r3, r3, #2
   41798:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4179c:	440b      	add	r3, r1
   4179e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   417a2:	4413      	add	r3, r2
   417a4:	61bb      	str	r3, [r7, #24]
   417a6:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   417a8:	69bb      	ldr	r3, [r7, #24]
   417aa:	4053      	eors	r3, r2
   417ac:	2110      	movs	r1, #16
   417ae:	4618      	mov	r0, r3
   417b0:	f7ff f9f0 	bl	40b94 <rotr32>
   417b4:	4603      	mov	r3, r0
   417b6:	647b      	str	r3, [r7, #68]	; 0x44
   417b8:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   417ba:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   417bc:	4413      	add	r3, r2
   417be:	633b      	str	r3, [r7, #48]	; 0x30
   417c0:	69fa      	ldr	r2, [r7, #28]
   417c2:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   417c4:	4053      	eors	r3, r2
   417c6:	210c      	movs	r1, #12
   417c8:	4618      	mov	r0, r3
   417ca:	f7ff f9e3 	bl	40b94 <rotr32>
   417ce:	4603      	mov	r3, r0
   417d0:	61fb      	str	r3, [r7, #28]
   417d2:	69ba      	ldr	r2, [r7, #24]
   417d4:	69fb      	ldr	r3, [r7, #28]
   417d6:	441a      	add	r2, r3
   417d8:	2303      	movs	r3, #3
   417da:	009b      	lsls	r3, r3, #2
   417dc:	f107 0190 	add.w	r1, r7, #144	; 0x90
   417e0:	440b      	add	r3, r1
   417e2:	f853 3c44 	ldr.w	r3, [r3, #-68]
   417e6:	4413      	add	r3, r2
   417e8:	61bb      	str	r3, [r7, #24]
   417ea:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   417ec:	69bb      	ldr	r3, [r7, #24]
   417ee:	4053      	eors	r3, r2
   417f0:	2108      	movs	r1, #8
   417f2:	4618      	mov	r0, r3
   417f4:	f7ff f9ce 	bl	40b94 <rotr32>
   417f8:	4603      	mov	r3, r0
   417fa:	647b      	str	r3, [r7, #68]	; 0x44
   417fc:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   417fe:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   41800:	4413      	add	r3, r2
   41802:	633b      	str	r3, [r7, #48]	; 0x30
   41804:	69fa      	ldr	r2, [r7, #28]
   41806:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   41808:	4053      	eors	r3, r2
   4180a:	2107      	movs	r1, #7
   4180c:	4618      	mov	r0, r3
   4180e:	f7ff f9c1 	bl	40b94 <rotr32>
   41812:	4603      	mov	r3, r0
   41814:	61fb      	str	r3, [r7, #28]
   41816:	68fa      	ldr	r2, [r7, #12]
   41818:	69fb      	ldr	r3, [r7, #28]
   4181a:	441a      	add	r2, r3
   4181c:	230b      	movs	r3, #11
   4181e:	009b      	lsls	r3, r3, #2
   41820:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41824:	440b      	add	r3, r1
   41826:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4182a:	4413      	add	r3, r2
   4182c:	60fb      	str	r3, [r7, #12]
   4182e:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   41830:	68fb      	ldr	r3, [r7, #12]
   41832:	4053      	eors	r3, r2
   41834:	2110      	movs	r1, #16
   41836:	4618      	mov	r0, r3
   41838:	f7ff f9ac 	bl	40b94 <rotr32>
   4183c:	4603      	mov	r3, r0
   4183e:	63fb      	str	r3, [r7, #60]	; 0x3c
   41840:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   41842:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   41844:	4413      	add	r3, r2
   41846:	62fb      	str	r3, [r7, #44]	; 0x2c
   41848:	69fa      	ldr	r2, [r7, #28]
   4184a:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   4184c:	4053      	eors	r3, r2
   4184e:	210c      	movs	r1, #12
   41850:	4618      	mov	r0, r3
   41852:	f7ff f99f 	bl	40b94 <rotr32>
   41856:	4603      	mov	r3, r0
   41858:	61fb      	str	r3, [r7, #28]
   4185a:	68fa      	ldr	r2, [r7, #12]
   4185c:	69fb      	ldr	r3, [r7, #28]
   4185e:	441a      	add	r2, r3
   41860:	2308      	movs	r3, #8
   41862:	009b      	lsls	r3, r3, #2
   41864:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41868:	440b      	add	r3, r1
   4186a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4186e:	4413      	add	r3, r2
   41870:	60fb      	str	r3, [r7, #12]
   41872:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   41874:	68fb      	ldr	r3, [r7, #12]
   41876:	4053      	eors	r3, r2
   41878:	2108      	movs	r1, #8
   4187a:	4618      	mov	r0, r3
   4187c:	f7ff f98a 	bl	40b94 <rotr32>
   41880:	4603      	mov	r3, r0
   41882:	63fb      	str	r3, [r7, #60]	; 0x3c
   41884:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   41886:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   41888:	4413      	add	r3, r2
   4188a:	62fb      	str	r3, [r7, #44]	; 0x2c
   4188c:	69fa      	ldr	r2, [r7, #28]
   4188e:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   41890:	4053      	eors	r3, r2
   41892:	2107      	movs	r1, #7
   41894:	4618      	mov	r0, r3
   41896:	f7ff f97d 	bl	40b94 <rotr32>
   4189a:	4603      	mov	r3, r0
   4189c:	61fb      	str	r3, [r7, #28]
   4189e:	693a      	ldr	r2, [r7, #16]
   418a0:	6a3b      	ldr	r3, [r7, #32]
   418a2:	441a      	add	r2, r3
   418a4:	230c      	movs	r3, #12
   418a6:	009b      	lsls	r3, r3, #2
   418a8:	f107 0190 	add.w	r1, r7, #144	; 0x90
   418ac:	440b      	add	r3, r1
   418ae:	f853 3c44 	ldr.w	r3, [r3, #-68]
   418b2:	4413      	add	r3, r2
   418b4:	613b      	str	r3, [r7, #16]
   418b6:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   418b8:	693b      	ldr	r3, [r7, #16]
   418ba:	4053      	eors	r3, r2
   418bc:	2110      	movs	r1, #16
   418be:	4618      	mov	r0, r3
   418c0:	f7ff f968 	bl	40b94 <rotr32>
   418c4:	4603      	mov	r3, r0
   418c6:	643b      	str	r3, [r7, #64]	; 0x40
   418c8:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   418ca:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   418cc:	4413      	add	r3, r2
   418ce:	633b      	str	r3, [r7, #48]	; 0x30
   418d0:	6a3a      	ldr	r2, [r7, #32]
   418d2:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   418d4:	4053      	eors	r3, r2
   418d6:	210c      	movs	r1, #12
   418d8:	4618      	mov	r0, r3
   418da:	f7ff f95b 	bl	40b94 <rotr32>
   418de:	4603      	mov	r3, r0
   418e0:	623b      	str	r3, [r7, #32]
   418e2:	693a      	ldr	r2, [r7, #16]
   418e4:	6a3b      	ldr	r3, [r7, #32]
   418e6:	441a      	add	r2, r3
   418e8:	2300      	movs	r3, #0
   418ea:	009b      	lsls	r3, r3, #2
   418ec:	f107 0190 	add.w	r1, r7, #144	; 0x90
   418f0:	440b      	add	r3, r1
   418f2:	f853 3c44 	ldr.w	r3, [r3, #-68]
   418f6:	4413      	add	r3, r2
   418f8:	613b      	str	r3, [r7, #16]
   418fa:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   418fc:	693b      	ldr	r3, [r7, #16]
   418fe:	4053      	eors	r3, r2
   41900:	2108      	movs	r1, #8
   41902:	4618      	mov	r0, r3
   41904:	f7ff f946 	bl	40b94 <rotr32>
   41908:	4603      	mov	r3, r0
   4190a:	643b      	str	r3, [r7, #64]	; 0x40
   4190c:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   4190e:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   41910:	4413      	add	r3, r2
   41912:	633b      	str	r3, [r7, #48]	; 0x30
   41914:	6a3a      	ldr	r2, [r7, #32]
   41916:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   41918:	4053      	eors	r3, r2
   4191a:	2107      	movs	r1, #7
   4191c:	4618      	mov	r0, r3
   4191e:	f7ff f939 	bl	40b94 <rotr32>
   41922:	4603      	mov	r3, r0
   41924:	623b      	str	r3, [r7, #32]
   41926:	697a      	ldr	r2, [r7, #20]
   41928:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   4192a:	441a      	add	r2, r3
   4192c:	2305      	movs	r3, #5
   4192e:	009b      	lsls	r3, r3, #2
   41930:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41934:	440b      	add	r3, r1
   41936:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4193a:	4413      	add	r3, r2
   4193c:	617b      	str	r3, [r7, #20]
   4193e:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   41940:	697b      	ldr	r3, [r7, #20]
   41942:	4053      	eors	r3, r2
   41944:	2110      	movs	r1, #16
   41946:	4618      	mov	r0, r3
   41948:	f7ff f924 	bl	40b94 <rotr32>
   4194c:	4603      	mov	r3, r0
   4194e:	647b      	str	r3, [r7, #68]	; 0x44
   41950:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   41952:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   41954:	4413      	add	r3, r2
   41956:	637b      	str	r3, [r7, #52]	; 0x34
   41958:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   4195a:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   4195c:	4053      	eors	r3, r2
   4195e:	210c      	movs	r1, #12
   41960:	4618      	mov	r0, r3
   41962:	f7ff f917 	bl	40b94 <rotr32>
   41966:	4603      	mov	r3, r0
   41968:	627b      	str	r3, [r7, #36]	; 0x24
   4196a:	697a      	ldr	r2, [r7, #20]
   4196c:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   4196e:	441a      	add	r2, r3
   41970:	2302      	movs	r3, #2
   41972:	009b      	lsls	r3, r3, #2
   41974:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41978:	440b      	add	r3, r1
   4197a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4197e:	4413      	add	r3, r2
   41980:	617b      	str	r3, [r7, #20]
   41982:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   41984:	697b      	ldr	r3, [r7, #20]
   41986:	4053      	eors	r3, r2
   41988:	2108      	movs	r1, #8
   4198a:	4618      	mov	r0, r3
   4198c:	f7ff f902 	bl	40b94 <rotr32>
   41990:	4603      	mov	r3, r0
   41992:	647b      	str	r3, [r7, #68]	; 0x44
   41994:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   41996:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   41998:	4413      	add	r3, r2
   4199a:	637b      	str	r3, [r7, #52]	; 0x34
   4199c:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   4199e:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   419a0:	4053      	eors	r3, r2
   419a2:	2107      	movs	r1, #7
   419a4:	4618      	mov	r0, r3
   419a6:	f7ff f8f5 	bl	40b94 <rotr32>
   419aa:	4603      	mov	r3, r0
   419ac:	627b      	str	r3, [r7, #36]	; 0x24
   419ae:	69ba      	ldr	r2, [r7, #24]
   419b0:	6abb      	ldr	r3, [r7, #40]	; 0x28
   419b2:	441a      	add	r2, r3
   419b4:	230f      	movs	r3, #15
   419b6:	009b      	lsls	r3, r3, #2
   419b8:	f107 0190 	add.w	r1, r7, #144	; 0x90
   419bc:	440b      	add	r3, r1
   419be:	f853 3c44 	ldr.w	r3, [r3, #-68]
   419c2:	4413      	add	r3, r2
   419c4:	61bb      	str	r3, [r7, #24]
   419c6:	6cba      	ldr	r2, [r7, #72]	; 0x48
   419c8:	69bb      	ldr	r3, [r7, #24]
   419ca:	4053      	eors	r3, r2
   419cc:	2110      	movs	r1, #16
   419ce:	4618      	mov	r0, r3
   419d0:	f7ff f8e0 	bl	40b94 <rotr32>
   419d4:	4603      	mov	r3, r0
   419d6:	64bb      	str	r3, [r7, #72]	; 0x48
   419d8:	6bba      	ldr	r2, [r7, #56]	; 0x38
   419da:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   419dc:	4413      	add	r3, r2
   419de:	63bb      	str	r3, [r7, #56]	; 0x38
   419e0:	6aba      	ldr	r2, [r7, #40]	; 0x28
   419e2:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   419e4:	4053      	eors	r3, r2
   419e6:	210c      	movs	r1, #12
   419e8:	4618      	mov	r0, r3
   419ea:	f7ff f8d3 	bl	40b94 <rotr32>
   419ee:	4603      	mov	r3, r0
   419f0:	62bb      	str	r3, [r7, #40]	; 0x28
   419f2:	69ba      	ldr	r2, [r7, #24]
   419f4:	6abb      	ldr	r3, [r7, #40]	; 0x28
   419f6:	441a      	add	r2, r3
   419f8:	230d      	movs	r3, #13
   419fa:	009b      	lsls	r3, r3, #2
   419fc:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41a00:	440b      	add	r3, r1
   41a02:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41a06:	4413      	add	r3, r2
   41a08:	61bb      	str	r3, [r7, #24]
   41a0a:	6cba      	ldr	r2, [r7, #72]	; 0x48
   41a0c:	69bb      	ldr	r3, [r7, #24]
   41a0e:	4053      	eors	r3, r2
   41a10:	2108      	movs	r1, #8
   41a12:	4618      	mov	r0, r3
   41a14:	f7ff f8be 	bl	40b94 <rotr32>
   41a18:	4603      	mov	r3, r0
   41a1a:	64bb      	str	r3, [r7, #72]	; 0x48
   41a1c:	6bba      	ldr	r2, [r7, #56]	; 0x38
   41a1e:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   41a20:	4413      	add	r3, r2
   41a22:	63bb      	str	r3, [r7, #56]	; 0x38
   41a24:	6aba      	ldr	r2, [r7, #40]	; 0x28
   41a26:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   41a28:	4053      	eors	r3, r2
   41a2a:	2107      	movs	r1, #7
   41a2c:	4618      	mov	r0, r3
   41a2e:	f7ff f8b1 	bl	40b94 <rotr32>
   41a32:	4603      	mov	r3, r0
   41a34:	62bb      	str	r3, [r7, #40]	; 0x28
   41a36:	68fa      	ldr	r2, [r7, #12]
   41a38:	6a3b      	ldr	r3, [r7, #32]
   41a3a:	441a      	add	r2, r3
   41a3c:	230a      	movs	r3, #10
   41a3e:	009b      	lsls	r3, r3, #2
   41a40:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41a44:	440b      	add	r3, r1
   41a46:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41a4a:	4413      	add	r3, r2
   41a4c:	60fb      	str	r3, [r7, #12]
   41a4e:	6cba      	ldr	r2, [r7, #72]	; 0x48
   41a50:	68fb      	ldr	r3, [r7, #12]
   41a52:	4053      	eors	r3, r2
   41a54:	2110      	movs	r1, #16
   41a56:	4618      	mov	r0, r3
   41a58:	f7ff f89c 	bl	40b94 <rotr32>
   41a5c:	4603      	mov	r3, r0
   41a5e:	64bb      	str	r3, [r7, #72]	; 0x48
   41a60:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   41a62:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   41a64:	4413      	add	r3, r2
   41a66:	637b      	str	r3, [r7, #52]	; 0x34
   41a68:	6a3a      	ldr	r2, [r7, #32]
   41a6a:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   41a6c:	4053      	eors	r3, r2
   41a6e:	210c      	movs	r1, #12
   41a70:	4618      	mov	r0, r3
   41a72:	f7ff f88f 	bl	40b94 <rotr32>
   41a76:	4603      	mov	r3, r0
   41a78:	623b      	str	r3, [r7, #32]
   41a7a:	68fa      	ldr	r2, [r7, #12]
   41a7c:	6a3b      	ldr	r3, [r7, #32]
   41a7e:	441a      	add	r2, r3
   41a80:	230e      	movs	r3, #14
   41a82:	009b      	lsls	r3, r3, #2
   41a84:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41a88:	440b      	add	r3, r1
   41a8a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41a8e:	4413      	add	r3, r2
   41a90:	60fb      	str	r3, [r7, #12]
   41a92:	6cba      	ldr	r2, [r7, #72]	; 0x48
   41a94:	68fb      	ldr	r3, [r7, #12]
   41a96:	4053      	eors	r3, r2
   41a98:	2108      	movs	r1, #8
   41a9a:	4618      	mov	r0, r3
   41a9c:	f7ff f87a 	bl	40b94 <rotr32>
   41aa0:	4603      	mov	r3, r0
   41aa2:	64bb      	str	r3, [r7, #72]	; 0x48
   41aa4:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   41aa6:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   41aa8:	4413      	add	r3, r2
   41aaa:	637b      	str	r3, [r7, #52]	; 0x34
   41aac:	6a3a      	ldr	r2, [r7, #32]
   41aae:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   41ab0:	4053      	eors	r3, r2
   41ab2:	2107      	movs	r1, #7
   41ab4:	4618      	mov	r0, r3
   41ab6:	f7ff f86d 	bl	40b94 <rotr32>
   41aba:	4603      	mov	r3, r0
   41abc:	623b      	str	r3, [r7, #32]
   41abe:	693a      	ldr	r2, [r7, #16]
   41ac0:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   41ac2:	441a      	add	r2, r3
   41ac4:	2303      	movs	r3, #3
   41ac6:	009b      	lsls	r3, r3, #2
   41ac8:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41acc:	440b      	add	r3, r1
   41ace:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41ad2:	4413      	add	r3, r2
   41ad4:	613b      	str	r3, [r7, #16]
   41ad6:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   41ad8:	693b      	ldr	r3, [r7, #16]
   41ada:	4053      	eors	r3, r2
   41adc:	2110      	movs	r1, #16
   41ade:	4618      	mov	r0, r3
   41ae0:	f7ff f858 	bl	40b94 <rotr32>
   41ae4:	4603      	mov	r3, r0
   41ae6:	63fb      	str	r3, [r7, #60]	; 0x3c
   41ae8:	6bba      	ldr	r2, [r7, #56]	; 0x38
   41aea:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   41aec:	4413      	add	r3, r2
   41aee:	63bb      	str	r3, [r7, #56]	; 0x38
   41af0:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   41af2:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   41af4:	4053      	eors	r3, r2
   41af6:	210c      	movs	r1, #12
   41af8:	4618      	mov	r0, r3
   41afa:	f7ff f84b 	bl	40b94 <rotr32>
   41afe:	4603      	mov	r3, r0
   41b00:	627b      	str	r3, [r7, #36]	; 0x24
   41b02:	693a      	ldr	r2, [r7, #16]
   41b04:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   41b06:	441a      	add	r2, r3
   41b08:	2306      	movs	r3, #6
   41b0a:	009b      	lsls	r3, r3, #2
   41b0c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41b10:	440b      	add	r3, r1
   41b12:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41b16:	4413      	add	r3, r2
   41b18:	613b      	str	r3, [r7, #16]
   41b1a:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   41b1c:	693b      	ldr	r3, [r7, #16]
   41b1e:	4053      	eors	r3, r2
   41b20:	2108      	movs	r1, #8
   41b22:	4618      	mov	r0, r3
   41b24:	f7ff f836 	bl	40b94 <rotr32>
   41b28:	4603      	mov	r3, r0
   41b2a:	63fb      	str	r3, [r7, #60]	; 0x3c
   41b2c:	6bba      	ldr	r2, [r7, #56]	; 0x38
   41b2e:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   41b30:	4413      	add	r3, r2
   41b32:	63bb      	str	r3, [r7, #56]	; 0x38
   41b34:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   41b36:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   41b38:	4053      	eors	r3, r2
   41b3a:	2107      	movs	r1, #7
   41b3c:	4618      	mov	r0, r3
   41b3e:	f7ff f829 	bl	40b94 <rotr32>
   41b42:	4603      	mov	r3, r0
   41b44:	627b      	str	r3, [r7, #36]	; 0x24
   41b46:	697a      	ldr	r2, [r7, #20]
   41b48:	6abb      	ldr	r3, [r7, #40]	; 0x28
   41b4a:	441a      	add	r2, r3
   41b4c:	2307      	movs	r3, #7
   41b4e:	009b      	lsls	r3, r3, #2
   41b50:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41b54:	440b      	add	r3, r1
   41b56:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41b5a:	4413      	add	r3, r2
   41b5c:	617b      	str	r3, [r7, #20]
   41b5e:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   41b60:	697b      	ldr	r3, [r7, #20]
   41b62:	4053      	eors	r3, r2
   41b64:	2110      	movs	r1, #16
   41b66:	4618      	mov	r0, r3
   41b68:	f7ff f814 	bl	40b94 <rotr32>
   41b6c:	4603      	mov	r3, r0
   41b6e:	643b      	str	r3, [r7, #64]	; 0x40
   41b70:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   41b72:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   41b74:	4413      	add	r3, r2
   41b76:	62fb      	str	r3, [r7, #44]	; 0x2c
   41b78:	6aba      	ldr	r2, [r7, #40]	; 0x28
   41b7a:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   41b7c:	4053      	eors	r3, r2
   41b7e:	210c      	movs	r1, #12
   41b80:	4618      	mov	r0, r3
   41b82:	f7ff f807 	bl	40b94 <rotr32>
   41b86:	4603      	mov	r3, r0
   41b88:	62bb      	str	r3, [r7, #40]	; 0x28
   41b8a:	697a      	ldr	r2, [r7, #20]
   41b8c:	6abb      	ldr	r3, [r7, #40]	; 0x28
   41b8e:	441a      	add	r2, r3
   41b90:	2301      	movs	r3, #1
   41b92:	009b      	lsls	r3, r3, #2
   41b94:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41b98:	440b      	add	r3, r1
   41b9a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41b9e:	4413      	add	r3, r2
   41ba0:	617b      	str	r3, [r7, #20]
   41ba2:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   41ba4:	697b      	ldr	r3, [r7, #20]
   41ba6:	4053      	eors	r3, r2
   41ba8:	2108      	movs	r1, #8
   41baa:	4618      	mov	r0, r3
   41bac:	f7fe fff2 	bl	40b94 <rotr32>
   41bb0:	4603      	mov	r3, r0
   41bb2:	643b      	str	r3, [r7, #64]	; 0x40
   41bb4:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   41bb6:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   41bb8:	4413      	add	r3, r2
   41bba:	62fb      	str	r3, [r7, #44]	; 0x2c
   41bbc:	6aba      	ldr	r2, [r7, #40]	; 0x28
   41bbe:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   41bc0:	4053      	eors	r3, r2
   41bc2:	2107      	movs	r1, #7
   41bc4:	4618      	mov	r0, r3
   41bc6:	f7fe ffe5 	bl	40b94 <rotr32>
   41bca:	4603      	mov	r3, r0
   41bcc:	62bb      	str	r3, [r7, #40]	; 0x28
   41bce:	69ba      	ldr	r2, [r7, #24]
   41bd0:	69fb      	ldr	r3, [r7, #28]
   41bd2:	441a      	add	r2, r3
   41bd4:	2309      	movs	r3, #9
   41bd6:	009b      	lsls	r3, r3, #2
   41bd8:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41bdc:	440b      	add	r3, r1
   41bde:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41be2:	4413      	add	r3, r2
   41be4:	61bb      	str	r3, [r7, #24]
   41be6:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   41be8:	69bb      	ldr	r3, [r7, #24]
   41bea:	4053      	eors	r3, r2
   41bec:	2110      	movs	r1, #16
   41bee:	4618      	mov	r0, r3
   41bf0:	f7fe ffd0 	bl	40b94 <rotr32>
   41bf4:	4603      	mov	r3, r0
   41bf6:	647b      	str	r3, [r7, #68]	; 0x44
   41bf8:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   41bfa:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   41bfc:	4413      	add	r3, r2
   41bfe:	633b      	str	r3, [r7, #48]	; 0x30
   41c00:	69fa      	ldr	r2, [r7, #28]
   41c02:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   41c04:	4053      	eors	r3, r2
   41c06:	210c      	movs	r1, #12
   41c08:	4618      	mov	r0, r3
   41c0a:	f7fe ffc3 	bl	40b94 <rotr32>
   41c0e:	4603      	mov	r3, r0
   41c10:	61fb      	str	r3, [r7, #28]
   41c12:	69ba      	ldr	r2, [r7, #24]
   41c14:	69fb      	ldr	r3, [r7, #28]
   41c16:	441a      	add	r2, r3
   41c18:	2304      	movs	r3, #4
   41c1a:	009b      	lsls	r3, r3, #2
   41c1c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41c20:	440b      	add	r3, r1
   41c22:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41c26:	4413      	add	r3, r2
   41c28:	61bb      	str	r3, [r7, #24]
   41c2a:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   41c2c:	69bb      	ldr	r3, [r7, #24]
   41c2e:	4053      	eors	r3, r2
   41c30:	2108      	movs	r1, #8
   41c32:	4618      	mov	r0, r3
   41c34:	f7fe ffae 	bl	40b94 <rotr32>
   41c38:	4603      	mov	r3, r0
   41c3a:	647b      	str	r3, [r7, #68]	; 0x44
   41c3c:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   41c3e:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   41c40:	4413      	add	r3, r2
   41c42:	633b      	str	r3, [r7, #48]	; 0x30
   41c44:	69fa      	ldr	r2, [r7, #28]
   41c46:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   41c48:	4053      	eors	r3, r2
   41c4a:	2107      	movs	r1, #7
   41c4c:	4618      	mov	r0, r3
   41c4e:	f7fe ffa1 	bl	40b94 <rotr32>
   41c52:	4603      	mov	r3, r0
   41c54:	61fb      	str	r3, [r7, #28]
   41c56:	68fa      	ldr	r2, [r7, #12]
   41c58:	69fb      	ldr	r3, [r7, #28]
   41c5a:	441a      	add	r2, r3
   41c5c:	2307      	movs	r3, #7
   41c5e:	009b      	lsls	r3, r3, #2
   41c60:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41c64:	440b      	add	r3, r1
   41c66:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41c6a:	4413      	add	r3, r2
   41c6c:	60fb      	str	r3, [r7, #12]
   41c6e:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   41c70:	68fb      	ldr	r3, [r7, #12]
   41c72:	4053      	eors	r3, r2
   41c74:	2110      	movs	r1, #16
   41c76:	4618      	mov	r0, r3
   41c78:	f7fe ff8c 	bl	40b94 <rotr32>
   41c7c:	4603      	mov	r3, r0
   41c7e:	63fb      	str	r3, [r7, #60]	; 0x3c
   41c80:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   41c82:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   41c84:	4413      	add	r3, r2
   41c86:	62fb      	str	r3, [r7, #44]	; 0x2c
   41c88:	69fa      	ldr	r2, [r7, #28]
   41c8a:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   41c8c:	4053      	eors	r3, r2
   41c8e:	210c      	movs	r1, #12
   41c90:	4618      	mov	r0, r3
   41c92:	f7fe ff7f 	bl	40b94 <rotr32>
   41c96:	4603      	mov	r3, r0
   41c98:	61fb      	str	r3, [r7, #28]
   41c9a:	68fa      	ldr	r2, [r7, #12]
   41c9c:	69fb      	ldr	r3, [r7, #28]
   41c9e:	441a      	add	r2, r3
   41ca0:	2309      	movs	r3, #9
   41ca2:	009b      	lsls	r3, r3, #2
   41ca4:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41ca8:	440b      	add	r3, r1
   41caa:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41cae:	4413      	add	r3, r2
   41cb0:	60fb      	str	r3, [r7, #12]
   41cb2:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   41cb4:	68fb      	ldr	r3, [r7, #12]
   41cb6:	4053      	eors	r3, r2
   41cb8:	2108      	movs	r1, #8
   41cba:	4618      	mov	r0, r3
   41cbc:	f7fe ff6a 	bl	40b94 <rotr32>
   41cc0:	4603      	mov	r3, r0
   41cc2:	63fb      	str	r3, [r7, #60]	; 0x3c
   41cc4:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   41cc6:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   41cc8:	4413      	add	r3, r2
   41cca:	62fb      	str	r3, [r7, #44]	; 0x2c
   41ccc:	69fa      	ldr	r2, [r7, #28]
   41cce:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   41cd0:	4053      	eors	r3, r2
   41cd2:	2107      	movs	r1, #7
   41cd4:	4618      	mov	r0, r3
   41cd6:	f7fe ff5d 	bl	40b94 <rotr32>
   41cda:	4603      	mov	r3, r0
   41cdc:	61fb      	str	r3, [r7, #28]
   41cde:	693a      	ldr	r2, [r7, #16]
   41ce0:	6a3b      	ldr	r3, [r7, #32]
   41ce2:	441a      	add	r2, r3
   41ce4:	2303      	movs	r3, #3
   41ce6:	009b      	lsls	r3, r3, #2
   41ce8:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41cec:	440b      	add	r3, r1
   41cee:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41cf2:	4413      	add	r3, r2
   41cf4:	613b      	str	r3, [r7, #16]
   41cf6:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   41cf8:	693b      	ldr	r3, [r7, #16]
   41cfa:	4053      	eors	r3, r2
   41cfc:	2110      	movs	r1, #16
   41cfe:	4618      	mov	r0, r3
   41d00:	f7fe ff48 	bl	40b94 <rotr32>
   41d04:	4603      	mov	r3, r0
   41d06:	643b      	str	r3, [r7, #64]	; 0x40
   41d08:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   41d0a:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   41d0c:	4413      	add	r3, r2
   41d0e:	633b      	str	r3, [r7, #48]	; 0x30
   41d10:	6a3a      	ldr	r2, [r7, #32]
   41d12:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   41d14:	4053      	eors	r3, r2
   41d16:	210c      	movs	r1, #12
   41d18:	4618      	mov	r0, r3
   41d1a:	f7fe ff3b 	bl	40b94 <rotr32>
   41d1e:	4603      	mov	r3, r0
   41d20:	623b      	str	r3, [r7, #32]
   41d22:	693a      	ldr	r2, [r7, #16]
   41d24:	6a3b      	ldr	r3, [r7, #32]
   41d26:	441a      	add	r2, r3
   41d28:	2301      	movs	r3, #1
   41d2a:	009b      	lsls	r3, r3, #2
   41d2c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41d30:	440b      	add	r3, r1
   41d32:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41d36:	4413      	add	r3, r2
   41d38:	613b      	str	r3, [r7, #16]
   41d3a:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   41d3c:	693b      	ldr	r3, [r7, #16]
   41d3e:	4053      	eors	r3, r2
   41d40:	2108      	movs	r1, #8
   41d42:	4618      	mov	r0, r3
   41d44:	f7fe ff26 	bl	40b94 <rotr32>
   41d48:	4603      	mov	r3, r0
   41d4a:	643b      	str	r3, [r7, #64]	; 0x40
   41d4c:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   41d4e:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   41d50:	4413      	add	r3, r2
   41d52:	633b      	str	r3, [r7, #48]	; 0x30
   41d54:	6a3a      	ldr	r2, [r7, #32]
   41d56:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   41d58:	4053      	eors	r3, r2
   41d5a:	2107      	movs	r1, #7
   41d5c:	4618      	mov	r0, r3
   41d5e:	f7fe ff19 	bl	40b94 <rotr32>
   41d62:	4603      	mov	r3, r0
   41d64:	623b      	str	r3, [r7, #32]
   41d66:	697a      	ldr	r2, [r7, #20]
   41d68:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   41d6a:	441a      	add	r2, r3
   41d6c:	230d      	movs	r3, #13
   41d6e:	009b      	lsls	r3, r3, #2
   41d70:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41d74:	440b      	add	r3, r1
   41d76:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41d7a:	4413      	add	r3, r2
   41d7c:	617b      	str	r3, [r7, #20]
   41d7e:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   41d80:	697b      	ldr	r3, [r7, #20]
   41d82:	4053      	eors	r3, r2
   41d84:	2110      	movs	r1, #16
   41d86:	4618      	mov	r0, r3
   41d88:	f7fe ff04 	bl	40b94 <rotr32>
   41d8c:	4603      	mov	r3, r0
   41d8e:	647b      	str	r3, [r7, #68]	; 0x44
   41d90:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   41d92:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   41d94:	4413      	add	r3, r2
   41d96:	637b      	str	r3, [r7, #52]	; 0x34
   41d98:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   41d9a:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   41d9c:	4053      	eors	r3, r2
   41d9e:	210c      	movs	r1, #12
   41da0:	4618      	mov	r0, r3
   41da2:	f7fe fef7 	bl	40b94 <rotr32>
   41da6:	4603      	mov	r3, r0
   41da8:	627b      	str	r3, [r7, #36]	; 0x24
   41daa:	697a      	ldr	r2, [r7, #20]
   41dac:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   41dae:	441a      	add	r2, r3
   41db0:	230c      	movs	r3, #12
   41db2:	009b      	lsls	r3, r3, #2
   41db4:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41db8:	440b      	add	r3, r1
   41dba:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41dbe:	4413      	add	r3, r2
   41dc0:	617b      	str	r3, [r7, #20]
   41dc2:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   41dc4:	697b      	ldr	r3, [r7, #20]
   41dc6:	4053      	eors	r3, r2
   41dc8:	2108      	movs	r1, #8
   41dca:	4618      	mov	r0, r3
   41dcc:	f7fe fee2 	bl	40b94 <rotr32>
   41dd0:	4603      	mov	r3, r0
   41dd2:	647b      	str	r3, [r7, #68]	; 0x44
   41dd4:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   41dd6:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   41dd8:	4413      	add	r3, r2
   41dda:	637b      	str	r3, [r7, #52]	; 0x34
   41ddc:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   41dde:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   41de0:	4053      	eors	r3, r2
   41de2:	2107      	movs	r1, #7
   41de4:	4618      	mov	r0, r3
   41de6:	f7fe fed5 	bl	40b94 <rotr32>
   41dea:	4603      	mov	r3, r0
   41dec:	627b      	str	r3, [r7, #36]	; 0x24
   41dee:	69ba      	ldr	r2, [r7, #24]
   41df0:	6abb      	ldr	r3, [r7, #40]	; 0x28
   41df2:	441a      	add	r2, r3
   41df4:	230b      	movs	r3, #11
   41df6:	009b      	lsls	r3, r3, #2
   41df8:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41dfc:	440b      	add	r3, r1
   41dfe:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41e02:	4413      	add	r3, r2
   41e04:	61bb      	str	r3, [r7, #24]
   41e06:	6cba      	ldr	r2, [r7, #72]	; 0x48
   41e08:	69bb      	ldr	r3, [r7, #24]
   41e0a:	4053      	eors	r3, r2
   41e0c:	2110      	movs	r1, #16
   41e0e:	4618      	mov	r0, r3
   41e10:	f7fe fec0 	bl	40b94 <rotr32>
   41e14:	4603      	mov	r3, r0
   41e16:	64bb      	str	r3, [r7, #72]	; 0x48
   41e18:	6bba      	ldr	r2, [r7, #56]	; 0x38
   41e1a:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   41e1c:	4413      	add	r3, r2
   41e1e:	63bb      	str	r3, [r7, #56]	; 0x38
   41e20:	6aba      	ldr	r2, [r7, #40]	; 0x28
   41e22:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   41e24:	4053      	eors	r3, r2
   41e26:	210c      	movs	r1, #12
   41e28:	4618      	mov	r0, r3
   41e2a:	f7fe feb3 	bl	40b94 <rotr32>
   41e2e:	4603      	mov	r3, r0
   41e30:	62bb      	str	r3, [r7, #40]	; 0x28
   41e32:	69ba      	ldr	r2, [r7, #24]
   41e34:	6abb      	ldr	r3, [r7, #40]	; 0x28
   41e36:	441a      	add	r2, r3
   41e38:	230e      	movs	r3, #14
   41e3a:	009b      	lsls	r3, r3, #2
   41e3c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41e40:	440b      	add	r3, r1
   41e42:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41e46:	4413      	add	r3, r2
   41e48:	61bb      	str	r3, [r7, #24]
   41e4a:	6cba      	ldr	r2, [r7, #72]	; 0x48
   41e4c:	69bb      	ldr	r3, [r7, #24]
   41e4e:	4053      	eors	r3, r2
   41e50:	2108      	movs	r1, #8
   41e52:	4618      	mov	r0, r3
   41e54:	f7fe fe9e 	bl	40b94 <rotr32>
   41e58:	4603      	mov	r3, r0
   41e5a:	64bb      	str	r3, [r7, #72]	; 0x48
   41e5c:	6bba      	ldr	r2, [r7, #56]	; 0x38
   41e5e:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   41e60:	4413      	add	r3, r2
   41e62:	63bb      	str	r3, [r7, #56]	; 0x38
   41e64:	6aba      	ldr	r2, [r7, #40]	; 0x28
   41e66:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   41e68:	4053      	eors	r3, r2
   41e6a:	2107      	movs	r1, #7
   41e6c:	4618      	mov	r0, r3
   41e6e:	f7fe fe91 	bl	40b94 <rotr32>
   41e72:	4603      	mov	r3, r0
   41e74:	62bb      	str	r3, [r7, #40]	; 0x28
   41e76:	68fa      	ldr	r2, [r7, #12]
   41e78:	6a3b      	ldr	r3, [r7, #32]
   41e7a:	441a      	add	r2, r3
   41e7c:	2302      	movs	r3, #2
   41e7e:	009b      	lsls	r3, r3, #2
   41e80:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41e84:	440b      	add	r3, r1
   41e86:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41e8a:	4413      	add	r3, r2
   41e8c:	60fb      	str	r3, [r7, #12]
   41e8e:	6cba      	ldr	r2, [r7, #72]	; 0x48
   41e90:	68fb      	ldr	r3, [r7, #12]
   41e92:	4053      	eors	r3, r2
   41e94:	2110      	movs	r1, #16
   41e96:	4618      	mov	r0, r3
   41e98:	f7fe fe7c 	bl	40b94 <rotr32>
   41e9c:	4603      	mov	r3, r0
   41e9e:	64bb      	str	r3, [r7, #72]	; 0x48
   41ea0:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   41ea2:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   41ea4:	4413      	add	r3, r2
   41ea6:	637b      	str	r3, [r7, #52]	; 0x34
   41ea8:	6a3a      	ldr	r2, [r7, #32]
   41eaa:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   41eac:	4053      	eors	r3, r2
   41eae:	210c      	movs	r1, #12
   41eb0:	4618      	mov	r0, r3
   41eb2:	f7fe fe6f 	bl	40b94 <rotr32>
   41eb6:	4603      	mov	r3, r0
   41eb8:	623b      	str	r3, [r7, #32]
   41eba:	68fa      	ldr	r2, [r7, #12]
   41ebc:	6a3b      	ldr	r3, [r7, #32]
   41ebe:	441a      	add	r2, r3
   41ec0:	2306      	movs	r3, #6
   41ec2:	009b      	lsls	r3, r3, #2
   41ec4:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41ec8:	440b      	add	r3, r1
   41eca:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41ece:	4413      	add	r3, r2
   41ed0:	60fb      	str	r3, [r7, #12]
   41ed2:	6cba      	ldr	r2, [r7, #72]	; 0x48
   41ed4:	68fb      	ldr	r3, [r7, #12]
   41ed6:	4053      	eors	r3, r2
   41ed8:	2108      	movs	r1, #8
   41eda:	4618      	mov	r0, r3
   41edc:	f7fe fe5a 	bl	40b94 <rotr32>
   41ee0:	4603      	mov	r3, r0
   41ee2:	64bb      	str	r3, [r7, #72]	; 0x48
   41ee4:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   41ee6:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   41ee8:	4413      	add	r3, r2
   41eea:	637b      	str	r3, [r7, #52]	; 0x34
   41eec:	6a3a      	ldr	r2, [r7, #32]
   41eee:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   41ef0:	4053      	eors	r3, r2
   41ef2:	2107      	movs	r1, #7
   41ef4:	4618      	mov	r0, r3
   41ef6:	f7fe fe4d 	bl	40b94 <rotr32>
   41efa:	4603      	mov	r3, r0
   41efc:	623b      	str	r3, [r7, #32]
   41efe:	693a      	ldr	r2, [r7, #16]
   41f00:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   41f02:	441a      	add	r2, r3
   41f04:	2305      	movs	r3, #5
   41f06:	009b      	lsls	r3, r3, #2
   41f08:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41f0c:	440b      	add	r3, r1
   41f0e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41f12:	4413      	add	r3, r2
   41f14:	613b      	str	r3, [r7, #16]
   41f16:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   41f18:	693b      	ldr	r3, [r7, #16]
   41f1a:	4053      	eors	r3, r2
   41f1c:	2110      	movs	r1, #16
   41f1e:	4618      	mov	r0, r3
   41f20:	f7fe fe38 	bl	40b94 <rotr32>
   41f24:	4603      	mov	r3, r0
   41f26:	63fb      	str	r3, [r7, #60]	; 0x3c
   41f28:	6bba      	ldr	r2, [r7, #56]	; 0x38
   41f2a:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   41f2c:	4413      	add	r3, r2
   41f2e:	63bb      	str	r3, [r7, #56]	; 0x38
   41f30:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   41f32:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   41f34:	4053      	eors	r3, r2
   41f36:	210c      	movs	r1, #12
   41f38:	4618      	mov	r0, r3
   41f3a:	f7fe fe2b 	bl	40b94 <rotr32>
   41f3e:	4603      	mov	r3, r0
   41f40:	627b      	str	r3, [r7, #36]	; 0x24
   41f42:	693a      	ldr	r2, [r7, #16]
   41f44:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   41f46:	441a      	add	r2, r3
   41f48:	230a      	movs	r3, #10
   41f4a:	009b      	lsls	r3, r3, #2
   41f4c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41f50:	440b      	add	r3, r1
   41f52:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41f56:	4413      	add	r3, r2
   41f58:	613b      	str	r3, [r7, #16]
   41f5a:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   41f5c:	693b      	ldr	r3, [r7, #16]
   41f5e:	4053      	eors	r3, r2
   41f60:	2108      	movs	r1, #8
   41f62:	4618      	mov	r0, r3
   41f64:	f7fe fe16 	bl	40b94 <rotr32>
   41f68:	4603      	mov	r3, r0
   41f6a:	63fb      	str	r3, [r7, #60]	; 0x3c
   41f6c:	6bba      	ldr	r2, [r7, #56]	; 0x38
   41f6e:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   41f70:	4413      	add	r3, r2
   41f72:	63bb      	str	r3, [r7, #56]	; 0x38
   41f74:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   41f76:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   41f78:	4053      	eors	r3, r2
   41f7a:	2107      	movs	r1, #7
   41f7c:	4618      	mov	r0, r3
   41f7e:	f7fe fe09 	bl	40b94 <rotr32>
   41f82:	4603      	mov	r3, r0
   41f84:	627b      	str	r3, [r7, #36]	; 0x24
   41f86:	697a      	ldr	r2, [r7, #20]
   41f88:	6abb      	ldr	r3, [r7, #40]	; 0x28
   41f8a:	441a      	add	r2, r3
   41f8c:	2304      	movs	r3, #4
   41f8e:	009b      	lsls	r3, r3, #2
   41f90:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41f94:	440b      	add	r3, r1
   41f96:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41f9a:	4413      	add	r3, r2
   41f9c:	617b      	str	r3, [r7, #20]
   41f9e:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   41fa0:	697b      	ldr	r3, [r7, #20]
   41fa2:	4053      	eors	r3, r2
   41fa4:	2110      	movs	r1, #16
   41fa6:	4618      	mov	r0, r3
   41fa8:	f7fe fdf4 	bl	40b94 <rotr32>
   41fac:	4603      	mov	r3, r0
   41fae:	643b      	str	r3, [r7, #64]	; 0x40
   41fb0:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   41fb2:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   41fb4:	4413      	add	r3, r2
   41fb6:	62fb      	str	r3, [r7, #44]	; 0x2c
   41fb8:	6aba      	ldr	r2, [r7, #40]	; 0x28
   41fba:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   41fbc:	4053      	eors	r3, r2
   41fbe:	210c      	movs	r1, #12
   41fc0:	4618      	mov	r0, r3
   41fc2:	f7fe fde7 	bl	40b94 <rotr32>
   41fc6:	4603      	mov	r3, r0
   41fc8:	62bb      	str	r3, [r7, #40]	; 0x28
   41fca:	697a      	ldr	r2, [r7, #20]
   41fcc:	6abb      	ldr	r3, [r7, #40]	; 0x28
   41fce:	441a      	add	r2, r3
   41fd0:	2300      	movs	r3, #0
   41fd2:	009b      	lsls	r3, r3, #2
   41fd4:	f107 0190 	add.w	r1, r7, #144	; 0x90
   41fd8:	440b      	add	r3, r1
   41fda:	f853 3c44 	ldr.w	r3, [r3, #-68]
   41fde:	4413      	add	r3, r2
   41fe0:	617b      	str	r3, [r7, #20]
   41fe2:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   41fe4:	697b      	ldr	r3, [r7, #20]
   41fe6:	4053      	eors	r3, r2
   41fe8:	2108      	movs	r1, #8
   41fea:	4618      	mov	r0, r3
   41fec:	f7fe fdd2 	bl	40b94 <rotr32>
   41ff0:	4603      	mov	r3, r0
   41ff2:	643b      	str	r3, [r7, #64]	; 0x40
   41ff4:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   41ff6:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   41ff8:	4413      	add	r3, r2
   41ffa:	62fb      	str	r3, [r7, #44]	; 0x2c
   41ffc:	6aba      	ldr	r2, [r7, #40]	; 0x28
   41ffe:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   42000:	4053      	eors	r3, r2
   42002:	2107      	movs	r1, #7
   42004:	4618      	mov	r0, r3
   42006:	f7fe fdc5 	bl	40b94 <rotr32>
   4200a:	4603      	mov	r3, r0
   4200c:	62bb      	str	r3, [r7, #40]	; 0x28
   4200e:	69ba      	ldr	r2, [r7, #24]
   42010:	69fb      	ldr	r3, [r7, #28]
   42012:	441a      	add	r2, r3
   42014:	230f      	movs	r3, #15
   42016:	009b      	lsls	r3, r3, #2
   42018:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4201c:	440b      	add	r3, r1
   4201e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42022:	4413      	add	r3, r2
   42024:	61bb      	str	r3, [r7, #24]
   42026:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   42028:	69bb      	ldr	r3, [r7, #24]
   4202a:	4053      	eors	r3, r2
   4202c:	2110      	movs	r1, #16
   4202e:	4618      	mov	r0, r3
   42030:	f7fe fdb0 	bl	40b94 <rotr32>
   42034:	4603      	mov	r3, r0
   42036:	647b      	str	r3, [r7, #68]	; 0x44
   42038:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   4203a:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   4203c:	4413      	add	r3, r2
   4203e:	633b      	str	r3, [r7, #48]	; 0x30
   42040:	69fa      	ldr	r2, [r7, #28]
   42042:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   42044:	4053      	eors	r3, r2
   42046:	210c      	movs	r1, #12
   42048:	4618      	mov	r0, r3
   4204a:	f7fe fda3 	bl	40b94 <rotr32>
   4204e:	4603      	mov	r3, r0
   42050:	61fb      	str	r3, [r7, #28]
   42052:	69ba      	ldr	r2, [r7, #24]
   42054:	69fb      	ldr	r3, [r7, #28]
   42056:	441a      	add	r2, r3
   42058:	2308      	movs	r3, #8
   4205a:	009b      	lsls	r3, r3, #2
   4205c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42060:	440b      	add	r3, r1
   42062:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42066:	4413      	add	r3, r2
   42068:	61bb      	str	r3, [r7, #24]
   4206a:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   4206c:	69bb      	ldr	r3, [r7, #24]
   4206e:	4053      	eors	r3, r2
   42070:	2108      	movs	r1, #8
   42072:	4618      	mov	r0, r3
   42074:	f7fe fd8e 	bl	40b94 <rotr32>
   42078:	4603      	mov	r3, r0
   4207a:	647b      	str	r3, [r7, #68]	; 0x44
   4207c:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   4207e:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   42080:	4413      	add	r3, r2
   42082:	633b      	str	r3, [r7, #48]	; 0x30
   42084:	69fa      	ldr	r2, [r7, #28]
   42086:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   42088:	4053      	eors	r3, r2
   4208a:	2107      	movs	r1, #7
   4208c:	4618      	mov	r0, r3
   4208e:	f7fe fd81 	bl	40b94 <rotr32>
   42092:	4603      	mov	r3, r0
   42094:	61fb      	str	r3, [r7, #28]
   42096:	68fa      	ldr	r2, [r7, #12]
   42098:	69fb      	ldr	r3, [r7, #28]
   4209a:	441a      	add	r2, r3
   4209c:	2309      	movs	r3, #9
   4209e:	009b      	lsls	r3, r3, #2
   420a0:	f107 0190 	add.w	r1, r7, #144	; 0x90
   420a4:	440b      	add	r3, r1
   420a6:	f853 3c44 	ldr.w	r3, [r3, #-68]
   420aa:	4413      	add	r3, r2
   420ac:	60fb      	str	r3, [r7, #12]
   420ae:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   420b0:	68fb      	ldr	r3, [r7, #12]
   420b2:	4053      	eors	r3, r2
   420b4:	2110      	movs	r1, #16
   420b6:	4618      	mov	r0, r3
   420b8:	f7fe fd6c 	bl	40b94 <rotr32>
   420bc:	4603      	mov	r3, r0
   420be:	63fb      	str	r3, [r7, #60]	; 0x3c
   420c0:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   420c2:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   420c4:	4413      	add	r3, r2
   420c6:	62fb      	str	r3, [r7, #44]	; 0x2c
   420c8:	69fa      	ldr	r2, [r7, #28]
   420ca:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   420cc:	4053      	eors	r3, r2
   420ce:	210c      	movs	r1, #12
   420d0:	4618      	mov	r0, r3
   420d2:	f7fe fd5f 	bl	40b94 <rotr32>
   420d6:	4603      	mov	r3, r0
   420d8:	61fb      	str	r3, [r7, #28]
   420da:	68fa      	ldr	r2, [r7, #12]
   420dc:	69fb      	ldr	r3, [r7, #28]
   420de:	441a      	add	r2, r3
   420e0:	2300      	movs	r3, #0
   420e2:	009b      	lsls	r3, r3, #2
   420e4:	f107 0190 	add.w	r1, r7, #144	; 0x90
   420e8:	440b      	add	r3, r1
   420ea:	f853 3c44 	ldr.w	r3, [r3, #-68]
   420ee:	4413      	add	r3, r2
   420f0:	60fb      	str	r3, [r7, #12]
   420f2:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   420f4:	68fb      	ldr	r3, [r7, #12]
   420f6:	4053      	eors	r3, r2
   420f8:	2108      	movs	r1, #8
   420fa:	4618      	mov	r0, r3
   420fc:	f7fe fd4a 	bl	40b94 <rotr32>
   42100:	4603      	mov	r3, r0
   42102:	63fb      	str	r3, [r7, #60]	; 0x3c
   42104:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   42106:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   42108:	4413      	add	r3, r2
   4210a:	62fb      	str	r3, [r7, #44]	; 0x2c
   4210c:	69fa      	ldr	r2, [r7, #28]
   4210e:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   42110:	4053      	eors	r3, r2
   42112:	2107      	movs	r1, #7
   42114:	4618      	mov	r0, r3
   42116:	f7fe fd3d 	bl	40b94 <rotr32>
   4211a:	4603      	mov	r3, r0
   4211c:	61fb      	str	r3, [r7, #28]
   4211e:	693a      	ldr	r2, [r7, #16]
   42120:	6a3b      	ldr	r3, [r7, #32]
   42122:	441a      	add	r2, r3
   42124:	2305      	movs	r3, #5
   42126:	009b      	lsls	r3, r3, #2
   42128:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4212c:	440b      	add	r3, r1
   4212e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42132:	4413      	add	r3, r2
   42134:	613b      	str	r3, [r7, #16]
   42136:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   42138:	693b      	ldr	r3, [r7, #16]
   4213a:	4053      	eors	r3, r2
   4213c:	2110      	movs	r1, #16
   4213e:	4618      	mov	r0, r3
   42140:	f7fe fd28 	bl	40b94 <rotr32>
   42144:	4603      	mov	r3, r0
   42146:	643b      	str	r3, [r7, #64]	; 0x40
   42148:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   4214a:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   4214c:	4413      	add	r3, r2
   4214e:	633b      	str	r3, [r7, #48]	; 0x30
   42150:	6a3a      	ldr	r2, [r7, #32]
   42152:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   42154:	4053      	eors	r3, r2
   42156:	210c      	movs	r1, #12
   42158:	4618      	mov	r0, r3
   4215a:	f7fe fd1b 	bl	40b94 <rotr32>
   4215e:	4603      	mov	r3, r0
   42160:	623b      	str	r3, [r7, #32]
   42162:	693a      	ldr	r2, [r7, #16]
   42164:	6a3b      	ldr	r3, [r7, #32]
   42166:	441a      	add	r2, r3
   42168:	2307      	movs	r3, #7
   4216a:	009b      	lsls	r3, r3, #2
   4216c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42170:	440b      	add	r3, r1
   42172:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42176:	4413      	add	r3, r2
   42178:	613b      	str	r3, [r7, #16]
   4217a:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   4217c:	693b      	ldr	r3, [r7, #16]
   4217e:	4053      	eors	r3, r2
   42180:	2108      	movs	r1, #8
   42182:	4618      	mov	r0, r3
   42184:	f7fe fd06 	bl	40b94 <rotr32>
   42188:	4603      	mov	r3, r0
   4218a:	643b      	str	r3, [r7, #64]	; 0x40
   4218c:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   4218e:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   42190:	4413      	add	r3, r2
   42192:	633b      	str	r3, [r7, #48]	; 0x30
   42194:	6a3a      	ldr	r2, [r7, #32]
   42196:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   42198:	4053      	eors	r3, r2
   4219a:	2107      	movs	r1, #7
   4219c:	4618      	mov	r0, r3
   4219e:	f7fe fcf9 	bl	40b94 <rotr32>
   421a2:	4603      	mov	r3, r0
   421a4:	623b      	str	r3, [r7, #32]
   421a6:	697a      	ldr	r2, [r7, #20]
   421a8:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   421aa:	441a      	add	r2, r3
   421ac:	2302      	movs	r3, #2
   421ae:	009b      	lsls	r3, r3, #2
   421b0:	f107 0190 	add.w	r1, r7, #144	; 0x90
   421b4:	440b      	add	r3, r1
   421b6:	f853 3c44 	ldr.w	r3, [r3, #-68]
   421ba:	4413      	add	r3, r2
   421bc:	617b      	str	r3, [r7, #20]
   421be:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   421c0:	697b      	ldr	r3, [r7, #20]
   421c2:	4053      	eors	r3, r2
   421c4:	2110      	movs	r1, #16
   421c6:	4618      	mov	r0, r3
   421c8:	f7fe fce4 	bl	40b94 <rotr32>
   421cc:	4603      	mov	r3, r0
   421ce:	647b      	str	r3, [r7, #68]	; 0x44
   421d0:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   421d2:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   421d4:	4413      	add	r3, r2
   421d6:	637b      	str	r3, [r7, #52]	; 0x34
   421d8:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   421da:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   421dc:	4053      	eors	r3, r2
   421de:	210c      	movs	r1, #12
   421e0:	4618      	mov	r0, r3
   421e2:	f7fe fcd7 	bl	40b94 <rotr32>
   421e6:	4603      	mov	r3, r0
   421e8:	627b      	str	r3, [r7, #36]	; 0x24
   421ea:	697a      	ldr	r2, [r7, #20]
   421ec:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   421ee:	441a      	add	r2, r3
   421f0:	2304      	movs	r3, #4
   421f2:	009b      	lsls	r3, r3, #2
   421f4:	f107 0190 	add.w	r1, r7, #144	; 0x90
   421f8:	440b      	add	r3, r1
   421fa:	f853 3c44 	ldr.w	r3, [r3, #-68]
   421fe:	4413      	add	r3, r2
   42200:	617b      	str	r3, [r7, #20]
   42202:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   42204:	697b      	ldr	r3, [r7, #20]
   42206:	4053      	eors	r3, r2
   42208:	2108      	movs	r1, #8
   4220a:	4618      	mov	r0, r3
   4220c:	f7fe fcc2 	bl	40b94 <rotr32>
   42210:	4603      	mov	r3, r0
   42212:	647b      	str	r3, [r7, #68]	; 0x44
   42214:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   42216:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   42218:	4413      	add	r3, r2
   4221a:	637b      	str	r3, [r7, #52]	; 0x34
   4221c:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   4221e:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   42220:	4053      	eors	r3, r2
   42222:	2107      	movs	r1, #7
   42224:	4618      	mov	r0, r3
   42226:	f7fe fcb5 	bl	40b94 <rotr32>
   4222a:	4603      	mov	r3, r0
   4222c:	627b      	str	r3, [r7, #36]	; 0x24
   4222e:	69ba      	ldr	r2, [r7, #24]
   42230:	6abb      	ldr	r3, [r7, #40]	; 0x28
   42232:	441a      	add	r2, r3
   42234:	230a      	movs	r3, #10
   42236:	009b      	lsls	r3, r3, #2
   42238:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4223c:	440b      	add	r3, r1
   4223e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42242:	4413      	add	r3, r2
   42244:	61bb      	str	r3, [r7, #24]
   42246:	6cba      	ldr	r2, [r7, #72]	; 0x48
   42248:	69bb      	ldr	r3, [r7, #24]
   4224a:	4053      	eors	r3, r2
   4224c:	2110      	movs	r1, #16
   4224e:	4618      	mov	r0, r3
   42250:	f7fe fca0 	bl	40b94 <rotr32>
   42254:	4603      	mov	r3, r0
   42256:	64bb      	str	r3, [r7, #72]	; 0x48
   42258:	6bba      	ldr	r2, [r7, #56]	; 0x38
   4225a:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   4225c:	4413      	add	r3, r2
   4225e:	63bb      	str	r3, [r7, #56]	; 0x38
   42260:	6aba      	ldr	r2, [r7, #40]	; 0x28
   42262:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   42264:	4053      	eors	r3, r2
   42266:	210c      	movs	r1, #12
   42268:	4618      	mov	r0, r3
   4226a:	f7fe fc93 	bl	40b94 <rotr32>
   4226e:	4603      	mov	r3, r0
   42270:	62bb      	str	r3, [r7, #40]	; 0x28
   42272:	69ba      	ldr	r2, [r7, #24]
   42274:	6abb      	ldr	r3, [r7, #40]	; 0x28
   42276:	441a      	add	r2, r3
   42278:	230f      	movs	r3, #15
   4227a:	009b      	lsls	r3, r3, #2
   4227c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42280:	440b      	add	r3, r1
   42282:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42286:	4413      	add	r3, r2
   42288:	61bb      	str	r3, [r7, #24]
   4228a:	6cba      	ldr	r2, [r7, #72]	; 0x48
   4228c:	69bb      	ldr	r3, [r7, #24]
   4228e:	4053      	eors	r3, r2
   42290:	2108      	movs	r1, #8
   42292:	4618      	mov	r0, r3
   42294:	f7fe fc7e 	bl	40b94 <rotr32>
   42298:	4603      	mov	r3, r0
   4229a:	64bb      	str	r3, [r7, #72]	; 0x48
   4229c:	6bba      	ldr	r2, [r7, #56]	; 0x38
   4229e:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   422a0:	4413      	add	r3, r2
   422a2:	63bb      	str	r3, [r7, #56]	; 0x38
   422a4:	6aba      	ldr	r2, [r7, #40]	; 0x28
   422a6:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   422a8:	4053      	eors	r3, r2
   422aa:	2107      	movs	r1, #7
   422ac:	4618      	mov	r0, r3
   422ae:	f7fe fc71 	bl	40b94 <rotr32>
   422b2:	4603      	mov	r3, r0
   422b4:	62bb      	str	r3, [r7, #40]	; 0x28
   422b6:	68fa      	ldr	r2, [r7, #12]
   422b8:	6a3b      	ldr	r3, [r7, #32]
   422ba:	441a      	add	r2, r3
   422bc:	230e      	movs	r3, #14
   422be:	009b      	lsls	r3, r3, #2
   422c0:	f107 0190 	add.w	r1, r7, #144	; 0x90
   422c4:	440b      	add	r3, r1
   422c6:	f853 3c44 	ldr.w	r3, [r3, #-68]
   422ca:	4413      	add	r3, r2
   422cc:	60fb      	str	r3, [r7, #12]
   422ce:	6cba      	ldr	r2, [r7, #72]	; 0x48
   422d0:	68fb      	ldr	r3, [r7, #12]
   422d2:	4053      	eors	r3, r2
   422d4:	2110      	movs	r1, #16
   422d6:	4618      	mov	r0, r3
   422d8:	f7fe fc5c 	bl	40b94 <rotr32>
   422dc:	4603      	mov	r3, r0
   422de:	64bb      	str	r3, [r7, #72]	; 0x48
   422e0:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   422e2:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   422e4:	4413      	add	r3, r2
   422e6:	637b      	str	r3, [r7, #52]	; 0x34
   422e8:	6a3a      	ldr	r2, [r7, #32]
   422ea:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   422ec:	4053      	eors	r3, r2
   422ee:	210c      	movs	r1, #12
   422f0:	4618      	mov	r0, r3
   422f2:	f7fe fc4f 	bl	40b94 <rotr32>
   422f6:	4603      	mov	r3, r0
   422f8:	623b      	str	r3, [r7, #32]
   422fa:	68fa      	ldr	r2, [r7, #12]
   422fc:	6a3b      	ldr	r3, [r7, #32]
   422fe:	441a      	add	r2, r3
   42300:	2301      	movs	r3, #1
   42302:	009b      	lsls	r3, r3, #2
   42304:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42308:	440b      	add	r3, r1
   4230a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4230e:	4413      	add	r3, r2
   42310:	60fb      	str	r3, [r7, #12]
   42312:	6cba      	ldr	r2, [r7, #72]	; 0x48
   42314:	68fb      	ldr	r3, [r7, #12]
   42316:	4053      	eors	r3, r2
   42318:	2108      	movs	r1, #8
   4231a:	4618      	mov	r0, r3
   4231c:	f7fe fc3a 	bl	40b94 <rotr32>
   42320:	4603      	mov	r3, r0
   42322:	64bb      	str	r3, [r7, #72]	; 0x48
   42324:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   42326:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   42328:	4413      	add	r3, r2
   4232a:	637b      	str	r3, [r7, #52]	; 0x34
   4232c:	6a3a      	ldr	r2, [r7, #32]
   4232e:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   42330:	4053      	eors	r3, r2
   42332:	2107      	movs	r1, #7
   42334:	4618      	mov	r0, r3
   42336:	f7fe fc2d 	bl	40b94 <rotr32>
   4233a:	4603      	mov	r3, r0
   4233c:	623b      	str	r3, [r7, #32]
   4233e:	693a      	ldr	r2, [r7, #16]
   42340:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   42342:	441a      	add	r2, r3
   42344:	230b      	movs	r3, #11
   42346:	009b      	lsls	r3, r3, #2
   42348:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4234c:	440b      	add	r3, r1
   4234e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42352:	4413      	add	r3, r2
   42354:	613b      	str	r3, [r7, #16]
   42356:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   42358:	693b      	ldr	r3, [r7, #16]
   4235a:	4053      	eors	r3, r2
   4235c:	2110      	movs	r1, #16
   4235e:	4618      	mov	r0, r3
   42360:	f7fe fc18 	bl	40b94 <rotr32>
   42364:	4603      	mov	r3, r0
   42366:	63fb      	str	r3, [r7, #60]	; 0x3c
   42368:	6bba      	ldr	r2, [r7, #56]	; 0x38
   4236a:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   4236c:	4413      	add	r3, r2
   4236e:	63bb      	str	r3, [r7, #56]	; 0x38
   42370:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   42372:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   42374:	4053      	eors	r3, r2
   42376:	210c      	movs	r1, #12
   42378:	4618      	mov	r0, r3
   4237a:	f7fe fc0b 	bl	40b94 <rotr32>
   4237e:	4603      	mov	r3, r0
   42380:	627b      	str	r3, [r7, #36]	; 0x24
   42382:	693a      	ldr	r2, [r7, #16]
   42384:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   42386:	441a      	add	r2, r3
   42388:	230c      	movs	r3, #12
   4238a:	009b      	lsls	r3, r3, #2
   4238c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42390:	440b      	add	r3, r1
   42392:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42396:	4413      	add	r3, r2
   42398:	613b      	str	r3, [r7, #16]
   4239a:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   4239c:	693b      	ldr	r3, [r7, #16]
   4239e:	4053      	eors	r3, r2
   423a0:	2108      	movs	r1, #8
   423a2:	4618      	mov	r0, r3
   423a4:	f7fe fbf6 	bl	40b94 <rotr32>
   423a8:	4603      	mov	r3, r0
   423aa:	63fb      	str	r3, [r7, #60]	; 0x3c
   423ac:	6bba      	ldr	r2, [r7, #56]	; 0x38
   423ae:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   423b0:	4413      	add	r3, r2
   423b2:	63bb      	str	r3, [r7, #56]	; 0x38
   423b4:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   423b6:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   423b8:	4053      	eors	r3, r2
   423ba:	2107      	movs	r1, #7
   423bc:	4618      	mov	r0, r3
   423be:	f7fe fbe9 	bl	40b94 <rotr32>
   423c2:	4603      	mov	r3, r0
   423c4:	627b      	str	r3, [r7, #36]	; 0x24
   423c6:	697a      	ldr	r2, [r7, #20]
   423c8:	6abb      	ldr	r3, [r7, #40]	; 0x28
   423ca:	441a      	add	r2, r3
   423cc:	2306      	movs	r3, #6
   423ce:	009b      	lsls	r3, r3, #2
   423d0:	f107 0190 	add.w	r1, r7, #144	; 0x90
   423d4:	440b      	add	r3, r1
   423d6:	f853 3c44 	ldr.w	r3, [r3, #-68]
   423da:	4413      	add	r3, r2
   423dc:	617b      	str	r3, [r7, #20]
   423de:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   423e0:	697b      	ldr	r3, [r7, #20]
   423e2:	4053      	eors	r3, r2
   423e4:	2110      	movs	r1, #16
   423e6:	4618      	mov	r0, r3
   423e8:	f7fe fbd4 	bl	40b94 <rotr32>
   423ec:	4603      	mov	r3, r0
   423ee:	643b      	str	r3, [r7, #64]	; 0x40
   423f0:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   423f2:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   423f4:	4413      	add	r3, r2
   423f6:	62fb      	str	r3, [r7, #44]	; 0x2c
   423f8:	6aba      	ldr	r2, [r7, #40]	; 0x28
   423fa:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   423fc:	4053      	eors	r3, r2
   423fe:	210c      	movs	r1, #12
   42400:	4618      	mov	r0, r3
   42402:	f7fe fbc7 	bl	40b94 <rotr32>
   42406:	4603      	mov	r3, r0
   42408:	62bb      	str	r3, [r7, #40]	; 0x28
   4240a:	697a      	ldr	r2, [r7, #20]
   4240c:	6abb      	ldr	r3, [r7, #40]	; 0x28
   4240e:	441a      	add	r2, r3
   42410:	2308      	movs	r3, #8
   42412:	009b      	lsls	r3, r3, #2
   42414:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42418:	440b      	add	r3, r1
   4241a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4241e:	4413      	add	r3, r2
   42420:	617b      	str	r3, [r7, #20]
   42422:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   42424:	697b      	ldr	r3, [r7, #20]
   42426:	4053      	eors	r3, r2
   42428:	2108      	movs	r1, #8
   4242a:	4618      	mov	r0, r3
   4242c:	f7fe fbb2 	bl	40b94 <rotr32>
   42430:	4603      	mov	r3, r0
   42432:	643b      	str	r3, [r7, #64]	; 0x40
   42434:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   42436:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   42438:	4413      	add	r3, r2
   4243a:	62fb      	str	r3, [r7, #44]	; 0x2c
   4243c:	6aba      	ldr	r2, [r7, #40]	; 0x28
   4243e:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   42440:	4053      	eors	r3, r2
   42442:	2107      	movs	r1, #7
   42444:	4618      	mov	r0, r3
   42446:	f7fe fba5 	bl	40b94 <rotr32>
   4244a:	4603      	mov	r3, r0
   4244c:	62bb      	str	r3, [r7, #40]	; 0x28
   4244e:	69ba      	ldr	r2, [r7, #24]
   42450:	69fb      	ldr	r3, [r7, #28]
   42452:	441a      	add	r2, r3
   42454:	2303      	movs	r3, #3
   42456:	009b      	lsls	r3, r3, #2
   42458:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4245c:	440b      	add	r3, r1
   4245e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42462:	4413      	add	r3, r2
   42464:	61bb      	str	r3, [r7, #24]
   42466:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   42468:	69bb      	ldr	r3, [r7, #24]
   4246a:	4053      	eors	r3, r2
   4246c:	2110      	movs	r1, #16
   4246e:	4618      	mov	r0, r3
   42470:	f7fe fb90 	bl	40b94 <rotr32>
   42474:	4603      	mov	r3, r0
   42476:	647b      	str	r3, [r7, #68]	; 0x44
   42478:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   4247a:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   4247c:	4413      	add	r3, r2
   4247e:	633b      	str	r3, [r7, #48]	; 0x30
   42480:	69fa      	ldr	r2, [r7, #28]
   42482:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   42484:	4053      	eors	r3, r2
   42486:	210c      	movs	r1, #12
   42488:	4618      	mov	r0, r3
   4248a:	f7fe fb83 	bl	40b94 <rotr32>
   4248e:	4603      	mov	r3, r0
   42490:	61fb      	str	r3, [r7, #28]
   42492:	69ba      	ldr	r2, [r7, #24]
   42494:	69fb      	ldr	r3, [r7, #28]
   42496:	441a      	add	r2, r3
   42498:	230d      	movs	r3, #13
   4249a:	009b      	lsls	r3, r3, #2
   4249c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   424a0:	440b      	add	r3, r1
   424a2:	f853 3c44 	ldr.w	r3, [r3, #-68]
   424a6:	4413      	add	r3, r2
   424a8:	61bb      	str	r3, [r7, #24]
   424aa:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   424ac:	69bb      	ldr	r3, [r7, #24]
   424ae:	4053      	eors	r3, r2
   424b0:	2108      	movs	r1, #8
   424b2:	4618      	mov	r0, r3
   424b4:	f7fe fb6e 	bl	40b94 <rotr32>
   424b8:	4603      	mov	r3, r0
   424ba:	647b      	str	r3, [r7, #68]	; 0x44
   424bc:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   424be:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   424c0:	4413      	add	r3, r2
   424c2:	633b      	str	r3, [r7, #48]	; 0x30
   424c4:	69fa      	ldr	r2, [r7, #28]
   424c6:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   424c8:	4053      	eors	r3, r2
   424ca:	2107      	movs	r1, #7
   424cc:	4618      	mov	r0, r3
   424ce:	f7fe fb61 	bl	40b94 <rotr32>
   424d2:	4603      	mov	r3, r0
   424d4:	61fb      	str	r3, [r7, #28]
   424d6:	68fa      	ldr	r2, [r7, #12]
   424d8:	69fb      	ldr	r3, [r7, #28]
   424da:	441a      	add	r2, r3
   424dc:	2302      	movs	r3, #2
   424de:	009b      	lsls	r3, r3, #2
   424e0:	f107 0190 	add.w	r1, r7, #144	; 0x90
   424e4:	440b      	add	r3, r1
   424e6:	f853 3c44 	ldr.w	r3, [r3, #-68]
   424ea:	4413      	add	r3, r2
   424ec:	60fb      	str	r3, [r7, #12]
   424ee:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   424f0:	68fb      	ldr	r3, [r7, #12]
   424f2:	4053      	eors	r3, r2
   424f4:	2110      	movs	r1, #16
   424f6:	4618      	mov	r0, r3
   424f8:	f7fe fb4c 	bl	40b94 <rotr32>
   424fc:	4603      	mov	r3, r0
   424fe:	63fb      	str	r3, [r7, #60]	; 0x3c
   42500:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   42502:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   42504:	4413      	add	r3, r2
   42506:	62fb      	str	r3, [r7, #44]	; 0x2c
   42508:	69fa      	ldr	r2, [r7, #28]
   4250a:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   4250c:	4053      	eors	r3, r2
   4250e:	210c      	movs	r1, #12
   42510:	4618      	mov	r0, r3
   42512:	f7fe fb3f 	bl	40b94 <rotr32>
   42516:	4603      	mov	r3, r0
   42518:	61fb      	str	r3, [r7, #28]
   4251a:	68fa      	ldr	r2, [r7, #12]
   4251c:	69fb      	ldr	r3, [r7, #28]
   4251e:	441a      	add	r2, r3
   42520:	230c      	movs	r3, #12
   42522:	009b      	lsls	r3, r3, #2
   42524:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42528:	440b      	add	r3, r1
   4252a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4252e:	4413      	add	r3, r2
   42530:	60fb      	str	r3, [r7, #12]
   42532:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   42534:	68fb      	ldr	r3, [r7, #12]
   42536:	4053      	eors	r3, r2
   42538:	2108      	movs	r1, #8
   4253a:	4618      	mov	r0, r3
   4253c:	f7fe fb2a 	bl	40b94 <rotr32>
   42540:	4603      	mov	r3, r0
   42542:	63fb      	str	r3, [r7, #60]	; 0x3c
   42544:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   42546:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   42548:	4413      	add	r3, r2
   4254a:	62fb      	str	r3, [r7, #44]	; 0x2c
   4254c:	69fa      	ldr	r2, [r7, #28]
   4254e:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   42550:	4053      	eors	r3, r2
   42552:	2107      	movs	r1, #7
   42554:	4618      	mov	r0, r3
   42556:	f7fe fb1d 	bl	40b94 <rotr32>
   4255a:	4603      	mov	r3, r0
   4255c:	61fb      	str	r3, [r7, #28]
   4255e:	693a      	ldr	r2, [r7, #16]
   42560:	6a3b      	ldr	r3, [r7, #32]
   42562:	441a      	add	r2, r3
   42564:	2306      	movs	r3, #6
   42566:	009b      	lsls	r3, r3, #2
   42568:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4256c:	440b      	add	r3, r1
   4256e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42572:	4413      	add	r3, r2
   42574:	613b      	str	r3, [r7, #16]
   42576:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   42578:	693b      	ldr	r3, [r7, #16]
   4257a:	4053      	eors	r3, r2
   4257c:	2110      	movs	r1, #16
   4257e:	4618      	mov	r0, r3
   42580:	f7fe fb08 	bl	40b94 <rotr32>
   42584:	4603      	mov	r3, r0
   42586:	643b      	str	r3, [r7, #64]	; 0x40
   42588:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   4258a:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   4258c:	4413      	add	r3, r2
   4258e:	633b      	str	r3, [r7, #48]	; 0x30
   42590:	6a3a      	ldr	r2, [r7, #32]
   42592:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   42594:	4053      	eors	r3, r2
   42596:	210c      	movs	r1, #12
   42598:	4618      	mov	r0, r3
   4259a:	f7fe fafb 	bl	40b94 <rotr32>
   4259e:	4603      	mov	r3, r0
   425a0:	623b      	str	r3, [r7, #32]
   425a2:	693a      	ldr	r2, [r7, #16]
   425a4:	6a3b      	ldr	r3, [r7, #32]
   425a6:	441a      	add	r2, r3
   425a8:	230a      	movs	r3, #10
   425aa:	009b      	lsls	r3, r3, #2
   425ac:	f107 0190 	add.w	r1, r7, #144	; 0x90
   425b0:	440b      	add	r3, r1
   425b2:	f853 3c44 	ldr.w	r3, [r3, #-68]
   425b6:	4413      	add	r3, r2
   425b8:	613b      	str	r3, [r7, #16]
   425ba:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   425bc:	693b      	ldr	r3, [r7, #16]
   425be:	4053      	eors	r3, r2
   425c0:	2108      	movs	r1, #8
   425c2:	4618      	mov	r0, r3
   425c4:	f7fe fae6 	bl	40b94 <rotr32>
   425c8:	4603      	mov	r3, r0
   425ca:	643b      	str	r3, [r7, #64]	; 0x40
   425cc:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   425ce:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   425d0:	4413      	add	r3, r2
   425d2:	633b      	str	r3, [r7, #48]	; 0x30
   425d4:	6a3a      	ldr	r2, [r7, #32]
   425d6:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   425d8:	4053      	eors	r3, r2
   425da:	2107      	movs	r1, #7
   425dc:	4618      	mov	r0, r3
   425de:	f7fe fad9 	bl	40b94 <rotr32>
   425e2:	4603      	mov	r3, r0
   425e4:	623b      	str	r3, [r7, #32]
   425e6:	697a      	ldr	r2, [r7, #20]
   425e8:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   425ea:	441a      	add	r2, r3
   425ec:	2300      	movs	r3, #0
   425ee:	009b      	lsls	r3, r3, #2
   425f0:	f107 0190 	add.w	r1, r7, #144	; 0x90
   425f4:	440b      	add	r3, r1
   425f6:	f853 3c44 	ldr.w	r3, [r3, #-68]
   425fa:	4413      	add	r3, r2
   425fc:	617b      	str	r3, [r7, #20]
   425fe:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   42600:	697b      	ldr	r3, [r7, #20]
   42602:	4053      	eors	r3, r2
   42604:	2110      	movs	r1, #16
   42606:	4618      	mov	r0, r3
   42608:	f7fe fac4 	bl	40b94 <rotr32>
   4260c:	4603      	mov	r3, r0
   4260e:	647b      	str	r3, [r7, #68]	; 0x44
   42610:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   42612:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   42614:	4413      	add	r3, r2
   42616:	637b      	str	r3, [r7, #52]	; 0x34
   42618:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   4261a:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   4261c:	4053      	eors	r3, r2
   4261e:	210c      	movs	r1, #12
   42620:	4618      	mov	r0, r3
   42622:	f7fe fab7 	bl	40b94 <rotr32>
   42626:	4603      	mov	r3, r0
   42628:	627b      	str	r3, [r7, #36]	; 0x24
   4262a:	697a      	ldr	r2, [r7, #20]
   4262c:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   4262e:	441a      	add	r2, r3
   42630:	230b      	movs	r3, #11
   42632:	009b      	lsls	r3, r3, #2
   42634:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42638:	440b      	add	r3, r1
   4263a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4263e:	4413      	add	r3, r2
   42640:	617b      	str	r3, [r7, #20]
   42642:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   42644:	697b      	ldr	r3, [r7, #20]
   42646:	4053      	eors	r3, r2
   42648:	2108      	movs	r1, #8
   4264a:	4618      	mov	r0, r3
   4264c:	f7fe faa2 	bl	40b94 <rotr32>
   42650:	4603      	mov	r3, r0
   42652:	647b      	str	r3, [r7, #68]	; 0x44
   42654:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   42656:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   42658:	4413      	add	r3, r2
   4265a:	637b      	str	r3, [r7, #52]	; 0x34
   4265c:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   4265e:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   42660:	4053      	eors	r3, r2
   42662:	2107      	movs	r1, #7
   42664:	4618      	mov	r0, r3
   42666:	f7fe fa95 	bl	40b94 <rotr32>
   4266a:	4603      	mov	r3, r0
   4266c:	627b      	str	r3, [r7, #36]	; 0x24
   4266e:	69ba      	ldr	r2, [r7, #24]
   42670:	6abb      	ldr	r3, [r7, #40]	; 0x28
   42672:	441a      	add	r2, r3
   42674:	2308      	movs	r3, #8
   42676:	009b      	lsls	r3, r3, #2
   42678:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4267c:	440b      	add	r3, r1
   4267e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42682:	4413      	add	r3, r2
   42684:	61bb      	str	r3, [r7, #24]
   42686:	6cba      	ldr	r2, [r7, #72]	; 0x48
   42688:	69bb      	ldr	r3, [r7, #24]
   4268a:	4053      	eors	r3, r2
   4268c:	2110      	movs	r1, #16
   4268e:	4618      	mov	r0, r3
   42690:	f7fe fa80 	bl	40b94 <rotr32>
   42694:	4603      	mov	r3, r0
   42696:	64bb      	str	r3, [r7, #72]	; 0x48
   42698:	6bba      	ldr	r2, [r7, #56]	; 0x38
   4269a:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   4269c:	4413      	add	r3, r2
   4269e:	63bb      	str	r3, [r7, #56]	; 0x38
   426a0:	6aba      	ldr	r2, [r7, #40]	; 0x28
   426a2:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   426a4:	4053      	eors	r3, r2
   426a6:	210c      	movs	r1, #12
   426a8:	4618      	mov	r0, r3
   426aa:	f7fe fa73 	bl	40b94 <rotr32>
   426ae:	4603      	mov	r3, r0
   426b0:	62bb      	str	r3, [r7, #40]	; 0x28
   426b2:	69ba      	ldr	r2, [r7, #24]
   426b4:	6abb      	ldr	r3, [r7, #40]	; 0x28
   426b6:	441a      	add	r2, r3
   426b8:	2303      	movs	r3, #3
   426ba:	009b      	lsls	r3, r3, #2
   426bc:	f107 0190 	add.w	r1, r7, #144	; 0x90
   426c0:	440b      	add	r3, r1
   426c2:	f853 3c44 	ldr.w	r3, [r3, #-68]
   426c6:	4413      	add	r3, r2
   426c8:	61bb      	str	r3, [r7, #24]
   426ca:	6cba      	ldr	r2, [r7, #72]	; 0x48
   426cc:	69bb      	ldr	r3, [r7, #24]
   426ce:	4053      	eors	r3, r2
   426d0:	2108      	movs	r1, #8
   426d2:	4618      	mov	r0, r3
   426d4:	f7fe fa5e 	bl	40b94 <rotr32>
   426d8:	4603      	mov	r3, r0
   426da:	64bb      	str	r3, [r7, #72]	; 0x48
   426dc:	6bba      	ldr	r2, [r7, #56]	; 0x38
   426de:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   426e0:	4413      	add	r3, r2
   426e2:	63bb      	str	r3, [r7, #56]	; 0x38
   426e4:	6aba      	ldr	r2, [r7, #40]	; 0x28
   426e6:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   426e8:	4053      	eors	r3, r2
   426ea:	2107      	movs	r1, #7
   426ec:	4618      	mov	r0, r3
   426ee:	f7fe fa51 	bl	40b94 <rotr32>
   426f2:	4603      	mov	r3, r0
   426f4:	62bb      	str	r3, [r7, #40]	; 0x28
   426f6:	68fa      	ldr	r2, [r7, #12]
   426f8:	6a3b      	ldr	r3, [r7, #32]
   426fa:	441a      	add	r2, r3
   426fc:	2304      	movs	r3, #4
   426fe:	009b      	lsls	r3, r3, #2
   42700:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42704:	440b      	add	r3, r1
   42706:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4270a:	4413      	add	r3, r2
   4270c:	60fb      	str	r3, [r7, #12]
   4270e:	6cba      	ldr	r2, [r7, #72]	; 0x48
   42710:	68fb      	ldr	r3, [r7, #12]
   42712:	4053      	eors	r3, r2
   42714:	2110      	movs	r1, #16
   42716:	4618      	mov	r0, r3
   42718:	f7fe fa3c 	bl	40b94 <rotr32>
   4271c:	4603      	mov	r3, r0
   4271e:	64bb      	str	r3, [r7, #72]	; 0x48
   42720:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   42722:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   42724:	4413      	add	r3, r2
   42726:	637b      	str	r3, [r7, #52]	; 0x34
   42728:	6a3a      	ldr	r2, [r7, #32]
   4272a:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   4272c:	4053      	eors	r3, r2
   4272e:	210c      	movs	r1, #12
   42730:	4618      	mov	r0, r3
   42732:	f7fe fa2f 	bl	40b94 <rotr32>
   42736:	4603      	mov	r3, r0
   42738:	623b      	str	r3, [r7, #32]
   4273a:	68fa      	ldr	r2, [r7, #12]
   4273c:	6a3b      	ldr	r3, [r7, #32]
   4273e:	441a      	add	r2, r3
   42740:	230d      	movs	r3, #13
   42742:	009b      	lsls	r3, r3, #2
   42744:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42748:	440b      	add	r3, r1
   4274a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4274e:	4413      	add	r3, r2
   42750:	60fb      	str	r3, [r7, #12]
   42752:	6cba      	ldr	r2, [r7, #72]	; 0x48
   42754:	68fb      	ldr	r3, [r7, #12]
   42756:	4053      	eors	r3, r2
   42758:	2108      	movs	r1, #8
   4275a:	4618      	mov	r0, r3
   4275c:	f7fe fa1a 	bl	40b94 <rotr32>
   42760:	4603      	mov	r3, r0
   42762:	64bb      	str	r3, [r7, #72]	; 0x48
   42764:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   42766:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   42768:	4413      	add	r3, r2
   4276a:	637b      	str	r3, [r7, #52]	; 0x34
   4276c:	6a3a      	ldr	r2, [r7, #32]
   4276e:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   42770:	4053      	eors	r3, r2
   42772:	2107      	movs	r1, #7
   42774:	4618      	mov	r0, r3
   42776:	f7fe fa0d 	bl	40b94 <rotr32>
   4277a:	4603      	mov	r3, r0
   4277c:	623b      	str	r3, [r7, #32]
   4277e:	693a      	ldr	r2, [r7, #16]
   42780:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   42782:	441a      	add	r2, r3
   42784:	2307      	movs	r3, #7
   42786:	009b      	lsls	r3, r3, #2
   42788:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4278c:	440b      	add	r3, r1
   4278e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42792:	4413      	add	r3, r2
   42794:	613b      	str	r3, [r7, #16]
   42796:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   42798:	693b      	ldr	r3, [r7, #16]
   4279a:	4053      	eors	r3, r2
   4279c:	2110      	movs	r1, #16
   4279e:	4618      	mov	r0, r3
   427a0:	f7fe f9f8 	bl	40b94 <rotr32>
   427a4:	4603      	mov	r3, r0
   427a6:	63fb      	str	r3, [r7, #60]	; 0x3c
   427a8:	6bba      	ldr	r2, [r7, #56]	; 0x38
   427aa:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   427ac:	4413      	add	r3, r2
   427ae:	63bb      	str	r3, [r7, #56]	; 0x38
   427b0:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   427b2:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   427b4:	4053      	eors	r3, r2
   427b6:	210c      	movs	r1, #12
   427b8:	4618      	mov	r0, r3
   427ba:	f7fe f9eb 	bl	40b94 <rotr32>
   427be:	4603      	mov	r3, r0
   427c0:	627b      	str	r3, [r7, #36]	; 0x24
   427c2:	693a      	ldr	r2, [r7, #16]
   427c4:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   427c6:	441a      	add	r2, r3
   427c8:	2305      	movs	r3, #5
   427ca:	009b      	lsls	r3, r3, #2
   427cc:	f107 0190 	add.w	r1, r7, #144	; 0x90
   427d0:	440b      	add	r3, r1
   427d2:	f853 3c44 	ldr.w	r3, [r3, #-68]
   427d6:	4413      	add	r3, r2
   427d8:	613b      	str	r3, [r7, #16]
   427da:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   427dc:	693b      	ldr	r3, [r7, #16]
   427de:	4053      	eors	r3, r2
   427e0:	2108      	movs	r1, #8
   427e2:	4618      	mov	r0, r3
   427e4:	f7fe f9d6 	bl	40b94 <rotr32>
   427e8:	4603      	mov	r3, r0
   427ea:	63fb      	str	r3, [r7, #60]	; 0x3c
   427ec:	6bba      	ldr	r2, [r7, #56]	; 0x38
   427ee:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   427f0:	4413      	add	r3, r2
   427f2:	63bb      	str	r3, [r7, #56]	; 0x38
   427f4:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   427f6:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   427f8:	4053      	eors	r3, r2
   427fa:	2107      	movs	r1, #7
   427fc:	4618      	mov	r0, r3
   427fe:	f7fe f9c9 	bl	40b94 <rotr32>
   42802:	4603      	mov	r3, r0
   42804:	627b      	str	r3, [r7, #36]	; 0x24
   42806:	697a      	ldr	r2, [r7, #20]
   42808:	6abb      	ldr	r3, [r7, #40]	; 0x28
   4280a:	441a      	add	r2, r3
   4280c:	230f      	movs	r3, #15
   4280e:	009b      	lsls	r3, r3, #2
   42810:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42814:	440b      	add	r3, r1
   42816:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4281a:	4413      	add	r3, r2
   4281c:	617b      	str	r3, [r7, #20]
   4281e:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   42820:	697b      	ldr	r3, [r7, #20]
   42822:	4053      	eors	r3, r2
   42824:	2110      	movs	r1, #16
   42826:	4618      	mov	r0, r3
   42828:	f7fe f9b4 	bl	40b94 <rotr32>
   4282c:	4603      	mov	r3, r0
   4282e:	643b      	str	r3, [r7, #64]	; 0x40
   42830:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   42832:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   42834:	4413      	add	r3, r2
   42836:	62fb      	str	r3, [r7, #44]	; 0x2c
   42838:	6aba      	ldr	r2, [r7, #40]	; 0x28
   4283a:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   4283c:	4053      	eors	r3, r2
   4283e:	210c      	movs	r1, #12
   42840:	4618      	mov	r0, r3
   42842:	f7fe f9a7 	bl	40b94 <rotr32>
   42846:	4603      	mov	r3, r0
   42848:	62bb      	str	r3, [r7, #40]	; 0x28
   4284a:	697a      	ldr	r2, [r7, #20]
   4284c:	6abb      	ldr	r3, [r7, #40]	; 0x28
   4284e:	441a      	add	r2, r3
   42850:	230e      	movs	r3, #14
   42852:	009b      	lsls	r3, r3, #2
   42854:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42858:	440b      	add	r3, r1
   4285a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4285e:	4413      	add	r3, r2
   42860:	617b      	str	r3, [r7, #20]
   42862:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   42864:	697b      	ldr	r3, [r7, #20]
   42866:	4053      	eors	r3, r2
   42868:	2108      	movs	r1, #8
   4286a:	4618      	mov	r0, r3
   4286c:	f7fe f992 	bl	40b94 <rotr32>
   42870:	4603      	mov	r3, r0
   42872:	643b      	str	r3, [r7, #64]	; 0x40
   42874:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   42876:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   42878:	4413      	add	r3, r2
   4287a:	62fb      	str	r3, [r7, #44]	; 0x2c
   4287c:	6aba      	ldr	r2, [r7, #40]	; 0x28
   4287e:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   42880:	4053      	eors	r3, r2
   42882:	2107      	movs	r1, #7
   42884:	4618      	mov	r0, r3
   42886:	f7fe f985 	bl	40b94 <rotr32>
   4288a:	4603      	mov	r3, r0
   4288c:	62bb      	str	r3, [r7, #40]	; 0x28
   4288e:	69ba      	ldr	r2, [r7, #24]
   42890:	69fb      	ldr	r3, [r7, #28]
   42892:	441a      	add	r2, r3
   42894:	2301      	movs	r3, #1
   42896:	009b      	lsls	r3, r3, #2
   42898:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4289c:	440b      	add	r3, r1
   4289e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   428a2:	4413      	add	r3, r2
   428a4:	61bb      	str	r3, [r7, #24]
   428a6:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   428a8:	69bb      	ldr	r3, [r7, #24]
   428aa:	4053      	eors	r3, r2
   428ac:	2110      	movs	r1, #16
   428ae:	4618      	mov	r0, r3
   428b0:	f7fe f970 	bl	40b94 <rotr32>
   428b4:	4603      	mov	r3, r0
   428b6:	647b      	str	r3, [r7, #68]	; 0x44
   428b8:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   428ba:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   428bc:	4413      	add	r3, r2
   428be:	633b      	str	r3, [r7, #48]	; 0x30
   428c0:	69fa      	ldr	r2, [r7, #28]
   428c2:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   428c4:	4053      	eors	r3, r2
   428c6:	210c      	movs	r1, #12
   428c8:	4618      	mov	r0, r3
   428ca:	f7fe f963 	bl	40b94 <rotr32>
   428ce:	4603      	mov	r3, r0
   428d0:	61fb      	str	r3, [r7, #28]
   428d2:	69ba      	ldr	r2, [r7, #24]
   428d4:	69fb      	ldr	r3, [r7, #28]
   428d6:	441a      	add	r2, r3
   428d8:	2309      	movs	r3, #9
   428da:	009b      	lsls	r3, r3, #2
   428dc:	f107 0190 	add.w	r1, r7, #144	; 0x90
   428e0:	440b      	add	r3, r1
   428e2:	f853 3c44 	ldr.w	r3, [r3, #-68]
   428e6:	4413      	add	r3, r2
   428e8:	61bb      	str	r3, [r7, #24]
   428ea:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   428ec:	69bb      	ldr	r3, [r7, #24]
   428ee:	4053      	eors	r3, r2
   428f0:	2108      	movs	r1, #8
   428f2:	4618      	mov	r0, r3
   428f4:	f7fe f94e 	bl	40b94 <rotr32>
   428f8:	4603      	mov	r3, r0
   428fa:	647b      	str	r3, [r7, #68]	; 0x44
   428fc:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   428fe:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   42900:	4413      	add	r3, r2
   42902:	633b      	str	r3, [r7, #48]	; 0x30
   42904:	69fa      	ldr	r2, [r7, #28]
   42906:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   42908:	4053      	eors	r3, r2
   4290a:	2107      	movs	r1, #7
   4290c:	4618      	mov	r0, r3
   4290e:	f7fe f941 	bl	40b94 <rotr32>
   42912:	4603      	mov	r3, r0
   42914:	61fb      	str	r3, [r7, #28]
   42916:	68fa      	ldr	r2, [r7, #12]
   42918:	69fb      	ldr	r3, [r7, #28]
   4291a:	441a      	add	r2, r3
   4291c:	230c      	movs	r3, #12
   4291e:	009b      	lsls	r3, r3, #2
   42920:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42924:	440b      	add	r3, r1
   42926:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4292a:	4413      	add	r3, r2
   4292c:	60fb      	str	r3, [r7, #12]
   4292e:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   42930:	68fb      	ldr	r3, [r7, #12]
   42932:	4053      	eors	r3, r2
   42934:	2110      	movs	r1, #16
   42936:	4618      	mov	r0, r3
   42938:	f7fe f92c 	bl	40b94 <rotr32>
   4293c:	4603      	mov	r3, r0
   4293e:	63fb      	str	r3, [r7, #60]	; 0x3c
   42940:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   42942:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   42944:	4413      	add	r3, r2
   42946:	62fb      	str	r3, [r7, #44]	; 0x2c
   42948:	69fa      	ldr	r2, [r7, #28]
   4294a:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   4294c:	4053      	eors	r3, r2
   4294e:	210c      	movs	r1, #12
   42950:	4618      	mov	r0, r3
   42952:	f7fe f91f 	bl	40b94 <rotr32>
   42956:	4603      	mov	r3, r0
   42958:	61fb      	str	r3, [r7, #28]
   4295a:	68fa      	ldr	r2, [r7, #12]
   4295c:	69fb      	ldr	r3, [r7, #28]
   4295e:	441a      	add	r2, r3
   42960:	2305      	movs	r3, #5
   42962:	009b      	lsls	r3, r3, #2
   42964:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42968:	440b      	add	r3, r1
   4296a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4296e:	4413      	add	r3, r2
   42970:	60fb      	str	r3, [r7, #12]
   42972:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   42974:	68fb      	ldr	r3, [r7, #12]
   42976:	4053      	eors	r3, r2
   42978:	2108      	movs	r1, #8
   4297a:	4618      	mov	r0, r3
   4297c:	f7fe f90a 	bl	40b94 <rotr32>
   42980:	4603      	mov	r3, r0
   42982:	63fb      	str	r3, [r7, #60]	; 0x3c
   42984:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   42986:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   42988:	4413      	add	r3, r2
   4298a:	62fb      	str	r3, [r7, #44]	; 0x2c
   4298c:	69fa      	ldr	r2, [r7, #28]
   4298e:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   42990:	4053      	eors	r3, r2
   42992:	2107      	movs	r1, #7
   42994:	4618      	mov	r0, r3
   42996:	f7fe f8fd 	bl	40b94 <rotr32>
   4299a:	4603      	mov	r3, r0
   4299c:	61fb      	str	r3, [r7, #28]
   4299e:	693a      	ldr	r2, [r7, #16]
   429a0:	6a3b      	ldr	r3, [r7, #32]
   429a2:	441a      	add	r2, r3
   429a4:	2301      	movs	r3, #1
   429a6:	009b      	lsls	r3, r3, #2
   429a8:	f107 0190 	add.w	r1, r7, #144	; 0x90
   429ac:	440b      	add	r3, r1
   429ae:	f853 3c44 	ldr.w	r3, [r3, #-68]
   429b2:	4413      	add	r3, r2
   429b4:	613b      	str	r3, [r7, #16]
   429b6:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   429b8:	693b      	ldr	r3, [r7, #16]
   429ba:	4053      	eors	r3, r2
   429bc:	2110      	movs	r1, #16
   429be:	4618      	mov	r0, r3
   429c0:	f7fe f8e8 	bl	40b94 <rotr32>
   429c4:	4603      	mov	r3, r0
   429c6:	643b      	str	r3, [r7, #64]	; 0x40
   429c8:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   429ca:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   429cc:	4413      	add	r3, r2
   429ce:	633b      	str	r3, [r7, #48]	; 0x30
   429d0:	6a3a      	ldr	r2, [r7, #32]
   429d2:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   429d4:	4053      	eors	r3, r2
   429d6:	210c      	movs	r1, #12
   429d8:	4618      	mov	r0, r3
   429da:	f7fe f8db 	bl	40b94 <rotr32>
   429de:	4603      	mov	r3, r0
   429e0:	623b      	str	r3, [r7, #32]
   429e2:	693a      	ldr	r2, [r7, #16]
   429e4:	6a3b      	ldr	r3, [r7, #32]
   429e6:	441a      	add	r2, r3
   429e8:	230f      	movs	r3, #15
   429ea:	009b      	lsls	r3, r3, #2
   429ec:	f107 0190 	add.w	r1, r7, #144	; 0x90
   429f0:	440b      	add	r3, r1
   429f2:	f853 3c44 	ldr.w	r3, [r3, #-68]
   429f6:	4413      	add	r3, r2
   429f8:	613b      	str	r3, [r7, #16]
   429fa:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   429fc:	693b      	ldr	r3, [r7, #16]
   429fe:	4053      	eors	r3, r2
   42a00:	2108      	movs	r1, #8
   42a02:	4618      	mov	r0, r3
   42a04:	f7fe f8c6 	bl	40b94 <rotr32>
   42a08:	4603      	mov	r3, r0
   42a0a:	643b      	str	r3, [r7, #64]	; 0x40
   42a0c:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   42a0e:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   42a10:	4413      	add	r3, r2
   42a12:	633b      	str	r3, [r7, #48]	; 0x30
   42a14:	6a3a      	ldr	r2, [r7, #32]
   42a16:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   42a18:	4053      	eors	r3, r2
   42a1a:	2107      	movs	r1, #7
   42a1c:	4618      	mov	r0, r3
   42a1e:	f7fe f8b9 	bl	40b94 <rotr32>
   42a22:	4603      	mov	r3, r0
   42a24:	623b      	str	r3, [r7, #32]
   42a26:	697a      	ldr	r2, [r7, #20]
   42a28:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   42a2a:	441a      	add	r2, r3
   42a2c:	230e      	movs	r3, #14
   42a2e:	009b      	lsls	r3, r3, #2
   42a30:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42a34:	440b      	add	r3, r1
   42a36:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42a3a:	4413      	add	r3, r2
   42a3c:	617b      	str	r3, [r7, #20]
   42a3e:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   42a40:	697b      	ldr	r3, [r7, #20]
   42a42:	4053      	eors	r3, r2
   42a44:	2110      	movs	r1, #16
   42a46:	4618      	mov	r0, r3
   42a48:	f7fe f8a4 	bl	40b94 <rotr32>
   42a4c:	4603      	mov	r3, r0
   42a4e:	647b      	str	r3, [r7, #68]	; 0x44
   42a50:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   42a52:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   42a54:	4413      	add	r3, r2
   42a56:	637b      	str	r3, [r7, #52]	; 0x34
   42a58:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   42a5a:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   42a5c:	4053      	eors	r3, r2
   42a5e:	210c      	movs	r1, #12
   42a60:	4618      	mov	r0, r3
   42a62:	f7fe f897 	bl	40b94 <rotr32>
   42a66:	4603      	mov	r3, r0
   42a68:	627b      	str	r3, [r7, #36]	; 0x24
   42a6a:	697a      	ldr	r2, [r7, #20]
   42a6c:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   42a6e:	441a      	add	r2, r3
   42a70:	230d      	movs	r3, #13
   42a72:	009b      	lsls	r3, r3, #2
   42a74:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42a78:	440b      	add	r3, r1
   42a7a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42a7e:	4413      	add	r3, r2
   42a80:	617b      	str	r3, [r7, #20]
   42a82:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   42a84:	697b      	ldr	r3, [r7, #20]
   42a86:	4053      	eors	r3, r2
   42a88:	2108      	movs	r1, #8
   42a8a:	4618      	mov	r0, r3
   42a8c:	f7fe f882 	bl	40b94 <rotr32>
   42a90:	4603      	mov	r3, r0
   42a92:	647b      	str	r3, [r7, #68]	; 0x44
   42a94:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   42a96:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   42a98:	4413      	add	r3, r2
   42a9a:	637b      	str	r3, [r7, #52]	; 0x34
   42a9c:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   42a9e:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   42aa0:	4053      	eors	r3, r2
   42aa2:	2107      	movs	r1, #7
   42aa4:	4618      	mov	r0, r3
   42aa6:	f7fe f875 	bl	40b94 <rotr32>
   42aaa:	4603      	mov	r3, r0
   42aac:	627b      	str	r3, [r7, #36]	; 0x24
   42aae:	69ba      	ldr	r2, [r7, #24]
   42ab0:	6abb      	ldr	r3, [r7, #40]	; 0x28
   42ab2:	441a      	add	r2, r3
   42ab4:	2304      	movs	r3, #4
   42ab6:	009b      	lsls	r3, r3, #2
   42ab8:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42abc:	440b      	add	r3, r1
   42abe:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42ac2:	4413      	add	r3, r2
   42ac4:	61bb      	str	r3, [r7, #24]
   42ac6:	6cba      	ldr	r2, [r7, #72]	; 0x48
   42ac8:	69bb      	ldr	r3, [r7, #24]
   42aca:	4053      	eors	r3, r2
   42acc:	2110      	movs	r1, #16
   42ace:	4618      	mov	r0, r3
   42ad0:	f7fe f860 	bl	40b94 <rotr32>
   42ad4:	4603      	mov	r3, r0
   42ad6:	64bb      	str	r3, [r7, #72]	; 0x48
   42ad8:	6bba      	ldr	r2, [r7, #56]	; 0x38
   42ada:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   42adc:	4413      	add	r3, r2
   42ade:	63bb      	str	r3, [r7, #56]	; 0x38
   42ae0:	6aba      	ldr	r2, [r7, #40]	; 0x28
   42ae2:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   42ae4:	4053      	eors	r3, r2
   42ae6:	210c      	movs	r1, #12
   42ae8:	4618      	mov	r0, r3
   42aea:	f7fe f853 	bl	40b94 <rotr32>
   42aee:	4603      	mov	r3, r0
   42af0:	62bb      	str	r3, [r7, #40]	; 0x28
   42af2:	69ba      	ldr	r2, [r7, #24]
   42af4:	6abb      	ldr	r3, [r7, #40]	; 0x28
   42af6:	441a      	add	r2, r3
   42af8:	230a      	movs	r3, #10
   42afa:	009b      	lsls	r3, r3, #2
   42afc:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42b00:	440b      	add	r3, r1
   42b02:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42b06:	4413      	add	r3, r2
   42b08:	61bb      	str	r3, [r7, #24]
   42b0a:	6cba      	ldr	r2, [r7, #72]	; 0x48
   42b0c:	69bb      	ldr	r3, [r7, #24]
   42b0e:	4053      	eors	r3, r2
   42b10:	2108      	movs	r1, #8
   42b12:	4618      	mov	r0, r3
   42b14:	f7fe f83e 	bl	40b94 <rotr32>
   42b18:	4603      	mov	r3, r0
   42b1a:	64bb      	str	r3, [r7, #72]	; 0x48
   42b1c:	6bba      	ldr	r2, [r7, #56]	; 0x38
   42b1e:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   42b20:	4413      	add	r3, r2
   42b22:	63bb      	str	r3, [r7, #56]	; 0x38
   42b24:	6aba      	ldr	r2, [r7, #40]	; 0x28
   42b26:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   42b28:	4053      	eors	r3, r2
   42b2a:	2107      	movs	r1, #7
   42b2c:	4618      	mov	r0, r3
   42b2e:	f7fe f831 	bl	40b94 <rotr32>
   42b32:	4603      	mov	r3, r0
   42b34:	62bb      	str	r3, [r7, #40]	; 0x28
   42b36:	68fa      	ldr	r2, [r7, #12]
   42b38:	6a3b      	ldr	r3, [r7, #32]
   42b3a:	441a      	add	r2, r3
   42b3c:	2300      	movs	r3, #0
   42b3e:	009b      	lsls	r3, r3, #2
   42b40:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42b44:	440b      	add	r3, r1
   42b46:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42b4a:	4413      	add	r3, r2
   42b4c:	60fb      	str	r3, [r7, #12]
   42b4e:	6cba      	ldr	r2, [r7, #72]	; 0x48
   42b50:	68fb      	ldr	r3, [r7, #12]
   42b52:	4053      	eors	r3, r2
   42b54:	2110      	movs	r1, #16
   42b56:	4618      	mov	r0, r3
   42b58:	f7fe f81c 	bl	40b94 <rotr32>
   42b5c:	4603      	mov	r3, r0
   42b5e:	64bb      	str	r3, [r7, #72]	; 0x48
   42b60:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   42b62:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   42b64:	4413      	add	r3, r2
   42b66:	637b      	str	r3, [r7, #52]	; 0x34
   42b68:	6a3a      	ldr	r2, [r7, #32]
   42b6a:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   42b6c:	4053      	eors	r3, r2
   42b6e:	210c      	movs	r1, #12
   42b70:	4618      	mov	r0, r3
   42b72:	f7fe f80f 	bl	40b94 <rotr32>
   42b76:	4603      	mov	r3, r0
   42b78:	623b      	str	r3, [r7, #32]
   42b7a:	68fa      	ldr	r2, [r7, #12]
   42b7c:	6a3b      	ldr	r3, [r7, #32]
   42b7e:	441a      	add	r2, r3
   42b80:	2307      	movs	r3, #7
   42b82:	009b      	lsls	r3, r3, #2
   42b84:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42b88:	440b      	add	r3, r1
   42b8a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42b8e:	4413      	add	r3, r2
   42b90:	60fb      	str	r3, [r7, #12]
   42b92:	6cba      	ldr	r2, [r7, #72]	; 0x48
   42b94:	68fb      	ldr	r3, [r7, #12]
   42b96:	4053      	eors	r3, r2
   42b98:	2108      	movs	r1, #8
   42b9a:	4618      	mov	r0, r3
   42b9c:	f7fd fffa 	bl	40b94 <rotr32>
   42ba0:	4603      	mov	r3, r0
   42ba2:	64bb      	str	r3, [r7, #72]	; 0x48
   42ba4:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   42ba6:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   42ba8:	4413      	add	r3, r2
   42baa:	637b      	str	r3, [r7, #52]	; 0x34
   42bac:	6a3a      	ldr	r2, [r7, #32]
   42bae:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   42bb0:	4053      	eors	r3, r2
   42bb2:	2107      	movs	r1, #7
   42bb4:	4618      	mov	r0, r3
   42bb6:	f7fd ffed 	bl	40b94 <rotr32>
   42bba:	4603      	mov	r3, r0
   42bbc:	623b      	str	r3, [r7, #32]
   42bbe:	693a      	ldr	r2, [r7, #16]
   42bc0:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   42bc2:	441a      	add	r2, r3
   42bc4:	2306      	movs	r3, #6
   42bc6:	009b      	lsls	r3, r3, #2
   42bc8:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42bcc:	440b      	add	r3, r1
   42bce:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42bd2:	4413      	add	r3, r2
   42bd4:	613b      	str	r3, [r7, #16]
   42bd6:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   42bd8:	693b      	ldr	r3, [r7, #16]
   42bda:	4053      	eors	r3, r2
   42bdc:	2110      	movs	r1, #16
   42bde:	4618      	mov	r0, r3
   42be0:	f7fd ffd8 	bl	40b94 <rotr32>
   42be4:	4603      	mov	r3, r0
   42be6:	63fb      	str	r3, [r7, #60]	; 0x3c
   42be8:	6bba      	ldr	r2, [r7, #56]	; 0x38
   42bea:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   42bec:	4413      	add	r3, r2
   42bee:	63bb      	str	r3, [r7, #56]	; 0x38
   42bf0:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   42bf2:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   42bf4:	4053      	eors	r3, r2
   42bf6:	210c      	movs	r1, #12
   42bf8:	4618      	mov	r0, r3
   42bfa:	f7fd ffcb 	bl	40b94 <rotr32>
   42bfe:	4603      	mov	r3, r0
   42c00:	627b      	str	r3, [r7, #36]	; 0x24
   42c02:	693a      	ldr	r2, [r7, #16]
   42c04:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   42c06:	441a      	add	r2, r3
   42c08:	2303      	movs	r3, #3
   42c0a:	009b      	lsls	r3, r3, #2
   42c0c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42c10:	440b      	add	r3, r1
   42c12:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42c16:	4413      	add	r3, r2
   42c18:	613b      	str	r3, [r7, #16]
   42c1a:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   42c1c:	693b      	ldr	r3, [r7, #16]
   42c1e:	4053      	eors	r3, r2
   42c20:	2108      	movs	r1, #8
   42c22:	4618      	mov	r0, r3
   42c24:	f7fd ffb6 	bl	40b94 <rotr32>
   42c28:	4603      	mov	r3, r0
   42c2a:	63fb      	str	r3, [r7, #60]	; 0x3c
   42c2c:	6bba      	ldr	r2, [r7, #56]	; 0x38
   42c2e:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   42c30:	4413      	add	r3, r2
   42c32:	63bb      	str	r3, [r7, #56]	; 0x38
   42c34:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   42c36:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   42c38:	4053      	eors	r3, r2
   42c3a:	2107      	movs	r1, #7
   42c3c:	4618      	mov	r0, r3
   42c3e:	f7fd ffa9 	bl	40b94 <rotr32>
   42c42:	4603      	mov	r3, r0
   42c44:	627b      	str	r3, [r7, #36]	; 0x24
   42c46:	697a      	ldr	r2, [r7, #20]
   42c48:	6abb      	ldr	r3, [r7, #40]	; 0x28
   42c4a:	441a      	add	r2, r3
   42c4c:	2309      	movs	r3, #9
   42c4e:	009b      	lsls	r3, r3, #2
   42c50:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42c54:	440b      	add	r3, r1
   42c56:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42c5a:	4413      	add	r3, r2
   42c5c:	617b      	str	r3, [r7, #20]
   42c5e:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   42c60:	697b      	ldr	r3, [r7, #20]
   42c62:	4053      	eors	r3, r2
   42c64:	2110      	movs	r1, #16
   42c66:	4618      	mov	r0, r3
   42c68:	f7fd ff94 	bl	40b94 <rotr32>
   42c6c:	4603      	mov	r3, r0
   42c6e:	643b      	str	r3, [r7, #64]	; 0x40
   42c70:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   42c72:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   42c74:	4413      	add	r3, r2
   42c76:	62fb      	str	r3, [r7, #44]	; 0x2c
   42c78:	6aba      	ldr	r2, [r7, #40]	; 0x28
   42c7a:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   42c7c:	4053      	eors	r3, r2
   42c7e:	210c      	movs	r1, #12
   42c80:	4618      	mov	r0, r3
   42c82:	f7fd ff87 	bl	40b94 <rotr32>
   42c86:	4603      	mov	r3, r0
   42c88:	62bb      	str	r3, [r7, #40]	; 0x28
   42c8a:	697a      	ldr	r2, [r7, #20]
   42c8c:	6abb      	ldr	r3, [r7, #40]	; 0x28
   42c8e:	441a      	add	r2, r3
   42c90:	2302      	movs	r3, #2
   42c92:	009b      	lsls	r3, r3, #2
   42c94:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42c98:	440b      	add	r3, r1
   42c9a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42c9e:	4413      	add	r3, r2
   42ca0:	617b      	str	r3, [r7, #20]
   42ca2:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   42ca4:	697b      	ldr	r3, [r7, #20]
   42ca6:	4053      	eors	r3, r2
   42ca8:	2108      	movs	r1, #8
   42caa:	4618      	mov	r0, r3
   42cac:	f7fd ff72 	bl	40b94 <rotr32>
   42cb0:	4603      	mov	r3, r0
   42cb2:	643b      	str	r3, [r7, #64]	; 0x40
   42cb4:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   42cb6:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   42cb8:	4413      	add	r3, r2
   42cba:	62fb      	str	r3, [r7, #44]	; 0x2c
   42cbc:	6aba      	ldr	r2, [r7, #40]	; 0x28
   42cbe:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   42cc0:	4053      	eors	r3, r2
   42cc2:	2107      	movs	r1, #7
   42cc4:	4618      	mov	r0, r3
   42cc6:	f7fd ff65 	bl	40b94 <rotr32>
   42cca:	4603      	mov	r3, r0
   42ccc:	62bb      	str	r3, [r7, #40]	; 0x28
   42cce:	69ba      	ldr	r2, [r7, #24]
   42cd0:	69fb      	ldr	r3, [r7, #28]
   42cd2:	441a      	add	r2, r3
   42cd4:	2308      	movs	r3, #8
   42cd6:	009b      	lsls	r3, r3, #2
   42cd8:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42cdc:	440b      	add	r3, r1
   42cde:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42ce2:	4413      	add	r3, r2
   42ce4:	61bb      	str	r3, [r7, #24]
   42ce6:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   42ce8:	69bb      	ldr	r3, [r7, #24]
   42cea:	4053      	eors	r3, r2
   42cec:	2110      	movs	r1, #16
   42cee:	4618      	mov	r0, r3
   42cf0:	f7fd ff50 	bl	40b94 <rotr32>
   42cf4:	4603      	mov	r3, r0
   42cf6:	647b      	str	r3, [r7, #68]	; 0x44
   42cf8:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   42cfa:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   42cfc:	4413      	add	r3, r2
   42cfe:	633b      	str	r3, [r7, #48]	; 0x30
   42d00:	69fa      	ldr	r2, [r7, #28]
   42d02:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   42d04:	4053      	eors	r3, r2
   42d06:	210c      	movs	r1, #12
   42d08:	4618      	mov	r0, r3
   42d0a:	f7fd ff43 	bl	40b94 <rotr32>
   42d0e:	4603      	mov	r3, r0
   42d10:	61fb      	str	r3, [r7, #28]
   42d12:	69ba      	ldr	r2, [r7, #24]
   42d14:	69fb      	ldr	r3, [r7, #28]
   42d16:	441a      	add	r2, r3
   42d18:	230b      	movs	r3, #11
   42d1a:	009b      	lsls	r3, r3, #2
   42d1c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42d20:	440b      	add	r3, r1
   42d22:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42d26:	4413      	add	r3, r2
   42d28:	61bb      	str	r3, [r7, #24]
   42d2a:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   42d2c:	69bb      	ldr	r3, [r7, #24]
   42d2e:	4053      	eors	r3, r2
   42d30:	2108      	movs	r1, #8
   42d32:	4618      	mov	r0, r3
   42d34:	f7fd ff2e 	bl	40b94 <rotr32>
   42d38:	4603      	mov	r3, r0
   42d3a:	647b      	str	r3, [r7, #68]	; 0x44
   42d3c:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   42d3e:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   42d40:	4413      	add	r3, r2
   42d42:	633b      	str	r3, [r7, #48]	; 0x30
   42d44:	69fa      	ldr	r2, [r7, #28]
   42d46:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   42d48:	4053      	eors	r3, r2
   42d4a:	2107      	movs	r1, #7
   42d4c:	4618      	mov	r0, r3
   42d4e:	f7fd ff21 	bl	40b94 <rotr32>
   42d52:	4603      	mov	r3, r0
   42d54:	61fb      	str	r3, [r7, #28]
   42d56:	68fa      	ldr	r2, [r7, #12]
   42d58:	69fb      	ldr	r3, [r7, #28]
   42d5a:	441a      	add	r2, r3
   42d5c:	230d      	movs	r3, #13
   42d5e:	009b      	lsls	r3, r3, #2
   42d60:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42d64:	440b      	add	r3, r1
   42d66:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42d6a:	4413      	add	r3, r2
   42d6c:	60fb      	str	r3, [r7, #12]
   42d6e:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   42d70:	68fb      	ldr	r3, [r7, #12]
   42d72:	4053      	eors	r3, r2
   42d74:	2110      	movs	r1, #16
   42d76:	4618      	mov	r0, r3
   42d78:	f7fd ff0c 	bl	40b94 <rotr32>
   42d7c:	4603      	mov	r3, r0
   42d7e:	63fb      	str	r3, [r7, #60]	; 0x3c
   42d80:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   42d82:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   42d84:	4413      	add	r3, r2
   42d86:	62fb      	str	r3, [r7, #44]	; 0x2c
   42d88:	69fa      	ldr	r2, [r7, #28]
   42d8a:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   42d8c:	4053      	eors	r3, r2
   42d8e:	210c      	movs	r1, #12
   42d90:	4618      	mov	r0, r3
   42d92:	f7fd feff 	bl	40b94 <rotr32>
   42d96:	4603      	mov	r3, r0
   42d98:	61fb      	str	r3, [r7, #28]
   42d9a:	68fa      	ldr	r2, [r7, #12]
   42d9c:	69fb      	ldr	r3, [r7, #28]
   42d9e:	441a      	add	r2, r3
   42da0:	230b      	movs	r3, #11
   42da2:	009b      	lsls	r3, r3, #2
   42da4:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42da8:	440b      	add	r3, r1
   42daa:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42dae:	4413      	add	r3, r2
   42db0:	60fb      	str	r3, [r7, #12]
   42db2:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   42db4:	68fb      	ldr	r3, [r7, #12]
   42db6:	4053      	eors	r3, r2
   42db8:	2108      	movs	r1, #8
   42dba:	4618      	mov	r0, r3
   42dbc:	f7fd feea 	bl	40b94 <rotr32>
   42dc0:	4603      	mov	r3, r0
   42dc2:	63fb      	str	r3, [r7, #60]	; 0x3c
   42dc4:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   42dc6:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   42dc8:	4413      	add	r3, r2
   42dca:	62fb      	str	r3, [r7, #44]	; 0x2c
   42dcc:	69fa      	ldr	r2, [r7, #28]
   42dce:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   42dd0:	4053      	eors	r3, r2
   42dd2:	2107      	movs	r1, #7
   42dd4:	4618      	mov	r0, r3
   42dd6:	f7fd fedd 	bl	40b94 <rotr32>
   42dda:	4603      	mov	r3, r0
   42ddc:	61fb      	str	r3, [r7, #28]
   42dde:	693a      	ldr	r2, [r7, #16]
   42de0:	6a3b      	ldr	r3, [r7, #32]
   42de2:	441a      	add	r2, r3
   42de4:	2307      	movs	r3, #7
   42de6:	009b      	lsls	r3, r3, #2
   42de8:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42dec:	440b      	add	r3, r1
   42dee:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42df2:	4413      	add	r3, r2
   42df4:	613b      	str	r3, [r7, #16]
   42df6:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   42df8:	693b      	ldr	r3, [r7, #16]
   42dfa:	4053      	eors	r3, r2
   42dfc:	2110      	movs	r1, #16
   42dfe:	4618      	mov	r0, r3
   42e00:	f7fd fec8 	bl	40b94 <rotr32>
   42e04:	4603      	mov	r3, r0
   42e06:	643b      	str	r3, [r7, #64]	; 0x40
   42e08:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   42e0a:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   42e0c:	4413      	add	r3, r2
   42e0e:	633b      	str	r3, [r7, #48]	; 0x30
   42e10:	6a3a      	ldr	r2, [r7, #32]
   42e12:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   42e14:	4053      	eors	r3, r2
   42e16:	210c      	movs	r1, #12
   42e18:	4618      	mov	r0, r3
   42e1a:	f7fd febb 	bl	40b94 <rotr32>
   42e1e:	4603      	mov	r3, r0
   42e20:	623b      	str	r3, [r7, #32]
   42e22:	693a      	ldr	r2, [r7, #16]
   42e24:	6a3b      	ldr	r3, [r7, #32]
   42e26:	441a      	add	r2, r3
   42e28:	230e      	movs	r3, #14
   42e2a:	009b      	lsls	r3, r3, #2
   42e2c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42e30:	440b      	add	r3, r1
   42e32:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42e36:	4413      	add	r3, r2
   42e38:	613b      	str	r3, [r7, #16]
   42e3a:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   42e3c:	693b      	ldr	r3, [r7, #16]
   42e3e:	4053      	eors	r3, r2
   42e40:	2108      	movs	r1, #8
   42e42:	4618      	mov	r0, r3
   42e44:	f7fd fea6 	bl	40b94 <rotr32>
   42e48:	4603      	mov	r3, r0
   42e4a:	643b      	str	r3, [r7, #64]	; 0x40
   42e4c:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   42e4e:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   42e50:	4413      	add	r3, r2
   42e52:	633b      	str	r3, [r7, #48]	; 0x30
   42e54:	6a3a      	ldr	r2, [r7, #32]
   42e56:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   42e58:	4053      	eors	r3, r2
   42e5a:	2107      	movs	r1, #7
   42e5c:	4618      	mov	r0, r3
   42e5e:	f7fd fe99 	bl	40b94 <rotr32>
   42e62:	4603      	mov	r3, r0
   42e64:	623b      	str	r3, [r7, #32]
   42e66:	697a      	ldr	r2, [r7, #20]
   42e68:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   42e6a:	441a      	add	r2, r3
   42e6c:	230c      	movs	r3, #12
   42e6e:	009b      	lsls	r3, r3, #2
   42e70:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42e74:	440b      	add	r3, r1
   42e76:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42e7a:	4413      	add	r3, r2
   42e7c:	617b      	str	r3, [r7, #20]
   42e7e:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   42e80:	697b      	ldr	r3, [r7, #20]
   42e82:	4053      	eors	r3, r2
   42e84:	2110      	movs	r1, #16
   42e86:	4618      	mov	r0, r3
   42e88:	f7fd fe84 	bl	40b94 <rotr32>
   42e8c:	4603      	mov	r3, r0
   42e8e:	647b      	str	r3, [r7, #68]	; 0x44
   42e90:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   42e92:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   42e94:	4413      	add	r3, r2
   42e96:	637b      	str	r3, [r7, #52]	; 0x34
   42e98:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   42e9a:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   42e9c:	4053      	eors	r3, r2
   42e9e:	210c      	movs	r1, #12
   42ea0:	4618      	mov	r0, r3
   42ea2:	f7fd fe77 	bl	40b94 <rotr32>
   42ea6:	4603      	mov	r3, r0
   42ea8:	627b      	str	r3, [r7, #36]	; 0x24
   42eaa:	697a      	ldr	r2, [r7, #20]
   42eac:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   42eae:	441a      	add	r2, r3
   42eb0:	2301      	movs	r3, #1
   42eb2:	009b      	lsls	r3, r3, #2
   42eb4:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42eb8:	440b      	add	r3, r1
   42eba:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42ebe:	4413      	add	r3, r2
   42ec0:	617b      	str	r3, [r7, #20]
   42ec2:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   42ec4:	697b      	ldr	r3, [r7, #20]
   42ec6:	4053      	eors	r3, r2
   42ec8:	2108      	movs	r1, #8
   42eca:	4618      	mov	r0, r3
   42ecc:	f7fd fe62 	bl	40b94 <rotr32>
   42ed0:	4603      	mov	r3, r0
   42ed2:	647b      	str	r3, [r7, #68]	; 0x44
   42ed4:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   42ed6:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   42ed8:	4413      	add	r3, r2
   42eda:	637b      	str	r3, [r7, #52]	; 0x34
   42edc:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   42ede:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   42ee0:	4053      	eors	r3, r2
   42ee2:	2107      	movs	r1, #7
   42ee4:	4618      	mov	r0, r3
   42ee6:	f7fd fe55 	bl	40b94 <rotr32>
   42eea:	4603      	mov	r3, r0
   42eec:	627b      	str	r3, [r7, #36]	; 0x24
   42eee:	69ba      	ldr	r2, [r7, #24]
   42ef0:	6abb      	ldr	r3, [r7, #40]	; 0x28
   42ef2:	441a      	add	r2, r3
   42ef4:	2303      	movs	r3, #3
   42ef6:	009b      	lsls	r3, r3, #2
   42ef8:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42efc:	440b      	add	r3, r1
   42efe:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42f02:	4413      	add	r3, r2
   42f04:	61bb      	str	r3, [r7, #24]
   42f06:	6cba      	ldr	r2, [r7, #72]	; 0x48
   42f08:	69bb      	ldr	r3, [r7, #24]
   42f0a:	4053      	eors	r3, r2
   42f0c:	2110      	movs	r1, #16
   42f0e:	4618      	mov	r0, r3
   42f10:	f7fd fe40 	bl	40b94 <rotr32>
   42f14:	4603      	mov	r3, r0
   42f16:	64bb      	str	r3, [r7, #72]	; 0x48
   42f18:	6bba      	ldr	r2, [r7, #56]	; 0x38
   42f1a:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   42f1c:	4413      	add	r3, r2
   42f1e:	63bb      	str	r3, [r7, #56]	; 0x38
   42f20:	6aba      	ldr	r2, [r7, #40]	; 0x28
   42f22:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   42f24:	4053      	eors	r3, r2
   42f26:	210c      	movs	r1, #12
   42f28:	4618      	mov	r0, r3
   42f2a:	f7fd fe33 	bl	40b94 <rotr32>
   42f2e:	4603      	mov	r3, r0
   42f30:	62bb      	str	r3, [r7, #40]	; 0x28
   42f32:	69ba      	ldr	r2, [r7, #24]
   42f34:	6abb      	ldr	r3, [r7, #40]	; 0x28
   42f36:	441a      	add	r2, r3
   42f38:	2309      	movs	r3, #9
   42f3a:	009b      	lsls	r3, r3, #2
   42f3c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42f40:	440b      	add	r3, r1
   42f42:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42f46:	4413      	add	r3, r2
   42f48:	61bb      	str	r3, [r7, #24]
   42f4a:	6cba      	ldr	r2, [r7, #72]	; 0x48
   42f4c:	69bb      	ldr	r3, [r7, #24]
   42f4e:	4053      	eors	r3, r2
   42f50:	2108      	movs	r1, #8
   42f52:	4618      	mov	r0, r3
   42f54:	f7fd fe1e 	bl	40b94 <rotr32>
   42f58:	4603      	mov	r3, r0
   42f5a:	64bb      	str	r3, [r7, #72]	; 0x48
   42f5c:	6bba      	ldr	r2, [r7, #56]	; 0x38
   42f5e:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   42f60:	4413      	add	r3, r2
   42f62:	63bb      	str	r3, [r7, #56]	; 0x38
   42f64:	6aba      	ldr	r2, [r7, #40]	; 0x28
   42f66:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   42f68:	4053      	eors	r3, r2
   42f6a:	2107      	movs	r1, #7
   42f6c:	4618      	mov	r0, r3
   42f6e:	f7fd fe11 	bl	40b94 <rotr32>
   42f72:	4603      	mov	r3, r0
   42f74:	62bb      	str	r3, [r7, #40]	; 0x28
   42f76:	68fa      	ldr	r2, [r7, #12]
   42f78:	6a3b      	ldr	r3, [r7, #32]
   42f7a:	441a      	add	r2, r3
   42f7c:	2305      	movs	r3, #5
   42f7e:	009b      	lsls	r3, r3, #2
   42f80:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42f84:	440b      	add	r3, r1
   42f86:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42f8a:	4413      	add	r3, r2
   42f8c:	60fb      	str	r3, [r7, #12]
   42f8e:	6cba      	ldr	r2, [r7, #72]	; 0x48
   42f90:	68fb      	ldr	r3, [r7, #12]
   42f92:	4053      	eors	r3, r2
   42f94:	2110      	movs	r1, #16
   42f96:	4618      	mov	r0, r3
   42f98:	f7fd fdfc 	bl	40b94 <rotr32>
   42f9c:	4603      	mov	r3, r0
   42f9e:	64bb      	str	r3, [r7, #72]	; 0x48
   42fa0:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   42fa2:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   42fa4:	4413      	add	r3, r2
   42fa6:	637b      	str	r3, [r7, #52]	; 0x34
   42fa8:	6a3a      	ldr	r2, [r7, #32]
   42faa:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   42fac:	4053      	eors	r3, r2
   42fae:	210c      	movs	r1, #12
   42fb0:	4618      	mov	r0, r3
   42fb2:	f7fd fdef 	bl	40b94 <rotr32>
   42fb6:	4603      	mov	r3, r0
   42fb8:	623b      	str	r3, [r7, #32]
   42fba:	68fa      	ldr	r2, [r7, #12]
   42fbc:	6a3b      	ldr	r3, [r7, #32]
   42fbe:	441a      	add	r2, r3
   42fc0:	2300      	movs	r3, #0
   42fc2:	009b      	lsls	r3, r3, #2
   42fc4:	f107 0190 	add.w	r1, r7, #144	; 0x90
   42fc8:	440b      	add	r3, r1
   42fca:	f853 3c44 	ldr.w	r3, [r3, #-68]
   42fce:	4413      	add	r3, r2
   42fd0:	60fb      	str	r3, [r7, #12]
   42fd2:	6cba      	ldr	r2, [r7, #72]	; 0x48
   42fd4:	68fb      	ldr	r3, [r7, #12]
   42fd6:	4053      	eors	r3, r2
   42fd8:	2108      	movs	r1, #8
   42fda:	4618      	mov	r0, r3
   42fdc:	f7fd fdda 	bl	40b94 <rotr32>
   42fe0:	4603      	mov	r3, r0
   42fe2:	64bb      	str	r3, [r7, #72]	; 0x48
   42fe4:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   42fe6:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   42fe8:	4413      	add	r3, r2
   42fea:	637b      	str	r3, [r7, #52]	; 0x34
   42fec:	6a3a      	ldr	r2, [r7, #32]
   42fee:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   42ff0:	4053      	eors	r3, r2
   42ff2:	2107      	movs	r1, #7
   42ff4:	4618      	mov	r0, r3
   42ff6:	f7fd fdcd 	bl	40b94 <rotr32>
   42ffa:	4603      	mov	r3, r0
   42ffc:	623b      	str	r3, [r7, #32]
   42ffe:	693a      	ldr	r2, [r7, #16]
   43000:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   43002:	441a      	add	r2, r3
   43004:	230f      	movs	r3, #15
   43006:	009b      	lsls	r3, r3, #2
   43008:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4300c:	440b      	add	r3, r1
   4300e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   43012:	4413      	add	r3, r2
   43014:	613b      	str	r3, [r7, #16]
   43016:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   43018:	693b      	ldr	r3, [r7, #16]
   4301a:	4053      	eors	r3, r2
   4301c:	2110      	movs	r1, #16
   4301e:	4618      	mov	r0, r3
   43020:	f7fd fdb8 	bl	40b94 <rotr32>
   43024:	4603      	mov	r3, r0
   43026:	63fb      	str	r3, [r7, #60]	; 0x3c
   43028:	6bba      	ldr	r2, [r7, #56]	; 0x38
   4302a:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   4302c:	4413      	add	r3, r2
   4302e:	63bb      	str	r3, [r7, #56]	; 0x38
   43030:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   43032:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   43034:	4053      	eors	r3, r2
   43036:	210c      	movs	r1, #12
   43038:	4618      	mov	r0, r3
   4303a:	f7fd fdab 	bl	40b94 <rotr32>
   4303e:	4603      	mov	r3, r0
   43040:	627b      	str	r3, [r7, #36]	; 0x24
   43042:	693a      	ldr	r2, [r7, #16]
   43044:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   43046:	441a      	add	r2, r3
   43048:	2304      	movs	r3, #4
   4304a:	009b      	lsls	r3, r3, #2
   4304c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   43050:	440b      	add	r3, r1
   43052:	f853 3c44 	ldr.w	r3, [r3, #-68]
   43056:	4413      	add	r3, r2
   43058:	613b      	str	r3, [r7, #16]
   4305a:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   4305c:	693b      	ldr	r3, [r7, #16]
   4305e:	4053      	eors	r3, r2
   43060:	2108      	movs	r1, #8
   43062:	4618      	mov	r0, r3
   43064:	f7fd fd96 	bl	40b94 <rotr32>
   43068:	4603      	mov	r3, r0
   4306a:	63fb      	str	r3, [r7, #60]	; 0x3c
   4306c:	6bba      	ldr	r2, [r7, #56]	; 0x38
   4306e:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   43070:	4413      	add	r3, r2
   43072:	63bb      	str	r3, [r7, #56]	; 0x38
   43074:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   43076:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   43078:	4053      	eors	r3, r2
   4307a:	2107      	movs	r1, #7
   4307c:	4618      	mov	r0, r3
   4307e:	f7fd fd89 	bl	40b94 <rotr32>
   43082:	4603      	mov	r3, r0
   43084:	627b      	str	r3, [r7, #36]	; 0x24
   43086:	697a      	ldr	r2, [r7, #20]
   43088:	6abb      	ldr	r3, [r7, #40]	; 0x28
   4308a:	441a      	add	r2, r3
   4308c:	2308      	movs	r3, #8
   4308e:	009b      	lsls	r3, r3, #2
   43090:	f107 0190 	add.w	r1, r7, #144	; 0x90
   43094:	440b      	add	r3, r1
   43096:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4309a:	4413      	add	r3, r2
   4309c:	617b      	str	r3, [r7, #20]
   4309e:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   430a0:	697b      	ldr	r3, [r7, #20]
   430a2:	4053      	eors	r3, r2
   430a4:	2110      	movs	r1, #16
   430a6:	4618      	mov	r0, r3
   430a8:	f7fd fd74 	bl	40b94 <rotr32>
   430ac:	4603      	mov	r3, r0
   430ae:	643b      	str	r3, [r7, #64]	; 0x40
   430b0:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   430b2:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   430b4:	4413      	add	r3, r2
   430b6:	62fb      	str	r3, [r7, #44]	; 0x2c
   430b8:	6aba      	ldr	r2, [r7, #40]	; 0x28
   430ba:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   430bc:	4053      	eors	r3, r2
   430be:	210c      	movs	r1, #12
   430c0:	4618      	mov	r0, r3
   430c2:	f7fd fd67 	bl	40b94 <rotr32>
   430c6:	4603      	mov	r3, r0
   430c8:	62bb      	str	r3, [r7, #40]	; 0x28
   430ca:	697a      	ldr	r2, [r7, #20]
   430cc:	6abb      	ldr	r3, [r7, #40]	; 0x28
   430ce:	441a      	add	r2, r3
   430d0:	2306      	movs	r3, #6
   430d2:	009b      	lsls	r3, r3, #2
   430d4:	f107 0190 	add.w	r1, r7, #144	; 0x90
   430d8:	440b      	add	r3, r1
   430da:	f853 3c44 	ldr.w	r3, [r3, #-68]
   430de:	4413      	add	r3, r2
   430e0:	617b      	str	r3, [r7, #20]
   430e2:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   430e4:	697b      	ldr	r3, [r7, #20]
   430e6:	4053      	eors	r3, r2
   430e8:	2108      	movs	r1, #8
   430ea:	4618      	mov	r0, r3
   430ec:	f7fd fd52 	bl	40b94 <rotr32>
   430f0:	4603      	mov	r3, r0
   430f2:	643b      	str	r3, [r7, #64]	; 0x40
   430f4:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   430f6:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   430f8:	4413      	add	r3, r2
   430fa:	62fb      	str	r3, [r7, #44]	; 0x2c
   430fc:	6aba      	ldr	r2, [r7, #40]	; 0x28
   430fe:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   43100:	4053      	eors	r3, r2
   43102:	2107      	movs	r1, #7
   43104:	4618      	mov	r0, r3
   43106:	f7fd fd45 	bl	40b94 <rotr32>
   4310a:	4603      	mov	r3, r0
   4310c:	62bb      	str	r3, [r7, #40]	; 0x28
   4310e:	69ba      	ldr	r2, [r7, #24]
   43110:	69fb      	ldr	r3, [r7, #28]
   43112:	441a      	add	r2, r3
   43114:	2302      	movs	r3, #2
   43116:	009b      	lsls	r3, r3, #2
   43118:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4311c:	440b      	add	r3, r1
   4311e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   43122:	4413      	add	r3, r2
   43124:	61bb      	str	r3, [r7, #24]
   43126:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   43128:	69bb      	ldr	r3, [r7, #24]
   4312a:	4053      	eors	r3, r2
   4312c:	2110      	movs	r1, #16
   4312e:	4618      	mov	r0, r3
   43130:	f7fd fd30 	bl	40b94 <rotr32>
   43134:	4603      	mov	r3, r0
   43136:	647b      	str	r3, [r7, #68]	; 0x44
   43138:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   4313a:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   4313c:	4413      	add	r3, r2
   4313e:	633b      	str	r3, [r7, #48]	; 0x30
   43140:	69fa      	ldr	r2, [r7, #28]
   43142:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   43144:	4053      	eors	r3, r2
   43146:	210c      	movs	r1, #12
   43148:	4618      	mov	r0, r3
   4314a:	f7fd fd23 	bl	40b94 <rotr32>
   4314e:	4603      	mov	r3, r0
   43150:	61fb      	str	r3, [r7, #28]
   43152:	69ba      	ldr	r2, [r7, #24]
   43154:	69fb      	ldr	r3, [r7, #28]
   43156:	441a      	add	r2, r3
   43158:	230a      	movs	r3, #10
   4315a:	009b      	lsls	r3, r3, #2
   4315c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   43160:	440b      	add	r3, r1
   43162:	f853 3c44 	ldr.w	r3, [r3, #-68]
   43166:	4413      	add	r3, r2
   43168:	61bb      	str	r3, [r7, #24]
   4316a:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   4316c:	69bb      	ldr	r3, [r7, #24]
   4316e:	4053      	eors	r3, r2
   43170:	2108      	movs	r1, #8
   43172:	4618      	mov	r0, r3
   43174:	f7fd fd0e 	bl	40b94 <rotr32>
   43178:	4603      	mov	r3, r0
   4317a:	647b      	str	r3, [r7, #68]	; 0x44
   4317c:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   4317e:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   43180:	4413      	add	r3, r2
   43182:	633b      	str	r3, [r7, #48]	; 0x30
   43184:	69fa      	ldr	r2, [r7, #28]
   43186:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   43188:	4053      	eors	r3, r2
   4318a:	2107      	movs	r1, #7
   4318c:	4618      	mov	r0, r3
   4318e:	f7fd fd01 	bl	40b94 <rotr32>
   43192:	4603      	mov	r3, r0
   43194:	61fb      	str	r3, [r7, #28]
   43196:	68fa      	ldr	r2, [r7, #12]
   43198:	69fb      	ldr	r3, [r7, #28]
   4319a:	441a      	add	r2, r3
   4319c:	2306      	movs	r3, #6
   4319e:	009b      	lsls	r3, r3, #2
   431a0:	f107 0190 	add.w	r1, r7, #144	; 0x90
   431a4:	440b      	add	r3, r1
   431a6:	f853 3c44 	ldr.w	r3, [r3, #-68]
   431aa:	4413      	add	r3, r2
   431ac:	60fb      	str	r3, [r7, #12]
   431ae:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   431b0:	68fb      	ldr	r3, [r7, #12]
   431b2:	4053      	eors	r3, r2
   431b4:	2110      	movs	r1, #16
   431b6:	4618      	mov	r0, r3
   431b8:	f7fd fcec 	bl	40b94 <rotr32>
   431bc:	4603      	mov	r3, r0
   431be:	63fb      	str	r3, [r7, #60]	; 0x3c
   431c0:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   431c2:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   431c4:	4413      	add	r3, r2
   431c6:	62fb      	str	r3, [r7, #44]	; 0x2c
   431c8:	69fa      	ldr	r2, [r7, #28]
   431ca:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   431cc:	4053      	eors	r3, r2
   431ce:	210c      	movs	r1, #12
   431d0:	4618      	mov	r0, r3
   431d2:	f7fd fcdf 	bl	40b94 <rotr32>
   431d6:	4603      	mov	r3, r0
   431d8:	61fb      	str	r3, [r7, #28]
   431da:	68fa      	ldr	r2, [r7, #12]
   431dc:	69fb      	ldr	r3, [r7, #28]
   431de:	441a      	add	r2, r3
   431e0:	230f      	movs	r3, #15
   431e2:	009b      	lsls	r3, r3, #2
   431e4:	f107 0190 	add.w	r1, r7, #144	; 0x90
   431e8:	440b      	add	r3, r1
   431ea:	f853 3c44 	ldr.w	r3, [r3, #-68]
   431ee:	4413      	add	r3, r2
   431f0:	60fb      	str	r3, [r7, #12]
   431f2:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   431f4:	68fb      	ldr	r3, [r7, #12]
   431f6:	4053      	eors	r3, r2
   431f8:	2108      	movs	r1, #8
   431fa:	4618      	mov	r0, r3
   431fc:	f7fd fcca 	bl	40b94 <rotr32>
   43200:	4603      	mov	r3, r0
   43202:	63fb      	str	r3, [r7, #60]	; 0x3c
   43204:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   43206:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   43208:	4413      	add	r3, r2
   4320a:	62fb      	str	r3, [r7, #44]	; 0x2c
   4320c:	69fa      	ldr	r2, [r7, #28]
   4320e:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   43210:	4053      	eors	r3, r2
   43212:	2107      	movs	r1, #7
   43214:	4618      	mov	r0, r3
   43216:	f7fd fcbd 	bl	40b94 <rotr32>
   4321a:	4603      	mov	r3, r0
   4321c:	61fb      	str	r3, [r7, #28]
   4321e:	693a      	ldr	r2, [r7, #16]
   43220:	6a3b      	ldr	r3, [r7, #32]
   43222:	441a      	add	r2, r3
   43224:	230e      	movs	r3, #14
   43226:	009b      	lsls	r3, r3, #2
   43228:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4322c:	440b      	add	r3, r1
   4322e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   43232:	4413      	add	r3, r2
   43234:	613b      	str	r3, [r7, #16]
   43236:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   43238:	693b      	ldr	r3, [r7, #16]
   4323a:	4053      	eors	r3, r2
   4323c:	2110      	movs	r1, #16
   4323e:	4618      	mov	r0, r3
   43240:	f7fd fca8 	bl	40b94 <rotr32>
   43244:	4603      	mov	r3, r0
   43246:	643b      	str	r3, [r7, #64]	; 0x40
   43248:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   4324a:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   4324c:	4413      	add	r3, r2
   4324e:	633b      	str	r3, [r7, #48]	; 0x30
   43250:	6a3a      	ldr	r2, [r7, #32]
   43252:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   43254:	4053      	eors	r3, r2
   43256:	210c      	movs	r1, #12
   43258:	4618      	mov	r0, r3
   4325a:	f7fd fc9b 	bl	40b94 <rotr32>
   4325e:	4603      	mov	r3, r0
   43260:	623b      	str	r3, [r7, #32]
   43262:	693a      	ldr	r2, [r7, #16]
   43264:	6a3b      	ldr	r3, [r7, #32]
   43266:	441a      	add	r2, r3
   43268:	2309      	movs	r3, #9
   4326a:	009b      	lsls	r3, r3, #2
   4326c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   43270:	440b      	add	r3, r1
   43272:	f853 3c44 	ldr.w	r3, [r3, #-68]
   43276:	4413      	add	r3, r2
   43278:	613b      	str	r3, [r7, #16]
   4327a:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   4327c:	693b      	ldr	r3, [r7, #16]
   4327e:	4053      	eors	r3, r2
   43280:	2108      	movs	r1, #8
   43282:	4618      	mov	r0, r3
   43284:	f7fd fc86 	bl	40b94 <rotr32>
   43288:	4603      	mov	r3, r0
   4328a:	643b      	str	r3, [r7, #64]	; 0x40
   4328c:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   4328e:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   43290:	4413      	add	r3, r2
   43292:	633b      	str	r3, [r7, #48]	; 0x30
   43294:	6a3a      	ldr	r2, [r7, #32]
   43296:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   43298:	4053      	eors	r3, r2
   4329a:	2107      	movs	r1, #7
   4329c:	4618      	mov	r0, r3
   4329e:	f7fd fc79 	bl	40b94 <rotr32>
   432a2:	4603      	mov	r3, r0
   432a4:	623b      	str	r3, [r7, #32]
   432a6:	697a      	ldr	r2, [r7, #20]
   432a8:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   432aa:	441a      	add	r2, r3
   432ac:	230b      	movs	r3, #11
   432ae:	009b      	lsls	r3, r3, #2
   432b0:	f107 0190 	add.w	r1, r7, #144	; 0x90
   432b4:	440b      	add	r3, r1
   432b6:	f853 3c44 	ldr.w	r3, [r3, #-68]
   432ba:	4413      	add	r3, r2
   432bc:	617b      	str	r3, [r7, #20]
   432be:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   432c0:	697b      	ldr	r3, [r7, #20]
   432c2:	4053      	eors	r3, r2
   432c4:	2110      	movs	r1, #16
   432c6:	4618      	mov	r0, r3
   432c8:	f7fd fc64 	bl	40b94 <rotr32>
   432cc:	4603      	mov	r3, r0
   432ce:	647b      	str	r3, [r7, #68]	; 0x44
   432d0:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   432d2:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   432d4:	4413      	add	r3, r2
   432d6:	637b      	str	r3, [r7, #52]	; 0x34
   432d8:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   432da:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   432dc:	4053      	eors	r3, r2
   432de:	210c      	movs	r1, #12
   432e0:	4618      	mov	r0, r3
   432e2:	f7fd fc57 	bl	40b94 <rotr32>
   432e6:	4603      	mov	r3, r0
   432e8:	627b      	str	r3, [r7, #36]	; 0x24
   432ea:	697a      	ldr	r2, [r7, #20]
   432ec:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   432ee:	441a      	add	r2, r3
   432f0:	2303      	movs	r3, #3
   432f2:	009b      	lsls	r3, r3, #2
   432f4:	f107 0190 	add.w	r1, r7, #144	; 0x90
   432f8:	440b      	add	r3, r1
   432fa:	f853 3c44 	ldr.w	r3, [r3, #-68]
   432fe:	4413      	add	r3, r2
   43300:	617b      	str	r3, [r7, #20]
   43302:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   43304:	697b      	ldr	r3, [r7, #20]
   43306:	4053      	eors	r3, r2
   43308:	2108      	movs	r1, #8
   4330a:	4618      	mov	r0, r3
   4330c:	f7fd fc42 	bl	40b94 <rotr32>
   43310:	4603      	mov	r3, r0
   43312:	647b      	str	r3, [r7, #68]	; 0x44
   43314:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   43316:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   43318:	4413      	add	r3, r2
   4331a:	637b      	str	r3, [r7, #52]	; 0x34
   4331c:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   4331e:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   43320:	4053      	eors	r3, r2
   43322:	2107      	movs	r1, #7
   43324:	4618      	mov	r0, r3
   43326:	f7fd fc35 	bl	40b94 <rotr32>
   4332a:	4603      	mov	r3, r0
   4332c:	627b      	str	r3, [r7, #36]	; 0x24
   4332e:	69ba      	ldr	r2, [r7, #24]
   43330:	6abb      	ldr	r3, [r7, #40]	; 0x28
   43332:	441a      	add	r2, r3
   43334:	2300      	movs	r3, #0
   43336:	009b      	lsls	r3, r3, #2
   43338:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4333c:	440b      	add	r3, r1
   4333e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   43342:	4413      	add	r3, r2
   43344:	61bb      	str	r3, [r7, #24]
   43346:	6cba      	ldr	r2, [r7, #72]	; 0x48
   43348:	69bb      	ldr	r3, [r7, #24]
   4334a:	4053      	eors	r3, r2
   4334c:	2110      	movs	r1, #16
   4334e:	4618      	mov	r0, r3
   43350:	f7fd fc20 	bl	40b94 <rotr32>
   43354:	4603      	mov	r3, r0
   43356:	64bb      	str	r3, [r7, #72]	; 0x48
   43358:	6bba      	ldr	r2, [r7, #56]	; 0x38
   4335a:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   4335c:	4413      	add	r3, r2
   4335e:	63bb      	str	r3, [r7, #56]	; 0x38
   43360:	6aba      	ldr	r2, [r7, #40]	; 0x28
   43362:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   43364:	4053      	eors	r3, r2
   43366:	210c      	movs	r1, #12
   43368:	4618      	mov	r0, r3
   4336a:	f7fd fc13 	bl	40b94 <rotr32>
   4336e:	4603      	mov	r3, r0
   43370:	62bb      	str	r3, [r7, #40]	; 0x28
   43372:	69ba      	ldr	r2, [r7, #24]
   43374:	6abb      	ldr	r3, [r7, #40]	; 0x28
   43376:	441a      	add	r2, r3
   43378:	2308      	movs	r3, #8
   4337a:	009b      	lsls	r3, r3, #2
   4337c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   43380:	440b      	add	r3, r1
   43382:	f853 3c44 	ldr.w	r3, [r3, #-68]
   43386:	4413      	add	r3, r2
   43388:	61bb      	str	r3, [r7, #24]
   4338a:	6cba      	ldr	r2, [r7, #72]	; 0x48
   4338c:	69bb      	ldr	r3, [r7, #24]
   4338e:	4053      	eors	r3, r2
   43390:	2108      	movs	r1, #8
   43392:	4618      	mov	r0, r3
   43394:	f7fd fbfe 	bl	40b94 <rotr32>
   43398:	4603      	mov	r3, r0
   4339a:	64bb      	str	r3, [r7, #72]	; 0x48
   4339c:	6bba      	ldr	r2, [r7, #56]	; 0x38
   4339e:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   433a0:	4413      	add	r3, r2
   433a2:	63bb      	str	r3, [r7, #56]	; 0x38
   433a4:	6aba      	ldr	r2, [r7, #40]	; 0x28
   433a6:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   433a8:	4053      	eors	r3, r2
   433aa:	2107      	movs	r1, #7
   433ac:	4618      	mov	r0, r3
   433ae:	f7fd fbf1 	bl	40b94 <rotr32>
   433b2:	4603      	mov	r3, r0
   433b4:	62bb      	str	r3, [r7, #40]	; 0x28
   433b6:	68fa      	ldr	r2, [r7, #12]
   433b8:	6a3b      	ldr	r3, [r7, #32]
   433ba:	441a      	add	r2, r3
   433bc:	230c      	movs	r3, #12
   433be:	009b      	lsls	r3, r3, #2
   433c0:	f107 0190 	add.w	r1, r7, #144	; 0x90
   433c4:	440b      	add	r3, r1
   433c6:	f853 3c44 	ldr.w	r3, [r3, #-68]
   433ca:	4413      	add	r3, r2
   433cc:	60fb      	str	r3, [r7, #12]
   433ce:	6cba      	ldr	r2, [r7, #72]	; 0x48
   433d0:	68fb      	ldr	r3, [r7, #12]
   433d2:	4053      	eors	r3, r2
   433d4:	2110      	movs	r1, #16
   433d6:	4618      	mov	r0, r3
   433d8:	f7fd fbdc 	bl	40b94 <rotr32>
   433dc:	4603      	mov	r3, r0
   433de:	64bb      	str	r3, [r7, #72]	; 0x48
   433e0:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   433e2:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   433e4:	4413      	add	r3, r2
   433e6:	637b      	str	r3, [r7, #52]	; 0x34
   433e8:	6a3a      	ldr	r2, [r7, #32]
   433ea:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   433ec:	4053      	eors	r3, r2
   433ee:	210c      	movs	r1, #12
   433f0:	4618      	mov	r0, r3
   433f2:	f7fd fbcf 	bl	40b94 <rotr32>
   433f6:	4603      	mov	r3, r0
   433f8:	623b      	str	r3, [r7, #32]
   433fa:	68fa      	ldr	r2, [r7, #12]
   433fc:	6a3b      	ldr	r3, [r7, #32]
   433fe:	441a      	add	r2, r3
   43400:	2302      	movs	r3, #2
   43402:	009b      	lsls	r3, r3, #2
   43404:	f107 0190 	add.w	r1, r7, #144	; 0x90
   43408:	440b      	add	r3, r1
   4340a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4340e:	4413      	add	r3, r2
   43410:	60fb      	str	r3, [r7, #12]
   43412:	6cba      	ldr	r2, [r7, #72]	; 0x48
   43414:	68fb      	ldr	r3, [r7, #12]
   43416:	4053      	eors	r3, r2
   43418:	2108      	movs	r1, #8
   4341a:	4618      	mov	r0, r3
   4341c:	f7fd fbba 	bl	40b94 <rotr32>
   43420:	4603      	mov	r3, r0
   43422:	64bb      	str	r3, [r7, #72]	; 0x48
   43424:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   43426:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   43428:	4413      	add	r3, r2
   4342a:	637b      	str	r3, [r7, #52]	; 0x34
   4342c:	6a3a      	ldr	r2, [r7, #32]
   4342e:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   43430:	4053      	eors	r3, r2
   43432:	2107      	movs	r1, #7
   43434:	4618      	mov	r0, r3
   43436:	f7fd fbad 	bl	40b94 <rotr32>
   4343a:	4603      	mov	r3, r0
   4343c:	623b      	str	r3, [r7, #32]
   4343e:	693a      	ldr	r2, [r7, #16]
   43440:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   43442:	441a      	add	r2, r3
   43444:	230d      	movs	r3, #13
   43446:	009b      	lsls	r3, r3, #2
   43448:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4344c:	440b      	add	r3, r1
   4344e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   43452:	4413      	add	r3, r2
   43454:	613b      	str	r3, [r7, #16]
   43456:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   43458:	693b      	ldr	r3, [r7, #16]
   4345a:	4053      	eors	r3, r2
   4345c:	2110      	movs	r1, #16
   4345e:	4618      	mov	r0, r3
   43460:	f7fd fb98 	bl	40b94 <rotr32>
   43464:	4603      	mov	r3, r0
   43466:	63fb      	str	r3, [r7, #60]	; 0x3c
   43468:	6bba      	ldr	r2, [r7, #56]	; 0x38
   4346a:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   4346c:	4413      	add	r3, r2
   4346e:	63bb      	str	r3, [r7, #56]	; 0x38
   43470:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   43472:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   43474:	4053      	eors	r3, r2
   43476:	210c      	movs	r1, #12
   43478:	4618      	mov	r0, r3
   4347a:	f7fd fb8b 	bl	40b94 <rotr32>
   4347e:	4603      	mov	r3, r0
   43480:	627b      	str	r3, [r7, #36]	; 0x24
   43482:	693a      	ldr	r2, [r7, #16]
   43484:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   43486:	441a      	add	r2, r3
   43488:	2307      	movs	r3, #7
   4348a:	009b      	lsls	r3, r3, #2
   4348c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   43490:	440b      	add	r3, r1
   43492:	f853 3c44 	ldr.w	r3, [r3, #-68]
   43496:	4413      	add	r3, r2
   43498:	613b      	str	r3, [r7, #16]
   4349a:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   4349c:	693b      	ldr	r3, [r7, #16]
   4349e:	4053      	eors	r3, r2
   434a0:	2108      	movs	r1, #8
   434a2:	4618      	mov	r0, r3
   434a4:	f7fd fb76 	bl	40b94 <rotr32>
   434a8:	4603      	mov	r3, r0
   434aa:	63fb      	str	r3, [r7, #60]	; 0x3c
   434ac:	6bba      	ldr	r2, [r7, #56]	; 0x38
   434ae:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   434b0:	4413      	add	r3, r2
   434b2:	63bb      	str	r3, [r7, #56]	; 0x38
   434b4:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   434b6:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   434b8:	4053      	eors	r3, r2
   434ba:	2107      	movs	r1, #7
   434bc:	4618      	mov	r0, r3
   434be:	f7fd fb69 	bl	40b94 <rotr32>
   434c2:	4603      	mov	r3, r0
   434c4:	627b      	str	r3, [r7, #36]	; 0x24
   434c6:	697a      	ldr	r2, [r7, #20]
   434c8:	6abb      	ldr	r3, [r7, #40]	; 0x28
   434ca:	441a      	add	r2, r3
   434cc:	2301      	movs	r3, #1
   434ce:	009b      	lsls	r3, r3, #2
   434d0:	f107 0190 	add.w	r1, r7, #144	; 0x90
   434d4:	440b      	add	r3, r1
   434d6:	f853 3c44 	ldr.w	r3, [r3, #-68]
   434da:	4413      	add	r3, r2
   434dc:	617b      	str	r3, [r7, #20]
   434de:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   434e0:	697b      	ldr	r3, [r7, #20]
   434e2:	4053      	eors	r3, r2
   434e4:	2110      	movs	r1, #16
   434e6:	4618      	mov	r0, r3
   434e8:	f7fd fb54 	bl	40b94 <rotr32>
   434ec:	4603      	mov	r3, r0
   434ee:	643b      	str	r3, [r7, #64]	; 0x40
   434f0:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   434f2:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   434f4:	4413      	add	r3, r2
   434f6:	62fb      	str	r3, [r7, #44]	; 0x2c
   434f8:	6aba      	ldr	r2, [r7, #40]	; 0x28
   434fa:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   434fc:	4053      	eors	r3, r2
   434fe:	210c      	movs	r1, #12
   43500:	4618      	mov	r0, r3
   43502:	f7fd fb47 	bl	40b94 <rotr32>
   43506:	4603      	mov	r3, r0
   43508:	62bb      	str	r3, [r7, #40]	; 0x28
   4350a:	697a      	ldr	r2, [r7, #20]
   4350c:	6abb      	ldr	r3, [r7, #40]	; 0x28
   4350e:	441a      	add	r2, r3
   43510:	2304      	movs	r3, #4
   43512:	009b      	lsls	r3, r3, #2
   43514:	f107 0190 	add.w	r1, r7, #144	; 0x90
   43518:	440b      	add	r3, r1
   4351a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4351e:	4413      	add	r3, r2
   43520:	617b      	str	r3, [r7, #20]
   43522:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   43524:	697b      	ldr	r3, [r7, #20]
   43526:	4053      	eors	r3, r2
   43528:	2108      	movs	r1, #8
   4352a:	4618      	mov	r0, r3
   4352c:	f7fd fb32 	bl	40b94 <rotr32>
   43530:	4603      	mov	r3, r0
   43532:	643b      	str	r3, [r7, #64]	; 0x40
   43534:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   43536:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   43538:	4413      	add	r3, r2
   4353a:	62fb      	str	r3, [r7, #44]	; 0x2c
   4353c:	6aba      	ldr	r2, [r7, #40]	; 0x28
   4353e:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   43540:	4053      	eors	r3, r2
   43542:	2107      	movs	r1, #7
   43544:	4618      	mov	r0, r3
   43546:	f7fd fb25 	bl	40b94 <rotr32>
   4354a:	4603      	mov	r3, r0
   4354c:	62bb      	str	r3, [r7, #40]	; 0x28
   4354e:	69ba      	ldr	r2, [r7, #24]
   43550:	69fb      	ldr	r3, [r7, #28]
   43552:	441a      	add	r2, r3
   43554:	230a      	movs	r3, #10
   43556:	009b      	lsls	r3, r3, #2
   43558:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4355c:	440b      	add	r3, r1
   4355e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   43562:	4413      	add	r3, r2
   43564:	61bb      	str	r3, [r7, #24]
   43566:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   43568:	69bb      	ldr	r3, [r7, #24]
   4356a:	4053      	eors	r3, r2
   4356c:	2110      	movs	r1, #16
   4356e:	4618      	mov	r0, r3
   43570:	f7fd fb10 	bl	40b94 <rotr32>
   43574:	4603      	mov	r3, r0
   43576:	647b      	str	r3, [r7, #68]	; 0x44
   43578:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   4357a:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   4357c:	4413      	add	r3, r2
   4357e:	633b      	str	r3, [r7, #48]	; 0x30
   43580:	69fa      	ldr	r2, [r7, #28]
   43582:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   43584:	4053      	eors	r3, r2
   43586:	210c      	movs	r1, #12
   43588:	4618      	mov	r0, r3
   4358a:	f7fd fb03 	bl	40b94 <rotr32>
   4358e:	4603      	mov	r3, r0
   43590:	61fb      	str	r3, [r7, #28]
   43592:	69ba      	ldr	r2, [r7, #24]
   43594:	69fb      	ldr	r3, [r7, #28]
   43596:	441a      	add	r2, r3
   43598:	2305      	movs	r3, #5
   4359a:	009b      	lsls	r3, r3, #2
   4359c:	f107 0190 	add.w	r1, r7, #144	; 0x90
   435a0:	440b      	add	r3, r1
   435a2:	f853 3c44 	ldr.w	r3, [r3, #-68]
   435a6:	4413      	add	r3, r2
   435a8:	61bb      	str	r3, [r7, #24]
   435aa:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   435ac:	69bb      	ldr	r3, [r7, #24]
   435ae:	4053      	eors	r3, r2
   435b0:	2108      	movs	r1, #8
   435b2:	4618      	mov	r0, r3
   435b4:	f7fd faee 	bl	40b94 <rotr32>
   435b8:	4603      	mov	r3, r0
   435ba:	647b      	str	r3, [r7, #68]	; 0x44
   435bc:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   435be:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   435c0:	4413      	add	r3, r2
   435c2:	633b      	str	r3, [r7, #48]	; 0x30
   435c4:	69fa      	ldr	r2, [r7, #28]
   435c6:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   435c8:	4053      	eors	r3, r2
   435ca:	2107      	movs	r1, #7
   435cc:	4618      	mov	r0, r3
   435ce:	f7fd fae1 	bl	40b94 <rotr32>
   435d2:	4603      	mov	r3, r0
   435d4:	61fb      	str	r3, [r7, #28]
   435d6:	68fa      	ldr	r2, [r7, #12]
   435d8:	69fb      	ldr	r3, [r7, #28]
   435da:	441a      	add	r2, r3
   435dc:	230a      	movs	r3, #10
   435de:	009b      	lsls	r3, r3, #2
   435e0:	f107 0190 	add.w	r1, r7, #144	; 0x90
   435e4:	440b      	add	r3, r1
   435e6:	f853 3c44 	ldr.w	r3, [r3, #-68]
   435ea:	4413      	add	r3, r2
   435ec:	60fb      	str	r3, [r7, #12]
   435ee:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   435f0:	68fb      	ldr	r3, [r7, #12]
   435f2:	4053      	eors	r3, r2
   435f4:	2110      	movs	r1, #16
   435f6:	4618      	mov	r0, r3
   435f8:	f7fd facc 	bl	40b94 <rotr32>
   435fc:	4603      	mov	r3, r0
   435fe:	63fb      	str	r3, [r7, #60]	; 0x3c
   43600:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   43602:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   43604:	4413      	add	r3, r2
   43606:	62fb      	str	r3, [r7, #44]	; 0x2c
   43608:	69fa      	ldr	r2, [r7, #28]
   4360a:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   4360c:	4053      	eors	r3, r2
   4360e:	210c      	movs	r1, #12
   43610:	4618      	mov	r0, r3
   43612:	f7fd fabf 	bl	40b94 <rotr32>
   43616:	4603      	mov	r3, r0
   43618:	61fb      	str	r3, [r7, #28]
   4361a:	68fa      	ldr	r2, [r7, #12]
   4361c:	69fb      	ldr	r3, [r7, #28]
   4361e:	441a      	add	r2, r3
   43620:	2302      	movs	r3, #2
   43622:	009b      	lsls	r3, r3, #2
   43624:	f107 0190 	add.w	r1, r7, #144	; 0x90
   43628:	440b      	add	r3, r1
   4362a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4362e:	4413      	add	r3, r2
   43630:	60fb      	str	r3, [r7, #12]
   43632:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   43634:	68fb      	ldr	r3, [r7, #12]
   43636:	4053      	eors	r3, r2
   43638:	2108      	movs	r1, #8
   4363a:	4618      	mov	r0, r3
   4363c:	f7fd faaa 	bl	40b94 <rotr32>
   43640:	4603      	mov	r3, r0
   43642:	63fb      	str	r3, [r7, #60]	; 0x3c
   43644:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   43646:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   43648:	4413      	add	r3, r2
   4364a:	62fb      	str	r3, [r7, #44]	; 0x2c
   4364c:	69fa      	ldr	r2, [r7, #28]
   4364e:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   43650:	4053      	eors	r3, r2
   43652:	2107      	movs	r1, #7
   43654:	4618      	mov	r0, r3
   43656:	f7fd fa9d 	bl	40b94 <rotr32>
   4365a:	4603      	mov	r3, r0
   4365c:	61fb      	str	r3, [r7, #28]
   4365e:	693a      	ldr	r2, [r7, #16]
   43660:	6a3b      	ldr	r3, [r7, #32]
   43662:	441a      	add	r2, r3
   43664:	2308      	movs	r3, #8
   43666:	009b      	lsls	r3, r3, #2
   43668:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4366c:	440b      	add	r3, r1
   4366e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   43672:	4413      	add	r3, r2
   43674:	613b      	str	r3, [r7, #16]
   43676:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   43678:	693b      	ldr	r3, [r7, #16]
   4367a:	4053      	eors	r3, r2
   4367c:	2110      	movs	r1, #16
   4367e:	4618      	mov	r0, r3
   43680:	f7fd fa88 	bl	40b94 <rotr32>
   43684:	4603      	mov	r3, r0
   43686:	643b      	str	r3, [r7, #64]	; 0x40
   43688:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   4368a:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   4368c:	4413      	add	r3, r2
   4368e:	633b      	str	r3, [r7, #48]	; 0x30
   43690:	6a3a      	ldr	r2, [r7, #32]
   43692:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   43694:	4053      	eors	r3, r2
   43696:	210c      	movs	r1, #12
   43698:	4618      	mov	r0, r3
   4369a:	f7fd fa7b 	bl	40b94 <rotr32>
   4369e:	4603      	mov	r3, r0
   436a0:	623b      	str	r3, [r7, #32]
   436a2:	693a      	ldr	r2, [r7, #16]
   436a4:	6a3b      	ldr	r3, [r7, #32]
   436a6:	441a      	add	r2, r3
   436a8:	2304      	movs	r3, #4
   436aa:	009b      	lsls	r3, r3, #2
   436ac:	f107 0190 	add.w	r1, r7, #144	; 0x90
   436b0:	440b      	add	r3, r1
   436b2:	f853 3c44 	ldr.w	r3, [r3, #-68]
   436b6:	4413      	add	r3, r2
   436b8:	613b      	str	r3, [r7, #16]
   436ba:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   436bc:	693b      	ldr	r3, [r7, #16]
   436be:	4053      	eors	r3, r2
   436c0:	2108      	movs	r1, #8
   436c2:	4618      	mov	r0, r3
   436c4:	f7fd fa66 	bl	40b94 <rotr32>
   436c8:	4603      	mov	r3, r0
   436ca:	643b      	str	r3, [r7, #64]	; 0x40
   436cc:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   436ce:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   436d0:	4413      	add	r3, r2
   436d2:	633b      	str	r3, [r7, #48]	; 0x30
   436d4:	6a3a      	ldr	r2, [r7, #32]
   436d6:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   436d8:	4053      	eors	r3, r2
   436da:	2107      	movs	r1, #7
   436dc:	4618      	mov	r0, r3
   436de:	f7fd fa59 	bl	40b94 <rotr32>
   436e2:	4603      	mov	r3, r0
   436e4:	623b      	str	r3, [r7, #32]
   436e6:	697a      	ldr	r2, [r7, #20]
   436e8:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   436ea:	441a      	add	r2, r3
   436ec:	2307      	movs	r3, #7
   436ee:	009b      	lsls	r3, r3, #2
   436f0:	f107 0190 	add.w	r1, r7, #144	; 0x90
   436f4:	440b      	add	r3, r1
   436f6:	f853 3c44 	ldr.w	r3, [r3, #-68]
   436fa:	4413      	add	r3, r2
   436fc:	617b      	str	r3, [r7, #20]
   436fe:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   43700:	697b      	ldr	r3, [r7, #20]
   43702:	4053      	eors	r3, r2
   43704:	2110      	movs	r1, #16
   43706:	4618      	mov	r0, r3
   43708:	f7fd fa44 	bl	40b94 <rotr32>
   4370c:	4603      	mov	r3, r0
   4370e:	647b      	str	r3, [r7, #68]	; 0x44
   43710:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   43712:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   43714:	4413      	add	r3, r2
   43716:	637b      	str	r3, [r7, #52]	; 0x34
   43718:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   4371a:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   4371c:	4053      	eors	r3, r2
   4371e:	210c      	movs	r1, #12
   43720:	4618      	mov	r0, r3
   43722:	f7fd fa37 	bl	40b94 <rotr32>
   43726:	4603      	mov	r3, r0
   43728:	627b      	str	r3, [r7, #36]	; 0x24
   4372a:	697a      	ldr	r2, [r7, #20]
   4372c:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   4372e:	441a      	add	r2, r3
   43730:	2306      	movs	r3, #6
   43732:	009b      	lsls	r3, r3, #2
   43734:	f107 0190 	add.w	r1, r7, #144	; 0x90
   43738:	440b      	add	r3, r1
   4373a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4373e:	4413      	add	r3, r2
   43740:	617b      	str	r3, [r7, #20]
   43742:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   43744:	697b      	ldr	r3, [r7, #20]
   43746:	4053      	eors	r3, r2
   43748:	2108      	movs	r1, #8
   4374a:	4618      	mov	r0, r3
   4374c:	f7fd fa22 	bl	40b94 <rotr32>
   43750:	4603      	mov	r3, r0
   43752:	647b      	str	r3, [r7, #68]	; 0x44
   43754:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   43756:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   43758:	4413      	add	r3, r2
   4375a:	637b      	str	r3, [r7, #52]	; 0x34
   4375c:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   4375e:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   43760:	4053      	eors	r3, r2
   43762:	2107      	movs	r1, #7
   43764:	4618      	mov	r0, r3
   43766:	f7fd fa15 	bl	40b94 <rotr32>
   4376a:	4603      	mov	r3, r0
   4376c:	627b      	str	r3, [r7, #36]	; 0x24
   4376e:	69ba      	ldr	r2, [r7, #24]
   43770:	6abb      	ldr	r3, [r7, #40]	; 0x28
   43772:	441a      	add	r2, r3
   43774:	2301      	movs	r3, #1
   43776:	009b      	lsls	r3, r3, #2
   43778:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4377c:	440b      	add	r3, r1
   4377e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   43782:	4413      	add	r3, r2
   43784:	61bb      	str	r3, [r7, #24]
   43786:	6cba      	ldr	r2, [r7, #72]	; 0x48
   43788:	69bb      	ldr	r3, [r7, #24]
   4378a:	4053      	eors	r3, r2
   4378c:	2110      	movs	r1, #16
   4378e:	4618      	mov	r0, r3
   43790:	f7fd fa00 	bl	40b94 <rotr32>
   43794:	4603      	mov	r3, r0
   43796:	64bb      	str	r3, [r7, #72]	; 0x48
   43798:	6bba      	ldr	r2, [r7, #56]	; 0x38
   4379a:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   4379c:	4413      	add	r3, r2
   4379e:	63bb      	str	r3, [r7, #56]	; 0x38
   437a0:	6aba      	ldr	r2, [r7, #40]	; 0x28
   437a2:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   437a4:	4053      	eors	r3, r2
   437a6:	210c      	movs	r1, #12
   437a8:	4618      	mov	r0, r3
   437aa:	f7fd f9f3 	bl	40b94 <rotr32>
   437ae:	4603      	mov	r3, r0
   437b0:	62bb      	str	r3, [r7, #40]	; 0x28
   437b2:	69ba      	ldr	r2, [r7, #24]
   437b4:	6abb      	ldr	r3, [r7, #40]	; 0x28
   437b6:	441a      	add	r2, r3
   437b8:	2305      	movs	r3, #5
   437ba:	009b      	lsls	r3, r3, #2
   437bc:	f107 0190 	add.w	r1, r7, #144	; 0x90
   437c0:	440b      	add	r3, r1
   437c2:	f853 3c44 	ldr.w	r3, [r3, #-68]
   437c6:	4413      	add	r3, r2
   437c8:	61bb      	str	r3, [r7, #24]
   437ca:	6cba      	ldr	r2, [r7, #72]	; 0x48
   437cc:	69bb      	ldr	r3, [r7, #24]
   437ce:	4053      	eors	r3, r2
   437d0:	2108      	movs	r1, #8
   437d2:	4618      	mov	r0, r3
   437d4:	f7fd f9de 	bl	40b94 <rotr32>
   437d8:	4603      	mov	r3, r0
   437da:	64bb      	str	r3, [r7, #72]	; 0x48
   437dc:	6bba      	ldr	r2, [r7, #56]	; 0x38
   437de:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   437e0:	4413      	add	r3, r2
   437e2:	63bb      	str	r3, [r7, #56]	; 0x38
   437e4:	6aba      	ldr	r2, [r7, #40]	; 0x28
   437e6:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   437e8:	4053      	eors	r3, r2
   437ea:	2107      	movs	r1, #7
   437ec:	4618      	mov	r0, r3
   437ee:	f7fd f9d1 	bl	40b94 <rotr32>
   437f2:	4603      	mov	r3, r0
   437f4:	62bb      	str	r3, [r7, #40]	; 0x28
   437f6:	68fa      	ldr	r2, [r7, #12]
   437f8:	6a3b      	ldr	r3, [r7, #32]
   437fa:	441a      	add	r2, r3
   437fc:	230f      	movs	r3, #15
   437fe:	009b      	lsls	r3, r3, #2
   43800:	f107 0190 	add.w	r1, r7, #144	; 0x90
   43804:	440b      	add	r3, r1
   43806:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4380a:	4413      	add	r3, r2
   4380c:	60fb      	str	r3, [r7, #12]
   4380e:	6cba      	ldr	r2, [r7, #72]	; 0x48
   43810:	68fb      	ldr	r3, [r7, #12]
   43812:	4053      	eors	r3, r2
   43814:	2110      	movs	r1, #16
   43816:	4618      	mov	r0, r3
   43818:	f7fd f9bc 	bl	40b94 <rotr32>
   4381c:	4603      	mov	r3, r0
   4381e:	64bb      	str	r3, [r7, #72]	; 0x48
   43820:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   43822:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   43824:	4413      	add	r3, r2
   43826:	637b      	str	r3, [r7, #52]	; 0x34
   43828:	6a3a      	ldr	r2, [r7, #32]
   4382a:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   4382c:	4053      	eors	r3, r2
   4382e:	210c      	movs	r1, #12
   43830:	4618      	mov	r0, r3
   43832:	f7fd f9af 	bl	40b94 <rotr32>
   43836:	4603      	mov	r3, r0
   43838:	623b      	str	r3, [r7, #32]
   4383a:	68fa      	ldr	r2, [r7, #12]
   4383c:	6a3b      	ldr	r3, [r7, #32]
   4383e:	441a      	add	r2, r3
   43840:	230b      	movs	r3, #11
   43842:	009b      	lsls	r3, r3, #2
   43844:	f107 0190 	add.w	r1, r7, #144	; 0x90
   43848:	440b      	add	r3, r1
   4384a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4384e:	4413      	add	r3, r2
   43850:	60fb      	str	r3, [r7, #12]
   43852:	6cba      	ldr	r2, [r7, #72]	; 0x48
   43854:	68fb      	ldr	r3, [r7, #12]
   43856:	4053      	eors	r3, r2
   43858:	2108      	movs	r1, #8
   4385a:	4618      	mov	r0, r3
   4385c:	f7fd f99a 	bl	40b94 <rotr32>
   43860:	4603      	mov	r3, r0
   43862:	64bb      	str	r3, [r7, #72]	; 0x48
   43864:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   43866:	6cbb      	ldr	r3, [r7, #72]	; 0x48
   43868:	4413      	add	r3, r2
   4386a:	637b      	str	r3, [r7, #52]	; 0x34
   4386c:	6a3a      	ldr	r2, [r7, #32]
   4386e:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   43870:	4053      	eors	r3, r2
   43872:	2107      	movs	r1, #7
   43874:	4618      	mov	r0, r3
   43876:	f7fd f98d 	bl	40b94 <rotr32>
   4387a:	4603      	mov	r3, r0
   4387c:	623b      	str	r3, [r7, #32]
   4387e:	693a      	ldr	r2, [r7, #16]
   43880:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   43882:	441a      	add	r2, r3
   43884:	2309      	movs	r3, #9
   43886:	009b      	lsls	r3, r3, #2
   43888:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4388c:	440b      	add	r3, r1
   4388e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   43892:	4413      	add	r3, r2
   43894:	613b      	str	r3, [r7, #16]
   43896:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   43898:	693b      	ldr	r3, [r7, #16]
   4389a:	4053      	eors	r3, r2
   4389c:	2110      	movs	r1, #16
   4389e:	4618      	mov	r0, r3
   438a0:	f7fd f978 	bl	40b94 <rotr32>
   438a4:	4603      	mov	r3, r0
   438a6:	63fb      	str	r3, [r7, #60]	; 0x3c
   438a8:	6bba      	ldr	r2, [r7, #56]	; 0x38
   438aa:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   438ac:	4413      	add	r3, r2
   438ae:	63bb      	str	r3, [r7, #56]	; 0x38
   438b0:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   438b2:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   438b4:	4053      	eors	r3, r2
   438b6:	210c      	movs	r1, #12
   438b8:	4618      	mov	r0, r3
   438ba:	f7fd f96b 	bl	40b94 <rotr32>
   438be:	4603      	mov	r3, r0
   438c0:	627b      	str	r3, [r7, #36]	; 0x24
   438c2:	693a      	ldr	r2, [r7, #16]
   438c4:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   438c6:	441a      	add	r2, r3
   438c8:	230e      	movs	r3, #14
   438ca:	009b      	lsls	r3, r3, #2
   438cc:	f107 0190 	add.w	r1, r7, #144	; 0x90
   438d0:	440b      	add	r3, r1
   438d2:	f853 3c44 	ldr.w	r3, [r3, #-68]
   438d6:	4413      	add	r3, r2
   438d8:	613b      	str	r3, [r7, #16]
   438da:	6bfa      	ldr	r2, [r7, #60]	; 0x3c
   438dc:	693b      	ldr	r3, [r7, #16]
   438de:	4053      	eors	r3, r2
   438e0:	2108      	movs	r1, #8
   438e2:	4618      	mov	r0, r3
   438e4:	f7fd f956 	bl	40b94 <rotr32>
   438e8:	4603      	mov	r3, r0
   438ea:	63fb      	str	r3, [r7, #60]	; 0x3c
   438ec:	6bba      	ldr	r2, [r7, #56]	; 0x38
   438ee:	6bfb      	ldr	r3, [r7, #60]	; 0x3c
   438f0:	4413      	add	r3, r2
   438f2:	63bb      	str	r3, [r7, #56]	; 0x38
   438f4:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   438f6:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   438f8:	4053      	eors	r3, r2
   438fa:	2107      	movs	r1, #7
   438fc:	4618      	mov	r0, r3
   438fe:	f7fd f949 	bl	40b94 <rotr32>
   43902:	4603      	mov	r3, r0
   43904:	627b      	str	r3, [r7, #36]	; 0x24
   43906:	697a      	ldr	r2, [r7, #20]
   43908:	6abb      	ldr	r3, [r7, #40]	; 0x28
   4390a:	441a      	add	r2, r3
   4390c:	2303      	movs	r3, #3
   4390e:	009b      	lsls	r3, r3, #2
   43910:	f107 0190 	add.w	r1, r7, #144	; 0x90
   43914:	440b      	add	r3, r1
   43916:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4391a:	4413      	add	r3, r2
   4391c:	617b      	str	r3, [r7, #20]
   4391e:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   43920:	697b      	ldr	r3, [r7, #20]
   43922:	4053      	eors	r3, r2
   43924:	2110      	movs	r1, #16
   43926:	4618      	mov	r0, r3
   43928:	f7fd f934 	bl	40b94 <rotr32>
   4392c:	4603      	mov	r3, r0
   4392e:	643b      	str	r3, [r7, #64]	; 0x40
   43930:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   43932:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   43934:	4413      	add	r3, r2
   43936:	62fb      	str	r3, [r7, #44]	; 0x2c
   43938:	6aba      	ldr	r2, [r7, #40]	; 0x28
   4393a:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   4393c:	4053      	eors	r3, r2
   4393e:	210c      	movs	r1, #12
   43940:	4618      	mov	r0, r3
   43942:	f7fd f927 	bl	40b94 <rotr32>
   43946:	4603      	mov	r3, r0
   43948:	62bb      	str	r3, [r7, #40]	; 0x28
   4394a:	697a      	ldr	r2, [r7, #20]
   4394c:	6abb      	ldr	r3, [r7, #40]	; 0x28
   4394e:	441a      	add	r2, r3
   43950:	230c      	movs	r3, #12
   43952:	009b      	lsls	r3, r3, #2
   43954:	f107 0190 	add.w	r1, r7, #144	; 0x90
   43958:	440b      	add	r3, r1
   4395a:	f853 3c44 	ldr.w	r3, [r3, #-68]
   4395e:	4413      	add	r3, r2
   43960:	617b      	str	r3, [r7, #20]
   43962:	6c3a      	ldr	r2, [r7, #64]	; 0x40
   43964:	697b      	ldr	r3, [r7, #20]
   43966:	4053      	eors	r3, r2
   43968:	2108      	movs	r1, #8
   4396a:	4618      	mov	r0, r3
   4396c:	f7fd f912 	bl	40b94 <rotr32>
   43970:	4603      	mov	r3, r0
   43972:	643b      	str	r3, [r7, #64]	; 0x40
   43974:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   43976:	6c3b      	ldr	r3, [r7, #64]	; 0x40
   43978:	4413      	add	r3, r2
   4397a:	62fb      	str	r3, [r7, #44]	; 0x2c
   4397c:	6aba      	ldr	r2, [r7, #40]	; 0x28
   4397e:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   43980:	4053      	eors	r3, r2
   43982:	2107      	movs	r1, #7
   43984:	4618      	mov	r0, r3
   43986:	f7fd f905 	bl	40b94 <rotr32>
   4398a:	4603      	mov	r3, r0
   4398c:	62bb      	str	r3, [r7, #40]	; 0x28
   4398e:	69ba      	ldr	r2, [r7, #24]
   43990:	69fb      	ldr	r3, [r7, #28]
   43992:	441a      	add	r2, r3
   43994:	230d      	movs	r3, #13
   43996:	009b      	lsls	r3, r3, #2
   43998:	f107 0190 	add.w	r1, r7, #144	; 0x90
   4399c:	440b      	add	r3, r1
   4399e:	f853 3c44 	ldr.w	r3, [r3, #-68]
   439a2:	4413      	add	r3, r2
   439a4:	61bb      	str	r3, [r7, #24]
   439a6:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   439a8:	69bb      	ldr	r3, [r7, #24]
   439aa:	4053      	eors	r3, r2
   439ac:	2110      	movs	r1, #16
   439ae:	4618      	mov	r0, r3
   439b0:	f7fd f8f0 	bl	40b94 <rotr32>
   439b4:	4603      	mov	r3, r0
   439b6:	647b      	str	r3, [r7, #68]	; 0x44
   439b8:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   439ba:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   439bc:	4413      	add	r3, r2
   439be:	633b      	str	r3, [r7, #48]	; 0x30
   439c0:	69fa      	ldr	r2, [r7, #28]
   439c2:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   439c4:	4053      	eors	r3, r2
   439c6:	210c      	movs	r1, #12
   439c8:	4618      	mov	r0, r3
   439ca:	f7fd f8e3 	bl	40b94 <rotr32>
   439ce:	4603      	mov	r3, r0
   439d0:	61fb      	str	r3, [r7, #28]
   439d2:	69ba      	ldr	r2, [r7, #24]
   439d4:	69fb      	ldr	r3, [r7, #28]
   439d6:	441a      	add	r2, r3
   439d8:	2300      	movs	r3, #0
   439da:	009b      	lsls	r3, r3, #2
   439dc:	f107 0190 	add.w	r1, r7, #144	; 0x90
   439e0:	440b      	add	r3, r1
   439e2:	f853 3c44 	ldr.w	r3, [r3, #-68]
   439e6:	4413      	add	r3, r2
   439e8:	61bb      	str	r3, [r7, #24]
   439ea:	6c7a      	ldr	r2, [r7, #68]	; 0x44
   439ec:	69bb      	ldr	r3, [r7, #24]
   439ee:	4053      	eors	r3, r2
   439f0:	2108      	movs	r1, #8
   439f2:	4618      	mov	r0, r3
   439f4:	f7fd f8ce 	bl	40b94 <rotr32>
   439f8:	4603      	mov	r3, r0
   439fa:	647b      	str	r3, [r7, #68]	; 0x44
   439fc:	6b3a      	ldr	r2, [r7, #48]	; 0x30
   439fe:	6c7b      	ldr	r3, [r7, #68]	; 0x44
   43a00:	4413      	add	r3, r2
   43a02:	633b      	str	r3, [r7, #48]	; 0x30
   43a04:	69fa      	ldr	r2, [r7, #28]
   43a06:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   43a08:	4053      	eors	r3, r2
   43a0a:	2107      	movs	r1, #7
   43a0c:	4618      	mov	r0, r3
   43a0e:	f7fd f8c1 	bl	40b94 <rotr32>
   43a12:	4603      	mov	r3, r0
   43a14:	61fb      	str	r3, [r7, #28]
   43a16:	2300      	movs	r3, #0
   43a18:	f8c7 308c 	str.w	r3, [r7, #140]	; 0x8c
   43a1c:	e022      	b.n	43a64 <blake2s_compress+0x2bb0>
   43a1e:	687b      	ldr	r3, [r7, #4]
   43a20:	f8d7 208c 	ldr.w	r2, [r7, #140]	; 0x8c
   43a24:	f853 2022 	ldr.w	r2, [r3, r2, lsl #2]
   43a28:	f8d7 308c 	ldr.w	r3, [r7, #140]	; 0x8c
   43a2c:	009b      	lsls	r3, r3, #2
   43a2e:	f107 0190 	add.w	r1, r7, #144	; 0x90
   43a32:	440b      	add	r3, r1
   43a34:	f853 3c84 	ldr.w	r3, [r3, #-132]
   43a38:	405a      	eors	r2, r3
   43a3a:	f8d7 308c 	ldr.w	r3, [r7, #140]	; 0x8c
   43a3e:	3308      	adds	r3, #8
   43a40:	009b      	lsls	r3, r3, #2
   43a42:	f107 0190 	add.w	r1, r7, #144	; 0x90
   43a46:	440b      	add	r3, r1
   43a48:	f853 3c84 	ldr.w	r3, [r3, #-132]
   43a4c:	ea82 0103 	eor.w	r1, r2, r3
   43a50:	687b      	ldr	r3, [r7, #4]
   43a52:	f8d7 208c 	ldr.w	r2, [r7, #140]	; 0x8c
   43a56:	f843 1022 	str.w	r1, [r3, r2, lsl #2]
   43a5a:	f8d7 308c 	ldr.w	r3, [r7, #140]	; 0x8c
   43a5e:	3301      	adds	r3, #1
   43a60:	f8c7 308c 	str.w	r3, [r7, #140]	; 0x8c
   43a64:	f8d7 308c 	ldr.w	r3, [r7, #140]	; 0x8c
   43a68:	2b07      	cmp	r3, #7
   43a6a:	d9d8      	bls.n	43a1e <blake2s_compress+0x2b6a>
   43a6c:	bf00      	nop
   43a6e:	3790      	adds	r7, #144	; 0x90
   43a70:	46bd      	mov	sp, r7
   43a72:	bd80      	pop	{r7, pc}

00043a74 <blake2s_update>:
   43a74:	b580      	push	{r7, lr}
   43a76:	b088      	sub	sp, #32
   43a78:	af00      	add	r7, sp, #0
   43a7a:	60f8      	str	r0, [r7, #12]
   43a7c:	60b9      	str	r1, [r7, #8]
   43a7e:	607a      	str	r2, [r7, #4]
   43a80:	68bb      	ldr	r3, [r7, #8]
   43a82:	61fb      	str	r3, [r7, #28]
   43a84:	687b      	ldr	r3, [r7, #4]
   43a86:	2b00      	cmp	r3, #0
   43a88:	d04c      	beq.n	43b24 <blake2s_update+0xb0>
   43a8a:	68fb      	ldr	r3, [r7, #12]
   43a8c:	6f1b      	ldr	r3, [r3, #112]	; 0x70
   43a8e:	61bb      	str	r3, [r7, #24]
   43a90:	69bb      	ldr	r3, [r7, #24]
   43a92:	f1c3 0340 	rsb	r3, r3, #64	; 0x40
   43a96:	617b      	str	r3, [r7, #20]
   43a98:	687a      	ldr	r2, [r7, #4]
   43a9a:	697b      	ldr	r3, [r7, #20]
   43a9c:	429a      	cmp	r2, r3
   43a9e:	d930      	bls.n	43b02 <blake2s_update+0x8e>
   43aa0:	68fb      	ldr	r3, [r7, #12]
   43aa2:	2200      	movs	r2, #0
   43aa4:	671a      	str	r2, [r3, #112]	; 0x70
   43aa6:	68fb      	ldr	r3, [r7, #12]
   43aa8:	f103 0230 	add.w	r2, r3, #48	; 0x30
   43aac:	69bb      	ldr	r3, [r7, #24]
   43aae:	4413      	add	r3, r2
   43ab0:	697a      	ldr	r2, [r7, #20]
   43ab2:	69f9      	ldr	r1, [r7, #28]
   43ab4:	4618      	mov	r0, r3
   43ab6:	f7cc ef60 	blx	10978 <memcpy@plt>
   43aba:	2140      	movs	r1, #64	; 0x40
   43abc:	68f8      	ldr	r0, [r7, #12]
   43abe:	f7fd f8be 	bl	40c3e <blake2s_increment_counter>
   43ac2:	68fb      	ldr	r3, [r7, #12]
   43ac4:	3330      	adds	r3, #48	; 0x30
   43ac6:	4619      	mov	r1, r3
   43ac8:	68f8      	ldr	r0, [r7, #12]
   43aca:	f7fd f9f3 	bl	40eb4 <blake2s_compress>
   43ace:	69fa      	ldr	r2, [r7, #28]
   43ad0:	697b      	ldr	r3, [r7, #20]
   43ad2:	4413      	add	r3, r2
   43ad4:	61fb      	str	r3, [r7, #28]
   43ad6:	687a      	ldr	r2, [r7, #4]
   43ad8:	697b      	ldr	r3, [r7, #20]
   43ada:	1ad3      	subs	r3, r2, r3
   43adc:	607b      	str	r3, [r7, #4]
   43ade:	e00d      	b.n	43afc <blake2s_update+0x88>
   43ae0:	2140      	movs	r1, #64	; 0x40
   43ae2:	68f8      	ldr	r0, [r7, #12]
   43ae4:	f7fd f8ab 	bl	40c3e <blake2s_increment_counter>
   43ae8:	69f9      	ldr	r1, [r7, #28]
   43aea:	68f8      	ldr	r0, [r7, #12]
   43aec:	f7fd f9e2 	bl	40eb4 <blake2s_compress>
   43af0:	69fb      	ldr	r3, [r7, #28]
   43af2:	3340      	adds	r3, #64	; 0x40
   43af4:	61fb      	str	r3, [r7, #28]
   43af6:	687b      	ldr	r3, [r7, #4]
   43af8:	3b40      	subs	r3, #64	; 0x40
   43afa:	607b      	str	r3, [r7, #4]
   43afc:	687b      	ldr	r3, [r7, #4]
   43afe:	2b40      	cmp	r3, #64	; 0x40
   43b00:	d8ee      	bhi.n	43ae0 <blake2s_update+0x6c>
   43b02:	68fb      	ldr	r3, [r7, #12]
   43b04:	f103 0230 	add.w	r2, r3, #48	; 0x30
   43b08:	68fb      	ldr	r3, [r7, #12]
   43b0a:	6f1b      	ldr	r3, [r3, #112]	; 0x70
   43b0c:	4413      	add	r3, r2
   43b0e:	687a      	ldr	r2, [r7, #4]
   43b10:	69f9      	ldr	r1, [r7, #28]
   43b12:	4618      	mov	r0, r3
   43b14:	f7cc ef30 	blx	10978 <memcpy@plt>
   43b18:	68fb      	ldr	r3, [r7, #12]
   43b1a:	6f1a      	ldr	r2, [r3, #112]	; 0x70
   43b1c:	687b      	ldr	r3, [r7, #4]
   43b1e:	441a      	add	r2, r3
   43b20:	68fb      	ldr	r3, [r7, #12]
   43b22:	671a      	str	r2, [r3, #112]	; 0x70
   43b24:	2300      	movs	r3, #0
   43b26:	4618      	mov	r0, r3
   43b28:	3720      	adds	r7, #32
   43b2a:	46bd      	mov	sp, r7
   43b2c:	bd80      	pop	{r7, pc}

00043b2e <blake2s_final>:
   43b2e:	b580      	push	{r7, lr}
   43b30:	b08e      	sub	sp, #56	; 0x38
   43b32:	af00      	add	r7, sp, #0
   43b34:	60f8      	str	r0, [r7, #12]
   43b36:	60b9      	str	r1, [r7, #8]
   43b38:	607a      	str	r2, [r7, #4]
   43b3a:	f107 0314 	add.w	r3, r7, #20
   43b3e:	2220      	movs	r2, #32
   43b40:	2100      	movs	r1, #0
   43b42:	4618      	mov	r0, r3
   43b44:	f7cc ef6c 	blx	10a20 <memset@plt>
   43b48:	68bb      	ldr	r3, [r7, #8]
   43b4a:	2b00      	cmp	r3, #0
   43b4c:	d004      	beq.n	43b58 <blake2s_final+0x2a>
   43b4e:	68fb      	ldr	r3, [r7, #12]
   43b50:	6f5a      	ldr	r2, [r3, #116]	; 0x74
   43b52:	687b      	ldr	r3, [r7, #4]
   43b54:	429a      	cmp	r2, r3
   43b56:	d902      	bls.n	43b5e <blake2s_final+0x30>
   43b58:	f04f 33ff 	mov.w	r3, #4294967295	; 0xffffffff
   43b5c:	e048      	b.n	43bf0 <blake2s_final+0xc2>
   43b5e:	68f8      	ldr	r0, [r7, #12]
   43b60:	f7fd f848 	bl	40bf4 <blake2s_is_lastblock>
   43b64:	4603      	mov	r3, r0
   43b66:	2b00      	cmp	r3, #0
   43b68:	d002      	beq.n	43b70 <blake2s_final+0x42>
   43b6a:	f04f 33ff 	mov.w	r3, #4294967295	; 0xffffffff
   43b6e:	e03f      	b.n	43bf0 <blake2s_final+0xc2>
   43b70:	68fb      	ldr	r3, [r7, #12]
   43b72:	6f1b      	ldr	r3, [r3, #112]	; 0x70
   43b74:	4619      	mov	r1, r3
   43b76:	68f8      	ldr	r0, [r7, #12]
   43b78:	f7fd f861 	bl	40c3e <blake2s_increment_counter>
   43b7c:	68f8      	ldr	r0, [r7, #12]
   43b7e:	f7fd f84a 	bl	40c16 <blake2s_set_lastblock>
   43b82:	68fb      	ldr	r3, [r7, #12]
   43b84:	f103 0230 	add.w	r2, r3, #48	; 0x30
   43b88:	68fb      	ldr	r3, [r7, #12]
   43b8a:	6f1b      	ldr	r3, [r3, #112]	; 0x70
   43b8c:	18d0      	adds	r0, r2, r3
   43b8e:	68fb      	ldr	r3, [r7, #12]
   43b90:	6f1b      	ldr	r3, [r3, #112]	; 0x70
   43b92:	f1c3 0340 	rsb	r3, r3, #64	; 0x40
   43b96:	461a      	mov	r2, r3
   43b98:	2100      	movs	r1, #0
   43b9a:	f7cc ef42 	blx	10a20 <memset@plt>
   43b9e:	68fb      	ldr	r3, [r7, #12]
   43ba0:	3330      	adds	r3, #48	; 0x30
   43ba2:	4619      	mov	r1, r3
   43ba4:	68f8      	ldr	r0, [r7, #12]
   43ba6:	f7fd f985 	bl	40eb4 <blake2s_compress>
   43baa:	2300      	movs	r3, #0
   43bac:	637b      	str	r3, [r7, #52]	; 0x34
   43bae:	e00e      	b.n	43bce <blake2s_final+0xa0>
   43bb0:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   43bb2:	009b      	lsls	r3, r3, #2
   43bb4:	f107 0214 	add.w	r2, r7, #20
   43bb8:	18d0      	adds	r0, r2, r3
   43bba:	68fb      	ldr	r3, [r7, #12]
   43bbc:	6b7a      	ldr	r2, [r7, #52]	; 0x34
   43bbe:	f853 3022 	ldr.w	r3, [r3, r2, lsl #2]
   43bc2:	4619      	mov	r1, r3
   43bc4:	f7fc ffc3 	bl	40b4e <store32>
   43bc8:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   43bca:	3301      	adds	r3, #1
   43bcc:	637b      	str	r3, [r7, #52]	; 0x34
   43bce:	6b7b      	ldr	r3, [r7, #52]	; 0x34
   43bd0:	2b07      	cmp	r3, #7
   43bd2:	d9ed      	bls.n	43bb0 <blake2s_final+0x82>
   43bd4:	f107 0314 	add.w	r3, r7, #20
   43bd8:	687a      	ldr	r2, [r7, #4]
   43bda:	4619      	mov	r1, r3
   43bdc:	68b8      	ldr	r0, [r7, #8]
   43bde:	f7cc eecc 	blx	10978 <memcpy@plt>
   43be2:	f107 0314 	add.w	r3, r7, #20
   43be6:	2120      	movs	r1, #32
   43be8:	4618      	mov	r0, r3
   43bea:	f7fc ffe2 	bl	40bb2 <secure_zero_memory>
   43bee:	2300      	movs	r3, #0
   43bf0:	4618      	mov	r0, r3
   43bf2:	3738      	adds	r7, #56	; 0x38
   43bf4:	46bd      	mov	sp, r7
   43bf6:	bd80      	pop	{r7, pc}

00043bf8 <blake2s>:
   43bf8:	b580      	push	{r7, lr}
   43bfa:	b0a4      	sub	sp, #144	; 0x90
   43bfc:	af00      	add	r7, sp, #0
   43bfe:	60f8      	str	r0, [r7, #12]
   43c00:	60b9      	str	r1, [r7, #8]
   43c02:	607a      	str	r2, [r7, #4]
   43c04:	603b      	str	r3, [r7, #0]
   43c06:	687b      	ldr	r3, [r7, #4]
   43c08:	2b00      	cmp	r3, #0
   43c0a:	d105      	bne.n	43c18 <blake2s+0x20>
   43c0c:	683b      	ldr	r3, [r7, #0]
   43c0e:	2b00      	cmp	r3, #0
   43c10:	d002      	beq.n	43c18 <blake2s+0x20>
   43c12:	f04f 33ff 	mov.w	r3, #4294967295	; 0xffffffff
   43c16:	e04e      	b.n	43cb6 <blake2s+0xbe>
   43c18:	68fb      	ldr	r3, [r7, #12]
   43c1a:	2b00      	cmp	r3, #0
   43c1c:	d102      	bne.n	43c24 <blake2s+0x2c>
   43c1e:	f04f 33ff 	mov.w	r3, #4294967295	; 0xffffffff
   43c22:	e048      	b.n	43cb6 <blake2s+0xbe>
   43c24:	f8d7 3098 	ldr.w	r3, [r7, #152]	; 0x98
   43c28:	2b00      	cmp	r3, #0
   43c2a:	d106      	bne.n	43c3a <blake2s+0x42>
   43c2c:	f8d7 309c 	ldr.w	r3, [r7, #156]	; 0x9c
   43c30:	2b00      	cmp	r3, #0
   43c32:	d002      	beq.n	43c3a <blake2s+0x42>
   43c34:	f04f 33ff 	mov.w	r3, #4294967295	; 0xffffffff
   43c38:	e03d      	b.n	43cb6 <blake2s+0xbe>
   43c3a:	68bb      	ldr	r3, [r7, #8]
   43c3c:	2b00      	cmp	r3, #0
   43c3e:	d002      	beq.n	43c46 <blake2s+0x4e>
   43c40:	68bb      	ldr	r3, [r7, #8]
   43c42:	2b20      	cmp	r3, #32
   43c44:	d902      	bls.n	43c4c <blake2s+0x54>
   43c46:	f04f 33ff 	mov.w	r3, #4294967295	; 0xffffffff
   43c4a:	e034      	b.n	43cb6 <blake2s+0xbe>
   43c4c:	f8d7 309c 	ldr.w	r3, [r7, #156]	; 0x9c
   43c50:	2b20      	cmp	r3, #32
   43c52:	d902      	bls.n	43c5a <blake2s+0x62>
   43c54:	f04f 33ff 	mov.w	r3, #4294967295	; 0xffffffff
   43c58:	e02d      	b.n	43cb6 <blake2s+0xbe>
   43c5a:	f8d7 309c 	ldr.w	r3, [r7, #156]	; 0x9c
   43c5e:	2b00      	cmp	r3, #0
   43c60:	d00e      	beq.n	43c80 <blake2s+0x88>
   43c62:	f107 0014 	add.w	r0, r7, #20
   43c66:	f8d7 309c 	ldr.w	r3, [r7, #156]	; 0x9c
   43c6a:	f8d7 2098 	ldr.w	r2, [r7, #152]	; 0x98
   43c6e:	68b9      	ldr	r1, [r7, #8]
   43c70:	f7fd f89f 	bl	40db2 <blake2s_init_key>
   43c74:	4603      	mov	r3, r0
   43c76:	2b00      	cmp	r3, #0
   43c78:	da0e      	bge.n	43c98 <blake2s+0xa0>
   43c7a:	f04f 33ff 	mov.w	r3, #4294967295	; 0xffffffff
   43c7e:	e01a      	b.n	43cb6 <blake2s+0xbe>
   43c80:	f107 0314 	add.w	r3, r7, #20
   43c84:	68b9      	ldr	r1, [r7, #8]
   43c86:	4618      	mov	r0, r3
   43c88:	f7fd f848 	bl	40d1c <blake2s_init>
   43c8c:	4603      	mov	r3, r0
   43c8e:	2b00      	cmp	r3, #0
   43c90:	da02      	bge.n	43c98 <blake2s+0xa0>
   43c92:	f04f 33ff 	mov.w	r3, #4294967295	; 0xffffffff
   43c96:	e00e      	b.n	43cb6 <blake2s+0xbe>
   43c98:	f107 0314 	add.w	r3, r7, #20
   43c9c:	683a      	ldr	r2, [r7, #0]
   43c9e:	6879      	ldr	r1, [r7, #4]
   43ca0:	4618      	mov	r0, r3
   43ca2:	f7ff fee7 	bl	43a74 <blake2s_update>
   43ca6:	f107 0314 	add.w	r3, r7, #20
   43caa:	68ba      	ldr	r2, [r7, #8]
   43cac:	68f9      	ldr	r1, [r7, #12]
   43cae:	4618      	mov	r0, r3
   43cb0:	f7ff ff3d 	bl	43b2e <blake2s_final>
   43cb4:	2300      	movs	r3, #0
   43cb6:	4618      	mov	r0, r3
   43cb8:	3790      	adds	r7, #144	; 0x90
   43cba:	46bd      	mov	sp, r7
   43cbc:	bd80      	pop	{r7, pc}
   43cbe:	bf00      	nop

00043cc0 <push>:
   43cc0:	b084      	sub	sp, #16
   43cc2:	b490      	push	{r4, r7}
   43cc4:	b088      	sub	sp, #32
   43cc6:	af00      	add	r7, sp, #0
   43cc8:	6078      	str	r0, [r7, #4]
   43cca:	f107 002c 	add.w	r0, r7, #44	; 0x2c
   43cce:	e880 000e 	stmia.w	r0, {r1, r2, r3}
   43cd2:	687a      	ldr	r2, [r7, #4]
   43cd4:	f44f 43d0 	mov.w	r3, #26624	; 0x6800
   43cd8:	f6c0 1389 	movt	r3, #2441	; 0x989
   43cdc:	4413      	add	r3, r2
   43cde:	f3bf 8f5b 	dmb	ish
   43ce2:	681b      	ldr	r3, [r3, #0]
   43ce4:	f3bf 8f5b 	dmb	ish
   43ce8:	613b      	str	r3, [r7, #16]
   43cea:	693b      	ldr	r3, [r7, #16]
   43cec:	1c5a      	adds	r2, r3, #1
   43cee:	f64c 236b 	movw	r3, #51819	; 0xca6b
   43cf2:	f6c6 335f 	movt	r3, #27487	; 0x6b5f
   43cf6:	fba2 3403 	umull	r3, r4, r2, r3
   43cfa:	0da1      	lsrs	r1, r4, #22
   43cfc:	f249 6380 	movw	r3, #38528	; 0x9680
   43d00:	f2c0 0398 	movt	r3, #152	; 0x98
   43d04:	fb03 f301 	mul.w	r3, r3, r1
   43d08:	1ad3      	subs	r3, r2, r3
   43d0a:	61fb      	str	r3, [r7, #28]
   43d0c:	687a      	ldr	r2, [r7, #4]
   43d0e:	f646 0304 	movw	r3, #26628	; 0x6804
   43d12:	f6c0 1389 	movt	r3, #2441	; 0x989
   43d16:	4413      	add	r3, r2
   43d18:	61bb      	str	r3, [r7, #24]
   43d1a:	69bb      	ldr	r3, [r7, #24]
   43d1c:	f3bf 8f5b 	dmb	ish
   43d20:	681b      	ldr	r3, [r3, #0]
   43d22:	f3bf 8f5b 	dmb	ish
   43d26:	60fb      	str	r3, [r7, #12]
   43d28:	68fa      	ldr	r2, [r7, #12]
   43d2a:	69fb      	ldr	r3, [r7, #28]
   43d2c:	429a      	cmp	r2, r3
   43d2e:	d021      	beq.n	43d74 <push+0xb4>
   43d30:	687a      	ldr	r2, [r7, #4]
   43d32:	f44f 43d0 	mov.w	r3, #26624	; 0x6800
   43d36:	f6c0 1389 	movt	r3, #2441	; 0x989
   43d3a:	4413      	add	r3, r2
   43d3c:	681b      	ldr	r3, [r3, #0]
   43d3e:	687a      	ldr	r2, [r7, #4]
   43d40:	011b      	lsls	r3, r3, #4
   43d42:	4413      	add	r3, r2
   43d44:	461c      	mov	r4, r3
   43d46:	f107 032c 	add.w	r3, r7, #44	; 0x2c
   43d4a:	cb0f      	ldmia	r3, {r0, r1, r2, r3}
   43d4c:	e884 000f 	stmia.w	r4, {r0, r1, r2, r3}
   43d50:	687a      	ldr	r2, [r7, #4]
   43d52:	f44f 43d0 	mov.w	r3, #26624	; 0x6800
   43d56:	f6c0 1389 	movt	r3, #2441	; 0x989
   43d5a:	4413      	add	r3, r2
   43d5c:	617b      	str	r3, [r7, #20]
   43d5e:	69fb      	ldr	r3, [r7, #28]
   43d60:	60bb      	str	r3, [r7, #8]
   43d62:	68ba      	ldr	r2, [r7, #8]
   43d64:	697b      	ldr	r3, [r7, #20]
   43d66:	f3bf 8f5b 	dmb	ish
   43d6a:	601a      	str	r2, [r3, #0]
   43d6c:	f3bf 8f5b 	dmb	ish
   43d70:	2301      	movs	r3, #1
   43d72:	e000      	b.n	43d76 <push+0xb6>
   43d74:	2300      	movs	r3, #0
   43d76:	4618      	mov	r0, r3
   43d78:	3720      	adds	r7, #32
   43d7a:	46bd      	mov	sp, r7
   43d7c:	bc90      	pop	{r4, r7}
   43d7e:	b004      	add	sp, #16
   43d80:	4770      	bx	lr

00043d82 <pop>:
   43d82:	b490      	push	{r4, r7}
   43d84:	b08a      	sub	sp, #40	; 0x28
   43d86:	af00      	add	r7, sp, #0
   43d88:	6078      	str	r0, [r7, #4]
   43d8a:	6039      	str	r1, [r7, #0]
   43d8c:	687a      	ldr	r2, [r7, #4]
   43d8e:	f44f 43d0 	mov.w	r3, #26624	; 0x6800
   43d92:	f6c0 1389 	movt	r3, #2441	; 0x989
   43d96:	4413      	add	r3, r2
   43d98:	627b      	str	r3, [r7, #36]	; 0x24
   43d9a:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   43d9c:	f3bf 8f5b 	dmb	ish
   43da0:	681b      	ldr	r3, [r3, #0]
   43da2:	f3bf 8f5b 	dmb	ish
   43da6:	617b      	str	r3, [r7, #20]
   43da8:	697a      	ldr	r2, [r7, #20]
   43daa:	6879      	ldr	r1, [r7, #4]
   43dac:	f646 0304 	movw	r3, #26628	; 0x6804
   43db0:	f6c0 1389 	movt	r3, #2441	; 0x989
   43db4:	440b      	add	r3, r1
   43db6:	623b      	str	r3, [r7, #32]
   43db8:	6a3b      	ldr	r3, [r7, #32]
   43dba:	f3bf 8f5b 	dmb	ish
   43dbe:	681b      	ldr	r3, [r3, #0]
   43dc0:	f3bf 8f5b 	dmb	ish
   43dc4:	613b      	str	r3, [r7, #16]
   43dc6:	693b      	ldr	r3, [r7, #16]
   43dc8:	429a      	cmp	r2, r3
   43dca:	d101      	bne.n	43dd0 <pop+0x4e>
   43dcc:	2300      	movs	r3, #0
   43dce:	e03a      	b.n	43e46 <pop+0xc4>
   43dd0:	687a      	ldr	r2, [r7, #4]
   43dd2:	f646 0304 	movw	r3, #26628	; 0x6804
   43dd6:	f6c0 1389 	movt	r3, #2441	; 0x989
   43dda:	4413      	add	r3, r2
   43ddc:	681b      	ldr	r3, [r3, #0]
   43dde:	6839      	ldr	r1, [r7, #0]
   43de0:	687a      	ldr	r2, [r7, #4]
   43de2:	011b      	lsls	r3, r3, #4
   43de4:	4413      	add	r3, r2
   43de6:	460c      	mov	r4, r1
   43de8:	cb0f      	ldmia	r3, {r0, r1, r2, r3}
   43dea:	e884 000f 	stmia.w	r4, {r0, r1, r2, r3}
   43dee:	687a      	ldr	r2, [r7, #4]
   43df0:	f646 0304 	movw	r3, #26628	; 0x6804
   43df4:	f6c0 1389 	movt	r3, #2441	; 0x989
   43df8:	4413      	add	r3, r2
   43dfa:	61fb      	str	r3, [r7, #28]
   43dfc:	687a      	ldr	r2, [r7, #4]
   43dfe:	f646 0304 	movw	r3, #26628	; 0x6804
   43e02:	f6c0 1389 	movt	r3, #2441	; 0x989
   43e06:	4413      	add	r3, r2
   43e08:	f3bf 8f5b 	dmb	ish
   43e0c:	681b      	ldr	r3, [r3, #0]
   43e0e:	f3bf 8f5b 	dmb	ish
   43e12:	61bb      	str	r3, [r7, #24]
   43e14:	69bb      	ldr	r3, [r7, #24]
   43e16:	1c59      	adds	r1, r3, #1
   43e18:	f64c 236b 	movw	r3, #51819	; 0xca6b
   43e1c:	f6c6 335f 	movt	r3, #27487	; 0x6b5f
   43e20:	fba1 3403 	umull	r3, r4, r1, r3
   43e24:	0da3      	lsrs	r3, r4, #22
   43e26:	f249 6280 	movw	r2, #38528	; 0x9680
   43e2a:	f2c0 0298 	movt	r2, #152	; 0x98
   43e2e:	fb02 f303 	mul.w	r3, r2, r3
   43e32:	1acb      	subs	r3, r1, r3
   43e34:	60fb      	str	r3, [r7, #12]
   43e36:	68fa      	ldr	r2, [r7, #12]
   43e38:	69fb      	ldr	r3, [r7, #28]
   43e3a:	f3bf 8f5b 	dmb	ish
   43e3e:	601a      	str	r2, [r3, #0]
   43e40:	f3bf 8f5b 	dmb	ish
   43e44:	2301      	movs	r3, #1
   43e46:	4618      	mov	r0, r3
   43e48:	3728      	adds	r7, #40	; 0x28
   43e4a:	46bd      	mov	sp, r7
   43e4c:	bc90      	pop	{r4, r7}
   43e4e:	4770      	bx	lr

00043e50 <is_empty>:
   43e50:	b480      	push	{r7}
   43e52:	b085      	sub	sp, #20
   43e54:	af00      	add	r7, sp, #0
   43e56:	6078      	str	r0, [r7, #4]
   43e58:	687a      	ldr	r2, [r7, #4]
   43e5a:	f44f 43d0 	mov.w	r3, #26624	; 0x6800
   43e5e:	f6c0 1389 	movt	r3, #2441	; 0x989
   43e62:	4413      	add	r3, r2
   43e64:	f3bf 8f5b 	dmb	ish
   43e68:	681b      	ldr	r3, [r3, #0]
   43e6a:	f3bf 8f5b 	dmb	ish
   43e6e:	60bb      	str	r3, [r7, #8]
   43e70:	68ba      	ldr	r2, [r7, #8]
   43e72:	6879      	ldr	r1, [r7, #4]
   43e74:	f646 0304 	movw	r3, #26628	; 0x6804
   43e78:	f6c0 1389 	movt	r3, #2441	; 0x989
   43e7c:	440b      	add	r3, r1
   43e7e:	f3bf 8f5b 	dmb	ish
   43e82:	681b      	ldr	r3, [r3, #0]
   43e84:	f3bf 8f5b 	dmb	ish
   43e88:	60fb      	str	r3, [r7, #12]
   43e8a:	68fb      	ldr	r3, [r7, #12]
   43e8c:	429a      	cmp	r2, r3
   43e8e:	bf0c      	ite	eq
   43e90:	2301      	moveq	r3, #1
   43e92:	2300      	movne	r3, #0
   43e94:	b2db      	uxtb	r3, r3
   43e96:	4618      	mov	r0, r3
   43e98:	3714      	adds	r7, #20
   43e9a:	46bd      	mov	sp, r7
   43e9c:	f85d 7b04 	ldr.w	r7, [sp], #4
   43ea0:	4770      	bx	lr

00043ea2 <ringbuffer_init>:
   43ea2:	b480      	push	{r7}
   43ea4:	b087      	sub	sp, #28
   43ea6:	af00      	add	r7, sp, #0
   43ea8:	6078      	str	r0, [r7, #4]
   43eaa:	687a      	ldr	r2, [r7, #4]
   43eac:	f44f 43d0 	mov.w	r3, #26624	; 0x6800
   43eb0:	f6c0 1389 	movt	r3, #2441	; 0x989
   43eb4:	4413      	add	r3, r2
   43eb6:	617b      	str	r3, [r7, #20]
   43eb8:	2300      	movs	r3, #0
   43eba:	60fb      	str	r3, [r7, #12]
   43ebc:	68fa      	ldr	r2, [r7, #12]
   43ebe:	697b      	ldr	r3, [r7, #20]
   43ec0:	601a      	str	r2, [r3, #0]
   43ec2:	687a      	ldr	r2, [r7, #4]
   43ec4:	f646 0304 	movw	r3, #26628	; 0x6804
   43ec8:	f6c0 1389 	movt	r3, #2441	; 0x989
   43ecc:	4413      	add	r3, r2
   43ece:	613b      	str	r3, [r7, #16]
   43ed0:	2300      	movs	r3, #0
   43ed2:	60bb      	str	r3, [r7, #8]
   43ed4:	68ba      	ldr	r2, [r7, #8]
   43ed6:	693b      	ldr	r3, [r7, #16]
   43ed8:	601a      	str	r2, [r3, #0]
   43eda:	2301      	movs	r3, #1
   43edc:	4618      	mov	r0, r3
   43ede:	371c      	adds	r7, #28
   43ee0:	46bd      	mov	sp, r7
   43ee2:	f85d 7b04 	ldr.w	r7, [sp], #4
   43ee6:	4770      	bx	lr

00043ee8 <read_r8>:
   43ee8:	b480      	push	{r7}
   43eea:	b083      	sub	sp, #12
   43eec:	af00      	add	r7, sp, #0
   43eee:	4643      	mov	r3, r8
   43ef0:	607b      	str	r3, [r7, #4]
   43ef2:	687b      	ldr	r3, [r7, #4]
   43ef4:	4618      	mov	r0, r3
   43ef6:	370c      	adds	r7, #12
   43ef8:	46bd      	mov	sp, r7
   43efa:	f85d 7b04 	ldr.w	r7, [sp], #4
   43efe:	4770      	bx	lr

00043f00 <c_direct_tsf_recording>:
   43f00:	b590      	push	{r4, r7, lr}
   43f02:	b08b      	sub	sp, #44	; 0x2c
   43f04:	af02      	add	r7, sp, #8
   43f06:	6078      	str	r0, [r7, #4]
   43f08:	4c20      	ldr	r4, [pc, #128]	; (43f8c <c_direct_tsf_recording+0x8c>)
   43f0a:	447c      	add	r4, pc
   43f0c:	4b20      	ldr	r3, [pc, #128]	; (43f90 <c_direct_tsf_recording+0x90>)
   43f0e:	58e3      	ldr	r3, [r4, r3]
   43f10:	681b      	ldr	r3, [r3, #0]
   43f12:	2b00      	cmp	r3, #0
   43f14:	d109      	bne.n	43f2a <c_direct_tsf_recording+0x2a>
   43f16:	4b1e      	ldr	r3, [pc, #120]	; (43f90 <c_direct_tsf_recording+0x90>)
   43f18:	58e3      	ldr	r3, [r4, r3]
   43f1a:	461a      	mov	r2, r3
   43f1c:	2301      	movs	r3, #1
   43f1e:	6013      	str	r3, [r2, #0]
   43f20:	4b1c      	ldr	r3, [pc, #112]	; (43f94 <c_direct_tsf_recording+0x94>)
   43f22:	58e3      	ldr	r3, [r4, r3]
   43f24:	4618      	mov	r0, r3
   43f26:	f7ff ffbc 	bl	43ea2 <ringbuffer_init>
   43f2a:	f7ff ffdd 	bl	43ee8 <read_r8>
   43f2e:	61f8      	str	r0, [r7, #28]
   43f30:	687b      	ldr	r3, [r7, #4]
   43f32:	3308      	adds	r3, #8
   43f34:	60fb      	str	r3, [r7, #12]
   43f36:	69fb      	ldr	r3, [r7, #28]
   43f38:	613b      	str	r3, [r7, #16]
   43f3a:	230a      	movs	r3, #10
   43f3c:	763b      	strb	r3, [r7, #24]
   43f3e:	4b16      	ldr	r3, [pc, #88]	; (43f98 <c_direct_tsf_recording+0x98>)
   43f40:	58e3      	ldr	r3, [r4, r3]
   43f42:	681b      	ldr	r3, [r3, #0]
   43f44:	2b00      	cmp	r3, #0
   43f46:	d01c      	beq.n	43f82 <c_direct_tsf_recording+0x82>
   43f48:	69fb      	ldr	r3, [r7, #28]
   43f4a:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   43f4e:	d903      	bls.n	43f58 <c_direct_tsf_recording+0x58>
   43f50:	687b      	ldr	r3, [r7, #4]
   43f52:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   43f56:	d814      	bhi.n	43f82 <c_direct_tsf_recording+0x82>
   43f58:	69bb      	ldr	r3, [r7, #24]
   43f5a:	9300      	str	r3, [sp, #0]
   43f5c:	f107 030c 	add.w	r3, r7, #12
   43f60:	cb0e      	ldmia	r3, {r1, r2, r3}
   43f62:	480c      	ldr	r0, [pc, #48]	; (43f94 <c_direct_tsf_recording+0x94>)
   43f64:	5820      	ldr	r0, [r4, r0]
   43f66:	f7ff feab 	bl	43cc0 <push>
   43f6a:	4603      	mov	r3, r0
   43f6c:	f083 0301 	eor.w	r3, r3, #1
   43f70:	b2db      	uxtb	r3, r3
   43f72:	2b00      	cmp	r3, #0
   43f74:	d005      	beq.n	43f82 <c_direct_tsf_recording+0x82>
   43f76:	4b09      	ldr	r3, [pc, #36]	; (43f9c <c_direct_tsf_recording+0x9c>)
   43f78:	447b      	add	r3, pc
   43f7a:	4618      	mov	r0, r3
   43f7c:	f7cc ed1a 	blx	109b4 <puts@plt>
   43f80:	bf00      	nop
   43f82:	bf00      	nop
   43f84:	3724      	adds	r7, #36	; 0x24
   43f86:	46bd      	mov	sp, r7
   43f88:	bd90      	pop	{r4, r7, pc}
   43f8a:	bf00      	nop
   43f8c:	000130f2 	strdeq	r3, [r1], -r2
   43f90:	00000094 	muleq	r0, r4, r0
   43f94:	000000ac 	andeq	r0, r0, ip, lsr #1
   43f98:	000000b4 	strheq	r0, [r0], -r4
   43f9c:	00002814 	andeq	r2, r0, r4, lsl r8

00043fa0 <isBranchTaken>:
   43fa0:	b480      	push	{r7}
   43fa2:	b085      	sub	sp, #20
   43fa4:	af00      	add	r7, sp, #0
   43fa6:	6078      	str	r0, [r7, #4]
   43fa8:	6039      	str	r1, [r7, #0]
   43faa:	683b      	ldr	r3, [r7, #0]
   43fac:	f003 4300 	and.w	r3, r3, #2147483648	; 0x80000000
   43fb0:	2b00      	cmp	r3, #0
   43fb2:	bf14      	ite	ne
   43fb4:	2301      	movne	r3, #1
   43fb6:	2300      	moveq	r3, #0
   43fb8:	73fb      	strb	r3, [r7, #15]
   43fba:	683b      	ldr	r3, [r7, #0]
   43fbc:	f003 4380 	and.w	r3, r3, #1073741824	; 0x40000000
   43fc0:	2b00      	cmp	r3, #0
   43fc2:	bf14      	ite	ne
   43fc4:	2301      	movne	r3, #1
   43fc6:	2300      	moveq	r3, #0
   43fc8:	73bb      	strb	r3, [r7, #14]
   43fca:	683b      	ldr	r3, [r7, #0]
   43fcc:	f003 5300 	and.w	r3, r3, #536870912	; 0x20000000
   43fd0:	2b00      	cmp	r3, #0
   43fd2:	bf14      	ite	ne
   43fd4:	2301      	movne	r3, #1
   43fd6:	2300      	moveq	r3, #0
   43fd8:	737b      	strb	r3, [r7, #13]
   43fda:	683b      	ldr	r3, [r7, #0]
   43fdc:	f003 5380 	and.w	r3, r3, #268435456	; 0x10000000
   43fe0:	2b00      	cmp	r3, #0
   43fe2:	bf14      	ite	ne
   43fe4:	2301      	movne	r3, #1
   43fe6:	2300      	moveq	r3, #0
   43fe8:	733b      	strb	r3, [r7, #12]
   43fea:	687b      	ldr	r3, [r7, #4]
   43fec:	2b0e      	cmp	r3, #14
   43fee:	f200 80b0 	bhi.w	44152 <isBranchTaken+0x1b2>
   43ff2:	a202      	add	r2, pc, #8	; (adr r2, 43ffc <isBranchTaken+0x5c>)
   43ff4:	f852 3023 	ldr.w	r3, [r2, r3, lsl #2]
   43ff8:	441a      	add	r2, r3
   43ffa:	4710      	bx	r2
   43ffc:	0000003d 	andeq	r0, r0, sp, lsr r0
   44000:	00000041 	andeq	r0, r0, r1, asr #32
   44004:	0000005b 	andeq	r0, r0, fp, asr r0
   44008:	0000005f 	andeq	r0, r0, pc, asr r0
   4400c:	00000079 	andeq	r0, r0, r9, ror r0
   44010:	0000007d 	andeq	r0, r0, sp, ror r0
   44014:	00000097 	muleq	r0, r7, r0
   44018:	0000009b 	muleq	r0, fp, r0
   4401c:	000000b5 	strheq	r0, [r0], -r5
   44020:	000000d5 	ldrdeq	r0, [r0], -r5
   44024:	000000f5 	strdeq	r0, [r0], -r5
   44028:	00000105 	andeq	r0, r0, r5, lsl #2
   4402c:	00000115 	andeq	r0, r0, r5, lsl r1
   44030:	00000137 	andeq	r0, r0, r7, lsr r1
   44034:	00000153 	andeq	r0, r0, r3, asr r1
   44038:	7bbb      	ldrb	r3, [r7, #14]
   4403a:	e08b      	b.n	44154 <isBranchTaken+0x1b4>
   4403c:	7bbb      	ldrb	r3, [r7, #14]
   4403e:	2b00      	cmp	r3, #0
   44040:	bf14      	ite	ne
   44042:	2301      	movne	r3, #1
   44044:	2300      	moveq	r3, #0
   44046:	b2db      	uxtb	r3, r3
   44048:	f083 0301 	eor.w	r3, r3, #1
   4404c:	b2db      	uxtb	r3, r3
   4404e:	f003 0301 	and.w	r3, r3, #1
   44052:	b2db      	uxtb	r3, r3
   44054:	e07e      	b.n	44154 <isBranchTaken+0x1b4>
   44056:	7b7b      	ldrb	r3, [r7, #13]
   44058:	e07c      	b.n	44154 <isBranchTaken+0x1b4>
   4405a:	7b7b      	ldrb	r3, [r7, #13]
   4405c:	2b00      	cmp	r3, #0
   4405e:	bf14      	ite	ne
   44060:	2301      	movne	r3, #1
   44062:	2300      	moveq	r3, #0
   44064:	b2db      	uxtb	r3, r3
   44066:	f083 0301 	eor.w	r3, r3, #1
   4406a:	b2db      	uxtb	r3, r3
   4406c:	f003 0301 	and.w	r3, r3, #1
   44070:	b2db      	uxtb	r3, r3
   44072:	e06f      	b.n	44154 <isBranchTaken+0x1b4>
   44074:	7bfb      	ldrb	r3, [r7, #15]
   44076:	e06d      	b.n	44154 <isBranchTaken+0x1b4>
   44078:	7bfb      	ldrb	r3, [r7, #15]
   4407a:	2b00      	cmp	r3, #0
   4407c:	bf14      	ite	ne
   4407e:	2301      	movne	r3, #1
   44080:	2300      	moveq	r3, #0
   44082:	b2db      	uxtb	r3, r3
   44084:	f083 0301 	eor.w	r3, r3, #1
   44088:	b2db      	uxtb	r3, r3
   4408a:	f003 0301 	and.w	r3, r3, #1
   4408e:	b2db      	uxtb	r3, r3
   44090:	e060      	b.n	44154 <isBranchTaken+0x1b4>
   44092:	7b3b      	ldrb	r3, [r7, #12]
   44094:	e05e      	b.n	44154 <isBranchTaken+0x1b4>
   44096:	7b3b      	ldrb	r3, [r7, #12]
   44098:	2b00      	cmp	r3, #0
   4409a:	bf14      	ite	ne
   4409c:	2301      	movne	r3, #1
   4409e:	2300      	moveq	r3, #0
   440a0:	b2db      	uxtb	r3, r3
   440a2:	f083 0301 	eor.w	r3, r3, #1
   440a6:	b2db      	uxtb	r3, r3
   440a8:	f003 0301 	and.w	r3, r3, #1
   440ac:	b2db      	uxtb	r3, r3
   440ae:	e051      	b.n	44154 <isBranchTaken+0x1b4>
   440b0:	7b7b      	ldrb	r3, [r7, #13]
   440b2:	2b00      	cmp	r3, #0
   440b4:	d007      	beq.n	440c6 <isBranchTaken+0x126>
   440b6:	7bbb      	ldrb	r3, [r7, #14]
   440b8:	f083 0301 	eor.w	r3, r3, #1
   440bc:	b2db      	uxtb	r3, r3
   440be:	2b00      	cmp	r3, #0
   440c0:	d001      	beq.n	440c6 <isBranchTaken+0x126>
   440c2:	2301      	movs	r3, #1
   440c4:	e000      	b.n	440c8 <isBranchTaken+0x128>
   440c6:	2300      	movs	r3, #0
   440c8:	f003 0301 	and.w	r3, r3, #1
   440cc:	b2db      	uxtb	r3, r3
   440ce:	e041      	b.n	44154 <isBranchTaken+0x1b4>
   440d0:	7b7b      	ldrb	r3, [r7, #13]
   440d2:	f083 0301 	eor.w	r3, r3, #1
   440d6:	b2db      	uxtb	r3, r3
   440d8:	2b00      	cmp	r3, #0
   440da:	d102      	bne.n	440e2 <isBranchTaken+0x142>
   440dc:	7bbb      	ldrb	r3, [r7, #14]
   440de:	2b00      	cmp	r3, #0
   440e0:	d001      	beq.n	440e6 <isBranchTaken+0x146>
   440e2:	2301      	movs	r3, #1
   440e4:	e000      	b.n	440e8 <isBranchTaken+0x148>
   440e6:	2300      	movs	r3, #0
   440e8:	f003 0301 	and.w	r3, r3, #1
   440ec:	b2db      	uxtb	r3, r3
   440ee:	e031      	b.n	44154 <isBranchTaken+0x1b4>
   440f0:	7bfa      	ldrb	r2, [r7, #15]
   440f2:	7b3b      	ldrb	r3, [r7, #12]
   440f4:	429a      	cmp	r2, r3
   440f6:	bf0c      	ite	eq
   440f8:	2301      	moveq	r3, #1
   440fa:	2300      	movne	r3, #0
   440fc:	b2db      	uxtb	r3, r3
   440fe:	e029      	b.n	44154 <isBranchTaken+0x1b4>
   44100:	7bfa      	ldrb	r2, [r7, #15]
   44102:	7b3b      	ldrb	r3, [r7, #12]
   44104:	429a      	cmp	r2, r3
   44106:	bf14      	ite	ne
   44108:	2301      	movne	r3, #1
   4410a:	2300      	moveq	r3, #0
   4410c:	b2db      	uxtb	r3, r3
   4410e:	e021      	b.n	44154 <isBranchTaken+0x1b4>
   44110:	7bbb      	ldrb	r3, [r7, #14]
   44112:	f083 0301 	eor.w	r3, r3, #1
   44116:	b2db      	uxtb	r3, r3
   44118:	2b00      	cmp	r3, #0
   4411a:	d005      	beq.n	44128 <isBranchTaken+0x188>
   4411c:	7bfa      	ldrb	r2, [r7, #15]
   4411e:	7b3b      	ldrb	r3, [r7, #12]
   44120:	429a      	cmp	r2, r3
   44122:	d101      	bne.n	44128 <isBranchTaken+0x188>
   44124:	2301      	movs	r3, #1
   44126:	e000      	b.n	4412a <isBranchTaken+0x18a>
   44128:	2300      	movs	r3, #0
   4412a:	f003 0301 	and.w	r3, r3, #1
   4412e:	b2db      	uxtb	r3, r3
   44130:	e010      	b.n	44154 <isBranchTaken+0x1b4>
   44132:	7bbb      	ldrb	r3, [r7, #14]
   44134:	2b00      	cmp	r3, #0
   44136:	d103      	bne.n	44140 <isBranchTaken+0x1a0>
   44138:	7bfa      	ldrb	r2, [r7, #15]
   4413a:	7b3b      	ldrb	r3, [r7, #12]
   4413c:	429a      	cmp	r2, r3
   4413e:	d001      	beq.n	44144 <isBranchTaken+0x1a4>
   44140:	2301      	movs	r3, #1
   44142:	e000      	b.n	44146 <isBranchTaken+0x1a6>
   44144:	2300      	movs	r3, #0
   44146:	f003 0301 	and.w	r3, r3, #1
   4414a:	b2db      	uxtb	r3, r3
   4414c:	e002      	b.n	44154 <isBranchTaken+0x1b4>
   4414e:	2301      	movs	r3, #1
   44150:	e000      	b.n	44154 <isBranchTaken+0x1b4>
   44152:	2300      	movs	r3, #0
   44154:	4618      	mov	r0, r3
   44156:	3714      	adds	r7, #20
   44158:	46bd      	mov	sp, r7
   4415a:	f85d 7b04 	ldr.w	r7, [sp], #4
   4415e:	4770      	bx	lr

00044160 <c_direct_tsf_cc_recording>:
   44160:	b590      	push	{r4, r7, lr}
   44162:	b091      	sub	sp, #68	; 0x44
   44164:	af02      	add	r7, sp, #8
   44166:	60f8      	str	r0, [r7, #12]
   44168:	60b9      	str	r1, [r7, #8]
   4416a:	607a      	str	r2, [r7, #4]
   4416c:	4c3d      	ldr	r4, [pc, #244]	; (44264 <c_direct_tsf_cc_recording+0x104>)
   4416e:	447c      	add	r4, pc
   44170:	4b3d      	ldr	r3, [pc, #244]	; (44268 <c_direct_tsf_cc_recording+0x108>)
   44172:	58e3      	ldr	r3, [r4, r3]
   44174:	681b      	ldr	r3, [r3, #0]
   44176:	2b00      	cmp	r3, #0
   44178:	d109      	bne.n	4418e <c_direct_tsf_cc_recording+0x2e>
   4417a:	4b3b      	ldr	r3, [pc, #236]	; (44268 <c_direct_tsf_cc_recording+0x108>)
   4417c:	58e3      	ldr	r3, [r4, r3]
   4417e:	461a      	mov	r2, r3
   44180:	2301      	movs	r3, #1
   44182:	6013      	str	r3, [r2, #0]
   44184:	4b39      	ldr	r3, [pc, #228]	; (4426c <c_direct_tsf_cc_recording+0x10c>)
   44186:	58e3      	ldr	r3, [r4, r3]
   44188:	4618      	mov	r0, r3
   4418a:	f7ff fe8a 	bl	43ea2 <ringbuffer_init>
   4418e:	68b9      	ldr	r1, [r7, #8]
   44190:	6878      	ldr	r0, [r7, #4]
   44192:	f7ff ff05 	bl	43fa0 <isBranchTaken>
   44196:	4603      	mov	r3, r0
   44198:	f887 3037 	strb.w	r3, [r7, #55]	; 0x37
   4419c:	f7ff fea4 	bl	43ee8 <read_r8>
   441a0:	6338      	str	r0, [r7, #48]	; 0x30
   441a2:	68fb      	ldr	r3, [r7, #12]
   441a4:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   441a8:	d822      	bhi.n	441f0 <c_direct_tsf_cc_recording+0x90>
   441aa:	68fb      	ldr	r3, [r7, #12]
   441ac:	613b      	str	r3, [r7, #16]
   441ae:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   441b0:	617b      	str	r3, [r7, #20]
   441b2:	f897 3037 	ldrb.w	r3, [r7, #55]	; 0x37
   441b6:	61bb      	str	r3, [r7, #24]
   441b8:	2304      	movs	r3, #4
   441ba:	773b      	strb	r3, [r7, #28]
   441bc:	4b2c      	ldr	r3, [pc, #176]	; (44270 <c_direct_tsf_cc_recording+0x110>)
   441be:	58e3      	ldr	r3, [r4, r3]
   441c0:	681b      	ldr	r3, [r3, #0]
   441c2:	2b00      	cmp	r3, #0
   441c4:	d01b      	beq.n	441fe <c_direct_tsf_cc_recording+0x9e>
   441c6:	69fb      	ldr	r3, [r7, #28]
   441c8:	9300      	str	r3, [sp, #0]
   441ca:	f107 0310 	add.w	r3, r7, #16
   441ce:	cb0e      	ldmia	r3, {r1, r2, r3}
   441d0:	4826      	ldr	r0, [pc, #152]	; (4426c <c_direct_tsf_cc_recording+0x10c>)
   441d2:	5820      	ldr	r0, [r4, r0]
   441d4:	f7ff fd74 	bl	43cc0 <push>
   441d8:	4603      	mov	r3, r0
   441da:	f083 0301 	eor.w	r3, r3, #1
   441de:	b2db      	uxtb	r3, r3
   441e0:	2b00      	cmp	r3, #0
   441e2:	d00c      	beq.n	441fe <c_direct_tsf_cc_recording+0x9e>
   441e4:	4b23      	ldr	r3, [pc, #140]	; (44274 <c_direct_tsf_cc_recording+0x114>)
   441e6:	447b      	add	r3, pc
   441e8:	4618      	mov	r0, r3
   441ea:	f7cc ebe4 	blx	109b4 <puts@plt>
   441ee:	e006      	b.n	441fe <c_direct_tsf_cc_recording+0x9e>
   441f0:	f897 3037 	ldrb.w	r3, [r7, #55]	; 0x37
   441f4:	f083 0301 	eor.w	r3, r3, #1
   441f8:	b2db      	uxtb	r3, r3
   441fa:	2b00      	cmp	r3, #0
   441fc:	d12b      	bne.n	44256 <c_direct_tsf_cc_recording+0xf6>
   441fe:	68fb      	ldr	r3, [r7, #12]
   44200:	623b      	str	r3, [r7, #32]
   44202:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   44204:	627b      	str	r3, [r7, #36]	; 0x24
   44206:	68bb      	ldr	r3, [r7, #8]
   44208:	62bb      	str	r3, [r7, #40]	; 0x28
   4420a:	230a      	movs	r3, #10
   4420c:	f887 302c 	strb.w	r3, [r7, #44]	; 0x2c
   44210:	4b17      	ldr	r3, [pc, #92]	; (44270 <c_direct_tsf_cc_recording+0x110>)
   44212:	58e3      	ldr	r3, [r4, r3]
   44214:	681b      	ldr	r3, [r3, #0]
   44216:	2b00      	cmp	r3, #0
   44218:	d01f      	beq.n	4425a <c_direct_tsf_cc_recording+0xfa>
   4421a:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   4421c:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   44220:	d903      	bls.n	4422a <c_direct_tsf_cc_recording+0xca>
   44222:	68fb      	ldr	r3, [r7, #12]
   44224:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   44228:	d817      	bhi.n	4425a <c_direct_tsf_cc_recording+0xfa>
   4422a:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   4422c:	9300      	str	r3, [sp, #0]
   4422e:	f107 0320 	add.w	r3, r7, #32
   44232:	cb0e      	ldmia	r3, {r1, r2, r3}
   44234:	480d      	ldr	r0, [pc, #52]	; (4426c <c_direct_tsf_cc_recording+0x10c>)
   44236:	5820      	ldr	r0, [r4, r0]
   44238:	f7ff fd42 	bl	43cc0 <push>
   4423c:	4603      	mov	r3, r0
   4423e:	f083 0301 	eor.w	r3, r3, #1
   44242:	b2db      	uxtb	r3, r3
   44244:	2b00      	cmp	r3, #0
   44246:	d008      	beq.n	4425a <c_direct_tsf_cc_recording+0xfa>
   44248:	4b0b      	ldr	r3, [pc, #44]	; (44278 <c_direct_tsf_cc_recording+0x118>)
   4424a:	447b      	add	r3, pc
   4424c:	4618      	mov	r0, r3
   4424e:	f7cc ebb2 	blx	109b4 <puts@plt>
   44252:	bf00      	nop
   44254:	e001      	b.n	4425a <c_direct_tsf_cc_recording+0xfa>
   44256:	bf00      	nop
   44258:	e000      	b.n	4425c <c_direct_tsf_cc_recording+0xfc>
   4425a:	bf00      	nop
   4425c:	373c      	adds	r7, #60	; 0x3c
   4425e:	46bd      	mov	sp, r7
   44260:	bd90      	pop	{r4, r7, pc}
   44262:	bf00      	nop
   44264:	00012e8e 	andeq	r2, r1, lr, lsl #29
   44268:	00000094 	muleq	r0, r4, r0
   4426c:	000000ac 	andeq	r0, r0, ip, lsr #1
   44270:	000000b4 	strheq	r0, [r0], -r4
   44274:	000025a6 	andeq	r2, r0, r6, lsr #11
   44278:	00002542 	andeq	r2, r0, r2, asr #10

0004427c <c_direct_tsf_bcc_recording>:
   4427c:	b590      	push	{r4, r7, lr}
   4427e:	b091      	sub	sp, #68	; 0x44
   44280:	af02      	add	r7, sp, #8
   44282:	60f8      	str	r0, [r7, #12]
   44284:	60b9      	str	r1, [r7, #8]
   44286:	607a      	str	r2, [r7, #4]
   44288:	4c3f      	ldr	r4, [pc, #252]	; (44388 <c_direct_tsf_bcc_recording+0x10c>)
   4428a:	447c      	add	r4, pc
   4428c:	4b3f      	ldr	r3, [pc, #252]	; (4438c <c_direct_tsf_bcc_recording+0x110>)
   4428e:	58e3      	ldr	r3, [r4, r3]
   44290:	681b      	ldr	r3, [r3, #0]
   44292:	2b00      	cmp	r3, #0
   44294:	d109      	bne.n	442aa <c_direct_tsf_bcc_recording+0x2e>
   44296:	4b3d      	ldr	r3, [pc, #244]	; (4438c <c_direct_tsf_bcc_recording+0x110>)
   44298:	58e3      	ldr	r3, [r4, r3]
   4429a:	461a      	mov	r2, r3
   4429c:	2301      	movs	r3, #1
   4429e:	6013      	str	r3, [r2, #0]
   442a0:	4b3b      	ldr	r3, [pc, #236]	; (44390 <c_direct_tsf_bcc_recording+0x114>)
   442a2:	58e3      	ldr	r3, [r4, r3]
   442a4:	4618      	mov	r0, r3
   442a6:	f7ff fdfc 	bl	43ea2 <ringbuffer_init>
   442aa:	68b9      	ldr	r1, [r7, #8]
   442ac:	6878      	ldr	r0, [r7, #4]
   442ae:	f7ff fe77 	bl	43fa0 <isBranchTaken>
   442b2:	4603      	mov	r3, r0
   442b4:	f887 3037 	strb.w	r3, [r7, #55]	; 0x37
   442b8:	f7ff fe16 	bl	43ee8 <read_r8>
   442bc:	6338      	str	r0, [r7, #48]	; 0x30
   442be:	68fb      	ldr	r3, [r7, #12]
   442c0:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   442c4:	d825      	bhi.n	44312 <c_direct_tsf_bcc_recording+0x96>
   442c6:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   442c8:	2b64      	cmp	r3, #100	; 0x64
   442ca:	d122      	bne.n	44312 <c_direct_tsf_bcc_recording+0x96>
   442cc:	68fb      	ldr	r3, [r7, #12]
   442ce:	613b      	str	r3, [r7, #16]
   442d0:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   442d2:	617b      	str	r3, [r7, #20]
   442d4:	f897 3037 	ldrb.w	r3, [r7, #55]	; 0x37
   442d8:	61bb      	str	r3, [r7, #24]
   442da:	2304      	movs	r3, #4
   442dc:	773b      	strb	r3, [r7, #28]
   442de:	4b2d      	ldr	r3, [pc, #180]	; (44394 <c_direct_tsf_bcc_recording+0x118>)
   442e0:	58e3      	ldr	r3, [r4, r3]
   442e2:	681b      	ldr	r3, [r3, #0]
   442e4:	2b00      	cmp	r3, #0
   442e6:	d01c      	beq.n	44322 <c_direct_tsf_bcc_recording+0xa6>
   442e8:	69fb      	ldr	r3, [r7, #28]
   442ea:	9300      	str	r3, [sp, #0]
   442ec:	f107 0310 	add.w	r3, r7, #16
   442f0:	cb0e      	ldmia	r3, {r1, r2, r3}
   442f2:	4827      	ldr	r0, [pc, #156]	; (44390 <c_direct_tsf_bcc_recording+0x114>)
   442f4:	5820      	ldr	r0, [r4, r0]
   442f6:	f7ff fce3 	bl	43cc0 <push>
   442fa:	4603      	mov	r3, r0
   442fc:	f083 0301 	eor.w	r3, r3, #1
   44300:	b2db      	uxtb	r3, r3
   44302:	2b00      	cmp	r3, #0
   44304:	d00d      	beq.n	44322 <c_direct_tsf_bcc_recording+0xa6>
   44306:	4b24      	ldr	r3, [pc, #144]	; (44398 <c_direct_tsf_bcc_recording+0x11c>)
   44308:	447b      	add	r3, pc
   4430a:	4618      	mov	r0, r3
   4430c:	f7cc eb52 	blx	109b4 <puts@plt>
   44310:	e007      	b.n	44322 <c_direct_tsf_bcc_recording+0xa6>
   44312:	f897 3037 	ldrb.w	r3, [r7, #55]	; 0x37
   44316:	f083 0301 	eor.w	r3, r3, #1
   4431a:	b2db      	uxtb	r3, r3
   4431c:	2b00      	cmp	r3, #0
   4431e:	d12d      	bne.n	4437c <c_direct_tsf_bcc_recording+0x100>
   44320:	e000      	b.n	44324 <c_direct_tsf_bcc_recording+0xa8>
   44322:	bf00      	nop
   44324:	68fb      	ldr	r3, [r7, #12]
   44326:	623b      	str	r3, [r7, #32]
   44328:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   4432a:	627b      	str	r3, [r7, #36]	; 0x24
   4432c:	68bb      	ldr	r3, [r7, #8]
   4432e:	62bb      	str	r3, [r7, #40]	; 0x28
   44330:	230a      	movs	r3, #10
   44332:	f887 302c 	strb.w	r3, [r7, #44]	; 0x2c
   44336:	4b17      	ldr	r3, [pc, #92]	; (44394 <c_direct_tsf_bcc_recording+0x118>)
   44338:	58e3      	ldr	r3, [r4, r3]
   4433a:	681b      	ldr	r3, [r3, #0]
   4433c:	2b00      	cmp	r3, #0
   4433e:	d01f      	beq.n	44380 <c_direct_tsf_bcc_recording+0x104>
   44340:	6b3b      	ldr	r3, [r7, #48]	; 0x30
   44342:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   44346:	d903      	bls.n	44350 <c_direct_tsf_bcc_recording+0xd4>
   44348:	68fb      	ldr	r3, [r7, #12]
   4434a:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   4434e:	d817      	bhi.n	44380 <c_direct_tsf_bcc_recording+0x104>
   44350:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   44352:	9300      	str	r3, [sp, #0]
   44354:	f107 0320 	add.w	r3, r7, #32
   44358:	cb0e      	ldmia	r3, {r1, r2, r3}
   4435a:	480d      	ldr	r0, [pc, #52]	; (44390 <c_direct_tsf_bcc_recording+0x114>)
   4435c:	5820      	ldr	r0, [r4, r0]
   4435e:	f7ff fcaf 	bl	43cc0 <push>
   44362:	4603      	mov	r3, r0
   44364:	f083 0301 	eor.w	r3, r3, #1
   44368:	b2db      	uxtb	r3, r3
   4436a:	2b00      	cmp	r3, #0
   4436c:	d008      	beq.n	44380 <c_direct_tsf_bcc_recording+0x104>
   4436e:	4b0b      	ldr	r3, [pc, #44]	; (4439c <c_direct_tsf_bcc_recording+0x120>)
   44370:	447b      	add	r3, pc
   44372:	4618      	mov	r0, r3
   44374:	f7cc eb1e 	blx	109b4 <puts@plt>
   44378:	bf00      	nop
   4437a:	e001      	b.n	44380 <c_direct_tsf_bcc_recording+0x104>
   4437c:	bf00      	nop
   4437e:	e000      	b.n	44382 <c_direct_tsf_bcc_recording+0x106>
   44380:	bf00      	nop
   44382:	373c      	adds	r7, #60	; 0x3c
   44384:	46bd      	mov	sp, r7
   44386:	bd90      	pop	{r4, r7, pc}
   44388:	00012d72 	andeq	r2, r1, r2, ror sp
   4438c:	00000094 	muleq	r0, r4, r0
   44390:	000000ac 	andeq	r0, r0, ip, lsr #1
   44394:	000000b4 	strheq	r0, [r0], -r4
   44398:	00002484 	andeq	r2, r0, r4, lsl #9
   4439c:	0000241c 	andeq	r2, r0, ip, lsl r4

000443a0 <c_indirect_tsf_recording>:
   443a0:	b590      	push	{r4, r7, lr}
   443a2:	b08b      	sub	sp, #44	; 0x2c
   443a4:	af02      	add	r7, sp, #8
   443a6:	6078      	str	r0, [r7, #4]
   443a8:	4c23      	ldr	r4, [pc, #140]	; (44438 <c_indirect_tsf_recording+0x98>)
   443aa:	447c      	add	r4, pc
   443ac:	4b23      	ldr	r3, [pc, #140]	; (4443c <c_indirect_tsf_recording+0x9c>)
   443ae:	58e3      	ldr	r3, [r4, r3]
   443b0:	681b      	ldr	r3, [r3, #0]
   443b2:	2b00      	cmp	r3, #0
   443b4:	d109      	bne.n	443ca <c_indirect_tsf_recording+0x2a>
   443b6:	4b21      	ldr	r3, [pc, #132]	; (4443c <c_indirect_tsf_recording+0x9c>)
   443b8:	58e3      	ldr	r3, [r4, r3]
   443ba:	461a      	mov	r2, r3
   443bc:	2301      	movs	r3, #1
   443be:	6013      	str	r3, [r2, #0]
   443c0:	4b1f      	ldr	r3, [pc, #124]	; (44440 <c_indirect_tsf_recording+0xa0>)
   443c2:	58e3      	ldr	r3, [r4, r3]
   443c4:	4618      	mov	r0, r3
   443c6:	f7ff fd6c 	bl	43ea2 <ringbuffer_init>
   443ca:	f7ff fd8d 	bl	43ee8 <read_r8>
   443ce:	61f8      	str	r0, [r7, #28]
   443d0:	687b      	ldr	r3, [r7, #4]
   443d2:	60fb      	str	r3, [r7, #12]
   443d4:	69fb      	ldr	r3, [r7, #28]
   443d6:	613b      	str	r3, [r7, #16]
   443d8:	230a      	movs	r3, #10
   443da:	763b      	strb	r3, [r7, #24]
   443dc:	4b19      	ldr	r3, [pc, #100]	; (44444 <c_indirect_tsf_recording+0xa4>)
   443de:	58e3      	ldr	r3, [r4, r3]
   443e0:	681b      	ldr	r3, [r3, #0]
   443e2:	2b00      	cmp	r3, #0
   443e4:	d024      	beq.n	44430 <c_indirect_tsf_recording+0x90>
   443e6:	69fb      	ldr	r3, [r7, #28]
   443e8:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   443ec:	d803      	bhi.n	443f6 <c_indirect_tsf_recording+0x56>
   443ee:	687b      	ldr	r3, [r7, #4]
   443f0:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   443f4:	d807      	bhi.n	44406 <c_indirect_tsf_recording+0x66>
   443f6:	69fb      	ldr	r3, [r7, #28]
   443f8:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   443fc:	d918      	bls.n	44430 <c_indirect_tsf_recording+0x90>
   443fe:	687b      	ldr	r3, [r7, #4]
   44400:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   44404:	d814      	bhi.n	44430 <c_indirect_tsf_recording+0x90>
   44406:	69bb      	ldr	r3, [r7, #24]
   44408:	9300      	str	r3, [sp, #0]
   4440a:	f107 030c 	add.w	r3, r7, #12
   4440e:	cb0e      	ldmia	r3, {r1, r2, r3}
   44410:	480b      	ldr	r0, [pc, #44]	; (44440 <c_indirect_tsf_recording+0xa0>)
   44412:	5820      	ldr	r0, [r4, r0]
   44414:	f7ff fc54 	bl	43cc0 <push>
   44418:	4603      	mov	r3, r0
   4441a:	f083 0301 	eor.w	r3, r3, #1
   4441e:	b2db      	uxtb	r3, r3
   44420:	2b00      	cmp	r3, #0
   44422:	d005      	beq.n	44430 <c_indirect_tsf_recording+0x90>
   44424:	4b08      	ldr	r3, [pc, #32]	; (44448 <c_indirect_tsf_recording+0xa8>)
   44426:	447b      	add	r3, pc
   44428:	4618      	mov	r0, r3
   4442a:	f7cc eac4 	blx	109b4 <puts@plt>
   4442e:	bf00      	nop
   44430:	bf00      	nop
   44432:	3724      	adds	r7, #36	; 0x24
   44434:	46bd      	mov	sp, r7
   44436:	bd90      	pop	{r4, r7, pc}
   44438:	00012c52 	andeq	r2, r1, r2, asr ip
   4443c:	00000094 	muleq	r0, r4, r0
   44440:	000000ac 	andeq	r0, r0, ip, lsr #1
   44444:	000000b4 	strheq	r0, [r0], -r4
   44448:	00002366 	andeq	r2, r0, r6, ror #6

0004444c <c_tsf_bx_lr_recording>:
   4444c:	b590      	push	{r4, r7, lr}
   4444e:	b08b      	sub	sp, #44	; 0x2c
   44450:	af02      	add	r7, sp, #8
   44452:	6078      	str	r0, [r7, #4]
   44454:	4c2e      	ldr	r4, [pc, #184]	; (44510 <c_tsf_bx_lr_recording+0xc4>)
   44456:	447c      	add	r4, pc
   44458:	4b2e      	ldr	r3, [pc, #184]	; (44514 <c_tsf_bx_lr_recording+0xc8>)
   4445a:	58e3      	ldr	r3, [r4, r3]
   4445c:	681b      	ldr	r3, [r3, #0]
   4445e:	2b00      	cmp	r3, #0
   44460:	d109      	bne.n	44476 <c_tsf_bx_lr_recording+0x2a>
   44462:	4b2c      	ldr	r3, [pc, #176]	; (44514 <c_tsf_bx_lr_recording+0xc8>)
   44464:	58e3      	ldr	r3, [r4, r3]
   44466:	461a      	mov	r2, r3
   44468:	2301      	movs	r3, #1
   4446a:	6013      	str	r3, [r2, #0]
   4446c:	4b2a      	ldr	r3, [pc, #168]	; (44518 <c_tsf_bx_lr_recording+0xcc>)
   4446e:	58e3      	ldr	r3, [r4, r3]
   44470:	4618      	mov	r0, r3
   44472:	f7ff fd16 	bl	43ea2 <ringbuffer_init>
   44476:	f7ff fd37 	bl	43ee8 <read_r8>
   4447a:	61f8      	str	r0, [r7, #28]
   4447c:	687b      	ldr	r3, [r7, #4]
   4447e:	60fb      	str	r3, [r7, #12]
   44480:	69fb      	ldr	r3, [r7, #28]
   44482:	613b      	str	r3, [r7, #16]
   44484:	4b25      	ldr	r3, [pc, #148]	; (4451c <c_tsf_bx_lr_recording+0xd0>)
   44486:	58e3      	ldr	r3, [r4, r3]
   44488:	681b      	ldr	r3, [r3, #0]
   4448a:	2b00      	cmp	r3, #0
   4448c:	d03c      	beq.n	44508 <c_tsf_bx_lr_recording+0xbc>
   4448e:	69fb      	ldr	r3, [r7, #28]
   44490:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   44494:	d919      	bls.n	444ca <c_tsf_bx_lr_recording+0x7e>
   44496:	687b      	ldr	r3, [r7, #4]
   44498:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   4449c:	d815      	bhi.n	444ca <c_tsf_bx_lr_recording+0x7e>
   4449e:	2303      	movs	r3, #3
   444a0:	763b      	strb	r3, [r7, #24]
   444a2:	69bb      	ldr	r3, [r7, #24]
   444a4:	9300      	str	r3, [sp, #0]
   444a6:	f107 030c 	add.w	r3, r7, #12
   444aa:	cb0e      	ldmia	r3, {r1, r2, r3}
   444ac:	481a      	ldr	r0, [pc, #104]	; (44518 <c_tsf_bx_lr_recording+0xcc>)
   444ae:	5820      	ldr	r0, [r4, r0]
   444b0:	f7ff fc06 	bl	43cc0 <push>
   444b4:	4603      	mov	r3, r0
   444b6:	f083 0301 	eor.w	r3, r3, #1
   444ba:	b2db      	uxtb	r3, r3
   444bc:	2b00      	cmp	r3, #0
   444be:	d004      	beq.n	444ca <c_tsf_bx_lr_recording+0x7e>
   444c0:	4b17      	ldr	r3, [pc, #92]	; (44520 <c_tsf_bx_lr_recording+0xd4>)
   444c2:	447b      	add	r3, pc
   444c4:	4618      	mov	r0, r3
   444c6:	f7cc ea76 	blx	109b4 <puts@plt>
   444ca:	69fb      	ldr	r3, [r7, #28]
   444cc:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   444d0:	d81a      	bhi.n	44508 <c_tsf_bx_lr_recording+0xbc>
   444d2:	687b      	ldr	r3, [r7, #4]
   444d4:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   444d8:	d916      	bls.n	44508 <c_tsf_bx_lr_recording+0xbc>
   444da:	230a      	movs	r3, #10
   444dc:	763b      	strb	r3, [r7, #24]
   444de:	69bb      	ldr	r3, [r7, #24]
   444e0:	9300      	str	r3, [sp, #0]
   444e2:	f107 030c 	add.w	r3, r7, #12
   444e6:	cb0e      	ldmia	r3, {r1, r2, r3}
   444e8:	480b      	ldr	r0, [pc, #44]	; (44518 <c_tsf_bx_lr_recording+0xcc>)
   444ea:	5820      	ldr	r0, [r4, r0]
   444ec:	f7ff fbe8 	bl	43cc0 <push>
   444f0:	4603      	mov	r3, r0
   444f2:	f083 0301 	eor.w	r3, r3, #1
   444f6:	b2db      	uxtb	r3, r3
   444f8:	2b00      	cmp	r3, #0
   444fa:	d005      	beq.n	44508 <c_tsf_bx_lr_recording+0xbc>
   444fc:	4b09      	ldr	r3, [pc, #36]	; (44524 <c_tsf_bx_lr_recording+0xd8>)
   444fe:	447b      	add	r3, pc
   44500:	4618      	mov	r0, r3
   44502:	f7cc ea58 	blx	109b4 <puts@plt>
   44506:	bf00      	nop
   44508:	bf00      	nop
   4450a:	3724      	adds	r7, #36	; 0x24
   4450c:	46bd      	mov	sp, r7
   4450e:	bd90      	pop	{r4, r7, pc}
   44510:	00012ba6 	andeq	r2, r1, r6, lsr #23
   44514:	00000094 	muleq	r0, r4, r0
   44518:	000000ac 	andeq	r0, r0, ip, lsr #1
   4451c:	000000b4 	strheq	r0, [r0], -r4
   44520:	000022ca 	andeq	r2, r0, sl, asr #5
   44524:	0000228e 	andeq	r2, r0, lr, lsl #5

00044528 <c_tsf_pop_pc_recording>:
   44528:	b590      	push	{r4, r7, lr}
   4452a:	b08b      	sub	sp, #44	; 0x2c
   4452c:	af02      	add	r7, sp, #8
   4452e:	6078      	str	r0, [r7, #4]
   44530:	4c3d      	ldr	r4, [pc, #244]	; (44628 <c_tsf_pop_pc_recording+0x100>)
   44532:	447c      	add	r4, pc
   44534:	4b3d      	ldr	r3, [pc, #244]	; (4462c <c_tsf_pop_pc_recording+0x104>)
   44536:	58e3      	ldr	r3, [r4, r3]
   44538:	681b      	ldr	r3, [r3, #0]
   4453a:	2b00      	cmp	r3, #0
   4453c:	d109      	bne.n	44552 <c_tsf_pop_pc_recording+0x2a>
   4453e:	4b3b      	ldr	r3, [pc, #236]	; (4462c <c_tsf_pop_pc_recording+0x104>)
   44540:	58e3      	ldr	r3, [r4, r3]
   44542:	461a      	mov	r2, r3
   44544:	2301      	movs	r3, #1
   44546:	6013      	str	r3, [r2, #0]
   44548:	4b39      	ldr	r3, [pc, #228]	; (44630 <c_tsf_pop_pc_recording+0x108>)
   4454a:	58e3      	ldr	r3, [r4, r3]
   4454c:	4618      	mov	r0, r3
   4454e:	f7ff fca8 	bl	43ea2 <ringbuffer_init>
   44552:	f7ff fcc9 	bl	43ee8 <read_r8>
   44556:	61f8      	str	r0, [r7, #28]
   44558:	687b      	ldr	r3, [r7, #4]
   4455a:	60fb      	str	r3, [r7, #12]
   4455c:	69fb      	ldr	r3, [r7, #28]
   4455e:	613b      	str	r3, [r7, #16]
   44560:	4b34      	ldr	r3, [pc, #208]	; (44634 <c_tsf_pop_pc_recording+0x10c>)
   44562:	58e3      	ldr	r3, [r4, r3]
   44564:	681b      	ldr	r3, [r3, #0]
   44566:	2b00      	cmp	r3, #0
   44568:	d05a      	beq.n	44620 <c_tsf_pop_pc_recording+0xf8>
   4456a:	69fb      	ldr	r3, [r7, #28]
   4456c:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   44570:	d219      	bcs.n	445a6 <c_tsf_pop_pc_recording+0x7e>
   44572:	687b      	ldr	r3, [r7, #4]
   44574:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   44578:	d315      	bcc.n	445a6 <c_tsf_pop_pc_recording+0x7e>
   4457a:	2303      	movs	r3, #3
   4457c:	763b      	strb	r3, [r7, #24]
   4457e:	69bb      	ldr	r3, [r7, #24]
   44580:	9300      	str	r3, [sp, #0]
   44582:	f107 030c 	add.w	r3, r7, #12
   44586:	cb0e      	ldmia	r3, {r1, r2, r3}
   44588:	4829      	ldr	r0, [pc, #164]	; (44630 <c_tsf_pop_pc_recording+0x108>)
   4458a:	5820      	ldr	r0, [r4, r0]
   4458c:	f7ff fb98 	bl	43cc0 <push>
   44590:	4603      	mov	r3, r0
   44592:	f083 0301 	eor.w	r3, r3, #1
   44596:	b2db      	uxtb	r3, r3
   44598:	2b00      	cmp	r3, #0
   4459a:	d004      	beq.n	445a6 <c_tsf_pop_pc_recording+0x7e>
   4459c:	4b26      	ldr	r3, [pc, #152]	; (44638 <c_tsf_pop_pc_recording+0x110>)
   4459e:	447b      	add	r3, pc
   445a0:	4618      	mov	r0, r3
   445a2:	f7cc ea08 	blx	109b4 <puts@plt>
   445a6:	69fb      	ldr	r3, [r7, #28]
   445a8:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   445ac:	d319      	bcc.n	445e2 <c_tsf_pop_pc_recording+0xba>
   445ae:	687b      	ldr	r3, [r7, #4]
   445b0:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   445b4:	d215      	bcs.n	445e2 <c_tsf_pop_pc_recording+0xba>
   445b6:	230a      	movs	r3, #10
   445b8:	763b      	strb	r3, [r7, #24]
   445ba:	69bb      	ldr	r3, [r7, #24]
   445bc:	9300      	str	r3, [sp, #0]
   445be:	f107 030c 	add.w	r3, r7, #12
   445c2:	cb0e      	ldmia	r3, {r1, r2, r3}
   445c4:	481a      	ldr	r0, [pc, #104]	; (44630 <c_tsf_pop_pc_recording+0x108>)
   445c6:	5820      	ldr	r0, [r4, r0]
   445c8:	f7ff fb7a 	bl	43cc0 <push>
   445cc:	4603      	mov	r3, r0
   445ce:	f083 0301 	eor.w	r3, r3, #1
   445d2:	b2db      	uxtb	r3, r3
   445d4:	2b00      	cmp	r3, #0
   445d6:	d004      	beq.n	445e2 <c_tsf_pop_pc_recording+0xba>
   445d8:	4b18      	ldr	r3, [pc, #96]	; (4463c <c_tsf_pop_pc_recording+0x114>)
   445da:	447b      	add	r3, pc
   445dc:	4618      	mov	r0, r3
   445de:	f7cc e9ea 	blx	109b4 <puts@plt>
   445e2:	69fb      	ldr	r3, [r7, #28]
   445e4:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   445e8:	d81a      	bhi.n	44620 <c_tsf_pop_pc_recording+0xf8>
   445ea:	687b      	ldr	r3, [r7, #4]
   445ec:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   445f0:	d316      	bcc.n	44620 <c_tsf_pop_pc_recording+0xf8>
   445f2:	2303      	movs	r3, #3
   445f4:	763b      	strb	r3, [r7, #24]
   445f6:	69bb      	ldr	r3, [r7, #24]
   445f8:	9300      	str	r3, [sp, #0]
   445fa:	f107 030c 	add.w	r3, r7, #12
   445fe:	cb0e      	ldmia	r3, {r1, r2, r3}
   44600:	480b      	ldr	r0, [pc, #44]	; (44630 <c_tsf_pop_pc_recording+0x108>)
   44602:	5820      	ldr	r0, [r4, r0]
   44604:	f7ff fb5c 	bl	43cc0 <push>
   44608:	4603      	mov	r3, r0
   4460a:	f083 0301 	eor.w	r3, r3, #1
   4460e:	b2db      	uxtb	r3, r3
   44610:	2b00      	cmp	r3, #0
   44612:	d005      	beq.n	44620 <c_tsf_pop_pc_recording+0xf8>
   44614:	4b0a      	ldr	r3, [pc, #40]	; (44640 <c_tsf_pop_pc_recording+0x118>)
   44616:	447b      	add	r3, pc
   44618:	4618      	mov	r0, r3
   4461a:	f7cc e9cc 	blx	109b4 <puts@plt>
   4461e:	bf00      	nop
   44620:	bf00      	nop
   44622:	3724      	adds	r7, #36	; 0x24
   44624:	46bd      	mov	sp, r7
   44626:	bd90      	pop	{r4, r7, pc}
   44628:	00012aca 	andeq	r2, r1, sl, asr #21
   4462c:	00000094 	muleq	r0, r4, r0
   44630:	000000ac 	andeq	r0, r0, ip, lsr #1
   44634:	000000b4 	strheq	r0, [r0], -r4
   44638:	000021ee 	andeq	r2, r0, lr, ror #3
   4463c:	000021b2 			; <UNDEFINED> instruction: 0x000021b2
   44640:	00002176 	andeq	r2, r0, r6, ror r1

00044644 <cfv_icall_blx>:
   44644:	b590      	push	{r4, r7, lr}
   44646:	b08b      	sub	sp, #44	; 0x2c
   44648:	af02      	add	r7, sp, #8
   4464a:	6078      	str	r0, [r7, #4]
   4464c:	4c21      	ldr	r4, [pc, #132]	; (446d4 <cfv_icall_blx+0x90>)
   4464e:	447c      	add	r4, pc
   44650:	4b21      	ldr	r3, [pc, #132]	; (446d8 <cfv_icall_blx+0x94>)
   44652:	58e3      	ldr	r3, [r4, r3]
   44654:	681b      	ldr	r3, [r3, #0]
   44656:	2b00      	cmp	r3, #0
   44658:	d109      	bne.n	4466e <cfv_icall_blx+0x2a>
   4465a:	4b1f      	ldr	r3, [pc, #124]	; (446d8 <cfv_icall_blx+0x94>)
   4465c:	58e3      	ldr	r3, [r4, r3]
   4465e:	461a      	mov	r2, r3
   44660:	2301      	movs	r3, #1
   44662:	6013      	str	r3, [r2, #0]
   44664:	4b1d      	ldr	r3, [pc, #116]	; (446dc <cfv_icall_blx+0x98>)
   44666:	58e3      	ldr	r3, [r4, r3]
   44668:	4618      	mov	r0, r3
   4466a:	f7ff fc1a 	bl	43ea2 <ringbuffer_init>
   4466e:	f7ff fc3b 	bl	43ee8 <read_r8>
   44672:	61f8      	str	r0, [r7, #28]
   44674:	687b      	ldr	r3, [r7, #4]
   44676:	60fb      	str	r3, [r7, #12]
   44678:	69fb      	ldr	r3, [r7, #28]
   4467a:	613b      	str	r3, [r7, #16]
   4467c:	4b18      	ldr	r3, [pc, #96]	; (446e0 <cfv_icall_blx+0x9c>)
   4467e:	58e3      	ldr	r3, [r4, r3]
   44680:	681b      	ldr	r3, [r3, #0]
   44682:	2b00      	cmp	r3, #0
   44684:	d021      	beq.n	446ca <cfv_icall_blx+0x86>
   44686:	69fb      	ldr	r3, [r7, #28]
   44688:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   4468c:	d906      	bls.n	4469c <cfv_icall_blx+0x58>
   4468e:	687b      	ldr	r3, [r7, #4]
   44690:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   44694:	d802      	bhi.n	4469c <cfv_icall_blx+0x58>
   44696:	230a      	movs	r3, #10
   44698:	763b      	strb	r3, [r7, #24]
   4469a:	e001      	b.n	446a0 <cfv_icall_blx+0x5c>
   4469c:	2301      	movs	r3, #1
   4469e:	763b      	strb	r3, [r7, #24]
   446a0:	69bb      	ldr	r3, [r7, #24]
   446a2:	9300      	str	r3, [sp, #0]
   446a4:	f107 030c 	add.w	r3, r7, #12
   446a8:	cb0e      	ldmia	r3, {r1, r2, r3}
   446aa:	480c      	ldr	r0, [pc, #48]	; (446dc <cfv_icall_blx+0x98>)
   446ac:	5820      	ldr	r0, [r4, r0]
   446ae:	f7ff fb07 	bl	43cc0 <push>
   446b2:	4603      	mov	r3, r0
   446b4:	f083 0301 	eor.w	r3, r3, #1
   446b8:	b2db      	uxtb	r3, r3
   446ba:	2b00      	cmp	r3, #0
   446bc:	d005      	beq.n	446ca <cfv_icall_blx+0x86>
   446be:	4b09      	ldr	r3, [pc, #36]	; (446e4 <cfv_icall_blx+0xa0>)
   446c0:	447b      	add	r3, pc
   446c2:	4618      	mov	r0, r3
   446c4:	f7cc e976 	blx	109b4 <puts@plt>
   446c8:	bf00      	nop
   446ca:	bf00      	nop
   446cc:	3724      	adds	r7, #36	; 0x24
   446ce:	46bd      	mov	sp, r7
   446d0:	bd90      	pop	{r4, r7, pc}
   446d2:	bf00      	nop
   446d4:	000129ae 	andeq	r2, r1, lr, lsr #19
   446d8:	00000094 	muleq	r0, r4, r0
   446dc:	000000ac 	andeq	r0, r0, ip, lsr #1
   446e0:	000000b4 	strheq	r0, [r0], -r4
   446e4:	000020cc 	andeq	r2, r0, ip, asr #1

000446e8 <cfv_icall_blx_pre>:
   446e8:	b590      	push	{r4, r7, lr}
   446ea:	b08d      	sub	sp, #52	; 0x34
   446ec:	af02      	add	r7, sp, #8
   446ee:	60f8      	str	r0, [r7, #12]
   446f0:	60b9      	str	r1, [r7, #8]
   446f2:	607a      	str	r2, [r7, #4]
   446f4:	4c3e      	ldr	r4, [pc, #248]	; (447f0 <cfv_icall_blx_pre+0x108>)
   446f6:	447c      	add	r4, pc
   446f8:	68b9      	ldr	r1, [r7, #8]
   446fa:	6878      	ldr	r0, [r7, #4]
   446fc:	f7ff fc50 	bl	43fa0 <isBranchTaken>
   44700:	4603      	mov	r3, r0
   44702:	f887 3027 	strb.w	r3, [r7, #39]	; 0x27
   44706:	f7ff fbef 	bl	43ee8 <read_r8>
   4470a:	6238      	str	r0, [r7, #32]
   4470c:	68fb      	ldr	r3, [r7, #12]
   4470e:	613b      	str	r3, [r7, #16]
   44710:	f897 3027 	ldrb.w	r3, [r7, #39]	; 0x27
   44714:	617b      	str	r3, [r7, #20]
   44716:	68bb      	ldr	r3, [r7, #8]
   44718:	61bb      	str	r3, [r7, #24]
   4471a:	2304      	movs	r3, #4
   4471c:	773b      	strb	r3, [r7, #28]
   4471e:	4b35      	ldr	r3, [pc, #212]	; (447f4 <cfv_icall_blx_pre+0x10c>)
   44720:	58e3      	ldr	r3, [r4, r3]
   44722:	681b      	ldr	r3, [r3, #0]
   44724:	2b00      	cmp	r3, #0
   44726:	d05f      	beq.n	447e8 <cfv_icall_blx_pre+0x100>
   44728:	69fb      	ldr	r3, [r7, #28]
   4472a:	9300      	str	r3, [sp, #0]
   4472c:	f107 0310 	add.w	r3, r7, #16
   44730:	cb0e      	ldmia	r3, {r1, r2, r3}
   44732:	4831      	ldr	r0, [pc, #196]	; (447f8 <cfv_icall_blx_pre+0x110>)
   44734:	5820      	ldr	r0, [r4, r0]
   44736:	f7ff fac3 	bl	43cc0 <push>
   4473a:	4603      	mov	r3, r0
   4473c:	f083 0301 	eor.w	r3, r3, #1
   44740:	b2db      	uxtb	r3, r3
   44742:	2b00      	cmp	r3, #0
   44744:	d004      	beq.n	44750 <cfv_icall_blx_pre+0x68>
   44746:	4b2d      	ldr	r3, [pc, #180]	; (447fc <cfv_icall_blx_pre+0x114>)
   44748:	447b      	add	r3, pc
   4474a:	4618      	mov	r0, r3
   4474c:	f7cc e932 	blx	109b4 <puts@plt>
   44750:	6a3b      	ldr	r3, [r7, #32]
   44752:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   44756:	d91f      	bls.n	44798 <cfv_icall_blx_pre+0xb0>
   44758:	68fb      	ldr	r3, [r7, #12]
   4475a:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   4475e:	d81b      	bhi.n	44798 <cfv_icall_blx_pre+0xb0>
   44760:	f897 3027 	ldrb.w	r3, [r7, #39]	; 0x27
   44764:	2b00      	cmp	r3, #0
   44766:	d03c      	beq.n	447e2 <cfv_icall_blx_pre+0xfa>
   44768:	230a      	movs	r3, #10
   4476a:	773b      	strb	r3, [r7, #28]
   4476c:	6a3b      	ldr	r3, [r7, #32]
   4476e:	617b      	str	r3, [r7, #20]
   44770:	69fb      	ldr	r3, [r7, #28]
   44772:	9300      	str	r3, [sp, #0]
   44774:	f107 0310 	add.w	r3, r7, #16
   44778:	cb0e      	ldmia	r3, {r1, r2, r3}
   4477a:	481f      	ldr	r0, [pc, #124]	; (447f8 <cfv_icall_blx_pre+0x110>)
   4477c:	5820      	ldr	r0, [r4, r0]
   4477e:	f7ff fa9f 	bl	43cc0 <push>
   44782:	4603      	mov	r3, r0
   44784:	f083 0301 	eor.w	r3, r3, #1
   44788:	b2db      	uxtb	r3, r3
   4478a:	2b00      	cmp	r3, #0
   4478c:	d004      	beq.n	44798 <cfv_icall_blx_pre+0xb0>
   4478e:	4b1c      	ldr	r3, [pc, #112]	; (44800 <cfv_icall_blx_pre+0x118>)
   44790:	447b      	add	r3, pc
   44792:	4618      	mov	r0, r3
   44794:	f7cc e90e 	blx	109b4 <puts@plt>
   44798:	6a3b      	ldr	r3, [r7, #32]
   4479a:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   4479e:	d903      	bls.n	447a8 <cfv_icall_blx_pre+0xc0>
   447a0:	68fb      	ldr	r3, [r7, #12]
   447a2:	f5b3 2f80 	cmp.w	r3, #262144	; 0x40000
   447a6:	d81f      	bhi.n	447e8 <cfv_icall_blx_pre+0x100>
   447a8:	f897 3027 	ldrb.w	r3, [r7, #39]	; 0x27
   447ac:	2b00      	cmp	r3, #0
   447ae:	d01a      	beq.n	447e6 <cfv_icall_blx_pre+0xfe>
   447b0:	2301      	movs	r3, #1
   447b2:	773b      	strb	r3, [r7, #28]
   447b4:	6a3b      	ldr	r3, [r7, #32]
   447b6:	617b      	str	r3, [r7, #20]
   447b8:	69fb      	ldr	r3, [r7, #28]
   447ba:	9300      	str	r3, [sp, #0]
   447bc:	f107 0310 	add.w	r3, r7, #16
   447c0:	cb0e      	ldmia	r3, {r1, r2, r3}
   447c2:	480d      	ldr	r0, [pc, #52]	; (447f8 <cfv_icall_blx_pre+0x110>)
   447c4:	5820      	ldr	r0, [r4, r0]
   447c6:	f7ff fa7b 	bl	43cc0 <push>
   447ca:	4603      	mov	r3, r0
   447cc:	f083 0301 	eor.w	r3, r3, #1
   447d0:	b2db      	uxtb	r3, r3
   447d2:	2b00      	cmp	r3, #0
   447d4:	d008      	beq.n	447e8 <cfv_icall_blx_pre+0x100>
   447d6:	4b0b      	ldr	r3, [pc, #44]	; (44804 <cfv_icall_blx_pre+0x11c>)
   447d8:	447b      	add	r3, pc
   447da:	4618      	mov	r0, r3
   447dc:	f7cc e8ea 	blx	109b4 <puts@plt>
   447e0:	e002      	b.n	447e8 <cfv_icall_blx_pre+0x100>
   447e2:	bf00      	nop
   447e4:	e000      	b.n	447e8 <cfv_icall_blx_pre+0x100>
   447e6:	bf00      	nop
   447e8:	372c      	adds	r7, #44	; 0x2c
   447ea:	46bd      	mov	sp, r7
   447ec:	bd90      	pop	{r4, r7, pc}
   447ee:	bf00      	nop
   447f0:	00012906 	andeq	r2, r1, r6, lsl #18
   447f4:	000000b4 	strheq	r0, [r0], -r4
   447f8:	000000ac 	andeq	r0, r0, ip, lsr #1
   447fc:	00002044 	andeq	r2, r0, r4, asr #32
   44800:	00001ffc 	strdeq	r1, [r0], -ip
   44804:	00001fb4 			; <UNDEFINED> instruction: 0x00001fb4

00044808 <cfv_icall_bc_blc>:
   44808:	b590      	push	{r4, r7, lr}
   4480a:	b08d      	sub	sp, #52	; 0x34
   4480c:	af02      	add	r7, sp, #8
   4480e:	60f8      	str	r0, [r7, #12]
   44810:	60b9      	str	r1, [r7, #8]
   44812:	607a      	str	r2, [r7, #4]
   44814:	4c1f      	ldr	r4, [pc, #124]	; (44894 <cfv_icall_bc_blc+0x8c>)
   44816:	447c      	add	r4, pc
   44818:	4b1f      	ldr	r3, [pc, #124]	; (44898 <cfv_icall_bc_blc+0x90>)
   4481a:	58e3      	ldr	r3, [r4, r3]
   4481c:	681b      	ldr	r3, [r3, #0]
   4481e:	2b00      	cmp	r3, #0
   44820:	d109      	bne.n	44836 <cfv_icall_bc_blc+0x2e>
   44822:	4b1d      	ldr	r3, [pc, #116]	; (44898 <cfv_icall_bc_blc+0x90>)
   44824:	58e3      	ldr	r3, [r4, r3]
   44826:	461a      	mov	r2, r3
   44828:	2301      	movs	r3, #1
   4482a:	6013      	str	r3, [r2, #0]
   4482c:	4b1b      	ldr	r3, [pc, #108]	; (4489c <cfv_icall_bc_blc+0x94>)
   4482e:	58e3      	ldr	r3, [r4, r3]
   44830:	4618      	mov	r0, r3
   44832:	f7ff fb36 	bl	43ea2 <ringbuffer_init>
   44836:	68b9      	ldr	r1, [r7, #8]
   44838:	6878      	ldr	r0, [r7, #4]
   4483a:	f7ff fbb1 	bl	43fa0 <isBranchTaken>
   4483e:	4603      	mov	r3, r0
   44840:	f887 3027 	strb.w	r3, [r7, #39]	; 0x27
   44844:	68fb      	ldr	r3, [r7, #12]
   44846:	617b      	str	r3, [r7, #20]
   44848:	f897 3027 	ldrb.w	r3, [r7, #39]	; 0x27
   4484c:	61bb      	str	r3, [r7, #24]
   4484e:	68bb      	ldr	r3, [r7, #8]
   44850:	61fb      	str	r3, [r7, #28]
   44852:	2304      	movs	r3, #4
   44854:	f887 3020 	strb.w	r3, [r7, #32]
   44858:	4b11      	ldr	r3, [pc, #68]	; (448a0 <cfv_icall_bc_blc+0x98>)
   4485a:	58e3      	ldr	r3, [r4, r3]
   4485c:	681b      	ldr	r3, [r3, #0]
   4485e:	2b00      	cmp	r3, #0
   44860:	d014      	beq.n	4488c <cfv_icall_bc_blc+0x84>
   44862:	6a3b      	ldr	r3, [r7, #32]
   44864:	9300      	str	r3, [sp, #0]
   44866:	f107 0314 	add.w	r3, r7, #20
   4486a:	cb0e      	ldmia	r3, {r1, r2, r3}
   4486c:	480b      	ldr	r0, [pc, #44]	; (4489c <cfv_icall_bc_blc+0x94>)
   4486e:	5820      	ldr	r0, [r4, r0]
   44870:	f7ff fa26 	bl	43cc0 <push>
   44874:	4603      	mov	r3, r0
   44876:	f083 0301 	eor.w	r3, r3, #1
   4487a:	b2db      	uxtb	r3, r3
   4487c:	2b00      	cmp	r3, #0
   4487e:	d005      	beq.n	4488c <cfv_icall_bc_blc+0x84>
   44880:	4b08      	ldr	r3, [pc, #32]	; (448a4 <cfv_icall_bc_blc+0x9c>)
   44882:	447b      	add	r3, pc
   44884:	4618      	mov	r0, r3
   44886:	f7cc e896 	blx	109b4 <puts@plt>
   4488a:	bf00      	nop
   4488c:	bf00      	nop
   4488e:	372c      	adds	r7, #44	; 0x2c
   44890:	46bd      	mov	sp, r7
   44892:	bd90      	pop	{r4, r7, pc}
   44894:	000127e6 	andeq	r2, r1, r6, ror #15
   44898:	00000094 	muleq	r0, r4, r0
   4489c:	000000ac 	andeq	r0, r0, ip, lsr #1
   448a0:	000000b4 	strheq	r0, [r0], -r4
   448a4:	00001f0a 	andeq	r1, r0, sl, lsl #30

000448a8 <cfv_icall_ldmia_ret>:
   448a8:	b590      	push	{r4, r7, lr}
   448aa:	b08d      	sub	sp, #52	; 0x34
   448ac:	af02      	add	r7, sp, #8
   448ae:	60f8      	str	r0, [r7, #12]
   448b0:	60b9      	str	r1, [r7, #8]
   448b2:	607a      	str	r2, [r7, #4]
   448b4:	4c1d      	ldr	r4, [pc, #116]	; (4492c <cfv_icall_ldmia_ret+0x84>)
   448b6:	447c      	add	r4, pc
   448b8:	4b1d      	ldr	r3, [pc, #116]	; (44930 <cfv_icall_ldmia_ret+0x88>)
   448ba:	58e3      	ldr	r3, [r4, r3]
   448bc:	681b      	ldr	r3, [r3, #0]
   448be:	2b00      	cmp	r3, #0
   448c0:	d109      	bne.n	448d6 <cfv_icall_ldmia_ret+0x2e>
   448c2:	4b1b      	ldr	r3, [pc, #108]	; (44930 <cfv_icall_ldmia_ret+0x88>)
   448c4:	58e3      	ldr	r3, [r4, r3]
   448c6:	461a      	mov	r2, r3
   448c8:	2301      	movs	r3, #1
   448ca:	6013      	str	r3, [r2, #0]
   448cc:	4b19      	ldr	r3, [pc, #100]	; (44934 <cfv_icall_ldmia_ret+0x8c>)
   448ce:	58e3      	ldr	r3, [r4, r3]
   448d0:	4618      	mov	r0, r3
   448d2:	f7ff fae6 	bl	43ea2 <ringbuffer_init>
   448d6:	f7ff fb07 	bl	43ee8 <read_r8>
   448da:	6278      	str	r0, [r7, #36]	; 0x24
   448dc:	68fb      	ldr	r3, [r7, #12]
   448de:	617b      	str	r3, [r7, #20]
   448e0:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   448e2:	61bb      	str	r3, [r7, #24]
   448e4:	68bb      	ldr	r3, [r7, #8]
   448e6:	61fb      	str	r3, [r7, #28]
   448e8:	2303      	movs	r3, #3
   448ea:	f887 3020 	strb.w	r3, [r7, #32]
   448ee:	4b12      	ldr	r3, [pc, #72]	; (44938 <cfv_icall_ldmia_ret+0x90>)
   448f0:	58e3      	ldr	r3, [r4, r3]
   448f2:	681b      	ldr	r3, [r3, #0]
   448f4:	2b00      	cmp	r3, #0
   448f6:	d014      	beq.n	44922 <cfv_icall_ldmia_ret+0x7a>
   448f8:	6a3b      	ldr	r3, [r7, #32]
   448fa:	9300      	str	r3, [sp, #0]
   448fc:	f107 0314 	add.w	r3, r7, #20
   44900:	cb0e      	ldmia	r3, {r1, r2, r3}
   44902:	480c      	ldr	r0, [pc, #48]	; (44934 <cfv_icall_ldmia_ret+0x8c>)
   44904:	5820      	ldr	r0, [r4, r0]
   44906:	f7ff f9db 	bl	43cc0 <push>
   4490a:	4603      	mov	r3, r0
   4490c:	f083 0301 	eor.w	r3, r3, #1
   44910:	b2db      	uxtb	r3, r3
   44912:	2b00      	cmp	r3, #0
   44914:	d005      	beq.n	44922 <cfv_icall_ldmia_ret+0x7a>
   44916:	4b09      	ldr	r3, [pc, #36]	; (4493c <cfv_icall_ldmia_ret+0x94>)
   44918:	447b      	add	r3, pc
   4491a:	4618      	mov	r0, r3
   4491c:	f7cc e84a 	blx	109b4 <puts@plt>
   44920:	bf00      	nop
   44922:	bf00      	nop
   44924:	372c      	adds	r7, #44	; 0x2c
   44926:	46bd      	mov	sp, r7
   44928:	bd90      	pop	{r4, r7, pc}
   4492a:	bf00      	nop
   4492c:	00012746 	andeq	r2, r1, r6, asr #14
   44930:	00000094 	muleq	r0, r4, r0
   44934:	000000ac 	andeq	r0, r0, ip, lsr #1
   44938:	000000b4 	strheq	r0, [r0], -r4
   4493c:	00001e74 	andeq	r1, r0, r4, ror lr

00044940 <ict_checking>:
   44940:	b480      	push	{r7}
   44942:	b083      	sub	sp, #12
   44944:	af00      	add	r7, sp, #0
   44946:	6078      	str	r0, [r7, #4]
   44948:	2300      	movs	r3, #0
   4494a:	4618      	mov	r0, r3
   4494c:	370c      	adds	r7, #12
   4494e:	46bd      	mov	sp, r7
   44950:	f85d 7b04 	ldr.w	r7, [sp], #4
   44954:	4770      	bx	lr

00044956 <error_found>:
   44956:	b580      	push	{r7, lr}
   44958:	af00      	add	r7, sp, #0
   4495a:	4b03      	ldr	r3, [pc, #12]	; (44968 <error_found+0x12>)
   4495c:	447b      	add	r3, pc
   4495e:	4618      	mov	r0, r3
   44960:	f7cc e828 	blx	109b4 <puts@plt>
   44964:	bf00      	nop
   44966:	bd80      	pop	{r7, pc}
   44968:	00001e40 	andeq	r1, r0, r0, asr #28

0004496c <test_fwd_indirect_tsf>:
   4496c:	b580      	push	{r7, lr}
   4496e:	af00      	add	r7, sp, #0
   44970:	4a06      	ldr	r2, [pc, #24]	; (4498c <test_fwd_indirect_tsf+0x20>)
   44972:	447a      	add	r2, pc
   44974:	4b06      	ldr	r3, [pc, #24]	; (44990 <test_fwd_indirect_tsf+0x24>)
   44976:	58d3      	ldr	r3, [r2, r3]
   44978:	681b      	ldr	r3, [r3, #0]
   4497a:	2b00      	cmp	r3, #0
   4497c:	d004      	beq.n	44988 <test_fwd_indirect_tsf+0x1c>
   4497e:	4b05      	ldr	r3, [pc, #20]	; (44994 <test_fwd_indirect_tsf+0x28>)
   44980:	447b      	add	r3, pc
   44982:	4618      	mov	r0, r3
   44984:	f7cc e816 	blx	109b4 <puts@plt>
   44988:	bf00      	nop
   4498a:	bd80      	pop	{r7, pc}
   4498c:	0001268a 	andeq	r2, r1, sl, lsl #13
   44990:	000000b4 	strheq	r0, [r0], -r4
   44994:	00001e44 	andeq	r1, r0, r4, asr #28

00044998 <view_switch_to_rd_and_log>:
   44998:	b590      	push	{r4, r7, lr}
   4499a:	b089      	sub	sp, #36	; 0x24
   4499c:	af04      	add	r7, sp, #16
   4499e:	60f8      	str	r0, [r7, #12]
   449a0:	60b9      	str	r1, [r7, #8]
   449a2:	607a      	str	r2, [r7, #4]
   449a4:	4c54      	ldr	r4, [pc, #336]	; (44af8 <view_switch_to_rd_and_log+0x160>)
   449a6:	447c      	add	r4, pc
   449a8:	4b54      	ldr	r3, [pc, #336]	; (44afc <view_switch_to_rd_and_log+0x164>)
   449aa:	58e3      	ldr	r3, [r4, r3]
   449ac:	681b      	ldr	r3, [r3, #0]
   449ae:	3301      	adds	r3, #1
   449b0:	4a52      	ldr	r2, [pc, #328]	; (44afc <view_switch_to_rd_and_log+0x164>)
   449b2:	58a2      	ldr	r2, [r4, r2]
   449b4:	6013      	str	r3, [r2, #0]
   449b6:	4b51      	ldr	r3, [pc, #324]	; (44afc <view_switch_to_rd_and_log+0x164>)
   449b8:	58e3      	ldr	r3, [r4, r3]
   449ba:	6819      	ldr	r1, [r3, #0]
   449bc:	f246 6367 	movw	r3, #26215	; 0x6667
   449c0:	f2c6 6366 	movt	r3, #26214	; 0x6666
   449c4:	fb81 2303 	smull	r2, r3, r1, r3
   449c8:	109a      	asrs	r2, r3, #2
   449ca:	17cb      	asrs	r3, r1, #31
   449cc:	1ad2      	subs	r2, r2, r3
   449ce:	4613      	mov	r3, r2
   449d0:	009b      	lsls	r3, r3, #2
   449d2:	4413      	add	r3, r2
   449d4:	005b      	lsls	r3, r3, #1
   449d6:	1aca      	subs	r2, r1, r3
   449d8:	2a00      	cmp	r2, #0
   449da:	f040 8089 	bne.w	44af0 <view_switch_to_rd_and_log+0x158>
   449de:	4b48      	ldr	r3, [pc, #288]	; (44b00 <view_switch_to_rd_and_log+0x168>)
   449e0:	58e3      	ldr	r3, [r4, r3]
   449e2:	781b      	ldrb	r3, [r3, #0]
   449e4:	f083 0301 	eor.w	r3, r3, #1
   449e8:	b2db      	uxtb	r3, r3
   449ea:	2b00      	cmp	r3, #0
   449ec:	d045      	beq.n	44a7a <view_switch_to_rd_and_log+0xe2>
   449ee:	4b44      	ldr	r3, [pc, #272]	; (44b00 <view_switch_to_rd_and_log+0x168>)
   449f0:	58e3      	ldr	r3, [r4, r3]
   449f2:	2201      	movs	r2, #1
   449f4:	701a      	strb	r2, [r3, #0]
   449f6:	4b43      	ldr	r3, [pc, #268]	; (44b04 <view_switch_to_rd_and_log+0x16c>)
   449f8:	447b      	add	r3, pc
   449fa:	4618      	mov	r0, r3
   449fc:	f7cb efda 	blx	109b4 <puts@plt>
   44a00:	4b41      	ldr	r3, [pc, #260]	; (44b08 <view_switch_to_rd_and_log+0x170>)
   44a02:	58e3      	ldr	r3, [r4, r3]
   44a04:	4619      	mov	r1, r3
   44a06:	2000      	movs	r0, #0
   44a08:	f000 fbd2 	bl	451b0 <TEEC_InitializeContext>
   44a0c:	4602      	mov	r2, r0
   44a0e:	4b3f      	ldr	r3, [pc, #252]	; (44b0c <view_switch_to_rd_and_log+0x174>)
   44a10:	58e3      	ldr	r3, [r4, r3]
   44a12:	601a      	str	r2, [r3, #0]
   44a14:	4b3d      	ldr	r3, [pc, #244]	; (44b0c <view_switch_to_rd_and_log+0x174>)
   44a16:	58e3      	ldr	r3, [r4, r3]
   44a18:	681b      	ldr	r3, [r3, #0]
   44a1a:	2b00      	cmp	r3, #0
   44a1c:	d009      	beq.n	44a32 <view_switch_to_rd_and_log+0x9a>
   44a1e:	4b3b      	ldr	r3, [pc, #236]	; (44b0c <view_switch_to_rd_and_log+0x174>)
   44a20:	58e3      	ldr	r3, [r4, r3]
   44a22:	681b      	ldr	r3, [r3, #0]
   44a24:	461a      	mov	r2, r3
   44a26:	4b3a      	ldr	r3, [pc, #232]	; (44b10 <view_switch_to_rd_and_log+0x178>)
   44a28:	447b      	add	r3, pc
   44a2a:	4619      	mov	r1, r3
   44a2c:	2001      	movs	r0, #1
   44a2e:	f7cc e810 	blx	10a50 <errx@plt>
   44a32:	4b38      	ldr	r3, [pc, #224]	; (44b14 <view_switch_to_rd_and_log+0x17c>)
   44a34:	58e3      	ldr	r3, [r4, r3]
   44a36:	9302      	str	r3, [sp, #8]
   44a38:	2300      	movs	r3, #0
   44a3a:	9301      	str	r3, [sp, #4]
   44a3c:	2300      	movs	r3, #0
   44a3e:	9300      	str	r3, [sp, #0]
   44a40:	2300      	movs	r3, #0
   44a42:	4a35      	ldr	r2, [pc, #212]	; (44b18 <view_switch_to_rd_and_log+0x180>)
   44a44:	58a2      	ldr	r2, [r4, r2]
   44a46:	4935      	ldr	r1, [pc, #212]	; (44b1c <view_switch_to_rd_and_log+0x184>)
   44a48:	5861      	ldr	r1, [r4, r1]
   44a4a:	482f      	ldr	r0, [pc, #188]	; (44b08 <view_switch_to_rd_and_log+0x170>)
   44a4c:	5820      	ldr	r0, [r4, r0]
   44a4e:	f001 f800 	bl	45a52 <TEEC_OpenSession>
   44a52:	4602      	mov	r2, r0
   44a54:	4b2d      	ldr	r3, [pc, #180]	; (44b0c <view_switch_to_rd_and_log+0x174>)
   44a56:	58e3      	ldr	r3, [r4, r3]
   44a58:	601a      	str	r2, [r3, #0]
   44a5a:	4b2c      	ldr	r3, [pc, #176]	; (44b0c <view_switch_to_rd_and_log+0x174>)
   44a5c:	58e3      	ldr	r3, [r4, r3]
   44a5e:	681b      	ldr	r3, [r3, #0]
   44a60:	2b00      	cmp	r3, #0
   44a62:	d00a      	beq.n	44a7a <view_switch_to_rd_and_log+0xe2>
   44a64:	4b29      	ldr	r3, [pc, #164]	; (44b0c <view_switch_to_rd_and_log+0x174>)
   44a66:	58e3      	ldr	r3, [r4, r3]
   44a68:	681a      	ldr	r2, [r3, #0]
   44a6a:	4b2a      	ldr	r3, [pc, #168]	; (44b14 <view_switch_to_rd_and_log+0x17c>)
   44a6c:	58e3      	ldr	r3, [r4, r3]
   44a6e:	681b      	ldr	r3, [r3, #0]
   44a70:	492b      	ldr	r1, [pc, #172]	; (44b20 <view_switch_to_rd_and_log+0x188>)
   44a72:	4479      	add	r1, pc
   44a74:	2001      	movs	r0, #1
   44a76:	f7cb efec 	blx	10a50 <errx@plt>
   44a7a:	223c      	movs	r2, #60	; 0x3c
   44a7c:	2100      	movs	r1, #0
   44a7e:	4b29      	ldr	r3, [pc, #164]	; (44b24 <view_switch_to_rd_and_log+0x18c>)
   44a80:	58e3      	ldr	r3, [r4, r3]
   44a82:	4618      	mov	r0, r3
   44a84:	f7cb efcc 	blx	10a20 <memset@plt>
   44a88:	4b26      	ldr	r3, [pc, #152]	; (44b24 <view_switch_to_rd_and_log+0x18c>)
   44a8a:	58e3      	ldr	r3, [r4, r3]
   44a8c:	461a      	mov	r2, r3
   44a8e:	2333      	movs	r3, #51	; 0x33
   44a90:	6053      	str	r3, [r2, #4]
   44a92:	68fb      	ldr	r3, [r7, #12]
   44a94:	4a23      	ldr	r2, [pc, #140]	; (44b24 <view_switch_to_rd_and_log+0x18c>)
   44a96:	58a2      	ldr	r2, [r4, r2]
   44a98:	6093      	str	r3, [r2, #8]
   44a9a:	68bb      	ldr	r3, [r7, #8]
   44a9c:	4a21      	ldr	r2, [pc, #132]	; (44b24 <view_switch_to_rd_and_log+0x18c>)
   44a9e:	58a2      	ldr	r2, [r4, r2]
   44aa0:	60d3      	str	r3, [r2, #12]
   44aa2:	687b      	ldr	r3, [r7, #4]
   44aa4:	4a1f      	ldr	r2, [pc, #124]	; (44b24 <view_switch_to_rd_and_log+0x18c>)
   44aa6:	58a2      	ldr	r2, [r4, r2]
   44aa8:	6153      	str	r3, [r2, #20]
   44aaa:	4b1e      	ldr	r3, [pc, #120]	; (44b24 <view_switch_to_rd_and_log+0x18c>)
   44aac:	58e3      	ldr	r3, [r4, r3]
   44aae:	461a      	mov	r2, r3
   44ab0:	f44f 73de 	mov.w	r3, #444	; 0x1bc
   44ab4:	6193      	str	r3, [r2, #24]
   44ab6:	4b17      	ldr	r3, [pc, #92]	; (44b14 <view_switch_to_rd_and_log+0x17c>)
   44ab8:	58e3      	ldr	r3, [r4, r3]
   44aba:	4a1a      	ldr	r2, [pc, #104]	; (44b24 <view_switch_to_rd_and_log+0x18c>)
   44abc:	58a2      	ldr	r2, [r4, r2]
   44abe:	2100      	movs	r1, #0
   44ac0:	4816      	ldr	r0, [pc, #88]	; (44b1c <view_switch_to_rd_and_log+0x184>)
   44ac2:	5820      	ldr	r0, [r4, r0]
   44ac4:	f001 f8c8 	bl	45c58 <TEEC_InvokeCommand>
   44ac8:	4602      	mov	r2, r0
   44aca:	4b10      	ldr	r3, [pc, #64]	; (44b0c <view_switch_to_rd_and_log+0x174>)
   44acc:	58e3      	ldr	r3, [r4, r3]
   44ace:	601a      	str	r2, [r3, #0]
   44ad0:	4b0e      	ldr	r3, [pc, #56]	; (44b0c <view_switch_to_rd_and_log+0x174>)
   44ad2:	58e3      	ldr	r3, [r4, r3]
   44ad4:	681b      	ldr	r3, [r3, #0]
   44ad6:	2b00      	cmp	r3, #0
   44ad8:	d00b      	beq.n	44af2 <view_switch_to_rd_and_log+0x15a>
   44ada:	4b0c      	ldr	r3, [pc, #48]	; (44b0c <view_switch_to_rd_and_log+0x174>)
   44adc:	58e3      	ldr	r3, [r4, r3]
   44ade:	681a      	ldr	r2, [r3, #0]
   44ae0:	4b0c      	ldr	r3, [pc, #48]	; (44b14 <view_switch_to_rd_and_log+0x17c>)
   44ae2:	58e3      	ldr	r3, [r4, r3]
   44ae4:	681b      	ldr	r3, [r3, #0]
   44ae6:	4910      	ldr	r1, [pc, #64]	; (44b28 <view_switch_to_rd_and_log+0x190>)
   44ae8:	4479      	add	r1, pc
   44aea:	2001      	movs	r0, #1
   44aec:	f7cb efb0 	blx	10a50 <errx@plt>
   44af0:	bf00      	nop
   44af2:	3714      	adds	r7, #20
   44af4:	46bd      	mov	sp, r7
   44af6:	bd90      	pop	{r4, r7, pc}
   44af8:	00012656 	andeq	r2, r1, r6, asr r6
   44afc:	000000a8 	andeq	r0, r0, r8, lsr #1
   44b00:	000000c8 	andeq	r0, r0, r8, asr #1
   44b04:	00001df4 	strdeq	r1, [r0], -r4
   44b08:	00000090 	muleq	r0, r0, r0
   44b0c:	000000bc 	strheq	r0, [r0], -ip
   44b10:	00001dec 	andeq	r1, r0, ip, ror #27
   44b14:	000000a4 	andeq	r0, r0, r4, lsr #1
   44b18:	000000c4 	andeq	r0, r0, r4, asr #1
   44b1c:	000000b0 	strheq	r0, [r0], -r0	; <UNPREDICTABLE>
   44b20:	00001dd2 	ldrdeq	r1, [r0], -r2
   44b24:	000000c0 	andeq	r0, r0, r0, asr #1
   44b28:	00001d90 	muleq	r0, r0, sp

00044b2c <view_switch_to_text_and_log>:
   44b2c:	b598      	push	{r3, r4, r7, lr}
   44b2e:	af00      	add	r7, sp, #0
   44b30:	4c19      	ldr	r4, [pc, #100]	; (44b98 <view_switch_to_text_and_log+0x6c>)
   44b32:	447c      	add	r4, pc
   44b34:	223c      	movs	r2, #60	; 0x3c
   44b36:	2100      	movs	r1, #0
   44b38:	4b18      	ldr	r3, [pc, #96]	; (44b9c <view_switch_to_text_and_log+0x70>)
   44b3a:	58e3      	ldr	r3, [r4, r3]
   44b3c:	4618      	mov	r0, r3
   44b3e:	f7cb ef70 	blx	10a20 <memset@plt>
   44b42:	4b16      	ldr	r3, [pc, #88]	; (44b9c <view_switch_to_text_and_log+0x70>)
   44b44:	58e3      	ldr	r3, [r4, r3]
   44b46:	461a      	mov	r2, r3
   44b48:	2303      	movs	r3, #3
   44b4a:	6053      	str	r3, [r2, #4]
   44b4c:	4b13      	ldr	r3, [pc, #76]	; (44b9c <view_switch_to_text_and_log+0x70>)
   44b4e:	58e3      	ldr	r3, [r4, r3]
   44b50:	461a      	mov	r2, r3
   44b52:	f64f 73fa 	movw	r3, #65530	; 0xfffa
   44b56:	6093      	str	r3, [r2, #8]
   44b58:	4b11      	ldr	r3, [pc, #68]	; (44ba0 <view_switch_to_text_and_log+0x74>)
   44b5a:	58e3      	ldr	r3, [r4, r3]
   44b5c:	4a0f      	ldr	r2, [pc, #60]	; (44b9c <view_switch_to_text_and_log+0x70>)
   44b5e:	58a2      	ldr	r2, [r4, r2]
   44b60:	2100      	movs	r1, #0
   44b62:	4810      	ldr	r0, [pc, #64]	; (44ba4 <view_switch_to_text_and_log+0x78>)
   44b64:	5820      	ldr	r0, [r4, r0]
   44b66:	f001 f877 	bl	45c58 <TEEC_InvokeCommand>
   44b6a:	4602      	mov	r2, r0
   44b6c:	4b0e      	ldr	r3, [pc, #56]	; (44ba8 <view_switch_to_text_and_log+0x7c>)
   44b6e:	58e3      	ldr	r3, [r4, r3]
   44b70:	601a      	str	r2, [r3, #0]
   44b72:	4b0d      	ldr	r3, [pc, #52]	; (44ba8 <view_switch_to_text_and_log+0x7c>)
   44b74:	58e3      	ldr	r3, [r4, r3]
   44b76:	681b      	ldr	r3, [r3, #0]
   44b78:	2b00      	cmp	r3, #0
   44b7a:	d00a      	beq.n	44b92 <view_switch_to_text_and_log+0x66>
   44b7c:	4b0a      	ldr	r3, [pc, #40]	; (44ba8 <view_switch_to_text_and_log+0x7c>)
   44b7e:	58e3      	ldr	r3, [r4, r3]
   44b80:	681a      	ldr	r2, [r3, #0]
   44b82:	4b07      	ldr	r3, [pc, #28]	; (44ba0 <view_switch_to_text_and_log+0x74>)
   44b84:	58e3      	ldr	r3, [r4, r3]
   44b86:	681b      	ldr	r3, [r3, #0]
   44b88:	4908      	ldr	r1, [pc, #32]	; (44bac <view_switch_to_text_and_log+0x80>)
   44b8a:	4479      	add	r1, pc
   44b8c:	2001      	movs	r0, #1
   44b8e:	f7cb ef60 	blx	10a50 <errx@plt>
   44b92:	bf00      	nop
   44b94:	bd98      	pop	{r3, r4, r7, pc}
   44b96:	bf00      	nop
   44b98:	000124ca 	andeq	r2, r1, sl, asr #9
   44b9c:	000000c0 	andeq	r0, r0, r0, asr #1
   44ba0:	000000a4 	andeq	r0, r0, r4, lsr #1
   44ba4:	000000b0 	strheq	r0, [r0], -r0	; <UNPREDICTABLE>
   44ba8:	000000bc 	strheq	r0, [r0], -ip
   44bac:	00001cee 	andeq	r1, r0, lr, ror #25

00044bb0 <__test>:
   44bb0:	b480      	push	{r7}
   44bb2:	b085      	sub	sp, #20
   44bb4:	af00      	add	r7, sp, #0
   44bb6:	e9c7 0102 	strd	r0, r1, [r7, #8]
   44bba:	e9c7 2300 	strd	r2, r3, [r7]
   44bbe:	bf00      	nop
   44bc0:	3714      	adds	r7, #20
   44bc2:	46bd      	mov	sp, r7
   44bc4:	f85d 7b04 	ldr.w	r7, [sp], #4
   44bc8:	4770      	bx	lr

00044bca <__conditional_branch_recording>:
   44bca:	b480      	push	{r7}
   44bcc:	b083      	sub	sp, #12
   44bce:	af00      	add	r7, sp, #0
   44bd0:	4603      	mov	r3, r0
   44bd2:	71fb      	strb	r3, [r7, #7]
   44bd4:	bf00      	nop
   44bd6:	370c      	adds	r7, #12
   44bd8:	46bd      	mov	sp, r7
   44bda:	f85d 7b04 	ldr.w	r7, [sp], #4
   44bde:	4770      	bx	lr

00044be0 <__tsf_recording>:
   44be0:	b480      	push	{r7}
   44be2:	b083      	sub	sp, #12
   44be4:	af00      	add	r7, sp, #0
   44be6:	6078      	str	r0, [r7, #4]
   44be8:	6039      	str	r1, [r7, #0]
   44bea:	bf00      	nop
   44bec:	370c      	adds	r7, #12
   44bee:	46bd      	mov	sp, r7
   44bf0:	f85d 7b04 	ldr.w	r7, [sp], #4
   44bf4:	4770      	bx	lr

00044bf6 <write_two_numbers_to_file>:
   44bf6:	b580      	push	{r7, lr}
   44bf8:	b086      	sub	sp, #24
   44bfa:	af00      	add	r7, sp, #0
   44bfc:	60f8      	str	r0, [r7, #12]
   44bfe:	60b9      	str	r1, [r7, #8]
   44c00:	607a      	str	r2, [r7, #4]
   44c02:	4b0f      	ldr	r3, [pc, #60]	; (44c40 <write_two_numbers_to_file+0x4a>)
   44c04:	447b      	add	r3, pc
   44c06:	4619      	mov	r1, r3
   44c08:	6878      	ldr	r0, [r7, #4]
   44c0a:	f7cb eea4 	blx	10954 <fopen@plt>
   44c0e:	6178      	str	r0, [r7, #20]
   44c10:	697b      	ldr	r3, [r7, #20]
   44c12:	2b00      	cmp	r3, #0
   44c14:	d00a      	beq.n	44c2c <write_two_numbers_to_file+0x36>
   44c16:	68bb      	ldr	r3, [r7, #8]
   44c18:	68fa      	ldr	r2, [r7, #12]
   44c1a:	490a      	ldr	r1, [pc, #40]	; (44c44 <write_two_numbers_to_file+0x4e>)
   44c1c:	4479      	add	r1, pc
   44c1e:	6978      	ldr	r0, [r7, #20]
   44c20:	f7cb eeec 	blx	109fc <fprintf@plt>
   44c24:	6978      	ldr	r0, [r7, #20]
   44c26:	f7cb ef08 	blx	10a38 <fclose@plt>
   44c2a:	e005      	b.n	44c38 <write_two_numbers_to_file+0x42>
   44c2c:	6879      	ldr	r1, [r7, #4]
   44c2e:	4b06      	ldr	r3, [pc, #24]	; (44c48 <write_two_numbers_to_file+0x52>)
   44c30:	447b      	add	r3, pc
   44c32:	4618      	mov	r0, r3
   44c34:	f7cb ee88 	blx	10948 <printf@plt>
   44c38:	bf00      	nop
   44c3a:	3718      	adds	r7, #24
   44c3c:	46bd      	mov	sp, r7
   44c3e:	bd80      	pop	{r7, pc}
   44c40:	00001cac 	andeq	r1, r0, ip, lsr #25
   44c44:	00001c98 	muleq	r0, r8, ip
   44c48:	00001c8c 	andeq	r1, r0, ip, lsl #25

00044c4c <print_hash>:
   44c4c:	b580      	push	{r7, lr}
   44c4e:	b084      	sub	sp, #16
   44c50:	af00      	add	r7, sp, #0
   44c52:	6078      	str	r0, [r7, #4]
   44c54:	6039      	str	r1, [r7, #0]
   44c56:	2300      	movs	r3, #0
   44c58:	60fb      	str	r3, [r7, #12]
   44c5a:	e00c      	b.n	44c76 <print_hash+0x2a>
   44c5c:	687a      	ldr	r2, [r7, #4]
   44c5e:	68fb      	ldr	r3, [r7, #12]
   44c60:	4413      	add	r3, r2
   44c62:	781b      	ldrb	r3, [r3, #0]
   44c64:	4619      	mov	r1, r3
   44c66:	4b09      	ldr	r3, [pc, #36]	; (44c8c <print_hash+0x40>)
   44c68:	447b      	add	r3, pc
   44c6a:	4618      	mov	r0, r3
   44c6c:	f7cb ee6c 	blx	10948 <printf@plt>
   44c70:	68fb      	ldr	r3, [r7, #12]
   44c72:	3301      	adds	r3, #1
   44c74:	60fb      	str	r3, [r7, #12]
   44c76:	68fa      	ldr	r2, [r7, #12]
   44c78:	683b      	ldr	r3, [r7, #0]
   44c7a:	429a      	cmp	r2, r3
   44c7c:	d3ee      	bcc.n	44c5c <print_hash+0x10>
   44c7e:	200a      	movs	r0, #10
   44c80:	f7cb eed4 	blx	10a2c <putchar@plt>
   44c84:	bf00      	nop
   44c86:	3710      	adds	r7, #16
   44c88:	46bd      	mov	sp, r7
   44c8a:	bd80      	pop	{r7, pc}
   44c8c:	00001c70 	andeq	r1, r0, r0, ror ip

00044c90 <create_files>:
   44c90:	b580      	push	{r7, lr}
   44c92:	b08c      	sub	sp, #48	; 0x30
   44c94:	af00      	add	r7, sp, #0
   44c96:	60f8      	str	r0, [r7, #12]
   44c98:	60b9      	str	r1, [r7, #8]
   44c9a:	607a      	str	r2, [r7, #4]
   44c9c:	603b      	str	r3, [r7, #0]
   44c9e:	68fb      	ldr	r3, [r7, #12]
   44ca0:	617b      	str	r3, [r7, #20]
   44ca2:	68bb      	ldr	r3, [r7, #8]
   44ca4:	61bb      	str	r3, [r7, #24]
   44ca6:	687b      	ldr	r3, [r7, #4]
   44ca8:	61fb      	str	r3, [r7, #28]
   44caa:	683b      	ldr	r3, [r7, #0]
   44cac:	623b      	str	r3, [r7, #32]
   44cae:	6bbb      	ldr	r3, [r7, #56]	; 0x38
   44cb0:	627b      	str	r3, [r7, #36]	; 0x24
   44cb2:	2300      	movs	r3, #0
   44cb4:	62fb      	str	r3, [r7, #44]	; 0x2c
   44cb6:	e06d      	b.n	44d94 <create_files+0x104>
   44cb8:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   44cba:	009b      	lsls	r3, r3, #2
   44cbc:	f107 0230 	add.w	r2, r7, #48	; 0x30
   44cc0:	4413      	add	r3, r2
   44cc2:	f853 3c1c 	ldr.w	r3, [r3, #-28]
   44cc6:	4a37      	ldr	r2, [pc, #220]	; (44da4 <create_files+0x114>)
   44cc8:	447a      	add	r2, pc
   44cca:	4611      	mov	r1, r2
   44ccc:	4618      	mov	r0, r3
   44cce:	f7cb ee42 	blx	10954 <fopen@plt>
   44cd2:	62b8      	str	r0, [r7, #40]	; 0x28
   44cd4:	6abb      	ldr	r3, [r7, #40]	; 0x28
   44cd6:	2b00      	cmp	r3, #0
   44cd8:	d02a      	beq.n	44d30 <create_files+0xa0>
   44cda:	6ab8      	ldr	r0, [r7, #40]	; 0x28
   44cdc:	f7cb eeac 	blx	10a38 <fclose@plt>
   44ce0:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   44ce2:	009b      	lsls	r3, r3, #2
   44ce4:	f107 0230 	add.w	r2, r7, #48	; 0x30
   44ce8:	4413      	add	r3, r2
   44cea:	f853 3c1c 	ldr.w	r3, [r3, #-28]
   44cee:	4618      	mov	r0, r3
   44cf0:	f7cb eec0 	blx	10a74 <remove@plt>
   44cf4:	4603      	mov	r3, r0
   44cf6:	2b00      	cmp	r3, #0
   44cf8:	d10d      	bne.n	44d16 <create_files+0x86>
   44cfa:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   44cfc:	009b      	lsls	r3, r3, #2
   44cfe:	f107 0230 	add.w	r2, r7, #48	; 0x30
   44d02:	4413      	add	r3, r2
   44d04:	f853 3c1c 	ldr.w	r3, [r3, #-28]
   44d08:	4619      	mov	r1, r3
   44d0a:	4b27      	ldr	r3, [pc, #156]	; (44da8 <create_files+0x118>)
   44d0c:	447b      	add	r3, pc
   44d0e:	4618      	mov	r0, r3
   44d10:	f7cb ee1a 	blx	10948 <printf@plt>
   44d14:	e00c      	b.n	44d30 <create_files+0xa0>
   44d16:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   44d18:	009b      	lsls	r3, r3, #2
   44d1a:	f107 0230 	add.w	r2, r7, #48	; 0x30
   44d1e:	4413      	add	r3, r2
   44d20:	f853 3c1c 	ldr.w	r3, [r3, #-28]
   44d24:	4619      	mov	r1, r3
   44d26:	4b21      	ldr	r3, [pc, #132]	; (44dac <create_files+0x11c>)
   44d28:	447b      	add	r3, pc
   44d2a:	4618      	mov	r0, r3
   44d2c:	f7cb ee0c 	blx	10948 <printf@plt>
   44d30:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   44d32:	009b      	lsls	r3, r3, #2
   44d34:	f107 0230 	add.w	r2, r7, #48	; 0x30
   44d38:	4413      	add	r3, r2
   44d3a:	f853 3c1c 	ldr.w	r3, [r3, #-28]
   44d3e:	4a1c      	ldr	r2, [pc, #112]	; (44db0 <create_files+0x120>)
   44d40:	447a      	add	r2, pc
   44d42:	4611      	mov	r1, r2
   44d44:	4618      	mov	r0, r3
   44d46:	f7cb ee06 	blx	10954 <fopen@plt>
   44d4a:	62b8      	str	r0, [r7, #40]	; 0x28
   44d4c:	6abb      	ldr	r3, [r7, #40]	; 0x28
   44d4e:	2b00      	cmp	r3, #0
   44d50:	d010      	beq.n	44d74 <create_files+0xe4>
   44d52:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   44d54:	009b      	lsls	r3, r3, #2
   44d56:	f107 0230 	add.w	r2, r7, #48	; 0x30
   44d5a:	4413      	add	r3, r2
   44d5c:	f853 3c1c 	ldr.w	r3, [r3, #-28]
   44d60:	4619      	mov	r1, r3
   44d62:	4b14      	ldr	r3, [pc, #80]	; (44db4 <create_files+0x124>)
   44d64:	447b      	add	r3, pc
   44d66:	4618      	mov	r0, r3
   44d68:	f7cb edee 	blx	10948 <printf@plt>
   44d6c:	6ab8      	ldr	r0, [r7, #40]	; 0x28
   44d6e:	f7cb ee64 	blx	10a38 <fclose@plt>
   44d72:	e00c      	b.n	44d8e <create_files+0xfe>
   44d74:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   44d76:	009b      	lsls	r3, r3, #2
   44d78:	f107 0230 	add.w	r2, r7, #48	; 0x30
   44d7c:	4413      	add	r3, r2
   44d7e:	f853 3c1c 	ldr.w	r3, [r3, #-28]
   44d82:	4619      	mov	r1, r3
   44d84:	4b0c      	ldr	r3, [pc, #48]	; (44db8 <create_files+0x128>)
   44d86:	447b      	add	r3, pc
   44d88:	4618      	mov	r0, r3
   44d8a:	f7cb edde 	blx	10948 <printf@plt>
   44d8e:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   44d90:	3301      	adds	r3, #1
   44d92:	62fb      	str	r3, [r7, #44]	; 0x2c
   44d94:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   44d96:	2b04      	cmp	r3, #4
   44d98:	dd8e      	ble.n	44cb8 <create_files+0x28>
   44d9a:	bf00      	nop
   44d9c:	3730      	adds	r7, #48	; 0x30
   44d9e:	46bd      	mov	sp, r7
   44da0:	bd80      	pop	{r7, pc}
   44da2:	bf00      	nop
   44da4:	00001c18 	andeq	r1, r0, r8, lsl ip
   44da8:	00001bd8 	ldrdeq	r1, [r0], -r8
   44dac:	00001be0 	andeq	r1, r0, r0, ror #23
   44db0:	00001be8 	andeq	r1, r0, r8, ror #23
   44db4:	00001bc8 	andeq	r1, r0, r8, asr #23
   44db8:	00001bca 	andeq	r1, r0, sl, asr #23

00044dbc <read_measurement>:
   44dbc:	b590      	push	{r4, r7, lr}
   44dbe:	b085      	sub	sp, #20
   44dc0:	af00      	add	r7, sp, #0
   44dc2:	4c49      	ldr	r4, [pc, #292]	; (44ee8 <read_measurement+0x12c>)
   44dc4:	447c      	add	r4, pc
   44dc6:	463b      	mov	r3, r7
   44dc8:	4619      	mov	r1, r3
   44dca:	4b48      	ldr	r3, [pc, #288]	; (44eec <read_measurement+0x130>)
   44dcc:	58e3      	ldr	r3, [r4, r3]
   44dce:	4618      	mov	r0, r3
   44dd0:	f7fe ffd7 	bl	43d82 <pop>
   44dd4:	4603      	mov	r3, r0
   44dd6:	2b00      	cmp	r3, #0
   44dd8:	d0f5      	beq.n	44dc6 <read_measurement+0xa>
   44dda:	7b3b      	ldrb	r3, [r7, #12]
   44ddc:	2b01      	cmp	r3, #1
   44dde:	d807      	bhi.n	44df0 <read_measurement+0x34>
   44de0:	687b      	ldr	r3, [r7, #4]
   44de2:	4a43      	ldr	r2, [pc, #268]	; (44ef0 <read_measurement+0x134>)
   44de4:	447a      	add	r2, pc
   44de6:	4611      	mov	r1, r2
   44de8:	4618      	mov	r0, r3
   44dea:	f000 f89b 	bl	44f24 <write_number_to_file>
   44dee:	e048      	b.n	44e82 <read_measurement+0xc6>
   44df0:	7b3b      	ldrb	r3, [r7, #12]
   44df2:	2b03      	cmp	r3, #3
   44df4:	d830      	bhi.n	44e58 <read_measurement+0x9c>
   44df6:	4b3f      	ldr	r3, [pc, #252]	; (44ef4 <read_measurement+0x138>)
   44df8:	58e3      	ldr	r3, [r4, r3]
   44dfa:	681b      	ldr	r3, [r3, #0]
   44dfc:	2b00      	cmp	r3, #0
   44dfe:	d112      	bne.n	44e26 <read_measurement+0x6a>
   44e00:	4b3c      	ldr	r3, [pc, #240]	; (44ef4 <read_measurement+0x138>)
   44e02:	58e3      	ldr	r3, [r4, r3]
   44e04:	461a      	mov	r2, r3
   44e06:	2301      	movs	r3, #1
   44e08:	6013      	str	r3, [r2, #0]
   44e0a:	2120      	movs	r1, #32
   44e0c:	4b3a      	ldr	r3, [pc, #232]	; (44ef8 <read_measurement+0x13c>)
   44e0e:	58e3      	ldr	r3, [r4, r3]
   44e10:	4618      	mov	r0, r3
   44e12:	f7fb ff83 	bl	40d1c <blake2s_init>
   44e16:	4603      	mov	r3, r0
   44e18:	2b00      	cmp	r3, #0
   44e1a:	d004      	beq.n	44e26 <read_measurement+0x6a>
   44e1c:	4b37      	ldr	r3, [pc, #220]	; (44efc <read_measurement+0x140>)
   44e1e:	447b      	add	r3, pc
   44e20:	4618      	mov	r0, r3
   44e22:	f7cb edc8 	blx	109b4 <puts@plt>
   44e26:	463b      	mov	r3, r7
   44e28:	3304      	adds	r3, #4
   44e2a:	2204      	movs	r2, #4
   44e2c:	4619      	mov	r1, r3
   44e2e:	4b32      	ldr	r3, [pc, #200]	; (44ef8 <read_measurement+0x13c>)
   44e30:	58e3      	ldr	r3, [r4, r3]
   44e32:	4618      	mov	r0, r3
   44e34:	f7fe fe1e 	bl	43a74 <blake2s_update>
   44e38:	4603      	mov	r3, r0
   44e3a:	2b00      	cmp	r3, #0
   44e3c:	d004      	beq.n	44e48 <read_measurement+0x8c>
   44e3e:	4b30      	ldr	r3, [pc, #192]	; (44f00 <read_measurement+0x144>)
   44e40:	447b      	add	r3, pc
   44e42:	4618      	mov	r0, r3
   44e44:	f7cb edb6 	blx	109b4 <puts@plt>
   44e48:	687b      	ldr	r3, [r7, #4]
   44e4a:	4619      	mov	r1, r3
   44e4c:	4b2d      	ldr	r3, [pc, #180]	; (44f04 <read_measurement+0x148>)
   44e4e:	447b      	add	r3, pc
   44e50:	4618      	mov	r0, r3
   44e52:	f7cb ed7a 	blx	10948 <printf@plt>
   44e56:	e014      	b.n	44e82 <read_measurement+0xc6>
   44e58:	7b3b      	ldrb	r3, [r7, #12]
   44e5a:	2b04      	cmp	r3, #4
   44e5c:	d107      	bne.n	44e6e <read_measurement+0xb2>
   44e5e:	68bb      	ldr	r3, [r7, #8]
   44e60:	4a29      	ldr	r2, [pc, #164]	; (44f08 <read_measurement+0x14c>)
   44e62:	447a      	add	r2, pc
   44e64:	4611      	mov	r1, r2
   44e66:	4618      	mov	r0, r3
   44e68:	f000 f85c 	bl	44f24 <write_number_to_file>
   44e6c:	e009      	b.n	44e82 <read_measurement+0xc6>
   44e6e:	7b3b      	ldrb	r3, [r7, #12]
   44e70:	2b0a      	cmp	r3, #10
   44e72:	d106      	bne.n	44e82 <read_measurement+0xc6>
   44e74:	683b      	ldr	r3, [r7, #0]
   44e76:	6879      	ldr	r1, [r7, #4]
   44e78:	4a24      	ldr	r2, [pc, #144]	; (44f0c <read_measurement+0x150>)
   44e7a:	447a      	add	r2, pc
   44e7c:	4618      	mov	r0, r3
   44e7e:	f7ff feba 	bl	44bf6 <write_two_numbers_to_file>
   44e82:	4b1a      	ldr	r3, [pc, #104]	; (44eec <read_measurement+0x130>)
   44e84:	58e3      	ldr	r3, [r4, r3]
   44e86:	4618      	mov	r0, r3
   44e88:	f7fe ffe2 	bl	43e50 <is_empty>
   44e8c:	4603      	mov	r3, r0
   44e8e:	2b00      	cmp	r3, #0
   44e90:	d099      	beq.n	44dc6 <read_measurement+0xa>
   44e92:	4b1f      	ldr	r3, [pc, #124]	; (44f10 <read_measurement+0x154>)
   44e94:	58e3      	ldr	r3, [r4, r3]
   44e96:	681b      	ldr	r3, [r3, #0]
   44e98:	2b00      	cmp	r3, #0
   44e9a:	d194      	bne.n	44dc6 <read_measurement+0xa>
   44e9c:	4b1d      	ldr	r3, [pc, #116]	; (44f14 <read_measurement+0x158>)
   44e9e:	58e3      	ldr	r3, [r4, r3]
   44ea0:	681b      	ldr	r3, [r3, #0]
   44ea2:	2b00      	cmp	r3, #0
   44ea4:	d08f      	beq.n	44dc6 <read_measurement+0xa>
   44ea6:	2220      	movs	r2, #32
   44ea8:	4b1b      	ldr	r3, [pc, #108]	; (44f18 <read_measurement+0x15c>)
   44eaa:	58e3      	ldr	r3, [r4, r3]
   44eac:	4619      	mov	r1, r3
   44eae:	4b12      	ldr	r3, [pc, #72]	; (44ef8 <read_measurement+0x13c>)
   44eb0:	58e3      	ldr	r3, [r4, r3]
   44eb2:	4618      	mov	r0, r3
   44eb4:	f7fe fe3b 	bl	43b2e <blake2s_final>
   44eb8:	4603      	mov	r3, r0
   44eba:	2b00      	cmp	r3, #0
   44ebc:	d004      	beq.n	44ec8 <read_measurement+0x10c>
   44ebe:	4b17      	ldr	r3, [pc, #92]	; (44f1c <read_measurement+0x160>)
   44ec0:	447b      	add	r3, pc
   44ec2:	4618      	mov	r0, r3
   44ec4:	f7cb ed76 	blx	109b4 <puts@plt>
   44ec8:	4b15      	ldr	r3, [pc, #84]	; (44f20 <read_measurement+0x164>)
   44eca:	447b      	add	r3, pc
   44ecc:	461a      	mov	r2, r3
   44ece:	2120      	movs	r1, #32
   44ed0:	4b11      	ldr	r3, [pc, #68]	; (44f18 <read_measurement+0x15c>)
   44ed2:	58e3      	ldr	r3, [r4, r3]
   44ed4:	4618      	mov	r0, r3
   44ed6:	f000 f857 	bl	44f88 <write_array_to_file>
   44eda:	2120      	movs	r1, #32
   44edc:	4b0e      	ldr	r3, [pc, #56]	; (44f18 <read_measurement+0x15c>)
   44ede:	58e3      	ldr	r3, [r4, r3]
   44ee0:	4618      	mov	r0, r3
   44ee2:	f7ff feb3 	bl	44c4c <print_hash>
   44ee6:	e76e      	b.n	44dc6 <read_measurement+0xa>
   44ee8:	00012238 	andeq	r2, r1, r8, lsr r2
   44eec:	000000ac 	andeq	r0, r0, ip, lsr #1
   44ef0:	00001b8c 	andeq	r1, r0, ip, lsl #23
   44ef4:	0000009c 	muleq	r0, ip, r0
   44ef8:	00000098 	muleq	r0, r8, r0
   44efc:	00001b66 	andeq	r1, r0, r6, ror #22
   44f00:	00001b64 	andeq	r1, r0, r4, ror #22
   44f04:	00001b76 	andeq	r1, r0, r6, ror fp
   44f08:	00001b7a 	andeq	r1, r0, sl, ror fp
   44f0c:	00001b76 	andeq	r1, r0, r6, ror fp
   44f10:	000000b4 	strheq	r0, [r0], -r4
   44f14:	0000008c 	andeq	r0, r0, ip, lsl #1
   44f18:	000000a0 	andeq	r0, r0, r0, lsr #1
   44f1c:	00001b40 	andeq	r1, r0, r0, asr #22
   44f20:	00001b5a 	andeq	r1, r0, sl, asr fp

00044f24 <write_number_to_file>:
   44f24:	b580      	push	{r7, lr}
   44f26:	b086      	sub	sp, #24
   44f28:	af00      	add	r7, sp, #0
   44f2a:	6078      	str	r0, [r7, #4]
   44f2c:	6039      	str	r1, [r7, #0]
   44f2e:	4b13      	ldr	r3, [pc, #76]	; (44f7c <write_number_to_file+0x58>)
   44f30:	447b      	add	r3, pc
   44f32:	4619      	mov	r1, r3
   44f34:	6838      	ldr	r0, [r7, #0]
   44f36:	f7cb ed0e 	blx	10954 <fopen@plt>
   44f3a:	6178      	str	r0, [r7, #20]
   44f3c:	697b      	ldr	r3, [r7, #20]
   44f3e:	2b00      	cmp	r3, #0
   44f40:	d011      	beq.n	44f66 <write_number_to_file+0x42>
   44f42:	f107 0308 	add.w	r3, r7, #8
   44f46:	687a      	ldr	r2, [r7, #4]
   44f48:	490d      	ldr	r1, [pc, #52]	; (44f80 <write_number_to_file+0x5c>)
   44f4a:	4479      	add	r1, pc
   44f4c:	4618      	mov	r0, r3
   44f4e:	f7cb ed86 	blx	10a5c <sprintf@plt>
   44f52:	f107 0308 	add.w	r3, r7, #8
   44f56:	6979      	ldr	r1, [r7, #20]
   44f58:	4618      	mov	r0, r3
   44f5a:	f7cb ed9e 	blx	10a98 <fputs@plt>
   44f5e:	6978      	ldr	r0, [r7, #20]
   44f60:	f7cb ed6a 	blx	10a38 <fclose@plt>
   44f64:	e005      	b.n	44f72 <write_number_to_file+0x4e>
   44f66:	6839      	ldr	r1, [r7, #0]
   44f68:	4b06      	ldr	r3, [pc, #24]	; (44f84 <write_number_to_file+0x60>)
   44f6a:	447b      	add	r3, pc
   44f6c:	4618      	mov	r0, r3
   44f6e:	f7cb ecec 	blx	10948 <printf@plt>
   44f72:	bf00      	nop
   44f74:	3718      	adds	r7, #24
   44f76:	46bd      	mov	sp, r7
   44f78:	bd80      	pop	{r7, pc}
   44f7a:	bf00      	nop
   44f7c:	00001980 	andeq	r1, r0, r0, lsl #19
   44f80:	00001aee 	andeq	r1, r0, lr, ror #21
   44f84:	00001952 	andeq	r1, r0, r2, asr r9

00044f88 <write_array_to_file>:
   44f88:	b580      	push	{r7, lr}
   44f8a:	b086      	sub	sp, #24
   44f8c:	af00      	add	r7, sp, #0
   44f8e:	60f8      	str	r0, [r7, #12]
   44f90:	60b9      	str	r1, [r7, #8]
   44f92:	607a      	str	r2, [r7, #4]
   44f94:	4b16      	ldr	r3, [pc, #88]	; (44ff0 <write_array_to_file+0x68>)
   44f96:	447b      	add	r3, pc
   44f98:	4619      	mov	r1, r3
   44f9a:	6878      	ldr	r0, [r7, #4]
   44f9c:	f7cb ecda 	blx	10954 <fopen@plt>
   44fa0:	6138      	str	r0, [r7, #16]
   44fa2:	693b      	ldr	r3, [r7, #16]
   44fa4:	2b00      	cmp	r3, #0
   44fa6:	d018      	beq.n	44fda <write_array_to_file+0x52>
   44fa8:	2300      	movs	r3, #0
   44faa:	617b      	str	r3, [r7, #20]
   44fac:	e00d      	b.n	44fca <write_array_to_file+0x42>
   44fae:	68fa      	ldr	r2, [r7, #12]
   44fb0:	697b      	ldr	r3, [r7, #20]
   44fb2:	4413      	add	r3, r2
   44fb4:	781b      	ldrb	r3, [r3, #0]
   44fb6:	461a      	mov	r2, r3
   44fb8:	4b0e      	ldr	r3, [pc, #56]	; (44ff4 <write_array_to_file+0x6c>)
   44fba:	447b      	add	r3, pc
   44fbc:	4619      	mov	r1, r3
   44fbe:	6938      	ldr	r0, [r7, #16]
   44fc0:	f7cb ed1c 	blx	109fc <fprintf@plt>
   44fc4:	697b      	ldr	r3, [r7, #20]
   44fc6:	3301      	adds	r3, #1
   44fc8:	617b      	str	r3, [r7, #20]
   44fca:	697a      	ldr	r2, [r7, #20]
   44fcc:	68bb      	ldr	r3, [r7, #8]
   44fce:	429a      	cmp	r2, r3
   44fd0:	d3ed      	bcc.n	44fae <write_array_to_file+0x26>
   44fd2:	6938      	ldr	r0, [r7, #16]
   44fd4:	f7cb ed30 	blx	10a38 <fclose@plt>
   44fd8:	e005      	b.n	44fe6 <write_array_to_file+0x5e>
   44fda:	6879      	ldr	r1, [r7, #4]
   44fdc:	4b06      	ldr	r3, [pc, #24]	; (44ff8 <write_array_to_file+0x70>)
   44fde:	447b      	add	r3, pc
   44fe0:	4618      	mov	r0, r3
   44fe2:	f7cb ecb2 	blx	10948 <printf@plt>
   44fe6:	bf00      	nop
   44fe8:	3718      	adds	r7, #24
   44fea:	46bd      	mov	sp, r7
   44fec:	bd80      	pop	{r7, pc}
   44fee:	bf00      	nop
   44ff0:	00001aa6 	andeq	r1, r0, r6, lsr #21
   44ff4:	00001a7e 	andeq	r1, r0, lr, ror sl
   44ff8:	000018de 	ldrdeq	r1, [r0], -lr

00044ffc <bm_timestamp>:
   44ffc:	b480      	push	{r7}
   44ffe:	af00      	add	r7, sp, #0
   45000:	bf00      	nop
   45002:	46bd      	mov	sp, r7
   45004:	f85d 7b04 	ldr.w	r7, [sp], #4
   45008:	4770      	bx	lr

0004500a <teec_mutex_lock>:
   4500a:	b580      	push	{r7, lr}
   4500c:	b082      	sub	sp, #8
   4500e:	af00      	add	r7, sp, #0
   45010:	6078      	str	r0, [r7, #4]
   45012:	6878      	ldr	r0, [r7, #4]
   45014:	f7cb ecaa 	blx	1096c <pthread_mutex_lock@plt>
   45018:	bf00      	nop
   4501a:	3708      	adds	r7, #8
   4501c:	46bd      	mov	sp, r7
   4501e:	bd80      	pop	{r7, pc}

00045020 <teec_mutex_unlock>:
   45020:	b580      	push	{r7, lr}
   45022:	b082      	sub	sp, #8
   45024:	af00      	add	r7, sp, #0
   45026:	6078      	str	r0, [r7, #4]
   45028:	6878      	ldr	r0, [r7, #4]
   4502a:	f7cb ec82 	blx	10930 <pthread_mutex_unlock@plt>
   4502e:	bf00      	nop
   45030:	3708      	adds	r7, #8
   45032:	46bd      	mov	sp, r7
   45034:	bd80      	pop	{r7, pc}

00045036 <teec_open_dev>:
   45036:	b580      	push	{r7, lr}
   45038:	b08a      	sub	sp, #40	; 0x28
   4503a:	af02      	add	r7, sp, #8
   4503c:	60f8      	str	r0, [r7, #12]
   4503e:	60b9      	str	r1, [r7, #8]
   45040:	607a      	str	r2, [r7, #4]
   45042:	2102      	movs	r1, #2
   45044:	68f8      	ldr	r0, [r7, #12]
   45046:	f7cb ecc8 	blx	109d8 <open@plt>
   4504a:	61f8      	str	r0, [r7, #28]
   4504c:	69fb      	ldr	r3, [r7, #28]
   4504e:	2b00      	cmp	r3, #0
   45050:	da02      	bge.n	45058 <teec_open_dev+0x22>
   45052:	f04f 33ff 	mov.w	r3, #4294967295	; 0xffffffff
   45056:	e042      	b.n	450de <teec_open_dev+0xa8>
   45058:	f107 0310 	add.w	r3, r7, #16
   4505c:	461a      	mov	r2, r3
   4505e:	f44f 4124 	mov.w	r1, #41984	; 0xa400
   45062:	f2c8 010c 	movt	r1, #32780	; 0x800c
   45066:	69f8      	ldr	r0, [r7, #28]
   45068:	f7cb ec92 	blx	10990 <ioctl@plt>
   4506c:	4603      	mov	r3, r0
   4506e:	2b00      	cmp	r3, #0
   45070:	d00b      	beq.n	4508a <teec_open_dev+0x54>
   45072:	4b1d      	ldr	r3, [pc, #116]	; (450e8 <teec_open_dev+0xb2>)
   45074:	447b      	add	r3, pc
   45076:	9300      	str	r3, [sp, #0]
   45078:	4b1c      	ldr	r3, [pc, #112]	; (450ec <teec_open_dev+0xb6>)
   4507a:	447b      	add	r3, pc
   4507c:	2201      	movs	r2, #1
   4507e:	214d      	movs	r1, #77	; 0x4d
   45080:	481b      	ldr	r0, [pc, #108]	; (450f0 <teec_open_dev+0xba>)
   45082:	4478      	add	r0, pc
   45084:	f001 f8d0 	bl	46228 <_dprintf>
   45088:	e024      	b.n	450d4 <teec_open_dev+0x9e>
   4508a:	69bb      	ldr	r3, [r7, #24]
   4508c:	f003 0301 	and.w	r3, r3, #1
   45090:	2b00      	cmp	r3, #0
   45092:	d018      	beq.n	450c6 <teec_open_dev+0x90>
   45094:	68bb      	ldr	r3, [r7, #8]
   45096:	2b00      	cmp	r3, #0
   45098:	d010      	beq.n	450bc <teec_open_dev+0x86>
   4509a:	4b16      	ldr	r3, [pc, #88]	; (450f4 <teec_open_dev+0xbe>)
   4509c:	447b      	add	r3, pc
   4509e:	4619      	mov	r1, r3
   450a0:	68b8      	ldr	r0, [r7, #8]
   450a2:	f7cb ec4c 	blx	1093c <strcmp@plt>
   450a6:	4603      	mov	r3, r0
   450a8:	2b00      	cmp	r3, #0
   450aa:	d10e      	bne.n	450ca <teec_open_dev+0x94>
   450ac:	693b      	ldr	r3, [r7, #16]
   450ae:	2b01      	cmp	r3, #1
   450b0:	d10d      	bne.n	450ce <teec_open_dev+0x98>
   450b2:	697b      	ldr	r3, [r7, #20]
   450b4:	f003 0301 	and.w	r3, r3, #1
   450b8:	2b00      	cmp	r3, #0
   450ba:	d00a      	beq.n	450d2 <teec_open_dev+0x9c>
   450bc:	69ba      	ldr	r2, [r7, #24]
   450be:	687b      	ldr	r3, [r7, #4]
   450c0:	601a      	str	r2, [r3, #0]
   450c2:	69fb      	ldr	r3, [r7, #28]
   450c4:	e00b      	b.n	450de <teec_open_dev+0xa8>
   450c6:	bf00      	nop
   450c8:	e004      	b.n	450d4 <teec_open_dev+0x9e>
   450ca:	bf00      	nop
   450cc:	e002      	b.n	450d4 <teec_open_dev+0x9e>
   450ce:	bf00      	nop
   450d0:	e000      	b.n	450d4 <teec_open_dev+0x9e>
   450d2:	bf00      	nop
   450d4:	69f8      	ldr	r0, [r7, #28]
   450d6:	f7cb ece6 	blx	10aa4 <close@plt>
   450da:	f04f 33ff 	mov.w	r3, #4294967295	; 0xffffffff
   450de:	4618      	mov	r0, r3
   450e0:	3720      	adds	r7, #32
   450e2:	46bd      	mov	sp, r7
   450e4:	bd80      	pop	{r7, pc}
   450e6:	bf00      	nop
   450e8:	000019d4 	ldrdeq	r1, [r0], -r4
   450ec:	000019c6 	andeq	r1, r0, r6, asr #19
   450f0:	00001a62 	andeq	r1, r0, r2, ror #20
   450f4:	000019c4 	andeq	r1, r0, r4, asr #19

000450f8 <teec_shm_alloc>:
   450f8:	b590      	push	{r4, r7, lr}
   450fa:	b08b      	sub	sp, #44	; 0x2c
   450fc:	af00      	add	r7, sp, #0
   450fe:	60f8      	str	r0, [r7, #12]
   45100:	60b9      	str	r1, [r7, #8]
   45102:	607a      	str	r2, [r7, #4]
   45104:	f107 0310 	add.w	r3, r7, #16
   45108:	2210      	movs	r2, #16
   4510a:	2100      	movs	r1, #0
   4510c:	4618      	mov	r0, r3
   4510e:	f7cb ec88 	blx	10a20 <memset@plt>
   45112:	68bb      	ldr	r3, [r7, #8]
   45114:	f04f 0400 	mov.w	r4, #0
   45118:	e9c7 3404 	strd	r3, r4, [r7, #16]
   4511c:	f107 0310 	add.w	r3, r7, #16
   45120:	461a      	mov	r2, r3
   45122:	f24a 4101 	movw	r1, #41985	; 0xa401
   45126:	f2cc 0110 	movt	r1, #49168	; 0xc010
   4512a:	68f8      	ldr	r0, [r7, #12]
   4512c:	f7cb ec30 	blx	10990 <ioctl@plt>
   45130:	6278      	str	r0, [r7, #36]	; 0x24
   45132:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   45134:	2b00      	cmp	r3, #0
   45136:	da02      	bge.n	4513e <teec_shm_alloc+0x46>
   45138:	f04f 33ff 	mov.w	r3, #4294967295	; 0xffffffff
   4513c:	e003      	b.n	45146 <teec_shm_alloc+0x4e>
   4513e:	69fa      	ldr	r2, [r7, #28]
   45140:	687b      	ldr	r3, [r7, #4]
   45142:	601a      	str	r2, [r3, #0]
   45144:	6a7b      	ldr	r3, [r7, #36]	; 0x24
   45146:	4618      	mov	r0, r3
   45148:	372c      	adds	r7, #44	; 0x2c
   4514a:	46bd      	mov	sp, r7
   4514c:	bd90      	pop	{r4, r7, pc}

0004514e <teec_shm_register>:
   4514e:	b590      	push	{r4, r7, lr}
   45150:	b08d      	sub	sp, #52	; 0x34
   45152:	af00      	add	r7, sp, #0
   45154:	60f8      	str	r0, [r7, #12]
   45156:	60b9      	str	r1, [r7, #8]
   45158:	607a      	str	r2, [r7, #4]
   4515a:	603b      	str	r3, [r7, #0]
   4515c:	f107 0310 	add.w	r3, r7, #16
   45160:	2218      	movs	r2, #24
   45162:	2100      	movs	r1, #0
   45164:	4618      	mov	r0, r3
   45166:	f7cb ec5c 	blx	10a20 <memset@plt>
   4516a:	68bb      	ldr	r3, [r7, #8]
   4516c:	f04f 0400 	mov.w	r4, #0
   45170:	e9c7 3404 	strd	r3, r4, [r7, #16]
   45174:	687b      	ldr	r3, [r7, #4]
   45176:	f04f 0400 	mov.w	r4, #0
   4517a:	e9c7 3406 	strd	r3, r4, [r7, #24]
   4517e:	f107 0310 	add.w	r3, r7, #16
   45182:	461a      	mov	r2, r3
   45184:	f24a 4109 	movw	r1, #41993	; 0xa409
   45188:	f2cc 0118 	movt	r1, #49176	; 0xc018
   4518c:	68f8      	ldr	r0, [r7, #12]
   4518e:	f7cb ec00 	blx	10990 <ioctl@plt>
   45192:	62f8      	str	r0, [r7, #44]	; 0x2c
   45194:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   45196:	2b00      	cmp	r3, #0
   45198:	da02      	bge.n	451a0 <teec_shm_register+0x52>
   4519a:	f04f 33ff 	mov.w	r3, #4294967295	; 0xffffffff
   4519e:	e003      	b.n	451a8 <teec_shm_register+0x5a>
   451a0:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   451a2:	683b      	ldr	r3, [r7, #0]
   451a4:	601a      	str	r2, [r3, #0]
   451a6:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   451a8:	4618      	mov	r0, r3
   451aa:	3734      	adds	r7, #52	; 0x34
   451ac:	46bd      	mov	sp, r7
   451ae:	bd90      	pop	{r4, r7, pc}

000451b0 <TEEC_InitializeContext>:
   451b0:	b580      	push	{r7, lr}
   451b2:	f5ad 5d80 	sub.w	sp, sp, #4096	; 0x1000
   451b6:	b086      	sub	sp, #24
   451b8:	af00      	add	r7, sp, #0
   451ba:	f107 0318 	add.w	r3, r7, #24
   451be:	3b14      	subs	r3, #20
   451c0:	6018      	str	r0, [r3, #0]
   451c2:	f107 0318 	add.w	r3, r7, #24
   451c6:	3b18      	subs	r3, #24
   451c8:	6019      	str	r1, [r3, #0]
   451ca:	f107 0318 	add.w	r3, r7, #24
   451ce:	3b18      	subs	r3, #24
   451d0:	681b      	ldr	r3, [r3, #0]
   451d2:	2b00      	cmp	r3, #0
   451d4:	d103      	bne.n	451de <TEEC_InitializeContext+0x2e>
   451d6:	2306      	movs	r3, #6
   451d8:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   451dc:	e05d      	b.n	4529a <TEEC_InitializeContext+0xea>
   451de:	2300      	movs	r3, #0
   451e0:	f507 5280 	add.w	r2, r7, #4096	; 0x1000
   451e4:	f102 0214 	add.w	r2, r2, #20
   451e8:	6013      	str	r3, [r2, #0]
   451ea:	e04c      	b.n	45286 <TEEC_InitializeContext+0xd6>
   451ec:	f107 0018 	add.w	r0, r7, #24
   451f0:	3808      	subs	r0, #8
   451f2:	f507 5380 	add.w	r3, r7, #4096	; 0x1000
   451f6:	f103 0314 	add.w	r3, r3, #20
   451fa:	681b      	ldr	r3, [r3, #0]
   451fc:	4a2a      	ldr	r2, [pc, #168]	; (452a8 <TEEC_InitializeContext+0xf8>)
   451fe:	447a      	add	r2, pc
   45200:	f44f 5180 	mov.w	r1, #4096	; 0x1000
   45204:	f7cb ec06 	blx	10a14 <snprintf@plt>
   45208:	f107 0218 	add.w	r2, r7, #24
   4520c:	3a0c      	subs	r2, #12
   4520e:	f107 0318 	add.w	r3, r7, #24
   45212:	3b14      	subs	r3, #20
   45214:	f107 0018 	add.w	r0, r7, #24
   45218:	3808      	subs	r0, #8
   4521a:	6819      	ldr	r1, [r3, #0]
   4521c:	f7ff ff0b 	bl	45036 <teec_open_dev>
   45220:	f507 5380 	add.w	r3, r7, #4096	; 0x1000
   45224:	f103 0310 	add.w	r3, r3, #16
   45228:	6018      	str	r0, [r3, #0]
   4522a:	f507 5380 	add.w	r3, r7, #4096	; 0x1000
   4522e:	f103 0310 	add.w	r3, r3, #16
   45232:	681b      	ldr	r3, [r3, #0]
   45234:	2b00      	cmp	r3, #0
   45236:	db1b      	blt.n	45270 <TEEC_InitializeContext+0xc0>
   45238:	f107 0318 	add.w	r3, r7, #24
   4523c:	3b18      	subs	r3, #24
   4523e:	681b      	ldr	r3, [r3, #0]
   45240:	f507 5280 	add.w	r2, r7, #4096	; 0x1000
   45244:	f102 0210 	add.w	r2, r2, #16
   45248:	6812      	ldr	r2, [r2, #0]
   4524a:	601a      	str	r2, [r3, #0]
   4524c:	f107 0318 	add.w	r3, r7, #24
   45250:	3b0c      	subs	r3, #12
   45252:	681b      	ldr	r3, [r3, #0]
   45254:	f003 0304 	and.w	r3, r3, #4
   45258:	2b00      	cmp	r3, #0
   4525a:	bf14      	ite	ne
   4525c:	2301      	movne	r3, #1
   4525e:	2300      	moveq	r3, #0
   45260:	b2da      	uxtb	r2, r3
   45262:	f107 0318 	add.w	r3, r7, #24
   45266:	3b18      	subs	r3, #24
   45268:	681b      	ldr	r3, [r3, #0]
   4526a:	711a      	strb	r2, [r3, #4]
   4526c:	2300      	movs	r3, #0
   4526e:	e014      	b.n	4529a <TEEC_InitializeContext+0xea>
   45270:	f507 5380 	add.w	r3, r7, #4096	; 0x1000
   45274:	f103 0314 	add.w	r3, r3, #20
   45278:	681b      	ldr	r3, [r3, #0]
   4527a:	3301      	adds	r3, #1
   4527c:	f507 5280 	add.w	r2, r7, #4096	; 0x1000
   45280:	f102 0214 	add.w	r2, r2, #20
   45284:	6013      	str	r3, [r2, #0]
   45286:	f507 5380 	add.w	r3, r7, #4096	; 0x1000
   4528a:	f103 0314 	add.w	r3, r3, #20
   4528e:	681b      	ldr	r3, [r3, #0]
   45290:	2b09      	cmp	r3, #9
   45292:	d9ab      	bls.n	451ec <TEEC_InitializeContext+0x3c>
   45294:	2308      	movs	r3, #8
   45296:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   4529a:	4618      	mov	r0, r3
   4529c:	f507 5780 	add.w	r7, r7, #4096	; 0x1000
   452a0:	3718      	adds	r7, #24
   452a2:	46bd      	mov	sp, r7
   452a4:	bd80      	pop	{r7, pc}
   452a6:	bf00      	nop
   452a8:	0000186e 	andeq	r1, r0, lr, ror #16

000452ac <TEEC_FinalizeContext>:
   452ac:	b580      	push	{r7, lr}
   452ae:	b082      	sub	sp, #8
   452b0:	af00      	add	r7, sp, #0
   452b2:	6078      	str	r0, [r7, #4]
   452b4:	687b      	ldr	r3, [r7, #4]
   452b6:	2b00      	cmp	r3, #0
   452b8:	d004      	beq.n	452c4 <TEEC_FinalizeContext+0x18>
   452ba:	687b      	ldr	r3, [r7, #4]
   452bc:	681b      	ldr	r3, [r3, #0]
   452be:	4618      	mov	r0, r3
   452c0:	f7cb ebf0 	blx	10aa4 <close@plt>
   452c4:	bf00      	nop
   452c6:	3708      	adds	r7, #8
   452c8:	46bd      	mov	sp, r7
   452ca:	bd80      	pop	{r7, pc}

000452cc <teec_pre_process_tmpref>:
   452cc:	b590      	push	{r4, r7, lr}
   452ce:	b087      	sub	sp, #28
   452d0:	af00      	add	r7, sp, #0
   452d2:	60f8      	str	r0, [r7, #12]
   452d4:	60b9      	str	r1, [r7, #8]
   452d6:	607a      	str	r2, [r7, #4]
   452d8:	603b      	str	r3, [r7, #0]
   452da:	68bb      	ldr	r3, [r7, #8]
   452dc:	2b06      	cmp	r3, #6
   452de:	d00e      	beq.n	452fe <teec_pre_process_tmpref+0x32>
   452e0:	2b07      	cmp	r3, #7
   452e2:	d017      	beq.n	45314 <teec_pre_process_tmpref+0x48>
   452e4:	2b05      	cmp	r3, #5
   452e6:	d120      	bne.n	4532a <teec_pre_process_tmpref+0x5e>
   452e8:	683a      	ldr	r2, [r7, #0]
   452ea:	f04f 0305 	mov.w	r3, #5
   452ee:	f04f 0400 	mov.w	r4, #0
   452f2:	e9c2 3400 	strd	r3, r4, [r2]
   452f6:	6abb      	ldr	r3, [r7, #40]	; 0x28
   452f8:	2201      	movs	r2, #1
   452fa:	609a      	str	r2, [r3, #8]
   452fc:	e019      	b.n	45332 <teec_pre_process_tmpref+0x66>
   452fe:	683a      	ldr	r2, [r7, #0]
   45300:	f04f 0306 	mov.w	r3, #6
   45304:	f04f 0400 	mov.w	r4, #0
   45308:	e9c2 3400 	strd	r3, r4, [r2]
   4530c:	6abb      	ldr	r3, [r7, #40]	; 0x28
   4530e:	2202      	movs	r2, #2
   45310:	609a      	str	r2, [r3, #8]
   45312:	e00e      	b.n	45332 <teec_pre_process_tmpref+0x66>
   45314:	683a      	ldr	r2, [r7, #0]
   45316:	f04f 0307 	mov.w	r3, #7
   4531a:	f04f 0400 	mov.w	r4, #0
   4531e:	e9c2 3400 	strd	r3, r4, [r2]
   45322:	6abb      	ldr	r3, [r7, #40]	; 0x28
   45324:	2203      	movs	r2, #3
   45326:	609a      	str	r2, [r3, #8]
   45328:	e003      	b.n	45332 <teec_pre_process_tmpref+0x66>
   4532a:	2306      	movs	r3, #6
   4532c:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   45330:	e025      	b.n	4537e <teec_pre_process_tmpref+0xb2>
   45332:	687b      	ldr	r3, [r7, #4]
   45334:	685a      	ldr	r2, [r3, #4]
   45336:	6abb      	ldr	r3, [r7, #40]	; 0x28
   45338:	605a      	str	r2, [r3, #4]
   4533a:	6ab9      	ldr	r1, [r7, #40]	; 0x28
   4533c:	68f8      	ldr	r0, [r7, #12]
   4533e:	f000 fe86 	bl	4604e <TEEC_AllocateSharedMemory>
   45342:	6178      	str	r0, [r7, #20]
   45344:	697b      	ldr	r3, [r7, #20]
   45346:	2b00      	cmp	r3, #0
   45348:	d001      	beq.n	4534e <teec_pre_process_tmpref+0x82>
   4534a:	697b      	ldr	r3, [r7, #20]
   4534c:	e017      	b.n	4537e <teec_pre_process_tmpref+0xb2>
   4534e:	6abb      	ldr	r3, [r7, #40]	; 0x28
   45350:	6818      	ldr	r0, [r3, #0]
   45352:	687b      	ldr	r3, [r7, #4]
   45354:	6819      	ldr	r1, [r3, #0]
   45356:	687b      	ldr	r3, [r7, #4]
   45358:	685b      	ldr	r3, [r3, #4]
   4535a:	461a      	mov	r2, r3
   4535c:	f7cb eb0c 	blx	10978 <memcpy@plt>
   45360:	687b      	ldr	r3, [r7, #4]
   45362:	685b      	ldr	r3, [r3, #4]
   45364:	f04f 0400 	mov.w	r4, #0
   45368:	683a      	ldr	r2, [r7, #0]
   4536a:	e9c2 3404 	strd	r3, r4, [r2, #16]
   4536e:	6abb      	ldr	r3, [r7, #40]	; 0x28
   45370:	68db      	ldr	r3, [r3, #12]
   45372:	ea4f 74e3 	mov.w	r4, r3, asr #31
   45376:	683a      	ldr	r2, [r7, #0]
   45378:	e9c2 3406 	strd	r3, r4, [r2, #24]
   4537c:	2300      	movs	r3, #0
   4537e:	4618      	mov	r0, r3
   45380:	371c      	adds	r7, #28
   45382:	46bd      	mov	sp, r7
   45384:	bd90      	pop	{r4, r7, pc}

00045386 <teec_pre_process_whole>:
   45386:	b590      	push	{r4, r7, lr}
   45388:	b087      	sub	sp, #28
   4538a:	af00      	add	r7, sp, #0
   4538c:	6078      	str	r0, [r7, #4]
   4538e:	6039      	str	r1, [r7, #0]
   45390:	2303      	movs	r3, #3
   45392:	617b      	str	r3, [r7, #20]
   45394:	687b      	ldr	r3, [r7, #4]
   45396:	681b      	ldr	r3, [r3, #0]
   45398:	689a      	ldr	r2, [r3, #8]
   4539a:	697b      	ldr	r3, [r7, #20]
   4539c:	4013      	ands	r3, r2
   4539e:	613b      	str	r3, [r7, #16]
   453a0:	693a      	ldr	r2, [r7, #16]
   453a2:	697b      	ldr	r3, [r7, #20]
   453a4:	429a      	cmp	r2, r3
   453a6:	d107      	bne.n	453b8 <teec_pre_process_whole+0x32>
   453a8:	683a      	ldr	r2, [r7, #0]
   453aa:	f04f 0307 	mov.w	r3, #7
   453ae:	f04f 0400 	mov.w	r4, #0
   453b2:	e9c2 3400 	strd	r3, r4, [r2]
   453b6:	e01d      	b.n	453f4 <teec_pre_process_whole+0x6e>
   453b8:	693b      	ldr	r3, [r7, #16]
   453ba:	f003 0301 	and.w	r3, r3, #1
   453be:	2b00      	cmp	r3, #0
   453c0:	d007      	beq.n	453d2 <teec_pre_process_whole+0x4c>
   453c2:	683a      	ldr	r2, [r7, #0]
   453c4:	f04f 0305 	mov.w	r3, #5
   453c8:	f04f 0400 	mov.w	r4, #0
   453cc:	e9c2 3400 	strd	r3, r4, [r2]
   453d0:	e010      	b.n	453f4 <teec_pre_process_whole+0x6e>
   453d2:	693b      	ldr	r3, [r7, #16]
   453d4:	f003 0302 	and.w	r3, r3, #2
   453d8:	2b00      	cmp	r3, #0
   453da:	d007      	beq.n	453ec <teec_pre_process_whole+0x66>
   453dc:	683a      	ldr	r2, [r7, #0]
   453de:	f04f 0306 	mov.w	r3, #6
   453e2:	f04f 0400 	mov.w	r4, #0
   453e6:	e9c2 3400 	strd	r3, r4, [r2]
   453ea:	e003      	b.n	453f4 <teec_pre_process_whole+0x6e>
   453ec:	2306      	movs	r3, #6
   453ee:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   453f2:	e023      	b.n	4543c <teec_pre_process_whole+0xb6>
   453f4:	687b      	ldr	r3, [r7, #4]
   453f6:	681b      	ldr	r3, [r3, #0]
   453f8:	60fb      	str	r3, [r7, #12]
   453fa:	68fb      	ldr	r3, [r7, #12]
   453fc:	695b      	ldr	r3, [r3, #20]
   453fe:	2b00      	cmp	r3, #0
   45400:	d00d      	beq.n	4541e <teec_pre_process_whole+0x98>
   45402:	693b      	ldr	r3, [r7, #16]
   45404:	f003 0301 	and.w	r3, r3, #1
   45408:	2b00      	cmp	r3, #0
   4540a:	d008      	beq.n	4541e <teec_pre_process_whole+0x98>
   4540c:	68fb      	ldr	r3, [r7, #12]
   4540e:	6958      	ldr	r0, [r3, #20]
   45410:	68fb      	ldr	r3, [r7, #12]
   45412:	6819      	ldr	r1, [r3, #0]
   45414:	68fb      	ldr	r3, [r7, #12]
   45416:	685b      	ldr	r3, [r3, #4]
   45418:	461a      	mov	r2, r3
   4541a:	f7cb eaae 	blx	10978 <memcpy@plt>
   4541e:	68fb      	ldr	r3, [r7, #12]
   45420:	68db      	ldr	r3, [r3, #12]
   45422:	ea4f 74e3 	mov.w	r4, r3, asr #31
   45426:	683a      	ldr	r2, [r7, #0]
   45428:	e9c2 3406 	strd	r3, r4, [r2, #24]
   4542c:	68fb      	ldr	r3, [r7, #12]
   4542e:	685b      	ldr	r3, [r3, #4]
   45430:	f04f 0400 	mov.w	r4, #0
   45434:	683a      	ldr	r2, [r7, #0]
   45436:	e9c2 3404 	strd	r3, r4, [r2, #16]
   4543a:	2300      	movs	r3, #0
   4543c:	4618      	mov	r0, r3
   4543e:	371c      	adds	r7, #28
   45440:	46bd      	mov	sp, r7
   45442:	bd90      	pop	{r4, r7, pc}

00045444 <teec_pre_process_partial>:
   45444:	b590      	push	{r4, r7, lr}
   45446:	b087      	sub	sp, #28
   45448:	af00      	add	r7, sp, #0
   4544a:	60f8      	str	r0, [r7, #12]
   4544c:	60b9      	str	r1, [r7, #8]
   4544e:	607a      	str	r2, [r7, #4]
   45450:	68fb      	ldr	r3, [r7, #12]
   45452:	2b0e      	cmp	r3, #14
   45454:	d00d      	beq.n	45472 <teec_pre_process_partial+0x2e>
   45456:	2b0f      	cmp	r3, #15
   45458:	d015      	beq.n	45486 <teec_pre_process_partial+0x42>
   4545a:	2b0d      	cmp	r3, #13
   4545c:	d11d      	bne.n	4549a <teec_pre_process_partial+0x56>
   4545e:	2301      	movs	r3, #1
   45460:	617b      	str	r3, [r7, #20]
   45462:	687a      	ldr	r2, [r7, #4]
   45464:	f04f 0305 	mov.w	r3, #5
   45468:	f04f 0400 	mov.w	r4, #0
   4546c:	e9c2 3400 	strd	r3, r4, [r2]
   45470:	e017      	b.n	454a2 <teec_pre_process_partial+0x5e>
   45472:	2302      	movs	r3, #2
   45474:	617b      	str	r3, [r7, #20]
   45476:	687a      	ldr	r2, [r7, #4]
   45478:	f04f 0306 	mov.w	r3, #6
   4547c:	f04f 0400 	mov.w	r4, #0
   45480:	e9c2 3400 	strd	r3, r4, [r2]
   45484:	e00d      	b.n	454a2 <teec_pre_process_partial+0x5e>
   45486:	2303      	movs	r3, #3
   45488:	617b      	str	r3, [r7, #20]
   4548a:	687a      	ldr	r2, [r7, #4]
   4548c:	f04f 0307 	mov.w	r3, #7
   45490:	f04f 0400 	mov.w	r4, #0
   45494:	e9c2 3400 	strd	r3, r4, [r2]
   45498:	e003      	b.n	454a2 <teec_pre_process_partial+0x5e>
   4549a:	2306      	movs	r3, #6
   4549c:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   454a0:	e039      	b.n	45516 <teec_pre_process_partial+0xd2>
   454a2:	68bb      	ldr	r3, [r7, #8]
   454a4:	681b      	ldr	r3, [r3, #0]
   454a6:	613b      	str	r3, [r7, #16]
   454a8:	693b      	ldr	r3, [r7, #16]
   454aa:	689a      	ldr	r2, [r3, #8]
   454ac:	697b      	ldr	r3, [r7, #20]
   454ae:	401a      	ands	r2, r3
   454b0:	697b      	ldr	r3, [r7, #20]
   454b2:	429a      	cmp	r2, r3
   454b4:	d003      	beq.n	454be <teec_pre_process_partial+0x7a>
   454b6:	2306      	movs	r3, #6
   454b8:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   454bc:	e02b      	b.n	45516 <teec_pre_process_partial+0xd2>
   454be:	693b      	ldr	r3, [r7, #16]
   454c0:	695b      	ldr	r3, [r3, #20]
   454c2:	2b00      	cmp	r3, #0
   454c4:	d011      	beq.n	454ea <teec_pre_process_partial+0xa6>
   454c6:	68fb      	ldr	r3, [r7, #12]
   454c8:	2b0e      	cmp	r3, #14
   454ca:	d00e      	beq.n	454ea <teec_pre_process_partial+0xa6>
   454cc:	693b      	ldr	r3, [r7, #16]
   454ce:	695a      	ldr	r2, [r3, #20]
   454d0:	68bb      	ldr	r3, [r7, #8]
   454d2:	689b      	ldr	r3, [r3, #8]
   454d4:	18d0      	adds	r0, r2, r3
   454d6:	693b      	ldr	r3, [r7, #16]
   454d8:	681a      	ldr	r2, [r3, #0]
   454da:	68bb      	ldr	r3, [r7, #8]
   454dc:	689b      	ldr	r3, [r3, #8]
   454de:	18d1      	adds	r1, r2, r3
   454e0:	68bb      	ldr	r3, [r7, #8]
   454e2:	685b      	ldr	r3, [r3, #4]
   454e4:	461a      	mov	r2, r3
   454e6:	f7cb ea48 	blx	10978 <memcpy@plt>
   454ea:	693b      	ldr	r3, [r7, #16]
   454ec:	68db      	ldr	r3, [r3, #12]
   454ee:	ea4f 74e3 	mov.w	r4, r3, asr #31
   454f2:	687a      	ldr	r2, [r7, #4]
   454f4:	e9c2 3406 	strd	r3, r4, [r2, #24]
   454f8:	68bb      	ldr	r3, [r7, #8]
   454fa:	689b      	ldr	r3, [r3, #8]
   454fc:	f04f 0400 	mov.w	r4, #0
   45500:	687a      	ldr	r2, [r7, #4]
   45502:	e9c2 3402 	strd	r3, r4, [r2, #8]
   45506:	68bb      	ldr	r3, [r7, #8]
   45508:	685b      	ldr	r3, [r3, #4]
   4550a:	f04f 0400 	mov.w	r4, #0
   4550e:	687a      	ldr	r2, [r7, #4]
   45510:	e9c2 3404 	strd	r3, r4, [r2, #16]
   45514:	2300      	movs	r3, #0
   45516:	4618      	mov	r0, r3
   45518:	371c      	adds	r7, #28
   4551a:	46bd      	mov	sp, r7
   4551c:	bd90      	pop	{r4, r7, pc}

0004551e <teec_pre_process_operation>:
   4551e:	b590      	push	{r4, r7, lr}
   45520:	b08b      	sub	sp, #44	; 0x2c
   45522:	af02      	add	r7, sp, #8
   45524:	60f8      	str	r0, [r7, #12]
   45526:	60b9      	str	r1, [r7, #8]
   45528:	607a      	str	r2, [r7, #4]
   4552a:	603b      	str	r3, [r7, #0]
   4552c:	2280      	movs	r2, #128	; 0x80
   4552e:	2100      	movs	r1, #0
   45530:	6838      	ldr	r0, [r7, #0]
   45532:	f7cb ea76 	blx	10a20 <memset@plt>
   45536:	68bb      	ldr	r3, [r7, #8]
   45538:	2b00      	cmp	r3, #0
   4553a:	d106      	bne.n	4554a <teec_pre_process_operation+0x2c>
   4553c:	2280      	movs	r2, #128	; 0x80
   4553e:	2100      	movs	r1, #0
   45540:	6878      	ldr	r0, [r7, #4]
   45542:	f7cb ea6e 	blx	10a20 <memset@plt>
   45546:	2300      	movs	r3, #0
   45548:	e0c3      	b.n	456d2 <teec_pre_process_operation+0x1b4>
   4554a:	2300      	movs	r3, #0
   4554c:	61fb      	str	r3, [r7, #28]
   4554e:	e0bb      	b.n	456c8 <teec_pre_process_operation+0x1aa>
   45550:	68bb      	ldr	r3, [r7, #8]
   45552:	685a      	ldr	r2, [r3, #4]
   45554:	69fb      	ldr	r3, [r7, #28]
   45556:	009b      	lsls	r3, r3, #2
   45558:	fa22 f303 	lsr.w	r3, r2, r3
   4555c:	f003 030f 	and.w	r3, r3, #15
   45560:	61bb      	str	r3, [r7, #24]
   45562:	69bb      	ldr	r3, [r7, #24]
   45564:	2b0f      	cmp	r3, #15
   45566:	f200 80a3 	bhi.w	456b0 <teec_pre_process_operation+0x192>
   4556a:	a202      	add	r2, pc, #8	; (adr r2, 45574 <teec_pre_process_operation+0x56>)
   4556c:	f852 3023 	ldr.w	r3, [r2, r3, lsl #2]
   45570:	441a      	add	r2, r3
   45572:	4710      	bx	r2
   45574:	00000041 	andeq	r0, r0, r1, asr #32
   45578:	00000055 	andeq	r0, r0, r5, asr r0
   4557c:	00000055 	andeq	r0, r0, r5, asr r0
   45580:	00000055 	andeq	r0, r0, r5, asr r0
   45584:	0000013d 	andeq	r0, r0, sp, lsr r1
   45588:	000000ad 	andeq	r0, r0, sp, lsr #1
   4558c:	000000ad 	andeq	r0, r0, sp, lsr #1
   45590:	000000ad 	andeq	r0, r0, sp, lsr #1
   45594:	0000013d 	andeq	r0, r0, sp, lsr r1
   45598:	0000013d 	andeq	r0, r0, sp, lsr r1
   4559c:	0000013d 	andeq	r0, r0, sp, lsr r1
   455a0:	0000013d 	andeq	r0, r0, sp, lsr r1
   455a4:	000000e7 	andeq	r0, r0, r7, ror #1
   455a8:	00000111 	andeq	r0, r0, r1, lsl r1
   455ac:	00000111 	andeq	r0, r0, r1, lsl r1
   455b0:	00000111 	andeq	r0, r0, r1, lsl r1
   455b4:	69fb      	ldr	r3, [r7, #28]
   455b6:	015b      	lsls	r3, r3, #5
   455b8:	687a      	ldr	r2, [r7, #4]
   455ba:	441a      	add	r2, r3
   455bc:	69bb      	ldr	r3, [r7, #24]
   455be:	f04f 0400 	mov.w	r4, #0
   455c2:	e9c2 3400 	strd	r3, r4, [r2]
   455c6:	e07c      	b.n	456c2 <teec_pre_process_operation+0x1a4>
   455c8:	69fb      	ldr	r3, [r7, #28]
   455ca:	015b      	lsls	r3, r3, #5
   455cc:	687a      	ldr	r2, [r7, #4]
   455ce:	441a      	add	r2, r3
   455d0:	69bb      	ldr	r3, [r7, #24]
   455d2:	f04f 0400 	mov.w	r4, #0
   455d6:	e9c2 3400 	strd	r3, r4, [r2]
   455da:	69fb      	ldr	r3, [r7, #28]
   455dc:	015b      	lsls	r3, r3, #5
   455de:	687a      	ldr	r2, [r7, #4]
   455e0:	18d1      	adds	r1, r2, r3
   455e2:	68b8      	ldr	r0, [r7, #8]
   455e4:	69fa      	ldr	r2, [r7, #28]
   455e6:	4613      	mov	r3, r2
   455e8:	005b      	lsls	r3, r3, #1
   455ea:	4413      	add	r3, r2
   455ec:	009b      	lsls	r3, r3, #2
   455ee:	4403      	add	r3, r0
   455f0:	3308      	adds	r3, #8
   455f2:	681b      	ldr	r3, [r3, #0]
   455f4:	f04f 0400 	mov.w	r4, #0
   455f8:	e9c1 3402 	strd	r3, r4, [r1, #8]
   455fc:	69fb      	ldr	r3, [r7, #28]
   455fe:	015b      	lsls	r3, r3, #5
   45600:	687a      	ldr	r2, [r7, #4]
   45602:	18d1      	adds	r1, r2, r3
   45604:	68b8      	ldr	r0, [r7, #8]
   45606:	69fa      	ldr	r2, [r7, #28]
   45608:	4613      	mov	r3, r2
   4560a:	005b      	lsls	r3, r3, #1
   4560c:	4413      	add	r3, r2
   4560e:	009b      	lsls	r3, r3, #2
   45610:	4403      	add	r3, r0
   45612:	330c      	adds	r3, #12
   45614:	681b      	ldr	r3, [r3, #0]
   45616:	f04f 0400 	mov.w	r4, #0
   4561a:	e9c1 3404 	strd	r3, r4, [r1, #16]
   4561e:	e050      	b.n	456c2 <teec_pre_process_operation+0x1a4>
   45620:	69fa      	ldr	r2, [r7, #28]
   45622:	4613      	mov	r3, r2
   45624:	005b      	lsls	r3, r3, #1
   45626:	4413      	add	r3, r2
   45628:	009b      	lsls	r3, r3, #2
   4562a:	3308      	adds	r3, #8
   4562c:	68ba      	ldr	r2, [r7, #8]
   4562e:	18d1      	adds	r1, r2, r3
   45630:	69fb      	ldr	r3, [r7, #28]
   45632:	015b      	lsls	r3, r3, #5
   45634:	687a      	ldr	r2, [r7, #4]
   45636:	18d0      	adds	r0, r2, r3
   45638:	69fb      	ldr	r3, [r7, #28]
   4563a:	015b      	lsls	r3, r3, #5
   4563c:	683a      	ldr	r2, [r7, #0]
   4563e:	4413      	add	r3, r2
   45640:	9300      	str	r3, [sp, #0]
   45642:	4603      	mov	r3, r0
   45644:	460a      	mov	r2, r1
   45646:	69b9      	ldr	r1, [r7, #24]
   45648:	68f8      	ldr	r0, [r7, #12]
   4564a:	f7ff fe3f 	bl	452cc <teec_pre_process_tmpref>
   4564e:	6178      	str	r0, [r7, #20]
   45650:	697b      	ldr	r3, [r7, #20]
   45652:	2b00      	cmp	r3, #0
   45654:	d030      	beq.n	456b8 <teec_pre_process_operation+0x19a>
   45656:	697b      	ldr	r3, [r7, #20]
   45658:	e03b      	b.n	456d2 <teec_pre_process_operation+0x1b4>
   4565a:	69fa      	ldr	r2, [r7, #28]
   4565c:	4613      	mov	r3, r2
   4565e:	005b      	lsls	r3, r3, #1
   45660:	4413      	add	r3, r2
   45662:	009b      	lsls	r3, r3, #2
   45664:	3308      	adds	r3, #8
   45666:	68ba      	ldr	r2, [r7, #8]
   45668:	18d0      	adds	r0, r2, r3
   4566a:	69fb      	ldr	r3, [r7, #28]
   4566c:	015b      	lsls	r3, r3, #5
   4566e:	687a      	ldr	r2, [r7, #4]
   45670:	4413      	add	r3, r2
   45672:	4619      	mov	r1, r3
   45674:	f7ff fe87 	bl	45386 <teec_pre_process_whole>
   45678:	6178      	str	r0, [r7, #20]
   4567a:	697b      	ldr	r3, [r7, #20]
   4567c:	2b00      	cmp	r3, #0
   4567e:	d01d      	beq.n	456bc <teec_pre_process_operation+0x19e>
   45680:	697b      	ldr	r3, [r7, #20]
   45682:	e026      	b.n	456d2 <teec_pre_process_operation+0x1b4>
   45684:	69fa      	ldr	r2, [r7, #28]
   45686:	4613      	mov	r3, r2
   45688:	005b      	lsls	r3, r3, #1
   4568a:	4413      	add	r3, r2
   4568c:	009b      	lsls	r3, r3, #2
   4568e:	3308      	adds	r3, #8
   45690:	68ba      	ldr	r2, [r7, #8]
   45692:	18d1      	adds	r1, r2, r3
   45694:	69fb      	ldr	r3, [r7, #28]
   45696:	015b      	lsls	r3, r3, #5
   45698:	687a      	ldr	r2, [r7, #4]
   4569a:	4413      	add	r3, r2
   4569c:	461a      	mov	r2, r3
   4569e:	69b8      	ldr	r0, [r7, #24]
   456a0:	f7ff fed0 	bl	45444 <teec_pre_process_partial>
   456a4:	6178      	str	r0, [r7, #20]
   456a6:	697b      	ldr	r3, [r7, #20]
   456a8:	2b00      	cmp	r3, #0
   456aa:	d009      	beq.n	456c0 <teec_pre_process_operation+0x1a2>
   456ac:	697b      	ldr	r3, [r7, #20]
   456ae:	e010      	b.n	456d2 <teec_pre_process_operation+0x1b4>
   456b0:	2306      	movs	r3, #6
   456b2:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   456b6:	e00c      	b.n	456d2 <teec_pre_process_operation+0x1b4>
   456b8:	bf00      	nop
   456ba:	e002      	b.n	456c2 <teec_pre_process_operation+0x1a4>
   456bc:	bf00      	nop
   456be:	e000      	b.n	456c2 <teec_pre_process_operation+0x1a4>
   456c0:	bf00      	nop
   456c2:	69fb      	ldr	r3, [r7, #28]
   456c4:	3301      	adds	r3, #1
   456c6:	61fb      	str	r3, [r7, #28]
   456c8:	69fb      	ldr	r3, [r7, #28]
   456ca:	2b03      	cmp	r3, #3
   456cc:	f67f af40 	bls.w	45550 <teec_pre_process_operation+0x32>
   456d0:	2300      	movs	r3, #0
   456d2:	4618      	mov	r0, r3
   456d4:	3724      	adds	r7, #36	; 0x24
   456d6:	46bd      	mov	sp, r7
   456d8:	bd90      	pop	{r4, r7, pc}

000456da <teec_post_process_tmpref>:
   456da:	b590      	push	{r4, r7, lr}
   456dc:	b085      	sub	sp, #20
   456de:	af00      	add	r7, sp, #0
   456e0:	60f8      	str	r0, [r7, #12]
   456e2:	60b9      	str	r1, [r7, #8]
   456e4:	607a      	str	r2, [r7, #4]
   456e6:	603b      	str	r3, [r7, #0]
   456e8:	68fb      	ldr	r3, [r7, #12]
   456ea:	2b05      	cmp	r3, #5
   456ec:	d01f      	beq.n	4572e <teec_post_process_tmpref+0x54>
   456ee:	687b      	ldr	r3, [r7, #4]
   456f0:	e9d3 3404 	ldrd	r3, r4, [r3, #16]
   456f4:	68ba      	ldr	r2, [r7, #8]
   456f6:	6852      	ldr	r2, [r2, #4]
   456f8:	4611      	mov	r1, r2
   456fa:	f04f 0200 	mov.w	r2, #0
   456fe:	42a2      	cmp	r2, r4
   45700:	bf08      	it	eq
   45702:	4299      	cmpeq	r1, r3
   45704:	d30d      	bcc.n	45722 <teec_post_process_tmpref+0x48>
   45706:	68bb      	ldr	r3, [r7, #8]
   45708:	681b      	ldr	r3, [r3, #0]
   4570a:	2b00      	cmp	r3, #0
   4570c:	d009      	beq.n	45722 <teec_post_process_tmpref+0x48>
   4570e:	68bb      	ldr	r3, [r7, #8]
   45710:	6818      	ldr	r0, [r3, #0]
   45712:	683b      	ldr	r3, [r7, #0]
   45714:	6819      	ldr	r1, [r3, #0]
   45716:	687b      	ldr	r3, [r7, #4]
   45718:	e9d3 3404 	ldrd	r3, r4, [r3, #16]
   4571c:	461a      	mov	r2, r3
   4571e:	f7cb e92c 	blx	10978 <memcpy@plt>
   45722:	687b      	ldr	r3, [r7, #4]
   45724:	e9d3 3404 	ldrd	r3, r4, [r3, #16]
   45728:	461a      	mov	r2, r3
   4572a:	68bb      	ldr	r3, [r7, #8]
   4572c:	605a      	str	r2, [r3, #4]
   4572e:	bf00      	nop
   45730:	3714      	adds	r7, #20
   45732:	46bd      	mov	sp, r7
   45734:	bd90      	pop	{r4, r7, pc}

00045736 <teec_post_process_whole>:
   45736:	b590      	push	{r4, r7, lr}
   45738:	b085      	sub	sp, #20
   4573a:	af00      	add	r7, sp, #0
   4573c:	6078      	str	r0, [r7, #4]
   4573e:	6039      	str	r1, [r7, #0]
   45740:	687b      	ldr	r3, [r7, #4]
   45742:	681b      	ldr	r3, [r3, #0]
   45744:	60fb      	str	r3, [r7, #12]
   45746:	68fb      	ldr	r3, [r7, #12]
   45748:	689b      	ldr	r3, [r3, #8]
   4574a:	f003 0302 	and.w	r3, r3, #2
   4574e:	2b00      	cmp	r3, #0
   45750:	d01f      	beq.n	45792 <teec_post_process_whole+0x5c>
   45752:	68fb      	ldr	r3, [r7, #12]
   45754:	695b      	ldr	r3, [r3, #20]
   45756:	2b00      	cmp	r3, #0
   45758:	d015      	beq.n	45786 <teec_post_process_whole+0x50>
   4575a:	683b      	ldr	r3, [r7, #0]
   4575c:	e9d3 3404 	ldrd	r3, r4, [r3, #16]
   45760:	68fa      	ldr	r2, [r7, #12]
   45762:	6852      	ldr	r2, [r2, #4]
   45764:	4611      	mov	r1, r2
   45766:	f04f 0200 	mov.w	r2, #0
   4576a:	42a2      	cmp	r2, r4
   4576c:	bf08      	it	eq
   4576e:	4299      	cmpeq	r1, r3
   45770:	d309      	bcc.n	45786 <teec_post_process_whole+0x50>
   45772:	68fb      	ldr	r3, [r7, #12]
   45774:	6818      	ldr	r0, [r3, #0]
   45776:	68fb      	ldr	r3, [r7, #12]
   45778:	6959      	ldr	r1, [r3, #20]
   4577a:	683b      	ldr	r3, [r7, #0]
   4577c:	e9d3 3404 	ldrd	r3, r4, [r3, #16]
   45780:	461a      	mov	r2, r3
   45782:	f7cb e8fa 	blx	10978 <memcpy@plt>
   45786:	683b      	ldr	r3, [r7, #0]
   45788:	e9d3 3404 	ldrd	r3, r4, [r3, #16]
   4578c:	461a      	mov	r2, r3
   4578e:	687b      	ldr	r3, [r7, #4]
   45790:	605a      	str	r2, [r3, #4]
   45792:	bf00      	nop
   45794:	3714      	adds	r7, #20
   45796:	46bd      	mov	sp, r7
   45798:	bd90      	pop	{r4, r7, pc}

0004579a <teec_post_process_partial>:
   4579a:	b590      	push	{r4, r7, lr}
   4579c:	b087      	sub	sp, #28
   4579e:	af00      	add	r7, sp, #0
   457a0:	60f8      	str	r0, [r7, #12]
   457a2:	60b9      	str	r1, [r7, #8]
   457a4:	607a      	str	r2, [r7, #4]
   457a6:	68fb      	ldr	r3, [r7, #12]
   457a8:	2b0d      	cmp	r3, #13
   457aa:	d028      	beq.n	457fe <teec_post_process_partial+0x64>
   457ac:	68bb      	ldr	r3, [r7, #8]
   457ae:	681b      	ldr	r3, [r3, #0]
   457b0:	617b      	str	r3, [r7, #20]
   457b2:	697b      	ldr	r3, [r7, #20]
   457b4:	695b      	ldr	r3, [r3, #20]
   457b6:	2b00      	cmp	r3, #0
   457b8:	d01b      	beq.n	457f2 <teec_post_process_partial+0x58>
   457ba:	687b      	ldr	r3, [r7, #4]
   457bc:	e9d3 3404 	ldrd	r3, r4, [r3, #16]
   457c0:	68ba      	ldr	r2, [r7, #8]
   457c2:	6852      	ldr	r2, [r2, #4]
   457c4:	4611      	mov	r1, r2
   457c6:	f04f 0200 	mov.w	r2, #0
   457ca:	42a2      	cmp	r2, r4
   457cc:	bf08      	it	eq
   457ce:	4299      	cmpeq	r1, r3
   457d0:	d30f      	bcc.n	457f2 <teec_post_process_partial+0x58>
   457d2:	697b      	ldr	r3, [r7, #20]
   457d4:	681a      	ldr	r2, [r3, #0]
   457d6:	68bb      	ldr	r3, [r7, #8]
   457d8:	689b      	ldr	r3, [r3, #8]
   457da:	18d0      	adds	r0, r2, r3
   457dc:	697b      	ldr	r3, [r7, #20]
   457de:	695a      	ldr	r2, [r3, #20]
   457e0:	68bb      	ldr	r3, [r7, #8]
   457e2:	689b      	ldr	r3, [r3, #8]
   457e4:	18d1      	adds	r1, r2, r3
   457e6:	687b      	ldr	r3, [r7, #4]
   457e8:	e9d3 3404 	ldrd	r3, r4, [r3, #16]
   457ec:	461a      	mov	r2, r3
   457ee:	f7cb e8c4 	blx	10978 <memcpy@plt>
   457f2:	687b      	ldr	r3, [r7, #4]
   457f4:	e9d3 3404 	ldrd	r3, r4, [r3, #16]
   457f8:	461a      	mov	r2, r3
   457fa:	68bb      	ldr	r3, [r7, #8]
   457fc:	605a      	str	r2, [r3, #4]
   457fe:	bf00      	nop
   45800:	371c      	adds	r7, #28
   45802:	46bd      	mov	sp, r7
   45804:	bd90      	pop	{r4, r7, pc}

00045806 <teec_post_process_operation>:
   45806:	b590      	push	{r4, r7, lr}
   45808:	b087      	sub	sp, #28
   4580a:	af00      	add	r7, sp, #0
   4580c:	60f8      	str	r0, [r7, #12]
   4580e:	60b9      	str	r1, [r7, #8]
   45810:	607a      	str	r2, [r7, #4]
   45812:	68fb      	ldr	r3, [r7, #12]
   45814:	2b00      	cmp	r3, #0
   45816:	f000 8092 	beq.w	4593e <teec_post_process_operation+0x138>
   4581a:	2300      	movs	r3, #0
   4581c:	617b      	str	r3, [r7, #20]
   4581e:	e089      	b.n	45934 <teec_post_process_operation+0x12e>
   45820:	68fb      	ldr	r3, [r7, #12]
   45822:	685a      	ldr	r2, [r3, #4]
   45824:	697b      	ldr	r3, [r7, #20]
   45826:	009b      	lsls	r3, r3, #2
   45828:	fa22 f303 	lsr.w	r3, r2, r3
   4582c:	f003 030f 	and.w	r3, r3, #15
   45830:	613b      	str	r3, [r7, #16]
   45832:	693b      	ldr	r3, [r7, #16]
   45834:	3b01      	subs	r3, #1
   45836:	2b0e      	cmp	r3, #14
   45838:	d878      	bhi.n	4592c <teec_post_process_operation+0x126>
   4583a:	a202      	add	r2, pc, #8	; (adr r2, 45844 <teec_post_process_operation+0x3e>)
   4583c:	f852 3023 	ldr.w	r3, [r2, r3, lsl #2]
   45840:	441a      	add	r2, r3
   45842:	4710      	bx	r2
   45844:	000000e9 	andeq	r0, r0, r9, ror #1
   45848:	0000003d 	andeq	r0, r0, sp, lsr r0
   4584c:	0000003d 	andeq	r0, r0, sp, lsr r0
   45850:	000000e9 	andeq	r0, r0, r9, ror #1
   45854:	0000007f 	andeq	r0, r0, pc, ror r0
   45858:	0000007f 	andeq	r0, r0, pc, ror r0
   4585c:	0000007f 	andeq	r0, r0, pc, ror r0
   45860:	000000e9 	andeq	r0, r0, r9, ror #1
   45864:	000000e9 	andeq	r0, r0, r9, ror #1
   45868:	000000e9 	andeq	r0, r0, r9, ror #1
   4586c:	000000e9 	andeq	r0, r0, r9, ror #1
   45870:	000000a9 	andeq	r0, r0, r9, lsr #1
   45874:	000000c9 	andeq	r0, r0, r9, asr #1
   45878:	000000c9 	andeq	r0, r0, r9, asr #1
   4587c:	000000c9 	andeq	r0, r0, r9, asr #1
   45880:	697b      	ldr	r3, [r7, #20]
   45882:	015b      	lsls	r3, r3, #5
   45884:	68ba      	ldr	r2, [r7, #8]
   45886:	4413      	add	r3, r2
   45888:	e9d3 3402 	ldrd	r3, r4, [r3, #8]
   4588c:	4618      	mov	r0, r3
   4588e:	68f9      	ldr	r1, [r7, #12]
   45890:	697a      	ldr	r2, [r7, #20]
   45892:	4613      	mov	r3, r2
   45894:	005b      	lsls	r3, r3, #1
   45896:	4413      	add	r3, r2
   45898:	009b      	lsls	r3, r3, #2
   4589a:	440b      	add	r3, r1
   4589c:	3308      	adds	r3, #8
   4589e:	6018      	str	r0, [r3, #0]
   458a0:	697b      	ldr	r3, [r7, #20]
   458a2:	015b      	lsls	r3, r3, #5
   458a4:	68ba      	ldr	r2, [r7, #8]
   458a6:	4413      	add	r3, r2
   458a8:	e9d3 3404 	ldrd	r3, r4, [r3, #16]
   458ac:	4618      	mov	r0, r3
   458ae:	68f9      	ldr	r1, [r7, #12]
   458b0:	697a      	ldr	r2, [r7, #20]
   458b2:	4613      	mov	r3, r2
   458b4:	005b      	lsls	r3, r3, #1
   458b6:	4413      	add	r3, r2
   458b8:	009b      	lsls	r3, r3, #2
   458ba:	440b      	add	r3, r1
   458bc:	330c      	adds	r3, #12
   458be:	6018      	str	r0, [r3, #0]
   458c0:	e035      	b.n	4592e <teec_post_process_operation+0x128>
   458c2:	697a      	ldr	r2, [r7, #20]
   458c4:	4613      	mov	r3, r2
   458c6:	005b      	lsls	r3, r3, #1
   458c8:	4413      	add	r3, r2
   458ca:	009b      	lsls	r3, r3, #2
   458cc:	3308      	adds	r3, #8
   458ce:	68fa      	ldr	r2, [r7, #12]
   458d0:	18d1      	adds	r1, r2, r3
   458d2:	697b      	ldr	r3, [r7, #20]
   458d4:	015b      	lsls	r3, r3, #5
   458d6:	68ba      	ldr	r2, [r7, #8]
   458d8:	18d0      	adds	r0, r2, r3
   458da:	697b      	ldr	r3, [r7, #20]
   458dc:	015b      	lsls	r3, r3, #5
   458de:	687a      	ldr	r2, [r7, #4]
   458e0:	4413      	add	r3, r2
   458e2:	4602      	mov	r2, r0
   458e4:	6938      	ldr	r0, [r7, #16]
   458e6:	f7ff fef8 	bl	456da <teec_post_process_tmpref>
   458ea:	e020      	b.n	4592e <teec_post_process_operation+0x128>
   458ec:	697a      	ldr	r2, [r7, #20]
   458ee:	4613      	mov	r3, r2
   458f0:	005b      	lsls	r3, r3, #1
   458f2:	4413      	add	r3, r2
   458f4:	009b      	lsls	r3, r3, #2
   458f6:	3308      	adds	r3, #8
   458f8:	68fa      	ldr	r2, [r7, #12]
   458fa:	18d0      	adds	r0, r2, r3
   458fc:	697b      	ldr	r3, [r7, #20]
   458fe:	015b      	lsls	r3, r3, #5
   45900:	68ba      	ldr	r2, [r7, #8]
   45902:	4413      	add	r3, r2
   45904:	4619      	mov	r1, r3
   45906:	f7ff ff16 	bl	45736 <teec_post_process_whole>
   4590a:	e010      	b.n	4592e <teec_post_process_operation+0x128>
   4590c:	697a      	ldr	r2, [r7, #20]
   4590e:	4613      	mov	r3, r2
   45910:	005b      	lsls	r3, r3, #1
   45912:	4413      	add	r3, r2
   45914:	009b      	lsls	r3, r3, #2
   45916:	3308      	adds	r3, #8
   45918:	68fa      	ldr	r2, [r7, #12]
   4591a:	18d1      	adds	r1, r2, r3
   4591c:	697b      	ldr	r3, [r7, #20]
   4591e:	015b      	lsls	r3, r3, #5
   45920:	68ba      	ldr	r2, [r7, #8]
   45922:	4413      	add	r3, r2
   45924:	461a      	mov	r2, r3
   45926:	6938      	ldr	r0, [r7, #16]
   45928:	f7ff ff37 	bl	4579a <teec_post_process_partial>
   4592c:	bf00      	nop
   4592e:	697b      	ldr	r3, [r7, #20]
   45930:	3301      	adds	r3, #1
   45932:	617b      	str	r3, [r7, #20]
   45934:	697b      	ldr	r3, [r7, #20]
   45936:	2b03      	cmp	r3, #3
   45938:	f67f af72 	bls.w	45820 <teec_post_process_operation+0x1a>
   4593c:	e000      	b.n	45940 <teec_post_process_operation+0x13a>
   4593e:	bf00      	nop
   45940:	371c      	adds	r7, #28
   45942:	46bd      	mov	sp, r7
   45944:	bd90      	pop	{r4, r7, pc}

00045946 <teec_free_temp_refs>:
   45946:	b580      	push	{r7, lr}
   45948:	b084      	sub	sp, #16
   4594a:	af00      	add	r7, sp, #0
   4594c:	6078      	str	r0, [r7, #4]
   4594e:	6039      	str	r1, [r7, #0]
   45950:	687b      	ldr	r3, [r7, #4]
   45952:	2b00      	cmp	r3, #0
   45954:	d01d      	beq.n	45992 <teec_free_temp_refs+0x4c>
   45956:	2300      	movs	r3, #0
   45958:	60fb      	str	r3, [r7, #12]
   4595a:	e016      	b.n	4598a <teec_free_temp_refs+0x44>
   4595c:	687b      	ldr	r3, [r7, #4]
   4595e:	685a      	ldr	r2, [r3, #4]
   45960:	68fb      	ldr	r3, [r7, #12]
   45962:	009b      	lsls	r3, r3, #2
   45964:	fa22 f303 	lsr.w	r3, r2, r3
   45968:	f003 030f 	and.w	r3, r3, #15
   4596c:	3b05      	subs	r3, #5
   4596e:	2b02      	cmp	r3, #2
   45970:	d807      	bhi.n	45982 <teec_free_temp_refs+0x3c>
   45972:	68fb      	ldr	r3, [r7, #12]
   45974:	015b      	lsls	r3, r3, #5
   45976:	683a      	ldr	r2, [r7, #0]
   45978:	4413      	add	r3, r2
   4597a:	4618      	mov	r0, r3
   4597c:	f000 fbfb 	bl	46176 <TEEC_ReleaseSharedMemory>
   45980:	e000      	b.n	45984 <teec_free_temp_refs+0x3e>
   45982:	bf00      	nop
   45984:	68fb      	ldr	r3, [r7, #12]
   45986:	3301      	adds	r3, #1
   45988:	60fb      	str	r3, [r7, #12]
   4598a:	68fb      	ldr	r3, [r7, #12]
   4598c:	2b03      	cmp	r3, #3
   4598e:	d9e5      	bls.n	4595c <teec_free_temp_refs+0x16>
   45990:	e000      	b.n	45994 <teec_free_temp_refs+0x4e>
   45992:	bf00      	nop
   45994:	3710      	adds	r7, #16
   45996:	46bd      	mov	sp, r7
   45998:	bd80      	pop	{r7, pc}

0004599a <ioctl_errno_to_res>:
   4599a:	b480      	push	{r7}
   4599c:	b083      	sub	sp, #12
   4599e:	af00      	add	r7, sp, #0
   459a0:	6078      	str	r0, [r7, #4]
   459a2:	687b      	ldr	r3, [r7, #4]
   459a4:	2b0c      	cmp	r3, #12
   459a6:	d103      	bne.n	459b0 <ioctl_errno_to_res+0x16>
   459a8:	230c      	movs	r3, #12
   459aa:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   459ae:	e002      	b.n	459b6 <ioctl_errno_to_res+0x1c>
   459b0:	2300      	movs	r3, #0
   459b2:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   459b6:	4618      	mov	r0, r3
   459b8:	370c      	adds	r7, #12
   459ba:	46bd      	mov	sp, r7
   459bc:	f85d 7b04 	ldr.w	r7, [sp], #4
   459c0:	4770      	bx	lr

000459c2 <uuid_to_octets>:
   459c2:	b580      	push	{r7, lr}
   459c4:	b082      	sub	sp, #8
   459c6:	af00      	add	r7, sp, #0
   459c8:	6078      	str	r0, [r7, #4]
   459ca:	6039      	str	r1, [r7, #0]
   459cc:	683b      	ldr	r3, [r7, #0]
   459ce:	681b      	ldr	r3, [r3, #0]
   459d0:	0e1b      	lsrs	r3, r3, #24
   459d2:	b2da      	uxtb	r2, r3
   459d4:	687b      	ldr	r3, [r7, #4]
   459d6:	701a      	strb	r2, [r3, #0]
   459d8:	687b      	ldr	r3, [r7, #4]
   459da:	3301      	adds	r3, #1
   459dc:	683a      	ldr	r2, [r7, #0]
   459de:	6812      	ldr	r2, [r2, #0]
   459e0:	0c12      	lsrs	r2, r2, #16
   459e2:	b2d2      	uxtb	r2, r2
   459e4:	701a      	strb	r2, [r3, #0]
   459e6:	687b      	ldr	r3, [r7, #4]
   459e8:	3302      	adds	r3, #2
   459ea:	683a      	ldr	r2, [r7, #0]
   459ec:	6812      	ldr	r2, [r2, #0]
   459ee:	0a12      	lsrs	r2, r2, #8
   459f0:	b2d2      	uxtb	r2, r2
   459f2:	701a      	strb	r2, [r3, #0]
   459f4:	687b      	ldr	r3, [r7, #4]
   459f6:	3303      	adds	r3, #3
   459f8:	683a      	ldr	r2, [r7, #0]
   459fa:	6812      	ldr	r2, [r2, #0]
   459fc:	b2d2      	uxtb	r2, r2
   459fe:	701a      	strb	r2, [r3, #0]
   45a00:	687b      	ldr	r3, [r7, #4]
   45a02:	3304      	adds	r3, #4
   45a04:	683a      	ldr	r2, [r7, #0]
   45a06:	8892      	ldrh	r2, [r2, #4]
   45a08:	0a12      	lsrs	r2, r2, #8
   45a0a:	b292      	uxth	r2, r2
   45a0c:	b2d2      	uxtb	r2, r2
   45a0e:	701a      	strb	r2, [r3, #0]
   45a10:	687b      	ldr	r3, [r7, #4]
   45a12:	3305      	adds	r3, #5
   45a14:	683a      	ldr	r2, [r7, #0]
   45a16:	8892      	ldrh	r2, [r2, #4]
   45a18:	b2d2      	uxtb	r2, r2
   45a1a:	701a      	strb	r2, [r3, #0]
   45a1c:	687b      	ldr	r3, [r7, #4]
   45a1e:	3306      	adds	r3, #6
   45a20:	683a      	ldr	r2, [r7, #0]
   45a22:	88d2      	ldrh	r2, [r2, #6]
   45a24:	0a12      	lsrs	r2, r2, #8
   45a26:	b292      	uxth	r2, r2
   45a28:	b2d2      	uxtb	r2, r2
   45a2a:	701a      	strb	r2, [r3, #0]
   45a2c:	687b      	ldr	r3, [r7, #4]
   45a2e:	3307      	adds	r3, #7
   45a30:	683a      	ldr	r2, [r7, #0]
   45a32:	88d2      	ldrh	r2, [r2, #6]
   45a34:	b2d2      	uxtb	r2, r2
   45a36:	701a      	strb	r2, [r3, #0]
   45a38:	687b      	ldr	r3, [r7, #4]
   45a3a:	f103 0008 	add.w	r0, r3, #8
   45a3e:	683b      	ldr	r3, [r7, #0]
   45a40:	3308      	adds	r3, #8
   45a42:	2208      	movs	r2, #8
   45a44:	4619      	mov	r1, r3
   45a46:	f7ca ef98 	blx	10978 <memcpy@plt>
   45a4a:	bf00      	nop
   45a4c:	3708      	adds	r7, #8
   45a4e:	46bd      	mov	sp, r7
   45a50:	bd80      	pop	{r7, pc}

00045a52 <TEEC_OpenSession>:
   45a52:	b590      	push	{r4, r7, lr}
   45a54:	b0df      	sub	sp, #380	; 0x17c
   45a56:	af02      	add	r7, sp, #8
   45a58:	f107 040c 	add.w	r4, r7, #12
   45a5c:	6020      	str	r0, [r4, #0]
   45a5e:	f107 0008 	add.w	r0, r7, #8
   45a62:	6001      	str	r1, [r0, #0]
   45a64:	1d39      	adds	r1, r7, #4
   45a66:	600a      	str	r2, [r1, #0]
   45a68:	463a      	mov	r2, r7
   45a6a:	6013      	str	r3, [r2, #0]
   45a6c:	f107 03a0 	add.w	r3, r7, #160	; 0xa0
   45a70:	22b8      	movs	r2, #184	; 0xb8
   45a72:	2100      	movs	r1, #0
   45a74:	4618      	mov	r0, r3
   45a76:	f7ca efd4 	blx	10a20 <memset@plt>
   45a7a:	f107 030c 	add.w	r3, r7, #12
   45a7e:	681b      	ldr	r3, [r3, #0]
   45a80:	2b00      	cmp	r3, #0
   45a82:	d004      	beq.n	45a8e <TEEC_OpenSession+0x3c>
   45a84:	f107 0308 	add.w	r3, r7, #8
   45a88:	681b      	ldr	r3, [r3, #0]
   45a8a:	2b00      	cmp	r3, #0
   45a8c:	d108      	bne.n	45aa0 <TEEC_OpenSession+0x4e>
   45a8e:	2301      	movs	r3, #1
   45a90:	f8c7 3168 	str.w	r3, [r7, #360]	; 0x168
   45a94:	2306      	movs	r3, #6
   45a96:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   45a9a:	f8c7 316c 	str.w	r3, [r7, #364]	; 0x16c
   45a9e:	e091      	b.n	45bc4 <TEEC_OpenSession+0x172>
   45aa0:	f107 03a0 	add.w	r3, r7, #160	; 0xa0
   45aa4:	f04f 0400 	mov.w	r4, #0
   45aa8:	e9c7 3424 	strd	r3, r4, [r7, #144]	; 0x90
   45aac:	f04f 03b8 	mov.w	r3, #184	; 0xb8
   45ab0:	f04f 0400 	mov.w	r4, #0
   45ab4:	e9c7 3426 	strd	r3, r4, [r7, #152]	; 0x98
   45ab8:	f107 03a0 	add.w	r3, r7, #160	; 0xa0
   45abc:	f8c7 3164 	str.w	r3, [r7, #356]	; 0x164
   45ac0:	f8d7 3164 	ldr.w	r3, [r7, #356]	; 0x164
   45ac4:	2204      	movs	r2, #4
   45ac6:	635a      	str	r2, [r3, #52]	; 0x34
   45ac8:	f8d7 3164 	ldr.w	r3, [r7, #356]	; 0x164
   45acc:	3338      	adds	r3, #56	; 0x38
   45ace:	f8c7 3160 	str.w	r3, [r7, #352]	; 0x160
   45ad2:	f8d7 2164 	ldr.w	r2, [r7, #356]	; 0x164
   45ad6:	1d3b      	adds	r3, r7, #4
   45ad8:	6819      	ldr	r1, [r3, #0]
   45ada:	4610      	mov	r0, r2
   45adc:	f7ff ff71 	bl	459c2 <uuid_to_octets>
   45ae0:	f8d7 3164 	ldr.w	r3, [r7, #356]	; 0x164
   45ae4:	463a      	mov	r2, r7
   45ae6:	6812      	ldr	r2, [r2, #0]
   45ae8:	621a      	str	r2, [r3, #32]
   45aea:	f107 0310 	add.w	r3, r7, #16
   45aee:	f107 000c 	add.w	r0, r7, #12
   45af2:	f8d7 2160 	ldr.w	r2, [r7, #352]	; 0x160
   45af6:	f8d7 1184 	ldr.w	r1, [r7, #388]	; 0x184
   45afa:	6800      	ldr	r0, [r0, #0]
   45afc:	f7ff fd0f 	bl	4551e <teec_pre_process_operation>
   45b00:	f8c7 016c 	str.w	r0, [r7, #364]	; 0x16c
   45b04:	f8d7 316c 	ldr.w	r3, [r7, #364]	; 0x16c
   45b08:	2b00      	cmp	r3, #0
   45b0a:	d003      	beq.n	45b14 <TEEC_OpenSession+0xc2>
   45b0c:	2301      	movs	r3, #1
   45b0e:	f8c7 3168 	str.w	r3, [r7, #360]	; 0x168
   45b12:	e050      	b.n	45bb6 <TEEC_OpenSession+0x164>
   45b14:	f107 030c 	add.w	r3, r7, #12
   45b18:	681b      	ldr	r3, [r3, #0]
   45b1a:	681b      	ldr	r3, [r3, #0]
   45b1c:	f107 0290 	add.w	r2, r7, #144	; 0x90
   45b20:	f24a 4102 	movw	r1, #41986	; 0xa402
   45b24:	f2c8 0110 	movt	r1, #32784	; 0x8010
   45b28:	4618      	mov	r0, r3
   45b2a:	f7ca ef32 	blx	10990 <ioctl@plt>
   45b2e:	f8c7 015c 	str.w	r0, [r7, #348]	; 0x15c
   45b32:	f8d7 315c 	ldr.w	r3, [r7, #348]	; 0x15c
   45b36:	2b00      	cmp	r3, #0
   45b38:	d018      	beq.n	45b6c <TEEC_OpenSession+0x11a>
   45b3a:	4b2a      	ldr	r3, [pc, #168]	; (45be4 <TEEC_OpenSession+0x192>)
   45b3c:	447b      	add	r3, pc
   45b3e:	9300      	str	r3, [sp, #0]
   45b40:	4b29      	ldr	r3, [pc, #164]	; (45be8 <TEEC_OpenSession+0x196>)
   45b42:	447b      	add	r3, pc
   45b44:	2201      	movs	r2, #1
   45b46:	f240 210a 	movw	r1, #522	; 0x20a
   45b4a:	4828      	ldr	r0, [pc, #160]	; (45bec <TEEC_OpenSession+0x19a>)
   45b4c:	4478      	add	r0, pc
   45b4e:	f000 fb6b 	bl	46228 <_dprintf>
   45b52:	2302      	movs	r3, #2
   45b54:	f8c7 3168 	str.w	r3, [r7, #360]	; 0x168
   45b58:	f7ca ef56 	blx	10a08 <__errno_location@plt>
   45b5c:	4603      	mov	r3, r0
   45b5e:	681b      	ldr	r3, [r3, #0]
   45b60:	4618      	mov	r0, r3
   45b62:	f7ff ff1a 	bl	4599a <ioctl_errno_to_res>
   45b66:	f8c7 016c 	str.w	r0, [r7, #364]	; 0x16c
   45b6a:	e024      	b.n	45bb6 <TEEC_OpenSession+0x164>
   45b6c:	f8d7 3164 	ldr.w	r3, [r7, #356]	; 0x164
   45b70:	6adb      	ldr	r3, [r3, #44]	; 0x2c
   45b72:	f8c7 316c 	str.w	r3, [r7, #364]	; 0x16c
   45b76:	f8d7 3164 	ldr.w	r3, [r7, #356]	; 0x164
   45b7a:	6b1b      	ldr	r3, [r3, #48]	; 0x30
   45b7c:	f8c7 3168 	str.w	r3, [r7, #360]	; 0x168
   45b80:	f8d7 316c 	ldr.w	r3, [r7, #364]	; 0x16c
   45b84:	2b00      	cmp	r3, #0
   45b86:	d10d      	bne.n	45ba4 <TEEC_OpenSession+0x152>
   45b88:	f107 0308 	add.w	r3, r7, #8
   45b8c:	681b      	ldr	r3, [r3, #0]
   45b8e:	f107 020c 	add.w	r2, r7, #12
   45b92:	6812      	ldr	r2, [r2, #0]
   45b94:	601a      	str	r2, [r3, #0]
   45b96:	f8d7 3164 	ldr.w	r3, [r7, #356]	; 0x164
   45b9a:	6a9a      	ldr	r2, [r3, #40]	; 0x28
   45b9c:	f107 0308 	add.w	r3, r7, #8
   45ba0:	681b      	ldr	r3, [r3, #0]
   45ba2:	605a      	str	r2, [r3, #4]
   45ba4:	f107 0310 	add.w	r3, r7, #16
   45ba8:	461a      	mov	r2, r3
   45baa:	f8d7 1160 	ldr.w	r1, [r7, #352]	; 0x160
   45bae:	f8d7 0184 	ldr.w	r0, [r7, #388]	; 0x184
   45bb2:	f7ff fe28 	bl	45806 <teec_post_process_operation>
   45bb6:	f107 0310 	add.w	r3, r7, #16
   45bba:	4619      	mov	r1, r3
   45bbc:	f8d7 0184 	ldr.w	r0, [r7, #388]	; 0x184
   45bc0:	f7ff fec1 	bl	45946 <teec_free_temp_refs>
   45bc4:	f8d7 3188 	ldr.w	r3, [r7, #392]	; 0x188
   45bc8:	2b00      	cmp	r3, #0
   45bca:	d004      	beq.n	45bd6 <TEEC_OpenSession+0x184>
   45bcc:	f8d7 3188 	ldr.w	r3, [r7, #392]	; 0x188
   45bd0:	f8d7 2168 	ldr.w	r2, [r7, #360]	; 0x168
   45bd4:	601a      	str	r2, [r3, #0]
   45bd6:	f8d7 316c 	ldr.w	r3, [r7, #364]	; 0x16c
   45bda:	4618      	mov	r0, r3
   45bdc:	f507 77ba 	add.w	r7, r7, #372	; 0x174
   45be0:	46bd      	mov	sp, r7
   45be2:	bd90      	pop	{r4, r7, pc}
   45be4:	00000f3c 	andeq	r0, r0, ip, lsr pc
   45be8:	00000efe 	strdeq	r0, [r0], -lr
   45bec:	00000fa8 	andeq	r0, r0, r8, lsr #31

00045bf0 <TEEC_CloseSession>:
   45bf0:	b580      	push	{r7, lr}
   45bf2:	b086      	sub	sp, #24
   45bf4:	af02      	add	r7, sp, #8
   45bf6:	6078      	str	r0, [r7, #4]
   45bf8:	687b      	ldr	r3, [r7, #4]
   45bfa:	2b00      	cmp	r3, #0
   45bfc:	d021      	beq.n	45c42 <TEEC_CloseSession+0x52>
   45bfe:	687b      	ldr	r3, [r7, #4]
   45c00:	685b      	ldr	r3, [r3, #4]
   45c02:	60fb      	str	r3, [r7, #12]
   45c04:	687b      	ldr	r3, [r7, #4]
   45c06:	681b      	ldr	r3, [r3, #0]
   45c08:	681b      	ldr	r3, [r3, #0]
   45c0a:	f107 020c 	add.w	r2, r7, #12
   45c0e:	f24a 4105 	movw	r1, #41989	; 0xa405
   45c12:	f2c8 0104 	movt	r1, #32772	; 0x8004
   45c16:	4618      	mov	r0, r3
   45c18:	f7ca eeba 	blx	10990 <ioctl@plt>
   45c1c:	4603      	mov	r3, r0
   45c1e:	2b00      	cmp	r3, #0
   45c20:	d010      	beq.n	45c44 <TEEC_CloseSession+0x54>
   45c22:	687b      	ldr	r3, [r7, #4]
   45c24:	685b      	ldr	r3, [r3, #4]
   45c26:	9301      	str	r3, [sp, #4]
   45c28:	4b08      	ldr	r3, [pc, #32]	; (45c4c <TEEC_CloseSession+0x5c>)
   45c2a:	447b      	add	r3, pc
   45c2c:	9300      	str	r3, [sp, #0]
   45c2e:	4b08      	ldr	r3, [pc, #32]	; (45c50 <TEEC_CloseSession+0x60>)
   45c30:	447b      	add	r3, pc
   45c32:	2201      	movs	r2, #1
   45c34:	f44f 710a 	mov.w	r1, #552	; 0x228
   45c38:	4806      	ldr	r0, [pc, #24]	; (45c54 <TEEC_CloseSession+0x64>)
   45c3a:	4478      	add	r0, pc
   45c3c:	f000 faf4 	bl	46228 <_dprintf>
   45c40:	e000      	b.n	45c44 <TEEC_CloseSession+0x54>
   45c42:	bf00      	nop
   45c44:	3710      	adds	r7, #16
   45c46:	46bd      	mov	sp, r7
   45c48:	bd80      	pop	{r7, pc}
   45c4a:	bf00      	nop
   45c4c:	00000e6e 	andeq	r0, r0, lr, ror #28
   45c50:	00000e10 	andeq	r0, r0, r0, lsl lr
   45c54:	00000ece 	andeq	r0, r0, lr, asr #29

00045c58 <TEEC_InvokeCommand>:
   45c58:	b590      	push	{r4, r7, lr}
   45c5a:	b0d7      	sub	sp, #348	; 0x15c
   45c5c:	af02      	add	r7, sp, #8
   45c5e:	f107 040c 	add.w	r4, r7, #12
   45c62:	6020      	str	r0, [r4, #0]
   45c64:	f107 0008 	add.w	r0, r7, #8
   45c68:	6001      	str	r1, [r0, #0]
   45c6a:	1d39      	adds	r1, r7, #4
   45c6c:	600a      	str	r2, [r1, #0]
   45c6e:	463a      	mov	r2, r7
   45c70:	6013      	str	r3, [r2, #0]
   45c72:	f107 03a0 	add.w	r3, r7, #160	; 0xa0
   45c76:	2298      	movs	r2, #152	; 0x98
   45c78:	2100      	movs	r1, #0
   45c7a:	4618      	mov	r0, r3
   45c7c:	f7ca eed0 	blx	10a20 <memset@plt>
   45c80:	f107 030c 	add.w	r3, r7, #12
   45c84:	681b      	ldr	r3, [r3, #0]
   45c86:	2b00      	cmp	r3, #0
   45c88:	d108      	bne.n	45c9c <TEEC_InvokeCommand+0x44>
   45c8a:	2301      	movs	r3, #1
   45c8c:	f8c7 3148 	str.w	r3, [r7, #328]	; 0x148
   45c90:	2306      	movs	r3, #6
   45c92:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   45c96:	f8c7 314c 	str.w	r3, [r7, #332]	; 0x14c
   45c9a:	e099      	b.n	45dd0 <TEEC_InvokeCommand+0x178>
   45c9c:	f7ff f9ae 	bl	44ffc <bm_timestamp>
   45ca0:	f107 03a0 	add.w	r3, r7, #160	; 0xa0
   45ca4:	f04f 0400 	mov.w	r4, #0
   45ca8:	e9c7 3424 	strd	r3, r4, [r7, #144]	; 0x90
   45cac:	f04f 0398 	mov.w	r3, #152	; 0x98
   45cb0:	f04f 0400 	mov.w	r4, #0
   45cb4:	e9c7 3426 	strd	r3, r4, [r7, #152]	; 0x98
   45cb8:	f107 03a0 	add.w	r3, r7, #160	; 0xa0
   45cbc:	f8c7 3144 	str.w	r3, [r7, #324]	; 0x144
   45cc0:	f8d7 3144 	ldr.w	r3, [r7, #324]	; 0x144
   45cc4:	2204      	movs	r2, #4
   45cc6:	615a      	str	r2, [r3, #20]
   45cc8:	f8d7 3144 	ldr.w	r3, [r7, #324]	; 0x144
   45ccc:	3318      	adds	r3, #24
   45cce:	f8c7 3140 	str.w	r3, [r7, #320]	; 0x140
   45cd2:	f107 030c 	add.w	r3, r7, #12
   45cd6:	681b      	ldr	r3, [r3, #0]
   45cd8:	685a      	ldr	r2, [r3, #4]
   45cda:	f8d7 3144 	ldr.w	r3, [r7, #324]	; 0x144
   45cde:	605a      	str	r2, [r3, #4]
   45ce0:	f8d7 3144 	ldr.w	r3, [r7, #324]	; 0x144
   45ce4:	f107 0208 	add.w	r2, r7, #8
   45ce8:	6812      	ldr	r2, [r2, #0]
   45cea:	601a      	str	r2, [r3, #0]
   45cec:	1d3b      	adds	r3, r7, #4
   45cee:	681b      	ldr	r3, [r3, #0]
   45cf0:	2b00      	cmp	r3, #0
   45cf2:	d00f      	beq.n	45d14 <TEEC_InvokeCommand+0xbc>
   45cf4:	4b3e      	ldr	r3, [pc, #248]	; (45df0 <TEEC_InvokeCommand+0x198>)
   45cf6:	447b      	add	r3, pc
   45cf8:	4618      	mov	r0, r3
   45cfa:	f7ff f986 	bl	4500a <teec_mutex_lock>
   45cfe:	1d3b      	adds	r3, r7, #4
   45d00:	681b      	ldr	r3, [r3, #0]
   45d02:	f107 020c 	add.w	r2, r7, #12
   45d06:	6812      	ldr	r2, [r2, #0]
   45d08:	639a      	str	r2, [r3, #56]	; 0x38
   45d0a:	4b3a      	ldr	r3, [pc, #232]	; (45df4 <TEEC_InvokeCommand+0x19c>)
   45d0c:	447b      	add	r3, pc
   45d0e:	4618      	mov	r0, r3
   45d10:	f7ff f986 	bl	45020 <teec_mutex_unlock>
   45d14:	f107 030c 	add.w	r3, r7, #12
   45d18:	681b      	ldr	r3, [r3, #0]
   45d1a:	6818      	ldr	r0, [r3, #0]
   45d1c:	f107 0310 	add.w	r3, r7, #16
   45d20:	1d39      	adds	r1, r7, #4
   45d22:	f8d7 2140 	ldr.w	r2, [r7, #320]	; 0x140
   45d26:	6809      	ldr	r1, [r1, #0]
   45d28:	f7ff fbf9 	bl	4551e <teec_pre_process_operation>
   45d2c:	f8c7 014c 	str.w	r0, [r7, #332]	; 0x14c
   45d30:	f8d7 314c 	ldr.w	r3, [r7, #332]	; 0x14c
   45d34:	2b00      	cmp	r3, #0
   45d36:	d003      	beq.n	45d40 <TEEC_InvokeCommand+0xe8>
   45d38:	2301      	movs	r3, #1
   45d3a:	f8c7 3148 	str.w	r3, [r7, #328]	; 0x148
   45d3e:	e040      	b.n	45dc2 <TEEC_InvokeCommand+0x16a>
   45d40:	f107 030c 	add.w	r3, r7, #12
   45d44:	681b      	ldr	r3, [r3, #0]
   45d46:	681b      	ldr	r3, [r3, #0]
   45d48:	681b      	ldr	r3, [r3, #0]
   45d4a:	f107 0290 	add.w	r2, r7, #144	; 0x90
   45d4e:	f24a 4103 	movw	r1, #41987	; 0xa403
   45d52:	f2c8 0110 	movt	r1, #32784	; 0x8010
   45d56:	4618      	mov	r0, r3
   45d58:	f7ca ee1a 	blx	10990 <ioctl@plt>
   45d5c:	f8c7 013c 	str.w	r0, [r7, #316]	; 0x13c
   45d60:	f8d7 313c 	ldr.w	r3, [r7, #316]	; 0x13c
   45d64:	2b00      	cmp	r3, #0
   45d66:	d018      	beq.n	45d9a <TEEC_InvokeCommand+0x142>
   45d68:	4b23      	ldr	r3, [pc, #140]	; (45df8 <TEEC_InvokeCommand+0x1a0>)
   45d6a:	447b      	add	r3, pc
   45d6c:	9300      	str	r3, [sp, #0]
   45d6e:	4b23      	ldr	r3, [pc, #140]	; (45dfc <TEEC_InvokeCommand+0x1a4>)
   45d70:	447b      	add	r3, pc
   45d72:	2201      	movs	r2, #1
   45d74:	f240 215a 	movw	r1, #602	; 0x25a
   45d78:	4821      	ldr	r0, [pc, #132]	; (45e00 <TEEC_InvokeCommand+0x1a8>)
   45d7a:	4478      	add	r0, pc
   45d7c:	f000 fa54 	bl	46228 <_dprintf>
   45d80:	2302      	movs	r3, #2
   45d82:	f8c7 3148 	str.w	r3, [r7, #328]	; 0x148
   45d86:	f7ca ee40 	blx	10a08 <__errno_location@plt>
   45d8a:	4603      	mov	r3, r0
   45d8c:	681b      	ldr	r3, [r3, #0]
   45d8e:	4618      	mov	r0, r3
   45d90:	f7ff fe03 	bl	4599a <ioctl_errno_to_res>
   45d94:	f8c7 014c 	str.w	r0, [r7, #332]	; 0x14c
   45d98:	e013      	b.n	45dc2 <TEEC_InvokeCommand+0x16a>
   45d9a:	f8d7 3144 	ldr.w	r3, [r7, #324]	; 0x144
   45d9e:	68db      	ldr	r3, [r3, #12]
   45da0:	f8c7 314c 	str.w	r3, [r7, #332]	; 0x14c
   45da4:	f8d7 3144 	ldr.w	r3, [r7, #324]	; 0x144
   45da8:	691b      	ldr	r3, [r3, #16]
   45daa:	f8c7 3148 	str.w	r3, [r7, #328]	; 0x148
   45dae:	f107 0210 	add.w	r2, r7, #16
   45db2:	1d3b      	adds	r3, r7, #4
   45db4:	f8d7 1140 	ldr.w	r1, [r7, #320]	; 0x140
   45db8:	6818      	ldr	r0, [r3, #0]
   45dba:	f7ff fd24 	bl	45806 <teec_post_process_operation>
   45dbe:	f7ff f91d 	bl	44ffc <bm_timestamp>
   45dc2:	f107 0210 	add.w	r2, r7, #16
   45dc6:	1d3b      	adds	r3, r7, #4
   45dc8:	4611      	mov	r1, r2
   45dca:	6818      	ldr	r0, [r3, #0]
   45dcc:	f7ff fdbb 	bl	45946 <teec_free_temp_refs>
   45dd0:	463b      	mov	r3, r7
   45dd2:	681b      	ldr	r3, [r3, #0]
   45dd4:	2b00      	cmp	r3, #0
   45dd6:	d004      	beq.n	45de2 <TEEC_InvokeCommand+0x18a>
   45dd8:	463b      	mov	r3, r7
   45dda:	681b      	ldr	r3, [r3, #0]
   45ddc:	f8d7 2148 	ldr.w	r2, [r7, #328]	; 0x148
   45de0:	601a      	str	r2, [r3, #0]
   45de2:	f8d7 314c 	ldr.w	r3, [r7, #332]	; 0x14c
   45de6:	4618      	mov	r0, r3
   45de8:	f507 77aa 	add.w	r7, r7, #340	; 0x154
   45dec:	46bd      	mov	sp, r7
   45dee:	bd90      	pop	{r4, r7, pc}
   45df0:	00011fae 	andeq	r1, r1, lr, lsr #31
   45df4:	00011f98 	muleq	r1, r8, pc	; <UNPREDICTABLE>
   45df8:	00000d4e 	andeq	r0, r0, lr, asr #26
   45dfc:	00000cd0 	ldrdeq	r0, [r0], -r0	; <UNPREDICTABLE>
   45e00:	00000da2 	andeq	r0, r0, r2, lsr #27

00045e04 <TEEC_RequestCancellation>:
   45e04:	b580      	push	{r7, lr}
   45e06:	b088      	sub	sp, #32
   45e08:	af02      	add	r7, sp, #8
   45e0a:	6078      	str	r0, [r7, #4]
   45e0c:	687b      	ldr	r3, [r7, #4]
   45e0e:	2b00      	cmp	r3, #0
   45e10:	d039      	beq.n	45e86 <TEEC_RequestCancellation+0x82>
   45e12:	4b20      	ldr	r3, [pc, #128]	; (45e94 <TEEC_RequestCancellation+0x90>)
   45e14:	447b      	add	r3, pc
   45e16:	4618      	mov	r0, r3
   45e18:	f7ff f8f7 	bl	4500a <teec_mutex_lock>
   45e1c:	687b      	ldr	r3, [r7, #4]
   45e1e:	6b9b      	ldr	r3, [r3, #56]	; 0x38
   45e20:	617b      	str	r3, [r7, #20]
   45e22:	4b1d      	ldr	r3, [pc, #116]	; (45e98 <TEEC_RequestCancellation+0x94>)
   45e24:	447b      	add	r3, pc
   45e26:	4618      	mov	r0, r3
   45e28:	f7ff f8fa 	bl	45020 <teec_mutex_unlock>
   45e2c:	697b      	ldr	r3, [r7, #20]
   45e2e:	2b00      	cmp	r3, #0
   45e30:	d02b      	beq.n	45e8a <TEEC_RequestCancellation+0x86>
   45e32:	697b      	ldr	r3, [r7, #20]
   45e34:	685b      	ldr	r3, [r3, #4]
   45e36:	613b      	str	r3, [r7, #16]
   45e38:	2300      	movs	r3, #0
   45e3a:	60fb      	str	r3, [r7, #12]
   45e3c:	697b      	ldr	r3, [r7, #20]
   45e3e:	681b      	ldr	r3, [r3, #0]
   45e40:	681b      	ldr	r3, [r3, #0]
   45e42:	f107 020c 	add.w	r2, r7, #12
   45e46:	f24a 4104 	movw	r1, #41988	; 0xa404
   45e4a:	f2c8 0108 	movt	r1, #32776	; 0x8008
   45e4e:	4618      	mov	r0, r3
   45e50:	f7ca ed9e 	blx	10990 <ioctl@plt>
   45e54:	4603      	mov	r3, r0
   45e56:	2b00      	cmp	r3, #0
   45e58:	d018      	beq.n	45e8c <TEEC_RequestCancellation+0x88>
   45e5a:	f7ca edd6 	blx	10a08 <__errno_location@plt>
   45e5e:	4603      	mov	r3, r0
   45e60:	681b      	ldr	r3, [r3, #0]
   45e62:	4618      	mov	r0, r3
   45e64:	f7ca edb2 	blx	109cc <strerror@plt>
   45e68:	4603      	mov	r3, r0
   45e6a:	9301      	str	r3, [sp, #4]
   45e6c:	4b0b      	ldr	r3, [pc, #44]	; (45e9c <TEEC_RequestCancellation+0x98>)
   45e6e:	447b      	add	r3, pc
   45e70:	9300      	str	r3, [sp, #0]
   45e72:	4b0b      	ldr	r3, [pc, #44]	; (45ea0 <TEEC_RequestCancellation+0x9c>)
   45e74:	447b      	add	r3, pc
   45e76:	2201      	movs	r2, #1
   45e78:	f240 2181 	movw	r1, #641	; 0x281
   45e7c:	4809      	ldr	r0, [pc, #36]	; (45ea4 <TEEC_RequestCancellation+0xa0>)
   45e7e:	4478      	add	r0, pc
   45e80:	f000 f9d2 	bl	46228 <_dprintf>
   45e84:	e002      	b.n	45e8c <TEEC_RequestCancellation+0x88>
   45e86:	bf00      	nop
   45e88:	e000      	b.n	45e8c <TEEC_RequestCancellation+0x88>
   45e8a:	bf00      	nop
   45e8c:	3718      	adds	r7, #24
   45e8e:	46bd      	mov	sp, r7
   45e90:	bd80      	pop	{r7, pc}
   45e92:	bf00      	nop
   45e94:	00011e90 	muleq	r1, r0, lr
   45e98:	00011e80 	andeq	r1, r1, r0, lsl #29
   45e9c:	00000c62 	andeq	r0, r0, r2, ror #24
   45ea0:	00000bcc 	andeq	r0, r0, ip, asr #23
   45ea4:	00000cb2 			; <UNDEFINED> instruction: 0x00000cb2

00045ea8 <TEEC_RegisterSharedMemory>:
   45ea8:	b580      	push	{r7, lr}
   45eaa:	b086      	sub	sp, #24
   45eac:	af02      	add	r7, sp, #8
   45eae:	6078      	str	r0, [r7, #4]
   45eb0:	6039      	str	r1, [r7, #0]
   45eb2:	687b      	ldr	r3, [r7, #4]
   45eb4:	2b00      	cmp	r3, #0
   45eb6:	d002      	beq.n	45ebe <TEEC_RegisterSharedMemory+0x16>
   45eb8:	683b      	ldr	r3, [r7, #0]
   45eba:	2b00      	cmp	r3, #0
   45ebc:	d103      	bne.n	45ec6 <TEEC_RegisterSharedMemory+0x1e>
   45ebe:	2306      	movs	r3, #6
   45ec0:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   45ec4:	e069      	b.n	45f9a <TEEC_RegisterSharedMemory+0xf2>
   45ec6:	683b      	ldr	r3, [r7, #0]
   45ec8:	689b      	ldr	r3, [r3, #8]
   45eca:	2b00      	cmp	r3, #0
   45ecc:	d005      	beq.n	45eda <TEEC_RegisterSharedMemory+0x32>
   45ece:	683b      	ldr	r3, [r7, #0]
   45ed0:	689b      	ldr	r3, [r3, #8]
   45ed2:	f023 0303 	bic.w	r3, r3, #3
   45ed6:	2b00      	cmp	r3, #0
   45ed8:	d003      	beq.n	45ee2 <TEEC_RegisterSharedMemory+0x3a>
   45eda:	2306      	movs	r3, #6
   45edc:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   45ee0:	e05b      	b.n	45f9a <TEEC_RegisterSharedMemory+0xf2>
   45ee2:	683b      	ldr	r3, [r7, #0]
   45ee4:	685b      	ldr	r3, [r3, #4]
   45ee6:	60fb      	str	r3, [r7, #12]
   45ee8:	68fb      	ldr	r3, [r7, #12]
   45eea:	2b00      	cmp	r3, #0
   45eec:	d101      	bne.n	45ef2 <TEEC_RegisterSharedMemory+0x4a>
   45eee:	2308      	movs	r3, #8
   45ef0:	60fb      	str	r3, [r7, #12]
   45ef2:	687b      	ldr	r3, [r7, #4]
   45ef4:	791b      	ldrb	r3, [r3, #4]
   45ef6:	2b00      	cmp	r3, #0
   45ef8:	d017      	beq.n	45f2a <TEEC_RegisterSharedMemory+0x82>
   45efa:	687b      	ldr	r3, [r7, #4]
   45efc:	6818      	ldr	r0, [r3, #0]
   45efe:	683b      	ldr	r3, [r7, #0]
   45f00:	6819      	ldr	r1, [r3, #0]
   45f02:	683b      	ldr	r3, [r7, #0]
   45f04:	330c      	adds	r3, #12
   45f06:	68fa      	ldr	r2, [r7, #12]
   45f08:	f7ff f921 	bl	4514e <teec_shm_register>
   45f0c:	60b8      	str	r0, [r7, #8]
   45f0e:	68bb      	ldr	r3, [r7, #8]
   45f10:	2b00      	cmp	r3, #0
   45f12:	da03      	bge.n	45f1c <TEEC_RegisterSharedMemory+0x74>
   45f14:	230c      	movs	r3, #12
   45f16:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   45f1a:	e03e      	b.n	45f9a <TEEC_RegisterSharedMemory+0xf2>
   45f1c:	683b      	ldr	r3, [r7, #0]
   45f1e:	68ba      	ldr	r2, [r7, #8]
   45f20:	619a      	str	r2, [r3, #24]
   45f22:	683b      	ldr	r3, [r7, #0]
   45f24:	2200      	movs	r2, #0
   45f26:	615a      	str	r2, [r3, #20]
   45f28:	e030      	b.n	45f8c <TEEC_RegisterSharedMemory+0xe4>
   45f2a:	687b      	ldr	r3, [r7, #4]
   45f2c:	6818      	ldr	r0, [r3, #0]
   45f2e:	683b      	ldr	r3, [r7, #0]
   45f30:	330c      	adds	r3, #12
   45f32:	461a      	mov	r2, r3
   45f34:	68f9      	ldr	r1, [r7, #12]
   45f36:	f7ff f8df 	bl	450f8 <teec_shm_alloc>
   45f3a:	60b8      	str	r0, [r7, #8]
   45f3c:	68bb      	ldr	r3, [r7, #8]
   45f3e:	2b00      	cmp	r3, #0
   45f40:	da03      	bge.n	45f4a <TEEC_RegisterSharedMemory+0xa2>
   45f42:	230c      	movs	r3, #12
   45f44:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   45f48:	e027      	b.n	45f9a <TEEC_RegisterSharedMemory+0xf2>
   45f4a:	2300      	movs	r3, #0
   45f4c:	9301      	str	r3, [sp, #4]
   45f4e:	68bb      	ldr	r3, [r7, #8]
   45f50:	9300      	str	r3, [sp, #0]
   45f52:	2301      	movs	r3, #1
   45f54:	2203      	movs	r2, #3
   45f56:	68f9      	ldr	r1, [r7, #12]
   45f58:	2000      	movs	r0, #0
   45f5a:	f7ca ed4a 	blx	109f0 <mmap@plt>
   45f5e:	4602      	mov	r2, r0
   45f60:	683b      	ldr	r3, [r7, #0]
   45f62:	615a      	str	r2, [r3, #20]
   45f64:	68b8      	ldr	r0, [r7, #8]
   45f66:	f7ca ed9e 	blx	10aa4 <close@plt>
   45f6a:	683b      	ldr	r3, [r7, #0]
   45f6c:	695b      	ldr	r3, [r3, #20]
   45f6e:	f1b3 3fff 	cmp.w	r3, #4294967295	; 0xffffffff
   45f72:	d107      	bne.n	45f84 <TEEC_RegisterSharedMemory+0xdc>
   45f74:	683b      	ldr	r3, [r7, #0]
   45f76:	f04f 32ff 	mov.w	r2, #4294967295	; 0xffffffff
   45f7a:	60da      	str	r2, [r3, #12]
   45f7c:	230c      	movs	r3, #12
   45f7e:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   45f82:	e00a      	b.n	45f9a <TEEC_RegisterSharedMemory+0xf2>
   45f84:	683b      	ldr	r3, [r7, #0]
   45f86:	f04f 32ff 	mov.w	r2, #4294967295	; 0xffffffff
   45f8a:	619a      	str	r2, [r3, #24]
   45f8c:	683b      	ldr	r3, [r7, #0]
   45f8e:	68fa      	ldr	r2, [r7, #12]
   45f90:	611a      	str	r2, [r3, #16]
   45f92:	683b      	ldr	r3, [r7, #0]
   45f94:	2200      	movs	r2, #0
   45f96:	771a      	strb	r2, [r3, #28]
   45f98:	2300      	movs	r3, #0
   45f9a:	4618      	mov	r0, r3
   45f9c:	3710      	adds	r7, #16
   45f9e:	46bd      	mov	sp, r7
   45fa0:	bd80      	pop	{r7, pc}

00045fa2 <TEEC_RegisterSharedMemoryFileDescriptor>:
   45fa2:	b590      	push	{r4, r7, lr}
   45fa4:	b08d      	sub	sp, #52	; 0x34
   45fa6:	af00      	add	r7, sp, #0
   45fa8:	60f8      	str	r0, [r7, #12]
   45faa:	60b9      	str	r1, [r7, #8]
   45fac:	607a      	str	r2, [r7, #4]
   45fae:	68fb      	ldr	r3, [r7, #12]
   45fb0:	2b00      	cmp	r3, #0
   45fb2:	d005      	beq.n	45fc0 <TEEC_RegisterSharedMemoryFileDescriptor+0x1e>
   45fb4:	68bb      	ldr	r3, [r7, #8]
   45fb6:	2b00      	cmp	r3, #0
   45fb8:	d002      	beq.n	45fc0 <TEEC_RegisterSharedMemoryFileDescriptor+0x1e>
   45fba:	687b      	ldr	r3, [r7, #4]
   45fbc:	2b00      	cmp	r3, #0
   45fbe:	da03      	bge.n	45fc8 <TEEC_RegisterSharedMemoryFileDescriptor+0x26>
   45fc0:	2306      	movs	r3, #6
   45fc2:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   45fc6:	e03e      	b.n	46046 <TEEC_RegisterSharedMemoryFileDescriptor+0xa4>
   45fc8:	68bb      	ldr	r3, [r7, #8]
   45fca:	689b      	ldr	r3, [r3, #8]
   45fcc:	2b00      	cmp	r3, #0
   45fce:	d005      	beq.n	45fdc <TEEC_RegisterSharedMemoryFileDescriptor+0x3a>
   45fd0:	68bb      	ldr	r3, [r7, #8]
   45fd2:	689b      	ldr	r3, [r3, #8]
   45fd4:	f023 0303 	bic.w	r3, r3, #3
   45fd8:	2b00      	cmp	r3, #0
   45fda:	d003      	beq.n	45fe4 <TEEC_RegisterSharedMemoryFileDescriptor+0x42>
   45fdc:	2306      	movs	r3, #6
   45fde:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   45fe2:	e030      	b.n	46046 <TEEC_RegisterSharedMemoryFileDescriptor+0xa4>
   45fe4:	f107 0310 	add.w	r3, r7, #16
   45fe8:	2218      	movs	r2, #24
   45fea:	2100      	movs	r1, #0
   45fec:	4618      	mov	r0, r3
   45fee:	f7ca ed18 	blx	10a20 <memset@plt>
   45ff2:	687b      	ldr	r3, [r7, #4]
   45ff4:	ea4f 74e3 	mov.w	r4, r3, asr #31
   45ff8:	e9c7 3404 	strd	r3, r4, [r7, #16]
   45ffc:	68fb      	ldr	r3, [r7, #12]
   45ffe:	681b      	ldr	r3, [r3, #0]
   46000:	f107 0210 	add.w	r2, r7, #16
   46004:	f24a 4108 	movw	r1, #41992	; 0xa408
   46008:	f2cc 0118 	movt	r1, #49176	; 0xc018
   4600c:	4618      	mov	r0, r3
   4600e:	f7ca ecc0 	blx	10990 <ioctl@plt>
   46012:	62f8      	str	r0, [r7, #44]	; 0x2c
   46014:	6afb      	ldr	r3, [r7, #44]	; 0x2c
   46016:	2b00      	cmp	r3, #0
   46018:	da03      	bge.n	46022 <TEEC_RegisterSharedMemoryFileDescriptor+0x80>
   4601a:	2306      	movs	r3, #6
   4601c:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   46020:	e011      	b.n	46046 <TEEC_RegisterSharedMemoryFileDescriptor+0xa4>
   46022:	68bb      	ldr	r3, [r7, #8]
   46024:	2200      	movs	r2, #0
   46026:	601a      	str	r2, [r3, #0]
   46028:	68bb      	ldr	r3, [r7, #8]
   4602a:	2200      	movs	r2, #0
   4602c:	615a      	str	r2, [r3, #20]
   4602e:	68bb      	ldr	r3, [r7, #8]
   46030:	6afa      	ldr	r2, [r7, #44]	; 0x2c
   46032:	619a      	str	r2, [r3, #24]
   46034:	6a7a      	ldr	r2, [r7, #36]	; 0x24
   46036:	68bb      	ldr	r3, [r7, #8]
   46038:	60da      	str	r2, [r3, #12]
   4603a:	e9d7 3406 	ldrd	r3, r4, [r7, #24]
   4603e:	461a      	mov	r2, r3
   46040:	68bb      	ldr	r3, [r7, #8]
   46042:	605a      	str	r2, [r3, #4]
   46044:	2300      	movs	r3, #0
   46046:	4618      	mov	r0, r3
   46048:	3734      	adds	r7, #52	; 0x34
   4604a:	46bd      	mov	sp, r7
   4604c:	bd90      	pop	{r4, r7, pc}

0004604e <TEEC_AllocateSharedMemory>:
   4604e:	b580      	push	{r7, lr}
   46050:	b086      	sub	sp, #24
   46052:	af02      	add	r7, sp, #8
   46054:	6078      	str	r0, [r7, #4]
   46056:	6039      	str	r1, [r7, #0]
   46058:	687b      	ldr	r3, [r7, #4]
   4605a:	2b00      	cmp	r3, #0
   4605c:	d002      	beq.n	46064 <TEEC_AllocateSharedMemory+0x16>
   4605e:	683b      	ldr	r3, [r7, #0]
   46060:	2b00      	cmp	r3, #0
   46062:	d103      	bne.n	4606c <TEEC_AllocateSharedMemory+0x1e>
   46064:	2306      	movs	r3, #6
   46066:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   4606a:	e080      	b.n	4616e <TEEC_AllocateSharedMemory+0x120>
   4606c:	683b      	ldr	r3, [r7, #0]
   4606e:	689b      	ldr	r3, [r3, #8]
   46070:	2b00      	cmp	r3, #0
   46072:	d005      	beq.n	46080 <TEEC_AllocateSharedMemory+0x32>
   46074:	683b      	ldr	r3, [r7, #0]
   46076:	689b      	ldr	r3, [r3, #8]
   46078:	f023 0303 	bic.w	r3, r3, #3
   4607c:	2b00      	cmp	r3, #0
   4607e:	d003      	beq.n	46088 <TEEC_AllocateSharedMemory+0x3a>
   46080:	2306      	movs	r3, #6
   46082:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   46086:	e072      	b.n	4616e <TEEC_AllocateSharedMemory+0x120>
   46088:	683b      	ldr	r3, [r7, #0]
   4608a:	685b      	ldr	r3, [r3, #4]
   4608c:	60fb      	str	r3, [r7, #12]
   4608e:	68fb      	ldr	r3, [r7, #12]
   46090:	2b00      	cmp	r3, #0
   46092:	d101      	bne.n	46098 <TEEC_AllocateSharedMemory+0x4a>
   46094:	2308      	movs	r3, #8
   46096:	60fb      	str	r3, [r7, #12]
   46098:	687b      	ldr	r3, [r7, #4]
   4609a:	791b      	ldrb	r3, [r3, #4]
   4609c:	2b00      	cmp	r3, #0
   4609e:	d02b      	beq.n	460f8 <TEEC_AllocateSharedMemory+0xaa>
   460a0:	68f8      	ldr	r0, [r7, #12]
   460a2:	f7ca ec8e 	blx	109c0 <malloc@plt>
   460a6:	4603      	mov	r3, r0
   460a8:	461a      	mov	r2, r3
   460aa:	683b      	ldr	r3, [r7, #0]
   460ac:	601a      	str	r2, [r3, #0]
   460ae:	683b      	ldr	r3, [r7, #0]
   460b0:	681b      	ldr	r3, [r3, #0]
   460b2:	2b00      	cmp	r3, #0
   460b4:	d103      	bne.n	460be <TEEC_AllocateSharedMemory+0x70>
   460b6:	230c      	movs	r3, #12
   460b8:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   460bc:	e057      	b.n	4616e <TEEC_AllocateSharedMemory+0x120>
   460be:	687b      	ldr	r3, [r7, #4]
   460c0:	6818      	ldr	r0, [r3, #0]
   460c2:	683b      	ldr	r3, [r7, #0]
   460c4:	6819      	ldr	r1, [r3, #0]
   460c6:	683b      	ldr	r3, [r7, #0]
   460c8:	330c      	adds	r3, #12
   460ca:	68fa      	ldr	r2, [r7, #12]
   460cc:	f7ff f83f 	bl	4514e <teec_shm_register>
   460d0:	60b8      	str	r0, [r7, #8]
   460d2:	68bb      	ldr	r3, [r7, #8]
   460d4:	2b00      	cmp	r3, #0
   460d6:	da0b      	bge.n	460f0 <TEEC_AllocateSharedMemory+0xa2>
   460d8:	683b      	ldr	r3, [r7, #0]
   460da:	681b      	ldr	r3, [r3, #0]
   460dc:	4618      	mov	r0, r3
   460de:	f7ca ec40 	blx	10960 <free@plt>
   460e2:	683b      	ldr	r3, [r7, #0]
   460e4:	2200      	movs	r2, #0
   460e6:	601a      	str	r2, [r3, #0]
   460e8:	230c      	movs	r3, #12
   460ea:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   460ee:	e03e      	b.n	4616e <TEEC_AllocateSharedMemory+0x120>
   460f0:	683b      	ldr	r3, [r7, #0]
   460f2:	68ba      	ldr	r2, [r7, #8]
   460f4:	619a      	str	r2, [r3, #24]
   460f6:	e030      	b.n	4615a <TEEC_AllocateSharedMemory+0x10c>
   460f8:	687b      	ldr	r3, [r7, #4]
   460fa:	6818      	ldr	r0, [r3, #0]
   460fc:	683b      	ldr	r3, [r7, #0]
   460fe:	330c      	adds	r3, #12
   46100:	461a      	mov	r2, r3
   46102:	68f9      	ldr	r1, [r7, #12]
   46104:	f7fe fff8 	bl	450f8 <teec_shm_alloc>
   46108:	60b8      	str	r0, [r7, #8]
   4610a:	68bb      	ldr	r3, [r7, #8]
   4610c:	2b00      	cmp	r3, #0
   4610e:	da03      	bge.n	46118 <TEEC_AllocateSharedMemory+0xca>
   46110:	230c      	movs	r3, #12
   46112:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   46116:	e02a      	b.n	4616e <TEEC_AllocateSharedMemory+0x120>
   46118:	2300      	movs	r3, #0
   4611a:	9301      	str	r3, [sp, #4]
   4611c:	68bb      	ldr	r3, [r7, #8]
   4611e:	9300      	str	r3, [sp, #0]
   46120:	2301      	movs	r3, #1
   46122:	2203      	movs	r2, #3
   46124:	68f9      	ldr	r1, [r7, #12]
   46126:	2000      	movs	r0, #0
   46128:	f7ca ec62 	blx	109f0 <mmap@plt>
   4612c:	4602      	mov	r2, r0
   4612e:	683b      	ldr	r3, [r7, #0]
   46130:	601a      	str	r2, [r3, #0]
   46132:	68b8      	ldr	r0, [r7, #8]
   46134:	f7ca ecb6 	blx	10aa4 <close@plt>
   46138:	683b      	ldr	r3, [r7, #0]
   4613a:	681b      	ldr	r3, [r3, #0]
   4613c:	f1b3 3fff 	cmp.w	r3, #4294967295	; 0xffffffff
   46140:	d107      	bne.n	46152 <TEEC_AllocateSharedMemory+0x104>
   46142:	683b      	ldr	r3, [r7, #0]
   46144:	f04f 32ff 	mov.w	r2, #4294967295	; 0xffffffff
   46148:	60da      	str	r2, [r3, #12]
   4614a:	230c      	movs	r3, #12
   4614c:	f6cf 73ff 	movt	r3, #65535	; 0xffff
   46150:	e00d      	b.n	4616e <TEEC_AllocateSharedMemory+0x120>
   46152:	683b      	ldr	r3, [r7, #0]
   46154:	f04f 32ff 	mov.w	r2, #4294967295	; 0xffffffff
   46158:	619a      	str	r2, [r3, #24]
   4615a:	683b      	ldr	r3, [r7, #0]
   4615c:	2200      	movs	r2, #0
   4615e:	615a      	str	r2, [r3, #20]
   46160:	683b      	ldr	r3, [r7, #0]
   46162:	68fa      	ldr	r2, [r7, #12]
   46164:	611a      	str	r2, [r3, #16]
   46166:	683b      	ldr	r3, [r7, #0]
   46168:	2201      	movs	r2, #1
   4616a:	771a      	strb	r2, [r3, #28]
   4616c:	2300      	movs	r3, #0
   4616e:	4618      	mov	r0, r3
   46170:	3710      	adds	r7, #16
   46172:	46bd      	mov	sp, r7
   46174:	bd80      	pop	{r7, pc}

00046176 <TEEC_ReleaseSharedMemory>:
   46176:	b580      	push	{r7, lr}
   46178:	b082      	sub	sp, #8
   4617a:	af00      	add	r7, sp, #0
   4617c:	6078      	str	r0, [r7, #4]
   4617e:	687b      	ldr	r3, [r7, #4]
   46180:	2b00      	cmp	r3, #0
   46182:	d04c      	beq.n	4621e <TEEC_ReleaseSharedMemory+0xa8>
   46184:	687b      	ldr	r3, [r7, #4]
   46186:	68db      	ldr	r3, [r3, #12]
   46188:	f1b3 3fff 	cmp.w	r3, #4294967295	; 0xffffffff
   4618c:	d047      	beq.n	4621e <TEEC_ReleaseSharedMemory+0xa8>
   4618e:	687b      	ldr	r3, [r7, #4]
   46190:	695b      	ldr	r3, [r3, #20]
   46192:	2b00      	cmp	r3, #0
   46194:	d008      	beq.n	461a8 <TEEC_ReleaseSharedMemory+0x32>
   46196:	687b      	ldr	r3, [r7, #4]
   46198:	695a      	ldr	r2, [r3, #20]
   4619a:	687b      	ldr	r3, [r7, #4]
   4619c:	691b      	ldr	r3, [r3, #16]
   4619e:	4619      	mov	r1, r3
   461a0:	4610      	mov	r0, r2
   461a2:	f7ca ec50 	blx	10a44 <munmap@plt>
   461a6:	e028      	b.n	461fa <TEEC_ReleaseSharedMemory+0x84>
   461a8:	687b      	ldr	r3, [r7, #4]
   461aa:	681b      	ldr	r3, [r3, #0]
   461ac:	2b00      	cmp	r3, #0
   461ae:	d01b      	beq.n	461e8 <TEEC_ReleaseSharedMemory+0x72>
   461b0:	687b      	ldr	r3, [r7, #4]
   461b2:	699b      	ldr	r3, [r3, #24]
   461b4:	2b00      	cmp	r3, #0
   461b6:	db0e      	blt.n	461d6 <TEEC_ReleaseSharedMemory+0x60>
   461b8:	687b      	ldr	r3, [r7, #4]
   461ba:	7f1b      	ldrb	r3, [r3, #28]
   461bc:	2b00      	cmp	r3, #0
   461be:	d004      	beq.n	461ca <TEEC_ReleaseSharedMemory+0x54>
   461c0:	687b      	ldr	r3, [r7, #4]
   461c2:	681b      	ldr	r3, [r3, #0]
   461c4:	4618      	mov	r0, r3
   461c6:	f7ca ebcc 	blx	10960 <free@plt>
   461ca:	687b      	ldr	r3, [r7, #4]
   461cc:	699b      	ldr	r3, [r3, #24]
   461ce:	4618      	mov	r0, r3
   461d0:	f7ca ec68 	blx	10aa4 <close@plt>
   461d4:	e011      	b.n	461fa <TEEC_ReleaseSharedMemory+0x84>
   461d6:	687b      	ldr	r3, [r7, #4]
   461d8:	681a      	ldr	r2, [r3, #0]
   461da:	687b      	ldr	r3, [r7, #4]
   461dc:	691b      	ldr	r3, [r3, #16]
   461de:	4619      	mov	r1, r3
   461e0:	4610      	mov	r0, r2
   461e2:	f7ca ec30 	blx	10a44 <munmap@plt>
   461e6:	e008      	b.n	461fa <TEEC_ReleaseSharedMemory+0x84>
   461e8:	687b      	ldr	r3, [r7, #4]
   461ea:	699b      	ldr	r3, [r3, #24]
   461ec:	2b00      	cmp	r3, #0
   461ee:	db04      	blt.n	461fa <TEEC_ReleaseSharedMemory+0x84>
   461f0:	687b      	ldr	r3, [r7, #4]
   461f2:	699b      	ldr	r3, [r3, #24]
   461f4:	4618      	mov	r0, r3
   461f6:	f7ca ec56 	blx	10aa4 <close@plt>
   461fa:	687b      	ldr	r3, [r7, #4]
   461fc:	f04f 32ff 	mov.w	r2, #4294967295	; 0xffffffff
   46200:	60da      	str	r2, [r3, #12]
   46202:	687b      	ldr	r3, [r7, #4]
   46204:	2200      	movs	r2, #0
   46206:	615a      	str	r2, [r3, #20]
   46208:	687b      	ldr	r3, [r7, #4]
   4620a:	2200      	movs	r2, #0
   4620c:	601a      	str	r2, [r3, #0]
   4620e:	687b      	ldr	r3, [r7, #4]
   46210:	f04f 32ff 	mov.w	r2, #4294967295	; 0xffffffff
   46214:	619a      	str	r2, [r3, #24]
   46216:	687b      	ldr	r3, [r7, #4]
   46218:	2200      	movs	r2, #0
   4621a:	771a      	strb	r2, [r3, #28]
   4621c:	e000      	b.n	46220 <TEEC_ReleaseSharedMemory+0xaa>
   4621e:	bf00      	nop
   46220:	3708      	adds	r7, #8
   46222:	46bd      	mov	sp, r7
   46224:	bd80      	pop	{r7, pc}
   46226:	bf00      	nop

00046228 <_dprintf>:
   46228:	b590      	push	{r4, r7, lr}
   4622a:	b0cd      	sub	sp, #308	; 0x134
   4622c:	af04      	add	r7, sp, #16
   4622e:	f107 040c 	add.w	r4, r7, #12
   46232:	6020      	str	r0, [r4, #0]
   46234:	f107 0008 	add.w	r0, r7, #8
   46238:	6001      	str	r1, [r0, #0]
   4623a:	1d39      	adds	r1, r7, #4
   4623c:	600a      	str	r2, [r1, #0]
   4623e:	463a      	mov	r2, r7
   46240:	6013      	str	r3, [r2, #0]
   46242:	4c31      	ldr	r4, [pc, #196]	; (46308 <_dprintf+0xe0>)
   46244:	447c      	add	r4, pc
   46246:	2300      	movs	r3, #0
   46248:	f8c7 311c 	str.w	r3, [r7, #284]	; 0x11c
   4624c:	f107 030c 	add.w	r3, r7, #12
   46250:	681b      	ldr	r3, [r3, #0]
   46252:	2b00      	cmp	r3, #0
   46254:	d028      	beq.n	462a8 <_dprintf+0x80>
   46256:	20e0      	movs	r0, #224	; 0xe0
   46258:	f7ca ebc4 	blx	109e4 <syscall@plt>
   4625c:	f8c7 0118 	str.w	r0, [r7, #280]	; 0x118
   46260:	4b2a      	ldr	r3, [pc, #168]	; (4630c <_dprintf+0xe4>)
   46262:	447b      	add	r3, pc
   46264:	461a      	mov	r2, r3
   46266:	1d3b      	adds	r3, r7, #4
   46268:	681b      	ldr	r3, [r3, #0]
   4626a:	f852 2023 	ldr.w	r2, [r2, r3, lsl #2]
   4626e:	f107 0018 	add.w	r0, r7, #24
   46272:	f107 0308 	add.w	r3, r7, #8
   46276:	681b      	ldr	r3, [r3, #0]
   46278:	9303      	str	r3, [sp, #12]
   4627a:	f107 030c 	add.w	r3, r7, #12
   4627e:	681b      	ldr	r3, [r3, #0]
   46280:	9302      	str	r3, [sp, #8]
   46282:	463b      	mov	r3, r7
   46284:	681b      	ldr	r3, [r3, #0]
   46286:	9301      	str	r3, [sp, #4]
   46288:	f8d7 3118 	ldr.w	r3, [r7, #280]	; 0x118
   4628c:	9300      	str	r3, [sp, #0]
   4628e:	4613      	mov	r3, r2
   46290:	4a1f      	ldr	r2, [pc, #124]	; (46310 <_dprintf+0xe8>)
   46292:	447a      	add	r2, pc
   46294:	f44f 7180 	mov.w	r1, #256	; 0x100
   46298:	f7ca ebbc 	blx	10a14 <snprintf@plt>
   4629c:	f8c7 011c 	str.w	r0, [r7, #284]	; 0x11c
   462a0:	f8d7 311c 	ldr.w	r3, [r7, #284]	; 0x11c
   462a4:	2b00      	cmp	r3, #0
   462a6:	db28      	blt.n	462fa <_dprintf+0xd2>
   462a8:	f8d7 311c 	ldr.w	r3, [r7, #284]	; 0x11c
   462ac:	2bff      	cmp	r3, #255	; 0xff
   462ae:	d81a      	bhi.n	462e6 <_dprintf+0xbe>
   462b0:	f507 729a 	add.w	r2, r7, #308	; 0x134
   462b4:	f107 0314 	add.w	r3, r7, #20
   462b8:	601a      	str	r2, [r3, #0]
   462ba:	f8d7 311c 	ldr.w	r3, [r7, #284]	; 0x11c
   462be:	f107 0218 	add.w	r2, r7, #24
   462c2:	18d0      	adds	r0, r2, r3
   462c4:	f8d7 311c 	ldr.w	r3, [r7, #284]	; 0x11c
   462c8:	f5c3 7180 	rsb	r1, r3, #256	; 0x100
   462cc:	f107 0314 	add.w	r3, r7, #20
   462d0:	681b      	ldr	r3, [r3, #0]
   462d2:	f8d7 2130 	ldr.w	r2, [r7, #304]	; 0x130
   462d6:	f7ca ebd4 	blx	10a80 <vsnprintf@plt>
   462da:	f8c7 011c 	str.w	r0, [r7, #284]	; 0x11c
   462de:	f8d7 311c 	ldr.w	r3, [r7, #284]	; 0x11c
   462e2:	2b00      	cmp	r3, #0
   462e4:	db0b      	blt.n	462fe <_dprintf+0xd6>
   462e6:	4b0b      	ldr	r3, [pc, #44]	; (46314 <_dprintf+0xec>)
   462e8:	58e3      	ldr	r3, [r4, r3]
   462ea:	681a      	ldr	r2, [r3, #0]
   462ec:	f107 0318 	add.w	r3, r7, #24
   462f0:	4611      	mov	r1, r2
   462f2:	4618      	mov	r0, r3
   462f4:	f7ca ebd0 	blx	10a98 <fputs@plt>
   462f8:	e002      	b.n	46300 <_dprintf+0xd8>
   462fa:	bf00      	nop
   462fc:	e000      	b.n	46300 <_dprintf+0xd8>
   462fe:	bf00      	nop
   46300:	f507 7792 	add.w	r7, r7, #292	; 0x124
   46304:	46bd      	mov	sp, r7
   46306:	bd90      	pop	{r4, r7, pc}
   46308:	00010db8 			; <UNDEFINED> instruction: 0x00010db8
   4630c:	00010cc6 	andeq	r0, r1, r6, asr #25
   46310:	000008ce 	andeq	r0, r0, lr, asr #17
   46314:	000000b8 	strheq	r0, [r0], -r8

00046318 <dump_buffer>:
   46318:	b480      	push	{r7}
   4631a:	b085      	sub	sp, #20
   4631c:	af00      	add	r7, sp, #0
   4631e:	60f8      	str	r0, [r7, #12]
   46320:	60b9      	str	r1, [r7, #8]
   46322:	607a      	str	r2, [r7, #4]
   46324:	bf00      	nop
   46326:	3714      	adds	r7, #20
   46328:	46bd      	mov	sp, r7
   4632a:	f85d 7b04 	ldr.w	r7, [sp], #4
   4632e:	4770      	bx	lr

Disassembly of section .trampoline:

00046330 <__cfv_icall>:
   46330:	e24dd080 	sub	sp, sp, #128	; 0x80
   46334:	e58d0000 	str	r0, [sp]
   46338:	e58d1008 	str	r1, [sp, #8]
   4633c:	e58d2010 	str	r2, [sp, #16]
   46340:	e58d3018 	str	r3, [sp, #24]
   46344:	e58d4020 	str	r4, [sp, #32]
   46348:	e58d5028 	str	r5, [sp, #40]	; 0x28
   4634c:	e58d6030 	str	r6, [sp, #48]	; 0x30
   46350:	e58d7038 	str	r7, [sp, #56]	; 0x38
   46354:	e58d8040 	str	r8, [sp, #64]	; 0x40
   46358:	e58d9048 	str	r9, [sp, #72]	; 0x48
   4635c:	e58da050 	str	sl, [sp, #80]	; 0x50
   46360:	e58db058 	str	fp, [sp, #88]	; 0x58
   46364:	e58dc060 	str	ip, [sp, #96]	; 0x60
   46368:	e58dd068 	str	sp, [sp, #104]	; 0x68
   4636c:	e58de070 	str	lr, [sp, #112]	; 0x70
   46370:	e10f4000 	mrs	r4, CPSR
   46374:	e58d4078 	str	r4, [sp, #120]	; 0x78
   46378:	fafff986 	blx	44998 <view_switch_to_rd_and_log>
   4637c:	e59d4078 	ldr	r4, [sp, #120]	; 0x78
   46380:	e129f004 	msr	CPSR_fc, r4
   46384:	e59d0000 	ldr	r0, [sp]
   46388:	e59d1008 	ldr	r1, [sp, #8]
   4638c:	e59d2010 	ldr	r2, [sp, #16]
   46390:	e59d3018 	ldr	r3, [sp, #24]
   46394:	e59d4020 	ldr	r4, [sp, #32]
   46398:	e59d5028 	ldr	r5, [sp, #40]	; 0x28
   4639c:	e59d6030 	ldr	r6, [sp, #48]	; 0x30
   463a0:	e59d7038 	ldr	r7, [sp, #56]	; 0x38
   463a4:	e59d8040 	ldr	r8, [sp, #64]	; 0x40
   463a8:	e59d9048 	ldr	r9, [sp, #72]	; 0x48
   463ac:	e59da050 	ldr	sl, [sp, #80]	; 0x50
   463b0:	e59db058 	ldr	fp, [sp, #88]	; 0x58
   463b4:	e59dc060 	ldr	ip, [sp, #96]	; 0x60
   463b8:	e59dd068 	ldr	sp, [sp, #104]	; 0x68
   463bc:	e59de070 	ldr	lr, [sp, #112]	; 0x70
   463c0:	e28dd080 	add	sp, sp, #128	; 0x80
   463c4:	e1a0f00e 	mov	pc, lr

000463c8 <__cfv_icall_blx>:
   463c8:	e52de004 	push	{lr}		; (str lr, [sp, #-4]!)
   463cc:	e52d0004 	push	{r0}		; (str r0, [sp, #-4]!)
   463d0:	e52d1004 	push	{r1}		; (str r1, [sp, #-4]!)
   463d4:	e52d2004 	push	{r2}		; (str r2, [sp, #-4]!)
   463d8:	e52d3004 	push	{r3}		; (str r3, [sp, #-4]!)
   463dc:	e1a0000e 	mov	r0, lr
   463e0:	fafff897 	blx	44644 <cfv_icall_blx>
   463e4:	e49d3004 	pop	{r3}		; (ldr r3, [sp], #4)
   463e8:	e49d2004 	pop	{r2}		; (ldr r2, [sp], #4)
   463ec:	e49d1004 	pop	{r1}		; (ldr r1, [sp], #4)
   463f0:	e49d0004 	pop	{r0}		; (ldr r0, [sp], #4)
   463f4:	e49df004 	pop	{pc}		; (ldr pc, [sp], #4)

000463f8 <__cfv_icall_blx_pre>:
   463f8:	e92d400f 	push	{r0, r1, r2, r3, lr}
   463fc:	e1a0000e 	mov	r0, lr
   46400:	fafff8b8 	blx	446e8 <cfv_icall_blx_pre>
   46404:	e8bd800f 	pop	{r0, r1, r2, r3, pc}

00046408 <__cfv_icall_cond_dirbranch>:
   46408:	e92d400f 	push	{r0, r1, r2, r3, lr}
   4640c:	e1a0000e 	mov	r0, lr
   46410:	fafff8fc 	blx	44808 <cfv_icall_bc_blc>
   46414:	e8bd800f 	pop	{r0, r1, r2, r3, pc}

00046418 <__cfv_icall_ldmia_ret>:
   46418:	e92d400f 	push	{r0, r1, r2, r3, lr}
   4641c:	e1a0000e 	mov	r0, lr
   46420:	fafff920 	blx	448a8 <cfv_icall_ldmia_ret>
   46424:	e8bd400f 	pop	{r0, r1, r2, r3, lr}

Disassembly of section .rodata:

00046428 <mLBolusStepsLength>:
   46428:	00000009 	andeq	r0, r0, r9
   4642c:	69727953 	ldmdbvs	r2!, {r0, r1, r4, r6, r8, fp, ip, sp, lr}^
   46430:	5065676e 	rsbpl	r6, r5, lr, ror #14
   46434:	20706d75 	rsbscs	r6, r0, r5, ror sp
   46438:	302e3276 	eorcc	r3, lr, r6, ror r2
   4643c:	424c6d00 	submi	r6, ip, #0, 26
   46440:	73756c6f 	cmnvc	r5, #28416	; 0x6f00
   46444:	25203d20 	strcs	r3, [r0, #-3360]!	; 0xfffff2e0
   46448:	74202c66 	strtvc	r2, [r0], #-3174	; 0xfffff39a
   4644c:	20656d69 	rsbcs	r6, r5, r9, ror #26
   46450:	63657375 	cmnvs	r5, #-738197503	; 0xd4000001
   46454:	25203a73 	strcs	r3, [r0, #-2675]!	; 0xfffff58d
   46458:	000a756c 	andeq	r7, sl, ip, ror #10
   4645c:	52412f2e 	subpl	r2, r1, #46, 30	; 0xb8
   46460:	72625f49 	rsbvc	r5, r2, #292	; 0x124
   46464:	68636e61 	stmdavs	r3!, {r0, r5, r6, r9, sl, fp, sp, lr}^
   46468:	7478742e 	ldrbtvc	r7, [r8], #-1070	; 0xfffffbd2
   4646c:	412f2e00 			; <UNDEFINED> instruction: 0x412f2e00
   46470:	695f4952 	ldmdbvs	pc, {r1, r4, r6, r8, fp, lr}^	; <UNPREDICTABLE>
   46474:	6a5f646e 	bvs	181f634 <ringBuffer+0x17c795c>
   46478:	742e706d 	strtvc	r7, [lr], #-109	; 0xffffff93
   4647c:	2e007478 	mcrcs	4, 0, r7, cr0, cr8, {3}
   46480:	4952412f 	ldmdbmi	r2, {r0, r1, r2, r3, r5, r8, lr}^
   46484:	7465725f 	strbtvc	r7, [r5], #-607	; 0xfffffda1
   46488:	7361685f 	cmnvc	r1, #6225920	; 0x5f0000
   4648c:	78742e68 	ldmdavc	r4!, {r3, r5, r6, r9, sl, fp, sp}^
   46490:	2f2e0074 	svccs	0x002e0074
   46494:	5f495241 	svcpl	0x00495241
   46498:	2e667374 	mcrcs	3, 3, r7, cr6, cr4, {3}
   4649c:	00747874 	rsbseq	r7, r4, r4, ror r8
   464a0:	52412f2e 	subpl	r2, r1, #46, 30	; 0xb8
   464a4:	73745f49 	cmnvc	r4, #292	; 0x124
   464a8:	6f635f66 	svcvs	0x00635f66
   464ac:	742e646e 	strtvc	r6, [lr], #-1134	; 0xfffffb92
   464b0:	49007478 	stmdbmi	r0, {r3, r4, r5, r6, sl, ip, sp, lr}
   464b4:	6c61766e 	stclvs	6, cr7, [r1], #-440	; 0xfffffe48
   464b8:	63206469 			; <UNDEFINED> instruction: 0x63206469
   464bc:	616d6d6f 	cmnvs	sp, pc, ror #26
   464c0:	203a646e 	eorscs	r6, sl, lr, ror #8
   464c4:	0a5d005b 	beq	1786638 <ringBuffer+0x172e960>
   464c8:	65735500 	ldrbvs	r5, [r3, #-1280]!	; 0xfffffb00
   464cc:	64252064 	strtvs	r2, [r5], #-100	; 0xffffff9c
   464d0:	2064252e 	rsbcs	r2, r4, lr, lsr #10
   464d4:	42004c6d 	andmi	r4, r0, #27904	; 0x6d00
   464d8:	73756c6f 	cmnvc	r5, #28416	; 0x6f00
   464dc:	2e642520 	cdpcs	5, 6, cr2, cr4, cr0, {1}
   464e0:	6d206425 	cfstrsvs	mvf6, [r0, #-148]!	; 0xffffff6c
   464e4:	654d004c 	strbvs	r0, [sp, #-76]	; 0xffffffb4
   464e8:	203e756e 	eorscs	r7, lr, lr, ror #10
   464ec:	756c6f42 	strbvc	r6, [ip, #-3906]!	; 0xfffff0be
   464f0:	65745373 	ldrbvs	r5, [r4, #-883]!	; 0xfffffc8d
   464f4:	64250070 	strtvs	r0, [r5], #-112	; 0xffffff90
   464f8:	0064252e 	rsbeq	r2, r4, lr, lsr #10
   464fc:	77726f66 	ldrbvc	r6, [r2, -r6, ror #30]!
   46500:	5f647261 	svcpl	0x00647261
   46504:	67726174 			; <UNDEFINED> instruction: 0x67726174
   46508:	65207465 	strvs	r7, [r0, #-1125]!	; 0xfffffb9b
   4650c:	75636578 	strbvc	r6, [r3, #-1400]!	; 0xfffffa88
   46510:	676e6974 			; <UNDEFINED> instruction: 0x676e6974
   46514:	53000a20 	movwpl	r0, #2592	; 0xa20
   46518:	74726174 	ldrbtvc	r6, [r2], #-372	; 0xfffffe8c
   4651c:	20676e69 	rsbcs	r6, r7, r9, ror #28
   46520:	69727973 	ldmdbvs	r2!, {r0, r1, r4, r5, r6, r8, fp, ip, sp, lr}^
   46524:	2065676e 	rsbcs	r6, r5, lr, ror #14
   46528:	706d7570 	rsbvc	r7, sp, r0, ror r5
   4652c:	6868000a 	stmdavs	r8!, {r1, r3}^
   46530:	68686868 	stmdavs	r8!, {r3, r5, r6, fp, sp, lr}^
   46534:	68686868 	stmdavs	r8!, {r3, r5, r6, fp, sp, lr}^
   46538:	68686868 	stmdavs	r8!, {r3, r5, r6, fp, sp, lr}^
   4653c:	6e45000a 	cdpvs	0, 4, cr0, cr5, cr10, {0}
   46540:	676e6964 	strbvs	r6, [lr, -r4, ror #18]!
   46544:	72797320 	rsbsvc	r7, r9, #32, 6	; 0x80000000
   46548:	65676e69 	strbvs	r6, [r7, #-3689]!	; 0xfffff197
   4654c:	6d757020 	ldclvs	0, cr7, [r5, #-128]!	; 0xffffff80
   46550:	25000a70 	strcs	r0, [r0, #-2672]	; 0xfffff590
   46554:	69282073 	stmdbvs	r8!, {r0, r1, r4, r5, r6, sp}
   46558:	7020746e 	eorvc	r7, r0, lr, ror #8
   4655c:	3d206e69 	stccc	14, cr6, [r0, #-420]!	; 0xfffffe5c
   46560:	2c642520 	cfstr64cs	mvdx2, [r4], #-128	; 0xffffff80
   46564:	746e6920 	strbtvc	r6, [lr], #-2336	; 0xfffff6e0
   46568:	646f6d20 	strbtvs	r6, [pc], #-3360	; 46570 <mLBolusStepsLength+0x148>
   4656c:	203d2065 	eorscs	r2, sp, r5, rrx
   46570:	0a296425 	beq	a9f60c <ringBuffer+0xa47934>
   46574:	20732500 	rsbscs	r2, r3, r0, lsl #10
   46578:	746e6928 	strbtvc	r6, [lr], #-2344	; 0xfffff6d8
   4657c:	6e697020 	cdpvs	0, 6, cr7, cr9, cr0, {1}
   46580:	25203d20 	strcs	r3, [r0, #-3360]!	; 0xfffff2e0
   46584:	000a2964 	andeq	r2, sl, r4, ror #18
   46588:	28207325 	stmdacs	r0!, {r0, r2, r5, r8, r9, ip, sp, lr}
   4658c:	20746e69 	rsbscs	r6, r4, r9, ror #28
   46590:	64756162 	ldrbtvs	r6, [r5], #-354	; 0xfffffe9e
   46594:	25203d20 	strcs	r3, [r0, #-3360]!	; 0xfffff2e0
   46598:	000a2964 	andeq	r2, sl, r4, ror #18
   4659c:	29287325 	stmdbcs	r8!, {r0, r2, r5, r8, r9, ip, sp, lr}
   465a0:	253a6320 	ldrcs	r6, [sl, #-800]!	; 0xfffffce0
   465a4:	25000a63 	strcs	r0, [r0, #-2659]	; 0xfffff59d
   465a8:	63282073 			; <UNDEFINED> instruction: 0x63282073
   465ac:	20726168 	rsbscs	r6, r2, r8, ror #2
   465b0:	74756f2a 	ldrbtvc	r6, [r5], #-3882	; 0xfffff0d6
   465b4:	20747570 	rsbscs	r7, r4, r0, ror r5
   465b8:	7325203d 			; <UNDEFINED> instruction: 0x7325203d
   465bc:	6e69202c 	cdpvs	0, 6, cr2, cr9, cr12, {1}
   465c0:	656c2074 	strbvs	r2, [ip, #-116]!	; 0xffffff8c
   465c4:	203d206e 	eorscs	r2, sp, lr, rrx
   465c8:	0a296425 	beq	a9f664 <ringBuffer+0xa4798c>
   465cc:	61657200 	cmnvs	r5, r0, lsl #4
   465d0:	72662064 	rsbvc	r2, r6, #100	; 0x64
   465d4:	70206d6f 	eorvc	r6, r0, pc, ror #26
   465d8:	25206e69 	strcs	r6, [r0, #-3689]!	; 0xfffff197
   465dc:	25000a64 	strcs	r0, [r0, #-2660]	; 0xfffff59c
   465e0:	25000a73 	strcs	r0, [r0, #-2675]	; 0xfffff58d
   465e4:	4c282073 	stcmi	0, cr2, [r8], #-460	; 0xfffffe34
   465e8:	69757169 	ldmdbvs	r5!, {r0, r3, r5, r6, r8, ip, sp, lr}^
   465ec:	79724364 	ldmdbvc	r2!, {r2, r5, r6, r8, r9, lr}^
   465f0:	6c617473 	cfstrdvs	mvd7, [r1], #-460	; 0xfffffe34
   465f4:	6c202a20 			; <UNDEFINED> instruction: 0x6c202a20
   465f8:	3d206463 	cfstrscc	mvf6, [r0, #-396]!	; 0xfffffe74
   465fc:	25783020 	ldrbcs	r3, [r8, #-32]!	; 0xffffffe0
   46600:	75202c78 	strvc	r2, [r0, #-3192]!	; 0xfffff388
   46604:	6769736e 	strbvs	r7, [r9, -lr, ror #6]!
   46608:	2064656e 	rsbcs	r6, r4, lr, ror #10
   4660c:	20746e69 	rsbscs	r6, r4, r9, ror #28
   46610:	736c6f63 	cmnvc	ip, #396	; 0x18c
   46614:	25203d20 	strcs	r3, [r0, #-3360]!	; 0xfffff2e0
   46618:	75202c75 	strvc	r2, [r0, #-3189]!	; 0xfffff38b
   4661c:	6769736e 	strbvs	r7, [r9, -lr, ror #6]!
   46620:	2064656e 	rsbcs	r6, r4, lr, ror #10
   46624:	20746e69 	rsbscs	r6, r4, r9, ror #28
   46628:	73776f72 	cmnvc	r7, #456	; 0x1c8
   4662c:	25203d20 	strcs	r3, [r0, #-3360]!	; 0xfffff2e0
   46630:	000a2975 	andeq	r2, sl, r5, ror r9
   46634:	28207325 	stmdacs	r0!, {r0, r2, r5, r8, r9, ip, sp, lr}
   46638:	7571694c 	ldrbvc	r6, [r1, #-2380]!	; 0xfffff6b4
   4663c:	72436469 	subvc	r6, r3, #1761607680	; 0x69000000
   46640:	61747379 	cmnvs	r4, r9, ror r3
   46644:	202a206c 	eorcs	r2, sl, ip, rrx
   46648:	2064636c 	rsbcs	r6, r4, ip, ror #6
   4664c:	7830203d 	ldmdavc	r0!, {r0, r2, r3, r4, r5, sp}
   46650:	000a7825 	andeq	r7, sl, r5, lsr #16
   46654:	28207325 	stmdacs	r0!, {r0, r2, r5, r8, r9, ip, sp, lr}
   46658:	7571694c 	ldrbvc	r6, [r1, #-2380]!	; 0xfffff6b4
   4665c:	72436469 	subvc	r6, r3, #1761607680	; 0x69000000
   46660:	61747379 	cmnvs	r4, r9, ror r3
   46664:	202a206c 	eorcs	r2, sl, ip, rrx
   46668:	2064636c 	rsbcs	r6, r4, ip, ror #6
   4666c:	7830203d 	ldmdavc	r0!, {r0, r2, r3, r4, r5, sp}
   46670:	202c7825 	eorcs	r7, ip, r5, lsr #16
   46674:	72616863 	rsbvc	r6, r1, #6488064	; 0x630000
   46678:	756f202a 	strbvc	r2, [pc, #-42]!	; 46656 <mLBolusStepsLength+0x22e>
   4667c:	74757074 	ldrbtvc	r7, [r5], #-116	; 0xffffff8c
   46680:	25203d20 	strcs	r3, [r0, #-3360]!	; 0xfffff2e0
   46684:	69202c73 	stmdbvs	r0!, {r0, r1, r4, r5, r6, sl, fp, sp}
   46688:	6c20746e 	cfstrsvs	mvf7, [r0], #-440	; 0xfffffe48
   4668c:	3d206e65 	stccc	14, cr6, [r0, #-404]!	; 0xfffffe6c
   46690:	29642520 	stmdbcs	r4!, {r5, r8, sl, sp}^
   46694:	7325000a 			; <UNDEFINED> instruction: 0x7325000a
   46698:	694c2820 	stmdbvs	ip, {r5, fp, sp}^
   4669c:	64697571 	strbtvs	r7, [r9], #-1393	; 0xfffffa8f
   466a0:	73797243 	cmnvc	r9, #805306372	; 0x30000004
   466a4:	206c6174 	rsbcs	r6, ip, r4, ror r1
   466a8:	636c202a 	cmnvs	ip, #42	; 0x2a
   466ac:	203d2064 	eorscs	r2, sp, r4, rrx
   466b0:	78257830 	stmdavc	r5!, {r4, r5, fp, ip, sp, lr}
   466b4:	6e69202c 	cdpvs	0, 6, cr2, cr9, cr12, {1}
   466b8:	20782074 	rsbscs	r2, r8, r4, ror r0
   466bc:	6425203d 	strtvs	r2, [r5], #-61	; 0xffffffc3
   466c0:	6e69202c 	cdpvs	0, 6, cr2, cr9, cr12, {1}
   466c4:	20792074 	rsbscs	r2, r9, r4, ror r0
   466c8:	6425203d 	strtvs	r2, [r5], #-61	; 0xffffffc3
   466cc:	0000000a 	andeq	r0, r0, sl

000466d0 <blake2s_IV>:
   466d0:	6a09e667 	bvs	2c0074 <ringBuffer+0x26839c>
   466d4:	bb67ae85 	bllt	1a320f0 <ringBuffer+0x19da418>
   466d8:	3c6ef372 	stclcc	3, cr15, [lr], #-456	; 0xfffffe38
   466dc:	a54ff53a 	strbge	pc, [pc, #-1338]	; 461aa <TEEC_ReleaseSharedMemory+0x34>	; <UNPREDICTABLE>
   466e0:	510e527f 	tstpl	lr, pc, ror r2
   466e4:	9b05688c 	blls	1a091c <ringBuffer+0x148c44>
   466e8:	1f83d9ab 	svcne	0x0083d9ab
   466ec:	5be0cd19 	blpl	ff879b58 <__bss_end__+0xf5f8b584>

000466f0 <blake2s_sigma>:
   466f0:	03020100 	movweq	r0, #8448	; 0x2100
   466f4:	07060504 	streq	r0, [r6, -r4, lsl #10]
   466f8:	0b0a0908 	bleq	2c8b20 <ringBuffer+0x270e48>
   466fc:	0f0e0d0c 	svceq	0x000e0d0c
   46700:	08040a0e 	stmdaeq	r4, {r1, r2, r3, r9, fp}
   46704:	060d0f09 	streq	r0, [sp], -r9, lsl #30
   46708:	02000c01 	andeq	r0, r0, #256	; 0x100
   4670c:	0305070b 	movweq	r0, #22283	; 0x570b
   46710:	000c080b 	andeq	r0, ip, fp, lsl #16
   46714:	0d0f0205 	sfmeq	f0, 4, [pc, #-20]	; 46708 <blake2s_sigma+0x18>
   46718:	06030e0a 	streq	r0, [r3], -sl, lsl #28
   4671c:	04090107 	streq	r0, [r9], #-263	; 0xfffffef9
   46720:	01030907 	tsteq	r3, r7, lsl #18
   46724:	0e0b0c0d 	cdpeq	12, 0, cr0, cr11, cr13, {0}
   46728:	0a050602 	beq	187f38 <ringBuffer+0x130260>
   4672c:	080f0004 	stmdaeq	pc, {r2}	; <UNPREDICTABLE>
   46730:	07050009 	streq	r0, [r5, -r9]
   46734:	0f0a0402 	svceq	0x000a0402
   46738:	0c0b010e 	stfeqs	f0, [fp], {14}
   4673c:	0d030806 	stceq	8, cr0, [r3, #-24]	; 0xffffffe8
   46740:	0a060c02 	beq	1c9750 <ringBuffer+0x171a78>
   46744:	03080b00 	movweq	r0, #35584	; 0x8b00
   46748:	05070d04 	streq	r0, [r7, #-3332]	; 0xfffff2fc
   4674c:	09010e0f 	stmdbeq	r1, {r0, r1, r2, r3, r9, sl, fp}
   46750:	0f01050c 	svceq	0x0001050c
   46754:	0a040d0e 	beq	149b94 <ringBuffer+0xf1ebc>
   46758:	03060700 	movweq	r0, #26368	; 0x6700
   4675c:	0b080209 	bleq	246f88 <ringBuffer+0x1ef2b0>
   46760:	0e070b0d 	vmlaeq.f64	d0, d7, d13
   46764:	0903010c 	stmdbeq	r3, {r2, r3, r8}
   46768:	040f0005 	streq	r0, [pc], #-5	; 46770 <blake2s_sigma+0x80>
   4676c:	0a020608 	beq	c7f94 <ringBuffer+0x702bc>
   46770:	090e0f06 	stmdbeq	lr, {r1, r2, r8, r9, sl, fp}
   46774:	0800030b 	stmdaeq	r0, {r0, r1, r3, r8, r9}
   46778:	070d020c 	streq	r0, [sp, -ip, lsl #4]
   4677c:	050a0401 	streq	r0, [sl, #-1025]	; 0xfffffbff
   46780:	0408020a 	streq	r0, [r8], #-522	; 0xfffffdf6
   46784:	05010607 	streq	r0, [r1, #-1543]	; 0xfffff9f9
   46788:	0e090b0f 	vmlaeq.f64	d0, d9, d15
   4678c:	000d0c03 	andeq	r0, sp, r3, lsl #24
   46790:	66667562 	strbtvs	r7, [r6], -r2, ror #10
   46794:	69207265 	stmdbvs	r0!, {r0, r2, r5, r6, r9, ip, sp, lr}
   46798:	75662073 	strbvc	r2, [r6, #-115]!	; 0xffffff8d
   4679c:	00006c6c 	andeq	r6, r0, ip, ror #24
   467a0:	21212121 			; <UNDEFINED> instruction: 0x21212121
   467a4:	21212121 			; <UNDEFINED> instruction: 0x21212121
   467a8:	21212121 			; <UNDEFINED> instruction: 0x21212121
   467ac:	21212121 			; <UNDEFINED> instruction: 0x21212121
   467b0:	494e4150 	stmdbmi	lr, {r4, r6, r8, lr}^
   467b4:	21212143 			; <UNDEFINED> instruction: 0x21212143
   467b8:	21212121 			; <UNDEFINED> instruction: 0x21212121
   467bc:	21212121 			; <UNDEFINED> instruction: 0x21212121
   467c0:	21212121 			; <UNDEFINED> instruction: 0x21212121
   467c4:	00000021 	andeq	r0, r0, r1, lsr #32
   467c8:	21212121 			; <UNDEFINED> instruction: 0x21212121
   467cc:	21212121 			; <UNDEFINED> instruction: 0x21212121
   467d0:	21212121 			; <UNDEFINED> instruction: 0x21212121
   467d4:	21212121 			; <UNDEFINED> instruction: 0x21212121
   467d8:	5f647766 	svcpl	0x00647766
   467dc:	69646e69 	stmdbvs	r4!, {r0, r3, r5, r6, r9, sl, fp, sp, lr}^
   467e0:	74636572 	strbtvc	r6, [r3], #-1394	; 0xfffffa8e
   467e4:	6673745f 			; <UNDEFINED> instruction: 0x6673745f
   467e8:	726f7720 	rsbvc	r7, pc, #32, 14	; 0x800000
   467ec:	0000736b 	andeq	r7, r0, fp, ror #6
   467f0:	74696e49 	strbtvc	r6, [r9], #-3657	; 0xfffff1b7
   467f4:	696c6169 	stmdbvs	ip!, {r0, r3, r5, r6, r8, sp, lr}^
   467f8:	6120657a 			; <UNDEFINED> instruction: 0x6120657a
   467fc:	6e6f6320 	cdpvs	3, 6, cr6, cr15, cr0, {1}
   46800:	74786574 	ldrbtvc	r6, [r8], #-1396	; 0xfffffa8c
   46804:	6f726620 	svcvs	0x00726620
   46808:	7375206d 	cmnvc	r5, #109	; 0x6d
   4680c:	73207265 			; <UNDEFINED> instruction: 0x73207265
   46810:	65636170 	strbvs	r6, [r3, #-368]!	; 0xfffffe90
   46814:	00000021 	andeq	r0, r0, r1, lsr #32
   46818:	43454554 	movtmi	r4, #21844	; 0x5554
   4681c:	696e495f 	stmdbvs	lr!, {r0, r1, r2, r3, r4, r6, r8, fp, lr}^
   46820:	6c616974 			; <UNDEFINED> instruction: 0x6c616974
   46824:	43657a69 	cmnmi	r5, #430080	; 0x69000
   46828:	65746e6f 	ldrbvs	r6, [r4, #-3695]!	; 0xfffff191
   4682c:	66207478 			; <UNDEFINED> instruction: 0x66207478
   46830:	656c6961 	strbvs	r6, [ip, #-2401]!	; 0xfffff69f
   46834:	69772064 	ldmdbvs	r7!, {r2, r5, r6, sp}^
   46838:	63206874 			; <UNDEFINED> instruction: 0x63206874
   4683c:	2065646f 	rsbcs	r6, r5, pc, ror #8
   46840:	78257830 	stmdavc	r5!, {r4, r5, fp, ip, sp, lr}
   46844:	00000000 	andeq	r0, r0, r0
   46848:	43454554 	movtmi	r4, #21844	; 0x5554
   4684c:	65704f5f 	ldrbvs	r4, [r0, #-3935]!	; 0xfffff0a1
   46850:	7365736e 	cmnvc	r5, #-1207959551	; 0xb8000001
   46854:	6e6f6973 			; <UNDEFINED> instruction: 0x6e6f6973
   46858:	69616620 	stmdbvs	r1!, {r5, r9, sl, sp, lr}^
   4685c:	2064656c 	rsbcs	r6, r4, ip, ror #10
   46860:	68746977 	ldmdavs	r4!, {r0, r1, r2, r4, r5, r6, r8, fp, sp, lr}^
   46864:	646f6320 	strbtvs	r6, [pc], #-800	; 4686c <blake2s_sigma+0x17c>
   46868:	78302065 	ldmdavc	r0!, {r0, r2, r5, r6, sp}
   4686c:	6f207825 	svcvs	0x00207825
   46870:	69676972 	stmdbvs	r7!, {r1, r4, r5, r6, r8, fp, sp, lr}^
   46874:	7830206e 	ldmdavc	r0!, {r1, r2, r3, r5, r6, sp}
   46878:	00007825 	andeq	r7, r0, r5, lsr #16
   4687c:	43454554 	movtmi	r4, #21844	; 0x5554
   46880:	766e495f 			; <UNDEFINED> instruction: 0x766e495f
   46884:	43656b6f 	cmnmi	r5, #113664	; 0x1bc00
   46888:	616d6d6f 	cmnvs	sp, pc, ror #26
   4688c:	6620646e 	strtvs	r6, [r0], -lr, ror #8
   46890:	656c6961 	strbvs	r6, [ip, #-2401]!	; 0xfffff69f
   46894:	69772064 	ldmdbvs	r7!, {r2, r5, r6, sp}^
   46898:	63206874 			; <UNDEFINED> instruction: 0x63206874
   4689c:	2065646f 	rsbcs	r6, r5, pc, ror #8
   468a0:	78257830 	stmdavc	r5!, {r4, r5, fp, ip, sp, lr}
   468a4:	69726f20 	ldmdbvs	r2!, {r5, r8, r9, sl, fp, sp, lr}^
   468a8:	206e6967 	rsbcs	r6, lr, r7, ror #18
   468ac:	78257830 	stmdavc	r5!, {r4, r5, fp, ip, sp, lr}
   468b0:	00000000 	andeq	r0, r0, r0
   468b4:	00000061 	andeq	r0, r0, r1, rrx
   468b8:	25207825 	strcs	r7, [r0, #-2085]!	; 0xfffff7db
   468bc:	00000a78 	andeq	r0, r0, r8, ror sl
   468c0:	6c696146 	stfvse	f6, [r9], #-280	; 0xfffffee8
   468c4:	74206465 	strtvc	r6, [r0], #-1125	; 0xfffffb9b
   468c8:	706f206f 	rsbvc	r2, pc, pc, rrx
   468cc:	74206e65 	strtvc	r6, [r0], #-3685	; 0xfffff19b
   468d0:	66206568 	strtvs	r6, [r0], -r8, ror #10
   468d4:	20656c69 	rsbcs	r6, r5, r9, ror #24
   468d8:	000a7325 	andeq	r7, sl, r5, lsr #6
   468dc:	78323025 	ldmdavc	r2!, {r0, r2, r5, ip, sp}
   468e0:	00000000 	andeq	r0, r0, r0
   468e4:	00000072 	andeq	r0, r0, r2, ror r0
   468e8:	656c6544 	strbvs	r6, [ip, #-1348]!	; 0xfffffabc
   468ec:	20646574 	rsbcs	r6, r4, r4, ror r5
   468f0:	63637573 	cmnvs	r3, #482344960	; 0x1cc00000
   468f4:	66737365 	ldrbtvs	r7, [r3], -r5, ror #6
   468f8:	796c6c75 	stmdbvc	ip!, {r0, r2, r4, r5, r6, sl, fp, sp, lr}^
   468fc:	65687420 	strbvs	r7, [r8, #-1056]!	; 0xfffffbe0
   46900:	6c696620 	stclvs	6, cr6, [r9], #-128	; 0xffffff80
   46904:	73252065 			; <UNDEFINED> instruction: 0x73252065
   46908:	0000000a 	andeq	r0, r0, sl
   4690c:	62616e55 	rsbvs	r6, r1, #1360	; 0x550
   46910:	7420656c 	strtvc	r6, [r0], #-1388	; 0xfffffa94
   46914:	6564206f 	strbvs	r2, [r4, #-111]!	; 0xffffff91
   46918:	6574656c 	ldrbvs	r6, [r4, #-1388]!	; 0xfffffa94
   4691c:	65687420 	strbvs	r7, [r8, #-1056]!	; 0xfffffbe0
   46920:	6c696620 	stclvs	6, cr6, [r9], #-128	; 0xffffff80
   46924:	73252065 			; <UNDEFINED> instruction: 0x73252065
   46928:	0000000a 	andeq	r0, r0, sl
   4692c:	00000077 	andeq	r0, r0, r7, ror r0
   46930:	63637553 	cmnvs	r3, #348127232	; 0x14c00000
   46934:	66737365 	ldrbtvs	r7, [r3], -r5, ror #6
   46938:	796c6c75 	stmdbvc	ip!, {r0, r2, r4, r5, r6, sl, fp, sp, lr}^
   4693c:	65726320 	ldrbvs	r6, [r2, #-800]!	; 0xfffffce0
   46940:	64657461 	strbtvs	r7, [r5], #-1121	; 0xfffffb9f
   46944:	65687420 	strbvs	r7, [r8, #-1056]!	; 0xfffffbe0
   46948:	6c696620 	stclvs	6, cr6, [r9], #-128	; 0xffffff80
   4694c:	73252065 			; <UNDEFINED> instruction: 0x73252065
   46950:	0000000a 	andeq	r0, r0, sl
   46954:	6c696146 	stfvse	f6, [r9], #-280	; 0xfffffee8
   46958:	74206465 	strtvc	r6, [r0], #-1125	; 0xfffffb9b
   4695c:	7263206f 	rsbvc	r2, r3, #111	; 0x6f
   46960:	65746165 	ldrbvs	r6, [r4, #-357]!	; 0xfffffe9b
   46964:	65687420 	strbvs	r7, [r8, #-1056]!	; 0xfffffbe0
   46968:	6c696620 	stclvs	6, cr6, [r9], #-128	; 0xffffff80
   4696c:	73252065 			; <UNDEFINED> instruction: 0x73252065
   46970:	0000000a 	andeq	r0, r0, sl
   46974:	52412f2e 	subpl	r2, r1, #46, 30	; 0xb8
   46978:	6e695f49 	cdpvs	15, 6, cr5, cr9, cr9, {2}
   4697c:	6d6a5f64 	stclvs	15, cr5, [sl, #-400]!	; 0xfffffe70
   46980:	78742e70 	ldmdavc	r4!, {r4, r5, r6, r9, sl, fp, sp}^
   46984:	00000074 	andeq	r0, r0, r4, ror r0
   46988:	6c696146 	stfvse	f6, [r9], #-280	; 0xfffffee8
   4698c:	74206465 	strtvc	r6, [r0], #-1125	; 0xfffffb9b
   46990:	6e69206f 	cdpvs	0, 6, cr2, cr9, cr15, {3}
   46994:	6c617469 	cfstrdvs	mvd7, [r1], #-420	; 0xfffffe5c
   46998:	65617a69 	strbvs	r7, [r1, #-2665]!	; 0xfffff597
   4699c:	414c4220 	cmpmi	ip, r0, lsr #4
   469a0:	7332454b 	teqvc	r2, #314572800	; 0x12c00000
   469a4:	00000000 	andeq	r0, r0, r0
   469a8:	6c696146 	stfvse	f6, [r9], #-280	; 0xfffffee8
   469ac:	74206465 	strtvc	r6, [r0], #-1125	; 0xfffffb9b
   469b0:	7075206f 	rsbsvc	r2, r5, pc, rrx
   469b4:	65746164 	ldrbvs	r6, [r4, #-356]!	; 0xfffffe9c
   469b8:	414c4220 	cmpmi	ip, r0, lsr #4
   469bc:	7332454b 	teqvc	r2, #314572800	; 0x12c00000
   469c0:	73616820 	cmnvc	r1, #32, 16	; 0x200000
   469c4:	00000a68 	andeq	r0, r0, r8, ror #20
   469c8:	75746572 	ldrbvc	r6, [r4, #-1394]!	; 0xfffffa8e
   469cc:	75206e72 	strvc	r6, [r0, #-3698]!	; 0xfffff18e
   469d0:	74616470 	strbtvc	r6, [r1], #-1136	; 0xfffffb90
   469d4:	30203a65 	eorcc	r3, r0, r5, ror #20
   469d8:	0a782578 	beq	1e4ffc0 <ringBuffer+0x1df82e8>
   469dc:	00000000 	andeq	r0, r0, r0
   469e0:	52412f2e 	subpl	r2, r1, #46, 30	; 0xb8
   469e4:	72625f49 	rsbvc	r5, r2, #292	; 0x124
   469e8:	68636e61 	stmdavs	r3!, {r0, r5, r6, r9, sl, fp, sp, lr}^
   469ec:	7478742e 	ldrbtvc	r7, [r8], #-1070	; 0xfffffbd2
   469f0:	00000000 	andeq	r0, r0, r0
   469f4:	52412f2e 	subpl	r2, r1, #46, 30	; 0xb8
   469f8:	73745f49 	cmnvc	r4, #292	; 0x124
   469fc:	78742e66 	ldmdavc	r4!, {r1, r2, r5, r6, r9, sl, fp, sp}^
   46a00:	00000074 	andeq	r0, r0, r4, ror r0
   46a04:	6c696146 	stfvse	f6, [r9], #-280	; 0xfffffee8
   46a08:	74206465 	strtvc	r6, [r0], #-1125	; 0xfffffb9b
   46a0c:	6966206f 	stmdbvs	r6!, {r0, r1, r2, r3, r5, r6, sp}^
   46a10:	696c616e 	stmdbvs	ip!, {r1, r2, r3, r5, r6, r8, sp, lr}^
   46a14:	2064657a 	rsbcs	r6, r4, sl, ror r5
   46a18:	4b414c42 	blmi	1099b28 <ringBuffer+0x1041e50>
   46a1c:	20733245 	rsbscs	r3, r3, r5, asr #4
   46a20:	68736168 	ldmdavs	r3!, {r3, r5, r6, r8, sp, lr}^
   46a24:	00000000 	andeq	r0, r0, r0
   46a28:	52412f2e 	subpl	r2, r1, #46, 30	; 0xb8
   46a2c:	65725f49 	ldrbvs	r5, [r2, #-3913]!	; 0xfffff0b7
   46a30:	61685f74 	smcvs	34292	; 0x85f4
   46a34:	742e6873 	strtvc	r6, [lr], #-2163	; 0xfffff78d
   46a38:	00007478 	andeq	r7, r0, r8, ror r4
   46a3c:	000a7825 	andeq	r7, sl, r5, lsr #16
   46a40:	00006277 	andeq	r6, r0, r7, ror r2
   46a44:	43454554 	movtmi	r4, #21844	; 0x5554
   46a48:	00000000 	andeq	r0, r0, r0
   46a4c:	5f454554 	svcpl	0x00454554
   46a50:	5f434f49 	svcpl	0x00434f49
   46a54:	53524556 	cmppl	r2, #360710144	; 0x15800000
   46a58:	204e4f49 	subcs	r4, lr, r9, asr #30
   46a5c:	6c696166 	stfvse	f6, [r9], #-408	; 0xfffffe68
   46a60:	000a6465 	andeq	r6, sl, r5, ror #8
   46a64:	6574706f 	ldrbvs	r7, [r4, #-111]!	; 0xffffff91
   46a68:	7a742d65 	bvc	1d52004 <ringBuffer+0x1cfa32c>
   46a6c:	00000000 	andeq	r0, r0, r0
   46a70:	7665642f 	strbtvc	r6, [r5], -pc, lsr #8
   46a74:	6565742f 	strbvs	r7, [r5, #-1071]!	; 0xfffffbd1
   46a78:	00757a25 	rsbseq	r7, r5, r5, lsr #20
   46a7c:	5f454554 	svcpl	0x00454554
   46a80:	5f434f49 	svcpl	0x00434f49
   46a84:	4e45504f 	cdpmi	0, 4, cr5, cr5, cr15, {2}
   46a88:	5345535f 	movtpl	r5, #21343	; 0x535f
   46a8c:	4e4f4953 			; <UNDEFINED> instruction: 0x4e4f4953
   46a90:	69616620 	stmdbvs	r1!, {r5, r9, sl, sp, lr}^
   46a94:	0a64656c 	beq	196004c <ringBuffer+0x1908374>
   46a98:	00000000 	andeq	r0, r0, r0
   46a9c:	6c696146 	stfvse	f6, [r9], #-280	; 0xfffffee8
   46aa0:	74206465 	strtvc	r6, [r0], #-1125	; 0xfffffb9b
   46aa4:	6c63206f 	stclvs	0, cr2, [r3], #-444	; 0xfffffe44
   46aa8:	2065736f 	rsbcs	r7, r5, pc, ror #6
   46aac:	73736573 	cmnvc	r3, #482344960	; 0x1cc00000
   46ab0:	206e6f69 	rsbcs	r6, lr, r9, ror #30
   46ab4:	78257830 	stmdavc	r5!, {r4, r5, fp, ip, sp, lr}
   46ab8:	0000000a 	andeq	r0, r0, sl
   46abc:	5f454554 	svcpl	0x00454554
   46ac0:	5f434f49 	svcpl	0x00434f49
   46ac4:	4f564e49 	svcmi	0x00564e49
   46ac8:	6620454b 	strtvs	r4, [r0], -fp, asr #10
   46acc:	656c6961 	strbvs	r6, [ip, #-2401]!	; 0xfffff69f
   46ad0:	00000a64 	andeq	r0, r0, r4, ror #20
   46ad4:	5f454554 	svcpl	0x00454554
   46ad8:	5f434f49 	svcpl	0x00434f49
   46adc:	434e4143 	movtmi	r4, #57667	; 0xe143
   46ae0:	203a4c45 	eorscs	r4, sl, r5, asr #24
   46ae4:	000a7325 	andeq	r7, sl, r5, lsr #6

00046ae8 <__func__.8646>:
   46ae8:	63656574 	cmnvs	r5, #116, 10	; 0x1d000000
   46aec:	65706f5f 	ldrbvs	r6, [r0, #-3935]!	; 0xfffff0a1
   46af0:	65645f6e 	strbvs	r5, [r4, #-3950]!	; 0xfffff092
   46af4:	00000076 	andeq	r0, r0, r6, ror r0

00046af8 <__func__.8814>:
   46af8:	43454554 	movtmi	r4, #21844	; 0x5554
   46afc:	65704f5f 	ldrbvs	r4, [r0, #-3935]!	; 0xfffff0a1
   46b00:	7365536e 	cmnvc	r5, #-1207959551	; 0xb8000001
   46b04:	6e6f6973 			; <UNDEFINED> instruction: 0x6e6f6973
   46b08:	00000000 	andeq	r0, r0, r0

00046b0c <__func__.8819>:
   46b0c:	43454554 	movtmi	r4, #21844	; 0x5554
   46b10:	6f6c435f 	svcvs	0x006c435f
   46b14:	65536573 	ldrbvs	r6, [r3, #-1395]	; 0xfffffa8d
   46b18:	6f697373 	svcvs	0x00697373
   46b1c:	0000006e 	andeq	r0, r0, lr, rrx

00046b20 <__func__.8836>:
   46b20:	43454554 	movtmi	r4, #21844	; 0x5554
   46b24:	766e495f 			; <UNDEFINED> instruction: 0x766e495f
   46b28:	43656b6f 	cmnmi	r5, #113664	; 0x1bc00
   46b2c:	616d6d6f 	cmnvs	sp, pc, ror #26
   46b30:	0000646e 	andeq	r6, r0, lr, ror #8

00046b34 <__func__.8842>:
   46b34:	43454554 	movtmi	r4, #21844	; 0x5554
   46b38:	7165525f 	cmnvc	r5, pc, asr r2
   46b3c:	74736575 	ldrbtvc	r6, [r3], #-1397	; 0xfffffa8b
   46b40:	636e6143 	cmnvs	lr, #-1073741808	; 0xc0000010
   46b44:	616c6c65 	cmnvs	ip, r5, ror #24
   46b48:	6e6f6974 			; <UNDEFINED> instruction: 0x6e6f6974
	...
   46b54:	00525245 	subseq	r5, r2, r5, asr #4
   46b58:	00464e49 	subeq	r4, r6, r9, asr #28
   46b5c:	00474244 	subeq	r4, r7, r4, asr #4
   46b60:	00574c46 	subseq	r4, r7, r6, asr #24
   46b64:	5b207325 	blpl	863800 <ringBuffer+0x80bb28>
   46b68:	205d6425 	subscs	r6, sp, r5, lsr #8
   46b6c:	253a7325 	ldrcs	r7, [sl, #-805]!	; 0xfffffcdb
   46b70:	64253a73 	strtvs	r3, [r5], #-2675	; 0xfffff58d
   46b74:	地址 0x0000000000046b74 越界。


Disassembly of section .AMI_SFI_Metadata:

00046b77 <.cpt_tb>:
   46b77:	00000000 	andeq	r0, r0, r0
   46b7b:	ffffffff 			; <UNDEFINED> instruction: 0xffffffff
   46b7f:	00000000 	andeq	r0, r0, r0
   46b83:	ffffffff 			; <UNDEFINED> instruction: 0xffffffff
   46b87:	00000000 	andeq	r0, r0, r0
   46b8b:	ffffffff 			; <UNDEFINED> instruction: 0xffffffff
   46b8f:	00000000 	andeq	r0, r0, r0
   46b93:	ffffffff 			; <UNDEFINED> instruction: 0xffffffff

00046b97 <.cpt_direct_transfer_tb>:
   46b97:	00000000 	andeq	r0, r0, r0
   46b9b:	00000004 	andeq	r0, r0, r4
   46b9f:	00000020 	andeq	r0, r0, r0, lsr #32
   46ba3:	00000004 	andeq	r0, r0, r4
   46ba7:	00000040 	andeq	r0, r0, r0, asr #32
   46bab:	00000004 	andeq	r0, r0, r4
	...
   46bb7:	00000001 	andeq	r0, r0, r1
   46bbb:	00000000 	andeq	r0, r0, r0
   46bbf:	00000002 	andeq	r0, r0, r2
   46bc3:	00000000 	andeq	r0, r0, r0
   46bc7:	00000003 	andeq	r0, r0, r3
   46bcb:	00000000 	andeq	r0, r0, r0

00046bcf <.cpt_indirect_transfer_tb>:
   46bcf:	00000000 	andeq	r0, r0, r0
   46bd3:	00000004 	andeq	r0, r0, r4
   46bd7:	00000020 	andeq	r0, r0, r0, lsr #32
   46bdb:	00000004 	andeq	r0, r0, r4
   46bdf:	00000040 	andeq	r0, r0, r0, asr #32
   46be3:	00000004 	andeq	r0, r0, r4
	...
   46bef:	00000001 	andeq	r0, r0, r1
   46bf3:	00000000 	andeq	r0, r0, r0
   46bf7:	00000002 	andeq	r0, r0, r2
   46bfb:	00000000 	andeq	r0, r0, r0
   46bff:	00000003 	andeq	r0, r0, r3
   46c03:	00000000 	andeq	r0, r0, r0

00046c07 <.cpt_dt_wt_access_tb>:
   46c07:	00000000 	andeq	r0, r0, r0
   46c0b:	00000004 	andeq	r0, r0, r4
   46c0f:	00000020 	andeq	r0, r0, r0, lsr #32
   46c13:	00000004 	andeq	r0, r0, r4
   46c17:	00000040 	andeq	r0, r0, r0, asr #32
   46c1b:	00000004 	andeq	r0, r0, r4
   46c1f:	00000000 	andeq	r0, r0, r0
   46c23:	ffffffff 			; <UNDEFINED> instruction: 0xffffffff
   46c27:	00000001 	andeq	r0, r0, r1
   46c2b:	ffffffff 			; <UNDEFINED> instruction: 0xffffffff
   46c2f:	00000002 	andeq	r0, r0, r2
   46c33:	ffffffff 			; <UNDEFINED> instruction: 0xffffffff
   46c37:	00000003 	andeq	r0, r0, r3
   46c3b:	ffffffff 			; <UNDEFINED> instruction: 0xffffffff

Disassembly of section .ARM.exidx:

00046c40 <.ARM.exidx>:
   46c40:	7ffd93c0 	svcvc	0x00fd93c0
   46c44:	00000001 	andeq	r0, r0, r1

Disassembly of section .data.rel.ro:

00056f2c <trace_level_strings>:
   56f2c:	00046b50 	andeq	r6, r4, r0, asr fp
   56f30:	00046b54 	andeq	r6, r4, r4, asr fp
   56f34:	00046b58 	andeq	r6, r4, r8, asr fp
   56f38:	00046b5c 	andeq	r6, r4, ip, asr fp
   56f3c:	00046b60 	andeq	r6, r4, r0, ror #22

Disassembly of section .dynamic:

00056f40 <_DYNAMIC>:
   56f40:	00000001 	andeq	r0, r0, r1
   56f44:	00000001 	andeq	r0, r0, r1
   56f48:	00000001 	andeq	r0, r0, r1
   56f4c:	00000080 	andeq	r0, r0, r0, lsl #1
   56f50:	6ffffef5 	svcvs	0x00fffef5
   56f54:	00010130 	andeq	r0, r1, r0, lsr r1
   56f58:	00000005 	andeq	r0, r0, r5
   56f5c:	000105c0 	andeq	r0, r1, r0, asr #11
   56f60:	00000006 	andeq	r0, r0, r6
   56f64:	000102b0 			; <UNDEFINED> instruction: 0x000102b0
   56f68:	0000000a 	andeq	r0, r0, sl
   56f6c:	000001bf 			; <UNDEFINED> instruction: 0x000001bf
   56f70:	0000000b 	andeq	r0, r0, fp
   56f74:	00000010 	andeq	r0, r0, r0, lsl r0
   56f78:	00000015 	andeq	r0, r0, r5, lsl r0
   56f7c:	00000000 	andeq	r0, r0, r0
   56f80:	00000003 	andeq	r0, r0, r3
   56f84:	00057000 	andeq	r7, r5, r0
   56f88:	00000002 	andeq	r0, r0, r2
   56f8c:	00000100 	andeq	r0, r0, r0, lsl #2
   56f90:	00000014 	andeq	r0, r0, r4, lsl r0
   56f94:	00000011 	andeq	r0, r0, r1, lsl r0
   56f98:	00000017 	andeq	r0, r0, r7, lsl r0
   56f9c:	0001081c 	andeq	r0, r1, ip, lsl r8
   56fa0:	00000011 	andeq	r0, r0, r1, lsl r0
   56fa4:	00010814 	andeq	r0, r1, r4, lsl r8
   56fa8:	00000012 	andeq	r0, r0, r2, lsl r0
   56fac:	00000008 	andeq	r0, r0, r8
   56fb0:	00000013 	andeq	r0, r0, r3, lsl r0
   56fb4:	00000008 	andeq	r0, r0, r8
   56fb8:	6ffffffe 	svcvs	0x00fffffe
   56fbc:	000107e4 	andeq	r0, r1, r4, ror #15
   56fc0:	6fffffff 	svcvs	0x00ffffff
   56fc4:	00000001 	andeq	r0, r0, r1
   56fc8:	6ffffff0 	svcvs	0x00fffff0
   56fcc:	00010780 	andeq	r0, r1, r0, lsl #15
	...

Disassembly of section .got:

00057000 <_GLOBAL_OFFSET_TABLE_>:
   57000:	00056f40 	andeq	r6, r5, r0, asr #30
	...
   5700c:	0001091c 	andeq	r0, r1, ip, lsl r9
   57010:	0001091c 	andeq	r0, r1, ip, lsl r9
   57014:	0001091c 	andeq	r0, r1, ip, lsl r9
   57018:	0001091c 	andeq	r0, r1, ip, lsl r9
   5701c:	0001091c 	andeq	r0, r1, ip, lsl r9
   57020:	0001091c 	andeq	r0, r1, ip, lsl r9
   57024:	0001091c 	andeq	r0, r1, ip, lsl r9
   57028:	0001091c 	andeq	r0, r1, ip, lsl r9
   5702c:	0001091c 	andeq	r0, r1, ip, lsl r9
   57030:	0001091c 	andeq	r0, r1, ip, lsl r9
   57034:	0001091c 	andeq	r0, r1, ip, lsl r9
   57038:	0001091c 	andeq	r0, r1, ip, lsl r9
   5703c:	0001091c 	andeq	r0, r1, ip, lsl r9
   57040:	0001091c 	andeq	r0, r1, ip, lsl r9
   57044:	0001091c 	andeq	r0, r1, ip, lsl r9
   57048:	0001091c 	andeq	r0, r1, ip, lsl r9
   5704c:	0001091c 	andeq	r0, r1, ip, lsl r9
   57050:	0001091c 	andeq	r0, r1, ip, lsl r9
   57054:	0001091c 	andeq	r0, r1, ip, lsl r9
   57058:	0001091c 	andeq	r0, r1, ip, lsl r9
   5705c:	0001091c 	andeq	r0, r1, ip, lsl r9
   57060:	0001091c 	andeq	r0, r1, ip, lsl r9
   57064:	0001091c 	andeq	r0, r1, ip, lsl r9
   57068:	0001091c 	andeq	r0, r1, ip, lsl r9
   5706c:	0001091c 	andeq	r0, r1, ip, lsl r9
   57070:	0001091c 	andeq	r0, r1, ip, lsl r9
   57074:	0001091c 	andeq	r0, r1, ip, lsl r9
   57078:	0001091c 	andeq	r0, r1, ip, lsl r9
   5707c:	0001091c 	andeq	r0, r1, ip, lsl r9
   57080:	0001091c 	andeq	r0, r1, ip, lsl r9
   57084:	0001091c 	andeq	r0, r1, ip, lsl r9
   57088:	0001091c 	andeq	r0, r1, ip, lsl r9
   5708c:	00057c98 	muleq	r5, r8, ip
   57090:	098ee4e4 	stmibeq	lr, {r2, r5, r6, r7, sl, sp, lr, pc}
   57094:	00057c90 	muleq	r5, r0, ip
   57098:	098ee4ec 	stmibeq	lr, {r2, r3, r5, r6, r7, sl, sp, lr, pc}
   5709c:	00057c9c 	muleq	r5, ip, ip
   570a0:	098ee568 	stmibeq	lr, {r3, r5, r6, r8, sl, sp, lr, pc}
   570a4:	098ee588 	stmibeq	lr, {r3, r7, r8, sl, sp, lr, pc}
   570a8:	00057ca4 	andeq	r7, r5, r4, lsr #25
   570ac:	00057cd8 	ldrdeq	r7, [r5], -r8
   570b0:	098ee58c 	stmibeq	lr, {r2, r3, r7, r8, sl, sp, lr, pc}
   570b4:	000207fc 	strdeq	r0, [r2], -ip
   570b8:	00000000 	andeq	r0, r0, r0
   570bc:	098ee594 	stmibeq	lr, {r2, r4, r7, r8, sl, sp, lr, pc}
   570c0:	098ee598 	stmibeq	lr, {r3, r4, r7, r8, sl, sp, lr, pc}
   570c4:	000570d4 	ldrdeq	r7, [r5], -r4
   570c8:	00057ca0 	andeq	r7, r5, r0, lsr #25

Disassembly of section .data:

000570cc <ustepsPerMM>:
   570cc:	00000a00 	andeq	r0, r0, r0, lsl #20

000570d0 <memset_v.6351>:
   570d0:	00010a20 	andeq	r0, r1, r0, lsr #20

000570d4 <uuid>:
   570d4:	d96a5b40 	stmdble	sl!, {r6, r8, r9, fp, ip, lr}^
   570d8:	21e3c3e5 	mvncs	ip, r5, ror #7
   570dc:	02109487 	andseq	r9, r0, #-2030043136	; 0x87000000
   570e0:	1bc6d5a5 	blne	ff20c77c <__bss_end__+0xf591e1a8>

Disassembly of section .DATA_REGION_0__bss:

000570e4 <uiState>:
   570e4:	00000000 	andeq	r0, r0, r0

000570e8 <serialStr>:
	...

Disassembly of section .trampoline_fw:

00057138 <__trampoline_fw_blx>:
   57138:	e24dd00c 	sub	sp, sp, #12
   5713c:	e58d0000 	str	r0, [sp]
   57140:	e58d1004 	str	r1, [sp, #4]
   57144:	e10f0000 	mrs	r0, CPSR
   57148:	e58d0008 	str	r0, [sp, #8]
   5714c:	e59f0970 	ldr	r0, [pc, #2416]	; 57ac4 <.curr_cpt_id>
   57150:	e3a01004 	mov	r1, #4
   57154:	e0000190 	mul	r0, r0, r1
   57158:	e59f1b00 	ldr	r1, [pc, #2816]	; 57c60 <.cpt_stack+0x190>
   5715c:	e0811000 	add	r1, r1, r0
   57160:	e5911000 	ldr	r1, [r1]
   57164:	e1580001 	cmp	r8, r1
   57168:	3a000062 	bcc	572f8 <__error>
   5716c:	e2800004 	add	r0, r0, #4
   57170:	e59f1ae8 	ldr	r1, [pc, #2792]	; 57c60 <.cpt_stack+0x190>
   57174:	e0811000 	add	r1, r1, r0
   57178:	e5911000 	ldr	r1, [r1]
   5717c:	e1510008 	cmp	r1, r8
   57180:	3a00005c 	bcc	572f8 <__error>
   57184:	e59d0008 	ldr	r0, [sp, #8]
   57188:	e128f000 	msr	CPSR_f, r0
   5718c:	e59d0000 	ldr	r0, [sp]
   57190:	e59d1004 	ldr	r1, [sp, #4]
   57194:	e28dd00c 	add	sp, sp, #12
   57198:	e12fff18 	bx	r8

0005719c <__trampoline_fw_bx>:
   5719c:	e24dd00c 	sub	sp, sp, #12
   571a0:	e58d0000 	str	r0, [sp]
   571a4:	e58d1004 	str	r1, [sp, #4]
   571a8:	e10f0000 	mrs	r0, CPSR
   571ac:	e58d0008 	str	r0, [sp, #8]
   571b0:	e59f090c 	ldr	r0, [pc, #2316]	; 57ac4 <.curr_cpt_id>
   571b4:	e3a01004 	mov	r1, #4
   571b8:	e0000190 	mul	r0, r0, r1
   571bc:	e59f1a9c 	ldr	r1, [pc, #2716]	; 57c60 <.cpt_stack+0x190>
   571c0:	e0811000 	add	r1, r1, r0
   571c4:	e5911000 	ldr	r1, [r1]
   571c8:	e1580001 	cmp	r8, r1
   571cc:	3a000049 	bcc	572f8 <__error>
   571d0:	e2800004 	add	r0, r0, #4
   571d4:	e59f1a84 	ldr	r1, [pc, #2692]	; 57c60 <.cpt_stack+0x190>
   571d8:	e0811000 	add	r1, r1, r0
   571dc:	e5911000 	ldr	r1, [r1]
   571e0:	e1510008 	cmp	r1, r8
   571e4:	3a000043 	bcc	572f8 <__error>
   571e8:	e59d0008 	ldr	r0, [sp, #8]
   571ec:	e128f000 	msr	CPSR_f, r0
   571f0:	e59d0000 	ldr	r0, [sp]
   571f4:	e59d1004 	ldr	r1, [sp, #4]
   571f8:	e28dd00c 	add	sp, sp, #12
   571fc:	e12fff18 	bx	r8

00057200 <__trampoline_bkwd_bx_t>:
   57200:	e24dd00c 	sub	sp, sp, #12
   57204:	e58d0000 	str	r0, [sp]
   57208:	e58d1004 	str	r1, [sp, #4]
   5720c:	e10f0000 	mrs	r0, CPSR
   57210:	e58d0008 	str	r0, [sp, #8]
   57214:	e59f08a8 	ldr	r0, [pc, #2216]	; 57ac4 <.curr_cpt_id>
   57218:	e3a01004 	mov	r1, #4
   5721c:	e0000190 	mul	r0, r0, r1
   57220:	e59f1a38 	ldr	r1, [pc, #2616]	; 57c60 <.cpt_stack+0x190>
   57224:	e0811000 	add	r1, r1, r0
   57228:	e5911000 	ldr	r1, [r1]
   5722c:	e1580001 	cmp	r8, r1
   57230:	3a000030 	bcc	572f8 <__error>
   57234:	e2800004 	add	r0, r0, #4
   57238:	e59f1a20 	ldr	r1, [pc, #2592]	; 57c60 <.cpt_stack+0x190>
   5723c:	e0811000 	add	r1, r1, r0
   57240:	e5911000 	ldr	r1, [r1]
   57244:	e1510008 	cmp	r1, r8
   57248:	3a00002a 	bcc	572f8 <__error>
   5724c:	e59d0008 	ldr	r0, [sp, #8]
   57250:	e128f000 	msr	CPSR_f, r0
   57254:	e59d0000 	ldr	r0, [sp]
   57258:	e59d1004 	ldr	r1, [sp, #4]
   5725c:	e28dd00c 	add	sp, sp, #12
   57260:	e1a0e008 	mov	lr, r8
   57264:	e12fff18 	bx	r8

00057268 <__trampoline_bkwd_bx>:
   57268:	e1a0e008 	mov	lr, r8
   5726c:	e12fff18 	bx	r8

00057270 <__trampoline_bkwd_pop>:
   57270:	e59d8000 	ldr	r8, [sp]
   57274:	e1a0e008 	mov	lr, r8
   57278:	e59d8004 	ldr	r8, [sp, #4]
   5727c:	e24dd00c 	sub	sp, sp, #12
   57280:	e58d0000 	str	r0, [sp]
   57284:	e58d1004 	str	r1, [sp, #4]
   57288:	e10f0000 	mrs	r0, CPSR
   5728c:	e58d0008 	str	r0, [sp, #8]
   57290:	e59f082c 	ldr	r0, [pc, #2092]	; 57ac4 <.curr_cpt_id>
   57294:	e3a01004 	mov	r1, #4
   57298:	e0000190 	mul	r0, r0, r1
   5729c:	e59f19bc 	ldr	r1, [pc, #2492]	; 57c60 <.cpt_stack+0x190>
   572a0:	e0811000 	add	r1, r1, r0
   572a4:	e5911000 	ldr	r1, [r1]
   572a8:	e1580001 	cmp	r8, r1
   572ac:	3a000011 	bcc	572f8 <__error>
   572b0:	e2800004 	add	r0, r0, #4
   572b4:	e59f19a4 	ldr	r1, [pc, #2468]	; 57c60 <.cpt_stack+0x190>
   572b8:	e0811000 	add	r1, r1, r0
   572bc:	e5911000 	ldr	r1, [r1]
   572c0:	e1510008 	cmp	r1, r8
   572c4:	3a00000b 	bcc	572f8 <__error>
   572c8:	e59d0008 	ldr	r0, [sp, #8]
   572cc:	e128f000 	msr	CPSR_f, r0
   572d0:	e59d0000 	ldr	r0, [sp]
   572d4:	e59d1004 	ldr	r1, [sp, #4]
   572d8:	e28dd014 	add	sp, sp, #20
   572dc:	e12fff18 	bx	r8

000572e0 <__AMI_fake_direct_transfer>:
   572e0:	e320f000 	nop	{0}

000572e4 <__AMI_fake_indirect_transfer>:
   572e4:	e320f000 	nop	{0}

000572e8 <__AMI_fake_rt_transfer>:
   572e8:	e320f000 	nop	{0}

000572ec <__AMI_fake_local_wrt>:
   572ec:	e320f000 	nop	{0}

000572f0 <__AMI_fake_shared_wrt>:
   572f0:	e320f000 	nop	{0}

000572f4 <__AMI_fake_pop_pc_transfer>:
   572f4:	e320f000 	nop	{0}

000572f8 <__error>:
   572f8:	ea000260 	b	57c80 <__error_found_from_arm>

000572fc <__tsf_direct_jmp_link_checking>:
   572fc:	e24dd014 	sub	sp, sp, #20
   57300:	e58d0000 	str	r0, [sp]
   57304:	e58d1004 	str	r1, [sp, #4]
   57308:	e58d2008 	str	r2, [sp, #8]
   5730c:	e58d300c 	str	r3, [sp, #12]
   57310:	e10f0000 	mrs	r0, CPSR
   57314:	e58d0010 	str	r0, [sp, #16]
   57318:	e59f07a4 	ldr	r0, [pc, #1956]	; 57ac4 <.curr_cpt_id>
   5731c:	e3a01008 	mov	r1, #8
   57320:	e0010190 	mul	r1, r0, r1
   57324:	e59f2938 	ldr	r2, [pc, #2360]	; 57c64 <.cpt_stack+0x194>
   57328:	e0811002 	add	r1, r1, r2
   5732c:	e59f0794 	ldr	r0, [pc, #1940]	; 57ac8 <.total_cpt_cnt>
   57330:	e3a02008 	mov	r2, #8
   57334:	e0000290 	mul	r0, r0, r2
   57338:	e59f2924 	ldr	r2, [pc, #2340]	; 57c64 <.cpt_stack+0x194>
   5733c:	e0820000 	add	r0, r2, r0
   57340:	e5912000 	ldr	r2, [r1]
   57344:	e0822000 	add	r2, r2, r0
   57348:	e5911004 	ldr	r1, [r1, #4]
   5734c:	e3a03000 	mov	r3, #0

00057350 <direct_link_cpt_ck_loop>:
   57350:	e1530001 	cmp	r3, r1
   57354:	aa000007 	bge	57378 <direct_link_cpt_ck_fail>
   57358:	e3a00008 	mov	r0, #8
   5735c:	e0000093 	mul	r0, r3, r0
   57360:	e0800002 	add	r0, r0, r2
   57364:	e5900000 	ldr	r0, [r0]
   57368:	e1580000 	cmp	r8, r0
   5736c:	0a000003 	beq	57380 <direct_link_cpt_ck_pass>
   57370:	e2833001 	add	r3, r3, #1
   57374:	eafffff5 	b	57350 <direct_link_cpt_ck_loop>

00057378 <direct_link_cpt_ck_fail>:
   57378:	ea000000 	b	57380 <direct_link_cpt_ck_pass>
   5737c:	eaffffdd 	b	572f8 <__error>

00057380 <direct_link_cpt_ck_pass>:
   57380:	e3a00008 	mov	r0, #8
   57384:	e2433001 	sub	r3, r3, #1
   57388:	e0000093 	mul	r0, r3, r0
   5738c:	e0800002 	add	r0, r0, r2
   57390:	e5900004 	ldr	r0, [r0, #4]
   57394:	e59f18cc 	ldr	r1, [pc, #2252]	; 57c68 <.cpt_stack+0x198>
   57398:	e5810000 	str	r0, [r1]
   5739c:	e59f08c8 	ldr	r0, [pc, #2248]	; 57c6c <.cpt_stack+0x19c>
   573a0:	e59f1724 	ldr	r1, [pc, #1828]	; 57acc <.curr_cpt_stack_pointer_offset>
   573a4:	e0800001 	add	r0, r0, r1
   573a8:	e2811008 	add	r1, r1, #8
   573ac:	e58f1718 	str	r1, [pc, #1816]	; 57acc <.curr_cpt_stack_pointer_offset>
   573b0:	e59f170c 	ldr	r1, [pc, #1804]	; 57ac4 <.curr_cpt_id>
   573b4:	e5801000 	str	r1, [r0]
   573b8:	e2800004 	add	r0, r0, #4
   573bc:	e580e000 	str	lr, [r0]
   573c0:	e59d0010 	ldr	r0, [sp, #16]
   573c4:	e128f000 	msr	CPSR_f, r0
   573c8:	e59d0000 	ldr	r0, [sp]
   573cc:	e59d1004 	ldr	r1, [sp, #4]
   573d0:	e59d2008 	ldr	r2, [sp, #8]
   573d4:	e59d300c 	ldr	r3, [sp, #12]
   573d8:	e28dd014 	add	sp, sp, #20
   573dc:	e12fff18 	bx	r8

000573e0 <__tsf_direct_jmp_checking>:
   573e0:	e24dd014 	sub	sp, sp, #20
   573e4:	e58d0000 	str	r0, [sp]
   573e8:	e58d1004 	str	r1, [sp, #4]
   573ec:	e58d2008 	str	r2, [sp, #8]
   573f0:	e58d300c 	str	r3, [sp, #12]
   573f4:	e10f0000 	mrs	r0, CPSR
   573f8:	e58d0010 	str	r0, [sp, #16]
   573fc:	e59f06c0 	ldr	r0, [pc, #1728]	; 57ac4 <.curr_cpt_id>
   57400:	e3a01008 	mov	r1, #8
   57404:	e0010190 	mul	r1, r0, r1
   57408:	e59f2854 	ldr	r2, [pc, #2132]	; 57c64 <.cpt_stack+0x194>
   5740c:	e0811002 	add	r1, r1, r2
   57410:	e59f06b0 	ldr	r0, [pc, #1712]	; 57ac8 <.total_cpt_cnt>
   57414:	e3a02008 	mov	r2, #8
   57418:	e0000290 	mul	r0, r0, r2
   5741c:	e59f2840 	ldr	r2, [pc, #2112]	; 57c64 <.cpt_stack+0x194>
   57420:	e0820000 	add	r0, r2, r0
   57424:	e5912000 	ldr	r2, [r1]
   57428:	e0822000 	add	r2, r2, r0
   5742c:	e5911004 	ldr	r1, [r1, #4]
   57430:	e3a03000 	mov	r3, #0

00057434 <direct_cpt_ck_loop>:
   57434:	e1530001 	cmp	r3, r1
   57438:	aa000007 	bge	5745c <direct_cpt_ck_fail>
   5743c:	e3a00008 	mov	r0, #8
   57440:	e0000093 	mul	r0, r3, r0
   57444:	e0800002 	add	r0, r0, r2
   57448:	e5900000 	ldr	r0, [r0]
   5744c:	e1580000 	cmp	r8, r0
   57450:	0a000003 	beq	57464 <direct_cpt_ck_pass>
   57454:	e2833001 	add	r3, r3, #1
   57458:	eafffff5 	b	57434 <direct_cpt_ck_loop>

0005745c <direct_cpt_ck_fail>:
   5745c:	eaffffc7 	b	57380 <direct_link_cpt_ck_pass>
   57460:	eaffffa4 	b	572f8 <__error>

00057464 <direct_cpt_ck_pass>:
   57464:	e3a00008 	mov	r0, #8
   57468:	e2433001 	sub	r3, r3, #1
   5746c:	e0000093 	mul	r0, r3, r0
   57470:	e0800002 	add	r0, r0, r2
   57474:	e5900004 	ldr	r0, [r0, #4]
   57478:	e59f17e8 	ldr	r1, [pc, #2024]	; 57c68 <.cpt_stack+0x198>
   5747c:	e5810000 	str	r0, [r1]
   57480:	e59d0010 	ldr	r0, [sp, #16]
   57484:	e128f000 	msr	CPSR_f, r0
   57488:	e59d0000 	ldr	r0, [sp]
   5748c:	e59d1004 	ldr	r1, [sp, #4]
   57490:	e59d2008 	ldr	r2, [sp, #8]
   57494:	e59d300c 	ldr	r3, [sp, #12]
   57498:	e28dd014 	add	sp, sp, #20
   5749c:	e12fff18 	bx	r8

000574a0 <__tsf_direct_jmp_link_recording>:
   574a0:	e92d400f 	push	{r0, r1, r2, r3, lr}
   574a4:	e1a0000e 	mov	r0, lr
   574a8:	faffb294 	blx	43f00 <c_direct_tsf_recording>
   574ac:	e8bd400f 	pop	{r0, r1, r2, r3, lr}
   574b0:	e12fff1e 	bx	lr

000574b4 <__tsf_direct_jmp_link_cc_recording>:
   574b4:	e92d400f 	push	{r0, r1, r2, r3, lr}
   574b8:	e10f0000 	mrs	r0, CPSR
   574bc:	e52d0004 	push	{r0}		; (str r0, [sp, #-4]!)
   574c0:	e1a0000e 	mov	r0, lr
   574c4:	faffb325 	blx	44160 <c_direct_tsf_cc_recording>
   574c8:	e49d0004 	pop	{r0}		; (ldr r0, [sp], #4)
   574cc:	e129f000 	msr	CPSR_fc, r0
   574d0:	e8bd400f 	pop	{r0, r1, r2, r3, lr}
   574d4:	e12fff1e 	bx	lr

000574d8 <__tsf_direct_jmp_recording>:
   574d8:	e12fff1e 	bx	lr

000574dc <__tsf_direct_jmp_cc_recording>:
   574dc:	e92d400f 	push	{r0, r1, r2, r3, lr}
   574e0:	e10f0000 	mrs	r0, CPSR
   574e4:	e52d0004 	push	{r0}		; (str r0, [sp, #-4]!)
   574e8:	e1a0000e 	mov	r0, lr
   574ec:	faffb362 	blx	4427c <c_direct_tsf_bcc_recording>
   574f0:	e49d0004 	pop	{r0}		; (ldr r0, [sp], #4)
   574f4:	e129f000 	msr	CPSR_fc, r0
   574f8:	e8bd400f 	pop	{r0, r1, r2, r3, lr}
   574fc:	e12fff1e 	bx	lr

00057500 <__tsf_indirect_jmp_link_recording>:
   57500:	e92d400f 	push	{r0, r1, r2, r3, lr}
   57504:	e1a0000e 	mov	r0, lr
   57508:	faffb3a4 	blx	443a0 <c_indirect_tsf_recording>
   5750c:	e8bd400f 	pop	{r0, r1, r2, r3, lr}
   57510:	e12fff18 	bx	r8

00057514 <__tsf_indirect_jmp_link_cc_recording>:
   57514:	e12fff1e 	bx	lr

00057518 <__tsf_indirect_jmp_recording>:
   57518:	e12fff18 	bx	r8

0005751c <__tsf_indirect_jmp_cc_recording>:
   5751c:	e12fff1e 	bx	lr

00057520 <__tsf_bkwd_bx_lr_recording>:
   57520:	e92d400f 	push	{r0, r1, r2, r3, lr}
   57524:	e1a0000e 	mov	r0, lr
   57528:	faffb3c7 	blx	4444c <c_tsf_bx_lr_recording>
   5752c:	e8bd400f 	pop	{r0, r1, r2, r3, lr}
   57530:	e12fff18 	bx	r8

00057534 <__tsf_bkwd_pop_pc_recording>:
   57534:	e92d400f 	push	{r0, r1, r2, r3, lr}
   57538:	e1a0000e 	mov	r0, lr
   5753c:	faffb3f9 	blx	44528 <c_tsf_pop_pc_recording>
   57540:	e8bd400f 	pop	{r0, r1, r2, r3, lr}
   57544:	e12fff18 	bx	r8

00057548 <__tsf_test>:
   57548:	e12fff1e 	bx	lr

0005754c <__tsf_indirect_jmp_link_checking>:
   5754c:	e24dd014 	sub	sp, sp, #20
   57550:	e58d0000 	str	r0, [sp]
   57554:	e58d1004 	str	r1, [sp, #4]
   57558:	e58d2008 	str	r2, [sp, #8]
   5755c:	e58d300c 	str	r3, [sp, #12]
   57560:	e10f0000 	mrs	r0, CPSR
   57564:	e58d0010 	str	r0, [sp, #16]
   57568:	e59f0554 	ldr	r0, [pc, #1364]	; 57ac4 <.curr_cpt_id>
   5756c:	e3a01008 	mov	r1, #8
   57570:	e0010190 	mul	r1, r0, r1
   57574:	e59f26f4 	ldr	r2, [pc, #1780]	; 57c70 <.cpt_stack+0x1a0>
   57578:	e0811002 	add	r1, r1, r2
   5757c:	e59f0544 	ldr	r0, [pc, #1348]	; 57ac8 <.total_cpt_cnt>
   57580:	e3a02008 	mov	r2, #8
   57584:	e0000290 	mul	r0, r0, r2
   57588:	e59f26e0 	ldr	r2, [pc, #1760]	; 57c70 <.cpt_stack+0x1a0>
   5758c:	e0820000 	add	r0, r2, r0
   57590:	e5912000 	ldr	r2, [r1]
   57594:	e0822000 	add	r2, r2, r0
   57598:	e5911004 	ldr	r1, [r1, #4]
   5759c:	e3a03000 	mov	r3, #0

000575a0 <indirect_link_cpt_ck_loop>:
   575a0:	e1530001 	cmp	r3, r1
   575a4:	aa000007 	bge	575c8 <indirect_link_cpt_ck_fail>
   575a8:	e3a00008 	mov	r0, #8
   575ac:	e0000093 	mul	r0, r3, r0
   575b0:	e0800002 	add	r0, r0, r2
   575b4:	e5900000 	ldr	r0, [r0]
   575b8:	e1580000 	cmp	r8, r0
   575bc:	0a000009 	beq	575e8 <indirect_link_cpt_ck_pass>
   575c0:	e2833001 	add	r3, r3, #1
   575c4:	eafffff5 	b	575a0 <indirect_link_cpt_ck_loop>

000575c8 <indirect_link_cpt_ck_fail>:
   575c8:	e59f1698 	ldr	r1, [pc, #1688]	; 57c68 <.cpt_stack+0x198>
   575cc:	e5912000 	ldr	r2, [r1]
   575d0:	e1a01002 	mov	r1, r2
   575d4:	e3a02006 	mov	r2, #6
   575d8:	e92d4100 	push	{r8, lr}
   575dc:	faffb4ed 	blx	44998 <view_switch_to_rd_and_log>
   575e0:	e8bd4100 	pop	{r8, lr}
   575e4:	ea00001d 	b	57660 <indirect_link_internal_sfi>

000575e8 <indirect_link_cpt_ck_pass>:
   575e8:	e3a00008 	mov	r0, #8
   575ec:	e2433001 	sub	r3, r3, #1
   575f0:	e0000093 	mul	r0, r3, r0
   575f4:	e0800002 	add	r0, r0, r2
   575f8:	e5900004 	ldr	r0, [r0, #4]
   575fc:	e59f1664 	ldr	r1, [pc, #1636]	; 57c68 <.cpt_stack+0x198>
   57600:	e5912000 	ldr	r2, [r1]
   57604:	e5810000 	str	r0, [r1]
   57608:	e1a01002 	mov	r1, r2
   5760c:	e3a02006 	mov	r2, #6
   57610:	e92d4100 	push	{r8, lr}
   57614:	faffb4df 	blx	44998 <view_switch_to_rd_and_log>
   57618:	e8bd4100 	pop	{r8, lr}
   5761c:	e59f0648 	ldr	r0, [pc, #1608]	; 57c6c <.cpt_stack+0x19c>
   57620:	e59f14a4 	ldr	r1, [pc, #1188]	; 57acc <.curr_cpt_stack_pointer_offset>
   57624:	e0800001 	add	r0, r0, r1
   57628:	e2811008 	add	r1, r1, #8
   5762c:	e58f1498 	str	r1, [pc, #1176]	; 57acc <.curr_cpt_stack_pointer_offset>
   57630:	e59f148c 	ldr	r1, [pc, #1164]	; 57ac4 <.curr_cpt_id>
   57634:	e5801000 	str	r1, [r0]
   57638:	e2800004 	add	r0, r0, #4
   5763c:	e580e000 	str	lr, [r0]
   57640:	e59d0010 	ldr	r0, [sp, #16]
   57644:	e128f000 	msr	CPSR_f, r0
   57648:	e59d0000 	ldr	r0, [sp]
   5764c:	e59d1004 	ldr	r1, [sp, #4]
   57650:	e59d2008 	ldr	r2, [sp, #8]
   57654:	e59d300c 	ldr	r3, [sp, #12]
   57658:	e28dd014 	add	sp, sp, #20
   5765c:	e12fff18 	bx	r8

00057660 <indirect_link_internal_sfi>:
   57660:	e59f045c 	ldr	r0, [pc, #1116]	; 57ac4 <.curr_cpt_id>
   57664:	e3a01004 	mov	r1, #4
   57668:	e0000190 	mul	r0, r0, r1
   5766c:	e59f15ec 	ldr	r1, [pc, #1516]	; 57c60 <.cpt_stack+0x190>
   57670:	e0811000 	add	r1, r1, r0
   57674:	e5911000 	ldr	r1, [r1]
   57678:	e1580001 	cmp	r8, r1
   5767c:	3affff1d 	bcc	572f8 <__error>
   57680:	e2800004 	add	r0, r0, #4
   57684:	e59f15d4 	ldr	r1, [pc, #1492]	; 57c60 <.cpt_stack+0x190>
   57688:	e0811000 	add	r1, r1, r0
   5768c:	e5911000 	ldr	r1, [r1]
   57690:	e1510008 	cmp	r1, r8
   57694:	3affff17 	bcc	572f8 <__error>
   57698:	e59d0010 	ldr	r0, [sp, #16]
   5769c:	e128f000 	msr	CPSR_f, r0
   576a0:	e59d0000 	ldr	r0, [sp]
   576a4:	e59d1004 	ldr	r1, [sp, #4]
   576a8:	e59d2008 	ldr	r2, [sp, #8]
   576ac:	e59d300c 	ldr	r3, [sp, #12]
   576b0:	e28dd014 	add	sp, sp, #20
   576b4:	e12fff18 	bx	r8

000576b8 <__tsf_indirect_jmp_checking>:
   576b8:	e24dd014 	sub	sp, sp, #20
   576bc:	e58d0000 	str	r0, [sp]
   576c0:	e58d1004 	str	r1, [sp, #4]
   576c4:	e58d2008 	str	r2, [sp, #8]
   576c8:	e58d300c 	str	r3, [sp, #12]
   576cc:	e10f0000 	mrs	r0, CPSR
   576d0:	e58d0010 	str	r0, [sp, #16]
   576d4:	e59f03e8 	ldr	r0, [pc, #1000]	; 57ac4 <.curr_cpt_id>
   576d8:	e3a01008 	mov	r1, #8
   576dc:	e0010190 	mul	r1, r0, r1
   576e0:	e59f2588 	ldr	r2, [pc, #1416]	; 57c70 <.cpt_stack+0x1a0>
   576e4:	e0811002 	add	r1, r1, r2
   576e8:	e59f03d8 	ldr	r0, [pc, #984]	; 57ac8 <.total_cpt_cnt>
   576ec:	e3a02008 	mov	r2, #8
   576f0:	e0000290 	mul	r0, r0, r2
   576f4:	e59f2574 	ldr	r2, [pc, #1396]	; 57c70 <.cpt_stack+0x1a0>
   576f8:	e0820000 	add	r0, r2, r0
   576fc:	e5912000 	ldr	r2, [r1]
   57700:	e0822000 	add	r2, r2, r0
   57704:	e5911004 	ldr	r1, [r1, #4]
   57708:	e3a03000 	mov	r3, #0

0005770c <indirect_cpt_ck_loop>:
   5770c:	e1530001 	cmp	r3, r1
   57710:	aa000007 	bge	57734 <indirect_cpt_ck_fail>
   57714:	e3a00008 	mov	r0, #8
   57718:	e0000093 	mul	r0, r3, r0
   5771c:	e0800002 	add	r0, r0, r2
   57720:	e5900000 	ldr	r0, [r0]
   57724:	e1580000 	cmp	r8, r0
   57728:	0a000003 	beq	5773c <indirect_cpt_ck_pass>
   5772c:	e2833001 	add	r3, r3, #1
   57730:	eafffff5 	b	5770c <indirect_cpt_ck_loop>

00057734 <indirect_cpt_ck_fail>:
   57734:	ea000000 	b	5773c <indirect_cpt_ck_pass>
   57738:	ea00000e 	b	57778 <indirect_internal_sfi>

0005773c <indirect_cpt_ck_pass>:
   5773c:	e3a00008 	mov	r0, #8
   57740:	e2433001 	sub	r3, r3, #1
   57744:	e0000093 	mul	r0, r3, r0
   57748:	e0800002 	add	r0, r0, r2
   5774c:	e5900004 	ldr	r0, [r0, #4]
   57750:	e59f1510 	ldr	r1, [pc, #1296]	; 57c68 <.cpt_stack+0x198>
   57754:	e5810000 	str	r0, [r1]
   57758:	e59d0010 	ldr	r0, [sp, #16]
   5775c:	e128f000 	msr	CPSR_f, r0
   57760:	e59d0000 	ldr	r0, [sp]
   57764:	e59d1004 	ldr	r1, [sp, #4]
   57768:	e59d2008 	ldr	r2, [sp, #8]
   5776c:	e59d300c 	ldr	r3, [sp, #12]
   57770:	e28dd014 	add	sp, sp, #20
   57774:	e12fff18 	bx	r8

00057778 <indirect_internal_sfi>:
   57778:	e59f0344 	ldr	r0, [pc, #836]	; 57ac4 <.curr_cpt_id>
   5777c:	e3a01004 	mov	r1, #4
   57780:	e0000190 	mul	r0, r0, r1
   57784:	e59f14d4 	ldr	r1, [pc, #1236]	; 57c60 <.cpt_stack+0x190>
   57788:	e0811000 	add	r1, r1, r0
   5778c:	e5911000 	ldr	r1, [r1]
   57790:	e1580001 	cmp	r8, r1
   57794:	3afffed7 	bcc	572f8 <__error>
   57798:	e2800004 	add	r0, r0, #4
   5779c:	e59f14bc 	ldr	r1, [pc, #1212]	; 57c60 <.cpt_stack+0x190>
   577a0:	e0811000 	add	r1, r1, r0
   577a4:	e5911000 	ldr	r1, [r1]
   577a8:	e1510008 	cmp	r1, r8
   577ac:	3afffed1 	bcc	572f8 <__error>
   577b0:	e59d0010 	ldr	r0, [sp, #16]
   577b4:	e128f000 	msr	CPSR_f, r0
   577b8:	e59d0000 	ldr	r0, [sp]
   577bc:	e59d1004 	ldr	r1, [sp, #4]
   577c0:	e59d2008 	ldr	r2, [sp, #8]
   577c4:	e59d300c 	ldr	r3, [sp, #12]
   577c8:	e28dd014 	add	sp, sp, #20
   577cc:	e12fff18 	bx	r8

000577d0 <__tsf_bkwd_bx_lr_checking>:
   577d0:	e24dd00c 	sub	sp, sp, #12
   577d4:	e58d0000 	str	r0, [sp]
   577d8:	e58d1004 	str	r1, [sp, #4]
   577dc:	e10f0000 	mrs	r0, CPSR
   577e0:	e58d0008 	str	r0, [sp, #8]
   577e4:	e59f0480 	ldr	r0, [pc, #1152]	; 57c6c <.cpt_stack+0x19c>
   577e8:	e59f12dc 	ldr	r1, [pc, #732]	; 57acc <.curr_cpt_stack_pointer_offset>
   577ec:	e0810000 	add	r0, r1, r0
   577f0:	e2400004 	sub	r0, r0, #4
   577f4:	e5900000 	ldr	r0, [r0]
   577f8:	e1580000 	cmp	r8, r0
   577fc:	0a000006 	beq	5781c <__tsf_bkwd_bx_lr_pass>
   57800:	e59d0008 	ldr	r0, [sp, #8]
   57804:	e128f000 	msr	CPSR_f, r0
   57808:	e59d0000 	ldr	r0, [sp]
   5780c:	e59d1004 	ldr	r1, [sp, #4]
   57810:	e59de00c 	ldr	lr, [sp, #12]
   57814:	e28dd010 	add	sp, sp, #16
   57818:	ea00000e 	b	57858 <__tsf_trampoline_bkwd_bx>

0005781c <__tsf_bkwd_bx_lr_pass>:
   5781c:	e2411008 	sub	r1, r1, #8
   57820:	e59f044c 	ldr	r0, [pc, #1100]	; 57c74 <.cpt_stack+0x1a4>
   57824:	e5801000 	str	r1, [r0]
   57828:	e59f043c 	ldr	r0, [pc, #1084]	; 57c6c <.cpt_stack+0x19c>
   5782c:	e0811000 	add	r1, r1, r0
   57830:	e5910000 	ldr	r0, [r1]
   57834:	e59f142c 	ldr	r1, [pc, #1068]	; 57c68 <.cpt_stack+0x198>
   57838:	e5810000 	str	r0, [r1]
   5783c:	e59d0008 	ldr	r0, [sp, #8]
   57840:	e128f000 	msr	CPSR_f, r0
   57844:	e59d0000 	ldr	r0, [sp]
   57848:	e59d1004 	ldr	r1, [sp, #4]
   5784c:	e59de00c 	ldr	lr, [sp, #12]
   57850:	e28dd010 	add	sp, sp, #16
   57854:	e12fff18 	bx	r8

00057858 <__tsf_trampoline_bkwd_bx>:
   57858:	e24dd00c 	sub	sp, sp, #12
   5785c:	e58d0000 	str	r0, [sp]
   57860:	e58d1004 	str	r1, [sp, #4]
   57864:	e10f0000 	mrs	r0, CPSR
   57868:	e58d0008 	str	r0, [sp, #8]
   5786c:	e59f0250 	ldr	r0, [pc, #592]	; 57ac4 <.curr_cpt_id>
   57870:	e3a01004 	mov	r1, #4
   57874:	e0000190 	mul	r0, r0, r1
   57878:	e59f13e0 	ldr	r1, [pc, #992]	; 57c60 <.cpt_stack+0x190>
   5787c:	e0811000 	add	r1, r1, r0
   57880:	e5911000 	ldr	r1, [r1]
   57884:	e1580001 	cmp	r8, r1
   57888:	3afffe9a 	bcc	572f8 <__error>
   5788c:	e2800004 	add	r0, r0, #4
   57890:	e59f13c8 	ldr	r1, [pc, #968]	; 57c60 <.cpt_stack+0x190>
   57894:	e0811000 	add	r1, r1, r0
   57898:	e5911000 	ldr	r1, [r1]
   5789c:	e1510008 	cmp	r1, r8
   578a0:	3afffe94 	bcc	572f8 <__error>
   578a4:	e59d0008 	ldr	r0, [sp, #8]
   578a8:	e128f000 	msr	CPSR_f, r0
   578ac:	e59d0000 	ldr	r0, [sp]
   578b0:	e59d1004 	ldr	r1, [sp, #4]
   578b4:	e28dd00c 	add	sp, sp, #12
   578b8:	e12fff18 	bx	r8

000578bc <__tsf_bkwd_pop_pc_checking>:
   578bc:	e59d8004 	ldr	r8, [sp, #4]
   578c0:	e24dd00c 	sub	sp, sp, #12
   578c4:	e58d0000 	str	r0, [sp]
   578c8:	e58d1004 	str	r1, [sp, #4]
   578cc:	e10f0000 	mrs	r0, CPSR
   578d0:	e58d0008 	str	r0, [sp, #8]
   578d4:	e59f0390 	ldr	r0, [pc, #912]	; 57c6c <.cpt_stack+0x19c>
   578d8:	e59f11ec 	ldr	r1, [pc, #492]	; 57acc <.curr_cpt_stack_pointer_offset>
   578dc:	e0810000 	add	r0, r1, r0
   578e0:	e2400004 	sub	r0, r0, #4
   578e4:	e5900000 	ldr	r0, [r0]
   578e8:	e1580000 	cmp	r8, r0
   578ec:	0a000006 	beq	5790c <__tsf_bkwd_pop_pc_pass>
   578f0:	e59d0008 	ldr	r0, [sp, #8]
   578f4:	e128f000 	msr	CPSR_f, r0
   578f8:	e59d0000 	ldr	r0, [sp]
   578fc:	e59d1004 	ldr	r1, [sp, #4]
   57900:	e28dd00c 	add	sp, sp, #12
   57904:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   57908:	ea00000f 	b	5794c <__tsf_trampoline_bkwd_pop>

0005790c <__tsf_bkwd_pop_pc_pass>:
   5790c:	e2411008 	sub	r1, r1, #8
   57910:	e59f035c 	ldr	r0, [pc, #860]	; 57c74 <.cpt_stack+0x1a4>
   57914:	e5801000 	str	r1, [r0]
   57918:	e59f034c 	ldr	r0, [pc, #844]	; 57c6c <.cpt_stack+0x19c>
   5791c:	e0811000 	add	r1, r1, r0
   57920:	e5910000 	ldr	r0, [r1]
   57924:	e59f133c 	ldr	r1, [pc, #828]	; 57c68 <.cpt_stack+0x198>
   57928:	e5810000 	str	r0, [r1]
   5792c:	e59d0008 	ldr	r0, [sp, #8]
   57930:	e128f000 	msr	CPSR_f, r0
   57934:	e59d0000 	ldr	r0, [sp]
   57938:	e59d1004 	ldr	r1, [sp, #4]
   5793c:	e28dd00c 	add	sp, sp, #12
   57940:	e49de004 	pop	{lr}		; (ldr lr, [sp], #4)
   57944:	e28dd004 	add	sp, sp, #4
   57948:	e12fff18 	bx	r8

0005794c <__tsf_trampoline_bkwd_pop>:
   5794c:	e49d8004 	pop	{r8}		; (ldr r8, [sp], #4)
   57950:	e24dd00c 	sub	sp, sp, #12
   57954:	e58d0000 	str	r0, [sp]
   57958:	e58d1004 	str	r1, [sp, #4]
   5795c:	e10f0000 	mrs	r0, CPSR
   57960:	e58d0008 	str	r0, [sp, #8]
   57964:	e59f0158 	ldr	r0, [pc, #344]	; 57ac4 <.curr_cpt_id>
   57968:	e3a01004 	mov	r1, #4
   5796c:	e0000190 	mul	r0, r0, r1
   57970:	e59f12e8 	ldr	r1, [pc, #744]	; 57c60 <.cpt_stack+0x190>
   57974:	e0811000 	add	r1, r1, r0
   57978:	e5911000 	ldr	r1, [r1]
   5797c:	e1580001 	cmp	r8, r1
   57980:	3afffe5c 	bcc	572f8 <__error>
   57984:	e2800004 	add	r0, r0, #4
   57988:	e59f12d0 	ldr	r1, [pc, #720]	; 57c60 <.cpt_stack+0x190>
   5798c:	e0811000 	add	r1, r1, r0
   57990:	e5911000 	ldr	r1, [r1]
   57994:	e1510008 	cmp	r1, r8
   57998:	3afffe56 	bcc	572f8 <__error>
   5799c:	e59d0008 	ldr	r0, [sp, #8]
   579a0:	e128f000 	msr	CPSR_f, r0
   579a4:	e59d0000 	ldr	r0, [sp]
   579a8:	e59d1004 	ldr	r1, [sp, #4]
   579ac:	e28dd00c 	add	sp, sp, #12
   579b0:	e12fff18 	bx	r8

000579b4 <__storing_checking>:
   579b4:	e24dd018 	sub	sp, sp, #24
   579b8:	e58d0000 	str	r0, [sp]
   579bc:	e58d1004 	str	r1, [sp, #4]
   579c0:	e58d2008 	str	r2, [sp, #8]
   579c4:	e58d300c 	str	r3, [sp, #12]
   579c8:	e58d4010 	str	r4, [sp, #16]
   579cc:	e10f0000 	mrs	r0, CPSR
   579d0:	e58d0014 	str	r0, [sp, #20]
   579d4:	e59f00e8 	ldr	r0, [pc, #232]	; 57ac4 <.curr_cpt_id>
   579d8:	e3a01008 	mov	r1, #8
   579dc:	e0010190 	mul	r1, r0, r1
   579e0:	e59f2290 	ldr	r2, [pc, #656]	; 57c78 <.cpt_stack+0x1a8>
   579e4:	e0811002 	add	r1, r1, r2
   579e8:	e59f00d8 	ldr	r0, [pc, #216]	; 57ac8 <.total_cpt_cnt>
   579ec:	e3a02008 	mov	r2, #8
   579f0:	e0000290 	mul	r0, r0, r2
   579f4:	e59f227c 	ldr	r2, [pc, #636]	; 57c78 <.cpt_stack+0x1a8>
   579f8:	e0820000 	add	r0, r2, r0
   579fc:	e5912000 	ldr	r2, [r1]
   57a00:	e0822000 	add	r2, r2, r0
   57a04:	e5911004 	ldr	r1, [r1, #4]
   57a08:	e3a03000 	mov	r3, #0
   57a0c:	e3a04000 	mov	r4, #0

00057a10 <storing_ck_loop>:
   57a10:	e1530001 	cmp	r3, r1
   57a14:	aa000010 	bge	57a5c <storing_ck_valid>
   57a18:	e3a00008 	mov	r0, #8
   57a1c:	e0000093 	mul	r0, r3, r0
   57a20:	e0800002 	add	r0, r0, r2
   57a24:	e5900000 	ldr	r0, [r0]
   57a28:	e1580000 	cmp	r8, r0
   57a2c:	3a000008 	bcc	57a54 <storing_loop_next>
   57a30:	e3a00008 	mov	r0, #8
   57a34:	e0000093 	mul	r0, r3, r0
   57a38:	e0800002 	add	r0, r0, r2
   57a3c:	e2800004 	add	r0, r0, #4
   57a40:	e5900000 	ldr	r0, [r0]
   57a44:	e1580000 	cmp	r8, r0
   57a48:	8a000001 	bhi	57a54 <storing_loop_next>
   57a4c:	e3a04001 	mov	r4, #1
   57a50:	ea000006 	b	57a70 <storing_ck_pass>

00057a54 <storing_loop_next>:
   57a54:	e2833001 	add	r3, r3, #1
   57a58:	eaffffec 	b	57a10 <storing_ck_loop>

00057a5c <storing_ck_valid>:
   57a5c:	e3540000 	cmp	r4, #0
   57a60:	0a000000 	beq	57a68 <storing_ck_fail>
   57a64:	ea000001 	b	57a70 <storing_ck_pass>

00057a68 <storing_ck_fail>:
   57a68:	ea000000 	b	57a70 <storing_ck_pass>
   57a6c:	eafffe21 	b	572f8 <__error>

00057a70 <storing_ck_pass>:
   57a70:	e59d0020 	ldr	r0, [sp, #32]
   57a74:	e59d101c 	ldr	r1, [sp, #28]
   57a78:	e30021bf 	movw	r2, #447	; 0x1bf
   57a7c:	e1500002 	cmp	r0, r2
   57a80:	0a00000b 	beq	57ab4 <STRBi12>
   57a84:	e30021d7 	movw	r2, #471	; 0x1d7
   57a88:	e1500002 	cmp	r0, r2
   57a8c:	0a00000a 	beq	57abc <STRi12>

00057a90 <storing_ctx_restoring>:
   57a90:	e59d0014 	ldr	r0, [sp, #20]
   57a94:	e128f000 	msr	CPSR_f, r0
   57a98:	e59d0000 	ldr	r0, [sp]
   57a9c:	e59d1004 	ldr	r1, [sp, #4]
   57aa0:	e59d2008 	ldr	r2, [sp, #8]
   57aa4:	e59d300c 	ldr	r3, [sp, #12]
   57aa8:	e59d4010 	ldr	r4, [sp, #16]
   57aac:	e28dd018 	add	sp, sp, #24
   57ab0:	e12fff1e 	bx	lr

00057ab4 <STRBi12>:
   57ab4:	e5c81000 	strb	r1, [r8]
   57ab8:	eafffff4 	b	57a90 <storing_ctx_restoring>

00057abc <STRi12>:
   57abc:	e5881000 	str	r1, [r8]
   57ac0:	eafffff2 	b	57a90 <storing_ctx_restoring>

00057ac4 <.curr_cpt_id>:
   57ac4:	00000000 	andeq	r0, r0, r0

00057ac8 <.total_cpt_cnt>:
   57ac8:	00000003 	andeq	r0, r0, r3

00057acc <.curr_cpt_stack_pointer_offset>:
   57acc:	00000000 	andeq	r0, r0, r0

00057ad0 <.cpt_stack>:
	...
   57c60:	00046b77 	andeq	r6, r4, r7, ror fp
   57c64:	00046b97 	muleq	r4, r7, fp
   57c68:	00057ac4 	andeq	r7, r5, r4, asr #21
   57c6c:	00057ad0 	ldrdeq	r7, [r5], -r0
   57c70:	00046bcf 	andeq	r6, r4, pc, asr #23
   57c74:	00057acc 	andeq	r7, r5, ip, asr #21
   57c78:	00046c07 	andeq	r6, r4, r7, lsl #24
   57c7c:	00000000 	andeq	r0, r0, r0

00057c80 <__error_found_from_arm>:
   57c80:	e51ff004 	ldr	pc, [pc, #-4]	; 57c84 <__error_found_from_arm+0x4>
   57c84:	00044957 	andeq	r4, r4, r7, asr r9

Disassembly of section .bss:

00057c88 <__bss_start>:
   57c88:	00000000 	andeq	r0, r0, r0

00057c8c <stepperPos>:
   57c8c:	00000000 	andeq	r0, r0, r0

00057c90 <ringbuffer_init_flag>:
   57c90:	00000000 	andeq	r0, r0, r0

00057c94 <cnt>:
   57c94:	00000000 	andeq	r0, r0, r0

00057c98 <ret_recording_finish>:
   57c98:	00000000 	andeq	r0, r0, r0

00057c9c <ret_hash_init_flag>:
   57c9c:	00000000 	andeq	r0, r0, r0

00057ca0 <rd_optee_init>:
   57ca0:	00000000 	andeq	r0, r0, r0

00057ca4 <invoke_cnt>:
   57ca4:	00000000 	andeq	r0, r0, r0

00057ca8 <teec_mutex>:
	...

00057cc0 <charBuf>:
	...

00057cd0 <adc_key_in>:
   57cd0:	00000000 	andeq	r0, r0, r0

00057cd4 <lcd>:
   57cd4:	00000000 	andeq	r0, r0, r0

00057cd8 <ringBuffer>:
	...

098ee4e0 <current_cpt_id>:
 98ee4e0:	00000000 	andeq	r0, r0, r0

098ee4e4 <ctx>:
	...

098ee4ec <state>:
	...

098ee568 <hash>:
	...

098ee588 <err_origin>:
 98ee588:	00000000 	andeq	r0, r0, r0

098ee58c <sess>:
	...

098ee594 <res>:
 98ee594:	00000000 	andeq	r0, r0, r0

098ee598 <op>:
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
  58:	地址 0x0000000000000058 越界。


Disassembly of section .ARM.attributes:

00000000 <.ARM.attributes>:
   0:	00003641 	andeq	r3, r0, r1, asr #12
   4:	61656100 	cmnvs	r5, r0, lsl #2
   8:	01006962 	tsteq	r0, r2, ror #18
   c:	0000002c 	andeq	r0, r0, ip, lsr #32
  10:	412d3705 			; <UNDEFINED> instruction: 0x412d3705
  14:	070a0600 	streq	r0, [sl, -r0, lsl #12]
  18:	09010841 	stmdbeq	r1, {r0, r6, fp}
  1c:	11040a02 	tstne	r4, r2, lsl #20
  20:	14041201 	strne	r1, [r4], #-513	; 0xfffffdff
  24:	17011501 	strne	r1, [r1, -r1, lsl #10]
  28:	1a011803 	bne	4603c <TEEC_RegisterSharedMemoryFileDescriptor+0x9a>
  2c:	1e011c02 	cdpne	12, 0, cr1, cr1, cr2, {0}
  30:	26012201 	strcs	r2, [r1], -r1, lsl #4
  34:	地址 0x0000000000000034 越界。


Disassembly of section .debug_aranges:

00000000 <.debug_aranges>:
   0:	0000001c 	andeq	r0, r0, ip, lsl r0
   4:	09ed0002 	stmibeq	sp!, {r1}^
   8:	00040000 	andeq	r0, r4, r0
   c:	00000000 	andeq	r0, r0, r0
  10:	00040ad8 	ldrdeq	r0, [r4], -r8
  14:	000031e6 	andeq	r3, r0, r6, ror #3
	...
  20:	0000001c 	andeq	r0, r0, ip, lsl r0
  24:	14600002 	strbtne	r0, [r0], #-2
  28:	00040000 	andeq	r0, r4, r0
  2c:	00000000 	andeq	r0, r0, r0
  30:	00043cc0 	andeq	r3, r4, r0, asr #25
  34:	00000cd8 	ldrdeq	r0, [r0], -r8
	...
  40:	0000001c 	andeq	r0, r0, ip, lsl r0
  44:	1f3e0002 	svcne	0x003e0002
  48:	00040000 	andeq	r0, r4, r0
  4c:	00000000 	andeq	r0, r0, r0
  50:	00057138 	andeq	r7, r5, r8, lsr r1
  54:	00000b44 	andeq	r0, r0, r4, asr #22
	...
  60:	0000001c 	andeq	r0, r0, ip, lsl r0
  64:	1fd30002 	svcne	0x00d30002
  68:	00040000 	andeq	r0, r4, r0
  6c:	00000000 	andeq	r0, r0, r0
  70:	00046330 	andeq	r6, r4, r0, lsr r3
  74:	000000f8 	strdeq	r0, [r0], -r8
	...
  80:	0000001c 	andeq	r0, r0, ip, lsl r0
  84:	20650002 	rsbcs	r0, r5, r2
  88:	00040000 	andeq	r0, r4, r0
  8c:	00000000 	andeq	r0, r0, r0
  90:	00044998 	muleq	r4, r8, r9
  94:	00000664 	andeq	r0, r0, r4, ror #12
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
  20:	00004f00 	andeq	r4, r0, r0, lsl #30
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
 118:	6c6f424c 	sfmvs	f4, 2, [pc], #-304	; fffffff0 <__bss_end__+0xf6711a1c>
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
 150:	745f6472 	ldrbvc	r6, [pc], #-1138	; 158 <pthread_mutex_unlock@plt-0x107d8>
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
 1c0:	00260079 	eoreq	r0, r6, r9, ror r0
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
 264:	00003e00 	andeq	r3, r0, r0, lsl #28
 268:	63657200 	cmnvs	r5, #0, 4
 26c:	6964726f 	stmdbvs	r4!, {r0, r1, r2, r3, r5, r6, r9, ip, sp, lr}^
 270:	665f676e 	ldrbvs	r6, [pc], -lr, ror #14
 274:	0067616c 	rsbeq	r6, r7, ip, ror #2
 278:	0000022a 	andeq	r0, r0, sl, lsr #4
 27c:	69726573 	ldmdbvs	r2!, {r0, r1, r4, r5, r6, r8, sl, sp, lr}^
 280:	74536c61 	ldrbvc	r6, [r3], #-3169	; 0xfffff39f
 284:	05880072 	streq	r0, [r8, #114]	; 0x72
 288:	616d0000 	cmnvs	sp, r0
 28c:	ab006e69 	blge	1bc38 <.DATA_REGION_0__data_end+0xb16c>
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
 350:	646f4d6e 	strbtvs	r4, [pc], #-3438	; 358 <pthread_mutex_unlock@plt-0x105d8>
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
      30:	b003052a 	andlt	r0, r3, sl, lsr #10
      34:	0300010a 	movweq	r0, #266	; 0x10a
      38:	0000058c 	andeq	r0, r0, ip, lsl #11
      3c:	8f020405 	svchi	0x00020405
      40:	37000000 	strcc	r0, [r0, -r0]
      44:	01000000 	mrseq	r0, (UNDEF: 0)
      48:	fc03052c 	stc2	5, cr0, [r3], {44}	; 0x2c
      4c:	02000207 	andeq	r0, r0, #1879048192	; 0x70000000
      50:	0000009e 	muleq	r0, lr, r0
      54:	00000037 	andeq	r0, r0, r7, lsr r0
      58:	03052d01 	movweq	r2, #23809	; 0x5d01
      5c:	00057c88 	andeq	r7, r5, r8, lsl #25
      60:	0000ac02 	andeq	sl, r0, r2, lsl #24
      64:	00007100 	andeq	r7, r0, r0, lsl #2
      68:	052e0100 	streq	r0, [lr, #-256]!	; 0xffffff00
      6c:	0570cc03 	ldrbeq	ip, [r0, #-3075]!	; 0xfffff3fd
      70:	05be0300 	ldreq	r0, [lr, #768]!	; 0x300
      74:	04050000 	streq	r0, [r5], #-0
      78:	0000b802 	andeq	fp, r0, r2, lsl #16
      7c:	00007100 	andeq	r7, r0, r0, lsl #2
      80:	052f0100 	streq	r0, [pc, #-256]!	; ffffff88 <__bss_end__+0xf67119b4>
      84:	0207b803 	andeq	fp, r7, #196608	; 0x30000
      88:	00c40200 	sbceq	r0, r4, r0, lsl #4
      8c:	00370000 	eorseq	r0, r7, r0
      90:	34010000 	strcc	r0, [r1], #-0
      94:	0ab40305 	beq	fed00cb0 <__bss_end__+0xf54126dc>
      98:	d0020001 	andle	r0, r2, r1
      9c:	37000000 	strcc	r0, [r0, -r0]
      a0:	01000000 	mrseq	r0, (UNDEF: 0)
      a4:	b8030535 	stmdalt	r3, {r0, r2, r4, r5, r8, sl}
      a8:	0200010a 	andeq	r0, r0, #-2147483646	; 0x80000002
      ac:	000000dd 	ldrdeq	r0, [r0], -sp
      b0:	00000037 	andeq	r0, r0, r7, lsr r0
      b4:	03053701 	movweq	r3, #22273	; 0x5701
      b8:	00040ac4 	andeq	r0, r4, r4, asr #21
      bc:	0000e802 	andeq	lr, r0, r2, lsl #16
      c0:	00003700 	andeq	r3, r0, r0, lsl #14
      c4:	05380100 	ldreq	r0, [r8, #-256]!	; 0xffffff00
      c8:	040ac803 	streq	ip, [sl], #-2051	; 0xfffff7fd
      cc:	00f60200 	rscseq	r0, r6, r0, lsl #4
      d0:	00de0000 	sbcseq	r0, lr, r0
      d4:	3b010000 	blcc	400dc <setup+0xdc>
      d8:	0a340305 	beq	d00cf4 <ringBuffer+0xca901c>
      dc:	37040004 	strcc	r0, [r4, -r4]
      e0:	05000000 	streq	r0, [r0, #-0]
      e4:	000000ea 	andeq	r0, r0, sl, ror #1
      e8:	02060005 	andeq	r0, r6, #5
      ec:	08000001 	stmdaeq	r0, {r0}
      f0:	010b0207 	tsteq	fp, r7, lsl #4
      f4:	00370000 	eorseq	r0, r7, r0
      f8:	3e010000 	cdpcc	0, 0, cr0, cr1, cr0, {0}
      fc:	0a480305 	beq	1200d18 <ringBuffer+0x11a9040>
     100:	04020004 	streq	r0, [r2], #-4
     104:	37000003 	strcc	r0, [r0, -r3]
     108:	01000000 	mrseq	r0, (UNDEF: 0)
     10c:	4c030540 	cfstr32mi	mvfx0, [r3], {64}	; 0x40
     110:	0200040a 	andeq	r0, r0, #167772160	; 0xa000000
     114:	00000114 	andeq	r0, r0, r4, lsl r1
     118:	00000124 	andeq	r0, r0, r4, lsr #2
     11c:	03054901 	movweq	r4, #22785	; 0x5901
     120:	00046428 	andeq	r6, r4, r8, lsr #8
     124:	00003707 	andeq	r3, r0, r7, lsl #14
     128:	01270200 			; <UNDEFINED> instruction: 0x01270200
     12c:	013a0000 	teqeq	sl, r0
     130:	4a010000 	bmi	40138 <loop+0x30>
     134:	0a500305 	beq	1400d50 <ringBuffer+0x13a9078>
     138:	46040004 	strmi	r0, [r4], -r4
     13c:	05000001 	streq	r0, [r0, #-1]
     140:	000000ea 	andeq	r0, r0, sl, ror #1
     144:	34030009 	strcc	r0, [r3], #-9
     148:	04000001 	streq	r0, [r0], #-1
     14c:	013a0204 	teqeq	sl, r4, lsl #4
     150:	01460000 	mrseq	r0, (UNDEF: 70)
     154:	4d010000 	stcmi	0, cr0, [r1, #-0]
     158:	0abc0305 	beq	fef00d74 <__bss_end__+0xf56127a0>
     15c:	42020001 	andmi	r0, r2, #1
     160:	46000001 	strmi	r0, [r0], -r1
     164:	01000001 	tsteq	r0, r1
     168:	7403054e 	strvc	r0, [r3], #-1358	; 0xfffffab2
     16c:	0200040a 	andeq	r0, r0, #167772160	; 0xa000000
     170:	0000014d 	andeq	r0, r0, sp, asr #2
     174:	00000146 	andeq	r0, r0, r6, asr #2
     178:	03054f01 	movweq	r4, #24321	; 0x5f01
     17c:	00020800 	andeq	r0, r2, r0, lsl #16
     180:	00015402 	andeq	r5, r1, r2, lsl #8
     184:	00003700 	andeq	r3, r0, r0, lsl #14
     188:	05500100 	ldrbeq	r0, [r0, #-256]	; 0xffffff00
     18c:	040a7803 	streq	r7, [sl], #-2051	; 0xfffff7fd
     190:	01630200 	cmneq	r3, r0, lsl #4
     194:	01460000 	mrseq	r0, (UNDEF: 70)
     198:	52010000 	andpl	r0, r1, #0
     19c:	0ac00305 	beq	ff000db8 <__bss_end__+0xf57127e4>
     1a0:	6f020001 	svcvs	0x00020001
     1a4:	71000001 	tstvc	r0, r1
     1a8:	01000000 	mrseq	r0, (UNDEF: 0)
     1ac:	8c030554 	cfstr32hi	mvfx0, [r3], {84}	; 0x54
     1b0:	0200057c 	andeq	r0, r0, #124, 10	; 0x1f000000
     1b4:	0000017a 	andeq	r0, r0, sl, ror r1
     1b8:	00000071 	andeq	r0, r0, r1, ror r0
     1bc:	03055801 	movweq	r5, #22529	; 0x5801
     1c0:	00040acc 	andeq	r0, r4, ip, asr #21
     1c4:	00018a02 	andeq	r8, r1, r2, lsl #20
     1c8:	00007100 	andeq	r7, r0, r0, lsl #2
     1cc:	05590100 	ldrbeq	r0, [r9, #-256]	; 0xffffff00
     1d0:	040a7c03 	streq	r7, [sl], #-3075	; 0xfffff3fd
     1d4:	01990200 	orrseq	r0, r9, r0, lsl #4
     1d8:	00710000 	rsbseq	r0, r1, r0
     1dc:	5a010000 	bpl	401e4 <checkTriggers+0x14>
     1e0:	0a800305 	beq	fe000dfc <__bss_end__+0xf4712828>
     1e4:	a5020004 	strge	r0, [r2, #-4]
     1e8:	37000001 	strcc	r0, [r0, -r1]
     1ec:	01000000 	mrseq	r0, (UNDEF: 0)
     1f0:	8403055b 	strhi	r0, [r3], #-1371	; 0xfffffaa5
     1f4:	0200040a 	andeq	r0, r0, #167772160	; 0xa000000
     1f8:	000001ad 	andeq	r0, r0, sp, lsr #3
     1fc:	00000037 	andeq	r0, r0, r7, lsr r0
     200:	03055e01 	movweq	r5, #24065	; 0x5e01
     204:	000570e4 	andeq	r7, r5, r4, ror #1
     208:	0001b502 	andeq	fp, r1, r2, lsl #10
     20c:	00003700 	andeq	r3, r0, r0, lsl #14
     210:	05610100 	strbeq	r0, [r1, #-256]!	; 0xffffff00
     214:	040ad003 	streq	sp, [sl], #-3
     218:	01c40200 	biceq	r0, r4, r0, lsl #4
     21c:	00370000 	eorseq	r0, r7, r0
     220:	62010000 	andvs	r0, r1, #0
     224:	0ad40305 	beq	ff500e40 <__bss_end__+0xf5c1286c>
     228:	d0020004 	andle	r0, r2, r4
     22c:	3b000001 	blcc	238 <pthread_mutex_unlock@plt-0x106f8>
     230:	01000002 	tsteq	r0, r2
     234:	e8030565 	stmda	r3, {r0, r2, r5, r6, r8, sl}
     238:	04000570 	streq	r0, [r0], #-1392	; 0xfffffa90
     23c:	00000247 	andeq	r0, r0, r7, asr #4
     240:	0000ea05 	andeq	lr, r0, r5, lsl #20
     244:	03005000 	movweq	r5, #0
     248:	00000877 	andeq	r0, r0, r7, ror r8
     24c:	da020108 	ble	80674 <ringBuffer+0x2899c>
     250:	5f000001 	svcpl	0x00000001
     254:	01000002 	tsteq	r0, r2
     258:	c4030566 	strgt	r0, [r3], #-1382	; 0xfffffa9a
     25c:	0300010a 	movweq	r0, #266	; 0x10a
     260:	000001e9 	andeq	r0, r0, r9, ror #3
     264:	ef020102 	svc	0x00020102
     268:	37000001 	strcc	r0, [r0, -r1]
     26c:	01000000 	mrseq	r0, (UNDEF: 0)
     270:	c8030567 	stmdagt	r3, {r0, r1, r2, r5, r6, r8, sl}
     274:	0200010a 	andeq	r0, r0, #-2147483646	; 0x80000002
     278:	000001fc 	strdeq	r0, [r0], -ip
     27c:	00000037 	andeq	r0, r0, r7, lsr r0
     280:	03053f01 	movweq	r3, #24321	; 0x5f01
     284:	00057cd0 	ldrdeq	r7, [r5], -r0
     288:	00020702 	andeq	r0, r2, r2, lsl #14
     28c:	00029900 	andeq	r9, r2, r0, lsl #18
     290:	05550100 	ldrbeq	r0, [r5, #-256]	; 0xffffff00
     294:	057cc003 	ldrbeq	ip, [ip, #-3]!
     298:	02470400 	subeq	r0, r7, #0, 8
     29c:	ea050000 	b	1402a4 <ringBuffer+0xe85cc>
     2a0:	10000000 	andne	r0, r0, r0
     2a4:	020f0200 	andeq	r0, pc, #0, 4
     2a8:	02b60000 	adcseq	r0, r6, #0
     2ac:	6a010000 	bvs	402b4 <checkTriggers+0xe4>
     2b0:	7cd40305 	ldclvc	3, cr0, [r4], {5}
     2b4:	c1080005 	tstgt	r8, r5
     2b8:	27000002 	strcs	r0, [r0, -r2]
     2bc:	02000002 	andeq	r0, r0, #2
     2c0:	0213090a 	andseq	r0, r3, #163840	; 0x28000
     2c4:	02040000 	andeq	r0, r4, #0
     2c8:	12260a08 	eorne	r0, r6, #8, 20	; 0x8000
     2cc:	02d60000 	sbcseq	r0, r6, #0
     2d0:	09020000 	stmdbeq	r2, {}	; <UNPREDICTABLE>
     2d4:	83030000 	movwhi	r0, #12288	; 0x3000
     2d8:	07000005 	streq	r0, [r0, -r5]
     2dc:	01040b04 	tsteq	r4, r4, lsl #22
     2e0:	02350c46 	eorseq	r0, r5, #17920	; 0x4600
     2e4:	0c000000 	stceq	0, cr0, [r0], {-0}
     2e8:	0000023b 	andeq	r0, r0, fp, lsr r2
     2ec:	040b0001 	streq	r0, [fp], #-1
     2f0:	420c4701 	andmi	r4, ip, #262144	; 0x40000
     2f4:	00000002 	andeq	r0, r0, r2
     2f8:	0002470c 	andeq	r4, r2, ip, lsl #14
     2fc:	0b000100 	bleq	704 <pthread_mutex_unlock@plt-0x1022c>
     300:	0c430104 	stfeqe	f0, [r3], {4}
     304:	0000024b 	andeq	r0, r0, fp, asr #4
     308:	02500c00 	subseq	r0, r0, #0, 24
     30c:	00010000 	andeq	r0, r1, r0
     310:	3d01040b 	cfstrscc	mvf0, [r1, #-44]	; 0xffffffd4
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
     33c:	028c0c44 	addeq	r0, ip, #68, 24	; 0x4400
     340:	0c000000 	stceq	0, cr0, [r0], {-0}
     344:	00000291 	muleq	r0, r1, r2
     348:	000d0001 	andeq	r0, sp, r1
     34c:	08000400 	stmdaeq	r0, {sl}
     350:	01000001 	tsteq	r0, r1
     354:	0002b95b 	andeq	fp, r2, fp, asr r9
     358:	0e6c0100 	poweqe	f0, f4, f0
     35c:	00040108 	andeq	r0, r4, r8, lsl #2
     360:	000000c8 	andeq	r0, r0, r8, asr #1
     364:	02bf5b01 	adcseq	r5, pc, #1024	; 0x400
     368:	8d010000 	stchi	0, cr0, [r1, #-0]
     36c:	0c7d020f 	lfmeq	f0, 2, [sp], #-60	; 0xffffffc4
     370:	000003ec 	andeq	r0, r0, ip, ror #7
     374:	00378d01 	eorseq	r8, r7, r1, lsl #26
     378:	02100000 	andseq	r0, r0, #0
     37c:	03f2087d 	mvnseq	r0, #8192000	; 0x7d0000
     380:	9e010000 	cdpls	0, 0, cr0, cr1, cr0, {0}
     384:	00000845 	andeq	r0, r0, r5, asr #16
     388:	047d0210 	ldrbteq	r0, [sp], #-528	; 0xfffffdf0
     38c:	000005ff 	strdeq	r0, [r0], -pc	; <UNPREDICTABLE>
     390:	08459e01 	stmdaeq	r5, {r0, r9, sl, fp, ip, pc}^
     394:	11000000 	mrsne	r0, (UNDEF: 0)
     398:	00020000 	andeq	r0, r2, r0
     39c:	000001c0 	andeq	r0, r0, r0, asr #3
     3a0:	02c45b01 	sbceq	r5, r4, #1024	; 0x400
     3a4:	d4010000 	strle	r0, [r1], #-0
     3a8:	02012812 	andeq	r2, r1, #1179648	; 0x120000
     3ac:	00003400 	andeq	r3, r0, r0, lsl #8
     3b0:	7d021300 	stcvc	3, cr1, [r2, #-0]
     3b4:	0003f804 	andeq	pc, r3, r4, lsl #16
     3b8:	37e20100 	strbcc	r0, [r2, r0, lsl #2]!
     3bc:	00000000 	andeq	r0, r0, r0
     3c0:	01c00e00 	biceq	r0, r0, r0, lsl #28
     3c4:	02000002 	andeq	r0, r0, #2
     3c8:	5b010000 	blpl	403d0 <readKey+0x50>
     3cc:	000003fa 	strdeq	r0, [r0], -sl
     3d0:	020ff101 	andeq	pc, pc, #1073741824	; 0x40000000
     3d4:	04000c7d 	streq	r0, [r0], #-3197	; 0xfffff383
     3d8:	f1010000 	setend	le
     3dc:	00000037 	andeq	r0, r0, r7, lsr r0
     3e0:	087d0213 	ldmdaeq	sp!, {r0, r1, r4, r9}^
     3e4:	0000040a 	andeq	r0, r0, sl, lsl #8
     3e8:	0071f501 	rsbseq	pc, r1, r1, lsl #10
     3ec:	02140000 	andseq	r0, r4, #0
     3f0:	0410047d 	ldreq	r0, [r0], #-1149	; 0xfffffb83
     3f4:	07010000 	streq	r0, [r1, -r0]
     3f8:	00014601 	andeq	r4, r1, r1, lsl #12
     3fc:	00001500 	andeq	r1, r0, r0, lsl #10
     400:	02140000 	andseq	r0, r4, #0
     404:	0418007d 	ldreq	r0, [r8], #-125	; 0xffffff83
     408:	09010000 	stmdbeq	r1, {}	; <UNPREDICTABLE>
     40c:	00007101 	andeq	r7, r0, r1, lsl #2
     410:	16000000 	strne	r0, [r0], -r0
     414:	000203c0 	andeq	r0, r2, r0, asr #7
     418:	000001ec 	andeq	r0, r0, ip, ror #3
     41c:	02d25b01 	sbcseq	r5, r2, #1024	; 0x400
     420:	6b010000 	blvs	40428 <readKey+0xa8>
     424:	7d031401 	cfstrsvc	mvf1, [r3, #-4]
     428:	041a00d8 	ldreq	r0, [sl], #-216	; 0xffffff28
     42c:	6d010000 	stcvs	0, cr0, [r1, #-0]
     430:	00023b01 	andeq	r3, r2, r1, lsl #22
     434:	7d021400 	cfstrsvc	mvf1, [r2, #-0]
     438:	0007a008 	andeq	sl, r7, r8
     43c:	016e0100 	cmneq	lr, r0, lsl #2
     440:	0000023b 	andeq	r0, r0, fp, lsr r2
     444:	047d0214 	ldrbteq	r0, [sp], #-532	; 0xfffffdec
     448:	0000041d 	andeq	r0, r0, sp, lsl r4
     44c:	37016f01 	strcc	r6, [r1, -r1, lsl #30]
     450:	14000000 	strne	r0, [r0], #-0
     454:	23007d02 	movwcs	r7, #3330	; 0xd02
     458:	01000004 	tsteq	r0, r4
     45c:	00370170 	eorseq	r0, r7, r0, ror r1
     460:	11000000 	mrsne	r0, (UNDEF: 0)
     464:	000401d0 	ldrdeq	r0, [r4], -r0	; <UNPREDICTABLE>
     468:	0000013c 	andeq	r0, r0, ip, lsr r1
     46c:	02df5b01 	sbcseq	r5, pc, #1024	; 0x400
     470:	ae010000 	cdpge	0, 0, cr0, cr1, cr0, {0}
     474:	0c7d0213 	lfmeq	f0, 2, [sp], #-76	; 0xffffffb4
     478:	00000429 	andeq	r0, r0, r9, lsr #8
     47c:	0037b001 	eorseq	fp, r7, r1
     480:	02130000 	andseq	r0, r3, #0
     484:	043a087d 	ldrteq	r0, [sl], #-2173	; 0xfffff783
     488:	b8010000 	stmdalt	r1, {}	; <UNPREDICTABLE>
     48c:	00000037 	andeq	r0, r0, r7, lsr r0
     490:	04027c12 	streq	r7, [r2], #-3090	; 0xfffff3ee
     494:	00005400 	andeq	r5, r0, r0, lsl #8
     498:	7d021300 	stcvc	3, cr1, [r2, #-0]
     49c:	00044a04 	andeq	r4, r4, r4, lsl #20
     4a0:	46bb0100 	ldrtmi	r0, [fp], r0, lsl #2
     4a4:	00000001 	andeq	r0, r0, r1
     4a8:	030c1100 	movweq	r1, #49408	; 0xc100
     4ac:	00740004 	rsbseq	r0, r4, r4
     4b0:	5b010000 	blpl	404b8 <get_key+0x10>
     4b4:	000002ed 	andeq	r0, r0, sp, ror #5
     4b8:	1815c501 	ldmdane	r5, {r0, r8, sl, lr, pc}
     4bc:	13000000 	movwne	r0, #0
     4c0:	56077d02 	strpl	r7, [r7], -r2, lsl #26
     4c4:	01000004 	tsteq	r0, r4
     4c8:	000247c9 	andeq	r4, r2, r9, asr #15
     4cc:	16000000 	strne	r0, [r0], -r0
     4d0:	00040380 	andeq	r0, r4, r0, lsl #7
     4d4:	00000128 	andeq	r0, r0, r8, lsr #2
     4d8:	02f85b01 	rscseq	r5, r8, #1024	; 0x400
     4dc:	13010000 	movwne	r0, #4096	; 0x1000
     4e0:	7d021401 	cfstrsvc	mvf1, [r2, #-4]
     4e4:	00045d0c 	andeq	r5, r4, ip, lsl #26
     4e8:	011c0100 	tsteq	ip, r0, lsl #2
     4ec:	00000071 	andeq	r0, r0, r1, ror r0
     4f0:	087d0214 	ldmdaeq	sp!, {r2, r4, r9}^
     4f4:	00000469 	andeq	r0, r0, r9, ror #8
     4f8:	71011d01 	tstvc	r1, r1, lsl #26
     4fc:	14000000 	strne	r0, [r0], #-0
     500:	7c077d02 	stcvc	13, cr7, [r7], {2}
     504:	01000004 	tsteq	r0, r4
     508:	025f011f 	subseq	r0, pc, #-1073741817	; 0xc0000007
     50c:	17000000 	strne	r0, [r0, -r0]
     510:	000404a8 	andeq	r0, r4, r8, lsr #9
     514:	00000080 	andeq	r0, r0, r0, lsl #1
     518:	03005d01 	movweq	r5, #3329	; 0xd01
     51c:	87010000 	strhi	r0, [r1, -r0]
     520:	00003701 	andeq	r3, r0, r1, lsl #14
     524:	91021800 	tstls	r2, r0, lsl #16
     528:	00048b04 	andeq	r8, r4, r4, lsl #22
     52c:	01870100 	orreq	r0, r7, r0, lsl #2
     530:	000002d6 	ldrdeq	r0, [r0], -r6
     534:	00910214 	addseq	r0, r1, r4, lsl r2
     538:	00000799 	muleq	r0, r9, r7
     53c:	37018801 	strcc	r8, [r1, -r1, lsl #16]
     540:	00000000 	andeq	r0, r0, r0
     544:	04052819 	streq	r2, [r5], #-2073	; 0xfffff7e7
     548:	0001f800 	andeq	pc, r1, r0, lsl #16
     54c:	085b0100 	ldmdaeq	fp, {r8}^
     550:	01000003 	tsteq	r0, r3
     554:	02180132 	andseq	r0, r8, #-2147483636	; 0x8000000c
     558:	0304047d 	movweq	r0, #17533	; 0x447d
     55c:	32010000 	andcc	r0, r1, #0
     560:	0002d601 	andeq	sp, r2, r1, lsl #12
     564:	20190000 	andscs	r0, r9, r0
     568:	28000407 	stmdacs	r0, {r0, r1, r2, sl}
     56c:	01000000 	mrseq	r0, (UNDEF: 0)
     570:	0003145b 	andeq	r1, r3, fp, asr r4
     574:	01a60100 			; <UNDEFINED> instruction: 0x01a60100
     578:	047d0218 	ldrbteq	r0, [sp], #-536	; 0xfffffde8
     57c:	00000418 	andeq	r0, r0, r8, lsl r4
     580:	3701a601 	strcc	sl, [r1, -r1, lsl #12]
     584:	00000000 	andeq	r0, r0, r0
     588:	04074817 	streq	r4, [r7], #-2071	; 0xfffff7e9
     58c:	0000c400 	andeq	ip, r0, r0, lsl #8
     590:	235b0100 	cmpcs	fp, #0, 2
     594:	01000003 	tsteq	r0, r3
     598:	003701ad 	eorseq	r0, r7, sp, lsr #3
     59c:	02180000 	andseq	r0, r8, #0
     5a0:	04917891 	ldreq	r7, [r1], #2193	; 0x891
     5a4:	ad010000 	stcge	0, cr0, [r1, #-0]
     5a8:	00003701 	andeq	r3, r0, r1, lsl #14
     5ac:	7d021800 	stcvc	8, cr1, [r2, #-0]
     5b0:	0004960c 	andeq	r9, r4, ip, lsl #12
     5b4:	01ad0100 			; <UNDEFINED> instruction: 0x01ad0100
     5b8:	000005ea 	andeq	r0, r0, sl, ror #11
     5bc:	087d0214 	ldmdaeq	sp!, {r2, r4, r9}^
     5c0:	0000049b 	muleq	r0, fp, r4
     5c4:	f401b101 	vst4.8	{d11,d13,d15,d17}, [r1], r1
     5c8:	14000005 	strne	r0, [r0], #-5
     5cc:	a2047d02 	andge	r7, r4, #2, 26	; 0x80
     5d0:	01000004 	tsteq	r0, r4
     5d4:	060001b5 			; <UNDEFINED> instruction: 0x060001b5
     5d8:	02140000 	andseq	r0, r4, #0
     5dc:	03ec007d 	mvneq	r0, #125	; 0x7d
     5e0:	b9010000 	stmdblt	r1, {}	; <UNPREDICTABLE>
     5e4:	00003701 	andeq	r3, r0, r1, lsl #14
     5e8:	ef1a0000 	svc	0x001a0000
     5ec:	1a000005 	bne	608 <pthread_mutex_unlock@plt-0x10328>
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
     630:	05e40000 	strbeq	r0, [r4, #0]!
     634:	003b0000 	eorseq	r0, fp, r0
     638:	00000000 	andeq	r0, r0, r0
     63c:	00500000 	subseq	r0, r0, r0
     640:	0e1d0000 	cdpeq	0, 1, cr0, cr13, cr0, {0}
     644:	0004080c 	andeq	r0, r4, ip, lsl #16
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
     670:	08481f00 	stmdaeq	r8, {r8, r9, sl, fp, ip}^
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
     6a4:	000205ac 	andeq	r0, r2, ip, lsr #11
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
     6d0:	088c0e00 	stmeq	ip, {r9, sl, fp}
     6d4:	00300004 	eorseq	r0, r0, r4
     6d8:	5b010000 	blpl	406e0 <doKeyAction+0x1b8>
     6dc:	00000349 	andeq	r0, r0, r9, asr #6
     6e0:	021e1901 	andseq	r1, lr, #16384	; 0x4000
     6e4:	04b4047d 	ldrteq	r0, [r4], #1149	; 0x47d
     6e8:	19010000 	stmdbne	r1, {}	; <UNPREDICTABLE>
     6ec:	00000037 	andeq	r0, r0, r7, lsr r0
     6f0:	08bc2000 	ldmeq	ip!, {sp}
     6f4:	00500004 	subseq	r0, r0, r4
     6f8:	5b010000 	blpl	40700 <doKeyAction+0x1d8>
     6fc:	00000356 	andeq	r0, r0, r6, asr r3
     700:	00371e01 	eorseq	r1, r7, r1, lsl #28
     704:	02100000 	andseq	r0, r0, #0
     708:	02a7037d 	adceq	r0, r7, #-201326591	; 0xf4000001
     70c:	1f010000 	svcne	0x00010000
     710:	00000247 	andeq	r0, r0, r7, asr #4
     714:	090c2000 	stmdbeq	ip, {sp}
     718:	00200004 	eoreq	r0, r0, r4
     71c:	5b010000 	blpl	40724 <forward_target+0x4>
     720:	00000367 	andeq	r0, r0, r7, ror #6
     724:	00372b01 	eorseq	r2, r7, r1, lsl #22
     728:	02100000 	andseq	r0, r0, #0
     72c:	02a77f91 	adceq	r7, r7, #580	; 0x244
     730:	2c010000 	stccs	0, cr0, [r1], {-0}
     734:	00000247 	andeq	r0, r0, r7, asr #4
     738:	05d01f00 	ldrbeq	r1, [r0, #3840]	; 0xf00
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
     76c:	0004092c 	andeq	r0, r4, ip, lsr #18
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
     79c:	09682100 	stmdbeq	r8!, {r8, sp}^
     7a0:	00400004 	subeq	r0, r0, r4
     7a4:	5b010000 	blpl	407ac <main+0x64>
     7a8:	0000038b 	andeq	r0, r0, fp, lsl #7
     7ac:	02293f01 	eoreq	r3, r9, #1, 30
     7b0:	02130000 	andseq	r0, r3, #0
     7b4:	03f2007d 	mvnseq	r0, #125	; 0x7d
     7b8:	40010000 	andmi	r0, r1, r0
     7bc:	00000230 	andeq	r0, r0, r0, lsr r2
     7c0:	09a82100 	stmibeq	r8!, {r8, sp}
     7c4:	00300004 	eorseq	r0, r0, r4
     7c8:	5b010000 	blpl	407d0 <main+0x88>
     7cc:	00000392 	muleq	r0, r2, r3
     7d0:	02294801 	eoreq	r4, r9, #65536	; 0x10000
     7d4:	02130000 	andseq	r0, r3, #0
     7d8:	03f2007d 	mvnseq	r0, #125	; 0x7d
     7dc:	49010000 	stmdbmi	r1, {}	; <UNPREDICTABLE>
     7e0:	00000230 	andeq	r0, r0, r0, lsr r2
     7e4:	06180e00 	ldreq	r0, [r8], -r0, lsl #28
     7e8:	002c0002 	eoreq	r0, ip, r2
     7ec:	5b010000 	blpl	407f4 <main+0xac>
     7f0:	00000398 	muleq	r0, r8, r3
     7f4:	021e5101 	andseq	r5, lr, #1073741824	; 0x40000000
     7f8:	0392047d 	orrseq	r0, r2, #2097152000	; 0x7d000000
     7fc:	51010000 	mrspl	r0, (UNDEF: 1)
     800:	00000146 	andeq	r0, r0, r6, asr #2
     804:	06441f00 	strbeq	r1, [r4], -r0, lsl #30
     808:	00300002 	eorseq	r0, r0, r2
     80c:	5b010000 	blpl	40814 <pinMode+0x8>
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
     898:	074e0000 	strbeq	r0, [lr, -r0]
     89c:	003b0000 	eorseq	r0, fp, r0
     8a0:	06740000 	ldrbteq	r0, [r4], -r0
     8a4:	006c0002 	rsbeq	r0, ip, r2
     8a8:	74240000 	strtvc	r0, [r4], #-0
     8ac:	44000206 	strmi	r0, [r0], #-518	; 0xfffffdfa
     8b0:	01000000 	mrseq	r0, (UNDEF: 0)
     8b4:	0003b15b 	andeq	fp, r3, fp, asr r1
     8b8:	24070100 	strcs	r0, [r7], #-256	; 0xffffff00
     8bc:	000206b8 			; <UNDEFINED> instruction: 0x000206b8
     8c0:	00000028 	andeq	r0, r0, r8, lsr #32
     8c4:	03b85b01 			; <UNDEFINED> instruction: 0x03b85b01
     8c8:	0d010000 	stceq	0, cr0, [r1, #-0]
     8cc:	00011c00 	andeq	r1, r1, r0, lsl #24
     8d0:	00000500 	andeq	r0, r0, r0, lsl #10
     8d4:	04000000 	streq	r0, [r0], #-0
     8d8:	00000001 	andeq	r0, r0, r1
     8dc:	a9000c00 	stmdbge	r0, {sl, fp}
     8e0:	9f000002 	svcls	0x00000002
     8e4:	3b000007 	blcc	908 <pthread_mutex_unlock@plt-0x10028>
     8e8:	00000000 	andeq	r0, r0, r0
     8ec:	88000000 	stmdahi	r0, {}	; <UNPREDICTABLE>
     8f0:	0e000000 	cdpeq	0, 0, cr0, cr0, cr0, {0}
     8f4:	000409d8 	ldrdeq	r0, [r4], -r8
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
     930:	000206e0 	andeq	r0, r2, r0, ror #13
     934:	00000038 	andeq	r0, r0, r8, lsr r0
     938:	03ca5b01 	biceq	r5, sl, #1024	; 0x400
     93c:	0e010000 	cdpeq	0, 0, cr0, cr1, cr0, {0}
     940:	047d020f 	ldrbteq	r0, [sp], #-527	; 0xfffffdf1
     944:	0000020f 	andeq	r0, r0, pc, lsl #4
     948:	00fa0e01 	rscseq	r0, sl, r1, lsl #28
     94c:	0e000000 	cdpeq	0, 0, cr0, cr0, cr0, {0}
     950:	00020718 	andeq	r0, r2, r8, lsl r7
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
     98c:	00020768 	andeq	r0, r2, r8, ror #14
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
     9c4:	1a000000 	bne	9cc <pthread_mutex_unlock@plt-0xff64>
     9c8:	000000ff 	strdeq	r0, [r0], -pc	; <UNPREDICTABLE>
     9cc:	00010a08 	andeq	r0, r1, r8, lsl #20
     9d0:	00022700 	andeq	r2, r2, r0, lsl #14
     9d4:	090a0200 	stmdbeq	sl, {r9}
     9d8:	00000213 	andeq	r0, r0, r3, lsl r2
     9dc:	25080204 	strcs	r0, [r8, #-516]	; 0xfffffdfc
     9e0:	00001226 	andeq	r1, r0, r6, lsr #4
     9e4:	000002d6 	ldrdeq	r0, [r0], -r6
     9e8:	00000902 	andeq	r0, r0, r2, lsl #18
     9ec:	000a6f00 	andeq	r6, sl, r0, lsl #30
     9f0:	12000400 	andne	r0, r0, #0, 8
     9f4:	04000002 	streq	r0, [r0], #-2
     9f8:	000a3d01 	andeq	r3, sl, r1, lsl #26
     9fc:	09b00c00 	ldmibeq	r0!, {sl, fp}
     a00:	06f60000 	ldrbteq	r0, [r6], r0
     a04:	0ad80000 	beq	ff600a0c <__bss_end__+0xf5d12438>
     a08:	31e60004 	mvncc	r0, r4
     a0c:	08480000 	stmdaeq	r8, {}^	; <UNPREDICTABLE>
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
     b54:	0a200000 	beq	800b5c <ringBuffer+0x7a8e84>
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
     b88:	0a300000 	beq	c00b90 <ringBuffer+0xba8eb8>
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
     bbc:	0a400000 	beq	1000bc4 <ringBuffer+0xfa8eec>
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
     bf0:	0a480000 	beq	1200bf8 <ringBuffer+0x11a8f20>
     bf4:	0000069a 	muleq	r0, sl, r6
     bf8:	df012106 	svcle	0x00012106
     bfc:	50000000 	andpl	r0, r0, r0
     c00:	00096c0a 	andeq	r6, r9, sl, lsl #24
     c04:	01290600 			; <UNDEFINED> instruction: 0x01290600
     c08:	000000ea 	andeq	r0, r0, sl, ror #1
     c0c:	09730a58 	ldmdbeq	r3!, {r3, r4, r6, r9, fp}^
     c10:	2a060000 	bcs	180c18 <ringBuffer+0x128f40>
     c14:	0000ea01 	andeq	lr, r0, r1, lsl #20
     c18:	7a0a5c00 	bvc	297c20 <ringBuffer+0x23ff48>
     c1c:	06000009 	streq	r0, [r0], -r9
     c20:	00ea012b 	rsceq	r0, sl, fp, lsr #2
     c24:	0a600000 	beq	1800c2c <ringBuffer+0x17a8f54>
     c28:	00000981 	andeq	r0, r0, r1, lsl #19
     c2c:	ea012c06 	b	4bc4c <.cpt_dt_wt_access_tb+0x5045>
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
     d08:	aa070000 	bge	1c0d10 <ringBuffer+0x169038>
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
     ddc:	0a0b0970 	beq	2c33a4 <ringBuffer+0x26b6cc>
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
     e68:	4a090100 	bmi	241270 <ringBuffer+0x1e9598>
     e6c:	09000008 	stmdbeq	r0, {r3}
     e70:	0000415a 	andeq	r4, r0, sl, asr r1
     e74:	f3090200 	vhsub.u8	d0, d9, d0
     e78:	09000007 	stmdbeq	r0, {r0, r1, r2}
     e7c:	0000415a 	andeq	r4, r0, sl, asr r1
     e80:	70090300 	andvc	r0, r9, r0, lsl #6
     e84:	09000006 	stmdbeq	r0, {r1, r2}
     e88:	00006f5a 	andeq	r6, r0, sl, asr pc
     e8c:	1b090400 	blne	241e94 <ringBuffer+0x1ea1bc>
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
     ef0:	fa050000 	blx	140ef8 <ringBuffer+0xe9220>
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
     f20:	2a170200 	bcs	5c1728 <ringBuffer+0x569a50>
     f24:	05000005 	streq	r0, [r0, #-5]
     f28:	0466d003 	strbteq	sp, [r6], #-3
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
     f54:	0466f003 	strbteq	pc, [r6], #-3	; <UNPREDICTABLE>
     f58:	05191600 	ldreq	r1, [r9, #-1536]	; 0xfffffa00
     f5c:	09020000 	stmdbeq	r2, {}	; <UNPREDICTABLE>
     f60:	00003301 	andeq	r3, r0, r1, lsl #6
     f64:	043bf800 	ldrteq	pc, [fp], #-2048	; 0xfffff800	; <UNPREDICTABLE>
     f68:	0000c600 	andeq	ip, r0, r0, lsl #12
     f6c:	f29c0100 	vaddw.s16	q0, q6, d0
     f70:	17000005 	strne	r0, [r0, -r5]
     f74:	0074756f 	rsbseq	r7, r4, pc, ror #10
     f78:	ea010902 	b	43388 <blake2s_compress+0x24d4>
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
     fb0:	6b177ee8 	blvs	5e0b58 <ringBuffer+0x588e80>
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
     ff0:	043b2e00 	ldrteq	r2, [fp], #-3584	; 0xfffff200
     ff4:	0000ca00 	andeq	ip, r0, r0, lsl #20
     ff8:	559c0100 	ldrpl	r0, [ip, #256]	; 0x100
     ffc:	1c000006 	stcne	0, cr0, [r0], {6}
    1000:	f1020053 	cps	#19
    1004:	00000655 	andeq	r0, r0, r5, asr r6
    1008:	1c4c9102 	stfnep	f1, [ip], {2}
    100c:	0074756f 	rsbseq	r7, r4, pc, ror #10
    1010:	00eaf102 	rsceq	pc, sl, r2, lsl #2
    1014:	91020000 	mrsls	r0, (UNDEF: 2)
    1018:	0a0b1d48 	beq	2c8540 <ringBuffer+0x270868>
    101c:	f1020000 	cps	#0
    1020:	00000092 	muleq	r0, r2, r0
    1024:	15449102 	strbne	r9, [r4, #-258]	; 0xfffffefe
    1028:	000011d9 	ldrdeq	r1, [r0], -r9
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
    1060:	74000000 	strvc	r0, [r0], #-0
    1064:	ba00043a 	blt	2154 <pthread_mutex_unlock@plt-0xe7dc>
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
    10a4:	8a1f7491 	bhi	7de2f0 <ringBuffer+0x786618>
    10a8:	9a00043a 	bls	2198 <pthread_mutex_unlock@plt-0xe798>
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
    10d8:	0eb4ac02 	cdpeq	12, 11, cr10, cr4, cr2, {0}
    10dc:	2bc00004 	blcs	ff0010f4 <__bss_end__+0xf5712b20>
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
    1148:	b2000000 	andlt	r0, r0, #0
    114c:	0200040d 	andeq	r0, r0, #218103808	; 0xd000000
    1150:	01000001 	tsteq	r0, r1
    1154:	0007cc9c 	muleq	r7, ip, ip
    1158:	00531c00 	subseq	r1, r3, r0, lsl #24
    115c:	06557302 	ldrbeq	r7, [r5], -r2, lsl #6
    1160:	91030000 	mrsls	r0, (UNDEF: 3)
    1164:	0b1d7f94 	bleq	760fbc <ringBuffer+0x7092e4>
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
    11a0:	00040e74 	andeq	r0, r4, r4, ror lr
    11a4:	00000036 	andeq	r0, r0, r6, lsr r0
    11a8:	00061b15 	andeq	r1, r6, r5, lsl fp
    11ac:	298b0200 	stmibcs	fp, {r9}
    11b0:	03000004 	movweq	r0, #4
    11b4:	007f9891 			; <UNDEFINED> instruction: 0x007f9891
    11b8:	065a1b00 	ldrbeq	r1, [sl], -r0, lsl #22
    11bc:	5d020000 	stcpl	0, cr0, [r2, #-0]
    11c0:	00000033 	andeq	r0, r0, r3, lsr r0
    11c4:	00040d1c 	andeq	r0, r4, ip, lsl sp
    11c8:	00000096 	muleq	r0, r6, r0
    11cc:	080c9c01 	stmdaeq	ip, {r0, sl, fp, ip, pc}
    11d0:	531c0000 	tstpl	ip, #0
    11d4:	555d0200 	ldrbpl	r0, [sp, #-512]	; 0xfffffe00
    11d8:	02000006 	andeq	r0, r0, #6
    11dc:	0b1d5491 	bleq	756428 <ringBuffer+0x6fe750>
    11e0:	0200000a 	andeq	r0, r0, #10
    11e4:	0000925d 	andeq	r9, r0, sp, asr r2
    11e8:	50910200 	addspl	r0, r1, r0, lsl #4
    11ec:	0200501e 	andeq	r5, r0, #30
    11f0:	00050a5f 	andeq	r0, r5, pc, asr sl
    11f4:	58910200 	ldmpl	r1, {r9}
    11f8:	08f21b00 	ldmeq	r2!, {r8, r9, fp, ip}^
    11fc:	4c020000 	stcmi	0, cr0, [r2], {-0}
    1200:	00000033 	andeq	r0, r0, r3, lsr r0
    1204:	00040cc0 	andeq	r0, r4, r0, asr #25
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
    1250:	00040c7a 	andeq	r0, r4, sl, ror ip
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
    127c:	0c3e3d02 	ldceq	13, cr3, [lr], #-8
    1280:	003c0004 	eorseq	r0, ip, r4
    1284:	9c010000 	stcls	0, cr0, [r1], {-0}
    1288:	000008ba 			; <UNDEFINED> instruction: 0x000008ba
    128c:	0200531c 	andeq	r5, r0, #28, 6	; 0x70000000
    1290:	0006553d 	andeq	r5, r6, sp, lsr r5
    1294:	74910200 	ldrvc	r0, [r1], #512	; 0x200
    1298:	636e691c 	cmnvs	lr, #28, 18	; 0x70000
    129c:	7a3d0200 	bvc	f41aa4 <ringBuffer+0xee9dcc>
    12a0:	02000000 	andeq	r0, r0, #0
    12a4:	20007091 	mulcs	r0, r1, r0
    12a8:	000005c7 	andeq	r0, r0, r7, asr #11
    12ac:	0c163602 	ldceq	6, cr3, [r6], {2}
    12b0:	00280004 	eoreq	r0, r8, r4
    12b4:	9c010000 	stcls	0, cr0, [r1], {-0}
    12b8:	000008dc 	ldrdeq	r0, [r0], -ip
    12bc:	0200531c 	andeq	r5, r0, #28, 6	; 0x70000000
    12c0:	00065536 	andeq	r5, r6, r6, lsr r5
    12c4:	74910200 	ldrvc	r0, [r1], #512	; 0x200
    12c8:	060c2200 	streq	r2, [ip], -r0, lsl #4
    12cc:	31020000 	mrscc	r0, (UNDEF: 2)
    12d0:	00000033 	andeq	r0, r0, r3, lsr r0
    12d4:	00040bf4 	strdeq	r0, [r4], -r4
    12d8:	00000022 	andeq	r0, r0, r2, lsr #32
    12dc:	09029c01 	stmdbeq	r2, {r0, sl, fp, ip, pc}
    12e0:	531c0000 	tstpl	ip, #0
    12e4:	02310200 	eorseq	r0, r1, #0, 4
    12e8:	02000009 	andeq	r0, r0, #9
    12ec:	06007491 			; <UNDEFINED> instruction: 0x06007491
    12f0:	00044404 	andeq	r4, r4, r4, lsl #8
    12f4:	07cb2100 	strbeq	r2, [fp, r0, lsl #2]
    12f8:	2b020000 	blcs	81300 <ringBuffer+0x29628>
    12fc:	00040bd8 	ldrdeq	r0, [r4], -r8
    1300:	0000001c 	andeq	r0, r0, ip, lsl r0
    1304:	092a9c01 	stmdbeq	sl!, {r0, sl, fp, ip, pc}
    1308:	531c0000 	tstpl	ip, #0
    130c:	552b0200 	strpl	r0, [fp, #-512]!	; 0xfffffe00
    1310:	02000006 	andeq	r0, r0, #6
    1314:	20007491 	mulcs	r0, r1, r4
    1318:	00000542 	andeq	r0, r0, r2, asr #10
    131c:	0bb29a01 	bleq	feca7b28 <__bss_end__+0xf53b9554>
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
    1350:	0570d003 	ldrbeq	sp, [r0, #-3]!
    1354:	ea230000 	b	8c135c <ringBuffer+0x869684>
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
    1388:	0b940000 	bleq	fe501390 <__bss_end__+0xf4c12dbc>
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
    13b4:	5b010000 	blpl	413bc <blake2s_compress+0x508>
    13b8:	00040b4e 	andeq	r0, r4, lr, asr #22
    13bc:	00000046 	andeq	r0, r0, r6, asr #32
    13c0:	0a009c01 	beq	283cc <.DATA_REGION_1__bss_end+0x7bc8>
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
    13f8:	0b145001 	bleq	515404 <ringBuffer+0x4bd72c>
    13fc:	003a0004 	eorseq	r0, sl, r4
    1400:	9c010000 	stcls	0, cr0, [r1], {-0}
    1404:	00000a42 	andeq	r0, r0, r2, asr #20
    1408:	7473641c 	ldrbtvc	r6, [r3], #-1052	; 0xfffffbe4
    140c:	ea500100 	b	1401814 <ringBuffer+0x13a9b3c>
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
    1438:	0ad80000 	beq	ff601440 <__bss_end__+0xf5d12e6c>
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
    1478:	043cc000 	ldrteq	ip, [ip], #-0
    147c:	000cd800 	andeq	sp, ip, r0, lsl #16
    1480:	000b8000 	andeq	r8, fp, r0
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
    1594:	0a240000 	beq	90159c <ringBuffer+0x8a98c4>
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
    15c8:	0a340000 	beq	d015d0 <ringBuffer+0xca98f8>
    15cc:	000005ee 	andeq	r0, r0, lr, ror #11
    15d0:	5a010804 	bpl	435e8 <blake2s_compress+0x2734>
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
    15fc:	0a440000 	beq	1101604 <ringBuffer+0x10a992c>
    1600:	000008ae 	andeq	r0, r0, lr, lsr #17
    1604:	4c011304 	stcmi	3, cr1, [r1], {4}
    1608:	46000000 	strmi	r0, [r0], -r0
    160c:	0005380a 	andeq	r3, r5, sl, lsl #16
    1610:	01140400 	tsteq	r4, r0, lsl #8
    1614:	00000273 	andeq	r0, r0, r3, ror r2
    1618:	07950a47 	ldreq	r0, [r5, r7, asr #20]
    161c:	18040000 	stmdane	r4, {}	; <UNPREDICTABLE>
    1620:	00028301 	andeq	r8, r2, r1, lsl #6
    1624:	9a0a4800 	bls	29362c <ringBuffer+0x23b954>
    1628:	04000006 	streq	r0, [r0], #-6
    162c:	008c0121 	addeq	r0, ip, r1, lsr #2
    1630:	0a500000 	beq	1401638 <ringBuffer+0x13a9960>
    1634:	0000096c 	andeq	r0, r0, ip, ror #18
    1638:	9e012904 	vmlals.f16	s4, s2, s8	; <UNPREDICTABLE>
    163c:	58000000 	stmdapl	r0, {}	; <UNPREDICTABLE>
    1640:	0009730a 	andeq	r7, r9, sl, lsl #6
    1644:	012a0400 			; <UNDEFINED> instruction: 0x012a0400
    1648:	0000009e 	muleq	r0, lr, r0
    164c:	097a0a5c 	ldmdbeq	sl!, {r2, r3, r4, r6, r9, fp}^
    1650:	2b040000 	blcs	101658 <ringBuffer+0xa9980>
    1654:	00009e01 	andeq	r9, r0, r1, lsl #28
    1658:	810a6000 	mrshi	r6, (UNDEF: 10)
    165c:	04000009 	streq	r0, [r0], #-9
    1660:	009e012c 	addseq	r0, lr, ip, lsr #2
    1664:	0a640000 	beq	190166c <ringBuffer+0x18a9994>
    1668:	00000988 	andeq	r0, r0, r8, lsl #19
    166c:	25012e04 	strcs	r2, [r1, #-3588]	; 0xfffff1fc
    1670:	68000000 	stmdavs	r0, {}	; <UNPREDICTABLE>
    1674:	0007a30a 	andeq	sl, r7, sl, lsl #6
    1678:	012f0400 			; <UNDEFINED> instruction: 0x012f0400
    167c:	0000005a 	andeq	r0, r0, sl, asr r0
    1680:	098f0a6c 	stmibeq	pc, {r2, r3, r5, r6, r9, fp}	; <UNPREDICTABLE>
    1684:	31040000 	mrscc	r0, (UNDEF: 4)
    1688:	00028901 	andeq	r8, r2, r1, lsl #18
    168c:	0b007000 	bleq	1d694 <.DATA_REGION_0__data_end+0xcbc8>
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
    1708:	bd0f0000 	stclt	0, cr0, [pc, #-0]	; 1710 <pthread_mutex_unlock@plt-0xf220>
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
    176c:	1b060000 	blne	181774 <ringBuffer+0x129a9c>
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
    17a4:	0be00900 	bleq	ff803bac <__bss_end__+0xf5f155d8>
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
    17e0:	0011d909 	andseq	sp, r1, r9, lsl #18
    17e4:	ab180100 	blge	601bec <ringBuffer+0x5a9f14>
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
    1834:	7cd80305 	ldclvc	3, cr0, [r8], {5}
    1838:	8f100005 	svchi	0x00100005
    183c:	01000000 	mrseq	r0, (UNDEF: 0)
    1840:	00005a4c 	andeq	r5, r0, ip, asr #20
    1844:	009e1000 	addseq	r1, lr, r0
    1848:	4d010000 	stcmi	0, cr0, [r1, #-0]
    184c:	0000005a 	andeq	r0, r0, sl, asr r0
    1850:	000d0216 	andeq	r0, sp, r6, lsl r2
    1854:	5a500100 	bpl	1401c5c <ringBuffer+0x13a9f84>
    1858:	05000000 	streq	r0, [r0, #-0]
    185c:	057c9003 	ldrbeq	r9, [ip, #-3]!
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
    18a4:	0a004547 	beq	12dc8 <.DATA_REGION_0__data_end+0x22fc>
    18a8:	00544c18 	subseq	r4, r4, r8, lsl ip
    18ac:	5447180b 	strbpl	r1, [r7], #-2059	; 0xfffff7f5
    18b0:	4c180c00 	ldcmi	12, cr0, [r8], {-0}
    18b4:	180d0045 	stmdane	sp, {r0, r2, r6}
    18b8:	0e004c41 	cdpeq	12, 0, cr4, cr0, cr1, {2}
    18bc:	0cdd1900 			; <UNDEFINED> instruction: 0x0cdd1900
    18c0:	9d010000 	stcls	0, cr0, [r1, #-0]
    18c4:	00005a02 	andeq	r5, r0, r2, lsl #20
    18c8:	e0030500 	and	r0, r3, r0, lsl #10
    18cc:	1a098ee4 	bne	265464 <ringBuffer+0x20d78c>
    18d0:	00746e63 	rsbseq	r6, r4, r3, ror #28
    18d4:	5a02ab01 	bpl	ac4e0 <ringBuffer+0x54808>
    18d8:	05000000 	streq	r0, [r0, #-0]
    18dc:	057c9403 	ldrbeq	r9, [ip, #-1027]!	; 0xfffffbfd
    18e0:	0bfb1b00 	bleq	ffec84e8 <__bss_end__+0xf65d9f14>
    18e4:	ae010000 	cdpge	0, 0, cr0, cr1, cr0, {0}
    18e8:	04496c02 	strbeq	r6, [r9], #-3074	; 0xfffff3fe
    18ec:	00002c00 	andeq	r2, r0, r0, lsl #24
    18f0:	1b9c0100 	blne	fe701cf8 <__bss_end__+0xf4e13724>
    18f4:	00000cf6 	strdeq	r0, [r0], -r6
    18f8:	5602a601 	strpl	sl, [r2], -r1, lsl #12
    18fc:	16000449 	strne	r0, [r0], -r9, asr #8
    1900:	01000000 	mrseq	r0, (UNDEF: 0)
    1904:	0dc01c9c 	stcleq	12, cr1, [r0, #624]	; 0x270
    1908:	9f010000 	svcls	0x00010000
    190c:	00005a02 	andeq	r5, r0, r2, lsl #20
    1910:	04494000 	strbeq	r4, [r9], #-0
    1914:	00001600 	andeq	r1, r0, r0, lsl #12
    1918:	cf9c0100 	svcgt	0x009c0100
    191c:	1d000004 	stcne	0, cr0, [r0, #-16]
    1920:	0000031c 	andeq	r0, r0, ip, lsl r3
    1924:	5a029f01 	bpl	a9530 <ringBuffer+0x51858>
    1928:	02000000 	andeq	r0, r0, #0
    192c:	1e007491 	mcrne	4, 0, r7, cr0, cr1, {4}
    1930:	00000c64 	andeq	r0, r0, r4, ror #24
    1934:	a8027c01 	stmdage	r2, {r0, sl, fp, ip, sp, lr}
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
    1990:	0bac1e00 	bleq	feb09198 <__bss_end__+0xf521abc4>
    1994:	5a010000 	bpl	4199c <blake2s_compress+0xae8>
    1998:	04480802 	strbeq	r0, [r8], #-2050	; 0xfffff7fe
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
    19c4:	0d5f1d50 	ldcleq	13, cr1, [pc, #-320]	; 188c <pthread_mutex_unlock@plt-0xf0a4>
    19c8:	5a010000 	bpl	419d0 <blake2s_compress+0xb1c>
    19cc:	00032602 	andeq	r2, r3, r2, lsl #12
    19d0:	4c910200 	lfmmi	f0, 4, [r1], {0}
    19d4:	000bbd1f 	andeq	fp, fp, pc, lsl sp
    19d8:	02630100 	rsbeq	r0, r3, #0, 2
    19dc:	00000314 	andeq	r0, r0, r4, lsl r3
    19e0:	1f6f9102 	svcne	0x006f9102
    19e4:	00000c88 	andeq	r0, r0, r8, lsl #25
    19e8:	6a026501 	bvs	9adf4 <ringBuffer+0x4311c>
    19ec:	02000003 	andeq	r0, r0, #3
    19f0:	1e005c91 	mcrne	12, 0, r5, cr0, cr1, {4}
    19f4:	00000be9 	andeq	r0, r0, r9, ror #23
    19f8:	e8021801 	stmda	r2, {r0, fp, ip}
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
    1a34:	bd1f4c91 	ldclt	12, cr4, [pc, #-580]	; 17f8 <pthread_mutex_unlock@plt-0xf138>
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
    1a6c:	00044644 	andeq	r4, r4, r4, asr #12
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
    1ab0:	00044528 	andeq	r4, r4, r8, lsr #10
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
    1af4:	0004444c 	andeq	r4, r4, ip, asr #8
    1af8:	000000dc 	ldrdeq	r0, [r0], -ip
    1afc:	06d09c01 	ldrbeq	r9, [r0], r1, lsl #24
    1b00:	171d0000 	ldrne	r0, [sp, -r0]
    1b04:	0100000c 	tsteq	r0, ip
    1b08:	03260170 			; <UNDEFINED> instruction: 0x03260170
    1b0c:	91020000 	mrsls	r0, (UNDEF: 2)
    1b10:	0d691f54 	stcleq	15, cr1, [r9, #-336]!	; 0xfffffeb0
    1b14:	7b010000 	blvc	41b1c <blake2s_compress+0xc68>
    1b18:	00032601 	andeq	r2, r3, r1, lsl #12
    1b1c:	6c910200 	lfmvs	f0, 4, [r1], {0}
    1b20:	000c881f 	andeq	r8, ip, pc, lsl r8
    1b24:	017e0100 	cmneq	lr, r0, lsl #2
    1b28:	0000036a 	andeq	r0, r0, sl, ror #6
    1b2c:	005c9102 	subseq	r9, ip, r2, lsl #2
    1b30:	000cc41e 	andeq	ip, ip, lr, lsl r4
    1b34:	013f0100 	teqeq	pc, r0, lsl #2
    1b38:	000443a0 	andeq	r4, r4, r0, lsr #7
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
    1b78:	7cf50100 	ldfvce	f0, [r5]
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
    1ba4:	0d5f2140 	ldfeqe	f2, [pc, #-256]	; 1aac <pthread_mutex_unlock@plt-0xee84>
    1ba8:	f5010000 			; <UNDEFINED> instruction: 0xf5010000
    1bac:	00000326 	andeq	r0, r0, r6, lsr #6
    1bb0:	7fbc9103 	svcvc	0x00bc9103
    1bb4:	000bbd22 	andeq	fp, fp, r2, lsr #26
    1bb8:	14ff0100 	ldrbtne	r0, [pc], #256	; 1bc0 <pthread_mutex_unlock@plt-0xed70>
    1bbc:	02000003 	andeq	r0, r0, #3
    1bc0:	691f6f91 	ldmdbvs	pc, {r0, r4, r7, r8, r9, sl, fp, sp, lr}	; <UNPREDICTABLE>
    1bc4:	0100000d 	tsteq	r0, sp
    1bc8:	03260103 			; <UNDEFINED> instruction: 0x03260103
    1bcc:	91020000 	mrsls	r0, (UNDEF: 2)
    1bd0:	0c881f68 	stceq	15, cr1, [r8], {104}	; 0x68
    1bd4:	25010000 	strcs	r0, [r1, #-0]
    1bd8:	00036a01 	andeq	r6, r3, r1, lsl #20
    1bdc:	58910200 	ldmpl	r1, {r9}
    1be0:	0442cc23 	strbeq	ip, [r2], #-3107	; 0xfffff3dd
    1be4:	00004400 	andeq	r4, r0, r0, lsl #8
    1be8:	0c111f00 	ldceq	15, cr1, [r1], {-0}
    1bec:	0a010000 	beq	41bf4 <blake2s_compress+0xd40>
    1bf0:	00036a01 	andeq	r6, r3, r1, lsl #20
    1bf4:	48910200 	ldmmi	r1, {r9}
    1bf8:	1c200000 	stcne	0, cr0, [r0], #-0
    1bfc:	0100000d 	tsteq	r0, sp
    1c00:	044160a7 	strbeq	r6, [r1], #-167	; 0xffffff59
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
    1c64:	0441aa23 	strbeq	sl, [r1], #-2595	; 0xfffff5dd
    1c68:	00004600 	andeq	r4, r0, r0, lsl #12
    1c6c:	0c112200 	lfmeq	f2, 4, [r1], {-0}
    1c70:	bf010000 	svclt	0x00010000
    1c74:	0000036a 	andeq	r0, r0, sl, ror #6
    1c78:	00489102 	subeq	r9, r8, r2, lsl #2
    1c7c:	0b952400 	bleq	fe54ac84 <__bss_end__+0xf4c5c6b0>
    1c80:	8b010000 	blhi	41c88 <blake2s_compress+0xdd4>
    1c84:	00000314 	andeq	r0, r0, r4, lsl r3
    1c88:	00043fa0 	andeq	r3, r4, r0, lsr #31
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
    1cbc:	5a257791 	bpl	95fb08 <ringBuffer+0x907e30>
    1cc0:	148d0100 	strne	r0, [sp], #256	; 0x100
    1cc4:	02000003 	andeq	r0, r0, #3
    1cc8:	43257691 			; <UNDEFINED> instruction: 0x43257691
    1ccc:	148e0100 	strne	r0, [lr], #256	; 0x100
    1cd0:	02000003 	andeq	r0, r0, #3
    1cd4:	56257591 			; <UNDEFINED> instruction: 0x56257591
    1cd8:	148f0100 	strne	r0, [pc], #256	; 1ce0 <pthread_mutex_unlock@plt-0xec50>
    1cdc:	02000003 	andeq	r0, r0, #3
    1ce0:	20007491 	mulcs	r0, r1, r4
    1ce4:	00000b7e 	andeq	r0, r0, lr, ror fp
    1ce8:	3f005601 	svccc	0x00005601
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
    1d18:	6a630100 	bvs	18c2120 <ringBuffer+0x186a448>
    1d1c:	02000003 	andeq	r0, r0, #3
    1d20:	26005c91 			; <UNDEFINED> instruction: 0x26005c91
    1d24:	00000c95 	muleq	r0, r5, ip
    1d28:	03264501 			; <UNDEFINED> instruction: 0x03264501
    1d2c:	3ee80000 	cdpcc	0, 14, cr0, cr8, cr0, {0}
    1d30:	00180004 	andseq	r0, r8, r4
    1d34:	9c010000 	stcls	0, cr0, [r1], {-0}
    1d38:	000008eb 	andeq	r0, r0, fp, ror #17
    1d3c:	000d6c22 	andeq	r6, sp, r2, lsr #24
    1d40:	26460100 	strbcs	r0, [r6], -r0, lsl #2
    1d44:	02000003 	andeq	r0, r0, #3
    1d48:	24007491 	strcs	r7, [r0], #-1169	; 0xfffffb6f
    1d4c:	00000c78 	andeq	r0, r0, r8, ror ip
    1d50:	03143d01 	tsteq	r4, #1, 26	; 0x40
    1d54:	3ea20000 	cdpcc	0, 10, cr0, cr2, cr0, {0}
    1d58:	00460004 	subeq	r0, r6, r4
    1d5c:	9c010000 	stcls	0, cr0, [r1], {-0}
    1d60:	00000963 	andeq	r0, r0, r3, ror #18
    1d64:	000d9a21 	andeq	r9, sp, r1, lsr #20
    1d68:	633d0100 	teqvs	sp, #0, 2
    1d6c:	02000009 	andeq	r0, r0, #9
    1d70:	aa276491 	bge	9dafbc <ringBuffer+0x9832e4>
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
    1d9c:	043ec223 	ldrteq	ip, [lr], #-547	; 0xfffffddd
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
    1dd8:	3e500000 	cdpcc	0, 5, cr0, cr0, cr0, {0}
    1ddc:	00520004 	subseq	r0, r2, r4
    1de0:	9c010000 	stcls	0, cr0, [r1], {-0}
    1de4:	00000997 	muleq	r0, r7, r9
    1de8:	000d9a21 	andeq	r9, sp, r1, lsr #20
    1dec:	63380100 	teqvs	r8, #0, 2
    1df0:	02000009 	andeq	r0, r0, #9
    1df4:	28006c91 	stmdacs	r0, {r0, r4, r7, sl, fp, sp, lr}
    1df8:	00706f70 	rsbseq	r6, r0, r0, ror pc
    1dfc:	03142c01 	tsteq	r4, #256	; 0x100
    1e00:	3d820000 	stccc	0, cr0, [r2]
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
    1e2c:	043d8c27 	ldrteq	r8, [sp], #-3111	; 0xfffff3d9
    1e30:	00001e00 	andeq	r1, r0, r0, lsl #28
    1e34:	0009f600 	andeq	pc, r9, r0, lsl #12
    1e38:	0d722200 	lfmeq	f2, 2, [r2, #-0]
    1e3c:	2d010000 	stccs	0, cr0, [r1, #-0]
    1e40:	00000969 	andeq	r0, r0, r9, ror #18
    1e44:	22749102 	rsbscs	r9, r4, #-2147483648	; 0x80000000
    1e48:	00000ae2 	andeq	r0, r0, r2, ror #21
    1e4c:	00252d01 	eoreq	r2, r5, r1, lsl #26
    1e50:	91020000 	mrsls	r0, (UNDEF: 2)
    1e54:	aa270064 	bge	9c1fec <ringBuffer+0x96a314>
    1e58:	1e00043d 	cfmvdhrne	mvd0, r0
    1e5c:	20000000 	andcs	r0, r0, r0
    1e60:	2200000a 	andcs	r0, r0, #10
    1e64:	00000d72 	andeq	r0, r0, r2, ror sp
    1e68:	09692d01 	stmdbeq	r9!, {r0, r8, sl, fp, sp}^
    1e6c:	91020000 	mrsls	r0, (UNDEF: 2)
    1e70:	0ae22270 	beq	ff88a838 <__bss_end__+0xf5f9c264>
    1e74:	2d010000 	stccs	0, cr0, [r1, #-0]
    1e78:	00000025 	andeq	r0, r0, r5, lsr #32
    1e7c:	00609102 	rsbeq	r9, r0, r2, lsl #2
    1e80:	043dee23 	ldrteq	lr, [sp], #-3619	; 0xfffff1dd
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
    1eb8:	00043cc0 	andeq	r3, r4, r0, asr #25
    1ebc:	000000c2 	andeq	r0, r0, r2, asr #1
    1ec0:	9a219c01 	bls	868ecc <ringBuffer+0x8111f4>
    1ec4:	0100000d 	tsteq	r0, sp
    1ec8:	00096320 	andeq	r6, r9, r0, lsr #6
    1ecc:	4c910200 	lfmmi	f0, 4, [r1], {0}
    1ed0:	000d6c21 	andeq	r6, sp, r1, lsr #24
    1ed4:	6a200100 	bvs	8022dc <ringBuffer+0x7aa604>
    1ed8:	02000003 	andeq	r0, r0, #3
    1edc:	5a227491 	bpl	89f128 <ringBuffer+0x847450>
    1ee0:	0100000c 	tsteq	r0, ip
    1ee4:	00002521 	andeq	r2, r0, r1, lsr #10
    1ee8:	64910200 	ldrvs	r0, [r1], #512	; 0x200
    1eec:	043d0c27 	ldrteq	r0, [sp], #-3111	; 0xfffff3d9
    1ef0:	00001e00 	andeq	r1, r0, r0, lsl #28
    1ef4:	000ab600 	andeq	fp, sl, r0, lsl #12
    1ef8:	0d722200 	lfmeq	f2, 2, [r2, #-0]
    1efc:	22010000 	andcs	r0, r1, #0
    1f00:	00000969 	andeq	r0, r0, r9, ror #18
    1f04:	22609102 	rsbcs	r9, r0, #-2147483648	; 0x80000000
    1f08:	00000ae2 	andeq	r0, r0, r2, ror #21
    1f0c:	00252201 	eoreq	r2, r5, r1, lsl #4
    1f10:	91020000 	mrsls	r0, (UNDEF: 2)
    1f14:	50230054 	eorpl	r0, r3, r4, asr r0
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
    1f48:	0f970104 	svceq	0x00970104
    1f4c:	71380000 	teqvc	r8, r0
    1f50:	7c7c0005 	ldclvc	0, cr0, [ip], #-20	; 0xffffffec
    1f54:	2e2e0005 	cdpcs	0, 2, cr0, cr14, cr5, {0}
    1f58:	2f2e2e2f 	svccs	0x002e2e2f
    1f5c:	6d617274 	sfmvs	f7, 2, [r1, #-464]!	; 0xfffffe30
    1f60:	696c6f70 	stmdbvs	ip!, {r4, r5, r6, r8, r9, sl, fp, sp, lr}^
    1f64:	6c5f656e 	cfldr64vs	mvdx6, [pc], {110}	; 0x6e
    1f68:	742f6269 	strtvc	r6, [pc], #-617	; 1f70 <pthread_mutex_unlock@plt-0xe9c0>
    1f6c:	706d6172 	rsbvc	r6, sp, r2, ror r1
    1f70:	6e696c6f 	cdpvs	12, 6, cr6, cr9, cr15, {3}
    1f74:	77665f65 	strbvc	r5, [r6, -r5, ror #30]!
    1f78:	2f00532e 	svccs	0x0000532e
    1f7c:	656d6f68 	strbvs	r6, [sp, #-3944]!	; 0xfffff098
    1f80:	7a727a2f 	bvc	1ca0844 <ringBuffer+0x1c48b6c>
    1f84:	37313530 			; <UNDEFINED> instruction: 0x37313530
    1f88:	7574732f 	ldrbvc	r7, [r4, #-815]!	; 0xfffffcd1
    1f8c:	632f7964 			; <UNDEFINED> instruction: 0x632f7964
    1f90:	6e696168 	powvsez	f6, f1, #0.0
    1f94:	7474615f 	ldrbtvc	r6, [r4], #-351	; 0xfffffea1
    1f98:	61747365 	cmnvs	r4, r5, ror #6
    1f9c:	6e6f6974 			; <UNDEFINED> instruction: 0x6e6f6974
    1fa0:	4952412f 	ldmdbmi	r2, {r0, r1, r2, r3, r5, r8, lr}^
    1fa4:	7a727a2d 	bvc	1ca0860 <ringBuffer+0x1c48b88>
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
    1fdc:	68010400 	stmdavs	r1, {sl}
    1fe0:	30000012 	andcc	r0, r0, r2, lsl r0
    1fe4:	28000463 	stmdacs	r0, {r0, r1, r5, r6, sl}
    1fe8:	2e000464 	cdpcs	4, 0, cr0, cr0, cr4, {3}
    1fec:	2e2e2f2e 	cdpcs	15, 2, cr2, cr14, cr14, {1}
    1ff0:	6172742f 	cmnvs	r2, pc, lsr #8
    1ff4:	6c6f706d 	stclvs	0, cr7, [pc], #-436	; 1e48 <pthread_mutex_unlock@plt-0xeae8>
    1ff8:	5f656e69 	svcpl	0x00656e69
    1ffc:	2f62696c 	svccs	0x0062696c
    2000:	6d617274 	sfmvs	f7, 2, [r1, #-464]!	; 0xfffffe30
    2004:	696c6f70 	stmdbvs	ip!, {r4, r5, r6, r8, r9, sl, fp, sp, lr}^
    2008:	532e656e 			; <UNDEFINED> instruction: 0x532e656e
    200c:	6f682f00 	svcvs	0x00682f00
    2010:	7a2f656d 	bvc	bdb5cc <ringBuffer+0xb838f4>
    2014:	35307a72 	ldrcc	r7, [r0, #-2674]!	; 0xfffff58e
    2018:	732f3731 			; <UNDEFINED> instruction: 0x732f3731
    201c:	79647574 	stmdbvc	r4!, {r2, r4, r5, r6, r8, sl, ip, sp, lr}^
    2020:	6168632f 	cmnvs	r8, pc, lsr #6
    2024:	615f6e69 	cmpvs	pc, r9, ror #28
    2028:	73657474 	cmnvc	r5, #116, 8	; 0x74000000
    202c:	69746174 	ldmdbvs	r4!, {r2, r4, r5, r6, r8, sp, lr}^
    2030:	412f6e6f 			; <UNDEFINED> instruction: 0x412f6e6f
    2034:	7a2d4952 	bvc	b54584 <ringBuffer+0xafc8ac>
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
    2064:	000dc180 	andeq	ip, sp, r0, lsl #3
    2068:	cd000400 	cfstrsgt	mvf0, [r0, #-0]
    206c:	04000006 	streq	r0, [r0], #-6
    2070:	00102301 	andseq	r2, r0, r1, lsl #6
    2074:	0eab1d00 	cdpeq	13, 10, cr1, cr11, cr0, {0}
    2078:	003b0000 	eorseq	r0, fp, r0
    207c:	49980000 	ldmibmi	r8, {}	; <UNPREDICTABLE>
    2080:	06640004 	strbteq	r0, [r4], -r4
    2084:	12f60000 	rscsne	r0, r6, #0
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
    20d8:	7a830200 	bvc	fe0c28e0 <__bss_end__+0xf47d430c>
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
    2118:	000010b4 	strheq	r1, [r0], -r4
    211c:	be022204 	cdplt	2, 0, cr2, cr2, cr4, {0}
    2120:	06000000 	streq	r0, [r0], -r0
    2124:	00009504 	andeq	r9, r0, r4, lsl #10
    2128:	0f000900 	svceq	0x00000900
    212c:	39050000 	stmdbcc	r5, {}	; <UNPREDICTABLE>
    2130:	00000095 	muleq	r0, r5, r0
    2134:	000fec09 	andeq	lr, pc, r9, lsl #24
    2138:	4f470500 	svcmi	0x00470500
    213c:	09000000 	stmdbeq	r0, {}	; <UNPREDICTABLE>
    2140:	000011cb 	andeq	r1, r0, fp, asr #3
    2144:	004f4c05 	subeq	r4, pc, r5, lsl #24
    2148:	6f090000 	svcvs	0x00090000
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
    2180:	10060800 	andne	r0, r6, r0, lsl #16
    2184:	2d060000 	stccs	0, cr0, [r6, #-0]
    2188:	00010c01 	andeq	r0, r1, r1, lsl #24
    218c:	10070800 	andne	r0, r7, r0, lsl #16
    2190:	2e060000 	cdpcs	0, 0, cr0, cr6, cr0, {0}
    2194:	00010c01 	andeq	r0, r1, r1, lsl #24
    2198:	08160400 	ldmdaeq	r6, {sl}
    219c:	30070000 	andcc	r0, r7, r0
    21a0:	0000013f 	andeq	r0, r0, pc, lsr r1
    21a4:	0008120e 	andeq	r1, r8, lr, lsl #4
    21a8:	f1089800 			; <UNDEFINED> instruction: 0xf1089800
    21ac:	000002bc 			; <UNDEFINED> instruction: 0x000002bc
    21b0:	0006330f 	andeq	r3, r6, pc, lsl #6
    21b4:	4ff20800 	svcmi	0x00f20800
    21b8:	00000000 	andeq	r0, r0, r0
    21bc:	0005000f 	andeq	r0, r5, pc
    21c0:	95f70800 	ldrbls	r0, [r7, #2048]!	; 0x800
    21c4:	04000000 	streq	r0, [r0], #-0
    21c8:	0005f60f 	andeq	pc, r5, pc, lsl #12
    21cc:	95f80800 	ldrbls	r0, [r8, #2048]!	; 0x800
    21d0:	08000000 	stmdaeq	r0, {}	; <UNPREDICTABLE>
    21d4:	0009470f 	andeq	r4, r9, pc, lsl #14
    21d8:	95f90800 	ldrbls	r0, [r9, #2048]!	; 0x800
    21dc:	0c000000 	stceq	0, cr0, [r0], {-0}
    21e0:	000a290f 	andeq	r2, sl, pc, lsl #18
    21e4:	95fa0800 	ldrbls	r0, [sl, #2048]!	; 0x800
    21e8:	10000000 	andne	r0, r0, r0
    21ec:	0007250f 	andeq	r2, r7, pc, lsl #10
    21f0:	95fb0800 	ldrbls	r0, [fp, #2048]!	; 0x800
    21f4:	14000000 	strne	r0, [r0], #-0
    21f8:	0007e00f 	andeq	lr, r7, pc
    21fc:	95fc0800 	ldrbls	r0, [ip, #2048]!	; 0x800
    2200:	18000000 	stmdane	r0, {}	; <UNPREDICTABLE>
    2204:	00056c0f 	andeq	r6, r5, pc, lsl #24
    2208:	95fd0800 	ldrbls	r0, [sp, #2048]!	; 0x800
    220c:	1c000000 	stcne	0, cr0, [r0], {-0}
    2210:	0006420f 	andeq	r4, r6, pc, lsl #4
    2214:	95fe0800 	ldrbls	r0, [lr, #2048]!	; 0x800
    2218:	20000000 	andcs	r0, r0, r0
    221c:	00078710 	andeq	r8, r7, r0, lsl r7
    2220:	01000800 	tsteq	r0, r0, lsl #16
    2224:	00000095 	muleq	r0, r5, r0
    2228:	09c61024 	stmibeq	r6, {r2, r5, ip}^
    222c:	01080000 	mrseq	r0, (UNDEF: 8)
    2230:	00009501 	andeq	r9, r0, r1, lsl #10
    2234:	55102800 	ldrpl	r2, [r0, #-2048]	; 0xfffff800
    2238:	08000009 	stmdaeq	r0, {r0, r3}
    223c:	00950102 	addseq	r0, r5, r2, lsl #2
    2240:	102c0000 	eorne	r0, ip, r0
    2244:	00000841 	andeq	r0, r0, r1, asr #16
    2248:	f4010408 	vst3.8	{d0-d2}, [r1], r8
    224c:	30000002 	andcc	r0, r0, r2
    2250:	00050d10 	andeq	r0, r5, r0, lsl sp
    2254:	01060800 	tsteq	r6, r0, lsl #16
    2258:	000002fa 	strdeq	r0, [r0], -sl
    225c:	05ee1034 	strbeq	r1, [lr, #52]!	; 0x34
    2260:	08080000 	stmdaeq	r8, {}	; <UNPREDICTABLE>
    2264:	00004f01 	andeq	r4, r0, r1, lsl #30
    2268:	9b103800 	blls	410270 <ringBuffer+0x3b8598>
    226c:	08000007 	stmdaeq	r0, {r0, r1, r2}
    2270:	004f010c 	subeq	r0, pc, ip, lsl #2
    2274:	103c0000 	eorsne	r0, ip, r0
    2278:	00000696 	muleq	r0, r6, r6
    227c:	6f010e08 	svcvs	0x00010e08
    2280:	40000000 	andmi	r0, r0, r0
    2284:	00064e10 	andeq	r4, r6, r0, lsl lr
    2288:	01120800 	tsteq	r2, r0, lsl #16
    228c:	0000002c 	andeq	r0, r0, ip, lsr #32
    2290:	08ae1044 	stmiaeq	lr!, {r2, r6, ip}
    2294:	13080000 	movwne	r0, #32768	; 0x8000
    2298:	00004101 	andeq	r4, r0, r1, lsl #2
    229c:	38104600 	ldmdacc	r0, {r9, sl, lr}
    22a0:	08000005 	stmdaeq	r0, {r0, r2}
    22a4:	03000114 	movweq	r0, #276	; 0x114
    22a8:	10470000 	subne	r0, r7, r0
    22ac:	00000795 	muleq	r0, r5, r7
    22b0:	10011808 	andne	r1, r1, r8, lsl #16
    22b4:	48000003 	stmdami	r0, {r0, r1}
    22b8:	00069a10 	andeq	r9, r6, r0, lsl sl
    22bc:	01210800 			; <UNDEFINED> instruction: 0x01210800
    22c0:	00000081 	andeq	r0, r0, r1, lsl #1
    22c4:	096c1050 	stmdbeq	ip!, {r4, r6, ip}^
    22c8:	29080000 	stmdbcs	r8, {}	; <UNPREDICTABLE>
    22cc:	00009301 	andeq	r9, r0, r1, lsl #6
    22d0:	73105800 	tstvc	r0, #0, 16
    22d4:	08000009 	stmdaeq	r0, {r0, r3}
    22d8:	0093012a 	addseq	r0, r3, sl, lsr #2
    22dc:	105c0000 	subsne	r0, ip, r0
    22e0:	0000097a 	andeq	r0, r0, sl, ror r9
    22e4:	93012b08 	movwls	r2, #6920	; 0x1b08
    22e8:	60000000 	andvs	r0, r0, r0
    22ec:	00098110 	andeq	r8, r9, r0, lsl r1
    22f0:	012c0800 			; <UNDEFINED> instruction: 0x012c0800
    22f4:	00000093 	muleq	r0, r3, r0
    22f8:	09881064 	stmibeq	r8, {r2, r5, r6, ip}
    22fc:	2e080000 	cdpcs	0, 0, cr0, cr8, cr0, {0}
    2300:	0000a701 	andeq	sl, r0, r1, lsl #14
    2304:	a3106800 	tstge	r0, #0, 16
    2308:	08000007 	stmdaeq	r0, {r0, r1, r2}
    230c:	004f012f 	subeq	r0, pc, pc, lsr #2
    2310:	106c0000 	rsbne	r0, ip, r0
    2314:	0000098f 	andeq	r0, r0, pc, lsl #19
    2318:	16013108 	strne	r3, [r1], -r8, lsl #2
    231c:	70000003 	andvc	r0, r0, r3
    2320:	08071100 	stmdaeq	r7, {r8, ip}
    2324:	96080000 	strls	r0, [r8], -r0
    2328:	0006d40e 	andeq	sp, r6, lr, lsl #8
    232c:	9c080c00 	stcls	12, cr0, [r8], {-0}
    2330:	000002f4 	strdeq	r0, [r0], -r4
    2334:	0009370f 	andeq	r3, r9, pc, lsl #14
    2338:	f49d0800 			; <UNDEFINED> instruction: 0xf49d0800
    233c:	00000002 	andeq	r0, r0, r2
    2340:	00074d0f 	andeq	r4, r7, pc, lsl #26
    2344:	fa9e0800 	blx	fe78434c <__bss_end__+0xf4e95d78>
    2348:	04000002 	streq	r0, [r0], #-2
    234c:	0008300f 	andeq	r3, r8, pc
    2350:	4fa20800 	svcmi	0x00a20800
    2354:	08000000 	stmdaeq	r0, {}	; <UNPREDICTABLE>
    2358:	c3040600 	movwgt	r0, #17920	; 0x4600
    235c:	06000002 	streq	r0, [r0], -r2
    2360:	00013f04 	andeq	r3, r1, r4, lsl #30
    2364:	009b0c00 	addseq	r0, fp, r0, lsl #24
    2368:	03100000 	tsteq	r0, #0
    236c:	8c0d0000 	stchi	0, cr0, [sp], {-0}
    2370:	00000000 	andeq	r0, r0, r0
    2374:	bc040600 	stclt	6, cr0, [r4], {-0}
    2378:	0c000002 	stceq	0, cr0, [r0], {2}
    237c:	0000009b 	muleq	r0, fp, r0
    2380:	00000326 	andeq	r0, r0, r6, lsr #6
    2384:	00008c0d 	andeq	r8, r0, sp, lsl #24
    2388:	12002700 	andne	r2, r0, #0, 14
    238c:	00000717 	andeq	r0, r0, r7, lsl r7
    2390:	0007b008 	andeq	fp, r7, r8
    2394:	013b0800 	teqeq	fp, r0, lsl #16
    2398:	00000326 	andeq	r0, r0, r6, lsr #6
    239c:	0008bd08 	andeq	fp, r8, r8, lsl #26
    23a0:	013c0800 	teqeq	ip, r0, lsl #16
    23a4:	00000326 	andeq	r0, r0, r6, lsr #6
    23a8:	00055c08 	andeq	r5, r5, r8, lsl #24
    23ac:	013d0800 	teqeq	sp, r0, lsl #16
    23b0:	00000326 	andeq	r0, r0, r6, lsr #6
    23b4:	0006df09 	andeq	sp, r6, r9, lsl #30
    23b8:	faa80700 	blx	fea03fc0 <__bss_end__+0xf51159ec>
    23bc:	09000002 	stmdbeq	r0, {r1}
    23c0:	000007a9 	andeq	r0, r0, r9, lsr #15
    23c4:	02faa907 	rscseq	sl, sl, #114688	; 0x1c000
    23c8:	98090000 	stmdals	r9, {}	; <UNPREDICTABLE>
    23cc:	07000009 	streq	r0, [r0, -r9]
    23d0:	0002faaa 	andeq	pc, r2, sl, lsr #21
    23d4:	07440900 	strbeq	r0, [r4, -r0, lsl #18]
    23d8:	1a090000 	bne	2423e0 <ringBuffer+0x1ea708>
    23dc:	0000004f 	andeq	r0, r0, pc, asr #32
    23e0:	0001170c 	andeq	r1, r1, ip, lsl #14
    23e4:	00038600 	andeq	r8, r3, r0, lsl #12
    23e8:	07001300 	streq	r1, [r0, -r0, lsl #6]
    23ec:	0000037b 	andeq	r0, r0, fp, ror r3
    23f0:	00083509 	andeq	r3, r8, r9, lsl #10
    23f4:	861b0900 	ldrhi	r0, [fp], -r0, lsl #18
    23f8:	04000003 	streq	r0, [r0], #-3
    23fc:	00000fba 			; <UNDEFINED> instruction: 0x00000fba
    2400:	004f9503 	subeq	r9, pc, r3, lsl #10
    2404:	08020000 	stmdaeq	r2, {}	; <UNPREDICTABLE>
    2408:	0007bf04 	andeq	fp, r7, r4, lsl #30
    240c:	00931400 	addseq	r1, r3, r0, lsl #8
    2410:	03b70000 			; <UNDEFINED> instruction: 0x03b70000
    2414:	96150000 	ldrls	r0, [r5], -r0
    2418:	00000003 	andeq	r0, r0, r3
    241c:	0011b909 	andseq	fp, r1, r9, lsl #18
    2420:	c2470a00 	subgt	r0, r7, #0, 20
    2424:	06000003 	streq	r0, [r0], -r3
    2428:	0003a804 	andeq	sl, r3, r4, lsl #16
    242c:	12500900 	subsne	r0, r0, #0, 18
    2430:	930a0000 	movwls	r0, #40960	; 0xa000
    2434:	000000f7 	strdeq	r0, [r0], -r7
    2438:	0003e316 	andeq	lr, r3, r6, lsl r3
    243c:	00931500 	addseq	r1, r3, r0, lsl #10
    2440:	e3150000 	tst	r5, #0
    2444:	00000003 	andeq	r0, r0, r3
    2448:	03e90406 	mvneq	r0, #100663296	; 0x6000000
    244c:	09170000 	ldmdbeq	r7, {}	; <UNPREDICTABLE>
    2450:	00000f1b 	andeq	r0, r0, fp, lsl pc
    2454:	03fb960a 	mvnseq	r9, #10485760	; 0xa00000
    2458:	04060000 	streq	r0, [r6], #-0
    245c:	000003d3 	ldrdeq	r0, [r0], -r3
    2460:	0003f50b 	andeq	pc, r3, fp, lsl #10
    2464:	00931400 	addseq	r1, r3, r0, lsl #8
    2468:	04140000 	ldreq	r0, [r4], #-0
    246c:	a7150000 	ldrge	r0, [r5, -r0]
    2470:	15000000 	strne	r0, [r0, #-0]
    2474:	000003e3 	andeq	r0, r0, r3, ror #7
    2478:	0fd50900 	svceq	0x00d50900
    247c:	990a0000 	stmdbls	sl, {}	; <UNPREDICTABLE>
    2480:	00000425 	andeq	r0, r0, r5, lsr #8
    2484:	04000406 	streq	r0, [r0], #-1030	; 0xfffffbfa
    2488:	1f0b0000 	svcne	0x000b0000
    248c:	14000004 	strne	r0, [r0], #-4
    2490:	00000093 	muleq	r0, r3, r0
    2494:	00000443 	andeq	r0, r0, r3, asr #8
    2498:	00009315 	andeq	r9, r0, r5, lsl r3
    249c:	00a71500 	adceq	r1, r7, r0, lsl #10
    24a0:	e3150000 	tst	r5, #0
    24a4:	00000003 	andeq	r0, r0, r3
    24a8:	00113609 	andseq	r3, r1, r9, lsl #12
    24ac:	549c0a00 	ldrpl	r0, [ip], #2560	; 0xa00
    24b0:	06000004 	streq	r0, [r0], -r4
    24b4:	00042a04 	andeq	r2, r4, r4, lsl #20
    24b8:	044e0b00 	strbeq	r0, [lr], #-2816	; 0xfffff500
    24bc:	93140000 	tstls	r4, #0
    24c0:	72000000 	andvc	r0, r0, #0
    24c4:	15000004 	strne	r0, [r0, #-4]
    24c8:	000000a7 	andeq	r0, r0, r7, lsr #1
    24cc:	0000a715 	andeq	sl, r0, r5, lsl r7
    24d0:	03e31500 	mvneq	r1, #0, 10
    24d4:	09000000 	stmdbeq	r0, {}	; <UNPREDICTABLE>
    24d8:	0000111c 	andeq	r1, r0, ip, lsl r1
    24dc:	0483a00a 	streq	sl, [r3], #10
    24e0:	04060000 	streq	r0, [r6], #-0
    24e4:	00000459 	andeq	r0, r0, r9, asr r4
    24e8:	00047d0b 	andeq	r7, r4, fp, lsl #26
    24ec:	118f0900 	orrne	r0, pc, r0, lsl #18
    24f0:	a40a0000 	strge	r0, [sl], #-0
    24f4:	000000f7 	strdeq	r0, [r0], -r7
    24f8:	0009be04 	andeq	fp, r9, r4, lsl #28
    24fc:	25300b00 	ldrcs	r0, [r0, #-2816]!	; 0xfffff500
    2500:	04000000 	streq	r0, [r0], #-0
    2504:	00000667 	andeq	r0, r0, r7, ror #12
    2508:	002c310b 	eoreq	r3, ip, fp, lsl #2
    250c:	e9040000 	stmdb	r4, {}	; <UNPREDICTABLE>
    2510:	0b000008 	bleq	2538 <pthread_mutex_unlock@plt-0xe3f8>
    2514:	00003333 	andeq	r3, r0, r3, lsr r3
    2518:	0df10400 	cfldrdeq	mvd0, [r1]
    251c:	3a0b0000 	bcc	2c2524 <ringBuffer+0x26a84c>
    2520:	0000005d 	andeq	r0, r0, sp, asr r0
    2524:	00128304 	andseq	r8, r2, r4, lsl #6
    2528:	a9f80c00 	ldmibge	r8!, {sl, fp}^
    252c:	18000004 	stmdane	r0, {r2}
    2530:	ecfe0c08 	ldcl	12, cr0, [lr], #32
    2534:	19000004 	stmdbne	r0, {r2}
    2538:	0c006466 	cfstrseq	mvf6, [r0], {102}	; 0x66
    253c:	004f0100 	subeq	r0, pc, r0, lsl #2
    2540:	10000000 	andne	r0, r0, r0
    2544:	00000fb2 			; <UNDEFINED> instruction: 0x00000fb2
    2548:	ec01010c 	stfs	f0, [r1], {12}
    254c:	04000004 	streq	r0, [r0], #-4
    2550:	02010200 	andeq	r0, r1, #0, 4
    2554:	000001e9 	andeq	r0, r0, r9, ror #3
    2558:	000de41a 	andeq	lr, sp, sl, lsl r4
    255c:	01020c00 	tsteq	r2, r0, lsl #24
    2560:	000004ca 	andeq	r0, r0, sl, asr #9
    2564:	090c101b 	stmdbeq	ip, {r0, r1, r3, r4, ip}
    2568:	00053d01 	andeq	r3, r5, r1, lsl #26
    256c:	12291000 	eorne	r1, r9, #0
    2570:	0a0c0000 	beq	302578 <ringBuffer+0x2aa8a0>
    2574:	0004a901 	andeq	sl, r4, r1, lsl #18
    2578:	21100000 	tstcs	r0, r0
    257c:	0c000012 	stceq	0, cr0, [r0], {18}
    2580:	049e010b 	ldreq	r0, [lr], #267	; 0x10b
    2584:	10040000 	andne	r0, r4, r0
    2588:	00000e53 	andeq	r0, r0, r3, asr lr
    258c:	9e010c0c 	cdpls	12, 0, cr0, cr1, cr12, {0}
    2590:	06000004 	streq	r0, [r0], -r4
    2594:	000dcd10 	andeq	ip, sp, r0, lsl sp
    2598:	010d0c00 	tsteq	sp, r0, lsl #24
    259c:	0000053d 	andeq	r0, r0, sp, lsr r5
    25a0:	930c0008 	movwls	r0, #49160	; 0xc008
    25a4:	4d000004 	stcmi	0, cr0, [r0, #-16]
    25a8:	0d000005 	stceq	0, cr0, [r0, #-20]	; 0xffffffec
    25ac:	0000008c 	andeq	r0, r0, ip, lsl #1
    25b0:	d01a0007 	andsle	r0, sl, r7
    25b4:	0c00000e 	stceq	0, cr0, [r0], {14}
    25b8:	04ff010e 	ldrbteq	r0, [pc], #270	; 25c0 <pthread_mutex_unlock@plt-0xe370>
    25bc:	201b0000 	andscs	r0, fp, r0
    25c0:	ca01200c 	bgt	4a5f8 <.cpt_dt_wt_access_tb+0x39f1>
    25c4:	10000005 	andne	r0, r0, r5
    25c8:	000011d9 	ldrdeq	r1, [r0], -r9
    25cc:	9301210c 	movwls	r2, #4364	; 0x110c
    25d0:	00000000 	andeq	r0, r0, r0
    25d4:	0010f810 	andseq	pc, r0, r0, lsl r8	; <UNPREDICTABLE>
    25d8:	01220c00 			; <UNDEFINED> instruction: 0x01220c00
    25dc:	000000a7 	andeq	r0, r0, r7, lsr #1
    25e0:	06341004 	ldrteq	r1, [r4], -r4
    25e4:	230c0000 	movwcs	r0, #49152	; 0xc000
    25e8:	0004a901 	andeq	sl, r4, r1, lsl #18
    25ec:	69190800 	ldmdbvs	r9, {fp}
    25f0:	270c0064 	strcs	r0, [ip, -r4, rrx]
    25f4:	00004f01 	andeq	r4, r0, r1, lsl #30
    25f8:	f0100c00 			; <UNDEFINED> instruction: 0xf0100c00
    25fc:	0c000010 	stceq	0, cr0, [r0], {16}
    2600:	00a70128 	adceq	r0, r7, r8, lsr #2
    2604:	10100000 	andsne	r0, r0, r0
    2608:	000011d2 	ldrdeq	r1, [r0], -r2
    260c:	9301290c 	movwls	r2, #6412	; 0x190c
    2610:	14000000 	strne	r0, [r0], #-0
    2614:	000f5b10 	andeq	r5, pc, r0, lsl fp	; <UNPREDICTABLE>
    2618:	012a0c00 			; <UNDEFINED> instruction: 0x012a0c00
    261c:	0000004f 	andeq	r0, r0, pc, asr #32
    2620:	0fc41018 	svceq	0x00c41018
    2624:	2b0c0000 	blcs	30262c <ringBuffer+0x2aa954>
    2628:	0004ec01 	andeq	lr, r4, r1, lsl #24
    262c:	1a001c00 	bne	9634 <pthread_mutex_unlock@plt-0x72fc>
    2630:	000010cf 	andeq	r1, r0, pc, asr #1
    2634:	59012c0c 	stmdbpl	r1, {r2, r3, sl, fp, sp}
    2638:	1b000005 	blne	2654 <pthread_mutex_unlock@plt-0xe2dc>
    263c:	013a0c08 	teqeq	sl, r8, lsl #24
    2640:	000005fa 	strdeq	r0, [r0], -sl
    2644:	0011d910 	andseq	sp, r1, r0, lsl r9
    2648:	013b0c00 	teqeq	fp, r0, lsl #24
    264c:	00000093 	muleq	r0, r3, r0
    2650:	10f81000 	rscsne	r1, r8, r0
    2654:	3c0c0000 	stccc	0, cr0, [ip], {-0}
    2658:	0000a701 	andeq	sl, r0, r1, lsl #14
    265c:	1a000400 	bne	3664 <pthread_mutex_unlock@plt-0xd2cc>
    2660:	00001208 	andeq	r1, r0, r8, lsl #4
    2664:	d6013d0c 	strle	r3, [r1], -ip, lsl #26
    2668:	1b000005 	blne	2684 <pthread_mutex_unlock@plt-0xe2ac>
    266c:	014e0c0c 	cmpeq	lr, ip, lsl #24
    2670:	00000637 	andeq	r0, r0, r7, lsr r6
    2674:	000e9410 	andeq	r9, lr, r0, lsl r4
    2678:	014f0c00 	cmpeq	pc, r0, lsl #24
    267c:	00000637 	andeq	r0, r0, r7, lsr r6
    2680:	10f81000 	rscsne	r1, r8, r0
    2684:	500c0000 	andpl	r0, ip, r0
    2688:	0000a701 	andeq	sl, r0, r1, lsl #14
    268c:	9b100400 	blls	403694 <ringBuffer+0x3ab9bc>
    2690:	0c000006 	stceq	0, cr0, [r0], {6}
    2694:	00a70151 	adceq	r0, r7, r1, asr r1
    2698:	00080000 	andeq	r0, r8, r0
    269c:	05ca0406 	strbeq	r0, [sl, #1030]	; 0x406
    26a0:	311a0000 	tstcc	sl, r0
    26a4:	0c000012 	stceq	0, cr0, [r0], {18}
    26a8:	06060152 			; <UNDEFINED> instruction: 0x06060152
    26ac:	081b0000 	ldmdaeq	fp, {}	; <UNPREDICTABLE>
    26b0:	69015e0c 	stmdbvs	r1, {r2, r3, r9, sl, fp, ip, lr}
    26b4:	19000006 	stmdbne	r0, {r1, r2}
    26b8:	5f0c0061 	svcpl	0x000c0061
    26bc:	0004a901 	andeq	sl, r4, r1, lsl #18
    26c0:	62190000 	andsvs	r0, r9, #0
    26c4:	01600c00 	cmneq	r0, r0, lsl #24
    26c8:	000004a9 	andeq	r0, r0, r9, lsr #9
    26cc:	401a0004 	andsmi	r0, sl, r4
    26d0:	0c00000f 	stceq	0, cr0, [r0], {15}
    26d4:	06490161 	strbeq	r0, [r9], -r1, ror #2
    26d8:	0c1c0000 	ldceq	0, cr0, [ip], {-0}
    26dc:	a301710c 	movwge	r7, #4364	; 0x110c
    26e0:	1d000006 	stcne	0, cr0, [r0, #-24]	; 0xffffffe8
    26e4:	00001273 	andeq	r1, r0, r3, ror r2
    26e8:	fa01720c 	blx	5ef20 <ringBuffer+0x7248>
    26ec:	1d000005 	stcne	0, cr0, [r0, #-20]	; 0xffffffec
    26f0:	00000ddd 	ldrdeq	r0, [r0], -sp
    26f4:	3d01730c 	stccc	3, cr7, [r1, #-48]	; 0xffffffd0
    26f8:	1d000006 	stcne	0, cr0, [r0, #-24]	; 0xffffffe8
    26fc:	00000d6c 	andeq	r0, r0, ip, ror #26
    2700:	6901740c 	stmdbvs	r1, {r2, r3, sl, ip, sp, lr}
    2704:	00000006 	andeq	r0, r0, r6
    2708:	0010e11a 	andseq	lr, r0, sl, lsl r1
    270c:	01750c00 	cmneq	r5, r0, lsl #24
    2710:	00000675 	andeq	r0, r0, r5, ror r6
    2714:	7b0c081b 	blvc	304788 <ringBuffer+0x2acab0>
    2718:	0006d301 	andeq	sp, r6, r1, lsl #6
    271c:	74631900 	strbtvc	r1, [r3], #-2304	; 0xfffff700
    2720:	7d0c0078 	stcvc	0, cr0, [ip, #-480]	; 0xfffffe20
    2724:	0006d301 	andeq	sp, r6, r1, lsl #6
    2728:	48100000 	ldmdami	r0, {}	; <UNPREDICTABLE>
    272c:	0c00000e 	stceq	0, cr0, [r0], {14}
    2730:	04a9017e 	strteq	r0, [r9], #382	; 0x17e
    2734:	00040000 	andeq	r0, r4, r0
    2738:	04f30406 	ldrbteq	r0, [r3], #1030	; 0x406
    273c:	ac1a0000 	ldcge	0, cr0, [sl], {-0}
    2740:	0c000011 	stceq	0, cr0, [r0], {17}
    2744:	06af017f 			; <UNDEFINED> instruction: 0x06af017f
    2748:	3c1b0000 	ldccc	0, cr0, [fp], {-0}
    274c:	23018f0c 	movwcs	r8, #7948	; 0x1f0c
    2750:	10000007 	andne	r0, r0, r7
    2754:	00000e36 	andeq	r0, r0, r6, lsr lr
    2758:	a901900c 	stmdbge	r1, {r2, r3, ip, pc}
    275c:	00000004 	andeq	r0, r0, r4
    2760:	000e8910 	andeq	r8, lr, r0, lsl r9
    2764:	01910c00 	orrseq	r0, r1, r0, lsl #24
    2768:	000004a9 	andeq	r0, r0, r9, lsr #9
    276c:	11a51004 			; <UNDEFINED> instruction: 0x11a51004
    2770:	920c0000 	andls	r0, ip, #0
    2774:	00072301 	andeq	r2, r7, r1, lsl #6
    2778:	ac100800 	ldcge	8, cr0, [r0], {-0}
    277c:	0c000010 	stceq	0, cr0, [r0], {16}
    2780:	07330194 			; <UNDEFINED> instruction: 0x07330194
    2784:	00380000 	eorseq	r0, r8, r0
    2788:	0006a30c 	andeq	sl, r6, ip, lsl #6
    278c:	00073300 	andeq	r3, r7, r0, lsl #6
    2790:	008c0d00 	addeq	r0, ip, r0, lsl #26
    2794:	00030000 	andeq	r0, r3, r0
    2798:	06d90406 	ldrbeq	r0, [r9], r6, lsl #8
    279c:	831a0000 	tsthi	sl, #0
    27a0:	0c00000f 	stceq	0, cr0, [r0], {15}
    27a4:	06e50195 	usateq	r0, #5, r5, lsl #3
    27a8:	950c0000 	strls	r0, [ip, #-0]
    27ac:	55000000 	strpl	r0, [r0, #-0]
    27b0:	0d000007 	stceq	0, cr0, [r0, #-28]	; 0xffffffe4
    27b4:	0000008c 	andeq	r0, r0, ip, lsl #1
    27b8:	7a080001 	bvc	2027c4 <ringBuffer+0x1aaaec>
    27bc:	0d000012 	stceq	0, cr0, [r0, #-72]	; 0xffffffb8
    27c0:	0745011a 	smlaldeq	r0, r5, sl, r1
    27c4:	64080000 	strvs	r0, [r8], #-0
    27c8:	0d000011 	stceq	0, cr0, [r0, #-68]	; 0xffffffbc
    27cc:	004f011b 	subeq	r0, pc, fp, lsl r1	; <UNPREDICTABLE>
    27d0:	64080000 	strvs	r0, [r8], #-0
    27d4:	0d00000e 	stceq	0, cr0, [r0, #-56]	; 0xffffffc8
    27d8:	007a011c 	rsbseq	r0, sl, ip, lsl r1
    27dc:	7c080000 	stcvc	0, cr0, [r8], {-0}
    27e0:	0d000012 	stceq	0, cr0, [r0, #-72]	; 0xffffffb8
    27e4:	07450121 	strbeq	r0, [r5, -r1, lsr #2]
    27e8:	66080000 	strvs	r0, [r8], -r0
    27ec:	0d000011 	stceq	0, cr0, [r0, #-68]	; 0xffffffbc
    27f0:	004f0129 	subeq	r0, pc, r9, lsr #2
    27f4:	66080000 	strvs	r0, [r8], -r0
    27f8:	0d00000e 	stceq	0, cr0, [r0, #-56]	; 0xffffffc8
    27fc:	007a012a 	rsbseq	r0, sl, sl, lsr #2
    2800:	fa1e0000 	blx	782808 <ringBuffer+0x72ab30>
    2804:	04000009 	streq	r0, [r0], #-9
    2808:	00000033 	andeq	r0, r0, r3, lsr r0
    280c:	07cc1f0e 	strbeq	r1, [ip, lr, lsl #30]
    2810:	661f0000 	ldrvs	r0, [pc], -r0
    2814:	40000007 	andmi	r0, r0, r7
    2818:	0007331f 	andeq	r3, r7, pc, lsl r3
    281c:	e51f2000 	ldr	r2, [pc, #-0]	; 2824 <pthread_mutex_unlock@plt-0xe10c>
    2820:	20000006 	andcs	r0, r0, r6
    2824:	0008511f 	andeq	r5, r8, pc, lsl r1
    2828:	051f0800 	ldreq	r0, [pc, #-2048]	; 2030 <pthread_mutex_unlock@plt-0xe900>
    282c:	08000009 	stmdaeq	r0, {r0, r3}
    2830:	05dd1e00 	ldrbeq	r1, [sp, #3584]	; 0xe00
    2834:	33040000 	movwcc	r0, #16384	; 0x4000
    2838:	0e000000 	cdpeq	0, 0, cr0, cr0, cr0, {0}
    283c:	0007fb28 	andeq	pc, r7, r8, lsr #22
    2840:	08861f00 	stmeq	r6, {r8, r9, sl, fp, ip}
    2844:	1f800000 	svcne	0x00800000
    2848:	00000ad1 	ldrdeq	r0, [r0], -r1
    284c:	099f1f40 	ldmibeq	pc, {r6, r8, r9, sl, fp, ip}	; <UNPREDICTABLE>
    2850:	1f400000 	svcne	0x00400000
    2854:	00000621 	andeq	r0, r0, r1, lsr #12
    2858:	09e41f10 	stmibeq	r4!, {r4, r8, r9, sl, fp, ip}^
    285c:	00100000 	andseq	r0, r0, r0
    2860:	0005210e 	andeq	r2, r5, lr, lsl #2
    2864:	310e7c00 	tstcc	lr, r0, lsl #24
    2868:	00000856 	andeq	r0, r0, r6, asr r8
    286c:	0e006820 	cdpeq	8, 0, cr6, cr0, cr0, {1}
    2870:	00085633 	andeq	r5, r8, r3, lsr r6
    2874:	74200000 	strtvc	r0, [r0], #-0
    2878:	66340e00 	ldrtvs	r0, [r4], -r0, lsl #28
    287c:	20000008 	andcs	r0, r0, r8
    2880:	0e006620 	cfmadd32eq	mvax1, mvfx6, mvfx0, mvfx0
    2884:	00086635 	andeq	r6, r8, r5, lsr r6
    2888:	62202800 	eorvs	r2, r0, #0, 16
    288c:	0e006675 	mcreq	6, 0, r6, cr0, cr5, {3}
    2890:	00087636 	andeq	r7, r8, r6, lsr r6
    2894:	cd0f3000 	stcgt	0, cr3, [pc, #-0]	; 289c <pthread_mutex_unlock@plt-0xe094>
    2898:	0e000008 	cdpeq	0, 0, cr0, cr0, cr8, {0}
    289c:	0000a737 	andeq	sl, r0, r7, lsr r7
    28a0:	0b0f7000 	bleq	3de8a8 <ringBuffer+0x386bd0>
    28a4:	0e00000a 	cdpeq	0, 0, cr0, cr0, cr10, {0}
    28a8:	0000a738 	andeq	sl, r0, r8, lsr r7
    28ac:	620f7400 	andvs	r7, pc, #0, 8
    28b0:	0e000009 	cdpeq	0, 0, cr0, cr0, cr9, {0}
    28b4:	00049339 	andeq	r9, r4, r9, lsr r3
    28b8:	0c007800 	stceq	8, cr7, [r0], {-0}
    28bc:	000004a9 	andeq	r0, r0, r9, lsr #9
    28c0:	00000866 	andeq	r0, r0, r6, ror #16
    28c4:	00008c0d 	andeq	r8, r0, sp, lsl #24
    28c8:	0c000700 	stceq	7, cr0, [r0], {-0}
    28cc:	000004a9 	andeq	r0, r0, r9, lsr #9
    28d0:	00000876 	andeq	r0, r0, r6, ror r8
    28d4:	00008c0d 	andeq	r8, r0, sp, lsl #24
    28d8:	0c000100 	stfeqs	f0, [r0], {-0}
    28dc:	00000493 	muleq	r0, r3, r4
    28e0:	00000886 	andeq	r0, r0, r6, lsl #17
    28e4:	00008c0d 	andeq	r8, r0, sp, lsl #24
    28e8:	04003f00 	streq	r3, [r0], #-3840	; 0xfffff100
    28ec:	000009d6 	ldrdeq	r0, [r0], -r6
    28f0:	07fb3a0e 	ldrbeq	r3, [fp, lr, lsl #20]!
    28f4:	10180000 	andsne	r0, r8, r0
    28f8:	08ca1701 	stmiaeq	sl, {r0, r8, r9, sl, ip}^
    28fc:	920f0000 	andls	r0, pc, #0
    2900:	0100000d 	tsteq	r0, sp
    2904:	0004a918 	andeq	sl, r4, r8, lsl r9
    2908:	e00f0000 	and	r0, pc, r0
    290c:	0100000b 	tsteq	r0, fp
    2910:	0004a919 	andeq	sl, r4, r9, lsl r9
    2914:	420f0400 	andmi	r0, pc, #0, 8
    2918:	0100000c 	tsteq	r0, ip
    291c:	0004a91a 	andeq	sl, r4, sl, lsl r9
    2920:	a80f0800 	stmdage	pc, {fp}	; <UNPREDICTABLE>
    2924:	0100000c 	tsteq	r0, ip
    2928:	0004931b 	andeq	r9, r4, fp, lsl r3
    292c:	04000c00 	streq	r0, [r0], #-3072	; 0xfffff400
    2930:	00000c8d 	andeq	r0, r0, sp, lsl #25
    2934:	08911c01 	ldmeq	r1, {r0, sl, fp, ip}
    2938:	08210000 	stmdaeq	r1!, {}	; <UNPREDICTABLE>
    293c:	01098968 	tsteq	r9, r8, ror #18
    2940:	00090b1e 	andeq	r0, r9, lr, lsl fp
    2944:	11d90f00 	bicsne	r0, r9, r0, lsl #30
    2948:	1f010000 	svcne	0x00010000
    294c:	0000090b 	andeq	r0, r0, fp, lsl #18
    2950:	0c5f2200 	lfmeq	f2, 2, [pc], {-0}
    2954:	20010000 	andcs	r0, r1, r0
    2958:	000000a7 	andeq	r0, r0, r7, lsr #1
    295c:	09896800 	stmibeq	r9, {fp, sp, lr}
    2960:	000d3622 	andeq	r3, sp, r2, lsr #12
    2964:	a7210100 	strge	r0, [r1, -r0, lsl #2]!
    2968:	04000000 	streq	r0, [r0], #-0
    296c:	00098968 	andeq	r8, r9, r8, ror #18
    2970:	0008ca0c 	andeq	ip, r8, ip, lsl #20
    2974:	00091e00 	andeq	r1, r9, r0, lsl #28
    2978:	008c2300 	addeq	r2, ip, r0, lsl #6
    297c:	967f0000 	ldrbtls	r0, [pc], -r0
    2980:	04000098 	streq	r0, [r0], #-152	; 0xffffff68
    2984:	00000c9d 	muleq	r0, sp, ip
    2988:	08d52201 	ldmeq	r5, {r0, r9, sp}^
    298c:	05240000 	streq	r0, [r4, #-0]!
    2990:	0100000e 	tsteq	r0, lr
    2994:	00004f23 	andeq	r4, r0, r3, lsr #30
    2998:	98030500 	stmdals	r3, {r8, sl}
    299c:	2400057c 	strcs	r0, [r0], #-1404	; 0xfffffa84
    29a0:	000009de 	ldrdeq	r0, [r0], -lr
    29a4:	08862401 	stmeq	r6, {r0, sl, sp}
    29a8:	03050000 	movweq	r0, #20480	; 0x5000
    29ac:	098ee4ec 	stmibeq	lr, {r2, r3, r5, r6, r7, sl, sp, lr, pc}
    29b0:	0004930c 	andeq	r9, r4, ip, lsl #6
    29b4:	00095b00 	andeq	r5, r9, r0, lsl #22
    29b8:	008c0d00 	addeq	r0, ip, r0, lsl #26
    29bc:	001f0000 	andseq	r0, pc, r0
    29c0:	000e0024 	andeq	r0, lr, r4, lsr #32
    29c4:	4b250100 	blmi	942dcc <ringBuffer+0x8eb0f4>
    29c8:	05000009 	streq	r0, [r0, #-9]
    29cc:	8ee56803 	cdphi	8, 14, cr6, cr5, cr3, {0}
    29d0:	0ff32409 	svceq	0x00f32409
    29d4:	26010000 	strcs	r0, [r1], -r0
    29d8:	0000004f 	andeq	r0, r0, pc, asr #32
    29dc:	7c9c0305 	ldcvc	3, cr0, [ip], {5}
    29e0:	8f090005 	svchi	0x00090005
    29e4:	01000000 	mrseq	r0, (UNDEF: 0)
    29e8:	00004f27 	andeq	r4, r0, r7, lsr #30
    29ec:	009e0900 	addseq	r0, lr, r0, lsl #18
    29f0:	28010000 	stmdacs	r1, {}	; <UNPREDICTABLE>
    29f4:	0000004f 	andeq	r0, r0, pc, asr #32
    29f8:	000d0209 	andeq	r0, sp, r9, lsl #4
    29fc:	4f290100 	svcmi	0x00290100
    2a00:	09000000 	stmdbeq	r0, {}	; <UNPREDICTABLE>
    2a04:	00000d9a 	muleq	r0, sl, sp
    2a08:	091e2a01 	ldmdbeq	lr, {r0, r9, fp, sp}
    2a0c:	72250000 	eorvc	r0, r5, #0
    2a10:	01007365 	tsteq	r0, r5, ror #6
    2a14:	0004bf3a 	andeq	fp, r4, sl, lsr pc
    2a18:	94030500 	strls	r0, [r3], #-1280	; 0xfffffb00
    2a1c:	25098ee5 	strcs	r8, [r9, #-3813]	; 0xfffff11b
    2a20:	00787463 	rsbseq	r7, r8, r3, ror #8
    2a24:	04f33b01 	ldrbteq	r3, [r3], #2817	; 0xb01
    2a28:	03050000 	movweq	r0, #20480	; 0x5000
    2a2c:	098ee4e4 	stmibeq	lr, {r2, r5, r6, r7, sl, sp, lr, pc}
    2a30:	000ea624 	andeq	sl, lr, r4, lsr #12
    2a34:	d93c0100 	ldmdble	ip!, {r8}
    2a38:	05000006 	streq	r0, [r0, #-6]
    2a3c:	8ee58c03 	cdphi	12, 14, cr8, cr5, cr3, {0}
    2a40:	706f2509 	rsbvc	r2, pc, r9, lsl #10
    2a44:	393d0100 	ldmdbcc	sp!, {r8}
    2a48:	05000007 	streq	r0, [r0, #-7]
    2a4c:	8ee59803 	cdphi	8, 14, cr9, cr5, cr3, {0}
    2a50:	118a2409 	orrne	r2, sl, r9, lsl #8
    2a54:	3e010000 	cdpcc	0, 0, cr0, cr1, cr0, {0}
    2a58:	0000054d 	andeq	r0, r0, sp, asr #10
    2a5c:	70d40305 	sbcsvc	r0, r4, r5, lsl #6
    2a60:	da240005 	ble	902a7c <ringBuffer+0x8aada4>
    2a64:	0100000e 	tsteq	r0, lr
    2a68:	0004a93f 	andeq	sl, r4, pc, lsr r9
    2a6c:	88030500 	stmdahi	r3, {r8, sl}
    2a70:	24098ee5 	strcs	r8, [r9], #-3813	; 0xfffff11b
    2a74:	00000eeb 	andeq	r0, r0, fp, ror #29
    2a78:	04ec4101 	strbteq	r4, [ip], #257	; 0x101
    2a7c:	03050000 	movweq	r0, #20480	; 0x5000
    2a80:	00057ca0 	andeq	r7, r5, r0, lsr #25
    2a84:	000f9224 	andeq	r9, pc, r4, lsr #4
    2a88:	4f490100 	svcmi	0x00490100
    2a8c:	05000000 	streq	r0, [r0, #-0]
    2a90:	057ca403 	ldrbeq	sl, [ip, #-1027]!	; 0xfffffbfd
    2a94:	0f072600 	svceq	0x00072600
    2a98:	6f010000 	svcvs	0x00010000
    2a9c:	044f8801 	strbeq	r8, [pc], #-2049	; 2aa4 <pthread_mutex_unlock@plt-0xde8c>
    2aa0:	00007400 	andeq	r7, r0, r0, lsl #8
    2aa4:	9a9c0100 	bls	fe702eac <__bss_end__+0xf4e148d8>
    2aa8:	2700000a 	strcs	r0, [r0, -sl]
    2aac:	00000ee5 	andeq	r0, r0, r5, ror #29
    2ab0:	9a016f01 	bls	5e6bc <ringBuffer+0x69e4>
    2ab4:	0200000a 	andeq	r0, r0, #10
    2ab8:	9b276c91 	blls	9ddd04 <ringBuffer+0x98602c>
    2abc:	0100000e 	tsteq	r0, lr
    2ac0:	00a7016f 	adceq	r0, r7, pc, ror #2
    2ac4:	91020000 	mrsls	r0, (UNDEF: 2)
    2ac8:	0fe32768 	svceq	0x00e32768
    2acc:	6f010000 	svcvs	0x00010000
    2ad0:	00011101 	andeq	r1, r1, r1, lsl #2
    2ad4:	64910200 	ldrvs	r0, [r1], #512	; 0x200
    2ad8:	000fad28 	andeq	sl, pc, r8, lsr #26
    2adc:	01700100 	cmneq	r0, r0, lsl #2
    2ae0:	00000aa0 	andeq	r0, r0, r0, lsr #21
    2ae4:	29709102 	ldmdbcs	r0!, {r1, r8, ip, pc}^
    2ae8:	00044fa8 	andeq	r4, r4, r8, lsr #31
    2aec:	0000002a 	andeq	r0, r0, sl, lsr #32
    2af0:	0100692a 	tsteq	r0, sl, lsr #18
    2af4:	00a70173 	adceq	r0, r7, r3, ror r1
    2af8:	91020000 	mrsls	r0, (UNDEF: 2)
    2afc:	06000074 			; <UNDEFINED> instruction: 0x06000074
    2b00:	00049304 	andeq	r9, r4, r4, lsl #6
    2b04:	34040600 	strcc	r0, [r4], #-1536	; 0xfffffa00
    2b08:	26000001 	strcs	r0, [r0], -r1
    2b0c:	00000f9d 	muleq	r0, sp, pc	; <UNPREDICTABLE>
    2b10:	24016201 	strcs	r6, [r1], #-513	; 0xfffffdff
    2b14:	6400044f 	strvs	r0, [r0], #-1103	; 0xfffffbb1
    2b18:	01000000 	mrseq	r0, (UNDEF: 0)
    2b1c:	000b039c 	muleq	fp, ip, r3
    2b20:	0ef92700 	cdpeq	7, 15, cr2, cr9, cr0, {0}
    2b24:	62010000 	andvs	r0, r1, #0
    2b28:	0004a901 	andeq	sl, r4, r1, lsl #18
    2b2c:	64910200 	ldrvs	r0, [r1], #512	; 0x200
    2b30:	000fe327 	andeq	lr, pc, r7, lsr #6
    2b34:	01620100 	cmneq	r2, r0, lsl #2
    2b38:	00000111 	andeq	r0, r0, r1, lsl r1
    2b3c:	28609102 	stmdacs	r0!, {r1, r8, ip, pc}^
    2b40:	00000fad 	andeq	r0, r0, sp, lsr #31
    2b44:	a0016301 	andge	r6, r1, r1, lsl #6
    2b48:	0200000a 	andeq	r0, r0, #10
    2b4c:	42297491 	eormi	r7, r9, #-1862270976	; 0x91000000
    2b50:	2200044f 	andcs	r0, r0, #1325400064	; 0x4f000000
    2b54:	28000000 	stmdacs	r0, {}	; <UNPREDICTABLE>
    2b58:	00001176 	andeq	r1, r0, r6, ror r1
    2b5c:	03016501 	movweq	r6, #5377	; 0x1501
    2b60:	0200000b 	andeq	r0, r0, #11
    2b64:	00006891 	muleq	r0, r1, r8
    2b68:	00009b0c 	andeq	r9, r0, ip, lsl #22
    2b6c:	000b1300 	andeq	r1, fp, r0, lsl #6
    2b70:	008c0d00 	addeq	r0, ip, r0, lsl #26
    2b74:	000b0000 	andeq	r0, fp, r0
    2b78:	0010be2b 	andseq	fp, r0, fp, lsr #28
    2b7c:	93e20100 	mvnls	r0, #0, 2
    2b80:	bc000000 	stclt	0, cr0, [r0], {-0}
    2b84:	6800044d 	stmdavs	r0, {r0, r2, r3, r6, sl}
    2b88:	01000001 	tsteq	r0, r1
    2b8c:	000bc09c 	muleq	fp, ip, r0
    2b90:	11082c00 	tstne	r8, r0, lsl #24
    2b94:	e5010000 	str	r0, [r1, #-0]
    2b98:	000008ca 	andeq	r0, r0, sl, asr #17
    2b9c:	29609102 	stmdbcs	r0!, {r1, r8, ip, pc}^
    2ba0:	00044dc6 	andeq	r4, r4, r6, asr #27
    2ba4:	00000120 	andeq	r0, r0, r0, lsr #2
    2ba8:	706f702d 	rsbvc	r7, pc, sp, lsr #32
    2bac:	4feb0100 	svcmi	0x00eb0100
    2bb0:	54000000 	strpl	r0, [r0], #-0
    2bb4:	2e00000b 	cdpcs	0, 0, cr0, cr0, cr11, {0}
    2bb8:	4de02f00 	stclmi	15, cr2, [r0]
    2bbc:	000e0004 	andeq	r0, lr, r4
    2bc0:	0b6f0000 	bleq	1bc2bc8 <ringBuffer+0x1b6aef0>
    2bc4:	9d300000 	ldcls	0, cr0, [r0, #-0]
    2bc8:	0100000f 	tsteq	r0, pc
    2bcc:	00004ff4 	strdeq	r4, [r0], -r4	; <UNPREDICTABLE>
    2bd0:	00002e00 	andeq	r2, r0, r0, lsl #28
    2bd4:	044e5e2f 	strbeq	r5, [lr], #-3631	; 0xfffff1d1
    2bd8:	00000e00 	andeq	r0, r0, r0, lsl #28
    2bdc:	000b8a00 	andeq	r8, fp, r0, lsl #20
    2be0:	0f9d3000 	svceq	0x009d3000
    2be4:	f4010000 	vst4.8	{d0-d3}, [r1], r0
    2be8:	0000004f 	andeq	r0, r0, pc, asr #32
    2bec:	2900002e 	stmdbcs	r0, {r1, r2, r3, r5}
    2bf0:	00044e82 	andeq	r4, r4, r2, lsl #29
    2bf4:	00000064 	andeq	r0, r0, r4, rrx
    2bf8:	000ba331 	andeq	sl, fp, r1, lsr r3
    2bfc:	012f0100 			; <UNDEFINED> instruction: 0x012f0100
    2c00:	0000004f 	andeq	r0, r0, pc, asr #32
    2c04:	00000ba5 	andeq	r0, r0, r5, lsr #23
    2c08:	a629002e 	strtge	r0, [r9], -lr, lsr #32
    2c0c:	4000044e 	andmi	r0, r0, lr, asr #8
    2c10:	32000000 	andcc	r0, r0, #0
    2c14:	00000f07 	andeq	r0, r0, r7, lsl #30
    2c18:	4f013401 	svcmi	0x00013401
    2c1c:	2e000000 	cdpcs	0, 0, cr0, cr0, cr0, {0}
    2c20:	00000000 	andeq	r0, r0, r0
    2c24:	0f273300 	svceq	0x00273300
    2c28:	c6010000 	strgt	r0, [r1], -r0
    2c2c:	00044c90 	muleq	r4, r0, ip
    2c30:	0000012c 	andeq	r0, r0, ip, lsr #2
    2c34:	0c4e9c01 	mcrreq	12, 0, r9, lr, cr1
    2c38:	e0340000 	eors	r0, r4, r0
    2c3c:	01000011 	tsteq	r0, r1, lsl r0
    2c40:	000111c6 	andeq	r1, r1, r6, asr #3
    2c44:	54910200 	ldrpl	r0, [r1], #512	; 0x200
    2c48:	000e3e34 	andeq	r3, lr, r4, lsr lr
    2c4c:	11c60100 	bicne	r0, r6, r0, lsl #2
    2c50:	02000001 	andeq	r0, r0, #1
    2c54:	ea345091 	b	d16ea0 <ringBuffer+0xcbf1c8>
    2c58:	01000011 	tsteq	r0, r1, lsl r0
    2c5c:	000111c6 	andeq	r1, r1, r6, asr #3
    2c60:	4c910200 	lfmmi	f0, 4, [r1], {0}
    2c64:	0011f434 	andseq	pc, r1, r4, lsr r4	; <UNPREDICTABLE>
    2c68:	11c70100 	bicne	r0, r7, r0, lsl #2
    2c6c:	02000001 	andeq	r0, r0, #1
    2c70:	fe344891 	mrc2	8, 1, r4, cr4, cr1, {4}
    2c74:	01000011 	tsteq	r0, r1, lsl r0
    2c78:	000111c7 	andeq	r1, r1, r7, asr #3
    2c7c:	00910200 	addseq	r0, r1, r0, lsl #4
    2c80:	0012692c 	andseq	r6, r2, ip, lsr #18
    2c84:	4ec90100 	polmie	f0, f1, f0
    2c88:	0200000c 	andeq	r0, r0, #12
    2c8c:	ad2c5c91 	stcge	12, cr5, [ip, #-580]!	; 0xfffffdbc
    2c90:	0100000f 	tsteq	r0, pc
    2c94:	000aa0ca 	andeq	sl, sl, sl, asr #1
    2c98:	70910200 	addsvc	r0, r1, r0, lsl #4
    2c9c:	044cb229 	strbeq	fp, [ip], #-553	; 0xfffffdd7
    2ca0:	0000e800 	andeq	lr, r0, r0, lsl #16
    2ca4:	00693500 	rsbeq	r3, r9, r0, lsl #10
    2ca8:	004fcc01 	subeq	ip, pc, r1, lsl #24
    2cac:	91020000 	mrsls	r0, (UNDEF: 2)
    2cb0:	0c000074 	stceq	0, cr0, [r0], {116}	; 0x74
    2cb4:	00000111 	andeq	r0, r0, r1, lsl r1
    2cb8:	00000c5e 	andeq	r0, r0, lr, asr ip
    2cbc:	00008c0d 	andeq	r8, r0, sp, lsl #24
    2cc0:	33000400 	movwcc	r0, #1024	; 0x400
    2cc4:	00000dfa 	strdeq	r0, [r0], -sl
    2cc8:	4c4cbf01 	mcrrmi	15, 0, fp, ip, cr1
    2ccc:	00440004 	subeq	r0, r4, r4
    2cd0:	9c010000 	stcls	0, cr0, [r1], {-0}
    2cd4:	00000ca6 	andeq	r0, r0, r6, lsr #25
    2cd8:	000e0034 	andeq	r0, lr, r4, lsr r0
    2cdc:	9abf0100 	bls	fefc30e4 <__bss_end__+0xf56d4b10>
    2ce0:	0200000a 	andeq	r0, r0, #10
    2ce4:	75346c91 	ldrvc	r6, [r4, #-3217]!	; 0xfffff36f
    2ce8:	01000006 	tsteq	r0, r6
    2cec:	0000a7bf 			; <UNDEFINED> instruction: 0x0000a7bf
    2cf0:	68910200 	ldmvs	r1, {r9}
    2cf4:	044c5629 	strbeq	r5, [ip], #-1577	; 0xfffff9d7
    2cf8:	00002800 	andeq	r2, r0, r0, lsl #16
    2cfc:	00693500 	rsbeq	r3, r9, r0, lsl #10
    2d00:	00a7c001 	adceq	ip, r7, r1
    2d04:	91020000 	mrsls	r0, (UNDEF: 2)
    2d08:	33000074 	movwcc	r0, #116	; 0x74
    2d0c:	00000f69 	andeq	r0, r0, r9, ror #30
    2d10:	4bf6b501 	blmi	ffdb011c <__bss_end__+0xf64c1b48>
    2d14:	00560004 	subseq	r0, r6, r4
    2d18:	9c010000 	stcls	0, cr0, [r1], {-0}
    2d1c:	00000cf4 	strdeq	r0, [r0], -r4
    2d20:	00101334 	andseq	r1, r0, r4, lsr r3
    2d24:	a9b50100 	ldmibge	r5!, {r8}
    2d28:	02000004 	andeq	r0, r0, #4
    2d2c:	1b346c91 	blne	d1df78 <ringBuffer+0xcc62a0>
    2d30:	01000010 	tsteq	r0, r0, lsl r0
    2d34:	0004a9b5 			; <UNDEFINED> instruction: 0x0004a9b5
    2d38:	68910200 	ldmvs	r1, {r9}
    2d3c:	000fe334 	andeq	lr, pc, r4, lsr r3	; <UNPREDICTABLE>
    2d40:	11b50100 			; <UNDEFINED> instruction: 0x11b50100
    2d44:	02000001 	andeq	r0, r0, #1
    2d48:	ad2c6491 	cfstrsge	mvf6, [ip, #-580]!	; 0xfffffdbc
    2d4c:	0100000f 	tsteq	r0, pc
    2d50:	000aa0b6 	strheq	sl, [sl], -r6
    2d54:	74910200 	ldrvc	r0, [r1], #512	; 0x200
    2d58:	0f4b3600 	svceq	0x004b3600
    2d5c:	b1010000 	mrslt	r0, (UNDEF: 1)
    2d60:	00044be0 	andeq	r4, r4, r0, ror #23
    2d64:	00000016 	andeq	r0, r0, r6, lsl r0
    2d68:	0d269c01 	stceq	12, cr9, [r6, #-4]!
    2d6c:	fd340000 	ldc2	0, cr0, [r4, #-0]
    2d70:	01000010 	tsteq	r0, r0, lsl r0
    2d74:	00004fb1 			; <UNDEFINED> instruction: 0x00004fb1
    2d78:	74910200 	ldrvc	r0, [r1], #512	; 0x200
    2d7c:	00111334 	andseq	r1, r1, r4, lsr r3
    2d80:	4fb10100 	svcmi	0x00b10100
    2d84:	02000000 	andeq	r0, r0, #0
    2d88:	36007091 			; <UNDEFINED> instruction: 0x36007091
    2d8c:	00001145 	andeq	r1, r0, r5, asr #2
    2d90:	4bcaad01 	blmi	ff2ae19c <__bss_end__+0xf59bfbc8>
    2d94:	00160004 	andseq	r0, r6, r4
    2d98:	9c010000 	stcls	0, cr0, [r1], {-0}
    2d9c:	00000d4a 	andeq	r0, r0, sl, asr #26
    2da0:	00112c34 	andseq	r2, r1, r4, lsr ip
    2da4:	ecad0100 	stfs	f0, [sp]
    2da8:	02000004 	andeq	r0, r0, #4
    2dac:	36007791 			; <UNDEFINED> instruction: 0x36007791
    2db0:	000011c4 	andeq	r1, r0, r4, asr #3
    2db4:	4bb0a901 	blmi	fec2d1c0 <__bss_end__+0xf533ebec>
    2db8:	001a0004 	andseq	r0, sl, r4
    2dbc:	9c010000 	stcls	0, cr0, [r1], {-0}
    2dc0:	00000d78 	andeq	r0, r0, r8, ror sp
    2dc4:	01006137 	tsteq	r0, r7, lsr r1
    2dc8:	0004b4a9 	andeq	fp, r4, r9, lsr #9
    2dcc:	70910200 	addsvc	r0, r1, r0, lsl #4
    2dd0:	01006237 	tsteq	r0, r7, lsr r2
    2dd4:	0004b4a9 	andeq	fp, r4, r9, lsr #9
    2dd8:	68910200 	ldmvs	r1, {r9}
    2ddc:	0e1a3800 	cdpeq	8, 1, cr3, cr10, cr0, {0}
    2de0:	93010000 	movwls	r0, #4096	; 0x1000
    2de4:	00044b2c 	andeq	r4, r4, ip, lsr #22
    2de8:	00000084 	andeq	r0, r0, r4, lsl #1
    2dec:	6f399c01 	svcvs	0x00399c01
    2df0:	0100000e 	tsteq	r0, lr
    2df4:	0449984a 	strbeq	r9, [r9], #-2122	; 0xfffff7b6
    2df8:	00019400 	andeq	r9, r1, r0, lsl #8
    2dfc:	349c0100 	ldrcc	r0, [ip], #256	; 0x100
    2e00:	00000f34 	andeq	r0, r0, r4, lsr pc
    2e04:	004f4a01 	subeq	r4, pc, r1, lsl #20
    2e08:	91020000 	mrsls	r0, (UNDEF: 2)
    2e0c:	6370376c 	cmnvs	r0, #108, 14	; 0x1b00000
    2e10:	4f4a0100 	svcmi	0x004a0100
    2e14:	02000000 	andeq	r0, r0, #0
    2e18:	81346891 	teqhi	r4, r1	; <illegal shifter operand>
    2e1c:	01000011 	tsteq	r0, r1, lsl r0
    2e20:	00004f4a 	andeq	r4, r0, sl, asr #30
    2e24:	64910200 	ldrvs	r0, [r1], #512	; 0x200
	...

Disassembly of section .debug_abbrev:

00000000 <.debug_abbrev>:
   0:	25011101 	strcs	r1, [r1, #-257]	; 0xfffffeff
   4:	0305130e 	movweq	r1, #21262	; 0x530e
   8:	1b17100e 	blne	5c4048 <ringBuffer+0x56c370>
   c:	5501110e 	strpl	r1, [r1, #-270]	; 0xfffffef2
  10:	02000017 	andeq	r0, r0, #23
  14:	0e030034 	mcreq	0, 0, r0, cr3, cr4, {1}
  18:	193f1349 	ldmdbne	pc!, {r0, r3, r6, r8, r9, ip}	; <UNPREDICTABLE>
  1c:	0b3b0b3a 	bleq	ec2d0c <ringBuffer+0xe6b034>
  20:	00001802 	andeq	r1, r0, r2, lsl #16
  24:	03002403 	movweq	r2, #1027	; 0x403
  28:	0b0b3e0e 	bleq	2cf868 <ringBuffer+0x277b90>
  2c:	0400000b 	streq	r0, [r0], #-11
  30:	13490101 	movtne	r0, #37121	; 0x9101
  34:	21050000 	mrscs	r0, (UNDEF: 5)
  38:	37134900 	ldrcc	r4, [r3, -r0, lsl #18]
  3c:	0600000b 	streq	r0, [r0], -fp
  40:	0e030024 	cdpeq	0, 0, cr0, cr3, cr4, {1}
  44:	0b3e0b0b 	bleq	f82c78 <ringBuffer+0xf2afa0>
  48:	26070000 	strcs	r0, [r7], -r0
  4c:	00134900 	andseq	r4, r3, r0, lsl #18
  50:	00160800 	andseq	r0, r6, r0, lsl #16
  54:	0e031349 	cdpeq	3, 0, cr1, cr3, cr9, {2}
  58:	0b3b0b3a 	bleq	ec2d48 <ringBuffer+0xe6b070>
  5c:	13090000 	movwne	r0, #36864	; 0x9000
  60:	0b0e0301 	bleq	380c6c <ringBuffer+0x328f94>
  64:	3b0b3a0b 	blcc	2ce898 <ringBuffer+0x276bc0>
  68:	0a00000b 	beq	9c <pthread_mutex_unlock@plt-0x10894>
  6c:	0e03000d 	cdpeq	0, 0, cr0, cr3, cr13, {0}
  70:	0b3a1349 	bleq	e84d9c <ringBuffer+0xe2d0c4>
  74:	0b380b3b 	bleq	e02d68 <ringBuffer+0xdab090>
  78:	040b0000 	streq	r0, [fp], #-0
  7c:	3a0b0b01 	bcc	2c2c88 <ringBuffer+0x26afb0>
  80:	000b3b0b 	andeq	r3, fp, fp, lsl #22
  84:	00280c00 	eoreq	r0, r8, r0, lsl #24
  88:	0d1c0e03 	ldceq	14, cr0, [ip, #-12]
  8c:	2e0d0000 	cdpcs	0, 0, cr0, cr13, cr0, {0}
  90:	12011100 	andne	r1, r1, #0, 2
  94:	03184006 	tsteq	r8, #6
  98:	3b0b3a0e 	blcc	2ce8d8 <ringBuffer+0x276c00>
  9c:	00193f0b 	andseq	r3, r9, fp, lsl #30
  a0:	012e0e00 			; <UNDEFINED> instruction: 0x012e0e00
  a4:	06120111 			; <UNDEFINED> instruction: 0x06120111
  a8:	0e031840 	cdpeq	8, 0, cr1, cr3, cr0, {2}
  ac:	0b3b0b3a 	bleq	ec2d9c <ringBuffer+0xe6b0c4>
  b0:	193f1927 	ldmdbne	pc!, {r0, r1, r2, r5, r8, fp, ip}	; <UNPREDICTABLE>
  b4:	050f0000 	streq	r0, [pc, #-0]	; bc <pthread_mutex_unlock@plt-0x10874>
  b8:	03180200 	tsteq	r8, #0, 4
  bc:	3b0b3a0e 	blcc	2ce8fc <ringBuffer+0x276c24>
  c0:	0013490b 	andseq	r4, r3, fp, lsl #18
  c4:	00341000 	eorseq	r1, r4, r0
  c8:	0e031802 	cdpeq	8, 0, cr1, cr3, cr2, {0}
  cc:	0b3b0b3a 	bleq	ec2dbc <ringBuffer+0xe6b0e4>
  d0:	00001049 	andeq	r1, r0, r9, asr #32
  d4:	11012e11 	tstne	r1, r1, lsl lr
  d8:	40061201 	andmi	r1, r6, r1, lsl #4
  dc:	3a0e0318 	bcc	380d44 <ringBuffer+0x32906c>
  e0:	3f0b3b0b 	svccc	0x000b3b0b
  e4:	12000019 	andne	r0, r0, #25
  e8:	0111010b 	tsteq	r1, fp, lsl #2
  ec:	00000612 	andeq	r0, r0, r2, lsl r6
  f0:	02003413 	andeq	r3, r0, #318767104	; 0x13000000
  f4:	3a0e0318 	bcc	380d5c <ringBuffer+0x329084>
  f8:	490b3b0b 	stmdbmi	fp, {r0, r1, r3, r8, r9, fp, ip, sp}
  fc:	14000013 	strne	r0, [r0], #-19	; 0xffffffed
 100:	18020034 	stmdane	r2, {r2, r4, r5}
 104:	0b3a0e03 	bleq	e83918 <ringBuffer+0xe2bc40>
 108:	1349053b 	movtne	r0, #38203	; 0x953b
 10c:	0b150000 	bleq	540114 <ringBuffer+0x4e843c>
 110:	00175501 	andseq	r5, r7, r1, lsl #10
 114:	012e1600 			; <UNDEFINED> instruction: 0x012e1600
 118:	06120111 			; <UNDEFINED> instruction: 0x06120111
 11c:	0e031840 	cdpeq	8, 0, cr1, cr3, cr0, {2}
 120:	053b0b3a 	ldreq	r0, [fp, #-2874]!	; 0xfffff4c6
 124:	0000193f 	andeq	r1, r0, pc, lsr r9
 128:	11012e17 	tstne	r1, r7, lsl lr
 12c:	40061201 	andmi	r1, r6, r1, lsl #4
 130:	3a0e0318 	bcc	380d98 <ringBuffer+0x3290c0>
 134:	27053b0b 	strcs	r3, [r5, -fp, lsl #22]
 138:	3f134919 	svccc	0x00134919
 13c:	18000019 	stmdane	r0, {r0, r3, r4}
 140:	18020005 	stmdane	r2, {r0, r2}
 144:	0b3a0e03 	bleq	e83958 <ringBuffer+0xe2bc80>
 148:	1349053b 	movtne	r0, #38203	; 0x953b
 14c:	2e190000 	cdpcs	0, 1, cr0, cr9, cr0, {0}
 150:	12011101 	andne	r1, r1, #1073741824	; 0x40000000
 154:	03184006 	tsteq	r8, #6
 158:	3b0b3a0e 	blcc	2ce998 <ringBuffer+0x276cc0>
 15c:	3f192705 	svccc	0x00192705
 160:	1a000019 	bne	1cc <pthread_mutex_unlock@plt-0x10764>
 164:	1349000f 	movtne	r0, #36879	; 0x900f
 168:	151b0000 	ldrne	r0, [fp, #-0]
 16c:	00192701 	andseq	r2, r9, r1, lsl #14
 170:	00051c00 	andeq	r1, r5, r0, lsl #24
 174:	00001349 	andeq	r1, r0, r9, asr #6
 178:	00000f1d 	andeq	r0, r0, sp, lsl pc
 17c:	00051e00 	andeq	r1, r5, r0, lsl #28
 180:	0e031802 	cdpeq	8, 0, cr1, cr3, cr2, {0}
 184:	0b3b0b3a 	bleq	ec2e74 <ringBuffer+0xe6b19c>
 188:	00001049 	andeq	r1, r0, r9, asr #32
 18c:	11012e1f 	tstne	r1, pc, lsl lr
 190:	40061201 	andmi	r1, r6, r1, lsl #4
 194:	3a0e0318 	bcc	380dfc <ringBuffer+0x329124>
 198:	270b3b0b 	strcs	r3, [fp, -fp, lsl #22]
 19c:	3f104919 	svccc	0x00104919
 1a0:	20000019 	andcs	r0, r0, r9, lsl r0
 1a4:	0111012e 	tsteq	r1, lr, lsr #2
 1a8:	18400612 	stmdane	r0, {r1, r4, r9, sl}^
 1ac:	0b3a0e03 	bleq	e839c0 <ringBuffer+0xe2bce8>
 1b0:	10490b3b 	subne	r0, r9, fp, lsr fp
 1b4:	0000193f 	andeq	r1, r0, pc, lsr r9
 1b8:	11012e21 	tstne	r1, r1, lsr #28
 1bc:	40061201 	andmi	r1, r6, r1, lsl #4
 1c0:	3a0e0318 	bcc	380e28 <ringBuffer+0x329150>
 1c4:	490b3b0b 	stmdbmi	fp, {r0, r1, r3, r8, r9, fp, ip, sp}
 1c8:	00193f13 	andseq	r3, r9, r3, lsl pc
 1cc:	00162200 	andseq	r2, r6, r0, lsl #4
 1d0:	0e031049 	cdpeq	0, 0, cr1, cr3, cr9, {2}
 1d4:	0b3b0b3a 	bleq	ec2ec4 <ringBuffer+0xe6b1ec>
 1d8:	11230000 			; <UNDEFINED> instruction: 0x11230000
 1dc:	130e2501 	movwne	r2, #58625	; 0xe501
 1e0:	100e0305 	andne	r0, lr, r5, lsl #6
 1e4:	110e1b17 	tstne	lr, r7, lsl fp
 1e8:	00061201 	andeq	r1, r6, r1, lsl #4
 1ec:	002e2400 	eoreq	r2, lr, r0, lsl #8
 1f0:	06120111 			; <UNDEFINED> instruction: 0x06120111
 1f4:	0e031840 	cdpeq	8, 0, cr1, cr3, cr0, {2}
 1f8:	0b3b0b3a 	bleq	ec2ee8 <ringBuffer+0xe6b210>
 1fc:	193f1927 	ldmdbne	pc!, {r0, r1, r2, r5, r8, fp, ip}	; <UNPREDICTABLE>
 200:	0d250000 	stceq	0, cr0, [r5, #-0]
 204:	490e0300 	stmdbmi	lr, {r8, r9}
 208:	3b0b3a10 	blcc	2cea50 <ringBuffer+0x276d78>
 20c:	000b380b 	andeq	r3, fp, fp, lsl #16
 210:	11010000 	mrsne	r0, (UNDEF: 1)
 214:	130e2501 	movwne	r2, #58625	; 0xe501
 218:	1b0e030b 	blne	380e4c <ringBuffer+0x329174>
 21c:	1201110e 	andne	r1, r1, #-2147483645	; 0x80000003
 220:	00171006 	andseq	r1, r7, r6
 224:	00240200 	eoreq	r0, r4, r0, lsl #4
 228:	0b3e0b0b 	bleq	f82e5c <ringBuffer+0xf2b184>
 22c:	00000e03 	andeq	r0, r0, r3, lsl #28
 230:	0b002403 	bleq	9244 <pthread_mutex_unlock@plt-0x76ec>
 234:	030b3e0b 	movweq	r3, #48651	; 0xbe0b
 238:	04000008 	streq	r0, [r0], #-8
 23c:	0e030016 	mcreq	0, 0, r0, cr3, cr6, {0}
 240:	0b3b0b3a 	bleq	ec2f30 <ringBuffer+0xe6b258>
 244:	00001349 	andeq	r1, r0, r9, asr #6
 248:	49002605 	stmdbmi	r0, {r0, r2, r9, sl, sp}
 24c:	06000013 			; <UNDEFINED> instruction: 0x06000013
 250:	0b0b000f 	bleq	2c0294 <ringBuffer+0x2685bc>
 254:	00001349 	andeq	r1, r0, r9, asr #6
 258:	0b000f07 	bleq	3e7c <pthread_mutex_unlock@plt-0xcab4>
 25c:	0800000b 	stmdaeq	r0, {r0, r1, r3}
 260:	0e030113 	mcreq	1, 0, r0, cr3, cr3, {0}
 264:	0b3a0b0b 	bleq	e82e98 <ringBuffer+0xe2b1c0>
 268:	13010b3b 	movwne	r0, #6971	; 0x1b3b
 26c:	0d090000 	stceq	0, cr0, [r9, #-0]
 270:	3a0e0300 	bcc	380e78 <ringBuffer+0x3291a0>
 274:	490b3b0b 	stmdbmi	fp, {r0, r1, r3, r8, r9, fp, ip, sp}
 278:	000b3813 	andeq	r3, fp, r3, lsl r8
 27c:	000d0a00 	andeq	r0, sp, r0, lsl #20
 280:	0b3a0e03 	bleq	e83a94 <ringBuffer+0xe2bdbc>
 284:	1349053b 	movtne	r0, #38203	; 0x953b
 288:	00000b38 	andeq	r0, r0, r8, lsr fp
 28c:	0300160b 	movweq	r1, #1547	; 0x60b
 290:	3b0b3a0e 	blcc	2cead0 <ringBuffer+0x276df8>
 294:	0c00000b 	stceq	0, cr0, [r0], {11}
 298:	13490101 	movtne	r0, #37121	; 0x9101
 29c:	00001301 	andeq	r1, r0, r1, lsl #6
 2a0:	4900210d 	stmdbmi	r0, {r0, r2, r3, r8, sp}
 2a4:	000b2f13 	andeq	r2, fp, r3, lsl pc
 2a8:	00130e00 	andseq	r0, r3, r0, lsl #28
 2ac:	193c0e03 	ldmdbne	ip!, {r0, r1, r9, sl, fp}
 2b0:	340f0000 	strcc	r0, [pc], #-0	; 2b8 <pthread_mutex_unlock@plt-0x10678>
 2b4:	3a0e0300 	bcc	380ebc <ringBuffer+0x3291e4>
 2b8:	49053b0b 	stmdbmi	r5, {r0, r1, r3, r8, r9, fp, ip, sp}
 2bc:	3c193f13 	ldccc	15, cr3, [r9], {19}
 2c0:	10000019 	andne	r0, r0, r9, lsl r0
 2c4:	0e030034 	mcreq	0, 0, r0, cr3, cr4, {1}
 2c8:	0b3b0b3a 	bleq	ec2fb8 <ringBuffer+0xe6b2e0>
 2cc:	193f1349 	ldmdbne	pc!, {r0, r3, r6, r8, r9, ip}	; <UNPREDICTABLE>
 2d0:	0000193c 	andeq	r1, r0, ip, lsr r9
 2d4:	00002111 	andeq	r2, r0, r1, lsl r1
 2d8:	01041200 	mrseq	r1, R12_usr
 2dc:	0b0b0e03 	bleq	2c3af0 <ringBuffer+0x26be18>
 2e0:	0b3a1349 	bleq	e8500c <ringBuffer+0xe2d334>
 2e4:	13010b3b 	movwne	r0, #6971	; 0x1b3b
 2e8:	28130000 	ldmdacs	r3, {}	; <UNPREDICTABLE>
 2ec:	1c0e0300 	stcne	3, cr0, [lr], {-0}
 2f0:	1400000b 	strne	r0, [r0], #-11
 2f4:	0803000d 	stmdaeq	r3, {r0, r2, r3}
 2f8:	0b3b0b3a 	bleq	ec2fe8 <ringBuffer+0xe6b310>
 2fc:	0b381349 	bleq	e05028 <ringBuffer+0xdad350>
 300:	34150000 	ldrcc	r0, [r5], #-0
 304:	3a0e0300 	bcc	380f0c <ringBuffer+0x329234>
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
 330:	0b3a0803 	bleq	e82344 <ringBuffer+0xe2a66c>
 334:	1349053b 	movtne	r0, #38203	; 0x953b
 338:	00001802 	andeq	r1, r0, r2, lsl #16
 33c:	03000518 	movweq	r0, #1304	; 0x518
 340:	3b0b3a0e 	blcc	2ceb80 <ringBuffer+0x276ea8>
 344:	02134905 	andseq	r4, r3, #81920	; 0x14000
 348:	19000018 	stmdbne	r0, {r3, r4}
 34c:	08030034 	stmdaeq	r3, {r2, r4, r5}
 350:	053b0b3a 	ldreq	r0, [fp, #-2874]!	; 0xfffff4c6
 354:	18021349 	stmdane	r2, {r0, r3, r6, r8, r9, ip}
 358:	261a0000 	ldrcs	r0, [sl], -r0
 35c:	1b000000 	blne	364 <pthread_mutex_unlock@plt-0x105cc>
 360:	193f012e 	ldmdbne	pc!, {r1, r2, r3, r5, r8}	; <UNPREDICTABLE>
 364:	0b3a0e03 	bleq	e83b78 <ringBuffer+0xe2bea0>
 368:	19270b3b 	stmdbne	r7!, {r0, r1, r3, r4, r5, r8, r9, fp}
 36c:	01111349 	tsteq	r1, r9, asr #6
 370:	18400612 	stmdane	r0, {r1, r4, r9, sl}^
 374:	01194296 			; <UNDEFINED> instruction: 0x01194296
 378:	1c000013 	stcne	0, cr0, [r0], {19}
 37c:	08030005 	stmdaeq	r3, {r0, r2}
 380:	0b3b0b3a 	bleq	ec3070 <ringBuffer+0xe6b398>
 384:	18021349 	stmdane	r2, {r0, r3, r6, r8, r9, ip}
 388:	051d0000 	ldreq	r0, [sp, #-0]
 38c:	3a0e0300 	bcc	380f94 <ringBuffer+0x3292bc>
 390:	490b3b0b 	stmdbmi	fp, {r0, r1, r3, r8, r9, fp, ip, sp}
 394:	00180213 	andseq	r0, r8, r3, lsl r2
 398:	00341e00 	eorseq	r1, r4, r0, lsl #28
 39c:	0b3a0803 	bleq	e823b0 <ringBuffer+0xe2a6d8>
 3a0:	13490b3b 	movtne	r0, #39739	; 0x9b3b
 3a4:	00001802 	andeq	r1, r0, r2, lsl #16
 3a8:	11010b1f 	tstne	r1, pc, lsl fp
 3ac:	00061201 	andeq	r1, r6, r1, lsl #4
 3b0:	012e2000 			; <UNDEFINED> instruction: 0x012e2000
 3b4:	0b3a0e03 	bleq	e83bc8 <ringBuffer+0xe2bef0>
 3b8:	19270b3b 	stmdbne	r7!, {r0, r1, r3, r4, r5, r8, r9, fp}
 3bc:	06120111 			; <UNDEFINED> instruction: 0x06120111
 3c0:	42961840 	addsmi	r1, r6, #64, 16	; 0x400000
 3c4:	00130119 	andseq	r0, r3, r9, lsl r1
 3c8:	012e2100 			; <UNDEFINED> instruction: 0x012e2100
 3cc:	0b3a0e03 	bleq	e83be0 <ringBuffer+0xe2bf08>
 3d0:	19270b3b 	stmdbne	r7!, {r0, r1, r3, r4, r5, r8, r9, fp}
 3d4:	06120111 			; <UNDEFINED> instruction: 0x06120111
 3d8:	42971840 	addsmi	r1, r7, #64, 16	; 0x400000
 3dc:	00130119 	andseq	r0, r3, r9, lsl r1
 3e0:	012e2200 			; <UNDEFINED> instruction: 0x012e2200
 3e4:	0b3a0e03 	bleq	e83bf8 <ringBuffer+0xe2bf20>
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
 418:	3b0b3a0e 	blcc	2cec58 <ringBuffer+0x276f80>
 41c:	4919270b 	ldmdbmi	r9, {r0, r1, r3, r8, r9, sl, sp}
 420:	12011113 	andne	r1, r1, #-1073741820	; 0xc0000004
 424:	97184006 	ldrls	r4, [r8, -r6]
 428:	00001942 	andeq	r1, r0, r2, asr #18
 42c:	01110100 	tsteq	r1, r0, lsl #2
 430:	0b130e25 	bleq	4c3ccc <ringBuffer+0x46bff4>
 434:	0e1b0e03 	cdpeq	14, 1, cr0, cr11, cr3, {0}
 438:	06120111 			; <UNDEFINED> instruction: 0x06120111
 43c:	00001710 	andeq	r1, r0, r0, lsl r7
 440:	03001602 	movweq	r1, #1538	; 0x602
 444:	3b0b3a0e 	blcc	2cec84 <ringBuffer+0x276fac>
 448:	0013490b 	andseq	r4, r3, fp, lsl #18
 44c:	00240300 	eoreq	r0, r4, r0, lsl #6
 450:	0b3e0b0b 	bleq	f83084 <ringBuffer+0xf2b3ac>
 454:	00000e03 	andeq	r0, r0, r3, lsl #28
 458:	0b002404 	bleq	9470 <pthread_mutex_unlock@plt-0x74c0>
 45c:	030b3e0b 	movweq	r3, #48651	; 0xbe0b
 460:	05000008 	streq	r0, [r0, #-8]
 464:	0b0b000f 	bleq	2c04a8 <ringBuffer+0x2687d0>
 468:	0f060000 	svceq	0x00060000
 46c:	490b0b00 	stmdbmi	fp, {r8, r9, fp}
 470:	07000013 	smladeq	r0, r3, r0, r0
 474:	13490026 	movtne	r0, #36902	; 0x9026
 478:	13080000 	movwne	r0, #32768	; 0x8000
 47c:	0b0e0301 	bleq	381088 <ringBuffer+0x3293b0>
 480:	3b0b3a0b 	blcc	2cecb4 <ringBuffer+0x276fdc>
 484:	0013010b 	andseq	r0, r3, fp, lsl #2
 488:	000d0900 	andeq	r0, sp, r0, lsl #18
 48c:	0b3a0e03 	bleq	e83ca0 <ringBuffer+0xe2bfc8>
 490:	13490b3b 	movtne	r0, #39739	; 0x9b3b
 494:	00000b38 	andeq	r0, r0, r8, lsr fp
 498:	03000d0a 	movweq	r0, #3338	; 0xd0a
 49c:	3b0b3a0e 	blcc	2cecdc <ringBuffer+0x277004>
 4a0:	38134905 	ldmdacc	r3, {r0, r2, r8, fp, lr}
 4a4:	0b00000b 	bleq	4d8 <pthread_mutex_unlock@plt-0x10458>
 4a8:	0e030016 	mcreq	0, 0, r0, cr3, cr6, {0}
 4ac:	0b3b0b3a 	bleq	ec319c <ringBuffer+0xe6b4c4>
 4b0:	010c0000 	mrseq	r0, (UNDEF: 12)
 4b4:	01134901 	tsteq	r3, r1, lsl #18
 4b8:	0d000013 	stceq	0, cr0, [r0, #-76]	; 0xffffffb4
 4bc:	13490021 	movtne	r0, #36897	; 0x9021
 4c0:	00000b2f 	andeq	r0, r0, pc, lsr #22
 4c4:	0300130e 	movweq	r1, #782	; 0x30e
 4c8:	00193c0e 	andseq	r3, r9, lr, lsl #24
 4cc:	00340f00 	eorseq	r0, r4, r0, lsl #30
 4d0:	0b3a0e03 	bleq	e83ce4 <ringBuffer+0xe2c00c>
 4d4:	1349053b 	movtne	r0, #38203	; 0x953b
 4d8:	193c193f 	ldmdbne	ip!, {r0, r1, r2, r3, r4, r5, r8, fp, ip}
 4dc:	34100000 	ldrcc	r0, [r0], #-0
 4e0:	3a0e0300 	bcc	3810e8 <ringBuffer+0x329410>
 4e4:	490b3b0b 	stmdbmi	fp, {r0, r1, r3, r8, r9, fp, ip, sp}
 4e8:	3c193f13 	ldccc	15, cr3, [r9], {19}
 4ec:	11000019 	tstne	r0, r9, lsl r0
 4f0:	00000021 	andeq	r0, r0, r1, lsr #32
 4f4:	0b011312 	bleq	45144 <teec_shm_alloc+0x4c>
 4f8:	3b0b3a0b 	blcc	2ced2c <ringBuffer+0x277054>
 4fc:	0013010b 	andseq	r0, r3, fp, lsl #2
 500:	01131300 	tsteq	r3, r0, lsl #6
 504:	0b3a060b 	bleq	e81d38 <ringBuffer+0xe2a060>
 508:	13010b3b 	movwne	r0, #6971	; 0x1b3b
 50c:	0d140000 	ldceq	0, cr0, [r4, #-0]
 510:	3a0e0300 	bcc	381118 <ringBuffer+0x329440>
 514:	490b3b0b 	stmdbmi	fp, {r0, r1, r3, r8, r9, fp, ip, sp}
 518:	00063813 	andeq	r3, r6, r3, lsl r8
 51c:	00211500 	eoreq	r1, r1, r0, lsl #10
 520:	062f1349 	strteq	r1, [pc], -r9, asr #6
 524:	34160000 	ldrcc	r0, [r6], #-0
 528:	3a0e0300 	bcc	381130 <ringBuffer+0x329458>
 52c:	490b3b0b 	stmdbmi	fp, {r0, r1, r3, r8, r9, fp, ip, sp}
 530:	02193f13 	andseq	r3, r9, #19, 30	; 0x4c
 534:	17000018 	smladne	r0, r8, r0, r0
 538:	0e030104 	adfeqs	f0, f3, f4
 53c:	13490b0b 	movtne	r0, #39691	; 0x9b0b
 540:	0b3b0b3a 	bleq	ec3230 <ringBuffer+0xe6b558>
 544:	00001301 	andeq	r1, r0, r1, lsl #6
 548:	03002818 	movweq	r2, #2072	; 0x818
 54c:	000b1c08 	andeq	r1, fp, r8, lsl #24
 550:	00341900 	eorseq	r1, r4, r0, lsl #18
 554:	0b3a0e03 	bleq	e83d68 <ringBuffer+0xe2c090>
 558:	1349053b 	movtne	r0, #38203	; 0x953b
 55c:	1802193f 	stmdane	r2, {r0, r1, r2, r3, r4, r5, r8, fp, ip}
 560:	341a0000 	ldrcc	r0, [sl], #-0
 564:	3a080300 	bcc	20116c <ringBuffer+0x1a9494>
 568:	49053b0b 	stmdbmi	r5, {r0, r1, r3, r8, r9, fp, ip, sp}
 56c:	02193f13 	andseq	r3, r9, #19, 30	; 0x4c
 570:	1b000018 	blne	5d8 <pthread_mutex_unlock@plt-0x10358>
 574:	193f002e 	ldmdbne	pc!, {r1, r2, r3, r5}	; <UNPREDICTABLE>
 578:	0b3a0e03 	bleq	e83d8c <ringBuffer+0xe2c0b4>
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
 5a8:	0b3a0e03 	bleq	e83dbc <ringBuffer+0xe2c0e4>
 5ac:	1349053b 	movtne	r0, #38203	; 0x953b
 5b0:	00001802 	andeq	r1, r0, r2, lsl #16
 5b4:	3f012e1e 	svccc	0x00012e1e
 5b8:	3a0e0319 	bcc	381224 <ringBuffer+0x32954c>
 5bc:	27053b0b 	strcs	r3, [r5, -fp, lsl #22]
 5c0:	12011119 	andne	r1, r1, #1073741830	; 0x40000006
 5c4:	96184006 	ldrls	r4, [r8], -r6
 5c8:	13011942 	movwne	r1, #6466	; 0x1942
 5cc:	341f0000 	ldrcc	r0, [pc], #-0	; 5d4 <pthread_mutex_unlock@plt-0x1035c>
 5d0:	3a0e0300 	bcc	3811d8 <ringBuffer+0x329500>
 5d4:	49053b0b 	stmdbmi	r5, {r0, r1, r3, r8, r9, fp, ip, sp}
 5d8:	00180213 	andseq	r0, r8, r3, lsl r2
 5dc:	012e2000 			; <UNDEFINED> instruction: 0x012e2000
 5e0:	0e03193f 			; <UNDEFINED> instruction: 0x0e03193f
 5e4:	0b3b0b3a 	bleq	ec32d4 <ringBuffer+0xe6b5fc>
 5e8:	01111927 	tsteq	r1, r7, lsr #18
 5ec:	18400612 	stmdane	r0, {r1, r4, r9, sl}^
 5f0:	01194296 			; <UNDEFINED> instruction: 0x01194296
 5f4:	21000013 	tstcs	r0, r3, lsl r0
 5f8:	0e030005 	cdpeq	0, 0, cr0, cr3, cr5, {0}
 5fc:	0b3b0b3a 	bleq	ec32ec <ringBuffer+0xe6b614>
 600:	18021349 	stmdane	r2, {r0, r3, r6, r8, r9, ip}
 604:	34220000 	strtcc	r0, [r2], #-0
 608:	3a0e0300 	bcc	381210 <ringBuffer+0x329538>
 60c:	490b3b0b 	stmdbmi	fp, {r0, r1, r3, r8, r9, fp, ip, sp}
 610:	00180213 	andseq	r0, r8, r3, lsl r2
 614:	010b2300 	mrseq	r2, (UNDEF: 59)
 618:	06120111 			; <UNDEFINED> instruction: 0x06120111
 61c:	2e240000 	cdpcs	0, 2, cr0, cr4, cr0, {0}
 620:	03193f01 	tsteq	r9, #1, 30
 624:	3b0b3a0e 	blcc	2cee64 <ringBuffer+0x27718c>
 628:	4919270b 	ldmdbmi	r9, {r0, r1, r3, r8, r9, sl, sp}
 62c:	12011113 	andne	r1, r1, #-1073741820	; 0xc0000004
 630:	97184006 	ldrls	r4, [r8, -r6]
 634:	13011942 	movwne	r1, #6466	; 0x1942
 638:	34250000 	strtcc	r0, [r5], #-0
 63c:	3a080300 	bcc	201244 <ringBuffer+0x1a956c>
 640:	490b3b0b 	stmdbmi	fp, {r0, r1, r3, r8, r9, fp, ip, sp}
 644:	00180213 	andseq	r0, r8, r3, lsl r2
 648:	012e2600 			; <UNDEFINED> instruction: 0x012e2600
 64c:	0e03193f 			; <UNDEFINED> instruction: 0x0e03193f
 650:	0b3b0b3a 	bleq	ec3340 <ringBuffer+0xe6b668>
 654:	01111349 	tsteq	r1, r9, asr #6
 658:	18400612 	stmdane	r0, {r1, r4, r9, sl}^
 65c:	01194297 			; <UNDEFINED> instruction: 0x01194297
 660:	27000013 	smladcs	r0, r3, r0, r0
 664:	0111010b 	tsteq	r1, fp, lsl #2
 668:	13010612 	movwne	r0, #5650	; 0x1612
 66c:	2e280000 	cdpcs	0, 2, cr0, cr8, cr0, {0}
 670:	03193f01 	tsteq	r9, #1, 30
 674:	3b0b3a08 	blcc	2cee9c <ringBuffer+0x2771c4>
 678:	4919270b 	ldmdbmi	r9, {r0, r1, r3, r8, r9, sl, sp}
 67c:	12011113 	andne	r1, r1, #-1073741820	; 0xc0000004
 680:	97184006 	ldrls	r4, [r8, -r6]
 684:	13011942 	movwne	r1, #6466	; 0x1942
 688:	2e290000 	cdpcs	0, 2, cr0, cr9, cr0, {0}
 68c:	03193f01 	tsteq	r9, #1, 30
 690:	3b0b3a0e 	blcc	2ceed0 <ringBuffer+0x2771f8>
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
 6d0:	0b130e25 	bleq	4c3f6c <ringBuffer+0x46c294>
 6d4:	0e1b0e03 	cdpeq	14, 1, cr0, cr11, cr3, {0}
 6d8:	06120111 			; <UNDEFINED> instruction: 0x06120111
 6dc:	00001710 	andeq	r1, r0, r0, lsl r7
 6e0:	0b002402 	bleq	96f0 <pthread_mutex_unlock@plt-0x7240>
 6e4:	030b3e0b 	movweq	r3, #48651	; 0xbe0b
 6e8:	0300000e 	movweq	r0, #14
 6ec:	0b0b0024 	bleq	2c0784 <ringBuffer+0x268aac>
 6f0:	08030b3e 	stmdaeq	r3, {r1, r2, r3, r4, r5, r8, r9, fp}
 6f4:	16040000 	strne	r0, [r4], -r0
 6f8:	3a0e0300 	bcc	381300 <ringBuffer+0x329628>
 6fc:	490b3b0b 	stmdbmi	fp, {r0, r1, r3, r8, r9, fp, ip, sp}
 700:	05000013 	streq	r0, [r0, #-19]	; 0xffffffed
 704:	0b0b000f 	bleq	2c0748 <ringBuffer+0x268a70>
 708:	0f060000 	svceq	0x00060000
 70c:	490b0b00 	stmdbmi	fp, {r8, r9, fp}
 710:	07000013 	smladeq	r0, r3, r0, r0
 714:	13490026 	movtne	r0, #36902	; 0x9026
 718:	34080000 	strcc	r0, [r8], #-0
 71c:	3a0e0300 	bcc	381324 <ringBuffer+0x32964c>
 720:	49053b0b 	stmdbmi	r5, {r0, r1, r3, r8, r9, fp, ip, sp}
 724:	3c193f13 	ldccc	15, cr3, [r9], {19}
 728:	09000019 	stmdbeq	r0, {r0, r3, r4}
 72c:	0e030034 	mcreq	0, 0, r0, cr3, cr4, {1}
 730:	0b3b0b3a 	bleq	ec3420 <ringBuffer+0xe6b748>
 734:	193f1349 	ldmdbne	pc!, {r0, r3, r6, r8, r9, ip}	; <UNPREDICTABLE>
 738:	0000193c 	andeq	r1, r0, ip, lsr r9
 73c:	2700150a 	strcs	r1, [r0, -sl, lsl #10]
 740:	0b000019 	bleq	7ac <pthread_mutex_unlock@plt-0x10184>
 744:	13490035 	movtne	r0, #36917	; 0x9035
 748:	010c0000 	mrseq	r0, (UNDEF: 12)
 74c:	01134901 	tsteq	r3, r1, lsl #18
 750:	0d000013 	stceq	0, cr0, [r0, #-76]	; 0xffffffb4
 754:	13490021 	movtne	r0, #36897	; 0x9021
 758:	00000b2f 	andeq	r0, r0, pc, lsr #22
 75c:	0301130e 	movweq	r1, #4878	; 0x130e
 760:	3a0b0b0e 	bcc	2c33a0 <ringBuffer+0x26b6c8>
 764:	010b3b0b 	tsteq	fp, fp, lsl #22
 768:	0f000013 	svceq	0x00000013
 76c:	0e03000d 	cdpeq	0, 0, cr0, cr3, cr13, {0}
 770:	0b3b0b3a 	bleq	ec3460 <ringBuffer+0xe6b788>
 774:	0b381349 	bleq	e054a0 <ringBuffer+0xdad7c8>
 778:	0d100000 	ldceq	0, cr0, [r0, #-0]
 77c:	3a0e0300 	bcc	381384 <ringBuffer+0x3296ac>
 780:	49053b0b 	stmdbmi	r5, {r0, r1, r3, r8, r9, fp, ip, sp}
 784:	000b3813 	andeq	r3, fp, r3, lsl r8
 788:	00161100 	andseq	r1, r6, r0, lsl #2
 78c:	0b3a0e03 	bleq	e83fa0 <ringBuffer+0xe2c2c8>
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
 7c4:	3a0b0b01 	bcc	2c33d0 <ringBuffer+0x26b6f8>
 7c8:	010b3b0b 	tsteq	fp, fp, lsl #22
 7cc:	19000013 	stmdbne	r0, {r0, r1, r4}
 7d0:	0803000d 	stmdaeq	r3, {r0, r2, r3}
 7d4:	053b0b3a 	ldreq	r0, [fp, #-2874]!	; 0xfffff4c6
 7d8:	0b381349 	bleq	e05504 <ringBuffer+0xdad82c>
 7dc:	161a0000 	ldrne	r0, [sl], -r0
 7e0:	3a0e0300 	bcc	3813e8 <ringBuffer+0x329710>
 7e4:	49053b0b 	stmdbmi	r5, {r0, r1, r3, r8, r9, fp, ip, sp}
 7e8:	1b000013 	blne	83c <pthread_mutex_unlock@plt-0x100f4>
 7ec:	0b0b0113 	bleq	2c0c40 <ringBuffer+0x268f68>
 7f0:	053b0b3a 	ldreq	r0, [fp, #-2874]!	; 0xfffff4c6
 7f4:	00001301 	andeq	r1, r0, r1, lsl #6
 7f8:	0b01171c 	bleq	46470 <mLBolusStepsLength+0x48>
 7fc:	3b0b3a0b 	blcc	2cf030 <ringBuffer+0x277358>
 800:	00130105 	andseq	r0, r3, r5, lsl #2
 804:	000d1d00 	andeq	r1, sp, r0, lsl #26
 808:	0b3a0e03 	bleq	e8401c <ringBuffer+0xe2c344>
 80c:	1349053b 	movtne	r0, #38203	; 0x953b
 810:	041e0000 	ldreq	r0, [lr], #-0
 814:	0b0e0301 	bleq	381420 <ringBuffer+0x329748>
 818:	3a13490b 	bcc	4d2c4c <ringBuffer+0x47af74>
 81c:	010b3b0b 	tsteq	fp, fp, lsl #22
 820:	1f000013 	svcne	0x00000013
 824:	0e030028 	cdpeq	0, 0, cr0, cr3, cr8, {1}
 828:	00000b1c 	andeq	r0, r0, ip, lsl fp
 82c:	03000d20 	movweq	r0, #3360	; 0xd20
 830:	3b0b3a08 	blcc	2cf058 <ringBuffer+0x277380>
 834:	3813490b 	ldmdacc	r3, {r0, r1, r3, r8, fp, lr}
 838:	2100000b 	tstcs	r0, fp
 83c:	060b0113 			; <UNDEFINED> instruction: 0x060b0113
 840:	0b3b0b3a 	bleq	ec3530 <ringBuffer+0xe6b858>
 844:	00001301 	andeq	r1, r0, r1, lsl #6
 848:	03000d22 	movweq	r0, #3362	; 0xd22
 84c:	3b0b3a0e 	blcc	2cf08c <ringBuffer+0x2773b4>
 850:	3813490b 	ldmdacc	r3, {r0, r1, r3, r8, fp, lr}
 854:	23000006 	movwcs	r0, #6
 858:	13490021 	movtne	r0, #36897	; 0x9021
 85c:	0000062f 	andeq	r0, r0, pc, lsr #12
 860:	03003424 	movweq	r3, #1060	; 0x424
 864:	3b0b3a0e 	blcc	2cf0a4 <ringBuffer+0x2773cc>
 868:	3f13490b 	svccc	0x0013490b
 86c:	00180219 	andseq	r0, r8, r9, lsl r2
 870:	00342500 	eorseq	r2, r4, r0, lsl #10
 874:	0b3a0803 	bleq	e82888 <ringBuffer+0xe2abb0>
 878:	13490b3b 	movtne	r0, #39739	; 0x9b3b
 87c:	1802193f 	stmdane	r2, {r0, r1, r2, r3, r4, r5, r8, fp, ip}
 880:	2e260000 	cdpcs	0, 2, cr0, cr6, cr0, {0}
 884:	03193f01 	tsteq	r9, #1, 30
 888:	3b0b3a0e 	blcc	2cf0c8 <ringBuffer+0x2773f0>
 88c:	11192705 	tstne	r9, r5, lsl #14
 890:	40061201 	andmi	r1, r6, r1, lsl #4
 894:	19429618 	stmdbne	r2, {r3, r4, r9, sl, ip, pc}^
 898:	00001301 	andeq	r1, r0, r1, lsl #6
 89c:	03000527 	movweq	r0, #1319	; 0x527
 8a0:	3b0b3a0e 	blcc	2cf0e0 <ringBuffer+0x277408>
 8a4:	02134905 	andseq	r4, r3, #81920	; 0x14000
 8a8:	28000018 	stmdacs	r0, {r3, r4}
 8ac:	0e030034 	mcreq	0, 0, r0, cr3, cr4, {1}
 8b0:	053b0b3a 	ldreq	r0, [fp, #-2874]!	; 0xfffff4c6
 8b4:	18021349 	stmdane	r2, {r0, r3, r6, r8, r9, ip}
 8b8:	0b290000 	bleq	a408c0 <ringBuffer+0x9e8be8>
 8bc:	12011101 	andne	r1, r1, #1073741824	; 0x40000000
 8c0:	2a000006 	bcs	8e0 <pthread_mutex_unlock@plt-0x10050>
 8c4:	08030034 	stmdaeq	r3, {r2, r4, r5}
 8c8:	053b0b3a 	ldreq	r0, [fp, #-2874]!	; 0xfffff4c6
 8cc:	18021349 	stmdane	r2, {r0, r3, r6, r8, r9, ip}
 8d0:	2e2b0000 	cdpcs	0, 2, cr0, cr11, cr0, {0}
 8d4:	03193f01 	tsteq	r9, #1, 30
 8d8:	3b0b3a0e 	blcc	2cf118 <ringBuffer+0x277440>
 8dc:	1113490b 	tstne	r3, fp, lsl #18
 8e0:	40061201 	andmi	r1, r6, r1, lsl #4
 8e4:	19429618 	stmdbne	r2, {r3, r4, r9, sl, ip, pc}^
 8e8:	00001301 	andeq	r1, r0, r1, lsl #6
 8ec:	0300342c 	movweq	r3, #1068	; 0x42c
 8f0:	3b0b3a0e 	blcc	2cf130 <ringBuffer+0x277458>
 8f4:	0213490b 	andseq	r4, r3, #180224	; 0x2c000
 8f8:	2d000018 	stccs	0, cr0, [r0, #-96]	; 0xffffffa0
 8fc:	193f012e 	ldmdbne	pc!, {r1, r2, r3, r5, r8}	; <UNPREDICTABLE>
 900:	0b3a0803 	bleq	e82914 <ringBuffer+0xe2ac3c>
 904:	13490b3b 	movtne	r0, #39739	; 0x9b3b
 908:	1301193c 	movwne	r1, #6460	; 0x193c
 90c:	182e0000 	stmdane	lr!, {}	; <UNPREDICTABLE>
 910:	2f000000 	svccs	0x00000000
 914:	0111010b 	tsteq	r1, fp, lsl #2
 918:	13010612 	movwne	r0, #5650	; 0x1612
 91c:	2e300000 	cdpcs	0, 3, cr0, cr0, cr0, {0}
 920:	03193f01 	tsteq	r9, #1, 30
 924:	3b0b3a0e 	blcc	2cf164 <ringBuffer+0x27748c>
 928:	3c13490b 			; <UNDEFINED> instruction: 0x3c13490b
 92c:	31000019 	tstcc	r0, r9, lsl r0
 930:	193f012e 	ldmdbne	pc!, {r1, r2, r3, r5, r8}	; <UNPREDICTABLE>
 934:	0b3a0e03 	bleq	e84148 <ringBuffer+0xe2c470>
 938:	1349053b 	movtne	r0, #38203	; 0x953b
 93c:	1301193c 	movwne	r1, #6460	; 0x193c
 940:	2e320000 	cdpcs	0, 3, cr0, cr2, cr0, {0}
 944:	03193f01 	tsteq	r9, #1, 30
 948:	3b0b3a0e 	blcc	2cf188 <ringBuffer+0x2774b0>
 94c:	3c134905 			; <UNDEFINED> instruction: 0x3c134905
 950:	33000019 	movwcc	r0, #25
 954:	193f012e 	ldmdbne	pc!, {r1, r2, r3, r5, r8}	; <UNPREDICTABLE>
 958:	0b3a0e03 	bleq	e8416c <ringBuffer+0xe2c494>
 95c:	19270b3b 	stmdbne	r7!, {r0, r1, r3, r4, r5, r8, r9, fp}
 960:	06120111 			; <UNDEFINED> instruction: 0x06120111
 964:	42961840 	addsmi	r1, r6, #64, 16	; 0x400000
 968:	00130119 	andseq	r0, r3, r9, lsl r1
 96c:	00053400 	andeq	r3, r5, r0, lsl #8
 970:	0b3a0e03 	bleq	e84184 <ringBuffer+0xe2c4ac>
 974:	13490b3b 	movtne	r0, #39739	; 0x9b3b
 978:	00001802 	andeq	r1, r0, r2, lsl #16
 97c:	03003435 	movweq	r3, #1077	; 0x435
 980:	3b0b3a08 	blcc	2cf1a8 <ringBuffer+0x2774d0>
 984:	0213490b 	andseq	r4, r3, #180224	; 0x2c000
 988:	36000018 			; <UNDEFINED> instruction: 0x36000018
 98c:	193f012e 	ldmdbne	pc!, {r1, r2, r3, r5, r8}	; <UNPREDICTABLE>
 990:	0b3a0e03 	bleq	e841a4 <ringBuffer+0xe2c4cc>
 994:	19270b3b 	stmdbne	r7!, {r0, r1, r3, r4, r5, r8, r9, fp}
 998:	06120111 			; <UNDEFINED> instruction: 0x06120111
 99c:	42971840 	addsmi	r1, r7, #64, 16	; 0x400000
 9a0:	00130119 	andseq	r0, r3, r9, lsl r1
 9a4:	00053700 	andeq	r3, r5, r0, lsl #14
 9a8:	0b3a0803 	bleq	e829bc <ringBuffer+0xe2ace4>
 9ac:	13490b3b 	movtne	r0, #39739	; 0x9b3b
 9b0:	00001802 	andeq	r1, r0, r2, lsl #16
 9b4:	3f002e38 	svccc	0x00002e38
 9b8:	3a0e0319 	bcc	381624 <ringBuffer+0x32994c>
 9bc:	110b3b0b 	tstne	fp, fp, lsl #22
 9c0:	40061201 	andmi	r1, r6, r1, lsl #4
 9c4:	19429618 	stmdbne	r2, {r3, r4, r9, sl, ip, pc}^
 9c8:	2e390000 	cdpcs	0, 3, cr0, cr9, cr0, {0}
 9cc:	03193f01 	tsteq	r9, #1, 30
 9d0:	3b0b3a0e 	blcc	2cf210 <ringBuffer+0x277538>
 9d4:	1119270b 	tstne	r9, fp, lsl #14
 9d8:	40061201 	andmi	r1, r6, r1, lsl #4
 9dc:	19429618 	stmdbne	r2, {r3, r4, r9, sl, ip, pc}^
 9e0:	地址 0x00000000000009e0 越界。


Disassembly of section .debug_line:

00000000 <.debug_line>:
       0:	000005e0 	andeq	r0, r0, r0, ror #11
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
      4c:	eb030004 	bl	c0064 <ringBuffer+0x6838c>
      50:	02050100 	andeq	r0, r5, #0, 2
      54:	3d08840a 	cfstrscc	mvf8, [r8, #-40]	; 0xffffffd8
      58:	0a05ae08 	beq	16b880 <ringBuffer+0x113ba8>
      5c:	05152402 	ldreq	r2, [r5, #-1026]	; 0xfffffbfe
      60:	054a0602 	strbeq	r0, [sl, #-1538]	; 0xfffff9fe
      64:	02054a0a 	andeq	r4, r5, #40960	; 0xa000
      68:	060a054a 	streq	r0, [sl], -sl, asr #10
      6c:	0602054b 	streq	r0, [r2], -fp, asr #10
      70:	4a0a054a 	bmi	2815a0 <ringBuffer+0x2298c8>
      74:	054a0205 	strbeq	r0, [sl, #-517]	; 0xfffffdfb
      78:	054b060f 	strbeq	r0, [fp, #-1551]	; 0xfffff9f1
      7c:	054a0602 	strbeq	r0, [sl, #-1538]	; 0xfffff9fe
      80:	e508060f 	str	r0, [r8, #-1551]	; 0xfffff9f1
      84:	4a060205 	bmi	1808a0 <ringBuffer+0x128bc8>
      88:	08060a05 	stmdaeq	r6, {r0, r2, r9, fp}
      8c:	060205e7 	streq	r0, [r2], -r7, ror #11
      90:	4a0a054a 	bmi	2815c0 <ringBuffer+0x2298e8>
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
      e8:	4b2c054f 	blmi	b0162c <ringBuffer+0xaa9954>
      ec:	4a063b05 	bmi	18ed08 <ringBuffer+0x137030>
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
     158:	4b0d0584 	blmi	341770 <ringBuffer+0x2e9a98>
     15c:	05491705 	strbeq	r1, [r9, #-1797]	; 0xfffff8fb
     160:	09054b0d 	stmdbeq	r5, {r0, r2, r3, r8, r9, fp, lr}
     164:	4b0b0549 	blmi	2c1690 <ringBuffer+0x2699b8>
     168:	054b0305 	strbeq	r0, [fp, #-773]	; 0xfffffcfb
     16c:	05ad080d 	streq	r0, [sp, #2061]!	; 0x80d
     170:	054a060b 	strbeq	r0, [sl, #-1547]	; 0xfffff9f5
     174:	76080603 	strvc	r0, [r8], -r3, lsl #12
     178:	054c1305 	strbeq	r1, [ip, #-773]	; 0xfffffcfb
     17c:	054a0611 	strbeq	r0, [sl, #-1553]	; 0xfffff9ef
     180:	3d080601 	stccc	6, cr0, [r8, #-4]
     184:	24020005 	strcs	r0, [r2], #-5
     188:	0a130514 	beq	4c15e0 <ringBuffer+0x469908>
     18c:	4d0e05c0 	cfstr32mi	mvfx0, [lr, #-768]	; 0xfffffd00
     190:	4a060405 	bmi	1811ac <ringBuffer+0x1294d4>
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
     1e0:	ba060605 	blt	1819fc <ringBuffer+0x129d24>
     1e4:	08061505 	stmdaeq	r6, {r0, r2, r8, sl, ip}
     1e8:	4b29053e 	blmi	a416e8 <ringBuffer+0x9e9a10>
     1ec:	054d0605 	strbeq	r0, [sp, #-1541]	; 0xfffff9fb
     1f0:	0a054607 	beq	151a14 <ringBuffer+0xf9d3c>
     1f4:	4829054d 	stmdami	r9!, {r0, r2, r3, r6, r8, sl}
     1f8:	4a062805 	bmi	18a214 <ringBuffer+0x13253c>
     1fc:	054a0705 	strbeq	r0, [sl, #-1797]	; 0xfffff8fb
     200:	054d0611 	strbeq	r0, [sp, #-1553]	; 0xfffff9ef
     204:	054a0606 	strbeq	r0, [sl, #-1542]	; 0xfffff9fa
     208:	2d054a15 	vstrcs	s8, [r5, #-84]	; 0xffffffac
     20c:	01040200 	mrseq	r0, R12_usr
     210:	00180582 	andseq	r0, r8, r2, lsl #11
     214:	4a010402 	bmi	41224 <blake2s_compress+0x370>
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
     2ac:	4a1d054a 	bmi	7417dc <ringBuffer+0x6e9b04>
     2b0:	054a0705 	strbeq	r0, [sl, #-1797]	; 0xfffff8fb
     2b4:	05be0606 	ldreq	r0, [lr, #1542]!	; 0x606
     2b8:	054a060b 	strbeq	r0, [sl, #-1547]	; 0xfffff9f5
     2bc:	4b064a06 	blmi	192adc <ringBuffer+0x13ae04>
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
     300:	4b830613 	blmi	fe0c1b54 <__bss_end__+0xf47d3580>
     304:	11054b49 	tstne	r5, r9, asr #22
     308:	05740806 	ldrbeq	r0, [r4, #-2054]!	; 0xfffff7fa
     30c:	06850606 	streq	r0, [r5], r6, lsl #12
     310:	0607054a 	streq	r0, [r7], -sl, asr #10
     314:	05820683 	streq	r0, [r2, #1667]	; 0x683
     318:	05830614 	streq	r0, [r3, #1556]	; 0x614
     31c:	14054b13 	strne	r4, [r5], #-2835	; 0xfffff4ed
     320:	4b130549 	blmi	4c184c <ringBuffer+0x469b74>
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
     34c:	4a0f054a 	bmi	3c187c <ringBuffer+0x369ba4>
     350:	054a0c05 	strbeq	r0, [sl, #-3077]	; 0xfffff3fb
     354:	06bc0606 	ldrteq	r0, [ip], r6, lsl #12
     358:	0612054a 	ldreq	r0, [r2], -sl, asr #10
     35c:	06080583 	streq	r0, [r8], -r3, lsl #11
     360:	4a12054a 	bmi	481890 <ringBuffer+0x429bb8>
     364:	054a0805 	strbeq	r0, [sl, #-2053]	; 0xfffff7fb
     368:	07054a10 	smladeq	r5, r0, sl, r4
     36c:	0610054a 	ldreq	r0, [r0], -sl, asr #10
     370:	060d05bb 			; <UNDEFINED> instruction: 0x060d05bb
     374:	05f5064a 	ldrbeq	r0, [r5, #1610]!	; 0x64a
     378:	08190302 	ldmdaeq	r9, {r1, r8, r9}
     37c:	000105ac 	andeq	r0, r1, ip, lsr #11
     380:	4b010402 	blmi	41390 <blake2s_compress+0x4dc>
     384:	3d030005 	stccc	0, cr0, [r3, #-20]	; 0xffffffec
     388:	0205e408 	andeq	lr, r5, #8, 8	; 0x8000000
     38c:	05f3bb0a 	ldrbeq	fp, [r3, #2826]!	; 0xb0a
     390:	0205bf00 	andeq	fp, r5, #0, 30
     394:	7508bb0a 	strvc	fp, [r8, #-2826]	; 0xfffff4f6
     398:	4c090583 	cfstr32mi	mvfx0, [r9], {131}	; 0x83
     39c:	054b0205 	strbeq	r0, [fp, #-517]	; 0xfffffdfb
     3a0:	10054909 	andne	r4, r5, r9, lsl #18
     3a4:	02054008 	andeq	r4, r5, #8
     3a8:	b910054b 	ldmdblt	r0, {r0, r1, r3, r6, r8, sl}
     3ac:	3f080605 	svccc	0x00080605
     3b0:	05bc0905 	ldreq	r0, [ip, #2309]!	; 0x905
     3b4:	0805bb03 	stmdaeq	r5, {r0, r1, r8, r9, fp, ip, sp, pc}
     3b8:	01040200 	mrseq	r0, R12_usr
     3bc:	00020548 	andeq	r0, r2, r8, asr #10
     3c0:	06010402 	streq	r0, [r1], -r2, lsl #8
     3c4:	8486064a 	strhi	r0, [r6], #1610	; 0x64a
     3c8:	0004c802 	andeq	ip, r4, r2, lsl #16
     3cc:	05000101 	streq	r0, [r0, #-257]	; 0xfffffeff
     3d0:	02000002 	andeq	r0, r0, #2
     3d4:	01d30300 	bicseq	r0, r3, r0, lsl #6
     3d8:	0a020501 	beq	817e4 <ringBuffer+0x29b0c>
     3dc:	081005f4 	ldmdaeq	r0, {r2, r4, r5, r6, r7, r8, sl}
     3e0:	4b0505ae 	blmi	141aa0 <ringBuffer+0xe9dc8>
     3e4:	05811005 	streq	r1, [r1, #5]
     3e8:	4a064b05 	bmi	193004 <ringBuffer+0x13b32c>
     3ec:	02060305 	andeq	r0, r6, #335544320	; 0x14000000
     3f0:	0a051330 	beq	1450b8 <ringBuffer+0xed3e0>
     3f4:	054a0685 	strbeq	r0, [sl, #-1669]	; 0xfffff97b
     3f8:	30020603 	andcc	r0, r2, r3, lsl #12
     3fc:	054b4613 	strbeq	r4, [fp, #-1555]	; 0xfffff9ed
     400:	4a100311 	bmi	40104c <ringBuffer+0x3a9374>
     404:	05bb0f05 	ldreq	r0, [fp, #3845]!	; 0xf05
     408:	10058302 	andne	r8, r5, r2, lsl #6
     40c:	4b01054b 	blmi	41940 <blake2s_compress+0xa8c>
     410:	72031c05 	andvc	r1, r3, #1280	; 0x500
     414:	0a053c08 	beq	14f43c <ringBuffer+0xf7764>
     418:	1c054a06 			; <UNDEFINED> instruction: 0x1c054a06
     41c:	4a0a054a 	bmi	28194c <ringBuffer+0x229c74>
     420:	0611054a 	ldreq	r0, [r1], -sl, asr #10
     424:	05133002 	ldreq	r3, [r3, #-2]
     428:	054a0623 	strbeq	r0, [sl, #-1571]	; 0xfffff9dd
     42c:	0d054a11 	vstreq	s8, [r5, #-68]	; 0xffffffbc
     430:	1c054b06 			; <UNDEFINED> instruction: 0x1c054b06
     434:	0d054a06 	vstreq	s8, [r5, #-24]	; 0xffffffe8
     438:	0607054a 	streq	r0, [r7], -sl, asr #10
     43c:	4b0d0549 	blmi	341968 <ringBuffer+0x2e9c90>
     440:	4a061c05 	bmi	18745c <ringBuffer+0x12f784>
     444:	054a0d05 	strbeq	r0, [sl, #-3333]	; 0xfffff2fb
     448:	03054a0b 	movweq	r4, #23051	; 0x5a0b
     44c:	05bbbe06 	ldreq	fp, [fp, #3590]!	; 0xe06
     450:	054a061b 	strbeq	r0, [sl, #-1563]	; 0xfffff9e5
     454:	4b064a03 	blmi	192c68 <ringBuffer+0x13af90>
     458:	4c020005 	stcmi	0, cr0, [r2], {5}
     45c:	0a1a051a 	beq	6818cc <ringBuffer+0x629bf4>
     460:	061005f6 			; <UNDEFINED> instruction: 0x061005f6
     464:	4a1a0582 	bmi	681a74 <ringBuffer+0x629d9c>
     468:	05821005 	streq	r1, [r2, #5]
     46c:	07054a18 	smladeq	r5, r8, sl, r4
     470:	0605054a 	streq	r0, [r5], -sl, asr #10
     474:	054a064b 	strbeq	r0, [sl, #-1611]	; 0xfffff9b5
     478:	05490607 	strbeq	r0, [r9, #-1543]	; 0xfffff9f9
     47c:	1930020a 	ldmdbne	r0!, {r1, r3, r9}
     480:	03054a06 	movweq	r4, #23046	; 0x5a06
     484:	13300206 	teqne	r0, #1610612736	; 0x60000000
     488:	054b1005 	strbeq	r1, [fp, #-5]
     48c:	054a0603 	strbeq	r0, [sl, #-1539]	; 0xfffff9fd
     490:	03054a10 	movweq	r4, #23056	; 0x5a10
     494:	0607054a 	streq	r0, [r7], -sl, asr #10
     498:	060e054b 	streq	r0, [lr], -fp, asr #10
     49c:	4a07054a 	bmi	1c19cc <ringBuffer+0x169cf4>
     4a0:	054a0d05 	strbeq	r0, [sl, #-3333]	; 0xfffff2fb
     4a4:	0e054a06 	vmlaeq.f32	s8, s10, s12
     4a8:	13340206 	teqne	r4, #1610612736	; 0x60000000
     4ac:	4a060b05 	bmi	1830c8 <ringBuffer+0x12b3f0>
     4b0:	03060305 	movweq	r0, #25349	; 0x6305
     4b4:	1005ba77 	andne	fp, r5, r7, ror sl
     4b8:	0603054b 	streq	r0, [r3], -fp, asr #10
     4bc:	4a10054a 	bmi	4019ec <ringBuffer+0x3a9d14>
     4c0:	054a0305 	strbeq	r0, [sl, #-773]	; 0xfffffcfb
     4c4:	054b0615 	strbeq	r0, [fp, #-1557]	; 0xfffff9eb
     4c8:	15054b0a 	strne	r4, [r5, #-2826]	; 0xfffff4f6
     4cc:	060b0549 	streq	r0, [fp], -r9, asr #10
     4d0:	4a13054a 	bmi	4c1a00 <ringBuffer+0x469d28>
     4d4:	054a0905 	strbeq	r0, [sl, #-2309]	; 0xfffff6fb
     4d8:	054b060a 	strbeq	r0, [fp, #-1546]	; 0xfffff9f6
     4dc:	0d054909 	vstreq.16	s8, [r5, #-18]	; 0xffffffee	; <UNPREDICTABLE>
     4e0:	060a054b 	streq	r0, [sl], -fp, asr #10
     4e4:	060b054a 	streq	r0, [fp], -sl, asr #10
     4e8:	10058550 	andne	r8, r5, r0, asr r5
     4ec:	47080589 	strmi	r0, [r8, -r9, lsl #11]
     4f0:	05f40b05 	ldrbeq	r0, [r4, #2821]!	; 0xb05
     4f4:	03058310 	movweq	r8, #21264	; 0x5310
     4f8:	15054a06 	strne	r4, [r5, #-2566]	; 0xfffff5fa
     4fc:	03058306 	movweq	r8, #21254	; 0x5306
     500:	10054a06 	andne	r4, r5, r6, lsl #20
     504:	03054c06 	movweq	r4, #23558	; 0x5c06
     508:	15054a06 	strne	r4, [r5, #-2566]	; 0xfffff5fa
     50c:	03058306 	movweq	r8, #21254	; 0x5306
     510:	1c054a06 			; <UNDEFINED> instruction: 0x1c054a06
     514:	02040200 	andeq	r0, r4, #0, 4
     518:	14054506 	strne	r4, [r5], #-1286	; 0xfffffafa
     51c:	01040200 	mrseq	r0, R12_usr
     520:	1005ba06 	andne	fp, r5, r6, lsl #20
     524:	01040200 	mrseq	r0, R12_usr
     528:	0002054a 	andeq	r0, r2, sl, asr #10
     52c:	4a010402 	bmi	4153c <blake2s_compress+0x688>
     530:	02060105 	andeq	r0, r6, #1073741825	; 0x40000001
     534:	00051a30 	andeq	r1, r5, r0, lsr sl
     538:	0200da03 	andeq	sp, r0, #12288	; 0x3000
     53c:	05050128 	streq	r0, [r5, #-296]	; 0xfffffed8
     540:	0605f90a 	streq	pc, [r5], -sl, lsl #18
     544:	05054b7f 	streq	r4, [r5, #-2943]	; 0xfffff481
     548:	054a064c 	strbeq	r0, [sl, #-1612]	; 0xfffff9b4
     54c:	3002060a 	andcc	r0, r2, sl, lsl #12
     550:	054a0616 	strbeq	r0, [sl, #-1558]	; 0xfffff9ea
     554:	3002060b 	andcc	r0, r2, fp, lsl #12
     558:	bb250513 	bllt	9419ac <ringBuffer+0x8e9cd4>
     55c:	05490905 	strbeq	r0, [r9, #-2309]	; 0xfffff6fb
     560:	25054b32 	strcs	r4, [r5, #-2866]	; 0xfffff4ce
     564:	32054a06 	andcc	r4, r5, #24576	; 0x6000
     568:	4a0b054a 	bmi	2c1a98 <ringBuffer+0x269dc0>
     56c:	054a3205 	strbeq	r3, [sl, #-517]	; 0xfffffdfb
     570:	32054a20 	andcc	r4, r5, #32, 20	; 0x20000
     574:	4a20054a 	bmi	801aa4 <ringBuffer+0x7a9dcc>
     578:	054a3205 	strbeq	r3, [sl, #-517]	; 0xfffffdfb
     57c:	05ed062d 	strbeq	r0, [sp, #1581]!	; 0x62d
     580:	054a0635 	strbeq	r0, [sl, #-1589]	; 0xfffff9cb
     584:	0b05822d 	bleq	160e40 <ringBuffer+0x109168>
     588:	8235054a 	eorshi	r0, r5, #310378496	; 0x12800000
     58c:	054a2805 	strbeq	r2, [sl, #-2053]	; 0xfffff7fb
     590:	28054a35 	stmdacs	r5, {r0, r2, r4, r5, r9, fp, lr}
     594:	4a35054a 	bmi	d41ac4 <ringBuffer+0xce9dec>
     598:	74080b05 	strvc	r0, [r8], #-2821	; 0xfffff4fb
     59c:	4b062e05 	blmi	18bdb8 <ringBuffer+0x1340e0>
     5a0:	05490905 	strbeq	r0, [r9, #-2309]	; 0xfffff6fb
     5a4:	0b054b2e 	bleq	153264 <ringBuffer+0xfb58c>
     5a8:	37054a06 	strcc	r4, [r5, -r6, lsl #20]
     5ac:	4a29054a 	bmi	a41adc <ringBuffer+0x9e9e04>
     5b0:	054a3705 	strbeq	r3, [sl, #-1797]	; 0xfffff8fb
     5b4:	37054a29 	strcc	r4, [r5, -r9, lsr #20]
     5b8:	0632054a 	ldrteq	r0, [r2], -sl, asr #10
     5bc:	0b054008 	bleq	1505e4 <ringBuffer+0xf890c>
     5c0:	09058206 	stmdbeq	r5, {r1, r2, r9, pc}
     5c4:	0602054a 	streq	r0, [r2], -sl, asr #10
     5c8:	1605bc4e 	strne	fp, [r5], -lr, asr #24
     5cc:	060205f3 			; <UNDEFINED> instruction: 0x060205f3
     5d0:	05840682 	streq	r0, [r4, #1666]	; 0x682
     5d4:	0205f316 	andeq	pc, r5, #1476395008	; 0x58000000
     5d8:	01058206 	tsteq	r5, r6, lsl #4
     5dc:	d4028306 	strle	r8, [r2], #-774	; 0xfffffcfa
     5e0:	01010004 	tsteq	r1, r4
     5e4:	00000166 	andeq	r0, r0, r6, ror #2
     5e8:	00660002 	rsbeq	r0, r6, r2
     5ec:	01010000 	mrseq	r0, (UNDEF: 1)
     5f0:	000d0efb 	strdeq	r0, [sp], -fp
     5f4:	01010101 	tsteq	r1, r1, lsl #2
     5f8:	01000000 	mrseq	r0, (UNDEF: 0)
     5fc:	2f010000 	svccs	0x00010000
     600:	2f727375 	svccs	0x00727375
     604:	6c636e69 	stclvs	14, cr6, [r3], #-420	; 0xfffffe5c
     608:	2f656475 	svccs	0x00656475
     60c:	73746962 	cmnvc	r4, #1605632	; 0x188000
     610:	73752f00 	cmnvc	r5, #0, 30
     614:	6e692f72 	mcrvs	15, 3, r2, cr9, cr2, {3}
     618:	64756c63 	ldrbtvs	r6, [r5], #-3171	; 0xfffff39d
     61c:	69622f65 	stmdbvs	r2!, {r0, r2, r5, r6, r8, r9, sl, fp, sp}^
     620:	742f7374 	strtvc	r7, [pc], #-884	; 628 <pthread_mutex_unlock@plt-0x10308>
     624:	73657079 	cmnvc	r5, #121	; 0x79
     628:	74750000 	ldrbtvc	r0, [r5], #-0
     62c:	632e6c69 			; <UNDEFINED> instruction: 0x632e6c69
     630:	00000000 	andeq	r0, r0, r0
     634:	65707974 	ldrbvs	r7, [r0, #-2420]!	; 0xfffff68c
     638:	00682e73 	rsbeq	r2, r8, r3, ror lr
     63c:	73000001 	movwvc	r0, #1
     640:	63757274 	cmnvs	r5, #116, 4	; 0x40000007
     644:	69745f74 	ldmdbvs	r4!, {r2, r4, r5, r6, r8, r9, sl, fp, ip, lr}^
     648:	6176656d 	cmnvs	r6, sp, ror #10
     64c:	00682e6c 	rsbeq	r2, r8, ip, ror #28
     650:	00000002 	andeq	r0, r0, r2
     654:	0c020500 	cfstr32eq	mvfx0, [r2], {-0}
     658:	19000408 	stmdbne	r0, {r3, sl}
     65c:	f30a0205 	vhsub.u8	d0, d10, d5
     660:	ba063905 	blt	18ea7c <ringBuffer+0x136da4>
     664:	064a0205 	strbeq	r0, [sl], -r5, lsl #4
     668:	f50005bb 			; <UNDEFINED> instruction: 0xf50005bb
     66c:	f40a0205 	vst1.8	{d0-d3}, [sl], r5
     670:	bb0905f3 	bllt	241e44 <ringBuffer+0x1ea16c>
     674:	4a060205 	bmi	180e90 <ringBuffer+0x1291b8>
     678:	08060005 	stmdaeq	r6, {r0, r2}
     67c:	0a020544 	beq	81b94 <ringBuffer+0x29ebc>
     680:	0005f3f3 	strdeq	pc, [r5], -r3
     684:	0a0605f5 	beq	181e60 <ringBuffer+0x12a188>
     688:	060405bd 			; <UNDEFINED> instruction: 0x060405bd
     68c:	0602054a 	streq	r0, [r2], -sl, asr #10
     690:	0622054c 	strteq	r0, [r2], -ip, asr #10
     694:	4a020582 	bmi	81ca4 <ringBuffer+0x29fcc>
     698:	84060605 	strhi	r0, [r6], #-1541	; 0xfffff9fb
     69c:	03054a06 	movweq	r4, #23046	; 0x5a06
     6a0:	4c484d06 	mcrrmi	13, 0, r4, r8, cr6
     6a4:	054b0105 	strbeq	r0, [fp, #-261]	; 0xfffffefb
     6a8:	053e0800 	ldreq	r0, [lr, #-2048]!	; 0xfffff800
     6ac:	05bd0a06 	ldreq	r0, [sp, #2566]!	; 0xa06
     6b0:	054a0604 	strbeq	r0, [sl, #-1540]	; 0xfffff9fc
     6b4:	054c0609 	strbeq	r0, [ip, #-1545]	; 0xfffff9f7
     6b8:	054a0602 	strbeq	r0, [sl, #-1538]	; 0xfffff9fe
     6bc:	058a0600 	streq	r0, [sl, #1536]	; 0x600
     6c0:	bbf40a02 	bllt	ffd02ed0 <__bss_end__+0xf64148fc>
     6c4:	05bb0905 	ldreq	r0, [fp, #2309]!	; 0x905
     6c8:	054a0602 	strbeq	r0, [sl, #-1538]	; 0xfffff9fe
     6cc:	05f50600 	ldrbeq	r0, [r5, #1536]!	; 0x600
     6d0:	05f50a02 	ldrbeq	r0, [r5, #2562]!	; 0xa02
     6d4:	0f05842c 	svceq	0x0005842c
     6d8:	2c054a06 			; <UNDEFINED> instruction: 0x2c054a06
     6dc:	ba16054a 	blt	581c0c <ringBuffer+0x529f34>
     6e0:	054a1d05 	strbeq	r1, [sl, #-3333]	; 0xfffff2fb
     6e4:	00054a02 	andeq	r4, r5, r2, lsl #20
     6e8:	0205be06 	andeq	fp, r5, #6, 28	; 0x60
     6ec:	1d05f50a 	cfstr32ne	mvfx15, [r5, #-40]	; 0xffffffd8
     6f0:	060f0584 	streq	r0, [pc], -r4, lsl #11
     6f4:	4a1d054a 	bmi	741c24 <ringBuffer+0x6e9f4c>
     6f8:	054a2405 	strbeq	r2, [sl, #-1029]	; 0xfffffbfb
     6fc:	60024a02 	andvs	r4, r2, r2, lsl #20
     700:	00010100 	andeq	r0, r1, r0, lsl #2
     704:	05ac0205 	streq	r0, [ip, #517]!	; 0x205
     708:	13030002 	movwne	r0, #12290	; 0x3002
     70c:	0a020501 	beq	81b18 <ringBuffer+0x29e40>
     710:	00053e08 	andeq	r3, r5, r8, lsl #28
     714:	05f21d03 	ldrbeq	r1, [r2, #3331]!	; 0xd03
     718:	05f30a02 	ldrbeq	r0, [r3, #2562]!	; 0xa02
     71c:	05ba063d 	ldreq	r0, [sl, #1597]!	; 0x63d
     720:	bb064a02 	bllt	192f30 <ringBuffer+0x13b258>
     724:	1c030005 	stcne	0, cr0, [r3], {5}
     728:	0905ac08 	stmdbeq	r5, {r3, sl, fp, sp, pc}
     72c:	0205f30a 	andeq	pc, r5, #671088640	; 0x28000000
     730:	01058206 	tsteq	r5, r6, lsl #4
     734:	00054b06 	andeq	r4, r5, r6, lsl #22
     738:	0a0d05f4 	beq	341f10 <ringBuffer+0x2ea238>
     73c:	060805f4 			; <UNDEFINED> instruction: 0x060805f4
     740:	4a060582 	bmi	181d50 <ringBuffer+0x12a078>
     744:	4b060205 	blmi	180f60 <ringBuffer+0x129288>
     748:	0002d002 	andeq	sp, r2, r2
     74c:	004d0101 	subeq	r0, sp, r1, lsl #2
     750:	00020000 	andeq	r0, r2, r0
     754:	0000001c 	andeq	r0, r0, ip, lsl r0
     758:	0efb0101 	cdpeq	1, 15, cr0, cr11, cr1, {0}
     75c:	0101000d 	tsteq	r1, sp
     760:	00000101 	andeq	r0, r0, r1, lsl #2
     764:	00000100 	andeq	r0, r0, r0, lsl #2
     768:	656c0001 	strbvs	r0, [ip, #-1]!
     76c:	00632e64 	rsbeq	r2, r3, r4, ror #28
     770:	00000000 	andeq	r0, r0, r0
     774:	74020500 	strvc	r0, [r2], #-1280	; 0xfffffb00
     778:	18000206 	stmdane	r0, {r1, r2, r9}
     77c:	830a0e05 	movwhi	r0, #44549	; 0xae05
     780:	054b0205 	strbeq	r0, [fp, #-517]	; 0xfffffdfb
     784:	0205810e 	andeq	r8, r5, #-2147483645	; 0x80000003
     788:	810e0583 	smlabbhi	lr, r3, r5, r0
     78c:	4b4b0205 	blmi	12c0fa8 <ringBuffer+0x12692d0>
     790:	77080005 	strvc	r0, [r8, -r5]
     794:	830a0205 	movwhi	r0, #41477	; 0xa205
     798:	01e802bb 	strheq	r0, [r8, #43]!	; 0x2b
     79c:	a5010100 	strge	r0, [r1, #-256]	; 0xffffff00
     7a0:	02000000 	andeq	r0, r0, #0
     7a4:	00003f00 	andeq	r3, r0, r0, lsl #30
     7a8:	fb010100 	blx	40bb2 <secure_zero_memory>
     7ac:	01000d0e 	tsteq	r0, lr, lsl #26
     7b0:	00010101 	andeq	r0, r1, r1, lsl #2
     7b4:	00010000 	andeq	r0, r1, r0
     7b8:	2f2e0100 	svccs	0x002e0100
     7bc:	0062696c 	rsbeq	r6, r2, ip, ror #18
     7c0:	71694c00 	cmnvc	r9, r0, lsl #24
     7c4:	43646975 	cmnmi	r4, #1916928	; 0x1d4000
     7c8:	74737972 	ldrbtvc	r7, [r3], #-2418	; 0xfffff68e
     7cc:	632e6c61 			; <UNDEFINED> instruction: 0x632e6c61
     7d0:	00000000 	andeq	r0, r0, r0
     7d4:	7571694c 	ldrbvc	r6, [r1, #-2380]!	; 0xfffff6b4
     7d8:	72436469 	subvc	r6, r3, #1761607680	; 0x69000000
     7dc:	61747379 	cmnvs	r4, r9, ror r3
     7e0:	00682e6c 	rsbeq	r2, r8, ip, ror #28
     7e4:	00000001 	andeq	r0, r0, r1
     7e8:	d8020500 	stmdale	r2, {r8, sl}
     7ec:	17000409 	strne	r0, [r0, -r9, lsl #8]
     7f0:	bc0a0e05 	stclt	14, cr0, [sl], {5}
     7f4:	3e080205 	cdpcc	2, 0, cr0, cr8, cr5, {0}
     7f8:	05480e05 	strbeq	r0, [r8, #-3589]	; 0xfffff1fb
     7fc:	73058468 	movwvc	r8, #21608	; 0x5468
     800:	02054a06 	andeq	r4, r5, #24576	; 0x6000
     804:	02f3064a 	rscseq	r0, r3, #77594624	; 0x4a00000
     808:	01010014 	tsteq	r1, r4, lsl r0
     80c:	e0020500 	and	r0, r2, r0, lsl #10
     810:	03000206 	movweq	r0, #518	; 0x206
     814:	0205010d 	andeq	r0, r5, #1073741827	; 0x40000003
     818:	3d08bb0a 	vstrcc	d11, [r8, #-40]	; 0xffffffd8
     81c:	77080005 	strvc	r0, [r8, -r5]
     820:	080a0205 	stmdaeq	sl, {r0, r2, r9}
     824:	0659053d 			; <UNDEFINED> instruction: 0x0659053d
     828:	4a5e054a 	bmi	1781d58 <ringBuffer+0x172a080>
     82c:	064a0205 	strbeq	r0, [sl], -r5, lsl #4
     830:	00057508 	andeq	r7, r5, r8, lsl #10
     834:	02057708 	andeq	r7, r5, #8, 14	; 0x200000
     838:	4f05bb0a 	svcmi	0x0005bb0a
     83c:	0205f206 	andeq	pc, r5, #1610612736	; 0x60000000
     840:	02f30682 	rscseq	r0, r3, #136314880	; 0x8200000
     844:	01010018 	tsteq	r1, r8, lsl r0
     848:	00000334 	andeq	r0, r0, r4, lsr r3
     84c:	01640002 	cmneq	r4, r2
     850:	01020000 	mrseq	r0, (UNDEF: 2)
     854:	000d0efb 	strdeq	r0, [sp], -fp
     858:	01010101 	tsteq	r1, r1, lsl #2
     85c:	01000000 	mrseq	r0, (UNDEF: 0)
     860:	2f010000 	svccs	0x00010000
     864:	656d6f68 	strbvs	r6, [sp, #-3944]!	; 0xfffff098
     868:	62736f2f 	rsbsvs	r6, r3, #47, 30	; 0xbc
     86c:	7365786f 	cmnvc	r5, #7274496	; 0x6f0000
     870:	7665642f 	strbtvc	r6, [r5], -pc, lsr #8
     874:	6f2f6c65 	svcvs	0x002f6c65
     878:	65657470 	strbvs	r7, [r5, #-1136]!	; 0xfffffb90
     87c:	6f6f742f 	svcvs	0x006f742f
     880:	6168636c 	cmnvs	r8, ip, ror #6
     884:	2f736e69 	svccs	0x00736e69
     888:	63726161 	cmnvs	r2, #1073741848	; 0x40000018
     88c:	2f323368 	svccs	0x00323368
     890:	2d6d7261 	sfmcs	f7, 2, [sp, #-388]!	; 0xfffffe7c
     894:	756e696c 	strbvc	r6, [lr, #-2412]!	; 0xfffff694
     898:	6e672d78 	mcrvs	13, 3, r2, cr7, cr8, {3}
     89c:	62616575 	rsbvs	r6, r1, #490733568	; 0x1d400000
     8a0:	2f666869 	svccs	0x00666869
     8a4:	6362696c 	cmnvs	r2, #108, 18	; 0x1b0000
     8a8:	7273752f 	rsbsvc	r7, r3, #197132288	; 0xbc00000
     8ac:	636e692f 	cmnvs	lr, #770048	; 0xbc000
     8b0:	6564756c 	strbvs	r7, [r4, #-1388]!	; 0xfffffa94
     8b4:	6f682f00 	svcvs	0x00682f00
     8b8:	6f2f656d 	svcvs	0x002f656d
     8bc:	786f6273 	stmdavc	pc!, {r0, r1, r4, r5, r6, r9, sp, lr}^	; <UNPREDICTABLE>
     8c0:	642f7365 	strtvs	r7, [pc], #-869	; 8c8 <pthread_mutex_unlock@plt-0x10068>
     8c4:	6c657665 	stclvs	6, cr7, [r5], #-404	; 0xfffffe6c
     8c8:	74706f2f 	ldrbtvc	r6, [r0], #-3887	; 0xfffff0d1
     8cc:	742f6565 	strtvc	r6, [pc], #-1381	; 8d4 <pthread_mutex_unlock@plt-0x1005c>
     8d0:	636c6f6f 	cmnvs	ip, #444	; 0x1bc
     8d4:	6e696168 	powvsez	f6, f1, #0.0
     8d8:	61612f73 	smcvs	4851	; 0x12f3
     8dc:	33686372 	cmncc	r8, #-939524095	; 0xc8000001
     8e0:	696c2f32 	stmdbvs	ip!, {r1, r4, r5, r8, r9, sl, fp, sp}^
     8e4:	63672f62 	cmnvs	r7, #392	; 0x188
     8e8:	72612f63 	rsbvc	r2, r1, #396	; 0x18c
     8ec:	696c2d6d 	stmdbvs	ip!, {r0, r2, r3, r5, r6, r8, sl, fp, sp}^
     8f0:	2d78756e 	cfldr64cs	mvdx7, [r8, #-440]!	; 0xfffffe48
     8f4:	65756e67 	ldrbvs	r6, [r5, #-3687]!	; 0xfffff199
     8f8:	68696261 	stmdavs	r9!, {r0, r5, r6, r9, sp, lr}^
     8fc:	2e362f66 	cdpcs	15, 3, cr2, cr6, cr6, {3}
     900:	2f312e32 	svccs	0x00312e32
     904:	6c636e69 	stclvs	14, cr6, [r3], #-420	; 0xfffffe5c
     908:	00656475 	rsbeq	r6, r5, r5, ror r4
     90c:	64656d2f 	strbtvs	r6, [r5], #-3375	; 0xfffff2d1
     910:	722f6169 	eorvc	r6, pc, #1073741850	; 0x4000001a
     914:	752f6970 	strvc	r6, [pc, #-2416]!	; ffffffac <__bss_end__+0xf67119d8>
     918:	692f7273 	stmdbvs	pc!, {r0, r1, r4, r5, r6, r9, ip, sp, lr}	; <UNPREDICTABLE>
     91c:	756c636e 	strbvc	r6, [ip, #-878]!	; 0xfffffc92
     920:	612f6564 			; <UNDEFINED> instruction: 0x612f6564
     924:	6c2d6d72 	stcvs	13, cr6, [sp], #-456	; 0xfffffe38
     928:	78756e69 	ldmdavc	r5!, {r0, r3, r5, r6, r9, sl, fp, sp, lr}^
     92c:	756e672d 	strbvc	r6, [lr, #-1837]!	; 0xfffff8d3
     930:	69626165 	stmdbvs	r2!, {r0, r2, r5, r6, r8, sp, lr}^
     934:	622f6668 	eorvs	r6, pc, #104, 12	; 0x6800000
     938:	00737469 	rsbseq	r7, r3, r9, ror #8
     93c:	616c6200 	cmnvs	ip, r0, lsl #4
     940:	2d32656b 	cfldr32cs	mvfx6, [r2, #-428]!	; 0xfffffe54
     944:	6c706d69 	ldclvs	13, cr6, [r0], #-420	; 0xfffffe5c
     948:	0000682e 	andeq	r6, r0, lr, lsr #16
     94c:	6c620000 	stclvs	0, cr0, [r2], #-0
     950:	32656b61 	rsbcc	r6, r5, #99328	; 0x18400
     954:	65722d73 	ldrbvs	r2, [r2, #-3443]!	; 0xfffff28d
     958:	00632e66 	rsbeq	r2, r3, r6, ror #28
     95c:	73000000 	movwvc	r0, #0
     960:	6e696474 	mcrvs	4, 3, r6, cr9, cr4, {3}
     964:	00682e74 	rsbeq	r2, r8, r4, ror lr
     968:	73000001 	movwvc	r0, #1
     96c:	65646474 	strbvs	r6, [r4, #-1140]!	; 0xfffffb8c
     970:	00682e66 	rsbeq	r2, r8, r6, ror #28
     974:	74000002 	strvc	r0, [r0], #-2
     978:	73657079 	cmnvc	r5, #121	; 0x79
     97c:	0300682e 	movweq	r6, #2094	; 0x82e
     980:	696c0000 	stmdbvs	ip!, {}^	; <UNPREDICTABLE>
     984:	2e6f6962 	vnmulcs.f16	s13, s30, s5	; <UNPREDICTABLE>
     988:	00010068 	andeq	r0, r1, r8, rrx
     98c:	64747300 	ldrbtvs	r7, [r4], #-768	; 0xfffffd00
     990:	682e6f69 	stmdavs	lr!, {r0, r3, r5, r6, r8, r9, sl, fp, sp, lr}
     994:	00000100 	andeq	r0, r0, r0, lsl #2
     998:	5f737973 	svcpl	0x00737973
     99c:	6c727265 	lfmvs	f7, 2, [r2], #-404	; 0xfffffe6c
     9a0:	2e747369 	cdpcs	3, 7, cr7, cr4, cr9, {3}
     9a4:	00030068 	andeq	r0, r3, r8, rrx
     9a8:	616c6200 	cmnvs	ip, r0, lsl #4
     9ac:	2e32656b 	cdpcs	5, 3, cr6, cr2, cr11, {3}
     9b0:	00000068 	andeq	r0, r0, r8, rrx
     9b4:	05000000 	streq	r0, [r0, #-0]
     9b8:	040ad802 	streq	sp, [sl], #-2050	; 0xfffff7fe
     9bc:	01210300 			; <UNDEFINED> instruction: 0x01210300
     9c0:	493d2f50 	ldmdbmi	sp!, {r4, r6, r8, r9, sl, fp, sp}
     9c4:	49224922 	stmdbmi	r2!, {r1, r5, r8, fp, lr}
     9c8:	66230323 	strtvs	r0, [r3], -r3, lsr #6
     9cc:	68912f6a 	ldmvs	r1, {r1, r3, r5, r6, r8, r9, sl, fp, sp}
     9d0:	4b2f5c69 	blmi	bd7b7c <ringBuffer+0xb7fea4>
     9d4:	03686767 	cmneq	r8, #27000832	; 0x19c0000
     9d8:	4b59662a 	blmi	165a288 <ringBuffer+0x16025b0>
     9dc:	5a660903 	bpl	1982df0 <ringBuffer+0x192b118>
     9e0:	03020475 	movweq	r0, #9333	; 0x2475
     9e4:	4b747f8e 	blmi	1d20824 <ringBuffer+0x1cc8b4c>
     9e8:	754b6a4b 	strbvc	r6, [fp, #-2635]	; 0xfffff5b5
     9ec:	02004b69 	andeq	r4, r0, #107520	; 0x1a400
     9f0:	58060104 	stmdapl	r6, {r2, r8}
     9f4:	4d4b3e06 	stclmi	14, cr3, [fp, #-24]	; 0xffffffe8
     9f8:	69c96759 	stmibvs	r9, {r0, r3, r4, r6, r8, r9, sl, sp, lr}^
     9fc:	02005a4c 	andeq	r5, r0, #76, 20	; 0x4c000
     a00:	3c060304 	stccc	3, cr0, [r6], {4}
     a04:	01040200 	mrseq	r0, R12_usr
     a08:	783d06c8 	ldmdavc	sp!, {r3, r6, r7, r9, sl}
     a0c:	003f3159 	eorseq	r3, pc, r9, asr r1	; <UNPREDICTABLE>
     a10:	3d030402 	cfstrscc	mvf0, [r3, #-8]
     a14:	03040200 	movweq	r0, #16896	; 0x4200
     a18:	040200ff 	streq	r0, [r2], #-255	; 0xffffff01
     a1c:	063c0601 	ldrteq	r0, [ip], -r1, lsl #12
     a20:	4f21593f 	svcmi	0x0021593f
     a24:	0402005c 	streq	r0, [r2], #-92	; 0xffffffa4
     a28:	003c0602 	eorseq	r0, ip, r2, lsl #12
     a2c:	3c030402 	cfstrscc	mvf0, [r3], {2}
     a30:	2f3d3e06 	svccs	0x003d3e06
     a34:	75752f2f 	ldrbvc	r2, [r5, #-3887]!	; 0xfffff0d1
     a38:	83302f75 	teqhi	r0, #468	; 0x1d4
     a3c:	04020083 	streq	r0, [r2], #-131	; 0xffffff7d
     a40:	774d7501 	strbvc	r7, [sp, -r1, lsl #10]
     a44:	02040200 	andeq	r0, r4, #0, 4
     a48:	02003c06 	andeq	r3, r0, #1536	; 0x600
     a4c:	063c0304 	ldrteq	r0, [ip], -r4, lsl #6
     a50:	0402003e 	streq	r0, [r2], #-62	; 0xffffffc2
     a54:	003c0602 	eorseq	r0, ip, r2, lsl #12
     a58:	3c040402 	cfstrscc	mvf0, [r4], {2}
     a5c:	05040200 	streq	r0, [r4, #-512]	; 0xfffffe00
     a60:	4b3e063c 	blmi	f82358 <ringBuffer+0xf2a680>
     a64:	753d3d4b 	ldrvc	r3, [sp, #-3403]!	; 0xfffff2b5
     a68:	3e3d7575 	mrccc	5, 1, r7, cr13, cr5, {3}
     a6c:	02008483 	andeq	r8, r0, #-2097152000	; 0x83000000
     a70:	90060104 	andls	r0, r6, r4, lsl #2
     a74:	75754006 	ldrbvc	r4, [r5, #-6]!
     a78:	02006875 	andeq	r6, r0, #7667712	; 0x750000
     a7c:	03210104 			; <UNDEFINED> instruction: 0x03210104
     a80:	005d4a1b 	subseq	r4, sp, fp, lsl sl
     a84:	4b030402 	blmi	c1a94 <ringBuffer+0x69dbc>
     a88:	03040200 	movweq	r0, #16896	; 0x4200
     a8c:	040200ff 	streq	r0, [r2], #-255	; 0xffffff01
     a90:	06580601 	ldrbeq	r0, [r8], -r1, lsl #12
     a94:	0402004e 	streq	r0, [r2], #-78	; 0xffffffb2
     a98:	02004b03 	andeq	r4, r0, #3072	; 0xc00
     a9c:	00c70304 	sbceq	r0, r7, r4, lsl #6
     aa0:	06010402 	streq	r0, [r1], -r2, lsl #8
     aa4:	594e0658 	stmdbpl	lr, {r3, r4, r6, r9, sl}^
     aa8:	83595959 	cmphi	r9, #1458176	; 0x164000
     aac:	02848383 	addeq	r8, r4, #201326594	; 0xc000002
     ab0:	021304a0 	andseq	r0, r3, #160, 8	; 0xa0000000
     ab4:	021304a0 	andseq	r0, r3, #160, 8	; 0xa0000000
     ab8:	021304a0 	andseq	r0, r3, #160, 8	; 0xa0000000
     abc:	021304a0 	andseq	r0, r3, #160, 8	; 0xa0000000
     ac0:	021304a0 	andseq	r0, r3, #160, 8	; 0xa0000000
     ac4:	021304a0 	andseq	r0, r3, #160, 8	; 0xa0000000
     ac8:	021304a0 	andseq	r0, r3, #160, 8	; 0xa0000000
     acc:	021304a0 	andseq	r0, r3, #160, 8	; 0xa0000000
     ad0:	021304a0 	andseq	r0, r3, #160, 8	; 0xa0000000
     ad4:	001404a0 	andseq	r0, r4, r0, lsr #9
     ad8:	4b030402 	blmi	c1ae8 <ringBuffer+0x69e10>
     adc:	03040200 	movweq	r0, #16896	; 0x4200
     ae0:	0200c708 	andeq	ip, r0, #8, 14	; 0x200000
     ae4:	58060104 	stmdapl	r6, {r2, r8}
     ae8:	67504d06 	ldrbvs	r4, [r0, -r6, lsl #26]
     aec:	4b3d3e2f 	blmi	f503b0 <ringBuffer+0xef86d8>
     af0:	4b9f3d4c 	blmi	fe7d0028 <__bss_end__+0xf4ee1a54>
     af4:	4b218367 	blmi	861898 <ringBuffer+0x809bc0>
     af8:	43383d4b 	teqmi	r8, #4800	; 0x12c0
     afc:	4d2168ad 	stcmi	8, cr6, [r1, #-692]!	; 0xfffffd4c
     b00:	02007767 	andeq	r7, r0, #27000832	; 0x19c0000
     b04:	3c060104 	stfccs	f0, [r6], {4}
     b08:	673e5906 	ldrvs	r5, [lr, -r6, lsl #18]!
     b0c:	d73d673e 			; <UNDEFINED> instruction: 0xd73d673e
     b10:	04020068 	streq	r0, [r2], #-104	; 0xffffff98
     b14:	02003d03 	andeq	r3, r0, #3, 26	; 0xc0
     b18:	00b90304 	adcseq	r0, r9, r4, lsl #6
     b1c:	06010402 	streq	r0, [r1], -r2, lsl #8
     b20:	753f063c 	ldrvc	r0, [pc, #-1596]!	; 4ec <pthread_mutex_unlock@plt-0x10444>
     b24:	04020067 	streq	r0, [r2], #-103	; 0xffffff99
     b28:	784d2101 	stmdavc	sp, {r0, r8, sp}^
     b2c:	01040200 	mrseq	r0, R12_usr
     b30:	02003c06 	andeq	r3, r0, #1536	; 0x600
     b34:	063c0204 	ldrteq	r0, [ip], -r4, lsl #4
     b38:	0402003e 	streq	r0, [r2], #-62	; 0xffffffc2
     b3c:	063c0601 	ldrteq	r0, [ip], -r1, lsl #12
     b40:	0402003e 	streq	r0, [r2], #-62	; 0xffffffc2
     b44:	004a0601 	subeq	r0, sl, r1, lsl #12
     b48:	4a020402 	bmi	81b58 <ringBuffer+0x29e80>
     b4c:	02003e06 	andeq	r3, r0, #6, 28	; 0x60
     b50:	3c060204 	sfmcc	f0, 4, [r6], {4}
     b54:	03040200 	movweq	r0, #16896	; 0x4200
     b58:	003e063c 	eorseq	r0, lr, ip, lsr r6
     b5c:	06010402 	streq	r0, [r1], -r2, lsl #8
     b60:	4c3e064a 	ldcmi	6, cr0, [lr], #-296	; 0xfffffed8
     b64:	01040200 	mrseq	r0, R12_usr
     b68:	4006ba06 	andmi	fp, r6, r6, lsl #20
     b6c:	01040200 	mrseq	r0, R12_usr
     b70:	3f069006 	svccc	0x00069006
     b74:	02007575 	andeq	r7, r0, #490733568	; 0x1d400000
     b78:	02210104 	eoreq	r0, r1, #4, 2
     b7c:	01010004 	tsteq	r1, r4
     b80:	00000413 	andeq	r0, r0, r3, lsl r4
     b84:	02230002 	eoreq	r0, r3, #2
     b88:	01020000 	mrseq	r0, (UNDEF: 2)
     b8c:	000d0efb 	strdeq	r0, [sp], -fp
     b90:	01010101 	tsteq	r1, r1, lsl #2
     b94:	01000000 	mrseq	r0, (UNDEF: 0)
     b98:	2e010000 	cdpcs	0, 0, cr0, cr1, cr0, {0}
     b9c:	2e2e2f2e 	cdpcs	15, 2, cr2, cr14, cr14, {1}
     ba0:	6172742f 	cmnvs	r2, pc, lsr #8
     ba4:	6c6f706d 	stclvs	0, cr7, [pc], #-436	; 9f8 <pthread_mutex_unlock@plt-0xff38>
     ba8:	5f656e69 	svcpl	0x00656e69
     bac:	0062696c 	rsbeq	r6, r2, ip, ror #18
     bb0:	6d6f682f 	stclvs	8, cr6, [pc, #-188]!	; afc <pthread_mutex_unlock@plt-0xfe34>
     bb4:	727a2f65 	rsbsvc	r2, sl, #404	; 0x194
     bb8:	3135307a 	teqcc	r5, sl, ror r0
     bbc:	74732f37 	ldrbtvc	r2, [r3], #-3895	; 0xfffff0c9
     bc0:	2f796475 	svccs	0x00796475
     bc4:	69616863 	stmdbvs	r1!, {r0, r1, r5, r6, fp, sp, lr}^
     bc8:	74615f6e 	strbtvc	r5, [r1], #-3950	; 0xfffff092
     bcc:	74736574 	ldrbtvc	r6, [r3], #-1396	; 0xfffffa8c
     bd0:	6f697461 	svcvs	0x00697461
     bd4:	52412f6e 	subpl	r2, r1, #440	; 0x1b8
     bd8:	727a2d49 	rsbsvc	r2, sl, #4672	; 0x1240
     bdc:	63672f7a 	cmnvs	r7, #488	; 0x1e8
     be0:	696c2d63 	stmdbvs	ip!, {r0, r1, r5, r6, r8, sl, fp, sp}^
     be4:	6f72616e 	svcvs	0x0072616e
     be8:	322e362d 	eorcc	r3, lr, #47185920	; 0x2d00000
     bec:	322d312e 	eorcc	r3, sp, #-2147483637	; 0x8000000b
     bf0:	2e363130 	mrccs	1, 1, r3, cr6, cr0, {1}
     bf4:	782d3131 	stmdavc	sp!, {r0, r4, r5, r8, ip, sp}
     bf8:	365f3638 			; <UNDEFINED> instruction: 0x365f3638
     bfc:	72615f34 	rsbvc	r5, r1, #52, 30	; 0xd0
     c00:	696c2d6d 	stmdbvs	ip!, {r0, r2, r3, r5, r6, r8, sl, fp, sp}^
     c04:	2d78756e 	cfldr64cs	mvdx7, [r8, #-440]!	; 0xfffffe48
     c08:	65756e67 	ldrbvs	r6, [r5, #-3687]!	; 0xfffff199
     c0c:	68696261 	stmdavs	r9!, {r0, r5, r6, r9, sp, lr}^
     c10:	696c2f66 	stmdbvs	ip!, {r1, r2, r5, r6, r8, r9, sl, fp, sp}^
     c14:	63672f62 	cmnvs	r7, #392	; 0x188
     c18:	72612f63 	rsbvc	r2, r1, #396	; 0x18c
     c1c:	696c2d6d 	stmdbvs	ip!, {r0, r2, r3, r5, r6, r8, sl, fp, sp}^
     c20:	2d78756e 	cfldr64cs	mvdx7, [r8, #-440]!	; 0xfffffe48
     c24:	65756e67 	ldrbvs	r6, [r5, #-3687]!	; 0xfffff199
     c28:	68696261 	stmdavs	r9!, {r0, r5, r6, r9, sp, lr}^
     c2c:	2e362f66 	cdpcs	15, 3, cr2, cr6, cr6, {3}
     c30:	2f312e32 	svccs	0x00312e32
     c34:	6c636e69 	stclvs	14, cr6, [r3], #-420	; 0xfffffe5c
     c38:	00656475 	rsbeq	r6, r5, r5, ror r4
     c3c:	6d6f682f 	stclvs	8, cr6, [pc, #-188]!	; b88 <pthread_mutex_unlock@plt-0xfda8>
     c40:	727a2f65 	rsbsvc	r2, sl, #404	; 0x194
     c44:	3135307a 	teqcc	r5, sl, ror r0
     c48:	74732f37 	ldrbtvc	r2, [r3], #-3895	; 0xfffff0c9
     c4c:	2f796475 	svccs	0x00796475
     c50:	69616863 	stmdbvs	r1!, {r0, r1, r5, r6, fp, sp, lr}^
     c54:	74615f6e 	strbtvc	r5, [r1], #-3950	; 0xfffff092
     c58:	74736574 	ldrbtvc	r6, [r3], #-1396	; 0xfffffa8c
     c5c:	6f697461 	svcvs	0x00697461
     c60:	52412f6e 	subpl	r2, r1, #440	; 0x1b8
     c64:	727a2d49 	rsbsvc	r2, sl, #4672	; 0x1240
     c68:	63672f7a 	cmnvs	r7, #488	; 0x1e8
     c6c:	696c2d63 	stmdbvs	ip!, {r0, r1, r5, r6, r8, sl, fp, sp}^
     c70:	6f72616e 	svcvs	0x0072616e
     c74:	322e362d 	eorcc	r3, lr, #47185920	; 0x2d00000
     c78:	322d312e 	eorcc	r3, sp, #-2147483637	; 0x8000000b
     c7c:	2e363130 	mrccs	1, 1, r3, cr6, cr0, {1}
     c80:	782d3131 	stmdavc	sp!, {r0, r4, r5, r8, ip, sp}
     c84:	365f3638 			; <UNDEFINED> instruction: 0x365f3638
     c88:	72615f34 	rsbvc	r5, r1, #52, 30	; 0xd0
     c8c:	696c2d6d 	stmdbvs	ip!, {r0, r2, r3, r5, r6, r8, sl, fp, sp}^
     c90:	2d78756e 	cfldr64cs	mvdx7, [r8, #-440]!	; 0xfffffe48
     c94:	65756e67 	ldrbvs	r6, [r5, #-3687]!	; 0xfffff199
     c98:	68696261 	stmdavs	r9!, {r0, r5, r6, r9, sp, lr}^
     c9c:	72612f66 	rsbvc	r2, r1, #408	; 0x198
     ca0:	696c2d6d 	stmdbvs	ip!, {r0, r2, r3, r5, r6, r8, sl, fp, sp}^
     ca4:	2d78756e 	cfldr64cs	mvdx7, [r8, #-440]!	; 0xfffffe48
     ca8:	65756e67 	ldrbvs	r6, [r5, #-3687]!	; 0xfffff199
     cac:	68696261 	stmdavs	r9!, {r0, r5, r6, r9, sp, lr}^
     cb0:	696c2f66 	stmdbvs	ip!, {r1, r2, r5, r6, r8, r9, sl, fp, sp}^
     cb4:	752f6362 	strvc	r6, [pc, #-866]!	; 95a <pthread_mutex_unlock@plt-0xffd6>
     cb8:	692f7273 	stmdbvs	pc!, {r0, r1, r4, r5, r6, r9, ip, sp, lr}	; <UNPREDICTABLE>
     cbc:	756c636e 	strbvc	r6, [ip, #-878]!	; 0xfffffc92
     cc0:	622f6564 	eorvs	r6, pc, #100, 10	; 0x19000000
     cc4:	00737469 	rsbseq	r7, r3, r9, ror #8
     cc8:	6d6f682f 	stclvs	8, cr6, [pc, #-188]!	; c14 <pthread_mutex_unlock@plt-0xfd1c>
     ccc:	727a2f65 	rsbsvc	r2, sl, #404	; 0x194
     cd0:	3135307a 	teqcc	r5, sl, ror r0
     cd4:	74732f37 	ldrbtvc	r2, [r3], #-3895	; 0xfffff0c9
     cd8:	2f796475 	svccs	0x00796475
     cdc:	69616863 	stmdbvs	r1!, {r0, r1, r5, r6, fp, sp, lr}^
     ce0:	74615f6e 	strbtvc	r5, [r1], #-3950	; 0xfffff092
     ce4:	74736574 	ldrbtvc	r6, [r3], #-1396	; 0xfffffa8c
     ce8:	6f697461 	svcvs	0x00697461
     cec:	52412f6e 	subpl	r2, r1, #440	; 0x1b8
     cf0:	727a2d49 	rsbsvc	r2, sl, #4672	; 0x1240
     cf4:	63672f7a 	cmnvs	r7, #488	; 0x1e8
     cf8:	696c2d63 	stmdbvs	ip!, {r0, r1, r5, r6, r8, sl, fp, sp}^
     cfc:	6f72616e 	svcvs	0x0072616e
     d00:	322e362d 	eorcc	r3, lr, #47185920	; 0x2d00000
     d04:	322d312e 	eorcc	r3, sp, #-2147483637	; 0x8000000b
     d08:	2e363130 	mrccs	1, 1, r3, cr6, cr0, {1}
     d0c:	782d3131 	stmdavc	sp!, {r0, r4, r5, r8, ip, sp}
     d10:	365f3638 			; <UNDEFINED> instruction: 0x365f3638
     d14:	72615f34 	rsbvc	r5, r1, #52, 30	; 0xd0
     d18:	696c2d6d 	stmdbvs	ip!, {r0, r2, r3, r5, r6, r8, sl, fp, sp}^
     d1c:	2d78756e 	cfldr64cs	mvdx7, [r8, #-440]!	; 0xfffffe48
     d20:	65756e67 	ldrbvs	r6, [r5, #-3687]!	; 0xfffff199
     d24:	68696261 	stmdavs	r9!, {r0, r5, r6, r9, sp, lr}^
     d28:	72612f66 	rsbvc	r2, r1, #408	; 0x198
     d2c:	696c2d6d 	stmdbvs	ip!, {r0, r2, r3, r5, r6, r8, sl, fp, sp}^
     d30:	2d78756e 	cfldr64cs	mvdx7, [r8, #-440]!	; 0xfffffe48
     d34:	65756e67 	ldrbvs	r6, [r5, #-3687]!	; 0xfffff199
     d38:	68696261 	stmdavs	r9!, {r0, r5, r6, r9, sp, lr}^
     d3c:	696c2f66 	stmdbvs	ip!, {r1, r2, r5, r6, r8, r9, sl, fp, sp}^
     d40:	752f6362 	strvc	r6, [pc, #-866]!	; 9e6 <pthread_mutex_unlock@plt-0xff4a>
     d44:	692f7273 	stmdbvs	pc!, {r0, r1, r4, r5, r6, r9, ip, sp, lr}	; <UNPREDICTABLE>
     d48:	756c636e 	strbvc	r6, [ip, #-878]!	; 0xfffffc92
     d4c:	00006564 	andeq	r6, r0, r4, ror #10
     d50:	5f746369 	svcpl	0x00746369
     d54:	63656863 	cmnvs	r5, #6488064	; 0x630000
     d58:	676e696b 	strbvs	r6, [lr, -fp, ror #18]!
     d5c:	0100632e 	tsteq	r0, lr, lsr #6
     d60:	74730000 	ldrbtvc	r0, [r3], #-0
     d64:	66656464 	strbtvs	r6, [r5], -r4, ror #8
     d68:	0200682e 	andeq	r6, r0, #3014656	; 0x2e0000
     d6c:	79740000 	ldmdbvc	r4!, {}^	; <UNPREDICTABLE>
     d70:	2e736570 	mrccs	5, 3, r6, cr3, cr0, {3}
     d74:	00030068 	andeq	r0, r3, r8, rrx
     d78:	62696c00 	rsbvs	r6, r9, #0, 24
     d7c:	682e6f69 	stmdavs	lr!, {r0, r3, r5, r6, r8, r9, sl, fp, sp, lr}
     d80:	00000400 	andeq	r0, r0, r0, lsl #8
     d84:	69647473 	stmdbvs	r4!, {r0, r1, r4, r5, r6, sl, ip, sp, lr}^
     d88:	00682e6f 	rsbeq	r2, r8, pc, ror #28
     d8c:	73000004 	movwvc	r0, #4
     d90:	655f7379 	ldrbvs	r7, [pc, #-889]	; a1f <pthread_mutex_unlock@plt-0xff11>
     d94:	696c7272 	stmdbvs	ip!, {r1, r4, r5, r6, r9, ip, sp, lr}^
     d98:	682e7473 	stmdavs	lr!, {r0, r1, r4, r5, r6, sl, ip, sp, lr}
     d9c:	00000300 	andeq	r0, r0, r0, lsl #6
     da0:	69647473 	stmdbvs	r4!, {r0, r1, r4, r5, r6, sl, ip, sp, lr}^
     da4:	682e746e 	stmdavs	lr!, {r1, r2, r3, r5, r6, sl, ip, sp, lr}
     da8:	00000400 	andeq	r0, r0, r0, lsl #8
     dac:	02050000 	andeq	r0, r5, #0
     db0:	00043cc0 	andeq	r3, r4, r0, asr #25
     db4:	91011f03 	tstls	r1, r3, lsl #30
     db8:	2108bb08 	tstcs	r8, r8, lsl #22
     dbc:	2231f3f3 	eorscs	pc, r1, #-872415229	; 0xcc000003
     dc0:	e6085968 	str	r5, [r8], -r8, ror #18
     dc4:	2b02e530 	blcs	ba28c <ringBuffer+0x625b4>
     dc8:	4b5b2213 	blmi	16c961c <ringBuffer+0x1671944>
     dcc:	4c69d708 	stclmi	7, cr13, [r9], #-32	; 0xffffffe0
     dd0:	6921bbbb 	stmdbvs	r1!, {r0, r1, r3, r4, r5, r7, r8, r9, fp, ip, sp, pc}
     dd4:	03212f3e 			; <UNDEFINED> instruction: 0x03212f3e
     dd8:	5968660d 	stmdbpl	r8!, {r0, r2, r3, r9, sl, sp, lr}^
     ddc:	3d405c5b 	stclcc	12, cr5, [r0, #-364]	; 0xfffffe94
     de0:	005c312f 	subseq	r3, ip, pc, lsr #2
     de4:	06010402 	streq	r0, [r1], -r2, lsl #8
     de8:	e54e064a 	strb	r0, [lr, #-1610]	; 0xfffff9b6
     dec:	0c03355e 	cfstr32eq	mvfx3, [r3], {94}	; 0x5e
     df0:	838359d6 	orrhi	r5, r3, #3506176	; 0x358000
     df4:	27028483 	strcs	r8, [r2, -r3, lsl #9]
     df8:	2fc92f13 	svccs	0x00c92f13
     dfc:	2fc92fc9 	svccs	0x00c92fc9
     e00:	040200c9 	streq	r0, [r2], #-201	; 0xffffff37
     e04:	003c0601 	eorseq	r0, ip, r1, lsl #12
     e08:	66030402 	strvs	r0, [r3], -r2, lsl #8
     e0c:	04040200 	streq	r0, [r4], #-512	; 0xfffffe00
     e10:	0402002e 	streq	r0, [r2], #-46	; 0xffffffd2
     e14:	4b062006 	blmi	188e34 <ringBuffer+0x13115c>
     e18:	02040200 	andeq	r0, r4, #0, 4
     e1c:	02006606 	andeq	r6, r0, #6291456	; 0x600000
     e20:	003c0304 	eorseq	r0, ip, r4, lsl #6
     e24:	2e040402 	cdpcs	4, 0, cr0, cr4, cr2, {0}
     e28:	06040200 	streq	r0, [r4], -r0, lsl #4
     e2c:	834b0620 	movthi	r0, #46624	; 0xb620
     e30:	04020083 	streq	r0, [r2], #-131	; 0xffffff7d
     e34:	00660601 	rsbeq	r0, r6, r1, lsl #12
     e38:	4a030402 	bmi	c1e48 <ringBuffer+0x6a170>
     e3c:	04040200 	streq	r0, [r4], #-512	; 0xfffffe00
     e40:	0402002e 	streq	r0, [r2], #-46	; 0xffffffd2
     e44:	4b062006 	blmi	188e64 <ringBuffer+0x13118c>
     e48:	02040200 	andeq	r0, r4, #0, 4
     e4c:	02003c06 	andeq	r3, r0, #1536	; 0x600
     e50:	004a0304 	subeq	r0, sl, r4, lsl #6
     e54:	2e040402 	cdpcs	4, 0, cr0, cr4, cr2, {0}
     e58:	06040200 	streq	r0, [r4], -r0, lsl #4
     e5c:	2f4b0620 	svccs	0x004b0620
     e60:	59846a22 	stmibpl	r4, {r1, r5, r9, fp, sp, lr}
     e64:	42795c5b 	rsbsmi	r5, r9, #23296	; 0x5b00
     e68:	3d2f2f4e 	stccc	15, cr2, [pc, #-312]!	; d38 <pthread_mutex_unlock@plt-0xfbf8>
     e6c:	6ee55c2f 	cdpvs	12, 14, cr5, cr5, cr15, {1}
     e70:	2f740c03 	svccs	0x00740c03
     e74:	5c3f2f2f 	ldcpl	15, cr2, [pc], #-188	; dc0 <pthread_mutex_unlock@plt-0xfb70>
     e78:	01040200 	mrseq	r0, R12_usr
     e7c:	4e064a06 	vmlami.f32	s8, s12, s12
     e80:	62035de5 	andvs	r5, r3, #14656	; 0x3940
     e84:	2e1e032e 	cdpcs	3, 1, cr0, cr14, cr14, {1}
     e88:	5984f521 	stmibpl	r4, {r0, r5, r8, sl, ip, sp, lr, pc}
     e8c:	40785c5b 	rsbsmi	r5, r8, fp, asr ip
     e90:	01040200 	mrseq	r0, R12_usr
     e94:	40064a06 	andmi	r4, r6, r6, lsl #20
     e98:	2f3d2f2f 	svccs	0x003d2f2f
     e9c:	7303e55c 	movwvc	lr, #13660	; 0x355c
     ea0:	20150358 	andscs	r0, r5, r8, asr r3
     ea4:	03826b03 	orreq	r6, r2, #3072	; 0xc00
     ea8:	2f2f201f 	svccs	0x002f201f
     eac:	005c3f2f 	subseq	r3, ip, pc, lsr #30
     eb0:	06010402 	streq	r0, [r1], -r2, lsl #8
     eb4:	e54e064a 	strb	r0, [lr, #-1610]	; 0xfffff9b6
     eb8:	2e64035d 	mcrcs	3, 3, r0, cr4, cr13, {2}
     ebc:	212e1c03 			; <UNDEFINED> instruction: 0x212e1c03
     ec0:	5b5968e8 	blpl	165b268 <ringBuffer+0x1603590>
     ec4:	2f2f405c 	svccs	0x002f405c
     ec8:	02005c31 	andeq	r5, r0, #12544	; 0x3100
     ecc:	4a060104 	bmi	1812e4 <ringBuffer+0x12960c>
     ed0:	03040200 	movweq	r0, #16896	; 0x4200
     ed4:	4e4b064a 	cdpmi	6, 4, cr0, cr11, cr10, {2}
     ed8:	cc3660e5 	ldcgt	0, cr6, [r6], #-916	; 0xfffffc6c
     edc:	5c5b5969 	mrrcpl	9, 6, r5, fp, cr9	; <UNPREDICTABLE>
     ee0:	5d322f40 	ldcpl	15, cr2, [r2, #-256]!	; 0xffffff00
     ee4:	01040200 	mrseq	r0, R12_usr
     ee8:	4b064a06 	blmi	193708 <ringBuffer+0x13ba30>
     eec:	005de532 	subseq	lr, sp, r2, lsr r5
     ef0:	06010402 	streq	r0, [r1], -r2, lsl #8
     ef4:	324b064a 	subcc	r0, fp, #77594624	; 0x4a00000
     ef8:	e72f5de5 	str	r5, [pc, -r5, ror #27]!
     efc:	5c5b5968 	mrrcpl	9, 6, r5, fp, cr8	; <UNPREDICTABLE>
     f00:	5d322f40 	ldcpl	15, cr2, [r2, #-256]!	; 0xffffff00
     f04:	01040200 	mrseq	r0, R12_usr
     f08:	4b064a06 	blmi	193728 <ringBuffer+0x13ba50>
     f0c:	0903e532 	stmdbeq	r3, {r1, r4, r5, r8, sl, sp, lr, pc}
     f10:	04020058 	streq	r0, [r2], #-88	; 0xffffffa8
     f14:	064a0601 	strbeq	r0, [sl], -r1, lsl #12
     f18:	5de5324b 	sfmpl	f3, 2, [r5, #300]!	; 0x12c
     f1c:	01040200 	mrseq	r0, R12_usr
     f20:	4b064a06 	blmi	193740 <ringBuffer+0x13ba68>
     f24:	2f5fe532 	svccs	0x005fe532
     f28:	59691508 	stmdbpl	r9!, {r3, r8, sl, ip}^
     f2c:	2f405c5b 	svccs	0x00405c5b
     f30:	02005d32 	andeq	r5, r0, #3200	; 0xc80
     f34:	4a060104 	bmi	18134c <ringBuffer+0x129674>
     f38:	34434c06 	strbcc	r4, [r3], #-3078	; 0xfffff3fa
     f3c:	da2f5ce5 	ble	bd82d8 <ringBuffer+0xb80600>
     f40:	2f407785 	svccs	0x00407785
     f44:	5b302f3d 	blpl	c0cc40 <ringBuffer+0xbb4f68>
     f48:	02005ce5 	andeq	r5, r0, #58624	; 0xe500
     f4c:	4a060104 	bmi	181364 <ringBuffer+0x12968c>
     f50:	2f4b4d06 	svccs	0x004b4d06
     f54:	0b03e532 	bleq	fa424 <ringBuffer+0xa274c>
     f58:	04020058 	streq	r0, [r2], #-88	; 0xffffffa8
     f5c:	064a0601 	strbeq	r0, [sl], -r1, lsl #12
     f60:	322f4b4d 	eorcc	r4, pc, #78848	; 0x13400
     f64:	667003e5 	ldrbtvs	r0, [r0], -r5, ror #7
     f68:	262e1403 	strtcs	r1, [lr], -r3, lsl #8
     f6c:	5b5984f4 	blpl	1662344 <ringBuffer+0x160a66c>
     f70:	3d2f775b 	stccc	7, cr7, [pc, #-364]!	; e0c <pthread_mutex_unlock@plt-0xfb24>
     f74:	e55d3e2f 	ldrb	r3, [sp, #-3631]	; 0xfffff1d1
     f78:	84cb305e 	strbhi	r3, [fp], #94	; 0x5e
     f7c:	3f5b5b59 	svccc	0x005b5b59
     f80:	3e2f2f2f 	cdpcc	15, 2, cr2, cr15, cr15, {1}
     f84:	2f5de55e 	svccs	0x005de55e
     f88:	68214edb 	stmdavs	r1!, {r0, r1, r3, r4, r6, r7, r9, sl, fp, lr}
     f8c:	4d4f5a2f 	vstrmi	s11, [pc, #-188]	; ed8 <pthread_mutex_unlock@plt-0xfa58>
     f90:	08025c59 	stmdaeq	r2, {r0, r3, r4, r6, sl, fp, ip, lr}
     f94:	cd010100 	stfgts	f0, [r1, #-0]
     f98:	02000002 	andeq	r0, r0, #2
     f9c:	00003b00 	andeq	r3, r0, r0, lsl #22
     fa0:	fb010200 	blx	417aa <blake2s_compress+0x8f6>
     fa4:	01000d0e 	tsteq	r0, lr, lsl #26
     fa8:	00010101 	andeq	r0, r1, r1, lsl #2
     fac:	00010000 	andeq	r0, r1, r0
     fb0:	2e2e0100 	sufcse	f0, f6, f0
     fb4:	2f2e2e2f 	svccs	0x002e2e2f
     fb8:	6d617274 	sfmvs	f7, 2, [r1, #-464]!	; 0xfffffe30
     fbc:	696c6f70 	stmdbvs	ip!, {r4, r5, r6, r8, r9, sl, fp, sp, lr}^
     fc0:	6c5f656e 	cfldr64vs	mvdx6, [pc], {110}	; 0x6e
     fc4:	00006269 	andeq	r6, r0, r9, ror #4
     fc8:	6d617274 	sfmvs	f7, 2, [r1, #-464]!	; 0xfffffe30
     fcc:	696c6f70 	stmdbvs	ip!, {r4, r5, r6, r8, r9, sl, fp, sp, lr}^
     fd0:	665f656e 	ldrbvs	r6, [pc], -lr, ror #10
     fd4:	00532e77 	subseq	r2, r3, r7, ror lr
     fd8:	00000001 	andeq	r0, r0, r1
     fdc:	38020500 	stmdacc	r2, {r8, sl}
     fe0:	03000571 	movweq	r0, #1393	; 0x571
     fe4:	2f2f0121 	svccs	0x002f0121
     fe8:	2f2f2f2f 	svccs	0x002f2f2f
     fec:	2f2f2f2f 	svccs	0x002f2f2f
     ff0:	2f2f2f2f 	svccs	0x002f2f2f
     ff4:	2f2f2f2f 	svccs	0x002f2f2f
     ff8:	2f2f2f2f 	svccs	0x002f2f2f
     ffc:	2f322f2f 	svccs	0x00322f2f
    1000:	2f2f2f2f 	svccs	0x002f2f2f
    1004:	2f2f2f2f 	svccs	0x002f2f2f
    1008:	2f2f2f2f 	svccs	0x002f2f2f
    100c:	2f2f2f2f 	svccs	0x002f2f2f
    1010:	2f2f2f2f 	svccs	0x002f2f2f
    1014:	312f2f2f 			; <UNDEFINED> instruction: 0x312f2f2f
    1018:	2f2f2f2f 	svccs	0x002f2f2f
    101c:	2f2f2f2f 	svccs	0x002f2f2f
    1020:	2f2f2f2f 	svccs	0x002f2f2f
    1024:	2f2f2f2f 	svccs	0x002f2f2f
    1028:	2f2f2f2f 	svccs	0x002f2f2f
    102c:	302f2f2f 	eorcc	r2, pc, pc, lsr #30
    1030:	332f312f 			; <UNDEFINED> instruction: 0x332f312f
    1034:	2f322f2f 	svccs	0x00322f2f
    1038:	2f2f2f2f 	svccs	0x002f2f2f
    103c:	2f2f2f2f 	svccs	0x002f2f2f
    1040:	2f2f2f2f 	svccs	0x002f2f2f
    1044:	2f2f2f2f 	svccs	0x002f2f2f
    1048:	2f2f2f2f 	svccs	0x002f2f2f
    104c:	312f2f2f 			; <UNDEFINED> instruction: 0x312f2f2f
    1050:	31313131 	teqcc	r1, r1, lsr r1
    1054:	2f343131 	svccs	0x00343131
    1058:	2f2f2f2f 	svccs	0x002f2f2f
    105c:	2f2f302f 	svccs	0x002f302f
    1060:	2f302f2f 	svccs	0x00302f2f
    1064:	302f2f2f 	eorcc	r2, pc, pc, lsr #30
    1068:	3130302f 	teqcc	r0, pc, lsr #32
    106c:	2f2f302f 	svccs	0x002f302f
    1070:	302f302f 	eorcc	r3, pc, pc, lsr #32
    1074:	312f332f 			; <UNDEFINED> instruction: 0x312f332f
    1078:	2f2f2f2f 	svccs	0x002f2f2f
    107c:	2f312f2f 	svccs	0x00312f2f
    1080:	302f302f 	eorcc	r3, pc, pc, lsr #32
    1084:	302f302f 	eorcc	r3, pc, pc, lsr #32
    1088:	2f2f2f2f 	svccs	0x002f2f2f
    108c:	352f2f2f 	strcc	r2, [pc, #-3887]!	; 165 <pthread_mutex_unlock@plt-0x107cb>
    1090:	2f2f2f2f 	svccs	0x002f2f2f
    1094:	2f312f2f 	svccs	0x00312f2f
    1098:	302f2f2f 	eorcc	r2, pc, pc, lsr #30
    109c:	2f2f2f2f 	svccs	0x002f2f2f
    10a0:	30302f30 	eorscc	r2, r0, r0, lsr pc
    10a4:	2f302f31 	svccs	0x00302f31
    10a8:	2f302f2f 	svccs	0x00302f2f
    10ac:	2f332f30 	svccs	0x00332f30
    10b0:	2f2f2f31 	svccs	0x002f2f31
    10b4:	302f2f2f 	eorcc	r2, pc, pc, lsr #30
    10b8:	2f2f2f2f 	svccs	0x002f2f2f
    10bc:	352f2f2f 	strcc	r2, [pc, #-3887]!	; 195 <pthread_mutex_unlock@plt-0x1079b>
    10c0:	2f2f2f2f 	svccs	0x002f2f2f
    10c4:	2f2f2f31 	svccs	0x002f2f31
    10c8:	2f2f2f2f 	svccs	0x002f2f2f
    10cc:	2f31312f 	svccs	0x0031312f
    10d0:	2f2f2f2f 	svccs	0x002f2f2f
    10d4:	312f2f2f 			; <UNDEFINED> instruction: 0x312f2f2f
    10d8:	2f2f2f2f 	svccs	0x002f2f2f
    10dc:	32313231 	eorscc	r3, r1, #268435459	; 0x10000003
    10e0:	2f2f2f2f 	svccs	0x002f2f2f
    10e4:	2f2f2f32 	svccs	0x002f2f32
    10e8:	2f35312f 	svccs	0x0035312f
    10ec:	2f2f2f2f 	svccs	0x002f2f2f
    10f0:	2f2f322f 	svccs	0x002f322f
    10f4:	2f302f2f 	svccs	0x00302f2f
    10f8:	302f2f2f 	eorcc	r2, pc, pc, lsr #30
    10fc:	3130302f 	teqcc	r0, pc, lsr #32
    1100:	2f2f302f 	svccs	0x002f302f
    1104:	302f302f 	eorcc	r3, pc, pc, lsr #32
    1108:	312f322f 			; <UNDEFINED> instruction: 0x312f322f
    110c:	2f2f312f 	svccs	0x002f312f
    1110:	2f2f3233 	svccs	0x002f3233
    1114:	342f2f2f 	strtcc	r2, [pc], #-3887	; 111c <pthread_mutex_unlock@plt-0xf814>
    1118:	302f302f 	eorcc	r3, pc, pc, lsr #32
    111c:	2f352f30 	svccs	0x00352f30
    1120:	302f312f 	eorcc	r3, pc, pc, lsr #2
    1124:	302f302f 	eorcc	r3, pc, pc, lsr #32
    1128:	2f2f2f2f 	svccs	0x002f2f2f
    112c:	342f2f2f 	strtcc	r2, [pc], #-3887	; 1134 <pthread_mutex_unlock@plt-0xf7fc>
    1130:	2f2f2f2f 	svccs	0x002f2f2f
    1134:	2f2f2f2f 	svccs	0x002f2f2f
    1138:	2f2f2f2f 	svccs	0x002f2f2f
    113c:	2f2f2f2f 	svccs	0x002f2f2f
    1140:	2f2f2f2f 	svccs	0x002f2f2f
    1144:	2f2f3630 	svccs	0x002f3630
    1148:	2f2f2f2f 	svccs	0x002f2f2f
    114c:	2f2f2f32 	svccs	0x002f2f32
    1150:	2f2f302f 	svccs	0x002f302f
    1154:	2f302f2f 	svccs	0x00302f2f
    1158:	2f313030 	svccs	0x00313030
    115c:	2f2f2f30 	svccs	0x002f2f30
    1160:	2f302f30 	svccs	0x00302f30
    1164:	2f322f32 	svccs	0x00322f32
    1168:	2f2f2f2f 	svccs	0x002f2f2f
    116c:	2f2f302f 	svccs	0x002f302f
    1170:	2f2f2f2f 	svccs	0x002f2f2f
    1174:	2f2f312f 	svccs	0x002f312f
    1178:	2f2f2f2f 	svccs	0x002f2f2f
    117c:	2f2f2f2f 	svccs	0x002f2f2f
    1180:	2f2f2f2f 	svccs	0x002f2f2f
    1184:	2f2f2f2f 	svccs	0x002f2f2f
    1188:	35302f2f 	ldrcc	r2, [r0, #-3887]!	; 0xfffff0d1
    118c:	2f2f2f2f 	svccs	0x002f2f2f
    1190:	2f2f2f30 	svccs	0x002f2f30
    1194:	302f2f2f 	eorcc	r2, pc, pc, lsr #30
    1198:	2f2f2f2f 	svccs	0x002f2f2f
    119c:	2f31312f 	svccs	0x0031312f
    11a0:	2f2f2f2f 	svccs	0x002f2f2f
    11a4:	2f302f2f 	svccs	0x00302f2f
    11a8:	2f2f2f2f 	svccs	0x002f2f2f
    11ac:	2f2f312f 	svccs	0x002f312f
    11b0:	2f2f2f2f 	svccs	0x002f2f2f
    11b4:	2f2f2f2f 	svccs	0x002f2f2f
    11b8:	2f2f2f2f 	svccs	0x002f2f2f
    11bc:	2f2f2f2f 	svccs	0x002f2f2f
    11c0:	2f2f2f2f 	svccs	0x002f2f2f
    11c4:	31352f2f 	teqcc	r5, pc, lsr #30
    11c8:	2f2f2f2f 	svccs	0x002f2f2f
    11cc:	2f2f2f30 	svccs	0x002f2f30
    11d0:	302f2f2f 	eorcc	r2, pc, pc, lsr #30
    11d4:	2f2f2f2f 	svccs	0x002f2f2f
    11d8:	2f31322f 	svccs	0x0031322f
    11dc:	2f2f2f2f 	svccs	0x002f2f2f
    11e0:	2f302f2f 	svccs	0x00302f2f
    11e4:	2f2f2f2f 	svccs	0x002f2f2f
    11e8:	2f312f2f 	svccs	0x00312f2f
    11ec:	2f2f2f2f 	svccs	0x002f2f2f
    11f0:	2f2f2f2f 	svccs	0x002f2f2f
    11f4:	2f2f2f2f 	svccs	0x002f2f2f
    11f8:	2f2f2f2f 	svccs	0x002f2f2f
    11fc:	2f2f2f2f 	svccs	0x002f2f2f
    1200:	2f2f2f2f 	svccs	0x002f2f2f
    1204:	2f2f2f36 	svccs	0x002f2f36
    1208:	2f2f2f2f 	svccs	0x002f2f2f
    120c:	2f2f2f31 	svccs	0x002f2f31
    1210:	2f2f302f 	svccs	0x002f302f
    1214:	2f302f2f 	svccs	0x00302f2f
    1218:	31303030 	teqcc	r0, r0, lsr r0
    121c:	2f2f3030 	svccs	0x002f3030
    1220:	302f2f2f 	eorcc	r2, pc, pc, lsr #30
    1224:	2f2f2f2f 	svccs	0x002f2f2f
    1228:	2f2f2f2f 	svccs	0x002f2f2f
    122c:	2f312f32 	svccs	0x00312f32
    1230:	312f322f 			; <UNDEFINED> instruction: 0x312f322f
    1234:	2f2f2f2f 	svccs	0x002f2f2f
    1238:	312f2f2f 			; <UNDEFINED> instruction: 0x312f2f2f
    123c:	2f2f2f2f 	svccs	0x002f2f2f
    1240:	302f2f2f 	eorcc	r2, pc, pc, lsr #30
    1244:	2f312f31 	svccs	0x00312f31
    1248:	02799e03 	rsbseq	r9, r9, #3, 28	; 0x30
    124c:	030101d0 	movweq	r0, #4560	; 0x11d0
    1250:	032e0196 			; <UNDEFINED> instruction: 0x032e0196
    1254:	03322e2b 	teqeq	r2, #688	; 0x2b0
    1258:	032e01b8 			; <UNDEFINED> instruction: 0x032e01b8
    125c:	032e0284 			; <UNDEFINED> instruction: 0x032e0284
    1260:	022e018e 	eoreq	r0, lr, #-2147483613	; 0x80000023
    1264:	01010002 	tsteq	r1, r2
    1268:	0000008a 	andeq	r0, r0, sl, lsl #1
    126c:	00380002 	eorseq	r0, r8, r2
    1270:	01020000 	mrseq	r0, (UNDEF: 2)
    1274:	000d0efb 	strdeq	r0, [sp], -fp
    1278:	01010101 	tsteq	r1, r1, lsl #2
    127c:	01000000 	mrseq	r0, (UNDEF: 0)
    1280:	2e010000 	cdpcs	0, 0, cr0, cr1, cr0, {0}
    1284:	2e2e2f2e 	cdpcs	15, 2, cr2, cr14, cr14, {1}
    1288:	6172742f 	cmnvs	r2, pc, lsr #8
    128c:	6c6f706d 	stclvs	0, cr7, [pc], #-436	; 10e0 <pthread_mutex_unlock@plt-0xf850>
    1290:	5f656e69 	svcpl	0x00656e69
    1294:	0062696c 	rsbeq	r6, r2, ip, ror #18
    1298:	61727400 	cmnvs	r2, r0, lsl #8
    129c:	6c6f706d 	stclvs	0, cr7, [pc], #-436	; 10f0 <pthread_mutex_unlock@plt-0xf840>
    12a0:	2e656e69 	cdpcs	14, 6, cr6, cr5, cr9, {3}
    12a4:	00010053 	andeq	r0, r1, r3, asr r0
    12a8:	05000000 	streq	r0, [r0, #-0]
    12ac:	04633002 	strbteq	r3, [r3], #-2
    12b0:	010d0300 	mrseq	r0, SP_mon
    12b4:	2f2f2f2f 	svccs	0x002f2f2f
    12b8:	2f2f2f2f 	svccs	0x002f2f2f
    12bc:	2f2f2f2f 	svccs	0x002f2f2f
    12c0:	2f2f2f2f 	svccs	0x002f2f2f
    12c4:	2f2f2f2f 	svccs	0x002f2f2f
    12c8:	2f2f2f2f 	svccs	0x002f2f2f
    12cc:	2f2f2f2f 	svccs	0x002f2f2f
    12d0:	2f2f2f2f 	svccs	0x002f2f2f
    12d4:	2f2f2f2f 	svccs	0x002f2f2f
    12d8:	2f2f322f 	svccs	0x002f322f
    12dc:	2f2f2f2f 	svccs	0x002f2f2f
    12e0:	2f2f2f2f 	svccs	0x002f2f2f
    12e4:	2f2f322f 	svccs	0x002f322f
    12e8:	2f2f322f 	svccs	0x002f322f
    12ec:	2f2f322f 	svccs	0x002f322f
    12f0:	0002022f 	andeq	r0, r2, pc, lsr #4
    12f4:	037a0101 	cmneq	sl, #1073741824	; 0x40000000
    12f8:	00020000 	andeq	r0, r2, r0
    12fc:	000002ab 	andeq	r0, r0, fp, lsr #5
    1300:	0efb0102 	cdpeq	1, 15, cr0, cr11, cr2, {0}
    1304:	0101000d 	tsteq	r1, sp
    1308:	00000101 	andeq	r0, r0, r1, lsl #2
    130c:	00000100 	andeq	r0, r0, r0, lsl #2
    1310:	2f2e2e01 	svccs	0x002e2e01
    1314:	742f2e2e 	strtvc	r2, [pc], #-3630	; 131c <pthread_mutex_unlock@plt-0xf614>
    1318:	706d6172 	rsbvc	r6, sp, r2, ror r1
    131c:	6e696c6f 	cdpvs	12, 6, cr6, cr9, cr15, {3}
    1320:	696c5f65 	stmdbvs	ip!, {r0, r2, r5, r6, r8, r9, sl, fp, ip, lr}^
    1324:	682f0062 	stmdavs	pc!, {r1, r5, r6}	; <UNPREDICTABLE>
    1328:	2f656d6f 	svccs	0x00656d6f
    132c:	307a727a 	rsbscc	r7, sl, sl, ror r2
    1330:	2f373135 	svccs	0x00373135
    1334:	64757473 	ldrbtvs	r7, [r5], #-1139	; 0xfffffb8d
    1338:	68632f79 	stmdavs	r3!, {r0, r3, r4, r5, r6, r8, r9, sl, fp, sp}^
    133c:	5f6e6961 	svcpl	0x006e6961
    1340:	65747461 	ldrbvs	r7, [r4, #-1121]!	; 0xfffffb9f
    1344:	74617473 	strbtvc	r7, [r1], #-1139	; 0xfffffb8d
    1348:	2f6e6f69 	svccs	0x006e6f69
    134c:	2d495241 	sfmcs	f5, 2, [r9, #-260]	; 0xfffffefc
    1350:	2f7a727a 	svccs	0x007a727a
    1354:	2d636367 	stclcs	3, cr6, [r3, #-412]!	; 0xfffffe64
    1358:	616e696c 	cmnvs	lr, ip, ror #18
    135c:	362d6f72 	qsub16cc	r6, sp, r2
    1360:	312e322e 			; <UNDEFINED> instruction: 0x312e322e
    1364:	3130322d 	teqcc	r0, sp, lsr #4
    1368:	31312e36 	teqcc	r1, r6, lsr lr
    136c:	3638782d 	ldrtcc	r7, [r8], -sp, lsr #16
    1370:	5f34365f 	svcpl	0x0034365f
    1374:	2d6d7261 	sfmcs	f7, 2, [sp, #-388]!	; 0xfffffe7c
    1378:	756e696c 	strbvc	r6, [lr, #-2412]!	; 0xfffff694
    137c:	6e672d78 	mcrvs	13, 3, r2, cr7, cr8, {3}
    1380:	62616575 	rsbvs	r6, r1, #490733568	; 0x1d400000
    1384:	2f666869 	svccs	0x00666869
    1388:	2d6d7261 	sfmcs	f7, 2, [sp, #-388]!	; 0xfffffe7c
    138c:	756e696c 	strbvc	r6, [lr, #-2412]!	; 0xfffff694
    1390:	6e672d78 	mcrvs	13, 3, r2, cr7, cr8, {3}
    1394:	62616575 	rsbvs	r6, r1, #490733568	; 0x1d400000
    1398:	2f666869 	svccs	0x00666869
    139c:	6362696c 	cmnvs	r2, #108, 18	; 0x1b0000
    13a0:	7273752f 	rsbsvc	r7, r3, #197132288	; 0xbc00000
    13a4:	636e692f 	cmnvs	lr, #770048	; 0xbc000
    13a8:	6564756c 	strbvs	r7, [r4, #-1388]!	; 0xfffffa94
    13ac:	7469622f 	strbtvc	r6, [r9], #-559	; 0xfffffdd1
    13b0:	682f0073 	stmdavs	pc!, {r0, r1, r4, r5, r6}	; <UNPREDICTABLE>
    13b4:	2f656d6f 	svccs	0x00656d6f
    13b8:	307a727a 	rsbscc	r7, sl, sl, ror r2
    13bc:	2f373135 	svccs	0x00373135
    13c0:	64757473 	ldrbtvs	r7, [r5], #-1139	; 0xfffffb8d
    13c4:	68632f79 	stmdavs	r3!, {r0, r3, r4, r5, r6, r8, r9, sl, fp, sp}^
    13c8:	5f6e6961 	svcpl	0x006e6961
    13cc:	65747461 	ldrbvs	r7, [r4, #-1121]!	; 0xfffffb9f
    13d0:	74617473 	strbtvc	r7, [r1], #-1139	; 0xfffffb8d
    13d4:	2f6e6f69 	svccs	0x006e6f69
    13d8:	2d495241 	sfmcs	f5, 2, [r9, #-260]	; 0xfffffefc
    13dc:	2f7a727a 	svccs	0x007a727a
    13e0:	2d636367 	stclcs	3, cr6, [r3, #-412]!	; 0xfffffe64
    13e4:	616e696c 	cmnvs	lr, ip, ror #18
    13e8:	362d6f72 	qsub16cc	r6, sp, r2
    13ec:	312e322e 			; <UNDEFINED> instruction: 0x312e322e
    13f0:	3130322d 	teqcc	r0, sp, lsr #4
    13f4:	31312e36 	teqcc	r1, r6, lsr lr
    13f8:	3638782d 	ldrtcc	r7, [r8], -sp, lsr #16
    13fc:	5f34365f 	svcpl	0x0034365f
    1400:	2d6d7261 	sfmcs	f7, 2, [sp, #-388]!	; 0xfffffe7c
    1404:	756e696c 	strbvc	r6, [lr, #-2412]!	; 0xfffff694
    1408:	6e672d78 	mcrvs	13, 3, r2, cr7, cr8, {3}
    140c:	62616575 	rsbvs	r6, r1, #490733568	; 0x1d400000
    1410:	2f666869 	svccs	0x00666869
    1414:	2f62696c 	svccs	0x0062696c
    1418:	2f636367 	svccs	0x00636367
    141c:	2d6d7261 	sfmcs	f7, 2, [sp, #-388]!	; 0xfffffe7c
    1420:	756e696c 	strbvc	r6, [lr, #-2412]!	; 0xfffff694
    1424:	6e672d78 	mcrvs	13, 3, r2, cr7, cr8, {3}
    1428:	62616575 	rsbvs	r6, r1, #490733568	; 0x1d400000
    142c:	2f666869 	svccs	0x00666869
    1430:	2e322e36 	mrccs	14, 1, r2, cr2, cr6, {1}
    1434:	6e692f31 	mcrvs	15, 3, r2, cr9, cr1, {1}
    1438:	64756c63 	ldrbtvs	r6, [r5], #-3171	; 0xfffff39d
    143c:	682f0065 	stmdavs	pc!, {r0, r2, r5, r6}	; <UNPREDICTABLE>
    1440:	2f656d6f 	svccs	0x00656d6f
    1444:	307a727a 	rsbscc	r7, sl, sl, ror r2
    1448:	2f373135 	svccs	0x00373135
    144c:	64757473 	ldrbtvs	r7, [r5], #-1139	; 0xfffffb8d
    1450:	68632f79 	stmdavs	r3!, {r0, r3, r4, r5, r6, r8, r9, sl, fp, sp}^
    1454:	5f6e6961 	svcpl	0x006e6961
    1458:	65747461 	ldrbvs	r7, [r4, #-1121]!	; 0xfffffb9f
    145c:	74617473 	strbtvc	r7, [r1], #-1139	; 0xfffffb8d
    1460:	2f6e6f69 	svccs	0x006e6f69
    1464:	2d495241 	sfmcs	f5, 2, [r9, #-260]	; 0xfffffefc
    1468:	2f7a727a 	svccs	0x007a727a
    146c:	2d636367 	stclcs	3, cr6, [r3, #-412]!	; 0xfffffe64
    1470:	616e696c 	cmnvs	lr, ip, ror #18
    1474:	362d6f72 	qsub16cc	r6, sp, r2
    1478:	312e322e 			; <UNDEFINED> instruction: 0x312e322e
    147c:	3130322d 	teqcc	r0, sp, lsr #4
    1480:	31312e36 	teqcc	r1, r6, lsr lr
    1484:	3638782d 	ldrtcc	r7, [r8], -sp, lsr #16
    1488:	5f34365f 	svcpl	0x0034365f
    148c:	2d6d7261 	sfmcs	f7, 2, [sp, #-388]!	; 0xfffffe7c
    1490:	756e696c 	strbvc	r6, [lr, #-2412]!	; 0xfffff694
    1494:	6e672d78 	mcrvs	13, 3, r2, cr7, cr8, {3}
    1498:	62616575 	rsbvs	r6, r1, #490733568	; 0x1d400000
    149c:	2f666869 	svccs	0x00666869
    14a0:	2d6d7261 	sfmcs	f7, 2, [sp, #-388]!	; 0xfffffe7c
    14a4:	756e696c 	strbvc	r6, [lr, #-2412]!	; 0xfffff694
    14a8:	6e672d78 	mcrvs	13, 3, r2, cr7, cr8, {3}
    14ac:	62616575 	rsbvs	r6, r1, #490733568	; 0x1d400000
    14b0:	2f666869 	svccs	0x00666869
    14b4:	6362696c 	cmnvs	r2, #108, 18	; 0x1b0000
    14b8:	7273752f 	rsbsvc	r7, r3, #197132288	; 0xbc00000
    14bc:	636e692f 	cmnvs	lr, #770048	; 0xbc000
    14c0:	6564756c 	strbvs	r7, [r4, #-1388]!	; 0xfffffa94
    14c4:	2f2e2e00 	svccs	0x002e2e00
    14c8:	6f2f2e2e 	svcvs	0x002f2e2e
    14cc:	65657470 	strbvs	r7, [r5, #-1136]!	; 0xfffffb90
    14d0:	696c635f 	stmdbvs	ip!, {r0, r1, r2, r3, r4, r6, r8, r9, sp, lr}^
    14d4:	2d746e65 	ldclcs	14, cr6, [r4, #-404]!	; 0xfffffe6c
    14d8:	7473616d 	ldrbtvc	r6, [r3], #-365	; 0xfffffe93
    14dc:	6f2f7265 	svcvs	0x002f7265
    14e0:	652f7475 	strvs	r7, [pc, #-1141]!	; 1073 <pthread_mutex_unlock@plt-0xf8bd>
    14e4:	726f7078 	rsbvc	r7, pc, #120	; 0x78
    14e8:	6e692f74 	mcrvs	15, 3, r2, cr9, cr4, {3}
    14ec:	64756c63 	ldrbtvs	r6, [r5], #-3171	; 0xfffff39d
    14f0:	74000065 	strvc	r0, [r0], #-101	; 0xffffff9b
    14f4:	72745f61 	rsbsvc	r5, r4, #388	; 0x184
    14f8:	6f706d61 	svcvs	0x00706d61
    14fc:	656e696c 	strbvs	r6, [lr, #-2412]!	; 0xfffff694
    1500:	0100632e 	tsteq	r0, lr, lsr #6
    1504:	79740000 	ldmdbvc	r4!, {}^	; <UNPREDICTABLE>
    1508:	2e736570 	mrccs	5, 3, r6, cr3, cr0, {3}
    150c:	00020068 	andeq	r0, r2, r8, rrx
    1510:	64747300 	ldrbtvs	r7, [r4], #-768	; 0xfffffd00
    1514:	2e666564 	cdpcs	5, 6, cr6, cr6, cr4, {3}
    1518:	00030068 	andeq	r0, r3, r8, rrx
    151c:	696e7500 	stmdbvs	lr!, {r8, sl, ip, sp, lr}^
    1520:	2e647473 	mcrcs	4, 3, r7, cr4, cr3, {3}
    1524:	00040068 	andeq	r0, r4, r8, rrx
    1528:	74656700 	strbtvc	r6, [r5], #-1792	; 0xfffff900
    152c:	2e74706f 	cdpcs	0, 7, cr7, cr4, cr15, {3}
    1530:	00040068 	andeq	r0, r4, r8, rrx
    1534:	67697300 	strbvs	r7, [r9, -r0, lsl #6]!
    1538:	2e6c616e 	powcsez	f6, f4, #0.5
    153c:	00040068 	andeq	r0, r4, r8, rrx
    1540:	64747300 	ldrbtvs	r7, [r4], #-768	; 0xfffffd00
    1544:	682e6f69 	stmdavs	lr!, {r0, r3, r5, r6, r8, r9, sl, fp, sp, lr}
    1548:	00000400 	andeq	r0, r0, r0, lsl #8
    154c:	6962696c 	stmdbvs	r2!, {r2, r3, r5, r6, r8, fp, sp, lr}^
    1550:	00682e6f 	rsbeq	r2, r8, pc, ror #28
    1554:	73000004 	movwvc	r0, #4
    1558:	655f7379 	ldrbvs	r7, [pc, #-889]	; 11e7 <pthread_mutex_unlock@plt-0xf749>
    155c:	696c7272 	stmdbvs	ip!, {r1, r4, r5, r6, r9, ip, sp, lr}^
    1560:	682e7473 	stmdavs	lr!, {r0, r1, r4, r5, r6, sl, ip, sp, lr}
    1564:	00000200 	andeq	r0, r0, r0, lsl #4
    1568:	6c6c616d 	stfvse	f6, [ip], #-436	; 0xfffffe4c
    156c:	682e636f 	stmdavs	lr!, {r0, r1, r2, r3, r5, r6, r8, r9, sp, lr}
    1570:	00000400 	andeq	r0, r0, r0, lsl #8
    1574:	69647473 	stmdbvs	r4!, {r0, r1, r4, r5, r6, sl, ip, sp, lr}^
    1578:	682e746e 	stmdavs	lr!, {r1, r2, r3, r5, r6, sl, ip, sp, lr}
    157c:	00000400 	andeq	r0, r0, r0, lsl #8
    1580:	5f656574 	svcpl	0x00656574
    1584:	65696c63 	strbvs	r6, [r9, #-3171]!	; 0xfffff39d
    1588:	615f746e 	cmpvs	pc, lr, ror #8
    158c:	682e6970 	stmdavs	lr!, {r4, r5, r6, r8, fp, sp, lr}
    1590:	00000500 	andeq	r0, r0, r0, lsl #10
    1594:	656d6974 	strbvs	r6, [sp, #-2420]!	; 0xfffff68c
    1598:	0400682e 	streq	r6, [r0], #-2094	; 0xfffff7d2
    159c:	6c620000 	stclvs	0, cr0, [r2], #-0
    15a0:	32656b61 	rsbcc	r6, r5, #99328	; 0x18400
    15a4:	0100682e 	tsteq	r0, lr, lsr #16
    15a8:	00000000 	andeq	r0, r0, r0
    15ac:	49980205 	ldmibmi	r8, {r0, r2, r9}
    15b0:	ca030004 	bgt	c15c8 <ringBuffer+0x698f0>
    15b4:	7a860100 	bvc	fe1819bc <__bss_end__+0xf48933e8>
    15b8:	4d844408 	cfstrsmi	mvf4, [r4, #32]
    15bc:	a5599f59 	ldrbge	r9, [r9, #-3929]	; 0xfffff0a7
    15c0:	b1593e08 	cmplt	r9, r8, lsl #28
    15c4:	4b4b5e75 	blmi	12d8fa0 <ringBuffer+0x12812c8>
    15c8:	59ca694b 	stmibpl	sl, {r0, r1, r3, r6, r8, fp, sp, lr}^
    15cc:	03ac5503 			; <UNDEFINED> instruction: 0x03ac5503
    15d0:	be082037 	mcrlt	0, 0, r2, cr8, cr7, {1}
    15d4:	695a7550 	ldmdbvs	sl, {r4, r6, r8, sl, ip, sp, lr}^
    15d8:	e6b059ca 	ldrt	r5, [r0], sl, asr #19
    15dc:	685a6876 	ldmdavs	sl, {r1, r2, r4, r5, r6, fp, sp, lr}^
    15e0:	7567675b 	strbvc	r6, [r7, #-1883]!	; 0xfffff8a5
    15e4:	1e40753e 	mcrne	5, 2, r7, cr0, cr14, {1}
    15e8:	00599f68 	subseq	r9, r9, r8, ror #30
    15ec:	3d030402 	cfstrscc	mvf0, [r3, #-8]
    15f0:	03040200 	movweq	r0, #16896	; 0x4200
    15f4:	0402009d 	streq	r0, [r2], #-157	; 0xffffff63
    15f8:	063c0601 	ldrteq	r0, [ip], -r1, lsl #12
    15fc:	756a3d4d 	strbvc	r3, [sl, #-3405]!	; 0xfffff2b3
    1600:	3ed73da1 	cdpcc	13, 13, cr3, cr7, cr1, {5}
    1604:	cdd8c93d 	vldrgt.16	s25, [r8, #122]	; 0x7a	; <UNPREDICTABLE>
    1608:	4cc93dd7 	stclmi	13, cr3, [r9], {215}	; 0xd7
    160c:	02040200 	andeq	r0, r4, #0, 4
    1610:	00c86e03 	sbceq	r6, r8, r3, lsl #28
    1614:	06010402 	streq	r0, [r1], -r2, lsl #8
    1618:	1503063c 	strne	r0, [r3, #-1596]	; 0xfffff9c4
    161c:	0313083c 	tsteq	r3, #60, 16	; 0x3c0000
    1620:	41a25809 			; <UNDEFINED> instruction: 0x41a25809
    1624:	59593e86 	ldmdbpl	r9, {r1, r2, r7, r9, sl, fp, ip, sp}^
    1628:	5bbb5c91 	blpl	feed8874 <__bss_end__+0xf55ea2a0>
    162c:	41821903 	orrmi	r1, r2, r3, lsl #18
    1630:	00794085 	rsbseq	r4, r9, r5, lsl #1
    1634:	06010402 	streq	r0, [r1], -r2, lsl #8
    1638:	59590682 	ldmdbpl	r9, {r1, r7, r9, sl}^
    163c:	03915abb 	orrseq	r5, r1, #765952	; 0xbb000
    1640:	03667fb6 	cmneq	r6, #728	; 0x2d8
    1644:	d60800f7 			; <UNDEFINED> instruction: 0xd60800f7
    1648:	833e7559 	teqhi	lr, #373293056	; 0x16400000
    164c:	681e4067 	ldmdavs	lr, {r0, r1, r2, r5, r6, lr}
    1650:	3d7667af 	ldclcc	7, cr6, [r6, #-700]!	; 0xfffffd44
    1654:	03040200 	movweq	r0, #16896	; 0x4200
    1658:	0402003d 	streq	r0, [r2], #-61	; 0xffffffc3
    165c:	0200ab03 	andeq	sl, r0, #3072	; 0xc00
    1660:	3c060104 	stfccs	f0, [r6], {4}
    1664:	0c034d06 	stceq	13, cr4, [r3], {6}
    1668:	2077033c 	rsbscs	r0, r7, ip, lsr r3
    166c:	02660903 	rsbeq	r0, r6, #49152	; 0xc000
    1670:	0101000b 	tsteq	r1, fp

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
  64:	000001c0 	andeq	r0, r0, r0, asr #3
  68:	8e100e44 	cdphi	14, 1, cr0, cr0, cr4, {2}
  6c:	85028b01 	strhi	r8, [r2, #-2817]	; 0xfffff4ff
  70:	44048403 	strmi	r8, [r4], #-1027	; 0xfffffbfd
  74:	44080b0c 	strmi	r0, [r8], #-2828	; 0xfffff4f4
  78:	06028805 	streq	r8, [r2], -r5, lsl #16
  7c:	00000020 	andeq	r0, r0, r0, lsr #32
  80:	00000000 	andeq	r0, r0, r0
  84:	000201c0 	andeq	r0, r2, r0, asr #3
  88:	00000200 	andeq	r0, r0, r0, lsl #4
  8c:	8e100e44 	cdphi	14, 1, cr0, cr0, cr4, {2}
  90:	85028b01 	strhi	r8, [r2, #-2817]	; 0xfffff4ff
  94:	44048403 	strmi	r8, [r4], #-1027	; 0xfffffbfd
  98:	44080b0c 	strmi	r0, [r8], #-2828	; 0xfffff4f4
  9c:	06028805 	streq	r8, [r2], -r5, lsl #16
  a0:	00000024 	andeq	r0, r0, r4, lsr #32
  a4:	00000000 	andeq	r0, r0, r0
  a8:	000203c0 	andeq	r0, r2, r0, asr #7
  ac:	000001ec 	andeq	r0, r0, ip, ror #3
  b0:	8e100e44 	cdphi	14, 1, cr0, cr0, cr4, {2}
  b4:	8a028b01 	bhi	a2cc0 <ringBuffer+0x4afe8>
  b8:	44048403 	strmi	r8, [r4], #-1027	; 0xfffffbfd
  bc:	44080b0c 	strmi	r0, [r8], #-2828	; 0xfffff4f4
  c0:	06028905 	streq	r8, [r2], -r5, lsl #18
  c4:	08028805 	stmdaeq	r2, {r0, r2, fp, pc}
  c8:	00000020 	andeq	r0, r0, r0, lsr #32
  cc:	00000000 	andeq	r0, r0, r0
  d0:	000401d0 	ldrdeq	r0, [r4], -r0	; <UNPREDICTABLE>
  d4:	0000013c 	andeq	r0, r0, ip, lsr r1
  d8:	8e100e44 	cdphi	14, 1, cr0, cr0, cr4, {2}
  dc:	8a028b01 	bhi	a2ce8 <ringBuffer+0x4b010>
  e0:	44048403 	strmi	r8, [r4], #-1027	; 0xfffffbfd
  e4:	44080b0c 	strmi	r0, [r8], #-2828	; 0xfffff4f4
  e8:	06028805 	streq	r8, [r2], -r5, lsl #16
  ec:	00000024 	andeq	r0, r0, r4, lsr #32
  f0:	00000000 	andeq	r0, r0, r0
  f4:	0004030c 	andeq	r0, r4, ip, lsl #6
  f8:	00000074 	andeq	r0, r0, r4, ror r0
  fc:	8e200e44 	cdphi	14, 2, cr0, cr0, cr4, {2}
 100:	8a028b01 	bhi	a2d0c <ringBuffer+0x4b034>
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
 160:	8a028b01 	bhi	a2d6c <ringBuffer+0x4b094>
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
 19c:	000000c4 	andeq	r0, r0, r4, asr #1
 1a0:	8e080e44 	cdphi	14, 0, cr0, cr8, cr4, {2}
 1a4:	44028b01 	strmi	r8, [r2], #-2817	; 0xfffff4ff
 1a8:	00000b0d 	andeq	r0, r0, sp, lsl #22
 1ac:	00000018 	andeq	r0, r0, r8, lsl r0
 1b0:	00000000 	andeq	r0, r0, r0
 1b4:	0004080c 	andeq	r0, r4, ip, lsl #16
 1b8:	0000003c 	andeq	r0, r0, ip, lsr r0
 1bc:	8e080e44 	cdphi	14, 0, cr0, cr8, cr4, {2}
 1c0:	44028b01 	strmi	r8, [r2], #-2817	; 0xfffff4ff
 1c4:	00000b0d 	andeq	r0, r0, sp, lsl #22
 1c8:	00000018 	andeq	r0, r0, r8, lsl r0
 1cc:	00000000 	andeq	r0, r0, r0
 1d0:	00040848 	andeq	r0, r4, r8, asr #16
 1d4:	00000044 	andeq	r0, r0, r4, asr #32
 1d8:	8e080e44 	cdphi	14, 0, cr0, cr8, cr4, {2}
 1dc:	44028b01 	strmi	r8, [r2], #-2817	; 0xfffff4ff
 1e0:	00000b0d 	andeq	r0, r0, sp, lsl #22
 1e4:	00000018 	andeq	r0, r0, r8, lsl r0
 1e8:	00000000 	andeq	r0, r0, r0
 1ec:	000205ac 	andeq	r0, r2, ip, lsr #11
 1f0:	00000024 	andeq	r0, r0, r4, lsr #32
 1f4:	8e080e44 	cdphi	14, 0, cr0, cr8, cr4, {2}
 1f8:	44028b01 	strmi	r8, [r2], #-2817	; 0xfffff4ff
 1fc:	00000b0d 	andeq	r0, r0, sp, lsl #22
 200:	00000018 	andeq	r0, r0, r8, lsl r0
 204:	00000000 	andeq	r0, r0, r0
 208:	0004088c 	andeq	r0, r4, ip, lsl #17
 20c:	00000030 	andeq	r0, r0, r0, lsr r0
 210:	8e080e44 	cdphi	14, 0, cr0, cr8, cr4, {2}
 214:	44028b01 	strmi	r8, [r2], #-2817	; 0xfffff4ff
 218:	00000b0d 	andeq	r0, r0, sp, lsl #22
 21c:	00000018 	andeq	r0, r0, r8, lsl r0
 220:	00000000 	andeq	r0, r0, r0
 224:	000408bc 			; <UNDEFINED> instruction: 0x000408bc
 228:	00000050 	andeq	r0, r0, r0, asr r0
 22c:	8e080e44 	cdphi	14, 0, cr0, cr8, cr4, {2}
 230:	44028b01 	strmi	r8, [r2], #-2817	; 0xfffff4ff
 234:	00000b0d 	andeq	r0, r0, sp, lsl #22
 238:	00000018 	andeq	r0, r0, r8, lsl r0
 23c:	00000000 	andeq	r0, r0, r0
 240:	0004090c 	andeq	r0, r4, ip, lsl #18
 244:	00000020 	andeq	r0, r0, r0, lsr #32
 248:	8e080e44 	cdphi	14, 0, cr0, cr8, cr4, {2}
 24c:	44028b01 	strmi	r8, [r2], #-2817	; 0xfffff4ff
 250:	00000b0d 	andeq	r0, r0, sp, lsl #22
 254:	00000018 	andeq	r0, r0, r8, lsl r0
 258:	00000000 	andeq	r0, r0, r0
 25c:	000205d0 	ldrdeq	r0, [r2], -r0	; <UNPREDICTABLE>
 260:	00000048 	andeq	r0, r0, r8, asr #32
 264:	8e080e44 	cdphi	14, 0, cr0, cr8, cr4, {2}
 268:	44028b01 	strmi	r8, [r2], #-2817	; 0xfffff4ff
 26c:	00000b0d 	andeq	r0, r0, sp, lsl #22
 270:	00000018 	andeq	r0, r0, r8, lsl r0
 274:	00000000 	andeq	r0, r0, r0
 278:	0004092c 	andeq	r0, r4, ip, lsr #18
 27c:	0000003c 	andeq	r0, r0, ip, lsr r0
 280:	8e080e44 	cdphi	14, 0, cr0, cr8, cr4, {2}
 284:	44028b01 	strmi	r8, [r2], #-2817	; 0xfffff4ff
 288:	00000b0d 	andeq	r0, r0, sp, lsl #22
 28c:	00000018 	andeq	r0, r0, r8, lsl r0
 290:	00000000 	andeq	r0, r0, r0
 294:	00040968 	andeq	r0, r4, r8, ror #18
 298:	00000040 	andeq	r0, r0, r0, asr #32
 29c:	8e080e44 	cdphi	14, 0, cr0, cr8, cr4, {2}
 2a0:	44028b01 	strmi	r8, [r2], #-2817	; 0xfffff4ff
 2a4:	00000b0d 	andeq	r0, r0, sp, lsl #22
 2a8:	00000018 	andeq	r0, r0, r8, lsl r0
 2ac:	00000000 	andeq	r0, r0, r0
 2b0:	000409a8 	andeq	r0, r4, r8, lsr #19
 2b4:	00000030 	andeq	r0, r0, r0, lsr r0
 2b8:	8e080e44 	cdphi	14, 0, cr0, cr8, cr4, {2}
 2bc:	44028b01 	strmi	r8, [r2], #-2817	; 0xfffff4ff
 2c0:	00000b0d 	andeq	r0, r0, sp, lsl #22
 2c4:	00000018 	andeq	r0, r0, r8, lsl r0
 2c8:	00000000 	andeq	r0, r0, r0
 2cc:	00020618 	andeq	r0, r2, r8, lsl r6
 2d0:	0000002c 	andeq	r0, r0, ip, lsr #32
 2d4:	8e080e44 	cdphi	14, 0, cr0, cr8, cr4, {2}
 2d8:	44028b01 	strmi	r8, [r2], #-2817	; 0xfffff4ff
 2dc:	00000b0d 	andeq	r0, r0, sp, lsl #22
 2e0:	00000018 	andeq	r0, r0, r8, lsl r0
 2e4:	00000000 	andeq	r0, r0, r0
 2e8:	00020644 	andeq	r0, r2, r4, asr #12
 2ec:	00000030 	andeq	r0, r0, r0, lsr r0
 2f0:	8e080e44 	cdphi	14, 0, cr0, cr8, cr4, {2}
 2f4:	44028b01 	strmi	r8, [r2], #-2817	; 0xfffff4ff
 2f8:	00000b0d 	andeq	r0, r0, sp, lsl #22
 2fc:	00000020 	andeq	r0, r0, r0, lsr #32
 300:	00000000 	andeq	r0, r0, r0
 304:	00020674 	andeq	r0, r2, r4, ror r6
 308:	00000044 	andeq	r0, r0, r4, asr #32
 30c:	8e180e44 	cdphi	14, 1, cr0, cr8, cr4, {2}
 310:	87028b01 	strhi	r8, [r2, -r1, lsl #22]
 314:	85048603 	strhi	r8, [r4, #-1539]	; 0xfffff9fd
 318:	44068405 	strmi	r8, [r6], #-1029	; 0xfffffbfb
 31c:	00080b0c 	andeq	r0, r8, ip, lsl #22
 320:	00000018 	andeq	r0, r0, r8, lsl r0
 324:	00000000 	andeq	r0, r0, r0
 328:	000206b8 			; <UNDEFINED> instruction: 0x000206b8
 32c:	00000028 	andeq	r0, r0, r8, lsr #32
 330:	8e080e44 	cdphi	14, 0, cr0, cr8, cr4, {2}
 334:	44028b01 	strmi	r8, [r2], #-2817	; 0xfffff4ff
 338:	00000b0d 	andeq	r0, r0, sp, lsl #22
 33c:	00000020 	andeq	r0, r0, r0, lsr #32
 340:	00000000 	andeq	r0, r0, r0
 344:	000409d8 	ldrdeq	r0, [r4], -r8
 348:	00000058 	andeq	r0, r0, r8, asr r0
 34c:	8e180e44 	cdphi	14, 1, cr0, cr8, cr4, {2}
 350:	8a028b01 	bhi	a2f5c <ringBuffer+0x4b284>
 354:	85048603 	strhi	r8, [r4, #-1539]	; 0xfffff9fd
 358:	44068405 	strmi	r8, [r6], #-1029	; 0xfffffbfb
 35c:	00080b0c 	andeq	r0, r8, ip, lsl #22
 360:	00000018 	andeq	r0, r0, r8, lsl r0
 364:	00000000 	andeq	r0, r0, r0
 368:	000206e0 	andeq	r0, r2, r0, ror #13
 36c:	00000038 	andeq	r0, r0, r8, lsr r0
 370:	8e080e44 	cdphi	14, 0, cr0, cr8, cr4, {2}
 374:	44028b01 	strmi	r8, [r2], #-2817	; 0xfffff4ff
 378:	00000b0d 	andeq	r0, r0, sp, lsl #22
 37c:	00000018 	andeq	r0, r0, r8, lsl r0
 380:	00000000 	andeq	r0, r0, r0
 384:	00020718 	andeq	r0, r2, r8, lsl r7
 388:	00000050 	andeq	r0, r0, r0, asr r0
 38c:	8e080e44 	cdphi	14, 0, cr0, cr8, cr4, {2}
 390:	44028b01 	strmi	r8, [r2], #-2817	; 0xfffff4ff
 394:	00000b0d 	andeq	r0, r0, sp, lsl #22
 398:	00000018 	andeq	r0, r0, r8, lsl r0
 39c:	00000000 	andeq	r0, r0, r0
 3a0:	00020768 	andeq	r0, r2, r8, ror #14
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
 3cc:	00040ad8 	ldrdeq	r0, [r4], -r8
 3d0:	0000003c 	andeq	r0, r0, ip, lsr r0
 3d4:	87040e41 	strhi	r0, [r4, -r1, asr #28]
 3d8:	180e4101 	stmdane	lr, {r0, r8, lr}
 3dc:	57070d41 	strpl	r0, [r7, -r1, asr #26]
 3e0:	0d41040e 	cfstrdeq	mvd0, [r1, #-56]	; 0xffffffc8
 3e4:	0ec7420d 	cdpeq	2, 12, cr4, cr7, cr13, {0}
 3e8:	00000000 	andeq	r0, r0, r0
 3ec:	00000024 	andeq	r0, r0, r4, lsr #32
 3f0:	000003b4 			; <UNDEFINED> instruction: 0x000003b4
 3f4:	00040b14 	andeq	r0, r4, r4, lsl fp
 3f8:	0000003a 	andeq	r0, r0, sl, lsr r0
 3fc:	87040e41 	strhi	r0, [r4, -r1, asr #28]
 400:	180e4101 	stmdane	lr, {r0, r8, lr}
 404:	56070d41 	strpl	r0, [r7], -r1, asr #26
 408:	0d41040e 	cfstrdeq	mvd0, [r1, #-56]	; 0xffffffc8
 40c:	0ec7420d 	cdpeq	2, 12, cr4, cr7, cr13, {0}
 410:	00000000 	andeq	r0, r0, r0
 414:	00000024 	andeq	r0, r0, r4, lsr #32
 418:	000003b4 			; <UNDEFINED> instruction: 0x000003b4
 41c:	00040b4e 	andeq	r0, r4, lr, asr #22
 420:	00000046 	andeq	r0, r0, r6, asr #32
 424:	87040e41 	strhi	r0, [r4, -r1, asr #28]
 428:	180e4101 	stmdane	lr, {r0, r8, lr}
 42c:	5c070d41 	stcpl	13, cr0, [r7], {65}	; 0x41
 430:	0d41040e 	cfstrdeq	mvd0, [r1, #-56]	; 0xffffffc8
 434:	0ec7420d 	cdpeq	2, 12, cr4, cr7, cr13, {0}
 438:	00000000 	andeq	r0, r0, r0
 43c:	00000024 	andeq	r0, r0, r4, lsr #32
 440:	000003b4 			; <UNDEFINED> instruction: 0x000003b4
 444:	00040b94 	muleq	r4, r4, fp
 448:	0000001e 	andeq	r0, r0, lr, lsl r0
 44c:	87040e41 	strhi	r0, [r4, -r1, asr #28]
 450:	100e4101 	andne	r4, lr, r1, lsl #2
 454:	48070d41 	stmdami	r7, {r0, r6, r8, sl, fp}
 458:	0d41040e 	cfstrdeq	mvd0, [r1, #-56]	; 0xffffffc8
 45c:	0ec7420d 	cdpeq	2, 12, cr4, cr7, cr13, {0}
 460:	00000000 	andeq	r0, r0, r0
 464:	00000020 	andeq	r0, r0, r0, lsr #32
 468:	000003b4 			; <UNDEFINED> instruction: 0x000003b4
 46c:	00040bb2 			; <UNDEFINED> instruction: 0x00040bb2
 470:	00000026 	andeq	r0, r0, r6, lsr #32
 474:	87080e41 	strhi	r0, [r8, -r1, asr #28]
 478:	41018e02 	tstmi	r1, r2, lsl #28
 47c:	0d41100e 	stcleq	0, cr1, [r1, #-56]	; 0xffffffc8
 480:	080e4b07 	stmdaeq	lr, {r0, r1, r2, r8, r9, fp, lr}
 484:	000d0d41 	andeq	r0, sp, r1, asr #26
 488:	00000024 	andeq	r0, r0, r4, lsr #32
 48c:	000003b4 			; <UNDEFINED> instruction: 0x000003b4
 490:	00040bd8 	ldrdeq	r0, [r4], -r8
 494:	0000001c 	andeq	r0, r0, ip, lsl r0
 498:	87040e41 	strhi	r0, [r4, -r1, asr #28]
 49c:	100e4101 	andne	r4, lr, r1, lsl #2
 4a0:	47070d41 	strmi	r0, [r7, -r1, asr #26]
 4a4:	0d41040e 	cfstrdeq	mvd0, [r1, #-56]	; 0xffffffc8
 4a8:	0ec7420d 	cdpeq	2, 12, cr4, cr7, cr13, {0}
 4ac:	00000000 	andeq	r0, r0, r0
 4b0:	00000024 	andeq	r0, r0, r4, lsr #32
 4b4:	000003b4 			; <UNDEFINED> instruction: 0x000003b4
 4b8:	00040bf4 	strdeq	r0, [r4], -r4
 4bc:	00000022 	andeq	r0, r0, r2, lsr #32
 4c0:	87040e41 	strhi	r0, [r4, -r1, asr #28]
 4c4:	100e4101 	andne	r4, lr, r1, lsl #2
 4c8:	4a070d41 	bmi	1c39d4 <ringBuffer+0x16bcfc>
 4cc:	0d41040e 	cfstrdeq	mvd0, [r1, #-56]	; 0xffffffc8
 4d0:	0ec7420d 	cdpeq	2, 12, cr4, cr7, cr13, {0}
 4d4:	00000000 	andeq	r0, r0, r0
 4d8:	00000020 	andeq	r0, r0, r0, lsr #32
 4dc:	000003b4 			; <UNDEFINED> instruction: 0x000003b4
 4e0:	00040c16 	andeq	r0, r4, r6, lsl ip
 4e4:	00000028 	andeq	r0, r0, r8, lsr #32
 4e8:	87080e41 	strhi	r0, [r8, -r1, asr #28]
 4ec:	41018e02 	tstmi	r1, r2, lsl #28
 4f0:	0d41100e 	stcleq	0, cr1, [r1, #-56]	; 0xffffffc8
 4f4:	080e4f07 	stmdaeq	lr, {r0, r1, r2, r8, r9, sl, fp, lr}
 4f8:	000d0d41 	andeq	r0, sp, r1, asr #26
 4fc:	00000024 	andeq	r0, r0, r4, lsr #32
 500:	000003b4 			; <UNDEFINED> instruction: 0x000003b4
 504:	00040c3e 	andeq	r0, r4, lr, lsr ip
 508:	0000003c 	andeq	r0, r0, ip, lsr r0
 50c:	87040e41 	strhi	r0, [r4, -r1, asr #28]
 510:	100e4101 	andne	r4, lr, r1, lsl #2
 514:	57070d41 	strpl	r0, [r7, -r1, asr #26]
 518:	0d41040e 	cfstrdeq	mvd0, [r1, #-56]	; 0xffffffc8
 51c:	0ec7420d 	cdpeq	2, 12, cr4, cr7, cr13, {0}
 520:	00000000 	andeq	r0, r0, r0
 524:	00000020 	andeq	r0, r0, r0, lsr #32
 528:	000003b4 			; <UNDEFINED> instruction: 0x000003b4
 52c:	00040c7a 	andeq	r0, r4, sl, ror ip
 530:	00000046 	andeq	r0, r0, r6, asr #32
 534:	87080e41 	strhi	r0, [r8, -r1, asr #28]
 538:	41018e02 	tstmi	r1, r2, lsl #28
 53c:	0d41180e 	stcleq	8, cr1, [r1, #-56]	; 0xffffffc8
 540:	080e5b07 	stmdaeq	lr, {r0, r1, r2, r8, r9, fp, ip, lr}
 544:	000d0d41 	andeq	r0, sp, r1, asr #26
 548:	00000020 	andeq	r0, r0, r0, lsr #32
 54c:	000003b4 			; <UNDEFINED> instruction: 0x000003b4
 550:	00040cc0 	andeq	r0, r4, r0, asr #25
 554:	0000005c 	andeq	r0, r0, ip, asr r0
 558:	87080e41 	strhi	r0, [r8, -r1, asr #28]
 55c:	41018e02 	tstmi	r1, r2, lsl #28
 560:	0d41180e 	stcleq	8, cr1, [r1, #-56]	; 0xffffffc8
 564:	080e6907 	stmdaeq	lr, {r0, r1, r2, r8, fp, sp, lr}
 568:	000d0d41 	andeq	r0, sp, r1, asr #26
 56c:	00000020 	andeq	r0, r0, r0, lsr #32
 570:	000003b4 			; <UNDEFINED> instruction: 0x000003b4
 574:	00040d1c 	andeq	r0, r4, ip, lsl sp
 578:	00000096 	muleq	r0, r6, r0
 57c:	87080e41 	strhi	r0, [r8, -r1, asr #28]
 580:	41018e02 	tstmi	r1, r2, lsl #28
 584:	0d41300e 	stcleq	0, cr3, [r1, #-56]	; 0xffffffc8
 588:	0e460207 	cdpeq	2, 4, cr0, cr6, cr7, {0}
 58c:	0d0d4108 	stfeqs	f4, [sp, #-32]	; 0xffffffe0
 590:	00000020 	andeq	r0, r0, r0, lsr #32
 594:	000003b4 			; <UNDEFINED> instruction: 0x000003b4
 598:	00040db2 			; <UNDEFINED> instruction: 0x00040db2
 59c:	00000102 	andeq	r0, r0, r2, lsl #2
 5a0:	87080e41 	strhi	r0, [r8, -r1, asr #28]
 5a4:	41018e02 	tstmi	r1, r2, lsl #28
 5a8:	0d41780e 	stcleq	8, cr7, [r1, #-56]	; 0xffffffc8
 5ac:	0e7c0207 	cdpeq	2, 7, cr0, cr12, cr7, {0}
 5b0:	0d0d4108 	stfeqs	f4, [sp, #-32]	; 0xffffffe0
 5b4:	00000024 	andeq	r0, r0, r4, lsr #32
 5b8:	000003b4 			; <UNDEFINED> instruction: 0x000003b4
 5bc:	00040eb4 			; <UNDEFINED> instruction: 0x00040eb4
 5c0:	00002bc0 	andeq	r2, r0, r0, asr #23
 5c4:	87080e41 	strhi	r0, [r8, -r1, asr #28]
 5c8:	41018e02 	tstmi	r1, r2, lsl #28
 5cc:	4101980e 	tstmi	r1, lr, lsl #16
 5d0:	db03070d 	blle	c220c <ringBuffer+0x6a534>
 5d4:	41080e15 	tstmi	r8, r5, lsl lr
 5d8:	00000d0d 	andeq	r0, r0, sp, lsl #26
 5dc:	00000020 	andeq	r0, r0, r0, lsr #32
 5e0:	000003b4 			; <UNDEFINED> instruction: 0x000003b4
 5e4:	00043a74 	andeq	r3, r4, r4, ror sl
 5e8:	000000ba 	strheq	r0, [r0], -sl
 5ec:	87080e41 	strhi	r0, [r8, -r1, asr #28]
 5f0:	41018e02 	tstmi	r1, r2, lsl #28
 5f4:	0d41280e 	stcleq	8, cr2, [r1, #-56]	; 0xffffffc8
 5f8:	0e580207 	cdpeq	2, 5, cr0, cr8, cr7, {0}
 5fc:	0d0d4108 	stfeqs	f4, [sp, #-32]	; 0xffffffe0
 600:	00000020 	andeq	r0, r0, r0, lsr #32
 604:	000003b4 			; <UNDEFINED> instruction: 0x000003b4
 608:	00043b2e 	andeq	r3, r4, lr, lsr #22
 60c:	000000ca 	andeq	r0, r0, sl, asr #1
 610:	87080e41 	strhi	r0, [r8, -r1, asr #28]
 614:	41018e02 	tstmi	r1, r2, lsl #28
 618:	0d41400e 	stcleq	0, cr4, [r1, #-56]	; 0xffffffc8
 61c:	0e600207 	cdpeq	2, 6, cr0, cr0, cr7, {0}
 620:	0d0d4108 	stfeqs	f4, [sp, #-32]	; 0xffffffe0
 624:	00000024 	andeq	r0, r0, r4, lsr #32
 628:	000003b4 			; <UNDEFINED> instruction: 0x000003b4
 62c:	00043bf8 	strdeq	r3, [r4], -r8
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
 664:	00043cc0 	andeq	r3, r4, r0, asr #25
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
 694:	00043d82 	andeq	r3, r4, r2, lsl #27
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
 6c0:	00043e50 	andeq	r3, r4, r0, asr lr
 6c4:	00000052 	andeq	r0, r0, r2, asr r0
 6c8:	87040e41 	strhi	r0, [r4, -r1, asr #28]
 6cc:	180e4101 	stmdane	lr, {r0, r8, lr}
 6d0:	62070d41 	andvs	r0, r7, #4160	; 0x1040
 6d4:	0d41040e 	cfstrdeq	mvd0, [r1, #-56]	; 0xffffffc8
 6d8:	0ec7420d 	cdpeq	2, 12, cr4, cr7, cr13, {0}
 6dc:	00000000 	andeq	r0, r0, r0
 6e0:	00000024 	andeq	r0, r0, r4, lsr #32
 6e4:	0000064c 	andeq	r0, r0, ip, asr #12
 6e8:	00043ea2 	andeq	r3, r4, r2, lsr #29
 6ec:	00000046 	andeq	r0, r0, r6, asr #32
 6f0:	87040e41 	strhi	r0, [r4, -r1, asr #28]
 6f4:	200e4101 	andcs	r4, lr, r1, lsl #2
 6f8:	5c070d41 	stcpl	13, cr0, [r7], {65}	; 0x41
 6fc:	0d41040e 	cfstrdeq	mvd0, [r1, #-56]	; 0xffffffc8
 700:	0ec7420d 	cdpeq	2, 12, cr4, cr7, cr13, {0}
 704:	00000000 	andeq	r0, r0, r0
 708:	00000024 	andeq	r0, r0, r4, lsr #32
 70c:	0000064c 	andeq	r0, r0, ip, asr #12
 710:	00043ee8 	andeq	r3, r4, r8, ror #29
 714:	00000018 	andeq	r0, r0, r8, lsl r0
 718:	87040e41 	strhi	r0, [r4, -r1, asr #28]
 71c:	100e4101 	andne	r4, lr, r1, lsl #2
 720:	45070d41 	strmi	r0, [r7, #-3393]	; 0xfffff2bf
 724:	0d41040e 	cfstrdeq	mvd0, [r1, #-56]	; 0xffffffc8
 728:	0ec7420d 	cdpeq	2, 12, cr4, cr7, cr13, {0}
 72c:	00000000 	andeq	r0, r0, r0
 730:	00000024 	andeq	r0, r0, r4, lsr #32
 734:	0000064c 	andeq	r0, r0, ip, asr #12
 738:	00043f00 	andeq	r3, r4, r0, lsl #30
 73c:	000000a0 	andeq	r0, r0, r0, lsr #1
 740:	840c0e41 	strhi	r0, [ip], #-3649	; 0xfffff1bf
 744:	8e028703 	cdphi	7, 0, cr8, cr2, cr3, {0}
 748:	380e4101 	stmdacc	lr, {r0, r8, lr}
 74c:	30070c41 	andcc	r0, r7, r1, asr #24
 750:	0c0e4002 	stceq	0, cr4, [lr], {2}
 754:	000d0d41 	andeq	r0, sp, r1, asr #26
 758:	00000024 	andeq	r0, r0, r4, lsr #32
 75c:	0000064c 	andeq	r0, r0, ip, asr #12
 760:	00043fa0 	andeq	r3, r4, r0, lsr #31
 764:	000001c0 	andeq	r0, r0, r0, asr #3
 768:	87040e41 	strhi	r0, [r4, -r1, asr #28]
 76c:	180e4101 	stmdane	lr, {r0, r8, lr}
 770:	02070d41 	andeq	r0, r7, #4160	; 0x1040
 774:	41040ed9 	ldrdmi	r0, [r4, -r9]
 778:	c7420d0d 	strbgt	r0, [r2, -sp, lsl #26]
 77c:	0000000e 	andeq	r0, r0, lr
 780:	00000024 	andeq	r0, r0, r4, lsr #32
 784:	0000064c 	andeq	r0, r0, ip, asr #12
 788:	00044160 	andeq	r4, r4, r0, ror #2
 78c:	0000011c 	andeq	r0, r0, ip, lsl r1
 790:	840c0e41 	strhi	r0, [ip], #-3649	; 0xfffff1bf
 794:	8e028703 	cdphi	7, 0, cr8, cr2, cr3, {0}
 798:	500e4101 	andpl	r4, lr, r1, lsl #2
 79c:	48070c41 	stmdami	r7, {r0, r6, sl, fp}
 7a0:	0c0e7c02 	stceq	12, cr7, [lr], {2}
 7a4:	000d0d41 	andeq	r0, sp, r1, asr #26
 7a8:	00000024 	andeq	r0, r0, r4, lsr #32
 7ac:	0000064c 	andeq	r0, r0, ip, asr #12
 7b0:	0004427c 	andeq	r4, r4, ip, ror r2
 7b4:	00000124 	andeq	r0, r0, r4, lsr #2
 7b8:	840c0e41 	strhi	r0, [ip], #-3649	; 0xfffff1bf
 7bc:	8e028703 	cdphi	7, 0, cr8, cr2, cr3, {0}
 7c0:	500e4101 	andpl	r4, lr, r1, lsl #2
 7c4:	48070c41 	stmdami	r7, {r0, r6, sl, fp}
 7c8:	0c0e8102 	stfeqd	f0, [lr], {2}
 7cc:	000d0d41 	andeq	r0, sp, r1, asr #26
 7d0:	00000024 	andeq	r0, r0, r4, lsr #32
 7d4:	0000064c 	andeq	r0, r0, ip, asr #12
 7d8:	000443a0 	andeq	r4, r4, r0, lsr #7
 7dc:	000000ac 	andeq	r0, r0, ip, lsr #1
 7e0:	840c0e41 	strhi	r0, [ip], #-3649	; 0xfffff1bf
 7e4:	8e028703 	cdphi	7, 0, cr8, cr2, cr3, {0}
 7e8:	380e4101 	stmdacc	lr, {r0, r8, lr}
 7ec:	30070c41 	andcc	r0, r7, r1, asr #24
 7f0:	0c0e4702 	stceq	7, cr4, [lr], {2}
 7f4:	000d0d41 	andeq	r0, sp, r1, asr #26
 7f8:	00000024 	andeq	r0, r0, r4, lsr #32
 7fc:	0000064c 	andeq	r0, r0, ip, asr #12
 800:	0004444c 	andeq	r4, r4, ip, asr #8
 804:	000000dc 	ldrdeq	r0, [r0], -ip
 808:	840c0e41 	strhi	r0, [ip], #-3649	; 0xfffff1bf
 80c:	8e028703 	cdphi	7, 0, cr8, cr2, cr3, {0}
 810:	380e4101 	stmdacc	lr, {r0, r8, lr}
 814:	30070c41 	andcc	r0, r7, r1, asr #24
 818:	0c0e5d02 	stceq	13, cr5, [lr], {2}
 81c:	000d0d41 	andeq	r0, sp, r1, asr #26
 820:	00000024 	andeq	r0, r0, r4, lsr #32
 824:	0000064c 	andeq	r0, r0, ip, asr #12
 828:	00044528 	andeq	r4, r4, r8, lsr #10
 82c:	0000011c 	andeq	r0, r0, ip, lsl r1
 830:	840c0e41 	strhi	r0, [ip], #-3649	; 0xfffff1bf
 834:	8e028703 	cdphi	7, 0, cr8, cr2, cr3, {0}
 838:	380e4101 	stmdacc	lr, {r0, r8, lr}
 83c:	30070c41 	andcc	r0, r7, r1, asr #24
 840:	0c0e7b02 			; <UNDEFINED> instruction: 0x0c0e7b02
 844:	000d0d41 	andeq	r0, sp, r1, asr #26
 848:	00000024 	andeq	r0, r0, r4, lsr #32
 84c:	0000064c 	andeq	r0, r0, ip, asr #12
 850:	00044644 	andeq	r4, r4, r4, asr #12
 854:	000000a4 	andeq	r0, r0, r4, lsr #1
 858:	840c0e41 	strhi	r0, [ip], #-3649	; 0xfffff1bf
 85c:	8e028703 	cdphi	7, 0, cr8, cr2, cr3, {0}
 860:	380e4101 	stmdacc	lr, {r0, r8, lr}
 864:	30070c41 	andcc	r0, r7, r1, asr #24
 868:	0c0e4202 	sfmeq	f4, 4, [lr], {2}
 86c:	000d0d41 	andeq	r0, sp, r1, asr #26
 870:	00000024 	andeq	r0, r0, r4, lsr #32
 874:	0000064c 	andeq	r0, r0, ip, asr #12
 878:	000446e8 	andeq	r4, r4, r8, ror #13
 87c:	00000120 	andeq	r0, r0, r0, lsr #2
 880:	840c0e41 	strhi	r0, [ip], #-3649	; 0xfffff1bf
 884:	8e028703 	cdphi	7, 0, cr8, cr2, cr3, {0}
 888:	400e4101 	andmi	r4, lr, r1, lsl #2
 88c:	38070c41 	stmdacc	r7, {r0, r6, sl, fp}
 890:	0c0e7e02 	stceq	14, cr7, [lr], {2}
 894:	000d0d41 	andeq	r0, sp, r1, asr #26
 898:	00000024 	andeq	r0, r0, r4, lsr #32
 89c:	0000064c 	andeq	r0, r0, ip, asr #12
 8a0:	00044808 	andeq	r4, r4, r8, lsl #16
 8a4:	000000a0 	andeq	r0, r0, r0, lsr #1
 8a8:	840c0e41 	strhi	r0, [ip], #-3649	; 0xfffff1bf
 8ac:	8e028703 	cdphi	7, 0, cr8, cr2, cr3, {0}
 8b0:	400e4101 	andmi	r4, lr, r1, lsl #2
 8b4:	38070c41 	stmdacc	r7, {r0, r6, sl, fp}
 8b8:	0c0e4102 	stfeqs	f4, [lr], {2}
 8bc:	000d0d41 	andeq	r0, sp, r1, asr #26
 8c0:	00000024 	andeq	r0, r0, r4, lsr #32
 8c4:	0000064c 	andeq	r0, r0, ip, asr #12
 8c8:	000448a8 	andeq	r4, r4, r8, lsr #17
 8cc:	00000098 	muleq	r0, r8, r0
 8d0:	840c0e41 	strhi	r0, [ip], #-3649	; 0xfffff1bf
 8d4:	8e028703 	cdphi	7, 0, cr8, cr2, cr3, {0}
 8d8:	400e4101 	andmi	r4, lr, r1, lsl #2
 8dc:	38070c41 	stmdacc	r7, {r0, r6, sl, fp}
 8e0:	410c0e7c 	tstmi	ip, ip, ror lr
 8e4:	00000d0d 	andeq	r0, r0, sp, lsl #26
 8e8:	00000024 	andeq	r0, r0, r4, lsr #32
 8ec:	0000064c 	andeq	r0, r0, ip, asr #12
 8f0:	00044940 	andeq	r4, r4, r0, asr #18
 8f4:	00000016 	andeq	r0, r0, r6, lsl r0
 8f8:	87040e41 	strhi	r0, [r4, -r1, asr #28]
 8fc:	100e4101 	andne	r4, lr, r1, lsl #2
 900:	44070d41 	strmi	r0, [r7], #-3393	; 0xfffff2bf
 904:	0d41040e 	cfstrdeq	mvd0, [r1, #-56]	; 0xffffffc8
 908:	0ec7420d 	cdpeq	2, 12, cr4, cr7, cr13, {0}
 90c:	00000000 	andeq	r0, r0, r0
 910:	00000018 	andeq	r0, r0, r8, lsl r0
 914:	0000064c 	andeq	r0, r0, ip, asr #12
 918:	00044956 	andeq	r4, r4, r6, asr r9
 91c:	00000016 	andeq	r0, r0, r6, lsl r0
 920:	87080e41 	strhi	r0, [r8, -r1, asr #28]
 924:	41018e02 	tstmi	r1, r2, lsl #28
 928:	0000070d 	andeq	r0, r0, sp, lsl #14
 92c:	00000018 	andeq	r0, r0, r8, lsl r0
 930:	0000064c 	andeq	r0, r0, ip, asr #12
 934:	0004496c 	andeq	r4, r4, ip, ror #18
 938:	0000002c 	andeq	r0, r0, ip, lsr #32
 93c:	87080e41 	strhi	r0, [r8, -r1, asr #28]
 940:	41018e02 	tstmi	r1, r2, lsl #28
 944:	0000070d 	andeq	r0, r0, sp, lsl #14
 948:	0000000c 	andeq	r0, r0, ip
 94c:	ffffffff 			; <UNDEFINED> instruction: 0xffffffff
 950:	7c020001 	stcvc	0, cr0, [r2], {1}
 954:	000d0c0e 	andeq	r0, sp, lr, lsl #24
 958:	00000024 	andeq	r0, r0, r4, lsr #32
 95c:	00000948 	andeq	r0, r0, r8, asr #18
 960:	00044998 	muleq	r4, r8, r9
 964:	00000194 	muleq	r0, r4, r1
 968:	840c0e41 	strhi	r0, [ip], #-3649	; 0xfffff1bf
 96c:	8e028703 	cdphi	7, 0, cr8, cr2, cr3, {0}
 970:	300e4101 	andcc	r4, lr, r1, lsl #2
 974:	20070c41 	andcs	r0, r7, r1, asr #24
 978:	0c0eab02 			; <UNDEFINED> instruction: 0x0c0eab02
 97c:	000d0d41 	andeq	r0, sp, r1, asr #26
 980:	0000001c 	andeq	r0, r0, ip, lsl r0
 984:	00000948 	andeq	r0, r0, r8, asr #18
 988:	00044b2c 	andeq	r4, r4, ip, lsr #22
 98c:	00000084 	andeq	r0, r0, r4, lsl #1
 990:	83100e41 	tsthi	r0, #1040	; 0x410
 994:	87038404 	strhi	r8, [r3, -r4, lsl #8]
 998:	41018e02 	tstmi	r1, r2, lsl #28
 99c:	0000070d 	andeq	r0, r0, sp, lsl #14
 9a0:	00000024 	andeq	r0, r0, r4, lsr #32
 9a4:	00000948 	andeq	r0, r0, r8, asr #18
 9a8:	00044bb0 			; <UNDEFINED> instruction: 0x00044bb0
 9ac:	0000001a 	andeq	r0, r0, sl, lsl r0
 9b0:	87040e41 	strhi	r0, [r4, -r1, asr #28]
 9b4:	180e4101 	stmdane	lr, {r0, r8, lr}
 9b8:	46070d41 	strmi	r0, [r7], -r1, asr #26
 9bc:	0d41040e 	cfstrdeq	mvd0, [r1, #-56]	; 0xffffffc8
 9c0:	0ec7420d 	cdpeq	2, 12, cr4, cr7, cr13, {0}
 9c4:	00000000 	andeq	r0, r0, r0
 9c8:	00000024 	andeq	r0, r0, r4, lsr #32
 9cc:	00000948 	andeq	r0, r0, r8, asr #18
 9d0:	00044bca 	andeq	r4, r4, sl, asr #23
 9d4:	00000016 	andeq	r0, r0, r6, lsl r0
 9d8:	87040e41 	strhi	r0, [r4, -r1, asr #28]
 9dc:	100e4101 	andne	r4, lr, r1, lsl #2
 9e0:	44070d41 	strmi	r0, [r7], #-3393	; 0xfffff2bf
 9e4:	0d41040e 	cfstrdeq	mvd0, [r1, #-56]	; 0xffffffc8
 9e8:	0ec7420d 	cdpeq	2, 12, cr4, cr7, cr13, {0}
 9ec:	00000000 	andeq	r0, r0, r0
 9f0:	00000024 	andeq	r0, r0, r4, lsr #32
 9f4:	00000948 	andeq	r0, r0, r8, asr #18
 9f8:	00044be0 	andeq	r4, r4, r0, ror #23
 9fc:	00000016 	andeq	r0, r0, r6, lsl r0
 a00:	87040e41 	strhi	r0, [r4, -r1, asr #28]
 a04:	100e4101 	andne	r4, lr, r1, lsl #2
 a08:	44070d41 	strmi	r0, [r7], #-3393	; 0xfffff2bf
 a0c:	0d41040e 	cfstrdeq	mvd0, [r1, #-56]	; 0xffffffc8
 a10:	0ec7420d 	cdpeq	2, 12, cr4, cr7, cr13, {0}
 a14:	00000000 	andeq	r0, r0, r0
 a18:	00000020 	andeq	r0, r0, r0, lsr #32
 a1c:	00000948 	andeq	r0, r0, r8, asr #18
 a20:	00044bf6 	strdeq	r4, [r4], -r6
 a24:	00000056 	andeq	r0, r0, r6, asr r0
 a28:	87080e41 	strhi	r0, [r8, -r1, asr #28]
 a2c:	41018e02 	tstmi	r1, r2, lsl #28
 a30:	0d41200e 	stcleq	0, cr2, [r1, #-56]	; 0xffffffc8
 a34:	080e6007 	stmdaeq	lr, {r0, r1, r2, sp, lr}
 a38:	000d0d41 	andeq	r0, sp, r1, asr #26
 a3c:	00000020 	andeq	r0, r0, r0, lsr #32
 a40:	00000948 	andeq	r0, r0, r8, asr #18
 a44:	00044c4c 	andeq	r4, r4, ip, asr #24
 a48:	00000044 	andeq	r0, r0, r4, asr #32
 a4c:	87080e41 	strhi	r0, [r8, -r1, asr #28]
 a50:	41018e02 	tstmi	r1, r2, lsl #28
 a54:	0d41180e 	stcleq	8, cr1, [r1, #-56]	; 0xffffffc8
 a58:	080e5b07 	stmdaeq	lr, {r0, r1, r2, r8, r9, fp, ip, lr}
 a5c:	000d0d41 	andeq	r0, sp, r1, asr #26
 a60:	00000020 	andeq	r0, r0, r0, lsr #32
 a64:	00000948 	andeq	r0, r0, r8, asr #18
 a68:	00044c90 	muleq	r4, r0, ip
 a6c:	0000012c 	andeq	r0, r0, ip, lsr #2
 a70:	87080e41 	strhi	r0, [r8, -r1, asr #28]
 a74:	41018e02 	tstmi	r1, r2, lsl #28
 a78:	0d41380e 	stcleq	8, cr3, [r1, #-56]	; 0xffffffc8
 a7c:	0e840207 	cdpeq	2, 8, cr0, cr4, cr7, {0}
 a80:	0d0d4108 	stfeqs	f4, [sp, #-32]	; 0xffffffe0
 a84:	0000001c 	andeq	r0, r0, ip, lsl r0
 a88:	00000948 	andeq	r0, r0, r8, asr #18
 a8c:	00044dbc 			; <UNDEFINED> instruction: 0x00044dbc
 a90:	00000168 	andeq	r0, r0, r8, ror #2
 a94:	840c0e41 	strhi	r0, [ip], #-3649	; 0xfffff1bf
 a98:	8e028703 	cdphi	7, 0, cr8, cr2, cr3, {0}
 a9c:	200e4101 	andcs	r4, lr, r1, lsl #2
 aa0:	00070d41 	andeq	r0, r7, r1, asr #26
 aa4:	00000020 	andeq	r0, r0, r0, lsr #32
 aa8:	00000948 	andeq	r0, r0, r8, asr #18
 aac:	00044f24 	andeq	r4, r4, r4, lsr #30
 ab0:	00000064 	andeq	r0, r0, r4, rrx
 ab4:	87080e41 	strhi	r0, [r8, -r1, asr #28]
 ab8:	41018e02 	tstmi	r1, r2, lsl #28
 abc:	0d41200e 	stcleq	0, cr2, [r1, #-56]	; 0xffffffc8
 ac0:	080e6607 	stmdaeq	lr, {r0, r1, r2, r9, sl, sp, lr}
 ac4:	000d0d41 	andeq	r0, sp, r1, asr #26
 ac8:	00000020 	andeq	r0, r0, r0, lsr #32
 acc:	00000948 	andeq	r0, r0, r8, asr #18
 ad0:	00044f88 	andeq	r4, r4, r8, lsl #31
 ad4:	00000074 	andeq	r0, r0, r4, ror r0
 ad8:	87080e41 	strhi	r0, [r8, -r1, asr #28]
 adc:	41018e02 	tstmi	r1, r2, lsl #28
 ae0:	0d41200e 	stcleq	0, cr2, [r1, #-56]	; 0xffffffc8
 ae4:	080e6e07 	stmdaeq	lr, {r0, r1, r2, r9, sl, fp, sp, lr}
 ae8:	000d0d41 	andeq	r0, sp, r1, asr #26

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
      40:	7a727a2f 	bvc	1c9e904 <ringBuffer+0x1c46c2c>
      44:	37313530 			; <UNDEFINED> instruction: 0x37313530
      48:	7574732f 	ldrbvc	r7, [r4, #-815]!	; 0xfffffcd1
      4c:	632f7964 			; <UNDEFINED> instruction: 0x632f7964
      50:	6e696168 	powvsez	f6, f1, #0.0
      54:	7474615f 	ldrbtvc	r6, [r4], #-351	; 0xfffffea1
      58:	61747365 	cmnvs	r4, r5, ror #6
      5c:	6e6f6974 			; <UNDEFINED> instruction: 0x6e6f6974
      60:	4952412f 	ldmdbmi	r2, {r0, r1, r2, r3, r5, r8, lr}^
      64:	7a727a2d 	bvc	1c9e920 <ringBuffer+0x1c46c48>
      68:	74616f2f 	strbtvc	r6, [r1], #-3887	; 0xfffff0d1
      6c:	6176652d 	cmnvs	r6, sp, lsr #10
      70:	7461756c 	strbtvc	r7, [r1], #-1388	; 0xfffffa94
      74:	2f6e6f69 	svccs	0x006e6f69
      78:	69727973 	ldmdbvs	r2!, {r0, r1, r4, r5, r6, r8, fp, ip, sp, lr}^
      7c:	2d65676e 	stclcs	7, cr6, [r5, #-440]!	; 0xfffffe48
      80:	67006263 	strvs	r6, [r0, -r3, ror #4]
      84:	61626f6c 	cmnvs	r2, ip, ror #30
      88:	61645f6c 	cmnvs	r4, ip, ror #30
      8c:	72006174 	andvc	r6, r0, #116, 2
      90:	726f6365 	rsbvc	r6, pc, #-1811939327	; 0x94000001
      94:	676e6964 	strbvs	r6, [lr, -r4, ror #18]!
      98:	616c665f 	cmnvs	ip, pc, asr r6
      9c:	65720067 	ldrbvs	r0, [r2, #-103]!	; 0xffffff99
      a0:	64726f63 	ldrbtvs	r6, [r2], #-3939	; 0xfffff09d
      a4:	5f676e69 	svcpl	0x00676e69
      a8:	00746e63 	rsbseq	r6, r4, r3, ror #28
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
     10c:	4b5f4d55 	blmi	17d3668 <ringBuffer+0x177b990>
     110:	00535945 	subseq	r5, r3, r5, asr #18
     114:	6f424c6d 	svcvs	0x00424c6d
     118:	5373756c 	cmnpl	r3, #108, 10	; 0x1b000000
     11c:	73706574 	cmnvc	r0, #116, 10	; 0x1d000000
     120:	676e654c 	strbvs	r6, [lr, -ip, asr #10]!
     124:	6d006874 	stcvs	8, cr6, [r0, #-464]	; 0xfffffe30
     128:	6c6f424c 	sfmvs	f4, 2, [pc], #-304	; 0 <pthread_mutex_unlock@plt-0x10930>
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
     164:	6c6f424c 	sfmvs	f4, 2, [pc], #-304	; 3c <pthread_mutex_unlock@plt-0x108f4>
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
     25c:	4b005448 	blmi	15384 <.DATA_REGION_0__data_end+0x48b8>
     260:	555f5945 	ldrbpl	r5, [pc, #-2373]	; fffff923 <__bss_end__+0xf671134f>
     264:	454b0050 	strbmi	r0, [fp, #-80]	; 0xffffffb0
     268:	4f445f59 	svcmi	0x00445f59
     26c:	4b004e57 	blmi	13bd0 <.DATA_REGION_0__data_end+0x3104>
     270:	4c5f5945 	mrrcmi	9, 4, r5, pc, cr5	; <UNPREDICTABLE>
     274:	00544645 	subseq	r4, r4, r5, asr #12
     278:	5f59454b 	svcpl	0x0059454b
     27c:	454c4553 	strbmi	r4, [ip, #-1363]	; 0xfffffaad
     280:	4b005443 	blmi	15394 <.DATA_REGION_0__data_end+0x48c8>
     284:	4e5f5945 	vnmlami.f16	s11, s30, s10	; <UNPREDICTABLE>
     288:	00454e4f 	subeq	r4, r5, pc, asr #28
     28c:	4e49414d 	dvfmiem	f4, f1, #5.0
     290:	4c4f4200 	sfmmi	f4, 2, [pc], {-0}
     294:	4d5f5355 	ldclmi	3, cr5, [pc, #-340]	; 148 <pthread_mutex_unlock@plt-0x107e8>
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
     2e0:	6b636568 	blvs	18d9888 <ringBuffer+0x1881bb0>
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
     484:	4b736968 	blmi	1cdaa2c <ringBuffer+0x1c82d54>
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
     4d0:	755f7674 	ldrbvc	r7, [pc, #-1652]	; fffffe64 <__bss_end__+0xf6711890>
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
     530:	7a697300 	bvc	1a5d138 <ringBuffer+0x1a05460>
     534:	00745f65 	rsbseq	r5, r4, r5, ror #30
     538:	6f68735f 	svcvs	0x0068735f
     53c:	75627472 	strbvc	r7, [r2, #-1138]!	; 0xfffffb8e
     540:	65730066 	ldrbvs	r0, [r3, #-102]!	; 0xffffff9a
     544:	65727563 	ldrbvs	r7, [r2, #-1379]!	; 0xfffffa9d
     548:	72657a5f 	rsbvc	r7, r5, #389120	; 0x5f000
     54c:	656d5f6f 	strbvs	r5, [sp, #-3951]!	; 0xfffff091
     550:	79726f6d 	ldmdbvc	r2!, {r0, r2, r3, r5, r6, r8, r9, sl, fp, sp, lr}^
     554:	746f7200 	strbtvc	r7, [pc], #-512	; 55c <pthread_mutex_unlock@plt-0x103d4>
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
     590:	6b616c62 	blvs	185b720 <ringBuffer+0x1803a48>
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
     5d8:	6b636f6c 	blvs	18dc390 <ringBuffer+0x18846b8>
     5dc:	616c6200 	cmnvs	ip, r0, lsl #4
     5e0:	6232656b 	eorsvs	r6, r2, #448790528	; 0x1ac00000
     5e4:	6e6f635f 	mcrvs	3, 3, r6, cr15, cr15, {2}
     5e8:	6e617473 	mcrvs	4, 3, r7, cr1, cr3, {3}
     5ec:	665f0074 			; <UNDEFINED> instruction: 0x665f0074
     5f0:	6e656c69 	cdpvs	12, 6, cr6, cr5, cr9, {3}
     5f4:	495f006f 	ldmdbmi	pc, {r0, r1, r2, r3, r5, r6}^	; <UNPREDICTABLE>
     5f8:	65725f4f 	ldrbvs	r5, [r2, #-3919]!	; 0xfffff0b1
     5fc:	655f6461 	ldrbvs	r6, [pc, #-1121]	; 1a3 <pthread_mutex_unlock@plt-0x1078d>
     600:	5f00646e 	svcpl	0x0000646e
     604:	6175715f 	cmnvs	r5, pc, asr r1
     608:	00745f64 	rsbseq	r5, r4, r4, ror #30
     60c:	6b616c62 	blvs	185b79c <ringBuffer+0x1803ac4>
     610:	5f733265 	svcpl	0x00733265
     614:	6c5f7369 	mrrcvs	3, 6, r7, pc, cr9	; <UNPREDICTABLE>
     618:	62747361 	rsbsvs	r7, r4, #-2080374783	; 0x84000001
     61c:	6b636f6c 	blvs	18dc3d4 <ringBuffer+0x18846fc>
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
     67c:	6b616c62 	blvs	185b80c <ringBuffer+0x1803b34>
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
     6c4:	6b5f7469 	blvs	17dd870 <ringBuffer+0x1785b98>
     6c8:	6d007965 	vstrvs.16	s14, [r0, #-202]	; 0xffffff36	; <UNPREDICTABLE>
     6cc:	65736d65 	ldrbvs	r6, [r3, #-3429]!	; 0xfffff29b
     6d0:	00765f74 	rsbseq	r5, r6, r4, ror pc
     6d4:	5f4f495f 	svcpl	0x004f495f
     6d8:	6b72616d 	blvs	1c98c94 <ringBuffer+0x1c40fbc>
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
     704:	6b736544 	blvs	1cd9c1c <ringBuffer+0x1c81f44>
     708:	2f706f74 	svccs	0x00706f74
     70c:	4b414c42 	blmi	105381c <ringBuffer+0xffbb44>
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
     7f0:	645f6564 	ldrbvs	r6, [pc], #-1380	; 7f8 <pthread_mutex_unlock@plt-0x10138>
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
     92c:	6b616c62 	blvs	185babc <ringBuffer+0x1803de4>
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
     9a4:	4b5f4232 	blmi	17d1274 <ringBuffer+0x177959c>
     9a8:	59425945 	stmdbpl	r2, {r0, r2, r6, r8, fp, ip, lr}^
     9ac:	00534554 	subseq	r4, r3, r4, asr r5
     9b0:	6b616c62 	blvs	185bb40 <ringBuffer+0x1803e68>
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
     9e4:	4b414c42 	blmi	1053af4 <ringBuffer+0xffbe1c>
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
     ae4:	6d6f7461 	cfstrdvs	mvd7, [pc, #-388]!	; 968 <pthread_mutex_unlock@plt-0xffc8>
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
     b84:	745f7463 	ldrbvc	r7, [pc], #-1123	; b8c <pthread_mutex_unlock@plt-0xfda4>
     b88:	725f6673 	subsvc	r6, pc, #120586240	; 0x7300000
     b8c:	726f6365 	rsbvc	r6, pc, #-1811939327	; 0x94000001
     b90:	676e6964 	strbvs	r6, [lr, -r4, ror #18]!
     b94:	42736900 	rsbsmi	r6, r3, #0, 18
     b98:	636e6172 	cmnvs	lr, #-2147483620	; 0x8000001c
     b9c:	6b615468 	blvs	1855d44 <ringBuffer+0x17fe06c>
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
     c2c:	6d6f7461 	cfstrdvs	mvd7, [pc, #-388]!	; ab0 <pthread_mutex_unlock@plt-0xfe80>
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
     cac:	745f6300 	ldrbvc	r6, [pc], #-768	; cb4 <pthread_mutex_unlock@plt-0xfc7c>
     cb0:	705f6673 	subsvc	r6, pc, r3, ror r6	; <UNPREDICTABLE>
     cb4:	705f706f 	subsvc	r7, pc, pc, rrx
     cb8:	65725f63 	ldrbvs	r5, [r2, #-3939]!	; 0xfffff09d
     cbc:	64726f63 	ldrbtvs	r6, [r2], #-3939	; 0xfffff09d
     cc0:	00676e69 	rsbeq	r6, r7, r9, ror #28
     cc4:	6e695f63 	cdpvs	15, 6, cr5, cr9, cr3, {3}
     cc8:	65726964 	ldrbvs	r6, [r2, #-2404]!	; 0xfffff69c
     ccc:	745f7463 	ldrbvc	r7, [pc], #-1123	; cd4 <pthread_mutex_unlock@plt-0xfc5c>
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
     d44:	6c6f706d 	stclvs	0, cr7, [pc], #-436	; b98 <pthread_mutex_unlock@plt-0xfd98>
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
     d74:	6d6f7461 	cfstrdvs	mvd7, [pc, #-388]!	; bf8 <pthread_mutex_unlock@plt-0xfd38>
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
     da4:	645f6300 	ldrbvs	r6, [pc], #-768	; dac <pthread_mutex_unlock@plt-0xfb84>
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
     e78:	745f6863 	ldrbvc	r6, [pc], #-2147	; e80 <pthread_mutex_unlock@plt-0xfab0>
     e7c:	64725f6f 	ldrbtvs	r5, [r2], #-3951	; 0xfffff091
     e80:	646e615f 	strbtvs	r6, [lr], #-351	; 0xfffffea1
     e84:	676f6c5f 			; <UNDEFINED> instruction: 0x676f6c5f
     e88:	72617000 	rsbvc	r7, r1, #0
     e8c:	79546d61 	ldmdbvc	r4, {r0, r5, r6, r8, sl, fp, sp, lr}^
     e90:	00736570 	rsbseq	r6, r3, r0, ror r5
     e94:	65726170 	ldrbvs	r6, [r2, #-368]!	; 0xfffffe90
     e98:	6100746e 	tstvs	r0, lr, ror #8
     e9c:	79617272 	stmdbvc	r1!, {r1, r4, r5, r6, r9, ip, sp, lr}^
     ea0:	7a69735f 	bvc	1a5dc24 <ringBuffer+0x1a05f4c>
     ea4:	65730065 	ldrbvs	r0, [r3, #-101]!	; 0xffffff9b
     ea8:	2e007373 	mcrcs	3, 0, r7, cr0, cr3, {3}
     eac:	2e2e2f2e 	cdpcs	15, 2, cr2, cr14, cr14, {1}
     eb0:	6172742f 	cmnvs	r2, pc, lsr #8
     eb4:	6c6f706d 	stclvs	0, cr7, [pc], #-436	; d08 <pthread_mutex_unlock@plt-0xfc28>
     eb8:	5f656e69 	svcpl	0x00656e69
     ebc:	2f62696c 	svccs	0x0062696c
     ec0:	745f6174 	ldrbvc	r6, [pc], #-372	; ec8 <pthread_mutex_unlock@plt-0xfa68>
     ec4:	706d6172 	rsbvc	r6, sp, r2, ror r1
     ec8:	6e696c6f 	cdpvs	12, 6, cr6, cr9, cr15, {3}
     ecc:	00632e65 	rsbeq	r2, r3, r5, ror #28
     ed0:	43454554 	movtmi	r4, #21844	; 0x5554
     ed4:	4955555f 	ldmdbmi	r5, {r0, r1, r2, r3, r4, r6, r8, sl, ip, lr}^
     ed8:	72650044 	rsbvc	r0, r5, #68	; 0x44
     edc:	726f5f72 	rsbvc	r5, pc, #456	; 0x1c8
     ee0:	6e696769 	cdpvs	7, 6, cr6, cr9, cr9, {3}
     ee4:	72726100 	rsbsvc	r6, r2, #0, 2
     ee8:	72007961 	andvc	r7, r0, #1589248	; 0x184000
     eec:	706f5f64 	rsbvc	r5, pc, r4, ror #30
     ef0:	5f656574 	svcpl	0x00656574
     ef4:	74696e69 	strbtvc	r6, [r9], #-3689	; 0xfffff197
     ef8:	6d756e00 	ldclvs	14, cr6, [r5, #-0]
     efc:	00726562 	rsbseq	r6, r2, r2, ror #10
     f00:	6174706f 	cmnvs	r4, pc, rrx
     f04:	77006772 	smlsdxvc	r0, r2, r7, r6
     f08:	65746972 	ldrbvs	r6, [r4, #-2418]!	; 0xfffff68e
     f0c:	7272615f 	rsbsvc	r6, r2, #-1073741801	; 0xc0000017
     f10:	745f7961 	ldrbvc	r7, [pc], #-2401	; f18 <pthread_mutex_unlock@plt-0xfa18>
     f14:	69665f6f 	stmdbvs	r6!, {r0, r1, r2, r3, r5, r6, r8, r9, sl, fp, ip, lr}^
     f18:	5f00656c 	svcpl	0x0000656c
     f1c:	6572665f 	ldrbvs	r6, [r2, #-1631]!	; 0xfffff9a1
     f20:	6f685f65 	svcvs	0x00685f65
     f24:	63006b6f 	movwvs	r6, #2927	; 0xb6f
     f28:	74616572 	strbtvc	r6, [r1], #-1394	; 0xfffffa8e
     f2c:	69665f65 	stmdbvs	r6!, {r0, r2, r5, r6, r8, r9, sl, fp, ip, lr}^
     f30:	0073656c 	rsbseq	r6, r3, ip, ror #10
     f34:	74736564 	ldrbtvc	r6, [r3], #-1380	; 0xfffffa9c
     f38:	74616e69 	strbtvc	r6, [r1], #-3689	; 0xfffff197
     f3c:	006e6f69 	rsbeq	r6, lr, r9, ror #30
     f40:	43454554 	movtmi	r4, #21844	; 0x5554
     f44:	6c61565f 	stclvs	6, cr5, [r1], #-380	; 0xfffffe84
     f48:	5f006575 	svcpl	0x00006575
     f4c:	6673745f 			; <UNDEFINED> instruction: 0x6673745f
     f50:	6365725f 	cmnvs	r5, #-268435451	; 0xf0000005
     f54:	6964726f 	stmdbvs	r4!, {r0, r1, r2, r3, r5, r6, r9, ip, sp, lr}^
     f58:	7200676e 	andvc	r6, r0, #28835840	; 0x1b80000
     f5c:	73696765 	cmnvc	r9, #26476544	; 0x1940000
     f60:	65726574 	ldrbvs	r6, [r2, #-1396]!	; 0xfffffa8c
     f64:	64665f64 	strbtvs	r5, [r6], #-3940	; 0xfffff09c
     f68:	69727700 	ldmdbvs	r2!, {r8, r9, sl, ip, sp, lr}^
     f6c:	745f6574 	ldrbvc	r6, [pc], #-1396	; f74 <pthread_mutex_unlock@plt-0xf9bc>
     f70:	6e5f6f77 	mrcvs	15, 2, r6, cr15, cr7, {3}
     f74:	65626d75 	strbvs	r6, [r2, #-3445]!	; 0xfffff28b
     f78:	745f7372 	ldrbvc	r7, [pc], #-882	; f80 <pthread_mutex_unlock@plt-0xf9b0>
     f7c:	69665f6f 	stmdbvs	r6!, {r0, r1, r2, r3, r5, r6, r8, r9, sl, fp, ip, lr}^
     f80:	5400656c 	strpl	r6, [r0], #-1388	; 0xfffffa94
     f84:	5f434545 	svcpl	0x00434545
     f88:	7265704f 	rsbvc	r7, r5, #79	; 0x4f
     f8c:	6f697461 	svcvs	0x00697461
     f90:	6e69006e 	cdpvs	0, 6, cr0, cr9, cr14, {3}
     f94:	656b6f76 	strbvs	r6, [fp, #-3958]!	; 0xfffff08a
     f98:	746e635f 	strbtvc	r6, [lr], #-863	; 0xfffffca1
     f9c:	69727700 	ldmdbvs	r2!, {r8, r9, sl, ip, sp, lr}^
     fa0:	6e5f6574 	mrcvs	5, 2, r6, cr15, cr4, {3}
     fa4:	65626d75 	strbvs	r6, [r2, #-3445]!	; 0xfffff28b
     fa8:	6f745f72 	svcvs	0x00745f72
     fac:	6c69665f 	stclvs	6, cr6, [r9], #-380	; 0xfffffe84
     fb0:	65720065 	ldrbvs	r0, [r2, #-101]!	; 0xffffff9b
     fb4:	656d5f67 	strbvs	r5, [sp, #-3943]!	; 0xfffff099
     fb8:	7470006d 	ldrbtvc	r0, [r0], #-109	; 0xffffff93
     fbc:	66696472 			; <UNDEFINED> instruction: 0x66696472
     fc0:	00745f66 	rsbseq	r5, r4, r6, ror #30
     fc4:	66667562 	strbtvs	r7, [r6], -r2, ror #10
     fc8:	615f7265 	cmpvs	pc, r5, ror #4
     fcc:	636f6c6c 	cmnvs	pc, #108, 24	; 0x6c00
     fd0:	64657461 	strbtvs	r7, [r5], #-1121	; 0xfffffb9f
     fd4:	6d5f5f00 	ldclvs	15, cr5, [pc, #-0]	; fdc <pthread_mutex_unlock@plt-0xf954>
     fd8:	6f6c6c61 	svcvs	0x006c6c61
     fdc:	6f685f63 	svcvs	0x00685f63
     fe0:	66006b6f 	strvs	r6, [r0], -pc, ror #22
     fe4:	6e656c69 	cdpvs	12, 6, cr6, cr5, cr9, {3}
     fe8:	00656d61 	rsbeq	r6, r5, r1, ror #26
     fec:	6974706f 	ldmdbvs	r4!, {r0, r1, r2, r3, r5, r6, ip, sp, lr}^
     ff0:	7200646e 	andvc	r6, r0, #1845493760	; 0x6e000000
     ff4:	685f7465 	ldmdavs	pc, {r0, r2, r5, r6, sl, ip, sp, lr}^	; <UNPREDICTABLE>
     ff8:	5f687361 	svcpl	0x00687361
     ffc:	74696e69 	strbtvc	r6, [r9], #-3689	; 0xfffff197
    1000:	616c665f 	cmnvs	ip, pc, asr r6
    1004:	735f0067 	cmpvc	pc, #103	; 0x67
    1008:	735f7379 	cmpvc	pc, #-469762047	; 0xe4000001
    100c:	696c6769 	stmdbvs	ip!, {r0, r3, r5, r6, r8, r9, sl, sp, lr}^
    1010:	6e007473 	mcrvs	4, 0, r7, cr0, cr3, {3}
    1014:	65626d75 	strbvs	r6, [r2, #-3445]!	; 0xfffff28b
    1018:	6e003172 	mcrvs	1, 0, r3, cr0, cr2, {3}
    101c:	65626d75 	strbvs	r6, [r2, #-3445]!	; 0xfffff28b
    1020:	47003272 	smlsdxmi	r0, r2, r2, r3
    1024:	4320554e 			; <UNDEFINED> instruction: 0x4320554e
    1028:	36203131 			; <UNDEFINED> instruction: 0x36203131
    102c:	312e322e 			; <UNDEFINED> instruction: 0x312e322e
    1030:	31303220 	teqcc	r0, r0, lsr #4
    1034:	31303136 	teqcc	r0, r6, lsr r1
    1038:	6d2d2036 	stcvs	0, cr2, [sp, #-216]!	; 0xffffff28
    103c:	616f6c66 	cmnvs	pc, r6, ror #24
    1040:	62612d74 	rsbvs	r2, r1, #116, 26	; 0x1d00
    1044:	61683d69 	cmnvs	r8, r9, ror #26
    1048:	2d206472 	cfstrscs	mvf6, [r0, #-456]!	; 0xfffffe38
    104c:	6372616d 	cmnvs	r2, #1073741851	; 0x4000001b
    1050:	72613d68 	rsbvc	r3, r1, #104, 26	; 0x1a00
    1054:	2d37766d 	ldccs	6, cr7, [r7, #-436]!	; 0xfffffe4c
    1058:	6d2d2061 	stcvs	0, cr2, [sp, #-388]!	; 0xfffffe7c
    105c:	656e7574 	strbvs	r7, [lr, #-1396]!	; 0xfffffa8c
    1060:	726f633d 	rsbvc	r6, pc, #-201326592	; 0xf4000000
    1064:	2d786574 	cfldr64cs	mvdx6, [r8, #-464]!	; 0xfffffe30
    1068:	2d203961 			; <UNDEFINED> instruction: 0x2d203961
    106c:	7570666d 	ldrbvc	r6, [r0, #-1645]!	; 0xfffff993
    1070:	7066763d 	rsbvc	r7, r6, sp, lsr r6
    1074:	642d3376 	strtvs	r3, [sp], #-886	; 0xfffffc8a
    1078:	2d203631 	stccs	6, cr3, [r0, #-196]!	; 0xffffff3c
    107c:	7568746d 	strbvc	r7, [r8, #-1133]!	; 0xfffffb93
    1080:	2d20626d 	sfmcs	f6, 4, [r0, #-436]!	; 0xfffffe4c
    1084:	736c746d 	cmnvc	ip, #1828716544	; 0x6d000000
    1088:	6169642d 	cmnvs	r9, sp, lsr #8
    108c:	7463656c 	strbtvc	r6, [r3], #-1388	; 0xfffffa94
    1090:	756e673d 	strbvc	r6, [lr, #-1853]!	; 0xfffff8c3
    1094:	20672d20 	rsbcs	r2, r7, r0, lsr #26
    1098:	7764672d 	strbvc	r6, [r4, -sp, lsr #14]!
    109c:	2d667261 	sfmcs	f7, 2, [r6, #-388]!	; 0xfffffe7c
    10a0:	4f2d2035 	svcmi	0x002d2035
    10a4:	662d2030 			; <UNDEFINED> instruction: 0x662d2030
    10a8:	00434950 	subeq	r4, r3, r0, asr r9
    10ac:	73736573 	cmnvc	r3, #482344960	; 0x1cc00000
    10b0:	006e6f69 	rsbeq	r6, lr, r9, ror #30
    10b4:	6e655f5f 	mcrvs	15, 3, r5, cr5, cr15, {2}
    10b8:	6f726976 	svcvs	0x00726976
    10bc:	6572006e 	ldrbvs	r0, [r2, #-110]!	; 0xffffff92
    10c0:	6d5f6461 	cfldrdvs	mvd6, [pc, #-388]	; f44 <pthread_mutex_unlock@plt-0xf9ec>
    10c4:	75736165 	ldrbvc	r6, [r3, #-357]!	; 0xfffffe9b
    10c8:	656d6572 	strbvs	r6, [sp, #-1394]!	; 0xfffffa8e
    10cc:	5400746e 	strpl	r7, [r0], #-1134	; 0xfffffb92
    10d0:	5f434545 	svcpl	0x00434545
    10d4:	72616853 	rsbvc	r6, r1, #5439488	; 0x530000
    10d8:	654d6465 	strbvs	r6, [sp, #-1125]	; 0xfffffb9b
    10dc:	79726f6d 	ldmdbvc	r2!, {r0, r2, r3, r5, r6, r8, r9, sl, fp, sp, lr}^
    10e0:	45455400 	strbmi	r5, [r5, #-1024]	; 0xfffffc00
    10e4:	61505f43 	cmpvs	r0, r3, asr #30
    10e8:	656d6172 	strbvs	r6, [sp, #-370]!	; 0xfffffe8e
    10ec:	00726574 	rsbseq	r6, r2, r4, ror r5
    10f0:	6f6c6c61 	svcvs	0x006c6c61
    10f4:	5f646563 	svcpl	0x00646563
    10f8:	657a6973 	ldrbvs	r6, [sl, #-2419]!	; 0xfffff68d
    10fc:	756f7300 	strbvc	r7, [pc, #-768]!	; e04 <pthread_mutex_unlock@plt-0xfb2c>
    1100:	5f656372 	svcpl	0x00656372
    1104:	00747063 	rsbseq	r7, r4, r3, rrx
    1108:	70706f70 	rsbsvc	r6, r0, r0, ror pc
    110c:	6c456465 	cfstrdvs	mvd6, [r5], {101}	; 0x65
    1110:	64006d65 	strvs	r6, [r0], #-3429	; 0xfffff29b
    1114:	5f747365 	svcpl	0x00747365
    1118:	00747063 	rsbseq	r7, r4, r3, rrx
    111c:	656d5f5f 	strbvs	r5, [sp, #-3935]!	; 0xfffff0a1
    1120:	696c616d 	stmdbvs	ip!, {r0, r2, r3, r5, r6, r8, sp, lr}^
    1124:	685f6e67 	ldmdavs	pc, {r0, r1, r2, r5, r6, r9, sl, fp, sp, lr}^	; <UNPREDICTABLE>
    1128:	006b6f6f 	rsbeq	r6, fp, pc, ror #30
    112c:	646e6f63 	strbtvs	r6, [lr], #-3939	; 0xfffff09d
    1130:	6f697469 	svcvs	0x00697469
    1134:	5f5f006e 	svcpl	0x005f006e
    1138:	6c616572 	cfstr64vs	mvdx6, [r1], #-456	; 0xfffffe38
    113c:	5f636f6c 	svcpl	0x00636f6c
    1140:	6b6f6f68 	blvs	1bdcee8 <ringBuffer+0x1b85210>
    1144:	635f5f00 	cmpvs	pc, #0, 30
    1148:	69646e6f 	stmdbvs	r4!, {r0, r1, r2, r3, r5, r6, r9, sl, fp, sp, lr}^
    114c:	6e6f6974 			; <UNDEFINED> instruction: 0x6e6f6974
    1150:	625f6c61 	subsvs	r6, pc, #24832	; 0x6100
    1154:	636e6172 	cmnvs	lr, #-2147483620	; 0x8000001c
    1158:	65725f68 	ldrbvs	r5, [r2, #-3944]!	; 0xfffff098
    115c:	64726f63 	ldrbtvs	r6, [r2], #-3939	; 0xfffff09d
    1160:	00676e69 	rsbeq	r6, r7, r9, ror #28
    1164:	61645f5f 	cmnvs	r4, pc, asr pc
    1168:	67696c79 			; <UNDEFINED> instruction: 0x67696c79
    116c:	6f007468 	svcvs	0x00007468
    1170:	706f7470 	rsbvc	r7, pc, r0, ror r4	; <UNPREDICTABLE>
    1174:	756e0074 	strbvc	r0, [lr, #-116]!	; 0xffffff8c
    1178:	7265626d 	rsbvc	r6, r5, #-805306362	; 0xd0000006
    117c:	7274735f 	rsbsvc	r7, r4, #2080374785	; 0x7c000001
    1180:	65666300 	strbvs	r6, [r6, #-768]!	; 0xfffffd00
    1184:	7079745f 	rsbsvc	r7, r9, pc, asr r4
    1188:	75750065 	ldrbvc	r0, [r5, #-101]!	; 0xffffff9b
    118c:	5f006469 	svcpl	0x00006469
    1190:	7466615f 	strbtvc	r6, [r6], #-351	; 0xfffffea1
    1194:	6d5f7265 	lfmvs	f7, 2, [pc, #-404]	; 1008 <pthread_mutex_unlock@plt-0xf928>
    1198:	6365726f 	cmnvs	r5, #-268435450	; 0xf0000006
    119c:	5f65726f 	svcpl	0x0065726f
    11a0:	6b6f6f68 	blvs	1bdcf48 <ringBuffer+0x1b85270>
    11a4:	72617000 	rsbvc	r7, r1, #0
    11a8:	00736d61 	rsbseq	r6, r3, r1, ror #26
    11ac:	43454554 	movtmi	r4, #21844	; 0x5554
    11b0:	7365535f 	cmnvc	r5, #2080374785	; 0x7c000001
    11b4:	6e6f6973 			; <UNDEFINED> instruction: 0x6e6f6973
    11b8:	6d5f5f00 	ldclvs	15, cr5, [pc, #-0]	; 11c0 <pthread_mutex_unlock@plt-0xf770>
    11bc:	6365726f 	cmnvs	r5, #-268435450	; 0xf0000006
    11c0:	0065726f 	rsbeq	r7, r5, pc, ror #4
    11c4:	65745f5f 	ldrbvs	r5, [r4, #-3935]!	; 0xfffff0a1
    11c8:	6f007473 	svcvs	0x00007473
    11cc:	72657470 	rsbvc	r7, r5, #112, 8	; 0x70000000
    11d0:	68730072 	ldmdavs	r3!, {r1, r4, r5, r6}^
    11d4:	776f6461 	strbvc	r6, [pc, -r1, ror #8]!
    11d8:	6675625f 			; <UNDEFINED> instruction: 0x6675625f
    11dc:	00726566 	rsbseq	r6, r2, r6, ror #10
    11e0:	656c6966 	strbvs	r6, [ip, #-2406]!	; 0xfffff69a
    11e4:	656d616e 	strbvs	r6, [sp, #-366]!	; 0xfffffe92
    11e8:	69660031 	stmdbvs	r6!, {r0, r4, r5}^
    11ec:	616e656c 	cmnvs	lr, ip, ror #10
    11f0:	0033656d 	eorseq	r6, r3, sp, ror #10
    11f4:	656c6966 	strbvs	r6, [ip, #-2406]!	; 0xfffff69a
    11f8:	656d616e 	strbvs	r6, [sp, #-366]!	; 0xfffffe92
    11fc:	69660034 	stmdbvs	r6!, {r2, r4, r5}^
    1200:	616e656c 	cmnvs	lr, ip, ror #10
    1204:	0035656d 	eorseq	r6, r5, sp, ror #10
    1208:	43454554 	movtmi	r4, #21844	; 0x5554
    120c:	6d65545f 	cfstrdvs	mvd5, [r5, #-380]!	; 0xfffffe84
    1210:	6d654d70 	stclvs	13, cr4, [r5, #-448]!	; 0xfffffe40
    1214:	5279726f 	rsbspl	r7, r9, #-268435450	; 0xf0000006
    1218:	72656665 	rsbvc	r6, r5, #105906176	; 0x6500000
    121c:	65636e65 	strbvs	r6, [r3, #-3685]!	; 0xfffff19b
    1220:	6d697400 	cfstrdvs	mvd7, [r9, #-0]
    1224:	64694d65 	strbtvs	r4, [r9], #-3429	; 0xfffff29b
    1228:	6d697400 	cfstrdvs	mvd7, [r9, #-0]
    122c:	776f4c65 	strbvc	r4, [pc, -r5, ror #24]!
    1230:	45455400 	strbmi	r5, [r5, #-1024]	; 0xfffffc00
    1234:	65525f43 	ldrbvs	r5, [r2, #-3907]	; 0xfffff0bd
    1238:	74736967 	ldrbtvc	r6, [r3], #-2407	; 0xfffff699
    123c:	64657265 	strbtvs	r7, [r5], #-613	; 0xfffffd9b
    1240:	6f6d654d 	svcvs	0x006d654d
    1244:	65527972 	ldrbvs	r7, [r2, #-2418]	; 0xfffff68e
    1248:	65726566 	ldrbvs	r6, [r2, #-1382]!	; 0xfffffa9a
    124c:	0065636e 	rsbeq	r6, r5, lr, ror #6
    1250:	616d5f5f 	cmnvs	sp, pc, asr pc
    1254:	636f6c6c 	cmnvs	pc, #108, 24	; 0x6c00
    1258:	696e695f 	stmdbvs	lr!, {r0, r1, r2, r3, r4, r6, r8, fp, sp, lr}^
    125c:	6c616974 			; <UNDEFINED> instruction: 0x6c616974
    1260:	5f657a69 	svcpl	0x00657a69
    1264:	6b6f6f68 	blvs	1bdd00c <ringBuffer+0x1b85334>
    1268:	6c696600 	stclvs	6, cr6, [r9], #-0
    126c:	6d616e65 	stclvs	14, cr6, [r1, #-404]!	; 0xfffffe6c
    1270:	74007365 	strvc	r7, [r0], #-869	; 0xfffffc9b
    1274:	6572706d 	ldrbvs	r7, [r2, #-109]!	; 0xffffff93
    1278:	5f5f0066 	svcpl	0x005f0066
    127c:	616e7a74 	smcvs	59300	; 0xe7a4
    1280:	5400656d 	strpl	r6, [r0], #-1389	; 0xfffffa93
    1284:	5f434545 	svcpl	0x00434545
    1288:	75736552 	ldrbvc	r6, [r3, #-1362]!	; 0xfffffaae
    128c:	地址 0x000000000000128c 越界。


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
  90:	745f5f00 	ldrbvc	r5, [pc], #-3840	; 98 <pthread_mutex_unlock@plt-0x10898>
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
   0:	00020310 	andeq	r0, r2, r0, lsl r3
   4:	00020314 	andeq	r0, r2, r4, lsl r3
   8:	00020324 	andeq	r0, r2, r4, lsr #6
   c:	00020398 	muleq	r2, r8, r3
	...
  18:	00040318 	andeq	r0, r4, r8, lsl r3
  1c:	00040344 	andeq	r0, r4, r4, asr #6
  20:	00040350 	andeq	r0, r4, r0, asr r3
  24:	0004036c 	andeq	r0, r4, ip, ror #6
	...
  30:	00040000 	andeq	r0, r4, r0
  34:	000401d0 	ldrdeq	r0, [r4], -r0	; <UNPREDICTABLE>
  38:	00020000 	andeq	r0, r2, r0
  3c:	000205ac 	andeq	r0, r2, ip, lsr #11
  40:	000401d0 	ldrdeq	r0, [r4], -r0	; <UNPREDICTABLE>
  44:	0004080c 	andeq	r0, r4, ip, lsl #16
	...
  50:	0004080c 	andeq	r0, r4, ip, lsl #16
  54:	0004088c 	andeq	r0, r4, ip, lsl #17
  58:	000205ac 	andeq	r0, r2, ip, lsr #11
  5c:	000205d0 	ldrdeq	r0, [r2], -r0	; <UNPREDICTABLE>
  60:	0004088c 	andeq	r0, r4, ip, lsl #17
  64:	0004092c 	andeq	r0, r4, ip, lsr #18
  68:	000205d0 	ldrdeq	r0, [r2], -r0	; <UNPREDICTABLE>
  6c:	00020618 	andeq	r0, r2, r8, lsl r6
  70:	0004092c 	andeq	r0, r4, ip, lsr #18
  74:	000409d8 	ldrdeq	r0, [r4], -r8
  78:	00020618 	andeq	r0, r2, r8, lsl r6
  7c:	00020674 	andeq	r0, r2, r4, ror r6
	...
  88:	000409d8 	ldrdeq	r0, [r4], -r8
  8c:	00040a30 	andeq	r0, r4, r0, lsr sl
  90:	000206e0 	andeq	r0, r2, r0, ror #13
  94:	000207b4 			; <UNDEFINED> instruction: 0x000207b4
	...
