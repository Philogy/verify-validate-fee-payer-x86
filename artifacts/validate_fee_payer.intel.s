

Disassembly of section .text.validate_fee_payer:

00000000027f3560 <validate_fee_payer>:
 27f3560: 55                           	push	rbp
 27f3561: 41 57                        	push	r15
 27f3563: 41 56                        	push	r14
 27f3565: 41 54                        	push	r12
 27f3567: 53                           	push	rbx
 27f3568: 48 83 ec 10                  	sub	rsp, 0x10
 27f356c: 48 89 f0                     	mov	rax, rsi
 27f356f: 48 8b 76 08                  	mov	rsi, qword ptr [rsi + 0x8]
 27f3573: 48 85 f6                     	test	rsi, rsi
 27f3576: 74 4b                        	je	0x27f35c3 <validate_fee_payer+0x63>
 27f3578: f3 0f 6f 05 e0 da af fd      	movdqu	xmm0, xmmword ptr [rip - 0x2502520] # 0x2f1060 <system_program_id>
 27f3580: f3 0f 6f 48 10               	movdqu	xmm1, xmmword ptr [rax + 0x10]
 27f3585: 66 0f ef c8                  	pxor	xmm1, xmm0
 27f3589: f3 0f 6f 40 20               	movdqu	xmm0, xmmword ptr [rax + 0x20]
 27f358e: f3 0f 6f 15 da da af fd      	movdqu	xmm2, xmmword ptr [rip - 0x2502526] # 0x2f1070 <system_program_id+0x10>
 27f3596: 66 0f ef d0                  	pxor	xmm2, xmm0
 27f359a: 66 0f eb d1                  	por	xmm2, xmm1
 27f359e: 66 0f 38 17 d2               	ptest	xmm2, xmm2
 27f35a3: 74 4a                        	je	0x27f35ef <validate_fee_payer+0x8f>
 27f35a5: 48 8b 41 58                  	mov	rax, qword ptr [rcx + 0x58]
 27f35a9: 48 ff c0                     	inc	rax
 27f35ac: 48 c7 c2 ff ff ff ff         	mov	rdx, -0x1
 27f35b3: 48 0f 45 d0                  	cmovne	rdx, rax
 27f35b7: 48 89 51 58                  	mov	qword ptr [rcx + 0x58], rdx
 27f35bb: c7 07 3c 00 00 00            	mov	dword ptr [rdi], 0x3c
 27f35c1: eb 1c                        	jmp	0x27f35df <validate_fee_payer+0x7f>
 27f35c3: 48 8b 41 20                  	mov	rax, qword ptr [rcx + 0x20]
 27f35c7: 48 ff c0                     	inc	rax
 27f35ca: 48 c7 c2 ff ff ff ff         	mov	rdx, -0x1
 27f35d1: 48 0f 45 d0                  	cmovne	rdx, rax
 27f35d5: 48 89 51 20                  	mov	qword ptr [rcx + 0x20], rdx
 27f35d9: c7 07 39 00 00 00            	mov	dword ptr [rdi], 0x39
 27f35df: 48 89 f8                     	mov	rax, rdi
 27f35e2: 48 83 c4 10                  	add	rsp, 0x10
 27f35e6: 5b                           	pop	rbx
 27f35e7: 41 5c                        	pop	r12
 27f35e9: 41 5e                        	pop	r14
 27f35eb: 41 5f                        	pop	r15
 27f35ed: 5d                           	pop	rbp
 27f35ee: c3                           	ret
 27f35ef: 48 8b 18                     	mov	rbx, qword ptr [rax]
 27f35f2: 4c 8b 53 20                  	mov	r10, qword ptr [rbx + 0x20]
 27f35f6: 4d 89 d3                     	mov	r11, r10
 27f35f9: 4d 85 d2                     	test	r10, r10
 27f35fc: 0f 84 0e 01 00 00            	je	0x27f3710 <validate_fee_payer+0x1b0>
 27f3602: 49 83 fa 50                  	cmp	r10, 0x50
 27f3606: 75 9d                        	jne	0x27f35a5 <validate_fee_payer+0x45>
 27f3608: 4c 8b 5b 18                  	mov	r11, qword ptr [rbx + 0x18]
 27f360c: 41 8b 1b                     	mov	ebx, dword ptr [r11]
 27f360f: 45 8b 5b 04                  	mov	r11d, dword ptr [r11 + 0x4]
 27f3613: 83 fb 01                     	cmp	ebx, 0x1
 27f3616: 74 04                        	je	0x27f361c <validate_fee_payer+0xbc>
 27f3618: 85 db                        	test	ebx, ebx
 27f361a: 75 89                        	jne	0x27f35a5 <validate_fee_payer+0x45>
 27f361c: 41 83 fb 01                  	cmp	r11d, 0x1
 27f3620: 75 83                        	jne	0x27f35a5 <validate_fee_payer+0x45>
 27f3622: 4d 8b 18                     	mov	r11, qword ptr [r8]
 27f3625: 49 8b 58 08                  	mov	rbx, qword ptr [r8 + 0x8]
 27f3629: 49 be 00 00 00 00 00 00 00 40	movabs	r14, 0x4000000000000000
 27f3633: 4c 39 f3                     	cmp	rbx, r14
 27f3636: 40 0f 94 c5                  	sete	bpl
 27f363a: 49 bf 45 f6 28 cc cc 00 00 00	movabs	r15, 0xcccc28f645
 27f3644: 4d 39 fb                     	cmp	r11, r15
 27f3647: 77 02                        	ja	0x27f364b <validate_fee_payer+0xeb>
 27f3649: 31 ed                        	xor	ebp, ebp
 27f364b: 40 84 ed                     	test	bpl, bpl
 27f364e: 0f 85 23 01 00 00            	jne	0x27f3777 <validate_fee_payer+0x217>
 27f3654: 49 bf 00 00 00 00 00 00 f0 3f	movabs	r15, 0x3ff0000000000000
 27f365e: 4c 39 fb                     	cmp	rbx, r15
 27f3661: 40 0f 94 c5                  	sete	bpl
 27f3665: 49 bc 8b ec 51 98 99 01 00 00	movabs	r12, 0x1999851ec8b
 27f366f: 4d 39 e3                     	cmp	r11, r12
 27f3672: 77 02                        	ja	0x27f3676 <validate_fee_payer+0x116>
 27f3674: 31 ed                        	xor	ebp, ebp
 27f3676: 40 84 ed                     	test	bpl, bpl
 27f3679: 0f 85 f8 00 00 00            	jne	0x27f3777 <validate_fee_payer+0x217>
 27f367f: 4c 39 f3                     	cmp	rbx, r14
 27f3682: 74 0e                        	je	0x27f3692 <validate_fee_payer+0x132>
 27f3684: 4c 39 fb                     	cmp	rbx, r15
 27f3687: 75 12                        	jne	0x27f369b <validate_fee_payer+0x13b>
 27f3689: 4d 69 db d0 00 00 00         	imul	r11, r11, 0xd0
 27f3690: eb 7e                        	jmp	0x27f3710 <validate_fee_payer+0x1b0>
 27f3692: 4d 69 db a0 01 00 00         	imul	r11, r11, 0x1a0
 27f3699: eb 75                        	jmp	0x27f3710 <validate_fee_payer+0x1b0>
 27f369b: 66 48 0f 6e c3               	movq	xmm0, rbx
 27f36a0: 4d 69 db d0 00 00 00         	imul	r11, r11, 0xd0
 27f36a7: 66 49 0f 6e cb               	movq	xmm1, r11
 27f36ac: 66 0f 62 0d 7c 38 af fd      	punpckldq	xmm1, xmmword ptr [rip - 0x250c784] # xmm1 = xmm1[0],mem[0],xmm1[1],mem[1]
                                                                        # 0x2e6f30 <u64_to_f64_exponents>
 27f36b4: 66 0f 5c 0d e4 22 af fd      	subpd	xmm1, xmmword ptr [rip - 0x250dd1c] # 0x2e59a0 <u64_to_f64_bias>
 27f36bc: 66 0f 28 d1                  	movapd	xmm2, xmm1
 27f36c0: 66 0f 15 d1                  	unpckhpd	xmm2, xmm1              # xmm2 = xmm2[1],xmm1[1]
 27f36c4: f2 0f 58 d1                  	addsd	xmm2, xmm1
 27f36c8: f2 0f 59 d0                  	mulsd	xmm2, xmm0
 27f36cc: f2 4c 0f 2c da               	cvttsd2si	r11, xmm2
 27f36d1: 4c 89 db                     	mov	rbx, r11
 27f36d4: 48 c1 fb 3f                  	sar	rbx, 0x3f
 27f36d8: 66 0f 28 c2                  	movapd	xmm0, xmm2
 27f36dc: f2 0f 5c 05 44 28 b0 fd      	subsd	xmm0, qword ptr [rip - 0x24fd7bc] # 0x2f5f28 <f64_2pow63>
 27f36e4: f2 4c 0f 2c f0               	cvttsd2si	r14, xmm0
 27f36e9: 49 21 de                     	and	r14, rbx
 27f36ec: 4d 09 de                     	or	r14, r11
 27f36ef: 31 db                        	xor	ebx, ebx
 27f36f1: 66 0f 57 c0                  	xorpd	xmm0, xmm0
 27f36f5: 66 0f 2e d0                  	ucomisd	xmm2, xmm0
 27f36f9: 49 0f 43 de                  	cmovae	rbx, r14
 27f36fd: 66 0f 2e 15 73 04 b0 fd      	ucomisd	xmm2, qword ptr [rip - 0x24ffb8d] # 0x2f3b78 <f64_max_below_2pow64>
 27f3705: 49 c7 c3 ff ff ff ff         	mov	r11, -0x1
 27f370c: 4c 0f 46 db                  	cmovbe	r11, rbx
 27f3710: 48 89 f3                     	mov	rbx, rsi
 27f3713: 4c 29 db                     	sub	rbx, r11
 27f3716: 41 0f 92 c3                  	setb	r11b
 27f371a: 4c 39 cb                     	cmp	rbx, r9
 27f371d: 0f 92 c3                     	setb	bl
 27f3720: 44 08 db                     	or	bl, r11b
 27f3723: 74 21                        	je	0x27f3746 <validate_fee_payer+0x1e6>
 27f3725: 48 8b 41 50                  	mov	rax, qword ptr [rcx + 0x50]
 27f3729: 48 ff c0                     	inc	rax
 27f372c: 48 c7 c2 ff ff ff ff         	mov	rdx, -0x1
 27f3733: 48 0f 45 d0                  	cmovne	rdx, rax
 27f3737: 48 89 51 50                  	mov	qword ptr [rcx + 0x50], rdx
 27f373b: c7 07 3b 00 00 00            	mov	dword ptr [rdi], 0x3b
 27f3741: e9 99 fe ff ff               	jmp	0x27f35df <validate_fee_payer+0x7f>
 27f3746: 44 0f b6 5c 24 40            	movzx	r11d, byte ptr [rsp + 0x40]
 27f374c: 48 89 f1                     	mov	rcx, rsi
 27f374f: 4c 29 c9                     	sub	rcx, r9
 27f3752: 48 89 48 08                  	mov	qword ptr [rax + 0x8], rcx
 27f3756: 41 0f b6 c3                  	movzx	eax, r11b
 27f375a: 89 04 24                     	mov	dword ptr [rsp], eax
 27f375d: 48 89 fb                     	mov	rbx, rdi
 27f3760: 41 89 d1                     	mov	r9d, edx
 27f3763: 48 89 ca                     	mov	rdx, rcx
 27f3766: 4c 89 d1                     	mov	rcx, r10
 27f3769: ff 15 b1 19 00 01            	call	qword ptr [rip + 0x10019b1] # 0x37f5120 <got_check_static_account_rent_state_transition>
 27f376f: 48 89 d8                     	mov	rax, rbx
 27f3772: e9 6b fe ff ff               	jmp	0x27f35e2 <validate_fee_payer+0x82>
 27f3777: 48 8d 3d 9e 95 e1 fd         	lea	rdi, [rip - 0x21e6a62]  # 0x60cd1c <panic_msg>
 27f377e: 48 8d 15 db 60 f6 00         	lea	rdx, [rip + 0xf660db]   # 0x3759860 <panic_location>
 27f3785: be 26 00 00 00               	mov	esi, 0x26
 27f378a: ff 15 e8 5b ff 00            	call	qword ptr [rip + 0xff5be8] # 0x37e9378 <got_expect_failed>

Disassembly of section .text.check_static_account_rent_state_transition:

00000000027f3790 <check_static_account_rent_state_transition>:
 27f3790: 41 56                        	push	r14
 27f3792: 53                           	push	rbx
 27f3793: 50                           	push	rax
 27f3794: 48 81 f9 00 00 a0 00         	cmp	rcx, 0xa00000
 27f379b: 0f 87 72 01 00 00            	ja	0x27f3913 <check_static_account_rent_state_transition+0x183>
 27f37a1: 49 8b 00                     	mov	rax, qword ptr [r8]
 27f37a4: 4d 8b 40 08                  	mov	r8, qword ptr [r8 + 0x8]
 27f37a8: 49 ba 00 00 00 00 00 00 00 40	movabs	r10, 0x4000000000000000
 27f37b2: 4d 39 d0                     	cmp	r8, r10
 27f37b5: 41 0f 94 c3                  	sete	r11b
 27f37b9: 48 bb 45 f6 28 cc cc 00 00 00	movabs	rbx, 0xcccc28f645
 27f37c3: 48 39 d8                     	cmp	rax, rbx
 27f37c6: 77 03                        	ja	0x27f37cb <check_static_account_rent_state_transition+0x3b>
 27f37c8: 45 31 db                     	xor	r11d, r11d
 27f37cb: 45 84 db                     	test	r11b, r11b
 27f37ce: 0f 85 3f 01 00 00            	jne	0x27f3913 <check_static_account_rent_state_transition+0x183>
 27f37d4: 49 bb 00 00 00 00 00 00 f0 3f	movabs	r11, 0x3ff0000000000000
 27f37de: 4d 39 d8                     	cmp	r8, r11
 27f37e1: 0f 94 c3                     	sete	bl
 27f37e4: 49 be 8b ec 51 98 99 01 00 00	movabs	r14, 0x1999851ec8b
 27f37ee: 4c 39 f0                     	cmp	rax, r14
 27f37f1: 77 02                        	ja	0x27f37f5 <check_static_account_rent_state_transition+0x65>
 27f37f3: 31 db                        	xor	ebx, ebx
 27f37f5: 84 db                        	test	bl, bl
 27f37f7: 0f 85 16 01 00 00            	jne	0x27f3913 <check_static_account_rent_state_transition+0x183>
 27f37fd: 4d 39 d0                     	cmp	r8, r10
 27f3800: 74 0b                        	je	0x27f380d <check_static_account_rent_state_transition+0x7d>
 27f3802: 4d 39 d8                     	cmp	r8, r11
 27f3805: 75 44                        	jne	0x27f384b <check_static_account_rent_state_transition+0xbb>
 27f3807: 48 83 e9 80                  	sub	rcx, -0x80
 27f380b: eb 08                        	jmp	0x27f3815 <check_static_account_rent_state_transition+0x85>
 27f380d: 48 8d 0c 4d 00 01 00 00      	lea	rcx, [2*rcx + 0x100]
 27f3815: 48 0f af c1                  	imul	rax, rcx
 27f3819: 44 0f b6 44 24 20            	movzx	r8d, byte ptr [rsp + 0x20]
 27f381f: 48 85 f6                     	test	rsi, rsi
 27f3822: 0f 84 a8 00 00 00            	je	0x27f38d0 <check_static_account_rent_state_transition+0x140>
 27f3828: 48 39 c6                     	cmp	rsi, rax
 27f382b: b9 02 00 00 00               	mov	ecx, 0x2
 27f3830: 48 83 d9 00                  	sbb	rcx, 0x0
 27f3834: 45 84 c0                     	test	r8b, r8b
 27f3837: 0f 84 b0 00 00 00            	je	0x27f38ed <check_static_account_rent_state_transition+0x15d>
 27f383d: 48 39 f2                     	cmp	rdx, rsi
 27f3840: 0f 82 8f 00 00 00            	jb	0x27f38d5 <check_static_account_rent_state_transition+0x145>
 27f3846: e9 b7 00 00 00               	jmp	0x27f3902 <check_static_account_rent_state_transition+0x172>
 27f384b: 66 49 0f 6e c0               	movq	xmm0, r8
 27f3850: 48 83 e9 80                  	sub	rcx, -0x80
 27f3854: 48 0f af c1                  	imul	rax, rcx
 27f3858: 66 48 0f 6e c8               	movq	xmm1, rax
 27f385d: 66 0f 62 0d cb 36 af fd      	punpckldq	xmm1, xmmword ptr [rip - 0x250c935] # xmm1 = xmm1[0],mem[0],xmm1[1],mem[1]
                                                                        # 0x2e6f30 <u64_to_f64_exponents>
 27f3865: 66 0f 5c 0d 33 21 af fd      	subpd	xmm1, xmmword ptr [rip - 0x250decd] # 0x2e59a0 <u64_to_f64_bias>
 27f386d: 66 0f 28 d1                  	movapd	xmm2, xmm1
 27f3871: 66 0f 15 d1                  	unpckhpd	xmm2, xmm1              # xmm2 = xmm2[1],xmm1[1]
 27f3875: f2 0f 58 d1                  	addsd	xmm2, xmm1
 27f3879: f2 0f 59 d0                  	mulsd	xmm2, xmm0
 27f387d: f2 48 0f 2c c2               	cvttsd2si	rax, xmm2
 27f3882: 48 89 c1                     	mov	rcx, rax
 27f3885: 48 c1 f9 3f                  	sar	rcx, 0x3f
 27f3889: 66 0f 28 c2                  	movapd	xmm0, xmm2
 27f388d: f2 0f 5c 05 93 26 b0 fd      	subsd	xmm0, qword ptr [rip - 0x24fd96d] # 0x2f5f28 <f64_2pow63>
 27f3895: f2 4c 0f 2c c0               	cvttsd2si	r8, xmm0
 27f389a: 49 21 c8                     	and	r8, rcx
 27f389d: 49 09 c0                     	or	r8, rax
 27f38a0: 31 c9                        	xor	ecx, ecx
 27f38a2: 66 0f 57 c0                  	xorpd	xmm0, xmm0
 27f38a6: 66 0f 2e d0                  	ucomisd	xmm2, xmm0
 27f38aa: 49 0f 43 c8                  	cmovae	rcx, r8
 27f38ae: 66 0f 2e 15 c2 02 b0 fd      	ucomisd	xmm2, qword ptr [rip - 0x24ffd3e] # 0x2f3b78 <f64_max_below_2pow64>
 27f38b6: 48 c7 c0 ff ff ff ff         	mov	rax, -0x1
 27f38bd: 48 0f 46 c1                  	cmovbe	rax, rcx
 27f38c1: 44 0f b6 44 24 20            	movzx	r8d, byte ptr [rsp + 0x20]
 27f38c7: 48 85 f6                     	test	rsi, rsi
 27f38ca: 0f 85 58 ff ff ff            	jne	0x27f3828 <check_static_account_rent_state_transition+0x98>
 27f38d0: 45 84 c0                     	test	r8b, r8b
 27f38d3: 74 16                        	je	0x27f38eb <check_static_account_rent_state_transition+0x15b>
 27f38d5: 48 85 d2                     	test	rdx, rdx
 27f38d8: 74 28                        	je	0x27f3902 <check_static_account_rent_state_transition+0x172>
 27f38da: 48 39 c2                     	cmp	rdx, rax
 27f38dd: 73 23                        	jae	0x27f3902 <check_static_account_rent_state_transition+0x172>
 27f38df: c7 07 56 00 00 00            	mov	dword ptr [rdi], 0x56
 27f38e5: 44 88 4f 04                  	mov	byte ptr [rdi + 0x4], r9b
 27f38e9: eb 1d                        	jmp	0x27f3908 <check_static_account_rent_state_transition+0x178>
 27f38eb: 31 c9                        	xor	ecx, ecx
 27f38ed: 48 85 d2                     	test	rdx, rdx
 27f38f0: 74 10                        	je	0x27f3902 <check_static_account_rent_state_transition+0x172>
 27f38f2: 48 39 c2                     	cmp	rdx, rax
 27f38f5: 73 0b                        	jae	0x27f3902 <check_static_account_rent_state_transition+0x172>
 27f38f7: 48 39 f2                     	cmp	rdx, rsi
 27f38fa: 77 e3                        	ja	0x27f38df <check_static_account_rent_state_transition+0x14f>
 27f38fc: 48 83 f9 01                  	cmp	rcx, 0x1
 27f3900: 75 dd                        	jne	0x27f38df <check_static_account_rent_state_transition+0x14f>
 27f3902: c7 07 ff ff ff ff            	mov	dword ptr [rdi], 0xffffffff
 27f3908: 48 89 f8                     	mov	rax, rdi
 27f390b: 48 83 c4 08                  	add	rsp, 0x8
 27f390f: 5b                           	pop	rbx
 27f3910: 41 5e                        	pop	r14
 27f3912: c3                           	ret
 27f3913: 48 8d 3d 02 94 e1 fd         	lea	rdi, [rip - 0x21e6bfe]  # 0x60cd1c <panic_msg>
 27f391a: 48 8d 15 3f 5f f6 00         	lea	rdx, [rip + 0xf65f3f]   # 0x3759860 <panic_location>
 27f3921: be 26 00 00 00               	mov	esi, 0x26
 27f3926: ff 15 4c 5a ff 00            	call	qword ptr [rip + 0xff5a4c] # 0x37e9378 <got_expect_failed>
