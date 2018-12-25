#RDI - haystack       v1
#RSI - haystack_size  v2
#RDX - needle         v3
#RCX - needle_size    v4

	.text
	.globl	kmp_search
	.type	kmp_search, @function
kmp_search:                      
                                        # v1  v2  v3  v4  v5  v6  v7  v8  v9  v10 v11 v12 v13 v14 v15 v16
	testq	%rcx, %rcx              #  |   |   |   U
	movq	%rdi, %rax              #  U   |   |   |
	je	.exit                   #  |   |   |   |
	leaq	(%rcx,%rdx), %r8        #  |   |   U   U           D
	movq	%rdx, %r10              #  |   |   U   |   D       |
	leaq	8+T(%rip), %r11         #  |   |   |   |   |       |       D
	movq	$-1, T(%rip)            #  |   |   |   |   |       |       |
	cmpq	%r10, %r8               #  |   |   |   |   U       U       |
	leaq	-8(%r11), %r13          #  |   |   |   |   |       |   D   U
	je	.L20                    #  |   |   |   |   |       |   |   |
.L6:                                    #  |   |   |   |   |       |   |   |
	movq	-8(%r11), %r9           #  |   |   |   |   |       |   |   U                    D
	addq	$1, %r9                 #  |   |   |   |   |       |   |   |                    U
	testq	%r9, %r9                #  |   |   |   |   |       |   |   |                    U
	movq	%r9, (%r11)             #  |   |   |   |   |       |   |   U                    U
	jle	.L4                     #  |   |   |   |   |       |   |   |                    |
	movzbl	(%r10), %r12d           #  |   |   |   |   U       |   |   |        D           |
	cmpb	%r12b, -1(%rdx,%r9)     #  |   |   U   |   |       |   |   |        U           U
	jne	.L5                     #  |   |   |   |   |       |   |   |                    |
	jmp	.L4                     #  |   |   |   |   |       |   |   |                    |
.L21:                                   #  |   |   |   |   |       |   |   |                    |
	movzbl	-1(%rdx,%r9), %r12d     #  |   |   U   |   |       |   |   |            D       U
	cmpb	%r12b, (%r10)           #  |   |   |   |   U       |   |   |            U       |
	je	.L4                     #  |   |   |   |   |       |   |   |                    |
.L5:                                    #  |   |   |   |   |       |   |   |                    |
	movq	-8(%r13,%r9,8), %r12    #  |   |   |   |   |       |   U   |                    U   D
	addq	$1, %r12                #  |   |   |   |   |       |       |                        U
	testq	%r12, %r12              #  |   |   |   |   |       |       |                        U
	movq	%r12, (%r11)            #  |   |   |   |   |       |       U                        U
	jg	.L21                    #  |   |   |   |   |       |       |
.L4:                                    #  |   |   |   |   |       |       |
	addq	$1, %r10                #  |   |   |   |   U       |       |
	addq	$8, %r11                #  |   |   |   |   |       |       U
	cmpq	%r10, %r8               #  |   |   |   |   U       U       |
	jne	.L6                     #  |   |   |   |   |       |       |
.L20:
                                        # v1  v2  v3  v4  v5  v6  v7  v8  v9  v10 v11 v12 v13 v14 v15 v16
                                        #  |   |   |   |
	leaq	T(%rip), %r11           #  |   |   |   |       D
	xorq	%r9, %r9                #  |   |   |   |       |                                        D
	xorq	%r10, %r10              #  |   |   |   |       |                D                       |
.L7:                                    #  |   |   |   |       |                |                       |
	cmpq	%r10, %rsi              #  |   U   |   |       |                U                       |
	jbe	.L22                    #  |   |   |   |       |                |                       |
.L11:                                   #  |   |   |   |       |                |                       |
	testq	%r9, %r9                #  |   |   |   |       |                |                       U
	js	.L8                     #  |   |   |   |       |                |                       |
	movzbl	(%rdx,%r9), %r8d        #  |   |   U   |       |                |           D           U
	cmpb	%r8b, (%rdi,%r10)       #  U   |       |       |                U           U           |
	je	.L8                     #  |   |       |       |                |                       |
	cmpq	%r10, %rsi              #  |   U       |       |                U                       |
	movq	(%r11,%r9,8), %r9       #  |           |       U                |                       U
	ja	.L11                    #  |           |                        |                       |
.L22:                                   #  |           |                        |                       |
	xorq	%rax, %rax              #  |           |                        |                       |
	ret                             #  |           |                        |                       |
.L8:                                    #  |           |                        |                       |
	addq	$1, %r9                 #  |           |                        |                       U
	addq	$1, %r10                #  |           |                        U                       |
	cmpq	%r9, %rcx               #  |           U                        |                       U
	jne	.L7                     #  |           |                        |
	subq	%rcx, %r10              #  |           U                        U
	leaq	(%rdi,%r10), %rax       #  U                                    U
.exit:
	ret
	.comm	T,8192,32
