#RDI - haystack       v1
#RSI - haystack_size  v2
#RDX - needle         v3
#RCX - needle_size    v4

	.text
	.globl	kmp_search
	.type	kmp_search, @function
kmp_search:                      
                                        # v1  v2  v3  v4  v5  v6  v7  v8  v9  v10 v11 v12 v13 v14 v15 v16
	testq	%v4, %v4                #  |   |   |   U
	movq	%v1, %rax               #  U   |   |   |
	je	.exit                   #  |   |   |   |
	leaq	(%v4,%v3), %v7          #  |   |   U   U           D
	movq	%v3, %v5                #  |   |   U   |   D       |
	leaq	8+T(%rip), %v9          #  |   |   |   |   |       |       D
	movq	$-1, T(%rip)            #  |   |   |   |   |       |       |
	cmpq	%v5, %v7                #  |   |   |   |   U       U       |
	leaq	-8(%v9), %v8            #  |   |   |   |   |       |   D   U
	je	.L20                    #  |   |   |   |   |       |   |   |
.L6:                                    #  |   |   |   |   |       |   |   |
	movq	-8(%v9), %v14           #  |   |   |   |   |       |   |   U                    D
	addq	$1, %v14                #  |   |   |   |   |       |   |   |                    U
	testq	%v14, %v14              #  |   |   |   |   |       |   |   |                    U
	movq	%v14, (%v9)             #  |   |   |   |   |       |   |   U                    U
	jle	.L4                     #  |   |   |   |   |       |   |   |                    |
	movzbl	(%v5), %v11             #  |   |   |   |   U       |   |   |        D           |
	cmpb	%v11_byte, -1(%v3,%v14) #  |   |   U   |   |       |   |   |        U           U
	jne	.L5                     #  |   |   |   |   |       |   |   |                    |
	jmp	.L4                     #  |   |   |   |   |       |   |   |                    |
.L21:                                   #  |   |   |   |   |       |   |   |                    |
	movzbl	-1(%v3,%v14), %v12      #  |   |   U   |   |       |   |   |            D       U
	cmpb	%v12_byte, (%v5)        #  |   |   |   |   U       |   |   |            U       |
	je	.L4                     #  |   |   |   |   |       |   |   |                    |
.L5:                                    #  |   |   |   |   |       |   |   |                    |
	movq	-8(%v8,%v14,8), %v15    #  |   |   |   |   |       |   U   |                    U   D
	addq	$1, %v15                #  |   |   |   |   |       |       |                        U
	testq	%v15, %v15              #  |   |   |   |   |       |       |                        U
	movq	%v15, (%v9)             #  |   |   |   |   |       |       U                        U
	jg	.L21                    #  |   |   |   |   |       |       |
.L4:                                    #  |   |   |   |   |       |       |
	addq	$1, %v5                 #  |   |   |   |   U       |       |
	addq	$8, %v9                 #  |   |   |   |   |       |       U
	cmpq	%v5, %v7                #  |   |   |   |   U       U       |
	jne	.L6                     #  |   |   |   |   |       |       |
.L20:
                                        # v1  v2  v3  v4  v5  v6  v7  v8  v9  v10 v11 v12 v13 v14 v15 v16
                                        #  |   |   |   |
	leaq	T(%rip), %v6            #  |   |   |   |       D
	xorq	%v16, %v16              #  |   |   |   |       |                                        D
	xorq	%v10, %v10              #  |   |   |   |       |                D                       |
.L7:                                    #  |   |   |   |       |                |                       |
	cmpq	%v10, %v2               #  |   U   |   |       |                U                       |
	jbe	.L22                    #  |   |   |   |       |                |                       |
.L11:                                   #  |   |   |   |       |                |                       |
	testq	%v16, %v16              #  |   |   |   |       |                |                       U
	js	.L8                     #  |   |   |   |       |                |                       |
	movzbl	(%v3,%v16), %v13        #  |   |   U   |       |                |           D           U
	cmpb	%v13_byte, (%v1,%v10)   #  U   |       |       |                U           U           |
	je	.L8                     #  |   |       |       |                |                       |
	cmpq	%v10, %v2               #  |   U       |       |                U                       |
	movq	(%v6,%v16,8), %v16      #  |           |       U                |                       U
	ja	.L11                    #  |           |                        |                       |
.L22:                                   #  |           |                        |                       |
	xorq	%rax, %rax              #  |           |                        |                       |
	ret                             #  |           |                        |                       |
.L8:                                    #  |           |                        |                       |
	addq	$1, %v16                #  |           |                        |                       U
	addq	$1, %v10                #  |           |                        U                       |
	cmpq	%v16, %v4               #  |           U                        |                       U
	jne	.L7                     #  |           |                        |
	subq	%v4, %v10               #  |           U                        U
	leaq	(%v1,%v10), %rax        #  U                                    U
.exit:
	ret
	.comm	T,8192,32
