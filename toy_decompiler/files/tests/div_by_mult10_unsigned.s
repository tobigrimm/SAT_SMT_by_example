	mov	rax, rdi
	movabs	rdx, 0cccccccccccccccdh
	mul	rdx
	shr	rdx, 3
	mov	rax, rdx
