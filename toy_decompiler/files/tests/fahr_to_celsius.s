	; celsius = 5 * (fahr-32) / 9
	mov	rax, rdi
	sub	rax, 32
	imul	rax, 5
	mov	rbx, 9
	idiv	rbx
