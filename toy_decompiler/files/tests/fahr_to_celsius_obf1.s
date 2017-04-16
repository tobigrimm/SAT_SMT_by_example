	; celsius = 5 * (fahr-32) / 9
	; fake luggage:
	mov	rbx, 12345h
	mov	rax, rdi
	sub	rax, 32
	; fake luggage:
	add	rbx, rax
	imul	rax, 5
	mov	rbx, 9
	idiv	rbx
	; fake luggage:
	sub	rdx, rax
	
