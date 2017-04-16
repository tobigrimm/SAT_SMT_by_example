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
	mov	rcx, rax
	; OR result with garbage (result of fake luggage):
	or	rcx, rdx
	; the following instruction shouldn't affect result:
	and	rax, rcx

