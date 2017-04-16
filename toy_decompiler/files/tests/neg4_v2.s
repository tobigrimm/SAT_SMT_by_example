	; commutative test

	mov	rax, rdi
	not	rax
	mov	rbx, 1
	add	rbx, rax
	mov	rax, rbx

