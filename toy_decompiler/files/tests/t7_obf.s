; toggle last bit

	mov rax, rdi
	mov rbx, rax
	mov rcx, rbx
	mov rsi, rcx
	xor rsi, 12345678h
	xor rsi, 12345679h
	mov rax, rsi

