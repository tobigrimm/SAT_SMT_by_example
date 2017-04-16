; toggle all bits

	mov rax, rdi
	; toggle last bit:
	xor rax, 12345678h
	xor rax, 12345679h
	; toggle all bits except last:
	xor rax, 0fffffffffffffffeh

