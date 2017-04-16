	; uint64_t align2grain (uint64_t i, uint64_t grain)
	;    return ((i + grain-1) & ~(grain-1));
	
	; rdi=i
	; rsi=grain

	sub	rsi, 1
	add	rdi, rsi
	not	rsi
	and	rdi, rsi
	mov	rax, rdi

