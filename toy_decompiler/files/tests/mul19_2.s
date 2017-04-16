; multiplication by 19, as found by aha, no MUL allowed:

; Found a 4-operation program:
;   shl   r1,rx,2
;   shl   r2,r1,2
;   add   r3,r2,r1
;   sub   r4,r3,rx
;   Expr: ((((x << 2) << 2) + (x << 2)) - x)

	mov rax, rdi
	shl rax, 2
	mov rbx, rax
	shl rax, 2
	add rax, rbx
	sub rax, rdi

