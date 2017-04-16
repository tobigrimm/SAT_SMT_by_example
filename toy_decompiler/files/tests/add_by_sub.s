; addition without add allowed, as found by aha:

;Found a 2-operation program:
;   neg   r1,rx
;   sub   r2,ry,r1
;   Expr: (y - -(x))

	mov rax, rdi
	neg rax
	sub rsi, rax
	mov rax, rsi


