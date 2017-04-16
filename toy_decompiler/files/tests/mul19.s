; multiplication by 19, as found by aha:

;Found a 4-operation program:
;   add   r1,rx,rx
;   mul   r2,r1,3
;   mul   r3,r2,3
;   add   r4,r3,rx
;   Expr: ((((x + x)*3)*3) + x)

	mov	rax, rdi
	add	rax, rax
	mul	rax, 3
	mul	rax, 3
	add	rax, rdi
