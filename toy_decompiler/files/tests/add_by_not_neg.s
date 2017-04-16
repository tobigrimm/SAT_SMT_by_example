; arg1+2, without add/sub allowed, as found by aha:

;Found a 4-operation program:
;   not   r1,rx
;   neg   r2,r1
;   not   r3,r2
;   neg   r4,r3
;   Expr: -(~(-(~(x))))

	mov	rax, rdi
	not	rax
	neg	rax
	not	rax
	neg	rax

