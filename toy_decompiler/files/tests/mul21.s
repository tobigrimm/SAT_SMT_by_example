; multiplication by 21, as found by aha:

;Found a 4-operation program:
;   shl   r1,rx,2
;   shl   r2,r1,2
;   add   r3,r2,r1
;   add   r4,r3,rx
;   Expr: ((((x << 2) << 2) + (x << 2)) + x)

	mov	rax, rdi
	shl	rax, 2
	; rax=arg1<<2
	mov	rbx, rax
	shl	rbx, 2
	; rbx=arg1<<4
	add	rax, rdi
	; rax=arg1<<2 + arg1
	add	rax, rbx

