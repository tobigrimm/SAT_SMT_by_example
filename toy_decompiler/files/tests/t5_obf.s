; do nothing (obfuscation)

;Found a 5-operation program:
;   neg   r1,rx
;   neg   r2,r1
;   sub   r3,r1,3
;   sub   r4,r3,r1
;   sub   r5,r4,r3
;   Expr: (((-(x) - 3) - -(x)) - (-(x) - 3))

	mov rax, rdi
	neg rax
	mov rbx, rax
	; rbx=-x
	mov rcx, rbx
	sub rcx, 3
	; rcx=-x-3
	mov rax, rcx
	sub rax, rbx
	; rax=(-(x) - 3) - -(x)
	sub rax, rcx

