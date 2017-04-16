; AND using shifts
; often used in ARM thumb code
; это как "оператор подергивания" (мем из соц.сетей: "--i++")
; this is like "twitching operator" (soc.networks meme: "--i++")

	mov rax, rdi
	shr rax, 3
	shl rax, 3

