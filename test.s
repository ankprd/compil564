	.text
	.globl	main

main:
L13:
	pushq %rbp
L25:
	movq %rsp, %rbp
L24:
	addq $-8, %rsp
L12:
L11:
L10:
	movq $24, %rdi
L9:
L19:
L18:
	call sbrk
L17:
L8:
	movq %rax, -8(%rsp)
L7:
	movq $16, %rdi
L6:
L16:
L15:
	call sbrk
L14:
L5:
	movq -8(%rsp), %r10
L4:
L3:
	movq %rax, 8(%r10)
	.data
