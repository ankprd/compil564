	.text
	.globl	main

main:
	pushq %rbp
	movq %rsp, %rbp
	addq $-8, %rsp
	movq $1, %rax
	movq $0, %r10
	pushq %rdx
	movq %rax, %rdx
	sarq $32, %rdx
	idivq %r10
	popq %rdx
	movq %rax, %rdi
	call putchar
	movq -8(%rbp), %rax
	movq %rbp, %rsp
	popq %rbp
	ret
	.data
