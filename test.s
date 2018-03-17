	.text
	.globl	main

main:
L6:
	movq $216, %rax
L5:
	movq $2, %r10
L14:
	pushq %rdx
	movq %rax, %rdx
	shlq %rdx, $32
	idivq %r10
	popq %rdx
L12:
	movq %rax, %rdi
L11:
	call putchar
L2:
	movq $0, %rax
L15:
	ret
	.data
