	.text
	.globl	main

main:
L17:
	pushq %rbp
L32:
	movq %rsp, %rbp
L31:
	addq $-8, %rsp
L16:
L15:
L14:
	movq $65, %r10
L13:
	movq %r10, -8(%rbp)
L12:
	movq -8(%rbp), %rdi
L11:
L20:
L19:
	call putchar
L18:
L10:
	movq -8(%rbp), %r10
L9:
	movq $1, %r8
L8:
	addq %r8, %r10
L7:
	movq %r10, -8(%rbp)
L6:
	movq -8(%rbp), %rdi
L5:
L26:
L25:
	call putchar
L24:
L4:
	movq $10, %rdi
L3:
L23:
L22:
	call putchar
L21:
L2:
	movq $0, %rax
L1:
L30:
L29:
L28:
	movq %rbp, %rsp
L33:
	popq %rbp
L27:
	ret
	.data
