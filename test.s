	.text
	.globl	main

main:
L24:
	pushq %rbp
L42:
	movq %rsp, %rbp
L41:
	addq $-8, %rsp
L23:
L22:
L21:
	movq $16, %rdi
L20:
L30:
L29:
	call sbrk
L28:
L19:
	movq %rax, -8(%rbp)
L18:
	movq $65, %r10
L17:
	movq -8(%rbp), %r8
L16:
L15:
	movq %r10, 0(%r8)
L14:
	movq -8(%rbp), %r10
L13:
	movq 0(%r10), %rdi
L12:
L27:
L26:
	call putchar
L25:
L11:
	movq $66, %r10
L10:
	movq -8(%rbp), %r8
L9:
L8:
	movq %r10, 8(%r8)
L7:
	movq -8(%rbp), %r10
L6:
	movq 8(%r10), %rdi
L5:
L36:
L35:
	call putchar
L34:
L4:
	movq $10, %rdi
L3:
L33:
L32:
	call putchar
L31:
L2:
	movq $0, %rax
L1:
L40:
L39:
L38:
	movq %rbp, %rsp
L43:
	popq %rbp
L37:
	ret
	.data
