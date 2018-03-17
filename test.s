	.text
	.globl	main

f:
L43:
	pushq %rbp
L58:
	movq %rsp, %rbp
L57:
	addq $-32, %rsp
L42:
L41:
L40:
	movq %rdi, -24(%rbp)
L39:
	movq %rsi, -32(%rbp)
L38:
	movq %rdx, -8(%rbp)
L37:
	movq %rcx, -16(%rbp)
L20:
	movq -24(%rbp), %r10
L19:
	cmpq $0, %r10
	sete %r11b
	movzbq %r11b, %r11
	movq %r11, %r10
L18:
	cmpq $0, %r10
	je L16
L17:
	movq $10, %rax
L9:
L56:
L55:
L54:
	movq %rbp, %rsp
L59:
	popq %rbp
L53:
	ret
L16:
	movq -24(%rbp), %rdi
L15:
L52:
L51:
	call putchar
L50:
L14:
	movq -32(%rbp), %rdi
L13:
	movq -8(%rbp), %rsi
L12:
	movq -16(%rbp), %rdx
L11:
	movq -24(%rbp), %rcx
L10:
L49:
L48:
L47:
L46:
L45:
	call f
L44:
	jmp L9

main:
L23:
L22:
L21:
L8:
	movq $65, %rdi
L7:
	movq $66, %rsi
L6:
	movq $67, %rdx
L5:
	movq $0, %rcx
L4:
L32:
L31:
L30:
L29:
L28:
	call f
L27:
L3:
L26:
	movq %rax, %rdi
L25:
	call putchar
L24:
L2:
	movq $0, %rax
L1:
L36:
L35:
L34:
L33:
	ret
	.data
