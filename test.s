	.text
	.globl	main

main:
L23:
L22:
L21:
L20:
	movq $0, %rax
L19:
	movq $584, %r10
L18:
	subq %r10, %rax
L17:
L16:
L15:
	movq $4, %r10
L14:
L25:
	pushq %rdx
	movq %rax, %rdx
	sarq $32, %rdx
	idivq %r10
	popq %rdx
L24:
L13:
L12:
L11:
	movq $0, %r8
L10:
	movq $146, %r10
L9:
	subq %r10, %r8
L8:
	cmpq %r8, %rax
	sete %r11b
	movzbq %r11b, %r11
	movq %r11, %rax
L7:
	cmpq $0, %rax
	je L4
L6:
	movq $89, %rdi
L5:
L31:
L30:
	call putchar
L29:
L2:
	movq $0, %rax
L1:
L35:
L34:
L33:
L32:
	ret
L4:
	movq $78, %rdi
L3:
L28:
L27:
	call putchar
L26:
	jmp L2
	.data
