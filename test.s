	.text
	.globl	main

main:
L12:
L11:
L10:
L9:
	movq $16, %rdi
L8:
L15:
L14:
	call sbrk
L13:
L7:
L6:
	movq $3, %r10
L5:
L4:
L3:
	movq %r10, 0(%rax)
	.data
