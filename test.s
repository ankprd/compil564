	.text
	.globl	main

add:
	movq %rdi, %rax
	addq %rsi, %rax
	ret

sub:
	movq %rdi, %rax
	subq %rsi, %rax
	ret

mul:
	imulq %rsi, %rdi
	movq $4096, %rax
	addq %rax, %rdi
	movq $8192, %r10
	movq %rdi, %rax
	pushq %rdx
	movq %rax, %rdx
	sarq $32, %rdx
	idivq %r10
	popq %rdx
	movq %rax, %rdi
	movq %rdi, %rax
	ret

div:
	movq $8192, %r10
	imulq %r10, %rdi
	movq %rsi, %rax
	movq $2, %r10
	pushq %rdx
	movq %rax, %rdx
	sarq $32, %rdx
	idivq %r10
	popq %rdx
	addq %rax, %rdi
	movq %rdi, %rax
	pushq %rdx
	movq %rax, %rdx
	sarq $32, %rdx
	idivq %rsi
	popq %rdx
	movq %rax, %rdi
	movq %rdi, %rax
	ret

of_int:
	movq %rdi, %rax
	movq $8192, %r10
	imulq %r10, %rax
	ret

iter:
	pushq %rbp
	movq %rsp, %rbp
	addq $-104, %rsp
	movq %rdi, -16(%rbp)
	movq %rsi, -24(%rbp)
	movq %rdx, -32(%rbp)
	movq %rcx, -40(%rbp)
	movq %r8, -48(%rbp)
	movq -16(%rbp), %r10
	movq $100, %r8
	cmpq %r8, %r10
	sete %r11b
	movzbq %r11b, %r11
	movq %r11, %r10
	cmpq $0, %r10
	je L133
	movq $1, %rax
L98:
	movq %rbp, %rsp
	popq %rbp
	ret
L133:
	movq -40(%rbp), %rdi
	movq -40(%rbp), %rsi
	call mul
	movq %rax, -56(%rbp)
	movq -48(%rbp), %rdi
	movq -48(%rbp), %rsi
	call mul
	movq %rax, -64(%rbp)
	movq -56(%rbp), %rdi
	movq -64(%rbp), %rsi
	call add
	movq %rax, -8(%rbp)
	movq $4, %rdi
	call of_int
	movq -8(%rbp), %r15
	cmpq %rax, %r15
	setg %r11b
	movzbq %r11b, %r11
	movq %r11, %r15
	movq %r15, -8(%rbp)
	cmpq $0, -8(%rbp)
	je L117
	movq $0, %rax
	jmp L98
L117:
	movq -16(%rbp), %r11
	movq %r11, -72(%rbp)
	movq $1, %r10
	movq -72(%rbp), %r15
	addq %r10, %r15
	movq %r15, -72(%rbp)
	movq -24(%rbp), %r11
	movq %r11, -80(%rbp)
	movq -32(%rbp), %r11
	movq %r11, -88(%rbp)
	movq -56(%rbp), %rdi
	movq -64(%rbp), %rsi
	call sub
	movq -24(%rbp), %rsi
	movq %rax, %rdi
	call add
	movq %rax, -96(%rbp)
	movq $2, %rdi
	call of_int
	movq %rax, -104(%rbp)
	movq -40(%rbp), %rdi
	movq -48(%rbp), %rsi
	call mul
	movq %rax, %rsi
	movq -104(%rbp), %rdi
	call mul
	movq -32(%rbp), %rsi
	movq %rax, %rdi
	call add
	movq %rax, %r8
	movq -96(%rbp), %rcx
	movq -88(%rbp), %rdx
	movq -80(%rbp), %rsi
	movq -72(%rbp), %rdi
	call iter
	jmp L98

inside:
	pushq %rbp
	movq %rsp, %rbp
	addq $-32, %rsp
	movq $0, -8(%rbp)
	movq %rdi, -16(%rbp)
	movq %rsi, -24(%rbp)
	movq $0, %rdi
	call of_int
	movq %rax, -32(%rbp)
	movq $0, %rdi
	call of_int
	movq %rax, %r8
	movq -32(%rbp), %rcx
	movq -24(%rbp), %rdx
	movq -16(%rbp), %rsi
	movq -8(%rbp), %rdi
	call iter
	movq %rbp, %rsp
	popq %rbp
	ret

run:
	pushq %rbp
	movq %rsp, %rbp
	addq $-96, %rsp
	movq %rdi, -48(%rbp)
	movq $-2, %rdi
	call of_int
	movq %rax, -72(%rbp)
	movq $1, %rdi
	call of_int
	movq %rax, %rdi
	movq -72(%rbp), %rsi
	call sub
	movq %rax, -80(%rbp)
	movq $2, %rdi
	movq -48(%rbp), %r10
	imulq %r10, %rdi
	call of_int
	movq %rax, %rsi
	movq -80(%rbp), %rdi
	call div
	movq %rax, -88(%rbp)
	movq $-1, %rdi
	call of_int
	movq %rax, -96(%rbp)
	movq $1, %rdi
	call of_int
	movq %rax, %rdi
	movq -96(%rbp), %rsi
	call sub
	movq %rax, -64(%rbp)
	movq -48(%rbp), %rdi
	call of_int
	movq %rax, %rsi
	movq -64(%rbp), %rdi
	call div
	movq %rax, -8(%rbp)
	movq $0, %r10
	movq %r10, -16(%rbp)
L52:
	movq -16(%rbp), %r10
	movq -48(%rbp), %r8
	cmpq %r8, %r10
	setl %r11b
	movzbq %r11b, %r11
	movq %r11, %r10
	cmpq $0, %r10
	je L6
	movq -96(%rbp), %r11
	movq %r11, -56(%rbp)
	movq -16(%rbp), %rdi
	call of_int
	movq -8(%rbp), %rsi
	movq %rax, %rdi
	call mul
	movq %rax, %rsi
	movq -56(%rbp), %rdi
	call add
	movq %rax, -24(%rbp)
	movq $0, %r10
	movq %r10, -32(%rbp)
L39:
	movq -32(%rbp), %r10
	movq $2, %r8
	movq -48(%rbp), %r9
	imulq %r9, %r8
	cmpq %r8, %r10
	setl %r11b
	movzbq %r11b, %r11
	movq %r11, %r10
	cmpq $0, %r10
	je L13
	movq -72(%rbp), %r11
	movq %r11, -40(%rbp)
	movq -32(%rbp), %rdi
	call of_int
	movq -88(%rbp), %rsi
	movq %rax, %rdi
	call mul
	movq %rax, %rsi
	movq -40(%rbp), %rdi
	call add
	movq %rax, %rdi
	movq -24(%rbp), %rsi
	call inside
	cmpq $0, %rax
	je L20
	movq $48, %rdi
	call putchar
L18:
	movq -32(%rbp), %r10
	movq $1, %r8
	addq %r8, %r10
	movq %r10, -32(%rbp)
	jmp L39
L20:
	movq $49, %rdi
	call putchar
	jmp L18
L13:
	movq $10, %rdi
	call putchar
	movq -16(%rbp), %r10
	movq $1, %r8
	addq %r8, %r10
	movq %r10, -16(%rbp)
	jmp L52
L6:
	movq $0, %rax
	movq %rbp, %rsp
	popq %rbp
	ret

main:
	movq $30, %rdi
	call run
	movq $0, %rax
	ret
	.data
