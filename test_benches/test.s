	.file	"test.cc"
	.text
	.section	.rodata
.LC1:
	.string	"cos:%llx, sin:%llx\n"
	.text
	.globl	_Z9fpu_debugv
	.type	_Z9fpu_debugv, @function
_Z9fpu_debugv:
.LFB247:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$48, %rsp
	movabsq	$4606664306871666200, %rax
	movq	%rax, -24(%rbp)
	leaq	-24(%rbp), %rax
	movsd	(%rax), %xmm0
	movsd	%xmm0, -16(%rbp)
	pxor	%xmm0, %xmm0
	movsd	%xmm0, -32(%rbp)
	movq	-16(%rbp), %rax
	movq	%rax, %xmm0
	call	sin
	movq	%xmm0, %rax
	movq	%rax, -8(%rbp)
	movsd	-8(%rbp), %xmm0
	movsd	%xmm0, -40(%rbp)
	leaq	-40(%rbp), %rax
	movq	(%rax), %rdx
	leaq	-32(%rbp), %rax
	movq	(%rax), %rax
	movq	%rax, %rsi
	movl	$.LC1, %edi
	movl	$0, %eax
	call	printf
	movl	$0, %eax
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE247:
	.size	_Z9fpu_debugv, .-_Z9fpu_debugv
	.globl	main
	.type	main, @function
main:
.LFB248:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	call	_Z9fpu_debugv
	movl	$0, %eax
	popq	%rbp
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE248:
	.size	main, .-main
	.ident	"GCC: (GNU) 10.1.0"
	.section	.note.GNU-stack,"",@progbits
