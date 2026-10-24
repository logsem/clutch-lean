	.text
	.attribute	4, 16
	.attribute	5, "rv64i2p1_m2p0_a2p1_f2p2_d2p2_zicsr2p0"
	.file	"memset.c"
	.globl	memset                          # -- Begin function memset
	.p2align	2
	.type	memset,@function
memset:                                 # @memset
# %bb.0:
	beqz	a2, .LBB0_9
# %bb.1:
	sb	a1, 0(a0)
	add	a3, a0, a2
	li	a4, 3
	sb	a1, -1(a3)
	bltu	a2, a4, .LBB0_9
# %bb.2:
	sb	a1, 1(a0)
	sb	a1, 2(a0)
	sb	a1, -2(a3)
	li	a4, 7
	sb	a1, -3(a3)
	bltu	a2, a4, .LBB0_9
# %bb.3:
	sb	a1, 3(a0)
	li	a6, 9
	sb	a1, -4(a3)
	bltu	a2, a6, .LBB0_9
# %bb.4:
	negw	a3, a0
	andi	a3, a3, 3
	add	a4, a0, a3
	sub	a2, a2, a3
	andi	a2, a2, -4
	slli	a1, a1, 56
	lui	a5, 65793
	slli	a5, a5, 4
	addi	a5, a5, 256
	mulhu	a1, a1, a5
	sw	a1, 0(a4)
	add	a5, a4, a2
	sw	a1, -4(a5)
	bltu	a2, a6, .LBB0_9
# %bb.5:
	sw	a1, 4(a4)
	sw	a1, 8(a4)
	sw	a1, -12(a5)
	li	a6, 25
	sw	a1, -8(a5)
	bltu	a2, a6, .LBB0_9
# %bb.6:
	sw	a1, 12(a4)
	sw	a1, 16(a4)
	sw	a1, 20(a4)
	sw	a1, 24(a4)
	sw	a1, -28(a5)
	sw	a1, -24(a5)
	sw	a1, -20(a5)
	andi	a6, a4, 4
	addi	a7, a6, 24
	sub	t0, a2, a7
	li	t1, 32
	sw	a1, -16(a5)
	bltu	t0, t1, .LBB0_9
# %bb.7:
	slli	a1, a1, 32
	srli	a5, a1, 32
	or	a1, a1, a5
	add	a4, a4, a7
	sub	a2, a2, a6
	addi	a2, a2, -56
	andi	a2, a2, -32
	or	a2, a2, a6
	add	a3, a3, a0
	add	a2, a2, a3
	addi	a2, a2, 56
.LBB0_8:                                # =>This Inner Loop Header: Depth=1
	sd	a1, 0(a4)
	sd	a1, 8(a4)
	sd	a1, 16(a4)
	sd	a1, 24(a4)
	addi	a4, a4, 32
	bne	a4, a2, .LBB0_8
.LBB0_9:
	ret
.Lfunc_end0:
	.size	memset, .Lfunc_end0-memset
                                        # -- End function
	.ident	"clang version 18.1.6 (https://github.com/ziglang/zig-bootstrap 98bc6bf4fc4009888d33941daf6b600d20a42a56)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
