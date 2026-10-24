	.text
	.attribute	4, 16
	.attribute	5, "rv64i2p1_m2p0_a2p1_f2p2_d2p2_zicsr2p0"
	.file	"memcpy.c"
	.globl	memcpy                          # -- Begin function memcpy
	.p2align	2
	.type	memcpy,@function
memcpy:                                 # @memcpy
# %bb.0:
	andi	a3, a1, 3
	beqz	a3, .LBB0_5
# %bb.1:
	beqz	a2, .LBB0_5
# %bb.2:
	addi	a4, a1, 1
	li	a5, 1
	mv	a3, a0
.LBB0_3:                                # =>This Inner Loop Header: Depth=1
	lbu	a7, 0(a1)
	mv	a6, a2
	addi	a1, a1, 1
	sb	a7, 0(a3)
	addi	a3, a3, 1
	andi	a7, a4, 3
	addi	a2, a2, -1
	beqz	a7, .LBB0_6
# %bb.4:                                #   in Loop: Header=BB0_3 Depth=1
	addi	a4, a4, 1
	bne	a6, a5, .LBB0_3
	j	.LBB0_6
.LBB0_5:
	mv	a3, a0
.LBB0_6:
	andi	a5, a3, 3
	beqz	a5, .LBB0_13
# %bb.7:
	li	a4, 32
	bltu	a2, a4, .LBB0_26
# %bb.8:
	lw	a4, 0(a1)
	li	a6, 3
	beq	a5, a6, .LBB0_20
# %bb.9:
	li	a6, 2
	bne	a5, a6, .LBB0_23
# %bb.10:
	sb	a4, 0(a3)
	srli	a5, a4, 8
	sb	a5, 1(a3)
	addi	a3, a3, 2
	addi	a2, a2, -2
	addi	a1, a1, 16
	li	a5, 17
.LBB0_11:                               # =>This Inner Loop Header: Depth=1
	lw	a6, -12(a1)
	srliw	a4, a4, 16
	slli	a7, a6, 16
	lw	t0, -8(a1)
	or	a4, a7, a4
	sw	a4, 0(a3)
	srliw	a4, a6, 16
	slli	a6, t0, 16
	lw	a7, -4(a1)
	or	a4, a6, a4
	sw	a4, 4(a3)
	srliw	a6, t0, 16
	slli	t0, a7, 16
	lw	a4, 0(a1)
	or	a6, t0, a6
	sw	a6, 8(a3)
	srliw	a6, a7, 16
	slli	a7, a4, 16
	or	a6, a7, a6
	sw	a6, 12(a3)
	addi	a3, a3, 16
	addi	a2, a2, -16
	addi	a1, a1, 16
	bltu	a5, a2, .LBB0_11
# %bb.12:
	addi	a1, a1, -14
	j	.LBB0_26
.LBB0_13:
	li	a4, 16
	bltu	a2, a4, .LBB0_16
# %bb.14:
	li	a4, 15
.LBB0_15:                               # =>This Inner Loop Header: Depth=1
	lw	a5, 0(a1)
	lw	a6, 4(a1)
	lw	a7, 8(a1)
	lw	t0, 12(a1)
	sw	a5, 0(a3)
	sw	a6, 4(a3)
	sw	a7, 8(a3)
	sw	t0, 12(a3)
	addi	a1, a1, 16
	addi	a2, a2, -16
	addi	a3, a3, 16
	bltu	a4, a2, .LBB0_15
.LBB0_16:
	li	a4, 8
	bltu	a2, a4, .LBB0_18
# %bb.17:
	lw	a4, 0(a1)
	lw	a5, 4(a1)
	sw	a4, 0(a3)
	sw	a5, 4(a3)
	addi	a3, a3, 8
	addi	a1, a1, 8
.LBB0_18:
	andi	a4, a2, 4
	beqz	a4, .LBB0_32
# %bb.19:
	lw	a4, 0(a1)
	sw	a4, 0(a3)
	addi	a3, a3, 4
	addi	a1, a1, 4
	j	.LBB0_32
.LBB0_20:
	sb	a4, 0(a3)
	addi	a3, a3, 1
	addi	a2, a2, -1
	addi	a1, a1, 16
	li	a5, 18
.LBB0_21:                               # =>This Inner Loop Header: Depth=1
	lw	a6, -12(a1)
	srliw	a4, a4, 8
	slli	a7, a6, 24
	lw	t0, -8(a1)
	or	a4, a7, a4
	sw	a4, 0(a3)
	srliw	a4, a6, 8
	slli	a6, t0, 24
	lw	a7, -4(a1)
	or	a4, a6, a4
	sw	a4, 4(a3)
	srliw	a6, t0, 8
	slli	t0, a7, 24
	lw	a4, 0(a1)
	or	a6, t0, a6
	sw	a6, 8(a3)
	srliw	a6, a7, 8
	slli	a7, a4, 24
	or	a6, a7, a6
	sw	a6, 12(a3)
	addi	a3, a3, 16
	addi	a2, a2, -16
	addi	a1, a1, 16
	bltu	a5, a2, .LBB0_21
# %bb.22:
	addi	a1, a1, -15
	j	.LBB0_26
.LBB0_23:
	sb	a4, 0(a3)
	srli	a5, a4, 8
	sb	a5, 1(a3)
	srli	a5, a4, 16
	sb	a5, 2(a3)
	addi	a3, a3, 3
	addi	a2, a2, -3
	addi	a1, a1, 16
	li	a5, 16
.LBB0_24:                               # =>This Inner Loop Header: Depth=1
	lw	a6, -12(a1)
	srliw	a4, a4, 24
	slli	a7, a6, 8
	lw	t0, -8(a1)
	or	a4, a7, a4
	sw	a4, 0(a3)
	srliw	a4, a6, 24
	slli	a6, t0, 8
	lw	a7, -4(a1)
	or	a4, a6, a4
	sw	a4, 4(a3)
	srliw	a6, t0, 24
	slli	t0, a7, 8
	lw	a4, 0(a1)
	or	a6, t0, a6
	sw	a6, 8(a3)
	srliw	a6, a7, 24
	slli	a7, a4, 8
	or	a6, a7, a6
	sw	a6, 12(a3)
	addi	a3, a3, 16
	addi	a2, a2, -16
	addi	a1, a1, 16
	bltu	a5, a2, .LBB0_24
# %bb.25:
	addi	a1, a1, -13
.LBB0_26:
	li	a4, 16
	bltu	a2, a4, .LBB0_28
# %bb.27:
	lbu	a4, 0(a1)
	lbu	a5, 1(a1)
	lbu	a6, 2(a1)
	sb	a4, 0(a3)
	sb	a5, 1(a3)
	lbu	a4, 3(a1)
	sb	a6, 2(a3)
	lbu	a5, 4(a1)
	lbu	a6, 5(a1)
	sb	a4, 3(a3)
	lbu	a4, 6(a1)
	sb	a5, 4(a3)
	sb	a6, 5(a3)
	lbu	a5, 7(a1)
	sb	a4, 6(a3)
	lbu	a4, 8(a1)
	lbu	a6, 9(a1)
	sb	a5, 7(a3)
	lbu	a5, 10(a1)
	sb	a4, 8(a3)
	sb	a6, 9(a3)
	lbu	a4, 11(a1)
	sb	a5, 10(a3)
	lbu	a5, 12(a1)
	lbu	a6, 13(a1)
	sb	a4, 11(a3)
	lbu	a4, 14(a1)
	sb	a5, 12(a3)
	sb	a6, 13(a3)
	lbu	a5, 15(a1)
	sb	a4, 14(a3)
	addi	a1, a1, 16
	addi	a4, a3, 16
	sb	a5, 15(a3)
	mv	a3, a4
.LBB0_28:
	andi	a4, a2, 8
	beqz	a4, .LBB0_30
# %bb.29:
	lbu	a4, 0(a1)
	lbu	a5, 1(a1)
	lbu	a6, 2(a1)
	sb	a4, 0(a3)
	sb	a5, 1(a3)
	lbu	a4, 3(a1)
	sb	a6, 2(a3)
	lbu	a5, 4(a1)
	lbu	a6, 5(a1)
	sb	a4, 3(a3)
	lbu	a4, 6(a1)
	sb	a5, 4(a3)
	sb	a6, 5(a3)
	lbu	a5, 7(a1)
	sb	a4, 6(a3)
	addi	a1, a1, 8
	addi	a4, a3, 8
	sb	a5, 7(a3)
	mv	a3, a4
.LBB0_30:
	andi	a4, a2, 4
	beqz	a4, .LBB0_32
# %bb.31:
	lbu	a4, 0(a1)
	lbu	a5, 1(a1)
	lbu	a6, 2(a1)
	sb	a4, 0(a3)
	sb	a5, 1(a3)
	lbu	a4, 3(a1)
	sb	a6, 2(a3)
	addi	a1, a1, 4
	addi	a5, a3, 4
	sb	a4, 3(a3)
	mv	a3, a5
.LBB0_32:
	andi	a4, a2, 2
	beqz	a4, .LBB0_34
# %bb.33:
	lbu	a4, 0(a1)
	lbu	a5, 1(a1)
	sb	a4, 0(a3)
	addi	a1, a1, 2
	addi	a4, a3, 2
	sb	a5, 1(a3)
	mv	a3, a4
.LBB0_34:
	andi	a2, a2, 1
	beqz	a2, .LBB0_36
# %bb.35:
	lbu	a1, 0(a1)
	sb	a1, 0(a3)
.LBB0_36:
	ret
.Lfunc_end0:
	.size	memcpy, .Lfunc_end0-memcpy
                                        # -- End function
	.ident	"clang version 18.1.6 (https://github.com/ziglang/zig-bootstrap 98bc6bf4fc4009888d33941daf6b600d20a42a56)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
