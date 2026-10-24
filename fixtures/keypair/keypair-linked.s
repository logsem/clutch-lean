	.text
	.globl	crypto_box_curve25519xsalsa20poly1305_tweet_keypair
	.p2align 2
	.type	crypto_box_curve25519xsalsa20poly1305_tweet_keypair,@function
crypto_box_curve25519xsalsa20poly1305_tweet_keypair: # @crypto_box_curve25519xsalsa20poly1305_tweet_keypair
# %bb.0:
	addi	sp, sp, -32
	sd	ra, 24(sp)                      # 8-byte Folded Spill
	sd	s0, 16(sp)                      # 8-byte Folded Spill
	sd	s1, 8(sp)                       # 8-byte Folded Spill
	mv	s0, a1
	mv	s1, a0
	li	a1, 32
	mv	a0, s0
	call	randombytes
.Lpcrel_hi10:
	auipc	a0, %pcrel_hi(_9)
	addi	a2, a0, %pcrel_lo(.Lpcrel_hi10)
	mv	a0, s1
	mv	a1, s0
	call	crypto_scalarmult_curve25519_tweet
	li	a0, 0
	ld	ra, 24(sp)                      # 8-byte Folded Reload
	ld	s0, 16(sp)                      # 8-byte Folded Reload
	ld	s1, 8(sp)                       # 8-byte Folded Reload
	addi	sp, sp, 32
	ret
.Lfunc_end18:
	.size	crypto_box_curve25519xsalsa20poly1305_tweet_keypair, .Lfunc_end18-crypto_box_curve25519xsalsa20poly1305_tweet_keypair
	.p2align 2
	.type	crypto_scalarmult_curve25519_tweet,@function
crypto_scalarmult_curve25519_tweet:     # @crypto_scalarmult_curve25519_tweet
# %bb.0:
	addi	sp, sp, -1552
	sd	ra, 1544(sp)                    # 8-byte Folded Spill
	sd	s0, 1536(sp)                    # 8-byte Folded Spill
	sd	s1, 1528(sp)                    # 8-byte Folded Spill
	sd	s2, 1520(sp)                    # 8-byte Folded Spill
	sd	s3, 1512(sp)                    # 8-byte Folded Spill
	sd	s4, 1504(sp)                    # 8-byte Folded Spill
	sd	s5, 1496(sp)                    # 8-byte Folded Spill
	sd	s6, 1488(sp)                    # 8-byte Folded Spill
	sd	s7, 1480(sp)                    # 8-byte Folded Spill
	sd	s8, 1472(sp)                    # 8-byte Folded Spill
	sd	s9, 1464(sp)                    # 8-byte Folded Spill
	sd	s10, 1456(sp)                   # 8-byte Folded Spill
	mv	s1, a2
	mv	s0, a1
	mv	s2, a0
	addi	a0, sp, 1424
	li	a2, 31
	call	memcpy
	lbu	a0, 31(s0)
	lbu	a1, 1424(sp)
	andi	a0, a0, 63
	addi	a0, a0, 64
	sb	a0, 1455(sp)
	andi	a0, a1, 248
	sb	a0, 1424(sp)
	addi	s1, s1, 1
	addi	a0, sp, 784
	addi	a1, sp, 912
.LBB13_1:                               # =>This Inner Loop Header: Depth=1
	lbu	a2, 0(s1)
	lbu	a3, -1(s1)
	slli	a2, a2, 8
	or	a2, a2, a3
	sd	a2, 0(a0)
	addi	a0, a0, 8
	addi	s1, s1, 2
	bne	a0, a1, .LBB13_1
# %bb.2:
	ld	a0, 904(sp)
	slli	a0, a0, 49
	srli	a0, a0, 49
	sd	a0, 904(sp)
	addi	a0, sp, 400
	li	a2, 128
	li	a1, 0
	call	memset
	addi	a0, sp, 664
	li	a2, 120
	li	a1, 0
	call	memset
	addi	a0, sp, 280
	li	a2, 120
	li	a1, 0
	call	memset
	addi	a0, sp, 528
	addi	a1, sp, 784
	li	a2, 128
	call	memcpy
	li	a0, 1
	sd	a0, 272(sp)
	sd	a0, 656(sp)
	addi	s3, sp, 656
	addi	s7, sp, 400
	addi	s4, sp, 272
	li	a0, 254
	addi	s8, sp, 528
	addi	s5, sp, 1424
.LBB13_3:                               # =>This Loop Header: Depth=1
                                        #     Child Loop BB13_4 Depth 2
                                        #     Child Loop BB13_6 Depth 2
                                        #     Child Loop BB13_8 Depth 2
                                        #     Child Loop BB13_10 Depth 2
                                        #     Child Loop BB13_12 Depth 2
                                        #     Child Loop BB13_14 Depth 2
                                        #     Child Loop BB13_16 Depth 2
                                        #     Child Loop BB13_18 Depth 2
                                        #     Child Loop BB13_20 Depth 2
                                        #     Child Loop BB13_22 Depth 2
                                        #     Child Loop BB13_24 Depth 2
                                        #     Child Loop BB13_26 Depth 2
	mv	s6, a0
	srli	a0, a0, 3
	add	a0, a0, s5
	lbu	a0, 0(a0)
	andi	a1, s6, 7
	srlw	a0, a0, a1
	slli	a0, a0, 63
	srai	s9, a0, 63
	addi	a0, sp, 656
	addi	a1, sp, 528
.LBB13_4:                               #   Parent Loop BB13_3 Depth=1
                                        # =>  This Inner Loop Header: Depth=2
	ld	a2, 0(a0)
	ld	a3, 0(a1)
	xor	a4, a3, a2
	and	a4, a4, s9
	xor	a2, a2, a4
	sd	a2, 0(a0)
	xor	a3, a3, a4
	sd	a3, 0(a1)
	addi	a1, a1, 8
	addi	a0, a0, 8
	bne	a1, s3, .LBB13_4
# %bb.5:                                #   in Loop: Header=BB13_3 Depth=1
	addi	a0, sp, 272
	addi	a1, sp, 400
.LBB13_6:                               #   Parent Loop BB13_3 Depth=1
                                        # =>  This Inner Loop Header: Depth=2
	ld	a2, 0(a1)
	ld	a3, 0(a0)
	xor	a4, a3, a2
	and	a4, a4, s9
	xor	a2, a2, a4
	sd	a2, 0(a1)
	xor	a3, a3, a4
	sd	a3, 0(a0)
	addi	a0, a0, 8
	addi	a1, a1, 8
	bne	a0, s7, .LBB13_6
# %bb.7:                                #   in Loop: Header=BB13_3 Depth=1
	addi	a0, sp, 144
	addi	a1, sp, 400
	addi	a2, sp, 656
.LBB13_8:                               #   Parent Loop BB13_3 Depth=1
                                        # =>  This Inner Loop Header: Depth=2
	ld	a3, 0(a2)
	ld	a4, 0(a1)
	add	a3, a3, a4
	sd	a3, 0(a0)
	addi	a0, a0, 8
	addi	a1, a1, 8
	addi	a2, a2, 8
	bne	a0, s4, .LBB13_8
# %bb.9:                                #   in Loop: Header=BB13_3 Depth=1
	addi	a0, sp, 400
	addi	a1, sp, 656
.LBB13_10:                              #   Parent Loop BB13_3 Depth=1
                                        # =>  This Inner Loop Header: Depth=2
	ld	a2, 0(a1)
	ld	a3, 0(a0)
	sub	a2, a2, a3
	sd	a2, 0(a1)
	addi	a0, a0, 8
	addi	a1, a1, 8
	bne	a0, s8, .LBB13_10
# %bb.11:                               #   in Loop: Header=BB13_3 Depth=1
	addi	a0, sp, 400
	addi	a1, sp, 272
	addi	a2, sp, 528
.LBB13_12:                              #   Parent Loop BB13_3 Depth=1
                                        # =>  This Inner Loop Header: Depth=2
	ld	a3, 0(a2)
	ld	a4, 0(a1)
	add	a3, a3, a4
	sd	a3, 0(a0)
	addi	a0, a0, 8
	addi	a1, a1, 8
	addi	a2, a2, 8
	bne	a0, s8, .LBB13_12
# %bb.13:                               #   in Loop: Header=BB13_3 Depth=1
	addi	a0, sp, 272
	addi	a1, sp, 528
.LBB13_14:                              #   Parent Loop BB13_3 Depth=1
                                        # =>  This Inner Loop Header: Depth=2
	ld	a2, 0(a1)
	ld	a3, 0(a0)
	sub	a2, a2, a3
	sd	a2, 0(a1)
	addi	a0, a0, 8
	addi	a1, a1, 8
	bne	a0, s7, .LBB13_14
# %bb.15:                               #   in Loop: Header=BB13_3 Depth=1
	addi	a0, sp, 272
	addi	a1, sp, 144
	addi	a2, sp, 144
	addi	s1, sp, 144
	call	M
	addi	a0, sp, 16
	addi	a1, sp, 656
	addi	a2, sp, 656
	addi	s10, sp, 656
	call	M
	addi	a0, sp, 656
	addi	a1, sp, 400
	addi	a2, sp, 656
	addi	s0, sp, 400
	call	M
	addi	a0, sp, 400
	addi	a1, sp, 528
	addi	a2, sp, 144
	call	M
.LBB13_16:                              #   Parent Loop BB13_3 Depth=1
                                        # =>  This Inner Loop Header: Depth=2
	ld	a0, 0(s10)
	ld	a1, 0(s0)
	add	a0, a0, a1
	sd	a0, 0(s1)
	addi	s1, s1, 8
	addi	s0, s0, 8
	addi	s10, s10, 8
	bne	s1, s4, .LBB13_16
# %bb.17:                               #   in Loop: Header=BB13_3 Depth=1
	addi	a0, sp, 400
	addi	a1, sp, 656
.LBB13_18:                              #   Parent Loop BB13_3 Depth=1
                                        # =>  This Inner Loop Header: Depth=2
	ld	a2, 0(a1)
	ld	a3, 0(a0)
	sub	a2, a2, a3
	sd	a2, 0(a1)
	addi	a0, a0, 8
	addi	a1, a1, 8
	bne	a0, s8, .LBB13_18
# %bb.19:                               #   in Loop: Header=BB13_3 Depth=1
	addi	a0, sp, 528
	addi	a1, sp, 656
	addi	a2, sp, 656
	call	M
	addi	a0, sp, 400
	addi	a1, sp, 16
	addi	a2, sp, 272
.LBB13_20:                              #   Parent Loop BB13_3 Depth=1
                                        # =>  This Inner Loop Header: Depth=2
	ld	a3, 0(a2)
	ld	a4, 0(a1)
	sub	a3, a3, a4
	sd	a3, 0(a0)
	addi	a0, a0, 8
	addi	a1, a1, 8
	addi	a2, a2, 8
	bne	a0, s8, .LBB13_20
# %bb.21:                               #   in Loop: Header=BB13_3 Depth=1
.Lpcrel_hi8:
	auipc	a0, %pcrel_hi(_121665)
	addi	a2, a0, %pcrel_lo(.Lpcrel_hi8)
	addi	a0, sp, 656
	addi	a1, sp, 400
	addi	s0, sp, 656
	call	M
	addi	a0, sp, 272
.LBB13_22:                              #   Parent Loop BB13_3 Depth=1
                                        # =>  This Inner Loop Header: Depth=2
	ld	a1, 0(s0)
	ld	a2, 0(a0)
	add	a1, a1, a2
	sd	a1, 0(s0)
	addi	a0, a0, 8
	addi	s0, s0, 8
	bne	a0, s7, .LBB13_22
# %bb.23:                               #   in Loop: Header=BB13_3 Depth=1
	addi	a0, sp, 400
	addi	a1, sp, 400
	addi	a2, sp, 656
	addi	s1, sp, 656
	call	M
	addi	a0, sp, 656
	addi	a1, sp, 272
	addi	a2, sp, 16
	call	M
	addi	a0, sp, 272
	addi	a1, sp, 528
	addi	a2, sp, 784
	addi	s0, sp, 528
	call	M
	addi	a0, sp, 528
	addi	a1, sp, 144
	addi	a2, sp, 144
	call	M
.LBB13_24:                              #   Parent Loop BB13_3 Depth=1
                                        # =>  This Inner Loop Header: Depth=2
	ld	a0, 0(s1)
	ld	a1, 0(s0)
	xor	a2, a1, a0
	and	a2, a2, s9
	xor	a0, a0, a2
	sd	a0, 0(s1)
	xor	a1, a1, a2
	sd	a1, 0(s0)
	addi	s0, s0, 8
	addi	s1, s1, 8
	bne	s0, s3, .LBB13_24
# %bb.25:                               #   in Loop: Header=BB13_3 Depth=1
	addi	a0, sp, 272
	addi	a1, sp, 400
.LBB13_26:                              #   Parent Loop BB13_3 Depth=1
                                        # =>  This Inner Loop Header: Depth=2
	ld	a2, 0(a1)
	ld	a3, 0(a0)
	xor	a4, a3, a2
	and	a4, a4, s9
	xor	a2, a2, a4
	sd	a2, 0(a1)
	xor	a3, a3, a4
	sd	a3, 0(a0)
	addi	a0, a0, 8
	addi	a1, a1, 8
	bne	a0, s7, .LBB13_26
# %bb.27:                               #   in Loop: Header=BB13_3 Depth=1
	addi	a0, s6, -1
	bnez	s6, .LBB13_3
# %bb.28:
	addi	a0, sp, 1296
	addi	a1, sp, 272
	addi	a2, sp, 528
	addi	a3, sp, 400
	addi	a4, sp, 656
.LBB13_29:                              # =>This Inner Loop Header: Depth=1
	ld	a6, 0(a4)
	ld	s1, 0(a3)
	ld	s0, 0(a2)
	ld	a5, 0(a1)
	sd	a6, -384(a0)
	sd	s1, -256(a0)
	sd	s0, -128(a0)
	sd	a5, 0(a0)
	addi	a1, a1, 8
	addi	a2, a2, 8
	addi	a3, a3, 8
	addi	a4, a4, 8
	addi	a0, a0, 8
	bne	a1, s7, .LBB13_29
# %bb.30:
	addi	s0, sp, 1040
	mv	a0, s0
	mv	a1, s0
	call	inv25519
	addi	s1, sp, 912
	mv	a0, s1
	mv	a1, s1
	mv	a2, s0
	call	M
	mv	a0, s2
	mv	a1, s1
	call	pack25519
	li	a0, 0
	ld	ra, 1544(sp)                    # 8-byte Folded Reload
	ld	s0, 1536(sp)                    # 8-byte Folded Reload
	ld	s1, 1528(sp)                    # 8-byte Folded Reload
	ld	s2, 1520(sp)                    # 8-byte Folded Reload
	ld	s3, 1512(sp)                    # 8-byte Folded Reload
	ld	s4, 1504(sp)                    # 8-byte Folded Reload
	ld	s5, 1496(sp)                    # 8-byte Folded Reload
	ld	s6, 1488(sp)                    # 8-byte Folded Reload
	ld	s7, 1480(sp)                    # 8-byte Folded Reload
	ld	s8, 1472(sp)                    # 8-byte Folded Reload
	ld	s9, 1464(sp)                    # 8-byte Folded Reload
	ld	s10, 1456(sp)                   # 8-byte Folded Reload
	addi	sp, sp, 1552
	ret
.Lfunc_end13:
	.size	crypto_scalarmult_curve25519_tweet, .Lfunc_end13-crypto_scalarmult_curve25519_tweet
	.p2align 2
	.type	memcpy,@function
memcpy:                                 # @memcpy
# %bb.0:
	andi	a3, a1, 3
	beqz	a3, .Lmemcpy_BB0_5
# %bb.1:
	beqz	a2, .Lmemcpy_BB0_5
# %bb.2:
	addi	a4, a1, 1
	li	a5, 1
	mv	a3, a0
.Lmemcpy_BB0_3:                                # =>This Inner Loop Header: Depth=1
	lbu	a7, 0(a1)
	mv	a6, a2
	addi	a1, a1, 1
	sb	a7, 0(a3)
	addi	a3, a3, 1
	andi	a7, a4, 3
	addi	a2, a2, -1
	beqz	a7, .Lmemcpy_BB0_6
# %bb.4:                                #   in Loop: Header=BB0_3 Depth=1
	addi	a4, a4, 1
	bne	a6, a5, .Lmemcpy_BB0_3
	j	.Lmemcpy_BB0_6
.Lmemcpy_BB0_5:
	mv	a3, a0
.Lmemcpy_BB0_6:
	andi	a5, a3, 3
	beqz	a5, .Lmemcpy_BB0_13
# %bb.7:
	li	a4, 32
	bltu	a2, a4, .Lmemcpy_BB0_26
# %bb.8:
	lw	a4, 0(a1)
	li	a6, 3
	beq	a5, a6, .Lmemcpy_BB0_20
# %bb.9:
	li	a6, 2
	bne	a5, a6, .Lmemcpy_BB0_23
# %bb.10:
	sb	a4, 0(a3)
	srli	a5, a4, 8
	sb	a5, 1(a3)
	addi	a3, a3, 2
	addi	a2, a2, -2
	addi	a1, a1, 16
	li	a5, 17
.Lmemcpy_BB0_11:                               # =>This Inner Loop Header: Depth=1
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
	bltu	a5, a2, .Lmemcpy_BB0_11
# %bb.12:
	addi	a1, a1, -14
	j	.Lmemcpy_BB0_26
.Lmemcpy_BB0_13:
	li	a4, 16
	bltu	a2, a4, .Lmemcpy_BB0_16
# %bb.14:
	li	a4, 15
.Lmemcpy_BB0_15:                               # =>This Inner Loop Header: Depth=1
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
	bltu	a4, a2, .Lmemcpy_BB0_15
.Lmemcpy_BB0_16:
	li	a4, 8
	bltu	a2, a4, .Lmemcpy_BB0_18
# %bb.17:
	lw	a4, 0(a1)
	lw	a5, 4(a1)
	sw	a4, 0(a3)
	sw	a5, 4(a3)
	addi	a3, a3, 8
	addi	a1, a1, 8
.Lmemcpy_BB0_18:
	andi	a4, a2, 4
	beqz	a4, .Lmemcpy_BB0_32
# %bb.19:
	lw	a4, 0(a1)
	sw	a4, 0(a3)
	addi	a3, a3, 4
	addi	a1, a1, 4
	j	.Lmemcpy_BB0_32
.Lmemcpy_BB0_20:
	sb	a4, 0(a3)
	addi	a3, a3, 1
	addi	a2, a2, -1
	addi	a1, a1, 16
	li	a5, 18
.Lmemcpy_BB0_21:                               # =>This Inner Loop Header: Depth=1
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
	bltu	a5, a2, .Lmemcpy_BB0_21
# %bb.22:
	addi	a1, a1, -15
	j	.Lmemcpy_BB0_26
.Lmemcpy_BB0_23:
	sb	a4, 0(a3)
	srli	a5, a4, 8
	sb	a5, 1(a3)
	srli	a5, a4, 16
	sb	a5, 2(a3)
	addi	a3, a3, 3
	addi	a2, a2, -3
	addi	a1, a1, 16
	li	a5, 16
.Lmemcpy_BB0_24:                               # =>This Inner Loop Header: Depth=1
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
	bltu	a5, a2, .Lmemcpy_BB0_24
# %bb.25:
	addi	a1, a1, -13
.Lmemcpy_BB0_26:
	li	a4, 16
	bltu	a2, a4, .Lmemcpy_BB0_28
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
.Lmemcpy_BB0_28:
	andi	a4, a2, 8
	beqz	a4, .Lmemcpy_BB0_30
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
.Lmemcpy_BB0_30:
	andi	a4, a2, 4
	beqz	a4, .Lmemcpy_BB0_32
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
.Lmemcpy_BB0_32:
	andi	a4, a2, 2
	beqz	a4, .Lmemcpy_BB0_34
# %bb.33:
	lbu	a4, 0(a1)
	lbu	a5, 1(a1)
	sb	a4, 0(a3)
	addi	a1, a1, 2
	addi	a4, a3, 2
	sb	a5, 1(a3)
	mv	a3, a4
.Lmemcpy_BB0_34:
	andi	a2, a2, 1
	beqz	a2, .Lmemcpy_BB0_36
# %bb.35:
	lbu	a1, 0(a1)
	sb	a1, 0(a3)
.Lmemcpy_BB0_36:
	ret
.Lmemcpy_func_end0:
	.size	memcpy, .Lmemcpy_func_end0-memcpy
	.p2align 2
	.type	memset,@function
memset:                                 # @memset
# %bb.0:
	beqz	a2, .Lmemset_BB0_9
# %bb.1:
	sb	a1, 0(a0)
	add	a3, a0, a2
	li	a4, 3
	sb	a1, -1(a3)
	bltu	a2, a4, .Lmemset_BB0_9
# %bb.2:
	sb	a1, 1(a0)
	sb	a1, 2(a0)
	sb	a1, -2(a3)
	li	a4, 7
	sb	a1, -3(a3)
	bltu	a2, a4, .Lmemset_BB0_9
# %bb.3:
	sb	a1, 3(a0)
	li	a6, 9
	sb	a1, -4(a3)
	bltu	a2, a6, .Lmemset_BB0_9
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
	bltu	a2, a6, .Lmemset_BB0_9
# %bb.5:
	sw	a1, 4(a4)
	sw	a1, 8(a4)
	sw	a1, -12(a5)
	li	a6, 25
	sw	a1, -8(a5)
	bltu	a2, a6, .Lmemset_BB0_9
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
	bltu	t0, t1, .Lmemset_BB0_9
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
.Lmemset_BB0_8:                                # =>This Inner Loop Header: Depth=1
	sd	a1, 0(a4)
	sd	a1, 8(a4)
	sd	a1, 16(a4)
	sd	a1, 24(a4)
	addi	a4, a4, 32
	bne	a4, a2, .Lmemset_BB0_8
.Lmemset_BB0_9:
	ret
.Lmemset_func_end0:
	.size	memset, .Lmemset_func_end0-memset
	.p2align 2
	.type	M,@function
M:                                      # @M
# %bb.0:
	addi	sp, sp, -304
	sd	ra, 296(sp)                     # 8-byte Folded Spill
	sd	s0, 288(sp)                     # 8-byte Folded Spill
	sd	s1, 280(sp)                     # 8-byte Folded Spill
	sd	s2, 272(sp)                     # 8-byte Folded Spill
	sd	s3, 264(sp)                     # 8-byte Folded Spill
	sd	s4, 256(sp)                     # 8-byte Folded Spill
	sd	s5, 248(sp)                     # 8-byte Folded Spill
	mv	s4, a2
	mv	s5, a1
	mv	s2, a0
	mv	a0, sp
	li	a2, 248
	mv	s3, sp
	li	a1, 0
	call	memset
	li	a0, 0
	li	a6, 16
	mv	a1, sp
.LBB14_1:                               # =>This Loop Header: Depth=1
                                        #     Child Loop BB14_2 Depth 2
	slli	a2, a0, 3
	add	a3, s5, a2
	ld	a3, 0(a3)
	add	a2, a2, s3
	addi	a4, a2, 128
	mv	a5, s4
	mv	a2, a1
.LBB14_2:                               #   Parent Loop BB14_1 Depth=1
                                        # =>  This Inner Loop Header: Depth=2
	ld	s1, 0(a5)
	ld	s0, 0(a2)
	mul	s1, s1, a3
	add	s0, s0, s1
	sd	s0, 0(a2)
	addi	a2, a2, 8
	addi	a5, a5, 8
	bne	a2, a4, .LBB14_2
# %bb.3:                                #   in Loop: Header=BB14_1 Depth=1
	addi	a0, a0, 1
	addi	a1, a1, 8
	bne	a0, a6, .LBB14_1
# %bb.4:
	mv	a0, sp
	addi	a1, sp, 120
	li	a2, 38
.LBB14_5:                               # =>This Inner Loop Header: Depth=1
	ld	a3, 128(a0)
	ld	a4, 0(a0)
	mul	a3, a3, a2
	add	a3, a3, a4
	sd	a3, 0(a0)
	addi	a0, a0, 8
	bne	a0, a1, .LBB14_5
# %bb.6:
	mv	a1, sp
	li	a2, 128
	mv	a0, s2
	call	memcpy
	mv	a0, s2
	call	car25519
	mv	a0, s2
	ld	ra, 296(sp)                     # 8-byte Folded Reload
	ld	s0, 288(sp)                     # 8-byte Folded Reload
	ld	s1, 280(sp)                     # 8-byte Folded Reload
	ld	s2, 272(sp)                     # 8-byte Folded Reload
	ld	s3, 264(sp)                     # 8-byte Folded Reload
	ld	s4, 256(sp)                     # 8-byte Folded Reload
	ld	s5, 248(sp)                     # 8-byte Folded Reload
	addi	sp, sp, 304
	tail	car25519
.Lfunc_end14:
	.size	M, .Lfunc_end14-M
	.p2align 2
	.type	car25519,@function
car25519:                               # @car25519
# %bb.0:
	li	a5, -16
	lui	a6, 16
	li	a7, 37
	lui	t0, 1048560
	mv	a4, a0
.LBB34_1:                               # =>This Inner Loop Header: Depth=1
	ld	a1, 0(a4)
	add	a2, a1, a6
	sd	a2, 0(a4)
	srai	a1, a2, 16
	addi	t2, a1, -1
	mul	t1, t2, a7
	addi	t3, a5, 1
	seqz	a3, t3
	addi	a5, a5, 17
	addi	a1, a3, -1
	and	a1, a1, a5
	slli	a1, a1, 3
	add	a1, a1, a0
	ld	a5, 0(a1)
	neg	a3, a3
	and	a3, a3, t1
	add	a3, a3, t2
	add	a3, a3, a5
	sd	a3, 0(a1)
	ld	a1, 0(a4)
	and	a2, a2, t0
	sub	a1, a1, a2
	sd	a1, 0(a4)
	addi	a4, a4, 8
	mv	a5, t3
	bnez	t3, .LBB34_1
# %bb.2:
	ret
.Lfunc_end34:
	.size	car25519, .Lfunc_end34-car25519
	.p2align 2
	.type	inv25519,@function
inv25519:                               # @inv25519
# %bb.0:
	addi	sp, sp, -192
	sd	ra, 184(sp)                     # 8-byte Folded Spill
	sd	s0, 176(sp)                     # 8-byte Folded Spill
	sd	s1, 168(sp)                     # 8-byte Folded Spill
	sd	s2, 160(sp)                     # 8-byte Folded Spill
	sd	s3, 152(sp)                     # 8-byte Folded Spill
	sd	s4, 144(sp)                     # 8-byte Folded Spill
	sd	s5, 136(sp)                     # 8-byte Folded Spill
	mv	s3, a1
	mv	s2, a0
	addi	a0, sp, 8
	li	a2, 128
	call	memcpy
	li	s0, 253
	li	s4, 2
	li	s1, -1
	li	s5, 4
.LBB15_1:                               # =>This Inner Loop Header: Depth=1
	addi	a0, sp, 8
	addi	a1, sp, 8
	addi	a2, sp, 8
	call	M
	beq	s0, s4, .LBB15_4
# %bb.2:                                #   in Loop: Header=BB15_1 Depth=1
	beq	s0, s5, .LBB15_4
# %bb.3:                                #   in Loop: Header=BB15_1 Depth=1
	addi	a0, sp, 8
	addi	a1, sp, 8
	mv	a2, s3
	call	M
.LBB15_4:                               #   in Loop: Header=BB15_1 Depth=1
	addiw	s0, s0, -1
	bne	s0, s1, .LBB15_1
# %bb.5:
	addi	a1, sp, 8
	li	a2, 128
	mv	a0, s2
	call	memcpy
	ld	ra, 184(sp)                     # 8-byte Folded Reload
	ld	s0, 176(sp)                     # 8-byte Folded Reload
	ld	s1, 168(sp)                     # 8-byte Folded Reload
	ld	s2, 160(sp)                     # 8-byte Folded Reload
	ld	s3, 152(sp)                     # 8-byte Folded Reload
	ld	s4, 144(sp)                     # 8-byte Folded Reload
	ld	s5, 136(sp)                     # 8-byte Folded Reload
	addi	sp, sp, 192
	ret
.Lfunc_end15:
	.size	inv25519, .Lfunc_end15-inv25519
	.p2align 2
	.type	pack25519,@function
pack25519:                              # @pack25519
# %bb.0:
	addi	sp, sp, -288
	sd	ra, 280(sp)                     # 8-byte Folded Spill
	sd	s0, 272(sp)                     # 8-byte Folded Spill
	sd	s1, 264(sp)                     # 8-byte Folded Spill
	sd	s2, 256(sp)                     # 8-byte Folded Spill
	mv	s2, a0
	lui	s1, 1048560
	addiw	s1, s1, 1
	lui	s0, 16
	addiw	s0, s0, -1
	mv	a0, sp
	li	a2, 128
	call	memcpy
	mv	a0, sp
	call	car25519
	mv	a0, sp
	call	car25519
	mv	a0, sp
	call	car25519
	addi	a6, sp, 136
	addi	a7, sp, 8
	addi	t2, sp, 248
	li	t1, 1
	addi	t3, sp, 256
	lui	t0, 1048568
	addiw	t0, t0, 1
.LBB16_1:                               # =>This Loop Header: Depth=1
                                        #     Child Loop BB16_2 Depth 2
                                        #     Child Loop BB16_4 Depth 2
	ld	a0, 0(sp)
	add	a0, a0, s1
	addi	a2, a0, 18
	sd	a2, 128(sp)
	mv	a1, a7
	mv	a0, a6
.LBB16_2:                               #   Parent Loop BB16_1 Depth=1
                                        # =>  This Inner Loop Header: Depth=2
	ld	a4, 0(a1)
	slli	a5, a2, 47
	srai	a5, a5, 63
	add	a5, a5, s1
	and	a2, a2, s0
	add	a4, a4, a5
	sd	a4, 0(a0)
	sd	a2, -8(a0)
	addi	a0, a0, 8
	addi	a1, a1, 8
	mv	a2, a4
	bne	a0, t2, .LBB16_2
# %bb.3:                                #   in Loop: Header=BB16_1 Depth=1
	ld	a0, 240(sp)
	ld	a1, 120(sp)
	slli	a2, a0, 47
	srai	a2, a2, 63
	add	a1, a1, t0
	add	a1, a1, a2
	sd	a1, 248(sp)
	and	a0, a0, s0
	sd	a0, 240(sp)
	slli	a1, a1, 47
	srli	a0, a1, 63
	addi	a0, a0, -1
	addi	a1, sp, 128
	mv	a5, sp
.LBB16_4:                               #   Parent Loop BB16_1 Depth=1
                                        # =>  This Inner Loop Header: Depth=2
	ld	a3, 0(a5)
	ld	a4, 0(a1)
	xor	a2, a4, a3
	and	a2, a2, a0
	xor	a3, a3, a2
	sd	a3, 0(a5)
	xor	a2, a2, a4
	sd	a2, 0(a1)
	addi	a1, a1, 8
	addi	a5, a5, 8
	bne	a1, t3, .LBB16_4
# %bb.5:                                #   in Loop: Header=BB16_1 Depth=1
	andi	a0, t1, 1
	li	t1, 0
	bnez	a0, .LBB16_1
# %bb.6:
	addi	s2, s2, 1
	mv	a0, sp
	addi	a1, sp, 128
.LBB16_7:                               # =>This Inner Loop Header: Depth=1
	ld	a2, 0(a0)
	sb	a2, -1(s2)
	srli	a2, a2, 8
	sb	a2, 0(s2)
	addi	a0, a0, 8
	addi	s2, s2, 2
	bne	a0, a1, .LBB16_7
# %bb.8:
	ld	ra, 280(sp)                     # 8-byte Folded Reload
	ld	s0, 272(sp)                     # 8-byte Folded Reload
	ld	s1, 264(sp)                     # 8-byte Folded Reload
	ld	s2, 256(sp)                     # 8-byte Folded Reload
	addi	sp, sp, 288
	ret
.Lfunc_end16:
	.size	pack25519, .Lfunc_end16-pack25519
	.section .rodata
	.p2align 3

	.type	_121665,@object                 # @_121665
	.p2align	3, 0x0
_121665:
	.quad	56129                           # 0xdb41
	.quad	1                               # 0x1
	.zero	112
	.size	_121665, 128
	.p2align 3

	.type	_9,@object                      # @_9
_9:
	.byte	9                               # 0x9
	.zero	31
	.size	_9, 32
