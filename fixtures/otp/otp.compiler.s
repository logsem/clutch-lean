	.text
	.attribute	4, 16
	.attribute	5, "rv64i2p1_m2p0_zicsr2p0"
	.file	"otp.c"
	.globl	encrypt_byte                    # -- Begin function encrypt_byte
	.p2align	2
	.type	encrypt_byte,@function
encrypt_byte:                           # @encrypt_byte
# %bb.0:
	addi	sp, sp, -32
	sd	ra, 24(sp)                      # 8-byte Folded Spill
	sd	s0, 16(sp)                      # 8-byte Folded Spill
	sd	s1, 8(sp)                       # 8-byte Folded Spill
	mv	s0, a1
	mv	s1, a0
	li	a1, 1
	mv	a0, s0
	call	randombytes
	lbu	a0, 0(s0)
	xor	a0, a0, s1
	ld	ra, 24(sp)                      # 8-byte Folded Reload
	ld	s0, 16(sp)                      # 8-byte Folded Reload
	ld	s1, 8(sp)                       # 8-byte Folded Reload
	addi	sp, sp, 32
	ret
.Lfunc_end0:
	.size	encrypt_byte, .Lfunc_end0-encrypt_byte
                                        # -- End function
	.ident	"clang version 18.1.6 (https://github.com/ziglang/zig-bootstrap 98bc6bf4fc4009888d33941daf6b600d20a42a56)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
