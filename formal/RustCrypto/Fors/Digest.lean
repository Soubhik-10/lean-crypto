module
public import RustCrypto.Fors.Positions
public import EthLib.Cryptography.Sphincs.Digest
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ForsDigest
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem decode_three_bits (a b c : BitVec 8) :
    BitVec.fromLEBytes [c,b,a,0] = (0#8 ++ a ++ b ++ c) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi32 : i < 32 := by simpa using hi
  interval_cases i <;> simp only [BitVec.getLsbD_append] <;> simp [BitVec.fromLEBytes]

theorem field24_val (a b c : U8) :
    (core.num.U32.from_be_bytes (Aeneas.Std.Array.make 4#usize [0#u8,a,b,c])).val =
      65536*a.val+256*b.val+c.val := by
  change (BitVec.fromLEBytes [c.bv,b.bv,a.bv,0]).toNat = 65536*a.val+256*b.val+c.val
  have hbits := decode_three_bits a.bv b.bv c.bv
  rw [hbits]
  simp only [BitVec.toNat_append_eq_mul_add,BitVec.toNat_ofNat]
  change ((0*256+a.val)*256+b.val)*256+c.val = _
  omega

@[step] theorem field24_spec (a b c : U8) :
    lift (core.num.U32.from_be_bytes (Aeneas.Std.Array.make 4#usize [0#u8,a,b,c]))
      ⦃ out => out.val = 65536*a.val+256*b.val+c.val ⦄ := by
  simp only [lift,WP.spec_ok]
  exact field24_val a b c

def selected (digest : Aeneas.Std.Array U8 34#usize) (kappa : Nat) : Nat :=
  let bit := kappa*10
  let offset := bit/8
  ((65536*(digest.val[offset]!).val+256*(digest.val[offset+1]!).val+(digest.val[offset+2]!).val)
    >>> (14-bit%8)) % 1024

@[step] theorem leaf_position_spec (digest : Aeneas.Std.Array U8 34#usize) (kappa : Usize)
    (hkappa : kappa.val < 24) :
    lean_sphincs.fors.leaf_position digest kappa ⦃ out =>
      out.val = kappa.val*1024+selected digest kappa.val ⦄ := by
  unfold lean_sphincs.fors.leaf_position
  simp only [lean_sphincs.params.FORS_HEIGHT]
  step*
  have hbit : bit.val = kappa.val*10 := by scalar_tac
  have hat : «at».val = kappa.val*10/8 := by scalar_tac
  have hi2 : i2.val = kappa.val*10/8+1 := by scalar_tac
  have hi4 : i4.val = kappa.val*10/8+2 := by scalar_tac
  have hmask : i12 = 1023#u32 := by scalar_tac
  have hshift : i9.val = 14-(kappa.val*10)%8 := by scalar_tac
  have hwide : i13.val = kappa.val := by scalar_tac
  have h1 : i1 = digest.val[kappa.val*10/8]! := by
    rw [i1_post,← getElem!_pos digest.val «at».val (by scalar_tac),hat]
  have h3 : i3 = digest.val[kappa.val*10/8+1]! := by
    rw [i3_post,← getElem!_pos digest.val i2.val (by scalar_tac),hi2]
  have h5 : i5 = digest.val[kappa.val*10/8+2]! := by
    rw [i5_post,← getElem!_pos digest.val i4.val (by scalar_tac),hi4]
  have hmod (n : Nat) : n &&& 1023 = n % 1024 := by
    simpa using Nat.and_two_pow_sub_one_eq_mod n 10
  have hleaf : leaf.val = selected digest kappa.val := by
    rw [leaf_post,UScalar.val_and,hmask]
    have hv : (1023#u32).val = 1023 := by rfl
    rw [hv,hmod,i10_post,field_post,hshift,h1,h3,h5]
    rfl
  have hbound : leaf.val < 2^(10#u32).val := by
    rw [hleaf]
    exact Nat.mod_lt _ (by decide)
  rw [RustCrypto.ForsPositions.joined_index i14 i13 10#u32 leaf i14_post hbound,hwide,hleaf]
  rfl

end RustCrypto.ForsDigest
