import PerfectSecrecy.PerfectSecrecy_Def

namespace Bitvec

def bitVecEquivFin (n : ℕ) : BitVec n ≃ Fin (2^n) where
  toFun := BitVec.toFin  -- BitVec → Fin
  invFun := BitVec.ofFin  -- Fin → BitVec
  left_inv := by
    intro bv
    simp
  right_inv := by
    intro f
    simp

instance (n : ℕ) : Fintype (BitVec n) :=
  Fintype.ofEquiv (Fin (2^n)) (bitVecEquivFin n).symm

lemma card (n : ℕ) : Fintype.card (BitVec n) = 2^n := by
  calc
    Fintype.card (BitVec n)
    = Fintype.card (Fin (2^n)) := Fintype.card_congr (bitVecEquivFin n)
    _= 2^n                  := Fintype.card_fin _


end Bitvec


variable {n : ℕ}


def OTP_Enc (k : BitVec n) (m : BitVec n) : BitVec n :=
  k ^^^ m

def OTP_Dec (k : BitVec n) (c : BitVec n) : BitVec n :=
  k ^^^ c

example : correctness (@OTP_Enc n) (@OTP_Dec n) := by
  unfold OTP_Enc OTP_Dec correctness
  intro k m
  simp
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]


noncomputable
def OTP_Gen : PMF (BitVec n) :=
  PMF.uniformOfFintype (BitVec n)

lemma mkc_symm (m k c : (BitVec n)) : c=k^^^m ↔ k=c^^^m := by
  constructor
  · intro hc
    rw [hc, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  · intro hk
    rw [hk, BitVec.xor_assoc,BitVec.xor_self, BitVec.xor_zero]


theorem OTP_is_perfectly_secret :
  perfect_secrecy (@OTP_Enc n) (@OTP_Gen n) := by
    intro m₁ m₂ c

    unfold  Enc_dist
    simp_rw [Bind.bind]
    unfold OTP_Gen OTP_Enc

    simp [PMF.bind_apply]
    simp [mkc_symm]
