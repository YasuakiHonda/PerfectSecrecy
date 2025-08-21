import PerfectSecrecy.PerfectSecrecy_Def
open PMF
open Set


variable {M K C : Type}
variable [Fintype M] [Inhabited M] [DecidableEq M]
variable [Fintype K] [Inhabited K]
variable [Fintype C] [Inhabited C] [DecidableEq C]

def full_support {T : Type} (A : PMF T) :Prop := ∀t:T, t∈A.support

omit [Fintype C] [Inhabited C]
theorem K_GE_M (Enc : K → M → C) (Dec : K → C → M) (Gen : PMF K) :
    (full_support Gen ∧ correctness Enc Dec ∧ perfect_secrecy Enc Gen)
    → Fintype.card K ≥ Fintype.card M := by
  intro FullGen_CR_PS

  by_contra K_M
  push_neg at K_M

  have m₀:M := default
  have k₀:K := default
  let c₀:C := Enc k₀ m₀
  have hc₀ : c₀=Enc k₀ m₀ := by rfl

  let f : K → M := fun k => Dec k c₀
  have hf : ∀ k:K, f k = Dec k c₀ := by exact fun k ↦ rfl
  -- let S₀ := {m:M | ∃k:K, m=Dec k c₀}
  let S₀ := Finset.image f Finset.univ

  have S₀_le_K: S₀.card ≤ @Fintype.elems.card K := by
    exact Finset.card_image_le

  have S₀_lt_M : S₀.card < Fintype.card M := by
    exact Nat.lt_of_le_of_lt S₀_le_K K_M

  obtain ⟨m₁, hm₁⟩ : ∃m₁:M, ¬ m₁ ∈ S₀ := by
    by_contra hc
    push_neg at hc
    have : S₀=Finset.univ := by
      exact Finset.eq_univ_iff_forall.mpr hc
    simp_rw [this] at S₀_lt_M
    exact (lt_self_iff_false Finset.univ.card).mp S₀_lt_M

  have Enc_m1_ne_c₀ : ∀ k : K, Enc k m₁ ≠ c₀ := by
    intro k
    by_contra contra
    apply hm₁
    have correct:= FullGen_CR_PS.2.1 k m₁
    rw [contra] at correct
    rw [Finset.mem_image]
    use k
    constructor
    · exact Finset.mem_univ k
    · exact correct

  have Enc_m1_zero : (Enc_dist Enc Gen m₁) c₀ = 0 := by
    simp only [Enc_dist, Bind.bind, PMF.bind_apply, PMF.pure_apply]
    rw [tsum_eq_sum]
    · apply Finset.sum_eq_zero
      intro k _
      have : c₀ ≠ Enc k m₁ := by exact fun a => Enc_m1_ne_c₀ k (id (Eq.symm a))
      rw [if_neg this]
      simp
    · intro k _
      have : c₀ ≠ Enc k m₁ := by exact fun a => Enc_m1_ne_c₀ k (id (Eq.symm a))
      rw [if_neg this]
      simp
    · exact Finset.empty

  have Enc_m0_pos : (Enc_dist Enc Gen m₀) c₀ > 0 := by
    simp only [Enc_dist, Bind.bind, PMF.bind_apply, PMF.pure_apply]
    have single_le_tsum: (fun a => Gen a * if c₀ = Enc a m₀ then 1 else 0) k₀
      ≤ (∑' (a : K), Gen a * if c₀ = Enc a m₀ then 1 else 0) := by
      exact ENNReal.le_tsum k₀
    have single_gt_zero: 0<(fun a => Gen a * if c₀ = Enc a m₀ then 1 else 0) k₀ := by
      simp_all [c₀]
      have : k₀∈ Gen.support := by
        apply FullGen_CR_PS.1
      exact (apply_pos_iff Gen k₀).mpr this
    apply lt_of_lt_of_le single_gt_zero
    simp_all

  have ps := FullGen_CR_PS.2.2 m₀ m₁ c₀
  simp_all
