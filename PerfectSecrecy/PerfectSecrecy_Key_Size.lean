import PerfectSecrecy.PerfectSecrecy_Def
open PMF


-- Type and set relations and cardinality
lemma L3 {T : Type} [Fintype T] : @Fintype.elems.card T = Fintype.card T := by rfl

lemma L4 {T : Type} [Fintype T] : Fintype.card T = @Set.univ.ncard T := by
  calc
    Fintype.card T = @Fintype.elems.card T := rfl
    _= (@Fintype.elems T).toSet.ncard := by
      exact Eq.symm (Set.ncard_coe_finset Fintype.elems)
    _= (@Set.univ.ncard T) := by
      congr
      ext t;
      simp
      exact Fintype.complete t

variable {M K C : Type}
variable [Fintype M] [Inhabited M]
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
  let f : K → M := fun k => Dec k c₀
  let S₀ := {m:M | ∃k:K, m=Dec k c₀}

  have S₀_eq_image_f : S₀ = Set.image f (Set.univ) := by
    have : S₀={m:M | ∃k:K, m=f k} := by
      simp[f]
      rfl
    unfold Set.image
    rw [this]
    ext m
    simp
    constructor <;>
    · intro hc
      obtain ⟨k,hk⟩ := hc
      use k
      rw [hk]

  have S₀_le_K: S₀.ncard ≤ @Fintype.elems.card K := by
    rw [S₀_eq_image_f, L3, L4]
    refine Set.ncard_image_le ?_
    exact Set.finite_univ

  rw [L3] at S₀_le_K
  have S₀_lt_M : S₀.ncard < Fintype.card M := by linarith

  have exists_m₁ : ∃m₁:M, ¬ m₁ ∈ S₀ := by
    by_contra hc
    push_neg at hc
    have : S₀=Set.univ := by
      ext x
      constructor
      · simp
      · simp
        exact hc x
    simp_rw [this] at S₀_lt_M
    rw [L4] at S₀_lt_M
    linarith

  obtain ⟨m₁, hm₁⟩ := exists_m₁

  have Enc_m1_ne_c₀ : ∀ k : K, Enc k m₁ ≠ c₀ := by
    intro k
    by_contra contra
    apply hm₁
    use k
    rw [←contra]
    have correct:= FullGen_CR_PS.2.1 k m₁
    exact id (Eq.symm correct)

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

  have ps := FullGen_CR_PS.2.2
  unfold perfect_secrecy at ps
  have ps₀ := ps m₀ m₁ c₀
  simp_all
