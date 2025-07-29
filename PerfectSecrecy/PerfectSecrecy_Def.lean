import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform


open PMF

section PerfectSecrecyDefinition

variable {M K C : Type}
variable [Fintype M] [Inhabited M]
variable [Fintype K] [Inhabited K]
variable [Fintype C] [Inhabited C] [DecidableEq C]

noncomputable
def correctness (Enc : K → M → C) (Dec : K → C → M) :=
  ∀ k:K, ∀ m:M, Dec k (Enc k m) = m

noncomputable
def Enc_dist (Enc : K → M → C) (Gen : PMF K) (m : M) : PMF C :=
  do
    let k ← Gen
    PMF.pure (Enc k m)

def perfect_secrecy (Enc : K → M → C) (Gen : PMF K) :=
  ∀ (m1 m2 : M) (c : C),
    (Enc_dist Enc Gen m1) c = (Enc_dist Enc Gen m2) c

noncomputable
def joint_dist (Enc : K → M → C) (Gen : PMF K) (Msg : PMF M) : PMF (M × C) :=
  do
    let m ← Msg
    let k ← Gen
    PMF.pure (m, Enc k m)

noncomputable
def cipher_dist (Enc : K → M → C) (Gen : PMF K) (Msg : PMF M) : PMF C := do
  let m ← Msg
  Enc_dist Enc Gen m

noncomputable
def posterior (Enc : K → M → C) (Gen : PMF K) (Msg : PMF M) (m : M) (c : C) : ENNReal :=
  let joint := joint_dist Enc Gen Msg
  if (cipher_dist Enc Gen Msg) c ≠ 0 then
    (joint (m , c)) / ((cipher_dist Enc Gen Msg) c)
  else 0

noncomputable
def shannon_perfect_secrecy (Enc : K → M → C) (Gen : PMF K) : Prop :=
  ∀ m c, ∀ Msg : PMF M, posterior Enc Gen Msg m c = Msg m

end PerfectSecrecyDefinition
