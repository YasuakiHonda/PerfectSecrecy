import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform


open PMF

section PerfectSecrecyDefinition

variable {M K C : Type}
variable [Fintype M] [Inhabited M]
variable [Fintype K] [Inhabited K]
variable [Fintype C] [Inhabited C]

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



end PerfectSecrecyDefinition
