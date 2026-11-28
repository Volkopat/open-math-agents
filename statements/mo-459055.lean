import Mathlib

/-!
# Law of the change in Hamming distance under random edits

Harry L's question, https://mathoverflow.net/questions/459055 .
Each coordinate changes independently with probability μ, choosing uniformly
among the k−1 other symbols. For any original pair of words, the distribution
of d−H(new) is that of the number of repaired mismatches minus the number of
spoiled matches. The displayed formula gives its point mass at every integer
by taking the coefficient of degree d−z in the generating polynomial for H(new).

Credit: @connoranderson
-/

namespace OMA.S_mo_459055
open Polynomial

noncomputable def edit {k : ℕ} (μ : ℝ) (a b : Fin k) : ℝ :=
  if a=b then 1-μ else μ/(k-1:ℝ)

noncomputable def editMass {L k : ℕ} (μ : ℝ) (old newWord : Fin L → Fin k) : ℝ :=
  ∏ i, edit μ (old i) (newWord i)

noncomputable def distanceLaw (L k d : ℕ) (μ : ℝ) : ℝ[X] :=
  (C (1-μ)+C μ * X)^(L-d) *
    (C (μ/(k-1:ℝ)) + C (1-μ/(k-1:ℝ))*X)^d

theorem main : ∀ L k : ℕ, 2≤k → ∀ μ : ℝ, 0≤μ → μ≤1 →
    ∀ ref old : Fin L → Fin k, ∀ z : ℤ,
    (∑ y : Fin L → Fin k, if (hammingDist ref old : ℤ) - hammingDist ref y = z
      then editMass μ old y else 0) =
    if z ≤ (hammingDist ref old : ℤ) then
      (distanceLaw L k (hammingDist ref old) μ).coeff (((hammingDist ref old : ℤ)-z).toNat)
    else 0 := by
  sorry

end OMA.S_mo_459055
