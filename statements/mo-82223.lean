import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.BigOperators

/-!
# MathOverflow 82223: two measures of correlation

Source: https://mathoverflow.net/questions/82223/question-on-two-measures-of-correlation
Question by Ralph Crasto, 29 November 2011. Credit: @etaubman.

Two finite sigma-fields are represented by their finite partitions into atoms.
The nonnegative table w records the probabilities of intersections of their
atoms. Every measurable real function is constant on the appropriate atoms,
and every event is a union of atoms. Conversely every joint probability table
is realized on the finite product space with its coordinate sigma-fields.
Thus arbitrary finite tables express the full finite-sigma-field question.

The correlation is covariance divided by the square root of the product of
variances. Only positive-variance functions enter either supremum, removing
the undefined zero denominators. The empty supremum is conventionally zero.
The second supremum uses all indicator functions, including complements, so
absolute values would give the same maximal coefficient.
-/

namespace OMA.S_mo_82223

open scoped BigOperators

def probabilityTable {n m : ℕ} (w : Fin n → Fin m → ℝ) : Prop :=
  (∀ i j, 0 ≤ w i j) ∧ (∑ i, ∑ j, w i j) = 1

def meanLeft {n m : ℕ} (w : Fin n → Fin m → ℝ) (f : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, w i j * f i

def meanRight {n m : ℕ} (w : Fin n → Fin m → ℝ) (g : Fin m → ℝ) : ℝ :=
  ∑ i, ∑ j, w i j * g j

def varLeft {n m : ℕ} (w : Fin n → Fin m → ℝ) (f : Fin n → ℝ) : ℝ :=
  (∑ i, ∑ j, w i j * (f i) ^ 2) - (meanLeft w f) ^ 2

def varRight {n m : ℕ} (w : Fin n → Fin m → ℝ) (g : Fin m → ℝ) : ℝ :=
  (∑ i, ∑ j, w i j * (g j) ^ 2) - (meanRight w g) ^ 2

def covariance {n m : ℕ} (w : Fin n → Fin m → ℝ)
    (f : Fin n → ℝ) (g : Fin m → ℝ) : ℝ :=
  (∑ i, ∑ j, w i j * f i * g j) - meanLeft w f * meanRight w g

noncomputable def correlation {n m : ℕ} (w : Fin n → Fin m → ℝ)
    (f : Fin n → ℝ) (g : Fin m → ℝ) : ℝ :=
  covariance w f g / Real.sqrt (varLeft w f * varRight w g)

def indicator {n : ℕ} (a : Fin n → Bool) (i : Fin n) : ℝ :=
  if a i then 1 else 0

def allCorrelations {n m : ℕ} (w : Fin n → Fin m → ℝ) : Set ℝ :=
  {r | ∃ f g, 0 < varLeft w f ∧ 0 < varRight w g ∧ r = correlation w f g}

def indicatorCorrelations {n m : ℕ} (w : Fin n → Fin m → ℝ) : Set ℝ :=
  {r | ∃ a b, 0 < varLeft w (indicator a) ∧ 0 < varRight w (indicator b) ∧
    r = correlation w (indicator a) (indicator b)}

theorem main : ∀ (n m : ℕ) (w : Fin n → Fin m → ℝ),
    probabilityTable w → sSup (allCorrelations w) = sSup (indicatorCorrelations w) := by
  sorry

end OMA.S_mo_82223
