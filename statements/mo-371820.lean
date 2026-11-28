import Mathlib

/-!
# A concave upper bound for the interference-rate objective

Source: https://mathoverflow.net/questions/371820 (Math_Y, CC BY-SA 4.0).
Credit: @connoranderson

Retain the self-interference term in each denominator. This gives a concave
objective on the original feasible set and improves the question's bound at
every nonzero feasible point. It agrees with the objective along each axis,
so every additive majorant normalized at the origin bounds it term by term.
-/

namespace OMA.S_mo_371820
open Finset
noncomputable section

abbrev Allocation (n : ℕ) := Fin n → ℝ

def rate {n : ℕ} (β : Matrix (Fin n) (Fin n) ℝ) (x : Allocation n) : ℝ :=
  ∑ i, Real.log (1 + x i / (1 + ∑ j, β j i * x j))

def individual (b t : ℝ) : ℝ := Real.log (1+t/(1+b*t))

def upper {n : ℕ} (β : Matrix (Fin n) (Fin n) ℝ) (x : Allocation n) : ℝ :=
  ∑ i, individual (β i i) (x i)

def feasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (p : Allocation m) :
    Set (Allocation n) := {x | (∀ i, 0 ≤ x i) ∧ ∀ k, ∑ i, A k i*x i ≤ p k}

theorem main : ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (p : Allocation m)
    (β : Matrix (Fin n) (Fin n) ℝ), (∀ i j, 0 < β i j) →
    ConcaveOn ℝ (feasible A p) (upper β) ∧
    (∀ x ∈ feasible A p, rate β x ≤ upper β x ∧
      (x ≠ 0 → upper β x < ∑ i, Real.log (1+x i))) ∧
    (∀ h : Fin n → ℝ → ℝ, (∀ i, h i 0 = 0) →
      (∀ x : Allocation n, (∀ i, 0 ≤ x i) → rate β x ≤ ∑ i, h i (x i)) →
      ∀ i t, 0 ≤ t → individual (β i i) t ≤ h i t) := by
  sorry

end
end OMA.S_mo_371820
