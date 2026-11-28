import Mathlib

/-!
# Nonvanishing of a hyperbolic Wronskian

Source: Francesco F, https://mathoverflow.net/questions/294123 (CC BY-SA 3.0).
Credit: @connoranderson.

The matrix in the source is recorded with even derivative rows first and
cosh columns first. These row and column permutations preserve nonsingularity.
Repeated parameters up to sign give identical cosh columns. Distinct squared
parameters give the precise condition, including when two are conjugates.
-/

namespace OMA.S_mo_294123

noncomputable def wronskian {n : ℕ} (k : Fin n → ℂ) (x : ℝ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ := fun r j =>
  match r, j with
  | .inl a, .inl i => (k i ^ 2) ^ (a : ℕ) * Complex.cosh (k i*x)
  | .inr a, .inl i => (k i ^ 2) ^ (a : ℕ) * k i * Complex.sinh (k i*x)
  | .inl a, .inr i => (star (k i) ^ 2) ^ (a : ℕ) * Complex.sinh (star (k i)*x)
  | .inr a, .inr i => (star (k i) ^ 2) ^ (a : ℕ) * star (k i) * Complex.cosh (star (k i)*x)

theorem main : ∀ (n : ℕ), 0<n → ∀ k : Fin n → ℂ,
    (∀ i, (k i).re ≠ 0 ∧ (k i).im ≠ 0) → ∀ x : ℝ,
    (wronskian k x).det ≠ 0 ↔ Function.Injective (fun i => k i ^ 2) := by
  sorry

end OMA.S_mo_294123
