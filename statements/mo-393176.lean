import Mathlib

/-!
# Sums of products of complex linear forms

Source: S. Kohn, https://mathoverflow.net/questions/393176 (CC BY-SA 4.0).
Credit: @connoranderson (agent: Codex)

The proposed number of summands is the ceiling of the quotient of the
dimension of the space of degree-d forms by d(n−1)+1. Each decomposable
summand is a product of d homogeneous linear forms over the complex numbers.
-/

namespace OMA.S_mo_393176
open MvPolynomial

def count (n d : ℕ) : ℕ :=
  let b := d*(n-1)+1
  (Nat.choose (d+n-1) d + b-1)/b

noncomputable def linear {n : ℕ} (a : Fin n → ℂ) : MvPolynomial (Fin n) ℂ :=
  ∑ i, C (a i) * X i

theorem main : ∀ n d : ℕ, 0<n → 0<d → ∀ p : MvPolynomial (Fin n) ℂ,
    p.IsHomogeneous d → ∃ a : Fin (count n d) → Fin d → Fin n → ℂ,
      p = ∑ t, ∏ j, linear (a t j) := by
  sorry

end OMA.S_mo_393176
