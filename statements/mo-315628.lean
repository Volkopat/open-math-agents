import Mathlib

/-!
# MathOverflow 315628

Source: https://mathoverflow.net/questions/315628
-/

namespace OMA.S_mo_315628

open Finset

def successes {n : ℕ} (x : Fin n → Bool) : ℕ := ∑ i, if x i then 1 else 0

noncomputable def meanBit {n : ℕ} (w : (Fin n → Bool) → ℝ) (i : Fin n) : ℝ :=
  ∑ x, w x * (if x i then 1 else 0)

noncomputable def meanProduct {n : ℕ} (w : (Fin n → Bool) → ℝ) (i j : Fin n) : ℝ :=
  ∑ x, w x * (if x i && x j then 1 else 0)

theorem main : ∀ (n m : ℕ), m < n →
    ∀ w : (Fin n → Bool) → ℝ, (∀ x, 0 ≤ w x) → (∑ x, w x) = 1 →
    (∀ (x : Fin n → Bool) (σ : Equiv.Perm (Fin n)), w (x ∘ σ) = w x) →
    (∀ x, 0 < w x → successes x ≤ m) →
    ∀ i j : Fin n, i ≠ j → meanProduct w i j ≤ meanBit w i * meanBit w j := by
  sorry

end OMA.S_mo_315628
