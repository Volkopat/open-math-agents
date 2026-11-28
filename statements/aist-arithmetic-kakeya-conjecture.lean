import Mathlib

/-!
# The arithmetic Kakeya conjecture

Source: Green and Ruzsa, On the arithmetic Kakeya conjecture of Katz and Tao,
Conjecture 2, https://arxiv.org/abs/1712.02108
Catalog reference: https://arxiv.org/abs/2511.02864
Credit: @BhaveshKSinha
-/

namespace OMA.S_aist_arithmetic_kakeya_conjecture

open scoped BigOperators Classical

/-- Shannon entropy of the real-valued output of a finite weighted sample. -/
noncomputable def entropy {n : ℕ} (weight output : Fin n → ℝ) : ℝ :=
  -∑ z ∈ Finset.univ.image output,
    let mass := ∑ i ∈ Finset.univ.filter (fun i => output i = z), weight i
    mass * Real.log mass

/-- A single finite set of slopes works for every joint distribution.
The inner existential expresses the bound by the maximum over this finite set. -/
theorem main :
    ∀ ε : ℝ, 0 < ε →
      ∃ slopes : Finset ℚ, slopes.Nonempty ∧ (-1 : ℚ) ∉ slopes ∧
        ∀ (n : ℕ) (weight x y : Fin n → ℝ),
          (∀ i, 0 ≤ weight i) → (∑ i, weight i) = 1 →
          ∃ r ∈ slopes, entropy weight (fun i => x i - y i) ≤
            (1 + ε) * entropy weight (fun i => x i + (r : ℝ) * y i) := by
  sorry

end OMA.S_aist_arithmetic_kakeya_conjecture
