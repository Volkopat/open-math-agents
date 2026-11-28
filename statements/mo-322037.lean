import Mathlib

/-!
# MathOverflow 322037

Source: https://mathoverflow.net/questions/322037
-/

namespace OMA.S_mo_322037

open Finset

noncomputable def quadratic {n : ℕ} (k : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j ∈ range k,
    x i * x ⟨(i.val + j) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

theorem main : ∀ n k : ℕ, 0 < k → k ≤ n → ∀ x : Fin n → ℝ,
    (∀ i, 0 ≤ x i) → (∑ i, x i) = 1 →
      quadratic k (fun _ : Fin n => 1 / (n : ℝ)) ≤ quadratic k x := by
  sorry

end OMA.S_mo_322037
