import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Ring

/-!
# The exact floor formula for the nested recurrence A138467

Source: https://oeis.org/A138467. Yalcin Aktar proposed the floor formula in
2008. Michel Dekking gave the corrected parameter range p > 2 in 2023.
The entry itself is p = 3. Index zero is an auxiliary initial value, so the
first source term is a(p,1) = 1. The bounded recursion constructs all terms.
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a138467

def bounded (p : ℕ) : (n : ℕ) → Fin (n+1)
  | 0 => 0
  | n+1 =>
    let previous := bounded p n
    let earlier := bounded p previous.val
    ⟨n+1 - earlier.val / p, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
termination_by n => n
decreasing_by all_goals first | exact Nat.lt_succ_self _ | exact Fin.isLt _

def a (p n : ℕ) : ℕ := (bounded p n).val

noncomputable def slope (p : ℕ) : ℝ :=
  (Real.sqrt ((p:ℝ) * ((p:ℝ)+4)) - p) / 2

theorem main : ∀ p : ℕ, 2 < p → ∀ n : ℕ, 1 ≤ n →
    a p n = ⌊slope p * ((n:ℝ)+1)⌋₊ := by
  sorry

end OMA.S_oeis_a138467
