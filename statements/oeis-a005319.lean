import Mathlib.Data.Int.Basic

/-!
# Creighton Dement's identity for OEIS A005319

Source: https://oeis.org/A005319
Conjecture recorded November 17, 2004. All four sequences are indexed
from zero. The auxiliary recurrences and initial values are those in
OEIS A090390, A001542, and A046729.
Credit: @willperacchio
-/

namespace OMA.S_oeis_a005319

/-- OEIS A005319. -/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 4
  | n + 2 => 6 * a (n + 1) - a n

/-- OEIS A090390. -/
def a090390 : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | 2 => 9
  | n + 3 => 5 * a090390 (n + 2) + 5 * a090390 (n + 1) - a090390 n

/-- OEIS A001542. -/
def a001542 : ℕ → ℤ
  | 0 => 0
  | 1 => 2
  | n + 2 => 6 * a001542 (n + 1) - a001542 n

/-- OEIS A046729. -/
def a046729 : ℕ → ℤ
  | 0 => 0
  | 1 => 4
  | 2 => 20
  | n + 3 => 5 * a046729 (n + 2) + 5 * a046729 (n + 1) - a046729 n

theorem main : ∀ n : ℕ,
    (-1 : ℤ) ^ (n + 1) = a090390 (n + 1) + a001542 (n + 1) + a046729 n - a n := by
  sorry

end OMA.S_oeis_a005319
