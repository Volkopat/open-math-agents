import Mathlib

/-!
# A115026: Limiting value of n under iteration of the map A101337.

Source: https://oeis.org/A115026
Credit: @avivorly

A101337(n) is the sum of the decimal digits of n, each raised to the power of the number of decimal
digits of n. A115026 (offset 1): iterate A101337 starting at n until reaching a constant value (a fixed
point, like 370) or a cycle (like 160, 217, 352, 160, ...); a(n) is that constant value, or the smallest
value in the cycle (for example a(59) = 160). The entry notes that every orbit reaches a constant or a
cycle. The values on that final cycle are exactly the periodic points of the map that the orbit of n
reaches, so a(n) is the least of them.

Conjecture in the entry (Harvey P. Dale, Jun 08 2022): no term is greater than 370.
-/

namespace OMA.S_oeis_a115026

/-- OEIS A101337: the sum of the decimal digits of `n`, each raised to the power of the number of
decimal digits of `n`. -/
def f (n : ℕ) : ℕ :=
  ((Nat.digits 10 n).map fun d => d ^ (Nat.digits 10 n).length).sum

/-- OEIS A115026: the least value on the final cycle (or the constant value) that the iteration of `f`
starting at `n` reaches. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | (∃ k : ℕ, f^[k] n = m) ∧ m ∈ Function.periodicPts f}

theorem main : ∀ n : ℕ, 1 ≤ n → a n ≤ 370 := by
  sorry

end OMA.S_oeis_a115026
