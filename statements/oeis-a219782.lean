import Mathlib

/-!
# A219782: Number of ways to write n=x+y (0<x<=y) with n^2-xy and n^2+xy both prime.

Source: https://oeis.org/A219782
Credit: @gblacher2

Formalizes the OEIS comment (Zhi-Wei Sun): "Conjecture: a(n)>0 if n is not among 1, 8, 10, 18,
20, 41, 46, 58, 78, 116, 440."

Conventions: the sequence has offset 1, so `n ≥ 1`. A representation `n = x + y` with
`0 < x ≤ y` is determined by `x`, with `y = n - x`. Since `x * y ≤ n ^ 2`, the natural-number
subtraction `n ^ 2 - x * y` is the integer `n^2 - xy` of the source. The comment states only
one direction (`a(n) > 0` outside the list), so the statement does not claim `a(n) = 0` on it.
-/

namespace OMA.S_oeis_a219782

/-- A219782(n): the number of ways to write `n = x + y` with `0 < x ≤ y` such that
`n^2 - x*y` and `n^2 + x*y` are both prime. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter fun x =>
    0 < x ∧ x ≤ n - x ∧ (n ^ 2 - x * (n - x)).Prime ∧ (n ^ 2 + x * (n - x)).Prime).card

/-- For `n ≥ 1` not in `{1, 8, 10, 18, 20, 41, 46, 58, 78, 116, 440}`, `a(n) > 0`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    n ∉ ({1, 8, 10, 18, 20, 41, 46, 58, 78, 116, 440} : Finset ℕ) → 0 < a n := by
  sorry

end OMA.S_oeis_a219782
