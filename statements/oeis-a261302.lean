import Mathlib

/-!
# A261302: `a(n+1) = |a(n) - gcd(a(n), 2n+1)|`, `a(1) = 1`

Source: https://oeis.org/A261302
Credit: @Lenqth

A261302 is defined (offset 1) by `a(1) = 1` and `a(n+1) = |a(n) - gcd(a(n), 2n+1)|`. The absolute
value only matters when `a(n) = 0`, in which case `a(n+1) = 2n + 1`. The sequence begins
`1, 0, 5, 4, 3, 2, 1, 0, 17, 16, ...`.

Formalizes the conjecture in the comments of A261302: for all `n`, `a(n) = 0` implies that
`2n + 1 = a(n+1)` is prime (cf. A186254).

The function `a` below is indexed from `1` as in the OEIS entry; the value at index `0` is an
unused placeholder, and the statement only concerns `n ≥ 1`.
-/

namespace OMA.S_oeis_a261302

/-- A261302 with offset 1: `a 1 = 1` and `a (n + 1) = |a n - gcd (a n) (2n + 1)|` for `n ≥ 1`. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => Int.natAbs ((a (n + 1) : ℤ) - (Nat.gcd (a (n + 1)) (2 * (n + 1) + 1) : ℤ))

/-- If `a n = 0` for some `n ≥ 1`, then `2n + 1` is prime. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = 0 → (2 * n + 1).Prime := by
  sorry

end OMA.S_oeis_a261302
