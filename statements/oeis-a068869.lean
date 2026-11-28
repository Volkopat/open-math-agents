import Mathlib

/-!
# A068869: Smallest number k such that n! + k is a square.

Source: https://oeis.org/A068869

Conjecture (Alexander R. Povolotsky, Oct 06 2008): `a(n) ≠ n^2` for every `n ≥ 1`. The entry
derives it from his conjecture in A004664 that `n! + n^2` is never a perfect square for `n ≥ 1`.

The sequence has offset 1 and begins `0, 2, 3, 1, 1, 9, 1, 81, 729, 225, 324, …`; for example
`a(6) = 9`, because `720` is not a square and `720 + 9 = 27^2`, and `a(1) = 0`, because `1! = 1`
is a square. The hypothesis `n ≥ 1` matters: `a(0) = 0 = 0^2`.

For `n ≥ 6` the conjecture is the same as saying that `n! + n^2` is not a square: two squares
`j^2 < m^2` with `n! ≤ j^2` differ by more than `2 * sqrt(n!) ≥ n^2`, so at most one square lies
in the range from `n!` to `n! + n^2`. For a prime `n = p`, Wilson's theorem gives
`p! + p^2 = p * ((p - 1)! + p)` with `(p - 1)! + p ≡ -1 (mod p)`, so `p` divides `p! + p^2`
exactly once and the case is easy; the open cases are composite `n`. A numeric check finds no
`n ≤ 5000` with `n! + n^2` a square and no `n ≤ 2000` with `a(n) = n^2`.

Encoding:
- `a n` is `sInf` of the set of `k : ℕ` with `IsSquare (n ! + k)`. The set is never empty
  (`k = n ! * n ! - n !` is in it), so `sInf` is its least element.
- The index `n` is the OEIS index (offset 1), and `n ^ 2` is the square of that index.
-/

namespace OMA.S_oeis_a068869

/-- OEIS A068869: the least `k` such that `n ! + k` is a perfect square. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | IsSquare (Nat.factorial n + k)}

/-- Povolotsky's conjecture: `a n ≠ n ^ 2` for every `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n ≠ n ^ 2 := by
  sorry

end OMA.S_oeis_a068869
