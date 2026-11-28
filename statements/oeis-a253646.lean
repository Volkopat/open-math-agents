import Mathlib

/-!
# A253646: Primes p such that p^k is zeroless for k=1,...,6.

Source: https://oeis.org/A253646
Credit: @warshanks

A253646 lists the primes `p` such that `p^k` is zeroless (has no digit `0` in base 10) for
`k = 1, …, 6`. They are the primes in A253647, the numbers `n` such that `n^k` is zeroless for
`k = 0, …, 6`. The entry records one conjecture:

  both sequences are conjectured to be finite.

`main` is the conjunction: the set of terms of A253646 is finite, and the set of terms of A253647
is finite.

A number is zeroless when it is positive and `0` is not among its decimal digits. Positivity is
part of the definition because Mathlib's `Nat.digits 10 0` is the empty list, while `0` is written
with the digit `0`; this only excludes `n = 0` from A253647 (`0^1 = 0`), as in the OEIS data, which
starts `1, 2, 3, 5, 6, 14, 17, …`.
-/

namespace OMA.S_oeis_a253646

/-- `m` is zeroless: positive, with no digit `0` in base 10. -/
def Zeroless (m : ℕ) : Prop := 0 < m ∧ 0 ∉ Nat.digits 10 m

/-- The conjecture recorded in OEIS A253646: the primes `p` with `p^k` zeroless for `k = 1, …, 6`
(A253646) are finitely many, and so are the numbers `n` with `n^k` zeroless for `k = 0, …, 6`
(A253647). -/
theorem main : {p : ℕ | p.Prime ∧ ∀ k : ℕ, 1 ≤ k → k ≤ 6 → Zeroless (p ^ k)}.Finite ∧
    {n : ℕ | ∀ k : ℕ, k ≤ 6 → Zeroless (n ^ k)}.Finite := by
  sorry

end OMA.S_oeis_a253646
