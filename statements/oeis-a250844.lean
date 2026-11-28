import Mathlib

/-!
# A250844: Primes of the form 7^x + y^7 with x, y > 0.

Source: https://oeis.org/A250844
Credit: @gblacher2

The entry's comment (Robert Israel, May 09 2018) reads: "Conjecture: a(n+1)>=a(n)+42, with
equality for infinitely many n, namely those of the form a(n)=7^1+y^7, a(n+1)=7^2+y^7."

We state the three claims it contains: every gap between consecutive terms is at least 42, the
gap equals 42 for infinitely many `n`, and whenever it equals 42 the two terms are `7^1 + y^7` and
`7^2 + y^7` for the same `y`.

`a n` is `Nat.nth` of the set of terms, so it is indexed from `0` (the OEIS offset is `1`); the
statement is about all `n`, so the shift does not change it. If there were only finitely many
terms, `Nat.nth` would return `0` past the last one and the first claim would fail, as it should.
-/

namespace OMA.S_oeis_a250844

/-- `p` is a term of A250844: a prime of the form `7^x + y^7` with `x, y > 0`. -/
def IsTerm (p : ℕ) : Prop :=
  p.Prime ∧ ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ p = 7 ^ x + y ^ 7

/-- `a n` is the `n`-th term of A250844 in increasing order, counted from `0`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm n

/-- Consecutive terms differ by at least `42`; the difference is exactly `42` for infinitely many
`n`, and exactly for those `n` with `a n = 7^1 + y^7` and `a (n + 1) = 7^2 + y^7`. -/
theorem main :
    (∀ n : ℕ, a n + 42 ≤ a (n + 1)) ∧
    {n : ℕ | a (n + 1) = a n + 42}.Infinite ∧
    (∀ n : ℕ, a (n + 1) = a n + 42 →
      ∃ y : ℕ, a n = 7 ^ 1 + y ^ 7 ∧ a (n + 1) = 7 ^ 2 + y ^ 7) := by
  sorry

end OMA.S_oeis_a250844
