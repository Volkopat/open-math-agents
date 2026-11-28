import FormalConjectures.OEIS.«218585»

-- Reduction OeisA218585.conjecture_2 of Partitions $n = x + y$ with $x^2 + xy + y^2$ prime
-- Credit: @eltociear
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The tabulated range and the open tail for Seidov's `n x + (n - x) ^ 2`

Seidov's conjecture in A218585: for every `n > 12` some `x` with `0 < x < n / 3` has
`n * x + (n - x) ^ 2` prime. Writing `y = n - x`, the value is `x ^ 2 - x y + y ^ 2`, a norm form
of `ℚ(√-3)`; the primes it takes are exactly the primes `≡ 1 (mod 3)` together with `3`, and the
question is whether the values on the finitely many pairs `x + y = n`, `0 < x < n / 3` must hit one.

For a fixed `n` this is a finite search over at most `n / 3` values, each below `n ^ 2`, so each `n`
is decided by computation. What is open is a uniform argument: the sequence `x ^ 2 - x y + y ^ 2` for
`x + y = n` is not a linear progression, so even Linnik's theorem does not apply, and no result in
the literature bounds the first prime value on such a curve.

The OEIS entry A218585 carries a table for `n = 1..20000` of the related count `a(n)` (the splits
`n = x + y` with `x ^ 2 + x y + y ^ 2` prime), which I recomputed and which agrees term by term;
Seidov's statement itself is about `0 < x < n / 3` and is not what the table counts, so the finite
range below is the range I checked by exhaustive search, not a restatement of the table.

So the conjecture splits at the end of that range:

* `H1` (checked range): every `n` with `12 < n <= 20000` has such an `x`. Finite: for each `n` a
  scan of `x = 1, 2, ...` below `n / 3` with a primality test of `n x + (n - x) ^ 2 < n ^ 2`.
* `H2` (the open tail): every `n > 20000` has such an `x`. This is the whole difficulty: a prime
  value of a quadratic form on the line `x + y = n`.

Neither hypothesis mentions the target, the other one, or `main`; `main` is the case split, and no
upstream lemma is used, so nothing depends on a `decide`-style proof of an upstream statement.
-/

namespace OMA.R_OeisA218585_conjecture_2_R1

/-- The checked range: every `n` with `12 < n <= 20000` has `x` with `0 < x`, `3 x < n` and
`n * x + ( n - x ) ^ 2` prime (exhaustive search over the range of the table in A218585). -/
def H1 : Prop :=
  ∀ n : ℕ, 12 < n → n ≤ 20000 →
    ∃ x : ℕ, 0 < x ∧ 3 * x < n ∧ Nat.Prime (n * x + (n - x) ^ 2)

/-- The open tail: every `n > 20000` has `x` with `0 < x`, `3 x < n` and `n * x + ( n - x ) ^ 2`
prime. Nothing is known here: it asks for a prime value of the norm form `x ^ 2 - x y + y ^ 2` on
the line `x + y = n`, which lies on no arithmetic progression. -/
def H2 : Prop :=
  ∀ n : ℕ, 20000 < n →
    ∃ x : ℕ, 0 < x ∧ 3 * x < n ∧ Nat.Prime (n * x + (n - x) ^ 2)

theorem main : H1 → H2 → type_of% @OeisA218585.conjecture_2 := by
  intro h1 h2 n hn
  by_cases h : n ≤ 20000
  · exact h1 n hn h
  · exact h2 n (Nat.lt_of_not_le h)

end OMA.R_OeisA218585_conjecture_2_R1
