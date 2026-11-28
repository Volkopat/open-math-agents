import FormalConjectures.OEIS.«250131»

-- Reduction OeisA250131.conjecture_1.R1 of Odd part of the digital sum of $3^n$ divided by the maximal power of $3$ — conjecture 1
-- Credit: @eltociear
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The sieved sequence of A250131: the tabulated range and the open tail

`a n` is the odd part of the base-10 digit sum of `3 ^ n` after removing the largest power of `3`,
and `b` prepends `2, 3` to it (`b 1 = 2`, `b 2 = 3`, `b n = a (n - 2)`). Shevelev's conjecture is
that the Eratosthenes-like sieve of `b`, with the `1`s removed, leaves only primes: every index `n`
that survives the sieve has `b n` prime.

The sieve is a finite condition at each `n` and the values `b n` are small, so single indices are
decided by computation; what is open is the statement for all `n`. The surviving indices are sparse
and their values are not in increasing order, following `b`, not `n`.

The OEIS entry A250131 publishes the table of `a n` for `n = 1..77` (Vladimir Shevelev, extended by
Peter J. C. Moses), which determines `b n` for `n ≤ 79`. Running the sieve over those `79` indices
gives the surviving set `{1, 2, 16, 27, 36, 50, 64, 76}` with values `2, 3, 5, 7, 11, 13, 17, 19`:
the first eight primes, in order, and every one of them prime. Moses's remark in the entry that the
later primes "follow with some perturbation of order" (`73` before `71`, `101` and `103` before `97`)
is about the tail. So the conjecture splits at the end of the tabulated range:

* `H1` (tabulated range): every sieved `n ≤ 79` has `b n` prime. Finite: eight explicit indices.
* `H2` (the open tail): every sieved `n > 79` has `b n` prime. Nothing is known here; the surviving
  values are perturbed primes, and no argument rules out a surviving composite further out.

Neither hypothesis mentions the target, the other one, or `main`; `main` is the case split.
-/

namespace OMA.R_OeisA250131_conjecture_1_R1

/-- The tabulated range: the sieved indices `1, 2, 16, 27, 36, 50, 64, 76` (all `≤ 79`) have
`b n = 2, 3, 5, 7, 11, 13, 17, 19` (table of `a n` for `n = 1..77` in OEIS A250131). -/
def H1 : Prop :=
  ∀ n : ℕ, n ≤ 79 → n ∈ OeisA250131.sievedIndices → (OeisA250131.b n).Prime

/-- The open tail: every sieved `n > 79` has `b n` prime; the first eight surviving values are
`2, 3, 5, 7, 11, 13, 17, 19`, and beyond that nothing is known. -/
def H2 : Prop :=
  ∀ n : ℕ, 79 < n → n ∈ OeisA250131.sievedIndices → (OeisA250131.b n).Prime

theorem main : H1 → H2 → type_of% @OeisA250131.conjecture_1 := by
  intro h1 h2 n hn
  by_cases h : n ≤ 79
  · exact h1 n h hn
  · exact h2 n (Nat.lt_of_not_le h) hn

end OMA.R_OeisA250131_conjecture_1_R1
