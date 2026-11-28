import FormalConjectures.OEIS.«38771»

-- Reduction OeisA38771.conjecture2.R1 of Smallest composite c such that primorial(n) + c is prime — conjecture2
-- Credit: @eltociear
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Semiprime values of A038771: the tabulated range and the open tail

The theorem says that every term of the sequence is a semiprime, i.e. has exactly two prime factors
counted with multiplicity (`Nat.IsSemiprime`, so `Ω = 2`). Here `a n` is the smallest composite `c`
for which the `n`-th primorial plus `c` is prime.

The OEIS entry A038771 records the range in which this is known (Dmitry Kamenetsky, Jan 06 2019):
the conjecture is true for the first 133 terms, and the table he added to the entry runs from
`a(0)` to `a(133)`, the entry's offset being 0. Taking that published range:

* `H1` (tabulated range): every `n ≤ 133` has `a n` semiprime. Every listed value is composite by
  construction with exactly two prime factors (for instance `a 0 = 4 = 2 * 2`, `a 1 = 9 = 3 * 3`,
  `a 2 = 25 = 5 * 5`, `a 5 = 221 = 13 * 17`); the check is finite, over 134 explicit numbers.
* `H2` (the open tail): every `n > 133`. Nothing is known here, and no heuristic forces the values
  to stay semiprime: `a n` is the first composite in a short window of the arithmetic progression
  `Q + c`, and a window can in principle hold two primes separated by a composite with one factor.

Neither hypothesis mentions the target, the other one, or `main`; `main` is the case split.
-/

namespace OMA.R_OeisA38771_conjecture2_R1

/-- The tabulated range: `a 0` through `a 133` are all semiprimes (OEIS A038771, Kamenetsky). -/
def H1 : Prop :=
  ∀ n : ℕ, n ≤ 133 → (OeisA38771.a n).IsSemiprime

/-- The open tail: no index above 133 is known. -/
def H2 : Prop :=
  ∀ n : ℕ, 133 < n → (OeisA38771.a n).IsSemiprime

theorem main : H1 → H2 → type_of% @OeisA38771.conjecture2 := by
  intro h1 h2 n
  by_cases h : n ≤ 133
  · exact h1 n h
  · exact h2 n (Nat.lt_of_not_le h)

end OMA.R_OeisA38771_conjecture2_R1
