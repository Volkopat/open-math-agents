import Mathlib

/-!
# A006218: a(n) = Sum_{k=1..n} floor(n/k); also Sum_{k=1..n} d(k), where d = number of divisors (A000005); also number of solutions to x*y = z with 1 <= x,y,z <= n.

Source: https://oeis.org/A006218
Credit: @ShoQo

Conjecture (N. J. A. Sloane, Nov 24 2008): It appears that the partial sums give A078567.
(Sela Fried, 2025: this conjecture is true.)

A078567 is "Number of arithmetic subsequences of [1..n] with length > 1" (offset 1:
0, 1, 4, 9, 17, 27, ...). The partial sums of A006218 (offset 0: 0, 1, 3, 5, 8, ...) are
0, 1, 4, 9, 17, ..., so the claim is A078567(n) = a(0) + ... + a(n-1) for n ≥ 1.

Formalization notes:
* `a m = Sum_{k=1..m} floor(m/k)` (natural-number division).
* An arithmetic subsequence of `[1..n]` of length `ℓ ≥ 2` is `x, x+d, ..., x+(ℓ-1)d` with
  first term `x ≥ 1`, common difference `d ≥ 1` (a subsequence is increasing) and last term
  `≤ n`; it is determined by the triple `(x, d, ℓ)`, so `T n` (whose cardinality is
  A078567(n)) is the set of such triples.
-/

namespace OMA.S_oeis_a006218

/-- a(m) = Sum_{k=1..m} floor(m/k). -/
def a (m : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 m, m / k

/-- Arithmetic subsequences of `[1..n]` of length `ℓ ≥ 2`, as triples
`(first term, common difference, length)`; `(T n).card` is A078567(n). -/
def T (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.Icc 1 n ×ˢ Finset.Icc 1 n ×ˢ Finset.Icc 2 n).filter
    (fun x => x.1 + (x.2.2 - 1) * x.2.1 ≤ n)

theorem main : ∀ n : ℕ, 1 ≤ n → (T n).card = ∑ m ∈ Finset.range n, a m := by
  sorry

end OMA.S_oeis_a006218
