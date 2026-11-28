import Mathlib

/-!
# A079322: Composite numbers of the form 1^1 * 2^2 * 3^3 * 4^4 * ... * n^n + 11.

Source: https://oeis.org/A079322
Credit: @eltociear

The source states, in its COMMENTS section:
  No primes of this form in the sequence for n <= 60. Conjecture: There are no primes in the
  sequence 2^2 * 3^3 * 4^4 * ... * n^n + 1 for n > 3. Conjecture: There are no primes in the
  sequence 2^2 * 3^3 * 4^4 * ... * n^n + 11 for all n. Conjecture: There are no primes in the
  sequence 2^2 * 3^3 * 4^4 * ... * n^n + 61 for all n.

The sequence A079322 itself, described in its NAME, is the list of composite numbers of the form
1^1 * 2^2 * 3^3 * ... * n^n + 11, and its DATA line begins 12, 15, 119, 27659, 86400011, so the
offset is n = 1 (with 1^1 * 2^2 * ... * 1^1 + 11 = 12). The first of the three conjectures in
COMMENTS is the one stated here: with the product taken over 2, 3, ..., n for n > 3, adding 1
never gives a prime.

Reading of the product. The product 2^2 * 3^3 * 4^4 * ... * n^n is the product of k^k over the
integers k with 2 <= k <= n, written below as Finset.prod (Finset.Icc 2 n) (fun k => k ^ k). This
is the product as the source writes it, starting at 2^2 rather than at 1^1; the factor 1^1 = 1
in the NAME changes nothing, but the product is written here exactly as in the conjecture. The
range is n > 3 as in the source, i.e. 3 < n. For n <= 3 the same expression is prime (n = 2
gives 5, n = 3 gives 109), which is exactly why the source excludes them.

Check that the statement is not trivially false: the values for n = 4, ..., 25 are all composite
(n = 4 already gives 27649 = 43 * 643), and the source reports that there are no primes of this
form for n <= 60; the conjecture is that there is none at all.
-/

namespace OMA.S_oeis_a079322

theorem main : ∀ n : ℕ, 3 < n →
    ¬ Nat.Prime ((Finset.prod (Finset.Icc 2 n) (fun k : ℕ => k ^ k)) + 1) := by
  sorry

end OMA.S_oeis_a079322
-- ci: re-run check-proof
