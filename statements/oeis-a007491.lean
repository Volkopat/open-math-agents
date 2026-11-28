import Mathlib

/-!
# A007491: Smallest prime > n^2

Source: https://oeis.org/A007491
Credit: @eltociear

The source (COMMENTS) states Legendre's conjecture, still open: there is always a prime
between n^2 and (n+1)^2. It also notes that this is equivalent to a(n) < (n+1)^2, where
a(n) is the smallest prime greater than n^2, which is the sequence itself.

The statement below is Legendre's conjecture exactly: for every n >= 1 there is a prime p
with n^2 < p < (n+1)^2. The range begins at n = 1, as in the source, whose sequence has
offset 1; at n = 0 the open interval (0, 1) contains no natural number at all.
-/

namespace OMA.S_oeis_a007491

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, n ^ 2 < p ∧ p < (n + 1) ^ 2 ∧ p.Prime := by
  sorry

end OMA.S_oeis_a007491
-- ci: re-run check-proof
