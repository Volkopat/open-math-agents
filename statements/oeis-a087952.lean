import Mathlib

/-!
# A087952: Smallest prime == 1 (mod n) and > n^2.

Source: https://oeis.org/A087952
Credit: @keiichisince1986-bot

A087952 is the sequence `a(n)` named in the title. The entry states:
Since A014085(n) ~ n/log(n) one may conjecture that a(n) < 2*n^2 for all n > 1. - M. F. Hasler,
Feb 27 2020

Conventions:
- `a(n) < 2n^2` means that some prime `p` with `p ≡ 1 (mod n)` satisfies `n^2 < p < 2n^2`.
-/

namespace OMA.S_oeis_a087952

theorem main :
    ∀ n : ℕ, 1 < n → ∃ p : ℕ, p.Prime ∧ p % n = 1 ∧ n ^ 2 < p ∧ p < 2 * n ^ 2 := by
  sorry

end OMA.S_oeis_a087952
