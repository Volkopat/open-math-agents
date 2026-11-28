import Mathlib

/-!
# A249061: a(n) is the least number of successive numbers 1, 2, 3, ... which when added to n produce a prime number.

Source: https://oeis.org/A249061
Credit: @keiichisince1986-bot

A249061 is the sequence `a(n)` named in the title. The entry states:
Do we know that a(n) always exists? - N. J. A. Sloane, Oct 20 2014
Conjecturally (Hardy & Littlewood conjecture F), a(n) exists for all n. - Charles R Greathouse IV,
Oct 21 2014 (The statement below is the unconditional claim.)

Conventions:
- The offset is `0`. Adding `1, 2, …, k` to `n` gives `n + k(k + 1)/2`; at least one number is added
  (`a(0) = 2`, `a(2) = 1` in the data), so `k ≥ 1`.
-/

namespace OMA.S_oeis_a249061

theorem main :
    ∀ n : ℕ, ∃ k : ℕ, 0 < k ∧ (n + k * (k + 1) / 2).Prime := by
  sorry

end OMA.S_oeis_a249061
