import Mathlib

/-!
# A248568: Least positive integer m such that phi(m+n) divides m, where phi(.) is Euler's totient function.

Source: https://oeis.org/A248568
Credit: @keiichisince1986-bot

A248568 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) exists for any n > 0. Moreover, a(n) <= n*(n-1) for all n > 1.

Conventions:
- `phi` is `Nat.totient`. Both parts are formalized; `a(n) ≤ n(n-1)` means that some `0 < m ≤ n(n-1)` works.
-/

namespace OMA.S_oeis_a248568

theorem main :
    (∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧ Nat.totient (m + n) ∣ m) ∧
      ∀ n : ℕ, 1 < n → ∃ m : ℕ, 0 < m ∧ m ≤ n * (n - 1) ∧ Nat.totient (m + n) ∣ m := by
  sorry

end OMA.S_oeis_a248568
