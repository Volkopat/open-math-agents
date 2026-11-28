import Mathlib

/-!
# A248125: Least positive integer m such that m + n divides C(2m,m) + C(2n,n), where C(2k,k) = (2k)!/(k!)^2.

Source: https://oeis.org/A248125
Credit: @keiichisince1986-bot

A248125 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) exists for all n > 0. Moreover, for n > 66 we have a(n) < n except for n = 364, 408.

Conventions:
- `C(2k,k)` is `Nat.choose (2 * k) k`.
- Both parts are formalized. `a(n) < n` means that some `0 < m < n` works (the least one is then below
  `n`). The second part only says `a(n) < n` for the other `n > 66`; it does not assert anything about
  `n = 364, 408`.
-/

namespace OMA.S_oeis_a248125

theorem main :
    (∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧ m + n ∣ Nat.choose (2 * m) m + Nat.choose (2 * n) n) ∧
      ∀ n : ℕ, 66 < n → n ≠ 364 → n ≠ 408 →
        ∃ m : ℕ, 0 < m ∧ m < n ∧ m + n ∣ Nat.choose (2 * m) m + Nat.choose (2 * n) n := by
  sorry

end OMA.S_oeis_a248125
