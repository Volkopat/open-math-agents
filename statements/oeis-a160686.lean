import Mathlib

/-!
# A160686: Numbers n such that n/A000005(A000045(n)) is an integer.

Source: https://oeis.org/A160686
Credit: @luciusacarr

The entry records one conjecture (Max Alekseyev, May 21 2011): the sequence is finite and
complete, i.e. its terms are exactly the listed 1, 2, 4, 8, 16, 32, 64. (The source notes that
128 is not a term, as 128 / d(F(128)) = 1/2, and that a further term would exceed 3000.)

Reading of the source:
* `A000045(n) = F(n) = Nat.fib n` and `A000005(m) = d(m)`, the number of divisors of `m`.
  "`n / d(F(n))` is an integer" means `d(F(n)) ∣ n`.
* `n` ranges over the positive integers (offset 1; `n = 0` would give `F(0) = 0`, which has no
  meaningful divisor count).
* "Finite and complete" is stated as: the set of terms equals {1, 2, 4, 8, 16, 32, 64}.
-/

namespace OMA.S_oeis_a160686

theorem main :
    {n : ℕ | 0 < n ∧ (Nat.fib n).divisors.card ∣ n} = {1, 2, 4, 8, 16, 32, 64} := by
  sorry

end OMA.S_oeis_a160686
