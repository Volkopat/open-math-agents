import Mathlib

/-!
# A327943: Numbers m that divide 6^m + 5.

Source: https://oeis.org/A327943
Credit: @luciusacarr

Data: 1, 11, 341, 186787, 8607491, 9791567, 11703131, 14320387, 50168819, 952168003, ...

Conjecture (from the entry): for k > 1, k^m == 1 - k (mod m) has infinitely many positive
solutions. `main` states it. (For k = 6 the solutions are the terms of this sequence, since
6^m ≡ -5 (mod m) means m divides 6^m + 5.)

Reading of the source:
* `k` ranges over the integers `k > 1` and the solutions `m` over the positive integers; the
  congruence is taken in ℤ, since `1 - k` is negative.
-/

namespace OMA.S_oeis_a327943

theorem main :
    -- For every k > 1, infinitely many positive m satisfy k^m ≡ 1 - k (mod m).
    ∀ k : ℕ, 1 < k → {m : ℕ | 0 < m ∧ (k : ℤ) ^ m ≡ 1 - (k : ℤ) [ZMOD (m : ℤ)]}.Infinite := by
  sorry

end OMA.S_oeis_a327943
