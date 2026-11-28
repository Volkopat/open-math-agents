import Mathlib

/-!
# A227249: Number of consecutive composites beginning with the first, to be added to obtain a power.

Source: https://oeis.org/A227249
Credit: @azmiozgen

Conjecture (from the entry): all the powers obtained are squares with the exception of 3^3 (for
a(2) = 4) and 6^9 (for a(6) = 4151); these are the only nonsquare powers.

Formalization notes:
* The composites are 4, 6, 8, 9, 10, ... (`Nat.nth` of "m > 1 and not prime"); S(k) is the sum of
  the first k of them. A power is m = a^b with b ≥ 2.
* Stated as: whenever S(k) (k ≥ 1) is a perfect power but not a square, S(k) is 27 or 6^9.
* Controls (computed): among k < 300000 the only k with S(k) a nonsquare perfect power are k = 4
  (S = 27) and k = 4151 (S = 10077696 = 6^9).
-/

namespace OMA.S_oeis_a227249

/-- The `i`-th composite number (0-indexed): 4, 6, 8, 9, ... -/
noncomputable def composite (i : ℕ) : ℕ := Nat.nth (fun m => 1 < m ∧ ¬ m.Prime) i

/-- The sum of the first `k` composites. -/
noncomputable def S (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, composite i

/-- The only nonsquare perfect powers among the `S(k)` are `3^3` and `6^9`. -/
theorem main :
    ∀ k : ℕ, 1 ≤ k → (∃ a b : ℕ, 2 ≤ b ∧ a ^ b = S k) → ¬ IsSquare (S k) →
      S k = 3 ^ 3 ∨ S k = 6 ^ 9 := by
  sorry

end OMA.S_oeis_a227249
