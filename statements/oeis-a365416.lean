import Mathlib

/-!
# A365416: Numbers k such that 2*k-1 and 2*k+1 are both prime powers (A246655).

Source: https://oeis.org/A365416
Credit: @azmiozgen

Conjecture (Pillai's conjecture, as stated in the entry): k = 13 is the only term such that 2k-1
and 2k+1 both have exponent greater than 1.

Formalization notes:
* "2k-1 has exponent greater than 1" means 2k-1 = p^a for a prime p and a ≥ 2 (likewise 2k+1).
* Stated for every k ≥ 1 as an equivalence (k = 13 gives 25 = 5^2 and 27 = 3^3).
* Controls (computed): among 1 ≤ k < 2000000 only k = 13 qualifies.
-/

namespace OMA.S_oeis_a365416

/-- `k = 13` is the only `k ≥ 1` with `2k-1` and `2k+1` both proper prime powers. -/
theorem main :
    ∀ k : ℕ, 1 ≤ k →
      ((∃ p a : ℕ, p.Prime ∧ 2 ≤ a ∧ 2 * k - 1 = p ^ a) ∧
          (∃ q b : ℕ, q.Prime ∧ 2 ≤ b ∧ 2 * k + 1 = q ^ b) ↔ k = 13) := by
  sorry

end OMA.S_oeis_a365416
