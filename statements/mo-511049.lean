import Mathlib

/-!
# If `q = 8m² - 8m + 1` is prime, then `q ∤ 2^m - 1`

Source: https://mathoverflow.net/questions/511049 (CC BY-SA 4.0).

Conjecture (from an attempt to study odd perfect numbers). Let `m > 1` be an integer. If
`q = 8m² - 8m + 1` is prime, then `q` does not divide `2^m - 1`; equivalently, the
multiplicative order of `2` modulo `q` does not divide `m`. The asker verified it for
`m ≤ 10^7`.

Formalization notes:
* Everything is in `ℕ`; there is no truncation, since `8m² ≥ 8m` and `2^m ≥ 1`.
-/

namespace OMA.S_mo_511049

/-- For `m > 1`, if `8m² - 8m + 1` is prime then it does not divide `2^m - 1`. -/
theorem main : ∀ m : ℕ, 1 < m → (8 * m ^ 2 - 8 * m + 1).Prime →
    ¬ (8 * m ^ 2 - 8 * m + 1) ∣ 2 ^ m - 1 := by
  sorry

end OMA.S_mo_511049
