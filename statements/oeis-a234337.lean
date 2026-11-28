import Mathlib

/-!
# A234337: a(n) = |{0 < k < n - 2: 4^k + 2^{phi(n-k)} - 1 is prime}|, where phi(.) is Euler's totient function.

Source: https://oeis.org/A234337
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry): Let a be 2 or 3 or 4. If n > 3, then
a^k + a^{phi(n-k)/2} - 1 is prime for some 0 < k < n - 2.

Formalization notes:
* phi = `Nat.totient`.
* For 0 < k < n - 2 we have n - k ≥ 3, so phi(n-k) is even and phi(n-k)/2 is exact.
* The base a is written b in the Lean statement; it ranges over {2, 3, 4}.
* Controls (computed): a(1..25) = 0, 0, 0, 1, 2, 3, 3, 3, 5, 5, 5, 7, 7, 8, 8, 7, 6, 8, 6, 10, 8, 5, 6,
  7, 10, as in the entry; the conjecture holds for b = 2, 3, 4 and 3 < n < 150.
-/

namespace OMA.S_oeis_a234337

/-- A234337(n). -/
def a (n : ℕ) : ℕ :=
  ((Finset.Ioo 0 (n - 2)).filter fun k => (4 ^ k + 2 ^ Nat.totient (n - k) - 1).Prime).card

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    ∀ b : ℕ, b = 2 ∨ b = 3 ∨ b = 4 → ∀ n : ℕ, 3 < n →
      ∃ k, 0 < k ∧ k < n - 2 ∧ (b ^ k + b ^ (Nat.totient (n - k) / 2) - 1).Prime := by
  sorry

end OMA.S_oeis_a234337
