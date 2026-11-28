import Mathlib

/-!
# A conjecture on `p`-divisibility of Bernoulli numbers

Source: https://mathoverflow.net/questions/21125 (CC BY-SA 4.0).

Conjecture (mentioned in Ohta, *Companion forms and the structure of p-adic Hecke algebras*,
Example 3.3.4): for `p` an odd prime and `k` even with `2 ≤ k ≤ p - 3`, `p` cannot divide both
`B_k` and `B_{p-k+1}` (that is, their numerators).

Formalization notes:
* `B_k` is Mathlib's `bernoulli k`; all indices here are at least `2`, so the sign convention for
  `B_1` plays no role. "`p` divides `B_k`" means `p` divides the numerator `(bernoulli k).num`.
* For `p = 3` the range of `k` is empty.
* Checked numerically: no violation for primes `p < 260`.
-/

namespace OMA.S_mo_21125

/-- For an odd prime `p` and even `k` with `2 ≤ k ≤ p - 3`, `p` does not divide both the
numerators of `B_k` and `B_{p-k+1}`. -/
theorem main : ∀ p : ℕ, p.Prime → Odd p → ∀ k : ℕ, Even k → 2 ≤ k → k ≤ p - 3 →
    ¬ ((p : ℤ) ∣ (bernoulli k).num ∧ (p : ℤ) ∣ (bernoulli (p - k + 1)).num) := by
  sorry

end OMA.S_mo_21125
