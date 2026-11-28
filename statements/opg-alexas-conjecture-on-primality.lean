import Mathlib

/-!
# Alexa's conjecture on primality

Source: https://www.openproblemgarden.org/op/alexas_conjecture_on_primality
Credit: @shc261392

For a fixed natural number `p` let `r_i` be the unique integer with
`(2i+1)^(p-1) ≡ r_i (mod p)` and `0 ≤ r_i < p`, that is `r_i = (2i+1)^(p-1) % p`.

Conjecture (Alexa): a natural number `p ≥ 8` is prime if and only if
`∑_{i=1}^{⌊p^(1/3)/2⌋} r_i = ⌊p^(1/3)/2⌋`.
-/

namespace OMA.S_opg_alexas_conjecture_on_primality

theorem main : ∀ p : ℕ, 8 ≤ p →
    (p.Prime ↔
      ∑ i ∈ Finset.Icc 1 ⌊(p : ℝ) ^ ((1 : ℝ) / 3) / 2⌋₊, (2 * i + 1) ^ (p - 1) % p =
        ⌊(p : ℝ) ^ ((1 : ℝ) / 3) / 2⌋₊) := by
  sorry

end OMA.S_opg_alexas_conjecture_on_primality
