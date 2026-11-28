import Mathlib

/-!
# Special primes

Source: https://www.openproblemgarden.org/op/special_primes
Problem posed by George Balan.
-/

namespace OMA.S_opg_special_primes

/-- For primes `p` and `q` with `q ≡ 1 mod p`, the requested power congruence
holds exactly when `p` times the multiplicative order of 2 modulo `q`
divides `q - 1`. -/
theorem main : ∀ p q : ℕ, p.Prime → q.Prime → q ≡ 1 [MOD p] →
    (2 ^ ((q - 1) / p) ≡ 1 [MOD q] ↔ p * orderOf (2 : ZMod q) ∣ q - 1) := by
  sorry

end OMA.S_opg_special_primes
