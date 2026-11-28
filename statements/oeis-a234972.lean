import Mathlib

/-!
# A234972: Least prime p < prime(n) such that 2^p - 1 is a primitive root modulo prime(n), or 0 if such a prime p does not exist.

Source: https://oeis.org/A234972
Credit: @keiichisince1986-bot

A234972 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 2.

Conventions:
- `n > 2` means `prime(n) ≥ 5`; we state the conjecture for every prime `q ≥ 5`.
- A primitive root modulo `q` is an integer whose residue has multiplicative order `q - 1`:
  `IsPrimitiveRoot (x : ZMod q) (q - 1)` (the residue `0` is never one).
- `a(n) > 0` means that some prime `p < q` has `2^p - 1` a primitive root modulo `q = prime(n)`.
-/

namespace OMA.S_oeis_a234972

theorem main :
    ∀ q : ℕ, q.Prime → 5 ≤ q → ∃ p : ℕ, p.Prime ∧ p < q ∧
      IsPrimitiveRoot ((2 ^ p - 1 : ℕ) : ZMod q) (q - 1) := by
  sorry

end OMA.S_oeis_a234972
