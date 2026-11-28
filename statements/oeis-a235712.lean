import Mathlib

/-!
# A235712: Least prime p < prime(n) with 2^p + 1 a quadratic nonresidue modulo prime(n), or 0 if such a prime p does not exist.

Source: https://oeis.org/A235712
Credit: @keiichisince1986-bot

A235712 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 3.

Conventions:
- `n > 3` means `q = prime(n) ≥ 7`; we state the conjecture for every prime `q ≥ 7`.
- A quadratic nonresidue modulo `q` is a residue that is not a square in `ZMod q` (`0` is a square, so it is
  excluded automatically).
-/

namespace OMA.S_oeis_a235712

theorem main :
    ∀ q : ℕ, q.Prime → 7 ≤ q → ∃ p : ℕ, p.Prime ∧ p < q ∧ ¬ IsSquare ((2 ^ p + 1 : ℕ) : ZMod q) := by
  sorry

end OMA.S_oeis_a235712
