import Mathlib

/-!
# A301510: Smallest positive number b such that ((b+1)^prime(n) + b^prime(n))/(2*b + 1) is prime, or 0 if no such b exists.

Source: https://oeis.org/A301510
Credit: @keiichisince1986-bot

A301510 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for every n > 1.

Conventions:
- `n > 1` means that `p = prime(n)` is an odd prime; we state the conjecture for every odd prime `p`.
- For odd `p`, `2b + 1 = (b + 1) + b` divides `(b + 1)^p + b^p`, so the natural-number division is exact.
-/

namespace OMA.S_oeis_a301510

theorem main :
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∃ b : ℕ, 0 < b ∧ (((b + 1) ^ p + b ^ p) / (2 * b + 1)).Prime := by
  sorry

end OMA.S_oeis_a301510
