import Mathlib

/-!
# A073272: Zeros of prime(n+1) - floor(prime(n) * prime(n+2) / prime(n+1))

Source: https://oeis.org/A073272
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

a(n) = prime(n+1) - floor(prime(n) * prime(n+2) / prime(n+1)).
Conjecture: a(n) = 0 iff floor(prime(n) * prime(n+2) / prime(n+1)) in {3, 7, 23}.
-/

namespace OMA.S_oeis_a073272

/-- The `n`-th prime (1-indexed: `prime1 1 = 2`). -/
noncomputable def prime1 (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n - 1)

/-- `A073271(n) = floor(prime(n) * prime(n+2) / prime(n+1))`. -/
noncomputable def b (n : ℕ) : ℕ :=
  (prime1 n * prime1 (n + 2)) / prime1 (n + 1)

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      ((prime1 (n + 1) : ℤ) - (b n : ℤ) = 0 ↔ b n = 3 ∨ b n = 7 ∨ b n = 23) := by
  sorry

end OMA.S_oeis_a073272
