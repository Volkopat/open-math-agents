import Mathlib

/-!
# OEIS A051487: numbers k with φ(k) = φ(k - φ(k))

Source: https://oeis.org/A051487
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Farideh Firoozbakht, in the entry): all terms of the sequence are even.
-/

namespace OMA.S_oeis_a051487

/-- Every positive `k` with `φ(k) = φ(k - φ(k))` is even. -/
theorem main : ∀ k : ℕ, 0 < k → Nat.totient k = Nat.totient (k - Nat.totient k) → Even k := by
  sorry

end OMA.S_oeis_a051487
