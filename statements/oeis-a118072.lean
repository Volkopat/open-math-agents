import Mathlib

/-!
# OEIS A118072: Primes which are the sum of a twin prime pair - 1.

Source: https://oeis.org/A118072
Credit: @unserus

OEIS comment (C. R. Greathouse IV): "Dickson's conjecture implies this sequence is infinite."
The open statement is that the sequence is infinite. A twin prime pair is `(p, p + 2)` with both
prime; the term is `p + (p + 2) - 1` (e.g. `3 + 5 - 1 = 7`, the first term).
-/

namespace OMA.S_oeis_a118072

/-- The terms of A118072: primes `q = p + (p + 2) - 1` where `(p, p + 2)` is a twin prime pair. -/
def a118072Set : Set ℕ :=
  {q : ℕ | q.Prime ∧ ∃ p : ℕ, p.Prime ∧ (p + 2).Prime ∧ q = p + (p + 2) - 1}

/-- A118072 is infinite. -/
theorem main : a118072Set.Infinite := by
  sorry

end OMA.S_oeis_a118072
