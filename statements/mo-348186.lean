import Mathlib

/-!
# Consecutive positive powers and powers of two

Source: https://mathoverflow.net/q/348186
Lean formalization by @witeg4.

The question uses positive natural numbers. In particular the interval has at least two
terms, and the exponent is positive, as in the author's discussion of the linear case.
-/

namespace OMA.S_mo_348186

theorem main : ∀ n u m t : ℕ, 0 < n → 0 < u → 0 < m → 0 < t →
    (∑ i ∈ Finset.range (u + 1), (n + i) ^ m) ≠ 2 ^ t := by
  sorry

end OMA.S_mo_348186
