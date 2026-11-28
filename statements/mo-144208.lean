import Mathlib

/-!
# If (1^a + ⋯ + n^a)^b = 1^c + ⋯ + n^c for some n, then (a, b, c) = (1, 2, 3)?

Source: https://mathoverflow.net/questions/144208 (CC BY-SA 4.0).

Conjecture: for natural numbers `a, c` and `b ≥ 2`, `n ≥ 2`, if
`(∑_{k=1}^n k^a)^b = ∑_{k=1}^n k^c`, then `(a, b, c) = (1, 2, 3)`.
Natural numbers are positive, as in the poser's convention.
-/

namespace OMA.S_mo_144208

theorem main : ∀ a b c n : ℕ, 0 < a → 2 ≤ b → 0 < c → 2 ≤ n →
    (∑ k ∈ Finset.Icc 1 n, k ^ a) ^ b = ∑ k ∈ Finset.Icc 1 n, k ^ c → (a, b, c) = (1, 2, 3) := by
  sorry

end OMA.S_mo_144208
