import Mathlib

/-!
# A congruence conjecture regarding (r-s)⁴ - 1 ≡ 0 (mod 4r²s)

Source: https://mathoverflow.net/questions/181683 (CC BY-SA 4.0).

Conjecture: if `r > s ≥ 1` are coprime integers with `(r - s)⁴ - 1 ≡ 0 (mod 4r²s)`, then
`r - s = 1` or `2r > 3s`. The divisibility is taken in `ℤ`.
-/

namespace OMA.S_mo_181683

theorem main : ∀ r s : ℕ, 1 ≤ s → s < r → Nat.Coprime r s →
    (4 * (r : ℤ) ^ 2 * s ∣ ((r : ℤ) - s) ^ 4 - 1) → r - s = 1 ∨ 3 * s < 2 * r := by
  sorry

end OMA.S_mo_181683
