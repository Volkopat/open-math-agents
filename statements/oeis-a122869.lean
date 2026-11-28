import Mathlib.Data.Nat.Prime.Basic

namespace OMA.S_oeis_a122869

/-- The Lucas numbers `A000032`: `L(0) = 2`, `L(1) = 1`, `L(n + 2) = L(n + 1) + L(n)`. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n

/-- OEIS A122869 conjecture (Charles R. Greathouse IV, May 25 2011): an odd prime `p` divides
`L((p - 1) / 2)` if and only if `p ≡ 11` or `19 (mod 20)`. -/
theorem main :
    ∀ p : ℕ, p.Prime → Odd p →
      (p ∣ lucas ((p - 1) / 2) ↔ p % 20 = 11 ∨ p % 20 = 19) := by
  sorry

end OMA.S_oeis_a122869
