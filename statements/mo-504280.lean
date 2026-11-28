import Mathlib

/-!
# Consecutive integers with digit-disjoint factors

Jack Edward Tisdell asks whether a single base admits arbitrarily long runs of
consecutive cute integers. The digit restriction compares the two factors.

Source: https://mathoverflow.net/questions/504280 (CC BY-SA 4.0).
Lean formalization: @vubui.
-/

namespace OMA.S_mo_504280

/-- Both factors exceed one and have no digit in common in base `b`. -/
def IsCute (b n : ℕ) : Prop :=
  ∃ x y : ℕ, 1 < x ∧ 1 < y ∧ x * y = n ∧
    List.Disjoint (Nat.digits b x) (Nat.digits b y)

theorem main :
    ∃ b : ℕ, 2 ≤ b ∧ ∀ length : ℕ, ∃ start : ℕ, 0 < start ∧
      ∀ offset : ℕ, offset < length → IsCute b (start + offset) := by
  sorry

end OMA.S_mo_504280
