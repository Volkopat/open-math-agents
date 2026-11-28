import Mathlib

namespace OMA.S_mo_121719

/-- The exponent m is admissible if one group of order p^m contains copies
of every group of order p^n. -/
def Admissible (p n m : ℕ) : Prop :=
  ∃ (G : Type) (group : Group G),
    letI : Group G := group
    Nat.card G = p ^ m ∧
      ∀ (H : Type) [Group H], Nat.card H = p ^ n →
        ∃ embed : H →* G, Function.Injective embed

/-- Kourovka Notebook Problem 18.51 on the growth of the least admissible
exponent for each fixed prime. -/
theorem main :
    ∀ p : ℕ, p.Prime →
      ∃ f : ℕ → ℕ,
        (∀ n : ℕ, IsLeast {m : ℕ | Admissible p n m} (f n)) ∧
        (∀ d : ℕ, ∃ N : ℕ, ∀ n ≥ N, n ^ d < f n) ∧
        (∀ b : ℝ, 1 < b → ∃ N : ℕ, ∀ n ≥ N, (f n : ℝ) < b ^ n) := by
  sorry

end OMA.S_mo_121719
