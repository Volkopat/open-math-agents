import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Finite.Basic

/-!
# OEIS A268914

For every positive multiple of twelve, the conjecture asks for infinitely
many prime centers whose closest distinct prime pair summing to twice the
center has that difference.
Source: https://oeis.org/A268914
-/

namespace OMA.S_oeis_a268914

def realizesMinimalDifference (k p : ℕ) : Prop :=
  p.Prime ∧ (p - 6 * k).Prime ∧ (p + 6 * k).Prime ∧
    ∀ a b : ℕ, a.Prime → b.Prime → a < b → a + b = 2 * p → 12 * k ≤ b - a

theorem main :
    ∀ k : ℕ, 0 < k → {p : ℕ | realizesMinimalDifference k p}.Infinite := by
  sorry

end OMA.S_oeis_a268914
