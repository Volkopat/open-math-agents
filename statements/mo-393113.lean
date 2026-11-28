import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Finite.Basic

/-! Source: https://mathoverflow.net/questions/393113 -/

open scoped BigOperators

namespace OMA.S_mo_393113

/-- The starting position of run k, where the first run and entry have index zero. -/
def runStart (s : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, s i

/-- A sequence over 1 and 2 whose successive run lengths equal its own entries. -/
def IsKolakoski (s : ℕ → ℕ) : Prop :=
  (∀ i, s i = 1 ∨ s i = 2) ∧
  ∀ k j : ℕ, j < s k →
    s (runStart s k + j) = if k % 2 = 0 then 1 else 2

/-- Infinitely many positive-length prefixes contain equally many ones and twos. -/
theorem main :
    ∃ s : ℕ → ℕ, IsKolakoski s ∧
      {n : ℕ | 0 < n ∧
        ((Finset.range n).filter fun i => s i = 1).card =
          ((Finset.range n).filter fun i => s i = 2).card}.Infinite := by
  sorry

end OMA.S_mo_393113
