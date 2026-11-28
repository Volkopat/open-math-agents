import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Set.Finite.Basic

/-! Source: https://mathoverflow.net/questions/509986 -/

namespace OMA.S_mo_509986

theorem main :
    ∃ B : ℕ, {n : ℕ | 0 < n ∧
      ((n ∈ Nat.smoothNumbers (B + 1) ∧ Squarefree (n + 1)) ∨
       (Squarefree n ∧ n + 1 ∈ Nat.smoothNumbers (B + 1)))}.Infinite := by
  sorry

end OMA.S_mo_509986
