import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Finite.Basic

/-! Source: https://mathoverflow.net/questions/509684 -/

namespace OMA.S_mo_509684

def divisibleCount (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun k => n ∣ n.choose k)).card

theorem main : Set.Infinite {n : ℕ | 1 < n ∧ ¬ n.Prime ∧
    ∀ t : ℕ, 0 < t → t < n → divisibleCount t < divisibleCount n} := by
  sorry

end OMA.S_mo_509684
