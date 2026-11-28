import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Nat.Totient

/-! Source: https://mathoverflow.net/questions/452005 -/

namespace OMA.S_mo_452005

theorem main :
    Set.Infinite {m : ℕ | (∃ n : ℕ, m = 2 ^ n + 1) ∧ m.Coprime m.totient} := by
  sorry

end OMA.S_mo_452005
