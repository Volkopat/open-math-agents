import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Congruence (3) of https://mathoverflow.net/questions/137989 -/

open Finset

namespace OMA.S_mo_137989

def trinomial (n k l : ℕ) : ℕ :=
  n.choose (k + l) * (k + l).choose k

def apery (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), ∑ l ∈ range (n - k + 1),
    trinomial n k l ^ 2 * trinomial (n + k + l) k l ^ 2

theorem main :
    ∀ p n : ℕ, p.Prime → 0 < n → apery (n * p - 1) ≡ apery (n - 1) [MOD p ^ 3] := by
  sorry

end OMA.S_mo_137989
