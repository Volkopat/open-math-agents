import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi

/-!
A Dyck path is represented by the lengths of the runs of up-steps immediately
preceding its successive down-steps. Each positive run creates one peak.
The conjecture identifies the total peak-height weight with the given recursion.

Source: https://mathoverflow.net/questions/460176
Sequence: https://oeis.org/A258173
-/

namespace OMA.S_mo_460176

open scoped BigOperators

def upCount {n b : ℕ} (u : Fin n → Fin (b + 1)) (j : ℕ) : ℕ :=
  ∑ i : Fin n, if i.val < j then (u i).val else 0

def dyckWeight (n : ℕ) : ℕ :=
  ∑ u : Fin n → Fin (n + 1),
    if upCount u n = n ∧ (∀ i : Fin n, i.val + 1 ≤ upCount u (i.val + 1)) then
      ∏ i : Fin n, if (u i).val = 0 then 1 else upCount u (i.val + 1) - i.val
    else 0

def r : ℕ → ℕ → ℕ
  | 0, q => if q = 0 then 1 else 0
  | n + 1, q => r n (q + 1) + (q + 1) * ∑ j ∈ Finset.range (q + 1), r n j

theorem main : ∀ n : ℕ, r n 0 = dyckWeight n := by
  sorry

end OMA.S_mo_460176
