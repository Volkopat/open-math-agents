import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.Basic

/-!
The partition count η(s,n,m) permits at most n parts, each of size at most m.
The question asks whether the weighted sum has the sign of nL−nR on the
stated domain 0 < uc < s and 0 < nL,nR ≤ s−uc.

Source: https://mathoverflow.net/questions/486510
-/

namespace OMA.S_mo_486510

open scoped BigOperators

def eta : ℕ → ℕ → ℤ → ℕ
  | 0, _, s => if s = 0 then 1 else 0
  | _, 0, s => if s = 0 then 1 else 0
  | n + 1, m + 1, s =>
    let capacity : ℤ := ((n + 1) * (m + 1) : ℕ)
    if s < 0 ∨ capacity < s then 0
    else if s = capacity then 1
    else eta (n + 1) m s + eta n (m + 1) (s - ((m + 1 : ℕ) : ℤ))
termination_by n m _ => n + m
decreasing_by all_goals omega

def weightedSum (s uc nL nR : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (s - uc + 1),
    let j := s - uc - i
    ((i : ℤ) - j) * (eta nL uc i : ℤ) * eta nR uc j

theorem main :
    ∀ s uc nL nR : ℕ, 0 < uc → uc < s →
      0 < nL → nL ≤ s - uc → 0 < nR → nR ≤ s - uc →
      (weightedSum s uc nL nR).sign = ((nL : ℤ) - nR).sign := by
  sorry

end OMA.S_mo_486510
