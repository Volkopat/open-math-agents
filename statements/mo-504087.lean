import Mathlib

/-!
# Motzkin-greedy differences and the Conway–Guy sequence

Source: https://mathoverflow.net/questions/504087
Credit: @Mapika

Popov asks whether the first differences of Conway–Guy satisfy the given
positive-mex recursion from the initial pair 1, 1. This formulation substitutes
the proposed sequence into the recursion, which uniquely determines each new
term from earlier ones. The radius is floor(sqrt(2i) + 1/2).
-/

namespace OMA.S_mo_504087

def radius (i : ℕ) : ℕ := (Nat.sqrt (8 * i) + 1) / 2

def conwayGuy : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * conwayGuy (n + 1) - conwayGuy (n + 1 - radius (n + 1))
termination_by n => n
decreasing_by all_goals omega

def diff (i : ℕ) : ℕ := conwayGuy i - conwayGuy (i - 1)

def forbidden (n : ℕ) (x : ℕ) : Prop :=
  ∃ h : ℕ → ℕ, h 0 = 0 ∧ h (n - 1) = 0 ∧
    (∀ i : ℕ, i + 1 < n → Nat.dist (h i) (h (i + 1)) ≤ 1) ∧
    (∃ i ∈ Finset.Ico 1 (n - 1), 0 < h i) ∧
    x = ∑ i ∈ Finset.Ico 1 (n - 1), h i * diff i

theorem main : diff 1 = 1 ∧ diff 2 = 1 ∧ ∀ n : ℕ, 3 ≤ n →
    0 < diff n ∧ ¬ forbidden n (diff n) ∧ ∀ x : ℕ, 0 < x → x < diff n → forbidden n x := by
  sorry

end OMA.S_mo_504087
