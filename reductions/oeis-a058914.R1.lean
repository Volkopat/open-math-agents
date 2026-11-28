import OMAStatements.S_oeis_a058914
import Mathlib

/-! A058914 asks for the number of fixed points in [0, 1] of the continuous solutions of
Minkowski's functional equations f(x/(x+1)) = f(x)/2 and f(1 - x) = 1 - f(x) (whose unique
solution is the question-mark function); the conjecture is that there are exactly five.

The lower bound is classical. The equations alone determine f on the Stern-Brocot rationals:
f(0) = 0, f(1/2) = 1/2, f(1) = 1, and following 2/3, 2/5, 2/7, 5/7 and 1/3, 1/4, 3/4 one gets
f(5/12) = 13/32 < 5/12 and f(3/7) = 7/16 > 3/7, so the intermediate value theorem gives a fixed
point x0 in (5/12, 3/7) and the symmetry gives a fifth, 1 - x0. H1 is this bound for every
continuous solution. That there are no further fixed points (H2) is the open part. -/

namespace OMA.R_oeis_a058914_R1

open Set

/-- Every continuous solution of Minkowski's equations has at least five fixed points in [0, 1]. -/
def H1 : Prop :=
  ∀ f : ℝ → ℝ, ContinuousOn f (Icc 0 1) →
    (∀ x ∈ Icc (0 : ℝ) 1, f (x / (x + 1)) = f x / 2) →
    (∀ x ∈ Icc (0 : ℝ) 1, f (1 - x) = 1 - f x) →
    5 ≤ {x ∈ Icc (0 : ℝ) 1 | f x = x}.encard

/-- The open part: no continuous solution has more than five fixed points in [0, 1]. -/
def H2 : Prop :=
  ∀ f : ℝ → ℝ, ContinuousOn f (Icc 0 1) →
    (∀ x ∈ Icc (0 : ℝ) 1, f (x / (x + 1)) = f x / 2) →
    (∀ x ∈ Icc (0 : ℝ) 1, f (1 - x) = 1 - f x) →
    {x ∈ Icc (0 : ℝ) 1 | f x = x}.encard ≤ 5

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a058914.main := by
  intro h1 h2 f hf e1 e2
  have h : {x ∈ Icc (0 : ℝ) 1 | f x = x}.encard = 5 :=
    le_antisymm (h2 f hf e1 e2) (h1 f hf e1 e2)
  rw [Set.ncard_def, h]
  rfl

end OMA.R_oeis_a058914_R1
