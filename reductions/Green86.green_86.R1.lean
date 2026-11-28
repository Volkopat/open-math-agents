import FormalConjectures.GreensOpenProblems.«86»
import Mathlib

-- Reduction Green86.green_86.R1
-- Credit: @marcusbuffett

/-!
# Green 86 (Komlós–Ruzsa): the range `c > 1/2`

A classical case: for every `c > 1/2` and all large `n`, some dilation `θ` puts at most `n^c` of
the points `θ a mod 1` into every interval of length `1/n`. Second moment over the dilations
`θ = j/P` (`P` a prime above every difference of `A`): each nonzero difference is within `1/n`
of an integer for at most `2(P/n + 1)` values of `j`, so some `j` has at most `4n` close ordered
pairs, while `m` points in one interval give `m(m-1)` close pairs; hence `m ≤ 1 + 2√n`. This is
`H1`. The open core `H2` is the range `0 < c ≤ 1/2` (Komlós, Ruzsa and Szemerédi reached
`c > 1/3`).
-/

namespace OMA.R_Green86_green_86_R1
open Green86

/-- The range `c > 1/2`, given by the second-moment argument over the dilations `j/P`. -/
def H1 : Prop :=
  ∀ c : ℝ, 1 / 2 < c → ∃ n₀ : ℕ, ∀ A : Finset ℤ, n₀ ≤ A.card →
    ∃ θ : ℝ, ∀ t : ℝ, (numInInterval A θ t : ℝ) ≤ (A.card : ℝ) ^ c

/-- The open core: the range `0 < c ≤ 1/2`. -/
def H2 : Prop :=
  ∀ c : ℝ, 0 < c → c ≤ 1 / 2 → ∃ n₀ : ℕ, ∀ A : Finset ℤ, n₀ ≤ A.card →
    ∃ θ : ℝ, ∀ t : ℝ, (numInInterval A θ t : ℝ) ≤ (A.card : ℝ) ^ c

theorem main : H1 → H2 → type_of% @Green86.green_86 := by
  intro h1 h2 c hc
  rcases le_or_gt c (1 / 2) with h | h
  · exact h2 c hc h
  · exact h1 c h

end OMA.R_Green86_green_86_R1
