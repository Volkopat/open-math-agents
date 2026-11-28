import FormalConjectures.ErdosProblems.«158»
import Mathlib

-- Reduction Erdos158.erdos_158.R1 of Erdős Problem 158
-- Credit: @marcusbuffett
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős 158: the Sidon case, and the open rest

The question asks whether every infinite `B₂[2]` set `A ⊆ ℕ` has
`liminf |A ∩ [0, N)| / √N = 0`. A `B₂[1]` set is a Sidon set (`Erdos158.b2_one`), and every
Sidon set is `B₂[2]`. This separates the classical Sidon case from the open part. It is a
classical result, not progress on the question itself.

* `H1` (Erdős): every infinite Sidon set `A` has `liminf |A ∩ [0, N)| / √N = 0`. Proof sketch:
  the positive differences of a Sidon set are pairwise distinct, so at most `2D` ordered pairs
  of `A` lie at distance below `D`. Cut `[0, D K^J)` into blocks of length `D`; Cauchy-Schwarz
  on the block counts over each range of blocks `[K^j, K^(j+1))` shows that if
  `|A ∩ [0, N)| ≥ c √N` from some point on, each of the `J` ranges contributes at least
  `D / K` to the sum of squared block counts, while the pair bound caps that sum by `4 D`.
* `H2`: the same for infinite `B₂[2]` sets that are not Sidon sets. This is the open part.
-/

open Filter Real

namespace OMA.R_Erdos158_erdos_158_R1

/-- Erdős: an infinite Sidon set has `liminf |A ∩ [0, N)| / √N = 0`. -/
def H1 : Prop :=
  ∀ A : Set ℕ, A.Infinite → IsSidon A →
    liminf (fun N : ℕ => (A ∩ .Iio N).ncard * (N : ℝ) ^ (- 1 / 2 : ℝ)) atTop = 0

/-- The open part: infinite `B₂[2]` sets that are not Sidon sets. -/
def H2 : Prop :=
  ∀ A : Set ℕ, A.Infinite → Erdos158.B2 2 A → ¬ IsSidon A →
    liminf (fun N : ℕ => (A ∩ .Iio N).ncard * (N : ℝ) ^ (- 1 / 2 : ℝ)) atTop = 0

theorem main : H1 → H2 → type_of% @Erdos158.erdos_158 := by
  intro h1 h2 A hinf hB
  by_cases hS : IsSidon A
  · exact h1 A hinf hS
  · exact h2 A hinf hB hS

end OMA.R_Erdos158_erdos_158_R1
