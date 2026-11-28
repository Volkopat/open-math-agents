import OMAStatements.S_oeis_a046747

/-!
The lower estimate follows by counting matrices with two equal rows or two
equal columns and bounding their pairwise overlaps. The upper estimate is
the separate singularity bound of Hu, Song and Wu, arXiv:2609.39463v2,
Corollary 1.2, specialized to uniform entries in {0,1}.
-/

namespace OMA.R_oeis_a046747_R1

open Filter Asymptotics OMA.S_oeis_a046747
open scoped Topology

def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, 1 - ε ≤
    ((a n : ℝ) / 2 ^ (n ^ 2)) / (((n + 1).choose 2 : ℝ) * (1 / 2) ^ (n - 1))

def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    ((a n : ℝ) / 2 ^ (n ^ 2)) / (((n + 1).choose 2 : ℝ) * (1 / 2) ^ (n - 1)) ≤ 1 + ε

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a046747.main := by
  intro lower upper
  apply Asymptotics.isEquivalent_of_tendsto_one
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro x hx
    filter_upwards [lower ((1 - x) / 2) (by linarith)] with n hn
    exact (show x < 1 - (1 - x) / 2 by linarith).trans_le hn
  · intro x hx
    filter_upwards [upper ((x - 1) / 2) (by linarith)] with n hn
    exact hn.trans_lt (show 1 + (x - 1) / 2 < x by linarith)

end OMA.R_oeis_a046747_R1
