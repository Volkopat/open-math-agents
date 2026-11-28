import OMAStatements.S_oeis_a203914

/-!
# A203914: the two directions, without the Unique Games Conjecture
Credit: @my-other-github-account

The target is `UGC → ((∃ α > alphaGW, ApproximatesMaxCut α) ↔ P = NP)`. Both directions are
known to hold without the Unique Games Conjecture:

* H1 (hardness). An approximation ratio above `alphaGW` in polynomial time gives P = NP. The
  OpenAI formalization `OAI.OptimalMaxCut.main` (openai/math, commit 3344da59991e, Apache-2.0)
  proves that, for every `α` with `alphaGW < α ≤ 1`, binary 3SAT has a polynomial-time gap
  reduction to Max Cut on simple unweighted graphs. Such an `α`-approximate cut decides 3SAT,
  and with Cook–Levin it decides every NP language.
* H2 (algorithm). If P = NP, an optimal cut is found in polynomial time by prefix self-reduction,
  so the ratio `1` is attained.

`main` supplies the remaining fact `alphaGW < 1`: at `ρ = -1/2` the Goemans–Williamson quotient is
`2 · (2π/3) / (π · 3/2) = 8/9`, and every quotient is nonnegative.
-/

namespace OMA.R_oeis_a203914_R1

open OMA.S_oeis_a203914

def H1 : Prop :=
  ∀ α : ℝ, alphaGW < α → ApproximatesMaxCut α → P = NP

def H2 : Prop :=
  P = NP → ApproximatesMaxCut 1

lemma alphaGW_lt_one : alphaGW < 1 := by
  have hmem : (8 / 9 : ℝ) ∈ ((fun ρ : ℝ => 2 * Real.arccos ρ / (Real.pi * (1 - ρ))) ''
      Set.Ico (-1 : ℝ) 1) := by
    refine ⟨-1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    have h : Real.arccos (-1 / 2) = 2 * Real.pi / 3 := by
      have h3 : Real.arccos (1 / 2) = Real.pi / 3 := by
        rw [← Real.cos_pi_div_three]
        exact Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])
      rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.arccos_neg, h3]
      ring
    simp only [h]
    field_simp
    ring
  have hbdd : BddBelow ((fun ρ : ℝ => 2 * Real.arccos ρ / (Real.pi * (1 - ρ))) ''
      Set.Ico (-1 : ℝ) 1) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨ρ, ⟨-, hρ⟩, rfl⟩
    apply div_nonneg
    · exact mul_nonneg (by norm_num) (Real.arccos_nonneg ρ)
    · exact mul_nonneg Real.pi_pos.le (by linarith)
  calc alphaGW ≤ 8 / 9 := csInf_le hbdd hmem
    _ < 1 := by norm_num

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a203914.main := by
  intro h1 h2 _
  constructor
  · rintro ⟨α, hα, happ⟩
    exact h1 α hα happ
  · intro hpnp
    exact ⟨1, alphaGW_lt_one, h2 hpnp⟩

end OMA.R_oeis_a203914_R1
