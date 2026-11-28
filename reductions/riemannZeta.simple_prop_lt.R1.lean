import FormalConjectures.Paper.RiemannZetaZeros
import Mathlib

/-!
The strict proportion follows from two independent ingredients. `H1` is the
unconditional three-point estimate in the exact dyadic window and with the
exact zero counts used by Formal Conjectures. `H2` is the elementary
identification and lower bound for the Montgomery–Taylor constant.
-/

namespace OMA.R_riemannZeta_simple_prop_lt_R1

open Filter ZetaZeros

def H1 : Prop :=
  ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    (((149000000 *
      (3 / 2 - (Real.sqrt 2)⁻¹ *
        (Real.cos (Real.sqrt 2)⁻¹ / Real.sin (Real.sqrt 2)⁻¹)) - 99200) /
      148800133 - ε) * (N riemannZeta T (2 * T) : ℝ)
        ≤ Ns riemannZeta T (2 * T))

def H2 : Prop :=
  let H : ℝ :=
    3 / 2 - (Real.sqrt 2)⁻¹ *
      (Real.cos (Real.sqrt 2)⁻¹ / Real.sin (Real.sqrt 2)⁻¹)
  H = 2 - montgomeryTaylorConst⁻¹ ∧ (1 / 2 : ℝ) < H

theorem main : H1 → H2 → type_of% @riemannZeta.simple_prop_lt := by
  intro threePoint constantFacts
  let H : ℝ :=
    3 / 2 - (Real.sqrt 2)⁻¹ *
      (Real.cos (Real.sqrt 2)⁻¹ / Real.sin (Real.sqrt 2)⁻¹)
  change H = 2 - montgomeryTaylorConst⁻¹ ∧ (1 / 2 : ℝ) < H at constantFacts
  let B := (149000000 * H - 99200) / 148800133
  have hHB : H < B := by
    dsimp [B]
    linarith [constantFacts.2]
  obtain ⟨c, hc, hcB⟩ := exists_between hHB
  obtain ⟨T₀, hT₀⟩ := threePoint (B - c) (sub_pos.mpr hcB)
  refine ⟨c, constantFacts.1 ▸ hc, fun T => if T₀ ≤ T then 0 else c, ?_, ?_⟩
  · apply
      (Asymptotics.isLittleO_zero (1 : ℝ → ℝ) atTop).congr'
        ?_ Filter.EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop T₀] with T hT using (if_pos hT).symm
  · intro T _
    by_cases hT : T₀ ≤ T
    · simpa [hT, B, H] using hT₀ T hT
    · simp [hT]

end OMA.R_riemannZeta_simple_prop_lt_R1
