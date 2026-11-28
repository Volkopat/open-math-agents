import OMAReductions.R_Transcendental_transcendental_gamma_one_div_three_R1

-- Reduction Transcendental.transcendental_gamma_one_div_three.R1.H1.R1 of step
-- Transcendental.transcendental_gamma_one_div_three.R1.H1
-- Credit: @arindale

/-!
`H1` of reduction `R1` states that `π` and the CM period `∫₀¹ dx/√(1-x³)` are
algebraically independent.  For a two-element family this is exactly: `π` is
transcendental and the period is transcendental over `ℚ(π)` (Mathlib's
`AlgebraicIndependent.option_iff`).  We split the statement along that equivalence:
`H1` below is the (classical, Lindemann–Weierstrass) transcendence of `π`, and `H2`
is Chudnovsky's deep input, that the period is transcendental over `ℚ(π)`.
-/

namespace OMA.R_Transcendental_transcendental_gamma_one_div_three_R1_H1_R1

open Real

/-- `π` is transcendental (Lindemann–Weierstrass). -/
def H1 : Prop := Transcendental ℚ π

/-- Chudnovsky (1976): the period `∫₀¹ dx/√(1-x³)` of the CM curve `y² = 1 - x³`
is transcendental over `ℚ(π)`. -/
def H2 : Prop :=
  Transcendental (Algebra.adjoin ℚ ({π} : Set ℝ))
    (∫ x in (0 : ℝ)..1, 1 / √(1 - x ^ 3))

/-- Reindexing `Bool` by `Option (Fin 1)`. -/
private def e : Bool ≃ Option (Fin 1) where
  toFun b := if b then some 0 else none
  invFun o := o.isSome
  left_inv b := by cases b <;> rfl
  right_inv o := by
    cases o with
    | none => rfl
    | some i =>
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      rfl

theorem main : H1 → H2 →
    OMA.R_Transcendental_transcendental_gamma_one_div_three_R1.H1 := by
  intro h1 h2
  have hsing : AlgebraicIndependent ℚ (fun _ : Fin 1 => π) := by
    rw [algebraicIndependent_unique_type_iff]
    exact h1
  have hopt : AlgebraicIndependent ℚ
      (fun o : Option (Fin 1) => o.elim (∫ x in (0 : ℝ)..1, 1 / √(1 - x ^ 3))
        (fun _ => π)) := by
    refine (hsing.option_iff_transcendental
      (∫ x in (0 : ℝ)..1, 1 / √(1 - x ^ 3))).mpr ?_
    have hrange : Set.range (fun _ : Fin 1 => π) = ({π} : Set ℝ) := Set.range_const
    rw [hrange]
    exact h2
  have hcomp :
      (fun o : Option (Fin 1) => o.elim (∫ x in (0 : ℝ)..1, 1 / √(1 - x ^ 3))
        (fun _ => π)) ∘ e =
      fun b : Bool => if b then π else ∫ x in (0 : ℝ)..1, 1 / √(1 - x ^ 3) := by
    funext b
    cases b <;> rfl
  exact (algebraicIndependent_equiv' e hcomp).mpr hopt

end OMA.R_Transcendental_transcendental_gamma_one_div_three_R1_H1_R1
