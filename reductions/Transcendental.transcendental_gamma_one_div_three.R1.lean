import FormalConjectures.Wikipedia.Transcendental
import Mathlib

-- Reduction Transcendental.transcendental_gamma_one_div_three.R1: Gamma(1/3) is transcendental
-- Source: G. V. Chudnovsky, Algebraic independence of constants connected with the exponential
--   and the elliptic functions, Dokl. Akad. Nauk Ukrain. SSR Ser. A 8 (1976), 698-701; see also
--   M. Waldschmidt, Transcendence of periods: the state of the art, Pure Appl. Math. Q. 2 (2006).
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Transcendence of `Γ(1/3)` from Chudnovsky's theorem on periods

Chudnovsky's theorem (1976): if a Weierstrass elliptic function has algebraic invariants and
complex multiplication, then `π` and any nonzero period `ω` are algebraically independent over `ℚ`.
For the curve `y² = 1 - x³` (complex multiplication by `ℤ[ρ]`) the number
`∫₀¹ dx / √(1 - x³) = 1.40218…` is a nonzero algebraic multiple of a period.

* `H1` (Chudnovsky, the deep input): `π` and `∫₀¹ dx / √(1 - x³)` are algebraically independent
  over `ℚ`. This is the theorem in its original form, about periods; it does not mention the
  Gamma function.
* `H2` (Euler's Beta integral, elementary): `∫₀¹ dx / √(1 - x³) = Γ(1/3) Γ(1/2) / (3 Γ(5/6))`,
  by the substitution `t = x³`, which turns the integral into `B(1/3, 1/2) / 3`.

Both hypotheses are shared character for character with
`Transcendental.transcendental_gamma_one_div_six.R1`.

`main`: the reflection formula at `1/6` and `1/3` and the duplication formula at `1/6` give
`π · ω = Γ(1/3)³ · √3 · 2^(2/3) / 12`. If `Γ(1/3)` were algebraic, the monomial `π · ω` would be
algebraic, contradicting `H1`.
-/

namespace OMA.R_Transcendental_transcendental_gamma_one_div_three_R1

open Real

/-- Chudnovsky (1976): `π` and the period `∫₀¹ dx / √(1 - x³)` of the CM curve `y² = 1 - x³`
are algebraically independent over `ℚ`. -/
def H1 : Prop :=
  AlgebraicIndependent ℚ
    (fun b : Bool => if b then π else ∫ x in (0 : ℝ)..1, 1 / √(1 - x ^ 3))

/-- Euler's Beta integral: `∫₀¹ dx / √(1 - x³) = B(1/3, 1/2) / 3 = Γ(1/3) Γ(1/2) / (3 Γ(5/6))`. -/
def H2 : Prop :=
  ∫ x in (0 : ℝ)..1, 1 / √(1 - x ^ 3) =
    Real.Gamma (1 / 3) * Real.Gamma (1 / 2) / (3 * Real.Gamma (5 / 6))

/-- A monomial `x ^ m * y ^ n` with `0 < m` in two algebraically independent reals is
transcendental. -/
lemma monomial_ne {x y a : ℝ}
    (ind : AlgebraicIndependent ℚ (fun b : Bool => if b then x else y))
    (ha : IsAlgebraic ℚ a) (m n : ℕ) (hm : 0 < m) : x ^ m * y ^ n ≠ a := by
  intro h
  have indK : AlgebraicIndependent (algebraicClosure ℚ ℝ) (fun b : Bool => if b then x else y) :=
    ind.algebraicClosure
  let a' : algebraicClosure ℚ ℝ := ⟨a, mem_algebraicClosure_iff.mpr ha⟩
  have hp : MvPolynomial.aeval (fun b : Bool => if b then x else y)
      (MvPolynomial.X true ^ m * MvPolynomial.X false ^ n - MvPolynomial.C a' :
        MvPolynomial Bool (algebraicClosure ℚ ℝ)) = 0 := by
    have : algebraMap (algebraicClosure ℚ ℝ) ℝ a' = a := rfl
    simp [this, h]
  have p0 := indK.eq_zero_of_aeval_eq_zero _ hp
  have e0 := congrArg (MvPolynomial.eval (fun _ => (0 : algebraicClosure ℚ ℝ))) p0
  have e1 := congrArg (MvPolynomial.eval (fun _ => (1 : algebraicClosure ℚ ℝ))) p0
  simp [hm.ne'] at e0 e1
  rw [e0] at e1
  simp at e1

/-- The algebra behind `main`: reflection at `1/6` (`e1`) and `1/3` (`e3`), duplication at `1/6`
(`e2`) and the Beta evaluation (`e4`). -/
lemma period_identity {P I G S F T q r w : ℝ} (hG : 0 < G) (hS : 0 < S) (_hF : 0 < F) (hT : 0 < T)
    (hq : 0 < q) (hw : 0 < w) (hq2 : q ^ 2 = P)
    (e1 : S * F = 2 * P) (e2 : S * T = G * r * q) (e3 : G * T * w = 2 * P)
    (e4 : I = G * q / (3 * F)) : P * I = G ^ 3 * w * r / 12 := by
  subst hq2
  have hT' : T = 2 * q ^ 2 / (G * w) := by field_simp; linarith
  have hS' : S = G * r * q / T := by field_simp; linarith
  have hF' : F = 2 * q ^ 2 / S := by field_simp; linarith
  rw [e4, hF', hS', hT']
  field_simp
  ring

theorem main : H1 → H2 → type_of% @Transcendental.transcendental_gamma_one_div_three := by
  intro h1 h2 hG
  have hw : IsAlgebraic ℚ (√3 : ℝ) := by
    refine IsAlgebraic.of_pow (n := 2) (by norm_num) ?_
    rw [Real.sq_sqrt (by norm_num)]
    exact isAlgebraic_algebraMap (3 : ℚ)
  have hr3 : ((2 : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hr : IsAlgebraic ℚ ((2 : ℝ) ^ (2 / 3 : ℝ)) := by
    refine IsAlgebraic.of_pow (n := 3) (by norm_num) ?_
    rw [hr3]
    exact isAlgebraic_algebraMap (4 : ℚ)
  have ha : IsAlgebraic ℚ
      (Real.Gamma (1 / 3) ^ 3 * √3 * (2 : ℝ) ^ (2 / 3 : ℝ) * algebraMap ℚ ℝ (1 / 12)) :=
    (((hG.pow 3).mul hw).mul hr).mul (isAlgebraic_algebraMap _)
  have e1 := Real.Gamma_mul_Gamma_one_sub (1 / 6)
  have e2 := Real.Gamma_mul_Gamma_add_half (1 / 6)
  have e3 := Real.Gamma_mul_Gamma_one_sub (1 / 3)
  rw [show (1 : ℝ) - 1 / 6 = 5 / 6 by norm_num, show π * (1 / 6) = π / 6 by ring,
    Real.sin_pi_div_six] at e1
  rw [show (1 : ℝ) / 6 + 1 / 2 = 2 / 3 by norm_num, show (2 : ℝ) * (1 / 6) = 1 / 3 by norm_num,
    show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num] at e2
  rw [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num, show π * (1 / 3) = π / 3 by ring,
    Real.sin_pi_div_three] at e3
  have h3 : (0 : ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num)
  have key := period_identity (P := π) (I := ∫ x in (0 : ℝ)..1, 1 / √(1 - x ^ 3))
    (G := Real.Gamma (1 / 3)) (S := Real.Gamma (1 / 6)) (F := Real.Gamma (5 / 6))
    (T := Real.Gamma (2 / 3)) (q := √π) (r := (2 : ℝ) ^ (2 / 3 : ℝ)) (w := √3)
    (Real.Gamma_pos_of_pos (by norm_num)) (Real.Gamma_pos_of_pos (by norm_num))
    (Real.Gamma_pos_of_pos (by norm_num)) (Real.Gamma_pos_of_pos (by norm_num))
    (Real.sqrt_pos.mpr Real.pi_pos) h3
    (Real.sq_sqrt Real.pi_pos.le) (by rw [e1]; ring) (by rw [e2])
    (by rw [e3]; field_simp)
    (by rw [h2, Real.Gamma_one_half_eq])
  refine monomial_ne h1 ha 1 1 one_pos ?_
  rw [pow_one, pow_one, key]
  simp [div_eq_mul_inv]

end OMA.R_Transcendental_transcendental_gamma_one_div_three_R1
