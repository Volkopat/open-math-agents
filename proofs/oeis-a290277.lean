import OMAStatements.S_oeis_a290277
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The inverse Euler transform of the Motzkin numbers

Let M be the Motzkin series and R = 1 + XM'/M. The first-step recurrence gives
M = 1 + XM + X²M². Differentiation yields D R = 1 with D = 1 − X − 2X²M,
and squaring D gives 1 − 2X − 3X². The resulting differential equation for R
recovers the central trinomial recurrence. Möbius inversion then gives
Mathar's formula for the individual Euler exponents.

The generating-function identity also appears in OEIS A002426 and A001006.

This proof is a credited port of @wtho704's complete companion to statement
PR #22674, published at commit f3539210549a45ac432700539358a0bb222c515b:
https://github.com/wtho704/open-math-agents/blob/f3539210549a45ac432700539358a0bb222c515b/proofs/oeis-a290277.lean
The mathematical proof below is retained unchanged. R. J. Mathar posed the
conjecture; Alexander Burstein recorded the underlying generating-function identity.
-/

namespace MotzkinEuler

open OMA.S_oeis_a290277

section
open Polynomial

lemma centralTrinomial_cast (n : ℕ) :
    (centralTrinomial n : ℚ) = ((1 + X + X^2 : ℚ[X])^n).coeff n := by
  have h := Polynomial.coeff_map (p := (1 + X + X^2 : ℕ[X])^n) (Nat.castRingHom ℚ) n
  simpa [centralTrinomial] using h.symm

/-- The coefficient of degree n+2 in XQ' − (n+2)Q vanishes. Applying this to
Q = (X²−1)(1+X+X²)^(n+1) gives the central trinomial recurrence. -/
theorem centralTrinomial_recurrence (n : ℕ) :
    (n+2:ℚ) * centralTrinomial (n+2) =
      (2*(n:ℚ)+3)*centralTrinomial (n+1)+3*(n+1:ℚ)*centralTrinomial n := by
  let P : ℚ[X] := 1 + X + X^2
  let Q : ℚ[X] := (X^2-1)*P^(n+1)
  have hp : derivative P = 1+2*X := by
    dsimp [P]
    simp [Polynomial.derivative_pow_succ]
    ring
  have hq : X * derivative Q - C (n+2 : ℚ) * Q =
      C (n+2 : ℚ)*P^(n+2) - C (2*(n:ℚ)+3)*(X*P^(n+1)) - C (3*(n+1:ℚ))*(X^2*P^n) := by
    dsimp only [Q]
    rw [Polynomial.derivative_mul, Polynomial.derivative_pow_succ, hp, Polynomial.derivative_sub,
      Polynomial.derivative_X_pow, Polynomial.derivative_one]
    simp only [map_add, map_mul, map_natCast, map_ofNat, map_one,
      Nat.reduceSub, pow_one, sub_zero, pow_succ P (n+1), pow_succ P n]
    dsimp only [P]
    ring
  have eq := congrArg (fun S : ℚ[X] => S.coeff (n+2)) hq
  simp only [Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_derivative,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul] at eq
  push_cast at eq
  rw [centralTrinomial_cast, centralTrinomial_cast, centralTrinomial_cast]
  change (n+2:ℚ)*(P^(n+2)).coeff (n+2) = _
  linear_combination -eq

end

open PowerSeries

theorem motzkin_equation :
    motzkinSeries = 1 + X * motzkinSeries + X * (X * (motzkinSeries * motzkinSeries)) := by
  ext n
  cases n with
  | zero => simp [motzkinSeries, motzkin, coeff_zero_eq_constantCoeff_apply]
  | succ n =>
    cases n with
    | zero =>
      simp only [map_add, coeff_succ_X_mul, coeff_zero_X_mul, coeff_one, if_false,
        one_ne_zero, zero_add, add_zero, motzkinSeries, coeff_mk]
      norm_num [motzkin]
    | succ n =>
      simp only [map_add, coeff_succ_X_mul, coeff_one, Nat.succ_ne_zero, if_false, zero_add]
      rw [coeff_mul]
      simp only [motzkinSeries, coeff_mk]
      rw [motzkin, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => (motzkin i : ℚ) * motzkin j) n]
      push_cast
      exact congrArg ((motzkin (n+1) : ℚ) + ·)
        (Fin.sum_univ_eq_sum_range (fun i => (motzkin i : ℚ) * motzkin (n-i)) (n+1))

noncomputable def normalized : ℚ⟦X⟧ := 1 + X * derivative ℚ motzkinSeries * motzkinSeries⁻¹

/-- The differential equation characterizing the central trinomial generating function. -/
theorem normalized_ode :
    (1 - 2*X - 3*X^2) * derivative ℚ normalized = (1 + 3*X) * normalized := by
  let M := motzkinSeries
  let F := X * M
  let D := 1 - X - 2*X*F
  have hc : constantCoeff M = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    simp [M, motzkinSeries, motzkin]
  have hM : M ≠ 0 := by
    intro h
    rw [h, map_zero] at hc
    exact zero_ne_one hc
  have hm : M = 1 + F + F^2 := by
    dsimp only [F, M]
    calc
      _ = _ := motzkin_equation
      _ = _ := by ring
  have hf : F = X * (1 + F + F^2) := congrArg (fun z => X*z) hm
  have dsquare : D^2 = 1 - 2*X - 3*X^2 := by
    dsimp only [D]
    linear_combination (-4 * X) * hf
  have df : D * derivative ℚ F = M := by
    have he := congrArg (derivative ℚ) hf
    simp only [map_add, sq, Derivation.leibniz, derivative_one, derivative_X, smul_eq_mul] at he
    dsimp only [D]
    linear_combination he - hm
  have rm : normalized * M = derivative ℚ F := by
    change (1 + X * derivative ℚ M * M⁻¹) * M = derivative ℚ (X*M)
    rw [Derivation.leibniz, derivative_X]
    simp only [smul_eq_mul, mul_one]
    calc
      _ = M + X * derivative ℚ M * (M⁻¹ * M) := by ring
      _ = _ := by rw [MvPowerSeries.inv_mul_cancel M (by change constantCoeff M ≠ 0; rw [hc]; norm_num)]; ring
  have dr : D * normalized = 1 := by
    apply mul_right_cancel₀ hM
    rw [mul_assoc, rm, df, one_mul]
  have dd : D * derivative ℚ D = -(1 + 3*X) := by
    have two_ne : (2 : ℚ⟦X⟧) ≠ 0 := by
      intro h
      have h' := congrArg (constantCoeff (R := ℚ)) h
      rw [show (2 : ℚ⟦X⟧) = 1 + 1 by norm_num, map_add, map_one, map_zero] at h'
      norm_num at h'
    apply mul_left_cancel₀ two_ne
    have he := congrArg (derivative ℚ) dsquare
    have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := (derivative ℚ).map_natCast 2
    have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := (derivative ℚ).map_natCast 3
    simp only [map_sub, sq, Derivation.leibniz, derivative_one, derivative_X, d2, d3,
      smul_eq_mul] at he
    linear_combination he
  have hprod := congrArg (derivative ℚ) dr
  simp only [Derivation.leibniz, smul_eq_mul, derivative_one] at hprod
  rw [← dsquare]
  linear_combination D * hprod - normalized * dd

theorem coeff_normalized (n : ℕ) : coeff n normalized = centralTrinomial n := by
  let R := normalized
  let V := derivative ℚ R
  have shifts :
      V = X*V + X*V + X*(X*V) + X*(X*V) + X*(X*V) + R + X*R + X*R + X*R := by
    change derivative ℚ normalized = _
    dsimp only [R, V]
    linear_combination normalized_ode
  have rzero : coeff 0 R = 1 := by
    simp [R, normalized, coeff_zero_eq_constantCoeff_apply]
  induction n using Nat.twoStepInduction with
  | zero => simpa [centralTrinomial] using rzero
  | one =>
    have eq := congrArg (coeff 0) shifts
    simp only [map_add, coeff_zero_X_mul, rzero, zero_add, add_zero] at eq
    simpa [V, coeff_derivative, R, centralTrinomial, Polynomial.coeff_one] using eq
  | more n ih0 ih1 =>
    have eq := congrArg (coeff (n+1)) shifts
    simp only [map_add, coeff_succ_X_mul] at eq
    have shift (m : ℕ) : (coeff m) (X * V) = (m : ℚ) * coeff m R := by
      cases m with
      | zero => simp [coeff_zero_X_mul]
      | succ m => rw [coeff_succ_X_mul]; simp [V, coeff_derivative, mul_comm]
    simp only [shift, V, coeff_derivative] at eq
    change coeff (n+2) R = _
    change coeff n R = _ at ih0
    change coeff (n+1) R = _ at ih1
    have tri := centralTrinomial_recurrence n
    rw [← ih0, ← ih1] at tri
    apply mul_right_cancel₀ (by positivity : (n : ℚ)+2 ≠ 0)
    push_cast at eq
    linear_combination eq - tri

theorem logCoeffs_eq {n : ℕ} (hn : 0 < n) : logCoeffs n = centralTrinomial n := by
  have h := coeff_normalized n
  simpa [normalized, logCoeffs, coeff_one, hn.ne'] using h

/-- Summing the recursively determined weights over all divisors recovers the input. -/
theorem sum_eulerWeight (g : ℕ → ℚ) (n : ℕ) (hn : 0 < n) :
    ∑ d ∈ n.divisors, eulerWeight g d = g n := by
  rw [← Nat.insert_self_properDivisors hn.ne', Finset.sum_insert Nat.self_notMem_properDivisors]
  rw [eulerWeight.eq_def g n, Finset.sum_attach]
  ring

end MotzkinEuler

theorem OMA.solution : type_of% @OMA.S_oeis_a290277.main := by
  intro n hn
  have hd (m : ℕ) (hm : 0 < m) :
      ∑ d ∈ m.divisors, OMA.S_oeis_a290277.eulerWeight OMA.S_oeis_a290277.logCoeffs d =
        OMA.S_oeis_a290277.centralTrinomial m :=
    (MotzkinEuler.sum_eulerWeight _ m hm).trans (MotzkinEuler.logCoeffs_eq hm)
  have hi := ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp hd n hn
  rw [Nat.sum_divisorsAntidiagonal (fun u v => (ArithmeticFunction.moebius u : ℚ) * OMA.S_oeis_a290277.centralTrinomial v)] at hi
  unfold OMA.S_oeis_a290277.a
  rw [← hi]
  field_simp

