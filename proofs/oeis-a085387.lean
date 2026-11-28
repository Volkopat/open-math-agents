import OMAStatements.S_oeis_a085387
import Mathlib

namespace ExponentialRecurrence

open PowerSeries OMA.S_oeis_a085387

private noncomputable def D := d⁄dX ℚ
private noncomputable def pos : ℚ⟦X⟧ := exp ℚ * (exp ℚ).subst u
private noncomputable def neg : ℚ⟦X⟧ := exp ℚ * (exp ℚ).subst (-u)

private noncomputable def op (f : ℚ⟦X⟧) : ℚ⟦X⟧ :=
  D (D (D f)) - 3 * D (D f) + (2 - 2 * X - X ^ 2) * D f + (X ^ 2 - X - 3) * f

private theorem deriv_u : D u = 1 + X := by
  simp only [D, u, map_add, derivative_X, Derivation.leibniz, derivative_C,
    derivative_pow, smul_eq_mul, mul_one, mul_zero, add_zero]
  have hc : C (1 / 2 : ℚ) * 2 = (1 : ℚ⟦X⟧) := by
    rw [← map_ofNat (C (R := ℚ)) 2, ← map_mul]
    norm_num
  linear_combination X * hc

private theorem u_constant : constantCoeff u = 0 := by
  simp only [u, map_add, map_mul, map_pow, constantCoeff_X, zero_pow (by decide : 2 ≠ 0),
    mul_zero, add_zero]

private theorem deriv_pos : D pos = (2 + X) * pos := by
  have hs : HasSubst u := HasSubst.of_constantCoeff_zero u_constant
  simp only [pos, D, Derivation.leibniz, derivative_exp, derivative_subst hs, smul_eq_mul]
  rw [show (d⁄dX ℚ) u = 1 + X from deriv_u]
  ring

private theorem deriv_neg : D neg = -X * neg := by
  have hzero : constantCoeff (-u) = 0 := by rw [map_neg, u_constant, neg_zero]
  have hs : HasSubst (-u) := HasSubst.of_constantCoeff_zero hzero
  simp only [neg, D, Derivation.leibniz, derivative_exp, derivative_subst hs, smul_eq_mul,
    map_neg]
  rw [show (d⁄dX ℚ) u = 1 + X from deriv_u]
  ring

private theorem pos_op : op pos = 0 := by
  have dc : D (2 + X) = 1 := by simp [D, ← map_ofNat (C (R := ℚ)) 2]
  have dc₂ : D ((2 + X) ^ 2 + 1) = 2 * (2 + X) := by
    simp only [D, map_add, derivative_pow, derivative_one, add_zero, show (2 : ℕ) - 1 = 1 by decide, pow_one,
      show (d⁄dX ℚ) (2 + X) = 1 from dc, mul_one, Nat.cast_ofNat]
  have h₂ : D (D pos) = ((2 + X) ^ 2 + 1) * pos := by
    rw [deriv_pos]
    simp only [D, Derivation.leibniz, smul_eq_mul,
      show (d⁄dX ℚ) (2 + X) = 1 from dc, show (d⁄dX ℚ) pos = _ from deriv_pos, mul_one]
    ring
  have h₃ : D (D (D pos)) = ((2 + X) ^ 3 + 3 * (2 + X)) * pos := by
    rw [h₂]
    simp only [D, Derivation.leibniz, smul_eq_mul,
      show (d⁄dX ℚ) ((2 + X) ^ 2 + 1) = _ from dc₂,
      show (d⁄dX ℚ) pos = _ from deriv_pos]
    ring
  unfold op
  rw [h₃, h₂, deriv_pos]
  ring

private theorem neg_op : op neg = 0 := by
  have dc : D (-X) = -1 := by simp [D]
  have dc₂ : D (X ^ 2 - 1) = 2 * X := by
    simp only [D, map_sub, derivative_pow, derivative_X, derivative_one,
      show (2 : ℕ) - 1 = 1 by decide, pow_one, mul_one, sub_zero, Nat.cast_ofNat]
  have h₂ : D (D neg) = (X ^ 2 - 1) * neg := by
    rw [deriv_neg]
    simp only [D, Derivation.leibniz, smul_eq_mul,
      show (d⁄dX ℚ) (-X) = _ from dc, show (d⁄dX ℚ) neg = _ from deriv_neg]
    ring
  have h₃ : D (D (D neg)) = (-X ^ 3 + 3 * X) * neg := by
    rw [h₂]
    simp only [D, Derivation.leibniz, smul_eq_mul,
      show (d⁄dX ℚ) (X ^ 2 - 1) = _ from dc₂,
      show (d⁄dX ℚ) neg = _ from deriv_neg]
    ring
  unfold op
  rw [h₃, h₂, deriv_neg]
  ring

private theorem egf_op : op egf = 0 := by
  have h : egf = C (1 / 2 : ℚ) * (pos + neg) := by
    unfold egf pos neg
    ring
  have hlin (c : ℚ) (f g : ℚ⟦X⟧) : op (C c * (f + g)) = C c * (op f + op g) := by
    unfold op
    simp only [D, Derivation.leibniz, smul_eq_mul, derivative_C, map_add, mul_zero, add_zero]
    ring
  rw [h, hlin, pos_op, neg_op, add_zero, mul_zero]

private theorem scaled (j r : ℕ) :
    (j.factorial : ℚ) * coeff j (D^[r] egf) = a (j + r) := by
  rw [show coeff j (D^[r] egf) = _ from coeff_iterate_derivative egf r j, a]
  have hf : (j.factorial : ℚ) * ((j + 1).ascFactorial r : ℚ) = ((j + r).factorial : ℚ) := by
    exact_mod_cast Nat.factorial_mul_ascFactorial j r
  rw [← hf]
  ring

private theorem scaledShift (j r d : ℕ) :
    ((j + d).factorial : ℚ) * coeff (j + d) ((D^[r] egf) * X ^ d) =
      ((j + 1).ascFactorial d : ℚ) * a (j + r) := by
  rw [coeff_mul_X_pow, ← Nat.factorial_mul_ascFactorial]
  push_cast
  rw [mul_comm (j.factorial : ℚ), mul_assoc, scaled]

private theorem recurrence (t : ℕ) (ht : 2 ≤ t) :
    a (t + 3) - 3 * a (t + 2) + 2 * a (t + 1) + (-2 * (t : ℚ) - 3) * a t -
      (t : ℚ) ^ 2 * a (t - 1) + (t : ℚ) * ((t : ℚ) - 1) * a (t - 2) = 0 := by
  let F (k : ℕ) := D^[k] egf
  have hx : op egf =
      F 3 - C (3 : ℚ) * F 2 + C (2 : ℚ) * F 1 - C (2 : ℚ) * (F 1 * X) -
        F 1 * X ^ 2 + F 0 * X ^ 2 - F 0 * X - C (3 : ℚ) * F 0 := by
    unfold op F
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, map_ofNat]
    ring
  have h := congrArg (fun z => (t.factorial : ℚ) * coeff t z) (hx.symm.trans egf_op)
  simp only [map_add, map_sub, coeff_C_mul, map_zero, mul_zero] at h
  let T (r : ℕ) := (t.factorial : ℚ) * coeff t (F r)
  let S (r : ℕ) := (t.factorial : ℚ) * coeff t (F r * X)
  let U (r : ℕ) := (t.factorial : ℚ) * coeff t (F r * X ^ 2)
  have he : T 3 - 3 * T 2 + 2 * T 1 - 2 * S 1 - U 1 + U 0 - S 0 - 3 * T 0 = 0 := by
    dsimp [T, S, U]
    linear_combination h
  have hT (r : ℕ) : T r = a (t + r) := scaled t r
  have hS (r : ℕ) : S r = (t : ℚ) * a (t - 1 + r) := by
    have hh := scaledShift (t - 1) r 1
    rw [show t - 1 + 1 = t by omega, pow_one] at hh
    simpa [S, F, Nat.ascFactorial_succ] using hh
  have hU (r : ℕ) : U r = (t : ℚ) * ((t : ℚ) - 1) * a (t - 2 + r) := by
    have hh := scaledShift (t - 2) r 2
    rw [show t - 2 + 2 = t by omega, Nat.ascFactorial_succ,
      show t - 2 + 1 + 1 = t by omega] at hh
    simp only [Nat.ascFactorial_succ, Nat.ascFactorial_zero, Nat.add_zero, Nat.mul_one, Nat.cast_mul] at hh
    rw [show t - 2 + 1 = t - 1 by omega, Nat.cast_sub (by omega : 1 ≤ t), Nat.cast_one] at hh
    simpa [U, F, mul_comm (t : ℚ) ((t : ℚ) - 1)] using hh
  rw [hT, hT, hT, hT, hS, hS, hU, hU] at he
  rw [show t - 1 + 1 = t by omega, show t - 2 + 1 = t - 1 by omega,
    Nat.add_zero, Nat.add_zero, Nat.add_zero] at he
  linear_combination he

end ExponentialRecurrence

theorem OMA.solution : type_of% @OMA.S_oeis_a085387.main := by
  intro n hn
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 3 := ⟨n - 3, by omega⟩
  have h := ExponentialRecurrence.recurrence t (by omega)
  rw [show t + 3 - 1 = t + 2 by omega, show t + 3 - 2 = t + 1 by omega,
    show t + 3 - 3 = t by omega, show t + 3 - 4 = t - 1 by omega,
    show t + 3 - 5 = t - 2 by omega]
  push_cast
  linear_combination h