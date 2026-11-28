import OMAStatements.S_oeis_a355407
import Mathlib

/-!
# Proof of the conjecture of OEIS A355407

`a(n) = n! * [x^n] log((1 - x)/(1 - 2*x)) / (1 - x)^4`. Conjecture of the entry (Mélika Tebni,
Jul 01 2022): `a(p) == -1 (mod p)` for every prime `p`.

Proof.
1. Put `f = (1 - x)/(1 - 2*x)` and `L = log f`, Mathlib's `logOf f`, which is `log(1 + X)` with
   `f - 1` substituted. By the chain rule for substitution, `L' = D(f - 1) * f'`, where `D` is the
   derivative of `log(1 + X)`. Since `D * (1 + X) = 1` and substitution is a ring homomorphism,
   `D(f - 1) * f = 1`.
2. Differentiating `f * (1 - 2x) = 1 - x` gives `(1 - 2x) * f' = 2f - 1`. Together with step 1,
   `L' * (1 - x) * (1 - 2x) = 1`. The series `G = Sum (2^(n+1) - 1) x^n` has the same property,
   so `L' = G`, and as the constant coefficient of `L` is `0`, `[x^k] L = (2^k - 1)/k` for every `k`
   (which reads `0` at `k = 0`).
3. `1/(1 - x)^4 = Sum C(n+3,3) x^n`, hence
   `a(n) = Sum_{k=0..n} n! * (2^k - 1)/k * C(n-k+3,3)`.
4. For `n = p` prime and `k < p`, `k` divides `(p-1)!` (for `k = 0` the term is `0`), so the term is
   `p` times an integer. The term `k = p` is `(p-1)! * (2^p - 1)`. Thus
   `a(p) = p * S + (p-1)! * (2^p - 1)` with an integer `S`.
5. By Wilson's theorem and Fermat's little theorem `(p-1)! * (2^p - 1) == (-1) * (2 - 1) = -1 (mod p)`.
-/

namespace OMA.P_oeis_a355407

open Finset PowerSeries
open OMA.S_oeis_a355407

/-- `f = (1 - x) / (1 - 2*x)`. -/
private noncomputable def f : PowerSeries ℚ := (1 - X) * (1 - 2 * X)⁻¹

private lemma f_mul : f * (1 - 2 * X) = 1 - X := by
  unfold f
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by simp), mul_one]

private lemma cc_f : constantCoeff f = 1 := by
  unfold f
  simp

private lemma hasSubst_f : HasSubst (f - 1) :=
  HasSubst.of_constantCoeff_zero' (by simp [cc_f])

/-- `(log(1+X))' * (1 + X) = 1`. -/
private lemma dlog_mul : (derivative ℚ (log ℚ)) * (1 + X) = 1 := by
  rw [deriv_log]
  ext n
  rw [mul_add, mul_one, map_add]
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_succ_mul_X, coeff_mk, coeff_mk, coeff_one]
    simp [pow_succ]

private lemma subst_one' : (1 : PowerSeries ℚ).subst (f - 1) = (1 : PowerSeries ℚ) := by
  rw [← coe_substAlgHom hasSubst_f, map_one]

/-- `(log(1+X))'` composed with `f - 1`, times `f`, is `1`. -/
private lemma dlog_subst_mul : (derivative ℚ (log ℚ)).subst (f - 1) * f = 1 := by
  have h : (derivative ℚ (log ℚ) * (1 + X)).subst (f - 1) = (1 : PowerSeries ℚ).subst (f - 1) := by
    rw [dlog_mul]
  rw [subst_mul hasSubst_f, subst_add hasSubst_f, subst_X hasSubst_f, subst_one'] at h
  have h5 : (1 : PowerSeries ℚ) + (f - 1) = f := by ring
  rw [h5] at h
  exact h

/-- Chain rule for `log f`. -/
private lemma deriv_L :
    derivative ℚ (logOf f) = (derivative ℚ (log ℚ)).subst (f - 1) * derivative ℚ f := by
  rw [logOf_eq, derivative_subst hasSubst_f, map_sub, derivative_one, sub_zero]

/-- Differentiating `f * (1 - 2X) = 1 - X`. -/
private lemma deriv_f : (1 - 2 * X) * derivative ℚ f = -1 + 2 * f := by
  have h := congrArg (derivative ℚ) f_mul
  have h2 : (1 - 2 * X : PowerSeries ℚ) = 1 - (X + X) := by ring
  rw [h2, Derivation.leibniz, map_sub, map_sub, map_add, derivative_one, derivative_X,
    smul_eq_mul, smul_eq_mul] at h
  rw [h2]
  linear_combination h

/-- `(log f)' * (1 - X) * (1 - 2X) = 1`. -/
private lemma deriv_L_mul : derivative ℚ (logOf f) * ((1 - X) * (1 - 2 * X)) = 1 := by
  have hDL := deriv_L
  have hS := dlog_subst_mul
  have hf := f_mul
  have hDf := deriv_f
  generalize derivative ℚ (logOf f) = DL at *
  generalize (derivative ℚ (log ℚ)).subst (f - 1) = S at *
  generalize derivative ℚ f = Df at *
  generalize f = F at *
  linear_combination (1 - X) * (1 - 2 * X) * hDL + (-(S * Df * (1 - 2 * X)) + 2) * hf
    + Df * (1 - 2 * X) ^ 2 * hS + (1 - 2 * X) * hDf

/-- `Sum (2^(n+1) - 1) x^n = 1 / ((1 - x) (1 - 2x))`. -/
private lemma G_mul :
    (PowerSeries.mk fun n => (2 : ℚ) ^ (n + 1) - 1) * ((1 - X) * (1 - 2 * X)) = 1 := by
  have h1 : (PowerSeries.mk fun n => (2 : ℚ) ^ (n + 1) - 1) * (1 - X) = PowerSeries.mk fun n => (2 : ℚ) ^ n := by
    ext n
    rw [mul_sub, mul_one, map_sub]
    cases n with
    | zero => simp; norm_num
    | succ n =>
      rw [coeff_succ_mul_X, coeff_mk, coeff_mk, coeff_mk]
      ring
  have h2 : (1 - 2 * X : PowerSeries ℚ) = 1 - (X + X) := by ring
  rw [← mul_assoc, h1, h2]
  ext n
  rw [mul_sub, mul_one, mul_add, map_sub, map_add]
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_succ_mul_X, coeff_mk, coeff_mk, coeff_one]
    simp [pow_succ]
    ring

private lemma deriv_L_eq : derivative ℚ (logOf f) = PowerSeries.mk fun n => (2 : ℚ) ^ (n + 1) - 1 := by
  calc derivative ℚ (logOf f)
      = derivative ℚ (logOf f) * ((PowerSeries.mk fun n => (2 : ℚ) ^ (n + 1) - 1) * ((1 - X) * (1 - 2 * X))) := by
        rw [G_mul, mul_one]
    _ = (PowerSeries.mk fun n => (2 : ℚ) ^ (n + 1) - 1) * (derivative ℚ (logOf f) * ((1 - X) * (1 - 2 * X))) := by
        ring
    _ = PowerSeries.mk fun n => (2 : ℚ) ^ (n + 1) - 1 := by rw [deriv_L_mul, mul_one]

/-- `[x^k] log((1 - x)/(1 - 2x)) = (2^k - 1)/k` (which reads `0` at `k = 0`). -/
private lemma coeff_L (k : ℕ) : coeff k (logOf f) = ((2 : ℚ) ^ k - 1) / k := by
  cases k with
  | zero =>
    rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_logOf cc_f]
    simp
  | succ n =>
    have h := congrArg (coeff n) deriv_L_eq
    rw [coeff_derivative, coeff_mk] at h
    rw [eq_div_iff (by positivity)]
    push_cast
    exact h

/-- `1/(1 - x)^4 = Sum C(n+3,3) x^n`. -/
private lemma inv_pow_four :
    ((1 - X : PowerSeries ℚ) ^ 4)⁻¹ = PowerSeries.mk fun n => ((Nat.choose (3 + n) 3 : ℕ) : ℚ) := by
  rw [PowerSeries.inv_eq_iff_mul_eq_one (by simp)]
  exact mk_add_choose_mul_one_sub_pow_eq_one (S := ℚ) (d := 3)

/-- `a(n) = Sum_{k=0..n} n! * (2^k - 1)/k * C(n-k+3,3)`. -/
private lemma a_eq (n : ℕ) :
    a n = ∑ k ∈ range (n + 1),
      (n.factorial : ℚ) * (((2 : ℚ) ^ k - 1) / k) * ((Nat.choose (3 + (n - k)) 3 : ℕ) : ℚ) := by
  have he : egf = logOf f * ((1 - X : PowerSeries ℚ) ^ 4)⁻¹ := rfl
  unfold a
  rw [he, inv_pow_four, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [coeff_L, coeff_mk, mul_assoc]

private lemma term_lt (p k : ℕ) (hk : k < p) :
    (p.factorial : ℚ) * (((2 : ℚ) ^ k - 1) / k)
      = p * (((p - 1).factorial / k : ℕ) : ℚ) * ((2 : ℚ) ^ k - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  · have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hk0.ne'
    rw [Nat.cast_div (Nat.dvd_factorial hk0 (by omega)) hkq, Nat.factorial_succ]
    push_cast
    field_simp

private lemma term_last (p : ℕ) (hp : 0 < p) :
    (p.factorial : ℚ) * (((2 : ℚ) ^ p - 1) / p) * ((Nat.choose (3 + (p - p)) 3 : ℕ) : ℚ)
      = ((p - 1).factorial : ℚ) * ((2 : ℚ) ^ p - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel, Nat.sub_self, Nat.add_zero, Nat.choose_self, Nat.cast_one, mul_one]
  rw [Nat.factorial_succ]
  push_cast
  field_simp

/-- `a(p) = p * S + (p-1)! * (2^p - 1)` with an integer `S`. -/
private lemma a_prime_eq (p : ℕ) (hp : 0 < p) :
    ∃ S : ℤ, a p = (((p : ℤ) * S + ((p - 1).factorial : ℤ) * ((2 : ℤ) ^ p - 1) : ℤ) : ℚ) := by
  refine ⟨∑ k ∈ range p,
      (((p - 1).factorial / k : ℕ) : ℤ) * ((2 : ℤ) ^ k - 1) * ((Nat.choose (3 + (p - k)) 3 : ℕ) : ℤ), ?_⟩
  rw [a_eq, sum_range_succ, term_last p hp]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_sum, Int.cast_sub, Int.cast_pow, Int.cast_natCast,
    Int.cast_ofNat, Int.cast_one]
  rw [mul_sum]
  congr 1
  refine sum_congr rfl fun k hk => ?_
  rw [term_lt p k (mem_range.mp hk)]
  ring

/-- The conjecture: `a(p) == -1 (mod p)` for every prime `p`. -/
private lemma claim (p : ℕ) (hp : p.Prime) : ∃ z : ℤ, a p = (z : ℚ) ∧ (p : ℤ) ∣ z - (-1) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hS⟩ := a_prime_eq p hp.pos
  refine ⟨(p : ℤ) * S + ((p - 1).factorial : ℤ) * ((2 : ℤ) ^ p - 1), hS, ?_⟩
  have h1 : (p : ℤ) ∣ ((p - 1).factorial : ℤ) * ((2 : ℤ) ^ p - 1) + 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.wilsons_lemma, ZMod.pow_card]
    ring
  have h4 : (p : ℤ) * S + ((p - 1).factorial : ℤ) * ((2 : ℤ) ^ p - 1) - (-1)
      = (p : ℤ) * S + (((p - 1).factorial : ℤ) * ((2 : ℤ) ^ p - 1) + 1) := by ring
  rw [h4]
  exact dvd_add (dvd_mul_right _ _) h1

end OMA.P_oeis_a355407

theorem OMA.solution : type_of% @OMA.S_oeis_a355407.main := by
  exact OMA.P_oeis_a355407.claim
