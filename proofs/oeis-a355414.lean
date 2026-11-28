import OMAStatements.S_oeis_a355414
import Mathlib

/-!
# Proof of the conjecture of OEIS A355414

`a(n) = n! * [x^n] log((1 - x)/(1 - 2x)) / (1 - x)^5`. Conjecture of the entry: `a(p) == -1 (mod p)`
for every prime `p`.

Proof.
1. `D := d/dX log(1 + X) = Sum (-1)^n X^n` satisfies `(1 + X) * D = 1`.
2. Substitution is a ring homomorphism, so `(1 + g) * D.subst(g) = 1` when `g` has constant
   coefficient `0`.
3. Chain rule: `f * d/dX (logOf f) = d/dX f` when `f` has constant coefficient `1`.
4. With `u = (1 - 2X)^(-1)` and `f = (1 - X) * u`: `d/dX f = u^2`.
5. `L = Sum_{n >= 1} (2^n - 1)/n X^n` has derivative `L' = Sum (2^(n+1) - 1) X^n`, and
   `L' * ((1 - X) * (1 - 2X)) = 1`.
6. Hence `logOf f` and `L` have the same derivative and the same constant coefficient `0`, so they
   are equal.
7. `((1 - X)^5)^(-1) = Sum C(4 + n, 4) X^n`.
8. So `a(n) = n! * Sum_{k = 1..n} (2^k - 1)/k * C(4 + n - k, 4)`.
9. For a prime `p` and `0 < k < p`, `k` divides `(p-1)!`, so the `k`-th term of `a(p)` is `p` times
   an integer. The term `k = p` is `(p-1)! * (2^p - 1)`, which is `(-1) * (2 - 1) = -1` modulo `p`
   by Wilson and Fermat (both hold for `p = 2` as well).
-/

namespace OMA.P_oeis_a355414

open Finset PowerSeries
open OMA.S_oeis_a355414

/-- `log((1 - x)/(1 - 2x))` coefficientwise. -/
private noncomputable def L : PowerSeries ℚ :=
  PowerSeries.mk fun n => if n = 0 then 0 else ((2 : ℚ) ^ n - 1) / (n : ℚ)

/-- Its derivative. -/
private noncomputable def L' : PowerSeries ℚ :=
  PowerSeries.mk fun n => (2 : ℚ) ^ (n + 1) - 1

private lemma deriv_L : PowerSeries.derivative ℚ L = L' := by
  ext n
  rw [coeff_derivative]
  unfold L L'
  rw [coeff_mk, coeff_mk, if_neg (Nat.add_one_ne_zero n)]
  have h : ((n : ℚ) + 1) ≠ 0 := by positivity
  rw [Nat.cast_add, Nat.cast_one, div_mul_cancel₀ _ h]

private lemma two_eq_C : (2 : PowerSeries ℚ) = C (2 : ℚ) := (map_ofNat (C (R := ℚ)) 2).symm

private lemma geom_one : (PowerSeries.mk fun _ : ℕ => (1 : ℚ)) * (1 - X) = 1 := by
  rw [mul_comm, PowerSeries.ext_iff]
  intro n
  cases n with
  | zero => simp
  | succ n => simp [sub_mul]

private lemma geom_two : (PowerSeries.mk fun n : ℕ => (2 : ℚ) ^ n) * (1 - 2 * X) = 1 := by
  rw [two_eq_C, mul_comm, PowerSeries.ext_iff]
  intro n
  cases n with
  | zero => simp
  | succ n =>
    rw [sub_mul, one_mul, mul_assoc, map_sub, coeff_C_mul, coeff_succ_X_mul, coeff_mk, coeff_mk,
      coeff_one, if_neg (Nat.add_one_ne_zero n)]
    ring

private lemma L'_eq : L' = 2 * (PowerSeries.mk fun n : ℕ => (2 : ℚ) ^ n) -
    (PowerSeries.mk fun _ : ℕ => (1 : ℚ)) := by
  rw [two_eq_C]
  ext n
  unfold L'
  rw [map_sub, coeff_C_mul, coeff_mk, coeff_mk, coeff_mk]
  ring

private lemma L'_mul : L' * ((1 - X) * (1 - 2 * X)) = 1 := by
  rw [L'_eq]
  linear_combination (2 * (1 - X)) * geom_two - (1 - 2 * X) * geom_one

/-- Step 1: `(1 + X) * d/dX log(1 + X) = 1`. -/
private lemma one_add_X_mul_deriv_log :
    (1 + X) * PowerSeries.derivative ℚ (PowerSeries.log ℚ) = 1 := by
  rw [deriv_log]
  ext n
  cases n with
  | zero => simp
  | succ n =>
    rw [add_mul, one_mul, map_add, coeff_succ_X_mul, coeff_mk, coeff_mk, coeff_one,
      if_neg (Nat.add_one_ne_zero n)]
    simp [pow_succ]

/-- Step 2. -/
private lemma one_add_mul_subst (g : PowerSeries ℚ) (hg0 : constantCoeff g = 0) :
    (1 + g) * (PowerSeries.derivative ℚ (PowerSeries.log ℚ)).subst g = 1 := by
  have hg : HasSubst g := HasSubst.of_constantCoeff_zero' hg0
  have h1 : (1 : PowerSeries ℚ).subst g = 1 := by
    rw [← coe_substAlgHom hg, map_one]
  have h : ((1 + X) * PowerSeries.derivative ℚ (PowerSeries.log ℚ)).subst g =
      (1 : PowerSeries ℚ).subst g := by
    rw [one_add_X_mul_deriv_log]
  rw [subst_mul hg, subst_add hg, h1, subst_X hg] at h
  exact h

/-- Step 3: `f * (log f)' = f'`. -/
private lemma mul_deriv_logOf (f : PowerSeries ℚ) (hf : constantCoeff f = 1) :
    f * PowerSeries.derivative ℚ (logOf f) = PowerSeries.derivative ℚ f := by
  have hg0 : constantCoeff (f - 1) = 0 := by rw [map_sub, hf, map_one, sub_self]
  have hg : HasSubst (f - 1) := HasSubst.of_constantCoeff_zero' hg0
  have hB := one_add_mul_subst (f - 1) hg0
  have e : (1 : PowerSeries ℚ) + (f - 1) = f := by ring
  rw [e] at hB
  rw [logOf_eq, derivative_subst hg, map_sub, derivative_one, sub_zero, ← mul_assoc, hB, one_mul]

/-- Step 4. -/
private lemma deriv_quot (u : PowerSeries ℚ) (hu : u = (1 - 2 * X : PowerSeries ℚ)⁻¹) :
    PowerSeries.derivative ℚ ((1 - X) * u) = u ^ 2 := by
  have hc : constantCoeff (1 - 2 * X : PowerSeries ℚ) ≠ 0 := by simp
  have h2 : (1 - 2 * X : PowerSeries ℚ) * u = 1 := by
    rw [hu]; exact PowerSeries.mul_inv_cancel _ hc
  have hd1 : PowerSeries.derivative ℚ (1 - X : PowerSeries ℚ) = -1 := by
    rw [map_sub, derivative_one, derivative_X, zero_sub]
  have hd2 : PowerSeries.derivative ℚ (1 - 2 * X : PowerSeries ℚ) = -2 := by
    rw [two_mul, map_sub, map_add, derivative_one, derivative_X]; ring
  have hdu : PowerSeries.derivative ℚ u = 2 * u ^ 2 := by
    rw [hu, derivative_inv', hd2, ← hu]; ring
  rw [Derivation.leibniz, hdu, hd1, smul_eq_mul, smul_eq_mul]
  linear_combination u * h2

/-- Step 6. -/
private lemma logOf_eq_L : logOf ((1 - X) * (1 - 2 * X : PowerSeries ℚ)⁻¹) = L := by
  obtain ⟨u, hu⟩ : ∃ u : PowerSeries ℚ, u = (1 - 2 * X : PowerSeries ℚ)⁻¹ := ⟨_, rfl⟩
  rw [← hu]
  have hc : constantCoeff (1 - 2 * X : PowerSeries ℚ) ≠ 0 := by simp
  have h2 : (1 - 2 * X : PowerSeries ℚ) * u = 1 := by
    rw [hu]; exact PowerSeries.mul_inv_cancel _ hc
  have hf : constantCoeff ((1 - X) * u) = 1 := by
    rw [hu]; simp [PowerSeries.constantCoeff_inv]
  refine PowerSeries.derivative.ext ?_ ?_
  · have hC := mul_deriv_logOf _ hf
    rw [deriv_quot u hu] at hC
    rw [deriv_L]
    have h3 := L'_mul
    linear_combination (-(PowerSeries.derivative ℚ (logOf ((1 - X) * u)))) * h3 +
      (-(PowerSeries.derivative ℚ (logOf ((1 - X) * u)) * L' * (1 - X) * (1 - 2 * X)) +
        L' * ((1 - 2 * X) * u + 1)) * h2 + (L' * (1 - 2 * X) ^ 2) * hC
  · rw [constantCoeff_logOf hf]
    unfold L
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk, if_pos rfl]

/-- Step 7. -/
private lemma inv_pow5 : ((1 - X : PowerSeries ℚ) ^ 5)⁻¹ =
    PowerSeries.mk fun n => ((Nat.choose (4 + n) 4 : ℕ) : ℚ) := by
  have hc : constantCoeff ((1 - X : PowerSeries ℚ) ^ 5) ≠ 0 := by simp
  exact (PowerSeries.inv_eq_iff_mul_eq_one hc).mpr (mk_add_choose_mul_one_sub_pow_eq_one ℚ 4)

/-- Step 8: the explicit formula `a(n) = n! * Sum_{k=1..n} (2^k - 1)/k * C(4 + n - k, 4)`. -/
private lemma a_eq (n : ℕ) :
    a n = (n.factorial : ℚ) * ∑ k ∈ range (n + 1),
      (if k = 0 then 0 else ((2 : ℚ) ^ k - 1) / (k : ℚ)) *
        ((Nat.choose (4 + (n - k)) 4 : ℕ) : ℚ) := by
  unfold a egf
  rw [logOf_eq_L, inv_pow5, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  show coeff k L * coeff (n - k) (PowerSeries.mk fun m => ((Nat.choose (4 + m) 4 : ℕ) : ℚ)) = _
  unfold L
  rw [coeff_mk, coeff_mk]

/-- Step 9, terms `k < p`: each is `p` times an integer. -/
private lemma term_lt (p : ℕ) (hp : p.Prime) (k : ℕ) (hk : k ∈ range p) :
    ∃ w : ℤ, (p.factorial : ℚ) * ((if k = 0 then 0 else ((2 : ℚ) ^ k - 1) / (k : ℚ)) *
      ((Nat.choose (4 + (p - k)) 4 : ℕ) : ℚ)) = (((p : ℤ) * w : ℤ) : ℚ) := by
  rw [mem_range] at hk
  split_ifs with h0
  · exact ⟨0, by simp⟩
  · have hkpos : 0 < k := Nat.pos_of_ne_zero h0
    have hkle : k ≤ p - 1 := by omega
    obtain ⟨c, hc⟩ := Nat.dvd_factorial hkpos hkle
    refine ⟨(c : ℤ) * ((2 : ℤ) ^ k - 1) * ((Nat.choose (4 + (p - k)) 4 : ℕ) : ℤ), ?_⟩
    have hfac : (p.factorial : ℚ) = (p : ℚ) * ((k : ℚ) * (c : ℚ)) := by
      have h1 : p.factorial = p * (k * c) := by
        rw [← hc]
        exact (Nat.mul_factorial_pred hp.ne_zero).symm
      exact_mod_cast h1
    have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr h0
    rw [hfac, div_eq_mul_inv]
    push_cast
    linear_combination ((p : ℚ) * (c : ℚ) * ((2 : ℚ) ^ k - 1) *
      ((Nat.choose (4 + (p - k)) 4 : ℕ) : ℚ)) * mul_inv_cancel₀ hk0

/-- Step 9, the term `k = p`. -/
private lemma term_last (p : ℕ) (hp : p.Prime) :
    (p.factorial : ℚ) * ((if p = 0 then 0 else ((2 : ℚ) ^ p - 1) / (p : ℚ)) *
      ((Nat.choose (4 + (p - p)) 4 : ℕ) : ℚ)) =
      ((((p - 1).factorial : ℤ) * ((2 : ℤ) ^ p - 1) : ℤ) : ℚ) := by
  have hch : ((Nat.choose (4 + (p - p)) 4 : ℕ) : ℚ) = 1 := by
    rw [Nat.sub_self, add_zero, Nat.choose_self, Nat.cast_one]
  have hfac : (p.factorial : ℚ) = (p : ℚ) * ((p - 1).factorial : ℚ) := by
    exact_mod_cast (Nat.mul_factorial_pred hp.ne_zero).symm
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  rw [if_neg hp.ne_zero, hch, mul_one, hfac, div_eq_mul_inv]
  push_cast
  linear_combination (((p - 1).factorial : ℚ) * ((2 : ℚ) ^ p - 1)) * mul_inv_cancel₀ hpq

/-- Wilson and Fermat: `(p-1)! * (2^p - 1) == -1 (mod p)`. -/
private lemma wilson_fermat (p : ℕ) (hp : p.Prime) :
    (p : ℤ) ∣ ((p - 1).factorial : ℤ) * ((2 : ℤ) ^ p - 1) + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hW : ((((p - 1).factorial : ℤ) * ((2 : ℤ) ^ p - 1) + 1 : ℤ) : ZMod p) = 0 := by
    push_cast
    rw [ZMod.wilsons_lemma, ZMod.pow_card]
    ring
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hW

private lemma claim (p : ℕ) (hp : p.Prime) : ∃ z : ℤ, a p = (z : ℚ) ∧ (p : ℤ) ∣ z + 1 := by
  have hterm := term_lt p hp
  choose! g hg using hterm
  have hsum : (p.factorial : ℚ) * ∑ k ∈ range p,
      (if k = 0 then 0 else ((2 : ℚ) ^ k - 1) / (k : ℚ)) *
        ((Nat.choose (4 + (p - k)) 4 : ℕ) : ℚ) =
      (((p : ℤ) * ∑ k ∈ range p, g k : ℤ) : ℚ) := by
    rw [Finset.mul_sum, Finset.mul_sum, Int.cast_sum]
    exact Finset.sum_congr rfl hg
  refine ⟨(p : ℤ) * ∑ k ∈ range p, g k + ((p - 1).factorial : ℤ) * ((2 : ℤ) ^ p - 1), ?_, ?_⟩
  · rw [a_eq, Finset.sum_range_succ, mul_add, hsum, term_last p hp]
    exact (Int.cast_add _ _).symm
  · rw [add_assoc]
    exact dvd_add (dvd_mul_right _ _) (wilson_fermat p hp)

end OMA.P_oeis_a355414

theorem OMA.solution : type_of% @OMA.S_oeis_a355414.main := by
  exact OMA.P_oeis_a355414.claim
