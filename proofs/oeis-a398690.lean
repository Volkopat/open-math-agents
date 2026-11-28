import OMAStatements.S_oeis_a398690

/-!
Proof of OEIS A398690 (palindromicity of Verlinde-number row numerators):
1. Express `rowValue n k` as the `(n + 1)`-st Taylor coefficient of the rational
   generating function `(-1)^k * Z * U_{2k}(Z) / (1 - (-1)^k * T_{2k+1}(Z))` by
   matching the `2k + 1` reciprocal roots of `1 - (-1)^k * T_{2k+1}(Z)` (with double
   roots at `s_0, ..., s_{k-1}` and simple root at `s_k`) and differentiating in `R[X]`.
2. Expand `(-1)^k * T_{2k+1}` and `(-1)^k * X * U_{2k}` explicitly in `Q[Y]` via
   Chebyshev's zero-evaluation recurrence, lifting the series inverse to `(Q[Y])[[Z]]`.
3. Deduce `rowValue n k = (R_n).eval (k : Q)` for a polynomial `R_n` with `deg <= n`
   and `(R_n).eval (-x - 1) = (-1)^n * (R_n).eval x`, then apply `(n + 1)`-fold forward
   differences `Delta^[n + 1] R_n = 0`.
-/

private lemma negOnePow_cast (k : ℕ) : ((k : ℤ).negOnePow : ℚ) = (-1 : ℚ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp [Int.negOnePow_add, ih, pow_succ]

private noncomputable def A_coeff (r : ℕ) : Polynomial ℚ :=
  Polynomial.C ((-1 : ℚ) ^ r / ((2 * r + 1).factorial : ℚ)) * Polynomial.X *
    ∏ t ∈ Finset.range r, (Polynomial.X ^ 2 - Polynomial.C ((2 * (t : ℚ) + 1) ^ 2))

private noncomputable def B_coeff (r : ℕ) : Polynomial ℚ :=
  Polynomial.C ((-1 : ℚ) ^ r / ((2 * r).factorial : ℚ)) *
    ∏ t ∈ Finset.range r, (Polynomial.X ^ 2 - Polynomial.C ((2 * (t : ℚ) + 1) ^ 2))

private lemma A_coeff_natDegree (r : ℕ) : (A_coeff r).natDegree ≤ 2 * r + 1 := by
  unfold A_coeff
  refine le_trans Polynomial.natDegree_mul_le ?_
  have h1 : (Polynomial.C ((-1 : ℚ) ^ r / ((2 * r + 1).factorial : ℚ)) * Polynomial.X).natDegree ≤
      1 := by
    refine le_trans Polynomial.natDegree_mul_le ?_
    rw [Polynomial.natDegree_C, Polynomial.natDegree_X]
  have h2 : (∏ t ∈ Finset.range r,
      (Polynomial.X ^ 2 - Polynomial.C ((2 * (t : ℚ) + 1) ^ 2))).natDegree ≤ 2 * r := by
    refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
    calc
      ∑ t ∈ Finset.range r,
          (Polynomial.X ^ 2 - Polynomial.C ((2 * (t : ℚ) + 1) ^ 2)).natDegree
          ≤ ∑ _t ∈ Finset.range r, 2 := by
            refine Finset.sum_le_sum fun t _ => ?_
            refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
            rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_C]
            norm_num
      _ = 2 * r := by simp [mul_comm]
  omega

private lemma B_coeff_natDegree (r : ℕ) : (B_coeff r).natDegree ≤ 2 * r := by
  unfold B_coeff
  refine le_trans Polynomial.natDegree_mul_le ?_
  have h1 : (Polynomial.C ((-1 : ℚ) ^ r / ((2 * r).factorial : ℚ))).natDegree = 0 :=
    Polynomial.natDegree_C _
  have h2 : (∏ t ∈ Finset.range r,
      (Polynomial.X ^ 2 - Polynomial.C ((2 * (t : ℚ) + 1) ^ 2))).natDegree ≤ 2 * r := by
    refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
    calc
      ∑ t ∈ Finset.range r,
          (Polynomial.X ^ 2 - Polynomial.C ((2 * (t : ℚ) + 1) ^ 2)).natDegree
          ≤ ∑ _t ∈ Finset.range r, 2 := by
            refine Finset.sum_le_sum fun t _ => ?_
            refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
            rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_C]
            norm_num
      _ = 2 * r := by simp [mul_comm]
  omega

private lemma A_coeff_comp_neg (r : ℕ) :
    (A_coeff r).comp (-Polynomial.X) = -A_coeff r := by
  unfold A_coeff
  simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp, Polynomial.prod_comp,
    Polynomial.sub_comp, Polynomial.pow_comp, neg_sq]
  ring

private lemma B_coeff_comp_neg (r : ℕ) :
    (B_coeff r).comp (-Polynomial.X) = B_coeff r := by
  unfold B_coeff
  simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.prod_comp,
    Polynomial.sub_comp, Polynomial.pow_comp, Polynomial.X_comp, neg_sq]

private lemma poly_deriv_coeff (p : Polynomial ℚ) : ∀ d : ℕ,
    (Polynomial.derivative p).coeff d = ((d + 1 : ℕ) : ℚ) * p.coeff (d + 1) := by
  induction p using Polynomial.induction_on' with
  | add p q ihp ihq =>
    intro d
    simp only [Polynomial.derivative_add, Polynomial.coeff_add, ihp d, ihq d]
    ring
  | monomial n a =>
    intro d
    rw [Polynomial.derivative_monomial, Polynomial.coeff_monomial, Polynomial.coeff_monomial]
    rcases n with _ | n
    · simp
    · rw [Nat.add_one_sub_one]
      rcases eq_or_ne n d with rfl | hnd
      · simp
        ring
      · simp [hnd]

private lemma iterate_derivative_eval_zero (d : ℕ) : ∀ P : Polynomial ℚ,
    (Polynomial.derivative^[d] P).eval 0 = (d.factorial : ℚ) * P.coeff d := by
  induction d with
  | zero =>
    intro P
    rw [Function.iterate_zero_apply, Nat.factorial_zero, Nat.cast_one, one_mul,
      Polynomial.coeff_zero_eq_eval_zero]
  | succ d ih =>
    intro P
    rw [Function.iterate_succ_apply, ih (Polynomial.derivative P), Nat.factorial_succ,
      poly_deriv_coeff]
    push_cast
    ring

private lemma eval_zero_even_T (k r : ℕ) :
    (Polynomial.derivative^[2 * r]
      (Polynomial.Chebyshev.T ℚ (2 * (k : ℤ) + 1))).eval 0 = 0 := by
  induction r with
  | zero =>
    simp only [mul_zero, Function.iterate_zero, id_eq]
    have hodd : Odd (2 * (k : ℤ) + 1) := ⟨(k : ℤ), by ring⟩
    exact Polynomial.Chebyshev.T_eval_zero_of_odd ℚ hodd
  | succ r ih =>
    rw [show 2 * (r + 1) = 2 * r + 2 by omega,
      Polynomial.Chebyshev.iterate_derivative_T_eval_zero_recurrence, ih, mul_zero]

private lemma eval_zero_odd_T (k r : ℕ) :
    (Polynomial.derivative^[2 * r + 1]
      (Polynomial.Chebyshev.T ℚ (2 * (k : ℤ) + 1))).eval 0 =
      (-1 : ℚ) ^ k * ((2 * r + 1).factorial : ℚ) *
        (A_coeff r).eval (2 * (k : ℚ) + 1) := by
  induction r with
  | zero =>
    simp only [mul_zero, zero_add, Function.iterate_one,
      Polynomial.Chebyshev.T_derivative_eq_U,
      show 2 * (k : ℤ) + 1 - 1 = 2 * (k : ℤ) by ring,
      Polynomial.eval_mul, Polynomial.eval_intCast, Polynomial.Chebyshev.U_eval_two_mul_zero,
      negOnePow_cast]
    unfold A_coeff
    simp only [pow_zero, mul_zero, zero_add, Nat.factorial_one,
      Nat.cast_one, div_one, Polynomial.C_1, one_mul, Finset.range_zero,
      Finset.prod_empty, mul_one, Polynomial.eval_X]
    push_cast
    ring
  | succ r ih =>
    rw [show 2 * (r + 1) + 1 = (2 * r + 1) + 2 by omega,
      Polynomial.Chebyshev.iterate_derivative_T_eval_zero_recurrence, ih]
    have hA : (A_coeff (r + 1)).eval (2 * (k : ℚ) + 1) =
        (-1 : ℚ) / (((2 * r + 3 : ℕ) : ℚ) * ((2 * r + 2 : ℕ) : ℚ)) *
          ((2 * (k : ℚ) + 1) ^ 2 - (2 * (r : ℚ) + 1) ^ 2) *
          (A_coeff r).eval (2 * (k : ℚ) + 1) := by
      unfold A_coeff
      rw [Finset.prod_range_succ]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        Polynomial.eval_sub, Polynomial.eval_pow]
      have hfac : ((2 * (r + 1) + 1).factorial : ℚ) =
          ((2 * r + 3 : ℕ) : ℚ) * ((2 * r + 2 : ℕ) : ℚ) * ((2 * r + 1).factorial : ℚ) := by
        rw [show 2 * (r + 1) + 1 = (2 * r + 2) + 1 by omega, Nat.factorial_succ,
          Nat.factorial_succ]
        push_cast
        ring
      have hf0 : ((2 * r + 1).factorial : ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have h23 : ((2 * r + 3 : ℕ) : ℚ) ≠ 0 := by positivity
      have h22 : ((2 * r + 2 : ℕ) : ℚ) ≠ 0 := by positivity
      rw [hfac, pow_succ]
      push_cast
      field_simp
    have hfac2 : ((2 * r + 1 + 2).factorial : ℚ) =
        ((2 * r + 3 : ℕ) : ℚ) * ((2 * r + 2 : ℕ) : ℚ) * ((2 * r + 1).factorial : ℚ) := by
      rw [show 2 * r + 1 + 2 = (2 * r + 2) + 1 by omega, Nat.factorial_succ,
        Nat.factorial_succ]
      push_cast
      ring
    rw [hA, hfac2]
    have h23 : ((2 * r + 3 : ℕ) : ℚ) ≠ 0 := by positivity
    have h22 : ((2 * r + 2 : ℕ) : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp

private lemma chebyshev_T_coeff (k d : ℕ) :
    (Polynomial.C ((-1 : ℚ) ^ k) *
      Polynomial.Chebyshev.T ℚ (2 * (k : ℤ) + 1)).coeff d =
      if d % 2 = 1 then (A_coeff (d / 2)).eval (2 * (k : ℚ) + 1) else 0 := by
  have hfac_ne : (d.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)
  have htay := iterate_derivative_eval_zero d (Polynomial.Chebyshev.T ℚ (2 * (k : ℤ) + 1))
  simp only [Polynomial.coeff_C_mul]
  rcases Nat.even_or_odd' d with ⟨r, rfl | rfl⟩
  · rw [show (if (2 * r) % 2 = 1 then (A_coeff (2 * r / 2)).eval (2 * (k : ℚ) + 1) else 0) = 0 by
      split_ifs
      · omega
      · rfl]
    rw [eval_zero_even_T] at htay
    have h0 : (Polynomial.Chebyshev.T ℚ (2 * (k : ℤ) + 1)).coeff (2 * r) = 0 :=
      (mul_eq_zero.mp htay.symm).resolve_left hfac_ne
    rw [h0, mul_zero]
  · have hodd : (2 * r + 1) % 2 = 1 := by omega
    have hdiv : (2 * r + 1) / 2 = r := by omega
    rw [show (if (2 * r + 1) % 2 = 1 then
        (A_coeff ((2 * r + 1) / 2)).eval (2 * (k : ℚ) + 1) else 0) =
        (A_coeff r).eval (2 * (k : ℚ) + 1) by simp [hodd, hdiv]]
    rw [eval_zero_odd_T] at htay
    have hcoeff : (Polynomial.Chebyshev.T ℚ (2 * (k : ℤ) + 1)).coeff (2 * r + 1) =
        (-1 : ℚ) ^ k * (A_coeff r).eval (2 * (k : ℚ) + 1) := by
      apply mul_left_cancel₀ hfac_ne
      rw [← htay]
      ring
    rw [hcoeff, ← mul_assoc, ← pow_add, show k + k = 2 * k by omega, pow_mul]
    norm_num

private lemma chebyshev_X_U_coeff (k d : ℕ) :
    (Polynomial.C ((-1 : ℚ) ^ k) *
      (Polynomial.X * Polynomial.Chebyshev.U ℚ (2 * (k : ℤ)))).coeff d =
      if d % 2 = 1 then (B_coeff (d / 2)).eval (2 * (k : ℚ) + 1) else 0 := by
  rcases d with _ | d
  · simp
  · have hdu : (Polynomial.derivative
        (Polynomial.Chebyshev.T ℚ (2 * (k : ℤ) + 1))).coeff d =
        (2 * (k : ℚ) + 1) * (Polynomial.Chebyshev.U ℚ (2 * (k : ℤ))).coeff d := by
      rw [Polynomial.Chebyshev.T_derivative_eq_U,
        show 2 * (k : ℤ) + 1 - 1 = 2 * (k : ℤ) by ring,
        show ((2 * (k : ℤ) + 1 : ℤ) : Polynomial ℚ) = Polynomial.C (2 * (k : ℚ) + 1) by
          rw [← Polynomial.C_eq_intCast]
          push_cast
          rfl,
        Polynomial.coeff_C_mul]
    have hdt : (Polynomial.derivative
        (Polynomial.Chebyshev.T ℚ (2 * (k : ℤ) + 1))).coeff d =
        ((d + 1 : ℕ) : ℚ) * (Polynomial.Chebyshev.T ℚ (2 * (k : ℤ) + 1)).coeff (d + 1) :=
      poly_deriv_coeff _ d
    have h2k1 : (2 * (k : ℚ) + 1) ≠ 0 := by positivity
    have hxu : (Polynomial.C ((-1 : ℚ) ^ k) *
        (Polynomial.X * Polynomial.Chebyshev.U ℚ (2 * (k : ℤ)))).coeff (d + 1) =
        (-1 : ℚ) ^ k * (Polynomial.Chebyshev.U ℚ (2 * (k : ℤ))).coeff d := by
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_mul]
    rw [hxu]
    have hT := chebyshev_T_coeff k (d + 1)
    rw [Polynomial.coeff_C_mul] at hT
    rcases Nat.even_or_odd' (d + 1) with ⟨r, hdr | hdr⟩
    · rw [show (if (d + 1) % 2 = 1 then
          (B_coeff ((d + 1) / 2)).eval (2 * (k : ℚ) + 1) else 0) = 0 by
        split_ifs
        · omega
        · rfl]
      rw [show (if (d + 1) % 2 = 1 then
          (A_coeff ((d + 1) / 2)).eval (2 * (k : ℚ) + 1) else 0) = 0 by
        split_ifs
        · omega
        · rfl] at hT
      have ht0 : (Polynomial.Chebyshev.T ℚ (2 * (k : ℤ) + 1)).coeff (d + 1) = 0 := by
        have hsign : (-1 : ℚ) ^ k ≠ 0 := by positivity
        exact (mul_eq_zero.mp hT).resolve_left hsign
      rw [ht0, mul_zero] at hdt
      have hu0 : (Polynomial.Chebyshev.U ℚ (2 * (k : ℤ))).coeff d = 0 := by
        rw [hdt] at hdu
        exact (mul_eq_zero.mp hdu.symm).resolve_left h2k1
      rw [hu0, mul_zero]
    · have hodd : (d + 1) % 2 = 1 := by omega
      have hdiv : (d + 1) / 2 = r := by omega
      rw [show (if (d + 1) % 2 = 1 then
          (B_coeff ((d + 1) / 2)).eval (2 * (k : ℚ) + 1) else 0) =
          (B_coeff r).eval (2 * (k : ℚ) + 1) by simp [hodd, hdiv]]
      rw [show (if (d + 1) % 2 = 1 then
          (A_coeff ((d + 1) / 2)).eval (2 * (k : ℚ) + 1) else 0) =
          (A_coeff r).eval (2 * (k : ℚ) + 1) by simp [hodd, hdiv]] at hT
      have hprod_eq : ((2 * r + 1 : ℕ) : ℚ) * (A_coeff r).eval (2 * (k : ℚ) + 1) =
          (2 * (k : ℚ) + 1) * (B_coeff r).eval (2 * (k : ℚ) + 1) := by
        unfold A_coeff B_coeff
        simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Nat.factorial_succ]
        have hf0 : ((2 * r).factorial : ℚ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
        have h2r1 : ((2 * r + 1 : ℕ) : ℚ) ≠ 0 := by positivity
        field_simp
        push_cast
        ring
      apply mul_left_cancel₀ h2k1
      calc
        (2 * (k : ℚ) + 1) * ((-1 : ℚ) ^ k * (Polynomial.Chebyshev.U ℚ (2 * (k : ℤ))).coeff d)
            = (-1 : ℚ) ^ k *
                ((2 * (k : ℚ) + 1) * (Polynomial.Chebyshev.U ℚ (2 * (k : ℤ))).coeff d) := by
              ring
        _ = (-1 : ℚ) ^ k *
              (((d + 1 : ℕ) : ℚ) * (Polynomial.Chebyshev.T ℚ (2 * (k : ℤ) + 1)).coeff (d + 1)) := by
            rw [← hdu, hdt]
        _ = ((d + 1 : ℕ) : ℚ) *
              ((-1 : ℚ) ^ k * (Polynomial.Chebyshev.T ℚ (2 * (k : ℤ) + 1)).coeff (d + 1)) := by
            ring
        _ = ((2 * r + 1 : ℕ) : ℚ) * (A_coeff r).eval (2 * (k : ℚ) + 1) := by
            rw [hT, hdr]
        _ = (2 * (k : ℚ) + 1) * (B_coeff r).eval (2 * (k : ℚ) + 1) := hprod_eq

private lemma prod_dvd_of_pairwise_coprime {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → Polynomial ℝ) (g : Polynomial ℝ)
    (hcop : (s : Set ι).Pairwise fun i j => IsCoprime (f i) (f j))
    (hdvd : ∀ i ∈ s, f i ∣ g) : ∏ i ∈ s, f i ∣ g := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a t hat ih =>
    rw [Finset.prod_insert hat]
    refine IsCoprime.mul_dvd ?_ (hdvd a (Finset.mem_insert_self a t))
      (ih (fun i hi j hj hij => hcop (Finset.mem_insert_of_mem hi)
        (Finset.mem_insert_of_mem hj) hij)
        (fun i hi => hdvd i (Finset.mem_insert_of_mem hi)))
    exact IsCoprime.prod_right fun i hi =>
      hcop (Finset.mem_insert_self a t) (Finset.mem_insert_of_mem hi)
        fun h => hat (h ▸ hi)

private lemma isCoprime_X_sub_C_of_ne {a b : ℝ} (hab : a ≠ b) :
    IsCoprime (Polynomial.X - Polynomial.C a) (Polynomial.X - Polynomial.C b) := by
  refine ⟨-Polynomial.C ((a - b)⁻¹), Polynomial.C ((a - b)⁻¹), ?_⟩
  have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
  calc
    -Polynomial.C ((a - b)⁻¹) * (Polynomial.X - Polynomial.C a) +
        Polynomial.C ((a - b)⁻¹) * (Polynomial.X - Polynomial.C b)
        = Polynomial.C ((a - b)⁻¹) * (Polynomial.C a - Polynomial.C b) := by ring
    _ = Polynomial.C ((a - b)⁻¹ * (a - b)) := by rw [← Polynomial.C_sub, ← Polynomial.C_mul]
    _ = 1 := by rw [inv_mul_cancel₀ hne, Polynomial.C_1]

private lemma monic_prod_sq_X_sub_C (g : ℕ → ℝ) (m : ℕ) :
    (∏ j ∈ Finset.range m, (Polynomial.X - Polynomial.C (g j)) ^ 2).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun j _ => (Polynomial.monic_X_sub_C (g j)).pow 2

private lemma natDegree_prod_sq_X_sub_C (g : ℕ → ℝ) (m : ℕ) :
    (∏ j ∈ Finset.range m, (Polynomial.X - Polynomial.C (g j)) ^ 2).natDegree = 2 * m := by
  induction m with
  | zero => rw [Finset.range_zero, Finset.prod_empty, Polynomial.natDegree_one, mul_zero]
  | succ m ih =>
    rw [Finset.prod_range_succ,
      (monic_prod_sq_X_sub_C g m).natDegree_mul' ((Polynomial.monic_X_sub_C (g m)).pow 2).ne_zero,
      ih, (Polynomial.monic_X_sub_C (g m)).natDegree_pow, Polynomial.natDegree_X_sub_C]
    omega

private noncomputable def theta (k j : ℕ) : ℝ :=
  (2 * (j : ℝ) + 1) * Real.pi / (2 * (2 * (k : ℝ) + 1))

private noncomputable def sVal (k j : ℕ) : ℝ :=
  (-1 : ℝ) ^ j * Real.sin (theta k j)

private noncomputable def tVal (k j : ℕ) : ℝ :=
  Real.pi / 2 - (-1 : ℝ) ^ j * theta k j

private lemma theta_pos (k j : ℕ) : 0 < theta k j := by
  unfold theta
  positivity

private lemma theta_lt_pi {k j : ℕ} (hj : j < 2 * k + 1) : theta k j < Real.pi := by
  unfold theta
  have hden : (0 : ℝ) < 2 * (2 * (k : ℝ) + 1) := by positivity
  rw [div_lt_iff₀ hden]
  have hjr : (2 * (j : ℝ) + 1) < 2 * (2 * (k : ℝ) + 1) := by
    have : 2 * j + 1 < 2 * (2 * k + 1) := by omega
    exact_mod_cast this
  nlinarith [Real.pi_pos]

private lemma sin_theta_ne_zero {k j : ℕ} (hj : j < 2 * k + 1) :
    Real.sin (theta k j) ≠ 0 :=
  ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (theta_pos k j) (theta_lt_pi hj))

private lemma sVal_ne_zero {k j : ℕ} (hj : j < 2 * k + 1) : sVal k j ≠ 0 := by
  unfold sVal
  exact mul_ne_zero (pow_ne_zero j (by norm_num)) (sin_theta_ne_zero hj)

private lemma sVal_symm {k j : ℕ} (hj : j ≤ 2 * k) :
    sVal k (2 * k - j) = sVal k j := by
  unfold sVal theta
  have hth : (2 * ((2 * k - j : ℕ) : ℝ) + 1) * Real.pi / (2 * (2 * (k : ℝ) + 1)) =
      Real.pi - (2 * (j : ℝ) + 1) * Real.pi / (2 * (2 * (k : ℝ) + 1)) := by
    have hden : 2 * (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    rw [Nat.cast_sub (by omega)]
    push_cast
    field_simp
    ring
  rw [hth, Real.sin_pi_sub]
  have hpow : (-1 : ℝ) ^ (2 * k - j) = (-1 : ℝ) ^ j := by
    have h2 : 2 * k - j + j = 2 * k := by omega
    have hm : (-1 : ℝ) ^ (2 * k - j) * (-1 : ℝ) ^ j = 1 := by
      rw [← pow_add, h2, pow_mul]
      norm_num
    have hinv : (-1 : ℝ) ^ j * (-1 : ℝ) ^ j = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    calc
      (-1 : ℝ) ^ (2 * k - j) = (-1 : ℝ) ^ (2 * k - j) * ((-1 : ℝ) ^ j * (-1 : ℝ) ^ j) := by
        rw [hinv, mul_one]
      _ = ((-1 : ℝ) ^ (2 * k - j) * (-1 : ℝ) ^ j) * (-1 : ℝ) ^ j := by ring
      _ = (-1 : ℝ) ^ j := by rw [hm, one_mul]
  rw [hpow]

private lemma cos_tVal (k j : ℕ) : Real.cos (tVal k j) = sVal k j := by
  unfold tVal sVal
  rw [Real.cos_pi_div_two_sub]
  rcases Nat.even_or_odd j with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have h1 : (-1 : ℝ) ^ (m + m) = 1 := by
      rw [← two_mul, pow_mul]
      norm_num
    rw [h1, one_mul, one_mul]
  · have h1 : (-1 : ℝ) ^ (2 * m + 1) = -1 := by
      rw [pow_add, pow_mul]
      norm_num
    rw [h1, neg_one_mul, neg_one_mul, Real.sin_neg]

private lemma mul_tVal_eq (k j : ℕ) :
    ∃ z : ℤ, ((2 * k + 1 : ℕ) : ℝ) * tVal k j = ((k : ℤ) + 2 * z) * Real.pi := by
  unfold tVal theta
  have hden : 2 * (2 * (k : ℝ) + 1) ≠ 0 := by positivity
  rcases Nat.even_or_odd j with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · refine ⟨-(m : ℤ), ?_⟩
    have h1 : (-1 : ℝ) ^ (m + m) = 1 := by
      rw [← two_mul, pow_mul]
      norm_num
    rw [h1, one_mul]
    push_cast
    field_simp
    ring
  · refine ⟨(m : ℤ) + 1, ?_⟩
    have h1 : (-1 : ℝ) ^ (2 * m + 1) = -1 := by
      rw [pow_add, pow_mul]
      norm_num
    rw [h1, neg_one_mul]
    push_cast
    field_simp
    ring

private lemma eval_T_sVal (k j : ℕ) :
    (Polynomial.Chebyshev.T ℝ (2 * (k : ℤ) + 1)).eval (sVal k j) = (-1 : ℝ) ^ k := by
  rw [← cos_tVal,
    show 2 * (k : ℤ) + 1 = ((2 * k + 1 : ℕ) : ℤ) by push_cast; ring,
    Polynomial.Chebyshev.T_real_cos]
  obtain ⟨z, hz⟩ := mul_tVal_eq k j
  push_cast at hz ⊢
  rw [hz, show ((k : ℝ) + 2 * (z : ℝ)) * Real.pi = (((k : ℤ) + 2 * z : ℤ) : ℝ) * Real.pi by
      push_cast; ring,
    Real.cos_int_mul_pi, zpow_add₀ (by norm_num), zpow_natCast, zpow_mul]
  norm_num

private lemma eval_U_sVal {k j : ℕ} (hj : j < k) :
    (Polynomial.Chebyshev.U ℝ (2 * (k : ℤ))).eval (sVal k j) = 0 := by
  have hth_lt : theta k j < Real.pi / 2 := by
    unfold theta
    have hden : (0 : ℝ) < 2 * (2 * (k : ℝ) + 1) := by positivity
    rw [div_lt_div_iff₀ hden (by norm_num)]
    have : 2 * j + 1 < 2 * k + 1 := by omega
    have hkr : (2 * (j : ℝ) + 1) < 2 * (k : ℝ) + 1 := by exact_mod_cast this
    nlinarith [Real.pi_pos]
  have ht_pos : 0 < tVal k j := by
    unfold tVal
    rcases neg_one_pow_eq_or ℝ j with h1 | h1 <;> rw [h1] <;> linarith [theta_pos k j]
  have ht_lt : tVal k j < Real.pi := by
    unfold tVal
    rcases neg_one_pow_eq_or ℝ j with h1 | h1 <;> rw [h1] <;> linarith [theta_pos k j]
  have hsin_ne : Real.sin (tVal k j) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ht_pos ht_lt)
  have hu := Polynomial.Chebyshev.U_real_cos (tVal k j) (2 * (k : ℤ))
  rw [cos_tVal] at hu
  obtain ⟨z, hz⟩ := mul_tVal_eq k j
  rw [show (((2 * (k : ℤ) : ℤ) : ℝ) + 1) * tVal k j = (((k : ℤ) + 2 * z : ℤ) : ℝ) * Real.pi by
      push_cast at hz ⊢
      linarith,
    Real.sin_int_mul_pi] at hu
  exact (mul_eq_zero.mp hu).resolve_right hsin_ne

private lemma sVal_injOn (k : ℕ) : Set.InjOn (sVal k) (Finset.range (k + 1)) := by
  intro a ha b hb hab
  have ha' : a ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  have hb' : b ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
  have hmem : ∀ x, x ≤ k → theta k x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    intro x hx
    unfold theta
    constructor
    · have hnonneg : 0 ≤ (2 * (x : ℝ) + 1) * Real.pi / (2 * (2 * (k : ℝ) + 1)) := by positivity
      linarith [Real.pi_pos]
    · have hden : (0 : ℝ) < 2 * (2 * (k : ℝ) + 1) := by positivity
      rw [div_le_div_iff₀ hden (by norm_num)]
      have hxr : (2 * (x : ℝ) + 1) ≤ 2 * (k : ℝ) + 1 := by
        exact_mod_cast (by omega : 2 * x + 1 ≤ 2 * k + 1)
      nlinarith [Real.pi_pos]
  have hpos_sin : ∀ x, x ≤ k → 0 < Real.sin (theta k x) := fun x hx =>
    Real.sin_pos_of_pos_of_lt_pi (theta_pos k x) (theta_lt_pi (by omega))
  have hab_abs : |sVal k a| = |sVal k b| := congrArg abs hab
  have hsin_eq : Real.sin (theta k a) = Real.sin (theta k b) := by
    unfold sVal at hab_abs
    simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos (hpos_sin a ha'), abs_of_pos (hpos_sin b hb')] at hab_abs
    exact hab_abs
  have hth_eq : theta k a = theta k b :=
    Real.strictMonoOn_sin.injOn (hmem a ha') (hmem b hb') hsin_eq
  unfold theta at hth_eq
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hden : 2 * (2 * (k : ℝ) + 1) ≠ 0 := by positivity
  have heq_r : (a : ℝ) = (b : ℝ) := by
    have hmul := congrArg (· * (2 * (2 * (k : ℝ) + 1))) hth_eq
    rw [div_mul_cancel₀ _ hden, div_mul_cancel₀ _ hden] at hmul
    have hmul2 := mul_right_cancel₀ hpi hmul
    linarith
  exact_mod_cast heq_r

private lemma geo_mul_spec (a : ℝ) :
    (1 - PowerSeries.C a * PowerSeries.X) *
      PowerSeries.mk (fun m => if m = 0 then 0 else a ^ m) =
      PowerSeries.C a * PowerSeries.X := by
  ext m
  rcases m with _ | _ | m
  · rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_mk, mul_assoc,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_X]
    simp
  · rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_mk, mul_assoc,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_X]
    simp
  · rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_mk, mul_assoc,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_X]
    simp [pow_succ']

private lemma rowValue_eq_sum_inv (n k : ℕ) :
    OMA.S_oeis_a398690.rowValue n k =
      (∑ j ∈ Finset.range (2 * k + 1), (sVal k j)⁻¹ ^ (n + 1)) / (2 * (k : ℝ) + 1) := by
  unfold OMA.S_oeis_a398690.rowValue sVal theta
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have harg : (2 * (j : ℝ) + 1) * (2 * Real.pi) / (8 * (k : ℝ) + 4) =
      (2 * (j : ℝ) + 1) * Real.pi / (2 * (2 * (k : ℝ) + 1)) := by
    field_simp
    ring
  have hsign : (-1 : ℝ) ^ ((n + 3) * j) = ((-1 : ℝ) ^ j) ^ (n + 1) := by
    rw [show (n + 3) * j = j * (n + 1) + 2 * j by ring, pow_add, pow_mul, pow_mul]
    norm_num
  have hinv : (-1 : ℝ) ^ j = ((-1 : ℝ) ^ j)⁻¹ := by
    rcases neg_one_pow_eq_or ℝ j with h | h <;> rw [h] <;> norm_num
  rw [harg, hsign, mul_inv, ← hinv, div_eq_mul_inv, ← inv_pow, ← mul_pow]

private lemma chebyshev_series_identity (k : ℕ) :
    ((1 - Polynomial.C ((-1 : ℝ) ^ k) * Polynomial.Chebyshev.T ℝ (2 * (k : ℤ) + 1) :
        Polynomial ℝ) : PowerSeries ℝ) *
      PowerSeries.mk (fun m => if m = 0 then 0 else OMA.S_oeis_a398690.rowValue (m - 1) k) =
      PowerSeries.C ((-1 : ℝ) ^ k) *
        ((Polynomial.X * Polynomial.Chebyshev.U ℝ (2 * (k : ℤ)) : Polynomial ℝ) :
          PowerSeries ℝ) := by
  let M : ℕ := 2 * k + 1
  let P_rev : Polynomial ℝ :=
    ∏ j ∈ Finset.range M, (1 - Polynomial.C (sVal k j)⁻¹ * Polynomial.X)
  let D_poly : Polynomial ℝ :=
    (Polynomial.X - Polynomial.C (sVal k k)) *
      ∏ j ∈ Finset.range k, (Polynomial.X - Polynomial.C (sVal k j)) ^ 2
  let Q_poly : Polynomial ℝ :=
    1 - Polynomial.C ((-1 : ℝ) ^ k) * Polynomial.Chebyshev.T ℝ (2 * (k : ℤ) + 1)
  have hP_split : P_rev =
      (1 - Polynomial.C (sVal k k)⁻¹ * Polynomial.X) *
        ∏ j ∈ Finset.range k, (1 - Polynomial.C (sVal k j)⁻¹ * Polynomial.X) ^ 2 := by
    dsimp [P_rev, M]
    rw [show 2 * k + 1 = k + 1 + k by omega, Finset.prod_range_add, Finset.prod_range_succ]
    have htail :
        (∏ i ∈ Finset.range k, (1 - Polynomial.C (sVal k (k + 1 + i))⁻¹ * Polynomial.X)) =
          ∏ j ∈ Finset.range k, (1 - Polynomial.C (sVal k j)⁻¹ * Polynomial.X) := by
      refine Finset.prod_bij (fun i _ => k - 1 - i) (fun i hi => by
        rw [Finset.mem_range] at hi ⊢; omega)
        (fun i₁ hi₁ i₂ hi₂ h => by rw [Finset.mem_range] at hi₁ hi₂; omega)
        (fun j hj => ⟨k - 1 - j, by rw [Finset.mem_range] at hj ⊢; omega, by
          rw [Finset.mem_range] at hj; omega⟩)
        fun i hi => by
          rw [Finset.mem_range] at hi
          rw [show k + 1 + i = 2 * k - (k - 1 - i) by omega, sVal_symm (by omega)]
    rw [htail]
    simp only [pow_two]
    rw [Finset.prod_mul_distrib]
    ring
  have hfac : ∀ j, j ≤ k → 1 - Polynomial.C (sVal k j)⁻¹ * Polynomial.X =
      Polynomial.C (-(sVal k j)⁻¹) * (Polynomial.X - Polynomial.C (sVal k j)) := by
    intro j hj
    have hs := sVal_ne_zero (by omega : j < 2 * k + 1)
    calc
      1 - Polynomial.C (sVal k j)⁻¹ * Polynomial.X
          = -Polynomial.C (sVal k j)⁻¹ * Polynomial.X + Polynomial.C ((sVal k j)⁻¹ * sVal k j) := by
            rw [inv_mul_cancel₀ hs, Polynomial.C_1]
            ring
      _ = Polynomial.C (-(sVal k j)⁻¹) * (Polynomial.X - Polynomial.C (sVal k j)) := by
          rw [Polynomial.C_neg, Polynomial.C_mul]
          ring
  have hP_D : P_rev = Polynomial.C (-(sVal k k)⁻¹ *
      ∏ j ∈ Finset.range k, (-(sVal k j)⁻¹) ^ 2) * D_poly := by
    rw [hP_split, hfac k le_rfl]
    have hprod_eq :
        ∏ j ∈ Finset.range k, (1 - Polynomial.C (sVal k j)⁻¹ * Polynomial.X) ^ 2 =
          Polynomial.C (∏ j ∈ Finset.range k, (-(sVal k j)⁻¹) ^ 2) *
            ∏ j ∈ Finset.range k, (Polynomial.X - Polynomial.C (sVal k j)) ^ 2 := by
      have hcon :
          ∏ j ∈ Finset.range k, (1 - Polynomial.C (sVal k j)⁻¹ * Polynomial.X) ^ 2 =
            ∏ j ∈ Finset.range k,
              (Polynomial.C ((-(sVal k j)⁻¹) ^ 2) *
                (Polynomial.X - Polynomial.C (sVal k j)) ^ 2) := by
        refine Finset.prod_congr rfl fun j hj => ?_
        rw [Finset.mem_range] at hj
        rw [hfac j (by omega), mul_pow, Polynomial.C_pow]
      rw [hcon, Finset.prod_mul_distrib, map_prod]
    rw [hprod_eq]
    dsimp [D_poly]
    have hc : Polynomial.C (-(sVal k k)⁻¹) *
        Polynomial.C (∏ j ∈ Finset.range k, (-(sVal k j)⁻¹) ^ 2) =
        Polynomial.C (-(sVal k k)⁻¹ * ∏ j ∈ Finset.range k, (-(sVal k j)⁻¹) ^ 2) :=
      (Polynomial.C_mul).symm
    rw [← hc]
    ring
  have hD_monic : D_poly.Monic :=
    (Polynomial.monic_X_sub_C _).mul (monic_prod_sq_X_sub_C (sVal k) k)
  have hD_deg : D_poly.natDegree = 2 * k + 1 := by
    dsimp [D_poly]
    rw [(Polynomial.monic_X_sub_C _).natDegree_mul' (monic_prod_sq_X_sub_C _ k).ne_zero,
      Polynomial.natDegree_X_sub_C, natDegree_prod_sq_X_sub_C]
    omega
  have hQ_deg : Q_poly.natDegree = 2 * k + 1 := by
    dsimp [Q_poly]
    have hT_deg : (Polynomial.C ((-1 : ℝ) ^ k) *
        Polynomial.Chebyshev.T ℝ (2 * (k : ℤ) + 1)).natDegree = 2 * k + 1 := by
      rw [Polynomial.natDegree_C_mul (pow_ne_zero k (by norm_num)),
        Polynomial.Chebyshev.natDegree_T]
      omega
    have h1_lt : (1 : Polynomial ℝ).natDegree < (Polynomial.C ((-1 : ℝ) ^ k) *
        Polynomial.Chebyshev.T ℝ (2 * (k : ℤ) + 1)).natDegree := by
      rw [Polynomial.natDegree_one, hT_deg]
      omega
    rw [Polynomial.natDegree_sub_eq_right_of_natDegree_lt h1_lt, hT_deg]
  have hQ_root : ∀ j, Q_poly.eval (sVal k j) = 0 := by
    intro j
    dsimp [Q_poly]
    rw [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
      eval_T_sVal, ← pow_add, show k + k = 2 * k by omega, pow_mul]
    norm_num
  have hdQ_eq : Polynomial.derivative Q_poly =
      -Polynomial.C ((-1 : ℝ) ^ k * (M : ℝ)) * Polynomial.Chebyshev.U ℝ (2 * (k : ℤ)) := by
    dsimp [Q_poly, M]
    have h1 : Polynomial.derivative (1 : Polynomial ℝ) = 0 := by simp
    have hc0 : Polynomial.derivative (Polynomial.C ((-1 : ℝ) ^ k)) = 0 := by simp
    rw [Polynomial.derivative_sub, h1, zero_sub, Polynomial.derivative_mul, hc0, zero_mul,
      zero_add, Polynomial.Chebyshev.T_derivative_eq_U,
      show 2 * (k : ℤ) + 1 - 1 = 2 * (k : ℤ) by ring,
      show ((2 * (k : ℤ) + 1 : ℤ) : Polynomial ℝ) = Polynomial.C (2 * (k : ℝ) + 1) by
        rw [← Polynomial.C_eq_intCast]
        push_cast
        rfl]
    rw [← mul_assoc, ← Polynomial.C_mul, ← neg_mul]
    congr 2
    push_cast
    ring
  have hdvd_k : (Polynomial.X - Polynomial.C (sVal k k)) ∣ Q_poly :=
    Polynomial.dvd_iff_isRoot.mpr (hQ_root k)
  have hdvd_prod : (∏ j ∈ Finset.range k, (Polynomial.X - Polynomial.C (sVal k j)) ^ 2) ∣
      Q_poly := by
    refine prod_dvd_of_pairwise_coprime _ _ _ ?_ ?_
    · intro a ha b hb hab
      have hs_ne : sVal k a ≠ sVal k b := fun heq =>
        hab (sVal_injOn k (Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp ha)))
          (Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hb))) heq)
      exact ((isCoprime_X_sub_C_of_ne hs_ne).pow_left).pow_right
    · intro j hj
      rw [Finset.mem_range] at hj
      obtain ⟨g, hg⟩ := Polynomial.dvd_iff_isRoot.mpr (hQ_root j)
      have hd := congrArg Polynomial.derivative hg
      have hx1 : Polynomial.derivative (Polynomial.X - Polynomial.C (sVal k j)) = 1 := by simp
      rw [Polynomial.derivative_mul, hx1, one_mul] at hd
      have hev := congrArg (Polynomial.eval (sVal k j)) hd
      rw [hdQ_eq] at hev
      simp only [Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_C,
        eval_U_sVal hj, mul_zero, Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_X, sub_self, zero_mul, add_zero] at hev
      obtain ⟨h, hh⟩ := Polynomial.dvd_iff_isRoot.mpr hev.symm
      refine ⟨h, ?_⟩
      rw [hg, hh]
      ring
  have hdvd_D : D_poly ∣ Q_poly := by
    dsimp [D_poly]
    refine IsCoprime.mul_dvd ?_ hdvd_k hdvd_prod
    refine IsCoprime.prod_right fun j hj => ?_
    rw [Finset.mem_range] at hj
    have hs_ne : sVal k k ≠ sVal k j := fun heq =>
      (by omega : k ≠ j) (sVal_injOn k (Finset.mem_range.mpr (Nat.lt_succ_self k))
        (Finset.mem_range.mpr (Nat.lt_succ_of_lt hj)) heq)
    exact (isCoprime_X_sub_C_of_ne hs_ne).pow_right
  have hPQ : P_rev = Q_poly := by
    obtain ⟨q, hq⟩ := hdvd_D
    have hQ_ne : Q_poly ≠ 0 := by
      intro hz
      rw [hz, Polynomial.natDegree_zero] at hQ_deg
      omega
    have hq_ne : q ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hq
      exact hQ_ne hq
    have hq_deg : q.natDegree = 0 := by
      have hmul_deg := hD_monic.natDegree_mul' hq_ne
      rw [← hq, hQ_deg, hD_deg] at hmul_deg
      omega
    have hqc : q = Polynomial.C (q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hq_deg
    have hP0 : P_rev.eval 0 = 1 := by
      dsimp [P_rev]
      rw [Polynomial.eval_prod]
      refine Finset.prod_eq_one fun j _ => ?_
      simp
    have hQ0 : Q_poly.eval 0 = 1 := by
      dsimp [Q_poly]
      have hodd : Odd (2 * (k : ℤ) + 1) := ⟨(k : ℤ), by ring⟩
      rw [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.Chebyshev.T_eval_zero_of_odd ℝ hodd, mul_zero, sub_zero]
    have hD0 : D_poly.eval 0 ≠ 0 := by
      dsimp [D_poly]
      rw [Polynomial.eval_mul, Polynomial.eval_prod]
      refine mul_ne_zero ?_ (Finset.prod_ne_zero_iff.mpr fun j hj => ?_)
      · simp [sVal_ne_zero (by omega : k < 2 * k + 1)]
      · rw [Finset.mem_range] at hj
        simp [sVal_ne_zero (by omega : j < 2 * k + 1)]
    have h1 : (-(sVal k k)⁻¹ * ∏ j ∈ Finset.range k, (-(sVal k j)⁻¹) ^ 2) * D_poly.eval 0 =
        q.coeff 0 * D_poly.eval 0 := by
      have hp := congrArg (Polynomial.eval 0) hP_D
      have hq' := congrArg (Polynomial.eval 0) hq
      rw [hP0, Polynomial.eval_mul, Polynomial.eval_C] at hp
      rw [hQ0, hqc, Polynomial.eval_mul, Polynomial.eval_C, mul_comm (D_poly.eval 0)] at hq'
      linarith
    have hcoeff_eq := mul_right_cancel₀ hD0 h1
    rw [hP_D, hq, hqc, hcoeff_eq, mul_comm]
  have hdP : Polynomial.derivative P_rev =
      ∑ j ∈ Finset.range M, (-Polynomial.C (sVal k j)⁻¹) *
        ∏ i ∈ (Finset.range M).erase j, (1 - Polynomial.C (sVal k i)⁻¹ * Polynomial.X) := by
    dsimp [P_rev]
    rw [Polynomial.derivative_prod_finset]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hd1 : Polynomial.derivative (1 - Polynomial.C (sVal k j)⁻¹ * Polynomial.X) =
        -Polynomial.C (sVal k j)⁻¹ := by
      simp
    rw [hd1]
    ring
  have hpoly_diff :
      ∑ j ∈ Finset.range M, (Polynomial.C (sVal k j)⁻¹ * Polynomial.X) *
          ∏ i ∈ (Finset.range M).erase j, (1 - Polynomial.C (sVal k i)⁻¹ * Polynomial.X) =
        Polynomial.C ((-1 : ℝ) ^ k * (M : ℝ)) *
          (Polynomial.X * Polynomial.Chebyshev.U ℝ (2 * (k : ℤ))) := by
    have hder := congrArg (fun p : Polynomial ℝ => -Polynomial.X * Polynomial.derivative p) hPQ
    rw [hdP, hdQ_eq, Finset.mul_sum] at hder
    calc
      ∑ j ∈ Finset.range M, (Polynomial.C (sVal k j)⁻¹ * Polynomial.X) *
          ∏ i ∈ (Finset.range M).erase j, (1 - Polynomial.C (sVal k i)⁻¹ * Polynomial.X)
          = ∑ j ∈ Finset.range M, -Polynomial.X * ((-Polynomial.C (sVal k j)⁻¹) *
              ∏ i ∈ (Finset.range M).erase j, (1 - Polynomial.C (sVal k i)⁻¹ * Polynomial.X)) := by
            refine Finset.sum_congr rfl fun j _ => by ring
      _ = -Polynomial.X * (-Polynomial.C ((-1 : ℝ) ^ k * (M : ℝ)) *
            Polynomial.Chebyshev.U ℝ (2 * (k : ℤ))) := hder
      _ = Polynomial.C ((-1 : ℝ) ^ k * (M : ℝ)) *
            (Polynomial.X * Polynomial.Chebyshev.U ℝ (2 * (k : ℤ))) := by ring
  have hps_diff := congrArg Polynomial.coeToPowerSeries.ringHom hpoly_diff
  simp only [map_sum, map_mul, map_prod, map_sub, map_one,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, Polynomial.coe_X] at hps_diff
  have hser_row :
      PowerSeries.mk (fun m => if m = 0 then 0 else OMA.S_oeis_a398690.rowValue (m - 1) k) =
        PowerSeries.C ((M : ℝ)⁻¹) *
          ∑ j ∈ Finset.range M, PowerSeries.mk (fun m => if m = 0 then 0 else (sVal k j)⁻¹ ^ m) := by
    ext m
    rcases m with _ | m
    · simp
    · simp only [PowerSeries.coeff_mk, PowerSeries.coeff_C_mul, map_sum, Nat.add_eq_zero_iff,
        one_ne_zero, and_false, ite_false, Nat.add_one_sub_one, rowValue_eq_sum_inv, div_eq_mul_inv]
      dsimp [M]
      push_cast
      ring
  have hQ_ps : ((Q_poly : Polynomial ℝ) : PowerSeries ℝ) =
      ∏ i ∈ Finset.range M, (1 - PowerSeries.C (sVal k i)⁻¹ * PowerSeries.X) := by
    rw [← hPQ]
    dsimp [P_rev]
    rw [← Polynomial.coeToPowerSeries.ringHom_apply]
    simp only [map_prod, map_sub, map_one, map_mul, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coe_C, Polynomial.coe_X]
  change ((Q_poly : Polynomial ℝ) : PowerSeries ℝ) *
      PowerSeries.mk (fun m => if m = 0 then 0 else OMA.S_oeis_a398690.rowValue (m - 1) k) =
    PowerSeries.C ((-1 : ℝ) ^ k) *
      ((Polynomial.X * Polynomial.Chebyshev.U ℝ (2 * (k : ℤ)) : Polynomial ℝ) : PowerSeries ℝ)
  rw [hQ_ps, hser_row]
  have hM_ne : (M : ℝ) ≠ 0 := by positivity
  calc
    (∏ i ∈ Finset.range M, (1 - PowerSeries.C (sVal k i)⁻¹ * PowerSeries.X)) *
        (PowerSeries.C ((M : ℝ)⁻¹) *
          ∑ j ∈ Finset.range M, PowerSeries.mk (fun m => if m = 0 then 0 else (sVal k j)⁻¹ ^ m))
        = PowerSeries.C ((M : ℝ)⁻¹) *
            ((∏ i ∈ Finset.range M, (1 - PowerSeries.C (sVal k i)⁻¹ * PowerSeries.X)) *
              ∑ j ∈ Finset.range M,
                PowerSeries.mk (fun m => if m = 0 then 0 else (sVal k j)⁻¹ ^ m)) := by
          rw [mul_left_comm]
    _ = PowerSeries.C ((M : ℝ)⁻¹) *
          ∑ j ∈ Finset.range M,
            (∏ i ∈ Finset.range M, (1 - PowerSeries.C (sVal k i)⁻¹ * PowerSeries.X)) *
              PowerSeries.mk (fun m => if m = 0 then 0 else (sVal k j)⁻¹ ^ m) := by
          rw [Finset.mul_sum]
    _ = PowerSeries.C ((M : ℝ)⁻¹) *
          ∑ j ∈ Finset.range M,
            (PowerSeries.C (sVal k j)⁻¹ * PowerSeries.X) *
              ∏ i ∈ (Finset.range M).erase j, (1 - PowerSeries.C (sVal k i)⁻¹ * PowerSeries.X) := by
          congr 1
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [← Finset.mul_prod_erase (Finset.range M)
            (fun i => 1 - PowerSeries.C (sVal k i)⁻¹ * PowerSeries.X) hj,
            mul_comm (1 - PowerSeries.C (sVal k j)⁻¹ * PowerSeries.X), mul_assoc, geo_mul_spec,
            mul_comm]
    _ = PowerSeries.C ((M : ℝ)⁻¹) *
          (PowerSeries.C ((-1 : ℝ) ^ k) * PowerSeries.C (M : ℝ) *
            (PowerSeries.X *
              ((Polynomial.Chebyshev.U ℝ (2 * (k : ℤ)) : Polynomial ℝ) : PowerSeries ℝ))) := by
          rw [hps_diff]
    _ = PowerSeries.C ((-1 : ℝ) ^ k) *
          ((Polynomial.X * Polynomial.Chebyshev.U ℝ (2 * (k : ℤ)) : Polynomial ℝ) :
            PowerSeries ℝ) := by
          conv_rhs =>
            rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_mul,
              Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]
          have hMM : PowerSeries.C ((M : ℝ)⁻¹) *
              (PowerSeries.C ((-1 : ℝ) ^ k) * PowerSeries.C (M : ℝ)) =
              PowerSeries.C ((-1 : ℝ) ^ k) := by
            rw [← map_mul, ← map_mul]
            congr 1
            field_simp
          calc
            PowerSeries.C ((M : ℝ)⁻¹) *
                (PowerSeries.C ((-1 : ℝ) ^ k) * PowerSeries.C (M : ℝ) *
                  (PowerSeries.X *
                    ((Polynomial.Chebyshev.U ℝ (2 * (k : ℤ)) : Polynomial ℝ) : PowerSeries ℝ)))
                = (PowerSeries.C ((M : ℝ)⁻¹) *
                    (PowerSeries.C ((-1 : ℝ) ^ k) * PowerSeries.C (M : ℝ))) *
                    (PowerSeries.X *
                      ((Polynomial.Chebyshev.U ℝ (2 * (k : ℤ)) : Polynomial ℝ) :
                        PowerSeries ℝ)) := by ring
            _ = PowerSeries.C ((-1 : ℝ) ^ k) *
                  (PowerSeries.X *
                    ((Polynomial.Chebyshev.U ℝ (2 * (k : ℤ)) : Polynomial ℝ) : PowerSeries ℝ)) := by
                  rw [hMM]

private noncomputable def A_ser : PowerSeries (Polynomial ℚ) :=
  PowerSeries.mk fun d => if d % 2 = 1 then A_coeff (d / 2) else 0

private noncomputable def B_ser : PowerSeries (Polynomial ℚ) :=
  PowerSeries.mk fun d => if d % 2 = 1 then B_coeff (d / 2) else 0

private noncomputable def G_ser : PowerSeries (Polynomial ℚ) :=
  B_ser * PowerSeries.invOfUnit (1 - A_ser) 1

private lemma constantCoeff_one_sub_A_ser : PowerSeries.constantCoeff (1 - A_ser) = 1 := by
  rw [map_sub, map_one]
  have h0 : PowerSeries.constantCoeff A_ser = 0 := by
    rw [A_ser, PowerSeries.constantCoeff_mk]
    simp
  rw [h0, sub_zero]

private lemma one_sub_A_mul_G : (1 - A_ser) * G_ser = B_ser := by
  unfold G_ser
  rw [mul_left_comm, PowerSeries.mul_invOfUnit (1 - A_ser) 1 (by
    rw [constantCoeff_one_sub_A_ser, Units.val_one]), mul_one]

private noncomputable def Q_poly (n : ℕ) : Polynomial ℚ :=
  PowerSeries.coeff (n + 1) G_ser

private lemma rowValue_eq_eval_Q (n k : ℕ) :
    OMA.S_oeis_a398690.rowValue n k =
      Polynomial.eval₂ (algebraMap ℚ ℝ) (2 * (k : ℝ) + 1) (Q_poly n) := by
  let φ : Polynomial ℚ →+* ℝ := Polynomial.eval₂RingHom (algebraMap ℚ ℝ) (2 * (k : ℝ) + 1)
  have hφ_eval : ∀ p : Polynomial ℚ,
      φ p = algebraMap ℚ ℝ (p.eval (2 * (k : ℚ) + 1)) := by
    intro p
    change p.eval₂ (algebraMap ℚ ℝ) (2 * (k : ℝ) + 1) =
      algebraMap ℚ ℝ (p.eval₂ (RingHom.id ℚ) (2 * (k : ℚ) + 1))
    rw [Polynomial.hom_eval₂]
    congr 1
    simp only [map_add, map_mul, map_ofNat, map_natCast, map_one]
  have hmap := congrArg (PowerSeries.map φ) one_sub_A_mul_G
  rw [map_mul, map_sub, map_one] at hmap
  have hA_map : A_ser.map φ =
      ((Polynomial.C ((-1 : ℝ) ^ k) * Polynomial.Chebyshev.T ℝ (2 * (k : ℤ) + 1) :
        Polynomial ℝ) : PowerSeries ℝ) := by
    ext d
    rw [PowerSeries.coeff_map, A_ser, PowerSeries.coeff_mk, Polynomial.coeff_coe]
    have hmapT : (Polynomial.C ((-1 : ℚ) ^ k) *
        Polynomial.Chebyshev.T ℚ (2 * (k : ℤ) + 1)).map (algebraMap ℚ ℝ) =
        Polynomial.C ((-1 : ℝ) ^ k) * Polynomial.Chebyshev.T ℝ (2 * (k : ℤ) + 1) := by
      simp [Polynomial.Chebyshev.map_T]
    rw [← hmapT, Polynomial.coeff_map, chebyshev_T_coeff k d]
    split_ifs with hd
    · exact hφ_eval _
    · simp
  have hB_map : B_ser.map φ =
      PowerSeries.C ((-1 : ℝ) ^ k) *
        ((Polynomial.X * Polynomial.Chebyshev.U ℝ (2 * (k : ℤ)) : Polynomial ℝ) :
          PowerSeries ℝ) := by
    ext d
    rw [PowerSeries.coeff_map, B_ser, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul,
      Polynomial.coeff_coe]
    have hmapU : (Polynomial.C ((-1 : ℚ) ^ k) *
        (Polynomial.X * Polynomial.Chebyshev.U ℚ (2 * (k : ℤ)))).map (algebraMap ℚ ℝ) =
        Polynomial.C ((-1 : ℝ) ^ k) *
          (Polynomial.X * Polynomial.Chebyshev.U ℝ (2 * (k : ℤ))) := by
      simp [Polynomial.Chebyshev.map_U]
    have hcoef_mul : ((-1 : ℝ) ^ k) *
        (Polynomial.X * Polynomial.Chebyshev.U ℝ (2 * (k : ℤ))).coeff d =
        (Polynomial.C ((-1 : ℝ) ^ k) *
          (Polynomial.X * Polynomial.Chebyshev.U ℝ (2 * (k : ℤ)))).coeff d := by
      rw [Polynomial.coeff_C_mul]
    rw [hcoef_mul, ← hmapU, Polynomial.coeff_map, chebyshev_X_U_coeff k d]
    split_ifs with hd
    · exact hφ_eval _
    · simp
  let D_ps : PowerSeries ℝ :=
    ((1 - Polynomial.C ((-1 : ℝ) ^ k) * Polynomial.Chebyshev.T ℝ (2 * (k : ℤ) + 1) :
      Polynomial ℝ) : PowerSeries ℝ)
  have hD_sub : (1 : PowerSeries ℝ) - A_ser.map φ = D_ps := by
    dsimp [D_ps]
    rw [hA_map, ← Polynomial.coeToPowerSeries.ringHom_apply,
      ← Polynomial.coeToPowerSeries.ringHom_apply, map_sub, map_one]
  have hD_const : PowerSeries.constantCoeff D_ps = 1 := by
    rw [← hD_sub, map_sub, map_one, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map]
    have hA0 : PowerSeries.coeff 0 A_ser = 0 := by
      rw [A_ser, PowerSeries.coeff_mk]
      simp
    rw [hA0, map_zero, sub_zero]
  have hG_eq : G_ser.map φ =
      PowerSeries.mk (fun m => if m = 0 then 0 else OMA.S_oeis_a398690.rowValue (m - 1) k) := by
    rw [hD_sub, hB_map] at hmap
    have h1 := congrArg (PowerSeries.invOfUnit D_ps 1 * ·) hmap
    have h2 := congrArg (PowerSeries.invOfUnit D_ps 1 * ·) (chebyshev_series_identity k)
    rw [← mul_assoc, PowerSeries.invOfUnit_mul D_ps 1 (by
      rw [hD_const, Units.val_one]), one_mul] at h1 h2
    exact h1.trans h2.symm
  have hcoeff := congrArg (PowerSeries.coeff (n + 1)) hG_eq
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk] at hcoeff
  rw [show (if n + 1 = 0 then 0 else OMA.S_oeis_a398690.rowValue (n + 1 - 1) k) =
      OMA.S_oeis_a398690.rowValue n k by simp] at hcoeff
  simpa [Q_poly, φ] using hcoeff.symm

private lemma Q_poly_rec (n : ℕ) :
    Q_poly n = PowerSeries.coeff (n + 1) B_ser +
      ∑ j ∈ Finset.range n, PowerSeries.coeff (n - j) A_ser * Q_poly j := by
  have h0_B : PowerSeries.constantCoeff B_ser = 0 := by
    rw [B_ser, PowerSeries.constantCoeff_mk]
    simp
  have h0_G : PowerSeries.coeff 0 G_ser = 0 := by
    have h0 := congrArg PowerSeries.constantCoeff one_sub_A_mul_G
    rw [map_mul, constantCoeff_one_sub_A_ser, one_mul, h0_B] at h0
    rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have h0_A : PowerSeries.coeff 0 A_ser = 0 := by
    rw [A_ser, PowerSeries.coeff_mk]
    simp
  have hc := congrArg (PowerSeries.coeff (n + 1)) one_sub_A_mul_G
  rw [sub_mul, one_mul, map_sub] at hc
  have hprod : PowerSeries.coeff (n + 1) (A_ser * G_ser) =
      ∑ j ∈ Finset.range n, PowerSeries.coeff (n - j) A_ser * Q_poly j := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i A_ser * PowerSeries.coeff j G_ser) (n + 1),
      Finset.sum_range_succ', h0_A, zero_mul, add_zero, Finset.sum_range_succ]
    simp only [Nat.sub_self, h0_G, mul_zero, add_zero]
    refine Finset.sum_bij (fun i _ => n - 1 - i)
      (fun i hi => by rw [Finset.mem_range] at hi ⊢; omega)
      (fun i₁ hi₁ i₂ hi₂ h => by rw [Finset.mem_range] at hi₁ hi₂; omega)
      (fun j hj => ⟨n - 1 - j, by rw [Finset.mem_range] at hj ⊢; omega, by
        rw [Finset.mem_range] at hj; omega⟩)
      fun i hi => by
        rw [Finset.mem_range] at hi
        dsimp [Q_poly]
        rw [show n + 1 - (i + 1) = (n - 1 - i) + 1 by omega,
          show i + 1 = n - (n - 1 - i) by omega]
  rw [hprod] at hc
  exact eq_add_of_sub_eq hc

private lemma Q_poly_natDegree_and_comp : ∀ n : ℕ,
    (Q_poly n).natDegree ≤ n ∧
      (Q_poly n).comp (-Polynomial.X) = Polynomial.C ((-1 : ℚ) ^ n) * Q_poly n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [Q_poly_rec n]
    have hB_deg : (PowerSeries.coeff (n + 1) B_ser).natDegree ≤ n := by
      rw [B_ser, PowerSeries.coeff_mk]
      split_ifs with hn
      · have heven : 2 * ((n + 1) / 2) = n := by omega
        exact le_trans (B_coeff_natDegree _) (by omega)
      · simp
    have hB_comp : (PowerSeries.coeff (n + 1) B_ser).comp (-Polynomial.X) =
        Polynomial.C ((-1 : ℚ) ^ n) * PowerSeries.coeff (n + 1) B_ser := by
      rw [B_ser, PowerSeries.coeff_mk]
      split_ifs with hn
      · have hev : (-1 : ℚ) ^ n = 1 := by
          have : ∃ r, n = 2 * r := ⟨n / 2, by omega⟩
          obtain ⟨r, rfl⟩ := this
          rw [pow_mul]
          norm_num
        rw [B_coeff_comp_neg, hev, Polynomial.C_1, one_mul]
      · simp
    have hterm_deg : ∀ j ∈ Finset.range n,
        (PowerSeries.coeff (n - j) A_ser * Q_poly j).natDegree ≤ n := by
      intro j hj
      rw [Finset.mem_range] at hj
      refine le_trans Polynomial.natDegree_mul_le ?_
      have hA_deg : (PowerSeries.coeff (n - j) A_ser).natDegree ≤ n - j := by
        rw [A_ser, PowerSeries.coeff_mk]
        split_ifs with hnj
        · refine le_trans (A_coeff_natDegree _) (by omega)
        · simp
      have hQ_deg := (ih j hj).1
      omega
    have hterm_comp : ∀ j ∈ Finset.range n,
        (PowerSeries.coeff (n - j) A_ser * Q_poly j).comp (-Polynomial.X) =
          Polynomial.C ((-1 : ℚ) ^ n) * (PowerSeries.coeff (n - j) A_ser * Q_poly j) := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [Polynomial.mul_comp, (ih j hj).2]
      rw [A_ser, PowerSeries.coeff_mk]
      split_ifs with hnj
      · have hodd : (-1 : ℚ) ^ (n - j) = -1 := by
          have : ∃ r, n - j = 2 * r + 1 := ⟨(n - j) / 2, by omega⟩
          obtain ⟨r, hr⟩ := this
          rw [hr, pow_add, pow_mul]
          norm_num
        rw [A_coeff_comp_neg]
        have hpow : (-1 : ℚ) ^ n = -((-1 : ℚ) ^ j) := by
          rw [← Nat.sub_add_cancel (le_of_lt hj), pow_add, hodd]
          ring
        rw [hpow, Polynomial.C_neg]
        ring
      · simp
    constructor
    · refine le_trans (Polynomial.natDegree_add_le _ _) (max_le hB_deg ?_)
      exact le_trans (Polynomial.natDegree_sum_le _ _)
        (Finset.sup_le fun j hj => hterm_deg j hj)
    · rw [Polynomial.add_comp, hB_comp, Polynomial.sum_comp, mul_add, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun j hj => hterm_comp j hj

private noncomputable def R_poly (n : ℕ) : Polynomial ℚ :=
  (Q_poly n).comp (2 * Polynomial.X + 1)

private lemma R_poly_natDegree (n : ℕ) : (R_poly n).natDegree ≤ n := by
  unfold R_poly
  refine le_trans Polynomial.natDegree_comp_le ?_
  have h1 : (2 * Polynomial.X + 1 : Polynomial ℚ).natDegree ≤ 1 := by
    refine le_trans (Polynomial.natDegree_add_le _ _) ?_
    simp
  have hQ := (Q_poly_natDegree_and_comp n).1
  nlinarith

private lemma R_poly_eval_neg (n : ℕ) (x : ℚ) :
    (R_poly n).eval (-x - 1) = (-1 : ℚ) ^ n * (R_poly n).eval x := by
  unfold R_poly
  rw [Polynomial.eval_comp, Polynomial.eval_comp]
  have hlin : (2 * Polynomial.X + 1 : Polynomial ℚ).eval (-x - 1) =
      (-Polynomial.X).eval ((2 * Polynomial.X + 1 : Polynomial ℚ).eval x) := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_neg]
    ring
  rw [hlin, ← Polynomial.eval_comp, (Q_poly_natDegree_and_comp n).2,
    Polynomial.eval_mul, Polynomial.eval_C]

private noncomputable def delta (f : Polynomial ℚ) : Polynomial ℚ :=
  f.comp (Polynomial.X + 1) - f

private lemma delta_natDegree_le {f : Polynomial ℚ} {d : ℕ} (hf : f.natDegree ≤ d + 1) :
    (delta f).natDegree ≤ d := by
  unfold delta
  by_cases h0 : (f.comp (Polynomial.X + 1) - f).natDegree ≤ d
  · exact h0
  · exfalso
    have hcomp_deg : (f.comp (Polynomial.X + 1)).natDegree ≤ d + 1 := by
      refine le_trans Polynomial.natDegree_comp_le ?_
      have hx1 : (Polynomial.X + 1 : Polynomial ℚ).natDegree = 1 := by
        rw [← Polynomial.C_1, Polynomial.natDegree_X_add_C]
      rw [hx1, mul_one]
      exact hf
    have hsub_deg : (f.comp (Polynomial.X + 1) - f).natDegree ≤ d + 1 :=
      le_trans (Polynomial.natDegree_sub_le _ _) (max_le hcomp_deg hf)
    have heq : (f.comp (Polynomial.X + 1) - f).natDegree = d + 1 := by omega
    have hcoeff0 : (f.comp (Polynomial.X + 1) - f).coeff (d + 1) = 0 := by
      rw [Polynomial.coeff_sub]
      have hf_sum := Polynomial.as_sum_range_C_mul_X_pow' f (Nat.lt_succ_of_le hf)
      have hc1 : (f.comp (Polynomial.X + 1)).coeff (d + 1) = f.coeff (d + 1) := by
        nth_rw 1 [hf_sum]
        simp only [Polynomial.sum_comp, Polynomial.mul_comp, Polynomial.C_comp,
          Polynomial.pow_comp, Polynomial.X_comp, Polynomial.finsetSum_coeff]
        rw [Finset.sum_range_succ]
        have hlt : ∑ i ∈ Finset.range (d + 1),
            (Polynomial.C (f.coeff i) * (Polynomial.X + 1) ^ i).coeff (d + 1) = 0 := by
          refine Finset.sum_eq_zero fun i hi => ?_
          rw [Finset.mem_range] at hi
          refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
          refine lt_of_le_of_lt Polynomial.natDegree_mul_le ?_
          have hpow : ((Polynomial.X + 1 : Polynomial ℚ) ^ i).natDegree ≤ i := by
            refine le_trans Polynomial.natDegree_pow_le ?_
            rw [← Polynomial.C_1, Polynomial.natDegree_X_add_C, mul_one]
          have hc : (Polynomial.C (f.coeff i)).natDegree = 0 := Polynomial.natDegree_C _
          omega
        rw [hlt, zero_add, Polynomial.coeff_C_mul]
        have hmon1 : (Polynomial.X + 1 : Polynomial ℚ).Monic := by
          rw [← Polynomial.C_1]
          exact Polynomial.monic_X_add_C 1
        have hmon : ((Polynomial.X + 1 : Polynomial ℚ) ^ (d + 1)).Monic := hmon1.pow (d + 1)
        have hdeg : ((Polynomial.X + 1 : Polynomial ℚ) ^ (d + 1)).natDegree = d + 1 := by
          rw [hmon1.natDegree_pow, ← Polynomial.C_1, Polynomial.natDegree_X_add_C, mul_one]
        have hlc : ((Polynomial.X + 1 : Polynomial ℚ) ^ (d + 1)).coeff (d + 1) = 1 := by
          have := hmon.leadingCoeff
          rwa [Polynomial.leadingCoeff, hdeg] at this
        rw [hlc, mul_one]
      rw [hc1, sub_self]
    have hne0 : (f.comp (Polynomial.X + 1) - f) ≠ 0 := by
      intro hz
      rw [hz, Polynomial.natDegree_zero] at heq
      omega
    exact (Polynomial.leadingCoeff_ne_zero.mpr hne0)
      (by rw [Polynomial.leadingCoeff, heq]; exact hcoeff0)

private lemma iterate_delta_zero : ∀ d : ℕ, ∀ f : Polynomial ℚ,
    f.natDegree ≤ d → delta^[d + 1] f = 0
  | 0, f, hf => by
    have hfc := Polynomial.eq_C_of_natDegree_eq_zero (Nat.le_zero.mp hf)
    rw [Function.iterate_one, delta, hfc]
    simp
  | d + 1, f, hf => by
    rw [Function.iterate_succ_apply]
    exact iterate_delta_zero d (delta f) (delta_natDegree_le hf)

private lemma iterate_delta_eval (m : ℕ) : ∀ (f : Polynomial ℚ) (x : ℚ),
    (delta^[m] f).eval x =
      ∑ i ∈ Finset.range (m + 1),
        (-1 : ℚ) ^ (m - i) * (m.choose i : ℚ) * f.eval (x + (i : ℚ)) := by
  induction m with
  | zero =>
    intro f x
    simp
  | succ m ih =>
    intro f x
    rw [Function.iterate_succ_apply', delta, Polynomial.eval_sub, Polynomial.eval_comp,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one, ih f (x + 1), ih f x]
    rw [Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, one_mul,
      Nat.sub_zero, Nat.choose_zero_right, Nat.cast_zero, add_zero]
    have heq_arg : ∀ k : ℕ, x + 1 + (k : ℚ) = x + ((k + 1 : ℕ) : ℚ) := fun k => by
      push_cast; ring
    simp only [heq_arg]
    have hrhs :
        ∑ i ∈ Finset.range (m + 2),
            (-1 : ℚ) ^ (m + 1 - i) * ((m + 1).choose i : ℚ) * f.eval (x + (i : ℚ)) =
          f.eval (x + ((m + 1 : ℕ) : ℚ)) +
            (∑ k ∈ Finset.range m,
              (-1 : ℚ) ^ (m + 1 - (k + 1)) * ((m + 1).choose (k + 1) : ℚ) *
                f.eval (x + ((k + 1 : ℕ) : ℚ))) +
            (-1 : ℚ) ^ (m + 1) * f.eval x := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ']
      simp only [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, one_mul,
        Nat.sub_zero, Nat.choose_zero_right, Nat.cast_zero, add_zero]
      ring
    rw [hrhs]
    have hmid :
        (∑ k ∈ Finset.range m,
            (-1 : ℚ) ^ (m - k) * (m.choose k : ℚ) * f.eval (x + ((k + 1 : ℕ) : ℚ))) -
          ∑ k ∈ Finset.range m,
            (-1 : ℚ) ^ (m - (k + 1)) * (m.choose (k + 1) : ℚ) *
              f.eval (x + ((k + 1 : ℕ) : ℚ)) =
          ∑ k ∈ Finset.range m,
            (-1 : ℚ) ^ (m + 1 - (k + 1)) * ((m + 1).choose (k + 1) : ℚ) *
              f.eval (x + ((k + 1 : ℕ) : ℚ)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      rw [show m + 1 - (k + 1) = m - k by omega,
        show (m + 1).choose (k + 1) = m.choose k + m.choose (k + 1) from
          Nat.choose_succ_succ m k,
        show m - k = (m - (k + 1)) + 1 by omega, pow_succ]
      push_cast
      ring
    linarith [hmid, show (-1 : ℚ) ^ (m + 1) * f.eval x = -((-1 : ℚ) ^ m * f.eval x) by
      rw [pow_succ]; ring]

private lemma iterate_delta_eval_rev (m : ℕ) (f : Polynomial ℚ) (x : ℚ) :
    (delta^[m] f).eval x =
      ∑ r ∈ Finset.range (m + 1),
        (-1 : ℚ) ^ r * (m.choose r : ℚ) * f.eval (x + ((m - r : ℕ) : ℚ)) := by
  rw [iterate_delta_eval m f x]
  refine Finset.sum_bij (fun i _ => m - i)
    (fun i hi => by rw [Finset.mem_range] at hi ⊢; omega)
    (fun i₁ hi₁ i₂ hi₂ h => by rw [Finset.mem_range] at hi₁ hi₂; omega)
    (fun r hr => ⟨m - r, by rw [Finset.mem_range] at hr ⊢; omega, by
      rw [Finset.mem_range] at hr; omega⟩)
    fun i hi => by
      rw [Finset.mem_range] at hi
      rw [show m - (m - i) = i by omega, Nat.choose_symm (by omega)]

theorem OMA.solution : type_of% @OMA.S_oeis_a398690.main := by
  intro n j
  have hzero : ∑ r ∈ Finset.range (n + 2),
      (-1 : ℚ) ^ r * ((n + 1).choose r : ℚ) * (R_poly n).eval ((j : ℚ) - (r : ℚ)) = 0 := by
    have h0 := congrArg (Polynomial.eval ((j : ℚ) - ((n + 1 : ℕ) : ℚ)))
      (iterate_delta_zero n (R_poly n) (R_poly_natDegree n))
    rw [iterate_delta_eval_rev, Polynomial.eval_zero] at h0
    have hsum_eq : ∑ r ∈ Finset.range (n + 2),
        (-1 : ℚ) ^ r * ((n + 1).choose r : ℚ) * (R_poly n).eval ((j : ℚ) - (r : ℚ)) =
      ∑ r ∈ Finset.range (n + 1 + 1),
        (-1 : ℚ) ^ r * ((n + 1).choose r : ℚ) *
          (R_poly n).eval ((j : ℚ) - ((n + 1 : ℕ) : ℚ) + ((n + 1 - r : ℕ) : ℚ)) := by
      rw [show n + 2 = n + 1 + 1 by rfl]
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [Finset.mem_range] at hr
      congr 2
      rw [Nat.cast_sub (by omega)]
      ring
    exact hsum_eq.trans h0
  have hnum : ∀ n' j' : ℕ, OMA.S_oeis_a398690.numeratorCoeff n' j' =
      algebraMap ℚ ℝ (∑ i ∈ Finset.range (j' + 1),
        (-1 : ℚ) ^ i * ((n' + 1).choose i : ℚ) * (R_poly n').eval (j' - i : ℚ)) := by
    intro n' j'
    unfold OMA.S_oeis_a398690.numeratorCoeff
    rw [map_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [rowValue_eq_eval_Q n' (j' - i)]
    have hev : (R_poly n').eval ((j' : ℚ) - (i : ℚ)) =
        (Q_poly n').eval (2 * ((j' - i : ℕ) : ℚ) + 1) := by
      unfold R_poly
      rw [Polynomial.eval_comp, Nat.cast_sub (by omega)]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
        Polynomial.eval_X, Polynomial.eval_one]
    have hR : algebraMap ℚ ℝ ((R_poly n').eval ((j' : ℚ) - (i : ℚ))) =
        Polynomial.eval₂ (algebraMap ℚ ℝ) (2 * ((j' - i : ℕ) : ℝ) + 1) (Q_poly n') := by
      rw [hev]
      change algebraMap ℚ ℝ ((Q_poly n').eval₂ (RingHom.id ℚ) (2 * ((j' - i : ℕ) : ℚ) + 1)) = _
      rw [Polynomial.hom_eval₂]
      congr 1
      simp only [map_add, map_mul, map_ofNat, map_natCast, map_one]
    rw [map_mul, map_mul, ← hR]
    simp [map_pow, map_neg, map_one, map_natCast]
  by_cases hjn : j ≤ n
  · simp only [hjn, ite_true]
    rw [hnum n j, hnum n (n - j)]
    have hsplit : Finset.range (n + 2) = Finset.range (j + 1) ∪ Finset.Ico (j + 1) (n + 2) := by
      ext r
      simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
      omega
    have hdisj : Disjoint (Finset.range (j + 1)) (Finset.Ico (j + 1) (n + 2)) := by
      rw [Finset.disjoint_left]
      intro r hr1 hr2
      rw [Finset.mem_range] at hr1
      rw [Finset.mem_Ico] at hr2
      omega
    rw [hsplit, Finset.sum_union hdisj] at hzero
    have htail :
        ∑ r ∈ Finset.Ico (j + 1) (n + 2),
            (-1 : ℚ) ^ r * ((n + 1).choose r : ℚ) * (R_poly n).eval ((j : ℚ) - (r : ℚ)) =
          -∑ t ∈ Finset.range (n - j + 1),
            (-1 : ℚ) ^ t * ((n + 1).choose t : ℚ) *
              (R_poly n).eval (((n - j : ℕ) : ℚ) - (t : ℚ)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_bij (fun r _ => n + 1 - r)
        (fun r hr => by rw [Finset.mem_Ico] at hr; rw [Finset.mem_range]; omega)
        (fun r₁ hr₁ r₂ hr₂ h => by rw [Finset.mem_Ico] at hr₁ hr₂; omega)
        (fun t ht => ⟨n + 1 - t, by rw [Finset.mem_range] at ht; rw [Finset.mem_Ico]; omega, by
          rw [Finset.mem_range] at ht; omega⟩)
        fun r hr => by
          rw [Finset.mem_Ico] at hr
          have hsub : (j : ℚ) - (r : ℚ) =
              -(((n - j - (n + 1 - r) : ℕ) : ℚ)) - 1 := by
            rw [Nat.cast_sub (by omega : n + 1 - r ≤ n - j),
              Nat.cast_sub (by omega : j ≤ n),
              Nat.cast_sub (by omega : r ≤ n + 1)]
            push_cast
            ring
          rw [hsub, R_poly_eval_neg]
          have harg_eq : (((n - j : ℕ) : ℚ) - ((n + 1 - r : ℕ) : ℚ)) =
              ((n - j - (n + 1 - r) : ℕ) : ℚ) := by
            rw [Nat.cast_sub (by omega : n + 1 - r ≤ n - j)]
          rw [harg_eq]
          have hsign : (-1 : ℚ) ^ r * (-1 : ℚ) ^ n = -((-1 : ℚ) ^ (n + 1 - r)) := by
            rw [← pow_add, show r + n = (n + 1 - r) + (2 * r - 1) by omega, pow_add,
              show 2 * r - 1 = 2 * (r - 1) + 1 by omega, pow_add, pow_mul]
            norm_num
          calc
            (-1 : ℚ) ^ r * ((n + 1).choose r : ℚ) *
                ((-1 : ℚ) ^ n * (R_poly n).eval ((n - j - (n + 1 - r) : ℕ) : ℚ))
                = ((-1 : ℚ) ^ r * (-1 : ℚ) ^ n) * ((n + 1).choose (n + 1 - r) : ℚ) *
                    (R_poly n).eval ((n - j - (n + 1 - r) : ℕ) : ℚ) := by
                  rw [Nat.choose_symm (by omega : r ≤ n + 1)]
                  ring
            _ = -((-1 : ℚ) ^ (n + 1 - r) * ((n + 1).choose (n + 1 - r) : ℚ) *
                  (R_poly n).eval ((n - j - (n + 1 - r) : ℕ) : ℚ)) := by
                rw [hsign]
                ring
    rw [htail] at hzero
    have heq :
        ∑ i ∈ Finset.range (j + 1),
            (-1 : ℚ) ^ i * ((n + 1).choose i : ℚ) * (R_poly n).eval ((j : ℚ) - (i : ℚ)) =
          ∑ t ∈ Finset.range (n - j + 1),
            (-1 : ℚ) ^ t * ((n + 1).choose t : ℚ) *
              (R_poly n).eval (((n - j : ℕ) : ℚ) - (t : ℚ)) := by
      linarith
    rw [heq]
  · simp only [hjn, ite_false]
    rw [hnum n j]
    have hsplit : Finset.range (j + 1) = Finset.range (n + 2) ∪ Finset.Ico (n + 2) (j + 1) := by
      ext r
      simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
      omega
    have hdisj : Disjoint (Finset.range (n + 2)) (Finset.Ico (n + 2) (j + 1)) := by
      rw [Finset.disjoint_left]
      intro r hr1 hr2
      rw [Finset.mem_range] at hr1
      rw [Finset.mem_Ico] at hr2
      omega
    have htail0 : ∑ r ∈ Finset.Ico (n + 2) (j + 1),
        (-1 : ℚ) ^ r * ((n + 1).choose r : ℚ) * (R_poly n).eval ((j : ℚ) - (r : ℚ)) = 0 := by
      refine Finset.sum_eq_zero fun r hr => ?_
      rw [Finset.mem_Ico] at hr
      rw [Nat.choose_eq_zero_of_lt (by omega : n + 1 < r)]
      simp
    have hsum0 : ∑ i ∈ Finset.range (j + 1),
        (-1 : ℚ) ^ i * ((n + 1).choose i : ℚ) * (R_poly n).eval ((j : ℚ) - (i : ℚ)) = 0 := by
      rw [hsplit, Finset.sum_union hdisj, htail0, add_zero]
      exact hzero
    rw [hsum0, map_zero]
