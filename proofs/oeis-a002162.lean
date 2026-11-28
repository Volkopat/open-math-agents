import OMAStatements.S_oeis_a002162

private lemma S_zero_eq_zero : OMA.S_oeis_a002162.S 0 = 0 := by
  have hfun :
      (fun n : ℕ =>
          (-1 : ℝ) ^ (n + 1 + 0 + 1) * ((n + 1 + 0 : ℕ) : ℝ) /
            (∏ i ∈ Finset.range (2 * 0 + 1), ((n + 1 + i : ℕ) : ℝ)) ^ 2) =
        fun n : ℕ => (-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ) := by
    ext n
    simp only [mul_zero, zero_add, Finset.range_one, Finset.prod_singleton, add_zero]
    have hpow : (-1 : ℝ) ^ (n + 1 + 1) = (-1 : ℝ) ^ n := by
      rw [show n + 1 + 1 = n + 2 by omega, pow_add]
      norm_num
    have hpos : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [hpow, sq]
    field_simp [hpos]
  have hnot : ¬ Summable (fun n : ℕ => (-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)) := by
    intro hs
    have hnorm : Summable (fun n : ℕ => ‖(-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)‖) := hs.norm
    have heq : (fun n : ℕ => ‖(-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ)‖) =
        fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) := by
      ext n
      rw [norm_div, norm_pow, norm_neg, norm_one, one_pow,
        Real.norm_of_nonneg (by positivity)]
    rw [heq] at hnorm
    have hshift : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ)) :=
      (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ)) 1).mp hnorm
    exact Real.not_summable_one_div_natCast hshift
  unfold OMA.S_oeis_a002162.S
  rw [hfun]
  exact tsum_eq_zero_of_not_summable hnot

private lemma map_int_eval (G : Polynomial ℤ) (z : ℤ) :
    (G.map (Int.castRingHom ℝ)).eval (z : ℝ) = ((G.eval z : ℤ) : ℝ) := by
  induction G using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.map_add, Polynomial.eval_add, hp, hq, Int.cast_add]
  | monomial n a =>
    simp only [Polynomial.map_monomial, eq_intCast, Polynomial.eval_monomial, Int.cast_mul,
      Int.cast_pow]

private lemma log_two_not_rat (c : ℚ) : Real.log 2 ≠ (c : ℝ) := by
  intro hlog
  have hlog_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc_pos : 0 < c := Rat.cast_pos.mp (hlog ▸ hlog_pos)
  have hnum_pos : 0 < c.num := Rat.num_pos.mpr hc_pos
  set p : ℕ := c.num.natAbs
  set q : ℕ := c.den
  have hp_pos : 0 < p := Int.natAbs_pos.mpr hnum_pos.ne'
  have hq_pos : 0 < q := c.pos
  have hp_int : (p : ℤ) = c.num := Int.natAbs_of_nonneg hnum_pos.le
  have hcr : (c : ℝ) = (p : ℝ) / (q : ℝ) := by
    rw [Rat.cast_def, ← hp_int]
    push_cast
    rfl
  have hexp_pq : Real.exp (p : ℝ) = (2 : ℝ) ^ q := by
    have hq_ne : (q : ℝ) ≠ 0 := by positivity
    have hmul : (p : ℝ) = (q : ℝ) * Real.log 2 := by
      rw [hlog, hcr]
      field_simp [hq_ne]
    rw [hmul, Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hC_pos : 0 < (2 : ℝ) ^ q * (p : ℝ) ^ 2 := by positivity
  have hev : ∀ᶠ k : ℕ in Filter.atTop,
      ((p : ℝ) ^ 2) ^ k / (k.factorial : ℝ) < ((2 : ℝ) ^ q * (p : ℝ) ^ 2)⁻¹ :=
    (FloorSemiring.tendsto_pow_div_factorial_atTop ((p : ℝ) ^ 2)).eventually
      (gt_mem_nhds (inv_pos.mpr hC_pos))
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hev
  let m : ℕ := K + 1
  have hm_pos : 0 < m := Nat.succ_pos K
  have hK_le : K ≤ m - 1 := le_rfl
  have hbound : (2 : ℝ) ^ q * (p : ℝ) ^ 2 * ((p : ℝ) ^ 2) ^ (m - 1) < ((m - 1).factorial : ℝ) := by
    have hKm := hK (m - 1) hK_le
    have hfac_pos : (0 : ℝ) < ((m - 1).factorial : ℝ) := by positivity
    have h1 : ((p : ℝ) ^ 2) ^ (m - 1) < ((2 : ℝ) ^ q * (p : ℝ) ^ 2)⁻¹ * ((m - 1).factorial : ℝ) :=
      (div_lt_iff₀ hfac_pos).mp hKm
    have h2 := mul_lt_mul_of_pos_left h1 hC_pos
    rw [← mul_assoc, mul_inv_cancel₀ hC_pos.ne', one_mul] at h2
    exact h2
  let P : Polynomial ℤ :=
    Polynomial.X ^ (m - 1) * (Polynomial.C (p : ℤ) - Polynomial.X) ^ m
  let F : Polynomial ℤ := Polynomial.sumIDeriv P
  let Pℝ : Polynomial ℝ := P.map (Int.castRingHom ℝ)
  let Fℝ : Polynomial ℝ := Polynomial.sumIDeriv Pℝ
  have hFmap : Fℝ = F.map (Int.castRingHom ℝ) := Polynomial.sumIDeriv_map P (Int.castRingHom ℝ)
  have hF_deriv : Fℝ = Pℝ + Polynomial.derivative Fℝ := Polynomial.sumIDeriv_eq_self_add Pℝ
  let g : ℝ → ℝ := fun x => -Real.exp ((p : ℝ) - x) * Fℝ.eval x
  have hg_deriv : ∀ x : ℝ, HasDerivAt g (Real.exp ((p : ℝ) - x) * Pℝ.eval x) x := by
    intro x
    have hexp : HasDerivAt (fun t : ℝ => -Real.exp ((p : ℝ) - t)) (Real.exp ((p : ℝ) - x)) x := by
      have hsub : HasDerivAt (fun t : ℝ => (p : ℝ) - t) (0 - 1) x :=
        (hasDerivAt_const x (p : ℝ)).sub (hasDerivAt_id x)
      have h1 := (hsub.exp).neg
      rw [show -(Real.exp ((p : ℝ) - x) * (0 - 1)) = Real.exp ((p : ℝ) - x) by ring] at h1
      exact h1
    have hF := Fℝ.hasDerivAt x
    have hmul := hexp.mul hF
    have heval : Fℝ.eval x - (Polynomial.derivative Fℝ).eval x = Pℝ.eval x := by
      have he := congrArg (Polynomial.eval x) hF_deriv
      rw [Polynomial.eval_add] at he
      linarith
    have hd_eq :
        Real.exp ((p : ℝ) - x) * Fℝ.eval x +
            -Real.exp ((p : ℝ) - x) * (Polynomial.derivative Fℝ).eval x =
          Real.exp ((p : ℝ) - x) * Pℝ.eval x := by
      rw [← heval]
      ring
    rw [hd_eq] at hmul
    exact hmul
  have hcont : ContinuousOn g (Set.Icc 0 (p : ℝ)) := fun x _ =>
    (hg_deriv x).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioo 0 (p : ℝ), HasDerivAt g (Real.exp ((p : ℝ) - x) * Pℝ.eval x) x :=
    fun x _ => hg_deriv x
  obtain ⟨ξ, hξ, hslope⟩ :=
    exists_hasDerivAt_eq_slope g (fun x => Real.exp ((p : ℝ) - x) * Pℝ.eval x)
      (by positivity) hcont hderiv
  have hF0_real : Fℝ.eval (0 : ℝ) = ((F.eval (0 : ℤ) : ℤ) : ℝ) := by
    rw [hFmap, ← Int.cast_zero]
    exact map_int_eval F 0
  have hFp_real : Fℝ.eval (p : ℝ) = ((F.eval (p : ℤ) : ℤ) : ℝ) := by
    rw [hFmap, ← Int.cast_natCast]
    exact map_int_eval F p
  have hg0 : g 0 = -((2 : ℝ) ^ q * ((F.eval (0 : ℤ) : ℤ) : ℝ)) := by
    dsimp [g]
    rw [sub_zero, hexp_pq, hF0_real]
    ring
  have hgp_val : g (p : ℝ) = -((F.eval (p : ℤ) : ℤ) : ℝ) := by
    dsimp [g]
    rw [sub_self, Real.exp_zero, hFp_real]
    ring
  have hmvt :
      ((2 : ℝ) ^ q * ((F.eval (0 : ℤ) : ℤ) : ℝ) - ((F.eval (p : ℤ) : ℤ) : ℝ)) =
        (p : ℝ) * Real.exp ((p : ℝ) - ξ) * Pℝ.eval ξ := by
    have hp_ne : (p : ℝ) ≠ 0 := by positivity
    rw [hg0, hgp_val, sub_zero] at hslope
    have hmul := congrArg ((p : ℝ) * ·) hslope
    rw [mul_div_cancel₀ _ hp_ne] at hmul
    linear_combination -hmul
  have hPℝ_eval : Pℝ.eval ξ = ξ ^ (m - 1) * ((p : ℝ) - ξ) ^ m := by
    dsimp [Pℝ, P]
    rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_pow, Polynomial.map_sub,
      Polynomial.map_C, Polynomial.map_X, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]
    simp only [eq_intCast, Int.cast_natCast]
  have hξ_lo : 0 < ξ := hξ.1
  have hξ_hi : ξ < (p : ℝ) := hξ.2
  have hdiff_pos : 0 < (p : ℝ) - ξ := sub_pos.mpr hξ_hi
  have hmvt_pos : 0 < (2 : ℝ) ^ q * ((F.eval (0 : ℤ) : ℤ) : ℝ) - ((F.eval (p : ℤ) : ℤ) : ℝ) := by
    rw [hmvt, hPℝ_eval]
    positivity
  have hmvt_lt : (2 : ℝ) ^ q * ((F.eval (0 : ℤ) : ℤ) : ℝ) - ((F.eval (p : ℤ) : ℤ) : ℝ) <
      ((m - 1).factorial : ℝ) := by
    rw [hmvt, hPℝ_eval]
    have hexp_lt : Real.exp ((p : ℝ) - ξ) < (2 : ℝ) ^ q := by
      rw [← hexp_pq]
      exact Real.exp_lt_exp.mpr (by linarith)
    have hpow1 : ξ ^ (m - 1) ≤ (p : ℝ) ^ (m - 1) :=
      pow_le_pow_left₀ hξ_lo.le hξ_hi.le (m - 1)
    have hpow2 : ((p : ℝ) - ξ) ^ m ≤ (p : ℝ) ^ m :=
      pow_le_pow_left₀ hdiff_pos.le (by linarith) m
    have hP_le : ξ ^ (m - 1) * ((p : ℝ) - ξ) ^ m ≤ (p : ℝ) ^ (m - 1) * (p : ℝ) ^ m :=
      mul_le_mul hpow1 hpow2 (by positivity) (by positivity)
    have h_mul1 : (p : ℝ) * Real.exp ((p : ℝ) - ξ) * (ξ ^ (m - 1) * ((p : ℝ) - ξ) ^ m) <
        (p : ℝ) * (2 : ℝ) ^ q * (ξ ^ (m - 1) * ((p : ℝ) - ξ) ^ m) := by
      refine mul_lt_mul_of_pos_right ?_ (by positivity)
      exact mul_lt_mul_of_pos_left hexp_lt (by positivity)
    have h_mul2 : (p : ℝ) * (2 : ℝ) ^ q * (ξ ^ (m - 1) * ((p : ℝ) - ξ) ^ m) ≤
        (p : ℝ) * (2 : ℝ) ^ q * ((p : ℝ) ^ (m - 1) * (p : ℝ) ^ m) :=
      mul_le_mul_of_nonneg_left hP_le (by positivity)
    have hpow_eq : (p : ℝ) * (2 : ℝ) ^ q * ((p : ℝ) ^ (m - 1) * (p : ℝ) ^ m) =
        (2 : ℝ) ^ q * (p : ℝ) ^ 2 * ((p : ℝ) ^ 2) ^ (m - 1) := by
      have hm_eq : m = (m - 1) + 1 := (Nat.sub_add_cancel hm_pos).symm
      conv_lhs => rhs; rhs; rw [hm_eq, pow_succ]
      rw [← pow_mul, mul_comm 2 (m - 1), pow_mul]
      ring
    linarith
  obtain ⟨gp, _, hgp⟩ := Polynomial.eval_sumIDeriv_of_pos P hm_pos
  have hfac : (m.factorial : ℤ) = (m : ℤ) * ((m - 1).factorial : ℤ) := by
    exact_mod_cast Nat.mul_factorial_pred hm_pos.ne'
  have hF0 : F.eval 0 = ((m - 1).factorial : ℤ) * ((p : ℤ) ^ m + (m : ℤ) * gp.eval 0) := by
    have hP0 : P = (Polynomial.X - Polynomial.C (0 : ℤ)) ^ (m - 1) *
        (Polynomial.C (p : ℤ) - Polynomial.X) ^ m := by
      simp only [P, map_zero, sub_zero]
    have h := hgp (0 : ℤ) hP0
    dsimp [F]
    rw [h, nsmul_eq_mul, nsmul_eq_mul, hfac]
    have hev0 : ((Polynomial.C (p : ℤ) - Polynomial.X) ^ m).eval 0 = (p : ℤ) ^ m := by
      simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X,
        sub_zero]
    rw [hev0]
    ring
  have hFp : F.eval (p : ℤ) = ((m - 1).factorial : ℤ) * ((m : ℤ) * gp.eval (p : ℤ)) := by
    let p' : Polynomial ℤ :=
      Polynomial.X ^ (m - 1) * (-1 : Polynomial ℤ) ^ m * (Polynomial.X - Polynomial.C (p : ℤ))
    have hPp : P = (Polynomial.X - Polynomial.C (p : ℤ)) ^ (m - 1) * p' := by
      have hm_eq : m = (m - 1) + 1 := (Nat.sub_add_cancel hm_pos).symm
      have hneg : Polynomial.C (p : ℤ) - Polynomial.X = -(Polynomial.X - Polynomial.C (p : ℤ)) := by
        ring
      dsimp [P, p']
      rw [hneg, neg_eq_neg_one_mul, mul_pow]
      conv_lhs => rhs; rhs; rw [hm_eq, pow_succ]
      ring
    have h := hgp (p : ℤ) hPp
    have hp'_ev : p'.eval (p : ℤ) = 0 := by
      simp only [p', Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, sub_self, mul_zero]
    dsimp [F]
    rw [h, nsmul_eq_mul, nsmul_eq_mul, hp'_ev, mul_zero, zero_add, hfac]
    ring
  let N : ℤ := (2 : ℤ) ^ q * ((p : ℤ) ^ m + (m : ℤ) * gp.eval 0) - (m : ℤ) * gp.eval (p : ℤ)
  have hN_eq : (2 : ℤ) ^ q * F.eval 0 - F.eval (p : ℤ) = ((m - 1).factorial : ℤ) * N := by
    rw [hF0, hFp]
    dsimp [N]
    ring
  have hN_real : ((2 : ℝ) ^ q * ((F.eval (0 : ℤ) : ℤ) : ℝ) - ((F.eval (p : ℤ) : ℤ) : ℝ)) =
      ((m - 1).factorial : ℝ) * (N : ℝ) := by
    exact_mod_cast hN_eq
  have hfac_pos : (0 : ℝ) < ((m - 1).factorial : ℝ) := by positivity
  have hN_gt : 0 < N := by
    have h1 : (0 : ℝ) < (N : ℝ) := by
      nlinarith
    exact_mod_cast h1
  have hN_lt : N < 1 := by
    have h1 : (N : ℝ) < 1 := by
      nlinarith
    exact_mod_cast h1
  omega

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a002162.main) := by
  intro h
  obtain ⟨c, hc⟩ := h 0
  have hfac : ((2 * 0).factorial : ℝ) ^ 3 / (16 ^ 0 * (Nat.factorial 0 : ℝ) ^ 2) = 1 := by
    norm_num
  rw [hfac, S_zero_eq_zero, mul_zero, add_zero] at hc
  exact log_two_not_rat c hc
