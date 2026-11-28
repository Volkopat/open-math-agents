import OMAStatements.S_oeis_a002190

open OMA.S_oeis_a002190 PowerSeries

private lemma factorial_cast_pos (n : ℕ) : (0 : ℚ) < (n.factorial : ℚ) :=
  Nat.cast_pos.mpr (Nat.factorial_pos n)

private lemma factorial_cast_ne_zero (n : ℕ) : (n.factorial : ℚ) ≠ 0 :=
  ne_of_gt (factorial_cast_pos n)

private lemma choose_cast_eq (p q : ℕ) (h : q ≤ p) :
    (p.choose q : ℚ) = (p.factorial : ℚ) / ((q.factorial : ℚ) * ((p - q).factorial : ℚ)) := by
  have hnat : p.choose q * q.factorial * (p - q).factorial = p.factorial :=
    Nat.choose_mul_factorial_mul_factorial h
  have hq : (p.choose q : ℚ) * (q.factorial : ℚ) * ((p - q).factorial : ℚ) = (p.factorial : ℚ) := by
    exact_mod_cast hnat
  rw [eq_div_iff (mul_ne_zero (factorial_cast_ne_zero q) (factorial_cast_ne_zero (p - q)))]
  linarith

private lemma neg_one_pow_cancel (M k : ℕ) (hk : k ≤ M) :
    (-1 : ℚ) ^ M * (-1 : ℚ) ^ (M - k) = (-1 : ℚ) ^ k := by
  rw [← pow_add]
  have h : M + (M - k) = 2 * (M - k) + k := by omega
  rw [h, pow_add, pow_mul]
  norm_num

private lemma constantCoeff_f : PowerSeries.constantCoeff f = ((1 : ℚˣ) : ℚ) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, f, PowerSeries.coeff_mk]
  norm_num

private lemma gd_mul_f : gd * f = -fd := by
  rw [gd, mul_assoc, PowerSeries.invOfUnit_mul f 1 constantCoeff_f, mul_one]

private lemma coeff_mul_eq_sum_range (φ ψ : PowerSeries ℚ) (n : ℕ) :
    coeff n (φ * ψ) = ∑ k ∈ Finset.range (n + 1), coeff k φ * coeff (n - k) ψ := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i φ * coeff j ψ) n]

private lemma sum_coeff_gd_mul_f (r : ℕ) :
    ∑ n ∈ Finset.range (r + 1),
      coeff n gd * ((-1 : ℚ) ^ (r - n) / ((r - n).factorial : ℚ) ^ 2) =
    (-1 : ℚ) ^ r / ((r.factorial : ℚ) * ((r + 1).factorial : ℚ)) := by
  have hcoeff := congrArg (PowerSeries.coeff r) gd_mul_f
  rw [coeff_mul_eq_sum_range] at hcoeff
  have hL :
      ∑ n ∈ Finset.range (r + 1), coeff n gd * coeff (r - n) f =
      ∑ n ∈ Finset.range (r + 1),
        coeff n gd * ((-1 : ℚ) ^ (r - n) / ((r - n).factorial : ℚ) ^ 2) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [f, PowerSeries.coeff_mk]
  rw [← hL, hcoeff, map_neg, fd, PowerSeries.coeff_mk, f, PowerSeries.coeff_mk]
  have hfac : ((r + 1).factorial : ℚ) = ((r : ℚ) + 1) * (r.factorial : ℚ) := by
    have hnat : (r + 1).factorial = (r + 1) * r.factorial := Nat.factorial_succ r
    have hq : ((r + 1).factorial : ℚ) = (((r + 1 : ℕ) : ℚ)) * (r.factorial : ℚ) := by
      exact_mod_cast hnat
    push_cast at hq
    exact hq
  have hpos1 : (0 : ℚ) < (r.factorial : ℚ) := factorial_cast_pos r
  have hpow : (-1 : ℚ) ^ (r + 1) = -((-1 : ℚ) ^ r) := by
    rw [pow_succ]
    ring
  rw [hpow, hfac, mul_div_assoc', ← neg_div, div_eq_div_iff (by positivity) (by positivity)]
  ring

private lemma catalan_cast_eq (n : ℕ) :
    (catalan n : ℚ) = ((2 * n).factorial : ℚ) / ((n.factorial : ℚ) * ((n + 1).factorial : ℚ)) := by
  have h1 : catalan n * (n + 1) = n.centralBinom := by
    rw [catalan_eq_centralBinom_div, Nat.div_mul_cancel (Nat.succ_dvd_centralBinom n)]
  have h2 : n.centralBinom * n.factorial * n.factorial = (2 * n).factorial := by
    rw [Nat.centralBinom_eq_two_mul_choose]
    have hchoose := Nat.choose_mul_factorial_mul_factorial (by omega : n ≤ 2 * n)
    have hsub : 2 * n - n = n := by omega
    rw [hsub] at hchoose
    exact hchoose
  have hnat : catalan n * (n.factorial * (n + 1).factorial) = (2 * n).factorial := by
    rw [Nat.factorial_succ]
    calc
      catalan n * (n.factorial * ((n + 1) * n.factorial))
        = (catalan n * (n + 1)) * n.factorial * n.factorial := by ring
      _ = n.centralBinom * n.factorial * n.factorial := by rw [h1]
      _ = (2 * n).factorial := h2
  have hq : (catalan n : ℚ) * ((n.factorial : ℚ) * ((n + 1).factorial : ℚ)) =
      ((2 * n).factorial : ℚ) := by
    exact_mod_cast hnat
  rw [eq_div_iff (mul_ne_zero (factorial_cast_ne_zero n) (factorial_cast_ne_zero (n + 1)))]
  exact hq

private lemma a_succ_mul_catalan (n : ℕ) :
    a (n + 1) * (catalan n : ℚ) = ((2 * n).factorial : ℚ) * coeff n gd := by
  have ha : a (n + 1) = ((n + 1).factorial : ℚ) ^ 2 * (coeff n gd / ((n + 1 : ℕ) : ℚ)) := by
    simp [a]
  rw [ha, catalan_cast_eq n]
  have hfac : ((n + 1).factorial : ℚ) = ((n + 1 : ℕ) : ℚ) * (n.factorial : ℚ) := by
    have hnat : (n + 1).factorial = (n + 1) * n.factorial := Nat.factorial_succ n
    exact_mod_cast hnat
  have hpos1 : (0 : ℚ) < ((n + 1 : ℕ) : ℚ) := Nat.cast_pos.mpr (Nat.succ_pos n)
  have hpos2 : (0 : ℚ) < (n.factorial : ℚ) := factorial_cast_pos n
  rw [hfac]
  simp only [mul_div_assoc', div_mul_eq_mul_div, div_div]
  rw [div_eq_iff (by positivity)]
  ring

private noncomputable def negBinom (a : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun k => ((a + k).choose k : ℚ)

private lemma negBinom_succ_mul (a : ℕ) :
    negBinom (a + 1) * (1 - PowerSeries.X) = negBinom a := by
  ext k
  cases k with
  | zero =>
    rw [mul_sub, mul_one, map_sub, PowerSeries.coeff_zero_mul_X, sub_zero]
    simp [negBinom]
  | succ k =>
    rw [mul_sub, mul_one, map_sub, PowerSeries.coeff_succ_mul_X]
    simp only [negBinom, PowerSeries.coeff_mk]
    have h : (a + 1 + (k + 1)).choose (k + 1) =
        (a + (k + 1)).choose (k + 1) + (a + 1 + k).choose k := by
      have h1 : a + 1 + (k + 1) = (a + k + 1) + 1 := by omega
      have h2 : a + (k + 1) = a + k + 1 := by omega
      have h3 : a + 1 + k = a + k + 1 := by omega
      rw [h1, h2, h3, Nat.choose_succ_succ, add_comm]
    have hq : (((a + 1 + (k + 1)).choose (k + 1) : ℕ) : ℚ) =
        (((a + (k + 1)).choose (k + 1) : ℕ) : ℚ) + (((a + 1 + k).choose k : ℕ) : ℚ) := by
      exact_mod_cast h
    linarith

private lemma negBinom_zero_mul : negBinom 0 * (1 - PowerSeries.X) = 1 := by
  ext k
  cases k with
  | zero =>
    rw [mul_sub, mul_one, map_sub, PowerSeries.coeff_zero_mul_X, sub_zero,
      PowerSeries.coeff_one]
    simp [negBinom]
  | succ k =>
    rw [mul_sub, mul_one, map_sub, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_one]
    simp [negBinom]

private lemma negBinom_mul_pow (M : ℕ) : ∀ a : ℕ, M ≤ a →
    negBinom a * (1 - PowerSeries.X) ^ M = negBinom (a - M) := by
  induction M with
  | zero =>
    intro a _
    simp
  | succ M ih =>
    intro a hMa
    cases a with
    | zero => omega
    | succ b =>
      rw [pow_succ', ← mul_assoc, negBinom_succ_mul, ih b (by omega), Nat.succ_sub_succ]

private lemma negBinom_mul_pow_succ (m : ℕ) :
    negBinom m * (1 - PowerSeries.X) ^ (m + 1) = 1 := by
  rw [pow_succ, ← mul_assoc, negBinom_mul_pow m m (le_refl m), Nat.sub_self, negBinom_zero_mul]

private lemma coeff_one_sub_X_pow (M : ℕ) : ∀ k : ℕ,
    coeff k ((1 - PowerSeries.X : PowerSeries ℚ) ^ M) = (-1 : ℚ) ^ k * (M.choose k : ℚ) := by
  induction M with
  | zero =>
    intro k
    rw [pow_zero, PowerSeries.coeff_one]
    cases k with
    | zero => simp
    | succ k => simp
  | succ M ih =>
    intro k
    rw [pow_succ]
    cases k with
    | zero =>
      rw [mul_sub, mul_one, map_sub, PowerSeries.coeff_zero_mul_X, sub_zero, ih 0]
      simp
    | succ k =>
      rw [mul_sub, mul_one, map_sub, PowerSeries.coeff_succ_mul_X, ih (k + 1), ih k]
      have hnat : (M + 1).choose (k + 1) = M.choose k + M.choose (k + 1) :=
        Nat.choose_succ_succ M k
      have hq : (((M + 1).choose (k + 1) : ℕ) : ℚ) =
          (M.choose k : ℚ) + (M.choose (k + 1) : ℚ) := by
        exact_mod_cast hnat
      rw [hq, pow_succ]
      ring

private lemma binom_id1 (a M : ℕ) (hM : M ≤ a) :
    ∑ k ∈ Finset.range (M + 1),
      (-1 : ℚ) ^ k * (M.choose k : ℚ) * ((a + k).choose k : ℚ) =
    (-1 : ℚ) ^ M * (a.choose M : ℚ) := by
  have hc := congrArg (PowerSeries.coeff M) (negBinom_mul_pow M a hM)
  rw [coeff_mul_eq_sum_range] at hc
  have hR : coeff M (negBinom (a - M)) = (a.choose M : ℚ) := by
    rw [negBinom, PowerSeries.coeff_mk, Nat.sub_add_cancel hM]
  rw [hR] at hc
  have hmul := congrArg (fun x : ℚ => (-1 : ℚ) ^ M * x) hc
  rw [Finset.mul_sum] at hmul
  rw [← hmul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkM : k ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [negBinom, PowerSeries.coeff_mk, coeff_one_sub_X_pow M (M - k), Nat.choose_symm hkM]
  calc
    (-1 : ℚ) ^ k * (M.choose k : ℚ) * ((a + k).choose k : ℚ)
      = ((-1 : ℚ) ^ M * (-1 : ℚ) ^ (M - k)) * (M.choose k : ℚ) * ((a + k).choose k : ℚ) := by
          rw [neg_one_pow_cancel M k hkM]
    _ = (-1 : ℚ) ^ M * (((a + k).choose k : ℚ) * ((-1 : ℚ) ^ (M - k) * (M.choose k : ℚ))) := by
          ring

private lemma binom_id2 (m : ℕ) :
    ∑ r ∈ Finset.range (m + 1),
      (-1 : ℚ) ^ r * ((m + 1).choose (r + 1) : ℚ) * ((m + r).choose r : ℚ) =
    if m = 0 then 1 else 0 := by
  have hc := congrArg (PowerSeries.coeff m) (negBinom_mul_pow_succ m)
  rw [coeff_mul_eq_sum_range, PowerSeries.coeff_one] at hc
  have hmul := congrArg (fun x : ℚ => (-1 : ℚ) ^ m * x) hc
  rw [Finset.mul_sum] at hmul
  have hR : (-1 : ℚ) ^ m * (if m = 0 then 1 else 0) = if m = 0 then 1 else 0 := by
    split_ifs with hm
    · subst hm
      norm_num
    · ring
  rw [← hR, ← hmul]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hrm : r ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  have hsymm : (m + 1).choose (m - r) = (m + 1).choose (r + 1) := by
    have hsub : m + 1 - (r + 1) = m - r := by omega
    rw [← hsub, Nat.choose_symm (by omega : r + 1 ≤ m + 1)]
  rw [negBinom, PowerSeries.coeff_mk, coeff_one_sub_X_pow (m + 1) (m - r), hsymm]
  calc
    (-1 : ℚ) ^ r * ((m + 1).choose (r + 1) : ℚ) * ((m + r).choose r : ℚ)
      = ((-1 : ℚ) ^ m * (-1 : ℚ) ^ (m - r)) * ((m + 1).choose (r + 1) : ℚ) *
          ((m + r).choose r : ℚ) := by
          rw [neg_one_pow_cancel m r hrm]
    _ = (-1 : ℚ) ^ m *
          (((m + r).choose r : ℚ) * ((-1 : ℚ) ^ (m - r) * ((m + 1).choose (r + 1) : ℚ))) := by
          ring

private noncomputable def matC (m r : ℕ) : ℚ :=
  ((m + r).factorial : ℚ) / ((m - r).factorial : ℚ)

private lemma C_mul_f (m n : ℕ) (hnm : n ≤ m) :
    ∑ r ∈ Finset.Icc n m,
      matC m r * ((-1 : ℚ) ^ (r - n) / ((r - n).factorial : ℚ) ^ 2) =
    ((2 * n).factorial : ℚ) * (((m + n).choose (m - n) : ℕ) : ℚ) ^ 2 * (-1 : ℚ) ^ (m - n) := by
  have hreidx :
      ∑ r ∈ Finset.Icc n m,
        matC m r * ((-1 : ℚ) ^ (r - n) / ((r - n).factorial : ℚ) ^ 2) =
      ∑ k ∈ Finset.range (m - n + 1),
        (((m + n).factorial : ℚ) / ((m - n).factorial : ℚ)) *
          ((-1 : ℚ) ^ k * ((m - n).choose k : ℚ) * (((m + n) + k).choose k : ℚ)) := by
    symm
    refine Finset.sum_bij (fun k _ => n + k) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_range, Finset.mem_Icc] at hk ⊢
      omega
    · intro k1 _ k2 _ h
      omega
    · intro r hr
      simp only [Finset.mem_Icc] at hr
      refine ⟨r - n, ?_, ?_⟩
      · simp only [Finset.mem_range]
        omega
      · omega
    · intro k hk
      have hkM : k ≤ m - n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have h1 : m + (n + k) = m + n + k := by omega
      have h2 : m - (n + k) = m - n - k := by omega
      have h3 : n + k - n = k := by omega
      have h4 : m + n + k - k = m + n := by omega
      rw [matC, h1, h2, h3, choose_cast_eq (m - n) k hkM,
        choose_cast_eq (m + n + k) k (by omega), h4]
      have hpos1 : (0 : ℚ) < ((m + n).factorial : ℚ) := factorial_cast_pos (m + n)
      have hpos2 : (0 : ℚ) < ((m - n).factorial : ℚ) := factorial_cast_pos (m - n)
      have hpos3 : (0 : ℚ) < (k.factorial : ℚ) := factorial_cast_pos k
      have hpos4 : (0 : ℚ) < ((m - n - k).factorial : ℚ) := factorial_cast_pos (m - n - k)
      simp only [mul_div_assoc', div_mul_eq_mul_div, div_div]
      rw [div_eq_div_iff (by positivity) (by positivity)]
      ring
  rw [hreidx, ← Finset.mul_sum, binom_id1 (m + n) (m - n) (by omega)]
  have hsub : m + n - (m - n) = 2 * n := by omega
  have hch := choose_cast_eq (m + n) (m - n) (by omega)
  rw [hsub] at hch
  have hne1 : ((m - n).factorial : ℚ) ≠ 0 := factorial_cast_ne_zero (m - n)
  have hne2 : ((2 * n).factorial : ℚ) ≠ 0 := factorial_cast_ne_zero (2 * n)
  calc
    (((m + n).factorial : ℚ) / ((m - n).factorial : ℚ)) *
        ((-1 : ℚ) ^ (m - n) * ((m + n).choose (m - n) : ℚ))
      = (((2 * n).factorial : ℚ) * ((m + n).choose (m - n) : ℚ)) *
          ((-1 : ℚ) ^ (m - n) * ((m + n).choose (m - n) : ℚ)) := by
          congr 1
          rw [hch, mul_div_assoc', div_eq_div_iff hne1 (mul_ne_zero hne1 hne2)]
          ring
    _ = ((2 * n).factorial : ℚ) * (((m + n).choose (m - n) : ℕ) : ℚ) ^ 2 *
          (-1 : ℚ) ^ (m - n) := by
          ring

private lemma C_mul_neg_fd (m : ℕ) :
    ∑ r ∈ Finset.range (m + 1),
      matC m r * ((-1 : ℚ) ^ r / ((r.factorial : ℚ) * ((r + 1).factorial : ℚ))) =
    if m = 0 then 1 else 0 := by
  have hrew :
      ∑ r ∈ Finset.range (m + 1),
        matC m r * ((-1 : ℚ) ^ r / ((r.factorial : ℚ) * ((r + 1).factorial : ℚ))) =
      ∑ r ∈ Finset.range (m + 1),
        (1 / ((m + 1 : ℕ) : ℚ)) *
          ((-1 : ℚ) ^ r * ((m + 1).choose (r + 1) : ℚ) * ((m + r).choose r : ℚ)) := by
    refine Finset.sum_congr rfl fun r hr => ?_
    have hrm : r ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    have hsub1 : m + 1 - (r + 1) = m - r := by omega
    have hsub2 : m + r - r = m := by omega
    rw [matC, choose_cast_eq (m + 1) (r + 1) (by omega), hsub1,
      choose_cast_eq (m + r) r (by omega), hsub2]
    have hfac : ((m + 1).factorial : ℚ) = ((m + 1 : ℕ) : ℚ) * (m.factorial : ℚ) := by
      have hnat : (m + 1).factorial = (m + 1) * m.factorial := Nat.factorial_succ m
      exact_mod_cast hnat
    have hpos1 : (0 : ℚ) < ((m + 1 : ℕ) : ℚ) := Nat.cast_pos.mpr (Nat.succ_pos m)
    have hpos2 : (0 : ℚ) < (m.factorial : ℚ) := factorial_cast_pos m
    have hpos3 : (0 : ℚ) < (r.factorial : ℚ) := factorial_cast_pos r
    have hpos4 : (0 : ℚ) < ((r + 1).factorial : ℚ) := factorial_cast_pos (r + 1)
    have hpos5 : (0 : ℚ) < ((m - r).factorial : ℚ) := factorial_cast_pos (m - r)
    rw [hfac]
    simp only [mul_div_assoc', div_mul_eq_mul_div, div_div]
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [hrew, ← Finset.mul_sum, binom_id2 m]
  split_ifs with hm
  · subst hm
    norm_num
  · ring

private lemma sum_range_sum_Icc_comm (m : ℕ) (F : ℕ → ℕ → ℚ) :
    ∑ n ∈ Finset.range (m + 1), ∑ r ∈ Finset.Icc n m, F n r =
    ∑ r ∈ Finset.range (m + 1), ∑ n ∈ Finset.range (r + 1), F n r := by
  have hL : ∑ n ∈ Finset.range (m + 1), ∑ r ∈ Finset.Icc n m, F n r =
      ∑ n ∈ Finset.range (m + 1), ∑ r ∈ Finset.range (m + 1), if n ≤ r then F n r else 0 := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext r
    simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_range]
    omega
  have hR : ∑ r ∈ Finset.range (m + 1), ∑ n ∈ Finset.range (r + 1), F n r =
      ∑ r ∈ Finset.range (m + 1), ∑ n ∈ Finset.range (m + 1), if n ≤ r then F n r else 0 := by
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    have : r < m + 1 := Finset.mem_range.mp hr
    omega
  rw [hL, hR, Finset.sum_comm]

theorem OMA.solution : type_of% @OMA.S_oeis_a002190.main := by
  intro m
  have hstep1 :
      ∑ n ∈ Finset.range (m + 1), a (n + 1) * (catalan n : ℚ) *
        ((((2 * n + (m - n)).choose (m - n) : ℕ) : ℚ) ^ 2 * (-1) ^ (m - n)) =
      ∑ n ∈ Finset.range (m + 1),
        ∑ r ∈ Finset.Icc n m,
          coeff n gd * (matC m r * ((-1 : ℚ) ^ (r - n) / ((r - n).factorial : ℚ) ^ 2)) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have hnm : n ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    have hadd : 2 * n + (m - n) = m + n := by omega
    rw [a_succ_mul_catalan n, hadd, ← Finset.mul_sum, C_mul_f m n hnm]
    ring
  rw [hstep1, sum_range_sum_Icc_comm]
  have hstep2 :
      ∑ r ∈ Finset.range (m + 1),
        ∑ n ∈ Finset.range (r + 1),
          coeff n gd * (matC m r * ((-1 : ℚ) ^ (r - n) / ((r - n).factorial : ℚ) ^ 2)) =
      ∑ r ∈ Finset.range (m + 1),
        matC m r * ((-1 : ℚ) ^ r / ((r.factorial : ℚ) * ((r + 1).factorial : ℚ))) := by
    refine Finset.sum_congr rfl fun r _ => ?_
    calc
      ∑ n ∈ Finset.range (r + 1),
          coeff n gd * (matC m r * ((-1 : ℚ) ^ (r - n) / ((r - n).factorial : ℚ) ^ 2))
        = ∑ n ∈ Finset.range (r + 1),
            matC m r * (coeff n gd * ((-1 : ℚ) ^ (r - n) / ((r - n).factorial : ℚ) ^ 2)) := by
            refine Finset.sum_congr rfl fun n _ => ?_
            ring
      _ = matC m r * ∑ n ∈ Finset.range (r + 1),
            coeff n gd * ((-1 : ℚ) ^ (r - n) / ((r - n).factorial : ℚ) ^ 2) := by
            rw [← Finset.mul_sum]
      _ = matC m r * ((-1 : ℚ) ^ r / ((r.factorial : ℚ) * ((r + 1).factorial : ℚ))) := by
            rw [sum_coeff_gd_mul_f r]
  rw [hstep2, C_mul_neg_fd m]
