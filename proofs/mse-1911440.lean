import OMAStatements.S_mse_1911440

namespace MSE1911440Proof

/-- Minkowski's question mark function on positive rationals `a / b`, mapping `(0, ∞)` into `(0, 1)`. -/
private def F (a b : ℕ) : ℚ :=
  if h : a = 0 ∨ b = 0 then 0
  else if hlt : a < b then F a (b - a) / 2
  else if hgt : b < a then 1 / 2 + F (a - b) b / 2
  else 1 / 2
termination_by a + b

/-- Odd extension of Minkowski's question mark function to all of `ℚ`. -/
private def f (q : ℚ) : ℚ :=
  if 0 < q then F q.num.natAbs q.den
  else if q < 0 then -F q.num.natAbs q.den
  else 0

private lemma F_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : 0 < F a b := by
  induction hn : a + b using Nat.strong_induction_on generalizing a b with
  | _ n ih =>
    unfold F
    have h0 : ¬(a = 0 ∨ b = 0) := by omega
    rw [dif_neg h0]
    split_ifs with hlt hgt
    · have h1 := ih (a + (b - a)) (by omega) ha (by omega) rfl
      linarith
    · have h1 := ih ((a - b) + b) (by omega) (by omega) hb rfl
      linarith
    · norm_num

private lemma F_lt_one {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : F a b < 1 := by
  induction hn : a + b using Nat.strong_induction_on generalizing a b with
  | _ n ih =>
    unfold F
    have h0 : ¬(a = 0 ∨ b = 0) := by omega
    rw [dif_neg h0]
    split_ifs with hlt hgt
    · have h1 := ih (a + (b - a)) (by omega) ha (by omega) rfl
      linarith
    · have h1 := ih ((a - b) + b) (by omega) (by omega) hb rfl
      linarith
    · norm_num

private lemma F_mul_left {k a b : ℕ} (hk : 0 < k) : F (k * a) (k * b) = F a b := by
  induction hn : a + b using Nat.strong_induction_on generalizing a b with
  | _ n ih =>
    unfold F
    by_cases h0 : a = 0 ∨ b = 0
    · have hk0 : k * a = 0 ∨ k * b = 0 := by
        rcases h0 with rfl | rfl <;> simp
      rw [dif_pos hk0, dif_pos h0]
    · have hk0 : ¬(k * a = 0 ∨ k * b = 0) := by
        push Not at h0 ⊢
        exact ⟨Nat.mul_ne_zero (by omega) h0.1, Nat.mul_ne_zero (by omega) h0.2⟩
      rw [dif_neg hk0, dif_neg h0]
      by_cases hlt : a < b
      · have hklt : k * a < k * b := Nat.mul_lt_mul_of_pos_left hlt hk
        rw [dif_pos hklt, dif_pos hlt, ← Nat.mul_sub_left_distrib]
        rw [ih (a + (b - a)) (by omega) rfl]
      · have hklt : ¬(k * a < k * b) := by
          intro h
          exact hlt (Nat.lt_of_mul_lt_mul_left h)
        rw [dif_neg hklt, dif_neg hlt]
        by_cases hgt : b < a
        · have hkgt : k * b < k * a := Nat.mul_lt_mul_of_pos_left hgt hk
          rw [dif_pos hkgt, dif_pos hgt, ← Nat.mul_sub_left_distrib]
          rw [ih ((a - b) + b) (by omega) rfl]
        · have hkgt : ¬(k * b < k * a) := by
            intro h
            exact hgt (Nat.lt_of_mul_lt_mul_left h)
          rw [dif_neg hkgt, dif_neg hgt]

private lemma F_eq_of_cross {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a * d = c * b) : F a b = F c d := by
  calc F a b = F (d * a) (d * b) := (F_mul_left hd).symm
    _ = F (b * c) (b * d) := by
      congr 1 <;> linarith
    _ = F c d := F_mul_left hb

private lemma F_strictMono {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a * d < c * b) : F a b < F c d := by
  induction hn : a + b + c + d using Nat.strong_induction_on generalizing a b c d with
  | _ n ih =>
    unfold F
    have h01 : ¬(a = 0 ∨ b = 0) := by omega
    have h02 : ¬(c = 0 ∨ d = 0) := by omega
    rw [dif_neg h01, dif_neg h02]
    split_ifs with h1lt h2lt h2gt h1gt h2lt' h2gt' h2lt'' h2gt''
    · have hsub : a * (d - c) < c * (b - a) := by
        zify [le_of_lt h1lt, le_of_lt h2lt]
        have : (a : ℤ) * d < c * b := by exact_mod_cast h
        linarith
      have hrec := ih (a + (b - a) + c + (d - c)) (by omega) ha (by omega) hc (by omega) hsub rfl
      linarith
    · have h1 := F_lt_one ha (by omega : 0 < b - a)
      have h2 := F_pos (by omega : 0 < c - d) hd
      linarith
    · have h1 := F_lt_one ha (by omega : 0 < b - a)
      linarith
    · exfalso
      have : b * c ≤ a * d := by nlinarith
      linarith
    · have hsub : (a - b) * d < (c - d) * b := by
        zify [le_of_lt h1gt, le_of_lt h2gt']
        have : (a : ℤ) * d < c * b := by exact_mod_cast h
        linarith
      have hrec := ih ((a - b) + b + (c - d) + d) (by omega) (by omega) hb (by omega) hd hsub rfl
      linarith
    · exfalso
      have hcd : c = d := by omega
      subst hcd
      nlinarith
    · exfalso
      have hab : a = b := by omega
      subst hab
      nlinarith
    · have h2 := F_pos (by omega : 0 < c - d) hd
      linarith
    · exfalso
      have hab : a = b := by omega
      have hcd : c = d := by omega
      subst hab; subst hcd
      nlinarith

private lemma F_swap {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : F b a = 1 - F a b := by
  induction hn : a + b using Nat.strong_induction_on generalizing a b with
  | _ n ih =>
    unfold F
    have h01 : ¬(b = 0 ∨ a = 0) := by omega
    have h02 : ¬(a = 0 ∨ b = 0) := by omega
    rw [dif_neg h01, dif_neg h02]
    by_cases hlt : a < b
    · have hgt : ¬(b < a) := by omega
      rw [dif_neg hgt, dif_pos hlt, dif_pos hlt]
      have hrec := ih (a + (b - a)) (by omega) ha (by omega) rfl
      linarith
    · by_cases hgt : b < a
      · rw [dif_pos hgt, dif_neg hlt, dif_pos hgt]
        have hrec := ih ((a - b) + b) (by omega) (by omega) hb rfl
        linarith
      · rw [dif_neg hgt, dif_neg hlt, dif_neg hgt, dif_neg hlt]
        norm_num

private lemma F_one_left (n : ℕ) (hn : 0 < n) : F 1 n = 1 / (2 : ℚ) ^ n := by
  induction n with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero =>
      unfold F
      norm_num
    | succ m =>
      unfold F
      have h0 : ¬(1 = 0 ∨ m + 2 = 0) := by omega
      have hlt : 1 < m + 2 := by omega
      rw [dif_neg h0, dif_pos hlt]
      have hsub : m + 2 - 1 = m + 1 := by omega
      rw [hsub, ih (by omega)]
      rw [pow_succ]
      ring

private lemma f_neg (q : ℚ) : f (-q) = -f q := by
  unfold f
  by_cases hpos : 0 < q
  · have h1 : ¬(0 < -q) := by linarith
    have h2 : -q < 0 := by linarith
    rw [if_neg h1, if_pos h2, if_pos hpos]
    simp [Rat.neg_num, Rat.neg_den]
  · by_cases hneg : q < 0
    · have h1 : 0 < -q := by linarith
      rw [if_pos h1, if_neg hpos, if_pos hneg]
      simp [Rat.neg_num, Rat.neg_den]
    · have hq0 : q = 0 := by linarith
      subst hq0
      simp

private lemma f_zero : f 0 = 0 := by
  unfold f
  simp

private lemma f_div_nat {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    f ((a : ℚ) / (b : ℚ)) = F a b := by
  set q : ℚ := (a : ℚ) / (b : ℚ)
  have hq : 0 < q := div_pos (by exact_mod_cast ha) (by exact_mod_cast hb)
  unfold f
  rw [if_pos hq]
  have hnum_pos : 0 < q.num := Rat.num_pos.mpr hq
  have hnum_nat_pos : 0 < q.num.natAbs := by omega
  have hden_pos : 0 < q.den := q.pos
  have hnum_eq : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg (le_of_lt hnum_pos)
  have hq_eq : (q.num.natAbs : ℚ) / (q.den : ℚ) = (a : ℚ) / (b : ℚ) := by
    have h2 := q.num_div_den
    rw [← hnum_eq, Int.cast_natCast] at h2
    exact h2
  have hcross_q : (q.num.natAbs : ℚ) * (b : ℚ) = (a : ℚ) * (q.den : ℚ) := by
    have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
    have hd0 : (q.den : ℚ) ≠ 0 := by exact_mod_cast (by omega : q.den ≠ 0)
    field_simp [hb0, hd0] at hq_eq
    linarith
  have hcross : q.num.natAbs * b = a * q.den := by exact_mod_cast hcross_q
  exact F_eq_of_cross hnum_nat_pos hden_pos ha hb hcross

private lemma f_pos {q : ℚ} (hq : 0 < q) : 0 < f q := by
  unfold f
  rw [if_pos hq]
  have hnum_pos : 0 < q.num := Rat.num_pos.mpr hq
  exact F_pos (by omega) q.pos

private lemma f_strictMono_pos {x y : ℚ} (hx : 0 < x) (hy : 0 < y) (hxy : x < y) : f x < f y := by
  unfold f
  rw [if_pos hx, if_pos hy]
  have hxn : 0 < x.num := Rat.num_pos.mpr hx
  have hyn : 0 < y.num := Rat.num_pos.mpr hy
  have h1 : (x.num.natAbs : ℤ) = x.num := Int.natAbs_of_nonneg (le_of_lt hxn)
  have h2 : (y.num.natAbs : ℤ) = y.num := Int.natAbs_of_nonneg (le_of_lt hyn)
  have hx_eq : (x.num.natAbs : ℚ) / (x.den : ℚ) = x := by
    have h := x.num_div_den; rw [← h1, Int.cast_natCast] at h; exact h
  have hy_eq : (y.num.natAbs : ℚ) / (y.den : ℚ) = y := by
    have h := y.num_div_den; rw [← h2, Int.cast_natCast] at h; exact h
  have hcross_q : (x.num.natAbs : ℚ) * (y.den : ℚ) < (y.num.natAbs : ℚ) * (x.den : ℚ) := by
    rw [← hx_eq, ← hy_eq] at hxy
    have hxden : (0 : ℚ) < x.den := by exact_mod_cast x.pos
    have hyden : (0 : ℚ) < y.den := by exact_mod_cast y.pos
    exact (div_lt_div_iff₀ hxden hyden).mp hxy
  have hcross : x.num.natAbs * y.den < y.num.natAbs * x.den := by exact_mod_cast hcross_q
  exact F_strictMono (by omega) x.pos (by omega) y.pos hcross

private lemma f_strictMono : StrictMono f := by
  intro x y hxy
  by_cases hx : 0 < x
  · exact f_strictMono_pos hx (lt_trans hx hxy) hxy
  · by_cases hy : 0 < y
    · have hfy : 0 < f y := f_pos hy
      by_cases hx0 : x = 0
      · subst hx0; rw [f_zero]; exact hfy
      · have hxneg : x < 0 := lt_of_le_of_ne (not_lt.mp hx) hx0
        have hfx : f x < 0 := by
          have : 0 < f (-x) := f_pos (by linarith)
          rw [f_neg] at this
          linarith
        linarith
    · by_cases hy0 : y = 0
      · subst hy0
        have hfx : f x < 0 := by
          have : 0 < f (-x) := f_pos (by linarith)
          rw [f_neg] at this
          linarith
        rw [f_zero]
        exact hfx
      · have hyneg : y < 0 := lt_of_le_of_ne (not_lt.mp hy) hy0
        have h1 : f (-y) < f (-x) := f_strictMono_pos (by linarith) (by linarith) (by linarith)
        rw [f_neg, f_neg] at h1
        linarith

private lemma rat_eq_natAbs_div_den {q : ℚ} (hq : 0 < q) :
    q = (q.num.natAbs : ℚ) / (q.den : ℚ) := by
  have hnum_pos : 0 < q.num := Rat.num_pos.mpr hq
  have h1 : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg (le_of_lt hnum_pos)
  have h2 := q.num_div_den
  rw [← h1, Int.cast_natCast] at h2
  exact h2.symm

private lemma f_lt_one_eq {q : ℚ} (hq0 : 0 < q) (hq1 : q < 1) :
    f q = f (q / (1 - q)) / 2 := by
  have hnum_pos : 0 < q.num := Rat.num_pos.mpr hq0
  have ha : 0 < q.num.natAbs := by omega
  have hb : 0 < q.den := q.pos
  have hq_eq : q = (q.num.natAbs : ℚ) / (q.den : ℚ) := rat_eq_natAbs_div_den hq0
  have hab : q.num.natAbs < q.den := by
    rw [hq_eq, div_lt_one (by exact_mod_cast hb)] at hq1
    exact_mod_cast hq1
  have hphi : q / (1 - q) = (q.num.natAbs : ℚ) / ((q.den - q.num.natAbs : ℕ) : ℚ) := by
    conv_lhs => rw [hq_eq]
    rw [Nat.cast_sub (le_of_lt hab)]
    have hb0 : (q.den : ℚ) ≠ 0 := by exact_mod_cast (by omega : q.den ≠ 0)
    have hsub0 : (q.den : ℚ) - (q.num.natAbs : ℚ) ≠ 0 := by
      have : (q.num.natAbs : ℚ) < (q.den : ℚ) := by exact_mod_cast hab
      linarith
    field_simp [hb0, hsub0]
  rw [hphi, f_div_nat ha (by omega : 0 < q.den - q.num.natAbs)]
  conv_lhs => rw [hq_eq, f_div_nat ha hb]
  conv_lhs => unfold F
  have h0 : ¬(q.num.natAbs = 0 ∨ q.den = 0) := by omega
  rw [dif_neg h0, dif_pos hab]

private lemma f_gt_one_eq {q : ℚ} (hq1 : 1 < q) :
    f q = 1 / 2 + f (q - 1) / 2 := by
  have hq0 : 0 < q := by linarith
  have hnum_pos : 0 < q.num := Rat.num_pos.mpr hq0
  have ha : 0 < q.num.natAbs := by omega
  have hb : 0 < q.den := q.pos
  have hq_eq : q = (q.num.natAbs : ℚ) / (q.den : ℚ) := rat_eq_natAbs_div_den hq0
  have hba : q.den < q.num.natAbs := by
    rw [hq_eq, one_lt_div (by exact_mod_cast hb)] at hq1
    exact_mod_cast hq1
  have hpsi : q - 1 = ((q.num.natAbs - q.den : ℕ) : ℚ) / (q.den : ℚ) := by
    conv_lhs => rw [hq_eq]
    rw [Nat.cast_sub (le_of_lt hba)]
    have hb0 : (q.den : ℚ) ≠ 0 := by exact_mod_cast (by omega : q.den ≠ 0)
    field_simp [hb0]
  rw [hpsi, f_div_nat (by omega : 0 < q.num.natAbs - q.den) hb]
  conv_lhs => rw [hq_eq, f_div_nat ha hb]
  conv_lhs => unfold F
  have h0 : ¬(q.num.natAbs = 0 ∨ q.den = 0) := by omega
  have hnotlt : ¬(q.num.natAbs < q.den) := by omega
  rw [dif_neg h0, dif_neg hnotlt, dif_pos hba]

private lemma f_inv_eq {q : ℚ} (hq : 0 < q) : f (1 / q) = 1 - f q := by
  have hnum_pos : 0 < q.num := Rat.num_pos.mpr hq
  have ha : 0 < q.num.natAbs := by omega
  have hb : 0 < q.den := q.pos
  have hq_eq : q = (q.num.natAbs : ℚ) / (q.den : ℚ) := rat_eq_natAbs_div_den hq
  have hinv : 1 / q = (q.den : ℚ) / (q.num.natAbs : ℚ) := by
    conv_lhs => rw [hq_eq]
    rw [one_div_div]
  rw [hinv, f_div_nat hb ha]
  conv_rhs => rw [hq_eq, f_div_nat ha hb]
  exact F_swap ha hb

private lemma f_one : f 1 = 1 / 2 := by
  have := f_div_nat (a := 1) (b := 1) (by omega) (by omega)
  simp only [Nat.cast_one, div_one] at this
  rw [this]
  unfold F
  norm_num

private lemma mul_succ_le_two_pow (n : ℕ) : n * (n + 1) ≤ 2 ^ (n + 2) := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    cases k with
    | zero => norm_num
    | succ m =>
      cases m with
      | zero => norm_num
      | succ r =>
        calc (r + 3) * (r + 4) ≤ 2 * ((r + 2) * (r + 3)) := by nlinarith
          _ ≤ 2 * 2 ^ (r + 2 + 2) := Nat.mul_le_mul_left 2 ih
          _ = 2 ^ (r + 3 + 2) := by ring

private lemma rat_norm_eq (x : ℚ) : ‖x‖ = |(x : ℝ)| := by
  rw [← Rat.norm_cast_real, Real.norm_eq_abs]

private lemma hasDerivAt_f_zero : HasDerivAt f 0 0 := by
  rw [hasDerivAt_iff_isLittleO]
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (4 / ε)
  have hN_pos : 0 < N := by
    by_contra h
    have h0 : N = 0 := by omega
    subst h0
    have : (0 : ℝ) < 4 / ε := by positivity
    linarith
  have hδ_pos : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  rw [Metric.eventually_nhds_iff]
  refine ⟨1 / (N : ℝ), hδ_pos, ?_⟩
  intro x hx
  simp only [sub_zero, f_zero, smul_zero, dist_zero_right] at hx ⊢
  by_cases hx0 : x = 0
  · subst hx0; simp [f_zero]
  · set y : ℚ := |x|
    have hy_pos : 0 < y := abs_pos.mpr hx0
    have hnorm_x : ‖x‖ = (y : ℝ) := by
      rw [rat_norm_eq, Rat.cast_abs]
    have hnorm_fx : ‖f x‖ = (f y : ℝ) := by
      have hfx_abs : |f x| = f y := by
        by_cases hpos : 0 < x
        · dsimp only [y]
          rw [abs_of_pos hpos, abs_of_pos (f_pos hpos)]
        · have hneg : x < 0 := lt_of_le_of_ne (not_lt.mp hpos) hx0
          have habs : y = -x := abs_of_neg hneg
          rw [habs, f_neg]
          have : 0 < -f x := by
            have := f_pos (show 0 < -x by linarith)
            rw [f_neg] at this
            exact this
          rw [abs_of_neg (by linarith)]
      rw [rat_norm_eq, ← Rat.cast_abs, hfx_abs]
    rw [hnorm_x, hnorm_fx]
    rw [hnorm_x] at hx
    have hy_lt : y < 1 / (N : ℚ) := by
      have hx' : (y : ℝ) < ((1 / (N : ℚ) : ℚ) : ℝ) := by simpa using hx
      exact Rat.cast_lt.mp hx'
    have hnum_pos : 0 < y.num := Rat.num_pos.mpr hy_pos
    have ha : 0 < y.num.natAbs := by omega
    have hb : 0 < y.den := y.pos
    have hy_eq : y = (y.num.natAbs : ℚ) / (y.den : ℚ) := rat_eq_natAbs_div_den hy_pos
    set n : ℕ := y.den / y.num.natAbs
    have hN_le_n : N ≤ n := by
      have hmul : (y.num.natAbs : ℚ) * (N : ℚ) < (y.den : ℚ) := by
        rw [hy_eq] at hy_lt
        have hb0 : (0 : ℚ) < y.den := by exact_mod_cast hb
        have hN0 : (0 : ℚ) < N := by exact_mod_cast hN_pos
        rw [div_lt_div_iff₀ hb0 hN0] at hy_lt
        linarith
      have hmul_nat : y.num.natAbs * N < y.den := by exact_mod_cast hmul
      exact (Nat.le_div_iff_mul_le ha).mpr (by linarith)
    have hn_pos : 0 < n := lt_of_lt_of_le hN_pos hN_le_n
    have hy_le : y ≤ 1 / (n : ℚ) := by
      have h1 : n * y.num.natAbs ≤ y.den := Nat.div_mul_le_self y.den y.num.natAbs
      rw [hy_eq]
      have hb0 : (0 : ℚ) < y.den := by exact_mod_cast hb
      have hn0 : (0 : ℚ) < n := by exact_mod_cast hn_pos
      rw [div_le_div_iff₀ hb0 hn0]
      exact_mod_cast (by linarith : y.num.natAbs * n ≤ 1 * y.den)
    have hy_gt : 1 / ((n + 1 : ℕ) : ℚ) < y := by
      have h1 : y.den < (n + 1) * y.num.natAbs := by
        have hdiv : y.den < n * y.num.natAbs + y.num.natAbs :=
          Nat.lt_div_mul_add (a := y.den) ha
        linarith
      rw [hy_eq]
      have hb0 : (0 : ℚ) < y.den := by exact_mod_cast hb
      have hn1 : (0 : ℚ) < (n + 1 : ℕ) := by positivity
      rw [div_lt_div_iff₀ hn1 hb0]
      exact_mod_cast (by linarith : 1 * y.den < y.num.natAbs * (n + 1))
    have hfy_le : f y ≤ 1 / (2 : ℚ) ^ n := by
      calc f y ≤ f (1 / (n : ℚ)) := f_strictMono.monotone hy_le
        _ = F 1 n := by
          simpa using f_div_nat (a := 1) (b := n) (by omega) hn_pos
        _ = 1 / (2 : ℚ) ^ n := F_one_left n hn_pos
    have hfy_le_r : (f y : ℝ) ≤ 1 / (2 : ℝ) ^ n := by
      have h := Rat.cast_le (K := ℝ).mpr hfy_le
      simpa using h
    have hy_gt_r : 1 / ((n : ℝ) + 1) < (y : ℝ) := by
      have h := Rat.cast_lt (K := ℝ).mpr hy_gt
      simpa using h
    have hpow_bound : (n : ℝ) * ((n : ℝ) + 1) ≤ 4 * (2 : ℝ) ^ n := by
      have := mul_succ_le_two_pow n
      have h' : ((n * (n + 1) : ℕ) : ℝ) ≤ ((2 ^ (n + 2) : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at h'
      have h2 : (2 : ℝ) ^ (n + 2) = 4 * (2 : ℝ) ^ n := by ring
      linarith
    have hrat_bound : ((n : ℝ) + 1) / (2 : ℝ) ^ n ≤ 4 / (n : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    have h4n_le : 4 / (n : ℝ) ≤ ε := by
      have hN_le_nr : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hN_le_n
      have h4_lt : 4 / (N : ℝ) < ε := by
        rw [div_lt_iff₀ (by exact_mod_cast hN_pos)]
        rw [div_lt_iff₀ hε] at hN
        linarith
      have hmono : 4 / (n : ℝ) ≤ 4 / (N : ℝ) :=
        div_le_div_of_nonneg_left (by norm_num) (by exact_mod_cast hN_pos) hN_le_nr
      linarith
    calc (f y : ℝ) ≤ 1 / (2 : ℝ) ^ n := hfy_le_r
      _ = (((n : ℝ) + 1) / (2 : ℝ) ^ n) * (1 / ((n : ℝ) + 1)) := by
        field_simp
      _ ≤ (4 / (n : ℝ)) * (y : ℝ) := by
        gcongr
      _ ≤ ε * (y : ℝ) := by
        gcongr

private lemma hasDerivAt_f_one : HasDerivAt f 0 1 := by
  rw [hasDerivAt_iff_isLittleO]
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have h0 : HasDerivAt f 0 0 := hasDerivAt_f_zero
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff] at h0
  have hε' : 0 < ε / 2 := by linarith
  have hev := h0 hε'
  rw [Metric.eventually_nhds_iff] at hev ⊢
  obtain ⟨δ₀, hδ₀, hball⟩ := hev
  set δ : ℝ := min (1 / 2) (δ₀ / 2)
  have hδ : 0 < δ := lt_min (by norm_num) (by linarith)
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  simp only [smul_zero, sub_zero]
  have hdist : ‖x - 1‖ < δ := by simpa [dist_eq_norm] using hx
  have hlt_half : ‖x - 1‖ < 1 / 2 := lt_of_lt_of_le hdist (min_le_left _ _)
  have hlt_d0 : ‖x - 1‖ < δ₀ / 2 := lt_of_lt_of_le hdist (min_le_right _ _)
  have hx_gt_half_r : (1 / 2 : ℝ) < (x : ℝ) := by
    have : |(x : ℝ) - 1| < 1 / 2 := by
      simpa [rat_norm_eq, Rat.cast_sub] using hlt_half
    linarith [(abs_lt.mp this).1]
  have hx_gt_half : (1 / 2 : ℚ) < x := by
    have h1 : (((1 / 2 : ℚ) : ℚ) : ℝ) < (x : ℝ) := by simpa using hx_gt_half_r
    exact Rat.cast_lt.mp h1
  rcases lt_trichotomy x 1 with hxlt | rfl | hxgt
  · have hx0 : 0 < x := by linarith
    have hfx : f x - f 1 = -(f ((1 - x) / x) / 2) := by
      have h1 := f_lt_one_eq hx0 hxlt
      have h2 := f_inv_eq (show 0 < x / (1 - x) by exact div_pos hx0 (by linarith))
      rw [one_div_div] at h2
      rw [h1, f_one]
      linarith
    set t : ℚ := (1 - x) / x
    have ht_pos : 0 < t := div_pos (by linarith) hx0
    have hnorm_t : ‖t‖ < δ₀ := by
      have h1 : ‖t‖ = ‖1 - x‖ / ‖x‖ := by
        simp [t, norm_div]
      have h2 : (1 / 2 : ℝ) < ‖x‖ := by
        rw [rat_norm_eq, abs_of_pos (by exact_mod_cast hx0)]
        exact hx_gt_half_r
      have h3 : ‖1 - x‖ = ‖x - 1‖ := norm_sub_rev 1 x
      rw [h1, h3]
      rw [div_lt_iff₀ (by linarith)]
      nlinarith
    have hbt := hball (y := t) (by simpa [dist_zero_right] using hnorm_t)
    simp only [sub_zero, f_zero, smul_zero] at hbt
    rw [hfx, norm_neg, norm_div]
    have h2n : ‖(2 : ℚ)‖ = 2 := by simp [rat_norm_eq]
    rw [h2n]
    have hnorm_t_le : ‖t‖ ≤ 2 * ‖x - 1‖ := by
      have h1 : ‖t‖ = ‖x - 1‖ / ‖x‖ := by
        simp [t, norm_div, norm_sub_rev]
      have h2 : (1 / 2 : ℝ) < ‖x‖ := by
        rw [rat_norm_eq, abs_of_pos (by exact_mod_cast hx0)]
        exact hx_gt_half_r
      rw [h1, div_le_iff₀ (by linarith)]
      nlinarith [norm_nonneg (x - 1)]
    calc ‖f t‖ / 2 ≤ (ε / 2 * ‖t‖) / 2 := by linarith
      _ ≤ (ε / 2 * (2 * ‖x - 1‖)) / 2 := by
        have : 0 ≤ ε / 2 := by linarith
        nlinarith
      _ ≤ ε * ‖x - 1‖ := by
        have : 0 ≤ ‖x - 1‖ := norm_nonneg _
        nlinarith
  · simp
  · have hfx : f x - f 1 = f (x - 1) / 2 := by
      rw [f_gt_one_eq hxgt, f_one]
      ring
    have hbt := hball (y := x - 1) (by
      simpa [dist_zero_right] using (lt_trans hlt_d0 (by linarith : δ₀ / 2 < δ₀)))
    simp only [sub_zero, f_zero, smul_zero] at hbt
    rw [hfx, norm_div]
    have h2n : ‖(2 : ℚ)‖ = 2 := by simp [rat_norm_eq]
    rw [h2n]
    have : 0 ≤ ‖x - 1‖ := norm_nonneg _
    nlinarith

private lemma hasDerivAt_f_pos_nat (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt f 0 ((a : ℚ) / (b : ℚ)) := by
  induction hn : a + b using Nat.strong_induction_on generalizing a b with
  | _ n ih =>
    set q : ℚ := (a : ℚ) / (b : ℚ)
    have hq0 : 0 < q := div_pos (by exact_mod_cast ha) (by exact_mod_cast hb)
    by_cases hlt : a < b
    · have hq1 : q < 1 := by
        rw [div_lt_one (by exact_mod_cast hb)]
        exact_mod_cast hlt
      have hphi_q : q / (1 - q) = (a : ℚ) / ((b - a : ℕ) : ℚ) := by
        rw [Nat.cast_sub (le_of_lt hlt)]
        have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
        have hba0 : (b : ℚ) - (a : ℚ) ≠ 0 := by
          have : (a : ℚ) < (b : ℚ) := by exact_mod_cast hlt
          linarith
        dsimp [q]
        field_simp [hb0, hba0]
      have hih : HasDerivAt f 0 (q / (1 - q)) := by
        rw [hphi_q]
        exact ih (a + (b - a)) (by omega) a (b - a) ha (by omega) rfl
      have hphi_deriv : HasDerivAt (fun x : ℚ => x / (1 - x))
          ((1 * (1 - q) - q * (-1)) / (1 - q) ^ 2) q := by
        have h1 : HasDerivAt (fun x : ℚ => x) 1 q := hasDerivAt_id' q
        have h2 : HasDerivAt (fun x : ℚ => (1 : ℚ) - x) (-1) q :=
          (hasDerivAt_id' q).const_sub (1 : ℚ)
        exact h1.div h2 (by linarith)
      have hcomp : HasDerivAt (fun x : ℚ => f (x / (1 - x)) / 2) 0 q := by
        have h1 := (hih.comp q hphi_deriv).div_const (2 : ℚ)
        simpa using h1
      have hev : (fun x : ℚ => f (x / (1 - x)) / 2) =ᶠ[nhds q] f := by
        have hopen : IsOpen (Set.Ioo (0 : ℚ) 1) := isOpen_Ioo
        have hmem : Set.Ioo (0 : ℚ) 1 ∈ nhds q := hopen.mem_nhds ⟨hq0, hq1⟩
        filter_upwards [hmem] with x hx
        exact (f_lt_one_eq hx.1 hx.2).symm
      exact hcomp.congr_of_eventuallyEq hev.symm
    · by_cases hgt : b < a
      · have hq1 : 1 < q := by
          rw [one_lt_div (by exact_mod_cast hb)]
          exact_mod_cast hgt
        have hpsi_q : q - 1 = ((a - b : ℕ) : ℚ) / (b : ℚ) := by
          rw [Nat.cast_sub (le_of_lt hgt)]
          have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
          dsimp [q]
          field_simp [hb0]
        have hih : HasDerivAt f 0 (q - 1) := by
          rw [hpsi_q]
          exact ih ((a - b) + b) (by omega) (a - b) b (by omega) hb rfl
        have hpsi_deriv : HasDerivAt (fun x : ℚ => x - 1) 1 q :=
          (hasDerivAt_id' q).sub_const (1 : ℚ)
        have hcomp : HasDerivAt (fun x : ℚ => (1 : ℚ) / 2 + f (x - 1) / 2) 0 q := by
          have h1 := ((hih.comp q hpsi_deriv).div_const (2 : ℚ)).const_add ((1 : ℚ) / 2)
          simpa using h1
        have hev : (fun x : ℚ => (1 : ℚ) / 2 + f (x - 1) / 2) =ᶠ[nhds q] f := by
          have hopen : IsOpen (Set.Ioi (1 : ℚ)) := isOpen_Ioi
          have hmem : Set.Ioi (1 : ℚ) ∈ nhds q := hopen.mem_nhds hq1
          filter_upwards [hmem] with x hx
          exact (f_gt_one_eq hx).symm
        exact hcomp.congr_of_eventuallyEq hev.symm
      · have hab : a = b := by omega
        subst hab
        have hq_one : q = 1 := by
          dsimp [q]
          exact div_self (by exact_mod_cast (by omega : a ≠ 0))
        rw [hq_one]
        exact hasDerivAt_f_one

private lemma hasDerivAt_f_pos {q : ℚ} (hq : 0 < q) : HasDerivAt f 0 q := by
  have hnum_pos : 0 < q.num := Rat.num_pos.mpr hq
  have ha : 0 < q.num.natAbs := by omega
  have hb : 0 < q.den := q.pos
  have hq_eq : q = (q.num.natAbs : ℚ) / (q.den : ℚ) := by
    have h1 : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg (le_of_lt hnum_pos)
    have h2 := q.num_div_den
    rw [← h1, Int.cast_natCast] at h2
    exact h2.symm
  rw [hq_eq]
  exact hasDerivAt_f_pos_nat q.num.natAbs q.den ha hb

private lemma hasDerivAt_f (q : ℚ) : HasDerivAt f 0 q := by
  rcases lt_trichotomy q 0 with hneg | rfl | hpos
  · have hpos' : HasDerivAt f 0 (-q) := hasDerivAt_f_pos (by linarith)
    have hcomp : HasDerivAt (fun x : ℚ => -f (-x)) (-(0 * -1)) q :=
      (hpos'.comp q (hasDerivAt_neg q)).neg
    have hfun : (fun x : ℚ => -f (-x)) = f := by
      ext x
      rw [f_neg, neg_neg]
    rw [hfun] at hcomp
    simpa using hcomp
  · exact hasDerivAt_f_zero
  · exact hasDerivAt_f_pos hpos

theorem main_proof : ∃ f : ℚ → ℚ, StrictMono f ∧ ∀ q : ℚ, HasDerivAt f 0 q :=
  ⟨f, f_strictMono, hasDerivAt_f⟩

end MSE1911440Proof

theorem OMA.solution : type_of% @OMA.S_mse_1911440.main :=
  MSE1911440Proof.main_proof
