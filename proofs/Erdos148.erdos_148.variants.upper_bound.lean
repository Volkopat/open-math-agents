import FormalConjectures.ErdosProblems.«148»

/-!
# Upper bound for Erdős Problem 148

We prove `Erdos148.erdos_148.variants.upper_bound`:
there exists `o = o(1)` such that for all sufficiently large `k`,
`F k ≤ c₀ ^ ((1 / 5 + o k) * 2 ^ k)`,
where `F k` is the number of `k`-element sets of positive integers whose reciprocals sum to `1`,
and `c₀ = ⨆ n, (u n)^(1 / 2^n)` for `u 0 = 1`, `u (n + 1) = u n * (u n + 1)`.

The proof is completely elementary and combines four ingredients:
1. Basic growth bounds for `u n` and `c₀`, giving `u n ≤ c₀ ^ (2 ^ n)` and `∏_{j < r} u j ≤ c₀ ^ (2 ^ r)`.
2. Curtiss's theorem (following Soundararajan's short proof via Karamata's inequality for `exp`):
   if positive integers `b_0 ≤ … ≤ b_{r-1}` satisfy `∑ 1 / b_i < 1`, then `∑ 1 / b_i ≤ 1 - 1 / u r`.
   For any `k`-term Egyptian fraction representation of `1` sorted as `a_0 < … < a_{k-1}`,
   this yields `a_j ≤ k * u j` for every `j < k`.
3. The classical divisor bound `d(n) ≤ C * n^(1/100)` and elementary `f_2 → f_3 → f_4`
   counting bounds giving `f_4(m, n) ≤ C₄ * n^(209/100)`.
4. Splitting each `k`-term representation into its first `r = k - 4` denominators and the last `4`
   denominators gives `F k ≤ C₄ * (k^r * c₀^(2^r))^(309/100) ≤ c₀^((1/5) * 2^k)` for all large `k`,
   since `309 / 1600 < 1 / 5`.
-/

namespace Erdos148Upper

open Filter Real Finset Erdos148
open scoped Topology

/- ### Part 1: Sylvester sequence `u` and constant `c₀` -/

private lemma u_pos (n : ℕ) : 0 < u n := by
  induction n with
  | zero => simp [u]
  | succ n ih =>
    simp only [u]
    exact Nat.mul_pos ih (Nat.succ_pos _)

private lemma u_add_one_le (n : ℕ) : u n + 1 ≤ 2 ^ (2 ^ n) := by
  induction n with
  | zero => simp [u]
  | succ n ih =>
    have h1 : u (n + 1) + 1 ≤ (u n + 1) ^ 2 := by
      simp only [u]
      nlinarith
    have h2 : (u n + 1) ^ 2 ≤ (2 ^ (2 ^ n)) ^ 2 := Nat.pow_le_pow_left ih 2
    calc
      u (n + 1) + 1 ≤ (2 ^ (2 ^ n)) ^ 2 := h1.trans h2
      _ = 2 ^ (2 ^ n * 2) := (pow_mul 2 (2 ^ n) 2).symm
      _ = 2 ^ (2 ^ (n + 1)) := by rw [pow_succ]

private lemma u_rpow_le_two (n : ℕ) : (u n : ℝ) ^ ((1 : ℝ) / 2 ^ n) ≤ 2 := by
  have hu : (u n : ℝ) ≤ (2 : ℝ) ^ (2 ^ n : ℕ) := by
    have h := u_add_one_le n
    exact_mod_cast (show u n ≤ 2 ^ (2 ^ n) by omega)
  have h1 : (u n : ℝ) ^ ((1 : ℝ) / 2 ^ n) ≤ ((2 : ℝ) ^ (2 ^ n : ℕ)) ^ ((1 : ℝ) / 2 ^ n) :=
    rpow_le_rpow (Nat.cast_nonneg _) hu (by positivity)
  have h2 : ((2 : ℝ) ^ (2 ^ n : ℕ)) ^ ((1 : ℝ) / 2 ^ n) = (2 : ℝ) := by
    rw [← rpow_natCast, ← rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hne : ((2 ^ n : ℕ) : ℝ) ≠ 0 := by positivity
    rw [show ((2 ^ n : ℕ) : ℝ) * ((1 : ℝ) / (2 : ℝ) ^ n) = 1 by
      push_cast; field_simp]
    exact rpow_one 2
  exact h1.trans_eq h2

private lemma bddAbove_u_rpow :
    BddAbove (Set.range fun n : ℕ => (u n : ℝ) ^ ((1 : ℝ) / 2 ^ n)) := by
  refine ⟨2, ?_⟩
  rintro x ⟨n, rfl⟩
  exact u_rpow_le_two n

private lemma one_lt_c₀ : 1 < c₀ := by
  have h1 : (u 1 : ℝ) ^ ((1 : ℝ) / 2 ^ 1) ≤ c₀ :=
    le_ciSup bddAbove_u_rpow 1
  have h2 : (1 : ℝ) < (u 1 : ℝ) ^ ((1 : ℝ) / 2 ^ 1) := by
    have hu1 : u 1 = 2 := by simp [u]
    rw [hu1]
    exact one_lt_rpow (by norm_num) (by norm_num)
  exact h2.trans_le h1

private lemma u_le_c₀_pow (n : ℕ) : (u n : ℝ) ≤ c₀ ^ (2 ^ n : ℕ) := by
  have hle : (u n : ℝ) ^ ((1 : ℝ) / 2 ^ n) ≤ c₀ :=
    le_ciSup bddAbove_u_rpow n
  have hpow := pow_le_pow_left₀ (rpow_nonneg (Nat.cast_nonneg _) _) hle (2 ^ n)
  have heq : ((u n : ℝ) ^ ((1 : ℝ) / 2 ^ n)) ^ (2 ^ n : ℕ) = (u n : ℝ) := by
    rw [← rpow_natCast, ← rpow_mul (Nat.cast_nonneg _)]
    rw [show ((1 : ℝ) / (2 : ℝ) ^ n) * ((2 ^ n : ℕ) : ℝ) = 1 by
      push_cast; field_simp]
    exact rpow_one _
  exact heq ▸ hpow

private lemma sum_two_pow (r : ℕ) : ∑ j ∈ range r, 2 ^ j + 1 = 2 ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [sum_range_succ, pow_succ]
    omega

private lemma prod_u_le (r : ℕ) : (∏ j ∈ range r, (u j : ℝ)) ≤ c₀ ^ (2 ^ r : ℕ) := by
  have hc1 : (1 : ℝ) ≤ c₀ := one_lt_c₀.le
  calc
    ∏ j ∈ range r, (u j : ℝ) ≤ ∏ j ∈ range r, c₀ ^ (2 ^ j : ℕ) := by
      refine prod_le_prod (fun j _ => Nat.cast_nonneg _) (fun j _ => u_le_c₀_pow j)
    _ = c₀ ^ (∑ j ∈ range r, 2 ^ j) := by rw [prod_pow_eq_pow_sum]
    _ ≤ c₀ ^ (2 ^ r : ℕ) := by
      refine pow_le_pow_right₀ hc1 ?_
      have h := sum_two_pow r
      omega

/- ### Part 2: Soundararajan's proof of Curtiss's theorem via Karamata for `exp` -/

private noncomputable def expSlopeAux (t : ℝ) : ℝ :=
  if t = 0 then 1 else (exp t - 1) / t

private lemma expSlopeAux_pos (t : ℝ) : 0 < expSlopeAux t := by
  unfold expSlopeAux
  split_ifs with ht
  · norm_num
  · rcases lt_or_gt_of_ne ht with h | h
    · exact div_pos_of_neg_of_neg (by linarith [exp_lt_one_iff.mpr h]) h
    · exact div_pos (by linarith [one_lt_exp_iff.mpr h]) h

private lemma expSlopeAux_le_one_of_neg {t : ℝ} (ht : t < 0) : expSlopeAux t ≤ 1 := by
  unfold expSlopeAux
  rw [if_neg ht.ne, div_le_one_of_neg ht]
  linarith [add_one_le_exp t]

private lemma one_le_expSlopeAux_of_pos {t : ℝ} (ht : 0 < t) : 1 ≤ expSlopeAux t := by
  unfold expSlopeAux
  rw [if_neg ht.ne', one_le_div ht]
  linarith [add_one_le_exp t]

private lemma expSlopeAux_mono : Monotone expSlopeAux := by
  intro s t hst
  rcases eq_or_lt_of_le hst with rfl | hlt
  · exact le_rfl
  by_cases hs : s < 0
  · by_cases ht : t < 0
    · unfold expSlopeAux
      rw [if_neg hs.ne, if_neg ht.ne]
      have hconv := convexOn_exp.2 (Set.mem_univ s) (Set.mem_univ (0 : ℝ))
        (div_nonneg_of_nonpos ht.le hs.le)
        (show 0 ≤ 1 - t / s by rw [sub_nonneg, div_le_one_of_neg hs]; exact hlt.le)
        (by ring)
      simp only [smul_eq_mul, mul_zero, add_zero, exp_zero, mul_one] at hconv
      have hts : t / s * s = t := div_mul_cancel₀ t hs.ne
      rw [hts] at hconv
      have hsub : exp t - 1 ≤ (t / s) * (exp s - 1) := by linarith
      have hts_pos : 0 < s * t := mul_pos_of_neg_of_neg hs ht
      have hmul : s * (exp t - 1) ≥ t * (exp s - 1) := by
        have h1 := mul_le_mul_of_nonpos_left hsub hs.le
        have h2 : s * ((t / s) * (exp s - 1)) = t * (exp s - 1) := by field_simp [hs.ne]
        linarith
      have hdiff : (exp t - 1) / t - (exp s - 1) / s = (s * (exp t - 1) - t * (exp s - 1)) / (s * t) := by
        field_simp [hs.ne, ht.ne]
      have hnn : 0 ≤ (exp t - 1) / t - (exp s - 1) / s := by
        rw [hdiff]
        exact div_nonneg (by linarith) hts_pos.le
      linarith
    · push Not at ht
      rcases eq_or_lt_of_le ht with rfl | ht'
      · simp only [expSlopeAux]
        exact expSlopeAux_le_one_of_neg hs
      · exact (expSlopeAux_le_one_of_neg hs).trans (one_le_expSlopeAux_of_pos ht')
  · push Not at hs
    rcases eq_or_lt_of_le hs with rfl | hs'
    · simp only [expSlopeAux]
      exact one_le_expSlopeAux_of_pos hlt
    · have ht' : 0 < t := hs'.trans hlt
      unfold expSlopeAux
      rw [if_neg hs'.ne', if_neg ht'.ne']
      have hconv := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ t)
        (show 0 ≤ 1 - s / t by rw [sub_nonneg, div_le_one ht']; exact hlt.le)
        (div_nonneg hs'.le ht'.le)
        (by ring)
      simp only [smul_eq_mul, mul_zero, zero_add, exp_zero, mul_one] at hconv
      have hst' : s / t * t = s := div_mul_cancel₀ s ht'.ne'
      rw [hst'] at hconv
      have hsub : exp s - 1 ≤ (s / t) * (exp t - 1) := by linarith
      rw [div_le_div_iff₀ hs' ht']
      have hmul := mul_le_mul_of_nonneg_right hsub ht'.le
      have hcancel : (s / t) * (exp t - 1) * t = s * (exp t - 1) := by field_simp
      linarith

private noncomputable def expSlope (a b : ℝ) : ℝ :=
  exp b * expSlopeAux (a - b)

private lemma expSlope_mul_sub (a b : ℝ) : expSlope a b * (a - b) = exp a - exp b := by
  unfold expSlope expSlopeAux
  by_cases hab : a = b
  · subst hab; simp
  · have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
    rw [if_neg hne]
    field_simp
    rw [mul_sub, mul_one, ← exp_add, add_sub_cancel]

private lemma expSlope_symm (a b : ℝ) : expSlope a b = expSlope b a := by
  by_cases hab : a = b
  · subst hab; rfl
  · have h1 := expSlope_mul_sub a b
    have h2 := expSlope_mul_sub b a
    have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
    have h3 : (expSlope a b - expSlope b a) * (a - b) = 0 := by linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hne)

private lemma expSlope_nonneg (a b : ℝ) : 0 ≤ expSlope a b :=
  mul_nonneg (exp_pos b).le (expSlopeAux_pos (a - b)).le

private lemma expSlope_mono {a₁ a₂ b₁ b₂ : ℝ} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    expSlope a₁ b₁ ≤ expSlope a₂ b₂ := by
  have h1 : expSlope a₁ b₁ ≤ expSlope a₂ b₁ := by
    unfold expSlope
    exact mul_le_mul_of_nonneg_left (expSlopeAux_mono (by linarith)) (exp_pos b₁).le
  have h2 : expSlope a₂ b₁ ≤ expSlope a₂ b₂ := by
    rw [expSlope_symm a₂ b₁, expSlope_symm a₂ b₂]
    unfold expSlope
    exact mul_le_mul_of_nonneg_left (expSlopeAux_mono (by linarith)) (exp_pos a₂).le
  exact h1.trans h2

private lemma abel_nonneg : ∀ (n : ℕ) (c d : ℕ → ℝ),
    (∀ i < n, 0 ≤ c i) →
    (∀ i, i + 1 < n → c (i + 1) ≤ c i) →
    (∀ j < n, 0 ≤ ∑ i ∈ range (j + 1), d i) →
    0 ≤ ∑ i ∈ range n, c i * d i
  | 0, _, _, _, _, _ => by simp
  | n + 1, c, d, hc, hanti, hS => by
    let S : ℕ → ℝ := fun j => ∑ i ∈ range j, d i
    have hsum : ∑ i ∈ range (n + 1), c i * d i =
        c n * S (n + 1) + ∑ j ∈ range n, (c j - c (j + 1)) * S (j + 1) := by
      clear hc hanti hS
      induction n with
      | zero => simp [S]
      | succ m ih =>
        rw [sum_range_succ, ih, sum_range_succ]
        have hSm : S (m + 2) = S (m + 1) + d (m + 1) := sum_range_succ d (m + 1)
        rw [hSm]
        ring
    rw [hsum]
    have h1 : 0 ≤ c n * S (n + 1) :=
      mul_nonneg (hc n (Nat.lt_succ_self n)) (hS n (Nat.lt_succ_self n))
    have h2 : 0 ≤ ∑ j ∈ range n, (c j - c (j + 1)) * S (j + 1) := by
      refine sum_nonneg fun j hj => ?_
      have hj' : j < n := mem_range.mp hj
      exact mul_nonneg (sub_nonneg.mpr (hanti j (by omega))) (hS j (by omega))
    linarith

private lemma karamata_exp (n : ℕ) (α β : ℕ → ℝ)
    (hα : ∀ i, i + 1 < n → α (i + 1) ≤ α i)
    (hβ : ∀ i, i + 1 < n → β (i + 1) ≤ β i)
    (hpart : ∀ j < n, ∑ i ∈ range (j + 1), β i ≤ ∑ i ∈ range (j + 1), α i) :
    ∑ i ∈ range n, exp (β i) ≤ ∑ i ∈ range n, exp (α i) := by
  have hdiff : ∑ i ∈ range n, (exp (α i) - exp (β i)) =
      ∑ i ∈ range n, expSlope (α i) (β i) * (α i - β i) := by
    refine sum_congr rfl fun i _ => (expSlope_mul_sub (α i) (β i)).symm
  have hnn : 0 ≤ ∑ i ∈ range n, expSlope (α i) (β i) * (α i - β i) := by
    refine abel_nonneg n (fun i => expSlope (α i) (β i)) (fun i => α i - β i)
      (fun i _ => expSlope_nonneg _ _)
      (fun i hi => expSlope_mono (hα i hi) (hβ i hi))
      (fun j hj => ?_)
    rw [sum_sub_distrib]
    linarith [hpart j hj]
  rw [← hdiff, sum_sub_distrib] at hnn
  linarith

private lemma sum_le_of_partial_prod_le (n : ℕ) (x y : ℕ → ℝ)
    (hxpos : ∀ i < n, 0 < x i) (hypos : ∀ i < n, 0 < y i)
    (hx : ∀ i, i + 1 < n → x (i + 1) ≤ x i)
    (hy : ∀ i, i + 1 < n → y (i + 1) ≤ y i)
    (hprod : ∀ j < n, ∏ i ∈ range (j + 1), y i ≤ ∏ i ∈ range (j + 1), x i) :
    ∑ i ∈ range n, y i ≤ ∑ i ∈ range n, x i := by
  have hK := karamata_exp n (fun i => log (x i)) (fun i => log (y i))
    (fun i hi => log_le_log (hxpos (i + 1) hi) (hx i hi))
    (fun i hi => log_le_log (hypos (i + 1) hi) (hy i hi))
    (fun j hj => by
      have hlogx : ∑ i ∈ range (j + 1), log (x i) = log (∏ i ∈ range (j + 1), x i) :=
        (log_prod fun i hi => (hxpos i (by have := mem_range.mp hi; omega)).ne').symm
      have hlogy : ∑ i ∈ range (j + 1), log (y i) = log (∏ i ∈ range (j + 1), y i) :=
        (log_prod fun i hi => (hypos i (by have := mem_range.mp hi; omega)).ne').symm
      rw [hlogx, hlogy]
      exact log_le_log (prod_pos fun i hi => hypos i (by have := mem_range.mp hi; omega))
        (hprod j hj))
  have h1 : ∑ i ∈ range n, exp (log (y i)) = ∑ i ∈ range n, y i :=
    sum_congr rfl fun i hi => exp_log (hypos i (mem_range.mp hi))
  have h2 : ∑ i ∈ range n, exp (log (x i)) = ∑ i ∈ range n, x i :=
    sum_congr rfl fun i hi => exp_log (hxpos i (mem_range.mp hi))
  linarith

private def syl (n : ℕ) : ℕ := u n + 1

private lemma syl_pos (n : ℕ) : 0 < syl n := Nat.succ_pos _

private lemma syl_mono : Monotone syl := by
  refine monotone_nat_of_le_succ fun n => ?_
  simp only [syl, u]
  have hu := u_pos n
  nlinarith

private lemma prod_syl_eq_u (k : ℕ) : ∏ i ∈ range k, syl i = u k := by
  induction k with
  | zero => simp [u]
  | succ k ih =>
    rw [prod_range_succ, ih]
    rfl

private lemma sum_inv_syl (k : ℕ) :
    ∑ i ∈ range k, (1 : ℚ) / syl i = 1 - 1 / u k := by
  induction k with
  | zero => simp [u]
  | succ k ih =>
    rw [sum_range_succ, ih]
    have hu : (u k : ℚ) ≠ 0 := by exact_mod_cast (u_pos k).ne'
    have hs : (syl k : ℚ) ≠ 0 := by exact_mod_cast (syl_pos k).ne'
    have hu1 : (u (k + 1) : ℚ) = (u k : ℚ) * (syl k : ℚ) := by
      simp only [u, syl]; push_cast; ring
    have hs1 : (syl k : ℚ) = (u k : ℚ) + 1 := by simp [syl]
    rw [hu1]
    field_simp
    linarith

private lemma sum_inv_le_one_sub_inv_prod (k : ℕ) (b : ℕ → ℕ)
    (hb : ∀ i < k, 0 < b i) (hlt : ∑ i ∈ range k, (1 : ℚ) / b i < 1) :
    ∑ i ∈ range k, (1 : ℚ) / b i ≤ 1 - 1 / (∏ i ∈ range k, b i : ℕ) := by
  let P : ℕ := ∏ i ∈ range k, b i
  have hPpos : 0 < P := prod_pos fun i hi => hb i (mem_range.mp hi)
  have hPne : (P : ℚ) ≠ 0 := by exact_mod_cast hPpos.ne'
  have hM : ∃ M : ℕ, (∑ i ∈ range k, (1 : ℚ) / b i) * P = M := by
    refine ⟨∑ i ∈ range k, P / b i, ?_⟩
    rw [sum_mul, Nat.cast_sum]
    refine sum_congr rfl fun i hi => ?_
    have hdvd : b i ∣ P := dvd_prod_of_mem b hi
    have hbi : (b i : ℚ) ≠ 0 := by exact_mod_cast (hb i (mem_range.mp hi)).ne'
    rw [Nat.cast_div hdvd hbi]
    ring
  obtain ⟨M, hM⟩ := hM
  have hMlt : (M : ℚ) < (P : ℚ) := by
    rw [← hM]
    have hPposQ : (0 : ℚ) < P := by exact_mod_cast hPpos
    nlinarith
  have hMle : M + 1 ≤ P := by
    have : M < P := by exact_mod_cast hMlt
    omega
  have hMQ : (M : ℚ) ≤ (P : ℚ) - 1 := by
    have : (M : ℚ) + 1 ≤ (P : ℚ) := by exact_mod_cast hMle
    linarith
  have hdiv : ∑ i ∈ range k, (1 : ℚ) / b i = (M : ℚ) / P := by
    rw [eq_div_iff hPne, hM]
  rw [hdiv]
  calc
    (M : ℚ) / P ≤ ((P : ℚ) - 1) / P := div_le_div_of_nonneg_right hMQ (by positivity)
    _ = 1 - 1 / P := by field_simp

private lemma curtiss_bound : ∀ (r : ℕ) (b : ℕ → ℕ),
    (∀ i < r, 0 < b i) →
    (∀ i, i + 1 < r → b i ≤ b (i + 1)) →
    ∑ i ∈ range r, (1 : ℚ) / b i < 1 →
    ∑ i ∈ range r, (1 : ℚ) / b i ≤ 1 - 1 / u r := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro b hbpos hbmono hlt
    rcases eq_or_ne r 0 with rfl | hr0
    · simp [u]
    by_cases hprod : ∏ i ∈ range r, b i < ∏ i ∈ range r, syl i
    · have h1 := sum_inv_le_one_sub_inv_prod r b hbpos hlt
      have hPpos : (0 : ℚ) < (∏ i ∈ range r, b i : ℕ) := by
        exact_mod_cast (prod_pos fun i hi => hbpos i (mem_range.mp hi))
      have h2 : (1 : ℚ) / (u r : ℕ) ≤ 1 / (∏ i ∈ range r, b i : ℕ) := by
        rw [← prod_syl_eq_u r]
        exact one_div_le_one_div_of_le hPpos (by exact_mod_cast hprod.le)
      linarith
    · push Not at hprod
      let S := (range r).filter fun l => ∏ i ∈ Ico l r, syl i ≤ ∏ i ∈ Ico l r, b i
      have h0mem : 0 ∈ S := by
        simp only [S, mem_filter, mem_range, Nat.pos_of_ne_zero hr0, true_and]
        simpa [Nat.Ico_zero_eq_range] using hprod
      let l := S.max' ⟨0, h0mem⟩
      have hlmem : l ∈ S := max'_mem S ⟨0, h0mem⟩
      have hlr : l < r := mem_range.mp (mem_filter.mp hlmem).1
      have hlprod : ∏ i ∈ Ico l r, syl i ≤ ∏ i ∈ Ico l r, b i := (mem_filter.mp hlmem).2
      have htail_lt : ∀ m, l < m → m < r → ∏ i ∈ Ico m r, b i < ∏ i ∈ Ico m r, syl i := by
        intro m hlm hmr
        by_contra hge
        push Not at hge
        have hmS : m ∈ S := mem_filter.mpr ⟨mem_range.mpr hmr, hge⟩
        have hle := le_max' S m hmS
        omega
      have hprefix_prod : ∀ j < r - l,
          ∏ i ∈ range (j + 1), (1 / (b (l + i) : ℝ)) ≤
          ∏ i ∈ range (j + 1), (1 / (syl (l + i) : ℝ)) := by
        intro j hj
        have hnat : ∏ i ∈ Ico l (l + j + 1), syl i ≤ ∏ i ∈ Ico l (l + j + 1), b i := by
          by_cases hlast : l + j + 1 = r
          · rw [hlast]; exact hlprod
          · have hltm : l + j + 1 < r := by omega
            have hrem := htail_lt (l + j + 1) (by omega) hltm
            have hsplit_b : ∏ i ∈ Ico l r, b i =
                (∏ i ∈ Ico l (l + j + 1), b i) * (∏ i ∈ Ico (l + j + 1) r, b i) := by
              exact (prod_Ico_consecutive b (show l ≤ l + j + 1 by omega)
                (show l + j + 1 ≤ r by omega)).symm
            have hsplit_s : ∏ i ∈ Ico l r, syl i =
                (∏ i ∈ Ico l (l + j + 1), syl i) * (∏ i ∈ Ico (l + j + 1) r, syl i) := by
              exact (prod_Ico_consecutive syl (show l ≤ l + j + 1 by omega)
                (show l + j + 1 ≤ r by omega)).symm
            rw [hsplit_b, hsplit_s] at hlprod
            by_contra hnot
            push Not at hnot
            have hpos1 : 0 < ∏ i ∈ Ico l (l + j + 1), syl i :=
              prod_pos fun i _ => syl_pos i
            have hpos2 : 0 < ∏ i ∈ Ico (l + j + 1) r, b i :=
              prod_pos fun i hi => hbpos i (mem_Ico.mp hi).2
            nlinarith
        have hshift_b : ∏ i ∈ range (j + 1), b (l + i) = ∏ i ∈ Ico l (l + j + 1), b i := by
          rw [prod_Ico_eq_prod_range]
          simp [show l + j + 1 - l = j + 1 by omega]
        have hshift_s : ∏ i ∈ range (j + 1), syl (l + i) = ∏ i ∈ Ico l (l + j + 1), syl i := by
          rw [prod_Ico_eq_prod_range]
          simp [show l + j + 1 - l = j + 1 by omega]
        have hnat' : (∏ i ∈ range (j + 1), (syl (l + i) : ℝ)) ≤
            ∏ i ∈ range (j + 1), (b (l + i) : ℝ) := by
          rw [← Nat.cast_prod, ← Nat.cast_prod, hshift_b, hshift_s]
          exact_mod_cast hnat
        have hpos_s : 0 < ∏ i ∈ range (j + 1), (syl (l + i) : ℝ) :=
          prod_pos fun i _ => by exact_mod_cast syl_pos (l + i)
        simp only [one_div, prod_inv_distrib]
        exact inv_anti₀ hpos_s hnat'
      have htail_sumR :
          ∑ i ∈ range (r - l), (1 / (b (l + i) : ℝ)) ≤
          ∑ i ∈ range (r - l), (1 / (syl (l + i) : ℝ)) := by
        refine sum_le_of_partial_prod_le (r - l)
          (fun i => 1 / (syl (l + i) : ℝ)) (fun i => 1 / (b (l + i) : ℝ))
          (fun i _ => by
            have : (0 : ℝ) < syl (l + i) := by exact_mod_cast syl_pos (l + i)
            positivity)
          (fun i hi => by
            have : 0 < b (l + i) := hbpos (l + i) (by omega)
            positivity)
          (fun i hi => one_div_le_one_div_of_le (by exact_mod_cast syl_pos (l + i))
            (by exact_mod_cast syl_mono (show l + i ≤ l + (i + 1) by omega)))
          (fun i hi => one_div_le_one_div_of_le (by exact_mod_cast hbpos (l + i) (by omega))
            (by
              have : b (l + i) ≤ b (l + i + 1) := hbmono (l + i) (by omega)
              exact_mod_cast this))
          hprefix_prod
      have htail_sumQ :
          ∑ i ∈ Ico l r, (1 : ℚ) / b i ≤ ∑ i ∈ Ico l r, (1 : ℚ) / syl i := by
        have h1 : (∑ i ∈ Ico l r, (1 : ℚ) / b i : ℝ) = ∑ i ∈ range (r - l), (1 / (b (l + i) : ℝ)) := by
          rw [sum_Ico_eq_sum_range]
          push_cast
          rfl
        have h2 : (∑ i ∈ Ico l r, (1 : ℚ) / syl i : ℝ) = ∑ i ∈ range (r - l), (1 / (syl (l + i) : ℝ)) := by
          rw [sum_Ico_eq_sum_range]
          push_cast
          rfl
        exact_mod_cast (h1.trans_le (htail_sumR.trans_eq h2.symm))
      have hpref_lt : ∑ i ∈ range l, (1 : ℚ) / b i < 1 := by
        have hle : ∑ i ∈ range l, (1 : ℚ) / b i ≤ ∑ i ∈ range r, (1 : ℚ) / b i :=
          sum_le_sum_of_subset_of_nonneg (range_mono hlr.le) fun i _ _ => by positivity
        exact hle.trans_lt hlt
      have hpref_sumQ : ∑ i ∈ range l, (1 : ℚ) / b i ≤ ∑ i ∈ range l, (1 : ℚ) / syl i := by
        rw [sum_inv_syl l]
        exact ih l hlr b (fun i hi => hbpos i (hi.trans hlr))
          (fun i hi => hbmono i (hi.trans hlr)) hpref_lt
      have hsplit_b : ∑ i ∈ range r, (1 : ℚ) / b i =
          (∑ i ∈ range l, (1 : ℚ) / b i) + ∑ i ∈ Ico l r, (1 : ℚ) / b i := by
        rw [← sum_range_add_sum_Ico _ hlr.le]
      have hsplit_s : ∑ i ∈ range r, (1 : ℚ) / syl i =
          (∑ i ∈ range l, (1 : ℚ) / syl i) + ∑ i ∈ Ico l r, (1 : ℚ) / syl i := by
        rw [← sum_range_add_sum_Ico _ hlr.le]
      rw [← sum_inv_syl r, hsplit_b, hsplit_s]
      linarith

/- ### Part 3: Classical divisor bound `d(n) ≤ C * n^(1/100)` -/

private lemma card_divisors_mul_le (a b : ℕ) :
    (a * b).divisors.card ≤ a.divisors.card * b.divisors.card := by
  by_cases ha : a = 0
  · subst ha; simp
  by_cases hb : b = 0
  · subst hb; simp
  have hsub : (a * b).divisors ⊆ (a.divisors ×ˢ b.divisors).image (fun p => p.1 * p.2) := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    let g := Nat.gcd d a
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_right d (Nat.pos_of_ne_zero ha)
    have hgd : g ∣ d := Nat.gcd_dvd_left d a
    have hga : g ∣ a := Nat.gcd_dvd_right d a
    have hcop : Nat.Coprime (d / g) (a / g) := Nat.coprime_div_gcd_div_gcd hgpos
    have hdvd_mul : (d / g) ∣ (a / g) * b := by
      have hmul : g * (d / g) ∣ g * ((a / g) * b) := by
        rw [Nat.mul_div_cancel' hgd, ← mul_assoc, Nat.mul_div_cancel' hga]
        exact hd.1
      exact (Nat.mul_dvd_mul_iff_left hgpos).mp hmul
    have hdb : (d / g) ∣ b := hcop.dvd_of_dvd_mul_left hdvd_mul
    refine mem_image.mpr ⟨(g, d / g), mem_product.mpr
      ⟨Nat.mem_divisors.mpr ⟨hga, ha⟩, Nat.mem_divisors.mpr ⟨hdb, hb⟩⟩, ?_⟩
    exact Nat.mul_div_cancel' hgd
  exact (card_le_card hsub).trans (card_image_le.trans (by rw [card_product]))

private lemma card_divisors_le_prod (n : ℕ) (hn : n ≠ 0) :
    n.divisors.card ≤ ∏ p ∈ n.primeFactors, (n.factorization p + 1) := by
  have hfac : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n :=
    (Nat.prod_primeFactors_pow_factorization hn).symm
  have hsubmul : ∀ (s : Finset ℕ) (f : ℕ → ℕ),
      (∏ p ∈ s, f p).divisors.card ≤ ∏ p ∈ s, (f p).divisors.card := by
    intro s f
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert x s hx ih =>
      rw [prod_insert hx, prod_insert hx]
      exact (card_divisors_mul_le _ _).trans (Nat.mul_le_mul_left _ ih)
  calc
    n.divisors.card = (∏ p ∈ n.primeFactors, p ^ n.factorization p).divisors.card := by rw [hfac]
    _ ≤ ∏ p ∈ n.primeFactors, (p ^ n.factorization p).divisors.card := hsubmul _ _
    _ = ∏ p ∈ n.primeFactors, (n.factorization p + 1) := by
      refine prod_congr rfl fun p hp => ?_
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      rw [Nat.divisors_prime_pow hpp, card_map, card_range]

private lemma half_le_log_two : (1 / 2 : ℝ) ≤ log 2 := by
  rw [le_log_iff_exp_le (by norm_num : (0 : ℝ) < 2)]
  have hsq : exp (1 / 2 : ℝ) ^ 2 = exp 1 := by
    rw [← exp_nat_mul]; norm_num
  have h1 : exp 1 < 4 := lt_trans exp_one_lt_d9 (by norm_num)
  nlinarith [exp_pos (1 / 2 : ℝ)]

private lemma divisor_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ (1 / 100 : ℝ) := by
  let B : ℕ := 2 ^ 100
  refine ⟨(200 : ℝ) ^ B, by positivity, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := hn.ne'
  have hcard : (n.divisors.card : ℝ) ≤ ∏ p ∈ n.primeFactors, ((n.factorization p + 1 : ℕ) : ℝ) := by
    exact_mod_cast card_divisors_le_prod n hn0
  have hnprod : (n : ℝ) ^ (1 / 100 : ℝ) =
      ∏ p ∈ n.primeFactors, ((p : ℝ) ^ (n.factorization p : ℕ)) ^ (1 / 100 : ℝ) := by
    have hfac : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ (n.factorization p : ℕ) := by
      exact_mod_cast Nat.prod_primeFactors_pow_factorization hn0
    rw [hfac, Real.finsetProd_rpow _ _ (fun p _ => by positivity)]
  have hpos_fac : ∀ p ∈ n.primeFactors, 0 < ((p : ℝ) ^ (n.factorization p : ℕ)) ^ (1 / 100 : ℝ) :=
    fun p hp => rpow_pos_of_pos (pow_pos (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos) _) _
  have hratio : (n.divisors.card : ℝ) / (n : ℝ) ^ (1 / 100 : ℝ) ≤ (200 : ℝ) ^ B := by
    calc
      (n.divisors.card : ℝ) / (n : ℝ) ^ (1 / 100 : ℝ)
          ≤ (∏ p ∈ n.primeFactors, ((n.factorization p + 1 : ℕ) : ℝ)) /
              (∏ p ∈ n.primeFactors, ((p : ℝ) ^ (n.factorization p : ℕ)) ^ (1 / 100 : ℝ)) := by
            rw [hnprod]
            exact div_le_div_of_nonneg_right hcard (prod_nonneg fun p hp => (hpos_fac p hp).le)
      _ = ∏ p ∈ n.primeFactors,
            (((n.factorization p + 1 : ℕ) : ℝ) / ((p : ℝ) ^ (n.factorization p : ℕ)) ^ (1 / 100 : ℝ)) := by
            rw [prod_div_distrib]
      _ ≤ ∏ p ∈ n.primeFactors, (if p < B then (200 : ℝ) else 1) := by
            refine prod_le_prod (fun p hp => div_nonneg (Nat.cast_nonneg _) (hpos_fac p hp).le) ?_
            intro p hp
            have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
            let e := n.factorization p
            split_ifs with hlt
            · rw [div_le_iff₀ (hpos_fac p hp)]
              have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
              have hpow1 : (2 : ℝ) ^ ((e : ℝ) / 100) ≤ ((p : ℝ) ^ e) ^ (1 / 100 : ℝ) := by
                rw [← rpow_natCast, ← rpow_mul (by positivity)]
                have heq : (e : ℝ) * (1 / 100 : ℝ) = (e : ℝ) / 100 := by ring
                rw [heq]
                exact rpow_le_rpow (by norm_num) hp2 (by positivity)
              have hexp : 1 + (e : ℝ) / 200 ≤ (2 : ℝ) ^ ((e : ℝ) / 100) := by
                rw [rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
                have h1 := add_one_le_exp (log 2 * ((e : ℝ) / 100))
                have h2 : (e : ℝ) / 200 ≤ log 2 * ((e : ℝ) / 100) := by
                  nlinarith [half_le_log_two, Nat.cast_nonneg (α := ℝ) e]
                linarith
              push_cast
              nlinarith
            · push Not at hlt
              rw [div_le_one (hpos_fac p hp)]
              have hB : (2 : ℝ) ^ (100 : ℕ) ≤ p := by exact_mod_cast hlt
              have hpow1 : (2 : ℝ) ^ e ≤ ((p : ℝ) ^ e) ^ (1 / 100 : ℝ) := by
                rw [← rpow_natCast (p : ℝ), ← rpow_mul (by positivity)]
                have h2 : ((2 : ℝ) ^ (100 : ℕ)) ^ ((e : ℝ) * (1 / 100 : ℝ)) ≤
                    (p : ℝ) ^ ((e : ℝ) * (1 / 100 : ℝ)) :=
                  rpow_le_rpow (by positivity) hB (by positivity)
                have heq : ((2 : ℝ) ^ (100 : ℕ)) ^ ((e : ℝ) * (1 / 100 : ℝ)) = (2 : ℝ) ^ e := by
                  rw [← rpow_natCast (2 : ℝ) 100, ← rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
                  have hmul : ((100 : ℕ) : ℝ) * ((e : ℝ) * (1 / 100 : ℝ)) = (e : ℝ) := by
                    push_cast; ring
                  rw [hmul, rpow_natCast]
                exact heq ▸ h2
              have hle : (e + 1 : ℕ) ≤ 2 ^ e := Nat.lt_two_pow_self
              have hleR : ((e + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ e := by exact_mod_cast hle
              exact hleR.trans hpow1
      _ = ∏ p ∈ n.primeFactors.filter (· < B), (200 : ℝ) := by
            rw [prod_ite, prod_const_one, mul_one]
      _ = (200 : ℝ) ^ (n.primeFactors.filter (· < B)).card := by rw [prod_const]
      _ ≤ (200 : ℝ) ^ B := by
            refine pow_le_pow_right₀ (by norm_num) ?_
            have hsub : n.primeFactors.filter (· < B) ⊆ range B := by
              intro p hp; exact mem_range.mpr (mem_filter.mp hp).2
            exact (card_le_card hsub).trans_eq (card_range B)
  exact (div_le_iff₀ (rpow_pos_of_pos (by exact_mod_cast hn) _)).mp hratio

/- ### Part 4: Elementary `f_2 → f_3 → f_4` counting bounds -/

private lemma ncard_biUnion_finset_le {α β : Type*} [DecidableEq α]
    (s : Finset α) (f : α → Set β) :
    (⋃ a ∈ (s : Set α), f a).ncard ≤ ∑ a ∈ s, (f a).ncard := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
    rw [Finset.coe_insert, Set.biUnion_insert, sum_insert hx]
    exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left ih _)

private def sol2 (m n : ℕ) : Set (ℕ × ℕ) :=
  {t | 0 < t.1 ∧ t.1 ≤ t.2 ∧ (1 : ℚ) / t.1 + 1 / t.2 = (m : ℚ) / n}

private def sol3 (m n : ℕ) : Set (ℕ × ℕ × ℕ) :=
  {t | 0 < t.1 ∧ t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧
    (1 : ℚ) / t.1 + 1 / t.2.1 + 1 / t.2.2 = (m : ℚ) / n}

private def sol4 (m n : ℕ) : Set (ℕ × ℕ × ℕ × ℕ) :=
  {t | 0 < t.1 ∧ t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2.1 ∧ t.2.2.1 ≤ t.2.2.2 ∧
    (1 : ℚ) / t.1 + 1 / t.2.1 + 1 / t.2.2.1 + 1 / t.2.2.2 = (m : ℚ) / n}

private lemma sol2_finite_and_ncard_le (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (sol2 m n).Finite ∧ (sol2 m n).ncard ≤ (n ^ 2).divisors.card := by
  let f : ℕ × ℕ → ℕ := fun t => m * t.1 - n
  have hmaps : Set.MapsTo f (sol2 m n) ((n ^ 2).divisors : Set ℕ) := by
    rintro ⟨a, b⟩ ⟨ha, hab, heq⟩
    have hb : 0 < b := lt_of_lt_of_le ha hab
    have hma_gt : n < m * a := by
      have h1 : (1 : ℚ) / a < (m : ℚ) / n := by
        have hpos : (0 : ℚ) < 1 / b := by positivity
        linarith
      rw [div_lt_div_iff₀ (by exact_mod_cast ha) (by exact_mod_cast hn)] at h1
      exact_mod_cast (by linarith : (n : ℚ) < m * a)
    have hmb_gt : n < m * b := lt_of_lt_of_le hma_gt (Nat.mul_le_mul_left m hab)
    have hmulQ : ((m * a : ℚ) - n) * ((m * b : ℚ) - n) = (n : ℚ) ^ 2 := by
      have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
      have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
      have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
      have hclear : ((b : ℚ) + a) * n = m * a * b := by
        have := congrArg (fun x : ℚ => x * (a * b * n)) heq
        field_simp at this
        linarith
      nlinarith
    have hmulN : (m * a - n) * (m * b - n) = n ^ 2 := by
      have h1 : ((m * a - n : ℕ) : ℚ) = (m * a : ℚ) - n := by
        rw [Nat.cast_sub hma_gt.le]; push_cast; rfl
      have h2 : ((m * b - n : ℕ) : ℚ) = (m * b : ℚ) - n := by
        rw [Nat.cast_sub hmb_gt.le]; push_cast; rfl
      exact_mod_cast (show ((m * a - n : ℕ) : ℚ) * ((m * b - n : ℕ) : ℚ) = (n ^ 2 : ℕ) by
        rw [h1, h2, Nat.cast_pow]; exact hmulQ)
    exact Finset.mem_coe.mpr (Nat.mem_divisors.mpr ⟨⟨m * b - n, hmulN.symm⟩, pow_ne_zero 2 hn.ne'⟩)
  have hinj : Set.InjOn f (sol2 m n) := by
    rintro ⟨a₁, b₁⟩ ⟨ha₁, hab₁, heq₁⟩ ⟨a₂, b₂⟩ ⟨ha₂, hab₂, heq₂⟩ hfeq
    have hb₁ : 0 < b₁ := lt_of_lt_of_le ha₁ hab₁
    have hb₂ : 0 < b₂ := lt_of_lt_of_le ha₂ hab₂
    have hma₁ : n < m * a₁ := by
      have h1 : (1 : ℚ) / a₁ < (m : ℚ) / n := by linarith [show (0 : ℚ) < 1 / b₁ by positivity]
      rw [div_lt_div_iff₀ (by exact_mod_cast ha₁) (by exact_mod_cast hn)] at h1
      exact_mod_cast (by linarith : (n : ℚ) < m * a₁)
    have hma₂ : n < m * a₂ := by
      have h1 : (1 : ℚ) / a₂ < (m : ℚ) / n := by linarith [show (0 : ℚ) < 1 / b₂ by positivity]
      rw [div_lt_div_iff₀ (by exact_mod_cast ha₂) (by exact_mod_cast hn)] at h1
      exact_mod_cast (by linarith : (n : ℚ) < m * a₂)
    have haeq : a₁ = a₂ := by
      have hmeq : m * a₁ = m * a₂ := by
        dsimp only [f] at hfeq
        omega
      exact Nat.eq_of_mul_eq_mul_left hm hmeq
    subst haeq
    have hbeq : (1 : ℚ) / b₁ = 1 / b₂ := by linarith
    have hbQ : (b₁ : ℚ) = (b₂ : ℚ) := by
      simpa using congrArg Inv.inv hbeq
    have hbN : b₁ = b₂ := by exact_mod_cast hbQ
    subst hbN
    rfl
  have hfin : (sol2 m n).Finite :=
    Set.Finite.of_finite_image ((Finset.finite_toSet _).subset hmaps.image_subset) hinj
  have hcard : (sol2 m n).ncard ≤ ((n ^ 2).divisors : Set ℕ).ncard :=
    Set.ncard_le_ncard_of_injOn f hmaps hinj (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at hcard
  exact ⟨hfin, hcard⟩

private lemma sol2_bound :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ m n : ℕ, 0 < m → 0 < n →
      (sol2 m n).Finite ∧ ((sol2 m n).ncard : ℝ) ≤ C₂ * (n : ℝ) ^ (2 / 100 : ℝ) := by
  obtain ⟨C, hC, hdiv⟩ := divisor_bound
  refine ⟨C, hC, fun m n hm hn => ?_⟩
  obtain ⟨hfin, hcard⟩ := sol2_finite_and_ncard_le m n hm hn
  refine ⟨hfin, ?_⟩
  have h1 : ((sol2 m n).ncard : ℝ) ≤ ((n ^ 2).divisors.card : ℝ) := by exact_mod_cast hcard
  have h2 := hdiv (n ^ 2) (pow_pos hn 2)
  have h3 : ((n ^ 2 : ℕ) : ℝ) ^ (1 / 100 : ℝ) = (n : ℝ) ^ (2 / 100 : ℝ) := by
    rw [Nat.cast_pow, ← rpow_natCast, ← rpow_mul (Nat.cast_nonneg _)]
    norm_num
  rw [h3] at h2
  exact h1.trans h2

private lemma sol3_bound :
    ∃ C₃ : ℝ, 0 < C₃ ∧ ∀ m n : ℕ, 0 < m → 0 < n →
      (sol3 m n).Finite ∧ ((sol3 m n).ncard : ℝ) ≤ C₃ * (n : ℝ) ^ (104 / 100 : ℝ) / m := by
  obtain ⟨C₂, hC₂, hsol2⟩ := sol2_bound
  refine ⟨3 * C₂ * (3 : ℝ) ^ (2 / 100 : ℝ), by positivity, fun m n hm hn => ?_⟩
  let A : Finset ℕ := (Icc 1 (3 * n / m)).filter (fun a => n < m * a)
  have hsub : sol3 m n ⊆ ⋃ a ∈ (A : Set ℕ), (fun p : ℕ × ℕ => (a, p)) '' sol2 (m * a - n) (n * a) := by
    rintro ⟨a, b, c⟩ ⟨ha, hab, hbc, heq⟩
    dsimp only at ha hab hbc heq
    have hb : 0 < b := lt_of_lt_of_le ha hab
    have hc : 0 < c := lt_of_lt_of_le hb hbc
    have hma_gt : n < m * a := by
      have h1 : (1 : ℚ) / a < (m : ℚ) / n := by
        have hpos : (0 : ℚ) < 1 / b + 1 / c := by positivity
        linarith
      rw [div_lt_div_iff₀ (by exact_mod_cast ha) (by exact_mod_cast hn)] at h1
      exact_mod_cast (by linarith : (n : ℚ) < m * a)
    have hma_le : m * a ≤ 3 * n := by
      have h1 : (m : ℚ) / n ≤ 3 / a := by
        have h2 : (1 : ℚ) / b ≤ 1 / a :=
          one_div_le_one_div_of_le (by exact_mod_cast ha) (by exact_mod_cast hab)
        have h3 : (1 : ℚ) / c ≤ 1 / a :=
          one_div_le_one_div_of_le (by exact_mod_cast ha) (by exact_mod_cast (hab.trans hbc))
        have h3a : (1 : ℚ) / a + 1 / a + 1 / a = 3 / a := by ring
        linarith
      rw [div_le_div_iff₀ (by exact_mod_cast hn) (by exact_mod_cast ha)] at h1
      exact_mod_cast (by linarith : (m * a : ℚ) ≤ 3 * n)
    have ha_le : a ≤ 3 * n / m := Nat.le_div_iff_mul_le hm |>.mpr (by linarith)
    have haA : a ∈ A := mem_filter.mpr ⟨mem_Icc.mpr ⟨ha, ha_le⟩, hma_gt⟩
    refine Set.mem_biUnion (Finset.mem_coe.mpr haA) ⟨(b, c), ⟨hb, hbc, ?_⟩, rfl⟩
    have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
    have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [Nat.cast_sub hma_gt.le]
    push_cast
    have h1 : (1 : ℚ) / b + 1 / c = (m : ℚ) / n - 1 / a := by linarith
    rw [h1]
    field_simp
  have hfin_fiber : ∀ a ∈ (A : Set ℕ),
      ((fun p : ℕ × ℕ => (a, p)) '' sol2 (m * a - n) (n * a)).Finite := by
    intro a ha
    have ha' := mem_filter.mp (Finset.mem_coe.mp ha)
    have ha1 : 0 < a := (mem_Icc.mp ha'.1).1
    exact ((hsol2 (m * a - n) (n * a) (Nat.sub_pos_of_lt ha'.2) (Nat.mul_pos hn ha1)).1).image _
  have hfin : (sol3 m n).Finite :=
    ((Finset.finite_toSet A).biUnion hfin_fiber).subset hsub
  have hcard : ((sol3 m n).ncard : ℝ) ≤
      ∑ a ∈ A, ((sol2 (m * a - n) (n * a)).ncard : ℝ) := by
    have h1 : (sol3 m n).ncard ≤
        (⋃ a ∈ (A : Set ℕ), (fun p : ℕ × ℕ => (a, p)) '' sol2 (m * a - n) (n * a)).ncard :=
      Set.ncard_le_ncard hsub ((Finset.finite_toSet A).biUnion hfin_fiber)
    have h2 : (⋃ a ∈ (A : Set ℕ), (fun p : ℕ × ℕ => (a, p)) '' sol2 (m * a - n) (n * a)).ncard ≤
        ∑ a ∈ A, ((fun p : ℕ × ℕ => (a, p)) '' sol2 (m * a - n) (n * a)).ncard :=
      ncard_biUnion_finset_le A _
    have h3 : ∑ a ∈ A, ((fun p : ℕ × ℕ => (a, p)) '' sol2 (m * a - n) (n * a)).ncard ≤
        ∑ a ∈ A, (sol2 (m * a - n) (n * a)).ncard := by
      refine sum_le_sum fun a ha => ?_
      have ha' := mem_filter.mp ha
      have ha1 : 0 < a := (mem_Icc.mp ha'.1).1
      exact Set.ncard_image_le (hsol2 (m * a - n) (n * a) (Nat.sub_pos_of_lt ha'.2) (Nat.mul_pos hn ha1)).1
    exact_mod_cast h1.trans (h2.trans h3)
  have hsum : ∑ a ∈ A, ((sol2 (m * a - n) (n * a)).ncard : ℝ) ≤
      (A.card : ℝ) * (C₂ * ((3 * n ^ 2 : ℕ) : ℝ) ^ (2 / 100 : ℝ)) := by
    calc
      ∑ a ∈ A, ((sol2 (m * a - n) (n * a)).ncard : ℝ)
          ≤ ∑ a ∈ A, (C₂ * ((n * a : ℕ) : ℝ) ^ (2 / 100 : ℝ)) := by
            refine sum_le_sum fun a ha => ?_
            have ha' := mem_filter.mp ha
            exact (hsol2 _ _ (Nat.sub_pos_of_lt ha'.2) (Nat.mul_pos hn (mem_Icc.mp ha'.1).1)).2
      _ ≤ ∑ _a ∈ A, (C₂ * ((3 * n ^ 2 : ℕ) : ℝ) ^ (2 / 100 : ℝ)) := by
            refine sum_le_sum fun a ha => ?_
            have ha' := mem_filter.mp ha
            have ha_le : a ≤ 3 * n / m := (mem_Icc.mp ha'.1).2
            have ha_le3n : a ≤ 3 * n := ha_le.trans (Nat.div_le_self _ _)
            have hna : n * a ≤ 3 * n ^ 2 := by nlinarith
            exact mul_le_mul_of_nonneg_left
              (rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hna) (by norm_num)) hC₂.le
      _ = (A.card : ℝ) * (C₂ * ((3 * n ^ 2 : ℕ) : ℝ) ^ (2 / 100 : ℝ)) := by
            rw [sum_const, nsmul_eq_mul]
  have hAcard : (A.card : ℝ) ≤ 3 * (n : ℝ) / m := by
    have h1 : A.card ≤ (Icc 1 (3 * n / m)).card := card_le_card (filter_subset _ _)
    have h2 : (Icc 1 (3 * n / m)).card = 3 * n / m := by simp
    have h3 : ((3 * n / m : ℕ) : ℝ) ≤ (3 * n : ℝ) / m := by
      have := Nat.cast_div_le (m := 3 * n) (n := m) (α := ℝ)
      push_cast at this
      exact this
    have h4 : (A.card : ℝ) ≤ ((3 * n / m : ℕ) : ℝ) := by exact_mod_cast h1.trans_eq h2
    linarith
  have hrpow : ((3 * n ^ 2 : ℕ) : ℝ) ^ (2 / 100 : ℝ) = (3 : ℝ) ^ (2 / 100 : ℝ) * (n : ℝ) ^ (4 / 100 : ℝ) := by
    push_cast
    rw [mul_rpow (by norm_num) (by positivity), ← rpow_natCast (n : ℝ) 2, ← rpow_mul (Nat.cast_nonneg _)]
    norm_num
  have hfinal : (A.card : ℝ) * (C₂ * ((3 * n ^ 2 : ℕ) : ℝ) ^ (2 / 100 : ℝ)) ≤
      3 * C₂ * (3 : ℝ) ^ (2 / 100 : ℝ) * (n : ℝ) ^ (104 / 100 : ℝ) / m := by
    rw [hrpow]
    have hmul := mul_le_mul_of_nonneg_right hAcard
      (show 0 ≤ C₂ * ((3 : ℝ) ^ (2 / 100 : ℝ) * (n : ℝ) ^ (4 / 100 : ℝ)) by positivity)
    have hn_split : (n : ℝ) * (n : ℝ) ^ (4 / 100 : ℝ) = (n : ℝ) ^ (104 / 100 : ℝ) := by
      have hnp : (0 : ℝ) < n := by exact_mod_cast hn
      conv_lhs => arg 1; rw [← rpow_one (n : ℝ)]
      rw [← rpow_add hnp]
      norm_num
    calc
      (A.card : ℝ) * (C₂ * ((3 : ℝ) ^ (2 / 100 : ℝ) * (n : ℝ) ^ (4 / 100 : ℝ)))
          ≤ (3 * (n : ℝ) / m) * (C₂ * ((3 : ℝ) ^ (2 / 100 : ℝ) * (n : ℝ) ^ (4 / 100 : ℝ))) := hmul
      _ = 3 * C₂ * (3 : ℝ) ^ (2 / 100 : ℝ) * ((n : ℝ) * (n : ℝ) ^ (4 / 100 : ℝ)) / m := by ring
      _ = 3 * C₂ * (3 : ℝ) ^ (2 / 100 : ℝ) * (n : ℝ) ^ (104 / 100 : ℝ) / m := by rw [hn_split]
  exact ⟨hfin, hcard.trans (hsum.trans hfinal)⟩

private lemma harmonic_le_one_add_log (N : ℕ) (hN : 1 ≤ N) :
    ∑ u ∈ Icc 1 N, (1 : ℝ) / u ≤ 1 + log N := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [show Icc 1 (k + 1) = insert (k + 1) (Icc 1 k) by
      ext x; simp only [mem_Icc, mem_insert]; omega]
    rw [sum_insert (by simp)]
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hk1pos : (0 : ℝ) < k + 1 := by positivity
    have hlog : (1 : ℝ) / (k + 1) ≤ log (k + 1 : ℕ) - log k := by
      have h1 : log ((k : ℝ) / (k + 1)) ≤ (k : ℝ) / (k + 1) - 1 :=
        log_le_sub_one_of_pos (div_pos hkpos hk1pos)
      rw [log_div hkpos.ne' hk1pos.ne'] at h1
      push_cast
      have h2 : (k : ℝ) / (k + 1) - 1 = - (1 / (k + 1)) := by field_simp; ring
      linarith
    push_cast at hlog ⊢
    linarith

private lemma one_add_log_three_le (n : ℕ) (hn : 0 < n) :
    1 + log ((3 * n : ℕ) : ℝ) ≤ 200 * (n : ℝ) ^ (1 / 100 : ℝ) := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog_le : log (3 * (n : ℝ)) ≤ 100 * (3 * (n : ℝ)) ^ (1 / 100 : ℝ) := by
    have h1 := log_le_sub_one_of_pos (rpow_pos_of_pos (show (0 : ℝ) < 3 * n by positivity) (1 / 100 : ℝ))
    rw [log_rpow (by positivity)] at h1
    linarith
  have h3p : (3 : ℝ) ^ (1 / 100 : ℝ) ≤ (3 / 2 : ℝ) := by
    have h1 : (3 : ℝ) ≤ (3 / 2 : ℝ) ^ (100 : ℕ) := by
      have h2 : (3 : ℝ) ≤ (3 / 2 : ℝ) ^ (3 : ℕ) := by norm_num
      exact h2.trans (pow_le_pow_right₀ (by norm_num) (by norm_num))
    have h2 := rpow_le_rpow (by norm_num) h1 (by norm_num : (0 : ℝ) ≤ 1 / 100)
    rw [← rpow_natCast (3 / 2 : ℝ) 100, ← rpow_mul (by norm_num)] at h2
    norm_num at h2
    exact h2
  have h1le : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 100 : ℝ) :=
    one_le_rpow (by exact_mod_cast hn) (by norm_num)
  push_cast
  have hsplit : (3 * (n : ℝ)) ^ (1 / 100 : ℝ) = (3 : ℝ) ^ (1 / 100 : ℝ) * (n : ℝ) ^ (1 / 100 : ℝ) :=
    mul_rpow (by norm_num) (Nat.cast_nonneg _)
  rw [hsplit] at hlog_le
  nlinarith

private lemma sol4_bound :
    ∃ C₄ : ℝ, 0 < C₄ ∧ ∀ m n : ℕ, 0 < m → 0 < n →
      (sol4 m n).Finite ∧ ((sol4 m n).ncard : ℝ) ≤ C₄ * (n : ℝ) ^ (209 / 100 : ℝ) := by
  obtain ⟨C₃, hC₃, hsol3⟩ := sol3_bound
  refine ⟨200 * C₃ * (4 : ℝ) ^ (104 / 100 : ℝ), by positivity, fun m n hm hn => ?_⟩
  let U : Finset ℕ := (Icc 1 (3 * n)).filter (fun u => m ∣ n + u)
  have hsub : sol4 m n ⊆
      ⋃ u ∈ (U : Set ℕ), (fun p : ℕ × ℕ × ℕ => ((n + u) / m, p)) '' sol3 u (n * ((n + u) / m)) := by
    rintro ⟨a, b, c, d⟩ ⟨ha, hab, hbc, hcd, heq⟩
    dsimp only at ha hab hbc hcd heq
    have hb : 0 < b := lt_of_lt_of_le ha hab
    have hc : 0 < c := lt_of_lt_of_le hb hbc
    have hd : 0 < d := lt_of_lt_of_le hc hcd
    have hma_gt : n < m * a := by
      have h1 : (1 : ℚ) / a < (m : ℚ) / n := by
        have hpos : (0 : ℚ) < 1 / b + 1 / c + 1 / d := by positivity
        linarith
      rw [div_lt_div_iff₀ (by exact_mod_cast ha) (by exact_mod_cast hn)] at h1
      exact_mod_cast (by linarith : (n : ℚ) < m * a)
    have hma_le : m * a ≤ 4 * n := by
      have h1 : (m : ℚ) / n ≤ 4 / a := by
        have h2 : (1 : ℚ) / b ≤ 1 / a :=
          one_div_le_one_div_of_le (by exact_mod_cast ha) (by exact_mod_cast hab)
        have h3 : (1 : ℚ) / c ≤ 1 / a :=
          one_div_le_one_div_of_le (by exact_mod_cast ha) (by exact_mod_cast (hab.trans hbc))
        have h4 : (1 : ℚ) / d ≤ 1 / a :=
          one_div_le_one_div_of_le (by exact_mod_cast ha) (by exact_mod_cast ((hab.trans hbc).trans hcd))
        have h4a : (1 : ℚ) / a + 1 / a + 1 / a + 1 / a = 4 / a := by ring
        linarith
      rw [div_le_div_iff₀ (by exact_mod_cast hn) (by exact_mod_cast ha)] at h1
      exact_mod_cast (by linarith : (m * a : ℚ) ≤ 4 * n)
    let u := m * a - n
    have hu1 : 1 ≤ u := by omega
    have hu3n : u ≤ 3 * n := by omega
    have hnu : n + u = m * a := by omega
    have ha_eq : (n + u) / m = a := by rw [hnu, Nat.mul_div_cancel_left a hm]
    have huU : u ∈ U := mem_filter.mpr ⟨mem_Icc.mpr ⟨hu1, hu3n⟩, ⟨a, hnu⟩⟩
    refine Set.mem_biUnion (Finset.mem_coe.mpr huU) ⟨(b, c, d), ⟨hb, hbc, hcd, ?_⟩, ?_⟩
    · rw [ha_eq]
      have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
      have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
      have huQ : (u : ℚ) = m * a - n := by
        rw [Nat.cast_sub hma_gt.le]; push_cast; rfl
      rw [huQ]
      push_cast
      have h1 : (1 : ℚ) / b + 1 / c + 1 / d = (m : ℚ) / n - 1 / a := by linarith
      rw [h1]
      field_simp
    · simp [ha_eq]
  have hfin_fiber : ∀ u ∈ (U : Set ℕ),
      ((fun p : ℕ × ℕ × ℕ => ((n + u) / m, p)) '' sol3 u (n * ((n + u) / m))).Finite := by
    intro u hu
    have hu' := mem_filter.mp (Finset.mem_coe.mp hu)
    have hu1 : 0 < u := (mem_Icc.mp hu'.1).1
    obtain ⟨a, ha⟩ := hu'.2
    have hapos : 0 < (n + u) / m := by
      rw [ha, Nat.mul_div_cancel_left a hm]
      by_contra h0
      have : a = 0 := by omega
      subst this; omega
    exact ((hsol3 u (n * ((n + u) / m)) hu1 (Nat.mul_pos hn hapos)).1).image _
  have hfin : (sol4 m n).Finite :=
    ((Finset.finite_toSet U).biUnion hfin_fiber).subset hsub
  have hcard : ((sol4 m n).ncard : ℝ) ≤
      ∑ u ∈ U, ((sol3 u (n * ((n + u) / m))).ncard : ℝ) := by
    have h1 := Set.ncard_le_ncard hsub ((Finset.finite_toSet U).biUnion hfin_fiber)
    have h2 := ncard_biUnion_finset_le U
      (fun u => (fun p : ℕ × ℕ × ℕ => ((n + u) / m, p)) '' sol3 u (n * ((n + u) / m)))
    have h3 : ∑ u ∈ U, ((fun p : ℕ × ℕ × ℕ => ((n + u) / m, p)) '' sol3 u (n * ((n + u) / m))).ncard ≤
        ∑ u ∈ U, (sol3 u (n * ((n + u) / m))).ncard := by
      refine sum_le_sum fun u hu => ?_
      have hu' := mem_filter.mp hu
      obtain ⟨a, ha⟩ := hu'.2
      have hapos : 0 < (n + u) / m := by
        rw [ha, Nat.mul_div_cancel_left a hm]
        by_contra h0; have : a = 0 := by omega
        subst this; simp at ha; omega
      exact Set.ncard_image_le (hsol3 u _ (mem_Icc.mp hu'.1).1 (Nat.mul_pos hn hapos)).1
    exact_mod_cast h1.trans (h2.trans h3)
  have hsum : ∑ u ∈ U, ((sol3 u (n * ((n + u) / m))).ncard : ℝ) ≤
      (C₃ * ((4 * n ^ 2 : ℕ) : ℝ) ^ (104 / 100 : ℝ)) * ∑ u ∈ Icc 1 (3 * n), (1 : ℝ) / u := by
    calc
      ∑ u ∈ U, ((sol3 u (n * ((n + u) / m))).ncard : ℝ)
          ≤ ∑ u ∈ U, (C₃ * ((n * ((n + u) / m) : ℕ) : ℝ) ^ (104 / 100 : ℝ) / u) := by
            refine sum_le_sum fun u hu => ?_
            have hu' := mem_filter.mp hu
            obtain ⟨a, ha⟩ := hu'.2
            have hapos : 0 < (n + u) / m := by
              rw [ha, Nat.mul_div_cancel_left a hm]
              by_contra h0; have : a = 0 := by omega
              subst this; simp at ha; omega
            exact (hsol3 u _ (mem_Icc.mp hu'.1).1 (Nat.mul_pos hn hapos)).2
      _ ≤ ∑ u ∈ U, (C₃ * ((4 * n ^ 2 : ℕ) : ℝ) ^ (104 / 100 : ℝ) / u) := by
            refine sum_le_sum fun u hu => ?_
            have hu' := mem_filter.mp hu
            have hu3n : u ≤ 3 * n := (mem_Icc.mp hu'.1).2
            have hle : (n + u) / m ≤ 4 * n := (Nat.div_le_self _ _).trans (by omega)
            have hmul : n * ((n + u) / m) ≤ 4 * n ^ 2 := by nlinarith
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left
                (rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hmul) (by norm_num)) hC₃.le)
              (Nat.cast_nonneg _)
      _ ≤ ∑ u ∈ Icc 1 (3 * n), (C₃ * ((4 * n ^ 2 : ℕ) : ℝ) ^ (104 / 100 : ℝ) / u) := by
            refine sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun u _ _ => by positivity
      _ = (C₃ * ((4 * n ^ 2 : ℕ) : ℝ) ^ (104 / 100 : ℝ)) * ∑ u ∈ Icc 1 (3 * n), (1 : ℝ) / u := by
            rw [mul_sum]
            refine sum_congr rfl fun u _ => by ring
  have hharm : ∑ u ∈ Icc 1 (3 * n), (1 : ℝ) / u ≤ 200 * (n : ℝ) ^ (1 / 100 : ℝ) :=
    (harmonic_le_one_add_log (3 * n) (by omega)).trans (one_add_log_three_le n hn)
  have hrpow : ((4 * n ^ 2 : ℕ) : ℝ) ^ (104 / 100 : ℝ) * (n : ℝ) ^ (1 / 100 : ℝ) =
      (4 : ℝ) ^ (104 / 100 : ℝ) * (n : ℝ) ^ (209 / 100 : ℝ) := by
    push_cast
    rw [mul_rpow (by norm_num) (by positivity), ← rpow_natCast (n : ℝ) 2,
      ← rpow_mul (Nat.cast_nonneg _), mul_assoc, ← rpow_add (by exact_mod_cast hn)]
    norm_num
  refine ⟨hfin, ?_⟩
  calc
    ((sol4 m n).ncard : ℝ)
        ≤ (C₃ * ((4 * n ^ 2 : ℕ) : ℝ) ^ (104 / 100 : ℝ)) * (200 * (n : ℝ) ^ (1 / 100 : ℝ)) := by
          exact hcard.trans (hsum.trans (mul_le_mul_of_nonneg_left hharm (by positivity)))
    _ = 200 * C₃ * (((4 * n ^ 2 : ℕ) : ℝ) ^ (104 / 100 : ℝ) * (n : ℝ) ^ (1 / 100 : ℝ)) := by ring
    _ = 200 * C₃ * (4 : ℝ) ^ (104 / 100 : ℝ) * (n : ℝ) ^ (209 / 100 : ℝ) := by rw [hrpow]; ring

/- ### Part 5: Assembly for `F k` -/

private lemma F_le_bound :
    ∃ C₄ : ℝ, 0 < C₄ ∧ ∀ k : ℕ, 5 ≤ k →
      (F k : ℝ) ≤ C₄ * ((k : ℝ) ^ (k - 4) * c₀ ^ (2 ^ (k - 4) : ℕ)) ^ (309 / 100 : ℝ) := by
  obtain ⟨C₄, hC₄, hsol4⟩ := sol4_bound
  refine ⟨C₄, hC₄, fun k hk => ?_⟩
  let r := k - 4
  have hr_eq : r + 4 = k := by omega
  let T : Set (Finset ℕ) := {S : Finset ℕ | S.card = k ∧ 0 ∉ S ∧ ∑ n ∈ S, (1 : ℚ) / n = 1}
  let Box : Finset (Fin r → ℕ) := Fintype.piFinset fun j : Fin r => Icc 1 (k * u j.val)
  let GBox : Finset (Fin r → ℕ) := Box.filter fun p => ∑ j : Fin r, (1 : ℚ) / p j < 1
  -- For each valid prefix p ∈ GBox, define denominator n(p) and numerator m(p)
  let den (p : Fin r → ℕ) : ℕ := ∏ j : Fin r, p j
  let num (p : Fin r → ℕ) : ℕ := den p - ∑ j : Fin r, den p / p j
  have hden_pos : ∀ p ∈ GBox, 0 < den p := by
    intro p hp
    have hpB := (mem_filter.mp hp).1
    refine prod_pos fun j _ => ?_
    have hj := (Fintype.mem_piFinset.mp hpB) j
    exact (mem_Icc.mp hj).1
  have hnum_eq : ∀ p ∈ GBox, 0 < num p ∧ 1 - ∑ j : Fin r, (1 : ℚ) / p j = (num p : ℚ) / den p := by
    intro p hp
    have hpB := (mem_filter.mp hp).1
    have hlt := (mem_filter.mp hp).2
    have hdp : 0 < den p := hden_pos p hp
    have hdQ : (den p : ℚ) ≠ 0 := by exact_mod_cast hdp.ne'
    have hsum_eq : (∑ j : Fin r, (1 : ℚ) / p j) * den p = (∑ j : Fin r, den p / p j : ℕ) := by
      rw [sum_mul, Nat.cast_sum]
      refine sum_congr rfl fun j _ => ?_
      have hjp : 0 < p j := (mem_Icc.mp (Fintype.mem_piFinset.mp hpB j)).1
      have hdvd : p j ∣ den p := dvd_prod_of_mem p (mem_univ j)
      have hjQ : (p j : ℚ) ≠ 0 := by exact_mod_cast hjp.ne'
      rw [Nat.cast_div hdvd hjQ]
      ring
    have hltN : ∑ j : Fin r, den p / p j < den p := by
      have h1 : ((∑ j : Fin r, den p / p j : ℕ) : ℚ) < (den p : ℚ) := by
        rw [← hsum_eq]
        have hdpQ : (0 : ℚ) < den p := by exact_mod_cast hdp
        nlinarith
      exact_mod_cast h1
    refine ⟨Nat.sub_pos_of_lt hltN, ?_⟩
    rw [Nat.cast_sub hltN.le, sub_div, div_self hdQ]
    congr 1
    rw [eq_div_iff hdQ, hsum_eq]
  -- Map each (p, q) with p ∈ GBox and q ∈ sol4 (num p) (den p) to the Finset of all k values
  let mkSet (p : Fin r → ℕ) (q : ℕ × ℕ × ℕ × ℕ) : Finset ℕ :=
    (univ.image p) ∪ {q.1, q.2.1, q.2.2.1, q.2.2.2}
  have hcover : T ⊆ ⋃ p ∈ (GBox : Set (Fin r → ℕ)), (mkSet p) '' sol4 (num p) (den p) := by
    intro S hS
    rcases hS with ⟨hcard, h0, hsum⟩
    let e : Fin k ↪o ℕ := S.orderEmbOfFin hcard
    have hpos : ∀ i : Fin k, 0 < e i := by
      intro i
      have hmem : e i ∈ S := S.orderEmbOfFin_mem hcard i
      exact Nat.pos_of_ne_zero fun h => h0 (h ▸ hmem)
    have hsum_e : ∑ i : Fin k, (1 : ℚ) / e i = 1 := by
      have hbij : ∑ i : Fin k, (1 : ℚ) / e i = ∑ x ∈ S, (1 : ℚ) / x :=
        Finset.sum_nbij (fun i => e i) (fun i _ => S.orderEmbOfFin_mem hcard i)
          (fun i₁ _ i₂ _ h => e.injective h)
          (fun x hx => by
            have : x ∈ Set.range e := by
              rw [S.range_orderEmbOfFin hcard]; exact hx
            obtain ⟨i, rfl⟩ := this
            exact ⟨i, mem_univ i, rfl⟩)
          (fun _ _ => rfl)
      exact hbij.trans hsum
    let p : Fin r → ℕ := fun j => e ⟨j.val, by omega⟩
    let b : ℕ → ℕ := fun i => if h : i < k then e ⟨i, h⟩ else 1
    have hsum_split : ∑ i : Fin k, (1 : ℚ) / e i =
        (∑ j : Fin r, (1 : ℚ) / p j) +
        ((1 : ℚ) / e ⟨r, by omega⟩ + 1 / e ⟨r + 1, by omega⟩ +
         1 / e ⟨r + 2, by omega⟩ + 1 / e ⟨r + 3, by omega⟩) := by
      have h1 : ∑ i : Fin k, (1 : ℚ) / e i = ∑ i ∈ range (r + 4), (1 : ℚ) / b i := by
        rw [hr_eq, ← Fin.sum_univ_eq_sum_range]
        refine sum_congr rfl fun i _ => by simp [b, i.isLt]
      rw [h1, sum_range_add]
      have hleft : ∑ i ∈ range r, (1 : ℚ) / b i = ∑ j : Fin r, (1 : ℚ) / p j := by
        rw [← Fin.sum_univ_eq_sum_range]
        refine sum_congr rfl fun j _ => by simp [b, p, show j.val < k by omega]
      have hright : ∑ i ∈ range 4, (1 : ℚ) / b (r + i) =
          (1 : ℚ) / e ⟨r, by omega⟩ + 1 / e ⟨r + 1, by omega⟩ +
          1 / e ⟨r + 2, by omega⟩ + 1 / e ⟨r + 3, by omega⟩ := by
        simp only [sum_range_succ, sum_range_zero, zero_add, add_zero, b]
        have h0' : r < k := by omega
        have h1' : r + 1 < k := by omega
        have h2' : r + 2 < k := by omega
        have h3' : r + 3 < k := by omega
        simp [h0', h1', h2', h3']
      rw [hleft, hright]
    have hp_lt : ∑ j : Fin r, (1 : ℚ) / p j < 1 := by
      have hpos4 : (0 : ℚ) < (1 : ℚ) / e ⟨r, by omega⟩ + 1 / e ⟨r + 1, by omega⟩ +
          1 / e ⟨r + 2, by omega⟩ + 1 / e ⟨r + 3, by omega⟩ := by
        have := hpos ⟨r, by omega⟩
        have := hpos ⟨r + 1, by omega⟩
        have := hpos ⟨r + 2, by omega⟩
        have := hpos ⟨r + 3, by omega⟩
        positivity
      linarith
    have hp_box : p ∈ Box := by
      rw [Fintype.mem_piFinset]
      intro j
      refine mem_Icc.mpr ⟨hpos ⟨j.val, by omega⟩, ?_⟩
      have hbj_lt : ∑ i ∈ range j.val, (1 : ℚ) / b i < 1 := by
        have h1 : ∑ i ∈ range j.val, (1 : ℚ) / b i ≤ ∑ i : Fin r, (1 : ℚ) / p i := by
          have hsub' : range j.val ⊆ range r := range_mono j.isLt.le
          have h1' : ∑ i ∈ range j.val, (1 : ℚ) / b i ≤ ∑ i ∈ range r, (1 : ℚ) / b i :=
            sum_le_sum_of_subset_of_nonneg hsub' fun i _ _ => by positivity
          have heq' : ∑ i ∈ range r, (1 : ℚ) / b i = ∑ i : Fin r, (1 : ℚ) / p i := by
            rw [← Fin.sum_univ_eq_sum_range]
            refine sum_congr rfl fun i _ => by simp [b, p, show i.val < k by omega]
          linarith
        exact h1.trans_lt hp_lt
      have hcurt : ∑ i ∈ range j.val, (1 : ℚ) / b i ≤ 1 - 1 / u j.val :=
        curtiss_bound j.val b
          (fun i hi => by
            have hik : i < k := by omega
            simp only [b, dif_pos hik]
            exact hpos ⟨i, hik⟩)
          (fun i hi => by
            have hik : i < k := by omega
            have hi1k : i + 1 < k := by omega
            simp only [b, dif_pos hik, dif_pos hi1k]
            exact (e.strictMono (show (⟨i, hik⟩ : Fin k) < ⟨i + 1, hi1k⟩ by
              exact Fin.mk_lt_mk.mpr (Nat.lt_succ_self i))).le)
          hbj_lt
      have htail : 1 - ∑ i ∈ range j.val, (1 : ℚ) / b i ≤ (k : ℚ) / p j := by
        have hfull : ∑ i ∈ range k, (1 : ℚ) / b i = 1 := by
          have h1 : ∑ i ∈ range k, (1 : ℚ) / b i = ∑ i : Fin k, (1 : ℚ) / e i := by
            rw [← Fin.sum_univ_eq_sum_range]
            refine sum_congr rfl fun i _ => by simp [b, i.isLt]
          exact h1.trans hsum_e
        have hsplit : ∑ i ∈ range k, (1 : ℚ) / b i =
            (∑ i ∈ range j.val, (1 : ℚ) / b i) + ∑ i ∈ Ico j.val k, (1 : ℚ) / b i := by
          rw [← sum_range_add_sum_Ico _ (by omega : j.val ≤ k)]
        have htail_le : ∑ i ∈ Ico j.val k, (1 : ℚ) / b i ≤ (k - j.val : ℕ) * ((1 : ℚ) / p j) := by
          calc
            ∑ i ∈ Ico j.val k, (1 : ℚ) / b i
                ≤ ∑ _i ∈ Ico j.val k, (1 : ℚ) / p j := by
                  refine sum_le_sum fun i hi => ?_
                  have hi1 := mem_Ico.mp hi
                  simp only [b, dif_pos hi1.2]
                  refine one_div_le_one_div_of_le (by exact_mod_cast hpos ⟨j.val, by omega⟩) ?_
                  have hle_fin : (⟨j.val, by omega⟩ : Fin k) ≤ ⟨i, hi1.2⟩ := Fin.mk_le_mk.mpr hi1.1
                  exact_mod_cast e.monotone hle_fin
            _ = (k - j.val : ℕ) * ((1 : ℚ) / p j) := by
                  rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
        have hkj : ((k - j.val : ℕ) : ℚ) ≤ (k : ℚ) := by exact_mod_cast Nat.sub_le k j.val
        have hle2 : ((k - j.val : ℕ) : ℚ) * ((1 : ℚ) / p j) ≤ (k : ℚ) / p j := by
          rw [mul_one_div]
          exact div_le_div_of_nonneg_right hkj (Nat.cast_nonneg _)
        linarith
      have hge : (1 : ℚ) / u j.val ≤ (k : ℚ) / p j := by linarith
      rw [div_le_div_iff₀ (by exact_mod_cast u_pos j.val) (by exact_mod_cast hpos ⟨j.val, by omega⟩)] at hge
      exact_mod_cast (by linarith : (p j : ℚ) ≤ k * u j.val)
    have hpG : p ∈ GBox := mem_filter.mpr ⟨hp_box, hp_lt⟩
    let q : ℕ × ℕ × ℕ × ℕ :=
      (e ⟨r, by omega⟩, e ⟨r + 1, by omega⟩, e ⟨r + 2, by omega⟩, e ⟨r + 3, by omega⟩)
    have hq_mem : q ∈ sol4 (num p) (den p) := by
      refine ⟨hpos ⟨r, by omega⟩,
        e.monotone (Fin.mk_le_mk.mpr (by omega)),
        e.monotone (Fin.mk_le_mk.mpr (by omega)),
        e.monotone (Fin.mk_le_mk.mpr (by omega)), ?_⟩
      rw [← (hnum_eq p hpG).2]
      dsimp only [q]
      linarith
    refine Set.mem_biUnion (Finset.mem_coe.mpr hpG) ⟨q, hq_mem, ?_⟩
    ext x
    simp only [mkSet, mem_union, mem_image, mem_univ, true_and, mem_insert, mem_singleton, p, q]
    constructor
    · rintro (⟨j, rfl⟩ | rfl | rfl | rfl | rfl) <;> exact S.orderEmbOfFin_mem hcard _
    · intro hx
      have : x ∈ Set.range e := by rw [S.range_orderEmbOfFin hcard]; exact hx
      obtain ⟨i, rfl⟩ := this
      by_cases hi : i.val < r
      · exact Or.inl ⟨⟨i.val, hi⟩, rfl⟩
      · have hcases : i.val = r ∨ i.val = r + 1 ∨ i.val = r + 2 ∨ i.val = r + 3 := by omega
        rcases hcases with h | h | h | h
        · exact Or.inr (Or.inl (congrArg e (Fin.ext h)))
        · exact Or.inr (Or.inr (Or.inl (congrArg e (Fin.ext h))))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (congrArg e (Fin.ext h)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (congrArg e (Fin.ext h)))))
  have hfin_fiber : ∀ p ∈ (GBox : Set (Fin r → ℕ)), ((mkSet p) '' sol4 (num p) (den p)).Finite := by
    intro p hp
    have hp' := Finset.mem_coe.mp hp
    exact ((hsol4 (num p) (den p) (hnum_eq p hp').1 (hden_pos p hp')).1).image _
  have hBox_card : (Box.card : ℝ) ≤ (k : ℝ) ^ r * c₀ ^ (2 ^ r : ℕ) := by
    have h1 : Box.card = ∏ j : Fin r, (k * u j.val) := by
      simp [Box, Fintype.card_piFinset]
    have h2 : (Box.card : ℝ) = (k : ℝ) ^ r * ∏ j ∈ range r, (u j : ℝ) := by
      rw [h1, Nat.cast_prod, Fin.prod_univ_eq_prod_range (fun j => ((k * u j : ℕ) : ℝ)) r]
      simp only [Nat.cast_mul, prod_mul_distrib, prod_const, card_range]
    rw [h2]
    exact mul_le_mul_of_nonneg_left (prod_u_le r) (by positivity)
  have hden_le : ∀ p ∈ GBox, (den p : ℝ) ≤ (k : ℝ) ^ r * c₀ ^ (2 ^ r : ℕ) := by
    intro p hp
    have hpB := (mem_filter.mp hp).1
    have h1 : den p ≤ ∏ j : Fin r, (k * u j.val) := by
      refine prod_le_prod' fun j _ => (mem_Icc.mp (Fintype.mem_piFinset.mp hpB j)).2
    have h2 : (∏ j : Fin r, (k * u j.val) : ℕ) = Box.card := by
      simp [Box, Fintype.card_piFinset]
    exact (show (den p : ℝ) ≤ (Box.card : ℝ) by exact_mod_cast h1.trans_eq h2).trans hBox_card
  have hFcard : (F k : ℝ) ≤ ∑ p ∈ GBox, ((sol4 (num p) (den p)).ncard : ℝ) := by
    have h1 : T.ncard ≤ (⋃ p ∈ (GBox : Set (Fin r → ℕ)), (mkSet p) '' sol4 (num p) (den p)).ncard :=
      Set.ncard_le_ncard hcover ((Finset.finite_toSet GBox).biUnion hfin_fiber)
    have h2 := ncard_biUnion_finset_le GBox (fun p => (mkSet p) '' sol4 (num p) (den p))
    have h3 : ∑ p ∈ GBox, ((mkSet p) '' sol4 (num p) (den p)).ncard ≤
        ∑ p ∈ GBox, (sol4 (num p) (den p)).ncard := by
      refine sum_le_sum fun p hp =>
        Set.ncard_image_le (hsol4 (num p) (den p) (hnum_eq p hp).1 (hden_pos p hp)).1
    change (T.ncard : ℝ) ≤ _
    exact_mod_cast h1.trans (h2.trans h3)
  let M : ℝ := (k : ℝ) ^ r * c₀ ^ (2 ^ r : ℕ)
  have hMpos : 0 < M := mul_pos (pow_pos (by exact_mod_cast (by omega : 0 < k)) r)
    (pow_pos (lt_trans zero_lt_one one_lt_c₀) _)
  have hGBox_card : (GBox.card : ℝ) ≤ M :=
    (show (GBox.card : ℝ) ≤ (Box.card : ℝ) by exact_mod_cast card_le_card (filter_subset _ _)).trans hBox_card
  calc
    (F k : ℝ) ≤ ∑ p ∈ GBox, ((sol4 (num p) (den p)).ncard : ℝ) := hFcard
    _ ≤ ∑ p ∈ GBox, (C₄ * (den p : ℝ) ^ (209 / 100 : ℝ)) := by
          refine sum_le_sum fun p hp => (hsol4 _ _ (hnum_eq p hp).1 (hden_pos p hp)).2
    _ ≤ ∑ _p ∈ GBox, (C₄ * M ^ (209 / 100 : ℝ)) := by
          refine sum_le_sum fun p hp => mul_le_mul_of_nonneg_left
            (rpow_le_rpow (Nat.cast_nonneg _) (hden_le p hp) (by norm_num)) hC₄.le
    _ = (GBox.card : ℝ) * (C₄ * M ^ (209 / 100 : ℝ)) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ M * (C₄ * M ^ (209 / 100 : ℝ)) :=
          mul_le_mul_of_nonneg_right hGBox_card (by positivity)
    _ = C₄ * (M * M ^ (209 / 100 : ℝ)) := by ring
    _ = C₄ * M ^ (309 / 100 : ℝ) := by
          congr 1
          conv_lhs => arg 1; rw [← rpow_one M]
          rw [← rpow_add hMpos]
          norm_num

private lemma tendsto_eventually_poly_le_exp (C₄ : ℝ) (hC₄ : 0 < C₄) :
    ∀ᶠ k : ℕ in atTop,
      C₄ * ((k : ℝ) ^ (k - 4) * c₀ ^ (2 ^ (k - 4) : ℕ)) ^ (309 / 100 : ℝ) ≤
        c₀ ^ ((1 / 5 : ℝ) * 2 ^ k) := by
  have hc0 : 0 < c₀ := lt_trans zero_lt_one one_lt_c₀
  have hlogc : 0 < log c₀ := log_pos one_lt_c₀
  have hlim : Tendsto (fun k : ℕ => (log C₄ + 4 * (k : ℝ) ^ 2) / ((2 : ℝ) ^ k)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => log C₄ / ((2 : ℝ) ^ k)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
    have h2 : Tendsto (fun k : ℕ => 4 * ((k : ℝ) ^ 2 / ((2 : ℝ) ^ k))) atTop (𝓝 0) := by
      simpa using (tendsto_pow_const_div_const_pow_of_one_lt (2 : ℕ) (by norm_num : (1 : ℝ) < 2)).const_mul 4
    simpa [add_div, mul_div_assoc] using h1.add h2
  filter_upwards [eventually_ge_atTop 5, hlim.eventually (gt_mem_nhds (show (0 : ℝ) < (11 / 1600 : ℝ) * log c₀ by positivity))] with k hk hsmall
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have h2pow : ((2 ^ (k - 4) : ℕ) : ℝ) * (309 / 100 : ℝ) = (309 / 1600 : ℝ) * (2 : ℝ) ^ k := by
    have hsplit : (2 : ℕ) ^ k = 2 ^ (k - 4) * 16 := by
      have : k = (k - 4) + 4 := by omega
      conv_lhs => rw [this, pow_add]
      norm_num
    have hsplitR : (2 : ℝ) ^ k = ((2 ^ (k - 4) : ℕ) : ℝ) * 16 := by exact_mod_cast hsplit
    rw [hsplitR]
    ring
  have hlog_lhs : log (C₄ * ((k : ℝ) ^ (k - 4) * c₀ ^ (2 ^ (k - 4) : ℕ)) ^ (309 / 100 : ℝ)) ≤
      log C₄ + 4 * (k : ℝ) ^ 2 + (309 / 1600 : ℝ) * (2 : ℝ) ^ k * log c₀ := by
    have hinner : 0 < (k : ℝ) ^ (k - 4) * c₀ ^ (2 ^ (k - 4) : ℕ) :=
      mul_pos (pow_pos hkpos _) (pow_pos hc0 _)
    rw [log_mul hC₄.ne' (rpow_pos_of_pos hinner _).ne', log_rpow hinner,
      log_mul (pow_pos hkpos _).ne' (pow_pos hc0 _).ne', log_pow, log_pow]
    have hlogk : log (k : ℝ) ≤ (k : ℝ) := (log_le_sub_one_of_pos hkpos).trans (by linarith)
    have hkm4 : ((k - 4 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.sub_le k 4
    have h1 : (309 / 100 : ℝ) * (((k - 4 : ℕ) : ℝ) * log k) ≤ 4 * (k : ℝ) ^ 2 := by
      have hlognn : 0 ≤ log (k : ℝ) := log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
      nlinarith
    have h2 : (309 / 100 : ℝ) * (((2 ^ (k - 4) : ℕ) : ℝ) * log c₀) =
        (309 / 1600 : ℝ) * (2 : ℝ) ^ k * log c₀ := by
      rw [← mul_assoc, mul_comm (309 / 100 : ℝ), h2pow]
    linarith
  have hlog_rhs : log (c₀ ^ ((1 / 5 : ℝ) * (2 : ℝ) ^ k)) = (1 / 5 : ℝ) * (2 : ℝ) ^ k * log c₀ :=
    log_rpow hc0 _
  have h2kpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hsmall' : log C₄ + 4 * (k : ℝ) ^ 2 < (11 / 1600 : ℝ) * (2 : ℝ) ^ k * log c₀ := by
    have := (div_lt_iff₀ h2kpos).mp hsmall
    linarith
  have hlog_cmp : log (C₄ * ((k : ℝ) ^ (k - 4) * c₀ ^ (2 ^ (k - 4) : ℕ)) ^ (309 / 100 : ℝ)) ≤
      log (c₀ ^ ((1 / 5 : ℝ) * (2 : ℝ) ^ k)) := by
    rw [hlog_rhs]
    linarith
  have hpos_lhs : 0 < C₄ * ((k : ℝ) ^ (k - 4) * c₀ ^ (2 ^ (k - 4) : ℕ)) ^ (309 / 100 : ℝ) :=
    mul_pos hC₄ (rpow_pos_of_pos (mul_pos (pow_pos hkpos _) (pow_pos hc0 _)) _)
  exact (log_le_log_iff hpos_lhs (rpow_pos_of_pos hc0 _)).mp hlog_cmp

end Erdos148Upper

theorem OMA.solution : type_of% @Erdos148.erdos_148.variants.upper_bound := by
  refine ⟨fun _ => (0 : ℝ), Asymptotics.isLittleO_zero _ _, ?_⟩
  obtain ⟨C₄, hC₄, hF⟩ := Erdos148Upper.F_le_bound
  filter_upwards [Filter.eventually_ge_atTop 5,
    Erdos148Upper.tendsto_eventually_poly_le_exp C₄ hC₄] with k hk hbound
  simpa using (hF k hk).trans hbound
