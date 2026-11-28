import OMAStatements.S_oeis_a192205

/-!
Proof of coefficient growth limit for OEIS A192205:
Let M = 16 * sqrt 3 / 9, so M^2 = 256 / 27.
1. Lower bound: at z0 = (-1 + 2 * sqrt 2 * i) / 3, ||z0|| = 1 and ||P.eval z0|| = M,
   so M^n = ||(P^n).eval z0|| <= a n.
2. Unit-circle bound: for ||z|| = 1, P.eval z = (1 - z)^2 * (1 + z) gives
   ||P.eval z||^2 = 8 * (1 - z.re)^2 * (1 + z.re) <= 256 / 27 = M^2.
3. Upper bound via discrete Parseval at K = 3*n + 1 roots of unity:
   sum_i ||c_i||^2 = (1/K) sum_j ||(P^n).eval (omega^j)||^2 <= M^(2n),
   so Cauchy-Schwarz yields a n <= sqrt(3*n + 1) * M^n.
4. Squeeze theorem gives (a n)^(1/n) -> M.
-/

namespace OMA.P_oeis_a192205

open Polynomial

private noncomputable def M : ℝ := 16 * Real.sqrt 3 / 9

private lemma M_pos : 0 < M := by
  dsimp [M]
  positivity

private lemma M_sq : M ^ 2 = 256 / 27 := by
  dsimp [M]
  rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]
  norm_num

private lemma P_natDegree : OMA.S_oeis_a192205.P.natDegree ≤ 3 := by
  rw [OMA.S_oeis_a192205.P]
  have h1 : (1 - Polynomial.X - Polynomial.X ^ 2 : ℂ[X]).natDegree ≤ 2 := by
    refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
    · refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
      · simp
      · exact le_trans Polynomial.natDegree_X_le (by norm_num)
    · exact Polynomial.natDegree_X_pow_le 2
  refine le_trans (Polynomial.natDegree_add_le _ _) (max_le (le_trans h1 (by norm_num)) ?_)
  exact Polynomial.natDegree_X_pow_le 3

private lemma P_pow_eval_sum (n : ℕ) (z : ℂ) :
    (OMA.S_oeis_a192205.P ^ n).eval z =
      ∑ i ∈ Finset.range (3 * n + 1), (OMA.S_oeis_a192205.P ^ n).coeff i * z ^ i := by
  have hdeg : (OMA.S_oeis_a192205.P ^ n).natDegree < 3 * n + 1 :=
    lt_of_le_of_lt (le_trans Polynomial.natDegree_pow_le (Nat.mul_le_mul_left n P_natDegree))
      (by omega)
  exact Polynomial.eval_eq_sum_range' hdeg z

private lemma P_eval_factored (z : ℂ) :
    OMA.S_oeis_a192205.P.eval z = (1 - z) ^ 2 * (1 + z) := by
  simp [OMA.S_oeis_a192205.P]
  ring

private lemma mul_star_self_eq_normSq (z : ℂ) : z * star z = (Complex.normSq z : ℂ) := by
  apply Complex.ext
  · simp [Complex.normSq_apply]
  · simp; ring

private lemma a_lower (n : ℕ) : M ^ n ≤ OMA.S_oeis_a192205.a n := by
  let z0 : ℂ := ⟨-1 / 3, 2 * Real.sqrt 2 / 3⟩
  have hz0_sq : Complex.normSq z0 = 1 := by
    rw [Complex.normSq_apply]
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    dsimp [z0]
    linear_combination 4 / 9 * h2
  have hz0_norm : ‖z0‖ = 1 := by
    have hsq : ‖z0‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq, hz0_sq]
    nlinarith [norm_nonneg z0]
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h1m : Complex.normSq (1 - z0) = 8 / 3 := by
    rw [Complex.normSq_apply]
    dsimp [z0]
    linear_combination 4 / 9 * h2
  have h1p : Complex.normSq (1 + z0) = 4 / 3 := by
    rw [Complex.normSq_apply]
    dsimp [z0]
    linear_combination 4 / 9 * h2
  have hPz0_sq : ‖OMA.S_oeis_a192205.P.eval z0‖ ^ 2 = M ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, P_eval_factored, Complex.normSq_mul, sq, Complex.normSq_mul,
      h1m, h1p, M_sq]
    norm_num
  have hPz0 : ‖OMA.S_oeis_a192205.P.eval z0‖ = M := by
    nlinarith [norm_nonneg (OMA.S_oeis_a192205.P.eval z0), M_pos]
  calc M ^ n
      = ‖OMA.S_oeis_a192205.P.eval z0‖ ^ n := by rw [hPz0]
    _ = ‖(OMA.S_oeis_a192205.P ^ n).eval z0‖ := by rw [Polynomial.eval_pow, norm_pow]
    _ = ‖∑ i ∈ Finset.range (3 * n + 1), (OMA.S_oeis_a192205.P ^ n).coeff i * z0 ^ i‖ := by
        rw [P_pow_eval_sum]
    _ ≤ ∑ i ∈ Finset.range (3 * n + 1), ‖(OMA.S_oeis_a192205.P ^ n).coeff i * z0 ^ i‖ :=
        norm_sum_le _ _
    _ = OMA.S_oeis_a192205.a n := by
        simp only [OMA.S_oeis_a192205.a, norm_mul, norm_pow, hz0_norm, one_pow, mul_one]

private lemma P_eval_unit_circle {z : ℂ} (hz : ‖z‖ = 1) :
    ‖OMA.S_oeis_a192205.P.eval z‖ ≤ M := by
  have hz_sq : z.re * z.re + z.im * z.im = 1 := by
    have hns : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hz]; norm_num
    rw [Complex.normSq_apply] at hns
    exact hns
  have h1m : Complex.normSq (1 - z) = 2 - 2 * z.re := by
    rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
    linarith
  have h1p : Complex.normSq (1 + z) = 2 + 2 * z.re := by
    rw [Complex.normSq_apply]
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im]
    linarith
  have hle1 : z.re ≤ 1 := by nlinarith [sq_nonneg z.im]
  have hsq_le : ‖OMA.S_oeis_a192205.P.eval z‖ ^ 2 ≤ M ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, P_eval_factored, Complex.normSq_mul, sq, Complex.normSq_mul,
      h1m, h1p, M_sq]
    nlinarith [sq_nonneg (3 * (1 - z.re) - 4)]
  nlinarith [norm_nonneg (OMA.S_oeis_a192205.P.eval z), M_pos]

private lemma a_upper (n : ℕ) :
    OMA.S_oeis_a192205.a n ≤ Real.sqrt (3 * n + 1 : ℝ) * M ^ n := by
  let K : ℕ := 3 * n + 1
  have hK_pos : 0 < K := Nat.succ_pos _
  have hKR_pos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr hK_pos
  let ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / (K : ℂ))
  have hω_eq : ω = Complex.exp (↑(2 * Real.pi / (K : ℝ)) * Complex.I) := by
    dsimp [ω]
    congr 1
    push_cast
    ring
  have hω_norm : ‖ω‖ = 1 := by
    rw [hω_eq, Complex.norm_exp_ofReal_mul_I]
  have hω_star : ω * starRingEnd ℂ ω = 1 := by
    have hs := mul_star_self_eq_normSq ω
    rw [Complex.star_def, Complex.normSq_eq_norm_sq, hω_norm] at hs
    simpa using hs
  have hω_star' : starRingEnd ℂ ω * ω = 1 := by rw [mul_comm, hω_star]
  have hω_pow_K : ω ^ K = 1 := by
    dsimp [ω]
    rw [← Complex.exp_nat_mul]
    have hK_ne : (K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hK_pos)
    rw [show (K : ℂ) * (2 * ↑Real.pi * Complex.I / (K : ℂ)) = 2 * ↑Real.pi * Complex.I by
      field_simp [hK_ne]]
    exact Complex.exp_two_pi_mul_I
  have hω_prim : ∀ m : ℕ, 0 < m → m < K → ω ^ m ≠ 1 := by
    intro m hm0 hmK hpow
    dsimp [ω] at hpow
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff] at hpow
    rcases hpow with ⟨t, ht⟩
    have h2piI : (2 * ↑Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hK_ne : (K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hK_pos)
    have hdiv : ((m : ℂ) / (K : ℂ)) * (2 * ↑Real.pi * Complex.I) =
        (t : ℂ) * (2 * ↑Real.pi * Complex.I) := by
      calc ((m : ℂ) / (K : ℂ)) * (2 * ↑Real.pi * Complex.I)
          = (m : ℂ) * (2 * ↑Real.pi * Complex.I / (K : ℂ)) := by ring
        _ = (t : ℂ) * (2 * ↑Real.pi * Complex.I) := ht
    have hratC : (m : ℂ) / (K : ℂ) = (t : ℂ) := mul_right_cancel₀ h2piI hdiv
    have hratC' : (((m : ℝ) / (K : ℝ) : ℝ) : ℂ) = ((t : ℝ) : ℂ) := by
      simpa using hratC
    have hratR : (m : ℝ) / (K : ℝ) = (t : ℝ) := Complex.ofReal_inj.mp hratC'
    have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm0
    have hm_lt : (m : ℝ) < (K : ℝ) := Nat.cast_lt.mpr hmK
    have ht0 : (0 : ℝ) < (t : ℝ) := by rw [← hratR]; positivity
    have ht1 : (t : ℝ) < 1 := by rw [← hratR, div_lt_one hKR_pos]; exact hm_lt
    have ht0Z : (0 : ℤ) < t := by exact_mod_cast ht0
    have ht1Z : t < (1 : ℤ) := by exact_mod_cast ht1
    omega
  have h_ortho : ∀ i l : ℕ, i < K → l < K →
      (∑ j ∈ Finset.range K, (ω ^ j) ^ i * star ((ω ^ j) ^ l)) =
        if i = l then (K : ℂ) else 0 := by
    intro i l hi hl
    let ζ : ℂ := ω ^ i * (starRingEnd ℂ ω) ^ l
    have hterm : ∀ j : ℕ, (ω ^ j) ^ i * star ((ω ^ j) ^ l) = ζ ^ j := by
      intro j
      dsimp [ζ]
      rw [map_pow, map_pow, ← pow_mul, ← pow_mul,
        mul_comm j i, mul_comm j l, pow_mul, pow_mul, ← mul_pow]
    simp_rw [hterm]
    by_cases hil : i = l
    · have hζ1 : ζ = 1 := by
        dsimp [ζ]
        rw [hil, ← mul_pow, hω_star, one_pow]
      simp [hil, hζ1]
    · simp only [hil, ↓reduceIte]
      have hζ_ne : ζ ≠ 1 := by
        intro hζ1
        rcases lt_or_gt_of_ne hil with hlt | hgt
        · have hpow_l : ζ * ω ^ l = ω ^ l := by rw [hζ1, one_mul]
          have hpow_l' : ζ * ω ^ l = ω ^ i := by
            dsimp [ζ]
            rw [mul_assoc, ← mul_pow, hω_star', one_pow, mul_one]
          have heq : ω ^ i = ω ^ l := hpow_l'.symm.trans hpow_l
          have hdiff : ω ^ (l - i) = 1 := by
            calc ω ^ (l - i)
                = ω ^ (l - i) * (ω * starRingEnd ℂ ω) ^ i := by rw [hω_star, one_pow, mul_one]
              _ = (ω ^ (l - i) * ω ^ i) * (starRingEnd ℂ ω) ^ i := by rw [mul_pow]; ring
              _ = ω ^ l * (starRingEnd ℂ ω) ^ i := by
                  rw [← pow_add, Nat.sub_add_cancel (le_of_lt hlt)]
              _ = ω ^ i * (starRingEnd ℂ ω) ^ i := by rw [← heq]
              _ = (ω * starRingEnd ℂ ω) ^ i := by rw [← mul_pow]
              _ = 1 := by rw [hω_star, one_pow]
          exact hω_prim (l - i) (by omega) (by omega) hdiff
        · have hpow_l : ζ * ω ^ l = ω ^ l := by rw [hζ1, one_mul]
          have hpow_l' : ζ * ω ^ l = ω ^ i := by
            dsimp [ζ]
            rw [mul_assoc, ← mul_pow, hω_star', one_pow, mul_one]
          have heq : ω ^ i = ω ^ l := hpow_l'.symm.trans hpow_l
          have hdiff : ω ^ (i - l) = 1 := by
            calc ω ^ (i - l)
                = ω ^ (i - l) * (ω * starRingEnd ℂ ω) ^ l := by rw [hω_star, one_pow, mul_one]
              _ = (ω ^ (i - l) * ω ^ l) * (starRingEnd ℂ ω) ^ l := by rw [mul_pow]; ring
              _ = ω ^ i * (starRingEnd ℂ ω) ^ l := by
                  rw [← pow_add, Nat.sub_add_cancel (le_of_lt hgt)]
              _ = ω ^ l * (starRingEnd ℂ ω) ^ l := by rw [heq]
              _ = (ω * starRingEnd ℂ ω) ^ l := by rw [← mul_pow]
              _ = 1 := by rw [hω_star, one_pow]
          exact hω_prim (i - l) (by omega) (by omega) hdiff
      have hζK : ζ ^ K = 1 := by
        dsimp [ζ]
        rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm i K, mul_comm l K,
          pow_mul, pow_mul, hω_pow_K, one_pow, ← map_pow, hω_pow_K, map_one, one_pow, mul_one]
      rw [geom_sum_eq hζ_ne, hζK, sub_self, zero_div]
  let c := fun i : ℕ => (OMA.S_oeis_a192205.P ^ n).coeff i
  have hparsevalC :
      (∑ j ∈ Finset.range K,
          (OMA.S_oeis_a192205.P ^ n).eval (ω ^ j) *
            star ((OMA.S_oeis_a192205.P ^ n).eval (ω ^ j))) =
        (K : ℂ) * ∑ i ∈ Finset.range K, c i * star (c i) := by
    have heval : ∀ j : ℕ,
        (OMA.S_oeis_a192205.P ^ n).eval (ω ^ j) =
          ∑ i ∈ Finset.range K, c i * (ω ^ j) ^ i := fun j => P_pow_eval_sum n (ω ^ j)
    simp_rw [heval, star_sum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hswap :
        (∑ i ∈ Finset.range K, ∑ j ∈ Finset.range K, ∑ l ∈ Finset.range K,
            c i * (ω ^ j) ^ i * star (c l * (ω ^ j) ^ l)) =
          ∑ i ∈ Finset.range K, ∑ l ∈ Finset.range K,
            c i * star (c l) * ∑ j ∈ Finset.range K, (ω ^ j) ^ i * star ((ω ^ j) ^ l) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [star_mul']
      ring
    rw [hswap]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hiK : i < K := Finset.mem_range.mp hi
    have hinner :
        (∑ l ∈ Finset.range K,
            c i * star (c l) * ∑ j ∈ Finset.range K, (ω ^ j) ^ i * star ((ω ^ j) ^ l)) =
          ∑ l ∈ Finset.range K, if i = l then c i * star (c l) * (K : ℂ) else 0 := by
      refine Finset.sum_congr rfl (fun l hl => ?_)
      have hlK : l < K := Finset.mem_range.mp hl
      rw [h_ortho i l hiK hlK]
      split_ifs <;> ring
    rw [hinner, Finset.sum_eq_single i (fun l _ hli => by simp [Ne.symm hli]) (fun h => absurd hi h)]
    simp
    ring
  have hparsevalR :
      (K : ℝ) * ∑ i ∈ Finset.range K, ‖c i‖ ^ 2 =
        ∑ j ∈ Finset.range K, ‖(OMA.S_oeis_a192205.P ^ n).eval (ω ^ j)‖ ^ 2 := by
    have hC :
        (((K : ℝ) * ∑ i ∈ Finset.range K, ‖c i‖ ^ 2 : ℝ) : ℂ) =
          ((∑ j ∈ Finset.range K, ‖(OMA.S_oeis_a192205.P ^ n).eval (ω ^ j)‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_sum, Complex.ofReal_natCast]
      have hlhs : ∀ i : ℕ, ((‖c i‖ ^ 2 : ℝ) : ℂ) = c i * star (c i) := fun i => by
        rw [← Complex.normSq_eq_norm_sq, mul_star_self_eq_normSq]
      have hrhs : ∀ j : ℕ,
          ((‖(OMA.S_oeis_a192205.P ^ n).eval (ω ^ j)‖ ^ 2 : ℝ) : ℂ) =
            (OMA.S_oeis_a192205.P ^ n).eval (ω ^ j) *
              star ((OMA.S_oeis_a192205.P ^ n).eval (ω ^ j)) := fun j => by
        rw [← Complex.normSq_eq_norm_sq, mul_star_self_eq_normSq]
      simp_rw [hlhs, hrhs]
      exact hparsevalC.symm
    exact Complex.ofReal_inj.mp hC
  have hsum_eval :
      (∑ j ∈ Finset.range K, ‖(OMA.S_oeis_a192205.P ^ n).eval (ω ^ j)‖ ^ 2) ≤
        (K : ℝ) * (M ^ n) ^ 2 := by
    calc (∑ j ∈ Finset.range K, ‖(OMA.S_oeis_a192205.P ^ n).eval (ω ^ j)‖ ^ 2)
        ≤ ∑ _j ∈ Finset.range K, (M ^ n) ^ 2 := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          have hωj : ‖ω ^ j‖ = 1 := by rw [norm_pow, hω_norm, one_pow]
          have hle := pow_le_pow_left₀ (norm_nonneg _) (P_eval_unit_circle hωj) n
          rw [← norm_pow, ← Polynomial.eval_pow] at hle
          exact pow_le_pow_left₀ (norm_nonneg _) hle 2
      _ = (K : ℝ) * (M ^ n) ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hsum_sq : (∑ i ∈ Finset.range K, ‖c i‖ ^ 2) ≤ (M ^ n) ^ 2 := by
    have hmul : (K : ℝ) * (∑ i ∈ Finset.range K, ‖c i‖ ^ 2) ≤ (K : ℝ) * (M ^ n) ^ 2 := by
      rw [hparsevalR]
      exact hsum_eval
    exact le_of_mul_le_mul_left hmul hKR_pos
  have hcs :
      (OMA.S_oeis_a192205.a n) ^ 2 ≤ (K : ℝ) * ∑ i ∈ Finset.range K, ‖c i‖ ^ 2 := by
    have hcs0 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range K)
      (fun _ => (1 : ℝ)) (fun i => ‖c i‖)
    simpa [OMA.S_oeis_a192205.a, c, K] using hcs0
  have ha_sq : (OMA.S_oeis_a192205.a n) ^ 2 ≤ (K : ℝ) * (M ^ n) ^ 2 :=
    le_trans hcs (mul_le_mul_of_nonneg_left hsum_sq (le_of_lt hKR_pos))
  have ha_sqrt := Real.le_sqrt_of_sq_le ha_sq
  rw [Real.sqrt_mul (le_of_lt hKR_pos), Real.sqrt_sq (pow_nonneg (le_of_lt M_pos) n)] at ha_sqrt
  simpa [K] using ha_sqrt

end OMA.P_oeis_a192205

theorem OMA.solution : type_of% @OMA.S_oeis_a192205.main := by
  have hlog_div :
      Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h3n1_top :
      Filter.Tendsto (fun n : ℕ => (3 * (n : ℝ) + 1 : ℝ)) Filter.atTop Filter.atTop := by
    have h1 : Filter.Tendsto (fun n : ℕ => 3 * (n : ℝ)) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
    exact Filter.Tendsto.atTop_add h1 tendsto_const_nhds
  have hlog_comp :
      Filter.Tendsto (fun n : ℕ => Real.log (3 * (n : ℝ) + 1) / (3 * (n : ℝ) + 1))
        Filter.atTop (nhds 0) :=
    hlog_div.comp h3n1_top
  have hrat :
      Filter.Tendsto (fun n : ℕ => (3 * (n : ℝ) + 1) / (2 * (n : ℝ)))
        Filter.atTop (nhds (3 / 2 : ℝ)) := by
    have hinv : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hlin :
        Filter.Tendsto (fun n : ℕ => (3 : ℝ) / 2 + (1 : ℝ) / 2 * ((1 : ℝ) / (n : ℝ)))
          Filter.atTop (nhds (3 / 2 : ℝ)) := by
      simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)
    refine hlin.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp [hn_ne]
  have hexp_arg :
      Filter.Tendsto
        (fun n : ℕ => Real.log (3 * (n : ℝ) + 1) * (1 / (2 * (n : ℝ))))
        Filter.atTop (nhds 0) := by
    have hprod := hrat.mul hlog_comp
    rw [mul_zero] at hprod
    refine hprod.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have h3n1_ne : (3 * (n : ℝ) + 1 : ℝ) ≠ 0 := by positivity
    field_simp [h3n1_ne]
  have hroot_lim :
      Filter.Tendsto (fun n : ℕ => (3 * (n : ℝ) + 1 : ℝ) ^ (1 / (2 * (n : ℝ))))
        Filter.atTop (nhds 1) := by
    have hexp := Real.continuous_exp.continuousAt.tendsto.comp hexp_arg
    rw [Function.comp_def, Real.exp_zero] at hexp
    refine hexp.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n _
    rw [Real.rpow_def_of_pos (by positivity)]
  have hlo : Filter.Tendsto (fun _ : ℕ => OMA.P_oeis_a192205.M)
      Filter.atTop (nhds (16 * Real.sqrt 3 / 9)) :=
    tendsto_const_nhds
  have hhi : Filter.Tendsto
      (fun n : ℕ => (3 * (n : ℝ) + 1 : ℝ) ^ (1 / (2 * (n : ℝ))) * OMA.P_oeis_a192205.M)
      Filter.atTop (nhds (16 * Real.sqrt 3 / 9)) := by
    simpa [OMA.P_oeis_a192205.M] using hroot_lim.mul tendsto_const_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have hle := OMA.P_oeis_a192205.a_lower n
    have hpow := Real.rpow_le_rpow (pow_nonneg (le_of_lt OMA.P_oeis_a192205.M_pos) n) hle
      (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ))
    rw [← Real.rpow_natCast OMA.P_oeis_a192205.M,
      ← Real.rpow_mul (le_of_lt OMA.P_oeis_a192205.M_pos),
      mul_one_div_cancel (ne_of_gt hn_pos), Real.rpow_one] at hpow
    exact hpow
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have ha_nonneg : 0 ≤ OMA.S_oeis_a192205.a n :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have hle := OMA.P_oeis_a192205.a_upper n
    have hpow := Real.rpow_le_rpow ha_nonneg hle (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ))
    have h3n1_nonneg : (0 : ℝ) ≤ 3 * (n : ℝ) + 1 := by positivity
    rw [Real.mul_rpow (Real.sqrt_nonneg _) (pow_nonneg (le_of_lt OMA.P_oeis_a192205.M_pos) n),
      Real.sqrt_eq_rpow, ← Real.rpow_mul h3n1_nonneg,
      ← Real.rpow_natCast OMA.P_oeis_a192205.M,
      ← Real.rpow_mul (le_of_lt OMA.P_oeis_a192205.M_pos),
      mul_one_div_cancel (ne_of_gt hn_pos), Real.rpow_one] at hpow
    have hexp_eq : (1 / 2 : ℝ) * (1 / (n : ℝ)) = 1 / (2 * (n : ℝ)) := by ring
    rw [hexp_eq] at hpow
    exact hpow
