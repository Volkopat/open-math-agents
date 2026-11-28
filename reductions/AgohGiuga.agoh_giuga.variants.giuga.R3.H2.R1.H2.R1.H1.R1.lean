import OMAReductions.R_AgohGiuga_agoh_giuga_variants_giuga_R3_H2_R1_H2_R1

/-! The dyadic Mertens bound and a smaller sieve reduce the compatible-prime cardinality bound. -/

open scoped BigOperators Interval

namespace OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R3_H2_R1_H2_R1_H1_R1

private theorem sum_interval_split (f : ℕ → ℝ) {u v w : ℕ}
    (huv : u ≤ v) (hvw : v ≤ w) :
    (∑ p ∈ (Finset.Ioc u w).filter Nat.Prime, f p) =
      (∑ p ∈ (Finset.Ioc u v).filter Nat.Prime, f p) +
        ∑ p ∈ (Finset.Ioc v w).filter Nat.Prime, f p := by
  have hd : Disjoint (Finset.Ioc u v) (Finset.Ioc v w) :=
    Finset.Ioc_disjoint_Ioc_of_le le_rfl
  rw [← Finset.Ioc_union_Ioc_eq_Ioc huv hvw, Finset.filter_union,
    Finset.sum_union (hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]

private theorem sum_prime_blocks (f : ℕ → ℝ) (t : ℕ → ℕ) (ht : Monotone t) (k : ℕ) :
    (∑ j ∈ Finset.range k, ∑ p ∈ (Finset.Ioc (t j) (t (j + 1))).filter Nat.Prime, f p) =
      ∑ p ∈ (Finset.Ioc (t 0) (t k)).filter Nat.Prime, f p := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, sum_interval_split f (ht (Nat.zero_le k)) (ht (by omega : k ≤ k + 1))]

/-- With nonnegative decreasing weights, inequalities on all prefix sums
imply the inequality on the weighted sums. -/
private theorem weighted_prefix_le (a b w : ℕ → ℝ) (k : ℕ)
    (hp : ∀ j ≤ k, (∑ i ∈ Finset.range j, a i) ≤ ∑ i ∈ Finset.range j, b i)
    (hw : ∀ i, w (i + 1) ≤ w i) (hn : 0 ≤ w k) :
    (∑ i ∈ Finset.range k, a i * w i) ≤ ∑ i ∈ Finset.range k, b i * w i := by
  let d i := a i - b i
  have hneg (j : ℕ) (hj : j ≤ k) : (∑ i ∈ Finset.range j, d i) ≤ 0 := by
    dsimp only [d]
    rw [Finset.sum_sub_distrib]
    exact sub_nonpos.mpr (hp j hj)
  have hsum (j : ℕ) (hj : j ≤ k) :
      (∑ i ∈ Finset.range j, d i * w i) ≤ (∑ i ∈ Finset.range j, d i) * w j := by
    induction j with
    | zero => simp
    | succ j ih =>
      calc
        _ = (∑ i ∈ Finset.range j, d i * w i) + d j * w j := by rw [Finset.sum_range_succ]
        _ ≤ (∑ i ∈ Finset.range j, d i) * w j + d j * w j :=
          add_le_add (ih (by omega)) le_rfl
        _ = (∑ i ∈ Finset.range (j + 1), d i) * w j := by
          rw [Finset.sum_range_succ, add_mul]
        _ ≤ _ := mul_le_mul_of_nonpos_left (hw j) (hneg (j + 1) hj)
  have h := (hsum k le_rfl).trans (mul_nonpos_of_nonpos_of_nonneg (hneg k le_rfl) hn)
  dsimp only [d] at h
  simp only [sub_mul, Finset.sum_sub_distrib] at h
  exact sub_nonpos.mp h

private theorem dyadic_weighted_upper (j : ℕ) (hj : 18 ≤ j) (hj' : j ≤ 34) :
    (∑ p ∈ (Finset.Ioc 0 (2^j)).filter Nat.Prime,
      Real.log (p : ℝ) / (p : ℝ)) ≤ (j : ℝ) * Real.log 2 := by
  classical
  let N : ℕ := 2 ^ j
  let P := (Finset.Ioc 0 N).filter Nat.Prime
  let D : Finset ℕ := {4, 8, 16, 9}
  let g (d : ℕ) : ℝ := ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ)
  let L (p : ℕ) : ℝ := Real.log (p : ℝ)
  have hN : 2^18 ≤ N := Nat.pow_le_pow_right (by norm_num) hj
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (pow_pos Nat.zero_lt_two j : 0 < (2 : ℕ) ^ j)
  have hNge : (262144 : ℝ) ≤ N := by exact_mod_cast hN
  have hfloor (d : ℕ) : (N : ℝ) / (d : ℝ) ≤ ((N / d : ℕ) : ℝ) + 1 := by
    have hh := (Nat.lt_floor_add_one ((N : ℝ) / (d : ℝ))).le
    rwa [Nat.floor_div_natCast, Nat.floor_natCast] at hh
  have hlog : Real.log (N : ℝ) = (j : ℝ) * Real.log 2 := by
    simp only [N, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  have hlog2 : Real.log 2 < (7:ℝ)/10 := by linarith only [Real.log_two_lt_d9]
  have hlog3lo : (1:ℝ) < Real.log 3 := by linarith only [Real.log_three_gt_d9]
  have hlog3hi : Real.log 3 < 2 := by linarith only [Real.log_three_lt_d9]
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow] <;> norm_num
  have htheta : (∑ p ∈ P, L p) ≤ Real.log 4 * N := by
    simpa only [Chebyshev.theta, Nat.floor_natCast, P, L] using
      Chebyshev.theta_le_log4_mul_x hNpos.le
  have hprime : (N : ℝ) * (∑ p ∈ P, L p / p) ≤ (∑ p ∈ P, g p) + ∑ p ∈ P, L p := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hp
    have hpP := (Finset.mem_filter.mp hp).2
    dsimp only [g, L]
    rw [ArithmeticFunction.vonMangoldt_apply_prime hpP]
    calc
      _ = Real.log (p : ℝ) * ((N : ℝ) / (p : ℝ)) := by ring
      _ ≤ Real.log (p : ℝ) * (((N / p : ℕ) : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left (hfloor p) (Real.log_nonneg (by exact_mod_cast hpP.one_le))
      _ = _ := by ring
  have hl₄ : ArithmeticFunction.vonMangoldt 4 = Real.log 2 := by
    change ArithmeticFunction.vonMangoldt (2^2) = _
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by decide), ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two] <;> norm_num
  have hl₈ : ArithmeticFunction.vonMangoldt 8 = Real.log 2 := by
    change ArithmeticFunction.vonMangoldt (2^3) = _
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by decide), ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two] <;> norm_num
  have hl₁₆ : ArithmeticFunction.vonMangoldt 16 = Real.log 2 := by
    change ArithmeticFunction.vonMangoldt (2^4) = _
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by decide), ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two] <;> norm_num
  have hl₉ : ArithmeticFunction.vonMangoldt 9 = Real.log 3 := by
    change ArithmeticFunction.vonMangoldt (3^2) = _
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by decide), ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three] <;> norm_num
  have hpower (d : ℕ) (v : ℝ) (hv : 0 ≤ v)
      (h : ArithmeticFunction.vonMangoldt d = v) :
      v * ((N : ℝ) / d - 1) ≤ g d := by
    change _ ≤ ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ)
    rw [h]
    exact mul_le_mul_of_nonneg_left (by linarith only [hfloor d]) hv
  have hpowers : (7 * (N : ℝ) / 16 - 3) * Real.log 2 +
      ((N : ℝ) / 9 - 1) * Real.log 3 ≤ ∑ p ∈ D, g p := by
    have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h4 := hpower 4 (Real.log 2) h2 hl₄
    have h8 := hpower 8 (Real.log 2) h2 hl₈
    have h16 := hpower 16 (Real.log 2) h2 hl₁₆
    have h9 := hpower 9 (Real.log 3) (by linarith only [hlog3lo]) hl₉
    simp [D]
    norm_num at h4 h8 h16 h9
    nlinarith only [h4, h8, h16, h9]
  have hd : Disjoint P D := by
    apply Finset.disjoint_left.mpr
    intro d h₁ h₂
    have hp := (Finset.mem_filter.mp h₁).2
    simp [D] at h₂
    rcases h₂ with hd | hd | hd | hd
    · exact (by decide : ¬ Nat.Prime 4) (hd ▸ hp)
    · exact (by decide : ¬ Nat.Prime 8) (hd ▸ hp)
    · exact (by decide : ¬ Nat.Prime 16) (hd ▸ hp)
    · exact (by decide : ¬ Nat.Prime 9) (hd ▸ hp)
  have hTogether : (∑ p ∈ P, g p) + ∑ p ∈ D, g p ≤ ∑ d ∈ Finset.Ioc 0 N, g d := by
    rw [← Finset.sum_union hd]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      rcases Finset.mem_union.mp hp with hp | hp
      · exact (Finset.mem_filter.mp hp).1
      · simp [D] at hp
        exact Finset.mem_Ioc.mpr (by omega)
    · intro p _ _
      exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
  have hIdentity : (∑ d ∈ Finset.Ioc 0 N, g d) = ∑ d ∈ Finset.Ioc 0 N, L d := by
    simpa only [g, L, ArithmeticFunction.vonMangoldt_mul_zeta, ArithmeticFunction.log_apply] using
      (ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum ArithmeticFunction.vonMangoldt N).symm
  have hlogfact : (∑ d ∈ Finset.Ioc 0 N, L d) ≤
      (N : ℝ) * Real.log N - N + 1 + Real.log N := by
    have hsub : (Finset.Ioc 0 N : Finset ℕ) = insert N (Finset.Ico 1 N) := by
      ext d
      simp only [Finset.mem_Ioc, Finset.mem_insert, Finset.mem_Ico]
      omega
    rw [hsub, Finset.sum_insert (by simp)]
    have hm : MonotoneOn Real.log (Set.Icc (1 : ℝ) N) := by
      intro a ha b _ hab
      exact Real.log_le_log (by linarith [ha.1]) hab
    have hmCast : MonotoneOn Real.log (Set.Icc ((1 : ℕ) : ℝ) (N : ℝ)) := by
      simpa only [Nat.cast_one] using hm
    have hi := MonotoneOn.sum_le_integral_Ico (f := Real.log)
      (show 1 ≤ N by omega) hmCast
    simp only [Nat.cast_one] at hi
    change (∑ d ∈ Finset.Ico 1 N, L d) ≤ ∫ t in (1 : ℝ)..(N : ℝ), Real.log t at hi
    rw [integral_log] at hi
    simp only [Real.log_one, mul_zero, zero_sub] at hi
    dsimp only [L]
    linarith only [hi]
  have hmain : (N : ℝ) * ((∑ p ∈ P, L p / p) - Real.log N) ≤
      (N : ℝ) * ((25 / 16) * Real.log 2 - 1 - Real.log 3 / 9) +
        (1 + Real.log N + 3 * Real.log 2 + Real.log 3) := by
    rw [hlog4] at htheta
    nlinarith only [hprime, htheta, hpowers, hTogether, hIdentity, hlogfact]
  have hneg : (25 / 16 : ℝ) * Real.log 2 - 1 - Real.log 3 / 9 ≤ -(5/288) := by
    linarith only [hlog2, hlog3lo]
  have hjR : (j : ℝ) ≤ 34 := by exact_mod_cast hj'
  have hlogNlt : Real.log (N : ℝ) ≤ 24 := by
    rw [hlog]
    calc
      _ ≤ (34 : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_right hjR (by positivity)
      _ ≤ _ := by linarith only [hlog2]
  have hmain' := hmain.trans (add_le_add (mul_le_mul_of_nonneg_left hneg hNpos.le) le_rfl)
  have hfinal : (N : ℝ) * ((∑ p ∈ P, L p / p) - Real.log N) ≤ 0 := by
    linarith only [hmain', hNge, hlogNlt, hlog2, hlog3hi]
  have hdone := nonpos_of_mul_nonpos_right hfinal hNpos
  have hres := sub_nonpos.mp hdone
  rw [hlog] at hres
  exact hres

private theorem middle_bound
    (hlo : 15 * Real.log 2 ≤ ∑ p ∈ (Finset.Ioc 0 (2^17)).filter Nat.Prime,
      Real.log (p : ℝ) / (p : ℝ))
    (hhi : ∀ j : ℕ, 18 ≤ j → j ≤ 34 →
      (∑ p ∈ (Finset.Ioc 0 (2^j)).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)) ≤
        (j : ℝ) * Real.log 2) :
    (∑ p ∈ (Finset.Ioc (2^17) (2^34)).filter Nat.Prime, (p : ℝ)⁻¹) ≤ 5 / 6 := by
  let f (p : ℕ) : ℝ := Real.log (p : ℝ) / (p : ℝ)
  let t (j : ℕ) : ℕ := 2 ^ (17 + j)
  have ht : Monotone t := fun _ _ h => Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let a (j : ℕ) : ℝ :=
    (∑ p ∈ (Finset.Ioc (t j) (t (j + 1))).filter Nat.Prime, f p) / Real.log 2
  let b (j : ℕ) : ℝ := if j = 0 then 3 else 1
  let w (j : ℕ) : ℝ := (17 + (j : ℝ))⁻¹
  have hb (k : ℕ) : (∑ j ∈ Finset.range k, b j) = if k = 0 then 0 else (k : ℝ) + 2 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      by_cases hk : k = 0
      · subst k
        norm_num [b]
      · simp [b, hk, Nat.cast_succ]
        ring
  have hp (k : ℕ) (hk : k ≤ 17) :
      (∑ j ∈ Finset.range k, a j) ≤ ∑ j ∈ Finset.range k, b j := by
    by_cases hz : k = 0
    · simp [hz]
    rw [hb, if_neg hz]
    dsimp only [a]
    rw [← Finset.sum_div, sum_prime_blocks f t ht]
    apply (div_le_iff₀ hlog).mpr
    have hs := sum_interval_split f (show 0 ≤ t 0 from Nat.zero_le _) (ht (Nat.zero_le k))
    have hu := hhi (17 + k) (by omega) (by omega)
    have hl : 15 * Real.log 2 ≤ ∑ p ∈ (Finset.Ioc 0 (t 0)).filter Nat.Prime, f p := hlo
    change (∑ p ∈ (Finset.Ioc 0 (t k)).filter Nat.Prime, f p) ≤
      ((17 + k : ℕ) : ℝ) * Real.log 2 at hu
    push_cast at hu
    nlinarith only [hs, hu, hl]
  have hw (i : ℕ) : w (i + 1) ≤ w i := by
    dsimp only [w]
    apply inv_anti₀ (by positivity)
    push_cast
    linarith
  have hbin (j : ℕ) :
      (∑ p ∈ (Finset.Ioc (t j) (t (j + 1))).filter Nat.Prime, (p : ℝ)⁻¹) ≤ a j * w j := by
    dsimp only [a]
    rw [Finset.sum_div, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro p hp
    have hj : (0 : ℝ) < 17 + (j : ℝ) := by positivity
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.pos
    have ht0 : (0 : ℝ) < (t j : ℝ) := by dsimp only [t]; positivity
    have htp : (t j : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1.le
    have htl : Real.log (t j : ℝ) = (17 + (j : ℝ)) * Real.log 2 := by
      simp only [t, Nat.cast_pow, Real.log_pow, Nat.cast_add, Nat.cast_ofNat]
    have hpl := Real.log_le_log ht0 htp
    rw [htl] at hpl
    dsimp only [w, f]
    rw [← div_eq_mul_inv ((Real.log (p : ℝ) / (p : ℝ)) / Real.log 2)]
    refine (le_div_iff₀ hj).mpr ((le_div_iff₀ hlog).mpr ?_)
    calc
      _ = ((17 + (j : ℝ)) * Real.log 2) / (p : ℝ) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hpl hp0.le
  calc
    _ = ∑ j ∈ Finset.range 17,
        ∑ p ∈ (Finset.Ioc (t j) (t (j + 1))).filter Nat.Prime, (p : ℝ)⁻¹ :=
      (sum_prime_blocks (fun p => (p : ℝ)⁻¹) t ht 17).symm
    _ ≤ ∑ j ∈ Finset.range 17, a j * w j := Finset.sum_le_sum fun j _ => hbin j
    _ ≤ ∑ j ∈ Finset.range 17, b j * w j := weighted_prefix_le a b w 17 hp hw (by positivity)
    _ ≤ _ := by norm_num [b, w, Finset.sum_range_succ]

/-- A finite reciprocal-sum bound for compatible odd primes up to 2^17. -/
def H1 : Prop :=
  ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ Odd p ∧ p ≤ 2^17) →
    (∀ p ∈ S, ∀ q ∈ S, ¬ (p ∣ q - 1)) →
    ∑ p ∈ S, (p : ℝ)⁻¹ ≤ 111 / 100

/-- A lower bound for the logarithmically weighted prime sum at 2^17. -/
def H2 : Prop :=
  15 * Real.log 2 ≤
    ∑ p ∈ (Finset.Ioc 0 (2^17)).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)

theorem main : H1 → H2 → OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R3_H2_R1_H2_R1.H1 := by
  classical
  intro hsmall hlo S hprime hcompat n hn hdiv hsum
  by_contra! hc
  let f (p : ℕ) : ℝ := (p : ℝ)⁻¹
  have hscale : (n : ℝ) * (∑ p ∈ S, f p) = ((∑ p ∈ S, n / p : ℕ) : ℝ) := by
    rw [Finset.mul_sum, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro p hp
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hprime p hp).1.ne_zero
    have hnat := Nat.div_mul_cancel (hdiv p hp)
    have hreal : (n / p : ℕ) * p = n := hnat
    have hcast : ((n / p : ℕ) : ℝ) * (p : ℝ) = (n : ℝ) := by exact_mod_cast hreal
    rw [show n * f p = (n : ℝ) / (p : ℝ) by rfl]
    exact ((eq_div_iff hp0).mpr hcast).symm
  have hpositive : 2 < ∑ p ∈ S, f p := by
    have hcast : (2 : ℝ) * (n : ℝ) < ((∑ p ∈ S, n / p : ℕ) : ℝ) := by
      exact_mod_cast hsum
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [← hscale, mul_comm (2 : ℝ)] at hcast
    exact (mul_lt_mul_iff_right₀ hnR).mp hcast
  let small := S.filter (fun p => p ≤ 2^17)
  let rest := S.filter (fun p => 2^17 < p)
  let mid := rest.filter (fun p => p ≤ 2^34)
  let large := rest.filter (fun p => 2^34 < p)
  have hpart : (∑ p ∈ small, f p) + (∑ p ∈ rest, f p) = ∑ p ∈ S, f p := by
    simpa only [small, rest, not_le] using
      Finset.sum_filter_add_sum_filter_not S (fun p => p ≤ 2^17) f
  have hrest : (∑ p ∈ mid, f p) + (∑ p ∈ large, f p) = ∑ p ∈ rest, f p := by
    simpa only [mid, large, not_le] using
      Finset.sum_filter_add_sum_filter_not rest (fun p => p ≤ 2^34) f
  have hsmall' : (∑ p ∈ small, f p) ≤ 111 / 100 := by
    apply hsmall small
    · intro p hp
      obtain ⟨hpS, hpY⟩ := Finset.mem_filter.mp hp
      exact ⟨(hprime p hpS).1, (hprime p hpS).2, hpY⟩
    · exact fun p hp q hq => hcompat p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1
  have hmid : (∑ p ∈ mid, f p) ≤ 5 / 6 := by
    apply le_trans _ (middle_bound hlo dyadic_weighted_upper)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpR, hpX⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpS, hpY⟩ := Finset.mem_filter.mp hpR
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hpY, hpX⟩, (hprime p hpS).1⟩
    · intro p _ _
      dsimp only [f]
      positivity
  have hlarge : (∑ p ∈ large, f p) ≤ (887038346 : ℝ) / 2^34 := by
    have hcard : large.card ≤ 887038346 := by
      have h₁ : large.card ≤ rest.card := Finset.card_filter_le _ _
      have h₂ : rest.card ≤ S.card := Finset.card_filter_le _ _
      omega
    calc
      _ ≤ ∑ _p ∈ large, ((2 : ℝ)^34)⁻¹ := by
        apply Finset.sum_le_sum
        intro p hp
        have hpX : (2^34 : ℕ) ≤ p := (Finset.mem_filter.mp hp).2.le
        dsimp only [f]
        exact inv_anti₀ (by positivity) (by exact_mod_cast hpX)
      _ = (large.card : ℝ) / 2^34 := by simp [div_eq_mul_inv]
      _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
  norm_num at hlarge
  linarith only [hpositive, hpart, hrest, hsmall', hmid, hlarge]

end OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R3_H2_R1_H2_R1_H1_R1
