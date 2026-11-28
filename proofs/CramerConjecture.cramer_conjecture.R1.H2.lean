import OMAReductions.R_CramerConjecture_cramer_conjecture_R1
import Mathlib
-- Credit: @LordMike

open Filter Real Asymptotics ArithmeticFunction Finset
open scoped Topology

lemma qs_space {m n j x h : ℕ} (hmn : m < n) (hj : 1 ≤ j) (hx : x ≤ n^(j+1))
    (hh : (2*h)^2 ≤ x) : m^(j+1) + 2*h ≤ n^(j+1) := by
  have h1 : m^(j+1) + n^j ≤ n^(j+1) := by
    have : m^j ≤ n^j := Nat.pow_le_pow_left hmn.le j
    calc m^(j+1) + n^j = m * m^j + n^j := by ring
      _ ≤ m * n^j + n^j := by gcongr
      _ = (m+1) * n^j := by ring
      _ ≤ n * n^j := Nat.mul_le_mul_right _ hmn
      _ = n^(j+1) := by ring
  have h2 : n ≤ n^j := by
    have : n ≠ 0 := by omega
    simpa using Nat.pow_le_pow_right (Nat.pos_of_ne_zero this) hj
  have h3 : n^(j+1) ≤ n^j * n^j := by
    calc n^(j+1) = n^j * n := by ring
      _ ≤ n^j * n^j := Nat.mul_le_mul_left _ h2
  have h4 : 2*h ≤ n^j := by
    by_contra hc
    push_neg at hc
    have : n^j * n^j < (2*h)*(2*h) := Nat.mul_self_lt_mul_self hc
    nlinarith
  omega

lemma qs_unique {m n j x h : ℕ} (hj : 1 ≤ j) (hh : (2*h)^2 ≤ x)
    (ha : x ≤ m^(j+1)) (ha' : m^(j+1) < x + 2*h)
    (hb : x ≤ n^(j+1)) (hb' : n^(j+1) < x + 2*h) : m = n := by
  rcases lt_trichotomy m n with h1 | h1 | h1
  · have := qs_space h1 hj hb hh
    omega
  · exact h1
  · have := qs_space h1 hj ha hh
    omega

lemma qs_decomp {d : ℕ} (hd : Λ d ≠ 0) (hnp : ¬ d.Prime) :
    ∃ p, p.Prime ∧ 2 ≤ d.factorization d.minFac ∧ p ^ (d.factorization d.minFac) = d := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (vonMangoldt_ne_zero_iff.mp hd)
  have hp' : p.Prime := Nat.prime_iff.mpr hp
  have hk0 : k ≠ 0 := hk.ne'
  have hg : (p ^ k).factorization (p ^ k).minFac = k := by
    rw [Nat.Prime.pow_minFac hp' hk0]
    simp [Nat.factorization_pow, hp'.factorization]
  refine ⟨p, hp', ?_, ?_⟩
  · rw [hg]
    by_contra hc
    have : k = 1 := by omega
    subst this
    exact hnp (by simpa using hp')
  · rw [hg]

lemma qs_sum (x h : ℕ) (hh : (2*h)^2 ≤ x) :
    ∑ d ∈ (Ico x (x + 2*h)).filter (fun d => ¬ d.Prime), (Λ d : ℝ)
      ≤ Real.log ((x + 2*h : ℕ) : ℝ) * (1 + Real.log (Nat.log 2 (x + 2*h) : ℕ)) := by
  set N := x + 2*h with hN
  set K := Nat.log 2 N with hK
  set L := Real.log (N : ℝ) with hL
  have hL0 : 0 ≤ L := Real.log_natCast_nonneg N
  set s := (Ico x N).filter (fun d => ¬ d.Prime) with hs
  rw [← Finset.sum_filter_ne_zero]
  set s' := s.filter (fun d => (Λ d : ℝ) ≠ 0) with hs'
  let g : ℕ → ℕ := fun d => d.factorization d.minFac
  have hmem : ∀ d ∈ s', d ∈ Ico x N ∧ ∃ p, p.Prime ∧ 2 ≤ g d ∧ p ^ g d = d := by
    intro d hd
    simp only [hs', hs, mem_filter] at hd
    obtain ⟨⟨h1, h2⟩, h3⟩ := hd
    exact ⟨h1, qs_decomp (by exact_mod_cast h3) h2⟩
  have hmaps : ∀ d ∈ s', g d ∈ Icc 2 K := by
    intro d hd
    obtain ⟨h1, p, hp, h2, h3⟩ := hmem d hd
    rw [mem_Icc]
    refine ⟨h2, Nat.le_log_of_pow_le (by norm_num) ?_⟩
    have h4 : 2 ^ g d ≤ p ^ g d := Nat.pow_le_pow_left hp.two_le _
    have := (mem_Ico.mp h1).2
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ k ∈ Icc 2 K, ∑ d ∈ s' with g d = k, (Λ d : ℝ) ≤ L / k := by
    intro k hk
    have hk2 : 2 ≤ k := (mem_Icc.mp hk).1
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hcard : (s'.filter (fun d => g d = k)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      rw [mem_filter] at ha hb
      obtain ⟨ha1, pa, hpa, -, ha3⟩ := hmem a ha.1
      obtain ⟨hb1, pb, hpb, -, hb3⟩ := hmem b hb.1
      rw [ha.2] at ha3
      rw [hb.2] at hb3
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have ha4 := mem_Ico.mp ha1
      have hb4 := mem_Ico.mp hb1
      rw [← ha3, ← hb3] at *
      have := qs_unique (m := pa) (n := pb) (j := j) (by omega) hh ha4.1 ha4.2 hb4.1 hb4.2
      rw [this]
    have hterm : ∀ d ∈ s'.filter (fun d => g d = k), (Λ d : ℝ) ≤ L / k := by
      intro d hd
      rw [mem_filter] at hd
      obtain ⟨h1, p, hp, -, h3⟩ := hmem d hd.1
      rw [hd.2] at h3
      have hk0 : k ≠ 0 := by omega
      have hdN : d < N := (mem_Ico.mp h1).2
      have hdpos : 0 < d := by
        rw [← h3]; exact pow_pos hp.pos _
      have hlog : Real.log (d : ℝ) ≤ L := Real.log_le_log (by exact_mod_cast hdpos)
        (by exact_mod_cast hdN.le)
      have hlogd : Real.log (d : ℝ) = k * Real.log p := by
        rw [← h3]; push_cast; rw [Real.log_pow]
      rw [← h3, vonMangoldt_apply_pow hk0, vonMangoldt_apply_prime hp, le_div_iff₀ hkpos]
      rw [hlogd] at hlog
      nlinarith
    calc ∑ d ∈ s' with g d = k, (Λ d : ℝ)
        ≤ (s'.filter (fun d => g d = k)).card • (L / k) := Finset.sum_le_card_nsmul _ _ _ hterm
      _ ≤ 1 • (L / k) := nsmul_le_nsmul_left (by positivity) hcard
      _ = L / k := one_nsmul _
  calc ∑ k ∈ Icc 2 K, ∑ d ∈ s' with g d = k, (Λ d : ℝ)
      ≤ ∑ k ∈ Icc 2 K, L / (k : ℝ) := Finset.sum_le_sum hfib
    _ = L * ∑ k ∈ Icc 2 K, ((k : ℝ))⁻¹ := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by rw [div_eq_mul_inv]
    _ ≤ L * ∑ k ∈ Icc 1 K, ((k : ℝ))⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ hL0
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk; rw [mem_Icc] at hk ⊢; omega
        · intros; positivity
    _ ≤ L * (1 + Real.log K) := by
        apply mul_le_mul_of_nonneg_left _ hL0
        have := harmonic_le_one_add_log K
        simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at this
        exact this

lemma qs_little : (fun t : ℝ => 2 * t * (1 + Real.log (4 * t))) =o[atTop] fun t : ℝ => t ^ 2 := by
  have h1 : (fun t : ℝ => Real.log (4 * t)) =o[atTop] fun t : ℝ => t := by
    have h := Real.isLittleO_log_id_atTop.comp_tendsto
      (tendsto_id.const_mul_atTop (show (0 : ℝ) < 4 by norm_num))
    refine h.trans_isBigO ?_
    exact Asymptotics.isBigO_const_mul_self 4 _ _
  have h2 : (fun t : ℝ => 1 + Real.log (4 * t)) =o[atTop] fun t : ℝ => t :=
    (isLittleO_const_id_atTop (1 : ℝ)).add h1
  have h3 : (fun t : ℝ => 2 * t) =O[atTop] fun t : ℝ => t :=
    Asymptotics.isBigO_const_mul_self 2 _ _
  have := h3.mul_isLittleO h2
  refine this.congr_right ?_
  intro t; ring

lemma qs_eventually {C : ℝ} (hC : 0 < C) :
    ∀ᶠ x : ℕ in atTop, ((2 * ⌈C * (Real.log (x : ℝ)) ^ 2⌉₊ : ℕ))^2 ≤ x := by
  have hlit := (Real.isLittleO_pow_log_id_atTop (n := 4))
  have hpos : (0 : ℝ) < 4 * C ^ 2 + 8 * C + 4 := by positivity
  have hb := hlit.bound (show (0 : ℝ) < 1 / (4 * C ^ 2 + 8 * C + 4) by positivity)
  have hb' := tendsto_natCast_atTop_atTop (R := ℝ) |>.eventually hb
  have hb'' := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_ge_atTop (Real.exp 1))
  filter_upwards [hb', hb'', eventually_ge_atTop 1] with x hx hx1 hx2
  have ht : 1 ≤ Real.log (x : ℝ) := by
    rw [Real.le_log_iff_exp_le (by exact_mod_cast hx2)]; exact hx1
  set t := Real.log (x : ℝ)
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hn : ‖t ^ 4‖ ≤ 1 / (4 * C ^ 2 + 8 * C + 4) * ‖(x : ℝ)‖ := hx
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg hx0] at hn
  have hceil : (⌈C * t ^ 2⌉₊ : ℝ) < C * t ^ 2 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have h2 : ((2 * ⌈C * t ^ 2⌉₊ : ℕ) : ℝ) ≤ 2 * C * t ^ 2 + 2 := by push_cast; linarith
  have h2' : (0 : ℝ) ≤ ((2 * ⌈C * t ^ 2⌉₊ : ℕ) : ℝ) := Nat.cast_nonneg _
  have h3 : (((2 * ⌈C * t ^ 2⌉₊ : ℕ) : ℝ)) ^ 2 ≤ (2 * C * t ^ 2 + 2) ^ 2 :=
    pow_le_pow_left₀ h2' h2 2
  have ht2 : 1 ≤ t ^ 2 := by nlinarith
  have ht4 : t ^ 2 ≤ t ^ 4 := by nlinarith
  have h4 : (2 * C * t ^ 2 + 2) ^ 2 ≤ (4 * C ^ 2 + 8 * C + 4) * t ^ 4 := by
    nlinarith [mul_pos hC hC, mul_nonneg hC.le (sub_nonneg.mpr ht4), sub_nonneg.mpr ht2,
      mul_nonneg hC.le (sub_nonneg.mpr ht2)]
  have h5 : (4 * C ^ 2 + 8 * C + 4) * t ^ 4 ≤ x := by
    have := mul_le_mul_of_nonneg_left hn hpos.le
    rw [← mul_assoc, mul_one_div_cancel hpos.ne', one_mul] at this
    exact this
  exact_mod_cast h3.trans (h4.trans h5)

theorem OMA.solution : OMA.R_CramerConjecture_cramer_conjecture_R1.H2 := by
  intro C hC
  set B : ℕ → ℝ := fun x => 2 * Real.log (x : ℝ) * (1 + Real.log (4 * Real.log (x : ℝ))) with hB
  have hBo : B =o[atTop] fun x : ℕ => (Real.log (x : ℝ)) ^ 2 :=
    qs_little.comp_tendsto (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  refine IsBigO.trans_isLittleO ?_ hBo
  refine IsBigO.of_bound 1 ?_
  filter_upwards [qs_eventually hC, eventually_ge_atTop 3,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (Real.exp 1))]
    with x hx hx3 hxe
  set h := ⌈C * (Real.log (x : ℝ)) ^ 2⌉₊ with hh
  have ht : 1 ≤ Real.log (x : ℝ) := by
    rw [Real.le_log_iff_exp_le (by exact_mod_cast (show 0 < x by omega))]; exact hxe
  set t := Real.log (x : ℝ) with htdef
  have hS := qs_sum x h (by simpa using hx)
  have h2h : 2 * h ≤ x := by
    have : 2 * h ≤ (2 * h) ^ 2 := by nlinarith [Nat.zero_le (2 * h)]
    omega
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hNx : ((x + 2 * h : ℕ) : ℝ) ≤ (x : ℝ) ^ 2 := by
    have : x + 2 * h ≤ x ^ 2 := by nlinarith
    exact_mod_cast this
  have hNpos : (0 : ℝ) < ((x + 2 * h : ℕ) : ℝ) := by positivity
  have hL : Real.log ((x + 2 * h : ℕ) : ℝ) ≤ 2 * t := by
    have := Real.log_le_log hNpos hNx
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  have hK : ((Nat.log 2 (x + 2 * h) : ℕ) : ℝ) ≤ 4 * t := by
    have h1 : 2 ^ (Nat.log 2 (x + 2 * h)) ≤ x + 2 * h := Nat.pow_log_le_self 2 (by omega)
    have h2 : ((2 : ℝ)) ^ (Nat.log 2 (x + 2 * h)) ≤ ((x + 2 * h : ℕ) : ℝ) := by
      exact_mod_cast h1
    have h3 := Real.log_le_log (by positivity) h2
    rw [Real.log_pow] at h3
    have := Real.log_two_gt_d9
    nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.log 2 (x + 2 * h))]
  have hlogK : Real.log ((Nat.log 2 (x + 2 * h) : ℕ) : ℝ) ≤ Real.log (4 * t) := by
    rcases Nat.eq_zero_or_pos (Nat.log 2 (x + 2 * h)) with h0 | h0
    · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg (by linarith)
    · exact Real.log_le_log (by exact_mod_cast h0) hK
  have hlog4 : 0 ≤ Real.log (4 * t) := Real.log_nonneg (by linarith)
  have hSnn : 0 ≤ ∑ d ∈ (Ico x (x + 2 * h)).filter (fun d => ¬ d.Prime), (Λ d : ℝ) :=
    sum_nonneg fun _ _ => vonMangoldt_nonneg
  have hBnn : 0 ≤ B x := by
    simp only [hB]; positivity
  rw [Real.norm_of_nonneg hSnn, one_mul, Real.norm_of_nonneg hBnn]
  refine hS.trans ?_
  have hc0 : 0 ≤ 1 + Real.log ((Nat.log 2 (x + 2 * h) : ℕ) : ℝ) := by
    have := Real.log_natCast_nonneg (Nat.log 2 (x + 2 * h)); linarith
  have hc : 1 + Real.log ((Nat.log 2 (x + 2 * h) : ℕ) : ℝ) ≤ 1 + Real.log (4 * t) := by
    linarith
  calc _ ≤ (2 * t) * (1 + Real.log (4 * t)) :=
        mul_le_mul hL hc hc0 (by linarith)
    _ = _ := rfl
