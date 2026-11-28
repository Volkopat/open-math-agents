import OMAReductions.R_Erdos257_erdos_257_R1

-- Step Erdos257.erdos_257.R1.H2: hypothesis H2 of reduction Erdos257.erdos_257.R1
-- Credit: @nnkostov

/-!
We prove the averaging lemma of Erdős (1968): if `∑ 1/a` converges over `A`,
then for any `ε > 0` we choose `K ≥ 1` so the tail of `∑ 1/a` above `K` is `< ε/4`.
Given `M ≥ 1`, we choose `L ≥ K` so the tail above `L` is `< ε/(4M)`, and `T > L`
large enough that `L + 4 < ε T / 4`. Averaging over `N = M (t + 1)` for `t < T`,
residues `M (t + 1) mod n` cycle through cosets of `gcd(M, n) Z / n Z`, bounding the
average remainder by `1/n + 1/T` for `K < n ≤ M T`, while `n > M T` contribute at most
`4 * 2^(MT) * (1/2)^n` whose total over `n > M T` is at most `4`. Thus the total sum
over `t < T` is `< ε T`, yielding some `t < T` with remainder sum `< ε`.
-/

private noncomputable def rem (n N : ℕ) : ℝ :=
  ((2 : ℝ) ^ (N % n) - 1) / ((2 : ℝ) ^ n - 1)

private lemma sum_range_mul (f : ℕ → ℝ) (Q q : ℕ) :
    ∑ t ∈ Finset.range (Q * q), f t =
      ∑ k ∈ Finset.range Q, ∑ r ∈ Finset.range q, f (k * q + r) := by
  induction Q with
  | zero => simp
  | succ Q ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, Finset.sum_range_succ, ih]

private lemma sum_rem_period_le (M n k : ℕ) (hn : 0 < n) :
    ∑ r ∈ Finset.range (n / Nat.gcd M n),
      rem n (M * (k * (n / Nat.gcd M n) + r + 1)) ≤ 1 / (Nat.gcd M n : ℝ) := by
  set g := Nat.gcd M n
  set q := n / g
  set m' := M / g
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right M hn
  have hgq : g * q = n := Nat.mul_div_cancel' (Nat.gcd_dvd_right M n)
  have hgm : g * m' = M := Nat.mul_div_cancel' (Nat.gcd_dvd_left M n)
  have hq_pos : 0 < q := Nat.div_pos (Nat.le_of_dvd hn (Nat.gcd_dvd_right M n)) hg_pos
  have hcop : Nat.Coprime m' q := Nat.coprime_div_gcd_div_gcd hg_pos
  let φ : ℕ → ℕ := fun r => (m' * (k * q + r + 1)) % q
  let h : ℕ → ℝ := fun j => ((2 : ℝ) ^ (g * j) - 1) / ((2 : ℝ) ^ n - 1)
  have hrew : ∀ r, rem n (M * (k * q + r + 1)) = h (φ r) := by
    intro r
    dsimp [rem, h, φ]
    have hmul : M * (k * q + r + 1) = g * (m' * (k * q + r + 1)) := by
      rw [← hgm, mul_assoc]
    have hmod : (M * (k * q + r + 1)) % n = g * ((m' * (k * q + r + 1)) % q) := by
      conv_lhs => rw [hmul, ← hgq]
      exact Nat.mul_mod_mul_left g _ q
    rw [hmod]
  have hinj : Set.InjOn φ (Finset.range q : Set ℕ) := by
    intro r₁ hr₁ r₂ hr₂ heq
    have hr₁' : r₁ < q := Finset.mem_range.mp (Finset.mem_coe.mp hr₁)
    have hr₂' : r₂ < q := Finset.mem_range.mp (Finset.mem_coe.mp hr₂)
    have hmod : m' * (k * q + r₁ + 1) ≡ m' * (k * q + r₂ + 1) [MOD q] := heq
    have hc := Nat.ModEq.cancel_left_of_coprime hcop.symm hmod
    have hc1 := Nat.ModEq.add_right_cancel' 1 hc
    have hc2 : r₁ ≡ r₂ [MOD q] := by
      rw [add_assoc, add_assoc] at hmod
      exact Nat.ModEq.add_left_cancel' (k * q) hc1
    change r₁ % q = r₂ % q at hc2
    rwa [Nat.mod_eq_of_lt hr₁', Nat.mod_eq_of_lt hr₂'] at hc2
  have hsub : (Finset.range q).image φ ⊆ Finset.range q := by
    intro j hj
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr (Nat.mod_lt _ hq_pos)
  have h2n : (2 : ℝ) ≤ (2 : ℝ) ^ n := OMA.R_Erdos257_erdos_257_R1.two_le_two_pow hn
  have h2g : (2 : ℝ) ≤ (2 : ℝ) ^ g := OMA.R_Erdos257_erdos_257_R1.two_le_two_pow hg_pos
  have hden_pos : (0 : ℝ) < (2 : ℝ) ^ n - 1 := by linarith
  have hden_g_pos : (0 : ℝ) < (2 : ℝ) ^ g - 1 := by linarith
  have hh_nonneg : ∀ j, 0 ≤ h j := by
    intro j
    apply div_nonneg
    · have : (1 : ℝ) ≤ (2 : ℝ) ^ (g * j) := one_le_pow₀ (by norm_num)
      linarith
    · exact hden_pos.le
  calc
    ∑ r ∈ Finset.range q, rem n (M * (k * q + r + 1))
        = ∑ r ∈ Finset.range q, h (φ r) := Finset.sum_congr rfl fun r _ => hrew r
    _ = ∑ j ∈ (Finset.range q).image φ, h j := (Finset.sum_image fun r₁ hr₁ r₂ hr₂ => hinj hr₁ hr₂).symm
    _ ≤ ∑ j ∈ Finset.range q, h j := Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => hh_nonneg j
    _ ≤ ∑ j ∈ Finset.range q, (2 : ℝ) ^ (g * j) / ((2 : ℝ) ^ n - 1) := by
      refine Finset.sum_le_sum fun j _ => ?_
      dsimp [h]
      exact div_le_div_of_nonneg_right (by linarith) hden_pos.le
    _ = (∑ j ∈ Finset.range q, ((2 : ℝ) ^ g) ^ j) / ((2 : ℝ) ^ n - 1) := by
      rw [← Finset.sum_div]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [pow_mul]
    _ = 1 / ((2 : ℝ) ^ g - 1) := by
      have hgeom : (∑ j ∈ Finset.range q, ((2 : ℝ) ^ g) ^ j) * ((2 : ℝ) ^ g - 1) =
          (2 : ℝ) ^ n - 1 := by
        rw [geom_sum_mul, ← pow_mul, hgq]
      rw [div_eq_div_iff hden_pos.ne' hden_g_pos.ne', one_mul, hgeom]
    _ ≤ 1 / (g : ℝ) := by
      have hg_lt : g < 2 ^ g := Nat.lt_two_pow_self
      have hg_le : (g : ℝ) ≤ (2 : ℝ) ^ g - 1 := by
        have : (g : ℝ) + 1 ≤ (2 : ℝ) ^ g := by exact_mod_cast hg_lt
        linarith
      exact one_div_le_one_div_of_le (by exact_mod_cast hg_pos) hg_le

private lemma sum_rem_le (M n T : ℕ) (hn : 0 < n) :
    ∑ t ∈ Finset.range T, rem n (M * (t + 1)) ≤ (T : ℝ) / (n : ℝ) + 1 := by
  set g := Nat.gcd M n
  set q := n / g
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right M hn
  have hgq : g * q = n := Nat.mul_div_cancel' (Nat.gcd_dvd_right M n)
  have hq_pos : 0 < q := Nat.div_pos (Nat.le_of_dvd hn (Nat.gcd_dvd_right M n)) hg_pos
  set Q := T / q + 1
  have hTle : T ≤ Q * q := by
    dsimp [Q]
    rw [Nat.add_mul, one_mul]
    have hdiv := Nat.div_add_mod T q
    have hmod := Nat.mod_lt T hq_pos
    rw [mul_comm q (T / q)] at hdiv
    omega
  have hnonneg : ∀ t, 0 ≤ rem n (M * (t + 1)) := fun t =>
    OMA.R_Erdos257_erdos_257_R1.rem_nonneg n (M * (t + 1))
  calc
    ∑ t ∈ Finset.range T, rem n (M * (t + 1))
        ≤ ∑ t ∈ Finset.range (Q * q), rem n (M * (t + 1)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hTle) fun t _ _ => hnonneg t
    _ = ∑ k ∈ Finset.range Q, ∑ r ∈ Finset.range q, rem n (M * (k * q + r + 1)) := by
      simpa only [add_assoc] using sum_range_mul (fun t => rem n (M * (t + 1))) Q q
    _ ≤ ∑ _k ∈ Finset.range Q, (1 / (g : ℝ)) :=
      Finset.sum_le_sum fun k _ => sum_rem_period_le M n k hn
    _ = (Q : ℝ) / (g : ℝ) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one_div]
    _ = ((T / q : ℕ) : ℝ) / (g : ℝ) + 1 / (g : ℝ) := by
      dsimp [Q]
      push_cast
      ring
    _ ≤ (T : ℝ) / (q : ℝ) / (g : ℝ) + 1 := by
      have hg_ge1 : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg_pos
      have hdiv_le : ((T / q : ℕ) : ℝ) ≤ (T : ℝ) / (q : ℝ) := Nat.cast_div_le
      have hg_nn : (0 : ℝ) ≤ (g : ℝ) := by positivity
      have h1 : ((T / q : ℕ) : ℝ) / (g : ℝ) ≤ (T : ℝ) / (q : ℝ) / (g : ℝ) :=
        div_le_div_of_nonneg_right hdiv_le hg_nn
      have h2 : 1 / (g : ℝ) ≤ 1 := div_le_one_of_le₀ hg_ge1 hg_nn
      linarith
    _ = (T : ℝ) / (n : ℝ) + 1 := by
      rw [div_div, mul_comm (q : ℝ) (g : ℝ)]
      have hgn_r : (g : ℝ) * (q : ℝ) = (n : ℝ) := by exact_mod_cast hgq
      rw [hgn_r]

private lemma sum_rem_large_n_le (M T n : ℕ) (hM : 0 < M) (hn : M * T < n) :
    ∑ t ∈ Finset.range T, rem n (M * (t + 1)) ≤
      4 * (2 : ℝ) ^ (M * T) * ((1 : ℝ) / 2) ^ n := by
  have hn_pos : 0 < n := by omega
  have h2n : (2 : ℝ) ≤ (2 : ℝ) ^ n := OMA.R_Erdos257_erdos_257_R1.two_le_two_pow hn_pos
  have hden_pos : (0 : ℝ) < (2 : ℝ) ^ n - 1 := by linarith
  have hterm : ∀ t ∈ Finset.range T,
      rem n (M * (t + 1)) ≤ (2 : ℝ) ^ (M * (t + 1)) / ((2 : ℝ) ^ n - 1) := by
    intro t ht
    have ht_lt : t < T := Finset.mem_range.mp ht
    have hlt_n : M * (t + 1) < n := by
      calc
        M * (t + 1) ≤ M * T := Nat.mul_le_mul_left M ht_lt
        _ < n := hn
    dsimp [rem]
    rw [Nat.mod_eq_of_lt hlt_n]
    exact div_le_div_of_nonneg_right (by linarith) hden_pos.le
  have hsum_pow : ∑ t ∈ Finset.range T, (2 : ℝ) ^ (M * (t + 1)) ≤ 2 * (2 : ℝ) ^ (M * T) := by
    have h2M : (2 : ℝ) ≤ (2 : ℝ) ^ M := OMA.R_Erdos257_erdos_257_R1.two_le_two_pow hM
    have h2M_pos : (0 : ℝ) < (2 : ℝ) ^ M - 1 := by linarith
    have hgeom_nn : 0 ≤ ∑ t ∈ Finset.range T, ((2 : ℝ) ^ M) ^ t :=
      Finset.sum_nonneg fun t _ => by positivity
    calc
      ∑ t ∈ Finset.range T, (2 : ℝ) ^ (M * (t + 1))
          = ∑ t ∈ Finset.range T, (2 : ℝ) ^ M * ((2 : ℝ) ^ M) ^ t := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [mul_add, mul_one, pow_add, pow_mul, mul_comm]
      _ = (2 : ℝ) ^ M * ∑ t ∈ Finset.range T, ((2 : ℝ) ^ M) ^ t := (Finset.mul_sum _ _ _).symm
      _ ≤ (2 * ((2 : ℝ) ^ M - 1)) * ∑ t ∈ Finset.range T, ((2 : ℝ) ^ M) ^ t :=
        mul_le_mul_of_nonneg_right (by linarith) hgeom_nn
      _ = 2 * ((∑ t ∈ Finset.range T, ((2 : ℝ) ^ M) ^ t) * ((2 : ℝ) ^ M - 1)) := by ring
      _ = 2 * (((2 : ℝ) ^ M) ^ T - 1) := by rw [geom_sum_mul]
      _ ≤ 2 * (2 : ℝ) ^ (M * T) := by
        rw [← pow_mul]
        linarith
  have hinv : 1 / ((2 : ℝ) ^ n - 1) ≤ 2 * ((1 : ℝ) / 2) ^ n := by
    have hp : ((1 : ℝ) / 2) ^ n * (2 : ℝ) ^ n = 1 := by
      rw [← mul_pow]
      norm_num
    have hx : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ n := by positivity
    rw [div_le_iff₀ hden_pos]
    nlinarith [mul_nonneg hx (by linarith : (0 : ℝ) ≤ (2 : ℝ) ^ n - 2)]
  calc
    ∑ t ∈ Finset.range T, rem n (M * (t + 1))
        ≤ ∑ t ∈ Finset.range T, (2 : ℝ) ^ (M * (t + 1)) / ((2 : ℝ) ^ n - 1) :=
      Finset.sum_le_sum hterm
    _ = (∑ t ∈ Finset.range T, (2 : ℝ) ^ (M * (t + 1))) * (1 / ((2 : ℝ) ^ n - 1)) := by
      rw [← Finset.sum_div, div_eq_mul_one_div]
    _ ≤ (2 * (2 : ℝ) ^ (M * T)) * (2 * ((1 : ℝ) / 2) ^ n) :=
      mul_le_mul hsum_pow hinv (by positivity) (by positivity)
    _ = 4 * (2 : ℝ) ^ (M * T) * ((1 : ℝ) / 2) ^ n := by ring

private lemma tsum_tail_half_pow (N₀ : ℕ) :
    ∑' n : ℕ, (if N₀ < n then ((1 : ℝ) / 2) ^ n else 0) = 2 * ((1 : ℝ) / 2) ^ (N₀ + 1) := by
  let f : ℕ → ℝ := fun n => ((1 : ℝ) / 2) ^ n
  have hf : Summable f := summable_geometric_two
  have hf1 : Summable (fun n => if N₀ < n then f n else 0) :=
    Summable.of_nonneg_of_le
      (fun n => by split_ifs <;> positivity)
      (fun n => by split_ifs <;> [exact le_rfl; positivity])
      hf
  have hf2 : Summable (fun n => if n < N₀ + 1 then f n else 0) :=
    Summable.of_nonneg_of_le
      (fun n => by split_ifs <;> positivity)
      (fun n => by split_ifs <;> [exact le_rfl; positivity])
      hf
  have hpt : ∀ n, (if N₀ < n then f n else 0) + (if n < N₀ + 1 then f n else 0) = f n := by
    intro n
    by_cases h : N₀ < n <;> simp [h, show (n < N₀ + 1) ↔ ¬ N₀ < n by omega]
  have hsum_add : (∑' n, (if N₀ < n then f n else 0)) + ∑' n, (if n < N₀ + 1 then f n else 0) =
      ∑' n, f n := by
    rw [← hf1.tsum_add hf2]
    exact tsum_congr hpt
  have hfin : ∑' n, (if n < N₀ + 1 then f n else 0) = ∑ n ∈ Finset.range (N₀ + 1), f n := by
    rw [tsum_eq_sum (s := Finset.range (N₀ + 1))]
    · refine Finset.sum_congr rfl fun n hn => ?_
      rw [if_pos (Finset.mem_range.mp hn)]
    · intro n hn
      rw [Finset.mem_range] at hn
      exact if_neg hn
  have hnat := hf.sum_add_tsum_nat_add (N₀ + 1)
  have htail_eq : ∑' n, (if N₀ < n then f n else 0) = ∑' j, f (j + (N₀ + 1)) := by
    linarith
  rw [htail_eq]
  have hpow : ∀ j, f (j + (N₀ + 1)) = f j * ((1 : ℝ) / 2) ^ (N₀ + 1) := by
    intro j
    dsimp [f]
    rw [pow_add]
  simp_rw [hpow]
  rw [tsum_mul_right]
  have hgeom : ∑' j, f j = 2 := tsum_geometric_two
  rw [hgeom]

private lemma exists_tail_lt (A : Set ℕ) (hA : Summable (fun a : A => 1 / (a.1 : ℝ)))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℕ, 1 ≤ K ∧ ∑' a : A, (if K < a.1 then 1 / (a.1 : ℝ) else 0) < δ := by
  classical
  have hev := hA.hasSum.eventually (Ioi_mem_nhds (sub_lt_self (∑' a : A, 1 / (a.1 : ℝ)) hδ))
  obtain ⟨s, hs⟩ := hev.exists
  set K := max 1 (s.sup fun a => a.1)
  refine ⟨K, le_max_left 1 _, ?_⟩
  have h1 : Summable (fun a : A => if K < a.1 then 1 / (a.1 : ℝ) else 0) :=
    Summable.of_nonneg_of_le
      (fun a => by split_ifs <;> positivity)
      (fun a => by split_ifs <;> [exact le_rfl; positivity])
      hA
  have h2 : Summable (fun a : A => if a ∈ s then 1 / (a.1 : ℝ) else 0) :=
    Summable.of_nonneg_of_le
      (fun a => by split_ifs <;> positivity)
      (fun a => by split_ifs <;> [exact le_rfl; positivity])
      hA
  have hpt : ∀ a : A, (if K < a.1 then 1 / (a.1 : ℝ) else 0) +
      (if a ∈ s then 1 / (a.1 : ℝ) else 0) ≤ 1 / (a.1 : ℝ) := by
    intro a
    by_cases ha : a ∈ s
    · have hle : a.1 ≤ K := (Finset.le_sup ha).trans (le_max_right 1 _)
      have hnlt : ¬ K < a.1 := not_lt.mpr hle
      simp [ha, hnlt]
    · simp only [ha, ↓reduceIte, add_zero]
      split_ifs <;> [exact le_rfl; positivity]
  have hle_sum : (∑' a : A, if K < a.1 then 1 / (a.1 : ℝ) else 0) +
      ∑' a : A, (if a ∈ s then 1 / (a.1 : ℝ) else 0) ≤ ∑' a : A, 1 / (a.1 : ℝ) := by
    rw [← h1.tsum_add h2]
    exact (h1.add h2).tsum_le_tsum hpt hA
  have hfin : ∑' a : A, (if a ∈ s then 1 / (a.1 : ℝ) else 0) = ∑ a ∈ s, 1 / (a.1 : ℝ) := by
    rw [tsum_eq_sum (s := s)]
    · refine Finset.sum_congr rfl fun a ha => ?_
      rw [if_pos ha]
    · intro a ha
      exact if_neg ha
  linarith

theorem OMA.solution : OMA.R_Erdos257_erdos_257_R1.H2 := by
  intro A hA ε hε
  classical
  obtain ⟨K, hK1, hK⟩ := exists_tail_lt A hA (ε / 4) (by positivity)
  refine ⟨K, ?_⟩
  intro M hM
  obtain ⟨L₀, _, hL₀⟩ := exists_tail_lt A hA (ε / (4 * M)) (by positivity)
  set L := max K L₀
  have hKL : K ≤ L := le_max_left K L₀
  have hL0L : L₀ ≤ L := le_max_right K L₀
  have hL_tail : ∑' a : A, (if L < a.1 then 1 / (a.1 : ℝ) else 0) < ε / (4 * M) := by
    have hs1 : Summable (fun a : A => if L < a.1 then 1 / (a.1 : ℝ) else 0) :=
      Summable.of_nonneg_of_le
        (fun a => by split_ifs <;> positivity)
        (fun a => by split_ifs <;> [exact le_rfl; positivity])
        hA
    have hs2 : Summable (fun a : A => if L₀ < a.1 then 1 / (a.1 : ℝ) else 0) :=
      Summable.of_nonneg_of_le
        (fun a => by split_ifs <;> positivity)
        (fun a => by split_ifs <;> [exact le_rfl; positivity])
        hA
    have hpt : ∀ a : A, (if L < a.1 then 1 / (a.1 : ℝ) else 0) ≤
        if L₀ < a.1 then 1 / (a.1 : ℝ) else 0 := by
      intro a
      split_ifs with ha1 ha2
      · exact le_rfl
      · exfalso; exact ha2 (lt_of_le_of_lt hL0L ha1)
      · positivity
      · exact le_rfl
    exact lt_of_le_of_lt (hs1.tsum_le_tsum hpt hs2) hL₀
  obtain ⟨T₀, hT₀⟩ := exists_nat_gt ((4 * ((L : ℝ) + 4)) / ε)
  set T := max (L + 1) T₀
  have hT_pos : 0 < T := by omega
  have hLT : L < T := by omega
  have hLMT : L < M * T := by
    have h1 : T ≤ M * T := Nat.le_mul_of_pos_left T hM
    omega
  have hKMT : K < M * T := lt_of_le_of_lt hKL hLMT
  let F : ℕ → ℝ := fun t => ∑' a : A, (if K < a.1 then rem a.1 (M * (t + 1)) else 0)
  have hF_summable : ∀ t, Summable (fun a : A => if K < a.1 then rem a.1 (M * (t + 1)) else 0) := by
    intro t
    exact Summable.of_nonneg_of_le
      (fun a => by split_ifs <;> [exact OMA.R_Erdos257_erdos_257_R1.rem_nonneg _ _; exact le_rfl])
      (fun a => by split_ifs <;> [exact le_rfl; exact OMA.R_Erdos257_erdos_257_R1.rem_nonneg _ _])
      (OMA.R_Erdos257_erdos_257_R1.summable_rem A (M * (t + 1)))
  have hswap : ∑ t ∈ Finset.range T, F t =
      ∑' a : A, (if K < a.1 then ∑ t ∈ Finset.range T, rem a.1 (M * (t + 1)) else 0) := by
    have aux : ∀ k : ℕ, ∑ t ∈ Finset.range k, F t =
        ∑' a : A, ∑ t ∈ Finset.range k, (if K < a.1 then rem a.1 (M * (t + 1)) else 0) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        have hs1 : Summable (fun a : A => ∑ t ∈ Finset.range k,
            (if K < a.1 then rem a.1 (M * (t + 1)) else 0)) :=
          summable_sum fun t _ => hF_summable t
        rw [← hs1.tsum_add (hF_summable k)]
        refine tsum_congr fun a => ?_
        rw [Finset.sum_range_succ]
    rw [aux T]
    refine tsum_congr fun a => ?_
    by_cases ha : K < a.1 <;> simp [ha]
  let g_mid : A → ℝ := fun a =>
    if K < a.1 ∧ a.1 ≤ M * T then ∑ t ∈ Finset.range T, rem a.1 (M * (t + 1)) else 0
  let g_tail : A → ℝ := fun a =>
    if M * T < a.1 then ∑ t ∈ Finset.range T, rem a.1 (M * (t + 1)) else 0
  have hg_all : Summable (fun a : A =>
      if K < a.1 then ∑ t ∈ Finset.range T, rem a.1 (M * (t + 1)) else 0) := by
    have h1 : Summable (fun a : A => ∑ t ∈ Finset.range T,
        (if K < a.1 then rem a.1 (M * (t + 1)) else 0)) :=
      summable_sum fun t _ => hF_summable t
    refine h1.congr fun a => ?_
    by_cases ha : K < a.1 <;> simp [ha]
  have hg_nn : ∀ a : A, 0 ≤ if K < a.1 then ∑ t ∈ Finset.range T, rem a.1 (M * (t + 1)) else 0 := by
    intro a
    split_ifs
    · exact Finset.sum_nonneg fun t _ => OMA.R_Erdos257_erdos_257_R1.rem_nonneg _ _
    · exact le_rfl
  have hg_mid_summ : Summable g_mid := by
    refine Summable.of_nonneg_of_le (fun a => ?_) (fun a => ?_) hg_all
    · dsimp [g_mid]; split_ifs
      · exact Finset.sum_nonneg fun t _ => OMA.R_Erdos257_erdos_257_R1.rem_nonneg _ _
      · exact le_rfl
    · dsimp [g_mid]
      by_cases h1 : K < a.1 ∧ a.1 ≤ M * T
      · rw [if_pos h1, if_pos h1.1]
      · rw [if_neg h1]
        exact hg_nn a
  have hg_tail_summ : Summable g_tail := by
    refine Summable.of_nonneg_of_le (fun a => ?_) (fun a => ?_) hg_all
    · dsimp [g_tail]; split_ifs
      · exact Finset.sum_nonneg fun t _ => OMA.R_Erdos257_erdos_257_R1.rem_nonneg _ _
      · exact le_rfl
    · dsimp [g_tail]
      by_cases h1 : M * T < a.1
      · rw [if_pos h1, if_pos (lt_trans hKMT h1)]
      · rw [if_neg h1]
        exact hg_nn a
  have hsplit : ∑ t ∈ Finset.range T, F t = ∑' a : A, g_mid a + ∑' a : A, g_tail a := by
    rw [hswap, ← hg_mid_summ.tsum_add hg_tail_summ]
    refine tsum_congr fun a => ?_
    dsimp [g_mid, g_tail]
    by_cases h1 : K < a.1 <;> by_cases h2 : a.1 ≤ M * T
    · have h3 : ¬ M * T < a.1 := not_lt.mpr h2
      simp [h1, h2, h3]
    · have h3 : M * T < a.1 := lt_of_not_ge h2
      simp [h1, h2, h3]
    · have h3 : ¬ M * T < a.1 := not_lt.mpr h2
      simp [h1, h3]
    · have h3 : ¬ M * T < a.1 := fun h => h1 (lt_trans hKMT h)
      simp [h1, h3]
  have hK_summ : Summable (fun a : A => if K < a.1 then 1 / (a.1 : ℝ) else 0) :=
    Summable.of_nonneg_of_le
      (fun a => by split_ifs <;> positivity)
      (fun a => by split_ifs <;> [exact le_rfl; positivity])
      hA
  have hL_summ : Summable (fun a : A => if L < a.1 then 1 / (a.1 : ℝ) else 0) :=
    Summable.of_nonneg_of_le
      (fun a => by split_ifs <;> positivity)
      (fun a => by split_ifs <;> [exact le_rfl; positivity])
      hA
  have ht1_summ : Summable (fun a : A => (T : ℝ) * (if K < a.1 then 1 / (a.1 : ℝ) else 0)) :=
    hK_summ.mul_left _
  have ht3_summ : Summable (fun a : A => ((M : ℝ) * (T : ℝ)) * (if L < a.1 then 1 / (a.1 : ℝ) else 0)) :=
    hL_summ.mul_left _
  let t2_nat : ℕ → ℝ := fun n => if K < n ∧ n ≤ L then (1 : ℝ) else 0
  have ht2_has : HasSum t2_nat (∑ n ∈ Finset.Ioc K L, t2_nat n) :=
    hasSum_sum_of_ne_finset_zero fun n hn => by
      dsimp [t2_nat]
      rw [Finset.mem_Ioc] at hn
      exact if_neg hn
  have ht2_nat_summ : Summable t2_nat := ht2_has.summable
  have ht2_summ : Summable (fun a : A => t2_nat a.1) := ht2_nat_summ.subtype A
  have ht2_ind_summ : Summable (A.indicator t2_nat) :=
    Summable.of_nonneg_of_le
      (fun n => by rw [Set.indicator_apply]; dsimp [t2_nat]; split_ifs <;> positivity)
      (fun n => by rw [Set.indicator_apply]; dsimp [t2_nat]; split_ifs <;> linarith)
      ht2_nat_summ
  have hmid_pt : ∀ a : A, g_mid a ≤ (T : ℝ) * (if K < a.1 then 1 / (a.1 : ℝ) else 0) +
      t2_nat a.1 + ((M : ℝ) * (T : ℝ)) * (if L < a.1 then 1 / (a.1 : ℝ) else 0) := by
    intro a
    dsimp [g_mid, t2_nat]
    by_cases ha : K < a.1 ∧ a.1 ≤ M * T
    · rw [if_pos ha, if_pos ha.1]
      have ha_pos : 0 < a.1 := by omega
      have hrem_le := sum_rem_le M a.1 T ha_pos
      have hTdiv : (T : ℝ) / (a.1 : ℝ) = (T : ℝ) * (1 / (a.1 : ℝ)) := by ring
      rw [hTdiv] at hrem_le
      by_cases haL : a.1 ≤ L
      · have hnotL : ¬ L < a.1 := not_lt.mpr haL
        rw [if_pos ⟨ha.1, haL⟩, if_neg hnotL, mul_zero, add_zero]
        exact hrem_le
      · have haL_lt : L < a.1 := lt_of_not_ge haL
        rw [if_neg (fun h => haL h.2), if_pos haL_lt, add_zero]
        have h1_le : (1 : ℝ) ≤ ((M : ℝ) * (T : ℝ)) * (1 / (a.1 : ℝ)) := by
          have ha_r : (0 : ℝ) < (a.1 : ℝ) := by exact_mod_cast ha_pos
          have hMT_r : (a.1 : ℝ) ≤ (M : ℝ) * (T : ℝ) := by exact_mod_cast ha.2
          rw [mul_one_div, one_le_div ha_r]
          exact hMT_r
        linarith
    · rw [if_neg ha]
      positivity
  have ht2_le_L : ∑' a : A, t2_nat a.1 ≤ (L : ℝ) := by
    calc
      ∑' a : A, t2_nat a.1 = ∑' n : ℕ, A.indicator t2_nat n := tsum_subtype A t2_nat
      _ ≤ ∑' n : ℕ, t2_nat n := by
        refine ht2_ind_summ.tsum_le_tsum (fun n => ?_) ht2_nat_summ
        rw [Set.indicator_apply]
        split_ifs
        · exact le_rfl
        · dsimp [t2_nat]; split_ifs <;> positivity
      _ = ∑ n ∈ Finset.Ioc K L, t2_nat n := ht2_has.tsum_eq
      _ = ∑ n ∈ Finset.Ioc K L, (1 : ℝ) := by
        refine Finset.sum_congr rfl fun n hn => ?_
        dsimp [t2_nat]
        exact if_pos (Finset.mem_Ioc.mp hn)
      _ = ((Finset.Ioc K L).card : ℝ) := by simp
      _ ≤ (L : ℝ) := by
        rw [Nat.card_Ioc]
        exact_mod_cast Nat.sub_le L K
  have hmid_lt : ∑' a : A, g_mid a < (T : ℝ) * (ε / 2) + (L : ℝ) := by
    have hrhs_summ := (ht1_summ.add ht2_summ).add ht3_summ
    have h1 := hg_mid_summ.tsum_le_tsum hmid_pt hrhs_summ
    rw [(ht1_summ.add ht2_summ).tsum_add ht3_summ, ht1_summ.tsum_add ht2_summ,
      tsum_mul_left, tsum_mul_left] at h1
    have hterm1 : (T : ℝ) * ∑' a : A, (if K < a.1 then 1 / (a.1 : ℝ) else 0) < (T : ℝ) * (ε / 4) :=
      mul_lt_mul_of_pos_left hK (by exact_mod_cast hT_pos)
    have hMT_pos : (0 : ℝ) < (M : ℝ) * (T : ℝ) := by
      have : 0 < M * T := Nat.mul_pos hM hT_pos
      exact_mod_cast this
    have hterm3 : ((M : ℝ) * (T : ℝ)) * ∑' a : A, (if L < a.1 then 1 / (a.1 : ℝ) else 0) <
        ((M : ℝ) * (T : ℝ)) * (ε / (4 * M)) :=
      mul_lt_mul_of_pos_left hL_tail hMT_pos
    have hM_ne : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    have hterm3_eq : ((M : ℝ) * (T : ℝ)) * (ε / (4 * M)) = (T : ℝ) * (ε / 4) := by
      field_simp [hM_ne]
    linarith
  let tail_nat : ℕ → ℝ := fun n =>
    if M * T < n then 4 * (2 : ℝ) ^ (M * T) * ((1 : ℝ) / 2) ^ n else 0
  have hhalf_summ : Summable (fun n : ℕ => if M * T < n then ((1 : ℝ) / 2) ^ n else 0) :=
    Summable.of_nonneg_of_le
      (fun n => by split_ifs <;> positivity)
      (fun n => by split_ifs <;> [exact le_rfl; positivity])
      summable_geometric_two
  have htail_nat_summ : Summable tail_nat := by
    have hcongr : tail_nat = fun n => (4 * (2 : ℝ) ^ (M * T)) *
        (if M * T < n then ((1 : ℝ) / 2) ^ n else 0) := by
      funext n
      dsimp [tail_nat]
      split_ifs <;> ring
    rw [hcongr]
    exact hhalf_summ.mul_left _
  have htail_ind_summ : Summable (A.indicator tail_nat) :=
    Summable.of_nonneg_of_le
      (fun n => by rw [Set.indicator_apply]; dsimp [tail_nat]; split_ifs <;> positivity)
      (fun n => by rw [Set.indicator_apply]; dsimp [tail_nat]; split_ifs <;> first | exact le_rfl | positivity)
      htail_nat_summ
  have htail_le : ∑' a : A, g_tail a ≤ 4 := by
    have hpt : ∀ a : A, g_tail a ≤ tail_nat a.1 := by
      intro a
      dsimp [g_tail, tail_nat]
      split_ifs with ha
      · exact sum_rem_large_n_le M T a.1 hM ha
      · exact le_rfl
    calc
      ∑' a : A, g_tail a ≤ ∑' a : A, tail_nat a.1 :=
        hg_tail_summ.tsum_le_tsum hpt (htail_nat_summ.subtype A)
      _ = ∑' n : ℕ, A.indicator tail_nat n := tsum_subtype A tail_nat
      _ ≤ ∑' n : ℕ, tail_nat n := by
        refine htail_ind_summ.tsum_le_tsum (fun n => ?_) htail_nat_summ
        rw [Set.indicator_apply]
        split_ifs
        · exact le_rfl
        · dsimp [tail_nat]; split_ifs <;> positivity
      _ = (4 * (2 : ℝ) ^ (M * T)) *
          ∑' n : ℕ, (if M * T < n then ((1 : ℝ) / 2) ^ n else 0) := by
        have hcongr : tail_nat = fun n => (4 * (2 : ℝ) ^ (M * T)) *
            (if M * T < n then ((1 : ℝ) / 2) ^ n else 0) := by
          funext n
          dsimp [tail_nat]
          split_ifs <;> ring
        rw [hcongr, tsum_mul_left]
      _ = (4 * (2 : ℝ) ^ (M * T)) * (2 * ((1 : ℝ) / 2) ^ (M * T + 1)) := by
        rw [tsum_tail_half_pow (M * T)]
      _ = 4 := by
        rw [pow_succ]
        have hpow1 : (2 : ℝ) ^ (M * T) * ((1 : ℝ) / 2) ^ (M * T) = 1 := by
          rw [← mul_pow]
          norm_num
        calc
          (4 * (2 : ℝ) ^ (M * T)) * (2 * (((1 : ℝ) / 2) ^ (M * T) * ((1 : ℝ) / 2)))
              = 4 * ((2 : ℝ) ^ (M * T) * ((1 : ℝ) / 2) ^ (M * T)) := by ring
          _ = 4 := by rw [hpow1, mul_one]
  have hT_gt_bound : (L : ℝ) + 4 < (ε / 4) * (T : ℝ) := by
    have h1 : ((4 * ((L : ℝ) + 4)) / ε) < (T : ℝ) :=
      lt_of_lt_of_le hT₀ (by exact_mod_cast le_max_right (L + 1) T₀)
    have h2 : 4 * ((L : ℝ) + 4) < (T : ℝ) * ε := (div_lt_iff₀ hε).mp h1
    linarith
  have hsum_lt : ∑ t ∈ Finset.range T, F t < ∑ _t ∈ Finset.range T, ε := by
    have hconst : ∑ _t ∈ Finset.range T, ε = (T : ℝ) * ε := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hsplit, hconst]
    linarith
  obtain ⟨t, _, ht⟩ := Finset.exists_lt_of_sum_lt hsum_lt
  exact ⟨M * (t + 1), Nat.mul_pos hM (Nat.succ_pos t), dvd_mul_right M (t + 1), ht⟩
