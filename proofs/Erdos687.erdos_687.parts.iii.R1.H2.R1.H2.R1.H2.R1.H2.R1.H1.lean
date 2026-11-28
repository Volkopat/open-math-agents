import OMAReductions.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1_H2_R1_H2_R1

-- Step Erdos687.erdos_687.parts.iii.R1.H2.R1.H2.R1.H2.R1.H2.R1.H1: hypothesis H1 of reduction Erdos687.erdos_687.parts.iii.R1.H2.R1.H2.R1.H2.R1.H2.R1
-- Credit: @santiemanuel

/-!
# Unconditional CRT Fractional-Primorial Trough Expansion (`R1.H2.R1.H2.R1.H2.R1.H2.R1.H1`)

We prove `OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1_H2_R1_H2_R1.H1` with the explicit
constant `c₁ = (65536 * Real.exp 11)⁻¹`:
whenever a residue shift `M₀ < Q` (`Q = ∏_{p ≤ x} p`) satisfies `S_min(M₀) < -θ * L`, unfreezing a
deterministic pigeonhole-selected bucket `T ⊆ (Ioc (x / 4) x).filter Nat.Prime` of CRT coordinates
produces at least `Q ^ (c₁ * θ * ε)` distinct shifts `M < Q` satisfying `S_min(M) < -(3 * θ / 4) * L`.

Proof outline:
1. Establish Mertens' third theorem lower bound `V(x) ≥ exp (-11) / log x` for `x ≥ 2`.
2. Using `Chebyshev.theta_ge` and `Chebyshev.theta_le_log4_mul_x`, show that
   `S = (Ioc (x / 4) x).filter Nat.Prime` has cardinality `≥ x / (8 * log x)` for `x ≥ 104 ^ 4`.
3. Partition `S` into `K = ⌈512 * exp 11 / (θ * ε)⌉₊ + 1` pairwise disjoint buckets `T₀, …, T_{K-1}`
   of size `m = S.card / K`, and bound the sum of unique/subset-uncovered Fejér pairs across all `K`
   buckets by `L` times the `z`-rough count in `[M₀ + 1, M₀ + 2 * L]` (`z = ⌊x ^ (ε / 8)⌋₊`), which
   is `≤ (64 * exp 11 / ε) * L * V(x)` via `selberg_rough_Icc_upper`.
4. By pigeonhole, pick `j₀ < K` with uncovered Fejér mass `≤ (θ / 8) * L * V(x)`; then
   `crt_subcube_card`, `ramanujan_fejer_identity`, and `ramanujan_major_arc_bound` yield
   `∏_{p ∈ T_{j₀}} p ≥ Q ^ (c₁ * θ * ε)` shifts in `range Q` below `-(3 * θ / 4) * L`.
-/

open Filter Finset Real

private lemma finset_prod_dvd_of_coprime {S : Finset ℕ} {f : ℕ → ℕ} {n : ℕ}
    (hcop : Set.Pairwise (S : Set ℕ) (Function.onFun Nat.Coprime f))
    (hdvd : ∀ p ∈ S, f p ∣ n) : (∏ p ∈ S, f p) ∣ n := by
  induction S using Finset.cons_induction with
  | empty => simp
  | cons a s has ih =>
    rw [Finset.prod_cons]
    have hcop_s : Set.Pairwise (s : Set ℕ) (Function.onFun Nat.Coprime f) :=
      hcop.mono fun x hx => Finset.mem_coe.mpr (Finset.mem_cons_of_mem (Finset.mem_coe.mp hx))
    have hs_dvd : (∏ p ∈ s, f p) ∣ n := ih hcop_s (fun p hp => hdvd p (Finset.mem_cons_of_mem hp))
    have ha_dvd : f a ∣ n := hdvd a (Finset.mem_cons_self a s)
    have ha_cop : Nat.Coprime (f a) (∏ p ∈ s, f p) :=
      Nat.Coprime.prod_right fun p hp =>
        hcop (Finset.mem_coe.mpr (Finset.mem_cons_self a s))
          (Finset.mem_coe.mpr (Finset.mem_cons_of_mem hp))
          (fun heq => has (heq ▸ hp))
    exact ha_cop.mul_dvd_of_dvd_of_dvd ha_dvd hs_dvd

private lemma prime_pow_div_dvd_factorial {p n : ℕ} (hp : 1 ≤ p) :
    p ^ (n / p) ∣ n.factorial := by
  have hfact : n.factorial = ∏ m ∈ Icc 1 n, m := by
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Nat.factorial_succ, Finset.prod_Icc_succ_top (by omega : 1 ≤ k + 1), ih, Nat.mul_comm]
  rw [hfact]
  have himg_sub : (Icc 1 (n / p)).image (fun j => p * j) ⊆ Icc 1 n := by
    intro m hm
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hm
    have hj' := mem_Icc.mp hj
    have hmul : p * j ≤ n := by
      have h1 : j * p ≤ (n / p) * p := Nat.mul_le_mul_right p hj'.2
      have h2 : (n / p) * p ≤ n := Nat.div_mul_le_self n p
      rw [Nat.mul_comm]
      exact h1.trans h2
    exact mem_Icc.mpr ⟨Nat.mul_pos (by omega) (by omega), hmul⟩
  have hprod_dvd : (∏ m ∈ (Icc 1 (n / p)).image (fun j => p * j), m) ∣ ∏ m ∈ Icc 1 n, m :=
    Finset.prod_dvd_prod_of_subset _ _ _ himg_sub
  have hprod_eq : ∏ m ∈ (Icc 1 (n / p)).image (fun j => p * j), m =
      p ^ (n / p) * ∏ j ∈ Icc 1 (n / p), j := by
    rw [Finset.prod_image (fun j₁ _ j₂ _ h => Nat.eq_of_mul_eq_mul_left (by omega) h),
      Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]
  rw [hprod_eq] at hprod_dvd
  exact dvd_trans (dvd_mul_right _ _) hprod_dvd

private lemma mertens_first_upper {n : ℕ} (hn : 1 ≤ n) :
    ∑ p ∈ (range (n + 1)).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) ≤
      Real.log (n : ℝ) + 2 := by
  let P := (range (n + 1)).filter Nat.Prime
  have hcop : Set.Pairwise (P : Set ℕ) (Function.onFun Nat.Coprime (fun p => p ^ (n / p))) := by
    intro p hp q hq hpq
    exact ((Nat.coprime_primes (mem_filter.mp (mem_coe.mp hp)).2
      (mem_filter.mp (mem_coe.mp hq)).2).2 hpq).pow _ _
  have hdvd : (∏ p ∈ P, p ^ (n / p)) ∣ n.factorial :=
    finset_prod_dvd_of_coprime hcop fun p hp =>
      prime_pow_div_dvd_factorial (mem_filter.mp hp).2.one_le
  have hprod_le : ∏ p ∈ P, p ^ (n / p) ≤ n ^ n :=
    (Nat.le_of_dvd (Nat.factorial_pos n) hdvd).trans (Nat.factorial_le_pow n)
  have hprod_pos : 0 < ∏ p ∈ P, p ^ (n / p) :=
    Finset.prod_pos fun p hp => pow_pos (mem_filter.mp hp).2.pos _
  have hlog_le : Real.log ((∏ p ∈ P, p ^ (n / p) : ℕ) : ℝ) ≤ Real.log ((n ^ n : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast hprod_pos) (by exact_mod_cast hprod_le)
  have hlhs_log : Real.log ((∏ p ∈ P, p ^ (n / p) : ℕ) : ℝ) =
      ∑ p ∈ P, ((n / p : ℕ) : ℝ) * Real.log (p : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod (fun p hp => by
      exact_mod_cast (pow_pos (mem_filter.mp hp).2.pos _).ne')]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Nat.cast_pow, Real.log_pow]
  have hrhs_log : Real.log ((n ^ n : ℕ) : ℝ) = (n : ℝ) * Real.log (n : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
  rw [hlhs_log, hrhs_log] at hlog_le
  have hfloor : ∑ p ∈ P, ((n : ℝ) / (p : ℝ) - 1) * Real.log (p : ℝ) ≤
      ∑ p ∈ P, ((n / p : ℕ) : ℝ) * Real.log (p : ℝ) := by
    refine Finset.sum_le_sum fun p hp => ?_
    have hpp : p.Prime := (mem_filter.mp hp).2
    have hlogp_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hpp.one_le)
    have hlt_nat : n < (n / p + 1) * p := by
      rw [Nat.add_mul, Nat.one_mul]
      have hdm : (n / p) * p + n % p = n := by rw [Nat.mul_comm]; exact Nat.div_add_mod n p
      have hml := Nat.mod_lt n hpp.pos
      omega
    have hlt_r : (n : ℝ) < (((n / p : ℕ) : ℝ) + 1) * (p : ℝ) := by exact_mod_cast hlt_nat
    have hdiv_r : (n : ℝ) / (p : ℝ) - 1 ≤ ((n / p : ℕ) : ℝ) := by
      have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
      have h1 : (n : ℝ) / (p : ℝ) ≤ ((n / p : ℕ) : ℝ) + 1 :=
        (div_le_iff₀ hp_pos).mpr hlt_r.le
      linarith
    exact mul_le_mul_of_nonneg_right hdiv_r hlogp_nn
  have hsplit : ∑ p ∈ P, ((n : ℝ) / (p : ℝ) - 1) * Real.log (p : ℝ) =
      (n : ℝ) * (∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) - ∑ p ∈ P, Real.log (p : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have htheta : ∑ p ∈ P, Real.log (p : ℝ) ≤ Real.log 4 * (n : ℝ) := by
    have hth := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n)
    have hsum_eq : Chebyshev.theta (n : ℝ) = ∑ p ∈ P, Real.log (p : ℝ) := by
      rw [Chebyshev.theta]
      congr 1
      ext p
      simp only [P, mem_filter, mem_Ioc, mem_range, Nat.floor_natCast]
      exact ⟨fun ⟨⟨_, hpn⟩, hpp⟩ => ⟨by omega, hpp⟩, fun ⟨hpn, hpp⟩ => ⟨⟨hpp.pos, by omega⟩, hpp⟩⟩
    rwa [hsum_eq] at hth
  have hlog4_le2 : Real.log 4 ≤ 2 := by
    have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]
      push_cast; rfl
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcomb : (n : ℝ) * (∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) ≤
      (n : ℝ) * (Real.log (n : ℝ) + 2) := by
    have h1 := hfloor.trans hlog_le
    rw [hsplit] at h1
    have h2 : Real.log 4 * (n : ℝ) ≤ 2 * (n : ℝ) := mul_le_mul_of_nonneg_right hlog4_le2 hn_pos.le
    linarith
  exact le_of_mul_le_mul_left hcomb hn_pos

private lemma mertens_third_lower {x : ℕ} (hx : 2 ≤ x) :
    Real.exp (-11) / Real.log (x : ℝ) ≤
      ∏ p ∈ (range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹) := by
  let P := (range (x + 1)).filter Nat.Prime
  let M : ℕ → ℝ := fun k => ∑ p ∈ (range (k + 1)).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)
  have habel : ∀ n : ℕ, 2 ≤ n →
      ∑ p ∈ (range (n + 1)).filter Nat.Prime, (p : ℝ)⁻¹ =
        M n / Real.log (n : ℝ) +
          ∑ k ∈ Icc 2 (n - 1), M k * ((Real.log (k : ℝ))⁻¹ - (Real.log ((k + 1 : ℕ) : ℝ))⁻¹) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      have hP2 : (range 3).filter Nat.Prime = {2} := by decide
      have hlog2_ne : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
      simp only [M, hP2, Finset.sum_singleton, Nat.cast_ofNat]
      rw [Finset.Icc_eq_empty_of_lt (by norm_num), Finset.sum_empty, add_zero]
      field_simp
    | succ m hm ih =>
      have hsub : m + 1 - 1 = m := by omega
      rw [hsub]
      have hIcc : Icc 2 m = insert m (Icc 2 (m - 1)) := by
        ext k; simp only [mem_Icc, mem_insert]; omega
      have hnotmem : m ∉ Icc 2 (m - 1) := by simp only [mem_Icc]; omega
      rw [hIcc, Finset.sum_insert hnotmem]
      have hstep_sum :
          ∑ p ∈ (range (m + 1 + 1)).filter Nat.Prime, (p : ℝ)⁻¹ =
            (∑ p ∈ (range (m + 1)).filter Nat.Prime, (p : ℝ)⁻¹) +
              (M (m + 1) - M m) / Real.log ((m + 1 : ℕ) : ℝ) := by
        have hrange : range (m + 1 + 1) = insert (m + 1) (range (m + 1)) := Finset.range_add_one
        have hnm : m + 1 ∉ range (m + 1) := Finset.notMem_range_self
        have hlogm1_ne : Real.log ((m + 1 : ℕ) : ℝ) ≠ 0 :=
          (Real.log_pos (by exact_mod_cast (show 1 < m + 1 by omega))).ne'
        by_cases hp : (m + 1).Prime
        · have hf : (range (m + 1 + 1)).filter Nat.Prime =
              insert (m + 1) ((range (m + 1)).filter Nat.Prime) := by
            rw [hrange, Finset.filter_insert, if_pos hp]
          have hnmf : m + 1 ∉ (range (m + 1)).filter Nat.Prime := fun h => hnm (mem_filter.mp h).1
          rw [hf, Finset.sum_insert hnmf]
          have hMdiff : M (m + 1) - M m = Real.log ((m + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) := by
            dsimp [M]; rw [hf, Finset.sum_insert hnmf]; ring
          rw [hMdiff]; field_simp; ring
        · have hf : (range (m + 1 + 1)).filter Nat.Prime = (range (m + 1)).filter Nat.Prime := by
            rw [hrange, Finset.filter_insert, if_neg hp]
          have hMdiff : M (m + 1) - M m = 0 := by dsimp [M]; rw [hf, sub_self]
          rw [hf, hMdiff, zero_div, add_zero]
      rw [hstep_sum, ih]
      ring
  have hlog2_ge : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h1 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
    rw [Real.log_inv] at h1; linarith
  have hlogx_ge : Real.log 2 ≤ Real.log (x : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hx)
  have hlogx_pos : 0 < Real.log (x : ℝ) := by linarith
  have hsecond : ∑ p ∈ P, (p : ℝ)⁻¹ ≤ Real.log (Real.log (x : ℝ)) + 10 := by
    change ∑ p ∈ (range (x + 1)).filter Nat.Prime, (p : ℝ)⁻¹ ≤ _
    rw [habel x hx]
    have hterm1 : M x / Real.log (x : ℝ) ≤ 5 := by
      have hMx : M x ≤ Real.log (x : ℝ) + 2 := mertens_first_upper (by omega)
      have h1 : M x / Real.log (x : ℝ) ≤ (Real.log (x : ℝ) + 2) / Real.log (x : ℝ) :=
        div_le_div_of_nonneg_right hMx hlogx_pos.le
      have h2 : (Real.log (x : ℝ) + 2) / Real.log (x : ℝ) = 1 + 2 / Real.log (x : ℝ) := by field_simp
      have h3 : 2 / Real.log (x : ℝ) ≤ 4 := by rw [div_le_iff₀ hlogx_pos]; linarith
      linarith
    have hpt : ∀ k ∈ Icc 2 (x - 1),
        M k * ((Real.log (k : ℝ))⁻¹ - (Real.log ((k + 1 : ℕ) : ℝ))⁻¹) ≤
          (Real.log (Real.log ((k + 1 : ℕ) : ℝ)) - Real.log (Real.log (k : ℝ))) +
            2 * ((Real.log (k : ℝ))⁻¹ - (Real.log ((k + 1 : ℕ) : ℝ))⁻¹) := by
      intro k hk
      have hk2 : 2 ≤ k := (mem_Icc.mp hk).1
      have hlk_pos : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < k by omega))
      have hlk1_pos : 0 < Real.log ((k + 1 : ℕ) : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < k + 1 by omega))
      have hlk_le : Real.log (k : ℝ) ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast (show 0 < k by omega)) (by exact_mod_cast Nat.le_succ k)
      have hdiff_nn : 0 ≤ (Real.log (k : ℝ))⁻¹ - (Real.log ((k + 1 : ℕ) : ℝ))⁻¹ :=
        sub_nonneg.mpr (inv_anti₀ hlk_pos hlk_le)
      have hMk : M k ≤ Real.log (k : ℝ) + 2 := mertens_first_upper (by omega)
      have hstep1 := mul_le_mul_of_nonneg_right hMk hdiff_nn
      have hstep2 : Real.log (k : ℝ) * ((Real.log (k : ℝ))⁻¹ - (Real.log ((k + 1 : ℕ) : ℝ))⁻¹) =
          1 - Real.log (k : ℝ) / Real.log ((k + 1 : ℕ) : ℝ) := by field_simp
      have hlog_ineq : 1 - Real.log (k : ℝ) / Real.log ((k + 1 : ℕ) : ℝ) ≤
          Real.log (Real.log ((k + 1 : ℕ) : ℝ)) - Real.log (Real.log (k : ℝ)) := by
        have h := Real.log_le_sub_one_of_pos (div_pos hlk_pos hlk1_pos)
        rw [Real.log_div hlk_pos.ne' hlk1_pos.ne'] at h; linarith
      linarith
    have htele : ∀ n : ℕ, 2 ≤ n →
        ∑ k ∈ Icc 2 (n - 1),
          ((Real.log (Real.log ((k + 1 : ℕ) : ℝ)) - Real.log (Real.log (k : ℝ))) +
            2 * ((Real.log (k : ℝ))⁻¹ - (Real.log ((k + 1 : ℕ) : ℝ))⁻¹)) =
        (Real.log (Real.log (n : ℝ)) - Real.log (Real.log 2)) +
          2 * ((Real.log 2)⁻¹ - (Real.log (n : ℝ))⁻¹) := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base => rw [Finset.Icc_eq_empty_of_lt (by norm_num), Finset.sum_empty]; simp
      | succ m hm ih =>
        have hsub : m + 1 - 1 = m := by omega
        rw [hsub]
        have hIcc : Icc 2 m = insert m (Icc 2 (m - 1)) := by
          ext k; simp only [mem_Icc, mem_insert]; omega
        have hnotmem : m ∉ Icc 2 (m - 1) := by simp only [mem_Icc]; omega
        rw [hIcc, Finset.sum_insert hnotmem, ih]; ring
    have h1 := (Finset.sum_le_sum hpt).trans_eq (htele x hx)
    have hll2_ge : -1 ≤ Real.log (Real.log 2) := by
      have h1' : Real.log (2⁻¹ : ℝ) ≤ Real.log (Real.log 2) :=
        Real.log_le_log (by norm_num) (by linarith)
      rw [Real.log_inv] at h1'
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hinv2_le : (Real.log 2)⁻¹ ≤ 2 := by rw [inv_eq_one_div, div_le_iff₀ (by linarith)]; linarith
    have hinvx_nn : 0 ≤ (Real.log (x : ℝ))⁻¹ := inv_nonneg.mpr hlogx_pos.le
    linarith
  have hV_pos : 0 < ∏ p ∈ P, (1 - (p : ℝ)⁻¹) := by
    apply Finset.prod_pos; intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (mem_filter.mp hp).2.two_le
    have hinv : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp2
    linarith
  have hinv_le : (∏ p ∈ P, (1 - (p : ℝ)⁻¹))⁻¹ ≤
      Real.exp (∑ p ∈ P, (p : ℝ)⁻¹ + ∑ p ∈ P, ((p : ℝ) * ((p - 1 : ℕ) : ℝ))⁻¹) := by
    rw [← Finset.prod_inv_distrib, ← Finset.sum_add_distrib, Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (mem_filter.mp hp).2.two_le
      have hinv : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp2
      exact inv_nonneg.mpr (by linarith)
    · intro p hp
      have hpp : p.Prime := (mem_filter.mp hp).2
      have hp_ne : (p : ℝ) ≠ 0 := by exact_mod_cast hpp.ne_zero
      have hp_sub : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub hpp.one_le, Nat.cast_one]
      have hp1_ne : (p : ℝ) - 1 ≠ 0 := by
        have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
        linarith
      have hid : (1 - (p : ℝ)⁻¹)⁻¹ = 1 + ((p : ℝ)⁻¹ + ((p : ℝ) * ((p - 1 : ℕ) : ℝ))⁻¹) := by
        rw [hp_sub]; field_simp; ring
      rw [hid]
      linarith [Real.add_one_le_exp ((p : ℝ)⁻¹ + ((p : ℝ) * ((p - 1 : ℕ) : ℝ))⁻¹)]
  have hsq_sum : ∑ p ∈ P, ((p : ℝ) * ((p - 1 : ℕ) : ℝ))⁻¹ ≤ 1 := by
    have htele : ∀ m : ℕ, 2 ≤ m →
        ∑ n ∈ Icc 2 m, ((n : ℝ) * ((n - 1 : ℕ) : ℝ))⁻¹ = 1 - (m : ℝ)⁻¹ := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => norm_num
      | succ k hk ih =>
        rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ k + 1), ih]
        have hsub : k + 1 - 1 = k := by omega
        rw [hsub]
        have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        have hk1_ne : ((k + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        push_cast; field_simp; ring
    have hP_sub : P ⊆ Icc 2 x := fun p hp =>
      mem_Icc.mpr ⟨(mem_filter.mp hp).2.two_le, by have := mem_range.mp (mem_filter.mp hp).1; omega⟩
    have h1 : ∑ p ∈ P, ((p : ℝ) * ((p - 1 : ℕ) : ℝ))⁻¹ ≤
        ∑ n ∈ Icc 2 x, ((n : ℝ) * ((n - 1 : ℕ) : ℝ))⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hP_sub (fun _ _ _ => by positivity)
    rw [htele x hx] at h1
    have hnn : (0 : ℝ) ≤ (x : ℝ)⁻¹ := by positivity
    linarith
  have hinv_bound : (∏ p ∈ P, (1 - (p : ℝ)⁻¹))⁻¹ ≤ Real.exp 11 * Real.log (x : ℝ) := by
    calc
      (∏ p ∈ P, (1 - (p : ℝ)⁻¹))⁻¹ ≤ Real.exp (Real.log (Real.log (x : ℝ)) + 11) :=
        hinv_le.trans (Real.exp_le_exp.mpr (by linarith))
      _ = Real.exp 11 * Real.log (x : ℝ) := by rw [Real.exp_add, Real.exp_log hlogx_pos, mul_comm]
  rw [div_le_iff₀ hlogx_pos]
  have hmul := mul_le_mul_of_nonneg_right hinv_bound hV_pos.le
  rw [inv_mul_cancel₀ hV_pos.ne'] at hmul
  have hmul2 := mul_le_mul_of_nonneg_left hmul (by positivity : 0 ≤ Real.exp (-11))
  have hexp_cancel : Real.exp (-11) * (Real.exp 11 * Real.log (x : ℝ)) = Real.log (x : ℝ) := by
    rw [← mul_assoc, ← Real.exp_add]; norm_num
  have hgoal : Real.exp (-11) ≤ Real.log (x : ℝ) * (∏ p ∈ P, (1 - (p : ℝ)⁻¹)) := by
    calc
      Real.exp (-11) = Real.exp (-11) * 1 := (mul_one _).symm
      _ ≤ Real.exp (-11) * ((Real.exp 11 * Real.log (x : ℝ)) * (∏ p ∈ P, (1 - (p : ℝ)⁻¹))) := hmul2
      _ = Real.log (x : ℝ) * (∏ p ∈ P, (1 - (p : ℝ)⁻¹)) := by rw [← mul_assoc, hexp_cancel]
  linarith

private lemma exists_disjoint_buckets {α : Type*} [DecidableEq α] (S : Finset α) (K m : ℕ)
    (hcard : K * m ≤ S.card) :
    ∃ T : ℕ → Finset α,
      (∀ j ∈ range K, T j ⊆ S ∧ (T j).card = m) ∧
      (range K : Set ℕ).PairwiseDisjoint T := by
  induction K generalizing S with
  | zero =>
    exact ⟨fun _ => ∅, by simp, by simp⟩
  | succ k ih =>
    have hm_le : m ≤ S.card := by
      have : 1 * m ≤ (k + 1) * m := Nat.mul_le_mul_right m (by omega)
      omega
    obtain ⟨A, hAS, hAm⟩ := Finset.exists_subset_card_eq hm_le
    have hcard_sdiff : (S \ A).card + A.card = S.card := by
      rw [← Finset.card_union_of_disjoint Finset.sdiff_disjoint, Finset.sdiff_union_of_subset hAS]
    rw [Nat.add_mul, Nat.one_mul] at hcard
    obtain ⟨T', hT'_sub, hT'_pw⟩ := ih (S \ A) (by omega)
    let T : ℕ → Finset α := fun j => if j = k then A else T' j
    refine ⟨T, ?_, ?_⟩
    · intro j hj
      by_cases hjk : j = k
      · subst hjk
        simp only [T, if_pos]
        exact ⟨hAS, hAm⟩
      · have hj_lt : j ∈ range k := mem_range.mpr (by have := mem_range.mp hj; omega)
        simp only [T, if_neg hjk]
        exact ⟨(hT'_sub j hj_lt).1.trans Finset.sdiff_subset, (hT'_sub j hj_lt).2⟩
    · intro i hi j hj hij
      rw [Function.onFun]
      by_cases hik : i = k
      · have hjk : j ≠ k := by omega
        have hj_lt : j ∈ range k := mem_range.mpr (by have := mem_range.mp hj; omega)
        dsimp [T]
        rw [if_pos hik, if_neg hjk]
        exact Finset.disjoint_of_subset_right (hT'_sub j hj_lt).1 Finset.sdiff_disjoint.symm
      · by_cases hjk : j = k
        · have hi_lt : i ∈ range k := mem_range.mpr (by have := mem_range.mp hi; omega)
          dsimp [T]
          rw [if_neg hik, if_pos hjk]
          exact Finset.disjoint_of_subset_left (hT'_sub i hi_lt).1 Finset.sdiff_disjoint
        · have hi_lt : i ∈ range k := mem_range.mpr (by have := mem_range.mp hi; omega)
          have hj_lt : j ∈ range k := mem_range.mpr (by have := mem_range.mp hj; omega)
          dsimp [T]
          rw [if_neg hik, if_neg hjk]
          exact hT'_pw (mem_coe.mpr hi_lt) (mem_coe.mpr hj_lt) hij

private lemma primes_Ioc_quarter_card {x : ℕ} (hx : 104 ^ 4 ≤ x) :
    (x : ℝ) / (8 * Real.log (x : ℝ)) ≤ (((Ioc (x / 4) x).filter Nat.Prime).card : ℝ) := by
  let S := (Ioc (x / 4) x).filter Nat.Prime
  have hx2 : 2 ≤ x := by omega
  have hx_pos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (show 0 < x by omega)
  have hlogx_pos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  -- Relate `∑ p ∈ S, log p` to `Chebyshev.theta x - Chebyshev.theta (x / 4)`.
  have htheta_diff : Chebyshev.theta (x : ℝ) - Chebyshev.theta ((x / 4 : ℕ) : ℝ) =
      ∑ p ∈ S, Real.log (p : ℝ) := by
    have hθ : ∀ n : ℕ, Chebyshev.theta (n : ℝ) = ∑ p ∈ (Ioc 0 n).filter Nat.Prime, Real.log (p : ℝ) :=
      fun n => by simp [Chebyshev.theta]
    rw [hθ x, hθ (x / 4)]
    have hdisj : Disjoint ((Ioc 0 (x / 4)).filter Nat.Prime) S := by
      rw [Finset.disjoint_left]
      intro p h1 h2
      have := (mem_Ioc.mp (mem_filter.mp h1).1).2
      have := (mem_Ioc.mp (mem_filter.mp h2).1).1
      omega
    have hunion : (Ioc 0 x).filter Nat.Prime = (Ioc 0 (x / 4)).filter Nat.Prime ∪ S := by
      ext p
      simp only [S, mem_union, mem_filter, mem_Ioc]
      constructor
      · rintro ⟨⟨hp0, hpx⟩, hpp⟩
        by_cases hp4 : p ≤ x / 4
        · exact Or.inl ⟨⟨hp0, hp4⟩, hpp⟩
        · exact Or.inr ⟨⟨by omega, hpx⟩, hpp⟩
      · rintro (⟨⟨hp0, hp4⟩, hpp⟩ | ⟨⟨hp4, hpx⟩, hpp⟩)
        · exact ⟨⟨hp0, hp4.trans (Nat.div_le_self x 4)⟩, hpp⟩
        · exact ⟨⟨by omega, hpx⟩, hpp⟩
    rw [hunion, Finset.sum_union hdisj, add_sub_cancel_left]
  -- Bound `Chebyshev.theta (x / 4) ≤ (1 / 2) * x * log 2`.
  have hup4 : Chebyshev.theta ((x / 4 : ℕ) : ℝ) ≤ (1 / 2 : ℝ) * (x : ℝ) * Real.log 2 := by
    have h1 := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg (x / 4))
    have hdiv_r : ((x / 4 : ℕ) : ℝ) ≤ (x : ℝ) / 4 := by
      rw [le_div_iff₀ (by norm_num)]
      exact_mod_cast Nat.div_mul_le_self x 4
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]
      push_cast; rfl
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith
  -- Bound `Chebyshev.theta x ≥ (3 / 4) * x * log 2` for `x ≥ 104 ^ 4` via `q = √√x`.
  have hlo_x : (3 / 4 : ℝ) * (x : ℝ) * Real.log 2 ≤ Chebyshev.theta (x : ℝ) := by
    have hth := Chebyshev.theta_ge x
    let q := Real.sqrt (Real.sqrt (x : ℝ))
    have hq_sq : q * q = Real.sqrt (x : ℝ) := Real.mul_self_sqrt (Real.sqrt_nonneg _)
    have hq_pow4 : q ^ 4 = (x : ℝ) := by
      calc
        q ^ 4 = (q * q) * (q * q) := by ring
        _ = Real.sqrt (x : ℝ) * Real.sqrt (x : ℝ) := by rw [hq_sq]
        _ = (x : ℝ) := Real.mul_self_sqrt hx_pos.le
    have hq_pos : 0 ≤ q := Real.sqrt_nonneg _
    have hq_ge : (104 : ℝ) ≤ q := by
      have hx_r : ((104 ^ 4 : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
      rw [Nat.cast_pow, Nat.cast_ofNat, ← hq_pow4] at hx_r
      by_contra hlt
      push Not at hlt
      have hp4 : q ^ 4 < (104 : ℝ) ^ 4 := pow_lt_pow_left₀ hlt hq_pos (by norm_num)
      linarith
    have hlogx_le : Real.log (x : ℝ) ≤ 4 * q := by
      have hs1 : Real.log (Real.sqrt (x : ℝ)) = Real.log (x : ℝ) / 2 := Real.log_sqrt hx_pos.le
      have hs2 : Real.log q = Real.log (Real.sqrt (x : ℝ)) / 2 := Real.log_sqrt (Real.sqrt_nonneg _)
      have hlu : Real.log q ≤ q - 1 := Real.log_le_sub_one_of_pos (by linarith)
      linarith
    have hlogx1_le : Real.log ((x : ℝ) + 1) ≤ 5 * q ^ 3 := by
      have hx2_r : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx2
      have h1 : Real.log ((x : ℝ) + 1) ≤ Real.log (2 * (x : ℝ)) :=
        Real.log_le_log (by positivity) (by linarith)
      rw [Real.log_mul (by norm_num) hx_pos.ne'] at h1
      have hlog2_le1 : Real.log 2 ≤ 1 := by
        linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hq3_ge : q ≤ q ^ 3 := by nlinarith
      have hq3_ge1 : (1 : ℝ) ≤ q ^ 3 := by nlinarith
      linarith
    have hsqrt_log_le : 2 * Real.sqrt (x : ℝ) * Real.log (x : ℝ) ≤ 8 * q ^ 3 := by
      have h1 : Real.sqrt (x : ℝ) = q ^ 2 := by linarith [hq_sq, sq q]
      rw [h1]
      nlinarith [sq_nonneg q]
    have hlog2_ge : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have h1 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
      rw [Real.log_inv] at h1; linarith
    have herr_le : Real.log ((x : ℝ) + 1) + 2 * Real.sqrt (x : ℝ) * Real.log (x : ℝ) ≤
        (1 / 4 : ℝ) * (x : ℝ) * Real.log 2 := by
      have h13 : 13 * q ^ 3 ≤ (1 / 8 : ℝ) * q ^ 4 := by
        have hq3_nn : 0 ≤ q ^ 3 := by positivity
        nlinarith
      have h14 : (1 / 8 : ℝ) * (x : ℝ) ≤ (1 / 4 : ℝ) * (x : ℝ) * Real.log 2 := by nlinarith
      rw [hq_pow4] at h13
      linarith
    linarith
  have hsum_lo : (x : ℝ) / 8 ≤ ∑ p ∈ S, Real.log (p : ℝ) := by
    have hlog2_ge : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have h1 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
      rw [Real.log_inv] at h1; linarith
    nlinarith [htheta_diff, hup4, hlo_x, hx_pos]
  have hsum_hi : ∑ p ∈ S, Real.log (p : ℝ) ≤ (S.card : ℝ) * Real.log (x : ℝ) := by
    calc
      ∑ p ∈ S, Real.log (p : ℝ) ≤ ∑ _p ∈ S, Real.log (x : ℝ) := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hpx : p ≤ x := (mem_Ioc.mp (mem_filter.mp hp).1).2
        have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (mem_filter.mp hp).2.pos
        exact Real.log_le_log hp_pos (by exact_mod_cast hpx)
      _ = (S.card : ℝ) * Real.log (x : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [div_le_iff₀ (by positivity)]
  have : (x : ℝ) ≤ (S.card : ℝ) * (8 * Real.log (x : ℝ)) := by linarith
  exact this

private lemma two_mul_le_primes_Ioc_quarter {K x : ℕ} (hx_104 : 104 ^ 4 ≤ x)
    (hx_K4 : (16 * K + 8) ^ 4 ≤ x) :
    2 * K ≤ ((Ioc (x / 4) x).filter Nat.Prime).card := by
  have hx_pos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (show 0 < x by omega)
  have hlogx_pos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hScard_lo : (x : ℝ) / (8 * Real.log (x : ℝ)) ≤ (((Ioc (x / 4) x).filter Nat.Prime).card : ℝ) :=
    primes_Ioc_quarter_card hx_104
  let q := Real.sqrt (Real.sqrt (x : ℝ))
  have hq_sq : q * q = Real.sqrt (x : ℝ) := Real.mul_self_sqrt (Real.sqrt_nonneg _)
  have hq_pow4 : q ^ 4 = (x : ℝ) := by
    calc
      q ^ 4 = (q * q) * (q * q) := by ring
      _ = Real.sqrt (x : ℝ) * Real.sqrt (x : ℝ) := by rw [hq_sq]
      _ = (x : ℝ) := Real.mul_self_sqrt hx_pos.le
  have hq_pos : 0 ≤ q := Real.sqrt_nonneg _
  have hq_ge : ((16 * K + 8 : ℕ) : ℝ) ≤ q := by
    have hx_r : (((16 * K + 8) ^ 4 : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx_K4
    rw [Nat.cast_pow, ← hq_pow4] at hx_r
    by_contra hlt
    push Not at hlt
    have hp4 : q ^ 4 < ((16 * K + 8 : ℕ) : ℝ) ^ 4 := pow_lt_pow_left₀ hlt hq_pos (by norm_num)
    linarith
  have hq_ge_lin : 16 * (K : ℝ) + 8 ≤ q := by exact_mod_cast hq_ge
  have hlogx_le : Real.log (x : ℝ) ≤ 4 * q := by
    have hs1 : Real.log (Real.sqrt (x : ℝ)) = Real.log (x : ℝ) / 2 := Real.log_sqrt hx_pos.le
    have hs2 : Real.log q = Real.log (Real.sqrt (x : ℝ)) / 2 := Real.log_sqrt (Real.sqrt_nonneg _)
    have hK_nn : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    have hq_pos' : 0 < q := by linarith
    have hlu : Real.log q ≤ q - 1 := Real.log_le_sub_one_of_pos hq_pos'
    linarith
  have h2K_r : (2 * (K : ℝ)) * (8 * Real.log (x : ℝ)) ≤ (x : ℝ) := by
    have hK_nn : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    have h1 : (2 * (K : ℝ)) * (8 * Real.log (x : ℝ)) ≤ (16 * (K : ℝ)) * (4 * q) := by nlinarith
    have hq_ge8 : (8 : ℝ) ≤ q := by linarith
    have hq2_ge64 : (64 : ℝ) ≤ q ^ 2 := by nlinarith
    have hK_le_q : 16 * (K : ℝ) ≤ q := by linarith
    have h2 : 64 * (K : ℝ) * q ≤ q ^ 4 := by
      calc
        64 * (K : ℝ) * q = 4 * (16 * (K : ℝ)) * q := by ring
        _ ≤ 4 * q * q := by nlinarith
        _ = 4 * q ^ 2 := by ring
        _ ≤ q ^ 2 * q ^ 2 := by nlinarith
        _ = q ^ 4 := by ring
    rw [hq_pow4] at h2
    linarith
  have h2K_le_r : ((2 * K : ℕ) : ℝ) ≤ (((Ioc (x / 4) x).filter Nat.Prime).card : ℝ) := by
    have : ((2 * K : ℕ) : ℝ) ≤ (x : ℝ) / (8 * Real.log (x : ℝ)) := by
      rw [le_div_iff₀ (by positivity)]
      push_cast; exact h2K_r
    exact this.trans hScard_lo
  exact_mod_cast h2K_le_r

private lemma exists_le_of_sum_le {K : ℕ} (hK : 1 ≤ K) (f : ℕ → ℝ) (B_val : ℝ)
    (hsum : ∑ j ∈ range K, f j ≤ (K : ℝ) * B_val) :
    ∃ j₀ ∈ range K, f j₀ ≤ B_val := by
  by_contra hnone
  push Not at hnone
  have hsum_gt : (K : ℝ) * B_val < ∑ j ∈ range K, f j := by
    calc
      (K : ℝ) * B_val = ∑ _j ∈ range K, B_val := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ < ∑ j ∈ range K, f j :=
        Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr (by omega)) hnone
  linarith

set_option maxHeartbeats 800000 in
theorem OMA.solution : OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1_H2_R1_H2_R1.H1 := by
  let c₁ : ℝ := (65536 * Real.exp 11)⁻¹
  refine ⟨c₁, by dsimp [c₁]; positivity, fun θ hθ_pos hθ_lt1 ε hε_pos hε_lt1 => ?_⟩
  let K : ℕ := ⌈512 * Real.exp 11 / (θ * ε)⌉₊ + 1
  have hK_pos : 1 ≤ K := by dsimp [K]; omega
  have hK_ge : 512 * Real.exp 11 / (θ * ε) ≤ (K : ℝ) := by
    dsimp [K]
    have h1 := Nat.le_ceil (512 * Real.exp 11 / (θ * ε))
    push_cast
    linarith
  have hK_le : (K : ℝ) ≤ 1024 * Real.exp 11 / (θ * ε) := by
    dsimp [K]
    have hpos_arg : 0 ≤ 512 * Real.exp 11 / (θ * ε) := by positivity
    have hlt := Nat.ceil_lt_add_one hpos_arg
    have hbig : (2 : ℝ) ≤ 512 * Real.exp 11 / (θ * ε) := by
      have hθe_le1 : θ * ε ≤ 1 := by nlinarith
      have hθe_pos : 0 < θ * ε := mul_pos hθ_pos hε_pos
      rw [le_div_iff₀ hθe_pos]
      have he11 : (1 : ℝ) ≤ Real.exp 11 := Real.one_le_exp (by norm_num)
      nlinarith
    have hdouble : 1024 * Real.exp 11 / (θ * ε) = 2 * (512 * Real.exp 11 / (θ * ε)) := by ring
    push_cast
    linarith
  -- Choose asymptotic threshold `X₀` so all power/logarithm inequalities hold cleanly.
  -- 1) `(x : ℝ) ^ (ε / 16) ≥ 12` (so `(x : ℝ) ^ ε ≥ 12` and `(x : ℝ) ^ (ε / 16) ≥ 4`).
  obtain ⟨N_rpow, hN_rpow⟩ := exists_nat_ge ((12 : ℝ) ^ ((16 : ℝ) / ε))
  -- 2) Major-arc error `3 / (4 * (Nat.log 2 L + 1)^2) ≤ (θ / 16) * (exp (-11) / log x)?`
  -- Wait: `S_maj` is ALREADY inside the `V(x)` factor! `|S_maj| ≤ 3 * D ^ 2 / (4 * L) ≤ (3 / (4 * (log₂ L + 1)^2)) * L ≤ (θ / 16) * L`!
  obtain ⟨N_maj, hN_maj⟩ := exists_nat_ge (4 / θ)
  let N_maj1 := max 4 N_maj
  -- 3) `x ≥ max (104 ^ 4) ((16 * K + 8) ^ 4)` so `S.card ≥ 2 * K`.
  let X₀ := max (max (104 ^ 4) ((16 * K + 8) ^ 4)) (max (N_rpow + 2) (2 ^ (N_maj1 + 2)))
  filter_upwards [eventually_ge_atTop X₀] with x hx
  intro L D Q hprem
  obtain ⟨M₀, hM₀_mem, hM₀_lt⟩ := hprem
  have hx_104 : 104 ^ 4 ≤ x :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hx)
  have hx_K4 : (16 * K + 8) ^ 4 ≤ x :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hx)
  have hx_Nrpow : N_rpow + 2 ≤ x :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hx)
  have hx_Nmaj : 2 ^ (N_maj1 + 2) ≤ x :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hx)
  have hx2 : 2 ≤ x := by omega
  have hx16 : 16 ≤ x := by omega
  have hx_pos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (show 0 < x by omega)
  have hx_ge1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (show 1 ≤ x by omega)
  have hlogx_pos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  -- Establish `(x : ℝ) ^ (ε / 16) ≥ 12` and `L ≥ 5 * x`.
  have hrpow16_ge12 : (12 : ℝ) ≤ (x : ℝ) ^ (ε / 16) := by
    have hNx : ((12 : ℝ) ^ ((16 : ℝ) / ε)) ≤ (x : ℝ) := by
      exact hN_rpow.trans (by exact_mod_cast (show N_rpow ≤ x by omega))
    calc
      (12 : ℝ) = ((12 : ℝ) ^ ((16 : ℝ) / ε)) ^ (ε / 16) := by
        rw [← Real.rpow_mul (by norm_num), div_mul_div_cancel₀ hε_pos.ne',
          div_self (by norm_num), Real.rpow_one]
      _ ≤ (x : ℝ) ^ (ε / 16) := Real.rpow_le_rpow (by positivity) hNx (by positivity)
  have hrpow_eps_ge12 : (12 : ℝ) ≤ (x : ℝ) ^ ε := by
    calc
      (12 : ℝ) ≤ (x : ℝ) ^ (ε / 16) := hrpow16_ge12
      _ ≤ (x : ℝ) ^ ε := Real.rpow_le_rpow_of_exponent_le hx_ge1 (by linarith)
  have hceil_ge_12x : 12 * x ≤ ⌈(x : ℝ) ^ (1 + ε)⌉₊ := by
    have h1 : (12 * (x : ℝ)) ≤ (x : ℝ) ^ (1 + ε) := by
      rw [Real.rpow_add hx_pos, Real.rpow_one]
      nlinarith
    exact_mod_cast h1.trans (Nat.le_ceil _)
  have hL_ge_5x : 5 * x ≤ L := by dsimp [L]; omega
  have hL_ge2 : 2 ≤ L := by omega
  have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  -- Step 1: Bound `|S_maj(M)| ≤ (θ / 16) * L` for every shift `M : ℕ`.
  let P := (range (x + 1)).filter Nat.Prime
  have hP : ∀ p ∈ P, p.Prime := fun _ hp => (mem_filter.mp hp).2
  let f_term : ℕ → ℕ → ℝ := fun M d =>
    ((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ)) *
      ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
        Real.cos (2 * Real.pi * (r : ℝ) * ((M + L : ℕ) : ℝ) / (d : ℝ)) *
          (‖∑ u ∈ range L,
            Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 /
            (L : ℝ))
  have hmaj_all : ∀ M : ℕ,
      |∑ d ∈ Q.divisors.filter (fun d => 1 < d ∧ d ≤ D), f_term M d| ≤ (θ / 16) * (L : ℝ) := by
    intro M
    have h1 := OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1.ramanujan_major_arc_bound x M L D (by omega)
    have hL_pow : 2 ^ N_maj1 ≤ L := by
      have : 2 * 2 ^ N_maj1 ≤ x := by
        calc
          2 * 2 ^ N_maj1 ≤ 4 * 2 ^ N_maj1 := by omega
          _ = 2 ^ (N_maj1 + 2) := by ring
          _ ≤ x := hx_Nmaj
      omega
    have hlogL_ge : N_maj1 ≤ Nat.log 2 L + 1 := by
      have := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hL_pow
      omega
    have hlog_ge4 : (4 : ℝ) ≤ ((Nat.log 2 L + 1 : ℕ) : ℝ) := by
      exact_mod_cast (le_max_left 4 N_maj).trans hlogL_ge
    have hlog_ge_th : 4 / θ ≤ ((Nat.log 2 L + 1 : ℕ) : ℝ) :=
      hN_maj.trans (by exact_mod_cast (le_max_right 4 N_maj).trans hlogL_ge)
    have hD_le : (D : ℝ) ≤ (L : ℝ) / ((Nat.log 2 L + 1 : ℕ) : ℝ) := by
      rw [le_div_iff₀ (by positivity)]
      exact_mod_cast Nat.div_mul_le_self L (Nat.log 2 L + 1)
    have hDsq : (D : ℝ) ^ 2 ≤ ((L : ℝ) / ((Nat.log 2 L + 1 : ℕ) : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg D) hD_le 2
    have hratio : 3 / (4 * ((Nat.log 2 L + 1 : ℕ) : ℝ) ^ 2) ≤ θ / 16 := by
      have hsq : 16 / θ ≤ ((Nat.log 2 L + 1 : ℕ) : ℝ) ^ 2 := by
        calc
          16 / θ = 4 * (4 / θ) := by ring
          _ ≤ ((Nat.log 2 L + 1 : ℕ) : ℝ) * ((Nat.log 2 L + 1 : ℕ) : ℝ) :=
            mul_le_mul hlog_ge4 hlog_ge_th (by positivity) (by positivity)
          _ = ((Nat.log 2 L + 1 : ℕ) : ℝ) ^ 2 := (sq _).symm
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have hmul := (div_le_iff₀ hθ_pos).mp hsq
      linarith
    have h2 : 3 * (D : ℝ) ^ 2 / (4 * (L : ℝ)) ≤
        (3 / (4 * ((Nat.log 2 L + 1 : ℕ) : ℝ) ^ 2)) * (L : ℝ) := by
      have hln : ((Nat.log 2 L + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      calc
        3 * (D : ℝ) ^ 2 / (4 * (L : ℝ))
            ≤ 3 * ((L : ℝ) / ((Nat.log 2 L + 1 : ℕ) : ℝ)) ^ 2 / (4 * (L : ℝ)) := by gcongr
        _ = (3 / (4 * ((Nat.log 2 L + 1 : ℕ) : ℝ) ^ 2)) * (L : ℝ) := by field_simp
    exact h1.trans (h2.trans (mul_le_mul_of_nonneg_right hratio hL_pos.le))
  -- Exact decomposition `S_Fejer(M) / V(x) = L + S_maj(M) + S_min(M)` for every `M : ℕ`.
  let Vx : ℝ := ∏ p ∈ P, (1 - (p : ℝ)⁻¹)
  have hVx_lo : Real.exp (-11) / Real.log (x : ℝ) ≤ Vx := mertens_third_lower hx2
  have hVx_pos : 0 < Vx := lt_of_lt_of_le (by positivity) hVx_lo
  let S_fej : ℕ → ℝ := fun M =>
    (∑ u ∈ range L, ∑ v ∈ range L,
      (if ∀ p ≤ x, p.Prime → ¬ (p ∣ (M + L + u - v)) then (1 : ℝ) else 0)) / (L : ℝ)
  have hfej_decomp : ∀ M : ℕ,
      S_fej M = Vx * ((L : ℝ) +
        (∑ d ∈ Q.divisors.filter (fun d => 1 < d ∧ d ≤ D), f_term M d) +
        (∑ d ∈ Q.divisors.filter (fun d => D < d), f_term M d)) := by
    intro M
    have hid := OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1.ramanujan_fejer_identity x M L (by omega)
    have hQ_pos : 0 < Q := Finset.prod_pos fun p hp => (hP p hp).pos
    have hD_ge1 : 1 ≤ D := by
      dsimp [D]
      have hlt : Nat.log 2 L < L := Nat.log_lt_self 2 (by omega)
      exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    have hpart : Q.divisors = ({1} ∪ Q.divisors.filter (fun d => 1 < d ∧ d ≤ D)) ∪
        Q.divisors.filter (fun d => D < d) := by
      ext d
      simp only [mem_union, mem_singleton, mem_filter]
      constructor
      · intro hd
        have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 hQ_pos
        by_cases hdeq : d = 1
        · exact Or.inl (Or.inl hdeq)
        · by_cases hdD : d ≤ D
          · exact Or.inl (Or.inr ⟨hd, by omega, hdD⟩)
          · exact Or.inr ⟨hd, by omega⟩
      · rintro ((rfl | ⟨hd, _⟩) | ⟨hd, _⟩)
        · exact Nat.mem_divisors.mpr ⟨one_dvd Q, hQ_pos.ne'⟩
        · exact hd
        · exact hd
    have hdisj1 : Disjoint ({1} : Finset ℕ) (Q.divisors.filter (fun d => 1 < d ∧ d ≤ D)) := by
      rw [Finset.disjoint_left]; intro d h1 h2; rw [mem_singleton] at h1
      have := (mem_filter.mp h2).2.1; omega
    have hdisj2 : Disjoint ({1} ∪ Q.divisors.filter (fun d => 1 < d ∧ d ≤ D))
        (Q.divisors.filter (fun d => D < d)) := by
      rw [Finset.disjoint_left]; intro d h1 h2; have := (mem_filter.mp h2).2
      rcases mem_union.mp h1 with h1' | h1'
      · rw [mem_singleton] at h1'; omega
      · have := (mem_filter.mp h1').2.2; omega
    have hf1 : f_term M 1 = (L : ℝ) := by
      dsimp [f_term]
      have h0 : ({0} : Finset ℕ).filter (fun r => Nat.Coprime r 1) = {0} := by decide
      rw [h0]
      simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one, Nat.cast_one, div_one, one_mul,
        Finset.sum_singleton, Nat.cast_zero, mul_zero, zero_mul, Real.cos_zero, Complex.ofReal_zero,
        Complex.exp_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
        Complex.norm_natCast]
      field_simp
    dsimp [S_fej]
    rw [hid]
    congr 1
    conv_lhs => rw [hpart]
    rw [Finset.sum_union hdisj2, Finset.sum_union hdisj1, Finset.sum_singleton]
    change f_term M 1 + (∑ d ∈ Q.divisors.filter (fun d => 1 < d ∧ d ≤ D), f_term M d) +
        (∑ d ∈ Q.divisors.filter (fun d => D < d), f_term M d) = _
    rw [hf1]
  -- Step 2: Set `z = ⌊x ^ (ε / 8)⌋₊` and bound `z`-rough Fejér pairs at `M₀` via `selberg_rough_Icc_upper`.
  let z : ℕ := ⌊(x : ℝ) ^ (ε / 8)⌋₊
  have hz_gt_rpow16 : (x : ℝ) ^ (ε / 16) < (z : ℝ) := by
    have hsub := Nat.sub_one_lt_floor ((x : ℝ) ^ (ε / 8))
    have hsq : ((x : ℝ) ^ (ε / 16)) ^ 2 = (x : ℝ) ^ (ε / 8) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx_pos.le]
      congr 1; push_cast; ring
    nlinarith [hrpow16_ge12, hsq]
  have hz_ge2 : 2 ≤ z := by
    have : (12 : ℝ) < (z : ℝ) := lt_of_le_of_lt hrpow16_ge12 hz_gt_rpow16
    exact_mod_cast (show (2 : ℝ) ≤ (z : ℝ) by linarith)
  have hz_le_x4 : z ≤ x / 4 := by
    have hz_r : (z : ℝ) ≤ (x : ℝ) ^ (1 / 8 : ℝ) :=
      (Nat.floor_le (by positivity)).trans (Real.rpow_le_rpow_of_exponent_le hx_ge1 (by linarith))
    have hpow8 : ((x : ℝ) ^ (1 / 8 : ℝ)) ≤ Real.sqrt (x : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hx_ge1 (by norm_num)
    have hsqrt_x4 : Real.sqrt (x : ℝ) ≤ (x : ℝ) / 4 := by
      have hx16_r : (16 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx16
      have hsq : (4 * Real.sqrt (x : ℝ)) ^ 2 ≤ (x : ℝ) ^ 2 := by
        calc
          (4 * Real.sqrt (x : ℝ)) ^ 2 = 16 * (Real.sqrt (x : ℝ) * Real.sqrt (x : ℝ)) := by ring
          _ = 16 * (x : ℝ) := by rw [Real.mul_self_sqrt hx_pos.le]
          _ ≤ (x : ℝ) ^ 2 := by nlinarith
      have h4s : 4 * Real.sqrt (x : ℝ) ≤ (x : ℝ) := by
        nlinarith [Real.sqrt_nonneg x]
      linarith
    have hz_le_div_r : (z : ℝ) ≤ (x : ℝ) / 4 := hz_r.trans (hpow8.trans hsqrt_x4)
    have hmul4 : 4 * z ≤ x := by
      have : (4 * (z : ℝ)) ≤ (x : ℝ) := by linarith
      exact_mod_cast this
    omega
  have hlogz_ge : (ε / 16) * Real.log (x : ℝ) ≤ Real.log (z : ℝ) := by
    have h1 : Real.log ((x : ℝ) ^ (ε / 16)) ≤ Real.log (z : ℝ) :=
      Real.log_le_log (by positivity) hz_gt_rpow16.le
    rwa [Real.log_rpow hx_pos] at h1
  have hlogz_pos : 0 < Real.log (z : ℝ) := lt_of_lt_of_le (by positivity) hlogz_ge
  have hz_rough_M0 :
      (((Icc (M₀ + 1) (M₀ + 2 * L)).filter fun n => ∀ p ≤ z, p.Prime → ¬ (p ∣ n)).card : ℝ) ≤
        (64 * Real.exp 11 / ε) * (L : ℝ) * Vx := by
    have hsel := OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1_H2_R1_H2_R1.selberg_rough_Icc_upper
      hz_ge2 M₀ (2 * L)
    have hz7_le_x : (z : ℝ) ^ 7 ≤ (x : ℝ) := by
      have hz_r : (z : ℝ) ≤ (x : ℝ) ^ (1 / 8 : ℝ) :=
        (Nat.floor_le (by positivity)).trans (Real.rpow_le_rpow_of_exponent_le hx_ge1 (by linarith))
      calc
        (z : ℝ) ^ 7 ≤ ((x : ℝ) ^ (1 / 8 : ℝ)) ^ 7 := pow_le_pow_left₀ (Nat.cast_nonneg z) hz_r 7
        _ = (x : ℝ) ^ (7 / 8 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hx_pos.le]; congr 1; push_cast; ring
        _ ≤ (x : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx_ge1 (by norm_num)
        _ = (x : ℝ) := Real.rpow_one _
    have hz6_le : 4 * (z : ℝ) ^ 6 ≤ ((2 * L : ℕ) : ℝ) / Real.log (z : ℝ) := by
      rw [le_div_iff₀ hlogz_pos]
      have hlogz_le_z : Real.log (z : ℝ) ≤ (z : ℝ) := by
        linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < (z : ℝ) by exact_mod_cast (by omega : 0 < z))]
      have hmul : 4 * (z : ℝ) ^ 6 * Real.log (z : ℝ) ≤ 4 * (z : ℝ) ^ 7 := by
        calc
          4 * (z : ℝ) ^ 6 * Real.log (z : ℝ) ≤ 4 * (z : ℝ) ^ 6 * (z : ℝ) :=
            mul_le_mul_of_nonneg_left hlogz_le_z (by positivity)
          _ = 4 * (z : ℝ) ^ 7 := by ring
      have hxL_r : 5 * (x : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL_ge_5x
      push_cast
      linarith
    have hstep1 : (((Icc (M₀ + 1) (M₀ + 2 * L)).filter fun n => ∀ p ≤ z, p.Prime → ¬ (p ∣ n)).card : ℝ) ≤
        4 * (L : ℝ) / Real.log (z : ℝ) := by
      have : ((2 * L : ℕ) : ℝ) / Real.log (z : ℝ) + ((2 * L : ℕ) : ℝ) / Real.log (z : ℝ) =
          4 * (L : ℝ) / Real.log (z : ℝ) := by push_cast; ring
      linarith
    have hstep2 : 4 * (L : ℝ) / Real.log (z : ℝ) ≤ (64 / ε) * ((L : ℝ) / Real.log (x : ℝ)) := by
      have h1 : 4 * (L : ℝ) / Real.log (z : ℝ) ≤ 4 * (L : ℝ) / ((ε / 16) * Real.log (x : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hlogz_ge
      have h2 : 4 * (L : ℝ) / ((ε / 16) * Real.log (x : ℝ)) =
          (64 / ε) * ((L : ℝ) / Real.log (x : ℝ)) := by field_simp; ring
      linarith
    have hstep3 : (L : ℝ) / Real.log (x : ℝ) ≤ Real.exp 11 * (L : ℝ) * Vx := by
      have hmul := mul_le_mul_of_nonneg_left hVx_lo (show 0 ≤ Real.exp 11 * (L : ℝ) by positivity)
      have hlhs : Real.exp 11 * (L : ℝ) * (Real.exp (-11) / Real.log (x : ℝ)) =
          (L : ℝ) / Real.log (x : ℝ) := by
        have hexp : Real.exp 11 * Real.exp (-11) = 1 := by rw [← Real.exp_add]; norm_num
        calc
          Real.exp 11 * (L : ℝ) * (Real.exp (-11) / Real.log (x : ℝ))
              = (Real.exp 11 * Real.exp (-11)) * ((L : ℝ) / Real.log (x : ℝ)) := by ring
          _ = (L : ℝ) / Real.log (x : ℝ) := by rw [hexp, one_mul]
      linarith
    calc
      (((Icc (M₀ + 1) (M₀ + 2 * L)).filter fun n => ∀ p ≤ z, p.Prime → ¬ (p ∣ n)).card : ℝ)
          ≤ (64 / ε) * ((L : ℝ) / Real.log (x : ℝ)) := hstep1.trans hstep2
      _ ≤ (64 / ε) * (Real.exp 11 * (L : ℝ) * Vx) :=
          mul_le_mul_of_nonneg_left hstep3 (by positivity)
      _ = (64 * Real.exp 11 / ε) * (L : ℝ) * Vx := by ring
  -- Step 3: Partition `S = (Ioc (x / 4) x).filter Nat.Prime` into `K` buckets of size `m = S.card / K`.
  let S := (Ioc (x / 4) x).filter Nat.Prime
  have hS_sub_P : S ⊆ P := by
    intro p hp
    obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
    have hpx := (mem_Ioc.mp hpI).2
    exact mem_filter.mpr ⟨mem_range.mpr (by omega), hpp⟩
  have hScard_lo : (x : ℝ) / (8 * Real.log (x : ℝ)) ≤ (S.card : ℝ) := primes_Ioc_quarter_card hx_104
  have h2K_le_S : 2 * K ≤ S.card := two_mul_le_primes_Ioc_quarter hx_104 hx_K4
  clear hx_104 hx_K4 hx_Nrpow hx_Nmaj hrpow16_ge12 hrpow_eps_ge12 hceil_ge_12x hN_rpow hN_maj
  let m : ℕ := S.card / K
  have hm_lo : (x : ℝ) / (16 * (K : ℝ) * Real.log (x : ℝ)) ≤ (m : ℝ) := by
    have hm1 : 1 ≤ m := (Nat.le_div_iff_mul_le hK_pos).mpr (by omega)
    have hScard_lt : S.card < (m + 1) * K := by
      rw [Nat.add_mul, Nat.one_mul]
      have hdm : m * K + S.card % K = S.card := by
        dsimp [m]; rw [Nat.mul_comm]; exact Nat.div_add_mod S.card K
      have hrm := Nat.mod_lt S.card hK_pos
      omega
    have h2mK : S.card ≤ 2 * (m * K) := by
      rw [Nat.add_mul, Nat.one_mul] at hScard_lt
      have hKm : K ≤ m * K := by
        calc
          K = 1 * K := (Nat.one_mul K).symm
          _ ≤ m * K := Nat.mul_le_mul_right K hm1
      omega
    have h2mK_r : (S.card : ℝ) ≤ 2 * (m : ℝ) * (K : ℝ) := by
      have : (S.card : ℝ) ≤ 2 * ((m : ℝ) * (K : ℝ)) := by exact_mod_cast h2mK
      linarith
    rw [div_le_iff₀ (by positivity)]
    have h1 : (x : ℝ) ≤ (S.card : ℝ) * (8 * Real.log (x : ℝ)) :=
      (div_le_iff₀ (by positivity)).mp hScard_lo
    calc
      (x : ℝ) ≤ (S.card : ℝ) * (8 * Real.log (x : ℝ)) := h1
      _ ≤ (2 * (m : ℝ) * (K : ℝ)) * (8 * Real.log (x : ℝ)) :=
        mul_le_mul_of_nonneg_right h2mK_r (by positivity)
      _ = (m : ℝ) * (16 * (K : ℝ) * Real.log (x : ℝ)) := by ring
  obtain ⟨T, hT_props, hT_pw⟩ := exists_disjoint_buckets S K m (by dsimp [m]; rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _)
  -- Step 4: Bound sum of uncovered Fejér pairs across the `K` disjoint buckets and pick `j₀ < K`.
  let UV := range L ×ˢ range L
  let B : ℕ → Finset (ℕ × ℕ) := fun j =>
    UV.filter fun uv =>
      (∃ q ∈ T j, q ∣ (M₀ + L + uv.1 - uv.2)) ∧
      (∀ p ∈ P \ T j, ¬ (p ∣ (M₀ + L + uv.1 - uv.2)))
  have hB_pw : (range K : Set ℕ).PairwiseDisjoint B := by
    intro i hi j hj hij
    rw [Function.onFun, Finset.disjoint_left]
    intro uv huv_i huv_j
    obtain ⟨_, ⟨q, hqTi, hq_dvd⟩, _⟩ := mem_filter.mp huv_i
    obtain ⟨_, _, havoid_j⟩ := mem_filter.mp huv_j
    have hdisj_ij : Disjoint (T i) (T j) := hT_pw hi hj hij
    have hq_not_Tj : q ∉ T j := Finset.disjoint_left.mp hdisj_ij hqTi
    have hqP : q ∈ P := hS_sub_P ((hT_props i (mem_coe.mp hi)).1 hqTi)
    exact havoid_j q (mem_sdiff.mpr ⟨hqP, hq_not_Tj⟩) hq_dvd
  let Z_uv := UV.filter fun uv => ∀ p ≤ z, p.Prime → ¬ (p ∣ (M₀ + L + uv.1 - uv.2))
  have hB_sub_Z : (range K).biUnion B ⊆ Z_uv := by
    intro uv huv
    obtain ⟨j, hj, huv_j⟩ := mem_biUnion.mp huv
    obtain ⟨huv_UV, _, havoid_j⟩ := mem_filter.mp huv_j
    refine mem_filter.mpr ⟨huv_UV, fun p hpz hpp => ?_⟩
    have hpP : p ∈ P := mem_filter.mpr ⟨mem_range.mpr (by omega), hpp⟩
    have hp_not_Tj : p ∉ T j := by
      intro hpTj
      have hpS : p ∈ S := (hT_props j hj).1 hpTj
      have hp_gt : x / 4 < p := (mem_Ioc.mp (mem_filter.mp hpS).1).1
      omega
    exact havoid_j p (mem_sdiff.mpr ⟨hpP, hp_not_Tj⟩)
  have hZ_uv_card : (Z_uv.card : ℝ) ≤
      (L : ℝ) * (((Icc (M₀ + 1) (M₀ + 2 * L)).filter fun n => ∀ p ≤ z, p.Prime → ¬ (p ∣ n)).card : ℝ) := by
    have hpart_u : Z_uv = (range L).biUnion (fun u =>
        ((range L).filter fun v => ∀ p ≤ z, p.Prime → ¬ (p ∣ (M₀ + L + u - v))).image (fun v => (u, v))) := by
      ext ⟨u, v⟩
      simp only [Z_uv, UV, mem_filter, mem_product, mem_biUnion, mem_image]
      constructor
      · rintro ⟨⟨hu, hv⟩, hr⟩
        exact ⟨u, hu, v, ⟨hv, hr⟩, rfl⟩
      · rintro ⟨u', hu', v', ⟨hv', hr'⟩, heq⟩
        cases heq
        exact ⟨⟨hu', hv'⟩, hr'⟩
    have hpw_u : (range L : Set ℕ).PairwiseDisjoint (fun u =>
        ((range L).filter fun v => ∀ p ≤ z, p.Prime → ¬ (p ∣ (M₀ + L + u - v))).image (fun v => (u, v))) := by
      intro u₁ _ u₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro p hp₁ hp₂
      obtain ⟨_, _, heq₁⟩ := mem_image.mp hp₁
      obtain ⟨_, _, heq₂⟩ := mem_image.mp hp₂
      rw [← heq₁] at heq₂
      exact hne (Prod.mk.inj heq₂).1.symm
    have hnat : Z_uv.card ≤ ∑ _u ∈ range L,
        ((Icc (M₀ + 1) (M₀ + 2 * L)).filter fun n => ∀ p ≤ z, p.Prime → ¬ (p ∣ n)).card := by
      rw [hpart_u, Finset.card_biUnion hpw_u]
      refine Finset.sum_le_sum fun u hu => ?_
      have hu_lt : u < L := mem_range.mp hu
      rw [Finset.card_image_of_injective _ (fun v₁ v₂ h => (Prod.mk.inj h).2)]
      refine Finset.card_le_card_of_injOn (fun v => M₀ + L + u - v) ?_ ?_
      · intro v hv
        rw [mem_coe, mem_filter, mem_range] at hv
        dsimp only
        rw [mem_coe, mem_filter, mem_Icc]
        exact ⟨⟨by omega, by omega⟩, hv.2⟩
      · intro v₁ hv₁ v₂ hv₂ heq
        rw [mem_coe, mem_filter, mem_range] at hv₁ hv₂
        dsimp only at heq
        omega
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hnat
    exact_mod_cast hnat
  have hsum_B : ∑ j ∈ range K, ((B j).card : ℝ) ≤
      (64 * Real.exp 11 / ε) * (L : ℝ) ^ 2 * Vx := by
    have h1 : ∑ j ∈ range K, (B j).card ≤ Z_uv.card := by
      rw [← Finset.card_biUnion hB_pw]
      exact Finset.card_le_card hB_sub_Z
    have h1_r : ∑ j ∈ range K, ((B j).card : ℝ) ≤ (Z_uv.card : ℝ) := by exact_mod_cast h1
    calc
      ∑ j ∈ range K, ((B j).card : ℝ) ≤ (Z_uv.card : ℝ) := h1_r
      _ ≤ (L : ℝ) * (((Icc (M₀ + 1) (M₀ + 2 * L)).filter fun n => ∀ p ≤ z, p.Prime → ¬ (p ∣ n)).card : ℝ) := hZ_uv_card
      _ ≤ (L : ℝ) * ((64 * Real.exp 11 / ε) * (L : ℝ) * Vx) :=
          mul_le_mul_of_nonneg_left hz_rough_M0 hL_pos.le
      _ = (64 * Real.exp 11 / ε) * (L : ℝ) ^ 2 * Vx := by ring
  -- Pigeonhole: there exists `j₀ ∈ range K` with `(B j₀).card / L ≤ (θ / 8) * L * Vx`.
  have hj₀_exists : ∃ j₀ ∈ range K, ((B j₀).card : ℝ) ≤ (θ / 8) * (L : ℝ) ^ 2 * Vx := by
    apply exists_le_of_sum_le hK_pos (fun j => ((B j).card : ℝ)) ((θ / 8) * (L : ℝ) ^ 2 * Vx)
    have hK_mul : (64 * Real.exp 11 / ε) ≤ (K : ℝ) * (θ / 8) := by
      have h1 := (div_le_iff₀ (mul_pos hθ_pos hε_pos)).mp hK_ge
      rw [div_le_iff₀ hε_pos]
      linarith
    have h2 := mul_le_mul_of_nonneg_right hK_mul (show 0 ≤ (L : ℝ) ^ 2 * Vx by positivity)
    linarith [hsum_B]
  obtain ⟨j₀, hj₀_mem, hj₀_raw⟩ := hj₀_exists
  have hj₀_bound : ((B j₀).card : ℝ) / (L : ℝ) ≤ (θ / 8) * (L : ℝ) * Vx := by
    rw [div_le_iff₀ hL_pos]
    nlinarith [hj₀_raw]
  -- Step 5: Apply `crt_subcube_card` to `T j₀ ⊆ P` and show every CRT neighbor has `S_min(M) < -(3*θ/4)*L`.
  have hTj0_sub_P : T j₀ ⊆ P := (hT_props j₀ hj₀_mem).1.trans hS_sub_P
  let good : ℕ → Prop := fun M =>
    ∑ d ∈ Q.divisors.filter (fun d => D < d), f_term M d < -((3 * θ / 4) * (L : ℝ))
  have hgood_subcube : ∀ M ∈ range Q, (∀ p ∈ P \ T j₀, M % p = M₀ % p) → good M := by
    intro M _ hcong
    -- Compare `S_fej M` with `S_fej M₀ + (B j₀).card / L`.
    have hfej_diff : S_fej M ≤ S_fej M₀ + ((B j₀).card : ℝ) / (L : ℝ) := by
      dsimp [S_fej]
      rw [← add_div]
      refine div_le_div_of_nonneg_right ?_ hL_pos.le
      let R_M := UV.filter fun uv => ∀ p ≤ x, p.Prime → ¬ (p ∣ (M + L + uv.1 - uv.2))
      let R_M0 := UV.filter fun uv => ∀ p ≤ x, p.Prime → ¬ (p ∣ (M₀ + L + uv.1 - uv.2))
      have hsum_eq : ∀ N : ℕ,
          (∑ u ∈ range L, ∑ v ∈ range L,
            (if ∀ p ≤ x, p.Prime → ¬ (p ∣ (N + L + u - v)) then (1 : ℝ) else 0)) =
          ((UV.filter fun uv => ∀ p ≤ x, p.Prime → ¬ (p ∣ (N + L + uv.1 - uv.2))).card : ℝ) := by
        intro N
        rw [← Finset.sum_product', Finset.sum_boole]
      rw [hsum_eq M, hsum_eq M₀]
      have hsub_union : R_M ⊆ R_M0 ∪ B j₀ := by
        intro uv huv
        obtain ⟨huv_UV, hrough_M⟩ := mem_filter.mp huv
        have huv_lt := mem_product.mp huv_UV
        have hu_lt : uv.1 < L := mem_range.mp huv_lt.1
        have hv_lt : uv.2 < L := mem_range.mp huv_lt.2
        by_cases hrough_M0 : ∀ p ≤ x, p.Prime → ¬ (p ∣ (M₀ + L + uv.1 - uv.2))
        · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨huv_UV, hrough_M0⟩))
        · refine mem_union.mpr (Or.inr (mem_filter.mpr ⟨huv_UV, ?_, ?_⟩))
          · push Not at hrough_M0
            obtain ⟨q, hqx, hqp, hq_dvd⟩ := hrough_M0
            have hqP : q ∈ P := mem_filter.mpr ⟨mem_range.mpr (by omega), hqp⟩
            have hqTj : q ∈ T j₀ := by
              by_contra hq_not
              have hmod_eq : M % q = M₀ % q := hcong q (mem_sdiff.mpr ⟨hqP, hq_not⟩)
              have hint_dvd : (q : ℤ) ∣ ((M : ℤ) - (M₀ : ℤ)) :=
                Int.modEq_iff_dvd.mp (Int.natCast_modEq_iff.mpr hmod_eq).symm
              have hdiff_eq : ((M + L + uv.1 - uv.2 : ℕ) : ℤ) - ((M₀ + L + uv.1 - uv.2 : ℕ) : ℤ) =
                  (M : ℤ) - (M₀ : ℤ) := by
                rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
                push_cast; ring
              have hdvd_M0_z : (q : ℤ) ∣ ((M₀ + L + uv.1 - uv.2 : ℕ) : ℤ) :=
                Int.ofNat_dvd.mpr hq_dvd
              have hdvd_M_z : (q : ℤ) ∣ ((M + L + uv.1 - uv.2 : ℕ) : ℤ) := by
                have := dvd_add hdvd_M0_z (hdiff_eq ▸ hint_dvd)
                simpa using this
              exact hrough_M q hqx hqp (Int.ofNat_dvd.mp hdvd_M_z)
            exact ⟨q, hqTj, hq_dvd⟩
          · intro p hp_sdiff hp_dvd_M0
            have hpP : p ∈ P := (mem_sdiff.mp hp_sdiff).1
            have hp_lt_x : p ≤ x := by have := mem_range.mp (mem_filter.mp hpP).1; omega
            have hpp : p.Prime := (mem_filter.mp hpP).2
            have hmod_eq : M % p = M₀ % p := hcong p hp_sdiff
            have hint_dvd : (p : ℤ) ∣ ((M : ℤ) - (M₀ : ℤ)) :=
              Int.modEq_iff_dvd.mp (Int.natCast_modEq_iff.mpr hmod_eq).symm
            have hdiff_eq : ((M + L + uv.1 - uv.2 : ℕ) : ℤ) - ((M₀ + L + uv.1 - uv.2 : ℕ) : ℤ) =
                (M : ℤ) - (M₀ : ℤ) := by
              rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
              push_cast; ring
            have hdvd_M0_z : (p : ℤ) ∣ ((M₀ + L + uv.1 - uv.2 : ℕ) : ℤ) :=
              Int.ofNat_dvd.mpr hp_dvd_M0
            have hdvd_M_z : (p : ℤ) ∣ ((M + L + uv.1 - uv.2 : ℕ) : ℤ) := by
              have := dvd_add hdvd_M0_z (hdiff_eq ▸ hint_dvd)
              simpa using this
            exact hrough_M p hp_lt_x hpp (Int.ofNat_dvd.mp hdvd_M_z)
      have hcard_le : R_M.card ≤ R_M0.card + (B j₀).card :=
        (Finset.card_le_card hsub_union).trans (Finset.card_union_le _ _)
      exact_mod_cast hcard_le
    -- Convert `hfej_diff` to `S_min(M) < -(3*θ/4)*L`.
    have hmaj_M0 : ∑ d ∈ Q.divisors.filter (fun d => 1 < d ∧ d ≤ D), f_term M₀ d ≤
        (θ / 16) * (L : ℝ) := (abs_le.mp (hmaj_all M₀)).2
    have hmaj_M : -((θ / 16) * (L : ℝ)) ≤
        ∑ d ∈ Q.divisors.filter (fun d => 1 < d ∧ d ≤ D), f_term M d := (abs_le.mp (hmaj_all M)).1
    have hfej_M0_lt : S_fej M₀ < Vx * ((1 - 15 * θ / 16) * (L : ℝ)) := by
      rw [hfej_decomp M₀]
      have h1 : (L : ℝ) + (∑ d ∈ Q.divisors.filter (fun d => 1 < d ∧ d ≤ D), f_term M₀ d) +
          (∑ d ∈ Q.divisors.filter (fun d => D < d), f_term M₀ d) <
          (1 - 15 * θ / 16) * (L : ℝ) := by linarith [hM₀_lt, hmaj_M0]
      exact mul_lt_mul_of_pos_left h1 hVx_pos
    have hfej_M_lt : S_fej M < Vx * ((1 - 13 * θ / 16) * (L : ℝ)) := by
      have hB_le : ((B j₀).card : ℝ) / (L : ℝ) ≤ Vx * ((θ / 8) * (L : ℝ)) := by
        have : (θ / 8) * (L : ℝ) * Vx = Vx * ((θ / 8) * (L : ℝ)) := by ring
        linarith [hj₀_bound]
      have hlin_vx : Vx * ((1 - 15 * θ / 16) * (L : ℝ)) + Vx * ((θ / 8) * (L : ℝ)) =
          Vx * ((1 - 13 * θ / 16) * (L : ℝ)) := by ring
      linarith [hfej_diff, hfej_M0_lt, hB_le, hlin_vx]
    rw [hfej_decomp M] at hfej_M_lt
    have hsum_M_lt : (L : ℝ) + (∑ d ∈ Q.divisors.filter (fun d => 1 < d ∧ d ≤ D), f_term M d) +
        (∑ d ∈ Q.divisors.filter (fun d => D < d), f_term M d) <
        (1 - 13 * θ / 16) * (L : ℝ) := lt_of_mul_lt_mul_left hfej_M_lt hVx_pos.le
    dsimp [good]
    have hlin_end : (1 - 13 * θ / 16) * (L : ℝ) - (L : ℝ) + (θ / 16) * (L : ℝ) =
        -((3 * θ / 4) * (L : ℝ)) := by ring
    linarith [hsum_M_lt, hmaj_M, hlin_end]
  have hsubcube := OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1_H2_R1_H2_R1.crt_subcube_card
    hP hTj0_sub_P M₀ good hgood_subcube
  -- Step 6: Show `(Q : ℝ) ^ (c₁ * θ * ε) ≤ (∏ p ∈ T j₀, p : ℝ)`.
  have hprod_ge_rpow : (Q : ℝ) ^ (c₁ * θ * ε) ≤ ((∏ p ∈ T j₀, p : ℕ) : ℝ) := by
    have hQ_pos_r : (0 : ℝ) < (Q : ℝ) := by
      exact_mod_cast (Finset.prod_pos fun p hp => (hP p hp).pos)
    have hQt_pos_r : (0 : ℝ) < ((∏ p ∈ T j₀, p : ℕ) : ℝ) := by
      exact_mod_cast (Finset.prod_pos fun p hp => (hP p (hTj0_sub_P hp)).pos)
    rw [Real.rpow_def_of_pos hQ_pos_r, ← Real.exp_log hQt_pos_r]
    apply Real.exp_le_exp.mpr
    have hlogQ_le : Real.log (Q : ℝ) ≤ 2 * (x : ℝ) := by
      have hth := Chebyshev.theta_le_log4_mul_x hx_pos.le
      have hlogQ_eq : Real.log (Q : ℝ) = Chebyshev.theta (x : ℝ) := by
        dsimp [Q]
        rw [Nat.cast_prod, Real.log_prod (fun p hp => by exact_mod_cast (hP p hp).pos.ne'),
          Chebyshev.theta]
        congr 1
        ext p
        simp only [mem_filter, mem_range, mem_Ioc, Nat.floor_natCast]
        exact ⟨fun ⟨hpx, hpp⟩ => ⟨⟨hpp.pos, by omega⟩, hpp⟩,
          fun ⟨⟨_, hpx⟩, hpp⟩ => ⟨by omega, hpp⟩⟩
      have hlog4_le2 : Real.log 4 ≤ 2 := by
        have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]
          push_cast; rfl
        linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
      rw [hlogQ_eq]
      exact hth.trans (mul_le_mul_of_nonneg_right hlog4_le2 hx_pos.le)
    have hlogQt_lo : (x : ℝ) / (32 * (K : ℝ)) ≤ Real.log ((∏ p ∈ T j₀, p : ℕ) : ℝ) := by
      rw [Nat.cast_prod, Real.log_prod (fun p hp => by exact_mod_cast (hP p (hTj0_sub_P hp)).pos.ne')]
      have hp_log_lo : ∀ p ∈ T j₀, (1 / 2 : ℝ) * Real.log (x : ℝ) ≤ Real.log (p : ℝ) := by
        intro p hp
        have hpS : p ∈ S := (hT_props j₀ hj₀_mem).1 hp
        have hp_gt : x / 4 < p := (mem_Ioc.mp (mem_filter.mp hpS).1).1
        have hp_ge_x4 : (x : ℝ) / 4 ≤ (p : ℝ) := by
          have hdm := Nat.div_add_mod x 4
          have hrm := Nat.mod_lt x (by norm_num : 0 < 4)
          have hnat : x < 4 * p := by omega
          have hr : (x : ℝ) < 4 * (p : ℝ) := by exact_mod_cast hnat
          linarith
        have hsqrt_x4 : Real.sqrt (x : ℝ) ≤ (p : ℝ) := by
          have hx16_r : (16 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx16
          have hsq : (4 * Real.sqrt (x : ℝ)) ^ 2 ≤ (x : ℝ) ^ 2 := by
            calc
              (4 * Real.sqrt (x : ℝ)) ^ 2 = 16 * (Real.sqrt (x : ℝ) * Real.sqrt (x : ℝ)) := by ring
              _ = 16 * (x : ℝ) := by rw [Real.mul_self_sqrt hx_pos.le]
              _ ≤ (x : ℝ) ^ 2 := by nlinarith
          have h4s : 4 * Real.sqrt (x : ℝ) ≤ (x : ℝ) := by nlinarith [Real.sqrt_nonneg x]
          linarith
        have hls : Real.log (Real.sqrt (x : ℝ)) ≤ Real.log (p : ℝ) :=
          Real.log_le_log (Real.sqrt_pos.mpr hx_pos) hsqrt_x4
        rw [Real.log_sqrt hx_pos.le] at hls
        linarith
      have hcard_Tj0 : ((T j₀).card : ℝ) = (m : ℝ) := by
        exact_mod_cast (hT_props j₀ hj₀_mem).2
      calc
        (x : ℝ) / (32 * (K : ℝ))
            = ((x : ℝ) / (16 * (K : ℝ) * Real.log (x : ℝ))) * ((1 / 2 : ℝ) * Real.log (x : ℝ)) := by
              field_simp; ring
        _ ≤ (m : ℝ) * ((1 / 2 : ℝ) * Real.log (x : ℝ)) :=
            mul_le_mul_of_nonneg_right hm_lo (by positivity)
        _ = ∑ _p ∈ T j₀, ((1 / 2 : ℝ) * Real.log (x : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul, hcard_Tj0]
        _ ≤ ∑ p ∈ T j₀, Real.log (p : ℝ) := Finset.sum_le_sum hp_log_lo
    have hc1_le : Real.log (Q : ℝ) * (c₁ * θ * ε) ≤ (x : ℝ) / (32 * (K : ℝ)) := by
      have h1 : Real.log (Q : ℝ) * (c₁ * θ * ε) ≤ (2 * (x : ℝ)) * (c₁ * θ * ε) :=
        mul_le_mul_of_nonneg_right hlogQ_le (by positivity)
      have h2 : (2 * (x : ℝ)) * (c₁ * θ * ε) =
          (x : ℝ) / (32 * (1024 * Real.exp 11 / (θ * ε))) := by
        dsimp [c₁]
        have hθ_ne : θ ≠ 0 := hθ_pos.ne'
        have hε_ne : ε ≠ 0 := hε_pos.ne'
        field_simp
        ring
      have h3 : (x : ℝ) / (32 * (1024 * Real.exp 11 / (θ * ε))) ≤ (x : ℝ) / (32 * (K : ℝ)) :=
        div_le_div_of_nonneg_left hx_pos.le (by positivity) (by linarith)
      exact h1.trans (h2.le.trans h3)
    exact hc1_le.trans hlogQt_lo
  have hsub_r : ((∏ p ∈ T j₀, p : ℕ) : ℝ) ≤ (((range Q).filter good).card : ℝ) :=
    Nat.cast_le.mpr hsubcube
  exact hprod_ge_rpow.trans hsub_r
