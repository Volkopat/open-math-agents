import OMAStatements.S_oeis_a214619

namespace OMA.S_oeis_a214619_Proof

open OMA.S_oeis_a214619

lemma minFac_six_mul_add_three (k : ℕ) : (6 * k + 3).minFac = 3 := by
  have hne1 : 6 * k + 3 ≠ 1 := by omega
  have hp : (6 * k + 3).minFac.Prime := Nat.minFac_prime hne1
  have h2 : 2 ≤ (6 * k + 3).minFac := hp.two_le
  have hle : (6 * k + 3).minFac ≤ 3 :=
    Nat.minFac_le_of_dvd (by decide) ⟨2 * k + 1, by omega⟩
  have hne2 : (6 * k + 3).minFac ≠ 2 := by
    intro h
    rw [Nat.minFac_eq_two_iff] at h
    omega
  omega

lemma card_even_or_mult3 (N : ℕ) :
    N / 2 + N / 6 ≤
      ((Finset.Icc 1 N).filter (fun n => 2 ≤ n ∧ (n.minFac = 2 ∨ n.minFac = 3))).card := by
  let S2 : Finset ℕ := (Finset.Icc 1 (N / 2)).image (2 * ·)
  let S3 : Finset ℕ := (Finset.range (N / 6)).image (fun k => 6 * k + 3)
  have hS2_card : S2.card = N / 2 := by
    rw [Finset.card_image_of_injective _ (fun a b h => by omega)]
    simp
  have hS3_card : S3.card = N / 6 := by
    rw [Finset.card_image_of_injective _ (fun a b h => by omega)]
    simp
  have hdisj : Disjoint S2 S3 := by
    rw [Finset.disjoint_left]
    intro x hx2 hx3
    rcases Finset.mem_image.mp hx2 with ⟨a, _, rfl⟩
    rcases Finset.mem_image.mp hx3 with ⟨b, _, h⟩
    omega
  have hsub : S2 ∪ S3 ⊆ (Finset.Icc 1 N).filter
      (fun n => 2 ≤ n ∧ (n.minFac = 2 ∨ n.minFac = 3)) := by
    intro x hx
    rw [Finset.mem_union] at hx
    rcases hx with hx2 | hx3
    · rcases Finset.mem_image.mp hx2 with ⟨k, hk, rfl⟩
      rw [Finset.mem_Icc] at hk
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, by omega⟩, by omega, Or.inl ?_⟩
      exact (Nat.minFac_eq_two_iff _).mpr ⟨k, rfl⟩
    · rcases Finset.mem_image.mp hx3 with ⟨k, hk, rfl⟩
      rw [Finset.mem_range] at hk
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, by omega⟩, by omega, Or.inr (minFac_six_mul_add_three k)⟩
  calc N / 2 + N / 6 = S2.card + S3.card := by rw [hS2_card, hS3_card]
    _ = (S2 ∪ S3).card := (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ ((Finset.Icc 1 N).filter
        (fun n => 2 ≤ n ∧ (n.minFac = 2 ∨ n.minFac = 3))).card := Finset.card_le_card hsub

lemma sup_primeFactors_mem {n : ℕ} (hn : 2 ≤ n) :
    n.primeFactors.sup id ∈ n.primeFactors := by
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  rcases Finset.exists_mem_eq_sup n.primeFactors hne id with ⟨p, hp, hsup⟩
  rwa [hsup]

lemma card_large_prime_factor_le (N L : ℕ) (hL : 1 ≤ L) :
    ((Finset.Icc 1 N).filter (fun n => ∃ p ∈ n.primeFactors, N / L < p)).card ≤
      ∑ k ∈ Finset.Ico 1 L, Nat.primeCounting (N / k) := by
  let B := (Finset.Icc 1 N).filter (fun n => ∃ p ∈ n.primeFactors, N / L < p)
  let T := (Finset.Ico 1 L).sigma (fun k => Nat.primesLE (N / k))
  let g : ℕ → Σ _ : ℕ, ℕ := fun n => ⟨n / n.primeFactors.sup id, n.primeFactors.sup id⟩
  have hg_mem : ∀ n ∈ B, g n ∈ T := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    rcases hn with ⟨⟨hn1, hnN⟩, p, hp, hpL⟩
    have hn2 : 2 ≤ n := by
      by_contra hlt
      have : n = 1 := by omega
      subst this
      simp at hp
    have hq_mem : n.primeFactors.sup id ∈ n.primeFactors := sup_primeFactors_mem hn2
    have hq_prime : (n.primeFactors.sup id).Prime := Nat.prime_of_mem_primeFactors hq_mem
    have hq_dvd : n.primeFactors.sup id ∣ n := Nat.dvd_of_mem_primeFactors hq_mem
    have hq_ge : p ≤ n.primeFactors.sup id := Finset.le_sup (f := id) hp
    have hqL : N / L < n.primeFactors.sup id := lt_of_lt_of_le hpL hq_ge
    have hq_pos : 0 < n.primeFactors.sup id := hq_prime.pos
    have hq_le_n : n.primeFactors.sup id ≤ n := Nat.le_of_dvd (by omega) hq_dvd
    have hk_pos : 1 ≤ n / n.primeFactors.sup id := Nat.div_pos hq_le_n hq_pos
    have hmul : n.primeFactors.sup id * (n / n.primeFactors.sup id) = n :=
      Nat.mul_div_cancel' hq_dvd
    have hNL_lt : N < (N / L + 1) * L := by
      rw [add_mul, one_mul]
      exact Nat.lt_div_mul_add (by omega : 0 < L) (a := N)
    have hk_lt_L : n / n.primeFactors.sup id < L := by
      have h1 : n.primeFactors.sup id * (n / n.primeFactors.sup id) <
          n.primeFactors.sup id * L := by
        calc n.primeFactors.sup id * (n / n.primeFactors.sup id) = n := hmul
          _ ≤ N := hnN
          _ < (N / L + 1) * L := hNL_lt
          _ ≤ n.primeFactors.sup id * L := Nat.mul_le_mul_right L hqL
      exact Nat.lt_of_mul_lt_mul_left h1
    have hq_le_div : n.primeFactors.sup id ≤ N / (n / n.primeFactors.sup id) := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      rw [hmul]
      exact hnN
    rw [Finset.mem_sigma, Finset.mem_Ico, Nat.mem_primesLE]
    exact ⟨⟨hk_pos, hk_lt_L⟩, hq_le_div, hq_prime⟩
  have hg_inj : Set.InjOn g (B : Set ℕ) := by
    intro n₁ hn₁ n₂ hn₂ hEq
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hn₁ hn₂
    rcases hn₁ with ⟨_, p₁, hp₁, _⟩
    rcases hn₂ with ⟨_, p₂, hp₂, _⟩
    have hn₁2 : 2 ≤ n₁ := by
      by_contra hlt
      have : n₁ = 1 := by omega
      subst this
      simp at hp₁
    have hn₂2 : 2 ≤ n₂ := by
      by_contra hlt
      have : n₂ = 1 := by omega
      subst this
      simp at hp₂
    have hq₁_dvd : n₁.primeFactors.sup id ∣ n₁ :=
      Nat.dvd_of_mem_primeFactors (sup_primeFactors_mem hn₁2)
    have hq₂_dvd : n₂.primeFactors.sup id ∣ n₂ :=
      Nat.dvd_of_mem_primeFactors (sup_primeFactors_mem hn₂2)
    have h1 : n₁ / n₁.primeFactors.sup id = n₂ / n₂.primeFactors.sup id :=
      congr_arg Sigma.fst hEq
    have h2 : n₁.primeFactors.sup id = n₂.primeFactors.sup id := by
      have := congr_arg Sigma.snd hEq
      simpa [g] using this
    calc n₁ = n₁.primeFactors.sup id * (n₁ / n₁.primeFactors.sup id) :=
          (Nat.mul_div_cancel' hq₁_dvd).symm
      _ = n₂.primeFactors.sup id * (n₂ / n₂.primeFactors.sup id) := by rw [h1, h2]
      _ = n₂ := Nat.mul_div_cancel' hq₂_dvd
  calc B.card ≤ T.card := Finset.card_le_card_of_injOn g hg_mem hg_inj
    _ = ∑ k ∈ Finset.Ico 1 L, (Nat.primesLE (N / k)).card := Finset.card_sigma _ _
    _ = ∑ k ∈ Finset.Ico 1 L, Nat.primeCounting (N / k) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      exact Nat.primesLE_card_eq_primeCounting (N / k)

open Classical in
lemma card_unmatched_le (N y : ℕ) :
    ((Finset.Icc 1 N).filter
      (fun n => 2 ≤ n ∧ (n.minFac = 2 ∨ n.minFac = 3) ∧
        n.primeFactors.sup id ≤ y ∧ ¬ Occurs n)).card ≤
      2 * (Nat.log 10 N + 2) ^ 10 * (y + 1) := by
  let A := (Finset.Icc 1 N).filter
    (fun n => 2 ≤ n ∧ (n.minFac = 2 ∨ n.minFac = 3) ∧
      n.primeFactors.sup id ≤ y ∧ ¬ Occurs n)
  let d := Nat.log 10 N + 1
  have hlen : ∀ n ∈ A, (Nat.digits 10 n).length ≤ d := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    rw [Nat.digits_length_le_iff (by decide : 1 < 10) n]
    exact lt_of_le_of_lt hn.1.2 (Nat.lt_pow_succ_log_self (by decide : 1 < 10) N)
  let f : ℕ → (Fin 10 → Fin (d + 1)) × Bool × Fin (y + 1) := fun n =>
    ( (fun i => ⟨min ((Nat.digits 10 n).count i.val) d, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩),
      decide (n.minFac = 2),
      ⟨min (n.primeFactors.sup id) y, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ )
  have hf_inj : Set.InjOn f (A : Set ℕ) := by
    intro n₁ hn₁ n₂ hn₂ hEq
    by_contra hne
    have h₁ := (Finset.mem_filter.mp hn₁).2
    have h₂ := (Finset.mem_filter.mp hn₂).2
    have hlen₁ : (Nat.digits 10 n₁).length ≤ d := hlen n₁ (Finset.mem_coe.mp hn₁)
    have hlen₂ : (Nat.digits 10 n₂).length ≤ d := hlen n₂ (Finset.mem_coe.mp hn₂)
    have hperm : (Nat.digits 10 n₁).Perm (Nat.digits 10 n₂) := by
      rw [List.perm_iff_count]
      intro x
      by_cases hx : x < 10
      · have hfst := congr_fun (congr_arg Prod.fst hEq) ⟨x, hx⟩
        have hval := congr_arg Fin.val hfst
        have hc₁ : (Nat.digits 10 n₁).count x ≤ d := (List.count_le_length).trans hlen₁
        have hc₂ : (Nat.digits 10 n₂).count x ≤ d := (List.count_le_length).trans hlen₂
        dsimp [f] at hval
        rwa [Nat.min_eq_left hc₁, Nat.min_eq_left hc₂] at hval
      · have hx1 : x ∉ Nat.digits 10 n₁ := fun hm =>
          hx (Nat.digits_lt_base (by decide : 1 < 10) hm)
        have hx2 : x ∉ Nat.digits 10 n₂ := fun hm =>
          hx (Nat.digits_lt_base (by decide : 1 < 10) hm)
        rw [List.count_eq_zero.mpr hx1, List.count_eq_zero.mpr hx2]
    have hmin : n₁.minFac = n₂.minFac := by
      have hsnd := congr_arg (fun p => p.2.1) hEq
      dsimp [f] at hsnd
      rcases h₁.2.1 with h1 | h1 <;> rcases h₂.2.1 with h2 | h2 <;>
        simp [h1, h2] at hsnd ⊢
    have hsup : n₁.primeFactors.sup id = n₂.primeFactors.sup id := by
      have hthd := congr_arg (fun p => p.2.2.val) hEq
      dsimp [f] at hthd
      rwa [Nat.min_eq_left h₁.2.2.1, Nat.min_eq_left h₂.2.2.1] at hthd
    have hOcc : Occurs n₁ :=
      ⟨h₁.1, n₂, h₂.1, Ne.symm hne, hmin, hsup, hperm⟩
    exact h₁.2.2.2 hOcc
  have hcard : A.card ≤ Fintype.card ((Fin 10 → Fin (d + 1)) × Bool × Fin (y + 1)) :=
    Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _) hf_inj
  simp only [Fintype.card_prod, Fintype.card_pi, Fintype.card_fin, Fintype.card_bool,
    Finset.prod_const, Finset.card_univ] at hcard
  calc A.card ≤ (d + 1) ^ 10 * (2 * (y + 1)) := hcard
    _ = 2 * (Nat.log 10 N + 2) ^ 10 * (y + 1) := by dsimp [d]; ring

lemma nat_log_ten_le_two (N : ℕ) : Nat.log 10 N ≤ Nat.log 2 N := by
  by_cases hN : N = 0
  · subst hN; simp
  exact Nat.le_log_of_pow_le (by decide : 1 < 2)
    ((Nat.pow_le_pow_left (by decide : 2 ≤ 10) _).trans
      (Nat.pow_log_le_self 10 hN))

lemma sum_primeCounting_div_le (N L : ℕ) (hN64 : 64 ≤ N) (hL_pos : 1 ≤ L)
    (h_log4_lt : Real.log 4 < 2) (hlog3 : (3 : ℝ) ≤ Real.log (N : ℝ))
    (hL_le_sqrt : (L : ℝ) ≤ Real.sqrt (N : ℝ) / 30)
    (hlogL_le : 1 + Real.log (L : ℝ) ≤ (1 / 1000 : ℝ) * Real.log (N : ℝ)) :
    ∑ k ∈ Finset.Ico 1 L, Nat.primeCounting (N / k) ≤ N / 12 := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have h_sum_real :
      (∑ k ∈ Finset.Ico 1 L, (Nat.primeCounting (N / k) : ℝ)) ≤ (N : ℝ) / 12 := by
    have hterm : ∀ k ∈ Finset.Ico 1 L,
        (Nat.primeCounting (N / k) : ℝ) ≤
          (12 * (N : ℝ) / Real.log (N : ℝ)) * (k : ℝ)⁻¹ + Real.sqrt (N : ℝ) := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      have hk1 : 1 ≤ k := hk.1
      have hkL : k < L := hk.2
      have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
      have hNk_ge_real : Real.sqrt (N : ℝ) ≤ ((N / k : ℕ) : ℝ) + 1 := by
        have hdiv : (N : ℝ) / (k : ℝ) ≤ ((N / k : ℕ) : ℝ) + 1 := by
          have := Nat.lt_div_mul_add (by omega : 0 < k) (a := N)
          have h1 : (N : ℝ) < ((N / k : ℕ) : ℝ) * (k : ℝ) + (k : ℝ) := by exact_mod_cast this
          rw [div_le_iff₀ hk_pos]
          linarith
        have hN_ge_kL : (L : ℝ) * Real.sqrt (N : ℝ) ≤ (N : ℝ) / 30 := by
          have hsq : (L : ℝ) * Real.sqrt (N : ℝ) ≤ (Real.sqrt (N : ℝ) / 30) * Real.sqrt (N : ℝ) :=
            mul_le_mul_of_nonneg_right hL_le_sqrt (Real.sqrt_nonneg _)
          rwa [div_mul_eq_mul_div, ← sq, Real.sq_sqrt hN_pos.le] at hsq
        have hk_lt_L_real : (k : ℝ) < (L : ℝ) := by exact_mod_cast hkL
        have hsqrt_le : Real.sqrt (N : ℝ) ≤ (N : ℝ) / (k : ℝ) := by
          rw [le_div_iff₀ hk_pos]
          calc Real.sqrt (N : ℝ) * (k : ℝ) ≤ Real.sqrt (N : ℝ) * (L : ℝ) :=
                mul_le_mul_of_nonneg_left hk_lt_L_real.le (Real.sqrt_nonneg _)
            _ = (L : ℝ) * Real.sqrt (N : ℝ) := mul_comm _ _
            _ ≤ (N : ℝ) / 30 := hN_ge_kL
            _ ≤ (N : ℝ) := by linarith
        linarith
      have hsqrt_ge8 : (8 : ℝ) ≤ Real.sqrt (N : ℝ) := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 8)]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hN64)
      have hNk_gt1 : (1 : ℝ) < ((N / k : ℕ) : ℝ) := by linarith
      have hpi_le := Chebyshev.pi_le_log4_mul_div hNk_gt1
      rw [Nat.floor_natCast] at hpi_le
      have hsqrt_Nk_le : Real.sqrt ((N / k : ℕ) : ℝ) ≤ Real.sqrt (N : ℝ) := by
        apply Real.sqrt_le_sqrt
        exact_mod_cast Nat.div_le_self N k
      have hlog_Nk_ge : Real.log (N : ℝ) / 3 ≤ Real.log ((N / k : ℕ) : ℝ) := by
        have hNk_ge_half_sqrt : Real.sqrt (N : ℝ) / 2 ≤ ((N / k : ℕ) : ℝ) := by linarith
        have hN_pow_third : (N : ℝ) ^ (1 / 3 : ℝ) ≤ Real.sqrt (N : ℝ) / 2 := by
          have hcub : ((N : ℝ) ^ (1 / 3 : ℝ)) ^ 6 ≤ (Real.sqrt (N : ℝ) / 2) ^ 6 := by
            have h6a : ((N : ℝ) ^ (1 / 3 : ℝ)) ^ 6 = (N : ℝ) ^ 2 := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hN_pos.le]
              norm_num
            have h6b : (Real.sqrt (N : ℝ) / 2) ^ 6 = (N : ℝ) ^ 3 / 64 := by
              rw [div_pow, show (Real.sqrt (N : ℝ)) ^ 6 = ((Real.sqrt (N : ℝ)) ^ 2) ^ 3 by ring,
                Real.sq_sqrt hN_pos.le]
              norm_num
            rw [h6a, h6b]
            have h64r : (64 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN64
            have hN2_le : (N : ℝ) ^ 2 * 64 ≤ (N : ℝ) ^ 3 := by
              calc (N : ℝ) ^ 2 * 64 ≤ (N : ℝ) ^ 2 * (N : ℝ) :=
                    mul_le_mul_of_nonneg_left h64r (sq_nonneg _)
                _ = (N : ℝ) ^ 3 := by ring
            linarith
          exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hcub
        have h1 : Real.log ((N : ℝ) ^ (1 / 3 : ℝ)) ≤ Real.log ((N / k : ℕ) : ℝ) :=
          Real.log_le_log (Real.rpow_pos_of_pos hN_pos _) (hN_pow_third.trans hNk_ge_half_sqrt)
        rw [Real.log_rpow hN_pos] at h1
        linarith
      have hlog_sqrt_ge : Real.log (N : ℝ) / 6 ≤ Real.log (Real.sqrt ((N / k : ℕ) : ℝ)) := by
        rw [Real.log_sqrt (by linarith)]
        linarith
      have hdiv_le : Real.log 4 * ((N / k : ℕ) : ℝ) / Real.log (Real.sqrt ((N / k : ℕ) : ℝ)) ≤
          (12 * (N : ℝ) / Real.log (N : ℝ)) * (k : ℝ)⁻¹ := by
        have hNk_le_div : ((N / k : ℕ) : ℝ) ≤ (N : ℝ) / (k : ℝ) := by
          rw [le_div_iff₀ hk_pos]
          exact_mod_cast Nat.div_mul_le_self N k
        have hnum : Real.log 4 * ((N / k : ℕ) : ℝ) ≤ 2 * ((N : ℝ) / (k : ℝ)) := by
          calc Real.log 4 * ((N / k : ℕ) : ℝ)
              ≤ 2 * ((N / k : ℕ) : ℝ) := mul_le_mul_of_nonneg_right h_log4_lt.le (by positivity)
            _ ≤ 2 * ((N : ℝ) / (k : ℝ)) := mul_le_mul_of_nonneg_left hNk_le_div (by norm_num)
        have hlogN_pos : 0 < Real.log (N : ℝ) := by linarith
        calc Real.log 4 * ((N / k : ℕ) : ℝ) / Real.log (Real.sqrt ((N / k : ℕ) : ℝ))
            ≤ (2 * ((N : ℝ) / (k : ℝ))) / (Real.log (N : ℝ) / 6) := by
              exact div_le_div₀ (by positivity) hnum (by positivity) hlog_sqrt_ge
          _ = (12 * (N : ℝ) / Real.log (N : ℝ)) * (k : ℝ)⁻¹ := by ring
      linarith
    have hsum1 : ∑ k ∈ Finset.Ico 1 L, (Nat.primeCounting (N / k) : ℝ) ≤
        ∑ k ∈ Finset.Ico 1 L, ((12 * (N : ℝ) / Real.log (N : ℝ)) * (k : ℝ)⁻¹ + Real.sqrt (N : ℝ)) :=
      Finset.sum_le_sum hterm
    have hharm : ∑ k ∈ Finset.Ico 1 L, (k : ℝ)⁻¹ ≤ 1 + Real.log (L : ℝ) := by
      have hsub : Finset.Ico 1 L ⊆ Finset.Icc 1 L := Finset.Ico_subset_Icc_self
      have h1 : ∑ k ∈ Finset.Ico 1 L, (k : ℝ)⁻¹ ≤ ∑ k ∈ Finset.Icc 1 L, (k : ℝ)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      have h2 : ∑ k ∈ Finset.Icc 1 L, (k : ℝ)⁻¹ = (harmonic L : ℝ) := by
        simp [harmonic_eq_sum_Icc]
      rw [h2] at h1
      exact h1.trans (harmonic_le_one_add_log L)
    have hterm1 : (12 * (N : ℝ) / Real.log (N : ℝ)) * (∑ k ∈ Finset.Ico 1 L, (k : ℝ)⁻¹) ≤
        (12 / 1000 : ℝ) * (N : ℝ) := by
      have hlogN_pos : 0 < Real.log (N : ℝ) := by linarith
      calc (12 * (N : ℝ) / Real.log (N : ℝ)) * (∑ k ∈ Finset.Ico 1 L, (k : ℝ)⁻¹)
          ≤ (12 * (N : ℝ) / Real.log (N : ℝ)) * ((1 / 1000 : ℝ) * Real.log (N : ℝ)) := by
            exact mul_le_mul_of_nonneg_left (hharm.trans hlogL_le) (by positivity)
        _ = (12 / 1000 : ℝ) * (N : ℝ) := by field_simp
    have hterm2 : ∑ _k ∈ Finset.Ico 1 L, Real.sqrt (N : ℝ) ≤ (N : ℝ) / 30 := by
      rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      have h1 : ((L - 1 : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast Nat.sub_le L 1
      calc ((L - 1 : ℕ) : ℝ) * Real.sqrt (N : ℝ)
          ≤ (L : ℝ) * Real.sqrt (N : ℝ) := mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
        _ ≤ (Real.sqrt (N : ℝ) / 30) * Real.sqrt (N : ℝ) :=
            mul_le_mul_of_nonneg_right hL_le_sqrt (Real.sqrt_nonneg _)
        _ = (N : ℝ) / 30 := by rw [div_mul_eq_mul_div, ← sq, Real.sq_sqrt hN_pos.le]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum1
    linarith
  have h_mul12 : (∑ k ∈ Finset.Ico 1 L, Nat.primeCounting (N / k)) * 12 ≤ N := by
    have hreal : ((∑ k ∈ Finset.Ico 1 L, Nat.primeCounting (N / k)) * 12 : ℝ) ≤ (N : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hreal
  exact (Nat.le_div_iff_mul_le (by decide : 0 < 12)).mpr h_mul12

lemma eventually_sum_primeCounting_le :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∑ k ∈ Finset.Ico 1 ((Nat.log 2 N + 1) ^ 12), Nat.primeCounting (N / k) ≤ N / 12 := by
  have h_log2_gt : (1 / 2 : ℝ) < Real.log 2 := by
    have hexp : Real.exp 1 < 4 := by linarith [Real.exp_one_lt_d9]
    have hlog4 : 1 < Real.log 4 := by
      rw [← Real.log_exp 1]
      exact Real.log_lt_log (Real.exp_pos 1) hexp
    have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith
  have h_log4_lt : Real.log 4 < 2 := by
    have hexp : (2 : ℝ) < Real.exp 1 := by linarith [Real.add_one_lt_exp (one_ne_zero)]
    have hlog2 : Real.log 2 < 1 := by
      rw [← Real.log_exp 1]
      exact Real.log_lt_log (by norm_num) hexp
    have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith
  have h_pow_log : ∀ᶠ x : ℝ in Filter.atTop,
      (Real.log x) ^ 24 ≤ (1 / (1000 * 3 ^ 24 : ℝ)) * x := by
    have h := (Real.isLittleO_pow_log_id_atTop (n := 24)).bound
      (show (0 : ℝ) < 1 / (1000 * 3 ^ 24 : ℝ) by positivity)
    filter_upwards [h, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hnonneg : 0 ≤ (Real.log x) ^ 24 := pow_nonneg (Real.log_nonneg hx1) _
    simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg hnonneg,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ x)] at hx
    exact hx
  have h_log_log : ∀ᶠ x : ℝ in Filter.atTop,
      1 + 12 * Real.log (3 * Real.log x) ≤ (1 / 1000 : ℝ) * Real.log x := by
    have h1 := (Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop).bound
      (show (0 : ℝ) < 1 / 24000 by positivity)
    have h2 : ∀ᶠ x : ℝ in Filter.atTop, 1 + 12 * Real.log 3 ≤ (1 / 2000 : ℝ) * Real.log x := by
      exact (Real.tendsto_log_atTop.eventually_ge_atTop ((1 + 12 * Real.log 3) * 2000)).mono
        fun x hx => by linarith
    have h3 : ∀ᶠ x : ℝ in Filter.atTop, (3 : ℝ) ≤ Real.log x :=
      Real.tendsto_log_atTop.eventually_ge_atTop 3
    filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
    have hll_pos : 0 < Real.log (Real.log x) := Real.log_pos (by linarith)
    have hl_pos : 0 < Real.log x := by linarith
    simp only [Function.comp_apply, id_eq, Real.norm_eq_abs, abs_of_nonneg hll_pos.le,
      abs_of_nonneg hl_pos.le] at hx1
    rw [Real.log_mul (by norm_num) hl_pos.ne']
    linarith
  have h_all : ∀ᶠ N : ℕ in Filter.atTop,
      64 ≤ N ∧
      (Real.log (N : ℝ)) ^ 24 ≤ (1 / (1000 * 3 ^ 24 : ℝ)) * (N : ℝ) ∧
      1 + 12 * Real.log (3 * Real.log (N : ℝ)) ≤ (1 / 1000 : ℝ) * Real.log (N : ℝ) ∧
      (3 : ℝ) ≤ Real.log (N : ℝ) := by
    have hNat := tendsto_natCast_atTop_atTop (R := ℝ)
    exact (Filter.eventually_ge_atTop 64).and
      ((hNat.eventually h_pow_log).and
        ((hNat.eventually h_log_log).and
          (hNat.eventually (Real.tendsto_log_atTop.eventually_ge_atTop 3))))
  rw [Filter.eventually_atTop] at h_all
  rcases h_all with ⟨N₀, hN₀⟩
  refine ⟨N₀, fun N hN => ?_⟩
  rcases hN₀ N hN with ⟨hN64, hpow24, hllog, hlog3⟩
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hnatlog_le : (Nat.log 2 N : ℝ) ≤ 2 * Real.log (N : ℝ) := by
    have hp : (2 : ℝ) ^ (Nat.log 2 N) ≤ (N : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have h1 : (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log (N : ℝ) := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) hp
    nlinarith
  have hL_real_le : (((Nat.log 2 N + 1) ^ 12 : ℕ) : ℝ) ≤ (3 * Real.log (N : ℝ)) ^ 12 := by
    have hbase : (Nat.log 2 N + 1 : ℝ) ≤ 3 * Real.log (N : ℝ) := by linarith
    push_cast
    exact pow_le_pow_left₀ (by positivity) hbase 12
  have hL_sq_le : (((Nat.log 2 N + 1) ^ 12 : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) / 1000 := by
    calc (((Nat.log 2 N + 1) ^ 12 : ℕ) : ℝ) ^ 2 ≤ ((3 * Real.log (N : ℝ)) ^ 12) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hL_real_le 2
      _ = (3 : ℝ) ^ 24 * (Real.log (N : ℝ)) ^ 24 := by ring
      _ ≤ (3 : ℝ) ^ 24 * ((1 / (1000 * 3 ^ 24 : ℝ)) * (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hpow24 (by positivity)
      _ = (N : ℝ) / 1000 := by ring
  have hL_le_sqrt : (((Nat.log 2 N + 1) ^ 12 : ℕ) : ℝ) ≤ Real.sqrt (N : ℝ) / 30 := by
    have hsq : (30 * (((Nat.log 2 N + 1) ^ 12 : ℕ) : ℝ)) ^ 2 ≤ (Real.sqrt (N : ℝ)) ^ 2 := by
      rw [Real.sq_sqrt hN_pos.le, mul_pow]
      calc (30 : ℝ) ^ 2 * (((Nat.log 2 N + 1) ^ 12 : ℕ) : ℝ) ^ 2
          = 900 * (((Nat.log 2 N + 1) ^ 12 : ℕ) : ℝ) ^ 2 := by norm_num
        _ ≤ 900 * ((N : ℝ) / 1000) := mul_le_mul_of_nonneg_left hL_sq_le (by norm_num)
        _ ≤ (N : ℝ) := by linarith
    have h30 : 30 * (((Nat.log 2 N + 1) ^ 12 : ℕ) : ℝ) ≤ Real.sqrt (N : ℝ) :=
      le_of_pow_le_pow_left₀ (by norm_num) (Real.sqrt_nonneg _) hsq
    linarith
  have hL_pos : 1 ≤ (Nat.log 2 N + 1) ^ 12 := Nat.one_le_pow _ _ (by omega)
  have hlogL_le : 1 + Real.log (((Nat.log 2 N + 1) ^ 12 : ℕ) : ℝ) ≤
      (1 / 1000 : ℝ) * Real.log (N : ℝ) := by
    have h1 : Real.log (((Nat.log 2 N + 1) ^ 12 : ℕ) : ℝ) ≤ 12 * Real.log (3 * Real.log (N : ℝ)) := by
      calc Real.log (((Nat.log 2 N + 1) ^ 12 : ℕ) : ℝ) ≤ Real.log ((3 * Real.log (N : ℝ)) ^ 12) :=
            Real.log_le_log (by exact_mod_cast hL_pos) hL_real_le
        _ = 12 * Real.log (3 * Real.log (N : ℝ)) := by rw [Real.log_pow]; norm_num
    linarith
  exact sum_primeCounting_div_le N ((Nat.log 2 N + 1) ^ 12) hN64 hL_pos h_log4_lt hlog3 hL_le_sqrt hlogL_le

lemma eventually_unmatched_bound_le :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      2 * (Nat.log 10 N + 2) ^ 10 * (N / ((Nat.log 2 N + 1) ^ 12) + 1) ≤ N / 24 := by
  have h_log2_gt : (1 / 2 : ℝ) < Real.log 2 := by
    have hexp : Real.exp 1 < 4 := by linarith [Real.exp_one_lt_d9]
    have hlog4 : 1 < Real.log 4 := by
      rw [← Real.log_exp 1]
      exact Real.log_lt_log (Real.exp_pos 1) hexp
    have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith
  have h_pow_log10 : ∀ᶠ x : ℝ in Filter.atTop,
      (Real.log x) ^ 10 ≤ (1 / (200 * 2048 * 3 ^ 10 : ℝ)) * x := by
    have h := (Real.isLittleO_pow_log_id_atTop (n := 10)).bound
      (show (0 : ℝ) < 1 / (200 * 2048 * 3 ^ 10 : ℝ) by positivity)
    filter_upwards [h, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hnonneg : 0 ≤ (Real.log x) ^ 10 := pow_nonneg (Real.log_nonneg hx1) _
    simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg hnonneg,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ x)] at hx
    exact hx
  have h_all : ∀ᶠ N : ℕ in Filter.atTop,
      2 ^ 255 ≤ N ∧
      (Real.log (N : ℝ)) ^ 10 ≤ (1 / (200 * 2048 * 3 ^ 10 : ℝ)) * (N : ℝ) ∧
      (3 : ℝ) ≤ Real.log (N : ℝ) := by
    have hNat := tendsto_natCast_atTop_atTop (R := ℝ)
    exact (Filter.eventually_ge_atTop (2 ^ 255)).and
      ((hNat.eventually h_pow_log10).and
        (hNat.eventually (Real.tendsto_log_atTop.eventually_ge_atTop 3)))
  rw [Filter.eventually_atTop] at h_all
  rcases h_all with ⟨N₀, hN₀⟩
  refine ⟨N₀, fun N hN => ?_⟩
  rcases hN₀ N hN with ⟨hN255, hpow10, hlog3⟩
  let m := Nat.log 2 N + 1
  have hm256 : 256 ≤ m := by
    have : 255 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by decide : 1 < 2) hN255
    omega
  have hlog_le : Nat.log 10 N + 2 ≤ 2 * m := by
    have := nat_log_ten_le_two N
    omega
  have hpow_le : 2 * (Nat.log 10 N + 2) ^ 10 ≤ 2048 * m ^ 10 := by
    calc 2 * (Nat.log 10 N + 2) ^ 10 ≤ 2 * (2 * m) ^ 10 :=
          Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hlog_le 10)
      _ = 2048 * m ^ 10 := by ring
  have hterm1 : 2048 * m ^ 10 * (N / m ^ 12) ≤ N / 32 := by
    have hm_pos : 0 < m := by omega
    have h1 : (N / m ^ 12) * m ^ 10 ≤ N / m ^ 2 := by
      rw [Nat.le_div_iff_mul_le (by positivity)]
      calc (N / m ^ 12) * m ^ 10 * m ^ 2 = (N / m ^ 12) * m ^ 12 := by ring
        _ ≤ N := Nat.div_mul_le_self N (m ^ 12)
    have h2 : 65536 ≤ m ^ 2 := by
      have : 256 ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hm256 2
      omega
    have h4 : 2048 * (N / m ^ 2) ≤ N / 32 := by
      rw [Nat.le_div_iff_mul_le (by decide : 0 < 32)]
      calc 2048 * (N / m ^ 2) * 32 = (N / m ^ 2) * 65536 := by ring
        _ ≤ (N / m ^ 2) * m ^ 2 := Nat.mul_le_mul_left _ h2
        _ ≤ N := Nat.div_mul_le_self N (m ^ 2)
    calc 2048 * m ^ 10 * (N / m ^ 12) = 2048 * ((N / m ^ 12) * m ^ 10) := by ring
      _ ≤ 2048 * (N / m ^ 2) := Nat.mul_le_mul_left 2048 h1
      _ ≤ N / 32 := h4
  have hterm2 : 2048 * m ^ 10 ≤ N / 200 := by
    have hnatlog_le : (Nat.log 2 N : ℝ) ≤ 2 * Real.log (N : ℝ) := by
      have hp : (2 : ℝ) ^ (Nat.log 2 N) ≤ (N : ℝ) := by
        exact_mod_cast Nat.pow_log_le_self 2 (by omega)
      have h1 : (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log (N : ℝ) := by
        rw [← Real.log_pow]
        exact Real.log_le_log (by positivity) hp
      have h2 : (Nat.log 2 N : ℝ) * (1 / 2) ≤ (Nat.log 2 N : ℝ) * Real.log 2 :=
        mul_le_mul_of_nonneg_left h_log2_gt.le (Nat.cast_nonneg _)
      linarith
    have hm_real : (m : ℝ) ≤ 3 * Real.log (N : ℝ) := by
      have : (m : ℝ) = (Nat.log 2 N : ℝ) + 1 := by push_cast [m]; rfl
      linarith
    have hm10 : (2048 * (m : ℝ) ^ 10 * 200 : ℝ) ≤ (N : ℝ) := by
      calc (2048 * (m : ℝ) ^ 10 * 200 : ℝ)
          ≤ 2048 * (3 * Real.log (N : ℝ)) ^ 10 * 200 := by
            have h1 : (m : ℝ) ^ 10 ≤ (3 * Real.log (N : ℝ)) ^ 10 :=
              pow_le_pow_left₀ (by positivity) hm_real 10
            gcongr
        _ = 2048 * ((3 : ℝ) ^ 10 * (Real.log (N : ℝ)) ^ 10) * 200 := by ring
        _ ≤ 2048 * ((3 : ℝ) ^ 10 * ((1 / (200 * 2048 * 3 ^ 10 : ℝ)) * (N : ℝ))) * 200 := by
            gcongr
        _ = (N : ℝ) := by ring
    have hnat : 2048 * m ^ 10 * 200 ≤ N := by exact_mod_cast hm10
    exact (Nat.le_div_iff_mul_le (by decide : 0 < 200)).mpr hnat
  calc 2 * (Nat.log 10 N + 2) ^ 10 * (N / ((Nat.log 2 N + 1) ^ 12) + 1)
      ≤ (2048 * m ^ 10) * (N / m ^ 12 + 1) := Nat.mul_le_mul_right _ hpow_le
    _ = 2048 * m ^ 10 * (N / m ^ 12) + 2048 * m ^ 10 := by ring
    _ ≤ N / 32 + N / 200 := Nat.add_le_add hterm1 hterm2
    _ ≤ N / 24 := by omega

end OMA.S_oeis_a214619_Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a214619.main := by
  classical
  rcases OMA.S_oeis_a214619_Proof.eventually_sum_primeCounting_le with ⟨N₁, hN₁⟩
  rcases OMA.S_oeis_a214619_Proof.eventually_unmatched_bound_le with ⟨N₂, hN₂⟩
  refine ⟨max (max N₁ N₂) 100, fun N hN => ?_⟩
  have h1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have h2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have h100 : 100 ≤ N := le_trans (le_max_right _ _) hN
  let L := (Nat.log 2 N + 1) ^ 12
  let y := N / L
  have hL_pos : 1 ≤ L := Nat.one_le_pow _ _ (by omega)
  let U := (Finset.Icc 1 N).filter (fun n => 2 ≤ n ∧ (n.minFac = 2 ∨ n.minFac = 3))
  let B := (Finset.Icc 1 N).filter (fun n => ∃ p ∈ n.primeFactors, y < p)
  let A_bad := (Finset.Icc 1 N).filter
    (fun n => 2 ≤ n ∧ (n.minFac = 2 ∨ n.minFac = 3) ∧
      n.primeFactors.sup id ≤ y ∧ ¬ OMA.S_oeis_a214619.Occurs n)
  let C_good := (Finset.Icc 1 N).filter OMA.S_oeis_a214619.Occurs
  have hU_sub : U ⊆ B ∪ A_bad ∪ C_good := by
    intro n hn
    rw [Finset.mem_union, Finset.mem_union]
    rcases Finset.mem_filter.mp hn with ⟨hnIcc, hn2, hmin⟩
    by_cases hy : y < n.primeFactors.sup id
    · left; left
      rw [Finset.mem_filter]
      refine ⟨hnIcc, ?_⟩
      have hmem := OMA.S_oeis_a214619_Proof.sup_primeFactors_mem hn2
      exact ⟨n.primeFactors.sup id, hmem, hy⟩
    · have hle : n.primeFactors.sup id ≤ y := not_lt.mp hy
      by_cases hocc : OMA.S_oeis_a214619.Occurs n
      · right
        exact Finset.mem_filter.mpr ⟨hnIcc, hocc⟩
      · left; right
        exact Finset.mem_filter.mpr ⟨hnIcc, hn2, hmin, hle, hocc⟩
  have hcard_U : N / 2 + N / 6 ≤ U.card := OMA.S_oeis_a214619_Proof.card_even_or_mult3 N
  have hcard_B : B.card ≤ N / 12 :=
    (OMA.S_oeis_a214619_Proof.card_large_prime_factor_le N L hL_pos).trans (hN₁ N h1)
  have hcard_Abad : A_bad.card ≤ N / 24 :=
    (OMA.S_oeis_a214619_Proof.card_unmatched_le N y).trans (hN₂ N h2)
  have hcard_split : U.card ≤ B.card + A_bad.card + C_good.card :=
    (Finset.card_le_card hU_sub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hcount : C_good.card = OMA.S_oeis_a214619.count N := by
    unfold OMA.S_oeis_a214619.count
    congr 2
  rw [← hcount]
  generalize U.card = uc at hcard_U hcard_split
  generalize B.card = bc at hcard_B hcard_split
  generalize A_bad.card = ac at hcard_Abad hcard_split
  generalize C_good.card = cc at hcard_split
  omega
