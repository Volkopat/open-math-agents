import OMAReductions.R_Erdos292_erdos_292_variants_martin_R1


namespace E292Part1

open Finset Filter Real
open scoped Classical

/- ## Part 1: Largest prime power divisor `PStar` -/

/-- The largest prime power dividing `n` (with `PStar 0 = 0`, `PStar 1 = 1`). -/
def PStar (n : ℕ) : ℕ :=
  if n ≤ 1 then n else (n.primeFactors.image (fun p => p ^ n.factorization p)).sup id

lemma PStar_zero : PStar 0 = 0 := by simp [PStar]

lemma PStar_one : PStar 1 = 1 := by simp [PStar]

lemma prime_pow_dvd_le_PStar {n p k : ℕ} (hn : 0 < n) (hp : p.Prime) (hd : p ^ k ∣ n) :
    p ^ k ≤ PStar n := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [pow_zero]
    rcases (show n = 1 ∨ 1 < n by omega) with rfl | h1
    · simp [PStar]
    · unfold PStar
      rw [if_neg (by omega)]
      obtain ⟨q, hq, hqn⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
      have hqm : q ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqn, hn.ne'⟩
      have hpos : 1 ≤ q ^ n.factorization q := Nat.one_le_pow _ _ hq.pos
      exact hpos.trans (Finset.le_sup (f := id) (Finset.mem_image.mpr ⟨q, hqm, rfl⟩))
  · have hpn : p ∣ n := dvd_trans (dvd_pow_self p hk.ne') hd
    have hn1 : ¬ n ≤ 1 := by
      have := Nat.le_of_dvd hn hpn
      have := hp.two_le
      omega
    unfold PStar
    rw [if_neg hn1]
    have hpm : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, hn.ne'⟩
    have hkle : k ≤ n.factorization p := (hp.pow_dvd_iff_le_factorization hn.ne').mp hd
    have hpow : p ^ k ≤ p ^ n.factorization p := Nat.pow_le_pow_right hp.pos hkle
    exact hpow.trans (Finset.le_sup (f := id) (Finset.mem_image.mpr ⟨p, hpm, rfl⟩))

lemma PStar_le_iff {n B : ℕ} (hn : 0 < n) (hB : 1 ≤ B) :
    PStar n ≤ B ↔ ∀ p k : ℕ, p.Prime → p ^ k ∣ n → p ^ k ≤ B := by
  constructor
  · intro h p k hp hd
    exact (prime_pow_dvd_le_PStar hn hp hd).trans h
  · intro h
    unfold PStar
    split_ifs with hn1
    · omega
    · apply Finset.sup_le
      intro b hb
      rcases Finset.mem_image.mp hb with ⟨p, hp, rfl⟩
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      exact h p (n.factorization p) hpp (Nat.ordProj_dvd n p)

lemma PStar_dvd_le {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hd : a ∣ b) : PStar a ≤ PStar b := by
  have hb1 : 1 ≤ PStar b := by
    have := prime_pow_dvd_le_PStar hb Nat.prime_two (show 2 ^ 0 ∣ b by simp)
    simpa using this
  rw [PStar_le_iff ha hb1]
  intro p k hp hpk
  exact prime_pow_dvd_le_PStar hb hp (dvd_trans hpk hd)

lemma PStar_pos {n : ℕ} (hn : 0 < n) : 0 < PStar n := by
  have h1 : 1 ≤ PStar n := by
    have := prime_pow_dvd_le_PStar hn Nat.prime_two (show 2 ^ 0 ∣ n by simp)
    simpa using this
  omega

lemma PStar_le_self (n : ℕ) : PStar n ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [PStar]
  · rw [PStar_le_iff hn hn]
    intro p k _ hd
    exact Nat.le_of_dvd hn hd

lemma PStar_eq_one_iff {n : ℕ} (hn : 0 < n) : PStar n = 1 ↔ n = 1 := by
  constructor
  · intro h
    by_contra hn1
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn1
    have h1 : p ^ 1 ≤ PStar n := prime_pow_dvd_le_PStar hn hp (by simpa using hpn)
    rw [pow_one] at h1
    have := hp.two_le
    omega
  · rintro rfl
    exact PStar_one

lemma PStar_prime_pow {p k : ℕ} (hp : p.Prime) (_hk : 1 ≤ k) : PStar (p ^ k) = p ^ k := by
  apply le_antisymm (PStar_le_self _)
  exact prime_pow_dvd_le_PStar (pow_pos hp.pos k) hp dvd_rfl

lemma PStar_lcm_le {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    PStar (Nat.lcm a b) ≤ max (PStar a) (PStar b) := by
  have hlpos : 0 < Nat.lcm a b := Nat.lcm_pos ha hb
  have h1 : 1 ≤ max (PStar a) (PStar b) := le_trans (PStar_pos ha) (le_max_left _ _)
  rw [PStar_le_iff hlpos h1]
  intro p k hp hpk
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using h1
  · have hle : k ≤ (Nat.lcm a b).factorization p :=
      (hp.pow_dvd_iff_le_factorization hlpos.ne').mp hpk
    rw [Nat.factorization_lcm ha.ne' hb.ne', Finsupp.sup_apply] at hle
    rcases le_max_iff.mp hle with hka | hkb
    · exact le_trans (prime_pow_dvd_le_PStar ha hp
        ((hp.pow_dvd_iff_le_factorization ha.ne').mpr hka)) (le_max_left _ _)
    · exact le_trans (prime_pow_dvd_le_PStar hb hp
        ((hp.pow_dvd_iff_le_factorization hb.ne').mpr hkb)) (le_max_right _ _)

lemma PStar_mul_coprime {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b) :
    PStar (a * b) = max (PStar a) (PStar b) := by
  apply le_antisymm
  · rw [← hcop.lcm_eq_mul]
    exact PStar_lcm_le ha hb
  · exact max_le (PStar_dvd_le ha (Nat.mul_pos ha hb) (dvd_mul_right a b))
      (PStar_dvd_le hb (Nat.mul_pos ha hb) (dvd_mul_left b a))

lemma PStar_mul_prime_pow_eq {p ν m : ℕ} (hp : p.Prime) (hν : 1 ≤ ν) (hm : 0 < m)
    (hndvd : ¬ p ∣ m) (hPm : PStar m < p ^ ν) :
    PStar (p ^ ν * m) = p ^ ν := by
  have hcop : Nat.Coprime (p ^ ν) m :=
    (hp.coprime_iff_not_dvd.mpr hndvd).pow_left ν
  rw [PStar_mul_coprime (pow_pos hp.pos ν) hm hcop, PStar_prime_pow hp hν]
  exact max_eq_left hPm.le

lemma PStar_rat_add_den_le (r₁ r₂ : ℚ) :
    PStar (r₁ + r₂).den ≤ max (PStar r₁.den) (PStar r₂.den) := by
  have hdvd : (r₁ + r₂).den ∣ Nat.lcm r₁.den r₂.den := by
    have h1 : r₁.den ∣ Nat.lcm r₁.den r₂.den := Nat.dvd_lcm_left _ _
    have h2 : r₂.den ∣ Nat.lcm r₁.den r₂.den := Nat.dvd_lcm_right _ _
    obtain ⟨c₁, hc₁⟩ := h1
    obtain ⟨c₂, hc₂⟩ := h2
    have hmul : ((Nat.lcm r₁.den r₂.den : ℕ) : ℚ) * (r₁ + r₂) =
        ((r₁.num * (c₁ : ℤ) + r₂.num * (c₂ : ℤ) : ℤ) : ℚ) := by
      have h1' : (r₁.den : ℚ) * r₁ = (r₁.num : ℚ) := by
        rw [mul_comm]; exact Rat.mul_den_eq_num r₁
      have h2' : (r₂.den : ℚ) * r₂ = (r₂.num : ℚ) := by
        rw [mul_comm]; exact Rat.mul_den_eq_num r₂
      push_cast
      rw [mul_add]
      have eq1 : ((Nat.lcm r₁.den r₂.den : ℕ) : ℚ) * r₁ = (r₁.num : ℚ) * (c₁ : ℚ) := by
        rw [hc₁]; push_cast; linear_combination (c₁ : ℚ) * h1'
      have eq2 : ((Nat.lcm r₁.den r₂.den : ℕ) : ℚ) * r₂ = (r₂.num : ℚ) * (c₂ : ℚ) := by
        rw [hc₂]; push_cast; linear_combination (c₂ : ℚ) * h2'
      rw [eq1, eq2]
    have hden_dvd : ((r₁ + r₂).den : ℤ) ∣ (Nat.lcm r₁.den r₂.den : ℤ) := by
      have hne : ((r₁ + r₂).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (r₁ + r₂).den_nz
      have hmul2 : ((r₁ + r₂).num : ℚ) * (Nat.lcm r₁.den r₂.den : ℚ) =
          ((r₁.num * (c₁ : ℤ) + r₂.num * (c₂ : ℤ) : ℤ) : ℚ) * ((r₁ + r₂).den : ℚ) := by
        calc ((r₁ + r₂).num : ℚ) * (Nat.lcm r₁.den r₂.den : ℚ)
            = ((r₁ + r₂) * ((r₁ + r₂).den : ℚ)) * (Nat.lcm r₁.den r₂.den : ℚ) := by
                rw [Rat.mul_den_eq_num]
          _ = (((Nat.lcm r₁.den r₂.den : ℕ) : ℚ) * (r₁ + r₂)) * ((r₁ + r₂).den : ℚ) := by ring
          _ = _ := by rw [hmul]
      have hmulZ : (r₁ + r₂).num * (Nat.lcm r₁.den r₂.den : ℤ) =
          (r₁.num * (c₁ : ℤ) + r₂.num * (c₂ : ℤ)) * ((r₁ + r₂).den : ℤ) := by
        exact_mod_cast hmul2
      have hd1 : ((r₁ + r₂).den : ℤ) ∣ (r₁ + r₂).num * (Nat.lcm r₁.den r₂.den : ℤ) :=
        ⟨r₁.num * (c₁ : ℤ) + r₂.num * (c₂ : ℤ), by linarith⟩
      have hcop : IsCoprime ((r₁ + r₂).den : ℤ) (r₁ + r₂).num := by
        have hc := (r₁ + r₂).reduced
        exact (Int.isCoprime_iff_nat_coprime.mpr (by simpa [Int.natAbs_natCast] using hc.symm))
      exact hcop.dvd_of_dvd_mul_left hd1
    exact Int.ofNat_dvd.mp hden_dvd
  exact (PStar_dvd_le (r₁ + r₂).den_pos (Nat.lcm_pos r₁.den_pos r₂.den_pos) hdvd).trans
    (PStar_lcm_le r₁.den_pos r₂.den_pos)

lemma PStar_rat_neg_den (r : ℚ) : PStar (-r).den = PStar r.den := by
  simp [Rat.neg_den]

lemma PStar_rat_sub_den_le (r₁ r₂ : ℚ) :
    PStar (r₁ - r₂).den ≤ max (PStar r₁.den) (PStar r₂.den) := by
  rw [sub_eq_add_neg]
  simpa [PStar_rat_neg_den] using PStar_rat_add_den_le r₁ (-r₂)

lemma PStar_rat_inv_nat_den {n : ℕ} (hn : 0 < n) :
    PStar ((1 : ℚ) / n).den = PStar n := by
  have hden : ((1 : ℚ) / n).den = n := by
    have hq : ((1 : ℚ) / n) = { num := 1, den := n, den_nz := hn.ne', reduced := by simp } := by
      have h1 : (({ num := 1, den := n, den_nz := hn.ne', reduced := by simp } : ℚ) : ℚ) =
          (1 : ℚ) / (n : ℚ) := by
        simpa [Rat.num_div_den] using (Rat.num_div_den { num := 1, den := n, den_nz := hn.ne', reduced := by simp }).symm
      exact h1.symm
    rw [hq]
  rw [hden]

lemma PStar_sum_inv_den_le (S : Finset ℕ) (B : ℕ) (hB : 1 ≤ B)
    (hS : ∀ n ∈ S, 0 < n ∧ PStar n ≤ B) :
    PStar (∑ n ∈ S, (1 : ℚ) / n).den ≤ B := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp [PStar_one, hB]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have ha' := hS a (Finset.mem_insert_self a s)
    have hs' : PStar (∑ n ∈ s, (1 : ℚ) / n).den ≤ B :=
      ih (fun n hn => hS n (Finset.mem_insert_of_mem hn))
    have h1 := PStar_rat_add_den_le ((1 : ℚ) / a) (∑ n ∈ s, (1 : ℚ) / n)
    rw [PStar_rat_inv_nat_den ha'.1] at h1
    exact h1.trans (max_le ha'.2 hs')

lemma exists_prime_pow_eq_PStar {n : ℕ} (hn : 1 < n) :
    ∃ p ν : ℕ, p.Prime ∧ 1 ≤ ν ∧ p ^ ν = PStar n ∧ p ^ ν ∣ n ∧ ¬ p ^ (ν + 1) ∣ n := by
  unfold PStar
  rw [if_neg (by omega)]
  have hne : (n.primeFactors.image (fun p => p ^ n.factorization p)).Nonempty := by
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
    exact ⟨_, Finset.mem_image.mpr ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpn, by omega⟩, rfl⟩⟩
  obtain ⟨b, hb, hsup⟩ := Finset.exists_mem_eq_sup _ hne id
  rcases Finset.mem_image.mp hb with ⟨p, hp, rfl⟩
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have hν : 1 ≤ n.factorization p := by
    exact (hpp.pow_dvd_iff_le_factorization (by omega : n ≠ 0)).mp (by rw [pow_one]; exact hpn)
  refine ⟨p, n.factorization p, hpp, hν, hsup.symm, Nat.ordProj_dvd n p, ?_⟩
  intro hd
  have := (hpp.pow_dvd_iff_le_factorization (by omega : n ≠ 0)).mp hd
  omega

/- ## Part 2: Elementary Chebyshev prime-interval lower bound -/

/-- For `0 < α ≤ 21/50` (`= 0.42`) and `B ≥ 10^6`, the number of primes in `(⌊α B⌋, ⌊B⌋]`
is at least `B / (20 * log B)`. Uses only Mathlib's `Chebyshev.theta_ge` and
`Chebyshev.theta_le_log4_mul_x`. -/
lemma prime_count_interval_ge {α B : ℝ} (hα0 : 0 < α) (hα : α ≤ 21 / 50) (hB : 1000000 ≤ B) :
    B / (20 * Real.log B) ≤
      (((Finset.Ioc ⌊α * B⌋₊ ⌊B⌋₊).filter Nat.Prime).card : ℝ) := by
  have hBpos : 0 < B := by linarith
  have hB1 : 1 < B := by linarith
  have hlogB : 0 < Real.log B := Real.log_pos hB1
  set N : ℕ := ⌊B⌋₊ with hNdef
  set M : ℕ := ⌊α * B⌋₊ with hMdef
  have hMN : M ≤ N := Nat.floor_mono (by nlinarith)
  have hNR : B - 1 < (N : ℝ) := Nat.sub_one_lt_floor B
  have hNRle : (N : ℝ) ≤ B := Nat.floor_le hBpos.le
  have hMRle : (M : ℝ) ≤ α * B := Nat.floor_le (by positivity)
  have hNpos : 0 < (N : ℝ) := by linarith
  -- Theta difference equals sum of log p over primes in (M, N]
  have hdiff_eq : Chebyshev.theta (N : ℝ) - Chebyshev.theta (M : ℝ) =
      ∑ p ∈ (Finset.Ioc M N).filter Nat.Prime, Real.log p := by
    rw [Chebyshev.theta_eq_sum_primesLE_log N, Chebyshev.theta_eq_sum_primesLE_log M]
    have hsub : Nat.primesLE M ⊆ Nat.primesLE N := by
      intro p hp
      rw [Nat.mem_primesLE] at hp ⊢
      exact ⟨hp.1.trans hMN, hp.2⟩
    have hsdiff : Nat.primesLE N \ Nat.primesLE M = (Finset.Ioc M N).filter Nat.Prime := by
      ext p
      simp only [Finset.mem_sdiff, Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Ioc]
      constructor
      · rintro ⟨⟨hpN, hp⟩, hnot⟩
        exact ⟨⟨by by_contra hle; exact hnot ⟨by omega, hp⟩, hpN⟩, hp⟩
      · rintro ⟨⟨hpM, hpN⟩, hp⟩
        exact ⟨⟨hpN, hp⟩, fun h => by omega⟩
    rw [← hsdiff, Finset.sum_sdiff_eq_sub hsub]
  -- Upper bound on the sum: each log p ≤ log B
  have hsum_le : ∑ p ∈ (Finset.Ioc M N).filter Nat.Prime, Real.log p ≤
      (((Finset.Ioc M N).filter Nat.Prime).card : ℝ) * Real.log B := by
    calc ∑ p ∈ (Finset.Ioc M N).filter Nat.Prime, Real.log p
        ≤ ∑ _p ∈ (Finset.Ioc M N).filter Nat.Prime, Real.log B := by
          apply Finset.sum_le_sum
          intro p hp
          have hp' := Finset.mem_filter.mp hp
          have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp'.2.pos
          have hp_le : (p : ℝ) ≤ B := by
            have : p ≤ N := (Finset.mem_Ioc.mp hp'.1).2
            exact le_trans (by exact_mod_cast this) hNRle
          exact Real.log_le_log hp_pos hp_le
      _ = (((Finset.Ioc M N).filter Nat.Prime).card : ℝ) * Real.log B := by simp
  -- Lower bound on θ(N) - θ(M)
  have hthN := Chebyshev.theta_ge N
  have hthM : Chebyshev.theta (M : ℝ) ≤ Real.log 4 * (M : ℝ) :=
    Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg M)
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hlog2_gt : (69 / 100 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlog2_lt : Real.log 2 < (70 / 100 : ℝ) := by
    linarith [Real.log_two_lt_d9]
  have hsqrtN : Real.sqrt (N : ℝ) ≤ Real.sqrt B := Real.sqrt_le_sqrt hNRle
  have hlogN : Real.log (N : ℝ) ≤ Real.log B := Real.log_le_log hNpos hNRle
  have hlogN1 : Real.log ((N : ℝ) + 1) ≤ Real.log (2 * B) :=
    Real.log_le_log (by linarith only [hNpos]) (by linarith only [hNRle, hB])
  have hlog_1e6 : Real.log (1000000 : ℝ) ≤ 14 := by
    have h1 : (1000000 : ℝ) ≤ (2 : ℝ) ^ (20 : ℕ) := by norm_num
    have h2 : Real.log (1000000 : ℝ) ≤ Real.log ((2 : ℝ) ^ (20 : ℕ)) :=
      Real.log_le_log (by norm_num) h1
    rw [Real.log_pow] at h2
    norm_num at h2
    linarith only [h2, hlog2_lt]
  have hlogB_tight : Real.log B ≤ 14 + 4 * (B / 1000000) ^ ((1 : ℝ) / 4) := by
    have hq_pos : 0 < (B / 1000000) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos (by positivity) _
    have h1 := Real.log_le_sub_one_of_pos hq_pos
    rw [Real.log_rpow (by positivity), Real.log_div hBpos.ne' (by norm_num)] at h1
    linarith only [h1, hlog_1e6]
  have hsqrtB_ge : (1000 : ℝ) ≤ Real.sqrt B := by
    rw [show (1000 : ℝ) = Real.sqrt 1000000 by norm_num]
    exact Real.sqrt_le_sqrt hB
  have hsqrt_term1 : Real.sqrt B * 14 ≤ (14 / 1000 : ℝ) * B := by
    have h1 : Real.sqrt B * 1000 ≤ Real.sqrt B * Real.sqrt B :=
      mul_le_mul_of_nonneg_left hsqrtB_ge (Real.sqrt_nonneg B)
    rw [Real.mul_self_sqrt hBpos.le] at h1
    linarith only [h1]
  have hsqrt_term2 : Real.sqrt B * (4 * (B / 1000000) ^ ((1 : ℝ) / 4)) ≤ (4 / 1000 : ℝ) * B := by
    have h1 : (B / 1000000) ^ ((1 : ℝ) / 4) ≤ (B / 1000000) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith only [hB]) (by norm_num)
    have h2 : (B / 1000000) ^ ((1 : ℝ) / 2) = Real.sqrt B / 1000 := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_div hBpos.le]
      norm_num
    rw [h2] at h1
    have h3 : Real.sqrt B * (4 * (B / 1000000) ^ ((1 : ℝ) / 4)) ≤
        Real.sqrt B * (4 * (Real.sqrt B / 1000)) :=
      mul_le_mul_of_nonneg_left (by linarith only [h1]) (Real.sqrt_nonneg B)
    have h4 : Real.sqrt B * (4 * (Real.sqrt B / 1000)) = (4 / 1000 : ℝ) * B := by
      have hs := Real.mul_self_sqrt hBpos.le
      linear_combination (4 / 1000 : ℝ) * hs
    linarith only [h3, h4]
  have hsqrtB_logB : Real.sqrt B * Real.log B ≤ (18 / 1000 : ℝ) * B := by
    have h2 : Real.sqrt B * Real.log B ≤
        Real.sqrt B * (14 + 4 * (B / 1000000) ^ ((1 : ℝ) / 4)) :=
      mul_le_mul_of_nonneg_left hlogB_tight (Real.sqrt_nonneg B)
    linarith only [h2, hsqrt_term1, hsqrt_term2]
  have hsqrt_log_tight : Real.sqrt (N : ℝ) * Real.log (N : ℝ) ≤ (18 / 1000 : ℝ) * B := by
    have h1 : Real.sqrt (N : ℝ) * Real.log (N : ℝ) ≤ Real.sqrt B * Real.log B :=
      mul_le_mul hsqrtN hlogN (Real.log_nonneg (by linarith only [hNR, hB])) (Real.sqrt_nonneg B)
    linarith only [h1, hsqrtB_logB]
  have hlogN1_le : Real.log ((N : ℝ) + 1) ≤ (1 / 1000 : ℝ) * B := by
    have h1 : Real.log (2 * B) = Real.log 2 + Real.log B :=
      Real.log_mul (by norm_num) hBpos.ne'
    have h2 : 1000 * Real.log B ≤ Real.sqrt B * Real.log B :=
      mul_le_mul_of_nonneg_right hsqrtB_ge hlogB.le
    linarith only [hlogN1, h1, h2, hsqrtB_logB, hlog2_lt, hB]
  have hdiff_ge : B / 20 ≤ Chebyshev.theta (N : ℝ) - Chebyshev.theta (M : ℝ) := by
    have hMle : (M : ℝ) ≤ (21 / 50 : ℝ) * B :=
      hMRle.trans (mul_le_mul_of_nonneg_right hα hBpos.le)
    have hMbound : Real.log 4 * (M : ℝ) ≤ (42 / 50 : ℝ) * B * Real.log 2 := by
      rw [hlog4]
      have := mul_le_mul_of_nonneg_left hMle (by linarith only [hlog2_gt] : (0 : ℝ) ≤ 2 * Real.log 2)
      linarith only [this]
    have hNbound : (B - 1) * Real.log 2 ≤ (N : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hNR.le (by linarith only [hlog2_gt])
    have hmain : (8 / 50 : ℝ) * B * Real.log 2 - Real.log 2 ≥ (11 / 100 : ℝ) * B - 1 := by
      have h1 : (8 / 50 : ℝ) * (69 / 100 : ℝ) * B ≤ (8 / 50 : ℝ) * B * Real.log 2 := by
        have := mul_le_mul_of_nonneg_left hlog2_gt.le (by linarith only [hB] : (0 : ℝ) ≤ (8 / 50 : ℝ) * B)
        linarith only [this]
      linarith only [h1, hlog2_lt, hB]
    linarith only [hthN, hthM, hMbound, hNbound, hmain, hsqrt_log_tight, hlogN1_le, hB]
  rw [div_le_iff₀ (by positivity)]
  have hcomb : B / 20 ≤ (((Finset.Ioc M N).filter Nat.Prime).card : ℝ) * Real.log B :=
    hdiff_ge.trans (hdiff_eq ▸ hsum_le)
  linarith only [hcomb]

/- ## Part 3: Upper bound on `#{n ∈ [1, x] : PStar n > y}` and reciprocal sum bounds -/

/-- Elementary dyadic upper bound on `∑_{y < p ≤ x} 1/p`: for `x ≥ 16` and `√x ≤ y ≤ x`,
we have `∑_{p ∈ (Ioc ⌊y⌋₊ x).filter Prime} 1/p ≤ 64 * (log (x / y) + 1) / log x`. -/
lemma sum_inv_primes_Ioc_le {x : ℕ} {y : ℝ} (hx : 16 ≤ x) (hy_lo : Real.sqrt (x : ℝ) ≤ y)
    (hy_hi : y ≤ (x : ℝ)) :
    ∑ p ∈ (Finset.Ioc ⌊y⌋₊ x).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤
      64 * (Real.log ((x : ℝ) / y) + 1) / Real.log (x : ℝ) := by
  have hxR : (16 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hxpos : (0 : ℝ) < x := by linarith
  have hsqrt_pos : 0 < Real.sqrt (x : ℝ) := Real.sqrt_pos.mpr hxpos
  have hy_pos : 0 < y := lt_of_lt_of_le hsqrt_pos hy_lo
  have hlogx_pos : 0 < Real.log (x : ℝ) := Real.log_pos (by linarith)
  -- Let K = ⌊log((x:ℝ)/y) / log 2⌋₊ + 1, so y * 2^K > x.
  set K : ℕ := ⌊Real.log ((x : ℝ) / y) / Real.log 2⌋₊ + 1 with hKdef
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hxy_ge1 : (1 : ℝ) ≤ (x : ℝ) / y := (one_le_div hy_pos).mpr hy_hi
  have hK_pow : (x : ℝ) < y * (2 : ℝ) ^ K := by
    have hlt : Real.log ((x : ℝ) / y) / Real.log 2 < (K : ℝ) := by
      dsimp [K]
      exact_mod_cast Nat.lt_floor_add_one _
    have hlt2 : Real.log ((x : ℝ) / y) < (K : ℝ) * Real.log 2 := (div_lt_iff₀ hlog2_pos).mp hlt
    have hexp := Real.exp_lt_exp.mpr hlt2
    rw [Real.exp_log (div_pos hxpos hy_pos)] at hexp
    have h2K : Real.exp ((K : ℝ) * Real.log 2) = (2 : ℝ) ^ K := by
      rw [mul_comm, ← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
    rw [h2K, div_lt_iff₀ hy_pos] at hexp
    linarith
  -- Cover (⌊y⌋₊, x] by dyadic intervals (⌊y * 2^j⌋₊, ⌊y * 2^(j+1)⌋₊] (with Icc on lower end via p ≥ y * 2^j)
  have hcover : (Finset.Ioc ⌊y⌋₊ x).filter Nat.Prime ⊆
      (Finset.range K).biUnion (fun j =>
        (Finset.Icc ⌈y * (2 : ℝ) ^ j⌉₊ ⌊y * (2 : ℝ) ^ (j + 1)⌋₊).filter Nat.Prime) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    rw [Finset.mem_biUnion]
    have hp_gt : y < (p : ℝ) := (Nat.floor_lt hy_pos.le).mp hp.1.1
    have hp_le : (p : ℝ) ≤ (x : ℝ) := by exact_mod_cast hp.1.2
    set j : ℕ := ⌊Real.log ((p : ℝ) / y) / Real.log 2⌋₊
    have hpy1 : (1 : ℝ) < (p : ℝ) / y := (one_lt_div hy_pos).mpr hp_gt
    have hj_le : (j : ℝ) ≤ Real.log ((p : ℝ) / y) / Real.log 2 :=
      Nat.floor_le (div_nonneg (Real.log_nonneg hpy1.le) hlog2_pos.le)
    have hj_lt : Real.log ((p : ℝ) / y) / Real.log 2 < (j : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hjK : j < K := by
      have hdiv_le : Real.log ((p : ℝ) / y) / Real.log 2 ≤ Real.log ((x : ℝ) / y) / Real.log 2 :=
        div_le_div_of_nonneg_right
          (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hp_le hy_pos.le))
          hlog2_pos.le
      have hKgt : Real.log ((x : ℝ) / y) / Real.log 2 < (K : ℝ) := by
        dsimp [K]; exact_mod_cast Nat.lt_floor_add_one _
      have h1 : (j : ℝ) < (K : ℝ) := by linarith
      exact_mod_cast h1
    have hlo : y * (2 : ℝ) ^ j ≤ (p : ℝ) := by
      have hle1 : (j : ℝ) * Real.log 2 ≤ Real.log ((p : ℝ) / y) := (le_div_iff₀ hlog2_pos).mp hj_le
      have hexp := Real.exp_le_exp.mpr hle1
      rw [Real.exp_log (by positivity)] at hexp
      have h2j : Real.exp ((j : ℝ) * Real.log 2) = (2 : ℝ) ^ j := by
        rw [mul_comm, ← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
      rw [h2j, le_div_iff₀ hy_pos] at hexp
      linarith
    have hhi : (p : ℝ) < y * (2 : ℝ) ^ (j + 1) := by
      have hlt1 : Real.log ((p : ℝ) / y) < ((j : ℝ) + 1) * Real.log 2 :=
        (div_lt_iff₀ hlog2_pos).mp hj_lt
      have hexp := Real.exp_lt_exp.mpr hlt1
      rw [Real.exp_log (by positivity)] at hexp
      have h2j1 : Real.exp (((j : ℝ) + 1) * Real.log 2) = (2 : ℝ) ^ (j + 1) := by
        rw [show ((j : ℝ) + 1) = ((j + 1 : ℕ) : ℝ) by push_cast; ring,
          mul_comm, ← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
      rw [h2j1, div_lt_iff₀ hy_pos] at hexp
      linarith
    refine ⟨j, Finset.mem_range.mpr hjK, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, hp.2⟩⟩
    · exact Nat.ceil_le.mpr hlo
    · exact Nat.le_floor hhi.le
  -- Bound each dyadic block by 32 / log x
  have hblock : ∀ j ∈ Finset.range K,
      ∑ p ∈ (Finset.Icc ⌈y * (2 : ℝ) ^ j⌉₊ ⌊y * (2 : ℝ) ^ (j + 1)⌋₊).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ) ≤ 32 / Real.log (x : ℝ) := by
    intro j _
    set u : ℝ := y * (2 : ℝ) ^ j with hudef
    have hu_ge_sqrt : Real.sqrt (x : ℝ) ≤ u := by
      have h2j : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
      nlinarith
    have hu_ge4 : (4 : ℝ) ≤ u := by
      have : (4 : ℝ) ≤ Real.sqrt (x : ℝ) := by
        rw [show (4 : ℝ) = Real.sqrt 16 by norm_num]
        exact Real.sqrt_le_sqrt hxR
      linarith
    have hu_pos : 0 < u := by linarith
    have h2u_gt1 : (1 : ℝ) < 2 * u := by linarith
    have hu2_eq : y * (2 : ℝ) ^ (j + 1) = 2 * u := by dsimp [u]; ring
    rw [hu2_eq]
    calc ∑ p ∈ (Finset.Icc ⌈u⌉₊ ⌊2 * u⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ)
        ≤ ∑ _p ∈ (Finset.Icc ⌈u⌉₊ ⌊2 * u⌋₊).filter Nat.Prime, (1 : ℝ) / u := by
          apply Finset.sum_le_sum
          intro p hp
          have hp_ge : u ≤ (p : ℝ) := le_trans (Nat.le_ceil u) (by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1)
          exact one_div_le_one_div_of_le hu_pos hp_ge
      _ = (((Finset.Icc ⌈u⌉₊ ⌊2 * u⌋₊).filter Nat.Prime).card : ℝ) / u := by
          simp [div_eq_mul_inv]
      _ ≤ (Nat.primeCounting ⌊2 * u⌋₊ : ℝ) / u := by
          apply div_le_div_of_nonneg_right _ hu_pos.le
          rw [← Nat.primesLE_card_eq_primeCounting]
          exact_mod_cast Finset.card_le_card (fun p hp => by
            rw [Finset.mem_filter, Finset.mem_Icc] at hp
            exact Nat.mem_primesLE.mpr ⟨hp.1.2, hp.2⟩)
      _ ≤ (Real.log 4 * (2 * u) / Real.log (Real.sqrt (2 * u)) + Real.sqrt (2 * u)) / u := by
          apply div_le_div_of_nonneg_right (Chebyshev.pi_le_log4_mul_div h2u_gt1) hu_pos.le
      _ ≤ 32 / Real.log (x : ℝ) := by
          have hlog_sq : Real.log (Real.sqrt (2 * u)) = Real.log (2 * u) / 2 :=
            Real.log_sqrt (by positivity)
          have hlog2u_ge : Real.log (x : ℝ) / 2 ≤ Real.log (2 * u) := by
            have h1 : Real.sqrt (x : ℝ) ≤ 2 * u := by linarith
            have h2 := Real.log_le_log hsqrt_pos h1
            rw [Real.log_sqrt hxpos.le] at h2
            exact h2
          have hlog2u_pos : 0 < Real.log (2 * u) := by linarith
          have hlog4_le : Real.log (4 : ℝ) ≤ 2 := by
            have := Real.log_two_lt_d9
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
            norm_num; linarith
          have ht1 : Real.log 4 * (2 * u) / Real.log (Real.sqrt (2 * u)) / u ≤ 16 / Real.log (x : ℝ) := by
            rw [hlog_sq]
            have hrw : Real.log 4 * (2 * u) / (Real.log (2 * u) / 2) / u =
                4 * Real.log 4 / Real.log (2 * u) := by field_simp; ring
            rw [hrw]
            calc 4 * Real.log 4 / Real.log (2 * u)
                ≤ 8 / (Real.log (x : ℝ) / 2) := by
                  apply div_le_div₀ (by norm_num) (by linarith) (by positivity) hlog2u_ge
              _ = 16 / Real.log (x : ℝ) := by field_simp; ring
          have ht2 : Real.sqrt (2 * u) / u ≤ 16 / Real.log (x : ℝ) := by
            -- √(2u)/u = √2 / √u; also log(√u) ≤ √u implies log(x)/4 ≤ √u!
            have hlog_sqrtu : Real.log (Real.sqrt u) ≤ Real.sqrt u := by
              linarith [Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hu_pos)]
            have hlogx4 : Real.log (x : ℝ) / 4 ≤ Real.sqrt u := by
              have h1 := Real.log_le_log hsqrt_pos hu_ge_sqrt
              rw [Real.log_sqrt hxpos.le] at h1
              rw [Real.log_sqrt hu_pos.le] at hlog_sqrtu
              linarith
            have hsqrt2 : Real.sqrt (2 * u) ≤ 2 * Real.sqrt u := by
              rw [Real.sqrt_mul (by norm_num)]
              have : Real.sqrt 2 ≤ 2 := by
                rw [Real.sqrt_le_left (by norm_num)]; norm_num
              nlinarith [Real.sqrt_nonneg u]
            have hsu_pos : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu_pos
            have hsq_u : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu_pos.le
            have hrw2 : 2 * Real.sqrt u / u = 2 / Real.sqrt u := by
              rw [div_eq_div_iff hu_pos.ne' hsu_pos.ne']
              linear_combination 2 * hsq_u
            calc Real.sqrt (2 * u) / u ≤ 2 * Real.sqrt u / u :=
                  div_le_div_of_nonneg_right hsqrt2 hu_pos.le
              _ = 2 / Real.sqrt u := hrw2
              _ ≤ 2 / (Real.log (x : ℝ) / 4) :=
                  div_le_div_of_nonneg_left (by norm_num) (by positivity) hlogx4
              _ = 8 / Real.log (x : ℝ) := by field_simp; ring
              _ ≤ 16 / Real.log (x : ℝ) := by
                  apply div_le_div_of_nonneg_right (by norm_num) hlogx_pos.le
          rw [add_div]
          have h32 : 16 / Real.log (x : ℝ) + 16 / Real.log (x : ℝ) = 32 / Real.log (x : ℝ) := by ring
          linarith only [ht1, ht2, h32]
  have hbiU : ∀ (s : Finset ℕ) (t : ℕ → Finset ℕ),
      ∑ p ∈ s.biUnion t, (1 : ℝ) / (p : ℝ) ≤ ∑ j ∈ s, ∑ p ∈ t j, (1 : ℝ) / (p : ℝ) := by
    intro s t
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      calc ∑ p ∈ t a ∪ s.biUnion t, (1 : ℝ) / (p : ℝ)
          ≤ (∑ p ∈ t a, (1 : ℝ) / (p : ℝ)) + ∑ p ∈ s.biUnion t, (1 : ℝ) / (p : ℝ) := by
            have h := Finset.sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := fun p : ℕ => (1 : ℝ) / (p : ℝ))
            have hnn : 0 ≤ ∑ p ∈ t a ∩ s.biUnion t, (1 : ℝ) / (p : ℝ) := Finset.sum_nonneg (fun _ _ => by positivity)
            linarith only [h, hnn]
        _ ≤ (∑ p ∈ t a, (1 : ℝ) / (p : ℝ)) + ∑ j ∈ s, ∑ p ∈ t j, (1 : ℝ) / (p : ℝ) :=
            add_le_add_right ih _
  have hsum_le : ∑ p ∈ (Finset.Ioc ⌊y⌋₊ x).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤
      (K : ℝ) * (32 / Real.log (x : ℝ)) := by
    calc ∑ p ∈ (Finset.Ioc ⌊y⌋₊ x).filter Nat.Prime, (1 : ℝ) / (p : ℝ)
        ≤ ∑ p ∈ (Finset.range K).biUnion (fun j =>
            (Finset.Icc ⌈y * (2 : ℝ) ^ j⌉₊ ⌊y * (2 : ℝ) ^ (j + 1)⌋₊).filter Nat.Prime),
            (1 : ℝ) / (p : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hcover (fun _ _ _ => by positivity)
      _ ≤ ∑ j ∈ Finset.range K,
            ∑ p ∈ (Finset.Icc ⌈y * (2 : ℝ) ^ j⌉₊ ⌊y * (2 : ℝ) ^ (j + 1)⌋₊).filter Nat.Prime,
              (1 : ℝ) / (p : ℝ) := hbiU _ _
      _ ≤ ∑ _j ∈ Finset.range K, (32 / Real.log (x : ℝ)) :=
          Finset.sum_le_sum hblock
      _ = (K : ℝ) * (32 / Real.log (x : ℝ)) := by simp
  have hK_le : (K : ℝ) ≤ 2 * (Real.log ((x : ℝ) / y) + 1) := by
    have hfl : (⌊Real.log ((x : ℝ) / y) / Real.log 2⌋₊ : ℝ) ≤
        Real.log ((x : ℝ) / y) / Real.log 2 :=
      Nat.floor_le (div_nonneg (Real.log_nonneg hxy_ge1) hlog2_pos.le)
    have hlog2_ge : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hdiv_le : Real.log ((x : ℝ) / y) / Real.log 2 ≤ 2 * Real.log ((x : ℝ) / y) := by
      rw [div_le_iff₀ hlog2_pos]
      nlinarith [Real.log_nonneg hxy_ge1]
    dsimp [K]
    push_cast
    linarith
  calc ∑ p ∈ (Finset.Ioc ⌊y⌋₊ x).filter Nat.Prime, (1 : ℝ) / (p : ℝ)
      ≤ (K : ℝ) * (32 / Real.log (x : ℝ)) := hsum_le
    _ ≤ 2 * (Real.log ((x : ℝ) / y) + 1) * (32 / Real.log (x : ℝ)) :=
        mul_le_mul_of_nonneg_right hK_le (by positivity)
    _ = 64 * (Real.log ((x : ℝ) / y) + 1) / Real.log (x : ℝ) := by ring

/-- Upper bound on the number of integers in `[1, x]` divisible by a proper prime power `p^ν > y`
with `ν ≥ 2`: at most `2 * x / √y + 2 * x^(4/3) / y`. -/
lemma card_proper_prime_pow_gt_le {x : ℕ} {y : ℝ} (hx : 16 ≤ x) (hy : 1 ≤ y) :
    (((Finset.Icc 1 x).filter (fun n =>
        ∃ p ν : ℕ, p.Prime ∧ 2 ≤ ν ∧ y < ((p ^ ν : ℕ) : ℝ) ∧ p ^ ν ∣ n)).card : ℝ) ≤
      2 * (x : ℝ) / Real.sqrt y + 2 * (x : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 3) / y := by
  classical
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hypos : 0 < y := by linarith
  set S2 := (Finset.Icc 1 x).filter (fun n =>
      ∃ p : ℕ, p.Prime ∧ y < ((p ^ 2 : ℕ) : ℝ) ∧ p ^ 2 ∣ n)
  set S3 := (Finset.Icc 1 x).filter (fun n =>
      ∃ p ν : ℕ, p.Prime ∧ 3 ≤ ν ∧ y < ((p ^ ν : ℕ) : ℝ) ∧ p ^ ν ∣ n)
  have hsub : (Finset.Icc 1 x).filter (fun n =>
        ∃ p ν : ℕ, p.Prime ∧ 2 ≤ ν ∧ y < ((p ^ ν : ℕ) : ℝ) ∧ p ^ ν ∣ n) ⊆ S2 ∪ S3 := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hnI, p, ν, hp, hν, hgt, hdvd⟩ := hn
    rw [Finset.mem_union]
    rcases (show ν = 2 ∨ 3 ≤ ν by omega) with rfl | hν3
    · exact Or.inl (Finset.mem_filter.mpr ⟨hnI, p, hp, hgt, hdvd⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨hnI, p, ν, hp, hν3, hgt, hdvd⟩)
  -- Bound |S2| ≤ ∑_{m > ⌊√y⌋₊, m ≤ x} ⌊x / m^2⌋ ≤ x * ∑_{m = ⌊√y⌋₊ + 1}^{x} 1/(m*(m-1)) ≤ 2*x/√y
  have hS2 : (S2.card : ℝ) ≤ 2 * (x : ℝ) / Real.sqrt y := by
    set L := ⌊Real.sqrt y⌋₊
    have hLpos : 1 ≤ L := Nat.le_floor (by push_cast; rw [Real.one_le_sqrt]; exact hy)
    have hS2sub : S2 ⊆ (Finset.Icc (L + 1) x).biUnion (fun m =>
        (Finset.Icc 1 x).filter (fun n => m ^ 2 ∣ n)) := by
      intro n hn
      rw [Finset.mem_filter] at hn
      obtain ⟨hnI, p, hp, hgt, hdvd⟩ := hn
      rw [Finset.mem_biUnion]
      have hp_gt : Real.sqrt y < (p : ℝ) := by
        rw [Real.sqrt_lt' (by exact_mod_cast hp.pos)]
        exact_mod_cast hgt
      have hpL : L + 1 ≤ p := by
        have : L < p := (Nat.floor_lt (Real.sqrt_nonneg y)).mpr hp_gt
        omega
      have hpx : p ≤ x := by
        have h1 : p ^ 2 ≤ n := Nat.le_of_dvd (Finset.mem_Icc.mp hnI).1 hdvd
        have h2 : n ≤ x := (Finset.mem_Icc.mp hnI).2
        have h3 : p ≤ p ^ 2 := Nat.le_self_pow (by norm_num) p
        omega
      exact ⟨p, Finset.mem_Icc.mpr ⟨hpL, hpx⟩, Finset.mem_filter.mpr ⟨hnI, hdvd⟩⟩
    have hmult : ∀ m : ℕ, 0 < m →
        (((Finset.Icc 1 x).filter (fun n => m ^ 2 ∣ n)).card : ℝ) ≤ (x : ℝ) / ((m : ℝ) ^ 2) := by
      intro m hm
      have hcard : ((Finset.Icc 1 x).filter (fun n => m ^ 2 ∣ n)).card ≤ x / m ^ 2 := by
        have hinj : (Finset.Icc 1 x).filter (fun n => m ^ 2 ∣ n) ⊆
            (Finset.Icc 1 (x / m ^ 2)).image (fun k => k * m ^ 2) := by
          intro n hn
          rw [Finset.mem_filter, Finset.mem_Icc] at hn
          obtain ⟨⟨hn1, hnx⟩, k, rfl⟩ := hn
          rw [Finset.mem_image]
          refine ⟨k, Finset.mem_Icc.mpr ⟨?_, ?_⟩, mul_comm _ _⟩
          · rcases Nat.eq_zero_or_pos k with rfl | hk
            · simp at hn1
            · exact hk
          · rw [Nat.le_div_iff_mul_le (pow_pos hm 2)]
            linarith
        calc ((Finset.Icc 1 x).filter (fun n => m ^ 2 ∣ n)).card
            ≤ ((Finset.Icc 1 (x / m ^ 2)).image (fun k => k * m ^ 2)).card := Finset.card_le_card hinj
          _ ≤ (Finset.Icc 1 (x / m ^ 2)).card := Finset.card_image_le
          _ = x / m ^ 2 := by simp
      have h1 : ((x / m ^ 2 : ℕ) : ℝ) ≤ (x : ℝ) / ((m : ℝ) ^ 2) := by
        rw [le_div_iff₀ (by positivity)]
        exact_mod_cast Nat.div_mul_le_self x (m ^ 2)
      exact le_trans (by exact_mod_cast hcard) h1
    have hsum_inv_sq : ∑ m ∈ Finset.Icc (L + 1) x, (1 : ℝ) / ((m : ℝ) ^ 2) ≤ 2 / Real.sqrt y := by
      have htele : ∑ m ∈ Finset.Icc (L + 1) x, (1 : ℝ) / ((m : ℝ) ^ 2) ≤
          ∑ m ∈ Finset.Icc (L + 1) x, ((1 : ℝ) / ((m : ℝ) - 1) - (1 : ℝ) / (m : ℝ)) := by
        apply Finset.sum_le_sum
        intro m hm
        have hm2 : 2 ≤ m := by have := (Finset.mem_Icc.mp hm).1; omega
        have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm2
        have h1 : (1 : ℝ) / ((m : ℝ) - 1) - (1 : ℝ) / (m : ℝ) =
            1 / ((m : ℝ) * ((m : ℝ) - 1)) := by
          have hm0 : (m : ℝ) ≠ 0 := by linarith only [hmR]
          have hm1 : (m : ℝ) - 1 ≠ 0 := by linarith only [hmR]
          field_simp [hm0, hm1]
          ring
        rw [h1]
        apply one_div_le_one_div_of_le (by nlinarith) (by nlinarith)
      -- Telescope the RHS
      have htele_le : ∑ m ∈ Finset.Icc (L + 1) x,
            ((1 : ℝ) / ((m : ℝ) - 1) - (1 : ℝ) / (m : ℝ)) ≤ 1 / (L : ℝ) := by
        by_cases hLx : L + 1 ≤ x
        · have hreidx : ∑ m ∈ Finset.Icc (L + 1) x,
              ((1 : ℝ) / ((m : ℝ) - 1) - (1 : ℝ) / (m : ℝ)) =
              ∑ k ∈ Finset.range (x - L),
                ((1 : ℝ) / ((L + k : ℕ) : ℝ) - (1 : ℝ) / ((L + (k + 1) : ℕ) : ℝ)) := by
            refine Finset.sum_bij (fun m _ => m - (L + 1)) ?_ ?_ ?_ ?_
            · intro m hm; rw [Finset.mem_Icc] at hm; rw [Finset.mem_range]; omega
            · intro m₁ hm₁ m₂ hm₂ h; rw [Finset.mem_Icc] at hm₁ hm₂; omega
            · intro k hk; rw [Finset.mem_range] at hk
              exact ⟨L + 1 + k, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
            · intro m hm; rw [Finset.mem_Icc] at hm
              have e1 : L + (m - (L + 1)) = m - 1 := by omega
              have e2 : L + (m - (L + 1) + 1) = m := by omega
              rw [e1, e2, Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
          rw [hreidx]
          have hsum_t : ∀ n : ℕ, ∑ k ∈ Finset.range n,
              ((1 : ℝ) / ((L + k : ℕ) : ℝ) - (1 : ℝ) / ((L + (k + 1) : ℕ) : ℝ)) =
              (1 : ℝ) / (L : ℝ) - (1 : ℝ) / ((L + n : ℕ) : ℝ) := by
            intro n
            induction n with
            | zero => simp
            | succ n ih =>
              rw [Finset.sum_range_succ, ih]
              ring
          rw [hsum_t]
          have hnn : (0 : ℝ) ≤ 1 / ((L + (x - L) : ℕ) : ℝ) := by positivity
          linarith
        · have hempty : Finset.Icc (L + 1) x = ∅ := Finset.Icc_eq_empty (by omega)
          rw [hempty, Finset.sum_empty]
          positivity
      have hLge : Real.sqrt y / 2 ≤ (L : ℝ) := by
        have h1 : Real.sqrt y - 1 < (L : ℝ) := Nat.sub_one_lt_floor (Real.sqrt y)
        have h2 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLpos
        linarith
      have h1L : 1 / (L : ℝ) ≤ 2 / Real.sqrt y := by
        calc 1 / (L : ℝ) ≤ 1 / (Real.sqrt y / 2) :=
              one_div_le_one_div_of_le (by positivity) hLge
          _ = 2 / Real.sqrt y := by field_simp
      exact htele.trans (htele_le.trans h1L)
    calc (S2.card : ℝ)
        ≤ (((Finset.Icc (L + 1) x).biUnion (fun m =>
            (Finset.Icc 1 x).filter (fun n => m ^ 2 ∣ n))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hS2sub
      _ ≤ ∑ m ∈ Finset.Icc (L + 1) x,
            (((Finset.Icc 1 x).filter (fun n => m ^ 2 ∣ n)).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ m ∈ Finset.Icc (L + 1) x, (x : ℝ) / ((m : ℝ) ^ 2) := by
          apply Finset.sum_le_sum
          intro m hm
          exact hmult m (by have := (Finset.mem_Icc.mp hm).1; omega)
      _ = (x : ℝ) * ∑ m ∈ Finset.Icc (L + 1) x, (1 : ℝ) / ((m : ℝ) ^ 2) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro m _; ring
      _ ≤ (x : ℝ) * (2 / Real.sqrt y) := mul_le_mul_of_nonneg_left hsum_inv_sq hxpos.le
      _ = 2 * (x : ℝ) / Real.sqrt y := by ring
  -- Bound |S3| ≤ 2 * x * x^(1/3) / y: for each p ≤ ⌊x^(1/3)⌋₊ (prime), let ν₀ be least ≥ 3 with p^ν₀ > y.
  -- Every n ∈ S3 divisible by some p^ν > y (ν ≥ 3) is divisible by p^ν₀, and there are ≤ x / p^ν₀ ≤ x / y such n!
  have hS3 : (S3.card : ℝ) ≤ 2 * (x : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 3) / y := by
    set P3 := (Finset.Icc 2 ⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊).filter Nat.Prime
    -- For each p ∈ P3, pick minimal ν₀ ≥ 3 with y < p^ν₀ (if exists, always exists since p ≥ 2)
    have hex : ∀ p : ℕ, 2 ≤ p → ∃ ν : ℕ, 3 ≤ ν ∧ y < ((p ^ ν : ℕ) : ℝ) := by
      intro p hp
      obtain ⟨k, hk⟩ := exists_nat_gt y
      refine ⟨max 3 k, le_max_left _ _, ?_⟩
      have h1 : (k : ℝ) ≤ (2 ^ k : ℕ) := by exact_mod_cast Nat.lt_two_pow_self.le
      have h2 : 2 ^ k ≤ p ^ max 3 k :=
        le_trans (Nat.pow_le_pow_left hp k) (Nat.pow_le_pow_right (by omega) (le_max_right 3 k))
      have h3 : ((2 ^ k : ℕ) : ℝ) ≤ ((p ^ max 3 k : ℕ) : ℝ) := by exact_mod_cast h2
      linarith
    let νmin (p : ℕ) : ℕ := if h : 2 ≤ p then Nat.find (hex p h) else 3
    have hνmin_spec : ∀ p : ℕ, 2 ≤ p → 3 ≤ νmin p ∧ y < ((p ^ νmin p : ℕ) : ℝ) := by
      intro p hp
      simpa [νmin, hp] using Nat.find_spec (hex p hp)
    have hνmin_le : ∀ p ν : ℕ, 2 ≤ p → 3 ≤ ν → y < ((p ^ ν : ℕ) : ℝ) → νmin p ≤ ν := by
      intro p ν hp hν hgt
      simpa [νmin, hp] using Nat.find_min' (hex p hp) ⟨hν, hgt⟩
    have hS3sub : S3 ⊆ P3.biUnion (fun p =>
        (Finset.Icc 1 x).filter (fun n => p ^ νmin p ∣ n)) := by
      intro n hn
      rw [Finset.mem_filter] at hn
      obtain ⟨hnI, p, ν, hp, hν3, hgt, hdvd⟩ := hn
      rw [Finset.mem_biUnion]
      have hp_cub : p ^ 3 ≤ x := by
        have h1 : p ^ 3 ≤ p ^ ν := Nat.pow_le_pow_right hp.pos hν3
        have h2 : p ^ ν ≤ n := Nat.le_of_dvd (Finset.mem_Icc.mp hnI).1 hdvd
        have h3 : n ≤ x := (Finset.mem_Icc.mp hnI).2
        omega
      have hp_le : p ≤ ⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ := by
        apply Nat.le_floor
        have h1 : ((p : ℝ) ^ (3 : ℝ)) ≤ (x : ℝ) := by exact_mod_cast hp_cub
        have h2 := Real.rpow_le_rpow (by positivity) h1 (by positivity : (0 : ℝ) ≤ 1 / 3)
        rw [← Real.rpow_mul (by positivity)] at h2
        norm_num at h2
        exact h2
      have hle : νmin p ≤ ν := hνmin_le p ν hp.two_le hν3 hgt
      have hdvd0 : p ^ νmin p ∣ n := dvd_trans (pow_dvd_pow p hle) hdvd
      exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le, hp_le⟩, hp⟩,
        Finset.mem_filter.mpr ⟨hnI, hdvd0⟩⟩
    have heach : ∀ p ∈ P3,
        (((Finset.Icc 1 x).filter (fun n => p ^ νmin p ∣ n)).card : ℝ) ≤ (x : ℝ) / y := by
      intro p hp
      have hp2 : 2 ≤ p := (Finset.mem_filter.mp hp).2.two_le
      have hspec := hνmin_spec p hp2
      set q := p ^ νmin p
      have hqpos : 0 < q := pow_pos (by omega) _
      have hcard : ((Finset.Icc 1 x).filter (fun n => q ∣ n)).card ≤ x / q := by
        have hinj : (Finset.Icc 1 x).filter (fun n => q ∣ n) ⊆
            (Finset.Icc 1 (x / q)).image (fun k => k * q) := by
          intro n hn
          rw [Finset.mem_filter, Finset.mem_Icc] at hn
          obtain ⟨⟨hn1, hnx⟩, k, rfl⟩ := hn
          rw [Finset.mem_image]
          refine ⟨k, Finset.mem_Icc.mpr ⟨?_, ?_⟩, mul_comm _ _⟩
          · rcases Nat.eq_zero_or_pos k with rfl | hk
            · simp at hn1
            · exact hk
          · rw [Nat.le_div_iff_mul_le hqpos]; linarith
        calc ((Finset.Icc 1 x).filter (fun n => q ∣ n)).card
            ≤ ((Finset.Icc 1 (x / q)).image (fun k => k * q)).card := Finset.card_le_card hinj
          _ ≤ (Finset.Icc 1 (x / q)).card := Finset.card_image_le
          _ = x / q := by simp
      have h1 : ((x / q : ℕ) : ℝ) ≤ (x : ℝ) / (q : ℝ) := by
        rw [le_div_iff₀ (by exact_mod_cast hqpos)]
        exact_mod_cast Nat.div_mul_le_self x q
      have h2 : (x : ℝ) / (q : ℝ) ≤ (x : ℝ) / y :=
        div_le_div_of_nonneg_left hxpos.le hypos hspec.2.le
      exact (le_trans (by exact_mod_cast hcard) h1).trans h2
    have hP3card : (P3.card : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := by
      have h1 : P3.card ≤ ⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ := by
        calc P3.card ≤ (Finset.Icc 2 ⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊).card :=
              Finset.card_le_card (Finset.filter_subset _ _)
          _ ≤ ⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ := by simp
      exact le_trans (by exact_mod_cast h1) (Nat.floor_le (by positivity))
    calc (S3.card : ℝ)
        ≤ ((P3.biUnion (fun p => (Finset.Icc 1 x).filter (fun n => p ^ νmin p ∣ n))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hS3sub
      _ ≤ ∑ p ∈ P3, (((Finset.Icc 1 x).filter (fun n => p ^ νmin p ∣ n)).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ P3, (x : ℝ) / y := Finset.sum_le_sum heach
      _ = (P3.card : ℝ) * ((x : ℝ) / y) := by simp
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / 3) * ((x : ℝ) / y) := mul_le_mul_of_nonneg_right hP3card (by positivity)
      _ ≤ 2 * (x : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 3) / y := by
          have hnn : (0 : ℝ) ≤ (x : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 3) / y := by positivity
          have heq : (x : ℝ) ^ ((1 : ℝ) / 3) * ((x : ℝ) / y) = (x : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 3) / y := by ring
          have heq2 : 2 * (x : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 3) / y = 2 * ((x : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 3) / y) := by ring
          linarith only [hnn, heq, heq2]
  have hunion : (((Finset.Icc 1 x).filter (fun n =>
        ∃ p ν : ℕ, p.Prime ∧ 2 ≤ ν ∧ y < ((p ^ ν : ℕ) : ℝ) ∧ p ^ ν ∣ n)).card : ℝ) ≤
      (S2.card : ℝ) + (S3.card : ℝ) := by
    have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le S2 S3)
    exact_mod_cast h1
  linarith

/-- Total count of `n ∈ [1, x]` with `PStar n > y` when `x ≥ 16` and `√x ≤ y ≤ x`. -/
lemma card_PStar_gt_le {x : ℕ} {y : ℝ} (hx : 16 ≤ x) (hy_lo : Real.sqrt (x : ℝ) ≤ y)
    (hy_hi : y ≤ (x : ℝ)) :
    (((Finset.Icc 1 x).filter (fun n => y < (PStar n : ℝ))).card : ℝ) ≤
      64 * (x : ℝ) * (Real.log ((x : ℝ) / y) + 1) / Real.log (x : ℝ) +
      2 * (x : ℝ) / Real.sqrt y + 2 * (x : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 3) / y := by
  classical
  have hxR : (16 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hxpos : (0 : ℝ) < x := by linarith
  have hy1 : (1 : ℝ) ≤ y := by
    have : (4 : ℝ) ≤ Real.sqrt (x : ℝ) := by
      rw [show (4 : ℝ) = Real.sqrt 16 by norm_num]
      exact Real.sqrt_le_sqrt hxR
    linarith
  set S1 := (Finset.Icc 1 x).filter (fun n =>
      ∃ p : ℕ, p.Prime ∧ y < (p : ℝ) ∧ p ∣ n)
  set Sprop := (Finset.Icc 1 x).filter (fun n =>
      ∃ p ν : ℕ, p.Prime ∧ 2 ≤ ν ∧ y < ((p ^ ν : ℕ) : ℝ) ∧ p ^ ν ∣ n)
  have hsub : (Finset.Icc 1 x).filter (fun n => y < (PStar n : ℝ)) ⊆ S1 ∪ Sprop := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hnI, hgt⟩ := hn
    have hn1 : 1 < n := by
      have hge1 : 1 ≤ n := (Finset.mem_Icc.mp hnI).1
      rcases (show n = 1 ∨ 1 < n by omega) with rfl | h
      · simp [PStar_one] at hgt; linarith
      · exact h
    obtain ⟨p, ν, hp, hν, hpeq, hdvd, _⟩ := exists_prime_pow_eq_PStar hn1
    rw [Finset.mem_union]
    rcases (show ν = 1 ∨ 2 ≤ ν by omega) with rfl | hν2
    · left
      rw [pow_one] at hpeq hdvd
      exact Finset.mem_filter.mpr ⟨hnI, p, hp, by rwa [hpeq], hdvd⟩
    · right
      exact Finset.mem_filter.mpr ⟨hnI, p, ν, hp, hν2, by rwa [hpeq], hdvd⟩
  have hS1 : (S1.card : ℝ) ≤ 64 * (x : ℝ) * (Real.log ((x : ℝ) / y) + 1) / Real.log (x : ℝ) := by
    have hS1sub : S1 ⊆ ((Finset.Ioc ⌊y⌋₊ x).filter Nat.Prime).biUnion (fun p =>
        (Finset.Icc 1 x).filter (fun n => p ∣ n)) := by
      intro n hn
      rw [Finset.mem_filter] at hn
      obtain ⟨hnI, p, hp, hgt, hdvd⟩ := hn
      rw [Finset.mem_biUnion]
      have hp_lo : ⌊y⌋₊ < p := (Nat.floor_lt (by linarith)).mpr hgt
      have hp_hi : p ≤ x := (Nat.le_of_dvd (Finset.mem_Icc.mp hnI).1 hdvd).trans (Finset.mem_Icc.mp hnI).2
      exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hp_lo, hp_hi⟩, hp⟩,
        Finset.mem_filter.mpr ⟨hnI, hdvd⟩⟩
    have hmult : ∀ p : ℕ, 0 < p →
        (((Finset.Icc 1 x).filter (fun n => p ∣ n)).card : ℝ) ≤ (x : ℝ) / (p : ℝ) := by
      intro p hp
      have hcard : ((Finset.Icc 1 x).filter (fun n => p ∣ n)).card ≤ x / p := by
        have hinj : (Finset.Icc 1 x).filter (fun n => p ∣ n) ⊆
            (Finset.Icc 1 (x / p)).image (fun k => k * p) := by
          intro n hn
          rw [Finset.mem_filter, Finset.mem_Icc] at hn
          obtain ⟨⟨hn1, hnx⟩, k, rfl⟩ := hn
          rw [Finset.mem_image]
          refine ⟨k, Finset.mem_Icc.mpr ⟨?_, ?_⟩, mul_comm _ _⟩
          · rcases Nat.eq_zero_or_pos k with rfl | hk
            · simp at hn1
            · exact hk
          · rw [Nat.le_div_iff_mul_le hp]; linarith
        calc ((Finset.Icc 1 x).filter (fun n => p ∣ n)).card
            ≤ ((Finset.Icc 1 (x / p)).image (fun k => k * p)).card := Finset.card_le_card hinj
          _ ≤ (Finset.Icc 1 (x / p)).card := Finset.card_image_le
          _ = x / p := by simp
      have h1 : ((x / p : ℕ) : ℝ) ≤ (x : ℝ) / (p : ℝ) := by
        rw [le_div_iff₀ (by exact_mod_cast hp)]
        exact_mod_cast Nat.div_mul_le_self x p
      exact le_trans (by exact_mod_cast hcard) h1
    calc (S1.card : ℝ)
        ≤ ((((Finset.Ioc ⌊y⌋₊ x).filter Nat.Prime).biUnion (fun p =>
            (Finset.Icc 1 x).filter (fun n => p ∣ n))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hS1sub
      _ ≤ ∑ p ∈ (Finset.Ioc ⌊y⌋₊ x).filter Nat.Prime,
            (((Finset.Icc 1 x).filter (fun n => p ∣ n)).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ p ∈ (Finset.Ioc ⌊y⌋₊ x).filter Nat.Prime, (x : ℝ) / (p : ℝ) :=
          Finset.sum_le_sum (fun p hp => hmult p (Finset.mem_filter.mp hp).2.pos)
      _ = (x : ℝ) * ∑ p ∈ (Finset.Ioc ⌊y⌋₊ x).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
      _ ≤ (x : ℝ) * (64 * (Real.log ((x : ℝ) / y) + 1) / Real.log (x : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_inv_primes_Ioc_le hx hy_lo hy_hi) hxpos.le
      _ = 64 * (x : ℝ) * (Real.log ((x : ℝ) / y) + 1) / Real.log (x : ℝ) := by ring
  have hSp := card_proper_prime_pow_gt_le hx hy1
  have hu : (((Finset.Icc 1 x).filter (fun n => y < (PStar n : ℝ))).card : ℝ) ≤
      (S1.card : ℝ) + (Sprop.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le S1 Sprop)
  linarith

/-- Lower bound on `∑_{n ∈ [⌈α x⌉₊, x], PStar n > y} 1 / n` using Chebyshev's prime-interval
lower bound on `m * p` for `1 ≤ m ≤ M`, where `M * 10^6 ≤ x` and `M ≤ α * x / y`. -/
lemma sum_inv_PStar_gt_ge {x M : ℕ} {α y : ℝ}
    (hα0 : 0 < α) (hα : α ≤ 21 / 50)
    (hx : 16 ≤ x) (_hM1 : 1 ≤ M)
    (hy_lo : Real.sqrt (x : ℝ) < y)
    (hM_big : 1000000 * (M : ℝ) ≤ (x : ℝ))
    (hMy : (M : ℝ) * y ≤ α * (x : ℝ)) :
    (Real.log ((M : ℝ) + 1)) / (20 * Real.log (x : ℝ)) ≤
      ∑ n ∈ (Finset.Icc ⌈α * (x : ℝ)⌉₊ x).filter (fun n => y < (PStar n : ℝ)),
        (1 : ℝ) / (n : ℝ) := by
  classical
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hlogx_pos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  set T := (Finset.Icc ⌈α * (x : ℝ)⌉₊ x).filter (fun n => y < (PStar n : ℝ))
  -- For each m ∈ [1, M], let B_m = {m * p : p prime, ⌊α x / m⌋₊ < p ≤ ⌊x / m⌋₊}.
  -- Notice every p > α x / m ≥ y > √x, so p is the unique prime factor > √x of m * p!
  -- Hence the sets B_m are pairwise disjoint subsets of T!
  let Pm (m : ℕ) : Finset ℕ := (Finset.Ioc ⌊α * ((x : ℝ) / (m : ℝ))⌋₊ ⌊(x : ℝ) / (m : ℝ)⌋₊).filter Nat.Prime
  let Bm (m : ℕ) : Finset ℕ := (Pm m).image (fun p => m * p)
  have hBm_sub : ∀ m ∈ Finset.Icc 1 M, Bm m ⊆ T := by
    intro m hm n hn
    rw [Finset.mem_Icc] at hm
    rcases Finset.mem_image.mp hn with ⟨p, hp, rfl⟩
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hp_gt : α * ((x : ℝ) / (m : ℝ)) < (p : ℝ) :=
      (Nat.floor_lt (by positivity)).mp hp.1.1
    have hp_le : (p : ℝ) ≤ (x : ℝ) / (m : ℝ) :=
      le_trans (by exact_mod_cast hp.1.2) (Nat.floor_le (by positivity))
    have hmp_gt : α * (x : ℝ) < (m : ℝ) * (p : ℝ) := by
      have := mul_lt_mul_of_pos_left hp_gt hmpos
      rwa [show (m : ℝ) * (α * ((x : ℝ) / (m : ℝ))) = α * (x : ℝ) by field_simp] at this
    have hmp_le : (m : ℝ) * (p : ℝ) ≤ (x : ℝ) := by
      have := mul_le_mul_of_nonneg_left hp_le hmpos.le
      rwa [show (m : ℝ) * ((x : ℝ) / (m : ℝ)) = (x : ℝ) by field_simp] at this
    have hp_y : y < (p : ℝ) := by
      have hmM : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hm.2
      have h1 : (m : ℝ) * y ≤ α * (x : ℝ) :=
        (mul_le_mul_of_nonneg_right hmM (by linarith [Real.sqrt_nonneg (x : ℝ)])).trans hMy
      nlinarith
    have hmp_pos : 0 < m * p := Nat.mul_pos (by omega) hp.2.pos
    have hPStar : p ≤ PStar (m * p) := by
      have := prime_pow_dvd_le_PStar hmp_pos hp.2 (show p ^ 1 ∣ m * p by simp)
      simpa using this
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Nat.ceil_le.mpr (by exact_mod_cast hmp_gt.le)
    · exact_mod_cast hmp_le
    · exact lt_of_lt_of_le hp_y (by exact_mod_cast hPStar)
  have hdisj : Set.PairwiseDisjoint (Finset.Icc 1 M : Set ℕ) Bm := by
    intro m₁ hm₁ m₂ hm₂ hne
    change Disjoint (Bm m₁) (Bm m₂)
    rw [Finset.disjoint_left]
    intro n hn₁ hn₂
    rcases Finset.mem_image.mp hn₁ with ⟨p₁, hp₁, rfl⟩
    rcases Finset.mem_image.mp hn₂ with ⟨p₂, hp₂, heq⟩
    rw [Finset.mem_coe, Finset.mem_Icc] at hm₁ hm₂
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp₁ hp₂
    -- Both p₁, p₂ > √x while m₁ * p₁ = m₂ * p₂ ≤ x, so p₁ = p₂ (otherwise p₁ * p₂ ∣ m₁ * p₁ gives p₁*p₂ > x!)
    have hp1_gt : Real.sqrt (x : ℝ) < (p₁ : ℝ) := by
      have hm1pos : (0 : ℝ) < m₁ := by exact_mod_cast (by omega : 0 < m₁)
      have h1 : α * ((x : ℝ) / (m₁ : ℝ)) < (p₁ : ℝ) := (Nat.floor_lt (by positivity)).mp hp₁.1.1
      have h2 : (m₁ : ℝ) * y ≤ α * (x : ℝ) :=
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hm₁.2) (by linarith [Real.sqrt_nonneg (x : ℝ)])).trans hMy
      have h3 : y < (p₁ : ℝ) := by
        have h1' := mul_lt_mul_of_pos_left h1 hm1pos
        rw [show (m₁ : ℝ) * (α * ((x : ℝ) / (m₁ : ℝ))) = α * (x : ℝ) by field_simp] at h1'
        nlinarith
      exact lt_trans hy_lo h3
    have hp2_gt : Real.sqrt (x : ℝ) < (p₂ : ℝ) := by
      have hm2pos : (0 : ℝ) < m₂ := by exact_mod_cast (by omega : 0 < m₂)
      have h1 : α * ((x : ℝ) / (m₂ : ℝ)) < (p₂ : ℝ) := (Nat.floor_lt (by positivity)).mp hp₂.1.1
      have h2 : (m₂ : ℝ) * y ≤ α * (x : ℝ) :=
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hm₂.2) (by linarith [Real.sqrt_nonneg (x : ℝ)])).trans hMy
      have h3 : y < (p₂ : ℝ) := by
        have h1' := mul_lt_mul_of_pos_left h1 hm2pos
        rw [show (m₂ : ℝ) * (α * ((x : ℝ) / (m₂ : ℝ))) = α * (x : ℝ) by field_simp] at h1'
        nlinarith
      exact lt_trans hy_lo h3
    have hp_eq : p₁ = p₂ := by
      by_contra hpne
      have hcop : Nat.Coprime p₁ p₂ := (Nat.coprime_primes hp₁.2 hp₂.2).mpr hpne
      have hd1 : p₁ ∣ m₁ * p₁ := dvd_mul_left p₁ m₁
      have hd2 : p₂ ∣ m₁ * p₁ := by rw [← heq]; exact dvd_mul_left p₂ m₂
      have hd12 : p₁ * p₂ ∣ m₁ * p₁ := hcop.mul_dvd_of_dvd_of_dvd hd1 hd2
      have hle_n : p₁ * p₂ ≤ m₁ * p₁ := Nat.le_of_dvd (Nat.mul_pos (by omega) hp₁.2.pos) hd12
      have hn_le_x : m₁ * p₁ ≤ x := by
        have hp_le : (p₁ : ℝ) ≤ (x : ℝ) / (m₁ : ℝ) :=
          le_trans (by exact_mod_cast hp₁.1.2) (Nat.floor_le (by positivity))
        have hm1pos : (0 : ℝ) < m₁ := by exact_mod_cast (by omega : 0 < m₁)
        have hprod := mul_le_mul_of_nonneg_left hp_le hm1pos.le
        rw [show (m₁ : ℝ) * ((x : ℝ) / (m₁ : ℝ)) = (x : ℝ) by field_simp] at hprod
        exact_mod_cast hprod
      have hgt_x : (x : ℝ) < (p₁ : ℝ) * (p₂ : ℝ) := by
        have hsq := Real.mul_self_sqrt hxpos.le
        nlinarith [Real.sqrt_nonneg (x : ℝ)]
      have hle_xR : (p₁ : ℝ) * (p₂ : ℝ) ≤ (x : ℝ) := by exact_mod_cast (hle_n.trans hn_le_x)
      linarith
    subst hp_eq
    have : m₁ = m₂ := Nat.eq_of_mul_eq_mul_right hp₁.2.pos heq.symm
    exact hne this
  have hBm_sum : ∀ m ∈ Finset.Icc 1 M,
      (1 : ℝ) / (m : ℝ) / (20 * Real.log (x : ℝ)) ≤ ∑ n ∈ Bm m, (1 : ℝ) / (n : ℝ) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hB : 1000000 ≤ (x : ℝ) / (m : ℝ) := by
      rw [le_div_iff₀ hmpos]
      have hmM : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hm.2
      nlinarith
    have hcard := prime_count_interval_ge hα0 hα hB
    have hBm_card : (Bm m).card = (Pm m).card :=
      Finset.card_image_of_injective _ (fun _ _ h => Nat.eq_of_mul_eq_mul_left (by omega : 0 < m) h)
    have hlog_le : Real.log ((x : ℝ) / (m : ℝ)) ≤ Real.log (x : ℝ) := by
      apply Real.log_le_log (by positivity)
      exact div_le_self hxpos.le (by exact_mod_cast hm.1)
    have hlog_pos : 0 < Real.log ((x : ℝ) / (m : ℝ)) := Real.log_pos (by linarith)
    calc (1 : ℝ) / (m : ℝ) / (20 * Real.log (x : ℝ))
        ≤ ((x : ℝ) / (m : ℝ)) / (20 * Real.log ((x : ℝ) / (m : ℝ))) / (x : ℝ) := by
          have hrw : ((x : ℝ) / (m : ℝ)) / (20 * Real.log ((x : ℝ) / (m : ℝ))) / (x : ℝ) =
              (1 : ℝ) / (m : ℝ) / (20 * Real.log ((x : ℝ) / (m : ℝ))) := by field_simp
          rw [hrw]
          apply div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
      _ ≤ ((Pm m).card : ℝ) / (x : ℝ) :=
          div_le_div_of_nonneg_right hcard hxpos.le
      _ = ((Bm m).card : ℝ) / (x : ℝ) := by rw [hBm_card]
      _ = ∑ _n ∈ Bm m, (1 : ℝ) / (x : ℝ) := by simp [div_eq_mul_inv]
      _ ≤ ∑ n ∈ Bm m, (1 : ℝ) / (n : ℝ) := by
          apply Finset.sum_le_sum
          intro n hn
          have hnT := hBm_sub m (Finset.mem_Icc.mpr hm) hn
          have hnI := Finset.mem_Icc.mp (Finset.mem_filter.mp hnT).1
          exact one_div_le_one_div_of_le (by exact_mod_cast (by
            have : 1 ≤ ⌈α * (x : ℝ)⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
              intro hz
              have h0 := Nat.ceil_eq_zero.mp hz
              linarith [mul_pos hα0 hxpos])
            omega : 0 < n)) (by exact_mod_cast hnI.2)
  have hharm : Real.log ((M : ℝ) + 1) ≤ ∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / (m : ℝ) := by
    have h1 := log_add_one_le_harmonic M
    have h2 : (harmonic M : ℝ) = ∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / (m : ℝ) := by
      simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      refine Finset.sum_bij (fun i _ => i + 1) ?_ ?_ ?_ ?_
      · intro i hi; rw [Finset.mem_range] at hi; rw [Finset.mem_Icc]; omega
      · intro i₁ _ i₂ _ h; omega
      · intro m hm; rw [Finset.mem_Icc] at hm
        exact ⟨m - 1, Finset.mem_range.mpr (by omega), by omega⟩
      · intro i _; simp [one_div]
    push_cast at h1
    linarith only [h1, h2]
  calc Real.log ((M : ℝ) + 1) / (20 * Real.log (x : ℝ))
      ≤ (∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / (m : ℝ)) / (20 * Real.log (x : ℝ)) :=
        div_le_div_of_nonneg_right hharm (by positivity)
    _ = ∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / (m : ℝ) / (20 * Real.log (x : ℝ)) := by
        rw [Finset.sum_div]
    _ ≤ ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Bm m, (1 : ℝ) / (n : ℝ) :=
        Finset.sum_le_sum hBm_sum
    _ = ∑ n ∈ (Finset.Icc 1 M).biUnion Bm, (1 : ℝ) / (n : ℝ) :=
        (Finset.sum_biUnion hdisj).symm
    _ ≤ ∑ n ∈ T, (1 : ℝ) / (n : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          rcases Finset.mem_biUnion.mp hn with ⟨m, hm, hnm⟩
          exact hBm_sub m hm hnm
        · intro _ _ _; positivity

end E292Part1



namespace E292Part2

open Finset Filter Real E292Part1
open scoped Pointwise Classical

/- ## Part 4: Cauchy-Davenport subset sum mod p and Croot's Fourier subset-sum lemma -/

/-- If `p` is prime and `M : Finset ℕ` has `p ≤ M.card` with every `m ∈ M` coprime to `p`,
then every residue `a : ZMod p` is the sum of `(m : ZMod p)⁻¹` over a subset `K ⊆ M` of size `≤ p`. -/
lemma cauchy_davenport_subset_sum {p : ℕ} (hp : p.Prime) {M : Finset ℕ}
    (hcop : ∀ m ∈ M, ¬ p ∣ m) (hcard : p ≤ M.card) (a : ZMod p) :
    ∃ K ⊆ M, K.card ≤ p ∧ ∑ m ∈ K, (m : ZMod p)⁻¹ = a := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  -- Pick a subset M₀ ⊆ M of cardinality exactly p
  obtain ⟨M₀, hM₀sub, hM₀card⟩ := Finset.exists_subset_card_eq hcard
  -- Prove by induction on any Finset S ⊆ M₀: the set of subset sums of S has cardinality ≥ min p (S.card + 1)
  let subSums (S : Finset ℕ) : Finset (ZMod p) :=
    S.powerset.image (fun (K : Finset ℕ) => ∑ m ∈ K, (m : ZMod p)⁻¹)
  have hsubSums_card : ∀ S : Finset ℕ, (∀ m ∈ S, ¬ p ∣ m) →
      min p (S.card + 1) ≤ (subSums S).card := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      have hne : (subSums ∅).Nonempty := ⟨0, Finset.mem_image.mpr ⟨∅, by simp, by simp⟩⟩
      have h1 : 1 ≤ (subSums ∅).card := Finset.card_pos.mpr hne
      exact le_trans (min_le_right _ _) h1
    | insert b S hb ih =>
      intro hS
      have hS' : ∀ m ∈ S, ¬ p ∣ m := fun m hm => hS m (Finset.mem_insert_of_mem hm)
      have hb_ndvd : ¬ p ∣ b := hS b (Finset.mem_insert_self b S)
      have hb_ne0 : ((b : ZMod p)⁻¹) ≠ 0 := by
        have hb0 : (b : ZMod p) ≠ 0 := by
          intro h
          exact hb_ndvd ((ZMod.natCast_eq_zero_iff b p).mp h)
        exact inv_ne_zero hb0
      have htwo : ({0, (b : ZMod p)⁻¹} : Finset (ZMod p)).card = 2 := by
        rw [Finset.card_pair hb_ne0.symm]
      have hadd_sub : subSums S + ({0, (b : ZMod p)⁻¹} : Finset (ZMod p)) ⊆ subSums (insert b S) := by
        intro z hz
        rcases Finset.mem_add.mp hz with ⟨x, hx, y, hy, rfl⟩
        rcases Finset.mem_image.mp hx with ⟨K, hK, rfl⟩
        have hKS : K ⊆ S := Finset.mem_powerset.mp hK
        rcases Finset.mem_insert.mp hy with rfl | hy2
        · refine Finset.mem_image.mpr ⟨K, Finset.mem_powerset.mpr (hKS.trans (Finset.subset_insert b S)), ?_⟩
          simp
        · have hy2' : y = (b : ZMod p)⁻¹ := Finset.mem_singleton.mp hy2
          subst hy2'
          refine Finset.mem_image.mpr ⟨insert b K, Finset.mem_powerset.mpr (Finset.insert_subset_insert b hKS), ?_⟩
          rw [Finset.sum_insert (fun h => hb (hKS h)), add_comm]
      have hneS : (subSums S).Nonempty := ⟨0, Finset.mem_image.mpr ⟨∅, by simp, by simp⟩⟩
      have hneT : ({0, (b : ZMod p)⁻¹} : Finset (ZMod p)).Nonempty := ⟨0, by simp⟩
      have hcd := ZMod.cauchy_davenport hp hneS hneT
      rw [htwo] at hcd
      have hih := ih hS'
      have hle := hcd.trans (Finset.card_le_card hadd_sub)
      rw [Finset.card_insert_of_notMem hb]
      omega
  have hfull : (subSums M₀).card = p := by
    apply le_antisymm
    · calc (subSums M₀).card ≤ (Finset.univ : Finset (ZMod p)).card :=
            Finset.card_le_card (Finset.subset_univ _)
        _ = p := by simp [ZMod.card]
    · have h1 := hsubSums_card M₀ (fun m hm => hcop m (hM₀sub hm))
      rw [hM₀card] at h1
      omega
  have huniv : subSums M₀ = Finset.univ :=
    Finset.eq_univ_of_card _ (by simpa [ZMod.card] using hfull)
  have ha : a ∈ subSums M₀ := by rw [huniv]; exact Finset.mem_univ a
  rcases Finset.mem_image.mp ha with ⟨K, hK, hsum⟩
  have hKM₀ : K ⊆ M₀ := Finset.mem_powerset.mp hK
  exact ⟨K, hKM₀.trans hM₀sub, (Finset.card_le_card hKM₀).trans hM₀card.le, hsum⟩

/-- Trivial bound on the number of distinct prime factors: `2 ^ n.primeFactors.card ≤ n` for `n ≥ 1`. -/
lemma two_pow_primeFactors_card_le {n : ℕ} (hn : 0 < n) : 2 ^ n.primeFactors.card ≤ n := by
  have h1 : ∏ p ∈ n.primeFactors, p ∣ n := Nat.prod_primeFactors_dvd n
  have h2 : ∏ p ∈ n.primeFactors, p ≤ n := Nat.le_of_dvd hn h1
  have h3 : 2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p := by
    calc 2 ^ n.primeFactors.card = ∏ _p ∈ n.primeFactors, 2 := by simp
      _ ≤ ∏ p ∈ n.primeFactors, p :=
          Finset.prod_le_prod (fun _ _ => by omega) (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  exact h3.trans h2

/-- Number of divisors of a positive integer `N` that are products of 2 distinct primes is at most
`n.primeFactors.card ^ 2`, which is at most `(2 * Real.log N) ^ 2`. -/
lemma card_semiprime_divisors_le {N : ℕ} (hN : 0 < N) (M : Finset ℕ)
    (hM : ∀ m ∈ M, ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₁ < p₂ ∧ m = p₁ * p₂) :
    ((M.filter (fun m => m ∣ N)).card : ℝ) ≤ (2 * Real.log (N : ℝ)) ^ 2 := by
  classical
  have hsub : M.filter (fun m => m ∣ N) ⊆
      (N.primeFactors ×ˢ N.primeFactors).image (fun z => z.1 * z.2) := by
    intro m hm
    rw [Finset.mem_filter] at hm
    obtain ⟨p₁, p₂, hp₁, hp₂, _, rfl⟩ := hM m hm.1
    rw [Finset.mem_image]
    refine ⟨(p₁, p₂), Finset.mem_product.mpr ⟨?_, ?_⟩, rfl⟩
    · exact Nat.mem_primeFactors.mpr ⟨hp₁, dvd_trans (dvd_mul_right p₁ p₂) hm.2, hN.ne'⟩
    · exact Nat.mem_primeFactors.mpr ⟨hp₂, dvd_trans (dvd_mul_left p₂ p₁) hm.2, hN.ne'⟩
  have hcard : (M.filter (fun m => m ∣ N)).card ≤ N.primeFactors.card ^ 2 := by
    calc (M.filter (fun m => m ∣ N)).card
        ≤ ((N.primeFactors ×ˢ N.primeFactors).image (fun z => z.1 * z.2)).card :=
          Finset.card_le_card hsub
      _ ≤ (N.primeFactors ×ˢ N.primeFactors).card := Finset.card_image_le
      _ = N.primeFactors.card ^ 2 := by rw [Finset.card_product, sq]
  have hlog : (N.primeFactors.card : ℝ) ≤ 2 * Real.log (N : ℝ) := by
    have hpow : ((2 : ℝ) ^ N.primeFactors.card) ≤ (N : ℝ) := by
      exact_mod_cast two_pow_primeFactors_card_le hN
    have h1 := Real.log_le_log (by positivity) hpow
    rw [Real.log_pow] at h1
    have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    nlinarith [Nat.cast_nonneg (α := ℝ) N.primeFactors.card]
  have hcardR : ((M.filter (fun m => m ∣ N)).card : ℝ) ≤ (N.primeFactors.card : ℝ) ^ 2 := by
    exact_mod_cast hcard
  exact hcardR.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hlog 2)

/-- Distance from a real number to the nearest integer, bounded below on `r / p` for `|r| ≤ p / 2`. -/
lemma norm_one_add_exp_sq_le {θ : ℝ} {d : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 1 / 2)
    (hdist : ∀ k : ℤ, d ≤ |θ - (k : ℝ)|) :
    ‖(1 : ℂ) + Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ))‖ ^ 2 ≤ 4 * (1 - 4 * d ^ 2) := by
  -- Use |1 + e^(2πiθ)|^2 = 2 + 2 cos(2πθ) = 4 cos^2(πθ)
  -- Shift θ by integer k₀ = round θ so t = θ - k₀ ∈ [-1/2, 1/2] with |t| ≥ d.
  -- Since cos(2πt) = cos(2π|t|) and on [0, 1/2], 1 + cos(2πu) ≤ 2 - 8 u^2 (equivalently cos(πu)^2 ≤ 1 - 4 u^2,
  -- i.e. sin(πu) ≥ 2 u on [0, 1/2], Jordan's inequality!).
  set k₀ : ℤ := round θ
  set t : ℝ := θ - (k₀ : ℝ)
  have ht_abs : |t| ≤ 1 / 2 := abs_sub_round θ
  have ht_ge : d ≤ |t| := hdist k₀
  have hcos_eq : Real.cos (2 * Real.pi * θ) = Real.cos (2 * Real.pi * |t|) := by
    have h1 : 2 * Real.pi * θ = 2 * Real.pi * t + (k₀ : ℝ) * (2 * Real.pi) := by
      dsimp [t]; ring
    rw [h1, Real.cos_add_int_mul_two_pi]
    rcases le_or_gt 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_neg ht, mul_neg, Real.cos_neg]
  have hnorm_sq : ‖(1 : ℂ) + Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ))‖ ^ 2 =
      2 + 2 * Real.cos (2 * Real.pi * θ) := by
    have hexp : Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ)) =
        Complex.exp (((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I) := by
      congr 1; push_cast; ring
    rw [hexp, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.one_re, Complex.exp_ofReal_mul_I_re,
      Complex.add_im, Complex.one_im, Complex.exp_ofReal_mul_I_im, zero_add]
    have hsc := Real.sin_sq_add_cos_sq (2 * Real.pi * θ)
    nlinarith
  rw [hnorm_sq, hcos_eq]
  -- Now 2 + 2 cos(2π|t|) = 4 - 4 sin^2(π|t|), and Jordan's inequality gives 2|t| ≤ sin(π|t|) for 0 ≤ |t| ≤ 1/2!
  have hdouble : 2 + 2 * Real.cos (2 * Real.pi * |t|) = 4 * (1 - Real.sin (Real.pi * |t|) ^ 2) := by
    have h1 : 2 * Real.pi * |t| = 2 * (Real.pi * |t|) := by ring
    rw [h1, Real.cos_two_mul]
    have hsc := Real.sin_sq_add_cos_sq (Real.pi * |t|)
    nlinarith
  rw [hdouble]
  -- Jordan's inequality via Mathlib's `Real.mul_le_sin`: (2/π)*(π*|t|) ≤ sin(π*|t|)
  have hjordan : 2 * |t| ≤ Real.sin (Real.pi * |t|) := by
    have hu0 : 0 ≤ Real.pi * |t| := by positivity
    have hu1 : Real.pi * |t| ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
    have h := Real.mul_le_sin hu0 hu1
    have hrw : 2 / Real.pi * (Real.pi * |t|) = 2 * |t| := by
      field_simp [Real.pi_ne_zero]
    linarith
  have hsq : 4 * d ^ 2 ≤ Real.sin (Real.pi * |t|) ^ 2 := by
    have h1 : 2 * d ≤ Real.sin (Real.pi * |t|) := by linarith
    nlinarith
  nlinarith

/-- Croot's `halfbiglem` for `k = 2`: for prime `p ≥ 100`, `0 < h < p`, and a set `M` of
`C` integers `< B` each of the form `p₁ * p₂` (`p₁ < p₂` primes not dividing `p`), with
`256 * (Real.log p)^2 < C < p`, at least `C / 2` elements `m ∈ M` have
`∀ k : ℤ, C / (256 * B * (Real.log p)^2) ≤ |((h * (m : ZMod p)⁻¹).val : ℝ) / p - k|`. -/
lemma halfbiglem_k2 {p h : ℕ} {B : ℝ} {M : Finset ℕ}
    (hp : p.Prime) (hp100 : 100 ≤ p) (hh0 : 0 < h) (hhp : h < p)
    (hBpos : 0 < B)
    (hM_semiprime : ∀ m ∈ M, ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₁ < p₂ ∧ m = p₁ * p₂)
    (hM_cop : ∀ m ∈ M, ¬ p ∣ m)
    (hM_lt : ∀ m ∈ M, (m : ℝ) < B)
    (hC_lo : 256 * (Real.log (p : ℝ)) ^ 2 < (M.card : ℝ))
    (hC_hi : M.card < p) :
    let d : ℝ := (M.card : ℝ) / (256 * B * (Real.log (p : ℝ)) ^ 2)
    (M.card : ℝ) / 2 ≤
      ((M.filter (fun (m : ℕ) =>
          ∀ k : ℤ, d ≤ |(((h * (m : ZMod p)⁻¹).val : ℕ) : ℝ) / (p : ℝ) - (k : ℝ)|)).card : ℝ) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hpR : (100 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp100
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hlogp_ge : (1 : ℝ) < Real.log (p : ℝ) := by
    have h1 : Real.log (4 : ℝ) < Real.log (p : ℝ) := Real.log_lt_log (by norm_num) (by linarith)
    have h2 : (1 : ℝ) < Real.log 4 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]
      push_cast; linarith [Real.log_two_gt_d9]
    linarith
  set C : ℝ := (M.card : ℝ)
  set T : ℝ := C / (128 * (Real.log (p : ℝ)) ^ 2)
  have hT_gt2 : 2 < T := by
    dsimp [T]
    rw [lt_div_iff₀ (by positivity)]
    linarith
  -- Centered representative r_m ∈ (-p/2, p/2] of h * m⁻¹ mod p
  let rZ (m : ℕ) : ℤ :=
    let v : ℕ := (h * (m : ZMod p)⁻¹).val
    if 2 * v ≤ p then (v : ℤ) else (v : ℤ) - (p : ℤ)
  have hrZ_ne0 : ∀ m ∈ M, rZ m ≠ 0 := by
    intro m hm
    dsimp [rZ]
    have hm0 : (m : ZMod p) ≠ 0 := fun hz => hM_cop m hm ((ZMod.natCast_eq_zero_iff m p).mp hz)
    have hh0' : (h : ZMod p) ≠ 0 := fun hz => by
      have := (ZMod.natCast_eq_zero_iff h p).mp hz
      have := Nat.le_of_dvd hh0 this
      omega
    have hprod : (h : ZMod p) * (m : ZMod p)⁻¹ ≠ 0 := mul_ne_zero hh0' (inv_ne_zero hm0)
    have hv_pos : 0 < ((h : ZMod p) * (m : ZMod p)⁻¹).val := by
      by_contra hv0
      have hvz : ((h : ZMod p) * (m : ZMod p)⁻¹).val = 0 := by omega
      apply hprod
      rw [← ZMod.natCast_zmod_val ((h : ZMod p) * (m : ZMod p)⁻¹), hvz]
      simp
    have hv_lt : ((h : ZMod p) * (m : ZMod p)⁻¹).val < p := ZMod.val_lt _
    split_ifs <;> omega
  have hrZ_dvd : ∀ m ∈ M, ((p : ℤ) ∣ (m : ℤ) * rZ m - (h : ℤ)) := by
    intro m hm
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    have hr_cast : (rZ m : ZMod p) = (h : ZMod p) * (m : ZMod p)⁻¹ := by
      dsimp [rZ]
      split_ifs <;> simp
    rw [hr_cast]
    have hm0 : (m : ZMod p) ≠ 0 := fun hz => hM_cop m hm ((ZMod.natCast_eq_zero_iff m p).mp hz)
    rw [← mul_assoc, mul_comm (m : ZMod p) (h : ZMod p), mul_assoc, mul_inv_cancel₀ hm0, mul_one, sub_self]
  let sZ (m : ℕ) : ℤ := ((m : ℤ) * rZ m - (h : ℤ)) / (p : ℤ)
  have hsZ_eq : ∀ m ∈ M, (p : ℤ) * sZ m + (h : ℤ) = (m : ℤ) * rZ m := by
    intro m hm
    dsimp [sZ]
    have hd := hrZ_dvd m hm
    have h1 := Int.mul_ediv_cancel' hd
    omega
  -- Split M into Bad = {m ∈ M : |(sZ m : ℝ)| < T} and Good = M \ Bad.
  set Bad := M.filter (fun m => |(sZ m : ℝ)| < T)
  have hBad_le : (Bad.card : ℝ) ≤ C / 2 := by
    by_contra hgt
    push Not at hgt
    set K := (⌊T⌋₊ : ℤ)
    have hK_le : (K : ℝ) ≤ T := by exact_mod_cast Nat.floor_le (by linarith)
    have hBad_img : ∀ m ∈ Bad, sZ m ∈ Finset.Icc (-K) K := by
      intro m hm
      have hlt : |(sZ m : ℝ)| < T := (Finset.mem_filter.mp hm).2
      rw [abs_lt] at hlt
      rw [Finset.mem_Icc]
      have hleK : sZ m ≤ K := by
        by_contra hc
        push Not at hc
        have h1 : (K : ℝ) + 1 ≤ (sZ m : ℝ) := by exact_mod_cast hc
        have h2 : T < (K : ℝ) + 1 := by exact_mod_cast Nat.lt_floor_add_one T
        linarith
      have hgeK : -K ≤ sZ m := by
        by_contra hc
        push Not at hc
        have h1 : (sZ m : ℝ) ≤ -(K : ℝ) - 1 := by exact_mod_cast (show sZ m ≤ -K - 1 by omega)
        have h2 : T < (K : ℝ) + 1 := by exact_mod_cast Nat.lt_floor_add_one T
        linarith
      exact ⟨hgeK, hleK⟩
    have hIcc_card : (Finset.Icc (-K) K).card = 2 * ⌊T⌋₊ + 1 := by
      rw [Int.card_Icc]
      dsimp [K]
      omega
    have hsum_fib : Bad.card = ∑ s ∈ Finset.Icc (-K) K, (Bad.filter (fun m => sZ m = s)).card := by
      rw [← Finset.card_biUnion]
      · congr 1; ext m
        simp only [Finset.mem_biUnion, Finset.mem_filter]
        exact ⟨fun hm => ⟨sZ m, hBad_img m hm, hm, rfl⟩, fun ⟨_, _, hm, _⟩ => hm⟩
      · intro s₁ _ s₂ _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro m h1 h2
        exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    have hex_s : ∃ s ∈ Finset.Icc (-K) K,
        (Bad.card : ℝ) ≤ ((2 * ⌊T⌋₊ + 1 : ℕ) : ℝ) * ((Bad.filter (fun m => sZ m = s)).card : ℝ) := by
      by_contra hall
      push Not at hall
      have hne : (Finset.Icc (-K) K).Nonempty := ⟨0, Finset.mem_Icc.mpr ⟨by dsimp [K]; omega, by dsimp [K]; omega⟩⟩
      have hlt_sum : ∑ s ∈ Finset.Icc (-K) K,
          ((2 * ⌊T⌋₊ + 1 : ℕ) : ℝ) * ((Bad.filter (fun m => sZ m = s)).card : ℝ) <
          ∑ _s ∈ Finset.Icc (-K) K, (Bad.card : ℝ) :=
        Finset.sum_lt_sum_of_nonempty hne hall
      rw [← Finset.mul_sum, Finset.sum_const, hIcc_card, nsmul_eq_mul] at hlt_sum
      have hsumR : (Bad.card : ℝ) = ∑ s ∈ Finset.Icc (-K) K, ((Bad.filter (fun m => sZ m = s)).card : ℝ) := by
        exact_mod_cast hsum_fib
      rw [← hsumR] at hlt_sum
      linarith
    obtain ⟨s, hsI, hfib⟩ := hex_s
    set Nz : ℤ := (p : ℤ) * s + (h : ℤ)
    have hNz_ne0 : Nz ≠ 0 := by
      intro hz
      have hd : (p : ℤ) ∣ (h : ℤ) := ⟨-s, by linarith⟩
      have hdn : p ∣ h := Int.ofNat_dvd.mp hd
      have := Nat.le_of_dvd hh0 hdn
      omega
    set N : ℕ := Nz.natAbs
    have hN_pos : 0 < N := Int.natAbs_pos.mpr hNz_ne0
    have hN_lt : (N : ℝ) < (p : ℝ) ^ 2 := by
      have hs_abs : |(s : ℝ)| ≤ T := by
        rw [Finset.mem_Icc] at hsI
        rw [abs_le]
        have h1 : -(K : ℝ) ≤ (s : ℝ) := by exact_mod_cast hsI.1
        have h2 : (s : ℝ) ≤ (K : ℝ) := by exact_mod_cast hsI.2
        constructor <;> linarith
      have hNR : (N : ℝ) = |(Nz : ℝ)| := by
        dsimp [N]
        rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      rw [hNR]
      have hNzR : (Nz : ℝ) = (p : ℝ) * (s : ℝ) + (h : ℝ) := by dsimp [Nz]; push_cast; ring
      rw [hNzR]
      have h1 : |(p : ℝ) * (s : ℝ) + (h : ℝ)| ≤ (p : ℝ) * |(s : ℝ)| + (h : ℝ) := by
        calc |(p : ℝ) * (s : ℝ) + (h : ℝ)| ≤ |(p : ℝ) * (s : ℝ)| + |(h : ℝ)| := abs_add_le _ _
          _ = (p : ℝ) * |(s : ℝ)| + (h : ℝ) := by
              rw [abs_mul, abs_of_pos hppos, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) h)]
      have hT_le : T ≤ (p : ℝ) / 2 := by
        have hCp : C < (p : ℝ) := by dsimp [C]; exact_mod_cast hC_hi
        dsimp [T]
        rw [div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg (Real.log (p : ℝ) - 1)]
      have hh_lt : (h : ℝ) < (p : ℝ) := by exact_mod_cast hhp
      nlinarith
    have hfib_sub : Bad.filter (fun m => sZ m = s) ⊆ M.filter (fun m => m ∣ N) := by
      intro m hm
      rw [Finset.mem_filter] at hm
      have hmM : m ∈ M := (Finset.mem_filter.mp hm.1).1
      refine Finset.mem_filter.mpr ⟨hmM, ?_⟩
      have heq := hsZ_eq m hmM
      rw [hm.2] at heq
      have hdz : (m : ℤ) ∣ Nz := ⟨rZ m, by dsimp [Nz]; linarith⟩
      exact Int.natCast_dvd.mp hdz
    have hfib_ub : ((Bad.filter (fun m => sZ m = s)).card : ℝ) ≤ 16 * (Real.log (p : ℝ)) ^ 2 := by
      have h1 : ((Bad.filter (fun m => sZ m = s)).card : ℝ) ≤ ((M.filter (fun m => m ∣ N)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hfib_sub
      have h2 := card_semiprime_divisors_le hN_pos M hM_semiprime
      have hlogN : Real.log (N : ℝ) ≤ 2 * Real.log (p : ℝ) := by
        have := Real.log_le_log (by exact_mod_cast hN_pos) hN_lt.le
        rw [Real.log_pow] at this
        simpa using this
      have h3 : (2 * Real.log (N : ℝ)) ^ 2 ≤ (4 * Real.log (p : ℝ)) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity)
        linarith
      linarith
    have h2K1 : ((2 * ⌊T⌋₊ + 1 : ℕ) : ℝ) ≤ 3 * T := by
      push_cast
      have hfl : (⌊T⌋₊ : ℝ) ≤ T := Nat.floor_le (by linarith)
      linarith
    have hprod_ub : ((2 * ⌊T⌋₊ + 1 : ℕ) : ℝ) * ((Bad.filter (fun m => sZ m = s)).card : ℝ) ≤
        3 * T * (16 * (Real.log (p : ℝ)) ^ 2) :=
      mul_le_mul h2K1 hfib_ub (Nat.cast_nonneg _) (by positivity)
    have h3T : 3 * T * (16 * (Real.log (p : ℝ)) ^ 2) = (48 / 128 : ℝ) * C := by
      dsimp [T]
      have hl0 : (Real.log (p : ℝ)) ^ 2 ≠ 0 := by positivity
      field_simp [hl0]
      ring
    linarith
  -- Every m ∈ M \ Bad has |(sZ m : ℝ)| ≥ T, which forces distance ≥ d!
  dsimp only
  set d : ℝ := C / (256 * B * (Real.log (p : ℝ)) ^ 2)
  have hsub_good : M \ Bad ⊆ M.filter (fun (m : ℕ) =>
      ∀ k : ℤ, d ≤ |(((h * (m : ZMod p)⁻¹).val : ℕ) : ℝ) / (p : ℝ) - (k : ℝ)|) := by
    intro m hm
    rw [Finset.mem_sdiff] at hm
    have hmM : m ∈ M := hm.1
    have hgeT : T ≤ |(sZ m : ℝ)| := by
      by_contra hlt
      push Not at hlt
      exact hm.2 (Finset.mem_filter.mpr ⟨hmM, hlt⟩)
    refine Finset.mem_filter.mpr ⟨hmM, fun k => ?_⟩
    -- First show |(rZ m : ℝ)| / p ≥ d
    have hm_pos : (0 : ℝ) < (m : ℝ) := by
      obtain ⟨p₁, p₂, hp₁, hp₂, _, rfl⟩ := hM_semiprime m hmM
      exact_mod_cast Nat.mul_pos hp₁.pos hp₂.pos
    have hm_ltB : (m : ℝ) < B := hM_lt m hmM
    have hmr_ge : (p : ℝ) * (T - 1) ≤ (m : ℝ) * |(rZ m : ℝ)| := by
      have heq : (m : ℝ) * (rZ m : ℝ) = (p : ℝ) * (sZ m : ℝ) + (h : ℝ) := by
        exact_mod_cast (hsZ_eq m hmM).symm
      have habs : (p : ℝ) * |(sZ m : ℝ)| - (h : ℝ) ≤ (m : ℝ) * |(rZ m : ℝ)| := by
        have h1 : |(p : ℝ) * (sZ m : ℝ)| - |(h : ℝ)| ≤ |(p : ℝ) * (sZ m : ℝ) + (h : ℝ)| := by
          have := abs_sub_abs_le_abs_sub ((p : ℝ) * (sZ m : ℝ)) (-(h : ℝ))
          simpa [sub_neg_eq_add, abs_neg] using this
        have h2 : |(p : ℝ) * (sZ m : ℝ)| = (p : ℝ) * |(sZ m : ℝ)| := by
          rw [abs_mul, abs_of_pos hppos]
        have h3 : |(h : ℝ)| = (h : ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
        have h4 : |(m : ℝ) * (rZ m : ℝ)| = (m : ℝ) * |(rZ m : ℝ)| := by
          rw [abs_mul, abs_of_pos hm_pos]
        rw [h2, h3, ← heq, h4] at h1
        exact h1
      have hh_lt : (h : ℝ) < (p : ℝ) := by exact_mod_cast hhp
      nlinarith
    have hr_div_ge : d ≤ |(rZ m : ℝ)| / (p : ℝ) := by
      have hT2 : T / 2 ≤ T - 1 := by linarith
      have h1 : (p : ℝ) * (T / 2) ≤ B * |(rZ m : ℝ)| := by
        have : (m : ℝ) * |(rZ m : ℝ)| ≤ B * |(rZ m : ℝ)| :=
          mul_le_mul_of_nonneg_right hm_ltB.le (abs_nonneg _)
        nlinarith
      have h2 : T / (2 * B) ≤ |(rZ m : ℝ)| / (p : ℝ) := by
        rw [div_le_div_iff₀ (by positivity) hppos]
        linarith
      have hd_eq : d = T / (2 * B) := by
        dsimp [d, T]
        field_simp
        ring
      rwa [hd_eq]
    -- Relate ((h * m⁻¹).val : ℝ) / p - k to (rZ m : ℝ) / p
    set v : ℕ := (h * (m : ZMod p)⁻¹).val
    have hv_lt : v < p := ZMod.val_lt _
    have hr_abs_le : |(rZ m : ℝ)| ≤ (p : ℝ) / 2 := by
      dsimp [rZ]
      split_ifs with h2v
      · rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg v)]
        have : (2 : ℝ) * (v : ℝ) ≤ (p : ℝ) := by exact_mod_cast h2v
        linarith
      · have hgt2 : (p : ℝ) < 2 * (v : ℝ) := by
          push Not at h2v; exact_mod_cast h2v
        have hvle : (v : ℝ) < (p : ℝ) := by exact_mod_cast hv_lt
        rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, abs_of_neg (by linarith)]
        linarith
    have hdiff_int : ∃ j : ℤ, ((v : ℝ) / (p : ℝ) - (k : ℝ)) = (rZ m : ℝ) / (p : ℝ) - (j : ℝ) := by
      dsimp [rZ]
      split_ifs
      · exact ⟨k, by simp [v]⟩
      · refine ⟨k - 1, ?_⟩
        dsimp [v]
        push_cast
        field_simp [hppos.ne']
        ring
    obtain ⟨j, hj⟩ := hdiff_int
    rw [hj]
    rcases eq_or_ne j 0 with rfl | hjne
    · rw [Int.cast_zero, sub_zero, abs_div, abs_of_pos hppos]
      exact hr_div_ge
    · have hj1 : (1 : ℝ) ≤ |(j : ℝ)| := by
        have hna : 1 ≤ j.natAbs := Int.natAbs_pos.mpr hjne
        have h1 : (1 : ℝ) ≤ (j.natAbs : ℝ) := by exact_mod_cast hna
        have h2 : (j.natAbs : ℝ) = |(j : ℝ)| := by
          rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
        linarith
      have htri : |(j : ℝ)| - |(rZ m : ℝ) / (p : ℝ)| ≤ |(rZ m : ℝ) / (p : ℝ) - (j : ℝ)| := by
        have := abs_sub_abs_le_abs_sub (j : ℝ) ((rZ m : ℝ) / (p : ℝ))
        simpa [abs_sub_comm] using this
      have hhalf : |(rZ m : ℝ) / (p : ℝ)| ≤ 1 / 2 := by
        rw [abs_div, abs_of_pos hppos, div_le_iff₀ hppos]
        linarith
      have hd_le_half : d ≤ 1 / 2 := by
        rw [abs_div, abs_of_pos hppos] at hhalf
        linarith [hr_div_ge, hhalf]
      linarith
  have hcard_sdiff : (M \ Bad).card + Bad.card = M.card :=
    Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ M)
  have hcard_sdiffR : ((M \ Bad).card : ℝ) + (Bad.card : ℝ) = C := by
    dsimp [C]; exact_mod_cast hcard_sdiff
  have hge_sdiff : C / 2 ≤ ((M \ Bad).card : ℝ) := by linarith
  have hcard_mono : ((M \ Bad).card : ℝ) ≤
      ((M.filter (fun (m : ℕ) =>
        ∀ k : ℤ, d ≤ |(((h * (m : ZMod p)⁻¹).val : ℕ) : ℝ) / (p : ℝ) - (k : ℝ)|)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub_good
  exact hge_sdiff.trans hcard_mono

/-- Finite Fourier orthogonality on `ZMod p`. -/
lemma sum_exp_zmod {p : ℕ} (hp : 0 < p) (z : ZMod p) :
    ∑ h ∈ Finset.range p,
      Complex.exp (2 * Real.pi * Complex.I * ((h * z.val : ℕ) : ℂ) / (p : ℂ)) =
    if z = 0 then (p : ℂ) else 0 := by
  have : NeZero p := ⟨hp.ne'⟩
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I * (z.val : ℂ) / (p : ℂ))
  have hterm : ∀ h : ℕ,
      Complex.exp (2 * Real.pi * Complex.I * ((h * z.val : ℕ) : ℂ) / (p : ℂ)) = ζ ^ h := by
    intro h
    dsimp [ζ]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [hterm]
  split_ifs with hz
  · subst hz
    have hζ1 : ζ = 1 := by simp [ζ]
    simp [hζ1]
  · have hz_pos : 0 < z.val := by
      by_contra h0
      have hv0 : z.val = 0 := by omega
      apply hz
      rw [← ZMod.natCast_zmod_val z, hv0]; simp
    have hz_lt : z.val < p := ZMod.val_lt z
    have hζ_ne1 : ζ ≠ 1 := by
      intro h1
      rw [Complex.exp_eq_one_iff] at h1
      obtain ⟨n, hn⟩ := h1
      have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have hmul : (2 * Real.pi * Complex.I : ℂ) * ((z.val : ℂ) / (p : ℂ)) =
          (2 * Real.pi * Complex.I : ℂ) * (n : ℂ) := by
        calc (2 * Real.pi * Complex.I : ℂ) * ((z.val : ℂ) / (p : ℂ))
            = 2 * Real.pi * Complex.I * (z.val : ℂ) / (p : ℂ) := by ring
          _ = (n : ℂ) * (2 * Real.pi * Complex.I) := hn
          _ = (2 * Real.pi * Complex.I : ℂ) * (n : ℂ) := by ring
      have heq : (z.val : ℂ) / (p : ℂ) = (n : ℂ) := mul_left_cancel₀ h2pi hmul
      have heq2 : (z.val : ℂ) = (n : ℂ) * (p : ℂ) := (div_eq_iff hpC).mp heq
      have hre := congrArg Complex.re heq2
      simp only [Complex.natCast_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
        Complex.natCast_im, mul_zero, sub_zero] at hre
      have hzZ : (z.val : ℤ) = n * (p : ℤ) := by exact_mod_cast hre
      have hdvd : p ∣ z.val := Int.ofNat_dvd.mp ⟨n, by linarith⟩
      have := Nat.le_of_dvd hz_pos hdvd
      omega
    have hζ_pow : ζ ^ p = 1 := by
      dsimp [ζ]
      rw [← Complex.exp_nat_mul]
      have heq : (p : ℂ) * (2 * Real.pi * Complex.I * (z.val : ℂ) / (p : ℂ)) =
          (z.val : ℂ) * (2 * Real.pi * Complex.I) := by
        field_simp [hpC]
      rw [heq]
      exact Complex.exp_nat_mul_two_pi_mul_I z.val
    have hgeom := geom_sum_mul ζ p
    rw [hζ_pow, sub_self] at hgeom
    exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hζ_ne1)

/-- Croot's Fourier subset-sum lemma for `k = 2`: if `p` is prime, `B ≥ 8`, `M` is a set of
semiprimes `p₁ * p₂ < B` coprime to `p` with `100 ≤ M.card` and `M.card > 100 * B^(2/3) * (log p)^2`,
then every `a : ZMod p` is `∑ m ∈ K, (m : ZMod p)⁻¹` for some `K ⊆ M`. -/
lemma crootlem_k2 {p : ℕ} {B : ℝ} {M : Finset ℕ}
    (hp : p.Prime) (hM100 : 100 ≤ M.card) (hB8 : 8 ≤ B)
    (hM_semiprime : ∀ m ∈ M, ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₁ < p₂ ∧ m = p₁ * p₂)
    (hM_cop : ∀ m ∈ M, ¬ p ∣ m)
    (hM_lt : ∀ m ∈ M, (m : ℝ) < B)
    (hC_lo : 100 * B ^ ((2 : ℝ) / 3) * (Real.log (p : ℝ)) ^ 2 < (M.card : ℝ))
    (a : ZMod p) :
    ∃ K ⊆ M, ∑ m ∈ K, (m : ZMod p)⁻¹ = a := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  -- Case 1: p ≤ M.card → Cauchy-Davenport!
  by_cases hCp : p ≤ M.card
  · obtain ⟨K, hKM, _, hsum⟩ := cauchy_davenport_subset_sum hp hM_cop hCp a
    exact ⟨K, hKM, hsum⟩
  push Not at hCp
  have hp100 : 100 ≤ p := by omega
  -- Case 2: M.card < p → Fourier transform mod p!
  have hpR : (100 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp100
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hBpos : 0 < B := by linarith
  have hlogp_ge : (1 : ℝ) < Real.log (p : ℝ) := by
    have h1 : Real.log (4 : ℝ) < Real.log (p : ℝ) := Real.log_lt_log (by norm_num) (by linarith)
    have h2 : (1 : ℝ) < Real.log 4 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]
      push_cast; linarith [Real.log_two_gt_d9]
    linarith
  set C : ℝ := (M.card : ℝ)
  have hC_gt256 : 256 * (Real.log (p : ℝ)) ^ 2 < C := by
    have hB23 : (4 : ℝ) ≤ B ^ ((2 : ℝ) / 3) := by
      have h1 : ((8 : ℝ) ^ ((2 : ℝ) / 3)) ≤ B ^ ((2 : ℝ) / 3) :=
        Real.rpow_le_rpow (by positivity) hB8 (by positivity)
      have h2 : (8 : ℝ) ^ ((2 : ℝ) / 3) = 4 := by
        rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by positivity)]
        norm_num
      linarith
    have hlogp_pos : 0 < Real.log (p : ℝ) := by linarith
    nlinarith [sq_pos_of_pos hlogp_pos]
  -- Define character e_p(z) = exp(2πi * z.val / p)
  let ep (z : ZMod p) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (z.val : ℂ) / (p : ℂ))
  have hep_add : ∀ x y : ZMod p, ep (x + y) = ep x * ep y := by
    intro x y
    dsimp [ep]
    rw [← Complex.exp_add]
    have hmod : ((x + y).val : ℤ) ≡ (x.val : ℤ) + (y.val : ℤ) [ZMOD (p : ℤ)] := by
      rw [← ZMod.intCast_eq_intCast_iff]
      simp
    obtain ⟨q, hq⟩ := Int.modEq_iff_dvd.mp hmod.symm
    have heq : (2 * Real.pi * Complex.I * ((x + y).val : ℂ) / (p : ℂ)) =
        (2 * Real.pi * Complex.I * (x.val : ℂ) / (p : ℂ) +
         2 * Real.pi * Complex.I * (y.val : ℂ) / (p : ℂ)) + (q : ℂ) * (2 * Real.pi * Complex.I) := by
      have hqC : (((x + y).val : ℂ) - ((x.val : ℂ) + (y.val : ℂ))) = (p : ℂ) * (q : ℂ) := by
        exact_mod_cast hq
      have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
      apply mul_right_cancel₀ hpC
      have hLHS : (2 * Real.pi * Complex.I * ((x + y).val : ℂ) / (p : ℂ)) * (p : ℂ) =
          2 * Real.pi * Complex.I * ((x + y).val : ℂ) := div_mul_cancel₀ _ hpC
      have hRHS : ((2 * Real.pi * Complex.I * (x.val : ℂ) / (p : ℂ) +
          2 * Real.pi * Complex.I * (y.val : ℂ) / (p : ℂ)) + (q : ℂ) * (2 * Real.pi * Complex.I)) * (p : ℂ) =
          2 * Real.pi * Complex.I * (x.val : ℂ) + 2 * Real.pi * Complex.I * (y.val : ℂ) +
          (q : ℂ) * (2 * Real.pi * Complex.I) * (p : ℂ) := by
        rw [add_mul, add_mul, div_mul_cancel₀ _ hpC, div_mul_cancel₀ _ hpC]
      rw [hLHS, hRHS]
      linear_combination (2 * Real.pi * Complex.I) * hqC
    rw [heq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hep_sum : ∀ (S : Finset ℕ) (f : ℕ → ZMod p),
      ep (∑ m ∈ S, f m) = ∏ m ∈ S, ep (f m) := by
    intro S f
    induction S using Finset.induction_on with
    | empty => simp [ep]
    | insert b S hb ih => rw [Finset.sum_insert hb, Finset.prod_insert hb, hep_add, ih]
  have hep_mul_nat : ∀ (h : ℕ) (z : ZMod p),
      ep ((h : ZMod p) * z) = Complex.exp (2 * Real.pi * Complex.I * ((h * z.val : ℕ) : ℂ) / (p : ℂ)) := by
    intro h z
    induction h with
    | zero => simp [ep]
    | succ h ih =>
      rw [Nat.cast_succ, add_mul, one_mul, hep_add, ih]
      dsimp [ep]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
  -- Let N = number of K ⊆ M with ∑ m ∈ K, m⁻¹ = a
  set N : ℕ := (M.powerset.filter (fun (K : Finset ℕ) => ∑ m ∈ K, (m : ZMod p)⁻¹ = a)).card
  -- Fourier identity: p * N = 2^M.card + ∑_{h=1}^{p-1} ep(-h*a) * ∏_{m ∈ M} (1 + ep(h * m⁻¹))
  let Ph (h : ℕ) : ℂ := ∏ m ∈ M, ((1 : ℂ) + ep ((h : ZMod p) * (m : ZMod p)⁻¹))
  have hprod_expand : ∀ h : ℕ,
      Ph h = ∑ K ∈ M.powerset, ep ((h : ZMod p) * ∑ m ∈ K, (m : ZMod p)⁻¹) := by
    intro h
    dsimp [Ph]
    rw [Finset.prod_one_add]
    apply Finset.sum_congr rfl
    intro K _
    rw [Finset.mul_sum, hep_sum]
  have hFourier : (p : ℂ) * (N : ℂ) =
      (2 : ℂ) ^ M.card + ∑ h ∈ Finset.Ico 1 p, ep (-((h : ZMod p) * a)) * Ph h := by
    have hLHS : (p : ℂ) * (N : ℂ) =
        ∑ K ∈ M.powerset, ∑ h ∈ Finset.range p,
          ep ((h : ZMod p) * ((∑ m ∈ K, (m : ZMod p)⁻¹) - a)) := by
      have hinner : ∀ K ∈ M.powerset,
          ∑ h ∈ Finset.range p, ep ((h : ZMod p) * ((∑ m ∈ K, (m : ZMod p)⁻¹) - a)) =
          if ∑ m ∈ K, (m : ZMod p)⁻¹ = a then (p : ℂ) else 0 := by
        intro K _
        simp_rw [hep_mul_nat]
        rw [sum_exp_zmod hp.pos]
        simp [sub_eq_zero]
      rw [Finset.sum_congr rfl hinner, Finset.sum_ite, Finset.sum_const_zero, add_zero,
        Finset.sum_const, nsmul_eq_mul, mul_comm]
    rw [hLHS, Finset.sum_comm]
    have hsplit : Finset.range p = insert 0 (Finset.Ico 1 p) := by
      ext h; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
    rw [hsplit, Finset.sum_insert (by simp)]
    congr 1
    · have h0 : ∀ K ∈ M.powerset, ep (((0 : ℕ) : ZMod p) * ((∑ m ∈ K, (m : ZMod p)⁻¹) - a)) = 1 := by
        intro K _; simp [ep]
      rw [Finset.sum_congr rfl h0, Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, mul_one]
      norm_cast
    · apply Finset.sum_congr rfl
      intro h _
      rw [hprod_expand, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro K _
      rw [← hep_add, mul_sub, sub_eq_add_neg, add_comm]
  -- Bound ‖Ph h‖ < 2^M.card / p for each 1 ≤ h < p!
  have hPh_lt : ∀ h ∈ Finset.Ico 1 p, ‖Ph h‖ < (2 : ℝ) ^ M.card / (p : ℝ) := by
    intro h hh
    rw [Finset.mem_Ico] at hh
    set d : ℝ := C / (256 * B * (Real.log (p : ℝ)) ^ 2)
    have hlogp_pos : 0 < Real.log (p : ℝ) := by linarith
    have hC_pos : 0 < C := by nlinarith [sq_pos_of_pos hlogp_pos]
    have hd_pos : 0 < d := by positivity
    have hC_le_B : C ≤ B := by
      have hsub : M ⊆ Finset.Icc 1 ⌊B⌋₊ := by
        intro m hm
        obtain ⟨p₁, p₂, hp₁, hp₂, _, rfl⟩ := hM_semiprime m hm
        exact Finset.mem_Icc.mpr ⟨Nat.mul_pos hp₁.pos hp₂.pos, Nat.le_floor (hM_lt _ hm).le⟩
      have h1 : M.card ≤ ⌊B⌋₊ := by
        calc M.card ≤ (Finset.Icc 1 ⌊B⌋₊).card := Finset.card_le_card hsub
          _ = ⌊B⌋₊ := by simp
      exact le_trans (by dsimp [C]; exact_mod_cast h1) (Nat.floor_le hBpos.le)
    have hd_le : d ≤ 1 / 2 := by
      dsimp [d]
      rw [div_le_iff₀ (by positivity)]
      have hlogsq : (1 : ℝ) ≤ (Real.log (p : ℝ)) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hlogsq hBpos.le]
    set Good : Finset ℕ := M.filter (fun (m : ℕ) =>
        ∀ k : ℤ, d ≤ |(((h * (m : ZMod p)⁻¹).val : ℕ) : ℝ) / (p : ℝ) - (k : ℝ)|)
    set Rest : Finset ℕ := M.filter (fun (m : ℕ) =>
        ¬ ∀ k : ℤ, d ≤ |(((h * (m : ZMod p)⁻¹).val : ℕ) : ℝ) / (p : ℝ) - (k : ℝ)|)
    have hGood_card : C / 2 ≤ (Good.card : ℝ) :=
      halfbiglem_k2 hp hp100 hh.1 hh.2 hBpos hM_semiprime hM_cop hM_lt hC_gt256 hCp
    -- Product bound: ‖Ph h‖^2 ≤ 4^M.card * exp(-4 * d^2 * Good.card)
    have hnorm_sq_le : ‖Ph h‖ ^ 2 ≤ (4 : ℝ) ^ M.card * Real.exp (-4 * d ^ 2 * (Good.card : ℝ)) := by
      have hprod_norm : ‖Ph h‖ ^ 2 = ∏ m ∈ M, ‖(1 : ℂ) + ep ((h : ZMod p) * (m : ZMod p)⁻¹)‖ ^ 2 := by
        dsimp [Ph]
        rw [norm_prod, Finset.prod_pow]
      rw [hprod_norm, ← Finset.prod_filter_mul_prod_filter_not M (fun (m : ℕ) =>
          ∀ k : ℤ, d ≤ |(((h * (m : ZMod p)⁻¹).val : ℕ) : ℝ) / (p : ℝ) - (k : ℝ)|)]
      change (∏ m ∈ Good, ‖(1 : ℂ) + ep ((h : ZMod p) * (m : ZMod p)⁻¹)‖ ^ 2) *
          (∏ m ∈ Rest, ‖(1 : ℂ) + ep ((h : ZMod p) * (m : ZMod p)⁻¹)‖ ^ 2) ≤ _
      have hgood_bound : ∏ m ∈ Good, ‖(1 : ℂ) + ep ((h : ZMod p) * (m : ZMod p)⁻¹)‖ ^ 2 ≤
          (4 : ℝ) ^ Good.card * Real.exp (-4 * d ^ 2 * (Good.card : ℝ)) := by
        calc ∏ m ∈ Good, ‖(1 : ℂ) + ep ((h : ZMod p) * (m : ZMod p)⁻¹)‖ ^ 2
            ≤ ∏ _m ∈ Good, (4 * Real.exp (-4 * d ^ 2)) := by
              apply Finset.prod_le_prod (fun _ _ => sq_nonneg _)
              intro m hm
              have hdist := (Finset.mem_filter.mp hm).2
              have h1 : ep ((h : ZMod p) * (m : ZMod p)⁻¹) =
                  Complex.exp (2 * Real.pi * Complex.I *
                    (((((h : ZMod p) * (m : ZMod p)⁻¹).val : ℕ) : ℝ) / (p : ℝ) : ℝ)) := by
                dsimp [ep]
                congr 1
                push_cast
                ring
              rw [h1]
              have h2 := norm_one_add_exp_sq_le hd_pos.le hd_le hdist
              have h3 : 1 - 4 * d ^ 2 ≤ Real.exp (-4 * d ^ 2) := by
                linarith [Real.add_one_le_exp (-4 * d ^ 2)]
              linarith
          _ = (4 * Real.exp (-4 * d ^ 2)) ^ Good.card := by simp
          _ = (4 : ℝ) ^ Good.card * Real.exp (-4 * d ^ 2 * (Good.card : ℝ)) := by
              rw [mul_pow, ← Real.exp_nat_mul]; congr 2; ring
      have hrest_bound : ∏ m ∈ Rest, ‖(1 : ℂ) + ep ((h : ZMod p) * (m : ZMod p)⁻¹)‖ ^ 2 ≤
          (4 : ℝ) ^ Rest.card := by
        calc ∏ m ∈ Rest, ‖(1 : ℂ) + ep ((h : ZMod p) * (m : ZMod p)⁻¹)‖ ^ 2
            ≤ ∏ _m ∈ Rest, (4 : ℝ) := by
              apply Finset.prod_le_prod (fun _ _ => sq_nonneg _)
              intro m _
              have h1 : ‖(1 : ℂ) + ep ((h : ZMod p) * (m : ZMod p)⁻¹)‖ ≤ 2 := by
                have hexp1 : ‖ep ((h : ZMod p) * (m : ZMod p)⁻¹)‖ = 1 := by
                  dsimp [ep]
                  have hrw : 2 * Real.pi * Complex.I * (((h : ZMod p) * (m : ZMod p)⁻¹).val : ℂ) / (p : ℂ) =
                      ((2 * Real.pi * (((h : ZMod p) * (m : ZMod p)⁻¹).val : ℝ) / (p : ℝ) : ℝ) : ℂ) * Complex.I := by
                    push_cast; ring
                  rw [hrw, Complex.norm_exp_ofReal_mul_I]
                calc ‖(1 : ℂ) + ep _‖ ≤ ‖(1 : ℂ)‖ + ‖ep _‖ := norm_add_le _ _
                  _ = 2 := by rw [norm_one, hexp1]; norm_num
              nlinarith [norm_nonneg ((1 : ℂ) + ep ((h : ZMod p) * (m : ZMod p)⁻¹))]
          _ = (4 : ℝ) ^ Rest.card := by simp
      have hcard_add : Good.card + Rest.card = M.card :=
        Finset.card_filter_add_card_filter_not _
      calc (∏ m ∈ Good, ‖(1 : ℂ) + ep ((h : ZMod p) * (m : ZMod p)⁻¹)‖ ^ 2) *
            (∏ m ∈ Rest, ‖(1 : ℂ) + ep ((h : ZMod p) * (m : ZMod p)⁻¹)‖ ^ 2)
          ≤ ((4 : ℝ) ^ Good.card * Real.exp (-4 * d ^ 2 * (Good.card : ℝ))) *
              (4 : ℝ) ^ Rest.card :=
            mul_le_mul hgood_bound hrest_bound (Finset.prod_nonneg (fun _ _ => sq_nonneg _)) (by positivity)
        _ = (4 : ℝ) ^ M.card * Real.exp (-4 * d ^ 2 * (Good.card : ℝ)) := by
            rw [← hcard_add, pow_add]; ring
    -- Show 4 * d^2 * Good.card > 2 * log p
    have hexp_gt : 2 * Real.log (p : ℝ) < 4 * d ^ 2 * (Good.card : ℝ) := by
      have h1 : 2 * C * d ^ 2 ≤ 4 * d ^ 2 * (Good.card : ℝ) := by nlinarith [sq_nonneg d]
      have hC3 : (100 : ℝ) ^ 3 * B ^ 2 * (Real.log (p : ℝ)) ^ 6 < C ^ 3 := by
        have hpow := pow_lt_pow_left₀ hC_lo (by positivity) (by norm_num : 3 ≠ 0)
        have hBpow : (B ^ ((2 : ℝ) / 3)) ^ (3 : ℕ) = B ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hBpos.le]
          norm_num
        have hLHS : (100 * B ^ ((2 : ℝ) / 3) * (Real.log (p : ℝ)) ^ 2) ^ 3 =
            (100 : ℝ) ^ 3 * B ^ 2 * (Real.log (p : ℝ)) ^ 6 := by
          rw [mul_pow, mul_pow, hBpow]; ring
        linarith
      have h2Cd2 : 2 * C * d ^ 2 = C ^ 3 / (32768 * B ^ 2 * (Real.log (p : ℝ)) ^ 4) := by
        dsimp [d]; field_simp; ring
      have hgt2 : 2 * Real.log (p : ℝ) < C ^ 3 / (32768 * B ^ 2 * (Real.log (p : ℝ)) ^ 4) := by
        rw [lt_div_iff₀ (by positivity)]
        have hlog5 : Real.log (p : ℝ) ^ 5 ≤ Real.log (p : ℝ) ^ 6 :=
          pow_le_pow_right₀ hlogp_ge.le (by norm_num : 5 ≤ 6)
        nlinarith [sq_pos_of_pos hBpos, pow_pos hlogp_pos 5]
      linarith
    have hsq_lt : ‖Ph h‖ ^ 2 < ((2 : ℝ) ^ M.card / (p : ℝ)) ^ 2 := by
      have hexp_lt : Real.exp (-4 * d ^ 2 * (Good.card : ℝ)) < Real.exp (-(2 * Real.log (p : ℝ))) :=
        Real.exp_lt_exp.mpr (by linarith)
      have hexp_p : Real.exp (-(2 * Real.log (p : ℝ))) = ((p : ℝ) ^ 2)⁻¹ := by
        rw [Real.exp_neg, show 2 * Real.log (p : ℝ) = ((2 : ℕ) : ℝ) * Real.log (p : ℝ) by norm_num,
          ← Real.log_pow, Real.exp_log (by positivity)]
      rw [hexp_p] at hexp_lt
      have h4_eq : (4 : ℝ) ^ M.card * ((p : ℝ) ^ 2)⁻¹ = ((2 : ℝ) ^ M.card / (p : ℝ)) ^ 2 := by
        rw [div_pow, ← pow_mul, mul_comm M.card 2, pow_mul]
        norm_num
        ring
      calc ‖Ph h‖ ^ 2 ≤ (4 : ℝ) ^ M.card * Real.exp (-4 * d ^ 2 * (Good.card : ℝ)) := hnorm_sq_le
        _ < (4 : ℝ) ^ M.card * ((p : ℝ) ^ 2)⁻¹ := mul_lt_mul_of_pos_left hexp_lt (by positivity)
        _ = ((2 : ℝ) ^ M.card / (p : ℝ)) ^ 2 := h4_eq
    nlinarith [norm_nonneg (Ph h), div_pos (pow_pos (by norm_num : (0 : ℝ) < 2) M.card) hppos]
  -- Conclude N > 0 from hFourier and hPh_lt!
  have hN_pos : 0 < N := by
    by_contra hN0
    have hNz : N = 0 := by omega
    rw [hNz, Nat.cast_zero, mul_zero] at hFourier
    have heq2 : (2 : ℂ) ^ M.card = -(∑ h ∈ Finset.Ico 1 p, ep (-((h : ZMod p) * a)) * Ph h) :=
      eq_neg_of_add_eq_zero_left hFourier.symm
    have hnorm2 : (2 : ℝ) ^ M.card ≤ ∑ h ∈ Finset.Ico 1 p, ‖Ph h‖ := by
      have h1 : ‖(2 : ℂ) ^ M.card‖ = (2 : ℝ) ^ M.card := by simp
      rw [← h1, heq2, norm_neg]
      calc ‖∑ h ∈ Finset.Ico 1 p, ep (-((h : ZMod p) * a)) * Ph h‖
          ≤ ∑ h ∈ Finset.Ico 1 p, ‖ep (-((h : ZMod p) * a)) * Ph h‖ := norm_sum_le _ _
        _ = ∑ h ∈ Finset.Ico 1 p, ‖Ph h‖ := by
            apply Finset.sum_congr rfl
            intro h _
            rw [norm_mul]
            have h1 : ‖ep (-((h : ZMod p) * a))‖ = 1 := by
              dsimp [ep]
              have hrw : 2 * Real.pi * Complex.I * ((-((h : ZMod p) * a)).val : ℂ) / (p : ℂ) =
                  ((2 * Real.pi * ((-((h : ZMod p) * a)).val : ℝ) / (p : ℝ) : ℝ) : ℂ) * Complex.I := by
                push_cast; ring
              rw [hrw, Complex.norm_exp_ofReal_mul_I]
            rw [h1, one_mul]
    have hne : (Finset.Ico 1 p).Nonempty := ⟨1, Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩⟩
    have hstrict : ∑ h ∈ Finset.Ico 1 p, ‖Ph h‖ < ∑ _h ∈ Finset.Ico 1 p, ((2 : ℝ) ^ M.card / (p : ℝ)) :=
      Finset.sum_lt_sum_of_nonempty hne hPh_lt
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at hstrict
    have hpm1 : ((p - 1 : ℕ) : ℝ) * ((2 : ℝ) ^ M.card / (p : ℝ)) ≤ (2 : ℝ) ^ M.card := by
      have hle : ((p - 1 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast Nat.sub_le p 1
      calc ((p - 1 : ℕ) : ℝ) * ((2 : ℝ) ^ M.card / (p : ℝ))
          ≤ (p : ℝ) * ((2 : ℝ) ^ M.card / (p : ℝ)) := mul_le_mul_of_nonneg_right hle (by positivity)
        _ = (2 : ℝ) ^ M.card := mul_div_cancel₀ _ hppos.ne'
    linarith
  obtain ⟨K, hK⟩ := Finset.card_pos.mp hN_pos
  rw [Finset.mem_filter, Finset.mem_powerset] at hK
  exact ⟨K, hK.1, hK.2⟩

end E292Part2


namespace E292Part3

open Finset Filter Real E292Part1
open scoped Classical

/- ## Part 5: Universal prime-power denominator cancellation lemma -/

/-- Universal prime-power cancellation lemma (addition version, for `biglem`):
if `PStar r.den ≤ p^ν`, `p^ν ∣ r.den`, every `m ∈ K` is positive, coprime to `p`, with `PStar m < p^ν`,
and `(r.num : ZMod p) * ((r.den / p^ν : ℕ) : ZMod p)⁻¹ + ∑ m ∈ K, (m : ZMod p)⁻¹ = 0`,
then `PStar (r + ∑ m ∈ K, (1 : ℚ) / (p^ν * m)).den < p^ν`. -/
lemma PStar_add_sum_cancel {r : ℚ} {p ν : ℕ} {K : Finset ℕ}
    (hp : p.Prime) (hν : 1 ≤ ν)
    (hPr : PStar r.den ≤ p ^ ν) (hdvd : p ^ ν ∣ r.den)
    (hK : ∀ m ∈ K, 0 < m ∧ ¬ p ∣ m ∧ PStar m < p ^ ν)
    (hcong : (r.num : ZMod p) * ((r.den / p ^ ν : ℕ) : ZMod p)⁻¹ +
        ∑ m ∈ K, (m : ZMod p)⁻¹ = 0) :
    PStar (r + ∑ m ∈ K, (1 : ℚ) / ((p ^ ν * m : ℕ) : ℚ)).den < p ^ ν := by
  have : Fact p.Prime := ⟨hp⟩
  set q : ℕ := p ^ ν
  have hq_pos : 0 < q := pow_pos hp.pos ν
  have hq_ge2 : 2 ≤ q := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  -- Step 1: PStar ≤ q
  have hsum_PStar : PStar (∑ m ∈ K, (1 : ℚ) / ((q * m : ℕ) : ℚ)).den ≤ q := by
    have h1 : ∑ m ∈ K, (1 : ℚ) / ((q * m : ℕ) : ℚ) = ∑ n ∈ K.image (fun m => q * m), (1 : ℚ) / (n : ℚ) := by
      rw [Finset.sum_image]
      intro a _ b _ hab
      exact Nat.eq_of_mul_eq_mul_left hq_pos hab
    rw [h1]
    apply PStar_sum_inv_den_le _ q (by omega)
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
    obtain ⟨hm0, hnd, hPm⟩ := hK m hm
    exact ⟨Nat.mul_pos hq_pos hm0, (PStar_mul_prime_pow_eq hp hν hm0 hnd hPm).le⟩
  have hle : PStar (r + ∑ m ∈ K, (1 : ℚ) / ((q * m : ℕ) : ℚ)).den ≤ q :=
    (PStar_rat_add_den_le _ _).trans (max_le hPr hsum_PStar)
  -- Step 2: show ¬ q ∣ den, hence PStar < q!
  set d₀ : ℕ := r.den / q
  have hd₀_eq : q * d₀ = r.den := Nat.mul_div_cancel' hdvd
  have hd₀_pos : 0 < d₀ := by
    rcases Nat.eq_zero_or_pos d₀ with h0 | hpos
    · rw [h0, mul_zero] at hd₀_eq; exact absurd hd₀_eq.symm r.den_nz
    · exact hpos
  have hd₀_ndvd : ¬ p ∣ d₀ := by
    intro hpd
    have hpow : p ^ (ν + 1) ∣ r.den := by
      rw [← hd₀_eq, pow_succ]
      exact mul_dvd_mul_left q hpd
    have hle1 : p ^ (ν + 1) ≤ PStar r.den := prime_pow_dvd_le_PStar r.den_pos hp hpow
    have hlt : p ^ ν < p ^ (ν + 1) := Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self ν)
    omega
  set P : ℕ := ∏ m ∈ K, m
  have hP_pos : 0 < P := Finset.prod_pos (fun m hm => (hK m hm).1)
  have hP_ndvd : ¬ p ∣ P := by
    intro h
    obtain ⟨m, hm, hpm⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp h
    exact (hK m hm).2.1 hpm
  set M : ℕ := d₀ * P
  have hM_pos : 0 < M := Nat.mul_pos hd₀_pos hP_pos
  have hM_ndvd : ¬ p ∣ M := hp.prime.not_dvd_mul hd₀_ndvd hP_ndvd
  -- Integer numerator A = (q * M) * (r + ∑ 1/(q*m))
  set A : ℤ := r.num * (P : ℤ) + (d₀ : ℤ) * ∑ m ∈ K, ((∏ j ∈ K.erase m, j : ℕ) : ℤ)
  have hqM_eq : ((q * M : ℕ) : ℚ) * (r + ∑ m ∈ K, (1 : ℚ) / ((q * m : ℕ) : ℚ)) = (A : ℚ) := by
    rw [mul_add]
    have ht1 : ((q * M : ℕ) : ℚ) * r = (r.num : ℚ) * (P : ℚ) := by
      have hrm : (r.den : ℚ) * r = (r.num : ℚ) := by rw [mul_comm]; exact Rat.mul_den_eq_num r
      have hqMeq : ((q * M : ℕ) : ℚ) = (r.den : ℚ) * (P : ℚ) := by
        dsimp [M]; rw [← mul_assoc, hd₀_eq]; push_cast; ring
      rw [hqMeq]
      linear_combination (P : ℚ) * hrm
    have ht2 : ((q * M : ℕ) : ℚ) * ∑ m ∈ K, (1 : ℚ) / ((q * m : ℕ) : ℚ) =
        (d₀ : ℚ) * ∑ m ∈ K, ((∏ j ∈ K.erase m, j : ℕ) : ℚ) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      have hm0 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (hK m hm).1.ne'
      have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq_pos.ne'
      have hPsplit : (P : ℚ) = (m : ℚ) * ((∏ j ∈ K.erase m, j : ℕ) : ℚ) := by
        have hnat : P = m * ∏ j ∈ K.erase m, j := (Finset.mul_prod_erase K (fun j => j) hm).symm
        rw [hnat]; push_cast; rfl
      dsimp [M]
      rw [Nat.cast_mul, Nat.cast_mul, hPsplit, Nat.cast_mul]
      field_simp [hq0, hm0]
    rw [ht1, ht2]
    dsimp [A]
    push_cast
    rfl
  -- Show p ∣ A via ZMod p!
  have hp_dvd_A : (p : ℤ) ∣ A := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hd₀0 : (d₀ : ZMod p) ≠ 0 := fun h => hd₀_ndvd ((ZMod.natCast_eq_zero_iff d₀ p).mp h)
    have hP0 : (P : ZMod p) ≠ 0 := fun h => hP_ndvd ((ZMod.natCast_eq_zero_iff P p).mp h)
    have hcast : (A : ZMod p) = (d₀ : ZMod p) * (P : ZMod p) *
        ((r.num : ZMod p) * (d₀ : ZMod p)⁻¹ + ∑ m ∈ K, (m : ZMod p)⁻¹) := by
      dsimp [A]
      push_cast
      rw [mul_add]
      congr 1
      · calc (r.num : ZMod p) * (P : ZMod p)
            = (r.num : ZMod p) * (P : ZMod p) * ((d₀ : ZMod p) * (d₀ : ZMod p)⁻¹) := by
                rw [mul_inv_cancel₀ hd₀0, mul_one]
          _ = (d₀ : ZMod p) * (P : ZMod p) * ((r.num : ZMod p) * (d₀ : ZMod p)⁻¹) := by ring
      · rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        have hm0 : (m : ZMod p) ≠ 0 := fun h => (hK m hm).2.1 ((ZMod.natCast_eq_zero_iff m p).mp h)
        have hPs : (P : ZMod p) = (m : ZMod p) * ((∏ j ∈ K.erase m, j : ℕ) : ZMod p) := by
          have hnat : P = m * ∏ j ∈ K.erase m, j := (Finset.mul_prod_erase K (fun j => j) hm).symm
          rw [hnat, Nat.cast_mul]
        rw [hPs]
        have hprod_eq : (d₀ : ZMod p) * ((m : ZMod p) * ((∏ j ∈ K.erase m, j : ℕ) : ZMod p)) * (m : ZMod p)⁻¹ =
            (d₀ : ZMod p) * ((∏ j ∈ K.erase m, j : ℕ) : ZMod p) * ((m : ZMod p) * (m : ZMod p)⁻¹) := by ring
        rw [hprod_eq, mul_inv_cancel₀ hm0, mul_one]
        simp only [Nat.cast_prod]
    rw [hcast, hcong, mul_zero]
  obtain ⟨B, hB⟩ := hp_dvd_A
  set r' : ℚ := r + ∑ m ∈ K, (1 : ℚ) / ((q * m : ℕ) : ℚ)
  -- Show r'.den ∣ p^(ν - 1) * M
  have hden_dvd : r'.den ∣ p ^ (ν - 1) * M := by
    have hq_split : q = p * p ^ (ν - 1) := by
      dsimp [q]; rw [← pow_succ', Nat.sub_add_cancel hν]
    have heqQ : ((p ^ (ν - 1) * M : ℕ) : ℚ) * r' = (B : ℚ) := by
      have hpQ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
      apply mul_left_cancel₀ hpQ
      have h1 : (p : ℚ) * (((p ^ (ν - 1) * M : ℕ) : ℚ) * r') = ((q * M : ℕ) : ℚ) * r' := by
        rw [hq_split]; push_cast; ring
      rw [h1, hqM_eq, hB]; push_cast; ring
    have hmulZ : r'.num * ((p ^ (ν - 1) * M : ℕ) : ℤ) = B * (r'.den : ℤ) := by
      have hmulQ : (r'.num : ℚ) * ((p ^ (ν - 1) * M : ℕ) : ℚ) = (B : ℚ) * (r'.den : ℚ) := by
        calc (r'.num : ℚ) * ((p ^ (ν - 1) * M : ℕ) : ℚ)
            = (r' * (r'.den : ℚ)) * ((p ^ (ν - 1) * M : ℕ) : ℚ) := by rw [Rat.mul_den_eq_num]
          _ = (((p ^ (ν - 1) * M : ℕ) : ℚ) * r') * (r'.den : ℚ) := by ring
          _ = (B : ℚ) * (r'.den : ℚ) := by rw [heqQ]
      exact_mod_cast hmulQ
    have hd1 : (r'.den : ℤ) ∣ r'.num * ((p ^ (ν - 1) * M : ℕ) : ℤ) := ⟨B, by linarith⟩
    have hcop : IsCoprime (r'.den : ℤ) r'.num :=
      Int.isCoprime_iff_nat_coprime.mpr (by simpa [Int.natAbs_natCast] using r'.reduced.symm)
    exact Int.ofNat_dvd.mp (hcop.dvd_of_dvd_mul_left hd1)
  have hndvd_q : ¬ q ∣ r'.den := by
    intro hqr
    have h1 : q ∣ p ^ (ν - 1) * M := dvd_trans hqr hden_dvd
    have hq_split : q = p ^ (ν - 1) * p := by
      dsimp [q]; rw [← pow_succ, Nat.sub_add_cancel hν]
    rw [hq_split] at h1
    have h2 : p ∣ M := (mul_dvd_mul_iff_left (pow_pos hp.pos (ν - 1)).ne').mp h1
    exact hM_ndvd h2
  -- Combine PStar r'.den ≤ q and ¬ q ∣ r'.den → PStar r'.den < q!
  by_contra hge
  have heq : PStar r'.den = q := by omega
  have hr1 : 1 < r'.den := by
    by_contra hle1
    have h1 : r'.den = 1 := by have := r'.den_pos; omega
    rw [h1, PStar_one] at heq
    omega
  obtain ⟨p', ν', _, _, hpeq, hdvd', _⟩ := exists_prime_pow_eq_PStar hr1
  rw [heq] at hpeq
  exact hndvd_q (hpeq ▸ hdvd')

/-- Subtraction version of `PStar_add_sum_cancel` (for `medlem` and `smalllem`). -/
lemma PStar_sub_sum_cancel {r : ℚ} {p ν : ℕ} {K : Finset ℕ}
    (hp : p.Prime) (hν : 1 ≤ ν)
    (hPr : PStar r.den ≤ p ^ ν) (hdvd : p ^ ν ∣ r.den)
    (hK : ∀ m ∈ K, 0 < m ∧ ¬ p ∣ m ∧ PStar m < p ^ ν)
    (hcong : ∑ m ∈ K, (m : ZMod p)⁻¹ = (r.num : ZMod p) * ((r.den / p ^ ν : ℕ) : ZMod p)⁻¹) :
    PStar (r - ∑ m ∈ K, (1 : ℚ) / ((p ^ ν * m : ℕ) : ℚ)).den < p ^ ν := by
  have hneg : r - ∑ m ∈ K, (1 : ℚ) / ((p ^ ν * m : ℕ) : ℚ) =
      -((-r) + ∑ m ∈ K, (1 : ℚ) / ((p ^ ν * m : ℕ) : ℚ)) := by ring
  rw [hneg, PStar_rat_neg_den]
  apply PStar_add_sum_cancel hp hν (by simpa [Rat.neg_den] using hPr)
    (by simpa [Rat.neg_den] using hdvd) hK
  simp only [Rat.neg_num, Rat.neg_den, Int.cast_neg, neg_mul]
  rw [hcong, neg_add_cancel]

/- ## Part 6: Martin's `unetun`, `medlem`, `smalllem`, and `small_prop` -/

/-- Lemma `unetun` (Martin 2000, Lemma 5.1): for any odd prime power `q = p^ν ≥ 5` and
`a : ZMod p`, there exist `m₁ < m₂` with `q / 5 ≤ m₁`, `m₂ < q`, `¬ p ∣ m₁`, `¬ p ∣ m₂`,
and `(m₁ : ZMod p)⁻¹ + (m₂ : ZMod p)⁻¹ = a`. -/
lemma unetun {p ν : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (hν : 1 ≤ ν) (hq5 : 5 ≤ p ^ ν) (a : ZMod p) :
    ∃ m₁ m₂ : ℕ, m₁ < m₂ ∧ p ^ ν ≤ 5 * m₁ ∧ m₂ < p ^ ν ∧
      ¬ p ∣ m₁ ∧ ¬ p ∣ m₂ ∧ (m₁ : ZMod p)⁻¹ + (m₂ : ZMod p)⁻¹ = a := by
  have : Fact p.Prime := ⟨hp⟩
  set q : ℕ := p ^ ν
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  rcases eq_or_lt_of_le hp3 with rfl | hp5
  · -- Case p = 3, so ν ≥ 2 and q ≥ 9
    have hq9 : 9 ≤ q := by
      have hν2 : 2 ≤ ν := by
        by_contra h; have h1 : ν = 1 := by omega
        subst h1; dsimp [q] at hq5; omega
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ ν := Nat.pow_le_pow_right (by norm_num) hν2
    have h3q : 3 ∣ q := dvd_pow_self 3 (by omega)
    have hq0 : (q : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff q 3).mpr h3q
    have h3z0 : ((0 : ZMod 3) - 2 : ZMod 3) = 1 := rfl
    have h3z1 : ((0 : ZMod 3) - 1 : ZMod 3) = 2 := rfl
    have h3z4 : ((0 : ZMod 3) - 4 : ZMod 3) = 2 := rfl
    have h3z5 : ((0 : ZMod 3) - 5 : ZMod 3) = 1 := rfl
    have hinv2 : (2 : ZMod 3)⁻¹ = 2 := inv_eq_of_mul_eq_one_right (rfl : (2 : ZMod 3) * 2 = 1)
    have h3a0 : (1 : ZMod 3)⁻¹ + (2 : ZMod 3)⁻¹ = 0 := by rw [inv_one, hinv2]; rfl
    have h3a1 : (2 : ZMod 3)⁻¹ + (2 : ZMod 3)⁻¹ = 1 := by rw [hinv2]; rfl
    have h3a2 : (1 : ZMod 3)⁻¹ + (1 : ZMod 3)⁻¹ = 2 := by rw [inv_one]; rfl
    fin_cases a
    · -- a = 0: (q - 2, q - 1)
      refine ⟨q - 2, q - 1, by omega, by omega, by omega, ?_, ?_, ?_⟩
      · intro h; have := (Nat.dvd_sub_iff_right (by omega) h3q).mp h; omega
      · intro h; have := (Nat.dvd_sub_iff_right (by omega) h3q).mp h; omega
      · have h1 : ((q - 2 : ℕ) : ZMod 3) = 1 := by
          rw [Nat.cast_sub (by omega), hq0]; exact h3z0
        have h2 : ((q - 1 : ℕ) : ZMod 3) = 2 := by
          rw [Nat.cast_sub (by omega), hq0]; exact h3z1
        rw [h1, h2]; exact h3a0
    · -- a = 1: (q - 4, q - 1)
      refine ⟨q - 4, q - 1, by omega, by omega, by omega, ?_, ?_, ?_⟩
      · intro h; have := (Nat.dvd_sub_iff_right (by omega) h3q).mp h; omega
      · intro h; have := (Nat.dvd_sub_iff_right (by omega) h3q).mp h; omega
      · have h1 : ((q - 4 : ℕ) : ZMod 3) = 2 := by
          rw [Nat.cast_sub (by omega), hq0]; exact h3z4
        have h2 : ((q - 1 : ℕ) : ZMod 3) = 2 := by
          rw [Nat.cast_sub (by omega), hq0]; exact h3z1
        rw [h1, h2]; exact h3a1
    · -- a = 2: (q - 5, q - 2)
      refine ⟨q - 5, q - 2, by omega, by omega, by omega, ?_, ?_, ?_⟩
      · intro h; have := (Nat.dvd_sub_iff_right (by omega) h3q).mp h; omega
      · intro h; have := (Nat.dvd_sub_iff_right (by omega) h3q).mp h; omega
      · have h1 : ((q - 5 : ℕ) : ZMod 3) = 1 := by
          rw [Nat.cast_sub (by omega), hq0]; exact h3z5
        have h2 : ((q - 2 : ℕ) : ZMod 3) = 1 := by
          rw [Nat.cast_sub (by omega), hq0]; exact h3z0
        rw [h1, h2]; exact h3a2
  · -- Case p ≥ 5: pigeonhole on M = Ico (q - (p + 3)/2) q
    have hp5' : 5 ≤ p := by
      by_contra h
      have hp4 : p = 4 := by omega
      subst hp4; exact absurd hp (by decide)
    set k : ℕ := (p + 3) / 2
    have hk_lt : k < p := by dsimp [k]; omega
    have hk_ge : p + 2 ≤ 2 * k := by dsimp [k]; omega
    have hp_le_q : p ≤ q := Nat.le_self_pow (by omega) p
    set M := Finset.Ico (q - k) q
    have hM_card : M.card = k := by simp [M]; omega
    have hM_cop : ∀ m ∈ M, ¬ p ∣ m := by
      intro m hm hpm
      rw [Finset.mem_Ico] at hm
      have hpq : p ∣ q := dvd_pow_self p (by omega)
      have hsub : p ∣ q - m := Nat.dvd_sub hpq hpm
      have hle : p ≤ q - m := Nat.le_of_dvd (by omega) hsub
      omega
    have hM_inj : Set.InjOn (fun m : ℕ => (m : ZMod p)⁻¹) (M : Set ℕ) := by
      intro m₁ hm₁ m₂ hm₂ heq
      have h1 : (m₁ : ZMod p) = (m₂ : ZMod p) := inv_injective heq
      rw [Finset.mem_coe, Finset.mem_Ico] at hm₁ hm₂
      have hmod : (m₁ : ℤ) ≡ (m₂ : ℤ) [ZMOD (p : ℤ)] := (ZMod.intCast_eq_intCast_iff _ _ _).mp (by simpa using h1)
      have hdvd : (p : ℤ) ∣ (m₁ : ℤ) - (m₂ : ℤ) := Int.modEq_iff_dvd.mp hmod.symm
      obtain ⟨t, ht⟩ := hdvd
      have hlt : |(m₁ : ℤ) - (m₂ : ℤ)| < (p : ℤ) := by
        rw [abs_lt]; constructor <;> omega
      have ht0 : t = 0 := by nlinarith [abs_lt.mp hlt]
      have heqZ : (m₁ : ℤ) = (m₂ : ℤ) := by nlinarith
      exact_mod_cast heqZ
    set M₁ := M.image (fun m : ℕ => (m : ZMod p)⁻¹)
    set M₂ := M.image (fun m : ℕ => a - (m : ZMod p)⁻¹)
    have hM₁_card : M₁.card = k := by
      rw [Finset.card_image_of_injOn hM_inj, hM_card]
    have hM₂_card : M₂.card = k := by
      have hinj2 : Set.InjOn (fun m : ℕ => a - (m : ZMod p)⁻¹) (M : Set ℕ) := by
        intro m₁ hm₁ m₂ hm₂ heq
        exact hM_inj hm₁ hm₂ (sub_right_injective heq)
      rw [Finset.card_image_of_injOn hinj2, hM_card]
    have hinter_card : 2 ≤ (M₁ ∩ M₂).card := by
      have hu := Finset.card_union_add_card_inter M₁ M₂
      have hle_p : (M₁ ∪ M₂).card ≤ p := by
        calc (M₁ ∪ M₂).card ≤ (Finset.univ : Finset (ZMod p)).card := Finset.card_le_card (Finset.subset_univ _)
          _ = p := by simp [ZMod.card]
      omega
    -- Pick x ∈ M₁ ∩ M₂ with x ≠ (2 : ZMod p)⁻¹ * a (so x ≠ a - x!)
    have hex_x : ∃ x ∈ M₁ ∩ M₂, x ≠ a - x := by
      set S := (M₁ ∩ M₂).erase ((2 : ZMod p)⁻¹ * a)
      have hS_pos : 0 < S.card := by
        have h1 : (M₁ ∩ M₂).card - 1 ≤ S.card := Finset.pred_card_le_card_erase
        omega
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hS_pos
      rw [Finset.mem_erase] at hx
      refine ⟨x, hx.2, fun heq => hx.1 ?_⟩
      have h20 : (2 : ZMod p) ≠ 0 := by
        intro hz
        have := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using hz)
        have := Nat.le_of_dvd (by norm_num) this
        omega
      have h2x : (2 : ZMod p) * x = a := by linear_combination heq
      calc x = (2 : ZMod p)⁻¹ * ((2 : ZMod p) * x) := by rw [← mul_assoc, inv_mul_cancel₀ h20, one_mul]
        _ = (2 : ZMod p)⁻¹ * a := by rw [h2x]
    obtain ⟨x, hx, hxne⟩ := hex_x
    rw [Finset.mem_inter] at hx
    rcases Finset.mem_image.mp hx.1 with ⟨u₁, hu₁, rfl⟩
    rcases Finset.mem_image.mp hx.2 with ⟨u₂, hu₂, hu₂eq⟩
    have hsum : (u₁ : ZMod p)⁻¹ + (u₂ : ZMod p)⁻¹ = a := by linear_combination -hu₂eq
    have hune : u₁ ≠ u₂ := by
      intro h; subst h; exact hxne hu₂eq.symm
    have hlo : ∀ m ∈ M, q ≤ 5 * m := by
      intro m hm
      rw [Finset.mem_Ico] at hm
      -- 5 * (q - k) ≥ q ↔ 4 * q ≥ 5 * k; since k = (p+3)/2 ≤ p - 1 and p ≤ q, 5*k ≤ 5*(p+3)/2 ≤ 4*q for p ≥ 5!
      have : 5 * k ≤ 4 * q := by dsimp [k]; omega
      omega
    rcases lt_or_gt_of_ne hune with hlt | hgt
    · exact ⟨u₁, u₂, hlt, hlo u₁ hu₁, (Finset.mem_Ico.mp hu₂).2, hM_cop u₁ hu₁, hM_cop u₂ hu₂, hsum⟩
    · exact ⟨u₂, u₁, hgt, hlo u₂ hu₂, (Finset.mem_Ico.mp hu₁).2, hM_cop u₂ hu₂, hM_cop u₁ hu₁, by rw [add_comm]; exact hsum⟩

/-- Lemma `medlem` (Martin 2000, Lemma 5.2): for any prime power `q = p^ν ≥ 4` and rational `r`
with `PStar r.den ≤ q`, there exists `U : Finset ℕ` with:
(i) `∀ n ∈ U, q^2 / 5 ≤ n ≤ q^2` (as `q^2 ≤ 5 * n ∧ n ≤ q^2`),
(ii) `U.card ≤ 2`,
(iii) `∀ n ∈ U, PStar n = q`,
(iv) `PStar (r - ∑ n ∈ U, (1 : ℚ) / n).den < q`. -/
lemma medlem {p ν : ℕ} {r : ℚ} (hp : p.Prime) (hν : 1 ≤ ν) (hq4 : 4 ≤ p ^ ν)
    (hPr : PStar r.den ≤ p ^ ν) :
    ∃ U : Finset ℕ,
      (∀ n ∈ U, (p ^ ν) ^ 2 ≤ 5 * n ∧ n ≤ (p ^ ν) ^ 2 ∧ PStar n = p ^ ν) ∧
      U.card ≤ 2 ∧
      PStar (r - ∑ n ∈ U, (1 : ℚ) / (n : ℚ)).den < p ^ ν := by
  have : Fact p.Prime := ⟨hp⟩
  set q : ℕ := p ^ ν
  have hq_pos : 0 < q := pow_pos hp.pos ν
  by_cases hdvd : q ∣ r.den
  · by_cases hp2 : p = 2
    · -- Even prime power q = 2^ν ≥ 4: take K = {q - 1}, U = {q * (q - 1)}
      subst hp2
      have hqm1_pos : 0 < q - 1 := by omega
      have hqm1_ndvd : ¬ 2 ∣ q - 1 := by
        have h2q : 2 ∣ q := dvd_pow_self 2 (by omega)
        intro h; have := (Nat.dvd_sub_iff_right (by omega) h2q).mp h; omega
      have hqm1_PStar : PStar (q - 1) < q := lt_of_le_of_lt (PStar_le_self _) (by omega)
      have hcong : ∑ m ∈ ({q - 1} : Finset ℕ), (m : ZMod 2)⁻¹ =
          (r.num : ZMod 2) * ((r.den / q : ℕ) : ZMod 2)⁻¹ := by
        simp only [Finset.sum_singleton]
        have hnum_odd : (r.num : ZMod 2) ≠ 0 := by
          intro h
          have hd2 : (2 : ℤ) ∣ r.num := (ZMod.intCast_zmod_eq_zero_iff_dvd r.num 2).mp h
          have h2den : 2 ∣ r.den := dvd_trans (dvd_pow_self 2 (by omega)) hdvd
          have h2num : 2 ∣ r.num.natAbs := Int.natCast_dvd.mp hd2
          have hcop := r.reduced
          have h2g : 2 ∣ Nat.gcd r.num.natAbs r.den := Nat.dvd_gcd h2num h2den
          rw [hcop] at h2g; omega
        have hd0_odd : ((r.den / q : ℕ) : ZMod 2) ≠ 0 := by
          intro h
          have h2d : 2 ∣ r.den / q := (ZMod.natCast_eq_zero_iff _ 2).mp h
          have h2pow : 2 ^ (ν + 1) ∣ r.den := by
            rw [← Nat.mul_div_cancel' hdvd, pow_succ]
            exact mul_dvd_mul_left q h2d
          have hle := prime_pow_dvd_le_PStar r.den_pos Nat.prime_two h2pow
          have hlt : 2 ^ ν < 2 ^ (ν + 1) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self ν)
          omega
        have hm_odd : ((q - 1 : ℕ) : ZMod 2) ≠ 0 :=
          fun h => hqm1_ndvd ((ZMod.natCast_eq_zero_iff _ 2).mp h)
        have h1 : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by
          intro z hz; fin_cases z
          · exact absurd rfl hz
          · rfl
        rw [h1 _ hm_odd, h1 _ hnum_odd, h1 _ hd0_odd]; simp
      have hcancel := PStar_sub_sum_cancel Nat.prime_two hν hPr hdvd (K := {q - 1})
        (fun m hm => by rw [Finset.mem_singleton.mp hm]; exact ⟨hqm1_pos, hqm1_ndvd, hqm1_PStar⟩)
        hcong
      refine ⟨{q * (q - 1)}, ?_, by simp, ?_⟩
      · intro n hn
        rw [Finset.mem_singleton.mp hn]
        refine ⟨?_, ?_, PStar_mul_prime_pow_eq Nat.prime_two hν hqm1_pos hqm1_ndvd hqm1_PStar⟩
        · have : q ≤ 5 * (q - 1) := by omega
          calc q ^ 2 = q * q := sq q
            _ ≤ q * (5 * (q - 1)) := Nat.mul_le_mul_left q this
            _ = 5 * (q * (q - 1)) := by ring
        · calc q * (q - 1) ≤ q * q := Nat.mul_le_mul_left q (Nat.sub_le q 1)
            _ = q ^ 2 := (sq q).symm
      · rw [Finset.sum_singleton] at hcancel ⊢
        exact hcancel
    · -- Odd prime power q ≥ 5: apply unetun!
      have hq5 : 5 ≤ q := by
        have hp3 : 3 ≤ p := by have := hp.two_le; omega
        by_contra h
        have hq4' : q = 4 := by omega
        have h2 : 2 ∣ p ^ ν := by dsimp [q] at hq4'; omega
        have h2p : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow h2
        have hp2eq : 2 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2p
        omega
      set a : ZMod p := (r.num : ZMod p) * ((r.den / q : ℕ) : ZMod p)⁻¹
      obtain ⟨m₁, m₂, hlt, h5, hm2lt, hnd1, hnd2, hsum⟩ := unetun hp hp2 hν hq5 a
      have hm1_pos : 0 < m₁ := by omega
      have hm2_pos : 0 < m₂ := by omega
      have hm1_P : PStar m₁ < q := lt_of_le_of_lt (PStar_le_self _) (by omega)
      have hm2_P : PStar m₂ < q := lt_of_le_of_lt (PStar_le_self _) (by omega)
      set K : Finset ℕ := {m₁, m₂}
      have hK_sum : ∑ m ∈ K, (m : ZMod p)⁻¹ = a := by
        dsimp [K]; rw [Finset.sum_pair hlt.ne]; exact hsum
      have hcancel := PStar_sub_sum_cancel hp hν hPr hdvd (K := K)
        (fun m hm => by
          rcases Finset.mem_insert.mp hm with rfl | hm2
          · exact ⟨hm1_pos, hnd1, hm1_P⟩
          · rw [Finset.mem_singleton.mp hm2]; exact ⟨hm2_pos, hnd2, hm2_P⟩)
        hK_sum
      set U : Finset ℕ := {q * m₁, q * m₂}
      have hU_sum : ∑ n ∈ U, (1 : ℚ) / (n : ℚ) = ∑ m ∈ K, (1 : ℚ) / ((q * m : ℕ) : ℚ) := by
        have hne : q * m₁ ≠ q * m₂ := fun h => hlt.ne (Nat.eq_of_mul_eq_mul_left hq_pos h)
        dsimp [U, K]
        rw [Finset.sum_pair hne, Finset.sum_pair hlt.ne]
      refine ⟨U, ?_, Finset.card_le_two, by rw [hU_sum]; exact hcancel⟩
      · intro n hn
        rcases Finset.mem_insert.mp hn with rfl | hn2
        · refine ⟨?_, ?_, PStar_mul_prime_pow_eq hp hν hm1_pos hnd1 hm1_P⟩
          · calc q ^ 2 = q * q := sq q
              _ ≤ q * (5 * m₁) := Nat.mul_le_mul_left q h5
              _ = 5 * (q * m₁) := by ring
          · calc q * m₁ ≤ q * q := Nat.mul_le_mul_left q (by omega)
              _ = q ^ 2 := (sq q).symm
        · rw [Finset.mem_singleton.mp hn2]
          refine ⟨?_, ?_, PStar_mul_prime_pow_eq hp hν hm2_pos hnd2 hm2_P⟩
          · calc q ^ 2 = q * q := sq q
              _ ≤ q * (5 * m₂) := Nat.mul_le_mul_left q (by omega)
              _ = 5 * (q * m₂) := by ring
          · calc q * m₂ ≤ q * q := Nat.mul_le_mul_left q hm2lt.le
              _ = q ^ 2 := (sq q).symm
  · -- q ∤ r.den: take U = ∅!
    refine ⟨∅, by simp, by simp, ?_⟩
    simp only [Finset.sum_empty, sub_zero]
    by_contra hge
    have heq : PStar r.den = q := by omega
    have hr1 : 1 < r.den := by
      by_contra hle1
      have h1 : r.den = 1 := by have := r.den_pos; omega
      rw [h1, PStar_one] at heq; omega
    obtain ⟨p', ν', _, _, hpeq, hdvd', _⟩ := exists_prime_pow_eq_PStar hr1
    rw [heq] at hpeq
    exact hdvd (hpeq ▸ hdvd')

/-- `PStar (Nat.lcmUpto m) ≤ m` for all `m ≥ 1`. -/
lemma PStar_lcmUpto_le {m : ℕ} (hm : 1 ≤ m) : PStar (Nat.lcmUpto m) ≤ m := by
  rw [PStar_le_iff (Nat.lcmUpto_pos m) hm]
  intro p k hp hpk
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using hm
  · have hle : k ≤ (Nat.lcmUpto m).factorization p :=
      (hp.pow_dvd_iff_le_factorization (Nat.lcmUpto_ne_zero m)).mp hpk
    rw [Nat.factorization_lcmUpto m hp] at hle
    exact (Nat.pow_le_pow_right hp.pos hle).trans (Nat.pow_log_le_self p (by omega))

/-- Recursion for `Nat.lcmUpto`: at a prime power `q = p^ν ≥ 2`,
`lcmUpto q = p * lcmUpto (q - 1)`. -/
lemma lcmUpto_prime_pow {p ν : ℕ} (hp : p.Prime) (hν : 1 ≤ ν) :
    Nat.lcmUpto (p ^ ν) = p * Nat.lcmUpto (p ^ ν - 1) := by
  have hq2 : 2 ≤ p ^ ν := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  apply Nat.eq_of_factorization_eq (Nat.lcmUpto_ne_zero _)
    (mul_ne_zero hp.ne_zero (Nat.lcmUpto_ne_zero _))
  intro r
  by_cases hr : r.Prime
  · rw [Nat.factorization_mul hp.ne_zero (Nat.lcmUpto_ne_zero _), Finsupp.add_apply,
      Nat.factorization_lcmUpto _ hr, Nat.factorization_lcmUpto _ hr]
    by_cases hrp : r = p
    · subst r
      rw [hp.factorization_self]
      have h1 : Nat.log p (p ^ ν) = ν := Nat.log_pow hp.one_lt ν
      have h2 : Nat.log p (p ^ ν - 1) = ν - 1 := by
        apply le_antisymm
        · by_contra hc
          push Not at hc
          have hge : ν ≤ Nat.log p (p ^ ν - 1) := by omega
          have hpow : p ^ ν ≤ p ^ ν - 1 :=
            (Nat.pow_le_pow_right hp.pos hge).trans (Nat.pow_log_le_self p (by omega))
          omega
        · exact Nat.le_log_of_pow_le hp.one_lt (by
            have hlt : p ^ (ν - 1) < p ^ ν := Nat.pow_lt_pow_right hp.one_lt (by omega)
            omega)
      omega
    · have h0 : p.factorization r = 0 := by
        rw [hp.factorization]; simp [hrp]
      rw [h0, zero_add]
      apply le_antisymm
      · have hle : r ^ Nat.log r (p ^ ν) ≤ p ^ ν := Nat.pow_log_le_self r (by omega)
        have hne : r ^ Nat.log r (p ^ ν) ≠ p ^ ν := by
          intro heq
          have hr_dvd : r ∣ p ^ ν := by
            rcases Nat.eq_zero_or_pos (Nat.log r (p ^ ν)) with h0' | hpos
            · rw [h0', pow_zero] at heq; omega
            · exact heq ▸ dvd_pow_self r hpos.ne'
          exact hrp ((Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow hr_dvd))
        exact Nat.le_log_of_pow_le hr.one_lt (by omega)
      · exact Nat.log_mono_right (Nat.sub_le _ _)
  · simp [Nat.factorization_eq_zero_of_not_prime _ hr]

/-- Lemma `smalllem` (Martin 2000, Lemma 5.3): for any prime power `q = p^ν ≥ 2` and `r : ℚ`
with `PStar r.den ≤ q` and `q ∣ r.den`, there exists `n : ℕ` with:
(i) `lcmUpto q ≤ (p - 1) * n` and `n ≤ lcmUpto q`,
(ii) `PStar n = q`,
(iii) `PStar (r - 1 / n).den < q`. -/
lemma smalllem {p ν : ℕ} {r : ℚ} (hp : p.Prime) (hν : 1 ≤ ν)
    (hPr : PStar r.den ≤ p ^ ν) (hdvd : p ^ ν ∣ r.den) :
    ∃ n : ℕ, 0 < n ∧
      Nat.lcmUpto (p ^ ν) ≤ (p - 1) * n ∧
      n ≤ Nat.lcmUpto (p ^ ν) ∧
      PStar n = p ^ ν ∧
      PStar (r - (1 : ℚ) / (n : ℚ)).den < p ^ ν := by
  have : Fact p.Prime := ⟨hp⟩
  set q : ℕ := p ^ ν
  have hq_pos : 0 < q := pow_pos hp.pos ν
  have hq_ge_p : p ≤ q := Nat.le_self_pow (by omega) p
  set L : ℕ := Nat.lcmUpto q
  have hL_pos : 0 < L := Nat.lcmUpto_pos q
  have hqL : q ∣ L := by
    rw [hp.pow_dvd_iff_le_factorization hL_pos.ne', Nat.factorization_lcmUpto q hp,
      Nat.log_pow hp.one_lt ν]
  have hLq_ndvd : ¬ p ∣ L / q := by
    intro h
    have hpow : p ^ (ν + 1) ∣ L := by
      rw [← Nat.mul_div_cancel' hqL, pow_succ]; exact mul_dvd_mul_left q h
    have hle := (hp.pow_dvd_iff_le_factorization hL_pos.ne').mp hpow
    rw [Nat.factorization_lcmUpto q hp, Nat.log_pow hp.one_lt ν] at hle
    omega
  have hd₀_ndvd : ¬ p ∣ r.den / q := by
    intro h
    have hpow : p ^ (ν + 1) ∣ r.den := by
      rw [← Nat.mul_div_cancel' hdvd, pow_succ]; exact mul_dvd_mul_left q h
    have hle := prime_pow_dvd_le_PStar r.den_pos hp hpow
    have hlt : p ^ ν < p ^ (ν + 1) := Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self ν)
    omega
  have hnum_ndvd : (r.num : ZMod p) ≠ 0 := by
    intro h
    have hpd : (p : ℤ) ∣ r.num := (ZMod.intCast_zmod_eq_zero_iff_dvd r.num p).mp h
    have hpnum : p ∣ r.num.natAbs := Int.natCast_dvd.mp hpd
    have hpden : p ∣ r.den := dvd_trans (dvd_pow_self p (by omega)) hdvd
    have hpg : p ∣ Nat.gcd r.num.natAbs r.den := Nat.dvd_gcd hpnum hpden
    rw [r.reduced] at hpg
    have hple1 : p ≤ 1 := Nat.le_of_dvd (by norm_num) hpg
    have := hp.two_le; omega
  set c : ZMod p := (r.num : ZMod p) * ((L / q : ℕ) : ZMod p) * ((r.den / q : ℕ) : ZMod p)⁻¹
  have hc_ne0 : c ≠ 0 := by
    have h1 : ((L / q : ℕ) : ZMod p) ≠ 0 := fun h => hLq_ndvd ((ZMod.natCast_eq_zero_iff _ p).mp h)
    have h2 : ((r.den / q : ℕ) : ZMod p) ≠ 0 := fun h => hd₀_ndvd ((ZMod.natCast_eq_zero_iff _ p).mp h)
    exact mul_ne_zero (mul_ne_zero hnum_ndvd h1) (inv_ne_zero h2)
  set a : ℕ := c.val with hadef
  have ha_pos : 1 ≤ a := by
    by_contra h0
    have ha0 : a = 0 := by omega
    rw [hadef] at ha0
    apply hc_ne0
    rw [← ZMod.natCast_zmod_val c, ha0]; simp
  have ha_lt : a < p := ZMod.val_lt c
  -- Since 1 ≤ a < p ≤ q, we have a ∣ L = lcmUpto q!
  have ha_dvd_L : a ∣ L := by
    rw [← Nat.factorization_le_iff_dvd (by omega) hL_pos.ne']
    intro r
    by_cases hr : r.Prime
    · rw [Nat.factorization_lcmUpto q hr]
      exact Nat.le_log_of_pow_le hr.one_lt
        ((Nat.le_of_dvd (by omega) (Nat.ordProj_dvd a r)).trans (by omega))
    · simp [Nat.factorization_eq_zero_of_not_prime _ hr]
  set n : ℕ := L / a
  have han : a * n = L := Nat.mul_div_cancel' ha_dvd_L
  have hn_pos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, mul_zero] at han; omega
    · exact hpos
  have ha_cop_q : Nat.Coprime a q :=
    ((hp.coprime_iff_not_dvd.mpr (fun h => by have := Nat.le_of_dvd (by omega) h; omega)).symm).pow_right ν
  have hq_dvd_n : q ∣ n := ha_cop_q.symm.dvd_of_dvd_mul_left (han.symm ▸ hqL)
  set m : ℕ := n / q
  have hqm : q * m = n := Nat.mul_div_cancel' hq_dvd_n
  have hm_pos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0, mul_zero] at hqm; omega
    · exact hpos
  have ham_eq : a * m = L / q := by
    apply Nat.eq_of_mul_eq_mul_left hq_pos
    calc q * (a * m) = a * (q * m) := by ring
      _ = a * n := by rw [hqm]
      _ = L := han
      _ = q * (L / q) := (Nat.mul_div_cancel' hqL).symm
  have hm_ndvd : ¬ p ∣ m := fun h => hLq_ndvd (ham_eq ▸ dvd_mul_of_dvd_right h a)
  have hPn_le : PStar n ≤ q :=
    (PStar_dvd_le hn_pos hL_pos ⟨a, by linarith⟩).trans (PStar_lcmUpto_le (by omega))
  have hPn_eq : PStar n = q :=
    le_antisymm hPn_le (prime_pow_dvd_le_PStar hn_pos hp hq_dvd_n)
  have hm_PStar : PStar m < q := by
    have hle : PStar m ≤ q := (PStar_dvd_le hm_pos hn_pos ⟨q, by rw [mul_comm, hqm]⟩).trans hPn_le
    by_contra hge
    have heq : PStar m = q := by omega
    have hm1 : 1 < m := by
      by_contra h1; have : m = 1 := by omega
      rw [this, PStar_one] at heq; have := hp.two_le; omega
    obtain ⟨_, _, _, _, hpeq, hdvd', _⟩ := exists_prime_pow_eq_PStar hm1
    rw [heq] at hpeq
    exact hm_ndvd (dvd_trans (dvd_pow_self p (by omega)) (hpeq ▸ hdvd'))
  have hcong : ∑ k ∈ ({m} : Finset ℕ), (k : ZMod p)⁻¹ =
      (r.num : ZMod p) * ((r.den / q : ℕ) : ZMod p)⁻¹ := by
    simp only [Finset.sum_singleton]
    have hm0 : (m : ZMod p) ≠ 0 := fun h => hm_ndvd ((ZMod.natCast_eq_zero_iff m p).mp h)
    have hLq0 : ((L / q : ℕ) : ZMod p) ≠ 0 := fun h => hLq_ndvd ((ZMod.natCast_eq_zero_iff _ p).mp h)
    have hamZ : (a : ZMod p) * (m : ZMod p) = ((L / q : ℕ) : ZMod p) := by
      rw [← Nat.cast_mul, ham_eq]
    have haZ : (a : ZMod p) = c := ZMod.natCast_zmod_val c
    rw [haZ] at hamZ
    apply mul_left_cancel₀ hLq0
    apply mul_right_cancel₀ hm0
    calc ((L / q : ℕ) : ZMod p) * (m : ZMod p)⁻¹ * (m : ZMod p)
        = ((L / q : ℕ) : ZMod p) := by rw [mul_assoc, inv_mul_cancel₀ hm0, mul_one]
      _ = c * (m : ZMod p) := hamZ.symm
      _ = ((L / q : ℕ) : ZMod p) * ((r.num : ZMod p) * ((r.den / q : ℕ) : ZMod p)⁻¹) * (m : ZMod p) := by
          dsimp [c]; ring
  have hcancel := PStar_sub_sum_cancel hp hν hPr hdvd (K := {m})
    (fun k hk => by rw [Finset.mem_singleton.mp hk]; exact ⟨hm_pos, hm_ndvd, hm_PStar⟩)
    hcong
  rw [Finset.sum_singleton, hqm] at hcancel
  refine ⟨n, hn_pos, ?_, ?_, hPn_eq, hcancel⟩
  · calc L = a * n := han.symm
      _ ≤ (p - 1) * n := Nat.mul_le_mul_right n (by omega)
  · exact Nat.div_le_self L a

/-- Monotonicity of `Nat.lcmUpto`. -/
lemma lcmUpto_mono {a b : ℕ} (hab : a ≤ b) : Nat.lcmUpto a ≤ Nat.lcmUpto b := by
  have hdvd : Nat.lcmUpto a ∣ Nat.lcmUpto b := by
    rw [← Nat.factorization_le_iff_dvd (Nat.lcmUpto_ne_zero a) (Nat.lcmUpto_ne_zero b)]
    intro p
    by_cases hp : p.Prime
    · rw [Nat.factorization_lcmUpto a hp, Nat.factorization_lcmUpto b hp]
      exact Nat.log_mono_right hab
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  exact Nat.le_of_dvd (Nat.lcmUpto_pos b) hdvd

/-- `Nat.lcmUpto m ≤ y ^ 2` whenever `1 ≤ m` and `3 * m ≤ Real.log y` (`y ≥ 1`). -/
lemma lcmUpto_le_sq {m y : ℕ} (hm : 1 ≤ m) (hy : 1 ≤ y) (hmy : 3 * (m : ℝ) ≤ Real.log (y : ℝ)) :
    Nat.lcmUpto m ≤ y ^ 2 := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hypos : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy
  have hlog : Real.log (Nat.lcmUpto m : ℝ) ≤ Real.log ((y ^ 2 : ℕ) : ℝ) := by
    rw [← Chebyshev.psi_eq_log_lcmUpto m]
    have hth := Chebyshev.theta_le_log4_mul_x hmpos.le
    have hsub := Chebyshev.psi_sub_theta_le hmR
    have hlog4 : Real.log (4 : ℝ) ≤ 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]
      push_cast; linarith [Real.log_two_lt_d9]
    have hlogm : Real.log (m : ℝ) ≤ 2 * Real.sqrt (m : ℝ) := by
      have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hmpos)
      rw [Real.log_sqrt hmpos.le] at h1
      linarith
    have hsq : Real.sqrt (m : ℝ) * Real.log (m : ℝ) ≤ 2 * (m : ℝ) := by
      have h1 := mul_le_mul_of_nonneg_left hlogm (Real.sqrt_nonneg (m : ℝ))
      have h2 : Real.sqrt (m : ℝ) * (2 * Real.sqrt (m : ℝ)) = 2 * (m : ℝ) := by
        have hs := Real.mul_self_sqrt hmpos.le
        linear_combination 2 * hs
      linarith
    have hpsi : Chebyshev.psi (m : ℝ) ≤ 6 * (m : ℝ) := by nlinarith
    have hlogy2 : Real.log ((y ^ 2 : ℕ) : ℝ) = 2 * Real.log (y : ℝ) := by
      rw [Nat.cast_pow, Real.log_pow]; norm_num
    linarith
  have hR : (Nat.lcmUpto m : ℝ) ≤ ((y ^ 2 : ℕ) : ℝ) :=
    (Real.log_le_log_iff (by exact_mod_cast Nat.lcmUpto_pos m) (by positivity)).mp hlog
  exact_mod_cast hR

/-- Martin's Proposition `smallprop` (without cardinality adjustment):
for `y ≥ 10000` and rational `r` with `PStar r.den ≤ y`, `40 / log y < r`, and `r < 1`,
there exists a finite set `S ⊆ [1, y^2]` with `∑ n ∈ S, (1 : ℚ) / n = r`. -/
lemma small_prop {y : ℕ} {r : ℚ} (hy : 10000 ≤ y)
    (hP : PStar r.den ≤ y)
    (hr_lo : 40 / Real.log (y : ℝ) < (r : ℝ))
    (hr_hi : (r : ℝ) < 1) :
    ∃ S : Finset ℕ, (∀ n ∈ S, 1 ≤ n ∧ n ≤ y ^ 2) ∧ ∑ n ∈ S, (1 : ℚ) / (n : ℚ) = r := by
  have hyR : (10000 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hypos : (0 : ℝ) < (y : ℝ) := by linarith
  have hlogy_ge : (9 : ℝ) < Real.log (y : ℝ) := by
    have h1 : (2 : ℝ) ^ (13 : ℕ) < (y : ℝ) := by norm_num; linarith
    have h2 := Real.log_lt_log (by positivity) h1
    rw [Real.log_pow] at h2
    have := Real.log_two_gt_d9
    norm_num at h2
    linarith
  set y' : ℕ := ⌊Real.log (y : ℝ) / 3⌋₊ with hy'def
  have hy'_ge3 : 3 ≤ y' := Nat.le_floor (by push_cast; linarith)
  have hy'_le_log : 3 * (y' : ℝ) ≤ Real.log (y : ℝ) := by
    have h1 : (y' : ℝ) ≤ Real.log (y : ℝ) / 3 := Nat.floor_le (by positivity)
    linarith
  have hy'_ge_log4 : Real.log (y : ℝ) / 4 ≤ (y' : ℝ) := by
    have h1 : Real.log (y : ℝ) / 3 - 1 < (y' : ℝ) := Nat.sub_one_lt_floor _
    -- Since log y > 9: log y / 3 - 1 > log y / 4 ↔ log y / 12 > 1 ↔ log y > 12!
    -- Wait: for y = 10000, log y ≈ 9.21, y' = 3, log y / 4 = 2.30 ≤ 3!
    -- Indeed if y' ≥ 3 and log y ≤ 12, then log y / 4 ≤ 3 ≤ y'; if log y ≥ 12, then log y / 3 - 1 ≥ log y / 4!
    by_cases h12 : Real.log (y : ℝ) ≤ 12
    · have : (3 : ℝ) ≤ (y' : ℝ) := by exact_mod_cast hy'_ge3
      linarith
    · linarith
  -- Induction on k ≤ y: eradicate all prime powers ≤ k from r!
  have hind : ∀ k : ℕ, k ≤ y → ∀ q0 : ℚ, PStar q0.den ≤ k →
      ∃ S : Finset ℕ,
        (∀ n ∈ S, 1 ≤ n ∧ n ≤ y ^ 2 ∧ PStar n ≤ k) ∧
        PStar (q0 - ∑ n ∈ S, (1 : ℚ) / (n : ℚ)).den ≤ 1 ∧
        ∑ n ∈ S, (1 : ℝ) / (n : ℝ) ≤
          (∑ m ∈ Finset.Ioc y' k, (10 : ℝ) / ((m : ℝ) ^ 2)) +
          (1 - (1 : ℝ) / (Nat.lcmUpto (min k y') : ℝ)) := by
    intro k
    induction k with
    | zero =>
      intro _ q0 hPq
      have := PStar_pos q0.den_pos
      omega
    | succ k ih =>
      intro hk1y q0 hPq
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · -- k + 1 = 1: PStar q0.den ≤ 1, take S = ∅
        refine ⟨∅, by simp, by simpa using hPq, ?_⟩
        simp only [Finset.sum_empty]
        have hI : Finset.Ioc y' 1 = ∅ := Finset.Ioc_eq_empty (by omega)
        have hm : min 1 y' = 1 := min_eq_left (by omega)
        have hl1 : Nat.lcmUpto 1 = 1 := by decide
        rw [hI, Finset.sum_empty, hm, hl1]
        norm_num
      · -- k + 1 ≥ 2
        have hstep_rhs_mono :
            (∑ m ∈ Finset.Ioc y' k, (10 : ℝ) / ((m : ℝ) ^ 2)) +
              (1 - (1 : ℝ) / (Nat.lcmUpto (min k y') : ℝ)) ≤
            (∑ m ∈ Finset.Ioc y' (k + 1), (10 : ℝ) / ((m : ℝ) ^ 2)) +
              (1 - (1 : ℝ) / (Nat.lcmUpto (min (k + 1) y') : ℝ)) := by
          have h1 : ∑ m ∈ Finset.Ioc y' k, (10 : ℝ) / ((m : ℝ) ^ 2) ≤
              ∑ m ∈ Finset.Ioc y' (k + 1), (10 : ℝ) / ((m : ℝ) ^ 2) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_right (Nat.le_succ k))
              (fun _ _ _ => by positivity)
          have h2 : (1 : ℝ) / (Nat.lcmUpto (min (k + 1) y') : ℝ) ≤
              (1 : ℝ) / (Nat.lcmUpto (min k y') : ℝ) :=
            one_div_le_one_div_of_le (by exact_mod_cast Nat.lcmUpto_pos _)
              (by exact_mod_cast lcmUpto_mono (min_le_min_right y' (Nat.le_succ k)))
          linarith
        by_cases hdiv : (k + 1) ∣ q0.den ∧ ∃ p ν : ℕ, p.Prime ∧ 1 ≤ ν ∧ p ^ ν = k + 1
        · obtain ⟨hdvd, p, ν, hp, hν, hpeq⟩ := hdiv
          by_cases hgt : y' < k + 1
          · -- Medium prime power: y' < k + 1 ≤ y (and k + 1 ≥ 4 since y' ≥ 3!)
            have hq4 : 4 ≤ p ^ ν := by omega
            obtain ⟨U, hUprop, hUcard, hUcancel⟩ := medlem hp hν hq4 (hpeq.symm ▸ hPq)
            have hPr' : PStar (q0 - ∑ n ∈ U, (1 : ℚ) / (n : ℚ)).den ≤ k := by omega
            obtain ⟨S₀, hS₀prop, hS₀end, hS₀sum⟩ := ih (by omega) _ hPr'
            have hdisj : Disjoint U S₀ := by
              rw [Finset.disjoint_left]
              intro n hnU hnS₀
              have h1 := (hUprop n hnU).2.2
              have h2 := (hS₀prop n hnS₀).2.2
              omega
            refine ⟨U ∪ S₀, ?_, ?_, ?_⟩
            · intro n hn
              rcases Finset.mem_union.mp hn with hnU | hnS₀
              · obtain ⟨h5, hle, hPn⟩ := hUprop n hnU
                have hpos : 1 ≤ n := by
                  have hq2 : 16 ≤ (p ^ ν) ^ 2 := by nlinarith
                  omega
                have hley2 : n ≤ y ^ 2 := hle.trans (Nat.pow_le_pow_left (by omega) 2)
                exact ⟨hpos, hley2, by omega⟩
              · obtain ⟨h1, h2, h3⟩ := hS₀prop n hnS₀
                exact ⟨h1, h2, by omega⟩
            · rw [Finset.sum_union hdisj, sub_add_eq_sub_sub]
              exact hS₀end
            · rw [Finset.sum_union hdisj]
              have hUsum : ∑ n ∈ U, (1 : ℝ) / (n : ℝ) ≤ (10 : ℝ) / (((k + 1 : ℕ) : ℝ) ^ 2) := by
                calc ∑ n ∈ U, (1 : ℝ) / (n : ℝ)
                    ≤ ∑ _n ∈ U, (5 : ℝ) / (((k + 1 : ℕ) : ℝ) ^ 2) := by
                      apply Finset.sum_le_sum
                      intro n hn
                      have h5 := (hUprop n hn).1
                      have h5R : (((k + 1 : ℕ) : ℝ) ^ 2) ≤ 5 * (n : ℝ) := by
                        rw [← hpeq]; exact_mod_cast h5
                      have hn_pos : (0 : ℝ) < (n : ℝ) := by
                        have hq2 : 16 ≤ (p ^ ν) ^ 2 := by nlinarith
                        exact_mod_cast (by omega : 0 < n)
                      rw [div_le_div_iff₀ hn_pos (by positivity)]
                      linarith
                  _ = (U.card : ℝ) * ((5 : ℝ) / (((k + 1 : ℕ) : ℝ) ^ 2)) := by simp
                  _ ≤ 2 * ((5 : ℝ) / (((k + 1 : ℕ) : ℝ) ^ 2)) :=
                      mul_le_mul_of_nonneg_right (by exact_mod_cast hUcard) (by positivity)
                  _ = (10 : ℝ) / (((k + 1 : ℕ) : ℝ) ^ 2) := by ring
              have hIoc_eq : Finset.Ioc y' (k + 1) = insert (k + 1) (Finset.Ioc y' k) := by
                ext m; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
              have hmin_eq : min (k + 1) y' = min k y' := by omega
              rw [hIoc_eq, Finset.sum_insert (by simp), hmin_eq]
              linarith
          · -- Small prime power: 2 ≤ k + 1 ≤ y'
            push Not at hgt
            obtain ⟨n, hn_pos, hLn, hnL, hPn, hncancel⟩ := smalllem hp hν (hpeq.symm ▸ hPq) (hpeq.symm ▸ hdvd)
            have hPr' : PStar (q0 - (1 : ℚ) / (n : ℚ)).den ≤ k := by omega
            obtain ⟨S₀, hS₀prop, hS₀end, hS₀sum⟩ := ih (by omega) _ hPr'
            have hn_notMem : n ∉ S₀ := by
              intro hmem
              have h2 := (hS₀prop n hmem).2.2
              omega
            have hny2 : n ≤ y ^ 2 := by
              have h3le : 3 * ((k + 1 : ℕ) : ℝ) ≤ Real.log (y : ℝ) :=
                le_trans (by exact_mod_cast (show 3 * (k + 1) ≤ 3 * y' by omega)) hy'_le_log
              exact (hpeq ▸ hnL).trans (lcmUpto_le_sq (by omega) (by omega) h3le)
            refine ⟨insert n S₀, ?_, ?_, ?_⟩
            · intro m hm
              rcases Finset.mem_insert.mp hm with rfl | hmS₀
              · exact ⟨hn_pos, hny2, by omega⟩
              · obtain ⟨h1, h2, h3⟩ := hS₀prop m hmS₀
                exact ⟨h1, h2, by omega⟩
            · rw [Finset.sum_insert hn_notMem, sub_add_eq_sub_sub]
              exact hS₀end
            · rw [Finset.sum_insert hn_notMem]
              have hI1 : Finset.Ioc y' k = ∅ := Finset.Ioc_eq_empty (by omega)
              have hI2 : Finset.Ioc y' (k + 1) = ∅ := Finset.Ioc_eq_empty (by omega)
              have hm1 : min k y' = k := min_eq_left (by omega)
              have hm2 : min (k + 1) y' = k + 1 := min_eq_left hgt
              rw [hI1, Finset.sum_empty, zero_add, hm1] at hS₀sum
              rw [hI2, Finset.sum_empty, zero_add, hm2]
              have hlcm_rec : Nat.lcmUpto (k + 1) = p * Nat.lcmUpto k := by
                have h1 := lcmUpto_prime_pow hp hν
                rw [hpeq] at h1
                simpa using h1
              have hinv_le : (1 : ℝ) / (n : ℝ) ≤
                  (1 : ℝ) / (Nat.lcmUpto k : ℝ) - (1 : ℝ) / (Nat.lcmUpto (k + 1) : ℝ) := by
                have hL1pos : (0 : ℝ) < (Nat.lcmUpto k : ℝ) := by exact_mod_cast Nat.lcmUpto_pos k
                have hL2pos : (0 : ℝ) < (Nat.lcmUpto (k + 1) : ℝ) := by exact_mod_cast Nat.lcmUpto_pos (k + 1)
                have hrecR : (Nat.lcmUpto (k + 1) : ℝ) = (p : ℝ) * (Nat.lcmUpto k : ℝ) := by
                  exact_mod_cast hlcm_rec
                have hdiff : (1 : ℝ) / (Nat.lcmUpto k : ℝ) - (1 : ℝ) / (Nat.lcmUpto (k + 1) : ℝ) =
                    ((p - 1 : ℕ) : ℝ) / (Nat.lcmUpto (k + 1) : ℝ) := by
                  rw [Nat.cast_sub hp.pos, Nat.cast_one, hrecR]
                  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
                  field_simp [hL1pos.ne', hp0]
                rw [hdiff, div_le_div_iff₀ (by exact_mod_cast hn_pos) hL2pos, one_mul]
                rw [hpeq] at hLn
                exact_mod_cast hLn
              linarith
        · -- Either ¬ (k + 1) ∣ q0.den OR k + 1 is not a prime power → PStar q0.den ≤ k!
          have hPqk : PStar q0.den ≤ k := by
            by_contra hgt
            have heq : PStar q0.den = k + 1 := by omega
            have hq1 : 1 < q0.den := by
              by_contra hle1
              have : q0.den = 1 := by have := q0.den_pos; omega
              rw [this, PStar_one] at heq; omega
            obtain ⟨p, ν, hp, hν, hpeq, hdvd, _⟩ := exists_prime_pow_eq_PStar hq1
            rw [heq] at hpeq
            exact hdiv ⟨hpeq ▸ hdvd, p, ν, hp, hν, hpeq⟩
          obtain ⟨S₀, hS₀prop, hS₀end, hS₀sum⟩ := ih (by omega) q0 hPqk
          refine ⟨S₀, fun n hn => by obtain ⟨h1, h2, h3⟩ := hS₀prop n hn; exact ⟨h1, h2, by omega⟩,
            hS₀end, hS₀sum.trans hstep_rhs_mono⟩
  -- Apply hind at k = y!
  obtain ⟨S, hSprop, hSend, hSsum⟩ := hind y le_rfl r hP
  -- Bound ∑ m ∈ Ioc y' y, 10 / m^2 ≤ 10 / y' ≤ 40 / log y
  have htail : ∑ m ∈ Finset.Ioc y' y, (10 : ℝ) / ((m : ℝ) ^ 2) ≤ 40 / Real.log (y : ℝ) := by
    have htele : ∑ m ∈ Finset.Ioc y' y, (10 : ℝ) / ((m : ℝ) ^ 2) ≤
        10 * ∑ m ∈ Finset.Ioc y' y, ((1 : ℝ) / ((m : ℝ) - 1) - (1 : ℝ) / (m : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro m hm
      have hm2 : 2 ≤ m := by have := (Finset.mem_Ioc.mp hm).1; omega
      have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
      have h1 : (1 : ℝ) / ((m : ℝ) - 1) - (1 : ℝ) / (m : ℝ) = 1 / ((m : ℝ) * ((m : ℝ) - 1)) := by
        field_simp [show (m : ℝ) ≠ 0 by linarith, show (m : ℝ) - 1 ≠ 0 by linarith]; ring
      rw [h1, show 10 * (1 / ((m : ℝ) * ((m : ℝ) - 1))) = 10 / ((m : ℝ) * ((m : ℝ) - 1)) by ring]
      apply div_le_div_of_nonneg_left (by norm_num) (by nlinarith) (by nlinarith)
    have htele_val : ∑ m ∈ Finset.Ioc y' y,
        ((1 : ℝ) / ((m : ℝ) - 1) - (1 : ℝ) / (m : ℝ)) ≤ 1 / (y' : ℝ) := by
      by_cases hy'y : y' ≤ y
      · have hreidx : ∑ m ∈ Finset.Ioc y' y, ((1 : ℝ) / ((m : ℝ) - 1) - (1 : ℝ) / (m : ℝ)) =
            ∑ j ∈ Finset.range (y - y'),
              ((1 : ℝ) / ((y' + j : ℕ) : ℝ) - (1 : ℝ) / ((y' + (j + 1) : ℕ) : ℝ)) := by
          refine Finset.sum_bij (fun m _ => m - (y' + 1)) ?_ ?_ ?_ ?_
          · intro m hm; rw [Finset.mem_Ioc] at hm; rw [Finset.mem_range]; omega
          · intro m₁ hm₁ m₂ hm₂ h; rw [Finset.mem_Ioc] at hm₁ hm₂; omega
          · intro j hj; rw [Finset.mem_range] at hj
            exact ⟨y' + 1 + j, Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, by omega⟩
          · intro m hm; rw [Finset.mem_Ioc] at hm
            have e1 : y' + (m - (y' + 1)) = m - 1 := by omega
            have e2 : y' + (m - (y' + 1) + 1) = m := by omega
            rw [e1, e2, Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
        rw [hreidx]
        have ht : ∀ n : ℕ, ∑ j ∈ Finset.range n,
            ((1 : ℝ) / ((y' + j : ℕ) : ℝ) - (1 : ℝ) / ((y' + (j + 1) : ℕ) : ℝ)) =
            (1 : ℝ) / (y' : ℝ) - (1 : ℝ) / ((y' + n : ℕ) : ℝ) := by
          intro n; induction n with
          | zero => simp
          | succ n ih => rw [Finset.sum_range_succ, ih]; ring
        rw [ht]
        have : (0 : ℝ) ≤ 1 / ((y' + (y - y') : ℕ) : ℝ) := by positivity
        linarith
      · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]; positivity
    have h10y' : 10 * (1 / (y' : ℝ)) ≤ 40 / Real.log (y : ℝ) := by
      calc 10 * (1 / (y' : ℝ)) = 10 / (y' : ℝ) := by ring
        _ ≤ 10 / (Real.log (y : ℝ) / 4) :=
            div_le_div_of_nonneg_left (by norm_num) (by positivity) hy'_ge_log4
        _ = 40 / Real.log (y : ℝ) := by field_simp; ring
    linarith
  -- Show rem := r - ∑ n ∈ S, 1/n equals 0!
  set rem : ℚ := r - ∑ n ∈ S, (1 : ℚ) / (n : ℚ)
  have hden1 : rem.den = 1 := by
    have hpos := rem.den_pos
    have hP1 : PStar rem.den = 1 := by have := PStar_pos hpos; omega
    exact (PStar_eq_one_iff hpos).mp hP1
  have hrem_int : rem = (rem.num : ℚ) := by
    have h := Rat.mul_den_eq_num rem
    rw [hden1, Nat.cast_one, mul_one] at h
    exact h
  have hremR : (rem : ℝ) = (r : ℝ) - ∑ n ∈ S, (1 : ℝ) / (n : ℝ) := by
    dsimp [rem]; push_cast; rfl
  have hrem_lt1 : (rem : ℝ) < 1 := by
    have hnn : 0 ≤ ∑ n ∈ S, (1 : ℝ) / (n : ℝ) := Finset.sum_nonneg (fun _ _ => by positivity)
    linarith
  have hrem_gt_neg1 : (-1 : ℝ) < (rem : ℝ) := by
    have hLpos : (0 : ℝ) < 1 / (Nat.lcmUpto (min y y') : ℝ) := by
      have : (0 : ℝ) < (Nat.lcmUpto (min y y') : ℝ) := by exact_mod_cast Nat.lcmUpto_pos _
      positivity
    linarith
  have hnum_eq0 : rem.num = 0 := by
    have h1 : (rem.num : ℝ) = (rem : ℝ) := by rw [hrem_int]; norm_cast
    have hlt : (rem.num : ℝ) < 1 := by linarith
    have hgt : (-1 : ℝ) < (rem.num : ℝ) := by linarith
    have hltZ : rem.num < 1 := by exact_mod_cast hlt
    have hgtZ : -1 < rem.num := by exact_mod_cast hgt
    omega
  have hrem0 : rem = 0 := by rw [hrem_int, hnum_eq0]; simp
  refine ⟨S, fun n hn => ⟨(hSprop n hn).1, (hSprop n hn).2.1⟩, ?_⟩
  exact (sub_eq_zero.mp hrem0).symm

end E292Part3


namespace E292Part4

open Finset Filter Real E292Part1 E292Part2 E292Part3
open scoped Classical

/- ## Part 7: Martin's `biglem` (k = 2 semiprimes) and `big_prop` -/

/-- AM-GM integral bound: `∑_{n=1}^M n^(-2/3) ≤ 3 * M^(1/3)`. -/
lemma sum_rpow_neg_two_thirds (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M, ((n : ℝ) ^ ((2 : ℝ) / 3))⁻¹ ≤ 3 * (M : ℝ) ^ ((1 : ℝ) / 3) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hIcc : Finset.Icc 1 (M + 1) = insert (M + 1) (Finset.Icc 1 M) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.sum_insert (by simp)]
    have hstep : (((M + 1 : ℕ) : ℝ) ^ ((2 : ℝ) / 3))⁻¹ ≤
        3 * ((M + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) - 3 * (M : ℝ) ^ ((1 : ℝ) / 3) := by
      set a : ℝ := (M : ℝ) ^ ((1 : ℝ) / 3)
      set b : ℝ := ((M + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 3)
      have ha0 : 0 ≤ a := by positivity
      have hbpos : 0 < b := Real.rpow_pos_of_pos (by positivity) _
      have ha3 : a ^ 3 = (M : ℝ) := by
        dsimp [a]
        rcases Nat.eq_zero_or_pos M with rfl | hM
        · simp
        · rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
      have hb3 : b ^ 3 = (M : ℝ) + 1 := by
        dsimp [b]
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      have hb2 : ((M + 1 : ℕ) : ℝ) ^ ((2 : ℝ) / 3) = b ^ 2 := by
        dsimp [b]
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      rw [hb2, inv_le_iff_one_le_mul₀ (sq_pos_of_pos hbpos)]
      -- 1 ≤ (3 * b - 3 * a) * b^2 = 3 * b^3 - 3 * a * b^2 ↔ 3 * a * b^2 ≤ a^3 + 2 * b^3 (AM-GM!)
      have hamgm : 3 * a * b ^ 2 ≤ a ^ 3 + 2 * b ^ 3 := by
        have h1 : 0 ≤ (a - b) ^ 2 * (a + 2 * b) := mul_nonneg (sq_nonneg _) (by linarith)
        nlinarith
      nlinarith
    linarith

/-- Elementary harmonic-sum approximation on `[L, U]`:
`|∑_{n=L}^U 1/n - log(U / L)| ≤ 2 / L` for `1 ≤ L ≤ U`. -/
lemma harmonic_Icc_approx {L U : ℕ} (hL : 1 ≤ L) (hLU : L ≤ U) :
    Real.log ((U : ℝ) / (L : ℝ)) - 2 / (L : ℝ) ≤ ∑ n ∈ Finset.Icc L U, (1 : ℝ) / (n : ℝ) ∧
    ∑ n ∈ Finset.Icc L U, (1 : ℝ) / (n : ℝ) ≤ Real.log ((U : ℝ) / (L : ℝ)) + 2 / (L : ℝ) := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hUpos : (0 : ℝ) < (U : ℝ) := by exact_mod_cast (by omega : 0 < U)
  -- For any k ≥ 1: 1/(k+1) ≤ log((k+1)/k) ≤ 1/k
  have hstep_ub : ∀ k : ℕ, 1 ≤ k → Real.log (((k + 1 : ℕ) : ℝ)) - Real.log (k : ℝ) ≤ (1 : ℝ) / (k : ℝ) := by
    intro k hk
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    rw [← Real.log_div (by positivity) hkpos.ne']
    have h1 := Real.log_le_sub_one_of_pos (div_pos (by positivity : (0 : ℝ) < ((k + 1 : ℕ) : ℝ)) hkpos)
    have h2 : ((k + 1 : ℕ) : ℝ) / (k : ℝ) - 1 = 1 / (k : ℝ) := by
      push_cast; rw [div_sub_one hkpos.ne']; ring
    linarith
  have hstep_lb : ∀ k : ℕ, 1 ≤ k → (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ≤ Real.log (((k + 1 : ℕ) : ℝ)) - Real.log (k : ℝ) := by
    intro k hk
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    have hk1pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have h1 := Real.log_le_sub_one_of_pos (div_pos hkpos hk1pos)
    rw [Real.log_div hkpos.ne' hk1pos.ne'] at h1
    have h2 : (k : ℝ) / ((k + 1 : ℕ) : ℝ) - 1 = -((1 : ℝ) / ((k + 1 : ℕ) : ℝ)) := by
      have hk1' : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      push_cast; rw [div_sub_one hk1'.ne']; ring
    linarith
  have htele_log : ∀ d : ℕ, ∑ j ∈ Finset.range d, (Real.log (((L + j + 1 : ℕ) : ℝ)) - Real.log (((L + j : ℕ) : ℝ))) =
      Real.log (((L + d : ℕ) : ℝ)) - Real.log (L : ℝ) := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  set d := U - L
  have hUd : L + d = U := by omega
  have hlog_eq : Real.log ((U : ℝ) / (L : ℝ)) = Real.log (U : ℝ) - Real.log (L : ℝ) :=
    Real.log_div hUpos.ne' hLpos.ne'
  -- Reindex ∑_{n ∈ Icc L U} 1/n = ∑_{j ∈ range (d + 1)} 1/(L + j)
  have hsum_eq : ∑ n ∈ Finset.Icc L U, (1 : ℝ) / (n : ℝ) =
      ∑ j ∈ Finset.range (d + 1), (1 : ℝ) / ((L + j : ℕ) : ℝ) := by
    refine Finset.sum_bij (fun n _ => n - L) ?_ ?_ ?_ ?_
    · intro n hn; rw [Finset.mem_Icc] at hn; rw [Finset.mem_range]; omega
    · intro n₁ hn₁ n₂ hn₂ h; rw [Finset.mem_Icc] at hn₁ hn₂; omega
    · intro j hj; rw [Finset.mem_range] at hj
      exact ⟨L + j, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro n hn; rw [Finset.mem_Icc] at hn
      have : L + (n - L) = n := by omega
      rw [this]
  rw [hsum_eq, hlog_eq]
  constructor
  · have h1 : Real.log (U : ℝ) - Real.log (L : ℝ) ≤ ∑ j ∈ Finset.range d, (1 : ℝ) / ((L + j : ℕ) : ℝ) := by
      rw [← hUd, ← htele_log d]
      exact Finset.sum_le_sum (fun j _ => hstep_ub (L + j) (by omega))
    rw [Finset.sum_range_succ]
    have hnn : (0 : ℝ) ≤ 1 / ((L + d : ℕ) : ℝ) := by positivity
    have h2L : (0 : ℝ) ≤ 2 / (L : ℝ) := by positivity
    linarith
  · rw [Finset.sum_range_succ']
    have h1 : ∑ j ∈ Finset.range d, (1 : ℝ) / ((L + (j + 1) : ℕ) : ℝ) ≤
        Real.log (U : ℝ) - Real.log (L : ℝ) := by
      rw [← hUd, ← htele_log d]
      exact Finset.sum_le_sum (fun j _ => by
        have := hstep_lb (L + j) (by omega)
        simpa [Nat.add_assoc] using this)
    have h0 : (1 : ℝ) / ((L + 0 : ℕ) : ℝ) = 1 / (L : ℝ) := by simp
    rw [h0]
    have h1L : (1 : ℝ) / (L : ℝ) ≤ 2 / (L : ℝ) :=
      div_le_div_of_nonneg_right (by norm_num) hLpos.le
    linarith

/-- Martin's `biglem` (for `k = 2` semiprimes): for a large prime power `q = p^ν`, produces a set
`U ⊆ [⌈α x⌉₊, x]` of multiples of `q` with `∀ n ∈ U, PStar n = q`, `U.card ≤ C`, and
`PStar (r + ∑ n ∈ U, 1/n).den < q`. -/
lemma biglem {x p ν : ℕ} {α : ℝ} {r : ℚ}
    (hp : p.Prime) (hν : 1 ≤ ν)
    (hα_lo : 35 / 100 ≤ α) (hα_hi : α ≤ 42 / 100)
    (hPr : PStar r.den ≤ p ^ ν) (hdvd : p ^ ν ∣ r.den)
    (hx_ge : 10000 ≤ x)
    (hq_le_x : ((p ^ ν : ℕ) : ℝ) ≤ (x : ℝ))
    (hB_lo : (100000000000000 : ℝ) ≤ (x : ℝ) / ((p ^ ν : ℕ) : ℝ))
    (hB_vs_C : 101 * ((x : ℝ) / ((p ^ ν : ℕ) : ℝ)) ^ ((2 : ℝ) / 3) * (Real.log (x : ℝ)) ^ 2 + 2 ≤
        ((x : ℝ) / ((p ^ ν : ℕ) : ℝ)) / (1000 * (Real.log ((x : ℝ) / ((p ^ ν : ℕ) : ℝ))) ^ 2))
    (hp2_lt_q : 10 * Real.sqrt ((x : ℝ) / ((p ^ ν : ℕ) : ℝ)) < ((p ^ ν : ℕ) : ℝ)) :
    ∃ U : Finset ℕ,
      (∀ n ∈ U, ⌈α * (x : ℝ)⌉₊ ≤ n ∧ n ≤ x ∧ PStar n = p ^ ν) ∧
      (U.card : ℝ) ≤ 101 * ((x : ℝ) / ((p ^ ν : ℕ) : ℝ)) ^ ((2 : ℝ) / 3) * (Real.log (x : ℝ)) ^ 2 + 2 ∧
      PStar (r + ∑ n ∈ U, (1 : ℚ) / (n : ℚ)).den < p ^ ν := by
  have : Fact p.Prime := ⟨hp⟩
  set q : ℕ := p ^ ν
  have hq_pos : 0 < q := pow_pos hp.pos ν
  have hqR_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  set B : ℝ := (x : ℝ) / (q : ℝ)
  have hBpos : 0 < B := by positivity
  have hlogB_pos : 0 < Real.log B := Real.log_pos (by linarith)
  have hsqrtB_ge : (10000000 : ℝ) ≤ Real.sqrt B := by
    rw [show (10000000 : ℝ) = Real.sqrt 100000000000000 by norm_num]
    exact Real.sqrt_le_sqrt hB_lo
  -- Construct P₁ = primes in (⌊√B / 10⌋₊, ⌊√B / 3⌋₊] \ {p}
  set P₁ : Finset ℕ := ((Finset.Ioc ⌊(3 / 10 : ℝ) * (Real.sqrt B / 3)⌋₊ ⌊Real.sqrt B / 3⌋₊).filter Nat.Prime).erase p
  -- For each p₁ ∈ P₁, P₂ p₁ = primes in (⌊α * (B / p₁)⌋₊, ⌊B / p₁⌋₊] \ {p}
  let P₂ (p₁ : ℕ) : Finset ℕ := ((Finset.Ioc ⌊α * (B / (p₁ : ℝ))⌋₊ ⌊B / (p₁ : ℝ)⌋₊).filter Nat.Prime).erase p
  have h1_le_420 : (1 : ℝ) ≤ Real.sqrt B / (420 * Real.log B) := by
    rw [le_div_iff₀ (by positivity)]
    have hlogB_le_sqrt : Real.log B ≤ 4 * B ^ ((1 : ℝ) / 4) := by
      have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hBpos ((1 : ℝ) / 4))
      rw [Real.log_rpow hBpos] at h1; linarith only [h1]
    have hB14 : (3000 : ℝ) ≤ B ^ ((1 : ℝ) / 4) := by
      have h1 : (3000 : ℝ) ^ (4 : ℝ) ≤ B := by norm_num; linarith only [hB_lo]
      have h2 := Real.rpow_le_rpow (by positivity) h1 (by positivity : (0 : ℝ) ≤ 1 / 4)
      rw [← Real.rpow_mul (by positivity)] at h2; norm_num at h2; exact h2
    have hsq_eq : B ^ ((1 : ℝ) / 4) * B ^ ((1 : ℝ) / 4) = Real.sqrt B := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hBpos]; norm_num
    have h420 : 420 * Real.log B ≤ 1680 * B ^ ((1 : ℝ) / 4) := by linarith only [hlogB_le_sqrt]
    have hB14_pos : 0 < B ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hBpos ((1 : ℝ) / 4)
    nlinarith only [hB14, hsq_eq, h420, hB14_pos]
  -- Check sizes of P₁ and P₂ p₁ via prime_count_interval_ge!
  have hP₁_card : Real.sqrt B / (70 * Real.log B) ≤ (P₁.card : ℝ) := by
    have h1 := prime_count_interval_ge (α := 3 / 10) (B := Real.sqrt B / 3) (by norm_num) (by norm_num) (by linarith only [hsqrtB_ge])
    have herase : (((Finset.Ioc ⌊(3 / 10 : ℝ) * (Real.sqrt B / 3)⌋₊ ⌊Real.sqrt B / 3⌋₊).filter Nat.Prime).card : ℝ) - 1 ≤ (P₁.card : ℝ) := by
      have hcard := Finset.pred_card_le_card_erase (s := (Finset.Ioc ⌊(3 / 10 : ℝ) * (Real.sqrt B / 3)⌋₊ ⌊Real.sqrt B / 3⌋₊).filter Nat.Prime) (a := p)
      have hle : ((Finset.Ioc ⌊(3 / 10 : ℝ) * (Real.sqrt B / 3)⌋₊ ⌊Real.sqrt B / 3⌋₊).filter Nat.Prime).card ≤ P₁.card + 1 := by
        dsimp [P₁]; omega
      have h' : (((Finset.Ioc ⌊(3 / 10 : ℝ) * (Real.sqrt B / 3)⌋₊ ⌊Real.sqrt B / 3⌋₊).filter Nat.Prime).card : ℝ) ≤ (P₁.card : ℝ) + 1 := by
        exact_mod_cast hle
      linarith only [h']
    have hlog_le : Real.log (Real.sqrt B / 3) ≤ Real.log B := by
      apply Real.log_le_log (by linarith only [hsqrtB_ge])
      have hsq : Real.sqrt B ≤ B := by
        have hmul : Real.sqrt B * 1 ≤ Real.sqrt B * Real.sqrt B := mul_le_mul_of_nonneg_left (by linarith only [hsqrtB_ge]) (Real.sqrt_nonneg B)
        rw [Real.mul_self_sqrt hBpos.le] at hmul; linarith only [hmul]
      linarith only [hsq, hsqrtB_ge]
    have hlog_pos : 0 < Real.log (Real.sqrt B / 3) := Real.log_pos (by linarith only [hsqrtB_ge])
    have hdiv_ge : Real.sqrt B / (60 * Real.log B) ≤ (Real.sqrt B / 3) / (20 * Real.log (Real.sqrt B / 3)) := by
      rw [show (Real.sqrt B / 3) / (20 * Real.log (Real.sqrt B / 3)) = Real.sqrt B / (60 * Real.log (Real.sqrt B / 3)) by ring]
      exact div_le_div_of_nonneg_left (Real.sqrt_nonneg B) (by positivity) (by linarith only [hlog_le])
    have hfrac : Real.sqrt B / (70 * Real.log B) + Real.sqrt B / (420 * Real.log B) = Real.sqrt B / (60 * Real.log B) := by
      field_simp [hlogB_pos.ne']; ring
    linarith only [h1, herase, hdiv_ge, h1_le_420, hfrac]
  have hP₁_bounds : ∀ p₁ ∈ P₁, Real.sqrt B / 10 < (p₁ : ℝ) ∧ (p₁ : ℝ) ≤ Real.sqrt B / 3 ∧ p₁.Prime ∧ p₁ ≠ p := by
    intro p₁ hp₁
    rw [Finset.mem_erase, Finset.mem_filter, Finset.mem_Ioc] at hp₁
    have hlo : (3 / 10 : ℝ) * (Real.sqrt B / 3) < (p₁ : ℝ) := (Nat.floor_lt (by positivity)).mp hp₁.2.1.1
    have hhi : (p₁ : ℝ) ≤ Real.sqrt B / 3 := le_trans (by exact_mod_cast hp₁.2.1.2) (Nat.floor_le (by positivity))
    exact ⟨by linarith only [hlo], hhi, hp₁.2.2, hp₁.1⟩
  have hP₂_card : ∀ p₁ ∈ P₁, Real.sqrt B / (10 * Real.log B) ≤ ((P₂ p₁).card : ℝ) := by
    intro p₁ hp₁
    obtain ⟨hp₁_lo, hp₁_hi, hp₁_pr, _⟩ := hP₁_bounds p₁ hp₁
    have hp₁_pos : (0 : ℝ) < (p₁ : ℝ) := by linarith only [hp₁_lo, hsqrtB_ge]
    have hBp1_ge : 3 * Real.sqrt B ≤ B / (p₁ : ℝ) := by
      rw [le_div_iff₀ hp₁_pos]
      have hs := Real.mul_self_sqrt hBpos.le
      nlinarith only [hp₁_hi, hs, hsqrtB_ge]
    have h1 := prime_count_interval_ge (by linarith only [hα_lo]) (by linarith only [hα_hi]) (by linarith only [hBp1_ge, hsqrtB_ge] : 1000000 ≤ B / (p₁ : ℝ))
    have herase : (((Finset.Ioc ⌊α * (B / (p₁ : ℝ))⌋₊ ⌊B / (p₁ : ℝ)⌋₊).filter Nat.Prime).card : ℝ) - 1 ≤ ((P₂ p₁).card : ℝ) := by
      have hcard := Finset.pred_card_le_card_erase (s := (Finset.Ioc ⌊α * (B / (p₁ : ℝ))⌋₊ ⌊B / (p₁ : ℝ)⌋₊).filter Nat.Prime) (a := p)
      have hle : ((Finset.Ioc ⌊α * (B / (p₁ : ℝ))⌋₊ ⌊B / (p₁ : ℝ)⌋₊).filter Nat.Prime).card ≤ (P₂ p₁).card + 1 := by
        dsimp [P₂]; omega
      have h' : (((Finset.Ioc ⌊α * (B / (p₁ : ℝ))⌋₊ ⌊B / (p₁ : ℝ)⌋₊).filter Nat.Prime).card : ℝ) ≤ ((P₂ p₁).card : ℝ) + 1 := by
        exact_mod_cast hle
      linarith only [h']
    have hlog_le : Real.log (B / (p₁ : ℝ)) ≤ Real.log B := by
      apply Real.log_le_log (by positivity)
      exact div_le_self hBpos.le (by exact_mod_cast hp₁_pr.one_lt.le)
    have hlog_pos : 0 < Real.log (B / (p₁ : ℝ)) := Real.log_pos (by linarith only [hBp1_ge, hsqrtB_ge])
    have hdiv_ge : (3 * Real.sqrt B) / (20 * Real.log B) ≤ (B / (p₁ : ℝ)) / (20 * Real.log (B / (p₁ : ℝ))) := by
      calc (3 * Real.sqrt B) / (20 * Real.log B)
          ≤ (3 * Real.sqrt B) / (20 * Real.log (B / (p₁ : ℝ))) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith only [hlog_le])
        _ ≤ (B / (p₁ : ℝ)) / (20 * Real.log (B / (p₁ : ℝ))) :=
            div_le_div_of_nonneg_right hBp1_ge (by positivity)
    have h1_le : (1 : ℝ) ≤ Real.sqrt B / (20 * Real.log B) := by
      have h20 : Real.sqrt B / (420 * Real.log B) ≤ Real.sqrt B / (20 * Real.log B) :=
        div_le_div_of_nonneg_left (Real.sqrt_nonneg B) (by positivity) (by linarith only [hlogB_pos])
      linarith only [h1_le_420, h20]
    have hfrac : Real.sqrt B / (10 * Real.log B) + Real.sqrt B / (20 * Real.log B) =
        (3 * Real.sqrt B) / (20 * Real.log B) := by
      field_simp [hlogB_pos.ne']; ring
    linarith only [h1, herase, hdiv_ge, h1_le, hfrac]
  -- Construct M₀ = {p₁ * p₂ : p₁ ∈ P₁, p₂ ∈ P₂ p₁}
  set Pairs : Finset (Σ _ : ℕ, ℕ) := P₁.sigma P₂
  set M₀ : Finset ℕ := Pairs.image (fun z => z.1 * z.2)
  have hPair_prop : ∀ z ∈ Pairs, z.1.Prime ∧ z.2.Prime ∧ z.1 < z.2 ∧ z.1 ≠ p ∧ z.2 ≠ p ∧
      α * B < ((z.1 * z.2 : ℕ) : ℝ) ∧ ((z.1 * z.2 : ℕ) : ℝ) ≤ B ∧ (z.2 : ℝ) < (q : ℝ) := by
    intro z hz
    rw [Finset.mem_sigma] at hz
    obtain ⟨hp₁_lo, hp₁_hi, hp₁_pr, hp₁_nep⟩ := hP₁_bounds z.1 hz.1
    have hp₂ := hz.2
    rw [Finset.mem_erase, Finset.mem_filter, Finset.mem_Ioc] at hp₂
    have hp₁_pos : (0 : ℝ) < (z.1 : ℝ) := by linarith
    have hp₂_lo : α * (B / (z.1 : ℝ)) < (z.2 : ℝ) := (Nat.floor_lt (by positivity)).mp hp₂.2.1.1
    have hp₂_hi : (z.2 : ℝ) ≤ B / (z.1 : ℝ) := le_trans (by exact_mod_cast hp₂.2.1.2) (Nat.floor_le (by positivity))
    have hsq := Real.mul_self_sqrt hBpos.le
    have hlt12 : (z.1 : ℝ) < (z.2 : ℝ) := by
      have h1a : 3 * Real.sqrt B * (z.1 : ℝ) ≤ B := by nlinarith only [hp₁_hi, hsq, hsqrtB_ge]
      have h1 : 3 * α * Real.sqrt B ≤ α * (B / (z.1 : ℝ)) := by
        rw [show α * (B / (z.1 : ℝ)) = (α * B) / (z.1 : ℝ) by ring, le_div_iff₀ hp₁_pos]
        nlinarith only [h1a, hα_lo]
      nlinarith only [h1, hp₂_lo, hp₁_hi, hα_lo, hsqrtB_ge]
    have hprod_lo : α * B < (z.1 : ℝ) * (z.2 : ℝ) := by
      have := mul_lt_mul_of_pos_left hp₂_lo hp₁_pos
      rwa [show (z.1 : ℝ) * (α * (B / (z.1 : ℝ))) = α * B by field_simp] at this
    have hprod_hi : (z.1 : ℝ) * (z.2 : ℝ) ≤ B := by
      have := mul_le_mul_of_nonneg_left hp₂_hi hp₁_pos.le
      rwa [show (z.1 : ℝ) * (B / (z.1 : ℝ)) = B by field_simp] at this
    have hp2_lt : (z.2 : ℝ) < (q : ℝ) := by
      have h1 : B / (z.1 : ℝ) < 10 * Real.sqrt B := by
        rw [div_lt_iff₀ hp₁_pos]
        nlinarith only [hp₁_lo, hsq, hsqrtB_ge]
      linarith only [h1, hp₂_hi, hp2_lt_q]
    exact ⟨hp₁_pr, hp₂.2.2, by exact_mod_cast hlt12, hp₁_nep, hp₂.1,
      by push_cast; exact hprod_lo, by push_cast; exact hprod_hi, hp2_lt⟩
  -- Injectivity of z ↦ z.1 * z.2 on Pairs
  have hinj : Set.InjOn (fun z : Σ _ : ℕ, ℕ => z.1 * z.2) (Pairs : Set (Σ _ : ℕ, ℕ)) := by
    intro a ha b hb heq
    dsimp only at heq
    obtain ⟨ha1, ha2, halt, _, _, _, _, _⟩ := hPair_prop a ha
    obtain ⟨hb1, hb2, hblt, _, _, _, _, _⟩ := hPair_prop b hb
    have hd1 : a.1 ∣ b.1 * b.2 := heq ▸ dvd_mul_right a.1 a.2
    rcases ha1.dvd_mul.mp hd1 with h1 | h2
    · have e1 : a.1 = b.1 := (Nat.prime_dvd_prime_iff_eq ha1 hb1).mp h1
      have e2 : a.2 = b.2 := Nat.eq_of_mul_eq_mul_left hb1.pos (by rw [e1] at heq; exact heq)
      cases a; cases b; simp only at e1 e2; subst e1; subst e2; rfl
    · have e1 : a.1 = b.2 := (Nat.prime_dvd_prime_iff_eq ha1 hb2).mp h2
      have e2 : a.2 = b.1 := Nat.eq_of_mul_eq_mul_left hb2.pos (by rw [e1, mul_comm b.1 b.2] at heq; exact heq)
      omega
  have hM₀_card : B / (1000 * (Real.log B) ^ 2) ≤ (M₀.card : ℝ) := by
    have hcard_eq : M₀.card = Pairs.card := Finset.card_image_of_injOn hinj
    rw [hcard_eq, Finset.card_sigma, Nat.cast_sum]
    have hsum_ge : ∑ _p₁ ∈ P₁, (Real.sqrt B / (10 * Real.log B)) ≤ ∑ p₁ ∈ P₁, ((P₂ p₁).card : ℝ) :=
      Finset.sum_le_sum hP₂_card
    rw [Finset.sum_const, nsmul_eq_mul] at hsum_ge
    have hprod_ge : (Real.sqrt B / (70 * Real.log B)) * (Real.sqrt B / (10 * Real.log B)) ≤
        (P₁.card : ℝ) * (Real.sqrt B / (10 * Real.log B)) :=
      mul_le_mul_of_nonneg_right hP₁_card (by positivity)
    have hprod_eq : (Real.sqrt B / (70 * Real.log B)) * (Real.sqrt B / (10 * Real.log B)) =
        B / (700 * (Real.log B) ^ 2) := by
      have hs := Real.mul_self_sqrt hBpos.le
      rw [div_mul_div_comm, hs]
      ring
    have h700 : B / (1000 * (Real.log B) ^ 2) ≤ B / (700 * (Real.log B) ^ 2) :=
      div_le_div_of_nonneg_left hBpos.le (by positivity) (by nlinarith only [sq_pos_of_pos hlogB_pos])
    linarith only [hsum_ge, hprod_ge, hprod_eq, h700]
  -- Pick subset M ⊆ M₀ of cardinality C = ⌈101 * B^(2/3) * (log x)^2⌉₊ + 1
  set C : ℕ := ⌈101 * B ^ ((2 : ℝ) / 3) * (Real.log (x : ℝ)) ^ 2⌉₊ + 1
  have hCR_le : (C : ℝ) ≤ 101 * B ^ ((2 : ℝ) / 3) * (Real.log (x : ℝ)) ^ 2 + 2 := by
    dsimp [C]; push_cast
    linarith [Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 101 * B ^ ((2 : ℝ) / 3) * (Real.log (x : ℝ)) ^ 2)]
  have hC_le_M₀ : C ≤ M₀.card := by
    have : (C : ℝ) ≤ (M₀.card : ℝ) := hCR_le.trans (hB_vs_C.trans hM₀_card)
    exact_mod_cast this
  obtain ⟨M, hMM₀, hMcard⟩ := Finset.exists_subset_card_eq hC_le_M₀
  have hM_mem : ∀ m ∈ M, ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₁ < p₂ ∧ p₁ ≠ p ∧ p₂ ≠ p ∧
      m = p₁ * p₂ ∧ α * B < (m : ℝ) ∧ (m : ℝ) ≤ B ∧ (p₂ : ℝ) < (q : ℝ) := by
    intro m hm
    rcases Finset.mem_image.mp (hMM₀ hm) with ⟨z, hz, rfl⟩
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hPair_prop z hz
    exact ⟨z.1, z.2, h1, h2, h3, h4, h5, rfl, h6, h7, h8⟩
  have hM100 : 100 ≤ M.card := by
    rw [hMcard]
    have hlogx1 : (1 : ℝ) ≤ Real.log (x : ℝ) := by
      have h1 : (4 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 4 ≤ x)
      have h2 := Real.log_le_log (by norm_num) h1
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow] at h2
      push_cast at h2; linarith [Real.log_two_gt_d9]
    have hB1 : (1 : ℝ) ≤ B ^ ((2 : ℝ) / 3) := Real.one_le_rpow (by linarith) (by positivity)
    have h100 : (100 : ℝ) ≤ (C : ℝ) := by
      dsimp [C]; push_cast
      have hcl := Nat.le_ceil (101 * B ^ ((2 : ℝ) / 3) * (Real.log (x : ℝ)) ^ 2)
      nlinarith only [hcl, hB1, hlogx1, sq_nonneg (Real.log (x : ℝ) - 1)]
    exact_mod_cast h100
  -- Apply crootlem_k2 with B' = B + 1: since B ≥ 10^14, 100 * (B + 1)^(2/3) ≤ 101 * B^(2/3)!
  have hBp_rpow : 100 * (B + 1) ^ ((2 : ℝ) / 3) ≤ 101 * B ^ ((2 : ℝ) / 3) := by
    have h1 : (B + 1) ^ (2 : ℕ) * 100 ^ 3 ≤ B ^ (2 : ℕ) * 101 ^ 3 := by nlinarith only [hB_lo]
    have h2 : (100 * (B + 1) ^ ((2 : ℝ) / 3)) ^ (3 : ℕ) ≤ (101 * B ^ ((2 : ℝ) / 3)) ^ (3 : ℕ) := by
      rw [mul_pow, mul_pow, ← Real.rpow_natCast ((B + 1) ^ ((2 : ℝ) / 3)) 3, ← Real.rpow_mul (by positivity),
        ← Real.rpow_natCast (B ^ ((2 : ℝ) / 3)) 3, ← Real.rpow_mul (by positivity)]
      norm_num
      linarith only [h1]
    by_contra hc
    push Not at hc
    have hlt := pow_lt_pow_left₀ hc (by positivity) (by norm_num : 3 ≠ 0)
    linarith only [h2, hlt]
  have hlogp_le : Real.log (p : ℝ) ≤ Real.log (x : ℝ) := by
    apply Real.log_le_log (by exact_mod_cast hp.pos)
    have hpq : (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.le_self_pow (by omega) p
    linarith
  have hC_lo : 100 * (B + 1) ^ ((2 : ℝ) / 3) * (Real.log (p : ℝ)) ^ 2 < (M.card : ℝ) := by
    rw [hMcard]
    have hlogp_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    have hsq : (Real.log (p : ℝ)) ^ 2 ≤ (Real.log (x : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hlogp_nn hlogp_le 2
    have h1 : 100 * (B + 1) ^ ((2 : ℝ) / 3) * (Real.log (p : ℝ)) ^ 2 ≤
        101 * B ^ ((2 : ℝ) / 3) * (Real.log (x : ℝ)) ^ 2 :=
      mul_le_mul hBp_rpow hsq (sq_nonneg _) (by positivity)
    have h2 : 101 * B ^ ((2 : ℝ) / 3) * (Real.log (x : ℝ)) ^ 2 < (C : ℝ) := by
      dsimp [C]; push_cast
      linarith [Nat.le_ceil (101 * B ^ ((2 : ℝ) / 3) * (Real.log (x : ℝ)) ^ 2)]
    linarith
  set target : ZMod p := -((r.num : ZMod p) * ((r.den / q : ℕ) : ZMod p)⁻¹)
  obtain ⟨K, hKM, hKsum⟩ := crootlem_k2 hp hM100 (by linarith : 8 ≤ B + 1)
    (fun m hm => by obtain ⟨p₁, p₂, h1, h2, h3, _, _, h6, _, _, _⟩ := hM_mem m hm; exact ⟨p₁, p₂, h1, h2, h3, h6⟩)
    (fun m hm => by
      obtain ⟨p₁, p₂, h1, h2, _, h4, h5, rfl, _, _, _⟩ := hM_mem m hm
      intro hd
      rcases hp.dvd_mul.mp hd with hd1 | hd2
      · exact h4 ((Nat.prime_dvd_prime_iff_eq hp h1).mp hd1).symm
      · exact h5 ((Nat.prime_dvd_prime_iff_eq hp h2).mp hd2).symm)
    (fun m hm => by obtain ⟨_, _, _, _, _, _, _, _, _, hle, _⟩ := hM_mem m hm; linarith)
    hC_lo target
  have hK_prop : ∀ m ∈ K, 0 < m ∧ ¬ p ∣ m ∧ PStar m < q := by
    intro m hm
    obtain ⟨p₁, p₂, h1, h2, h3, h4, h5, rfl, _, _, hp2q⟩ := hM_mem m (hKM hm)
    have hnd : ¬ p ∣ p₁ * p₂ := by
      intro hd
      rcases hp.dvd_mul.mp hd with hd1 | hd2
      · exact h4 ((Nat.prime_dvd_prime_iff_eq hp h1).mp hd1).symm
      · exact h5 ((Nat.prime_dvd_prime_iff_eq hp h2).mp hd2).symm
    have hcop12 : Nat.Coprime p₁ p₂ := (Nat.coprime_primes h1 h2).mpr h3.ne
    have hP12 : PStar (p₁ * p₂) = p₂ := by
      rw [PStar_mul_coprime h1.pos h2.pos hcop12]
      have hp1 : PStar p₁ = p₁ := by simpa using PStar_prime_pow h1 (le_refl 1)
      have hp2 : PStar p₂ = p₂ := by simpa using PStar_prime_pow h2 (le_refl 1)
      rw [hp1, hp2]
      exact max_eq_right h3.le
    exact ⟨Nat.mul_pos h1.pos h2.pos, hnd, by rw [hP12]; exact_mod_cast hp2q⟩
  have hcancel := PStar_add_sum_cancel hp hν hPr hdvd hK_prop (by rw [hKsum]; dsimp [target]; ring)
  set U : Finset ℕ := K.image (fun m => q * m)
  have hU_sum : ∑ n ∈ U, (1 : ℚ) / (n : ℚ) = ∑ m ∈ K, (1 : ℚ) / ((q * m : ℕ) : ℚ) := by
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left hq_pos hab
  refine ⟨U, ?_, ?_, by rw [hU_sum]; exact hcancel⟩
  · intro n hn
    rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
    obtain ⟨_, _, _, _, _, _, _, _, hmlo, hmhi, _⟩ := hM_mem m (hKM hm)
    obtain ⟨hm0, hnd, hPm⟩ := hK_prop m hm
    refine ⟨?_, ?_, PStar_mul_prime_pow_eq hp hν hm0 hnd hPm⟩
    · apply Nat.ceil_le.mpr
      have h1 : α * (x : ℝ) < (q : ℝ) * (m : ℝ) := by
        have := mul_lt_mul_of_pos_left hmlo hqR_pos
        rwa [show (q : ℝ) * (α * B) = α * (x : ℝ) by dsimp [B]; field_simp [hqR_pos.ne']] at this
      push_cast; exact h1.le
    · have h1 : (q : ℝ) * (m : ℝ) ≤ (x : ℝ) := by
        have := mul_le_mul_of_nonneg_left hmhi hqR_pos.le
        rwa [show (q : ℝ) * B = (x : ℝ) by dsimp [B]; field_simp [hqR_pos.ne']] at this
      exact_mod_cast h1
  · have hcardU : U.card ≤ C := by
      calc U.card ≤ K.card := Finset.card_image_le
        _ ≤ M.card := Finset.card_le_card hKM
        _ = C := hMcard
    exact (by exact_mod_cast hcardU : (U.card : ℝ) ≤ (C : ℝ)).trans hCR_le

/-- Asymptotic helper: for any `c > 0` and `k : ℕ`, eventually `(log x)^k ≤ c * x^(1/20)` and similar. -/
lemma eventually_log_pow_le_rpow {k : ℕ} {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) :
    ∀ᶠ x : ℕ in Filter.atTop, (Real.log (x : ℝ)) ^ k ≤ c * (x : ℝ) ^ ε := by
  -- For any δ > 0, log x ≤ x^δ / δ, so (log x)^k ≤ x^(k*δ) / δ^k, and x^(ε - k*δ) → ∞!
  set δ : ℝ := ε / (2 * (k + 1 : ℕ))
  have hδ : 0 < δ := by positivity
  have hpow_gt : 0 < ε - (k : ℝ) * δ := by
    dsimp [δ]
    have hk : (k : ℝ) < 2 * ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
    rw [sub_pos, mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  have htend : Tendsto (fun x : ℕ => (x : ℝ) ^ (ε - (k : ℝ) * δ)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hpow_gt).comp tendsto_natCast_atTop_atTop
  filter_upwards [htend.eventually_ge_atTop (1 / (c * δ ^ k)), Filter.eventually_ge_atTop 2] with x hx hx2
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hlog_nn : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ x))
  have hlog_le : Real.log (x : ℝ) ≤ (x : ℝ) ^ δ / δ := Real.log_le_rpow_div hxpos.le hδ
  have hpow_le : (Real.log (x : ℝ)) ^ k ≤ ((x : ℝ) ^ δ / δ) ^ k :=
    pow_le_pow_left₀ hlog_nn hlog_le k
  rw [div_pow, ← Real.rpow_natCast ((x : ℝ) ^ δ) k, ← Real.rpow_mul hxpos.le, mul_comm δ (k : ℝ)] at hpow_le
  have h2 : 1 / (δ ^ k) ≤ c * (x : ℝ) ^ (ε - (k : ℝ) * δ) := by
    rw [div_le_iff₀ (pow_pos hδ k)]
    have hx' := (div_le_iff₀ (by positivity : 0 < c * δ ^ k)).mp hx
    nlinarith
  calc (Real.log (x : ℝ)) ^ k ≤ (x : ℝ) ^ ((k : ℝ) * δ) / δ ^ k := hpow_le
    _ = (x : ℝ) ^ ((k : ℝ) * δ) * (1 / δ ^ k) := by ring
    _ ≤ (x : ℝ) ^ ((k : ℝ) * δ) * (c * (x : ℝ) ^ (ε - (k : ℝ) * δ)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = c * ((x : ℝ) ^ ((k : ℝ) * δ) * (x : ℝ) ^ (ε - (k : ℝ) * δ)) := by ring
    _ = c * (x : ℝ) ^ ε := by rw [← Real.rpow_add hxpos, add_sub_cancel]

/-- Helper step for `exists_egyptian_of_PStar_le`: invokes `biglem` for a prime power `k = p^ν`
in `(x^(2/5), x / (log x)^13]`. -/
lemma biglem_in_range {x k p ν : ℕ} {α : ℝ} {q0 : ℚ}
    (hx_big : 10 ^ 20 ≤ x)
    (hlog_big : (10 ^ 18 : ℝ) ≤ Real.log (x : ℝ))
    (hα_lo : 35 / 100 ≤ α) (hα_hi : α ≤ 42 / 100)
    (hp : p.Prime) (hν : 1 ≤ ν) (hpeq : p ^ ν = k)
    (hPq : PStar q0.den ≤ k) (hdvd : k ∣ q0.den)
    (hk_gt : (x : ℝ) ^ ((2 : ℝ) / 5) < (k : ℝ))
    (hk_le_yb : (k : ℝ) ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ 13)
    (hk_le_x : k ≤ x) :
    ∃ U : Finset ℕ,
      (∀ n ∈ U, ⌈α * (x : ℝ)⌉₊ ≤ n ∧ n ≤ x ∧ PStar n = k) ∧
      (U.card : ℝ) ≤ 101 * ((x : ℝ) / (k : ℝ)) ^ ((2 : ℝ) / 3) * (Real.log (x : ℝ)) ^ 2 + 2 ∧
      PStar (q0 + ∑ n ∈ U, (1 : ℚ) / (n : ℚ)).den < k := by
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hlogx_pos : 0 < Real.log (x : ℝ) := by linarith only [hlog_big]
  have hk_pos : (0 : ℝ) < (k : ℝ) := lt_trans (Real.rpow_pos_of_pos hxpos _) hk_gt
  set B : ℝ := (x : ℝ) / (k : ℝ)
  have hBpos : 0 < B := by positivity
  have hB_ge_log13 : (Real.log (x : ℝ)) ^ 13 ≤ B := by
    dsimp [B]
    rw [le_div_iff₀ hk_pos]
    have hmul := (le_div_iff₀ (by positivity : 0 < (Real.log (x : ℝ)) ^ 13)).mp hk_le_yb
    linarith only [hmul]
  have hB_ge : (100000000000000 : ℝ) ≤ B := by
    have h1 : (1000000 : ℝ) ^ (13 : ℕ) ≤ (Real.log (x : ℝ)) ^ 13 :=
      pow_le_pow_left₀ (by norm_num) (by linarith only [hlog_big]) 13
    norm_num at h1
    linarith only [h1, hB_ge_log13]
  have hB_lo : (100000000000000 : ℝ) ≤ (x : ℝ) / ((p ^ ν : ℕ) : ℝ) := by
    rw [hpeq]; exact hB_ge
  have hB_vs_C : 101 * ((x : ℝ) / ((p ^ ν : ℕ) : ℝ)) ^ ((2 : ℝ) / 3) * (Real.log (x : ℝ)) ^ 2 + 2 ≤
      ((x : ℝ) / ((p ^ ν : ℕ) : ℝ)) / (1000 * (Real.log ((x : ℝ) / ((p ^ ν : ℕ) : ℝ))) ^ 2) := by
    rw [hpeq]
    change 101 * B ^ ((2 : ℝ) / 3) * (Real.log (x : ℝ)) ^ 2 + 2 ≤ B / (1000 * (Real.log B) ^ 2)
    have hlogB_le : Real.log B ≤ Real.log (x : ℝ) := by
      apply Real.log_le_log hBpos
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
        have h1 : (1 : ℝ) ≤ (x : ℝ) ^ ((2 : ℝ) / 5) :=
          Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ x)) (by norm_num)
        linarith only [h1, hk_gt]
      exact div_le_self hxpos.le hk1
    have hlogB_pos : 0 < Real.log B := Real.log_pos (by linarith only [hB_ge])
    have hB13_ge : 102000 * (Real.log (x : ℝ)) ^ 4 ≤ B ^ ((1 : ℝ) / 3) := by
      have hcub : (102000 * (Real.log (x : ℝ)) ^ 4) ^ (3 : ℕ) ≤ B := by
        have h1 : (102000 : ℝ) ^ 3 ≤ Real.log (x : ℝ) := by norm_num at hlog_big ⊢; linarith only [hlog_big]
        calc (102000 * (Real.log (x : ℝ)) ^ 4) ^ (3 : ℕ)
            = (102000 : ℝ) ^ 3 * (Real.log (x : ℝ)) ^ 12 := by ring
          _ ≤ Real.log (x : ℝ) * (Real.log (x : ℝ)) ^ 12 :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = (Real.log (x : ℝ)) ^ 13 := by ring
          _ ≤ B := hB_ge_log13
      have hr := Real.rpow_le_rpow (by positivity) hcub (by positivity : (0 : ℝ) ≤ 1 / 3)
      rw [← Real.rpow_natCast (102000 * (Real.log (x : ℝ)) ^ 4) 3, ← Real.rpow_mul (by positivity)] at hr
      norm_num at hr
      exact hr
    have h2_le : (2 : ℝ) ≤ B ^ ((2 : ℝ) / 3) * (Real.log (x : ℝ)) ^ 2 := by
      have hB1 : (1 : ℝ) ≤ B ^ ((2 : ℝ) / 3) := Real.one_le_rpow (by linarith only [hB_ge]) (by positivity)
      have hl1 : (2 : ℝ) ≤ (Real.log (x : ℝ)) ^ 2 := by nlinarith only [hlog_big]
      nlinarith only [hB1, hl1]
    have hlogBsq : (Real.log B) ^ 2 ≤ (Real.log (x : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hlogB_pos.le hlogB_le 2
    rw [le_div_iff₀ (by positivity)]
    have hLHS_le : (101 * B ^ ((2 : ℝ) / 3) * (Real.log (x : ℝ)) ^ 2 + 2) * (1000 * (Real.log B) ^ 2) ≤
        102000 * (Real.log (x : ℝ)) ^ 4 * B ^ ((2 : ℝ) / 3) := by
      have h1 : 101 * B ^ ((2 : ℝ) / 3) * (Real.log (x : ℝ)) ^ 2 + 2 ≤
          102 * B ^ ((2 : ℝ) / 3) * (Real.log (x : ℝ)) ^ 2 := by linarith only [h2_le]
      have h2 := mul_le_mul h1 (show 1000 * (Real.log B) ^ 2 ≤ 1000 * (Real.log (x : ℝ)) ^ 2 by linarith only [hlogBsq])
        (by positivity) (by positivity)
      have heq : 102 * B ^ ((2 : ℝ) / 3) * (Real.log (x : ℝ)) ^ 2 * (1000 * (Real.log (x : ℝ)) ^ 2) =
          102000 * (Real.log (x : ℝ)) ^ 4 * B ^ ((2 : ℝ) / 3) := by ring
      linarith only [h2, heq]
    have hmulB : 102000 * (Real.log (x : ℝ)) ^ 4 * B ^ ((2 : ℝ) / 3) ≤ B := by
      have h1 := mul_le_mul_of_nonneg_right hB13_ge (by positivity : (0 : ℝ) ≤ B ^ ((2 : ℝ) / 3))
      have h2 : B ^ ((1 : ℝ) / 3) * B ^ ((2 : ℝ) / 3) = B := by
        rw [← Real.rpow_add hBpos]; norm_num
      linarith only [h1, h2]
    linarith only [hLHS_le, hmulB]
  have hp2_lt_q : 10 * Real.sqrt ((x : ℝ) / ((p ^ ν : ℕ) : ℝ)) < ((p ^ ν : ℕ) : ℝ) := by
    rw [hpeq]
    have hdiv_lt : (x : ℝ) / (k : ℝ) < (x : ℝ) ^ ((3 : ℝ) / 5) := by
      rw [div_lt_iff₀ hk_pos]
      have hmul : (x : ℝ) ^ ((3 : ℝ) / 5) * (x : ℝ) ^ ((2 : ℝ) / 5) = (x : ℝ) := by
        rw [← Real.rpow_add hxpos]; norm_num
      have hx35 : 0 < (x : ℝ) ^ ((3 : ℝ) / 5) := Real.rpow_pos_of_pos hxpos _
      nlinarith only [hk_gt, hmul, hx35]
    have hsq_lt : Real.sqrt ((x : ℝ) / (k : ℝ)) < (x : ℝ) ^ ((3 : ℝ) / 10) := by
      have h1 := Real.sqrt_lt_sqrt (by positivity) hdiv_lt
      have h2 : Real.sqrt ((x : ℝ) ^ ((3 : ℝ) / 5)) = (x : ℝ) ^ ((3 : ℝ) / 10) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hxpos.le]; norm_num
      linarith only [h1, h2]
    have h10_lt : 10 * (x : ℝ) ^ ((3 : ℝ) / 10) ≤ (x : ℝ) ^ ((2 : ℝ) / 5) := by
      have h1 : (10 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 10) := by
        have h10 : (10 : ℝ) ^ (10 : ℝ) ≤ (x : ℝ) := by
          have : (10 ^ 10 : ℕ) ≤ (10 ^ 20 : ℕ) := by norm_num
          exact_mod_cast this.trans hx_big
        have hr := Real.rpow_le_rpow (by positivity) h10 (by positivity : (0 : ℝ) ≤ 1 / 10)
        rw [← Real.rpow_mul (by positivity)] at hr; norm_num at hr; exact hr
      have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ (x : ℝ) ^ ((3 : ℝ) / 10))
      rw [← Real.rpow_add hxpos] at h2
      norm_num at h2
      exact h2
    linarith only [hsq_lt, h10_lt, hk_gt]
  have hq_le_x : ((p ^ ν : ℕ) : ℝ) ≤ (x : ℝ) := by rw [hpeq]; exact_mod_cast hk_le_x
  obtain ⟨U, hUprop, hUcard, hUcancel⟩ := biglem hp hν hα_lo hα_hi (hpeq.symm ▸ hPq)
    (hpeq.symm ▸ hdvd) (by omega) hq_le_x hB_lo hB_vs_C hp2_lt_q
  rw [hpeq] at hUprop hUcard hUcancel
  exact ⟨U, hUprop, hUcard, hUcancel⟩

/-- Helper for `exists_egyptian_of_PStar_le`: bounds the sum of reciprocals over
`BadA = {n ∈ [⌈α x⌉₊, x] : PStar n > y_big}` from below and above. -/
lemma badA_sum_bounds {x y_small y_big : ℕ} {α : ℝ}
    (hx_big : 10 ^ 20 ≤ x)
    (hlog_big : (10 ^ 18 : ℝ) ≤ Real.log (x : ℝ))
    (hll_big : (10000 : ℝ) ≤ Real.log (Real.log (x : ℝ)))
    (hlog15 : (Real.log (x : ℝ)) ^ 15 ≤ (1 / 10000000 : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 10))
    (hlog13_half : (Real.log (x : ℝ)) ^ 13 ≤ (1 / 100 : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 2))
    (hlog13_6 : (Real.log (x : ℝ)) ^ 13 ≤ (1 / 1000 : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 6))
    (hα_lo : 35 / 100 ≤ α) (hα_hi : α ≤ 42 / 100)
    (hy_big_def : y_big = ⌊(x : ℝ) / (Real.log (x : ℝ)) ^ 13⌋₊)
    (hyb_le_x : y_big ≤ x)
    (_hys_ge : 10000 ≤ y_small) :
    let L := ⌈α * (x : ℝ)⌉₊
    let BadA := (Finset.Icc L x).filter (fun n => ¬ PStar n ≤ y_big)
    200 / Real.log (x : ℝ) < ∑ n ∈ BadA, (1 : ℝ) / (n : ℝ) ∧
    ∑ n ∈ BadA, (1 : ℝ) / (n : ℝ) < 1 / 4 := by
  intro L BadA
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hlogx_pos : 0 < Real.log (x : ℝ) := by linarith only [hlog_big]
  have hL_ge : α * (x : ℝ) ≤ (L : ℝ) := Nat.le_ceil _
  have hL_pos : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr (by
    intro hz; have h0 := Nat.ceil_eq_zero.mp hz; linarith [mul_pos (show 0 < α by linarith only [hα_lo]) hxpos])
  have hBadA_eq : BadA = (Finset.Icc L x).filter (fun n => (y_big : ℝ) < (PStar n : ℝ)) := by
    ext n; simp only [BadA, Finset.mem_filter, not_le, Nat.cast_lt]
  have hyb_gt_sqrt : Real.sqrt (x : ℝ) < (y_big : ℝ) := by
    have h1 : 100 * Real.sqrt (x : ℝ) ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ 13 := by
      rw [le_div_iff₀ (by positivity), Real.sqrt_eq_rpow]
      have hm : (x : ℝ) ^ ((1 : ℝ) / 2) * (x : ℝ) ^ ((1 : ℝ) / 2) = (x : ℝ) := by
        rw [← Real.rpow_add hxpos]; norm_num
      have hx12 : 0 < (x : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hxpos ((1 : ℝ) / 2)
      nlinarith only [hlog13_half, hm, hx12]
    have h2 : (x : ℝ) / (Real.log (x : ℝ)) ^ 13 - 1 < (y_big : ℝ) := by
      rw [hy_big_def]; exact Nat.sub_one_lt_floor _
    have h3 : (1 : ℝ) ≤ Real.sqrt (x : ℝ) := by rw [Real.one_le_sqrt]; exact_mod_cast (by omega : 1 ≤ x)
    linarith only [h1, h2, h3]
  have hyb_pos : (0 : ℝ) < (y_big : ℝ) := lt_trans (Real.sqrt_pos.mpr hxpos) hyb_gt_sqrt
  constructor
  · rw [hBadA_eq]
    set M : ℕ := ⌊(Real.log (x : ℝ)) ^ 12⌋₊
    have hM1 : 1 ≤ M := Nat.le_floor (by push_cast; exact one_le_pow₀ (by linarith only [hlog_big]))
    have hM_le : (M : ℝ) ≤ (Real.log (x : ℝ)) ^ 12 := Nat.floor_le (by positivity)
    have hM_gt : (Real.log (x : ℝ)) ^ 12 - 1 < (M : ℝ) := Nat.sub_one_lt_floor _
    have hM_big : 1000000 * (M : ℝ) ≤ (x : ℝ) := by
      have h1 : (Real.log (x : ℝ)) ^ 12 ≤ (Real.log (x : ℝ)) ^ 15 :=
        pow_le_pow_right₀ (by linarith only [hlog_big]) (by norm_num)
      have h2 : (x : ℝ) ^ ((1 : ℝ) / 10) ≤ (x : ℝ) :=
        Real.rpow_le_self_of_one_le (by exact_mod_cast (by omega : 1 ≤ x)) (by norm_num)
      nlinarith only [hM_le, h1, hlog15, h2]
    have hMy : (M : ℝ) * (y_big : ℝ) ≤ α * (x : ℝ) := by
      have hyb_le : (y_big : ℝ) ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ 13 := by
        rw [hy_big_def]; exact Nat.floor_le (by positivity)
      have hprod : (M : ℝ) * (y_big : ℝ) ≤ (Real.log (x : ℝ)) ^ 12 * ((x : ℝ) / (Real.log (x : ℝ)) ^ 13) :=
        mul_le_mul hM_le hyb_le (Nat.cast_nonneg _) (by positivity)
      have hrw : (Real.log (x : ℝ)) ^ 12 * ((x : ℝ) / (Real.log (x : ℝ)) ^ 13) = (x : ℝ) / Real.log (x : ℝ) := by
        field_simp [hlogx_pos.ne']
      have hdiv : (x : ℝ) / Real.log (x : ℝ) ≤ α * (x : ℝ) := by
        rw [div_le_iff₀ hlogx_pos]
        have h1 : (1 : ℝ) ≤ α * Real.log (x : ℝ) := by nlinarith only [hlog_big, hα_lo]
        nlinarith only [h1, hxpos]
      linarith only [hprod, hrw, hdiv]
    have hlb := sum_inv_PStar_gt_ge (show 0 < α by linarith only [hα_lo]) (by linarith only [hα_hi]) (by omega) hM1 hyb_gt_sqrt hM_big hMy
    have hlogM : 12 * Real.log (Real.log (x : ℝ)) - 1 ≤ Real.log ((M : ℝ) + 1) := by
      have hle : (Real.log (x : ℝ)) ^ 12 ≤ (M : ℝ) + 1 := by linarith only [hM_gt]
      have h1 := Real.log_le_log (by positivity) hle
      rw [Real.log_pow] at h1
      push_cast at h1
      linarith only [h1]
    have h200 : 200 / Real.log (x : ℝ) < Real.log ((M : ℝ) + 1) / (20 * Real.log (x : ℝ)) := by
      rw [div_lt_div_iff₀ hlogx_pos (by positivity)]
      nlinarith only [hlogM, hll_big, hlogx_pos]
    exact lt_of_lt_of_le h200 hlb
  · rw [hBadA_eq]
    have hsub : (Finset.Icc L x).filter (fun n => (y_big : ℝ) < (PStar n : ℝ)) ⊆
        (Finset.Icc 1 x).filter (fun n => (y_big : ℝ) < (PStar n : ℝ)) :=
      Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_left hL_pos)
    have hsum_card : ∑ n ∈ (Finset.Icc L x).filter (fun n => (y_big : ℝ) < (PStar n : ℝ)), (1 : ℝ) / (n : ℝ) ≤
        (((Finset.Icc 1 x).filter (fun n => (y_big : ℝ) < (PStar n : ℝ))).card : ℝ) / (α * (x : ℝ)) := by
      calc ∑ n ∈ (Finset.Icc L x).filter (fun n => (y_big : ℝ) < (PStar n : ℝ)), (1 : ℝ) / (n : ℝ)
          ≤ ∑ _n ∈ (Finset.Icc L x).filter (fun n => (y_big : ℝ) < (PStar n : ℝ)), (1 : ℝ) / (α * (x : ℝ)) := by
            apply Finset.sum_le_sum
            intro n hn
            have hnL : L ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
            exact one_div_le_one_div_of_le (by positivity) (hL_ge.trans (by exact_mod_cast hnL))
        _ = ((((Finset.Icc L x).filter (fun n => (y_big : ℝ) < (PStar n : ℝ))).card : ℝ)) / (α * (x : ℝ)) := by
            simp [div_eq_mul_inv]
        _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) (by positivity)
    have hcard_ub := card_PStar_gt_le (by omega) hyb_gt_sqrt.le (by exact_mod_cast hyb_le_x)
    have hxyb : (x : ℝ) / (y_big : ℝ) ≤ 2 * (Real.log (x : ℝ)) ^ 13 := by
      have h1 : (x : ℝ) / (Real.log (x : ℝ)) ^ 13 / 2 ≤ (y_big : ℝ) := by
        have hgt : (x : ℝ) / (Real.log (x : ℝ)) ^ 13 - 1 < (y_big : ℝ) := by
          rw [hy_big_def]; exact Nat.sub_one_lt_floor _
        have hbig : (2 : ℝ) ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ 13 := by
          rw [le_div_iff₀ (by positivity)]
          have hx12 : (x : ℝ) ^ ((1 : ℝ) / 2) ≤ (x : ℝ) :=
            Real.rpow_le_self_of_one_le (by exact_mod_cast (by omega : 1 ≤ x)) (by norm_num)
          nlinarith only [hlog13_half, hx12]
        linarith only [hgt, hbig]
      rw [div_le_iff₀ hyb_pos]
      have hmul := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * (Real.log (x : ℝ)) ^ 13)
      have hrw : 2 * (Real.log (x : ℝ)) ^ 13 * ((x : ℝ) / (Real.log (x : ℝ)) ^ 13 / 2) = (x : ℝ) := by
        field_simp [hlogx_pos.ne']
      linarith only [hmul, hrw]
    have hlog_xyb : Real.log ((x : ℝ) / (y_big : ℝ)) ≤ 14 * Real.log (Real.log (x : ℝ)) := by
      have h1 := Real.log_le_log (by positivity) hxyb
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h1
      push_cast at h1
      have h2 : Real.log 2 ≤ Real.log (Real.log (x : ℝ)) := by linarith only [Real.log_two_lt_d9, hll_big]
      linarith only [h1, h2]
    have hll_le : Real.log (Real.log (x : ℝ)) ≤ Real.log (x : ℝ) / 100000 := by
      have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hlogx_pos)
      rw [Real.log_sqrt hlogx_pos.le] at h1
      have hsq : (1000000000 : ℝ) ≤ Real.sqrt (Real.log (x : ℝ)) := by
        rw [show (1000000000 : ℝ) = Real.sqrt (10 ^ 18 : ℝ) by norm_num]
        exact Real.sqrt_le_sqrt hlog_big
      have hmul : 1000000000 * Real.sqrt (Real.log (x : ℝ)) ≤ Real.log (x : ℝ) := by
        have hm := mul_le_mul_of_nonneg_right hsq (Real.sqrt_nonneg (Real.log (x : ℝ)))
        rwa [Real.mul_self_sqrt hlogx_pos.le] at hm
      linarith only [h1, hmul, hlogx_pos]
    have hsqrt_yb : (1000 : ℝ) ≤ Real.sqrt (y_big : ℝ) := by
      have h1 : (1000000 : ℝ) ≤ (y_big : ℝ) := by
        have hsq : (10000000000 : ℝ) ≤ Real.sqrt (x : ℝ) := by
          rw [show (10000000000 : ℝ) = Real.sqrt (10 ^ 20 : ℝ) by norm_num]
          exact Real.sqrt_le_sqrt (by exact_mod_cast hx_big)
        linarith only [hsq, hyb_gt_sqrt]
      rw [show (1000 : ℝ) = Real.sqrt 1000000 by norm_num]
      exact Real.sqrt_le_sqrt h1
    have hx13_div : (x : ℝ) ^ ((1 : ℝ) / 3) / (y_big : ℝ) ≤ 1 / 100 := by
      rw [div_le_iff₀ hyb_pos]
      have hyb_ge2 : (x : ℝ) / (2 * (Real.log (x : ℝ)) ^ 13) ≤ (y_big : ℝ) := by
        have h1 := (div_le_iff₀ hyb_pos).mp hxyb
        rw [div_le_iff₀ (by positivity)]
        linarith only [h1]
      have h1 : (x : ℝ) ^ ((1 : ℝ) / 3) * (2 * (Real.log (x : ℝ)) ^ 13) * 100 ≤ (x : ℝ) := by
        have hm1 : (x : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 6) = (x : ℝ) ^ ((1 : ℝ) / 2) := by
          rw [← Real.rpow_add hxpos]; norm_num
        have hle_x : (x : ℝ) ^ ((1 : ℝ) / 2) ≤ (x : ℝ) :=
          Real.rpow_le_self_of_one_le (by exact_mod_cast (by omega : 1 ≤ x)) (by norm_num)
        have hprod := mul_le_mul_of_nonneg_left hlog13_6 (by positivity : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3))
        nlinarith only [hprod, hm1, hle_x]
      have h2 := mul_le_mul_of_nonneg_left hyb_ge2 (by norm_num : (0 : ℝ) ≤ (1 / 100 : ℝ))
      have h3 : (x : ℝ) ^ ((1 : ℝ) / 3) ≤ (1 / 100 : ℝ) * ((x : ℝ) / (2 * (Real.log (x : ℝ)) ^ 13)) := by
        rw [show (1 / 100 : ℝ) * ((x : ℝ) / (2 * (Real.log (x : ℝ)) ^ 13)) =
            (x : ℝ) / (100 * (2 * (Real.log (x : ℝ)) ^ 13)) by ring, le_div_iff₀ (by positivity)]
        linarith only [h1]
      linarith only [h2, h3]
    have htotal : (64 * (x : ℝ) * (Real.log ((x : ℝ) / (y_big : ℝ)) + 1) / Real.log (x : ℝ) +
        2 * (x : ℝ) / Real.sqrt (y_big : ℝ) + 2 * (x : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 3) / (y_big : ℝ)) /
        (α * (x : ℝ)) < 1 / 4 := by
      have ht1 : (64 * (x : ℝ) * (Real.log ((x : ℝ) / (y_big : ℝ)) + 1) / Real.log (x : ℝ)) / (α * (x : ℝ)) ≤ 1 / 10 := by
        rw [show (64 * (x : ℝ) * (Real.log ((x : ℝ) / (y_big : ℝ)) + 1) / Real.log (x : ℝ)) / (α * (x : ℝ)) =
            64 * (Real.log ((x : ℝ) / (y_big : ℝ)) + 1) / (α * Real.log (x : ℝ)) by field_simp [hxpos.ne']]
        rw [div_le_iff₀ (by positivity)]
        nlinarith only [hlog_xyb, hll_le, hα_lo, hlog_big]
      have ht2 : (2 * (x : ℝ) / Real.sqrt (y_big : ℝ)) / (α * (x : ℝ)) ≤ 1 / 100 := by
        rw [show (2 * (x : ℝ) / Real.sqrt (y_big : ℝ)) / (α * (x : ℝ)) =
            2 / (α * Real.sqrt (y_big : ℝ)) by field_simp [hxpos.ne']]
        rw [div_le_iff₀ (by positivity)]
        nlinarith only [hα_lo, hsqrt_yb]
      have ht3 : (2 * (x : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 3) / (y_big : ℝ)) / (α * (x : ℝ)) ≤ 1 / 10 := by
        rw [show (2 * (x : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 3) / (y_big : ℝ)) / (α * (x : ℝ)) =
            (2 / α) * ((x : ℝ) ^ ((1 : ℝ) / 3) / (y_big : ℝ)) by field_simp [hxpos.ne']]
        have h2α : 2 / α ≤ 6 := by rw [div_le_iff₀ (by linarith only [hα_lo])]; linarith only [hα_lo]
        have hnn1 : 0 ≤ 2 / α := by positivity
        have hnn2 : 0 ≤ (x : ℝ) ^ ((1 : ℝ) / 3) / (y_big : ℝ) := by positivity
        nlinarith only [h2α, hx13_div, hnn1, hnn2]
      rw [add_div, add_div]
      linarith only [ht1, ht2, ht3]
    have hdiv_ub := div_le_div_of_nonneg_right hcard_ub (by positivity : (0 : ℝ) ≤ α * (x : ℝ))
    linarith only [hsum_card, hdiv_ub, htotal]

/-- Main representation theorem: eventually in `x : ℕ`, EVERY rational `r ∈ [9/10, 1)` with
`PStar r.den ≤ x / (log x)^13` can be represented as `∑ n ∈ E, (1 : ℚ) / n` for some
`E ⊆ Finset.Icc 1 x`. -/
lemma exists_egyptian_of_PStar_le :
    ∀ᶠ x : ℕ in Filter.atTop,
      ∀ r : ℚ, (9 / 10 : ℝ) ≤ (r : ℝ) → (r : ℝ) < 1 →
        (PStar r.den : ℝ) ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ 13 →
        ∃ E : Finset ℕ, E ⊆ Finset.Icc 1 x ∧ ∑ n ∈ E, (1 : ℚ) / (n : ℚ) = r := by
  have hlog_tend : Tendsto (fun x : ℕ => Real.log (x : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hll_tend : Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ))) Filter.atTop Filter.atTop :=
    tendsto_log_atTop.comp hlog_tend
  have h1 := eventually_log_pow_le_rpow (k := 15) (ε := (1 : ℝ) / 10) (c := (1 : ℝ) / 10000000) (by norm_num) (by norm_num)
  have h2 := eventually_log_pow_le_rpow (k := 13) (ε := (1 : ℝ) / 2) (c := (1 : ℝ) / 100) (by norm_num) (by norm_num)
  have h3 := eventually_log_pow_le_rpow (k := 2) (ε := (1 : ℝ) / 10) (c := (1 : ℝ) / 1000) (by norm_num) (by norm_num)
  have h4 := eventually_log_pow_le_rpow (k := 13) (ε := (1 : ℝ) / 6) (c := (1 : ℝ) / 1000) (by norm_num) (by norm_num)
  have h5 := eventually_log_pow_le_rpow (k := 1) (ε := (1 : ℝ) / 5) (c := (1 : ℝ) / 100) (by norm_num) (by norm_num)
  filter_upwards [Filter.eventually_ge_atTop (10 ^ 20 : ℕ), hlog_tend.eventually_ge_atTop (10 ^ 18 : ℝ),
    hll_tend.eventually_ge_atTop 10000, h1, h2, h3, h4, h5]
    with x hx_big hlog_big hll_big hlog15 hlog13_half hlog2_10 hlog13_6 hlog1_5
  intro r hr_lo hr_hi hPr_le
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hlogx_pos : 0 < Real.log (x : ℝ) := by linarith
  set α : ℝ := Real.exp (-(r : ℝ))
  have hα_lo : (35 / 100 : ℝ) ≤ α := by
    have h1 : Real.exp (-1 : ℝ) ≤ α := Real.exp_le_exp.mpr (by linarith)
    have h2 : (35 / 100 : ℝ) ≤ Real.exp (-1 : ℝ) := by
      rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos 1)]
      linarith [Real.exp_one_lt_d9]
    linarith
  have hα_hi : α ≤ (42 / 100 : ℝ) := by
    have h1 : α ≤ Real.exp (-(9 / 10 : ℝ)) := Real.exp_le_exp.mpr (by linarith)
    -- Show exp(9/10) ≥ 100/42: exp(9/10) ≥ 1 + 9/10 + (9/10)^2 / 2 + (9/10)^3 / 6 = 1 + 0.9 + 0.405 + 0.1215 = 2.4265 > 100/42 = 2.381!
    -- Even simpler: (exp(9/10))^10 = exp(9) = e^9 > (2.71)^9 > (100/42)^10!
    -- Or use Real.sum_le_exp_of_nonneg (k = 4): 1 + 0.9 + 0.405 + 0.1215 = 2.4265 > 100/42!
    have h2 : (100 / 42 : ℝ) ≤ Real.exp (9 / 10 : ℝ) := by
      have hsum := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 9 / 10 by norm_num) 4
      simp [Finset.sum_range_succ, Nat.factorial] at hsum
      linarith
    have h3 : Real.exp (-(9 / 10 : ℝ)) ≤ 42 / 100 := by
      rw [Real.exp_neg]
      rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      linarith
    linarith
  set y_small : ℕ := ⌊(x : ℝ) ^ ((2 : ℝ) / 5)⌋₊
  set y_big : ℕ := ⌊(x : ℝ) / (Real.log (x : ℝ)) ^ 13⌋₊
  have hys_ge : 10000 ≤ y_small := by
    apply Nat.le_floor
    have h1 : (10000 : ℝ) ≤ (10 ^ 20 : ℝ) ^ ((2 : ℝ) / 5) := by
      rw [show (10 ^ 20 : ℝ) = ((10 : ℝ) ^ (5 : ℝ)) ^ (4 : ℝ) by
        rw [← Real.rpow_mul (by positivity)]; norm_num]
      rw [← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity)]
      norm_num
    have h2 : (10 ^ 20 : ℝ) ^ ((2 : ℝ) / 5) ≤ (x : ℝ) ^ ((2 : ℝ) / 5) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hx_big) (by positivity)
    linarith
  have hy_order : y_small < y_big := by
    have h1 : (x : ℝ) ^ ((2 : ℝ) / 5) + 1 < (x : ℝ) / (Real.log (x : ℝ)) ^ 13 := by
      -- x / (log x)^13 ≥ 100 * x^(1/2) > x^(2/5) + 1
      have hdiv : 100 * (x : ℝ) ^ ((1 : ℝ) / 2) ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ 13 := by
        rw [le_div_iff₀ (by positivity)]
        have hmul : (x : ℝ) ^ ((1 : ℝ) / 2) * (x : ℝ) ^ ((1 : ℝ) / 2) = (x : ℝ) := by
          rw [← Real.rpow_add hxpos]; norm_num
        nlinarith [Real.rpow_pos_of_pos hxpos ((1 : ℝ) / 2)]
      have hcmp : (x : ℝ) ^ ((2 : ℝ) / 5) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ x)) (by norm_num)
      have hge1 : (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) :=
        Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ x)) (by norm_num)
      linarith
    have hys_le : (y_small : ℝ) ≤ (x : ℝ) ^ ((2 : ℝ) / 5) := Nat.floor_le (by positivity)
    have hyb_gt : (x : ℝ) / (Real.log (x : ℝ)) ^ 13 - 1 < (y_big : ℝ) := Nat.sub_one_lt_floor _
    have : (y_small : ℝ) < (y_big : ℝ) := by linarith
    exact_mod_cast this
  have hyb_le_x : y_big ≤ x := by
    have h1 : (x : ℝ) / (Real.log (x : ℝ)) ^ 13 ≤ (x : ℝ) :=
      div_le_self hxpos.le (one_le_pow₀ (by linarith))
    have : (y_big : ℝ) ≤ (x : ℝ) := (Nat.floor_le (by positivity)).trans h1
    exact_mod_cast this
  -- Initial set A = {n ∈ [⌈α x⌉₊, x] : PStar n ≤ y_big}
  set L : ℕ := ⌈α * (x : ℝ)⌉₊
  set A : Finset ℕ := (Finset.Icc L x).filter (fun n => PStar n ≤ y_big)
  have hP_rA : PStar (r - ∑ n ∈ A, (1 : ℚ) / (n : ℚ)).den ≤ y_big := by
    have hPr_yb : PStar r.den ≤ y_big := Nat.le_floor hPr_le
    have hPA : PStar (∑ n ∈ A, (1 : ℚ) / (n : ℚ)).den ≤ y_big := by
      apply PStar_sum_inv_den_le _ y_big (by omega)
      intro n hn
      have hn' := Finset.mem_filter.mp hn
      have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr (by
        intro hz; have := Nat.ceil_eq_zero.mp hz; linarith [mul_pos (show 0 < α by linarith) hxpos])
      exact ⟨by have := (Finset.mem_Icc.mp hn'.1).1; omega, hn'.2⟩
    exact (PStar_rat_sub_den_le _ _).trans (max_le hPr_yb hPA)
  -- Descending induction on k from y_big down to y_small:
  -- For any k ∈ [y_small, y_big] and q0 : ℚ with PStar q0.den ≤ k, there exists Rrem ⊆ A such that:
  -- (1) ∀ n ∈ Rrem, y_small < PStar n ∧ PStar n ≤ k
  -- (2) PStar (q0 + ∑ n ∈ Rrem, 1/n).den ≤ y_small
  -- (3) (Rrem.card : ℝ) ≤ ∑ m ∈ Ioc y_small k, (101 * ((x : ℝ) / m)^(2/3) * (log x)^2 + 2)
  have hbig_ind : ∀ d : ℕ, y_small + d ≤ y_big → ∀ q0 : ℚ, PStar q0.den ≤ y_small + d →
      ∃ Rrem : Finset ℕ, Rrem ⊆ A ∧
        (∀ n ∈ Rrem, y_small < PStar n ∧ PStar n ≤ y_small + d) ∧
        PStar (q0 + ∑ n ∈ Rrem, (1 : ℚ) / (n : ℚ)).den ≤ y_small ∧
        (Rrem.card : ℝ) ≤ ∑ m ∈ Finset.Ioc y_small (y_small + d),
          (101 * ((x : ℝ) / (m : ℝ)) ^ ((2 : ℝ) / 3) * (Real.log (x : ℝ)) ^ 2 + 2) := by
    intro d
    induction d with
    | zero =>
      intro _ q0 hPq
      refine ⟨∅, Finset.empty_subset A, by simp, by simpa using hPq, by simp⟩
    | succ d ih =>
      intro hd_le q0 hPq
      set k := y_small + d + 1
      have hk_eq : y_small + (d + 1) = k := by omega
      rw [hk_eq] at hd_le hPq ⊢
      have hstep_mono :
          ∑ m ∈ Finset.Ioc y_small (y_small + d),
            (101 * ((x : ℝ) / (m : ℝ)) ^ ((2 : ℝ) / 3) * (Real.log (x : ℝ)) ^ 2 + 2) ≤
          ∑ m ∈ Finset.Ioc y_small k,
            (101 * ((x : ℝ) / (m : ℝ)) ^ ((2 : ℝ) / 3) * (Real.log (x : ℝ)) ^ 2 + 2) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_right (by omega))
          (fun _ _ _ => by positivity)
      by_cases hdiv : k ∣ q0.den ∧ ∃ p ν : ℕ, p.Prime ∧ 1 ≤ ν ∧ p ^ ν = k
      · obtain ⟨hdvd, p, ν, hp, hν, hpeq⟩ := hdiv
        have hk_gt : (x : ℝ) ^ ((2 : ℝ) / 5) < (k : ℝ) := by
          have h1 : (x : ℝ) ^ ((2 : ℝ) / 5) < (y_small : ℝ) + 1 := Nat.lt_floor_add_one _
          have h2 : (y_small : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast (show y_small + 1 ≤ k by omega)
          linarith only [h1, h2]
        have hk_le_yb : (k : ℝ) ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ 13 :=
          (by exact_mod_cast hd_le : (k : ℝ) ≤ (y_big : ℝ)).trans (Nat.floor_le (by positivity))
        obtain ⟨U, hUprop, hUcard, hUcancel⟩ := biglem_in_range hx_big hlog_big hα_lo hα_hi
          hp hν hpeq hPq hdvd hk_gt hk_le_yb (hd_le.trans hyb_le_x)
        have hPr' : PStar (q0 + ∑ n ∈ U, (1 : ℚ) / (n : ℚ)).den ≤ y_small + d := by omega
        obtain ⟨R₀, hR₀sub, hR₀P, hR₀end, hR₀card⟩ := ih (by omega) _ hPr'
        have hUsubA : U ⊆ A := by
          intro n hn
          obtain ⟨hnL, hnx, hnP⟩ := hUprop n hn
          exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hnL, hnx⟩, by omega⟩
        have hdisj : Disjoint U R₀ := by
          rw [Finset.disjoint_left]
          intro n hnU hnR₀
          have h1 := (hUprop n hnU).2.2
          have h2 := (hR₀P n hnR₀).2
          omega
        refine ⟨U ∪ R₀, Finset.union_subset hUsubA hR₀sub, ?_, ?_, ?_⟩
        · intro n hn
          rcases Finset.mem_union.mp hn with hnU | hnR₀
          · have h1 := (hUprop n hnU).2.2; omega
          · have h2 := hR₀P n hnR₀; omega
        · rw [Finset.sum_union hdisj, ← add_assoc]
          exact hR₀end
        · rw [Finset.card_union_of_disjoint hdisj, Nat.cast_add]
          have hIoc_eq : Finset.Ioc y_small k = insert k (Finset.Ioc y_small (y_small + d)) := by
            ext m; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
          rw [hIoc_eq, Finset.sum_insert (by simp only [Finset.mem_Ioc]; omega)]
          linarith only [hUcard, hR₀card]
      · -- Either ¬ k ∣ q0.den or k is not a prime power → PStar q0.den ≤ y_small + d!
        have hPq' : PStar q0.den ≤ y_small + d := by
          by_contra hgt
          have heq : PStar q0.den = k := by omega
          have hq1 : 1 < q0.den := by
            by_contra hle1
            have : q0.den = 1 := by have := q0.den_pos; omega
            rw [this, PStar_one] at heq; omega
          obtain ⟨p, ν, hp, hν, hpeq, hdvd, _⟩ := exists_prime_pow_eq_PStar hq1
          rw [heq] at hpeq
          exact hdiv ⟨hpeq ▸ hdvd, p, ν, hp, hν, hpeq⟩
        obtain ⟨R₀, hR₀sub, hR₀P, hR₀end, hR₀card⟩ := ih (by omega) q0 hPq'
        refine ⟨R₀, hR₀sub, fun n hn => by have := hR₀P n hn; omega, hR₀end, hR₀card.trans hstep_mono⟩
  -- Apply hbig_ind at d = y_big - y_small to q0 = r - ∑ n ∈ A, 1/n!
  obtain ⟨Rrem, hRrem_sub, _, hRrem_end, hRrem_card⟩ :=
    hbig_ind (y_big - y_small) (by omega) (r - ∑ n ∈ A, (1 : ℚ) / (n : ℚ)) (by omega)
  set R' : Finset ℕ := A \ Rrem
  set r' : ℚ := r - ∑ n ∈ R', (1 : ℚ) / (n : ℚ)
  have hr'_eq : r' = (r - ∑ n ∈ A, (1 : ℚ) / (n : ℚ)) + ∑ n ∈ Rrem, (1 : ℚ) / (n : ℚ) := by
    have hsplit : ∑ n ∈ R', (1 : ℚ) / (n : ℚ) + ∑ n ∈ Rrem, (1 : ℚ) / (n : ℚ) =
        ∑ n ∈ A, (1 : ℚ) / (n : ℚ) := Finset.sum_sdiff hRrem_sub
    dsimp [r']
    linarith
  have hPr' : PStar r'.den ≤ y_small := hr'_eq ▸ hRrem_end
  -- Now bound (r' : ℝ): decompose as (r - ∑_{Icc L x} 1/n) + ∑_{Icc L x, PStar > y_big} 1/n + ∑_{Rrem} 1/n!
  have hL_ge : α * (x : ℝ) ≤ (L : ℝ) := Nat.le_ceil _
  have hL_lt : (L : ℝ) < α * (x : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hL_pos : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr (by
    intro hz; have h0 := Nat.ceil_eq_zero.mp hz; linarith [mul_pos (show 0 < α by linarith only [hα_lo]) hxpos])
  have hLR_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hL_le_x : L ≤ x := by
    have hx10 : (10 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 10 ≤ x)
    have hle : (L : ℝ) ≤ (x : ℝ) := by nlinarith only [hL_lt, hα_hi, hx10]
    exact_mod_cast hle
  set BadA : Finset ℕ := (Finset.Icc L x).filter (fun n => ¬ PStar n ≤ y_big)
  have hA_split : ∑ n ∈ Finset.Icc L x, (1 : ℝ) / (n : ℝ) =
      (∑ n ∈ A, (1 : ℝ) / (n : ℝ)) + ∑ n ∈ BadA, (1 : ℝ) / (n : ℝ) :=
    (Finset.sum_filter_add_sum_filter_not (Finset.Icc L x) (fun n => PStar n ≤ y_big) _).symm
  have hr'R_eq : (r' : ℝ) = ((r : ℝ) - ∑ n ∈ Finset.Icc L x, (1 : ℝ) / (n : ℝ)) +
      (∑ n ∈ BadA, (1 : ℝ) / (n : ℝ)) + (∑ n ∈ Rrem, (1 : ℝ) / (n : ℝ)) := by
    have h1 : (r' : ℝ) = (r : ℝ) - (∑ n ∈ A, (1 : ℝ) / (n : ℝ)) + ∑ n ∈ Rrem, (1 : ℝ) / (n : ℝ) := by
      rw [hr'_eq]; push_cast; rfl
    linarith only [h1, hA_split]
  -- 1) Bound |(r : ℝ) - ∑_{Icc L x} 1/n| ≤ 10 / x
  have hharm := harmonic_Icc_approx hL_pos hL_le_x
  have hlog_diff : |(r : ℝ) - Real.log ((x : ℝ) / (L : ℝ))| ≤ 4 / (x : ℝ) := by
    have hr_log : (r : ℝ) = Real.log ((x : ℝ) / (α * (x : ℝ))) := by
      rw [show (x : ℝ) / (α * (x : ℝ)) = α⁻¹ by field_simp [hxpos.ne'], Real.log_inv]
      dsimp [α]; rw [Real.log_exp]; ring
    rw [hr_log, Real.log_div hxpos.ne' (by positivity), Real.log_div hxpos.ne' hLR_pos.ne']
    have hsub : (Real.log (x : ℝ) - Real.log (α * (x : ℝ))) - (Real.log (x : ℝ) - Real.log (L : ℝ)) =
        Real.log ((L : ℝ) / (α * (x : ℝ))) := by
      rw [Real.log_div hLR_pos.ne' (by positivity)]; ring
    rw [hsub, abs_of_nonneg (Real.log_nonneg ((one_le_div (by positivity)).mpr hL_ge))]
    have h1 := Real.log_le_sub_one_of_pos (div_pos hLR_pos (by positivity : 0 < α * (x : ℝ)))
    have h2 : (L : ℝ) / (α * (x : ℝ)) - 1 < 1 / (α * (x : ℝ)) := by
      rw [div_sub_one (by positivity), div_lt_div_iff_of_pos_right (by positivity)]
      linarith only [hL_lt]
    have h3 : 1 / (α * (x : ℝ)) ≤ 4 / (x : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hxpos]; nlinarith only [hα_lo, hxpos]
    linarith only [h1, h2, h3]
  have hdiff_small : -(10 / (x : ℝ)) ≤ (r : ℝ) - ∑ n ∈ Finset.Icc L x, (1 : ℝ) / (n : ℝ) ∧
      (r : ℝ) - ∑ n ∈ Finset.Icc L x, (1 : ℝ) / (n : ℝ) ≤ 10 / (x : ℝ) := by
    rw [abs_le] at hlog_diff
    have h2L : 2 / (L : ℝ) ≤ 6 / (x : ℝ) := by
      rw [div_le_div_iff₀ hLR_pos hxpos]; nlinarith only [hL_ge, hα_lo, hxpos]
    have h46 : (4 : ℝ) / (x : ℝ) + 6 / (x : ℝ) = 10 / (x : ℝ) := by ring
    constructor <;> linarith only [hharm.1, hharm.2, hlog_diff.1, hlog_diff.2, h2L, h46]
  -- 2) & 3) Lower & upper bounds on ∑_{BadA} 1/n via badA_sum_bounds!
  obtain ⟨hBadA_lb, hBadA_ub⟩ := badA_sum_bounds hx_big hlog_big hll_big hlog15 hlog13_half hlog13_6
    hα_lo hα_hi rfl hyb_le_x hys_ge
  -- 4) Upper bound on ∑_{Rrem} 1/n < 1/4 (using sum_rpow_neg_two_thirds!)
  have hRrem_ub : ∑ n ∈ Rrem, (1 : ℝ) / (n : ℝ) < 1 / 4 := by
    have hsum_card : ∑ n ∈ Rrem, (1 : ℝ) / (n : ℝ) ≤ (Rrem.card : ℝ) / (α * (x : ℝ)) := by
      calc ∑ n ∈ Rrem, (1 : ℝ) / (n : ℝ)
          ≤ ∑ _n ∈ Rrem, (1 : ℝ) / (α * (x : ℝ)) := by
            apply Finset.sum_le_sum
            intro n hn
            have hnL : L ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp (hRrem_sub hn)).1).1
            exact one_div_le_one_div_of_le (by positivity) (hL_ge.trans (by exact_mod_cast hnL))
        _ = (Rrem.card : ℝ) / (α * (x : ℝ)) := by simp [div_eq_mul_inv]
    have hcard_le : (Rrem.card : ℝ) ≤
        101 * (x : ℝ) ^ ((2 : ℝ) / 3) * (Real.log (x : ℝ)) ^ 2 * (3 * (y_big : ℝ) ^ ((1 : ℝ) / 3)) + 2 * (y_big : ℝ) := by
      have h1 : ∑ m ∈ Finset.Ioc y_small (y_small + (y_big - y_small)),
            (101 * ((x : ℝ) / (m : ℝ)) ^ ((2 : ℝ) / 3) * (Real.log (x : ℝ)) ^ 2 + 2) ≤
          ∑ m ∈ Finset.Icc 1 y_big,
            (101 * ((x : ℝ) / (m : ℝ)) ^ ((2 : ℝ) / 3) * (Real.log (x : ℝ)) ^ 2 + 2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro m hm; rw [Finset.mem_Ioc] at hm; rw [Finset.mem_Icc]; omega
        · intro _ _ _; positivity
      have h1' : ∑ m ∈ Finset.Icc 1 y_big,
            (101 * ((x : ℝ) / (m : ℝ)) ^ ((2 : ℝ) / 3) * (Real.log (x : ℝ)) ^ 2 + 2) =
          (∑ m ∈ Finset.Icc 1 y_big, 101 * ((x : ℝ) / (m : ℝ)) ^ ((2 : ℝ) / 3) * (Real.log (x : ℝ)) ^ 2) +
            ∑ _m ∈ Finset.Icc 1 y_big, (2 : ℝ) := Finset.sum_add_distrib
      have hpart1 : ∑ m ∈ Finset.Icc 1 y_big, 101 * ((x : ℝ) / (m : ℝ)) ^ ((2 : ℝ) / 3) * (Real.log (x : ℝ)) ^ 2 =
          101 * (x : ℝ) ^ ((2 : ℝ) / 3) * (Real.log (x : ℝ)) ^ 2 *
            ∑ m ∈ Finset.Icc 1 y_big, ((m : ℝ) ^ ((2 : ℝ) / 3))⁻¹ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        rw [Real.div_rpow hxpos.le (Nat.cast_nonneg m), div_eq_mul_inv]
        ring
      have hpart2 : ∑ _m ∈ Finset.Icc 1 y_big, (2 : ℝ) = 2 * (y_big : ℝ) := by simp; ring
      have hsr := sum_rpow_neg_two_thirds y_big
      have hmul := mul_le_mul_of_nonneg_left hsr (by positivity : (0 : ℝ) ≤ 101 * (x : ℝ) ^ ((2 : ℝ) / 3) * (Real.log (x : ℝ)) ^ 2)
      linarith only [hRrem_card, h1, h1', hpart1, hpart2, hmul]
    -- Since y_big ≤ x / (log x)^13: x^(2/3) * (log x)^2 * y_big^(1/3) ≤ x / (log x)^(7/3) ≤ x / log x!
    have hyb_le : (y_big : ℝ) ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ 13 := Nat.floor_le (by positivity)
    have hterm1 : 101 * (x : ℝ) ^ ((2 : ℝ) / 3) * (Real.log (x : ℝ)) ^ 2 * (3 * (y_big : ℝ) ^ ((1 : ℝ) / 3)) ≤
        303 * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 := by
      have hyb13 : (y_big : ℝ) ^ ((1 : ℝ) / 3) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) / (Real.log (x : ℝ)) ^ 4 := by
        have h1 : (y_big : ℝ) ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ 12 := by
          have : (Real.log (x : ℝ)) ^ 12 ≤ (Real.log (x : ℝ)) ^ 13 :=
            pow_le_pow_right₀ (by linarith only [hlog_big]) (by norm_num)
          exact hyb_le.trans (div_le_div_of_nonneg_left hxpos.le (by positivity) this)
        have hr := Real.rpow_le_rpow (Nat.cast_nonneg _) h1 (by positivity : (0 : ℝ) ≤ 1 / 3)
        rw [Real.div_rpow hxpos.le (by positivity), ← Real.rpow_natCast (Real.log (x : ℝ)) 12,
          ← Real.rpow_mul hlogx_pos.le] at hr
        norm_num at hr
        exact_mod_cast hr
      have hmul : (x : ℝ) ^ ((2 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 3) = (x : ℝ) := by
        rw [← Real.rpow_add hxpos]; norm_num
      have hbound := mul_le_mul_of_nonneg_left hyb13
        (by positivity : (0 : ℝ) ≤ 303 * (x : ℝ) ^ ((2 : ℝ) / 3) * (Real.log (x : ℝ)) ^ 2)
      have hrw1 : 101 * (x : ℝ) ^ ((2 : ℝ) / 3) * (Real.log (x : ℝ)) ^ 2 * (3 * (y_big : ℝ) ^ ((1 : ℝ) / 3)) =
          303 * (x : ℝ) ^ ((2 : ℝ) / 3) * (Real.log (x : ℝ)) ^ 2 * (y_big : ℝ) ^ ((1 : ℝ) / 3) := by ring
      have hrw2 : 303 * (x : ℝ) ^ ((2 : ℝ) / 3) * (Real.log (x : ℝ)) ^ 2 *
          ((x : ℝ) ^ ((1 : ℝ) / 3) / (Real.log (x : ℝ)) ^ 4) = 303 * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 := by
        calc 303 * (x : ℝ) ^ ((2 : ℝ) / 3) * (Real.log (x : ℝ)) ^ 2 *
              ((x : ℝ) ^ ((1 : ℝ) / 3) / (Real.log (x : ℝ)) ^ 4)
            = 303 * ((x : ℝ) ^ ((2 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 3)) *
                ((Real.log (x : ℝ)) ^ 2 / (Real.log (x : ℝ)) ^ 4) := by ring
          _ = 303 * (x : ℝ) * ((Real.log (x : ℝ)) ^ 2 / (Real.log (x : ℝ)) ^ 4) := by rw [hmul]
          _ = 303 * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 := by field_simp [hlogx_pos.ne']
      linarith only [hbound, hrw1, hrw2]
    have hterm2 : 2 * (y_big : ℝ) ≤ 2 * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 := by
      have hpow : (Real.log (x : ℝ)) ^ 2 ≤ (Real.log (x : ℝ)) ^ 13 :=
        pow_le_pow_right₀ (by linarith only [hlog_big]) (by norm_num)
      have h1 := hyb_le.trans (div_le_div_of_nonneg_left hxpos.le (by positivity) hpow)
      rw [mul_div_assoc]
      linarith only [h1]
    have hcard_final : (Rrem.card : ℝ) / (α * (x : ℝ)) < 1 / 4 := by
      rw [div_lt_iff₀ (by positivity)]
      have h305 : 303 * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 + 2 * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 =
          305 * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 := by ring
      have h1 : 305 * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 < (1 / 4 : ℝ) * (α * (x : ℝ)) := by
        rw [div_lt_iff₀ (by positivity)]
        have hlog2 : (10000 : ℝ) < (Real.log (x : ℝ)) ^ 2 := by nlinarith only [hlog_big]
        have h0 : (305 : ℝ) < (1 / 4 : ℝ) * α * (Real.log (x : ℝ)) ^ 2 := by nlinarith only [hα_lo, hlog2]
        nlinarith only [h0, hxpos]
      linarith only [hcard_le, hterm1, hterm2, h305, h1]
    linarith only [hsum_card, hcard_final]
  -- Combine into 40 / log y_small < r' < 1 and apply small_prop!
  have hr'_lo : 40 / Real.log (y_small : ℝ) < (r' : ℝ) := by
    have hlog_ys : Real.log (x : ℝ) / 3 ≤ Real.log (y_small : ℝ) := by
      have h1 : (x : ℝ) ^ ((1 : ℝ) / 3) ≤ (y_small : ℝ) := by
        have hgt : (x : ℝ) ^ ((2 : ℝ) / 5) - 1 < (y_small : ℝ) := Nat.sub_one_lt_floor _
        have h2 : (x : ℝ) ^ ((1 : ℝ) / 3) + 1 ≤ (x : ℝ) ^ ((2 : ℝ) / 5) := by
          have hgap : (2 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 15) := by
            have h15 : (2 : ℝ) ^ (15 : ℝ) ≤ (x : ℝ) := by
              have : 2 ^ 15 ≤ (10 ^ 20 : ℕ) := by norm_num
              exact_mod_cast this.trans hx_big
            have hr := Real.rpow_le_rpow (by positivity) h15 (by positivity : (0 : ℝ) ≤ 1 / 15)
            rw [← Real.rpow_mul (by positivity)] at hr; norm_num at hr; exact hr
          have hm : (x : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 15) = (x : ℝ) ^ ((2 : ℝ) / 5) := by
            rw [← Real.rpow_add hxpos]; norm_num
          have hge1 : (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) :=
            Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ x)) (by norm_num)
          nlinarith only [hgap, hm, hge1]
        linarith only [hgt, h2]
      have h2 := Real.log_le_log (by positivity) h1
      rw [Real.log_rpow hxpos] at h2
      linarith only [h2]
    have h40 : 40 / Real.log (y_small : ℝ) ≤ 120 / Real.log (x : ℝ) := by
      calc 40 / Real.log (y_small : ℝ) ≤ 40 / (Real.log (x : ℝ) / 3) :=
            div_le_div_of_nonneg_left (by norm_num) (by positivity) hlog_ys
        _ = 120 / Real.log (x : ℝ) := by field_simp [hlogx_pos.ne']; ring
    have h10x : 10 / (x : ℝ) ≤ 1 / Real.log (x : ℝ) := by
      rw [div_le_div_iff₀ hxpos hlogx_pos]
      have h1 : (x : ℝ) ^ ((1 : ℝ) / 5) ≤ (x : ℝ) :=
        Real.rpow_le_self_of_one_le (by exact_mod_cast (by omega : 1 ≤ x)) (by norm_num)
      rw [pow_one] at hlog1_5
      linarith only [hlog1_5, h1]
    have hRrem_nn : 0 ≤ ∑ n ∈ Rrem, (1 : ℝ) / (n : ℝ) := Finset.sum_nonneg (fun _ _ => by positivity)
    have h121 : 120 / Real.log (x : ℝ) + 1 / Real.log (x : ℝ) < 200 / Real.log (x : ℝ) := by
      rw [← add_div]; exact div_lt_div_of_pos_right (by norm_num) hlogx_pos
    linarith only [hr'R_eq, hdiff_small.1, hBadA_lb, hRrem_nn, h40, h10x, h121]
  have hr'_hi : (r' : ℝ) < 1 := by
    have h10x : 10 / (x : ℝ) < 1 / 4 := by
      rw [div_lt_iff₀ hxpos]
      have hx100 : (100 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 100 ≤ x)
      linarith only [hx100]
    linarith only [hr'R_eq, hdiff_small.2, hBadA_ub, hRrem_ub, h10x]
  obtain ⟨S, hSprop, hSsum⟩ := small_prop hys_ge hPr' hr'_lo hr'_hi
  -- Verify S and R' are disjoint: every n ∈ S has n ≤ y_small^2 ≤ x^(4/5) < α * x ≤ L ≤ m for m ∈ R'!
  have hys2_lt_L : y_small ^ 2 < L := by
    have h1 : ((y_small ^ 2 : ℕ) : ℝ) ≤ (x : ℝ) ^ ((4 : ℝ) / 5) := by
      have hys : (y_small : ℝ) ≤ (x : ℝ) ^ ((2 : ℝ) / 5) := Nat.floor_le (by positivity)
      have hsq := pow_le_pow_left₀ (Nat.cast_nonneg _) hys 2
      rw [← Real.rpow_natCast ((x : ℝ) ^ ((2 : ℝ) / 5)) 2, ← Real.rpow_mul hxpos.le] at hsq
      norm_num at hsq
      exact_mod_cast hsq
    have h2 : (x : ℝ) ^ ((4 : ℝ) / 5) < α * (x : ℝ) := by
      have h15 : (3 : ℝ) < (x : ℝ) ^ ((1 : ℝ) / 5) := by
        have h3 : (3 : ℝ) ^ (5 : ℝ) < (x : ℝ) := by
          have : 3 ^ 5 < (10 ^ 20 : ℕ) := by norm_num
          exact_mod_cast this.trans_le hx_big
        have hr := Real.rpow_lt_rpow (by positivity) h3 (by positivity : (0 : ℝ) < 1 / 5)
        rw [← Real.rpow_mul (by positivity)] at hr; norm_num at hr; exact hr
      have hm : (x : ℝ) ^ ((4 : ℝ) / 5) * (x : ℝ) ^ ((1 : ℝ) / 5) = (x : ℝ) := by
        rw [← Real.rpow_add hxpos]; norm_num
      have hx45 : 0 < (x : ℝ) ^ ((4 : ℝ) / 5) := Real.rpow_pos_of_pos hxpos ((4 : ℝ) / 5)
      nlinarith only [h15, hm, hα_lo, hx45]
    have hlt : ((y_small ^ 2 : ℕ) : ℝ) < (L : ℝ) := by linarith only [h1, h2, hL_ge]
    exact_mod_cast hlt
  have hdisjSR : Disjoint S R' := by
    rw [Finset.disjoint_left]
    intro n hnS hnR
    have h1 := (hSprop n hnS).2
    have h2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp hnR).1).1).1
    omega
  refine ⟨S ∪ R', ?_, ?_⟩
  · intro n hn
    rcases Finset.mem_union.mp hn with hnS | hnR
    · obtain ⟨h1, h2⟩ := hSprop n hnS
      exact Finset.mem_Icc.mpr ⟨h1, by omega⟩
    · have hI := Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp hnR).1).1
      exact Finset.mem_Icc.mpr ⟨by omega, hI.2⟩
  · rw [Finset.sum_union hdisjSR, hSsum]
    dsimp [r']
    ring

end E292Part4




namespace E292Final

open Finset Filter Real Asymptotics E292Part1 E292Part4
open scoped Classical

lemma martin_upper_bound : OMA.R_Erdos292_erdos_292_variants_martin_R1.H1 := by
  unfold OMA.R_Erdos292_erdos_292_variants_martin_R1.H1
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp exists_egyptian_of_PStar_le
  have hlog_tend : Tendsto (fun x : ℕ => Real.log (x : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hll_tend : Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ))) Filter.atTop Filter.atTop :=
    tendsto_log_atTop.comp hlog_tend
  have hxdiv_tend : Tendsto (fun x : ℕ => (x : ℝ) / Real.log (x : ℝ)) Filter.atTop Filter.atTop := by
    have h1 := eventually_log_pow_le_rpow (k := 1) (ε := (1 : ℝ) / 2) (c := 1) (by norm_num) (by norm_num)
    have hsq : Tendsto (fun x : ℕ => (x : ℝ) ^ ((1 : ℝ) / 2)) Filter.atTop Filter.atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp tendsto_natCast_atTop_atTop
    rw [tendsto_atTop]
    intro B
    filter_upwards [h1, hsq.eventually_ge_atTop B, Filter.eventually_ge_atTop 3] with x hx1 hxB hx3
    have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
    have hlog_pos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
    rw [pow_one, one_mul] at hx1
    have hmul : (x : ℝ) ^ ((1 : ℝ) / 2) * (x : ℝ) ^ ((1 : ℝ) / 2) = (x : ℝ) := by
      rw [← Real.rpow_add hxpos]; norm_num
    rw [le_div_iff₀ hlog_pos]
    have h2 := mul_le_mul_of_nonneg_left hx1 (by positivity : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2))
    nlinarith [Real.rpow_pos_of_pos hxpos ((1 : ℝ) / 2)]
  have hlog14_half := eventually_log_pow_le_rpow (k := 14) (ε := (1 : ℝ) / 2) (c := (1 : ℝ) / 100) (by norm_num) (by norm_num)
  have hlog14_6 := eventually_log_pow_le_rpow (k := 14) (ε := (1 : ℝ) / 6) (c := (1 : ℝ) / 100) (by norm_num) (by norm_num)
  have hlog1_4 := eventually_log_pow_le_rpow (k := 1) (ε := (1 : ℝ) / 4) (c := 1) (by norm_num) (by norm_num)
  refine Asymptotics.IsBigO.of_bound 2000 ?_
  filter_upwards [Filter.eventually_ge_atTop (max 10000 X₀),
    hxdiv_tend.eventually_ge_atTop ((max 100 X₀ : ℕ) + 2 : ℝ),
    hlog_tend.eventually_ge_atTop 1000,
    hll_tend.eventually_ge_atTop 10,
    hlog14_half, hlog14_6, hlog1_4]
    with x hx_big hxdiv_big hlog_big hll_big h14_half h14_6 h1_4
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hlogx_pos : 0 < Real.log (x : ℝ) := by linarith
  have hll_pos : 0 < Real.log (Real.log (x : ℝ)) := by linarith
  set x' : ℕ := ⌊(x : ℝ) / Real.log (x : ℝ)⌋₊
  have hx'_ge : max 100 X₀ ≤ x' := by
    apply Nat.le_floor
    have : ((max 100 X₀ : ℕ) : ℝ) ≤ (x : ℝ) / Real.log (x : ℝ) := by linarith
    exact this
  have hx'_ge100 : 100 ≤ x' := le_trans (le_max_left _ _) hx'_ge
  have hx'_geX₀ : X₀ ≤ x' := le_trans (le_max_right _ _) hx'_ge
  have hx'_le : (x' : ℝ) ≤ (x : ℝ) / Real.log (x : ℝ) := Nat.floor_le (by positivity)
  have hx'_gt : (x : ℝ) / (2 * Real.log (x : ℝ)) ≤ (x' : ℝ) := by
    have h1 : (x : ℝ) / Real.log (x : ℝ) - 1 < (x' : ℝ) := Nat.sub_one_lt_floor _
    have h2 : (2 : ℝ) ≤ (x : ℝ) / Real.log (x : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) (max 100 X₀)]
    have heq : (x : ℝ) / (2 * Real.log (x : ℝ)) = ((x : ℝ) / Real.log (x : ℝ)) / 2 := by ring
    linarith only [h1, h2, heq]
  have hx'_pos : (0 : ℝ) < (x' : ℝ) := by exact_mod_cast (by omega : 0 < x')
  have hx'_le_x : x' ≤ x := by
    have : (x' : ℝ) ≤ (x : ℝ) := hx'_le.trans (div_le_self hxpos.le (by linarith))
    exact_mod_cast this
  have hlogx'_pos : 0 < Real.log (x' : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x'))
  have hlogx'_le : Real.log (x' : ℝ) ≤ Real.log (x : ℝ) :=
    Real.log_le_log hx'_pos (by exact_mod_cast hx'_le_x)
  set y : ℝ := (x' : ℝ) / (Real.log (x' : ℝ)) ^ 13
  have hy_ge : (x : ℝ) / (2 * (Real.log (x : ℝ)) ^ 14) ≤ y := by
    dsimp [y]
    have hden : (Real.log (x' : ℝ)) ^ 13 ≤ (Real.log (x : ℝ)) ^ 13 :=
      pow_le_pow_left₀ hlogx'_pos.le hlogx'_le 13
    calc (x : ℝ) / (2 * (Real.log (x : ℝ)) ^ 14)
        = ((x : ℝ) / (2 * Real.log (x : ℝ))) / (Real.log (x : ℝ)) ^ 13 := by
          field_simp [hlogx_pos.ne']
      _ ≤ (x' : ℝ) / (Real.log (x : ℝ)) ^ 13 :=
          div_le_div_of_nonneg_right hx'_gt (by positivity)
      _ ≤ (x' : ℝ) / (Real.log (x' : ℝ)) ^ 13 :=
          div_le_div_of_nonneg_left hx'_pos.le (by positivity) hden
  have hy_le_x : y ≤ (x : ℝ) := by
    dsimp [y]
    have h1 : (1 : ℝ) ≤ Real.log (x' : ℝ) := by
      have h4 : (4 : ℝ) ≤ (x' : ℝ) := by exact_mod_cast (by omega : 4 ≤ x')
      have h2 := Real.log_le_log (by norm_num) h4
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow] at h2
      push_cast at h2; linarith [Real.log_two_gt_d9]
    have h2 : (1 : ℝ) ≤ (Real.log (x' : ℝ)) ^ 13 := one_le_pow₀ h1
    exact (div_le_self hx'_pos.le h2).trans (by exact_mod_cast hx'_le_x)
  have hy_ge_sqrt : Real.sqrt (x : ℝ) ≤ y := by
    have h1 : Real.sqrt (x : ℝ) ≤ (x : ℝ) / (2 * (Real.log (x : ℝ)) ^ 14) := by
      rw [le_div_iff₀ (by positivity), Real.sqrt_eq_rpow]
      have hm : (x : ℝ) ^ ((1 : ℝ) / 2) * (x : ℝ) ^ ((1 : ℝ) / 2) = (x : ℝ) := by
        rw [← Real.rpow_add hxpos]; norm_num
      nlinarith [Real.rpow_pos_of_pos hxpos ((1 : ℝ) / 2)]
    linarith
  -- Every k ∈ (x', x] with PStar k ≤ y belongs to Erdos292.A!
  have hmemA : ∀ k ∈ Finset.Icc 1 x, x' < k → (PStar k : ℝ) ≤ y → k ∈ Erdos292.A := by
    intro k hk hkx' hPk
    set r : ℚ := 1 - (1 : ℚ) / (k : ℚ)
    have hk100 : 100 < k := by omega
    have hr_lo : (9 / 10 : ℝ) ≤ (r : ℝ) := by
      dsimp [r]; push_cast
      have hkR : (100 : ℝ) < (k : ℝ) := by exact_mod_cast hk100
      have h1 : (1 : ℝ) / (k : ℝ) ≤ 1 / 10 :=
        one_div_le_one_div_of_le (by norm_num) (by linarith)
      linarith
    have hr_hi : (r : ℝ) < 1 := by
      dsimp [r]; push_cast
      have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
      linarith [one_div_pos.mpr hkpos]
    have hPr : PStar r.den ≤ PStar k := by
      have h1 := PStar_rat_sub_den_le 1 ((1 : ℚ) / (k : ℚ))
      rw [show (1 : ℚ).den = 1 from rfl, PStar_one, PStar_rat_inv_nat_den (by omega : 0 < k)] at h1
      exact h1.trans (max_le (PStar_pos (by omega)) le_rfl)
    have hPr_le : (PStar r.den : ℝ) ≤ (x' : ℝ) / (Real.log (x' : ℝ)) ^ 13 :=
      (by exact_mod_cast hPr : (PStar r.den : ℝ) ≤ (PStar k : ℝ)).trans hPk
    obtain ⟨E, hEsub, hEsum⟩ := hX₀ x' hx'_geX₀ r hr_lo hr_hi hPr_le
    have hk_notMem : k ∉ E := by
      intro hmem
      have := (Finset.mem_Icc.mp (hEsub hmem)).2
      omega
    refine ⟨insert k E, ?_, Finset.mem_insert_self k E, ?_⟩
    · intro m hm
      rcases Finset.mem_insert.mp hm with rfl | hmE
      · exact Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
      · have hI := Finset.mem_Icc.mp (hEsub hmE)
        exact Finset.mem_Icc.mpr ⟨hI.1, by omega⟩
    · rw [Finset.sum_insert hk_notMem, hEsum]
      dsimp [r]; ring
  -- Bound (Erdos292.Aᶜ ∩ Set.Icc 1 x).ncard by x' + #{k ∈ Icc 1 x : y < PStar k}
  set BadSet : Finset ℕ := Finset.Icc 1 x' ∪ (Finset.Icc 1 x).filter (fun k => y < (PStar k : ℝ))
  have hsub_set : Erdos292.Aᶜ ∩ Set.Icc 1 x ⊆ (BadSet : Set ℕ) := by
    intro k hk
    rw [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_Icc] at hk
    rw [Finset.mem_coe, Finset.mem_union]
    by_cases hkx' : k ≤ x'
    · exact Or.inl (Finset.mem_Icc.mpr ⟨hk.2.1, hkx'⟩)
    · right
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hk.2, ?_⟩
      by_contra hle
      push Not at hle
      exact hk.1 (hmemA k (Finset.mem_Icc.mpr hk.2) (by omega) hle)
  have hncard_le : ((Erdos292.Aᶜ ∩ Set.Icc 1 x).ncard : ℝ) ≤
      (x' : ℝ) + (((Finset.Icc 1 x).filter (fun k => y < (PStar k : ℝ))).card : ℝ) := by
    have h1 : (Erdos292.Aᶜ ∩ Set.Icc 1 x).ncard ≤ BadSet.card := by
      calc (Erdos292.Aᶜ ∩ Set.Icc 1 x).ncard ≤ (BadSet : Set ℕ).ncard :=
            Set.ncard_le_ncard hsub_set BadSet.finite_toSet
        _ = BadSet.card := Set.ncard_coe_finset BadSet
    have h2 : BadSet.card ≤ x' + ((Finset.Icc 1 x).filter (fun k => y < (PStar k : ℝ))).card := by
      calc BadSet.card ≤ (Finset.Icc 1 x').card + ((Finset.Icc 1 x).filter (fun k => y < (PStar k : ℝ))).card :=
            Finset.card_union_le _ _
        _ = x' + _ := by simp
    exact_mod_cast h1.trans h2
  have hcard_ub := card_PStar_gt_le (by omega) hy_ge_sqrt hy_le_x
  -- Show each term divided by x is O(log log x / log x):
  have hlog_xy : Real.log ((x : ℝ) / y) ≤ 15 * Real.log (Real.log (x : ℝ)) := by
    have hy_pos : 0 < y := lt_of_lt_of_le (Real.sqrt_pos.mpr hxpos) hy_ge_sqrt
    have hxy : (x : ℝ) / y ≤ 2 * (Real.log (x : ℝ)) ^ 14 := by
      rw [div_le_iff₀ hy_pos]
      have h1 := (div_le_iff₀ (by positivity : 0 < 2 * (Real.log (x : ℝ)) ^ 14)).mp hy_ge
      linarith only [h1]
    have h1 := Real.log_le_log (div_pos hxpos hy_pos) hxy
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h1
    push_cast at h1
    have h2 : Real.log 2 ≤ Real.log (Real.log (x : ℝ)) := by linarith only [Real.log_two_lt_d9, hll_big]
    linarith only [h1, h2]
  have hterm_sq : 2 * (x : ℝ) / Real.sqrt y ≤ 2 * (x : ℝ) / Real.log (x : ℝ) := by
    have hsqy : Real.log (x : ℝ) ≤ Real.sqrt y := by
      have h1 : (x : ℝ) ^ ((1 : ℝ) / 4) ≤ Real.sqrt y := by
        have h2 := Real.sqrt_le_sqrt hy_ge_sqrt
        have h3 : Real.sqrt (Real.sqrt (x : ℝ)) = (x : ℝ) ^ ((1 : ℝ) / 4) := by
          rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hxpos.le]; norm_num
        linarith only [h2, h3]
      rw [pow_one, one_mul] at h1_4
      linarith only [h1, h1_4]
    exact div_le_div_of_nonneg_left (by positivity) hlogx_pos hsqy
  have hterm_cub : 2 * (x : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 3) / y ≤ 2 * (x : ℝ) / Real.log (x : ℝ) := by
    have hy_pos : 0 < y := lt_of_lt_of_le (Real.sqrt_pos.mpr hxpos) hy_ge_sqrt
    rw [div_le_div_iff₀ hy_pos hlogx_pos]
    have h1 : (x : ℝ) ^ ((1 : ℝ) / 3) * Real.log (x : ℝ) ≤ y := by
      rw [pow_one, one_mul] at h1_4
      have h2 : (x : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 4) = (x : ℝ) ^ ((7 : ℝ) / 12) := by
        rw [← Real.rpow_add hxpos]; norm_num
      have h3 : (x : ℝ) ^ ((7 : ℝ) / 12) ≤ (x : ℝ) ^ ((5 : ℝ) / 6) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ x)) (by norm_num)
      have h4 : 50 * (x : ℝ) ^ ((5 : ℝ) / 6) ≤ (x : ℝ) / (2 * (Real.log (x : ℝ)) ^ 14) := by
        rw [le_div_iff₀ (by positivity)]
        have hm : (x : ℝ) ^ ((5 : ℝ) / 6) * (x : ℝ) ^ ((1 : ℝ) / 6) = (x : ℝ) := by
          rw [← Real.rpow_add hxpos]; norm_num
        have hprod := mul_le_mul_of_nonneg_left h14_6 (by positivity : (0 : ℝ) ≤ (x : ℝ) ^ ((5 : ℝ) / 6))
        have hx56 : 0 < (x : ℝ) ^ ((5 : ℝ) / 6) := Real.rpow_pos_of_pos hxpos _
        nlinarith only [hprod, hm, hx56]
      have h5 := mul_le_mul_of_nonneg_left h1_4 (by positivity : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3))
      have hx56 : 0 < (x : ℝ) ^ ((5 : ℝ) / 6) := Real.rpow_pos_of_pos hxpos _
      linarith only [h5, h2, h3, h4, hy_ge, hx56]
    have h2x := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * (x : ℝ))
    linarith only [h2x]
  have hcomb : ((Erdos292.Aᶜ ∩ Set.Icc 1 x).ncard : ℝ) ≤
      2000 * (x : ℝ) * Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ) := by
    have h1 : 64 * (x : ℝ) * (Real.log ((x : ℝ) / y) + 1) / Real.log (x : ℝ) ≤
        1024 * (x : ℝ) * Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ) := by
      apply div_le_div_of_nonneg_right _ hlogx_pos.le
      nlinarith only [hlog_xy, hll_big, hxpos]
    have h2 : (x : ℝ) / Real.log (x : ℝ) ≤ (x : ℝ) * Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ) := by
      apply div_le_div_of_nonneg_right _ hlogx_pos.le
      nlinarith only [hll_big, hxpos]
    have h3 : 2 * (x : ℝ) / Real.log (x : ℝ) ≤ 2 * ((x : ℝ) * Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ)) := by
      rw [mul_div_assoc]; linarith only [h2]
    have h4 : 1024 * (x : ℝ) * Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ) +
        5 * ((x : ℝ) * Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ)) ≤
        2000 * (x : ℝ) * Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ) := by
      have hnn : (0 : ℝ) ≤ (x : ℝ) * Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ) := by positivity
      have heq1 : 1024 * (x : ℝ) * Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ) =
          1024 * ((x : ℝ) * Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ)) := by ring
      have heq2 : 2000 * (x : ℝ) * Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ) =
          2000 * ((x : ℝ) * Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ)) := by ring
      linarith only [hnn, heq1, heq2]
    linarith only [hncard_le, hx'_le, hcard_ub, hterm_sq, hterm_cub, h1, h2, h3, h4]
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  rw [div_le_iff₀ hxpos]
  have hrw : 2000 * (Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ)) * (x : ℝ) =
      2000 * (x : ℝ) * Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ) := by ring
  linarith only [hcomb, hrw]

end E292Final

theorem OMA.solution : OMA.R_Erdos292_erdos_292_variants_martin_R1.H1 :=
  E292Final.martin_upper_bound
