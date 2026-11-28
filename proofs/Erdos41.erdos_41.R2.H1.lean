import OMAReductions.R_Erdos41_erdos_41_R2

-- Step Erdos41.erdos_41.R2.H1: the regular case of Erdős Problem 41.
-- No B_3 sequence f has f n / (n+1)^3 convergent (Helm, On the distribution of B_3-sequences,
-- J. Number Theory 58 (1996) 124-129). Elementary route: for j < i < k the value f i + f j - f k
-- determines the triple, so at most X triples have value in (0, X]; with X = f m, each dyadic scale
-- n = 2^s m supplies m^3/1080 such triples, and J scales exceed f m once J > 17280 L.
-- Credit: @ehsanmok

namespace OMA.E41
open Filter


lemma inj_core {f : ℕ → ℕ} (hf : StrictMono f) (hB : Erdos41.NtupleCondition (Set.range f) 3)
    {i j k i' j' k' : ℕ} (hji : j < i) (hik : i < k) (hji' : j' < i') (hik' : i' < k')
    (h : f i + f j + f k' = f i' + f j' + f k) : i = i' ∧ j = j' ∧ k = k' := by
  have hm : (f i ::ₘ f j ::ₘ {f k'} : Multiset ℕ) = f i' ::ₘ f j' ::ₘ {f k} := by
    apply hB
    · intro x hx
      simp only [Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> exact Set.mem_range_self _
    · intro x hx
      simp only [Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> exact Set.mem_range_self _
    · simp
    · simp
    · simp only [Multiset.sum_cons, Multiset.sum_singleton]
      omega
  have h1 : f k ∈ (f i ::ₘ f j ::ₘ {f k'} : Multiset ℕ) := by
    rw [hm]; simp
  have h2 : f i ∈ (f i' ::ₘ f j' ::ₘ {f k} : Multiset ℕ) := by
    rw [← hm]; simp
  have h3 : f i' ∈ (f i ::ₘ f j ::ₘ {f k'} : Multiset ℕ) := by
    rw [hm]; simp
  simp only [Multiset.mem_cons, Multiset.mem_singleton, hf.injective.eq_iff] at h1 h2 h3
  have hkk : k = k' := by omega
  subst hkk
  have hii : i = i' := by omega
  subst hii
  have hjj : f j = f j' := by omega
  exact ⟨rfl, hf.injective hjj, rfl⟩

lemma count_bound {f : ℕ → ℕ} (hf : StrictMono f) (hB : Erdos41.NtupleCondition (Set.range f) 3)
    (X : ℕ) (T : Finset (ℕ × ℕ × ℕ))
    (hT : ∀ p ∈ T, p.2.1 < p.1 ∧ p.1 < p.2.2 ∧ f p.2.2 < f p.1 + f p.2.1 ∧
      f p.1 + f p.2.1 ≤ f p.2.2 + X) : T.card ≤ X := by
  have key : T.card ≤ (Finset.Ioc 0 X).card := by
    apply Finset.card_le_card_of_injOn (fun p => f p.1 + f p.2.1 - f p.2.2)
    · intro p hp
      have := hT p hp
      simp only [Finset.coe_Ioc, Set.mem_Ioc]
      omega
    · intro p hp p' hp' hpp
      obtain ⟨i, j, k⟩ := p
      obtain ⟨i', j', k'⟩ := p'
      have h1 := hT _ hp
      have h2 := hT _ hp'
      simp only at h1 h2 hpp
      have h : f i + f j + f k' = f i' + f j' + f k := by omega
      obtain ⟨rfl, rfl, rfl⟩ := inj_core hf hB h1.1 h1.2.1 h2.1 h2.2.1 h
      rfl
  simpa using key

lemma cube_le {f : ℕ → ℕ} (hf : StrictMono f) (hB : Erdos41.NtupleCondition (Set.range f) 3)
    (q : ℕ) : q ^ 3 ≤ 3 * f (3 * q) + 1 := by
  set S : Finset (ℕ × ℕ × ℕ) := Finset.Ico q (2 * q) ×ˢ (Finset.range q ×ˢ Finset.Ico (2 * q) (3 * q))
    with hS
  have hcard : S.card = q ^ 3 := by
    rw [hS, Finset.card_product, Finset.card_product, Nat.card_Ico, Nat.card_Ico, Finset.card_range]
    have e1 : 2 * q - q = q := by omega
    have e2 : 3 * q - 2 * q = q := by omega
    rw [e1, e2]; ring
  have key : S.card ≤ (Finset.range (3 * f (3 * q) + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun p => f p.1 + f p.2.1 + f (3 * q) - f p.2.2)
    · intro p hp
      obtain ⟨i, j, k⟩ := p
      simp only [hS, Finset.coe_product, Set.mem_prod, Finset.coe_Ico, Finset.coe_range,
        Set.mem_Ico, Set.mem_Iio] at hp
      have a1 : f i ≤ f (3 * q) := hf.monotone (by omega)
      have a2 : f j ≤ f (3 * q) := hf.monotone (by omega)
      simp only [Finset.coe_range, Set.mem_Iio]
      omega
    · intro p hp p' hp' hpp
      obtain ⟨i, j, k⟩ := p
      obtain ⟨i', j', k'⟩ := p'
      simp only [hS, Finset.coe_product, Set.mem_prod, Finset.coe_Ico, Finset.coe_range,
        Set.mem_Ico, Set.mem_Iio] at hp hp'
      simp only at hpp
      have b1 : f k ≤ f (3 * q) := hf.monotone (by omega)
      have b2 : f k' ≤ f (3 * q) := hf.monotone (by omega)
      have h : f i + f j + f k' = f i' + f j' + f k := by omega
      obtain ⟨rfl, rfl, rfl⟩ := inj_core hf hB (by omega) (by omega) (by omega) (by omega) h
      rfl
  rw [hcard, Finset.card_range] at key
  exact key

lemma L_pos {f : ℕ → ℕ} (hf : StrictMono f) (hB : Erdos41.NtupleCondition (Set.range f) 3) {L : ℝ}
    (hL : Tendsto (fun n : ℕ => (f n : ℝ) / ((n : ℝ) + 1) ^ 3) atTop (nhds L)) : 0 < L := by
  have h3 : Tendsto (fun q : ℕ => 3 * q) atTop atTop :=
    tendsto_atTop_mono (fun q => (by omega : q ≤ 3 * q)) tendsto_id
  have hL3 := hL.comp h3
  have hev : ∀ᶠ q : ℕ in atTop, (1 / 384 : ℝ) ≤ ((fun n : ℕ => (f n : ℝ) / ((n : ℝ) + 1) ^ 3) ∘
      (fun q : ℕ => 3 * q)) q := by
    rw [eventually_atTop]
    refine ⟨2, fun q hq => ?_⟩
    simp only [Function.comp_apply]
    have hc := cube_le hf hB q
    have hN : (3 * q + 1) ^ 3 ≤ 384 * f (3 * q) := by
      have hq3 : 8 ≤ q ^ 3 := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
      nlinarith [hq3]
    have hR : ((3 * q : ℕ) + 1 : ℝ) ^ 3 ≤ 384 * (f (3 * q) : ℝ) := by
      exact_mod_cast hN
    have hpos : (0 : ℝ) < ((3 * q : ℕ) + 1 : ℝ) ^ 3 := by positivity
    rw [le_div_iff₀ hpos]
    linarith
  have := ge_of_tendsto hL3 hev
  linarith

lemma bounds {f : ℕ → ℕ} {L : ℝ} (hLpos : 0 < L)
    (hL : Tendsto (fun n : ℕ => (f n : ℝ) / ((n : ℝ) + 1) ^ 3) atTop (nhds L))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ x : ℕ, N0 ≤ x → (1 - ε) * L * ((x : ℝ) + 1) ^ 3 ≤ (f x : ℝ) ∧
      (f x : ℝ) ≤ (1 + ε) * L * ((x : ℝ) + 1) ^ 3 := by
  obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.mp hL (ε * L) (mul_pos hε hLpos)
  refine ⟨N0, fun x hx => ?_⟩
  have h := hN0 x hx
  rw [Real.dist_eq, abs_sub_lt_iff] at h
  have hpos : (0 : ℝ) < ((x : ℝ) + 1) ^ 3 := by positivity
  obtain ⟨h1, h2⟩ := h
  constructor
  · have h3 : (1 - ε) * L < (f x : ℝ) / ((x : ℝ) + 1) ^ 3 := by linarith
    rw [lt_div_iff₀ hpos] at h3
    exact h3.le
  · have h3 : (f x : ℝ) / ((x : ℝ) + 1) ^ 3 < (1 + ε) * L := by linarith
    rw [div_lt_iff₀ hpos] at h3
    exact h3.le

lemma real_F2 {K I r N m ε : ℝ} (hKI : K = I + r) (hr : N ≤ 20 * r) (hI : N ≤ 2 * I)
    (hK : K ≤ 3 * N) (hN : 0 ≤ N) (hm : 1 ≤ m) (hmN : 16 * m ≤ N) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hεn : ε * (108 * N ^ 3) ≤ m ^ 3) :
    (1 + ε) * I ^ 3 + (1 + ε) * (m + 1) ^ 3 ≤ (1 - ε) * K ^ 3 := by
  have hI0 : 0 ≤ I := by linarith
  have hr0 : 0 ≤ r := by linarith
  have h1 : 3 * I ^ 2 * r ≤ K ^ 3 - I ^ 3 := by
    subst hKI; nlinarith [mul_nonneg (mul_nonneg hI0 hr0) hr0, pow_nonneg hr0 3]
  have h2 : N ^ 2 / 4 ≤ I ^ 2 := by nlinarith
  have h3 : 3 * (N ^ 2 / 4) * (N / 20) ≤ 3 * I ^ 2 * r := by
    have := mul_le_mul h2 (show N / 20 ≤ r by linarith) (by positivity) (by positivity)
    nlinarith
  have h4 : I ^ 3 ≤ K ^ 3 := pow_le_pow_left₀ hI0 (by linarith) 3
  have h5 : K ^ 3 ≤ (3 * N) ^ 3 := pow_le_pow_left₀ (by linarith) hK 3
  have h6 : (m + 1) ^ 3 ≤ (2 * m) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
  have h7 : (16 * m) ^ 3 ≤ N ^ 3 := pow_le_pow_left₀ (by linarith) hmN 3
  have h8 : (1 + ε) * (m + 1) ^ 3 ≤ 2 * (2 * m) ^ 3 :=
    mul_le_mul (by linarith) h6 (by positivity) (by norm_num)
  have h9 := mul_le_mul_of_nonneg_left h4 hε0
  have h10 := mul_le_mul_of_nonneg_left h5 hε0
  nlinarith

lemma real_F1 {K I r N m ε : ℝ} (hKI : K = I + r) (hr : 10 * r ≤ N) (hNK : N ≤ K) (hN : 0 < N)
    (hm : 1 ≤ m) (hmN : 16 * m ≤ N) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 100) :
    (1 + ε) * K ^ 3 + (1 + ε) * (m + 1) ^ 3 < 2 * ((1 - ε) * I ^ 3) := by
  have hK0 : 0 < K := by linarith
  have hI1 : 9 / 10 * K ≤ I := by linarith
  have h1 : (9 / 10 * K) ^ 3 ≤ I ^ 3 := pow_le_pow_left₀ (by positivity) hI1 3
  have h6 : (m + 1) ^ 3 ≤ (2 * m) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
  have h7 : (16 * m) ^ 3 ≤ K ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
  have h8 : (1 + ε) * (m + 1) ^ 3 ≤ 2 * (2 * m) ^ 3 :=
    mul_le_mul (by linarith) h6 (by positivity) (by norm_num)
  have h9 : (1 + ε) * K ^ 3 ≤ (101 / 100) * K ^ 3 :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have h10 : (99 / 100) * I ^ 3 ≤ (1 - ε) * I ^ 3 :=
    mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (by linarith) 3)
  have hK3 : 0 < K ^ 3 := by positivity
  nlinarith

lemma real_F3 {A B t N m ε : ℝ} (hAB : B = A + t) (hA : 0 ≤ A) (ht : 0 ≤ t) (hB : B ≤ 2 * N)
    (htm : 54 * t * N ^ 2 ≤ m ^ 3) (hεn : ε * (108 * N ^ 3) ≤ m ^ 3) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1 / 100) (hm : 0 ≤ m) :
    (1 + ε) * B ^ 3 ≤ (1 - ε) * A ^ 3 + (1 - ε) * (m + 1) ^ 3 := by
  have hB0 : 0 ≤ B := by linarith
  have h1 : B ^ 3 - A ^ 3 ≤ 3 * t * B ^ 2 := by
    subst hAB; nlinarith [mul_nonneg (mul_nonneg hA ht) ht, pow_nonneg ht 3, mul_nonneg ht (sq_nonneg A)]
  have h2 : B ^ 2 ≤ (2 * N) ^ 2 := pow_le_pow_left₀ hB0 hB 2
  have h3 : 3 * t * B ^ 2 ≤ 3 * t * (2 * N) ^ 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
  have h4 : A ^ 3 ≤ B ^ 3 := pow_le_pow_left₀ hA (by linarith) 3
  have h5 : B ^ 3 ≤ (2 * N) ^ 3 := pow_le_pow_left₀ hB0 hB 3
  have h9 := mul_le_mul_of_nonneg_left h4 hε0
  have h10 := mul_le_mul_of_nonneg_left h5 hε0
  have h6 : m ^ 3 ≤ (m + 1) ^ 3 := pow_le_pow_left₀ hm (by linarith) 3
  have h11 : (99 / 100) * (m + 1) ^ 3 ≤ (1 - ε) * (m + 1) ^ 3 :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hm3 : 0 ≤ m ^ 3 := by positivity
  nlinarith

lemma window {f : ℕ → ℕ} (hf : StrictMono f) {L ε : ℝ} (hLpos : 0 < L) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1 / 100) (N0 m n t : ℕ)
    (hb : ∀ x : ℕ, N0 ≤ x → (1 - ε) * L * ((x : ℝ) + 1) ^ 3 ≤ (f x : ℝ) ∧
      (f x : ℝ) ≤ (1 + ε) * L * ((x : ℝ) + 1) ^ 3)
    (hN : N0 ≤ m) (hm : 5 ≤ m) (hmn : 16 * m ≤ n) (ht1 : 1 ≤ t) (ht : 54 * t * n ^ 2 ≤ m ^ 3)
    (hεn : ε * (108 * (n : ℝ) ^ 3) ≤ (m : ℝ) ^ 3)
    {k r : ℕ} (hk : n < k) (hk2 : k ≤ 2 * n) (hr : n < 20 * r) (hr2 : 10 * r ≤ n) :
    ∃ a : ℕ, a + t ≤ k - r ∧ ∀ j : ℕ, a ≤ j → j < a + t →
      f k < f (k - r) + f j ∧ f (k - r) + f j ≤ f k + f m := by
  have hn0 : 0 < n := by omega
  have htn : 20 * t ≤ n := by
    by_contra hcon
    push_neg at hcon
    have h1 : (16 * m) ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left hmn 3
    have h2 : n ^ 3 < 20 * t * n ^ 2 := by
      have : n * n ^ 2 < 20 * t * n ^ 2 := Nat.mul_lt_mul_of_pos_right hcon (by positivity)
      calc n ^ 3 = n * n ^ 2 := by ring
        _ < _ := this
    nlinarith
  set i := k - r with hi
  have hrk : r ≤ k := by omega
  have hmi : m ≤ i := by omega
  have hN0k : N0 ≤ k := by omega
  have hN0i : N0 ≤ i := by omega
  obtain ⟨hk_lo, hk_hi⟩ := hb k hN0k
  obtain ⟨hi_lo, hi_hi⟩ := hb i hN0i
  obtain ⟨hm_lo, hm_hi⟩ := hb m hN
  have hKI : (k : ℝ) + 1 = ((i : ℝ) + 1) + (r : ℝ) := by
    rw [hi, Nat.cast_sub hrk]; ring
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hmR : (5 : ℝ) ≤ m := by exact_mod_cast hm
  have hmnR : 16 * (m : ℝ) ≤ n := by exact_mod_cast hmn
  have F2 : f i + f m ≤ f k := by
    have hreal := real_F2 (K := (k : ℝ) + 1) (I := (i : ℝ) + 1) (r := (r : ℝ)) (N := (n : ℝ))
      (m := (m : ℝ)) (ε := ε) hKI (by exact_mod_cast hr.le)
      (by have : n ≤ 2 * i + 2 := by omega
          have : (n : ℝ) ≤ 2 * (i : ℝ) + 2 := by exact_mod_cast this
          linarith)
      (by have : (k : ℝ) ≤ 2 * n := by exact_mod_cast hk2
          linarith)
      hnR.le (by linarith) hmnR hε0.le (by linarith) hεn
    have hL := mul_le_mul_of_nonneg_left hreal hLpos.le
    have : (f i : ℝ) + f m ≤ f k := by nlinarith
    exact_mod_cast this
  have F1 : f k + f m < 2 * f i := by
    have hreal := real_F1 (K := (k : ℝ) + 1) (I := (i : ℝ) + 1) (r := (r : ℝ)) (N := (n : ℝ))
      (m := (m : ℝ)) (ε := ε) hKI (by exact_mod_cast hr2)
      (by have : (n : ℝ) < k := by exact_mod_cast hk
          linarith)
      hnR (by linarith) hmnR hε0.le hε1
    have hL := mul_lt_mul_of_pos_left hreal hLpos
    have : (f k : ℝ) + f m < 2 * (f i : ℝ) := by nlinarith
    exact_mod_cast this
  have hex : ∃ j, f k - f i < f j := ⟨i, by omega⟩
  classical
  let a := Nat.find hex
  have ha : f k - f i < f a := Nat.find_spec hex
  have hai : a ≤ i := Nat.find_min' hex (show f k - f i < f i by omega)
  have hma : m < a := by
    by_contra hcon
    push_neg at hcon
    have : f a ≤ f m := hf.monotone hcon
    omega
  have ha1 : f (a - 1) ≤ f k - f i := by
    have := Nat.find_min hex (show a - 1 < a by omega)
    omega
  have hat : a + t ≤ 2 * n := by omega
  have F3 : f (a + t - 1) ≤ f (a - 1) + f m := by
    obtain ⟨hA_lo, hA_hi⟩ := hb (a - 1) (by omega)
    obtain ⟨hB_lo, hB_hi⟩ := hb (a + t - 1) (by omega)
    have hAc : ((a - 1 : ℕ) : ℝ) + 1 = (a : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ a)]; push_cast; ring
    have hBc : ((a + t - 1 : ℕ) : ℝ) + 1 = (a : ℝ) + t := by
      rw [Nat.cast_sub (by omega : 1 ≤ a + t)]; push_cast; ring
    rw [hAc] at hA_lo hA_hi
    rw [hBc] at hB_lo hB_hi
    have hreal := real_F3 (A := (a : ℝ)) (B := (a : ℝ) + t) (t := (t : ℝ)) (N := (n : ℝ))
      (m := (m : ℝ)) (ε := ε) rfl (by positivity) (by positivity)
      (by exact_mod_cast hat) (by exact_mod_cast ht) hεn hε0.le hε1 (by positivity)
    have hL := mul_le_mul_of_nonneg_left hreal hLpos.le
    have : (f (a + t - 1) : ℝ) ≤ f (a - 1) + f m := by nlinarith
    exact_mod_cast this
  have hlast : a + t - 1 < i := by
    have : f (a + t - 1) < f i := by omega
    exact hf.lt_iff_lt.mp this
  refine ⟨a, by omega, fun j hj1 hj2 => ⟨?_, ?_⟩⟩
  · have : f a ≤ f j := hf.monotone hj1
    omega
  · have : f j ≤ f (a + t - 1) := hf.monotone (by omega)
    omega

lemma scales_bound {f : ℕ → ℕ} (hf : StrictMono f) (hB : Erdos41.NtupleCondition (Set.range f) 3)
    (m J X : ℕ) (t : ℕ → ℕ)
    (hgood : ∀ s : ℕ, 4 ≤ s → s < J + 4 → ∀ k r : ℕ, 2 ^ s * m < k → k ≤ 2 * (2 ^ s * m) →
      2 ^ s * m < 20 * r → 10 * r ≤ 2 ^ s * m →
      ∃ a : ℕ, a + t s ≤ k - r ∧ ∀ j : ℕ, a ≤ j → j < a + t s →
        f k < f (k - r) + f j ∧ f (k - r) + f j ≤ f k + X) :
    ∑ s ∈ Finset.Ico 4 (J + 4), (2 ^ s * m) * ((2 ^ s * m) / 10 - (2 ^ s * m) / 20) * t s ≤ X := by
  classical
  have hex : ∀ s k r : ℕ, ∃ a : ℕ, (4 ≤ s ∧ s < J + 4 ∧ 2 ^ s * m < k ∧ k ≤ 2 * (2 ^ s * m) ∧
      2 ^ s * m < 20 * r ∧ 10 * r ≤ 2 ^ s * m) → (a + t s ≤ k - r ∧ ∀ j : ℕ, a ≤ j → j < a + t s →
        f k < f (k - r) + f j ∧ f (k - r) + f j ≤ f k + X) := by
    intro s k r
    by_cases hc : 4 ≤ s ∧ s < J + 4 ∧ 2 ^ s * m < k ∧ k ≤ 2 * (2 ^ s * m) ∧
      2 ^ s * m < 20 * r ∧ 10 * r ≤ 2 ^ s * m
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hc
      obtain ⟨a, ha⟩ := hgood s h1 h2 k r h3 h4 h5 h6
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h => absurd h hc⟩
  choose a ha using hex
  set N : ℕ → ℕ := fun s => 2 ^ s * m with hNdef
  have hNmono : ∀ s s' : ℕ, s < s' → 2 * N s ≤ N s' := by
    intro s s' hss
    simp only [hNdef]
    have : 2 ^ (s + 1) ≤ 2 ^ s' := Nat.pow_le_pow_right (by norm_num) hss
    rw [pow_succ] at this
    nlinarith [Nat.zero_le m]
  let B : ℕ → ℕ → ℕ → Finset (ℕ × ℕ × ℕ) := fun s k r =>
    (Finset.Ico (a s k r) (a s k r + t s)).image (fun j => (k - r, j, k))
  let C : ℕ → ℕ → Finset (ℕ × ℕ × ℕ) := fun s k =>
    (Finset.Ioc (N s / 20) (N s / 10)).biUnion (fun r => B s k r)
  let D : ℕ → Finset (ℕ × ℕ × ℕ) := fun s =>
    (Finset.Ioc (N s) (2 * N s)).biUnion (fun k => C s k)
  let T : Finset (ℕ × ℕ × ℕ) := (Finset.Ico 4 (J + 4)).biUnion D
  have hBcard : ∀ s k r, (B s k r).card = t s := by
    intro s k r
    rw [Finset.card_image_of_injective]
    · simp
    · intro j1 j2 h
      simpa using h
  have hBmem : ∀ s k r p, p ∈ B s k r → p.2.2 = k ∧ p.1 = k - r := by
    intro s k r p hp
    simp only [B, Finset.mem_image] at hp
    obtain ⟨j, _, rfl⟩ := hp
    exact ⟨rfl, rfl⟩
  have hCcard : ∀ s k, N s < k → (C s k).card = (N s / 10 - N s / 20) * t s := by
    intro s k hk
    rw [Finset.card_biUnion]
    · simp [hBcard]
    · intro r1 hr1 r2 hr2 hne
      rw [Function.onFun, Finset.disjoint_left]
      intro p hp1 hp2
      have e1 := hBmem s k r1 p hp1
      have e2 := hBmem s k r2 p hp2
      simp only [Finset.coe_Ioc, Set.mem_Ioc] at hr1 hr2
      have : r1 ≤ N s := le_trans hr1.2 (Nat.div_le_self _ _)
      have : r2 ≤ N s := le_trans hr2.2 (Nat.div_le_self _ _)
      omega
  have hCmem : ∀ s k p, p ∈ C s k → p.2.2 = k := by
    intro s k p hp
    simp only [C, Finset.mem_biUnion] at hp
    obtain ⟨r, _, hp⟩ := hp
    exact (hBmem s k r p hp).1
  have hDcard : ∀ s, (D s).card = N s * ((N s / 10 - N s / 20) * t s) := by
    intro s
    rw [Finset.card_biUnion]
    · rw [Finset.sum_congr rfl (fun k hk => hCcard s k (Finset.mem_Ioc.mp hk).1)]
      simp only [Finset.sum_const, Nat.card_Ioc, smul_eq_mul]
      congr 1
      omega
    · intro k1 _ k2 _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro p hp1 hp2
      exact hne ((hCmem s k1 p hp1).symm.trans (hCmem s k2 p hp2))
  have hDmem : ∀ s p, p ∈ D s → N s < p.2.2 ∧ p.2.2 ≤ 2 * N s := by
    intro s p hp
    simp only [D, Finset.mem_biUnion] at hp
    obtain ⟨k, hk, hp⟩ := hp
    rw [hCmem s k p hp]
    exact Finset.mem_Ioc.mp hk
  have hTcard : T.card = ∑ s ∈ Finset.Ico 4 (J + 4), N s * ((N s / 10 - N s / 20) * t s) := by
    rw [Finset.card_biUnion]
    · exact Finset.sum_congr rfl (fun s _ => hDcard s)
    · intro s1 _ s2 _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro p hp1 hp2
      have h1 := hDmem s1 p hp1
      have h2 := hDmem s2 p hp2
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · have := hNmono s1 s2 h
        omega
      · have := hNmono s2 s1 h
        omega
  have hT : ∀ p ∈ T, p.2.1 < p.1 ∧ p.1 < p.2.2 ∧ f p.2.2 < f p.1 + f p.2.1 ∧
      f p.1 + f p.2.1 ≤ f p.2.2 + X := by
    intro p hp
    simp only [T, D, C, B, Finset.mem_biUnion, Finset.mem_image, Finset.mem_Ioc,
      Finset.mem_Ico] at hp
    obtain ⟨s, ⟨hs1, hs2⟩, k, ⟨hk1, hk2⟩, r, ⟨hr1, hr2⟩, j, ⟨hj1, hj2⟩, rfl⟩ := hp
    have hcond : 4 ≤ s ∧ s < J + 4 ∧ 2 ^ s * m < k ∧ k ≤ 2 * (2 ^ s * m) ∧
        2 ^ s * m < 20 * r ∧ 10 * r ≤ 2 ^ s * m := by
      simp only [hNdef] at hk1 hk2 hr1 hr2
      refine ⟨hs1, hs2, hk1, hk2, ?_, ?_⟩ <;> omega
    obtain ⟨hA1, hA2⟩ := ha s k r hcond
    obtain ⟨hv1, hv2⟩ := hA2 j hj1 hj2
    refine ⟨?_, ?_, hv1, hv2⟩
    · simp only
      omega
    · simp only
      omega
  have hle := count_bound hf hB X T hT
  rw [hTcard] at hle
  calc ∑ s ∈ Finset.Ico 4 (J + 4), (2 ^ s * m) * ((2 ^ s * m) / 10 - (2 ^ s * m) / 20) * t s
      = ∑ s ∈ Finset.Ico 4 (J + 4), N s * ((N s / 10 - N s / 20) * t s) := by
        refine Finset.sum_congr rfl (fun s _ => ?_)
        simp only [hNdef]
        ring
    _ ≤ X := hle

lemma term_eq (J M s : ℕ) (hs : s < J + 4) :
    (2 ^ s * (1080 * 4 ^ (J + 4) * M)) * ((2 ^ s * (1080 * 4 ^ (J + 4) * M)) / 10 -
      (2 ^ s * (1080 * 4 ^ (J + 4) * M)) / 20) * ((1080 * 4 ^ (J + 4) * M) / (54 * 4 ^ s)) =
      1080 ^ 2 * (4 ^ (J + 4) * M) ^ 3 := by
  obtain ⟨d, hd⟩ : ∃ d, J + 4 = s + d := ⟨J + 4 - s, by omega⟩
  rw [hd, pow_add]
  have h4 : (4 : ℕ) ^ s = 2 ^ s * 2 ^ s := by
    rw [← pow_two, ← pow_mul, mul_comm, pow_mul]; norm_num
  have e1 : (2 ^ s * (1080 * (4 ^ s * 4 ^ d) * M)) / 10 = 2 ^ s * (108 * (4 ^ s * 4 ^ d) * M) := by
    apply Nat.div_eq_of_eq_mul_left (by norm_num); ring
  have e2 : (2 ^ s * (1080 * (4 ^ s * 4 ^ d) * M)) / 20 = 2 ^ s * (54 * (4 ^ s * 4 ^ d) * M) := by
    apply Nat.div_eq_of_eq_mul_left (by norm_num); ring
  have e3 : (1080 * (4 ^ s * 4 ^ d) * M) / (54 * 4 ^ s) = 20 * 4 ^ d * M := by
    apply Nat.div_eq_of_eq_mul_left (by positivity); ring
  have e4 : 2 ^ s * (108 * (4 ^ s * 4 ^ d) * M) - 2 ^ s * (54 * (4 ^ s * 4 ^ d) * M) =
      2 ^ s * (54 * (4 ^ s * 4 ^ d) * M) := by
    have : 2 ^ s * (108 * (4 ^ s * 4 ^ d) * M) =
        2 ^ s * (54 * (4 ^ s * 4 ^ d) * M) + 2 ^ s * (54 * (4 ^ s * 4 ^ d) * M) := by ring
    omega
  rw [e1, e2, e3, e4, h4]
  ring

theorem regular_case (f : ℕ → ℕ) (hf : StrictMono f) (hB : Erdos41.NtupleCondition (Set.range f) 3)
    (hL : ∃ L : ℝ, Tendsto (fun n : ℕ => (f n : ℝ) / ((n : ℝ) + 1) ^ 3) atTop (nhds L)) : False := by
  obtain ⟨L, hL⟩ := hL
  have hLpos := L_pos hf hB hL
  obtain ⟨J, hJ⟩ := exists_nat_gt (17280 * L)
  have hε0 : (0 : ℝ) < 1 / (108 * 8 ^ (J + 5)) := by positivity
  have hε1 : (1 : ℝ) / (108 * 8 ^ (J + 5)) ≤ 1 / 100 := by
    apply one_div_le_one_div_of_le (by norm_num)
    have : (1 : ℝ) ≤ 8 ^ (J + 5) := one_le_pow₀ (by norm_num)
    linarith
  obtain ⟨N0, hb⟩ := bounds hLpos hL (1 / (108 * 8 ^ (J + 5))) hε0
  have hMpos : 0 < 4 ^ (J + 4) * (N0 + 5) := by positivity
  have hm_def : 1080 * 4 ^ (J + 4) * (N0 + 5) = 1080 * (4 ^ (J + 4) * (N0 + 5)) := by ring
  have h41 : 1 ≤ 4 ^ (J + 4) := Nat.one_le_pow _ _ (by norm_num)
  have hmM : N0 + 5 ≤ 1080 * 4 ^ (J + 4) * (N0 + 5) := by
    calc N0 + 5 = 1 * 1 * (N0 + 5) := by ring
      _ ≤ 1080 * 4 ^ (J + 4) * (N0 + 5) := by gcongr <;> omega
  have key := scales_bound hf hB (1080 * 4 ^ (J + 4) * (N0 + 5)) J
    (f (1080 * 4 ^ (J + 4) * (N0 + 5))) (fun s => (1080 * 4 ^ (J + 4) * (N0 + 5)) / (54 * 4 ^ s))
    (by
      intro s hs4 hsJ k r hk hk2 hr hr2
      have hpow : (4 : ℕ) ^ s ≤ 4 ^ (J + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
      refine window hf hLpos hε0 hε1 N0 _ (2 ^ s * (1080 * 4 ^ (J + 4) * (N0 + 5))) _ hb
        (by omega) (by omega) ?_ ?_ ?_ ?_ hk hk2 hr hr2
      · have : 2 ^ 4 ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs4
        calc 16 * (1080 * 4 ^ (J + 4) * (N0 + 5)) = 2 ^ 4 * (1080 * 4 ^ (J + 4) * (N0 + 5)) := by norm_num
          _ ≤ 2 ^ s * (1080 * 4 ^ (J + 4) * (N0 + 5)) := Nat.mul_le_mul_right _ this
      · rw [Nat.one_le_div_iff (by positivity)]
        calc 54 * 4 ^ s ≤ 1080 * 4 ^ (J + 4) * 1 := by nlinarith
          _ ≤ 1080 * 4 ^ (J + 4) * (N0 + 5) := by gcongr; omega
      · have h4 : (4 : ℕ) ^ s = 2 ^ s * 2 ^ s := by
          rw [← pow_two, ← pow_mul, mul_comm, pow_mul]; norm_num
        have hdiv := Nat.div_mul_le_self (1080 * 4 ^ (J + 4) * (N0 + 5)) (54 * 4 ^ s)
        calc 54 * ((1080 * 4 ^ (J + 4) * (N0 + 5)) / (54 * 4 ^ s)) *
              (2 ^ s * (1080 * 4 ^ (J + 4) * (N0 + 5))) ^ 2
            = ((1080 * 4 ^ (J + 4) * (N0 + 5)) / (54 * 4 ^ s) * (54 * 4 ^ s)) *
              (1080 * 4 ^ (J + 4) * (N0 + 5)) ^ 2 := by rw [h4]; ring
          _ ≤ (1080 * 4 ^ (J + 4) * (N0 + 5)) * (1080 * 4 ^ (J + 4) * (N0 + 5)) ^ 2 :=
              Nat.mul_le_mul_right _ hdiv
          _ = (1080 * 4 ^ (J + 4) * (N0 + 5)) ^ 3 := by ring
      · have h8 : ((2 : ℝ) ^ s) ^ 3 ≤ 8 ^ (J + 5) := by
          rw [← pow_mul, mul_comm, pow_mul]
          norm_num
          exact pow_le_pow_right₀ (by norm_num) (by omega)
        have hmpos : (0 : ℝ) ≤ ((1080 * 4 ^ (J + 4) * (N0 + 5) : ℕ) : ℝ) ^ 3 := by positivity
        push_cast
        have h8pos : (0 : ℝ) < 8 ^ (J + 5) := by positivity
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        push_cast at hmpos
        nlinarith [mul_le_mul_of_nonneg_right h8 hmpos])
  have hsum : ∑ s ∈ Finset.Ico 4 (J + 4), (2 ^ s * (1080 * 4 ^ (J + 4) * (N0 + 5))) *
      ((2 ^ s * (1080 * 4 ^ (J + 4) * (N0 + 5))) / 10 - (2 ^ s * (1080 * 4 ^ (J + 4) * (N0 + 5))) / 20) *
      ((1080 * 4 ^ (J + 4) * (N0 + 5)) / (54 * 4 ^ s)) =
      J * (1080 ^ 2 * (4 ^ (J + 4) * (N0 + 5)) ^ 3) := by
    rw [Finset.sum_congr rfl (fun s hs => term_eq J (N0 + 5) s (Finset.mem_Ico.mp hs).2)]
    simp
  rw [hsum] at key
  have hub := (hb (1080 * 4 ^ (J + 4) * (N0 + 5)) (by omega)).2
  have keyR : (J : ℝ) * (1080 ^ 2 * ((4 ^ (J + 4) * (N0 + 5) : ℕ) : ℝ) ^ 3) ≤
      (f (1080 * 4 ^ (J + 4) * (N0 + 5)) : ℝ) := by exact_mod_cast key
  set w : ℝ := ((4 ^ (J + 4) * (N0 + 5) : ℕ) : ℝ) with hw
  have hw1 : (1 : ℝ) ≤ w := by rw [hw]; exact_mod_cast hMpos
  have hmw : ((1080 * 4 ^ (J + 4) * (N0 + 5) : ℕ) : ℝ) = 1080 * w := by
    rw [hw]; push_cast; ring
  rw [hmw] at hub
  have h1 : (1080 * w + 1) ^ 3 ≤ (1081 * w) ^ 3 := by
    apply pow_le_pow_left₀ (by positivity); linarith
  have h2 : (1 + 1 / (108 * 8 ^ (J + 5))) * L * (1080 * w + 1) ^ 3 ≤ (1 + 1 / 100) * L * (1081 * w) ^ 3 := by
    gcongr
  have hw3 : (0 : ℝ) < w ^ 3 := by positivity
  have : (J : ℝ) * 1080 ^ 2 * w ^ 3 ≤ (1 + 1 / 100) * L * 1081 ^ 3 * w ^ 3 := by
    calc (J : ℝ) * 1080 ^ 2 * w ^ 3 = (J : ℝ) * (1080 ^ 2 * w ^ 3) := by ring
      _ ≤ _ := keyR
      _ ≤ _ := hub
      _ ≤ _ := h2
      _ = (1 + 1 / 100) * L * 1081 ^ 3 * w ^ 3 := by ring
  have h3 : (J : ℝ) * 1080 ^ 2 ≤ (1 + 1 / 100) * L * 1081 ^ 3 := le_of_mul_le_mul_right this hw3
  nlinarith

end OMA.E41

theorem OMA.solution : OMA.R_Erdos41_erdos_41_R2.H1 := by
  intro f hf hB _ _ hL
  exact OMA.E41.regular_case f hf hB hL
