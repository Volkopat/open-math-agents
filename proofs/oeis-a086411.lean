import OMAStatements.S_oeis_a086411

-- Problem: A086411, greatest prime factor of 3-smooth numbers equals A049237(n+1) (Mathar's conjecture).
-- Credit: @bnb9001

namespace OMA_A086411_Proof

open OMA.S_oeis_a086411

theorem tot_two_pow (i : ℕ) : Nat.totient (2 ^ (i + 1)) = 2 ^ i := by
  rw [Nat.totient_prime_pow Nat.prime_two (by omega)]; simp

theorem tot_three_pow (j : ℕ) : Nat.totient (3 ^ (j + 1)) = 2 * 3 ^ j := by
  rw [Nat.totient_prime_pow Nat.prime_three (by omega)]; simp [mul_comm]

theorem cop23 (i j : ℕ) : Nat.Coprime (2 ^ i) (3 ^ j) :=
  Nat.Coprime.pow _ _ (by norm_num)

theorem odd_part {r : ℕ} (hr : Odd r) (hd : Nat.totient r ∣ 2 * r) : ∃ j, r = 3 ^ j := by
  rcases eq_or_ne r 1 with h1 | h1
  · exact ⟨0, by simp [h1]⟩
  have hr0 : r ≠ 0 := by rintro rfl; simp at hr
  set p := r.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime h1
  have hpr : p ∣ r := Nat.minFac_dvd r
  have hnot2 : ¬ 2 ∣ r := by rcases hr with ⟨k, rfl⟩; omega
  have hpodd : p ≠ 2 := by rintro h; rw [h] at hpr; exact hnot2 hpr
  -- every prime divisor is p
  have huniq : ∀ {q : ℕ}, q.Prime → q ∣ r → q = p := by
    intro q hq hqr
    by_contra hne
    have hcop : Nat.Coprime q p := (Nat.coprime_primes hq hp).mpr hne
    have hqp : q * p ∣ r := hcop.mul_dvd_of_dvd_of_dvd hqr hpr
    have htot : Nat.totient (q * p) = (q - 1) * (p - 1) := by
      rw [Nat.totient_mul hcop, Nat.totient_prime hq, Nat.totient_prime hp]
    have hqodd : q ≠ 2 := by rintro h; rw [h] at hqr; exact hnot2 hqr
    have h4 : 4 ∣ Nat.totient r := by
      have := Nat.totient_dvd_of_dvd hqp
      rw [htot] at this
      refine dvd_trans ?_ this
      have hq2 : 2 ∣ q - 1 := by
        rcases hq.eq_two_or_odd' with he | ⟨t, ht⟩
        · exact absurd he hqodd
        · omega
      have hp2 : 2 ∣ p - 1 := by
        rcases hp.eq_two_or_odd' with he | ⟨t, ht⟩
        · exact absurd he hpodd
        · omega
      exact (by
        obtain ⟨u, hu⟩ := hq2; obtain ⟨v, hv⟩ := hp2
        exact ⟨u * v, by rw [hu, hv]; ring⟩)
    have : 4 ∣ 2 * r := dvd_trans h4 hd
    omega
  have hrp : r = p ^ r.primeFactorsList.length := Nat.eq_prime_pow_of_unique_prime_dvd hr0 huniq
  set k := r.primeFactorsList.length
  have hk : k ≠ 0 := by
    rintro hk0; rw [hk0, pow_zero] at hrp; exact h1 hrp
  -- (p - 1) ∣ 2
  have hdv : p - 1 ∣ 2 * p ^ k := by
    have h := Nat.totient_prime_pow hp (Nat.pos_of_ne_zero hk)
    have : p - 1 ∣ Nat.totient r := by
      rw [hrp, h]; exact Dvd.intro_left _ rfl
    have h2r := dvd_trans this hd
    rwa [hrp] at h2r
  have hcop : Nat.Coprime (p - 1) (p ^ k) := by
    apply Nat.Coprime.pow_right
    have hp1 : 1 ≤ p := hp.one_lt.le
    have : p = (p - 1) + 1 := by omega
    conv => rhs; rw [this]
    simp
  have h2 : p - 1 ∣ 2 := hcop.dvd_of_dvd_mul_right hdv
  have hp3 : p ≤ 3 := by
    have := Nat.le_of_dvd (by norm_num) h2; omega
  have hp2 : 2 ≤ p := hp.two_le
  have hp3' : p = 3 := by omega
  exact ⟨k, by rw [hrp, hp3']⟩

theorem char_fwd {m : ℕ} (hm : 0 < m) (hd : Nat.totient m ∣ m) (h1 : m ≠ 1) :
    ∃ i j, m = 2 ^ (i + 1) * 3 ^ j := by
  obtain ⟨a, r, hr, hmr⟩ := Nat.exists_eq_two_pow_mul_odd (n := m) (by omega)
  have hcop : Nat.Coprime (2 ^ a) r :=
    Nat.Coprime.pow_left _ ((Nat.coprime_two_left).mpr hr)
  rcases a with _ | a
  · rw [pow_zero, one_mul] at hmr
    rw [hmr] at hd h1
    have h3 : 2 < r := by rcases hr with ⟨k, rfl⟩; omega
    have := Nat.totient_even h3
    have h2 : 2 ∣ r := dvd_trans (even_iff_two_dvd.mp this) hd
    exact absurd h2 (by rcases hr with ⟨k, rfl⟩; omega)
  · rw [hmr, Nat.totient_mul hcop, tot_two_pow] at hd
    have hd' : Nat.totient r ∣ 2 * r := by
      have : 2 ^ (a + 1) * r = 2 ^ a * (2 * r) := by ring
      rw [this] at hd
      exact Nat.dvd_of_mul_dvd_mul_left (by positivity) hd
    obtain ⟨j, hj⟩ := odd_part hr hd'
    exact ⟨a, j, by rw [hmr, hj]⟩

theorem char_bwd (i j : ℕ) : PhiDvd (2 ^ (i + 1) * 3 ^ j) := by
  refine ⟨by positivity, ?_⟩
  rw [Nat.totient_mul (cop23 _ _), tot_two_pow]
  rcases j with _ | j
  · simp [pow_succ]
  · rw [tot_three_pow]
    exact ⟨3, by ring⟩

theorem phiDvd_iff (m : ℕ) : PhiDvd m ↔ m = 1 ∨ ∃ i j, m = 2 ^ (i + 1) * 3 ^ j := by
  constructor
  · rintro ⟨hm, hd⟩
    rcases eq_or_ne m 1 with h | h
    · exact Or.inl h
    · exact Or.inr (char_fwd hm hd h)
  · rintro (rfl | ⟨i, j, rfl⟩)
    · exact ⟨by norm_num, by simp⟩
    · exact char_bwd i j

theorem smooth_inf : (Set.ofPred Is3Smooth).Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun i : ℕ => 2 ^ i)
  · intro x y h; exact Nat.pow_right_injective (le_refl 2) h
  · intro i; show Is3Smooth (2 ^ i); exact ⟨i, 0, by simp⟩

theorem smooth_pos {m : ℕ} (h : Is3Smooth m) : 0 < m := by
  obtain ⟨i, j, rfl⟩ := h; positivity

theorem nth_smooth_zero : Nat.nth Is3Smooth 0 = 1 := by
  rw [Nat.nth_zero]
  apply le_antisymm
  · exact Nat.sInf_le (show Is3Smooth 1 from ⟨0, 0, by simp⟩)
  · apply le_csInf ⟨1, show Is3Smooth 1 from ⟨0, 0, by simp⟩⟩
    intro m hm; exact smooth_pos hm

/-- the explicit enumeration of A007694 (0-indexed) -/
noncomputable def h (k : ℕ) : ℕ := if k = 0 then 1 else 2 * Nat.nth Is3Smooth (k - 1)

theorem h_strictMono : StrictMono h := by
  apply strictMono_nat_of_lt_succ
  intro k
  unfold h
  rcases k with _ | k
  · simp [nth_smooth_zero]
  · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    have := Nat.nth_strictMono smooth_inf (show k < k + 1 by omega)
    omega

theorem h_maps (k : ℕ) : PhiDvd (h k) := by
  unfold h
  split_ifs with hk
  · exact (phiDvd_iff 1).mpr (Or.inl rfl)
  · obtain ⟨i, j, hij⟩ := Nat.nth_mem_of_infinite smooth_inf (k - 1)
    rw [hij, show 2 * (2 ^ i * 3 ^ j) = 2 ^ (i + 1) * 3 ^ j by ring]
    exact char_bwd i j

theorem h_surj {m : ℕ} (hm : PhiDvd m) : ∃ k, h k = m := by
  classical
  rcases (phiDvd_iff m).mp hm with rfl | ⟨i, j, rfl⟩
  · exact ⟨0, by simp [h]⟩
  · have hs : Is3Smooth (2 ^ i * 3 ^ j) := ⟨i, j, rfl⟩
    refine ⟨Nat.count Is3Smooth (2 ^ i * 3 ^ j) + 1, ?_⟩
    simp only [h, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, Nat.nth_count hs]
    ring

theorem nth_phiDvd (k : ℕ) : Nat.nth PhiDvd k = h k := by
  have hinf : (Set.ofPred PhiDvd).Infinite :=
    Set.infinite_of_injective_forall_mem h_strictMono.injective (fun k => h_maps k)
  have hk : ∀ hf : (Set.ofPred PhiDvd).Finite, k < hf.toFinset.card := fun hf => absurd hf hinf
  refine (Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn h ?_ ?_ ?_ hk).symm
  · intro m hm
    obtain ⟨j, hj⟩ := h_surj hm
    exact ⟨j, fun hf => absurd hf hinf, hj⟩
  · intro j _
    exact h_maps j
  · exact h_strictMono.strictMonoOn _

theorem ratio_eq_gpf (i j : ℕ) (hne : 2 ^ i * 3 ^ j ≠ 1) :
    2 * (2 ^ i * 3 ^ j) / Nat.totient (2 * (2 ^ i * 3 ^ j)) = gpf (2 ^ i * 3 ^ j) := by
  rw [show 2 * (2 ^ i * 3 ^ j) = 2 ^ (i + 1) * 3 ^ j by ring, Nat.totient_mul (cop23 _ _),
    tot_two_pow]
  rcases j with _ | j
  · -- 2^i with i ≥ 1
    have hi : i ≠ 0 := by rintro rfl; simp at hne
    simp only [pow_zero, mul_one, Nat.totient_one]
    rw [pow_succ, Nat.mul_div_cancel_left _ (by positivity)]
    unfold gpf
    rw [Nat.primeFactors_prime_pow hi Nat.prime_two]
    simp
  · rw [tot_three_pow]
    have : 2 ^ (i + 1) * 3 ^ (j + 1) = (2 ^ i * (2 * 3 ^ j)) * 3 := by ring
    rw [this, Nat.mul_div_cancel_left _ (by positivity)]
    unfold gpf
    have hpf : (2 ^ i * 3 ^ (j + 1)).primeFactors ⊆ {2, 3} := by
      rw [Nat.primeFactors_mul (by positivity) (by positivity)]
      intro q hq
      rcases Finset.mem_union.mp hq with hq | hq
      · rw [Nat.primeFactors_pow _ ] at hq
        · have := Nat.mem_primeFactors.mp hq
          simp only [Finset.mem_insert, Finset.mem_singleton]
          left
          exact (Nat.prime_dvd_prime_iff_eq this.1 Nat.prime_two).mp this.2.1
        · rintro rfl; simp at hq
      · rw [Nat.primeFactors_prime_pow (by omega) Nat.prime_three] at hq
        simp at hq; simp [hq]
    have h3 : 3 ∈ (2 ^ i * 3 ^ (j + 1)).primeFactors := by
      rw [Nat.mem_primeFactors]
      exact ⟨Nat.prime_three, Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) _, by positivity⟩
    have hsup : (2 ^ i * 3 ^ (j + 1)).primeFactors.sup id = 3 := by
      apply le_antisymm
      · apply Finset.sup_le
        intro q hq
        have := hpf hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with rfl | rfl <;> simp
      · exact Finset.le_sup (f := id) h3
    rw [hsup]; rfl

end OMA_A086411_Proof

open OMA.S_oeis_a086411 OMA_A086411_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a086411.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hb : phiDvdSeq (k + 2 + 1) = 2 * Nat.nth Is3Smooth (k + 1) := by
    unfold phiDvdSeq
    rw [show k + 2 + 1 - 1 = k + 2 by omega, nth_phiDvd]
    simp [h]
  have ha : smooth3 (k + 2) = Nat.nth Is3Smooth (k + 1) := by
    unfold smooth3; rw [show k + 2 - 1 = k + 1 by omega]
  unfold a b
  rw [hb, ha]
  obtain ⟨i, j, hij⟩ := Nat.nth_mem_of_infinite smooth_inf (k + 1)
  have hne : 2 ^ i * 3 ^ j ≠ 1 := by
    rw [← hij]
    have := Nat.nth_strictMono smooth_inf (show 0 < k + 1 by omega)
    rw [nth_smooth_zero] at this
    omega
  rw [hij, ratio_eq_gpf i j hne]
