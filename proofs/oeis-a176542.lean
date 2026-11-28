import OMAStatements.S_oeis_a176542

namespace OMA.A176542Proof

open OMA.S_oeis_a176542 PowerSeries

lemma two_mul_choose_two (m : ℕ) : 2 * (m + 1).choose 2 = m * (m + 1) := by
  rw [Nat.choose_two_right, Nat.add_sub_cancel]
  have h : Even ((m + 1) * m) := by
    rw [mul_comm]
    exact Nat.even_mul_succ_self m
  obtain ⟨k, hk⟩ := h
  rw [mul_comm (m + 1) m] at hk ⊢
  rw [hk]
  omega

lemma block_closed_form (n j : ℕ) :
    6 * block n j =
      (n : ℤ) * (3 * (j : ℤ) ^ 2 + 3 * (n : ℤ) * (j : ℤ) + (n : ℤ) ^ 2 - 1) := by
  induction n with
  | zero => simp [block]
  | succ n ih =>
    have hstep : block (n + 1) j = block n j + (((j + n + 1).choose 2 : ℕ) : ℤ) := by
      simp [block, Finset.sum_range_succ]
    have hch : 2 * (((j + n + 1).choose 2 : ℕ) : ℤ) =
        ((j + n : ℕ) : ℤ) * ((j + n + 1 : ℕ) : ℤ) := by
      exact_mod_cast two_mul_choose_two (j + n)
    rw [hstep]
    push_cast at hch ⊢
    linear_combination ih + 3 * hch

lemma mem_starts_iff (n j : ℕ) :
    j ∈ starts n ↔
      ∃ x : ℕ, 24 * (x : ℤ) ^ 2 - 3 * (n : ℤ) * (2 * (j : ℤ) + (n : ℤ)) ^ 2 =
        (n : ℤ) * ((n : ℤ) ^ 2 - 4) := by
  have hb : 24 * block n j =
      (n : ℤ) * (3 * (2 * (j : ℤ) + (n : ℤ)) ^ 2 + (n : ℤ) ^ 2 - 4) := by
    linear_combination 4 * block_closed_form n j
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by linarith⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, by linarith⟩

lemma starts_infinite_of_not_isSquare {n : ℕ} (hn : 0 < n) (hnsq : ¬ IsSquare (2 * (n : ℤ)))
    (hne : (starts n).Nonempty) : (starts n).Infinite := by
  obtain ⟨p, q, hpq, hq0⟩ := Pell.exists_of_not_isSquare (by positivity : (0 : ℤ) < 2 * (n : ℤ)) hnsq
  set p₁ : ℤ := |p|
  set q₁ : ℤ := |q|
  have hpq₁ : p₁ ^ 2 - 2 * (n : ℤ) * q₁ ^ 2 = 1 := by
    simpa [p₁, q₁, sq_abs] using hpq
  have hq₁_pos : 0 < q₁ := abs_pos.mpr hq0
  have hp₁_nonneg : 0 ≤ p₁ := abs_nonneg p
  have hp₁_pos : 1 ≤ p₁ := by nlinarith
  set A : ℤ := p₁ ^ 2 + 2 * (n : ℤ) * q₁ ^ 2
  set C : ℤ := p₁ * q₁
  have hA_eq : A = 1 + 4 * (n : ℤ) * q₁ ^ 2 := by
    dsimp [A]; linarith
  have hAC : A ^ 2 - 8 * (n : ℤ) * C ^ 2 = 1 := by
    dsimp [A, C]
    linear_combination (p₁ ^ 2 - 2 * (n : ℤ) * q₁ ^ 2 + 1) * hpq₁
  have hA_pos : 0 < A := by nlinarith
  have hC_pos : 0 < C := by nlinarith
  intro hfin
  have hne_fin : hfin.toFinset.Nonempty := by
    obtain ⟨j₀, hj₀⟩ := hne
    exact ⟨j₀, hfin.mem_toFinset.mpr hj₀⟩
  set j := hfin.toFinset.max' hne_fin
  have hj : j ∈ starts n := hfin.mem_toFinset.mp (Finset.max'_mem _ hne_fin)
  obtain ⟨x, hx⟩ := (mem_starts_iff n j).mp hj
  set u : ℤ := 2 * (j : ℤ) + (n : ℤ)
  have hu_pos : 0 < u := by omega
  have hx'_nonneg : 0 ≤ A * (x : ℤ) + (n : ℤ) * C * u := by positivity
  have hj'_gt : (j : ℤ) < (j : ℤ) + 4 * C * (x : ℤ) + 2 * (n : ℤ) * q₁ ^ 2 * u := by
    have h1 : 0 ≤ 4 * C * (x : ℤ) := by positivity
    have h2 : 0 < 2 * (n : ℤ) * q₁ ^ 2 * u := by positivity
    linarith
  set x' : ℕ := (A * (x : ℤ) + (n : ℤ) * C * u).toNat
  set j' : ℕ := ((j : ℤ) + 4 * C * (x : ℤ) + 2 * (n : ℤ) * q₁ ^ 2 * u).toNat
  have hx'_eq : (x' : ℤ) = A * (x : ℤ) + (n : ℤ) * C * u := Int.toNat_of_nonneg hx'_nonneg
  have hj'_eq : (j' : ℤ) = (j : ℤ) + 4 * C * (x : ℤ) + 2 * (n : ℤ) * q₁ ^ 2 * u :=
    Int.toNat_of_nonneg (by omega)
  have hu'_eq : 2 * (j' : ℤ) + (n : ℤ) = 8 * C * (x : ℤ) + A * u := by
    rw [hj'_eq, hA_eq]
    dsimp [u]
    ring
  have hj'_mem : j' ∈ starts n := by
    rw [mem_starts_iff]
    refine ⟨x', ?_⟩
    rw [hx'_eq, hu'_eq]
    linear_combination (24 * (x : ℤ) ^ 2 - 3 * (n : ℤ) * u ^ 2) * hAC + hx
  have hle : j' ≤ j := Finset.le_max' _ j' (hfin.mem_toFinset.mpr hj'_mem)
  omega

lemma no_twelve_sq_eq_sq_mul :
    ∀ m x K : ℕ, ¬ 3 ∣ K → 0 < m → 12 * x ^ 2 = m ^ 2 * K → False := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro x K hK hm h
    have h3_dvd : 3 ∣ m ^ 2 * K := ⟨4 * x ^ 2, by omega⟩
    have h3m2 : 3 ∣ m ^ 2 := (Nat.prime_three.dvd_mul.mp h3_dvd).resolve_right hK
    have h3m : 3 ∣ m := Nat.prime_three.dvd_of_dvd_pow h3m2
    obtain ⟨m', rfl⟩ := h3m
    have hm' : 0 < m' := by omega
    have h1 : 4 * x ^ 2 = 3 * m' ^ 2 * K := by nlinarith
    have h3x2 : 3 ∣ 4 * x ^ 2 := ⟨m' ^ 2 * K, by linarith⟩
    have h3x2' : 3 ∣ x ^ 2 := (Nat.prime_three.dvd_mul.mp h3x2).resolve_left (by decide)
    have h3x : 3 ∣ x := Nat.prime_three.dvd_of_dvd_pow h3x2'
    obtain ⟨x', rfl⟩ := h3x
    have h2 : 12 * x' ^ 2 = m' ^ 2 * K := by nlinarith
    exact ih m' (by omega) x' K hK hm' h2

lemma starts_empty_of_dvd_three {m : ℕ} (hm : 1 ≤ m) (h3 : 3 ∣ m) : starts (2 * m ^ 2) = ∅ := by
  ext j
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hj
  obtain ⟨x, hx⟩ := (mem_starts_iff (2 * m ^ 2) j).mp hj
  have hm3 : 3 ≤ m := by
    obtain ⟨t, rfl⟩ := h3
    omega
  have h1 : 12 * (x : ℤ) ^ 2 =
      (m : ℤ) ^ 2 * (3 * (2 * (j : ℤ) + 2 * (m : ℤ) ^ 2) ^ 2 + 4 * (m : ℤ) ^ 4 - 4) := by
    push_cast at hx
    linarith
  have h4le : 4 ≤ 4 * m ^ 4 := by
    have : 1 ≤ m ^ 4 := Nat.one_le_pow 4 m (by omega)
    omega
  set K : ℕ := 3 * (2 * j + 2 * m ^ 2) ^ 2 + 4 * m ^ 4 - 4
  have hK_cast : (K : ℤ) = 3 * (2 * (j : ℤ) + 2 * (m : ℤ) ^ 2) ^ 2 + 4 * (m : ℤ) ^ 4 - 4 := by
    dsimp [K]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hnat : 12 * x ^ 2 = m ^ 2 * K := by
    have : ((12 * x ^ 2 : ℕ) : ℤ) = ((m ^ 2 * K : ℕ) : ℤ) := by
      push_cast
      rw [hK_cast]
      exact h1
    exact_mod_cast this
  have h3_not_dvd_K : ¬ 3 ∣ K := by
    obtain ⟨t, rfl⟩ := h3
    have hpow : 3 ∣ 4 * (3 * t) ^ 4 := by
      refine ⟨108 * t ^ 4, ?_⟩
      ring
    obtain ⟨s, hs⟩ := hpow
    dsimp [K]
    omega
  exact no_twelve_sq_eq_sq_mul m x K h3_not_dvd_K (by omega) hnat

lemma not_mem_lengths_two : 2 ∉ lengths := by
  rintro ⟨_, _, hfin⟩
  have huniv : starts 2 = Set.univ := by
    ext j
    simp only [Set.mem_univ, iff_true, mem_starts_iff]
    refine ⟨j + 1, ?_⟩
    push_cast
    ring
  rw [huniv] at hfin
  exact Set.infinite_univ hfin

lemma not_mem_lengths_eight : 8 ∉ lengths := by
  rintro ⟨_, ⟨j, hj⟩, _⟩
  obtain ⟨x, hx⟩ := (mem_starts_iff 8 j).mp hj
  set u : ℤ := 2 * (j : ℤ) + 8
  have hu : 8 ≤ u := by dsimp [u]; omega
  have hsq : (x : ℤ) ^ 2 - u ^ 2 = 20 := by
    dsimp [u] at hx ⊢
    linarith
  have hlt1 : u < (x : ℤ) := by nlinarith
  have hlt2 : (x : ℤ) < u + 2 := by nlinarith
  have heq : (x : ℤ) = u + 1 := by omega
  rw [heq] at hsq
  have hlin : 2 * u + 1 = 20 := by linarith
  omega

lemma starts_finite_of_two_mul_sq {m : ℕ} (hm : 2 ≤ m) : (starts (2 * m ^ 2)).Finite := by
  set M : ℕ := 4 * m ^ 2 * (m ^ 4 - 1)
  have hm4_ge : 2 ≤ m ^ 4 := by
    calc
      2 ≤ 2 ^ 4 := by norm_num
      _ ≤ m ^ 4 := Nat.pow_le_pow_left hm 4
  have hM_pos : 0 < M := by
    have h1 : 0 < m ^ 2 := by positivity
    have h2 : 0 < m ^ 4 - 1 := by omega
    dsimp [M]
    positivity
  refine (Set.finite_Iic M).subset ?_
  intro j hj
  obtain ⟨x, hx⟩ := (mem_starts_iff (2 * m ^ 2) j).mp hj
  set u : ℤ := 2 * (j : ℤ) + 2 * (m : ℤ) ^ 2
  have hu_pos : 0 < u := by dsimp [u]; nlinarith
  have hfac : 3 * (2 * (x : ℤ) - (m : ℤ) * u) * (2 * (x : ℤ) + (m : ℤ) * u) =
      4 * (m : ℤ) ^ 2 * ((m : ℤ) ^ 4 - 1) := by
    dsimp [u]
    push_cast at hx
    linarith
  have hM_cast : (M : ℤ) = 4 * (m : ℤ) ^ 2 * ((m : ℤ) ^ 4 - 1) := by
    dsimp [M]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hsum_pos : 0 < 2 * (x : ℤ) + (m : ℤ) * u := by nlinarith
  have hdiff_pos : 1 ≤ 2 * (x : ℤ) - (m : ℤ) * u := by
    by_contra h
    push Not at h
    have : 3 * (2 * (x : ℤ) - (m : ℤ) * u) * (2 * (x : ℤ) + (m : ℤ) * u) ≤ 0 := by nlinarith
    linarith
  have hsum_le : 2 * (x : ℤ) + (m : ℤ) * u ≤ (M : ℤ) := by nlinarith
  have hj_le : (j : ℤ) ≤ (M : ℤ) := by
    dsimp [u] at hsum_le
    nlinarith
  exact_mod_cast hj_le

lemma starts_nonempty_of_ge_four {m : ℕ} (hm : 4 ≤ m) (h3 : ¬ 3 ∣ m) :
    (starts (2 * m ^ 2)).Nonempty := by
  have hmod : m % 6 = 1 ∨ m % 6 = 2 ∨ m % 6 = 4 ∨ m % 6 = 5 := by omega
  rcases hmod with h1 | h2 | h4 | h5
  · obtain ⟨r, hr⟩ : ∃ r : ℕ, m = 6 * r + 7 := ⟨(m - 7) / 6, by omega⟩
    subst hr
    refine ⟨108 * r ^ 4 + 504 * r ^ 3 + 846 * r ^ 2 + 602 * r + 150, ?_⟩
    rw [mem_starts_iff]
    refine ⟨(6 * r + 7) * (108 * r ^ 4 + 504 * r ^ 3 + 882 * r ^ 2 + 686 * r + 201), ?_⟩
    push_cast
    ring
  · obtain ⟨r, hr⟩ : ∃ r : ℕ, m = 6 * r + 8 := ⟨(m - 8) / 6, by omega⟩
    subst hr
    refine ⟨216 * r ^ 4 + 1152 * r ^ 3 + 2268 * r ^ 2 + 1952 * r + 618, ?_⟩
    rw [mem_starts_iff]
    refine ⟨(3 * r + 4) * (432 * r ^ 4 + 2304 * r ^ 3 + 4608 * r ^ 2 + 4096 * r + 1366), ?_⟩
    push_cast
    ring
  · obtain ⟨r, hr⟩ : ∃ r : ℕ, m = 6 * r + 4 := ⟨(m - 4) / 6, by omega⟩
    subst hr
    refine ⟨216 * r ^ 4 + 576 * r ^ 3 + 540 * r ^ 2 + 208 * r + 26, ?_⟩
    rw [mem_starts_iff]
    refine ⟨(3 * r + 2) * (432 * r ^ 4 + 1152 * r ^ 3 + 1152 * r ^ 2 + 512 * r + 86), ?_⟩
    push_cast
    ring
  · obtain ⟨r, hr⟩ : ∃ r : ℕ, m = 6 * r + 5 := ⟨(m - 5) / 6, by omega⟩
    subst hr
    refine ⟨108 * r ^ 4 + 360 * r ^ 3 + 414 * r ^ 2 + 190 * r + 26, ?_⟩
    rw [mem_starts_iff]
    refine ⟨(6 * r + 5) * (108 * r ^ 4 + 360 * r ^ 3 + 450 * r ^ 2 + 250 * r + 53), ?_⟩
    push_cast
    ring

lemma mem_lengths_iff (n : ℕ) : n ∈ lengths ↔ ∃ m : ℕ, 4 ≤ m ∧ ¬ 3 ∣ m ∧ n = 2 * m ^ 2 := by
  constructor
  · rintro ⟨hn, hne, hfin⟩
    have hsq : IsSquare (2 * (n : ℤ)) := by
      by_contra hnsq
      exact starts_infinite_of_not_isSquare hn hnsq hne hfin
    obtain ⟨k, hk⟩ := hsq
    set k' : ℕ := k.natAbs
    have hk' : 2 * n = k' ^ 2 := by
      have : (2 * (n : ℤ)) = (k' : ℤ) ^ 2 := by
        have hk2 : k * k = (k' : ℤ) ^ 2 := by
          rw [← sq, Int.natAbs_sq]
        linarith
      exact_mod_cast this
    have h2k : 2 ∣ k' := by
      have : 2 ∣ k' ^ 2 := ⟨n, hk'.symm⟩
      exact Nat.prime_two.dvd_of_dvd_pow this
    obtain ⟨m, hm_eq⟩ := h2k
    rw [hm_eq] at hk'
    have hn_eq : n = 2 * m ^ 2 := by nlinarith
    subst hn_eq
    have hm_pos : 1 ≤ m := by nlinarith
    have hm_ne_1 : m ≠ 1 := by
      rintro rfl
      exact not_mem_lengths_two ⟨hn, hne, hfin⟩
    have hm_ne_2 : m ≠ 2 := by
      rintro rfl
      exact not_mem_lengths_eight ⟨hn, hne, hfin⟩
    have h3 : ¬ 3 ∣ m := by
      intro h3
      have hemp := starts_empty_of_dvd_three hm_pos h3
      rw [hemp] at hne
      exact Set.not_nonempty_empty hne
    have hm4 : 4 ≤ m := by omega
    exact ⟨m, hm4, h3, rfl⟩
  · rintro ⟨m, hm, h3, rfl⟩
    refine ⟨by nlinarith, starts_nonempty_of_ge_four hm h3, starts_finite_of_two_mul_sq (by omega)⟩

def seqA (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if Even n then (9 * n ^ 2 + 24 * n + 16) / 2
  else (9 * n ^ 2 + 30 * n + 25) / 2

lemma seqA_even {r : ℕ} (hr : 1 ≤ r) : seqA (2 * r) = 2 * (3 * r + 2) ^ 2 := by
  have hne : 2 * r ≠ 0 := by omega
  have hev : Even (2 * r) := ⟨r, by omega⟩
  simp only [seqA, hne, ↓reduceIte, hev]
  have h : 9 * (2 * r) ^ 2 + 24 * (2 * r) + 16 = 2 * (2 * (3 * r + 2) ^ 2) := by ring
  omega

lemma seqA_odd (r : ℕ) : seqA (2 * r + 1) = 2 * (3 * r + 4) ^ 2 := by
  have hne : 2 * r + 1 ≠ 0 := by omega
  have hnev : ¬ Even (2 * r + 1) := by
    rintro ⟨k, hk⟩
    omega
  simp only [seqA, hne, ↓reduceIte, hnev]
  have h : 9 * (2 * r + 1) ^ 2 + 30 * (2 * r + 1) + 25 = 2 * (2 * (3 * r + 4) ^ 2) := by ring
  omega

lemma seqA_strictMono : StrictMono seqA := by
  refine strictMono_nat_of_lt_succ ?_
  intro n
  rcases Nat.even_or_odd n with ⟨r, hr⟩ | ⟨r, hr⟩
  · rcases r with _ | r
    · subst hr
      simp [seqA]
    · have h1 : n = 2 * (r + 1) := by omega
      rw [h1, seqA_even (by omega), seqA_odd (r + 1)]
      nlinarith
  · subst hr
    have h1 : 2 * r + 1 + 1 = 2 * (r + 1) := by omega
    rw [h1, seqA_odd r, seqA_even (by omega)]
    nlinarith

lemma lengths_eq_image : lengths = seqA '' Set.Ioi 0 := by
  ext n
  rw [mem_lengths_iff]
  constructor
  · rintro ⟨m, hm, h3, rfl⟩
    have hmod : m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases hmod with h1 | h2
    · obtain ⟨r, hr⟩ : ∃ r : ℕ, m = 3 * r + 4 := ⟨(m - 4) / 3, by omega⟩
      subst hr
      exact ⟨2 * r + 1, by simp, seqA_odd r⟩
    · obtain ⟨r, hr⟩ : ∃ r : ℕ, 1 ≤ r ∧ m = 3 * r + 2 := ⟨(m - 2) / 3, by omega, by omega⟩
      rcases hr with ⟨hr1, rfl⟩
      exact ⟨2 * r, by simp; omega, seqA_even hr1⟩
  · rintro ⟨k, hk, rfl⟩
    have hk0 : 0 < k := hk
    rcases Nat.even_or_odd k with ⟨r, hr⟩ | ⟨r, hr⟩
    · have hr1 : 1 ≤ r := by omega
      have hkr : k = 2 * r := by omega
      rw [hkr, seqA_even hr1]
      exact ⟨3 * r + 2, by omega, by omega, rfl⟩
    · subst hr
      rw [seqA_odd r]
      exact ⟨3 * r + 4, by omega, by omega, rfl⟩

lemma seqA_rec (n : ℕ) (hn : 5 < n) :
    (seqA n : ℤ) = (seqA (n - 1) : ℤ) + 2 * (seqA (n - 2) : ℤ) -
      2 * (seqA (n - 3) : ℤ) - (seqA (n - 4) : ℤ) + (seqA (n - 5) : ℤ) := by
  rcases Nat.even_or_odd n with ⟨r, hr⟩ | ⟨r, hr⟩
  · have hr3 : 3 ≤ r := by omega
    have h0 : n = 2 * r := by omega
    have h1 : n - 1 = 2 * (r - 1) + 1 := by omega
    have h2 : n - 2 = 2 * (r - 1) := by omega
    have h3 : n - 3 = 2 * (r - 2) + 1 := by omega
    have h4 : n - 4 = 2 * (r - 2) := by omega
    have h5 : n - 5 = 2 * (r - 3) + 1 := by omega
    rw [h1, h2, h3, h4, h5, h0, seqA_even (by omega), seqA_odd, seqA_even (by omega),
        seqA_odd, seqA_even (by omega), seqA_odd]
    have hr1 : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by omega
    have hr2 : ((r - 2 : ℕ) : ℤ) = (r : ℤ) - 2 := by omega
    have hr3' : ((r - 3 : ℕ) : ℤ) = (r : ℤ) - 3 := by omega
    push_cast
    rw [hr1, hr2, hr3']
    ring
  · have hr3 : 3 ≤ r := by omega
    have h0 : n = 2 * r + 1 := by omega
    have h1 : n - 1 = 2 * r := by omega
    have h2 : n - 2 = 2 * (r - 1) + 1 := by omega
    have h3 : n - 3 = 2 * (r - 1) := by omega
    have h4 : n - 4 = 2 * (r - 2) + 1 := by omega
    have h5 : n - 5 = 2 * (r - 2) := by omega
    rw [h1, h2, h3, h4, h5, h0, seqA_odd, seqA_even (by omega), seqA_odd,
        seqA_even (by omega), seqA_odd, seqA_even (by omega)]
    have hr1 : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by omega
    have hr2 : ((r - 2 : ℕ) : ℤ) = (r : ℤ) - 2 := by omega
    push_cast
    rw [hr1, hr2]
    ring

lemma seqA_gf :
    (PowerSeries.mk (fun n => (seqA n : ℤ))) * (1 - X) ^ 3 * (1 + X) ^ 2 =
      2 * X * (4 * X ^ 4 - 3 * X ^ 3 - 8 * X ^ 2 + 9 * X + 16) := by
  set A : PowerSeries ℤ := PowerSeries.mk (fun n => (seqA n : ℤ))
  have hpoly : (1 - (X : PowerSeries ℤ)) ^ 3 * (1 + X) ^ 2 =
      1 - X ^ 1 - 2 * X ^ 2 + 2 * X ^ 3 + X ^ 4 - X ^ 5 := by ring
  have hrhs : (2 : PowerSeries ℤ) * X * (4 * X ^ 4 - 3 * X ^ 3 - 8 * X ^ 2 + 9 * X + 16) =
      32 * X ^ 1 + 18 * X ^ 2 - 16 * X ^ 3 - 6 * X ^ 4 + 8 * X ^ 5 := by ring
  rw [mul_assoc, hpoly, hrhs]
  have hmul : A * (1 - X ^ 1 - 2 * X ^ 2 + 2 * X ^ 3 + X ^ 4 - X ^ 5) =
      A - A * X ^ 1 - 2 * (A * X ^ 2) + 2 * (A * X ^ 3) + A * X ^ 4 - A * X ^ 5 := by ring
  rw [hmul]
  ext k
  have hcoeffA : ∀ m, PowerSeries.coeff m A = (seqA m : ℤ) := fun m => PowerSeries.coeff_mk m _
  have hsmul : ∀ (c : ℤ) (P : PowerSeries ℤ), PowerSeries.coeff k ((c : PowerSeries ℤ) * P) =
      c * PowerSeries.coeff k P := by
    intro c P
    have hc : (c : PowerSeries ℤ) = PowerSeries.C (R := ℤ) c :=
      (map_intCast (PowerSeries.C (R := ℤ)) c).symm
    rw [hc, PowerSeries.coeff_C_mul]
  have hX : ∀ (d : ℕ), PowerSeries.coeff k ((X : PowerSeries ℤ) ^ d) = if k = d then 1 else 0 := by
    intro d
    exact PowerSeries.coeff_X_pow k d
  simp only [map_sub, map_add]
  have h2 : PowerSeries.coeff k ((2 : PowerSeries ℤ) * (A * X ^ 2)) =
      2 * PowerSeries.coeff k (A * X ^ 2) := by
    simpa only [Int.cast_ofNat] using hsmul 2 (A * X ^ 2)
  have h3 : PowerSeries.coeff k ((2 : PowerSeries ℤ) * (A * X ^ 3)) =
      2 * PowerSeries.coeff k (A * X ^ 3) := by
    simpa only [Int.cast_ofNat] using hsmul 2 (A * X ^ 3)
  have h32 : PowerSeries.coeff k ((32 : PowerSeries ℤ) * X ^ 1) =
      32 * PowerSeries.coeff k (X ^ 1) := by
    simpa only [Int.cast_ofNat] using hsmul 32 (X ^ 1)
  have h18 : PowerSeries.coeff k ((18 : PowerSeries ℤ) * X ^ 2) =
      18 * PowerSeries.coeff k (X ^ 2) := by
    simpa only [Int.cast_ofNat] using hsmul 18 (X ^ 2)
  have h16 : PowerSeries.coeff k ((16 : PowerSeries ℤ) * X ^ 3) =
      16 * PowerSeries.coeff k (X ^ 3) := by
    simpa only [Int.cast_ofNat] using hsmul 16 (X ^ 3)
  have h6 : PowerSeries.coeff k ((6 : PowerSeries ℤ) * X ^ 4) =
      6 * PowerSeries.coeff k (X ^ 4) := by
    simpa only [Int.cast_ofNat] using hsmul 6 (X ^ 4)
  have h8 : PowerSeries.coeff k ((8 : PowerSeries ℤ) * X ^ 5) =
      8 * PowerSeries.coeff k (X ^ 5) := by
    simpa only [Int.cast_ofNat] using hsmul 8 (X ^ 5)
  rw [h2, h3, h32, h18, h16, h6, h8]
  simp only [PowerSeries.coeff_mul_X_pow', hcoeffA, hX]
  match k with
  | 0 => simp [seqA]
  | 1 => simp [seqA]
  | 2 => simp [seqA]
  | 3 => simp [seqA]; decide
  | 4 => simp [seqA]; decide
  | 5 => simp [seqA]; decide
  | k + 6 =>
    have hrec := seqA_rec (k + 6) (by omega)
    have hle1 : 1 ≤ k + 6 := by omega
    have hle2 : 2 ≤ k + 6 := by omega
    have hle3 : 3 ≤ k + 6 := by omega
    have hle4 : 4 ≤ k + 6 := by omega
    have hle5 : 5 ≤ k + 6 := by omega
    have hne1 : k + 6 ≠ 1 := by omega
    have hne2 : k + 6 ≠ 2 := by omega
    have hne3 : k + 6 ≠ 3 := by omega
    have hne4 : k + 6 ≠ 4 := by omega
    have hne5 : k + 6 ≠ 5 := by omega
    simp only [hle1, hle2, hle3, hle4, hle5, hne1, hne2, hne3, hne4, hne5, ↓reduceIte,
      mul_zero, add_zero, sub_zero]
    linarith

end OMA.A176542Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a176542.main := by
  refine ⟨OMA.A176542Proof.seqA, rfl, OMA.A176542Proof.seqA_strictMono,
    OMA.A176542Proof.lengths_eq_image, ?_, OMA.A176542Proof.seqA_rec,
    OMA.A176542Proof.seqA_gf⟩
  intro n hn
  have hne : n ≠ 0 := by omega
  simp [OMA.A176542Proof.seqA, hne]
