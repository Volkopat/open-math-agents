import OMAStatements.S_oeis_a397245
import Mathlib

namespace OMA.P_oeis_a397245

open Classical

/-- Indicator of powers of 3 in `ZMod 3`. -/
private noncomputable def sInd (n : ℕ) : ZMod 3 :=
  if ∃ k : ℕ, n = 3 ^ k then 1 else 0

/-- Discrete convolution over `ZMod 3`. -/
private noncomputable def conv (f g : ℕ → ZMod 3) (n : ℕ) : ZMod 3 :=
  ∑ i ∈ Finset.range (n + 1), f i * g (n - i)

private lemma sInd_zero : sInd 0 = 0 := by
  dsimp [sInd]
  rw [if_neg]
  rintro ⟨k, hk⟩
  exact absurd hk.symm (pow_ne_zero k (by norm_num))

private lemma pow3_inj {j k : ℕ} (h : 3 ^ j = 3 ^ k) : j = k :=
  Nat.pow_right_injective (by norm_num : 2 ≤ 3) h

private lemma pow3_add_unique {j1 k1 j2 k2 : ℕ} (h1 : j1 ≤ k1) (h2 : j2 ≤ k2)
    (heq : 3 ^ j1 + 3 ^ k1 = 3 ^ j2 + 3 ^ k2) : j1 = j2 ∧ k1 = k2 := by
  induction j1 generalizing k1 j2 k2 with
  | zero =>
    have hne : (3 ^ 0 + 3 ^ k1) % 3 ≠ 0 := by
      rcases k1 with _ | k1'
      · norm_num
      · rw [pow_zero, pow_succ]; omega
    have hj2 : j2 = 0 := by
      by_contra hne0
      have h3 : 3 ∣ 3 ^ j2 + 3 ^ k2 :=
        dvd_add (dvd_pow_self 3 hne0) (dvd_pow_self 3 (by omega))
      rw [← heq] at h3
      omega
    subst hj2
    have hk : 3 ^ k1 = 3 ^ k2 := by omega
    exact ⟨rfl, pow3_inj hk⟩
  | succ j1 ih =>
    have h3 : 3 ∣ 3 ^ (j1 + 1) + 3 ^ k1 :=
      dvd_add (dvd_pow_self 3 (by omega)) (dvd_pow_self 3 (by omega))
    rw [heq] at h3
    have hj2_pos : j2 ≠ 0 := by
      rintro rfl
      rcases k2 with _ | k2'
      · norm_num at h3
      · rw [pow_zero, pow_succ] at h3; omega
    obtain ⟨j2', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj2_pos
    obtain ⟨k1', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k1 ≠ 0)
    obtain ⟨k2', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k2 ≠ 0)
    have hdiv : 3 ^ j1 + 3 ^ k1' = 3 ^ j2' + 3 ^ k2' := by
      have : (3 ^ j1 + 3 ^ k1') * 3 = (3 ^ j2' + 3 ^ k2') * 3 := by
        simpa [pow_succ, add_mul] using heq
      omega
    obtain ⟨hj, hk⟩ := ih (by omega) (by omega) hdiv
    exact ⟨by omega, by omega⟩

private lemma pow3_ne_two_pow3 (j k : ℕ) : 3 ^ j ≠ 2 * 3 ^ k := by
  intro h
  rcases le_total j k with hjk | hkj
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
    have hmul : 3 ^ j * 1 = 3 ^ j * (2 * 3 ^ d) := by
      calc 3 ^ j * 1 = 3 ^ j := mul_one _
        _ = 2 * 3 ^ (j + d) := h
        _ = 3 ^ j * (2 * 3 ^ d) := by rw [pow_add]; ring
    have h1 : 1 = 2 * 3 ^ d := Nat.eq_of_mul_eq_mul_left (by positivity) hmul
    have : 1 ≤ 3 ^ d := Nat.one_le_pow d 3 (by norm_num)
    omega
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkj
    have hmul : 3 ^ k * 3 ^ d = 3 ^ k * 2 := by
      calc 3 ^ k * 3 ^ d = 3 ^ (k + d) := (pow_add 3 k d).symm
        _ = 2 * 3 ^ k := h
        _ = 3 ^ k * 2 := by ring
    have h1 : 3 ^ d = 2 := Nat.eq_of_mul_eq_mul_left (by positivity) hmul
    rcases d with _ | d'
    · norm_num at h1
    · rw [pow_succ] at h1
      have : 1 ≤ 3 ^ d' := Nat.one_le_pow d' 3 (by norm_num)
      omega

private lemma pow3_ne_sum_distinct {m j k : ℕ} (hjk : j < k) : 3 ^ m ≠ 3 ^ j + 3 ^ k := by
  intro h
  have hlt : 3 ^ j + 3 ^ k < 3 ^ (k + 1) := by
    have : 3 ^ j < 3 ^ k := Nat.pow_lt_pow_right (by norm_num) hjk
    rw [pow_succ]; omega
  have hpos : 0 < 3 ^ j := by positivity
  have hgt : 3 ^ k < 3 ^ j + 3 ^ k := by omega
  have hm1 : k < m := by
    by_contra hle
    have : 3 ^ m ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hm2 : m < k + 1 := by
    by_contra hle
    have : 3 ^ (k + 1) ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  omega

private lemma two_pow3_ne_sum_distinct {m j k : ℕ} (hjk : j < k) : 2 * 3 ^ m ≠ 3 ^ j + 3 ^ k := by
  intro h
  have h2 : 3 ^ m + 3 ^ m = 3 ^ j + 3 ^ k := by omega
  obtain ⟨h1, h3⟩ := pow3_add_unique le_rfl (le_of_lt hjk) h2
  omega

private lemma conv_sInd_sInd (N : ℕ) :
    conv sInd sInd N =
      if ∃ k : ℕ, N = 2 * 3 ^ k then 1
      else if ∃ j k : ℕ, j < k ∧ N = 3 ^ j + 3 ^ k then 2 else 0 := by
  dsimp [conv]
  by_cases h2 : ∃ k : ℕ, N = 2 * 3 ^ k
  · rw [if_pos h2]
    obtain ⟨k, rfl⟩ := h2
    have hmem : 3 ^ k ∈ Finset.range (2 * 3 ^ k + 1) := by
      rw [Finset.mem_range]
      have : 0 < 3 ^ k := by positivity
      omega
    rw [Finset.sum_eq_single (3 ^ k)]
    · have hsub : 2 * 3 ^ k - 3 ^ k = 3 ^ k := by omega
      rw [hsub]
      simp [sInd]
    · intro i hi hne
      dsimp [sInd]
      split_ifs with h1 h3
      · exfalso
        obtain ⟨a, ha⟩ := h1
        obtain ⟨b, hb⟩ := h3
        have hlt : i ≤ 2 * 3 ^ k := by rw [Finset.mem_range] at hi; omega
        have hsum : 3 ^ a + 3 ^ b = 3 ^ k + 3 ^ k := by omega
        rcases le_total a b with hab | hba
        · obtain ⟨hka, _⟩ := pow3_add_unique hab le_rfl hsum
          exact hne (by rw [ha, hka])
        · obtain ⟨_, hka⟩ := pow3_add_unique (j2 := k) (k2 := k) hba le_rfl (by omega)
          exact hne (by rw [ha, hka])
      · simp
      · simp
      · simp
    · intro hnot; exact absurd hmem hnot
  · rw [if_neg h2]
    by_cases hsum : ∃ j k : ℕ, j < k ∧ N = 3 ^ j + 3 ^ k
    · rw [if_pos hsum]
      obtain ⟨j, k, hjk, rfl⟩ := hsum
      have hne_jk : 3 ^ j ≠ 3 ^ k := fun h => absurd (pow3_inj h) (by omega)
      have hmem_j : 3 ^ j ∈ Finset.range (3 ^ j + 3 ^ k + 1) := by
        rw [Finset.mem_range]
        have : 0 < 3 ^ k := by positivity
        omega
      have hmem_k : 3 ^ k ∈ Finset.range (3 ^ j + 3 ^ k + 1) := by
        rw [Finset.mem_range]
        have : 0 < 3 ^ j := by positivity
        omega
      have hpair : ∑ i ∈ Finset.range (3 ^ j + 3 ^ k + 1), sInd i * sInd (3 ^ j + 3 ^ k - i) =
          sInd (3 ^ j) * sInd (3 ^ j + 3 ^ k - 3 ^ j) +
          sInd (3 ^ k) * sInd (3 ^ j + 3 ^ k - 3 ^ k) := by
        rw [← Finset.sum_subset (s₁ := {3 ^ j, 3 ^ k}) (by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption)]
        · rw [Finset.sum_pair hne_jk]
        · intro i hi hnot
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
          dsimp [sInd]
          split_ifs with h1 h3
          · exfalso
            obtain ⟨a, ha⟩ := h1
            obtain ⟨b, hb⟩ := h3
            have hle : i ≤ 3 ^ j + 3 ^ k := by rw [Finset.mem_range] at hi; omega
            have heq : 3 ^ a + 3 ^ b = 3 ^ j + 3 ^ k := by omega
            rcases le_total a b with hab | hba
            · obtain ⟨haj, _⟩ := pow3_add_unique hab (le_of_lt hjk) heq
              exact hnot.1 (by rw [ha, haj])
            · obtain ⟨_, hak⟩ := pow3_add_unique hba (le_of_lt hjk) (by omega)
              exact hnot.2 (by rw [ha, hak])
          · simp
          · simp
          · simp
      rw [hpair, Nat.add_sub_cancel_left, Nat.add_sub_cancel]
      have h1 : sInd (3 ^ j) = 1 := if_pos ⟨j, rfl⟩
      have h2' : sInd (3 ^ k) = 1 := if_pos ⟨k, rfl⟩
      rw [h1, h2']; decide
    · rw [if_neg hsum]
      refine Finset.sum_eq_zero (fun i hi => ?_)
      dsimp [sInd]
      split_ifs with h1 h3
      · exfalso
        obtain ⟨a, ha⟩ := h1
        obtain ⟨b, hb⟩ := h3
        have hle : i ≤ N := by rw [Finset.mem_range] at hi; omega
        rcases lt_trichotomy a b with hab | rfl | hba
        · exact hsum ⟨a, b, hab, by omega⟩
        · exact h2 ⟨a, by omega⟩
        · exact hsum ⟨b, a, hba, by omega⟩
      · simp
      · simp
      · simp

private lemma conv_sInd_cube (N : ℕ) (hN : 2 ≤ N) :
    conv sInd (conv sInd sInd) N = sInd N := by
  -- Express as sum over triples `(a, b, c) ∈ (range (N+1))^3` with `a + b + c = N`!
  set R := Finset.range (N + 1)
  set T := (R ×ˢ (R ×ˢ R)).filter (fun t : ℕ × ℕ × ℕ => t.1 + t.2.1 + t.2.2 = N)
  have htriple : conv sInd (conv sInd sInd) N =
      ∑ t ∈ T, sInd t.1 * sInd t.2.1 * sInd t.2.2 := by
    dsimp [conv]
    have h1 : ∑ i ∈ R, sInd i * ∑ j ∈ Finset.range (N - i + 1), sInd j * sInd (N - i - j) =
        ∑ i ∈ R, ∑ j ∈ Finset.range (N - i + 1), sInd i * sInd j * sInd (N - i - j) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => by ring)
    rw [h1, Finset.sum_sigma']
    refine Finset.sum_bij (fun x _ => (x.1, (x.2, N - x.1 - x.2))) ?_ ?_ ?_ ?_
    · rintro ⟨i, j⟩ hx
      simp only [Finset.mem_sigma, R, Finset.mem_range] at hx
      simp only [T, Finset.mem_filter, Finset.mem_product, R, Finset.mem_range]
      exact ⟨⟨by omega, by omega, by omega⟩, by omega⟩
    · rintro ⟨i1, j1⟩ _ ⟨i2, j2⟩ _ h
      simp only [Prod.mk.injEq] at h
      exact Sigma.ext h.1 (heq_of_eq h.2.1)
    · rintro ⟨a, b, c⟩ ht
      simp only [T, Finset.mem_filter, Finset.mem_product, R, Finset.mem_range] at ht
      refine ⟨⟨a, b⟩, ?_, ?_⟩
      · simp only [Finset.mem_sigma, R, Finset.mem_range]; omega
      · refine Prod.ext rfl (Prod.ext rfl ?_); dsimp; omega
    · rintro ⟨i, j⟩ _; rfl
  rw [htriple]
  -- Split `T` into diagonal (`a = b ∧ b = c`) and off-diagonal (`¬ (a = b ∧ b = c)`).
  set Tdiag := T.filter (fun t => t.1 = t.2.1 ∧ t.2.1 = t.2.2)
  set Toff := T.filter (fun t => ¬ (t.1 = t.2.1 ∧ t.2.1 = t.2.2))
  have hsplit : ∑ t ∈ T, sInd t.1 * sInd t.2.1 * sInd t.2.2 =
      (∑ t ∈ Tdiag, sInd t.1 * sInd t.2.1 * sInd t.2.2) +
      (∑ t ∈ Toff, sInd t.1 * sInd t.2.1 * sInd t.2.2) := by
    rw [← Finset.sum_filter_add_sum_filter_not T (fun t => t.1 = t.2.1 ∧ t.2.1 = t.2.2)]
  rw [hsplit]
  -- Off-diagonal splits into 3 disjoint isomorphic pieces via cyclic shift `rot (a, b, c) = (b, c, a)`!
  have hoff : ∑ t ∈ Toff, sInd t.1 * sInd t.2.1 * sInd t.2.2 = 0 := by
    let P : ℕ × ℕ × ℕ → Prop := fun t => (t.1 < t.2.1 ∧ t.1 < t.2.2) ∨ (t.1 = t.2.1 ∧ t.2.1 < t.2.2)
    let rot : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ := fun t => (t.2.1, t.2.2, t.1)
    set S0 := Toff.filter P
    set S1 := Toff.filter (fun t => P (rot t))
    set S2 := Toff.filter (fun t => P (rot (rot t)))
    have hdisj01 : Disjoint S0 S1 := by
      rw [Finset.disjoint_left]
      rintro ⟨a, b, c⟩ h0 h1
      simp only [S0, S1, Finset.mem_filter, P, rot] at h0 h1
      omega
    have hdisj012 : Disjoint (S0 ∪ S1) S2 := by
      rw [Finset.disjoint_left]
      rintro ⟨a, b, c⟩ h01 h2
      simp only [Finset.mem_union, S0, S1, S2, Finset.mem_filter, P, rot] at h01 h2
      omega
    have hunion : Toff = S0 ∪ S1 ∪ S2 := by
      ext ⟨a, b, c⟩
      simp only [Finset.mem_union, S0, S1, S2, Finset.mem_filter, P, rot, Toff]
      constructor
      · intro h
        have hne := h.2
        have hcov : ((a < b ∧ a < c) ∨ (a = b ∧ b < c)) ∨
            ((b < c ∧ b < a) ∨ (b = c ∧ c < a)) ∨
            ((c < a ∧ c < b) ∨ (c = a ∧ a < b)) := by omega
        rcases hcov with h0 | h1 | h2
        · exact Or.inl (Or.inl ⟨h, h0⟩)
        · exact Or.inl (Or.inr ⟨h, h1⟩)
        · exact Or.inr ⟨h, h2⟩
      · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
    have hsum_eq1 : ∑ t ∈ S1, sInd t.1 * sInd t.2.1 * sInd t.2.2 =
        ∑ t ∈ S0, sInd t.1 * sInd t.2.1 * sInd t.2.2 := by
      refine Finset.sum_bij (fun t _ => rot t) ?_ ?_ ?_ ?_
      · rintro ⟨a, b, c⟩ ht
        simp only [S1, S0, Toff, T, R, Finset.mem_filter, Finset.mem_product, Finset.mem_range, P, rot] at ht ⊢
        refine ⟨⟨⟨⟨by omega, by omega, by omega⟩, by omega⟩, by omega⟩, ht.2⟩
      · rintro ⟨a1, b1, c1⟩ _ ⟨a2, b2, c2⟩ _ h
        simp only [rot, Prod.mk.injEq] at h
        ext <;> dsimp <;> omega
      · rintro ⟨a, b, c⟩ ht
        refine ⟨(c, a, b), ?_, rfl⟩
        simp only [S1, S0, Toff, T, R, Finset.mem_filter, Finset.mem_product, Finset.mem_range, P, rot] at ht ⊢
        refine ⟨⟨⟨⟨by omega, by omega, by omega⟩, by omega⟩, by omega⟩, ht.2⟩
      · rintro ⟨a, b, c⟩ _; dsimp [rot]; ring
    have hsum_eq2 : ∑ t ∈ S2, sInd t.1 * sInd t.2.1 * sInd t.2.2 =
        ∑ t ∈ S0, sInd t.1 * sInd t.2.1 * sInd t.2.2 := by
      refine Finset.sum_bij (fun t _ => rot (rot t)) ?_ ?_ ?_ ?_
      · rintro ⟨a, b, c⟩ ht
        simp only [S2, S0, Toff, T, R, Finset.mem_filter, Finset.mem_product, Finset.mem_range, P, rot] at ht ⊢
        refine ⟨⟨⟨⟨by omega, by omega, by omega⟩, by omega⟩, by omega⟩, ht.2⟩
      · rintro ⟨a1, b1, c1⟩ _ ⟨a2, b2, c2⟩ _ h
        simp only [rot, Prod.mk.injEq] at h
        ext <;> dsimp <;> omega
      · rintro ⟨a, b, c⟩ ht
        refine ⟨(b, c, a), ?_, rfl⟩
        simp only [S2, S0, Toff, T, R, Finset.mem_filter, Finset.mem_product, Finset.mem_range, P, rot] at ht ⊢
        refine ⟨⟨⟨⟨by omega, by omega, by omega⟩, by omega⟩, by omega⟩, ht.2⟩
      · rintro ⟨a, b, c⟩ _; dsimp [rot]; ring
    rw [hunion, Finset.sum_union hdisj012, Finset.sum_union hdisj01, hsum_eq1, hsum_eq2]
    set S := ∑ t ∈ S0, sInd t.1 * sInd t.2.1 * sInd t.2.2
    have h3 : (3 : ZMod 3) = 0 := by decide
    calc S + S + S = 3 * S := by ring
      _ = 0 := by rw [h3, zero_mul]
  rw [hoff, add_zero]
  -- Diagonal sum: nonzero only if `3 ∣ N`, when `(N/3, N/3, N/3)` gives `sInd (N/3)^3 = sInd N`!
  by_cases h3N : 3 ∣ N
  · obtain ⟨q, rfl⟩ := h3N
    have hmem : (q, q, q) ∈ Tdiag := by
      simp only [Tdiag, T, R, Finset.mem_filter, Finset.mem_product, Finset.mem_range, and_true]
      exact ⟨⟨by omega, by omega, by omega⟩, by omega⟩
    rw [Finset.sum_eq_single (q, q, q)]
    · have hcube : sInd q * sInd q * sInd q = sInd q := by
        dsimp [sInd]; split_ifs <;> decide
      rw [hcube]
      dsimp [sInd]
      have hiff : (∃ k : ℕ, q = 3 ^ k) ↔ (∃ k : ℕ, 3 * q = 3 ^ k) := by
        constructor
        · rintro ⟨k, rfl⟩; exact ⟨k + 1, by rw [pow_succ, mul_comm]⟩
        · rintro ⟨k, hk⟩
          rcases k with _ | k'
          · rw [pow_zero] at hk; omega
          · rw [pow_succ, mul_comm] at hk
            exact ⟨k', by omega⟩
      exact if_congr hiff rfl rfl
    · rintro ⟨a, b, c⟩ ht hne
      exfalso
      simp only [Tdiag, T, Finset.mem_filter] at ht
      exact hne (by ext <;> dsimp <;> omega)
    · intro hnot; exact absurd hmem hnot
  · have hempty : Tdiag = ∅ := by
      ext ⟨a, b, c⟩
      simp only [Tdiag, T, Finset.mem_filter, Finset.notMem_empty, iff_false]
      rintro ⟨⟨_, hsum⟩, h1, h2⟩
      exact h3N ⟨a, by omega⟩
    rw [hempty, Finset.sum_empty]
    dsimp [sInd]
    rw [if_neg]
    rintro ⟨k, rfl⟩
    rcases k with _ | k'
    · norm_num at hN
    · exact h3N ⟨3 ^ k', by rw [pow_succ, mul_comm]⟩

/-- Target value of `b n` in `ZMod 3` (where `a n = n * b n`). -/
private noncomputable def b3Target (n : ℕ) : ZMod 3 :=
  if n % 3 = 0 then (if n = 0 then 0 else - sInd (n / 3))
  else if n % 3 = 1 then sInd (n / 3 + 1) + conv sInd sInd (n / 3 + 1)
  else sInd (n / 3 + 1)

private lemma b3Target_rec (n : ℕ) (hn : 2 ≤ n) :
    b3Target n = ((n - 1 : ℕ) : ZMod 3) * b3Target (n - 1) -
      ∑ k ∈ (Finset.Icc 2 (n - 1)).filter (fun k => 3 ∣ k),
        b3Target k * ((n - k : ℕ) : ZMod 3) * b3Target (n - k) := by
  have hmod3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hmod3 with h0 | h1 | h2
  · -- `n = 3 * m` (`m ≥ 1`): every `n - k` with `3 ∣ k` is divisible by 3, so the sum vanishes!
    have hsum0 : ∑ k ∈ (Finset.Icc 2 (n - 1)).filter (fun k => 3 ∣ k),
        b3Target k * ((n - k : ℕ) : ZMod 3) * b3Target (n - k) = 0 := by
      refine Finset.sum_eq_zero (fun k hk => ?_)
      simp only [Finset.mem_filter, Finset.mem_Icc] at hk
      have h3 : 3 ∣ n - k := by
        obtain ⟨q1, hq1⟩ := Nat.dvd_of_mod_eq_zero h0
        obtain ⟨q2, hq2⟩ := hk.2
        exact ⟨q1 - q2, by omega⟩
      have hz : ((n - k : ℕ) : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff (n - k) 3).mpr h3
      rw [hz, mul_zero, zero_mul]
    rw [hsum0, sub_zero]
    have hm1 : 1 ≤ n / 3 := by omega
    have hprev_mod : (n - 1) % 3 = 2 := by omega
    have hprev_div : (n - 1) / 3 + 1 = n / 3 := by omega
    have hcoeff : ((n - 1 : ℕ) : ZMod 3) = -1 := by
      rw [← ZMod.natCast_mod, hprev_mod]; decide
    dsimp [b3Target]
    rw [if_pos h0, if_neg (by omega : n ≠ 0), if_neg (by omega : (n - 1) % 3 ≠ 0),
      if_neg (by omega : (n - 1) % 3 ≠ 1), hprev_div, hcoeff]
    ring
  · -- `n = 3 * m + 1` (`m ≥ 1`): first term vanishes since `3 ∣ n - 1`!
    set m := n / 3
    have hm1 : 1 ≤ m := by omega
    have hn_eq : n = 3 * m + 1 := by omega
    have hfirst0 : ((n - 1 : ℕ) : ZMod 3) = 0 :=
      (ZMod.natCast_eq_zero_iff (n - 1) 3).mpr ⟨m, by omega⟩
    rw [hfirst0, zero_mul, zero_sub]
    -- Reindex `k = 3 * r` for `r ∈ Icc 1 m`!
    have hsum_re : ∑ k ∈ (Finset.Icc 2 (n - 1)).filter (fun k => 3 ∣ k),
        b3Target k * ((n - k : ℕ) : ZMod 3) * b3Target (n - k) =
        ∑ r ∈ Finset.Icc 1 m, (- sInd r) * b3Target (3 * (m - r) + 1) := by
      refine Finset.sum_bij (fun k _ => k / 3) ?_ ?_ ?_ ?_
      · intro k hk; simp only [Finset.mem_filter, Finset.mem_Icc] at hk ⊢; omega
      · intro k1 h1 k2 h2 h; simp only [Finset.mem_filter] at h1 h2; omega
      · intro r hr; simp only [Finset.mem_Icc, Finset.mem_filter] at hr ⊢
        exact ⟨3 * r, ⟨⟨by omega, by omega⟩, ⟨r, rfl⟩⟩, by omega⟩
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_Icc] at hk
        set r := k / 3
        have hk_eq : k = 3 * r := by omega
        have hr1 : 1 ≤ r := by omega
        have hnk : n - k = 3 * (m - r) + 1 := by omega
        have hnk_mod : ((n - k : ℕ) : ZMod 3) = 1 := by
          rw [← ZMod.natCast_mod, hnk, show (3 * (m - r) + 1) % 3 = 1 by omega]; rfl
        have hbk : b3Target k = - sInd r := by
          dsimp [b3Target]; rw [if_pos (by omega), if_neg (by omega)]
        rw [hbk, hnk_mod, mul_one, hnk]
    rw [hsum_re, ← Finset.sum_neg_distrib]
    have hneg : ∑ r ∈ Finset.Icc 1 m, -((- sInd r) * b3Target (3 * (m - r) + 1)) =
        ∑ r ∈ Finset.Icc 1 m, sInd r * (sInd (m - r + 1) + conv sInd sInd (m - r + 1)) := by
      refine Finset.sum_congr rfl (fun r hr => ?_)
      have hdiv : (3 * (m - r) + 1) / 3 = m - r := by omega
      have hb : b3Target (3 * (m - r) + 1) = sInd (m - r + 1) + conv sInd sInd (m - r + 1) := by
        dsimp [b3Target]
        rw [if_neg (by omega), if_pos (by omega), hdiv]
      rw [hb]; ring
    rw [hneg]
    -- Show `∑ r ∈ Icc 1 m, sInd r * (sInd + conv sInd sInd)(m + 1 - r) = conv sInd (sInd + conv sInd sInd) (m + 1)`!
    have hconv_eq : ∑ r ∈ Finset.Icc 1 m, sInd r * (sInd (m - r + 1) + conv sInd sInd (m - r + 1)) =
        conv sInd sInd (m + 1) + conv sInd (conv sInd sInd) (m + 1) := by
      have hsplit_sum : ∑ r ∈ Finset.Icc 1 m, sInd r * (sInd (m - r + 1) + conv sInd sInd (m - r + 1)) =
          (∑ r ∈ Finset.Icc 1 m, sInd r * sInd (m + 1 - r)) +
          (∑ r ∈ Finset.Icc 1 m, sInd r * conv sInd sInd (m + 1 - r)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun r hr => ?_)
        have hrm : r ≤ m := (Finset.mem_Icc.mp hr).2
        rw [show m - r + 1 = m + 1 - r by omega]; ring
      rw [hsplit_sum]
      have hpad : ∀ g : ℕ → ZMod 3, g 0 = 0 →
          ∑ r ∈ Finset.Icc 1 m, sInd r * g (m + 1 - r) = conv sInd g (m + 1) := by
        intro g hg0
        dsimp [conv]
        refine Finset.sum_subset (fun r hr => ?_) (fun r hr hnot => ?_)
        · simp only [Finset.mem_Icc, Finset.mem_range] at hr ⊢; omega
        · simp only [Finset.mem_range, Finset.mem_Icc] at hr hnot
          have hcase : r = 0 ∨ r = m + 1 := by omega
          rcases hcase with rfl | rfl
          · rw [sInd_zero, zero_mul]
          · rw [Nat.sub_self, hg0, mul_zero]
      have hcs0 : conv sInd sInd 0 = 0 := by simp [conv, sInd_zero]
      rw [hpad sInd sInd_zero, hpad (conv sInd sInd) hcs0]
    rw [hconv_eq, conv_sInd_cube (m + 1) (by omega)]
    dsimp [b3Target]
    rw [if_neg (by omega : n % 3 ≠ 0), if_pos h1]
    ring
  · -- `n = 3 * m + 2` (`m ≥ 0`): `n - 1 ≡ 1 (mod 3)`, `n - k ≡ 2 ≡ -1 (mod 3)` for `3 ∣ k`!
    set m := n / 3
    have hn_eq : n = 3 * m + 2 := by omega
    have hcoeff1 : ((n - 1 : ℕ) : ZMod 3) = 1 := by
      rw [← ZMod.natCast_mod, show (n - 1) % 3 = 1 by omega]; rfl
    have hprev_b : b3Target (n - 1) = sInd (m + 1) + conv sInd sInd (m + 1) := by
      dsimp [b3Target]
      rw [if_neg (by omega : (n - 1) % 3 ≠ 0), if_pos (by omega : (n - 1) % 3 = 1),
        show (n - 1) / 3 = m by omega]
    rw [hcoeff1, one_mul, hprev_b]
    have hsum_re : ∑ k ∈ (Finset.Icc 2 (n - 1)).filter (fun k => 3 ∣ k),
        b3Target k * ((n - k : ℕ) : ZMod 3) * b3Target (n - k) =
        conv sInd sInd (m + 1) := by
      have hbij : ∑ k ∈ (Finset.Icc 2 (n - 1)).filter (fun k => 3 ∣ k),
          b3Target k * ((n - k : ℕ) : ZMod 3) * b3Target (n - k) =
          ∑ r ∈ Finset.Icc 1 m, sInd r * sInd (m + 1 - r) := by
        refine Finset.sum_bij (fun k _ => k / 3) ?_ ?_ ?_ ?_
        · intro k hk; simp only [Finset.mem_filter, Finset.mem_Icc] at hk ⊢; omega
        · intro k1 h1 k2 h2 h; simp only [Finset.mem_filter] at h1 h2; omega
        · intro r hr; simp only [Finset.mem_Icc, Finset.mem_filter] at hr ⊢
          exact ⟨3 * r, ⟨⟨by omega, by omega⟩, ⟨r, rfl⟩⟩, by omega⟩
        · intro k hk
          simp only [Finset.mem_filter, Finset.mem_Icc] at hk
          set r := k / 3
          have hnk_mod : ((n - k : ℕ) : ZMod 3) = -1 := by
            rw [← ZMod.natCast_mod, show (n - k) % 3 = 2 by omega]; decide
          have hbk : b3Target k = - sInd r := by
            dsimp [b3Target]; rw [if_pos (by omega), if_neg (by omega)]
          have hbnk : b3Target (n - k) = sInd (m + 1 - r) := by
            dsimp [b3Target]
            rw [if_neg (by omega), if_neg (by omega), show (n - k) / 3 + 1 = m + 1 - r by omega]
          rw [hbk, hnk_mod, hbnk]; ring
      rw [hbij]
      dsimp [conv]
      refine Finset.sum_subset (fun r hr => ?_) (fun r hr hnot => ?_)
      · simp only [Finset.mem_Icc, Finset.mem_range] at hr ⊢; omega
      · simp only [Finset.mem_range, Finset.mem_Icc] at hr hnot
        have hcase : r = 0 ∨ r = m + 1 := by omega
        rcases hcase with rfl | rfl
        · rw [sInd_zero, zero_mul]
        · rw [Nat.sub_self, sInd_zero, mul_zero]
    rw [hsum_re]
    dsimp [b3Target]
    rw [if_neg (by omega : n % 3 ≠ 0), if_neg (by omega : n % 3 ≠ 1)]
    ring

private lemma prove_a397245
    (a : ℕ → ℤ) (_ha0 : a 0 = 1) (ha1 : a 1 = 1)
    (harec : ∀ n : ℕ, 2 ≤ n →
      (a n : ℚ) = (4 * n : ℚ) * ((a (n - 1) : ℚ) +
        ∑ k ∈ Finset.Icc 2 (n - 1),
          ((4 * k ^ 2 - 1 : ℕ) : ℚ) / (4 * k : ℚ) * (a k : ℚ) * (a (n - k) : ℚ))) :
    ∀ n : ℕ, 1 ≤ n →
      ((a n : ZMod 3) = 1 ↔ (∃ m : ℕ, n + 2 = 3 ^ m) ∨ (∃ m : ℕ, n + 2 = 2 * 3 ^ m)) ∧
      ((a n : ZMod 3) = 2 ↔ ∃ j k : ℕ, j < k ∧ n + 2 = 3 ^ j + 3 ^ k) := by
  have hdvd4 : ∀ n : ℕ, 2 ≤ n → ((4 * n : ℤ) ∣ a n) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn2
      have hrec := harec n hn2
      have hsum_int : ∑ k ∈ Finset.Icc 2 (n - 1),
          ((4 * k ^ 2 - 1 : ℕ) : ℚ) / (4 * k : ℚ) * (a k : ℚ) * (a (n - k) : ℚ) =
          ((∑ k ∈ Finset.Icc 2 (n - 1),
            ((4 * k ^ 2 - 1 : ℕ) : ℤ) * (a k / (4 * k : ℤ)) * a (n - k) : ℤ) : ℚ) := by
        push_cast
        refine Finset.sum_congr rfl (fun k hk => ?_)
        simp only [Finset.mem_Icc] at hk
        have hkd := ih k (by omega) (by omega)
        have hkeq : (a k : ℚ) = (4 * k : ℚ) * ((a k / (4 * k : ℤ) : ℤ) : ℚ) := by
          have hz : a k = (4 * k : ℤ) * (a k / (4 * k : ℤ)) := (Int.mul_ediv_cancel' hkd).symm
          exact_mod_cast hz
        have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        rw [hkeq]; field_simp [hk0]
      rw [hsum_int] at hrec
      have heq_z : a n = (4 * n : ℤ) * (a (n - 1) +
          ∑ k ∈ Finset.Icc 2 (n - 1), ((4 * k ^ 2 - 1 : ℕ) : ℤ) * (a k / (4 * k : ℤ)) * a (n - k)) := by
        exact_mod_cast hrec
      exact ⟨_, heq_z⟩
  have hdvd : ∀ n : ℕ, 1 ≤ n → ((n : ℤ) ∣ a n) := by
    intro n hn
    by_cases hn1 : n = 1
    · subst hn1; simp [ha1]
    · exact dvd_trans (dvd_mul_left (n : ℤ) 4) (hdvd4 n (by omega))
  let b : ℕ → ℤ := fun n => a n / (n : ℤ)
  have hab : ∀ n : ℕ, 1 ≤ n → a n = (n : ℤ) * b n := fun n hn =>
    (Int.mul_ediv_cancel' (hdvd n hn)).symm
  have hb1 : b 1 = 1 := by simp [b, ha1]
  have hbrec : ∀ n : ℕ, 2 ≤ n →
      b n = 4 * ((n - 1 : ℕ) : ℤ) * b (n - 1) +
        ∑ k ∈ Finset.Icc 2 (n - 1),
          ((4 * k ^ 2 - 1 : ℕ) : ℤ) * b k * ((n - k : ℕ) : ℤ) * b (n - k) := by
    intro n hn2
    have hrec := harec n hn2
    have hsum_int : (4 : ℚ) * ∑ k ∈ Finset.Icc 2 (n - 1),
        ((4 * k ^ 2 - 1 : ℕ) : ℚ) / (4 * k : ℚ) * (a k : ℚ) * (a (n - k) : ℚ) =
        ((∑ k ∈ Finset.Icc 2 (n - 1),
          ((4 * k ^ 2 - 1 : ℕ) : ℤ) * b k * ((n - k : ℕ) : ℤ) * b (n - k) : ℤ) : ℚ) := by
      rw [Finset.mul_sum]; push_cast
      refine Finset.sum_congr rfl (fun k hk => ?_)
      simp only [Finset.mem_Icc] at hk
      have hkeq : (a k : ℚ) = (k : ℚ) * (b k : ℚ) := by exact_mod_cast hab k (by omega)
      have hnkeq : (a (n - k) : ℚ) = ((n - k : ℕ) : ℚ) * (b (n - k) : ℚ) := by
        exact_mod_cast hab (n - k) (by omega)
      have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      rw [hkeq, hnkeq]; field_simp [hk0]
    have ha1_eq : (a (n - 1) : ℚ) = ((n - 1 : ℕ) : ℚ) * (b (n - 1) : ℚ) := by
      exact_mod_cast hab (n - 1) (by omega)
    have han_eq : (a n : ℚ) = (n : ℚ) * (b n : ℚ) := by exact_mod_cast hab n (by omega)
    have hmul : (n : ℚ) * (b n : ℚ) = (n : ℚ) * (4 * ((n - 1 : ℕ) : ℚ) * (b (n - 1) : ℚ) +
        (4 : ℚ) * ∑ k ∈ Finset.Icc 2 (n - 1),
          ((4 * k ^ 2 - 1 : ℕ) : ℚ) / (4 * k : ℚ) * (a k : ℚ) * (a (n - k) : ℚ)) := by
      rw [← han_eq, hrec, ha1_eq]; ring
    rw [hsum_int] at hmul
    have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hq := mul_left_cancel₀ hn0 hmul
    exact_mod_cast hq
  have hb3 : ∀ n : ℕ, 1 ≤ n → (b n : ZMod 3) = b3Target n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hn1 : n = 1
      · subst hn1; rw [hb1]
        have hs1 : sInd 1 = 1 := if_pos ⟨0, by norm_num⟩
        have hcs1 : conv sInd sInd 1 = 0 := by
          simp [conv, Finset.sum_range_succ, sInd_zero]
        simp [b3Target, hs1, hcs1]
      · have hn2 : 2 ≤ n := by omega
        have h := congr_arg (Int.cast (R := ZMod 3)) (hbrec n hn2)
        push_cast at h
        have h41 : (4 : ZMod 3) = 1 := by decide
        rw [h41, one_mul] at h
        rw [h, ih (n - 1) (by omega) (by omega), b3Target_rec n hn2, sub_eq_add_neg]
        congr 1
        rw [← Finset.sum_neg_distrib,
          ← Finset.sum_subset (s₁ := (Finset.Icc 2 (n - 1)).filter (fun k => 3 ∣ k)) (Finset.filter_subset _ _)]
        · refine Finset.sum_congr rfl (fun k hk => ?_)
          simp only [Finset.mem_filter, Finset.mem_Icc] at hk
          have hk1 : 1 ≤ k := by omega
          have hnk1 : 1 ≤ n - k := by omega
          rw [ih k (by omega) hk1, ih (n - k) (by omega) hnk1]
          have hk3 : ((4 * k ^ 2 - 1 : ℕ) : ZMod 3) = -1 := by
            have h1 : 1 ≤ 4 * k ^ 2 := by nlinarith
            rw [Nat.cast_sub h1]; push_cast
            have hk0 : (k : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff k 3).mpr hk.2
            rw [hk0]; ring
          rw [hk3]; ring
        · intro k hk hnot
          simp only [Finset.mem_filter, Finset.mem_Icc, not_and] at hk hnot
          have hnd : ¬ 3 ∣ k := hnot hk
          have hsq0 : ((4 * k ^ 2 - 1 : ℕ) : ZMod 3) = 0 := by
            have h1 : 1 ≤ 4 * k ^ 2 := by nlinarith
            rw [Nat.cast_sub h1]; push_cast
            have hmod : k % 3 = 1 ∨ k % 3 = 2 := by omega
            rcases hmod with h | h
            · have hk1 : (k : ZMod 3) = 1 := by rw [← ZMod.natCast_mod, h]; rfl
              rw [hk1]; decide
            · have hk2 : (k : ZMod 3) = 2 := by rw [← ZMod.natCast_mod, h]; rfl
              rw [hk2]; decide
          rw [hsq0, zero_mul, zero_mul, zero_mul]
  intro n hn
  have ha3 : (a n : ZMod 3) = (n : ZMod 3) * b3Target n := by
    rw [hab n hn]; push_cast; rw [hb3 n hn]
  rw [ha3]
  have hmod3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hmod3 with h0 | h1 | h2
  · have hn0 : (n : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff n 3).mpr (Nat.dvd_of_mod_eq_zero h0)
    rw [hn0, zero_mul]
    constructor
    · constructor
      · intro h; exact absurd h (by decide)
      · rintro (⟨k, hk⟩ | ⟨k, hk⟩)
        · rcases k with _ | k'
          · norm_num at hk; omega
          · rw [pow_succ] at hk; omega
        · rcases k with _ | k'
          · norm_num at hk; omega
          · rw [pow_succ] at hk; omega
    · constructor
      · intro h; exact absurd h (by decide)
      · rintro ⟨j, k, hjk, hsum⟩
        rcases j with _ | j'
        · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
          rw [pow_zero, pow_succ] at hsum; omega
        · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
          rw [pow_succ, pow_succ] at hsum; omega
  · set m := n / 3
    have hn_eq : n = 3 * m + 1 := by omega
    have hn1 : (n : ZMod 3) = 1 := by rw [← ZMod.natCast_mod, h1]; rfl
    have hb_eq : b3Target n = sInd (m + 1) + conv sInd sInd (m + 1) := by
      dsimp [b3Target]; rw [if_neg (by omega), if_pos h1]
    rw [hn1, one_mul, hb_eq, conv_sInd_sInd (m + 1)]
    have hiff1 : (∃ k, m + 1 = 3 ^ k) ↔ (∃ k, n + 2 = 3 ^ k) := by
      constructor
      · rintro ⟨k, hk⟩; exact ⟨k + 1, by rw [pow_succ]; omega⟩
      · rintro ⟨k, hk⟩
        rcases k with _ | k'
        · norm_num at hk; omega
        · rw [pow_succ] at hk; exact ⟨k', by omega⟩
    have hiff2 : (∃ k, m + 1 = 2 * 3 ^ k) ↔ (∃ k, n + 2 = 2 * 3 ^ k) := by
      constructor
      · rintro ⟨k, hk⟩; exact ⟨k + 1, by rw [pow_succ]; omega⟩
      · rintro ⟨k, hk⟩
        rcases k with _ | k'
        · norm_num at hk; omega
        · rw [pow_succ] at hk; exact ⟨k', by omega⟩
    have hiff3 : (∃ j k, j < k ∧ m + 1 = 3 ^ j + 3 ^ k) ↔ (∃ j k, j < k ∧ n + 2 = 3 ^ j + 3 ^ k) := by
      constructor
      · rintro ⟨j, k, hjk, h⟩; exact ⟨j + 1, k + 1, by omega, by rw [pow_succ, pow_succ]; omega⟩
      · rintro ⟨j, k, hjk, h⟩
        rcases j with _ | j'
        · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
          rw [pow_zero, pow_succ] at h; omega
        · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
          rw [pow_succ, pow_succ] at h; exact ⟨j', k', by omega, by omega⟩
    rw [← hiff1, ← hiff2, ← hiff3]
    dsimp [sInd]
    by_cases hp1 : ∃ k, m + 1 = 3 ^ k
    · have hnot2 : ¬ ∃ k, m + 1 = 2 * 3 ^ k := by
        obtain ⟨a, ha⟩ := hp1; rintro ⟨b, hb⟩; exact pow3_ne_two_pow3 a b (ha.symm.trans hb)
      have hnot3 : ¬ ∃ j k, j < k ∧ m + 1 = 3 ^ j + 3 ^ k := by
        obtain ⟨a, ha⟩ := hp1; rintro ⟨j, k, hjk, h⟩; exact pow3_ne_sum_distinct hjk (ha.symm.trans h)
      rw [if_pos hp1, if_neg hnot2, if_neg hnot3, add_zero]
      exact ⟨⟨fun _ => Or.inl hp1, fun _ => rfl⟩, ⟨fun h => absurd h (by decide), fun h => absurd h hnot3⟩⟩
    · by_cases hp2 : ∃ k, m + 1 = 2 * 3 ^ k
      · have hnot3 : ¬ ∃ j k, j < k ∧ m + 1 = 3 ^ j + 3 ^ k := by
          obtain ⟨a, ha⟩ := hp2; rintro ⟨j, k, hjk, h⟩; exact two_pow3_ne_sum_distinct hjk (ha.symm.trans h)
        rw [if_neg hp1, if_pos hp2, zero_add]
        exact ⟨⟨fun _ => Or.inr hp2, fun _ => rfl⟩, ⟨fun h => absurd h (by decide), fun h => absurd h hnot3⟩⟩
      · by_cases hp3 : ∃ j k, j < k ∧ m + 1 = 3 ^ j + 3 ^ k
        · rw [if_neg hp1, if_neg hp2, if_pos hp3, zero_add]
          exact ⟨⟨fun h => absurd h (by decide), fun h => by rcases h with h | h <;> contradiction⟩,
            ⟨fun _ => hp3, fun _ => rfl⟩⟩
        · rw [if_neg hp1, if_neg hp2, if_neg hp3, add_zero]
          exact ⟨⟨fun h => absurd h (by decide), fun h => by rcases h with h | h <;> contradiction⟩,
            ⟨fun h => absurd h (by decide), fun h => absurd h hp3⟩⟩
  · set m := n / 3
    have hn_eq : n = 3 * m + 2 := by omega
    have hn2 : (n : ZMod 3) = 2 := by rw [← ZMod.natCast_mod, h2]; rfl
    have hb_eq : b3Target n = sInd (m + 1) := by
      dsimp [b3Target]; rw [if_neg (by omega), if_neg (by omega)]
    rw [hn2, hb_eq]
    have hnot1 : ¬ ((∃ k, n + 2 = 3 ^ k) ∨ (∃ k, n + 2 = 2 * 3 ^ k)) := by
      rintro (⟨k, hk⟩ | ⟨k, hk⟩)
      · rcases k with _ | k'
        · norm_num at hk; omega
        · rw [pow_succ] at hk; omega
      · rcases k with _ | k'
        · norm_num at hk; omega
        · rw [pow_succ] at hk; omega
    have hiff3 : (∃ k, m + 1 = 3 ^ k) ↔ (∃ j k, j < k ∧ n + 2 = 3 ^ j + 3 ^ k) := by
      constructor
      · rintro ⟨k, hk⟩; exact ⟨0, k + 1, by omega, by rw [pow_zero, pow_succ]; omega⟩
      · rintro ⟨j, k, hjk, h⟩
        rcases j with _ | j'
        · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
          rw [pow_zero, pow_succ] at h; exact ⟨k', by omega⟩
        · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
          rw [pow_succ, pow_succ] at h; omega
    dsimp [sInd]
    by_cases hp : ∃ k, m + 1 = 3 ^ k
    · rw [if_pos hp, mul_one]
      exact ⟨⟨fun h => absurd h (by decide), fun h => absurd h hnot1⟩,
        ⟨fun _ => hiff3.mp hp, fun _ => rfl⟩⟩
    · rw [if_neg hp, mul_zero]
      exact ⟨⟨fun h => absurd h (by decide), fun h => absurd h hnot1⟩,
        ⟨fun h => absurd h (by decide), fun h => absurd (hiff3.mpr h) hp⟩⟩

end OMA.P_oeis_a397245

theorem OMA.solution : type_of% @OMA.S_oeis_a397245.main := by
  intro a ha0 ha1 harec
  have hpos := OMA.P_oeis_a397245.prove_a397245 a ha0 ha1 harec
  constructor
  · intro n
    rcases n with _ | n'
    · rw [ha0]
      exact ⟨fun _ => Or.inr ⟨0, by norm_num⟩, fun _ => by norm_num⟩
    · exact (hpos (n' + 1) (by omega)).1
  · intro n
    rcases n with _ | n'
    · rw [ha0]
      constructor
      · intro h; exact absurd h (by decide)
      · rintro ⟨j, k, hjk, hsum⟩
        have h1 : 1 ≤ 3 ^ j := Nat.one_le_pow j 3 (by norm_num)
        have h2 : 3 ≤ 3 ^ k := by
          obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
          have := Nat.one_le_pow k' 3 (by norm_num)
          rw [pow_succ]; omega
        omega
    · exact (hpos (n' + 1) (by omega)).2
