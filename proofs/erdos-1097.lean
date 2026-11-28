import OMAStatements.S_erdos_1097

-- Problem: Erdős Problem 1097
-- Credit: @EmadY
--
-- Disproof of the O(n^(3/2)) upper bound on the number of common differences of
-- three-term arithmetic progressions in an n-element integer set.
-- Following Koishi Chan's 3-block reduction to restricted sums-vs-differences
-- (Bourgain (1999), Marius Lemm (γ ≈ 1.77898), Katz–Tao (11/6) upper bound),
-- Ruzsa's minimal 2-element seed X0 = Z0 = S0 = {0, 1} with differences D0 = {-1, 0, 1}
-- already achieves |D0|^2 = 9 > 8 = 2^3 (exponent log 3 / log 2 ≈ 1.58496 > 3/2)
-- via ternary Cantor blowup.

private def cantor : ℕ → Finset ℤ
  | 0 => {0}
  | n + 1 => (cantor n).image (3 * ·) ∪ (cantor n).image (fun x => 3 * x + 1)

private lemma card_cantor_le : ∀ n : ℕ, (cantor n).card ≤ 2 ^ n
  | 0 => by simp [cantor]
  | n + 1 => by
    have h1 : ((cantor n).image (3 * ·)).card ≤ (cantor n).card := Finset.card_image_le
    have h2 : ((cantor n).image (fun x => 3 * x + 1)).card ≤ (cantor n).card := Finset.card_image_le
    have h3 : (cantor (n + 1)).card ≤
        ((cantor n).image (3 * ·)).card + ((cantor n).image (fun x => 3 * x + 1)).card :=
      Finset.card_union_le _ _
    have ih := card_cantor_le n
    rw [pow_succ']
    omega

private lemma cantor_witness : ∀ (n : ℕ) {t : ℕ}, t < 3 ^ n →
    ∃ x ∈ cantor n, ∃ z ∈ cantor n, x + z ∈ cantor n ∧
      2 * (z - x) = 2 * (t : ℤ) - ((3 : ℤ) ^ n - 1)
  | 0, t, ht => by
    simp only [pow_zero] at ht ⊢
    exact ⟨0, by simp [cantor], 0, by simp [cantor], by simp [cantor], by omega⟩
  | n + 1, t, ht => by
    have hq : t / 3 < 3 ^ n := by rw [pow_succ'] at ht; omega
    obtain ⟨x0, hx0, z0, hz0, hs0, hd0⟩ := cantor_witness n hq
    have mem0 : ∀ {u : ℤ}, u ∈ cantor n → 3 * u ∈ cantor (n + 1) := fun hu =>
      Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, hu, rfl⟩)
    have mem1 : ∀ {u : ℤ}, u ∈ cantor n → 3 * u + 1 ∈ cantor (n + 1) := fun hu =>
      Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, hu, rfl⟩)
    rcases (by omega : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2) with hr | hr | hr
    · refine ⟨3 * x0 + 1, mem1 hx0, 3 * z0, mem0 hz0, ?_, by rw [pow_succ']; omega⟩
      rw [show 3 * x0 + 1 + 3 * z0 = 3 * (x0 + z0) + 1 by ring]; exact mem1 hs0
    · refine ⟨3 * x0, mem0 hx0, 3 * z0, mem0 hz0, ?_, by rw [pow_succ']; omega⟩
      rw [show 3 * x0 + 3 * z0 = 3 * (x0 + z0) by ring]; exact mem0 hs0
    · refine ⟨3 * x0, mem0 hx0, 3 * z0 + 1, mem1 hz0, ?_, by rw [pow_succ']; omega⟩
      rw [show 3 * x0 + (3 * z0 + 1) = 3 * (x0 + z0) + 1 by ring]; exact mem1 hs0

private lemma three_pow_mod_two : ∀ n : ℕ, ((3 : ℤ) ^ n) % 2 = 1
  | 0 => rfl
  | n + 1 => by rw [pow_succ, Int.mul_emod, three_pow_mod_two n]; rfl

private def mkA (n : ℕ) : Finset ℤ :=
  let L : ℤ := ((3 : ℤ) ^ n + 1) / 2
  (cantor n).image (2 * ·) ∪ (cantor n).image (L + ·) ∪
    (cantor n).image (fun z => 2 * L + 2 * z)

private lemma card_mkA_le (n : ℕ) : (mkA n).card ≤ 4 * 2 ^ n := by
  dsimp [mkA]
  set L : ℤ := ((3 : ℤ) ^ n + 1) / 2
  have h1 : ((cantor n).image (2 * ·)).card ≤ (cantor n).card := Finset.card_image_le
  have h2 : ((cantor n).image (L + ·)).card ≤ (cantor n).card := Finset.card_image_le
  have h3 : ((cantor n).image (fun z => 2 * L + 2 * z)).card ≤ (cantor n).card :=
    Finset.card_image_le
  have h4 := Finset.card_union_le
    ((cantor n).image (2 * ·) ∪ (cantor n).image (L + ·))
    ((cantor n).image (fun z => 2 * L + 2 * z))
  have h5 := Finset.card_union_le ((cantor n).image (2 * ·)) ((cantor n).image (L + ·))
  have ih := card_cantor_le n
  omega

private lemma le_card_apDiffs_mkA (n : ℕ) :
    3 ^ n ≤ (OMA.S_erdos_1097.apDiffs (mkA n)).card := by
  have hinj : Function.Injective (fun t : ℕ => (t : ℤ) + 1) := fun _ _ h => by dsimp at h; omega
  rw [← Finset.card_range (3 ^ n), ← Finset.card_image_of_injective _ hinj]
  apply Finset.card_le_card
  intro δ hδ
  rcases Finset.mem_image.mp hδ with ⟨t, ht, rfl⟩
  obtain ⟨x, hx, z, hz, hxz, hdz⟩ := cantor_witness n (Finset.mem_range.mp ht)
  set L : ℤ := ((3 : ℤ) ^ n + 1) / 2
  have hL : 2 * L = (3 : ℤ) ^ n + 1 := by have := three_pow_mod_two n; omega
  have hd_eq : (t : ℤ) + 1 = L + (z - x) := by omega
  have ha : 2 * x ∈ mkA n :=
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
  have hb : 2 * x + ((t : ℤ) + 1) ∈ mkA n :=
    Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨x + z, hxz, by omega⟩))
  have hc : 2 * x + 2 * ((t : ℤ) + 1) ∈ mkA n :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z, hz, by omega⟩)
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_image.mpr ⟨(2 * x, 2 * x + ((t : ℤ) + 1)), Finset.mem_product.mpr ⟨ha, hb⟩, by omega⟩,
     by omega, 2 * x, ha, hb, hc⟩

private lemma pow_grow_nat {P Q : ℕ} (hPQ : P + 1 ≤ Q) :
    ∀ k : ℕ, k * P ^ k ≤ P * Q ^ k
  | 0 => by simp
  | k + 1 => by
    have ih := pow_grow_nat hPQ k
    have hle : P ^ k ≤ Q ^ k := Nat.pow_le_pow_left (Nat.le_of_succ_le hPQ) k
    calc (k + 1) * P ^ (k + 1)
        = k * P ^ k * P + P * P ^ k := by ring
      _ ≤ P * Q ^ k * P + P * Q ^ k :=
          Nat.add_le_add (Nat.mul_le_mul_right P ih) (Nat.mul_le_mul_left P hle)
      _ = P * Q ^ k * (P + 1) := by ring
      _ ≤ P * Q ^ k * Q := Nat.mul_le_mul_left _ hPQ
      _ = P * Q ^ (k + 1) := by ring

private lemma rpow_three_halves_card_le {c m k : ℕ} (hc : c ≤ 4 * m ^ (2 * k)) :
    (c : ℝ) ^ ((3 : ℝ) / 2) ≤ 8 * (((m ^ 3) ^ k : ℕ) : ℝ) := by
  let u : ℝ := ((2 * m ^ k : ℕ) : ℝ)
  have hu : 0 ≤ u := Nat.cast_nonneg _
  have hc_nat : c ≤ (2 * m ^ k) ^ 2 := by
    calc c ≤ 4 * m ^ (2 * k) := hc
      _ = (2 * m ^ k) ^ 2 := by rw [Nat.two_mul, pow_add]; ring
  have hc_real : (c : ℝ) ≤ u ^ 2 := by
    simpa [u, Nat.cast_pow] using (Nat.cast_le (α := ℝ)).mpr hc_nat
  have hrpow : (c : ℝ) ^ ((3 : ℝ) / 2) ≤ (u ^ 2) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow (Nat.cast_nonneg c) hc_real (by positivity)
  have h23 : ((2 : ℕ) : ℝ) * ((3 : ℝ) / 2) = ((3 : ℕ) : ℝ) := by norm_num
  have hu3 : (u ^ 2) ^ ((3 : ℝ) / 2) = u ^ 3 := by
    rw [← Real.rpow_natCast u 2, ← Real.rpow_mul hu, h23, Real.rpow_natCast u 3]
  have hnat3 : (2 * m ^ k) ^ 3 = 8 * (m ^ 3) ^ k := by
    calc (2 * m ^ k) ^ 3 = 8 * (m ^ k) ^ 3 := by ring
      _ = 8 * m ^ (k * 3) := by rw [← pow_mul]
      _ = 8 * m ^ (3 * k) := by rw [Nat.mul_comm k 3]
      _ = 8 * (m ^ 3) ^ k := by rw [pow_mul]
  have hu3_val : u ^ 3 = 8 * (((m ^ 3) ^ k : ℕ) : ℝ) := by
    have hcast : (((2 * m ^ k) ^ 3 : ℕ) : ℝ) = ((8 * (m ^ 3) ^ k : ℕ) : ℝ) :=
      congrArg Nat.cast hnat3
    simpa [u, Nat.cast_pow, Nat.cast_mul] using hcast
  linarith

private theorem not_apDiffs_rpow_bound
    {m D : ℕ} (hm : 0 < m) (hDm : m ^ 3 < D ^ 2)
    (A : ℕ → Finset ℤ)
    (hcard : ∀ k : ℕ, (A k).card ≤ 4 * m ^ (2 * k))
    (hdiff : ∀ k : ℕ, D ^ (2 * k) ≤ (OMA.S_erdos_1097.apDiffs (A k)).card) :
    ¬ (∃ C : ℝ, ∀ S : Finset ℤ,
        ((OMA.S_erdos_1097.apDiffs S).card : ℝ) ≤ C * (S.card : ℝ) ^ ((3 : ℝ) / 2)) := by
  rintro ⟨C, hC⟩
  let P : ℕ := m ^ 3
  let Q : ℕ := D ^ 2
  let C' : ℝ := max C 0
  have hC'_nonneg : 0 ≤ C' := le_max_right C 0
  obtain ⟨k, hk⟩ := exists_nat_gt (8 * C' * (P : ℝ))
  have hPk_pos : (0 : ℝ) < ((P ^ k : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_pos (Nat.pow_pos hm)
  have hlt : (8 * C' * (P : ℝ)) * ((P ^ k : ℕ) : ℝ) < (k : ℝ) * ((P ^ k : ℕ) : ℝ) :=
    mul_lt_mul_of_pos_right hk hPk_pos
  have hgrow : (k : ℝ) * ((P ^ k : ℕ) : ℝ) ≤ (P : ℝ) * ((Q ^ k : ℕ) : ℝ) := by
    have hnat : k * P ^ k ≤ P * Q ^ k := pow_grow_nat hDm k
    simpa [Nat.cast_mul] using (Nat.cast_le (α := ℝ)).mpr hnat
  have hQk : ((Q ^ k : ℕ) : ℝ) ≤ ((OMA.S_erdos_1097.apDiffs (A k)).card : ℝ) := by
    have h1 : Q ^ k ≤ (OMA.S_erdos_1097.apDiffs (A k)).card := by
      simpa [Q, pow_mul] using hdiff k
    exact Nat.cast_le.mpr h1
  have hAk := hC (A k)
  have hrpow_nonneg : 0 ≤ (((A k).card : ℝ) ^ ((3 : ℝ) / 2)) := by positivity
  have hCC' : C * (((A k).card : ℝ) ^ ((3 : ℝ) / 2)) ≤
      C' * (((A k).card : ℝ) ^ ((3 : ℝ) / 2)) :=
    mul_le_mul_of_nonneg_right (le_max_left C 0) hrpow_nonneg
  have hcard_rpow : (((A k).card : ℝ) ^ ((3 : ℝ) / 2)) ≤ 8 * ((P ^ k : ℕ) : ℝ) :=
    rpow_three_halves_card_le (hcard k)
  have hupper : ((Q ^ k : ℕ) : ℝ) ≤ 8 * C' * ((P ^ k : ℕ) : ℝ) := by
    have hmul : C' * (((A k).card : ℝ) ^ ((3 : ℝ) / 2)) ≤ C' * (8 * ((P ^ k : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hcard_rpow hC'_nonneg
    linarith
  have hP_nonneg : (0 : ℝ) ≤ (P : ℝ) := Nat.cast_nonneg P
  have hupperP : (P : ℝ) * ((Q ^ k : ℕ) : ℝ) ≤ (P : ℝ) * (8 * C' * ((P ^ k : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left hupper hP_nonneg
  linarith

theorem OMA.disproof : ¬ (type_of% @OMA.S_erdos_1097.main) := by
  exact not_apDiffs_rpow_bound (m := 2) (D := 3) (by positivity) (by norm_num)
    (fun k => mkA (2 * k)) (fun k => card_mkA_le (2 * k)) (fun k => le_card_apDiffs_mkA (2 * k))
