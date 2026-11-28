import OMAStatements.S_mo_478343
import Mathlib
open OMA.S_mo_478343

/-- Blocks of length `m` separated by gaps of length `m`: `L` blocks inside `{1, ..., 2mL}`. -/
def blocks (m L : ℕ) : Finset ℕ :=
  (Finset.range L ×ˢ Finset.range m).image fun p => 2 * m * p.1 + p.2 + 1

lemma mem_blocks {m L x : ℕ} :
    x ∈ blocks m L ↔ ∃ j < L, ∃ r < m, x = 2 * m * j + r + 1 := by
  unfold blocks
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨j, r⟩, hp, rfl⟩
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    exact ⟨j, hp.1, r, hp.2, rfl⟩
  · rintro ⟨j, hj, r, hr, rfl⟩
    exact ⟨(j, r), by rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]; exact ⟨hj, hr⟩, rfl⟩

lemma card_blocks (m L : ℕ) : (blocks m L).card = L * m := by
  unfold blocks
  rw [Finset.card_image_of_injOn, Finset.card_product, Finset.card_range, Finset.card_range]
  rintro ⟨j1, r1⟩ h1 ⟨j2, r2⟩ h2 h
  simp only [Finset.coe_product, Set.mem_prod, Finset.coe_range, Set.mem_Iio] at h1 h2
  simp only at h
  have hm : 0 < m := by omega
  have e1 : (2 * m * j1 + r1) / (2 * m) = j1 := by
    rw [show 2 * m * j1 + r1 = r1 + 2 * m * j1 by ring, Nat.add_mul_div_left _ _ (by omega),
      Nat.div_eq_of_lt (by omega), zero_add]
  have e2 : (2 * m * j2 + r2) / (2 * m) = j2 := by
    rw [show 2 * m * j2 + r2 = r2 + 2 * m * j2 by ring, Nat.add_mul_div_left _ _ (by omega),
      Nat.div_eq_of_lt (by omega), zero_add]
  have hj : j1 = j2 := by rw [← e1, ← e2]; congr 1; omega
  subst hj
  have : r1 = r2 := by omega
  rw [this]

lemma blocks_sub (m L : ℕ) : blocks m L ⊆ Finset.Icc 1 (2 * m * L) := by
  intro x hx
  obtain ⟨j, hj, r, hr, rfl⟩ := mem_blocks.mp hx
  rw [Finset.mem_Icc]
  constructor
  · omega
  · have : 2 * m * (j + 1) ≤ 2 * m * L := Nat.mul_le_mul_left _ hj
    nlinarith

/-- A gap-bounded subset of the blocks lies in one block. -/
lemma one_block (m L : ℕ) (I : Finset ℕ) (hI : I ⊆ blocks m L)
    (hgap : ∀ x ∈ I, ∀ y ∈ I, x < y → (∀ z ∈ I, ¬ (x < z ∧ z < y)) → y - x ≤ m)
    (hne : I.Nonempty) :
    ∃ j, ∀ y ∈ I, ∃ r < m, y = 2 * m * j + r + 1 := by
  set x0 := I.min' hne with hx0
  have hx0I : x0 ∈ I := I.min'_mem hne
  obtain ⟨j0, _, r0, hr0, hx0e⟩ := mem_blocks.mp (hI hx0I)
  refine ⟨j0, ?_⟩
  by_contra hcon
  push Not at hcon
  set S := I.filter fun y => ∀ r < m, y ≠ 2 * m * j0 + r + 1 with hS
  have hSne : S.Nonempty := by
    obtain ⟨y, hy, hy2⟩ := hcon
    exact ⟨y, Finset.mem_filter.mpr ⟨hy, hy2⟩⟩
  set y := S.min' hSne with hy
  have hyS : y ∈ S := S.min'_mem hSne
  have hyI : y ∈ I := (Finset.mem_filter.mp hyS).1
  have hy2 := (Finset.mem_filter.mp hyS).2
  have hxy : x0 < y := by
    rcases lt_trichotomy x0 y with h | h | h
    · exact h
    · exact absurd hx0e (h ▸ hy2 r0 hr0)
    · exact absurd (I.min'_le y hyI) (by rw [← hx0]; omega)
  set P := I.filter fun z => z < y with hP
  have hPne : P.Nonempty := ⟨x0, Finset.mem_filter.mpr ⟨hx0I, hxy⟩⟩
  set x' := P.max' hPne with hx'
  have hx'P : x' ∈ P := P.max'_mem hPne
  have hx'I : x' ∈ I := (Finset.mem_filter.mp hx'P).1
  have hx'y : x' < y := (Finset.mem_filter.mp hx'P).2
  -- x' is in block j0, since it is smaller than the least element outside block j0
  have hx'blk : ∃ r < m, x' = 2 * m * j0 + r + 1 := by
    by_contra h
    push Not at h
    have : x' ∈ S := Finset.mem_filter.mpr ⟨hx'I, h⟩
    have := S.min'_le x' this
    rw [← hy] at this
    omega
  obtain ⟨r', hr', hx'e⟩ := hx'blk
  have hcons : ∀ z ∈ I, ¬ (x' < z ∧ z < y) := by
    rintro z hz ⟨h1, h2⟩
    have : z ∈ P := Finset.mem_filter.mpr ⟨hz, h2⟩
    have := P.le_max' z this
    rw [← hx'] at this
    omega
  have hgy := hgap x' hx'I y hyI hx'y hcons
  obtain ⟨j, _, r, hr, hye⟩ := mem_blocks.mp (hI hyI)
  have hjj : j ≠ j0 := by
    intro h
    exact hy2 r hr (by rw [hye, h])
  rcases Nat.lt_or_gt_of_ne hjj with h | h
  · have : 2 * m * (j + 1) ≤ 2 * m * j0 := Nat.mul_le_mul_left _ h
    nlinarith
  · have h1 : 2 * m * (j0 + 1) ≤ 2 * m * j := Nat.mul_le_mul_left _ h
    have e : 2 * m * (j0 + 1) = 2 * m * j0 + 2 * m := by ring
    omega

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_478343.main) := by
  intro h
  obtain ⟨b, hb, hgood⟩ := h (1 / 2) (by norm_num)
  set m : ℕ := ⌈1 / b⌉₊ + 1 with hm
  set L : ℕ := ⌈1 / b⌉₊ + 1 with hL
  have hb1 : 1 / b ≤ (⌈1 / b⌉₊ : ℝ) := Nat.le_ceil _
  have hm1 : 1 ≤ m := by omega
  have hL1 : 1 ≤ L := by omega
  have hn : 1 ≤ 2 * m * L := by nlinarith
  have hA := hgood (2 * m * L) hn (blocks m L) (blocks_sub m L) (by
    rw [card_blocks]
    push_cast
    nlinarith)
  obtain ⟨I, hIA, hIc, hIg⟩ := hA
  -- gaps are at most m - 1 as natural numbers
  have hgap : ∀ x ∈ I, ∀ y ∈ I, x < y → (∀ z ∈ I, ¬ (x < z ∧ z < y)) → y - x ≤ m := by
    intro x hx y hy hxy hc
    have h1 := hIg x hx y hy hxy hc
    have h2 : ((y - x : ℕ) : ℝ) ≤ (⌈1 / b⌉₊ : ℝ) := by
      rw [Nat.cast_sub hxy.le]; linarith
    have h3 : y - x ≤ ⌈1 / b⌉₊ := by exact_mod_cast h2
    omega
  -- b * n > m
  have hbig : (m : ℝ) < b * ((2 * m * L : ℕ) : ℝ) := by
    have hbL : 1 < b * L := by
      have : (1 / b) < (L : ℝ) := by rw [hL]; push_cast; linarith
      rw [div_lt_iff₀ hb] at this
      linarith
    push_cast
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    nlinarith
  rcases I.eq_empty_or_nonempty with hI0 | hIne
  · rw [hI0, Finset.card_empty] at hIc
    push_cast at hIc hbig
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    linarith
  obtain ⟨j, hj⟩ := one_block m L I hIA hgap hIne
  have hsub : I ⊆ (Finset.range m).image fun r => 2 * m * j + r + 1 := by
    intro y hy
    obtain ⟨r, hr, rfl⟩ := hj y hy
    exact Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr hr, rfl⟩
  have hcard : I.card ≤ m :=
    (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))
  have : (I.card : ℝ) ≤ m := by exact_mod_cast hcard
  linarith
