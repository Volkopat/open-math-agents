import OMAReductions.R_Erdos1186_erdos_1186_variants_prs_conjecture_R1

/-!
# Exact count of mixed endpoint–midpoint pairs

For the Parrilo–Robertson–Saracino reference coloring, separate each position
into its index among 548 equal cells and its residue within a cell. The
residues determine one of three possible bands of cell indices. Each band
has the same number of differently colored cell pairs.
-/

open Finset

namespace OMA.Erdos1186ReferenceCount

private def color (a : ℕ) : Bool :=
  a < 28 || (34 ≤ a && a < 62) || (99 ≤ a && a < 158) ||
    (274 ≤ a && a < 390) || (449 ≤ a && a < 486) || (514 ≤ a && a < 520)

private def block (c : Bool) (j : Fin 6) : ℕ × ℕ :=
  if c then (![(0, 28), (34, 62), (99, 158), (274, 390), (449, 486), (514, 520)]) j
  else (![(28, 34), (62, 99), (158, 274), (390, 449), (486, 514), (520, 548)]) j

private theorem color_iff_mem_block (c : Bool) {b : ℕ} (hb : b < 548) :
    color b = c ↔ ∃ j : Fin 6, (block c j).1 ≤ b ∧ b < (block c j).2 := by
  cases c <;> simp [Fin.exists_fin_succ, color, block] <;> omega

private theorem block_upper_le_lower :
    ∀ (c : Bool) (i j : Fin 6), i < j → (block c i).2 ≤ (block c j).1 := by
  decide

private theorem color_ne_iff {a b : ℕ} :
    color a ≠ color b ↔ color b = !color a := by
  cases color a <;> cases color b <;> decide

private def band (s : ℤ) : Finset (ℕ × ℕ) :=
  (range 548 ×ˢ range 548).filter fun p =>
    color p.1 ≠ color p.2 ∧ s ≤ 2 * (p.2 : ℤ) - p.1 ∧
      2 * (p.2 : ℤ) - p.1 < s + 548

private theorem mem_band (s : ℤ) (a b : ℕ) :
    (a, b) ∈ band s ↔ a < 548 ∧ b < 548 ∧ color a ≠ color b ∧
      s ≤ 2 * (b : ℤ) - a ∧ 2 * (b : ℤ) - a < s + 548 := by
  simp only [band, mem_filter, mem_product, mem_range, and_assoc]

private def row (s : ℤ) (a : ℕ) : Finset ℕ :=
  (range 548).filter fun b =>
    color a ≠ color b ∧ s ≤ 2 * (b : ℤ) - a ∧ 2 * (b : ℤ) - a < s + 548

private def lower (s : ℤ) (a : ℕ) : ℕ := (((a : ℤ) + s + 1) / 2).toNat

private def upper (s : ℤ) (a : ℕ) : ℕ := (((a : ℤ) + s + 547) / 2 + 1).toNat

private def clipped (L U : ℕ) (c : Bool) (j : Fin 6) : Finset ℕ :=
  Ico (max L (block c j).1) (min U (block c j).2)

private theorem clip_disjoint {L U : ℕ} {c : Bool} {i j : Fin 6} (hij : i < j) :
    Disjoint (clipped L U c i) (clipped L U c j) := by
  apply disjoint_left.mpr
  intro b hbi hbj
  have hi := (mem_Ico.mp hbi).2.trans_le (min_le_right U (block c i).2)
  have hj := (le_max_right L (block c j).1).trans (mem_Ico.mp hbj).1
  exact (not_lt_of_ge ((block_upper_le_lower c i j hij).trans hj)) hi

private theorem row_eq_biUnion (s : ℤ) (a : ℕ) :
    row s a = (univ : Finset (Fin 6)).biUnion (clipped (lower s a) (upper s a) (!color a)) := by
  ext b
  have hbnds : (s ≤ 2 * (b : ℤ) - a ∧ 2 * (b : ℤ) - a < s + 548) ↔
      lower s a ≤ b ∧ b < upper s a := by
    simp only [lower, upper]
    omega
  constructor
  · intro hb
    obtain ⟨hb548, hdiff, hrange⟩ := mem_filter.mp hb
    obtain ⟨j, hj₁, hj₂⟩ := (color_iff_mem_block _ (mem_range.mp hb548)).mp
      (color_ne_iff.mp hdiff)
    obtain ⟨hl, hu⟩ := hbnds.mp hrange
    exact mem_biUnion.mpr ⟨j, mem_univ _, mem_Ico.mpr
      ⟨max_le hl hj₁, lt_min hu hj₂⟩⟩
  · intro hb
    obtain ⟨j, _, hj⟩ := mem_biUnion.mp hb
    obtain ⟨hl, hu⟩ := mem_Ico.mp hj
    have hj₁ := (le_max_right (lower s a) (block (!color a) j).1).trans hl
    have hj₂ := hu.trans_le (min_le_right (upper s a) (block (!color a) j).2)
    have hblock : ∀ (c : Bool) (i : Fin 6), (block c i).2 ≤ 548 := by decide
    have h548 := hj₂.trans_le (hblock _ _)
    exact mem_filter.mpr ⟨mem_range.mpr h548, color_ne_iff.mpr
      ((color_iff_mem_block _ h548).mpr ⟨j, hj₁, hj₂⟩),
      hbnds.mpr ⟨(le_max_left _ _).trans hl, hu.trans_le (min_le_left _ _)⟩⟩

private def rowCount (s : ℤ) (a : ℕ) : ℕ :=
  ∑ j : Fin 6, (min (upper s a) (block (!color a) j).2 -
    max (lower s a) (block (!color a) j).1)

private theorem row_card (s : ℤ) (a : ℕ) : (row s a).card = rowCount s a := by
  rw [row_eq_biUnion, card_biUnion]
  · simp only [clipped, Nat.card_Ico, rowCount]
  · intro i _ j _ hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact clip_disjoint h
    · exact (clip_disjoint h).symm

private theorem band_card_formula (s : ℤ) : (band s).card = ∑ a ∈ range 548, rowCount s a := by
  simp only [← row_card, band, row, card_eq_sum_ones, sum_filter, sum_product]

set_option maxRecDepth 3500 in
set_option maxHeartbeats 800000 in
private theorem counts :
    (∑ a ∈ range 548, rowCount (-1) a) = 80556 ∧
    (∑ a ∈ range 548, rowCount 0 a) = 80556 ∧
    (∑ a ∈ range 548, rowCount 1 a) = 80556 := by
  decide

private theorem band_card_of_cases {s : ℤ} (hs : s = -1 ∨ s = 0 ∨ s = 1) :
    (band s).card = 80556 := by
  rw [band_card_formula]
  rcases hs with rfl | rfl | rfl
  · exact counts.1
  · exact counts.2.1
  · exact counts.2.2

private def shift (W : ℕ) (r : ℕ × ℕ) : ℤ :=
  -((2 * (r.2 : ℤ) - r.1) / (W : ℤ))

private theorem shift_cases {W i j : ℕ} (hW : 0 < W) (hi : i < W) (hj : j < W) :
    shift W (i, j) = -1 ∨ shift W (i, j) = 0 ∨ shift W (i, j) = 1 := by
  have hW' : (0 : ℤ) < W := by exact_mod_cast hW
  have hlo : (-1 : ℤ) ≤ (2 * (j : ℤ) - i) / (W : ℤ) :=
    (Int.le_ediv_iff_mul_le hW').2 (by omega)
  have hhi : (2 * (j : ℤ) - i) / (W : ℤ) < 2 :=
    (Int.ediv_lt_iff_lt_mul hW').2 (by omega)
  unfold shift
  dsimp only
  omega

private def cell (W a i : ℕ) : ℕ := W * a + i + 1

private theorem cell_div {W a i : ℕ} (hW : 0 < W) (hi : i < W) :
    (cell W a i - 1) / W = a := by
  simp only [cell, Nat.add_sub_cancel, Nat.mul_add_div hW, Nat.div_eq_of_lt hi, add_zero]

private theorem cell_mod {W a i : ℕ} (hi : i < W) : (cell W a i - 1) % W = i := by
  simp only [cell, Nat.add_sub_cancel, Nat.mul_add_mod, Nat.mod_eq_of_lt hi]

private theorem cell_decode {W x : ℕ} (hx : 1 ≤ x) :
    cell W ((x - 1) / W) ((x - 1) % W) = x := by
  unfold cell
  have h := Nat.mod_add_div (x - 1) W
  omega

private theorem cell_mem {W a i : ℕ} (ha : a < 548) (hi : i < W) :
    cell W a i ∈ Icc 1 (548 * W) := by
  have hlt : W * a + i < W * 548 := calc
    W * a + i < W * a + W := Nat.add_lt_add_left hi _
    _ = W * (a + 1) := by rw [Nat.mul_succ]
    _ ≤ W * 548 := Nat.mul_le_mul_left W (by omega)
  rw [Nat.mul_comm W 548] at hlt
  exact mem_Icc.mpr ⟨by simp [cell], by unfold cell; omega⟩

private theorem cell_bounds {W : ℕ} (hW : 0 < W) (a b i j : ℕ) :
    (cell W a i + 1 ≤ 2 * cell W b j ∧ 2 * cell W b j ≤ cell W a i + 548 * W) ↔
      shift W (i, j) ≤ 2 * (b : ℤ) - a ∧
        2 * (b : ℤ) - a < shift W (i, j) + 548 := by
  let r : ℤ := 2 * (j : ℤ) - i
  let d : ℤ := 2 * (b : ℤ) - a
  have hW' : (0 : ℤ) < W := by exact_mod_cast hW
  have hdiv : (r + d * (W : ℤ)) / (W : ℤ) = r / (W : ℤ) + d :=
    Int.add_mul_ediv_right r d hW'.ne'
  have hlow : 0 ≤ r + d * (W : ℤ) ↔ 0 ≤ r / (W : ℤ) + d := by
    rw [← hdiv, Int.le_ediv_iff_mul_le hW', zero_mul]
  have hhigh : r + d * (W : ℤ) < 548 * W ↔ r / (W : ℤ) + d < 548 := by
    rw [← hdiv, Int.ediv_lt_iff_lt_mul hW']
  have hcalc : r + d * (W : ℤ) = 2 * (cell W b j : ℤ) - (cell W a i : ℤ) - 1 := by
    simp only [r, d, cell, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring
  calc
    _ ↔ 0 ≤ r + d * (W : ℤ) ∧ r + d * (W : ℤ) < 548 * W := by
      rw [hcalc]
      zify
      omega
    _ ↔ _ := by
      rw [hlow, hhigh]
      change 0 ≤ r / (W : ℤ) + d ∧ r / (W : ℤ) + d < 548 ↔
        -(r / (W : ℤ)) ≤ d ∧ d < -(r / (W : ℤ)) + 548
      omega

private def fine (W : ℕ) : Finset (ℕ × ℕ) :=
  (((Icc 1 (548 * W) ×ˢ Icc 1 (548 * W)).filter fun p =>
    p.1 + 1 ≤ 2 * p.2 ∧ 2 * p.2 ≤ p.1 + 548 * W).filter fun p =>
    color ((p.1 - 1) / W) ≠ color ((p.2 - 1) / W))

private def cells (W : ℕ) : Finset (Σ _ : ℕ × ℕ, ℕ × ℕ) :=
  (range W ×ˢ range W).sigma (fun r => band (shift W r))

private theorem mem_fine {W x y : ℕ} :
    (x, y) ∈ fine W ↔ x ∈ Icc 1 (548 * W) ∧ y ∈ Icc 1 (548 * W) ∧
      (x + 1 ≤ 2 * y ∧ 2 * y ≤ x + 548 * W) ∧
        color ((x - 1) / W) ≠ color ((y - 1) / W) := by
  simp only [fine, mem_filter, mem_product, and_assoc]

private theorem mem_cells (W i j a b : ℕ) :
    (⟨(i, j), (a, b)⟩ : Σ _ : ℕ × ℕ, ℕ × ℕ) ∈ cells W ↔
      i < W ∧ j < W ∧ a < 548 ∧ b < 548 ∧ color a ≠ color b ∧
        shift W (i, j) ≤ 2 * (b : ℤ) - a ∧
        2 * (b : ℤ) - a < shift W (i, j) + 548 := by
  simp only [cells, mem_sigma, mem_product, mem_range, mem_band, and_assoc]

private def encode (W : ℕ) (p : Σ _ : ℕ × ℕ, ℕ × ℕ) : ℕ × ℕ :=
  (cell W p.2.1 p.1.1, cell W p.2.2 p.1.2)

private def decode (W : ℕ) (p : ℕ × ℕ) : Σ _ : ℕ × ℕ, ℕ × ℕ :=
  ⟨((p.1 - 1) % W, (p.2 - 1) % W), ((p.1 - 1) / W, (p.2 - 1) / W)⟩

set_option maxRecDepth 1500 in
private theorem cards_eq {W : ℕ} (hW : 0 < W) : (cells W).card = (fine W).card := by
  refine card_nbij' (encode W) (decode W) ?_ ?_ ?_ ?_
  · rintro ⟨⟨i, j⟩, a, b⟩ hp
    obtain ⟨hi, hj, ha, hb, hcolor, hbnds⟩ := (mem_cells W i j a b).mp hp
    have h := (cell_bounds hW a b i j).mpr hbnds
    have hx := cell_mem ha hi
    have hy := cell_mem hb hj
    refine mem_fine.mpr ⟨hx, hy, h, ?_⟩
    simpa only [cell_div hW hi, cell_div hW hj] using hcolor
  · rintro ⟨x, y⟩ hp
    obtain ⟨hx, hy, hxy, hcolor⟩ := mem_fine.mp hp
    have hx₁ := (mem_Icc.mp hx).1
    have hy₁ := (mem_Icc.mp hy).1
    have hxq : (x - 1) / W < 548 := (Nat.div_lt_iff_lt_mul hW).2 (by
      have := (mem_Icc.mp hx).2
      omega)
    have hyq : (y - 1) / W < 548 := (Nat.div_lt_iff_lt_mul hW).2 (by
      have := (mem_Icc.mp hy).2
      omega)
    have h := (cell_bounds hW ((x - 1) / W) ((y - 1) / W)
      ((x - 1) % W) ((y - 1) % W)).mp (by
        simpa only [cell_decode hx₁, cell_decode hy₁] using hxy)
    exact (mem_cells W ((x - 1) % W) ((y - 1) % W) ((x - 1) / W) ((y - 1) / W)).mpr
      ⟨Nat.mod_lt _ hW, Nat.mod_lt _ hW, hxq, hyq, hcolor, h⟩
  · rintro ⟨⟨i, j⟩, a, b⟩ hp
    obtain ⟨hi, hj, _⟩ := (mem_cells W i j a b).mp hp
    simp only [encode, decode, cell_div hW hi, cell_div hW hj, cell_mod hi, cell_mod hj]
  · rintro ⟨x, y⟩ hp
    obtain ⟨hx, hy, _, _⟩ := mem_fine.mp hp
    simp only [encode, decode, cell_decode (mem_Icc.mp hx).1, cell_decode (mem_Icc.mp hy).1]

private theorem fine_card {W : ℕ} (hW : 0 < W) : (fine W).card = 80556 * W ^ 2 := by
  rw [← cards_eq hW]
  calc
    _ = ∑ r ∈ range W ×ˢ range W, (band (shift W r)).card := card_sigma _ _
    _ = ∑ _r ∈ range W ×ˢ range W, 80556 := by
      apply sum_congr rfl
      rintro ⟨i, j⟩ hr
      obtain ⟨hi, hj⟩ := mem_product.mp hr
      exact band_card_of_cases (shift_cases hW (mem_range.mp hi) (mem_range.mp hj))
    _ = _ := by simp only [sum_const, card_product, card_range, Nat.nsmul_eq_mul]; ring

end OMA.Erdos1186ReferenceCount

theorem OMA.solution : OMA.R_Erdos1186_erdos_1186_variants_prs_conjecture_R1.H3 := by
  intro w hw
  have h := OMA.Erdos1186ReferenceCount.fine_card (W := 2 * w) (by omega)
  unfold OMA.Erdos1186ReferenceCount.fine at h
  rw [show 548 * (2 * w) = 1096 * w by ring,
    show 80556 * (2 * w) ^ 2 = 322224 * w ^ 2 by ring] at h
  exact h.le
