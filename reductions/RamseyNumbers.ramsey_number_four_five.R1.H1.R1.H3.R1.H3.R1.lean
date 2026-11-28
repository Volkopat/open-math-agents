import OMAReductions.R_RamseyNumbers_ramsey_number_four_five_R1_H1_R1_H3_R1
import Mathlib

/-!
Bit-pack the `7 × 16` crossing matrix into `Fin (2 ^ 112)` and partition the
sixteen seven-vertex left blocks into four balanced groups of four.
-/

namespace OMA.R_RamseyNumbers_ramsey_number_four_five_R1_H1_R1_H3_R1_H3_R1

private theorem exists_mask_of_bool : ∀ (k : ℕ) (f : ℕ → Bool),
    ∃ w < 2 ^ k, ∀ j < k, w.testBit j = f j
  | 0, _ => ⟨0, by simp, fun _ hj => by omega⟩
  | k + 1, f => by
    obtain ⟨w, hw, hbit⟩ := exists_mask_of_bool k f
    refine ⟨w ||| (if f k then 2 ^ k else 0), ?_, ?_⟩
    · have h2 : 2 ^ k < 2 ^ (k + 1) := by rw [pow_succ]; have := Nat.two_pow_pos k; omega
      apply Nat.or_lt_two_pow (hw.trans h2)
      split
      · exact h2
      · exact Nat.two_pow_pos _
    · intro j hj
      rw [Nat.testBit_or]
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | rfl
      · rw [hbit j hlt]
        split
        · simp [Nat.testBit_two_pow_of_ne (Nat.ne_of_gt hlt)]
        · simp
      · rw [Nat.testBit_lt_two_pow hw, Bool.false_or]
        split <;> simp_all [Nat.testBit_two_pow_self]

private theorem pack_rows {n : ℕ} (rows : Fin n → Fin 16 → Bool) :
    ∃ w : Fin (2 ^ (16 * n)),
      ∀ (i : Fin n) (j : Fin 16), w.val.testBit (16 * i.val + j.val) = rows i j := by
  let f : ℕ → Bool := fun q =>
    if h : q / 16 < n then rows ⟨q / 16, h⟩ ⟨q % 16, Nat.mod_lt _ (by decide)⟩ else false
  obtain ⟨w, hw, hbit⟩ := exists_mask_of_bool (16 * n) f
  refine ⟨⟨w, hw⟩, fun i j => ?_⟩
  have hlt : 16 * i.val + j.val < 16 * n := by omega
  rw [hbit _ hlt]
  dsimp only [f]
  have hdiv : (16 * i.val + j.val) / 16 = i.val := by omega
  have hmod : (16 * i.val + j.val) % 16 = j.val := by omega
  simp [hdiv, hmod]

def H1 : Prop :=
  ∀ g ∈ ([236608, 332992, 368064, 396480] : List ℕ), ∀ w : Fin (2 ^ 112),
    ∃ (c : Bool) (s : Finset (Fin 7)) (t : Finset (Fin 16)),
      s.card + t.card = (if c then 4 else 5) ∧
      (∀ i ∈ s, ∀ j ∈ s, i < j → g.testBit (j.val * (j.val - 1) / 2 + i.val) = c) ∧
      (∀ i ∈ t, ∀ j ∈ t, i < j →
        (0xacb96354eb266b51b2b6553699403b : ℕ).testBit (j.val * (j.val - 1) / 2 + i.val) = c) ∧
      ∀ i ∈ s, ∀ j ∈ t, w.val.testBit (16 * i.val + j.val) = c

def H2 : Prop :=
  ∀ g ∈ ([433344, 437696, 439488, 466056] : List ℕ), ∀ w : Fin (2 ^ 112),
    ∃ (c : Bool) (s : Finset (Fin 7)) (t : Finset (Fin 16)),
      s.card + t.card = (if c then 4 else 5) ∧
      (∀ i ∈ s, ∀ j ∈ s, i < j → g.testBit (j.val * (j.val - 1) / 2 + i.val) = c) ∧
      (∀ i ∈ t, ∀ j ∈ t, i < j →
        (0xacb96354eb266b51b2b6553699403b : ℕ).testBit (j.val * (j.val - 1) / 2 + i.val) = c) ∧
      ∀ i ∈ s, ∀ j ∈ t, w.val.testBit (16 * i.val + j.val) = c

def H3 : Prop :=
  ∀ g ∈ ([472256, 494784, 496832, 498752] : List ℕ), ∀ w : Fin (2 ^ 112),
    ∃ (c : Bool) (s : Finset (Fin 7)) (t : Finset (Fin 16)),
      s.card + t.card = (if c then 4 else 5) ∧
      (∀ i ∈ s, ∀ j ∈ s, i < j → g.testBit (j.val * (j.val - 1) / 2 + i.val) = c) ∧
      (∀ i ∈ t, ∀ j ∈ t, i < j →
        (0xacb96354eb266b51b2b6553699403b : ℕ).testBit (j.val * (j.val - 1) / 2 + i.val) = c) ∧
      ∀ i ∈ s, ∀ j ∈ t, w.val.testBit (16 * i.val + j.val) = c

def H4 : Prop :=
  ∀ g ∈ ([506944, 507840, 922816, 924864] : List ℕ), ∀ w : Fin (2 ^ 112),
    ∃ (c : Bool) (s : Finset (Fin 7)) (t : Finset (Fin 16)),
      s.card + t.card = (if c then 4 else 5) ∧
      (∀ i ∈ s, ∀ j ∈ s, i < j → g.testBit (j.val * (j.val - 1) / 2 + i.val) = c) ∧
      (∀ i ∈ t, ∀ j ∈ t, i < j →
        (0xacb96354eb266b51b2b6553699403b : ℕ).testBit (j.val * (j.val - 1) / 2 + i.val) = c) ∧
      ∀ i ∈ s, ∀ j ∈ t, w.val.testBit (16 * i.val + j.val) = c

theorem main : H1 → H2 → H3 → H4 → OMA.R_RamseyNumbers_ramsey_number_four_five_R1_H1_R1_H3_R1.H3 := by
  intro h1 h2 h3 h4 p hp rows
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨w, hw⟩ := pack_rows rows
    obtain ⟨c, s, t, hcard, hl, hr, hm⟩ := h1 236608 (by decide) w
    exact ⟨c, s, t, hcard, hl, hr, fun i hi j hj => (hw i j).symm.trans (hm i hi j hj)⟩
  · obtain ⟨w, hw⟩ := pack_rows rows
    obtain ⟨c, s, t, hcard, hl, hr, hm⟩ := h1 332992 (by decide) w
    exact ⟨c, s, t, hcard, hl, hr, fun i hi j hj => (hw i j).symm.trans (hm i hi j hj)⟩
  · obtain ⟨w, hw⟩ := pack_rows rows
    obtain ⟨c, s, t, hcard, hl, hr, hm⟩ := h1 368064 (by decide) w
    exact ⟨c, s, t, hcard, hl, hr, fun i hi j hj => (hw i j).symm.trans (hm i hi j hj)⟩
  · obtain ⟨w, hw⟩ := pack_rows rows
    obtain ⟨c, s, t, hcard, hl, hr, hm⟩ := h1 396480 (by decide) w
    exact ⟨c, s, t, hcard, hl, hr, fun i hi j hj => (hw i j).symm.trans (hm i hi j hj)⟩
  · obtain ⟨w, hw⟩ := pack_rows rows
    obtain ⟨c, s, t, hcard, hl, hr, hm⟩ := h2 433344 (by decide) w
    exact ⟨c, s, t, hcard, hl, hr, fun i hi j hj => (hw i j).symm.trans (hm i hi j hj)⟩
  · obtain ⟨w, hw⟩ := pack_rows rows
    obtain ⟨c, s, t, hcard, hl, hr, hm⟩ := h2 437696 (by decide) w
    exact ⟨c, s, t, hcard, hl, hr, fun i hi j hj => (hw i j).symm.trans (hm i hi j hj)⟩
  · obtain ⟨w, hw⟩ := pack_rows rows
    obtain ⟨c, s, t, hcard, hl, hr, hm⟩ := h2 439488 (by decide) w
    exact ⟨c, s, t, hcard, hl, hr, fun i hi j hj => (hw i j).symm.trans (hm i hi j hj)⟩
  · obtain ⟨w, hw⟩ := pack_rows rows
    obtain ⟨c, s, t, hcard, hl, hr, hm⟩ := h2 466056 (by decide) w
    exact ⟨c, s, t, hcard, hl, hr, fun i hi j hj => (hw i j).symm.trans (hm i hi j hj)⟩
  · obtain ⟨w, hw⟩ := pack_rows rows
    obtain ⟨c, s, t, hcard, hl, hr, hm⟩ := h3 472256 (by decide) w
    exact ⟨c, s, t, hcard, hl, hr, fun i hi j hj => (hw i j).symm.trans (hm i hi j hj)⟩
  · obtain ⟨w, hw⟩ := pack_rows rows
    obtain ⟨c, s, t, hcard, hl, hr, hm⟩ := h3 494784 (by decide) w
    exact ⟨c, s, t, hcard, hl, hr, fun i hi j hj => (hw i j).symm.trans (hm i hi j hj)⟩
  · obtain ⟨w, hw⟩ := pack_rows rows
    obtain ⟨c, s, t, hcard, hl, hr, hm⟩ := h3 496832 (by decide) w
    exact ⟨c, s, t, hcard, hl, hr, fun i hi j hj => (hw i j).symm.trans (hm i hi j hj)⟩
  · obtain ⟨w, hw⟩ := pack_rows rows
    obtain ⟨c, s, t, hcard, hl, hr, hm⟩ := h3 498752 (by decide) w
    exact ⟨c, s, t, hcard, hl, hr, fun i hi j hj => (hw i j).symm.trans (hm i hi j hj)⟩
  · obtain ⟨w, hw⟩ := pack_rows rows
    obtain ⟨c, s, t, hcard, hl, hr, hm⟩ := h4 506944 (by decide) w
    exact ⟨c, s, t, hcard, hl, hr, fun i hi j hj => (hw i j).symm.trans (hm i hi j hj)⟩
  · obtain ⟨w, hw⟩ := pack_rows rows
    obtain ⟨c, s, t, hcard, hl, hr, hm⟩ := h4 507840 (by decide) w
    exact ⟨c, s, t, hcard, hl, hr, fun i hi j hj => (hw i j).symm.trans (hm i hi j hj)⟩
  · obtain ⟨w, hw⟩ := pack_rows rows
    obtain ⟨c, s, t, hcard, hl, hr, hm⟩ := h4 922816 (by decide) w
    exact ⟨c, s, t, hcard, hl, hr, fun i hi j hj => (hw i j).symm.trans (hm i hi j hj)⟩
  · obtain ⟨w, hw⟩ := pack_rows rows
    obtain ⟨c, s, t, hcard, hl, hr, hm⟩ := h4 924864 (by decide) w
    exact ⟨c, s, t, hcard, hl, hr, fun i hi j hj => (hw i j).symm.trans (hm i hi j hj)⟩

end OMA.R_RamseyNumbers_ramsey_number_four_five_R1_H1_R1_H3_R1_H3_R1
