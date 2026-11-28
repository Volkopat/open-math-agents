import OMAReductions.R_RamseyNumbers_ramsey_number_four_five_R1_H1_R1_H2_R1
import Mathlib

/-!
Bit-pack the `8 × 16` crossing matrix into `Fin (2 ^ 128)` and separate the
four eight-vertex left blocks against the fixed 16-vertex right graph.
-/

namespace OMA.R_RamseyNumbers_ramsey_number_four_five_R1_H1_R1_H2_R1_H4_R1

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
  ∀ w : Fin (2 ^ 128),
    ∃ (c : Bool) (s : Finset (Fin 8)) (t : Finset (Fin 16)),
      s.card + t.card = (if c then 4 else 5) ∧
      (∀ i ∈ s, ∀ j ∈ s, i < j → (31956160 : ℕ).testBit (j.val * (j.val - 1) / 2 + i.val) = c) ∧
      (∀ i ∈ t, ∀ j ∈ t, i < j →
        (0xcb94e332f53ae143a3b6933356490b : ℕ).testBit (j.val * (j.val - 1) / 2 + i.val) = c) ∧
      ∀ i ∈ s, ∀ j ∈ t, w.val.testBit (16 * i.val + j.val) = c

def H2 : Prop :=
  ∀ w : Fin (2 ^ 128),
    ∃ (c : Bool) (s : Finset (Fin 8)) (t : Finset (Fin 16)),
      s.card + t.card = (if c then 4 else 5) ∧
      (∀ i ∈ s, ∀ j ∈ s, i < j → (31960512 : ℕ).testBit (j.val * (j.val - 1) / 2 + i.val) = c) ∧
      (∀ i ∈ t, ∀ j ∈ t, i < j →
        (0xcb94e332f53ae143a3b6933356490b : ℕ).testBit (j.val * (j.val - 1) / 2 + i.val) = c) ∧
      ∀ i ∈ s, ∀ j ∈ t, w.val.testBit (16 * i.val + j.val) = c

def H3 : Prop :=
  ∀ w : Fin (2 ^ 128),
    ∃ (c : Bool) (s : Finset (Fin 8)) (t : Finset (Fin 16)),
      s.card + t.card = (if c then 4 else 5) ∧
      (∀ i ∈ s, ∀ j ∈ s, i < j → (59186376 : ℕ).testBit (j.val * (j.val - 1) / 2 + i.val) = c) ∧
      (∀ i ∈ t, ∀ j ∈ t, i < j →
        (0xcb94e332f53ae143a3b6933356490b : ℕ).testBit (j.val * (j.val - 1) / 2 + i.val) = c) ∧
      ∀ i ∈ s, ∀ j ∈ t, w.val.testBit (16 * i.val + j.val) = c

def H4 : Prop :=
  ∀ w : Fin (2 ^ 128),
    ∃ (c : Bool) (s : Finset (Fin 8)) (t : Finset (Fin 16)),
      s.card + t.card = (if c then 4 else 5) ∧
      (∀ i ∈ s, ∀ j ∈ s, i < j → (59227328 : ℕ).testBit (j.val * (j.val - 1) / 2 + i.val) = c) ∧
      (∀ i ∈ t, ∀ j ∈ t, i < j →
        (0xcb94e332f53ae143a3b6933356490b : ℕ).testBit (j.val * (j.val - 1) / 2 + i.val) = c) ∧
      ∀ i ∈ s, ∀ j ∈ t, w.val.testBit (16 * i.val + j.val) = c

theorem main : H1 → H2 → H3 → H4 → OMA.R_RamseyNumbers_ramsey_number_four_five_R1_H1_R1_H2_R1.H4 := by
  intro h1 h2 h3 h4 p hp rows
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · obtain ⟨w, hw⟩ := pack_rows rows
    obtain ⟨c, s, t, hcard, hl, hr, hm⟩ := h1 w
    exact ⟨c, s, t, hcard, hl, hr, fun i hi j hj => (hw i j).symm.trans (hm i hi j hj)⟩
  · obtain ⟨w, hw⟩ := pack_rows rows
    obtain ⟨c, s, t, hcard, hl, hr, hm⟩ := h2 w
    exact ⟨c, s, t, hcard, hl, hr, fun i hi j hj => (hw i j).symm.trans (hm i hi j hj)⟩
  · obtain ⟨w, hw⟩ := pack_rows rows
    obtain ⟨c, s, t, hcard, hl, hr, hm⟩ := h3 w
    exact ⟨c, s, t, hcard, hl, hr, fun i hi j hj => (hw i j).symm.trans (hm i hi j hj)⟩
  · obtain ⟨w, hw⟩ := pack_rows rows
    obtain ⟨c, s, t, hcard, hl, hr, hm⟩ := h4 w
    exact ⟨c, s, t, hcard, hl, hr, fun i hi j hj => (hw i j).symm.trans (hm i hi j hj)⟩

end OMA.R_RamseyNumbers_ramsey_number_four_five_R1_H1_R1_H2_R1_H4_R1
