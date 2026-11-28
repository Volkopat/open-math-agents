import OMAStatements.S_oeis_a272010

section Proof_a272010
open OMA.S_oeis_a272010

def pOrig (x y : ℤ) : Bool := decide (x = 0 ∧ y = 0)
def pCross (x y : ℤ) : Bool := decide (|x| + |y| ≤ 1)
def pNotOrig (x y : ℤ) : Bool := decide (¬(x = 0 ∧ y = 0))
def pNotCross (x y : ℤ) : Bool := decide (¬(|x| + |y| ≤ 1))

lemma far_not_cross {u v : ℤ} (h : 3 ≤ |u| ∨ 3 ≤ |v|) : ¬(|u| + |v| ≤ 1) := by
  have hx : 0 ≤ |u| := abs_nonneg u
  have hy : 0 ≤ |v| := abs_nonneg v
  omega

lemma far_not_orig {u v : ℤ} (h : 3 ≤ |u| ∨ 3 ≤ |v|) : ¬(u = 0 ∧ v = 0) := by
  rintro ⟨rfl, rfl⟩; simp at h

lemma nbr_far {x y : ℤ} (h : ¬(|x| ≤ 3 ∧ |y| ≤ 3)) :
    (3 ≤ |x| ∨ 3 ≤ |y|) ∧
    (3 ≤ |x - 1| ∨ 3 ≤ |y|) ∧
    (3 ≤ |x + 1| ∨ 3 ≤ |y|) ∧
    (3 ≤ |x| ∨ 3 ≤ |y - 1|) ∧
    (3 ≤ |x| ∨ 3 ≤ |y + 1|) := by
  have h4 : 4 ≤ |x| ∨ 4 ≤ |y| := by omega
  rcases h4 with hx | hy
  · refine ⟨Or.inl (by omega),
      Or.inl (by cases abs_cases x <;> cases abs_cases (x - 1) <;> omega),
      Or.inl (by cases abs_cases x <;> cases abs_cases (x + 1) <;> omega),
      Or.inl (by omega), Or.inl (by omega)⟩
  · refine ⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by omega),
      Or.inr (by cases abs_cases y <;> cases abs_cases (y - 1) <;> omega),
      Or.inr (by cases abs_cases y <;> cases abs_cases (y + 1) <;> omega)⟩

set_option maxHeartbeats 2000000 in
lemma step1_orig (x y : ℤ) : step 1 pOrig x y = pNotCross x y := by
  unfold step pOrig pNotCross
  by_cases h : |x| ≤ 3 ∧ |y| ≤ 3
  · rcases abs_le.mp h.1 with ⟨_, _⟩; rcases abs_le.mp h.2 with ⟨_, _⟩
    interval_cases x <;> interval_cases y <;> decide +kernel
  · rcases nbr_far h with ⟨h0, h1, h2, h3, h4⟩
    simp only [far_not_orig h0, far_not_orig h1, far_not_orig h2,
      far_not_orig h3, far_not_orig h4, far_not_cross h0, decide_false, decide_true, not_false_eq_true]
    decide

set_option maxHeartbeats 2000000 in
lemma step1_notCross (x y : ℤ) : step 1 pNotCross x y = pOrig x y := by
  unfold step pNotCross pOrig
  by_cases h : |x| ≤ 3 ∧ |y| ≤ 3
  · rcases abs_le.mp h.1 with ⟨_, _⟩; rcases abs_le.mp h.2 with ⟨_, _⟩
    interval_cases x <;> interval_cases y <;> decide +kernel
  · rcases nbr_far h with ⟨h0, h1, h2, h3, h4⟩
    simp only [far_not_cross h0, far_not_cross h1, far_not_cross h2,
      far_not_cross h3, far_not_cross h4, far_not_orig h0, decide_false, decide_true, not_false_eq_true]
    decide

set_option maxHeartbeats 2000000 in
lemma step413_orig (x y : ℤ) : step 413 pOrig x y = pNotOrig x y := by
  unfold step pOrig pNotOrig
  by_cases h : |x| ≤ 3 ∧ |y| ≤ 3
  · rcases abs_le.mp h.1 with ⟨_, _⟩; rcases abs_le.mp h.2 with ⟨_, _⟩
    interval_cases x <;> interval_cases y <;> decide +kernel
  · rcases nbr_far h with ⟨h0, h1, h2, h3, h4⟩
    simp only [far_not_orig h0, far_not_orig h1, far_not_orig h2,
      far_not_orig h3, far_not_orig h4, decide_false, decide_true, not_false_eq_true]
    decide

set_option maxHeartbeats 2000000 in
lemma step413_notOrig (x y : ℤ) : step 413 pNotOrig x y = pCross x y := by
  unfold step pNotOrig pCross
  by_cases h : |x| ≤ 3 ∧ |y| ≤ 3
  · rcases abs_le.mp h.1 with ⟨_, _⟩; rcases abs_le.mp h.2 with ⟨_, _⟩
    interval_cases x <;> interval_cases y <;> decide +kernel
  · rcases nbr_far h with ⟨h0, h1, h2, h3, h4⟩
    simp only [far_not_orig h0, far_not_orig h1, far_not_orig h2,
      far_not_orig h3, far_not_orig h4, far_not_cross h0, decide_false, decide_true, not_false_eq_true]
    decide

set_option maxHeartbeats 2000000 in
lemma step413_cross (x y : ℤ) : step 413 pCross x y = pNotOrig x y := by
  unfold step pCross pNotOrig
  by_cases h : |x| ≤ 3 ∧ |y| ≤ 3
  · rcases abs_le.mp h.1 with ⟨_, _⟩; rcases abs_le.mp h.2 with ⟨_, _⟩
    interval_cases x <;> interval_cases y <;> decide +kernel
  · rcases nbr_far h with ⟨h0, h1, h2, h3, h4⟩
    simp only [far_not_cross h0, far_not_cross h1, far_not_cross h2,
      far_not_cross h3, far_not_cross h4, far_not_orig h0, decide_false, decide_true, not_false_eq_true]
    decide

lemma state1_even_odd (k : ℕ) :
    state 1 (2 * k) = pOrig ∧ state 1 (2 * k + 1) = pNotCross := by
  induction k with
  | zero =>
    refine ⟨rfl, ?_⟩
    funext x y; exact step1_orig x y
  | succ k ih =>
    have h1 : state 1 (2 * (k + 1)) = pOrig := by
      have heq : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
      rw [heq]; change step 1 (state 1 (2 * k + 1)) = pOrig
      rw [ih.2]; funext x y; exact step1_notCross x y
    have h2 : state 1 (2 * (k + 1) + 1) = pNotCross := by
      change step 1 (state 1 (2 * (k + 1))) = pNotCross
      rw [h1]; funext x y; exact step1_orig x y
    exact ⟨h1, h2⟩

lemma state413_odd_even (k : ℕ) :
    state 413 (2 * k + 1) = pNotOrig ∧ state 413 (2 * k + 2) = pCross := by
  induction k with
  | zero =>
    have h1 : state 413 1 = pNotOrig := by
      change step 413 pOrig = pNotOrig; funext x y; exact step413_orig x y
    refine ⟨h1, ?_⟩
    change step 413 (state 413 1) = pCross
    rw [h1]; funext x y; exact step413_notOrig x y
  | succ k ih =>
    have h1 : state 413 (2 * (k + 1) + 1) = pNotOrig := by
      have heq : 2 * (k + 1) + 1 = (2 * k + 2) + 1 := by omega
      rw [heq]; change step 413 (state 413 (2 * k + 2)) = pNotOrig
      rw [ih.2]; funext x y; exact step413_cross x y
    have h2 : state 413 (2 * (k + 1) + 2) = pCross := by
      have heq : 2 * (k + 1) + 2 = (2 * (k + 1) + 1) + 1 := by omega
      rw [heq]; change step 413 (state 413 (2 * (k + 1) + 1)) = pCross
      rw [h1]; funext x y; exact step413_notOrig x y
    exact ⟨h1, h2⟩

lemma state_diff_at_pos (t : ℕ) (ht : 1 ≤ t) (x y : ℤ) :
    (state 413 t x y = true ↔ state 1 t x y = true ∨ |x| + |y| = 1) ∧
    ¬(state 1 t x y = true ∧ |x| + |y| = 1) := by
  rcases Nat.even_or_odd' t with ⟨m, rfl | rfl⟩
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have h413 : state 413 (2 * (k + 1)) = pCross := by
      simpa [show 2 * (k + 1) = 2 * k + 2 by omega] using (state413_odd_even k).2
    have h1 : state 1 (2 * (k + 1)) = pOrig := (state1_even_odd (k + 1)).1
    rw [h413, h1]
    simp only [pCross, pOrig, decide_eq_true_eq]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro hle
      by_cases h0 : x = 0 ∧ y = 0
      · exact Or.inl h0
      · exact Or.inr (by cases abs_cases x <;> cases abs_cases y <;> omega)
    · rintro (⟨rfl, rfl⟩ | h1')
      · simp
      · omega
    · rintro ⟨⟨rfl, rfl⟩, h1'⟩; norm_num at h1'
  · rw [(state413_odd_even m).1, (state1_even_odd m).2]
    simp only [pNotOrig, pNotCross, decide_eq_true_eq]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro hne
      by_cases hgt : ¬(|x| + |y| ≤ 1)
      · exact Or.inl hgt
      · exact Or.inr (by cases abs_cases x <;> cases abs_cases y <;> omega)
    · rintro (hgt | h1')
      · rintro ⟨rfl, rfl⟩; simp at hgt
      · rintro ⟨rfl, rfl⟩; norm_num at h1'
    · rintro ⟨hgt, h1'⟩; omega

lemma unit_nbr_card (t : ℕ) (ht : 1 ≤ t) :
    ((Finset.range (2 * t + 1) ×ˢ Finset.range (2 * t + 1)).filter fun p : ℕ × ℕ =>
      |(p.1 : ℤ) - t| + |(p.2 : ℤ) - t| = 1).card = 4 := by
  set S : Finset (ℕ × ℕ) := {(t + 1, t), (t - 1, t), (t, t + 1), (t, t - 1)}
  have hS : ((Finset.range (2 * t + 1) ×ˢ Finset.range (2 * t + 1)).filter fun p : ℕ × ℕ =>
      |(p.1 : ℤ) - t| + |(p.2 : ℤ) - t| = 1) = S := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, S,
      Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hi, hj⟩, habs⟩
      cases abs_cases ((i : ℤ) - t) <;> cases abs_cases ((j : ℤ) - t) <;> omega
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · refine ⟨⟨by omega, by omega⟩, ?_⟩; push_cast; norm_num
      · refine ⟨⟨by omega, by omega⟩, ?_⟩
        rw [Nat.cast_sub ht]; norm_num
      · refine ⟨⟨by omega, by omega⟩, ?_⟩; push_cast; norm_num
      · refine ⟨⟨by omega, by omega⟩, ?_⟩
        rw [Nat.cast_sub ht]; norm_num
  rw [hS]
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
  · simp; omega
  · simp; omega
  · simp; omega

lemma onCount_diff (t : ℕ) (ht : 1 ≤ t) : onCount 413 t = onCount 1 t + 4 := by
  unfold onCount
  set B := Finset.range (2 * t + 1) ×ˢ Finset.range (2 * t + 1)
  let P1 : ℕ × ℕ → Prop := fun p => state 1 t ((p.1 : ℤ) - t) ((p.2 : ℤ) - t) = true
  let P2 : ℕ × ℕ → Prop := fun p => |(p.1 : ℤ) - t| + |(p.2 : ℤ) - t| = 1
  have heq : B.filter (fun p : ℕ × ℕ => state 413 t ((p.1 : ℤ) - t) ((p.2 : ℤ) - t) = true) =
      B.filter P1 ∪ B.filter P2 := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_union, P1, P2]
    have hd := (state_diff_at_pos t ht ((p.1 : ℤ) - t) ((p.2 : ℤ) - t)).1
    tauto
  have hdisj : Disjoint (B.filter P1) (B.filter P2) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_filter, P1, P2] at hp1 hp2
    exact (state_diff_at_pos t ht ((p.1 : ℤ) - t) ((p.2 : ℤ) - t)).2 ⟨hp1.2, hp2.2⟩
  rw [heq, Finset.card_union_of_disjoint hdisj, unit_nbr_card t ht]
  push_cast
  rfl

end Proof_a272010

theorem OMA.solution : type_of% @OMA.S_oeis_a272010.main := by
  intro n hn
  unfold OMA.S_oeis_a272010.a OMA.S_oeis_a272010.A269909
  rw [onCount_diff (n + 1) (by omega), onCount_diff n (by omega)]
  ring
