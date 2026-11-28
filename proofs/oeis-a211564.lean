import OMAStatements.S_oeis_a211564

namespace OMA.P_oeis_a211564

open OMA.S_oeis_a211564 Finset

/-- The values of an array, as natural numbers. -/
def vals {L B : ℕ} (x : Fin L → Fin B) : Finset ℕ := univ.image (fun i => (x i : ℕ))

/-- The new-values-in-order property of an array with entries in `Fin B`. -/
abbrev P {L B : ℕ} (x : Fin L → Fin B) : Prop := NewValuesInOrder (fun i => (x i : ℕ))

lemma vals_eq {L B : ℕ} (x : Fin L → Fin B) (h : P x) : vals x = range (vals x).card := by
  have hdc : ∀ v ∈ vals x, ∀ w < v, w ∈ vals x := by
    intro v hv w hw
    obtain ⟨i, -, rfl⟩ := mem_image.1 hv
    obtain ⟨j, -, hj⟩ := h i w hw
    exact mem_image.2 ⟨j, mem_univ _, hj⟩
  have hsub : vals x ⊆ range (vals x).card := by
    intro v hv
    have h1 : range (v + 1) ⊆ vals x := by
      intro w hw
      rcases Nat.lt_succ_iff_lt_or_eq.1 (mem_range.1 hw) with h2 | h2
      · exact hdc v hv w h2
      · exact h2 ▸ hv
    have := card_le_card h1
    rw [card_range] at this
    rw [mem_range]
    omega
  exact eq_of_subset_of_card_le hsub (by rw [card_range])

lemma vals_card_le {L B : ℕ} (x : Fin L → Fin B) : (vals x).card ≤ L :=
  card_image_le.trans (by simp)

lemma vals_snoc {L B : ℕ} (x : Fin L → Fin B) (a : Fin B) :
    vals (Fin.snoc (α := fun _ => Fin B) x a) = insert (a : ℕ) (vals x) := by
  ext v
  simp [vals, Fin.exists_fin_succ', or_comm, eq_comm]

lemma P_snoc {L B : ℕ} (x : Fin L → Fin B) (a : Fin B) :
    P (Fin.snoc (α := fun _ => Fin B) x a) ↔ P x ∧ ∀ v < (a : ℕ), v ∈ vals x := by
  have hl : ∀ i : Fin L, ¬ Fin.last L < i.castSucc := fun i => not_lt.2 (Fin.le_last _)
  simp only [P, NewValuesInOrder, Fin.forall_fin_succ', Fin.exists_fin_succ', Fin.snoc_castSucc,
    Fin.snoc_last, Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_last, vals, mem_image, mem_univ,
    true_and, hl, lt_self_iff_false, false_and, or_false]

/-- The number of arrays of length `L` with entries in `Fin B` that introduce new values in
order and take exactly `k` distinct values. -/
def cnt (L B k : ℕ) : ℕ := (univ.filter (fun x : Fin L → Fin B => P x ∧ (vals x).card = k)).card

lemma inner {L B : ℕ} (hLB : L < B) (x : Fin L → Fin B) (k : ℕ) :
    (∑ a : Fin B, if P (Fin.snoc (α := fun _ => Fin B) x a) ∧
        (vals (Fin.snoc (α := fun _ => Fin B) x a)).card = k + 1 then 1 else 0) =
      (if P x ∧ (vals x).card = k + 1 then k + 1 else 0) +
        (if P x ∧ (vals x).card = k then 1 else 0) := by
  by_cases hP : P x
  · have hv := vals_eq x hP
    set d := (vals x).card with hd
    have hdB : d < B := lt_of_le_of_lt (vals_card_le x) hLB
    have key : ∀ a : Fin B, (P (Fin.snoc (α := fun _ => Fin B) x a) ∧
        (vals (Fin.snoc (α := fun _ => Fin B) x a)).card = k + 1) ↔
        ((a : ℕ) < d ∧ d = k + 1) ∨ ((a : ℕ) = d ∧ d = k) := by
      intro a
      rw [P_snoc, vals_snoc, hv]
      simp only [hP, true_and, mem_range]
      rcases lt_trichotomy (a : ℕ) d with ha | ha | ha
      · rw [insert_eq_of_mem (mem_range.2 ha), card_range]
        constructor
        · rintro ⟨-, h⟩; exact Or.inl ⟨ha, h⟩
        · rintro (⟨-, h⟩ | ⟨h, -⟩)
          · exact ⟨fun v hv' => lt_trans hv' ha, h⟩
          · omega
      · rw [ha, ← range_add_one, card_range]
        constructor
        · rintro ⟨-, h⟩; exact Or.inr ⟨rfl, by omega⟩
        · rintro (⟨h, -⟩ | ⟨-, h⟩)
          · omega
          · exact ⟨fun v hv' => hv', by omega⟩
      · constructor
        · rintro ⟨h, -⟩; exact absurd (h d ha) (lt_irrefl d)
        · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> omega
    simp only [key]
    rw [← card_filter]
    by_cases h1 : d = k + 1
    · have e : univ.filter (fun a : Fin B => ((a : ℕ) < d ∧ d = k + 1) ∨ ((a : ℕ) = d ∧ d = k)) =
          univ.filter (fun a : Fin B => (a : ℕ) < d) := by
        ext a; simp only [mem_filter, mem_univ, true_and]; omega
      rw [e, Fin.card_filter_val_lt, min_eq_right hdB.le]
      simp [hP, h1]
    · by_cases h2 : d = k
      · have e : univ.filter (fun a : Fin B => ((a : ℕ) < d ∧ d = k + 1) ∨ ((a : ℕ) = d ∧ d = k)) =
            {⟨d, hdB⟩} := by
          ext a; simp only [mem_filter, mem_univ, true_and, mem_singleton, Fin.ext_iff]; omega
        rw [e, card_singleton]
        simp [hP, h2]
      · have e : univ.filter (fun a : Fin B => ((a : ℕ) < d ∧ d = k + 1) ∨ ((a : ℕ) = d ∧ d = k)) =
            ∅ := by
          ext a; simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]; omega
        rw [e, card_empty]
        simp [hP, h1, h2]
  · simp [P_snoc, hP]

lemma cnt_succ {L B : ℕ} (hLB : L < B) (k : ℕ) :
    cnt (L + 1) B (k + 1) = (k + 1) * cnt L B (k + 1) + cnt L B k := by
  unfold cnt
  rw [card_filter, card_filter, card_filter, ← (Fin.snocEquiv (fun _ => Fin B)).sum_comp,
    Fintype.sum_prod_type, Finset.sum_comm]
  rw [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun x _ => ?_
  refine (inner hLB x k).trans ?_
  split_ifs <;> simp

lemma cnt_zero (B k : ℕ) : cnt 0 B k = if k = 0 then 1 else 0 := by
  unfold cnt
  by_cases hk : k = 0
  · subst hk
    simp [vals, P, NewValuesInOrder]
  · simp [vals, P, NewValuesInOrder, hk, Ne.symm hk]

lemma cnt_succ_zero (L B : ℕ) : cnt (L + 1) B 0 = 0 := by
  unfold cnt
  simp [vals, card_eq_zero, image_eq_empty, univ_eq_empty_iff]

lemma cnt_eq (B : ℕ) : ∀ L ≤ B, ∀ k, cnt L B k = Nat.stirlingSecond L k := by
  intro L
  induction L with
  | zero => intro _ k; rw [cnt_zero]; cases k <;> simp
  | succ L ih =>
    intro hL k
    cases k with
    | zero => rw [cnt_succ_zero, Nat.stirlingSecond_succ_zero]
    | succ k =>
      rw [cnt_succ (by omega), ih (by omega), ih (by omega), Nat.stirlingSecond_succ_succ]

lemma a_eq (n : ℕ) (hn : 1 ≤ n) :
    a n =
      cnt (n + 4) (n + 4) n + cnt (n + 4) (n + 4) (n + 1) + cnt (n + 4) (n + 4) (n + 2) + cnt (n + 4) (n + 4) (n + 3) + cnt (n + 4) (n + 4) (n + 4) := by
  unfold a cnt
  rw [card_filter, card_filter, card_filter, card_filter, card_filter, card_filter, ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun x _ => ?_
  have hle := vals_card_le x
  by_cases hP : P x
  · have hc : (∃ i, (x i : ℕ) = n - 1) ↔ n ≤ (vals x).card := by
      have h1 : (∃ i, (x i : ℕ) = n - 1) ↔ n - 1 ∈ vals x := by simp [vals]
      rw [h1, vals_eq x hP, mem_range, card_range]
      omega
    have hP' : NewValuesInOrder (fun i => (x i : ℕ)) := hP
    simp only [hP', true_and, hc]
    split_ifs <;> omega
  · simp [hP]

lemma s1 (m : ℕ) : (Nat.stirlingSecond (m + 1) m : ℚ) = m * (m + 1) / 2 := by
  rw [Nat.stirlingSecond_succ_self_left, Nat.cast_choose_two]
  push_cast
  ring

lemma s2 (m : ℕ) : (Nat.stirlingSecond (m + 2) m : ℚ) = m * (m + 1) * (m + 2) * (3 * m + 1) / 24 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show m + 1 + 2 = (m + 2) + 1 by ring, Nat.stirlingSecond_succ_succ]
    push_cast
    rw [ih, show m + 2 = (m + 1) + 1 by ring, s1]
    push_cast
    ring

lemma s3 (m : ℕ) :
    (Nat.stirlingSecond (m + 3) m : ℚ) = m ^ 2 * (m + 1) ^ 2 * (m + 2) * (m + 3) / 48 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show m + 1 + 3 = (m + 3) + 1 by ring, Nat.stirlingSecond_succ_succ]
    push_cast
    rw [ih, show m + 3 = (m + 1) + 2 by ring, s2]
    push_cast
    ring

lemma s4 (m : ℕ) :
    (Nat.stirlingSecond (m + 4) m : ℚ) =
      m * (m + 1) * (m + 2) * (m + 3) * (m + 4) * (15 * m ^ 3 + 30 * m ^ 2 + 5 * m - 2) / 5760 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show m + 1 + 4 = (m + 4) + 1 by ring, Nat.stirlingSecond_succ_succ]
    push_cast
    rw [ih, show m + 4 = (m + 1) + 3 by ring, s3]
    push_cast
    ring

lemma poly (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) = (15 * n ^ 8 + 180 * n ^ 7 + 950 * n ^ 6 + 3408 * n ^ 5 + 10775 * n ^ 4 + 30060 * n ^ 3 + 66020 * n ^ 2 + 101712 * n + 86400) / 5760 := by
  rw [a_eq n hn, cnt_eq _ _ le_rfl, cnt_eq _ _ le_rfl, cnt_eq _ _ le_rfl, cnt_eq _ _ le_rfl, cnt_eq _ _ le_rfl]
  have h1 := s3 (n + 1)
  rw [show n + 1 + 3 = n + 4 by ring] at h1
  have h2 := s2 (n + 2)
  rw [show n + 2 + 2 = n + 4 by ring] at h2
  have h3 := s1 (n + 3)
  rw [show n + 3 + 1 = n + 4 by ring] at h3
  push_cast
  rw [s4, h1, h2, h3, Nat.stirlingSecond_self]
  push_cast
  ring

set_option maxRecDepth 8000 in
open PowerSeries in
theorem gf :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
      X * (52 - 266 * X + 867 * X ^ 2 - 1367 * X ^ 3 + 1534 * X ^ 4 - 1097 * X ^ 5 + 497 * X ^ 6 - 130 * X ^ 7 + 15 * X ^ 8) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have hl : A * (1 - X) ^ 9 =
      A - C 9 * (A * X ^ 1) + C 36 * (A * X ^ 2) - C 84 * (A * X ^ 3) + C 126 * (A * X ^ 4) - C 126 * (A * X ^ 5) + C 84 * (A * X ^ 6) - C 36 * (A * X ^ 7) + C 9 * (A * X ^ 8) - (A * X ^ 9) := by
    simp only [map_ofNat]; ring
  have hr : (X : ℚ⟦X⟧) * (52 - 266 * X + 867 * X ^ 2 - 1367 * X ^ 3 + 1534 * X ^ 4 - 1097 * X ^ 5 + 497 * X ^ 6 - 130 * X ^ 7 + 15 * X ^ 8) =
      C 52 * X ^ 1 - C 266 * X ^ 2 + C 867 * X ^ 3 - C 1367 * X ^ 4 + C 1534 * X ^ 5 - C 1097 * X ^ 6 + C 497 * X ^ 7 - C 130 * X ^ 8 + C 15 * X ^ 9 := by
    simp only [map_ofNat]; ring
  have hq : A = PowerSeries.mk (fun k => if k = 0 then (0 : ℚ) else
      (15 * k ^ 8 + 180 * k ^ 7 + 950 * k ^ 6 + 3408 * k ^ 5 + 10775 * k ^ 4 + 30060 * k ^ 3 + 66020 * k ^ 2 + 101712 * k + 86400) / 5760) := by
    rw [hA]; congr 1; funext k; split_ifs with h
    · rfl
    · exact poly k (by omega)
  rw [hl, hr, hq]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hn : n < 10
  · interval_cases n <;> norm_num
  · obtain ⟨n, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
    simp only [show n + 10 - 1 = n + 9 by omega, show n + 10 - 2 = n + 8 by omega, show n + 10 - 3 = n + 7 by omega, show n + 10 - 4 = n + 6 by omega, show n + 10 - 5 = n + 5 by omega, show n + 10 - 6 = n + 4 by omega, show n + 10 - 7 = n + 3 by omega, show n + 10 - 8 = n + 2 by omega, show n + 10 - 9 = n + 1 by omega, show 1 ≤ n + 10 by omega, show 2 ≤ n + 10 by omega, show 3 ≤ n + 10 by omega, show 4 ≤ n + 10 by omega, show 5 ≤ n + 10 by omega, show 6 ≤ n + 10 by omega, show 7 ≤ n + 10 by omega, show 8 ≤ n + 10 by omega, show 9 ≤ n + 10 by omega, if_true,
      Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, one_ne_zero, and_false, if_false, coeff_C]
    push_cast
    ring

end OMA.P_oeis_a211564

theorem OMA.solution : type_of% @OMA.S_oeis_a211564.main := by
  refine ⟨OMA.P_oeis_a211564.gf, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
  have h : (OMA.S_oeis_a211564.a (m + 10) : ℚ) =
      9 * (OMA.S_oeis_a211564.a (m + 9) : ℚ) - 36 * (OMA.S_oeis_a211564.a (m + 8) : ℚ) + 84 * (OMA.S_oeis_a211564.a (m + 7) : ℚ) - 126 * (OMA.S_oeis_a211564.a (m + 6) : ℚ) + 126 * (OMA.S_oeis_a211564.a (m + 5) : ℚ) - 84 * (OMA.S_oeis_a211564.a (m + 4) : ℚ) + 36 * (OMA.S_oeis_a211564.a (m + 3) : ℚ) - 9 * (OMA.S_oeis_a211564.a (m + 2) : ℚ) + (OMA.S_oeis_a211564.a (m + 1) : ℚ) := by
    rw [OMA.P_oeis_a211564.poly (m + 10) (by omega), OMA.P_oeis_a211564.poly (m + 9) (by omega), OMA.P_oeis_a211564.poly (m + 8) (by omega), OMA.P_oeis_a211564.poly (m + 7) (by omega), OMA.P_oeis_a211564.poly (m + 6) (by omega), OMA.P_oeis_a211564.poly (m + 5) (by omega), OMA.P_oeis_a211564.poly (m + 4) (by omega), OMA.P_oeis_a211564.poly (m + 3) (by omega), OMA.P_oeis_a211564.poly (m + 2) (by omega), OMA.P_oeis_a211564.poly (m + 1) (by omega)]
    push_cast
    ring
  simp only [show m + 10 - 1 = m + 9 by omega, show m + 10 - 2 = m + 8 by omega, show m + 10 - 3 = m + 7 by omega, show m + 10 - 4 = m + 6 by omega, show m + 10 - 5 = m + 5 by omega, show m + 10 - 6 = m + 4 by omega, show m + 10 - 7 = m + 3 by omega, show m + 10 - 8 = m + 2 by omega, show m + 10 - 9 = m + 1 by omega]
  exact_mod_cast h
