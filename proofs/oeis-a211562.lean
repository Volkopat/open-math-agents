import OMAStatements.S_oeis_a211562

namespace OMA.P_oeis_a211562

open OMA.S_oeis_a211562 Finset

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
    a n = cnt (n + 2) (n + 2) n + cnt (n + 2) (n + 2) (n + 1) + cnt (n + 2) (n + 2) (n + 2) := by
  unfold a cnt
  rw [card_filter, card_filter, card_filter, card_filter, ← sum_add_distrib, ← sum_add_distrib]
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
  · have hP' : ¬ NewValuesInOrder (fun i => (x i : ℕ)) := hP
    simp [hP]

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

lemma poly (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) = (3 * n ^ 4 + 10 * n ^ 3 + 21 * n ^ 2 + 38 * n + 48) / 24 := by
  rw [a_eq n hn, cnt_eq _ _ le_rfl, cnt_eq _ _ le_rfl, cnt_eq _ _ le_rfl]
  push_cast
  rw [s2, show n + 2 = (n + 1) + 1 by ring, s1, Nat.stirlingSecond_self]
  push_cast
  ring

set_option maxRecDepth 4000 in
open PowerSeries in
theorem gf :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
      X * (5 - 11 * X + 16 * X ^ 2 - 9 * X ^ 3 + 2 * X ^ 4) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have hl : A * (1 - X) ^ 5 = A - C 5 * (A * X ^ 1) + C 10 * (A * X ^ 2) - C 10 * (A * X ^ 3) +
      C 5 * (A * X ^ 4) - A * X ^ 5 := by
    simp only [map_ofNat]; ring
  have hr : (X : ℚ⟦X⟧) * (5 - 11 * X + 16 * X ^ 2 - 9 * X ^ 3 + 2 * X ^ 4) =
      C 5 * X ^ 1 - C 11 * X ^ 2 + C 16 * X ^ 3 - C 9 * X ^ 4 + C 2 * X ^ 5 := by
    simp only [map_ofNat]; ring
  rw [hl, hr, hA]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  have p := fun k (hk : 1 ≤ k) => poly k hk
  have v : ∀ k, 1 ≤ k → (a k : ℚ) = (3 * k ^ 4 + 10 * k ^ 3 + 21 * k ^ 2 + 38 * k + 48) / 24 := p
  by_cases hn : n < 6
  · interval_cases n
    · simp
    · norm_num [v 1]
    · norm_num [v 1, v 2]
    · norm_num [v 1, v 2, v 3]
    · norm_num [v 1, v 2, v 3, v 4]
    · norm_num [v 1, v 2, v 3, v 4, v 5]
  · obtain ⟨n, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    simp only [show n + 6 - 1 = n + 5 by omega, show n + 6 - 2 = n + 4 by omega,
      show n + 6 - 3 = n + 3 by omega, show n + 6 - 4 = n + 2 by omega,
      show n + 6 - 5 = n + 1 by omega, show 1 ≤ n + 6 by omega, show 2 ≤ n + 6 by omega,
      show 3 ≤ n + 6 by omega, show 4 ≤ n + 6 by omega, show 5 ≤ n + 6 by omega, if_true,
      Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, one_ne_zero, and_false, if_false, coeff_C]
    rw [v (n + 6) (by omega), v (n + 5) (by omega), v (n + 4) (by omega), v (n + 3) (by omega),
      v (n + 2) (by omega), v (n + 1) (by omega)]
    push_cast
    ring

end OMA.P_oeis_a211562

theorem OMA.solution : type_of% @OMA.S_oeis_a211562.main := by
  refine ⟨OMA.P_oeis_a211562.gf, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  have h : (OMA.S_oeis_a211562.a (m + 6) : ℚ) = 5 * OMA.S_oeis_a211562.a (m + 5) -
      10 * OMA.S_oeis_a211562.a (m + 4) + 10 * OMA.S_oeis_a211562.a (m + 3) -
      5 * OMA.S_oeis_a211562.a (m + 2) + OMA.S_oeis_a211562.a (m + 1) := by
    simp only [OMA.P_oeis_a211562.poly _ (by omega : 1 ≤ m + 6),
      OMA.P_oeis_a211562.poly _ (by omega : 1 ≤ m + 5), OMA.P_oeis_a211562.poly _ (by omega : 1 ≤ m + 4),
      OMA.P_oeis_a211562.poly _ (by omega : 1 ≤ m + 3), OMA.P_oeis_a211562.poly _ (by omega : 1 ≤ m + 2),
      OMA.P_oeis_a211562.poly _ (by omega : 1 ≤ m + 1)]
    push_cast
    ring
  have e1 : m + 6 - 1 = m + 5 := by omega
  have e2 : m + 6 - 2 = m + 4 := by omega
  have e3 : m + 6 - 3 = m + 3 := by omega
  have e4 : m + 6 - 4 = m + 2 := by omega
  have e5 : m + 6 - 5 = m + 1 := by omega
  rw [e1, e2, e3, e4, e5]
  exact_mod_cast h
