import OMAStatements.S_oeis_a285346

namespace OMA.S_oeis_a285346





theorem iter_succ (k : ℕ) : iter (k + 1) = (iter k).flatMap sigma := by
  unfold iter
  rw [Function.iterate_succ_apply']

theorem len_flatMap (u : List ℕ) : 2 * u.length ≤ (u.flatMap sigma).length := by
  induction u with
  | nil => simp
  | cons x u ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have : 2 ≤ (sigma x).length := by rcases x with _ | x <;> simp [sigma]
    omega

theorem len_iter (k : ℕ) : k + 1 ≤ (iter k).length := by
  induction k with
  | zero => simp [iter]
  | succ k ih =>
    rw [iter_succ]
    have := len_flatMap (iter k)
    omega

theorem iter_step (k : ℕ) : ∃ t, iter (k + 1) = iter k ++ t := by
  induction k with
  | zero => exact ⟨[1, 0, 0], by rw [iter_succ]; rfl⟩
  | succ k ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨t.flatMap sigma, ?_⟩
    rw [iter_succ (k + 1), ht, List.flatMap_append, ← iter_succ, ht]

theorem iter_mono {j k : ℕ} (h : j ≤ k) : ∃ t, iter k = iter j ++ t := by
  induction k, h using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ k _ ih =>
    obtain ⟨t, ht⟩ := ih
    obtain ⟨s, hs⟩ := iter_step k
    exact ⟨t ++ s, by rw [hs, ht, List.append_assoc]⟩

/-- Every iterate long enough to contain position i agrees with A285345 there. -/
theorem agree (K i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ (iter K).length) :
    A285345 i = (iter K).getD (i - 1) 0 := by
  unfold A285345
  rcases le_total i K with h | h
  · obtain ⟨t, ht⟩ := iter_mono h
    have := len_iter i
    rw [ht, List.getD_append _ _ _ _ (by omega)]
  · obtain ⟨t, ht⟩ := iter_mono h
    rw [ht, List.getD_append _ _ _ _ (by omega)]

/-- Both images have as many 0s as half their length, so the block of an image word ending at a
0 (position L, counted from 0) is an image word followed by nothing or by 110, and its length
L + 1 is 2c or 2c + 1 for c the number of its 0s. -/
theorem key (u : List ℕ) (L : ℕ) (hlen : L < (u.flatMap sigma).length)
    (hL : (u.flatMap sigma).getD L 0 = 0) :
    2 * ((u.flatMap sigma).take (L + 1)).count 0 ≤ L + 1 ∧
      L + 1 ≤ 2 * ((u.flatMap sigma).take (L + 1)).count 0 + 1 := by
  induction u generalizing L with
  | nil => simp at hlen
  | cons x u ih =>
    rw [List.flatMap_cons] at hL hlen ⊢
    rcases x with _ | x
    · simp only [sigma, List.cons_append, List.nil_append] at hL hlen ⊢
      rcases L with _ | _ | L
      · simp at hL
      · simp
      · rw [List.getD_cons_succ, List.getD_cons_succ] at hL
        have := ih L (by simp only [List.length_cons] at hlen; omega) hL
        simp only [List.take_succ_cons, List.count_cons] at this ⊢
        simp
        omega
    · simp only [sigma, List.cons_append, List.nil_append] at hL hlen ⊢
      rcases L with _ | _ | _ | _ | L
      · simp at hL
      · simp at hL
      · simp
      · simp
      · rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ,
          List.getD_cons_succ] at hL
        have := ih L (by simp only [List.length_cons] at hlen; omega) hL
        simp only [List.take_succ_cons, List.count_cons] at this ⊢
        simp
        omega

theorem count_eq (K m : ℕ) (hm : m ≤ (iter K).length) :
    Nat.count (fun i => 1 ≤ i ∧ A285345 i = 0) (m + 1) = ((iter K).take m).count 0 := by
  induction m with
  | zero => simp [Nat.count_succ]
  | succ m ih =>
    have hlt : m < (iter K).length := by omega
    rw [Nat.count_succ, ih (by omega), List.take_add_one, List.getElem?_eq_getElem hlt,
      Option.toList_some, List.count_append, List.count_singleton]
    have hag := agree K (m + 1) (by omega) (by omega)
    rw [Nat.add_sub_cancel, List.getD_eq_getElem (iter K) 0 hlt] at hag
    by_cases h : (iter K)[m] = 0
    · simp [h, hag]
    · simp [h, hag]

/-- Both images end with 0, so every iterate after the first ends with 0. -/
theorem iter_last (k : ℕ) : ∃ t, iter (k + 1) = t ++ [0] := by
  induction k with
  | zero => exact ⟨[1, 1, 0], by rw [iter_succ]; rfl⟩
  | succ k ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨t.flatMap sigma ++ [1], ?_⟩
    rw [iter_succ, ht, List.flatMap_append]
    simp [sigma]

theorem infinite_zeros : (Set.ofPred (fun i => 1 ≤ i ∧ A285345 i = 0)).Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨N, hN⟩
  obtain ⟨t, ht⟩ := iter_last N
  have hlen := len_iter (N + 1)
  rw [ht, List.length_append, List.length_singleton] at hlen
  have hmem : t.length + 1 ∈ Set.ofPred (fun i => 1 ≤ i ∧ A285345 i = 0) := by
    show 1 ≤ t.length + 1 ∧ A285345 (t.length + 1) = 0
    refine ⟨by omega, ?_⟩
    rw [agree (N + 1) (t.length + 1) (by omega) (by rw [ht]; simp), ht,
      Nat.add_sub_cancel, List.getD_append_right _ _ _ _ le_rfl]
    simp
  have := hN hmem
  omega

theorem conjecture : ∀ n : ℕ, 1 ≤ n → (2 * n : ℤ) + 1 - a n ∈ ({0, 1} : Set ℤ) := by
  intro n hn
  have hinf := infinite_zeros
  have hp : 1 ≤ a n ∧ A285345 (a n) = 0 := Nat.nth_mem_of_infinite hinf (n - 1)
  have hc : Nat.count (fun i => 1 ≤ i ∧ A285345 i = 0) (a n) = n - 1 :=
    Nat.count_nth_of_infinite hinf (n - 1)
  obtain ⟨m, hm⟩ : ∃ m, a n = m + 1 := ⟨a n - 1, by omega⟩
  rw [hm] at hp hc
  have hlen := len_iter (m + 1)
  have h1 := count_eq (m + 1) (m + 1) (by omega)
  rw [Nat.count_succ, hc, if_pos hp] at h1
  have hag := agree (m + 1) (m + 1) (by omega) (by omega)
  rw [Nat.add_sub_cancel] at hag
  have hw : (iter (m + 1)).getD m 0 = 0 := by rw [← hag]; exact hp.2
  rw [iter_succ] at hw h1 hlen
  have hk := key (iter m) m (by omega) hw
  rw [← h1] at hk
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [hm]
  push_cast
  omega

/-- Control: a(k) = m + 1 when position m + 1 holds a 0 of the third iterate (34 letters). -/
theorem a_eq (k m : ℕ) (hm : m + 1 ≤ (iter 3).length)
    (h1 : ((iter 3).take m).count 0 + 1 = k) (h2 : (iter 3).getD m 0 = 0) : a k = m + 1 := by
  have hp : 1 ≤ m + 1 ∧ A285345 (m + 1) = 0 := by
    refine ⟨by omega, ?_⟩
    rw [agree 3 (m + 1) (by omega) hm, Nat.add_sub_cancel]
    exact h2
  have hc := count_eq 3 m (by omega)
  unfold a
  rw [← h1, Nat.add_sub_cancel, ← hc]
  exact Nat.nth_count hp

/-- Controls: a(1..8) = 3, 4, 7, 8, 10, 12, 15, 16, the entry's data. -/
example : a 1 = 3 ∧ a 2 = 4 ∧ a 3 = 7 ∧ a 4 = 8 ∧ a 5 = 10 ∧ a 6 = 12 ∧ a 7 = 15 ∧ a 8 = 16 :=
  ⟨a_eq 1 2 (by decide) (by decide) (by decide), a_eq 2 3 (by decide) (by decide) (by decide),
    a_eq 3 6 (by decide) (by decide) (by decide), a_eq 4 7 (by decide) (by decide) (by decide),
    a_eq 5 9 (by decide) (by decide) (by decide), a_eq 6 11 (by decide) (by decide) (by decide),
    a_eq 7 14 (by decide) (by decide) (by decide),
    a_eq 8 15 (by decide) (by decide) (by decide)⟩

end OMA.S_oeis_a285346

theorem OMA.solution : type_of% @OMA.S_oeis_a285346.main :=
  OMA.S_oeis_a285346.conjecture
