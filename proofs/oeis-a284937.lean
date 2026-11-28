import OMAStatements.S_oeis_a284937

-- Original proof by @jleguina.

namespace OMA.S_oeis_a284937

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

theorem iter_step : ∀ k : ℕ, iter k <+: iter (k + 1)
  | 0 => ⟨[1], by decide⟩
  | k + 1 => by simpa only [iter_succ] using (iter_step k).flatMap sigma

theorem iter_mono {j k : ℕ} (h : j ≤ k) : iter j <+: iter k := by
  induction k, h using Nat.le_induction with
  | base => exact List.prefix_rfl
  | succ k _ ih => exact ih.trans (iter_step k)

/-- Every sufficiently long iterate agrees with A284935 at the position read. -/
theorem agree (K i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ (iter K).length) :
    A284935 i = (iter K).getD (i - 1) 0 := by
  have hi := len_iter i
  rw [A284935, List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
  rcases le_total i K with h | h
  · exact (iter_mono h).getElem (by omega)
  · exact ((iter_mono h).getElem (by omega)).symm

/-- Each complete morphism block contributes equal numbers of zeros and ones. -/
theorem key (u : List ℕ) (L : ℕ) (hL : (u.flatMap sigma).getD L 0 = 1) :
    L + 1 ≤ 2 * ((u.flatMap sigma).take (L + 1)).count 1 ∧
      2 * ((u.flatMap sigma).take (L + 1)).count 1 ≤ L + 3 := by
  induction u generalizing L with
  | nil => simp at hL
  | cons x u ih =>
    rw [List.flatMap_cons] at hL ⊢
    by_cases h : L < (sigma x).length
    · rw [List.getD_append _ _ _ _ h] at hL
      rw [List.take_append_of_le_length (by omega)]
      cases x <;> simp [sigma] at h <;> interval_cases L <;> simp_all [sigma]
    · rw [List.getD_append_right _ _ _ _ (by omega)] at hL
      have hi := ih _ hL
      rw [List.take_append, List.take_of_length_le (by omega), List.count_append,
        show L + 1 - (sigma x).length = L - (sigma x).length + 1 by omega]
      have hb : (sigma x).length = 2 * (sigma x).count 1 := by cases x <;> simp [sigma]
      omega

theorem count_eq (K m : ℕ) (hm : m ≤ (iter K).length) :
    Nat.count (fun i => 1 ≤ i ∧ A284935 i = 1) (m + 1) = ((iter K).take m).count 1 := by
  induction m with
  | zero => simp [Nat.count_succ]
  | succ m ih =>
    have hlt : m < (iter K).length := by omega
    rw [Nat.count_succ, ih (by omega), List.take_add_one, List.getElem?_eq_getElem hlt,
      Option.toList_some, List.count_append, List.count_singleton]
    have hag := agree K (m + 1) (by omega) (by omega)
    rw [Nat.add_sub_cancel, List.getD_eq_getElem (iter K) 0 hlt] at hag
    simp [hag]

theorem iter_last (k : ℕ) : ∃ t, iter k = t ++ [k % 2] := by
  induction k with
  | zero => exact ⟨[], by simp [iter]⟩
  | succ k ih =>
    obtain ⟨t, ht⟩ := ih
    rw [iter_succ, ht, List.flatMap_append]
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · have h' : (k + 1) % 2 = 1 := by omega
      refine ⟨t.flatMap sigma ++ [0], ?_⟩
      rw [h, h']
      simp [sigma]
    · have h' : (k + 1) % 2 = 0 := by omega
      refine ⟨t.flatMap sigma ++ [1, 1, 0], ?_⟩
      rw [h, h']
      simp [sigma]

theorem infinite_ones : (Set.ofPred (fun i => 1 ≤ i ∧ A284935 i = 1)).Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨N, hN⟩
  obtain ⟨t, ht⟩ := iter_last (2 * N + 1)
  have h2 : (2 * N + 1) % 2 = 1 := by omega
  rw [h2] at ht
  have hlen := len_iter (2 * N + 1)
  rw [ht, List.length_append, List.length_singleton] at hlen
  have hmem : t.length + 1 ∈ Set.ofPred (fun i => 1 ≤ i ∧ A284935 i = 1) := by
    show 1 ≤ t.length + 1 ∧ A284935 (t.length + 1) = 1
    refine ⟨by omega, ?_⟩
    rw [agree (2 * N + 1) (t.length + 1) (by omega) (by rw [ht]; simp), ht,
      Nat.add_sub_cancel, List.getD_append_right _ _ _ _ le_rfl]
    simp
  have := hN hmem
  omega

theorem conjecture : ∀ n : ℕ, 1 ≤ n → (2 * n : ℤ) - a n ∈ ({0, 1, 2} : Set ℤ) := by
  intro n hn
  have hp : 1 ≤ a n ∧ A284935 (a n) = 1 := Nat.nth_mem_of_infinite infinite_ones (n - 1)
  have hc := Nat.count_nth_succ_of_infinite infinite_ones (n - 1)
  change Nat.count _ (a n + 1) = n - 1 + 1 at hc
  obtain ⟨m, hm⟩ : ∃ m, a n = m + 1 := ⟨a n - 1, by omega⟩
  rw [hm] at hp hc ⊢
  have hlen := len_iter (m + 1)
  have hw : (iter (m + 1)).getD m 0 = 1 := hp.2
  have hcnt := (count_eq (m + 1) (m + 1) (by omega)).symm.trans hc
  rw [iter_succ] at hw hcnt
  have hk := key (iter m) m hw
  rw [hcnt] at hk
  simp
  omega

/-- Control: a(n) at the position m + 1 of a 1 in the fourth iterate (54 letters). -/
theorem a_eq (k m : ℕ) (hm : m + 1 ≤ (iter 4).length)
    (h1 : ((iter 4).take m).count 1 + 1 = k) (h2 : (iter 4).getD m 0 = 1) : a k = m + 1 := by
  have hp : 1 ≤ m + 1 ∧ A284935 (m + 1) = 1 := by
    refine ⟨by omega, ?_⟩
    rw [agree 4 (m + 1) (by omega) hm, Nat.add_sub_cancel]
    exact h2
  have hc := count_eq 4 m (by omega)
  unfold a
  rw [← h1, Nat.add_sub_cancel, ← hc]
  exact Nat.nth_count hp

/-- Controls: a(1..8) = 2, 3, 4, 7, 8, 11, 12, 16, the entry's data. -/
example : a 1 = 2 ∧ a 2 = 3 ∧ a 3 = 4 ∧ a 4 = 7 ∧ a 5 = 8 ∧ a 6 = 11 ∧ a 7 = 12 ∧ a 8 = 16 :=
  ⟨a_eq 1 1 (by decide) (by decide) (by decide), a_eq 2 2 (by decide) (by decide) (by decide),
    a_eq 3 3 (by decide) (by decide) (by decide), a_eq 4 6 (by decide) (by decide) (by decide),
    a_eq 5 7 (by decide) (by decide) (by decide), a_eq 6 10 (by decide) (by decide) (by decide),
    a_eq 7 11 (by decide) (by decide) (by decide),
    a_eq 8 15 (by decide) (by decide) (by decide)⟩

end OMA.S_oeis_a284937

theorem OMA.solution : type_of% @OMA.S_oeis_a284937.main :=
  OMA.S_oeis_a284937.conjecture
