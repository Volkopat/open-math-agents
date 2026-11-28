import OMAStatements.S_oeis_a284941

namespace OMA.S_oeis_a284941





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
  | zero => exact ⟨[1], by simp [iter, sigma]⟩
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

/-- Every iterate long enough to contain position i agrees with A284939 there. -/
theorem agree (K i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ (iter K).length) :
    A284939 i = (iter K).getD (i - 1) 0 := by
  unfold A284939
  rcases le_total i K with h | h
  · obtain ⟨t, ht⟩ := iter_mono h
    have := len_iter i
    rw [ht, List.getD_append _ _ _ _ (by omega)]
  · obtain ⟨t, ht⟩ := iter_mono h
    rw [ht, List.getD_append _ _ _ _ (by omega)]

theorem count_eq (K m : ℕ) (hm : m ≤ (iter K).length) :
    Nat.count (fun i => 1 ≤ i ∧ A284939 i = 1) (m + 1) = ((iter K).take m).count 1 := by
  induction m with
  | zero => simp [Nat.count_succ]
  | succ m ih =>
    have hlt : m < (iter K).length := by omega
    rw [Nat.count_succ, ih (by omega), List.take_add_one, List.getElem?_eq_getElem hlt,
      Option.toList_some, List.count_append, List.count_singleton]
    have hag := agree K (m + 1) (by omega) (by omega)
    rw [Nat.add_sub_cancel, List.getD_eq_getElem (iter K) 0 hlt] at hag
    by_cases h : (iter K)[m] = 1
    · simp [h, hag]
    · simp [h, hag]

theorem iter_last (k : ℕ) : ∃ t, iter (k + 1) = t ++ [1] := by
  induction k with
  | zero => exact ⟨[0], by simp [iter, sigma]⟩
  | succ k ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨t.flatMap sigma ++ [1, 1, 0], ?_⟩
    rw [iter_succ, ht, List.flatMap_append]
    simp [sigma]

theorem infinite_ones : (Set.ofPred (fun i => 1 ≤ i ∧ A284939 i = 1)).Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨N, hN⟩
  obtain ⟨t, ht⟩ := iter_last N
  have hlen := len_iter (N + 1)
  rw [ht, List.length_append, List.length_singleton] at hlen
  have hmem : t.length + 1 ∈ Set.ofPred (fun i => 1 ≤ i ∧ A284939 i = 1) := by
    show 1 ≤ t.length + 1 ∧ A284939 (t.length + 1) = 1
    refine ⟨by omega, ?_⟩
    rw [agree (N + 1) (t.length + 1) (by omega) (by rw [ht]; simp), ht,
      Nat.add_sub_cancel, List.getD_append_right _ _ _ _ le_rfl]
    simp
  have := hN hmem
  omega

/-- E(u) = sqrt 2 * (number of 1s in u) - (length of u). -/
noncomputable def E (u : List ℕ) : ℝ := Real.sqrt 2 * (u.count 1 : ℝ) - u.length

theorem E_append (u v : List ℕ) : E (u ++ v) = E u + E v := by
  unfold E
  rw [List.count_append, List.length_append]
  push_cast
  ring

theorem sq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)

theorem s_lo : (4 : ℝ) / 3 < Real.sqrt 2 := by
  rw [Real.lt_sqrt (by norm_num)]
  norm_num

theorem s_hi : Real.sqrt 2 < 2 := by
  rw [Real.sqrt_lt' (by norm_num)]
  norm_num

theorem E_nil : E [] = 0 := by simp [E]
theorem E_0 : E [0] = -1 := by simp [E]
theorem E_1 : E [1] = Real.sqrt 2 - 1 := by simp [E]
theorem E_11 : E [1, 1] = 2 * Real.sqrt 2 - 2 := by simp [E]; ring
theorem E_110 : E [1, 1, 0] = 2 * Real.sqrt 2 - 3 := by simp [E]; ring
theorem E_01 : E [0, 1] = Real.sqrt 2 - 2 := by simp [E]
theorem E_1101 : E [1, 1, 0, 1] = 3 * Real.sqrt 2 - 4 := by simp [E]; ring

/-- The morphism multiplies E by the second eigenvalue 2 - sqrt 2. -/
theorem E_flatMap (u : List ℕ) (hu : ∀ y ∈ u, y ≤ 1) :
    E (u.flatMap sigma) = (2 - Real.sqrt 2) * E u := by
  induction u with
  | nil => simp [E]
  | cons x u ih =>
    rw [List.flatMap_cons, E_append, ih (fun y hy => hu y (by simp [hy]))]
    have hx : x ≤ 1 := hu x (by simp)
    have h2 : E (x :: u) = E [x] + E u := by rw [← E_append]; rfl
    rw [h2]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hx with rfl | rfl
    · rw [show sigma 0 = [0, 1] from rfl, E_01, E_0]
      ring
    · rw [show sigma 1 = [1, 1, 0, 1] from rfl, E_1101, E_1]
      linear_combination sq2

/-- The bound on E of the letters before a position, by the letter at that position. -/
def Bd (e : ℝ) (x : ℕ) : Prop := if x = 0 then 0 ≤ e ∧ e ≤ Real.sqrt 2 else -1 ≤ e ∧ e ≤ 1

theorem Bd_zero (e : ℝ) : Bd e 0 ↔ 0 ≤ e ∧ e ≤ Real.sqrt 2 := by simp [Bd]
theorem Bd_one (e : ℝ) : Bd e 1 ↔ -1 ≤ e ∧ e ≤ 1 := by simp [Bd]

theorem letters_flatMap (u : List ℕ) : ∀ y ∈ u.flatMap sigma, y ≤ 1 := by
  intro y hy
  rw [List.mem_flatMap] at hy
  obtain ⟨x, _, hx⟩ := hy
  rcases x with _ | x <;> simp [sigma] at hx <;> omega

theorem letters_iter (k : ℕ) : ∀ y ∈ iter k, y ≤ 1 := by
  cases k with
  | zero => simp [iter]
  | succ k => rw [iter_succ]; exact letters_flatMap _

/-- If the bound holds before every letter of u (after the word pre), it holds before every
letter of the image of u (after the image of pre). -/
theorem step (u : List ℕ) : ∀ pre : List ℕ, (∀ y ∈ pre, y ≤ 1) → (∀ y ∈ u, y ≤ 1) →
    (∀ j, j < u.length → Bd (E (pre ++ u.take j)) (u.getD j 0)) →
    ∀ L, L < (u.flatMap sigma).length →
      Bd (E (pre.flatMap sigma ++ (u.flatMap sigma).take L)) ((u.flatMap sigma).getD L 0) := by
  induction u with
  | nil => intro pre _ _ _ L hL; simp at hL
  | cons x u ih =>
    intro pre hpre hu hb L hL
    have hx : x ≤ 1 := hu x (by simp)
    have hu' : ∀ y ∈ u, y ≤ 1 := fun y hy => hu y (by simp [hy])
    have hb0 := hb 0 (by simp)
    rw [List.take_zero, List.append_nil, List.getD_cons_zero] at hb0
    have hE : ∀ v, E (pre.flatMap sigma ++ v) = (2 - Real.sqrt 2) * E pre + E v := by
      intro v
      rw [E_append, E_flatMap pre hpre]
    have hlo := s_lo
    have hhi := s_hi
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hx with rfl | rfl
    · rw [Bd_zero] at hb0
      obtain ⟨h1, h2⟩ := hb0
      have hm1 := mul_nonneg (sub_nonneg.2 hhi.le) h1
      have hm2 := mul_nonneg (sub_nonneg.2 hhi.le) (sub_nonneg.2 h2)
      rw [List.flatMap_cons, show sigma 0 = [0, 1] from rfl, List.cons_append,
        List.cons_append, List.nil_append] at hL ⊢
      rcases L with _ | _ | L
      · rw [List.take_zero, List.getD_cons_zero, hE, E_nil, Bd_zero]
        constructor <;> nlinarith [sq2]
      · rw [List.take_succ_cons, List.take_zero, List.getD_cons_succ, List.getD_cons_zero, hE,
          E_0, Bd_one]
        constructor <;> nlinarith [sq2]
      · have hb' : ∀ j, j < u.length → Bd (E ((pre ++ [0]) ++ u.take j)) (u.getD j 0) := by
          intro j hj
          have := hb (j + 1) (by simp; omega)
          rw [List.take_succ_cons, List.getD_cons_succ] at this
          rw [List.append_assoc, List.singleton_append]
          exact this
        have hpre' : ∀ y ∈ pre ++ [0], y ≤ 1 := by
          intro y hy
          rw [List.mem_append, List.mem_singleton] at hy
          rcases hy with hy | hy
          · exact hpre y hy
          · omega
        have := ih (pre ++ [0]) hpre' hu' hb' L (by simp at hL ⊢; omega)
        rw [List.flatMap_append, show [0].flatMap sigma = [0, 1] from rfl, List.append_assoc]
          at this
        rw [List.take_succ_cons, List.take_succ_cons, List.getD_cons_succ, List.getD_cons_succ]
        exact this
    · rw [Bd_one] at hb0
      obtain ⟨h1, h2⟩ := hb0
      have hm1 := mul_nonneg (sub_nonneg.2 hhi.le) (neg_le_iff_add_nonneg.1 h1)
      have hm2 := mul_nonneg (sub_nonneg.2 hhi.le) (sub_nonneg.2 h2)
      rw [List.flatMap_cons, show sigma 1 = [1, 1, 0, 1] from rfl, List.cons_append,
        List.cons_append, List.cons_append, List.cons_append, List.nil_append] at hL ⊢
      rcases L with _ | _ | _ | _ | L
      · rw [List.take_zero, List.getD_cons_zero, hE, E_nil, Bd_one]
        constructor <;> nlinarith [sq2]
      · rw [List.take_succ_cons, List.take_zero, List.getD_cons_succ, List.getD_cons_zero, hE,
          E_1, Bd_one]
        constructor <;> nlinarith [sq2]
      · rw [List.take_succ_cons, List.take_succ_cons, List.take_zero, List.getD_cons_succ,
          List.getD_cons_succ, List.getD_cons_zero, hE, E_11, Bd_zero]
        constructor <;> nlinarith [sq2]
      · rw [List.take_succ_cons, List.take_succ_cons, List.take_succ_cons, List.take_zero,
          List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_zero, hE,
          E_110, Bd_one]
        constructor <;> nlinarith [sq2]
      · have hb' : ∀ j, j < u.length → Bd (E ((pre ++ [1]) ++ u.take j)) (u.getD j 0) := by
          intro j hj
          have := hb (j + 1) (by simp; omega)
          rw [List.take_succ_cons, List.getD_cons_succ] at this
          rw [List.append_assoc, List.singleton_append]
          exact this
        have hpre' : ∀ y ∈ pre ++ [1], y ≤ 1 := by
          intro y hy
          rw [List.mem_append, List.mem_singleton] at hy
          rcases hy with hy | hy
          · exact hpre y hy
          · omega
        have := ih (pre ++ [1]) hpre' hu' hb' L (by simp at hL ⊢; omega)
        rw [List.flatMap_append, show [1].flatMap sigma = [1, 1, 0, 1] from rfl,
          List.append_assoc] at this
        rw [List.take_succ_cons, List.take_succ_cons, List.take_succ_cons, List.take_succ_cons,
          List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ]
        exact this

/-- The bound holds before every letter of every iterate. -/
theorem bound_iter (k : ℕ) :
    ∀ L, L < (iter k).length → Bd (E ((iter k).take L)) ((iter k).getD L 0) := by
  induction k with
  | zero =>
    intro L hL
    have hL0 : L = 0 := by simp [iter] at hL; omega
    subst hL0
    rw [List.take_zero, E_nil]
    show Bd 0 0
    rw [Bd_zero]
    exact ⟨le_rfl, Real.sqrt_nonneg 2⟩
  | succ k ih =>
    intro L hL
    rw [iter_succ] at hL ⊢
    have := step (iter k) [] (by simp) (letters_iter k)
      (fun j hj => by rw [List.nil_append]; exact ih j hj) L hL
    rw [List.flatMap_nil, List.nil_append] at this
    exact this

theorem conjecture : ∀ n : ℕ, 1 ≤ n →
    -1 < (n : ℝ) * Real.sqrt 2 - a n ∧ (n : ℝ) * Real.sqrt 2 - a n < 2 := by
  intro n hn
  have hinf := infinite_ones
  have hp : 1 ≤ a n ∧ A284939 (a n) = 1 := Nat.nth_mem_of_infinite hinf (n - 1)
  have hc : Nat.count (fun i => 1 ≤ i ∧ A284939 i = 1) (a n) = n - 1 :=
    Nat.count_nth_of_infinite hinf (n - 1)
  obtain ⟨m, hm⟩ : ∃ m, a n = m + 1 := ⟨a n - 1, by omega⟩
  rw [hm] at hp hc
  have hlen := len_iter (m + 1)
  have h1 := count_eq (m + 1) (m + 1) (by omega)
  rw [Nat.count_succ, hc, if_pos hp] at h1
  have hcount : ((iter (m + 1)).take (m + 1)).count 1 = n := by omega
  have hag := agree (m + 1) (m + 1) (by omega) (by omega)
  rw [Nat.add_sub_cancel] at hag
  have hw : (iter (m + 1)).getD m 0 = 1 := by rw [← hag]; exact hp.2
  have hb := bound_iter (m + 1) m (by omega)
  rw [hw, Bd_one] at hb
  have hlt : m < (iter (m + 1)).length := by omega
  have htake : (iter (m + 1)).take (m + 1) = (iter (m + 1)).take m ++ [1] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some]
    rw [List.getD_eq_getElem _ _ hlt] at hw
    rw [hw]
  have hE1 : E ((iter (m + 1)).take (m + 1)) = Real.sqrt 2 * n - (m + 1) := by
    unfold E
    rw [hcount, List.length_take, min_eq_left (by omega)]
    push_cast
    ring
  have hE2 : E ((iter (m + 1)).take (m + 1)) = E ((iter (m + 1)).take m) + (Real.sqrt 2 - 1) := by
    rw [htake, E_append, E_1]
  have hlo := s_lo
  have hhi := s_hi
  rw [hm]
  push_cast
  constructor <;> nlinarith

/-- Control: a(k) = m + 1 when position m + 1 holds a 1 of the third iterate (20 letters). -/
theorem a_eq (k m : ℕ) (hm : m + 1 ≤ (iter 3).length)
    (h1 : ((iter 3).take m).count 1 + 1 = k) (h2 : (iter 3).getD m 0 = 1) : a k = m + 1 := by
  have hp : 1 ≤ m + 1 ∧ A284939 (m + 1) = 1 := by
    refine ⟨by omega, ?_⟩
    rw [agree 3 (m + 1) (by omega) hm, Nat.add_sub_cancel]
    exact h2
  have hc := count_eq 3 m (by omega)
  unfold a
  rw [← h1, Nat.add_sub_cancel, ← hc]
  exact Nat.nth_count hp

/-- Controls: a(1..8) = 2, 3, 4, 6, 7, 8, 10, 11, the entry's data. -/
example : a 1 = 2 ∧ a 2 = 3 ∧ a 3 = 4 ∧ a 4 = 6 ∧ a 5 = 7 ∧ a 6 = 8 ∧ a 7 = 10 ∧ a 8 = 11 :=
  ⟨a_eq 1 1 (by decide) (by decide) (by decide), a_eq 2 2 (by decide) (by decide) (by decide),
    a_eq 3 3 (by decide) (by decide) (by decide), a_eq 4 5 (by decide) (by decide) (by decide),
    a_eq 5 6 (by decide) (by decide) (by decide), a_eq 6 7 (by decide) (by decide) (by decide),
    a_eq 7 9 (by decide) (by decide) (by decide),
    a_eq 8 10 (by decide) (by decide) (by decide)⟩

end OMA.S_oeis_a284941

theorem OMA.solution : type_of% @OMA.S_oeis_a284941.main :=
  OMA.S_oeis_a284941.conjecture
