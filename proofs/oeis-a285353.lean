import OMAStatements.S_oeis_a285353

namespace OMA.S_oeis_a285353







/-! ### The fixed point and its zeros (as for A285346) -/

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

theorem agree (K i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ (iter K).length) :
    A285345 i = (iter K).getD (i - 1) 0 := by
  unfold A285345
  rcases le_total i K with h | h
  · obtain ⟨t, ht⟩ := iter_mono h
    have := len_iter i
    rw [ht, List.getD_append _ _ _ _ (by omega)]
  · obtain ⟨t, ht⟩ := iter_mono h
    rw [ht, List.getD_append _ _ _ _ (by omega)]

theorem letters_flatMap (u : List ℕ) : ∀ y ∈ u.flatMap sigma, y ≤ 1 := by
  intro y hy
  rw [List.mem_flatMap] at hy
  obtain ⟨x, _, hx⟩ := hy
  rcases x with _ | x <;> simp [sigma] at hx <;> omega

theorem letters_iter (k : ℕ) : ∀ y ∈ iter k, y ≤ 1 := by
  cases k with
  | zero => simp [iter]
  | succ k => rw [iter_succ]; exact letters_flatMap _

theorem count01 (l : List ℕ) (hl : ∀ y ∈ l, y ≤ 1) : l.count 0 + l.count 1 = l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have hx : x ≤ 1 := hl x (by simp)
    have := ih (fun y hy => hl y (by simp [hy]))
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hx with rfl | rfl <;> simp [List.count_cons] <;> omega

/-- The block of an image word ending at a 0 has length 2c or 2c + 1, c its number of 0s. -/
theorem key0 (u : List ℕ) (L : ℕ) (hlen : L < (u.flatMap sigma).length)
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

theorem count_eq0 (K m : ℕ) (hm : m ≤ (iter K).length) :
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

/-- A285346(n) is 2n or 2n + 1 (the conjecture of A285346). -/
theorem zero_pos (n : ℕ) (hn : 1 ≤ n) : A285346 n = 2 * n ∨ A285346 n = 2 * n + 1 := by
  have hinf := infinite_zeros
  have hp : 1 ≤ A285346 n ∧ A285345 (A285346 n) = 0 := Nat.nth_mem_of_infinite hinf (n - 1)
  have hc : Nat.count (fun i => 1 ≤ i ∧ A285345 i = 0) (A285346 n) = n - 1 :=
    Nat.count_nth_of_infinite hinf (n - 1)
  obtain ⟨m, hm⟩ : ∃ m, A285346 n = m + 1 := ⟨A285346 n - 1, by omega⟩
  rw [hm] at hp hc
  have hlen := len_iter (m + 1)
  have h1 := count_eq0 (m + 1) (m + 1) (by omega)
  rw [Nat.count_succ, hc, if_pos hp] at h1
  have hag := agree (m + 1) (m + 1) (by omega) (by omega)
  rw [Nat.add_sub_cancel] at hag
  have hw : (iter (m + 1)).getD m 0 = 0 := by rw [← hag]; exact hp.2
  rw [iter_succ] at hw h1 hlen
  have hk := key0 (iter m) m (by omega) hw
  rw [← h1] at hk
  rw [hm]
  omega

/-! ### A285351 is the image of the fixed point under 0 -> 1, 1 -> 01

We work with its complement V = 1 - A285351, the image under nu : 0 -> 0, 1 -> 10. -/

/-- The morphism nu : 0 -> 0, 1 -> 10. -/
def nu : ℕ → List ℕ
  | 0 => [0]
  | _ => [1, 0]

/-- nu after sigma: 0 -> 100, 1 -> 101000. -/
def rho : ℕ → List ℕ
  | 0 => [1, 0, 0]
  | _ => [1, 0, 1, 0, 0, 0]

theorem rho_eq (u : List ℕ) : (u.flatMap sigma).flatMap nu = u.flatMap rho := by
  induction u with
  | nil => rfl
  | cons x u ih =>
    rw [List.flatMap_cons, List.flatMap_append, ih, List.flatMap_cons]
    congr 1
    rcases x with _ | x <;> rfl

theorem len_nu (u : List ℕ) : u.length ≤ (u.flatMap nu).length := by
  induction u with
  | nil => simp
  | cons x u ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have : 1 ≤ (nu x).length := by rcases x with _ | x <;> simp [nu]
    omega

theorem len_rho (u : List ℕ) : u.length ≤ (u.flatMap rho).length := by
  induction u with
  | nil => simp
  | cons x u ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have : 1 ≤ (rho x).length := by rcases x with _ | x <;> simp [rho]
    omega

/-- Pair n of the image word (letters 2n - 1, 2n) closes with two more 1s than 0s exactly when
letter n of the nu-image is 1. -/
theorem lemE (u : List ℕ) : ∀ n, 1 ≤ n → n ≤ (u.flatMap nu).length →
    (((u.flatMap sigma).take (2 * n)).count 1 = n + 1 ↔ (u.flatMap nu).getD (n - 1) 0 = 1) := by
  induction u with
  | nil => intro n h1 h2; simp at h2; omega
  | cons x u ih =>
    intro n h1 h2
    simp only [List.flatMap_cons] at h2 ⊢
    rcases x with _ | x
    · simp only [sigma, nu, List.cons_append, List.nil_append] at h2 ⊢
      rcases n with _ | _ | n
      · omega
      · simp
      · rw [show 2 * (n + 1 + 1) = 2 * (n + 1) + 1 + 1 by ring, List.take_succ_cons,
          List.take_succ_cons, show n + 1 + 1 - 1 = n + 1 by omega, List.getD_cons_succ]
        have := ih (n + 1) (by omega) (by simp only [List.length_cons] at h2; omega)
        rw [show n + 1 - 1 = n by omega] at this
        have e : List.count 1 (1 :: 0 :: List.take (2 * (n + 1)) (List.flatMap sigma u)) =
            List.count 1 (List.take (2 * (n + 1)) (List.flatMap sigma u)) + 1 := by
          simp [List.count_cons]
        rw [e, ← this]
        constructor <;> intro h <;> omega
    · simp only [sigma, nu, List.cons_append, List.nil_append] at h2 ⊢
      rcases n with _ | _ | _ | n
      · omega
      · simp
      · simp
      · rw [show 2 * (n + 1 + 1 + 1) = 2 * (n + 1) + 1 + 1 + 1 + 1 by ring, List.take_succ_cons,
          List.take_succ_cons, List.take_succ_cons, List.take_succ_cons,
          show n + 1 + 1 + 1 - 1 = n + 1 + 1 by omega, List.getD_cons_succ, List.getD_cons_succ]
        have := ih (n + 1) (by omega) (by simp only [List.length_cons] at h2; omega)
        rw [show n + 1 - 1 = n by omega] at this
        have e : List.count 1
            (1 :: 1 :: 0 :: 0 :: List.take (2 * (n + 1)) (List.flatMap sigma u)) =
            List.count 1 (List.take (2 * (n + 1)) (List.flatMap sigma u)) + 2 := by
          simp [List.count_cons]
        rw [e, ← this]
        constructor <;> intro h <;> omega

/-- V(i) for i >= 1: the i-th letter of the nu-image of the fixed point. -/
def V (i : ℕ) : ℕ := ((iter i).flatMap nu).getD (i - 1) 0

theorem agreeV (K i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ ((iter K).flatMap nu).length) :
    V i = ((iter K).flatMap nu).getD (i - 1) 0 := by
  unfold V
  rcases le_total i K with h | h
  · obtain ⟨t, ht⟩ := iter_mono h
    have := len_iter i
    have := len_nu (iter i)
    rw [ht, List.flatMap_append, List.getD_append _ _ _ _ (by omega)]
  · obtain ⟨t, ht⟩ := iter_mono h
    rw [ht, List.flatMap_append, List.getD_append _ _ _ _ (by omega)]

/-- The zeros of A285351 are the 1s of V. -/
theorem t_iff (n : ℕ) (hn : 1 ≤ n) : A285351 n = 0 ↔ V n = 1 := by
  have hz := zero_pos n hn
  have hinf := infinite_zeros
  have hp : 1 ≤ A285346 n ∧ A285345 (A285346 n) = 0 := Nat.nth_mem_of_infinite hinf (n - 1)
  have hc : Nat.count (fun i => 1 ≤ i ∧ A285345 i = 0) (A285346 n) = n - 1 :=
    Nat.count_nth_of_infinite hinf (n - 1)
  have hlen := len_iter n
  have hlen1 := len_iter (n + 1)
  have hl2 := len_flatMap (iter n)
  have hc2 := count_eq0 (n + 1) (2 * n) (by rw [iter_succ]; omega)
  have h01 := count01 ((iter (n + 1)).take (2 * n))
    (fun y hy => letters_iter (n + 1) y (List.mem_of_mem_take hy))
  rw [List.length_take, min_eq_left (by rw [iter_succ]; omega)] at h01
  have hE := lemE (iter n) n hn (by have := len_nu (iter n); omega)
  rw [← iter_succ] at hE
  have hV : V n = ((iter n).flatMap nu).getD (n - 1) 0 := rfl
  rw [hV, ← hE]
  unfold A285351
  constructor
  · intro h0
    have hZ : A285346 n = 2 * n + 1 := by omega
    rw [hZ] at hc
    omega
  · intro h1
    rcases hz with hz | hz
    · exfalso
      rw [hz] at hp hc
      have := Nat.count_succ (fun i => 1 ≤ i ∧ A285345 i = 0) (2 * n)
      rw [hc, if_pos hp] at this
      omega
    · rw [hz]
      push_cast
      ring

/-- The block of a rho-image word ending at a 1 has length 3c - 3 or 3c - 2, c its number of 1s. -/
theorem keyV (u : List ℕ) (L : ℕ) (hL : (u.flatMap rho).getD L 0 = 1) :
    3 * ((u.flatMap rho).take (L + 1)).count 1 ≤ L + 4 ∧
      L + 3 ≤ 3 * ((u.flatMap rho).take (L + 1)).count 1 := by
  induction u generalizing L with
  | nil => simp at hL
  | cons x u ih =>
    rw [List.flatMap_cons] at hL ⊢
    rcases x with _ | x
    · simp only [rho, List.cons_append, List.nil_append] at hL ⊢
      rcases L with _ | _ | _ | L
      · simp
      · simp at hL
      · simp at hL
      · rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ] at hL
        have := ih L hL
        simp only [List.take_succ_cons, List.count_cons] at this ⊢
        simp
        omega
    · simp only [rho, List.cons_append, List.nil_append] at hL ⊢
      rcases L with _ | _ | _ | _ | _ | _ | L
      · simp
      · simp at hL
      · simp
      · simp at hL
      · simp at hL
      · simp at hL
      · rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ,
          List.getD_cons_succ, List.getD_cons_succ] at hL
        have := ih L hL
        simp only [List.take_succ_cons, List.count_cons] at this ⊢
        simp
        omega

theorem count_eqV (K m : ℕ) (hm : m ≤ ((iter K).flatMap nu).length) :
    Nat.count (fun i => 1 ≤ i ∧ V i = 1) (m + 1) = (((iter K).flatMap nu).take m).count 1 := by
  induction m with
  | zero => simp [Nat.count_succ]
  | succ m ih =>
    have hlt : m < ((iter K).flatMap nu).length := by omega
    rw [Nat.count_succ, ih (by omega), List.take_add_one, List.getElem?_eq_getElem hlt,
      Option.toList_some, List.count_append, List.count_singleton]
    have hag := agreeV K (m + 1) (by omega) (by omega)
    rw [Nat.add_sub_cancel, List.getD_eq_getElem ((iter K).flatMap nu) 0 hlt] at hag
    by_cases h : ((iter K).flatMap nu)[m] = 1
    · simp [h, hag]
    · simp [h, hag]

theorem infinite_V : (Set.ofPred (fun i => 1 ≤ i ∧ V i = 1)).Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨N, hN⟩
  have hne : iter N ≠ [] := by
    intro h
    have := len_iter N
    rw [h] at this
    simp at this
  obtain ⟨t, x, ht⟩ : ∃ t x, iter N = t ++ [x] :=
    ⟨(iter N).dropLast, (iter N).getLast hne, (List.dropLast_concat_getLast hne).symm⟩
  have hlen := len_iter N
  rw [ht, List.length_append, List.length_singleton] at hlen
  have hft := len_rho t
  have hsucc : (iter (N + 1)).flatMap nu = t.flatMap rho ++ rho x := by
    rw [iter_succ, rho_eq, ht, List.flatMap_append, List.flatMap_singleton]
  have hx : 1 ≤ (rho x).length ∧ (rho x).getD 0 0 = 1 := by
    rcases x with _ | x <;> exact ⟨by simp [rho], rfl⟩
  have hmem : (t.flatMap rho).length + 1 ∈ Set.ofPred (fun i => 1 ≤ i ∧ V i = 1) := by
    show 1 ≤ _ ∧ V _ = 1
    refine ⟨by omega, ?_⟩
    have hl : ((iter (N + 1)).flatMap nu).length = (t.flatMap rho).length + (rho x).length := by
      rw [hsucc, List.length_append]
    rw [agreeV (N + 1) _ (by omega) (by omega), hsucc, Nat.add_sub_cancel,
      List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
    exact hx.2
  have := hN hmem
  omega

theorem pred_eq : (fun i => 1 ≤ i ∧ A285351 i = 0) = (fun i => 1 ≤ i ∧ V i = 1) := by
  funext i
  apply propext
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (t_iff i h1).1 h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (t_iff i h1).2 h2⟩

theorem conjecture : ∀ n : ℕ, 1 ≤ n → (3 * n : ℤ) - 2 - a n ∈ ({0, 1} : Set ℤ) := by
  intro n hn
  have ha : a n = Nat.nth (fun i => 1 ≤ i ∧ V i = 1) (n - 1) := by
    unfold a
    rw [pred_eq]
  have hinf := infinite_V
  have hp : 1 ≤ a n ∧ V (a n) = 1 := by rw [ha]; exact Nat.nth_mem_of_infinite hinf (n - 1)
  have hc : Nat.count (fun i => 1 ≤ i ∧ V i = 1) (a n) = n - 1 := by
    rw [ha]; exact Nat.count_nth_of_infinite hinf (n - 1)
  obtain ⟨m, hm⟩ : ∃ m, a n = m + 1 := ⟨a n - 1, by omega⟩
  rw [hm] at hp hc
  have hlen := len_iter (m + 1)
  have hlen2 := len_nu (iter (m + 2))
  have hlen3 := len_iter (m + 2)
  have h1 := count_eqV (m + 2) (m + 1) (by omega)
  rw [Nat.count_succ, hc, if_pos hp] at h1
  have hag := agreeV (m + 2) (m + 1) (by omega) (by omega)
  rw [Nat.add_sub_cancel] at hag
  have hw : ((iter (m + 2)).flatMap nu).getD m 0 = 1 := by rw [← hag]; exact hp.2
  rw [iter_succ, rho_eq] at hw h1
  have hk := keyV (iter (m + 1)) m hw
  rw [← h1] at hk
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [hm]
  push_cast
  omega

/-- Control: a(k) = m + 1 when position m + 1 of the nu-image of iter 3 (51 letters) is a 1. -/
theorem a_eq (k m : ℕ) (hm : m + 1 ≤ ((iter 3).flatMap nu).length)
    (h1 : (((iter 3).flatMap nu).take m).count 1 + 1 = k)
    (h2 : ((iter 3).flatMap nu).getD m 0 = 1) : a k = m + 1 := by
  have hp : 1 ≤ m + 1 ∧ V (m + 1) = 1 := by
    refine ⟨by omega, ?_⟩
    rw [agreeV 3 (m + 1) (by omega) hm, Nat.add_sub_cancel]
    exact h2
  have hc := count_eqV 3 m (by omega)
  unfold a
  rw [pred_eq, ← h1, Nat.add_sub_cancel, ← hc]
  exact Nat.nth_count hp

/-- Controls: a(1..8) = 1, 3, 7, 9, 13, 16, 19, 21, the entry's data. -/
example : a 1 = 1 ∧ a 2 = 3 ∧ a 3 = 7 ∧ a 4 = 9 ∧ a 5 = 13 ∧ a 6 = 16 ∧ a 7 = 19 ∧ a 8 = 21 :=
  ⟨a_eq 1 0 (by decide) (by decide) (by decide), a_eq 2 2 (by decide) (by decide) (by decide),
    a_eq 3 6 (by decide) (by decide) (by decide), a_eq 4 8 (by decide) (by decide) (by decide),
    a_eq 5 12 (by decide) (by decide) (by decide), a_eq 6 15 (by decide) (by decide) (by decide),
    a_eq 7 18 (by decide) (by decide) (by decide),
    a_eq 8 20 (by decide) (by decide) (by decide)⟩

end OMA.S_oeis_a285353

theorem OMA.solution : type_of% @OMA.S_oeis_a285353.main :=
  OMA.S_oeis_a285353.conjecture
