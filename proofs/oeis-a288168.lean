import OMAStatements.S_oeis_a288168

namespace OMA.S_oeis_a288168





/-! ### One pass -/

/-- Induction along the cases of `step`. -/
theorem step_rec {P : List ℕ → Prop} (h0 : P []) (h00 : ∀ l, P l → P (0 :: 0 :: l))
    (h1 : ∀ l, P l → P (1 :: l)) (hz : P [0])
    (hzy : ∀ y l, P ((y + 1) :: l) → P (0 :: (y + 1) :: l))
    (hx : ∀ x l, P l → P ((x + 2) :: l)) : ∀ u, P u := by
  have key : ∀ n, ∀ u : List ℕ, u.length ≤ n → P u := by
    intro n
    induction n with
    | zero =>
      intro u hu
      cases u with
      | nil => exact h0
      | cons x l => simp at hu
    | succ n ih =>
      intro u hu
      rcases u with _ | ⟨x, l⟩
      · exact h0
      · simp only [List.length_cons] at hu
        rcases x with _ | _ | x
        · rcases l with _ | ⟨y, l⟩
          · exact hz
          · rcases y with _ | y
            · exact h00 l (ih l (by simp at hu; omega))
            · exact hzy y l (ih _ (by simpa using hu))
        · exact h1 l (ih l (by omega))
        · exact hx x l (ih l (by omega))
  exact fun u => key u.length u le_rfl

lemma step_zero_cons (w : List ℕ) : ∃ r, step (0 :: w) = 0 :: r := by
  rcases w with _ | ⟨y, w⟩
  · exact ⟨[], rfl⟩
  · rcases y with _ | y
    · exact ⟨0 :: 1 :: 0 :: step w, rfl⟩
    · exact ⟨step ((y + 1) :: w), rfl⟩

/-- A pass over u is a prefix of the pass over any extension of u. -/
lemma step_prefix (u : List ℕ) : ∀ w, step u <+: step (u ++ w) := by
  refine step_rec (P := fun u => ∀ w, step u <+: step (u ++ w)) ?_ ?_ ?_ ?_ ?_ ?_ u
  · intro w
    exact List.nil_prefix
  · intro l ih w
    show [0, 0, 1, 0] ++ step l <+: [0, 0, 1, 0] ++ step (l ++ w)
    exact (List.prefix_append_right_inj _).mpr (ih w)
  · intro l ih w
    show [0, 0, 0] ++ step l <+: [0, 0, 0] ++ step (l ++ w)
    exact (List.prefix_append_right_inj _).mpr (ih w)
  · intro w
    obtain ⟨r, hr⟩ := step_zero_cons w
    show [0] <+: step (0 :: w)
    rw [hr]
    exact ⟨r, rfl⟩
  · intro y l ih w
    show [0] ++ step ((y + 1) :: l) <+: [0] ++ step ((y + 1) :: l ++ w)
    exact (List.prefix_append_right_inj _).mpr (ih w)
  · intro x l ih w
    show [x + 2] ++ step l <+: [x + 2] ++ step (l ++ w)
    exact (List.prefix_append_right_inj _).mpr (ih w)

lemma step_length (u : List ℕ) : u.length ≤ (step u).length := by
  refine step_rec (P := fun u => u.length ≤ (step u).length) ?_ ?_ ?_ ?_ ?_ ?_ u
  · exact le_rfl
  · intro l ih
    show (0 :: 0 :: l).length ≤ (0 :: 0 :: 1 :: 0 :: step l).length
    simp only [List.length_cons]
    omega
  · intro l ih
    show (1 :: l).length ≤ (0 :: 0 :: 0 :: step l).length
    simp only [List.length_cons]
    omega
  · exact le_rfl
  · intro y l ih
    show (0 :: (y + 1) :: l).length ≤ (0 :: step ((y + 1) :: l)).length
    simp only [List.length_cons] at ih ⊢
    omega
  · intro x l ih
    show ((x + 2) :: l).length ≤ ((x + 2) :: step l).length
    simp only [List.length_cons]
    omega

/-- A pass keeps all letters in {0, 1}. -/
lemma step_le (u : List ℕ) : (∀ x ∈ u, x ≤ 1) → ∀ x ∈ step u, x ≤ 1 := by
  refine step_rec (P := fun u => (∀ x ∈ u, x ≤ 1) → ∀ x ∈ step u, x ≤ 1) ?_ ?_ ?_ ?_ ?_ ?_ u
  · intro _ x hx
    exact absurd hx List.not_mem_nil
  · intro l ih hu x hx
    change x ∈ 0 :: 0 :: 1 :: 0 :: step l at hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | rfl | hx
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact ih (fun y hy => hu y (by simp [hy])) x hx
  · intro l ih hu x hx
    change x ∈ 0 :: 0 :: 0 :: step l at hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | hx
    · norm_num
    · norm_num
    · norm_num
    · exact ih (fun y hy => hu y (by simp [hy])) x hx
  · intro hu x hx
    exact hu x hx
  · intro y l ih hu x hx
    change x ∈ 0 :: step ((y + 1) :: l) at hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · norm_num
    · exact ih (fun z hz => hu z (by simp [hz])) x hx
  · intro x l ih hu z hz
    change z ∈ (x + 2) :: step l at hz
    have := hu (x + 2) (by simp)
    omega

/-- In a pass, every letter 1 is followed by a letter 0. -/
lemma step_one (u : List ℕ) : ∀ i, (step u).getD i 0 = 1 → (step u).getD (i + 1) 0 = 0 := by
  refine step_rec (P := fun u => ∀ i, (step u).getD i 0 = 1 → (step u).getD (i + 1) 0 = 0)
    ?_ ?_ ?_ ?_ ?_ ?_ u
  · intro i h
    change ([] : List ℕ).getD i 0 = 1 at h
    simp at h
  · intro l ih i h
    change (0 :: 0 :: 1 :: 0 :: step l).getD i 0 = 1 at h
    change (0 :: 0 :: 1 :: 0 :: step l).getD (i + 1) 0 = 0
    rcases i with _ | _ | _ | _ | j
    · simp at h
    · simp at h
    · rfl
    · simp at h
    · exact ih j h
  · intro l ih i h
    change (0 :: 0 :: 0 :: step l).getD i 0 = 1 at h
    change (0 :: 0 :: 0 :: step l).getD (i + 1) 0 = 0
    rcases i with _ | _ | _ | j
    · simp at h
    · simp at h
    · simp at h
    · exact ih j h
  · intro i h
    change [0].getD i 0 = 1 at h
    rcases i with _ | j
    · simp at h
    · simp at h
  · intro y l ih i h
    change (0 :: step ((y + 1) :: l)).getD i 0 = 1 at h
    change (0 :: step ((y + 1) :: l)).getD (i + 1) 0 = 0
    rcases i with _ | j
    · simp at h
    · exact ih j h
  · intro x l ih i h
    change ((x + 2) :: step l).getD i 0 = 1 at h
    change ((x + 2) :: step l).getD (i + 1) 0 = 0
    rcases i with _ | j
    · simp at h
    · exact ih j h

/-! ### The iterates and the fixed point -/

lemma iter_head (n : ℕ) : ∃ r, iter n = 0 :: 0 :: r := by
  induction n with
  | zero => exact ⟨[], rfl⟩
  | succ n ih =>
    obtain ⟨r, hr⟩ := ih
    exact ⟨1 :: 0 :: step r, by rw [show iter (n + 1) = step (iter n) from rfl, hr]; rfl⟩

lemma iter_length (n : ℕ) : 2 * n + 2 ≤ (iter n).length := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    obtain ⟨r, hr⟩ := iter_head n
    have h1 : iter (n + 1) = 0 :: 0 :: 1 :: 0 :: step r := by
      rw [show iter (n + 1) = step (iter n) from rfl, hr]
      rfl
    have h2 := step_length r
    rw [hr] at ih
    rw [h1]
    simp only [List.length_cons] at ih ⊢
    omega

lemma iter_prefix_succ (n : ℕ) : iter n <+: iter (n + 1) := by
  induction n with
  | zero => exact ⟨[1, 0], rfl⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    show step (iter n) <+: step (iter (n + 1))
    rw [← ht]
    exact step_prefix _ _

lemma iter_le (n : ℕ) : ∀ x ∈ iter n, x ≤ 1 := by
  induction n with
  | zero =>
    intro x hx
    change x ∈ [0, 0] at hx
    simp at hx
    omega
  | succ n ih => exact step_le _ ih

lemma W_le (i : ℕ) : W i ≤ 1 := by
  unfold W
  rcases lt_or_ge i (iter (i + 1)).length with h | h
  · rw [List.getD_eq_getElem _ _ h]
    exact iter_le _ _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ h]
    norm_num

lemma W_eq_succ (i : ℕ) : W i = (iter (i + 2)).getD i 0 := by
  unfold W
  obtain ⟨t, ht⟩ := iter_prefix_succ (i + 1)
  have hi : i < (iter (i + 1)).length := by
    have := iter_length (i + 1)
    omega
  rw [← ht, List.getD_append _ _ _ _ hi]

lemma W_one (i : ℕ) (h : W i = 1) : W (i + 1) = 0 := by
  rw [W_eq_succ] at h
  exact step_one (iter (i + 1)) i h

lemma W_zero : W 0 = 0 := rfl

/-! ### Counting letters 0 -/

/-- Z(N): the number of letters 0 among the first N letters of W. -/
noncomputable def Z (N : ℕ) : ℕ := Nat.count (fun i => W i = 0) N

lemma Z_succ (N : ℕ) : Z (N + 1) = Z N + if W N = 0 then 1 else 0 := Nat.count_succ _ _

lemma Z_odd (m : ℕ) : m + 1 ≤ Z (2 * m + 1) := by
  induction m with
  | zero =>
    rw [show 2 * 0 + 1 = 0 + 1 from rfl, Z_succ, if_pos W_zero]
    simp [Z]
  | succ m ih =>
    have h1 := W_le (2 * m + 1)
    have h2 : W (2 * m + 1) = 1 → W (2 * m + 1 + 1) = 0 := W_one _
    have h2' : W (2 * m + 1) = 1 → W (2 * m + 2) = 0 := W_one _
    have z1 := Z_succ (2 * m + 1)
    have z2 := Z_succ (2 * m + 1 + 1)
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring]
    split_ifs at z1 z2 <;> omega

lemma zeros_infinite : (setOf (fun i => W i = 0)).Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  have hconst : ∀ j, Z (B + 1 + j) = Z (B + 1) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      have hno : ¬ W (B + 1 + j) = 0 := fun h => by
        have := hB h
        omega
      rw [show B + 1 + (j + 1) = B + 1 + j + 1 by ring, Z_succ, if_neg hno, ih, add_zero]
  have h1 := Z_odd (B + 1)
  have h2 := hconst (B + 1)
  have h3 : Z (B + 1) ≤ B + 1 := Nat.count_le _
  rw [show B + 1 + (B + 1) = 2 * (B + 1) by ring] at h2
  have h4 : Z (2 * (B + 1) + 1) = Z (2 * (B + 1)) := by
    rw [Z_succ, if_neg (fun h => by have := hB h; omega), add_zero]
  omega

lemma a_le (n : ℕ) (hn : 1 ≤ n) : a n ≤ 2 * n - 1 := by
  have key := Z_odd (n - 1)
  have hlt : Nat.nth (fun i => W i = 0) (n - 1) < 2 * (n - 1) + 1 :=
    Nat.nth_lt_of_lt_count (by unfold Z at key; omega)
  unfold a
  omega

lemma a_ge (n : ℕ) (hn : 1 ≤ n) : n ≤ a n := by
  have hZp : Z (Nat.nth (fun i => W i = 0) (n - 1)) = n - 1 :=
    Nat.count_nth_of_infinite zeros_infinite (n - 1)
  have hle : Z (Nat.nth (fun i => W i = 0) (n - 1)) ≤ Nat.nth (fun i => W i = 0) (n - 1) :=
    Nat.count_le _
  unfold a
  omega

/-- Kimberling's conjecture: -1 < 6/5 - a(n)/n < 1 for n >= 1. -/
theorem conjecture : ∀ n : ℕ, 1 ≤ n → -1 < 6 / 5 - (a n : ℝ) / n ∧ 6 / 5 - (a n : ℝ) / n < 1 := by
  intro n hn
  have h1 := a_le n hn
  have h2 := a_ge n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1' : (a n : ℝ) ≤ 2 * n := by exact_mod_cast (show a n ≤ 2 * n by omega)
  have h2' : (n : ℝ) ≤ a n := by exact_mod_cast h2
  have e1 : (a n : ℝ) / n ≤ 2 := by
    rw [div_le_iff₀ hn']
    linarith
  have e2 : 1 ≤ (a n : ℝ) / n := by
    rw [le_div_iff₀ hn']
    linarith
  constructor <;> linarith

end OMA.S_oeis_a288168

theorem OMA.solution : type_of% @OMA.S_oeis_a288168.main :=
  OMA.S_oeis_a288168.conjecture
