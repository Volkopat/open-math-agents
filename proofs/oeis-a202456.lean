import OMAStatements.S_oeis_a202456

namespace OMA.S_oeis_a202456

open PowerSeries





/-- The 10 good rows. -/
def R : Fin 10 → Fin 5 → Bool :=
  ![![false, false, false, false, false],
    ![false, false, false, false, true],
    ![false, false, false, true, false],
    ![false, false, false, true, true],
    ![false, false, true, false, false],
    ![false, false, true, false, true],
    ![false, false, true, true, false],
    ![false, false, true, true, true],
    ![false, true, true, true, true],
    ![true, true, true, true, true]]

lemma rowR : ∀ r : Fin 5 → Bool, windowsOK (List.ofFn r) = true ↔ ∃ k, R k = r := by
  decide +kernel

lemma R_inj : Function.Injective R := by
  decide +kernel

/-- The column condition on four consecutive rows. -/
def step4 (r0 r1 r2 r3 : Fin 5 → Bool) : Bool :=
  decide (∀ j, win (r0 j) (r1 j) (r2 j) ≤ win (r1 j) (r2 j) (r3 j))

/-- The column condition along a list of rows. -/
def chain : List (Fin 5 → Bool) → Bool
  | r0 :: r1 :: r2 :: r3 :: rest => step4 r0 r1 r2 r3 && chain (r1 :: r2 :: r3 :: rest)
  | _ => true

theorem windows_map : ∀ l : List (Fin 5 → Bool),
    (∀ j, windowsOK (l.map fun r => r j) = true) ↔ chain l = true
  | r0 :: r1 :: r2 :: r3 :: rest => by
    have ih := windows_map (r1 :: r2 :: r3 :: rest)
    simp only [List.map_cons] at ih ⊢
    simp only [windowsOK, chain, step4, Bool.and_eq_true, decide_eq_true_eq] at ih ⊢
    rw [← ih]
    constructor
    · intro h
      exact ⟨fun j => (h j).1, fun j => (h j).2⟩
    · rintro ⟨h1, h2⟩ j
      exact ⟨h1 j, h2 j⟩
  | [] => by simp [windowsOK, chain]
  | [_] => by simp [windowsOK, chain]
  | [_, _] => by simp [windowsOK, chain]
  | [_, _, _] => by simp [windowsOK, chain]

theorem good_iff {r : ℕ} (x : Fin r → Fin 5 → Bool) :
    good x = true ↔ (∀ i, ∃ k, R k = x i) ∧ chain (List.ofFn x) = true := by
  unfold good
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, ← windows_map]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => (rowR (x i)).1 (h1 i), fun j => ?_⟩
    rw [List.map_ofFn]
    exact h2 j
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => (rowR (x i)).2 (h1 i), fun j => ?_⟩
    have := h2 j
    rwa [List.map_ofFn] at this

/-- The column condition on codes of rows. -/
def step4C (a b c d : Fin 10) : Bool := step4 (R a) (R b) (R c) (R d)

/-- The column condition along a list of codes. -/
def chainC : List (Fin 10) → Bool
  | a :: b :: c :: d :: rest => step4C a b c d && chainC (b :: c :: d :: rest)
  | _ => true

theorem chain_map : ∀ l : List (Fin 10), chain (l.map R) = chainC l
  | a :: b :: c :: d :: rest => by
    simp only [List.map_cons, chain, chainC, step4C]
    rw [← List.map_cons, ← List.map_cons, ← List.map_cons, chain_map (b :: c :: d :: rest)]
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl

/-- The count over codes of rows. -/
theorem a_codes (n : ℕ) :
    a n = (Finset.univ.filter fun y : Fin (n + 2) → Fin 10 => chainC (List.ofFn y) = true).card := by
  symm
  unfold a
  apply Finset.card_bij (fun y _ => fun i => R (y i))
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    rw [good_iff]
    refine ⟨fun i => ⟨y i, rfl⟩, ?_⟩
    rw [show List.ofFn (fun i => R (y i)) = (List.ofFn y).map R by rw [List.map_ofFn]; rfl, chain_map]
    exact hy
  · intro y₁ _ y₂ _ h
    funext i
    exact R_inj (congrFun h i)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [good_iff] at hx
    obtain ⟨h1, h2⟩ := hx
    choose y hy using h1
    refine ⟨y, ?_, funext hy⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← chain_map, show (List.ofFn y).map R = List.ofFn x by rw [List.map_ofFn]; exact congrArg _ (funext hy)]
    exact h2

theorem sum_cons (m : ℕ) (f : List (Fin 10) → ℕ) :
    ∑ x : Fin (m + 1) → Fin 10, f (List.ofFn x) = ∑ c : Fin 10, ∑ y : Fin m → Fin 10, f (c :: List.ofFn y) := by
  rw [← (Fin.consEquiv fun _ => Fin 10).sum_comp, Fintype.sum_prod_type]
  simp [List.ofFn_succ]

/-- The continuations by m rows of the column condition from the rows a, b, c. -/
def G (a b c : Fin 10) (m : ℕ) : ℕ :=
  ∑ y : Fin m → Fin 10, if chainC (a :: b :: c :: List.ofFn y) = true then 1 else 0

theorem G_zero (a b c : Fin 10) : G a b c 0 = 1 := by
  simp [G, chainC]

theorem G_succ (a b c : Fin 10) (m : ℕ) :
    G a b c (m + 1) = ∑ d : Fin 10, if step4C a b c d = true then G b c d m else 0 := by
  unfold G
  rw [sum_cons m (fun l => if chainC (a :: b :: c :: l) = true then 1 else 0)]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : step4C a b c d = true
  · rw [if_pos hd]
    apply Finset.sum_congr rfl
    intro y _
    simp only [chainC, hd, Bool.true_and]
  · rw [if_neg hd]
    apply Finset.sum_eq_zero
    intro y _
    have hd' := Bool.eq_false_iff.mpr hd
    simp [chainC, hd']

/-- The total count over the first three rows. -/
def T (m : ℕ) : ℕ := ∑ a : Fin 10, ∑ b : Fin 10, ∑ c : Fin 10, G a b c m

theorem a_T (m : ℕ) : a (m + 1) = T m := by
  rw [a_codes, Finset.card_filter]
  rw [show m + 1 + 2 = (m + 2) + 1 from rfl, sum_cons (m + 2) (fun l => if chainC l = true then 1 else 0)]
  unfold T G
  apply Finset.sum_congr rfl
  intro a _
  rw [sum_cons (m + 1) (fun l => if chainC (a :: l) = true then 1 else 0)]
  apply Finset.sum_congr rfl
  intro b _
  rw [sum_cons m (fun l => if chainC (a :: b :: l) = true then 1 else 0)]

/-- A table lookup. -/
def look (t : List (List (List ℕ))) (a b c : Fin 10) : ℕ := ((t.getD a.val []).getD b.val []).getD c.val 0
abbrev s : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]


/-- The table of G_1. -/
def t1 : List (List (List ℕ)) :=
  [[[10, 10, 10, 10, 10, 10, 10, 10, 10, 10], [10, 10, 10, 10, 10, 10, 10, 10, 10, 10], [10, 10, 10, 10, 10, 10, 10, 10, 10, 10], [10, 10, 10, 10, 10, 10, 10, 10, 10, 10], [10, 10, 10, 10, 10, 10, 10, 10, 10, 10], [10, 10, 10, 10, 10, 10, 10, 10, 10, 10], [10, 10, 10, 10, 10, 10, 10, 10, 10, 10], [10, 10, 10, 10, 10, 10, 10, 10, 10, 10], [10, 10, 10, 10, 10, 10, 10, 10, 10, 10], [10, 10, 10, 10, 10, 10, 10, 10, 10, 10]], [s, [0, 6, 0, 6, 0, 6, 0, 6, 6, 6], s, [0, 6, 0, 6, 0, 6, 0, 6, 6, 6], s, [0, 6, 0, 6, 0, 6, 0, 6, 6, 6], s, [0, 6, 0, 6, 0, 6, 0, 6, 6, 6], [0, 6, 0, 6, 0, 6, 0, 6, 6, 6], [0, 6, 0, 6, 0, 6, 0, 6, 6, 6]], [s, s, [0, 0, 6, 6, 0, 0, 6, 6, 6, 6], [0, 0, 6, 6, 0, 0, 6, 6, 6, 6], s, s, [0, 0, 6, 6, 0, 0, 6, 6, 6, 6], [0, 0, 6, 6, 0, 0, 6, 6, 6, 6], [0, 0, 6, 6, 0, 0, 6, 6, 6, 6], [0, 0, 6, 6, 0, 0, 6, 6, 6, 6]], [s, s, s, [0, 0, 0, 4, 0, 0, 0, 4, 4, 4], s, s, s, [0, 0, 0, 4, 0, 0, 0, 4, 4, 4], [0, 0, 0, 4, 0, 0, 0, 4, 4, 4], [0, 0, 0, 4, 0, 0, 0, 4, 4, 4]], [s, s, s, s, [0, 0, 0, 0, 6, 6, 6, 6, 6, 6], [0, 0, 0, 0, 6, 6, 6, 6, 6, 6], [0, 0, 0, 0, 6, 6, 6, 6, 6, 6], [0, 0, 0, 0, 6, 6, 6, 6, 6, 6], [0, 0, 0, 0, 6, 6, 6, 6, 6, 6], [0, 0, 0, 0, 6, 6, 6, 6, 6, 6]], [s, s, s, s, s, [0, 0, 0, 0, 0, 4, 0, 4, 4, 4], s, [0, 0, 0, 0, 0, 4, 0, 4, 4, 4], [0, 0, 0, 0, 0, 4, 0, 4, 4, 4], [0, 0, 0, 0, 0, 4, 0, 4, 4, 4]], [s, s, s, s, s, s, [0, 0, 0, 0, 0, 0, 4, 4, 4, 4], [0, 0, 0, 0, 0, 0, 4, 4, 4, 4], [0, 0, 0, 0, 0, 0, 4, 4, 4, 4], [0, 0, 0, 0, 0, 0, 4, 4, 4, 4]], [s, s, s, s, s, s, s, [0, 0, 0, 0, 0, 0, 0, 3, 3, 3], [0, 0, 0, 0, 0, 0, 0, 3, 3, 3], [0, 0, 0, 0, 0, 0, 0, 3, 3, 3]], [s, s, s, s, s, s, s, s, [0, 0, 0, 0, 0, 0, 0, 0, 2, 2], [0, 0, 0, 0, 0, 0, 0, 0, 2, 2]], [s, s, s, s, s, s, s, s, s, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]]

/-- The table of G_2. -/
def t2 : List (List (List ℕ)) :=
  [[[100, 100, 100, 100, 100, 100, 100, 100, 100, 100], [0, 36, 0, 36, 0, 36, 0, 36, 36, 36], [0, 0, 36, 36, 0, 0, 36, 36, 36, 36], [0, 0, 0, 16, 0, 0, 0, 16, 16, 16], [0, 0, 0, 0, 36, 36, 36, 36, 36, 36], [0, 0, 0, 0, 0, 16, 0, 16, 16, 16], [0, 0, 0, 0, 0, 0, 16, 16, 16, 16], [0, 0, 0, 0, 0, 0, 0, 9, 9, 9], [0, 0, 0, 0, 0, 0, 0, 0, 4, 4], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, [0, 36, 0, 36, 0, 36, 0, 36, 36, 36], s, [0, 0, 0, 16, 0, 0, 0, 16, 16, 16], s, [0, 0, 0, 0, 0, 16, 0, 16, 16, 16], s, [0, 0, 0, 0, 0, 0, 0, 9, 9, 9], [0, 0, 0, 0, 0, 0, 0, 0, 4, 4], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, [0, 0, 36, 36, 0, 0, 36, 36, 36, 36], [0, 0, 0, 16, 0, 0, 0, 16, 16, 16], s, s, [0, 0, 0, 0, 0, 0, 16, 16, 16, 16], [0, 0, 0, 0, 0, 0, 0, 9, 9, 9], [0, 0, 0, 0, 0, 0, 0, 0, 4, 4], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, [0, 0, 0, 16, 0, 0, 0, 16, 16, 16], s, s, s, [0, 0, 0, 0, 0, 0, 0, 9, 9, 9], [0, 0, 0, 0, 0, 0, 0, 0, 4, 4], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, [0, 0, 0, 0, 36, 36, 36, 36, 36, 36], [0, 0, 0, 0, 0, 16, 0, 16, 16, 16], [0, 0, 0, 0, 0, 0, 16, 16, 16, 16], [0, 0, 0, 0, 0, 0, 0, 9, 9, 9], [0, 0, 0, 0, 0, 0, 0, 0, 4, 4], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, [0, 0, 0, 0, 0, 16, 0, 16, 16, 16], s, [0, 0, 0, 0, 0, 0, 0, 9, 9, 9], [0, 0, 0, 0, 0, 0, 0, 0, 4, 4], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, s, [0, 0, 0, 0, 0, 0, 16, 16, 16, 16], [0, 0, 0, 0, 0, 0, 0, 9, 9, 9], [0, 0, 0, 0, 0, 0, 0, 0, 4, 4], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, s, s, [0, 0, 0, 0, 0, 0, 0, 9, 9, 9], [0, 0, 0, 0, 0, 0, 0, 0, 4, 4], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, s, s, s, [0, 0, 0, 0, 0, 0, 0, 0, 4, 4], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, s, s, s, s, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]]

/-- The table of G_3. -/
def t3 : List (List (List ℕ)) :=
  [[[1000, 216, 216, 64, 216, 64, 64, 27, 8, 1], [0, 216, 0, 64, 0, 64, 0, 27, 8, 1], [0, 0, 216, 64, 0, 0, 64, 27, 8, 1], [0, 0, 0, 64, 0, 0, 0, 27, 8, 1], [0, 0, 0, 0, 216, 64, 64, 27, 8, 1], [0, 0, 0, 0, 0, 64, 0, 27, 8, 1], [0, 0, 0, 0, 0, 0, 64, 27, 8, 1], [0, 0, 0, 0, 0, 0, 0, 27, 8, 1], [0, 0, 0, 0, 0, 0, 0, 0, 8, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, [0, 216, 0, 64, 0, 64, 0, 27, 8, 1], s, [0, 0, 0, 64, 0, 0, 0, 27, 8, 1], s, [0, 0, 0, 0, 0, 64, 0, 27, 8, 1], s, [0, 0, 0, 0, 0, 0, 0, 27, 8, 1], [0, 0, 0, 0, 0, 0, 0, 0, 8, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, [0, 0, 216, 64, 0, 0, 64, 27, 8, 1], [0, 0, 0, 64, 0, 0, 0, 27, 8, 1], s, s, [0, 0, 0, 0, 0, 0, 64, 27, 8, 1], [0, 0, 0, 0, 0, 0, 0, 27, 8, 1], [0, 0, 0, 0, 0, 0, 0, 0, 8, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, [0, 0, 0, 64, 0, 0, 0, 27, 8, 1], s, s, s, [0, 0, 0, 0, 0, 0, 0, 27, 8, 1], [0, 0, 0, 0, 0, 0, 0, 0, 8, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, [0, 0, 0, 0, 216, 64, 64, 27, 8, 1], [0, 0, 0, 0, 0, 64, 0, 27, 8, 1], [0, 0, 0, 0, 0, 0, 64, 27, 8, 1], [0, 0, 0, 0, 0, 0, 0, 27, 8, 1], [0, 0, 0, 0, 0, 0, 0, 0, 8, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, [0, 0, 0, 0, 0, 64, 0, 27, 8, 1], s, [0, 0, 0, 0, 0, 0, 0, 27, 8, 1], [0, 0, 0, 0, 0, 0, 0, 0, 8, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, s, [0, 0, 0, 0, 0, 0, 64, 27, 8, 1], [0, 0, 0, 0, 0, 0, 0, 27, 8, 1], [0, 0, 0, 0, 0, 0, 0, 0, 8, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, s, s, [0, 0, 0, 0, 0, 0, 0, 27, 8, 1], [0, 0, 0, 0, 0, 0, 0, 0, 8, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, s, s, s, [0, 0, 0, 0, 0, 0, 0, 0, 8, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, s, s, s, s, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]]

/-- The table of G_4. -/
def t4 : List (List (List ℕ)) :=
  [[[1876, 380, 380, 100, 380, 100, 100, 36, 9, 1], [0, 380, 0, 100, 0, 100, 0, 36, 9, 1], [0, 0, 380, 100, 0, 0, 100, 36, 9, 1], [0, 0, 0, 100, 0, 0, 0, 36, 9, 1], [0, 0, 0, 0, 380, 100, 100, 36, 9, 1], [0, 0, 0, 0, 0, 100, 0, 36, 9, 1], [0, 0, 0, 0, 0, 0, 100, 36, 9, 1], [0, 0, 0, 0, 0, 0, 0, 36, 9, 1], [0, 0, 0, 0, 0, 0, 0, 0, 9, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, [0, 380, 0, 100, 0, 100, 0, 36, 9, 1], s, [0, 0, 0, 100, 0, 0, 0, 36, 9, 1], s, [0, 0, 0, 0, 0, 100, 0, 36, 9, 1], s, [0, 0, 0, 0, 0, 0, 0, 36, 9, 1], [0, 0, 0, 0, 0, 0, 0, 0, 9, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, [0, 0, 380, 100, 0, 0, 100, 36, 9, 1], [0, 0, 0, 100, 0, 0, 0, 36, 9, 1], s, s, [0, 0, 0, 0, 0, 0, 100, 36, 9, 1], [0, 0, 0, 0, 0, 0, 0, 36, 9, 1], [0, 0, 0, 0, 0, 0, 0, 0, 9, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, [0, 0, 0, 100, 0, 0, 0, 36, 9, 1], s, s, s, [0, 0, 0, 0, 0, 0, 0, 36, 9, 1], [0, 0, 0, 0, 0, 0, 0, 0, 9, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, [0, 0, 0, 0, 380, 100, 100, 36, 9, 1], [0, 0, 0, 0, 0, 100, 0, 36, 9, 1], [0, 0, 0, 0, 0, 0, 100, 36, 9, 1], [0, 0, 0, 0, 0, 0, 0, 36, 9, 1], [0, 0, 0, 0, 0, 0, 0, 0, 9, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, [0, 0, 0, 0, 0, 100, 0, 36, 9, 1], s, [0, 0, 0, 0, 0, 0, 0, 36, 9, 1], [0, 0, 0, 0, 0, 0, 0, 0, 9, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, s, [0, 0, 0, 0, 0, 0, 100, 36, 9, 1], [0, 0, 0, 0, 0, 0, 0, 36, 9, 1], [0, 0, 0, 0, 0, 0, 0, 0, 9, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, s, s, [0, 0, 0, 0, 0, 0, 0, 36, 9, 1], [0, 0, 0, 0, 0, 0, 0, 0, 9, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, s, s, s, [0, 0, 0, 0, 0, 0, 0, 0, 9, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, s, s, s, s, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]]

/-- The table of G_5. -/
def t5 : List (List (List ℕ)) :=
  [[[3362, 626, 626, 146, 626, 146, 146, 46, 10, 1], [0, 626, 0, 146, 0, 146, 0, 46, 10, 1], [0, 0, 626, 146, 0, 0, 146, 46, 10, 1], [0, 0, 0, 146, 0, 0, 0, 46, 10, 1], [0, 0, 0, 0, 626, 146, 146, 46, 10, 1], [0, 0, 0, 0, 0, 146, 0, 46, 10, 1], [0, 0, 0, 0, 0, 0, 146, 46, 10, 1], [0, 0, 0, 0, 0, 0, 0, 46, 10, 1], [0, 0, 0, 0, 0, 0, 0, 0, 10, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, [0, 626, 0, 146, 0, 146, 0, 46, 10, 1], s, [0, 0, 0, 146, 0, 0, 0, 46, 10, 1], s, [0, 0, 0, 0, 0, 146, 0, 46, 10, 1], s, [0, 0, 0, 0, 0, 0, 0, 46, 10, 1], [0, 0, 0, 0, 0, 0, 0, 0, 10, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, [0, 0, 626, 146, 0, 0, 146, 46, 10, 1], [0, 0, 0, 146, 0, 0, 0, 46, 10, 1], s, s, [0, 0, 0, 0, 0, 0, 146, 46, 10, 1], [0, 0, 0, 0, 0, 0, 0, 46, 10, 1], [0, 0, 0, 0, 0, 0, 0, 0, 10, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, [0, 0, 0, 146, 0, 0, 0, 46, 10, 1], s, s, s, [0, 0, 0, 0, 0, 0, 0, 46, 10, 1], [0, 0, 0, 0, 0, 0, 0, 0, 10, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, [0, 0, 0, 0, 626, 146, 146, 46, 10, 1], [0, 0, 0, 0, 0, 146, 0, 46, 10, 1], [0, 0, 0, 0, 0, 0, 146, 46, 10, 1], [0, 0, 0, 0, 0, 0, 0, 46, 10, 1], [0, 0, 0, 0, 0, 0, 0, 0, 10, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, [0, 0, 0, 0, 0, 146, 0, 46, 10, 1], s, [0, 0, 0, 0, 0, 0, 0, 46, 10, 1], [0, 0, 0, 0, 0, 0, 0, 0, 10, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, s, [0, 0, 0, 0, 0, 0, 146, 46, 10, 1], [0, 0, 0, 0, 0, 0, 0, 46, 10, 1], [0, 0, 0, 0, 0, 0, 0, 0, 10, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, s, s, [0, 0, 0, 0, 0, 0, 0, 46, 10, 1], [0, 0, 0, 0, 0, 0, 0, 0, 10, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, s, s, s, [0, 0, 0, 0, 0, 0, 0, 0, 10, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, s, s, s, s, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]]

/-- The table of G_6. -/
def t6 : List (List (List ℕ)) :=
  [[[5735, 975, 975, 203, 975, 203, 203, 57, 11, 1], [0, 975, 0, 203, 0, 203, 0, 57, 11, 1], [0, 0, 975, 203, 0, 0, 203, 57, 11, 1], [0, 0, 0, 203, 0, 0, 0, 57, 11, 1], [0, 0, 0, 0, 975, 203, 203, 57, 11, 1], [0, 0, 0, 0, 0, 203, 0, 57, 11, 1], [0, 0, 0, 0, 0, 0, 203, 57, 11, 1], [0, 0, 0, 0, 0, 0, 0, 57, 11, 1], [0, 0, 0, 0, 0, 0, 0, 0, 11, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, [0, 975, 0, 203, 0, 203, 0, 57, 11, 1], s, [0, 0, 0, 203, 0, 0, 0, 57, 11, 1], s, [0, 0, 0, 0, 0, 203, 0, 57, 11, 1], s, [0, 0, 0, 0, 0, 0, 0, 57, 11, 1], [0, 0, 0, 0, 0, 0, 0, 0, 11, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, [0, 0, 975, 203, 0, 0, 203, 57, 11, 1], [0, 0, 0, 203, 0, 0, 0, 57, 11, 1], s, s, [0, 0, 0, 0, 0, 0, 203, 57, 11, 1], [0, 0, 0, 0, 0, 0, 0, 57, 11, 1], [0, 0, 0, 0, 0, 0, 0, 0, 11, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, [0, 0, 0, 203, 0, 0, 0, 57, 11, 1], s, s, s, [0, 0, 0, 0, 0, 0, 0, 57, 11, 1], [0, 0, 0, 0, 0, 0, 0, 0, 11, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, [0, 0, 0, 0, 975, 203, 203, 57, 11, 1], [0, 0, 0, 0, 0, 203, 0, 57, 11, 1], [0, 0, 0, 0, 0, 0, 203, 57, 11, 1], [0, 0, 0, 0, 0, 0, 0, 57, 11, 1], [0, 0, 0, 0, 0, 0, 0, 0, 11, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, [0, 0, 0, 0, 0, 203, 0, 57, 11, 1], s, [0, 0, 0, 0, 0, 0, 0, 57, 11, 1], [0, 0, 0, 0, 0, 0, 0, 0, 11, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, s, [0, 0, 0, 0, 0, 0, 203, 57, 11, 1], [0, 0, 0, 0, 0, 0, 0, 57, 11, 1], [0, 0, 0, 0, 0, 0, 0, 0, 11, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, s, s, [0, 0, 0, 0, 0, 0, 0, 57, 11, 1], [0, 0, 0, 0, 0, 0, 0, 0, 11, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, s, s, s, [0, 0, 0, 0, 0, 0, 0, 0, 11, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, s, s, s, s, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]]

/-- The table of G_7. -/
def t7 : List (List (List ℕ)) :=
  [[[9338, 1450, 1450, 272, 1450, 272, 272, 69, 12, 1], [0, 1450, 0, 272, 0, 272, 0, 69, 12, 1], [0, 0, 1450, 272, 0, 0, 272, 69, 12, 1], [0, 0, 0, 272, 0, 0, 0, 69, 12, 1], [0, 0, 0, 0, 1450, 272, 272, 69, 12, 1], [0, 0, 0, 0, 0, 272, 0, 69, 12, 1], [0, 0, 0, 0, 0, 0, 272, 69, 12, 1], [0, 0, 0, 0, 0, 0, 0, 69, 12, 1], [0, 0, 0, 0, 0, 0, 0, 0, 12, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, [0, 1450, 0, 272, 0, 272, 0, 69, 12, 1], s, [0, 0, 0, 272, 0, 0, 0, 69, 12, 1], s, [0, 0, 0, 0, 0, 272, 0, 69, 12, 1], s, [0, 0, 0, 0, 0, 0, 0, 69, 12, 1], [0, 0, 0, 0, 0, 0, 0, 0, 12, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, [0, 0, 1450, 272, 0, 0, 272, 69, 12, 1], [0, 0, 0, 272, 0, 0, 0, 69, 12, 1], s, s, [0, 0, 0, 0, 0, 0, 272, 69, 12, 1], [0, 0, 0, 0, 0, 0, 0, 69, 12, 1], [0, 0, 0, 0, 0, 0, 0, 0, 12, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, [0, 0, 0, 272, 0, 0, 0, 69, 12, 1], s, s, s, [0, 0, 0, 0, 0, 0, 0, 69, 12, 1], [0, 0, 0, 0, 0, 0, 0, 0, 12, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, [0, 0, 0, 0, 1450, 272, 272, 69, 12, 1], [0, 0, 0, 0, 0, 272, 0, 69, 12, 1], [0, 0, 0, 0, 0, 0, 272, 69, 12, 1], [0, 0, 0, 0, 0, 0, 0, 69, 12, 1], [0, 0, 0, 0, 0, 0, 0, 0, 12, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, [0, 0, 0, 0, 0, 272, 0, 69, 12, 1], s, [0, 0, 0, 0, 0, 0, 0, 69, 12, 1], [0, 0, 0, 0, 0, 0, 0, 0, 12, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, s, [0, 0, 0, 0, 0, 0, 272, 69, 12, 1], [0, 0, 0, 0, 0, 0, 0, 69, 12, 1], [0, 0, 0, 0, 0, 0, 0, 0, 12, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, s, s, [0, 0, 0, 0, 0, 0, 0, 69, 12, 1], [0, 0, 0, 0, 0, 0, 0, 0, 12, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, s, s, s, [0, 0, 0, 0, 0, 0, 0, 0, 12, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, s, s, s, s, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]]

/-- The table of G_8. -/
def t8 : List (List (List ℕ)) :=
  [[[14586, 2076, 2076, 354, 2076, 354, 354, 82, 13, 1], [0, 2076, 0, 354, 0, 354, 0, 82, 13, 1], [0, 0, 2076, 354, 0, 0, 354, 82, 13, 1], [0, 0, 0, 354, 0, 0, 0, 82, 13, 1], [0, 0, 0, 0, 2076, 354, 354, 82, 13, 1], [0, 0, 0, 0, 0, 354, 0, 82, 13, 1], [0, 0, 0, 0, 0, 0, 354, 82, 13, 1], [0, 0, 0, 0, 0, 0, 0, 82, 13, 1], [0, 0, 0, 0, 0, 0, 0, 0, 13, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, [0, 2076, 0, 354, 0, 354, 0, 82, 13, 1], s, [0, 0, 0, 354, 0, 0, 0, 82, 13, 1], s, [0, 0, 0, 0, 0, 354, 0, 82, 13, 1], s, [0, 0, 0, 0, 0, 0, 0, 82, 13, 1], [0, 0, 0, 0, 0, 0, 0, 0, 13, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, [0, 0, 2076, 354, 0, 0, 354, 82, 13, 1], [0, 0, 0, 354, 0, 0, 0, 82, 13, 1], s, s, [0, 0, 0, 0, 0, 0, 354, 82, 13, 1], [0, 0, 0, 0, 0, 0, 0, 82, 13, 1], [0, 0, 0, 0, 0, 0, 0, 0, 13, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, [0, 0, 0, 354, 0, 0, 0, 82, 13, 1], s, s, s, [0, 0, 0, 0, 0, 0, 0, 82, 13, 1], [0, 0, 0, 0, 0, 0, 0, 0, 13, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, [0, 0, 0, 0, 2076, 354, 354, 82, 13, 1], [0, 0, 0, 0, 0, 354, 0, 82, 13, 1], [0, 0, 0, 0, 0, 0, 354, 82, 13, 1], [0, 0, 0, 0, 0, 0, 0, 82, 13, 1], [0, 0, 0, 0, 0, 0, 0, 0, 13, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, [0, 0, 0, 0, 0, 354, 0, 82, 13, 1], s, [0, 0, 0, 0, 0, 0, 0, 82, 13, 1], [0, 0, 0, 0, 0, 0, 0, 0, 13, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, s, [0, 0, 0, 0, 0, 0, 354, 82, 13, 1], [0, 0, 0, 0, 0, 0, 0, 82, 13, 1], [0, 0, 0, 0, 0, 0, 0, 0, 13, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, s, s, [0, 0, 0, 0, 0, 0, 0, 82, 13, 1], [0, 0, 0, 0, 0, 0, 0, 0, 13, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, s, s, s, [0, 0, 0, 0, 0, 0, 0, 0, 13, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, s, s, s, s, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]]

/-- The table of G_9. -/
def t9 : List (List (List ℕ)) :=
  [[[21972, 2880, 2880, 450, 2880, 450, 450, 96, 14, 1], [0, 2880, 0, 450, 0, 450, 0, 96, 14, 1], [0, 0, 2880, 450, 0, 0, 450, 96, 14, 1], [0, 0, 0, 450, 0, 0, 0, 96, 14, 1], [0, 0, 0, 0, 2880, 450, 450, 96, 14, 1], [0, 0, 0, 0, 0, 450, 0, 96, 14, 1], [0, 0, 0, 0, 0, 0, 450, 96, 14, 1], [0, 0, 0, 0, 0, 0, 0, 96, 14, 1], [0, 0, 0, 0, 0, 0, 0, 0, 14, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, [0, 2880, 0, 450, 0, 450, 0, 96, 14, 1], s, [0, 0, 0, 450, 0, 0, 0, 96, 14, 1], s, [0, 0, 0, 0, 0, 450, 0, 96, 14, 1], s, [0, 0, 0, 0, 0, 0, 0, 96, 14, 1], [0, 0, 0, 0, 0, 0, 0, 0, 14, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, [0, 0, 2880, 450, 0, 0, 450, 96, 14, 1], [0, 0, 0, 450, 0, 0, 0, 96, 14, 1], s, s, [0, 0, 0, 0, 0, 0, 450, 96, 14, 1], [0, 0, 0, 0, 0, 0, 0, 96, 14, 1], [0, 0, 0, 0, 0, 0, 0, 0, 14, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, [0, 0, 0, 450, 0, 0, 0, 96, 14, 1], s, s, s, [0, 0, 0, 0, 0, 0, 0, 96, 14, 1], [0, 0, 0, 0, 0, 0, 0, 0, 14, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, [0, 0, 0, 0, 2880, 450, 450, 96, 14, 1], [0, 0, 0, 0, 0, 450, 0, 96, 14, 1], [0, 0, 0, 0, 0, 0, 450, 96, 14, 1], [0, 0, 0, 0, 0, 0, 0, 96, 14, 1], [0, 0, 0, 0, 0, 0, 0, 0, 14, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, [0, 0, 0, 0, 0, 450, 0, 96, 14, 1], s, [0, 0, 0, 0, 0, 0, 0, 96, 14, 1], [0, 0, 0, 0, 0, 0, 0, 0, 14, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, s, [0, 0, 0, 0, 0, 0, 450, 96, 14, 1], [0, 0, 0, 0, 0, 0, 0, 96, 14, 1], [0, 0, 0, 0, 0, 0, 0, 0, 14, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, s, s, [0, 0, 0, 0, 0, 0, 0, 96, 14, 1], [0, 0, 0, 0, 0, 0, 0, 0, 14, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, s, s, s, [0, 0, 0, 0, 0, 0, 0, 0, 14, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [s, s, s, s, s, s, s, s, s, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]]

lemma G1 (a b c : Fin 10) : G a b c 1 = look t1 a b c := by
  rw [G_succ]
  simp only [G_zero]
  revert a b c
  decide +kernel

lemma G2 (a b c : Fin 10) : G a b c 2 = look t2 a b c := by
  rw [G_succ]
  simp only [G1]
  revert a b c
  decide +kernel

lemma G3 (a b c : Fin 10) : G a b c 3 = look t3 a b c := by
  rw [G_succ]
  simp only [G2]
  revert a b c
  decide +kernel

lemma G4 (a b c : Fin 10) : G a b c 4 = look t4 a b c := by
  rw [G_succ]
  simp only [G3]
  revert a b c
  decide +kernel

lemma G5 (a b c : Fin 10) : G a b c 5 = look t5 a b c := by
  rw [G_succ]
  simp only [G4]
  revert a b c
  decide +kernel

lemma G6 (a b c : Fin 10) : G a b c 6 = look t6 a b c := by
  rw [G_succ]
  simp only [G5]
  revert a b c
  decide +kernel

lemma G7 (a b c : Fin 10) : G a b c 7 = look t7 a b c := by
  rw [G_succ]
  simp only [G6]
  revert a b c
  decide +kernel

lemma G8 (a b c : Fin 10) : G a b c 8 = look t8 a b c := by
  rw [G_succ]
  simp only [G7]
  revert a b c
  decide +kernel

lemma G9 (a b c : Fin 10) : G a b c 9 = look t9 a b c := by
  rw [G_succ]
  simp only [G8]
  revert a b c
  decide +kernel

/-- (E - 1)^6 G = 0 from m = 3 on, on every state. -/
theorem G_rec (m : ℕ) : ∀ a b c : Fin 10,
    (G a b c (m + 9) : ℤ) = 6 * G a b c (m + 8) - 15 * G a b c (m + 7) + 20 * G a b c (m + 6) -
      15 * G a b c (m + 5) + 6 * G a b c (m + 4) - G a b c (m + 3) := by
  induction m with
  | zero =>
    intro a b c
    rw [G9, G8, G7, G6, G5, G4, G3]
    revert a b c
    decide +kernel
  | succ m ih =>
    intro a b c
    rw [G_succ a b c (m + 9), G_succ a b c (m + 8), G_succ a b c (m + 7), G_succ a b c (m + 6),
      G_succ a b c (m + 5), G_succ a b c (m + 4), G_succ a b c (m + 3)]
    push_cast
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    split_ifs
    · exact ih _ _ _
    · simp

lemma T_vals : T 0 = 1000 ∧ T 1 = 1876 ∧ T 2 = 3362 ∧ T 3 = 5735 ∧ T 4 = 9338 ∧ T 5 = 14586 ∧ T 6 = 21972 ∧ T 7 = 32073 ∧ T 8 = 45556 := by
  unfold T
  simp only [G_zero, G1, G2, G3, G4, G5, G6, G7, G8]
  decide +kernel

/-- The order-6 recurrence of T, for all m. -/
theorem T_rec (m : ℕ) : (T (m + 6) : ℤ) = 6 * T (m + 5) - 15 * T (m + 4) + 20 * T (m + 3) - 15 * T (m + 2) +
    6 * T (m + 1) - T m := by
  rcases Nat.lt_or_ge m 3 with hm | hm
  · obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8⟩ := T_vals
    interval_cases m <;> simp only [v0, v1, v2, v3, v4, v5, v6, v7, v8] <;> norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
    unfold T
    push_cast
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_)))
    have h := G_rec k a b c
    rw [show k + 3 + 6 = k + 9 by omega, show k + 3 + 5 = k + 8 by omega, show k + 3 + 4 = k + 7 by omega,
      show k + 3 + 3 = k + 6 by omega, show k + 3 + 2 = k + 5 by omega, show k + 3 + 1 = k + 4 by omega]
    linarith

/-- Barker's recurrence, for n > 6. -/
theorem recurrence (n : ℕ) (hn : 6 < n) :
    (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
  rw [show k + 7 = (k + 6) + 1 from rfl, show k + 6 + 1 - 1 = (k + 5) + 1 by omega,
    show k + 6 + 1 - 2 = (k + 4) + 1 by omega, show k + 6 + 1 - 3 = (k + 3) + 1 by omega,
    show k + 6 + 1 - 4 = (k + 2) + 1 by omega, show k + 6 + 1 - 5 = (k + 1) + 1 by omega,
    show k + 6 + 1 - 6 = k + 1 by omega]
  simp only [a_T]
  exact T_rec k

lemma values : a 1 = 1000 ∧ a 2 = 1876 ∧ a 3 = 3362 ∧ a 4 = 5735 ∧ a 5 = 9338 ∧ a 6 = 14586 := by
  obtain ⟨v0, v1, v2, v3, v4, v5, -, -, -⟩ := T_vals
  exact ⟨by rw [a_T, v0], by rw [a_T, v1], by rw [a_T, v2], by rw [a_T, v3], by rw [a_T, v4],
    by rw [a_T, v5]⟩

/-- Barker's g.f., as A(x) (1 - x)^6 = N(x) in Z[[x]]. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 6 =
    X * (1000 - 4124 * X + 7106 * X ^ 2 - 6297 * X ^ 3 + 2838 * X ^ 4 - 517 * X ^ 5) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (1 - X) ^ 6 = A - C 6 * (A * X ^ 1) + C 15 * (A * X ^ 2) - C 20 * (A * X ^ 3) +
      C 15 * (A * X ^ 4) - C 6 * (A * X ^ 5) + A * X ^ 6 := by
    simp only [map_ofNat]; ring
  have e2 : (X * (1000 - 4124 * X + 7106 * X ^ 2 - 6297 * X ^ 3 + 2838 * X ^ 4 - 517 * X ^ 5) : ℤ⟦X⟧) =
      X ^ 1 * C 1000 - X ^ 2 * C 4124 + X ^ 3 * C 7106 - X ^ 4 * C 6297 + X ^ 5 * C 2838 -
        X ^ 6 * C 517 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  have v := values
  rcases Nat.lt_or_ge n 7 with hn | hn
  · interval_cases n <;> simp_all
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 7 := ⟨n - 7, by omega⟩
    have h := recurrence (q + 7) (by omega)
    simp only [show q + 7 - 1 = q + 6 by omega, show q + 7 - 2 = q + 5 by omega,
      show q + 7 - 3 = q + 4 by omega, show q + 7 - 4 = q + 3 by omega, show q + 7 - 5 = q + 2 by omega,
      show q + 7 - 6 = q + 1 by omega] at h ⊢
    simp only [show ¬ q + 7 = 0 by omega, show ¬ q + 6 = 0 by omega, show ¬ q + 5 = 0 by omega,
      show ¬ q + 4 = 0 by omega, show ¬ q + 3 = 0 by omega, show ¬ q + 2 = 0 by omega,
      show ¬ q + 1 = 0 by omega, show 1 ≤ q + 7 by omega, show 2 ≤ q + 7 by omega,
      show 3 ≤ q + 7 by omega, show 4 ≤ q + 7 by omega, show 5 ≤ q + 7 by omega,
      show 6 ≤ q + 7 by omega, show ¬ q + 7 = 1 by omega, show ¬ q + 7 = 2 by omega,
      show ¬ q + 7 = 3 by omega, show ¬ q + 7 = 4 by omega, show ¬ q + 7 = 5 by omega,
      show ¬ q + 7 = 6 by omega, if_true, if_false]
    rw [h]
    ring

/-- Hardin's empirical formula, for n >= 1. -/
theorem empirical (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) = 1 / 20 * n ^ 5 + 2 * n ^ 4 + 275 / 12 * n ^ 3 + 113 * n ^ 2 + 10351 / 30 * n + 517 := by
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := values
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 7 with h7 | h7
    · interval_cases n
      · rw [v1]; norm_num
      · rw [v2]; norm_num
      · rw [v3]; norm_num
      · rw [v4]; norm_num
      · rw [v5]; norm_num
      · rw [v6]; norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
      have h := recurrence (k + 7) (by omega)
      simp only [show k + 7 - 1 = k + 6 by omega, show k + 7 - 2 = k + 5 by omega,
        show k + 7 - 3 = k + 4 by omega, show k + 7 - 4 = k + 3 by omega,
        show k + 7 - 5 = k + 2 by omega, show k + 7 - 6 = k + 1 by omega] at h
      have h' : (a (k + 7) : ℚ) = 6 * a (k + 6) - 15 * a (k + 5) + 20 * a (k + 4) - 15 * a (k + 3) +
          6 * a (k + 2) - a (k + 1) := by exact_mod_cast h
      rw [h', ih (k + 6) (by omega) (by omega), ih (k + 5) (by omega) (by omega),
        ih (k + 4) (by omega) (by omega), ih (k + 3) (by omega) (by omega),
        ih (k + 2) (by omega) (by omega), ih (k + 1) (by omega) (by omega)]
      push_cast
      ring

/-- Controls: the entry's data a(1..31). -/
theorem controls : a 1 = 1000 ∧ a 2 = 1876 ∧ a 3 = 3362 ∧ a 4 = 5735 ∧ a 5 = 9338 ∧ a 6 = 14586 ∧
    a 7 = 21972 ∧ a 8 = 32073 ∧ a 9 = 45556 ∧ a 10 = 63184 ∧ a 11 = 85822 ∧ a 12 = 114443 ∧
    a 13 = 150134 ∧ a 14 = 194102 ∧ a 15 = 247680 ∧ a 16 = 312333 ∧ a 17 = 389664 ∧ a 18 = 481420 ∧
    a 19 = 589498 ∧ a 20 = 715951 ∧ a 21 = 862994 ∧ a 22 = 1033010 ∧ a 23 = 1228556 ∧
    a 24 = 1452369 ∧ a 25 = 1707372 ∧ a 26 = 1996680 ∧ a 27 = 2323606 ∧ a 28 = 2691667 ∧
    a 29 = 3104590 ∧ a 30 = 3566318 ∧ a 31 = 4081016 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [← Nat.cast_inj (R := ℚ), empirical _ (by norm_num)]
    norm_num

/-- Both of Barker's conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 6 < n →
      (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) +
        6 * a (n - 5) - a (n - 6)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 6 =
      X * (1000 - 4124 * X + 7106 * X ^ 2 - 6297 * X ^ 3 + 2838 * X ^ 4 - 517 * X ^ 5) :=
  ⟨recurrence, gf⟩

end OMA.S_oeis_a202456

theorem OMA.solution : type_of% @OMA.S_oeis_a202456.main :=
  OMA.S_oeis_a202456.conjecture
