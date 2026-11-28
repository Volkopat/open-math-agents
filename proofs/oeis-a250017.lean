import OMAStatements.S_oeis_a250017

/-!
# Proof of OEIS A250017

The transition operator `advance` on the 80-state DAG is nilpotent of index 9,
since every valid strict transition increases the number of occupied positions
among the 8 total positions. Expressing `ways q s` in the binomial basis
`∑ k < 9, q.choose k * P k s` reduces `total n` to an explicit degree-8
polynomial in `n`, from which the 9th-order difference recurrence and the
rational generating function follow directly.
-/

namespace OMA.A250017Proof

open OMA.S_oeis_a250017 PowerSeries

private def edges' (s : State) : List (State × ℕ) :=
  (List.finRange 80).filterMap fun t =>
    let w := OMA.S_oeis_a250017.multiplicity s t
    if w = 0 then none else some (t, w)

private def weighted' : List (State × ℕ) → (State → ℕ) → ℕ
  | [], _ => 0
  | (t, w) :: rest, f => w * f t + weighted' rest f

private def edgesRows : List (List (State × ℕ)) := [
  [(1, 1), (2, 1), (3, 1), (4, 1), (5, 1), (6, 1), (7, 1), (8, 1), (9, 1), (10, 1), (11, 1), (12, 1), (13, 1), (14, 1), (15, 1), (16, 4), (17, 4), (18, 4), (19, 4), (20, 4), (21, 4), (22, 4), (23, 4), (24, 4), (25, 4), (26, 4), (27, 4), (28, 4), (29, 4), (30, 4), (31, 4), (32, 6), (33, 6), (34, 6), (36, 6), (37, 6), (40, 6), (41, 6), (42, 6), (48, 4)],
  [(3, 1), (5, 1), (7, 1), (9, 1), (11, 1), (13, 1), (15, 1), (17, 4), (19, 4), (21, 4), (23, 4), (25, 4), (27, 4), (29, 4), (31, 4), (33, 6), (37, 6), (41, 6)],
  [(3, 1), (6, 1), (7, 1), (10, 1), (11, 1), (14, 1), (15, 1), (18, 4), (19, 4), (22, 4), (23, 4), (26, 4), (27, 4), (30, 4), (31, 4), (34, 6), (42, 6)],
  [(7, 1), (11, 1), (15, 1), (19, 4), (23, 4), (27, 4), (31, 4)],
  [(5, 1), (6, 1), (7, 1), (12, 1), (13, 1), (14, 1), (15, 1), (20, 4), (21, 4), (22, 4), (23, 4), (28, 4), (29, 4), (30, 4), (31, 4), (36, 6), (37, 6)],
  [(7, 1), (13, 1), (15, 1), (21, 4), (23, 4), (29, 4), (31, 4), (37, 6)],
  [(7, 1), (14, 1), (15, 1), (22, 4), (23, 4), (30, 4), (31, 4)],
  [(15, 1), (23, 4), (31, 4)],
  [(9, 1), (10, 1), (11, 1), (12, 1), (13, 1), (14, 1), (15, 1), (24, 4), (25, 4), (26, 4), (27, 4), (28, 4), (29, 4), (30, 4), (31, 4), (40, 6), (41, 6), (42, 6)],
  [(11, 1), (13, 1), (15, 1), (25, 4), (27, 4), (29, 4), (31, 4), (41, 6)],
  [(11, 1), (14, 1), (15, 1), (26, 4), (27, 4), (30, 4), (31, 4), (42, 6)],
  [(15, 1), (27, 4), (31, 4)],
  [(13, 1), (14, 1), (15, 1), (28, 4), (29, 4), (30, 4), (31, 4)],
  [(15, 1), (29, 4), (31, 4)],
  [(15, 1), (30, 4), (31, 4)],
  [(31, 4)],
  [(17, 1), (18, 1), (19, 1), (20, 1), (21, 1), (22, 1), (23, 1), (24, 1), (25, 1), (26, 1), (27, 1), (28, 1), (29, 1), (30, 1), (31, 1), (32, 3), (33, 3), (34, 3), (36, 3), (37, 3), (40, 3), (41, 3), (42, 3), (48, 3)],
  [(19, 1), (21, 1), (23, 1), (25, 1), (27, 1), (29, 1), (31, 1), (33, 3), (37, 3), (41, 3)],
  [(19, 1), (22, 1), (23, 1), (26, 1), (27, 1), (30, 1), (31, 1), (34, 3), (42, 3)],
  [(23, 1), (27, 1), (31, 1), (35, 3), (43, 3)],
  [(21, 1), (22, 1), (23, 1), (28, 1), (29, 1), (30, 1), (31, 1), (36, 3), (37, 3)],
  [(23, 1), (29, 1), (31, 1), (37, 3)],
  [(23, 1), (30, 1), (31, 1), (38, 3)],
  [(31, 1), (39, 3)],
  [(25, 1), (26, 1), (27, 1), (28, 1), (29, 1), (30, 1), (31, 1), (40, 3), (41, 3), (42, 3)],
  [(27, 1), (29, 1), (31, 1), (41, 3)],
  [(27, 1), (30, 1), (31, 1), (42, 3)],
  [(31, 1), (43, 3)],
  [(29, 1), (30, 1), (31, 1), (44, 3), (45, 3)],
  [(31, 1), (45, 3)],
  [(31, 1), (46, 3)],
  [(47, 3), (63, 3), (79, 1)],
  [(33, 1), (34, 1), (36, 1), (37, 1), (40, 1), (41, 1), (42, 1), (48, 2)],
  [(35, 1), (37, 1), (41, 1), (43, 1), (49, 2)],
  [(35, 1), (38, 1), (39, 1), (42, 1), (43, 1), (50, 2), (51, 2)],
  [(39, 1), (43, 1), (51, 2)],
  [(37, 1), (38, 1), (44, 1), (45, 1), (46, 1), (52, 2), (60, 2)],
  [(39, 1), (45, 1), (47, 1), (53, 2), (55, 2), (61, 2), (63, 2), (69, 1), (71, 1), (77, 1), (79, 1)],
  [(39, 1), (46, 1), (47, 1), (54, 2), (55, 2), (62, 2), (63, 2), (70, 1), (71, 1), (78, 1), (79, 1)],
  [(47, 1), (55, 2), (63, 2), (71, 1), (79, 1)],
  [(41, 1), (42, 1), (44, 1), (45, 1), (56, 2)],
  [(43, 1), (45, 1), (57, 2)],
  [(43, 1), (46, 1), (47, 1), (58, 2), (59, 2), (62, 2), (63, 2), (74, 1), (75, 1), (78, 1), (79, 1)],
  [(47, 1), (59, 2), (63, 2), (75, 1), (79, 1)],
  [(45, 1), (46, 1), (60, 2)],
  [(47, 1), (61, 2), (63, 2), (77, 1), (79, 1)],
  [(47, 1), (62, 2), (63, 2), (78, 1), (79, 1)],
  [(63, 2), (79, 1)],
  [(49, 1), (50, 1), (51, 1), (52, 1), (53, 1), (54, 1), (55, 1), (56, 1), (57, 1), (58, 1), (59, 1), (60, 1), (61, 1), (62, 1), (63, 1), (64, 1), (65, 1), (66, 1), (67, 1), (68, 1), (69, 1), (70, 1), (71, 1), (72, 1), (73, 1), (74, 1), (75, 1), (76, 1), (77, 1), (78, 1), (79, 1)],
  [(51, 1), (53, 1), (55, 1), (57, 1), (59, 1), (61, 1), (63, 1), (65, 1), (67, 1), (69, 1), (71, 1), (73, 1), (75, 1), (77, 1), (79, 1)],
  [(51, 1), (54, 1), (55, 1), (58, 1), (59, 1), (62, 1), (63, 1), (66, 1), (67, 1), (70, 1), (71, 1), (74, 1), (75, 1), (78, 1), (79, 1)],
  [(55, 1), (59, 1), (63, 1), (67, 1), (71, 1), (75, 1), (79, 1)],
  [(53, 1), (54, 1), (55, 1), (60, 1), (61, 1), (62, 1), (63, 1), (68, 1), (69, 1), (70, 1), (71, 1), (76, 1), (77, 1), (78, 1), (79, 1)],
  [(55, 1), (61, 1), (63, 1), (69, 1), (71, 1), (77, 1), (79, 1)],
  [(55, 1), (62, 1), (63, 1), (70, 1), (71, 1), (78, 1), (79, 1)],
  [(63, 1), (71, 1), (79, 1)],
  [(57, 1), (58, 1), (59, 1), (60, 1), (61, 1), (62, 1), (63, 1), (72, 1), (73, 1), (74, 1), (75, 1), (76, 1), (77, 1), (78, 1), (79, 1)],
  [(59, 1), (61, 1), (63, 1), (73, 1), (75, 1), (77, 1), (79, 1)],
  [(59, 1), (62, 1), (63, 1), (74, 1), (75, 1), (78, 1), (79, 1)],
  [(63, 1), (75, 1), (79, 1)],
  [(61, 1), (62, 1), (63, 1), (76, 1), (77, 1), (78, 1), (79, 1)],
  [(63, 1), (77, 1), (79, 1)],
  [(63, 1), (78, 1), (79, 1)],
  [(79, 1)],
  [(65, 1), (66, 1), (67, 1), (68, 1), (69, 1), (70, 1), (71, 1), (72, 1), (73, 1), (74, 1), (75, 1), (76, 1), (77, 1), (78, 1), (79, 1)],
  [(67, 1), (69, 1), (71, 1), (73, 1), (75, 1), (77, 1), (79, 1)],
  [(67, 1), (70, 1), (71, 1), (74, 1), (75, 1), (78, 1), (79, 1)],
  [(71, 1), (75, 1), (79, 1)],
  [(69, 1), (70, 1), (71, 1), (76, 1), (77, 1), (78, 1), (79, 1)],
  [(71, 1), (77, 1), (79, 1)],
  [(71, 1), (78, 1), (79, 1)],
  [(79, 1)],
  [(73, 1), (74, 1), (75, 1), (76, 1), (77, 1), (78, 1), (79, 1)],
  [(75, 1), (77, 1), (79, 1)],
  [(75, 1), (78, 1), (79, 1)],
  [(79, 1)],
  [(77, 1), (78, 1), (79, 1)],
  [(79, 1)],
  [(79, 1)],
  []
]

private def edgesTable (s : State) : List (State × ℕ) :=
  edgesRows.getD s.val []

private lemma edges'_eq : ∀ s : State, edges' s = edgesTable s := by decide

private def advance' (f : State → ℕ) (s : State) : ℕ :=
  weighted' (edgesTable s) f

private lemma ways_succ_eq_aux
    (e : State → List (State × ℕ))
    (w : List (State × ℕ) → (State → ℕ) → ℕ)
    (hw_nil : ∀ f, w [] f = 0)
    (hw_cons : ∀ t m rest f, w ((t, m) :: rest) f = m * f t + w rest f)
    (he : ∀ s, e s = edges' s)
    (hstep : ∀ q s, ways (q + 1) s = ways q s + w (e s) (ways q))
    (q : ℕ) (s : State) :
    ways (q + 1) s = ways q s + advance' (ways q) s := by
  have hw : ∀ l f, w l f = weighted' l f := by
    intro l f
    induction l with
    | nil => exact hw_nil f
    | cons p rest ih =>
      rcases p with ⟨t, m⟩
      rw [hw_cons, weighted', ih]
  rw [hstep, he, edges'_eq, hw]
  rfl

private lemma ways_succ_eq (q : ℕ) (s : State) :
    ways (q + 1) s = ways q s + advance' (ways q) s :=
  ways_succ_eq_aux _ _ (fun _ => rfl) (fun _ _ _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) q s

private lemma weighted'_add (l : List (State × ℕ)) (f g : State → ℕ) :
    weighted' l (fun t => f t + g t) = weighted' l f + weighted' l g := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨t, w⟩
    simp only [weighted', ih]
    ring

private lemma weighted'_mul (l : List (State × ℕ)) (c : ℕ) (f : State → ℕ) :
    weighted' l (fun t => c * f t) = c * weighted' l f := by
  induction l with
  | nil => simp [weighted']
  | cons p rest ih =>
    rcases p with ⟨t, w⟩
    simp only [weighted', ih]
    ring

private lemma weighted'_zero (l : List (State × ℕ)) :
    weighted' l (fun _ => 0) = 0 := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨t, w⟩
    simp [weighted', ih]

private lemma advance'_sum (n : ℕ) (c : ℕ → ℕ) (F : ℕ → State → ℕ) (s : State) :
    advance' (fun t => ∑ k ∈ Finset.range n, c k * F k t) s =
      ∑ k ∈ Finset.range n, c k * advance' (F k) s := by
  induction n with
  | zero =>
    simp [advance', weighted'_zero]
  | succ n ih =>
    simp_rw [Finset.sum_range_succ]
    rw [advance', weighted'_add, weighted'_mul, ← advance', ← advance', ih]

private def pRows : List (List ℕ) := [
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0],
  [20, 10, 10, 4, 10, 10, 4, 4, 10, 4, 10, 4, 4, 4, 4, 4, 10, 4, 4, 4, 4, 4, 4, 4, 4, 1, 4, 4, 4, 4, 4, 6, 4, 4, 8, 4, 8, 14, 14, 6, 4, 4, 14, 6, 4, 6, 6, 2, 30, 14, 14, 6, 14, 6, 6, 2, 14, 6, 6, 2, 6, 2, 2, 0, 14, 6, 6, 2, 6, 2, 2, 0, 6, 2, 2, 0, 2, 0, 0, 0],
  [852, 290, 302, 84, 302, 168, 84, 44, 290, 96, 168, 44, 84, 44, 44, 24, 329, 93, 96, 44, 96, 56, 56, 24, 93, 26, 56, 24, 44, 24, 24, 6, 116, 56, 84, 24, 84, 36, 36, 6, 56, 24, 36, 6, 24, 6, 6, 0, 150, 36, 36, 6, 36, 6, 6, 0, 36, 6, 6, 0, 6, 0, 0, 0, 36, 6, 6, 0, 6, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0],
  [9984, 2388, 2532, 504, 2532, 768, 552, 144, 2388, 576, 768, 144, 504, 144, 144, 24, 2688, 552, 594, 144, 594, 162, 162, 24, 552, 126, 162, 24, 144, 24, 24, 0, 676, 162, 192, 24, 192, 24, 24, 0, 162, 24, 24, 0, 24, 0, 0, 0, 240, 24, 24, 0, 24, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [47712, 7788, 8112, 1080, 8112, 1296, 1152, 120, 7788, 1152, 1296, 120, 1080, 120, 120, 0, 8376, 1134, 1188, 120, 1188, 120, 120, 0, 1134, 120, 120, 0, 120, 0, 0, 0, 1260, 120, 120, 0, 120, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [105216, 10584, 10800, 720, 10800, 720, 720, 0, 10584, 720, 720, 0, 720, 0, 0, 0, 10944, 720, 720, 0, 720, 0, 0, 0, 720, 0, 0, 0, 0, 0, 0, 0, 720, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [106704, 5040, 5040, 0, 5040, 0, 0, 0, 5040, 0, 0, 0, 0, 0, 0, 0, 5040, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [40320, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
]

private def pVal (k : ℕ) (s : State) : ℕ :=
  (pRows.getD k []).getD s.val 0

private lemma pVal_zero : ∀ s : State, pVal 0 s = ways 0 s := by decide

private lemma pVal_step :
    ∀ k : Fin 9, ∀ s : State, advance' (pVal k.val) s = pVal (k.val + 1) s := by decide

private lemma pVal_nine (s : State) : pVal 9 s = 0 := rfl

private lemma ways_eq (q : ℕ) (s : State) :
    ways q s = ∑ k ∈ Finset.range 9, q.choose k * pVal k s := by
  induction q generalizing s with
  | zero =>
    rw [Finset.sum_range_succ', Nat.choose_zero_right, one_mul]
    have hrest : ∑ k ∈ Finset.range 8, Nat.choose 0 (k + 1) * pVal (k + 1) s = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      simp
    rw [hrest, zero_add, pVal_zero]
  | succ q ih =>
    rw [ways_succ_eq]
    have hfun : ways q = fun t => ∑ k ∈ Finset.range 9, q.choose k * pVal k t := funext ih
    rw [hfun, advance'_sum]
    dsimp only
    have hadv : ∀ k ∈ Finset.range 9,
        q.choose k * advance' (pVal k) s = q.choose k * pVal (k + 1) s := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [pVal_step ⟨k, hk⟩ s]
    rw [Finset.sum_congr rfl hadv]
    rw [Finset.sum_range_succ' (fun k => q.choose k * pVal k s) 8]
    rw [Finset.sum_range_succ (fun k => q.choose k * pVal (k + 1) s) 8]
    rw [pVal_nine, mul_zero, add_zero]
    rw [Finset.sum_range_succ' (fun k => (q + 1).choose k * pVal k s) 8]
    simp only [Nat.choose_zero_right, one_mul]
    rw [add_right_comm, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [Nat.choose_succ_succ]
    ring

private lemma cast_descFactorial (m k : ℕ) :
    (m.descFactorial k : ℚ) = ∏ i ∈ Finset.range k, ((m : ℚ) - i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.descFactorial_succ, Finset.prod_range_succ, Nat.cast_mul, ih]
    by_cases h : k ≤ m
    · rw [Nat.cast_sub h]
      ring
    · have hlt : m < k := by omega
      have hz : m.descFactorial k = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr hlt
      have hp : ∏ i ∈ Finset.range k, ((m : ℚ) - i) = 0 := by
        rw [← ih, hz, Nat.cast_zero]
      rw [hp, mul_zero, zero_mul]

private lemma cast_choose (m k : ℕ) :
    (m.choose k : ℚ) = (∏ i ∈ Finset.range k, ((m : ℚ) - i)) / (k.factorial : ℚ) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose m k
  have hq : (m.descFactorial k : ℚ) = (k.factorial : ℚ) * (m.choose k : ℚ) := by
    exact_mod_cast h
  have hf : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  rw [← cast_descFactorial, hq, mul_div_cancel_left₀ _ hf]

private lemma total_poly (n : ℕ) :
    total n = (n : ℚ) ^ 8 + 41 / 35 * (n : ℚ) ^ 7 + 56 / 15 * (n : ℚ) ^ 6 +
      22 / 5 * (n : ℚ) ^ 5 + 19 / 3 * (n : ℚ) ^ 4 + 17 / 5 * (n : ℚ) ^ 3 -
      16 / 15 * (n : ℚ) ^ 2 + 36 / 35 * (n : ℚ) := by
  unfold total
  rw [ways_eq]
  push_cast
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have hp : pVal 0 0 = 0 ∧ pVal 1 0 = 0 ∧ pVal 2 0 = 20 ∧ pVal 3 0 = 852 ∧
      pVal 4 0 = 9984 ∧ pVal 5 0 = 47712 ∧ pVal 6 0 = 105216 ∧ pVal 7 0 = 106704 ∧
      pVal 8 0 = 40320 := by decide
  rw [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1,
    hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2]
  simp only [cast_choose, Finset.prod_range_succ, Finset.prod_range_zero, Nat.factorial]
  push_cast
  ring

private lemma total_rec (n : ℕ) :
    total (n + 9) = 9 * total (n + 8) - 36 * total (n + 7) + 84 * total (n + 6) -
      126 * total (n + 5) + 126 * total (n + 4) - 84 * total (n + 3) +
      36 * total (n + 2) - 9 * total (n + 1) + total n := by
  simp only [total_poly]
  push_cast
  ring

private lemma total_gf :
    (1 - X) ^ 9 * mk total =
      (4 * X * (5 + 183 * X + 1506 * X ^ 2 + 3974 * X ^ 3 + 3441 * X ^ 4 +
        903 * X ^ 5 + 68 * X ^ 6) : PowerSeries ℚ) := by
  have hL : (1 - X : PowerSeries ℚ) ^ 9 * mk total =
      mk total - C 9 * (X ^ 1 * mk total) + C 36 * (X ^ 2 * mk total) -
      C 84 * (X ^ 3 * mk total) + C 126 * (X ^ 4 * mk total) -
      C 126 * (X ^ 5 * mk total) + C 84 * (X ^ 6 * mk total) -
      C 36 * (X ^ 7 * mk total) + C 9 * (X ^ 8 * mk total) -
      X ^ 9 * mk total := by
    simp only [map_ofNat]
    ring
  have hR : (4 * X * (5 + 183 * X + 1506 * X ^ 2 + 3974 * X ^ 3 + 3441 * X ^ 4 +
      903 * X ^ 5 + 68 * X ^ 6) : PowerSeries ℚ) =
      C 20 * X ^ 1 + C 732 * X ^ 2 + C 6024 * X ^ 3 + C 15896 * X ^ 4 +
      C 13764 * X ^ 5 + C 3612 * X ^ 6 + C 272 * X ^ 7 := by
    simp only [map_ofNat]
    ring
  rw [hL, hR]
  ext m
  simp only [map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_X_pow, PowerSeries.coeff_mk]
  by_cases hm : m < 9
  · interval_cases m <;> simp [total_poly] <;> norm_num
  · obtain ⟨n, rfl⟩ : ∃ n, m = n + 9 := ⟨m - 9, by omega⟩
    have h1 : 1 ≤ n + 9 := by omega
    have h2 : 2 ≤ n + 9 := by omega
    have h3 : 3 ≤ n + 9 := by omega
    have h4 : 4 ≤ n + 9 := by omega
    have h5 : 5 ≤ n + 9 := by omega
    have h6 : 6 ≤ n + 9 := by omega
    have h7 : 7 ≤ n + 9 := by omega
    have h8 : 8 ≤ n + 9 := by omega
    have h9 : 9 ≤ n + 9 := by omega
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, ↓reduceIte]
    have hn1 : n + 9 ≠ 1 := by omega
    have hn2 : n + 9 ≠ 2 := by omega
    have hn3 : n + 9 ≠ 3 := by omega
    have hn4 : n + 9 ≠ 4 := by omega
    have hn5 : n + 9 ≠ 5 := by omega
    have hn6 : n + 9 ≠ 6 := by omega
    have hn7 : n + 9 ≠ 7 := by omega
    simp only [hn1, hn2, hn3, hn4, hn5, hn6, hn7, ↓reduceIte, mul_zero, add_zero]
    rw [show n + 9 - 1 = n + 8 by omega, show n + 9 - 2 = n + 7 by omega,
      show n + 9 - 3 = n + 6 by omega, show n + 9 - 4 = n + 5 by omega,
      show n + 9 - 5 = n + 4 by omega, show n + 9 - 6 = n + 3 by omega,
      show n + 9 - 7 = n + 2 by omega, show n + 9 - 8 = n + 1 by omega,
      show n + 9 - 9 = n by omega]
    linarith [total_rec n]

end OMA.A250017Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a250017.main :=
  ⟨OMA.A250017Proof.total_poly, OMA.A250017Proof.total_rec, OMA.A250017Proof.total_gf⟩
