import OMAStatements.S_oeis_a275138

namespace OMA.P_oeis_a275138

open OMA.S_oeis_a275138 PowerSeries Finset

/-- A row of the array. -/
abbrev R := Fin 4 → Fin 3

/-- The first two columns of a row. -/
abbrev Q := Fin 2 → Fin 3

/-- The first two columns of a row. -/
def proj (c : R) : Q := fun j => c ⟨j, by omega⟩

/-- The element of a row at an integer column, or `none` outside. -/
def col (r : R) (c : ℤ) : Option (Fin 3) :=
  if h : 0 ≤ c ∧ c < 4 then some (r ⟨c.toNat, by omega⟩) else none

/-- The element of a two-column row at an integer column, or `none` outside. -/
def colQ (r : Q) (c : ℤ) : Option (Fin 3) :=
  if h : 0 ≤ c ∧ c < 2 then some (r ⟨c.toNat, by omega⟩) else none

/-- The row of an array at an integer index, or `none` outside. -/
def rowAt {m : ℕ} (A : Fin m → R) (r : ℤ) : Option R :=
  if h : 0 ≤ r ∧ r < m then some (A ⟨r.toNat, by omega⟩) else none

/-- The row of `y` at a natural index, or `none` outside. -/
def rowN {m : ℕ} (y : Fin m → R) (k : ℕ) : Option R := if h : k < m then some (y ⟨k, h⟩) else none

lemma entry_eq {m : ℕ} (A : Fin m → R) (r c : ℤ) :
    entry A r c = (rowAt A r).bind (col · c) := by
  unfold entry rowAt col
  by_cases h1 : 0 ≤ r ∧ r < m
  · by_cases h2 : 0 ≤ c ∧ c < 4
    · rw [dif_pos ⟨h1.1, h1.2, h2⟩, dif_pos h1, Option.bind_some, dif_pos h2]
    · rw [dif_neg (by tauto), dif_pos h1, Option.bind_some, dif_neg h2]
  · rw [dif_neg (by tauto), dif_neg h1, Option.bind_none]

lemma rowAt_self {m : ℕ} (A : Fin m → R) (i : Fin m) : rowAt A ((i : ℤ) + 0) = some (A i) := by
  unfold rowAt
  rw [dif_pos (by omega)]
  congr 2

lemma rowAt_minus {m : ℕ} (A : Fin m → R) (i : Fin m) (d : ℕ) :
    rowAt A ((i : ℤ) + -(d : ℤ)) = if (i : ℕ) < d then none else rowN A (i - d) := by
  unfold rowAt rowN
  by_cases h : (i : ℕ) < d
  · rw [if_pos h, dif_neg (by omega)]
  · rw [if_neg h, dif_pos (by omega), dif_pos (by omega)]
    congr 2
    ext
    simp
    omega

lemma col_proj (r : R) (j : Fin 4) : col r ((j : ℤ) + -2) = colQ (proj r) ((j : ℤ) + -2) := by
  unfold col colQ proj
  split_ifs with h1 h2 h2
  · rfl
  · omega
  · omega
  · rfl

/-- The condition on a row `c`, given the first two columns of the two rows above it. -/
def rowCond (q2 q1 : Option Q) (c : R) : Prop :=
  ∀ j : Fin 4, q2.bind (colQ · ((j : ℤ) + -2)) ≠ some (c j) ∧
    q1.bind (colQ · ((j : ℤ) + -2)) ≠ some (c j) ∧ col c ((j : ℤ) + -1) ≠ some (c j)

instance (q2 q1 : Option Q) : DecidablePred (rowCond q2 q1) := fun c => by
  unfold rowCond; infer_instance

lemma bind_map_proj (o : Option R) (j : Fin 4) :
    (o.map proj).bind (colQ · ((j : ℤ) + -2)) = o.bind (col · ((j : ℤ) + -2)) := by
  cases o <;> simp [col_proj]

/-- The first two columns of the row `k` rows above row `i` (`p` for the virtual rows). -/
def above (q2 q1 : Option Q) {m : ℕ} (y : Fin m → R) (i : Fin m) (k : ℕ) : Option Q :=
  if (i : ℕ) + 2 < k + 2 then (if (i : ℕ) + 2 = k then q2 else if (i : ℕ) + 1 = k then q1 else none)
  else (rowN y (i - k)).map proj

/-- The row conditions for an array whose two virtual rows above are `q2`, `q1`. -/
def VR (q2 q1 : Option Q) {m : ℕ} (y : Fin m → R) : Prop :=
  ∀ i : Fin m, rowCond (if (i : ℕ) = 0 then q2 else if (i : ℕ) = 1 then q1
      else (rowN y (i - 2)).map proj)
    (if (i : ℕ) = 0 then q1 else (rowN y (i - 1)).map proj) (y i)

instance (q2 q1 : Option Q) {m : ℕ} : DecidablePred (VR q2 q1 (m := m)) := fun y => by
  unfold VR; infer_instance

lemma cond_iff {n : ℕ} (A : Fin n → R) : NoEqualAtOffsets A ↔ VR none none A := by
  unfold NoEqualAtOffsets VR rowCond
  apply forall_congr'; intro i
  have h2 := rowAt_minus A i 2
  have h1 := rowAt_minus A i 1
  simp only [Nat.cast_ofNat, Nat.cast_one] at h2 h1
  have e2 : (if (i : ℕ) = 0 then (none : Option Q) else if (i : ℕ) = 1 then none
      else (rowN A (i - 2)).map proj) = (rowAt A ((i : ℤ) + -2)).map proj := by
    rw [h2]; split_ifs <;> first | rfl | omega
  have e1 : (if (i : ℕ) = 0 then (none : Option Q) else (rowN A (i - 1)).map proj) =
      (rowAt A ((i : ℤ) + -1)).map proj := by
    rw [h1]; split_ifs <;> first | rfl | omega
  rw [e2, e1]
  apply forall_congr'; intro j
  simp only [offsets, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    bind_map_proj, entry_eq]
  rw [rowAt_self]
  simp only [Option.bind_some]

lemma rowN_cons {m : ℕ} (c : R) (x : Fin m → R) (k : ℕ) :
    rowN (Fin.cons c x : Fin (m + 1) → R) k = if k = 0 then some c else rowN x (k - 1) := by
  unfold rowN
  by_cases h0 : k = 0
  · subst h0
    rw [if_pos rfl, dif_pos (by omega)]
    rfl
  · rw [if_neg h0]
    by_cases hk : k < m + 1
    · rw [dif_pos hk, dif_pos (by omega),
        show (⟨k, hk⟩ : Fin (m + 1)) = Fin.succ ⟨k - 1, by omega⟩ by ext; simp; omega,
        Fin.cons_succ]
    · rw [dif_neg hk, dif_neg (by omega)]

lemma VR_cons (q2 q1 : Option Q) {m : ℕ} (c : R) (x : Fin m → R) :
    VR q2 q1 (Fin.cons c x : Fin (m + 1) → R) ↔ rowCond q2 q1 c ∧ VR q1 (some (proj c)) x := by
  unfold VR
  rw [Fin.forall_fin_succ]
  apply and_congr
  · simp
  · apply forall_congr'; intro i
    simp only [Fin.val_succ, Fin.cons_succ, rowN_cons,
      show (i : ℕ) + 1 - 2 = (i : ℕ) - 1 by omega, show (i : ℕ) + 1 - 1 = (i : ℕ) by omega,
      Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, Nat.add_eq_right]
    have e2 : (if (i : ℕ) = 0 then q1
        else Option.map proj (if (i : ℕ) - 1 = 0 then some c else rowN x ((i : ℕ) - 1 - 1))) =
        (if (i : ℕ) = 0 then q1 else if (i : ℕ) = 1 then some (proj c)
        else Option.map proj (rowN x ((i : ℕ) - 2))) := by
      rw [show (i : ℕ) - 1 - 1 = (i : ℕ) - 2 by omega]
      split_ifs <;> first | rfl | omega
    have e1 : Option.map proj (if (i : ℕ) = 0 then some c else rowN x ((i : ℕ) - 1)) =
        (if (i : ℕ) = 0 then some (proj c) else Option.map proj (rowN x ((i : ℕ) - 1))) := by
      split_ifs <;> rfl
    rw [e2, e1]

/-- The new-values condition inside one row, given the set `S` of values in earlier rows. -/
def rowOK (S : Finset (Fin 3)) (c : R) : Prop :=
  ∀ (j : Fin 4) (w : Fin 3), w < c j → w ∈ S ∨ ∃ j' : Fin 4, j' < j ∧ c j' = w

instance (S : Finset (Fin 3)) : DecidablePred (rowOK S) := fun c => by
  unfold rowOK; infer_instance

/-- The values of a row. -/
def vals (c : R) : Finset (Fin 3) := univ.image c

/-- The new-values condition for an array whose earlier rows have value set `S`. -/
def NVS {m : ℕ} (S : Finset (Fin 3)) (y : Fin m → R) : Prop :=
  ∀ (i : Fin m) (j : Fin 4) (w : Fin 3), w < y i j →
    w ∈ S ∨ ∃ (i' : Fin m) (j' : Fin 4), 4 * (i' : ℕ) + j' < 4 * (i : ℕ) + j ∧ y i' j' = w

instance {m : ℕ} (S : Finset (Fin 3)) : DecidablePred (NVS (m := m) S) := fun y => by
  unfold NVS; infer_instance

lemma NVS_cons {m : ℕ} (S : Finset (Fin 3)) (c : R) (x : Fin m → R) :
    NVS S (Fin.cons c x : Fin (m + 1) → R) ↔ rowOK S c ∧ NVS (S ∪ vals c) x := by
  unfold NVS rowOK
  rw [Fin.forall_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ]
  apply and_congr
  · apply forall_congr'; intro j; apply forall_congr'; intro w; apply imp_congr_right; intro _
    apply or_congr_right
    constructor
    · rintro ⟨i', j', h1, h2⟩
      refine Fin.cases (motive := fun i' => 4 * (i' : ℕ) + j' < 4 * 0 + j →
        (Fin.cons c x : Fin (m + 1) → R) i' j' = w → ∃ j' : Fin 4, j' < j ∧ c j' = w)
        ?_ ?_ i' h1 h2
      · intro h1 h2
        exact ⟨j', by simp at h1; exact h1, by simpa using h2⟩
      · intro i'' h1 _
        simp at h1; omega
    · rintro ⟨j', h1, h2⟩
      exact ⟨0, j', by simp; exact h1, by simpa using h2⟩
  · apply forall_congr'; intro i; apply forall_congr'; intro j; apply forall_congr'; intro w
    apply imp_congr_right; intro _
    constructor
    · rintro (h | ⟨i', j', h1, h2⟩)
      · exact Or.inl (mem_union_left _ h)
      · refine Fin.cases (motive := fun i' => 4 * (i' : ℕ) + j' < 4 * ((i : ℕ) + 1) + j →
          (Fin.cons c x : Fin (m + 1) → R) i' j' = w →
          w ∈ S ∪ vals c ∨ ∃ (i' : Fin m) (j' : Fin 4), 4 * (i' : ℕ) + j' < 4 * (i : ℕ) + j ∧
            x i' j' = w) ?_ ?_ i' h1 h2
        · intro _ h2
          exact Or.inl (mem_union_right _ (mem_image.2 ⟨j', mem_univ _, by simpa using h2⟩))
        · intro i'' h1 h2
          exact Or.inr ⟨i'', j', by simp at h1; omega, by simpa using h2⟩
    · rintro (h | ⟨i', j', h1, h2⟩)
      · rcases mem_union.1 h with h | h
        · exact Or.inl h
        · obtain ⟨j', -, hj⟩ := mem_image.1 h
          exact Or.inr ⟨0, j', by simp; omega, by simpa using hj⟩
      · exact Or.inr ⟨i'.succ, j', by simp; omega, by simpa using h2⟩

/-- Completions of length `n` after earlier rows with value set `S` and the first two columns
`q2`, `q1` of the last two rows. -/
def F (S : Finset (Fin 3)) (q2 q1 : Option Q) (n : ℕ) : ℕ :=
  (univ.filter fun x : Fin n → R => NVS S x ∧ VR q2 q1 x).card

lemma card_cons' {n : ℕ} (P : (Fin (n + 1) → R) → Prop) [DecidablePred P] :
    (univ.filter P).card = ∑ d : R, (univ.filter fun x : Fin n → R => P (Fin.cons d x)).card := by
  simp only [card_filter]
  rw [← (Fin.consEquiv fun _ => R).sum_comp, Fintype.sum_prod_type]
  rfl

lemma F_zero (S : Finset (Fin 3)) (q2 q1 : Option Q) : F S q2 q1 0 = 1 := by
  unfold F
  rw [card_filter, Fintype.sum_unique]
  simp [NVS, VR]

lemma F_succ (S : Finset (Fin 3)) (q2 q1 : Option Q) (n : ℕ) :
    F S q2 q1 (n + 1) = ∑ c : R, if rowOK S c ∧ rowCond q2 q1 c then
      F (S ∪ vals c) q1 (some (proj c)) n else 0 := by
  unfold F
  rw [card_cons']
  refine sum_congr rfl fun c _ => ?_
  simp only [NVS_cons, VR_cons]
  split_ifs with h
  · congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and]
    tauto
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro x _ hx
    exact h ⟨hx.1.1, hx.2.1⟩

lemma a_eq (n : ℕ) : a n = F ∅ none none n := by
  unfold a F
  congr 1
  ext A
  simp only [mem_filter, mem_univ, true_and, cond_iff]
  have : NewValuesInOrder A ↔ NVS ∅ A := by
    simp [NewValuesInOrder, NVS]
  rw [this, and_comm]

/-- The value set `{0, ..., k - 1}`. -/
def rangeF (k : Fin 4) : Finset (Fin 3) := univ.filter fun v => (v : ℕ) < k

/-- The number of values seen after a row `c`, when `k` values were seen before. -/
def nk (k : Fin 4) (c : R) : Fin 4 :=
  ⟨max (k : ℕ) (max ((c 0 : ℕ) + 1) (max ((c 1 : ℕ) + 1) (max ((c 2 : ℕ) + 1) ((c 3 : ℕ) + 1)))),
    by omega⟩

lemma seen_check : ∀ (k : Fin 4) (c : R), rowOK (rangeF k) c →
    rangeF k ∪ vals c = rangeF (nk k c) := by
  decide +kernel

/-- A code for the first two columns of a row. -/
def codeQ : Option Q → ℕ
  | none => 0
  | some q => (q 0 : ℕ) + 3 * q 1 + 1

/-- The class table of the states. -/
def tbl : List (List (List (Fin 50))) := [[[14, 12, 6, 46, 0, 45, 9, 49, 5, 12], [0, 12, 22, 38, 38, 38, 38, 8, 1, 38], [4, 12, 6, 46, 38, 1, 9, 8, 45, 12], [42, 38, 2, 46, 38, 1, 9, 38, 1, 12], [0, 38, 38, 38, 0, 1, 38, 8, 1, 38], [42, 38, 22, 12, 0, 45, 9, 8, 1, 38], [0, 38, 22, 12, 38, 1, 9, 38, 38, 38], [42, 12, 22, 38, 0, 1, 38, 49, 45, 38], [4, 12, 2, 12, 0, 1, 38, 49, 5, 12], [0, 38, 22, 12, 38, 38, 38, 38, 1, 12]],
  [[39, 21, 27, 31, 25, 21, 29, 30, 26, 21], [14, 21, 41, 44, 23, 38, 23, 43, 43, 38], [28, 34, 27, 21, 38, 34, 48, 43, 11, 34], [28, 34, 24, 31, 23, 34, 15, 38, 40, 34], [28, 34, 38, 44, 25, 34, 19, 17, 43, 34], [14, 38, 47, 34, 41, 21, 48, 43, 43, 38], [28, 34, 47, 20, 19, 34, 29, 44, 38, 34], [28, 34, 41, 38, 10, 34, 23, 30, 18, 34], [28, 34, 13, 34, 41, 34, 38, 18, 26, 34], [14, 38, 47, 34, 23, 38, 23, 44, 40, 21]],
  [[3, 37, 35, 35, 35, 37, 35, 35, 35, 37], [33, 37, 7, 7, 16, 38, 16, 16, 16, 38], [39, 21, 35, 36, 38, 21, 7, 16, 32, 21], [39, 21, 36, 35, 16, 21, 32, 38, 7, 21], [39, 21, 38, 7, 35, 21, 36, 32, 16, 21], [33, 38, 16, 16, 7, 37, 7, 16, 16, 38], [39, 21, 16, 32, 36, 21, 35, 7, 38, 21], [39, 21, 7, 38, 32, 21, 16, 35, 36, 21], [39, 21, 32, 16, 7, 21, 38, 36, 35, 21], [33, 38, 16, 16, 16, 38, 16, 7, 7, 37]],
  [[3, 37, 35, 35, 35, 37, 35, 35, 35, 37], [33, 37, 7, 7, 16, 38, 16, 16, 16, 38], [39, 21, 35, 36, 38, 21, 7, 16, 32, 21], [39, 21, 36, 35, 16, 21, 32, 38, 7, 21], [39, 21, 38, 7, 35, 21, 36, 32, 16, 21], [33, 38, 16, 16, 7, 37, 7, 16, 16, 38], [39, 21, 16, 32, 36, 21, 35, 7, 38, 21], [39, 21, 7, 38, 32, 21, 16, 35, 36, 21], [39, 21, 32, 16, 7, 21, 38, 36, 35, 21], [33, 38, 16, 16, 16, 38, 16, 7, 7, 37]]]

/-- The class of the state (number of values seen, first two columns of the last two rows). -/
def cls (k : Fin 4) (q2 q1 : Option Q) : Fin 50 :=
  ((tbl.getD k []).getD (codeQ q2) []).getD (codeQ q1) 0

/-- Class transitions: the list of target classes (with multiplicity) of each class. -/
def BL : List (List (Fin 50)) := [[35], [7], [38, 38], [35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35], [35, 35, 35], [7, 7, 7], [38, 38, 38], [7, 35, 36, 38], [32], [36], [16, 35, 38, 38], [7, 7, 32, 35], [16], [32, 35, 38, 38], [35, 35, 35, 35], [16, 36, 38, 38], [7, 16, 32, 38], [7, 7, 32, 36], [7, 7, 32, 32], [16, 16, 38, 38], [7, 7, 16, 36], [7, 7, 16, 16], [38], [16, 38], [32, 32, 38, 38], [16, 16, 35, 38, 38, 38], [7, 7, 7, 32, 32, 35], [32, 32, 35, 38, 38, 38], [35, 35, 35, 35, 35, 35], [16, 16, 36, 38, 38, 38], [7, 7, 7, 32, 32, 36], [7, 7, 7, 16, 16, 36], [7, 7, 16, 32, 35, 36, 38, 38], [35, 35, 35, 35, 35, 35, 35, 35], [7, 16], [7, 7, 7, 16, 16, 32, 32, 35, 36, 38, 38, 38], [7, 7, 16, 16, 32, 32, 38, 38], [7, 7, 7, 7, 16, 16, 16, 16], [], [35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35], [7, 35], [35, 38], [35, 35], [7, 32], [7, 36], [7, 7], [16, 16], [32, 38], [36, 38], [32, 32]]

/-- The target classes of a class, as a multiset. -/
def Brow (i : Fin 50) : Multiset (Fin 50) := (BL.getD i [] : Multiset (Fin 50))

/-- Class counts. -/
def cnt : ℕ → Fin 50 → ℕ
  | 0 => fun _ => 1
  | n + 1 => fun i => ((Brow i).map (cnt n)).sum

/-- The target classes of the admissible next rows from a state. -/
def tgt (k : Fin 4) (q2 q1 : Option Q) : Multiset (Fin 50) :=
  (univ.filter fun c : R => rowOK (rangeF k) c ∧ rowCond q2 q1 c).val.map
    (fun c => cls (nk k c) q1 (some (proj c)))

lemma step_check : ∀ (k : Fin 4) (q2 q1 : Option Q), tgt k q2 q1 = Brow (cls k q2 q1) := by
  decide +kernel

lemma F_cls (n : ℕ) : ∀ (k : Fin 4) (q2 q1 : Option Q),
    F (rangeF k) q2 q1 n = cnt n (cls k q2 q1) := by
  induction n with
  | zero => intro k q2 q1; rw [F_zero]; rfl
  | succ n ih =>
    intro k q2 q1
    rw [F_succ]
    have hd : ∀ c : R, (if rowOK (rangeF k) c ∧ rowCond q2 q1 c then
        F (rangeF k ∪ vals c) q1 (some (proj c)) n else 0) =
        (if rowOK (rangeF k) c ∧ rowCond q2 q1 c then
        cnt n (cls (nk k c) q1 (some (proj c))) else 0) := by
      intro c
      split_ifs with h
      · rw [seen_check k c h.1, ih]
      · rfl
    rw [sum_congr rfl (fun c _ => hd c), ← sum_filter, sum_eq_multiset_sum]
    show _ = ((Brow (cls k q2 q1)).map (cnt n)).sum
    rw [← step_check, tgt, Multiset.map_map]
    rfl

lemma a_cnt (n : ℕ) : a n = cnt n 14 := by
  rw [a_eq, show (∅ : Finset (Fin 3)) = rangeF 0 by decide, F_cls]
  rfl

lemma sum_map_count (s : Multiset (Fin 50)) (f : Fin 50 → ℤ) :
    (s.map f).sum = ∑ j, (s.count j : ℤ) * f j := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih]
    simp only [Multiset.count_cons, Nat.cast_add, add_mul, sum_add_distrib]
    rw [add_comm]
    congr 1
    simp

/-- A linear form in the class counts. -/
def L (w : Fin 50 → ℤ) (n : ℕ) : ℤ := ∑ i, w i * (cnt n i : ℤ)

lemma L_succ (w w' : Fin 50 → ℤ) (h : ∀ j, ∑ i, w i * ((Brow i).count j : ℤ) = w' j) (n : ℕ) :
    L w (n + 1) = L w' n := by
  unfold L
  have e : ∀ i, ((cnt (n + 1) i : ℕ) : ℤ) = ∑ j, ((Brow i).count j : ℤ) * (cnt n j : ℤ) := by
    intro i
    rw [← sum_map_count]
    simp only [cnt, Nat.cast_multiset_sum, Multiset.map_map]
    rfl
  simp only [e, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [← h j, sum_mul]
  refine sum_congr rfl fun i _ => ?_
  ring

/-- The row vector of the start class. -/
def w0 : Fin 50 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- The row vector `w0 * B`. -/
def w1 : Fin 50 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- The row vector `w0 * B ^ 2`. -/
def w2 : Fin 50 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 4, 4, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- The row vector `w0 * B ^ 3`. -/
def w3 : Fin 50 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 24, 24, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- The row vector `w0 * B ^ 4`. -/
def w4 : Fin 50 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 272, 0, 0, 0, 0, 0, 0, 0, 0, 160, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 160, 0, 0, 112, 112, 0, 272, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

lemma h01 : ∀ j, ∑ i, w0 i * ((Brow i).count j : ℤ) = w1 j := by decide +kernel
lemma h12 : ∀ j, ∑ i, w1 i * ((Brow i).count j : ℤ) = w2 j := by decide +kernel
lemma h23 : ∀ j, ∑ i, w2 i * ((Brow i).count j : ℤ) = w3 j := by decide +kernel
lemma h34 : ∀ j, ∑ i, w3 i * ((Brow i).count j : ℤ) = w4 j := by decide +kernel
lemma hzero : ∀ j, w4 j - 4 * w3 j - 4 * w2 j = 0 := by decide +kernel
lemma w0_zero : ∀ b, b ≠ 14 → w0 b = 0 := by decide +kernel

lemma a_L (n : ℕ) : (a n : ℤ) = L w0 n := by
  rw [a_cnt, L, sum_eq_single 14]
  · simp [w0]
  · intro b _ hb
    simp [w0_zero b hb]
  · simp

lemma a_rec (m : ℕ) : (a (m + 4) : ℤ) - 4 * a (m + 3) - 4 * a (m + 2) = 0 := by
  rw [a_L, a_L, a_L, L_succ _ _ h01, L_succ _ _ h12, L_succ _ _ h23, L_succ _ _ h34,
    L_succ _ _ h01, L_succ _ _ h12, L_succ _ _ h23, L_succ _ _ h01, L_succ _ _ h12]
  unfold L
  rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
  apply sum_eq_zero
  intro j _
  have := hzero j
  linear_combination (cnt m j : ℤ) * this

lemma a1 : a 1 = 4 := by rw [a_cnt]; decide +kernel
lemma a2 : a 2 = 48 := by rw [a_cnt]; decide +kernel
lemma a3 : a 3 = 224 := by rw [a_cnt]; decide +kernel

theorem gf :
    (1 - 4 * X - 4 * X ^ 2) * PowerSeries.mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (4 * X * (1 + 8 * X + 4 * X ^ 2) : PowerSeries ℤ) := by
  set s : PowerSeries ℤ := PowerSeries.mk (fun n => if n = 0 then 0 else (a n : ℤ)) with hs
  have hd : (1 - 4 * X - 4 * X ^ 2) * s = s - (s * C (4 : ℤ)) * X ^ 1 -
      (s * C (4 : ℤ)) * X ^ 2 := by
    simp only [pow_one, map_ofNat]
    ring
  have hn : (4 * X * (1 + 8 * X + 4 * X ^ 2) : PowerSeries ℤ) =
      C (4 : ℤ) * X ^ 1 + C (32 : ℤ) * X ^ 2 + C (16 : ℤ) * X ^ 3 := by
    simp only [pow_one, map_ofNat]
    ring
  rw [hd, hn]
  ext n
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_mul_C, coeff_C, hs, coeff_mk]
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ 4 ≤ n) with h | h | h | h | h
  · subst h; simp
  · subst h; simp [a1]
  · subst h; simp [a1, a2]
  · subst h; simp [a1, a2, a3]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have := a_rec m
    simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega]
    simp
    omega

/-- The closed form. -/
noncomputable def T (n : ℕ) : ℝ := 2 * ((2 - 2 * Real.sqrt 2) ^ n + (2 * (1 + Real.sqrt 2)) ^ n)

lemma pow_step (x : ℝ) (h : x ^ 2 = 4 * x + 4) (j : ℕ) :
    x ^ (j + 2) = 4 * x ^ (j + 1) + 4 * x ^ j := by
  linear_combination (x ^ j) * h

lemma T_rec (j : ℕ) : T (j + 2) = 4 * T (j + 1) + 4 * T j := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have ha : (2 - 2 * Real.sqrt 2) ^ 2 = 4 * (2 - 2 * Real.sqrt 2) + 4 := by
    linear_combination 4 * hs
  have hb : (2 * (1 + Real.sqrt 2)) ^ 2 = 4 * (2 * (1 + Real.sqrt 2)) + 4 := by
    linear_combination 4 * hs
  have e1 := pow_step _ ha j
  have e2 := pow_step _ hb j
  unfold T
  linear_combination 2 * e1 + 2 * e2

lemma closed (m : ℕ) : (a (m + 2) : ℝ) = T (m + 2) ∧ (a (m + 3) : ℝ) = T (m + 3) := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [a2, T]; push_cast; linear_combination (-16 : ℝ) * hs
    · rw [a3, T]; push_cast; linear_combination (-96 : ℝ) * hs
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨h2, ?_⟩
    have hr : (a (m + 4) : ℝ) = 4 * a (m + 3) + 4 * a (m + 2) := by
      have := a_rec m
      have h' : (a (m + 4) : ℤ) = 4 * a (m + 3) + 4 * a (m + 2) := by linarith
      exact_mod_cast h'
    rw [T_rec (m + 2)]
    rw [show m + 1 + 3 = m + 4 by ring, hr, show m + 2 + 1 = m + 3 by ring, h1, h2]

end OMA.P_oeis_a275138

theorem OMA.solution : type_of% @OMA.S_oeis_a275138.main := by
  refine ⟨OMA.P_oeis_a275138.gf, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact (OMA.P_oeis_a275138.closed m).1

