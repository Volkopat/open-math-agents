import OMAStatements.S_oeis_a280668

namespace OMA.S_oeis_a280668

open PowerSeries Finset






/-! ## Rows, their neighbors and the count of the elements meeting the condition -/

/-- The row r of the array x, counted from 0, or none outside the array. -/
def rowOpt {m : ℕ} (x : Fin m → Fin 3 → Fin 3) (r : ℤ) : Option (Fin 3 → Fin 3) :=
  if h : 0 ≤ r ∧ r < m then some (x ⟨r.toNat, by omega⟩) else none

/-- The element in column c of the optional row u. -/
def rc (u : Option (Fin 3 → Fin 3)) (c : ℤ) : Option (Fin 3) :=
  match u with
  | none => none
  | some v => if h : 0 ≤ c ∧ c < 3 then some (v ⟨c.toNat, by omega⟩) else none

theorem cell_eq (n : ℕ) (x : Fin n → Fin 3 → Fin 3) (r c : ℤ) :
    cell n x r c = rc (rowOpt x r) c := by
  unfold cell rowOpt
  by_cases h1 : 0 ≤ r ∧ r < n
  · rw [dif_pos h1]
    by_cases h2 : 0 ≤ c ∧ c < 3
    · rw [dif_pos ⟨h1.1, h1.2, h2.1, h2.2⟩]
      simp only [rc, dif_pos h2]
    · rw [dif_neg (fun h => h2 ⟨h.2.2.1, h.2.2.2⟩)]
      simp only [rc, dif_neg h2]
  · rw [dif_neg (fun h => h1 ⟨h.1, h.2.1⟩), dif_neg h1]
    rfl

theorem rowOpt_self {m : ℕ} (x : Fin m → Fin 3 → Fin 3) (i : Fin m) :
    rowOpt x (i : ℤ) = some (x i) := by
  have hi := i.isLt
  unfold rowOpt
  rw [dif_pos ⟨by omega, by omega⟩]
  simp

theorem rowOpt_neg {m : ℕ} (y : Fin m → Fin 3 → Fin 3) (r : ℤ) (h : r < 0) : rowOpt y r = none := by
  unfold rowOpt
  rw [dif_neg (by omega)]

/-- The values of the neighbors of the element in column j of the row v, with the row u above v
and the row w below it (none where there is no such row). -/
def nbrsR (u : Option (Fin 3 → Fin 3)) (v : Fin 3 → Fin 3) (w : Option (Fin 3 → Fin 3))
    (j : Fin 3) : List (Fin 3) :=
  [((0 : ℤ), (-1 : ℤ)), (0, 1), (-1, 1), (1, -1)].filterMap fun d =>
    rc (if d.1 = -1 then u else if d.1 = 0 then some v else w) (j + d.2)

theorem nbrs_eq (n : ℕ) (x : Fin n → Fin 3 → Fin 3) (i : Fin n) (j : Fin 3) :
    nbrs n x i j = nbrsR (rowOpt x ((i : ℤ) + -1)) (x i) (rowOpt x ((i : ℤ) + 1)) j := by
  unfold nbrs nbrsR
  refine List.filterMap_congr (fun d hd => ?_)
  rw [cell_eq]
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> simp [rowOpt_self]

/-- The condition of the entry for the element in column j of the row v. -/
def excR (u : Option (Fin 3 → Fin 3)) (v : Fin 3 → Fin 3) (w : Option (Fin 3 → Fin 3))
    (j : Fin 3) : Bool :=
  decide (1 < (nbrsR u v w j).count (v j))

theorem exc_iff (n : ℕ) (x : Fin n → Fin 3 → Fin 3) (i : Fin n) (j : Fin 3) :
    eqmore n x i j ↔ excR (rowOpt x ((i : ℤ) + -1)) (x i) (rowOpt x ((i : ℤ) + 1)) j = true := by
  unfold eqmore excR
  rw [nbrs_eq, decide_eq_true_iff]

/-- The number of elements of the row v that meet the condition. -/
def exr (u : Option (Fin 3 → Fin 3)) (v : Fin 3 → Fin 3) (w : Option (Fin 3 → Fin 3)) : ℕ :=
  (if excR u v w 0 = true then 1 else 0) +
    (if excR u v w 1 = true then 1 else 0) +
    (if excR u v w 2 = true then 1 else 0)

theorem all_iff (n : ℕ) (x : Fin n → Fin 3 → Fin 3) :
    (∀ i j, ¬ eqmore n x i j) ↔
      ∑ i : Fin n, exr (rowOpt x ((i : ℤ) + -1)) (x i) (rowOpt x ((i : ℤ) + 1)) = 0 := by
  rw [Finset.sum_eq_zero_iff]
  simp only [mem_univ, true_implies]
  refine forall_congr' (fun i => ?_)
  have e : exr (rowOpt x ((i : ℤ) + -1)) (x i) (rowOpt x ((i : ℤ) + 1)) =
      ∑ j : Fin 3, if excR (rowOpt x ((i : ℤ) + -1)) (x i) (rowOpt x ((i : ℤ) + 1)) j = true
        then 1 else 0 := by
    rw [Fin.sum_univ_three]
    rfl
  rw [e, Finset.sum_eq_zero_iff]
  simp only [mem_univ, true_implies]
  refine forall_congr' (fun j => ?_)
  rw [exc_iff]
  constructor
  · intro h
    rw [if_neg h]
  · intro h hc
    rw [if_pos hc] at h
    exact one_ne_zero h

/-- The row r of y, with the optional row p in place of row -1. -/
def above {m : ℕ} (p : Option (Fin 3 → Fin 3)) (y : Fin m → Fin 3 → Fin 3) (r : ℤ) :
    Option (Fin 3 → Fin 3) :=
  if r = -1 then p else rowOpt y r

/-- The number of elements of y that meet the condition, with the optional row p above y. -/
def G {m : ℕ} (p : Option (Fin 3 → Fin 3)) (y : Fin m → Fin 3 → Fin 3) : ℕ :=
  ∑ i : Fin m, exr (above p y ((i : ℤ) + -1)) (y i) (above p y ((i : ℤ) + 1))

theorem G_none {m : ℕ} (x : Fin m → Fin 3 → Fin 3) :
    G none x = ∑ i : Fin m, exr (rowOpt x ((i : ℤ) + -1)) (x i) (rowOpt x ((i : ℤ) + 1)) := by
  unfold G
  refine sum_congr rfl (fun i _ => ?_)
  have h1 : above none x ((i : ℤ) + -1) = rowOpt x ((i : ℤ) + -1) := by
    unfold above
    split_ifs with h
    · rw [rowOpt_neg x _ (by omega)]
    · rfl
  have h2 : above none x ((i : ℤ) + 1) = rowOpt x ((i : ℤ) + 1) := by
    unfold above
    rw [if_neg (by omega)]
  rw [h1, h2]

theorem rowOpt_empty (y : Fin 0 → Fin 3 → Fin 3) (r : ℤ) : rowOpt y r = none := by
  unfold rowOpt
  rw [dif_neg (by omega)]

theorem rowOpt_cons {m : ℕ} (c : Fin 3 → Fin 3) (y : Fin m → Fin 3 → Fin 3) (r : ℤ) :
    rowOpt (Fin.cons c y : Fin (m + 1) → Fin 3 → Fin 3) r =
      if r = 0 then some c else rowOpt y (r - 1) := by
  unfold rowOpt
  by_cases h0 : r = 0
  · subst h0
    rw [dif_pos ⟨le_refl 0, by omega⟩, if_pos rfl]
    rfl
  · rw [if_neg h0]
    by_cases h1 : 0 ≤ r ∧ r < ((m + 1 : ℕ) : ℤ)
    · rw [dif_pos h1, dif_pos ⟨by omega, by omega⟩]
      have e : (⟨r.toNat, by omega⟩ : Fin (m + 1)) = Fin.succ ⟨(r - 1).toNat, by omega⟩ := by
        ext
        simp only [Fin.val_succ]
        omega
      rw [e, Fin.cons_succ]
    · rw [dif_neg h1, dif_neg (by omega)]

theorem above_cons {m : ℕ} (p : Option (Fin 3 → Fin 3)) (c : Fin 3 → Fin 3)
    (y : Fin m → Fin 3 → Fin 3) (r : ℤ) (h : r ≠ -1) :
    above p (Fin.cons c y : Fin (m + 1) → Fin 3 → Fin 3) r = above (some c) y (r - 1) := by
  unfold above
  rw [if_neg h, rowOpt_cons]
  by_cases h0 : r = 0
  · rw [if_pos h0, if_pos (by omega)]
  · rw [if_neg h0, if_neg (by omega)]

theorem G_cons {m : ℕ} (p : Option (Fin 3 → Fin 3)) (c : Fin 3 → Fin 3)
    (y : Fin m → Fin 3 → Fin 3) :
    G p (Fin.cons c y : Fin (m + 1) → Fin 3 → Fin 3) = exr p c (rowOpt y 0) + G (some c) y := by
  unfold G
  rw [Fin.sum_univ_succ]
  congr 1
  · have e0 : (((0 : Fin (m + 1)) : ℕ) : ℤ) = 0 := by simp
    rw [e0, zero_add, zero_add, Fin.cons_zero]
    have h1 : above p (Fin.cons c y : Fin (m + 1) → Fin 3 → Fin 3) (-1) = p := by
      unfold above
      rw [if_pos rfl]
    have h2 : above p (Fin.cons c y : Fin (m + 1) → Fin 3 → Fin 3) 1 = rowOpt y 0 := by
      rw [above_cons p c y 1 (by norm_num)]
      unfold above
      rw [if_neg (by norm_num)]
      norm_num
    rw [h1, h2]
  · refine sum_congr rfl (fun i _ => ?_)
    simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one, Fin.cons_succ]
    rw [above_cons p c y _ (by omega), above_cons p c y _ (by omega)]
    congr 2 <;> ring

/-! ## New values in order, row by row -/

/-- Reading the rows of y in order, every element other than 0 is at most lim (so its predecessor
value was introduced above y) or comes after an element of y one less. -/
def orderedL {m : ℕ} (lim : ℕ) (y : Fin m → Fin 3 → Fin 3) : Prop :=
  ∀ i j, y i j ≠ 0 → (y i j).val ≤ lim ∨
    ∃ i' j', (i' < i ∨ (i' = i ∧ j' < j)) ∧ (y i' j').val + 1 = (y i j).val

instance {m : ℕ} (lim : ℕ) (y : Fin m → Fin 3 → Fin 3) : Decidable (orderedL lim y) := by
  unfold orderedL
  infer_instance

theorem ordered_iff (n : ℕ) (x : Fin n → Fin 3 → Fin 3) : ordered n x ↔ orderedL 0 x := by
  unfold ordered orderedL
  refine forall_congr' (fun i => forall_congr' (fun j => imp_congr_right (fun h => ?_)))
  have hx : ¬ (x i j).val ≤ 0 := fun h' => h (Fin.ext (Nat.le_zero.mp h'))
  constructor
  · exact Or.inr
  · rintro (h' | h')
    · exact absurd h' hx
    · exact h'

/-- The row r continues the order of new values after lim values: each element is at most the
number of values introduced before it, counting those of r to its left. -/
def rgsRow (lim : ℕ) (r : Fin 3 → Fin 3) : Bool :=
  decide ((r 0).val ≤ lim ∧ (r 1).val ≤ max lim ((r 0).val + 1) ∧ (r 2).val ≤ max (max lim ((r 0).val + 1)) ((r 1).val + 1))

/-- The number of values introduced after the row r. -/
def limNext (lim : ℕ) (r : Fin 3 → Fin 3) : ℕ := max (max (max lim ((r 0).val + 1)) ((r 1).val + 1)) ((r 2).val + 1)

/-- The row with code c: column j holds the digit of 3 ^ j. -/
def dig (c : ℕ) : Fin 3 → Fin 3 := fun j => ⟨c / 3 ^ j.val % 3, Nat.mod_lt _ (by norm_num)⟩

/-- The code of the row r. -/
def code (r : Fin 3 → Fin 3) : ℕ := (r 0).val + 3 * (r 1).val + 9 * (r 2).val

theorem dig_code (r : Fin 3 → Fin 3) : dig (code r) = r := by
  funext j
  apply Fin.ext
  have h0 := (r 0).isLt
  have h1 := (r 1).isLt
  have h2 := (r 2).isLt
  fin_cases j <;> simp [dig, code] <;> omega

theorem code_lt (r : Fin 3 → Fin 3) : code r < 27 := by
  have h0 := (r 0).isLt
  have h1 := (r 1).isLt
  have h2 := (r 2).isLt
  unfold code
  omega

theorem code_dig (c : ℕ) (h : c < 27) : code (dig c) = c := by
  simp [code, dig]
  omega

/-- Reading the row r from left to right after lim values, every element other than 0 is at most
lim or comes after an element of r one less. -/
def rowOrd (lim : ℕ) (r : Fin 3 → Fin 3) : Prop :=
  ∀ j, r j ≠ 0 → (r j).val ≤ lim ∨ ∃ j', j' < j ∧ (r j').val + 1 = (r j).val

instance (lim : ℕ) (r : Fin 3 → Fin 3) : Decidable (rowOrd lim r) := by
  unfold rowOrd
  infer_instance

/-- On every row and lim ≤ 3: rgsRow is rowOrd, and when it holds, a value v ≥ 1 is at most lim or
one more than an element of the row exactly when v ≤ limNext. -/
def rowcheck : Bool := (List.range 4).all fun lim => (List.range 27).all fun rc =>
  (rgsRow lim (dig rc) == decide (rowOrd lim (dig rc))) &&
    (!(rgsRow lim (dig rc)) || (List.range 2).all fun v =>
      decide (v + 1 ≤ lim ∨ ∃ j, (dig rc j).val + 1 = v + 1) == decide (v + 1 ≤ limNext lim (dig rc)))

theorem rowcheck_true : rowcheck = true := by
  decide +kernel

theorem rgsRow_iff (lim : ℕ) (hl : lim ≤ 3) (r : Fin 3 → Fin 3) :
    rgsRow lim r = true ↔ rowOrd lim r := by
  have h := rowcheck_true
  unfold rowcheck at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h
  have := (h lim (by omega) (code r) (code_lt r)).1
  rw [dig_code] at this
  rw [this, decide_eq_true_iff]

theorem next_iff (lim : ℕ) (hl : lim ≤ 3) (r : Fin 3 → Fin 3) (hr : rgsRow lim r = true)
    (v : ℕ) (hv1 : 1 ≤ v) (hv2 : v < 3) :
    (v ≤ lim ∨ ∃ j, (r j).val + 1 = v) ↔ v ≤ limNext lim r := by
  have h := rowcheck_true
  unfold rowcheck at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  have h2 := (h lim (by omega) (code r) (code_lt r)).2
  rw [dig_code] at h2
  rcases h2 with h2 | h2
  · rw [hr] at h2
    exact absurd h2 (by decide)
  · have := h2 (v - 1) (by omega)
    rw [decide_eq_decide, show v - 1 + 1 = v by omega] at this
    exact this

theorem orderedL_cons {m : ℕ} (lim : ℕ) (hl : lim ≤ 3) (r : Fin 3 → Fin 3)
    (y : Fin m → Fin 3 → Fin 3) :
    orderedL lim (Fin.cons r y : Fin (m + 1) → Fin 3 → Fin 3) ↔
      rgsRow lim r = true ∧ orderedL (limNext lim r) y := by
  constructor
  · intro H
    have hr : rgsRow lim r = true := by
      rw [rgsRow_iff lim hl]
      intro j hj
      rcases H 0 j (by simpa using hj) with h | ⟨i', j', hij, hv⟩
      · left
        simpa using h
      · right
        rcases hij with h | ⟨h, h'⟩
        · exact absurd h (Fin.not_lt_zero _)
        · subst h
          exact ⟨j', h', by simpa using hv⟩
    refine ⟨hr, fun i j hne => ?_⟩
    have hv1 : 1 ≤ (y i j).val := Nat.pos_of_ne_zero (fun h => hne (Fin.ext h))
    rcases H i.succ j (by simpa using hne) with h | ⟨i', j', hij, hv⟩
    · left
      rw [← next_iff lim hl r hr _ hv1 (y i j).isLt]
      left
      simpa using h
    · cases i' using Fin.cases with
      | zero =>
        left
        rw [← next_iff lim hl r hr _ hv1 (y i j).isLt]
        right
        exact ⟨j', by simpa using hv⟩
      | succ i2 =>
        right
        refine ⟨i2, j', ?_, by simpa using hv⟩
        rcases hij with h | ⟨h, h'⟩
        · exact Or.inl (Fin.succ_lt_succ_iff.mp h)
        · exact Or.inr ⟨Fin.succ_injective _ h, h'⟩
  · rintro ⟨hr, Hy⟩ i j hne
    cases i using Fin.cases with
    | zero =>
      simp only [Fin.cons_zero] at hne ⊢
      rcases (rgsRow_iff lim hl r).mp hr j hne with h | ⟨j', hj', hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨0, j', Or.inr ⟨rfl, hj'⟩, by simpa using hv⟩
    | succ i1 =>
      simp only [Fin.cons_succ] at hne ⊢
      have hv1 : 1 ≤ (y i1 j).val := Nat.pos_of_ne_zero (fun h => hne (Fin.ext h))
      rcases Hy i1 j hne with h | ⟨i2, j', hij, hv⟩
      · rcases (next_iff lim hl r hr _ hv1 (y i1 j).isLt).mpr h with h' | ⟨j', hv⟩
        · exact Or.inl h'
        · exact Or.inr ⟨0, j', Or.inl (Fin.succ_pos i1), by simpa using hv⟩
      · right
        refine ⟨i2.succ, j', ?_, by simpa using hv⟩
        rcases hij with h | ⟨h, h'⟩
        · exact Or.inl (Fin.succ_lt_succ_iff.mpr h)
        · exact Or.inr ⟨by rw [h], h'⟩

/-! ## The count by the first row and the continuation counts -/

/-- The ways to put m more rows below the current row c, with the optional row p above c, lim
values introduced up to c and e elements above c meeting the condition. -/
noncomputable def N (p : Option (Fin 3 → Fin 3)) (c : Fin 3 → Fin 3) (lim e m : ℕ) : ℕ :=
  ∑ y : Fin m → Fin 3 → Fin 3, if orderedL lim y ∧ G p (Fin.cons c y) + e = 0 then 1 else 0

theorem sum_cons {α : Type} [Fintype α] [DecidableEq α] (m : ℕ) (f : (Fin (m + 1) → α) → ℕ) :
    ∑ y : Fin (m + 1) → α, f y = ∑ r : α, ∑ y : Fin m → α, f (Fin.cons r y) := by
  rw [← (Fin.consEquiv fun _ => α).sum_comp, Fintype.sum_prod_type]
  rfl

theorem N_zero (p : Option (Fin 3 → Fin 3)) (c : Fin 3 → Fin 3) (lim e : ℕ) :
    N p c lim e 0 = if exr p c none + e = 0 then 1 else 0 := by
  have key : ∀ y : Fin 0 → Fin 3 → Fin 3,
      (if orderedL lim y ∧ G p (Fin.cons c y) + e = 0 then 1 else 0) =
        if exr p c none + e = 0 then 1 else 0 := by
    intro y
    have h1 : orderedL lim y := fun i => i.elim0
    have h2 : G p (Fin.cons c y) = exr p c none := by
      rw [G_cons, rowOpt_empty]
      simp [G]
    by_cases h : exr p c none + e = 0 <;> simp [h, h1, h2]
  unfold N
  rw [Fintype.sum_unique]
  exact key _

theorem N_succ (p : Option (Fin 3 → Fin 3)) (c : Fin 3 → Fin 3) (lim e m : ℕ)
    (hl : lim ≤ 3) : N p c lim e (m + 1) = ∑ r : Fin 3 → Fin 3,
      if rgsRow lim r = true then N (some c) r (limNext lim r) (e + exr p c (some r)) m else 0 := by
  unfold N
  rw [sum_cons]
  refine sum_congr rfl (fun r _ => ?_)
  have hG : ∀ y : Fin m → Fin 3 → Fin 3,
      G p (Fin.cons c (Fin.cons r y : Fin (m + 1) → Fin 3 → Fin 3)) =
        exr p c (some r) + G (some c) (Fin.cons r y) := by
    intro y
    rw [G_cons, rowOpt_cons, if_pos rfl]
  by_cases hr : rgsRow lim r = true
  · rw [if_pos hr]
    refine sum_congr rfl (fun y _ => ?_)
    have he : (exr p c (some r) + G (some c) (Fin.cons r y) + e = 0) ↔
        (G (some c) (Fin.cons r y) + (e + exr p c (some r)) = 0) := by omega
    simp only [hG, orderedL_cons lim hl, hr, true_and, he]
  · rw [if_neg hr]
    refine sum_eq_zero (fun y _ => ?_)
    simp [orderedL_cons lim hl, hr]

theorem N_over (p : Option (Fin 3 → Fin 3)) (c : Fin 3 → Fin 3) (lim e m : ℕ) (h : 0 < e) :
    N p c lim e m = 0 := by
  unfold N
  refine sum_eq_zero (fun y _ => ?_)
  rw [if_neg (fun h' => by have := h'.2; omega)]

theorem cond_iff (n : ℕ) (x : Fin n → Fin 3 → Fin 3) :
    ((∀ i j, ¬ eqmore n x i j) ∧ ordered n x) ↔ (orderedL 0 x ∧ G none x + 0 = 0) := by
  rw [all_iff, ← G_none, ordered_iff, add_zero, and_comm]

theorem a_succ (n : ℕ) : a (n + 1) = ∑ c : Fin 3 → Fin 3,
    if rgsRow 0 c = true then N none c (limNext 0 c) 0 n else 0 := by
  have ha : a (n + 1) = ∑ x : Fin (n + 1) → Fin 3 → Fin 3,
      if orderedL 0 x ∧ G none x + 0 = 0 then 1 else 0 := by
    rw [← card_filter]
    unfold a
    rw [← Set.ncard_coe_finset]
    congr 1
    ext x
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    exact cond_iff (n + 1) x
  rw [ha, sum_cons]
  refine sum_congr rfl (fun c _ => ?_)
  unfold N
  by_cases hc : rgsRow 0 c = true
  · rw [if_pos hc]
    refine sum_congr rfl (fun y _ => ?_)
    simp only [orderedL_cons 0 (by norm_num), hc, true_and]
  · rw [if_neg hc]
    refine sum_eq_zero (fun y _ => ?_)
    simp [orderedL_cons 0 (by norm_num), hc]

/-! ## Codes of rows and states -/

theorem sum_dig (g : (Fin 3 → Fin 3) → ℕ) : ∑ r, g r = ∑ c ∈ range 27, g (dig c) := by
  rw [← (finFunctionFinEquiv (m := 3) (n := 3)).symm.sum_comp]
  exact Fin.sum_univ_eq_sum_range (fun c => g (dig c)) _

/-- The code of an optional row: 0 for none, 1 + the row code otherwise. -/
def encO (p : Option (Fin 3 → Fin 3)) : ℕ :=
  match p with
  | none => 0
  | some r => 1 + code r

/-- The code of the columns of the row with code cc that the row below reads (columns 1, 2). -/
def pcodeC (cc : ℕ) : ℕ := cc / 3 % 9

/-- The code of the columns of the row with code cc that the row above reads (columns 0, 1). -/
def pcodeW (cc : ℕ) : ℕ := cc % 9

/-- The table index of an optional row above: 0 for none, 1 + the code of its read columns. -/
def projIdx (pc : ℕ) : ℕ := if pc = 0 then 0 else 1 + pcodeC (pc - 1)

/-- The table index of an optional row below: 0 for none, 1 + the code of its read columns. -/
def projW (pc : ℕ) : ℕ := if pc = 0 then 0 else 1 + pcodeW (pc - 1)

/-- The row r with the columns that the row below does not read set to 0. -/
def keepU (r : Fin 3 → Fin 3) : Fin 3 → Fin 3 := fun j => if 1 ≤ j.val then r j else 0

/-- The row r with the columns that the row above does not read set to 0. -/
def keepW (r : Fin 3 → Fin 3) : Fin 3 → Fin 3 := fun j => if j.val < 2 then r j else 0

theorem nbrsR_keep (u : Option (Fin 3 → Fin 3)) (v : Fin 3 → Fin 3)
    (w : Option (Fin 3 → Fin 3)) (j : Fin 3) :
    nbrsR u v w j = nbrsR (u.map keepU) v (w.map keepW) j := by
  unfold nbrsR
  refine List.filterMap_congr (fun d hd => ?_)
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> fin_cases j <;> cases u <;> cases w <;> simp [rc, keepU, keepW]

theorem exr_keep (u : Option (Fin 3 → Fin 3)) (v : Fin 3 → Fin 3)
    (w : Option (Fin 3 → Fin 3)) : exr u v w = exr (u.map keepU) v (w.map keepW) := by
  unfold exr excR
  rw [nbrsR_keep u v w 0, nbrsR_keep u v w 1, nbrsR_keep u v w 2]

/-- The element in column i of the optional row u, or none outside the array. -/
def rcN (u : Option (Fin 3 → Fin 3)) (i : ℕ) : Option (Fin 3) :=
  match u with
  | none => none
  | some v => if h : i < 3 then some (v ⟨i, h⟩) else none

/-- nbrsR with natural-number column arithmetic, which the kernel evaluates several times faster
than the integer arithmetic of nbrsR. -/
def nbrsN (u : Option (Fin 3 → Fin 3)) (v : Fin 3 → Fin 3) (w : Option (Fin 3 → Fin 3))
    (j : Fin 3) : List (Fin 3) :=
  [(if j.val < 1 then none else rcN (some v) (j.val - 1)),
    rcN (some v) (j.val + 1),
    rcN u (j.val + 1),
    (if j.val < 1 then none else rcN w (j.val - 1))].filterMap id

theorem nbrsR_N (u : Option (Fin 3 → Fin 3)) (v : Fin 3 → Fin 3)
    (w : Option (Fin 3 → Fin 3)) (j : Fin 3) : nbrsR u v w j = nbrsN u v w j := by
  unfold nbrsR nbrsN
  fin_cases j <;> cases u <;> cases w <;> simp [rc, rcN]

/-- excR with nbrsN in place of nbrsR. -/
def excN (u : Option (Fin 3 → Fin 3)) (v : Fin 3 → Fin 3) (w : Option (Fin 3 → Fin 3))
    (j : Fin 3) : Bool :=
  decide (1 < (nbrsN u v w j).count (v j))

/-- exr with excN in place of excR. -/
def exrN (u : Option (Fin 3 → Fin 3)) (v : Fin 3 → Fin 3) (w : Option (Fin 3 → Fin 3)) : ℕ :=
  (if excN u v w 0 = true then 1 else 0) +
    (if excN u v w 1 = true then 1 else 0) +
    (if excN u v w 2 = true then 1 else 0)

theorem exr_N (u : Option (Fin 3 → Fin 3)) (v : Fin 3 → Fin 3)
    (w : Option (Fin 3 → Fin 3)) : exr u v w = exrN u v w := by
  unfold exr exrN excR excN
  rw [nbrsR_N u v w 0, nbrsR_N u v w 1, nbrsR_N u v w 2]

/-- The row with the code pc in the columns that the row below reads. -/
def liftU (pc : ℕ) : Fin 3 → Fin 3 := dig (3 * pc)

/-- The row with the code pc in the columns that the row above reads. -/
def liftW (pc : ℕ) : Fin 3 → Fin 3 := dig pc

def decU (qc : ℕ) : Option (Fin 3 → Fin 3) := if qc = 0 then none else some (liftU (qc - 1))

def decW (wc : ℕ) : Option (Fin 3 → Fin 3) := if wc = 0 then none else some (liftW (wc - 1))

theorem keepU_eq (r : Fin 3 → Fin 3) : keepU r = liftU (pcodeC (code r)) := by
  funext j
  apply Fin.ext
  have h0 := (r 0).isLt
  have h1 := (r 1).isLt
  have h2 := (r 2).isLt
  fin_cases j <;> simp [keepU, liftU, dig, pcodeC, code] <;> omega

theorem keepW_eq (r : Fin 3 → Fin 3) : keepW r = liftW (pcodeW (code r)) := by
  funext j
  apply Fin.ext
  have h0 := (r 0).isLt
  have h1 := (r 1).isLt
  have h2 := (r 2).isLt
  fin_cases j <;> simp [keepW, liftW, dig, pcodeW, code] <;> omega

theorem mapU_eq (p : Option (Fin 3 → Fin 3)) : p.map keepU = decU (projIdx (encO p)) := by
  cases p with
  | none => rfl
  | some r => simp [encO, projIdx, decU, keepU_eq]

theorem mapW_eq (p : Option (Fin 3 → Fin 3)) : p.map keepW = decW (projW (encO p)) := by
  cases p with
  | none => rfl
  | some r => simp [encO, projW, decW, keepW_eq]

theorem projIdx_lt (p : Option (Fin 3 → Fin 3)) : projIdx (encO p) < 10 := by
  cases p with
  | none => simp [encO, projIdx]
  | some r =>
    have h : projIdx (encO (some r)) = 1 + pcodeC (code r) := by simp [encO, projIdx]
    have := code_lt r
    rw [h]
    unfold pcodeC
    omega

theorem projW_lt (p : Option (Fin 3 → Fin 3)) : projW (encO p) < 10 := by
  cases p with
  | none => simp [encO, projW]
  | some r =>
    have h : projW (encO (some r)) = 1 + pcodeW (code r) := by simp [encO, projW]
    have := code_lt r
    rw [h]
    unfold pcodeW
    omega

/-- The number of elements meeting the condition in the row with code cc, with the row above of
table index qc and the row below of table index wc (0 for none, 1 + the code of the read
columns otherwise). -/
def exrT (qc cc wc : ℕ) : ℕ := 362834622623281049768879990586142914047676838667889081011808383879425816465748529090344845220104540182811595016946978491985913169767343466437708538519763626446839993734545912847969519078486872508879178744699060793034178200727959385330388182322745035863791800869092488162953375134380220861104212163773837262381976932577166656067710314024402410719191749968458178722288144409153164284644969530667644172678787757155560117524254699934701387487593463203408788094807880398180571165410118148889207385302909548899560506957673489303342675784921830033384972450926536891785950573041081010601693820027906782111853938389857444514651217061784201115989559689854731957252188646800871743690740074105994938553733678323419939087786564368553777860013052212972019566178168665429778588053622059250956304144971169628009061738442249965457103371344767147163862442016571946214911479529026424181017514684955940883894348847012020925942028255001040304026400667212789861441092290418261404377200793252111522241634988281487341351946726240256202949671858490087075448098971008956287962218913702153767258325617962583620313732495541463515108238415402279343802973259849854691919584644141379142126394290211152238344070131771844408936659775496458839083557496927358648912974353925333577951818661563368955673967548200505829270534890427210422654201611869026869909718915952143737502253868169649488205305124839112607780940977824394886612702032501267127414034350869046002550029797964455177710241272275828852543237812858600277891485054750352380092161098170606292680366431972926073737363556993489462749712432074932919834515713218621088778881726726167865466474502277506094505 >>> (2 * ((qc * 27 + cc) * 10 + wc)) % 4

/-- The first row condition on codes. -/
def rgsC (lim cc : ℕ) : Bool := decide (cc % 3 ≤ lim ∧ cc / 3 % 3 ≤ max lim (cc % 3 + 1) ∧ cc / 9 % 3 ≤ max (max lim (cc % 3 + 1)) (cc / 3 % 3 + 1))

/-- The values introduced after the row with code cc. -/
def limC (lim cc : ℕ) : ℕ := max (max (max lim (cc % 3 + 1)) (cc / 3 % 3 + 1)) (cc / 9 % 3 + 1)

/-- The code of the state (qc, cc, lim, e): row above (table index qc), current row cc, lim values
introduced, e elements above meeting the condition. -/
def enc (qc cc lim e : ℕ) : ℕ := ((qc * 27 + cc) * 3 + (lim - 1)) * 1 + e

def qcOf (s : ℕ) : ℕ := s / (27 * 3 * 1)

def ccOf (s : ℕ) : ℕ := s / (3 * 1) % 27

def limOf (s : ℕ) : ℕ := s / 1 % 3 + 1

def eOf (s : ℕ) : ℕ := s % 1

/-- The next row with code rc may follow the state s. -/
def guardB (s rc : ℕ) : Bool :=
  rgsC (limOf s) rc && decide (eOf s + exrT (qcOf s) (ccOf s) (1 + pcodeW rc) ≤ 0)

/-- The state after the row with code rc. -/
def succS (s rc : ℕ) : ℕ :=
  enc (1 + pcodeC (ccOf s)) rc (limC (limOf s) rc) (eOf s + exrT (qcOf s) (ccOf s) (1 + pcodeW rc))

/-- The continuation counts on state codes. -/
def Ncode : ℕ → ℕ → ℕ
  | s, 0 => if exrT (qcOf s) (ccOf s) 0 + eOf s = 0 then 1 else 0
  | s, m + 1 => ∑ rc ∈ range 27, if guardB s rc = true then Ncode (succS s rc) m else 0

theorem Ncode_succ (s m : ℕ) : Ncode s (m + 1) =
    ∑ rc ∈ range 27, if guardB s rc = true then Ncode (succS s rc) m else 0 := rfl

/-- The table of Ncode 0: entry s in the bits 1 * s.. of one number. -/
def tab0 (s : ℕ) : ℕ := 939520955276180130824972489276637044326859121621972466298808995362549927329667593865476796010897253923087805008810874717660581756545731282358570081991561832168318844465256663970989046008371314691114509731590437460160390705715532335283176448 >>> (1 * s) % 2 ^ 1

/-- The table of Ncode 1: entry s in the bits 5 * s.. of one number. -/
def tab1 (s : ℕ) : ℕ := 5229912513958203803148615809495781920590315480024411181937385212631638443164538450864517530501066323713447181538373599556446170398553377453757014756309168889906082080926963221392638473832841936860880320382161629667516591122218495104157067454658010669445882462141860145645270330177037543090155767059668674211470345920370862874924400268894260521246061029484909728702703724332733913535169310289020259191369412194036736591370924688945766540107368357616064118995489915103290879911601666579904873251921209575325885014390105345823445266955790035112929977657618560691182280146052628845977475614402927904076463543233204469429809915051013026911071490774436452942637140092155564639223093066936744041356806779029840966353160407742361772010040416872696507552251319197888547776657349400030118626887820227118178977114305481369430362845112287164304898625617051223364646043117477435338585311059206714494825517464500559738369760266206747217303034518975534858643330546155049619648068095187977639733840886306665712545111888301475384269164862636776113956286855722592241146177048886021191485272416727596470206030888576268782702092622085261734787077092719535650489785348694847650687153037707995573810672828464870693399429120 >>> (5 * s) % 2 ^ 5

/-- The table of Ncode 2: entry s in the bits 9 * s.. of one number. -/
def tab2 (s : ℕ) : ℕ := 36890326853299579288937574904252499399523553421666510954878018117982287763972571204686930659146737752126953982482651064450448290607807079506316348623775982104789148003126232191625273948004223517120360544887354229135904631502462705074728002702055502204635521294601810121914651851201662601554329714844053139880565546762266309718873597142267581980315203607794304949817483723970249507689662672180744297347792297272006676146048320972787250778378848318635652056053056324286168397998379341670481352597137269222044633483160201231531750118260867476110047535581874926834528480986937709105390423148887125442595166298123786035383321827101020643954502979406866192555475407361200983393550193985775518035818396832168678828532126673058043174254086717423465565914632947903055673688539473045803464708324384722522322913462551520817230204540230004263113875744678826977155011579459841308717071480152809243842975893566493113490961303944409764375001437506893996400850327461994752281084055440990930438693436412428722731849057545497228284876268463902389985416752467404413700879451573879333124675456100519760478968784933983287876739532467380273232781634204743474090163312751709249538723104144966953964543839958317882866230953017933203445267169586588848940481143481642573026758508242890442781710283097407717003515893154160181441964278156982003045852929797317554448351536737831666412890613771675845234264778886894467247440322980516905924319671472766865766588859812310132788346530867125110367375807062063675030634078508565833966048175656526776731990703771420314120863926643982462772738484589822168465123708631091486364435996000138245623164846791910902296606581351236142104705545633015105427416908632221819153478213390883615153979644833027495396635842883829753891726527367658839767186318767948591892588162956030886683243577498978410651882105909259670481915986540249544986412898867500183768723529413264332310843319101460569696532599392582476905746437393460567964900381411603786489379993039402070494385524186478211475190845664711141714814686021209903311218466247417853231670486105653654069565992130968724589538251843538949480986449682098236777633194432657406826423941201601468003841016743329792 >>> (9 * s) % 2 ^ 9

/-- The table of Ncode 3: entry s in the bits 12 * s.. of one number. -/
def tab3 (s : ℕ) : ℕ := 310753886569016619027618890383418732036312011151041122864078274900107505390859216002690781425903945425948898409455556403193409077023074619363045971912914217468930026587001922080889282650141728013797384327452886447539736429646421460714484307135684403144963666335612086270930961412359932323161020802973415097590221581812449317059200741263091873531231621078847381873570351333215025717419516234855719450026780502098275565624535582718443203221144521311669873552699229659436164145677940837183358650240017852563265246851566100530024740015548774603151691309019016524756794576253347486020212383638652966895349678437856403838290184870382457062158795467322279679139223348259767479277896767638180305860417524313707273936718327263398413301704060308517301087979312121464262667011997543496720034425801375088750537312583956113360462307969768024900315367068259695646564086741837276802678933770323807032511169450322951026068906432539334092761938627283587141083072216526406670689932326033945389530689217152435636460932634104665752790957046626657612392225864405509124860531563520358185374130250588063118470282059270169278286991566616802691133499894631191761641798286265666856846712085155171081932166519163978575192718853806741983414220952625709469664461625879498109585324241626317977591669172192926552857587500527582311190331389203416615830604455537825755819898766180106771341106331472949056229804934404724597975810335930773781977093007631294117790225349473964704708468296945148857951128729024649287651247067206762350013206346718532570652890761253942576731770703784453392478179273822909257872184757431665106635697997620379326285077461898972483935737845681389286774459500336288632450603090631523339060800142855116793628573314729552496732716304186519475030854861183917674106682496939650767144880881958576172491851374923846997874516986970130920942556031111201975987369440313131866119420430059596758179711949160505225590031657880186396425526287943683646368818096686887938964026970491395830788443350592312822084665370163462775390787635293172241553103499219204980783358510110348487754614409479213257578059076949314429344888691801298276586777532482713344018983125525622534276255002124006255879383577283422196269860758300079741003465494774095794646348494153684438111806668524975466049251243120068857383440038602652094864517221591976378502807054738819907760601721600489676659399978015894276143086157447257448251527447812657062429156415652483788984771721345075832027717163162797088366697670096711505350231490605819056242150695123230663579968175051051379866034137131639216398026823374622300984041073714452264127746599128160882666074275059965824681542472901176078391636512843922842634200680005861714857022864366846050460008559652785645433737954170120021284033115819232614600907146474639483623123288187847197638134498784727551444328124195336891221526295017875066454004909721560958833741320653397730322540771816767488 >>> (12 * s) % 2 ^ 12

/-- The states reachable from a first row. -/
def reach (s : ℕ) : Bool := 939520961486252500040715200907002932637331936703156695773614999411293500202560517851671576155915271713318745542594294815753079337123590673595101771031866032650935588409754708230602011921861572409249702474207649064004644425903086728883733505 >>> s % 2 == 1

/-- exrT agrees with exr on all rows above, current rows and rows below. -/
def xcheck : Bool :=
  (List.range 10).all fun qc => (List.range 27).all fun cc =>
    (List.range 10).all fun wc => exrN (decU qc) (dig cc) (decW wc) == exrT qc cc wc

set_option maxRecDepth 100000 in
theorem xcheck_ok : xcheck = true := by
  decide +kernel

/-- The recurrence of order 2 on the reachable states. -/
def crec : Bool := (List.range 810).all fun s =>
  !(reach s) || ((tab3 s : ℤ) == (14 : ℤ) * (tab2 s : ℤ) + (8 : ℤ) * (tab1 s : ℤ))

set_option maxRecDepth 100000 in
theorem crec_ok : crec = true := by
  decide +kernel

/-- The successors of reachable states are in range and reachable. -/
def cclos : Bool := (List.range 810).all fun s => !(reach s) || (List.range 27).all fun rc =>
  !(guardB s rc) || (decide (succS s rc < 810) && reach (succS s rc))

set_option maxRecDepth 100000 in
theorem cclos_ok : cclos = true := by
  decide +kernel

/-- The first states are in range and reachable. -/
def cinit : Bool := (List.range 27).all fun cc =>
  !(rgsC 0 cc) || (reach (enc 0 cc (limC 0 cc) 0) && decide (enc 0 cc (limC 0 cc) 0 < 810))

set_option maxRecDepth 100000 in
theorem cinit_ok : cinit = true := by
  decide +kernel

def c0 : Bool := (List.range 810).all fun s =>
  !(reach s) || (tab0 s == if exrT (qcOf s) (ccOf s) 0 + eOf s = 0 then 1 else 0)

set_option maxRecDepth 100000 in
theorem c0_ok : c0 = true := by
  decide +kernel

def c1 : Bool := (List.range 810).all fun s =>
  !(reach s) || (tab1 s ==
    (if guardB s 0 = true then tab0 (succS s 0) else 0) +
    (if guardB s 1 = true then tab0 (succS s 1) else 0) +
    (if guardB s 2 = true then tab0 (succS s 2) else 0) +
    (if guardB s 3 = true then tab0 (succS s 3) else 0) +
    (if guardB s 4 = true then tab0 (succS s 4) else 0) +
    (if guardB s 5 = true then tab0 (succS s 5) else 0) +
    (if guardB s 6 = true then tab0 (succS s 6) else 0) +
    (if guardB s 7 = true then tab0 (succS s 7) else 0) +
    (if guardB s 8 = true then tab0 (succS s 8) else 0) +
    (if guardB s 9 = true then tab0 (succS s 9) else 0) +
    (if guardB s 10 = true then tab0 (succS s 10) else 0) +
    (if guardB s 11 = true then tab0 (succS s 11) else 0) +
    (if guardB s 12 = true then tab0 (succS s 12) else 0) +
    (if guardB s 13 = true then tab0 (succS s 13) else 0) +
    (if guardB s 14 = true then tab0 (succS s 14) else 0) +
    (if guardB s 15 = true then tab0 (succS s 15) else 0) +
    (if guardB s 16 = true then tab0 (succS s 16) else 0) +
    (if guardB s 17 = true then tab0 (succS s 17) else 0) +
    (if guardB s 18 = true then tab0 (succS s 18) else 0) +
    (if guardB s 19 = true then tab0 (succS s 19) else 0) +
    (if guardB s 20 = true then tab0 (succS s 20) else 0) +
    (if guardB s 21 = true then tab0 (succS s 21) else 0) +
    (if guardB s 22 = true then tab0 (succS s 22) else 0) +
    (if guardB s 23 = true then tab0 (succS s 23) else 0) +
    (if guardB s 24 = true then tab0 (succS s 24) else 0) +
    (if guardB s 25 = true then tab0 (succS s 25) else 0) +
    (if guardB s 26 = true then tab0 (succS s 26) else 0))

set_option maxRecDepth 100000 in
theorem c1_ok : c1 = true := by
  decide +kernel

def c2 : Bool := (List.range 810).all fun s =>
  !(reach s) || (tab2 s ==
    (if guardB s 0 = true then tab1 (succS s 0) else 0) +
    (if guardB s 1 = true then tab1 (succS s 1) else 0) +
    (if guardB s 2 = true then tab1 (succS s 2) else 0) +
    (if guardB s 3 = true then tab1 (succS s 3) else 0) +
    (if guardB s 4 = true then tab1 (succS s 4) else 0) +
    (if guardB s 5 = true then tab1 (succS s 5) else 0) +
    (if guardB s 6 = true then tab1 (succS s 6) else 0) +
    (if guardB s 7 = true then tab1 (succS s 7) else 0) +
    (if guardB s 8 = true then tab1 (succS s 8) else 0) +
    (if guardB s 9 = true then tab1 (succS s 9) else 0) +
    (if guardB s 10 = true then tab1 (succS s 10) else 0) +
    (if guardB s 11 = true then tab1 (succS s 11) else 0) +
    (if guardB s 12 = true then tab1 (succS s 12) else 0) +
    (if guardB s 13 = true then tab1 (succS s 13) else 0) +
    (if guardB s 14 = true then tab1 (succS s 14) else 0) +
    (if guardB s 15 = true then tab1 (succS s 15) else 0) +
    (if guardB s 16 = true then tab1 (succS s 16) else 0) +
    (if guardB s 17 = true then tab1 (succS s 17) else 0) +
    (if guardB s 18 = true then tab1 (succS s 18) else 0) +
    (if guardB s 19 = true then tab1 (succS s 19) else 0) +
    (if guardB s 20 = true then tab1 (succS s 20) else 0) +
    (if guardB s 21 = true then tab1 (succS s 21) else 0) +
    (if guardB s 22 = true then tab1 (succS s 22) else 0) +
    (if guardB s 23 = true then tab1 (succS s 23) else 0) +
    (if guardB s 24 = true then tab1 (succS s 24) else 0) +
    (if guardB s 25 = true then tab1 (succS s 25) else 0) +
    (if guardB s 26 = true then tab1 (succS s 26) else 0))

set_option maxRecDepth 100000 in
theorem c2_ok : c2 = true := by
  decide +kernel

def c3 : Bool := (List.range 810).all fun s =>
  !(reach s) || (tab3 s ==
    (if guardB s 0 = true then tab2 (succS s 0) else 0) +
    (if guardB s 1 = true then tab2 (succS s 1) else 0) +
    (if guardB s 2 = true then tab2 (succS s 2) else 0) +
    (if guardB s 3 = true then tab2 (succS s 3) else 0) +
    (if guardB s 4 = true then tab2 (succS s 4) else 0) +
    (if guardB s 5 = true then tab2 (succS s 5) else 0) +
    (if guardB s 6 = true then tab2 (succS s 6) else 0) +
    (if guardB s 7 = true then tab2 (succS s 7) else 0) +
    (if guardB s 8 = true then tab2 (succS s 8) else 0) +
    (if guardB s 9 = true then tab2 (succS s 9) else 0) +
    (if guardB s 10 = true then tab2 (succS s 10) else 0) +
    (if guardB s 11 = true then tab2 (succS s 11) else 0) +
    (if guardB s 12 = true then tab2 (succS s 12) else 0) +
    (if guardB s 13 = true then tab2 (succS s 13) else 0) +
    (if guardB s 14 = true then tab2 (succS s 14) else 0) +
    (if guardB s 15 = true then tab2 (succS s 15) else 0) +
    (if guardB s 16 = true then tab2 (succS s 16) else 0) +
    (if guardB s 17 = true then tab2 (succS s 17) else 0) +
    (if guardB s 18 = true then tab2 (succS s 18) else 0) +
    (if guardB s 19 = true then tab2 (succS s 19) else 0) +
    (if guardB s 20 = true then tab2 (succS s 20) else 0) +
    (if guardB s 21 = true then tab2 (succS s 21) else 0) +
    (if guardB s 22 = true then tab2 (succS s 22) else 0) +
    (if guardB s 23 = true then tab2 (succS s 23) else 0) +
    (if guardB s 24 = true then tab2 (succS s 24) else 0) +
    (if guardB s 25 = true then tab2 (succS s 25) else 0) +
    (if guardB s 26 = true then tab2 (succS s 26) else 0))

set_option maxRecDepth 100000 in
theorem c3_ok : c3 = true := by
  decide +kernel

def cval0 : Bool :=
    (if rgsC 0 0 = true then tab0 (enc 0 0 (limC 0 0) 0) else 0) +
    (if rgsC 0 1 = true then tab0 (enc 0 1 (limC 0 1) 0) else 0) +
    (if rgsC 0 2 = true then tab0 (enc 0 2 (limC 0 2) 0) else 0) +
    (if rgsC 0 3 = true then tab0 (enc 0 3 (limC 0 3) 0) else 0) +
    (if rgsC 0 4 = true then tab0 (enc 0 4 (limC 0 4) 0) else 0) +
    (if rgsC 0 5 = true then tab0 (enc 0 5 (limC 0 5) 0) else 0) +
    (if rgsC 0 6 = true then tab0 (enc 0 6 (limC 0 6) 0) else 0) +
    (if rgsC 0 7 = true then tab0 (enc 0 7 (limC 0 7) 0) else 0) +
    (if rgsC 0 8 = true then tab0 (enc 0 8 (limC 0 8) 0) else 0) +
    (if rgsC 0 9 = true then tab0 (enc 0 9 (limC 0 9) 0) else 0) +
    (if rgsC 0 10 = true then tab0 (enc 0 10 (limC 0 10) 0) else 0) +
    (if rgsC 0 11 = true then tab0 (enc 0 11 (limC 0 11) 0) else 0) +
    (if rgsC 0 12 = true then tab0 (enc 0 12 (limC 0 12) 0) else 0) +
    (if rgsC 0 13 = true then tab0 (enc 0 13 (limC 0 13) 0) else 0) +
    (if rgsC 0 14 = true then tab0 (enc 0 14 (limC 0 14) 0) else 0) +
    (if rgsC 0 15 = true then tab0 (enc 0 15 (limC 0 15) 0) else 0) +
    (if rgsC 0 16 = true then tab0 (enc 0 16 (limC 0 16) 0) else 0) +
    (if rgsC 0 17 = true then tab0 (enc 0 17 (limC 0 17) 0) else 0) +
    (if rgsC 0 18 = true then tab0 (enc 0 18 (limC 0 18) 0) else 0) +
    (if rgsC 0 19 = true then tab0 (enc 0 19 (limC 0 19) 0) else 0) +
    (if rgsC 0 20 = true then tab0 (enc 0 20 (limC 0 20) 0) else 0) +
    (if rgsC 0 21 = true then tab0 (enc 0 21 (limC 0 21) 0) else 0) +
    (if rgsC 0 22 = true then tab0 (enc 0 22 (limC 0 22) 0) else 0) +
    (if rgsC 0 23 = true then tab0 (enc 0 23 (limC 0 23) 0) else 0) +
    (if rgsC 0 24 = true then tab0 (enc 0 24 (limC 0 24) 0) else 0) +
    (if rgsC 0 25 = true then tab0 (enc 0 25 (limC 0 25) 0) else 0) +
    (if rgsC 0 26 = true then tab0 (enc 0 26 (limC 0 26) 0) else 0) == 4

set_option maxRecDepth 100000 in
theorem cval0_ok : cval0 = true := by
  decide +kernel

def cval1 : Bool :=
    (if rgsC 0 0 = true then tab1 (enc 0 0 (limC 0 0) 0) else 0) +
    (if rgsC 0 1 = true then tab1 (enc 0 1 (limC 0 1) 0) else 0) +
    (if rgsC 0 2 = true then tab1 (enc 0 2 (limC 0 2) 0) else 0) +
    (if rgsC 0 3 = true then tab1 (enc 0 3 (limC 0 3) 0) else 0) +
    (if rgsC 0 4 = true then tab1 (enc 0 4 (limC 0 4) 0) else 0) +
    (if rgsC 0 5 = true then tab1 (enc 0 5 (limC 0 5) 0) else 0) +
    (if rgsC 0 6 = true then tab1 (enc 0 6 (limC 0 6) 0) else 0) +
    (if rgsC 0 7 = true then tab1 (enc 0 7 (limC 0 7) 0) else 0) +
    (if rgsC 0 8 = true then tab1 (enc 0 8 (limC 0 8) 0) else 0) +
    (if rgsC 0 9 = true then tab1 (enc 0 9 (limC 0 9) 0) else 0) +
    (if rgsC 0 10 = true then tab1 (enc 0 10 (limC 0 10) 0) else 0) +
    (if rgsC 0 11 = true then tab1 (enc 0 11 (limC 0 11) 0) else 0) +
    (if rgsC 0 12 = true then tab1 (enc 0 12 (limC 0 12) 0) else 0) +
    (if rgsC 0 13 = true then tab1 (enc 0 13 (limC 0 13) 0) else 0) +
    (if rgsC 0 14 = true then tab1 (enc 0 14 (limC 0 14) 0) else 0) +
    (if rgsC 0 15 = true then tab1 (enc 0 15 (limC 0 15) 0) else 0) +
    (if rgsC 0 16 = true then tab1 (enc 0 16 (limC 0 16) 0) else 0) +
    (if rgsC 0 17 = true then tab1 (enc 0 17 (limC 0 17) 0) else 0) +
    (if rgsC 0 18 = true then tab1 (enc 0 18 (limC 0 18) 0) else 0) +
    (if rgsC 0 19 = true then tab1 (enc 0 19 (limC 0 19) 0) else 0) +
    (if rgsC 0 20 = true then tab1 (enc 0 20 (limC 0 20) 0) else 0) +
    (if rgsC 0 21 = true then tab1 (enc 0 21 (limC 0 21) 0) else 0) +
    (if rgsC 0 22 = true then tab1 (enc 0 22 (limC 0 22) 0) else 0) +
    (if rgsC 0 23 = true then tab1 (enc 0 23 (limC 0 23) 0) else 0) +
    (if rgsC 0 24 = true then tab1 (enc 0 24 (limC 0 24) 0) else 0) +
    (if rgsC 0 25 = true then tab1 (enc 0 25 (limC 0 25) 0) else 0) +
    (if rgsC 0 26 = true then tab1 (enc 0 26 (limC 0 26) 0) else 0) == 59

set_option maxRecDepth 100000 in
theorem cval1_ok : cval1 = true := by
  decide +kernel

def cval2 : Bool :=
    (if rgsC 0 0 = true then tab2 (enc 0 0 (limC 0 0) 0) else 0) +
    (if rgsC 0 1 = true then tab2 (enc 0 1 (limC 0 1) 0) else 0) +
    (if rgsC 0 2 = true then tab2 (enc 0 2 (limC 0 2) 0) else 0) +
    (if rgsC 0 3 = true then tab2 (enc 0 3 (limC 0 3) 0) else 0) +
    (if rgsC 0 4 = true then tab2 (enc 0 4 (limC 0 4) 0) else 0) +
    (if rgsC 0 5 = true then tab2 (enc 0 5 (limC 0 5) 0) else 0) +
    (if rgsC 0 6 = true then tab2 (enc 0 6 (limC 0 6) 0) else 0) +
    (if rgsC 0 7 = true then tab2 (enc 0 7 (limC 0 7) 0) else 0) +
    (if rgsC 0 8 = true then tab2 (enc 0 8 (limC 0 8) 0) else 0) +
    (if rgsC 0 9 = true then tab2 (enc 0 9 (limC 0 9) 0) else 0) +
    (if rgsC 0 10 = true then tab2 (enc 0 10 (limC 0 10) 0) else 0) +
    (if rgsC 0 11 = true then tab2 (enc 0 11 (limC 0 11) 0) else 0) +
    (if rgsC 0 12 = true then tab2 (enc 0 12 (limC 0 12) 0) else 0) +
    (if rgsC 0 13 = true then tab2 (enc 0 13 (limC 0 13) 0) else 0) +
    (if rgsC 0 14 = true then tab2 (enc 0 14 (limC 0 14) 0) else 0) +
    (if rgsC 0 15 = true then tab2 (enc 0 15 (limC 0 15) 0) else 0) +
    (if rgsC 0 16 = true then tab2 (enc 0 16 (limC 0 16) 0) else 0) +
    (if rgsC 0 17 = true then tab2 (enc 0 17 (limC 0 17) 0) else 0) +
    (if rgsC 0 18 = true then tab2 (enc 0 18 (limC 0 18) 0) else 0) +
    (if rgsC 0 19 = true then tab2 (enc 0 19 (limC 0 19) 0) else 0) +
    (if rgsC 0 20 = true then tab2 (enc 0 20 (limC 0 20) 0) else 0) +
    (if rgsC 0 21 = true then tab2 (enc 0 21 (limC 0 21) 0) else 0) +
    (if rgsC 0 22 = true then tab2 (enc 0 22 (limC 0 22) 0) else 0) +
    (if rgsC 0 23 = true then tab2 (enc 0 23 (limC 0 23) 0) else 0) +
    (if rgsC 0 24 = true then tab2 (enc 0 24 (limC 0 24) 0) else 0) +
    (if rgsC 0 25 = true then tab2 (enc 0 25 (limC 0 25) 0) else 0) +
    (if rgsC 0 26 = true then tab2 (enc 0 26 (limC 0 26) 0) else 0) == 858

set_option maxRecDepth 100000 in
theorem cval2_ok : cval2 = true := by
  decide +kernel


theorem exr_eq (p : Option (Fin 3 → Fin 3)) (c : Fin 3 → Fin 3) (w : Option (Fin 3 → Fin 3)) :
    exr p c w = exrT (projIdx (encO p)) (code c) (projW (encO w)) := by
  have h := xcheck_ok
  unfold xcheck at h
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have := h (projIdx (encO p)) (projIdx_lt p) (code c) (code_lt c) (projW (encO w)) (projW_lt w)
  rw [dig_code, ← mapU_eq, ← mapW_eq, ← exr_N, ← exr_keep] at this
  exact this

theorem rgsRow_dig (lim cc : ℕ) : rgsRow lim (dig cc) = rgsC lim cc := by
  simp [rgsRow, rgsC, dig]

theorem limNext_dig (lim cc : ℕ) : limNext lim (dig cc) = limC lim cc := by
  simp [limNext, limC, dig]

theorem dec_enc (qc cc lim e : ℕ) (h1 : cc < 27) (h2 : 1 ≤ lim) (h3 : lim ≤ 3) (h4 : e ≤ 0) :
    qcOf (enc qc cc lim e) = qc ∧ ccOf (enc qc cc lim e) = cc ∧ limOf (enc qc cc lim e) = lim ∧
      eOf (enc qc cc lim e) = e := by
  unfold qcOf ccOf limOf eOf enc
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem N_code (m : ℕ) : ∀ (p : Option (Fin 3 → Fin 3)) (c : Fin 3 → Fin 3) (lim e : ℕ),
    1 ≤ lim → lim ≤ 3 → e ≤ 0 →
      N p c lim e m = Ncode (enc (projIdx (encO p)) (code c) lim e) m := by
  induction m with
  | zero =>
    intro p c lim e h1 h2 h3
    obtain ⟨d1, d2, d3, d4⟩ := dec_enc (projIdx (encO p)) (code c) lim e (code_lt c) h1 h2 h3
    rw [N_zero, exr_eq, Ncode, d1, d2, d4]
    rfl
  | succ m ih =>
    intro p c lim e h1 h2 h3
    obtain ⟨d1, d2, d3, d4⟩ := dec_enc (projIdx (encO p)) (code c) lim e (code_lt c) h1 h2 h3
    rw [N_succ p c lim e m h2, sum_dig, Ncode_succ]
    refine sum_congr rfl (fun rc hrc => ?_)
    rw [mem_range] at hrc
    have hx : exr p c (some (dig rc)) = exrT (projIdx (encO p)) (code c) (1 + pcodeW rc) := by
      rw [exr_eq]
      simp [encO, projW, code_dig rc hrc]
    unfold guardB succS
    rw [rgsRow_dig, limNext_dig, hx, d1, d2, d3, d4]
    have hl1 : 1 ≤ limC lim rc := by unfold limC; omega
    have hl2 : limC lim rc ≤ 3 := by unfold limC; omega
    have hpi : projIdx (encO (some c)) = 1 + pcodeC (code c) := by
      simp [projIdx, encO]
    by_cases hg : rgsC lim rc = true
    · by_cases he : e + exrT (projIdx (encO p)) (code c) (1 + pcodeW rc) ≤ 0
      · rw [if_pos hg, if_pos (by simp [hg, he]), ih (some c) (dig rc) _ _ hl1 hl2 he, hpi,
          code_dig rc hrc]
      · rw [if_pos hg, if_neg (by simp [he]), N_over _ _ _ _ _ (by omega)]
    · rw [if_neg hg, if_neg (by simp [hg])]

theorem succ_ok (s rc : ℕ) (hs : s < 810) (hrc : rc < 27) (hg : guardB s rc = true)
    (hr : reach s = true) : succS s rc < 810 ∧ reach (succS s rc) = true := by
  have h := cclos_ok
  unfold cclos at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h s hs with h' | h'
  · rw [hr] at h'
    exact absurd h' (by decide)
  · rcases h' rc hrc with h'' | h''
    · rw [hg] at h''
      exact absurd h'' (by decide)
    · exact h''

theorem init_ok (cc : ℕ) (hcc : cc < 27) (hg : rgsC 0 cc = true) :
    enc 0 cc (limC 0 cc) 0 < 810 ∧ reach (enc 0 cc (limC 0 cc) 0) = true := by
  have h := cinit_ok
  unfold cinit at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h cc hcc with h' | h'
  · rw [hg] at h'
    exact absurd h' (by decide)
  · exact ⟨h'.2, h'.1⟩

theorem tab_eq0 (s : ℕ) (hs : s < 810) (hr : reach s = true) : Ncode s 0 = tab0 s := by
  have h := c0_ok
  unfold c0 at h
  rw [List.all_eq_true] at h
  have hc := h s (List.mem_range.mpr hs)
  rw [hr, Bool.not_true, Bool.false_or, beq_iff_eq] at hc
  rw [hc]
  rfl

theorem tab_eq1 (s : ℕ) (hs : s < 810) (hr : reach s = true) :
    Ncode s 1 = tab1 s := by
  have h := c1_ok
  unfold c1 at h
  rw [List.all_eq_true] at h
  have hc := h s (List.mem_range.mpr hs)
  rw [hr, Bool.not_true, Bool.false_or, beq_iff_eq] at hc
  rw [hc, Ncode_succ]
  have e : ∀ rc ∈ range 27, (if guardB s rc = true then Ncode (succS s rc) 0 else 0) =
      (if guardB s rc = true then tab0 (succS s rc) else 0) := by
    intro rc hrc
    split_ifs with hg
    · exact tab_eq0 _ (succ_ok s rc hs (mem_range.mp hrc) hg hr).1
        (succ_ok s rc hs (mem_range.mp hrc) hg hr).2
    · rfl
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

theorem tab_eq2 (s : ℕ) (hs : s < 810) (hr : reach s = true) :
    Ncode s 2 = tab2 s := by
  have h := c2_ok
  unfold c2 at h
  rw [List.all_eq_true] at h
  have hc := h s (List.mem_range.mpr hs)
  rw [hr, Bool.not_true, Bool.false_or, beq_iff_eq] at hc
  rw [hc, Ncode_succ]
  have e : ∀ rc ∈ range 27, (if guardB s rc = true then Ncode (succS s rc) 1 else 0) =
      (if guardB s rc = true then tab1 (succS s rc) else 0) := by
    intro rc hrc
    split_ifs with hg
    · exact tab_eq1 _ (succ_ok s rc hs (mem_range.mp hrc) hg hr).1
        (succ_ok s rc hs (mem_range.mp hrc) hg hr).2
    · rfl
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

theorem tab_eq3 (s : ℕ) (hs : s < 810) (hr : reach s = true) :
    Ncode s 3 = tab3 s := by
  have h := c3_ok
  unfold c3 at h
  rw [List.all_eq_true] at h
  have hc := h s (List.mem_range.mpr hs)
  rw [hr, Bool.not_true, Bool.false_or, beq_iff_eq] at hc
  rw [hc, Ncode_succ]
  have e : ∀ rc ∈ range 27, (if guardB s rc = true then Ncode (succS s rc) 2 else 0) =
      (if guardB s rc = true then tab2 (succS s rc) else 0) := by
    intro rc hrc
    split_ifs with hg
    · exact tab_eq2 _ (succ_ok s rc hs (mem_range.mp hrc) hg hr).1
        (succ_ok s rc hs (mem_range.mp hrc) hg hr).2
    · rfl
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

/-- The recurrence of order 2 of the continuation counts, on every reachable state, from
m = 1. -/
theorem Ncode_rec (m : ℕ) : ∀ s, s < 810 → reach s = true →
    (Ncode s (m + 3) : ℤ) = (14 : ℤ) * (Ncode s (m + 2) : ℤ) + (8 : ℤ) * (Ncode s (m + 1) : ℤ) := by
  induction m with
  | zero =>
    intro s hs hr
    simp only [zero_add]
    rw [tab_eq3 s hs hr, tab_eq2 s hs hr, tab_eq1 s hs hr]
    have h := crec_ok
    unfold crec at h
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
      beq_iff_eq] at h
    rcases h s hs with h' | h'
    · rw [hr] at h'
      exact absurd h' (by decide)
    · exact h'
  | succ m ih =>
    intro s hs hr
    show (Ncode s (m + 1 + 3) : ℤ) = (14 : ℤ) * (Ncode s (m + 1 + 2) : ℤ) + (8 : ℤ) * (Ncode s (m + 1 + 1) : ℤ)
    rw [Ncode_succ s (m + 3), Ncode_succ s (m + 2), Ncode_succ s (m + 1)]
    push_cast
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine sum_congr rfl (fun rc hrc => ?_)
    split_ifs with hg
    · exact ih _ (succ_ok s rc hs (mem_range.mp hrc) hg hr).1 (succ_ok s rc hs (mem_range.mp hrc) hg hr).2
    · simp

theorem a_code (n : ℕ) : a (n + 1) = ∑ cc ∈ range 27,
    if rgsC 0 cc = true then Ncode (enc 0 cc (limC 0 cc) 0) n else 0 := by
  rw [a_succ, sum_dig]
  refine sum_congr rfl (fun cc hcc => ?_)
  rw [mem_range] at hcc
  rw [rgsRow_dig, limNext_dig]
  split_ifs with hg
  · have hl1 : 1 ≤ limC 0 cc := by unfold limC; omega
    have hl2 : limC 0 cc ≤ 3 := by unfold limC; omega
    rw [N_code n none (dig cc) _ 0 hl1 hl2 (by norm_num), code_dig cc hcc]
    rfl
  · rfl

/-- The recurrence of order 2: a(n) for n >= 4. -/
theorem a_rec (m : ℕ) : (a (m + 4) : ℤ) = (14 : ℤ) * (a (m + 3) : ℤ) + (8 : ℤ) * (a (m + 2) : ℤ) := by
  rw [a_code (m + 3), a_code (m + 2), a_code (m + 1)]
  push_cast
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine sum_congr rfl (fun cc hcc => ?_)
  split_ifs with hg
  · exact Ncode_rec m _ (init_ok cc (mem_range.mp hcc) hg).1 (init_ok cc (mem_range.mp hcc) hg).2
  · simp

theorem v1 : a 1 = 4 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, a_code]
  have e : ∀ cc ∈ range 27, (if rgsC 0 cc = true then Ncode (enc 0 cc (limC 0 cc) 0) 0 else 0) =
      (if rgsC 0 cc = true then tab0 (enc 0 cc (limC 0 cc) 0) else 0) := by
    intro cc hcc
    split_ifs with hg
    · exact tab_eq0 _ (init_ok cc (mem_range.mp hcc) hg).1 (init_ok cc (mem_range.mp hcc) hg).2
    · rfl
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have h := cval0_ok
  unfold cval0 at h
  exact beq_iff_eq.mp h

theorem v2 : a 2 = 59 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, a_code]
  have e : ∀ cc ∈ range 27, (if rgsC 0 cc = true then Ncode (enc 0 cc (limC 0 cc) 0) 1 else 0) =
      (if rgsC 0 cc = true then tab1 (enc 0 cc (limC 0 cc) 0) else 0) := by
    intro cc hcc
    split_ifs with hg
    · exact tab_eq1 _ (init_ok cc (mem_range.mp hcc) hg).1 (init_ok cc (mem_range.mp hcc) hg).2
    · rfl
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have h := cval1_ok
  unfold cval1 at h
  exact beq_iff_eq.mp h

theorem v3 : a 3 = 858 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, a_code]
  have e : ∀ cc ∈ range 27, (if rgsC 0 cc = true then Ncode (enc 0 cc (limC 0 cc) 0) 2 else 0) =
      (if rgsC 0 cc = true then tab2 (enc 0 cc (limC 0 cc) 0) else 0) := by
    intro cc hcc
    split_ifs with hg
    · exact tab_eq2 _ (init_ok cc (mem_range.mp hcc) hg).1 (init_ok cc (mem_range.mp hcc) hg).2
    · rfl
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have h := cval2_ok
  unfold cval2 at h
  exact beq_iff_eq.mp h

/-- Barker's g.f., as A(x) (1 - 14 * X - 8 * X ^ 2) = X * (4 + 3 * X) in Z[[x]], with A(x) = Sum_{n >= 1} a(n) x^n. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - 14 * X - 8 * X ^ 2) = X * (4 + 3 * X) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (1 - 14 * X - 8 * X ^ 2) = A - C 14 * (A * X ^ 1) - C 8 * (A * X ^ 2) := by
    simp only [map_ofNat]; ring
  have e2 : (X * (4 + 3 * X) : ℤ⟦X⟧) = X ^ 1 * C 4 + X ^ 2 * C 3 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  rcases Nat.lt_or_ge n 4 with hn | hn
  · interval_cases n <;> simp [v1, v2, v3]
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 4 := ⟨n - 4, by omega⟩
    have h := a_rec q
    simp only [show q + 4 - 1 = q + 3 by omega, 
      show 1 ≤ q + 4 by omega, 
      show ¬ q + 3 = 0 by omega, 
      show q + 4 - 2 = q + 2 by omega, 
      show 2 ≤ q + 4 by omega, 
      show ¬ q + 2 = 0 by omega, 
      show ¬ q + 4 = 0 by omega, 
      show ¬ q + 4 = 1 by omega, 
      show ¬ q + 4 = 2 by omega,
      if_true, if_false]
    rw [h]
    ring

lemma dv (z : ℝ) : z / (16 * Real.sqrt 57) = z * Real.sqrt 57 / 912 := by
  have hs : Real.sqrt 57 ^ 2 = 57 := Real.sq_sqrt (by norm_num)
  rw [div_eq_div_iff (by positivity) (by norm_num)]
  linear_combination (-16 * z) * hs

/-- Barker's closed form, for n >= 1. -/
theorem closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℝ) = ((7 - Real.sqrt 57) ^ n * (-11 + 3 * Real.sqrt 57) +
      (7 + Real.sqrt 57) ^ n * (11 + 3 * Real.sqrt 57)) / (16 * Real.sqrt 57) := by
  have hs : Real.sqrt 57 ^ 2 = 57 := Real.sq_sqrt (by norm_num)
  rw [dv]
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 4 with hlt | hge
    · interval_cases n
      · rw [v1]
        push_cast
        linear_combination ((-4 / 57 : ℝ)) * hs
      · rw [v2]
        push_cast
        linear_combination ((-1 / 152 : ℝ) * Real.sqrt 57 ^ 2 + (-59 / 57 : ℝ)) * hs
      · rw [v3]
        push_cast
        linear_combination ((-37 / 228 : ℝ) * Real.sqrt 57 ^ 2 + (-286 / 19 : ℝ)) * hs
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      have hR : (a (k + 4) : ℝ) = (14 : ℝ) * (a (k + 3) : ℝ) + (8 : ℝ) * (a (k + 2) : ℝ) := by exact_mod_cast a_rec k
      rw [hR, ih (k + 3) (by omega) (by omega), ih (k + 2) (by omega) (by omega)]
      push_cast
      linear_combination ((-1 / 304 : ℝ) * Real.sqrt 57 ^ 4 * (7 - Real.sqrt 57) ^ k + (-1 / 304 : ℝ) * Real.sqrt 57 ^ 4 * (7 + Real.sqrt 57) ^ k + (53 / 912 : ℝ) * Real.sqrt 57 ^ 3 * (7 - Real.sqrt 57) ^ k + (-53 / 912 : ℝ) * Real.sqrt 57 ^ 3 * (7 + Real.sqrt 57) ^ k + (-301 / 912 : ℝ) * Real.sqrt 57 ^ 2 * (7 - Real.sqrt 57) ^ k + (-301 / 912 : ℝ) * Real.sqrt 57 ^ 2 * (7 + Real.sqrt 57) ^ k + (539 / 912 : ℝ) * Real.sqrt 57 * (7 - Real.sqrt 57) ^ k + (-539 / 912 : ℝ) * Real.sqrt 57 * (7 + Real.sqrt 57) ^ k) * hs

/-- Controls: the entry's data a(1..16). -/
theorem controls : a 1 = 4 ∧ a 2 = 59 ∧ a 3 = 858 ∧ a 4 = 12484 ∧ a 5 = 181640 ∧ a 6 = 2642832 ∧ a 7 = 38452768 ∧ a 8 = 559481408 ∧ a 9 = 8140361856 ∧ a 10 = 118440917248 ∧ a 11 = 1723295736320 ∧ a 12 = 25073667646464 ∧ a 13 = 364817712941056 ∧ a 14 = 5308037322346496 ∧ a 15 = 77231064216379392 ∧ a 16 = 1123699197608083456 := by
  have v4 : a 4 = 12484 := by
    have h : (a 4 : ℤ) = (14 : ℤ) * (a 3 : ℤ) + (8 : ℤ) * (a 2 : ℤ) := a_rec 0
    rw [v3, v2] at h
    omega
  have v5 : a 5 = 181640 := by
    have h : (a 5 : ℤ) = (14 : ℤ) * (a 4 : ℤ) + (8 : ℤ) * (a 3 : ℤ) := a_rec 1
    rw [v4, v3] at h
    omega
  have v6 : a 6 = 2642832 := by
    have h : (a 6 : ℤ) = (14 : ℤ) * (a 5 : ℤ) + (8 : ℤ) * (a 4 : ℤ) := a_rec 2
    rw [v5, v4] at h
    omega
  have v7 : a 7 = 38452768 := by
    have h : (a 7 : ℤ) = (14 : ℤ) * (a 6 : ℤ) + (8 : ℤ) * (a 5 : ℤ) := a_rec 3
    rw [v6, v5] at h
    omega
  have v8 : a 8 = 559481408 := by
    have h : (a 8 : ℤ) = (14 : ℤ) * (a 7 : ℤ) + (8 : ℤ) * (a 6 : ℤ) := a_rec 4
    rw [v7, v6] at h
    omega
  have v9 : a 9 = 8140361856 := by
    have h : (a 9 : ℤ) = (14 : ℤ) * (a 8 : ℤ) + (8 : ℤ) * (a 7 : ℤ) := a_rec 5
    rw [v8, v7] at h
    omega
  have v10 : a 10 = 118440917248 := by
    have h : (a 10 : ℤ) = (14 : ℤ) * (a 9 : ℤ) + (8 : ℤ) * (a 8 : ℤ) := a_rec 6
    rw [v9, v8] at h
    omega
  have v11 : a 11 = 1723295736320 := by
    have h : (a 11 : ℤ) = (14 : ℤ) * (a 10 : ℤ) + (8 : ℤ) * (a 9 : ℤ) := a_rec 7
    rw [v10, v9] at h
    omega
  have v12 : a 12 = 25073667646464 := by
    have h : (a 12 : ℤ) = (14 : ℤ) * (a 11 : ℤ) + (8 : ℤ) * (a 10 : ℤ) := a_rec 8
    rw [v11, v10] at h
    omega
  have v13 : a 13 = 364817712941056 := by
    have h : (a 13 : ℤ) = (14 : ℤ) * (a 12 : ℤ) + (8 : ℤ) * (a 11 : ℤ) := a_rec 9
    rw [v12, v11] at h
    omega
  have v14 : a 14 = 5308037322346496 := by
    have h : (a 14 : ℤ) = (14 : ℤ) * (a 13 : ℤ) + (8 : ℤ) * (a 12 : ℤ) := a_rec 10
    rw [v13, v12] at h
    omega
  have v15 : a 15 = 77231064216379392 := by
    have h : (a 15 : ℤ) = (14 : ℤ) * (a 14 : ℤ) + (8 : ℤ) * (a 13 : ℤ) := a_rec 11
    rw [v14, v13] at h
    omega
  have v16 : a 16 = 1123699197608083456 := by
    have h : (a 16 : ℤ) = (14 : ℤ) * (a 15 : ℤ) + (8 : ℤ) * (a 14 : ℤ) := a_rec 12
    rw [v15, v14] at h
    omega
  exact ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16⟩

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - 14 * X - 8 * X ^ 2) = X * (4 + 3 * X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) = ((7 - Real.sqrt 57) ^ n * (-11 + 3 * Real.sqrt 57) +
      (7 + Real.sqrt 57) ^ n * (11 + 3 * Real.sqrt 57)) / (16 * Real.sqrt 57) :=
  ⟨gf, closed⟩

end OMA.S_oeis_a280668

theorem OMA.solution : type_of% @OMA.S_oeis_a280668.main :=
  OMA.S_oeis_a280668.conjecture
