import OMAStatements.S_oeis_a277761

namespace OMA.S_oeis_a277761

open PowerSeries Finset






/-! ## Rows, their neighbors and the count of the elements meeting the condition -/

/-- The row r of the array x, counted from 0, or none outside the array. -/
def rowOpt {m : ℕ} (x : Fin m → Fin 2 → Fin 3) (r : ℤ) : Option (Fin 2 → Fin 3) :=
  if h : 0 ≤ r ∧ r < m then some (x ⟨r.toNat, by omega⟩) else none

/-- The element in column c of the optional row u. -/
def rc (u : Option (Fin 2 → Fin 3)) (c : ℤ) : Option (Fin 3) :=
  match u with
  | none => none
  | some v => if h : 0 ≤ c ∧ c < 2 then some (v ⟨c.toNat, by omega⟩) else none

theorem cell_eq (n : ℕ) (x : Fin n → Fin 2 → Fin 3) (r c : ℤ) :
    cell n x r c = rc (rowOpt x r) c := by
  unfold cell rowOpt
  by_cases h1 : 0 ≤ r ∧ r < n
  · rw [dif_pos h1]
    by_cases h2 : 0 ≤ c ∧ c < 2
    · rw [dif_pos ⟨h1.1, h1.2, h2.1, h2.2⟩]
      simp only [rc, dif_pos h2]
    · rw [dif_neg (fun h => h2 ⟨h.2.2.1, h.2.2.2⟩)]
      simp only [rc, dif_neg h2]
  · rw [dif_neg (fun h => h1 ⟨h.1, h.2.1⟩), dif_neg h1]
    rfl

theorem rowOpt_self {m : ℕ} (x : Fin m → Fin 2 → Fin 3) (i : Fin m) :
    rowOpt x (i : ℤ) = some (x i) := by
  have hi := i.isLt
  unfold rowOpt
  rw [dif_pos ⟨by omega, by omega⟩]
  simp

theorem rowOpt_neg {m : ℕ} (y : Fin m → Fin 2 → Fin 3) (r : ℤ) (h : r < 0) : rowOpt y r = none := by
  unfold rowOpt
  rw [dif_neg (by omega)]

/-- The values of the neighbors of the element in column j of the row v, with the row u above v
and the row w below it (none where there is no such row). -/
def nbrsR (u : Option (Fin 2 → Fin 3)) (v : Fin 2 → Fin 3) (w : Option (Fin 2 → Fin 3))
    (j : Fin 2) : List (Fin 3) :=
  [((-1 : ℤ), (-1 : ℤ)), (-1, 0), (-1, 1), (0, -1), (0, 1), (1, 0)].filterMap fun d =>
    rc (if d.1 = -1 then u else if d.1 = 0 then some v else w) (j + d.2)

theorem nbrs_eq (n : ℕ) (x : Fin n → Fin 2 → Fin 3) (i : Fin n) (j : Fin 2) :
    nbrs n x i j = nbrsR (rowOpt x ((i : ℤ) + -1)) (x i) (rowOpt x ((i : ℤ) + 1)) j := by
  unfold nbrs nbrsR
  refine List.filterMap_congr (fun d hd => ?_)
  rw [cell_eq]
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [rowOpt_self]

/-- The element in column j of the row v fails the condition of the entry. -/
def excR (u : Option (Fin 2 → Fin 3)) (v : Fin 2 → Fin 3) (w : Option (Fin 2 → Fin 3))
    (j : Fin 2) : Bool :=
  !(decide ((∃ y ∈ nbrsR u v w j, v j = y + 1) ∧ (∃ z ∈ nbrsR u v w j, v j = z - 1)))

theorem exc_iff (n : ℕ) (x : Fin n → Fin 2 → Fin 3) (i : Fin n) (j : Fin 2) :
    ¬ both n x i j ↔ excR (rowOpt x ((i : ℤ) + -1)) (x i) (rowOpt x ((i : ℤ) + 1)) j = true := by
  unfold both excR
  rw [nbrs_eq, Bool.not_eq_true', decide_eq_false_iff_not]

/-- The number of elements of the row v that fail the condition. -/
def exr (u : Option (Fin 2 → Fin 3)) (v : Fin 2 → Fin 3) (w : Option (Fin 2 → Fin 3)) : ℕ :=
  (if excR u v w 0 = true then 1 else 0) + (if excR u v w 1 = true then 1 else 0)

theorem all_iff (n : ℕ) (x : Fin n → Fin 2 → Fin 3) :
    (∀ i j, both n x i j) ↔
      ∑ i : Fin n, exr (rowOpt x ((i : ℤ) + -1)) (x i) (rowOpt x ((i : ℤ) + 1)) = 0 := by
  rw [Finset.sum_eq_zero_iff]
  refine forall_congr' (fun i => ?_)
  simp only [mem_univ, true_implies, exr, Fin.forall_fin_two]
  have h0 := exc_iff n x i 0
  have h1 := exc_iff n x i 1
  constructor
  · rintro ⟨g0, g1⟩
    rw [if_neg (fun h => h0.2 h g0), if_neg (fun h => h1.2 h g1)]
    rfl
  · intro h
    refine ⟨?_, ?_⟩
    · by_contra hc
      rw [if_pos (h0.1 hc)] at h
      omega
    · by_contra hc
      rw [if_pos (h1.1 hc)] at h
      omega

/-- The row r of y, with the optional row p in place of row -1. -/
def above {m : ℕ} (p : Option (Fin 2 → Fin 3)) (y : Fin m → Fin 2 → Fin 3) (r : ℤ) :
    Option (Fin 2 → Fin 3) :=
  if r = -1 then p else rowOpt y r

/-- The number of elements of y that meet the condition, with the optional row p above y. -/
def G {m : ℕ} (p : Option (Fin 2 → Fin 3)) (y : Fin m → Fin 2 → Fin 3) : ℕ :=
  ∑ i : Fin m, exr (above p y ((i : ℤ) + -1)) (y i) (above p y ((i : ℤ) + 1))

theorem G_none {m : ℕ} (x : Fin m → Fin 2 → Fin 3) :
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

theorem rowOpt_empty (y : Fin 0 → Fin 2 → Fin 3) (r : ℤ) : rowOpt y r = none := by
  unfold rowOpt
  rw [dif_neg (by omega)]

theorem rowOpt_cons {m : ℕ} (c : Fin 2 → Fin 3) (y : Fin m → Fin 2 → Fin 3) (r : ℤ) :
    rowOpt (Fin.cons c y : Fin (m + 1) → Fin 2 → Fin 3) r =
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

theorem above_cons {m : ℕ} (p : Option (Fin 2 → Fin 3)) (c : Fin 2 → Fin 3)
    (y : Fin m → Fin 2 → Fin 3) (r : ℤ) (h : r ≠ -1) :
    above p (Fin.cons c y : Fin (m + 1) → Fin 2 → Fin 3) r = above (some c) y (r - 1) := by
  unfold above
  rw [if_neg h, rowOpt_cons]
  by_cases h0 : r = 0
  · rw [if_pos h0, if_pos (by omega)]
  · rw [if_neg h0, if_neg (by omega)]

theorem G_cons {m : ℕ} (p : Option (Fin 2 → Fin 3)) (c : Fin 2 → Fin 3)
    (y : Fin m → Fin 2 → Fin 3) :
    G p (Fin.cons c y : Fin (m + 1) → Fin 2 → Fin 3) = exr p c (rowOpt y 0) + G (some c) y := by
  unfold G
  rw [Fin.sum_univ_succ]
  congr 1
  · have e0 : (((0 : Fin (m + 1)) : ℕ) : ℤ) = 0 := by simp
    rw [e0, zero_add, zero_add, Fin.cons_zero]
    have h1 : above p (Fin.cons c y : Fin (m + 1) → Fin 2 → Fin 3) (-1) = p := by
      unfold above
      rw [if_pos rfl]
    have h2 : above p (Fin.cons c y : Fin (m + 1) → Fin 2 → Fin 3) 1 = rowOpt y 0 := by
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
def orderedL {m : ℕ} (lim : ℕ) (y : Fin m → Fin 2 → Fin 3) : Prop :=
  ∀ i j, y i j ≠ 0 → (y i j).val ≤ lim ∨
    ∃ i' j', (i' < i ∨ (i' = i ∧ j' < j)) ∧ (y i' j').val + 1 = (y i j).val

instance {m : ℕ} (lim : ℕ) (y : Fin m → Fin 2 → Fin 3) : Decidable (orderedL lim y) := by
  unfold orderedL
  infer_instance

theorem ordered_iff (n : ℕ) (x : Fin n → Fin 2 → Fin 3) : ordered n x ↔ orderedL 0 x := by
  unfold ordered orderedL
  refine forall_congr' (fun i => forall_congr' (fun j => imp_congr_right (fun h => ?_)))
  have hx : ¬ (x i j).val ≤ 0 := fun h' => h (Fin.ext (Nat.le_zero.mp h'))
  constructor
  · exact Or.inr
  · rintro (h' | h')
    · exact absurd h' hx
    · exact h'

/-- The row r continues the order of new values after lim values: r 0 ≤ lim and
r 1 ≤ max lim (r 0 + 1). -/
def rgsRow (lim : ℕ) (r : Fin 2 → Fin 3) : Bool :=
  decide ((r 0).val ≤ lim ∧ (r 1).val ≤ max lim ((r 0).val + 1))

/-- The number of values introduced after the row r. -/
def limNext (lim : ℕ) (r : Fin 2 → Fin 3) : ℕ := max (max lim ((r 0).val + 1)) ((r 1).val + 1)

theorem orderedL_cons {m : ℕ} (lim : ℕ) (r : Fin 2 → Fin 3) (y : Fin m → Fin 2 → Fin 3) :
    orderedL lim (Fin.cons r y : Fin (m + 1) → Fin 2 → Fin 3) ↔
      rgsRow lim r = true ∧ orderedL (limNext lim r) y := by
  unfold orderedL rgsRow limNext
  rw [decide_eq_true_iff]
  constructor
  · intro H
    have hr0 : (r 0).val ≤ lim := by
      by_cases hz : r 0 = 0
      · rw [hz]
        exact Nat.zero_le _
      · rcases H 0 0 (by simpa using hz) with h | ⟨i', j', hij, _⟩
        · simpa using h
        · exfalso
          rcases hij with h | ⟨_, h'⟩
          · exact Fin.not_lt_zero _ h
          · exact Fin.not_lt_zero _ h'
    have hr1 : (r 1).val ≤ max lim ((r 0).val + 1) := by
      by_cases hz : r 1 = 0
      · rw [hz]
        exact Nat.zero_le _
      · rcases H 0 1 (by simpa using hz) with h | ⟨i', j', hij, hv⟩
        · simp only [Fin.cons_zero] at h
          omega
        · rcases hij with h | ⟨h, h'⟩
          · exact absurd h (Fin.not_lt_zero _)
          · subst h
            fin_cases j'
            · simp only [Fin.cons_zero] at hv
              simp only [Fin.zero_eta] at hv
              omega
            · exact absurd h' (by decide)
    refine ⟨⟨hr0, hr1⟩, fun i j hne => ?_⟩
    rcases H i.succ j (by simpa using hne) with h | ⟨i', j', hij, hv⟩
    · left
      simp only [Fin.cons_succ] at h
      omega
    · cases i' using Fin.cases with
      | zero =>
        left
        simp only [Fin.cons_zero, Fin.cons_succ] at hv
        fin_cases j' <;> simp only [Fin.zero_eta, Fin.mk_one] at hv <;> omega
      | succ i2 =>
        right
        refine ⟨i2, j', ?_, by simpa using hv⟩
        rcases hij with h | ⟨h, h'⟩
        · exact Or.inl (Fin.succ_lt_succ_iff.mp h)
        · exact Or.inr ⟨Fin.succ_injective _ h, h'⟩
  · rintro ⟨⟨hr0, hr1⟩, Hy⟩ i j hne
    cases i using Fin.cases with
    | zero =>
      simp only [Fin.cons_zero] at hne ⊢
      fin_cases j
      · left
        simpa using hr0
      · by_cases h : (r 1).val ≤ lim
        · left
          simpa using h
        · right
          refine ⟨0, 0, Or.inr ⟨rfl, by decide⟩, ?_⟩
          simp only [Fin.cons_zero, Fin.mk_one]
          omega
    | succ i1 =>
      simp only [Fin.cons_succ] at hne ⊢
      rcases Hy i1 j hne with h | ⟨i2, j', hij, hv⟩
      · by_cases h1 : (y i1 j).val ≤ lim
        · exact Or.inl h1
        · right
          by_cases h2 : (y i1 j).val = (r 0).val + 1
          · exact ⟨0, 0, Or.inl (Fin.succ_pos i1), by simp only [Fin.cons_zero]; omega⟩
          · exact ⟨0, 1, Or.inl (Fin.succ_pos i1), by simp only [Fin.cons_zero]; omega⟩
      · right
        refine ⟨i2.succ, j', ?_, by simpa using hv⟩
        rcases hij with h | ⟨h, h'⟩
        · exact Or.inl (Fin.succ_lt_succ_iff.mpr h)
        · exact Or.inr ⟨by rw [h], h'⟩

/-! ## The count by the first row and the continuation counts -/

/-- The ways to put m more rows below the current row c, with the optional row p above c, lim
values introduced up to c and e elements above c meeting the condition. -/
noncomputable def N (p : Option (Fin 2 → Fin 3)) (c : Fin 2 → Fin 3) (lim e m : ℕ) : ℕ :=
  ∑ y : Fin m → Fin 2 → Fin 3, if orderedL lim y ∧ G p (Fin.cons c y) + e = 0 then 1 else 0

theorem sum_cons {α : Type} [Fintype α] [DecidableEq α] (m : ℕ) (f : (Fin (m + 1) → α) → ℕ) :
    ∑ y : Fin (m + 1) → α, f y = ∑ r : α, ∑ y : Fin m → α, f (Fin.cons r y) := by
  rw [← (Fin.consEquiv fun _ => α).sum_comp, Fintype.sum_prod_type]
  rfl

theorem N_zero (p : Option (Fin 2 → Fin 3)) (c : Fin 2 → Fin 3) (lim e : ℕ) :
    N p c lim e 0 = if exr p c none + e = 0 then 1 else 0 := by
  have key : ∀ y : Fin 0 → Fin 2 → Fin 3,
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

theorem N_succ (p : Option (Fin 2 → Fin 3)) (c : Fin 2 → Fin 3) (lim e m : ℕ) :
    N p c lim e (m + 1) = ∑ r : Fin 2 → Fin 3,
      if rgsRow lim r = true then N (some c) r (limNext lim r) (e + exr p c (some r)) m else 0 := by
  unfold N
  rw [sum_cons]
  refine sum_congr rfl (fun r _ => ?_)
  have hG : ∀ y : Fin m → Fin 2 → Fin 3,
      G p (Fin.cons c (Fin.cons r y : Fin (m + 1) → Fin 2 → Fin 3)) =
        exr p c (some r) + G (some c) (Fin.cons r y) := by
    intro y
    rw [G_cons, rowOpt_cons, if_pos rfl]
  by_cases hr : rgsRow lim r = true
  · rw [if_pos hr]
    refine sum_congr rfl (fun y _ => ?_)
    have he : (exr p c (some r) + G (some c) (Fin.cons r y) + e = 0) ↔
        (G (some c) (Fin.cons r y) + (e + exr p c (some r)) = 0) := by omega
    simp only [hG, orderedL_cons, hr, true_and, he]
  · rw [if_neg hr]
    refine sum_eq_zero (fun y _ => ?_)
    simp [orderedL_cons, hr]

theorem N_over (p : Option (Fin 2 → Fin 3)) (c : Fin 2 → Fin 3) (lim e m : ℕ) (h : 0 < e) :
    N p c lim e m = 0 := by
  unfold N
  refine sum_eq_zero (fun y _ => ?_)
  rw [if_neg (fun h' => by have := h'.2; omega)]

theorem cond_iff (n : ℕ) (x : Fin n → Fin 2 → Fin 3) :
    ((∀ i j, both n x i j) ∧ ordered n x) ↔ (orderedL 0 x ∧ G none x + 0 = 0) := by
  rw [all_iff, ← G_none, ordered_iff, add_zero, and_comm]

theorem a_succ (n : ℕ) : a (n + 1) = ∑ c : Fin 2 → Fin 3,
    if rgsRow 0 c = true then N none c (limNext 0 c) 0 n else 0 := by
  have ha : a (n + 1) = ∑ x : Fin (n + 1) → Fin 2 → Fin 3,
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
    simp only [orderedL_cons, hc, true_and]
  · rw [if_neg hc]
    refine sum_eq_zero (fun y _ => ?_)
    simp [orderedL_cons, hc]

/-! ## Codes of rows and states -/

/-- The row with code c: column j holds the digit of 3 ^ j. -/
def dig (c : ℕ) : Fin 2 → Fin 3 := fun j => ⟨c / 3 ^ j.val % 3, Nat.mod_lt _ (by norm_num)⟩

/-- The code of the row r. -/
def code (r : Fin 2 → Fin 3) : ℕ := (r 0).val + 3 * (r 1).val

theorem dig_code (r : Fin 2 → Fin 3) : dig (code r) = r := by
  funext j
  apply Fin.ext
  have h0 := (r 0).isLt
  have h1 := (r 1).isLt
  fin_cases j <;> simp [dig, code] <;> omega

theorem code_lt (r : Fin 2 → Fin 3) : code r < 9 := by
  have h0 := (r 0).isLt
  have h1 := (r 1).isLt
  unfold code
  omega

theorem code_dig (c : ℕ) (h : c < 9) : code (dig c) = c := by
  simp [code, dig]
  omega

theorem sum_dig (g : (Fin 2 → Fin 3) → ℕ) : ∑ r, g r = ∑ c ∈ range 9, g (dig c) := by
  rw [← (finFunctionFinEquiv (m := 3) (n := 2)).symm.sum_comp]
  exact Fin.sum_univ_eq_sum_range (fun c => g (dig c)) _

/-- The code of an optional row: 0 for none, 1 + the row code otherwise. -/
def encO (p : Option (Fin 2 → Fin 3)) : ℕ :=
  match p with
  | none => 0
  | some r => 1 + code r

/-- The optional row of a code. -/
def decO (c : ℕ) : Option (Fin 2 → Fin 3) := if c = 0 then none else some (dig (c - 1))

theorem decO_encO (p : Option (Fin 2 → Fin 3)) : decO (encO p) = p := by
  cases p with
  | none => rfl
  | some r => simp [encO, decO, dig_code]

theorem encO_lt (p : Option (Fin 2 → Fin 3)) : encO p < 10 := by
  cases p with
  | none => simp [encO]
  | some r =>
    have := code_lt r
    simp only [encO]
    omega

/-- The code of the columns of the row with code cc that the row below reads (both columns). -/
def pcodeC (cc : ℕ) : ℕ := cc

/-- The table index of an optional row above: 0 for none, 1 + the code of its read columns. -/
def projIdx (pc : ℕ) : ℕ := if pc = 0 then 0 else 1 + pcodeC (pc - 1)

/-- The number of elements meeting the condition in the row with code cc, with the row above of
table index qc and the row below of code wc (0 for none, 1 + the row code otherwise). -/
def exrT (qc cc wc : ℕ) : ℕ := 47632231297465215717131365576121984538751478371043507054440163169981020155371954564443821099562472767500060094762310535383959340392723393567510664727626392717149763842738772642674150021631507458195988202529741807850288578866534663852276287988203776042760069216096271747883858260511447495860278337902551813728729293924948612970511174937309892193297020146724255620038428432933792180598666721285299301036434186661307051760086237879708298920421709868261517451715824970652864660984080638532924084077510407482460225404505630460033055205629186714282 >>> (2 * ((qc * 9 + cc) * 10 + wc)) % 4

/-- The first row condition on codes. -/
def rgsC (lim cc : ℕ) : Bool := decide (cc % 3 ≤ lim ∧ cc / 3 % 3 ≤ max lim (cc % 3 + 1))

/-- The values introduced after the row with code cc. -/
def limC (lim cc : ℕ) : ℕ := max (max lim (cc % 3 + 1)) (cc / 3 % 3 + 1)

/-- The code of the state (qc, cc, lim, e): row above (table index qc), current row cc, lim values
introduced, e elements above meeting the condition. -/
def enc (qc cc lim e : ℕ) : ℕ := ((qc * 9 + cc) * 3 + (lim - 1)) * 1 + e

def qcOf (s : ℕ) : ℕ := s / (9 * 3 * 1)

def ccOf (s : ℕ) : ℕ := s / (3 * 1) % 9

def limOf (s : ℕ) : ℕ := s / 1 % 3 + 1

def eOf (s : ℕ) : ℕ := s % 1

/-- The next row with code rc may follow the state s. -/
def guardB (s rc : ℕ) : Bool :=
  rgsC (limOf s) rc && decide (eOf s + exrT (qcOf s) (ccOf s) (1 + rc) ≤ 0)

/-- The state after the row with code rc. -/
def succS (s rc : ℕ) : ℕ :=
  enc (1 + pcodeC (ccOf s)) rc (limC (limOf s) rc) (eOf s + exrT (qcOf s) (ccOf s) (1 + rc))

/-- The continuation counts on state codes. -/
def Ncode : ℕ → ℕ → ℕ
  | s, 0 => if exrT (qcOf s) (ccOf s) 0 + eOf s = 0 then 1 else 0
  | s, m + 1 => ∑ rc ∈ range 9, if guardB s rc = true then Ncode (succS s rc) m else 0

theorem Ncode_succ (s m : ℕ) : Ncode s (m + 1) =
    ∑ rc ∈ range 9, if guardB s rc = true then Ncode (succS s rc) m else 0 := rfl

/-- The table of Ncode 0: entry s in the bits 1 * s.. of one number. -/
def tab0 (s : ℕ) : ℕ := 29400445832291325747531552575454074884978679822280358081002481996489348349952 >>> (1 * s) % 2 ^ 1

/-- The table of Ncode 1: entry s in the bits 3 * s.. of one number. -/
def tab1 (s : ℕ) : ℕ := 1670265833877712566308139709883414283017435794292457793076257906601911537075507396760359949727636619572559823617188217244720801343885348263743784659585976863857369847624478534393694440980230560803737519113097656045956053345305960226888876032 >>> (3 * s) % 2 ^ 3

/-- The table of Ncode 2: entry s in the bits 5 * s.. of one number. -/
def tab2 (s : ℕ) : ℕ := 46874590052550650676806842073458492191654584583250102242367241215768028900745271105051957312209660889538140549167941299681663796081647369464033429125080212185284266033795500553194821415426875312622437970976018737652771037675208944356187402050968091349022111782520138791742623058747509700355339812388393441629688914804607715616763539916458714431253424940451903248704553968259595991297095336806754287616 >>> (5 * s) % 2 ^ 5

/-- The table of Ncode 3: entry s in the bits 7 * s.. of one number. -/
def tab3 (s : ℕ) : ℕ := 4612965102027633008494078131336603956615716660372637824591622731286081740622795190308837913191714005670624447098846550427632691204640113944443237081136974501936226461872946935563069027919317968550300751786552365825765384945237668675748721270289831453248521708115496496793974810311752930434458198519829266677870949260860735353310638309982508797899700442698974106683626849133625002194089937345885240844842116198952615351279647477434288610347733973523359501752232281899347390981735689905398847258547708417140182216699953642137822269891668677838663046803993107890176 >>> (7 * s) % 2 ^ 7

/-- The states reachable from a first row. -/
def reach (s : ℕ) : Bool := 1084078622893822026182735439075624389867414530721060000698556032220370694792283137 >>> s % 2 == 1

/-- exrT agrees with exr on all rows above, current rows and rows below. -/
def xcheck : Bool :=
  (List.range 10).all fun pc => (List.range 9).all fun cc =>
    (List.range 10).all fun wc => exr (decO pc) (dig cc) (decO wc) == exrT (projIdx pc) cc wc

/-- The recurrence of order 3 on the reachable states. -/
def crec : Bool := (List.range 270).all fun s =>
  !(reach s) || ((tab3 s : ℤ) == (4 : ℤ) * (tab2 s : ℤ) + (6 : ℤ) * (tab1 s : ℤ) + (-12 : ℤ) * (tab0 s : ℤ))

/-- Successor states are in range, and reachable from reachable ones. -/
def cclos : Bool := (List.range 270).all fun s => (List.range 9).all fun rc =>
  !(guardB s rc) || (decide (succS s rc < 270) && (!(reach s) || reach (succS s rc)))

/-- The first states are in range and reachable. -/
def cinit : Bool := (List.range 9).all fun cc =>
  !(rgsC 0 cc) || (reach (enc 0 cc (limC 0 cc) 0) && decide (enc 0 cc (limC 0 cc) 0 < 270))

def c0 : Bool := (List.range 270).all fun s =>
  !(reach s) || (tab0 s == if exrT (qcOf s) (ccOf s) 0 + eOf s = 0 then 1 else 0)

def c1 : Bool := (List.range 270).all fun s =>
  !(reach s) || (tab1 s ==
    (if guardB s 0 = true then tab0 (succS s 0) else 0) +
    (if guardB s 1 = true then tab0 (succS s 1) else 0) +
    (if guardB s 2 = true then tab0 (succS s 2) else 0) +
    (if guardB s 3 = true then tab0 (succS s 3) else 0) +
    (if guardB s 4 = true then tab0 (succS s 4) else 0) +
    (if guardB s 5 = true then tab0 (succS s 5) else 0) +
    (if guardB s 6 = true then tab0 (succS s 6) else 0) +
    (if guardB s 7 = true then tab0 (succS s 7) else 0) +
    (if guardB s 8 = true then tab0 (succS s 8) else 0))

def c2 : Bool := (List.range 270).all fun s =>
  !(reach s) || (tab2 s ==
    (if guardB s 0 = true then tab1 (succS s 0) else 0) +
    (if guardB s 1 = true then tab1 (succS s 1) else 0) +
    (if guardB s 2 = true then tab1 (succS s 2) else 0) +
    (if guardB s 3 = true then tab1 (succS s 3) else 0) +
    (if guardB s 4 = true then tab1 (succS s 4) else 0) +
    (if guardB s 5 = true then tab1 (succS s 5) else 0) +
    (if guardB s 6 = true then tab1 (succS s 6) else 0) +
    (if guardB s 7 = true then tab1 (succS s 7) else 0) +
    (if guardB s 8 = true then tab1 (succS s 8) else 0))

def c3 : Bool := (List.range 270).all fun s =>
  !(reach s) || (tab3 s ==
    (if guardB s 0 = true then tab2 (succS s 0) else 0) +
    (if guardB s 1 = true then tab2 (succS s 1) else 0) +
    (if guardB s 2 = true then tab2 (succS s 2) else 0) +
    (if guardB s 3 = true then tab2 (succS s 3) else 0) +
    (if guardB s 4 = true then tab2 (succS s 4) else 0) +
    (if guardB s 5 = true then tab2 (succS s 5) else 0) +
    (if guardB s 6 = true then tab2 (succS s 6) else 0) +
    (if guardB s 7 = true then tab2 (succS s 7) else 0) +
    (if guardB s 8 = true then tab2 (succS s 8) else 0))

def cval0 : Bool :=
    (if rgsC 0 0 = true then tab0 (enc 0 0 (limC 0 0) 0) else 0) +
    (if rgsC 0 1 = true then tab0 (enc 0 1 (limC 0 1) 0) else 0) +
    (if rgsC 0 2 = true then tab0 (enc 0 2 (limC 0 2) 0) else 0) +
    (if rgsC 0 3 = true then tab0 (enc 0 3 (limC 0 3) 0) else 0) +
    (if rgsC 0 4 = true then tab0 (enc 0 4 (limC 0 4) 0) else 0) +
    (if rgsC 0 5 = true then tab0 (enc 0 5 (limC 0 5) 0) else 0) +
    (if rgsC 0 6 = true then tab0 (enc 0 6 (limC 0 6) 0) else 0) +
    (if rgsC 0 7 = true then tab0 (enc 0 7 (limC 0 7) 0) else 0) +
    (if rgsC 0 8 = true then tab0 (enc 0 8 (limC 0 8) 0) else 0) == 0

def cval1 : Bool :=
    (if rgsC 0 0 = true then tab1 (enc 0 0 (limC 0 0) 0) else 0) +
    (if rgsC 0 1 = true then tab1 (enc 0 1 (limC 0 1) 0) else 0) +
    (if rgsC 0 2 = true then tab1 (enc 0 2 (limC 0 2) 0) else 0) +
    (if rgsC 0 3 = true then tab1 (enc 0 3 (limC 0 3) 0) else 0) +
    (if rgsC 0 4 = true then tab1 (enc 0 4 (limC 0 4) 0) else 0) +
    (if rgsC 0 5 = true then tab1 (enc 0 5 (limC 0 5) 0) else 0) +
    (if rgsC 0 6 = true then tab1 (enc 0 6 (limC 0 6) 0) else 0) +
    (if rgsC 0 7 = true then tab1 (enc 0 7 (limC 0 7) 0) else 0) +
    (if rgsC 0 8 = true then tab1 (enc 0 8 (limC 0 8) 0) else 0) == 1

def cval2 : Bool :=
    (if rgsC 0 0 = true then tab2 (enc 0 0 (limC 0 0) 0) else 0) +
    (if rgsC 0 1 = true then tab2 (enc 0 1 (limC 0 1) 0) else 0) +
    (if rgsC 0 2 = true then tab2 (enc 0 2 (limC 0 2) 0) else 0) +
    (if rgsC 0 3 = true then tab2 (enc 0 3 (limC 0 3) 0) else 0) +
    (if rgsC 0 4 = true then tab2 (enc 0 4 (limC 0 4) 0) else 0) +
    (if rgsC 0 5 = true then tab2 (enc 0 5 (limC 0 5) 0) else 0) +
    (if rgsC 0 6 = true then tab2 (enc 0 6 (limC 0 6) 0) else 0) +
    (if rgsC 0 7 = true then tab2 (enc 0 7 (limC 0 7) 0) else 0) +
    (if rgsC 0 8 = true then tab2 (enc 0 8 (limC 0 8) 0) else 0) == 2

set_option maxRecDepth 100000 in
theorem tabs : (xcheck && (crec && (cclos && (cinit && (c0 && (c1 && (c2 && (c3 && (cval0 && (cval1 && (cval2))))))))))) = true := by
  decide +kernel

theorem tabs_split : xcheck = true ∧ crec = true ∧ cclos = true ∧ cinit = true ∧ c0 = true ∧ c1 = true ∧ c2 = true ∧ c3 = true ∧ cval0 = true ∧ cval1 = true ∧ cval2 = true := by
  have h := tabs
  simp only [Bool.and_eq_true] at h
  exact h


theorem exr_eq (p : Option (Fin 2 → Fin 3)) (c : Fin 2 → Fin 3) (w : Option (Fin 2 → Fin 3)) :
    exr p c w = exrT (projIdx (encO p)) (code c) (encO w) := by
  have h := tabs_split.1
  unfold xcheck at h
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have := h (encO p) (encO_lt p) (code c) (code_lt c) (encO w) (encO_lt w)
  rwa [decO_encO, dig_code, decO_encO] at this

theorem rgsRow_dig (lim cc : ℕ) : rgsRow lim (dig cc) = rgsC lim cc := by
  simp [rgsRow, rgsC, dig]

theorem limNext_dig (lim cc : ℕ) : limNext lim (dig cc) = limC lim cc := by
  simp [limNext, limC, dig]

theorem dec_enc (qc cc lim e : ℕ) (h1 : cc < 9) (h2 : 1 ≤ lim) (h3 : lim ≤ 3) (h4 : e ≤ 0) :
    qcOf (enc qc cc lim e) = qc ∧ ccOf (enc qc cc lim e) = cc ∧ limOf (enc qc cc lim e) = lim ∧
      eOf (enc qc cc lim e) = e := by
  unfold qcOf ccOf limOf eOf enc
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem N_code (m : ℕ) : ∀ (p : Option (Fin 2 → Fin 3)) (c : Fin 2 → Fin 3) (lim e : ℕ),
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
    rw [N_succ, sum_dig, Ncode_succ]
    refine sum_congr rfl (fun rc hrc => ?_)
    rw [mem_range] at hrc
    have hx : exr p c (some (dig rc)) = exrT (projIdx (encO p)) (code c) (1 + rc) := by
      rw [exr_eq]
      simp only [encO, code_dig rc hrc]
    unfold guardB succS
    rw [rgsRow_dig, limNext_dig, hx, d1, d2, d3, d4]
    have hl1 : 1 ≤ limC lim rc := by unfold limC; omega
    have hl2 : limC lim rc ≤ 3 := by unfold limC; omega
    have hpi : projIdx (encO (some c)) = 1 + pcodeC (code c) := by
      simp [projIdx, encO]
    by_cases hg : rgsC lim rc = true
    · by_cases he : e + exrT (projIdx (encO p)) (code c) (1 + rc) ≤ 0
      · rw [if_pos hg, if_pos (by simp [hg, he]), ih (some c) (dig rc) _ _ hl1 hl2 he, hpi,
          code_dig rc hrc]
      · rw [if_pos hg, if_neg (by simp [he]), N_over _ _ _ _ _ (by omega)]
    · rw [if_neg hg, if_neg (by simp [hg])]

theorem succ_lt (s rc : ℕ) (hs : s < 270) (hrc : rc < 9) (hg : guardB s rc = true) :
    succS s rc < 270 := by
  have h := tabs_split.2.2.1
  unfold cclos at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h s hs rc hrc with h' | h'
  · rw [hg] at h'
    exact absurd h' (by decide)
  · exact h'.1

theorem reach_succ (s rc : ℕ) (hs : s < 270) (hrc : rc < 9) (hg : guardB s rc = true)
    (hr : reach s = true) : reach (succS s rc) = true := by
  have h := tabs_split.2.2.1
  unfold cclos at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h s hs rc hrc with h' | h'
  · rw [hg] at h'
    exact absurd h' (by decide)
  · rcases h'.2 with h'' | h''
    · rw [hr] at h''
      exact absurd h'' (by decide)
    · exact h''

theorem init_ok (cc : ℕ) (hcc : cc < 9) (hg : rgsC 0 cc = true) :
    enc 0 cc (limC 0 cc) 0 < 270 ∧ reach (enc 0 cc (limC 0 cc) 0) = true := by
  have h := tabs_split.2.2.2.1
  unfold cinit at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h cc hcc with h' | h'
  · rw [hg] at h'
    exact absurd h' (by decide)
  · exact ⟨h'.2, h'.1⟩

theorem tab_eq0 (s : ℕ) (hs : s < 270) (hr : reach s = true) : Ncode s 0 = tab0 s := by
  have h := tabs_split.2.2.2.2.1
  unfold c0 at h
  rw [List.all_eq_true] at h
  have hc := h s (List.mem_range.mpr hs)
  rw [hr, Bool.not_true, Bool.false_or, beq_iff_eq] at hc
  rw [hc]
  rfl

theorem tab_eq1 (s : ℕ) (hs : s < 270) (hr : reach s = true) :
    Ncode s 1 = tab1 s := by
  have h := tabs_split.2.2.2.2.2.1
  unfold c1 at h
  rw [List.all_eq_true] at h
  have hc := h s (List.mem_range.mpr hs)
  rw [hr, Bool.not_true, Bool.false_or, beq_iff_eq] at hc
  rw [hc, Ncode_succ]
  have e : ∀ rc ∈ range 9, (if guardB s rc = true then Ncode (succS s rc) 0 else 0) =
      (if guardB s rc = true then tab0 (succS s rc) else 0) := by
    intro rc hrc
    split_ifs with hg
    · exact tab_eq0 _ (succ_lt s rc hs (mem_range.mp hrc) hg)
        (reach_succ s rc hs (mem_range.mp hrc) hg hr)
    · rfl
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

theorem tab_eq2 (s : ℕ) (hs : s < 270) (hr : reach s = true) :
    Ncode s 2 = tab2 s := by
  have h := tabs_split.2.2.2.2.2.2.1
  unfold c2 at h
  rw [List.all_eq_true] at h
  have hc := h s (List.mem_range.mpr hs)
  rw [hr, Bool.not_true, Bool.false_or, beq_iff_eq] at hc
  rw [hc, Ncode_succ]
  have e : ∀ rc ∈ range 9, (if guardB s rc = true then Ncode (succS s rc) 1 else 0) =
      (if guardB s rc = true then tab1 (succS s rc) else 0) := by
    intro rc hrc
    split_ifs with hg
    · exact tab_eq1 _ (succ_lt s rc hs (mem_range.mp hrc) hg)
        (reach_succ s rc hs (mem_range.mp hrc) hg hr)
    · rfl
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

theorem tab_eq3 (s : ℕ) (hs : s < 270) (hr : reach s = true) :
    Ncode s 3 = tab3 s := by
  have h := tabs_split.2.2.2.2.2.2.2.1
  unfold c3 at h
  rw [List.all_eq_true] at h
  have hc := h s (List.mem_range.mpr hs)
  rw [hr, Bool.not_true, Bool.false_or, beq_iff_eq] at hc
  rw [hc, Ncode_succ]
  have e : ∀ rc ∈ range 9, (if guardB s rc = true then Ncode (succS s rc) 2 else 0) =
      (if guardB s rc = true then tab2 (succS s rc) else 0) := by
    intro rc hrc
    split_ifs with hg
    · exact tab_eq2 _ (succ_lt s rc hs (mem_range.mp hrc) hg)
        (reach_succ s rc hs (mem_range.mp hrc) hg hr)
    · rfl
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

/-- The recurrence of order 3 of the continuation counts, on every reachable state. -/
theorem Ncode_rec (m : ℕ) : ∀ s, s < 270 → reach s = true →
    (Ncode s (m + 3) : ℤ) = (4 : ℤ) * (Ncode s (m + 2) : ℤ) + (6 : ℤ) * (Ncode s (m + 1) : ℤ) + (-12 : ℤ) * (Ncode s m : ℤ) := by
  induction m with
  | zero =>
    intro s hs hr
    simp only [zero_add]
    rw [tab_eq3 s hs hr, tab_eq2 s hs hr, tab_eq1 s hs hr, tab_eq0 s hs hr]
    have h := tabs_split.2.1
    unfold crec at h
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
      beq_iff_eq] at h
    rcases h s hs with h' | h'
    · rw [hr] at h'
      exact absurd h' (by decide)
    · exact h'
  | succ m ih =>
    intro s hs hr
    show (Ncode s (m + 1 + 3) : ℤ) = (4 : ℤ) * (Ncode s (m + 1 + 2) : ℤ) + (6 : ℤ) * (Ncode s (m + 1 + 1) : ℤ) + (-12 : ℤ) * (Ncode s (m + 1) : ℤ)
    rw [Ncode_succ s (m + 3), Ncode_succ s (m + 2), Ncode_succ s (m + 1), Ncode_succ s m]
    push_cast
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine sum_congr rfl (fun rc hrc => ?_)
    split_ifs with hg
    · exact ih _ (succ_lt s rc hs (mem_range.mp hrc) hg) (reach_succ s rc hs (mem_range.mp hrc) hg hr)
    · simp

theorem a_code (n : ℕ) : a (n + 1) = ∑ cc ∈ range 9,
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

/-- The recurrence of order 3: a(n) for n >= 4. -/
theorem a_rec (m : ℕ) : (a (m + 4) : ℤ) = (4 : ℤ) * (a (m + 3) : ℤ) + (6 : ℤ) * (a (m + 2) : ℤ) + (-12 : ℤ) * (a (m + 1) : ℤ) := by
  rw [a_code (m + 3), a_code (m + 2), a_code (m + 1), a_code m]
  push_cast
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine sum_congr rfl (fun cc hcc => ?_)
  split_ifs with hg
  · exact Ncode_rec m _ (init_ok cc (mem_range.mp hcc) hg).1 (init_ok cc (mem_range.mp hcc) hg).2
  · simp

theorem v1 : a 1 = 0 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, a_code]
  have e : ∀ cc ∈ range 9, (if rgsC 0 cc = true then Ncode (enc 0 cc (limC 0 cc) 0) 0 else 0) =
      (if rgsC 0 cc = true then tab0 (enc 0 cc (limC 0 cc) 0) else 0) := by
    intro cc hcc
    split_ifs with hg
    · exact tab_eq0 _ (init_ok cc (mem_range.mp hcc) hg).1 (init_ok cc (mem_range.mp hcc) hg).2
    · rfl
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have h := tabs_split.2.2.2.2.2.2.2.2.1
  unfold cval0 at h
  exact beq_iff_eq.mp h

theorem v2 : a 2 = 1 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, a_code]
  have e : ∀ cc ∈ range 9, (if rgsC 0 cc = true then Ncode (enc 0 cc (limC 0 cc) 0) 1 else 0) =
      (if rgsC 0 cc = true then tab1 (enc 0 cc (limC 0 cc) 0) else 0) := by
    intro cc hcc
    split_ifs with hg
    · exact tab_eq1 _ (init_ok cc (mem_range.mp hcc) hg).1 (init_ok cc (mem_range.mp hcc) hg).2
    · rfl
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have h := tabs_split.2.2.2.2.2.2.2.2.2.1
  unfold cval1 at h
  exact beq_iff_eq.mp h

theorem v3 : a 3 = 2 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, a_code]
  have e : ∀ cc ∈ range 9, (if rgsC 0 cc = true then Ncode (enc 0 cc (limC 0 cc) 0) 2 else 0) =
      (if rgsC 0 cc = true then tab2 (enc 0 cc (limC 0 cc) 0) else 0) := by
    intro cc hcc
    split_ifs with hg
    · exact tab_eq2 _ (init_ok cc (mem_range.mp hcc) hg).1 (init_ok cc (mem_range.mp hcc) hg).2
    · rfl
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have h := tabs_split.2.2.2.2.2.2.2.2.2.2
  unfold cval2 at h
  exact beq_iff_eq.mp h

/-- Barker's g.f., as A(x) ((1 + 2 * X) * (1 - 6 * X + 6 * X ^ 2)) = X ^ 2 * (1 - 2 * X) in Z[[x]], with A(x) = Sum_{n >= 1} a(n) x^n. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * ((1 + 2 * X) * (1 - 6 * X + 6 * X ^ 2)) = X ^ 2 * (1 - 2 * X) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * ((1 + 2 * X) * (1 - 6 * X + 6 * X ^ 2)) = A - C 4 * (A * X ^ 1) - C 6 * (A * X ^ 2) + C 12 * (A * X ^ 3) := by
    simp only [map_ofNat]; ring
  have e2 : (X ^ 2 * (1 - 2 * X) : ℤ⟦X⟧) = X ^ 2 - X ^ 3 * C 2 := by
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
      show q + 4 - 3 = q + 1 by omega, 
      show 3 ≤ q + 4 by omega, 
      show ¬ q + 1 = 0 by omega, 
      show ¬ q + 4 = 0 by omega, 
      show ¬ q + 4 = 2 by omega, 
      show ¬ q + 4 = 3 by omega,
      if_true, if_false]
    rw [h]
    ring


/-- Barker's closed form, for n >= 1. -/
theorem closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℝ) = (3 * (-1) ^ n * 2 ^ (2 + n) - (-5 + Real.sqrt 3) * (3 + Real.sqrt 3) ^ n +
      (3 - Real.sqrt 3) ^ n * (5 + Real.sqrt 3)) / 132 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  skip
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 4 with hlt | hge
    · interval_cases n
      · rw [v1]
        push_cast
        linear_combination ((1 / 66 : ℝ)) * hs
      · rw [v2]
        push_cast
        linear_combination ((1 / 66 : ℝ)) * hs
      · rw [v3]
        push_cast
        linear_combination ((1 / 66 : ℝ) * Real.sqrt 3 ^ 2 + (-5 / 22 : ℝ)) * hs
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      have hR : (a (k + 4) : ℝ) = (4 : ℝ) * (a (k + 3) : ℝ) + (6 : ℝ) * (a (k + 2) : ℝ) + (-12 : ℝ) * (a (k + 1) : ℝ) := by exact_mod_cast a_rec k
      rw [hR, ih (k + 3) (by omega) (by omega), ih (k + 2) (by omega) (by omega), ih (k + 1) (by omega) (by omega)]
      push_cast
      linear_combination ((1 / 132 : ℝ) * Real.sqrt 3 ^ 3 * (3 + Real.sqrt 3) ^ k + (-1 / 132 : ℝ) * Real.sqrt 3 ^ 3 * (3 - Real.sqrt 3) ^ k + (1 / 44 : ℝ) * Real.sqrt 3 ^ 2 * (3 + Real.sqrt 3) ^ k + (1 / 44 : ℝ) * Real.sqrt 3 ^ 2 * (3 - Real.sqrt 3) ^ k + (-25 / 132 : ℝ) * Real.sqrt 3 * (3 + Real.sqrt 3) ^ k + (25 / 132 : ℝ) * Real.sqrt 3 * (3 - Real.sqrt 3) ^ k + (-25 / 44 : ℝ) * (3 + Real.sqrt 3) ^ k + (-25 / 44 : ℝ) * (3 - Real.sqrt 3) ^ k) * hs

/-- Controls: the entry's data a(1..13). -/
theorem controls : a 1 = 0 ∧ a 2 = 1 ∧ a 3 = 2 ∧ a 4 = 14 ∧ a 5 = 56 ∧ a 6 = 284 ∧ a 7 = 1304 ∧ a 8 = 6248 ∧ a 9 = 29408 ∧ a 10 = 139472 ∧ a 11 = 659360 ∧ a 12 = 3121376 ∧ a 13 = 14768000 := by
  have v4 : a 4 = 14 := by
    have h : (a 4 : ℤ) = (4 : ℤ) * (a 3 : ℤ) + (6 : ℤ) * (a 2 : ℤ) + (-12 : ℤ) * (a 1 : ℤ) := a_rec 0
    rw [v3, v2, v1] at h
    omega
  have v5 : a 5 = 56 := by
    have h : (a 5 : ℤ) = (4 : ℤ) * (a 4 : ℤ) + (6 : ℤ) * (a 3 : ℤ) + (-12 : ℤ) * (a 2 : ℤ) := a_rec 1
    rw [v4, v3, v2] at h
    omega
  have v6 : a 6 = 284 := by
    have h : (a 6 : ℤ) = (4 : ℤ) * (a 5 : ℤ) + (6 : ℤ) * (a 4 : ℤ) + (-12 : ℤ) * (a 3 : ℤ) := a_rec 2
    rw [v5, v4, v3] at h
    omega
  have v7 : a 7 = 1304 := by
    have h : (a 7 : ℤ) = (4 : ℤ) * (a 6 : ℤ) + (6 : ℤ) * (a 5 : ℤ) + (-12 : ℤ) * (a 4 : ℤ) := a_rec 3
    rw [v6, v5, v4] at h
    omega
  have v8 : a 8 = 6248 := by
    have h : (a 8 : ℤ) = (4 : ℤ) * (a 7 : ℤ) + (6 : ℤ) * (a 6 : ℤ) + (-12 : ℤ) * (a 5 : ℤ) := a_rec 4
    rw [v7, v6, v5] at h
    omega
  have v9 : a 9 = 29408 := by
    have h : (a 9 : ℤ) = (4 : ℤ) * (a 8 : ℤ) + (6 : ℤ) * (a 7 : ℤ) + (-12 : ℤ) * (a 6 : ℤ) := a_rec 5
    rw [v8, v7, v6] at h
    omega
  have v10 : a 10 = 139472 := by
    have h : (a 10 : ℤ) = (4 : ℤ) * (a 9 : ℤ) + (6 : ℤ) * (a 8 : ℤ) + (-12 : ℤ) * (a 7 : ℤ) := a_rec 6
    rw [v9, v8, v7] at h
    omega
  have v11 : a 11 = 659360 := by
    have h : (a 11 : ℤ) = (4 : ℤ) * (a 10 : ℤ) + (6 : ℤ) * (a 9 : ℤ) + (-12 : ℤ) * (a 8 : ℤ) := a_rec 7
    rw [v10, v9, v8] at h
    omega
  have v12 : a 12 = 3121376 := by
    have h : (a 12 : ℤ) = (4 : ℤ) * (a 11 : ℤ) + (6 : ℤ) * (a 10 : ℤ) + (-12 : ℤ) * (a 9 : ℤ) := a_rec 8
    rw [v11, v10, v9] at h
    omega
  have v13 : a 13 = 14768000 := by
    have h : (a 13 : ℤ) = (4 : ℤ) * (a 12 : ℤ) + (6 : ℤ) * (a 11 : ℤ) + (-12 : ℤ) * (a 10 : ℤ) := a_rec 9
    rw [v12, v11, v10] at h
    omega
  exact ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13⟩

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * ((1 + 2 * X) * (1 - 6 * X + 6 * X ^ 2)) = X ^ 2 * (1 - 2 * X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) = (3 * (-1) ^ n * 2 ^ (2 + n) - (-5 + Real.sqrt 3) * (3 + Real.sqrt 3) ^ n +
      (3 - Real.sqrt 3) ^ n * (5 + Real.sqrt 3)) / 132 :=
  ⟨gf, closed⟩

end OMA.S_oeis_a277761

theorem OMA.solution : type_of% @OMA.S_oeis_a277761.main :=
  OMA.S_oeis_a277761.conjecture
