import OMAStatements.S_oeis_a280474

namespace OMA.S_oeis_a280474

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
  [((0 : ℤ), (-1 : ℤ)), (0, 1), (-1, 1), (1, -1)].filterMap fun d =>
    rc (if d.1 = -1 then u else if d.1 = 0 then some v else w) (j + d.2)

theorem nbrs_eq (n : ℕ) (x : Fin n → Fin 2 → Fin 3) (i : Fin n) (j : Fin 2) :
    nbrs n x i j = nbrsR (rowOpt x ((i : ℤ) + -1)) (x i) (rowOpt x ((i : ℤ) + 1)) j := by
  unfold nbrs nbrsR
  refine List.filterMap_congr (fun d hd => ?_)
  rw [cell_eq]
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> simp [rowOpt_self]

/-- The condition of the entry for the element in column j of the row v. -/
def excR (u : Option (Fin 2 → Fin 3)) (v : Fin 2 → Fin 3) (w : Option (Fin 2 → Fin 3))
    (j : Fin 2) : Bool :=
  decide ((nbrsR u v w j).length < 2 * (nbrsR u v w j).countP (· ≠ v j))

theorem exc_iff (n : ℕ) (x : Fin n → Fin 2 → Fin 3) (i : Fin n) (j : Fin 2) :
    unmaj n x i j ↔ excR (rowOpt x ((i : ℤ) + -1)) (x i) (rowOpt x ((i : ℤ) + 1)) j = true := by
  unfold unmaj excR
  rw [nbrs_eq, decide_eq_true_iff]

/-- The number of elements of the row v that meet the condition. -/
def exr (u : Option (Fin 2 → Fin 3)) (v : Fin 2 → Fin 3) (w : Option (Fin 2 → Fin 3)) : ℕ :=
  (if excR u v w 0 = true then 1 else 0) + (if excR u v w 1 = true then 1 else 0)

theorem ncard_eq (n : ℕ) (x : Fin n → Fin 2 → Fin 3) :
    {p : Fin n × Fin 2 | unmaj n x p.1 p.2}.ncard =
      ∑ i : Fin n, exr (rowOpt x ((i : ℤ) + -1)) (x i) (rowOpt x ((i : ℤ) + 1)) := by
  have e : {p : Fin n × Fin 2 | unmaj n x p.1 p.2} = ↑(univ.filter fun p : Fin n × Fin 2 =>
      excR (rowOpt x ((p.1 : ℤ) + -1)) (x p.1) (rowOpt x ((p.1 : ℤ) + 1)) p.2 = true) := by
    ext p
    simp [exc_iff]
  rw [e, Set.ncard_coe_finset, card_filter, Fintype.sum_prod_type]
  refine sum_congr rfl (fun i _ => ?_)
  rw [Fin.sum_univ_two]
  rfl

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
  ∑ y : Fin m → Fin 2 → Fin 3, if orderedL lim y ∧ G p (Fin.cons c y) + e = 2 then 1 else 0

theorem sum_cons {α : Type} [Fintype α] [DecidableEq α] (m : ℕ) (f : (Fin (m + 1) → α) → ℕ) :
    ∑ y : Fin (m + 1) → α, f y = ∑ r : α, ∑ y : Fin m → α, f (Fin.cons r y) := by
  rw [← (Fin.consEquiv fun _ => α).sum_comp, Fintype.sum_prod_type]
  rfl

theorem N_zero (p : Option (Fin 2 → Fin 3)) (c : Fin 2 → Fin 3) (lim e : ℕ) :
    N p c lim e 0 = if exr p c none + e = 2 then 1 else 0 := by
  have key : ∀ y : Fin 0 → Fin 2 → Fin 3,
      (if orderedL lim y ∧ G p (Fin.cons c y) + e = 2 then 1 else 0) =
        if exr p c none + e = 2 then 1 else 0 := by
    intro y
    have h1 : orderedL lim y := fun i => i.elim0
    have h2 : G p (Fin.cons c y) = exr p c none := by
      rw [G_cons, rowOpt_empty]
      simp [G]
    by_cases h : exr p c none + e = 2 <;> simp [h, h1, h2]
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
    have he : (exr p c (some r) + G (some c) (Fin.cons r y) + e = 2) ↔
        (G (some c) (Fin.cons r y) + (e + exr p c (some r)) = 2) := by omega
    simp only [hG, orderedL_cons, hr, true_and, he]
  · rw [if_neg hr]
    refine sum_eq_zero (fun y _ => ?_)
    simp [orderedL_cons, hr]

theorem N_over (p : Option (Fin 2 → Fin 3)) (c : Fin 2 → Fin 3) (lim e m : ℕ) (h : 2 < e) :
    N p c lim e m = 0 := by
  unfold N
  refine sum_eq_zero (fun y _ => ?_)
  rw [if_neg (fun h' => by have := h'.2; omega)]

theorem cond_iff (n : ℕ) (x : Fin n → Fin 2 → Fin 3) :
    ({p : Fin n × Fin 2 | unmaj n x p.1 p.2}.ncard = 2 ∧ ordered n x) ↔
      (orderedL 0 x ∧ G none x + 0 = 2) := by
  rw [ncard_eq, ← G_none, ordered_iff, add_zero, and_comm]

theorem a_succ (n : ℕ) : a (n + 1) = ∑ c : Fin 2 → Fin 3,
    if rgsRow 0 c = true then N none c (limNext 0 c) 0 n else 0 := by
  have ha : a (n + 1) = ∑ x : Fin (n + 1) → Fin 2 → Fin 3,
      if orderedL 0 x ∧ G none x + 0 = 2 then 1 else 0 := by
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

/-- The code of the columns of the row with code cc that the row below reads (column 1). -/
def pcodeC (cc : ℕ) : ℕ := cc / 3 % 3

/-- The table index of an optional row above: 0 for none, 1 + the code of its read columns. -/
def projIdx (pc : ℕ) : ℕ := if pc = 0 then 0 else 1 + pcodeC (pc - 1)

/-- The number of elements meeting the condition in the row with code cc, with the row above of
table index qc and the row below of code wc (0 for none, 1 + the row code otherwise). -/
def exrT (qc cc wc : ℕ) : ℕ := 2170853559212012304106962677723693766913208723038290031387203279278850987184844629751806971467892433853399210410926546772927344423126639607540050368923794954886335181988478775588895463066814609590738265841860608 >>> (2 * ((qc * 9 + cc) * 10 + wc)) % 4

/-- The first row condition on codes. -/
def rgsC (lim cc : ℕ) : Bool := decide (cc % 3 ≤ lim ∧ cc / 3 % 3 ≤ max lim (cc % 3 + 1))

/-- The values introduced after the row with code cc. -/
def limC (lim cc : ℕ) : ℕ := max (max lim (cc % 3 + 1)) (cc / 3 % 3 + 1)

/-- The code of the state (qc, cc, lim, e): row above (table index qc), current row cc, lim values
introduced, e elements above meeting the condition. -/
def enc (qc cc lim e : ℕ) : ℕ := ((qc * 9 + cc) * 3 + (lim - 1)) * 3 + e

def qcOf (s : ℕ) : ℕ := s / (9 * 3 * 3)

def ccOf (s : ℕ) : ℕ := s / (3 * 3) % 9

def limOf (s : ℕ) : ℕ := s / 3 % 3 + 1

def eOf (s : ℕ) : ℕ := s % 3

/-- The next row with code rc may follow the state s. -/
def guardB (s rc : ℕ) : Bool :=
  rgsC (limOf s) rc && decide (eOf s + exrT (qcOf s) (ccOf s) (1 + rc) ≤ 2)

/-- The state after the row with code rc. -/
def succS (s rc : ℕ) : ℕ :=
  enc (1 + pcodeC (ccOf s)) rc (limC (limOf s) rc) (eOf s + exrT (qcOf s) (ccOf s) (1 + rc))

/-- The continuation counts on state codes. -/
def Ncode : ℕ → ℕ → ℕ
  | s, 0 => if exrT (qcOf s) (ccOf s) 0 + eOf s = 2 then 1 else 0
  | s, m + 1 => ∑ rc ∈ range 9, if guardB s rc = true then Ncode (succS s rc) m else 0

theorem Ncode_succ (s m : ℕ) : Ncode s (m + 1) =
    ∑ rc ∈ range 9, if guardB s rc = true then Ncode (succS s rc) m else 0 := rfl

/-- The table of Ncode 0: entry s in the bits 1 * s.. of one number. -/
def tab0 (s : ℕ) : ℕ := 17096256346920315160272758425577026452565530921786154786461424468724781080398990956522097856217088 >>> (1 * s) % 2 ^ 1

/-- The table of Ncode 1: entry s in the bits 3 * s.. of one number. -/
def tab1 (s : ℕ) : ℕ := 16528052570304790250702413320938493016776890778536169932616654653241983589351826298616583770343811904232576956038039566081725807850909974943905354837835988726071879531015187302737890835245551470344757906965268907822213848589942002719203003854023905843853575200076391460573202036063483090436098 >>> (3 * s) % 2 ^ 3

/-- The table of Ncode 2: entry s in the bits 5 * s.. of one number. -/
def tab2 (s : ℕ) : ℕ := 16885758680004875006757975231902851989342788022583221757895183013019177459696337257297183578184734737541885978960633576124850546391570787223270426003263981280036252863088864856385062623074234132546021906156122589847518680268136410084718078966774055049040041631299873757043923293469045781840679512727236285759690790674316735291200158236744916240628779954281731817224731922327648620098655744978869082881355059985211055234713775447070587059868067158643887467845256636568779293793511792443406 >>> (5 * s) % 2 ^ 5

/-- The table of Ncode 3: entry s in the bits 8 * s.. of one number. -/
def tab3 (s : ℕ) : ℕ := 315620698395398287627634527160106337549381152504076882430411572660435107143750011461932556848675959989905568299896985392466715929731733075822865772792061656519748021139385995258940961612808421147773007516383191950025097908127482957081579819846755911240824601555255892941504177472627366423095923388824986632812721929956400006912433298725221273257823664517354628831787136499580883080403248693319444562540192556512581156394324439370765432974783385290128618151023895197242929802004070361488214814679094621080659741238818509312363397436169646276193815952469553000631849886385855280012436325729829342057126203104529542599527461304486015275612566025021409193024811628562365973056778950346372339775971119043937507363069687053815821583466925335694996618661699097232877402399077138039832662 >>> (8 * s) % 2 ^ 8

/-- The table of Ncode 4: entry s in the bits 10 * s.. of one number. -/
def tab4 (s : ℕ) : ℕ := 364113394105031500259622050251189603600634699109278692338546853524268962587011542737737154794753473895246619088104330843222468215397026450329467695871082154386175853489661238080019968484408624288405621941443810584159656229732553840776915694480375179484414247784163773286589011619324308630525357836606369089939899525980039134785067003804948847754863685084104474466543173193280754002789975252216314496022880922884416477905988126487274127834118423617128629037234816822223932554670145490289661207399500281382360224132695297961273854027704264525839235433339223682637367452629241246889572948934975031060130585819972209782330932655622945128436255912848526319654186992815764196732766139662098648931234051385079533143144917321593817789620506390119894043840363668327536741944977325384409915930618072518791652440308045614648375235078194523272940945817621233877962898416556808946242507079610316540284650737321524981394351269005448487271686264110325266284223044063385137307402626404450814 >>> (10 * s) % 2 ^ 10

/-- The table of Ncode 5: entry s in the bits 13 * s.. of one number. -/
def tab5 (s : ℕ) : ℕ := 7237327002858555950252834266319391440764777418375587496890590030073116319934654213610131397774695172799177320759651000118711799047144611115308998337479213681251969623940432338049014713453515486800853712597763467370433270037840887767770005414502387402933034686739355762933615014482445314692377003029561522679238142537601953245525660578545734349391338088915194604905053115754282024778136639305732963349547022238970251218943125824394337405402618575459320731931992494076816011651363006100997619009482010060762978828020855421050955028224187692280560906528137021701120764289267532388374763825323109893878789612584563067172566702279653447377245762846124362867530176910330452833795793706295481207396350734230946443566420533909064282165072645602723433775854858220340145684799490963255625572939369488369734006006673508490933450763226090532295635090121696052497755162700021824500663134948964262458819235972828988605355222467319332745687862910756474237661604300454679649226435804221152282531296956289020447807003905110164673805857834526003978329313222999155498660576923851840169655528550505807293264909825628076218844890764952733194797044735598254751807950696985099198567967081232434806047027786466427358932473754890592786534590099223338237583022175983368334193851843345031105350 >>> (13 * s) % 2 ^ 13

/-- The table of Ncode 6: entry s in the bits 15 * s.. of one number. -/
def tab6 (s : ℕ) : ℕ := 8447166121734070608008825763322815994235142752812114592579255764494477252509972731088486975006931992845889841947116974166557656106406611701238182009095395850533692510823450846446752749379744822057295309054351207636800062292385843667903126044978476720121683511882470493949604076098813603484029567912652547433523762166020799927654900399049965818939733240422943581264085914136211562176321843925971059357528757042397059699094647421884027508320938111805005587429298161685336368744941349107270627281599965154389218890916560224925452708535277917511608082622194542182158697339480601301241516470025039594743017631986271629561709669849682450514166554917814943581916062751955208936003664275138418366892786091134837990864603911357983524610906958538865147620371568226117312745010803943814309271712748344450166346891313211683329362367885894838901681880420701682158934589982995216452794819571589179804550607851861078544846313624663751039207290498950773627332386018119859812115525110558223088391025642866608376269045756444424384694218475794955238330527182201121292252250168557022187023901056541286496488651619445119099500399148077766612039307133195314734028796682849896344224644563827717508152702048794876084569965352671071042680436682346257660507990576099214234307159295016205725788995155099987901401765165757418056577367233301004731599411995997372458364178059525419319356064978531655707174327398635610632758864780174606496665318896928685927436473738606880736020836781716946158 >>> (15 * s) % 2 ^ 15

/-- The states reachable from a first row. -/
def reach (s : ℕ) : Bool := 29962338695657697594143866124898922835598187991405488366776615228950914518575349477900239765504001 >>> s % 2 == 1

/-- exrT agrees with exr on all rows above, current rows and rows below. -/
def xcheck : Bool :=
  (List.range 10).all fun pc => (List.range 9).all fun cc =>
    (List.range 10).all fun wc => exr (decO pc) (dig cc) (decO wc) == exrT (projIdx pc) cc wc

/-- The recurrence of order 6 on the reachable states. -/
def crec : Bool := (List.range 324).all fun s =>
  !(reach s) || ((tab6 s : ℤ) == (15 : ℤ) * (tab5 s : ℤ) + (-87 : ℤ) * (tab4 s : ℤ) + (245 : ℤ) * (tab3 s : ℤ) + (-348 : ℤ) * (tab2 s : ℤ) + (240 : ℤ) * (tab1 s : ℤ) + (-64 : ℤ) * (tab0 s : ℤ))

/-- Successor states are in range, and reachable from reachable ones. -/
def cclos : Bool := (List.range 324).all fun s => (List.range 9).all fun rc =>
  !(guardB s rc) || (decide (succS s rc < 324) && (!(reach s) || reach (succS s rc)))

/-- The first states are in range and reachable. -/
def cinit : Bool := (List.range 9).all fun cc =>
  !(rgsC 0 cc) || (reach (enc 0 cc (limC 0 cc) 0) && decide (enc 0 cc (limC 0 cc) 0 < 324))

def c0 : Bool := (List.range 324).all fun s =>
  !(reach s) || (tab0 s == if exrT (qcOf s) (ccOf s) 0 + eOf s = 2 then 1 else 0)

def c1 : Bool := (List.range 324).all fun s =>
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

def c2 : Bool := (List.range 324).all fun s =>
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

def c3 : Bool := (List.range 324).all fun s =>
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

def c4 : Bool := (List.range 324).all fun s =>
  !(reach s) || (tab4 s ==
    (if guardB s 0 = true then tab3 (succS s 0) else 0) +
    (if guardB s 1 = true then tab3 (succS s 1) else 0) +
    (if guardB s 2 = true then tab3 (succS s 2) else 0) +
    (if guardB s 3 = true then tab3 (succS s 3) else 0) +
    (if guardB s 4 = true then tab3 (succS s 4) else 0) +
    (if guardB s 5 = true then tab3 (succS s 5) else 0) +
    (if guardB s 6 = true then tab3 (succS s 6) else 0) +
    (if guardB s 7 = true then tab3 (succS s 7) else 0) +
    (if guardB s 8 = true then tab3 (succS s 8) else 0))

def c5 : Bool := (List.range 324).all fun s =>
  !(reach s) || (tab5 s ==
    (if guardB s 0 = true then tab4 (succS s 0) else 0) +
    (if guardB s 1 = true then tab4 (succS s 1) else 0) +
    (if guardB s 2 = true then tab4 (succS s 2) else 0) +
    (if guardB s 3 = true then tab4 (succS s 3) else 0) +
    (if guardB s 4 = true then tab4 (succS s 4) else 0) +
    (if guardB s 5 = true then tab4 (succS s 5) else 0) +
    (if guardB s 6 = true then tab4 (succS s 6) else 0) +
    (if guardB s 7 = true then tab4 (succS s 7) else 0) +
    (if guardB s 8 = true then tab4 (succS s 8) else 0))

def c6 : Bool := (List.range 324).all fun s =>
  !(reach s) || (tab6 s ==
    (if guardB s 0 = true then tab5 (succS s 0) else 0) +
    (if guardB s 1 = true then tab5 (succS s 1) else 0) +
    (if guardB s 2 = true then tab5 (succS s 2) else 0) +
    (if guardB s 3 = true then tab5 (succS s 3) else 0) +
    (if guardB s 4 = true then tab5 (succS s 4) else 0) +
    (if guardB s 5 = true then tab5 (succS s 5) else 0) +
    (if guardB s 6 = true then tab5 (succS s 6) else 0) +
    (if guardB s 7 = true then tab5 (succS s 7) else 0) +
    (if guardB s 8 = true then tab5 (succS s 8) else 0))

def cval0 : Bool :=
    (if rgsC 0 0 = true then tab0 (enc 0 0 (limC 0 0) 0) else 0) +
    (if rgsC 0 1 = true then tab0 (enc 0 1 (limC 0 1) 0) else 0) +
    (if rgsC 0 2 = true then tab0 (enc 0 2 (limC 0 2) 0) else 0) +
    (if rgsC 0 3 = true then tab0 (enc 0 3 (limC 0 3) 0) else 0) +
    (if rgsC 0 4 = true then tab0 (enc 0 4 (limC 0 4) 0) else 0) +
    (if rgsC 0 5 = true then tab0 (enc 0 5 (limC 0 5) 0) else 0) +
    (if rgsC 0 6 = true then tab0 (enc 0 6 (limC 0 6) 0) else 0) +
    (if rgsC 0 7 = true then tab0 (enc 0 7 (limC 0 7) 0) else 0) +
    (if rgsC 0 8 = true then tab0 (enc 0 8 (limC 0 8) 0) else 0) == 1

def cval1 : Bool :=
    (if rgsC 0 0 = true then tab1 (enc 0 0 (limC 0 0) 0) else 0) +
    (if rgsC 0 1 = true then tab1 (enc 0 1 (limC 0 1) 0) else 0) +
    (if rgsC 0 2 = true then tab1 (enc 0 2 (limC 0 2) 0) else 0) +
    (if rgsC 0 3 = true then tab1 (enc 0 3 (limC 0 3) 0) else 0) +
    (if rgsC 0 4 = true then tab1 (enc 0 4 (limC 0 4) 0) else 0) +
    (if rgsC 0 5 = true then tab1 (enc 0 5 (limC 0 5) 0) else 0) +
    (if rgsC 0 6 = true then tab1 (enc 0 6 (limC 0 6) 0) else 0) +
    (if rgsC 0 7 = true then tab1 (enc 0 7 (limC 0 7) 0) else 0) +
    (if rgsC 0 8 = true then tab1 (enc 0 8 (limC 0 8) 0) else 0) == 6

def cval2 : Bool :=
    (if rgsC 0 0 = true then tab2 (enc 0 0 (limC 0 0) 0) else 0) +
    (if rgsC 0 1 = true then tab2 (enc 0 1 (limC 0 1) 0) else 0) +
    (if rgsC 0 2 = true then tab2 (enc 0 2 (limC 0 2) 0) else 0) +
    (if rgsC 0 3 = true then tab2 (enc 0 3 (limC 0 3) 0) else 0) +
    (if rgsC 0 4 = true then tab2 (enc 0 4 (limC 0 4) 0) else 0) +
    (if rgsC 0 5 = true then tab2 (enc 0 5 (limC 0 5) 0) else 0) +
    (if rgsC 0 6 = true then tab2 (enc 0 6 (limC 0 6) 0) else 0) +
    (if rgsC 0 7 = true then tab2 (enc 0 7 (limC 0 7) 0) else 0) +
    (if rgsC 0 8 = true then tab2 (enc 0 8 (limC 0 8) 0) else 0) == 30

def cval3 : Bool :=
    (if rgsC 0 0 = true then tab3 (enc 0 0 (limC 0 0) 0) else 0) +
    (if rgsC 0 1 = true then tab3 (enc 0 1 (limC 0 1) 0) else 0) +
    (if rgsC 0 2 = true then tab3 (enc 0 2 (limC 0 2) 0) else 0) +
    (if rgsC 0 3 = true then tab3 (enc 0 3 (limC 0 3) 0) else 0) +
    (if rgsC 0 4 = true then tab3 (enc 0 4 (limC 0 4) 0) else 0) +
    (if rgsC 0 5 = true then tab3 (enc 0 5 (limC 0 5) 0) else 0) +
    (if rgsC 0 6 = true then tab3 (enc 0 6 (limC 0 6) 0) else 0) +
    (if rgsC 0 7 = true then tab3 (enc 0 7 (limC 0 7) 0) else 0) +
    (if rgsC 0 8 = true then tab3 (enc 0 8 (limC 0 8) 0) else 0) == 158

def cval4 : Bool :=
    (if rgsC 0 0 = true then tab4 (enc 0 0 (limC 0 0) 0) else 0) +
    (if rgsC 0 1 = true then tab4 (enc 0 1 (limC 0 1) 0) else 0) +
    (if rgsC 0 2 = true then tab4 (enc 0 2 (limC 0 2) 0) else 0) +
    (if rgsC 0 3 = true then tab4 (enc 0 3 (limC 0 3) 0) else 0) +
    (if rgsC 0 4 = true then tab4 (enc 0 4 (limC 0 4) 0) else 0) +
    (if rgsC 0 5 = true then tab4 (enc 0 5 (limC 0 5) 0) else 0) +
    (if rgsC 0 6 = true then tab4 (enc 0 6 (limC 0 6) 0) else 0) +
    (if rgsC 0 7 = true then tab4 (enc 0 7 (limC 0 7) 0) else 0) +
    (if rgsC 0 8 = true then tab4 (enc 0 8 (limC 0 8) 0) else 0) == 846

def cval5 : Bool :=
    (if rgsC 0 0 = true then tab5 (enc 0 0 (limC 0 0) 0) else 0) +
    (if rgsC 0 1 = true then tab5 (enc 0 1 (limC 0 1) 0) else 0) +
    (if rgsC 0 2 = true then tab5 (enc 0 2 (limC 0 2) 0) else 0) +
    (if rgsC 0 3 = true then tab5 (enc 0 3 (limC 0 3) 0) else 0) +
    (if rgsC 0 4 = true then tab5 (enc 0 4 (limC 0 4) 0) else 0) +
    (if rgsC 0 5 = true then tab5 (enc 0 5 (limC 0 5) 0) else 0) +
    (if rgsC 0 6 = true then tab5 (enc 0 6 (limC 0 6) 0) else 0) +
    (if rgsC 0 7 = true then tab5 (enc 0 7 (limC 0 7) 0) else 0) +
    (if rgsC 0 8 = true then tab5 (enc 0 8 (limC 0 8) 0) else 0) == 4446

set_option maxRecDepth 100000 in
theorem tabs : (xcheck && (crec && (cclos && (cinit && (c0 && (c1 && (c2 && (c3 && (c4 && (c5 && (c6 && (cval0 && (cval1 && (cval2 && (cval3 && (cval4 && (cval5))))))))))))))))) = true := by
  decide +kernel

theorem tabs_split : xcheck = true ∧ crec = true ∧ cclos = true ∧ cinit = true ∧ c0 = true ∧ c1 = true ∧ c2 = true ∧ c3 = true ∧ c4 = true ∧ c5 = true ∧ c6 = true ∧ cval0 = true ∧ cval1 = true ∧ cval2 = true ∧ cval3 = true ∧ cval4 = true ∧ cval5 = true := by
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

theorem dec_enc (qc cc lim e : ℕ) (h1 : cc < 9) (h2 : 1 ≤ lim) (h3 : lim ≤ 3) (h4 : e ≤ 2) :
    qcOf (enc qc cc lim e) = qc ∧ ccOf (enc qc cc lim e) = cc ∧ limOf (enc qc cc lim e) = lim ∧
      eOf (enc qc cc lim e) = e := by
  unfold qcOf ccOf limOf eOf enc
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem N_code (m : ℕ) : ∀ (p : Option (Fin 2 → Fin 3)) (c : Fin 2 → Fin 3) (lim e : ℕ),
    1 ≤ lim → lim ≤ 3 → e ≤ 2 →
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
    · by_cases he : e + exrT (projIdx (encO p)) (code c) (1 + rc) ≤ 2
      · rw [if_pos hg, if_pos (by simp [hg, he]), ih (some c) (dig rc) _ _ hl1 hl2 he, hpi,
          code_dig rc hrc]
      · rw [if_pos hg, if_neg (by simp [he]), N_over _ _ _ _ _ (by omega)]
    · rw [if_neg hg, if_neg (by simp [hg])]

theorem succ_lt (s rc : ℕ) (hs : s < 324) (hrc : rc < 9) (hg : guardB s rc = true) :
    succS s rc < 324 := by
  have h := tabs_split.2.2.1
  unfold cclos at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h s hs rc hrc with h' | h'
  · rw [hg] at h'
    exact absurd h' (by decide)
  · exact h'.1

theorem reach_succ (s rc : ℕ) (hs : s < 324) (hrc : rc < 9) (hg : guardB s rc = true)
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
    enc 0 cc (limC 0 cc) 0 < 324 ∧ reach (enc 0 cc (limC 0 cc) 0) = true := by
  have h := tabs_split.2.2.2.1
  unfold cinit at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h cc hcc with h' | h'
  · rw [hg] at h'
    exact absurd h' (by decide)
  · exact ⟨h'.2, h'.1⟩

theorem tab_eq0 (s : ℕ) (hs : s < 324) (hr : reach s = true) : Ncode s 0 = tab0 s := by
  have h := tabs_split.2.2.2.2.1
  unfold c0 at h
  rw [List.all_eq_true] at h
  have hc := h s (List.mem_range.mpr hs)
  rw [hr, Bool.not_true, Bool.false_or, beq_iff_eq] at hc
  rw [hc]
  rfl

theorem tab_eq1 (s : ℕ) (hs : s < 324) (hr : reach s = true) :
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

theorem tab_eq2 (s : ℕ) (hs : s < 324) (hr : reach s = true) :
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

theorem tab_eq3 (s : ℕ) (hs : s < 324) (hr : reach s = true) :
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

theorem tab_eq4 (s : ℕ) (hs : s < 324) (hr : reach s = true) :
    Ncode s 4 = tab4 s := by
  have h := tabs_split.2.2.2.2.2.2.2.2.1
  unfold c4 at h
  rw [List.all_eq_true] at h
  have hc := h s (List.mem_range.mpr hs)
  rw [hr, Bool.not_true, Bool.false_or, beq_iff_eq] at hc
  rw [hc, Ncode_succ]
  have e : ∀ rc ∈ range 9, (if guardB s rc = true then Ncode (succS s rc) 3 else 0) =
      (if guardB s rc = true then tab3 (succS s rc) else 0) := by
    intro rc hrc
    split_ifs with hg
    · exact tab_eq3 _ (succ_lt s rc hs (mem_range.mp hrc) hg)
        (reach_succ s rc hs (mem_range.mp hrc) hg hr)
    · rfl
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

theorem tab_eq5 (s : ℕ) (hs : s < 324) (hr : reach s = true) :
    Ncode s 5 = tab5 s := by
  have h := tabs_split.2.2.2.2.2.2.2.2.2.1
  unfold c5 at h
  rw [List.all_eq_true] at h
  have hc := h s (List.mem_range.mpr hs)
  rw [hr, Bool.not_true, Bool.false_or, beq_iff_eq] at hc
  rw [hc, Ncode_succ]
  have e : ∀ rc ∈ range 9, (if guardB s rc = true then Ncode (succS s rc) 4 else 0) =
      (if guardB s rc = true then tab4 (succS s rc) else 0) := by
    intro rc hrc
    split_ifs with hg
    · exact tab_eq4 _ (succ_lt s rc hs (mem_range.mp hrc) hg)
        (reach_succ s rc hs (mem_range.mp hrc) hg hr)
    · rfl
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

theorem tab_eq6 (s : ℕ) (hs : s < 324) (hr : reach s = true) :
    Ncode s 6 = tab6 s := by
  have h := tabs_split.2.2.2.2.2.2.2.2.2.2.1
  unfold c6 at h
  rw [List.all_eq_true] at h
  have hc := h s (List.mem_range.mpr hs)
  rw [hr, Bool.not_true, Bool.false_or, beq_iff_eq] at hc
  rw [hc, Ncode_succ]
  have e : ∀ rc ∈ range 9, (if guardB s rc = true then Ncode (succS s rc) 5 else 0) =
      (if guardB s rc = true then tab5 (succS s rc) else 0) := by
    intro rc hrc
    split_ifs with hg
    · exact tab_eq5 _ (succ_lt s rc hs (mem_range.mp hrc) hg)
        (reach_succ s rc hs (mem_range.mp hrc) hg hr)
    · rfl
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

/-- The recurrence of order 6 of the continuation counts, on every reachable state. -/
theorem Ncode_rec (m : ℕ) : ∀ s, s < 324 → reach s = true →
    (Ncode s (m + 6) : ℤ) = (15 : ℤ) * (Ncode s (m + 5) : ℤ) + (-87 : ℤ) * (Ncode s (m + 4) : ℤ) + (245 : ℤ) * (Ncode s (m + 3) : ℤ) + (-348 : ℤ) * (Ncode s (m + 2) : ℤ) + (240 : ℤ) * (Ncode s (m + 1) : ℤ) + (-64 : ℤ) * (Ncode s m : ℤ) := by
  induction m with
  | zero =>
    intro s hs hr
    simp only [zero_add]
    rw [tab_eq6 s hs hr, tab_eq5 s hs hr, tab_eq4 s hs hr, tab_eq3 s hs hr, tab_eq2 s hs hr, tab_eq1 s hs hr, tab_eq0 s hs hr]
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
    show (Ncode s (m + 1 + 6) : ℤ) = (15 : ℤ) * (Ncode s (m + 1 + 5) : ℤ) + (-87 : ℤ) * (Ncode s (m + 1 + 4) : ℤ) + (245 : ℤ) * (Ncode s (m + 1 + 3) : ℤ) + (-348 : ℤ) * (Ncode s (m + 1 + 2) : ℤ) + (240 : ℤ) * (Ncode s (m + 1 + 1) : ℤ) + (-64 : ℤ) * (Ncode s (m + 1) : ℤ)
    rw [Ncode_succ s (m + 6), Ncode_succ s (m + 5), Ncode_succ s (m + 4), Ncode_succ s (m + 3), Ncode_succ s (m + 2), Ncode_succ s (m + 1), Ncode_succ s m]
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

/-- The recurrence of order 6: a(n) for n >= 7. -/
theorem a_rec (m : ℕ) : (a (m + 7) : ℤ) = (15 : ℤ) * (a (m + 6) : ℤ) + (-87 : ℤ) * (a (m + 5) : ℤ) + (245 : ℤ) * (a (m + 4) : ℤ) + (-348 : ℤ) * (a (m + 3) : ℤ) + (240 : ℤ) * (a (m + 2) : ℤ) + (-64 : ℤ) * (a (m + 1) : ℤ) := by
  rw [a_code (m + 6), a_code (m + 5), a_code (m + 4), a_code (m + 3), a_code (m + 2), a_code (m + 1), a_code m]
  push_cast
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine sum_congr rfl (fun cc hcc => ?_)
  split_ifs with hg
  · exact Ncode_rec m _ (init_ok cc (mem_range.mp hcc) hg).1 (init_ok cc (mem_range.mp hcc) hg).2
  · simp

theorem v1 : a 1 = 1 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, a_code]
  have e : ∀ cc ∈ range 9, (if rgsC 0 cc = true then Ncode (enc 0 cc (limC 0 cc) 0) 0 else 0) =
      (if rgsC 0 cc = true then tab0 (enc 0 cc (limC 0 cc) 0) else 0) := by
    intro cc hcc
    split_ifs with hg
    · exact tab_eq0 _ (init_ok cc (mem_range.mp hcc) hg).1 (init_ok cc (mem_range.mp hcc) hg).2
    · rfl
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have h := tabs_split.2.2.2.2.2.2.2.2.2.2.2.1
  unfold cval0 at h
  exact beq_iff_eq.mp h

theorem v2 : a 2 = 6 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, a_code]
  have e : ∀ cc ∈ range 9, (if rgsC 0 cc = true then Ncode (enc 0 cc (limC 0 cc) 0) 1 else 0) =
      (if rgsC 0 cc = true then tab1 (enc 0 cc (limC 0 cc) 0) else 0) := by
    intro cc hcc
    split_ifs with hg
    · exact tab_eq1 _ (init_ok cc (mem_range.mp hcc) hg).1 (init_ok cc (mem_range.mp hcc) hg).2
    · rfl
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have h := tabs_split.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold cval1 at h
  exact beq_iff_eq.mp h

theorem v3 : a 3 = 30 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, a_code]
  have e : ∀ cc ∈ range 9, (if rgsC 0 cc = true then Ncode (enc 0 cc (limC 0 cc) 0) 2 else 0) =
      (if rgsC 0 cc = true then tab2 (enc 0 cc (limC 0 cc) 0) else 0) := by
    intro cc hcc
    split_ifs with hg
    · exact tab_eq2 _ (init_ok cc (mem_range.mp hcc) hg).1 (init_ok cc (mem_range.mp hcc) hg).2
    · rfl
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have h := tabs_split.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold cval2 at h
  exact beq_iff_eq.mp h

theorem v4 : a 4 = 158 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, a_code]
  have e : ∀ cc ∈ range 9, (if rgsC 0 cc = true then Ncode (enc 0 cc (limC 0 cc) 0) 3 else 0) =
      (if rgsC 0 cc = true then tab3 (enc 0 cc (limC 0 cc) 0) else 0) := by
    intro cc hcc
    split_ifs with hg
    · exact tab_eq3 _ (init_ok cc (mem_range.mp hcc) hg).1 (init_ok cc (mem_range.mp hcc) hg).2
    · rfl
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have h := tabs_split.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold cval3 at h
  exact beq_iff_eq.mp h

theorem v5 : a 5 = 846 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, a_code]
  have e : ∀ cc ∈ range 9, (if rgsC 0 cc = true then Ncode (enc 0 cc (limC 0 cc) 0) 4 else 0) =
      (if rgsC 0 cc = true then tab4 (enc 0 cc (limC 0 cc) 0) else 0) := by
    intro cc hcc
    split_ifs with hg
    · exact tab_eq4 _ (init_ok cc (mem_range.mp hcc) hg).1 (init_ok cc (mem_range.mp hcc) hg).2
    · rfl
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have h := tabs_split.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold cval4 at h
  exact beq_iff_eq.mp h

theorem v6 : a 6 = 4446 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, a_code]
  have e : ∀ cc ∈ range 9, (if rgsC 0 cc = true then Ncode (enc 0 cc (limC 0 cc) 0) 5 else 0) =
      (if rgsC 0 cc = true then tab5 (enc 0 cc (limC 0 cc) 0) else 0) := by
    intro cc hcc
    split_ifs with hg
    · exact tab_eq5 _ (init_ok cc (mem_range.mp hcc) hg).1 (init_ok cc (mem_range.mp hcc) hg).2
    · rfl
  rw [sum_congr rfl e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have h := tabs_split.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  unfold cval5 at h
  exact beq_iff_eq.mp h

/-- Barker's g.f., as A(x) ((1 - X) ^ 3 * (1 - 4 * X) ^ 3) = X * (1 - 3 * X) * (1 - 6 * X + 9 * X ^ 2 + 12 * X ^ 3) in Z[[x]], with A(x) = Sum_{n >= 1} a(n) x^n. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * ((1 - X) ^ 3 * (1 - 4 * X) ^ 3) = X * (1 - 3 * X) * (1 - 6 * X + 9 * X ^ 2 + 12 * X ^ 3) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * ((1 - X) ^ 3 * (1 - 4 * X) ^ 3) = A - C 15 * (A * X ^ 1) + C 87 * (A * X ^ 2) - C 245 * (A * X ^ 3) + C 348 * (A * X ^ 4) - C 240 * (A * X ^ 5) + C 64 * (A * X ^ 6) := by
    simp only [map_ofNat]; ring
  have e2 : (X * (1 - 3 * X) * (1 - 6 * X + 9 * X ^ 2 + 12 * X ^ 3) : ℤ⟦X⟧) = X ^ 1 - X ^ 2 * C 9 + X ^ 3 * C 27 - X ^ 4 * C 15 - X ^ 5 * C 36 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  rcases Nat.lt_or_ge n 7 with hn | hn
  · interval_cases n <;> simp [v1, v2, v3, v4, v5, v6]
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 7 := ⟨n - 7, by omega⟩
    have h := a_rec q
    simp only [show q + 7 - 1 = q + 6 by omega, 
      show 1 ≤ q + 7 by omega, 
      show ¬ q + 6 = 0 by omega, 
      show q + 7 - 2 = q + 5 by omega, 
      show 2 ≤ q + 7 by omega, 
      show ¬ q + 5 = 0 by omega, 
      show q + 7 - 3 = q + 4 by omega, 
      show 3 ≤ q + 7 by omega, 
      show ¬ q + 4 = 0 by omega, 
      show q + 7 - 4 = q + 3 by omega, 
      show 4 ≤ q + 7 by omega, 
      show ¬ q + 3 = 0 by omega, 
      show q + 7 - 5 = q + 2 by omega, 
      show 5 ≤ q + 7 by omega, 
      show ¬ q + 2 = 0 by omega, 
      show q + 7 - 6 = q + 1 by omega, 
      show 6 ≤ q + 7 by omega, 
      show ¬ q + 1 = 0 by omega, 
      show ¬ q + 7 = 0 by omega, 
      show ¬ q + 7 = 1 by omega, 
      show ¬ q + 7 = 2 by omega, 
      show ¬ q + 7 = 3 by omega, 
      show ¬ q + 7 = 4 by omega, 
      show ¬ q + 7 = 5 by omega,
      if_true, if_false]
    rw [h]
    ring


/-- Barker's closed form, for n >= 1. -/
theorem closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = (8 * (4 ^ n - 1) + 21 * 4 ^ n * n + 6 * (32 + 4 ^ n) * n ^ 2) / 324 := by
  skip
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 7 with hlt | hge
    · interval_cases n
      · rw [v1]
        push_cast
        ring
      · rw [v2]
        push_cast
        ring
      · rw [v3]
        push_cast
        ring
      · rw [v4]
        push_cast
        ring
      · rw [v5]
        push_cast
        ring
      · rw [v6]
        push_cast
        ring
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
      have hR : (a (k + 7) : ℚ) = (15 : ℚ) * (a (k + 6) : ℚ) + (-87 : ℚ) * (a (k + 5) : ℚ) + (245 : ℚ) * (a (k + 4) : ℚ) + (-348 : ℚ) * (a (k + 3) : ℚ) + (240 : ℚ) * (a (k + 2) : ℚ) + (-64 : ℚ) * (a (k + 1) : ℚ) := by exact_mod_cast a_rec k
      rw [hR, ih (k + 6) (by omega) (by omega), ih (k + 5) (by omega) (by omega), ih (k + 4) (by omega) (by omega), ih (k + 3) (by omega) (by omega), ih (k + 2) (by omega) (by omega), ih (k + 1) (by omega) (by omega)]
      push_cast
      ring

/-- Controls: the entry's data a(1..12). -/
theorem controls : a 1 = 1 ∧ a 2 = 6 ∧ a 3 = 30 ∧ a 4 = 158 ∧ a 5 = 846 ∧ a 6 = 4446 ∧ a 7 = 22734 ∧ a 8 = 113310 ∧ a 9 = 552654 ∧ a 10 = 2647390 ∧ a 11 = 12492366 ∧ a 12 = 58202526 := by
  have v7 : a 7 = 22734 := by
    have h : (a 7 : ℤ) = (15 : ℤ) * (a 6 : ℤ) + (-87 : ℤ) * (a 5 : ℤ) + (245 : ℤ) * (a 4 : ℤ) + (-348 : ℤ) * (a 3 : ℤ) + (240 : ℤ) * (a 2 : ℤ) + (-64 : ℤ) * (a 1 : ℤ) := a_rec 0
    rw [v6, v5, v4, v3, v2, v1] at h
    omega
  have v8 : a 8 = 113310 := by
    have h : (a 8 : ℤ) = (15 : ℤ) * (a 7 : ℤ) + (-87 : ℤ) * (a 6 : ℤ) + (245 : ℤ) * (a 5 : ℤ) + (-348 : ℤ) * (a 4 : ℤ) + (240 : ℤ) * (a 3 : ℤ) + (-64 : ℤ) * (a 2 : ℤ) := a_rec 1
    rw [v7, v6, v5, v4, v3, v2] at h
    omega
  have v9 : a 9 = 552654 := by
    have h : (a 9 : ℤ) = (15 : ℤ) * (a 8 : ℤ) + (-87 : ℤ) * (a 7 : ℤ) + (245 : ℤ) * (a 6 : ℤ) + (-348 : ℤ) * (a 5 : ℤ) + (240 : ℤ) * (a 4 : ℤ) + (-64 : ℤ) * (a 3 : ℤ) := a_rec 2
    rw [v8, v7, v6, v5, v4, v3] at h
    omega
  have v10 : a 10 = 2647390 := by
    have h : (a 10 : ℤ) = (15 : ℤ) * (a 9 : ℤ) + (-87 : ℤ) * (a 8 : ℤ) + (245 : ℤ) * (a 7 : ℤ) + (-348 : ℤ) * (a 6 : ℤ) + (240 : ℤ) * (a 5 : ℤ) + (-64 : ℤ) * (a 4 : ℤ) := a_rec 3
    rw [v9, v8, v7, v6, v5, v4] at h
    omega
  have v11 : a 11 = 12492366 := by
    have h : (a 11 : ℤ) = (15 : ℤ) * (a 10 : ℤ) + (-87 : ℤ) * (a 9 : ℤ) + (245 : ℤ) * (a 8 : ℤ) + (-348 : ℤ) * (a 7 : ℤ) + (240 : ℤ) * (a 6 : ℤ) + (-64 : ℤ) * (a 5 : ℤ) := a_rec 4
    rw [v10, v9, v8, v7, v6, v5] at h
    omega
  have v12 : a 12 = 58202526 := by
    have h : (a 12 : ℤ) = (15 : ℤ) * (a 11 : ℤ) + (-87 : ℤ) * (a 10 : ℤ) + (245 : ℤ) * (a 9 : ℤ) + (-348 : ℤ) * (a 8 : ℤ) + (240 : ℤ) * (a 7 : ℤ) + (-64 : ℤ) * (a 6 : ℤ) := a_rec 5
    rw [v11, v10, v9, v8, v7, v6] at h
    omega
  exact ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12⟩

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * ((1 - X) ^ 3 * (1 - 4 * X) ^ 3) = X * (1 - 3 * X) * (1 - 6 * X + 9 * X ^ 2 + 12 * X ^ 3) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (8 * (4 ^ n - 1) + 21 * 4 ^ n * n + 6 * (32 + 4 ^ n) * n ^ 2) / 324 :=
  ⟨gf, closed⟩

end OMA.S_oeis_a280474

theorem OMA.solution : type_of% @OMA.S_oeis_a280474.main :=
  OMA.S_oeis_a280474.conjecture
