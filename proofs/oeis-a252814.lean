import OMAStatements.S_oeis_a252814

namespace OMA.S_oeis_a252814

open PowerSeries Finset



/-! ## The arrays y = (city block distance) - x -/

/-- Consecutive entries of a row of y stay or increase by 1. -/
def hrow (r : Fin 2 → Fin 3) : Prop := ∀ j j' : Fin 2, j'.val = j.val + 1 → r j' = r j ∨ (r j').val = (r j).val + 1

/-- Every entry of the row s below r stays or increases by 1. -/
def ok (r s : Fin 2 → Fin 3) : Prop := ∀ j, s j = r j ∨ (s j).val = (r j).val + 1

instance (r : Fin 2 → Fin 3) : Decidable (hrow r) := by unfold hrow; infer_instance

instance (r s : Fin 2 → Fin 3) : Decidable (ok r s) := by unfold ok; infer_instance

/-! ## Counting by the first row -/

/-- Every row is allowed and consecutive rows are compatible. -/
def Valid {n : ℕ} (g : Fin n → Fin 2 → Fin 3) : Prop :=
  (∀ i, hrow (g i)) ∧ ∀ i i' : Fin n, i'.val = i.val + 1 → ok (g i) (g i')

instance {n : ℕ} : DecidablePred (@Valid n) := fun g => by unfold Valid; infer_instance

/-- W(n, r): the arrays of n + 1 allowed rows with first row r, consecutive rows compatible. -/
def W (n : ℕ) (r : Fin 2 → Fin 3) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 2 → Fin 3)).filter (fun g => Valid g ∧ g 0 = r)).card

lemma valid_cons {n : ℕ} (x : Fin 2 → Fin 3) (g : Fin (n + 1) → Fin 2 → Fin 3) :
    Valid (Fin.cons x g : Fin (n + 2) → Fin 2 → Fin 3) ↔ hrow x ∧ ok x (g 0) ∧ Valid g := by
  constructor
  · rintro ⟨hr, h⟩
    refine ⟨by simpa using hr 0, ?_, fun i => by simpa using hr i.succ, ?_⟩
    · have := h 0 1 (by simp)
      simpa using this
    · intro i j hij
      have := h i.succ j.succ (by simp [hij])
      simpa using this
  · rintro ⟨hx, h0, hg, hgo⟩
    refine ⟨?_, ?_⟩
    · intro i
      induction i using Fin.cases with
      | zero => simpa using hx
      | succ i => simpa using hg i
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => simp at hij
        | succ j =>
          have hj : j = 0 := by ext; simp at hij; omega
          subst hj
          simpa using h0
      | succ i =>
        induction j using Fin.cases with
        | zero => simp at hij
        | succ j =>
          simp only [Fin.cons_succ]
          exact hgo i j (by simp at hij; omega)

lemma W_zero (r : Fin 2 → Fin 3) : W 0 r = if hrow r then 1 else 0 := by
  unfold W
  split_ifs with hr
  · rw [Finset.card_eq_one]
    refine ⟨fun _ => r, ?_⟩
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hf⟩
      funext i
      rw [Fin.fin_one_eq_zero i, hf]
    · rintro rfl
      refine ⟨⟨fun _ => hr, ?_⟩, rfl⟩
      intro i j hij
      have := j.isLt
      omega
  · rw [Finset.card_eq_zero]
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨⟨h1, _⟩, h0⟩
    apply hr
    rw [← h0]
    exact h1 0

/-- Prepending the row r to an array with n + 1 rows. -/
def consEmb (n : ℕ) (r : Fin 2 → Fin 3) :
    (Fin (n + 1) → Fin 2 → Fin 3) ↪ (Fin (n + 2) → Fin 2 → Fin 3) where
  toFun g := Fin.cons r g
  inj' g g' h := by
    funext i
    have := congrFun h i.succ
    simpa using this

lemma consEmb_apply (n : ℕ) (r : Fin 2 → Fin 3) (g : Fin (n + 1) → Fin 2 → Fin 3) :
    consEmb n r g = Fin.cons r g := rfl

lemma W_succ (n : ℕ) (r : Fin 2 → Fin 3) :
    W (n + 1) r = if hrow r then ∑ s : Fin 2 → Fin 3, (if ok r s then W n s else 0) else 0 := by
  have e : ((univ : Finset (Fin (n + 2) → Fin 2 → Fin 3)).filter (fun f => Valid f ∧ f 0 = r)) =
      (((univ : Finset (Fin (n + 1) → Fin 2 → Fin 3)).filter
        (fun g => (hrow r ∧ ok r (g 0)) ∧ Valid g)).map (consEmb n r)) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, consEmb_apply]
    constructor
    · rintro ⟨hv, h0⟩
      refine ⟨Fin.tail f, ?_, ?_⟩
      · have hf : f = Fin.cons r (Fin.tail f) := by
          rw [← h0]; exact (Fin.cons_self_tail f).symm
        rw [hf, valid_cons] at hv
        exact ⟨⟨hv.1, hv.2.1⟩, hv.2.2⟩
      · rw [← h0]; exact Fin.cons_self_tail f
    · rintro ⟨g, ⟨⟨h1, h2⟩, hg⟩, rfl⟩
      exact ⟨(valid_cons r g).2 ⟨h1, h2, hg⟩, by simp⟩
  unfold W
  rw [e, Finset.card_map]
  split_ifs with hrc
  · rw [Finset.card_eq_sum_card_fiberwise (f := fun g => g 0) (t := univ) (by simp)]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    split_ifs with hrs
    · congr 1
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨_, hg⟩, h0⟩
        exact ⟨hg, h0⟩
      · rintro ⟨hg, h0⟩
        exact ⟨⟨⟨hrc, by rw [h0]; exact hrs⟩, hg⟩, h0⟩
    · rw [Finset.card_eq_zero]
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨⟨⟨_, h2⟩, _⟩, h0⟩
      exact hrs (by rw [← h0]; exact h2)
  · rw [Finset.card_eq_zero]
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨⟨h1, _⟩, _⟩
    exact hrc h1

lemma x_le {R : ℕ} (x : Fin R → Fin 2 → ℕ) (h : Cond x) (i : Fin R) (j : Fin 2) : x i j ≤ i.val + j.val := by
  obtain ⟨h0, -, hh, hv⟩ := h
  have row0 : ∀ (k : ℕ) (hk : k < 2) (i : Fin R), i.val = 0 → x i ⟨k, hk⟩ ≤ k := by
    intro k
    induction k with
    | zero => intro hk i hi; rw [h0 i ⟨0, hk⟩ hi rfl]
    | succ k ih =>
      intro hk i hi
      have := ih (by omega) i hi
      rcases hh i ⟨k, by omega⟩ ⟨k + 1, hk⟩ rfl with e | e <;> omega
  have key : ∀ (t : ℕ) (i : Fin R), i.val = t → x i j ≤ i.val + j.val := by
    intro t
    induction t with
    | zero => intro i hi; have := row0 j.val j.isLt i hi; rw [hi]; simpa using this
    | succ t ih =>
      intro i hi
      have := ih ⟨t, by omega⟩ rfl
      rcases hv ⟨t, by omega⟩ i j (by simp [hi]) with e | e <;> simp only at this <;> omega
  exact key i.val i rfl

/-- The arrays y: y(0,0) = 0, every row allowed, consecutive rows compatible. -/
def YCond {R : ℕ} (y : Fin R → Fin 2 → Fin 3) : Prop :=
  Valid y ∧ ∀ i j, i.val = 0 → j.val = 0 → y i j = 0

instance {R : ℕ} : DecidablePred (@YCond R) := fun y => by unfold YCond; infer_instance

lemma y_le {R : ℕ} (y : Fin R → Fin 2 → Fin 3) (hy : YCond y) (i : Fin R) (j : Fin 2) : (y i j).val ≤ i.val + j.val := by
  obtain ⟨⟨hh, hv⟩, h0⟩ := hy
  have row0 : ∀ (k : ℕ) (hk : k < 2) (i : Fin R), i.val = 0 → (y i ⟨k, hk⟩).val ≤ k := by
    intro k
    induction k with
    | zero => intro hk i hi; rw [h0 i ⟨0, hk⟩ hi rfl]; rfl
    | succ k ih =>
      intro hk i hi
      have := ih (by omega) i hi
      rcases hh i ⟨k, by omega⟩ ⟨k + 1, hk⟩ rfl with e | e
      · rw [e]; omega
      · omega
  have key : ∀ (t : ℕ) (i : Fin R), i.val = t → (y i j).val ≤ i.val + j.val := by
    intro t
    induction t with
    | zero => intro i hi; have := row0 j.val j.isLt i hi; rw [hi]; simpa using this
    | succ t ih =>
      intro i hi
      have := ih ⟨t, by omega⟩ rfl
      rcases hv ⟨t, by omega⟩ i (by simp [hi]) j with e | e
      · rw [e]; simp only at this; omega
      · simp only at this; omega
  exact key i.val i rfl

/-- x and y = i + j - x determine each other. -/
lemma card_eq (R : ℕ) : {x : Fin R → Fin 2 → ℕ | Cond x}.ncard =
    ((univ : Finset (Fin R → Fin 2 → Fin 3)).filter YCond).card := by
  have himg : {x : Fin R → Fin 2 → ℕ | Cond x} =
      (fun y : Fin R → Fin 2 → Fin 3 => fun i j => i.val + j.val - (y i j).val) ''
        ↑((univ : Finset (Fin R → Fin 2 → Fin 3)).filter YCond) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_image, coe_filter, mem_univ, true_and]
    constructor
    · intro hx
      have hle := x_le x hx
      obtain ⟨h0, hw, hh, hv⟩ := hx
      refine ⟨fun i j => ⟨i.val + j.val - x i j, by have := (hw i j).2; omega⟩, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · intro i j j' hj
        have h1 := hle i j
        have h2 := hle i j'
        rcases hh i j j' hj with e | e
        · right; simp only; omega
        · left; ext; simp only; omega
      · intro i i' hi j
        have h1 := hle i j
        have h2 := hle i' j
        rcases hv i i' j hi with e | e
        · right; simp only; omega
        · left; ext; simp only; omega
      · intro i j hi hj
        ext; simp only [Fin.val_zero]; rw [h0 i j hi hj]; omega
      · funext i j
        have := hle i j
        simp only
        omega
    · rintro ⟨y, hy, rfl⟩
      have hle := y_le y hy
      obtain ⟨⟨hh, hv⟩, h0⟩ := hy
      refine ⟨fun i j hi hj => ?_, fun i j => ?_, ?_, ?_⟩
      · dsimp only
        rw [h0 i j hi hj, hi, hj]; rfl
      · dsimp only
        have := (y i j).isLt
        omega
      · intro i j j' hj
        dsimp only
        have h1 := hle i j
        have h2 := hle i j'
        rcases hh i j j' hj with e | e
        · right; rw [e]; omega
        · left; omega
      · intro i i' j hi
        dsimp only
        have h1 := hle i j
        have h2 := hle i' j
        rcases hv i i' hi j with e | e
        · right; rw [e]; omega
        · left; omega
  have hinj : Set.InjOn (fun y : Fin R → Fin 2 → Fin 3 => fun i j => i.val + j.val - (y i j).val)
      ↑((univ : Finset (Fin R → Fin 2 → Fin 3)).filter YCond) := by
    intro y hy y' hy' e
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hy hy'
    funext i j
    have h1 := y_le y hy i j
    have h2 := y_le y' hy' i j
    have := congrFun (congrFun e i) j
    simp only at this
    ext; omega
  rw [himg, hinj.ncard_image, Set.ncard_coe_finset]

lemma a_eq (n : ℕ) : a (n + 1) = ∑ r : Fin 2 → Fin 3, if r 0 = 0 then W n r else 0 := by
  unfold a
  rw [card_eq, Finset.card_eq_sum_card_fiberwise (f := fun g => g 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Finset.filter_filter]
  split_ifs with hr
  · unfold W
    congr 1
    refine Finset.filter_congr (fun g _ => ?_)
    unfold YCond
    constructor
    · rintro ⟨⟨hv, _⟩, h0⟩
      exact ⟨hv, h0⟩
    · rintro ⟨hv, h0⟩
      refine ⟨⟨hv, fun i j hi hj => ?_⟩, h0⟩
      obtain rfl : i = 0 := Fin.ext hi
      obtain rfl : j = 0 := Fin.ext hj
      rw [h0]; exact hr
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro g - ⟨⟨_, h00⟩, h0⟩
    exact hr (by rw [← h0]; exact h00 0 0 rfl rfl)

/-! ## Kernel form of the transfer -/

lemma sum_cons {m : ℕ} (f : (Fin (m + 1) → Fin 3) → ℕ) :
    ∑ s : Fin (m + 1) → Fin 3, f s = ∑ x : Fin 3, ∑ t : Fin m → Fin 3, f (Fin.cons x t) := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 3).symm _ _
    (fun s => by simp [Fin.consEquiv, Fin.cons_self_tail])

lemma sum_row (f : (Fin 2 → Fin 3) → ℕ) :
    ∑ s : Fin 2 → Fin 3, f s = ∑ x : Fin 3, ∑ y : Fin 3, f ![x, y] := by
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Fintype.sum_unique]
  exact congrArg f (by funext j; fin_cases j <;> rfl)

lemma row_eta (r : Fin 2 → Fin 3) : r = ![r 0, r 1] := by
  funext j
  fin_cases j <;> rfl

/-- `hrow` as a Boolean. -/
def hrowB (r : Fin 2 → Fin 3) : Bool :=
  decide (r 1 = r 0 ∨ (r 1).val = (r 0).val + 1)

/-- The entry b below the entry a stays or increases by 1. -/
def okC (a b : Fin 3) : Bool := decide (b = a ∨ b.val = a.val + 1)

/-- `ok` as a Boolean. -/
def okB (r s : Fin 2 → Fin 3) : Bool :=
  okC (r 0) (s 0) &&
    okC (r 1) (s 1)

lemma hrow_iff (r : Fin 2 → Fin 3) : hrow r ↔ hrowB r = true := by
  simp only [hrowB, decide_eq_true_eq]
  constructor
  · intro h
    exact h 0 1 rfl
  · intro h j j' hj
    have := j'.isLt
    obtain rfl : j = 0 := Fin.ext (by show j.val = 0; omega)
    obtain rfl : j' = 1 := Fin.ext (by show j'.val = 1; omega)
    exact h

lemma ok_iff (r s : Fin 2 → Fin 3) : ok r s ↔ okB r s = true := by
  simp only [okB, okC, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  constructor
  · intro h
    exact ⟨h 0, h 1⟩
  · intro h j
    fin_cases j
    · exact h.1
    · exact h.2

/-- One step of the transfer, the rows below r enumerated entry by entry. -/
def T (g : (Fin 2 → Fin 3) → ℕ) (r : Fin 2 → Fin 3) : ℕ :=
  if hrowB r = true then
    ∑ x : Fin 3, ∑ y : Fin 3, (if okB r ![x, y] = true then g ![x, y] else 0)
  else 0

lemma W_succT (n : ℕ) (r : Fin 2 → Fin 3) : W (n + 1) r = T (W n) r := by
  rw [W_succ, sum_row]
  unfold T
  simp only [hrow_iff, ok_iff]

lemma T_congr (g g' : (Fin 2 → Fin 3) → ℕ) (r : Fin 2 → Fin 3) (h : ∀ s, g s = g' s) : T g r = T g' r := by
  unfold T
  simp only [h]

/-- `T` with the sums over the cells of the row below cut as soon as a cell fails `okC`. -/
def Tp (g : (Fin 2 → Fin 3) → ℕ) (r : Fin 2 → Fin 3) : ℕ :=
  if hrowB r = true then
    ∑ x : Fin 3, (if okC (r 0) x = true then (∑ y : Fin 3, (if okC (r 1) y = true then (g ![x, y]) else 0)) else 0)
  else 0

lemma T_eq_Tp (g : (Fin 2 → Fin 3) → ℕ) (r : Fin 2 → Fin 3) : T g r = Tp g r := by
  unfold T Tp
  by_cases hr : hrowB r = true
  · rw [if_pos hr, if_pos hr]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases h0 : okC (r 0) x = true
    · rw [if_pos h0]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      by_cases h1 : okC (r 1) y = true
      · rw [if_pos h1, if_pos (show okB r ![x, y] = true by simp [okB, h0, h1])]
      · rw [if_neg h1, if_neg (show ¬ okB r ![x, y] = true by simp [okB, h1])]
    · rw [if_neg h0]
      simp [okB, h0]
  · rw [if_neg hr, if_neg hr]

/-- W(0) as a function. -/
def W0f (r : Fin 2 → Fin 3) : ℕ := if hrowB r = true then 1 else 0

lemma W_zero' (r : Fin 2 → Fin 3) : W 0 r = W0f r := by
  rw [W_zero]
  unfold W0f
  simp only [hrow_iff]

/-- W(1, r), nested by the entries of r. -/
def L1 : List (List ℕ) :=
  [[3, 3, 0], [0, 3, 2], [0, 0, 1]]

/-- W(1) as a table. -/
def tab1 (r : Fin 2 → Fin 3) : ℕ := (L1.getD (r 0).val []).getD (r 1).val 0

/-- W(2, r), nested by the entries of r. -/
def L2 : List (List ℕ) :=
  [[9, 8, 0], [0, 6, 3], [0, 0, 1]]

/-- W(2) as a table. -/
def tab2 (r : Fin 2 → Fin 3) : ℕ := (L2.getD (r 0).val []).getD (r 1).val 0

/-- W(3, r), nested by the entries of r. -/
def L3 : List (List ℕ) :=
  [[23, 17, 0], [0, 10, 4], [0, 0, 1]]

/-- W(3) as a table. -/
def tab3 (r : Fin 2 → Fin 3) : ℕ := (L3.getD (r 0).val []).getD (r 1).val 0

/-- W(4, r), nested by the entries of r. -/
def L4 : List (List ℕ) :=
  [[50, 31, 0], [0, 15, 5], [0, 0, 1]]

/-- W(4) as a table. -/
def tab4 (r : Fin 2 → Fin 3) : ℕ := (L4.getD (r 0).val []).getD (r 1).val 0

set_option maxHeartbeats 4000000 in
lemma checks_all :
    (∀ y1 y2 : Fin 3,
    Tp W0f ![y1, y2] = tab1 ![y1, y2]) ∧
    (∀ y1 y2 : Fin 3,
    Tp tab1 ![y1, y2] = tab2 ![y1, y2]) ∧
    (∀ y1 y2 : Fin 3,
    Tp tab2 ![y1, y2] = tab3 ![y1, y2]) ∧
    (∀ y1 y2 : Fin 3,
    Tp tab3 ![y1, y2] = tab4 ![y1, y2]) ∧
    (∀ y1 y2 : Fin 3,
    Tp tab4 ![y1, y2] + 10 * tab3 ![y1, y2] + 5 * tab1 ![y1, y2] =
      5 * tab4 ![y1, y2] + 10 * tab2 ![y1, y2] + W0f ![y1, y2]) ∧
    (∑ x : Fin 3, ∑ y : Fin 3, (if ![x, y] 0 = 0 then W0f ![x, y] else 0) = 2) ∧
    (∑ x : Fin 3, ∑ y : Fin 3, (if ![x, y] 0 = 0 then tab1 ![x, y] else 0) = 6) ∧
    (∑ x : Fin 3, ∑ y : Fin 3, (if ![x, y] 0 = 0 then tab2 ![x, y] else 0) = 17) ∧
    (∑ x : Fin 3, ∑ y : Fin 3, (if ![x, y] 0 = 0 then tab3 ![x, y] else 0) = 40) ∧
    (∑ x : Fin 3, ∑ y : Fin 3, (if ![x, y] 0 = 0 then tab4 ![x, y] else 0) = 81) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

lemma check1 : ∀ y1 y2 : Fin 3,
    Tp W0f ![y1, y2] = tab1 ![y1, y2] := checks_all.1

lemma check2 : ∀ y1 y2 : Fin 3,
    Tp tab1 ![y1, y2] = tab2 ![y1, y2] := checks_all.2.1

lemma check3 : ∀ y1 y2 : Fin 3,
    Tp tab2 ![y1, y2] = tab3 ![y1, y2] := checks_all.2.2.1

lemma check4 : ∀ y1 y2 : Fin 3,
    Tp tab3 ![y1, y2] = tab4 ![y1, y2] := checks_all.2.2.2.1

lemma check_rel : ∀ y1 y2 : Fin 3,
    Tp tab4 ![y1, y2] + 10 * tab3 ![y1, y2] + 5 * tab1 ![y1, y2] =
      5 * tab4 ![y1, y2] + 10 * tab2 ![y1, y2] + W0f ![y1, y2] := checks_all.2.2.2.2.1

lemma sum1 : ∑ x : Fin 3, ∑ y : Fin 3, (if ![x, y] 0 = 0 then W0f ![x, y] else 0) = 2 := checks_all.2.2.2.2.2.1

lemma sum2 : ∑ x : Fin 3, ∑ y : Fin 3, (if ![x, y] 0 = 0 then tab1 ![x, y] else 0) = 6 := checks_all.2.2.2.2.2.2.1

lemma sum3 : ∑ x : Fin 3, ∑ y : Fin 3, (if ![x, y] 0 = 0 then tab2 ![x, y] else 0) = 17 := checks_all.2.2.2.2.2.2.2.1

lemma sum4 : ∑ x : Fin 3, ∑ y : Fin 3, (if ![x, y] 0 = 0 then tab3 ![x, y] else 0) = 40 := checks_all.2.2.2.2.2.2.2.2.1

lemma sum5 : ∑ x : Fin 3, ∑ y : Fin 3, (if ![x, y] 0 = 0 then tab4 ![x, y] else 0) = 81 := checks_all.2.2.2.2.2.2.2.2.2

lemma W_1 (r : Fin 2 → Fin 3) : W 1 r = tab1 r := by
  rw [W_succT, T_congr _ W0f r W_zero', T_eq_Tp, row_eta r]
  exact check1 (r 0) (r 1)

lemma W_2 (r : Fin 2 → Fin 3) : W 2 r = tab2 r := by
  rw [show W 2 r = W (1 + 1) r from rfl, W_succT, T_congr _ tab1 r W_1, T_eq_Tp,
    row_eta r]
  exact check2 (r 0) (r 1)

lemma W_3 (r : Fin 2 → Fin 3) : W 3 r = tab3 r := by
  rw [show W 3 r = W (2 + 1) r from rfl, W_succT, T_congr _ tab2 r W_2, T_eq_Tp,
    row_eta r]
  exact check3 (r 0) (r 1)

lemma W_4 (r : Fin 2 → Fin 3) : W 4 r = tab4 r := by
  rw [show W 4 r = W (3 + 1) r from rfl, W_succT, T_congr _ tab3 r W_3, T_eq_Tp,
    row_eta r]
  exact check4 (r 0) (r 1)

lemma W_rec (n : ℕ) : ∀ r : Fin 2 → Fin 3, W (n + 5) r + 10 * W (n + 3) r + 5 * W (n + 1) r = 5 * W (n + 4) r + 10 * W (n + 2) r + W n r := by
  induction n with
  | zero =>
    intro r
    rw [show W (0 + 5) r = W (4 + 1) r from rfl, W_succT 4 r,
      T_congr _ tab4 r W_4,
      W_zero' r,
      show W (0 + 1) r = W 1 r from rfl, W_1 r,
      show W (0 + 2) r = W 2 r from rfl, W_2 r,
      show W (0 + 3) r = W 3 r from rfl, W_3 r,
      show W (0 + 4) r = W 4 r from rfl, W_4 r,
      T_eq_Tp,
      row_eta r]
    exact check_rel (r 0) (r 1)
  | succ n ih =>
    intro r
    rw [W_succT (n + 5) r, W_succT (n + 4) r, W_succT (n + 3) r, W_succT (n + 2) r, W_succT (n + 1) r, W_succT n r]
    unfold T
    by_cases h : hrowB r = true
    · rw [if_pos h, if_pos h, if_pos h, if_pos h, if_pos h, if_pos h]
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      split_ifs
      · exact ih _
      · simp
    · rw [if_neg h, if_neg h, if_neg h, if_neg h, if_neg h, if_neg h] <;> simp

lemma a_rec (n : ℕ) : a (n + 6) + 10 * a (n + 4) + 5 * a (n + 2) = 5 * a (n + 5) + 10 * a (n + 3) + a (n + 1) := by
  rw [a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  split_ifs
  · exact W_rec n r
  · simp

lemma a_1 : a 1 = 2 := by
  rw [show a 1 = a (0 + 1) from rfl, a_eq, sum_row]
  have h : ∀ r : Fin 2 → Fin 3, (if r 0 = 0 then W 0 r else 0) = (if r 0 = 0 then W0f r else 0) := fun r => by split_ifs <;> simp only [W_zero']
  simp only [h]
  exact sum1

lemma a_2 : a 2 = 6 := by
  rw [show a 2 = a (1 + 1) from rfl, a_eq, sum_row]
  have h : ∀ r : Fin 2 → Fin 3, (if r 0 = 0 then W 1 r else 0) = (if r 0 = 0 then tab1 r else 0) := fun r => by split_ifs <;> simp only [W_1]
  simp only [h]
  exact sum2

lemma a_3 : a 3 = 17 := by
  rw [show a 3 = a (2 + 1) from rfl, a_eq, sum_row]
  have h : ∀ r : Fin 2 → Fin 3, (if r 0 = 0 then W 2 r else 0) = (if r 0 = 0 then tab2 r else 0) := fun r => by split_ifs <;> simp only [W_2]
  simp only [h]
  exact sum3

lemma a_4 : a 4 = 40 := by
  rw [show a 4 = a (3 + 1) from rfl, a_eq, sum_row]
  have h : ∀ r : Fin 2 → Fin 3, (if r 0 = 0 then W 3 r else 0) = (if r 0 = 0 then tab3 r else 0) := fun r => by split_ifs <;> simp only [W_3]
  simp only [h]
  exact sum4

lemma a_5 : a 5 = 81 := by
  rw [show a 5 = a (4 + 1) from rfl, a_eq, sum_row]
  have h : ∀ r : Fin 2 → Fin 3, (if r 0 = 0 then W 4 r else 0) = (if r 0 = 0 then tab4 r else 0) := fun r => by split_ifs <;> simp only [W_4]
  simp only [h]
  exact sum5

/-- Barker's g.f. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
      X * (2 - 4 * X + 7 * X ^ 2 - 5 * X ^ 3 + X ^ 4) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - X) ^ 5 = A - A * X ^ 1 * C 5 + A * X ^ 2 * C 10 - A * X ^ 3 * C 10 + A * X ^ 4 * C 5 - A * X ^ 5 * C 1 := by
    rw [show (C (1 : ℚ) : ℚ⟦X⟧) = 1 from map_one C,
      show (C (5 : ℚ) : ℚ⟦X⟧) = 5 from map_ofNat C 5,
      show (C (10 : ℚ) : ℚ⟦X⟧) = 10 from map_ofNat C 10]
    ring
  have e2 : (X * (2 - 4 * X + 7 * X ^ 2 - 5 * X ^ 3 + X ^ 4) : ℚ⟦X⟧) = X ^ 1 * C 2 - X ^ 2 * C 4 + X ^ 3 * C 7 - X ^ 4 * C 5 + X ^ 5 * C 1 := by
    rw [show (C (1 : ℚ) : ℚ⟦X⟧) = 1 from map_one C,
      show (C (2 : ℚ) : ℚ⟦X⟧) = 2 from map_ofNat C 2,
      show (C (4 : ℚ) : ℚ⟦X⟧) = 4 from map_ofNat C 4,
      show (C (5 : ℚ) : ℚ⟦X⟧) = 5 from map_ofNat C 5,
      show (C (7 : ℚ) : ℚ⟦X⟧) = 7 from map_ofNat C 7]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk]
  rcases n with _ | _ | _ | _ | _ | _ | n
  · simp
  · simp [a_1] <;> norm_num
  · simp [a_1, a_2] <;> norm_num
  · simp [a_1, a_2, a_3] <;> norm_num
  · simp [a_1, a_2, a_3, a_4] <;> norm_num
  · simp [a_1, a_2, a_3, a_4, a_5] <;> norm_num
  · have h := a_rec n
    
    have hq : (a (n + 6) : ℚ) + 10 * (a (n + 4) : ℚ) + 5 * (a (n + 2) : ℚ) = 5 * (a (n + 5) : ℚ) + 10 * (a (n + 3) : ℚ) + (a (n + 1) : ℚ) := by exact_mod_cast h
    simp only [show ¬ (n + 6 = 0) by omega,
      if_false,
      if_true,
      show 1 ≤ n + 6 by omega,
      show n + 6 - 1 = n + 5 by omega,
      show ¬ (n + 5 = 0) by omega,
      show 2 ≤ n + 6 by omega,
      show n + 6 - 2 = n + 4 by omega,
      show ¬ (n + 4 = 0) by omega,
      show 3 ≤ n + 6 by omega,
      show n + 6 - 3 = n + 3 by omega,
      show ¬ (n + 3 = 0) by omega,
      show 4 ≤ n + 6 by omega,
      show n + 6 - 4 = n + 2 by omega,
      show ¬ (n + 2 = 0) by omega,
      show 5 ≤ n + 6 by omega,
      show n + 6 - 5 = n + 1 by omega,
      show ¬ (n + 1 = 0) by omega,
      show ¬ (n + 6 = 1) by omega,
      show ¬ (n + 6 = 2) by omega,
      show ¬ (n + 6 = 3) by omega,
      show ¬ (n + 6 = 4) by omega,
      show ¬ (n + 6 = 5) by omega]
    linear_combination hq

/-- Barker's recurrence. -/
theorem rec_int : ∀ n : ℕ, 5 < n → (a n : ℤ) =
      5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  have h := a_rec m
  rw [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega, show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega, show m + 6 - 5 = m + 1 by omega]
  have hz : ((a (m + 6) + 10 * a (m + 4) + 5 * a (m + 2) : ℕ) : ℤ) = ((5 * a (m + 5) + 10 * a (m + 3) + a (m + 1) : ℕ) : ℤ) := by rw [h]
  push_cast at hz
  linarith

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
      X * (2 - 4 * X + 7 * X ^ 2 - 5 * X ^ 3 + X ^ 4) ∧
    ∀ n : ℕ, 5 < n → (a n : ℤ) =
      5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) :=
  ⟨gf, rec_int⟩

/-- Controls: the entry's terms a(1..10). -/
theorem controls : a 1 = 2 ∧ a 2 = 6 ∧ a 3 = 17 ∧ a 4 = 40 ∧ a 5 = 81 ∧ a 6 = 147 ∧ a 7 = 246 ∧ a 8 = 387 ∧ a 9 = 580 ∧ a 10 = 836 := by
  have h1 := a_1; have h2 := a_2; have h3 := a_3; have h4 := a_4; have h5 := a_5
  have r0 := a_rec 0; have r1 := a_rec 1; have r2 := a_rec 2; have r3 := a_rec 3; have r4 := a_rec 4
  norm_num at r0 r1 r2 r3 r4
  omega

end OMA.S_oeis_a252814

theorem OMA.solution : type_of% @OMA.S_oeis_a252814.main :=
  OMA.S_oeis_a252814.conjecture
