import OMAStatements.S_oeis_a252817

namespace OMA.S_oeis_a252817

open PowerSeries Finset



/-! ## The arrays y = (city block distance) - x -/

/-- Consecutive entries of a row of y stay or increase by 1. -/
def hrow (r : Fin 5 → Fin 3) : Prop := ∀ j j' : Fin 5, j'.val = j.val + 1 → r j' = r j ∨ (r j').val = (r j).val + 1

/-- Every entry of the row s below r stays or increases by 1. -/
def ok (r s : Fin 5 → Fin 3) : Prop := ∀ j, s j = r j ∨ (s j).val = (r j).val + 1

instance (r : Fin 5 → Fin 3) : Decidable (hrow r) := by unfold hrow; infer_instance

instance (r s : Fin 5 → Fin 3) : Decidable (ok r s) := by unfold ok; infer_instance

/-! ## Counting by the first row -/

/-- Every row is allowed and consecutive rows are compatible. -/
def Valid {n : ℕ} (g : Fin n → Fin 5 → Fin 3) : Prop :=
  (∀ i, hrow (g i)) ∧ ∀ i i' : Fin n, i'.val = i.val + 1 → ok (g i) (g i')

instance {n : ℕ} : DecidablePred (@Valid n) := fun g => by unfold Valid; infer_instance

/-- W(n, r): the arrays of n + 1 allowed rows with first row r, consecutive rows compatible. -/
def W (n : ℕ) (r : Fin 5 → Fin 3) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 5 → Fin 3)).filter (fun g => Valid g ∧ g 0 = r)).card

lemma valid_cons {n : ℕ} (x : Fin 5 → Fin 3) (g : Fin (n + 1) → Fin 5 → Fin 3) :
    Valid (Fin.cons x g : Fin (n + 2) → Fin 5 → Fin 3) ↔ hrow x ∧ ok x (g 0) ∧ Valid g := by
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

lemma W_zero (r : Fin 5 → Fin 3) : W 0 r = if hrow r then 1 else 0 := by
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
def consEmb (n : ℕ) (r : Fin 5 → Fin 3) :
    (Fin (n + 1) → Fin 5 → Fin 3) ↪ (Fin (n + 2) → Fin 5 → Fin 3) where
  toFun g := Fin.cons r g
  inj' g g' h := by
    funext i
    have := congrFun h i.succ
    simpa using this

lemma consEmb_apply (n : ℕ) (r : Fin 5 → Fin 3) (g : Fin (n + 1) → Fin 5 → Fin 3) :
    consEmb n r g = Fin.cons r g := rfl

lemma W_succ (n : ℕ) (r : Fin 5 → Fin 3) :
    W (n + 1) r = if hrow r then ∑ s : Fin 5 → Fin 3, (if ok r s then W n s else 0) else 0 := by
  have e : ((univ : Finset (Fin (n + 2) → Fin 5 → Fin 3)).filter (fun f => Valid f ∧ f 0 = r)) =
      (((univ : Finset (Fin (n + 1) → Fin 5 → Fin 3)).filter
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

lemma x_le {R : ℕ} (x : Fin R → Fin 5 → ℕ) (h : Cond x) (i : Fin R) (j : Fin 5) : x i j ≤ i.val + j.val := by
  obtain ⟨h0, -, hh, hv⟩ := h
  have row0 : ∀ (k : ℕ) (hk : k < 5) (i : Fin R), i.val = 0 → x i ⟨k, hk⟩ ≤ k := by
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
def YCond {R : ℕ} (y : Fin R → Fin 5 → Fin 3) : Prop :=
  Valid y ∧ ∀ i j, i.val = 0 → j.val = 0 → y i j = 0

instance {R : ℕ} : DecidablePred (@YCond R) := fun y => by unfold YCond; infer_instance

lemma y_le {R : ℕ} (y : Fin R → Fin 5 → Fin 3) (hy : YCond y) (i : Fin R) (j : Fin 5) : (y i j).val ≤ i.val + j.val := by
  obtain ⟨⟨hh, hv⟩, h0⟩ := hy
  have row0 : ∀ (k : ℕ) (hk : k < 5) (i : Fin R), i.val = 0 → (y i ⟨k, hk⟩).val ≤ k := by
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
lemma card_eq (R : ℕ) : {x : Fin R → Fin 5 → ℕ | Cond x}.ncard =
    ((univ : Finset (Fin R → Fin 5 → Fin 3)).filter YCond).card := by
  have himg : {x : Fin R → Fin 5 → ℕ | Cond x} =
      (fun y : Fin R → Fin 5 → Fin 3 => fun i j => i.val + j.val - (y i j).val) ''
        ↑((univ : Finset (Fin R → Fin 5 → Fin 3)).filter YCond) := by
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
  have hinj : Set.InjOn (fun y : Fin R → Fin 5 → Fin 3 => fun i j => i.val + j.val - (y i j).val)
      ↑((univ : Finset (Fin R → Fin 5 → Fin 3)).filter YCond) := by
    intro y hy y' hy' e
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hy hy'
    funext i j
    have h1 := y_le y hy i j
    have h2 := y_le y' hy' i j
    have := congrFun (congrFun e i) j
    simp only at this
    ext; omega
  rw [himg, hinj.ncard_image, Set.ncard_coe_finset]

lemma a_eq (n : ℕ) : a (n + 1) = ∑ r : Fin 5 → Fin 3, if r 0 = 0 then W n r else 0 := by
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

lemma sum_row (f : (Fin 5 → Fin 3) → ℕ) :
    ∑ s : Fin 5 → Fin 3, f s = ∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3, ∑ u : Fin 3, ∑ v : Fin 3, f ![x, y, z, u, v] := by
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Fintype.sum_unique]
  exact congrArg f (by funext j; fin_cases j <;> rfl)

lemma row_eta (r : Fin 5 → Fin 3) : r = ![r 0, r 1, r 2, r 3, r 4] := by
  funext j
  fin_cases j <;> rfl

/-- `hrow` as a Boolean. -/
def hrowB (r : Fin 5 → Fin 3) : Bool :=
  decide (r 1 = r 0 ∨ (r 1).val = (r 0).val + 1) &&
    decide (r 2 = r 1 ∨ (r 2).val = (r 1).val + 1) &&
    decide (r 3 = r 2 ∨ (r 3).val = (r 2).val + 1) &&
    decide (r 4 = r 3 ∨ (r 4).val = (r 3).val + 1)

/-- The entry b below the entry a stays or increases by 1. -/
def okC (a b : Fin 3) : Bool := decide (b = a ∨ b.val = a.val + 1)

/-- `ok` as a Boolean. -/
def okB (r s : Fin 5 → Fin 3) : Bool :=
  okC (r 0) (s 0) &&
    okC (r 1) (s 1) &&
    okC (r 2) (s 2) &&
    okC (r 3) (s 3) &&
    okC (r 4) (s 4)

lemma hrow_iff (r : Fin 5 → Fin 3) : hrow r ↔ hrowB r = true := by
  simp only [hrowB, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  constructor
  · intro h
    exact ⟨h 0 1 rfl, h 1 2 rfl, h 2 3 rfl, h 3 4 rfl⟩
  · intro h j j' hj
    have := j'.isLt
    rcases (by omega : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3) with e | e | e | e
    · obtain rfl : j = 0 := Fin.ext (by show j.val = 0; omega)
      obtain rfl : j' = 1 := Fin.ext (by show j'.val = 1; omega)
      exact h.1
    · obtain rfl : j = 1 := Fin.ext (by show j.val = 1; omega)
      obtain rfl : j' = 2 := Fin.ext (by show j'.val = 2; omega)
      exact h.2.1
    · obtain rfl : j = 2 := Fin.ext (by show j.val = 2; omega)
      obtain rfl : j' = 3 := Fin.ext (by show j'.val = 3; omega)
      exact h.2.2.1
    · obtain rfl : j = 3 := Fin.ext (by show j.val = 3; omega)
      obtain rfl : j' = 4 := Fin.ext (by show j'.val = 4; omega)
      exact h.2.2.2

lemma ok_iff (r s : Fin 5 → Fin 3) : ok r s ↔ okB r s = true := by
  simp only [okB, okC, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3, h 4⟩
  · intro h j
    fin_cases j
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2.1
    · exact h.2.2.2.2

/-- One step of the transfer, the rows below r enumerated entry by entry. -/
def T (g : (Fin 5 → Fin 3) → ℕ) (r : Fin 5 → Fin 3) : ℕ :=
  if hrowB r = true then
    ∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3, ∑ u : Fin 3, ∑ v : Fin 3, (if okB r ![x, y, z, u, v] = true then g ![x, y, z, u, v] else 0)
  else 0

lemma W_succT (n : ℕ) (r : Fin 5 → Fin 3) : W (n + 1) r = T (W n) r := by
  rw [W_succ, sum_row]
  unfold T
  simp only [hrow_iff, ok_iff]

lemma T_congr (g g' : (Fin 5 → Fin 3) → ℕ) (r : Fin 5 → Fin 3) (h : ∀ s, g s = g' s) : T g r = T g' r := by
  unfold T
  simp only [h]

/-- `T` with the sums over the cells of the row below cut as soon as a cell fails `okC`. -/
def Tp (g : (Fin 5 → Fin 3) → ℕ) (r : Fin 5 → Fin 3) : ℕ :=
  if hrowB r = true then
    ∑ x : Fin 3, (if okC (r 0) x = true then (∑ y : Fin 3, (if okC (r 1) y = true then (∑ z : Fin 3, (if okC (r 2) z = true then (∑ u : Fin 3, (if okC (r 3) u = true then (∑ v : Fin 3, (if okC (r 4) v = true then (g ![x, y, z, u, v]) else 0)) else 0)) else 0)) else 0)) else 0)
  else 0

lemma T_eq_Tp (g : (Fin 5 → Fin 3) → ℕ) (r : Fin 5 → Fin 3) : T g r = Tp g r := by
  unfold T Tp
  by_cases hr : hrowB r = true
  · rw [if_pos hr, if_pos hr]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases h0 : okC (r 0) x = true
    · rw [if_pos h0]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      by_cases h1 : okC (r 1) y = true
      · rw [if_pos h1]
        refine Finset.sum_congr rfl (fun z _ => ?_)
        by_cases h2 : okC (r 2) z = true
        · rw [if_pos h2]
          refine Finset.sum_congr rfl (fun u _ => ?_)
          by_cases h3 : okC (r 3) u = true
          · rw [if_pos h3]
            refine Finset.sum_congr rfl (fun v _ => ?_)
            by_cases h4 : okC (r 4) v = true
            · rw [if_pos h4, if_pos (show okB r ![x, y, z, u, v] = true by simp [okB, h0, h1, h2, h3, h4])]
            · rw [if_neg h4, if_neg (show ¬ okB r ![x, y, z, u, v] = true by simp [okB, h4])]
          · rw [if_neg h3]
            simp [okB, h3]
        · rw [if_neg h2]
          simp [okB, h2]
      · rw [if_neg h1]
        simp [okB, h1]
    · rw [if_neg h0]
      simp [okB, h0]
  · rw [if_neg hr, if_neg hr]

/-- W(0) as a function. -/
def W0f (r : Fin 5 → Fin 3) : ℕ := if hrowB r = true then 1 else 0

lemma W_zero' (r : Fin 5 → Fin 3) : W 0 r = W0f r := by
  rw [W_zero]
  unfold W0f
  simp only [hrow_iff]

/-- W(1, r), nested by the entries of r. -/
def L1 : List (List (List (List (List ℕ)))) :=
  [[[[[6, 9, 0], [0, 11, 7], [0, 0, 0]], [[0, 0, 0], [0, 11, 8], [0, 0, 5]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 9, 7], [0, 0, 5]], [[0, 0, 0], [0, 0, 0], [0, 0, 3]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]]], [[[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 6, 5], [0, 0, 4]], [[0, 0, 0], [0, 0, 0], [0, 0, 3]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 2]]]], [[[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 1]]]]]

/-- W(1) as a table. -/
def tab1 (r : Fin 5 → Fin 3) : ℕ := ((((L1.getD (r 0).val []).getD (r 1).val []).getD (r 2).val []).getD (r 3).val []).getD (r 4).val 0

/-- W(2, r), nested by the entries of r. -/
def L2 : List (List (List (List (List ℕ)))) :=
  [[[[[52, 73, 0], [0, 78, 41], [0, 0, 0]], [[0, 0, 0], [0, 66, 40], [0, 0, 20]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 44, 29], [0, 0, 17]], [[0, 0, 0], [0, 0, 0], [0, 0, 8]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]]], [[[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 21, 15], [0, 0, 10]], [[0, 0, 0], [0, 0, 0], [0, 0, 6]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 3]]]], [[[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 1]]]]]

/-- W(2) as a table. -/
def tab2 (r : Fin 5 → Fin 3) : ℕ := ((((L2.getD (r 0).val []).getD (r 1).val []).getD (r 2).val []).getD (r 3).val []).getD (r 4).val 0

/-- W(3, r), nested by the entries of r. -/
def L3 : List (List (List (List (List ℕ)))) :=
  [[[[[334, 407, 0], [0, 381, 172], [0, 0, 0]], [[0, 0, 0], [0, 276, 145], [0, 0, 61]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 153, 88], [0, 0, 44]], [[0, 0, 0], [0, 0, 0], [0, 0, 17]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]]], [[[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 56, 35], [0, 0, 20]], [[0, 0, 0], [0, 0, 0], [0, 0, 10]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 4]]]], [[[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 1]]]]]

/-- W(3) as a table. -/
def tab3 (r : Fin 5 → Fin 3) : ℕ := ((((L3.getD (r 0).val []).getD (r 1).val []).getD (r 2).val []).getD (r 3).val []).getD (r 4).val 0

/-- W(4, r), nested by the entries of r. -/
def L4 : List (List (List (List (List ℕ)))) :=
  [[[[[1607, 1713, 0], [0, 1431, 565], [0, 0, 0]], [[0, 0, 0], [0, 905, 420], [0, 0, 152]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 427, 218], [0, 0, 95]], [[0, 0, 0], [0, 0, 0], [0, 0, 31]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]]], [[[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 126, 70], [0, 0, 35]], [[0, 0, 0], [0, 0, 0], [0, 0, 15]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 5]]]], [[[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 1]]]]]

/-- W(4) as a table. -/
def tab4 (r : Fin 5 → Fin 3) : ℕ := ((((L4.getD (r 0).val []).getD (r 1).val []).getD (r 2).val []).getD (r 3).val []).getD (r 4).val 0

/-- W(5, r), nested by the entries of r. -/
def L5 : List (List (List (List (List ℕ)))) :=
  [[[[[6209, 5875, 0], [0, 4444, 1555], [0, 0, 0]], [[0, 0, 0], [0, 2494, 1036], [0, 0, 328]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 1022, 469], [0, 0, 181]], [[0, 0, 0], [0, 0, 0], [0, 0, 51]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]]], [[[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 252, 126], [0, 0, 56]], [[0, 0, 0], [0, 0, 0], [0, 0, 21]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 6]]]], [[[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 1]]]]]

/-- W(5) as a table. -/
def tab5 (r : Fin 5 → Fin 3) : ℕ := ((((L5.getD (r 0).val []).getD (r 1).val []).getD (r 2).val []).getD (r 3).val []).getD (r 4).val 0

/-- W(6, r), nested by the entries of r. -/
def L6 : List (List (List (List (List ℕ)))) :=
  [[[[[20296, 17273, 0], [0, 11963, 3751], [0, 0, 0]], [[0, 0, 0], [0, 6036, 2268], [0, 0, 637]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 2184, 910], [0, 0, 315]], [[0, 0, 0], [0, 0, 0], [0, 0, 78]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]]], [[[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 462, 210], [0, 0, 84]], [[0, 0, 0], [0, 0, 0], [0, 0, 28]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 7]]]], [[[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 1]]]]]

/-- W(6) as a table. -/
def tab6 (r : Fin 5 → Fin 3) : ℕ := ((((L6.getD (r 0).val []).getD (r 1).val []).getD (r 2).val []).getD (r 3).val []).getD (r 4).val 0

/-- W(7, r), nested by the entries of r. -/
def L7 : List (List (List (List (List ℕ)))) :=
  [[[[[58214, 45057, 0], [0, 28820, 8175], [0, 0, 0]], [[0, 0, 0], [0, 13212, 4530], [0, 0, 1142]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 4278, 1632], [0, 0, 512]], [[0, 0, 0], [0, 0, 0], [0, 0, 113]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]]], [[[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 792, 330], [0, 0, 120]], [[0, 0, 0], [0, 0, 0], [0, 0, 36]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 8]]]], [[[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 1]]]]]

/-- W(7) as a table. -/
def tab7 (r : Fin 5 → Fin 3) : ℕ := ((((L7.getD (r 0).val []).getD (r 1).val []).getD (r 2).val []).getD (r 3).val []).getD (r 4).val 0

/-- W(8, r), nested by the entries of r. -/
def L8 : List (List (List (List (List ℕ)))) :=
  [[[[[150373, 106826, 0], [0, 63543, 16441], [0, 0, 0]], [[0, 0, 0], [0, 26697, 8415], [0, 0, 1923]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 7821, 2751], [0, 0, 789]], [[0, 0, 0], [0, 0, 0], [0, 0, 157]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]]], [[[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 1287, 495], [0, 0, 165]], [[0, 0, 0], [0, 0, 0], [0, 0, 45]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 9]]]], [[[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 1]]]]]

/-- W(8) as a table. -/
def tab8 (r : Fin 5 → Fin 3) : ℕ := ((((L8.getD (r 0).val []).getD (r 1).val []).getD (r 2).val []).getD (r 3).val []).getD (r 4).val 0

/-- W(9, r), nested by the entries of r. -/
def L9 : List (List (List (List (List ℕ)))) :=
  [[[[[356547, 234276, 0], [0, 130327, 30979], [0, 0, 0]], [[0, 0, 0], [0, 50545, 14740], [0, 0, 3079]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 13519, 4411], [0, 0, 1165]], [[0, 0, 0], [0, 0, 0], [0, 0, 211]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]]], [[[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 2002, 715], [0, 0, 220]], [[0, 0, 0], [0, 0, 0], [0, 0, 55]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 10]]]], [[[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 1]]]]]

/-- W(9) as a table. -/
def tab9 (r : Fin 5 → Fin 3) : ℕ := ((((L9.getD (r 0).val []).getD (r 1).val []).getD (r 2).val []).getD (r 3).val []).getD (r 4).val 0

/-- W(10, r), nested by the entries of r. -/
def L10 : List (List (List (List (List ℕ)))) :=
  [[[[[787216, 481514, 0], [0, 251702, 55309], [0, 0, 0]], [[0, 0, 0], [0, 90662, 24596], [0, 0, 4730]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 22308, 6787], [0, 0, 1661]], [[0, 0, 0], [0, 0, 0], [0, 0, 276]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]]], [[[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 3003, 1001], [0, 0, 286]], [[0, 0, 0], [0, 0, 0], [0, 0, 66]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 11]]]], [[[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 1]]]]]

/-- W(10) as a table. -/
def tab10 (r : Fin 5 → Fin 3) : ℕ := ((((L10.getD (r 0).val []).getD (r 1).val []).getD (r 2).val []).getD (r 3).val []).getD (r 4).val 0

set_option maxHeartbeats 4000000 in
lemma checks_all :
    (∀ y1 y2 y3 y4 y5 : Fin 3,
    Tp W0f ![y1, y2, y3, y4, y5] = tab1 ![y1, y2, y3, y4, y5]) ∧
    (∀ y1 y2 y3 y4 y5 : Fin 3,
    Tp tab1 ![y1, y2, y3, y4, y5] = tab2 ![y1, y2, y3, y4, y5]) ∧
    (∀ y1 y2 y3 y4 y5 : Fin 3,
    Tp tab2 ![y1, y2, y3, y4, y5] = tab3 ![y1, y2, y3, y4, y5]) ∧
    (∀ y1 y2 y3 y4 y5 : Fin 3,
    Tp tab3 ![y1, y2, y3, y4, y5] = tab4 ![y1, y2, y3, y4, y5]) ∧
    (∀ y1 y2 y3 y4 y5 : Fin 3,
    Tp tab4 ![y1, y2, y3, y4, y5] = tab5 ![y1, y2, y3, y4, y5]) ∧
    (∀ y1 y2 y3 y4 y5 : Fin 3,
    Tp tab5 ![y1, y2, y3, y4, y5] = tab6 ![y1, y2, y3, y4, y5]) ∧
    (∀ y1 y2 y3 y4 y5 : Fin 3,
    Tp tab6 ![y1, y2, y3, y4, y5] = tab7 ![y1, y2, y3, y4, y5]) ∧
    (∀ y1 y2 y3 y4 y5 : Fin 3,
    Tp tab7 ![y1, y2, y3, y4, y5] = tab8 ![y1, y2, y3, y4, y5]) ∧
    (∀ y1 y2 y3 y4 y5 : Fin 3,
    Tp tab8 ![y1, y2, y3, y4, y5] = tab9 ![y1, y2, y3, y4, y5]) ∧
    (∀ y1 y2 y3 y4 y5 : Fin 3,
    Tp tab9 ![y1, y2, y3, y4, y5] = tab10 ![y1, y2, y3, y4, y5]) ∧
    (∀ y1 y2 y3 y4 y5 : Fin 3,
    Tp tab10 ![y1, y2, y3, y4, y5] + 55 * tab9 ![y1, y2, y3, y4, y5] + 330 * tab7 ![y1, y2, y3, y4, y5] + 462 * tab5 ![y1, y2, y3, y4, y5] + 165 * tab3 ![y1, y2, y3, y4, y5] + 11 * tab1 ![y1, y2, y3, y4, y5] =
      11 * tab10 ![y1, y2, y3, y4, y5] + 165 * tab8 ![y1, y2, y3, y4, y5] + 462 * tab6 ![y1, y2, y3, y4, y5] + 330 * tab4 ![y1, y2, y3, y4, y5] + 55 * tab2 ![y1, y2, y3, y4, y5] + W0f ![y1, y2, y3, y4, y5]) ∧
    (∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3, ∑ u : Fin 3, ∑ v : Fin 3, (if ![x, y, z, u, v] 0 = 0 then W0f ![x, y, z, u, v] else 0) = 11) ∧
    (∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3, ∑ u : Fin 3, ∑ v : Fin 3, (if ![x, y, z, u, v] 0 = 0 then tab1 ![x, y, z, u, v] else 0) = 81) ∧
    (∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3, ∑ u : Fin 3, ∑ v : Fin 3, (if ![x, y, z, u, v] 0 = 0 then tab2 ![x, y, z, u, v] else 0) = 468) ∧
    (∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3, ∑ u : Fin 3, ∑ v : Fin 3, (if ![x, y, z, u, v] 0 = 0 then tab3 ![x, y, z, u, v] else 0) = 2078) ∧
    (∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3, ∑ u : Fin 3, ∑ v : Fin 3, (if ![x, y, z, u, v] 0 = 0 then tab4 ![x, y, z, u, v] else 0) = 7564) ∧
    (∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3, ∑ u : Fin 3, ∑ v : Fin 3, (if ![x, y, z, u, v] 0 = 0 then tab5 ![x, y, z, u, v] else 0) = 23664) ∧
    (∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3, ∑ u : Fin 3, ∑ v : Fin 3, (if ![x, y, z, u, v] 0 = 0 then tab6 ![x, y, z, u, v] else 0) = 65711) ∧
    (∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3, ∑ u : Fin 3, ∑ v : Fin 3, (if ![x, y, z, u, v] 0 = 0 then tab7 ![x, y, z, u, v] else 0) = 165685) ∧
    (∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3, ∑ u : Fin 3, ∑ v : Fin 3, (if ![x, y, z, u, v] 0 = 0 then tab8 ![x, y, z, u, v] else 0) = 385736) ∧
    (∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3, ∑ u : Fin 3, ∑ v : Fin 3, (if ![x, y, z, u, v] 0 = 0 then tab9 ![x, y, z, u, v] else 0) = 839799) ∧
    (∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3, ∑ u : Fin 3, ∑ v : Fin 3, (if ![x, y, z, u, v] 0 = 0 then tab10 ![x, y, z, u, v] else 0) = 1726761) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · decide +kernel
  · decide +kernel

lemma check1 : ∀ y1 y2 y3 y4 y5 : Fin 3,
    Tp W0f ![y1, y2, y3, y4, y5] = tab1 ![y1, y2, y3, y4, y5] := checks_all.1

lemma check2 : ∀ y1 y2 y3 y4 y5 : Fin 3,
    Tp tab1 ![y1, y2, y3, y4, y5] = tab2 ![y1, y2, y3, y4, y5] := checks_all.2.1

lemma check3 : ∀ y1 y2 y3 y4 y5 : Fin 3,
    Tp tab2 ![y1, y2, y3, y4, y5] = tab3 ![y1, y2, y3, y4, y5] := checks_all.2.2.1

lemma check4 : ∀ y1 y2 y3 y4 y5 : Fin 3,
    Tp tab3 ![y1, y2, y3, y4, y5] = tab4 ![y1, y2, y3, y4, y5] := checks_all.2.2.2.1

lemma check5 : ∀ y1 y2 y3 y4 y5 : Fin 3,
    Tp tab4 ![y1, y2, y3, y4, y5] = tab5 ![y1, y2, y3, y4, y5] := checks_all.2.2.2.2.1

lemma check6 : ∀ y1 y2 y3 y4 y5 : Fin 3,
    Tp tab5 ![y1, y2, y3, y4, y5] = tab6 ![y1, y2, y3, y4, y5] := checks_all.2.2.2.2.2.1

lemma check7 : ∀ y1 y2 y3 y4 y5 : Fin 3,
    Tp tab6 ![y1, y2, y3, y4, y5] = tab7 ![y1, y2, y3, y4, y5] := checks_all.2.2.2.2.2.2.1

lemma check8 : ∀ y1 y2 y3 y4 y5 : Fin 3,
    Tp tab7 ![y1, y2, y3, y4, y5] = tab8 ![y1, y2, y3, y4, y5] := checks_all.2.2.2.2.2.2.2.1

lemma check9 : ∀ y1 y2 y3 y4 y5 : Fin 3,
    Tp tab8 ![y1, y2, y3, y4, y5] = tab9 ![y1, y2, y3, y4, y5] := checks_all.2.2.2.2.2.2.2.2.1

lemma check10 : ∀ y1 y2 y3 y4 y5 : Fin 3,
    Tp tab9 ![y1, y2, y3, y4, y5] = tab10 ![y1, y2, y3, y4, y5] := checks_all.2.2.2.2.2.2.2.2.2.1

lemma check_rel : ∀ y1 y2 y3 y4 y5 : Fin 3,
    Tp tab10 ![y1, y2, y3, y4, y5] + 55 * tab9 ![y1, y2, y3, y4, y5] + 330 * tab7 ![y1, y2, y3, y4, y5] + 462 * tab5 ![y1, y2, y3, y4, y5] + 165 * tab3 ![y1, y2, y3, y4, y5] + 11 * tab1 ![y1, y2, y3, y4, y5] =
      11 * tab10 ![y1, y2, y3, y4, y5] + 165 * tab8 ![y1, y2, y3, y4, y5] + 462 * tab6 ![y1, y2, y3, y4, y5] + 330 * tab4 ![y1, y2, y3, y4, y5] + 55 * tab2 ![y1, y2, y3, y4, y5] + W0f ![y1, y2, y3, y4, y5] := checks_all.2.2.2.2.2.2.2.2.2.2.1

lemma sum1 : ∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3, ∑ u : Fin 3, ∑ v : Fin 3, (if ![x, y, z, u, v] 0 = 0 then W0f ![x, y, z, u, v] else 0) = 11 := checks_all.2.2.2.2.2.2.2.2.2.2.2.1

lemma sum2 : ∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3, ∑ u : Fin 3, ∑ v : Fin 3, (if ![x, y, z, u, v] 0 = 0 then tab1 ![x, y, z, u, v] else 0) = 81 := checks_all.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma sum3 : ∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3, ∑ u : Fin 3, ∑ v : Fin 3, (if ![x, y, z, u, v] 0 = 0 then tab2 ![x, y, z, u, v] else 0) = 468 := checks_all.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma sum4 : ∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3, ∑ u : Fin 3, ∑ v : Fin 3, (if ![x, y, z, u, v] 0 = 0 then tab3 ![x, y, z, u, v] else 0) = 2078 := checks_all.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma sum5 : ∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3, ∑ u : Fin 3, ∑ v : Fin 3, (if ![x, y, z, u, v] 0 = 0 then tab4 ![x, y, z, u, v] else 0) = 7564 := checks_all.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma sum6 : ∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3, ∑ u : Fin 3, ∑ v : Fin 3, (if ![x, y, z, u, v] 0 = 0 then tab5 ![x, y, z, u, v] else 0) = 23664 := checks_all.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma sum7 : ∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3, ∑ u : Fin 3, ∑ v : Fin 3, (if ![x, y, z, u, v] 0 = 0 then tab6 ![x, y, z, u, v] else 0) = 65711 := checks_all.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma sum8 : ∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3, ∑ u : Fin 3, ∑ v : Fin 3, (if ![x, y, z, u, v] 0 = 0 then tab7 ![x, y, z, u, v] else 0) = 165685 := checks_all.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma sum9 : ∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3, ∑ u : Fin 3, ∑ v : Fin 3, (if ![x, y, z, u, v] 0 = 0 then tab8 ![x, y, z, u, v] else 0) = 385736 := checks_all.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma sum10 : ∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3, ∑ u : Fin 3, ∑ v : Fin 3, (if ![x, y, z, u, v] 0 = 0 then tab9 ![x, y, z, u, v] else 0) = 839799 := checks_all.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma sum11 : ∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3, ∑ u : Fin 3, ∑ v : Fin 3, (if ![x, y, z, u, v] 0 = 0 then tab10 ![x, y, z, u, v] else 0) = 1726761 := checks_all.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

lemma W_1 (r : Fin 5 → Fin 3) : W 1 r = tab1 r := by
  rw [W_succT, T_congr _ W0f r W_zero', T_eq_Tp, row_eta r]
  exact check1 (r 0) (r 1) (r 2) (r 3) (r 4)

lemma W_2 (r : Fin 5 → Fin 3) : W 2 r = tab2 r := by
  rw [show W 2 r = W (1 + 1) r from rfl, W_succT, T_congr _ tab1 r W_1, T_eq_Tp,
    row_eta r]
  exact check2 (r 0) (r 1) (r 2) (r 3) (r 4)

lemma W_3 (r : Fin 5 → Fin 3) : W 3 r = tab3 r := by
  rw [show W 3 r = W (2 + 1) r from rfl, W_succT, T_congr _ tab2 r W_2, T_eq_Tp,
    row_eta r]
  exact check3 (r 0) (r 1) (r 2) (r 3) (r 4)

lemma W_4 (r : Fin 5 → Fin 3) : W 4 r = tab4 r := by
  rw [show W 4 r = W (3 + 1) r from rfl, W_succT, T_congr _ tab3 r W_3, T_eq_Tp,
    row_eta r]
  exact check4 (r 0) (r 1) (r 2) (r 3) (r 4)

lemma W_5 (r : Fin 5 → Fin 3) : W 5 r = tab5 r := by
  rw [show W 5 r = W (4 + 1) r from rfl, W_succT, T_congr _ tab4 r W_4, T_eq_Tp,
    row_eta r]
  exact check5 (r 0) (r 1) (r 2) (r 3) (r 4)

lemma W_6 (r : Fin 5 → Fin 3) : W 6 r = tab6 r := by
  rw [show W 6 r = W (5 + 1) r from rfl, W_succT, T_congr _ tab5 r W_5, T_eq_Tp,
    row_eta r]
  exact check6 (r 0) (r 1) (r 2) (r 3) (r 4)

lemma W_7 (r : Fin 5 → Fin 3) : W 7 r = tab7 r := by
  rw [show W 7 r = W (6 + 1) r from rfl, W_succT, T_congr _ tab6 r W_6, T_eq_Tp,
    row_eta r]
  exact check7 (r 0) (r 1) (r 2) (r 3) (r 4)

lemma W_8 (r : Fin 5 → Fin 3) : W 8 r = tab8 r := by
  rw [show W 8 r = W (7 + 1) r from rfl, W_succT, T_congr _ tab7 r W_7, T_eq_Tp,
    row_eta r]
  exact check8 (r 0) (r 1) (r 2) (r 3) (r 4)

lemma W_9 (r : Fin 5 → Fin 3) : W 9 r = tab9 r := by
  rw [show W 9 r = W (8 + 1) r from rfl, W_succT, T_congr _ tab8 r W_8, T_eq_Tp,
    row_eta r]
  exact check9 (r 0) (r 1) (r 2) (r 3) (r 4)

lemma W_10 (r : Fin 5 → Fin 3) : W 10 r = tab10 r := by
  rw [show W 10 r = W (9 + 1) r from rfl, W_succT, T_congr _ tab9 r W_9, T_eq_Tp,
    row_eta r]
  exact check10 (r 0) (r 1) (r 2) (r 3) (r 4)

lemma W_rec (n : ℕ) : ∀ r : Fin 5 → Fin 3, W (n + 11) r + 55 * W (n + 9) r + 330 * W (n + 7) r + 462 * W (n + 5) r + 165 * W (n + 3) r + 11 * W (n + 1) r = 11 * W (n + 10) r + 165 * W (n + 8) r + 462 * W (n + 6) r + 330 * W (n + 4) r + 55 * W (n + 2) r + W n r := by
  induction n with
  | zero =>
    intro r
    rw [show W (0 + 11) r = W (10 + 1) r from rfl, W_succT 10 r,
      T_congr _ tab10 r W_10,
      W_zero' r,
      show W (0 + 1) r = W 1 r from rfl, W_1 r,
      show W (0 + 2) r = W 2 r from rfl, W_2 r,
      show W (0 + 3) r = W 3 r from rfl, W_3 r,
      show W (0 + 4) r = W 4 r from rfl, W_4 r,
      show W (0 + 5) r = W 5 r from rfl, W_5 r,
      show W (0 + 6) r = W 6 r from rfl, W_6 r,
      show W (0 + 7) r = W 7 r from rfl, W_7 r,
      show W (0 + 8) r = W 8 r from rfl, W_8 r,
      show W (0 + 9) r = W 9 r from rfl, W_9 r,
      show W (0 + 10) r = W 10 r from rfl, W_10 r,
      T_eq_Tp,
      row_eta r]
    exact check_rel (r 0) (r 1) (r 2) (r 3) (r 4)
  | succ n ih =>
    intro r
    rw [W_succT (n + 11) r, W_succT (n + 10) r, W_succT (n + 9) r, W_succT (n + 8) r, W_succT (n + 7) r, W_succT (n + 6) r, W_succT (n + 5) r, W_succT (n + 4) r, W_succT (n + 3) r, W_succT (n + 2) r, W_succT (n + 1) r, W_succT n r]
    unfold T
    by_cases h : hrowB r = true
    · rw [if_pos h, if_pos h, if_pos h, if_pos h, if_pos h, if_pos h, if_pos h, if_pos h, if_pos h, if_pos h, if_pos h, if_pos h]
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      split_ifs
      · exact ih _
      · simp
    · rw [if_neg h, if_neg h, if_neg h, if_neg h, if_neg h, if_neg h, if_neg h, if_neg h, if_neg h, if_neg h, if_neg h, if_neg h] <;> simp

lemma a_rec (n : ℕ) : a (n + 12) + 55 * a (n + 10) + 330 * a (n + 8) + 462 * a (n + 6) + 165 * a (n + 4) + 11 * a (n + 2) = 11 * a (n + 11) + 165 * a (n + 9) + 462 * a (n + 7) + 330 * a (n + 5) + 55 * a (n + 3) + a (n + 1) := by
  rw [a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  split_ifs
  · exact W_rec n r
  · simp

lemma a_1 : a 1 = 11 := by
  rw [show a 1 = a (0 + 1) from rfl, a_eq, sum_row]
  have h : ∀ r : Fin 5 → Fin 3, (if r 0 = 0 then W 0 r else 0) = (if r 0 = 0 then W0f r else 0) := fun r => by split_ifs <;> simp only [W_zero']
  simp only [h]
  exact sum1

lemma a_2 : a 2 = 81 := by
  rw [show a 2 = a (1 + 1) from rfl, a_eq, sum_row]
  have h : ∀ r : Fin 5 → Fin 3, (if r 0 = 0 then W 1 r else 0) = (if r 0 = 0 then tab1 r else 0) := fun r => by split_ifs <;> simp only [W_1]
  simp only [h]
  exact sum2

lemma a_3 : a 3 = 468 := by
  rw [show a 3 = a (2 + 1) from rfl, a_eq, sum_row]
  have h : ∀ r : Fin 5 → Fin 3, (if r 0 = 0 then W 2 r else 0) = (if r 0 = 0 then tab2 r else 0) := fun r => by split_ifs <;> simp only [W_2]
  simp only [h]
  exact sum3

lemma a_4 : a 4 = 2078 := by
  rw [show a 4 = a (3 + 1) from rfl, a_eq, sum_row]
  have h : ∀ r : Fin 5 → Fin 3, (if r 0 = 0 then W 3 r else 0) = (if r 0 = 0 then tab3 r else 0) := fun r => by split_ifs <;> simp only [W_3]
  simp only [h]
  exact sum4

lemma a_5 : a 5 = 7564 := by
  rw [show a 5 = a (4 + 1) from rfl, a_eq, sum_row]
  have h : ∀ r : Fin 5 → Fin 3, (if r 0 = 0 then W 4 r else 0) = (if r 0 = 0 then tab4 r else 0) := fun r => by split_ifs <;> simp only [W_4]
  simp only [h]
  exact sum5

lemma a_6 : a 6 = 23664 := by
  rw [show a 6 = a (5 + 1) from rfl, a_eq, sum_row]
  have h : ∀ r : Fin 5 → Fin 3, (if r 0 = 0 then W 5 r else 0) = (if r 0 = 0 then tab5 r else 0) := fun r => by split_ifs <;> simp only [W_5]
  simp only [h]
  exact sum6

lemma a_7 : a 7 = 65711 := by
  rw [show a 7 = a (6 + 1) from rfl, a_eq, sum_row]
  have h : ∀ r : Fin 5 → Fin 3, (if r 0 = 0 then W 6 r else 0) = (if r 0 = 0 then tab6 r else 0) := fun r => by split_ifs <;> simp only [W_6]
  simp only [h]
  exact sum7

lemma a_8 : a 8 = 165685 := by
  rw [show a 8 = a (7 + 1) from rfl, a_eq, sum_row]
  have h : ∀ r : Fin 5 → Fin 3, (if r 0 = 0 then W 7 r else 0) = (if r 0 = 0 then tab7 r else 0) := fun r => by split_ifs <;> simp only [W_7]
  simp only [h]
  exact sum8

lemma a_9 : a 9 = 385736 := by
  rw [show a 9 = a (8 + 1) from rfl, a_eq, sum_row]
  have h : ∀ r : Fin 5 → Fin 3, (if r 0 = 0 then W 8 r else 0) = (if r 0 = 0 then tab8 r else 0) := fun r => by split_ifs <;> simp only [W_8]
  simp only [h]
  exact sum9

lemma a_10 : a 10 = 839799 := by
  rw [show a 10 = a (9 + 1) from rfl, a_eq, sum_row]
  have h : ∀ r : Fin 5 → Fin 3, (if r 0 = 0 then W 9 r else 0) = (if r 0 = 0 then tab9 r else 0) := fun r => by split_ifs <;> simp only [W_9]
  simp only [h]
  exact sum10

lemma a_11 : a 11 = 1726761 := by
  rw [show a 11 = a (10 + 1) from rfl, a_eq, sum_row]
  have h : ∀ r : Fin 5 → Fin 3, (if r 0 = 0 then W 10 r else 0) = (if r 0 = 0 then tab10 r else 0) := fun r => by split_ifs <;> simp only [W_10]
  simp only [h]
  exact sum11

/-- Barker's g.f. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 11 =
      X * (11 - 40 * X + 182 * X ^ 2 - 430 * X ^ 3 + 711 * X ^ 4 - 822 * X ^ 5 + 657 * X ^ 6 - 360 * X ^ 7 + 131 * X ^ 8 - 29 * X ^ 9 + 3 * X ^ 10) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - X) ^ 11 = A - A * X ^ 1 * C 11 + A * X ^ 2 * C 55 - A * X ^ 3 * C 165 + A * X ^ 4 * C 330 - A * X ^ 5 * C 462 + A * X ^ 6 * C 462 - A * X ^ 7 * C 330 + A * X ^ 8 * C 165 - A * X ^ 9 * C 55 + A * X ^ 10 * C 11 - A * X ^ 11 * C 1 := by
    rw [show (C (1 : ℚ) : ℚ⟦X⟧) = 1 from map_one C,
      show (C (11 : ℚ) : ℚ⟦X⟧) = 11 from map_ofNat C 11,
      show (C (55 : ℚ) : ℚ⟦X⟧) = 55 from map_ofNat C 55,
      show (C (165 : ℚ) : ℚ⟦X⟧) = 165 from map_ofNat C 165,
      show (C (330 : ℚ) : ℚ⟦X⟧) = 330 from map_ofNat C 330,
      show (C (462 : ℚ) : ℚ⟦X⟧) = 462 from map_ofNat C 462]
    ring
  have e2 : (X * (11 - 40 * X + 182 * X ^ 2 - 430 * X ^ 3 + 711 * X ^ 4 - 822 * X ^ 5 + 657 * X ^ 6 - 360 * X ^ 7 + 131 * X ^ 8 - 29 * X ^ 9 + 3 * X ^ 10) : ℚ⟦X⟧) = X ^ 1 * C 11 - X ^ 2 * C 40 + X ^ 3 * C 182 - X ^ 4 * C 430 + X ^ 5 * C 711 - X ^ 6 * C 822 + X ^ 7 * C 657 - X ^ 8 * C 360 + X ^ 9 * C 131 - X ^ 10 * C 29 + X ^ 11 * C 3 := by
    rw [show (C (3 : ℚ) : ℚ⟦X⟧) = 3 from map_ofNat C 3,
      show (C (11 : ℚ) : ℚ⟦X⟧) = 11 from map_ofNat C 11,
      show (C (29 : ℚ) : ℚ⟦X⟧) = 29 from map_ofNat C 29,
      show (C (40 : ℚ) : ℚ⟦X⟧) = 40 from map_ofNat C 40,
      show (C (131 : ℚ) : ℚ⟦X⟧) = 131 from map_ofNat C 131,
      show (C (182 : ℚ) : ℚ⟦X⟧) = 182 from map_ofNat C 182,
      show (C (360 : ℚ) : ℚ⟦X⟧) = 360 from map_ofNat C 360,
      show (C (430 : ℚ) : ℚ⟦X⟧) = 430 from map_ofNat C 430,
      show (C (657 : ℚ) : ℚ⟦X⟧) = 657 from map_ofNat C 657,
      show (C (711 : ℚ) : ℚ⟦X⟧) = 711 from map_ofNat C 711,
      show (C (822 : ℚ) : ℚ⟦X⟧) = 822 from map_ofNat C 822]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk]
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n
  · simp
  · simp [a_1] <;> norm_num
  · simp [a_1, a_2] <;> norm_num
  · simp [a_1, a_2, a_3] <;> norm_num
  · simp [a_1, a_2, a_3, a_4] <;> norm_num
  · simp [a_1, a_2, a_3, a_4, a_5] <;> norm_num
  · simp [a_1, a_2, a_3, a_4, a_5, a_6] <;> norm_num
  · simp [a_1, a_2, a_3, a_4, a_5, a_6, a_7] <;> norm_num
  · simp [a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8] <;> norm_num
  · simp [a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, a_9] <;> norm_num
  · simp [a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, a_9, a_10] <;> norm_num
  · simp [a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, a_9, a_10, a_11] <;> norm_num
  · have h := a_rec n
    
    have hq : (a (n + 12) : ℚ) + 55 * (a (n + 10) : ℚ) + 330 * (a (n + 8) : ℚ) + 462 * (a (n + 6) : ℚ) + 165 * (a (n + 4) : ℚ) + 11 * (a (n + 2) : ℚ) = 11 * (a (n + 11) : ℚ) + 165 * (a (n + 9) : ℚ) + 462 * (a (n + 7) : ℚ) + 330 * (a (n + 5) : ℚ) + 55 * (a (n + 3) : ℚ) + (a (n + 1) : ℚ) := by exact_mod_cast h
    simp only [show ¬ (n + 12 = 0) by omega,
      if_false,
      if_true,
      show 1 ≤ n + 12 by omega,
      show n + 12 - 1 = n + 11 by omega,
      show ¬ (n + 11 = 0) by omega,
      show 2 ≤ n + 12 by omega,
      show n + 12 - 2 = n + 10 by omega,
      show ¬ (n + 10 = 0) by omega,
      show 3 ≤ n + 12 by omega,
      show n + 12 - 3 = n + 9 by omega,
      show ¬ (n + 9 = 0) by omega,
      show 4 ≤ n + 12 by omega,
      show n + 12 - 4 = n + 8 by omega,
      show ¬ (n + 8 = 0) by omega,
      show 5 ≤ n + 12 by omega,
      show n + 12 - 5 = n + 7 by omega,
      show ¬ (n + 7 = 0) by omega,
      show 6 ≤ n + 12 by omega,
      show n + 12 - 6 = n + 6 by omega,
      show ¬ (n + 6 = 0) by omega,
      show 7 ≤ n + 12 by omega,
      show n + 12 - 7 = n + 5 by omega,
      show ¬ (n + 5 = 0) by omega,
      show 8 ≤ n + 12 by omega,
      show n + 12 - 8 = n + 4 by omega,
      show ¬ (n + 4 = 0) by omega,
      show 9 ≤ n + 12 by omega,
      show n + 12 - 9 = n + 3 by omega,
      show ¬ (n + 3 = 0) by omega,
      show 10 ≤ n + 12 by omega,
      show n + 12 - 10 = n + 2 by omega,
      show ¬ (n + 2 = 0) by omega,
      show 11 ≤ n + 12 by omega,
      show n + 12 - 11 = n + 1 by omega,
      show ¬ (n + 1 = 0) by omega,
      show ¬ (n + 12 = 1) by omega,
      show ¬ (n + 12 = 2) by omega,
      show ¬ (n + 12 = 3) by omega,
      show ¬ (n + 12 = 4) by omega,
      show ¬ (n + 12 = 5) by omega,
      show ¬ (n + 12 = 6) by omega,
      show ¬ (n + 12 = 7) by omega,
      show ¬ (n + 12 = 8) by omega,
      show ¬ (n + 12 = 9) by omega,
      show ¬ (n + 12 = 10) by omega,
      show ¬ (n + 12 = 11) by omega]
    linear_combination hq

/-- Barker's recurrence. -/
theorem rec_int : ∀ n : ℕ, 11 < n → (a n : ℤ) =
      11 * a (n - 1) - 55 * a (n - 2) + 165 * a (n - 3) - 330 * a (n - 4) + 462 * a (n - 5) - 462 * a (n - 6) + 330 * a (n - 7) - 165 * a (n - 8) + 55 * a (n - 9) - 11 * a (n - 10) + a (n - 11) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
  have h := a_rec m
  rw [show m + 12 - 1 = m + 11 by omega, show m + 12 - 2 = m + 10 by omega, show m + 12 - 3 = m + 9 by omega, show m + 12 - 4 = m + 8 by omega, show m + 12 - 5 = m + 7 by omega, show m + 12 - 6 = m + 6 by omega, show m + 12 - 7 = m + 5 by omega, show m + 12 - 8 = m + 4 by omega, show m + 12 - 9 = m + 3 by omega, show m + 12 - 10 = m + 2 by omega, show m + 12 - 11 = m + 1 by omega]
  have hz : ((a (m + 12) + 55 * a (m + 10) + 330 * a (m + 8) + 462 * a (m + 6) + 165 * a (m + 4) + 11 * a (m + 2) : ℕ) : ℤ) = ((11 * a (m + 11) + 165 * a (m + 9) + 462 * a (m + 7) + 330 * a (m + 5) + 55 * a (m + 3) + a (m + 1) : ℕ) : ℤ) := by rw [h]
  push_cast at hz
  linarith

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 11 =
      X * (11 - 40 * X + 182 * X ^ 2 - 430 * X ^ 3 + 711 * X ^ 4 - 822 * X ^ 5 + 657 * X ^ 6 - 360 * X ^ 7 + 131 * X ^ 8 - 29 * X ^ 9 + 3 * X ^ 10) ∧
    ∀ n : ℕ, 11 < n → (a n : ℤ) =
      11 * a (n - 1) - 55 * a (n - 2) + 165 * a (n - 3) - 330 * a (n - 4) + 462 * a (n - 5) - 462 * a (n - 6) + 330 * a (n - 7) - 165 * a (n - 8) + 55 * a (n - 9) - 11 * a (n - 10) + a (n - 11) :=
  ⟨gf, rec_int⟩

/-- Controls: the entry's terms a(1..10). -/
theorem controls : a 1 = 11 ∧ a 2 = 81 ∧ a 3 = 468 ∧ a 4 = 2078 ∧ a 5 = 7564 ∧ a 6 = 23664 ∧ a 7 = 65711 ∧ a 8 = 165685 ∧ a 9 = 385736 ∧ a 10 = 839799 := by
  have h1 := a_1; have h2 := a_2; have h3 := a_3; have h4 := a_4; have h5 := a_5; have h6 := a_6; have h7 := a_7; have h8 := a_8; have h9 := a_9; have h10 := a_10
  
  
  omega

end OMA.S_oeis_a252817

theorem OMA.solution : type_of% @OMA.S_oeis_a252817.main :=
  OMA.S_oeis_a252817.conjecture
