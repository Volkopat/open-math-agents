import OMAStatements.S_oeis_a206687

namespace OMA.S_oeis_a206687

open PowerSeries Finset


instance {R C K : ℕ} : DecidablePred (@RowMajorNew R C K) := fun x => by
  unfold RowMajorNew; infer_instance


instance {R C K : ℕ} : DecidablePred (@Cond R C K) := fun x => by
  unfold Cond; infer_instance


/-! ## Rows -/

/-- Inside the row r, entries one or two columns apart differ. -/
def hrow (r : Fin 2 → Fin 4) : Prop := ∀ j j' : Fin 2, (j'.val = j.val + 1 ∨ j'.val = j.val + 2) → r j ≠ r j'

/-- The row s below r, if any: the entries of r and t in the same column differ. -/
def okBelow (r : Fin 2 → Fin 4) (s : Option (Fin 2 → Fin 4)) : Prop :=
  match s with
  | none => True
  | some t => ∀ j, r j ≠ t j

/-- The rows q and s two apart, if both exist: the entries in the same column differ. -/
def okTwo (q s : Option (Fin 2 → Fin 4)) : Prop :=
  match q, s with
  | some p, some t => ∀ j, p j ≠ t j
  | _, _ => True

/-- The condition on the row r with the row q above it and the row s below it. -/
def rowCond (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (s : Option (Fin 2 → Fin 4)) : Prop :=
  hrow r ∧ okBelow r s ∧ okTwo q s

instance : DecidablePred hrow := fun r => by unfold hrow; infer_instance

instance (r : Fin 2 → Fin 4) (s : Option (Fin 2 → Fin 4)) : Decidable (okBelow r s) := by
  unfold okBelow; split <;> infer_instance

instance (q s : Option (Fin 2 → Fin 4)) : Decidable (okTwo q s) := by
  unfold okTwo; split <;> infer_instance

instance (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (s : Option (Fin 2 → Fin 4)) : Decidable (rowCond q r s) := by
  unfold rowCond; infer_instance

/-! ## Values introduced in row major order, after the values below c -/

/-- The values below c count as introduced before the array; every other value below an entry
occurs at an earlier position in row major order. -/
def RGSfrom {R C K : ℕ} (c : ℕ) (x : Fin R → Fin C → Fin K) : Prop :=
  ∀ i j, ∀ u : Fin K, u < x i j → u.val < c ∨ ∃ i' j', (i' < i ∨ (i' = i ∧ j' < j)) ∧ x i' j' = u

instance {R C K : ℕ} (c : ℕ) : DecidablePred (@RGSfrom R C K c) := fun x => by
  unfold RGSfrom; infer_instance

/-- The same for one row. -/
def rowRgs {C K : ℕ} (c : ℕ) (r : Fin C → Fin K) : Prop :=
  ∀ j, ∀ u : Fin K, u < r j → u.val < c ∨ ∃ j', j' < j ∧ r j' = u

instance {C K : ℕ} (c : ℕ) : DecidablePred (@rowRgs C K c) := fun r => by
  unfold rowRgs; infer_instance

/-- The number of values introduced after the row r, when c were introduced before it. -/
def newc {C K : ℕ} (c : ℕ) (r : Fin C → Fin K) : ℕ := max c (univ.sup fun j => (r j).val + 1)

lemma lt_newc {C K : ℕ} (c : ℕ) (r : Fin C → Fin K) (u : ℕ) :
    u < newc c r ↔ u < c ∨ ∃ j, u ≤ (r j).val := by
  unfold newc
  rw [lt_max_iff, Finset.lt_sup_iff]
  simp

lemma newc_le {C K : ℕ} (c : ℕ) (hc : c ≤ K) (r : Fin C → Fin K) : newc c r ≤ K :=
  max_le hc (Finset.sup_le fun j _ => (r j).isLt)

lemma rmn_iff {R C K : ℕ} (x : Fin R → Fin C → Fin K) : RowMajorNew x ↔ RGSfrom 0 x := by
  unfold RowMajorNew RGSfrom
  simp only [Nat.not_lt_zero, false_or]

lemma RGSfrom_one {C K : ℕ} (c : ℕ) (f : Fin 1 → Fin C → Fin K) : RGSfrom c f ↔ rowRgs c (f 0) := by
  constructor
  · intro H j u hu
    rcases H 0 j u hu with h | ⟨i', j', hb, he⟩
    · exact Or.inl h
    · right
      have hi : i' = 0 := Fin.fin_one_eq_zero i'
      subst hi
      rcases hb with hb | ⟨_, hj⟩
      · exact absurd hb (lt_irrefl _)
      · exact ⟨j', hj, he⟩
  · intro H i j u hu
    have hi : i = 0 := Fin.fin_one_eq_zero i
    subst hi
    rcases H j u hu with h | ⟨j', hj, he⟩
    · exact Or.inl h
    · exact Or.inr ⟨0, j', Or.inr ⟨rfl, hj⟩, he⟩

lemma RGSfrom_cons {n C K : ℕ} (c : ℕ) (r : Fin C → Fin K) (h : Fin (n + 1) → Fin C → Fin K) :
    RGSfrom c (Fin.cons r h : Fin (n + 2) → Fin C → Fin K) ↔
      rowRgs c r ∧ RGSfrom (newc c r) h := by
  constructor
  · intro H
    refine ⟨fun j u hu => ?_, fun i j u hu => ?_⟩
    · rcases H 0 j u (by simpa using hu) with h1 | ⟨i', j', hb, he⟩
      · exact Or.inl h1
      · right
        rcases hb with hb | ⟨rfl, hj⟩
        · exact absurd hb (Fin.not_lt_zero _)
        · exact ⟨j', hj, by simpa using he⟩
    · rcases H i.succ j u (by simpa using hu) with h1 | ⟨i', j', hb, he⟩
      · left
        rw [lt_newc]
        exact Or.inl h1
      · induction i' using Fin.cases with
        | zero =>
          left
          rw [lt_newc]
          right
          refine ⟨j', ?_⟩
          simp only [Fin.cons_zero] at he
          rw [he]
        | succ i'' =>
          right
          refine ⟨i'', j', ?_, by simpa using he⟩
          rcases hb with hb | ⟨hb, hj⟩
          · exact Or.inl (Fin.succ_lt_succ_iff.mp hb)
          · exact Or.inr ⟨Fin.succ_injective _ hb, hj⟩
  · rintro ⟨H0, H⟩ i j u hu
    induction i using Fin.cases with
    | zero =>
      rcases H0 j u (by simpa using hu) with h1 | ⟨j', hj, he⟩
      · exact Or.inl h1
      · exact Or.inr ⟨0, j', Or.inr ⟨rfl, hj⟩, by simpa using he⟩
    | succ i =>
      rcases H i j u (by simpa using hu) with h1 | ⟨i', j', hb, he⟩
      · rw [lt_newc] at h1
        rcases h1 with h1 | ⟨j', hj'⟩
        · exact Or.inl h1
        · rcases Nat.lt_or_eq_of_le hj' with hlt | heq
          · rcases H0 j' u hlt with h2 | ⟨j'', _, he⟩
            · exact Or.inl h2
            · exact Or.inr ⟨0, j'', Or.inl (Fin.succ_pos _), by simpa using he⟩
          · exact Or.inr ⟨0, j', Or.inl (Fin.succ_pos _), by simpa using (Fin.ext heq).symm⟩
      · right
        refine ⟨i'.succ, j', ?_, by simpa using he⟩
        rcases hb with hb | ⟨rfl, hj⟩
        · exact Or.inl (Fin.succ_lt_succ_iff.mpr hb)
        · exact Or.inr ⟨rfl, hj⟩


/-! ## Rows with the row above and the row below -/

/-- The row above row i of g: q for the first row, g (i - 1) otherwise. -/
def prevRow {n : ℕ} (q : Option (Fin 2 → Fin 4)) (g : Fin n → Fin 2 → Fin 4) (i : Fin n) : Option (Fin 2 → Fin 4) :=
  match i with
  | ⟨0, _⟩ => q
  | ⟨k + 1, h⟩ => some (g ⟨k, Nat.lt_of_succ_lt h⟩)

/-- The row below row i of g, none for the last row. -/
def nextRow {n : ℕ} (g : Fin n → Fin 2 → Fin 4) (i : Fin n) : Option (Fin 2 → Fin 4) :=
  if h : i.val + 1 < n then some (g ⟨i.val + 1, h⟩) else none

/-- Every row of g satisfies the condition with the rows above and below it; q is the row above
the first row. -/
def ValidFrom {n : ℕ} (q : Option (Fin 2 → Fin 4)) (g : Fin n → Fin 2 → Fin 4) : Prop :=
  ∀ i, rowCond (prevRow q g i) (g i) (nextRow g i)

instance {n : ℕ} (q : Option (Fin 2 → Fin 4)) : DecidablePred (@ValidFrom n q) := fun g => by
  unfold ValidFrom; infer_instance

lemma validFrom_one (q : Option (Fin 2 → Fin 4)) (g : Fin 1 → Fin 2 → Fin 4) :
    ValidFrom q g ↔ rowCond q (g 0) none := by
  constructor
  · intro h
    exact h 0
  · intro h i
    have hi : i = 0 := Fin.fin_one_eq_zero i
    subst hi
    exact h

lemma prevRow_cons_zero {n : ℕ} (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (h : Fin (n + 1) → Fin 2 → Fin 4) :
    prevRow q (Fin.cons r h : Fin (n + 2) → Fin 2 → Fin 4) 0 = q := rfl

lemma prevRow_cons_succ {n : ℕ} (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (h : Fin (n + 1) → Fin 2 → Fin 4)
    (k : Fin (n + 1)) :
    prevRow q (Fin.cons r h : Fin (n + 2) → Fin 2 → Fin 4) k.succ = prevRow (some r) h k := by
  rcases k with ⟨_ | j, hk⟩ <;> rfl

lemma nextRow_cons_zero {n : ℕ} (r : Fin 2 → Fin 4) (h : Fin (n + 1) → Fin 2 → Fin 4) :
    nextRow (Fin.cons r h : Fin (n + 2) → Fin 2 → Fin 4) 0 = some (h 0) := by
  unfold nextRow
  rw [dif_pos (by simp)]
  rfl

lemma nextRow_cons_succ {n : ℕ} (r : Fin 2 → Fin 4) (h : Fin (n + 1) → Fin 2 → Fin 4) (k : Fin (n + 1)) :
    nextRow (Fin.cons r h : Fin (n + 2) → Fin 2 → Fin 4) k.succ = nextRow h k := by
  unfold nextRow
  by_cases hk : k.val + 1 < n + 1
  · rw [dif_pos (by simp; omega), dif_pos hk]
    rfl
  · rw [dif_neg (by simp; omega), dif_neg hk]

lemma validFrom_cons {n : ℕ} (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (h : Fin (n + 1) → Fin 2 → Fin 4) :
    ValidFrom q (Fin.cons r h : Fin (n + 2) → Fin 2 → Fin 4) ↔
      rowCond q r (some (h 0)) ∧ ValidFrom (some r) h := by
  unfold ValidFrom
  rw [Fin.forall_fin_succ]
  simp only [prevRow_cons_zero, prevRow_cons_succ, nextRow_cons_zero, nextRow_cons_succ,
    Fin.cons_zero, Fin.cons_succ]

/-! ## Counting by the first row -/

/-- W(n, q, r, c): arrays with n + 1 rows, first row r with the row q above it, every row
satisfying the condition, values introduced in row major order after the values below c. -/
def W (n : ℕ) (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (c : ℕ) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 2 → Fin 4)).filter
    (fun g => ValidFrom q g ∧ RGSfrom c g ∧ g 0 = r)).card

lemma W_zero (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (c : ℕ) :
    W 0 q r c = if rowCond q r none ∧ rowRgs c r then 1 else 0 := by
  unfold W
  split_ifs with hr
  · rw [Finset.card_eq_one]
    refine ⟨fun _ => r, ?_⟩
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨_, _, hf⟩
      funext i
      rw [Fin.fin_one_eq_zero i, hf]
    · rintro rfl
      exact ⟨(validFrom_one q _).2 hr.1, (RGSfrom_one c _).2 hr.2, rfl⟩
  · rw [Finset.card_eq_zero]
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨hv, hR, h0⟩
    apply hr
    rw [← h0]
    exact ⟨(validFrom_one q f).1 hv, (RGSfrom_one c f).1 hR⟩

/-- Prepending the row r to an array with n + 1 rows. -/
def consEmb (n : ℕ) (r : Fin 2 → Fin 4) :
    (Fin (n + 1) → Fin 2 → Fin 4) ↪ (Fin (n + 2) → Fin 2 → Fin 4) where
  toFun g := Fin.cons r g
  inj' g g' h := by
    funext i
    have := congrFun h i.succ
    simpa using this

lemma consEmb_apply (n : ℕ) (r : Fin 2 → Fin 4) (g : Fin (n + 1) → Fin 2 → Fin 4) :
    consEmb n r g = Fin.cons r g := rfl

lemma W_succ (n : ℕ) (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (c : ℕ) :
    W (n + 1) q r c = if rowRgs c r then
      ∑ s : Fin 2 → Fin 4, (if rowCond q r (some s) then W n (some r) s (newc c r) else 0) else 0 := by
  have e : ((univ : Finset (Fin (n + 2) → Fin 2 → Fin 4)).filter
      (fun f => ValidFrom q f ∧ RGSfrom c f ∧ f 0 = r)) =
      (((univ : Finset (Fin (n + 1) → Fin 2 → Fin 4)).filter
        (fun g => (rowRgs c r ∧ rowCond q r (g 0)) ∧ ValidFrom (some r) g ∧
          RGSfrom (newc c r) g)).map (consEmb n r)) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, consEmb_apply]
    constructor
    · rintro ⟨hv, hR, h0⟩
      refine ⟨Fin.tail f, ?_, ?_⟩
      · have hf : f = Fin.cons r (Fin.tail f) := by
          rw [← h0]; exact (Fin.cons_self_tail f).symm
        rw [hf, validFrom_cons] at hv
        rw [hf, RGSfrom_cons] at hR
        exact ⟨⟨hR.1, hv.1⟩, hv.2, hR.2⟩
      · rw [← h0]; exact Fin.cons_self_tail f
    · rintro ⟨g, ⟨⟨h1, h2⟩, hg, hR⟩, rfl⟩
      exact ⟨(validFrom_cons q r g).2 ⟨h2, hg⟩, (RGSfrom_cons c r g).2 ⟨h1, hR⟩, by simp⟩
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
        exact ⟨hg.1, hg.2, h0⟩
      · rintro ⟨hg, hR, h0⟩
        exact ⟨⟨⟨hrc, by rw [h0]; exact hrs⟩, hg, hR⟩, h0⟩
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

lemma nextRow_eq {R : ℕ} (x : Fin R → Fin 2 → Fin 4) (i i' : Fin R) (h : i'.val = i.val + 1) :
    nextRow x i = some (x i') := by
  unfold nextRow
  rw [dif_pos (by omega)]
  have e : (⟨i.val + 1, by omega⟩ : Fin R) = i' := Fin.ext h.symm
  rw [e]

lemma nextRow_none {R : ℕ} (x : Fin R → Fin 2 → Fin 4) (i : Fin R) (h : ¬ i.val + 1 < R) :
    nextRow x i = none := by
  unfold nextRow
  rw [dif_neg h]

lemma prevRow_eq {R : ℕ} (q : Option (Fin 2 → Fin 4)) (x : Fin R → Fin 2 → Fin 4) (i i' : Fin R)
    (h : i.val = i'.val + 1) : prevRow q x i = some (x i') := by
  rcases i with ⟨_ | k, hi⟩
  · simp at h
  · have e : (⟨k, Nat.lt_of_succ_lt hi⟩ : Fin R) = i' := Fin.ext (by simp only [Fin.val_mk] at h ⊢; omega)
    show some (x ⟨k, Nat.lt_of_succ_lt hi⟩) = some (x i')
    rw [e]

lemma cond_iff {R : ℕ} (x : Fin R → Fin 2 → Fin 4) : Cond x ↔ ValidFrom none x := by
  unfold Cond ValidFrom rowCond
  constructor
  · intro H i
    refine ⟨fun j j' hj => H i i j j' (Or.inl ⟨rfl, fun h => by rw [h] at hj; omega, by omega, by omega⟩),
      ?_, ?_⟩
    · by_cases hlt : i.val + 1 < R
      · rw [nextRow_eq x i ⟨i.val + 1, hlt⟩ rfl]
        intro j
        exact H i ⟨i.val + 1, hlt⟩ j j
          (Or.inr ⟨rfl, fun h => absurd (congrArg Fin.val h) (by show i.val ≠ i.val + 1; omega),
            by show i.val ≤ i.val + 1 + 2; omega, by show i.val + 1 ≤ i.val + 2; omega⟩)
      · rw [nextRow_none x i hlt]
        trivial
    · rcases i with ⟨_ | k, hi⟩
      · trivial
      · by_cases hlt : k + 1 + 1 < R
        · rw [prevRow_eq none x ⟨k + 1, hi⟩ ⟨k, by omega⟩ rfl,
            nextRow_eq x ⟨k + 1, hi⟩ ⟨k + 1 + 1, hlt⟩ rfl]
          intro j
          exact H ⟨k, by omega⟩ ⟨k + 1 + 1, hlt⟩ j j
            (Or.inr ⟨rfl, fun h => absurd (congrArg Fin.val h) (by show k ≠ k + 1 + 1; omega),
              by show k ≤ k + 1 + 1 + 2; omega, by show k + 1 + 1 ≤ k + 2; omega⟩)
        · rw [nextRow_none x ⟨k + 1, hi⟩ hlt]
          cases prevRow none x ⟨k + 1, hi⟩ <;> trivial
  · intro V i i' j j' hd
    rcases hd with ⟨hi, hj, h1, h2⟩ | ⟨hj, hi, h1, h2⟩
    · rw [show i' = i from hi.symm]
      have hne : j.val ≠ j'.val := fun h => hj (Fin.ext h)
      rcases (by omega : (j'.val = j.val + 1 ∨ j'.val = j.val + 2) ∨
          (j.val = j'.val + 1 ∨ j.val = j'.val + 2)) with h | h
      · exact (V i).1 j j' h
      · exact fun e => (V i).1 j' j h e.symm
    · rw [show j' = j from hj.symm]
      have hne : i.val ≠ i'.val := fun h => hi (Fin.ext h)
      rcases (by omega : i'.val = i.val + 1 ∨ i.val = i'.val + 1 ∨ i'.val = i.val + 2 ∨
          i.val = i'.val + 2) with h | h | h | h
      · have hb := (V i).2.1
        rw [nextRow_eq x i i' h] at hb
        exact hb j
      · have hb := (V i').2.1
        rw [nextRow_eq x i' i h] at hb
        exact fun e => hb j e.symm
      · have hm : i.val + 1 < R := by omega
        have hb := (V ⟨i.val + 1, hm⟩).2.2
        rw [prevRow_eq none x ⟨i.val + 1, hm⟩ i rfl,
          nextRow_eq x ⟨i.val + 1, hm⟩ i' (by show i'.val = i.val + 1 + 1; omega)] at hb
        exact hb j
      · have hm : i'.val + 1 < R := by omega
        have hb := (V ⟨i'.val + 1, hm⟩).2.2
        rw [prevRow_eq none x ⟨i'.val + 1, hm⟩ i' rfl,
          nextRow_eq x ⟨i'.val + 1, hm⟩ i (by show i.val = i'.val + 1 + 1; omega)] at hb
        exact fun e => hb j e.symm

/-! ## Kernel form of the transfer -/

lemma sum_cons {m : ℕ} (f : (Fin (m + 1) → Fin 4) → ℕ) :
    ∑ s : Fin (m + 1) → Fin 4, f s = ∑ x : Fin 4, ∑ t : Fin m → Fin 4, f (Fin.cons x t) := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 4).symm _ _
    (fun s => by simp [Fin.consEquiv, Fin.cons_self_tail])

lemma sum_row (f : (Fin 2 → Fin 4) → ℕ) :
    ∑ s : Fin 2 → Fin 4, f s = ∑ x : Fin 4, ∑ y : Fin 4, f ![x, y] := by
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Fintype.sum_unique]
  exact congrArg f (by funext j; fin_cases j <;> rfl)

lemma row_eta (r : Fin 2 → Fin 4) : r = ![r 0, r 1] := by
  funext j
  fin_cases j <;> rfl

/-! Fast Boolean forms of the conditions for the kernel checks, tied to the definitions by
`decide` over all small cases. -/

/-- `rowRgs c r` as a Boolean. -/
def rgsB (c : ℕ) (r : Fin 2 → Fin 4) : Bool :=
  decide ((r 0).val ≤ c) &&
    decide ((r 1).val ≤ max c ((r 0).val + 1))

/-- `newc c r` by explicit maxima. -/
def newcB (c : ℕ) (r : Fin 2 → Fin 4) : ℕ :=
  max (max c ((r 0).val + 1)) ((r 1).val + 1)

/-- `rowCond q r (some t)` as a Boolean. -/
def condB (q : Option (Fin 2 → Fin 4)) (r t : Fin 2 → Fin 4) : Bool :=
  decide (r 0 ≠ r 1) &&
    decide (r 0 ≠ t 0) && decide (r 1 ≠ t 1) &&
    (match q with | none => true | some p => decide (p 0 ≠ t 0) && decide (p 1 ≠ t 1))

/-- `rowCond q r none` as a Boolean. -/
def endB (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) : Bool :=
  decide (r 0 ≠ r 1)

lemma rgsB_eq : ∀ c : Fin 5, ∀ y1 y2 : Fin 4,
    decide (rowRgs c.val ![y1, y2]) = rgsB c.val ![y1, y2] := by
  decide +kernel

lemma newcB_eq : ∀ c : Fin 5, ∀ y1 y2 : Fin 4,
    newc c.val ![y1, y2] = newcB c.val ![y1, y2] := by
  decide +kernel

lemma condB_eqN : ∀ y1 y2 x y : Fin 4,
    decide (rowCond none ![y1, y2] (some ![x, y])) = condB none ![y1, y2] ![x, y] := by
  decide +kernel

lemma condB_eqS : ∀ p1 p2 y1 y2 x y : Fin 4,
    decide (rowCond (some ![p1, p2]) ![y1, y2] (some ![x, y])) =
      condB (some ![p1, p2]) ![y1, y2] ![x, y] := by
  decide +kernel

lemma endB_eqN : ∀ y1 y2 : Fin 4,
    decide (rowCond none ![y1, y2] none) = endB none ![y1, y2] := by
  decide +kernel

lemma endB_eqS : ∀ p1 p2 y1 y2 : Fin 4,
    decide (rowCond (some ![p1, p2]) ![y1, y2] none) = endB (some ![p1, p2]) ![y1, y2] := by
  decide +kernel

lemma rgsB_iff (c : ℕ) (hc : c ≤ 4) (r : Fin 2 → Fin 4) : rowRgs c r ↔ rgsB c r = true := by
  rw [row_eta r, ← rgsB_eq ⟨c, by omega⟩, decide_eq_true_iff]

lemma newcB_eq' (c : ℕ) (hc : c ≤ 4) (r : Fin 2 → Fin 4) : newc c r = newcB c r := by
  rw [row_eta r]
  exact newcB_eq ⟨c, by omega⟩ (r 0) (r 1)

lemma newcB_le (c : ℕ) (hc : c ≤ 4) (r : Fin 2 → Fin 4) : newcB c r ≤ 4 := by
  rw [← newcB_eq' c hc r]
  exact newc_le c hc r

lemma condB_iff (q : Option (Fin 2 → Fin 4)) (r t : Fin 2 → Fin 4) : rowCond q r (some t) ↔ condB q r t = true := by
  rcases q with _ | p
  · rw [row_eta r, row_eta t, ← condB_eqN, decide_eq_true_iff]
  · rw [row_eta p, row_eta r, row_eta t, ← condB_eqS, decide_eq_true_iff]

lemma endB_iff (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) : rowCond q r none ↔ endB q r = true := by
  rcases q with _ | p
  · rw [row_eta r, ← endB_eqN, decide_eq_true_iff]
  · rw [row_eta p, row_eta r, ← endB_eqS, decide_eq_true_iff]

/-- One step of the transfer, the rows below r enumerated entry by entry. -/
def T (g : Option (Fin 2 → Fin 4) → (Fin 2 → Fin 4) → ℕ → ℕ) (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (c : ℕ) : ℕ :=
  if rgsB c r = true then
    ∑ x : Fin 4, ∑ y : Fin 4, (if condB q r ![x, y] = true then g (some r) ![x, y] (newcB c r) else 0)
  else 0

lemma W_succT (n : ℕ) (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (c : ℕ) (hc : c ≤ 4) :
    W (n + 1) q r c = T (W n) q r c := by
  rw [W_succ, sum_row]
  unfold T
  simp only [rgsB_iff c hc, condB_iff, newcB_eq' c hc]

lemma T_congr (g g' : Option (Fin 2 → Fin 4) → (Fin 2 → Fin 4) → ℕ → ℕ) (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (c : ℕ)
    (h : ∀ s, g (some r) s (newcB c r) = g' (some r) s (newcB c r)) : T g q r c = T g' q r c := by
  unfold T
  simp only [h]

/-- W(0) as a function. -/
def W0f (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (c : ℕ) : ℕ :=
  if endB q r = true ∧ rgsB c r = true then 1 else 0

lemma W_zero' (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (c : ℕ) (hc : c ≤ 4) : W 0 q r c = W0f q r c := by
  rw [W_zero]
  unfold W0f
  simp only [endB_iff, rgsB_iff c hc]

lemma inv_next (c : ℕ) (hc : c ≤ 4) (r : Fin 2 → Fin 4) :
    ∀ p, some r = some p → ∀ j, (p j).val < newcB c r := by
  intro p hp j
  rw [← Option.some.inj hp, ← newcB_eq' c hc r]
  exact (lt_newc c r _).2 (Or.inr ⟨j, le_refl _⟩)

/-- W(1, none, r, c) for c <= 4, nested by the entries of r and then c. -/
def LN1 : List (List (List ℕ)) :=
  [[[0, 0, 0, 0, 0], [4, 4, 4, 7, 7], [0, 0, 7, 7, 7], [0, 0, 0, 7, 7]], [[0, 4, 4, 7, 7], [0, 0, 0, 0, 0], [0, 7, 7, 7, 7], [0, 0, 0, 7, 7]], [[0, 0, 7, 7, 7], [0, 0, 7, 7, 7], [0, 0, 0, 0, 0], [0, 0, 7, 7, 7]], [[0, 0, 0, 7, 7], [0, 0, 0, 7, 7], [0, 0, 0, 7, 7], [0, 0, 0, 0, 0]]]

/-- W(1, some p, r, c) for c <= 4, nested by the entries of p, of r, and then c. -/
def LS1 : List (List (List (List (List ℕ)))) :=
  [[[[[0, 0, 0, 0, 0], [2, 2, 2, 4, 4], [0, 0, 4, 4, 4], [0, 0, 0, 4, 4]], [[0, 2, 2, 4, 4], [0, 0, 0, 0, 0], [0, 3, 3, 3, 3], [0, 0, 0, 3, 3]], [[0, 0, 4, 4, 4], [0, 0, 3, 3, 3], [0, 0, 0, 0, 0], [0, 0, 3, 3, 3]], [[0, 0, 0, 4, 4], [0, 0, 0, 3, 3], [0, 0, 0, 3, 3], [0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0], [4, 4, 4, 7, 7], [0, 0, 5, 5, 5], [0, 0, 0, 5, 5]], [[0, 1, 1, 2, 2], [0, 0, 0, 0, 0], [0, 3, 3, 3, 3], [0, 0, 0, 3, 3]], [[0, 0, 3, 3, 3], [0, 0, 5, 5, 5], [0, 0, 0, 0, 0], [0, 0, 4, 4, 4]], [[0, 0, 0, 3, 3], [0, 0, 0, 5, 5], [0, 0, 0, 4, 4], [0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0], [3, 3, 3, 5, 5], [0, 0, 7, 7, 7], [0, 0, 0, 5, 5]], [[0, 2, 2, 3, 3], [0, 0, 0, 0, 0], [0, 5, 5, 5, 5], [0, 0, 0, 4, 4]], [[0, 0, 2, 2, 2], [0, 0, 3, 3, 3], [0, 0, 0, 0, 0], [0, 0, 3, 3, 3]], [[0, 0, 0, 3, 3], [0, 0, 0, 4, 4], [0, 0, 0, 5, 5], [0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0], [3, 3, 3, 5, 5], [0, 0, 5, 5, 5], [0, 0, 0, 7, 7]], [[0, 1, 1, 3, 3], [0, 0, 0, 0, 0], [0, 4, 4, 4, 4], [0, 0, 0, 5, 5]], [[0, 0, 3, 3, 3], [0, 0, 4, 4, 4], [0, 0, 0, 0, 0], [0, 0, 5, 5, 5]], [[0, 0, 0, 2, 2], [0, 0, 0, 3, 3], [0, 0, 0, 3, 3], [0, 0, 0, 0, 0]]]], [[[[0, 0, 0, 0, 0], [1, 1, 1, 2, 2], [0, 0, 3, 3, 3], [0, 0, 0, 3, 3]], [[0, 4, 4, 7, 7], [0, 0, 0, 0, 0], [0, 5, 5, 5, 5], [0, 0, 0, 5, 5]], [[0, 0, 5, 5, 5], [0, 0, 3, 3, 3], [0, 0, 0, 0, 0], [0, 0, 4, 4, 4]], [[0, 0, 0, 5, 5], [0, 0, 0, 3, 3], [0, 0, 0, 4, 4], [0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0], [2, 2, 2, 4, 4], [0, 0, 3, 3, 3], [0, 0, 0, 3, 3]], [[0, 2, 2, 4, 4], [0, 0, 0, 0, 0], [0, 4, 4, 4, 4], [0, 0, 0, 4, 4]], [[0, 0, 3, 3, 3], [0, 0, 4, 4, 4], [0, 0, 0, 0, 0], [0, 0, 3, 3, 3]], [[0, 0, 0, 3, 3], [0, 0, 0, 4, 4], [0, 0, 0, 3, 3], [0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0], [2, 2, 2, 3, 3], [0, 0, 5, 5, 5], [0, 0, 0, 4, 4]], [[0, 3, 3, 5, 5], [0, 0, 0, 0, 0], [0, 7, 7, 7, 7], [0, 0, 0, 5, 5]], [[0, 0, 3, 3, 3], [0, 0, 2, 2, 2], [0, 0, 0, 0, 0], [0, 0, 3, 3, 3]], [[0, 0, 0, 4, 4], [0, 0, 0, 3, 3], [0, 0, 0, 5, 5], [0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0], [1, 1, 1, 3, 3], [0, 0, 4, 4, 4], [0, 0, 0, 5, 5]], [[0, 3, 3, 5, 5], [0, 0, 0, 0, 0], [0, 5, 5, 5, 5], [0, 0, 0, 7, 7]], [[0, 0, 4, 4, 4], [0, 0, 3, 3, 3], [0, 0, 0, 0, 0], [0, 0, 5, 5, 5]], [[0, 0, 0, 3, 3], [0, 0, 0, 2, 2], [0, 0, 0, 3, 3], [0, 0, 0, 0, 0]]]], [[[[0, 0, 0, 0, 0], [1, 1, 1, 3, 3], [0, 0, 2, 2, 2], [0, 0, 0, 3, 3]], [[0, 2, 2, 5, 5], [0, 0, 0, 0, 0], [0, 3, 3, 3, 3], [0, 0, 0, 4, 4]], [[0, 0, 7, 7, 7], [0, 0, 5, 5, 5], [0, 0, 0, 0, 0], [0, 0, 5, 5, 5]], [[0, 0, 0, 5, 5], [0, 0, 0, 4, 4], [0, 0, 0, 3, 3], [0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0], [2, 2, 2, 5, 5], [0, 0, 3, 3, 3], [0, 0, 0, 4, 4]], [[0, 1, 1, 3, 3], [0, 0, 0, 0, 0], [0, 2, 2, 2, 2], [0, 0, 0, 3, 3]], [[0, 0, 5, 5, 5], [0, 0, 7, 7, 7], [0, 0, 0, 0, 0], [0, 0, 5, 5, 5]], [[0, 0, 0, 4, 4], [0, 0, 0, 5, 5], [0, 0, 0, 3, 3], [0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0], [1, 1, 1, 3, 3], [0, 0, 4, 4, 4], [0, 0, 0, 3, 3]], [[0, 1, 1, 3, 3], [0, 0, 0, 0, 0], [0, 4, 4, 4, 4], [0, 0, 0, 3, 3]], [[0, 0, 4, 4, 4], [0, 0, 4, 4, 4], [0, 0, 0, 0, 0], [0, 0, 4, 4, 4]], [[0, 0, 0, 3, 3], [0, 0, 0, 3, 3], [0, 0, 0, 4, 4], [0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0], [2, 2, 2, 4, 4], [0, 0, 3, 3, 3], [0, 0, 0, 5, 5]], [[0, 2, 2, 4, 4], [0, 0, 0, 0, 0], [0, 3, 3, 3, 3], [0, 0, 0, 5, 5]], [[0, 0, 5, 5, 5], [0, 0, 5, 5, 5], [0, 0, 0, 0, 0], [0, 0, 7, 7, 7]], [[0, 0, 0, 3, 3], [0, 0, 0, 3, 3], [0, 0, 0, 2, 2], [0, 0, 0, 0, 0]]]], [[[[0, 0, 0, 0, 0], [2, 2, 2, 3, 3], [0, 0, 3, 3, 3], [0, 0, 0, 2, 2]], [[0, 4, 4, 5, 5], [0, 0, 0, 0, 0], [0, 4, 4, 4, 4], [0, 0, 0, 3, 3]], [[0, 0, 5, 5, 5], [0, 0, 4, 4, 4], [0, 0, 0, 0, 0], [0, 0, 3, 3, 3]], [[0, 0, 0, 7, 7], [0, 0, 0, 5, 5], [0, 0, 0, 5, 5], [0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0], [4, 4, 4, 5, 5], [0, 0, 4, 4, 4], [0, 0, 0, 3, 3]], [[0, 2, 2, 3, 3], [0, 0, 0, 0, 0], [0, 3, 3, 3, 3], [0, 0, 0, 2, 2]], [[0, 0, 4, 4, 4], [0, 0, 5, 5, 5], [0, 0, 0, 0, 0], [0, 0, 3, 3, 3]], [[0, 0, 0, 5, 5], [0, 0, 0, 7, 7], [0, 0, 0, 5, 5], [0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0], [3, 3, 3, 4, 4], [0, 0, 5, 5, 5], [0, 0, 0, 3, 3]], [[0, 3, 3, 4, 4], [0, 0, 0, 0, 0], [0, 5, 5, 5, 5], [0, 0, 0, 3, 3]], [[0, 0, 3, 3, 3], [0, 0, 3, 3, 3], [0, 0, 0, 0, 0], [0, 0, 2, 2, 2]], [[0, 0, 0, 5, 5], [0, 0, 0, 5, 5], [0, 0, 0, 7, 7], [0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0], [3, 3, 3, 3, 3], [0, 0, 3, 3, 3], [0, 0, 0, 4, 4]], [[0, 3, 3, 3, 3], [0, 0, 0, 0, 0], [0, 3, 3, 3, 3], [0, 0, 0, 4, 4]], [[0, 0, 3, 3, 3], [0, 0, 3, 3, 3], [0, 0, 0, 0, 0], [0, 0, 4, 4, 4]], [[0, 0, 0, 4, 4], [0, 0, 0, 4, 4], [0, 0, 0, 4, 4], [0, 0, 0, 0, 0]]]]]

/-- W(1) as a table. -/
def tab1 (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (c : ℕ) : ℕ :=
  match q with
  | none => ((LN1.getD (r 0).val []).getD (r 1).val []).getD c 0
  | some p => ((((LS1.getD (p 0).val []).getD (p 1).val []).getD (r 0).val []).getD (r 1).val []).getD c 0

/-- W(2, none, r, c) for c <= 4, nested by the entries of r and then c. -/
def LN2 : List (List (List ℕ)) :=
  [[[0, 0, 0, 0, 0], [11, 11, 11, 22, 22], [0, 0, 22, 22, 22], [0, 0, 0, 22, 22]], [[0, 11, 11, 22, 22], [0, 0, 0, 0, 0], [0, 22, 22, 22, 22], [0, 0, 0, 22, 22]], [[0, 0, 22, 22, 22], [0, 0, 22, 22, 22], [0, 0, 0, 0, 0], [0, 0, 22, 22, 22]], [[0, 0, 0, 22, 22], [0, 0, 0, 22, 22], [0, 0, 0, 22, 22], [0, 0, 0, 0, 0]]]

/-- W(2, some p, r, c) for c <= 4, nested by the entries of p, of r, and then c. -/
def LS2 : List (List (List (List (List ℕ)))) :=
  [[[[[0, 0, 0, 0, 0], [7, 7, 7, 14, 14], [0, 0, 14, 14, 14], [0, 0, 0, 14, 14]], [[0, 7, 7, 14, 14], [0, 0, 0, 0, 0], [0, 8, 8, 8, 8], [0, 0, 0, 8, 8]], [[0, 0, 14, 14, 14], [0, 0, 8, 8, 8], [0, 0, 0, 0, 0], [0, 0, 8, 8, 8]], [[0, 0, 0, 14, 14], [0, 0, 0, 8, 8], [0, 0, 0, 8, 8], [0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0], [11, 11, 11, 22, 22], [0, 0, 15, 15, 15], [0, 0, 0, 15, 15]], [[0, 4, 4, 8, 8], [0, 0, 0, 0, 0], [0, 10, 10, 10, 10], [0, 0, 0, 10, 10]], [[0, 0, 10, 10, 10], [0, 0, 15, 15, 15], [0, 0, 0, 0, 0], [0, 0, 12, 12, 12]], [[0, 0, 0, 10, 10], [0, 0, 0, 15, 15], [0, 0, 0, 12, 12], [0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0], [8, 8, 8, 15, 15], [0, 0, 22, 22, 22], [0, 0, 0, 15, 15]], [[0, 7, 7, 10, 10], [0, 0, 0, 0, 0], [0, 15, 15, 15, 15], [0, 0, 0, 12, 12]], [[0, 0, 8, 8, 8], [0, 0, 10, 10, 10], [0, 0, 0, 0, 0], [0, 0, 10, 10, 10]], [[0, 0, 0, 10, 10], [0, 0, 0, 12, 12], [0, 0, 0, 15, 15], [0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0], [7, 7, 7, 15, 15], [0, 0, 15, 15, 15], [0, 0, 0, 22, 22]], [[0, 3, 3, 10, 10], [0, 0, 0, 0, 0], [0, 12, 12, 12, 12], [0, 0, 0, 15, 15]], [[0, 0, 10, 10, 10], [0, 0, 12, 12, 12], [0, 0, 0, 0, 0], [0, 0, 15, 15, 15]], [[0, 0, 0, 8, 8], [0, 0, 0, 10, 10], [0, 0, 0, 10, 10], [0, 0, 0, 0, 0]]]], [[[[0, 0, 0, 0, 0], [4, 4, 4, 8, 8], [0, 0, 10, 10, 10], [0, 0, 0, 10, 10]], [[0, 11, 11, 22, 22], [0, 0, 0, 0, 0], [0, 15, 15, 15, 15], [0, 0, 0, 15, 15]], [[0, 0, 15, 15, 15], [0, 0, 10, 10, 10], [0, 0, 0, 0, 0], [0, 0, 12, 12, 12]], [[0, 0, 0, 15, 15], [0, 0, 0, 10, 10], [0, 0, 0, 12, 12], [0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0], [7, 7, 7, 14, 14], [0, 0, 8, 8, 8], [0, 0, 0, 8, 8]], [[0, 7, 7, 14, 14], [0, 0, 0, 0, 0], [0, 14, 14, 14, 14], [0, 0, 0, 14, 14]], [[0, 0, 8, 8, 8], [0, 0, 14, 14, 14], [0, 0, 0, 0, 0], [0, 0, 8, 8, 8]], [[0, 0, 0, 8, 8], [0, 0, 0, 14, 14], [0, 0, 0, 8, 8], [0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0], [7, 7, 7, 10, 10], [0, 0, 15, 15, 15], [0, 0, 0, 12, 12]], [[0, 8, 8, 15, 15], [0, 0, 0, 0, 0], [0, 22, 22, 22, 22], [0, 0, 0, 15, 15]], [[0, 0, 10, 10, 10], [0, 0, 8, 8, 8], [0, 0, 0, 0, 0], [0, 0, 10, 10, 10]], [[0, 0, 0, 12, 12], [0, 0, 0, 10, 10], [0, 0, 0, 15, 15], [0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0], [3, 3, 3, 10, 10], [0, 0, 12, 12, 12], [0, 0, 0, 15, 15]], [[0, 7, 7, 15, 15], [0, 0, 0, 0, 0], [0, 15, 15, 15, 15], [0, 0, 0, 22, 22]], [[0, 0, 12, 12, 12], [0, 0, 10, 10, 10], [0, 0, 0, 0, 0], [0, 0, 15, 15, 15]], [[0, 0, 0, 10, 10], [0, 0, 0, 8, 8], [0, 0, 0, 10, 10], [0, 0, 0, 0, 0]]]], [[[[0, 0, 0, 0, 0], [3, 3, 3, 10, 10], [0, 0, 8, 8, 8], [0, 0, 0, 10, 10]], [[0, 4, 4, 15, 15], [0, 0, 0, 0, 0], [0, 10, 10, 10, 10], [0, 0, 0, 12, 12]], [[0, 0, 22, 22, 22], [0, 0, 15, 15, 15], [0, 0, 0, 0, 0], [0, 0, 15, 15, 15]], [[0, 0, 0, 15, 15], [0, 0, 0, 12, 12], [0, 0, 0, 10, 10], [0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0], [4, 4, 4, 15, 15], [0, 0, 10, 10, 10], [0, 0, 0, 12, 12]], [[0, 3, 3, 10, 10], [0, 0, 0, 0, 0], [0, 8, 8, 8, 8], [0, 0, 0, 10, 10]], [[0, 0, 15, 15, 15], [0, 0, 22, 22, 22], [0, 0, 0, 0, 0], [0, 0, 15, 15, 15]], [[0, 0, 0, 12, 12], [0, 0, 0, 15, 15], [0, 0, 0, 10, 10], [0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0], [1, 1, 1, 8, 8], [0, 0, 14, 14, 14], [0, 0, 0, 8, 8]], [[0, 1, 1, 8, 8], [0, 0, 0, 0, 0], [0, 14, 14, 14, 14], [0, 0, 0, 8, 8]], [[0, 0, 14, 14, 14], [0, 0, 14, 14, 14], [0, 0, 0, 0, 0], [0, 0, 14, 14, 14]], [[0, 0, 0, 8, 8], [0, 0, 0, 8, 8], [0, 0, 0, 14, 14], [0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0], [4, 4, 4, 12, 12], [0, 0, 10, 10, 10], [0, 0, 0, 15, 15]], [[0, 4, 4, 12, 12], [0, 0, 0, 0, 0], [0, 10, 10, 10, 10], [0, 0, 0, 15, 15]], [[0, 0, 15, 15, 15], [0, 0, 15, 15, 15], [0, 0, 0, 0, 0], [0, 0, 22, 22, 22]], [[0, 0, 0, 10, 10], [0, 0, 0, 10, 10], [0, 0, 0, 8, 8], [0, 0, 0, 0, 0]]]], [[[[0, 0, 0, 0, 0], [7, 7, 7, 10, 10], [0, 0, 10, 10, 10], [0, 0, 0, 8, 8]], [[0, 11, 11, 15, 15], [0, 0, 0, 0, 0], [0, 12, 12, 12, 12], [0, 0, 0, 10, 10]], [[0, 0, 15, 15, 15], [0, 0, 12, 12, 12], [0, 0, 0, 0, 0], [0, 0, 10, 10, 10]], [[0, 0, 0, 22, 22], [0, 0, 0, 15, 15], [0, 0, 0, 15, 15], [0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0], [11, 11, 11, 15, 15], [0, 0, 12, 12, 12], [0, 0, 0, 10, 10]], [[0, 7, 7, 10, 10], [0, 0, 0, 0, 0], [0, 10, 10, 10, 10], [0, 0, 0, 8, 8]], [[0, 0, 12, 12, 12], [0, 0, 15, 15, 15], [0, 0, 0, 0, 0], [0, 0, 10, 10, 10]], [[0, 0, 0, 15, 15], [0, 0, 0, 22, 22], [0, 0, 0, 15, 15], [0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0], [8, 8, 8, 12, 12], [0, 0, 15, 15, 15], [0, 0, 0, 10, 10]], [[0, 8, 8, 12, 12], [0, 0, 0, 0, 0], [0, 15, 15, 15, 15], [0, 0, 0, 10, 10]], [[0, 0, 10, 10, 10], [0, 0, 10, 10, 10], [0, 0, 0, 0, 0], [0, 0, 8, 8, 8]], [[0, 0, 0, 15, 15], [0, 0, 0, 15, 15], [0, 0, 0, 22, 22], [0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0], [7, 7, 7, 8, 8], [0, 0, 8, 8, 8], [0, 0, 0, 14, 14]], [[0, 7, 7, 8, 8], [0, 0, 0, 0, 0], [0, 8, 8, 8, 8], [0, 0, 0, 14, 14]], [[0, 0, 8, 8, 8], [0, 0, 8, 8, 8], [0, 0, 0, 0, 0], [0, 0, 14, 14, 14]], [[0, 0, 0, 14, 14], [0, 0, 0, 14, 14], [0, 0, 0, 14, 14], [0, 0, 0, 0, 0]]]]]

/-- W(2) as a table. -/
def tab2 (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (c : ℕ) : ℕ :=
  match q with
  | none => ((LN2.getD (r 0).val []).getD (r 1).val []).getD c 0
  | some p => ((((LS2.getD (p 0).val []).getD (p 1).val []).getD (r 0).val []).getD (r 1).val []).getD c 0

/-- W(3, none, r, c) for c <= 4, nested by the entries of r and then c. -/
def LN3 : List (List (List ℕ)) :=
  [[[0, 0, 0, 0, 0], [36, 36, 36, 72, 72], [0, 0, 72, 72, 72], [0, 0, 0, 72, 72]], [[0, 36, 36, 72, 72], [0, 0, 0, 0, 0], [0, 72, 72, 72, 72], [0, 0, 0, 72, 72]], [[0, 0, 72, 72, 72], [0, 0, 72, 72, 72], [0, 0, 0, 0, 0], [0, 0, 72, 72, 72]], [[0, 0, 0, 72, 72], [0, 0, 0, 72, 72], [0, 0, 0, 72, 72], [0, 0, 0, 0, 0]]]

/-- W(3, some p, r, c) for c <= 4, nested by the entries of p, of r, and then c. -/
def LS3 : List (List (List (List (List ℕ)))) :=
  [[[[[0, 0, 0, 0, 0], [22, 22, 22, 44, 44], [0, 0, 44, 44, 44], [0, 0, 0, 44, 44]], [[0, 22, 22, 44, 44], [0, 0, 0, 0, 0], [0, 28, 28, 28, 28], [0, 0, 0, 28, 28]], [[0, 0, 44, 44, 44], [0, 0, 28, 28, 28], [0, 0, 0, 0, 0], [0, 0, 28, 28, 28]], [[0, 0, 0, 44, 44], [0, 0, 0, 28, 28], [0, 0, 0, 28, 28], [0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0], [36, 36, 36, 72, 72], [0, 0, 50, 50, 50], [0, 0, 0, 50, 50]], [[0, 12, 12, 24, 24], [0, 0, 0, 0, 0], [0, 32, 32, 32, 32], [0, 0, 0, 32, 32]], [[0, 0, 32, 32, 32], [0, 0, 50, 50, 50], [0, 0, 0, 0, 0], [0, 0, 40, 40, 40]], [[0, 0, 0, 32, 32], [0, 0, 0, 50, 50], [0, 0, 0, 40, 40], [0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0], [26, 26, 26, 50, 50], [0, 0, 72, 72, 72], [0, 0, 0, 50, 50]], [[0, 22, 22, 32, 32], [0, 0, 0, 0, 0], [0, 50, 50, 50, 50], [0, 0, 0, 40, 40]], [[0, 0, 24, 24, 24], [0, 0, 32, 32, 32], [0, 0, 0, 0, 0], [0, 0, 32, 32, 32]], [[0, 0, 0, 32, 32], [0, 0, 0, 40, 40], [0, 0, 0, 50, 50], [0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0], [24, 24, 24, 50, 50], [0, 0, 50, 50, 50], [0, 0, 0, 72, 72]], [[0, 10, 10, 32, 32], [0, 0, 0, 0, 0], [0, 40, 40, 40, 40], [0, 0, 0, 50, 50]], [[0, 0, 32, 32, 32], [0, 0, 40, 40, 40], [0, 0, 0, 0, 0], [0, 0, 50, 50, 50]], [[0, 0, 0, 24, 24], [0, 0, 0, 32, 32], [0, 0, 0, 32, 32], [0, 0, 0, 0, 0]]]], [[[[0, 0, 0, 0, 0], [12, 12, 12, 24, 24], [0, 0, 32, 32, 32], [0, 0, 0, 32, 32]], [[0, 36, 36, 72, 72], [0, 0, 0, 0, 0], [0, 50, 50, 50, 50], [0, 0, 0, 50, 50]], [[0, 0, 50, 50, 50], [0, 0, 32, 32, 32], [0, 0, 0, 0, 0], [0, 0, 40, 40, 40]], [[0, 0, 0, 50, 50], [0, 0, 0, 32, 32], [0, 0, 0, 40, 40], [0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0], [22, 22, 22, 44, 44], [0, 0, 28, 28, 28], [0, 0, 0, 28, 28]], [[0, 22, 22, 44, 44], [0, 0, 0, 0, 0], [0, 44, 44, 44, 44], [0, 0, 0, 44, 44]], [[0, 0, 28, 28, 28], [0, 0, 44, 44, 44], [0, 0, 0, 0, 0], [0, 0, 28, 28, 28]], [[0, 0, 0, 28, 28], [0, 0, 0, 44, 44], [0, 0, 0, 28, 28], [0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0], [22, 22, 22, 32, 32], [0, 0, 50, 50, 50], [0, 0, 0, 40, 40]], [[0, 26, 26, 50, 50], [0, 0, 0, 0, 0], [0, 72, 72, 72, 72], [0, 0, 0, 50, 50]], [[0, 0, 32, 32, 32], [0, 0, 24, 24, 24], [0, 0, 0, 0, 0], [0, 0, 32, 32, 32]], [[0, 0, 0, 40, 40], [0, 0, 0, 32, 32], [0, 0, 0, 50, 50], [0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0], [10, 10, 10, 32, 32], [0, 0, 40, 40, 40], [0, 0, 0, 50, 50]], [[0, 24, 24, 50, 50], [0, 0, 0, 0, 0], [0, 50, 50, 50, 50], [0, 0, 0, 72, 72]], [[0, 0, 40, 40, 40], [0, 0, 32, 32, 32], [0, 0, 0, 0, 0], [0, 0, 50, 50, 50]], [[0, 0, 0, 32, 32], [0, 0, 0, 24, 24], [0, 0, 0, 32, 32], [0, 0, 0, 0, 0]]]], [[[[0, 0, 0, 0, 0], [10, 10, 10, 32, 32], [0, 0, 24, 24, 24], [0, 0, 0, 32, 32]], [[0, 14, 14, 50, 50], [0, 0, 0, 0, 0], [0, 32, 32, 32, 32], [0, 0, 0, 40, 40]], [[0, 0, 72, 72, 72], [0, 0, 50, 50, 50], [0, 0, 0, 0, 0], [0, 0, 50, 50, 50]], [[0, 0, 0, 50, 50], [0, 0, 0, 40, 40], [0, 0, 0, 32, 32], [0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0], [14, 14, 14, 50, 50], [0, 0, 32, 32, 32], [0, 0, 0, 40, 40]], [[0, 10, 10, 32, 32], [0, 0, 0, 0, 0], [0, 24, 24, 24, 24], [0, 0, 0, 32, 32]], [[0, 0, 50, 50, 50], [0, 0, 72, 72, 72], [0, 0, 0, 0, 0], [0, 0, 50, 50, 50]], [[0, 0, 0, 40, 40], [0, 0, 0, 50, 50], [0, 0, 0, 32, 32], [0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0], [4, 4, 4, 28, 28], [0, 0, 44, 44, 44], [0, 0, 0, 28, 28]], [[0, 4, 4, 28, 28], [0, 0, 0, 0, 0], [0, 44, 44, 44, 44], [0, 0, 0, 28, 28]], [[0, 0, 44, 44, 44], [0, 0, 44, 44, 44], [0, 0, 0, 0, 0], [0, 0, 44, 44, 44]], [[0, 0, 0, 28, 28], [0, 0, 0, 28, 28], [0, 0, 0, 44, 44], [0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0], [14, 14, 14, 40, 40], [0, 0, 32, 32, 32], [0, 0, 0, 50, 50]], [[0, 14, 14, 40, 40], [0, 0, 0, 0, 0], [0, 32, 32, 32, 32], [0, 0, 0, 50, 50]], [[0, 0, 50, 50, 50], [0, 0, 50, 50, 50], [0, 0, 0, 0, 0], [0, 0, 72, 72, 72]], [[0, 0, 0, 32, 32], [0, 0, 0, 32, 32], [0, 0, 0, 24, 24], [0, 0, 0, 0, 0]]]], [[[[0, 0, 0, 0, 0], [22, 22, 22, 32, 32], [0, 0, 32, 32, 32], [0, 0, 0, 24, 24]], [[0, 36, 36, 50, 50], [0, 0, 0, 0, 0], [0, 40, 40, 40, 40], [0, 0, 0, 32, 32]], [[0, 0, 50, 50, 50], [0, 0, 40, 40, 40], [0, 0, 0, 0, 0], [0, 0, 32, 32, 32]], [[0, 0, 0, 72, 72], [0, 0, 0, 50, 50], [0, 0, 0, 50, 50], [0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0], [36, 36, 36, 50, 50], [0, 0, 40, 40, 40], [0, 0, 0, 32, 32]], [[0, 22, 22, 32, 32], [0, 0, 0, 0, 0], [0, 32, 32, 32, 32], [0, 0, 0, 24, 24]], [[0, 0, 40, 40, 40], [0, 0, 50, 50, 50], [0, 0, 0, 0, 0], [0, 0, 32, 32, 32]], [[0, 0, 0, 50, 50], [0, 0, 0, 72, 72], [0, 0, 0, 50, 50], [0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0], [26, 26, 26, 40, 40], [0, 0, 50, 50, 50], [0, 0, 0, 32, 32]], [[0, 26, 26, 40, 40], [0, 0, 0, 0, 0], [0, 50, 50, 50, 50], [0, 0, 0, 32, 32]], [[0, 0, 32, 32, 32], [0, 0, 32, 32, 32], [0, 0, 0, 0, 0], [0, 0, 24, 24, 24]], [[0, 0, 0, 50, 50], [0, 0, 0, 50, 50], [0, 0, 0, 72, 72], [0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0], [24, 24, 24, 28, 28], [0, 0, 28, 28, 28], [0, 0, 0, 44, 44]], [[0, 24, 24, 28, 28], [0, 0, 0, 0, 0], [0, 28, 28, 28, 28], [0, 0, 0, 44, 44]], [[0, 0, 28, 28, 28], [0, 0, 28, 28, 28], [0, 0, 0, 0, 0], [0, 0, 44, 44, 44]], [[0, 0, 0, 44, 44], [0, 0, 0, 44, 44], [0, 0, 0, 44, 44], [0, 0, 0, 0, 0]]]]]

/-- W(3) as a table. -/
def tab3 (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (c : ℕ) : ℕ :=
  match q with
  | none => ((LN3.getD (r 0).val []).getD (r 1).val []).getD c 0
  | some p => ((((LS3.getD (p 0).val []).getD (p 1).val []).getD (r 0).val []).getD (r 1).val []).getD c 0

lemma checkN1 : ∀ y1 y2 : Fin 4, ∀ c : Fin 5,
    T W0f none ![y1, y2] c.val = tab1 none ![y1, y2] c.val := by
  decide +kernel

lemma checkS1 : ∀ p1 p2 : Fin 4, ∀ y1 y2 : Fin 4, ∀ c : Fin 5, (p1.val < c.val ∧ p2.val < c.val) →
    T W0f (some ![p1, p2]) ![y1, y2] c.val = tab1 (some ![p1, p2]) ![y1, y2] c.val := by
  decide +kernel

lemma checkN2 : ∀ y1 y2 : Fin 4, ∀ c : Fin 5,
    T tab1 none ![y1, y2] c.val = tab2 none ![y1, y2] c.val := by
  decide +kernel

lemma checkS2 : ∀ p1 p2 : Fin 4, ∀ y1 y2 : Fin 4, ∀ c : Fin 5, (p1.val < c.val ∧ p2.val < c.val) →
    T tab1 (some ![p1, p2]) ![y1, y2] c.val = tab2 (some ![p1, p2]) ![y1, y2] c.val := by
  decide +kernel

lemma checkN3 : ∀ y1 y2 : Fin 4, ∀ c : Fin 5,
    T tab2 none ![y1, y2] c.val = tab3 none ![y1, y2] c.val := by
  decide +kernel

lemma checkS3 : ∀ p1 p2 : Fin 4, ∀ y1 y2 : Fin 4, ∀ c : Fin 5, (p1.val < c.val ∧ p2.val < c.val) →
    T tab2 (some ![p1, p2]) ![y1, y2] c.val = tab3 (some ![p1, p2]) ![y1, y2] c.val := by
  decide +kernel

lemma checkN_rel : ∀ y1 y2 : Fin 4, ∀ c : Fin 5,
    T tab3 none ![y1, y2] c.val =
      2 * tab3 none ![y1, y2] c.val + 4 * tab2 none ![y1, y2] c.val := by
  decide +kernel

lemma checkS_rel : ∀ p1 p2 : Fin 4, ∀ y1 y2 : Fin 4, ∀ c : Fin 5, (p1.val < c.val ∧ p2.val < c.val) →
    T tab3 (some ![p1, p2]) ![y1, y2] c.val =
      2 * tab3 (some ![p1, p2]) ![y1, y2] c.val + 4 * tab2 (some ![p1, p2]) ![y1, y2] c.val := by
  decide +kernel

lemma W_1 (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (c : ℕ) (hc : c ≤ 4)
    (hq : ∀ p, q = some p → ∀ j, (p j).val < c) :
    W 1 q r c = tab1 q r c := by
  rw [W_succT _ q r c hc,
    T_congr _ W0f q r c (fun s => W_zero' _ s _ (newcB_le c hc r))]
  rcases q with _ | p
  · rw [row_eta r]
    exact checkN1 (r 0) (r 1) ⟨c, by omega⟩
  · rw [row_eta p, row_eta r]
    exact checkS1 (p 0) (p 1) (r 0) (r 1) ⟨c, by omega⟩ ⟨hq p rfl 0, hq p rfl 1⟩

lemma W_2 (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (c : ℕ) (hc : c ≤ 4)
    (hq : ∀ p, q = some p → ∀ j, (p j).val < c) :
    W 2 q r c = tab2 q r c := by
  rw [show W 2 q r c = W (1 + 1) q r c from rfl, W_succT _ q r c hc,
    T_congr _ tab1 q r c
      (fun s => W_1 _ s _ (newcB_le c hc r) (inv_next c hc r))]
  rcases q with _ | p
  · rw [row_eta r]
    exact checkN2 (r 0) (r 1) ⟨c, by omega⟩
  · rw [row_eta p, row_eta r]
    exact checkS2 (p 0) (p 1) (r 0) (r 1) ⟨c, by omega⟩ ⟨hq p rfl 0, hq p rfl 1⟩

lemma W_3 (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (c : ℕ) (hc : c ≤ 4)
    (hq : ∀ p, q = some p → ∀ j, (p j).val < c) :
    W 3 q r c = tab3 q r c := by
  rw [show W 3 q r c = W (2 + 1) q r c from rfl, W_succT _ q r c hc,
    T_congr _ tab2 q r c
      (fun s => W_2 _ s _ (newcB_le c hc r) (inv_next c hc r))]
  rcases q with _ | p
  · rw [row_eta r]
    exact checkN3 (r 0) (r 1) ⟨c, by omega⟩
  · rw [row_eta p, row_eta r]
    exact checkS3 (p 0) (p 1) (r 0) (r 1) ⟨c, by omega⟩ ⟨hq p rfl 0, hq p rfl 1⟩

lemma W_rec (n : ℕ) : ∀ (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (c : ℕ), c ≤ 4 →
    (∀ p, q = some p → ∀ j, (p j).val < c) →
    W (n + 4) q r c = 2 * W (n + 3) q r c + 4 * W (n + 2) q r c := by
  induction n with
  | zero =>
    intro q r c hc hq
    rw [show W (0 + 4) q r c = W (3 + 1) q r c from rfl, W_succT 3 q r c hc,
      T_congr _ tab3 q r c
        (fun s => W_3 _ s _ (newcB_le c hc r) (inv_next c hc r)),
      show W (0 + 2) q r c = W 2 q r c from rfl, W_2 q r c hc hq,
      show W (0 + 3) q r c = W 3 q r c from rfl, W_3 q r c hc hq]
    rcases q with _ | p
    · rw [row_eta r]
      exact checkN_rel (r 0) (r 1) ⟨c, by omega⟩
    · rw [row_eta p, row_eta r]
      exact checkS_rel (p 0) (p 1) (r 0) (r 1) ⟨c, by omega⟩ ⟨hq p rfl 0, hq p rfl 1⟩
  | succ n ih =>
    intro q r c hc hq
    rw [W_succT (n + 4) q r c hc, W_succT (n + 3) q r c hc, W_succT (n + 2) q r c hc]
    unfold T
    split_ifs with h
    · rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      split_ifs
      · exact ih _ _ _ (newcB_le c hc r) (inv_next c hc r)
      · simp
    · simp

lemma a_eq (n : ℕ) : a (n + 1) = ∑ r : Fin 2 → Fin 4, W (n) none r 0 := by
  unfold a W
  rw [Finset.card_eq_sum_card_fiberwise (f := fun f => f 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Finset.filter_filter]
  refine congrArg Finset.card (Finset.filter_congr (fun f _ => ?_))
  rw [cond_iff, rmn_iff, and_assoc]

lemma a_rec (n : ℕ) : a (n + 5) = 2 * a (n + 4) + 4 * a (n + 3) := by
  rw [a_eq, a_eq, a_eq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  exact W_rec n none r 0 (by norm_num) (fun _ h => by cases h)

lemma a_one : a 1 = 1 := by
  rw [a_eq 0, sum_row]
  simp only [W_zero]
  decide +kernel

lemma a_two : a 2 = 4 := by
  have h : ∀ r, W 1 none r 0 = tab1 none r 0 := fun r => W_1 none r 0 (by norm_num) (fun _ h => by cases h)
  rw [a_eq 1, sum_row]
  simp only [h]
  decide +kernel

lemma a_three : a 3 = 11 := by
  have h : ∀ r, W 2 none r 0 = tab2 none r 0 := fun r => W_2 none r 0 (by norm_num) (fun _ h => by cases h)
  rw [a_eq 2, sum_row]
  simp only [h]
  decide +kernel

lemma a_four : a 4 = 36 := by
  have h : ∀ r, W 3 none r 0 = tab3 none r 0 := fun r => W_3 none r 0 (by norm_num) (fun _ h => by cases h)
  rw [a_eq 3, sum_row]
  simp only [h]
  decide +kernel

/-- Barker's g.f.: Sum_{n >= 1} a(n) x^n = x(1 - x)(1 + x)(1 + 2x) / (1 - 2x - 4x^2). -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    (1 - 2 * X - 4 * X ^ 2) = X * (1 - X) * (1 + X) * (1 + 2 * X) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - 2 * X - 4 * X ^ 2) = A - A * X ^ 1 * C 2 - A * X ^ 2 * C 4 := by
    rw [show (C (2 : ℚ) : ℚ⟦X⟧) = 2 from map_ofNat C 2,
      show (C (4 : ℚ) : ℚ⟦X⟧) = 4 from map_ofNat C 4]
    ring
  have e2 : (X * (1 - X) * (1 + X) * (1 + 2 * X) : ℚ⟦X⟧) = X ^ 1 * C 1 + X ^ 2 * C 2 - X ^ 3 * C 1 - X ^ 4 * C 2 := by
    rw [show (C (1 : ℚ) : ℚ⟦X⟧) = 1 from map_one C,
      show (C (2 : ℚ) : ℚ⟦X⟧) = 2 from map_ofNat C 2]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk]
  rcases n with _ | _ | _ | _ | _ | n
  · simp
  · simp [a_one] <;> norm_num
  · simp [a_one, a_two] <;> norm_num
  · simp [a_one, a_two, a_three] <;> norm_num
  · simp [a_one, a_two, a_three, a_four] <;> norm_num
  · have h := a_rec n
    
    have hq : (a (n + 5) : ℚ) = 2 * (a (n + 4) : ℚ) + 4 * (a (n + 3) : ℚ) := by exact_mod_cast h
    simp only [show ¬ (n + 5 = 0) by omega,
      if_false,
      if_true,
      show 1 ≤ n + 5 by omega,
      show n + 5 - 1 = n + 4 by omega,
      show ¬ (n + 4 = 0) by omega,
      show 2 ≤ n + 5 by omega,
      show n + 5 - 2 = n + 3 by omega,
      show ¬ (n + 3 = 0) by omega,
      show ¬ (n + 5 = 1) by omega,
      show ¬ (n + 5 = 2) by omega,
      show ¬ (n + 5 = 3) by omega,
      show ¬ (n + 5 = 4) by omega]
    linear_combination hq

theorem cf (b : ℕ → ℕ) (h3 : b 3 = 11) (h4 : b 4 = 36)
    (hr : ∀ n, b (n + 5) = 2 * b (n + 4) + 4 * b (n + 3)) :
    ∀ n : ℕ, 2 < n → (b n : ℝ) =
      ((1 - Real.sqrt 5) ^ n * (-5 + 3 * Real.sqrt 5) +
        (1 + Real.sqrt 5) ^ n * (5 + 3 * Real.sqrt 5)) / (16 * Real.sqrt 5) := by
  have s2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  set s := Real.sqrt 5 with hsdef
  set G : ℕ → ℝ := fun n => (1 - s) ^ n * (-5 + 3 * s) + (1 + s) ^ n * (5 + 3 * s) with hG
  have Grec : ∀ n, G (n + 2) = 2 * G (n + 1) + 4 * G n := by
    intro n
    simp only [hG]
    have e1 : (1 - s) ^ 2 = 2 * (1 - s) + 4 := by linear_combination s2
    have e2 : (1 + s) ^ 2 = 2 * (1 + s) + 4 := by linear_combination s2
    rw [show (1 - s) ^ (n + 2) = (1 - s) ^ n * (1 - s) ^ 2 by ring,
      show (1 + s) ^ (n + 2) = (1 + s) ^ n * (1 + s) ^ 2 by ring, e1, e2]
    ring
  have G0 : G 0 = 6 * s := by simp only [hG]; ring
  have G1 : G 1 = 16 * s := by simp only [hG]; linear_combination 0 * s2
  have G2 : G 2 = 56 * s := by
    rw [show G 2 = G (0 + 2) from rfl, Grec, show G (0 + 1) = G 1 from rfl, G1, G0]; ring
  have G3 : G 3 = 176 * s := by
    rw [show G 3 = G (1 + 2) from rfl, Grec, show G (1 + 1) = G 2 from rfl, G2, G1]; ring
  have G4 : G 4 = 576 * s := by
    rw [show G 4 = G (2 + 2) from rfl, Grec, show G (2 + 1) = G 3 from rfl, G3, G2]; ring
  have key : ∀ k, (b (k + 3) : ℝ) * (16 * s) = G (k + 3) ∧
      (b (k + 4) : ℝ) * (16 * s) = G (k + 4) := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [h3, G3]; push_cast; ring
      · rw [h4, G4]; push_cast; ring
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have h := hr k
      have hq : ((b (k + 5) : ℕ) : ℝ) = 2 * b (k + 4) + 4 * b (k + 3) := by exact_mod_cast h
      have hg := Grec (k + 3)
      rw [show k + 3 + 2 = k + 5 from rfl, show k + 3 + 1 = k + 4 from rfl] at hg
      rw [show k + 1 + 4 = k + 5 from rfl, hg]
      linear_combination (16 * s) * hq + 2 * ih.2 + 4 * ih.1
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  rw [eq_div_iff (mul_ne_zero (by norm_num) hs.ne')]
  exact (key k).1

/-- Barker's closed form. -/
theorem closed_form : ∀ n : ℕ, 2 < n → (a n : ℝ) =
      ((1 - Real.sqrt 5) ^ n * (-5 + 3 * Real.sqrt 5) +
        (1 + Real.sqrt 5) ^ n * (5 + 3 * Real.sqrt 5)) / (16 * Real.sqrt 5) :=
  cf a a_three a_four a_rec

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - 2 * X - 4 * X ^ 2) = X * (1 - X) * (1 + X) * (1 + 2 * X) ∧
    ∀ n : ℕ, 2 < n → (a n : ℝ) =
      ((1 - Real.sqrt 5) ^ n * (-5 + 3 * Real.sqrt 5) +
        (1 + Real.sqrt 5) ^ n * (5 + 3 * Real.sqrt 5)) / (16 * Real.sqrt 5) :=
  ⟨gf, closed_form⟩

/-- Controls: the entry's terms a(1..10), from the recurrence and the first values. -/
theorem controls : a 1 = 1 ∧ a 2 = 4 ∧ a 3 = 11 ∧ a 4 = 36 ∧ a 5 = 116 ∧ a 6 = 376 ∧ a 7 = 1216 ∧ a 8 = 3936 ∧ a 9 = 12736 ∧ a 10 = 41216 := by
  have r0 := a_rec 0; have r1 := a_rec 1; have r2 := a_rec 2; have r3 := a_rec 3; have r4 := a_rec 4; have r5 := a_rec 5
  have h1 := a_one; have h2 := a_two; have h3 := a_three; have h4 := a_four
  norm_num at r0 r1 r2 r3 r4 r5
  omega

end OMA.S_oeis_a206687

theorem OMA.solution : type_of% @OMA.S_oeis_a206687.main :=
  OMA.S_oeis_a206687.conjecture
