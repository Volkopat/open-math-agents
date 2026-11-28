import OMAStatements.S_oeis_a208086

namespace OMA.S_oeis_a208086

open PowerSeries Finset


instance {R C K : ℕ} : DecidablePred (@RowMajorNew R C K) := fun x => by
  unfold RowMajorNew; infer_instance



instance {R C K : ℕ} : DecidablePred (@Cond R C K) := fun x => by
  unfold Cond; infer_instance


/-! ## Rows -/

/-- edgeNum of the subblock in columns i, i' of the rows r above t. -/
def enR (r t : Fin 4 → Fin 2) (i i' : Fin 4) : ℕ :=
  (if r i = r i' then 1 else 0) + (if t i = t i' then 1 else 0) +
    (if r i = t i then 1 else 0) + (if r i' = t i' then 1 else 0)

/-- The subblocks between r and the row s below it, if any, differ from their horizontal
neighbors. -/
def okBelow (r : Fin 4 → Fin 2) (s : Option (Fin 4 → Fin 2)) : Prop :=
  match s with
  | none => True
  | some t => ∀ i i' i'' : Fin 4, i'.val = i.val + 1 → i''.val = i'.val + 1 →
      enR r t i i' ≠ enR r t i' i''

/-- The subblocks between q and r equal the ones below them, between r and s. -/
def okVert (q : Option (Fin 4 → Fin 2)) (r : Fin 4 → Fin 2) (s : Option (Fin 4 → Fin 2)) : Prop :=
  match q, s with
  | some p, some t => ∀ i i' : Fin 4, i'.val = i.val + 1 → enR p r i i' = enR r t i i'
  | _, _ => True

/-- The condition on the row r with the row q above it and the row s below it. -/
def rowCond (q : Option (Fin 4 → Fin 2)) (r : Fin 4 → Fin 2) (s : Option (Fin 4 → Fin 2)) : Prop :=
  okBelow r s ∧ okVert q r s

instance (r : Fin 4 → Fin 2) (s : Option (Fin 4 → Fin 2)) : Decidable (okBelow r s) := by
  unfold okBelow; split <;> infer_instance

instance (q : Option (Fin 4 → Fin 2)) (r : Fin 4 → Fin 2) (s : Option (Fin 4 → Fin 2)) : Decidable (okVert q r s) := by
  unfold okVert; split <;> infer_instance

instance (q : Option (Fin 4 → Fin 2)) (r : Fin 4 → Fin 2) (s : Option (Fin 4 → Fin 2)) : Decidable (rowCond q r s) := by
  unfold rowCond; infer_instance

/-- The condition of the transposed array y, whose rows are the columns of x: vertically
neighboring subblocks have equal numbers and horizontally neighboring ones different numbers. -/
def CondT {R : ℕ} (y : Fin R → Fin 4 → Fin 2) : Prop :=
  (∀ j j' : Fin R, j'.val = j.val + 1 → ∀ i i' i'' : Fin 4, i'.val = i.val + 1 →
      i''.val = i'.val + 1 → enR (y j) (y j') i i' ≠ enR (y j) (y j') i' i'') ∧
    ∀ j j' j'' : Fin R, j'.val = j.val + 1 → j''.val = j'.val + 1 → ∀ i i' : Fin 4,
      i'.val = i.val + 1 → enR (y j) (y j') i i' = enR (y j') (y j'') i i'

instance {R : ℕ} : DecidablePred (@CondT R) := fun y => by unfold CondT; infer_instance

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
def prevRow {n : ℕ} (q : Option (Fin 4 → Fin 2)) (g : Fin n → Fin 4 → Fin 2) (i : Fin n) : Option (Fin 4 → Fin 2) :=
  match i with
  | ⟨0, _⟩ => q
  | ⟨k + 1, h⟩ => some (g ⟨k, Nat.lt_of_succ_lt h⟩)

/-- The row below row i of g, none for the last row. -/
def nextRow {n : ℕ} (g : Fin n → Fin 4 → Fin 2) (i : Fin n) : Option (Fin 4 → Fin 2) :=
  if h : i.val + 1 < n then some (g ⟨i.val + 1, h⟩) else none

/-- Every row of g satisfies the condition with the rows above and below it; q is the row above
the first row. -/
def ValidFrom {n : ℕ} (q : Option (Fin 4 → Fin 2)) (g : Fin n → Fin 4 → Fin 2) : Prop :=
  ∀ i, rowCond (prevRow q g i) (g i) (nextRow g i)

instance {n : ℕ} (q : Option (Fin 4 → Fin 2)) : DecidablePred (@ValidFrom n q) := fun g => by
  unfold ValidFrom; infer_instance

lemma validFrom_one (q : Option (Fin 4 → Fin 2)) (g : Fin 1 → Fin 4 → Fin 2) :
    ValidFrom q g ↔ rowCond q (g 0) none := by
  constructor
  · intro h
    exact h 0
  · intro h i
    have hi : i = 0 := Fin.fin_one_eq_zero i
    subst hi
    exact h

lemma prevRow_cons_zero {n : ℕ} (q : Option (Fin 4 → Fin 2)) (r : Fin 4 → Fin 2) (h : Fin (n + 1) → Fin 4 → Fin 2) :
    prevRow q (Fin.cons r h : Fin (n + 2) → Fin 4 → Fin 2) 0 = q := rfl

lemma prevRow_cons_succ {n : ℕ} (q : Option (Fin 4 → Fin 2)) (r : Fin 4 → Fin 2) (h : Fin (n + 1) → Fin 4 → Fin 2)
    (k : Fin (n + 1)) :
    prevRow q (Fin.cons r h : Fin (n + 2) → Fin 4 → Fin 2) k.succ = prevRow (some r) h k := by
  rcases k with ⟨_ | j, hk⟩ <;> rfl

lemma nextRow_cons_zero {n : ℕ} (r : Fin 4 → Fin 2) (h : Fin (n + 1) → Fin 4 → Fin 2) :
    nextRow (Fin.cons r h : Fin (n + 2) → Fin 4 → Fin 2) 0 = some (h 0) := by
  unfold nextRow
  rw [dif_pos (by simp)]
  rfl

lemma nextRow_cons_succ {n : ℕ} (r : Fin 4 → Fin 2) (h : Fin (n + 1) → Fin 4 → Fin 2) (k : Fin (n + 1)) :
    nextRow (Fin.cons r h : Fin (n + 2) → Fin 4 → Fin 2) k.succ = nextRow h k := by
  unfold nextRow
  by_cases hk : k.val + 1 < n + 1
  · rw [dif_pos (by simp; omega), dif_pos hk]
    rfl
  · rw [dif_neg (by simp; omega), dif_neg hk]

lemma validFrom_cons {n : ℕ} (q : Option (Fin 4 → Fin 2)) (r : Fin 4 → Fin 2) (h : Fin (n + 1) → Fin 4 → Fin 2) :
    ValidFrom q (Fin.cons r h : Fin (n + 2) → Fin 4 → Fin 2) ↔
      rowCond q r (some (h 0)) ∧ ValidFrom (some r) h := by
  unfold ValidFrom
  rw [Fin.forall_fin_succ]
  simp only [prevRow_cons_zero, prevRow_cons_succ, nextRow_cons_zero, nextRow_cons_succ,
    Fin.cons_zero, Fin.cons_succ]

/-! ## Counting by the first row -/

/-- W(n, q, r, c): arrays with n + 1 rows, first row r with the row q above it, every row
satisfying the condition, values introduced in row major order after the values below c. -/
def W (n : ℕ) (q : Option (Fin 4 → Fin 2)) (r : Fin 4 → Fin 2) (c : ℕ) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 4 → Fin 2)).filter
    (fun g => ValidFrom q g ∧ RGSfrom c g ∧ g 0 = r)).card

lemma W_zero (q : Option (Fin 4 → Fin 2)) (r : Fin 4 → Fin 2) (c : ℕ) :
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
def consEmb (n : ℕ) (r : Fin 4 → Fin 2) :
    (Fin (n + 1) → Fin 4 → Fin 2) ↪ (Fin (n + 2) → Fin 4 → Fin 2) where
  toFun g := Fin.cons r g
  inj' g g' h := by
    funext i
    have := congrFun h i.succ
    simpa using this

lemma consEmb_apply (n : ℕ) (r : Fin 4 → Fin 2) (g : Fin (n + 1) → Fin 4 → Fin 2) :
    consEmb n r g = Fin.cons r g := rfl

lemma W_succ (n : ℕ) (q : Option (Fin 4 → Fin 2)) (r : Fin 4 → Fin 2) (c : ℕ) :
    W (n + 1) q r c = if rowRgs c r then
      ∑ s : Fin 4 → Fin 2, (if rowCond q r (some s) then W n (some r) s (newc c r) else 0) else 0 := by
  have e : ((univ : Finset (Fin (n + 2) → Fin 4 → Fin 2)).filter
      (fun f => ValidFrom q f ∧ RGSfrom c f ∧ f 0 = r)) =
      (((univ : Finset (Fin (n + 1) → Fin 4 → Fin 2)).filter
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

lemma nextRow_eq {R : ℕ} (x : Fin R → Fin 4 → Fin 2) (i i' : Fin R) (h : i'.val = i.val + 1) :
    nextRow x i = some (x i') := by
  unfold nextRow
  rw [dif_pos (by omega)]
  have e : (⟨i.val + 1, by omega⟩ : Fin R) = i' := Fin.ext h.symm
  rw [e]

lemma nextRow_none {R : ℕ} (x : Fin R → Fin 4 → Fin 2) (i : Fin R) (h : ¬ i.val + 1 < R) :
    nextRow x i = none := by
  unfold nextRow
  rw [dif_neg h]

lemma prevRow_eq {R : ℕ} (q : Option (Fin 4 → Fin 2)) (x : Fin R → Fin 4 → Fin 2) (i i' : Fin R)
    (h : i.val = i'.val + 1) : prevRow q x i = some (x i') := by
  rcases i with ⟨_ | k, hi⟩
  · simp at h
  · have e : (⟨k, Nat.lt_of_succ_lt hi⟩ : Fin R) = i' := Fin.ext (by simp only [Fin.val_mk] at h ⊢; omega)
    show some (x ⟨k, Nat.lt_of_succ_lt hi⟩) = some (x i')
    rw [e]

lemma edge_T {C : ℕ} (x : Fin 4 → Fin C → Fin 2) (i i' : Fin 4) (j j' : Fin C) :
    edgeNum x i i' j j' = enR (fun a => x a j) (fun a => x a j') i i' := by
  unfold edgeNum enR
  ring

lemma condT_iff {C : ℕ} (x : Fin 4 → Fin C → Fin 2) : Cond x ↔ CondT (fun j i => x i j) := by
  unfold Cond CondT
  simp only [edge_T]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun j j' hj i i' i'' hi hi' => h2 i i' i'' j j' hi hi' hj,
      fun j j' j'' hj hj' i i' hi => h1 i i' j j' j'' hi hj hj'⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i i' j j' j'' hi hj hj' => h2 j j' j'' hj hj' i i' hi,
      fun i i' i'' j j' hi hi' hj => h1 j j' hj i i' i'' hi hi'⟩

lemma two_ne (v : Fin 2) (h : v ≠ 0) : v = 1 := by
  revert v h
  decide

lemma two_lt (u v : Fin 2) (h : u < v) : u = 0 ∧ v = 1 := by
  revert u v h
  decide

lemma rmn_two {R C : ℕ} (x : Fin R → Fin C → Fin 2) (h0 : 0 < R) (h1 : 0 < C) :
    RowMajorNew x ↔ x ⟨0, h0⟩ ⟨0, h1⟩ = 0 := by
  constructor
  · intro H
    by_contra hne
    have h1' := two_ne _ hne
    obtain ⟨i', j', hb, _⟩ := H ⟨0, h0⟩ ⟨0, h1⟩ 0 (by rw [h1']; decide)
    rcases hb with hb | ⟨_, hb⟩
    · exact absurd hb (by simp [Fin.lt_def])
    · exact absurd hb (by simp [Fin.lt_def])
  · intro H i j u hu
    obtain ⟨rfl, hv⟩ := two_lt u (x i j) hu
    refine ⟨⟨0, h0⟩, ⟨0, h1⟩, ?_, H⟩
    by_cases hi : i.val = 0
    · right
      refine ⟨Fin.ext hi.symm, ?_⟩
      show 0 < j.val
      by_contra hj
      have e1 : i = ⟨0, h0⟩ := Fin.ext hi
      have e2 : j = ⟨0, h1⟩ := Fin.ext (by omega)
      rw [e1, e2, H] at hv
      exact absurd hv (by decide)
    · left
      show 0 < i.val
      omega

lemma cond_iff {R : ℕ} (y : Fin R → Fin 4 → Fin 2) : CondT y ↔ ValidFrom none y := by
  unfold CondT ValidFrom rowCond
  constructor
  · rintro ⟨Hh, Hv⟩ i
    refine ⟨?_, ?_⟩
    · by_cases hlt : i.val + 1 < R
      · rw [nextRow_eq y i ⟨i.val + 1, hlt⟩ rfl]
        intro j j' j'' h1 h2
        exact Hh i ⟨i.val + 1, hlt⟩ rfl j j' j'' h1 h2
      · rw [nextRow_none y i hlt]
        trivial
    · rcases i with ⟨_ | k, hi⟩
      · trivial
      · by_cases hlt : k + 1 + 1 < R
        · rw [prevRow_eq none y ⟨k + 1, hi⟩ ⟨k, by omega⟩ rfl,
            nextRow_eq y ⟨k + 1, hi⟩ ⟨k + 1 + 1, hlt⟩ rfl]
          intro j j' h1
          exact Hv ⟨k, by omega⟩ ⟨k + 1, hi⟩ ⟨k + 1 + 1, hlt⟩ rfl rfl j j' h1
        · rw [nextRow_none y ⟨k + 1, hi⟩ hlt]
          cases prevRow none y ⟨k + 1, hi⟩ <;> trivial
  · intro V
    refine ⟨fun i i' hi j j' j'' h1 h2 => ?_, fun i i' i'' hi hi' j j' h1 => ?_⟩
    · have hb := (V i).1
      rw [nextRow_eq y i i' hi] at hb
      exact hb j j' j'' h1 h2
    · have hb := (V i').2
      rw [prevRow_eq none y i' i hi, nextRow_eq y i' i'' hi'] at hb
      exact hb j j' h1

/-! ## Kernel form of the transfer -/

lemma sum_cons {m : ℕ} (f : (Fin (m + 1) → Fin 2) → ℕ) :
    ∑ s : Fin (m + 1) → Fin 2, f s = ∑ x : Fin 2, ∑ t : Fin m → Fin 2, f (Fin.cons x t) := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 2).symm _ _
    (fun s => by simp [Fin.consEquiv, Fin.cons_self_tail])

lemma sum_row (f : (Fin 4 → Fin 2) → ℕ) :
    ∑ s : Fin 4 → Fin 2, f s = ∑ x : Fin 2, ∑ y : Fin 2, ∑ z : Fin 2, ∑ u : Fin 2, f ![x, y, z, u] := by
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Fintype.sum_unique]
  exact congrArg f (by funext j; fin_cases j <;> rfl)

lemma row_eta (r : Fin 4 → Fin 2) : r = ![r 0, r 1, r 2, r 3] := by
  funext j
  fin_cases j <;> rfl

/-! Fast Boolean forms of the conditions for the kernel checks, tied to the definitions by
`decide` over all small cases. -/

/-- `rowRgs c r` as a Boolean. -/
def rgsB (c : ℕ) (r : Fin 4 → Fin 2) : Bool :=
  decide ((r 0).val ≤ c) &&
    decide ((r 1).val ≤ max c ((r 0).val + 1)) &&
    decide ((r 2).val ≤ max (max c ((r 0).val + 1)) ((r 1).val + 1)) &&
    decide ((r 3).val ≤ max (max (max c ((r 0).val + 1)) ((r 1).val + 1)) ((r 2).val + 1))

/-- `newc c r` by explicit maxima. -/
def newcB (c : ℕ) (r : Fin 4 → Fin 2) : ℕ :=
  max (max (max (max c ((r 0).val + 1)) ((r 1).val + 1)) ((r 2).val + 1)) ((r 3).val + 1)

/-- `rowCond q r (some t)` as a Boolean. -/
def condB (q : Option (Fin 4 → Fin 2)) (r t : Fin 4 → Fin 2) : Bool :=
  (((if r 0 = r 1 then 1 else 0) + (if t 0 = t 1 then 1 else 0) + (if r 0 = t 0 then 1 else 0) + (if r 1 = t 1 then 1 else 0)) != ((if r 1 = r 2 then 1 else 0) + (if t 1 = t 2 then 1 else 0) + (if r 1 = t 1 then 1 else 0) + (if r 2 = t 2 then 1 else 0))) &&
    (((if r 1 = r 2 then 1 else 0) + (if t 1 = t 2 then 1 else 0) + (if r 1 = t 1 then 1 else 0) + (if r 2 = t 2 then 1 else 0)) != ((if r 2 = r 3 then 1 else 0) + (if t 2 = t 3 then 1 else 0) + (if r 2 = t 2 then 1 else 0) + (if r 3 = t 3 then 1 else 0))) &&
    (match q with
    | none => true
    | some p =>
      (((if p 0 = p 1 then 1 else 0) + (if r 0 = r 1 then 1 else 0) + (if p 0 = r 0 then 1 else 0) + (if p 1 = r 1 then 1 else 0)) == ((if r 0 = r 1 then 1 else 0) + (if t 0 = t 1 then 1 else 0) + (if r 0 = t 0 then 1 else 0) + (if r 1 = t 1 then 1 else 0))) &&
      (((if p 1 = p 2 then 1 else 0) + (if r 1 = r 2 then 1 else 0) + (if p 1 = r 1 then 1 else 0) + (if p 2 = r 2 then 1 else 0)) == ((if r 1 = r 2 then 1 else 0) + (if t 1 = t 2 then 1 else 0) + (if r 1 = t 1 then 1 else 0) + (if r 2 = t 2 then 1 else 0))) &&
      (((if p 2 = p 3 then 1 else 0) + (if r 2 = r 3 then 1 else 0) + (if p 2 = r 2 then 1 else 0) + (if p 3 = r 3 then 1 else 0)) == ((if r 2 = r 3 then 1 else 0) + (if t 2 = t 3 then 1 else 0) + (if r 2 = t 2 then 1 else 0) + (if r 3 = t 3 then 1 else 0))))

/-- `rowCond q r none` as a Boolean. -/
def endB (q : Option (Fin 4 → Fin 2)) (r : Fin 4 → Fin 2) : Bool :=
  true

lemma rgsB_eq : ∀ c : Fin 3, ∀ y1 y2 y3 y4 : Fin 2,
    decide (rowRgs c.val ![y1, y2, y3, y4]) = rgsB c.val ![y1, y2, y3, y4] := by
  decide +kernel

lemma newcB_eq : ∀ c : Fin 3, ∀ y1 y2 y3 y4 : Fin 2,
    newc c.val ![y1, y2, y3, y4] = newcB c.val ![y1, y2, y3, y4] := by
  decide +kernel

lemma condB_eqN : ∀ y1 y2 y3 y4 x y z u : Fin 2,
    decide (rowCond none ![y1, y2, y3, y4] (some ![x, y, z, u])) = condB none ![y1, y2, y3, y4] ![x, y, z, u] := by
  decide +kernel

lemma condB_eqS : ∀ p1 p2 p3 p4 y1 y2 y3 y4 x y z u : Fin 2,
    decide (rowCond (some ![p1, p2, p3, p4]) ![y1, y2, y3, y4] (some ![x, y, z, u])) =
      condB (some ![p1, p2, p3, p4]) ![y1, y2, y3, y4] ![x, y, z, u] := by
  decide +kernel

lemma endB_eqN : ∀ y1 y2 y3 y4 : Fin 2,
    decide (rowCond none ![y1, y2, y3, y4] none) = endB none ![y1, y2, y3, y4] := by
  decide +kernel

lemma endB_eqS : ∀ p1 p2 p3 p4 y1 y2 y3 y4 : Fin 2,
    decide (rowCond (some ![p1, p2, p3, p4]) ![y1, y2, y3, y4] none) = endB (some ![p1, p2, p3, p4]) ![y1, y2, y3, y4] := by
  decide +kernel

lemma rgsB_iff (c : ℕ) (hc : c ≤ 2) (r : Fin 4 → Fin 2) : rowRgs c r ↔ rgsB c r = true := by
  rw [row_eta r, ← rgsB_eq ⟨c, by omega⟩, decide_eq_true_iff]

lemma newcB_eq' (c : ℕ) (hc : c ≤ 2) (r : Fin 4 → Fin 2) : newc c r = newcB c r := by
  rw [row_eta r]
  exact newcB_eq ⟨c, by omega⟩ (r 0) (r 1) (r 2) (r 3)

lemma newcB_le (c : ℕ) (hc : c ≤ 2) (r : Fin 4 → Fin 2) : newcB c r ≤ 2 := by
  rw [← newcB_eq' c hc r]
  exact newc_le c hc r

lemma condB_iff (q : Option (Fin 4 → Fin 2)) (r t : Fin 4 → Fin 2) : rowCond q r (some t) ↔ condB q r t = true := by
  rcases q with _ | p
  · rw [row_eta r, row_eta t, ← condB_eqN, decide_eq_true_iff]
  · rw [row_eta p, row_eta r, row_eta t, ← condB_eqS, decide_eq_true_iff]

lemma endB_iff (q : Option (Fin 4 → Fin 2)) (r : Fin 4 → Fin 2) : rowCond q r none ↔ endB q r = true := by
  rcases q with _ | p
  · rw [row_eta r, ← endB_eqN, decide_eq_true_iff]
  · rw [row_eta p, row_eta r, ← endB_eqS, decide_eq_true_iff]


/-- One step of the transfer, the rows below r enumerated entry by entry. -/
def T (g : Option (Fin 4 → Fin 2) → (Fin 4 → Fin 2) → ℕ → ℕ) (q : Option (Fin 4 → Fin 2)) (r : Fin 4 → Fin 2) (c : ℕ) : ℕ :=
  if rgsB c r = true then
    ∑ x : Fin 2, ∑ y : Fin 2, ∑ z : Fin 2, ∑ u : Fin 2, (if condB q r ![x, y, z, u] = true then g (some r) ![x, y, z, u] (newcB c r) else 0)
  else 0

lemma W_succT (n : ℕ) (q : Option (Fin 4 → Fin 2)) (r : Fin 4 → Fin 2) (c : ℕ) (hc : c ≤ 2) :
    W (n + 1) q r c = T (W n) q r c := by
  rw [W_succ, sum_row]
  unfold T
  simp only [rgsB_iff c hc, condB_iff, newcB_eq' c hc]

lemma T_congr (g g' : Option (Fin 4 → Fin 2) → (Fin 4 → Fin 2) → ℕ → ℕ) (q : Option (Fin 4 → Fin 2)) (r : Fin 4 → Fin 2) (c : ℕ)
    (h : ∀ s, g (some r) s (newcB c r) = g' (some r) s (newcB c r)) : T g q r c = T g' q r c := by
  unfold T
  simp only [h]

/-- W(0) as a function. -/
def W0f (q : Option (Fin 4 → Fin 2)) (r : Fin 4 → Fin 2) (c : ℕ) : ℕ :=
  if endB q r = true ∧ rgsB c r = true then 1 else 0

lemma W_zero' (q : Option (Fin 4 → Fin 2)) (r : Fin 4 → Fin 2) (c : ℕ) (hc : c ≤ 2) : W 0 q r c = W0f q r c := by
  rw [W_zero]
  unfold W0f
  simp only [endB_iff, rgsB_iff c hc]

lemma inv_next (c : ℕ) (hc : c ≤ 2) (r : Fin 4 → Fin 2) :
    ∀ p, some r = some p → ∀ j, (p j).val < newcB c r := by
  intro p hp j
  rw [← Option.some.inj hp, ← newcB_eq' c hc r]
  exact (lt_newc c r _).2 (Or.inr ⟨j, le_refl _⟩)

/-- W(1, none, r, c) for c <= 2, nested by the entries of r and then c. -/
def LN1 : List (List (List (List (List ℕ)))) :=
  [[[[[1, 1, 1], [3, 3, 3]], [[3, 3, 3], [5, 5, 5]]], [[[3, 3, 3], [1, 1, 1]], [[5, 5, 5], [3, 3, 3]]]], [[[[0, 3, 3], [0, 5, 5]], [[0, 1, 1], [0, 3, 3]]], [[[0, 5, 5], [0, 3, 3]], [[0, 3, 3], [0, 1, 1]]]]]
abbrev w : List (List (List ℕ)) := [[[0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0]]]


/-- W(1, some p, r, c) for c <= 2, nested by the entries of p, of r, and then c. -/
def LS1 : List (List (List (List (List (List (List (List (List ℕ)))))))) :=
  [[[[[[w, w], [[[[0, 0, 0], [0, 4, 4]], [[0, 0, 0], [0, 0, 0]]], w]], [[[[[0, 0, 0], [0, 0, 0]], [[1, 1, 1], [0, 0, 0]]], w], [[[[0, 2, 2], [0, 4, 4]], [[0, 0, 0], [0, 0, 0]]], w]]], [[[[[[0, 0, 0], [1, 1, 1]], [[0, 0, 0], [0, 0, 0]]], [[[2, 2, 2], [0, 0, 0]], [[0, 0, 0], [0, 0, 0]]]], [w, [[[0, 4, 4], [0, 0, 0]], [[0, 0, 0], [0, 0, 0]]]]], [[[[[0, 0, 0], [0, 0, 0]], [[0, 0, 0], [1, 1, 1]]], [[[2, 2, 2], [1, 1, 1]], [[0, 0, 0], [0, 0, 0]]]], [w, [[[0, 4, 4], [0, 2, 2]], [[0, 0, 0], [0, 0, 0]]]]]]], [[[[[[[0, 0, 0], [0, 0, 0]], [[2, 2, 2], [4, 4, 4]]], w], [[[[0, 1, 1], [0, 0, 0]], [[0, 0, 0], [0, 0, 0]]], w]], [[[[[0, 0, 0], [0, 0, 0]], [[0, 0, 0], [4, 4, 4]]], w], [w, w]]], [[[w, [[[0, 0, 0], [0, 0, 0]], [[4, 4, 4], [2, 2, 2]]]], [[[[0, 0, 0], [0, 1, 1]], [[0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0]], [[0, 2, 2], [0, 1, 1]]]]], [[w, [[[0, 0, 0], [0, 0, 0]], [[4, 4, 4], [0, 0, 0]]]], [[[[0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 1, 1]]], [[[0, 0, 0], [0, 0, 0]], [[0, 2, 2], [0, 0, 0]]]]]]]], [[[[[[[[0, 0, 0], [2, 2, 2]], [[0, 0, 0], [0, 0, 0]]], [[[1, 1, 1], [0, 0, 0]], [[0, 0, 0], [0, 0, 0]]]], [[[[0, 0, 0], [0, 4, 4]], [[0, 0, 0], [0, 0, 0]]], w]], [[[[[1, 1, 1], [2, 2, 2]], [[0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0]], [[1, 1, 1], [0, 0, 0]]]], [[[[0, 2, 2], [0, 4, 4]], [[0, 0, 0], [0, 0, 0]]], w]]], [[[w, w], [w, [[[0, 4, 4], [0, 0, 0]], [[0, 0, 0], [0, 0, 0]]]]], [[w, [[[0, 0, 0], [0, 0, 0]], [[0, 0, 0], [1, 1, 1]]]], [w, [[[0, 4, 4], [0, 2, 2]], [[0, 0, 0], [0, 0, 0]]]]]]], [[[[[[[0, 0, 0], [0, 0, 0]], [[2, 2, 2], [4, 4, 4]]], w], [[[[0, 0, 0], [0, 0, 0]], [[0, 1, 1], [0, 2, 2]]], [[[0, 1, 1], [0, 0, 0]], [[0, 0, 0], [0, 0, 0]]]]], [[[[[0, 0, 0], [0, 0, 0]], [[0, 0, 0], [4, 4, 4]]], w], [[[[0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 2, 2]]], [[[0, 0, 0], [0, 0, 0]], [[0, 1, 1], [0, 0, 0]]]]]], [[[w, [[[0, 0, 0], [0, 0, 0]], [[4, 4, 4], [2, 2, 2]]]], [w, [[[0, 0, 0], [0, 1, 1]], [[0, 0, 0], [0, 0, 0]]]]], [[w, [[[0, 0, 0], [0, 0, 0]], [[4, 4, 4], [0, 0, 0]]]], [w, w]]]]]]

/-- W(1) as a table. -/
def tab1 (q : Option (Fin 4 → Fin 2)) (r : Fin 4 → Fin 2) (c : ℕ) : ℕ :=
  match q with
  | none => ((((LN1.getD (r 0).val []).getD (r 1).val []).getD (r 2).val []).getD (r 3).val []).getD c 0
  | some p => ((((((((LS1.getD (p 0).val []).getD (p 1).val []).getD (p 2).val []).getD (p 3).val []).getD (r 0).val []).getD (r 1).val []).getD (r 2).val []).getD (r 3).val []).getD c 0

/-- W(2, none, r, c) for c <= 2, nested by the entries of r and then c. -/
def LN2 : List (List (List (List (List ℕ)))) :=
  [[[[[4, 4, 4], [7, 7, 7]], [[7, 7, 7], [10, 10, 10]]], [[[7, 7, 7], [4, 4, 4]], [[10, 10, 10], [7, 7, 7]]]], [[[[0, 7, 7], [0, 10, 10]], [[0, 4, 4], [0, 7, 7]]], [[[0, 10, 10], [0, 7, 7]], [[0, 7, 7], [0, 4, 4]]]]]

/-- W(2, some p, r, c) for c <= 2, nested by the entries of p, of r, and then c. -/
def LS2 : List (List (List (List (List (List (List (List (List ℕ)))))))) :=
  [[[[[[w, w], [[[[0, 0, 0], [0, 9, 9]], [[0, 0, 0], [0, 0, 0]]], w]], [[[[[0, 0, 0], [0, 0, 0]], [[1, 1, 1], [0, 0, 0]]], w], [[[[0, 6, 6], [0, 9, 9]], [[0, 0, 0], [0, 0, 0]]], w]]], [[[[[[0, 0, 0], [1, 1, 1]], [[0, 0, 0], [0, 0, 0]]], [[[6, 6, 6], [0, 0, 0]], [[0, 0, 0], [0, 0, 0]]]], [w, [[[0, 9, 9], [0, 0, 0]], [[0, 0, 0], [0, 0, 0]]]]], [[[[[0, 0, 0], [0, 0, 0]], [[0, 0, 0], [1, 1, 1]]], [[[6, 6, 6], [4, 4, 4]], [[0, 0, 0], [0, 0, 0]]]], [w, [[[0, 9, 9], [0, 6, 6]], [[0, 0, 0], [0, 0, 0]]]]]]], [[[[[[[0, 0, 0], [0, 0, 0]], [[6, 6, 6], [9, 9, 9]]], w], [[[[0, 1, 1], [0, 0, 0]], [[0, 0, 0], [0, 0, 0]]], w]], [[[[[0, 0, 0], [0, 0, 0]], [[0, 0, 0], [9, 9, 9]]], w], [w, w]]], [[[w, [[[0, 0, 0], [0, 0, 0]], [[9, 9, 9], [6, 6, 6]]]], [[[[0, 0, 0], [0, 1, 1]], [[0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0]], [[0, 6, 6], [0, 4, 4]]]]], [[w, [[[0, 0, 0], [0, 0, 0]], [[9, 9, 9], [0, 0, 0]]]], [[[[0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 1, 1]]], [[[0, 0, 0], [0, 0, 0]], [[0, 6, 6], [0, 0, 0]]]]]]]], [[[[[[[[0, 0, 0], [6, 6, 6]], [[0, 0, 0], [0, 0, 0]]], [[[1, 1, 1], [0, 0, 0]], [[0, 0, 0], [0, 0, 0]]]], [[[[0, 0, 0], [0, 9, 9]], [[0, 0, 0], [0, 0, 0]]], w]], [[[[[4, 4, 4], [6, 6, 6]], [[0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0]], [[1, 1, 1], [0, 0, 0]]]], [[[[0, 6, 6], [0, 9, 9]], [[0, 0, 0], [0, 0, 0]]], w]]], [[[w, w], [w, [[[0, 9, 9], [0, 0, 0]], [[0, 0, 0], [0, 0, 0]]]]], [[w, [[[0, 0, 0], [0, 0, 0]], [[0, 0, 0], [1, 1, 1]]]], [w, [[[0, 9, 9], [0, 6, 6]], [[0, 0, 0], [0, 0, 0]]]]]]], [[[[[[[0, 0, 0], [0, 0, 0]], [[6, 6, 6], [9, 9, 9]]], w], [[[[0, 0, 0], [0, 0, 0]], [[0, 4, 4], [0, 6, 6]]], [[[0, 1, 1], [0, 0, 0]], [[0, 0, 0], [0, 0, 0]]]]], [[[[[0, 0, 0], [0, 0, 0]], [[0, 0, 0], [9, 9, 9]]], w], [[[[0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 6, 6]]], [[[0, 0, 0], [0, 0, 0]], [[0, 1, 1], [0, 0, 0]]]]]], [[[w, [[[0, 0, 0], [0, 0, 0]], [[9, 9, 9], [6, 6, 6]]]], [w, [[[0, 0, 0], [0, 1, 1]], [[0, 0, 0], [0, 0, 0]]]]], [[w, [[[0, 0, 0], [0, 0, 0]], [[9, 9, 9], [0, 0, 0]]]], [w, w]]]]]]

/-- W(2) as a table. -/
def tab2 (q : Option (Fin 4 → Fin 2)) (r : Fin 4 → Fin 2) (c : ℕ) : ℕ :=
  match q with
  | none => ((((LN2.getD (r 0).val []).getD (r 1).val []).getD (r 2).val []).getD (r 3).val []).getD c 0
  | some p => ((((((((LS2.getD (p 0).val []).getD (p 1).val []).getD (p 2).val []).getD (p 3).val []).getD (r 0).val []).getD (r 1).val []).getD (r 2).val []).getD (r 3).val []).getD c 0

/-- W(3, none, r, c) for c <= 2, nested by the entries of r and then c. -/
def LN3 : List (List (List (List (List ℕ)))) :=
  [[[[[9, 9, 9], [16, 16, 16]], [[16, 16, 16], [26, 26, 26]]], [[[16, 16, 16], [9, 9, 9]], [[26, 26, 26], [16, 16, 16]]]], [[[[0, 16, 16], [0, 26, 26]], [[0, 9, 9], [0, 16, 16]]], [[[0, 26, 26], [0, 16, 16]], [[0, 16, 16], [0, 9, 9]]]]]

/-- W(3, some p, r, c) for c <= 2, nested by the entries of p, of r, and then c. -/
def LS3 : List (List (List (List (List (List (List (List (List ℕ)))))))) :=
  [[[[[[w, w], [[[[0, 0, 0], [0, 25, 25]], [[0, 0, 0], [0, 0, 0]]], w]], [[[[[0, 0, 0], [0, 0, 0]], [[1, 1, 1], [0, 0, 0]]], w], [[[[0, 15, 15], [0, 25, 25]], [[0, 0, 0], [0, 0, 0]]], w]]], [[[[[[0, 0, 0], [1, 1, 1]], [[0, 0, 0], [0, 0, 0]]], [[[15, 15, 15], [0, 0, 0]], [[0, 0, 0], [0, 0, 0]]]], [w, [[[0, 25, 25], [0, 0, 0]], [[0, 0, 0], [0, 0, 0]]]]], [[[[[0, 0, 0], [0, 0, 0]], [[0, 0, 0], [1, 1, 1]]], [[[15, 15, 15], [9, 9, 9]], [[0, 0, 0], [0, 0, 0]]]], [w, [[[0, 25, 25], [0, 15, 15]], [[0, 0, 0], [0, 0, 0]]]]]]], [[[[[[[0, 0, 0], [0, 0, 0]], [[15, 15, 15], [25, 25, 25]]], w], [[[[0, 1, 1], [0, 0, 0]], [[0, 0, 0], [0, 0, 0]]], w]], [[[[[0, 0, 0], [0, 0, 0]], [[0, 0, 0], [25, 25, 25]]], w], [w, w]]], [[[w, [[[0, 0, 0], [0, 0, 0]], [[25, 25, 25], [15, 15, 15]]]], [[[[0, 0, 0], [0, 1, 1]], [[0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0]], [[0, 15, 15], [0, 9, 9]]]]], [[w, [[[0, 0, 0], [0, 0, 0]], [[25, 25, 25], [0, 0, 0]]]], [[[[0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 1, 1]]], [[[0, 0, 0], [0, 0, 0]], [[0, 15, 15], [0, 0, 0]]]]]]]], [[[[[[[[0, 0, 0], [15, 15, 15]], [[0, 0, 0], [0, 0, 0]]], [[[1, 1, 1], [0, 0, 0]], [[0, 0, 0], [0, 0, 0]]]], [[[[0, 0, 0], [0, 25, 25]], [[0, 0, 0], [0, 0, 0]]], w]], [[[[[9, 9, 9], [15, 15, 15]], [[0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0]], [[1, 1, 1], [0, 0, 0]]]], [[[[0, 15, 15], [0, 25, 25]], [[0, 0, 0], [0, 0, 0]]], w]]], [[[w, w], [w, [[[0, 25, 25], [0, 0, 0]], [[0, 0, 0], [0, 0, 0]]]]], [[w, [[[0, 0, 0], [0, 0, 0]], [[0, 0, 0], [1, 1, 1]]]], [w, [[[0, 25, 25], [0, 15, 15]], [[0, 0, 0], [0, 0, 0]]]]]]], [[[[[[[0, 0, 0], [0, 0, 0]], [[15, 15, 15], [25, 25, 25]]], w], [[[[0, 0, 0], [0, 0, 0]], [[0, 9, 9], [0, 15, 15]]], [[[0, 1, 1], [0, 0, 0]], [[0, 0, 0], [0, 0, 0]]]]], [[[[[0, 0, 0], [0, 0, 0]], [[0, 0, 0], [25, 25, 25]]], w], [[[[0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 15, 15]]], [[[0, 0, 0], [0, 0, 0]], [[0, 1, 1], [0, 0, 0]]]]]], [[[w, [[[0, 0, 0], [0, 0, 0]], [[25, 25, 25], [15, 15, 15]]]], [w, [[[0, 0, 0], [0, 1, 1]], [[0, 0, 0], [0, 0, 0]]]]], [[w, [[[0, 0, 0], [0, 0, 0]], [[25, 25, 25], [0, 0, 0]]]], [w, w]]]]]]

/-- W(3) as a table. -/
def tab3 (q : Option (Fin 4 → Fin 2)) (r : Fin 4 → Fin 2) (c : ℕ) : ℕ :=
  match q with
  | none => ((((LN3.getD (r 0).val []).getD (r 1).val []).getD (r 2).val []).getD (r 3).val []).getD c 0
  | some p => ((((((((LS3.getD (p 0).val []).getD (p 1).val []).getD (p 2).val []).getD (p 3).val []).getD (r 0).val []).getD (r 1).val []).getD (r 2).val []).getD (r 3).val []).getD c 0

/-- W(4, none, r, c) for c <= 2, nested by the entries of r and then c. -/
def LN4 : List (List (List (List (List ℕ)))) :=
  [[[[[25, 25, 25], [41, 41, 41]], [[41, 41, 41], [65, 65, 65]]], [[[41, 41, 41], [25, 25, 25]], [[65, 65, 65], [41, 41, 41]]]], [[[[0, 41, 41], [0, 65, 65]], [[0, 25, 25], [0, 41, 41]]], [[[0, 65, 65], [0, 41, 41]], [[0, 41, 41], [0, 25, 25]]]]]

/-- W(4, some p, r, c) for c <= 2, nested by the entries of p, of r, and then c. -/
def LS4 : List (List (List (List (List (List (List (List (List ℕ)))))))) :=
  [[[[[[w, w], [[[[0, 0, 0], [0, 64, 64]], [[0, 0, 0], [0, 0, 0]]], w]], [[[[[0, 0, 0], [0, 0, 0]], [[1, 1, 1], [0, 0, 0]]], w], [[[[0, 40, 40], [0, 64, 64]], [[0, 0, 0], [0, 0, 0]]], w]]], [[[[[[0, 0, 0], [1, 1, 1]], [[0, 0, 0], [0, 0, 0]]], [[[40, 40, 40], [0, 0, 0]], [[0, 0, 0], [0, 0, 0]]]], [w, [[[0, 64, 64], [0, 0, 0]], [[0, 0, 0], [0, 0, 0]]]]], [[[[[0, 0, 0], [0, 0, 0]], [[0, 0, 0], [1, 1, 1]]], [[[40, 40, 40], [25, 25, 25]], [[0, 0, 0], [0, 0, 0]]]], [w, [[[0, 64, 64], [0, 40, 40]], [[0, 0, 0], [0, 0, 0]]]]]]], [[[[[[[0, 0, 0], [0, 0, 0]], [[40, 40, 40], [64, 64, 64]]], w], [[[[0, 1, 1], [0, 0, 0]], [[0, 0, 0], [0, 0, 0]]], w]], [[[[[0, 0, 0], [0, 0, 0]], [[0, 0, 0], [64, 64, 64]]], w], [w, w]]], [[[w, [[[0, 0, 0], [0, 0, 0]], [[64, 64, 64], [40, 40, 40]]]], [[[[0, 0, 0], [0, 1, 1]], [[0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0]], [[0, 40, 40], [0, 25, 25]]]]], [[w, [[[0, 0, 0], [0, 0, 0]], [[64, 64, 64], [0, 0, 0]]]], [[[[0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 1, 1]]], [[[0, 0, 0], [0, 0, 0]], [[0, 40, 40], [0, 0, 0]]]]]]]], [[[[[[[[0, 0, 0], [40, 40, 40]], [[0, 0, 0], [0, 0, 0]]], [[[1, 1, 1], [0, 0, 0]], [[0, 0, 0], [0, 0, 0]]]], [[[[0, 0, 0], [0, 64, 64]], [[0, 0, 0], [0, 0, 0]]], w]], [[[[[25, 25, 25], [40, 40, 40]], [[0, 0, 0], [0, 0, 0]]], [[[0, 0, 0], [0, 0, 0]], [[1, 1, 1], [0, 0, 0]]]], [[[[0, 40, 40], [0, 64, 64]], [[0, 0, 0], [0, 0, 0]]], w]]], [[[w, w], [w, [[[0, 64, 64], [0, 0, 0]], [[0, 0, 0], [0, 0, 0]]]]], [[w, [[[0, 0, 0], [0, 0, 0]], [[0, 0, 0], [1, 1, 1]]]], [w, [[[0, 64, 64], [0, 40, 40]], [[0, 0, 0], [0, 0, 0]]]]]]], [[[[[[[0, 0, 0], [0, 0, 0]], [[40, 40, 40], [64, 64, 64]]], w], [[[[0, 0, 0], [0, 0, 0]], [[0, 25, 25], [0, 40, 40]]], [[[0, 1, 1], [0, 0, 0]], [[0, 0, 0], [0, 0, 0]]]]], [[[[[0, 0, 0], [0, 0, 0]], [[0, 0, 0], [64, 64, 64]]], w], [[[[0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 40, 40]]], [[[0, 0, 0], [0, 0, 0]], [[0, 1, 1], [0, 0, 0]]]]]], [[[w, [[[0, 0, 0], [0, 0, 0]], [[64, 64, 64], [40, 40, 40]]]], [w, [[[0, 0, 0], [0, 1, 1]], [[0, 0, 0], [0, 0, 0]]]]], [[w, [[[0, 0, 0], [0, 0, 0]], [[64, 64, 64], [0, 0, 0]]]], [w, w]]]]]]

/-- W(4) as a table. -/
def tab4 (q : Option (Fin 4 → Fin 2)) (r : Fin 4 → Fin 2) (c : ℕ) : ℕ :=
  match q with
  | none => ((((LN4.getD (r 0).val []).getD (r 1).val []).getD (r 2).val []).getD (r 3).val []).getD c 0
  | some p => ((((((((LS4.getD (p 0).val []).getD (p 1).val []).getD (p 2).val []).getD (p 3).val []).getD (r 0).val []).getD (r 1).val []).getD (r 2).val []).getD (r 3).val []).getD c 0

lemma checkN1 : ∀ y1 y2 y3 y4 : Fin 2, ∀ c : Fin 3,
    T W0f none ![y1, y2, y3, y4] c.val = tab1 none ![y1, y2, y3, y4] c.val := by
  decide +kernel

lemma checkS1 : ∀ p1 p2 p3 p4 : Fin 2, ∀ y1 y2 y3 y4 : Fin 2, ∀ c : Fin 3, (p1.val < c.val ∧ p2.val < c.val ∧ p3.val < c.val ∧ p4.val < c.val) →
    T W0f (some ![p1, p2, p3, p4]) ![y1, y2, y3, y4] c.val = tab1 (some ![p1, p2, p3, p4]) ![y1, y2, y3, y4] c.val := by
  decide +kernel

lemma checkN2 : ∀ y1 y2 y3 y4 : Fin 2, ∀ c : Fin 3,
    T tab1 none ![y1, y2, y3, y4] c.val = tab2 none ![y1, y2, y3, y4] c.val := by
  decide +kernel

lemma checkS2 : ∀ p1 p2 p3 p4 : Fin 2, ∀ y1 y2 y3 y4 : Fin 2, ∀ c : Fin 3, (p1.val < c.val ∧ p2.val < c.val ∧ p3.val < c.val ∧ p4.val < c.val) →
    T tab1 (some ![p1, p2, p3, p4]) ![y1, y2, y3, y4] c.val = tab2 (some ![p1, p2, p3, p4]) ![y1, y2, y3, y4] c.val := by
  decide +kernel

lemma checkN3 : ∀ y1 y2 y3 y4 : Fin 2, ∀ c : Fin 3,
    T tab2 none ![y1, y2, y3, y4] c.val = tab3 none ![y1, y2, y3, y4] c.val := by
  decide +kernel

lemma checkS3 : ∀ p1 p2 p3 p4 : Fin 2, ∀ y1 y2 y3 y4 : Fin 2, ∀ c : Fin 3, (p1.val < c.val ∧ p2.val < c.val ∧ p3.val < c.val ∧ p4.val < c.val) →
    T tab2 (some ![p1, p2, p3, p4]) ![y1, y2, y3, y4] c.val = tab3 (some ![p1, p2, p3, p4]) ![y1, y2, y3, y4] c.val := by
  decide +kernel

lemma checkN4 : ∀ y1 y2 y3 y4 : Fin 2, ∀ c : Fin 3,
    T tab3 none ![y1, y2, y3, y4] c.val = tab4 none ![y1, y2, y3, y4] c.val := by
  decide +kernel

lemma checkS4 : ∀ p1 p2 p3 p4 : Fin 2, ∀ y1 y2 y3 y4 : Fin 2, ∀ c : Fin 3, (p1.val < c.val ∧ p2.val < c.val ∧ p3.val < c.val ∧ p4.val < c.val) →
    T tab3 (some ![p1, p2, p3, p4]) ![y1, y2, y3, y4] c.val = tab4 (some ![p1, p2, p3, p4]) ![y1, y2, y3, y4] c.val := by
  decide +kernel

lemma checkN_rel : ∀ y1 y2 y3 y4 : Fin 2, ∀ c : Fin 3,
    T tab4 none ![y1, y2, y3, y4] c.val + 3 * tab2 none ![y1, y2, y3, y4] c.val =
      3 * tab4 none ![y1, y2, y3, y4] c.val + tab1 none ![y1, y2, y3, y4] c.val := by
  decide +kernel

lemma checkS_rel : ∀ p1 p2 p3 p4 : Fin 2, ∀ y1 y2 y3 y4 : Fin 2, ∀ c : Fin 3, (p1.val < c.val ∧ p2.val < c.val ∧ p3.val < c.val ∧ p4.val < c.val) →
    T tab4 (some ![p1, p2, p3, p4]) ![y1, y2, y3, y4] c.val + 3 * tab2 (some ![p1, p2, p3, p4]) ![y1, y2, y3, y4] c.val =
      3 * tab4 (some ![p1, p2, p3, p4]) ![y1, y2, y3, y4] c.val + tab1 (some ![p1, p2, p3, p4]) ![y1, y2, y3, y4] c.val := by
  decide +kernel

lemma W_1 (q : Option (Fin 4 → Fin 2)) (r : Fin 4 → Fin 2) (c : ℕ) (hc : c ≤ 2)
    (hq : ∀ p, q = some p → ∀ j, (p j).val < c) :
    W 1 q r c = tab1 q r c := by
  rw [W_succT _ q r c hc,
    T_congr _ W0f q r c (fun s => W_zero' _ s _ (newcB_le c hc r))]
  rcases q with _ | p
  · rw [row_eta r]
    exact checkN1 (r 0) (r 1) (r 2) (r 3) ⟨c, by omega⟩
  · rw [row_eta p, row_eta r]
    exact checkS1 (p 0) (p 1) (p 2) (p 3) (r 0) (r 1) (r 2) (r 3) ⟨c, by omega⟩ ⟨hq p rfl 0, hq p rfl 1, hq p rfl 2, hq p rfl 3⟩

lemma W_2 (q : Option (Fin 4 → Fin 2)) (r : Fin 4 → Fin 2) (c : ℕ) (hc : c ≤ 2)
    (hq : ∀ p, q = some p → ∀ j, (p j).val < c) :
    W 2 q r c = tab2 q r c := by
  rw [show W 2 q r c = W (1 + 1) q r c from rfl, W_succT _ q r c hc,
    T_congr _ tab1 q r c
      (fun s => W_1 _ s _ (newcB_le c hc r) (inv_next c hc r))]
  rcases q with _ | p
  · rw [row_eta r]
    exact checkN2 (r 0) (r 1) (r 2) (r 3) ⟨c, by omega⟩
  · rw [row_eta p, row_eta r]
    exact checkS2 (p 0) (p 1) (p 2) (p 3) (r 0) (r 1) (r 2) (r 3) ⟨c, by omega⟩ ⟨hq p rfl 0, hq p rfl 1, hq p rfl 2, hq p rfl 3⟩

lemma W_3 (q : Option (Fin 4 → Fin 2)) (r : Fin 4 → Fin 2) (c : ℕ) (hc : c ≤ 2)
    (hq : ∀ p, q = some p → ∀ j, (p j).val < c) :
    W 3 q r c = tab3 q r c := by
  rw [show W 3 q r c = W (2 + 1) q r c from rfl, W_succT _ q r c hc,
    T_congr _ tab2 q r c
      (fun s => W_2 _ s _ (newcB_le c hc r) (inv_next c hc r))]
  rcases q with _ | p
  · rw [row_eta r]
    exact checkN3 (r 0) (r 1) (r 2) (r 3) ⟨c, by omega⟩
  · rw [row_eta p, row_eta r]
    exact checkS3 (p 0) (p 1) (p 2) (p 3) (r 0) (r 1) (r 2) (r 3) ⟨c, by omega⟩ ⟨hq p rfl 0, hq p rfl 1, hq p rfl 2, hq p rfl 3⟩

lemma W_4 (q : Option (Fin 4 → Fin 2)) (r : Fin 4 → Fin 2) (c : ℕ) (hc : c ≤ 2)
    (hq : ∀ p, q = some p → ∀ j, (p j).val < c) :
    W 4 q r c = tab4 q r c := by
  rw [show W 4 q r c = W (3 + 1) q r c from rfl, W_succT _ q r c hc,
    T_congr _ tab3 q r c
      (fun s => W_3 _ s _ (newcB_le c hc r) (inv_next c hc r))]
  rcases q with _ | p
  · rw [row_eta r]
    exact checkN4 (r 0) (r 1) (r 2) (r 3) ⟨c, by omega⟩
  · rw [row_eta p, row_eta r]
    exact checkS4 (p 0) (p 1) (p 2) (p 3) (r 0) (r 1) (r 2) (r 3) ⟨c, by omega⟩ ⟨hq p rfl 0, hq p rfl 1, hq p rfl 2, hq p rfl 3⟩

lemma W_rec (n : ℕ) : ∀ (q : Option (Fin 4 → Fin 2)) (r : Fin 4 → Fin 2) (c : ℕ), c ≤ 2 →
    (∀ p, q = some p → ∀ j, (p j).val < c) →
    W (n + 5) q r c + 3 * W (n + 2) q r c = 3 * W (n + 4) q r c + W (n + 1) q r c := by
  induction n with
  | zero =>
    intro q r c hc hq
    rw [show W (0 + 5) q r c = W (4 + 1) q r c from rfl, W_succT 4 q r c hc,
      T_congr _ tab4 q r c
        (fun s => W_4 _ s _ (newcB_le c hc r) (inv_next c hc r)),
      show W (0 + 1) q r c = W 1 q r c from rfl, W_1 q r c hc hq,
      show W (0 + 2) q r c = W 2 q r c from rfl, W_2 q r c hc hq,
      show W (0 + 4) q r c = W 4 q r c from rfl, W_4 q r c hc hq]
    rcases q with _ | p
    · rw [row_eta r]
      exact checkN_rel (r 0) (r 1) (r 2) (r 3) ⟨c, by omega⟩
    · rw [row_eta p, row_eta r]
      exact checkS_rel (p 0) (p 1) (p 2) (p 3) (r 0) (r 1) (r 2) (r 3) ⟨c, by omega⟩ ⟨hq p rfl 0, hq p rfl 1, hq p rfl 2, hq p rfl 3⟩
  | succ n ih =>
    intro q r c hc hq
    rw [W_succT (n + 5) q r c hc, W_succT (n + 4) q r c hc, W_succT (n + 2) q r c hc, W_succT (n + 1) q r c hc]
    unfold T
    split_ifs with h
    · rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      split_ifs
      · exact ih _ _ _ (newcB_le c hc r) (inv_next c hc r)
      · simp
    · simp

lemma a_eq (n : ℕ) : a n = ∑ r : Fin 4 → Fin 2, W n none r 0 := by
  have e : a n = ((univ : Finset (Fin (n + 1) → Fin 4 → Fin 2)).filter
      (fun y => CondT y ∧ RowMajorNew y)).card := by
    unfold a
    refine Finset.card_bij'
      (fun (x : Fin 4 → Fin (n + 1) → Fin 2) _ => (fun j i => x i j : Fin (n + 1) → Fin 4 → Fin 2))
      (fun (y : Fin (n + 1) → Fin 4 → Fin 2) _ => (fun i j => y j i : Fin 4 → Fin (n + 1) → Fin 2))
      ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      refine ⟨(condT_iff x).1 hx.1, ?_⟩
      rw [rmn_two _ (by omega) (by norm_num)]
      exact (rmn_two x (by norm_num) (by omega)).1 hx.2
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      refine ⟨(condT_iff _).2 hy.1, ?_⟩
      rw [rmn_two _ (by norm_num) (by omega)]
      exact (rmn_two y (by omega) (by norm_num)).1 hy.2
    · intro x _
      rfl
    · intro y _
      rfl
  rw [e]
  unfold W
  rw [Finset.card_eq_sum_card_fiberwise (f := fun f => f 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Finset.filter_filter]
  refine congrArg Finset.card (Finset.filter_congr (fun f _ => ?_))
  rw [cond_iff, rmn_iff, and_assoc]

lemma a_rec (n : ℕ) : a (n + 5) + 3 * a (n + 2) = 3 * a (n + 4) + a (n + 1) := by
  rw [a_eq, a_eq, a_eq, a_eq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  exact W_rec n none r 0 (by norm_num) (fun _ h => by cases h)

lemma a_zero : a 0 = 8 := by
  rw [a_eq, sum_row]
  simp only [W_zero]
  decide +kernel

lemma a_one : a 1 = 24 := by
  have h : ∀ r, W 1 none r 0 = tab1 none r 0 := fun r => W_1 none r 0 (by norm_num) (fun _ h => by cases h)
  rw [a_eq, sum_row]
  simp only [h]
  decide +kernel

lemma a_two : a 2 = 56 := by
  have h : ∀ r, W 2 none r 0 = tab2 none r 0 := fun r => W_2 none r 0 (by norm_num) (fun _ h => by cases h)
  rw [a_eq, sum_row]
  simp only [h]
  decide +kernel

lemma a_three : a 3 = 134 := by
  have h : ∀ r, W 3 none r 0 = tab3 none r 0 := fun r => W_3 none r 0 (by norm_num) (fun _ h => by cases h)
  rw [a_eq, sum_row]
  simp only [h]
  decide +kernel

lemma a_four : a 4 = 344 := by
  have h : ∀ r, W 4 none r 0 = tab4 none r 0 := fun r => W_4 none r 0 (by norm_num) (fun _ h => by cases h)
  rw [a_eq, sum_row]
  simp only [h]
  decide +kernel

/-- Barker's g.f.: Sum_{n >= 1} a(n) x^n = 2x(12 - 8x - 17x^2 + 7x^3) / ((1 - x)(1 + x)(1 - 3x + x^2)). -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - X) * (1 + X) * (1 - 3 * X + X ^ 2)) = 2 * X * (12 - 8 * X - 17 * X ^ 2 + 7 * X ^ 3) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - X) * (1 + X) * (1 - 3 * X + X ^ 2)) = A - A * X ^ 1 * C 3 + A * X ^ 3 * C 3 - A * X ^ 4 * C 1 := by
    rw [show (C (1 : ℚ) : ℚ⟦X⟧) = 1 from map_one C,
      show (C (3 : ℚ) : ℚ⟦X⟧) = 3 from map_ofNat C 3]
    ring
  have e2 : (2 * X * (12 - 8 * X - 17 * X ^ 2 + 7 * X ^ 3) : ℚ⟦X⟧) = X ^ 1 * C 24 - X ^ 2 * C 16 - X ^ 3 * C 34 + X ^ 4 * C 14 := by
    rw [show (C (14 : ℚ) : ℚ⟦X⟧) = 14 from map_ofNat C 14,
      show (C (16 : ℚ) : ℚ⟦X⟧) = 16 from map_ofNat C 16,
      show (C (24 : ℚ) : ℚ⟦X⟧) = 24 from map_ofNat C 24,
      show (C (34 : ℚ) : ℚ⟦X⟧) = 34 from map_ofNat C 34]
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
    
    have hq : (a (n + 5) : ℚ) + 3 * (a (n + 2) : ℚ) = 3 * (a (n + 4) : ℚ) + (a (n + 1) : ℚ) := by exact_mod_cast h
    simp only [show ¬ (n + 5 = 0) by omega,
      if_false,
      if_true,
      show 1 ≤ n + 5 by omega,
      show n + 5 - 1 = n + 4 by omega,
      show ¬ (n + 4 = 0) by omega,
      show 2 ≤ n + 5 by omega,
      show n + 5 - 2 = n + 3 by omega,
      show ¬ (n + 3 = 0) by omega,
      show 3 ≤ n + 5 by omega,
      show n + 5 - 3 = n + 2 by omega,
      show ¬ (n + 2 = 0) by omega,
      show 4 ≤ n + 5 by omega,
      show n + 5 - 4 = n + 1 by omega,
      show ¬ (n + 1 = 0) by omega,
      show ¬ (n + 5 = 1) by omega,
      show ¬ (n + 5 = 2) by omega,
      show ¬ (n + 5 = 3) by omega,
      show ¬ (n + 5 = 4) by omega]
    linear_combination hq

theorem cf (b : ℕ → ℕ) (h1 : b 1 = 24) (h2 : b 2 = 56) (h3 : b 3 = 134) (h4 : b 4 = 344)
    (hr : ∀ n, b (n + 5) + 3 * b (n + 2) = 3 * b (n + 4) + b (n + 1)) :
    ∀ n : ℕ, 1 ≤ n → (b n : ℝ) =
      2 ^ (1 - (n : ℤ)) * (2 ^ n * (15 + 2 * (-1) ^ n) +
        (9 - 4 * Real.sqrt 5) * (3 - Real.sqrt 5) ^ n +
        (3 + Real.sqrt 5) ^ n * (9 + 4 * Real.sqrt 5)) / 5 := by
  have s2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  set s := Real.sqrt 5 with hsdef
  set U : ℕ → ℝ := fun n => (9 - 4 * s) * (3 - s) ^ n + (3 + s) ^ n * (9 + 4 * s) with hU
  have Urec : ∀ n, U (n + 2) = 6 * U (n + 1) - 4 * U n := by
    intro n
    simp only [hU]
    have e1 : (3 - s) ^ 2 = 6 * (3 - s) - 4 := by linear_combination s2
    have e2 : (3 + s) ^ 2 = 6 * (3 + s) - 4 := by linear_combination s2
    rw [show (3 - s) ^ (n + 2) = (3 - s) ^ n * (3 - s) ^ 2 by ring,
      show (3 + s) ^ (n + 2) = (3 + s) ^ n * (3 + s) ^ 2 by ring, e1, e2]
    ring
  have U0 : U 0 = 18 := by simp only [hU]; ring
  have U1 : U 1 = 94 := by simp only [hU]; linear_combination 8 * s2
  have U2 : U 2 = 492 := by
    rw [show U 2 = U (0 + 2) from rfl, Urec, show U (0 + 1) = U 1 from rfl, U1, U0]; norm_num
  have U3 : U 3 = 2576 := by
    rw [show U 3 = U (1 + 2) from rfl, Urec, show U (1 + 1) = U 2 from rfl, U2, U1]; norm_num
  have U4 : U 4 = 13488 := by
    rw [show U 4 = U (2 + 2) from rfl, Urec, show U (2 + 1) = U 3 from rfl, U3, U2]; norm_num
  set G : ℕ → ℝ := fun n => 2 ^ n * (15 + 2 * (-1) ^ n) + U n with hG
  have Grec : ∀ n, G (n + 4) = 6 * G (n + 3) - 24 * G (n + 1) + 16 * G n := by
    intro n
    simp only [hG]
    have r0 := Urec n
    have r2 := Urec (n + 2)
    rw [show n + 2 + 2 = n + 4 from rfl, show n + 2 + 1 = n + 3 from rfl] at r2
    have r1 := Urec (n + 1)
    rw [show n + 1 + 2 = n + 3 from rfl, show n + 1 + 1 = n + 2 from rfl] at r1
    linear_combination r2 + 6 * r1 - 4 * r0 - 6 * r1
  have key : ∀ k, (b (k + 1) : ℝ) * 5 * 2 ^ (k + 1) = 2 * G (k + 1) ∧
      (b (k + 2) : ℝ) * 5 * 2 ^ (k + 2) = 2 * G (k + 2) ∧
      (b (k + 3) : ℝ) * 5 * 2 ^ (k + 3) = 2 * G (k + 3) ∧
      (b (k + 4) : ℝ) * 5 * 2 ^ (k + 4) = 2 * G (k + 4) := by
    intro k
    induction k with
    | zero =>
      simp only [hG, Nat.zero_add]
      rw [h1, h2, h3, h4, U1, U2, U3, U4]
      norm_num
    | succ k ih =>
      obtain ⟨i1, i2, i3, i4⟩ := ih
      refine ⟨i2, i3, i4, ?_⟩
      have h := hr k
      have hq : ((b (k + 5) : ℕ) : ℝ) + 3 * b (k + 2) = 3 * b (k + 4) + b (k + 1) := by
        exact_mod_cast h
      have hg := Grec (k + 1)
      rw [show k + 1 + 4 = k + 5 from rfl, show k + 1 + 3 = k + 4 from rfl,
        show k + 1 + 1 = k + 2 from rfl] at hg
      rw [show k + 1 + 4 = k + 5 from rfl]
      linear_combination (5 * 2 ^ (k + 5)) * hq + 6 * i4 - 24 * i2 + 16 * i1 - 2 * hg
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hk := (key k).1
  have hz : (2 : ℝ) ^ (1 - ((k + 1 : ℕ) : ℤ)) = 2 / 2 ^ (k + 1) := by
    rw [zpow_sub₀ two_ne_zero, zpow_natCast, zpow_one]
  have e : (2 : ℝ) ^ (k + 1) * (15 + 2 * (-1) ^ (k + 1)) + (9 - 4 * s) * (3 - s) ^ (k + 1) +
      (3 + s) ^ (k + 1) * (9 + 4 * s) = G (k + 1) := by simp only [hG, hU]; ring
  rw [hz, e]
  have hG' : G (k + 1) = (b (k + 1) : ℝ) * 5 * 2 ^ (k + 1) / 2 := by linear_combination (-1 / 2 : ℝ) * hk
  rw [hG']
  field_simp

/-- Barker's closed form. -/
theorem closed_form : ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      2 ^ (1 - (n : ℤ)) * (2 ^ n * (15 + 2 * (-1) ^ n) +
        (9 - 4 * Real.sqrt 5) * (3 - Real.sqrt 5) ^ n +
        (3 + Real.sqrt 5) ^ n * (9 + 4 * Real.sqrt 5)) / 5 :=
  cf a a_one a_two a_three a_four a_rec

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 + X) * (1 - 3 * X + X ^ 2)) = 2 * X * (12 - 8 * X - 17 * X ^ 2 + 7 * X ^ 3) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      2 ^ (1 - (n : ℤ)) * (2 ^ n * (15 + 2 * (-1) ^ n) +
        (9 - 4 * Real.sqrt 5) * (3 - Real.sqrt 5) ^ n +
        (3 + Real.sqrt 5) ^ n * (9 + 4 * Real.sqrt 5)) / 5 :=
  ⟨gf, closed_form⟩

/-- Controls: the entry's terms a(1..10), from the recurrence and the first values. -/
theorem controls : a 1 = 24 ∧ a 2 = 56 ∧ a 3 = 134 ∧ a 4 = 344 ∧ a 5 = 888 ∧ a 6 = 2318 ∧ a 7 = 6056 ∧ a 8 = 15848 ∧ a 9 = 41478 ∧ a 10 = 108584 := by
  have r0 := a_rec 0; have r1 := a_rec 1; have r2 := a_rec 2; have r3 := a_rec 3; have r4 := a_rec 4; have r5 := a_rec 5
  have h1 := a_one; have h2 := a_two; have h3 := a_three; have h4 := a_four
  norm_num at r0 r1 r2 r3 r4 r5
  omega

end OMA.S_oeis_a208086

theorem OMA.solution : type_of% @OMA.S_oeis_a208086.main :=
  OMA.S_oeis_a208086.conjecture
