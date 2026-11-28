import OMAStatements.S_oeis_a206170

namespace OMA.S_oeis_a206170

open PowerSeries Finset


instance {R C K : ℕ} : DecidablePred (@RowMajorNew R C K) := fun x => by
  unfold RowMajorNew; infer_instance



instance {R C K : ℕ} : DecidablePred (@Cond R C K) := fun x => by
  unfold Cond; infer_instance


/-! ## Rows -/

/-- blockNum of the subblock in columns i, i' of the rows r above t: the pairs (r i, t i') and
(t i, r i'), the diagonal and antidiagonal of the subblock of the array transposed back. -/
def bnT (r t : Fin 2 → Fin 4) (i i' : Fin 2) : ℕ :=
  (if r i = t i' then 1 else 0) + (if t i = r i' then 1 else 0)

/-- The subblocks between r and the row s below it, if any, differ from their horizontal
neighbors. -/
def okBelow (r : Fin 2 → Fin 4) (s : Option (Fin 2 → Fin 4)) : Prop :=
  match s with
  | none => True
  | some t => ∀ i i' i'' : Fin 2, i'.val = i.val + 1 → i''.val = i'.val + 1 →
      bnT r t i i' ≠ bnT r t i' i''

/-- The subblocks between q and r equal the ones below them, between r and s. -/
def okVert (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (s : Option (Fin 2 → Fin 4)) : Prop :=
  match q, s with
  | some p, some t => ∀ i i' : Fin 2, i'.val = i.val + 1 → bnT p r i i' = bnT r t i i'
  | _, _ => True

/-- The condition on the row r with the row q above it and the row s below it. -/
def rowCond (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (s : Option (Fin 2 → Fin 4)) : Prop :=
  okBelow r s ∧ okVert q r s

instance (r : Fin 2 → Fin 4) (s : Option (Fin 2 → Fin 4)) : Decidable (okBelow r s) := by
  unfold okBelow; split <;> infer_instance

instance (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (s : Option (Fin 2 → Fin 4)) : Decidable (okVert q r s) := by
  unfold okVert; split <;> infer_instance

instance (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (s : Option (Fin 2 → Fin 4)) : Decidable (rowCond q r s) := by
  unfold rowCond; infer_instance

/-- The condition of the transposed array y, whose rows are the columns of x: vertically
neighboring subblocks have equal numbers and horizontally neighboring ones different numbers. -/
def CondT {R : ℕ} (y : Fin R → Fin 2 → Fin 4) : Prop :=
  (∀ j j' : Fin R, j'.val = j.val + 1 → ∀ i i' i'' : Fin 2, i'.val = i.val + 1 →
      i''.val = i'.val + 1 → bnT (y j) (y j') i i' ≠ bnT (y j) (y j') i' i'') ∧
    ∀ j j' j'' : Fin R, j'.val = j.val + 1 → j''.val = j'.val + 1 → ∀ i i' : Fin 2,
      i'.val = i.val + 1 → bnT (y j) (y j') i i' = bnT (y j') (y j'') i i'

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

lemma blk_T {C : ℕ} (x : Fin 2 → Fin C → Fin 4) (i i' : Fin 2) (j j' : Fin C) :
    blockNum x i i' j j' = bnT (fun a => x a j) (fun a => x a j') i i' := rfl

lemma condT_iff {C : ℕ} (x : Fin 2 → Fin C → Fin 4) : Cond x ↔ CondT (fun j i => x i j) := by
  unfold Cond CondT
  simp only [blk_T]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun j j' hj i i' i'' hi hi' => h2 i i' i'' j j' hi hi' hj,
      fun j j' j'' hj hj' i i' hi => h1 i i' j j' j'' hi hj hj'⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i i' j j' j'' hi hj hj' => h2 j j' j'' hj hj' i i' hi,
      fun i i' i'' j j' hi hi' hj => h1 j j' hj i i' i'' hi hi'⟩

lemma cond_iff {R : ℕ} (y : Fin R → Fin 2 → Fin 4) : CondT y ↔ ValidFrom none y := by
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

/-! ## The count does not depend on the reading order

Every array has exactly one renaming of its values that introduces them in a given reading order
(the lexicographically least renaming does, and two such renamings agree on the array). A condition
that does not depend on the names of the values is therefore met by as many arrays introducing
their values in row major order as in column major order. -/

/-- The values of the sequence s are introduced in order: every value below s k occurs at an
earlier index. -/
def Rgs {N K : ℕ} (s : Fin N → Fin K) : Prop :=
  ∀ k, ∀ u : Fin K, u < s k → ∃ k', k' < k ∧ s k' = u

instance {N K : ℕ} : DecidablePred (@Rgs N K) := fun s => by unfold Rgs; infer_instance

/-- σ fixes every value of s when both s and σ ∘ s introduce their values in order. -/
lemma rgs_unique {N K : ℕ} (s : Fin N → Fin K) (σ : Equiv.Perm (Fin K)) (hs : Rgs s)
    (hσ : Rgs (fun k => σ (s k))) : ∀ k, σ (s k) = s k := by
  suffices h : ∀ m, ∀ k : Fin N, k.val = m → σ (s k) = s k from fun k => h _ k rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro k hk
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · obtain ⟨k', hk', he⟩ := hs k (σ (s k)) hlt
      have h2 := ih k'.val (by rw [← hk]; exact hk') k' rfl
      rw [he] at h2
      exact hne (σ.injective h2)
    · obtain ⟨k', hk', he⟩ := hσ k (s k) hgt
      have h2 := ih k'.val (by rw [← hk]; exact hk') k' rfl
      have e1 : s k' = s k := h2.symm.trans he
      apply hne
      rw [← e1]
      exact h2

/-- Every sequence has a renaming of its values that introduces them in order: the
lexicographically least renaming does. -/
lemma rgs_exists {N K : ℕ} (s : Fin N → Fin K) :
    ∃ σ : Equiv.Perm (Fin K), Rgs (fun k => σ (s k)) := by
  classical
  let O : Finset (Lex (Fin N → Fin K)) :=
    univ.image (fun σ : Equiv.Perm (Fin K) => toLex (fun k => σ (s k)))
  have hO : O.Nonempty := ⟨_, mem_image.2 ⟨1, mem_univ _, rfl⟩⟩
  obtain ⟨σ, -, hσ⟩ := mem_image.1 (O.min'_mem hO)
  refine ⟨σ, ?_⟩
  set y : Fin N → Fin K := fun k => σ (s k) with hy
  have hmin : ∀ τ : Equiv.Perm (Fin K), toLex y ≤ toLex (fun k => τ (y k)) := by
    intro τ
    rw [hσ]
    apply O.min'_le
    exact mem_image.2 ⟨τ * σ, mem_univ _, rfl⟩
  by_contra hbad
  have hex : ∃ k : Fin N, ∃ u : Fin K, u < y k ∧ ∀ k', k' < k → y k' ≠ u := by
    by_contra hno
    push_neg at hno
    exact hbad (fun k u hu => by
      obtain ⟨k', hk', he⟩ := hno k u hu
      exact ⟨k', hk', he⟩)
  obtain ⟨k, ⟨u, hu, hnu⟩, hkmin⟩ := WellFounded.has_min wellFounded_lt
    {k : Fin N | ∃ u : Fin K, u < y k ∧ ∀ k', k' < k → y k' ≠ u} hex
  have hyk : ∀ j, j < k → y j ≠ y k := by
    intro j hj hjk
    apply hkmin j ⟨u, hjk ▸ hu, fun k' hk' => hnu k' (lt_trans hk' hj)⟩ hj
  have hagree : ∀ j, j < k → Equiv.swap u (y k) (y j) = y j := by
    intro j hj
    exact Equiv.swap_apply_of_ne_of_ne (hnu j hj) (hyk j hj)
  have hle := Pi.apply_le_of_toLex (hmin (Equiv.swap u (y k))) (fun j hj => (hagree j hj).symm)
  rw [Equiv.swap_apply_right] at hle
  exact absurd hu (not_lt.2 hle)

/-- For a property of sequences that does not depend on the names of the values, as many
sequences introduce their values in the order of the indices as in the order given by e. -/
lemma card_rgs_reorder {N K : ℕ} (P : (Fin N → Fin K) → Prop) [DecidablePred P]
    (hP : ∀ (σ : Equiv.Perm (Fin K)) s, P (fun k => σ (s k)) ↔ P s) (e : Equiv.Perm (Fin N)) :
    ((univ : Finset (Fin N → Fin K)).filter (fun s => P s ∧ Rgs s)).card =
      ((univ : Finset (Fin N → Fin K)).filter (fun s => P s ∧ Rgs (fun k => s (e k)))).card := by
  classical
  have ex2 : ∀ s : Fin N → Fin K, ∃ σ : Equiv.Perm (Fin K), Rgs (fun k => σ (s (e k))) :=
    fun s => rgs_exists (fun k => s (e k))
  refine Finset.card_bij (fun s _ => fun k => (Classical.choose (ex2 s)) (s k)) ?_ ?_ ?_
  · intro s hs
    simp only [mem_filter, mem_univ, true_and] at hs ⊢
    exact ⟨(hP _ s).2 hs.1, Classical.choose_spec (ex2 s)⟩
  · intro s1 hs1 s2 hs2 h12
    simp only [mem_filter, mem_univ, true_and] at hs1 hs2
    set σ1 := Classical.choose (ex2 s1)
    set σ2 := Classical.choose (ex2 s2)
    have h21 : ∀ k, (σ2.symm * σ1) (s1 k) = s2 k := by
      intro k
      have := congrFun h12 k
      rw [Equiv.Perm.mul_apply, this, Equiv.symm_apply_apply]
    have hr : Rgs (fun k => (σ2.symm * σ1) (s1 k)) := by
      simp only [h21]
      exact hs2.2
    funext k
    rw [← h21 k, rgs_unique s1 (σ2.symm * σ1) hs1.2 hr k]
  · intro t ht
    simp only [mem_filter, mem_univ, true_and] at ht
    obtain ⟨ρ, hρ⟩ := rgs_exists t
    refine ⟨fun k => ρ (t k), ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and]
      exact ⟨(hP ρ t).2 ht.1, hρ⟩
    · set σ := Classical.choose (ex2 (fun k => ρ (t k)))
      have hs : Rgs (fun k => σ (ρ (t (e k)))) := Classical.choose_spec (ex2 (fun k => ρ (t k)))
      have hu := rgs_unique (fun k => t (e k)) (σ * ρ) ht.2 hs
      funext k
      have := hu (e.symm k)
      simp only [Equiv.apply_symm_apply, Equiv.Perm.mul_apply] at this
      exact this

/-- The same for arrays read through two enumerations of their cells. -/
lemma card_reorder_arr {R C N K : ℕ} (e1 e2 : Fin N ≃ Fin R × Fin C)
    (P : (Fin R → Fin C → Fin K) → Prop) [DecidablePred P]
    (hP : ∀ (σ : Equiv.Perm (Fin K)) x, P (fun i j => σ (x i j)) ↔ P x) :
    ((univ : Finset (Fin R → Fin C → Fin K)).filter
        (fun x => P x ∧ Rgs (fun k => x (e1 k).1 (e1 k).2))).card =
      ((univ : Finset (Fin R → Fin C → Fin K)).filter
        (fun x => P x ∧ Rgs (fun k => x (e2 k).1 (e2 k).2))).card := by
  classical
  let Q : (Fin N → Fin K) → Prop := fun s => P (fun i j => s (e1.symm (i, j)))
  have hQ : ∀ (σ : Equiv.Perm (Fin K)) s, Q (fun k => σ (s k)) ↔ Q s := fun σ s => hP σ _
  have key := card_rgs_reorder Q hQ (e2.trans e1.symm)
  have tr : ∀ (G : (Fin N → Fin K) → Prop) [DecidablePred G],
      ((univ : Finset (Fin R → Fin C → Fin K)).filter
          (fun x => G (fun k => x (e1 k).1 (e1 k).2))).card =
        ((univ : Finset (Fin N → Fin K)).filter G).card := by
    intro G _
    refine Finset.card_bij' (fun x _ => fun k => x (e1 k).1 (e1 k).2)
      (fun s _ => fun i j => s (e1.symm (i, j))) ?_ ?_ ?_ ?_
    · intro x hx
      simpa using hx
    · intro s hs
      simp only [mem_filter, mem_univ, true_and] at hs ⊢
      simpa using hs
    · intro x _
      funext i j
      simp
    · intro s _
      funext k
      simp
  have hx1 : ∀ x : Fin R → Fin C → Fin K, P x ↔ Q (fun k => x (e1 k).1 (e1 k).2) := by
    intro x
    simp [Q]
  have hx2 : ∀ x : Fin R → Fin C → Fin K, (fun k => x (e2 k).1 (e2 k).2) =
      (fun k => (fun k => x (e1 k).1 (e1 k).2) ((e2.trans e1.symm) k)) := by
    intro x
    funext k
    simp
  rw [Finset.filter_congr (fun x _ => and_congr_left' (hx1 x)),
    Finset.filter_congr (fun x _ => and_congr (hx1 x) (Iff.of_eq (congrArg Rgs (hx2 x)))),
    tr (fun s => Q s ∧ Rgs s), tr (fun s => Q s ∧ Rgs (fun k => s ((e2.trans e1.symm) k))), key]

/-- The cells of a 2 X (n+1) array in row major order. -/
def eRow (n : ℕ) : Fin (2 * (n + 1)) ≃ Fin 2 × Fin (n + 1) := finProdFinEquiv.symm

/-- The cells of a 2 X (n+1) array in column major order. -/
def eCol (n : ℕ) : Fin (2 * (n + 1)) ≃ Fin 2 × Fin (n + 1) :=
  (finCongr (Nat.mul_comm 2 (n + 1))).trans (finProdFinEquiv.symm.trans (Equiv.prodComm _ _))

lemma eRow_symm_val (n : ℕ) (i : Fin 2) (j : Fin (n + 1)) :
    ((eRow n).symm (i, j)).val = j.val + (n + 1) * i.val := rfl

lemma eCol_symm_val (n : ℕ) (i : Fin 2) (j : Fin (n + 1)) :
    ((eCol n).symm (i, j)).val = i.val + 2 * j.val := rfl

lemma rmn_iff_row {n K : ℕ} (x : Fin 2 → Fin (n + 1) → Fin K) :
    RowMajorNew x ↔ Rgs (fun k => x ((eRow n) k).1 ((eRow n) k).2) := by
  have ord : ∀ (i i' : Fin 2) (j j' : Fin (n + 1)),
      (eRow n).symm (i', j') < (eRow n).symm (i, j) ↔ (i' < i ∨ (i' = i ∧ j' < j)) := by
    intro i i' j j'
    simp only [Fin.lt_def, Fin.ext_iff, eRow_symm_val]
    have hi := i.isLt
    have hi' := i'.isLt
    have hj := j.isLt
    have hj' := j'.isLt
    rcases (by omega : i.val = 0 ∨ i.val = 1) with h | h <;>
      rcases (by omega : i'.val = 0 ∨ i'.val = 1) with h' | h' <;>
      simp only [h, h', true_and] <;> omega
  constructor
  · intro H k u hu
    obtain ⟨i', j', hb, he⟩ := H ((eRow n) k).1 ((eRow n) k).2 u hu
    refine ⟨(eRow n).symm (i', j'), ?_, by simpa using he⟩
    have h := (ord ((eRow n) k).1 i' ((eRow n) k).2 j').2 hb
    simpa using h
  · intro H i j u hu
    obtain ⟨k', hk', he⟩ := H ((eRow n).symm (i, j)) u (by simpa using hu)
    refine ⟨((eRow n) k').1, ((eRow n) k').2, ?_, he⟩
    have h := hk'
    rw [show k' = (eRow n).symm (((eRow n) k').1, ((eRow n) k').2) by simp] at h
    exact (ord i _ j _).1 h

lemma rmn_iff_col {n K : ℕ} (x : Fin 2 → Fin (n + 1) → Fin K) :
    RowMajorNew (fun j i => x i j) ↔ Rgs (fun k => x ((eCol n) k).1 ((eCol n) k).2) := by
  have ord : ∀ (i i' : Fin 2) (j j' : Fin (n + 1)),
      (eCol n).symm (i', j') < (eCol n).symm (i, j) ↔ (j' < j ∨ (j' = j ∧ i' < i)) := by
    intro i i' j j'
    simp only [Fin.lt_def, Fin.ext_iff, eCol_symm_val]
    have hi := i.isLt
    have hi' := i'.isLt
    rcases (by omega : i.val = 0 ∨ i.val = 1) with h | h <;>
      rcases (by omega : i'.val = 0 ∨ i'.val = 1) with h' | h' <;>
      simp only [h, h', true_and] <;> omega
  constructor
  · intro H k u hu
    obtain ⟨j', i', hb, he⟩ := H ((eCol n) k).2 ((eCol n) k).1 u hu
    refine ⟨(eCol n).symm (i', j'), ?_, by simpa using he⟩
    have h := (ord ((eCol n) k).1 i' ((eCol n) k).2 j').2 hb
    simpa using h
  · intro H j i u hu
    obtain ⟨k', hk', he⟩ := H ((eCol n).symm (i, j)) u (by simpa using hu)
    refine ⟨((eCol n) k').2, ((eCol n) k').1, ?_, he⟩
    have h := hk'
    rw [show k' = (eCol n).symm (((eCol n) k').1, ((eCol n) k').2) by simp] at h
    exact (ord i _ j _).1 h

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
  true &&
    (match q with
    | none => true
    | some p =>
      (((if p 0 = r 1 then 1 else 0) + (if r 0 = p 1 then 1 else 0)) == ((if r 0 = t 1 then 1 else 0) + (if t 0 = r 1 then 1 else 0))))

/-- `rowCond q r none` as a Boolean. -/
def endB (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) : Bool :=
  true

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
  [[[5, 5, 10, 16, 16], [10, 10, 10, 16, 16], [0, 0, 16, 16, 16], [0, 0, 0, 16, 16]], [[0, 10, 10, 16, 16], [0, 10, 10, 16, 16], [0, 16, 16, 16, 16], [0, 0, 0, 16, 16]], [[0, 0, 16, 16, 16], [0, 0, 16, 16, 16], [0, 0, 16, 16, 16], [0, 0, 16, 16, 16]], [[0, 0, 0, 16, 16], [0, 0, 0, 16, 16], [0, 0, 0, 16, 16], [0, 0, 0, 16, 16]]]

/-- W(1, some p, r, c) for c <= 4, nested by the entries of p, of r, and then c. -/
def LS1 : List (List (List (List (List ℕ)))) :=
  [[[[[1, 1, 1, 1, 1], [4, 4, 4, 6, 6], [0, 0, 6, 6, 6], [0, 0, 0, 6, 6]], [[0, 4, 4, 6, 6], [0, 5, 5, 9, 9], [0, 9, 9, 9, 9], [0, 0, 0, 9, 9]], [[0, 0, 6, 6, 6], [0, 0, 9, 9, 9], [0, 0, 9, 9, 9], [0, 0, 9, 9, 9]], [[0, 0, 0, 6, 6], [0, 0, 0, 9, 9], [0, 0, 0, 9, 9], [0, 0, 0, 9, 9]]], [[[2, 2, 4, 6, 6], [5, 5, 5, 9, 9], [0, 0, 9, 9, 9], [0, 0, 0, 9, 9]], [[0, 1, 1, 1, 1], [0, 4, 4, 6, 6], [0, 6, 6, 6, 6], [0, 0, 0, 6, 6]], [[0, 0, 6, 6, 6], [0, 0, 9, 9, 9], [0, 0, 9, 9, 9], [0, 0, 9, 9, 9]], [[0, 0, 0, 6, 6], [0, 0, 0, 9, 9], [0, 0, 0, 9, 9], [0, 0, 0, 9, 9]]], [[[2, 2, 4, 6, 6], [5, 5, 5, 9, 9], [0, 0, 9, 9, 9], [0, 0, 0, 9, 9]], [[0, 4, 4, 6, 6], [0, 5, 5, 9, 9], [0, 9, 9, 9, 9], [0, 0, 0, 9, 9]], [[0, 0, 1, 1, 1], [0, 0, 6, 6, 6], [0, 0, 6, 6, 6], [0, 0, 6, 6, 6]], [[0, 0, 0, 6, 6], [0, 0, 0, 9, 9], [0, 0, 0, 9, 9], [0, 0, 0, 9, 9]]], [[[2, 2, 4, 6, 6], [5, 5, 5, 9, 9], [0, 0, 9, 9, 9], [0, 0, 0, 9, 9]], [[0, 4, 4, 6, 6], [0, 5, 5, 9, 9], [0, 9, 9, 9, 9], [0, 0, 0, 9, 9]], [[0, 0, 6, 6, 6], [0, 0, 9, 9, 9], [0, 0, 9, 9, 9], [0, 0, 9, 9, 9]], [[0, 0, 0, 1, 1], [0, 0, 0, 6, 6], [0, 0, 0, 6, 6], [0, 0, 0, 6, 6]]]], [[[[2, 2, 4, 6, 6], [1, 1, 1, 1, 1], [0, 0, 6, 6, 6], [0, 0, 0, 6, 6]], [[0, 5, 5, 9, 9], [0, 4, 4, 6, 6], [0, 9, 9, 9, 9], [0, 0, 0, 9, 9]], [[0, 0, 9, 9, 9], [0, 0, 6, 6, 6], [0, 0, 9, 9, 9], [0, 0, 9, 9, 9]], [[0, 0, 0, 9, 9], [0, 0, 0, 6, 6], [0, 0, 0, 9, 9], [0, 0, 0, 9, 9]]], [[[2, 2, 5, 9, 9], [4, 4, 4, 6, 6], [0, 0, 9, 9, 9], [0, 0, 0, 9, 9]], [[0, 4, 4, 6, 6], [0, 1, 1, 1, 1], [0, 6, 6, 6, 6], [0, 0, 0, 6, 6]], [[0, 0, 9, 9, 9], [0, 0, 6, 6, 6], [0, 0, 9, 9, 9], [0, 0, 9, 9, 9]], [[0, 0, 0, 9, 9], [0, 0, 0, 6, 6], [0, 0, 0, 9, 9], [0, 0, 0, 9, 9]]], [[[2, 2, 5, 9, 9], [4, 4, 4, 6, 6], [0, 0, 9, 9, 9], [0, 0, 0, 9, 9]], [[0, 5, 5, 9, 9], [0, 4, 4, 6, 6], [0, 9, 9, 9, 9], [0, 0, 0, 9, 9]], [[0, 0, 6, 6, 6], [0, 0, 1, 1, 1], [0, 0, 6, 6, 6], [0, 0, 6, 6, 6]], [[0, 0, 0, 9, 9], [0, 0, 0, 6, 6], [0, 0, 0, 9, 9], [0, 0, 0, 9, 9]]], [[[2, 2, 5, 9, 9], [4, 4, 4, 6, 6], [0, 0, 9, 9, 9], [0, 0, 0, 9, 9]], [[0, 5, 5, 9, 9], [0, 4, 4, 6, 6], [0, 9, 9, 9, 9], [0, 0, 0, 9, 9]], [[0, 0, 9, 9, 9], [0, 0, 6, 6, 6], [0, 0, 9, 9, 9], [0, 0, 9, 9, 9]], [[0, 0, 0, 6, 6], [0, 0, 0, 1, 1], [0, 0, 0, 6, 6], [0, 0, 0, 6, 6]]]], [[[[2, 2, 4, 6, 6], [4, 4, 4, 6, 6], [0, 0, 1, 1, 1], [0, 0, 0, 6, 6]], [[0, 5, 5, 9, 9], [0, 5, 5, 9, 9], [0, 6, 6, 6, 6], [0, 0, 0, 9, 9]], [[0, 0, 9, 9, 9], [0, 0, 9, 9, 9], [0, 0, 6, 6, 6], [0, 0, 9, 9, 9]], [[0, 0, 0, 9, 9], [0, 0, 0, 9, 9], [0, 0, 0, 6, 6], [0, 0, 0, 9, 9]]], [[[2, 2, 5, 9, 9], [5, 5, 5, 9, 9], [0, 0, 6, 6, 6], [0, 0, 0, 9, 9]], [[0, 4, 4, 6, 6], [0, 4, 4, 6, 6], [0, 1, 1, 1, 1], [0, 0, 0, 6, 6]], [[0, 0, 9, 9, 9], [0, 0, 9, 9, 9], [0, 0, 6, 6, 6], [0, 0, 9, 9, 9]], [[0, 0, 0, 9, 9], [0, 0, 0, 9, 9], [0, 0, 0, 6, 6], [0, 0, 0, 9, 9]]], [[[2, 2, 5, 9, 9], [5, 5, 5, 9, 9], [0, 0, 6, 6, 6], [0, 0, 0, 9, 9]], [[0, 5, 5, 9, 9], [0, 5, 5, 9, 9], [0, 6, 6, 6, 6], [0, 0, 0, 9, 9]], [[0, 0, 6, 6, 6], [0, 0, 6, 6, 6], [0, 0, 1, 1, 1], [0, 0, 6, 6, 6]], [[0, 0, 0, 9, 9], [0, 0, 0, 9, 9], [0, 0, 0, 6, 6], [0, 0, 0, 9, 9]]], [[[2, 2, 5, 9, 9], [5, 5, 5, 9, 9], [0, 0, 6, 6, 6], [0, 0, 0, 9, 9]], [[0, 5, 5, 9, 9], [0, 5, 5, 9, 9], [0, 6, 6, 6, 6], [0, 0, 0, 9, 9]], [[0, 0, 9, 9, 9], [0, 0, 9, 9, 9], [0, 0, 6, 6, 6], [0, 0, 9, 9, 9]], [[0, 0, 0, 6, 6], [0, 0, 0, 6, 6], [0, 0, 0, 1, 1], [0, 0, 0, 6, 6]]]], [[[[2, 2, 4, 6, 6], [4, 4, 4, 6, 6], [0, 0, 6, 6, 6], [0, 0, 0, 1, 1]], [[0, 5, 5, 9, 9], [0, 5, 5, 9, 9], [0, 9, 9, 9, 9], [0, 0, 0, 6, 6]], [[0, 0, 9, 9, 9], [0, 0, 9, 9, 9], [0, 0, 9, 9, 9], [0, 0, 6, 6, 6]], [[0, 0, 0, 9, 9], [0, 0, 0, 9, 9], [0, 0, 0, 9, 9], [0, 0, 0, 6, 6]]], [[[2, 2, 5, 9, 9], [5, 5, 5, 9, 9], [0, 0, 9, 9, 9], [0, 0, 0, 6, 6]], [[0, 4, 4, 6, 6], [0, 4, 4, 6, 6], [0, 6, 6, 6, 6], [0, 0, 0, 1, 1]], [[0, 0, 9, 9, 9], [0, 0, 9, 9, 9], [0, 0, 9, 9, 9], [0, 0, 6, 6, 6]], [[0, 0, 0, 9, 9], [0, 0, 0, 9, 9], [0, 0, 0, 9, 9], [0, 0, 0, 6, 6]]], [[[2, 2, 5, 9, 9], [5, 5, 5, 9, 9], [0, 0, 9, 9, 9], [0, 0, 0, 6, 6]], [[0, 5, 5, 9, 9], [0, 5, 5, 9, 9], [0, 9, 9, 9, 9], [0, 0, 0, 6, 6]], [[0, 0, 6, 6, 6], [0, 0, 6, 6, 6], [0, 0, 6, 6, 6], [0, 0, 1, 1, 1]], [[0, 0, 0, 9, 9], [0, 0, 0, 9, 9], [0, 0, 0, 9, 9], [0, 0, 0, 6, 6]]], [[[2, 2, 5, 9, 9], [5, 5, 5, 9, 9], [0, 0, 9, 9, 9], [0, 0, 0, 6, 6]], [[0, 5, 5, 9, 9], [0, 5, 5, 9, 9], [0, 9, 9, 9, 9], [0, 0, 0, 6, 6]], [[0, 0, 9, 9, 9], [0, 0, 9, 9, 9], [0, 0, 9, 9, 9], [0, 0, 6, 6, 6]], [[0, 0, 0, 6, 6], [0, 0, 0, 6, 6], [0, 0, 0, 6, 6], [0, 0, 0, 1, 1]]]]]

/-- W(1) as a table. -/
def tab1 (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (c : ℕ) : ℕ :=
  match q with
  | none => ((LN1.getD (r 0).val []).getD (r 1).val []).getD c 0
  | some p => ((((LS1.getD (p 0).val []).getD (p 1).val []).getD (r 0).val []).getD (r 1).val []).getD c 0

/-- W(2, none, r, c) for c <= 4, nested by the entries of r and then c. -/
def LN2 : List (List (List ℕ)) :=
  [[[23, 23, 62, 118, 118], [62, 62, 62, 118, 118], [0, 0, 118, 118, 118], [0, 0, 0, 118, 118]], [[0, 62, 62, 118, 118], [0, 62, 62, 118, 118], [0, 118, 118, 118, 118], [0, 0, 0, 118, 118]], [[0, 0, 118, 118, 118], [0, 0, 118, 118, 118], [0, 0, 118, 118, 118], [0, 0, 118, 118, 118]], [[0, 0, 0, 118, 118], [0, 0, 0, 118, 118], [0, 0, 0, 118, 118], [0, 0, 0, 118, 118]]]

/-- W(2, some p, r, c) for c <= 4, nested by the entries of p, of r, and then c. -/
def LS2 : List (List (List (List (List ℕ)))) :=
  [[[[[1, 1, 1, 1, 1], [20, 20, 20, 36, 36], [0, 0, 36, 36, 36], [0, 0, 0, 36, 36]], [[0, 20, 20, 36, 36], [0, 41, 41, 81, 81], [0, 81, 81, 81, 81], [0, 0, 0, 81, 81]], [[0, 0, 36, 36, 36], [0, 0, 81, 81, 81], [0, 0, 81, 81, 81], [0, 0, 81, 81, 81]], [[0, 0, 0, 36, 36], [0, 0, 0, 81, 81], [0, 0, 0, 81, 81], [0, 0, 0, 81, 81]]], [[[8, 8, 20, 36, 36], [41, 41, 41, 81, 81], [0, 0, 81, 81, 81], [0, 0, 0, 81, 81]], [[0, 1, 1, 1, 1], [0, 20, 20, 36, 36], [0, 36, 36, 36, 36], [0, 0, 0, 36, 36]], [[0, 0, 36, 36, 36], [0, 0, 81, 81, 81], [0, 0, 81, 81, 81], [0, 0, 81, 81, 81]], [[0, 0, 0, 36, 36], [0, 0, 0, 81, 81], [0, 0, 0, 81, 81], [0, 0, 0, 81, 81]]], [[[8, 8, 20, 36, 36], [41, 41, 41, 81, 81], [0, 0, 81, 81, 81], [0, 0, 0, 81, 81]], [[0, 20, 20, 36, 36], [0, 41, 41, 81, 81], [0, 81, 81, 81, 81], [0, 0, 0, 81, 81]], [[0, 0, 1, 1, 1], [0, 0, 36, 36, 36], [0, 0, 36, 36, 36], [0, 0, 36, 36, 36]], [[0, 0, 0, 36, 36], [0, 0, 0, 81, 81], [0, 0, 0, 81, 81], [0, 0, 0, 81, 81]]], [[[8, 8, 20, 36, 36], [41, 41, 41, 81, 81], [0, 0, 81, 81, 81], [0, 0, 0, 81, 81]], [[0, 20, 20, 36, 36], [0, 41, 41, 81, 81], [0, 81, 81, 81, 81], [0, 0, 0, 81, 81]], [[0, 0, 36, 36, 36], [0, 0, 81, 81, 81], [0, 0, 81, 81, 81], [0, 0, 81, 81, 81]], [[0, 0, 0, 1, 1], [0, 0, 0, 36, 36], [0, 0, 0, 36, 36], [0, 0, 0, 36, 36]]]], [[[[8, 8, 20, 36, 36], [1, 1, 1, 1, 1], [0, 0, 36, 36, 36], [0, 0, 0, 36, 36]], [[0, 41, 41, 81, 81], [0, 20, 20, 36, 36], [0, 81, 81, 81, 81], [0, 0, 0, 81, 81]], [[0, 0, 81, 81, 81], [0, 0, 36, 36, 36], [0, 0, 81, 81, 81], [0, 0, 81, 81, 81]], [[0, 0, 0, 81, 81], [0, 0, 0, 36, 36], [0, 0, 0, 81, 81], [0, 0, 0, 81, 81]]], [[[14, 14, 41, 81, 81], [20, 20, 20, 36, 36], [0, 0, 81, 81, 81], [0, 0, 0, 81, 81]], [[0, 20, 20, 36, 36], [0, 1, 1, 1, 1], [0, 36, 36, 36, 36], [0, 0, 0, 36, 36]], [[0, 0, 81, 81, 81], [0, 0, 36, 36, 36], [0, 0, 81, 81, 81], [0, 0, 81, 81, 81]], [[0, 0, 0, 81, 81], [0, 0, 0, 36, 36], [0, 0, 0, 81, 81], [0, 0, 0, 81, 81]]], [[[14, 14, 41, 81, 81], [20, 20, 20, 36, 36], [0, 0, 81, 81, 81], [0, 0, 0, 81, 81]], [[0, 41, 41, 81, 81], [0, 20, 20, 36, 36], [0, 81, 81, 81, 81], [0, 0, 0, 81, 81]], [[0, 0, 36, 36, 36], [0, 0, 1, 1, 1], [0, 0, 36, 36, 36], [0, 0, 36, 36, 36]], [[0, 0, 0, 81, 81], [0, 0, 0, 36, 36], [0, 0, 0, 81, 81], [0, 0, 0, 81, 81]]], [[[14, 14, 41, 81, 81], [20, 20, 20, 36, 36], [0, 0, 81, 81, 81], [0, 0, 0, 81, 81]], [[0, 41, 41, 81, 81], [0, 20, 20, 36, 36], [0, 81, 81, 81, 81], [0, 0, 0, 81, 81]], [[0, 0, 81, 81, 81], [0, 0, 36, 36, 36], [0, 0, 81, 81, 81], [0, 0, 81, 81, 81]], [[0, 0, 0, 36, 36], [0, 0, 0, 1, 1], [0, 0, 0, 36, 36], [0, 0, 0, 36, 36]]]], [[[[8, 8, 20, 36, 36], [20, 20, 20, 36, 36], [0, 0, 1, 1, 1], [0, 0, 0, 36, 36]], [[0, 41, 41, 81, 81], [0, 41, 41, 81, 81], [0, 36, 36, 36, 36], [0, 0, 0, 81, 81]], [[0, 0, 81, 81, 81], [0, 0, 81, 81, 81], [0, 0, 36, 36, 36], [0, 0, 81, 81, 81]], [[0, 0, 0, 81, 81], [0, 0, 0, 81, 81], [0, 0, 0, 36, 36], [0, 0, 0, 81, 81]]], [[[14, 14, 41, 81, 81], [41, 41, 41, 81, 81], [0, 0, 36, 36, 36], [0, 0, 0, 81, 81]], [[0, 20, 20, 36, 36], [0, 20, 20, 36, 36], [0, 1, 1, 1, 1], [0, 0, 0, 36, 36]], [[0, 0, 81, 81, 81], [0, 0, 81, 81, 81], [0, 0, 36, 36, 36], [0, 0, 81, 81, 81]], [[0, 0, 0, 81, 81], [0, 0, 0, 81, 81], [0, 0, 0, 36, 36], [0, 0, 0, 81, 81]]], [[[14, 14, 41, 81, 81], [41, 41, 41, 81, 81], [0, 0, 36, 36, 36], [0, 0, 0, 81, 81]], [[0, 41, 41, 81, 81], [0, 41, 41, 81, 81], [0, 36, 36, 36, 36], [0, 0, 0, 81, 81]], [[0, 0, 36, 36, 36], [0, 0, 36, 36, 36], [0, 0, 1, 1, 1], [0, 0, 36, 36, 36]], [[0, 0, 0, 81, 81], [0, 0, 0, 81, 81], [0, 0, 0, 36, 36], [0, 0, 0, 81, 81]]], [[[14, 14, 41, 81, 81], [41, 41, 41, 81, 81], [0, 0, 36, 36, 36], [0, 0, 0, 81, 81]], [[0, 41, 41, 81, 81], [0, 41, 41, 81, 81], [0, 36, 36, 36, 36], [0, 0, 0, 81, 81]], [[0, 0, 81, 81, 81], [0, 0, 81, 81, 81], [0, 0, 36, 36, 36], [0, 0, 81, 81, 81]], [[0, 0, 0, 36, 36], [0, 0, 0, 36, 36], [0, 0, 0, 1, 1], [0, 0, 0, 36, 36]]]], [[[[8, 8, 20, 36, 36], [20, 20, 20, 36, 36], [0, 0, 36, 36, 36], [0, 0, 0, 1, 1]], [[0, 41, 41, 81, 81], [0, 41, 41, 81, 81], [0, 81, 81, 81, 81], [0, 0, 0, 36, 36]], [[0, 0, 81, 81, 81], [0, 0, 81, 81, 81], [0, 0, 81, 81, 81], [0, 0, 36, 36, 36]], [[0, 0, 0, 81, 81], [0, 0, 0, 81, 81], [0, 0, 0, 81, 81], [0, 0, 0, 36, 36]]], [[[14, 14, 41, 81, 81], [41, 41, 41, 81, 81], [0, 0, 81, 81, 81], [0, 0, 0, 36, 36]], [[0, 20, 20, 36, 36], [0, 20, 20, 36, 36], [0, 36, 36, 36, 36], [0, 0, 0, 1, 1]], [[0, 0, 81, 81, 81], [0, 0, 81, 81, 81], [0, 0, 81, 81, 81], [0, 0, 36, 36, 36]], [[0, 0, 0, 81, 81], [0, 0, 0, 81, 81], [0, 0, 0, 81, 81], [0, 0, 0, 36, 36]]], [[[14, 14, 41, 81, 81], [41, 41, 41, 81, 81], [0, 0, 81, 81, 81], [0, 0, 0, 36, 36]], [[0, 41, 41, 81, 81], [0, 41, 41, 81, 81], [0, 81, 81, 81, 81], [0, 0, 0, 36, 36]], [[0, 0, 36, 36, 36], [0, 0, 36, 36, 36], [0, 0, 36, 36, 36], [0, 0, 1, 1, 1]], [[0, 0, 0, 81, 81], [0, 0, 0, 81, 81], [0, 0, 0, 81, 81], [0, 0, 0, 36, 36]]], [[[14, 14, 41, 81, 81], [41, 41, 41, 81, 81], [0, 0, 81, 81, 81], [0, 0, 0, 36, 36]], [[0, 41, 41, 81, 81], [0, 41, 41, 81, 81], [0, 81, 81, 81, 81], [0, 0, 0, 36, 36]], [[0, 0, 81, 81, 81], [0, 0, 81, 81, 81], [0, 0, 81, 81, 81], [0, 0, 36, 36, 36]], [[0, 0, 0, 36, 36], [0, 0, 0, 36, 36], [0, 0, 0, 36, 36], [0, 0, 0, 1, 1]]]]]

/-- W(2) as a table. -/
def tab2 (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (c : ℕ) : ℕ :=
  match q with
  | none => ((LN2.getD (r 0).val []).getD (r 1).val []).getD c 0
  | some p => ((((LS2.getD (p 0).val []).getD (p 1).val []).getD (r 0).val []).getD (r 1).val []).getD c 0

/-- W(3, none, r, c) for c <= 4, nested by the entries of r and then c. -/
def LN3 : List (List (List ℕ)) :=
  [[[163, 163, 478, 946, 946], [478, 478, 478, 946, 946], [0, 0, 946, 946, 946], [0, 0, 0, 946, 946]], [[0, 478, 478, 946, 946], [0, 478, 478, 946, 946], [0, 946, 946, 946, 946], [0, 0, 0, 946, 946]], [[0, 0, 946, 946, 946], [0, 0, 946, 946, 946], [0, 0, 946, 946, 946], [0, 0, 946, 946, 946]], [[0, 0, 0, 946, 946], [0, 0, 0, 946, 946], [0, 0, 0, 946, 946], [0, 0, 0, 946, 946]]]

/-- W(3, some p, r, c) for c <= 4, nested by the entries of p, of r, and then c. -/
def LS3 : List (List (List (List (List ℕ)))) :=
  [[[[[1, 1, 1, 1, 1], [112, 112, 112, 216, 216], [0, 0, 216, 216, 216], [0, 0, 0, 216, 216]], [[0, 112, 112, 216, 216], [0, 365, 365, 729, 729], [0, 729, 729, 729, 729], [0, 0, 0, 729, 729]], [[0, 0, 216, 216, 216], [0, 0, 729, 729, 729], [0, 0, 729, 729, 729], [0, 0, 729, 729, 729]], [[0, 0, 0, 216, 216], [0, 0, 0, 729, 729], [0, 0, 0, 729, 729], [0, 0, 0, 729, 729]]], [[[40, 40, 112, 216, 216], [365, 365, 365, 729, 729], [0, 0, 729, 729, 729], [0, 0, 0, 729, 729]], [[0, 1, 1, 1, 1], [0, 112, 112, 216, 216], [0, 216, 216, 216, 216], [0, 0, 0, 216, 216]], [[0, 0, 216, 216, 216], [0, 0, 729, 729, 729], [0, 0, 729, 729, 729], [0, 0, 729, 729, 729]], [[0, 0, 0, 216, 216], [0, 0, 0, 729, 729], [0, 0, 0, 729, 729], [0, 0, 0, 729, 729]]], [[[40, 40, 112, 216, 216], [365, 365, 365, 729, 729], [0, 0, 729, 729, 729], [0, 0, 0, 729, 729]], [[0, 112, 112, 216, 216], [0, 365, 365, 729, 729], [0, 729, 729, 729, 729], [0, 0, 0, 729, 729]], [[0, 0, 1, 1, 1], [0, 0, 216, 216, 216], [0, 0, 216, 216, 216], [0, 0, 216, 216, 216]], [[0, 0, 0, 216, 216], [0, 0, 0, 729, 729], [0, 0, 0, 729, 729], [0, 0, 0, 729, 729]]], [[[40, 40, 112, 216, 216], [365, 365, 365, 729, 729], [0, 0, 729, 729, 729], [0, 0, 0, 729, 729]], [[0, 112, 112, 216, 216], [0, 365, 365, 729, 729], [0, 729, 729, 729, 729], [0, 0, 0, 729, 729]], [[0, 0, 216, 216, 216], [0, 0, 729, 729, 729], [0, 0, 729, 729, 729], [0, 0, 729, 729, 729]], [[0, 0, 0, 1, 1], [0, 0, 0, 216, 216], [0, 0, 0, 216, 216], [0, 0, 0, 216, 216]]]], [[[[40, 40, 112, 216, 216], [1, 1, 1, 1, 1], [0, 0, 216, 216, 216], [0, 0, 0, 216, 216]], [[0, 365, 365, 729, 729], [0, 112, 112, 216, 216], [0, 729, 729, 729, 729], [0, 0, 0, 729, 729]], [[0, 0, 729, 729, 729], [0, 0, 216, 216, 216], [0, 0, 729, 729, 729], [0, 0, 729, 729, 729]], [[0, 0, 0, 729, 729], [0, 0, 0, 216, 216], [0, 0, 0, 729, 729], [0, 0, 0, 729, 729]]], [[[122, 122, 365, 729, 729], [112, 112, 112, 216, 216], [0, 0, 729, 729, 729], [0, 0, 0, 729, 729]], [[0, 112, 112, 216, 216], [0, 1, 1, 1, 1], [0, 216, 216, 216, 216], [0, 0, 0, 216, 216]], [[0, 0, 729, 729, 729], [0, 0, 216, 216, 216], [0, 0, 729, 729, 729], [0, 0, 729, 729, 729]], [[0, 0, 0, 729, 729], [0, 0, 0, 216, 216], [0, 0, 0, 729, 729], [0, 0, 0, 729, 729]]], [[[122, 122, 365, 729, 729], [112, 112, 112, 216, 216], [0, 0, 729, 729, 729], [0, 0, 0, 729, 729]], [[0, 365, 365, 729, 729], [0, 112, 112, 216, 216], [0, 729, 729, 729, 729], [0, 0, 0, 729, 729]], [[0, 0, 216, 216, 216], [0, 0, 1, 1, 1], [0, 0, 216, 216, 216], [0, 0, 216, 216, 216]], [[0, 0, 0, 729, 729], [0, 0, 0, 216, 216], [0, 0, 0, 729, 729], [0, 0, 0, 729, 729]]], [[[122, 122, 365, 729, 729], [112, 112, 112, 216, 216], [0, 0, 729, 729, 729], [0, 0, 0, 729, 729]], [[0, 365, 365, 729, 729], [0, 112, 112, 216, 216], [0, 729, 729, 729, 729], [0, 0, 0, 729, 729]], [[0, 0, 729, 729, 729], [0, 0, 216, 216, 216], [0, 0, 729, 729, 729], [0, 0, 729, 729, 729]], [[0, 0, 0, 216, 216], [0, 0, 0, 1, 1], [0, 0, 0, 216, 216], [0, 0, 0, 216, 216]]]], [[[[40, 40, 112, 216, 216], [112, 112, 112, 216, 216], [0, 0, 1, 1, 1], [0, 0, 0, 216, 216]], [[0, 365, 365, 729, 729], [0, 365, 365, 729, 729], [0, 216, 216, 216, 216], [0, 0, 0, 729, 729]], [[0, 0, 729, 729, 729], [0, 0, 729, 729, 729], [0, 0, 216, 216, 216], [0, 0, 729, 729, 729]], [[0, 0, 0, 729, 729], [0, 0, 0, 729, 729], [0, 0, 0, 216, 216], [0, 0, 0, 729, 729]]], [[[122, 122, 365, 729, 729], [365, 365, 365, 729, 729], [0, 0, 216, 216, 216], [0, 0, 0, 729, 729]], [[0, 112, 112, 216, 216], [0, 112, 112, 216, 216], [0, 1, 1, 1, 1], [0, 0, 0, 216, 216]], [[0, 0, 729, 729, 729], [0, 0, 729, 729, 729], [0, 0, 216, 216, 216], [0, 0, 729, 729, 729]], [[0, 0, 0, 729, 729], [0, 0, 0, 729, 729], [0, 0, 0, 216, 216], [0, 0, 0, 729, 729]]], [[[122, 122, 365, 729, 729], [365, 365, 365, 729, 729], [0, 0, 216, 216, 216], [0, 0, 0, 729, 729]], [[0, 365, 365, 729, 729], [0, 365, 365, 729, 729], [0, 216, 216, 216, 216], [0, 0, 0, 729, 729]], [[0, 0, 216, 216, 216], [0, 0, 216, 216, 216], [0, 0, 1, 1, 1], [0, 0, 216, 216, 216]], [[0, 0, 0, 729, 729], [0, 0, 0, 729, 729], [0, 0, 0, 216, 216], [0, 0, 0, 729, 729]]], [[[122, 122, 365, 729, 729], [365, 365, 365, 729, 729], [0, 0, 216, 216, 216], [0, 0, 0, 729, 729]], [[0, 365, 365, 729, 729], [0, 365, 365, 729, 729], [0, 216, 216, 216, 216], [0, 0, 0, 729, 729]], [[0, 0, 729, 729, 729], [0, 0, 729, 729, 729], [0, 0, 216, 216, 216], [0, 0, 729, 729, 729]], [[0, 0, 0, 216, 216], [0, 0, 0, 216, 216], [0, 0, 0, 1, 1], [0, 0, 0, 216, 216]]]], [[[[40, 40, 112, 216, 216], [112, 112, 112, 216, 216], [0, 0, 216, 216, 216], [0, 0, 0, 1, 1]], [[0, 365, 365, 729, 729], [0, 365, 365, 729, 729], [0, 729, 729, 729, 729], [0, 0, 0, 216, 216]], [[0, 0, 729, 729, 729], [0, 0, 729, 729, 729], [0, 0, 729, 729, 729], [0, 0, 216, 216, 216]], [[0, 0, 0, 729, 729], [0, 0, 0, 729, 729], [0, 0, 0, 729, 729], [0, 0, 0, 216, 216]]], [[[122, 122, 365, 729, 729], [365, 365, 365, 729, 729], [0, 0, 729, 729, 729], [0, 0, 0, 216, 216]], [[0, 112, 112, 216, 216], [0, 112, 112, 216, 216], [0, 216, 216, 216, 216], [0, 0, 0, 1, 1]], [[0, 0, 729, 729, 729], [0, 0, 729, 729, 729], [0, 0, 729, 729, 729], [0, 0, 216, 216, 216]], [[0, 0, 0, 729, 729], [0, 0, 0, 729, 729], [0, 0, 0, 729, 729], [0, 0, 0, 216, 216]]], [[[122, 122, 365, 729, 729], [365, 365, 365, 729, 729], [0, 0, 729, 729, 729], [0, 0, 0, 216, 216]], [[0, 365, 365, 729, 729], [0, 365, 365, 729, 729], [0, 729, 729, 729, 729], [0, 0, 0, 216, 216]], [[0, 0, 216, 216, 216], [0, 0, 216, 216, 216], [0, 0, 216, 216, 216], [0, 0, 1, 1, 1]], [[0, 0, 0, 729, 729], [0, 0, 0, 729, 729], [0, 0, 0, 729, 729], [0, 0, 0, 216, 216]]], [[[122, 122, 365, 729, 729], [365, 365, 365, 729, 729], [0, 0, 729, 729, 729], [0, 0, 0, 216, 216]], [[0, 365, 365, 729, 729], [0, 365, 365, 729, 729], [0, 729, 729, 729, 729], [0, 0, 0, 216, 216]], [[0, 0, 729, 729, 729], [0, 0, 729, 729, 729], [0, 0, 729, 729, 729], [0, 0, 216, 216, 216]], [[0, 0, 0, 216, 216], [0, 0, 0, 216, 216], [0, 0, 0, 216, 216], [0, 0, 0, 1, 1]]]]]

/-- W(3) as a table. -/
def tab3 (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (c : ℕ) : ℕ :=
  match q with
  | none => ((LN3.getD (r 0).val []).getD (r 1).val []).getD c 0
  | some p => ((((LS3.getD (p 0).val []).getD (p 1).val []).getD (r 0).val []).getD (r 1).val []).getD c 0

/-- W(4, none, r, c) for c <= 4, nested by the entries of r and then c. -/
def LN4 : List (List (List ℕ)) :=
  [[[1319, 1319, 3938, 7858, 7858], [3938, 3938, 3938, 7858, 7858], [0, 0, 7858, 7858, 7858], [0, 0, 0, 7858, 7858]], [[0, 3938, 3938, 7858, 7858], [0, 3938, 3938, 7858, 7858], [0, 7858, 7858, 7858, 7858], [0, 0, 0, 7858, 7858]], [[0, 0, 7858, 7858, 7858], [0, 0, 7858, 7858, 7858], [0, 0, 7858, 7858, 7858], [0, 0, 7858, 7858, 7858]], [[0, 0, 0, 7858, 7858], [0, 0, 0, 7858, 7858], [0, 0, 0, 7858, 7858], [0, 0, 0, 7858, 7858]]]

/-- W(4, some p, r, c) for c <= 4, nested by the entries of p, of r, and then c. -/
def LS4 : List (List (List (List (List ℕ)))) :=
  [[[[[1, 1, 1, 1, 1], [656, 656, 656, 1296, 1296], [0, 0, 1296, 1296, 1296], [0, 0, 0, 1296, 1296]], [[0, 656, 656, 1296, 1296], [0, 3281, 3281, 6561, 6561], [0, 6561, 6561, 6561, 6561], [0, 0, 0, 6561, 6561]], [[0, 0, 1296, 1296, 1296], [0, 0, 6561, 6561, 6561], [0, 0, 6561, 6561, 6561], [0, 0, 6561, 6561, 6561]], [[0, 0, 0, 1296, 1296], [0, 0, 0, 6561, 6561], [0, 0, 0, 6561, 6561], [0, 0, 0, 6561, 6561]]], [[[224, 224, 656, 1296, 1296], [3281, 3281, 3281, 6561, 6561], [0, 0, 6561, 6561, 6561], [0, 0, 0, 6561, 6561]], [[0, 1, 1, 1, 1], [0, 656, 656, 1296, 1296], [0, 1296, 1296, 1296, 1296], [0, 0, 0, 1296, 1296]], [[0, 0, 1296, 1296, 1296], [0, 0, 6561, 6561, 6561], [0, 0, 6561, 6561, 6561], [0, 0, 6561, 6561, 6561]], [[0, 0, 0, 1296, 1296], [0, 0, 0, 6561, 6561], [0, 0, 0, 6561, 6561], [0, 0, 0, 6561, 6561]]], [[[224, 224, 656, 1296, 1296], [3281, 3281, 3281, 6561, 6561], [0, 0, 6561, 6561, 6561], [0, 0, 0, 6561, 6561]], [[0, 656, 656, 1296, 1296], [0, 3281, 3281, 6561, 6561], [0, 6561, 6561, 6561, 6561], [0, 0, 0, 6561, 6561]], [[0, 0, 1, 1, 1], [0, 0, 1296, 1296, 1296], [0, 0, 1296, 1296, 1296], [0, 0, 1296, 1296, 1296]], [[0, 0, 0, 1296, 1296], [0, 0, 0, 6561, 6561], [0, 0, 0, 6561, 6561], [0, 0, 0, 6561, 6561]]], [[[224, 224, 656, 1296, 1296], [3281, 3281, 3281, 6561, 6561], [0, 0, 6561, 6561, 6561], [0, 0, 0, 6561, 6561]], [[0, 656, 656, 1296, 1296], [0, 3281, 3281, 6561, 6561], [0, 6561, 6561, 6561, 6561], [0, 0, 0, 6561, 6561]], [[0, 0, 1296, 1296, 1296], [0, 0, 6561, 6561, 6561], [0, 0, 6561, 6561, 6561], [0, 0, 6561, 6561, 6561]], [[0, 0, 0, 1, 1], [0, 0, 0, 1296, 1296], [0, 0, 0, 1296, 1296], [0, 0, 0, 1296, 1296]]]], [[[[224, 224, 656, 1296, 1296], [1, 1, 1, 1, 1], [0, 0, 1296, 1296, 1296], [0, 0, 0, 1296, 1296]], [[0, 3281, 3281, 6561, 6561], [0, 656, 656, 1296, 1296], [0, 6561, 6561, 6561, 6561], [0, 0, 0, 6561, 6561]], [[0, 0, 6561, 6561, 6561], [0, 0, 1296, 1296, 1296], [0, 0, 6561, 6561, 6561], [0, 0, 6561, 6561, 6561]], [[0, 0, 0, 6561, 6561], [0, 0, 0, 1296, 1296], [0, 0, 0, 6561, 6561], [0, 0, 0, 6561, 6561]]], [[[1094, 1094, 3281, 6561, 6561], [656, 656, 656, 1296, 1296], [0, 0, 6561, 6561, 6561], [0, 0, 0, 6561, 6561]], [[0, 656, 656, 1296, 1296], [0, 1, 1, 1, 1], [0, 1296, 1296, 1296, 1296], [0, 0, 0, 1296, 1296]], [[0, 0, 6561, 6561, 6561], [0, 0, 1296, 1296, 1296], [0, 0, 6561, 6561, 6561], [0, 0, 6561, 6561, 6561]], [[0, 0, 0, 6561, 6561], [0, 0, 0, 1296, 1296], [0, 0, 0, 6561, 6561], [0, 0, 0, 6561, 6561]]], [[[1094, 1094, 3281, 6561, 6561], [656, 656, 656, 1296, 1296], [0, 0, 6561, 6561, 6561], [0, 0, 0, 6561, 6561]], [[0, 3281, 3281, 6561, 6561], [0, 656, 656, 1296, 1296], [0, 6561, 6561, 6561, 6561], [0, 0, 0, 6561, 6561]], [[0, 0, 1296, 1296, 1296], [0, 0, 1, 1, 1], [0, 0, 1296, 1296, 1296], [0, 0, 1296, 1296, 1296]], [[0, 0, 0, 6561, 6561], [0, 0, 0, 1296, 1296], [0, 0, 0, 6561, 6561], [0, 0, 0, 6561, 6561]]], [[[1094, 1094, 3281, 6561, 6561], [656, 656, 656, 1296, 1296], [0, 0, 6561, 6561, 6561], [0, 0, 0, 6561, 6561]], [[0, 3281, 3281, 6561, 6561], [0, 656, 656, 1296, 1296], [0, 6561, 6561, 6561, 6561], [0, 0, 0, 6561, 6561]], [[0, 0, 6561, 6561, 6561], [0, 0, 1296, 1296, 1296], [0, 0, 6561, 6561, 6561], [0, 0, 6561, 6561, 6561]], [[0, 0, 0, 1296, 1296], [0, 0, 0, 1, 1], [0, 0, 0, 1296, 1296], [0, 0, 0, 1296, 1296]]]], [[[[224, 224, 656, 1296, 1296], [656, 656, 656, 1296, 1296], [0, 0, 1, 1, 1], [0, 0, 0, 1296, 1296]], [[0, 3281, 3281, 6561, 6561], [0, 3281, 3281, 6561, 6561], [0, 1296, 1296, 1296, 1296], [0, 0, 0, 6561, 6561]], [[0, 0, 6561, 6561, 6561], [0, 0, 6561, 6561, 6561], [0, 0, 1296, 1296, 1296], [0, 0, 6561, 6561, 6561]], [[0, 0, 0, 6561, 6561], [0, 0, 0, 6561, 6561], [0, 0, 0, 1296, 1296], [0, 0, 0, 6561, 6561]]], [[[1094, 1094, 3281, 6561, 6561], [3281, 3281, 3281, 6561, 6561], [0, 0, 1296, 1296, 1296], [0, 0, 0, 6561, 6561]], [[0, 656, 656, 1296, 1296], [0, 656, 656, 1296, 1296], [0, 1, 1, 1, 1], [0, 0, 0, 1296, 1296]], [[0, 0, 6561, 6561, 6561], [0, 0, 6561, 6561, 6561], [0, 0, 1296, 1296, 1296], [0, 0, 6561, 6561, 6561]], [[0, 0, 0, 6561, 6561], [0, 0, 0, 6561, 6561], [0, 0, 0, 1296, 1296], [0, 0, 0, 6561, 6561]]], [[[1094, 1094, 3281, 6561, 6561], [3281, 3281, 3281, 6561, 6561], [0, 0, 1296, 1296, 1296], [0, 0, 0, 6561, 6561]], [[0, 3281, 3281, 6561, 6561], [0, 3281, 3281, 6561, 6561], [0, 1296, 1296, 1296, 1296], [0, 0, 0, 6561, 6561]], [[0, 0, 1296, 1296, 1296], [0, 0, 1296, 1296, 1296], [0, 0, 1, 1, 1], [0, 0, 1296, 1296, 1296]], [[0, 0, 0, 6561, 6561], [0, 0, 0, 6561, 6561], [0, 0, 0, 1296, 1296], [0, 0, 0, 6561, 6561]]], [[[1094, 1094, 3281, 6561, 6561], [3281, 3281, 3281, 6561, 6561], [0, 0, 1296, 1296, 1296], [0, 0, 0, 6561, 6561]], [[0, 3281, 3281, 6561, 6561], [0, 3281, 3281, 6561, 6561], [0, 1296, 1296, 1296, 1296], [0, 0, 0, 6561, 6561]], [[0, 0, 6561, 6561, 6561], [0, 0, 6561, 6561, 6561], [0, 0, 1296, 1296, 1296], [0, 0, 6561, 6561, 6561]], [[0, 0, 0, 1296, 1296], [0, 0, 0, 1296, 1296], [0, 0, 0, 1, 1], [0, 0, 0, 1296, 1296]]]], [[[[224, 224, 656, 1296, 1296], [656, 656, 656, 1296, 1296], [0, 0, 1296, 1296, 1296], [0, 0, 0, 1, 1]], [[0, 3281, 3281, 6561, 6561], [0, 3281, 3281, 6561, 6561], [0, 6561, 6561, 6561, 6561], [0, 0, 0, 1296, 1296]], [[0, 0, 6561, 6561, 6561], [0, 0, 6561, 6561, 6561], [0, 0, 6561, 6561, 6561], [0, 0, 1296, 1296, 1296]], [[0, 0, 0, 6561, 6561], [0, 0, 0, 6561, 6561], [0, 0, 0, 6561, 6561], [0, 0, 0, 1296, 1296]]], [[[1094, 1094, 3281, 6561, 6561], [3281, 3281, 3281, 6561, 6561], [0, 0, 6561, 6561, 6561], [0, 0, 0, 1296, 1296]], [[0, 656, 656, 1296, 1296], [0, 656, 656, 1296, 1296], [0, 1296, 1296, 1296, 1296], [0, 0, 0, 1, 1]], [[0, 0, 6561, 6561, 6561], [0, 0, 6561, 6561, 6561], [0, 0, 6561, 6561, 6561], [0, 0, 1296, 1296, 1296]], [[0, 0, 0, 6561, 6561], [0, 0, 0, 6561, 6561], [0, 0, 0, 6561, 6561], [0, 0, 0, 1296, 1296]]], [[[1094, 1094, 3281, 6561, 6561], [3281, 3281, 3281, 6561, 6561], [0, 0, 6561, 6561, 6561], [0, 0, 0, 1296, 1296]], [[0, 3281, 3281, 6561, 6561], [0, 3281, 3281, 6561, 6561], [0, 6561, 6561, 6561, 6561], [0, 0, 0, 1296, 1296]], [[0, 0, 1296, 1296, 1296], [0, 0, 1296, 1296, 1296], [0, 0, 1296, 1296, 1296], [0, 0, 1, 1, 1]], [[0, 0, 0, 6561, 6561], [0, 0, 0, 6561, 6561], [0, 0, 0, 6561, 6561], [0, 0, 0, 1296, 1296]]], [[[1094, 1094, 3281, 6561, 6561], [3281, 3281, 3281, 6561, 6561], [0, 0, 6561, 6561, 6561], [0, 0, 0, 1296, 1296]], [[0, 3281, 3281, 6561, 6561], [0, 3281, 3281, 6561, 6561], [0, 6561, 6561, 6561, 6561], [0, 0, 0, 1296, 1296]], [[0, 0, 6561, 6561, 6561], [0, 0, 6561, 6561, 6561], [0, 0, 6561, 6561, 6561], [0, 0, 1296, 1296, 1296]], [[0, 0, 0, 1296, 1296], [0, 0, 0, 1296, 1296], [0, 0, 0, 1296, 1296], [0, 0, 0, 1, 1]]]]]

/-- W(4) as a table. -/
def tab4 (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (c : ℕ) : ℕ :=
  match q with
  | none => ((LN4.getD (r 0).val []).getD (r 1).val []).getD c 0
  | some p => ((((LS4.getD (p 0).val []).getD (p 1).val []).getD (r 0).val []).getD (r 1).val []).getD c 0

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

lemma checkN4 : ∀ y1 y2 : Fin 4, ∀ c : Fin 5,
    T tab3 none ![y1, y2] c.val = tab4 none ![y1, y2] c.val := by
  decide +kernel

lemma checkS4 : ∀ p1 p2 : Fin 4, ∀ y1 y2 : Fin 4, ∀ c : Fin 5, (p1.val < c.val ∧ p2.val < c.val) →
    T tab3 (some ![p1, p2]) ![y1, y2] c.val = tab4 (some ![p1, p2]) ![y1, y2] c.val := by
  decide +kernel

lemma checkN_rel : ∀ y1 y2 : Fin 4, ∀ c : Fin 5,
    T tab4 none ![y1, y2] c.val + 101 * tab3 none ![y1, y2] c.val + 108 * tab1 none ![y1, y2] c.val =
      18 * tab4 none ![y1, y2] c.val + 192 * tab2 none ![y1, y2] c.val := by
  decide +kernel

lemma checkS_rel : ∀ p1 p2 : Fin 4, ∀ y1 y2 : Fin 4, ∀ c : Fin 5, (p1.val < c.val ∧ p2.val < c.val) →
    T tab4 (some ![p1, p2]) ![y1, y2] c.val + 101 * tab3 (some ![p1, p2]) ![y1, y2] c.val + 108 * tab1 (some ![p1, p2]) ![y1, y2] c.val =
      18 * tab4 (some ![p1, p2]) ![y1, y2] c.val + 192 * tab2 (some ![p1, p2]) ![y1, y2] c.val := by
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

lemma W_4 (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (c : ℕ) (hc : c ≤ 4)
    (hq : ∀ p, q = some p → ∀ j, (p j).val < c) :
    W 4 q r c = tab4 q r c := by
  rw [show W 4 q r c = W (3 + 1) q r c from rfl, W_succT _ q r c hc,
    T_congr _ tab3 q r c
      (fun s => W_3 _ s _ (newcB_le c hc r) (inv_next c hc r))]
  rcases q with _ | p
  · rw [row_eta r]
    exact checkN4 (r 0) (r 1) ⟨c, by omega⟩
  · rw [row_eta p, row_eta r]
    exact checkS4 (p 0) (p 1) (r 0) (r 1) ⟨c, by omega⟩ ⟨hq p rfl 0, hq p rfl 1⟩

lemma W_rec (n : ℕ) : ∀ (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (c : ℕ), c ≤ 4 →
    (∀ p, q = some p → ∀ j, (p j).val < c) →
    W (n + 5) q r c + 101 * W (n + 3) q r c + 108 * W (n + 1) q r c = 18 * W (n + 4) q r c + 192 * W (n + 2) q r c := by
  induction n with
  | zero =>
    intro q r c hc hq
    rw [show W (0 + 5) q r c = W (4 + 1) q r c from rfl, W_succT 4 q r c hc,
      T_congr _ tab4 q r c
        (fun s => W_4 _ s _ (newcB_le c hc r) (inv_next c hc r)),
      show W (0 + 1) q r c = W 1 q r c from rfl, W_1 q r c hc hq,
      show W (0 + 2) q r c = W 2 q r c from rfl, W_2 q r c hc hq,
      show W (0 + 3) q r c = W 3 q r c from rfl, W_3 q r c hc hq,
      show W (0 + 4) q r c = W 4 q r c from rfl, W_4 q r c hc hq]
    rcases q with _ | p
    · rw [row_eta r]
      exact checkN_rel (r 0) (r 1) ⟨c, by omega⟩
    · rw [row_eta p, row_eta r]
      exact checkS_rel (p 0) (p 1) (r 0) (r 1) ⟨c, by omega⟩ ⟨hq p rfl 0, hq p rfl 1⟩
  | succ n ih =>
    intro q r c hc hq
    rw [W_succT (n + 5) q r c hc, W_succT (n + 4) q r c hc, W_succT (n + 3) q r c hc, W_succT (n + 2) q r c hc, W_succT (n + 1) q r c hc]
    unfold T
    split_ifs with h
    · rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      split_ifs
      · exact ih _ _ _ (newcB_le c hc r) (inv_next c hc r)
      · simp
    · simp

lemma cond_perm {R C K : ℕ} (σ : Equiv.Perm (Fin K)) (x : Fin R → Fin C → Fin K) :
    Cond (fun i j => σ (x i j)) ↔ Cond x := by
  simp [Cond, blockNum]

lemma a_eq (n : ℕ) : a n = ∑ r : Fin 2 → Fin 4, W n none r 0 := by
  have e1 : a n = ((univ : Finset (Fin 2 → Fin (n + 1) → Fin 4)).filter
      (fun x => Cond x ∧ Rgs (fun k => x ((eRow n) k).1 ((eRow n) k).2))).card := by
    unfold a
    exact congrArg Finset.card (Finset.filter_congr (fun x _ => and_congr_right' (rmn_iff_row x)))
  have e2 := card_reorder_arr (eRow n) (eCol n) (fun x : Fin 2 → Fin (n + 1) → Fin 4 => Cond x)
    (fun σ x => cond_perm σ x)
  have e3 : ((univ : Finset (Fin 2 → Fin (n + 1) → Fin 4)).filter
      (fun x => Cond x ∧ Rgs (fun k => x ((eCol n) k).1 ((eCol n) k).2))).card =
      ((univ : Finset (Fin (n + 1) → Fin 2 → Fin 4)).filter (fun y => CondT y ∧ RowMajorNew y)).card := by
    refine Finset.card_bij' (fun x _ => fun j i => x i j) (fun y _ => fun i j => y j i) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx ⊢
      exact ⟨(condT_iff x).1 hx.1, (rmn_iff_col x).2 hx.2⟩
    · intro y hy
      simp only [mem_filter, mem_univ, true_and] at hy ⊢
      exact ⟨(condT_iff _).2 hy.1, (rmn_iff_col (fun i j => y j i)).1 hy.2⟩
    · intro x _
      rfl
    · intro y _
      rfl
  rw [e1, e2, e3]
  unfold W
  rw [Finset.card_eq_sum_card_fiberwise (f := fun f => f 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Finset.filter_filter]
  refine congrArg Finset.card (Finset.filter_congr (fun f _ => ?_))
  rw [cond_iff, rmn_iff, and_assoc]

lemma a_rec (n : ℕ) : a (n + 5) + 101 * a (n + 3) + 108 * a (n + 1) = 18 * a (n + 4) + 192 * a (n + 2) := by
  rw [a_eq, a_eq, a_eq, a_eq, a_eq, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  exact W_rec n none r 0 (by norm_num) (fun _ h => by cases h)

lemma a_zero : a 0 = 2 := by
  rw [a_eq, sum_row]
  simp only [W_zero]
  decide +kernel

lemma a_one : a 1 = 15 := by
  have h : ∀ r, W 1 none r 0 = tab1 none r 0 := fun r => W_1 none r 0 (by norm_num) (fun _ h => by cases h)
  rw [a_eq, sum_row]
  simp only [h]
  decide +kernel

lemma a_two : a 2 = 85 := by
  have h : ∀ r, W 2 none r 0 = tab2 none r 0 := fun r => W_2 none r 0 (by norm_num) (fun _ h => by cases h)
  rw [a_eq, sum_row]
  simp only [h]
  decide +kernel

lemma a_three : a 3 = 641 := by
  have h : ∀ r, W 3 none r 0 = tab3 none r 0 := fun r => W_3 none r 0 (by norm_num) (fun _ h => by cases h)
  rw [a_eq, sum_row]
  simp only [h]
  decide +kernel

lemma a_four : a 4 = 5257 := by
  have h : ∀ r, W 4 none r 0 = tab4 none r 0 := fun r => W_4 none r 0 (by norm_num) (fun _ h => by cases h)
  rw [a_eq, sum_row]
  simp only [h]
  decide +kernel

/-- Barker's g.f.: Sum_{n >= 1} a(n) x^n = x(15 - 185x + 626x^2 - 576x^3) / ((1 - x)(1 - 2x)(1 - 6x)(1 - 9x)). -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - X) * (1 - 2 * X) * (1 - 6 * X) * (1 - 9 * X)) = X * (15 - 185 * X + 626 * X ^ 2 - 576 * X ^ 3) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - X) * (1 - 2 * X) * (1 - 6 * X) * (1 - 9 * X)) = A - A * X ^ 1 * C 18 + A * X ^ 2 * C 101 - A * X ^ 3 * C 192 + A * X ^ 4 * C 108 := by
    rw [show (C (18 : ℚ) : ℚ⟦X⟧) = 18 from map_ofNat C 18,
      show (C (101 : ℚ) : ℚ⟦X⟧) = 101 from map_ofNat C 101,
      show (C (108 : ℚ) : ℚ⟦X⟧) = 108 from map_ofNat C 108,
      show (C (192 : ℚ) : ℚ⟦X⟧) = 192 from map_ofNat C 192]
    ring
  have e2 : (X * (15 - 185 * X + 626 * X ^ 2 - 576 * X ^ 3) : ℚ⟦X⟧) = X ^ 1 * C 15 - X ^ 2 * C 185 + X ^ 3 * C 626 - X ^ 4 * C 576 := by
    rw [show (C (15 : ℚ) : ℚ⟦X⟧) = 15 from map_ofNat C 15,
      show (C (185 : ℚ) : ℚ⟦X⟧) = 185 from map_ofNat C 185,
      show (C (576 : ℚ) : ℚ⟦X⟧) = 576 from map_ofNat C 576,
      show (C (626 : ℚ) : ℚ⟦X⟧) = 626 from map_ofNat C 626]
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
    
    have hq : (a (n + 5) : ℚ) + 101 * (a (n + 3) : ℚ) + 108 * (a (n + 1) : ℚ) = 18 * (a (n + 4) : ℚ) + 192 * (a (n + 2) : ℚ) := by exact_mod_cast h
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

theorem cf (b : ℕ → ℕ) (h1 : b 1 = 15) (h2 : b 2 = 85) (h3 : b 3 = 641) (h4 : b 4 = 5257)
    (hr : ∀ n, b (n + 5) + 101 * b (n + 3) + 108 * b (n + 1) = 18 * b (n + 4) + 192 * b (n + 2)) :
    ∀ n : ℕ, 1 ≤ n → (b n : ℝ) = (9 + 3 * 2 ^ n + 2 ^ (1 + n) * 3 ^ n + 2 * 9 ^ n) / 3 := by
  set H : ℕ → ℝ := fun n => (9 + 3 * 2 ^ n + 2 ^ (1 + n) * 3 ^ n + 2 * 9 ^ n) / 3 with hH
  have Hrec : ∀ k, H (k + 5) + 101 * H (k + 3) + 108 * H (k + 1) =
      18 * H (k + 4) + 192 * H (k + 2) := by
    intro k
    simp only [hH]
    ring
  have key : ∀ k, (b (k + 1) : ℝ) = H (k + 1) ∧ (b (k + 2) : ℝ) = H (k + 2) ∧
      (b (k + 3) : ℝ) = H (k + 3) ∧ (b (k + 4) : ℝ) = H (k + 4) := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [h1]; simp only [hH]; norm_num
      · rw [h2]; simp only [hH]; norm_num
      · rw [h3]; simp only [hH]; norm_num
      · rw [h4]; simp only [hH]; norm_num
    | succ k ih =>
      obtain ⟨e1, e2, e3, e4⟩ := ih
      refine ⟨e2, e3, e4, ?_⟩
      have hq : ((b (k + 5) : ℕ) : ℝ) + 101 * b (k + 3) + 108 * b (k + 1) =
          18 * b (k + 4) + 192 * b (k + 2) := by exact_mod_cast hr k
      have hg := Hrec k
      rw [show k + 1 + 4 = k + 5 from rfl]
      linear_combination hq - hg - 101 * e3 - 108 * e1 + 18 * e4 + 192 * e2
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact (key k).1

/-- Barker's closed form. -/
theorem closed_form : ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (9 + 3 * 2 ^ n + 2 ^ (1 + n) * 3 ^ n + 2 * 9 ^ n) / 3 :=
  cf a a_one a_two a_three a_four a_rec

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 - 2 * X) * (1 - 6 * X) * (1 - 9 * X)) = X * (15 - 185 * X + 626 * X ^ 2 - 576 * X ^ 3) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (9 + 3 * 2 ^ n + 2 ^ (1 + n) * 3 ^ n + 2 * 9 ^ n) / 3 :=
  ⟨gf, closed_form⟩

/-- Controls: the entry's terms a(1..10), from the recurrence and the first values. -/
theorem controls : a 1 = 15 ∧ a 2 = 85 ∧ a 3 = 641 ∧ a 4 = 5257 ∧ a 5 = 44585 ∧ a 6 = 385465 ∧ a 7 = 3375401 ∧ a 8 = 29817817 ∧ a 9 = 264999305 ∧ a 10 = 2364834745 := by
  have r0 := a_rec 0; have r1 := a_rec 1; have r2 := a_rec 2; have r3 := a_rec 3; have r4 := a_rec 4; have r5 := a_rec 5
  have h1 := a_one; have h2 := a_two; have h3 := a_three; have h4 := a_four
  norm_num at r0 r1 r2 r3 r4 r5
  omega

end OMA.S_oeis_a206170

theorem OMA.solution : type_of% @OMA.S_oeis_a206170.main :=
  OMA.S_oeis_a206170.conjecture
