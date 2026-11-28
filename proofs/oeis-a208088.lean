import OMAStatements.S_oeis_a208088

namespace OMA.S_oeis_a208088

open PowerSeries Finset


instance {R C K : ℕ} : DecidablePred (@RowMajorNew R C K) := fun x => by
  unfold RowMajorNew; infer_instance



instance {R C K : ℕ} : DecidablePred (@Cond R C K) := fun x => by
  unfold Cond; infer_instance


/-! ## Rows -/

/-- edgeNum of the subblock in columns i, i' of the rows r above t. -/
def enR (r t : Fin 7 → Fin 2) (i i' : Fin 7) : ℕ :=
  (if r i = r i' then 1 else 0) + (if t i = t i' then 1 else 0) +
    (if r i = t i then 1 else 0) + (if r i' = t i' then 1 else 0)

/-- The subblocks between r and the row s below it, if any, differ from their horizontal
neighbors. -/
def okBelow (r : Fin 7 → Fin 2) (s : Option (Fin 7 → Fin 2)) : Prop :=
  match s with
  | none => True
  | some t => ∀ i i' i'' : Fin 7, i'.val = i.val + 1 → i''.val = i'.val + 1 →
      enR r t i i' ≠ enR r t i' i''

/-- The subblocks between q and r equal the ones below them, between r and s. -/
def okVert (q : Option (Fin 7 → Fin 2)) (r : Fin 7 → Fin 2) (s : Option (Fin 7 → Fin 2)) : Prop :=
  match q, s with
  | some p, some t => ∀ i i' : Fin 7, i'.val = i.val + 1 → enR p r i i' = enR r t i i'
  | _, _ => True

/-- The condition on the row r with the row q above it and the row s below it. -/
def rowCond (q : Option (Fin 7 → Fin 2)) (r : Fin 7 → Fin 2) (s : Option (Fin 7 → Fin 2)) : Prop :=
  okBelow r s ∧ okVert q r s

instance (r : Fin 7 → Fin 2) (s : Option (Fin 7 → Fin 2)) : Decidable (okBelow r s) := by
  unfold okBelow; split <;> infer_instance

instance (q : Option (Fin 7 → Fin 2)) (r : Fin 7 → Fin 2) (s : Option (Fin 7 → Fin 2)) : Decidable (okVert q r s) := by
  unfold okVert; split <;> infer_instance

instance (q : Option (Fin 7 → Fin 2)) (r : Fin 7 → Fin 2) (s : Option (Fin 7 → Fin 2)) : Decidable (rowCond q r s) := by
  unfold rowCond; infer_instance

/-- The condition of the transposed array y, whose rows are the columns of x: vertically
neighboring subblocks have equal numbers and horizontally neighboring ones different numbers. -/
def CondT {R : ℕ} (y : Fin R → Fin 7 → Fin 2) : Prop :=
  (∀ j j' : Fin R, j'.val = j.val + 1 → ∀ i i' i'' : Fin 7, i'.val = i.val + 1 →
      i''.val = i'.val + 1 → enR (y j) (y j') i i' ≠ enR (y j) (y j') i' i'') ∧
    ∀ j j' j'' : Fin R, j'.val = j.val + 1 → j''.val = j'.val + 1 → ∀ i i' : Fin 7,
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
def prevRow {n : ℕ} (q : Option (Fin 7 → Fin 2)) (g : Fin n → Fin 7 → Fin 2) (i : Fin n) : Option (Fin 7 → Fin 2) :=
  match i with
  | ⟨0, _⟩ => q
  | ⟨k + 1, h⟩ => some (g ⟨k, Nat.lt_of_succ_lt h⟩)

/-- The row below row i of g, none for the last row. -/
def nextRow {n : ℕ} (g : Fin n → Fin 7 → Fin 2) (i : Fin n) : Option (Fin 7 → Fin 2) :=
  if h : i.val + 1 < n then some (g ⟨i.val + 1, h⟩) else none

/-- Every row of g satisfies the condition with the rows above and below it; q is the row above
the first row. -/
def ValidFrom {n : ℕ} (q : Option (Fin 7 → Fin 2)) (g : Fin n → Fin 7 → Fin 2) : Prop :=
  ∀ i, rowCond (prevRow q g i) (g i) (nextRow g i)

instance {n : ℕ} (q : Option (Fin 7 → Fin 2)) : DecidablePred (@ValidFrom n q) := fun g => by
  unfold ValidFrom; infer_instance

lemma validFrom_one (q : Option (Fin 7 → Fin 2)) (g : Fin 1 → Fin 7 → Fin 2) :
    ValidFrom q g ↔ rowCond q (g 0) none := by
  constructor
  · intro h
    exact h 0
  · intro h i
    have hi : i = 0 := Fin.fin_one_eq_zero i
    subst hi
    exact h

lemma prevRow_cons_zero {n : ℕ} (q : Option (Fin 7 → Fin 2)) (r : Fin 7 → Fin 2) (h : Fin (n + 1) → Fin 7 → Fin 2) :
    prevRow q (Fin.cons r h : Fin (n + 2) → Fin 7 → Fin 2) 0 = q := rfl

lemma prevRow_cons_succ {n : ℕ} (q : Option (Fin 7 → Fin 2)) (r : Fin 7 → Fin 2) (h : Fin (n + 1) → Fin 7 → Fin 2)
    (k : Fin (n + 1)) :
    prevRow q (Fin.cons r h : Fin (n + 2) → Fin 7 → Fin 2) k.succ = prevRow (some r) h k := by
  rcases k with ⟨_ | j, hk⟩ <;> rfl

lemma nextRow_cons_zero {n : ℕ} (r : Fin 7 → Fin 2) (h : Fin (n + 1) → Fin 7 → Fin 2) :
    nextRow (Fin.cons r h : Fin (n + 2) → Fin 7 → Fin 2) 0 = some (h 0) := by
  unfold nextRow
  rw [dif_pos (by simp)]
  rfl

lemma nextRow_cons_succ {n : ℕ} (r : Fin 7 → Fin 2) (h : Fin (n + 1) → Fin 7 → Fin 2) (k : Fin (n + 1)) :
    nextRow (Fin.cons r h : Fin (n + 2) → Fin 7 → Fin 2) k.succ = nextRow h k := by
  unfold nextRow
  by_cases hk : k.val + 1 < n + 1
  · rw [dif_pos (by simp; omega), dif_pos hk]
    rfl
  · rw [dif_neg (by simp; omega), dif_neg hk]

lemma validFrom_cons {n : ℕ} (q : Option (Fin 7 → Fin 2)) (r : Fin 7 → Fin 2) (h : Fin (n + 1) → Fin 7 → Fin 2) :
    ValidFrom q (Fin.cons r h : Fin (n + 2) → Fin 7 → Fin 2) ↔
      rowCond q r (some (h 0)) ∧ ValidFrom (some r) h := by
  unfold ValidFrom
  rw [Fin.forall_fin_succ]
  simp only [prevRow_cons_zero, prevRow_cons_succ, nextRow_cons_zero, nextRow_cons_succ,
    Fin.cons_zero, Fin.cons_succ]

/-! ## Counting by the first row -/

/-- W(n, q, r, c): arrays with n + 1 rows, first row r with the row q above it, every row
satisfying the condition, values introduced in row major order after the values below c. -/
def W (n : ℕ) (q : Option (Fin 7 → Fin 2)) (r : Fin 7 → Fin 2) (c : ℕ) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 7 → Fin 2)).filter
    (fun g => ValidFrom q g ∧ RGSfrom c g ∧ g 0 = r)).card

lemma W_zero (q : Option (Fin 7 → Fin 2)) (r : Fin 7 → Fin 2) (c : ℕ) :
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
def consEmb (n : ℕ) (r : Fin 7 → Fin 2) :
    (Fin (n + 1) → Fin 7 → Fin 2) ↪ (Fin (n + 2) → Fin 7 → Fin 2) where
  toFun g := Fin.cons r g
  inj' g g' h := by
    funext i
    have := congrFun h i.succ
    simpa using this

lemma consEmb_apply (n : ℕ) (r : Fin 7 → Fin 2) (g : Fin (n + 1) → Fin 7 → Fin 2) :
    consEmb n r g = Fin.cons r g := rfl

lemma W_succ (n : ℕ) (q : Option (Fin 7 → Fin 2)) (r : Fin 7 → Fin 2) (c : ℕ) :
    W (n + 1) q r c = if rowRgs c r then
      ∑ s : Fin 7 → Fin 2, (if rowCond q r (some s) then W n (some r) s (newc c r) else 0) else 0 := by
  have e : ((univ : Finset (Fin (n + 2) → Fin 7 → Fin 2)).filter
      (fun f => ValidFrom q f ∧ RGSfrom c f ∧ f 0 = r)) =
      (((univ : Finset (Fin (n + 1) → Fin 7 → Fin 2)).filter
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

/-! ## Renaming the values introduced before a row

W(n, q, r, c) does not change when the values below c are permuted among themselves in all rows at
once (the values from c on, which the array still has to introduce in order, stay fixed). The
kernel checks with a row above p then run only over the pairs with p 0 = 0 (`ren` exchanges the
values p 0 and 0). -/

/-- σ fixes every value from c on. -/
def FixFrom (c : ℕ) (σ : Equiv.Perm (Fin 2)) : Prop := ∀ v : Fin 2, c ≤ v.val → σ v = v

lemma fixFrom_lt (c : ℕ) (σ : Equiv.Perm (Fin 2)) (h : FixFrom c σ) (v : Fin 2)
    (hv : v.val < c) : (σ v).val < c := by
  by_contra hc
  push_neg at hc
  have h1 : σ (σ v) = σ v := h (σ v) hc
  have h2 : σ v = v := σ.injective h1
  rw [h2] at hc
  omega

lemma fixFrom_symm (c : ℕ) (σ : Equiv.Perm (Fin 2)) (h : FixFrom c σ) : FixFrom c σ.symm := by
  intro v hv
  rw [Equiv.symm_apply_eq]
  exact (h v hv).symm

lemma RGSfrom_perm {R : ℕ} (c : ℕ) (σ : Equiv.Perm (Fin 2)) (h : FixFrom c σ)
    (g : Fin R → Fin 7 → Fin 2) (H : RGSfrom c g) : RGSfrom c (fun i j => σ (g i j)) := by
  intro i j u hu
  by_cases huc : u.val < c
  · exact Or.inl huc
  · push_neg at huc
    have hv : c ≤ (g i j).val := by
      by_contra hv
      push_neg at hv
      have h1 := fixFrom_lt c σ h (g i j) hv
      have h2 : u.val < (σ (g i j)).val := hu
      omega
    have hσv : σ (g i j) = g i j := h _ hv
    have hu' : u < g i j := by
      have h2 : u.val < (σ (g i j)).val := hu
      rw [hσv] at h2
      exact h2
    rcases H i j u hu' with h1 | ⟨i', j', hb, he⟩
    · omega
    · right
      refine ⟨i', j', hb, ?_⟩
      show σ (g i' j') = u
      rw [he]
      exact h u huc

/-- The row r with σ applied to its entries. -/
def mapRow (σ : Equiv.Perm (Fin 2)) (r : Fin 7 → Fin 2) : Fin 7 → Fin 2 := fun j => σ (r j)

lemma mapRow_symm_apply (σ : Equiv.Perm (Fin 2)) (r : Fin 7 → Fin 2) : mapRow σ (mapRow σ.symm r) = r := by
  funext j
  simp [mapRow]

lemma mapRow_apply_symm (σ : Equiv.Perm (Fin 2)) (r : Fin 7 → Fin 2) : mapRow σ.symm (mapRow σ r) = r := by
  funext j
  simp [mapRow]

lemma prevRow_map {n : ℕ} (σ : Equiv.Perm (Fin 2)) (q : Option (Fin 7 → Fin 2)) (g : Fin n → Fin 7 → Fin 2)
    (i : Fin n) :
    prevRow (q.map (mapRow σ)) (fun i => mapRow σ (g i)) i = (prevRow q g i).map (mapRow σ) := by
  rcases i with ⟨_ | k, h⟩ <;> rfl

lemma nextRow_map {n : ℕ} (σ : Equiv.Perm (Fin 2)) (g : Fin n → Fin 7 → Fin 2) (i : Fin n) :
    nextRow (fun i => mapRow σ (g i)) i = (nextRow g i).map (mapRow σ) := by
  unfold nextRow
  split_ifs <;> rfl

lemma enR_perm (σ : Equiv.Perm (Fin 2)) (r t : Fin 7 → Fin 2) (i i' : Fin 7) :
    enR (mapRow σ r) (mapRow σ t) i i' = enR r t i i' := by
  simp [enR, mapRow]

lemma rowCond_perm (σ : Equiv.Perm (Fin 2)) (q : Option (Fin 7 → Fin 2)) (r : Fin 7 → Fin 2)
    (s : Option (Fin 7 → Fin 2)) :
    rowCond (q.map (mapRow σ)) (mapRow σ r) (s.map (mapRow σ)) ↔ rowCond q r s := by
  rcases q with _ | p <;> rcases s with _ | t <;> simp [rowCond, okBelow, okVert, enR_perm]

lemma validFrom_perm {n : ℕ} (σ : Equiv.Perm (Fin 2)) (q : Option (Fin 7 → Fin 2)) (g : Fin n → Fin 7 → Fin 2) :
    ValidFrom (q.map (mapRow σ)) (fun i => mapRow σ (g i)) ↔ ValidFrom q g := by
  unfold ValidFrom
  simp only [prevRow_map, nextRow_map, rowCond_perm]

lemma W_perm (σ : Equiv.Perm (Fin 2)) (c : ℕ) (hσ : FixFrom c σ) (n : ℕ) (q : Option (Fin 7 → Fin 2))
    (r : Fin 7 → Fin 2) : W n (q.map (mapRow σ)) (mapRow σ r) c = W n q r c := by
  have hv : ∀ g : Fin (n + 1) → Fin 7 → Fin 2,
      ValidFrom (q.map (mapRow σ)) g ↔ ValidFrom q (fun i => mapRow σ.symm (g i)) := by
    intro g
    have h := validFrom_perm σ q (fun i => mapRow σ.symm (g i))
    simp only [mapRow_symm_apply] at h
    exact h
  unfold W
  refine Finset.card_bij' (fun g _ => fun i => mapRow σ.symm (g i))
    (fun g _ => fun i => mapRow σ (g i)) ?_ ?_ ?_ ?_
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    obtain ⟨h1, h2, h3⟩ := hg
    refine ⟨(hv g).1 h1, RGSfrom_perm c σ.symm (fixFrom_symm c σ hσ) g h2, ?_⟩
    show mapRow σ.symm (g 0) = r
    rw [h3, mapRow_apply_symm]
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    obtain ⟨h1, h2, h3⟩ := hg
    refine ⟨(validFrom_perm σ q g).2 h1, RGSfrom_perm c σ hσ g h2, ?_⟩
    show mapRow σ (g 0) = mapRow σ r
    rw [h3]
  · intro g _
    funext i
    exact mapRow_symm_apply σ (g i)
  · intro g _
    funext i
    exact mapRow_apply_symm σ (g i)

/-- The swap of the values a and b, by cases (the kernel evaluates it faster than `Equiv.swap`). -/
def swV (a b v : Fin 2) : Fin 2 := if v = a then b else if v = b then a else v

/-- The pair (p, r) with the values p 0 and 0 exchanged in both rows when p 0 is below c. -/
def ren (c : ℕ) (p r : Fin 7 → Fin 2) : (Fin 7 → Fin 2) × (Fin 7 → Fin 2) :=
  if (p 0).val < c then (fun j => swV (p 0) 0 (p j), fun j => swV (p 0) 0 (r j)) else (p, r)

lemma W_ren (n c : ℕ) (p r : Fin 7 → Fin 2) : W n (some (ren c p r).1) (ren c p r).2 c = W n (some p) r c := by
  unfold ren
  split_ifs with h
  · have hσ : FixFrom c (Equiv.swap (p 0) 0) := by
      intro v hv
      apply Equiv.swap_apply_of_ne_of_ne
      · intro e
        rw [e] at hv
        omega
      · intro e
        rw [e] at hv
        simp at hv
        omega
    have e2 : ((fun j => swV (p 0) 0 (p j)), (fun j => swV (p 0) 0 (r j))) =
        (mapRow (Equiv.swap (p 0) 0) p, mapRow (Equiv.swap (p 0) 0) r) := by
      refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
        simp only [swV, mapRow, Equiv.swap_apply_def]
    rw [e2]
    exact W_perm _ c hσ n (some p) r
  · rfl

lemma ren_zero (c : ℕ) (p r : Fin 7 → Fin 2) (h : (p 0).val < c) : (ren c p r).1 0 = 0 := by
  unfold ren
  rw [if_pos h]
  simp [swV]

lemma ren_lt (c : ℕ) (p r : Fin 7 → Fin 2) (hp : ∀ j, (p j).val < c) : ∀ j, ((ren c p r).1 j).val < c := by
  intro j
  unfold ren
  rw [if_pos (hp 0)]
  show (swV (p 0) 0 (p j)).val < c
  unfold swV
  split_ifs with h1 h2
  · show 0 < c
    have := hp 0
    omega
  · exact hp 0
  · exact hp j

/-- `ren` applies one permutation to both rows. -/
lemma ren_eq (c : ℕ) (p r : Fin 7 → Fin 2) :
    ∃ σ : Equiv.Perm (Fin 2), ren c p r = (mapRow σ p, mapRow σ r) := by
  unfold ren
  split_ifs with h
  · refine ⟨Equiv.swap (p 0) 0, Prod.ext (funext fun j => ?_) (funext fun j => ?_)⟩ <;>
      simp only [swV, mapRow, Equiv.swap_apply_def]
  · exact ⟨Equiv.refl _, rfl⟩

lemma nextRow_eq {R : ℕ} (x : Fin R → Fin 7 → Fin 2) (i i' : Fin R) (h : i'.val = i.val + 1) :
    nextRow x i = some (x i') := by
  unfold nextRow
  rw [dif_pos (by omega)]
  have e : (⟨i.val + 1, by omega⟩ : Fin R) = i' := Fin.ext h.symm
  rw [e]

lemma nextRow_none {R : ℕ} (x : Fin R → Fin 7 → Fin 2) (i : Fin R) (h : ¬ i.val + 1 < R) :
    nextRow x i = none := by
  unfold nextRow
  rw [dif_neg h]

lemma prevRow_eq {R : ℕ} (q : Option (Fin 7 → Fin 2)) (x : Fin R → Fin 7 → Fin 2) (i i' : Fin R)
    (h : i.val = i'.val + 1) : prevRow q x i = some (x i') := by
  rcases i with ⟨_ | k, hi⟩
  · simp at h
  · have e : (⟨k, Nat.lt_of_succ_lt hi⟩ : Fin R) = i' := Fin.ext (by simp only [Fin.val_mk] at h ⊢; omega)
    show some (x ⟨k, Nat.lt_of_succ_lt hi⟩) = some (x i')
    rw [e]

lemma edge_T {C : ℕ} (x : Fin 7 → Fin C → Fin 2) (i i' : Fin 7) (j j' : Fin C) :
    edgeNum x i i' j j' = enR (fun a => x a j) (fun a => x a j') i i' := by
  unfold edgeNum enR
  ring

lemma condT_iff {C : ℕ} (x : Fin 7 → Fin C → Fin 2) : Cond x ↔ CondT (fun j i => x i j) := by
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

lemma cond_iff {R : ℕ} (y : Fin R → Fin 7 → Fin 2) : CondT y ↔ ValidFrom none y := by
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

lemma sum_row (f : (Fin 7 → Fin 2) → ℕ) :
    ∑ s : Fin 7 → Fin 2, f s = ∑ x : Fin 2, ∑ y : Fin 2, ∑ z : Fin 2, ∑ u : Fin 2, ∑ v : Fin 2, ∑ x6 : Fin 2, ∑ x7 : Fin 2, f ![x, y, z, u, v, x6, x7] := by
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
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x6 _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x7 _ => ?_)
  rw [Fintype.sum_unique]
  exact congrArg f (by funext j; fin_cases j <;> rfl)

lemma row_eta (r : Fin 7 → Fin 2) : r = ![r 0, r 1, r 2, r 3, r 4, r 5, r 6] := by
  funext j
  fin_cases j <;> rfl

/-! Fast Boolean forms of the conditions for the kernel checks, tied to the definitions by
`decide` over all small cases. -/

/-- `rowRgs c r` as a Boolean. -/
def rgsB (c : ℕ) (r : Fin 7 → Fin 2) : Bool :=
  decide ((r 0).val ≤ c) &&
    decide ((r 1).val ≤ max c ((r 0).val + 1)) &&
    decide ((r 2).val ≤ max (max c ((r 0).val + 1)) ((r 1).val + 1)) &&
    decide ((r 3).val ≤ max (max (max c ((r 0).val + 1)) ((r 1).val + 1)) ((r 2).val + 1)) &&
    decide ((r 4).val ≤ max (max (max (max c ((r 0).val + 1)) ((r 1).val + 1)) ((r 2).val + 1)) ((r 3).val + 1)) &&
    decide ((r 5).val ≤ max (max (max (max (max c ((r 0).val + 1)) ((r 1).val + 1)) ((r 2).val + 1)) ((r 3).val + 1)) ((r 4).val + 1)) &&
    decide ((r 6).val ≤ max (max (max (max (max (max c ((r 0).val + 1)) ((r 1).val + 1)) ((r 2).val + 1)) ((r 3).val + 1)) ((r 4).val + 1)) ((r 5).val + 1))

/-- `newc c r` by explicit maxima. -/
def newcB (c : ℕ) (r : Fin 7 → Fin 2) : ℕ :=
  max (max (max (max (max (max (max c ((r 0).val + 1)) ((r 1).val + 1)) ((r 2).val + 1)) ((r 3).val + 1)) ((r 4).val + 1)) ((r 5).val + 1)) ((r 6).val + 1)

/-- The number of equal edges of the subblock with top cells a0, a1 and bottom cells b0, b1. -/
def enB4 (a0 a1 b0 b1 : Fin 2) : ℕ :=
  (if a0 = a1 then 1 else 0) + (if b0 = b1 then 1 else 0) + (if a0 = b0 then 1 else 0) +
    (if a1 = b1 then 1 else 0)

/-- Two neighboring subblocks (cells a0 a1 a2 above b0 b1 b2) with different numbers. -/
def bandNe (a0 a1 a2 b0 b1 b2 : Fin 2) : Bool := enB4 a0 a1 b0 b1 != enB4 a1 a2 b1 b2

/-- The condition read at cell 1 of the row below. -/
def G1 (q : Option (Fin 7 → Fin 2)) (r : Fin 7 → Fin 2) (b c : Fin 2) : Bool :=
  (match q with
    | none => true
    | some p => enB4 (p 0) (p 1) (r 0) (r 1) == enB4 (r 0) (r 1) b c)

/-- The condition read at cell 2 of the row below. -/
def G2 (q : Option (Fin 7 → Fin 2)) (r : Fin 7 → Fin 2) (a b c : Fin 2) : Bool :=
  (match q with
    | none => true
    | some p => enB4 (p 1) (p 2) (r 1) (r 2) == enB4 (r 1) (r 2) b c) &&
    bandNe (r 0) (r 1) (r 2) a b c

/-- The condition read at cell 3 of the row below. -/
def G3 (q : Option (Fin 7 → Fin 2)) (r : Fin 7 → Fin 2) (a b c : Fin 2) : Bool :=
  (match q with
    | none => true
    | some p => enB4 (p 2) (p 3) (r 2) (r 3) == enB4 (r 2) (r 3) b c) &&
    bandNe (r 1) (r 2) (r 3) a b c

/-- The condition read at cell 4 of the row below. -/
def G4 (q : Option (Fin 7 → Fin 2)) (r : Fin 7 → Fin 2) (a b c : Fin 2) : Bool :=
  (match q with
    | none => true
    | some p => enB4 (p 3) (p 4) (r 3) (r 4) == enB4 (r 3) (r 4) b c) &&
    bandNe (r 2) (r 3) (r 4) a b c

/-- The condition read at cell 5 of the row below. -/
def G5 (q : Option (Fin 7 → Fin 2)) (r : Fin 7 → Fin 2) (a b c : Fin 2) : Bool :=
  (match q with
    | none => true
    | some p => enB4 (p 4) (p 5) (r 4) (r 5) == enB4 (r 4) (r 5) b c) &&
    bandNe (r 3) (r 4) (r 5) a b c

/-- The condition read at cell 6 of the row below. -/
def G6 (q : Option (Fin 7 → Fin 2)) (r : Fin 7 → Fin 2) (a b c : Fin 2) : Bool :=
  (match q with
    | none => true
    | some p => enB4 (p 5) (p 6) (r 5) (r 6) == enB4 (r 5) (r 6) b c) &&
    bandNe (r 4) (r 5) (r 6) a b c

/-- The condition between the row r and the row t below it (the subblocks between them), as a
Boolean. -/
def belowB (r t : Fin 7 → Fin 2) : Bool :=
  bandNe (r 0) (r 1) (r 2) (t 0) (t 1) (t 2) &&
    bandNe (r 1) (r 2) (r 3) (t 1) (t 2) (t 3) &&
    bandNe (r 2) (r 3) (r 4) (t 2) (t 3) (t 4) &&
    bandNe (r 3) (r 4) (r 5) (t 3) (t 4) (t 5) &&
    bandNe (r 4) (r 5) (r 6) (t 4) (t 5) (t 6)

/-- `rowCond q r (some t)` as a Boolean. -/
def condB (q : Option (Fin 7 → Fin 2)) (r t : Fin 7 → Fin 2) : Bool :=
  G1 q r (t 0) (t 1) &&
    G2 q r (t 0) (t 1) (t 2) &&
    G3 q r (t 1) (t 2) (t 3) &&
    G4 q r (t 2) (t 3) (t 4) &&
    G5 q r (t 3) (t 4) (t 5) &&
    G6 q r (t 4) (t 5) (t 6)

/-- `rowCond q r none` as a Boolean. -/
def endB (q : Option (Fin 7 → Fin 2)) (r : Fin 7 → Fin 2) : Bool :=
  true

lemma rgsB_eq : ∀ c : Fin 3, ∀ y1 y2 y3 y4 y5 y6 y7 : Fin 2,
    decide (rowRgs c.val ![y1, y2, y3, y4, y5, y6, y7]) = rgsB c.val ![y1, y2, y3, y4, y5, y6, y7] := by
  decide +kernel

lemma newcB_eq : ∀ c : Fin 3, ∀ y1 y2 y3 y4 y5 y6 y7 : Fin 2,
    newc c.val ![y1, y2, y3, y4, y5, y6, y7] = newcB c.val ![y1, y2, y3, y4, y5, y6, y7] := by
  decide +kernel


lemma rgsB_iff (c : ℕ) (hc : c ≤ 2) (r : Fin 7 → Fin 2) : rowRgs c r ↔ rgsB c r = true := by
  rw [row_eta r, ← rgsB_eq ⟨c, by omega⟩, decide_eq_true_iff]

lemma newcB_eq' (c : ℕ) (hc : c ≤ 2) (r : Fin 7 → Fin 2) : newc c r = newcB c r := by
  rw [row_eta r]
  exact newcB_eq ⟨c, by omega⟩ (r 0) (r 1) (r 2) (r 3) (r 4) (r 5) (r 6)

lemma newcB_le (c : ℕ) (hc : c ≤ 2) (r : Fin 7 → Fin 2) : newcB c r ≤ 2 := by
  rw [← newcB_eq' c hc r]
  exact newc_le c hc r

lemma okBelow_iffC (r t : Fin 7 → Fin 2) : okBelow r (some t) ↔ (enR r t 0 1 ≠ enR r t 1 2 ∧ enR r t 1 2 ≠ enR r t 2 3 ∧ enR r t 2 3 ≠ enR r t 3 4 ∧ enR r t 3 4 ≠ enR r t 4 5 ∧ enR r t 4 5 ≠ enR r t 5 6) := by
  constructor
  · intro h
    exact ⟨h 0 1 2 rfl rfl, h 1 2 3 rfl rfl, h 2 3 4 rfl rfl, h 3 4 5 rfl rfl, h 4 5 6 rfl rfl⟩
  · intro h i i' i'' h1 h2
    have hi := i''.isLt
    rcases (by omega : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4) with e | e | e | e | e
    · obtain rfl : i = 0 := Fin.ext (by rw [e]; rfl)
      obtain rfl : i' = 1 := Fin.ext (by rw [h1]; rfl)
      obtain rfl : i'' = 2 := Fin.ext (by rw [h2]; rfl)
      exact h.1
    · obtain rfl : i = 1 := Fin.ext (by rw [e]; rfl)
      obtain rfl : i' = 2 := Fin.ext (by rw [h1]; rfl)
      obtain rfl : i'' = 3 := Fin.ext (by rw [h2]; rfl)
      exact h.2.1
    · obtain rfl : i = 2 := Fin.ext (by rw [e]; rfl)
      obtain rfl : i' = 3 := Fin.ext (by rw [h1]; rfl)
      obtain rfl : i'' = 4 := Fin.ext (by rw [h2]; rfl)
      exact h.2.2.1
    · obtain rfl : i = 3 := Fin.ext (by rw [e]; rfl)
      obtain rfl : i' = 4 := Fin.ext (by rw [h1]; rfl)
      obtain rfl : i'' = 5 := Fin.ext (by rw [h2]; rfl)
      exact h.2.2.2.1
    · obtain rfl : i = 4 := Fin.ext (by rw [e]; rfl)
      obtain rfl : i' = 5 := Fin.ext (by rw [h1]; rfl)
      obtain rfl : i'' = 6 := Fin.ext (by rw [h2]; rfl)
      exact h.2.2.2.2

lemma okVert_iffC (p r t : Fin 7 → Fin 2) : okVert (some p) r (some t) ↔ (enR p r 0 1 = enR r t 0 1 ∧ enR p r 1 2 = enR r t 1 2 ∧ enR p r 2 3 = enR r t 2 3 ∧ enR p r 3 4 = enR r t 3 4 ∧ enR p r 4 5 = enR r t 4 5 ∧ enR p r 5 6 = enR r t 5 6) := by
  constructor
  · intro h
    exact ⟨h 0 1 rfl, h 1 2 rfl, h 2 3 rfl, h 3 4 rfl, h 4 5 rfl, h 5 6 rfl⟩
  · intro h i i' h1
    have hi := i'.isLt
    rcases (by omega : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5) with e | e | e | e | e | e
    · obtain rfl : i = 0 := Fin.ext (by rw [e]; rfl)
      obtain rfl : i' = 1 := Fin.ext (by rw [h1]; rfl)
      exact h.1
    · obtain rfl : i = 1 := Fin.ext (by rw [e]; rfl)
      obtain rfl : i' = 2 := Fin.ext (by rw [h1]; rfl)
      exact h.2.1
    · obtain rfl : i = 2 := Fin.ext (by rw [e]; rfl)
      obtain rfl : i' = 3 := Fin.ext (by rw [h1]; rfl)
      exact h.2.2.1
    · obtain rfl : i = 3 := Fin.ext (by rw [e]; rfl)
      obtain rfl : i' = 4 := Fin.ext (by rw [h1]; rfl)
      exact h.2.2.2.1
    · obtain rfl : i = 4 := Fin.ext (by rw [e]; rfl)
      obtain rfl : i' = 5 := Fin.ext (by rw [h1]; rfl)
      exact h.2.2.2.2.1
    · obtain rfl : i = 5 := Fin.ext (by rw [e]; rfl)
      obtain rfl : i' = 6 := Fin.ext (by rw [h1]; rfl)
      exact h.2.2.2.2.2

lemma condB_iff (q : Option (Fin 7 → Fin 2)) (r t : Fin 7 → Fin 2) : rowCond q r (some t) ↔ condB q r t = true := by
  rcases q with _ | p
  · have hv : okVert none r (some t) := trivial
    simp only [rowCond, okBelow_iffC, hv, condB, G1, G2, G3, G4, G5, G6, bandNe, enB4, enR, Bool.and_eq_true,
      Bool.true_and, bne_iff_ne, beq_iff_eq, ne_eq, eq_self_iff_true, and_true, true_and]
    tauto
  · simp only [rowCond, okBelow_iffC, okVert_iffC, condB, G1, G2, G3, G4, G5, G6, bandNe, enB4, enR, Bool.and_eq_true,
      bne_iff_ne, beq_iff_eq, ne_eq]
    tauto

lemma endB_iff (q : Option (Fin 7 → Fin 2)) (r : Fin 7 → Fin 2) : rowCond q r none ↔ endB q r = true := by
  rcases q with _ | p <;> simp [rowCond, okBelow, okVert, endB]

lemma belowB_perm (σ : Equiv.Perm (Fin 2)) (r t : Fin 7 → Fin 2) :
    belowB (mapRow σ r) (mapRow σ t) = belowB r t := by
  simp [belowB, bandNe, enB4, mapRow]

lemma ren_reach (c : ℕ) (p r : Fin 7 → Fin 2) : belowB (ren c p r).1 (ren c p r).2 = belowB p r := by
  obtain ⟨σ, hσ⟩ := ren_eq c p r
  rw [hσ]
  exact belowB_perm σ p r

/-- One step of the transfer, the rows below r enumerated entry by entry. -/
def T (g : Option (Fin 7 → Fin 2) → (Fin 7 → Fin 2) → ℕ → ℕ) (q : Option (Fin 7 → Fin 2)) (r : Fin 7 → Fin 2) (c : ℕ) : ℕ :=
  if rgsB c r = true then
    ∑ x : Fin 2, ∑ y : Fin 2, ∑ z : Fin 2, ∑ u : Fin 2, ∑ v : Fin 2, ∑ x6 : Fin 2, ∑ x7 : Fin 2, (if condB q r ![x, y, z, u, v, x6, x7] = true then g (some r) ![x, y, z, u, v, x6, x7] (newcB c r) else 0)
  else 0

lemma W_succT (n : ℕ) (q : Option (Fin 7 → Fin 2)) (r : Fin 7 → Fin 2) (c : ℕ) (hc : c ≤ 2) :
    W (n + 1) q r c = T (W n) q r c := by
  rw [W_succ, sum_row]
  unfold T
  simp only [rgsB_iff c hc, condB_iff, newcB_eq' c hc]

lemma T_congr (g g' : Option (Fin 7 → Fin 2) → (Fin 7 → Fin 2) → ℕ → ℕ) (q : Option (Fin 7 → Fin 2)) (r : Fin 7 → Fin 2) (c : ℕ)
    (h : ∀ s, condB q r s = true → g (some r) s (newcB c r) = g' (some r) s (newcB c r)) :
    T g q r c = T g' q r c := by
  unfold T
  by_cases hr : rgsB c r = true
  · rw [if_pos hr, if_pos hr]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    refine Finset.sum_congr rfl (fun y _ => ?_)
    refine Finset.sum_congr rfl (fun z _ => ?_)
    refine Finset.sum_congr rfl (fun u _ => ?_)
    refine Finset.sum_congr rfl (fun v _ => ?_)
    refine Finset.sum_congr rfl (fun x6 _ => ?_)
    refine Finset.sum_congr rfl (fun x7 _ => ?_)
    split_ifs with hs
    · exact h _ hs
    · rfl
  · rw [if_neg hr, if_neg hr]

/-- `T` with the sums over the cells of the row below cut as soon as a cell fails the condition. -/
def Tp (g : Option (Fin 7 → Fin 2) → (Fin 7 → Fin 2) → ℕ → ℕ) (q : Option (Fin 7 → Fin 2)) (r : Fin 7 → Fin 2) (c : ℕ) : ℕ :=
  if rgsB c r = true then
    ∑ x : Fin 2, ∑ y : Fin 2, (if G1 q r x y = true then (∑ z : Fin 2, (if G2 q r x y z = true then (∑ u : Fin 2, (if G3 q r y z u = true then (∑ v : Fin 2, (if G4 q r z u v = true then (∑ x6 : Fin 2, (if G5 q r u v x6 = true then (∑ x7 : Fin 2, (if G6 q r v x6 x7 = true then g (some r) ![x, y, z, u, v, x6, x7] (newcB c r) else 0)) else 0)) else 0)) else 0)) else 0)) else 0)
  else 0

lemma T_eq_Tp (g : Option (Fin 7 → Fin 2) → (Fin 7 → Fin 2) → ℕ → ℕ) (q : Option (Fin 7 → Fin 2)) (r : Fin 7 → Fin 2) (c : ℕ) :
    T g q r c = Tp g q r c := by
  unfold T Tp
  by_cases hr : rgsB c r = true
  · rw [if_pos hr, if_pos hr]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    refine Finset.sum_congr rfl (fun y _ => ?_)
    by_cases h1 : G1 q r x y = true
    · rw [if_pos h1]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      by_cases h2 : G2 q r x y z = true
      · rw [if_pos h2]
        refine Finset.sum_congr rfl (fun u _ => ?_)
        by_cases h3 : G3 q r y z u = true
        · rw [if_pos h3]
          refine Finset.sum_congr rfl (fun v _ => ?_)
          by_cases h4 : G4 q r z u v = true
          · rw [if_pos h4]
            refine Finset.sum_congr rfl (fun x6 _ => ?_)
            by_cases h5 : G5 q r u v x6 = true
            · rw [if_pos h5]
              refine Finset.sum_congr rfl (fun x7 _ => ?_)
              by_cases h6 : G6 q r v x6 x7 = true
              · rw [if_pos h6, if_pos (show condB q r ![x, y, z, u, v, x6, x7] = true by simp [condB, h1, h2, h3, h4, h5, h6])]
              · rw [if_neg h6, if_neg (show ¬ condB q r ![x, y, z, u, v, x6, x7] = true by simp [condB, h6])]
            · rw [if_neg h5]
              simp [condB, h5]
          · rw [if_neg h4]
            simp [condB, h4]
        · rw [if_neg h3]
          simp [condB, h3]
      · rw [if_neg h2]
        simp [condB, h2]
    · rw [if_neg h1]
      simp [condB, h1]
  · rw [if_neg hr, if_neg hr]

/-- W(0) as a function. -/
def W0f (q : Option (Fin 7 → Fin 2)) (r : Fin 7 → Fin 2) (c : ℕ) : ℕ :=
  if endB q r = true ∧ rgsB c r = true then 1 else 0

lemma W_zero' (q : Option (Fin 7 → Fin 2)) (r : Fin 7 → Fin 2) (c : ℕ) (hc : c ≤ 2) : W 0 q r c = W0f q r c := by
  rw [W_zero]
  unfold W0f
  simp only [endB_iff, rgsB_iff c hc]

lemma reach_next (q : Option (Fin 7 → Fin 2)) (r t : Fin 7 → Fin 2) (h : condB q r t = true) : belowB r t = true := by
  simp only [condB, G1, G2, G3, G4, G5, G6, Bool.and_eq_true] at h
  simp only [belowB, Bool.and_eq_true]
  tauto

lemma inv_next (c : ℕ) (hc : c ≤ 2) (q : Option (Fin 7 → Fin 2)) (r t : Fin 7 → Fin 2) (h : condB q r t = true) :
    ∀ p, some r = some p → (∀ j, (p j).val < newcB c r) ∧ belowB p t = true := by
  intro p hp
  rw [← Option.some.inj hp]
  refine ⟨fun j => ?_, reach_next q r t h⟩
  rw [← newcB_eq' c hc r]
  exact (lt_newc c r _).2 (Or.inr ⟨j, le_refl _⟩)

/-- W(1, none, r, c) for c <= 2, nested by the entries of r and then c. -/
def LN1 : List (List (List (List (List (List (List (List ℕ))))))) :=
  [[[[[[[[0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0]]], [[[1, 1, 1], [0, 0, 0]], [[1, 1, 1], [1, 1, 1]]]], [[[[2, 2, 2], [3, 3, 3]], [[0, 0, 0], [1, 1, 1]]], [[[3, 3, 3], [2, 2, 2]], [[3, 3, 3], [1, 1, 1]]]]], [[[[[1, 1, 1], [4, 4, 4]], [[3, 3, 3], [4, 4, 4]]], [[[0, 0, 0], [0, 0, 0]], [[2, 2, 2], [1, 1, 1]]]], [[[[3, 3, 3], [4, 4, 4]], [[1, 1, 1], [4, 4, 4]]], [[[4, 4, 4], [3, 3, 3]], [[2, 2, 2], [0, 0, 0]]]]]], [[[[[[0, 0, 0], [1, 1, 1]], [[2, 2, 2], [3, 3, 3]]], [[[3, 3, 3], [1, 1, 1]], [[3, 3, 3], [2, 2, 2]]]], [[[[0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0]]], [[[1, 1, 1], [1, 1, 1]], [[1, 1, 1], [0, 0, 0]]]]], [[[[[1, 1, 1], [4, 4, 4]], [[3, 3, 3], [4, 4, 4]]], [[[2, 2, 2], [0, 0, 0]], [[4, 4, 4], [3, 3, 3]]]], [[[[3, 3, 3], [4, 4, 4]], [[1, 1, 1], [4, 4, 4]]], [[[2, 2, 2], [1, 1, 1]], [[0, 0, 0], [0, 0, 0]]]]]]], [[[[[[[0, 0, 0], [0, 0, 0]], [[0, 1, 1], [0, 2, 2]]], [[[0, 4, 4], [0, 1, 1]], [[0, 4, 4], [0, 3, 3]]]], [[[[0, 3, 3], [0, 4, 4]], [[0, 0, 0], [0, 2, 2]]], [[[0, 4, 4], [0, 3, 3]], [[0, 4, 4], [0, 1, 1]]]]], [[[[[0, 0, 0], [0, 1, 1]], [[0, 1, 1], [0, 1, 1]]], [[[0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0]]]], [[[[0, 2, 2], [0, 3, 3]], [[0, 1, 1], [0, 3, 3]]], [[[0, 3, 3], [0, 2, 2]], [[0, 1, 1], [0, 0, 0]]]]]], [[[[[[0, 0, 0], [0, 2, 2]], [[0, 3, 3], [0, 4, 4]]], [[[0, 4, 4], [0, 1, 1]], [[0, 4, 4], [0, 3, 3]]]], [[[[0, 1, 1], [0, 2, 2]], [[0, 0, 0], [0, 0, 0]]], [[[0, 4, 4], [0, 3, 3]], [[0, 4, 4], [0, 1, 1]]]]], [[[[[0, 1, 1], [0, 3, 3]], [[0, 2, 2], [0, 3, 3]]], [[[0, 1, 1], [0, 0, 0]], [[0, 3, 3], [0, 2, 2]]]], [[[[0, 1, 1], [0, 1, 1]], [[0, 0, 0], [0, 1, 1]]], [[[0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0]]]]]]]]

/-- W(1, some p, r, c) at the pairs (p, r) with p 0 = 0 and the values of p below c, nested by the entries of p, of r, and then c (0 elsewhere). -/
def LS1 : List (List (List (List (List (List (List (List (List (List (List (List (List (List (List ℕ)))))))))))))) :=
  [[[[[[], [[[[], [[[[], [[[[0, 0, 2]]]]]]]]], [[[], [[[[], [[[[], [0, 0, 2]]]]]]]], [[], [[[[], [[[], [[], [0, 0, 2]]]]]]]]]]], [[[[[[[], [[[[[], [0, 0, 2]]]]]]], [[[[[], [[[0, 0, 2]]]]]]]], [[[[], [[[[[0, 0, 1], [0, 0, 2]]]]]]], [[[[[], [[], [[0, 0, 2]]]]]]]]], [[], [[], [[[[[], [[], [[], [0, 0, 2]]]]]]]]]], [[[[[[], [[[[], [[0, 0, 1], [0, 0, 2]]]]]]], [[[[], [[], [[[0, 0, 2]]]]]]]], [[[[], [[[[], [[], [0, 0, 2]]]]]]], [[[[], [[], [[], [[0, 0, 2]]]]]]]]], [[[[[], [[[], [[], [[0, 0, 2], [0, 0, 1]]]]]]], [[[[], [[], [[[], [0, 0, 2]]]]]]]], [[[[], [[[], [[], [[0, 0, 2]]]]]]]]]]]], [[[[[[[[[], [[[[], [0, 0, 2]]]]]]]], [[[[[], [[[[0, 0, 1], [0, 0, 2]]]]]], [[[[[], [[0, 0, 1]]]]]]], [[], [[[[[], [[0, 0, 2]]]]]]]]], [[[[[[], [[], [[[0, 0, 2]]]]]], [[[[[[], [0, 0, 1]]]]]]], [[], [[[[[[], [0, 0, 2]]]]]]]], [[[[[], [[], [[[0, 0, 2], [0, 0, 1]]]]]], [[[[[], [[], [0, 0, 1]]]]]]], [[], [[[[[], [[], [0, 0, 2]]]]]]]]]], [[], [[[[[[], [[], [[], [[0, 0, 2], [0, 0, 1]]]]]]]], [[[[[], [[], [[], [[0, 0, 2]]]]]]]]]]], [[[[[[[], [[], [[[[], [0, 0, 2]]]]]], [[[[], [[[0, 0, 1]]]]]]], [[], [[[[], [[[0, 0, 2]]]]]]]], [[[[], [[], [[[[0, 0, 1], [0, 0, 2]]]]]], [[[[], [[], [[0, 0, 1]]]]]]], [[], [[[[], [[], [[0, 0, 2]]]]]]]]], [[[[[], [[], [[], [[[0, 0, 2]]]]]]]], [[[[], [[], [[], [[[0, 0, 2], [0, 0, 1]]]]]], [[[[], [[], [[], [0, 0, 1]]]]]]], [[], [[[[], [[], [[], [0, 0, 2]]]]]]]]]], [[[[[[], [[], [[[], [[0, 0, 1], [0, 0, 2]]]]]], [[[], [[], [[[0, 0, 1]]]]]]], [[], [[[], [[], [[[0, 0, 2]]]]]]]], [[[[], [[], [[[], [[], [0, 0, 2]]]]]], [[[], [[], [[], [[0, 0, 1]]]]]]], [[], [[[], [[], [[], [[0, 0, 2]]]]]]]]], [[[[], [[[], [[], [[[], [0, 0, 1]]]]]]], [[], [[[], [[], [[[], [0, 0, 2]]]]]]]]]]]]], [[[[[[], [[[[], [[[[], [[0, 0, 2]]]]]]]]], [[[[[], [[[[[], [0, 0, 2]]]]]]], [[[[[], [[[0, 0, 2]]]]]]]], [[[[], [[[[], [[], [0, 0, 2]]]]]]], [[[[[], [[[0, 0, 2], [0, 0, 1]]]]]]]]]], [[[[[[], [[], [[[[0, 0, 2]]]]]]], [[[[[[], [[0, 0, 1], [0, 0, 2]]]]]]]], [[], [[[[[[], [[], [0, 0, 2]]]]]]]]], [[[[[], [[], [[[[], [0, 0, 2]]]]]]], [[[[[], [[], [[0, 0, 2], [0, 0, 1]]]]]]]], [[[[], [[], [[[], [[], [0, 0, 2]]]]]]], [[[[[], [[], [[0, 0, 2]]]]]]]]]]], [[], [[[[[[], [[], [[], [[[0, 0, 2]]]]]]]], [[[[], [[], [[], [[], [[0, 0, 2]]]]]]]]], [[[[[], [[], [[], [[[], [0, 0, 2]]]]]]]]]]]], [[[[[[], [[[[], [[[[], [0, 0, 2]]]]]]]], [[[], [[], [[[[], [[0, 0, 2]]]]]]], [[[[], [[[[0, 0, 1], [0, 0, 2]]]]]], [[], [[[[], [[0, 0, 1]]]]]]]]], [[[[], [[], [[[[[], [0, 0, 2]]]]]]], [[[[], [[], [[[0, 0, 2]]]]]], [[], [[[[[], [0, 0, 1]]]]]]]], [[[], [[], [[[[], [[], [0, 0, 2]]]]]]], [[[[], [[], [[[0, 0, 2], [0, 0, 1]]]]]], [[], [[[[], [[], [0, 0, 1]]]]]]]]]], [[[[[], [[], [[], [[[[0, 0, 2]]]]]]], [[], [[], [[], [[[[0, 0, 1]]]]]]]]], [[[[], [[], [[], [[[[], [0, 0, 2]]]]]]], [[[[], [[], [[], [[0, 0, 2], [0, 0, 1]]]]]], [[], [[], [[[[], [0, 0, 1]]]]]]]], [[[], [[], [[], [[[], [[], [0, 0, 2]]]]]]], [[[[], [[], [[], [[0, 0, 2]]]]]], [[], [[], [[[], [[], [0, 0, 1]]]]]]]]]]], [[[[[[], [[], [[[], [[[0, 0, 2]]]]]]], [[[], [[], [[[[], [0, 0, 2]]]]]], [[], [[[], [[[0, 0, 1]]]]]]]], [[[], [[], [[[], [[], [[0, 0, 2]]]]]]], [[[], [[], [[[[0, 0, 1], [0, 0, 2]]]]]], [[], [[[], [[], [[0, 0, 1]]]]]]]]], [[[], [[[], [[], [[], [[[0, 0, 2]]]]]]]], [[[], [[], [[[], [[], [[], [0, 0, 2]]]]]]], [[[], [[], [[], [[[0, 0, 2], [0, 0, 1]]]]]], [[], [[[], [[], [[], [0, 0, 1]]]]]]]]]], [[[[], [[[], [[], [[[], [[0, 0, 1], [0, 0, 2]]]]]]]], [[], [[[], [[], [[[], [[], [0, 0, 2]]]]]]]]]]]]]]]

/-- W(1) as a table. -/
def tab1 (q : Option (Fin 7 → Fin 2)) (r : Fin 7 → Fin 2) (c : ℕ) : ℕ :=
  match q with
  | none => (((((((LN1.getD (r 0).val []).getD (r 1).val []).getD (r 2).val []).getD (r 3).val []).getD (r 4).val []).getD (r 5).val []).getD (r 6).val []).getD c 0
  | some p => ((((((((((((((LS1.getD (p 0).val []).getD (p 1).val []).getD (p 2).val []).getD (p 3).val []).getD (p 4).val []).getD (p 5).val []).getD (p 6).val []).getD (r 0).val []).getD (r 1).val []).getD (r 2).val []).getD (r 3).val []).getD (r 4).val []).getD (r 5).val []).getD (r 6).val []).getD c 0

/-- W(1) read at the renamed pair. -/
def tabc1 (q : Option (Fin 7 → Fin 2)) (r : Fin 7 → Fin 2) (c : ℕ) : ℕ :=
  match q with
  | none => tab1 none r c
  | some p => tab1 (some (ren c p r).1) (ren c p r).2 c

/-- W(2, none, r, c) for c <= 2, nested by the entries of r and then c. -/
def LN2 : List (List (List (List (List (List (List (List ℕ))))))) :=
  [[[[[[[[0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0]]], [[[2, 2, 2], [0, 0, 0]], [[2, 2, 2], [2, 2, 2]]]], [[[[4, 4, 4], [5, 5, 5]], [[0, 0, 0], [2, 2, 2]]], [[[5, 5, 5], [4, 4, 4]], [[5, 5, 5], [2, 2, 2]]]]], [[[[[2, 2, 2], [6, 6, 6]], [[5, 5, 5], [6, 6, 6]]], [[[0, 0, 0], [0, 0, 0]], [[3, 3, 3], [2, 2, 2]]]], [[[[5, 5, 5], [6, 6, 6]], [[2, 2, 2], [6, 6, 6]]], [[[6, 6, 6], [5, 5, 5]], [[3, 3, 3], [0, 0, 0]]]]]], [[[[[[0, 0, 0], [2, 2, 2]], [[4, 4, 4], [5, 5, 5]]], [[[5, 5, 5], [2, 2, 2]], [[5, 5, 5], [4, 4, 4]]]], [[[[0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0]]], [[[2, 2, 2], [2, 2, 2]], [[2, 2, 2], [0, 0, 0]]]]], [[[[[2, 2, 2], [6, 6, 6]], [[5, 5, 5], [6, 6, 6]]], [[[3, 3, 3], [0, 0, 0]], [[6, 6, 6], [5, 5, 5]]]], [[[[5, 5, 5], [6, 6, 6]], [[2, 2, 2], [6, 6, 6]]], [[[3, 3, 3], [2, 2, 2]], [[0, 0, 0], [0, 0, 0]]]]]]], [[[[[[[0, 0, 0], [0, 0, 0]], [[0, 2, 2], [0, 3, 3]]], [[[0, 6, 6], [0, 2, 2]], [[0, 6, 6], [0, 5, 5]]]], [[[[0, 5, 5], [0, 6, 6]], [[0, 0, 0], [0, 3, 3]]], [[[0, 6, 6], [0, 5, 5]], [[0, 6, 6], [0, 2, 2]]]]], [[[[[0, 0, 0], [0, 2, 2]], [[0, 2, 2], [0, 2, 2]]], [[[0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0]]]], [[[[0, 4, 4], [0, 5, 5]], [[0, 2, 2], [0, 5, 5]]], [[[0, 5, 5], [0, 4, 4]], [[0, 2, 2], [0, 0, 0]]]]]], [[[[[[0, 0, 0], [0, 3, 3]], [[0, 5, 5], [0, 6, 6]]], [[[0, 6, 6], [0, 2, 2]], [[0, 6, 6], [0, 5, 5]]]], [[[[0, 2, 2], [0, 3, 3]], [[0, 0, 0], [0, 0, 0]]], [[[0, 6, 6], [0, 5, 5]], [[0, 6, 6], [0, 2, 2]]]]], [[[[[0, 2, 2], [0, 5, 5]], [[0, 4, 4], [0, 5, 5]]], [[[0, 2, 2], [0, 0, 0]], [[0, 5, 5], [0, 4, 4]]]], [[[[0, 2, 2], [0, 2, 2]], [[0, 0, 0], [0, 2, 2]]], [[[0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0]]]]]]]]

/-- W(2, some p, r, c) at the pairs (p, r) with p 0 = 0 and the values of p below c, nested by the entries of p, of r, and then c (0 elsewhere). -/
def LS2 : List (List (List (List (List (List (List (List (List (List (List (List (List (List (List ℕ)))))))))))))) :=
  [[[[[[], [[[[], [[[[], [[[[0, 0, 3]]]]]]]]], [[[], [[[[], [[[[], [0, 0, 3]]]]]]]], [[], [[[[], [[[], [[], [0, 0, 3]]]]]]]]]]], [[[[[[[], [[[[[], [0, 0, 3]]]]]]], [[[[[], [[[0, 0, 3]]]]]]]], [[[[], [[[[[0, 0, 2], [0, 0, 3]]]]]]], [[[[[], [[], [[0, 0, 3]]]]]]]]], [[], [[], [[[[[], [[], [[], [0, 0, 3]]]]]]]]]], [[[[[[], [[[[], [[0, 0, 2], [0, 0, 3]]]]]]], [[[[], [[], [[[0, 0, 3]]]]]]]], [[[[], [[[[], [[], [0, 0, 3]]]]]]], [[[[], [[], [[], [[0, 0, 3]]]]]]]]], [[[[[], [[[], [[], [[0, 0, 3], [0, 0, 2]]]]]]], [[[[], [[], [[[], [0, 0, 3]]]]]]]], [[[[], [[[], [[], [[0, 0, 3]]]]]]]]]]]], [[[[[[[[[], [[[[], [0, 0, 3]]]]]]]], [[[[[], [[[[0, 0, 2], [0, 0, 3]]]]]], [[[[[], [[0, 0, 2]]]]]]], [[], [[[[[], [[0, 0, 3]]]]]]]]], [[[[[[], [[], [[[0, 0, 3]]]]]], [[[[[[], [0, 0, 2]]]]]]], [[], [[[[[[], [0, 0, 3]]]]]]]], [[[[[], [[], [[[0, 0, 3], [0, 0, 2]]]]]], [[[[[], [[], [0, 0, 2]]]]]]], [[], [[[[[], [[], [0, 0, 3]]]]]]]]]], [[], [[[[[[], [[], [[], [[0, 0, 3], [0, 0, 2]]]]]]]], [[[[[], [[], [[], [[0, 0, 3]]]]]]]]]]], [[[[[[[], [[], [[[[], [0, 0, 3]]]]]], [[[[], [[[0, 0, 2]]]]]]], [[], [[[[], [[[0, 0, 3]]]]]]]], [[[[], [[], [[[[0, 0, 2], [0, 0, 3]]]]]], [[[[], [[], [[0, 0, 2]]]]]]], [[], [[[[], [[], [[0, 0, 3]]]]]]]]], [[[[[], [[], [[], [[[0, 0, 3]]]]]]]], [[[[], [[], [[], [[[0, 0, 3], [0, 0, 2]]]]]], [[[[], [[], [[], [0, 0, 2]]]]]]], [[], [[[[], [[], [[], [0, 0, 3]]]]]]]]]], [[[[[[], [[], [[[], [[0, 0, 2], [0, 0, 3]]]]]], [[[], [[], [[[0, 0, 2]]]]]]], [[], [[[], [[], [[[0, 0, 3]]]]]]]], [[[[], [[], [[[], [[], [0, 0, 3]]]]]], [[[], [[], [[], [[0, 0, 2]]]]]]], [[], [[[], [[], [[], [[0, 0, 3]]]]]]]]], [[[[], [[[], [[], [[[], [0, 0, 2]]]]]]], [[], [[[], [[], [[[], [0, 0, 3]]]]]]]]]]]]], [[[[[[], [[[[], [[[[], [[0, 0, 3]]]]]]]]], [[[[[], [[[[[], [0, 0, 3]]]]]]], [[[[[], [[[0, 0, 3]]]]]]]], [[[[], [[[[], [[], [0, 0, 3]]]]]]], [[[[[], [[[0, 0, 3], [0, 0, 2]]]]]]]]]], [[[[[[], [[], [[[[0, 0, 3]]]]]]], [[[[[[], [[0, 0, 2], [0, 0, 3]]]]]]]], [[], [[[[[[], [[], [0, 0, 3]]]]]]]]], [[[[[], [[], [[[[], [0, 0, 3]]]]]]], [[[[[], [[], [[0, 0, 3], [0, 0, 2]]]]]]]], [[[[], [[], [[[], [[], [0, 0, 3]]]]]]], [[[[[], [[], [[0, 0, 3]]]]]]]]]]], [[], [[[[[[], [[], [[], [[[0, 0, 3]]]]]]]], [[[[], [[], [[], [[], [[0, 0, 3]]]]]]]]], [[[[[], [[], [[], [[[], [0, 0, 3]]]]]]]]]]]], [[[[[[], [[[[], [[[[], [0, 0, 3]]]]]]]], [[[], [[], [[[[], [[0, 0, 3]]]]]]], [[[[], [[[[0, 0, 2], [0, 0, 3]]]]]], [[], [[[[], [[0, 0, 2]]]]]]]]], [[[[], [[], [[[[[], [0, 0, 3]]]]]]], [[[[], [[], [[[0, 0, 3]]]]]], [[], [[[[[], [0, 0, 2]]]]]]]], [[[], [[], [[[[], [[], [0, 0, 3]]]]]]], [[[[], [[], [[[0, 0, 3], [0, 0, 2]]]]]], [[], [[[[], [[], [0, 0, 2]]]]]]]]]], [[[[[], [[], [[], [[[[0, 0, 3]]]]]]], [[], [[], [[], [[[[0, 0, 2]]]]]]]]], [[[[], [[], [[], [[[[], [0, 0, 3]]]]]]], [[[[], [[], [[], [[0, 0, 3], [0, 0, 2]]]]]], [[], [[], [[[[], [0, 0, 2]]]]]]]], [[[], [[], [[], [[[], [[], [0, 0, 3]]]]]]], [[[[], [[], [[], [[0, 0, 3]]]]]], [[], [[], [[[], [[], [0, 0, 2]]]]]]]]]]], [[[[[[], [[], [[[], [[[0, 0, 3]]]]]]], [[[], [[], [[[[], [0, 0, 3]]]]]], [[], [[[], [[[0, 0, 2]]]]]]]], [[[], [[], [[[], [[], [[0, 0, 3]]]]]]], [[[], [[], [[[[0, 0, 2], [0, 0, 3]]]]]], [[], [[[], [[], [[0, 0, 2]]]]]]]]], [[[], [[[], [[], [[], [[[0, 0, 3]]]]]]]], [[[], [[], [[[], [[], [[], [0, 0, 3]]]]]]], [[[], [[], [[], [[[0, 0, 3], [0, 0, 2]]]]]], [[], [[[], [[], [[], [0, 0, 2]]]]]]]]]], [[[[], [[[], [[], [[[], [[0, 0, 2], [0, 0, 3]]]]]]]], [[], [[[], [[], [[[], [[], [0, 0, 3]]]]]]]]]]]]]]]

/-- W(2) as a table. -/
def tab2 (q : Option (Fin 7 → Fin 2)) (r : Fin 7 → Fin 2) (c : ℕ) : ℕ :=
  match q with
  | none => (((((((LN2.getD (r 0).val []).getD (r 1).val []).getD (r 2).val []).getD (r 3).val []).getD (r 4).val []).getD (r 5).val []).getD (r 6).val []).getD c 0
  | some p => ((((((((((((((LS2.getD (p 0).val []).getD (p 1).val []).getD (p 2).val []).getD (p 3).val []).getD (p 4).val []).getD (p 5).val []).getD (p 6).val []).getD (r 0).val []).getD (r 1).val []).getD (r 2).val []).getD (r 3).val []).getD (r 4).val []).getD (r 5).val []).getD (r 6).val []).getD c 0

/-- W(2) read at the renamed pair. -/
def tabc2 (q : Option (Fin 7 → Fin 2)) (r : Fin 7 → Fin 2) (c : ℕ) : ℕ :=
  match q with
  | none => tab2 none r c
  | some p => tab2 (some (ren c p r).1) (ren c p r).2 c

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxSize 1024 in
lemma checks_all :
    (∀ y1 y2 y3 y4 y5 y6 y7 : Fin 2,
    Tp W0f none ![y1, y2, y3, y4, y5, y6, y7] 0 = tab1 none ![y1, y2, y3, y4, y5, y6, y7] 0) ∧
    (∀ c : Fin 3, ∀ p1 : Fin 2, p1.val < c.val → p1.val = 0 →
    ∀ p2 : Fin 2, p2.val < c.val →
    ∀ p3 : Fin 2, p3.val < c.val →
    ∀ p4 : Fin 2, p4.val < c.val →
    ∀ p5 : Fin 2, p5.val < c.val →
    ∀ p6 : Fin 2, p6.val < c.val →
    ∀ p7 : Fin 2, p7.val < c.val →
    ∀ y1 : Fin 2,
    ∀ y2 : Fin 2,
    ∀ y3 : Fin 2, bandNe p1 p2 p3 y1 y2 y3 = true →
    ∀ y4 : Fin 2, bandNe p2 p3 p4 y2 y3 y4 = true →
    ∀ y5 : Fin 2, bandNe p3 p4 p5 y3 y4 y5 = true →
    ∀ y6 : Fin 2, bandNe p4 p5 p6 y4 y5 y6 = true →
    ∀ y7 : Fin 2, bandNe p5 p6 p7 y5 y6 y7 = true →
    Tp W0f (some ![p1, p2, p3, p4, p5, p6, p7]) ![y1, y2, y3, y4, y5, y6, y7] c.val = tab1 (some ![p1, p2, p3, p4, p5, p6, p7]) ![y1, y2, y3, y4, y5, y6, y7] c.val) ∧
    (∀ y1 y2 y3 y4 y5 y6 y7 : Fin 2,
    Tp tabc1 none ![y1, y2, y3, y4, y5, y6, y7] 0 = tab2 none ![y1, y2, y3, y4, y5, y6, y7] 0) ∧
    (∀ c : Fin 3, ∀ p1 : Fin 2, p1.val < c.val → p1.val = 0 →
    ∀ p2 : Fin 2, p2.val < c.val →
    ∀ p3 : Fin 2, p3.val < c.val →
    ∀ p4 : Fin 2, p4.val < c.val →
    ∀ p5 : Fin 2, p5.val < c.val →
    ∀ p6 : Fin 2, p6.val < c.val →
    ∀ p7 : Fin 2, p7.val < c.val →
    ∀ y1 : Fin 2,
    ∀ y2 : Fin 2,
    ∀ y3 : Fin 2, bandNe p1 p2 p3 y1 y2 y3 = true →
    ∀ y4 : Fin 2, bandNe p2 p3 p4 y2 y3 y4 = true →
    ∀ y5 : Fin 2, bandNe p3 p4 p5 y3 y4 y5 = true →
    ∀ y6 : Fin 2, bandNe p4 p5 p6 y4 y5 y6 = true →
    ∀ y7 : Fin 2, bandNe p5 p6 p7 y5 y6 y7 = true →
    Tp tabc1 (some ![p1, p2, p3, p4, p5, p6, p7]) ![y1, y2, y3, y4, y5, y6, y7] c.val = tab2 (some ![p1, p2, p3, p4, p5, p6, p7]) ![y1, y2, y3, y4, y5, y6, y7] c.val) ∧
    (∀ y1 y2 y3 y4 y5 y6 y7 : Fin 2,
    Tp tabc2 none ![y1, y2, y3, y4, y5, y6, y7] 0 =
      tabc2 none ![y1, y2, y3, y4, y5, y6, y7] 0 + tabc1 none ![y1, y2, y3, y4, y5, y6, y7] 0) ∧
    (∀ c : Fin 3, ∀ p1 : Fin 2, p1.val < c.val → p1.val = 0 →
    ∀ p2 : Fin 2, p2.val < c.val →
    ∀ p3 : Fin 2, p3.val < c.val →
    ∀ p4 : Fin 2, p4.val < c.val →
    ∀ p5 : Fin 2, p5.val < c.val →
    ∀ p6 : Fin 2, p6.val < c.val →
    ∀ p7 : Fin 2, p7.val < c.val →
    ∀ y1 : Fin 2,
    ∀ y2 : Fin 2,
    ∀ y3 : Fin 2, bandNe p1 p2 p3 y1 y2 y3 = true →
    ∀ y4 : Fin 2, bandNe p2 p3 p4 y2 y3 y4 = true →
    ∀ y5 : Fin 2, bandNe p3 p4 p5 y3 y4 y5 = true →
    ∀ y6 : Fin 2, bandNe p4 p5 p6 y4 y5 y6 = true →
    ∀ y7 : Fin 2, bandNe p5 p6 p7 y5 y6 y7 = true →
    Tp tabc2 (some ![p1, p2, p3, p4, p5, p6, p7]) ![y1, y2, y3, y4, y5, y6, y7] c.val =
      tabc2 (some ![p1, p2, p3, p4, p5, p6, p7]) ![y1, y2, y3, y4, y5, y6, y7] c.val + tabc1 (some ![p1, p2, p3, p4, p5, p6, p7]) ![y1, y2, y3, y4, y5, y6, y7] c.val) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · intro c
    fin_cases c <;> decide +kernel
  · decide +kernel
  · intro c
    fin_cases c <;> decide +kernel
  · decide +kernel
  · intro c
    fin_cases c <;> decide +kernel

lemma checkN1 : ∀ y1 y2 y3 y4 y5 y6 y7 : Fin 2,
    Tp W0f none ![y1, y2, y3, y4, y5, y6, y7] 0 = tab1 none ![y1, y2, y3, y4, y5, y6, y7] 0 := checks_all.1

lemma checkS1 : ∀ c : Fin 3, ∀ p1 : Fin 2, p1.val < c.val → p1.val = 0 →
    ∀ p2 : Fin 2, p2.val < c.val →
    ∀ p3 : Fin 2, p3.val < c.val →
    ∀ p4 : Fin 2, p4.val < c.val →
    ∀ p5 : Fin 2, p5.val < c.val →
    ∀ p6 : Fin 2, p6.val < c.val →
    ∀ p7 : Fin 2, p7.val < c.val →
    ∀ y1 : Fin 2,
    ∀ y2 : Fin 2,
    ∀ y3 : Fin 2, bandNe p1 p2 p3 y1 y2 y3 = true →
    ∀ y4 : Fin 2, bandNe p2 p3 p4 y2 y3 y4 = true →
    ∀ y5 : Fin 2, bandNe p3 p4 p5 y3 y4 y5 = true →
    ∀ y6 : Fin 2, bandNe p4 p5 p6 y4 y5 y6 = true →
    ∀ y7 : Fin 2, bandNe p5 p6 p7 y5 y6 y7 = true →
    Tp W0f (some ![p1, p2, p3, p4, p5, p6, p7]) ![y1, y2, y3, y4, y5, y6, y7] c.val = tab1 (some ![p1, p2, p3, p4, p5, p6, p7]) ![y1, y2, y3, y4, y5, y6, y7] c.val := checks_all.2.1

lemma checkN2 : ∀ y1 y2 y3 y4 y5 y6 y7 : Fin 2,
    Tp tabc1 none ![y1, y2, y3, y4, y5, y6, y7] 0 = tab2 none ![y1, y2, y3, y4, y5, y6, y7] 0 := checks_all.2.2.1

lemma checkS2 : ∀ c : Fin 3, ∀ p1 : Fin 2, p1.val < c.val → p1.val = 0 →
    ∀ p2 : Fin 2, p2.val < c.val →
    ∀ p3 : Fin 2, p3.val < c.val →
    ∀ p4 : Fin 2, p4.val < c.val →
    ∀ p5 : Fin 2, p5.val < c.val →
    ∀ p6 : Fin 2, p6.val < c.val →
    ∀ p7 : Fin 2, p7.val < c.val →
    ∀ y1 : Fin 2,
    ∀ y2 : Fin 2,
    ∀ y3 : Fin 2, bandNe p1 p2 p3 y1 y2 y3 = true →
    ∀ y4 : Fin 2, bandNe p2 p3 p4 y2 y3 y4 = true →
    ∀ y5 : Fin 2, bandNe p3 p4 p5 y3 y4 y5 = true →
    ∀ y6 : Fin 2, bandNe p4 p5 p6 y4 y5 y6 = true →
    ∀ y7 : Fin 2, bandNe p5 p6 p7 y5 y6 y7 = true →
    Tp tabc1 (some ![p1, p2, p3, p4, p5, p6, p7]) ![y1, y2, y3, y4, y5, y6, y7] c.val = tab2 (some ![p1, p2, p3, p4, p5, p6, p7]) ![y1, y2, y3, y4, y5, y6, y7] c.val := checks_all.2.2.2.1

lemma checkN_rel : ∀ y1 y2 y3 y4 y5 y6 y7 : Fin 2,
    Tp tabc2 none ![y1, y2, y3, y4, y5, y6, y7] 0 =
      tabc2 none ![y1, y2, y3, y4, y5, y6, y7] 0 + tabc1 none ![y1, y2, y3, y4, y5, y6, y7] 0 := checks_all.2.2.2.2.1

lemma checkS_rel : ∀ c : Fin 3, ∀ p1 : Fin 2, p1.val < c.val → p1.val = 0 →
    ∀ p2 : Fin 2, p2.val < c.val →
    ∀ p3 : Fin 2, p3.val < c.val →
    ∀ p4 : Fin 2, p4.val < c.val →
    ∀ p5 : Fin 2, p5.val < c.val →
    ∀ p6 : Fin 2, p6.val < c.val →
    ∀ p7 : Fin 2, p7.val < c.val →
    ∀ y1 : Fin 2,
    ∀ y2 : Fin 2,
    ∀ y3 : Fin 2, bandNe p1 p2 p3 y1 y2 y3 = true →
    ∀ y4 : Fin 2, bandNe p2 p3 p4 y2 y3 y4 = true →
    ∀ y5 : Fin 2, bandNe p3 p4 p5 y3 y4 y5 = true →
    ∀ y6 : Fin 2, bandNe p4 p5 p6 y4 y5 y6 = true →
    ∀ y7 : Fin 2, bandNe p5 p6 p7 y5 y6 y7 = true →
    Tp tabc2 (some ![p1, p2, p3, p4, p5, p6, p7]) ![y1, y2, y3, y4, y5, y6, y7] c.val =
      tabc2 (some ![p1, p2, p3, p4, p5, p6, p7]) ![y1, y2, y3, y4, y5, y6, y7] c.val + tabc1 (some ![p1, p2, p3, p4, p5, p6, p7]) ![y1, y2, y3, y4, y5, y6, y7] c.val := checks_all.2.2.2.2.2

lemma W_1 (q : Option (Fin 7 → Fin 2)) (r : Fin 7 → Fin 2) (c : ℕ) (hc : c ≤ 2)
    (hq : ∀ p, q = some p → (∀ j, (p j).val < c) ∧ belowB p r = true) (hn : q = none → c = 0) :
    W 1 q r c = tabc1 q r c := by
  rcases q with _ | p
  · rw [W_succT _ none r c hc,
      T_congr _ W0f none r c (fun s _ => W_zero' _ s _ (newcB_le c hc r))]
    rw [T_eq_Tp, row_eta r]
    rw [hn rfl]
    exact checkN1 (r 0) (r 1) (r 2) (r 3) (r 4) (r 5) (r 6)
  · have hp := hq p rfl
    have h0 := ren_zero c p r (hp.1 0)
    have hlt := ren_lt c p r hp.1
    have hb : belowB (ren c p r).1 (ren c p r).2 = true := (ren_reach c p r).trans hp.2
    rw [← W_ren 1 c p r]
    show W 1 (some (ren c p r).1) (ren c p r).2 c = tab1 (some (ren c p r).1) (ren c p r).2 c
    generalize ren c p r = x at h0 hlt hb ⊢
    rw [W_succT _ (some x.1) x.2 c hc,
      T_congr _ W0f (some x.1) x.2 c (fun s _ => W_zero' _ s _ (newcB_le c hc x.2))]
    simp only [belowB, Bool.and_eq_true] at hb
    rw [T_eq_Tp, row_eta x.1, row_eta x.2]
    exact checkS1 ⟨c, by omega⟩ (x.1 0) (hlt 0) (congrArg Fin.val h0) (x.1 1) (hlt 1) (x.1 2) (hlt 2) (x.1 3) (hlt 3) (x.1 4) (hlt 4) (x.1 5) (hlt 5) (x.1 6) (hlt 6) (x.2 0) (x.2 1) (x.2 2) hb.1.1.1.1 (x.2 3) hb.1.1.1.2 (x.2 4) hb.1.1.2 (x.2 5) hb.1.2 (x.2 6) hb.2

lemma W_2 (q : Option (Fin 7 → Fin 2)) (r : Fin 7 → Fin 2) (c : ℕ) (hc : c ≤ 2)
    (hq : ∀ p, q = some p → (∀ j, (p j).val < c) ∧ belowB p r = true) (hn : q = none → c = 0) :
    W 2 q r c = tabc2 q r c := by
  rcases q with _ | p
  · rw [show W 2 none r c = W (1 + 1) none r c from rfl, W_succT _ none r c hc,
      T_congr _ tabc1 none r c
        (fun s hs => W_1 _ s _ (newcB_le c hc r) (inv_next c hc none r s hs) (fun h => by cases h))]
    rw [T_eq_Tp, row_eta r]
    rw [hn rfl]
    exact checkN2 (r 0) (r 1) (r 2) (r 3) (r 4) (r 5) (r 6)
  · have hp := hq p rfl
    have h0 := ren_zero c p r (hp.1 0)
    have hlt := ren_lt c p r hp.1
    have hb : belowB (ren c p r).1 (ren c p r).2 = true := (ren_reach c p r).trans hp.2
    rw [← W_ren 2 c p r]
    show W 2 (some (ren c p r).1) (ren c p r).2 c = tab2 (some (ren c p r).1) (ren c p r).2 c
    generalize ren c p r = x at h0 hlt hb ⊢
    rw [show W 2 (some x.1) x.2 c = W (1 + 1) (some x.1) x.2 c from rfl, W_succT _ (some x.1) x.2 c hc,
      T_congr _ tabc1 (some x.1) x.2 c
        (fun s hs => W_1 _ s _ (newcB_le c hc x.2) (inv_next c hc (some x.1) x.2 s hs) (fun h => by cases h))]
    simp only [belowB, Bool.and_eq_true] at hb
    rw [T_eq_Tp, row_eta x.1, row_eta x.2]
    exact checkS2 ⟨c, by omega⟩ (x.1 0) (hlt 0) (congrArg Fin.val h0) (x.1 1) (hlt 1) (x.1 2) (hlt 2) (x.1 3) (hlt 3) (x.1 4) (hlt 4) (x.1 5) (hlt 5) (x.1 6) (hlt 6) (x.2 0) (x.2 1) (x.2 2) hb.1.1.1.1 (x.2 3) hb.1.1.1.2 (x.2 4) hb.1.1.2 (x.2 5) hb.1.2 (x.2 6) hb.2

lemma W_rec (n : ℕ) : ∀ (q : Option (Fin 7 → Fin 2)) (r : Fin 7 → Fin 2) (c : ℕ), c ≤ 2 →
    (∀ p, q = some p → (∀ j, (p j).val < c) ∧ belowB p r = true) →
    (q = none → c = 0) →
    W (n + 3) q r c = W (n + 2) q r c + W (n + 1) q r c := by
  induction n with
  | zero =>
    intro q r c hc hq hn
    rcases q with _ | p
    · rw [show W (0 + 3) none r c = W (2 + 1) none r c from rfl, W_succT 2 none r c hc,
        T_congr _ tabc2 none r c
          (fun s hs => W_2 _ s _ (newcB_le c hc r) (inv_next c hc none r s hs) (fun h => by cases h)),
        show W (0 + 1) none r c = W 1 none r c from rfl, W_1 none r c hc hq hn,
        show W (0 + 2) none r c = W 2 none r c from rfl, W_2 none r c hc hq hn]
      rw [T_eq_Tp, row_eta r]
      rw [hn rfl]
      exact checkN_rel (r 0) (r 1) (r 2) (r 3) (r 4) (r 5) (r 6)
    · have hp := hq p rfl
      have h0 := ren_zero c p r (hp.1 0)
      have hlt := ren_lt c p r hp.1
      have hb : belowB (ren c p r).1 (ren c p r).2 = true := (ren_reach c p r).trans hp.2
      rw [show W (0 + 3) (some p) r c = W 3 (some p) r c from rfl, show W (0 + 2) (some p) r c = W 2 (some p) r c from rfl, show W (0 + 1) (some p) r c = W 1 (some p) r c from rfl]
      rw [← W_ren 3 c p r, ← W_ren 2 c p r, ← W_ren 1 c p r]
      generalize ren c p r = x at h0 hlt hb ⊢
      have hx : ∀ p', some x.1 = some p' → (∀ j, (p' j).val < c) ∧ belowB p' x.2 = true := fun p' h => by
        rw [← Option.some.inj h]
        exact ⟨hlt, hb⟩
      rw [show W 3 (some x.1) x.2 c = W (2 + 1) (some x.1) x.2 c from rfl, W_succT 2 (some x.1) x.2 c hc,
        T_congr _ tabc2 (some x.1) x.2 c
          (fun s hs => W_2 _ s _ (newcB_le c hc x.2) (inv_next c hc (some x.1) x.2 s hs) (fun h => by cases h)),
        W_1 (some x.1) x.2 c hc hx (fun h => by cases h),
        W_2 (some x.1) x.2 c hc hx (fun h => by cases h)]
      simp only [belowB, Bool.and_eq_true] at hb
      rw [T_eq_Tp, row_eta x.1, row_eta x.2]
      exact checkS_rel ⟨c, by omega⟩ (x.1 0) (hlt 0) (congrArg Fin.val h0) (x.1 1) (hlt 1) (x.1 2) (hlt 2) (x.1 3) (hlt 3) (x.1 4) (hlt 4) (x.1 5) (hlt 5) (x.1 6) (hlt 6) (x.2 0) (x.2 1) (x.2 2) hb.1.1.1.1 (x.2 3) hb.1.1.1.2 (x.2 4) hb.1.1.2 (x.2 5) hb.1.2 (x.2 6) hb.2
  | succ n ih =>
    intro q r c hc hq hn
    rw [W_succT (n + 3) q r c hc, W_succT (n + 2) q r c hc, W_succT (n + 1) q r c hc]
    unfold T
    by_cases h : rgsB c r = true
    · rw [if_pos h, if_pos h, if_pos h]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun x6 _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun x7 _ => ?_)
      split_ifs with hs
      · exact ih _ _ _ (newcB_le c hc r) (inv_next c hc q r _ hs) (fun h => by cases h)
      · simp
    · rw [if_neg h, if_neg h, if_neg h] <;> simp

lemma a_eq (n : ℕ) : a n = ∑ r : Fin 7 → Fin 2, W n none r 0 := by
  have e : a n = ((univ : Finset (Fin (n + 1) → Fin 7 → Fin 2)).filter
      (fun y => CondT y ∧ RowMajorNew y)).card := by
    unfold a
    refine Finset.card_bij'
      (fun (x : Fin 7 → Fin (n + 1) → Fin 2) _ => (fun j i => x i j : Fin (n + 1) → Fin 7 → Fin 2))
      (fun (y : Fin (n + 1) → Fin 7 → Fin 2) _ => (fun i j => y j i : Fin 7 → Fin (n + 1) → Fin 2))
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

lemma a_rec (n : ℕ) : a (n + 3) = a (n + 2) + a (n + 1) := by
  rw [a_eq, a_eq, a_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  exact W_rec n none r 0 (by norm_num) (fun _ h => by cases h) (fun _ => rfl)

lemma a_zero : a 0 = 64 := by
  rw [a_eq, sum_row]
  simp only [W_zero]
  decide +kernel

lemma a_one : a 1 = 108 := by
  have h : ∀ r, W 1 none r 0 = tabc1 none r 0 := fun r => W_1 none r 0 (by norm_num) (fun _ h => by cases h) (fun _ => rfl)
  rw [a_eq, sum_row]
  simp only [h]
  decide +kernel

lemma a_two : a 2 = 180 := by
  have h : ∀ r, W 2 none r 0 = tabc2 none r 0 := fun r => W_2 none r 0 (by norm_num) (fun _ h => by cases h) (fun _ => rfl)
  rw [a_eq, sum_row]
  simp only [h]
  decide +kernel

/-- Barker's g.f.: Sum_{n >= 1} a(n) x^n = 36x(3 + 2x) / (1 - x - x^2). -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    (1 - X - X ^ 2) = 36 * X * (3 + 2 * X) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - X - X ^ 2) = A - A * X ^ 1 * C 1 - A * X ^ 2 * C 1 := by
    rw [show (C (1 : ℚ) : ℚ⟦X⟧) = 1 from map_one C]
    ring
  have e2 : (36 * X * (3 + 2 * X) : ℚ⟦X⟧) = X ^ 1 * C 108 + X ^ 2 * C 72 := by
    rw [show (C (72 : ℚ) : ℚ⟦X⟧) = 72 from map_ofNat C 72,
      show (C (108 : ℚ) : ℚ⟦X⟧) = 108 from map_ofNat C 108]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk]
  rcases n with _ | _ | _ | n
  · simp
  · simp [a_one] <;> norm_num
  · simp [a_one, a_two] <;> norm_num
  · have h := a_rec n
    
    have hq : (a (n + 3) : ℚ) = (a (n + 2) : ℚ) + (a (n + 1) : ℚ) := by exact_mod_cast h
    simp only [show ¬ (n + 3 = 0) by omega,
      if_false,
      if_true,
      show 1 ≤ n + 3 by omega,
      show n + 3 - 1 = n + 2 by omega,
      show ¬ (n + 2 = 0) by omega,
      show 2 ≤ n + 3 by omega,
      show n + 3 - 2 = n + 1 by omega,
      show ¬ (n + 1 = 0) by omega,
      show ¬ (n + 3 = 1) by omega,
      show ¬ (n + 3 = 2) by omega]
    linear_combination hq

theorem cf (b : ℕ → ℕ) (h1 : b 1 = 108) (h2 : b 2 = 180)
    (hr : ∀ n, b (n + 3) = b (n + 2) + b (n + 1)) :
    ∀ n : ℕ, 1 ≤ n → (b n : ℝ) =
      (9 * 2 ^ (2 - (n : ℤ)) * ((1 - Real.sqrt 5) ^ n * (-2 + Real.sqrt 5) +
        (1 + Real.sqrt 5) ^ n * (2 + Real.sqrt 5))) / Real.sqrt 5 := by
  have s2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  set s := Real.sqrt 5 with hsdef
  set G : ℕ → ℝ := fun n => (1 - s) ^ n * (-2 + s) + (1 + s) ^ n * (2 + s) with hG
  have Grec : ∀ n, G (n + 2) = 2 * G (n + 1) + 4 * G n := by
    intro n
    simp only [hG]
    have e1 : (1 - s) ^ 2 = 2 * (1 - s) + 4 := by linear_combination s2
    have e2 : (1 + s) ^ 2 = 2 * (1 + s) + 4 := by linear_combination s2
    rw [show (1 - s) ^ (n + 2) = (1 - s) ^ n * (1 - s) ^ 2 by ring,
      show (1 + s) ^ (n + 2) = (1 + s) ^ n * (1 + s) ^ 2 by ring, e1, e2]
    ring
  have G0 : G 0 = 2 * s := by simp only [hG]; ring
  have G1 : G 1 = 6 * s := by simp only [hG]; linear_combination 0 * s2
  have G2 : G 2 = 20 * s := by
    rw [show G 2 = G (0 + 2) from rfl, Grec, show G (0 + 1) = G 1 from rfl, G1, G0]; ring
  have key : ∀ k, (b (k + 1) : ℝ) * s * 2 ^ (k + 1) = 36 * G (k + 1) ∧
      (b (k + 2) : ℝ) * s * 2 ^ (k + 2) = 36 * G (k + 2) := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [h1, G1]; push_cast; ring
      · rw [h2, G2]; push_cast; ring
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have hq : ((b (k + 3) : ℕ) : ℝ) = b (k + 2) + b (k + 1) := by exact_mod_cast hr k
      have hg := Grec (k + 1)
      rw [show k + 1 + 2 = k + 3 from rfl, show k + 1 + 1 = k + 2 from rfl] at hg
      rw [show k + 1 + 2 = k + 3 from rfl, hg]
      linear_combination (s * 2 ^ (k + 3)) * hq + 2 * ih.2 + 4 * ih.1
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hk := (key k).1
  have hz : (2 : ℝ) ^ (2 - ((k + 1 : ℕ) : ℤ)) = 4 / 2 ^ (k + 1) := by
    rw [zpow_sub₀ two_ne_zero, zpow_natCast]
    norm_num
  show (b (k + 1) : ℝ) = (9 * 2 ^ (2 - ((k + 1 : ℕ) : ℤ)) * G (k + 1)) / s
  have hG' : G (k + 1) = (b (k + 1) : ℝ) * s * 2 ^ (k + 1) / 36 := by
    linear_combination (-1 / 36 : ℝ) * hk
  rw [hz, hG']
  field_simp
  ring

/-- Barker's closed form. -/
theorem closed_form : ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (9 * 2 ^ (2 - (n : ℤ)) * ((1 - Real.sqrt 5) ^ n * (-2 + Real.sqrt 5) +
        (1 + Real.sqrt 5) ^ n * (2 + Real.sqrt 5))) / Real.sqrt 5 :=
  cf a a_one a_two a_rec

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - X - X ^ 2) = 36 * X * (3 + 2 * X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (9 * 2 ^ (2 - (n : ℤ)) * ((1 - Real.sqrt 5) ^ n * (-2 + Real.sqrt 5) +
        (1 + Real.sqrt 5) ^ n * (2 + Real.sqrt 5))) / Real.sqrt 5 :=
  ⟨gf, closed_form⟩

/-- Controls: the entry's terms a(1..10), from the recurrence and the first values. -/
theorem controls : a 1 = 108 ∧ a 2 = 180 ∧ a 3 = 288 ∧ a 4 = 468 ∧ a 5 = 756 ∧ a 6 = 1224 ∧ a 7 = 1980 ∧ a 8 = 3204 ∧ a 9 = 5184 ∧ a 10 = 8388 := by
  have r0 := a_rec 0; have r1 := a_rec 1; have r2 := a_rec 2; have r3 := a_rec 3; have r4 := a_rec 4; have r5 := a_rec 5; have r6 := a_rec 6; have r7 := a_rec 7
  have h1 := a_one; have h2 := a_two
  norm_num at r0 r1 r2 r3 r4 r5 r6 r7
  omega

end OMA.S_oeis_a208088

theorem OMA.solution : type_of% @OMA.S_oeis_a208088.main :=
  OMA.S_oeis_a208088.conjecture
