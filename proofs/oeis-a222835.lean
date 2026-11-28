import OMAStatements.S_oeis_a222835

namespace OMA.S_oeis_a222835

open PowerSeries Finset


instance {R C K : ℕ} : DecidablePred (@RowMajorNew R C K) := fun x => by
  unfold RowMajorNew; infer_instance


instance {R C K : ℕ} : DecidablePred (@Cond R C K) := fun x => by
  unfold Cond; infer_instance


/-! ## Rows -/

/-- Inside the row r, entries two columns apart differ. -/
def hrow (r : Fin 5 → Fin 4) : Prop := ∀ j j' : Fin 5, j'.val = j.val + 2 → r j ≠ r j'

/-- The row s below r, if any: the entries of r and t in adjacent columns differ. -/
def okBelow (r : Fin 5 → Fin 4) (s : Option (Fin 5 → Fin 4)) : Prop :=
  match s with
  | none => True
  | some t => ∀ j j' : Fin 5, (j'.val = j.val + 1 ∨ j.val = j'.val + 1) → r j ≠ t j'

/-- The rows q and s two apart, if both exist: the entries in the same column differ. -/
def okTwo (q s : Option (Fin 5 → Fin 4)) : Prop :=
  match q, s with
  | some p, some t => ∀ j, p j ≠ t j
  | _, _ => True

/-- The condition on the row r with the row q above it and the row s below it. -/
def rowCond (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (s : Option (Fin 5 → Fin 4)) : Prop :=
  hrow r ∧ okBelow r s ∧ okTwo q s

instance : DecidablePred hrow := fun r => by unfold hrow; infer_instance

instance (r : Fin 5 → Fin 4) (s : Option (Fin 5 → Fin 4)) : Decidable (okBelow r s) := by
  unfold okBelow; split <;> infer_instance

instance (q s : Option (Fin 5 → Fin 4)) : Decidable (okTwo q s) := by
  unfold okTwo; split <;> infer_instance

instance (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (s : Option (Fin 5 → Fin 4)) : Decidable (rowCond q r s) := by
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

/-- A row introduces its values in order after the values below c when its first entry is at most
c and the rest of the row does so after the values below max c (x + 1). -/
lemma rowRgs_cons {C K : ℕ} (c : ℕ) (x : Fin K) (t : Fin C → Fin K) :
    rowRgs c (Matrix.vecCons x t) ↔ x.val ≤ c ∧ rowRgs (max c (x.val + 1)) t := by
  constructor
  · intro H
    refine ⟨?_, fun j u hu => ?_⟩
    · by_contra hx
      have := x.isLt
      rcases H 0 ⟨c, by omega⟩ (by show c < (Matrix.vecCons x t 0).val; rw [Matrix.cons_val_zero]; omega)
        with h | ⟨j', hj', _⟩
      · exact absurd h (lt_irrefl c)
      · exact absurd hj' (Fin.not_lt_zero j')
    · rcases H j.succ u (by rwa [Matrix.cons_val_succ]) with h | ⟨j', hj', he⟩
      · exact Or.inl (lt_max_of_lt_left h)
      · induction j' using Fin.cases with
        | zero =>
          rw [Matrix.cons_val_zero] at he
          subst he
          exact Or.inl (lt_max_of_lt_right (Nat.lt_succ_self _))
        | succ j'' =>
          rw [Matrix.cons_val_succ] at he
          exact Or.inr ⟨j'', Fin.succ_lt_succ_iff.mp hj', he⟩
  · rintro ⟨hx, H⟩ j u hu
    induction j using Fin.cases with
    | zero =>
      rw [Matrix.cons_val_zero] at hu
      have h : u.val < x.val := hu
      exact Or.inl (by omega)
    | succ j =>
      rw [Matrix.cons_val_succ] at hu
      rcases H j u hu with h | ⟨j', hj', he⟩
      · rcases (by omega : u.val < c ∨ u.val < x.val ∨ u.val = x.val) with h | h | h
        · exact Or.inl h
        · exact Or.inl (by omega)
        · exact Or.inr ⟨0, Fin.succ_pos j, by rw [Matrix.cons_val_zero]; exact Fin.ext h.symm⟩
      · exact Or.inr ⟨j'.succ, Fin.succ_lt_succ_iff.mpr hj', by rw [Matrix.cons_val_succ]; exact he⟩

lemma rowRgs_zero {K : ℕ} (c : ℕ) (t : Fin 0 → Fin K) : rowRgs c t := fun j => j.elim0

/-- The number of values introduced after the row r, when c were introduced before it. -/
def newc {C K : ℕ} (c : ℕ) (r : Fin C → Fin K) : ℕ := max c (univ.sup fun j => (r j).val + 1)

lemma lt_newc {C K : ℕ} (c : ℕ) (r : Fin C → Fin K) (u : ℕ) :
    u < newc c r ↔ u < c ∨ ∃ j, u ≤ (r j).val := by
  unfold newc
  rw [lt_max_iff, Finset.lt_sup_iff]
  simp

lemma newc_le {C K : ℕ} (c : ℕ) (hc : c ≤ K) (r : Fin C → Fin K) : newc c r ≤ K :=
  max_le hc (Finset.sup_le fun j _ => (r j).isLt)

lemma newc_cons {C K : ℕ} (c : ℕ) (x : Fin K) (t : Fin C → Fin K) :
    newc c (Matrix.vecCons x t) = newc (max c (x.val + 1)) t := by
  refine eq_of_forall_lt_iff (fun u => ?_)
  rw [lt_newc, lt_newc, Fin.exists_fin_succ, Matrix.cons_val_zero]
  simp only [Matrix.cons_val_succ, lt_max_iff, Nat.lt_add_one_iff, or_assoc]

lemma newc_zero {K : ℕ} (c : ℕ) (t : Fin 0 → Fin K) : newc c t = c := by
  simp [newc]

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
def prevRow {n : ℕ} (q : Option (Fin 5 → Fin 4)) (g : Fin n → Fin 5 → Fin 4) (i : Fin n) : Option (Fin 5 → Fin 4) :=
  match i with
  | ⟨0, _⟩ => q
  | ⟨k + 1, h⟩ => some (g ⟨k, Nat.lt_of_succ_lt h⟩)

/-- The row below row i of g, none for the last row. -/
def nextRow {n : ℕ} (g : Fin n → Fin 5 → Fin 4) (i : Fin n) : Option (Fin 5 → Fin 4) :=
  if h : i.val + 1 < n then some (g ⟨i.val + 1, h⟩) else none

/-- Every row of g satisfies the condition with the rows above and below it; q is the row above
the first row. -/
def ValidFrom {n : ℕ} (q : Option (Fin 5 → Fin 4)) (g : Fin n → Fin 5 → Fin 4) : Prop :=
  ∀ i, rowCond (prevRow q g i) (g i) (nextRow g i)

instance {n : ℕ} (q : Option (Fin 5 → Fin 4)) : DecidablePred (@ValidFrom n q) := fun g => by
  unfold ValidFrom; infer_instance

lemma validFrom_one (q : Option (Fin 5 → Fin 4)) (g : Fin 1 → Fin 5 → Fin 4) :
    ValidFrom q g ↔ rowCond q (g 0) none := by
  constructor
  · intro h
    exact h 0
  · intro h i
    have hi : i = 0 := Fin.fin_one_eq_zero i
    subst hi
    exact h

lemma prevRow_cons_zero {n : ℕ} (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (h : Fin (n + 1) → Fin 5 → Fin 4) :
    prevRow q (Fin.cons r h : Fin (n + 2) → Fin 5 → Fin 4) 0 = q := rfl

lemma prevRow_cons_succ {n : ℕ} (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (h : Fin (n + 1) → Fin 5 → Fin 4)
    (k : Fin (n + 1)) :
    prevRow q (Fin.cons r h : Fin (n + 2) → Fin 5 → Fin 4) k.succ = prevRow (some r) h k := by
  rcases k with ⟨_ | j, hk⟩ <;> rfl

lemma nextRow_cons_zero {n : ℕ} (r : Fin 5 → Fin 4) (h : Fin (n + 1) → Fin 5 → Fin 4) :
    nextRow (Fin.cons r h : Fin (n + 2) → Fin 5 → Fin 4) 0 = some (h 0) := by
  unfold nextRow
  rw [dif_pos (by simp)]
  rfl

lemma nextRow_cons_succ {n : ℕ} (r : Fin 5 → Fin 4) (h : Fin (n + 1) → Fin 5 → Fin 4) (k : Fin (n + 1)) :
    nextRow (Fin.cons r h : Fin (n + 2) → Fin 5 → Fin 4) k.succ = nextRow h k := by
  unfold nextRow
  by_cases hk : k.val + 1 < n + 1
  · rw [dif_pos (by simp; omega), dif_pos hk]
    rfl
  · rw [dif_neg (by simp; omega), dif_neg hk]

lemma validFrom_cons {n : ℕ} (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (h : Fin (n + 1) → Fin 5 → Fin 4) :
    ValidFrom q (Fin.cons r h : Fin (n + 2) → Fin 5 → Fin 4) ↔
      rowCond q r (some (h 0)) ∧ ValidFrom (some r) h := by
  unfold ValidFrom
  rw [Fin.forall_fin_succ]
  simp only [prevRow_cons_zero, prevRow_cons_succ, nextRow_cons_zero, nextRow_cons_succ,
    Fin.cons_zero, Fin.cons_succ]

/-! ## Counting by the first row -/

/-- W(n, q, r, c): arrays with n + 1 rows, first row r with the row q above it, every row
satisfying the condition, values introduced in row major order after the values below c. -/
def W (n : ℕ) (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (c : ℕ) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 5 → Fin 4)).filter
    (fun g => ValidFrom q g ∧ RGSfrom c g ∧ g 0 = r)).card

lemma W_zero (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (c : ℕ) :
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
def consEmb (n : ℕ) (r : Fin 5 → Fin 4) :
    (Fin (n + 1) → Fin 5 → Fin 4) ↪ (Fin (n + 2) → Fin 5 → Fin 4) where
  toFun g := Fin.cons r g
  inj' g g' h := by
    funext i
    have := congrFun h i.succ
    simpa using this

lemma consEmb_apply (n : ℕ) (r : Fin 5 → Fin 4) (g : Fin (n + 1) → Fin 5 → Fin 4) :
    consEmb n r g = Fin.cons r g := rfl

lemma W_succ (n : ℕ) (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (c : ℕ) :
    W (n + 1) q r c = if rowRgs c r then
      ∑ s : Fin 5 → Fin 4, (if rowCond q r (some s) then W n (some r) s (newc c r) else 0) else 0 := by
  have e : ((univ : Finset (Fin (n + 2) → Fin 5 → Fin 4)).filter
      (fun f => ValidFrom q f ∧ RGSfrom c f ∧ f 0 = r)) =
      (((univ : Finset (Fin (n + 1) → Fin 5 → Fin 4)).filter
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
def FixFrom (c : ℕ) (σ : Equiv.Perm (Fin 4)) : Prop := ∀ v : Fin 4, c ≤ v.val → σ v = v

lemma fixFrom_lt (c : ℕ) (σ : Equiv.Perm (Fin 4)) (h : FixFrom c σ) (v : Fin 4)
    (hv : v.val < c) : (σ v).val < c := by
  by_contra hc
  push_neg at hc
  have h1 : σ (σ v) = σ v := h (σ v) hc
  have h2 : σ v = v := σ.injective h1
  rw [h2] at hc
  omega

lemma fixFrom_symm (c : ℕ) (σ : Equiv.Perm (Fin 4)) (h : FixFrom c σ) : FixFrom c σ.symm := by
  intro v hv
  rw [Equiv.symm_apply_eq]
  exact (h v hv).symm

lemma RGSfrom_perm {R : ℕ} (c : ℕ) (σ : Equiv.Perm (Fin 4)) (h : FixFrom c σ)
    (g : Fin R → Fin 5 → Fin 4) (H : RGSfrom c g) : RGSfrom c (fun i j => σ (g i j)) := by
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
def mapRow (σ : Equiv.Perm (Fin 4)) (r : Fin 5 → Fin 4) : Fin 5 → Fin 4 := fun j => σ (r j)

lemma mapRow_symm_apply (σ : Equiv.Perm (Fin 4)) (r : Fin 5 → Fin 4) : mapRow σ (mapRow σ.symm r) = r := by
  funext j
  simp [mapRow]

lemma mapRow_apply_symm (σ : Equiv.Perm (Fin 4)) (r : Fin 5 → Fin 4) : mapRow σ.symm (mapRow σ r) = r := by
  funext j
  simp [mapRow]

lemma prevRow_map {n : ℕ} (σ : Equiv.Perm (Fin 4)) (q : Option (Fin 5 → Fin 4)) (g : Fin n → Fin 5 → Fin 4)
    (i : Fin n) :
    prevRow (q.map (mapRow σ)) (fun i => mapRow σ (g i)) i = (prevRow q g i).map (mapRow σ) := by
  rcases i with ⟨_ | k, h⟩ <;> rfl

lemma nextRow_map {n : ℕ} (σ : Equiv.Perm (Fin 4)) (g : Fin n → Fin 5 → Fin 4) (i : Fin n) :
    nextRow (fun i => mapRow σ (g i)) i = (nextRow g i).map (mapRow σ) := by
  unfold nextRow
  split_ifs <;> rfl

lemma rowCond_perm (σ : Equiv.Perm (Fin 4)) (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4)
    (s : Option (Fin 5 → Fin 4)) :
    rowCond (q.map (mapRow σ)) (mapRow σ r) (s.map (mapRow σ)) ↔ rowCond q r s := by
  rcases q with _ | p <;> rcases s with _ | t <;> simp [rowCond, hrow, okBelow, okTwo, mapRow]

lemma validFrom_perm {n : ℕ} (σ : Equiv.Perm (Fin 4)) (q : Option (Fin 5 → Fin 4)) (g : Fin n → Fin 5 → Fin 4) :
    ValidFrom (q.map (mapRow σ)) (fun i => mapRow σ (g i)) ↔ ValidFrom q g := by
  unfold ValidFrom
  simp only [prevRow_map, nextRow_map, rowCond_perm]

lemma W_perm (σ : Equiv.Perm (Fin 4)) (c : ℕ) (hσ : FixFrom c σ) (n : ℕ) (q : Option (Fin 5 → Fin 4))
    (r : Fin 5 → Fin 4) : W n (q.map (mapRow σ)) (mapRow σ r) c = W n q r c := by
  have hv : ∀ g : Fin (n + 1) → Fin 5 → Fin 4,
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
def swV (a b v : Fin 4) : Fin 4 := if v = a then b else if v = b then a else v

/-- The pair (p, r) with the values p 0 and 0 exchanged in both rows when p 0 is below c. -/
def ren (c : ℕ) (p r : Fin 5 → Fin 4) : (Fin 5 → Fin 4) × (Fin 5 → Fin 4) :=
  if (p 0).val < c then (fun j => swV (p 0) 0 (p j), fun j => swV (p 0) 0 (r j)) else (p, r)

lemma W_ren (n c : ℕ) (p r : Fin 5 → Fin 4) : W n (some (ren c p r).1) (ren c p r).2 c = W n (some p) r c := by
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

lemma ren_zero (c : ℕ) (p r : Fin 5 → Fin 4) (h : (p 0).val < c) : (ren c p r).1 0 = 0 := by
  unfold ren
  rw [if_pos h]
  simp [swV]

lemma ren_lt (c : ℕ) (p r : Fin 5 → Fin 4) (hp : ∀ j, (p j).val < c) : ∀ j, ((ren c p r).1 j).val < c := by
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
lemma ren_eq (c : ℕ) (p r : Fin 5 → Fin 4) :
    ∃ σ : Equiv.Perm (Fin 4), ren c p r = (mapRow σ p, mapRow σ r) := by
  unfold ren
  split_ifs with h
  · refine ⟨Equiv.swap (p 0) 0, Prod.ext (funext fun j => ?_) (funext fun j => ?_)⟩ <;>
      simp only [swV, mapRow, Equiv.swap_apply_def]
  · exact ⟨Equiv.refl _, rfl⟩

/-! ## Renaming the row above in order of first occurrence

`sigP c p` renames the values of the row above p that are below c in order of first occurrence (one
swap per cell, fixing every value from c on); it depends on p alone. `tauV` is the same map by
cases, for the kernel. -/

/-- The swap of v with the label m when v is below c, m is a value and v is not below it; the
identity otherwise (once every value is a label nothing moves). -/
def sw (c m : ℕ) (v : Fin 4) : Equiv.Perm (Fin 4) :=
  if v.val < c ∧ m < 4 ∧ m % 4 ≤ v.val then Equiv.swap v ⟨m % 4, Nat.mod_lt _ (by norm_num)⟩
  else Equiv.refl _

lemma sw_fix (c m : ℕ) (v : Fin 4) : FixFrom c (sw c m v) := by
  intro u hu
  unfold sw
  split_ifs with h
  · rw [Equiv.swap_apply_of_ne_of_ne]
    · intro e
      rw [e] at hu
      omega
    · intro e
      rw [e] at hu
      simp at hu
      omega
  · rfl

lemma fixFrom_mul (c : ℕ) (σ τ : Equiv.Perm (Fin 4)) (hσ : FixFrom c σ) (hτ : FixFrom c τ) :
    FixFrom c (σ * τ) := by
  intro v hv
  rw [Equiv.Perm.mul_apply, hτ v hv, hσ v hv]

/-- The next label after a step whose cell now holds v. -/
def nextMv (c m : ℕ) (v : Fin 4) : ℕ :=
  if v.val < c ∧ v.val = m % 4 then m + 1 else m

/-- The renaming of the row above p. -/
def sigP (c : ℕ) (p : Fin 5 → Fin 4) : Equiv.Perm (Fin 4) :=
  let s1 := sw c 0 (p 0)
  let m1 := nextMv c 0 (s1 (p 0))
  let s2 := sw c m1 (s1 (p 1))
  let m2 := nextMv c m1 (s2 (s1 (p 1)))
  let s3 := sw c m2 (s2 (s1 (p 2)))
  let m3 := nextMv c m2 (s3 (s2 (s1 (p 2))))
  let s4 := sw c m3 (s3 (s2 (s1 (p 3))))
  let m4 := nextMv c m3 (s4 (s3 (s2 (s1 (p 3)))))
  let s5 := sw c m4 (s4 (s3 (s2 (s1 (p 4)))))
  s5 * s4 * s3 * s2 * s1

lemma sigP_fix (c : ℕ) (p : Fin 5 → Fin 4) : FixFrom c (sigP c p) := by
  unfold sigP
  exact fixFrom_mul c _ _ (fixFrom_mul c _ _ (fixFrom_mul c _ _ (fixFrom_mul c _ _ (sw_fix _ _ _) (sw_fix _ _ _)) (sw_fix _ _ _)) (sw_fix _ _ _)) (sw_fix _ _ _)

/-- `sw` by cases. -/
def swIfV (c m : ℕ) (a v : Fin 4) : Fin 4 :=
  if a.val < c ∧ m < 4 ∧ m % 4 ≤ a.val then swV a ⟨m % 4, Nat.mod_lt _ (by norm_num)⟩ v else v

lemma sw_apply_eq (c m : ℕ) (a v : Fin 4) : sw c m a v = swIfV c m a v := by
  unfold sw swIfV
  split_ifs with h
  · rw [Equiv.swap_apply_def]
    rfl
  · rfl

/-- `sigP` by cases. -/
def tauV (c : ℕ) (p : Fin 5 → Fin 4) (v : Fin 4) : Fin 4 :=
  let a1 := (p 0)
  let m1 := nextMv c 0 (swIfV c 0 a1 a1)
  let a2 := (swIfV c 0 a1 (p 1))
  let m2 := nextMv c m1 (swIfV c m1 a2 a2)
  let a3 := (swIfV c m1 a2 (swIfV c 0 a1 (p 2)))
  let m3 := nextMv c m2 (swIfV c m2 a3 a3)
  let a4 := (swIfV c m2 a3 (swIfV c m1 a2 (swIfV c 0 a1 (p 3))))
  let m4 := nextMv c m3 (swIfV c m3 a4 a4)
  let a5 := (swIfV c m3 a4 (swIfV c m2 a3 (swIfV c m1 a2 (swIfV c 0 a1 (p 4)))))
  swIfV c m4 a5 (swIfV c m3 a4 (swIfV c m2 a3 (swIfV c m1 a2 (swIfV c 0 a1 v))))

lemma tauV_eq (c : ℕ) (p : Fin 5 → Fin 4) (v : Fin 4) : tauV c p v = sigP c p v := by
  unfold tauV sigP
  simp only [Equiv.Perm.mul_apply, sw_apply_eq]

/-- `tauV c p` as a vector of its values, so that the kernel computes it once per row above. -/
def piV (c : ℕ) (p : Fin 5 → Fin 4) : Fin 4 → Fin 4 :=
  ![tauV c p 0, tauV c p 1, tauV c p 2, tauV c p 3]

lemma piV_eq (c : ℕ) (p : Fin 5 → Fin 4) (v : Fin 4) : piV c p v = tauV c p v := by
  fin_cases v <;> rfl

/-- The pair with both rows renamed by the renaming of the row above. -/
def renP (c : ℕ) (p r : Fin 5 → Fin 4) : (Fin 5 → Fin 4) × (Fin 5 → Fin 4) :=
  (fun j => piV c p (p j), fun j => piV c p (r j))

lemma renP_eq (c : ℕ) (p r : Fin 5 → Fin 4) :
    renP c p r = (mapRow (sigP c p) p, mapRow (sigP c p) r) := by
  unfold renP mapRow
  simp only [piV_eq, tauV_eq]

lemma W_renP (n c : ℕ) (p r : Fin 5 → Fin 4) :
    W n (some (renP c p r).1) (renP c p r).2 c = W n (some p) r c := by
  rw [renP_eq]
  exact W_perm _ c (sigP_fix c p) n (some p) r

/-- The row above is renamed to itself. -/
def isCanonP (c : ℕ) (p : Fin 5 → Fin 4) : Bool :=
  decide (tauV c p (p 0) = p 0) &&
    decide (tauV c p (p 1) = p 1) &&
    decide (tauV c p (p 2) = p 2) &&
    decide (tauV c p (p 3) = p 3) &&
    decide (tauV c p (p 4) = p 4)

lemma nextRow_eq {R : ℕ} (x : Fin R → Fin 5 → Fin 4) (i i' : Fin R) (h : i'.val = i.val + 1) :
    nextRow x i = some (x i') := by
  unfold nextRow
  rw [dif_pos (by omega)]
  have e : (⟨i.val + 1, by omega⟩ : Fin R) = i' := Fin.ext h.symm
  rw [e]

lemma nextRow_none {R : ℕ} (x : Fin R → Fin 5 → Fin 4) (i : Fin R) (h : ¬ i.val + 1 < R) :
    nextRow x i = none := by
  unfold nextRow
  rw [dif_neg h]

lemma prevRow_eq {R : ℕ} (q : Option (Fin 5 → Fin 4)) (x : Fin R → Fin 5 → Fin 4) (i i' : Fin R)
    (h : i.val = i'.val + 1) : prevRow q x i = some (x i') := by
  rcases i with ⟨_ | k, hi⟩
  · simp at h
  · have e : (⟨k, Nat.lt_of_succ_lt hi⟩ : Fin R) = i' := Fin.ext (by simp only [Fin.val_mk] at h ⊢; omega)
    show some (x ⟨k, Nat.lt_of_succ_lt hi⟩) = some (x i')
    rw [e]

lemma cond_iff {R : ℕ} (x : Fin R → Fin 5 → Fin 4) : Cond x ↔ ValidFrom none x := by
  unfold Cond ValidFrom rowCond
  constructor
  · intro H i
    refine ⟨fun j j' hj => H i i j j' (by omega), ?_, ?_⟩
    · by_cases hlt : i.val + 1 < R
      · rw [nextRow_eq x i ⟨i.val + 1, hlt⟩ rfl]
        intro j j' hj
        exact H i ⟨i.val + 1, hlt⟩ j j'
          (by show (i.val - (i.val + 1)) + ((i.val + 1) - i.val) + ((j.val - j'.val) + (j'.val - j.val)) = 2; omega)
      · rw [nextRow_none x i hlt]
        trivial
    · rcases i with ⟨_ | k, hi⟩
      · trivial
      · by_cases hlt : k + 1 + 1 < R
        · rw [prevRow_eq none x ⟨k + 1, hi⟩ ⟨k, by omega⟩ rfl,
            nextRow_eq x ⟨k + 1, hi⟩ ⟨k + 1 + 1, hlt⟩ rfl]
          intro j
          exact H ⟨k, by omega⟩ ⟨k + 1 + 1, hlt⟩ j j
            (by show (k - (k + 1 + 1)) + ((k + 1 + 1) - k) + ((j.val - j.val) + (j.val - j.val)) = 2; omega)
        · rw [nextRow_none x ⟨k + 1, hi⟩ hlt]
          cases prevRow none x ⟨k + 1, hi⟩ <;> trivial
  · intro V i i' j j' hd
    have hc : (i'.val = i.val ∧ (j'.val = j.val + 2 ∨ j.val = j'.val + 2)) ∨
        (i'.val = i.val + 1 ∧ (j'.val = j.val + 1 ∨ j.val = j'.val + 1)) ∨
        (i.val = i'.val + 1 ∧ (j'.val = j.val + 1 ∨ j.val = j'.val + 1)) ∨
        (i'.val = i.val + 2 ∧ j'.val = j.val) ∨ (i.val = i'.val + 2 ∧ j'.val = j.val) := by omega
    rcases hc with ⟨hi, hj | hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩
    · rw [show i' = i from Fin.ext hi]
      exact (V i).1 j j' hj
    · rw [show i' = i from Fin.ext hi]
      exact fun h => (V i).1 j' j hj h.symm
    · have hb := (V i).2.1
      rw [nextRow_eq x i i' hi] at hb
      exact hb j j' hj
    · have hb := (V i').2.1
      rw [nextRow_eq x i' i hi] at hb
      exact fun h => hb j' j (by omega) h.symm
    · have hm : i.val + 1 < R := by omega
      have hb := (V ⟨i.val + 1, hm⟩).2.2
      rw [prevRow_eq none x ⟨i.val + 1, hm⟩ i rfl,
        nextRow_eq x ⟨i.val + 1, hm⟩ i' (by show i'.val = i.val + 1 + 1; omega)] at hb
      rw [show j' = j from Fin.ext hj]
      exact hb j
    · have hm : i'.val + 1 < R := by omega
      have hb := (V ⟨i'.val + 1, hm⟩).2.2
      rw [prevRow_eq none x ⟨i'.val + 1, hm⟩ i' rfl,
        nextRow_eq x ⟨i'.val + 1, hm⟩ i (by show i.val = i'.val + 1 + 1; omega)] at hb
      rw [show j' = j from Fin.ext hj]
      exact fun h => hb j h.symm

/-! ## Kernel form of the transfer -/

lemma sum_cons {m : ℕ} (f : (Fin (m + 1) → Fin 4) → ℕ) :
    ∑ s : Fin (m + 1) → Fin 4, f s = ∑ x : Fin 4, ∑ t : Fin m → Fin 4, f (Fin.cons x t) := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 4).symm _ _
    (fun s => by simp [Fin.consEquiv, Fin.cons_self_tail])

lemma sum_row (f : (Fin 5 → Fin 4) → ℕ) :
    ∑ s : Fin 5 → Fin 4, f s = ∑ x : Fin 4, ∑ y : Fin 4, ∑ z : Fin 4, ∑ u : Fin 4, ∑ v : Fin 4, f ![x, y, z, u, v] := by
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

lemma row_eta (r : Fin 5 → Fin 4) : r = ![r 0, r 1, r 2, r 3, r 4] := by
  funext j
  fin_cases j <;> rfl

/-! Fast Boolean forms of the conditions for the kernel checks, tied to the definitions cell by
cell (`rowRgs_cons`) or by `decide` over all small cases. -/

/-- `rowRgs c r` as a Boolean. -/
def rgsB (c : ℕ) (r : Fin 5 → Fin 4) : Bool :=
  decide ((r 0).val ≤ c) &&
    decide ((r 1).val ≤ max c ((r 0).val + 1)) &&
    decide ((r 2).val ≤ max (max c ((r 0).val + 1)) ((r 1).val + 1)) &&
    decide ((r 3).val ≤ max (max (max c ((r 0).val + 1)) ((r 1).val + 1)) ((r 2).val + 1)) &&
    decide ((r 4).val ≤ max (max (max (max c ((r 0).val + 1)) ((r 1).val + 1)) ((r 2).val + 1)) ((r 3).val + 1))

/-- `newc c r` by explicit maxima. -/
def newcB (c : ℕ) (r : Fin 5 → Fin 4) : ℕ :=
  max (max (max (max (max c ((r 0).val + 1)) ((r 1).val + 1)) ((r 2).val + 1)) ((r 3).val + 1)) ((r 4).val + 1)

/-- The entries two columns apart differ. -/
def rowNe (a0 a1 a2 a3 a4 : Fin 4) : Bool :=
  decide (a0 ≠ a2) && decide (a1 ≠ a3) && decide (a2 ≠ a4)

/-- The cell b differs from the cell a diagonally next to it. -/
def dB1 (a b : Fin 4) : Bool := decide (a ≠ b)

/-- The cell b differs from the cells a and a' diagonally next to it. -/
def dB2 (a a' b : Fin 4) : Bool := decide (a ≠ b) && decide (a' ≠ b)

/-- The condition read at cell 0 of the row below. -/
def G0 (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (b : Fin 4) : Bool :=
  (match q with | none => true | some p => decide (p 0 ≠ b)) && decide (r 0 ≠ r 2) && decide (r 1 ≠ r 3) && decide (r 2 ≠ r 4) && decide (r 1 ≠ b)

/-- The condition read at cell 1 of the row below. -/
def G1 (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (b : Fin 4) : Bool :=
  (match q with | none => true | some p => decide (p 1 ≠ b)) && decide (r 0 ≠ b) && decide (r 2 ≠ b)

/-- The condition read at cell 2 of the row below. -/
def G2 (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (b : Fin 4) : Bool :=
  (match q with | none => true | some p => decide (p 2 ≠ b)) && decide (r 1 ≠ b) && decide (r 3 ≠ b)

/-- The condition read at cell 3 of the row below. -/
def G3 (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (b : Fin 4) : Bool :=
  (match q with | none => true | some p => decide (p 3 ≠ b)) && decide (r 2 ≠ b) && decide (r 4 ≠ b)

/-- The condition read at cell 4 of the row below. -/
def G4 (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (b : Fin 4) : Bool :=
  (match q with | none => true | some p => decide (p 4 ≠ b)) && decide (r 3 ≠ b)

/-- The condition between the row r and the row t below it (the subblocks between them), as a
Boolean. -/
def belowB (r t : Fin 5 → Fin 4) : Bool :=
  rowNe (r 0) (r 1) (r 2) (r 3) (r 4) &&
    dB1 (r 1) (t 0) &&
    dB2 (r 0) (r 2) (t 1) &&
    dB2 (r 1) (r 3) (t 2) &&
    dB2 (r 2) (r 4) (t 3) &&
    dB1 (r 3) (t 4)

/-- `rowCond q r (some t)` as a Boolean. -/
def condB (q : Option (Fin 5 → Fin 4)) (r t : Fin 5 → Fin 4) : Bool :=
  G0 q r (t 0) &&
    G1 q r (t 1) &&
    G2 q r (t 2) &&
    G3 q r (t 3) &&
    G4 q r (t 4)

/-- `rowCond q r none` as a Boolean. -/
def endB (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) : Bool :=
  decide (r 0 ≠ r 2) && decide (r 1 ≠ r 3) && decide (r 2 ≠ r 4)


lemma rgsB_iff (c : ℕ) (r : Fin 5 → Fin 4) : rowRgs c r ↔ rgsB c r = true := by
  have e : rowRgs c r ↔ rowRgs c ![r 0, r 1, r 2, r 3, r 4] := by rw [← row_eta r]
  rw [e, rowRgs_cons, rowRgs_cons, rowRgs_cons, rowRgs_cons, rowRgs_cons]
  simp only [rgsB, rowRgs_zero, and_true, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

lemma newcB_eq' (c : ℕ) (r : Fin 5 → Fin 4) : newc c r = newcB c r := by
  have e : newc c r = newc c ![r 0, r 1, r 2, r 3, r 4] := by rw [← row_eta r]
  rw [e, newc_cons, newc_cons, newc_cons, newc_cons, newc_cons, newc_zero]
  rfl

lemma newcB_le (c : ℕ) (hc : c ≤ 4) (r : Fin 5 → Fin 4) : newcB c r ≤ 4 := by
  rw [← newcB_eq' c r]
  exact newc_le c hc r

lemma hrow_iffC (r : Fin 5 → Fin 4) : hrow r ↔ (r 0 ≠ r 2 ∧ r 1 ≠ r 3 ∧ r 2 ≠ r 4) := by
  constructor
  · intro h
    exact ⟨h 0 2 rfl, h 1 3 rfl, h 2 4 rfl⟩
  · intro h j j' hj
    have := j'.isLt
    rcases (by omega : j.val = 0 ∨ j.val = 1 ∨ j.val = 2) with e | e | e
    · obtain rfl : j = 0 := Fin.ext (by show j.val = 0; omega)
      obtain rfl : j' = 2 := Fin.ext (by show j'.val = 2; omega)
      exact h.1
    · obtain rfl : j = 1 := Fin.ext (by show j.val = 1; omega)
      obtain rfl : j' = 3 := Fin.ext (by show j'.val = 3; omega)
      exact h.2.1
    · obtain rfl : j = 2 := Fin.ext (by show j.val = 2; omega)
      obtain rfl : j' = 4 := Fin.ext (by show j'.val = 4; omega)
      exact h.2.2

lemma okBelow_iffC (r t : Fin 5 → Fin 4) :
    okBelow r (some t) ↔ (r 0 ≠ t 1 ∧ r 1 ≠ t 0 ∧ r 1 ≠ t 2 ∧ r 2 ≠ t 1 ∧ r 2 ≠ t 3 ∧ r 3 ≠ t 2 ∧ r 3 ≠ t 4 ∧ r 4 ≠ t 3) := by
  constructor
  · intro h
    exact ⟨h 0 1 (Or.inl rfl), h 1 0 (Or.inr rfl), h 1 2 (Or.inl rfl), h 2 1 (Or.inr rfl), h 2 3 (Or.inl rfl), h 3 2 (Or.inr rfl), h 3 4 (Or.inl rfl), h 4 3 (Or.inr rfl)⟩
  · intro h j j' hj
    have := j.isLt
    have := j'.isLt
    rcases hj with hj | hj
    · rcases (by omega : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3) with e | e | e | e
      · obtain rfl : j = 0 := Fin.ext (by show j.val = 0; omega)
        obtain rfl : j' = 1 := Fin.ext (by show j'.val = 1; omega)
        exact h.1
      · obtain rfl : j = 1 := Fin.ext (by show j.val = 1; omega)
        obtain rfl : j' = 2 := Fin.ext (by show j'.val = 2; omega)
        exact h.2.2.1
      · obtain rfl : j = 2 := Fin.ext (by show j.val = 2; omega)
        obtain rfl : j' = 3 := Fin.ext (by show j'.val = 3; omega)
        exact h.2.2.2.2.1
      · obtain rfl : j = 3 := Fin.ext (by show j.val = 3; omega)
        obtain rfl : j' = 4 := Fin.ext (by show j'.val = 4; omega)
        exact h.2.2.2.2.2.2.1
    · rcases (by omega : j'.val = 0 ∨ j'.val = 1 ∨ j'.val = 2 ∨ j'.val = 3) with e | e | e | e
      · obtain rfl : j' = 0 := Fin.ext (by show j'.val = 0; omega)
        obtain rfl : j = 1 := Fin.ext (by show j.val = 1; omega)
        exact h.2.1
      · obtain rfl : j' = 1 := Fin.ext (by show j'.val = 1; omega)
        obtain rfl : j = 2 := Fin.ext (by show j.val = 2; omega)
        exact h.2.2.2.1
      · obtain rfl : j' = 2 := Fin.ext (by show j'.val = 2; omega)
        obtain rfl : j = 3 := Fin.ext (by show j.val = 3; omega)
        exact h.2.2.2.2.2.1
      · obtain rfl : j' = 3 := Fin.ext (by show j'.val = 3; omega)
        obtain rfl : j = 4 := Fin.ext (by show j.val = 4; omega)
        exact h.2.2.2.2.2.2.2

lemma okTwo_iffC (p t : Fin 5 → Fin 4) : okTwo (some p) (some t) ↔ (p 0 ≠ t 0 ∧ p 1 ≠ t 1 ∧ p 2 ≠ t 2 ∧ p 3 ≠ t 3 ∧ p 4 ≠ t 4) := by
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

lemma condB_iff (q : Option (Fin 5 → Fin 4)) (r t : Fin 5 → Fin 4) : rowCond q r (some t) ↔ condB q r t = true := by
  rcases q with _ | p
  · have h2 : okTwo none (some t) := trivial
    simp only [rowCond, hrow_iffC, okBelow_iffC, h2, condB, G0, G1, G2, G3, G4, Bool.and_eq_true,
      Bool.true_and, decide_eq_true_eq, eq_self_iff_true, and_true, true_and]
    tauto
  · simp only [rowCond, hrow_iffC, okBelow_iffC, okTwo_iffC, condB, G0, G1, G2, G3, G4, Bool.and_eq_true,
      decide_eq_true_eq]
    tauto

lemma endB_iff (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) : rowCond q r none ↔ endB q r = true := by
  have h2 : okTwo q none := by rcases q with _ | p <;> trivial
  simp only [rowCond, okBelow, endB, hrow_iffC, h2, and_true, decide_eq_true_eq, Bool.and_eq_true,
    and_assoc]

lemma belowB_perm (σ : Equiv.Perm (Fin 4)) (r t : Fin 5 → Fin 4) :
    belowB (mapRow σ r) (mapRow σ t) = belowB r t := by
  simp [belowB, rowNe, dB1, dB2, mapRow]

lemma ren_reach (c : ℕ) (p r : Fin 5 → Fin 4) : belowB (renP c p r).1 (renP c p r).2 = belowB p r := by
  rw [renP_eq]
  exact belowB_perm _ p r

/-- One step of the transfer, the rows below r enumerated entry by entry. -/
def T (g : Option (Fin 5 → Fin 4) → (Fin 5 → Fin 4) → ℕ → ℕ) (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (c : ℕ) : ℕ :=
  if rgsB c r = true then
    ∑ x : Fin 4, ∑ y : Fin 4, ∑ z : Fin 4, ∑ u : Fin 4, ∑ v : Fin 4, (if condB q r ![x, y, z, u, v] = true then g (some r) ![x, y, z, u, v] (newcB c r) else 0)
  else 0

lemma W_succT (n : ℕ) (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (c : ℕ) :
    W (n + 1) q r c = T (W n) q r c := by
  rw [W_succ, sum_row]
  unfold T
  simp only [rgsB_iff, condB_iff, newcB_eq']

lemma T_congr (g g' : Option (Fin 5 → Fin 4) → (Fin 5 → Fin 4) → ℕ → ℕ) (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (c : ℕ)
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
    split_ifs with hs
    · exact h _ hs
    · rfl
  · rw [if_neg hr, if_neg hr]

/-- `T` with the sums over the cells of the row below cut as soon as a cell fails the condition. -/
def Tp (g : Option (Fin 5 → Fin 4) → (Fin 5 → Fin 4) → ℕ → ℕ) (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (c : ℕ) : ℕ :=
  if rgsB c r = true then
    ∑ x : Fin 4, (if G0 q r x = true then (∑ y : Fin 4, (if G1 q r y = true then (∑ z : Fin 4, (if G2 q r z = true then (∑ u : Fin 4, (if G3 q r u = true then (∑ v : Fin 4, (if G4 q r v = true then g (some r) ![x, y, z, u, v] (newcB c r) else 0)) else 0)) else 0)) else 0)) else 0)
  else 0

lemma T_eq_Tp (g : Option (Fin 5 → Fin 4) → (Fin 5 → Fin 4) → ℕ → ℕ) (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (c : ℕ) :
    T g q r c = Tp g q r c := by
  unfold T Tp
  by_cases hr : rgsB c r = true
  · rw [if_pos hr, if_pos hr]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases h0 : G0 q r x = true
    · rw [if_pos h0]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      by_cases h1 : G1 q r y = true
      · rw [if_pos h1]
        refine Finset.sum_congr rfl (fun z _ => ?_)
        by_cases h2 : G2 q r z = true
        · rw [if_pos h2]
          refine Finset.sum_congr rfl (fun u _ => ?_)
          by_cases h3 : G3 q r u = true
          · rw [if_pos h3]
            refine Finset.sum_congr rfl (fun v _ => ?_)
            by_cases h4 : G4 q r v = true
            · rw [if_pos h4, if_pos (show condB q r ![x, y, z, u, v] = true by simp [condB, h0, h1, h2, h3, h4])]
            · rw [if_neg h4, if_neg (show ¬ condB q r ![x, y, z, u, v] = true by simp [condB, h4])]
          · rw [if_neg h3]
            simp [condB, h3]
        · rw [if_neg h2]
          simp [condB, h2]
      · rw [if_neg h1]
        simp [condB, h1]
    · rw [if_neg h0]
      simp [condB, h0]
  · rw [if_neg hr, if_neg hr]

/-- W(0) as a function. -/
def W0f (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (c : ℕ) : ℕ :=
  if endB q r = true ∧ rgsB c r = true then 1 else 0

lemma W_zero' (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (c : ℕ) : W 0 q r c = W0f q r c := by
  rw [W_zero]
  unfold W0f
  simp only [endB_iff, rgsB_iff]

lemma reach_next (q : Option (Fin 5 → Fin 4)) (r t : Fin 5 → Fin 4) (h : condB q r t = true) : belowB r t = true := by
  simp only [condB, G0, G1, G2, G3, G4, Bool.and_eq_true] at h
  simp only [belowB, rowNe, dB1, dB2, Bool.and_eq_true]
  tauto

lemma inv_next (c : ℕ) (q : Option (Fin 5 → Fin 4)) (r t : Fin 5 → Fin 4) (h : condB q r t = true) :
    ∀ p, some r = some p → (∀ j, (p j).val < newcB c r) ∧ belowB p t = true := by
  intro p hp
  rw [← Option.some.inj hp]
  refine ⟨fun j => ?_, reach_next q r t h⟩
  rw [← newcB_eq' c r]
  exact (lt_newc c r _).2 (Or.inr ⟨j, le_refl _⟩)

/-- W(1..6) at the states with no row above, nested by the entries of r: W(j, none, r, c) is
the digit (j - 1) 5 + c of the cell in base 2048. -/
def LN : List (List (List (List (List ℕ)))) :=
  [[[[], [[], [1453180572104383707647412180116918515975124496976062754682669024068816994457294443800055214067695624, 0, 1307862670803325135658635611639437465659552560336606321501157221511887423010527824519476099277701144, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632], [1453180745337027927982355018679402890930572909263973899932024286088611935212716616966978451043024912, 0, 1307862670803325135658635611639437465659552560336606321501157221511887423010527824519476099277701144, 1307862670803325135658635611639437465659552560336606321501157221511887423010527824519476099277701144], [1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336, 0, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632]], [[], [1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 0, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648], [1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 0, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648], [1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 0, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648]], [[], [1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632], [1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632], [1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632]]], [[], [[1453180572104383707647412180116918515975124496976062754682669024068816994457294443800055214067695624, 0, 1307862670803325135658635611639437465659552560336606321501157221511887423010527824519476099277701144, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632], [], [1453180745337027927982355018679402890930572909263973899932024286088611935212716616966978451043024912, 0, 1307862670803325135658635611639437465659552560336606321501157221511887423010527824519476099277701144, 1307862670803325135658635611639437465659552560336606321501157221511887423010527824519476099277701144], [1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336, 0, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632]], [[1453180745337027927982355018679402890930572909263973899932024286088611935212716616966978451043024912, 1307862670803325135658635611639437465659552560336606321501157221511887423010527824519476099277701144, 0, 1307862670803325135658635611639437465659552560336606321501157221511887423010527824519476099277701144], [], [1453180745337027927982355018679402890930572909263973899932024286088611935212716616966978451043024912, 1307862670803325135658635611639437465659552560336606321501157221511887423010527824519476099277701144, 0, 1307862670803325135658635611639437465659552560336606321501157221511887423010527824519476099277701144], [1453180745337027927982355018679402890930572909263973899932024286088611935212716616966978451043024912, 1307862670803325135658635611639437465659552560336606321501157221511887423010527824519476099277701144, 0, 1307862670803325135658635611639437465659552560336606321501157221511887423010527824519476099277701144]], [[1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632], [], [1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632], [1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632]]], [[], [[1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104, 0, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648], [1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104, 0, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648], [], [1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104, 0, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648]], [[1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 0, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648], [1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 0, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648], [], [1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 0, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648]], [[1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648], [1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648], [], [1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648]]], [[], [[1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336, 0, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632], [1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336, 0, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632], [1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336, 0, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632]], [[1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 0, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632], [1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 0, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632], [1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 0, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632]], [[1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632], [1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632], [1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632]]]], [[[[], [0, 1453180572104342425933452383373689678342929360997651908905122366446052174673319941316071343567945728, 1307862670803250828573507977501598597974934164934624527712847426956776383940515872488563571098173440, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632], [0, 1453180745336945364554435425192945215666182637307152208376930970843082295644767611999010710043525120, 1307862670803250828573507977501598597974934164934624527712847426956776383940515872488563571098173440, 1307862670803250828573507977501598597974934164934624527712847426956776383940515872488563571098173440], [0, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632]], [], [[], [1307862670803250828573507977501598597974934164934624527712847426956776383940515872488563571098173440, 1453180745336945364554435425192945215666182637307152208376930970843082295644767611999010710043525120, 0, 1307862670803250828573507977501598597974934164934624527712847426956776383940515872488563571098173440], [1307862670803250828573507977501598597974934164934624527712847426956776383940515872488563571098173440, 1453180745336945364554435425192945215666182637307152208376930970843082295644767611999010710043525120, 0, 1307862670803250828573507977501598597974934164934624527712847426956776383940515872488563571098173440], [1307862670803250828573507977501598597974934164934624527712847426956776383940515872488563571098173440, 1453180745336945364554435425192945215666182637307152208376930970843082295644767611999010710043525120, 0, 1307862670803250828573507977501598597974934164934624527712847426956776383940515872488563571098173440]], [[], [1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632], [1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632], [1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632]]], [[[0, 1453180572104342425933452383373689678342929360997651908905122366446052174673319941316071343567945728, 1307862670803250828573507977501598597974934164934624527712847426956776383940515872488563571098173440, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632], [], [0, 1453180745336945364554435425192945215666182637307152208376930970843082295644767611999010710043525120, 1307862670803250828573507977501598597974934164934624527712847426956776383940515872488563571098173440, 1307862670803250828573507977501598597974934164934624527712847426956776383940515872488563571098173440], [0, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632]], [], [[1307862670803250828573507977501598597974934164934624527712847426956776383940515872488563571098173440, 1453180745336945364554435425192945215666182637307152208376930970843082295644767611999010710043525120, 0, 1307862670803250828573507977501598597974934164934624527712847426956776383940515872488563571098173440], [], [1307862670803250828573507977501598597974934164934624527712847426956776383940515872488563571098173440, 1453180745336945364554435425192945215666182637307152208376930970843082295644767611999010710043525120, 0, 1307862670803250828573507977501598597974934164934624527712847426956776383940515872488563571098173440], [1307862670803250828573507977501598597974934164934624527712847426956776383940515872488563571098173440, 1453180745336945364554435425192945215666182637307152208376930970843082295644767611999010710043525120, 0, 1307862670803250828573507977501598597974934164934624527712847426956776383940515872488563571098173440]], [[1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632], [], [1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632], [1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632]]], [[[0, 1453180745336945364554435425192945215666182637307152208376930970843082295644767611999010710043525120, 1307862670803250828573507977501598597974934164934624527712847426956776383940515872488563571098173440, 1307862670803250828573507977501598597974934164934624527712847426956776383940515872488563571098173440], [0, 1453180745336945364554435425192945215666182637307152208376930970843082295644767611999010710043525120, 1307862670803250828573507977501598597974934164934624527712847426956776383940515872488563571098173440, 1307862670803250828573507977501598597974934164934624527712847426956776383940515872488563571098173440], [], [0, 1453180745336945364554435425192945215666182637307152208376930970843082295644767611999010710043525120, 1307862670803250828573507977501598597974934164934624527712847426956776383940515872488563571098173440, 1307862670803250828573507977501598597974934164934624527712847426956776383940515872488563571098173440]], [], [[1307862670803250828573507977501598597974934164934624527712847426956776383940515872488563571098173440, 1453180745336945364554435425192945215666182637307152208376930970843082295644767611999010710043525120, 0, 1307862670803250828573507977501598597974934164934624527712847426956776383940515872488563571098173440], [1307862670803250828573507977501598597974934164934624527712847426956776383940515872488563571098173440, 1453180745336945364554435425192945215666182637307152208376930970843082295644767611999010710043525120, 0, 1307862670803250828573507977501598597974934164934624527712847426956776383940515872488563571098173440], [], [1307862670803250828573507977501598597974934164934624527712847426956776383940515872488563571098173440, 1453180745336945364554435425192945215666182637307152208376930970843082295644767611999010710043525120, 0, 1307862670803250828573507977501598597974934164934624527712847426956776383940515872488563571098173440]], [[1307862670803250828573507977501598597974934164934624527712847426956776383940515872488563571098173440, 1453180745336945364554435425192945215666182637307152208376930970843082295644767611999010710043525120, 1307862670803250828573507977501598597974934164934624527712847426956776383940515872488563571098173440], [1307862670803250828573507977501598597974934164934624527712847426956776383940515872488563571098173440, 1453180745336945364554435425192945215666182637307152208376930970843082295644767611999010710043525120, 1307862670803250828573507977501598597974934164934624527712847426956776383940515872488563571098173440], [], [1307862670803250828573507977501598597974934164934624527712847426956776383940515872488563571098173440, 1453180745336945364554435425192945215666182637307152208376930970843082295644767611999010710043525120, 1307862670803250828573507977501598597974934164934624527712847426956776383940515872488563571098173440]]], [[[0, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632], [0, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632], [0, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632]], [], [[1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336, 0, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632], [1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336, 0, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632], [1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336, 0, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632]], [[1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632], [1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632], [1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632]]]], [[[[], [0, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648], [0, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648], [0, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648]], [[], [1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 0, 1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648], [1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 0, 1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648], [1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 0, 1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648]], [], [[], [1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104], [1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104], [1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104]]], [[[0, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648], [], [0, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648], [0, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648]], [[1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 0, 1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648], [], [1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 0, 1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648], [1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 0, 1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648]], [], [[1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104], [], [1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104], [1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104]]], [[[0, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648], [0, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648], [], [0, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648]], [[1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 0, 1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648], [1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 0, 1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648], [], [1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 0, 1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648]], [], [[1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104], [1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104], [], [1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104]]], [[[0, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648], [0, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648], [0, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648]], [[1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 0, 1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648], [1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 0, 1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648], [1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 0, 1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648]], [], [[1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104], [1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104], [1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1307862670651069918232113263207597579876460381675910849254388178089368368556038113179705859425435648, 1453180745167855464175107964927626274194905669736327903545821347998380460485205437601077143067951104]]]], [[[[], [0, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336], [0, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336], [0, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336]], [[], [1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 0, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336], [1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 0, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336], [1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 0, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336]], [[], [1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 0, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336], [1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 0, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336], [1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 0, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336]]], [[[0, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336], [], [0, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336], [0, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336]], [[1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 0, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336], [], [1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 0, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336], [1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 0, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336]], [[1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 0, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336], [], [1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 0, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336], [1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 0, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336]]], [[[0, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336], [0, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336], [], [0, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336]], [[1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 0, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336], [1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 0, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336], [], [1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 0, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336]], [[1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 0, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336], [1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 0, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336], [], [1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 0, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336]]], [[[0, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336], [0, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336], [0, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336]], [[1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 0, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336], [1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 0, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336], [1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 0, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336]], [[1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 0, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336], [1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 0, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336], [1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 1307862358984565539055738389093512514202152267830297366329846497637752861145587048639112353658437632, 0, 1453180398871739487312469341554434141019676084688151609433313762049022053701872270633131977092366336]]]]]

/-- The same at the renamed pairs (p, r) (the values of p below c, in order of first occurrence), nested by the entries of p and then of r (0 elsewhere). -/
def LS : List (List (List (List (List (List (List (List (List (List ℕ))))))))) :=
  [[[[], [[], [[[], [[], [], [[], [], [[], [], [], [0, 0, 0, 254306630404374706289958405708926339621739152068009350128412356511069349248627924249907319577509888]], [[], [], [], [0, 0, 254306630404374706289958405708926339621739152068009350128412356511069349248627924249907319577509888]]], [[], [], [[], [], [0, 0, 0, 254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792]], [[], [], [0, 0, 254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792]]]], [[], [], [[], [], [], [[], [], [], [254306630404374706289958405708926339621739152068009350128412356511069349248627924249907319577509888, 0, 363295186291963866043776991231906568548726417434081975886455336999595115121301359400269285766987776]]], [[], [], [], [[], [], [254306630404374706289958405708926339621739152068009350128412356511069349248627924249907319577509888, 0, 363295186291963866043776991231906568548726417434081975886455336999595115121301359400269285766987776]]]], [[], [], [[], [], [[], [], [], [254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792, 0, 0, 363295099717934871828117335388608535254919021172037902358328440512255513425468067658282994273091584]]], [[], [], [[], [], [254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792, 0, 0, 363295099717934871828117335388608535254919021172037902358328440512255513425468067658282994273091584]]]]], [], [[], [[], [], [[], [], [[0, 0, 0, 104714469918698874810578320604043305026093959338563911104381110763048060717832712375801360334979072], [], [], [0, 0, 0, 179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928]], [[0, 0, 104714469918698874810578320604043305026093959338563911104381110763048060717832712375801360334979072], [], [], [0, 0, 179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928]]], [[], [], [[0, 0, 0, 179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928]], [[0, 0, 179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928]]]], [[], [], [[], [], [], [[104714469918698874810578320604043305026093959338563911104381110763048060717832712375801360334979072, 0, 149592099883855535409789316456167450851456355291832065069210535858279325835593029163467318272983040], [], [], [179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928, 0, 256443599800895203618953325922387993053187688231934983713769488185267419630530548410866355885047808]]], [[], [], [], [[179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928, 0, 256443599800895203618953325922387993053187688231934983713769488185267419630530548410866355885047808]]]], [[], [], [[], [], [[104714469918698874810578320604043305026093959338563911104381110763048060717832712375801360334979072, 0, 0, 149592099883855535409789316456167450851456355291832065069210535858279325835593029163467318272983040], [], [], [179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928, 0, 0, 256443599800895203618953325922387993053187688231934983713769488185267419630530548410866355885047808]]], [[], [], [[179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928, 0, 0, 256443599800895203618953325922387993053187688231934983713769488185267419630530548410866355885047808]]]]]], [[[], [[], [], [[], [], [], [[], [], [], [254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792, 363295099717934871828117335388608535254919021172037902358328440512255513425468067658282994273091584]]], [[], [], [], [[], [], [254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792, 363295099717934871828117335388608535254919021172037902358328440512255513425468067658282994273091584]]]], [[], [], [[], [[], [], [], [0, 0, 0, 254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792]], [], [[], [], [], [0, 254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792]]], [[], [[], [], [0, 0, 0, 254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792]], [], [[], [], [0, 254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792]]]], [[], [], [[], [[], [], [], [254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792, 0, 0, 363295099717934871828117335388608535254919021172037902358328440512255513425468067658282994273091584]]], [[], [[], [], [254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792, 0, 0, 363295099717934871828117335388608535254919021172037902358328440512255513425468067658282994273091584]]]]], [], [[], [[], [], [[], [], [], [[104714469918698874810578320604043305026093959338563911104381110763048060717832712375801360334979072, 149592099883855535409789316456167450851456355291832065069210535858279325835593029163467318272983040], [], [], [179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928, 256443599800895203618953325922387993053187688231934983713769488185267419630530548410866355885047808]]], [[], [], [], [[179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928, 256443599800895203618953325922387993053187688231934983713769488185267419630530548410866355885047808]]]], [[], [], [[], [[0, 0, 0, 104714469918698874810578320604043305026093959338563911104381110763048060717832712375801360334979072], [], [], [0, 0, 0, 179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928]], [], [[0, 104714469918698874810578320604043305026093959338563911104381110763048060717832712375801360334979072], [], [], [0, 179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928]]], [[], [[0, 0, 0, 179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928]], [], [[0, 179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928]]]], [[], [], [[], [[104714469918698874810578320604043305026093959338563911104381110763048060717832712375801360334979072, 0, 0, 149592099883855535409789316456167450851456355291832065069210535858279325835593029163467318272983040], [], [], [179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928, 0, 0, 256443599800895203618953325922387993053187688231934983713769488185267419630530548410866355885047808]]], [[], [[179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928, 0, 0, 256443599800895203618953325922387993053187688231934983713769488185267419630530548410866355885047808]]]]], [[], [[], [], [[], [], [], [[179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256, 256318444310509212792394539526134997448964561004881818763201518693717752759066160637117763227222016]]], [[], [], [], [[104663364760124595223067057392425909562440423975294724227316991138468730283124155659170905791135744, 149519092514463707427646910738033645360557645503988320771958602946684265159245741203895103866798080], [], [179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256, 256318444310509212792394539526134997448964561004881818763201518693717752759066160637117763227222016]]]], [[], [], [[], [[0, 0, 0, 179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256]], [], [[0, 179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256]]], [[], [[0, 0, 0, 104663364760124595223067057392425909562440423975294724227316991138468730283124155659170905791135744], [], [0, 0, 0, 179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256]], [], [[0, 104663364760124595223067057392425909562440423975294724227316991138468730283124155659170905791135744], [], [0, 179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256]]]], [[], [], [[], [[179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256, 0, 0, 256318444310509212792394539526134997448964561004881818763201518693717752759066160637117763227222016]]], [[], [[104663364760124595223067057392425909562440423975294724227316991138468730283124155659170905791135744, 0, 0, 149519092514463707427646910738033645360557645503988320771958602946684265159245741203895103866798080], [], [179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256, 0, 0, 256318444310509212792394539526134997448964561004881818763201518693717752759066160637117763227222016]]]]]]]], [[], [[[[[], [], [[], [], [[], [], [], [0, 0, 0, 254306630404374706289958405708926339621739152068009350128412356511069349248627924249907319577509888]], [[], [], [], [0, 0, 254306630404374706289958405708926339621739152068009350128412356511069349248627924249907319577509888]]], [[], [], [[], [], [0, 0, 0, 254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792]], [[], [], [0, 0, 254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792]]]], [], [[], [], [[], [], [], [[], [], [], [0, 254306630404374706289958405708926339621739152068009350128412356511069349248627924249907319577509888, 363295186291963866043776991231906568548726417434081975886455336999595115121301359400269285766987776]]], [[], [], [], [[], [], [0, 254306630404374706289958405708926339621739152068009350128412356511069349248627924249907319577509888, 363295186291963866043776991231906568548726417434081975886455336999595115121301359400269285766987776]]]], [[], [], [[], [], [[], [], [], [0, 254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792, 0, 363295099717934871828117335388608535254919021172037902358328440512255513425468067658282994273091584]]], [[], [], [[], [], [0, 254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792, 0, 363295099717934871828117335388608535254919021172037902358328440512255513425468067658282994273091584]]]]], [], [[[], [], [[], [], [[0, 0, 0, 104714469918698874810578320604043305026093959338563911104381110763048060717832712375801360334979072], [], [], [0, 0, 0, 179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928]], [[0, 0, 104714469918698874810578320604043305026093959338563911104381110763048060717832712375801360334979072], [], [], [0, 0, 179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928]]], [[], [], [[0, 0, 0, 179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928]], [[0, 0, 179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928]]]], [], [[], [], [[], [], [], [[0, 104714469918698874810578320604043305026093959338563911104381110763048060717832712375801360334979072, 149592099883855535409789316456167450851456355291832065069210535858279325835593029163467318272983040], [], [], [0, 179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928, 256443599800895203618953325922387993053187688231934983713769488185267419630530548410866355885047808]]], [[], [], [], [[0, 179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928, 256443599800895203618953325922387993053187688231934983713769488185267419630530548410866355885047808]]]], [[], [], [[], [], [[0, 104714469918698874810578320604043305026093959338563911104381110763048060717832712375801360334979072, 0, 149592099883855535409789316456167450851456355291832065069210535858279325835593029163467318272983040], [], [], [0, 179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928, 0, 256443599800895203618953325922387993053187688231934983713769488185267419630530548410866355885047808]]], [[], [], [[0, 179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928, 0, 256443599800895203618953325922387993053187688231934983713769488185267419630530548410866355885047808]]]]]], [], [[[[], [], [[], [], [], [[], [], [], [363295099717934871828117335388608535254919021172037902358328440512255513425468067658282994273091584, 254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792]]], [[], [], [], [[], [], [363295099717934871828117335388608535254919021172037902358328440512255513425468067658282994273091584, 254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792]]]], [], [[], [], [[[], [], [], [0, 0, 0, 254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792]], [], [], [[], [], [], [254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792]]], [[[], [], [0, 0, 0, 254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792]], [], [], [[], [], [254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792]]]], [[], [], [[[], [], [], [0, 254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792, 0, 363295099717934871828117335388608535254919021172037902358328440512255513425468067658282994273091584]]], [[[], [], [0, 254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792, 0, 363295099717934871828117335388608535254919021172037902358328440512255513425468067658282994273091584]]]]], [], [[[], [], [[], [], [], [[149592099883855535409789316456167450851456355291832065069210535858279325835593029163467318272983040, 104714469918698874810578320604043305026093959338563911104381110763048060717832712375801360334979072], [], [], [256443599800895203618953325922387993053187688231934983713769488185267419630530548410866355885047808, 179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928]]], [[], [], [], [[256443599800895203618953325922387993053187688231934983713769488185267419630530548410866355885047808, 179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928]]]], [], [[], [], [[[0, 0, 0, 104714469918698874810578320604043305026093959338563911104381110763048060717832712375801360334979072], [], [], [0, 0, 0, 179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928]], [], [], [[104714469918698874810578320604043305026093959338563911104381110763048060717832712375801360334979072], [], [], [179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928]]], [[[0, 0, 0, 179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928]], [], [], [[179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928]]]], [[], [], [[[0, 104714469918698874810578320604043305026093959338563911104381110763048060717832712375801360334979072, 0, 149592099883855535409789316456167450851456355291832065069210535858279325835593029163467318272983040], [], [], [0, 179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928, 0, 256443599800895203618953325922387993053187688231934983713769488185267419630530548410866355885047808]]], [[[0, 179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928, 0, 256443599800895203618953325922387993053187688231934983713769488185267419630530548410866355885047808]]]]], [[[], [], [[], [], [], [[256318444310509212792394539526134997448964561004881818763201518693717752759066160637117763227222016, 179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256]]], [[], [], [], [[149519092514463707427646910738033645360557645503988320771958602946684265159245741203895103866798080, 104663364760124595223067057392425909562440423975294724227316991138468730283124155659170905791135744], [], [256318444310509212792394539526134997448964561004881818763201518693717752759066160637117763227222016, 179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256]]]], [], [[], [], [[[0, 0, 0, 179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256]], [], [], [[179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256]]], [[[0, 0, 0, 104663364760124595223067057392425909562440423975294724227316991138468730283124155659170905791135744], [], [0, 0, 0, 179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256]], [], [], [[104663364760124595223067057392425909562440423975294724227316991138468730283124155659170905791135744], [], [179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256]]]], [[], [], [[[0, 179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256, 0, 256318444310509212792394539526134997448964561004881818763201518693717752759066160637117763227222016]]], [[[0, 104663364760124595223067057392425909562440423975294724227316991138468730283124155659170905791135744, 0, 149519092514463707427646910738033645360557645503988320771958602946684265159245741203895103866798080], [], [0, 179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256, 0, 256318444310509212792394539526134997448964561004881818763201518693717752759066160637117763227222016]]]]]]], [[[[[], [[], [], [[], [], [], [0, 0, 0, 254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792]], [[], [], [], [0, 0, 254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792]]], [], [[], [], [[], [0, 0, 0, 254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792]], [[], [0, 0, 254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792]]]], [], [[], [[], [], [], [[], [], [], [0, 254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792, 363295099717934871828117335388608535254919021172037902358328440512255513425468067658282994273091584]]], [], [[], [], [], [[], [0, 254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792, 363295099717934871828117335388608535254919021172037902358328440512255513425468067658282994273091584]]]], [[], [[], [], [[], [], [], [0, 254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792, 0, 363295099717934871828117335388608535254919021172037902358328440512255513425468067658282994273091584]]], [], [[], [], [[], [0, 254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792, 0, 363295099717934871828117335388608535254919021172037902358328440512255513425468067658282994273091584]]]]], [[[], [[], [], [[0, 0, 0, 104714469918698874810578320604043305026093959338563911104381110763048060717832712375801360334979072], [], [], [0, 0, 0, 179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928]], [[0, 0, 104714469918698874810578320604043305026093959338563911104381110763048060717832712375801360334979072], [], [], [0, 0, 179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928]]], [], [[], [], [[0, 0, 0, 179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928]], [[0, 0, 179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928]]]], [], [[], [[], [], [], [[0, 104714469918698874810578320604043305026093959338563911104381110763048060717832712375801360334979072, 149592099883855535409789316456167450851456355291832065069210535858279325835593029163467318272983040], [], [], [0, 179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928, 256443599800895203618953325922387993053187688231934983713769488185267419630530548410866355885047808]]], [], [[], [], [], [[0, 179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928, 256443599800895203618953325922387993053187688231934983713769488185267419630530548410866355885047808]]]], [[], [[], [], [[0, 104714469918698874810578320604043305026093959338563911104381110763048060717832712375801360334979072, 0, 149592099883855535409789316456167450851456355291832065069210535858279325835593029163467318272983040], [], [], [0, 179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928, 0, 256443599800895203618953325922387993053187688231934983713769488185267419630530548410866355885047808]]], [], [[], [], [[0, 179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928, 0, 256443599800895203618953325922387993053187688231934983713769488185267419630530548410866355885047808]]]]], [], [[[], [[], [], [[0, 0, 0, 179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256]], [[0, 0, 179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256]]], [], [[], [], [[0, 0, 0, 104663364760124595223067057392425909562440423975294724227316991138468730283124155659170905791135744], [0, 0, 0, 179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256]], [[0, 0, 104663364760124595223067057392425909562440423975294724227316991138468730283124155659170905791135744], [0, 0, 179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256]]]], [], [[], [[], [], [], [[0, 179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256, 256318444310509212792394539526134997448964561004881818763201518693717752759066160637117763227222016]]], [], [[], [], [], [[0, 104663364760124595223067057392425909562440423975294724227316991138468730283124155659170905791135744, 149519092514463707427646910738033645360557645503988320771958602946684265159245741203895103866798080], [0, 179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256, 256318444310509212792394539526134997448964561004881818763201518693717752759066160637117763227222016]]]], [[], [[], [], [[0, 179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256, 0, 256318444310509212792394539526134997448964561004881818763201518693717752759066160637117763227222016]]], [], [[], [], [[0, 104663364760124595223067057392425909562440423975294724227316991138468730283124155659170905791135744, 0, 149519092514463707427646910738033645360557645503988320771958602946684265159245741203895103866798080], [0, 179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256, 0, 256318444310509212792394539526134997448964561004881818763201518693717752759066160637117763227222016]]]]]], [], [[[[], [[], [], [], [[], [], [], [363295099717934871828117335388608535254919021172037902358328440512255513425468067658282994273091584, 254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792]]], [], [[], [], [], [[], [363295099717934871828117335388608535254919021172037902358328440512255513425468067658282994273091584, 254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792]]]], [], [[], [[[], [], [], [0, 0, 0, 254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792]], [], [], [[], [], [], [254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792]]], [], [[[], [0, 0, 0, 254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792]], [], [], [[], [254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792]]]], [[], [[[], [], [], [0, 254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792, 0, 363295099717934871828117335388608535254919021172037902358328440512255513425468067658282994273091584]]], [], [[[], [0, 254306569802554410338996632483841198088998788771796646380812922332782510398476555042425429968289792, 0, 363295099717934871828117335388608535254919021172037902358328440512255513425468067658282994273091584]]]]], [[[], [[], [], [], [[149592099883855535409789316456167450851456355291832065069210535858279325835593029163467318272983040, 104714469918698874810578320604043305026093959338563911104381110763048060717832712375801360334979072], [], [], [256443599800895203618953325922387993053187688231934983713769488185267419630530548410866355885047808, 179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928]]], [], [[], [], [], [[256443599800895203618953325922387993053187688231934983713769488185267419630530548410866355885047808, 179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928]]]], [], [[], [[[0, 0, 0, 104714469918698874810578320604043305026093959338563911104381110763048060717832712375801360334979072], [], [], [0, 0, 0, 179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928]], [], [], [[104714469918698874810578320604043305026093959338563911104381110763048060717832712375801360334979072], [], [], [179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928]]], [], [[[0, 0, 0, 179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928]], [], [], [[179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928]]]], [[], [[[0, 104714469918698874810578320604043305026093959338563911104381110763048060717832712375801360334979072, 0, 149592099883855535409789316456167450851456355291832065069210535858279325835593029163467318272983040], [], [], [0, 179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928, 0, 256443599800895203618953325922387993053187688231934983713769488185267419630530548410866355885047808]]], [], [[[0, 179510519860626642574787476543942251557546374055180278742597016547915285558154633709104594763644928, 0, 256443599800895203618953325922387993053187688231934983713769488185267419630530548410866355885047808]]]]], [], [[[], [[], [], [], [[256318444310509212792394539526134997448964561004881818763201518693717752759066160637117763227222016, 179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256]]], [], [[], [], [], [[149519092514463707427646910738033645360557645503988320771958602946684265159245741203895103866798080, 104663364760124595223067057392425909562440423975294724227316991138468730283124155659170905791135744], [256318444310509212792394539526134997448964561004881818763201518693717752759066160637117763227222016, 179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256]]]], [], [[], [[[0, 0, 0, 179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256]], [], [], [[179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256]]], [], [[[0, 0, 0, 104663364760124595223067057392425909562440423975294724227316991138468730283124155659170905791135744], [0, 0, 0, 179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256]], [], [], [[104663364760124595223067057392425909562440423975294724227316991138468730283124155659170905791135744], [179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256]]]], [[], [[[0, 179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256, 0, 256318444310509212792394539526134997448964561004881818763201518693717752759066160637117763227222016]]], [], [[[0, 104663364760124595223067057392425909562440423975294724227316991138468730283124155659170905791135744, 0, 149519092514463707427646910738033645360557645503988320771958602946684265159245741203895103866798080], [0, 179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256, 0, 256318444310509212792394539526134997448964561004881818763201518693717752759066160637117763227222016]]]]]], [[[[], [[], [], [[], [], [], [363117796106554718157142168314236349537371476505775316754444434440751240358886580070358014773690368, 254182457274588302769285067509471339036734758128179371297171725201336545288472418119515510285533184]]], [], [[], [], [[], [363117796106554718157142168314236349537371476505775316754444434440751240358886580070358014773690368, 254182457274588302769285067509471339036734758128179371297171725201336545288472418119515510285533184]]]], [], [[], [[[], [], [], [0, 254182457274588302769285067509471339036734758128179371297171725201336545288472418119515510285533184, 363117796106554718157142168314236349537371476505775316754444434440751240358886580070358014773690368]]], [], [[[], [0, 254182457274588302769285067509471339036734758128179371297171725201336545288472418119515510285533184, 363117796106554718157142168314236349537371476505775316754444434440751240358886580070358014773690368]]]], [[], [[[], [], [], [0, 0, 254182457274588302769285067509471339036734758128179371297171725201336545288472418119515510285533184]], [], [[], [], [], [254182457274588302769285067509471339036734758128179371297171725201336545288472418119515510285533184]]], [], [[[], [0, 0, 254182457274588302769285067509471339036734758128179371297171725201336545288472418119515510285533184]], [], [[], [254182457274588302769285067509471339036734758128179371297171725201336545288472418119515510285533184]]]]], [[[], [[], [], [[149519092514463707427646910738033645360557645503988320771958602946684265159245741203895103866798080, 104663364760124595223067057392425909562440423975294724227316991138468730283124155659170905791135744], [], [], [256318444310509212792394539526134997448964561004881818763201518693717752759066160637117763227222016, 179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256]]], [], [[], [], [[256318444310509212792394539526134997448964561004881818763201518693717752759066160637117763227222016, 179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256]]]], [], [[], [[[0, 104663364760124595223067057392425909562440423975294724227316991138468730283124155659170905791135744, 149519092514463707427646910738033645360557645503988320771958602946684265159245741203895103866798080], [], [], [0, 179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256, 256318444310509212792394539526134997448964561004881818763201518693717752759066160637117763227222016]]], [], [[[0, 179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256, 256318444310509212792394539526134997448964561004881818763201518693717752759066160637117763227222016]]]], [[], [[[0, 0, 104663364760124595223067057392425909562440423975294724227316991138468730283124155659170905791135744], [], [], [0, 0, 179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256]], [], [[104663364760124595223067057392425909562440423975294724227316991138468730283124155659170905791135744], [], [], [179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256]]], [], [[[0, 0, 179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256]], [], [[179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256]]]]], [], [[[], [[], [], [[256318444310509212792394539526134997448964561004881818763201518693717752759066160637117763227222016, 179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256]]], [], [[], [], [[149519092514463707427646910738033645360557645503988320771958602946684265159245741203895103866798080, 104663364760124595223067057392425909562440423975294724227316991138468730283124155659170905791135744], [256318444310509212792394539526134997448964561004881818763201518693717752759066160637117763227222016, 179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256]]]], [], [[], [[[0, 179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256, 256318444310509212792394539526134997448964561004881818763201518693717752759066160637117763227222016]]], [], [[[0, 104663364760124595223067057392425909562440423975294724227316991138468730283124155659170905791135744, 149519092514463707427646910738033645360557645503988320771958602946684265159245741203895103866798080], [0, 179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256, 256318444310509212792394539526134997448964561004881818763201518693717752759066160637117763227222016]]]], [[], [[[0, 0, 179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256]], [], [[179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256]]], [], [[[0, 0, 104663364760124595223067057392425909562440423975294724227316991138468730283124155659170905791135744], [0, 0, 179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256]], [], [[104663364760124595223067057392425909562440423975294724227316991138468730283124155659170905791135744], [179422911017356448996176062450948624299587591051737047762244358169902637785798286889334411945312256]]]]]]]]]]

/-- The cell of the tables at the state (q, r). -/
def cell (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) : ℕ :=
  match q with
  | none => ((((LN.getD (r 0).val []).getD (r 1).val []).getD (r 2).val []).getD (r 3).val []).getD (r 4).val 0
  | some p => (((((((((LS.getD (p 0).val []).getD (p 1).val []).getD (p 2).val []).getD (p 3).val []).getD (p 4).val []).getD (r 0).val []).getD (r 1).val []).getD (r 2).val []).getD (r 3).val []).getD (r 4).val 0

/-- W(1) as a table. -/
def tab1 (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (c : ℕ) : ℕ :=
  cell q r / 2048 ^ c % 2048

/-- W(1) read at the renamed pair. -/
def tabc1 (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (c : ℕ) : ℕ :=
  match q with
  | none => tab1 none r c
  | some p => tab1 (some (renP c p r).1) (renP c p r).2 c

/-- W(2) as a table. -/
def tab2 (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (c : ℕ) : ℕ :=
  cell q r / 2048 ^ (5 + c) % 2048

/-- W(2) read at the renamed pair. -/
def tabc2 (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (c : ℕ) : ℕ :=
  match q with
  | none => tab2 none r c
  | some p => tab2 (some (renP c p r).1) (renP c p r).2 c

/-- W(3) as a table. -/
def tab3 (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (c : ℕ) : ℕ :=
  cell q r / 2048 ^ (10 + c) % 2048

/-- W(3) read at the renamed pair. -/
def tabc3 (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (c : ℕ) : ℕ :=
  match q with
  | none => tab3 none r c
  | some p => tab3 (some (renP c p r).1) (renP c p r).2 c

/-- W(4) as a table. -/
def tab4 (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (c : ℕ) : ℕ :=
  cell q r / 2048 ^ (15 + c) % 2048

/-- W(4) read at the renamed pair. -/
def tabc4 (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (c : ℕ) : ℕ :=
  match q with
  | none => tab4 none r c
  | some p => tab4 (some (renP c p r).1) (renP c p r).2 c

/-- W(5) as a table. -/
def tab5 (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (c : ℕ) : ℕ :=
  cell q r / 2048 ^ (20 + c) % 2048

/-- W(5) read at the renamed pair. -/
def tabc5 (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (c : ℕ) : ℕ :=
  match q with
  | none => tab5 none r c
  | some p => tab5 (some (renP c p r).1) (renP c p r).2 c

/-- W(6) as a table. -/
def tab6 (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (c : ℕ) : ℕ :=
  cell q r / 2048 ^ (25 + c) % 2048

/-- W(6) read at the renamed pair. -/
def tabc6 (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (c : ℕ) : ℕ :=
  match q with
  | none => tab6 none r c
  | some p => tab6 (some (renP c p r).1) (renP c p r).2 c

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxSize 1024 in
lemma checks_all :
    (∀ c : Fin 5, ∀ p1 : Fin 4, p1.val < c.val → ∀ p2 : Fin 4, p2.val < c.val → ∀ p3 : Fin 4, p3.val < c.val → ∀ p4 : Fin 4, p4.val < c.val → ∀ p5 : Fin 4, p5.val < c.val →
    (∀ j, ((renP c.val ![p1, p2, p3, p4, p5] ![p1, p2, p3, p4, p5]).1 j).val < c.val) ∧
      ((renP c.val ![p1, p2, p3, p4, p5] ![p1, p2, p3, p4, p5]).1 0).val = 0 ∧ ((renP c.val ![p1, p2, p3, p4, p5] ![p1, p2, p3, p4, p5]).1 1).val ≤ ((renP c.val ![p1, p2, p3, p4, p5] ![p1, p2, p3, p4, p5]).1 0).val + 1 ∧ ((renP c.val ![p1, p2, p3, p4, p5] ![p1, p2, p3, p4, p5]).1 2).val ≤ max ((renP c.val ![p1, p2, p3, p4, p5] ![p1, p2, p3, p4, p5]).1 0).val ((renP c.val ![p1, p2, p3, p4, p5] ![p1, p2, p3, p4, p5]).1 1).val + 1 ∧ ((renP c.val ![p1, p2, p3, p4, p5] ![p1, p2, p3, p4, p5]).1 3).val ≤ max (max ((renP c.val ![p1, p2, p3, p4, p5] ![p1, p2, p3, p4, p5]).1 0).val ((renP c.val ![p1, p2, p3, p4, p5] ![p1, p2, p3, p4, p5]).1 1).val) ((renP c.val ![p1, p2, p3, p4, p5] ![p1, p2, p3, p4, p5]).1 2).val + 1 ∧ ((renP c.val ![p1, p2, p3, p4, p5] ![p1, p2, p3, p4, p5]).1 4).val ≤ max (max (max ((renP c.val ![p1, p2, p3, p4, p5] ![p1, p2, p3, p4, p5]).1 0).val ((renP c.val ![p1, p2, p3, p4, p5] ![p1, p2, p3, p4, p5]).1 1).val) ((renP c.val ![p1, p2, p3, p4, p5] ![p1, p2, p3, p4, p5]).1 2).val) ((renP c.val ![p1, p2, p3, p4, p5] ![p1, p2, p3, p4, p5]).1 3).val + 1) ∧
    (∀ y1 y2 y3 y4 y5 : Fin 4,
    Tp W0f none ![y1, y2, y3, y4, y5] 0 = tab1 none ![y1, y2, y3, y4, y5] 0) ∧
    (∀ c : Fin 5, ∀ y1 : Fin 4,
    ∀ p1 : Fin 4, p1.val < c.val → p1.val = 0 →
    ∀ p2 : Fin 4, p2.val < c.val → p2.val ≤ p1.val + 1 →
    ∀ p3 : Fin 4, p3.val < c.val → p3.val ≤ max p1.val p2.val + 1 →
    ∀ p4 : Fin 4, p4.val < c.val → p4.val ≤ max (max p1.val p2.val) p3.val + 1 →
    ∀ p5 : Fin 4, p5.val < c.val → p5.val ≤ max (max (max p1.val p2.val) p3.val) p4.val + 1 →
    rowNe p1 p2 p3 p4 p5 = true → dB1 p2 y1 = true →
    ∀ y2 : Fin 4, dB2 p1 p3 y2 = true →
    ∀ y3 : Fin 4, dB2 p2 p4 y3 = true →
    ∀ y4 : Fin 4, dB2 p3 p5 y4 = true →
    ∀ y5 : Fin 4, dB1 p4 y5 = true →
    Tp W0f (some ![p1, p2, p3, p4, p5]) ![y1, y2, y3, y4, y5] c.val = tab1 (some ![p1, p2, p3, p4, p5]) ![y1, y2, y3, y4, y5] c.val) ∧
    (∀ y1 y2 y3 y4 y5 : Fin 4,
    Tp tabc1 none ![y1, y2, y3, y4, y5] 0 = tab2 none ![y1, y2, y3, y4, y5] 0) ∧
    (∀ c : Fin 5, ∀ y1 : Fin 4,
    ∀ p1 : Fin 4, p1.val < c.val → p1.val = 0 →
    ∀ p2 : Fin 4, p2.val < c.val → p2.val ≤ p1.val + 1 →
    ∀ p3 : Fin 4, p3.val < c.val → p3.val ≤ max p1.val p2.val + 1 →
    ∀ p4 : Fin 4, p4.val < c.val → p4.val ≤ max (max p1.val p2.val) p3.val + 1 →
    ∀ p5 : Fin 4, p5.val < c.val → p5.val ≤ max (max (max p1.val p2.val) p3.val) p4.val + 1 →
    rowNe p1 p2 p3 p4 p5 = true → dB1 p2 y1 = true →
    ∀ y2 : Fin 4, dB2 p1 p3 y2 = true →
    ∀ y3 : Fin 4, dB2 p2 p4 y3 = true →
    ∀ y4 : Fin 4, dB2 p3 p5 y4 = true →
    ∀ y5 : Fin 4, dB1 p4 y5 = true →
    Tp tabc1 (some ![p1, p2, p3, p4, p5]) ![y1, y2, y3, y4, y5] c.val = tab2 (some ![p1, p2, p3, p4, p5]) ![y1, y2, y3, y4, y5] c.val) ∧
    (∀ y1 y2 y3 y4 y5 : Fin 4,
    Tp tabc2 none ![y1, y2, y3, y4, y5] 0 = tab3 none ![y1, y2, y3, y4, y5] 0) ∧
    (∀ c : Fin 5, ∀ y1 : Fin 4,
    ∀ p1 : Fin 4, p1.val < c.val → p1.val = 0 →
    ∀ p2 : Fin 4, p2.val < c.val → p2.val ≤ p1.val + 1 →
    ∀ p3 : Fin 4, p3.val < c.val → p3.val ≤ max p1.val p2.val + 1 →
    ∀ p4 : Fin 4, p4.val < c.val → p4.val ≤ max (max p1.val p2.val) p3.val + 1 →
    ∀ p5 : Fin 4, p5.val < c.val → p5.val ≤ max (max (max p1.val p2.val) p3.val) p4.val + 1 →
    rowNe p1 p2 p3 p4 p5 = true → dB1 p2 y1 = true →
    ∀ y2 : Fin 4, dB2 p1 p3 y2 = true →
    ∀ y3 : Fin 4, dB2 p2 p4 y3 = true →
    ∀ y4 : Fin 4, dB2 p3 p5 y4 = true →
    ∀ y5 : Fin 4, dB1 p4 y5 = true →
    Tp tabc2 (some ![p1, p2, p3, p4, p5]) ![y1, y2, y3, y4, y5] c.val = tab3 (some ![p1, p2, p3, p4, p5]) ![y1, y2, y3, y4, y5] c.val) ∧
    (∀ y1 y2 y3 y4 y5 : Fin 4,
    Tp tabc3 none ![y1, y2, y3, y4, y5] 0 = tab4 none ![y1, y2, y3, y4, y5] 0) ∧
    (∀ c : Fin 5, ∀ y1 : Fin 4,
    ∀ p1 : Fin 4, p1.val < c.val → p1.val = 0 →
    ∀ p2 : Fin 4, p2.val < c.val → p2.val ≤ p1.val + 1 →
    ∀ p3 : Fin 4, p3.val < c.val → p3.val ≤ max p1.val p2.val + 1 →
    ∀ p4 : Fin 4, p4.val < c.val → p4.val ≤ max (max p1.val p2.val) p3.val + 1 →
    ∀ p5 : Fin 4, p5.val < c.val → p5.val ≤ max (max (max p1.val p2.val) p3.val) p4.val + 1 →
    rowNe p1 p2 p3 p4 p5 = true → dB1 p2 y1 = true →
    ∀ y2 : Fin 4, dB2 p1 p3 y2 = true →
    ∀ y3 : Fin 4, dB2 p2 p4 y3 = true →
    ∀ y4 : Fin 4, dB2 p3 p5 y4 = true →
    ∀ y5 : Fin 4, dB1 p4 y5 = true →
    Tp tabc3 (some ![p1, p2, p3, p4, p5]) ![y1, y2, y3, y4, y5] c.val = tab4 (some ![p1, p2, p3, p4, p5]) ![y1, y2, y3, y4, y5] c.val) ∧
    (∀ y1 y2 y3 y4 y5 : Fin 4,
    Tp tabc4 none ![y1, y2, y3, y4, y5] 0 = tab5 none ![y1, y2, y3, y4, y5] 0) ∧
    (∀ c : Fin 5, ∀ y1 : Fin 4,
    ∀ p1 : Fin 4, p1.val < c.val → p1.val = 0 →
    ∀ p2 : Fin 4, p2.val < c.val → p2.val ≤ p1.val + 1 →
    ∀ p3 : Fin 4, p3.val < c.val → p3.val ≤ max p1.val p2.val + 1 →
    ∀ p4 : Fin 4, p4.val < c.val → p4.val ≤ max (max p1.val p2.val) p3.val + 1 →
    ∀ p5 : Fin 4, p5.val < c.val → p5.val ≤ max (max (max p1.val p2.val) p3.val) p4.val + 1 →
    rowNe p1 p2 p3 p4 p5 = true → dB1 p2 y1 = true →
    ∀ y2 : Fin 4, dB2 p1 p3 y2 = true →
    ∀ y3 : Fin 4, dB2 p2 p4 y3 = true →
    ∀ y4 : Fin 4, dB2 p3 p5 y4 = true →
    ∀ y5 : Fin 4, dB1 p4 y5 = true →
    Tp tabc4 (some ![p1, p2, p3, p4, p5]) ![y1, y2, y3, y4, y5] c.val = tab5 (some ![p1, p2, p3, p4, p5]) ![y1, y2, y3, y4, y5] c.val) ∧
    (∀ y1 y2 y3 y4 y5 : Fin 4,
    Tp tabc5 none ![y1, y2, y3, y4, y5] 0 = tab6 none ![y1, y2, y3, y4, y5] 0) ∧
    (∀ c : Fin 5, ∀ y1 : Fin 4,
    ∀ p1 : Fin 4, p1.val < c.val → p1.val = 0 →
    ∀ p2 : Fin 4, p2.val < c.val → p2.val ≤ p1.val + 1 →
    ∀ p3 : Fin 4, p3.val < c.val → p3.val ≤ max p1.val p2.val + 1 →
    ∀ p4 : Fin 4, p4.val < c.val → p4.val ≤ max (max p1.val p2.val) p3.val + 1 →
    ∀ p5 : Fin 4, p5.val < c.val → p5.val ≤ max (max (max p1.val p2.val) p3.val) p4.val + 1 →
    rowNe p1 p2 p3 p4 p5 = true → dB1 p2 y1 = true →
    ∀ y2 : Fin 4, dB2 p1 p3 y2 = true →
    ∀ y3 : Fin 4, dB2 p2 p4 y3 = true →
    ∀ y4 : Fin 4, dB2 p3 p5 y4 = true →
    ∀ y5 : Fin 4, dB1 p4 y5 = true →
    Tp tabc5 (some ![p1, p2, p3, p4, p5]) ![y1, y2, y3, y4, y5] c.val = tab6 (some ![p1, p2, p3, p4, p5]) ![y1, y2, y3, y4, y5] c.val) ∧
    (∀ y1 y2 y3 y4 y5 : Fin 4,
    Tp tabc6 none ![y1, y2, y3, y4, y5] 0 =
      2 * tabc6 none ![y1, y2, y3, y4, y5] 0 + 2 * tabc4 none ![y1, y2, y3, y4, y5] 0 + tabc3 none ![y1, y2, y3, y4, y5] 0) ∧
    (∀ c : Fin 5, ∀ y1 : Fin 4,
    ∀ p1 : Fin 4, p1.val < c.val → p1.val = 0 →
    ∀ p2 : Fin 4, p2.val < c.val → p2.val ≤ p1.val + 1 →
    ∀ p3 : Fin 4, p3.val < c.val → p3.val ≤ max p1.val p2.val + 1 →
    ∀ p4 : Fin 4, p4.val < c.val → p4.val ≤ max (max p1.val p2.val) p3.val + 1 →
    ∀ p5 : Fin 4, p5.val < c.val → p5.val ≤ max (max (max p1.val p2.val) p3.val) p4.val + 1 →
    rowNe p1 p2 p3 p4 p5 = true → dB1 p2 y1 = true →
    ∀ y2 : Fin 4, dB2 p1 p3 y2 = true →
    ∀ y3 : Fin 4, dB2 p2 p4 y3 = true →
    ∀ y4 : Fin 4, dB2 p3 p5 y4 = true →
    ∀ y5 : Fin 4, dB1 p4 y5 = true →
    Tp tabc6 (some ![p1, p2, p3, p4, p5]) ![y1, y2, y3, y4, y5] c.val =
      2 * tabc6 (some ![p1, p2, p3, p4, p5]) ![y1, y2, y3, y4, y5] c.val + 2 * tabc4 (some ![p1, p2, p3, p4, p5]) ![y1, y2, y3, y4, y5] c.val + tabc3 (some ![p1, p2, p3, p4, p5]) ![y1, y2, y3, y4, y5] c.val) ∧
    (∑ x : Fin 4, ∑ y : Fin 4, ∑ z : Fin 4, ∑ u : Fin 4, ∑ v : Fin 4, W0f none ![x, y, z, u, v] 0 = 19) ∧
    (∑ x : Fin 4, ∑ y : Fin 4, ∑ z : Fin 4, ∑ u : Fin 4, ∑ v : Fin 4, tabc1 none ![x, y, z, u, v] 0 = 384) ∧
    (∑ x : Fin 4, ∑ y : Fin 4, ∑ z : Fin 4, ∑ u : Fin 4, ∑ v : Fin 4, tabc2 none ![x, y, z, u, v] 0 = 648) ∧
    (∑ x : Fin 4, ∑ y : Fin 4, ∑ z : Fin 4, ∑ u : Fin 4, ∑ v : Fin 4, tabc3 none ![x, y, z, u, v] 0 = 1536) ∧
    (∑ x : Fin 4, ∑ y : Fin 4, ∑ z : Fin 4, ∑ u : Fin 4, ∑ v : Fin 4, tabc4 none ![x, y, z, u, v] 0 = 4032) ∧
    (∑ x : Fin 4, ∑ y : Fin 4, ∑ z : Fin 4, ∑ u : Fin 4, ∑ v : Fin 4, tabc5 none ![x, y, z, u, v] 0 = 9600) ∧
    (∑ x : Fin 4, ∑ y : Fin 4, ∑ z : Fin 4, ∑ u : Fin 4, ∑ v : Fin 4, tabc6 none ![x, y, z, u, v] 0 = 22848) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c p1
    fin_cases c <;> fin_cases p1 <;> decide +kernel
  · decide +kernel
  · intro c y1
    fin_cases c <;> fin_cases y1 <;> decide +kernel
  · decide +kernel
  · intro c y1
    fin_cases c <;> fin_cases y1 <;> decide +kernel
  · decide +kernel
  · intro c y1
    fin_cases c <;> fin_cases y1 <;> decide +kernel
  · decide +kernel
  · intro c y1
    fin_cases c <;> fin_cases y1 <;> decide +kernel
  · decide +kernel
  · intro c y1
    fin_cases c <;> fin_cases y1 <;> decide +kernel
  · decide +kernel
  · intro c y1
    fin_cases c <;> fin_cases y1 <;> decide +kernel
  · decide +kernel
  · intro c y1
    fin_cases c <;> fin_cases y1 <;> decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

/-- The renamed row above stays below c and introduces its values in order (it is a restricted
growth string, so it is renamed to itself). -/
lemma canon_idemP : ∀ c : Fin 5, ∀ p1 : Fin 4, p1.val < c.val → ∀ p2 : Fin 4, p2.val < c.val → ∀ p3 : Fin 4, p3.val < c.val → ∀ p4 : Fin 4, p4.val < c.val → ∀ p5 : Fin 4, p5.val < c.val →
    (∀ j, ((renP c.val ![p1, p2, p3, p4, p5] ![p1, p2, p3, p4, p5]).1 j).val < c.val) ∧
      ((renP c.val ![p1, p2, p3, p4, p5] ![p1, p2, p3, p4, p5]).1 0).val = 0 ∧ ((renP c.val ![p1, p2, p3, p4, p5] ![p1, p2, p3, p4, p5]).1 1).val ≤ ((renP c.val ![p1, p2, p3, p4, p5] ![p1, p2, p3, p4, p5]).1 0).val + 1 ∧ ((renP c.val ![p1, p2, p3, p4, p5] ![p1, p2, p3, p4, p5]).1 2).val ≤ max ((renP c.val ![p1, p2, p3, p4, p5] ![p1, p2, p3, p4, p5]).1 0).val ((renP c.val ![p1, p2, p3, p4, p5] ![p1, p2, p3, p4, p5]).1 1).val + 1 ∧ ((renP c.val ![p1, p2, p3, p4, p5] ![p1, p2, p3, p4, p5]).1 3).val ≤ max (max ((renP c.val ![p1, p2, p3, p4, p5] ![p1, p2, p3, p4, p5]).1 0).val ((renP c.val ![p1, p2, p3, p4, p5] ![p1, p2, p3, p4, p5]).1 1).val) ((renP c.val ![p1, p2, p3, p4, p5] ![p1, p2, p3, p4, p5]).1 2).val + 1 ∧ ((renP c.val ![p1, p2, p3, p4, p5] ![p1, p2, p3, p4, p5]).1 4).val ≤ max (max (max ((renP c.val ![p1, p2, p3, p4, p5] ![p1, p2, p3, p4, p5]).1 0).val ((renP c.val ![p1, p2, p3, p4, p5] ![p1, p2, p3, p4, p5]).1 1).val) ((renP c.val ![p1, p2, p3, p4, p5] ![p1, p2, p3, p4, p5]).1 2).val) ((renP c.val ![p1, p2, p3, p4, p5] ![p1, p2, p3, p4, p5]).1 3).val + 1 := checks_all.1

lemma checkN1 : ∀ y1 y2 y3 y4 y5 : Fin 4,
    Tp W0f none ![y1, y2, y3, y4, y5] 0 = tab1 none ![y1, y2, y3, y4, y5] 0 := checks_all.2.1

lemma checkS1 : ∀ c : Fin 5, ∀ y1 : Fin 4,
    ∀ p1 : Fin 4, p1.val < c.val → p1.val = 0 →
    ∀ p2 : Fin 4, p2.val < c.val → p2.val ≤ p1.val + 1 →
    ∀ p3 : Fin 4, p3.val < c.val → p3.val ≤ max p1.val p2.val + 1 →
    ∀ p4 : Fin 4, p4.val < c.val → p4.val ≤ max (max p1.val p2.val) p3.val + 1 →
    ∀ p5 : Fin 4, p5.val < c.val → p5.val ≤ max (max (max p1.val p2.val) p3.val) p4.val + 1 →
    rowNe p1 p2 p3 p4 p5 = true → dB1 p2 y1 = true →
    ∀ y2 : Fin 4, dB2 p1 p3 y2 = true →
    ∀ y3 : Fin 4, dB2 p2 p4 y3 = true →
    ∀ y4 : Fin 4, dB2 p3 p5 y4 = true →
    ∀ y5 : Fin 4, dB1 p4 y5 = true →
    Tp W0f (some ![p1, p2, p3, p4, p5]) ![y1, y2, y3, y4, y5] c.val = tab1 (some ![p1, p2, p3, p4, p5]) ![y1, y2, y3, y4, y5] c.val := checks_all.2.2.1

lemma checkN2 : ∀ y1 y2 y3 y4 y5 : Fin 4,
    Tp tabc1 none ![y1, y2, y3, y4, y5] 0 = tab2 none ![y1, y2, y3, y4, y5] 0 := checks_all.2.2.2.1

lemma checkS2 : ∀ c : Fin 5, ∀ y1 : Fin 4,
    ∀ p1 : Fin 4, p1.val < c.val → p1.val = 0 →
    ∀ p2 : Fin 4, p2.val < c.val → p2.val ≤ p1.val + 1 →
    ∀ p3 : Fin 4, p3.val < c.val → p3.val ≤ max p1.val p2.val + 1 →
    ∀ p4 : Fin 4, p4.val < c.val → p4.val ≤ max (max p1.val p2.val) p3.val + 1 →
    ∀ p5 : Fin 4, p5.val < c.val → p5.val ≤ max (max (max p1.val p2.val) p3.val) p4.val + 1 →
    rowNe p1 p2 p3 p4 p5 = true → dB1 p2 y1 = true →
    ∀ y2 : Fin 4, dB2 p1 p3 y2 = true →
    ∀ y3 : Fin 4, dB2 p2 p4 y3 = true →
    ∀ y4 : Fin 4, dB2 p3 p5 y4 = true →
    ∀ y5 : Fin 4, dB1 p4 y5 = true →
    Tp tabc1 (some ![p1, p2, p3, p4, p5]) ![y1, y2, y3, y4, y5] c.val = tab2 (some ![p1, p2, p3, p4, p5]) ![y1, y2, y3, y4, y5] c.val := checks_all.2.2.2.2.1

lemma checkN3 : ∀ y1 y2 y3 y4 y5 : Fin 4,
    Tp tabc2 none ![y1, y2, y3, y4, y5] 0 = tab3 none ![y1, y2, y3, y4, y5] 0 := checks_all.2.2.2.2.2.1

lemma checkS3 : ∀ c : Fin 5, ∀ y1 : Fin 4,
    ∀ p1 : Fin 4, p1.val < c.val → p1.val = 0 →
    ∀ p2 : Fin 4, p2.val < c.val → p2.val ≤ p1.val + 1 →
    ∀ p3 : Fin 4, p3.val < c.val → p3.val ≤ max p1.val p2.val + 1 →
    ∀ p4 : Fin 4, p4.val < c.val → p4.val ≤ max (max p1.val p2.val) p3.val + 1 →
    ∀ p5 : Fin 4, p5.val < c.val → p5.val ≤ max (max (max p1.val p2.val) p3.val) p4.val + 1 →
    rowNe p1 p2 p3 p4 p5 = true → dB1 p2 y1 = true →
    ∀ y2 : Fin 4, dB2 p1 p3 y2 = true →
    ∀ y3 : Fin 4, dB2 p2 p4 y3 = true →
    ∀ y4 : Fin 4, dB2 p3 p5 y4 = true →
    ∀ y5 : Fin 4, dB1 p4 y5 = true →
    Tp tabc2 (some ![p1, p2, p3, p4, p5]) ![y1, y2, y3, y4, y5] c.val = tab3 (some ![p1, p2, p3, p4, p5]) ![y1, y2, y3, y4, y5] c.val := checks_all.2.2.2.2.2.2.1

lemma checkN4 : ∀ y1 y2 y3 y4 y5 : Fin 4,
    Tp tabc3 none ![y1, y2, y3, y4, y5] 0 = tab4 none ![y1, y2, y3, y4, y5] 0 := checks_all.2.2.2.2.2.2.2.1

lemma checkS4 : ∀ c : Fin 5, ∀ y1 : Fin 4,
    ∀ p1 : Fin 4, p1.val < c.val → p1.val = 0 →
    ∀ p2 : Fin 4, p2.val < c.val → p2.val ≤ p1.val + 1 →
    ∀ p3 : Fin 4, p3.val < c.val → p3.val ≤ max p1.val p2.val + 1 →
    ∀ p4 : Fin 4, p4.val < c.val → p4.val ≤ max (max p1.val p2.val) p3.val + 1 →
    ∀ p5 : Fin 4, p5.val < c.val → p5.val ≤ max (max (max p1.val p2.val) p3.val) p4.val + 1 →
    rowNe p1 p2 p3 p4 p5 = true → dB1 p2 y1 = true →
    ∀ y2 : Fin 4, dB2 p1 p3 y2 = true →
    ∀ y3 : Fin 4, dB2 p2 p4 y3 = true →
    ∀ y4 : Fin 4, dB2 p3 p5 y4 = true →
    ∀ y5 : Fin 4, dB1 p4 y5 = true →
    Tp tabc3 (some ![p1, p2, p3, p4, p5]) ![y1, y2, y3, y4, y5] c.val = tab4 (some ![p1, p2, p3, p4, p5]) ![y1, y2, y3, y4, y5] c.val := checks_all.2.2.2.2.2.2.2.2.1

lemma checkN5 : ∀ y1 y2 y3 y4 y5 : Fin 4,
    Tp tabc4 none ![y1, y2, y3, y4, y5] 0 = tab5 none ![y1, y2, y3, y4, y5] 0 := checks_all.2.2.2.2.2.2.2.2.2.1

lemma checkS5 : ∀ c : Fin 5, ∀ y1 : Fin 4,
    ∀ p1 : Fin 4, p1.val < c.val → p1.val = 0 →
    ∀ p2 : Fin 4, p2.val < c.val → p2.val ≤ p1.val + 1 →
    ∀ p3 : Fin 4, p3.val < c.val → p3.val ≤ max p1.val p2.val + 1 →
    ∀ p4 : Fin 4, p4.val < c.val → p4.val ≤ max (max p1.val p2.val) p3.val + 1 →
    ∀ p5 : Fin 4, p5.val < c.val → p5.val ≤ max (max (max p1.val p2.val) p3.val) p4.val + 1 →
    rowNe p1 p2 p3 p4 p5 = true → dB1 p2 y1 = true →
    ∀ y2 : Fin 4, dB2 p1 p3 y2 = true →
    ∀ y3 : Fin 4, dB2 p2 p4 y3 = true →
    ∀ y4 : Fin 4, dB2 p3 p5 y4 = true →
    ∀ y5 : Fin 4, dB1 p4 y5 = true →
    Tp tabc4 (some ![p1, p2, p3, p4, p5]) ![y1, y2, y3, y4, y5] c.val = tab5 (some ![p1, p2, p3, p4, p5]) ![y1, y2, y3, y4, y5] c.val := checks_all.2.2.2.2.2.2.2.2.2.2.1

lemma checkN6 : ∀ y1 y2 y3 y4 y5 : Fin 4,
    Tp tabc5 none ![y1, y2, y3, y4, y5] 0 = tab6 none ![y1, y2, y3, y4, y5] 0 := checks_all.2.2.2.2.2.2.2.2.2.2.2.1

lemma checkS6 : ∀ c : Fin 5, ∀ y1 : Fin 4,
    ∀ p1 : Fin 4, p1.val < c.val → p1.val = 0 →
    ∀ p2 : Fin 4, p2.val < c.val → p2.val ≤ p1.val + 1 →
    ∀ p3 : Fin 4, p3.val < c.val → p3.val ≤ max p1.val p2.val + 1 →
    ∀ p4 : Fin 4, p4.val < c.val → p4.val ≤ max (max p1.val p2.val) p3.val + 1 →
    ∀ p5 : Fin 4, p5.val < c.val → p5.val ≤ max (max (max p1.val p2.val) p3.val) p4.val + 1 →
    rowNe p1 p2 p3 p4 p5 = true → dB1 p2 y1 = true →
    ∀ y2 : Fin 4, dB2 p1 p3 y2 = true →
    ∀ y3 : Fin 4, dB2 p2 p4 y3 = true →
    ∀ y4 : Fin 4, dB2 p3 p5 y4 = true →
    ∀ y5 : Fin 4, dB1 p4 y5 = true →
    Tp tabc5 (some ![p1, p2, p3, p4, p5]) ![y1, y2, y3, y4, y5] c.val = tab6 (some ![p1, p2, p3, p4, p5]) ![y1, y2, y3, y4, y5] c.val := checks_all.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma checkN_rel : ∀ y1 y2 y3 y4 y5 : Fin 4,
    Tp tabc6 none ![y1, y2, y3, y4, y5] 0 =
      2 * tabc6 none ![y1, y2, y3, y4, y5] 0 + 2 * tabc4 none ![y1, y2, y3, y4, y5] 0 + tabc3 none ![y1, y2, y3, y4, y5] 0 := checks_all.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma checkS_rel : ∀ c : Fin 5, ∀ y1 : Fin 4,
    ∀ p1 : Fin 4, p1.val < c.val → p1.val = 0 →
    ∀ p2 : Fin 4, p2.val < c.val → p2.val ≤ p1.val + 1 →
    ∀ p3 : Fin 4, p3.val < c.val → p3.val ≤ max p1.val p2.val + 1 →
    ∀ p4 : Fin 4, p4.val < c.val → p4.val ≤ max (max p1.val p2.val) p3.val + 1 →
    ∀ p5 : Fin 4, p5.val < c.val → p5.val ≤ max (max (max p1.val p2.val) p3.val) p4.val + 1 →
    rowNe p1 p2 p3 p4 p5 = true → dB1 p2 y1 = true →
    ∀ y2 : Fin 4, dB2 p1 p3 y2 = true →
    ∀ y3 : Fin 4, dB2 p2 p4 y3 = true →
    ∀ y4 : Fin 4, dB2 p3 p5 y4 = true →
    ∀ y5 : Fin 4, dB1 p4 y5 = true →
    Tp tabc6 (some ![p1, p2, p3, p4, p5]) ![y1, y2, y3, y4, y5] c.val =
      2 * tabc6 (some ![p1, p2, p3, p4, p5]) ![y1, y2, y3, y4, y5] c.val + 2 * tabc4 (some ![p1, p2, p3, p4, p5]) ![y1, y2, y3, y4, y5] c.val + tabc3 (some ![p1, p2, p3, p4, p5]) ![y1, y2, y3, y4, y5] c.val := checks_all.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma sum1 : ∑ x : Fin 4, ∑ y : Fin 4, ∑ z : Fin 4, ∑ u : Fin 4, ∑ v : Fin 4, W0f none ![x, y, z, u, v] 0 = 19 := checks_all.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma sum2 : ∑ x : Fin 4, ∑ y : Fin 4, ∑ z : Fin 4, ∑ u : Fin 4, ∑ v : Fin 4, tabc1 none ![x, y, z, u, v] 0 = 384 := checks_all.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma sum3 : ∑ x : Fin 4, ∑ y : Fin 4, ∑ z : Fin 4, ∑ u : Fin 4, ∑ v : Fin 4, tabc2 none ![x, y, z, u, v] 0 = 648 := checks_all.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma sum4 : ∑ x : Fin 4, ∑ y : Fin 4, ∑ z : Fin 4, ∑ u : Fin 4, ∑ v : Fin 4, tabc3 none ![x, y, z, u, v] 0 = 1536 := checks_all.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma sum5 : ∑ x : Fin 4, ∑ y : Fin 4, ∑ z : Fin 4, ∑ u : Fin 4, ∑ v : Fin 4, tabc4 none ![x, y, z, u, v] 0 = 4032 := checks_all.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma sum6 : ∑ x : Fin 4, ∑ y : Fin 4, ∑ z : Fin 4, ∑ u : Fin 4, ∑ v : Fin 4, tabc5 none ![x, y, z, u, v] 0 = 9600 := checks_all.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma sum7 : ∑ x : Fin 4, ∑ y : Fin 4, ∑ z : Fin 4, ∑ u : Fin 4, ∑ v : Fin 4, tabc6 none ![x, y, z, u, v] 0 = 22848 := checks_all.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

lemma canon_idemP' (c : ℕ) (hc : c ≤ 4) (p r : Fin 5 → Fin 4) (hp : ∀ j, (p j).val < c) :
    (∀ j, ((renP c p r).1 j).val < c) ∧ ((renP c p r).1 0).val = 0 ∧ ((renP c p r).1 1).val ≤ ((renP c p r).1 0).val + 1 ∧ ((renP c p r).1 2).val ≤ max ((renP c p r).1 0).val ((renP c p r).1 1).val + 1 ∧ ((renP c p r).1 3).val ≤ max (max ((renP c p r).1 0).val ((renP c p r).1 1).val) ((renP c p r).1 2).val + 1 ∧ ((renP c p r).1 4).val ≤ max (max (max ((renP c p r).1 0).val ((renP c p r).1 1).val) ((renP c p r).1 2).val) ((renP c p r).1 3).val + 1 := by
  have h := canon_idemP ⟨c, by omega⟩ (p 0) (hp 0) (p 1) (hp 1) (p 2) (hp 2) (p 3) (hp 3) (p 4) (hp 4)
  rw [← row_eta p] at h
  exact h

lemma W_1 (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (c : ℕ) (hc : c ≤ 4)
    (hq : ∀ p, q = some p → (∀ j, (p j).val < c) ∧ belowB p r = true) (hn : q = none → c = 0) :
    W 1 q r c = tabc1 q r c := by
  rcases q with _ | p
  · rw [W_succT _ none r c,
      T_congr _ W0f none r c (fun s _ => W_zero' _ s _)]
    rw [T_eq_Tp, row_eta r]
    rw [hn rfl]
    exact checkN1 (r 0) (r 1) (r 2) (r 3) (r 4)
  · have hp := hq p rfl
    obtain ⟨hlt, h0, h1, h2, h3, h4⟩ := canon_idemP' c hc p r hp.1
    have hb : belowB (renP c p r).1 (renP c p r).2 = true := (ren_reach c p r).trans hp.2
    rw [← W_renP 1 c p r]
    show W 1 (some (renP c p r).1) (renP c p r).2 c = tab1 (some (renP c p r).1) (renP c p r).2 c
    generalize renP c p r = x at hlt h0 h1 h2 h3 h4 hb ⊢
    rw [W_succT _ (some x.1) x.2 c,
      T_congr _ W0f (some x.1) x.2 c (fun s _ => W_zero' _ s _)]
    simp only [belowB, Bool.and_eq_true] at hb
    rw [T_eq_Tp, row_eta x.1, row_eta x.2]
    exact checkS1 ⟨c, by omega⟩ (x.2 0) (x.1 0) (hlt 0) h0 (x.1 1) (hlt 1) h1 (x.1 2) (hlt 2) h2 (x.1 3) (hlt 3) h3 (x.1 4) (hlt 4) h4 hb.1.1.1.1.1 hb.1.1.1.1.2 (x.2 1) hb.1.1.1.2 (x.2 2) hb.1.1.2 (x.2 3) hb.1.2 (x.2 4) hb.2

lemma W_2 (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (c : ℕ) (hc : c ≤ 4)
    (hq : ∀ p, q = some p → (∀ j, (p j).val < c) ∧ belowB p r = true) (hn : q = none → c = 0) :
    W 2 q r c = tabc2 q r c := by
  rcases q with _ | p
  · rw [show W 2 none r c = W (1 + 1) none r c from rfl, W_succT _ none r c,
      T_congr _ tabc1 none r c
        (fun s hs => W_1 _ s _ (newcB_le c hc r) (inv_next c none r s hs) (fun h => by cases h))]
    rw [T_eq_Tp, row_eta r]
    rw [hn rfl]
    exact checkN2 (r 0) (r 1) (r 2) (r 3) (r 4)
  · have hp := hq p rfl
    obtain ⟨hlt, h0, h1, h2, h3, h4⟩ := canon_idemP' c hc p r hp.1
    have hb : belowB (renP c p r).1 (renP c p r).2 = true := (ren_reach c p r).trans hp.2
    rw [← W_renP 2 c p r]
    show W 2 (some (renP c p r).1) (renP c p r).2 c = tab2 (some (renP c p r).1) (renP c p r).2 c
    generalize renP c p r = x at hlt h0 h1 h2 h3 h4 hb ⊢
    rw [show W 2 (some x.1) x.2 c = W (1 + 1) (some x.1) x.2 c from rfl, W_succT _ (some x.1) x.2 c,
      T_congr _ tabc1 (some x.1) x.2 c
        (fun s hs => W_1 _ s _ (newcB_le c hc x.2) (inv_next c (some x.1) x.2 s hs) (fun h => by cases h))]
    simp only [belowB, Bool.and_eq_true] at hb
    rw [T_eq_Tp, row_eta x.1, row_eta x.2]
    exact checkS2 ⟨c, by omega⟩ (x.2 0) (x.1 0) (hlt 0) h0 (x.1 1) (hlt 1) h1 (x.1 2) (hlt 2) h2 (x.1 3) (hlt 3) h3 (x.1 4) (hlt 4) h4 hb.1.1.1.1.1 hb.1.1.1.1.2 (x.2 1) hb.1.1.1.2 (x.2 2) hb.1.1.2 (x.2 3) hb.1.2 (x.2 4) hb.2

lemma W_3 (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (c : ℕ) (hc : c ≤ 4)
    (hq : ∀ p, q = some p → (∀ j, (p j).val < c) ∧ belowB p r = true) (hn : q = none → c = 0) :
    W 3 q r c = tabc3 q r c := by
  rcases q with _ | p
  · rw [show W 3 none r c = W (2 + 1) none r c from rfl, W_succT _ none r c,
      T_congr _ tabc2 none r c
        (fun s hs => W_2 _ s _ (newcB_le c hc r) (inv_next c none r s hs) (fun h => by cases h))]
    rw [T_eq_Tp, row_eta r]
    rw [hn rfl]
    exact checkN3 (r 0) (r 1) (r 2) (r 3) (r 4)
  · have hp := hq p rfl
    obtain ⟨hlt, h0, h1, h2, h3, h4⟩ := canon_idemP' c hc p r hp.1
    have hb : belowB (renP c p r).1 (renP c p r).2 = true := (ren_reach c p r).trans hp.2
    rw [← W_renP 3 c p r]
    show W 3 (some (renP c p r).1) (renP c p r).2 c = tab3 (some (renP c p r).1) (renP c p r).2 c
    generalize renP c p r = x at hlt h0 h1 h2 h3 h4 hb ⊢
    rw [show W 3 (some x.1) x.2 c = W (2 + 1) (some x.1) x.2 c from rfl, W_succT _ (some x.1) x.2 c,
      T_congr _ tabc2 (some x.1) x.2 c
        (fun s hs => W_2 _ s _ (newcB_le c hc x.2) (inv_next c (some x.1) x.2 s hs) (fun h => by cases h))]
    simp only [belowB, Bool.and_eq_true] at hb
    rw [T_eq_Tp, row_eta x.1, row_eta x.2]
    exact checkS3 ⟨c, by omega⟩ (x.2 0) (x.1 0) (hlt 0) h0 (x.1 1) (hlt 1) h1 (x.1 2) (hlt 2) h2 (x.1 3) (hlt 3) h3 (x.1 4) (hlt 4) h4 hb.1.1.1.1.1 hb.1.1.1.1.2 (x.2 1) hb.1.1.1.2 (x.2 2) hb.1.1.2 (x.2 3) hb.1.2 (x.2 4) hb.2

lemma W_4 (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (c : ℕ) (hc : c ≤ 4)
    (hq : ∀ p, q = some p → (∀ j, (p j).val < c) ∧ belowB p r = true) (hn : q = none → c = 0) :
    W 4 q r c = tabc4 q r c := by
  rcases q with _ | p
  · rw [show W 4 none r c = W (3 + 1) none r c from rfl, W_succT _ none r c,
      T_congr _ tabc3 none r c
        (fun s hs => W_3 _ s _ (newcB_le c hc r) (inv_next c none r s hs) (fun h => by cases h))]
    rw [T_eq_Tp, row_eta r]
    rw [hn rfl]
    exact checkN4 (r 0) (r 1) (r 2) (r 3) (r 4)
  · have hp := hq p rfl
    obtain ⟨hlt, h0, h1, h2, h3, h4⟩ := canon_idemP' c hc p r hp.1
    have hb : belowB (renP c p r).1 (renP c p r).2 = true := (ren_reach c p r).trans hp.2
    rw [← W_renP 4 c p r]
    show W 4 (some (renP c p r).1) (renP c p r).2 c = tab4 (some (renP c p r).1) (renP c p r).2 c
    generalize renP c p r = x at hlt h0 h1 h2 h3 h4 hb ⊢
    rw [show W 4 (some x.1) x.2 c = W (3 + 1) (some x.1) x.2 c from rfl, W_succT _ (some x.1) x.2 c,
      T_congr _ tabc3 (some x.1) x.2 c
        (fun s hs => W_3 _ s _ (newcB_le c hc x.2) (inv_next c (some x.1) x.2 s hs) (fun h => by cases h))]
    simp only [belowB, Bool.and_eq_true] at hb
    rw [T_eq_Tp, row_eta x.1, row_eta x.2]
    exact checkS4 ⟨c, by omega⟩ (x.2 0) (x.1 0) (hlt 0) h0 (x.1 1) (hlt 1) h1 (x.1 2) (hlt 2) h2 (x.1 3) (hlt 3) h3 (x.1 4) (hlt 4) h4 hb.1.1.1.1.1 hb.1.1.1.1.2 (x.2 1) hb.1.1.1.2 (x.2 2) hb.1.1.2 (x.2 3) hb.1.2 (x.2 4) hb.2

lemma W_5 (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (c : ℕ) (hc : c ≤ 4)
    (hq : ∀ p, q = some p → (∀ j, (p j).val < c) ∧ belowB p r = true) (hn : q = none → c = 0) :
    W 5 q r c = tabc5 q r c := by
  rcases q with _ | p
  · rw [show W 5 none r c = W (4 + 1) none r c from rfl, W_succT _ none r c,
      T_congr _ tabc4 none r c
        (fun s hs => W_4 _ s _ (newcB_le c hc r) (inv_next c none r s hs) (fun h => by cases h))]
    rw [T_eq_Tp, row_eta r]
    rw [hn rfl]
    exact checkN5 (r 0) (r 1) (r 2) (r 3) (r 4)
  · have hp := hq p rfl
    obtain ⟨hlt, h0, h1, h2, h3, h4⟩ := canon_idemP' c hc p r hp.1
    have hb : belowB (renP c p r).1 (renP c p r).2 = true := (ren_reach c p r).trans hp.2
    rw [← W_renP 5 c p r]
    show W 5 (some (renP c p r).1) (renP c p r).2 c = tab5 (some (renP c p r).1) (renP c p r).2 c
    generalize renP c p r = x at hlt h0 h1 h2 h3 h4 hb ⊢
    rw [show W 5 (some x.1) x.2 c = W (4 + 1) (some x.1) x.2 c from rfl, W_succT _ (some x.1) x.2 c,
      T_congr _ tabc4 (some x.1) x.2 c
        (fun s hs => W_4 _ s _ (newcB_le c hc x.2) (inv_next c (some x.1) x.2 s hs) (fun h => by cases h))]
    simp only [belowB, Bool.and_eq_true] at hb
    rw [T_eq_Tp, row_eta x.1, row_eta x.2]
    exact checkS5 ⟨c, by omega⟩ (x.2 0) (x.1 0) (hlt 0) h0 (x.1 1) (hlt 1) h1 (x.1 2) (hlt 2) h2 (x.1 3) (hlt 3) h3 (x.1 4) (hlt 4) h4 hb.1.1.1.1.1 hb.1.1.1.1.2 (x.2 1) hb.1.1.1.2 (x.2 2) hb.1.1.2 (x.2 3) hb.1.2 (x.2 4) hb.2

lemma W_6 (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (c : ℕ) (hc : c ≤ 4)
    (hq : ∀ p, q = some p → (∀ j, (p j).val < c) ∧ belowB p r = true) (hn : q = none → c = 0) :
    W 6 q r c = tabc6 q r c := by
  rcases q with _ | p
  · rw [show W 6 none r c = W (5 + 1) none r c from rfl, W_succT _ none r c,
      T_congr _ tabc5 none r c
        (fun s hs => W_5 _ s _ (newcB_le c hc r) (inv_next c none r s hs) (fun h => by cases h))]
    rw [T_eq_Tp, row_eta r]
    rw [hn rfl]
    exact checkN6 (r 0) (r 1) (r 2) (r 3) (r 4)
  · have hp := hq p rfl
    obtain ⟨hlt, h0, h1, h2, h3, h4⟩ := canon_idemP' c hc p r hp.1
    have hb : belowB (renP c p r).1 (renP c p r).2 = true := (ren_reach c p r).trans hp.2
    rw [← W_renP 6 c p r]
    show W 6 (some (renP c p r).1) (renP c p r).2 c = tab6 (some (renP c p r).1) (renP c p r).2 c
    generalize renP c p r = x at hlt h0 h1 h2 h3 h4 hb ⊢
    rw [show W 6 (some x.1) x.2 c = W (5 + 1) (some x.1) x.2 c from rfl, W_succT _ (some x.1) x.2 c,
      T_congr _ tabc5 (some x.1) x.2 c
        (fun s hs => W_5 _ s _ (newcB_le c hc x.2) (inv_next c (some x.1) x.2 s hs) (fun h => by cases h))]
    simp only [belowB, Bool.and_eq_true] at hb
    rw [T_eq_Tp, row_eta x.1, row_eta x.2]
    exact checkS6 ⟨c, by omega⟩ (x.2 0) (x.1 0) (hlt 0) h0 (x.1 1) (hlt 1) h1 (x.1 2) (hlt 2) h2 (x.1 3) (hlt 3) h3 (x.1 4) (hlt 4) h4 hb.1.1.1.1.1 hb.1.1.1.1.2 (x.2 1) hb.1.1.1.2 (x.2 2) hb.1.1.2 (x.2 3) hb.1.2 (x.2 4) hb.2

lemma W_rec (n : ℕ) : ∀ (q : Option (Fin 5 → Fin 4)) (r : Fin 5 → Fin 4) (c : ℕ), c ≤ 4 →
    (∀ p, q = some p → (∀ j, (p j).val < c) ∧ belowB p r = true) →
    (q = none → c = 0) →
    W (n + 7) q r c = 2 * W (n + 6) q r c + 2 * W (n + 4) q r c + W (n + 3) q r c := by
  induction n with
  | zero =>
    intro q r c hc hq hn
    rcases q with _ | p
    · rw [show W (0 + 7) none r c = W (6 + 1) none r c from rfl, W_succT 6 none r c,
        T_congr _ tabc6 none r c
          (fun s hs => W_6 _ s _ (newcB_le c hc r) (inv_next c none r s hs) (fun h => by cases h)),
        show W (0 + 3) none r c = W 3 none r c from rfl, W_3 none r c hc hq hn,
        show W (0 + 4) none r c = W 4 none r c from rfl, W_4 none r c hc hq hn,
        show W (0 + 6) none r c = W 6 none r c from rfl, W_6 none r c hc hq hn]
      rw [T_eq_Tp, row_eta r]
      rw [hn rfl]
      exact checkN_rel (r 0) (r 1) (r 2) (r 3) (r 4)
    · have hp := hq p rfl
      obtain ⟨hlt, h0, h1, h2, h3, h4⟩ := canon_idemP' c hc p r hp.1
      have hb : belowB (renP c p r).1 (renP c p r).2 = true := (ren_reach c p r).trans hp.2
      rw [show W (0 + 7) (some p) r c = W 7 (some p) r c from rfl, show W (0 + 6) (some p) r c = W 6 (some p) r c from rfl, show W (0 + 4) (some p) r c = W 4 (some p) r c from rfl, show W (0 + 3) (some p) r c = W 3 (some p) r c from rfl]
      rw [← W_renP 7 c p r, ← W_renP 6 c p r, ← W_renP 4 c p r, ← W_renP 3 c p r]
      generalize renP c p r = x at hlt h0 h1 h2 h3 h4 hb ⊢
      have hx : ∀ p', some x.1 = some p' → (∀ j, (p' j).val < c) ∧ belowB p' x.2 = true := fun p' h => by
        rw [← Option.some.inj h]
        exact ⟨hlt, hb⟩
      rw [show W 7 (some x.1) x.2 c = W (6 + 1) (some x.1) x.2 c from rfl, W_succT 6 (some x.1) x.2 c,
        T_congr _ tabc6 (some x.1) x.2 c
          (fun s hs => W_6 _ s _ (newcB_le c hc x.2) (inv_next c (some x.1) x.2 s hs) (fun h => by cases h)),
        W_3 (some x.1) x.2 c hc hx (fun h => by cases h),
        W_4 (some x.1) x.2 c hc hx (fun h => by cases h),
        W_6 (some x.1) x.2 c hc hx (fun h => by cases h)]
      simp only [belowB, Bool.and_eq_true] at hb
      rw [T_eq_Tp, row_eta x.1, row_eta x.2]
      exact checkS_rel ⟨c, by omega⟩ (x.2 0) (x.1 0) (hlt 0) h0 (x.1 1) (hlt 1) h1 (x.1 2) (hlt 2) h2 (x.1 3) (hlt 3) h3 (x.1 4) (hlt 4) h4 hb.1.1.1.1.1 hb.1.1.1.1.2 (x.2 1) hb.1.1.1.2 (x.2 2) hb.1.1.2 (x.2 3) hb.1.2 (x.2 4) hb.2
  | succ n ih =>
    intro q r c hc hq hn
    rw [W_succT (n + 7) q r c, W_succT (n + 6) q r c, W_succT (n + 4) q r c, W_succT (n + 3) q r c]
    unfold T
    by_cases h : rgsB c r = true
    · rw [if_pos h, if_pos h, if_pos h, if_pos h]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      split_ifs with hs
      · exact ih _ _ _ (newcB_le c hc r) (inv_next c q r _ hs) (fun h => by cases h)
      · simp
    · rw [if_neg h, if_neg h, if_neg h, if_neg h] <;> simp

lemma a_eq (n : ℕ) : a (n + 1) = ∑ r : Fin 5 → Fin 4, W (n) none r 0 := by
  unfold a W
  rw [Finset.card_eq_sum_card_fiberwise (f := fun f => f 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Finset.filter_filter]
  refine congrArg Finset.card (Finset.filter_congr (fun f _ => ?_))
  rw [cond_iff, rmn_iff, and_assoc]

lemma a_rec (n : ℕ) : a (n + 8) = 2 * a (n + 7) + 2 * a (n + 5) + a (n + 4) := by
  rw [a_eq, a_eq, a_eq, a_eq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  exact W_rec n none r 0 (by norm_num) (fun _ h => by cases h) (fun _ => rfl)

lemma a_one : a 1 = 19 := by
  have h : ∀ r, W 0 none r 0 = W0f none r 0 := fun r => W_zero' none r 0
  rw [a_eq 0, sum_row]
  simp only [h]
  exact sum1

lemma a_two : a 2 = 384 := by
  have h : ∀ r, W 1 none r 0 = tabc1 none r 0 := fun r => W_1 none r 0 (by norm_num) (fun _ h => by cases h) (fun _ => rfl)
  rw [a_eq 1, sum_row]
  simp only [h]
  exact sum2

lemma a_three : a 3 = 648 := by
  have h : ∀ r, W 2 none r 0 = tabc2 none r 0 := fun r => W_2 none r 0 (by norm_num) (fun _ h => by cases h) (fun _ => rfl)
  rw [a_eq 2, sum_row]
  simp only [h]
  exact sum3

lemma a_four : a 4 = 1536 := by
  have h : ∀ r, W 3 none r 0 = tabc3 none r 0 := fun r => W_3 none r 0 (by norm_num) (fun _ h => by cases h) (fun _ => rfl)
  rw [a_eq 3, sum_row]
  simp only [h]
  exact sum4

lemma a_five : a 5 = 4032 := by
  have h : ∀ r, W 4 none r 0 = tabc4 none r 0 := fun r => W_4 none r 0 (by norm_num) (fun _ h => by cases h) (fun _ => rfl)
  rw [a_eq 4, sum_row]
  simp only [h]
  exact sum5

lemma a_six : a 6 = 9600 := by
  have h : ∀ r, W 5 none r 0 = tabc5 none r 0 := fun r => W_5 none r 0 (by norm_num) (fun _ h => by cases h) (fun _ => rfl)
  rw [a_eq 5, sum_row]
  simp only [h]
  exact sum6

lemma a_seven : a 7 = 22848 := by
  have h : ∀ r, W 6 none r 0 = tabc6 none r 0 := fun r => W_6 none r 0 (by norm_num) (fun _ h => by cases h) (fun _ => rfl)
  rw [a_eq 6, sum_row]
  simp only [h]
  exact sum7

/-- Barker's g.f.: Sum_{n >= 1} a(n) x^n = x(19 + 346x - 120x^2 + 202x^3 + 173x^4 - 144x^5 - 72x^6) / ((1 + x^2)(1 - 2x - x^2)). -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 + X ^ 2) * (1 - 2 * X - X ^ 2)) = X * (19 + 346 * X - 120 * X ^ 2 + 202 * X ^ 3 + 173 * X ^ 4 - 144 * X ^ 5 - 72 * X ^ 6) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 + X ^ 2) * (1 - 2 * X - X ^ 2)) = A - A * X ^ 1 * C 2 - A * X ^ 3 * C 2 - A * X ^ 4 * C 1 := by
    rw [show (C (1 : ℚ) : ℚ⟦X⟧) = 1 from map_one C,
      show (C (2 : ℚ) : ℚ⟦X⟧) = 2 from map_ofNat C 2]
    ring
  have e2 : (X * (19 + 346 * X - 120 * X ^ 2 + 202 * X ^ 3 + 173 * X ^ 4 - 144 * X ^ 5 - 72 * X ^ 6) : ℚ⟦X⟧) = X ^ 1 * C 19 + X ^ 2 * C 346 - X ^ 3 * C 120 + X ^ 4 * C 202 + X ^ 5 * C 173 - X ^ 6 * C 144 - X ^ 7 * C 72 := by
    rw [show (C (19 : ℚ) : ℚ⟦X⟧) = 19 from map_ofNat C 19,
      show (C (72 : ℚ) : ℚ⟦X⟧) = 72 from map_ofNat C 72,
      show (C (120 : ℚ) : ℚ⟦X⟧) = 120 from map_ofNat C 120,
      show (C (144 : ℚ) : ℚ⟦X⟧) = 144 from map_ofNat C 144,
      show (C (173 : ℚ) : ℚ⟦X⟧) = 173 from map_ofNat C 173,
      show (C (202 : ℚ) : ℚ⟦X⟧) = 202 from map_ofNat C 202,
      show (C (346 : ℚ) : ℚ⟦X⟧) = 346 from map_ofNat C 346]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk]
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | n
  · simp
  · simp [a_one] <;> norm_num
  · simp [a_one, a_two] <;> norm_num
  · simp [a_one, a_two, a_three] <;> norm_num
  · simp [a_one, a_two, a_three, a_four] <;> norm_num
  · simp [a_one, a_two, a_three, a_four, a_five] <;> norm_num
  · simp [a_one, a_two, a_three, a_four, a_five, a_six] <;> norm_num
  · simp [a_one, a_two, a_three, a_four, a_five, a_six, a_seven] <;> norm_num
  · have h := a_rec n
    
    have hq : (a (n + 8) : ℚ) = 2 * (a (n + 7) : ℚ) + 2 * (a (n + 5) : ℚ) + (a (n + 4) : ℚ) := by exact_mod_cast h
    simp only [show ¬ (n + 8 = 0) by omega,
      if_false,
      if_true,
      show 1 ≤ n + 8 by omega,
      show n + 8 - 1 = n + 7 by omega,
      show ¬ (n + 7 = 0) by omega,
      show 2 ≤ n + 8 by omega,
      show n + 8 - 2 = n + 6 by omega,
      show ¬ (n + 6 = 0) by omega,
      show 3 ≤ n + 8 by omega,
      show n + 8 - 3 = n + 5 by omega,
      show ¬ (n + 5 = 0) by omega,
      show 4 ≤ n + 8 by omega,
      show n + 8 - 4 = n + 4 by omega,
      show ¬ (n + 4 = 0) by omega,
      show ¬ (n + 8 = 1) by omega,
      show ¬ (n + 8 = 2) by omega,
      show ¬ (n + 8 = 3) by omega,
      show ¬ (n + 8 = 4) by omega,
      show ¬ (n + 8 = 5) by omega,
      show ¬ (n + 8 = 6) by omega,
      show ¬ (n + 8 = 7) by omega]
    linear_combination hq

theorem cf (b : ℕ → ℕ) (h4 : b 4 = 1536) (h5 : b 5 = 4032) (h6 : b 6 = 9600)
    (h7 : b 7 = 22848)
    (hr : ∀ n, b (n + 8) = 2 * b (n + 7) + 2 * b (n + 5) + b (n + 4)) :
    ∀ n : ℕ, 3 < n → (b n : ℂ) =
      48 * ((-1 + Complex.I) * ((-Complex.I) ^ n + Complex.I ^ (1 + n)) +
        (1 - (Real.sqrt 2 : ℂ)) ^ n + (1 + (Real.sqrt 2 : ℂ)) ^ n) := by
  have s2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have i2 : Complex.I ^ 2 = -1 := Complex.I_sq
  set s : ℂ := (Real.sqrt 2 : ℂ) with hsdef
  set V : ℕ → ℂ := fun n => (-1 + Complex.I) * ((-Complex.I) ^ n + Complex.I ^ (1 + n)) with hV
  set P : ℕ → ℂ := fun n => (1 - s) ^ n + (1 + s) ^ n with hP
  have Vrec : ∀ n, V (n + 2) = -V n := by
    intro n
    simp only [hV]
    linear_combination ((-1 + Complex.I) * ((-Complex.I) ^ n + Complex.I ^ (1 + n))) * i2
  have Prec : ∀ n, P (n + 2) = 2 * P (n + 1) + P n := by
    intro n
    simp only [hP]
    linear_combination ((1 - s) ^ n + (1 + s) ^ n) * s2
  have V0 : V 0 = -2 := by simp only [hV]; linear_combination i2
  have V1 : V 1 = 2 := by simp only [hV]; linear_combination (Complex.I - 2) * i2
  have V2 : V 2 = 2 := by rw [show V 2 = V (0 + 2) from rfl, Vrec, V0]; norm_num
  have V3 : V 3 = -2 := by rw [show V 3 = V (1 + 2) from rfl, Vrec, V1]
  have V4 : V 4 = -2 := by rw [show V 4 = V (2 + 2) from rfl, Vrec, V2]
  have V5 : V 5 = 2 := by rw [show V 5 = V (3 + 2) from rfl, Vrec, V3]; norm_num
  have V6 : V 6 = 2 := by rw [show V 6 = V (4 + 2) from rfl, Vrec, V4]; norm_num
  have V7 : V 7 = -2 := by rw [show V 7 = V (5 + 2) from rfl, Vrec, V5]
  have P0 : P 0 = 2 := by simp only [hP]; ring
  have P1 : P 1 = 2 := by simp only [hP]; ring
  have P2 : P 2 = 6 := by
    rw [show P 2 = P (0 + 2) from rfl, Prec, show P (0 + 1) = P 1 from rfl, P1, P0]; norm_num
  have P3 : P 3 = 14 := by
    rw [show P 3 = P (1 + 2) from rfl, Prec, show P (1 + 1) = P 2 from rfl, P2, P1]; norm_num
  have P4 : P 4 = 34 := by
    rw [show P 4 = P (2 + 2) from rfl, Prec, show P (2 + 1) = P 3 from rfl, P3, P2]; norm_num
  have P5 : P 5 = 82 := by
    rw [show P 5 = P (3 + 2) from rfl, Prec, show P (3 + 1) = P 4 from rfl, P4, P3]; norm_num
  have P6 : P 6 = 198 := by
    rw [show P 6 = P (4 + 2) from rfl, Prec, show P (4 + 1) = P 5 from rfl, P5, P4]; norm_num
  have P7 : P 7 = 478 := by
    rw [show P 7 = P (5 + 2) from rfl, Prec, show P (5 + 1) = P 6 from rfl, P6, P5]; norm_num
  set G : ℕ → ℂ := fun n => V n + P n with hG
  have Grec : ∀ n, G (n + 4) = 2 * G (n + 3) + 2 * G (n + 1) + G n := by
    intro n
    simp only [hG]
    have v0 := Vrec n
    have v1 := Vrec (n + 1)
    have v2 := Vrec (n + 2)
    have p0 := Prec n
    have p2 := Prec (n + 2)
    rw [show n + 1 + 2 = n + 3 from rfl] at v1
    rw [show n + 2 + 2 = n + 4 from rfl] at v2
    rw [show n + 2 + 2 = n + 4 from rfl, show n + 2 + 1 = n + 3 from rfl] at p2
    linear_combination v2 - 2 * v1 - v0 + p2 + p0
  have key : ∀ k, (b (k + 4) : ℂ) = 48 * G (k + 4) ∧ (b (k + 5) : ℂ) = 48 * G (k + 5) ∧
      (b (k + 6) : ℂ) = 48 * G (k + 6) ∧ (b (k + 7) : ℂ) = 48 * G (k + 7) := by
    intro k
    induction k with
    | zero =>
      simp only [hG, Nat.zero_add]
      rw [h4, h5, h6, h7, V4, V5, V6, V7, P4, P5, P6, P7]
      norm_num
    | succ k ih =>
      obtain ⟨i4, i5, i6, i7⟩ := ih
      refine ⟨i5, i6, i7, ?_⟩
      have hq : ((b (k + 8) : ℕ) : ℂ) = 2 * b (k + 7) + 2 * b (k + 5) + b (k + 4) := by
        exact_mod_cast hr k
      have hg := Grec (k + 4)
      rw [show k + 4 + 4 = k + 8 from rfl, show k + 4 + 3 = k + 7 from rfl,
        show k + 4 + 1 = k + 5 from rfl] at hg
      rw [show k + 1 + 7 = k + 8 from rfl]
      linear_combination hq + 2 * i7 + 2 * i5 + i4 - 48 * hg
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  rw [(key k).1]
  simp only [hG, hV, hP]
  ring

/-- Barker's closed form. -/
theorem closed_form : ∀ n : ℕ, 3 < n → (a n : ℂ) =
      48 * ((-1 + Complex.I) * ((-Complex.I) ^ n + Complex.I ^ (1 + n)) +
        (1 - (Real.sqrt 2 : ℂ)) ^ n + (1 + (Real.sqrt 2 : ℂ)) ^ n) :=
  cf a a_four a_five a_six a_seven a_rec

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 + X ^ 2) * (1 - 2 * X - X ^ 2)) = X * (19 + 346 * X - 120 * X ^ 2 + 202 * X ^ 3 + 173 * X ^ 4 - 144 * X ^ 5 - 72 * X ^ 6) ∧
    ∀ n : ℕ, 3 < n → (a n : ℂ) =
      48 * ((-1 + Complex.I) * ((-Complex.I) ^ n + Complex.I ^ (1 + n)) +
        (1 - (Real.sqrt 2 : ℂ)) ^ n + (1 + (Real.sqrt 2 : ℂ)) ^ n) :=
  ⟨gf, closed_form⟩

/-- Controls: the entry's terms a(1..10), from the recurrence and the first values. -/
theorem controls : a 1 = 19 ∧ a 2 = 384 ∧ a 3 = 648 ∧ a 4 = 1536 ∧ a 5 = 4032 ∧ a 6 = 9600 ∧ a 7 = 22848 ∧ a 8 = 55296 ∧ a 9 = 133824 ∧ a 10 = 322944 := by
  have r0 := a_rec 0; have r1 := a_rec 1; have r2 := a_rec 2
  have h1 := a_one; have h2 := a_two; have h3 := a_three; have h4 := a_four; have h5 := a_five; have h6 := a_six; have h7 := a_seven
  norm_num at r0 r1 r2
  omega

end OMA.S_oeis_a222835

theorem OMA.solution : type_of% @OMA.S_oeis_a222835.main :=
  OMA.S_oeis_a222835.conjecture
