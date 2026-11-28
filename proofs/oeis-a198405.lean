import OMAStatements.S_oeis_a198405

namespace OMA.S_oeis_a198405

open PowerSeries Finset


instance {R C K : ℕ} : DecidablePred (@RowMajorNew R C K) := fun x => by
  unfold RowMajorNew; infer_instance



instance {R C K : ℕ} : DecidablePred (@Cond R C K) := fun x => by
  unfold Cond; infer_instance


/-! ## Rows -/

/-- The number of horizontal neighbors of entry j of the row r with an equal value. -/
def hEq (r : Fin 2 → Fin 5) (j : Fin 2) : ℕ :=
  ((univ : Finset (Fin 2)).filter
    (fun j' => (j'.val + 1 = j.val ∨ j.val + 1 = j'.val) ∧ r j' = r j)).card

/-- 1 when the row q exists and its entry j is equal to r j. -/
def vEq (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (j : Fin 2) : ℕ :=
  match q with
  | none => 0
  | some p => if p j = r j then 1 else 0

/-- The condition on the row r with the row q above it and the row s below it. -/
def rowCond (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (s : Option (Fin 2 → Fin 5)) : Prop :=
  ∀ j, (hEq r j + vEq q r j + vEq s r j) = 1

instance (q : Option (Fin 2 → Fin 5)) (s : Option (Fin 2 → Fin 5)) : DecidablePred (fun r => rowCond q r s) :=
  fun r => by unfold rowCond; infer_instance

instance (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (s : Option (Fin 2 → Fin 5)) : Decidable (rowCond q r s) := by
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
def prevRow {n : ℕ} (q : Option (Fin 2 → Fin 5)) (g : Fin n → Fin 2 → Fin 5) (i : Fin n) : Option (Fin 2 → Fin 5) :=
  match i with
  | ⟨0, _⟩ => q
  | ⟨k + 1, h⟩ => some (g ⟨k, Nat.lt_of_succ_lt h⟩)

/-- The row below row i of g, none for the last row. -/
def nextRow {n : ℕ} (g : Fin n → Fin 2 → Fin 5) (i : Fin n) : Option (Fin 2 → Fin 5) :=
  if h : i.val + 1 < n then some (g ⟨i.val + 1, h⟩) else none

/-- Every row of g satisfies the condition with the rows above and below it; q is the row above
the first row. -/
def ValidFrom {n : ℕ} (q : Option (Fin 2 → Fin 5)) (g : Fin n → Fin 2 → Fin 5) : Prop :=
  ∀ i, rowCond (prevRow q g i) (g i) (nextRow g i)

instance {n : ℕ} (q : Option (Fin 2 → Fin 5)) : DecidablePred (@ValidFrom n q) := fun g => by
  unfold ValidFrom; infer_instance

lemma validFrom_one (q : Option (Fin 2 → Fin 5)) (g : Fin 1 → Fin 2 → Fin 5) :
    ValidFrom q g ↔ rowCond q (g 0) none := by
  constructor
  · intro h
    exact h 0
  · intro h i
    have hi : i = 0 := Fin.fin_one_eq_zero i
    subst hi
    exact h

lemma prevRow_cons_zero {n : ℕ} (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (h : Fin (n + 1) → Fin 2 → Fin 5) :
    prevRow q (Fin.cons r h : Fin (n + 2) → Fin 2 → Fin 5) 0 = q := rfl

lemma prevRow_cons_succ {n : ℕ} (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (h : Fin (n + 1) → Fin 2 → Fin 5)
    (k : Fin (n + 1)) :
    prevRow q (Fin.cons r h : Fin (n + 2) → Fin 2 → Fin 5) k.succ = prevRow (some r) h k := by
  rcases k with ⟨_ | j, hk⟩ <;> rfl

lemma nextRow_cons_zero {n : ℕ} (r : Fin 2 → Fin 5) (h : Fin (n + 1) → Fin 2 → Fin 5) :
    nextRow (Fin.cons r h : Fin (n + 2) → Fin 2 → Fin 5) 0 = some (h 0) := by
  unfold nextRow
  rw [dif_pos (by simp)]
  rfl

lemma nextRow_cons_succ {n : ℕ} (r : Fin 2 → Fin 5) (h : Fin (n + 1) → Fin 2 → Fin 5) (k : Fin (n + 1)) :
    nextRow (Fin.cons r h : Fin (n + 2) → Fin 2 → Fin 5) k.succ = nextRow h k := by
  unfold nextRow
  by_cases hk : k.val + 1 < n + 1
  · rw [dif_pos (by simp; omega), dif_pos hk]
    rfl
  · rw [dif_neg (by simp; omega), dif_neg hk]

lemma validFrom_cons {n : ℕ} (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (h : Fin (n + 1) → Fin 2 → Fin 5) :
    ValidFrom q (Fin.cons r h : Fin (n + 2) → Fin 2 → Fin 5) ↔
      rowCond q r (some (h 0)) ∧ ValidFrom (some r) h := by
  unfold ValidFrom
  rw [Fin.forall_fin_succ]
  simp only [prevRow_cons_zero, prevRow_cons_succ, nextRow_cons_zero, nextRow_cons_succ,
    Fin.cons_zero, Fin.cons_succ]

/-! ## Counting by the first row -/

/-- W(n, q, r, c): arrays with n + 1 rows, first row r with the row q above it, every row
satisfying the condition, values introduced in row major order after the values below c. -/
def W (n : ℕ) (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 2 → Fin 5)).filter
    (fun g => ValidFrom q g ∧ RGSfrom c g ∧ g 0 = r)).card

lemma W_zero (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ) :
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
def consEmb (n : ℕ) (r : Fin 2 → Fin 5) :
    (Fin (n + 1) → Fin 2 → Fin 5) ↪ (Fin (n + 2) → Fin 2 → Fin 5) where
  toFun g := Fin.cons r g
  inj' g g' h := by
    funext i
    have := congrFun h i.succ
    simpa using this

lemma consEmb_apply (n : ℕ) (r : Fin 2 → Fin 5) (g : Fin (n + 1) → Fin 2 → Fin 5) :
    consEmb n r g = Fin.cons r g := rfl

lemma W_succ (n : ℕ) (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ) :
    W (n + 1) q r c = if rowRgs c r then
      ∑ s : Fin 2 → Fin 5, (if rowCond q r (some s) then W n (some r) s (newc c r) else 0) else 0 := by
  have e : ((univ : Finset (Fin (n + 2) → Fin 2 → Fin 5)).filter
      (fun f => ValidFrom q f ∧ RGSfrom c f ∧ f 0 = r)) =
      (((univ : Finset (Fin (n + 1) → Fin 2 → Fin 5)).filter
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
def FixFrom (c : ℕ) (σ : Equiv.Perm (Fin 5)) : Prop := ∀ v : Fin 5, c ≤ v.val → σ v = v

lemma fixFrom_lt (c : ℕ) (σ : Equiv.Perm (Fin 5)) (h : FixFrom c σ) (v : Fin 5)
    (hv : v.val < c) : (σ v).val < c := by
  by_contra hc
  push_neg at hc
  have h1 : σ (σ v) = σ v := h (σ v) hc
  have h2 : σ v = v := σ.injective h1
  rw [h2] at hc
  omega

lemma fixFrom_symm (c : ℕ) (σ : Equiv.Perm (Fin 5)) (h : FixFrom c σ) : FixFrom c σ.symm := by
  intro v hv
  rw [Equiv.symm_apply_eq]
  exact (h v hv).symm

lemma RGSfrom_perm {R : ℕ} (c : ℕ) (σ : Equiv.Perm (Fin 5)) (h : FixFrom c σ)
    (g : Fin R → Fin 2 → Fin 5) (H : RGSfrom c g) : RGSfrom c (fun i j => σ (g i j)) := by
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
def mapRow (σ : Equiv.Perm (Fin 5)) (r : Fin 2 → Fin 5) : Fin 2 → Fin 5 := fun j => σ (r j)

lemma mapRow_symm_apply (σ : Equiv.Perm (Fin 5)) (r : Fin 2 → Fin 5) : mapRow σ (mapRow σ.symm r) = r := by
  funext j
  simp [mapRow]

lemma mapRow_apply_symm (σ : Equiv.Perm (Fin 5)) (r : Fin 2 → Fin 5) : mapRow σ.symm (mapRow σ r) = r := by
  funext j
  simp [mapRow]

lemma prevRow_map {n : ℕ} (σ : Equiv.Perm (Fin 5)) (q : Option (Fin 2 → Fin 5)) (g : Fin n → Fin 2 → Fin 5)
    (i : Fin n) :
    prevRow (q.map (mapRow σ)) (fun i => mapRow σ (g i)) i = (prevRow q g i).map (mapRow σ) := by
  rcases i with ⟨_ | k, h⟩ <;> rfl

lemma nextRow_map {n : ℕ} (σ : Equiv.Perm (Fin 5)) (g : Fin n → Fin 2 → Fin 5) (i : Fin n) :
    nextRow (fun i => mapRow σ (g i)) i = (nextRow g i).map (mapRow σ) := by
  unfold nextRow
  split_ifs <;> rfl

lemma hEq_perm (σ : Equiv.Perm (Fin 5)) (r : Fin 2 → Fin 5) (j : Fin 2) :
    hEq (mapRow σ r) j = hEq r j := by
  simp [hEq, mapRow]

lemma vEq_perm (σ : Equiv.Perm (Fin 5)) (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (j : Fin 2) :
    vEq (q.map (mapRow σ)) (mapRow σ r) j = vEq q r j := by
  rcases q with _ | p <;> simp [vEq, mapRow]

lemma rowCond_perm (σ : Equiv.Perm (Fin 5)) (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5)
    (s : Option (Fin 2 → Fin 5)) :
    rowCond (q.map (mapRow σ)) (mapRow σ r) (s.map (mapRow σ)) ↔ rowCond q r s := by
  simp only [rowCond, hEq_perm, vEq_perm]

lemma validFrom_perm {n : ℕ} (σ : Equiv.Perm (Fin 5)) (q : Option (Fin 2 → Fin 5)) (g : Fin n → Fin 2 → Fin 5) :
    ValidFrom (q.map (mapRow σ)) (fun i => mapRow σ (g i)) ↔ ValidFrom q g := by
  unfold ValidFrom
  simp only [prevRow_map, nextRow_map, rowCond_perm]

lemma W_perm (σ : Equiv.Perm (Fin 5)) (c : ℕ) (hσ : FixFrom c σ) (n : ℕ) (q : Option (Fin 2 → Fin 5))
    (r : Fin 2 → Fin 5) : W n (q.map (mapRow σ)) (mapRow σ r) c = W n q r c := by
  have hv : ∀ g : Fin (n + 1) → Fin 2 → Fin 5,
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
def swV (a b v : Fin 5) : Fin 5 := if v = a then b else if v = b then a else v

/-- The pair (p, r) with the values p 0 and 0 exchanged in both rows when p 0 is below c. -/
def ren (c : ℕ) (p r : Fin 2 → Fin 5) : (Fin 2 → Fin 5) × (Fin 2 → Fin 5) :=
  if (p 0).val < c then (fun j => swV (p 0) 0 (p j), fun j => swV (p 0) 0 (r j)) else (p, r)

lemma W_ren (n c : ℕ) (p r : Fin 2 → Fin 5) : W n (some (ren c p r).1) (ren c p r).2 c = W n (some p) r c := by
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

lemma ren_zero (c : ℕ) (p r : Fin 2 → Fin 5) (h : (p 0).val < c) : (ren c p r).1 0 = 0 := by
  unfold ren
  rw [if_pos h]
  simp [swV]

lemma ren_lt (c : ℕ) (p r : Fin 2 → Fin 5) (hp : ∀ j, (p j).val < c) : ∀ j, ((ren c p r).1 j).val < c := by
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

lemma vcard {R : ℕ} (x : Fin R → Fin 2 → Fin 5) (i : Fin R) (j : Fin 2) :
    ((univ : Finset (Fin R)).filter
      (fun i' => (i'.val + 1 = i.val ∨ i.val + 1 = i'.val) ∧ x i' j = x i j)).card =
      vEq (prevRow none x i) (x i) j + vEq (nextRow x i) (x i) j := by
  rw [Finset.card_filter]
  have split : ∀ i' : Fin R,
      (if (i'.val + 1 = i.val ∨ i.val + 1 = i'.val) ∧ x i' j = x i j then 1 else 0) =
      (if i'.val + 1 = i.val ∧ x i' j = x i j then 1 else 0) +
        (if i.val + 1 = i'.val ∧ x i' j = x i j then 1 else 0) := by
    intro i'
    by_cases h1 : i'.val + 1 = i.val <;> by_cases h2 : i.val + 1 = i'.val <;>
      by_cases h3 : x i' j = x i j <;> simp [h1, h2, h3] <;> omega
  rw [Finset.sum_congr rfl (fun i' _ => split i'), Finset.sum_add_distrib]
  congr 1
  · rcases i with ⟨_ | k, hi⟩
    · refine Finset.sum_eq_zero (fun i' _ => ?_)
      rw [if_neg]
      rintro ⟨h1, _⟩
      simp at h1
    · rw [Finset.sum_eq_single (⟨k, by omega⟩ : Fin R)]
      · simp [prevRow, vEq]
      · intro b _ hb
        rw [if_neg]
        rintro ⟨h1, _⟩
        exact hb (Fin.ext (by simp at h1 ⊢; omega))
      · intro h
        exact absurd (Finset.mem_univ _) h
  · by_cases hlt : i.val + 1 < R
    · rw [Finset.sum_eq_single (⟨i.val + 1, hlt⟩ : Fin R)]
      · simp [nextRow, hlt, vEq]
      · intro b _ hb
        rw [if_neg]
        rintro ⟨h1, _⟩
        exact hb (Fin.ext (by simp; omega))
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [Finset.sum_eq_zero]
      · simp [nextRow, hlt, vEq]
      · intro b _
        rw [if_neg]
        rintro ⟨h1, _⟩
        have := b.isLt
        omega

lemma cond_iff {R : ℕ} (x : Fin R → Fin 2 → Fin 5) : Cond x ↔ ValidFrom none x := by
  unfold Cond ValidFrom rowCond eqNbrs
  simp only [vcard, hEq, Nat.add_assoc]

/-! ## Kernel form of the transfer -/

lemma sum_cons {m : ℕ} (f : (Fin (m + 1) → Fin 5) → ℕ) :
    ∑ s : Fin (m + 1) → Fin 5, f s = ∑ x : Fin 5, ∑ t : Fin m → Fin 5, f (Fin.cons x t) := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 5).symm _ _
    (fun s => by simp [Fin.consEquiv, Fin.cons_self_tail])

lemma sum_row (f : (Fin 2 → Fin 5) → ℕ) :
    ∑ s : Fin 2 → Fin 5, f s = ∑ x : Fin 5, ∑ y : Fin 5, f ![x, y] := by
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Fintype.sum_unique]
  exact congrArg f (by funext j; fin_cases j <;> rfl)

lemma row_eta (r : Fin 2 → Fin 5) : r = ![r 0, r 1] := by
  funext j
  fin_cases j <;> rfl

/-! Fast Boolean forms of the conditions for the kernel checks, tied to the definitions by
`decide` over all small cases. -/

/-- `rowRgs c r` as a Boolean. -/
def rgsB (c : ℕ) (r : Fin 2 → Fin 5) : Bool :=
  decide ((r 0).val ≤ c) &&
    decide ((r 1).val ≤ max c ((r 0).val + 1))

/-- `newc c r` by explicit maxima. -/
def newcB (c : ℕ) (r : Fin 2 → Fin 5) : ℕ :=
  max (max c ((r 0).val + 1)) ((r 1).val + 1)

/-- `rowCond q r (some t)` as a Boolean. -/
def condB (q : Option (Fin 2 → Fin 5)) (r t : Fin 2 → Fin 5) : Bool :=
  (((if r 1 = r 0 then 1 else 0) + (match q with | none => 0 | some p => if p 0 = r 0 then 1 else 0) + (if t 0 = r 0 then 1 else 0)) == 1) &&
    (((if r 0 = r 1 then 1 else 0) + (match q with | none => 0 | some p => if p 1 = r 1 then 1 else 0) + (if t 1 = r 1 then 1 else 0)) == 1)

/-- `rowCond q r none` as a Boolean. -/
def endB (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) : Bool :=
  (((if r 1 = r 0 then 1 else 0) + (match q with | none => 0 | some p => if p 0 = r 0 then 1 else 0)) == 1) &&
    (((if r 0 = r 1 then 1 else 0) + (match q with | none => 0 | some p => if p 1 = r 1 then 1 else 0)) == 1)

lemma rgsB_eq : ∀ c : Fin 6, ∀ y1 y2 : Fin 5,
    decide (rowRgs c.val ![y1, y2]) = rgsB c.val ![y1, y2] := by
  decide +kernel

lemma newcB_eq : ∀ c : Fin 6, ∀ y1 y2 : Fin 5,
    newc c.val ![y1, y2] = newcB c.val ![y1, y2] := by
  decide +kernel


lemma rgsB_iff (c : ℕ) (hc : c ≤ 5) (r : Fin 2 → Fin 5) : rowRgs c r ↔ rgsB c r = true := by
  rw [row_eta r, ← rgsB_eq ⟨c, by omega⟩, decide_eq_true_iff]

lemma newcB_eq' (c : ℕ) (hc : c ≤ 5) (r : Fin 2 → Fin 5) : newc c r = newcB c r := by
  rw [row_eta r]
  exact newcB_eq ⟨c, by omega⟩ (r 0) (r 1)

lemma newcB_le (c : ℕ) (hc : c ≤ 5) (r : Fin 2 → Fin 5) : newcB c r ≤ 5 := by
  rw [← newcB_eq' c hc r]
  exact newc_le c hc r

lemma hEq_two : ∀ y1 y2 : Fin 5,
    hEq ![y1, y2] 0 = (if y2 = y1 then 1 else 0) ∧ hEq ![y1, y2] 1 = (if y1 = y2 then 1 else 0) := by
  decide +kernel

lemma condB_iff (q : Option (Fin 2 → Fin 5)) (r t : Fin 2 → Fin 5) : rowCond q r (some t) ↔ condB q r t = true := by
  have h0 := (hEq_two (r 0) (r 1)).1
  have h1 := (hEq_two (r 0) (r 1)).2
  rw [← row_eta r] at h0 h1
  rcases q with _ | p <;>
    simp only [rowCond, condB, Fin.forall_fin_two, h0, h1, vEq, Bool.and_eq_true, beq_iff_eq]

lemma endB_iff (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) : rowCond q r none ↔ endB q r = true := by
  have h0 := (hEq_two (r 0) (r 1)).1
  have h1 := (hEq_two (r 0) (r 1)).2
  rw [← row_eta r] at h0 h1
  rcases q with _ | p <;>
    simp only [rowCond, endB, Fin.forall_fin_two, h0, h1, vEq, add_zero, Bool.and_eq_true,
      beq_iff_eq]


/-- One step of the transfer, the rows below r enumerated entry by entry. -/
def T (g : Option (Fin 2 → Fin 5) → (Fin 2 → Fin 5) → ℕ → ℕ) (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ) : ℕ :=
  if rgsB c r = true then
    ∑ x : Fin 5, ∑ y : Fin 5, (if condB q r ![x, y] = true then g (some r) ![x, y] (newcB c r) else 0)
  else 0

lemma W_succT (n : ℕ) (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ) (hc : c ≤ 5) :
    W (n + 1) q r c = T (W n) q r c := by
  rw [W_succ, sum_row]
  unfold T
  simp only [rgsB_iff c hc, condB_iff, newcB_eq' c hc]

lemma T_congr (g g' : Option (Fin 2 → Fin 5) → (Fin 2 → Fin 5) → ℕ → ℕ) (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ)
    (h : ∀ s, g (some r) s (newcB c r) = g' (some r) s (newcB c r)) : T g q r c = T g' q r c := by
  unfold T
  simp only [h]

/-- W(0) as a function. -/
def W0f (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ) : ℕ :=
  if endB q r = true ∧ rgsB c r = true then 1 else 0

lemma W_zero' (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ) (hc : c ≤ 5) : W 0 q r c = W0f q r c := by
  rw [W_zero]
  unfold W0f
  simp only [endB_iff, rgsB_iff c hc]

lemma inv_next (c : ℕ) (hc : c ≤ 5) (r : Fin 2 → Fin 5) :
    ∀ p, some r = some p → ∀ j, (p j).val < newcB c r := by
  intro p hp j
  rw [← Option.some.inj hp, ← newcB_eq' c hc r]
  exact (lt_newc c r _).2 (Or.inr ⟨j, le_refl _⟩)

/-- W(1, none, r, c) for c <= 5, nested by the entries of r and then c. -/
def LN1 : List (List (List ℕ)) :=
  [[[1, 1, 2, 3, 4, 4], [1, 1, 1, 1, 1, 1], [0, 0, 1, 1, 1, 1], [0, 0, 0, 1, 1, 1], [0, 0, 0, 0, 1, 1]], [[0, 1, 1, 1, 1, 1], [0, 2, 2, 3, 4, 4], [0, 1, 1, 1, 1, 1], [0, 0, 0, 1, 1, 1], [0, 0, 0, 0, 1, 1]], [[0, 0, 1, 1, 1, 1], [0, 0, 1, 1, 1, 1], [0, 0, 3, 3, 4, 4], [0, 0, 1, 1, 1, 1], [0, 0, 0, 0, 1, 1]], [[0, 0, 0, 1, 1, 1], [0, 0, 0, 1, 1, 1], [0, 0, 0, 1, 1, 1], [0, 0, 0, 4, 4, 4], [0, 0, 0, 1, 1, 1]], [[0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 4, 4]]]

/-- W(1, some p, r, c) at the pairs (p, r) with p 0 = 0 and the values of p below c, nested by the entries of p, of r, and then c (0 elsewhere). -/
def LS1 : List (List (List (List (List ℕ)))) :=
  [[[[], [[], [0, 2, 2, 3, 4, 4], [0, 1, 1, 1, 1, 1], [0, 0, 0, 1, 1, 1], [0, 0, 0, 0, 1, 1]], [[], [0, 0, 1, 1, 1, 1], [0, 0, 3, 3, 4, 4], [0, 0, 1, 1, 1, 1], [0, 0, 0, 0, 1, 1]], [[], [0, 0, 0, 1, 1, 1], [0, 0, 0, 1, 1, 1], [0, 0, 0, 4, 4, 4], [0, 0, 0, 1, 1, 1]], [[], [0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 4, 4]]], [[[], [0, 0, 1, 2, 3, 3]], [[0, 0, 1, 1, 1, 1], [], [0, 0, 1, 1, 1, 1], [0, 0, 0, 1, 1, 1], [0, 0, 0, 0, 1, 1]], [[0, 0, 1, 1, 1, 1], [], [0, 0, 3, 3, 4, 4], [0, 0, 1, 1, 1, 1], [0, 0, 0, 0, 1, 1]], [[0, 0, 0, 1, 1, 1], [], [0, 0, 0, 1, 1, 1], [0, 0, 0, 4, 4, 4], [0, 0, 0, 1, 1, 1]], [[0, 0, 0, 0, 1, 1], [], [0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 4, 4]]], [[[], [], [0, 0, 0, 2, 3, 3]], [[0, 0, 0, 1, 1, 1], [0, 0, 0, 3, 4, 4], [], [0, 0, 0, 1, 1, 1], [0, 0, 0, 0, 1, 1]], [[0, 0, 0, 1, 1, 1], [0, 0, 0, 1, 1, 1], [], [0, 0, 0, 1, 1, 1], [0, 0, 0, 0, 1, 1]], [[0, 0, 0, 1, 1, 1], [0, 0, 0, 1, 1, 1], [], [0, 0, 0, 4, 4, 4], [0, 0, 0, 1, 1, 1]], [[0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 1, 1], [], [0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 4, 4]]], [[[], [], [], [0, 0, 0, 0, 3, 3]], [[0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 4, 4], [0, 0, 0, 0, 1, 1], [], [0, 0, 0, 0, 1, 1]], [[0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 4, 4], [], [0, 0, 0, 0, 1, 1]], [[0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 1, 1], [], [0, 0, 0, 0, 1, 1]], [[0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 1, 1], [], [0, 0, 0, 0, 4, 4]]], [[[], [], [], [], [0, 0, 0, 0, 0, 3]], [[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 4], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1]], [[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 4], [0, 0, 0, 0, 0, 1]], [[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 4]], [[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1]]]]]

/-- W(1) as a table. -/
def tab1 (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ) : ℕ :=
  match q with
  | none => ((LN1.getD (r 0).val []).getD (r 1).val []).getD c 0
  | some p => ((((LS1.getD (p 0).val []).getD (p 1).val []).getD (r 0).val []).getD (r 1).val []).getD c 0

/-- W(1) read at the renamed pair. -/
def tabc1 (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ) : ℕ :=
  match q with
  | none => tab1 none r c
  | some p => tab1 (some (ren c p r).1) (ren c p r).2 c

/-- W(2, none, r, c) for c <= 5, nested by the entries of r and then c. -/
def LN2 : List (List (List ℕ)) :=
  [[[3, 3, 8, 17, 28, 28], [1, 1, 1, 2, 3, 3], [0, 0, 2, 2, 3, 3], [0, 0, 0, 3, 3, 3], [0, 0, 0, 0, 3, 3]], [[0, 1, 1, 2, 3, 3], [0, 8, 8, 17, 28, 28], [0, 2, 2, 2, 3, 3], [0, 0, 0, 3, 3, 3], [0, 0, 0, 0, 3, 3]], [[0, 0, 2, 2, 3, 3], [0, 0, 2, 2, 3, 3], [0, 0, 17, 17, 28, 28], [0, 0, 3, 3, 3, 3], [0, 0, 0, 0, 3, 3]], [[0, 0, 0, 3, 3, 3], [0, 0, 0, 3, 3, 3], [0, 0, 0, 3, 3, 3], [0, 0, 0, 28, 28, 28], [0, 0, 0, 3, 3, 3]], [[0, 0, 0, 0, 3, 3], [0, 0, 0, 0, 3, 3], [0, 0, 0, 0, 3, 3], [0, 0, 0, 0, 3, 3], [0, 0, 0, 0, 28, 28]]]

/-- W(2, some p, r, c) at the pairs (p, r) with p 0 = 0 and the values of p below c, nested by the entries of p, of r, and then c (0 elsewhere). -/
def LS2 : List (List (List (List (List ℕ)))) :=
  [[[[], [[], [0, 8, 8, 17, 28, 28], [0, 2, 2, 2, 3, 3], [0, 0, 0, 3, 3, 3], [0, 0, 0, 0, 3, 3]], [[], [0, 0, 2, 2, 3, 3], [0, 0, 17, 17, 28, 28], [0, 0, 3, 3, 3, 3], [0, 0, 0, 0, 3, 3]], [[], [0, 0, 0, 3, 3, 3], [0, 0, 0, 3, 3, 3], [0, 0, 0, 28, 28, 28], [0, 0, 0, 3, 3, 3]], [[], [0, 0, 0, 0, 3, 3], [0, 0, 0, 0, 3, 3], [0, 0, 0, 0, 3, 3], [0, 0, 0, 0, 28, 28]]], [[[], [0, 0, 7, 15, 25, 25]], [[0, 0, 1, 2, 3, 3], [], [0, 0, 2, 2, 3, 3], [0, 0, 0, 3, 3, 3], [0, 0, 0, 0, 3, 3]], [[0, 0, 2, 2, 3, 3], [], [0, 0, 17, 17, 28, 28], [0, 0, 3, 3, 3, 3], [0, 0, 0, 0, 3, 3]], [[0, 0, 0, 3, 3, 3], [], [0, 0, 0, 3, 3, 3], [0, 0, 0, 28, 28, 28], [0, 0, 0, 3, 3, 3]], [[0, 0, 0, 0, 3, 3], [], [0, 0, 0, 0, 3, 3], [0, 0, 0, 0, 3, 3], [0, 0, 0, 0, 28, 28]]], [[[], [], [0, 0, 0, 15, 25, 25]], [[0, 0, 0, 2, 3, 3], [0, 0, 0, 17, 28, 28], [], [0, 0, 0, 3, 3, 3], [0, 0, 0, 0, 3, 3]], [[0, 0, 0, 2, 3, 3], [0, 0, 0, 2, 3, 3], [], [0, 0, 0, 3, 3, 3], [0, 0, 0, 0, 3, 3]], [[0, 0, 0, 3, 3, 3], [0, 0, 0, 3, 3, 3], [], [0, 0, 0, 28, 28, 28], [0, 0, 0, 3, 3, 3]], [[0, 0, 0, 0, 3, 3], [0, 0, 0, 0, 3, 3], [], [0, 0, 0, 0, 3, 3], [0, 0, 0, 0, 28, 28]]], [[[], [], [], [0, 0, 0, 0, 25, 25]], [[0, 0, 0, 0, 3, 3], [0, 0, 0, 0, 28, 28], [0, 0, 0, 0, 3, 3], [], [0, 0, 0, 0, 3, 3]], [[0, 0, 0, 0, 3, 3], [0, 0, 0, 0, 3, 3], [0, 0, 0, 0, 28, 28], [], [0, 0, 0, 0, 3, 3]], [[0, 0, 0, 0, 3, 3], [0, 0, 0, 0, 3, 3], [0, 0, 0, 0, 3, 3], [], [0, 0, 0, 0, 3, 3]], [[0, 0, 0, 0, 3, 3], [0, 0, 0, 0, 3, 3], [0, 0, 0, 0, 3, 3], [], [0, 0, 0, 0, 28, 28]]], [[[], [], [], [], [0, 0, 0, 0, 0, 25]], [[0, 0, 0, 0, 0, 3], [0, 0, 0, 0, 0, 28], [0, 0, 0, 0, 0, 3], [0, 0, 0, 0, 0, 3]], [[0, 0, 0, 0, 0, 3], [0, 0, 0, 0, 0, 3], [0, 0, 0, 0, 0, 28], [0, 0, 0, 0, 0, 3]], [[0, 0, 0, 0, 0, 3], [0, 0, 0, 0, 0, 3], [0, 0, 0, 0, 0, 3], [0, 0, 0, 0, 0, 28]], [[0, 0, 0, 0, 0, 3], [0, 0, 0, 0, 0, 3], [0, 0, 0, 0, 0, 3], [0, 0, 0, 0, 0, 3]]]]]

/-- W(2) as a table. -/
def tab2 (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ) : ℕ :=
  match q with
  | none => ((LN2.getD (r 0).val []).getD (r 1).val []).getD c 0
  | some p => ((((LS2.getD (p 0).val []).getD (p 1).val []).getD (r 0).val []).getD (r 1).val []).getD c 0

/-- W(2) read at the renamed pair. -/
def tabc2 (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ) : ℕ :=
  match q with
  | none => tab2 none r c
  | some p => tab2 (some (ren c p r).1) (ren c p r).2 c

/-- W(3, none, r, c) for c <= 5, nested by the entries of r and then c. -/
def LN3 : List (List (List ℕ)) :=
  [[[10, 10, 32, 81, 148, 148], [7, 7, 7, 15, 25, 25], [0, 0, 15, 15, 25, 25], [0, 0, 0, 25, 25, 25], [0, 0, 0, 0, 25, 25]], [[0, 7, 7, 15, 25, 25], [0, 32, 32, 81, 148, 148], [0, 15, 15, 15, 25, 25], [0, 0, 0, 25, 25, 25], [0, 0, 0, 0, 25, 25]], [[0, 0, 15, 15, 25, 25], [0, 0, 15, 15, 25, 25], [0, 0, 81, 81, 148, 148], [0, 0, 25, 25, 25, 25], [0, 0, 0, 0, 25, 25]], [[0, 0, 0, 25, 25, 25], [0, 0, 0, 25, 25, 25], [0, 0, 0, 25, 25, 25], [0, 0, 0, 148, 148, 148], [0, 0, 0, 25, 25, 25]], [[0, 0, 0, 0, 25, 25], [0, 0, 0, 0, 25, 25], [0, 0, 0, 0, 25, 25], [0, 0, 0, 0, 25, 25], [0, 0, 0, 0, 148, 148]]]

/-- W(3, some p, r, c) at the pairs (p, r) with p 0 = 0 and the values of p below c, nested by the entries of p, of r, and then c (0 elsewhere). -/
def LS3 : List (List (List (List (List ℕ)))) :=
  [[[[], [[], [0, 32, 32, 81, 148, 148], [0, 15, 15, 15, 25, 25], [0, 0, 0, 25, 25, 25], [0, 0, 0, 0, 25, 25]], [[], [0, 0, 15, 15, 25, 25], [0, 0, 81, 81, 148, 148], [0, 0, 25, 25, 25, 25], [0, 0, 0, 0, 25, 25]], [[], [0, 0, 0, 25, 25, 25], [0, 0, 0, 25, 25, 25], [0, 0, 0, 148, 148, 148], [0, 0, 0, 25, 25, 25]], [[], [0, 0, 0, 0, 25, 25], [0, 0, 0, 0, 25, 25], [0, 0, 0, 0, 25, 25], [0, 0, 0, 0, 148, 148]]], [[[], [0, 0, 25, 66, 123, 123]], [[0, 0, 7, 15, 25, 25], [], [0, 0, 15, 15, 25, 25], [0, 0, 0, 25, 25, 25], [0, 0, 0, 0, 25, 25]], [[0, 0, 15, 15, 25, 25], [], [0, 0, 81, 81, 148, 148], [0, 0, 25, 25, 25, 25], [0, 0, 0, 0, 25, 25]], [[0, 0, 0, 25, 25, 25], [], [0, 0, 0, 25, 25, 25], [0, 0, 0, 148, 148, 148], [0, 0, 0, 25, 25, 25]], [[0, 0, 0, 0, 25, 25], [], [0, 0, 0, 0, 25, 25], [0, 0, 0, 0, 25, 25], [0, 0, 0, 0, 148, 148]]], [[[], [], [0, 0, 0, 66, 123, 123]], [[0, 0, 0, 15, 25, 25], [0, 0, 0, 81, 148, 148], [], [0, 0, 0, 25, 25, 25], [0, 0, 0, 0, 25, 25]], [[0, 0, 0, 15, 25, 25], [0, 0, 0, 15, 25, 25], [], [0, 0, 0, 25, 25, 25], [0, 0, 0, 0, 25, 25]], [[0, 0, 0, 25, 25, 25], [0, 0, 0, 25, 25, 25], [], [0, 0, 0, 148, 148, 148], [0, 0, 0, 25, 25, 25]], [[0, 0, 0, 0, 25, 25], [0, 0, 0, 0, 25, 25], [], [0, 0, 0, 0, 25, 25], [0, 0, 0, 0, 148, 148]]], [[[], [], [], [0, 0, 0, 0, 123, 123]], [[0, 0, 0, 0, 25, 25], [0, 0, 0, 0, 148, 148], [0, 0, 0, 0, 25, 25], [], [0, 0, 0, 0, 25, 25]], [[0, 0, 0, 0, 25, 25], [0, 0, 0, 0, 25, 25], [0, 0, 0, 0, 148, 148], [], [0, 0, 0, 0, 25, 25]], [[0, 0, 0, 0, 25, 25], [0, 0, 0, 0, 25, 25], [0, 0, 0, 0, 25, 25], [], [0, 0, 0, 0, 25, 25]], [[0, 0, 0, 0, 25, 25], [0, 0, 0, 0, 25, 25], [0, 0, 0, 0, 25, 25], [], [0, 0, 0, 0, 148, 148]]], [[[], [], [], [], [0, 0, 0, 0, 0, 123]], [[0, 0, 0, 0, 0, 25], [0, 0, 0, 0, 0, 148], [0, 0, 0, 0, 0, 25], [0, 0, 0, 0, 0, 25]], [[0, 0, 0, 0, 0, 25], [0, 0, 0, 0, 0, 25], [0, 0, 0, 0, 0, 148], [0, 0, 0, 0, 0, 25]], [[0, 0, 0, 0, 0, 25], [0, 0, 0, 0, 0, 25], [0, 0, 0, 0, 0, 25], [0, 0, 0, 0, 0, 148]], [[0, 0, 0, 0, 0, 25], [0, 0, 0, 0, 0, 25], [0, 0, 0, 0, 0, 25], [0, 0, 0, 0, 0, 25]]]]]

/-- W(3) as a table. -/
def tab3 (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ) : ℕ :=
  match q with
  | none => ((LN3.getD (r 0).val []).getD (r 1).val []).getD c 0
  | some p => ((((LS3.getD (p 0).val []).getD (p 1).val []).getD (r 0).val []).getD (r 1).val []).getD c 0

/-- W(3) read at the renamed pair. -/
def tabc3 (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ) : ℕ :=
  match q with
  | none => tab3 none r c
  | some p => tab3 (some (ren c p r).1) (ren c p r).2 c

/-- W(4, none, r, c) for c <= 5, nested by the entries of r and then c. -/
def LN4 : List (List (List ℕ)) :=
  [[[47, 47, 168, 465, 892, 892], [25, 25, 25, 66, 123, 123], [0, 0, 66, 66, 123, 123], [0, 0, 0, 123, 123, 123], [0, 0, 0, 0, 123, 123]], [[0, 25, 25, 66, 123, 123], [0, 168, 168, 465, 892, 892], [0, 66, 66, 66, 123, 123], [0, 0, 0, 123, 123, 123], [0, 0, 0, 0, 123, 123]], [[0, 0, 66, 66, 123, 123], [0, 0, 66, 66, 123, 123], [0, 0, 465, 465, 892, 892], [0, 0, 123, 123, 123, 123], [0, 0, 0, 0, 123, 123]], [[0, 0, 0, 123, 123, 123], [0, 0, 0, 123, 123, 123], [0, 0, 0, 123, 123, 123], [0, 0, 0, 892, 892, 892], [0, 0, 0, 123, 123, 123]], [[0, 0, 0, 0, 123, 123], [0, 0, 0, 0, 123, 123], [0, 0, 0, 0, 123, 123], [0, 0, 0, 0, 123, 123], [0, 0, 0, 0, 892, 892]]]

/-- W(4, some p, r, c) at the pairs (p, r) with p 0 = 0 and the values of p below c, nested by the entries of p, of r, and then c (0 elsewhere). -/
def LS4 : List (List (List (List (List ℕ)))) :=
  [[[[], [[], [0, 168, 168, 465, 892, 892], [0, 66, 66, 66, 123, 123], [0, 0, 0, 123, 123, 123], [0, 0, 0, 0, 123, 123]], [[], [0, 0, 66, 66, 123, 123], [0, 0, 465, 465, 892, 892], [0, 0, 123, 123, 123, 123], [0, 0, 0, 0, 123, 123]], [[], [0, 0, 0, 123, 123, 123], [0, 0, 0, 123, 123, 123], [0, 0, 0, 892, 892, 892], [0, 0, 0, 123, 123, 123]], [[], [0, 0, 0, 0, 123, 123], [0, 0, 0, 0, 123, 123], [0, 0, 0, 0, 123, 123], [0, 0, 0, 0, 892, 892]]], [[[], [0, 0, 143, 399, 769, 769]], [[0, 0, 25, 66, 123, 123], [], [0, 0, 66, 66, 123, 123], [0, 0, 0, 123, 123, 123], [0, 0, 0, 0, 123, 123]], [[0, 0, 66, 66, 123, 123], [], [0, 0, 465, 465, 892, 892], [0, 0, 123, 123, 123, 123], [0, 0, 0, 0, 123, 123]], [[0, 0, 0, 123, 123, 123], [], [0, 0, 0, 123, 123, 123], [0, 0, 0, 892, 892, 892], [0, 0, 0, 123, 123, 123]], [[0, 0, 0, 0, 123, 123], [], [0, 0, 0, 0, 123, 123], [0, 0, 0, 0, 123, 123], [0, 0, 0, 0, 892, 892]]], [[[], [], [0, 0, 0, 399, 769, 769]], [[0, 0, 0, 66, 123, 123], [0, 0, 0, 465, 892, 892], [], [0, 0, 0, 123, 123, 123], [0, 0, 0, 0, 123, 123]], [[0, 0, 0, 66, 123, 123], [0, 0, 0, 66, 123, 123], [], [0, 0, 0, 123, 123, 123], [0, 0, 0, 0, 123, 123]], [[0, 0, 0, 123, 123, 123], [0, 0, 0, 123, 123, 123], [], [0, 0, 0, 892, 892, 892], [0, 0, 0, 123, 123, 123]], [[0, 0, 0, 0, 123, 123], [0, 0, 0, 0, 123, 123], [], [0, 0, 0, 0, 123, 123], [0, 0, 0, 0, 892, 892]]], [[[], [], [], [0, 0, 0, 0, 769, 769]], [[0, 0, 0, 0, 123, 123], [0, 0, 0, 0, 892, 892], [0, 0, 0, 0, 123, 123], [], [0, 0, 0, 0, 123, 123]], [[0, 0, 0, 0, 123, 123], [0, 0, 0, 0, 123, 123], [0, 0, 0, 0, 892, 892], [], [0, 0, 0, 0, 123, 123]], [[0, 0, 0, 0, 123, 123], [0, 0, 0, 0, 123, 123], [0, 0, 0, 0, 123, 123], [], [0, 0, 0, 0, 123, 123]], [[0, 0, 0, 0, 123, 123], [0, 0, 0, 0, 123, 123], [0, 0, 0, 0, 123, 123], [], [0, 0, 0, 0, 892, 892]]], [[[], [], [], [], [0, 0, 0, 0, 0, 769]], [[0, 0, 0, 0, 0, 123], [0, 0, 0, 0, 0, 892], [0, 0, 0, 0, 0, 123], [0, 0, 0, 0, 0, 123]], [[0, 0, 0, 0, 0, 123], [0, 0, 0, 0, 0, 123], [0, 0, 0, 0, 0, 892], [0, 0, 0, 0, 0, 123]], [[0, 0, 0, 0, 0, 123], [0, 0, 0, 0, 0, 123], [0, 0, 0, 0, 0, 123], [0, 0, 0, 0, 0, 892]], [[0, 0, 0, 0, 0, 123], [0, 0, 0, 0, 0, 123], [0, 0, 0, 0, 0, 123], [0, 0, 0, 0, 0, 123]]]]]

/-- W(4) as a table. -/
def tab4 (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ) : ℕ :=
  match q with
  | none => ((LN4.getD (r 0).val []).getD (r 1).val []).getD c 0
  | some p => ((((LS4.getD (p 0).val []).getD (p 1).val []).getD (r 0).val []).getD (r 1).val []).getD c 0

/-- W(4) read at the renamed pair. -/
def tabc4 (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ) : ℕ :=
  match q with
  | none => tab4 none r c
  | some p => tab4 (some (ren c p r).1) (ren c p r).2 c

/-- W(5, none, r, c) for c <= 5, nested by the entries of r and then c. -/
def LN5 : List (List (List ℕ)) :=
  [[[234, 234, 888, 2569, 5044, 5044], [143, 143, 143, 399, 769, 769], [0, 0, 399, 399, 769, 769], [0, 0, 0, 769, 769, 769], [0, 0, 0, 0, 769, 769]], [[0, 143, 143, 399, 769, 769], [0, 888, 888, 2569, 5044, 5044], [0, 399, 399, 399, 769, 769], [0, 0, 0, 769, 769, 769], [0, 0, 0, 0, 769, 769]], [[0, 0, 399, 399, 769, 769], [0, 0, 399, 399, 769, 769], [0, 0, 2569, 2569, 5044, 5044], [0, 0, 769, 769, 769, 769], [0, 0, 0, 0, 769, 769]], [[0, 0, 0, 769, 769, 769], [0, 0, 0, 769, 769, 769], [0, 0, 0, 769, 769, 769], [0, 0, 0, 5044, 5044, 5044], [0, 0, 0, 769, 769, 769]], [[0, 0, 0, 0, 769, 769], [0, 0, 0, 0, 769, 769], [0, 0, 0, 0, 769, 769], [0, 0, 0, 0, 769, 769], [0, 0, 0, 0, 5044, 5044]]]

/-- W(5, some p, r, c) at the pairs (p, r) with p 0 = 0 and the values of p below c, nested by the entries of p, of r, and then c (0 elsewhere). -/
def LS5 : List (List (List (List (List ℕ)))) :=
  [[[[], [[], [0, 888, 888, 2569, 5044, 5044], [0, 399, 399, 399, 769, 769], [0, 0, 0, 769, 769, 769], [0, 0, 0, 0, 769, 769]], [[], [0, 0, 399, 399, 769, 769], [0, 0, 2569, 2569, 5044, 5044], [0, 0, 769, 769, 769, 769], [0, 0, 0, 0, 769, 769]], [[], [0, 0, 0, 769, 769, 769], [0, 0, 0, 769, 769, 769], [0, 0, 0, 5044, 5044, 5044], [0, 0, 0, 769, 769, 769]], [[], [0, 0, 0, 0, 769, 769], [0, 0, 0, 0, 769, 769], [0, 0, 0, 0, 769, 769], [0, 0, 0, 0, 5044, 5044]]], [[[], [0, 0, 745, 2170, 4275, 4275]], [[0, 0, 143, 399, 769, 769], [], [0, 0, 399, 399, 769, 769], [0, 0, 0, 769, 769, 769], [0, 0, 0, 0, 769, 769]], [[0, 0, 399, 399, 769, 769], [], [0, 0, 2569, 2569, 5044, 5044], [0, 0, 769, 769, 769, 769], [0, 0, 0, 0, 769, 769]], [[0, 0, 0, 769, 769, 769], [], [0, 0, 0, 769, 769, 769], [0, 0, 0, 5044, 5044, 5044], [0, 0, 0, 769, 769, 769]], [[0, 0, 0, 0, 769, 769], [], [0, 0, 0, 0, 769, 769], [0, 0, 0, 0, 769, 769], [0, 0, 0, 0, 5044, 5044]]], [[[], [], [0, 0, 0, 2170, 4275, 4275]], [[0, 0, 0, 399, 769, 769], [0, 0, 0, 2569, 5044, 5044], [], [0, 0, 0, 769, 769, 769], [0, 0, 0, 0, 769, 769]], [[0, 0, 0, 399, 769, 769], [0, 0, 0, 399, 769, 769], [], [0, 0, 0, 769, 769, 769], [0, 0, 0, 0, 769, 769]], [[0, 0, 0, 769, 769, 769], [0, 0, 0, 769, 769, 769], [], [0, 0, 0, 5044, 5044, 5044], [0, 0, 0, 769, 769, 769]], [[0, 0, 0, 0, 769, 769], [0, 0, 0, 0, 769, 769], [], [0, 0, 0, 0, 769, 769], [0, 0, 0, 0, 5044, 5044]]], [[[], [], [], [0, 0, 0, 0, 4275, 4275]], [[0, 0, 0, 0, 769, 769], [0, 0, 0, 0, 5044, 5044], [0, 0, 0, 0, 769, 769], [], [0, 0, 0, 0, 769, 769]], [[0, 0, 0, 0, 769, 769], [0, 0, 0, 0, 769, 769], [0, 0, 0, 0, 5044, 5044], [], [0, 0, 0, 0, 769, 769]], [[0, 0, 0, 0, 769, 769], [0, 0, 0, 0, 769, 769], [0, 0, 0, 0, 769, 769], [], [0, 0, 0, 0, 769, 769]], [[0, 0, 0, 0, 769, 769], [0, 0, 0, 0, 769, 769], [0, 0, 0, 0, 769, 769], [], [0, 0, 0, 0, 5044, 5044]]], [[[], [], [], [], [0, 0, 0, 0, 0, 4275]], [[0, 0, 0, 0, 0, 769], [0, 0, 0, 0, 0, 5044], [0, 0, 0, 0, 0, 769], [0, 0, 0, 0, 0, 769]], [[0, 0, 0, 0, 0, 769], [0, 0, 0, 0, 0, 769], [0, 0, 0, 0, 0, 5044], [0, 0, 0, 0, 0, 769]], [[0, 0, 0, 0, 0, 769], [0, 0, 0, 0, 0, 769], [0, 0, 0, 0, 0, 769], [0, 0, 0, 0, 0, 5044]], [[0, 0, 0, 0, 0, 769], [0, 0, 0, 0, 0, 769], [0, 0, 0, 0, 0, 769], [0, 0, 0, 0, 0, 769]]]]]

/-- W(5) as a table. -/
def tab5 (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ) : ℕ :=
  match q with
  | none => ((LN5.getD (r 0).val []).getD (r 1).val []).getD c 0
  | some p => ((((LS5.getD (p 0).val []).getD (p 1).val []).getD (r 0).val []).getD (r 1).val []).getD c 0

/-- W(5) read at the renamed pair. -/
def tabc5 (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ) : ℕ :=
  match q with
  | none => tab5 none r c
  | some p => tab5 (some (ren c p r).1) (ren c p r).2 c

/-- W(6, none, r, c) for c <= 5, nested by the entries of r and then c. -/
def LN6 : List (List (List ℕ)) :=
  [[[1287, 1287, 5024, 14825, 29404, 29404], [745, 745, 745, 2170, 4275, 4275], [0, 0, 2170, 2170, 4275, 4275], [0, 0, 0, 4275, 4275, 4275], [0, 0, 0, 0, 4275, 4275]], [[0, 745, 745, 2170, 4275, 4275], [0, 5024, 5024, 14825, 29404, 29404], [0, 2170, 2170, 2170, 4275, 4275], [0, 0, 0, 4275, 4275, 4275], [0, 0, 0, 0, 4275, 4275]], [[0, 0, 2170, 2170, 4275, 4275], [0, 0, 2170, 2170, 4275, 4275], [0, 0, 14825, 14825, 29404, 29404], [0, 0, 4275, 4275, 4275, 4275], [0, 0, 0, 0, 4275, 4275]], [[0, 0, 0, 4275, 4275, 4275], [0, 0, 0, 4275, 4275, 4275], [0, 0, 0, 4275, 4275, 4275], [0, 0, 0, 29404, 29404, 29404], [0, 0, 0, 4275, 4275, 4275]], [[0, 0, 0, 0, 4275, 4275], [0, 0, 0, 0, 4275, 4275], [0, 0, 0, 0, 4275, 4275], [0, 0, 0, 0, 4275, 4275], [0, 0, 0, 0, 29404, 29404]]]

/-- W(6, some p, r, c) at the pairs (p, r) with p 0 = 0 and the values of p below c, nested by the entries of p, of r, and then c (0 elsewhere). -/
def LS6 : List (List (List (List (List ℕ)))) :=
  [[[[], [[], [0, 5024, 5024, 14825, 29404, 29404], [0, 2170, 2170, 2170, 4275, 4275], [0, 0, 0, 4275, 4275, 4275], [0, 0, 0, 0, 4275, 4275]], [[], [0, 0, 2170, 2170, 4275, 4275], [0, 0, 14825, 14825, 29404, 29404], [0, 0, 4275, 4275, 4275, 4275], [0, 0, 0, 0, 4275, 4275]], [[], [0, 0, 0, 4275, 4275, 4275], [0, 0, 0, 4275, 4275, 4275], [0, 0, 0, 29404, 29404, 29404], [0, 0, 0, 4275, 4275, 4275]], [[], [0, 0, 0, 0, 4275, 4275], [0, 0, 0, 0, 4275, 4275], [0, 0, 0, 0, 4275, 4275], [0, 0, 0, 0, 29404, 29404]]], [[[], [0, 0, 4279, 12655, 25129, 25129]], [[0, 0, 745, 2170, 4275, 4275], [], [0, 0, 2170, 2170, 4275, 4275], [0, 0, 0, 4275, 4275, 4275], [0, 0, 0, 0, 4275, 4275]], [[0, 0, 2170, 2170, 4275, 4275], [], [0, 0, 14825, 14825, 29404, 29404], [0, 0, 4275, 4275, 4275, 4275], [0, 0, 0, 0, 4275, 4275]], [[0, 0, 0, 4275, 4275, 4275], [], [0, 0, 0, 4275, 4275, 4275], [0, 0, 0, 29404, 29404, 29404], [0, 0, 0, 4275, 4275, 4275]], [[0, 0, 0, 0, 4275, 4275], [], [0, 0, 0, 0, 4275, 4275], [0, 0, 0, 0, 4275, 4275], [0, 0, 0, 0, 29404, 29404]]], [[[], [], [0, 0, 0, 12655, 25129, 25129]], [[0, 0, 0, 2170, 4275, 4275], [0, 0, 0, 14825, 29404, 29404], [], [0, 0, 0, 4275, 4275, 4275], [0, 0, 0, 0, 4275, 4275]], [[0, 0, 0, 2170, 4275, 4275], [0, 0, 0, 2170, 4275, 4275], [], [0, 0, 0, 4275, 4275, 4275], [0, 0, 0, 0, 4275, 4275]], [[0, 0, 0, 4275, 4275, 4275], [0, 0, 0, 4275, 4275, 4275], [], [0, 0, 0, 29404, 29404, 29404], [0, 0, 0, 4275, 4275, 4275]], [[0, 0, 0, 0, 4275, 4275], [0, 0, 0, 0, 4275, 4275], [], [0, 0, 0, 0, 4275, 4275], [0, 0, 0, 0, 29404, 29404]]], [[[], [], [], [0, 0, 0, 0, 25129, 25129]], [[0, 0, 0, 0, 4275, 4275], [0, 0, 0, 0, 29404, 29404], [0, 0, 0, 0, 4275, 4275], [], [0, 0, 0, 0, 4275, 4275]], [[0, 0, 0, 0, 4275, 4275], [0, 0, 0, 0, 4275, 4275], [0, 0, 0, 0, 29404, 29404], [], [0, 0, 0, 0, 4275, 4275]], [[0, 0, 0, 0, 4275, 4275], [0, 0, 0, 0, 4275, 4275], [0, 0, 0, 0, 4275, 4275], [], [0, 0, 0, 0, 4275, 4275]], [[0, 0, 0, 0, 4275, 4275], [0, 0, 0, 0, 4275, 4275], [0, 0, 0, 0, 4275, 4275], [], [0, 0, 0, 0, 29404, 29404]]], [[[], [], [], [], [0, 0, 0, 0, 0, 25129]], [[0, 0, 0, 0, 0, 4275], [0, 0, 0, 0, 0, 29404], [0, 0, 0, 0, 0, 4275], [0, 0, 0, 0, 0, 4275]], [[0, 0, 0, 0, 0, 4275], [0, 0, 0, 0, 0, 4275], [0, 0, 0, 0, 0, 29404], [0, 0, 0, 0, 0, 4275]], [[0, 0, 0, 0, 0, 4275], [0, 0, 0, 0, 0, 4275], [0, 0, 0, 0, 0, 4275], [0, 0, 0, 0, 0, 29404]], [[0, 0, 0, 0, 0, 4275], [0, 0, 0, 0, 0, 4275], [0, 0, 0, 0, 0, 4275], [0, 0, 0, 0, 0, 4275]]]]]

/-- W(6) as a table. -/
def tab6 (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ) : ℕ :=
  match q with
  | none => ((LN6.getD (r 0).val []).getD (r 1).val []).getD c 0
  | some p => ((((LS6.getD (p 0).val []).getD (p 1).val []).getD (r 0).val []).getD (r 1).val []).getD c 0

/-- W(6) read at the renamed pair. -/
def tabc6 (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ) : ℕ :=
  match q with
  | none => tab6 none r c
  | some p => tab6 (some (ren c p r).1) (ren c p r).2 c

/-- W(7, none, r, c) for c <= 5, nested by the entries of r and then c. -/
def LN7 : List (List (List ℕ)) :=
  [[[7194, 7194, 28464, 84769, 168916, 168916], [4279, 4279, 4279, 12655, 25129, 25129], [0, 0, 12655, 12655, 25129, 25129], [0, 0, 0, 25129, 25129, 25129], [0, 0, 0, 0, 25129, 25129]], [[0, 4279, 4279, 12655, 25129, 25129], [0, 28464, 28464, 84769, 168916, 168916], [0, 12655, 12655, 12655, 25129, 25129], [0, 0, 0, 25129, 25129, 25129], [0, 0, 0, 0, 25129, 25129]], [[0, 0, 12655, 12655, 25129, 25129], [0, 0, 12655, 12655, 25129, 25129], [0, 0, 84769, 84769, 168916, 168916], [0, 0, 25129, 25129, 25129, 25129], [0, 0, 0, 0, 25129, 25129]], [[0, 0, 0, 25129, 25129, 25129], [0, 0, 0, 25129, 25129, 25129], [0, 0, 0, 25129, 25129, 25129], [0, 0, 0, 168916, 168916, 168916], [0, 0, 0, 25129, 25129, 25129]], [[0, 0, 0, 0, 25129, 25129], [0, 0, 0, 0, 25129, 25129], [0, 0, 0, 0, 25129, 25129], [0, 0, 0, 0, 25129, 25129], [0, 0, 0, 0, 168916, 168916]]]

/-- W(7, some p, r, c) at the pairs (p, r) with p 0 = 0 and the values of p below c, nested by the entries of p, of r, and then c (0 elsewhere). -/
def LS7 : List (List (List (List (List ℕ)))) :=
  [[[[], [[], [0, 28464, 28464, 84769, 168916, 168916], [0, 12655, 12655, 12655, 25129, 25129], [0, 0, 0, 25129, 25129, 25129], [0, 0, 0, 0, 25129, 25129]], [[], [0, 0, 12655, 12655, 25129, 25129], [0, 0, 84769, 84769, 168916, 168916], [0, 0, 25129, 25129, 25129, 25129], [0, 0, 0, 0, 25129, 25129]], [[], [0, 0, 0, 25129, 25129, 25129], [0, 0, 0, 25129, 25129, 25129], [0, 0, 0, 168916, 168916, 168916], [0, 0, 0, 25129, 25129, 25129]], [[], [0, 0, 0, 0, 25129, 25129], [0, 0, 0, 0, 25129, 25129], [0, 0, 0, 0, 25129, 25129], [0, 0, 0, 0, 168916, 168916]]], [[[], [0, 0, 24185, 72114, 143787, 143787]], [[0, 0, 4279, 12655, 25129, 25129], [], [0, 0, 12655, 12655, 25129, 25129], [0, 0, 0, 25129, 25129, 25129], [0, 0, 0, 0, 25129, 25129]], [[0, 0, 12655, 12655, 25129, 25129], [], [0, 0, 84769, 84769, 168916, 168916], [0, 0, 25129, 25129, 25129, 25129], [0, 0, 0, 0, 25129, 25129]], [[0, 0, 0, 25129, 25129, 25129], [], [0, 0, 0, 25129, 25129, 25129], [0, 0, 0, 168916, 168916, 168916], [0, 0, 0, 25129, 25129, 25129]], [[0, 0, 0, 0, 25129, 25129], [], [0, 0, 0, 0, 25129, 25129], [0, 0, 0, 0, 25129, 25129], [0, 0, 0, 0, 168916, 168916]]], [[[], [], [0, 0, 0, 72114, 143787, 143787]], [[0, 0, 0, 12655, 25129, 25129], [0, 0, 0, 84769, 168916, 168916], [], [0, 0, 0, 25129, 25129, 25129], [0, 0, 0, 0, 25129, 25129]], [[0, 0, 0, 12655, 25129, 25129], [0, 0, 0, 12655, 25129, 25129], [], [0, 0, 0, 25129, 25129, 25129], [0, 0, 0, 0, 25129, 25129]], [[0, 0, 0, 25129, 25129, 25129], [0, 0, 0, 25129, 25129, 25129], [], [0, 0, 0, 168916, 168916, 168916], [0, 0, 0, 25129, 25129, 25129]], [[0, 0, 0, 0, 25129, 25129], [0, 0, 0, 0, 25129, 25129], [], [0, 0, 0, 0, 25129, 25129], [0, 0, 0, 0, 168916, 168916]]], [[[], [], [], [0, 0, 0, 0, 143787, 143787]], [[0, 0, 0, 0, 25129, 25129], [0, 0, 0, 0, 168916, 168916], [0, 0, 0, 0, 25129, 25129], [], [0, 0, 0, 0, 25129, 25129]], [[0, 0, 0, 0, 25129, 25129], [0, 0, 0, 0, 25129, 25129], [0, 0, 0, 0, 168916, 168916], [], [0, 0, 0, 0, 25129, 25129]], [[0, 0, 0, 0, 25129, 25129], [0, 0, 0, 0, 25129, 25129], [0, 0, 0, 0, 25129, 25129], [], [0, 0, 0, 0, 25129, 25129]], [[0, 0, 0, 0, 25129, 25129], [0, 0, 0, 0, 25129, 25129], [0, 0, 0, 0, 25129, 25129], [], [0, 0, 0, 0, 168916, 168916]]], [[[], [], [], [], [0, 0, 0, 0, 0, 143787]], [[0, 0, 0, 0, 0, 25129], [0, 0, 0, 0, 0, 168916], [0, 0, 0, 0, 0, 25129], [0, 0, 0, 0, 0, 25129]], [[0, 0, 0, 0, 0, 25129], [0, 0, 0, 0, 0, 25129], [0, 0, 0, 0, 0, 168916], [0, 0, 0, 0, 0, 25129]], [[0, 0, 0, 0, 0, 25129], [0, 0, 0, 0, 0, 25129], [0, 0, 0, 0, 0, 25129], [0, 0, 0, 0, 0, 168916]], [[0, 0, 0, 0, 0, 25129], [0, 0, 0, 0, 0, 25129], [0, 0, 0, 0, 0, 25129], [0, 0, 0, 0, 0, 25129]]]]]

/-- W(7) as a table. -/
def tab7 (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ) : ℕ :=
  match q with
  | none => ((LN7.getD (r 0).val []).getD (r 1).val []).getD c 0
  | some p => ((((LS7.getD (p 0).val []).getD (p 1).val []).getD (r 0).val []).getD (r 1).val []).getD c 0

/-- W(7) read at the renamed pair. -/
def tabc7 (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ) : ℕ :=
  match q with
  | none => tab7 none r c
  | some p => tab7 (some (ren c p r).1) (ren c p r).2 c

/-- W(8, none, r, c) for c <= 5, nested by the entries of r and then c. -/
def LN8 : List (List (List ℕ)) :=
  [[[41119, 41119, 163672, 489409, 977212, 977212], [24185, 24185, 24185, 72114, 143787, 143787], [0, 0, 72114, 72114, 143787, 143787], [0, 0, 0, 143787, 143787, 143787], [0, 0, 0, 0, 143787, 143787]], [[0, 24185, 24185, 72114, 143787, 143787], [0, 163672, 163672, 489409, 977212, 977212], [0, 72114, 72114, 72114, 143787, 143787], [0, 0, 0, 143787, 143787, 143787], [0, 0, 0, 0, 143787, 143787]], [[0, 0, 72114, 72114, 143787, 143787], [0, 0, 72114, 72114, 143787, 143787], [0, 0, 489409, 489409, 977212, 977212], [0, 0, 143787, 143787, 143787, 143787], [0, 0, 0, 0, 143787, 143787]], [[0, 0, 0, 143787, 143787, 143787], [0, 0, 0, 143787, 143787, 143787], [0, 0, 0, 143787, 143787, 143787], [0, 0, 0, 977212, 977212, 977212], [0, 0, 0, 143787, 143787, 143787]], [[0, 0, 0, 0, 143787, 143787], [0, 0, 0, 0, 143787, 143787], [0, 0, 0, 0, 143787, 143787], [0, 0, 0, 0, 143787, 143787], [0, 0, 0, 0, 977212, 977212]]]

/-- W(8, some p, r, c) at the pairs (p, r) with p 0 = 0 and the values of p below c, nested by the entries of p, of r, and then c (0 elsewhere). -/
def LS8 : List (List (List (List (List ℕ)))) :=
  [[[[], [[], [0, 163672, 163672, 489409, 977212, 977212], [0, 72114, 72114, 72114, 143787, 143787], [0, 0, 0, 143787, 143787, 143787], [0, 0, 0, 0, 143787, 143787]], [[], [0, 0, 72114, 72114, 143787, 143787], [0, 0, 489409, 489409, 977212, 977212], [0, 0, 143787, 143787, 143787, 143787], [0, 0, 0, 0, 143787, 143787]], [[], [0, 0, 0, 143787, 143787, 143787], [0, 0, 0, 143787, 143787, 143787], [0, 0, 0, 977212, 977212, 977212], [0, 0, 0, 143787, 143787, 143787]], [[], [0, 0, 0, 0, 143787, 143787], [0, 0, 0, 0, 143787, 143787], [0, 0, 0, 0, 143787, 143787], [0, 0, 0, 0, 977212, 977212]]], [[[], [0, 0, 139487, 417295, 833425, 833425]], [[0, 0, 24185, 72114, 143787, 143787], [], [0, 0, 72114, 72114, 143787, 143787], [0, 0, 0, 143787, 143787, 143787], [0, 0, 0, 0, 143787, 143787]], [[0, 0, 72114, 72114, 143787, 143787], [], [0, 0, 489409, 489409, 977212, 977212], [0, 0, 143787, 143787, 143787, 143787], [0, 0, 0, 0, 143787, 143787]], [[0, 0, 0, 143787, 143787, 143787], [], [0, 0, 0, 143787, 143787, 143787], [0, 0, 0, 977212, 977212, 977212], [0, 0, 0, 143787, 143787, 143787]], [[0, 0, 0, 0, 143787, 143787], [], [0, 0, 0, 0, 143787, 143787], [0, 0, 0, 0, 143787, 143787], [0, 0, 0, 0, 977212, 977212]]], [[[], [], [0, 0, 0, 417295, 833425, 833425]], [[0, 0, 0, 72114, 143787, 143787], [0, 0, 0, 489409, 977212, 977212], [], [0, 0, 0, 143787, 143787, 143787], [0, 0, 0, 0, 143787, 143787]], [[0, 0, 0, 72114, 143787, 143787], [0, 0, 0, 72114, 143787, 143787], [], [0, 0, 0, 143787, 143787, 143787], [0, 0, 0, 0, 143787, 143787]], [[0, 0, 0, 143787, 143787, 143787], [0, 0, 0, 143787, 143787, 143787], [], [0, 0, 0, 977212, 977212, 977212], [0, 0, 0, 143787, 143787, 143787]], [[0, 0, 0, 0, 143787, 143787], [0, 0, 0, 0, 143787, 143787], [], [0, 0, 0, 0, 143787, 143787], [0, 0, 0, 0, 977212, 977212]]], [[[], [], [], [0, 0, 0, 0, 833425, 833425]], [[0, 0, 0, 0, 143787, 143787], [0, 0, 0, 0, 977212, 977212], [0, 0, 0, 0, 143787, 143787], [], [0, 0, 0, 0, 143787, 143787]], [[0, 0, 0, 0, 143787, 143787], [0, 0, 0, 0, 143787, 143787], [0, 0, 0, 0, 977212, 977212], [], [0, 0, 0, 0, 143787, 143787]], [[0, 0, 0, 0, 143787, 143787], [0, 0, 0, 0, 143787, 143787], [0, 0, 0, 0, 143787, 143787], [], [0, 0, 0, 0, 143787, 143787]], [[0, 0, 0, 0, 143787, 143787], [0, 0, 0, 0, 143787, 143787], [0, 0, 0, 0, 143787, 143787], [], [0, 0, 0, 0, 977212, 977212]]], [[[], [], [], [], [0, 0, 0, 0, 0, 833425]], [[0, 0, 0, 0, 0, 143787], [0, 0, 0, 0, 0, 977212], [0, 0, 0, 0, 0, 143787], [0, 0, 0, 0, 0, 143787]], [[0, 0, 0, 0, 0, 143787], [0, 0, 0, 0, 0, 143787], [0, 0, 0, 0, 0, 977212], [0, 0, 0, 0, 0, 143787]], [[0, 0, 0, 0, 0, 143787], [0, 0, 0, 0, 0, 143787], [0, 0, 0, 0, 0, 143787], [0, 0, 0, 0, 0, 977212]], [[0, 0, 0, 0, 0, 143787], [0, 0, 0, 0, 0, 143787], [0, 0, 0, 0, 0, 143787], [0, 0, 0, 0, 0, 143787]]]]]

/-- W(8) as a table. -/
def tab8 (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ) : ℕ :=
  match q with
  | none => ((LN8.getD (r 0).val []).getD (r 1).val []).getD c 0
  | some p => ((((LS8.getD (p 0).val []).getD (p 1).val []).getD (r 0).val []).getD (r 1).val []).getD c 0

/-- W(8) read at the renamed pair. -/
def tabc8 (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ) : ℕ :=
  match q with
  | none => tab8 none r c
  | some p => tab8 (some (ren c p r).1) (ren c p r).2 c

/-- W(9, none, r, c) for c <= 5, nested by the entries of r and then c. -/
def LN9 : List (List (List ℕ)) :=
  [[[235786, 235786, 941096, 2819193, 5634292, 5634292], [139487, 139487, 139487, 417295, 833425, 833425], [0, 0, 417295, 417295, 833425, 833425], [0, 0, 0, 833425, 833425, 833425], [0, 0, 0, 0, 833425, 833425]], [[0, 139487, 139487, 417295, 833425, 833425], [0, 941096, 941096, 2819193, 5634292, 5634292], [0, 417295, 417295, 417295, 833425, 833425], [0, 0, 0, 833425, 833425, 833425], [0, 0, 0, 0, 833425, 833425]], [[0, 0, 417295, 417295, 833425, 833425], [0, 0, 417295, 417295, 833425, 833425], [0, 0, 2819193, 2819193, 5634292, 5634292], [0, 0, 833425, 833425, 833425, 833425], [0, 0, 0, 0, 833425, 833425]], [[0, 0, 0, 833425, 833425, 833425], [0, 0, 0, 833425, 833425, 833425], [0, 0, 0, 833425, 833425, 833425], [0, 0, 0, 5634292, 5634292, 5634292], [0, 0, 0, 833425, 833425, 833425]], [[0, 0, 0, 0, 833425, 833425], [0, 0, 0, 0, 833425, 833425], [0, 0, 0, 0, 833425, 833425], [0, 0, 0, 0, 833425, 833425], [0, 0, 0, 0, 5634292, 5634292]]]

/-- W(9, some p, r, c) at the pairs (p, r) with p 0 = 0 and the values of p below c, nested by the entries of p, of r, and then c (0 elsewhere). -/
def LS9 : List (List (List (List (List ℕ)))) :=
  [[[[], [[], [0, 941096, 941096, 2819193, 5634292, 5634292], [0, 417295, 417295, 417295, 833425, 833425], [0, 0, 0, 833425, 833425, 833425], [0, 0, 0, 0, 833425, 833425]], [[], [0, 0, 417295, 417295, 833425, 833425], [0, 0, 2819193, 2819193, 5634292, 5634292], [0, 0, 833425, 833425, 833425, 833425], [0, 0, 0, 0, 833425, 833425]], [[], [0, 0, 0, 833425, 833425, 833425], [0, 0, 0, 833425, 833425, 833425], [0, 0, 0, 5634292, 5634292, 5634292], [0, 0, 0, 833425, 833425, 833425]], [[], [0, 0, 0, 0, 833425, 833425], [0, 0, 0, 0, 833425, 833425], [0, 0, 0, 0, 833425, 833425], [0, 0, 0, 0, 5634292, 5634292]]], [[[], [0, 0, 801609, 2401898, 4800867, 4800867]], [[0, 0, 139487, 417295, 833425, 833425], [], [0, 0, 417295, 417295, 833425, 833425], [0, 0, 0, 833425, 833425, 833425], [0, 0, 0, 0, 833425, 833425]], [[0, 0, 417295, 417295, 833425, 833425], [], [0, 0, 2819193, 2819193, 5634292, 5634292], [0, 0, 833425, 833425, 833425, 833425], [0, 0, 0, 0, 833425, 833425]], [[0, 0, 0, 833425, 833425, 833425], [], [0, 0, 0, 833425, 833425, 833425], [0, 0, 0, 5634292, 5634292, 5634292], [0, 0, 0, 833425, 833425, 833425]], [[0, 0, 0, 0, 833425, 833425], [], [0, 0, 0, 0, 833425, 833425], [0, 0, 0, 0, 833425, 833425], [0, 0, 0, 0, 5634292, 5634292]]], [[[], [], [0, 0, 0, 2401898, 4800867, 4800867]], [[0, 0, 0, 417295, 833425, 833425], [0, 0, 0, 2819193, 5634292, 5634292], [], [0, 0, 0, 833425, 833425, 833425], [0, 0, 0, 0, 833425, 833425]], [[0, 0, 0, 417295, 833425, 833425], [0, 0, 0, 417295, 833425, 833425], [], [0, 0, 0, 833425, 833425, 833425], [0, 0, 0, 0, 833425, 833425]], [[0, 0, 0, 833425, 833425, 833425], [0, 0, 0, 833425, 833425, 833425], [], [0, 0, 0, 5634292, 5634292, 5634292], [0, 0, 0, 833425, 833425, 833425]], [[0, 0, 0, 0, 833425, 833425], [0, 0, 0, 0, 833425, 833425], [], [0, 0, 0, 0, 833425, 833425], [0, 0, 0, 0, 5634292, 5634292]]], [[[], [], [], [0, 0, 0, 0, 4800867, 4800867]], [[0, 0, 0, 0, 833425, 833425], [0, 0, 0, 0, 5634292, 5634292], [0, 0, 0, 0, 833425, 833425], [], [0, 0, 0, 0, 833425, 833425]], [[0, 0, 0, 0, 833425, 833425], [0, 0, 0, 0, 833425, 833425], [0, 0, 0, 0, 5634292, 5634292], [], [0, 0, 0, 0, 833425, 833425]], [[0, 0, 0, 0, 833425, 833425], [0, 0, 0, 0, 833425, 833425], [0, 0, 0, 0, 833425, 833425], [], [0, 0, 0, 0, 833425, 833425]], [[0, 0, 0, 0, 833425, 833425], [0, 0, 0, 0, 833425, 833425], [0, 0, 0, 0, 833425, 833425], [], [0, 0, 0, 0, 5634292, 5634292]]], [[[], [], [], [], [0, 0, 0, 0, 0, 4800867]], [[0, 0, 0, 0, 0, 833425], [0, 0, 0, 0, 0, 5634292], [0, 0, 0, 0, 0, 833425], [0, 0, 0, 0, 0, 833425]], [[0, 0, 0, 0, 0, 833425], [0, 0, 0, 0, 0, 833425], [0, 0, 0, 0, 0, 5634292], [0, 0, 0, 0, 0, 833425]], [[0, 0, 0, 0, 0, 833425], [0, 0, 0, 0, 0, 833425], [0, 0, 0, 0, 0, 833425], [0, 0, 0, 0, 0, 5634292]], [[0, 0, 0, 0, 0, 833425], [0, 0, 0, 0, 0, 833425], [0, 0, 0, 0, 0, 833425], [0, 0, 0, 0, 0, 833425]]]]]

/-- W(9) as a table. -/
def tab9 (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ) : ℕ :=
  match q with
  | none => ((LN9.getD (r 0).val []).getD (r 1).val []).getD c 0
  | some p => ((((LS9.getD (p 0).val []).getD (p 1).val []).getD (r 0).val []).getD (r 1).val []).getD c 0

/-- W(9) read at the renamed pair. -/
def tabc9 (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ) : ℕ :=
  match q with
  | none => tab9 none r c
  | some p => tab9 (some (ren c p r).1) (ren c p r).2 c

/-- W(10, none, r, c) for c <= 5, nested by the entries of r and then c. -/
def LN10 : List (List (List ℕ)) :=
  [[[1358391, 1358391, 5428304, 16274393, 32538268, 32538268], [801609, 801609, 801609, 2401898, 4800867, 4800867], [0, 0, 2401898, 2401898, 4800867, 4800867], [0, 0, 0, 4800867, 4800867, 4800867], [0, 0, 0, 0, 4800867, 4800867]], [[0, 801609, 801609, 2401898, 4800867, 4800867], [0, 5428304, 5428304, 16274393, 32538268, 32538268], [0, 2401898, 2401898, 2401898, 4800867, 4800867], [0, 0, 0, 4800867, 4800867, 4800867], [0, 0, 0, 0, 4800867, 4800867]], [[0, 0, 2401898, 2401898, 4800867, 4800867], [0, 0, 2401898, 2401898, 4800867, 4800867], [0, 0, 16274393, 16274393, 32538268, 32538268], [0, 0, 4800867, 4800867, 4800867, 4800867], [0, 0, 0, 0, 4800867, 4800867]], [[0, 0, 0, 4800867, 4800867, 4800867], [0, 0, 0, 4800867, 4800867, 4800867], [0, 0, 0, 4800867, 4800867, 4800867], [0, 0, 0, 32538268, 32538268, 32538268], [0, 0, 0, 4800867, 4800867, 4800867]], [[0, 0, 0, 0, 4800867, 4800867], [0, 0, 0, 0, 4800867, 4800867], [0, 0, 0, 0, 4800867, 4800867], [0, 0, 0, 0, 4800867, 4800867], [0, 0, 0, 0, 32538268, 32538268]]]

/-- W(10, some p, r, c) at the pairs (p, r) with p 0 = 0 and the values of p below c, nested by the entries of p, of r, and then c (0 elsewhere). -/
def LS10 : List (List (List (List (List ℕ)))) :=
  [[[[], [[], [0, 5428304, 5428304, 16274393, 32538268, 32538268], [0, 2401898, 2401898, 2401898, 4800867, 4800867], [0, 0, 0, 4800867, 4800867, 4800867], [0, 0, 0, 0, 4800867, 4800867]], [[], [0, 0, 2401898, 2401898, 4800867, 4800867], [0, 0, 16274393, 16274393, 32538268, 32538268], [0, 0, 4800867, 4800867, 4800867, 4800867], [0, 0, 0, 0, 4800867, 4800867]], [[], [0, 0, 0, 4800867, 4800867, 4800867], [0, 0, 0, 4800867, 4800867, 4800867], [0, 0, 0, 32538268, 32538268, 32538268], [0, 0, 0, 4800867, 4800867, 4800867]], [[], [0, 0, 0, 0, 4800867, 4800867], [0, 0, 0, 0, 4800867, 4800867], [0, 0, 0, 0, 4800867, 4800867], [0, 0, 0, 0, 32538268, 32538268]]], [[[], [0, 0, 4626695, 13872495, 27737401, 27737401]], [[0, 0, 801609, 2401898, 4800867, 4800867], [], [0, 0, 2401898, 2401898, 4800867, 4800867], [0, 0, 0, 4800867, 4800867, 4800867], [0, 0, 0, 0, 4800867, 4800867]], [[0, 0, 2401898, 2401898, 4800867, 4800867], [], [0, 0, 16274393, 16274393, 32538268, 32538268], [0, 0, 4800867, 4800867, 4800867, 4800867], [0, 0, 0, 0, 4800867, 4800867]], [[0, 0, 0, 4800867, 4800867, 4800867], [], [0, 0, 0, 4800867, 4800867, 4800867], [0, 0, 0, 32538268, 32538268, 32538268], [0, 0, 0, 4800867, 4800867, 4800867]], [[0, 0, 0, 0, 4800867, 4800867], [], [0, 0, 0, 0, 4800867, 4800867], [0, 0, 0, 0, 4800867, 4800867], [0, 0, 0, 0, 32538268, 32538268]]], [[[], [], [0, 0, 0, 13872495, 27737401, 27737401]], [[0, 0, 0, 2401898, 4800867, 4800867], [0, 0, 0, 16274393, 32538268, 32538268], [], [0, 0, 0, 4800867, 4800867, 4800867], [0, 0, 0, 0, 4800867, 4800867]], [[0, 0, 0, 2401898, 4800867, 4800867], [0, 0, 0, 2401898, 4800867, 4800867], [], [0, 0, 0, 4800867, 4800867, 4800867], [0, 0, 0, 0, 4800867, 4800867]], [[0, 0, 0, 4800867, 4800867, 4800867], [0, 0, 0, 4800867, 4800867, 4800867], [], [0, 0, 0, 32538268, 32538268, 32538268], [0, 0, 0, 4800867, 4800867, 4800867]], [[0, 0, 0, 0, 4800867, 4800867], [0, 0, 0, 0, 4800867, 4800867], [], [0, 0, 0, 0, 4800867, 4800867], [0, 0, 0, 0, 32538268, 32538268]]], [[[], [], [], [0, 0, 0, 0, 27737401, 27737401]], [[0, 0, 0, 0, 4800867, 4800867], [0, 0, 0, 0, 32538268, 32538268], [0, 0, 0, 0, 4800867, 4800867], [], [0, 0, 0, 0, 4800867, 4800867]], [[0, 0, 0, 0, 4800867, 4800867], [0, 0, 0, 0, 4800867, 4800867], [0, 0, 0, 0, 32538268, 32538268], [], [0, 0, 0, 0, 4800867, 4800867]], [[0, 0, 0, 0, 4800867, 4800867], [0, 0, 0, 0, 4800867, 4800867], [0, 0, 0, 0, 4800867, 4800867], [], [0, 0, 0, 0, 4800867, 4800867]], [[0, 0, 0, 0, 4800867, 4800867], [0, 0, 0, 0, 4800867, 4800867], [0, 0, 0, 0, 4800867, 4800867], [], [0, 0, 0, 0, 32538268, 32538268]]], [[[], [], [], [], [0, 0, 0, 0, 0, 27737401]], [[0, 0, 0, 0, 0, 4800867], [0, 0, 0, 0, 0, 32538268], [0, 0, 0, 0, 0, 4800867], [0, 0, 0, 0, 0, 4800867]], [[0, 0, 0, 0, 0, 4800867], [0, 0, 0, 0, 0, 4800867], [0, 0, 0, 0, 0, 32538268], [0, 0, 0, 0, 0, 4800867]], [[0, 0, 0, 0, 0, 4800867], [0, 0, 0, 0, 0, 4800867], [0, 0, 0, 0, 0, 4800867], [0, 0, 0, 0, 0, 32538268]], [[0, 0, 0, 0, 0, 4800867], [0, 0, 0, 0, 0, 4800867], [0, 0, 0, 0, 0, 4800867], [0, 0, 0, 0, 0, 4800867]]]]]

/-- W(10) as a table. -/
def tab10 (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ) : ℕ :=
  match q with
  | none => ((LN10.getD (r 0).val []).getD (r 1).val []).getD c 0
  | some p => ((((LS10.getD (p 0).val []).getD (p 1).val []).getD (r 0).val []).getD (r 1).val []).getD c 0

/-- W(10) read at the renamed pair. -/
def tabc10 (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ) : ℕ :=
  match q with
  | none => tab10 none r c
  | some p => tab10 (some (ren c p r).1) (ren c p r).2 c

lemma checkN1 : ∀ c : Fin 6, ∀ y1 y2 : Fin 5, 
    T W0f none ![y1, y2] c.val = tab1 none ![y1, y2] c.val := by
  intro c
  fin_cases c <;> decide +kernel

lemma checkS1 : ∀ c : Fin 6, ∀ p1 p2 : Fin 5, ∀ y1 y2 : Fin 5,  (p1.val < c.val ∧ p2.val < c.val) → p1.val = 0 →
    T W0f (some ![p1, p2]) ![y1, y2] c.val = tab1 (some ![p1, p2]) ![y1, y2] c.val := by
  intro c
  fin_cases c <;> decide +kernel

lemma checkN2 : ∀ c : Fin 6, ∀ y1 y2 : Fin 5, 
    T tabc1 none ![y1, y2] c.val = tab2 none ![y1, y2] c.val := by
  intro c
  fin_cases c <;> decide +kernel

lemma checkS2 : ∀ c : Fin 6, ∀ p1 p2 : Fin 5, ∀ y1 y2 : Fin 5,  (p1.val < c.val ∧ p2.val < c.val) → p1.val = 0 →
    T tabc1 (some ![p1, p2]) ![y1, y2] c.val = tab2 (some ![p1, p2]) ![y1, y2] c.val := by
  intro c
  fin_cases c <;> decide +kernel

lemma checkN3 : ∀ c : Fin 6, ∀ y1 y2 : Fin 5, 
    T tabc2 none ![y1, y2] c.val = tab3 none ![y1, y2] c.val := by
  intro c
  fin_cases c <;> decide +kernel

lemma checkS3 : ∀ c : Fin 6, ∀ p1 p2 : Fin 5, ∀ y1 y2 : Fin 5,  (p1.val < c.val ∧ p2.val < c.val) → p1.val = 0 →
    T tabc2 (some ![p1, p2]) ![y1, y2] c.val = tab3 (some ![p1, p2]) ![y1, y2] c.val := by
  intro c
  fin_cases c <;> decide +kernel

lemma checkN4 : ∀ c : Fin 6, ∀ y1 y2 : Fin 5, 
    T tabc3 none ![y1, y2] c.val = tab4 none ![y1, y2] c.val := by
  intro c
  fin_cases c <;> decide +kernel

lemma checkS4 : ∀ c : Fin 6, ∀ p1 p2 : Fin 5, ∀ y1 y2 : Fin 5,  (p1.val < c.val ∧ p2.val < c.val) → p1.val = 0 →
    T tabc3 (some ![p1, p2]) ![y1, y2] c.val = tab4 (some ![p1, p2]) ![y1, y2] c.val := by
  intro c
  fin_cases c <;> decide +kernel

lemma checkN5 : ∀ c : Fin 6, ∀ y1 y2 : Fin 5, 
    T tabc4 none ![y1, y2] c.val = tab5 none ![y1, y2] c.val := by
  intro c
  fin_cases c <;> decide +kernel

lemma checkS5 : ∀ c : Fin 6, ∀ p1 p2 : Fin 5, ∀ y1 y2 : Fin 5,  (p1.val < c.val ∧ p2.val < c.val) → p1.val = 0 →
    T tabc4 (some ![p1, p2]) ![y1, y2] c.val = tab5 (some ![p1, p2]) ![y1, y2] c.val := by
  intro c
  fin_cases c <;> decide +kernel

lemma checkN6 : ∀ c : Fin 6, ∀ y1 y2 : Fin 5, 
    T tabc5 none ![y1, y2] c.val = tab6 none ![y1, y2] c.val := by
  intro c
  fin_cases c <;> decide +kernel

lemma checkS6 : ∀ c : Fin 6, ∀ p1 p2 : Fin 5, ∀ y1 y2 : Fin 5,  (p1.val < c.val ∧ p2.val < c.val) → p1.val = 0 →
    T tabc5 (some ![p1, p2]) ![y1, y2] c.val = tab6 (some ![p1, p2]) ![y1, y2] c.val := by
  intro c
  fin_cases c <;> decide +kernel

lemma checkN7 : ∀ c : Fin 6, ∀ y1 y2 : Fin 5, 
    T tabc6 none ![y1, y2] c.val = tab7 none ![y1, y2] c.val := by
  intro c
  fin_cases c <;> decide +kernel

lemma checkS7 : ∀ c : Fin 6, ∀ p1 p2 : Fin 5, ∀ y1 y2 : Fin 5,  (p1.val < c.val ∧ p2.val < c.val) → p1.val = 0 →
    T tabc6 (some ![p1, p2]) ![y1, y2] c.val = tab7 (some ![p1, p2]) ![y1, y2] c.val := by
  intro c
  fin_cases c <;> decide +kernel

lemma checkN8 : ∀ c : Fin 6, ∀ y1 y2 : Fin 5, 
    T tabc7 none ![y1, y2] c.val = tab8 none ![y1, y2] c.val := by
  intro c
  fin_cases c <;> decide +kernel

lemma checkS8 : ∀ c : Fin 6, ∀ p1 p2 : Fin 5, ∀ y1 y2 : Fin 5,  (p1.val < c.val ∧ p2.val < c.val) → p1.val = 0 →
    T tabc7 (some ![p1, p2]) ![y1, y2] c.val = tab8 (some ![p1, p2]) ![y1, y2] c.val := by
  intro c
  fin_cases c <;> decide +kernel

lemma checkN9 : ∀ c : Fin 6, ∀ y1 y2 : Fin 5, 
    T tabc8 none ![y1, y2] c.val = tab9 none ![y1, y2] c.val := by
  intro c
  fin_cases c <;> decide +kernel

lemma checkS9 : ∀ c : Fin 6, ∀ p1 p2 : Fin 5, ∀ y1 y2 : Fin 5,  (p1.val < c.val ∧ p2.val < c.val) → p1.val = 0 →
    T tabc8 (some ![p1, p2]) ![y1, y2] c.val = tab9 (some ![p1, p2]) ![y1, y2] c.val := by
  intro c
  fin_cases c <;> decide +kernel

lemma checkN10 : ∀ c : Fin 6, ∀ y1 y2 : Fin 5, 
    T tabc9 none ![y1, y2] c.val = tab10 none ![y1, y2] c.val := by
  intro c
  fin_cases c <;> decide +kernel

lemma checkS10 : ∀ c : Fin 6, ∀ p1 p2 : Fin 5, ∀ y1 y2 : Fin 5,  (p1.val < c.val ∧ p2.val < c.val) → p1.val = 0 →
    T tabc9 (some ![p1, p2]) ![y1, y2] c.val = tab10 (some ![p1, p2]) ![y1, y2] c.val := by
  intro c
  fin_cases c <;> decide +kernel

lemma checkN_rel : ∀ c : Fin 6, ∀ y1 y2 : Fin 5, 
    T tabc10 none ![y1, y2] c.val + 691 * tabc7 none ![y1, y2] c.val + 7056 * tabc3 none ![y1, y2] c.val =
      51 * tabc9 none ![y1, y2] c.val + 3601 * tabc5 none ![y1, y2] c.val + 4096 * tabc1 none ![y1, y2] c.val := by
  intro c
  fin_cases c <;> decide +kernel

lemma checkS_rel : ∀ c : Fin 6, ∀ p1 p2 : Fin 5, ∀ y1 y2 : Fin 5,  (p1.val < c.val ∧ p2.val < c.val) → p1.val = 0 →
    T tabc10 (some ![p1, p2]) ![y1, y2] c.val + 691 * tabc7 (some ![p1, p2]) ![y1, y2] c.val + 7056 * tabc3 (some ![p1, p2]) ![y1, y2] c.val =
      51 * tabc9 (some ![p1, p2]) ![y1, y2] c.val + 3601 * tabc5 (some ![p1, p2]) ![y1, y2] c.val + 4096 * tabc1 (some ![p1, p2]) ![y1, y2] c.val := by
  intro c
  fin_cases c <;> decide +kernel

lemma W_1 (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ) (hc : c ≤ 5)
    (hq : ∀ p, q = some p → ∀ j, (p j).val < c) :
    W 1 q r c = tabc1 q r c := by
  rcases q with _ | p
  · rw [W_succT _ none r c hc,
      T_congr _ W0f none r c (fun s => W_zero' _ s _ (newcB_le c hc r))]
    rw [row_eta r]
    exact checkN1 ⟨c, by omega⟩ (r 0) (r 1)
  · have hp := hq p rfl
    have h0 := ren_zero c p r (hp 0)
    have hlt := ren_lt c p r hp
    rw [← W_ren 1 c p r]
    show W 1 (some (ren c p r).1) (ren c p r).2 c = tab1 (some (ren c p r).1) (ren c p r).2 c
    generalize ren c p r = x at h0 hlt ⊢
    rw [W_succT _ (some x.1) x.2 c hc,
      T_congr _ W0f (some x.1) x.2 c (fun s => W_zero' _ s _ (newcB_le c hc x.2))]
    rw [row_eta x.1, row_eta x.2]
    exact checkS1 ⟨c, by omega⟩ (x.1 0) (x.1 1) (x.2 0) (x.2 1) ⟨hlt 0, hlt 1⟩ (congrArg Fin.val h0)

lemma W_2 (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ) (hc : c ≤ 5)
    (hq : ∀ p, q = some p → ∀ j, (p j).val < c) :
    W 2 q r c = tabc2 q r c := by
  rcases q with _ | p
  · rw [show W 2 none r c = W (1 + 1) none r c from rfl, W_succT _ none r c hc,
      T_congr _ tabc1 none r c
        (fun s => W_1 _ s _ (newcB_le c hc r) (inv_next c hc r))]
    rw [row_eta r]
    exact checkN2 ⟨c, by omega⟩ (r 0) (r 1)
  · have hp := hq p rfl
    have h0 := ren_zero c p r (hp 0)
    have hlt := ren_lt c p r hp
    rw [← W_ren 2 c p r]
    show W 2 (some (ren c p r).1) (ren c p r).2 c = tab2 (some (ren c p r).1) (ren c p r).2 c
    generalize ren c p r = x at h0 hlt ⊢
    rw [show W 2 (some x.1) x.2 c = W (1 + 1) (some x.1) x.2 c from rfl, W_succT _ (some x.1) x.2 c hc,
      T_congr _ tabc1 (some x.1) x.2 c
        (fun s => W_1 _ s _ (newcB_le c hc x.2) (inv_next c hc x.2))]
    rw [row_eta x.1, row_eta x.2]
    exact checkS2 ⟨c, by omega⟩ (x.1 0) (x.1 1) (x.2 0) (x.2 1) ⟨hlt 0, hlt 1⟩ (congrArg Fin.val h0)

lemma W_3 (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ) (hc : c ≤ 5)
    (hq : ∀ p, q = some p → ∀ j, (p j).val < c) :
    W 3 q r c = tabc3 q r c := by
  rcases q with _ | p
  · rw [show W 3 none r c = W (2 + 1) none r c from rfl, W_succT _ none r c hc,
      T_congr _ tabc2 none r c
        (fun s => W_2 _ s _ (newcB_le c hc r) (inv_next c hc r))]
    rw [row_eta r]
    exact checkN3 ⟨c, by omega⟩ (r 0) (r 1)
  · have hp := hq p rfl
    have h0 := ren_zero c p r (hp 0)
    have hlt := ren_lt c p r hp
    rw [← W_ren 3 c p r]
    show W 3 (some (ren c p r).1) (ren c p r).2 c = tab3 (some (ren c p r).1) (ren c p r).2 c
    generalize ren c p r = x at h0 hlt ⊢
    rw [show W 3 (some x.1) x.2 c = W (2 + 1) (some x.1) x.2 c from rfl, W_succT _ (some x.1) x.2 c hc,
      T_congr _ tabc2 (some x.1) x.2 c
        (fun s => W_2 _ s _ (newcB_le c hc x.2) (inv_next c hc x.2))]
    rw [row_eta x.1, row_eta x.2]
    exact checkS3 ⟨c, by omega⟩ (x.1 0) (x.1 1) (x.2 0) (x.2 1) ⟨hlt 0, hlt 1⟩ (congrArg Fin.val h0)

lemma W_4 (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ) (hc : c ≤ 5)
    (hq : ∀ p, q = some p → ∀ j, (p j).val < c) :
    W 4 q r c = tabc4 q r c := by
  rcases q with _ | p
  · rw [show W 4 none r c = W (3 + 1) none r c from rfl, W_succT _ none r c hc,
      T_congr _ tabc3 none r c
        (fun s => W_3 _ s _ (newcB_le c hc r) (inv_next c hc r))]
    rw [row_eta r]
    exact checkN4 ⟨c, by omega⟩ (r 0) (r 1)
  · have hp := hq p rfl
    have h0 := ren_zero c p r (hp 0)
    have hlt := ren_lt c p r hp
    rw [← W_ren 4 c p r]
    show W 4 (some (ren c p r).1) (ren c p r).2 c = tab4 (some (ren c p r).1) (ren c p r).2 c
    generalize ren c p r = x at h0 hlt ⊢
    rw [show W 4 (some x.1) x.2 c = W (3 + 1) (some x.1) x.2 c from rfl, W_succT _ (some x.1) x.2 c hc,
      T_congr _ tabc3 (some x.1) x.2 c
        (fun s => W_3 _ s _ (newcB_le c hc x.2) (inv_next c hc x.2))]
    rw [row_eta x.1, row_eta x.2]
    exact checkS4 ⟨c, by omega⟩ (x.1 0) (x.1 1) (x.2 0) (x.2 1) ⟨hlt 0, hlt 1⟩ (congrArg Fin.val h0)

lemma W_5 (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ) (hc : c ≤ 5)
    (hq : ∀ p, q = some p → ∀ j, (p j).val < c) :
    W 5 q r c = tabc5 q r c := by
  rcases q with _ | p
  · rw [show W 5 none r c = W (4 + 1) none r c from rfl, W_succT _ none r c hc,
      T_congr _ tabc4 none r c
        (fun s => W_4 _ s _ (newcB_le c hc r) (inv_next c hc r))]
    rw [row_eta r]
    exact checkN5 ⟨c, by omega⟩ (r 0) (r 1)
  · have hp := hq p rfl
    have h0 := ren_zero c p r (hp 0)
    have hlt := ren_lt c p r hp
    rw [← W_ren 5 c p r]
    show W 5 (some (ren c p r).1) (ren c p r).2 c = tab5 (some (ren c p r).1) (ren c p r).2 c
    generalize ren c p r = x at h0 hlt ⊢
    rw [show W 5 (some x.1) x.2 c = W (4 + 1) (some x.1) x.2 c from rfl, W_succT _ (some x.1) x.2 c hc,
      T_congr _ tabc4 (some x.1) x.2 c
        (fun s => W_4 _ s _ (newcB_le c hc x.2) (inv_next c hc x.2))]
    rw [row_eta x.1, row_eta x.2]
    exact checkS5 ⟨c, by omega⟩ (x.1 0) (x.1 1) (x.2 0) (x.2 1) ⟨hlt 0, hlt 1⟩ (congrArg Fin.val h0)

lemma W_6 (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ) (hc : c ≤ 5)
    (hq : ∀ p, q = some p → ∀ j, (p j).val < c) :
    W 6 q r c = tabc6 q r c := by
  rcases q with _ | p
  · rw [show W 6 none r c = W (5 + 1) none r c from rfl, W_succT _ none r c hc,
      T_congr _ tabc5 none r c
        (fun s => W_5 _ s _ (newcB_le c hc r) (inv_next c hc r))]
    rw [row_eta r]
    exact checkN6 ⟨c, by omega⟩ (r 0) (r 1)
  · have hp := hq p rfl
    have h0 := ren_zero c p r (hp 0)
    have hlt := ren_lt c p r hp
    rw [← W_ren 6 c p r]
    show W 6 (some (ren c p r).1) (ren c p r).2 c = tab6 (some (ren c p r).1) (ren c p r).2 c
    generalize ren c p r = x at h0 hlt ⊢
    rw [show W 6 (some x.1) x.2 c = W (5 + 1) (some x.1) x.2 c from rfl, W_succT _ (some x.1) x.2 c hc,
      T_congr _ tabc5 (some x.1) x.2 c
        (fun s => W_5 _ s _ (newcB_le c hc x.2) (inv_next c hc x.2))]
    rw [row_eta x.1, row_eta x.2]
    exact checkS6 ⟨c, by omega⟩ (x.1 0) (x.1 1) (x.2 0) (x.2 1) ⟨hlt 0, hlt 1⟩ (congrArg Fin.val h0)

lemma W_7 (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ) (hc : c ≤ 5)
    (hq : ∀ p, q = some p → ∀ j, (p j).val < c) :
    W 7 q r c = tabc7 q r c := by
  rcases q with _ | p
  · rw [show W 7 none r c = W (6 + 1) none r c from rfl, W_succT _ none r c hc,
      T_congr _ tabc6 none r c
        (fun s => W_6 _ s _ (newcB_le c hc r) (inv_next c hc r))]
    rw [row_eta r]
    exact checkN7 ⟨c, by omega⟩ (r 0) (r 1)
  · have hp := hq p rfl
    have h0 := ren_zero c p r (hp 0)
    have hlt := ren_lt c p r hp
    rw [← W_ren 7 c p r]
    show W 7 (some (ren c p r).1) (ren c p r).2 c = tab7 (some (ren c p r).1) (ren c p r).2 c
    generalize ren c p r = x at h0 hlt ⊢
    rw [show W 7 (some x.1) x.2 c = W (6 + 1) (some x.1) x.2 c from rfl, W_succT _ (some x.1) x.2 c hc,
      T_congr _ tabc6 (some x.1) x.2 c
        (fun s => W_6 _ s _ (newcB_le c hc x.2) (inv_next c hc x.2))]
    rw [row_eta x.1, row_eta x.2]
    exact checkS7 ⟨c, by omega⟩ (x.1 0) (x.1 1) (x.2 0) (x.2 1) ⟨hlt 0, hlt 1⟩ (congrArg Fin.val h0)

lemma W_8 (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ) (hc : c ≤ 5)
    (hq : ∀ p, q = some p → ∀ j, (p j).val < c) :
    W 8 q r c = tabc8 q r c := by
  rcases q with _ | p
  · rw [show W 8 none r c = W (7 + 1) none r c from rfl, W_succT _ none r c hc,
      T_congr _ tabc7 none r c
        (fun s => W_7 _ s _ (newcB_le c hc r) (inv_next c hc r))]
    rw [row_eta r]
    exact checkN8 ⟨c, by omega⟩ (r 0) (r 1)
  · have hp := hq p rfl
    have h0 := ren_zero c p r (hp 0)
    have hlt := ren_lt c p r hp
    rw [← W_ren 8 c p r]
    show W 8 (some (ren c p r).1) (ren c p r).2 c = tab8 (some (ren c p r).1) (ren c p r).2 c
    generalize ren c p r = x at h0 hlt ⊢
    rw [show W 8 (some x.1) x.2 c = W (7 + 1) (some x.1) x.2 c from rfl, W_succT _ (some x.1) x.2 c hc,
      T_congr _ tabc7 (some x.1) x.2 c
        (fun s => W_7 _ s _ (newcB_le c hc x.2) (inv_next c hc x.2))]
    rw [row_eta x.1, row_eta x.2]
    exact checkS8 ⟨c, by omega⟩ (x.1 0) (x.1 1) (x.2 0) (x.2 1) ⟨hlt 0, hlt 1⟩ (congrArg Fin.val h0)

lemma W_9 (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ) (hc : c ≤ 5)
    (hq : ∀ p, q = some p → ∀ j, (p j).val < c) :
    W 9 q r c = tabc9 q r c := by
  rcases q with _ | p
  · rw [show W 9 none r c = W (8 + 1) none r c from rfl, W_succT _ none r c hc,
      T_congr _ tabc8 none r c
        (fun s => W_8 _ s _ (newcB_le c hc r) (inv_next c hc r))]
    rw [row_eta r]
    exact checkN9 ⟨c, by omega⟩ (r 0) (r 1)
  · have hp := hq p rfl
    have h0 := ren_zero c p r (hp 0)
    have hlt := ren_lt c p r hp
    rw [← W_ren 9 c p r]
    show W 9 (some (ren c p r).1) (ren c p r).2 c = tab9 (some (ren c p r).1) (ren c p r).2 c
    generalize ren c p r = x at h0 hlt ⊢
    rw [show W 9 (some x.1) x.2 c = W (8 + 1) (some x.1) x.2 c from rfl, W_succT _ (some x.1) x.2 c hc,
      T_congr _ tabc8 (some x.1) x.2 c
        (fun s => W_8 _ s _ (newcB_le c hc x.2) (inv_next c hc x.2))]
    rw [row_eta x.1, row_eta x.2]
    exact checkS9 ⟨c, by omega⟩ (x.1 0) (x.1 1) (x.2 0) (x.2 1) ⟨hlt 0, hlt 1⟩ (congrArg Fin.val h0)

lemma W_10 (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ) (hc : c ≤ 5)
    (hq : ∀ p, q = some p → ∀ j, (p j).val < c) :
    W 10 q r c = tabc10 q r c := by
  rcases q with _ | p
  · rw [show W 10 none r c = W (9 + 1) none r c from rfl, W_succT _ none r c hc,
      T_congr _ tabc9 none r c
        (fun s => W_9 _ s _ (newcB_le c hc r) (inv_next c hc r))]
    rw [row_eta r]
    exact checkN10 ⟨c, by omega⟩ (r 0) (r 1)
  · have hp := hq p rfl
    have h0 := ren_zero c p r (hp 0)
    have hlt := ren_lt c p r hp
    rw [← W_ren 10 c p r]
    show W 10 (some (ren c p r).1) (ren c p r).2 c = tab10 (some (ren c p r).1) (ren c p r).2 c
    generalize ren c p r = x at h0 hlt ⊢
    rw [show W 10 (some x.1) x.2 c = W (9 + 1) (some x.1) x.2 c from rfl, W_succT _ (some x.1) x.2 c hc,
      T_congr _ tabc9 (some x.1) x.2 c
        (fun s => W_9 _ s _ (newcB_le c hc x.2) (inv_next c hc x.2))]
    rw [row_eta x.1, row_eta x.2]
    exact checkS10 ⟨c, by omega⟩ (x.1 0) (x.1 1) (x.2 0) (x.2 1) ⟨hlt 0, hlt 1⟩ (congrArg Fin.val h0)

lemma W_rec (n : ℕ) : ∀ (q : Option (Fin 2 → Fin 5)) (r : Fin 2 → Fin 5) (c : ℕ), c ≤ 5 →
    (∀ p, q = some p → ∀ j, (p j).val < c) →
    W (n + 11) q r c + 691 * W (n + 7) q r c + 7056 * W (n + 3) q r c = 51 * W (n + 9) q r c + 3601 * W (n + 5) q r c + 4096 * W (n + 1) q r c := by
  induction n with
  | zero =>
    intro q r c hc hq
    rcases q with _ | p
    · rw [show W (0 + 11) none r c = W (10 + 1) none r c from rfl, W_succT 10 none r c hc,
        T_congr _ tabc10 none r c
          (fun s => W_10 _ s _ (newcB_le c hc r) (inv_next c hc r)),
        show W (0 + 1) none r c = W 1 none r c from rfl, W_1 none r c hc hq,
        show W (0 + 3) none r c = W 3 none r c from rfl, W_3 none r c hc hq,
        show W (0 + 5) none r c = W 5 none r c from rfl, W_5 none r c hc hq,
        show W (0 + 7) none r c = W 7 none r c from rfl, W_7 none r c hc hq,
        show W (0 + 9) none r c = W 9 none r c from rfl, W_9 none r c hc hq]
      rw [row_eta r]
      exact checkN_rel ⟨c, by omega⟩ (r 0) (r 1)
    · have hp := hq p rfl
      have h0 := ren_zero c p r (hp 0)
      have hlt := ren_lt c p r hp
      rw [show W (0 + 11) (some p) r c = W 11 (some p) r c from rfl, show W (0 + 9) (some p) r c = W 9 (some p) r c from rfl, show W (0 + 7) (some p) r c = W 7 (some p) r c from rfl, show W (0 + 5) (some p) r c = W 5 (some p) r c from rfl, show W (0 + 3) (some p) r c = W 3 (some p) r c from rfl, show W (0 + 1) (some p) r c = W 1 (some p) r c from rfl]
      rw [← W_ren 11 c p r, ← W_ren 9 c p r, ← W_ren 7 c p r, ← W_ren 5 c p r, ← W_ren 3 c p r, ← W_ren 1 c p r]
      generalize ren c p r = x at h0 hlt ⊢
      have hx : ∀ p', some x.1 = some p' → ∀ j, (p' j).val < c := fun p' h => by
        rw [← Option.some.inj h]
        exact hlt
      rw [show W 11 (some x.1) x.2 c = W (10 + 1) (some x.1) x.2 c from rfl, W_succT 10 (some x.1) x.2 c hc,
        T_congr _ tabc10 (some x.1) x.2 c
          (fun s => W_10 _ s _ (newcB_le c hc x.2) (inv_next c hc x.2)),
        W_1 (some x.1) x.2 c hc hx,
        W_3 (some x.1) x.2 c hc hx,
        W_5 (some x.1) x.2 c hc hx,
        W_7 (some x.1) x.2 c hc hx,
        W_9 (some x.1) x.2 c hc hx]
      rw [row_eta x.1, row_eta x.2]
      exact checkS_rel ⟨c, by omega⟩ (x.1 0) (x.1 1) (x.2 0) (x.2 1) ⟨hlt 0, hlt 1⟩ (congrArg Fin.val h0)
  | succ n ih =>
    intro q r c hc hq
    rw [W_succT (n + 11) q r c hc, W_succT (n + 9) q r c hc, W_succT (n + 7) q r c hc, W_succT (n + 5) q r c hc, W_succT (n + 3) q r c hc, W_succT (n + 1) q r c hc]
    unfold T
    split_ifs with h
    · rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      split_ifs
      · exact ih _ _ _ (newcB_le c hc r) (inv_next c hc r)
      · simp
    · simp

lemma a_eq (n : ℕ) : a (n + 1) = ∑ r : Fin 2 → Fin 5, W (2 * n + 1) none r 0 := by
  unfold a W
  rw [Finset.card_eq_sum_card_fiberwise (f := fun f => f 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Finset.filter_filter]
  refine congrArg Finset.card (Finset.filter_congr (fun f _ => ?_))
  rw [cond_iff, rmn_iff, and_assoc]

lemma a_rec (n : ℕ) : a (n + 6) + 691 * a (n + 4) + 7056 * a (n + 2) = 51 * a (n + 5) + 3601 * a (n + 3) + 4096 * a (n + 1) := by
  rw [a_eq (n + 5), a_eq (n + 4), a_eq (n + 3), a_eq (n + 2), a_eq (n + 1), a_eq n, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [show 2 * (n + 5) + 1 = 2 * n + 11 by ring, show 2 * (n + 4) + 1 = 2 * n + 9 by ring, show 2 * (n + 3) + 1 = 2 * n + 7 by ring, show 2 * (n + 2) + 1 = 2 * n + 5 by ring, show 2 * (n + 1) + 1 = 2 * n + 3 by ring]
  exact W_rec (2 * n) none r 0 (by norm_num) (fun _ h => by cases h)

lemma a_one : a 1 = 2 := by
  have h : ∀ r, W 1 none r 0 = tabc1 none r 0 := fun r => W_1 none r 0 (by norm_num) (fun _ h => by cases h)
  rw [a_eq 0, sum_row]
  simp only [h]
  decide +kernel

lemma a_two : a 2 = 17 := by
  have h : ∀ r, W 3 none r 0 = tabc3 none r 0 := fun r => W_3 none r 0 (by norm_num) (fun _ h => by cases h)
  rw [a_eq 1, sum_row]
  simp only [h]
  decide +kernel

lemma a_three : a 3 = 377 := by
  have h : ∀ r, W 5 none r 0 = tabc5 none r 0 := fun r => W_5 none r 0 (by norm_num) (fun _ h => by cases h)
  rw [a_eq 2, sum_row]
  simp only [h]
  decide +kernel

lemma a_four : a 4 = 11473 := by
  have h : ∀ r, W 7 none r 0 = tabc7 none r 0 := fun r => W_7 none r 0 (by norm_num) (fun _ h => by cases h)
  rw [a_eq 3, sum_row]
  simp only [h]
  decide +kernel

lemma a_five : a 5 = 375273 := by
  have h : ∀ r, W 9 none r 0 = tabc9 none r 0 := fun r => W_9 none r 0 (by norm_num) (fun _ h => by cases h)
  rw [a_eq 4, sum_row]
  simp only [h]
  decide +kernel

/-- Barker's g.f.: Sum_{n >= 1} a(n) x^n = x(2 - 85x + 892x^2 - 3209x^3 + 3552x^4) / ((1 - x)(1 - 9x + 16x^2)(1 - 41x + 256x^2)). -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - X) * (1 - 9 * X + 16 * X ^ 2) * (1 - 41 * X + 256 * X ^ 2)) = X * (2 - 85 * X + 892 * X ^ 2 - 3209 * X ^ 3 + 3552 * X ^ 4) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - X) * (1 - 9 * X + 16 * X ^ 2) * (1 - 41 * X + 256 * X ^ 2)) = A - A * X ^ 1 * C 51 + A * X ^ 2 * C 691 - A * X ^ 3 * C 3601 + A * X ^ 4 * C 7056 - A * X ^ 5 * C 4096 := by
    rw [show (C (51 : ℚ) : ℚ⟦X⟧) = 51 from map_ofNat C 51,
      show (C (691 : ℚ) : ℚ⟦X⟧) = 691 from map_ofNat C 691,
      show (C (3601 : ℚ) : ℚ⟦X⟧) = 3601 from map_ofNat C 3601,
      show (C (4096 : ℚ) : ℚ⟦X⟧) = 4096 from map_ofNat C 4096,
      show (C (7056 : ℚ) : ℚ⟦X⟧) = 7056 from map_ofNat C 7056]
    ring
  have e2 : (X * (2 - 85 * X + 892 * X ^ 2 - 3209 * X ^ 3 + 3552 * X ^ 4) : ℚ⟦X⟧) = X ^ 1 * C 2 - X ^ 2 * C 85 + X ^ 3 * C 892 - X ^ 4 * C 3209 + X ^ 5 * C 3552 := by
    rw [show (C (2 : ℚ) : ℚ⟦X⟧) = 2 from map_ofNat C 2,
      show (C (85 : ℚ) : ℚ⟦X⟧) = 85 from map_ofNat C 85,
      show (C (892 : ℚ) : ℚ⟦X⟧) = 892 from map_ofNat C 892,
      show (C (3209 : ℚ) : ℚ⟦X⟧) = 3209 from map_ofNat C 3209,
      show (C (3552 : ℚ) : ℚ⟦X⟧) = 3552 from map_ofNat C 3552]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk]
  rcases n with _ | _ | _ | _ | _ | _ | n
  · simp
  · simp [a_one] <;> norm_num
  · simp [a_one, a_two] <;> norm_num
  · simp [a_one, a_two, a_three] <;> norm_num
  · simp [a_one, a_two, a_three, a_four] <;> norm_num
  · simp [a_one, a_two, a_three, a_four, a_five] <;> norm_num
  · have h := a_rec n
    
    have hq : (a (n + 6) : ℚ) + 691 * (a (n + 4) : ℚ) + 7056 * (a (n + 2) : ℚ) = 51 * (a (n + 5) : ℚ) + 3601 * (a (n + 3) : ℚ) + 4096 * (a (n + 1) : ℚ) := by exact_mod_cast h
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

theorem cf (b : ℕ → ℕ) (h1 : b 1 = 2) (h2 : b 2 = 17) (h3 : b 3 = 377) (h4 : b 4 = 11473)
    (h5 : b 5 = 375273)
    (hr : ∀ n, b (n + 6) + 691 * b (n + 4) + 7056 * b (n + 2) =
      51 * b (n + 5) + 3601 * b (n + 3) + 4096 * b (n + 1)) :
    ∀ n : ℕ, 1 ≤ n → (b n : ℝ) =
      (2 ^ (-8 - (n : ℤ)) * (-1752 * (9 - Real.sqrt 17) ^ n * (-51 + 5 * Real.sqrt 17) +
        1752 * (9 + Real.sqrt 17) ^ n * (51 + 5 * Real.sqrt 17) +
        17 * (73 * 2 ^ (9 + n) + (365 - 17 * Real.sqrt 73) * (41 - 3 * Real.sqrt 73) ^ n +
          (41 + 3 * Real.sqrt 73) ^ n * (365 + 17 * Real.sqrt 73)))) / 3723 := by
  have s2 : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have t2 : Real.sqrt 73 ^ 2 = 73 := Real.sq_sqrt (by norm_num)
  set s := Real.sqrt 17 with hsdef
  set t := Real.sqrt 73 with htdef
  set U : ℕ → ℝ := fun n => -1752 * (9 - s) ^ n * (-51 + 5 * s) + 1752 * (9 + s) ^ n * (51 + 5 * s)
    with hU
  set V : ℕ → ℝ := fun n => (365 - 17 * t) * (41 - 3 * t) ^ n + (41 + 3 * t) ^ n * (365 + 17 * t)
    with hV
  have Urec : ∀ n, U (n + 2) = 18 * U (n + 1) - 64 * U n := by
    intro n
    simp only [hU]
    have e1 : (9 - s) ^ 2 = 18 * (9 - s) - 64 := by linear_combination s2
    have e2 : (9 + s) ^ 2 = 18 * (9 + s) - 64 := by linear_combination s2
    rw [show (9 - s) ^ (n + 2) = (9 - s) ^ n * (9 - s) ^ 2 by ring,
      show (9 + s) ^ (n + 2) = (9 + s) ^ n * (9 + s) ^ 2 by ring, e1, e2]
    ring
  have Vrec : ∀ n, V (n + 2) = 82 * V (n + 1) - 1024 * V n := by
    intro n
    simp only [hV]
    have e1 : (41 - 3 * t) ^ 2 = 82 * (41 - 3 * t) - 1024 := by linear_combination 9 * t2
    have e2 : (41 + 3 * t) ^ 2 = 82 * (41 + 3 * t) - 1024 := by linear_combination 9 * t2
    rw [show (41 - 3 * t) ^ (n + 2) = (41 - 3 * t) ^ n * (41 - 3 * t) ^ 2 by ring,
      show (41 + 3 * t) ^ (n + 2) = (41 + 3 * t) ^ n * (41 + 3 * t) ^ 2 by ring, e1, e2]
    ring
  have U0 : U 0 = 178704 := by simp only [hU]; ring
  have U1 : U 1 = 1906176 := by simp only [hU]; linear_combination 17520 * s2
  have U2 : U 2 = 22874112 := by
    rw [show U 2 = U (0 + 2) from rfl, Urec, show U (0 + 1) = U 1 from rfl, U1, U0]; norm_num
  have U3 : U 3 = 289738752 := by
    rw [show U 3 = U (1 + 2) from rfl, Urec, show U (1 + 1) = U 2 from rfl, U2, U1]; norm_num
  have U4 : U 4 = 3751354368 := by
    rw [show U 4 = U (2 + 2) from rfl, Urec, show U (2 + 1) = U 3 from rfl, U3, U2]; norm_num
  have U5 : U 5 = 48981098496 := by
    rw [show U 5 = U (3 + 2) from rfl, Urec, show U (3 + 1) = U 4 from rfl, U4, U3]; norm_num
  have V0 : V 0 = 730 := by simp only [hV]; ring
  have V1 : V 1 = 37376 := by simp only [hV]; linear_combination 102 * t2
  have V2 : V 2 = 2317312 := by
    rw [show V 2 = V (0 + 2) from rfl, Vrec, show V (0 + 1) = V 1 from rfl, V1, V0]; norm_num
  have V3 : V 3 = 151746560 := by
    rw [show V 3 = V (1 + 2) from rfl, Vrec, show V (1 + 1) = V 2 from rfl, V2, V1]; norm_num
  have V4 : V 4 = 10070290432 := by
    rw [show V 4 = V (2 + 2) from rfl, Vrec, show V (2 + 1) = V 3 from rfl, V3, V2]; norm_num
  have V5 : V 5 = 670375337984 := by
    rw [show V 5 = V (3 + 2) from rfl, Vrec, show V (3 + 1) = V 4 from rfl, V4, V3]; norm_num
  set G : ℕ → ℝ := fun n => U n + 17 * (73 * 2 ^ (9 + n) + V n) with hG
  have Grec : ∀ n, G (n + 5) = 102 * G (n + 4) - 2764 * G (n + 3) + 28808 * G (n + 2) -
      112896 * G (n + 1) + 131072 * G n := by
    intro n
    simp only [hG]
    have u0 := Urec n
    have u1 := Urec (n + 1)
    have u2 := Urec (n + 2)
    have u3 := Urec (n + 3)
    have v0 := Vrec n
    have v1 := Vrec (n + 1)
    have v2 := Vrec (n + 2)
    have v3 := Vrec (n + 3)
    rw [show n + 1 + 2 = n + 3 from rfl, show n + 1 + 1 = n + 2 from rfl] at u1 v1
    rw [show n + 2 + 2 = n + 4 from rfl, show n + 2 + 1 = n + 3 from rfl] at u2 v2
    rw [show n + 3 + 2 = n + 5 from rfl, show n + 3 + 1 = n + 4 from rfl] at u3 v3
    linear_combination u3 - 84 * u2 + 1188 * u1 - 2048 * u0 +
      17 * (v3 - 20 * v2 + 100 * v1 - 128 * v0)
  have key : ∀ k, (b (k + 1) : ℝ) * (3723 * 2 ^ (k + 9)) = G (k + 1) ∧
      (b (k + 2) : ℝ) * (3723 * 2 ^ (k + 10)) = G (k + 2) ∧
      (b (k + 3) : ℝ) * (3723 * 2 ^ (k + 11)) = G (k + 3) ∧
      (b (k + 4) : ℝ) * (3723 * 2 ^ (k + 12)) = G (k + 4) ∧
      (b (k + 5) : ℝ) * (3723 * 2 ^ (k + 13)) = G (k + 5) := by
    intro k
    induction k with
    | zero =>
      simp only [hG, Nat.zero_add]
      rw [h1, h2, h3, h4, h5, U1, U2, U3, U4, U5, V1, V2, V3, V4, V5]
      norm_num
    | succ k ih =>
      obtain ⟨i1, i2, i3, i4, i5⟩ := ih
      refine ⟨i2, i3, i4, i5, ?_⟩
      have hq : ((b (k + 6) : ℕ) : ℝ) + 691 * b (k + 4) + 7056 * b (k + 2) =
          51 * b (k + 5) + 3601 * b (k + 3) + 4096 * b (k + 1) := by exact_mod_cast hr k
      have hg := Grec (k + 1)
      rw [show k + 1 + 5 = k + 6 from rfl, show k + 1 + 4 = k + 5 from rfl,
        show k + 1 + 3 = k + 4 from rfl, show k + 1 + 2 = k + 3 from rfl,
        show k + 1 + 1 = k + 2 from rfl] at hg
      rw [show k + 1 + 5 = k + 6 from rfl, show k + 1 + 13 = k + 14 from rfl]
      linear_combination (3723 * 2 ^ (k + 14)) * hq - hg + 102 * i5 - 2764 * i4 + 28808 * i3 -
        112896 * i2 + 131072 * i1
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hk := (key k).1
  have hz : (2 : ℝ) ^ (-8 - ((k + 1 : ℕ) : ℤ)) = 1 / 2 ^ (k + 9) := by
    rw [show -8 - ((k + 1 : ℕ) : ℤ) = -((k + 9 : ℕ) : ℤ) by push_cast; ring, zpow_neg,
      zpow_natCast, one_div]
  have e : -1752 * (9 - s) ^ (k + 1) * (-51 + 5 * s) + 1752 * (9 + s) ^ (k + 1) * (51 + 5 * s) +
      17 * (73 * 2 ^ (9 + (k + 1)) + (365 - 17 * t) * (41 - 3 * t) ^ (k + 1) +
        (41 + 3 * t) ^ (k + 1) * (365 + 17 * t)) = G (k + 1) := by
    simp only [hG, hU, hV]
    ring
  rw [hz, e, ← hk]
  field_simp

/-- Barker's closed form. -/
theorem closed_form : ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (2 ^ (-8 - (n : ℤ)) * (-1752 * (9 - Real.sqrt 17) ^ n * (-51 + 5 * Real.sqrt 17) +
        1752 * (9 + Real.sqrt 17) ^ n * (51 + 5 * Real.sqrt 17) +
        17 * (73 * 2 ^ (9 + n) + (365 - 17 * Real.sqrt 73) * (41 - 3 * Real.sqrt 73) ^ n +
          (41 + 3 * Real.sqrt 73) ^ n * (365 + 17 * Real.sqrt 73)))) / 3723 :=
  cf a a_one a_two a_three a_four a_five a_rec

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 - 9 * X + 16 * X ^ 2) * (1 - 41 * X + 256 * X ^ 2)) = X * (2 - 85 * X + 892 * X ^ 2 - 3209 * X ^ 3 + 3552 * X ^ 4) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (2 ^ (-8 - (n : ℤ)) * (-1752 * (9 - Real.sqrt 17) ^ n * (-51 + 5 * Real.sqrt 17) +
        1752 * (9 + Real.sqrt 17) ^ n * (51 + 5 * Real.sqrt 17) +
        17 * (73 * 2 ^ (9 + n) + (365 - 17 * Real.sqrt 73) * (41 - 3 * Real.sqrt 73) ^ n +
          (41 + 3 * Real.sqrt 73) ^ n * (365 + 17 * Real.sqrt 73)))) / 3723 :=
  ⟨gf, closed_form⟩

/-- Controls: the entry's terms a(1..10), from the recurrence and the first values. -/
theorem controls : a 1 = 2 ∧ a 2 = 17 ∧ a 3 = 377 ∧ a 4 = 11473 ∧ a 5 = 375273 ∧ a 6 = 12456897 ∧ a 7 = 414711897 ∧ a 8 = 13814539697 ∧ a 9 = 460231956937 ∧ a 10 = 15333001667233 := by
  have r0 := a_rec 0; have r1 := a_rec 1; have r2 := a_rec 2; have r3 := a_rec 3; have r4 := a_rec 4
  have h1 := a_one; have h2 := a_two; have h3 := a_three; have h4 := a_four; have h5 := a_five
  norm_num at r0 r1 r2 r3 r4
  omega

end OMA.S_oeis_a198405

theorem OMA.solution : type_of% @OMA.S_oeis_a198405.main :=
  OMA.S_oeis_a198405.conjecture
