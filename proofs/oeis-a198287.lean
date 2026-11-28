import OMAStatements.S_oeis_a198287

namespace OMA.S_oeis_a198287

open PowerSeries Finset


instance {R C K : ℕ} : DecidablePred (@RowMajorNew R C K) := fun x => by
  unfold RowMajorNew; infer_instance



instance {R C K : ℕ} : DecidablePred (@Cond R C K) := fun x => by
  unfold Cond; infer_instance


/-! ## Rows -/

/-- The number of horizontal neighbors of entry j of the row r with an equal value. -/
def hEq (r : Fin 2 → Fin 4) (j : Fin 2) : ℕ :=
  ((univ : Finset (Fin 2)).filter
    (fun j' => (j'.val + 1 = j.val ∨ j.val + 1 = j'.val) ∧ r j' = r j)).card

/-- 1 when the row q exists and its entry j is equal to r j. -/
def vEq (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (j : Fin 2) : ℕ :=
  match q with
  | none => 0
  | some p => if p j = r j then 1 else 0

/-- The condition on the row r with the row q above it and the row s below it. -/
def rowCond (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (s : Option (Fin 2 → Fin 4)) : Prop :=
  ∀ j, (hEq r j + vEq q r j + vEq s r j) = 1

instance (q : Option (Fin 2 → Fin 4)) (s : Option (Fin 2 → Fin 4)) : DecidablePred (fun r => rowCond q r s) :=
  fun r => by unfold rowCond; infer_instance

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

lemma vcard {R : ℕ} (x : Fin R → Fin 2 → Fin 4) (i : Fin R) (j : Fin 2) :
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

lemma cond_iff {R : ℕ} (x : Fin R → Fin 2 → Fin 4) : Cond x ↔ ValidFrom none x := by
  unfold Cond ValidFrom rowCond eqNbrs
  simp only [vcard, hEq, Nat.add_assoc]

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

/-- One step of the transfer, the rows below r enumerated entry by entry. -/
def T (g : Option (Fin 2 → Fin 4) → (Fin 2 → Fin 4) → ℕ → ℕ) (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (c : ℕ) : ℕ :=
  if rowRgs c r then
    ∑ x : Fin 4, ∑ y : Fin 4, (if rowCond q r (some ![x, y]) then g (some r) ![x, y] (newc c r) else 0)
  else 0

lemma W_succT (n : ℕ) (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (c : ℕ) :
    W (n + 1) q r c = T (W n) q r c := by
  rw [W_succ, T, sum_row]

lemma T_congr (g g' : Option (Fin 2 → Fin 4) → (Fin 2 → Fin 4) → ℕ → ℕ) (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (c : ℕ)
    (h : ∀ s, g (some r) s (newc c r) = g' (some r) s (newc c r)) : T g q r c = T g' q r c := by
  unfold T
  simp only [h]

/-- W(0) as a function. -/
def W0f (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (c : ℕ) : ℕ := if rowCond q r none ∧ rowRgs c r then 1 else 0

lemma W_zero_fun : W 0 = W0f := by
  funext q r c
  exact W_zero q r c

/-- W(1, none, r, c) for c <= 4, nested by the entries of r and then c. -/
def LN1 : List (List (List ℕ)) :=
  [[[1, 1, 2, 3, 3], [1, 1, 1, 1, 1], [0, 0, 1, 1, 1], [0, 0, 0, 1, 1]], [[0, 1, 1, 1, 1], [0, 2, 2, 3, 3], [0, 1, 1, 1, 1], [0, 0, 0, 1, 1]], [[0, 0, 1, 1, 1], [0, 0, 1, 1, 1], [0, 0, 3, 3, 3], [0, 0, 1, 1, 1]], [[0, 0, 0, 1, 1], [0, 0, 0, 1, 1], [0, 0, 0, 1, 1], [0, 0, 0, 3, 3]]]

/-- W(1, some p, r, c) for c <= 4, nested by the entries of p, of r, and then c. -/
def LS1 : List (List (List (List (List ℕ)))) :=
  [[[[[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0], [0, 2, 2, 3, 3], [0, 1, 1, 1, 1], [0, 0, 0, 1, 1]], [[0, 0, 0, 0, 0], [0, 0, 1, 1, 1], [0, 0, 3, 3, 3], [0, 0, 1, 1, 1]], [[0, 0, 0, 0, 0], [0, 0, 0, 1, 1], [0, 0, 0, 1, 1], [0, 0, 0, 3, 3]]], [[[0, 0, 0, 0, 0], [1, 1, 1, 2, 2], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 1, 1, 1, 1], [0, 0, 0, 0, 0], [0, 1, 1, 1, 1], [0, 0, 0, 1, 1]], [[0, 0, 1, 1, 1], [0, 0, 0, 0, 0], [0, 0, 3, 3, 3], [0, 0, 1, 1, 1]], [[0, 0, 0, 1, 1], [0, 0, 0, 0, 0], [0, 0, 0, 1, 1], [0, 0, 0, 3, 3]]], [[[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 2, 2, 2], [0, 0, 0, 0, 0]], [[0, 1, 1, 1, 1], [0, 2, 2, 3, 3], [0, 0, 0, 0, 0], [0, 0, 0, 1, 1]], [[0, 0, 1, 1, 1], [0, 0, 1, 1, 1], [0, 0, 0, 0, 0], [0, 0, 1, 1, 1]], [[0, 0, 0, 1, 1], [0, 0, 0, 1, 1], [0, 0, 0, 0, 0], [0, 0, 0, 3, 3]]], [[[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 2, 2]], [[0, 1, 1, 1, 1], [0, 2, 2, 3, 3], [0, 1, 1, 1, 1], [0, 0, 0, 0, 0]], [[0, 0, 1, 1, 1], [0, 0, 1, 1, 1], [0, 0, 3, 3, 3], [0, 0, 0, 0, 0]], [[0, 0, 0, 1, 1], [0, 0, 0, 1, 1], [0, 0, 0, 1, 1], [0, 0, 0, 0, 0]]]], [[[[0, 0, 0, 0, 0], [1, 1, 1, 1, 1], [0, 0, 1, 1, 1], [0, 0, 0, 1, 1]], [[0, 1, 1, 2, 2], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0], [0, 0, 1, 1, 1], [0, 0, 3, 3, 3], [0, 0, 1, 1, 1]], [[0, 0, 0, 0, 0], [0, 0, 0, 1, 1], [0, 0, 0, 1, 1], [0, 0, 0, 3, 3]]], [[[1, 1, 2, 3, 3], [0, 0, 0, 0, 0], [0, 0, 1, 1, 1], [0, 0, 0, 1, 1]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 0, 1, 1, 1], [0, 0, 0, 0, 0], [0, 0, 3, 3, 3], [0, 0, 1, 1, 1]], [[0, 0, 0, 1, 1], [0, 0, 0, 0, 0], [0, 0, 0, 1, 1], [0, 0, 0, 3, 3]]], [[[1, 1, 2, 3, 3], [1, 1, 1, 1, 1], [0, 0, 0, 0, 0], [0, 0, 0, 1, 1]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 2, 2, 2, 2], [0, 0, 0, 0, 0]], [[0, 0, 1, 1, 1], [0, 0, 1, 1, 1], [0, 0, 0, 0, 0], [0, 0, 1, 1, 1]], [[0, 0, 0, 1, 1], [0, 0, 0, 1, 1], [0, 0, 0, 0, 0], [0, 0, 0, 3, 3]]], [[[1, 1, 2, 3, 3], [1, 1, 1, 1, 1], [0, 0, 1, 1, 1], [0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 2, 2]], [[0, 0, 1, 1, 1], [0, 0, 1, 1, 1], [0, 0, 3, 3, 3], [0, 0, 0, 0, 0]], [[0, 0, 0, 1, 1], [0, 0, 0, 1, 1], [0, 0, 0, 1, 1], [0, 0, 0, 0, 0]]]], [[[[0, 0, 0, 0, 0], [1, 1, 1, 1, 1], [0, 0, 1, 1, 1], [0, 0, 0, 1, 1]], [[0, 0, 0, 0, 0], [0, 2, 2, 3, 3], [0, 1, 1, 1, 1], [0, 0, 0, 1, 1]], [[0, 0, 2, 2, 2], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0], [0, 0, 0, 1, 1], [0, 0, 0, 1, 1], [0, 0, 0, 3, 3]]], [[[1, 1, 2, 3, 3], [0, 0, 0, 0, 0], [0, 0, 1, 1, 1], [0, 0, 0, 1, 1]], [[0, 1, 1, 1, 1], [0, 0, 0, 0, 0], [0, 1, 1, 1, 1], [0, 0, 0, 1, 1]], [[0, 0, 0, 0, 0], [0, 0, 2, 2, 2], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 0, 0, 1, 1], [0, 0, 0, 0, 0], [0, 0, 0, 1, 1], [0, 0, 0, 3, 3]]], [[[1, 1, 2, 3, 3], [1, 1, 1, 1, 1], [0, 0, 0, 0, 0], [0, 0, 0, 1, 1]], [[0, 1, 1, 1, 1], [0, 2, 2, 3, 3], [0, 0, 0, 0, 0], [0, 0, 0, 1, 1]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 0, 0, 1, 1], [0, 0, 0, 1, 1], [0, 0, 0, 0, 0], [0, 0, 0, 3, 3]]], [[[1, 1, 2, 3, 3], [1, 1, 1, 1, 1], [0, 0, 1, 1, 1], [0, 0, 0, 0, 0]], [[0, 1, 1, 1, 1], [0, 2, 2, 3, 3], [0, 1, 1, 1, 1], [0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 2, 2, 2]], [[0, 0, 0, 1, 1], [0, 0, 0, 1, 1], [0, 0, 0, 1, 1], [0, 0, 0, 0, 0]]]], [[[[0, 0, 0, 0, 0], [1, 1, 1, 1, 1], [0, 0, 1, 1, 1], [0, 0, 0, 1, 1]], [[0, 0, 0, 0, 0], [0, 2, 2, 3, 3], [0, 1, 1, 1, 1], [0, 0, 0, 1, 1]], [[0, 0, 0, 0, 0], [0, 0, 1, 1, 1], [0, 0, 3, 3, 3], [0, 0, 1, 1, 1]], [[0, 0, 0, 2, 2], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]]], [[[1, 1, 2, 3, 3], [0, 0, 0, 0, 0], [0, 0, 1, 1, 1], [0, 0, 0, 1, 1]], [[0, 1, 1, 1, 1], [0, 0, 0, 0, 0], [0, 1, 1, 1, 1], [0, 0, 0, 1, 1]], [[0, 0, 1, 1, 1], [0, 0, 0, 0, 0], [0, 0, 3, 3, 3], [0, 0, 1, 1, 1]], [[0, 0, 0, 0, 0], [0, 0, 0, 2, 2], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]]], [[[1, 1, 2, 3, 3], [1, 1, 1, 1, 1], [0, 0, 0, 0, 0], [0, 0, 0, 1, 1]], [[0, 1, 1, 1, 1], [0, 2, 2, 3, 3], [0, 0, 0, 0, 0], [0, 0, 0, 1, 1]], [[0, 0, 1, 1, 1], [0, 0, 1, 1, 1], [0, 0, 0, 0, 0], [0, 0, 1, 1, 1]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 2, 2], [0, 0, 0, 0, 0]]], [[[1, 1, 2, 3, 3], [1, 1, 1, 1, 1], [0, 0, 1, 1, 1], [0, 0, 0, 0, 0]], [[0, 1, 1, 1, 1], [0, 2, 2, 3, 3], [0, 1, 1, 1, 1], [0, 0, 0, 0, 0]], [[0, 0, 1, 1, 1], [0, 0, 1, 1, 1], [0, 0, 3, 3, 3], [0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]]]]]

/-- W(1) as a table. -/
def tab1 (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (c : ℕ) : ℕ :=
  match q with
  | none => ((LN1.getD (r 0).val []).getD (r 1).val []).getD c 0
  | some p => ((((LS1.getD (p 0).val []).getD (p 1).val []).getD (r 0).val []).getD (r 1).val []).getD c 0

/-- W(2, none, r, c) for c <= 4, nested by the entries of r and then c. -/
def LN2 : List (List (List ℕ)) :=
  [[[3, 3, 8, 15, 15], [1, 1, 1, 2, 2], [0, 0, 2, 2, 2], [0, 0, 0, 2, 2]], [[0, 1, 1, 2, 2], [0, 8, 8, 15, 15], [0, 2, 2, 2, 2], [0, 0, 0, 2, 2]], [[0, 0, 2, 2, 2], [0, 0, 2, 2, 2], [0, 0, 15, 15, 15], [0, 0, 2, 2, 2]], [[0, 0, 0, 2, 2], [0, 0, 0, 2, 2], [0, 0, 0, 2, 2], [0, 0, 0, 15, 15]]]

/-- W(2, some p, r, c) for c <= 4, nested by the entries of p, of r, and then c. -/
def LS2 : List (List (List (List (List ℕ)))) :=
  [[[[[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0], [0, 8, 8, 15, 15], [0, 2, 2, 2, 2], [0, 0, 0, 2, 2]], [[0, 0, 0, 0, 0], [0, 0, 2, 2, 2], [0, 0, 15, 15, 15], [0, 0, 2, 2, 2]], [[0, 0, 0, 0, 0], [0, 0, 0, 2, 2], [0, 0, 0, 2, 2], [0, 0, 0, 15, 15]]], [[[0, 0, 0, 0, 0], [7, 7, 7, 13, 13], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 1, 1, 2, 2], [0, 0, 0, 0, 0], [0, 2, 2, 2, 2], [0, 0, 0, 2, 2]], [[0, 0, 2, 2, 2], [0, 0, 0, 0, 0], [0, 0, 15, 15, 15], [0, 0, 2, 2, 2]], [[0, 0, 0, 2, 2], [0, 0, 0, 0, 0], [0, 0, 0, 2, 2], [0, 0, 0, 15, 15]]], [[[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 13, 13, 13], [0, 0, 0, 0, 0]], [[0, 1, 1, 2, 2], [0, 8, 8, 15, 15], [0, 0, 0, 0, 0], [0, 0, 0, 2, 2]], [[0, 0, 2, 2, 2], [0, 0, 2, 2, 2], [0, 0, 0, 0, 0], [0, 0, 2, 2, 2]], [[0, 0, 0, 2, 2], [0, 0, 0, 2, 2], [0, 0, 0, 0, 0], [0, 0, 0, 15, 15]]], [[[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 13, 13]], [[0, 1, 1, 2, 2], [0, 8, 8, 15, 15], [0, 2, 2, 2, 2], [0, 0, 0, 0, 0]], [[0, 0, 2, 2, 2], [0, 0, 2, 2, 2], [0, 0, 15, 15, 15], [0, 0, 0, 0, 0]], [[0, 0, 0, 2, 2], [0, 0, 0, 2, 2], [0, 0, 0, 2, 2], [0, 0, 0, 0, 0]]]], [[[[0, 0, 0, 0, 0], [1, 1, 1, 2, 2], [0, 0, 2, 2, 2], [0, 0, 0, 2, 2]], [[0, 7, 7, 13, 13], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0], [0, 0, 2, 2, 2], [0, 0, 15, 15, 15], [0, 0, 2, 2, 2]], [[0, 0, 0, 0, 0], [0, 0, 0, 2, 2], [0, 0, 0, 2, 2], [0, 0, 0, 15, 15]]], [[[3, 3, 8, 15, 15], [0, 0, 0, 0, 0], [0, 0, 2, 2, 2], [0, 0, 0, 2, 2]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 0, 2, 2, 2], [0, 0, 0, 0, 0], [0, 0, 15, 15, 15], [0, 0, 2, 2, 2]], [[0, 0, 0, 2, 2], [0, 0, 0, 0, 0], [0, 0, 0, 2, 2], [0, 0, 0, 15, 15]]], [[[3, 3, 8, 15, 15], [1, 1, 1, 2, 2], [0, 0, 0, 0, 0], [0, 0, 0, 2, 2]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 13, 13, 13, 13], [0, 0, 0, 0, 0]], [[0, 0, 2, 2, 2], [0, 0, 2, 2, 2], [0, 0, 0, 0, 0], [0, 0, 2, 2, 2]], [[0, 0, 0, 2, 2], [0, 0, 0, 2, 2], [0, 0, 0, 0, 0], [0, 0, 0, 15, 15]]], [[[3, 3, 8, 15, 15], [1, 1, 1, 2, 2], [0, 0, 2, 2, 2], [0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 13, 13]], [[0, 0, 2, 2, 2], [0, 0, 2, 2, 2], [0, 0, 15, 15, 15], [0, 0, 0, 0, 0]], [[0, 0, 0, 2, 2], [0, 0, 0, 2, 2], [0, 0, 0, 2, 2], [0, 0, 0, 0, 0]]]], [[[[0, 0, 0, 0, 0], [1, 1, 1, 2, 2], [0, 0, 2, 2, 2], [0, 0, 0, 2, 2]], [[0, 0, 0, 0, 0], [0, 8, 8, 15, 15], [0, 2, 2, 2, 2], [0, 0, 0, 2, 2]], [[0, 0, 13, 13, 13], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0], [0, 0, 0, 2, 2], [0, 0, 0, 2, 2], [0, 0, 0, 15, 15]]], [[[3, 3, 8, 15, 15], [0, 0, 0, 0, 0], [0, 0, 2, 2, 2], [0, 0, 0, 2, 2]], [[0, 1, 1, 2, 2], [0, 0, 0, 0, 0], [0, 2, 2, 2, 2], [0, 0, 0, 2, 2]], [[0, 0, 0, 0, 0], [0, 0, 13, 13, 13], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 0, 0, 2, 2], [0, 0, 0, 0, 0], [0, 0, 0, 2, 2], [0, 0, 0, 15, 15]]], [[[3, 3, 8, 15, 15], [1, 1, 1, 2, 2], [0, 0, 0, 0, 0], [0, 0, 0, 2, 2]], [[0, 1, 1, 2, 2], [0, 8, 8, 15, 15], [0, 0, 0, 0, 0], [0, 0, 0, 2, 2]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 0, 0, 2, 2], [0, 0, 0, 2, 2], [0, 0, 0, 0, 0], [0, 0, 0, 15, 15]]], [[[3, 3, 8, 15, 15], [1, 1, 1, 2, 2], [0, 0, 2, 2, 2], [0, 0, 0, 0, 0]], [[0, 1, 1, 2, 2], [0, 8, 8, 15, 15], [0, 2, 2, 2, 2], [0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 13, 13, 13]], [[0, 0, 0, 2, 2], [0, 0, 0, 2, 2], [0, 0, 0, 2, 2], [0, 0, 0, 0, 0]]]], [[[[0, 0, 0, 0, 0], [1, 1, 1, 2, 2], [0, 0, 2, 2, 2], [0, 0, 0, 2, 2]], [[0, 0, 0, 0, 0], [0, 8, 8, 15, 15], [0, 2, 2, 2, 2], [0, 0, 0, 2, 2]], [[0, 0, 0, 0, 0], [0, 0, 2, 2, 2], [0, 0, 15, 15, 15], [0, 0, 2, 2, 2]], [[0, 0, 0, 13, 13], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]]], [[[3, 3, 8, 15, 15], [0, 0, 0, 0, 0], [0, 0, 2, 2, 2], [0, 0, 0, 2, 2]], [[0, 1, 1, 2, 2], [0, 0, 0, 0, 0], [0, 2, 2, 2, 2], [0, 0, 0, 2, 2]], [[0, 0, 2, 2, 2], [0, 0, 0, 0, 0], [0, 0, 15, 15, 15], [0, 0, 2, 2, 2]], [[0, 0, 0, 0, 0], [0, 0, 0, 13, 13], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]]], [[[3, 3, 8, 15, 15], [1, 1, 1, 2, 2], [0, 0, 0, 0, 0], [0, 0, 0, 2, 2]], [[0, 1, 1, 2, 2], [0, 8, 8, 15, 15], [0, 0, 0, 0, 0], [0, 0, 0, 2, 2]], [[0, 0, 2, 2, 2], [0, 0, 2, 2, 2], [0, 0, 0, 0, 0], [0, 0, 2, 2, 2]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 13, 13], [0, 0, 0, 0, 0]]], [[[3, 3, 8, 15, 15], [1, 1, 1, 2, 2], [0, 0, 2, 2, 2], [0, 0, 0, 0, 0]], [[0, 1, 1, 2, 2], [0, 8, 8, 15, 15], [0, 2, 2, 2, 2], [0, 0, 0, 0, 0]], [[0, 0, 2, 2, 2], [0, 0, 2, 2, 2], [0, 0, 15, 15, 15], [0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]]]]]

/-- W(2) as a table. -/
def tab2 (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (c : ℕ) : ℕ :=
  match q with
  | none => ((LN2.getD (r 0).val []).getD (r 1).val []).getD c 0
  | some p => ((((LS2.getD (p 0).val []).getD (p 1).val []).getD (r 0).val []).getD (r 1).val []).getD c 0

/-- W(3, none, r, c) for c <= 4, nested by the entries of r and then c. -/
def LN3 : List (List (List ℕ)) :=
  [[[10, 10, 29, 57, 57], [7, 7, 7, 13, 13], [0, 0, 13, 13, 13], [0, 0, 0, 13, 13]], [[0, 7, 7, 13, 13], [0, 29, 29, 57, 57], [0, 13, 13, 13, 13], [0, 0, 0, 13, 13]], [[0, 0, 13, 13, 13], [0, 0, 13, 13, 13], [0, 0, 57, 57, 57], [0, 0, 13, 13, 13]], [[0, 0, 0, 13, 13], [0, 0, 0, 13, 13], [0, 0, 0, 13, 13], [0, 0, 0, 57, 57]]]

/-- W(3, some p, r, c) for c <= 4, nested by the entries of p, of r, and then c. -/
def LS3 : List (List (List (List (List ℕ)))) :=
  [[[[[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0], [0, 29, 29, 57, 57], [0, 13, 13, 13, 13], [0, 0, 0, 13, 13]], [[0, 0, 0, 0, 0], [0, 0, 13, 13, 13], [0, 0, 57, 57, 57], [0, 0, 13, 13, 13]], [[0, 0, 0, 0, 0], [0, 0, 0, 13, 13], [0, 0, 0, 13, 13], [0, 0, 0, 57, 57]]], [[[0, 0, 0, 0, 0], [22, 22, 22, 44, 44], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 7, 7, 13, 13], [0, 0, 0, 0, 0], [0, 13, 13, 13, 13], [0, 0, 0, 13, 13]], [[0, 0, 13, 13, 13], [0, 0, 0, 0, 0], [0, 0, 57, 57, 57], [0, 0, 13, 13, 13]], [[0, 0, 0, 13, 13], [0, 0, 0, 0, 0], [0, 0, 0, 13, 13], [0, 0, 0, 57, 57]]], [[[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 44, 44, 44], [0, 0, 0, 0, 0]], [[0, 7, 7, 13, 13], [0, 29, 29, 57, 57], [0, 0, 0, 0, 0], [0, 0, 0, 13, 13]], [[0, 0, 13, 13, 13], [0, 0, 13, 13, 13], [0, 0, 0, 0, 0], [0, 0, 13, 13, 13]], [[0, 0, 0, 13, 13], [0, 0, 0, 13, 13], [0, 0, 0, 0, 0], [0, 0, 0, 57, 57]]], [[[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 44, 44]], [[0, 7, 7, 13, 13], [0, 29, 29, 57, 57], [0, 13, 13, 13, 13], [0, 0, 0, 0, 0]], [[0, 0, 13, 13, 13], [0, 0, 13, 13, 13], [0, 0, 57, 57, 57], [0, 0, 0, 0, 0]], [[0, 0, 0, 13, 13], [0, 0, 0, 13, 13], [0, 0, 0, 13, 13], [0, 0, 0, 0, 0]]]], [[[[0, 0, 0, 0, 0], [7, 7, 7, 13, 13], [0, 0, 13, 13, 13], [0, 0, 0, 13, 13]], [[0, 22, 22, 44, 44], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0], [0, 0, 13, 13, 13], [0, 0, 57, 57, 57], [0, 0, 13, 13, 13]], [[0, 0, 0, 0, 0], [0, 0, 0, 13, 13], [0, 0, 0, 13, 13], [0, 0, 0, 57, 57]]], [[[10, 10, 29, 57, 57], [0, 0, 0, 0, 0], [0, 0, 13, 13, 13], [0, 0, 0, 13, 13]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 0, 13, 13, 13], [0, 0, 0, 0, 0], [0, 0, 57, 57, 57], [0, 0, 13, 13, 13]], [[0, 0, 0, 13, 13], [0, 0, 0, 0, 0], [0, 0, 0, 13, 13], [0, 0, 0, 57, 57]]], [[[10, 10, 29, 57, 57], [7, 7, 7, 13, 13], [0, 0, 0, 0, 0], [0, 0, 0, 13, 13]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 44, 44, 44, 44], [0, 0, 0, 0, 0]], [[0, 0, 13, 13, 13], [0, 0, 13, 13, 13], [0, 0, 0, 0, 0], [0, 0, 13, 13, 13]], [[0, 0, 0, 13, 13], [0, 0, 0, 13, 13], [0, 0, 0, 0, 0], [0, 0, 0, 57, 57]]], [[[10, 10, 29, 57, 57], [7, 7, 7, 13, 13], [0, 0, 13, 13, 13], [0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 44, 44]], [[0, 0, 13, 13, 13], [0, 0, 13, 13, 13], [0, 0, 57, 57, 57], [0, 0, 0, 0, 0]], [[0, 0, 0, 13, 13], [0, 0, 0, 13, 13], [0, 0, 0, 13, 13], [0, 0, 0, 0, 0]]]], [[[[0, 0, 0, 0, 0], [7, 7, 7, 13, 13], [0, 0, 13, 13, 13], [0, 0, 0, 13, 13]], [[0, 0, 0, 0, 0], [0, 29, 29, 57, 57], [0, 13, 13, 13, 13], [0, 0, 0, 13, 13]], [[0, 0, 44, 44, 44], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0], [0, 0, 0, 13, 13], [0, 0, 0, 13, 13], [0, 0, 0, 57, 57]]], [[[10, 10, 29, 57, 57], [0, 0, 0, 0, 0], [0, 0, 13, 13, 13], [0, 0, 0, 13, 13]], [[0, 7, 7, 13, 13], [0, 0, 0, 0, 0], [0, 13, 13, 13, 13], [0, 0, 0, 13, 13]], [[0, 0, 0, 0, 0], [0, 0, 44, 44, 44], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 0, 0, 13, 13], [0, 0, 0, 0, 0], [0, 0, 0, 13, 13], [0, 0, 0, 57, 57]]], [[[10, 10, 29, 57, 57], [7, 7, 7, 13, 13], [0, 0, 0, 0, 0], [0, 0, 0, 13, 13]], [[0, 7, 7, 13, 13], [0, 29, 29, 57, 57], [0, 0, 0, 0, 0], [0, 0, 0, 13, 13]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 0, 0, 13, 13], [0, 0, 0, 13, 13], [0, 0, 0, 0, 0], [0, 0, 0, 57, 57]]], [[[10, 10, 29, 57, 57], [7, 7, 7, 13, 13], [0, 0, 13, 13, 13], [0, 0, 0, 0, 0]], [[0, 7, 7, 13, 13], [0, 29, 29, 57, 57], [0, 13, 13, 13, 13], [0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 44, 44, 44]], [[0, 0, 0, 13, 13], [0, 0, 0, 13, 13], [0, 0, 0, 13, 13], [0, 0, 0, 0, 0]]]], [[[[0, 0, 0, 0, 0], [7, 7, 7, 13, 13], [0, 0, 13, 13, 13], [0, 0, 0, 13, 13]], [[0, 0, 0, 0, 0], [0, 29, 29, 57, 57], [0, 13, 13, 13, 13], [0, 0, 0, 13, 13]], [[0, 0, 0, 0, 0], [0, 0, 13, 13, 13], [0, 0, 57, 57, 57], [0, 0, 13, 13, 13]], [[0, 0, 0, 44, 44], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]]], [[[10, 10, 29, 57, 57], [0, 0, 0, 0, 0], [0, 0, 13, 13, 13], [0, 0, 0, 13, 13]], [[0, 7, 7, 13, 13], [0, 0, 0, 0, 0], [0, 13, 13, 13, 13], [0, 0, 0, 13, 13]], [[0, 0, 13, 13, 13], [0, 0, 0, 0, 0], [0, 0, 57, 57, 57], [0, 0, 13, 13, 13]], [[0, 0, 0, 0, 0], [0, 0, 0, 44, 44], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]]], [[[10, 10, 29, 57, 57], [7, 7, 7, 13, 13], [0, 0, 0, 0, 0], [0, 0, 0, 13, 13]], [[0, 7, 7, 13, 13], [0, 29, 29, 57, 57], [0, 0, 0, 0, 0], [0, 0, 0, 13, 13]], [[0, 0, 13, 13, 13], [0, 0, 13, 13, 13], [0, 0, 0, 0, 0], [0, 0, 13, 13, 13]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 44, 44], [0, 0, 0, 0, 0]]], [[[10, 10, 29, 57, 57], [7, 7, 7, 13, 13], [0, 0, 13, 13, 13], [0, 0, 0, 0, 0]], [[0, 7, 7, 13, 13], [0, 29, 29, 57, 57], [0, 13, 13, 13, 13], [0, 0, 0, 0, 0]], [[0, 0, 13, 13, 13], [0, 0, 13, 13, 13], [0, 0, 57, 57, 57], [0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]]]]]

/-- W(3) as a table. -/
def tab3 (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (c : ℕ) : ℕ :=
  match q with
  | none => ((LN3.getD (r 0).val []).getD (r 1).val []).getD c 0
  | some p => ((((LS3.getD (p 0).val []).getD (p 1).val []).getD (r 0).val []).getD (r 1).val []).getD c 0

/-- W(4, none, r, c) for c <= 4, nested by the entries of r and then c. -/
def LN4 : List (List (List ℕ)) :=
  [[[42, 42, 125, 249, 249], [22, 22, 22, 44, 44], [0, 0, 44, 44, 44], [0, 0, 0, 44, 44]], [[0, 22, 22, 44, 44], [0, 125, 125, 249, 249], [0, 44, 44, 44, 44], [0, 0, 0, 44, 44]], [[0, 0, 44, 44, 44], [0, 0, 44, 44, 44], [0, 0, 249, 249, 249], [0, 0, 44, 44, 44]], [[0, 0, 0, 44, 44], [0, 0, 0, 44, 44], [0, 0, 0, 44, 44], [0, 0, 0, 249, 249]]]

/-- W(4, some p, r, c) for c <= 4, nested by the entries of p, of r, and then c. -/
def LS4 : List (List (List (List (List ℕ)))) :=
  [[[[[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0], [0, 125, 125, 249, 249], [0, 44, 44, 44, 44], [0, 0, 0, 44, 44]], [[0, 0, 0, 0, 0], [0, 0, 44, 44, 44], [0, 0, 249, 249, 249], [0, 0, 44, 44, 44]], [[0, 0, 0, 0, 0], [0, 0, 0, 44, 44], [0, 0, 0, 44, 44], [0, 0, 0, 249, 249]]], [[[0, 0, 0, 0, 0], [103, 103, 103, 205, 205], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 22, 22, 44, 44], [0, 0, 0, 0, 0], [0, 44, 44, 44, 44], [0, 0, 0, 44, 44]], [[0, 0, 44, 44, 44], [0, 0, 0, 0, 0], [0, 0, 249, 249, 249], [0, 0, 44, 44, 44]], [[0, 0, 0, 44, 44], [0, 0, 0, 0, 0], [0, 0, 0, 44, 44], [0, 0, 0, 249, 249]]], [[[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 205, 205, 205], [0, 0, 0, 0, 0]], [[0, 22, 22, 44, 44], [0, 125, 125, 249, 249], [0, 0, 0, 0, 0], [0, 0, 0, 44, 44]], [[0, 0, 44, 44, 44], [0, 0, 44, 44, 44], [0, 0, 0, 0, 0], [0, 0, 44, 44, 44]], [[0, 0, 0, 44, 44], [0, 0, 0, 44, 44], [0, 0, 0, 0, 0], [0, 0, 0, 249, 249]]], [[[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 205, 205]], [[0, 22, 22, 44, 44], [0, 125, 125, 249, 249], [0, 44, 44, 44, 44], [0, 0, 0, 0, 0]], [[0, 0, 44, 44, 44], [0, 0, 44, 44, 44], [0, 0, 249, 249, 249], [0, 0, 0, 0, 0]], [[0, 0, 0, 44, 44], [0, 0, 0, 44, 44], [0, 0, 0, 44, 44], [0, 0, 0, 0, 0]]]], [[[[0, 0, 0, 0, 0], [22, 22, 22, 44, 44], [0, 0, 44, 44, 44], [0, 0, 0, 44, 44]], [[0, 103, 103, 205, 205], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0], [0, 0, 44, 44, 44], [0, 0, 249, 249, 249], [0, 0, 44, 44, 44]], [[0, 0, 0, 0, 0], [0, 0, 0, 44, 44], [0, 0, 0, 44, 44], [0, 0, 0, 249, 249]]], [[[42, 42, 125, 249, 249], [0, 0, 0, 0, 0], [0, 0, 44, 44, 44], [0, 0, 0, 44, 44]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 0, 44, 44, 44], [0, 0, 0, 0, 0], [0, 0, 249, 249, 249], [0, 0, 44, 44, 44]], [[0, 0, 0, 44, 44], [0, 0, 0, 0, 0], [0, 0, 0, 44, 44], [0, 0, 0, 249, 249]]], [[[42, 42, 125, 249, 249], [22, 22, 22, 44, 44], [0, 0, 0, 0, 0], [0, 0, 0, 44, 44]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 205, 205, 205, 205], [0, 0, 0, 0, 0]], [[0, 0, 44, 44, 44], [0, 0, 44, 44, 44], [0, 0, 0, 0, 0], [0, 0, 44, 44, 44]], [[0, 0, 0, 44, 44], [0, 0, 0, 44, 44], [0, 0, 0, 0, 0], [0, 0, 0, 249, 249]]], [[[42, 42, 125, 249, 249], [22, 22, 22, 44, 44], [0, 0, 44, 44, 44], [0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 205, 205]], [[0, 0, 44, 44, 44], [0, 0, 44, 44, 44], [0, 0, 249, 249, 249], [0, 0, 0, 0, 0]], [[0, 0, 0, 44, 44], [0, 0, 0, 44, 44], [0, 0, 0, 44, 44], [0, 0, 0, 0, 0]]]], [[[[0, 0, 0, 0, 0], [22, 22, 22, 44, 44], [0, 0, 44, 44, 44], [0, 0, 0, 44, 44]], [[0, 0, 0, 0, 0], [0, 125, 125, 249, 249], [0, 44, 44, 44, 44], [0, 0, 0, 44, 44]], [[0, 0, 205, 205, 205], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0], [0, 0, 0, 44, 44], [0, 0, 0, 44, 44], [0, 0, 0, 249, 249]]], [[[42, 42, 125, 249, 249], [0, 0, 0, 0, 0], [0, 0, 44, 44, 44], [0, 0, 0, 44, 44]], [[0, 22, 22, 44, 44], [0, 0, 0, 0, 0], [0, 44, 44, 44, 44], [0, 0, 0, 44, 44]], [[0, 0, 0, 0, 0], [0, 0, 205, 205, 205], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 0, 0, 44, 44], [0, 0, 0, 0, 0], [0, 0, 0, 44, 44], [0, 0, 0, 249, 249]]], [[[42, 42, 125, 249, 249], [22, 22, 22, 44, 44], [0, 0, 0, 0, 0], [0, 0, 0, 44, 44]], [[0, 22, 22, 44, 44], [0, 125, 125, 249, 249], [0, 0, 0, 0, 0], [0, 0, 0, 44, 44]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 0, 0, 44, 44], [0, 0, 0, 44, 44], [0, 0, 0, 0, 0], [0, 0, 0, 249, 249]]], [[[42, 42, 125, 249, 249], [22, 22, 22, 44, 44], [0, 0, 44, 44, 44], [0, 0, 0, 0, 0]], [[0, 22, 22, 44, 44], [0, 125, 125, 249, 249], [0, 44, 44, 44, 44], [0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 205, 205, 205]], [[0, 0, 0, 44, 44], [0, 0, 0, 44, 44], [0, 0, 0, 44, 44], [0, 0, 0, 0, 0]]]], [[[[0, 0, 0, 0, 0], [22, 22, 22, 44, 44], [0, 0, 44, 44, 44], [0, 0, 0, 44, 44]], [[0, 0, 0, 0, 0], [0, 125, 125, 249, 249], [0, 44, 44, 44, 44], [0, 0, 0, 44, 44]], [[0, 0, 0, 0, 0], [0, 0, 44, 44, 44], [0, 0, 249, 249, 249], [0, 0, 44, 44, 44]], [[0, 0, 0, 205, 205], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]]], [[[42, 42, 125, 249, 249], [0, 0, 0, 0, 0], [0, 0, 44, 44, 44], [0, 0, 0, 44, 44]], [[0, 22, 22, 44, 44], [0, 0, 0, 0, 0], [0, 44, 44, 44, 44], [0, 0, 0, 44, 44]], [[0, 0, 44, 44, 44], [0, 0, 0, 0, 0], [0, 0, 249, 249, 249], [0, 0, 44, 44, 44]], [[0, 0, 0, 0, 0], [0, 0, 0, 205, 205], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]]], [[[42, 42, 125, 249, 249], [22, 22, 22, 44, 44], [0, 0, 0, 0, 0], [0, 0, 0, 44, 44]], [[0, 22, 22, 44, 44], [0, 125, 125, 249, 249], [0, 0, 0, 0, 0], [0, 0, 0, 44, 44]], [[0, 0, 44, 44, 44], [0, 0, 44, 44, 44], [0, 0, 0, 0, 0], [0, 0, 44, 44, 44]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 205, 205], [0, 0, 0, 0, 0]]], [[[42, 42, 125, 249, 249], [22, 22, 22, 44, 44], [0, 0, 44, 44, 44], [0, 0, 0, 0, 0]], [[0, 22, 22, 44, 44], [0, 125, 125, 249, 249], [0, 44, 44, 44, 44], [0, 0, 0, 0, 0]], [[0, 0, 44, 44, 44], [0, 0, 44, 44, 44], [0, 0, 249, 249, 249], [0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]]]]]

/-- W(4) as a table. -/
def tab4 (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (c : ℕ) : ℕ :=
  match q with
  | none => ((LN4.getD (r 0).val []).getD (r 1).val []).getD c 0
  | some p => ((((LS4.getD (p 0).val []).getD (p 1).val []).getD (r 0).val []).getD (r 1).val []).getD c 0

/-- W(5, none, r, c) for c <= 4, nested by the entries of r and then c. -/
def LN5 : List (List (List ℕ)) :=
  [[[169, 169, 506, 1011, 1011], [103, 103, 103, 205, 205], [0, 0, 205, 205, 205], [0, 0, 0, 205, 205]], [[0, 103, 103, 205, 205], [0, 506, 506, 1011, 1011], [0, 205, 205, 205, 205], [0, 0, 0, 205, 205]], [[0, 0, 205, 205, 205], [0, 0, 205, 205, 205], [0, 0, 1011, 1011, 1011], [0, 0, 205, 205, 205]], [[0, 0, 0, 205, 205], [0, 0, 0, 205, 205], [0, 0, 0, 205, 205], [0, 0, 0, 1011, 1011]]]

/-- W(5, some p, r, c) for c <= 4, nested by the entries of p, of r, and then c. -/
def LS5 : List (List (List (List (List ℕ)))) :=
  [[[[[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0], [0, 506, 506, 1011, 1011], [0, 205, 205, 205, 205], [0, 0, 0, 205, 205]], [[0, 0, 0, 0, 0], [0, 0, 205, 205, 205], [0, 0, 1011, 1011, 1011], [0, 0, 205, 205, 205]], [[0, 0, 0, 0, 0], [0, 0, 0, 205, 205], [0, 0, 0, 205, 205], [0, 0, 0, 1011, 1011]]], [[[0, 0, 0, 0, 0], [403, 403, 403, 806, 806], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 103, 103, 205, 205], [0, 0, 0, 0, 0], [0, 205, 205, 205, 205], [0, 0, 0, 205, 205]], [[0, 0, 205, 205, 205], [0, 0, 0, 0, 0], [0, 0, 1011, 1011, 1011], [0, 0, 205, 205, 205]], [[0, 0, 0, 205, 205], [0, 0, 0, 0, 0], [0, 0, 0, 205, 205], [0, 0, 0, 1011, 1011]]], [[[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 806, 806, 806], [0, 0, 0, 0, 0]], [[0, 103, 103, 205, 205], [0, 506, 506, 1011, 1011], [0, 0, 0, 0, 0], [0, 0, 0, 205, 205]], [[0, 0, 205, 205, 205], [0, 0, 205, 205, 205], [0, 0, 0, 0, 0], [0, 0, 205, 205, 205]], [[0, 0, 0, 205, 205], [0, 0, 0, 205, 205], [0, 0, 0, 0, 0], [0, 0, 0, 1011, 1011]]], [[[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 806, 806]], [[0, 103, 103, 205, 205], [0, 506, 506, 1011, 1011], [0, 205, 205, 205, 205], [0, 0, 0, 0, 0]], [[0, 0, 205, 205, 205], [0, 0, 205, 205, 205], [0, 0, 1011, 1011, 1011], [0, 0, 0, 0, 0]], [[0, 0, 0, 205, 205], [0, 0, 0, 205, 205], [0, 0, 0, 205, 205], [0, 0, 0, 0, 0]]]], [[[[0, 0, 0, 0, 0], [103, 103, 103, 205, 205], [0, 0, 205, 205, 205], [0, 0, 0, 205, 205]], [[0, 403, 403, 806, 806], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0], [0, 0, 205, 205, 205], [0, 0, 1011, 1011, 1011], [0, 0, 205, 205, 205]], [[0, 0, 0, 0, 0], [0, 0, 0, 205, 205], [0, 0, 0, 205, 205], [0, 0, 0, 1011, 1011]]], [[[169, 169, 506, 1011, 1011], [0, 0, 0, 0, 0], [0, 0, 205, 205, 205], [0, 0, 0, 205, 205]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 0, 205, 205, 205], [0, 0, 0, 0, 0], [0, 0, 1011, 1011, 1011], [0, 0, 205, 205, 205]], [[0, 0, 0, 205, 205], [0, 0, 0, 0, 0], [0, 0, 0, 205, 205], [0, 0, 0, 1011, 1011]]], [[[169, 169, 506, 1011, 1011], [103, 103, 103, 205, 205], [0, 0, 0, 0, 0], [0, 0, 0, 205, 205]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 806, 806, 806, 806], [0, 0, 0, 0, 0]], [[0, 0, 205, 205, 205], [0, 0, 205, 205, 205], [0, 0, 0, 0, 0], [0, 0, 205, 205, 205]], [[0, 0, 0, 205, 205], [0, 0, 0, 205, 205], [0, 0, 0, 0, 0], [0, 0, 0, 1011, 1011]]], [[[169, 169, 506, 1011, 1011], [103, 103, 103, 205, 205], [0, 0, 205, 205, 205], [0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 806, 806]], [[0, 0, 205, 205, 205], [0, 0, 205, 205, 205], [0, 0, 1011, 1011, 1011], [0, 0, 0, 0, 0]], [[0, 0, 0, 205, 205], [0, 0, 0, 205, 205], [0, 0, 0, 205, 205], [0, 0, 0, 0, 0]]]], [[[[0, 0, 0, 0, 0], [103, 103, 103, 205, 205], [0, 0, 205, 205, 205], [0, 0, 0, 205, 205]], [[0, 0, 0, 0, 0], [0, 506, 506, 1011, 1011], [0, 205, 205, 205, 205], [0, 0, 0, 205, 205]], [[0, 0, 806, 806, 806], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0], [0, 0, 0, 205, 205], [0, 0, 0, 205, 205], [0, 0, 0, 1011, 1011]]], [[[169, 169, 506, 1011, 1011], [0, 0, 0, 0, 0], [0, 0, 205, 205, 205], [0, 0, 0, 205, 205]], [[0, 103, 103, 205, 205], [0, 0, 0, 0, 0], [0, 205, 205, 205, 205], [0, 0, 0, 205, 205]], [[0, 0, 0, 0, 0], [0, 0, 806, 806, 806], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 0, 0, 205, 205], [0, 0, 0, 0, 0], [0, 0, 0, 205, 205], [0, 0, 0, 1011, 1011]]], [[[169, 169, 506, 1011, 1011], [103, 103, 103, 205, 205], [0, 0, 0, 0, 0], [0, 0, 0, 205, 205]], [[0, 103, 103, 205, 205], [0, 506, 506, 1011, 1011], [0, 0, 0, 0, 0], [0, 0, 0, 205, 205]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 0, 0, 205, 205], [0, 0, 0, 205, 205], [0, 0, 0, 0, 0], [0, 0, 0, 1011, 1011]]], [[[169, 169, 506, 1011, 1011], [103, 103, 103, 205, 205], [0, 0, 205, 205, 205], [0, 0, 0, 0, 0]], [[0, 103, 103, 205, 205], [0, 506, 506, 1011, 1011], [0, 205, 205, 205, 205], [0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 806, 806, 806]], [[0, 0, 0, 205, 205], [0, 0, 0, 205, 205], [0, 0, 0, 205, 205], [0, 0, 0, 0, 0]]]], [[[[0, 0, 0, 0, 0], [103, 103, 103, 205, 205], [0, 0, 205, 205, 205], [0, 0, 0, 205, 205]], [[0, 0, 0, 0, 0], [0, 506, 506, 1011, 1011], [0, 205, 205, 205, 205], [0, 0, 0, 205, 205]], [[0, 0, 0, 0, 0], [0, 0, 205, 205, 205], [0, 0, 1011, 1011, 1011], [0, 0, 205, 205, 205]], [[0, 0, 0, 806, 806], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]]], [[[169, 169, 506, 1011, 1011], [0, 0, 0, 0, 0], [0, 0, 205, 205, 205], [0, 0, 0, 205, 205]], [[0, 103, 103, 205, 205], [0, 0, 0, 0, 0], [0, 205, 205, 205, 205], [0, 0, 0, 205, 205]], [[0, 0, 205, 205, 205], [0, 0, 0, 0, 0], [0, 0, 1011, 1011, 1011], [0, 0, 205, 205, 205]], [[0, 0, 0, 0, 0], [0, 0, 0, 806, 806], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]]], [[[169, 169, 506, 1011, 1011], [103, 103, 103, 205, 205], [0, 0, 0, 0, 0], [0, 0, 0, 205, 205]], [[0, 103, 103, 205, 205], [0, 506, 506, 1011, 1011], [0, 0, 0, 0, 0], [0, 0, 0, 205, 205]], [[0, 0, 205, 205, 205], [0, 0, 205, 205, 205], [0, 0, 0, 0, 0], [0, 0, 205, 205, 205]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 806, 806], [0, 0, 0, 0, 0]]], [[[169, 169, 506, 1011, 1011], [103, 103, 103, 205, 205], [0, 0, 205, 205, 205], [0, 0, 0, 0, 0]], [[0, 103, 103, 205, 205], [0, 506, 506, 1011, 1011], [0, 205, 205, 205, 205], [0, 0, 0, 0, 0]], [[0, 0, 205, 205, 205], [0, 0, 205, 205, 205], [0, 0, 1011, 1011, 1011], [0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]]]]]

/-- W(5) as a table. -/
def tab5 (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (c : ℕ) : ℕ :=
  match q with
  | none => ((LN5.getD (r 0).val []).getD (r 1).val []).getD c 0
  | some p => ((((LS5.getD (p 0).val []).getD (p 1).val []).getD (r 0).val []).getD (r 1).val []).getD c 0

/-- W(6, none, r, c) for c <= 4, nested by the entries of r and then c. -/
def LN6 : List (List (List ℕ)) :=
  [[[711, 711, 2132, 4263, 4263], [403, 403, 403, 806, 806], [0, 0, 806, 806, 806], [0, 0, 0, 806, 806]], [[0, 403, 403, 806, 806], [0, 2132, 2132, 4263, 4263], [0, 806, 806, 806, 806], [0, 0, 0, 806, 806]], [[0, 0, 806, 806, 806], [0, 0, 806, 806, 806], [0, 0, 4263, 4263, 4263], [0, 0, 806, 806, 806]], [[0, 0, 0, 806, 806], [0, 0, 0, 806, 806], [0, 0, 0, 806, 806], [0, 0, 0, 4263, 4263]]]

/-- W(6, some p, r, c) for c <= 4, nested by the entries of p, of r, and then c. -/
def LS6 : List (List (List (List (List ℕ)))) :=
  [[[[[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0], [0, 2132, 2132, 4263, 4263], [0, 806, 806, 806, 806], [0, 0, 0, 806, 806]], [[0, 0, 0, 0, 0], [0, 0, 806, 806, 806], [0, 0, 4263, 4263, 4263], [0, 0, 806, 806, 806]], [[0, 0, 0, 0, 0], [0, 0, 0, 806, 806], [0, 0, 0, 806, 806], [0, 0, 0, 4263, 4263]]], [[[0, 0, 0, 0, 0], [1729, 1729, 1729, 3457, 3457], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 403, 403, 806, 806], [0, 0, 0, 0, 0], [0, 806, 806, 806, 806], [0, 0, 0, 806, 806]], [[0, 0, 806, 806, 806], [0, 0, 0, 0, 0], [0, 0, 4263, 4263, 4263], [0, 0, 806, 806, 806]], [[0, 0, 0, 806, 806], [0, 0, 0, 0, 0], [0, 0, 0, 806, 806], [0, 0, 0, 4263, 4263]]], [[[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 3457, 3457, 3457], [0, 0, 0, 0, 0]], [[0, 403, 403, 806, 806], [0, 2132, 2132, 4263, 4263], [0, 0, 0, 0, 0], [0, 0, 0, 806, 806]], [[0, 0, 806, 806, 806], [0, 0, 806, 806, 806], [0, 0, 0, 0, 0], [0, 0, 806, 806, 806]], [[0, 0, 0, 806, 806], [0, 0, 0, 806, 806], [0, 0, 0, 0, 0], [0, 0, 0, 4263, 4263]]], [[[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 3457, 3457]], [[0, 403, 403, 806, 806], [0, 2132, 2132, 4263, 4263], [0, 806, 806, 806, 806], [0, 0, 0, 0, 0]], [[0, 0, 806, 806, 806], [0, 0, 806, 806, 806], [0, 0, 4263, 4263, 4263], [0, 0, 0, 0, 0]], [[0, 0, 0, 806, 806], [0, 0, 0, 806, 806], [0, 0, 0, 806, 806], [0, 0, 0, 0, 0]]]], [[[[0, 0, 0, 0, 0], [403, 403, 403, 806, 806], [0, 0, 806, 806, 806], [0, 0, 0, 806, 806]], [[0, 1729, 1729, 3457, 3457], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0], [0, 0, 806, 806, 806], [0, 0, 4263, 4263, 4263], [0, 0, 806, 806, 806]], [[0, 0, 0, 0, 0], [0, 0, 0, 806, 806], [0, 0, 0, 806, 806], [0, 0, 0, 4263, 4263]]], [[[711, 711, 2132, 4263, 4263], [0, 0, 0, 0, 0], [0, 0, 806, 806, 806], [0, 0, 0, 806, 806]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 0, 806, 806, 806], [0, 0, 0, 0, 0], [0, 0, 4263, 4263, 4263], [0, 0, 806, 806, 806]], [[0, 0, 0, 806, 806], [0, 0, 0, 0, 0], [0, 0, 0, 806, 806], [0, 0, 0, 4263, 4263]]], [[[711, 711, 2132, 4263, 4263], [403, 403, 403, 806, 806], [0, 0, 0, 0, 0], [0, 0, 0, 806, 806]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 3457, 3457, 3457, 3457], [0, 0, 0, 0, 0]], [[0, 0, 806, 806, 806], [0, 0, 806, 806, 806], [0, 0, 0, 0, 0], [0, 0, 806, 806, 806]], [[0, 0, 0, 806, 806], [0, 0, 0, 806, 806], [0, 0, 0, 0, 0], [0, 0, 0, 4263, 4263]]], [[[711, 711, 2132, 4263, 4263], [403, 403, 403, 806, 806], [0, 0, 806, 806, 806], [0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 3457, 3457]], [[0, 0, 806, 806, 806], [0, 0, 806, 806, 806], [0, 0, 4263, 4263, 4263], [0, 0, 0, 0, 0]], [[0, 0, 0, 806, 806], [0, 0, 0, 806, 806], [0, 0, 0, 806, 806], [0, 0, 0, 0, 0]]]], [[[[0, 0, 0, 0, 0], [403, 403, 403, 806, 806], [0, 0, 806, 806, 806], [0, 0, 0, 806, 806]], [[0, 0, 0, 0, 0], [0, 2132, 2132, 4263, 4263], [0, 806, 806, 806, 806], [0, 0, 0, 806, 806]], [[0, 0, 3457, 3457, 3457], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0], [0, 0, 0, 806, 806], [0, 0, 0, 806, 806], [0, 0, 0, 4263, 4263]]], [[[711, 711, 2132, 4263, 4263], [0, 0, 0, 0, 0], [0, 0, 806, 806, 806], [0, 0, 0, 806, 806]], [[0, 403, 403, 806, 806], [0, 0, 0, 0, 0], [0, 806, 806, 806, 806], [0, 0, 0, 806, 806]], [[0, 0, 0, 0, 0], [0, 0, 3457, 3457, 3457], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 0, 0, 806, 806], [0, 0, 0, 0, 0], [0, 0, 0, 806, 806], [0, 0, 0, 4263, 4263]]], [[[711, 711, 2132, 4263, 4263], [403, 403, 403, 806, 806], [0, 0, 0, 0, 0], [0, 0, 0, 806, 806]], [[0, 403, 403, 806, 806], [0, 2132, 2132, 4263, 4263], [0, 0, 0, 0, 0], [0, 0, 0, 806, 806]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], [[0, 0, 0, 806, 806], [0, 0, 0, 806, 806], [0, 0, 0, 0, 0], [0, 0, 0, 4263, 4263]]], [[[711, 711, 2132, 4263, 4263], [403, 403, 403, 806, 806], [0, 0, 806, 806, 806], [0, 0, 0, 0, 0]], [[0, 403, 403, 806, 806], [0, 2132, 2132, 4263, 4263], [0, 806, 806, 806, 806], [0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 3457, 3457, 3457]], [[0, 0, 0, 806, 806], [0, 0, 0, 806, 806], [0, 0, 0, 806, 806], [0, 0, 0, 0, 0]]]], [[[[0, 0, 0, 0, 0], [403, 403, 403, 806, 806], [0, 0, 806, 806, 806], [0, 0, 0, 806, 806]], [[0, 0, 0, 0, 0], [0, 2132, 2132, 4263, 4263], [0, 806, 806, 806, 806], [0, 0, 0, 806, 806]], [[0, 0, 0, 0, 0], [0, 0, 806, 806, 806], [0, 0, 4263, 4263, 4263], [0, 0, 806, 806, 806]], [[0, 0, 0, 3457, 3457], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]]], [[[711, 711, 2132, 4263, 4263], [0, 0, 0, 0, 0], [0, 0, 806, 806, 806], [0, 0, 0, 806, 806]], [[0, 403, 403, 806, 806], [0, 0, 0, 0, 0], [0, 806, 806, 806, 806], [0, 0, 0, 806, 806]], [[0, 0, 806, 806, 806], [0, 0, 0, 0, 0], [0, 0, 4263, 4263, 4263], [0, 0, 806, 806, 806]], [[0, 0, 0, 0, 0], [0, 0, 0, 3457, 3457], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]]], [[[711, 711, 2132, 4263, 4263], [403, 403, 403, 806, 806], [0, 0, 0, 0, 0], [0, 0, 0, 806, 806]], [[0, 403, 403, 806, 806], [0, 2132, 2132, 4263, 4263], [0, 0, 0, 0, 0], [0, 0, 0, 806, 806]], [[0, 0, 806, 806, 806], [0, 0, 806, 806, 806], [0, 0, 0, 0, 0], [0, 0, 806, 806, 806]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 3457, 3457], [0, 0, 0, 0, 0]]], [[[711, 711, 2132, 4263, 4263], [403, 403, 403, 806, 806], [0, 0, 806, 806, 806], [0, 0, 0, 0, 0]], [[0, 403, 403, 806, 806], [0, 2132, 2132, 4263, 4263], [0, 806, 806, 806, 806], [0, 0, 0, 0, 0]], [[0, 0, 806, 806, 806], [0, 0, 806, 806, 806], [0, 0, 4263, 4263, 4263], [0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]]]]]

/-- W(6) as a table. -/
def tab6 (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (c : ℕ) : ℕ :=
  match q with
  | none => ((LN6.getD (r 0).val []).getD (r 1).val []).getD c 0
  | some p => ((((LS6.getD (p 0).val []).getD (p 1).val []).getD (r 0).val []).getD (r 1).val []).getD c 0

lemma checkN1 : ∀ y1 y2 : Fin 4, ∀ c : Fin 5,
    T W0f none ![y1, y2] c.val = tab1 none ![y1, y2] c.val := by
  decide +kernel

lemma checkS1 : ∀ p1 p2 : Fin 4, ∀ y1 y2 : Fin 4, ∀ c : Fin 5,
    T W0f (some ![p1, p2]) ![y1, y2] c.val = tab1 (some ![p1, p2]) ![y1, y2] c.val := by
  decide +kernel

lemma checkN2 : ∀ y1 y2 : Fin 4, ∀ c : Fin 5,
    T tab1 none ![y1, y2] c.val = tab2 none ![y1, y2] c.val := by
  decide +kernel

lemma checkS2 : ∀ p1 p2 : Fin 4, ∀ y1 y2 : Fin 4, ∀ c : Fin 5,
    T tab1 (some ![p1, p2]) ![y1, y2] c.val = tab2 (some ![p1, p2]) ![y1, y2] c.val := by
  decide +kernel

lemma checkN3 : ∀ y1 y2 : Fin 4, ∀ c : Fin 5,
    T tab2 none ![y1, y2] c.val = tab3 none ![y1, y2] c.val := by
  decide +kernel

lemma checkS3 : ∀ p1 p2 : Fin 4, ∀ y1 y2 : Fin 4, ∀ c : Fin 5,
    T tab2 (some ![p1, p2]) ![y1, y2] c.val = tab3 (some ![p1, p2]) ![y1, y2] c.val := by
  decide +kernel

lemma checkN4 : ∀ y1 y2 : Fin 4, ∀ c : Fin 5,
    T tab3 none ![y1, y2] c.val = tab4 none ![y1, y2] c.val := by
  decide +kernel

lemma checkS4 : ∀ p1 p2 : Fin 4, ∀ y1 y2 : Fin 4, ∀ c : Fin 5,
    T tab3 (some ![p1, p2]) ![y1, y2] c.val = tab4 (some ![p1, p2]) ![y1, y2] c.val := by
  decide +kernel

lemma checkN5 : ∀ y1 y2 : Fin 4, ∀ c : Fin 5,
    T tab4 none ![y1, y2] c.val = tab5 none ![y1, y2] c.val := by
  decide +kernel

lemma checkS5 : ∀ p1 p2 : Fin 4, ∀ y1 y2 : Fin 4, ∀ c : Fin 5,
    T tab4 (some ![p1, p2]) ![y1, y2] c.val = tab5 (some ![p1, p2]) ![y1, y2] c.val := by
  decide +kernel

lemma checkN6 : ∀ y1 y2 : Fin 4, ∀ c : Fin 5,
    T tab5 none ![y1, y2] c.val = tab6 none ![y1, y2] c.val := by
  decide +kernel

lemma checkS6 : ∀ p1 p2 : Fin 4, ∀ y1 y2 : Fin 4, ∀ c : Fin 5,
    T tab5 (some ![p1, p2]) ![y1, y2] c.val = tab6 (some ![p1, p2]) ![y1, y2] c.val := by
  decide +kernel

lemma checkN_rel : ∀ y1 y2 : Fin 4, ∀ c : Fin 5,
    T tab6 none ![y1, y2] c.val + 103 * tab3 none ![y1, y2] c.val =
      23 * tab5 none ![y1, y2] c.val + 81 * tab1 none ![y1, y2] c.val := by
  decide +kernel

lemma checkS_rel : ∀ p1 p2 : Fin 4, ∀ y1 y2 : Fin 4, ∀ c : Fin 5,
    T tab6 (some ![p1, p2]) ![y1, y2] c.val + 103 * tab3 (some ![p1, p2]) ![y1, y2] c.val =
      23 * tab5 (some ![p1, p2]) ![y1, y2] c.val + 81 * tab1 (some ![p1, p2]) ![y1, y2] c.val := by
  decide +kernel

lemma W_1 (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (c : ℕ) (hc : c ≤ 4) :
    W 1 q r c = tab1 q r c := by
  rw [W_succT, W_zero_fun]
  rcases q with _ | p
  · rw [row_eta r]
    exact checkN1 (r 0) (r 1) ⟨c, by omega⟩
  · rw [row_eta p, row_eta r]
    exact checkS1 (p 0) (p 1) (r 0) (r 1) ⟨c, by omega⟩

lemma W_2 (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (c : ℕ) (hc : c ≤ 4) :
    W 2 q r c = tab2 q r c := by
  rw [show W 2 q r c = W (1 + 1) q r c from rfl, W_succT,
    T_congr _ tab1 q r c (fun s => W_1 _ s _ (newc_le c hc r))]
  rcases q with _ | p
  · rw [row_eta r]
    exact checkN2 (r 0) (r 1) ⟨c, by omega⟩
  · rw [row_eta p, row_eta r]
    exact checkS2 (p 0) (p 1) (r 0) (r 1) ⟨c, by omega⟩

lemma W_3 (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (c : ℕ) (hc : c ≤ 4) :
    W 3 q r c = tab3 q r c := by
  rw [show W 3 q r c = W (2 + 1) q r c from rfl, W_succT,
    T_congr _ tab2 q r c (fun s => W_2 _ s _ (newc_le c hc r))]
  rcases q with _ | p
  · rw [row_eta r]
    exact checkN3 (r 0) (r 1) ⟨c, by omega⟩
  · rw [row_eta p, row_eta r]
    exact checkS3 (p 0) (p 1) (r 0) (r 1) ⟨c, by omega⟩

lemma W_4 (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (c : ℕ) (hc : c ≤ 4) :
    W 4 q r c = tab4 q r c := by
  rw [show W 4 q r c = W (3 + 1) q r c from rfl, W_succT,
    T_congr _ tab3 q r c (fun s => W_3 _ s _ (newc_le c hc r))]
  rcases q with _ | p
  · rw [row_eta r]
    exact checkN4 (r 0) (r 1) ⟨c, by omega⟩
  · rw [row_eta p, row_eta r]
    exact checkS4 (p 0) (p 1) (r 0) (r 1) ⟨c, by omega⟩

lemma W_5 (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (c : ℕ) (hc : c ≤ 4) :
    W 5 q r c = tab5 q r c := by
  rw [show W 5 q r c = W (4 + 1) q r c from rfl, W_succT,
    T_congr _ tab4 q r c (fun s => W_4 _ s _ (newc_le c hc r))]
  rcases q with _ | p
  · rw [row_eta r]
    exact checkN5 (r 0) (r 1) ⟨c, by omega⟩
  · rw [row_eta p, row_eta r]
    exact checkS5 (p 0) (p 1) (r 0) (r 1) ⟨c, by omega⟩

lemma W_6 (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (c : ℕ) (hc : c ≤ 4) :
    W 6 q r c = tab6 q r c := by
  rw [show W 6 q r c = W (5 + 1) q r c from rfl, W_succT,
    T_congr _ tab5 q r c (fun s => W_5 _ s _ (newc_le c hc r))]
  rcases q with _ | p
  · rw [row_eta r]
    exact checkN6 (r 0) (r 1) ⟨c, by omega⟩
  · rw [row_eta p, row_eta r]
    exact checkS6 (p 0) (p 1) (r 0) (r 1) ⟨c, by omega⟩

lemma W_rec (n : ℕ) : ∀ (q : Option (Fin 2 → Fin 4)) (r : Fin 2 → Fin 4) (c : ℕ), c ≤ 4 →
    W (n + 7) q r c + 103 * W (n + 3) q r c = 23 * W (n + 5) q r c + 81 * W (n + 1) q r c := by
  induction n with
  | zero =>
    intro q r c hc
    rw [show W (0 + 7) q r c = W (6 + 1) q r c from rfl, W_succT 6 q r c,
      T_congr _ tab6 q r c (fun s => W_6 _ s _ (newc_le c hc r)),
      show W (0 + 1) q r c = W 1 q r c from rfl, W_1 q r c hc,
      show W (0 + 3) q r c = W 3 q r c from rfl, W_3 q r c hc,
      show W (0 + 5) q r c = W 5 q r c from rfl, W_5 q r c hc]
    rcases q with _ | p
    · rw [row_eta r]
      exact checkN_rel (r 0) (r 1) ⟨c, by omega⟩
    · rw [row_eta p, row_eta r]
      exact checkS_rel (p 0) (p 1) (r 0) (r 1) ⟨c, by omega⟩
  | succ n ih =>
    intro q r c hc
    rw [W_succT (n + 7), W_succT (n + 5), W_succT (n + 3), W_succT (n + 1)]
    unfold T
    split_ifs with h
    · rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      split_ifs
      · exact ih _ _ _ (newc_le c hc r)
      · simp
    · simp

lemma a_eq (n : ℕ) : a (n + 1) = ∑ r : Fin 2 → Fin 4, W (2 * n + 1) none r 0 := by
  unfold a W
  rw [Finset.card_eq_sum_card_fiberwise (f := fun f => f 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Finset.filter_filter]
  refine congrArg Finset.card (Finset.filter_congr (fun f _ => ?_))
  rw [cond_iff, rmn_iff, and_assoc]

lemma a_rec (n : ℕ) : a (n + 4) + 103 * a (n + 2) = 23 * a (n + 3) + 81 * a (n + 1) := by
  rw [a_eq (n + 3), a_eq (n + 2), a_eq (n + 1), a_eq n, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [show 2 * (n + 3) + 1 = 2 * n + 7 by ring, show 2 * (n + 2) + 1 = 2 * n + 5 by ring, show 2 * (n + 1) + 1 = 2 * n + 3 by ring]
  exact W_rec (2 * n) none r 0 (by norm_num)

lemma a_one : a 1 = 2 := by
  have h : ∀ r, W 1 none r 0 = tab1 none r 0 := fun r => W_1 none r 0 (by norm_num)
  rw [a_eq 0, sum_row]
  simp only [h]
  decide +kernel

lemma a_two : a 2 = 17 := by
  have h : ∀ r, W 3 none r 0 = tab3 none r 0 := fun r => W_3 none r 0 (by norm_num)
  rw [a_eq 1, sum_row]
  simp only [h]
  decide +kernel

lemma a_three : a 3 = 272 := by
  have h : ∀ r, W 5 none r 0 = tab5 none r 0 := fun r => W_5 none r 0 (by norm_num)
  rw [a_eq 2, sum_row]
  simp only [h]
  decide +kernel

/-- Barker's g.f.: Sum_{n >= 1} a(n) x^n = x(2 - 29x + 87x^2) / ((1 - x)(1 - 22x + 81x^2)). -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - X) * (1 - 22 * X + 81 * X ^ 2)) = X * (2 - 29 * X + 87 * X ^ 2) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - X) * (1 - 22 * X + 81 * X ^ 2)) = A - A * X ^ 1 * C 23 + A * X ^ 2 * C 103 - A * X ^ 3 * C 81 := by
    rw [show (C (23 : ℚ) : ℚ⟦X⟧) = 23 from map_ofNat C 23,
      show (C (81 : ℚ) : ℚ⟦X⟧) = 81 from map_ofNat C 81,
      show (C (103 : ℚ) : ℚ⟦X⟧) = 103 from map_ofNat C 103]
    ring
  have e2 : (X * (2 - 29 * X + 87 * X ^ 2) : ℚ⟦X⟧) = X ^ 1 * C 2 - X ^ 2 * C 29 + X ^ 3 * C 87 := by
    rw [show (C (2 : ℚ) : ℚ⟦X⟧) = 2 from map_ofNat C 2,
      show (C (29 : ℚ) : ℚ⟦X⟧) = 29 from map_ofNat C 29,
      show (C (87 : ℚ) : ℚ⟦X⟧) = 87 from map_ofNat C 87]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk]
  rcases n with _ | _ | _ | _ | n
  · simp
  · simp [a_one] <;> norm_num
  · simp [a_one, a_two] <;> norm_num
  · simp [a_one, a_two, a_three] <;> norm_num
  · have h := a_rec n
    
    have hq : (a (n + 4) : ℚ) + 103 * (a (n + 2) : ℚ) = 23 * (a (n + 3) : ℚ) + 81 * (a (n + 1) : ℚ) := by exact_mod_cast h
    simp only [show ¬ (n + 4 = 0) by omega,
      if_false,
      if_true,
      show 1 ≤ n + 4 by omega,
      show n + 4 - 1 = n + 3 by omega,
      show ¬ (n + 3 = 0) by omega,
      show 2 ≤ n + 4 by omega,
      show n + 4 - 2 = n + 2 by omega,
      show ¬ (n + 2 = 0) by omega,
      show 3 ≤ n + 4 by omega,
      show n + 4 - 3 = n + 1 by omega,
      show ¬ (n + 1 = 0) by omega,
      show ¬ (n + 4 = 1) by omega,
      show ¬ (n + 4 = 2) by omega,
      show ¬ (n + 4 = 3) by omega]
    linear_combination hq

theorem cf (b : ℕ → ℕ) (h1 : b 1 = 2) (h2 : b 2 = 17) (h3 : b 3 = 272)
    (hr : ∀ n, b (n + 4) + 103 * b (n + 2) = 23 * b (n + 3) + 81 * b (n + 1)) :
    ∀ n : ℕ, 1 ≤ n → (b n : ℝ) =
      (216 - (11 - 2 * Real.sqrt 10) ^ n * (-8 + Real.sqrt 10) +
        (8 + Real.sqrt 10) * (11 + 2 * Real.sqrt 10) ^ n) / 216 := by
  have s2 : Real.sqrt 10 ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  set s := Real.sqrt 10 with hsdef
  have hinh : ∀ n, (b (n + 3) : ℝ) = 22 * b (n + 2) - 81 * b (n + 1) + 60 := by
    intro n
    induction n with
    | zero => rw [h3, h2, h1]; norm_num
    | succ n ih =>
      have h := hr n
      have hq : ((b (n + 4) : ℕ) : ℝ) + 103 * b (n + 2) = 23 * b (n + 3) + 81 * b (n + 1) := by
        exact_mod_cast h
      rw [show n + 1 + 3 = n + 4 from rfl, show n + 1 + 2 = n + 3 from rfl,
        show n + 1 + 1 = n + 2 from rfl]
      linear_combination hq + ih
  set G : ℕ → ℝ := fun n => -((11 - 2 * s) ^ n * (-8 + s)) + (8 + s) * (11 + 2 * s) ^ n with hG
  have Grec : ∀ n, G (n + 2) = 22 * G (n + 1) - 81 * G n := by
    intro n
    simp only [hG]
    have e1 : (11 - 2 * s) ^ 2 = 22 * (11 - 2 * s) - 81 := by linear_combination 4 * s2
    have e2 : (11 + 2 * s) ^ 2 = 22 * (11 + 2 * s) - 81 := by linear_combination 4 * s2
    rw [show (11 - 2 * s) ^ (n + 2) = (11 - 2 * s) ^ n * (11 - 2 * s) ^ 2 by ring,
      show (11 + 2 * s) ^ (n + 2) = (11 + 2 * s) ^ n * (11 + 2 * s) ^ 2 by ring, e1, e2]
    ring
  have G0 : G 0 = 16 := by simp only [hG]; ring
  have G1 : G 1 = 216 := by simp only [hG]; linear_combination 4 * s2
  have key : ∀ k, G (k + 1) = ((b (k + 1) : ℝ) - 1) * 216 ∧
      G (k + 2) = ((b (k + 2) : ℝ) - 1) * 216 := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [G1, h1]; push_cast; ring
      · rw [Grec, G1, G0, h2]; push_cast; ring
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have hi := hinh k
      rw [show k + 1 + 2 = (k + 1) + 2 from rfl, Grec, show k + 1 + 1 = k + 2 from rfl,
        show k + 1 + 2 = k + 3 from rfl]
      linear_combination 22 * ih.2 - 81 * ih.1 - 216 * hi
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hk := (key k).1
  have e : (216 : ℝ) - (11 - 2 * s) ^ (k + 1) * (-8 + s) + (8 + s) * (11 + 2 * s) ^ (k + 1) =
      216 + G (k + 1) := by simp only [hG]; ring
  rw [e, hk]
  ring

/-- Barker's closed form. -/
theorem closed_form : ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (216 - (11 - 2 * Real.sqrt 10) ^ n * (-8 + Real.sqrt 10) +
        (8 + Real.sqrt 10) * (11 + 2 * Real.sqrt 10) ^ n) / 216 :=
  cf a a_one a_two a_three a_rec

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 - 22 * X + 81 * X ^ 2)) = X * (2 - 29 * X + 87 * X ^ 2) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (216 - (11 - 2 * Real.sqrt 10) ^ n * (-8 + Real.sqrt 10) +
        (8 + Real.sqrt 10) * (11 + 2 * Real.sqrt 10) ^ n) / 216 :=
  ⟨gf, closed_form⟩

/-- Controls: the entry's terms a(1..10), from the recurrence and the first values. -/
theorem controls : a 1 = 2 ∧ a 2 = 17 ∧ a 3 = 272 ∧ a 4 = 4667 ∧ a 5 = 80702 ∧ a 6 = 1397477 ∧ a 7 = 24207692 ∧ a 8 = 419373647 ∧ a 9 = 7265397242 ∧ a 10 = 125869473977 := by
  have r0 := a_rec 0; have r1 := a_rec 1; have r2 := a_rec 2; have r3 := a_rec 3; have r4 := a_rec 4; have r5 := a_rec 5; have r6 := a_rec 6
  have h1 := a_one; have h2 := a_two; have h3 := a_three
  norm_num at r0 r1 r2 r3 r4 r5 r6
  omega

end OMA.S_oeis_a198287

theorem OMA.solution : type_of% @OMA.S_oeis_a198287.main :=
  OMA.S_oeis_a198287.conjecture
