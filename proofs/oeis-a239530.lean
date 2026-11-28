import OMAStatements.S_oeis_a239530

namespace OMA.S_oeis_a239530

open PowerSeries Finset


instance {R C K : ℕ} : DecidablePred (@RowMajorNew R C K) := fun x => by
  unfold RowMajorNew; infer_instance


instance {R C K : ℕ} : DecidablePred (@Cond R C K) := fun x => by
  unfold Cond; infer_instance


/-! ## Rows -/

/-- 1 when the row q exists and its entry j equals r j. -/
def vEq (q : Option (Fin 2 → Fin 3)) (r : Fin 2 → Fin 3) (j : Fin 2) : ℕ :=
  match q with
  | none => 0
  | some p => if p j = r j then 1 else 0

/-- The condition on the row r with the row q above it and the row s below it. -/
def rowCond (q : Option (Fin 2 → Fin 3)) (r : Fin 2 → Fin 3) (s : Option (Fin 2 → Fin 3)) : Prop :=
  ∀ j, ¬ (∀ j' : Fin 2, (j'.val + 1 = j.val ∨ j.val + 1 = j'.val) → r j' = r j) ∧
    0 < vEq q r j + vEq s r j

instance (q : Option (Fin 2 → Fin 3)) (r : Fin 2 → Fin 3) (s : Option (Fin 2 → Fin 3)) : Decidable (rowCond q r s) := by
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
def prevRow {n : ℕ} (q : Option (Fin 2 → Fin 3)) (g : Fin n → Fin 2 → Fin 3) (i : Fin n) : Option (Fin 2 → Fin 3) :=
  match i with
  | ⟨0, _⟩ => q
  | ⟨k + 1, h⟩ => some (g ⟨k, Nat.lt_of_succ_lt h⟩)

/-- The row below row i of g, none for the last row. -/
def nextRow {n : ℕ} (g : Fin n → Fin 2 → Fin 3) (i : Fin n) : Option (Fin 2 → Fin 3) :=
  if h : i.val + 1 < n then some (g ⟨i.val + 1, h⟩) else none

/-- Every row of g satisfies the condition with the rows above and below it; q is the row above
the first row. -/
def ValidFrom {n : ℕ} (q : Option (Fin 2 → Fin 3)) (g : Fin n → Fin 2 → Fin 3) : Prop :=
  ∀ i, rowCond (prevRow q g i) (g i) (nextRow g i)

instance {n : ℕ} (q : Option (Fin 2 → Fin 3)) : DecidablePred (@ValidFrom n q) := fun g => by
  unfold ValidFrom; infer_instance

lemma validFrom_one (q : Option (Fin 2 → Fin 3)) (g : Fin 1 → Fin 2 → Fin 3) :
    ValidFrom q g ↔ rowCond q (g 0) none := by
  constructor
  · intro h
    exact h 0
  · intro h i
    have hi : i = 0 := Fin.fin_one_eq_zero i
    subst hi
    exact h

lemma prevRow_cons_zero {n : ℕ} (q : Option (Fin 2 → Fin 3)) (r : Fin 2 → Fin 3) (h : Fin (n + 1) → Fin 2 → Fin 3) :
    prevRow q (Fin.cons r h : Fin (n + 2) → Fin 2 → Fin 3) 0 = q := rfl

lemma prevRow_cons_succ {n : ℕ} (q : Option (Fin 2 → Fin 3)) (r : Fin 2 → Fin 3) (h : Fin (n + 1) → Fin 2 → Fin 3)
    (k : Fin (n + 1)) :
    prevRow q (Fin.cons r h : Fin (n + 2) → Fin 2 → Fin 3) k.succ = prevRow (some r) h k := by
  rcases k with ⟨_ | j, hk⟩ <;> rfl

lemma nextRow_cons_zero {n : ℕ} (r : Fin 2 → Fin 3) (h : Fin (n + 1) → Fin 2 → Fin 3) :
    nextRow (Fin.cons r h : Fin (n + 2) → Fin 2 → Fin 3) 0 = some (h 0) := by
  unfold nextRow
  rw [dif_pos (by simp)]
  rfl

lemma nextRow_cons_succ {n : ℕ} (r : Fin 2 → Fin 3) (h : Fin (n + 1) → Fin 2 → Fin 3) (k : Fin (n + 1)) :
    nextRow (Fin.cons r h : Fin (n + 2) → Fin 2 → Fin 3) k.succ = nextRow h k := by
  unfold nextRow
  by_cases hk : k.val + 1 < n + 1
  · rw [dif_pos (by simp; omega), dif_pos hk]
    rfl
  · rw [dif_neg (by simp; omega), dif_neg hk]

lemma validFrom_cons {n : ℕ} (q : Option (Fin 2 → Fin 3)) (r : Fin 2 → Fin 3) (h : Fin (n + 1) → Fin 2 → Fin 3) :
    ValidFrom q (Fin.cons r h : Fin (n + 2) → Fin 2 → Fin 3) ↔
      rowCond q r (some (h 0)) ∧ ValidFrom (some r) h := by
  unfold ValidFrom
  rw [Fin.forall_fin_succ]
  simp only [prevRow_cons_zero, prevRow_cons_succ, nextRow_cons_zero, nextRow_cons_succ,
    Fin.cons_zero, Fin.cons_succ]

/-! ## Counting by the first row -/

/-- W(n, q, r, c): arrays with n + 1 rows, first row r with the row q above it, every row
satisfying the condition, values introduced in row major order after the values below c. -/
def W (n : ℕ) (q : Option (Fin 2 → Fin 3)) (r : Fin 2 → Fin 3) (c : ℕ) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 2 → Fin 3)).filter
    (fun g => ValidFrom q g ∧ RGSfrom c g ∧ g 0 = r)).card

lemma W_zero (q : Option (Fin 2 → Fin 3)) (r : Fin 2 → Fin 3) (c : ℕ) :
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
def consEmb (n : ℕ) (r : Fin 2 → Fin 3) :
    (Fin (n + 1) → Fin 2 → Fin 3) ↪ (Fin (n + 2) → Fin 2 → Fin 3) where
  toFun g := Fin.cons r g
  inj' g g' h := by
    funext i
    have := congrFun h i.succ
    simpa using this

lemma consEmb_apply (n : ℕ) (r : Fin 2 → Fin 3) (g : Fin (n + 1) → Fin 2 → Fin 3) :
    consEmb n r g = Fin.cons r g := rfl

lemma W_succ (n : ℕ) (q : Option (Fin 2 → Fin 3)) (r : Fin 2 → Fin 3) (c : ℕ) :
    W (n + 1) q r c = if rowRgs c r then
      ∑ s : Fin 2 → Fin 3, (if rowCond q r (some s) then W n (some r) s (newc c r) else 0) else 0 := by
  have e : ((univ : Finset (Fin (n + 2) → Fin 2 → Fin 3)).filter
      (fun f => ValidFrom q f ∧ RGSfrom c f ∧ f 0 = r)) =
      (((univ : Finset (Fin (n + 1) → Fin 2 → Fin 3)).filter
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

lemma vcard {R : ℕ} (x : Fin R → Fin 2 → Fin 3) (i : Fin R) (j : Fin 2) :
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

lemma vnot {R : ℕ} (x : Fin R → Fin 2 → Fin 3) (i : Fin R) (j : Fin 2) :
    ¬ (∀ i' : Fin R, (i'.val + 1 = i.val ∨ i.val + 1 = i'.val) → x i' j ≠ x i j) ↔
      0 < vEq (prevRow none x i) (x i) j + vEq (nextRow x i) (x i) j := by
  rw [← vcard, Finset.card_pos, Finset.filter_nonempty_iff]
  simp only [Finset.mem_univ, true_and, not_forall, not_not, exists_prop]

lemma cond_iff {R : ℕ} (x : Fin R → Fin 2 → Fin 3) : Cond x ↔ ValidFrom none x := by
  unfold Cond ValidFrom rowCond
  simp only [vnot]

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

/-- One step of the transfer, the rows below r enumerated entry by entry. -/
def T (g : Option (Fin 2 → Fin 3) → (Fin 2 → Fin 3) → ℕ → ℕ) (q : Option (Fin 2 → Fin 3)) (r : Fin 2 → Fin 3) (c : ℕ) : ℕ :=
  if rowRgs c r then
    ∑ x : Fin 3, ∑ y : Fin 3, (if rowCond q r (some ![x, y]) then g (some r) ![x, y] (newc c r) else 0)
  else 0

lemma W_succT (n : ℕ) (q : Option (Fin 2 → Fin 3)) (r : Fin 2 → Fin 3) (c : ℕ) :
    W (n + 1) q r c = T (W n) q r c := by
  rw [W_succ, T, sum_row]

lemma T_congr (g g' : Option (Fin 2 → Fin 3) → (Fin 2 → Fin 3) → ℕ → ℕ) (q : Option (Fin 2 → Fin 3)) (r : Fin 2 → Fin 3) (c : ℕ)
    (h : ∀ s, g (some r) s (newc c r) = g' (some r) s (newc c r)) : T g q r c = T g' q r c := by
  unfold T
  simp only [h]

/-- W(0) as a function. -/
def W0f (q : Option (Fin 2 → Fin 3)) (r : Fin 2 → Fin 3) (c : ℕ) : ℕ := if rowCond q r none ∧ rowRgs c r then 1 else 0

lemma W_zero_fun : W 0 = W0f := by
  funext q r c
  exact W_zero q r c

/-- W(1, none, r, c) for c <= 3, nested by the entries of r and then c. -/
def LN1 : List (List (List ℕ)) :=
  [[[0, 0, 0, 0], [1, 1, 1, 1], [0, 0, 1, 1]], [[0, 1, 1, 1], [0, 0, 0, 0], [0, 1, 1, 1]], [[0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 0, 0]]]

/-- W(1, some p, r, c) for c <= 3, nested by the entries of p, of r, and then c. -/
def LS1 : List (List (List (List (List ℕ)))) :=
  [[[[[0, 0, 0, 0], [1, 1, 1, 1], [0, 0, 1, 1]], [[0, 1, 1, 1], [0, 0, 0, 0], [0, 1, 1, 1]], [[0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 0, 0]]], [[[0, 0, 0, 0], [1, 1, 1, 1], [0, 0, 1, 1]], [[0, 1, 1, 1], [0, 0, 0, 0], [0, 1, 1, 1]], [[0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 0, 0]]], [[[0, 0, 0, 0], [1, 1, 1, 1], [0, 0, 1, 1]], [[0, 1, 1, 1], [0, 0, 0, 0], [0, 1, 1, 1]], [[0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 0, 0]]]], [[[[0, 0, 0, 0], [1, 1, 1, 1], [0, 0, 1, 1]], [[0, 1, 1, 1], [0, 0, 0, 0], [0, 1, 1, 1]], [[0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 0, 0]]], [[[0, 0, 0, 0], [1, 1, 1, 1], [0, 0, 1, 1]], [[0, 1, 1, 1], [0, 0, 0, 0], [0, 1, 1, 1]], [[0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 0, 0]]], [[[0, 0, 0, 0], [1, 1, 1, 1], [0, 0, 1, 1]], [[0, 1, 1, 1], [0, 0, 0, 0], [0, 1, 1, 1]], [[0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 0, 0]]]], [[[[0, 0, 0, 0], [1, 1, 1, 1], [0, 0, 1, 1]], [[0, 1, 1, 1], [0, 0, 0, 0], [0, 1, 1, 1]], [[0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 0, 0]]], [[[0, 0, 0, 0], [1, 1, 1, 1], [0, 0, 1, 1]], [[0, 1, 1, 1], [0, 0, 0, 0], [0, 1, 1, 1]], [[0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 0, 0]]], [[[0, 0, 0, 0], [1, 1, 1, 1], [0, 0, 1, 1]], [[0, 1, 1, 1], [0, 0, 0, 0], [0, 1, 1, 1]], [[0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 0, 0]]]]]

/-- W(1) as a table. -/
def tab1 (q : Option (Fin 2 → Fin 3)) (r : Fin 2 → Fin 3) (c : ℕ) : ℕ :=
  match q with
  | none => ((LN1.getD (r 0).val []).getD (r 1).val []).getD c 0
  | some p => ((((LS1.getD (p 0).val []).getD (p 1).val []).getD (r 0).val []).getD (r 1).val []).getD c 0

/-- W(2, none, r, c) for c <= 3, nested by the entries of r and then c. -/
def LN2 : List (List (List ℕ)) :=
  [[[0, 0, 0, 0], [1, 1, 1, 1], [0, 0, 1, 1]], [[0, 1, 1, 1], [0, 0, 0, 0], [0, 1, 1, 1]], [[0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 0, 0]]]

/-- W(2, some p, r, c) for c <= 3, nested by the entries of p, of r, and then c. -/
def LS2 : List (List (List (List (List ℕ)))) :=
  [[[[[0, 0, 0, 0], [2, 2, 2, 2], [0, 0, 2, 2]], [[0, 2, 2, 2], [0, 0, 0, 0], [0, 1, 1, 1]], [[0, 0, 2, 2], [0, 0, 1, 1], [0, 0, 0, 0]]], [[[0, 0, 0, 0], [6, 6, 6, 6], [0, 0, 2, 2]], [[0, 1, 1, 1], [0, 0, 0, 0], [0, 1, 1, 1]], [[0, 0, 1, 1], [0, 0, 2, 2], [0, 0, 0, 0]]], [[[0, 0, 0, 0], [2, 2, 2, 2], [0, 0, 6, 6]], [[0, 1, 1, 1], [0, 0, 0, 0], [0, 2, 2, 2]], [[0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 0, 0]]]], [[[[0, 0, 0, 0], [1, 1, 1, 1], [0, 0, 1, 1]], [[0, 6, 6, 6], [0, 0, 0, 0], [0, 2, 2, 2]], [[0, 0, 2, 2], [0, 0, 1, 1], [0, 0, 0, 0]]], [[[0, 0, 0, 0], [2, 2, 2, 2], [0, 0, 1, 1]], [[0, 2, 2, 2], [0, 0, 0, 0], [0, 2, 2, 2]], [[0, 0, 1, 1], [0, 0, 2, 2], [0, 0, 0, 0]]], [[[0, 0, 0, 0], [1, 1, 1, 1], [0, 0, 2, 2]], [[0, 2, 2, 2], [0, 0, 0, 0], [0, 6, 6, 6]], [[0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 0, 0]]]], [[[[0, 0, 0, 0], [1, 1, 1, 1], [0, 0, 1, 1]], [[0, 2, 2, 2], [0, 0, 0, 0], [0, 1, 1, 1]], [[0, 0, 6, 6], [0, 0, 2, 2], [0, 0, 0, 0]]], [[[0, 0, 0, 0], [2, 2, 2, 2], [0, 0, 1, 1]], [[0, 1, 1, 1], [0, 0, 0, 0], [0, 1, 1, 1]], [[0, 0, 2, 2], [0, 0, 6, 6], [0, 0, 0, 0]]], [[[0, 0, 0, 0], [1, 1, 1, 1], [0, 0, 2, 2]], [[0, 1, 1, 1], [0, 0, 0, 0], [0, 2, 2, 2]], [[0, 0, 2, 2], [0, 0, 2, 2], [0, 0, 0, 0]]]]]

/-- W(2) as a table. -/
def tab2 (q : Option (Fin 2 → Fin 3)) (r : Fin 2 → Fin 3) (c : ℕ) : ℕ :=
  match q with
  | none => ((LN2.getD (r 0).val []).getD (r 1).val []).getD c 0
  | some p => ((((LS2.getD (p 0).val []).getD (p 1).val []).getD (r 0).val []).getD (r 1).val []).getD c 0

lemma checkN1 : ∀ y1 y2 : Fin 3, ∀ c : Fin 4,
    T W0f none ![y1, y2] c.val = tab1 none ![y1, y2] c.val := by
  decide +kernel

lemma checkS1 : ∀ p1 p2 : Fin 3, ∀ y1 y2 : Fin 3, ∀ c : Fin 4,
    T W0f (some ![p1, p2]) ![y1, y2] c.val = tab1 (some ![p1, p2]) ![y1, y2] c.val := by
  decide +kernel

lemma checkN2 : ∀ y1 y2 : Fin 3, ∀ c : Fin 4,
    T tab1 none ![y1, y2] c.val = tab2 none ![y1, y2] c.val := by
  decide +kernel

lemma checkS2 : ∀ p1 p2 : Fin 3, ∀ y1 y2 : Fin 3, ∀ c : Fin 4,
    T tab1 (some ![p1, p2]) ![y1, y2] c.val = tab2 (some ![p1, p2]) ![y1, y2] c.val := by
  decide +kernel

lemma checkN_rel : ∀ y1 y2 : Fin 3, ∀ c : Fin 4,
    T tab2 none ![y1, y2] c.val + 3 * W0f none ![y1, y2] c.val =
      2 * tab2 none ![y1, y2] c.val + 4 * tab1 none ![y1, y2] c.val := by
  decide +kernel

lemma checkS_rel : ∀ p1 p2 : Fin 3, ∀ y1 y2 : Fin 3, ∀ c : Fin 4,
    T tab2 (some ![p1, p2]) ![y1, y2] c.val + 3 * W0f (some ![p1, p2]) ![y1, y2] c.val =
      2 * tab2 (some ![p1, p2]) ![y1, y2] c.val + 4 * tab1 (some ![p1, p2]) ![y1, y2] c.val := by
  decide +kernel

lemma W_1 (q : Option (Fin 2 → Fin 3)) (r : Fin 2 → Fin 3) (c : ℕ) (hc : c ≤ 3) :
    W 1 q r c = tab1 q r c := by
  rw [W_succT, W_zero_fun]
  rcases q with _ | p
  · rw [row_eta r]
    exact checkN1 (r 0) (r 1) ⟨c, by omega⟩
  · rw [row_eta p, row_eta r]
    exact checkS1 (p 0) (p 1) (r 0) (r 1) ⟨c, by omega⟩

lemma W_2 (q : Option (Fin 2 → Fin 3)) (r : Fin 2 → Fin 3) (c : ℕ) (hc : c ≤ 3) :
    W 2 q r c = tab2 q r c := by
  rw [show W 2 q r c = W (1 + 1) q r c from rfl, W_succT,
    T_congr _ tab1 q r c (fun s => W_1 _ s _ (newc_le c hc r))]
  rcases q with _ | p
  · rw [row_eta r]
    exact checkN2 (r 0) (r 1) ⟨c, by omega⟩
  · rw [row_eta p, row_eta r]
    exact checkS2 (p 0) (p 1) (r 0) (r 1) ⟨c, by omega⟩

lemma W_rec (n : ℕ) : ∀ (q : Option (Fin 2 → Fin 3)) (r : Fin 2 → Fin 3) (c : ℕ), c ≤ 3 →
    W (n + 3) q r c + 3 * W n q r c = 2 * W (n + 2) q r c + 4 * W (n + 1) q r c := by
  induction n with
  | zero =>
    intro q r c hc
    rw [show W (0 + 3) q r c = W (2 + 1) q r c from rfl, W_succT 2 q r c,
      T_congr _ tab2 q r c (fun s => W_2 _ s _ (newc_le c hc r)),
      show W 0 q r c = W0f q r c from congrFun (congrFun (congrFun W_zero_fun q) r) c,
      show W (0 + 1) q r c = W 1 q r c from rfl, W_1 q r c hc,
      show W (0 + 2) q r c = W 2 q r c from rfl, W_2 q r c hc]
    rcases q with _ | p
    · rw [row_eta r]
      exact checkN_rel (r 0) (r 1) ⟨c, by omega⟩
    · rw [row_eta p, row_eta r]
      exact checkS_rel (p 0) (p 1) (r 0) (r 1) ⟨c, by omega⟩
  | succ n ih =>
    intro q r c hc
    rw [W_succT (n + 3), W_succT (n + 2), W_succT (n + 1), W_succT n]
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

lemma a_eq (n : ℕ) : a n = ∑ r : Fin 2 → Fin 3, W (n) none r 0 := by
  unfold a W
  rw [Finset.card_eq_sum_card_fiberwise (f := fun f => f 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Finset.filter_filter]
  refine congrArg Finset.card (Finset.filter_congr (fun f _ => ?_))
  rw [cond_iff, rmn_iff, and_assoc]

lemma a_rec (n : ℕ) : a (n + 3) + 3 * a n = 2 * a (n + 2) + 4 * a (n + 1) := by
  rw [a_eq, a_eq, a_eq, a_eq, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  exact W_rec n none r 0 (by norm_num)

lemma a_zero : a 0 = 0 := by
  rw [a_eq, sum_row]
  simp only [W_zero]
  decide +kernel

lemma a_one : a 1 = 1 := by
  have h : ∀ r, W 1 none r 0 = tab1 none r 0 := fun r => W_1 none r 0 (by norm_num)
  rw [a_eq, sum_row]
  simp only [h]
  decide +kernel

lemma a_two : a 2 = 1 := by
  have h : ∀ r, W 2 none r 0 = tab2 none r 0 := fun r => W_2 none r 0 (by norm_num)
  rw [a_eq, sum_row]
  simp only [h]
  decide +kernel

lemma a_three : a 3 = 6 := by
  have h := a_rec 0
  have h0 := a_zero; have h1 := a_one; have h2 := a_two
  norm_num at h
  omega

/-- Barker's g.f.: Sum_{n >= 1} a(n) x^n = x(1 - x) / ((1 - 3x)(1 + x - x^2)). -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - 3 * X) * (1 + X - X ^ 2)) = X * (1 - X) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - 3 * X) * (1 + X - X ^ 2)) = A - A * X ^ 1 * C 2 - A * X ^ 2 * C 4 + A * X ^ 3 * C 3 := by
    rw [show (C (2 : ℚ) : ℚ⟦X⟧) = 2 from map_ofNat C 2,
      show (C (3 : ℚ) : ℚ⟦X⟧) = 3 from map_ofNat C 3,
      show (C (4 : ℚ) : ℚ⟦X⟧) = 4 from map_ofNat C 4]
    ring
  have e2 : (X * (1 - X) : ℚ⟦X⟧) = X ^ 1 * C 1 - X ^ 2 * C 1 := by
    rw [show (C (1 : ℚ) : ℚ⟦X⟧) = 1 from map_one C]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk]
  rcases n with _ | _ | _ | _ | n
  · simp
  · simp [a_one] <;> norm_num
  · simp [a_one, a_two] <;> norm_num
  · simp [a_one, a_two, a_three] <;> norm_num
  · have h := a_rec (n + 1)
    rw [show n + 1 + 3 = n + 4 from rfl, show n + 1 + 2 = n + 3 from rfl, show n + 1 + 1 = n + 2 from rfl] at h
    have hq : (a (n + 4) : ℚ) + 3 * (a (n + 1) : ℚ) = 2 * (a (n + 3) : ℚ) + 4 * (a (n + 2) : ℚ) := by exact_mod_cast h
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
      show ¬ (n + 4 = 2) by omega]
    linear_combination hq

theorem cf (b : ℕ → ℕ) (h0 : b 0 = 0) (h1 : b 1 = 1) (h2 : b 2 = 1)
    (hr : ∀ n, b (n + 3) + 3 * b n = 2 * b (n + 2) + 4 * b (n + 1)) :
    ∀ n : ℕ, 1 ≤ n → (b n : ℝ) =
      (10 * 3 ^ n + 2 ^ (-(n : ℤ)) * ((-1 + Real.sqrt 5) ^ n * (-5 + 4 * Real.sqrt 5) -
        (-1 - Real.sqrt 5) ^ n * (5 + 4 * Real.sqrt 5))) / 55 := by
  have s2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  set s := Real.sqrt 5 with hsdef
  set G : ℕ → ℝ := fun n => (-1 + s) ^ n * (-5 + 4 * s) - (-1 - s) ^ n * (5 + 4 * s) with hG
  have Grec : ∀ n, G (n + 2) = -2 * G (n + 1) + 4 * G n := by
    intro n
    simp only [hG]
    have e1 : (-1 + s) ^ 2 = -2 * (-1 + s) + 4 := by linear_combination s2
    have e2 : (-1 - s) ^ 2 = -2 * (-1 - s) + 4 := by linear_combination s2
    rw [show (-1 + s) ^ (n + 2) = (-1 + s) ^ n * (-1 + s) ^ 2 by ring,
      show (-1 - s) ^ (n + 2) = (-1 - s) ^ n * (-1 - s) ^ 2 by ring, e1, e2]
    ring
  have G0 : G 0 = -10 := by simp only [hG]; ring
  have G1 : G 1 = 50 := by simp only [hG]; linear_combination 8 * s2
  set P : ℕ → ℝ := fun n => 10 * 6 ^ n + G n with hP
  have Prec : ∀ n, P (n + 3) + 24 * P n = 4 * P (n + 2) + 16 * P (n + 1) := by
    intro n
    simp only [hP]
    have r0 := Grec n
    have r1 := Grec (n + 1)
    rw [show n + 1 + 2 = n + 3 from rfl, show n + 1 + 1 = n + 2 from rfl] at r1
    linear_combination r1 - 6 * r0
  have key : ∀ k, (b k : ℝ) * 55 * 2 ^ k = P k ∧ (b (k + 1) : ℝ) * 55 * 2 ^ (k + 1) = P (k + 1) ∧
      (b (k + 2) : ℝ) * 55 * 2 ^ (k + 2) = P (k + 2) := by
    intro k
    induction k with
    | zero =>
      simp only [hP, Nat.zero_add]
      rw [h0, h1, h2, show G 2 = G (0 + 2) from rfl, Grec, show G (0 + 1) = G 1 from rfl, G1, G0]
      norm_num
    | succ k ih =>
      obtain ⟨i0, i1, i2⟩ := ih
      refine ⟨i1, i2, ?_⟩
      have h := hr k
      have hq : ((b (k + 3) : ℕ) : ℝ) + 3 * b k = 2 * b (k + 2) + 4 * b (k + 1) := by
        exact_mod_cast h
      have hp := Prec k
      rw [show k + 1 + 2 = k + 3 from rfl]
      linear_combination (55 * 2 ^ (k + 3)) * hq - hp + 4 * i2 + 16 * i1 - 24 * i0
  intro n hn
  have hk := (key n).1
  have hz : (2 : ℝ) ^ (-(n : ℤ)) = 1 / 2 ^ n := by rw [zpow_neg, zpow_natCast, one_div]
  have h6 : (6 : ℝ) ^ n = 3 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
  show (b n : ℝ) = (10 * 3 ^ n + 2 ^ (-(n : ℤ)) * G n) / 55
  have hG' : G n = (b n : ℝ) * 55 * 2 ^ n - 10 * 3 ^ n * 2 ^ n := by
    rw [hk]; simp only [hP]; rw [h6]; ring
  rw [hz, hG']
  field_simp
  ring

/-- Barker's closed form. -/
theorem closed_form : ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (10 * 3 ^ n + 2 ^ (-(n : ℤ)) * ((-1 + Real.sqrt 5) ^ n * (-5 + 4 * Real.sqrt 5) -
        (-1 - Real.sqrt 5) ^ n * (5 + 4 * Real.sqrt 5))) / 55 :=
  cf a a_zero a_one a_two a_rec

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - 3 * X) * (1 + X - X ^ 2)) = X * (1 - X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (10 * 3 ^ n + 2 ^ (-(n : ℤ)) * ((-1 + Real.sqrt 5) ^ n * (-5 + 4 * Real.sqrt 5) -
        (-1 - Real.sqrt 5) ^ n * (5 + 4 * Real.sqrt 5))) / 55 :=
  ⟨gf, closed_form⟩

/-- Controls: the entry's terms a(1..10), from the recurrence and the first values. -/
theorem controls : a 1 = 1 ∧ a 2 = 1 ∧ a 3 = 6 ∧ a 4 = 13 ∧ a 5 = 47 ∧ a 6 = 128 ∧ a 7 = 405 ∧ a 8 = 1181 ∧ a 9 = 3598 ∧ a 10 = 10705 := by
  have r1 := a_rec 1; have r2 := a_rec 2; have r3 := a_rec 3; have r4 := a_rec 4; have r5 := a_rec 5; have r6 := a_rec 6; have r7 := a_rec 7
  have h1 := a_one; have h2 := a_two; have h3 := a_three
  norm_num at r1 r2 r3 r4 r5 r6 r7
  omega

end OMA.S_oeis_a239530

theorem OMA.solution : type_of% @OMA.S_oeis_a239530.main :=
  OMA.S_oeis_a239530.conjecture
