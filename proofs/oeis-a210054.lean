import OMAStatements.S_oeis_a210054

namespace OMA.S_oeis_a210054

open PowerSeries Finset


instance {R C K : ℕ} : DecidablePred (@RowMajorNew R C K) := fun x => by
  unfold RowMajorNew; infer_instance



instance {R C K : ℕ} : DecidablePred (@BlocksOK R C K) := fun x => by
  unfold BlocksOK; infer_instance


/-! ## Rows -/

/-- No condition inside a row. -/
def hrow (_ : Fin 2 → Fin 4) : Prop := True

/-- The row s may lie directly below the row r: the 2 X 2 subblocks of the two rows have one, two or four
distinct values. -/
def ok (r s : Fin 2 → Fin 4) : Prop :=
  ∀ j j' : Fin 2, j'.val = j.val + 1 →
    ({r j, r j', s j, s j'} : Finset (Fin 4)).card = 1 ∨
    ({r j, r j', s j, s j'} : Finset (Fin 4)).card = 2 ∨
    ({r j, r j', s j, s j'} : Finset (Fin 4)).card = 4

instance : DecidablePred hrow := fun r => by unfold hrow; infer_instance

instance : DecidableRel ok := fun r s => by unfold ok; infer_instance

/-- Rows valid and consecutive rows compatible. -/
def Valid {n : ℕ} (g : Fin n → Fin 2 → Fin 4) : Prop :=
  (∀ i, hrow (g i)) ∧ ∀ i i' : Fin n, i'.val = i.val + 1 → ok (g i) (g i')

instance {n : ℕ} : DecidablePred (@Valid n) := fun g => by unfold Valid; infer_instance

lemma cond_iff {n : ℕ} (x : Fin n → Fin 2 → Fin 4) : BlocksOK x ↔ Valid x := by
  unfold BlocksOK Valid hrow ok blockCount
  constructor
  · intro h
    exact ⟨fun _ => trivial, fun i i' hi j j' hj => h i i' j j' hi hj⟩
  · rintro ⟨_, h⟩ i i' j j' hi hj
    exact h i i' hi j j' hj

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

/-! ## Counting by the first row -/

/-- W(n, r, c): arrays with n + 1 rows, first row r, consecutive rows compatible, values introduced
in row major order after the values below c. -/
def W (n : ℕ) (r : Fin 2 → Fin 4) (c : ℕ) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 2 → Fin 4)).filter
    (fun g => Valid g ∧ RGSfrom c g ∧ g 0 = r)).card

lemma valid_cons {n : ℕ} (x : Fin 2 → Fin 4) (g : Fin (n + 1) → Fin 2 → Fin 4) :
    Valid (Fin.cons x g : Fin (n + 2) → Fin 2 → Fin 4) ↔ hrow x ∧ ok x (g 0) ∧ Valid g := by
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

lemma W_zero (r : Fin 2 → Fin 4) (c : ℕ) : W 0 r c = if hrow r ∧ rowRgs c r then 1 else 0 := by
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
      refine ⟨⟨fun _ => hr.1, ?_⟩, (RGSfrom_one c _).2 hr.2, rfl⟩
      intro i j hij
      have := j.isLt
      omega
  · rw [Finset.card_eq_zero]
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨⟨h1, _⟩, hR, h0⟩
    apply hr
    rw [← h0]
    exact ⟨h1 0, (RGSfrom_one c f).1 hR⟩

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

lemma W_succ (n : ℕ) (r : Fin 2 → Fin 4) (c : ℕ) :
    W (n + 1) r c = if hrow r ∧ rowRgs c r then
      ∑ s : Fin 2 → Fin 4, (if ok r s then W n s (newc c r) else 0) else 0 := by
  have e : ((univ : Finset (Fin (n + 2) → Fin 2 → Fin 4)).filter
      (fun f => Valid f ∧ RGSfrom c f ∧ f 0 = r)) =
      (((univ : Finset (Fin (n + 1) → Fin 2 → Fin 4)).filter
        (fun g => ((hrow r ∧ rowRgs c r) ∧ ok r (g 0)) ∧ Valid g ∧
          RGSfrom (newc c r) g)).map (consEmb n r)) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, consEmb_apply]
    constructor
    · rintro ⟨hv, hR, h0⟩
      refine ⟨Fin.tail f, ?_, ?_⟩
      · have hf : f = Fin.cons r (Fin.tail f) := by
          rw [← h0]; exact (Fin.cons_self_tail f).symm
        rw [hf, valid_cons] at hv
        rw [hf, RGSfrom_cons] at hR
        exact ⟨⟨⟨hv.1, hR.1⟩, hv.2.1⟩, hv.2.2, hR.2⟩
      · rw [← h0]; exact Fin.cons_self_tail f
    · rintro ⟨g, ⟨⟨⟨h1, h2⟩, h3⟩, hg, hR⟩, rfl⟩
      exact ⟨(valid_cons r g).2 ⟨h1, h3, hg⟩, (RGSfrom_cons c r g).2 ⟨h2, hR⟩, by simp⟩
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
def T (g : (Fin 2 → Fin 4) → ℕ → ℕ) (r : Fin 2 → Fin 4) (c : ℕ) : ℕ :=
  if hrow r ∧ rowRgs c r then
    ∑ x : Fin 4, ∑ y : Fin 4, (if ok r ![x, y] then g ![x, y] (newc c r) else 0) else 0

lemma W_succT (n : ℕ) (r : Fin 2 → Fin 4) (c : ℕ) : W (n + 1) r c = T (W n) r c := by
  rw [W_succ, T, sum_row]

lemma T_congr (g g' : (Fin 2 → Fin 4) → ℕ → ℕ) (r : Fin 2 → Fin 4) (c : ℕ)
    (h : ∀ s, g s (newc c r) = g' s (newc c r)) : T g r c = T g' r c := by
  unfold T
  simp only [h]

/-- W(0) as a function. -/
def W0f (s : Fin 2 → Fin 4) (c : ℕ) : ℕ := if hrow s ∧ rowRgs c s then 1 else 0

lemma W_zero_fun : W 0 = W0f := by
  funext s c
  exact W_zero s c

/-- W(1, r, c) for c <= 4, nested by the entries of r and then c. -/
def L1 : List (List (List ℕ)) :=
  [[[4, 4, 7, 10, 10], [5, 5, 5, 6, 6], [0, 0, 6, 6, 6], [0, 0, 0, 6, 6]], [[0, 5, 5, 6, 6], [0, 7, 7, 10, 10], [0, 6, 6, 6, 6], [0, 0, 0, 6, 6]], [[0, 0, 6, 6, 6], [0, 0, 6, 6, 6], [0, 0, 10, 10, 10], [0, 0, 6, 6, 6]], [[0, 0, 0, 6, 6], [0, 0, 0, 6, 6], [0, 0, 0, 6, 6], [0, 0, 0, 10, 10]]]

/-- W(1) as a table. -/
def tab1 (r : Fin 2 → Fin 4) (c : ℕ) : ℕ := ((L1.getD (r 0).val []).getD (r 1).val []).getD c 0

/-- W(2, r, c) for c <= 4, nested by the entries of r and then c. -/
def L2 : List (List (List ℕ)) :=
  [[[21, 21, 46, 76, 76], [30, 30, 30, 44, 44], [0, 0, 44, 44, 44], [0, 0, 0, 44, 44]], [[0, 30, 30, 44, 44], [0, 46, 46, 76, 76], [0, 44, 44, 44, 44], [0, 0, 0, 44, 44]], [[0, 0, 44, 44, 44], [0, 0, 44, 44, 44], [0, 0, 76, 76, 76], [0, 0, 44, 44, 44]], [[0, 0, 0, 44, 44], [0, 0, 0, 44, 44], [0, 0, 0, 44, 44], [0, 0, 0, 76, 76]]]

/-- W(2) as a table. -/
def tab2 (r : Fin 2 → Fin 4) (c : ℕ) : ℕ := ((L2.getD (r 0).val []).getD (r 1).val []).getD c 0

/-- W(3, r, c) for c <= 4, nested by the entries of r and then c. -/
def L3 : List (List (List ℕ)) :=
  [[[127, 127, 316, 568, 568], [196, 196, 196, 328, 328], [0, 0, 328, 328, 328], [0, 0, 0, 328, 328]], [[0, 196, 196, 328, 328], [0, 316, 316, 568, 568], [0, 328, 328, 328, 328], [0, 0, 0, 328, 328]], [[0, 0, 328, 328, 328], [0, 0, 328, 328, 328], [0, 0, 568, 568, 568], [0, 0, 328, 328, 328]], [[0, 0, 0, 328, 328], [0, 0, 0, 328, 328], [0, 0, 0, 328, 328], [0, 0, 0, 568, 568]]]

/-- W(3) as a table. -/
def tab3 (r : Fin 2 → Fin 4) (c : ℕ) : ℕ := ((L3.getD (r 0).val []).getD (r 1).val []).getD c 0

lemma check1 : ∀ x y : Fin 4, ∀ c : Fin 5,
    T W0f ![x, y] c.val = tab1 ![x, y] c.val := by
  decide +kernel

lemma check2 : ∀ x y : Fin 4, ∀ c : Fin 5,
    T tab1 ![x, y] c.val = tab2 ![x, y] c.val := by
  decide +kernel

lemma check3 : ∀ x y : Fin 4, ∀ c : Fin 5,
    T tab2 ![x, y] c.val = tab3 ![x, y] c.val := by
  decide +kernel

lemma check_rel : ∀ x y : Fin 4, ∀ c : Fin 5,
    T tab3 ![x, y] c.val + 48 * tab2 ![x, y] c.val + 16 * W0f ![x, y] c.val =
      13 * tab3 ![x, y] c.val + 52 * tab1 ![x, y] c.val := by
  decide +kernel

lemma W_1 (r : Fin 2 → Fin 4) (c : ℕ) (hc : c ≤ 4) : W 1 r c = tab1 r c := by
  rw [W_succT, W_zero_fun, row_eta r]
  exact check1 (r 0) (r 1) ⟨c, by omega⟩

lemma W_2 (r : Fin 2 → Fin 4) (c : ℕ) (hc : c ≤ 4) : W 2 r c = tab2 r c := by
  rw [show W 2 r c = W (1 + 1) r c from rfl, W_succT,
    T_congr _ tab1 r c (fun s => W_1 s _ (newc_le c hc r)), row_eta r]
  exact check2 (r 0) (r 1) ⟨c, by omega⟩

lemma W_3 (r : Fin 2 → Fin 4) (c : ℕ) (hc : c ≤ 4) : W 3 r c = tab3 r c := by
  rw [show W 3 r c = W (2 + 1) r c from rfl, W_succT,
    T_congr _ tab2 r c (fun s => W_2 s _ (newc_le c hc r)), row_eta r]
  exact check3 (r 0) (r 1) ⟨c, by omega⟩

lemma W_rec (n : ℕ) : ∀ (r : Fin 2 → Fin 4) (c : ℕ), c ≤ 4 →
    W (n + 4) r c + 48 * W (n + 2) r c + 16 * W n r c = 13 * W (n + 3) r c + 52 * W (n + 1) r c := by
  induction n with
  | zero =>
    intro r c hc
    rw [show W (0 + 4) r c = W (3 + 1) r c from rfl, W_succT 3 r c,
      T_congr _ tab3 r c (fun s => W_3 s _ (newc_le c hc r)),
      show W 0 r c = W0f r c from congrFun (congrFun W_zero_fun r) c,
      show W (0 + 1) r c = W 1 r c from rfl, W_1 r c hc,
      show W (0 + 2) r c = W 2 r c from rfl, W_2 r c hc,
      show W (0 + 3) r c = W 3 r c from rfl, W_3 r c hc,
      row_eta r]
    exact check_rel (r 0) (r 1) ⟨c, by omega⟩
  | succ n ih =>
    intro r c hc
    rw [W_succT (n + 4), W_succT (n + 3), W_succT (n + 2), W_succT (n + 1), W_succT n]
    unfold T
    split_ifs with h
    · rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      split_ifs
      · exact ih _ _ (newc_le c hc r)
      · simp
    · simp

lemma a_eq (n : ℕ) : a n = ∑ r : Fin 2 → Fin 4, W n r 0 := by
  unfold a W
  rw [Finset.card_eq_sum_card_fiberwise (f := fun f => f 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Finset.filter_filter]
  refine congrArg Finset.card (Finset.filter_congr (fun f _ => ?_))
  rw [cond_iff, rmn_iff, and_assoc]

lemma a_rec (n : ℕ) : a (n + 4) + 48 * a (n + 2) + 16 * a n = 13 * a (n + 3) + 52 * a (n + 1) := by
  rw [a_eq, a_eq, a_eq, a_eq, a_eq, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  exact W_rec n r 0 (by norm_num)

lemma a_zero : a 0 = 2 := by
  rw [a_eq, sum_row]
  simp only [W_zero]
  decide +kernel

lemma a_one : a 1 = 9 := by
  have h : ∀ r, W 1 r 0 = tab1 r 0 := fun r => W_1 r 0 (by norm_num)
  rw [a_eq, sum_row]
  simp only [h]
  decide +kernel

lemma a_two : a 2 = 51 := by
  have h : ∀ r, W 2 r 0 = tab2 r 0 := fun r => W_2 r 0 (by norm_num)
  rw [a_eq, sum_row]
  simp only [h]
  decide +kernel

lemma a_three : a 3 = 323 := by
  have h : ∀ r, W 3 r 0 = tab3 r 0 := fun r => W_3 r 0 (by norm_num)
  rw [a_eq, sum_row]
  simp only [h]
  decide +kernel

lemma a_four : a 4 = 2187 := by
  have h := a_rec 0
  have h0 := a_zero; have h1 := a_one; have h2 := a_two; have h3 := a_three
  norm_num at h
  omega

/-- Barker's g.f.: Sum_{n >= 1} a(n) x^n = x(9 - 66x + 92x^2 - 32x^3) / ((1 - x)(1 - 4x)(1 - 8x + 4x^2)). -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - X) * (1 - 4 * X) * (1 - 8 * X + 4 * X ^ 2)) = X * (9 - 66 * X + 92 * X ^ 2 - 32 * X ^ 3) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - X) * (1 - 4 * X) * (1 - 8 * X + 4 * X ^ 2)) = A - A * X ^ 1 * C 13 + A * X ^ 2 * C 48 - A * X ^ 3 * C 52 + A * X ^ 4 * C 16 := by
    rw [show (C (13 : ℚ) : ℚ⟦X⟧) = 13 from map_ofNat C 13,
      show (C (16 : ℚ) : ℚ⟦X⟧) = 16 from map_ofNat C 16,
      show (C (48 : ℚ) : ℚ⟦X⟧) = 48 from map_ofNat C 48,
      show (C (52 : ℚ) : ℚ⟦X⟧) = 52 from map_ofNat C 52]
    ring
  have e2 : (X * (9 - 66 * X + 92 * X ^ 2 - 32 * X ^ 3) : ℚ⟦X⟧) = X ^ 1 * C 9 - X ^ 2 * C 66 + X ^ 3 * C 92 - X ^ 4 * C 32 := by
    rw [show (C (9 : ℚ) : ℚ⟦X⟧) = 9 from map_ofNat C 9,
      show (C (32 : ℚ) : ℚ⟦X⟧) = 32 from map_ofNat C 32,
      show (C (66 : ℚ) : ℚ⟦X⟧) = 66 from map_ofNat C 66,
      show (C (92 : ℚ) : ℚ⟦X⟧) = 92 from map_ofNat C 92]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, map_neg, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk]
  rcases n with _ | _ | _ | _ | _ | n
  · simp
  · simp [a_one] <;> norm_num
  · simp [a_one, a_two] <;> norm_num
  · simp [a_one, a_two, a_three] <;> norm_num
  · simp [a_one, a_two, a_three, a_four] <;> norm_num
  · have h := a_rec (n + 1)
    rw [show n + 1 + 4 = n + 5 from rfl, show n + 1 + 3 = n + 4 from rfl, show n + 1 + 2 = n + 3 from rfl, show n + 1 + 1 = n + 2 from rfl] at h
    have hq : (a (n + 5) : ℚ) + 48 * (a (n + 3) : ℚ) + 16 * (a (n + 1) : ℚ) = 13 * (a (n + 4) : ℚ) + 52 * (a (n + 2) : ℚ) := by exact_mod_cast h
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

theorem cf (b : ℕ → ℕ) (h0 : b 0 = 2) (h1 : b 1 = 9) (h2 : b 2 = 51) (h3 : b 3 = 323)
    (hr : ∀ n, b (n + 4) + 48 * b (n + 2) + 16 * b n = 13 * b (n + 3) + 52 * b (n + 1)) :
    ∀ n : ℕ, 1 ≤ n → (b n : ℝ) = (1 / 3) + 4 ^ n -
      (1 / 6) * (4 - 2 * Real.sqrt 3) ^ n * (-2 + Real.sqrt 3) +
      (1 / 3) * 2 ^ (-1 + (n : ℤ)) * (2 + Real.sqrt 3) ^ (1 + n) := by
  have s2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  set s := Real.sqrt 3 with hsdef
  set U : ℕ → ℝ := fun n => (2 - s) / 6 * (4 - 2 * s) ^ n + (2 + s) / 6 * (4 + 2 * s) ^ n
    with hU
  have Urec : ∀ n, U (n + 2) = 8 * U (n + 1) - 4 * U n := by
    intro n
    simp only [hU]
    have e1 : (4 - 2 * s) ^ 2 = 8 * (4 - 2 * s) - 4 := by linear_combination 4 * s2
    have e2 : (4 + 2 * s) ^ 2 = 8 * (4 + 2 * s) - 4 := by linear_combination 4 * s2
    rw [show (4 - 2 * s) ^ (n + 2) = (4 - 2 * s) ^ n * (4 - 2 * s) ^ 2 by ring,
      show (4 + 2 * s) ^ (n + 2) = (4 + 2 * s) ^ n * (4 + 2 * s) ^ 2 by ring, e1, e2]
    ring
  have U0 : U 0 = 2 / 3 := by simp only [hU]; ring
  have U1 : U 1 = 14 / 3 := by simp only [hU]; linear_combination (2 / 3 : ℝ) * s2
  set F : ℕ → ℝ := fun n => 1 / 3 + 4 ^ n + U n with hF
  have Frec : ∀ n, F (n + 4) + 48 * F (n + 2) + 16 * F n = 13 * F (n + 3) + 52 * F (n + 1) := by
    intro n
    simp only [hF]
    have r0 := Urec n
    have r1 := Urec (n + 1)
    have r2 := Urec (n + 2)
    rw [show n + 1 + 2 = n + 3 from rfl, show n + 1 + 1 = n + 2 from rfl] at r1
    rw [show n + 2 + 2 = n + 4 from rfl, show n + 2 + 1 = n + 3 from rfl] at r2
    linear_combination r2 - 5 * r1 + 4 * r0
  have U2 : U 2 = 104 / 3 := by
    rw [show U 2 = U (0 + 2) from rfl, Urec, show U (0 + 1) = U 1 from rfl, U1, U0]; norm_num
  have U3 : U 3 = 776 / 3 := by
    rw [show U 3 = U (1 + 2) from rfl, Urec, show U (1 + 1) = U 2 from rfl, U2, U1]; norm_num
  have key : ∀ k, (b k : ℝ) = F k ∧ (b (k + 1) : ℝ) = F (k + 1) ∧ (b (k + 2) : ℝ) = F (k + 2) ∧
      (b (k + 3) : ℝ) = F (k + 3) := by
    intro k
    induction k with
    | zero =>
      simp only [hF, Nat.zero_add]
      rw [h0, h1, h2, h3, U0, U1, U2, U3]
      norm_num
    | succ k ih =>
      obtain ⟨i0, i1, i2, i3⟩ := ih
      refine ⟨i1, i2, i3, ?_⟩
      have h := hr k
      have hq : ((b (k + 4) : ℕ) : ℝ) + 48 * b (k + 2) + 16 * b k =
          13 * b (k + 3) + 52 * b (k + 1) := by exact_mod_cast h
      have hf := Frec k
      rw [show k + 1 + 3 = k + 4 from rfl]
      linear_combination hq - hf - 48 * i2 - 16 * i0 + 13 * i3 + 52 * i1
  intro n hn
  have hz : (2 : ℝ) ^ (-1 + (n : ℤ)) = 2 ^ n / 2 := by
    rw [zpow_add₀ two_ne_zero, zpow_neg_one, zpow_natCast]
    ring
  rw [(key n).1, hz]
  simp only [hF, hU]
  rw [pow_add (2 + s) 1 n, pow_one,
    show (4 + 2 * s) ^ n = 2 ^ n * (2 + s) ^ n by rw [← mul_pow]; ring_nf]
  ring

/-- Barker's closed form. -/
theorem closed_form : ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (1 / 3) + 4 ^ n -
        (1 / 6) * (4 - 2 * Real.sqrt 3) ^ n * (-2 + Real.sqrt 3) +
        (1 / 3) * 2 ^ (-1 + (n : ℤ)) * (2 + Real.sqrt 3) ^ (1 + n) :=
  cf a a_zero a_one a_two a_three a_rec

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 - 4 * X) * (1 - 8 * X + 4 * X ^ 2)) = X * (9 - 66 * X + 92 * X ^ 2 - 32 * X ^ 3) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (1 / 3) + 4 ^ n -
        (1 / 6) * (4 - 2 * Real.sqrt 3) ^ n * (-2 + Real.sqrt 3) +
        (1 / 3) * 2 ^ (-1 + (n : ℤ)) * (2 + Real.sqrt 3) ^ (1 + n) :=
  ⟨gf, closed_form⟩

/-- Controls: the entry's terms a(1..10), from the recurrence and the first values. -/
theorem controls : a 1 = 9 ∧ a 2 = 51 ∧ a 3 = 323 ∧ a 4 = 2187 ∧ a 5 = 15435 ∧ a 6 = 111659 ∧ a 7 = 819243 ∧ a 8 = 6058155 ∧ a 9 = 44991659 ∧ a 10 = 334914219 := by
  have r1 := a_rec 1; have r2 := a_rec 2; have r3 := a_rec 3; have r4 := a_rec 4; have r5 := a_rec 5; have r6 := a_rec 6
  have h1 := a_one; have h2 := a_two; have h3 := a_three; have h4 := a_four
  norm_num at r1 r2 r3 r4 r5 r6
  omega

/-- Control by direct enumeration of the definition: a(1) = 9. -/
theorem control_direct : a 1 = 9 := by
  unfold a
  decide +kernel

end OMA.S_oeis_a210054

theorem OMA.solution : type_of% @OMA.S_oeis_a210054.main :=
  OMA.S_oeis_a210054.conjecture
