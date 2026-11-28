import OMAStatements.S_oeis_a233212

namespace OMA.S_oeis_a233212

open PowerSeries Finset


instance {R C : ℕ} : DecidablePred (@Cond R C) := fun x => by unfold Cond; infer_instance


instance {R C : ℕ} : DecidablePred (@Norm R C) := fun x => by unfold Norm; infer_instance


/-! ## Rows and the chain of first occurrences -/

/-- No two neighbors in the row add up to 5. -/
def hrow (r : Fin 3 → Fin 6) : Prop := ∀ j j' : Fin 3, j'.val = j.val + 1 → (r j).val + (r j').val ≠ 5

/-- No entry of the row s below r is a antidiagonal neighbor adding up to 5. -/
def ok (r s : Fin 3 → Fin 6) : Prop := ∀ j j' : Fin 3, j.val = j'.val + 1 → (r j).val + (s j').val ≠ 5

instance (r : Fin 3 → Fin 6) : Decidable (hrow r) := by unfold hrow; infer_instance

instance (r s : Fin 3 → Fin 6) : Decidable (ok r s) := by unfold ok; infer_instance

/-- req v: an entry v needs the chain values 1..req v before it. -/
def req (v : Fin 6) : ℕ := if v = 2 then 1 else if v = 3 then 2 else if v = 4 then 1 else 0

/-- The chain values in order: 1, 2. -/
def chain (k : ℕ) : Fin 6 := if k = 2 then 2 else 1

/-- The position of v in the chain, 0 for the other values. -/
def cidx (v : Fin 6) : ℕ := if v = 1 then 1 else if v = 2 then 2 else 0

lemma req_le (v : Fin 6) : req v ≤ 2 := by fin_cases v <;> decide

lemma cidx_le (v : Fin 6) : cidx v ≤ 2 := by fin_cases v <;> decide

lemma cidx_chain (k : ℕ) (hk : 1 ≤ k) (hkt : k ≤ 2) : cidx (chain k) = k := by
  interval_cases k <;> decide

lemma cidx_spec (v : Fin 6) (h : 1 ≤ cidx v) : chain (cidx v) = v ∧ cidx v ≤ 2 := by
  revert h
  fin_cases v <;> decide

lemma req_chain (k : ℕ) (hk : 1 ≤ k) (hkt : k ≤ 2) : req (chain k) = k - 1 := by
  interval_cases k <;> decide

/-! ## The order of first occurrences, after the chain values 1..c -/

/-- The chain values 1..c count as occurring before the array; every other chain value that an entry
needs (`req`) occurs at an earlier position in row major order. -/
def NormFrom {R C : ℕ} (c : ℕ) (x : Fin R → Fin C → Fin 6) : Prop :=
  ∀ i j, ∀ k, 1 ≤ k → k ≤ req (x i j) →
    k ≤ c ∨ ∃ i' j', (i' < i ∨ (i' = i ∧ j' < j)) ∧ x i' j' = chain k

instance {R C : ℕ} (c : ℕ) : DecidablePred (@NormFrom R C c) := fun x => by
  unfold NormFrom; infer_instance

/-- The same for one row. -/
def rowNorm {C : ℕ} (c : ℕ) (r : Fin C → Fin 6) : Prop :=
  ∀ j, ∀ k, 1 ≤ k → k ≤ req (r j) → k ≤ c ∨ ∃ j', j' < j ∧ r j' = chain k

instance {C : ℕ} (c : ℕ) : DecidablePred (@rowNorm C c) := fun r => by
  unfold rowNorm; infer_instance

/-- The chain values that occur in or before the row r, when 1..c occur before it. -/
def newph {C : ℕ} (c : ℕ) (r : Fin C → Fin 6) : ℕ := max c (univ.sup fun j => cidx (r j))

lemma lt_newph {C : ℕ} (c : ℕ) (r : Fin C → Fin 6) (k : ℕ) (hk : 1 ≤ k) :
    k ≤ newph c r ↔ k ≤ c ∨ ∃ j, k ≤ cidx (r j) := by
  unfold newph
  rw [le_max_iff, Finset.le_sup_iff (by simp; omega)]
  simp

lemma rowNorm_cons {C : ℕ} (c : ℕ) (v : Fin 6) (t : Fin C → Fin 6) :
    rowNorm c (Matrix.vecCons v t) ↔ req v ≤ c ∧ rowNorm (max c (cidx v)) t := by
  constructor
  · intro H
    refine ⟨?_, fun j k hk hkr => ?_⟩
    · by_contra hv
      rcases H 0 (req v) (by omega) (by rw [Matrix.cons_val_zero]) with h | ⟨j', hj', _⟩
      · omega
      · exact absurd hj' (Fin.not_lt_zero j')
    · rcases H j.succ k hk (by rwa [Matrix.cons_val_succ]) with h | ⟨j', hj', he⟩
      · exact Or.inl (le_max_of_le_left h)
      · induction j' using Fin.cases with
        | zero =>
          rw [Matrix.cons_val_zero] at he
          subst he
          exact Or.inl (le_max_of_le_right (le_of_eq (cidx_chain k hk (le_trans hkr (req_le _))).symm))
        | succ j'' =>
          rw [Matrix.cons_val_succ] at he
          exact Or.inr ⟨j'', Fin.succ_lt_succ_iff.mp hj', he⟩
  · rintro ⟨hv, H⟩ j k hk hkr
    induction j using Fin.cases with
    | zero =>
      rw [Matrix.cons_val_zero] at hkr
      exact Or.inl (by omega)
    | succ j =>
      rw [Matrix.cons_val_succ] at hkr
      rcases H j k hk hkr with h | ⟨j', hj', he⟩
      · rcases le_max_iff.mp h with h | h
        · exact Or.inl h
        · obtain ⟨e1, e2⟩ := cidx_spec v (by omega)
          rcases Nat.eq_or_lt_of_le h with h | h
          · exact Or.inr ⟨0, Fin.succ_pos j, by rw [Matrix.cons_val_zero, h, e1]⟩
          · have := req_chain (cidx v) (by omega) e2
            rw [e1] at this
            exact Or.inl (by omega)
      · exact Or.inr ⟨j'.succ, Fin.succ_lt_succ_iff.mpr hj', by rw [Matrix.cons_val_succ]; exact he⟩

lemma rowNorm_zero (c : ℕ) (t : Fin 0 → Fin 6) : rowNorm c t := fun j => j.elim0

lemma newph_cons {C : ℕ} (c : ℕ) (v : Fin 6) (t : Fin C → Fin 6) :
    newph c (Matrix.vecCons v t) = newph (max c (cidx v)) t := by
  refine eq_of_forall_ge_iff (fun k => ?_)
  simp only [newph, max_le_iff, Finset.sup_le_iff, Finset.mem_univ, true_imp_iff, Fin.forall_fin_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, and_assoc]

lemma newph_zero (c : ℕ) (t : Fin 0 → Fin 6) : newph c t = c := by
  simp [newph]

lemma newph_le (c : ℕ) (hc : c ≤ 2) {C : ℕ} (r : Fin C → Fin 6) : newph c r ≤ 2 :=
  max_le hc (Finset.sup_le fun j _ => cidx_le (r j))

lemma NormFrom_one {C : ℕ} (c : ℕ) (f : Fin 1 → Fin C → Fin 6) : NormFrom c f ↔ rowNorm c (f 0) := by
  constructor
  · intro H j k hk hkr
    rcases H 0 j k hk hkr with h | ⟨i', j', hb, he⟩
    · exact Or.inl h
    · right
      have hi : i' = 0 := Fin.fin_one_eq_zero i'
      subst hi
      rcases hb with hb | ⟨_, hj⟩
      · exact absurd hb (lt_irrefl _)
      · exact ⟨j', hj, he⟩
  · intro H i j k hk hkr
    have hi : i = 0 := Fin.fin_one_eq_zero i
    subst hi
    rcases H j k hk hkr with h | ⟨j', hj, he⟩
    · exact Or.inl h
    · exact Or.inr ⟨0, j', Or.inr ⟨rfl, hj⟩, he⟩

lemma NormFrom_cons {n C : ℕ} (c : ℕ) (r : Fin C → Fin 6) (h : Fin (n + 1) → Fin C → Fin 6) :
    NormFrom c (Fin.cons r h : Fin (n + 2) → Fin C → Fin 6) ↔ rowNorm c r ∧ NormFrom (newph c r) h := by
  constructor
  · intro H
    refine ⟨fun j k hk hkr => ?_, fun i j k hk hkr => ?_⟩
    · rcases H 0 j k hk (by simpa using hkr) with h1 | ⟨i', j', hb, he⟩
      · exact Or.inl h1
      · right
        rcases hb with hb | ⟨rfl, hj⟩
        · exact absurd hb (Fin.not_lt_zero _)
        · exact ⟨j', hj, by simpa using he⟩
    · rcases H i.succ j k hk (by simpa using hkr) with h1 | ⟨i', j', hb, he⟩
      · exact Or.inl ((lt_newph c r k hk).2 (Or.inl h1))
      · induction i' using Fin.cases with
        | zero =>
          left
          rw [lt_newph c r k hk]
          right
          refine ⟨j', ?_⟩
          simp only [Fin.cons_zero] at he
          rw [he, cidx_chain k hk (le_trans hkr (req_le _))]
        | succ i'' =>
          right
          refine ⟨i'', j', ?_, by simpa using he⟩
          rcases hb with hb | ⟨hb, hj⟩
          · exact Or.inl (Fin.succ_lt_succ_iff.mp hb)
          · exact Or.inr ⟨Fin.succ_injective _ hb, hj⟩
  · rintro ⟨H0, H⟩ i j k hk hkr
    induction i using Fin.cases with
    | zero =>
      rcases H0 j k hk (by simpa using hkr) with h1 | ⟨j', hj, he⟩
      · exact Or.inl h1
      · exact Or.inr ⟨0, j', Or.inr ⟨rfl, hj⟩, by simpa using he⟩
    | succ i =>
      rcases H i j k hk (by simpa using hkr) with h1 | ⟨i', j', hb, he⟩
      · rw [lt_newph c r k hk] at h1
        rcases h1 with h1 | ⟨j0, hj0⟩
        · exact Or.inl h1
        · obtain ⟨e1, e2⟩ := cidx_spec (r j0) (by omega)
          rcases Nat.eq_or_lt_of_le hj0 with heq | hlt
          · exact Or.inr ⟨0, j0, Or.inl (Fin.succ_pos _), by simp only [Fin.cons_zero]; rw [heq, e1]⟩
          · have hreq := req_chain (cidx (r j0)) (by omega) e2
            rw [e1] at hreq
            rcases H0 j0 k hk (by omega) with h2 | ⟨j'', _, he⟩
            · exact Or.inl h2
            · exact Or.inr ⟨0, j'', Or.inl (Fin.succ_pos _), by simpa using he⟩
      · right
        refine ⟨i'.succ, j', ?_, by simpa using he⟩
        rcases hb with hb | ⟨rfl, hj⟩
        · exact Or.inl (Fin.succ_lt_succ_iff.mpr hb)
        · exact Or.inr ⟨rfl, hj⟩

/-! ## Counting by the first row -/

/-- Every row is allowed and consecutive rows are compatible. -/
def Valid {n : ℕ} (g : Fin n → Fin 3 → Fin 6) : Prop :=
  (∀ i, hrow (g i)) ∧ ∀ i i' : Fin n, i'.val = i.val + 1 → ok (g i) (g i')

instance {n : ℕ} : DecidablePred (@Valid n) := fun g => by unfold Valid; infer_instance

/-- W(n, r, c): the arrays of n + 1 rows from the row r on, every row allowed, consecutive rows
compatible, whose entries need only chain values that occur before them or are among 1..c. -/
def W (n : ℕ) (r : Fin 3 → Fin 6) (c : ℕ) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 3 → Fin 6)).filter (fun g => Valid g ∧ NormFrom c g ∧ g 0 = r)).card

lemma valid_cons {n : ℕ} (x : Fin 3 → Fin 6) (g : Fin (n + 1) → Fin 3 → Fin 6) :
    Valid (Fin.cons x g : Fin (n + 2) → Fin 3 → Fin 6) ↔ hrow x ∧ ok x (g 0) ∧ Valid g := by
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

lemma W_zero (r : Fin 3 → Fin 6) (c : ℕ) : W 0 r c = if hrow r ∧ rowNorm c r then 1 else 0 := by
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
      refine ⟨⟨fun _ => hr.1, ?_⟩, (NormFrom_one c _).2 hr.2, rfl⟩
      intro i j hij
      have := j.isLt
      omega
  · rw [Finset.card_eq_zero]
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨⟨h1, _⟩, hR, h0⟩
    apply hr
    rw [← h0]
    exact ⟨h1 0, (NormFrom_one c f).1 hR⟩

/-- Prepending the row r to an array with n + 1 rows. -/
def consEmb (n : ℕ) (r : Fin 3 → Fin 6) :
    (Fin (n + 1) → Fin 3 → Fin 6) ↪ (Fin (n + 2) → Fin 3 → Fin 6) where
  toFun g := Fin.cons r g
  inj' g g' h := by
    funext i
    have := congrFun h i.succ
    simpa using this

lemma consEmb_apply (n : ℕ) (r : Fin 3 → Fin 6) (g : Fin (n + 1) → Fin 3 → Fin 6) :
    consEmb n r g = Fin.cons r g := rfl

lemma W_succ (n : ℕ) (r : Fin 3 → Fin 6) (c : ℕ) :
    W (n + 1) r c = if hrow r ∧ rowNorm c r then
      ∑ s : Fin 3 → Fin 6, (if ok r s then W n s (newph c r) else 0) else 0 := by
  have e : ((univ : Finset (Fin (n + 2) → Fin 3 → Fin 6)).filter
      (fun f => Valid f ∧ NormFrom c f ∧ f 0 = r)) =
      (((univ : Finset (Fin (n + 1) → Fin 3 → Fin 6)).filter
        (fun g => ((hrow r ∧ rowNorm c r) ∧ ok r (g 0)) ∧ Valid g ∧
          NormFrom (newph c r) g)).map (consEmb n r)) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, consEmb_apply]
    constructor
    · rintro ⟨hv, hR, h0⟩
      refine ⟨Fin.tail f, ?_, ?_⟩
      · have hf : f = Fin.cons r (Fin.tail f) := by
          rw [← h0]; exact (Fin.cons_self_tail f).symm
        rw [hf, valid_cons] at hv
        rw [hf, NormFrom_cons] at hR
        exact ⟨⟨⟨hv.1, hR.1⟩, hv.2.1⟩, hv.2.2, hR.2⟩
      · rw [← h0]; exact Fin.cons_self_tail f
    · rintro ⟨g, ⟨⟨⟨h1, h2⟩, h3⟩, hg, hR⟩, rfl⟩
      exact ⟨(valid_cons r g).2 ⟨h1, h3, hg⟩, (NormFrom_cons c r g).2 ⟨h2, hR⟩, by simp⟩
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

lemma cond_iff {R : ℕ} (x : Fin R → Fin 3 → Fin 6) : Cond x ↔ Valid x := by
  unfold Cond Valid hrow ok
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => fun j j' hj => h1 i j j' hj, fun i i' hi => fun j j' hj => h2 i i' j j' hi hj⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j j' hj => h1 i j j' hj, fun i i' j j' hi hj => h2 i i' hi j j' hj⟩

lemma norm_iff {R : ℕ} (x : Fin R → Fin 3 → Fin 6) :
    Norm x ↔ (∀ i j, i.val = 0 → j.val = 0 → x i j = 0) ∧ NormFrom 0 x := by
  unfold Norm NormFrom
  constructor
  · rintro ⟨h0, h1, h2⟩
    refine ⟨h0, fun i j k hk hkr => Or.inr ?_⟩
    have hv : ((x i j = 2 ∨ x i j = 3 ∨ x i j = 4) ∧ k = 1) ∨ (x i j = 3 ∧ k = 2) := by
      revert hk hkr
      generalize x i j = v
      fin_cases v <;> simp [req] <;> omega
    rcases hv with ⟨hv, rfl⟩ | ⟨hv, rfl⟩
    · exact h1 i j hv
    · exact h2 i j hv
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun i j hv => ?_, fun i j hv => ?_⟩
    · rcases h i j 1 le_rfl (by rcases hv with hv | hv | hv <;> rw [hv] <;> decide) with h1 | h1
      · omega
      · exact h1
    · rcases h i j 2 (by norm_num) (by rw [hv]; decide) with h1 | h1
      · omega
      · exact h1

lemma a_eq (n : ℕ) : a (n + 1) = ∑ r : Fin 3 → Fin 6, if r 0 = 0 then W n r 0 else 0 := by
  unfold a
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g => g 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Finset.filter_filter]
  split_ifs with hr
  · unfold W
    congr 1
    refine Finset.filter_congr (fun g _ => ?_)
    rw [cond_iff, norm_iff]
    constructor
    · rintro ⟨⟨hv, _, hn⟩, h0⟩
      exact ⟨hv, hn, h0⟩
    · rintro ⟨hv, hn, h0⟩
      refine ⟨⟨hv, fun i j hi hj => ?_, hn⟩, h0⟩
      obtain rfl : i = 0 := Fin.ext hi
      obtain rfl : j = 0 := Fin.ext hj
      rw [h0]; exact hr
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro g _ hg
    rw [cond_iff, norm_iff] at hg
    obtain ⟨⟨_, h00, _⟩, h0⟩ := hg
    exact hr (by rw [← h0]; exact h00 0 0 rfl rfl)

/-! ## Kernel form of the transfer -/

lemma sum_cons {m : ℕ} (f : (Fin (m + 1) → Fin 6) → ℕ) :
    ∑ s : Fin (m + 1) → Fin 6, f s = ∑ x : Fin 6, ∑ t : Fin m → Fin 6, f (Fin.cons x t) := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 6).symm _ _
    (fun s => by simp [Fin.consEquiv, Fin.cons_self_tail])

lemma sum_row (f : (Fin 3 → Fin 6) → ℕ) :
    ∑ s : Fin 3 → Fin 6, f s = ∑ x : Fin 6, ∑ y : Fin 6, ∑ z : Fin 6, f ![x, y, z] := by
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Fintype.sum_unique]
  exact congrArg f (by funext j; fin_cases j <;> rfl)

lemma row_eta (r : Fin 3 → Fin 6) : r = ![r 0, r 1, r 2] := by
  funext j
  fin_cases j <;> rfl

/-- `hrow` as a Boolean. -/
def hrowB (r : Fin 3 → Fin 6) : Bool :=
  decide ((r 0).val + (r 1).val ≠ 5) &&
    decide ((r 1).val + (r 2).val ≠ 5)

/-- The condition read at cell 0 of the row below. -/
def G0 (r : Fin 3 → Fin 6) (b : Fin 6) : Bool := decide ((r 1).val + b.val ≠ 5)

/-- The condition read at cell 1 of the row below. -/
def G1 (r : Fin 3 → Fin 6) (b : Fin 6) : Bool := decide ((r 2).val + b.val ≠ 5)

/-- The condition read at cell 2 of the row below. -/
def G2 (r : Fin 3 → Fin 6) (b : Fin 6) : Bool := true

/-- `ok` as a Boolean. -/
def okB (r s : Fin 3 → Fin 6) : Bool :=
  G0 r (s 0) &&
    G1 r (s 1) &&
    G2 r (s 2)

/-- `rowNorm c r` as a Boolean. -/
def nB (c : ℕ) (r : Fin 3 → Fin 6) : Bool :=
  decide (req (r 0) ≤ c) &&
    decide (req (r 1) ≤ max c (cidx (r 0))) &&
    decide (req (r 2) ≤ max (max c (cidx (r 0))) (cidx (r 1)))

/-- `newph c r` by explicit maxima. -/
def phB (c : ℕ) (r : Fin 3 → Fin 6) : ℕ :=
  max (max (max c (cidx (r 0))) (cidx (r 1))) (cidx (r 2))

lemma hrow_iff (r : Fin 3 → Fin 6) : hrow r ↔ hrowB r = true := by
  simp only [hrowB, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  constructor
  · intro h
    exact ⟨h 0 1 rfl, h 1 2 rfl⟩
  · intro h j j' hj
    have := j'.isLt
    rcases (by omega : j.val = 0 ∨ j.val = 1) with e | e
    · obtain rfl : j = 0 := Fin.ext (by show j.val = 0; omega)
      obtain rfl : j' = 1 := Fin.ext (by show j'.val = 1; omega)
      exact h.1
    · obtain rfl : j = 1 := Fin.ext (by show j.val = 1; omega)
      obtain rfl : j' = 2 := Fin.ext (by show j'.val = 2; omega)
      exact h.2

lemma ok_iff (r s : Fin 3 → Fin 6) : ok r s ↔ okB r s = true := by
  simp only [ok, okB, G0, G1, G2, Bool.and_eq_true, decide_eq_true_eq,
    Bool.true_and, Bool.and_true, and_assoc]
  constructor
  · intro hA
    exact ⟨hA 1 0 rfl, hA 2 1 rfl⟩
  · intro h j j' hj
    have := j.isLt
    have := j'.isLt
    rcases (by omega : j'.val = 0 ∨ j'.val = 1) with e | e
    · obtain rfl : j = 1 := Fin.ext (by omega)
      obtain rfl : j' = 0 := Fin.ext (by omega)
      exact h.1
    · obtain rfl : j = 2 := Fin.ext (by omega)
      obtain rfl : j' = 1 := Fin.ext (by omega)
      exact h.2

lemma rowNorm_iff (c : ℕ) (r : Fin 3 → Fin 6) : rowNorm c r ↔ nB c r = true := by
  have e : rowNorm c r ↔ rowNorm c ![r 0, r 1, r 2] := by rw [← row_eta r]
  rw [e, rowNorm_cons, rowNorm_cons, rowNorm_cons]
  simp only [nB, rowNorm_zero, and_true, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

lemma newph_eq (c : ℕ) (r : Fin 3 → Fin 6) : newph c r = phB c r := by
  have e : newph c r = newph c ![r 0, r 1, r 2] := by rw [← row_eta r]
  rw [e, newph_cons, newph_cons, newph_cons, newph_zero]
  rfl

lemma phB_le (c : ℕ) (hc : c ≤ 2) (r : Fin 3 → Fin 6) : phB c r ≤ 2 := by
  rw [← newph_eq]
  exact newph_le c hc r

/-- One step of the transfer, the rows below r enumerated entry by entry. -/
def T (g : (Fin 3 → Fin 6) → ℕ → ℕ) (r : Fin 3 → Fin 6) (c : ℕ) : ℕ :=
  if (hrowB r && nB c r) = true then
    ∑ x : Fin 6, ∑ y : Fin 6, ∑ z : Fin 6, (if okB r ![x, y, z] = true then g ![x, y, z] (phB c r) else 0)
  else 0

lemma W_succT (n : ℕ) (r : Fin 3 → Fin 6) (c : ℕ) : W (n + 1) r c = T (W n) r c := by
  rw [W_succ, sum_row]
  unfold T
  simp only [hrow_iff, rowNorm_iff, ok_iff, newph_eq, Bool.and_eq_true]

lemma T_congr (g g' : (Fin 3 → Fin 6) → ℕ → ℕ) (r : Fin 3 → Fin 6) (c : ℕ)
    (h : ∀ s, g s (phB c r) = g' s (phB c r)) : T g r c = T g' r c := by
  unfold T
  simp only [h]

/-- `T` with the sums over the cells of the row below cut as soon as a cell fails. -/
def Tp (g : (Fin 3 → Fin 6) → ℕ → ℕ) (r : Fin 3 → Fin 6) (c : ℕ) : ℕ :=
  if (hrowB r && nB c r) = true then
    ∑ x : Fin 6, (if G0 r x = true then (∑ y : Fin 6, (if G1 r y = true then (∑ z : Fin 6, (if G2 r z = true then (g ![x, y, z] (phB c r)) else 0)) else 0)) else 0)
  else 0

lemma T_eq_Tp (g : (Fin 3 → Fin 6) → ℕ → ℕ) (r : Fin 3 → Fin 6) (c : ℕ) : T g r c = Tp g r c := by
  unfold T Tp
  by_cases hr : (hrowB r && nB c r) = true
  · rw [if_pos hr, if_pos hr]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases h0 : G0 r x = true
    · rw [if_pos h0]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      by_cases h1 : G1 r y = true
      · rw [if_pos h1]
        refine Finset.sum_congr rfl (fun z _ => ?_)
        by_cases h2 : G2 r z = true
        · rw [if_pos h2, if_pos (show okB r ![x, y, z] = true by simp [okB, h0, h1, h2])]
        · rw [if_neg h2, if_neg (show ¬ okB r ![x, y, z] = true by simp [okB, h2])]
      · rw [if_neg h1]
        simp [okB, h1]
    · rw [if_neg h0]
      simp [okB, h0]
  · rw [if_neg hr, if_neg hr]

/-- W(0) as a function. -/
def W0f (r : Fin 3 → Fin 6) (c : ℕ) : ℕ := if (hrowB r && nB c r) = true then 1 else 0

lemma W_zero' (r : Fin 3 → Fin 6) (c : ℕ) : W 0 r c = W0f r c := by
  rw [W_zero]
  unfold W0f
  simp only [hrow_iff, rowNorm_iff, Bool.and_eq_true]

/-- W(1, r, c) for c <= 2, nested by the entries of r and then c. -/
def L1 : List (List (List (List ℕ))) :=
  [[[[19, 63, 105], [63, 63, 105], [0, 105, 105], [0, 0, 105], [0, 63, 105], [0, 0, 0]], [[63, 63, 105], [63, 63, 105], [105, 105, 105], [0, 0, 105], [0, 0, 0], [63, 63, 105]], [[0, 105, 105], [0, 105, 105], [0, 105, 105], [0, 0, 0], [0, 105, 105], [0, 105, 105]], [[0, 0, 105], [0, 0, 105], [0, 0, 0], [0, 0, 105], [0, 0, 105], [0, 0, 105]], [[0, 63, 105], [0, 0, 0], [0, 105, 105], [0, 0, 105], [0, 63, 105], [0, 63, 105]], [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[63, 63, 105], [63, 63, 105], [105, 105, 105], [0, 0, 105], [63, 63, 105], [0, 0, 0]], [[63, 63, 105], [63, 63, 105], [105, 105, 105], [0, 0, 105], [0, 0, 0], [63, 63, 105]], [[105, 105, 105], [105, 105, 105], [105, 105, 105], [0, 0, 0], [105, 105, 105], [105, 105, 105]], [[0, 0, 105], [0, 0, 105], [0, 0, 0], [0, 0, 105], [0, 0, 105], [0, 0, 105]], [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [63, 63, 105], [105, 105, 105], [0, 0, 105], [63, 63, 105], [63, 63, 105]]], [[[0, 105, 105], [0, 105, 105], [0, 105, 105], [0, 105, 105], [0, 105, 105], [0, 0, 0]], [[0, 105, 105], [0, 105, 105], [0, 105, 105], [0, 105, 105], [0, 0, 0], [0, 105, 105]], [[0, 105, 105], [0, 105, 105], [0, 105, 105], [0, 0, 0], [0, 105, 105], [0, 105, 105]], [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 105, 105], [0, 0, 0], [0, 105, 105], [0, 105, 105], [0, 105, 105], [0, 105, 105]], [[0, 0, 0], [0, 105, 105], [0, 105, 105], [0, 105, 105], [0, 105, 105], [0, 105, 105]]], [[[0, 0, 105], [0, 0, 105], [0, 0, 105], [0, 0, 105], [0, 0, 105], [0, 0, 0]], [[0, 0, 105], [0, 0, 105], [0, 0, 105], [0, 0, 105], [0, 0, 0], [0, 0, 105]], [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 105], [0, 0, 105], [0, 0, 0], [0, 0, 105], [0, 0, 105], [0, 0, 105]], [[0, 0, 105], [0, 0, 0], [0, 0, 105], [0, 0, 105], [0, 0, 105], [0, 0, 105]], [[0, 0, 0], [0, 0, 105], [0, 0, 105], [0, 0, 105], [0, 0, 105], [0, 0, 105]]], [[[0, 63, 105], [0, 63, 105], [0, 105, 105], [0, 0, 105], [0, 63, 105], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 105, 105], [0, 105, 105], [0, 105, 105], [0, 0, 0], [0, 105, 105], [0, 105, 105]], [[0, 0, 105], [0, 0, 105], [0, 0, 0], [0, 0, 105], [0, 0, 105], [0, 0, 105]], [[0, 63, 105], [0, 0, 0], [0, 105, 105], [0, 0, 105], [0, 63, 105], [0, 63, 105]], [[0, 0, 0], [0, 63, 105], [0, 105, 105], [0, 0, 105], [0, 63, 105], [0, 63, 105]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]], [[63, 63, 105], [63, 63, 105], [105, 105, 105], [0, 0, 105], [0, 0, 0], [63, 63, 105]], [[0, 105, 105], [0, 105, 105], [0, 105, 105], [0, 0, 0], [0, 105, 105], [0, 105, 105]], [[0, 0, 105], [0, 0, 105], [0, 0, 0], [0, 0, 105], [0, 0, 105], [0, 0, 105]], [[0, 63, 105], [0, 0, 0], [0, 105, 105], [0, 0, 105], [0, 63, 105], [0, 63, 105]], [[0, 0, 0], [63, 63, 105], [0, 105, 105], [0, 0, 105], [0, 63, 105], [19, 63, 105]]]]

/-- W(1) as a table. -/
def tab1 (r : Fin 3 → Fin 6) (c : ℕ) : ℕ := (((L1.getD (r 0).val []).getD (r 1).val []).getD (r 2).val []).getD c 0

/-- W(2, r, c) for c <= 2, nested by the entries of r and then c. -/
def L2 : List (List (List (List ℕ))) :=
  [[[[1489, 5733, 11025], [5733, 5733, 11025], [0, 11025, 11025], [0, 0, 11025], [0, 5733, 11025], [0, 0, 0]], [[5733, 5733, 11025], [5733, 5733, 11025], [11025, 11025, 11025], [0, 0, 11025], [0, 0, 0], [5733, 5733, 11025]], [[0, 11025, 11025], [0, 11025, 11025], [0, 11025, 11025], [0, 0, 0], [0, 11025, 11025], [0, 11025, 11025]], [[0, 0, 11025], [0, 0, 11025], [0, 0, 0], [0, 0, 11025], [0, 0, 11025], [0, 0, 11025]], [[0, 5733, 11025], [0, 0, 0], [0, 11025, 11025], [0, 0, 11025], [0, 5733, 11025], [0, 5733, 11025]], [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]], [[[5733, 5733, 11025], [5733, 5733, 11025], [11025, 11025, 11025], [0, 0, 11025], [5733, 5733, 11025], [0, 0, 0]], [[5733, 5733, 11025], [5733, 5733, 11025], [11025, 11025, 11025], [0, 0, 11025], [0, 0, 0], [5733, 5733, 11025]], [[11025, 11025, 11025], [11025, 11025, 11025], [11025, 11025, 11025], [0, 0, 0], [11025, 11025, 11025], [11025, 11025, 11025]], [[0, 0, 11025], [0, 0, 11025], [0, 0, 0], [0, 0, 11025], [0, 0, 11025], [0, 0, 11025]], [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [5733, 5733, 11025], [11025, 11025, 11025], [0, 0, 11025], [5733, 5733, 11025], [5733, 5733, 11025]]], [[[0, 11025, 11025], [0, 11025, 11025], [0, 11025, 11025], [0, 11025, 11025], [0, 11025, 11025], [0, 0, 0]], [[0, 11025, 11025], [0, 11025, 11025], [0, 11025, 11025], [0, 11025, 11025], [0, 0, 0], [0, 11025, 11025]], [[0, 11025, 11025], [0, 11025, 11025], [0, 11025, 11025], [0, 0, 0], [0, 11025, 11025], [0, 11025, 11025]], [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 11025, 11025], [0, 0, 0], [0, 11025, 11025], [0, 11025, 11025], [0, 11025, 11025], [0, 11025, 11025]], [[0, 0, 0], [0, 11025, 11025], [0, 11025, 11025], [0, 11025, 11025], [0, 11025, 11025], [0, 11025, 11025]]], [[[0, 0, 11025], [0, 0, 11025], [0, 0, 11025], [0, 0, 11025], [0, 0, 11025], [0, 0, 0]], [[0, 0, 11025], [0, 0, 11025], [0, 0, 11025], [0, 0, 11025], [0, 0, 0], [0, 0, 11025]], [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 11025], [0, 0, 11025], [0, 0, 0], [0, 0, 11025], [0, 0, 11025], [0, 0, 11025]], [[0, 0, 11025], [0, 0, 0], [0, 0, 11025], [0, 0, 11025], [0, 0, 11025], [0, 0, 11025]], [[0, 0, 0], [0, 0, 11025], [0, 0, 11025], [0, 0, 11025], [0, 0, 11025], [0, 0, 11025]]], [[[0, 5733, 11025], [0, 5733, 11025], [0, 11025, 11025], [0, 0, 11025], [0, 5733, 11025], [0, 0, 0]], [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 11025, 11025], [0, 11025, 11025], [0, 11025, 11025], [0, 0, 0], [0, 11025, 11025], [0, 11025, 11025]], [[0, 0, 11025], [0, 0, 11025], [0, 0, 0], [0, 0, 11025], [0, 0, 11025], [0, 0, 11025]], [[0, 5733, 11025], [0, 0, 0], [0, 11025, 11025], [0, 0, 11025], [0, 5733, 11025], [0, 5733, 11025]], [[0, 0, 0], [0, 5733, 11025], [0, 11025, 11025], [0, 0, 11025], [0, 5733, 11025], [0, 5733, 11025]]], [[[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]], [[5733, 5733, 11025], [5733, 5733, 11025], [11025, 11025, 11025], [0, 0, 11025], [0, 0, 0], [5733, 5733, 11025]], [[0, 11025, 11025], [0, 11025, 11025], [0, 11025, 11025], [0, 0, 0], [0, 11025, 11025], [0, 11025, 11025]], [[0, 0, 11025], [0, 0, 11025], [0, 0, 0], [0, 0, 11025], [0, 0, 11025], [0, 0, 11025]], [[0, 5733, 11025], [0, 0, 0], [0, 11025, 11025], [0, 0, 11025], [0, 5733, 11025], [0, 5733, 11025]], [[0, 0, 0], [5733, 5733, 11025], [0, 11025, 11025], [0, 0, 11025], [0, 5733, 11025], [1489, 5733, 11025]]]]

/-- W(2) as a table. -/
def tab2 (r : Fin 3 → Fin 6) (c : ℕ) : ℕ := (((L2.getD (r 0).val []).getD (r 1).val []).getD (r 2).val []).getD c 0

set_option maxHeartbeats 4000000 in
lemma checks_all :
    (∀ c : Fin 3, ∀ y1 y2 y3 : Fin 6,
    Tp W0f ![y1, y2, y3] c.val = tab1 ![y1, y2, y3] c.val) ∧
    (∀ c : Fin 3, ∀ y1 y2 y3 : Fin 6,
    Tp tab1 ![y1, y2, y3] c.val = tab2 ![y1, y2, y3] c.val) ∧
    (∀ c : Fin 3, ∀ y1 y2 y3 : Fin 6,
    Tp tab2 ![y1, y2, y3] c.val + 2331 * tab1 ![y1, y2, y3] c.val =
      127 * tab2 ![y1, y2, y3] c.val + 2205 * W0f ![y1, y2, y3] c.val) ∧
    (∑ x : Fin 6, ∑ y : Fin 6, ∑ z : Fin 6, (if ![x, y, z] 0 = 0 then W0f ![x, y, z] 0 else 0) = 6) ∧
    (∑ x : Fin 6, ∑ y : Fin 6, ∑ z : Fin 6, (if ![x, y, z] 0 = 0 then tab1 ![x, y, z] 0 else 0) = 376) ∧
    (∑ x : Fin 6, ∑ y : Fin 6, ∑ z : Fin 6, (if ![x, y, z] 0 = 0 then tab2 ![x, y, z] 0 else 0) = 35446) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c y1
    fin_cases c <;> fin_cases y1 <;> decide +kernel
  · intro c y1
    fin_cases c <;> fin_cases y1 <;> decide +kernel
  · intro c y1
    fin_cases c <;> fin_cases y1 <;> decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

lemma check1 : ∀ c : Fin 3, ∀ y1 y2 y3 : Fin 6,
    Tp W0f ![y1, y2, y3] c.val = tab1 ![y1, y2, y3] c.val := checks_all.1

lemma check2 : ∀ c : Fin 3, ∀ y1 y2 y3 : Fin 6,
    Tp tab1 ![y1, y2, y3] c.val = tab2 ![y1, y2, y3] c.val := checks_all.2.1

lemma check_rel : ∀ c : Fin 3, ∀ y1 y2 y3 : Fin 6,
    Tp tab2 ![y1, y2, y3] c.val + 2331 * tab1 ![y1, y2, y3] c.val =
      127 * tab2 ![y1, y2, y3] c.val + 2205 * W0f ![y1, y2, y3] c.val := checks_all.2.2.1

lemma sum1 : ∑ x : Fin 6, ∑ y : Fin 6, ∑ z : Fin 6, (if ![x, y, z] 0 = 0 then W0f ![x, y, z] 0 else 0) = 6 := checks_all.2.2.2.1

lemma sum2 : ∑ x : Fin 6, ∑ y : Fin 6, ∑ z : Fin 6, (if ![x, y, z] 0 = 0 then tab1 ![x, y, z] 0 else 0) = 376 := checks_all.2.2.2.2.1

lemma sum3 : ∑ x : Fin 6, ∑ y : Fin 6, ∑ z : Fin 6, (if ![x, y, z] 0 = 0 then tab2 ![x, y, z] 0 else 0) = 35446 := checks_all.2.2.2.2.2

lemma W_1 (r : Fin 3 → Fin 6) (c : ℕ) (hc : c ≤ 2) : W 1 r c = tab1 r c := by
  rw [W_succT, T_congr _ W0f r c (fun s => W_zero' s _), T_eq_Tp, row_eta r]
  exact check1 ⟨c, by omega⟩ (r 0) (r 1) (r 2)

lemma W_2 (r : Fin 3 → Fin 6) (c : ℕ) (hc : c ≤ 2) : W 2 r c = tab2 r c := by
  rw [show W 2 r c = W (1 + 1) r c from rfl, W_succT,
    T_congr _ tab1 r c (fun s => W_1 s _ (phB_le c hc r)), T_eq_Tp, row_eta r]
  exact check2 ⟨c, by omega⟩ (r 0) (r 1) (r 2)

lemma W_rec (n : ℕ) : ∀ (r : Fin 3 → Fin 6) (c : ℕ), c ≤ 2 → W (n + 3) r c + 2331 * W (n + 1) r c = 127 * W (n + 2) r c + 2205 * W n r c := by
  induction n with
  | zero =>
    intro r c hc
    rw [show W (0 + 3) r c = W (2 + 1) r c from rfl, W_succT 2 r c,
      T_congr _ tab2 r c (fun s => W_2 s _ (phB_le c hc r)),
      W_zero' r c,
      show W (0 + 1) r c = W 1 r c from rfl, W_1 r c hc,
      show W (0 + 2) r c = W 2 r c from rfl, W_2 r c hc,
      T_eq_Tp,
      row_eta r]
    exact check_rel ⟨c, by omega⟩ (r 0) (r 1) (r 2)
  | succ n ih =>
    intro r c hc
    rw [W_succT (n + 3) r c, W_succT (n + 2) r c, W_succT (n + 1) r c, W_succT n r c]
    unfold T
    by_cases h : (hrowB r && nB c r) = true
    · rw [if_pos h, if_pos h, if_pos h, if_pos h]
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      split_ifs
      · exact ih _ _ (phB_le c hc r)
      · simp
    · rw [if_neg h, if_neg h, if_neg h, if_neg h] <;> simp

lemma a_rec (n : ℕ) : a (n + 4) + 2331 * a (n + 2) = 127 * a (n + 3) + 2205 * a (n + 1) := by
  rw [a_eq, a_eq, a_eq, a_eq, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  split_ifs
  · exact W_rec n r 0 (by norm_num)
  · simp

lemma a_1 : a 1 = 6 := by
  rw [show a 1 = a (0 + 1) from rfl, a_eq, sum_row]
  have h : ∀ r : Fin 3 → Fin 6, (if r 0 = 0 then W 0 r 0 else 0) = (if r 0 = 0 then W0f r 0 else 0) := fun r => by split_ifs <;> simp only [W_zero']
  simp only [h]
  exact sum1

lemma a_2 : a 2 = 376 := by
  rw [show a 2 = a (1 + 1) from rfl, a_eq, sum_row]
  have h : ∀ r : Fin 3 → Fin 6, (if r 0 = 0 then W 1 r 0 else 0) = (if r 0 = 0 then tab1 r 0 else 0) := fun r => by split_ifs <;> simp only [W_1 r 0 (by norm_num)]
  simp only [h]
  exact sum2

lemma a_3 : a 3 = 35446 := by
  rw [show a 3 = a (2 + 1) from rfl, a_eq, sum_row]
  have h : ∀ r : Fin 3 → Fin 6, (if r 0 = 0 then W 2 r 0 else 0) = (if r 0 = 0 then tab2 r 0 else 0) := fun r => by split_ifs <;> simp only [W_2 r 0 (by norm_num)]
  simp only [h]
  exact sum3

/-- Barker's g.f.: 2x(3 - 193x + 840x^2) / ((1 - x)(1 - 21x)(1 - 105x)). -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 - 21 * X) * (1 - 105 * X)) = 2 * X * (3 - 193 * X + 840 * X ^ 2) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - X) * (1 - 21 * X) * (1 - 105 * X)) = A - A * X ^ 1 * C 127 + A * X ^ 2 * C 2331 - A * X ^ 3 * C 2205 := by
    rw [show (C (127 : ℚ) : ℚ⟦X⟧) = 127 from map_ofNat C 127,
      show (C (2205 : ℚ) : ℚ⟦X⟧) = 2205 from map_ofNat C 2205,
      show (C (2331 : ℚ) : ℚ⟦X⟧) = 2331 from map_ofNat C 2331]
    ring
  have e2 : (2 * X * (3 - 193 * X + 840 * X ^ 2) : ℚ⟦X⟧) = X ^ 1 * C 6 - X ^ 2 * C 386 + X ^ 3 * C 1680 := by
    rw [show (C (6 : ℚ) : ℚ⟦X⟧) = 6 from map_ofNat C 6,
      show (C (386 : ℚ) : ℚ⟦X⟧) = 386 from map_ofNat C 386,
      show (C (1680 : ℚ) : ℚ⟦X⟧) = 1680 from map_ofNat C 1680]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk]
  rcases n with _ | _ | _ | _ | n
  · simp
  · simp [a_1] <;> norm_num
  · simp [a_1, a_2] <;> norm_num
  · simp [a_1, a_2, a_3] <;> norm_num
  · have h := a_rec n
    
    have hq : (a (n + 4) : ℚ) + 2331 * (a (n + 2) : ℚ) = 127 * (a (n + 3) : ℚ) + 2205 * (a (n + 1) : ℚ) := by exact_mod_cast h
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

/-- The closed form from the recurrence and the first values. -/
theorem cf (b : ℕ → ℕ) (h1 : b 1 = 6) (h2 : b 2 = 376) (h3 : b 3 = 35446)
    (hr : ∀ n, b (n + 4) + 2331 * b (n + 2) = 127 * b (n + 3) + 2205 * b (n + 1)) :
    ∀ n : ℕ, 1 ≤ n → (b n : ℚ) = (105 + 2 * 3 ^ (2 + n) * 7 ^ n + 5 ^ (1 + n) * 21 ^ n) / 168 := by
  set G : ℕ → ℚ := fun n => (105 + 2 * 3 ^ (2 + n) * 7 ^ n + 5 ^ (1 + n) * 21 ^ n) / 168 with hG
  have Grec : ∀ n, G (n + 3) + 2331 * G (n + 1) = 2205 * G n + 127 * G (n + 2) := by
    intro n
    simp only [hG]
    ring
  have key : ∀ k, (b (k + 1) : ℚ) = G (k + 1) ∧ (b (k + 2) : ℚ) = G (k + 2) ∧ (b (k + 3) : ℚ) = G (k + 3) := by
    intro k
    induction k with
    | zero =>
      simp only [hG, Nat.zero_add]
      rw [h1, h2, h3]
      norm_num
    | succ k ih =>
      obtain ⟨i1, i2, i3⟩ := ih
      refine ⟨i2, i3, ?_⟩
      have hq : ((b (k + 4) + 2331 * b (k + 2) : ℕ) : ℚ) = ((127 * b (k + 3) + 2205 * b (k + 1) : ℕ) : ℚ) := by
        exact_mod_cast hr k
      push_cast at hq
      have hg : G (k + 4) + 2331 * G (k + 2) = 2205 * G (k + 1) + 127 * G (k + 3) := Grec (k + 1)
      linear_combination hq + 2205 * i1 + 127 * i3 - 2331 * i2 - hg
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact (key k).1

/-- Barker's closed form. -/
theorem closed_form : ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (105 + 2 * 3 ^ (2 + n) * 7 ^ n + 5 ^ (1 + n) * 21 ^ n) / 168 :=
  cf a a_1 a_2 a_3 a_rec

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 - 21 * X) * (1 - 105 * X)) = 2 * X * (3 - 193 * X + 840 * X ^ 2) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (105 + 2 * 3 ^ (2 + n) * 7 ^ n + 5 ^ (1 + n) * 21 ^ n) / 168 :=
  ⟨gf, closed_form⟩

/-- Controls: the entry's terms a(1..10). -/
theorem controls : a 1 = 6 ∧ a 2 = 376 ∧ a 3 = 35446 ∧ a 4 = 3638416 ∧ a 5 = 380283286 ∧ a 6 = 39892988056 ∧ a 7 = 4187991850726 ∧ a 8 = 439722934529296 ∧ a 9 = 46170567719841766 ∧ a 10 = 4847902462062966136 := by
  have r0 := a_rec 0; have r1 := a_rec 1; have r2 := a_rec 2; have r3 := a_rec 3; have r4 := a_rec 4; have r5 := a_rec 5; have r6 := a_rec 6
  have h1 := a_1; have h2 := a_2; have h3 := a_3
  norm_num at r0 r1 r2 r3 r4 r5 r6
  omega

end OMA.S_oeis_a233212

theorem OMA.solution : type_of% @OMA.S_oeis_a233212.main :=
  OMA.S_oeis_a233212.conjecture
