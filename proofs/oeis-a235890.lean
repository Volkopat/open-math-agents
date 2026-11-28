import OMAStatements.S_oeis_a235890

namespace OMA.S_oeis_a235890

open PowerSeries Finset



/-! ## The window condition, rows and the transfer -/

/-- A row. -/
abbrev Row := Fin 6 → Fin 4

/-- The window condition on the 2 X 2 block with top row (p, q) and bottom row (r, s). -/
def P (p q r s : Fin 4) : Prop :=
  medEq (p).val (q).val (r).val (s).val = true

instance (p q r s : Fin 4) : Decidable (P p q r s) := by unfold P; infer_instance

/-- Row s may follow row r: every block between them satisfies P. -/
def rowOK (r s : Fin 6 → Fin 4) : Prop :=
  ∀ j j' : Fin 6, j'.val = j.val + 1 → P (r j) (r j') (s j) (s j')

instance : DecidableRel rowOK := fun r s => by unfold rowOK; infer_instance

/-- Consecutive rows allowed. -/
def Valid {m : ℕ} (x : Fin m → Fin 6 → Fin 4) : Prop :=
  ∀ i i' : Fin m, i'.val = i.val + 1 → rowOK (x i) (x i')

instance {m : ℕ} : DecidablePred (@Valid m) := fun x => by unfold Valid; infer_instance

/-- The number of valid arrays with n + 1 rows. -/
def cnt (n : ℕ) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 6 → Fin 4)).filter Valid).card

lemma a_eq (n : ℕ) : a n = cnt n := by
  unfold a cnt
  exact congrArg Finset.card (Finset.filter_congr (fun x _ => Iff.rfl))

/-- W(n, r): valid arrays with n + 1 rows whose first row is r. -/
def W (n : ℕ) (r : Fin 6 → Fin 4) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 6 → Fin 4)).filter (fun x => Valid x ∧ x 0 = r)).card

lemma valid_cons {n : ℕ} (r : Row) (g : Fin (n + 1) → Row) :
    Valid (Fin.cons r g : Fin (n + 2) → Row) ↔ rowOK r (g 0) ∧ Valid g := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := h 0 1 (by simp)
      simpa using this
    · intro i j hij
      have := h i.succ j.succ (by simp [hij])
      simpa using this
  · rintro ⟨h0, hg⟩ i j hij
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
        exact hg i j (by simp at hij; omega)

lemma cnt_sum (n : ℕ) : cnt n = ∑ r : Row, W n r := by
  unfold cnt W
  rw [Finset.card_eq_sum_card_fiberwise (f := fun f => f 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  congr 1
  ext f
  simp

lemma W_zero (r : Row) : W 0 r = 1 := by
  unfold W
  rw [Finset.card_eq_one]
  refine ⟨fun _ => r, ?_⟩
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨_, hf⟩
    funext i
    rw [Fin.fin_one_eq_zero i, hf]
  · rintro rfl
    refine ⟨?_, rfl⟩
    intro i j hij
    have := j.isLt
    omega

/-- Prepending the row r. -/
def consEmb (n : ℕ) (r : Row) : (Fin (n + 1) → Row) ↪ (Fin (n + 2) → Row) where
  toFun g := Fin.cons r g
  inj' g g' h := by
    funext i
    have := congrFun h i.succ
    simpa using this

lemma consEmb_apply (n : ℕ) (r : Row) (g : Fin (n + 1) → Row) :
    consEmb n r g = Fin.cons r g := rfl

lemma W_succ (n : ℕ) (r : Row) :
    W (n + 1) r = ∑ s : Row, if rowOK r s then W n s else 0 := by
  have e : ((univ : Finset (Fin (n + 2) → Row)).filter (fun f => Valid f ∧ f 0 = r)) =
      (((univ : Finset (Fin (n + 1) → Row)).filter (fun g => rowOK r (g 0) ∧ Valid g)).map
        (consEmb n r)) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, consEmb_apply]
    constructor
    · rintro ⟨hv, h0⟩
      refine ⟨Fin.tail f, ?_, ?_⟩
      · have hf : f = Fin.cons r (Fin.tail f) := by
          rw [← h0]; exact (Fin.cons_self_tail f).symm
        rw [hf, valid_cons] at hv
        exact hv
      · rw [← h0]; exact Fin.cons_self_tail f
    · rintro ⟨g, hg, rfl⟩
      exact ⟨(valid_cons r g).2 hg, by simp⟩
  unfold W
  rw [e, Finset.card_map]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g => g 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  split_ifs with hrs
  · congr 1
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨_, hg⟩, h0⟩
      exact ⟨hg, h0⟩
    · rintro ⟨hg, h0⟩
      exact ⟨⟨h0 ▸ hrs, hg⟩, h0⟩
  · rw [Finset.card_eq_zero]
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨⟨hok, _⟩, h0⟩
    exact hrs (h0 ▸ hok)

lemma sum_cons {m : ℕ} (f : (Fin (m + 1) → Fin 4) → ℕ) :
    ∑ s : Fin (m + 1) → Fin 4, f s = ∑ x : Fin 4, ∑ t : Fin m → Fin 4, f (Fin.cons x t) := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 4).symm _ _
    (fun s => by simp [Fin.consEquiv, Fin.cons_self_tail])

lemma sum_row (f : Row → ℕ) :
    ∑ s : Row, f s = ∑ x0 : Fin 4, ∑ x1 : Fin 4, ∑ x2 : Fin 4, ∑ x3 : Fin 4, ∑ x4 : Fin 4, ∑ x5 : Fin 4, f ![x0, x1, x2, x3, x4, x5] := by
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x0 _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x1 _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x2 _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x3 _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x4 _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x5 _ => ?_)
  rw [Fintype.sum_unique]
  exact congrArg f (by funext j; fin_cases j <;> rfl)

lemma row_eta (r : Row) : r = ![r 0, r 1, r 2, r 3, r 4, r 5] := by
  funext j
  fin_cases j <;> rfl

lemma rowOK_iff (r s : Row) : rowOK r s ↔ P (r 0) (r 1) (s 0) (s 1) ∧ P (r 1) (r 2) (s 1) (s 2) ∧ P (r 2) (r 3) (s 2) (s 3) ∧ P (r 3) (r 4) (s 3) (s 4) ∧ P (r 4) (r 5) (s 4) (s 5) := by
  constructor
  · intro h
    exact ⟨h 0 1 rfl, h 1 2 rfl, h 2 3 rfl, h 3 4 rfl, h 4 5 rfl⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ j j' hj
    rcases j with ⟨j, hj0⟩
    rcases j' with ⟨j', hj1⟩
    simp only at hj
    subst hj
    have hjw : j < 5 := by omega
    interval_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4

/-! ## The transfer on row codes, as evaluated by the kernel -/

/-- The window condition on numbers: bit ((p K + q) K + r) K + s of a mask. -/
def PN (p q r s : ℕ) : Bool := Nat.testBit 59764098895288494110966848158054725425867294195120340983151555958713428902945 (((p * 4 + q) * 4 + r) * 4 + s)

lemma P_iff (p q r s : Fin 4) : P p q r s ↔ PN p.val q.val r.val s.val = true := by
  revert p q r s
  decide +kernel

/-- The sum of f over 0, ..., 3. -/
def sumK (f : ℕ → ℕ) : ℕ := f 0 + f 1 + f 2 + f 3

lemma sumK_fin (f : ℕ → ℕ) : ∑ x : Fin 4, f x.val = sumK f := by
  rw [Fin.sum_univ_eq_sum_range (fun x => f x) 4]
  simp [Finset.sum_range_succ, sumK]

/-- The code of a row: its entries as base-K digits, r 0 the most significant. -/
def code (r : Row) : ℕ := (((((r 0).val * 4 + (r 1).val) * 4 + (r 2).val) * 4 + (r 3).val) * 4 + (r 4).val) * 4 + (r 5).val

lemma code_lt (r : Row) : code r < 4096 := by
  unfold code; have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; have h3 := (r 3).isLt; have h4 := (r 4).isLt; have h5 := (r 5).isLt; omega

lemma dig0 (r : Row) : code r / 1024 % 4 = (r 0).val := by
  unfold code; have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; have h3 := (r 3).isLt; have h4 := (r 4).isLt; have h5 := (r 5).isLt; omega

lemma dig1 (r : Row) : code r / 256 % 4 = (r 1).val := by
  unfold code; have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; have h3 := (r 3).isLt; have h4 := (r 4).isLt; have h5 := (r 5).isLt; omega

lemma dig2 (r : Row) : code r / 64 % 4 = (r 2).val := by
  unfold code; have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; have h3 := (r 3).isLt; have h4 := (r 4).isLt; have h5 := (r 5).isLt; omega

lemma dig3 (r : Row) : code r / 16 % 4 = (r 3).val := by
  unfold code; have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; have h3 := (r 3).isLt; have h4 := (r 4).isLt; have h5 := (r 5).isLt; omega

lemma dig4 (r : Row) : code r / 4 % 4 = (r 4).val := by
  unfold code; have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; have h3 := (r 3).isLt; have h4 := (r 4).isLt; have h5 := (r 5).isLt; omega

lemma dig5 (r : Row) : code r % 4 = (r 5).val := by
  unfold code; have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; have h3 := (r 3).isLt; have h4 := (r 4).isLt; have h5 := (r 5).isLt; omega

/-- Level 5 of the transfer: the entry x below r5, next to the previous entry p. -/
def N5 (g : ℕ → ℕ) (r4 r5 : ℕ) (p acc : ℕ) : ℕ :=
  sumK (fun x => if PN r4 r5 p x then g (acc * 4 + x) else 0)

/-- Level 4 of the transfer: the entry x below r4, next to the previous entry p. -/
def N4 (g : ℕ → ℕ) (r3 r4 r5 : ℕ) (p acc : ℕ) : ℕ :=
  sumK (fun x => if PN r3 r4 p x then N5 g r4 r5 x (acc * 4 + x) else 0)

/-- Level 3 of the transfer: the entry x below r3, next to the previous entry p. -/
def N3 (g : ℕ → ℕ) (r2 r3 r4 r5 : ℕ) (p acc : ℕ) : ℕ :=
  sumK (fun x => if PN r2 r3 p x then N4 g r3 r4 r5 x (acc * 4 + x) else 0)

/-- Level 2 of the transfer: the entry x below r2, next to the previous entry p. -/
def N2 (g : ℕ → ℕ) (r1 r2 r3 r4 r5 : ℕ) (p acc : ℕ) : ℕ :=
  sumK (fun x => if PN r1 r2 p x then N3 g r2 r3 r4 r5 x (acc * 4 + x) else 0)

/-- Level 1 of the transfer: the entry x below r1, next to the previous entry p. -/
def N1 (g : ℕ → ℕ) (r0 r1 r2 r3 r4 r5 : ℕ) (p acc : ℕ) : ℕ :=
  sumK (fun x => if PN r0 r1 p x then N2 g r1 r2 r3 r4 r5 x (acc * 4 + x) else 0)

/-- One step of the transfer: the sum of g over the codes of the rows allowed below the row with entries r0, r1, .... -/
def Tn (g : ℕ → ℕ) (r0 r1 r2 r3 r4 r5 : ℕ) : ℕ :=
  sumK (fun x => N1 g r0 r1 r2 r3 r4 r5 x x)

/-- The sum of g over all row codes. -/
def Ts (g : ℕ → ℕ) : ℕ := sumK (fun x0 => sumK (fun x1 => sumK (fun x2 => sumK (fun x3 => sumK (fun x4 => sumK (fun x5 => g (((((x0 * 4 + x1) * 4 + x2) * 4 + x3) * 4 + x4) * 4 + x5)))))))

lemma bridge (g : ℕ → ℕ) (r : Row) :
    (∑ s : Row, if rowOK r s then g (code s) else 0) = Tn g (r 0).val (r 1).val (r 2).val (r 3).val (r 4).val (r 5).val := by
  rw [sum_row]
  simp only [rowOK_iff, P_iff, code, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_succ]
  simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero]
  unfold Tn N1 N2 N3 N4 N5
  simp only [← sumK_fin]

lemma total (g : ℕ → ℕ) : (∑ s : Row, g (code s)) = Ts g := by
  rw [sum_row]
  simp only [code, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_succ]
  unfold Ts
  simp only [← sumK_fin]

/-- W(0, r) = 1. -/
def tab0 (_ : ℕ) : ℕ := 1

/-- W(1, r) for every row r, packed: the entry of r is the base 2^3 digit number code r. -/
def L1 : ℕ := 0x89248945144a48948924924945124945124944a24924944a48948924924948948924924924924924924924924924924945124945124924924924924945124945124924924924924944a24924944a24924924924924924924924944a24924944a48948924924948948924924924924924924924924924924948948924924948948924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924945124945124924924924924945124945124924924924924924924924924924924924924924924924924924924924924945124945124924924924924945124945124924924924924924924924924924924924924924924924924924924924924944a24924944a24924924924924924924924944a24924944a24924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924944a24924944a24924924924924924924924944a24924944a48948924924948948924924924924924924924924924924948948924924948948924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924948948924924948948924924924924924924924924924924948948924924948951229128a24929129124924928a24928a24924924924924929129124924929129124924924924924924924924924924928a24928a24924924924924928a24928a24924924924924924924924924924924924924924924924924924924924924929129124924929129124924924924924924924924924924929129124924929129124924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924928a24928a24924924924924928a24928a24924924924924924924924924924924924924924924924924924924924924928a24928a24924924924924928a24928a4512494512492492492492494512494512492492492492492492492492492492492492492492492492492492492492494512494512492492492492494512494512492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492492912912492492912912492492492492492492492492492492912912492492912912492492492492492492492492492492492492492492492492492492492492494512494512492492492492494512494512492492492492492492492492492492912912492492912912492492492492494512494512492492912912494512914a225224924925225224924924924924924924924924924925225224924925225224924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924925225224924925225224924924924924924924924924924925225224924925225244a24924944a24924924924924924924924944a24924944a24924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924944a24924944a24924924924924924924924944a24924944a24924924924924924924924924924924924924924924924924924924924924928a24928a24924924924924928a24928a24924924924924924924924924924924924924924924924924924924924924928a24928a24924924924924928a24928a24924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924925225224924925225224924924924924924924924924924925225224924925225244a24924944a24924924924924924924924944a24924944a24924924924924928a24928a24924924924924928a24928a24924924924924924924924924924925225224924925225244a24924944a24928a24928a24924925225244a28a252494

def tab1 (c : ℕ) : ℕ := L1 / 2 ^ (3 * c) % 2 ^ 3

/-- W(2, r) for every row r, packed: the entry of r is the base 2^5 digit number code r. -/
def L2 : ℕ := 0x81084210212048120424210212102108421084212048108421204810842120424084210842120424210212102108421084212102121021084210842108421084210842108421084210842108421084212048108421204810842108421084210842108421204810842120481084210842108421084210842120424084210842120424084210842108421084210842108421084210842120424084210842120424210212102108421084212102121021084210842108421084210842108421084210842108421084212102121021084210842121021210210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084212048108421204810842108421084210842108421204810842120481084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421204810842120481084210842108421084210842120481084212048108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842120424084210842120424084210842108421084210842108421084210842120424084210842120424084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842120424084210842120424084210842108421084210842108421084210842120424084210842120424210212102108421084212102121021084210842108421084210842108421084210842108421084212102121021084210842121021210210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084212102121021084210842121021210210842108421084210842108421084210842108421084210842121021210210842108421210212408409081090240842109081090810842108421090240842109024084210842108421084210842109081090810842108421090810908108421084210842108421084210842108421084210842108421090240842109024084210842108421084210842109024084210902408421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842109081090810842108421090810908108421084210842108421084210842108421084210842108421090810908108421084210908109081084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421090240842109024084210842108421084210842109024084210902408421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842109024084210902408421084210842108421084210902408421090242048108421204810842108421084210842108421204810842120481084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421204810842120481084210842108421084210842120481084212048108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842109081090810842108421090810908108421084210842108421084210842108421084210842108421090810908108421084210908109081084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421204810842120481084210842108421084210842120481084212048108421084210842108421084210842108421084210842108421090810908108421084210908109081084210842108421084210842120481084212048108421084210908109081084212048109081212040848408421084210848408484084210842108421084210842108421084210842108421084210848408484084210842108484084840842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210848408484084210842108484084840842108421084210842108421084210842108421084210842108484084840842108421084840848420424084210842120424084210842108421084210842108421084210842120424084210842120424084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842120424084210842120424084210842108421084210842108421084210842120424084210842120424084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421090240842109024084210842108421084210842109024084210902408421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842109024084210902408421084210842108421084210902408421090240842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210848408484084210842108484084840842108421084210842108421084210842108421084210842108484084840842108421084840848420424084210842120424084210842108421084210842108421084210842120424084210842120424084210842108421084210842109024084210902408421084210842108421084210902408421090240842108421084210842108421084210842108421084210842108484084840842108421084840848420424084210842120424084210902408421090240842108421084840848420424090240848421090

def tab2 (c : ℕ) : ℕ := L2 / 2 ^ (5 * c) % 2 ^ 5

def t0 (r : Row) : ℕ := tab0 (code r)

def t1 (r : Row) : ℕ := tab1 (code r)

def t2 (r : Row) : ℕ := tab2 (code r)

lemma W0f : W 0 = t0 := by
  funext r
  exact W_zero r

/-- The table step W(1) = T W(0) at the row with code c. -/
def stepB1 (c : ℕ) : Bool := Tn tab0 (c / 1024 % 4) (c / 256 % 4) (c / 64 % 4) (c / 16 % 4) (c / 4 % 4) (c % 4) == tab1 c

/-- The table step W(2) = T W(1) at the row with code c. -/
def stepB2 (c : ℕ) : Bool := Tn tab1 (c / 1024 % 4) (c / 256 % 4) (c / 64 % 4) (c / 16 % 4) (c / 4 % 4) (c % 4) == tab2 c

/-- The relation on the tables, at the row with code c. -/
def relB (c : ℕ) : Bool := Tn tab2 (c / 1024 % 4) (c / 256 % 4) (c / 64 % 4) (c / 16 % 4) (c / 4 % 4) (c % 4) + 14 * tab1 c == 7 * tab2 c + 8 * tab0 c

/-- Every check on the row with code c: the table steps and the relation. -/
def rowB (c : ℕ) : Bool := stepB1 c && stepB2 c && relB c

lemma chunk0_ok : (List.range' 0 682).all rowB = true := by
  decide +kernel

lemma chunk1_ok : (List.range' 682 683).all rowB = true := by
  decide +kernel

lemma chunk2_ok : (List.range' 1365 683).all rowB = true := by
  decide +kernel

lemma chunk3_ok : (List.range' 2048 682).all rowB = true := by
  decide +kernel

lemma chunk4_ok : (List.range' 2730 683).all rowB = true := by
  decide +kernel

lemma chunk5_ok : (List.range' 3413 683).all rowB = true := by
  decide +kernel

/-- The totals of the tables. -/
def allB : Bool := (Ts tab0 == 4096) && (Ts tab1 == 4480) && (Ts tab2 == 5272)

lemma all_ok : allB = true := by
  decide +kernel

lemma all_parts : True ∧ (Ts tab0 == 4096) = true ∧ (Ts tab1 == 4480) = true ∧ (Ts tab2 == 5272) = true := by
  have h := all_ok
  unfold allB at h
  simp only [Bool.and_eq_true] at h
  exact ⟨trivial, h.1.1, h.1.2, h.2⟩

lemma row_ok (c : ℕ) (hc : c < 4096) : stepB1 c = true ∧ stepB2 c = true ∧ relB c = true := by
  have h : rowB c = true := by
    by_cases h0 : c < 682
    · exact List.all_eq_true.mp chunk0_ok c (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    by_cases h1 : c < 1365
    · exact List.all_eq_true.mp chunk1_ok c (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    by_cases h2 : c < 2048
    · exact List.all_eq_true.mp chunk2_ok c (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    by_cases h3 : c < 2730
    · exact List.all_eq_true.mp chunk3_ok c (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    by_cases h4 : c < 3413
    · exact List.all_eq_true.mp chunk4_ok c (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    by_cases h5 : c < 4096
    · exact List.all_eq_true.mp chunk5_ok c (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    omega
  unfold rowB at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

lemma W1f : W 1 = t1 := by
  funext r
  rw [W_succ]
  simp only [W0f, t0]
  rw [bridge]
  have h := (row_ok (code r) (code_lt r)).1
  unfold stepB1 at h
  rw [dig0 r, dig1 r, dig2 r, dig3 r, dig4 r, dig5 r] at h
  exact beq_iff_eq.mp h

lemma W2f : W 2 = t2 := by
  funext r
  rw [W_succ]
  simp only [W1f, t1]
  rw [bridge]
  have h := (row_ok (code r) (code_lt r)).2.1
  unfold stepB2 at h
  rw [dig0 r, dig1 r, dig2 r, dig3 r, dig4 r, dig5 r] at h
  exact beq_iff_eq.mp h

lemma rel_at (r : Row) : Tn tab2 (r 0).val (r 1).val (r 2).val (r 3).val (r 4).val (r 5).val + 14 * tab1 (code r) = 7 * tab2 (code r) + 8 * tab0 (code r) := by
  have h := (row_ok (code r) (code_lt r)).2.2
  unfold relB at h
  rw [dig0 r, dig1 r, dig2 r, dig3 r, dig4 r, dig5 r] at h
  exact beq_iff_eq.mp h

/-- The per-row relation: the g.f. denominator annihilates W(k + 0), ..., W(k + 3). -/
lemma W_rec (k : ℕ) : ∀ r : Row, W (k + 3) r + 14 * W (k + 1) r = 7 * W (k + 2) r + 8 * W (k + 0) r := by
  induction k with
  | zero =>
    intro r
    simp only [Nat.zero_add, W0f, W1f, W2f, t0, t1, t2]
    rw [W_succ]
    simp only [W2f, t2]
    rw [bridge]
    exact rel_at r
  | succ k ih =>
    intro r
    rw [show k + 1 + 0 = (k + 0) + 1 from rfl, show k + 1 + 1 = (k + 1) + 1 from rfl, show k + 1 + 2 = (k + 2) + 1 from rfl, show k + 1 + 3 = (k + 3) + 1 from rfl]
    rw [W_succ (k + 0), W_succ (k + 1), W_succ (k + 2), W_succ (k + 3)]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    split_ifs
    · exact ih s
    · simp

lemma cnt_rec (k : ℕ) : cnt (k + 3)  + 14 * cnt (k + 1)  = 7 * cnt (k + 2)  + 8 * cnt (k + 0)  := by
  simp only [cnt_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun r _ => W_rec k r)

lemma cnt0 : cnt 0 = 4096 := by
  rw [cnt_sum, W0f]
  unfold t0
  rw [total]
  exact beq_iff_eq.mp all_parts.2.1

lemma cnt1 : cnt 1 = 4480 := by
  rw [cnt_sum, W1f]
  unfold t1
  rw [total]
  exact beq_iff_eq.mp all_parts.2.2.1

lemma cnt2 : cnt 2 = 5272 := by
  rw [cnt_sum, W2f]
  unfold t2
  rw [total]
  exact beq_iff_eq.mp all_parts.2.2.2

lemma cnt3 : cnt 3 = 6952 := by
  have h := cnt_rec 0
  simp only [Nat.zero_add] at h
  rw [cnt0, cnt1, cnt2] at h
  generalize cnt 3 = x at h ⊢
  omega

lemma a_cast (n : ℕ) : (a n : ℚ) = (cnt n : ℚ) := by
  rw [a_eq]

lemma a_rec (k : ℕ) : (a (k + 3) : ℚ) + 14 * (a (k + 1) : ℚ) = 7 * (a (k + 2) : ℚ) + 8 * (a (k + 0) : ℚ) := by
  simp only [a_cast]
  have h : cnt (k + 3) + 14 * cnt (k + 1) = 7 * cnt (k + 2) + 8 * cnt (k + 0) := by simpa only [Nat.add_assoc, Nat.reduceAdd] using cnt_rec (k + 0)
  have h' : ((cnt (k + 3) : ℕ) : ℚ) + 14 * ((cnt (k + 1) : ℕ) : ℚ) = 7 * ((cnt (k + 2) : ℕ) : ℚ) + 8 * ((cnt (k + 0) : ℕ) : ℚ) := by exact_mod_cast h
  linear_combination h'

lemma a0 : (a 0 : ℚ) = 4096 := by
  rw [a_cast, cnt0]
  norm_num

lemma a1 : (a 1 : ℚ) = 4480 := by
  rw [a_cast, cnt1]
  norm_num

lemma a2 : (a 2 : ℚ) = 5272 := by
  rw [a_cast, cnt2]
  norm_num

lemma a3 : (a 3 : ℚ) = 6952 := by
  rw [a_cast, cnt3]
  norm_num

/-- The g.f. as stated. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - X) * (1 - 2 * X) * (1 - 4 * X)) =
      8 * X * (560 - 3261 * X + 4096 * X ^ 2) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - X) * (1 - 2 * X) * (1 - 4 * X)) = A - C (7 : ℚ) * (A * X ^ 1) + C (14 : ℚ) * (A * X ^ 2) - C (8 : ℚ) * (A * X ^ 3) := by
    rw [show (C (7 : ℚ) : ℚ⟦X⟧) = 7 from map_ofNat C 7, show (C (8 : ℚ) : ℚ⟦X⟧) = 8 from map_ofNat C 8, show (C (14 : ℚ) : ℚ⟦X⟧) = 14 from map_ofNat C 14]
    ring
  have e2 : (8 * X * (560 - 3261 * X + 4096 * X ^ 2) : ℚ⟦X⟧) = C (4480 : ℚ) * X ^ 1 - C (26088 : ℚ) * X ^ 2 + C (32768 : ℚ) * X ^ 3 := by
    rw [show (C (4480 : ℚ) : ℚ⟦X⟧) = 4480 from map_ofNat C 4480, show (C (26088 : ℚ) : ℚ⟦X⟧) = 26088 from map_ofNat C 26088, show (C (32768 : ℚ) : ℚ⟦X⟧) = 32768 from map_ofNat C 32768]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_C, hA,
    coeff_mk]
  rcases Nat.lt_or_ge n 4 with hn | hn
  · interval_cases n <;> norm_num only [a1, a2, a3, if_true, if_false]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    have h' := (show (a (k + 4) : ℚ) + 14 * (a (k + 2) : ℚ) = 7 * (a (k + 3) : ℚ) + 8 * (a (k + 1) : ℚ) by simpa only [Nat.add_assoc, Nat.reduceAdd] using a_rec (k + 1))
    simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega, show k + 4 - 3 = k + 1 by omega, show ¬ (k + 4 = 0) by omega, show ¬ (k + 3 = 0) by omega, show ¬ (k + 2 = 0) by omega, show ¬ (k + 1 = 0) by omega, show 1 ≤ k + 4 by omega, show 2 ≤ k + 4 by omega, show 3 ≤ k + 4 by omega, show ¬ (k + 4 = 0) by omega, show ¬ (k + 4 = 1) by omega, show ¬ (k + 4 = 2) by omega, show ¬ (k + 4 = 3) by omega, if_true, if_false]
    linear_combination h'

def closed_Q (n : ℕ) : ℚ := 4 * (930 + 93 * 2 ^ n + 4 ^ n)

lemma closed_Q_rec (m : ℕ) : closed_Q (m + 3) - 7 * closed_Q (m + 2) + 14 * closed_Q (m + 1) - 8 * closed_Q (m + 0) = 0 := by
  unfold closed_Q
  push_cast
  ring

lemma closed_key (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = closed_Q n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 4 with h | h
    · interval_cases n
      · have hk : (a 1 : ℚ) = 4480 := by exact_mod_cast a1
        rw [hk]
        unfold closed_Q
        norm_num
      · have hk : (a 2 : ℚ) = 5272 := by exact_mod_cast a2
        rw [hk]
        unfold closed_Q
        norm_num
      · have hk : (a 3 : ℚ) = 6952 := by exact_mod_cast a3
        rw [hk]
        unfold closed_Q
        norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      have hR := (show (a (m + 4) : ℚ) + 14 * (a (m + 2) : ℚ) = 7 * (a (m + 3) : ℚ) + 8 * (a (m + 1) : ℚ) by simpa only [Nat.add_assoc, Nat.reduceAdd] using a_rec (m + 1))
      have hR' : (a (m + 4) : ℚ) + 14 * (a (m + 2) : ℚ) = 7 * (a (m + 3) : ℚ) + 8 * (a (m + 1) : ℚ) := by exact_mod_cast hR
      have h1 := ih (m + 3) (by omega) (by omega)
      have h2 := ih (m + 2) (by omega) (by omega)
      have h3 := ih (m + 1) (by omega) (by omega)
      have hG := closed_Q_rec (m + 1)
      simp only [show m + 1 + 3 = m + 4 from rfl, show m + 1 + 2 = m + 3 from rfl, show m + 1 + 1 = m + 2 from rfl, show m + 1 + 0 = m + 1 from rfl] at hG
      linear_combination hR' + (-(-7 : ℚ)) * h1 + (-(14 : ℚ)) * h2 + (-(-8 : ℚ)) * h3 + (-1 : ℚ) * hG

theorem closed : ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 4 * (930 + 93 * 2 ^ n + 4 ^ n) := fun n hn => closed_key n hn

/-- Controls: the entry's data. -/
theorem controls : a 1 = 4480 ∧ a 2 = 5272 ∧ a 3 = 6952 ∧ a 4 = 10696 ∧ a 5 = 19720 ∧ a 6 = 43912 ∧ a 7 = 116872 ∧ a 8 = 361096 ∧ a 9 = 1242760 ∧ a 10 = 4578952 ∧ a 11 = 17542792 ∧ a 12 = 68636296 ∧ a 13 = 271486600 ∧ a 14 = 1079840392 ∧ a 15 = 4307160712 ∧ a 16 = 17204252296 ∧ a 17 = 68768239240 ∧ a 18 = 274975428232 ∧ a 19 = 1099706666632 ∧ a 20 = 4398436585096 ∧ a 21 = 17592966188680 ∧ a 22 = 70370304462472 := by
  have v4 : (a 4 : ℚ) = 10696 := by
    have h := a_rec 1
    simp only [Nat.reduceAdd] at h
    rw [a1, a2, a3] at h
    linarith
  have v5 : (a 5 : ℚ) = 19720 := by
    have h := a_rec 2
    simp only [Nat.reduceAdd] at h
    rw [a2, a3, v4] at h
    linarith
  have v6 : (a 6 : ℚ) = 43912 := by
    have h := a_rec 3
    simp only [Nat.reduceAdd] at h
    rw [a3, v4, v5] at h
    linarith
  have v7 : (a 7 : ℚ) = 116872 := by
    have h := a_rec 4
    simp only [Nat.reduceAdd] at h
    rw [v4, v5, v6] at h
    linarith
  have v8 : (a 8 : ℚ) = 361096 := by
    have h := a_rec 5
    simp only [Nat.reduceAdd] at h
    rw [v5, v6, v7] at h
    linarith
  have v9 : (a 9 : ℚ) = 1242760 := by
    have h := a_rec 6
    simp only [Nat.reduceAdd] at h
    rw [v6, v7, v8] at h
    linarith
  have v10 : (a 10 : ℚ) = 4578952 := by
    have h := a_rec 7
    simp only [Nat.reduceAdd] at h
    rw [v7, v8, v9] at h
    linarith
  have v11 : (a 11 : ℚ) = 17542792 := by
    have h := a_rec 8
    simp only [Nat.reduceAdd] at h
    rw [v8, v9, v10] at h
    linarith
  have v12 : (a 12 : ℚ) = 68636296 := by
    have h := a_rec 9
    simp only [Nat.reduceAdd] at h
    rw [v9, v10, v11] at h
    linarith
  have v13 : (a 13 : ℚ) = 271486600 := by
    have h := a_rec 10
    simp only [Nat.reduceAdd] at h
    rw [v10, v11, v12] at h
    linarith
  have v14 : (a 14 : ℚ) = 1079840392 := by
    have h := a_rec 11
    simp only [Nat.reduceAdd] at h
    rw [v11, v12, v13] at h
    linarith
  have v15 : (a 15 : ℚ) = 4307160712 := by
    have h := a_rec 12
    simp only [Nat.reduceAdd] at h
    rw [v12, v13, v14] at h
    linarith
  have v16 : (a 16 : ℚ) = 17204252296 := by
    have h := a_rec 13
    simp only [Nat.reduceAdd] at h
    rw [v13, v14, v15] at h
    linarith
  have v17 : (a 17 : ℚ) = 68768239240 := by
    have h := a_rec 14
    simp only [Nat.reduceAdd] at h
    rw [v14, v15, v16] at h
    linarith
  have v18 : (a 18 : ℚ) = 274975428232 := by
    have h := a_rec 15
    simp only [Nat.reduceAdd] at h
    rw [v15, v16, v17] at h
    linarith
  have v19 : (a 19 : ℚ) = 1099706666632 := by
    have h := a_rec 16
    simp only [Nat.reduceAdd] at h
    rw [v16, v17, v18] at h
    linarith
  have v20 : (a 20 : ℚ) = 4398436585096 := by
    have h := a_rec 17
    simp only [Nat.reduceAdd] at h
    rw [v17, v18, v19] at h
    linarith
  have v21 : (a 21 : ℚ) = 17592966188680 := by
    have h := a_rec 18
    simp only [Nat.reduceAdd] at h
    rw [v18, v19, v20] at h
    linarith
  have v22 : (a 22 : ℚ) = 70370304462472 := by
    have h := a_rec 19
    simp only [Nat.reduceAdd] at h
    rw [v19, v20, v21] at h
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast a1
  · exact_mod_cast a2
  · exact_mod_cast a3
  · exact_mod_cast v4
  · exact_mod_cast v5
  · exact_mod_cast v6
  · exact_mod_cast v7
  · exact_mod_cast v8
  · exact_mod_cast v9
  · exact_mod_cast v10
  · exact_mod_cast v11
  · exact_mod_cast v12
  · exact_mod_cast v13
  · exact_mod_cast v14
  · exact_mod_cast v15
  · exact_mod_cast v16
  · exact_mod_cast v17
  · exact_mod_cast v18
  · exact_mod_cast v19
  · exact_mod_cast v20
  · exact_mod_cast v21
  · exact_mod_cast v22

/-- The conjunction stated as `main`. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 - 2 * X) * (1 - 4 * X)) =
        8 * X * (560 - 3261 * X + 4096 * X ^ 2) ∧
      ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 4 * (930 + 93 * 2 ^ n + 4 ^ n) :=
  ⟨gf, closed⟩

end OMA.S_oeis_a235890

theorem OMA.solution : type_of% @OMA.S_oeis_a235890.main :=
  OMA.S_oeis_a235890.conjecture
