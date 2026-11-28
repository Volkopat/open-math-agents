import OMAStatements.S_oeis_a235881

namespace OMA.S_oeis_a235881

open PowerSeries Finset



/-! ## The window condition, rows and the transfer -/

/-- A row. -/
abbrev Row := Fin 6 → Fin 3

/-- The window condition on the 2 X 2 block with top row (p, q) and bottom row (r, s). -/
def P (p q r s : Fin 3) : Prop :=
  medEq (p).val (q).val (r).val (s).val = true

instance (p q r s : Fin 3) : Decidable (P p q r s) := by unfold P; infer_instance

/-- Row s may follow row r: every block between them satisfies P. -/
def rowOK (r s : Fin 6 → Fin 3) : Prop :=
  ∀ j j' : Fin 6, j'.val = j.val + 1 → P (r j) (r j') (s j) (s j')

instance : DecidableRel rowOK := fun r s => by unfold rowOK; infer_instance

/-- Consecutive rows allowed. -/
def Valid {m : ℕ} (x : Fin m → Fin 6 → Fin 3) : Prop :=
  ∀ i i' : Fin m, i'.val = i.val + 1 → rowOK (x i) (x i')

instance {m : ℕ} : DecidablePred (@Valid m) := fun x => by unfold Valid; infer_instance

/-- The number of valid arrays with n + 1 rows. -/
def cnt (n : ℕ) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 6 → Fin 3)).filter Valid).card

lemma a_eq (n : ℕ) : a n = cnt n := by
  unfold a cnt
  exact congrArg Finset.card (Finset.filter_congr (fun x _ => Iff.rfl))

/-- W(n, r): valid arrays with n + 1 rows whose first row is r. -/
def W (n : ℕ) (r : Fin 6 → Fin 3) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 6 → Fin 3)).filter (fun x => Valid x ∧ x 0 = r)).card

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

lemma sum_cons {m : ℕ} (f : (Fin (m + 1) → Fin 3) → ℕ) :
    ∑ s : Fin (m + 1) → Fin 3, f s = ∑ x : Fin 3, ∑ t : Fin m → Fin 3, f (Fin.cons x t) := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 3).symm _ _
    (fun s => by simp [Fin.consEquiv, Fin.cons_self_tail])

lemma sum_row (f : Row → ℕ) :
    ∑ s : Row, f s = ∑ x0 : Fin 3, ∑ x1 : Fin 3, ∑ x2 : Fin 3, ∑ x3 : Fin 3, ∑ x4 : Fin 3, ∑ x5 : Fin 3, f ![x0, x1, x2, x3, x4, x5] := by
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
def PN (p q r s : ℕ) : Bool := Nat.testBit 1290683019976669863613713 (((p * 3 + q) * 3 + r) * 3 + s)

lemma P_iff (p q r s : Fin 3) : P p q r s ↔ PN p.val q.val r.val s.val = true := by
  revert p q r s
  decide +kernel

/-- The sum of f over 0, ..., 2. -/
def sumK (f : ℕ → ℕ) : ℕ := f 0 + f 1 + f 2

lemma sumK_fin (f : ℕ → ℕ) : ∑ x : Fin 3, f x.val = sumK f := by
  rw [Fin.sum_univ_eq_sum_range (fun x => f x) 3]
  simp [Finset.sum_range_succ, sumK]

/-- The code of a row: its entries as base-K digits, r 0 the most significant. -/
def code (r : Row) : ℕ := (((((r 0).val * 3 + (r 1).val) * 3 + (r 2).val) * 3 + (r 3).val) * 3 + (r 4).val) * 3 + (r 5).val

lemma code_lt (r : Row) : code r < 729 := by
  unfold code; have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; have h3 := (r 3).isLt; have h4 := (r 4).isLt; have h5 := (r 5).isLt; omega

lemma dig0 (r : Row) : code r / 243 % 3 = (r 0).val := by
  unfold code; have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; have h3 := (r 3).isLt; have h4 := (r 4).isLt; have h5 := (r 5).isLt; omega

lemma dig1 (r : Row) : code r / 81 % 3 = (r 1).val := by
  unfold code; have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; have h3 := (r 3).isLt; have h4 := (r 4).isLt; have h5 := (r 5).isLt; omega

lemma dig2 (r : Row) : code r / 27 % 3 = (r 2).val := by
  unfold code; have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; have h3 := (r 3).isLt; have h4 := (r 4).isLt; have h5 := (r 5).isLt; omega

lemma dig3 (r : Row) : code r / 9 % 3 = (r 3).val := by
  unfold code; have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; have h3 := (r 3).isLt; have h4 := (r 4).isLt; have h5 := (r 5).isLt; omega

lemma dig4 (r : Row) : code r / 3 % 3 = (r 4).val := by
  unfold code; have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; have h3 := (r 3).isLt; have h4 := (r 4).isLt; have h5 := (r 5).isLt; omega

lemma dig5 (r : Row) : code r % 3 = (r 5).val := by
  unfold code; have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; have h3 := (r 3).isLt; have h4 := (r 4).isLt; have h5 := (r 5).isLt; omega

/-- Level 5 of the transfer: the entry x below r5, next to the previous entry p. -/
def N5 (g : ℕ → ℕ) (r4 r5 : ℕ) (p acc : ℕ) : ℕ :=
  sumK (fun x => if PN r4 r5 p x then g (acc * 3 + x) else 0)

/-- Level 4 of the transfer: the entry x below r4, next to the previous entry p. -/
def N4 (g : ℕ → ℕ) (r3 r4 r5 : ℕ) (p acc : ℕ) : ℕ :=
  sumK (fun x => if PN r3 r4 p x then N5 g r4 r5 x (acc * 3 + x) else 0)

/-- Level 3 of the transfer: the entry x below r3, next to the previous entry p. -/
def N3 (g : ℕ → ℕ) (r2 r3 r4 r5 : ℕ) (p acc : ℕ) : ℕ :=
  sumK (fun x => if PN r2 r3 p x then N4 g r3 r4 r5 x (acc * 3 + x) else 0)

/-- Level 2 of the transfer: the entry x below r2, next to the previous entry p. -/
def N2 (g : ℕ → ℕ) (r1 r2 r3 r4 r5 : ℕ) (p acc : ℕ) : ℕ :=
  sumK (fun x => if PN r1 r2 p x then N3 g r2 r3 r4 r5 x (acc * 3 + x) else 0)

/-- Level 1 of the transfer: the entry x below r1, next to the previous entry p. -/
def N1 (g : ℕ → ℕ) (r0 r1 r2 r3 r4 r5 : ℕ) (p acc : ℕ) : ℕ :=
  sumK (fun x => if PN r0 r1 p x then N2 g r1 r2 r3 r4 r5 x (acc * 3 + x) else 0)

/-- One step of the transfer: the sum of g over the codes of the rows allowed below the row with entries r0, r1, .... -/
def Tn (g : ℕ → ℕ) (r0 r1 r2 r3 r4 r5 : ℕ) : ℕ :=
  sumK (fun x => N1 g r0 r1 r2 r3 r4 r5 x x)

/-- The sum of g over all row codes. -/
def Ts (g : ℕ → ℕ) : ℕ := sumK (fun x0 => sumK (fun x1 => sumK (fun x2 => sumK (fun x3 => sumK (fun x4 => sumK (fun x5 => g (((((x0 * 3 + x1) * 3 + x2) * 3 + x3) * 3 + x4) * 3 + x5)))))))

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

/-- W(1, r) for every row r, packed: the entry of r is the base 2^2 digit number code r. -/
def L1 : ℕ := 0x3aa66a69566566a69569a55555566566555566566a69569a55555569a55a69555555555555555555566566555566566555555555555566566555566566a69569a55555569a55a69555555555555555555569a55a69555555a69569b9a55a69555555a69569a55555555555555555555a69569a55555569a55a6a656655556656655555555555556656655556656655555555555555555555a69569a55555569a55a6a656655556656655555569a55a6a656655a6a66ab

def tab1 (c : ℕ) : ℕ := L1 / 2 ^ (2 * c) % 2 ^ 2

/-- W(2, r) for every row r, packed: the entry of r is the base 2^4 digit number code r. -/
def L2 : ℕ := 0x944441414441441111414111414441441111441441111111111111414111414111111111414111414441441111441441111111111111441441111441441111111111111111111111111111111111111111414111414111111111414111414111111111111111111111111111414111414111111111414111414441441111441441111111111111441441111441441111111111111111111111111111111111111111441441111441441111111111111441441111441494144111144144111111111111144144111144144111111111111111111111111111111111111111144144111144144111111111111144144111144144414111414111111111414111414111111111111111111111111111414111414111111111414111414111111111111111111111111111111111111111144144111144144111111111111144144111144144414111414111111111414111414111111111111144144111144144414111414111144144414144449

def tab2 (c : ℕ) : ℕ := L2 / 2 ^ (4 * c) % 2 ^ 4

/-- W(3, r) for every row r, packed: the entry of r is the base 2^5 digit number code r. -/
def L3 : ℕ := 0x1b421080a02842028404210a028084280a1080a10108428405080842108421084210a028084280a02108421084280a0210a02842028404210a10142021084210842108428405080842142028404210842108421084210842108421084210842108421084210a028084280a02108421084280a0210a028084210842108421084210842108421084280a0210a02808421084210a028084280a1080a10108428405080842108421084210a10142021085080a10108421084210842108421084210842108421084210842108428405080842142028404210842108421085080a101084284051b405080842142028404210842108421085080a10108428405080842108421084210842108421084210842108421084210842142028404210a1014202108421084210842840508084214202842028084280a02108421084280a0210a028084210842108421084210842108421084280a0210a02808421084210a028084280a021084210842108421084210842108421084210842108421085080a10108428405080842108421084210a10142021085080a1080a0210a02808421084210a028084280a02108421084210842840508084214202842028084280a021085080a1080a0284211b

def tab3 (c : ℕ) : ℕ := L3 / 2 ^ (5 * c) % 2 ^ 5

def t0 (r : Row) : ℕ := tab0 (code r)

def t1 (r : Row) : ℕ := tab1 (code r)

def t2 (r : Row) : ℕ := tab2 (code r)

def t3 (r : Row) : ℕ := tab3 (code r)

lemma W0f : W 0 = t0 := by
  funext r
  exact W_zero r

def stepB1 (c : ℕ) : Bool := Tn tab0 (c / 243 % 3) (c / 81 % 3) (c / 27 % 3) (c / 9 % 3) (c / 3 % 3) (c % 3) == tab1 c

lemma chk1 : (List.range 729).all stepB1 = true := by
  decide +kernel

lemma W1f : W 1 = t1 := by
  funext r
  rw [W_succ]
  simp only [W0f, t0]
  rw [bridge]
  have h := List.all_eq_true.mp chk1 (code r) (List.mem_range.mpr (code_lt r))
  unfold stepB1 at h
  rw [dig0 r, dig1 r, dig2 r, dig3 r, dig4 r, dig5 r] at h
  exact beq_iff_eq.mp h

def stepB2 (c : ℕ) : Bool := Tn tab1 (c / 243 % 3) (c / 81 % 3) (c / 27 % 3) (c / 9 % 3) (c / 3 % 3) (c % 3) == tab2 c

lemma chk2 : (List.range 729).all stepB2 = true := by
  decide +kernel

lemma W2f : W 2 = t2 := by
  funext r
  rw [W_succ]
  simp only [W1f, t1]
  rw [bridge]
  have h := List.all_eq_true.mp chk2 (code r) (List.mem_range.mpr (code_lt r))
  unfold stepB2 at h
  rw [dig0 r, dig1 r, dig2 r, dig3 r, dig4 r, dig5 r] at h
  exact beq_iff_eq.mp h

def stepB3 (c : ℕ) : Bool := Tn tab2 (c / 243 % 3) (c / 81 % 3) (c / 27 % 3) (c / 9 % 3) (c / 3 % 3) (c % 3) == tab3 c

lemma chk3 : (List.range 729).all stepB3 = true := by
  decide +kernel

lemma W3f : W 3 = t3 := by
  funext r
  rw [W_succ]
  simp only [W2f, t2]
  rw [bridge]
  have h := List.all_eq_true.mp chk3 (code r) (List.mem_range.mpr (code_lt r))
  unfold stepB3 at h
  rw [dig0 r, dig1 r, dig2 r, dig3 r, dig4 r, dig5 r] at h
  exact beq_iff_eq.mp h

/-- The relation on the tables, at the row with code c. -/
def relB (c : ℕ) : Bool := tab3 c + 11 * tab1 c == 6 * tab2 c + 6 * tab0 c

lemma chk_rel : (List.range 729).all relB = true := by
  decide +kernel

lemma rel_at (r : Row) : tab3 (code r) + 11 * tab1 (code r) = 6 * tab2 (code r) + 6 * tab0 (code r) :=
  beq_iff_eq.mp (List.all_eq_true.mp chk_rel (code r) (List.mem_range.mpr (code_lt r)))

/-- The per-row relation: the g.f. denominator annihilates W(k + 0), ..., W(k + 3). -/
lemma W_rec (k : ℕ) : ∀ r : Row, W (k + 3) r + 11 * W (k + 1) r = 6 * W (k + 2) r + 6 * W (k + 0) r := by
  induction k with
  | zero =>
    intro r
    simp only [Nat.zero_add, W0f, W1f, W2f, W3f, t0, t1, t2, t3]
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

lemma cnt_rec (k : ℕ) : cnt (k + 3)  + 11 * cnt (k + 1)  = 6 * cnt (k + 2)  + 6 * cnt (k + 0)  := by
  simp only [cnt_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun r _ => W_rec k r)

lemma cnt0 : cnt 0 = 729 := by
  rw [cnt_sum, W0f]
  unfold t0
  rw [total]
  decide +kernel

lemma cnt1 : cnt 1 = 921 := by
  rw [cnt_sum, W1f]
  unfold t1
  rw [total]
  decide +kernel

lemma cnt2 : cnt 2 = 1311 := by
  rw [cnt_sum, W2f]
  unfold t2
  rw [total]
  decide +kernel

lemma cnt3 : cnt 3 = 2109 := by
  rw [cnt_sum, W3f]
  unfold t3
  rw [total]
  decide +kernel

lemma a_cast (n : ℕ) : (a n : ℚ) = (cnt n : ℚ) := by
  rw [a_eq]

lemma a_rec (k : ℕ) : (a (k + 3) : ℚ) + 11 * (a (k + 1) : ℚ) = 6 * (a (k + 2) : ℚ) + 6 * (a (k + 0) : ℚ) := by
  simp only [a_cast]
  have h : cnt (k + 3) + 11 * cnt (k + 1) = 6 * cnt (k + 2) + 6 * cnt (k + 0) := by simpa only [Nat.add_assoc, Nat.reduceAdd] using cnt_rec (k + 0)
  have h' : ((cnt (k + 3) : ℕ) : ℚ) + 11 * ((cnt (k + 1) : ℕ) : ℚ) = 6 * ((cnt (k + 2) : ℕ) : ℚ) + 6 * ((cnt (k + 0) : ℕ) : ℚ) := by exact_mod_cast h
  linear_combination h'

lemma a0 : (a 0 : ℚ) = 729 := by
  rw [a_cast, cnt0]
  norm_num

lemma a1 : (a 1 : ℚ) = 921 := by
  rw [a_cast, cnt1]
  norm_num

lemma a2 : (a 2 : ℚ) = 1311 := by
  rw [a_cast, cnt2]
  norm_num

lemma a3 : (a 3 : ℚ) = 2109 := by
  rw [a_cast, cnt3]
  norm_num

/-- The g.f. as stated. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - X) * (1 - 2 * X) * (1 - 3 * X)) =
      3 * X * (307 - 1405 * X + 1458 * X ^ 2) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - X) * (1 - 2 * X) * (1 - 3 * X)) = A - C (6 : ℚ) * (A * X ^ 1) + C (11 : ℚ) * (A * X ^ 2) - C (6 : ℚ) * (A * X ^ 3) := by
    rw [show (C (6 : ℚ) : ℚ⟦X⟧) = 6 from map_ofNat C 6, show (C (11 : ℚ) : ℚ⟦X⟧) = 11 from map_ofNat C 11]
    ring
  have e2 : (3 * X * (307 - 1405 * X + 1458 * X ^ 2) : ℚ⟦X⟧) = C (921 : ℚ) * X ^ 1 - C (4215 : ℚ) * X ^ 2 + C (4374 : ℚ) * X ^ 3 := by
    rw [show (C (921 : ℚ) : ℚ⟦X⟧) = 921 from map_ofNat C 921, show (C (4215 : ℚ) : ℚ⟦X⟧) = 4215 from map_ofNat C 4215, show (C (4374 : ℚ) : ℚ⟦X⟧) = 4374 from map_ofNat C 4374]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_C, hA,
    coeff_mk]
  rcases Nat.lt_or_ge n 4 with hn | hn
  · interval_cases n <;> norm_num only [a1, a2, a3, if_true, if_false]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    have h' := (show (a (k + 4) : ℚ) + 11 * (a (k + 2) : ℚ) = 6 * (a (k + 3) : ℚ) + 6 * (a (k + 1) : ℚ) by simpa only [Nat.add_assoc, Nat.reduceAdd] using a_rec (k + 1))
    simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega, show k + 4 - 3 = k + 1 by omega, show ¬ (k + 4 = 0) by omega, show ¬ (k + 3 = 0) by omega, show ¬ (k + 2 = 0) by omega, show ¬ (k + 1 = 0) by omega, show 1 ≤ k + 4 by omega, show 2 ≤ k + 4 by omega, show 3 ≤ k + 4 by omega, show ¬ (k + 4 = 0) by omega, show ¬ (k + 4 = 1) by omega, show ¬ (k + 4 = 2) by omega, show ¬ (k + 4 = 3) by omega, if_true, if_false]
    linear_combination h'

def closed_Q (n : ℕ) : ℚ := 3 * (180 + 31 * 2 ^ (1 + n) + 3 ^ n)

lemma closed_Q_rec (m : ℕ) : closed_Q (m + 3) - 6 * closed_Q (m + 2) + 11 * closed_Q (m + 1) - 6 * closed_Q (m + 0) = 0 := by
  unfold closed_Q
  push_cast
  ring

lemma closed_key (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = closed_Q n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 4 with h | h
    · interval_cases n
      · have hk : (a 1 : ℚ) = 921 := by exact_mod_cast a1
        rw [hk]
        unfold closed_Q
        norm_num
      · have hk : (a 2 : ℚ) = 1311 := by exact_mod_cast a2
        rw [hk]
        unfold closed_Q
        norm_num
      · have hk : (a 3 : ℚ) = 2109 := by exact_mod_cast a3
        rw [hk]
        unfold closed_Q
        norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      have hR := (show (a (m + 4) : ℚ) + 11 * (a (m + 2) : ℚ) = 6 * (a (m + 3) : ℚ) + 6 * (a (m + 1) : ℚ) by simpa only [Nat.add_assoc, Nat.reduceAdd] using a_rec (m + 1))
      have hR' : (a (m + 4) : ℚ) + 11 * (a (m + 2) : ℚ) = 6 * (a (m + 3) : ℚ) + 6 * (a (m + 1) : ℚ) := by exact_mod_cast hR
      have h1 := ih (m + 3) (by omega) (by omega)
      have h2 := ih (m + 2) (by omega) (by omega)
      have h3 := ih (m + 1) (by omega) (by omega)
      have hG := closed_Q_rec (m + 1)
      simp only [show m + 1 + 3 = m + 4 from rfl, show m + 1 + 2 = m + 3 from rfl, show m + 1 + 1 = m + 2 from rfl, show m + 1 + 0 = m + 1 from rfl] at hG
      linear_combination hR' + (-(-6 : ℚ)) * h1 + (-(11 : ℚ)) * h2 + (-(-6 : ℚ)) * h3 + (-1 : ℚ) * hG

theorem closed : ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 3 * (180 + 31 * 2 ^ (1 + n) + 3 ^ n) := fun n hn => closed_key n hn

/-- Controls: the entry's data. -/
theorem controls : a 1 = 921 ∧ a 2 = 1311 ∧ a 3 = 2109 ∧ a 4 = 3759 ∧ a 5 = 7221 ∧ a 6 = 14631 ∧ a 7 = 30909 ∧ a 8 = 67839 ∧ a 9 = 154821 ∧ a 10 = 368151 ∧ a 11 = 912909 ∧ a 12 = 2356719 ∧ a 13 = 6307221 ∧ a 14 = 17396871 ∧ a 15 = 49142109 ∧ a 16 = 141330399 ∧ a 17 = 411800421 ∧ a 18 = 1211020791 ∧ a 19 = 3584302509 ∧ a 20 = 10655388879 ∧ a 21 = 31771130421 ∧ a 22 = 94923319911 ∧ a 23 = 283989818109 ∧ a 24 = 850409172159 := by
  have v4 : (a 4 : ℚ) = 3759 := by
    have h := a_rec 1
    simp only [Nat.reduceAdd] at h
    rw [a1, a2, a3] at h
    linarith
  have v5 : (a 5 : ℚ) = 7221 := by
    have h := a_rec 2
    simp only [Nat.reduceAdd] at h
    rw [a2, a3, v4] at h
    linarith
  have v6 : (a 6 : ℚ) = 14631 := by
    have h := a_rec 3
    simp only [Nat.reduceAdd] at h
    rw [a3, v4, v5] at h
    linarith
  have v7 : (a 7 : ℚ) = 30909 := by
    have h := a_rec 4
    simp only [Nat.reduceAdd] at h
    rw [v4, v5, v6] at h
    linarith
  have v8 : (a 8 : ℚ) = 67839 := by
    have h := a_rec 5
    simp only [Nat.reduceAdd] at h
    rw [v5, v6, v7] at h
    linarith
  have v9 : (a 9 : ℚ) = 154821 := by
    have h := a_rec 6
    simp only [Nat.reduceAdd] at h
    rw [v6, v7, v8] at h
    linarith
  have v10 : (a 10 : ℚ) = 368151 := by
    have h := a_rec 7
    simp only [Nat.reduceAdd] at h
    rw [v7, v8, v9] at h
    linarith
  have v11 : (a 11 : ℚ) = 912909 := by
    have h := a_rec 8
    simp only [Nat.reduceAdd] at h
    rw [v8, v9, v10] at h
    linarith
  have v12 : (a 12 : ℚ) = 2356719 := by
    have h := a_rec 9
    simp only [Nat.reduceAdd] at h
    rw [v9, v10, v11] at h
    linarith
  have v13 : (a 13 : ℚ) = 6307221 := by
    have h := a_rec 10
    simp only [Nat.reduceAdd] at h
    rw [v10, v11, v12] at h
    linarith
  have v14 : (a 14 : ℚ) = 17396871 := by
    have h := a_rec 11
    simp only [Nat.reduceAdd] at h
    rw [v11, v12, v13] at h
    linarith
  have v15 : (a 15 : ℚ) = 49142109 := by
    have h := a_rec 12
    simp only [Nat.reduceAdd] at h
    rw [v12, v13, v14] at h
    linarith
  have v16 : (a 16 : ℚ) = 141330399 := by
    have h := a_rec 13
    simp only [Nat.reduceAdd] at h
    rw [v13, v14, v15] at h
    linarith
  have v17 : (a 17 : ℚ) = 411800421 := by
    have h := a_rec 14
    simp only [Nat.reduceAdd] at h
    rw [v14, v15, v16] at h
    linarith
  have v18 : (a 18 : ℚ) = 1211020791 := by
    have h := a_rec 15
    simp only [Nat.reduceAdd] at h
    rw [v15, v16, v17] at h
    linarith
  have v19 : (a 19 : ℚ) = 3584302509 := by
    have h := a_rec 16
    simp only [Nat.reduceAdd] at h
    rw [v16, v17, v18] at h
    linarith
  have v20 : (a 20 : ℚ) = 10655388879 := by
    have h := a_rec 17
    simp only [Nat.reduceAdd] at h
    rw [v17, v18, v19] at h
    linarith
  have v21 : (a 21 : ℚ) = 31771130421 := by
    have h := a_rec 18
    simp only [Nat.reduceAdd] at h
    rw [v18, v19, v20] at h
    linarith
  have v22 : (a 22 : ℚ) = 94923319911 := by
    have h := a_rec 19
    simp only [Nat.reduceAdd] at h
    rw [v19, v20, v21] at h
    linarith
  have v23 : (a 23 : ℚ) = 283989818109 := by
    have h := a_rec 20
    simp only [Nat.reduceAdd] at h
    rw [v20, v21, v22] at h
    linarith
  have v24 : (a 24 : ℚ) = 850409172159 := by
    have h := a_rec 21
    simp only [Nat.reduceAdd] at h
    rw [v21, v22, v23] at h
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · exact_mod_cast v23
  · exact_mod_cast v24

/-- The conjunction stated as `main`. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 - 2 * X) * (1 - 3 * X)) =
        3 * X * (307 - 1405 * X + 1458 * X ^ 2) ∧
      ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 3 * (180 + 31 * 2 ^ (1 + n) + 3 ^ n) :=
  ⟨gf, closed⟩

end OMA.S_oeis_a235881

theorem OMA.solution : type_of% @OMA.S_oeis_a235881.main :=
  OMA.S_oeis_a235881.conjecture
