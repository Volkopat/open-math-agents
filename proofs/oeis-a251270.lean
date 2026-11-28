import OMAStatements.S_oeis_a251270

namespace OMA.S_oeis_a251270

open PowerSeries Finset


/-! ## The window condition, rows and the transfer -/

/-- A row. -/
abbrev Row := Fin 4 → Fin 2

/-- The window condition on the 2 X 2 block with top row (p, q) and bottom row (r, s). -/
def P (p q r s : Fin 2) : Prop :=
  ¬ (((s).val : ℤ) - (p).val < ((q).val : ℤ) - (r).val)

instance (p q r s : Fin 2) : Decidable (P p q r s) := by unfold P; infer_instance

/-- Row s may follow row r: every block between them satisfies P. -/
def rowOK (r s : Fin 4 → Fin 2) : Prop :=
  ∀ j j' : Fin 4, j'.val = j.val + 1 → P (r j) (r j') (s j) (s j')

instance : DecidableRel rowOK := fun r s => by unfold rowOK; infer_instance

/-- Consecutive rows allowed. -/
def Valid {m : ℕ} (x : Fin m → Fin 4 → Fin 2) : Prop :=
  ∀ i i' : Fin m, i'.val = i.val + 1 → rowOK (x i) (x i')

instance {m : ℕ} : DecidablePred (@Valid m) := fun x => by unfold Valid; infer_instance

/-- The number of valid arrays with n + 1 rows. -/
def cnt (n : ℕ) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 4 → Fin 2)).filter Valid).card

/-- Transposing: the columns of an array are the rows of its transpose. -/
lemma a_eq (n : ℕ) : a n = cnt n := by
  unfold a cnt
  skip
  apply Finset.card_bij' (fun x _ => fun j i => x i j) (fun y _ => fun i j => y j i)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    intro c c' hc b b' hb
    exact hx b b' hb c c' hc
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    intro b b' hb c c' hc
    exact hy c c' hc b b' hb
  · intro x _
    rfl
  · intro y _
    rfl

/-- W(n, r): valid arrays with n + 1 rows whose first row is r. -/
def W (n : ℕ) (r : Fin 4 → Fin 2) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 4 → Fin 2)).filter (fun x => Valid x ∧ x 0 = r)).card

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

lemma sum_cons {m : ℕ} (f : (Fin (m + 1) → Fin 2) → ℕ) :
    ∑ s : Fin (m + 1) → Fin 2, f s = ∑ x : Fin 2, ∑ t : Fin m → Fin 2, f (Fin.cons x t) := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 2).symm _ _
    (fun s => by simp [Fin.consEquiv, Fin.cons_self_tail])

lemma sum_row (f : Row → ℕ) :
    ∑ s : Row, f s = ∑ x0 : Fin 2, ∑ x1 : Fin 2, ∑ x2 : Fin 2, ∑ x3 : Fin 2, f ![x0, x1, x2, x3] := by
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x0 _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x1 _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x2 _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x3 _ => ?_)
  rw [Fintype.sum_unique]
  exact congrArg f (by funext j; fin_cases j <;> rfl)

lemma row_eta (r : Row) : r = ![r 0, r 1, r 2, r 3] := by
  funext j
  fin_cases j <;> rfl

lemma rowOK_iff (r s : Row) : rowOK r s ↔ P (r 0) (r 1) (s 0) (s 1) ∧ P (r 1) (r 2) (s 1) (s 2) ∧ P (r 2) (r 3) (s 2) (s 3) := by
  constructor
  · intro h
    exact ⟨h 0 1 rfl, h 1 2 rfl, h 2 3 rfl⟩
  · rintro ⟨h0, h1, h2⟩ j j' hj
    rcases j with ⟨j, hj0⟩
    rcases j' with ⟨j', hj1⟩
    simp only at hj
    subst hj
    have hjw : j < 3 := by omega
    interval_cases j
    · exact h0
    · exact h1
    · exact h2

/-- One step of the transfer, the rows below r enumerated entry by entry. -/
def T (g : Row → ℕ) (r : Row) : ℕ :=
  ∑ x0 : Fin 2, ∑ x1 : Fin 2, if P (r 0) (r 1) x0 x1 then ∑ x2 : Fin 2, if P (r 1) (r 2) x1 x2 then ∑ x3 : Fin 2, if P (r 2) (r 3) x2 x3 then g ![x0, x1, x2, x3] else 0 else 0 else 0

lemma T_eq (g : Row → ℕ) (r : Row) :
    T g r = ∑ s, if rowOK r s then g s else 0 := by
  rw [sum_row]
  unfold T
  simp only [rowOK_iff, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ, Matrix.head_cons,
    Matrix.tail_cons, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero]

lemma W_succT (n : ℕ) (r : Row) : W (n + 1) r = T (W n) r := by
  rw [W_succ, T_eq]

/-- The index of a row in the tables. -/
def idx (r : Row) : ℕ := 8 * (r 0).val + 4 * (r 1).val + 2 * (r 2).val + (r 3).val

/-- W(1, r), by the index of r. -/
def L1 : List ℕ := [16, 12, 10, 4, 10, 8, 4, 2, 12, 9, 8, 3, 4, 3, 2, 1]

def t1 (r : Row) : ℕ := L1.getD (idx r) 0

/-- W(2, r), by the index of r. -/
def L2 : List ℕ := [108, 66, 45, 10, 45, 31, 9, 3, 66, 40, 31, 6, 10, 6, 3, 1]

def t2 (r : Row) : ℕ := L2.getD (idx r) 0

/-- W(3, r), by the index of r. -/
def L3 : List ℕ := [480, 251, 145, 20, 145, 90, 16, 4, 251, 130, 90, 10, 20, 10, 4, 1]

def t3 (r : Row) : ℕ := L3.getD (idx r) 0

/-- W(4, r), by the index of r. -/
def L4 : List ℕ := [1667, 771, 390, 35, 390, 225, 25, 5, 771, 355, 225, 15, 35, 15, 5, 1]

def t4 (r : Row) : ℕ := L4.getD (idx r) 0

/-- W(5, r), by the index of r. -/
def L5 : List ℕ := [4930, 2067, 941, 56, 941, 516, 36, 6, 2067, 871, 516, 21, 56, 21, 6, 1]

def t5 (r : Row) : ℕ := L5.getD (idx r) 0

/-- W(6, r), by the index of r. -/
def L6 : List ℕ := [13052, 5058, 2120, 84, 2120, 1123, 49, 7, 5058, 1994, 1123, 28, 84, 28, 7, 1]

def t6 (r : Row) : ℕ := L6.getD (idx r) 0

/-- W(7, r), by the index of r. -/
def L7 : List ℕ := [31936, 11622, 4570, 120, 4570, 2366, 64, 8, 11622, 4360, 2366, 36, 120, 36, 8, 1]

def t7 (r : Row) : ℕ := L7.getD (idx r) 0

/-- W(8, r), by the index of r. -/
def L8 : List ℕ := [73805, 25557, 9575, 165, 9575, 4885, 81, 9, 25557, 9245, 4885, 45, 165, 45, 9, 1]

def t8 (r : Row) : ℕ := L8.getD (idx r) 0

def t0 (_ : Row) : ℕ := 1

lemma W0f : W 0 = t0 := by
  funext r
  rw [W_zero]
  rfl

lemma check1 : ∀ x0 x1 x2 x3 : Fin 2, T t0 ![x0, x1, x2, x3] = t1 ![x0, x1, x2, x3] := by
  decide +kernel

lemma W1f : W 1 = t1 := by
  funext r
  rw [W_succT, W0f, row_eta r]
  exact check1 (r 0) (r 1) (r 2) (r 3)

lemma check2 : ∀ x0 x1 x2 x3 : Fin 2, T t1 ![x0, x1, x2, x3] = t2 ![x0, x1, x2, x3] := by
  decide +kernel

lemma W2f : W 2 = t2 := by
  funext r
  rw [W_succT, W1f, row_eta r]
  exact check2 (r 0) (r 1) (r 2) (r 3)

lemma check3 : ∀ x0 x1 x2 x3 : Fin 2, T t2 ![x0, x1, x2, x3] = t3 ![x0, x1, x2, x3] := by
  decide +kernel

lemma W3f : W 3 = t3 := by
  funext r
  rw [W_succT, W2f, row_eta r]
  exact check3 (r 0) (r 1) (r 2) (r 3)

lemma check4 : ∀ x0 x1 x2 x3 : Fin 2, T t3 ![x0, x1, x2, x3] = t4 ![x0, x1, x2, x3] := by
  decide +kernel

lemma W4f : W 4 = t4 := by
  funext r
  rw [W_succT, W3f, row_eta r]
  exact check4 (r 0) (r 1) (r 2) (r 3)

lemma check5 : ∀ x0 x1 x2 x3 : Fin 2, T t4 ![x0, x1, x2, x3] = t5 ![x0, x1, x2, x3] := by
  decide +kernel

lemma W5f : W 5 = t5 := by
  funext r
  rw [W_succT, W4f, row_eta r]
  exact check5 (r 0) (r 1) (r 2) (r 3)

lemma check6 : ∀ x0 x1 x2 x3 : Fin 2, T t5 ![x0, x1, x2, x3] = t6 ![x0, x1, x2, x3] := by
  decide +kernel

lemma W6f : W 6 = t6 := by
  funext r
  rw [W_succT, W5f, row_eta r]
  exact check6 (r 0) (r 1) (r 2) (r 3)

lemma check7 : ∀ x0 x1 x2 x3 : Fin 2, T t6 ![x0, x1, x2, x3] = t7 ![x0, x1, x2, x3] := by
  decide +kernel

lemma W7f : W 7 = t7 := by
  funext r
  rw [W_succT, W6f, row_eta r]
  exact check7 (r 0) (r 1) (r 2) (r 3)

lemma check8 : ∀ x0 x1 x2 x3 : Fin 2, T t7 ![x0, x1, x2, x3] = t8 ![x0, x1, x2, x3] := by
  decide +kernel

lemma W8f : W 8 = t8 := by
  funext r
  rw [W_succT, W7f, row_eta r]
  exact check8 (r 0) (r 1) (r 2) (r 3)

lemma check_rel : ∀ x0 x1 x2 x3 : Fin 2, t8 ![x0, x1, x2, x3] + 35 * t6 ![x0, x1, x2, x3] + 105 * t4 ![x0, x1, x2, x3] + 49 * t2 ![x0, x1, x2, x3] + 2 * t0 ![x0, x1, x2, x3] = 9 * t7 ![x0, x1, x2, x3] + 77 * t5 ![x0, x1, x2, x3] + 91 * t3 ![x0, x1, x2, x3] + 15 * t1 ![x0, x1, x2, x3] := by
  decide +kernel

/-- The per-row relation: the g.f. denominator annihilates W(k + 0), ..., W(k + 8). -/
lemma W_rec (k : ℕ) : ∀ r : Row, W (k + 8) r + 35 * W (k + 6) r + 105 * W (k + 4) r + 49 * W (k + 2) r + 2 * W (k + 0) r = 9 * W (k + 7) r + 77 * W (k + 5) r + 91 * W (k + 3) r + 15 * W (k + 1) r := by
  induction k with
  | zero =>
    intro r
    simp only [Nat.zero_add, W0f, W1f, W2f, W3f, W4f, W5f, W6f, W7f, W8f]
    rw [row_eta r]
    exact check_rel (r 0) (r 1) (r 2) (r 3)
  | succ k ih =>
    intro r
    rw [show k + 1 + 0 = (k + 0) + 1 from rfl, show k + 1 + 1 = (k + 1) + 1 from rfl, show k + 1 + 2 = (k + 2) + 1 from rfl, show k + 1 + 3 = (k + 3) + 1 from rfl, show k + 1 + 4 = (k + 4) + 1 from rfl, show k + 1 + 5 = (k + 5) + 1 from rfl, show k + 1 + 6 = (k + 6) + 1 from rfl, show k + 1 + 7 = (k + 7) + 1 from rfl, show k + 1 + 8 = (k + 8) + 1 from rfl]
    rw [W_succ (k + 0), W_succ (k + 1), W_succ (k + 2), W_succ (k + 3), W_succ (k + 4), W_succ (k + 5), W_succ (k + 6), W_succ (k + 7), W_succ (k + 8)]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    split_ifs
    · exact ih s
    · simp

lemma cnt_rec (k : ℕ) : cnt (k + 8)  + 35 * cnt (k + 6)  + 105 * cnt (k + 4)  + 49 * cnt (k + 2)  + 2 * cnt (k + 0)  = 9 * cnt (k + 7)  + 77 * cnt (k + 5)  + 91 * cnt (k + 3)  + 15 * cnt (k + 1)  := by
  simp only [cnt_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun r _ => W_rec k r)

lemma sum_tab (t : Row → ℕ) : ∑ r : Row, t r = ∑ x0 : Fin 2, ∑ x1 : Fin 2, ∑ x2 : Fin 2, ∑ x3 : Fin 2, t ![x0, x1, x2, x3] := sum_row t

lemma cnt0 : cnt 0 = 16 := by
  rw [cnt_sum, W0f, sum_tab]
  decide +kernel

lemma cnt1 : cnt 1 = 108 := by
  rw [cnt_sum, W1f, sum_tab]
  decide +kernel

lemma cnt2 : cnt 2 = 480 := by
  rw [cnt_sum, W2f, sum_tab]
  decide +kernel

lemma cnt3 : cnt 3 = 1667 := by
  rw [cnt_sum, W3f, sum_tab]
  decide +kernel

lemma cnt4 : cnt 4 = 4930 := by
  rw [cnt_sum, W4f, sum_tab]
  decide +kernel

lemma cnt5 : cnt 5 = 13052 := by
  rw [cnt_sum, W5f, sum_tab]
  decide +kernel

lemma cnt6 : cnt 6 = 31936 := by
  rw [cnt_sum, W6f, sum_tab]
  decide +kernel

lemma cnt7 : cnt 7 = 73805 := by
  rw [cnt_sum, W7f, sum_tab]
  decide +kernel

lemma cnt8 : cnt 8 = 163604 := by
  rw [cnt_sum, W8f, sum_tab]
  decide +kernel

lemma a_cast (n : ℕ) : (a n : ℚ) = (cnt n : ℚ) := by
  rw [a_eq]

lemma a_rec (k : ℕ) : (a (k + 8) : ℚ) + 35 * (a (k + 6) : ℚ) + 105 * (a (k + 4) : ℚ) + 49 * (a (k + 2) : ℚ) + 2 * (a (k + 0) : ℚ) = 9 * (a (k + 7) : ℚ) + 77 * (a (k + 5) : ℚ) + 91 * (a (k + 3) : ℚ) + 15 * (a (k + 1) : ℚ) := by
  simp only [a_cast]
  have h : cnt (k + 8) + 35 * cnt (k + 6) + 105 * cnt (k + 4) + 49 * cnt (k + 2) + 2 * cnt (k + 0) = 9 * cnt (k + 7) + 77 * cnt (k + 5) + 91 * cnt (k + 3) + 15 * cnt (k + 1) := by simpa only [Nat.add_assoc, Nat.reduceAdd] using cnt_rec (k + 0)
  have h' : ((cnt (k + 8) : ℕ) : ℚ) + 35 * ((cnt (k + 6) : ℕ) : ℚ) + 105 * ((cnt (k + 4) : ℕ) : ℚ) + 49 * ((cnt (k + 2) : ℕ) : ℚ) + 2 * ((cnt (k + 0) : ℕ) : ℚ) = 9 * ((cnt (k + 7) : ℕ) : ℚ) + 77 * ((cnt (k + 5) : ℕ) : ℚ) + 91 * ((cnt (k + 3) : ℕ) : ℚ) + 15 * ((cnt (k + 1) : ℕ) : ℚ) := by exact_mod_cast h
  linear_combination h'

lemma a0 : (a 0 : ℚ) = 16 := by
  rw [a_cast, cnt0]
  norm_num

lemma a1 : (a 1 : ℚ) = 108 := by
  rw [a_cast, cnt1]
  norm_num

lemma a2 : (a 2 : ℚ) = 480 := by
  rw [a_cast, cnt2]
  norm_num

lemma a3 : (a 3 : ℚ) = 1667 := by
  rw [a_cast, cnt3]
  norm_num

lemma a4 : (a 4 : ℚ) = 4930 := by
  rw [a_cast, cnt4]
  norm_num

lemma a5 : (a 5 : ℚ) = 13052 := by
  rw [a_cast, cnt5]
  norm_num

lemma a6 : (a 6 : ℚ) = 31936 := by
  rw [a_cast, cnt6]
  norm_num

lemma a7 : (a 7 : ℚ) = 73805 := by
  rw [a_cast, cnt7]
  norm_num

lemma a8 : (a 8 : ℚ) = 163604 := by
  rw [a_cast, cnt8]
  norm_num

/-- The g.f. as stated. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - X) ^ 7 * (1 - 2 * X)) =
      X * (108 - 492 * X + 1127 * X ^ 2 - 1589 * X ^ 3 + 1407 * X ^ 4 - 769 * X ^ 5 + 238 * X ^ 6 -
      32 * X ^ 7) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - X) ^ 7 * (1 - 2 * X)) = A - C (9 : ℚ) * (A * X ^ 1) + C (35 : ℚ) * (A * X ^ 2) - C (77 : ℚ) * (A * X ^ 3) + C (105 : ℚ) * (A * X ^ 4) - C (91 : ℚ) * (A * X ^ 5) + C (49 : ℚ) * (A * X ^ 6) - C (15 : ℚ) * (A * X ^ 7) + C (2 : ℚ) * (A * X ^ 8) := by
    rw [show (C (2 : ℚ) : ℚ⟦X⟧) = 2 from map_ofNat C 2, show (C (9 : ℚ) : ℚ⟦X⟧) = 9 from map_ofNat C 9, show (C (15 : ℚ) : ℚ⟦X⟧) = 15 from map_ofNat C 15, show (C (35 : ℚ) : ℚ⟦X⟧) = 35 from map_ofNat C 35, show (C (49 : ℚ) : ℚ⟦X⟧) = 49 from map_ofNat C 49, show (C (77 : ℚ) : ℚ⟦X⟧) = 77 from map_ofNat C 77, show (C (91 : ℚ) : ℚ⟦X⟧) = 91 from map_ofNat C 91, show (C (105 : ℚ) : ℚ⟦X⟧) = 105 from map_ofNat C 105]
    ring
  have e2 : (X * (108 - 492 * X + 1127 * X ^ 2 - 1589 * X ^ 3 + 1407 * X ^ 4 - 769 * X ^ 5 + 238 * X ^ 6 -
      32 * X ^ 7) : ℚ⟦X⟧) = C (108 : ℚ) * X ^ 1 - C (492 : ℚ) * X ^ 2 + C (1127 : ℚ) * X ^ 3 - C (1589 : ℚ) * X ^ 4 + C (1407 : ℚ) * X ^ 5 - C (769 : ℚ) * X ^ 6 + C (238 : ℚ) * X ^ 7 - C (32 : ℚ) * X ^ 8 := by
    rw [show (C (32 : ℚ) : ℚ⟦X⟧) = 32 from map_ofNat C 32, show (C (108 : ℚ) : ℚ⟦X⟧) = 108 from map_ofNat C 108, show (C (238 : ℚ) : ℚ⟦X⟧) = 238 from map_ofNat C 238, show (C (492 : ℚ) : ℚ⟦X⟧) = 492 from map_ofNat C 492, show (C (769 : ℚ) : ℚ⟦X⟧) = 769 from map_ofNat C 769, show (C (1127 : ℚ) : ℚ⟦X⟧) = 1127 from map_ofNat C 1127, show (C (1407 : ℚ) : ℚ⟦X⟧) = 1407 from map_ofNat C 1407, show (C (1589 : ℚ) : ℚ⟦X⟧) = 1589 from map_ofNat C 1589]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_C, hA,
    coeff_mk]
  rcases Nat.lt_or_ge n 9 with hn | hn
  · interval_cases n <;> norm_num only [a1, a2, a3, a4, a5, a6, a7, a8, if_true, if_false]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
    have h' := (show (a (k + 9) : ℚ) + 35 * (a (k + 7) : ℚ) + 105 * (a (k + 5) : ℚ) + 49 * (a (k + 3) : ℚ) + 2 * (a (k + 1) : ℚ) = 9 * (a (k + 8) : ℚ) + 77 * (a (k + 6) : ℚ) + 91 * (a (k + 4) : ℚ) + 15 * (a (k + 2) : ℚ) by simpa only [Nat.add_assoc, Nat.reduceAdd] using a_rec (k + 1))
    simp only [show k + 9 - 1 = k + 8 by omega, show k + 9 - 2 = k + 7 by omega, show k + 9 - 3 = k + 6 by omega, show k + 9 - 4 = k + 5 by omega, show k + 9 - 5 = k + 4 by omega, show k + 9 - 6 = k + 3 by omega, show k + 9 - 7 = k + 2 by omega, show k + 9 - 8 = k + 1 by omega, show ¬ (k + 9 = 0) by omega, show ¬ (k + 8 = 0) by omega, show ¬ (k + 7 = 0) by omega, show ¬ (k + 6 = 0) by omega, show ¬ (k + 5 = 0) by omega, show ¬ (k + 4 = 0) by omega, show ¬ (k + 3 = 0) by omega, show ¬ (k + 2 = 0) by omega, show ¬ (k + 1 = 0) by omega, show 1 ≤ k + 9 by omega, show 2 ≤ k + 9 by omega, show 3 ≤ k + 9 by omega, show 4 ≤ k + 9 by omega, show 5 ≤ k + 9 by omega, show 6 ≤ k + 9 by omega, show 7 ≤ k + 9 by omega, show 8 ≤ k + 9 by omega, show ¬ (k + 9 = 0) by omega, show ¬ (k + 9 = 1) by omega, show ¬ (k + 9 = 2) by omega, show ¬ (k + 9 = 3) by omega, show ¬ (k + 9 = 4) by omega, show ¬ (k + 9 = 5) by omega, show ¬ (k + 9 = 6) by omega, show ¬ (k + 9 = 7) by omega, show ¬ (k + 9 = 8) by omega, if_true, if_false]
    linear_combination h'

def closed_Q (n : ℕ) : ℚ := (5760 * (25 * 2 ^ (1 + n) - 49) - 186828 * n - 57236 * n ^ 2 - 9885 * n ^ 3 - 905 * n ^ 4 -
        27 * n ^ 5 + n ^ 6) / 360

lemma closed_Q_rec (m : ℕ) : closed_Q (m + 8) - 9 * closed_Q (m + 7) + 35 * closed_Q (m + 6) - 77 * closed_Q (m + 5) + 105 * closed_Q (m + 4) - 91 * closed_Q (m + 3) + 49 * closed_Q (m + 2) - 15 * closed_Q (m + 1) + 2 * closed_Q (m + 0) = 0 := by
  unfold closed_Q
  push_cast
  ring

lemma closed_key (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = closed_Q n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 9 with h | h
    · interval_cases n
      · have hk : (a 1 : ℚ) = 108 := by exact_mod_cast a1
        rw [hk]
        unfold closed_Q
        norm_num
      · have hk : (a 2 : ℚ) = 480 := by exact_mod_cast a2
        rw [hk]
        unfold closed_Q
        norm_num
      · have hk : (a 3 : ℚ) = 1667 := by exact_mod_cast a3
        rw [hk]
        unfold closed_Q
        norm_num
      · have hk : (a 4 : ℚ) = 4930 := by exact_mod_cast a4
        rw [hk]
        unfold closed_Q
        norm_num
      · have hk : (a 5 : ℚ) = 13052 := by exact_mod_cast a5
        rw [hk]
        unfold closed_Q
        norm_num
      · have hk : (a 6 : ℚ) = 31936 := by exact_mod_cast a6
        rw [hk]
        unfold closed_Q
        norm_num
      · have hk : (a 7 : ℚ) = 73805 := by exact_mod_cast a7
        rw [hk]
        unfold closed_Q
        norm_num
      · have hk : (a 8 : ℚ) = 163604 := by exact_mod_cast a8
        rw [hk]
        unfold closed_Q
        norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
      have hR := (show (a (m + 9) : ℚ) + 35 * (a (m + 7) : ℚ) + 105 * (a (m + 5) : ℚ) + 49 * (a (m + 3) : ℚ) + 2 * (a (m + 1) : ℚ) = 9 * (a (m + 8) : ℚ) + 77 * (a (m + 6) : ℚ) + 91 * (a (m + 4) : ℚ) + 15 * (a (m + 2) : ℚ) by simpa only [Nat.add_assoc, Nat.reduceAdd] using a_rec (m + 1))
      have hR' : (a (m + 9) : ℚ) + 35 * (a (m + 7) : ℚ) + 105 * (a (m + 5) : ℚ) + 49 * (a (m + 3) : ℚ) + 2 * (a (m + 1) : ℚ) = 9 * (a (m + 8) : ℚ) + 77 * (a (m + 6) : ℚ) + 91 * (a (m + 4) : ℚ) + 15 * (a (m + 2) : ℚ) := by exact_mod_cast hR
      have h1 := ih (m + 8) (by omega) (by omega)
      have h2 := ih (m + 7) (by omega) (by omega)
      have h3 := ih (m + 6) (by omega) (by omega)
      have h4 := ih (m + 5) (by omega) (by omega)
      have h5 := ih (m + 4) (by omega) (by omega)
      have h6 := ih (m + 3) (by omega) (by omega)
      have h7 := ih (m + 2) (by omega) (by omega)
      have h8 := ih (m + 1) (by omega) (by omega)
      have hG := closed_Q_rec (m + 1)
      simp only [show m + 1 + 8 = m + 9 from rfl, show m + 1 + 7 = m + 8 from rfl, show m + 1 + 6 = m + 7 from rfl, show m + 1 + 5 = m + 6 from rfl, show m + 1 + 4 = m + 5 from rfl, show m + 1 + 3 = m + 4 from rfl, show m + 1 + 2 = m + 3 from rfl, show m + 1 + 1 = m + 2 from rfl, show m + 1 + 0 = m + 1 from rfl] at hG
      linear_combination hR' + (-(-9 : ℚ)) * h1 + (-(35 : ℚ)) * h2 + (-(-77 : ℚ)) * h3 + (-(105 : ℚ)) * h4 + (-(-91 : ℚ)) * h5 + (-(49 : ℚ)) * h6 + (-(-15 : ℚ)) * h7 + (-(2 : ℚ)) * h8 + (-1 : ℚ) * hG

theorem closed : ∀ n : ℕ, 1 ≤ n → (a n : ℚ) =
      (5760 * (25 * 2 ^ (1 + n) - 49) - 186828 * n - 57236 * n ^ 2 - 9885 * n ^ 3 - 905 * n ^ 4 -
        27 * n ^ 5 + n ^ 6) / 360 := fun n hn => closed_key n hn

/-- Controls: the entry's data. -/
theorem controls : a 1 = 108 ∧ a 2 = 480 ∧ a 3 = 1667 ∧ a 4 = 4930 ∧ a 5 = 13052 ∧ a 6 = 31936 ∧ a 7 = 73805 ∧ a 8 = 163604 ∧ a 9 = 351804 ∧ a 10 = 740008 ∧ a 11 = 1532159 ∧ a 12 = 3136950 ∧ a 13 = 6372636 ∧ a 14 = 12876648 ∧ a 15 = 25924809 ∧ a 16 = 52069752 ∧ a 17 = 104417740 ∧ a 18 = 209182288 ∧ a 19 = 418791387 ∧ a 20 = 838101930 ∧ a 21 = 1676828540 ∧ a 22 = 3354401200 ∧ a 23 = 6709680485 ∧ a 24 = 13420387996 := by
  have v9 : (a 9 : ℚ) = 351804 := by
    have h := a_rec 1
    simp only [Nat.reduceAdd] at h
    rw [a1, a2, a3, a4, a5, a6, a7, a8] at h
    linarith
  have v10 : (a 10 : ℚ) = 740008 := by
    have h := a_rec 2
    simp only [Nat.reduceAdd] at h
    rw [a2, a3, a4, a5, a6, a7, a8, v9] at h
    linarith
  have v11 : (a 11 : ℚ) = 1532159 := by
    have h := a_rec 3
    simp only [Nat.reduceAdd] at h
    rw [a3, a4, a5, a6, a7, a8, v9, v10] at h
    linarith
  have v12 : (a 12 : ℚ) = 3136950 := by
    have h := a_rec 4
    simp only [Nat.reduceAdd] at h
    rw [a4, a5, a6, a7, a8, v9, v10, v11] at h
    linarith
  have v13 : (a 13 : ℚ) = 6372636 := by
    have h := a_rec 5
    simp only [Nat.reduceAdd] at h
    rw [a5, a6, a7, a8, v9, v10, v11, v12] at h
    linarith
  have v14 : (a 14 : ℚ) = 12876648 := by
    have h := a_rec 6
    simp only [Nat.reduceAdd] at h
    rw [a6, a7, a8, v9, v10, v11, v12, v13] at h
    linarith
  have v15 : (a 15 : ℚ) = 25924809 := by
    have h := a_rec 7
    simp only [Nat.reduceAdd] at h
    rw [a7, a8, v9, v10, v11, v12, v13, v14] at h
    linarith
  have v16 : (a 16 : ℚ) = 52069752 := by
    have h := a_rec 8
    simp only [Nat.reduceAdd] at h
    rw [a8, v9, v10, v11, v12, v13, v14, v15] at h
    linarith
  have v17 : (a 17 : ℚ) = 104417740 := by
    have h := a_rec 9
    simp only [Nat.reduceAdd] at h
    rw [v9, v10, v11, v12, v13, v14, v15, v16] at h
    linarith
  have v18 : (a 18 : ℚ) = 209182288 := by
    have h := a_rec 10
    simp only [Nat.reduceAdd] at h
    rw [v10, v11, v12, v13, v14, v15, v16, v17] at h
    linarith
  have v19 : (a 19 : ℚ) = 418791387 := by
    have h := a_rec 11
    simp only [Nat.reduceAdd] at h
    rw [v11, v12, v13, v14, v15, v16, v17, v18] at h
    linarith
  have v20 : (a 20 : ℚ) = 838101930 := by
    have h := a_rec 12
    simp only [Nat.reduceAdd] at h
    rw [v12, v13, v14, v15, v16, v17, v18, v19] at h
    linarith
  have v21 : (a 21 : ℚ) = 1676828540 := by
    have h := a_rec 13
    simp only [Nat.reduceAdd] at h
    rw [v13, v14, v15, v16, v17, v18, v19, v20] at h
    linarith
  have v22 : (a 22 : ℚ) = 3354401200 := by
    have h := a_rec 14
    simp only [Nat.reduceAdd] at h
    rw [v14, v15, v16, v17, v18, v19, v20, v21] at h
    linarith
  have v23 : (a 23 : ℚ) = 6709680485 := by
    have h := a_rec 15
    simp only [Nat.reduceAdd] at h
    rw [v15, v16, v17, v18, v19, v20, v21, v22] at h
    linarith
  have v24 : (a 24 : ℚ) = 13420387996 := by
    have h := a_rec 16
    simp only [Nat.reduceAdd] at h
    rw [v16, v17, v18, v19, v20, v21, v22, v23] at h
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast a1
  · exact_mod_cast a2
  · exact_mod_cast a3
  · exact_mod_cast a4
  · exact_mod_cast a5
  · exact_mod_cast a6
  · exact_mod_cast a7
  · exact_mod_cast a8
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
      ((1 - X) ^ 7 * (1 - 2 * X)) =
        X * (108 - 492 * X + 1127 * X ^ 2 - 1589 * X ^ 3 + 1407 * X ^ 4 - 769 * X ^ 5 + 238 * X ^ 6 -
          32 * X ^ 7) ∧
      ∀ n : ℕ, 1 ≤ n → (a n : ℚ) =
          (5760 * (25 * 2 ^ (1 + n) - 49) - 186828 * n - 57236 * n ^ 2 - 9885 * n ^ 3 - 905 * n ^ 4 -
            27 * n ^ 5 + n ^ 6) / 360 :=
  ⟨gf, closed⟩

end OMA.S_oeis_a251270

theorem OMA.solution : type_of% @OMA.S_oeis_a251270.main :=
  OMA.S_oeis_a251270.conjecture
