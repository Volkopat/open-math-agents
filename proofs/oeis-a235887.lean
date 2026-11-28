import OMAStatements.S_oeis_a235887

namespace OMA.S_oeis_a235887

open PowerSeries Finset



/-! ## The window condition, rows and the transfer -/

/-- A row. -/
abbrev Row := Fin 3 → Fin 4

/-- The window condition on the 2 X 2 block with top row (p, q) and bottom row (r, s). -/
def P (p q r s : Fin 4) : Prop :=
  medEq (p).val (q).val (r).val (s).val = true

instance (p q r s : Fin 4) : Decidable (P p q r s) := by unfold P; infer_instance

/-- Row s may follow row r: every block between them satisfies P. -/
def rowOK (r s : Fin 3 → Fin 4) : Prop :=
  ∀ j j' : Fin 3, j'.val = j.val + 1 → P (r j) (r j') (s j) (s j')

instance : DecidableRel rowOK := fun r s => by unfold rowOK; infer_instance

/-- Consecutive rows allowed. -/
def Valid {m : ℕ} (x : Fin m → Fin 3 → Fin 4) : Prop :=
  ∀ i i' : Fin m, i'.val = i.val + 1 → rowOK (x i) (x i')

instance {m : ℕ} : DecidablePred (@Valid m) := fun x => by unfold Valid; infer_instance

/-- The number of valid arrays with n + 1 rows. -/
def cnt (n : ℕ) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 3 → Fin 4)).filter Valid).card

lemma a_eq (n : ℕ) : a n = cnt n := by
  unfold a cnt
  exact congrArg Finset.card (Finset.filter_congr (fun x _ => Iff.rfl))

/-- W(n, r): valid arrays with n + 1 rows whose first row is r. -/
def W (n : ℕ) (r : Fin 3 → Fin 4) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 3 → Fin 4)).filter (fun x => Valid x ∧ x 0 = r)).card

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
    ∑ s : Row, f s = ∑ x0 : Fin 4, ∑ x1 : Fin 4, ∑ x2 : Fin 4, f ![x0, x1, x2] := by
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x0 _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x1 _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x2 _ => ?_)
  rw [Fintype.sum_unique]
  exact congrArg f (by funext j; fin_cases j <;> rfl)

lemma row_eta (r : Row) : r = ![r 0, r 1, r 2] := by
  funext j
  fin_cases j <;> rfl

lemma rowOK_iff (r s : Row) : rowOK r s ↔ P (r 0) (r 1) (s 0) (s 1) ∧ P (r 1) (r 2) (s 1) (s 2) := by
  constructor
  · intro h
    exact ⟨h 0 1 rfl, h 1 2 rfl⟩
  · rintro ⟨h0, h1⟩ j j' hj
    rcases j with ⟨j, hj0⟩
    rcases j' with ⟨j', hj1⟩
    simp only at hj
    subst hj
    have hjw : j < 2 := by omega
    interval_cases j
    · exact h0
    · exact h1

/-- One step of the transfer, the rows below r enumerated entry by entry. -/
def T (g : Row → ℕ) (r : Row) : ℕ :=
  ∑ x0 : Fin 4, ∑ x1 : Fin 4, if P (r 0) (r 1) x0 x1 then ∑ x2 : Fin 4, if P (r 1) (r 2) x1 x2 then g ![x0, x1, x2] else 0 else 0

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
def idx (r : Row) : ℕ := 16 * (r 0).val + 4 * (r 1).val + (r 2).val

/-- W(1, r), by the index of r. -/
def L1 : List ℕ := [4, 2, 2, 2, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 1, 2, 1,
    2, 2, 1, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 2,
    2, 2, 4]

def t1 (r : Row) : ℕ := L1.getD (idx r) 0

/-- W(2, r), by the index of r. -/
def L2 : List ℕ := [16, 4, 4, 4, 4, 4, 1, 1, 4, 1, 4, 1, 4, 1, 1, 4, 4, 4, 1, 1, 4, 16, 4, 4, 1, 4, 4, 1, 1, 4, 1,
    4, 4, 1, 4, 1, 1, 4, 4, 1, 4, 4, 16, 4, 1, 1, 4, 4, 4, 1, 1, 4, 1, 4, 1, 4, 1, 1, 4, 4, 4,
    4, 4, 16]

def t2 (r : Row) : ℕ := L2.getD (idx r) 0

/-- W(3, r), by the index of r. -/
def L3 : List ℕ := [64, 8, 8, 8, 8, 8, 1, 1, 8, 1, 8, 1, 8, 1, 1, 8, 8, 8, 1, 1, 8, 64, 8, 8, 1, 8, 8, 1, 1, 8, 1,
    8, 8, 1, 8, 1, 1, 8, 8, 1, 8, 8, 64, 8, 1, 1, 8, 8, 8, 1, 1, 8, 1, 8, 1, 8, 1, 1, 8, 8, 8,
    8, 8, 64]

def t3 (r : Row) : ℕ := L3.getD (idx r) 0

def t0 (_ : Row) : ℕ := 1

lemma W0f : W 0 = t0 := by
  funext r
  rw [W_zero]
  rfl

lemma check1 : ∀ x0 x1 x2 : Fin 4, T t0 ![x0, x1, x2] = t1 ![x0, x1, x2] := by
  decide +kernel

lemma W1f : W 1 = t1 := by
  funext r
  rw [W_succT, W0f, row_eta r]
  exact check1 (r 0) (r 1) (r 2)

lemma check2 : ∀ x0 x1 x2 : Fin 4, T t1 ![x0, x1, x2] = t2 ![x0, x1, x2] := by
  decide +kernel

lemma W2f : W 2 = t2 := by
  funext r
  rw [W_succT, W1f, row_eta r]
  exact check2 (r 0) (r 1) (r 2)

lemma check3 : ∀ x0 x1 x2 : Fin 4, T t2 ![x0, x1, x2] = t3 ![x0, x1, x2] := by
  decide +kernel

lemma W3f : W 3 = t3 := by
  funext r
  rw [W_succT, W2f, row_eta r]
  exact check3 (r 0) (r 1) (r 2)

lemma check_rel : ∀ x0 x1 x2 : Fin 4, t3 ![x0, x1, x2] + 14 * t1 ![x0, x1, x2] = 7 * t2 ![x0, x1, x2] + 8 * t0 ![x0, x1, x2] := by
  decide +kernel

/-- The per-row relation: the g.f. denominator annihilates W(k + 0), ..., W(k + 3). -/
lemma W_rec (k : ℕ) : ∀ r : Row, W (k + 3) r + 14 * W (k + 1) r = 7 * W (k + 2) r + 8 * W (k + 0) r := by
  induction k with
  | zero =>
    intro r
    simp only [Nat.zero_add, W0f, W1f, W2f, W3f]
    rw [row_eta r]
    exact check_rel (r 0) (r 1) (r 2)
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

lemma sum_tab (t : Row → ℕ) : ∑ r : Row, t r = ∑ x0 : Fin 4, ∑ x1 : Fin 4, ∑ x2 : Fin 4, t ![x0, x1, x2] := sum_row t

lemma cnt0 : cnt 0 = 64 := by
  rw [cnt_sum, W0f, sum_tab]
  decide +kernel

lemma cnt1 : cnt 1 = 112 := by
  rw [cnt_sum, W1f, sum_tab]
  decide +kernel

lemma cnt2 : cnt 2 = 232 := by
  rw [cnt_sum, W2f, sum_tab]
  decide +kernel

lemma cnt3 : cnt 3 = 568 := by
  rw [cnt_sum, W3f, sum_tab]
  decide +kernel

lemma a_cast (n : ℕ) : (a n : ℚ) = (cnt n : ℚ) := by
  rw [a_eq]

lemma a_rec (k : ℕ) : (a (k + 3) : ℚ) + 14 * (a (k + 1) : ℚ) = 7 * (a (k + 2) : ℚ) + 8 * (a (k + 0) : ℚ) := by
  simp only [a_cast]
  have h : cnt (k + 3) + 14 * cnt (k + 1) = 7 * cnt (k + 2) + 8 * cnt (k + 0) := by simpa only [Nat.add_assoc, Nat.reduceAdd] using cnt_rec (k + 0)
  have h' : ((cnt (k + 3) : ℕ) : ℚ) + 14 * ((cnt (k + 1) : ℕ) : ℚ) = 7 * ((cnt (k + 2) : ℕ) : ℚ) + 8 * ((cnt (k + 0) : ℕ) : ℚ) := by exact_mod_cast h
  linear_combination h'

lemma a0 : (a 0 : ℚ) = 64 := by
  rw [a_cast, cnt0]
  norm_num

lemma a1 : (a 1 : ℚ) = 112 := by
  rw [a_cast, cnt1]
  norm_num

lemma a2 : (a 2 : ℚ) = 232 := by
  rw [a_cast, cnt2]
  norm_num

lemma a3 : (a 3 : ℚ) = 568 := by
  rw [a_cast, cnt3]
  norm_num

/-- The g.f. as stated. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - X) * (1 - 2 * X) * (1 - 4 * X)) =
      8 * X * (14 - 69 * X + 64 * X ^ 2) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - X) * (1 - 2 * X) * (1 - 4 * X)) = A - C (7 : ℚ) * (A * X ^ 1) + C (14 : ℚ) * (A * X ^ 2) - C (8 : ℚ) * (A * X ^ 3) := by
    rw [show (C (7 : ℚ) : ℚ⟦X⟧) = 7 from map_ofNat C 7, show (C (8 : ℚ) : ℚ⟦X⟧) = 8 from map_ofNat C 8, show (C (14 : ℚ) : ℚ⟦X⟧) = 14 from map_ofNat C 14]
    ring
  have e2 : (8 * X * (14 - 69 * X + 64 * X ^ 2) : ℚ⟦X⟧) = C (112 : ℚ) * X ^ 1 - C (552 : ℚ) * X ^ 2 + C (512 : ℚ) * X ^ 3 := by
    rw [show (C (112 : ℚ) : ℚ⟦X⟧) = 112 from map_ofNat C 112, show (C (512 : ℚ) : ℚ⟦X⟧) = 512 from map_ofNat C 512, show (C (552 : ℚ) : ℚ⟦X⟧) = 552 from map_ofNat C 552]
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

def closed_Q (n : ℕ) : ℚ := 4 * (6 + 9 * 2 ^ n + 4 ^ n)

lemma closed_Q_rec (m : ℕ) : closed_Q (m + 3) - 7 * closed_Q (m + 2) + 14 * closed_Q (m + 1) - 8 * closed_Q (m + 0) = 0 := by
  unfold closed_Q
  push_cast
  ring

lemma closed_key (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = closed_Q n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 4 with h | h
    · interval_cases n
      · have hk : (a 1 : ℚ) = 112 := by exact_mod_cast a1
        rw [hk]
        unfold closed_Q
        norm_num
      · have hk : (a 2 : ℚ) = 232 := by exact_mod_cast a2
        rw [hk]
        unfold closed_Q
        norm_num
      · have hk : (a 3 : ℚ) = 568 := by exact_mod_cast a3
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

theorem closed : ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 4 * (6 + 9 * 2 ^ n + 4 ^ n) := fun n hn => closed_key n hn

/-- Controls: the entry's data. -/
theorem controls : a 1 = 112 ∧ a 2 = 232 ∧ a 3 = 568 ∧ a 4 = 1624 ∧ a 5 = 5272 ∧ a 6 = 18712 ∧ a 7 = 70168 ∧ a 8 = 271384 ∧ a 9 = 1067032 ∧ a 10 = 4231192 ∧ a 11 = 16850968 ∧ a 12 = 67256344 ∧ a 13 = 268730392 ∧ a 14 = 1074331672 ∧ a 15 = 4296146968 ∧ a 16 = 17182228504 ∧ a 17 = 68724195352 ∧ a 18 = 274887344152 ∧ a 19 = 1099530502168 ∧ a 20 = 4398084259864 ∧ a 21 = 17592261541912 ∧ a 22 = 70368895172632 := by
  have v4 : (a 4 : ℚ) = 1624 := by
    have h := a_rec 1
    simp only [Nat.reduceAdd] at h
    rw [a1, a2, a3] at h
    linarith
  have v5 : (a 5 : ℚ) = 5272 := by
    have h := a_rec 2
    simp only [Nat.reduceAdd] at h
    rw [a2, a3, v4] at h
    linarith
  have v6 : (a 6 : ℚ) = 18712 := by
    have h := a_rec 3
    simp only [Nat.reduceAdd] at h
    rw [a3, v4, v5] at h
    linarith
  have v7 : (a 7 : ℚ) = 70168 := by
    have h := a_rec 4
    simp only [Nat.reduceAdd] at h
    rw [v4, v5, v6] at h
    linarith
  have v8 : (a 8 : ℚ) = 271384 := by
    have h := a_rec 5
    simp only [Nat.reduceAdd] at h
    rw [v5, v6, v7] at h
    linarith
  have v9 : (a 9 : ℚ) = 1067032 := by
    have h := a_rec 6
    simp only [Nat.reduceAdd] at h
    rw [v6, v7, v8] at h
    linarith
  have v10 : (a 10 : ℚ) = 4231192 := by
    have h := a_rec 7
    simp only [Nat.reduceAdd] at h
    rw [v7, v8, v9] at h
    linarith
  have v11 : (a 11 : ℚ) = 16850968 := by
    have h := a_rec 8
    simp only [Nat.reduceAdd] at h
    rw [v8, v9, v10] at h
    linarith
  have v12 : (a 12 : ℚ) = 67256344 := by
    have h := a_rec 9
    simp only [Nat.reduceAdd] at h
    rw [v9, v10, v11] at h
    linarith
  have v13 : (a 13 : ℚ) = 268730392 := by
    have h := a_rec 10
    simp only [Nat.reduceAdd] at h
    rw [v10, v11, v12] at h
    linarith
  have v14 : (a 14 : ℚ) = 1074331672 := by
    have h := a_rec 11
    simp only [Nat.reduceAdd] at h
    rw [v11, v12, v13] at h
    linarith
  have v15 : (a 15 : ℚ) = 4296146968 := by
    have h := a_rec 12
    simp only [Nat.reduceAdd] at h
    rw [v12, v13, v14] at h
    linarith
  have v16 : (a 16 : ℚ) = 17182228504 := by
    have h := a_rec 13
    simp only [Nat.reduceAdd] at h
    rw [v13, v14, v15] at h
    linarith
  have v17 : (a 17 : ℚ) = 68724195352 := by
    have h := a_rec 14
    simp only [Nat.reduceAdd] at h
    rw [v14, v15, v16] at h
    linarith
  have v18 : (a 18 : ℚ) = 274887344152 := by
    have h := a_rec 15
    simp only [Nat.reduceAdd] at h
    rw [v15, v16, v17] at h
    linarith
  have v19 : (a 19 : ℚ) = 1099530502168 := by
    have h := a_rec 16
    simp only [Nat.reduceAdd] at h
    rw [v16, v17, v18] at h
    linarith
  have v20 : (a 20 : ℚ) = 4398084259864 := by
    have h := a_rec 17
    simp only [Nat.reduceAdd] at h
    rw [v17, v18, v19] at h
    linarith
  have v21 : (a 21 : ℚ) = 17592261541912 := by
    have h := a_rec 18
    simp only [Nat.reduceAdd] at h
    rw [v18, v19, v20] at h
    linarith
  have v22 : (a 22 : ℚ) = 70368895172632 := by
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
        8 * X * (14 - 69 * X + 64 * X ^ 2) ∧
      ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 4 * (6 + 9 * 2 ^ n + 4 ^ n) :=
  ⟨gf, closed⟩

end OMA.S_oeis_a235887

theorem OMA.solution : type_of% @OMA.S_oeis_a235887.main :=
  OMA.S_oeis_a235887.conjecture
