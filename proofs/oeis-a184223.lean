import OMAStatements.S_oeis_a184223

namespace OMA.S_oeis_a184223

open PowerSeries Finset


/-! ## The window condition, rows and the transfer -/

/-- A row. -/
abbrev Row := Fin 2 → Fin 4

/-- The window condition on the 2 X 2 block with top row (p, q) and bottom row (r, s). -/
def P (p q r s : Fin 4) : Prop :=
  3 < |((p).val + (s).val : ℤ) - ((q).val + (r).val)|

instance (p q r s : Fin 4) : Decidable (P p q r s) := by unfold P; infer_instance

/-- Row s may follow row r: every block between them satisfies P. -/
def rowOK (r s : Fin 2 → Fin 4) : Prop :=
  ∀ j j' : Fin 2, j'.val = j.val + 1 → P (r j) (r j') (s j) (s j')

instance : DecidableRel rowOK := fun r s => by unfold rowOK; infer_instance

/-- Consecutive rows allowed. -/
def Valid {m : ℕ} (x : Fin m → Fin 2 → Fin 4) : Prop :=
  ∀ i i' : Fin m, i'.val = i.val + 1 → rowOK (x i) (x i')

instance {m : ℕ} : DecidablePred (@Valid m) := fun x => by unfold Valid; infer_instance

/-- The number of valid arrays with n + 1 rows. -/
def cnt (n : ℕ) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 2 → Fin 4)).filter Valid).card

lemma a_eq (n : ℕ) : a n = cnt n / 2 := by
  unfold a cnt
  congr 1

/-- W(n, r): valid arrays with n + 1 rows whose first row is r. -/
def W (n : ℕ) (r : Fin 2 → Fin 4) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 2 → Fin 4)).filter (fun x => Valid x ∧ x 0 = r)).card

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
    ∑ s : Row, f s = ∑ x0 : Fin 4, ∑ x1 : Fin 4, f ![x0, x1] := by
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x0 _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x1 _ => ?_)
  rw [Fintype.sum_unique]
  exact congrArg f (by funext j; fin_cases j <;> rfl)

lemma row_eta (r : Row) : r = ![r 0, r 1] := by
  funext j
  fin_cases j <;> rfl

lemma rowOK_iff (r s : Row) : rowOK r s ↔ P (r 0) (r 1) (s 0) (s 1) := by
  constructor
  · intro h
    exact h 0 1 rfl
  · intro h0 j j' hj
    rcases j with ⟨j, hj0⟩
    rcases j' with ⟨j', hj1⟩
    simp only at hj
    subst hj
    have hjw : j < 1 := by omega
    interval_cases j
    · exact h0

/-- One step of the transfer, the rows below r enumerated entry by entry. -/
def T (g : Row → ℕ) (r : Row) : ℕ :=
  ∑ x0 : Fin 4, ∑ x1 : Fin 4, if P (r 0) (r 1) x0 x1 then g ![x0, x1] else 0

lemma T_eq (g : Row → ℕ) (r : Row) :
    T g r = ∑ s, if rowOK r s then g s else 0 := by
  rw [sum_row]
  unfold T
  simp only [rowOK_iff, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ, Matrix.head_cons,
    ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero]

lemma W_succT (n : ℕ) (r : Row) : W (n + 1) r = T (W n) r := by
  rw [W_succ, T_eq]

/-- The index of a row in the tables. -/
def idx (r : Row) : ℕ := 4 * (r 0).val + (r 1).val

/-- W(1, r), by the index of r. -/
def L1 : List ℕ := [0, 1, 3, 6, 1, 0, 1, 3, 3, 1, 0, 1, 6, 3, 1, 0]

def t1 (r : Row) : ℕ := L1.getD (idx r) 0

/-- W(2, r), by the index of r. -/
def L2 : List ℕ := [0, 6, 12, 15, 6, 0, 6, 12, 12, 6, 0, 6, 15, 12, 6, 0]

def t2 (r : Row) : ℕ := L2.getD (idx r) 0

/-- W(3, r), by the index of r. -/
def L3 : List ℕ := [0, 15, 39, 57, 15, 0, 15, 39, 39, 15, 0, 15, 57, 39, 15, 0]

def t3 (r : Row) : ℕ := L3.getD (idx r) 0

/-- W(4, r), by the index of r. -/
def L4 : List ℕ := [0, 57, 135, 180, 57, 0, 57, 135, 135, 57, 0, 57, 180, 135, 57, 0]

def t4 (r : Row) : ℕ := L4.getD (idx r) 0

def t0 (_ : Row) : ℕ := 1

lemma W0f : W 0 = t0 := by
  funext r
  rw [W_zero]
  rfl

lemma check1 : ∀ x0 x1 : Fin 4, T t0 ![x0, x1] = t1 ![x0, x1] := by
  decide +kernel

lemma W1f : W 1 = t1 := by
  funext r
  rw [W_succT, W0f, row_eta r]
  exact check1 (r 0) (r 1)

lemma check2 : ∀ x0 x1 : Fin 4, T t1 ![x0, x1] = t2 ![x0, x1] := by
  decide +kernel

lemma W2f : W 2 = t2 := by
  funext r
  rw [W_succT, W1f, row_eta r]
  exact check2 (r 0) (r 1)

lemma check3 : ∀ x0 x1 : Fin 4, T t2 ![x0, x1] = t3 ![x0, x1] := by
  decide +kernel

lemma W3f : W 3 = t3 := by
  funext r
  rw [W_succT, W2f, row_eta r]
  exact check3 (r 0) (r 1)

lemma check4 : ∀ x0 x1 : Fin 4, T t3 ![x0, x1] = t4 ![x0, x1] := by
  decide +kernel

lemma W4f : W 4 = t4 := by
  funext r
  rw [W_succT, W3f, row_eta r]
  exact check4 (r 0) (r 1)

lemma check_rel : ∀ x0 x1 : Fin 4, t4 ![x0, x1] + 6 * t1 ![x0, x1] = 3 * t3 ![x0, x1] + 3 * t2 ![x0, x1] := by
  decide +kernel

/-- The per-row relation: the g.f. denominator annihilates W(k + 1), ..., W(k + 4). -/
lemma W_rec (k : ℕ) : ∀ r : Row, W (k + 4) r + 6 * W (k + 1) r = 3 * W (k + 3) r + 3 * W (k + 2) r := by
  induction k with
  | zero =>
    intro r
    simp only [Nat.zero_add, W1f, W2f, W3f, W4f]
    rw [row_eta r]
    exact check_rel (r 0) (r 1)
  | succ k ih =>
    intro r
    rw [show k + 1 + 1 = (k + 1) + 1 from rfl, show k + 1 + 2 = (k + 2) + 1 from rfl, show k + 1 + 3 = (k + 3) + 1 from rfl, show k + 1 + 4 = (k + 4) + 1 from rfl]
    rw [W_succ (k + 1), W_succ (k + 2), W_succ (k + 3), W_succ (k + 4)]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    split_ifs
    · exact ih s
    · simp

lemma cnt_rec (k : ℕ) : cnt (k + 4)  + 6 * cnt (k + 1)  = 3 * cnt (k + 3)  + 3 * cnt (k + 2)  := by
  simp only [cnt_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun r _ => W_rec k r)

lemma sum_tab (t : Row → ℕ) : ∑ r : Row, t r = ∑ x0 : Fin 4, ∑ x1 : Fin 4, t ![x0, x1] := sum_row t

lemma cnt0 : cnt 0 = 16 := by
  rw [cnt_sum, W0f, sum_tab]
  decide +kernel

lemma cnt1 : cnt 1 = 30 := by
  rw [cnt_sum, W1f, sum_tab]
  decide +kernel

lemma cnt2 : cnt 2 = 114 := by
  rw [cnt_sum, W2f, sum_tab]
  decide +kernel

lemma cnt3 : cnt 3 = 360 := by
  rw [cnt_sum, W3f, sum_tab]
  decide +kernel

lemma cnt4 : cnt 4 = 1242 := by
  rw [cnt_sum, W4f, sum_tab]
  decide +kernel

lemma cnt_dvd (n : ℕ) : 2 ∣ cnt n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 5 with h | h
    · interval_cases n
      · rw [cnt0]; norm_num
      · rw [cnt1]; norm_num
      · rw [cnt2]; norm_num
      · rw [cnt3]; norm_num
      · rw [cnt4]; norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
      have h : cnt (k + 5) + 6 * cnt (k + 2) = 3 * cnt (k + 4) + 3 * cnt (k + 3) := by simpa only [Nat.add_assoc, Nat.reduceAdd] using cnt_rec (k + 1)
      have hs : 2 ∣ 3 * cnt (k + 4) + 3 * cnt (k + 3) := by
        exact (Dvd.dvd.add (Dvd.dvd.mul_left (ih (k + 4) (by omega)) 3) (Dvd.dvd.mul_left (ih (k + 3) (by omega)) 3))
      have hp : 2 ∣ 6 * cnt (k + 2) := by
        exact (Dvd.dvd.mul_left (ih (k + 2) (by omega)) 6)
      omega

lemma a_cast (n : ℕ) : (a n : ℚ) = (cnt n : ℚ) / 2 := by
  rw [a_eq]
  obtain ⟨m, hm⟩ := cnt_dvd n
  rw [hm, Nat.mul_div_cancel_left _ (by norm_num)]
  push_cast
  ring

lemma a_rec (k : ℕ) : (a (k + 4) : ℚ) + 6 * (a (k + 1) : ℚ) = 3 * (a (k + 3) : ℚ) + 3 * (a (k + 2) : ℚ) := by
  simp only [a_cast]
  have h := cnt_rec k
  have h' : ((cnt (k + 4) : ℕ) : ℚ) + 6 * ((cnt (k + 1) : ℕ) : ℚ) = 3 * ((cnt (k + 3) : ℕ) : ℚ) + 3 * ((cnt (k + 2) : ℕ) : ℚ) := by exact_mod_cast h
  linear_combination h' / 2

lemma a0 : (a 0 : ℚ) = 8 := by
  rw [a_cast, cnt0]
  norm_num

lemma a1 : (a 1 : ℚ) = 15 := by
  rw [a_cast, cnt1]
  norm_num

lemma a2 : (a 2 : ℚ) = 57 := by
  rw [a_cast, cnt2]
  norm_num

lemma a3 : (a 3 : ℚ) = 180 := by
  rw [a_cast, cnt3]
  norm_num

lemma a4 : (a 4 : ℚ) = 621 := by
  rw [a_cast, cnt4]
  norm_num

/-- The g.f. as stated. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    (6 * X ^ 3 - 3 * X ^ 2 - 3 * X + 1) = -3 * X * (2 * X + 1) * (6 * X - 5) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (6 * X ^ 3 - 3 * X ^ 2 - 3 * X + 1) = A - C (3 : ℚ) * (A * X ^ 1) - C (3 : ℚ) * (A * X ^ 2) + C (6 : ℚ) * (A * X ^ 3) := by
    rw [show (C (3 : ℚ) : ℚ⟦X⟧) = 3 from map_ofNat C 3, show (C (6 : ℚ) : ℚ⟦X⟧) = 6 from map_ofNat C 6]
    ring
  have e2 : (-3 * X * (2 * X + 1) * (6 * X - 5) : ℚ⟦X⟧) = C (15 : ℚ) * X ^ 1 + C (12 : ℚ) * X ^ 2 - C (36 : ℚ) * X ^ 3 := by
    rw [show (C (12 : ℚ) : ℚ⟦X⟧) = 12 from map_ofNat C 12, show (C (15 : ℚ) : ℚ⟦X⟧) = 15 from map_ofNat C 15, show (C (36 : ℚ) : ℚ⟦X⟧) = 36 from map_ofNat C 36]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_C, hA,
    coeff_mk]
  rcases Nat.lt_or_ge n 4 with hn | hn
  · interval_cases n <;> norm_num only [a1, a2, a3, if_true, if_false]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    have h' := (show (a (k + 4) : ℚ) + 6 * (a (k + 1) : ℚ) = 3 * (a (k + 3) : ℚ) + 3 * (a (k + 2) : ℚ) by simpa only [Nat.add_assoc, Nat.reduceAdd] using a_rec (k + 0))
    simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega, show k + 4 - 3 = k + 1 by omega, show ¬ (k + 4 = 0) by omega, show ¬ (k + 3 = 0) by omega, show ¬ (k + 2 = 0) by omega, show ¬ (k + 1 = 0) by omega, show 1 ≤ k + 4 by omega, show 2 ≤ k + 4 by omega, show 3 ≤ k + 4 by omega, show ¬ (k + 4 = 0) by omega, show ¬ (k + 4 = 1) by omega, show ¬ (k + 4 = 2) by omega, show ¬ (k + 4 = 3) by omega, if_true, if_false]
    linear_combination h'

/-- The recurrence as stated. -/
theorem rec : ∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 3 * a (n - 1) + 3 * a (n - 2) - 6 * a (n - 3) := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have h := (show (a (k + 4) : ℚ) + 6 * (a (k + 1) : ℚ) = 3 * (a (k + 3) : ℚ) + 3 * (a (k + 2) : ℚ) by simpa only [Nat.add_assoc, Nat.reduceAdd] using a_rec (k + 0))
  simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega, show k + 4 - 3 = k + 1 by omega]
  have h2 : ((a (k + 4) : ℤ) : ℚ) = ((3 * (a (k + 3) : ℤ) + 3 * (a (k + 2) : ℤ) - 6 * (a (k + 1) : ℤ) : ℤ) : ℚ) := by
    push_cast
    linear_combination h
  exact_mod_cast h2

/-- Controls: the entry's data. -/
theorem controls : a 1 = 15 ∧ a 2 = 57 ∧ a 3 = 180 ∧ a 4 = 621 ∧ a 5 = 2061 ∧ a 6 = 6966 ∧ a 7 = 23355 ∧ a 8 = 78597 ∧ a 9 = 264060 ∧ a 10 = 887841 ∧ a 11 = 2984121 ∧ a 12 = 10031526 ∧ a 13 = 33719895 ∧ a 14 = 113349537 ∧ a 15 = 381019140 ∧ a 16 = 1280786661 ∧ a 17 = 4305320181 ∧ a 18 = 14472205686 ∧ a 19 = 48647857635 ∧ a 20 = 163528268877 ∧ a 21 = 549695145420 ∧ a 22 = 1847783097081 ∧ a 23 = 6211265114241 := by
  have v5 : (a 5 : ℚ) = 2061 := by
    have h := a_rec 1
    simp only [Nat.reduceAdd] at h
    rw [a2, a3, a4] at h
    linarith
  have v6 : (a 6 : ℚ) = 6966 := by
    have h := a_rec 2
    simp only [Nat.reduceAdd] at h
    rw [a3, a4, v5] at h
    linarith
  have v7 : (a 7 : ℚ) = 23355 := by
    have h := a_rec 3
    simp only [Nat.reduceAdd] at h
    rw [a4, v5, v6] at h
    linarith
  have v8 : (a 8 : ℚ) = 78597 := by
    have h := a_rec 4
    simp only [Nat.reduceAdd] at h
    rw [v5, v6, v7] at h
    linarith
  have v9 : (a 9 : ℚ) = 264060 := by
    have h := a_rec 5
    simp only [Nat.reduceAdd] at h
    rw [v6, v7, v8] at h
    linarith
  have v10 : (a 10 : ℚ) = 887841 := by
    have h := a_rec 6
    simp only [Nat.reduceAdd] at h
    rw [v7, v8, v9] at h
    linarith
  have v11 : (a 11 : ℚ) = 2984121 := by
    have h := a_rec 7
    simp only [Nat.reduceAdd] at h
    rw [v8, v9, v10] at h
    linarith
  have v12 : (a 12 : ℚ) = 10031526 := by
    have h := a_rec 8
    simp only [Nat.reduceAdd] at h
    rw [v9, v10, v11] at h
    linarith
  have v13 : (a 13 : ℚ) = 33719895 := by
    have h := a_rec 9
    simp only [Nat.reduceAdd] at h
    rw [v10, v11, v12] at h
    linarith
  have v14 : (a 14 : ℚ) = 113349537 := by
    have h := a_rec 10
    simp only [Nat.reduceAdd] at h
    rw [v11, v12, v13] at h
    linarith
  have v15 : (a 15 : ℚ) = 381019140 := by
    have h := a_rec 11
    simp only [Nat.reduceAdd] at h
    rw [v12, v13, v14] at h
    linarith
  have v16 : (a 16 : ℚ) = 1280786661 := by
    have h := a_rec 12
    simp only [Nat.reduceAdd] at h
    rw [v13, v14, v15] at h
    linarith
  have v17 : (a 17 : ℚ) = 4305320181 := by
    have h := a_rec 13
    simp only [Nat.reduceAdd] at h
    rw [v14, v15, v16] at h
    linarith
  have v18 : (a 18 : ℚ) = 14472205686 := by
    have h := a_rec 14
    simp only [Nat.reduceAdd] at h
    rw [v15, v16, v17] at h
    linarith
  have v19 : (a 19 : ℚ) = 48647857635 := by
    have h := a_rec 15
    simp only [Nat.reduceAdd] at h
    rw [v16, v17, v18] at h
    linarith
  have v20 : (a 20 : ℚ) = 163528268877 := by
    have h := a_rec 16
    simp only [Nat.reduceAdd] at h
    rw [v17, v18, v19] at h
    linarith
  have v21 : (a 21 : ℚ) = 549695145420 := by
    have h := a_rec 17
    simp only [Nat.reduceAdd] at h
    rw [v18, v19, v20] at h
    linarith
  have v22 : (a 22 : ℚ) = 1847783097081 := by
    have h := a_rec 18
    simp only [Nat.reduceAdd] at h
    rw [v19, v20, v21] at h
    linarith
  have v23 : (a 23 : ℚ) = 6211265114241 := by
    have h := a_rec 19
    simp only [Nat.reduceAdd] at h
    rw [v20, v21, v22] at h
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast a1
  · exact_mod_cast a2
  · exact_mod_cast a3
  · exact_mod_cast a4
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

/-- The conjunction stated as `main`. -/
theorem conjecture :
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 3 * a (n - 1) + 3 * a (n - 2) - 6 * a (n - 3)) ∧
      PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        (6 * X ^ 3 - 3 * X ^ 2 - 3 * X + 1) = -3 * X * (2 * X + 1) * (6 * X - 5) :=
  ⟨rec, gf⟩

end OMA.S_oeis_a184223

theorem OMA.solution : type_of% @OMA.S_oeis_a184223.main :=
  OMA.S_oeis_a184223.conjecture
