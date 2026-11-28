import OMAStatements.S_oeis_a202936
/-!
Proof of Barker's two conjectures for A202936. Our own argument: a column (or row) is good exactly when,
read downwards, a 1 at some position forces 1s at the next 4 positions (when there are 4 of them).
So in an array with t + 4 rows, the bottom 4 rows are good rows lying above (entrywise) the row
just over them, and every other row lies below the next one. This gives a transfer over the 20 good
rows whose matrix is unipotent, hence the order-9 recurrence. The g.f. step follows the pattern of
the merged proof of oeis-a202456 by @jleguina.
-/

namespace OMA.S_oeis_a202936

open PowerSeries

theorem wOK_short : ∀ l : List Bool, l.length ≤ 4 → windowsOK l = true
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | [_, _, _], _ => rfl
  | [_, _, _, _], _ => rfl
  | _ :: _ :: _ :: _ :: _ :: _, h => by simp only [List.length_cons] at h; omega

theorem wOK_cons (b : Bool) (l : List Bool) (hl : 4 ≤ l.length) :
    windowsOK (b :: l) = true ↔ windowsOK l = true ∧ (b = true → ∀ x ∈ l.take 4, x = true) := by
  match l, hl with
  | c0 :: c1 :: c2 :: c3 :: rest, _ =>
    show (decide (win b c0 c1 c2 ≤ win c0 c1 c2 c3) && windowsOK (c0 :: c1 :: c2 :: c3 :: rest)) = true ↔ _
    rw [Bool.and_eq_true, decide_eq_true_eq, and_comm]
    apply and_congr_right
    intro _
    simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil, or_false]
    cases b <;> cases c0 <;> cases c1 <;> cases c2 <;> cases c3 <;> simp [win]
  | [], h => simp at h
  | [_], h => simp at h
  | [_, _], h => simp at h
  | [_, _, _], h => simp at h

abbrev Row := Fin 8 → Bool

/-- s lies entrywise below r. -/
def sub (s r : Row) : Prop := ∀ j, s j = true → r j = true

instance (s r : Row) : Decidable (sub s r) := by unfold sub; infer_instance

/-- In every column j where s has a 1, the first 4 entries of y are 1. -/
def Above (s : Row) {m : ℕ} (y : Fin m → Row) : Prop :=
  ∀ j, s j = true → ∀ x ∈ (List.ofFn fun i => y i j).take 4, x = true

instance (s : Row) {m : ℕ} (y : Fin m → Row) : Decidable (Above s y) := by unfold Above; infer_instance

theorem good_iff {m : ℕ} (x : Fin m → Row) :
    good x = true ↔ (∀ i, windowsOK (List.ofFn (x i)) = true) ∧ ∀ j, windowsOK (List.ofFn fun i => x i j) = true := by
  simp only [good, Bool.and_eq_true, decide_eq_true_eq]

theorem col_cons {m : ℕ} (r : Row) (y : Fin m → Row) (j : Fin 8) :
    (List.ofFn fun i : Fin (m + 1) => (Fin.cons r y : Fin (m + 1) → Row) i j) = r j :: List.ofFn fun i => y i j := by
  rw [List.ofFn_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

theorem good_cons {t : ℕ} (r : Row) (y : Fin (t + 4) → Row) :
    good (Fin.cons r y : Fin (t + 4 + 1) → Row) = true ↔
      windowsOK (List.ofFn r) = true ∧ good y = true ∧ Above r y := by
  rw [good_iff, good_iff, Fin.forall_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, col_cons]
  have hc : ∀ j, windowsOK (r j :: List.ofFn fun i => y i j) = true ↔
      windowsOK (List.ofFn fun i => y i j) = true ∧ (r j = true → ∀ x ∈ (List.ofFn fun i => y i j).take 4, x = true) :=
    fun j => wOK_cons _ _ (by simp)
  simp only [hc, forall_and, Above]
  tauto

theorem Above_cons {t : ℕ} (s r : Row) (y : Fin (t + 4) → Row) (h : Above r y) :
    Above s (Fin.cons r y : Fin (t + 4 + 1) → Row) ↔ sub s r := by
  unfold Above sub
  simp only [col_cons, List.take_succ_cons, List.mem_cons, forall_eq_or_imp]
  constructor
  · intro hs j hj
    exact (hs j hj).1
  · intro hs j hj
    refine ⟨hs j hj, fun x hx => h j (hs j hj) x ?_⟩
    have : (List.ofFn fun i => y i j).take 3 = ((List.ofFn fun i => y i j).take 4).take 3 := by
      rw [List.take_take]; rfl
    rw [this] at hx
    exact List.mem_of_mem_take hx

/-- H t s: good arrays with t + 4 rows whose first 4 rows lie above s. -/
def H (t : ℕ) (s : Row) : ℕ :=
  (Finset.univ.filter fun y : Fin (t + 4) → Row => good y = true ∧ Above s y).card

theorem H_succ (t : ℕ) (s : Row) :
    H (t + 1) s = ∑ r : Row, if windowsOK (List.ofFn r) = true ∧ sub s r then H t r else 0 := by
  unfold H
  rw [Finset.card_filter]
  rw [show (∑ x : Fin (t + 1 + 4) → Row, if good x = true ∧ Above s x then 1 else 0) =
      ∑ x : Fin (t + 4 + 1) → Row, if good x = true ∧ Above s x then 1 else 0 from rfl]
  rw [← (Fin.consEquiv fun _ => Row).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Finset.card_filter]
  split_ifs with hr
  · refine Finset.sum_congr rfl (fun y _ => ?_)
    by_cases hy : good y = true ∧ Above r y
    · rw [if_pos hy, if_pos]
      exact ⟨(good_cons r y).2 ⟨hr.1, hy⟩, (Above_cons s r y hy.2).2 hr.2⟩
    · rw [if_neg hy, if_neg]
      rintro ⟨h1, _⟩
      exact hy ((good_cons r y).1 h1).2
  · refine Finset.sum_eq_zero (fun y _ => ?_)
    rw [if_neg]
    rintro ⟨h1, h2⟩
    have h1' := (good_cons r y).1 h1
    exact hr ⟨h1'.1, (Above_cons s r y h1'.2.2).1 h2⟩

theorem H_zero (s : Row) :
    H 0 s = ((Finset.univ.filter fun r : Row => windowsOK (List.ofFn r) = true ∧ sub s r).card) ^ 4 := by
  unfold H
  rw [show (Finset.univ.filter fun y : Fin (0 + 4) → Row => good y = true ∧ Above s y) =
      Fintype.piFinset fun _ => Finset.univ.filter fun r : Row => windowsOK (List.ofFn r) = true ∧ sub s r from ?_]
  · rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ext y
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  simp only [Finset.mem_univ, true_and]
  have hm : ∀ i, y i ∈ (Finset.univ.filter fun r : Row => windowsOK (List.ofFn r) = true ∧ sub s r) ↔
      windowsOK (List.ofFn (y i)) = true ∧ sub s (y i) := fun i => by
    rw [Finset.mem_filter]; exact and_iff_right (Finset.mem_univ _)
  simp only [hm]
  rw [good_iff]
  unfold Above sub
  have hcol : ∀ j, windowsOK (List.ofFn fun i => y i j) = true := fun j => wOK_short _ (by simp)
  have htake : ∀ j, (List.ofFn fun i => y i j).take 4 = List.ofFn fun i => y i j :=
    fun j => List.take_of_length_le (by simp)
  simp only [hcol, htake, List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff, implies_true, and_true]
  constructor
  · rintro ⟨h1, h2⟩ i
    exact ⟨h1 i, fun j hj => h2 j hj i⟩
  · intro h
    exact ⟨fun i => (h i).1, fun j hj i => (h i).2 j hj⟩

/-- The 20 good rows. -/
def vr : Fin 20 → Row :=
  ![![false, false, false, false, false, false, false, false],
    ![false, false, false, false, false, false, false, true],
    ![false, false, false, false, false, false, true, false],
    ![false, false, false, false, false, false, true, true],
    ![false, false, false, false, false, true, false, false],
    ![false, false, false, false, false, true, false, true],
    ![false, false, false, false, false, true, true, false],
    ![false, false, false, false, false, true, true, true],
    ![false, false, false, false, true, false, false, false],
    ![false, false, false, false, true, false, false, true],
    ![false, false, false, false, true, false, true, false],
    ![false, false, false, false, true, false, true, true],
    ![false, false, false, false, true, true, false, false],
    ![false, false, false, false, true, true, false, true],
    ![false, false, false, false, true, true, true, false],
    ![false, false, false, false, true, true, true, true],
    ![false, false, false, true, true, true, true, true],
    ![false, false, true, true, true, true, true, true],
    ![false, true, true, true, true, true, true, true],
    ![true, true, true, true, true, true, true, true]]

theorem rowE : ∀ r : Row, windowsOK (List.ofFn r) = true ↔ ∃ i, vr i = r := by
  decide +kernel

theorem vr_inj : Function.Injective vr := by
  decide +kernel

theorem sum_rows (f : Row → ℕ) (P : Row → Prop) [DecidablePred P] :
    (∑ r : Row, if windowsOK (List.ofFn r) = true ∧ P r then f r else 0) =
      ∑ i : Fin 20, if P (vr i) then f (vr i) else 0 := by
  rw [← Finset.sum_image (f := fun r => if P r then f r else 0) (fun i _ j _ h => vr_inj h)]
  rw [← Finset.sum_filter]
  rw [← Finset.sum_filter]
  congr 1
  ext r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, rowE]

/-- h t i = H t (vr i). -/
def h (t : ℕ) (i : Fin 20) : ℕ := H t (vr i)

theorem h_succ (t : ℕ) (i : Fin 20) :
    h (t + 1) i = ∑ i' : Fin 20, if sub (vr i) (vr i') then h t i' else 0 := by
  unfold h
  rw [H_succ, sum_rows (fun r => H t r) (sub (vr i))]

theorem h_zero (i : Fin 20) :
    h 0 i = (∑ i' : Fin 20, if sub (vr i) (vr i') then 1 else 0) ^ 4 := by
  unfold h
  rw [H_zero, Finset.card_filter, sum_rows (fun _ => 1) (sub (vr i))]

theorem a_h (t : ℕ) : a (t + 1) = h t 0 := by
  unfold a h H
  show (Finset.univ.filter fun x : Fin (t + 4) → Row => good x = true).card = _
  congr 1
  apply Finset.filter_congr
  intro y _
  have hz : ∀ j, vr 0 j = false := by decide
  simp [Above, hz]

/-- The table of h 0. -/
def tb0 : Fin 20 → ℕ := ![160000, 20736, 20736, 4096, 20736, 4096, 4096, 1296, 20736, 4096, 4096, 1296, 4096, 1296, 1296, 625, 256, 81, 16, 1]

/-- The table of h 1. -/
def tb1 : Fin 20 → ℕ := ![273683, 37891, 37891, 7667, 37891, 7667, 7667, 2275, 37891, 7667, 7667, 2275, 7667, 2275, 2275, 979, 354, 98, 17, 1]

/-- The table of h 2. -/
def tb2 : Fin 20 → ℕ := ![481798, 69166, 69166, 13666, 69166, 13666, 13666, 3724, 69166, 13666, 13666, 3724, 13666, 3724, 3724, 1449, 470, 116, 18, 1]

/-- The table of h 3. -/
def tb3 : Fin 20 → ℕ := ![857408, 123390, 123390, 23168, 123390, 23168, 23168, 5778, 123390, 23168, 23168, 5778, 23168, 5778, 5778, 2054, 605, 135, 19, 1]

/-- The table of h 4. -/
def tb4 : Fin 20 → ℕ := ![1515902, 213042, 213042, 37538, 213042, 37538, 37538, 8592, 213042, 37538, 37538, 8592, 37538, 8592, 8592, 2814, 760, 155, 20, 1]

/-- The table of h 5. -/
def tb5 : Fin 20 → ℕ := ![2631416, 355182, 355182, 58472, 355182, 58472, 58472, 12342, 355182, 58472, 58472, 12342, 58472, 12342, 12342, 3750, 936, 176, 21, 1]

/-- The table of h 6. -/
def tb6 : Fin 20 → ℕ := ![4457228, 572508, 572508, 88040, 572508, 88040, 88040, 17226, 572508, 88040, 88040, 17226, 88040, 17226, 17226, 4884, 1134, 198, 22, 1]

/-- The table of h 7. -/
def tb7 : Fin 20 → ℕ := ![7350643, 894545, 894545, 128731, 894545, 128731, 128731, 23465, 894545, 128731, 128731, 23465, 128731, 23465, 23465, 6239, 1355, 221, 23, 1]

/-- The table of h 8. -/
def tb8 : Fin 20 → ℕ := ![11802908, 1358972, 1358972, 183500, 1358972, 183500, 183500, 31304, 1358972, 183500, 183500, 31304, 183500, 31304, 31304, 7839, 1600, 245, 24, 1]

/-- The table of h 9. -/
def tb9 : Fin 20 → ℕ := ![18474721, 2013093, 2013093, 255817, 2013093, 255817, 255817, 41013, 2013093, 255817, 255817, 41013, 255817, 41013, 41013, 9709, 1870, 270, 25, 1]

theorem hT0 : ∀ i, h 0 i = tb0 i := by
  intro i
  rw [h_zero]
  revert i
  decide +kernel

theorem hT1 : ∀ i, h 1 i = tb1 i := by
  intro i
  rw [h_succ]
  simp only [hT0]
  revert i
  decide +kernel

theorem hT2 : ∀ i, h 2 i = tb2 i := by
  intro i
  rw [h_succ]
  simp only [hT1]
  revert i
  decide +kernel

theorem hT3 : ∀ i, h 3 i = tb3 i := by
  intro i
  rw [h_succ]
  simp only [hT2]
  revert i
  decide +kernel

theorem hT4 : ∀ i, h 4 i = tb4 i := by
  intro i
  rw [h_succ]
  simp only [hT3]
  revert i
  decide +kernel

theorem hT5 : ∀ i, h 5 i = tb5 i := by
  intro i
  rw [h_succ]
  simp only [hT4]
  revert i
  decide +kernel

theorem hT6 : ∀ i, h 6 i = tb6 i := by
  intro i
  rw [h_succ]
  simp only [hT5]
  revert i
  decide +kernel

theorem hT7 : ∀ i, h 7 i = tb7 i := by
  intro i
  rw [h_succ]
  simp only [hT6]
  revert i
  decide +kernel

theorem hT8 : ∀ i, h 8 i = tb8 i := by
  intro i
  rw [h_succ]
  simp only [hT7]
  revert i
  decide +kernel

theorem hT9 : ∀ i, h 9 i = tb9 i := by
  intro i
  rw [h_succ]
  simp only [hT8]
  revert i
  decide +kernel

theorem h_rec (t : ℕ) : ∀ i, (h (t + 9) i : ℤ) = 9 * (h (t + 8) i : ℤ) - 36 * (h (t + 7) i : ℤ) + 84 * (h (t + 6) i : ℤ) - 126 * (h (t + 5) i : ℤ) + 126 * (h (t + 4) i : ℤ) - 84 * (h (t + 3) i : ℤ) + 36 * (h (t + 2) i : ℤ) - 9 * (h (t + 1) i : ℤ) + (h (t) i : ℤ) := by
  induction t with
  | zero =>
    intro i
    simp only [Nat.zero_add]
    rw [hT9 i, hT8 i, hT7 i, hT6 i, hT5 i, hT4 i, hT3 i, hT2 i, hT1 i, hT0 i]
    revert i
    decide +kernel
  | succ t ih =>
    intro i
    rw [show t + 1 + 9 = t + 9 + 1 from rfl, show t + 1 + 1 = t + 1 + 1 from rfl, show t + 1 + 2 = t + 2 + 1 from rfl, show t + 1 + 3 = t + 3 + 1 from rfl, show t + 1 + 4 = t + 4 + 1 from rfl, show t + 1 + 5 = t + 5 + 1 from rfl, show t + 1 + 6 = t + 6 + 1 from rfl, show t + 1 + 7 = t + 7 + 1 from rfl, show t + 1 + 8 = t + 8 + 1 from rfl]
    rw [h_succ (t + 9) i, h_succ (t + 8) i, h_succ (t + 7) i, h_succ (t + 6) i, h_succ (t + 5) i, h_succ (t + 4) i, h_succ (t + 3) i, h_succ (t + 2) i, h_succ (t + 1) i, h_succ t i]
    push_cast
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i' _ => ?_)
    split_ifs
    · exact ih i'
    · simp

theorem recurrence (n : ℕ) (hn : 9 < n) : (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
  rw [show k + 10 - 1 = (k + 8) + 1 from by omega, show k + 10 - 2 = (k + 7) + 1 from by omega, show k + 10 - 3 = (k + 6) + 1 from by omega, show k + 10 - 4 = (k + 5) + 1 from by omega, show k + 10 - 5 = (k + 4) + 1 from by omega, show k + 10 - 6 = (k + 3) + 1 from by omega, show k + 10 - 7 = (k + 2) + 1 from by omega, show k + 10 - 8 = (k + 1) + 1 from by omega, show k + 10 - 9 = (k + 0) + 1 from by omega]
  rw [show k + 10 = (k + 9) + 1 from rfl]
  simp only [a_h]
  rw [h_rec k]

theorem values : a 1 = 160000 ∧ a 2 = 273683 ∧ a 3 = 481798 ∧ a 4 = 857408 ∧ a 5 = 1515902 ∧ a 6 = 2631416 ∧ a 7 = 4457228 ∧ a 8 = 7350643 ∧ a 9 = 11802908 :=
  ⟨by rw [a_h, hT0]; rfl, by rw [a_h, hT1]; rfl, by rw [a_h, hT2]; rfl, by rw [a_h, hT3]; rfl, by rw [a_h, hT4]; rfl, by rw [a_h, hT5]; rfl, by rw [a_h, hT6]; rfl, by rw [a_h, hT7]; rfl, by rw [a_h, hT8]; rfl⟩

theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 9 =
    X * (160000 - 1166317 * X + 3778651 * X ^ 2 - 7066186 * X ^ 3 + 8314586 * X ^ 4 - 6291988 * X ^ 5 + 2987174 * X ^ 6 - 812969 * X ^ 7 + 97073 * X ^ 8) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (1 - X) ^ 9 = A - C 9 * (A * X ^ 1) + C 36 * (A * X ^ 2) - C 84 * (A * X ^ 3) + C 126 * (A * X ^ 4) - C 126 * (A * X ^ 5) + C 84 * (A * X ^ 6) - C 36 * (A * X ^ 7) + C 9 * (A * X ^ 8) - (A * X ^ 9) := by
    simp only [map_ofNat]; ring
  have e2 : (X * (160000 - 1166317 * X + 3778651 * X ^ 2 - 7066186 * X ^ 3 + 8314586 * X ^ 4 - 6291988 * X ^ 5 + 2987174 * X ^ 6 - 812969 * X ^ 7 + 97073 * X ^ 8) : ℤ⟦X⟧) = X ^ 1 * C 160000 - X ^ 2 * C 1166317 + X ^ 3 * C 3778651 - X ^ 4 * C 7066186 + X ^ 5 * C 8314586 - X ^ 6 * C 6291988 + X ^ 7 * C 2987174 - X ^ 8 * C 812969 + X ^ 9 * C 97073 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  have v := values
  rcases Nat.lt_or_ge n 10 with hn | hn
  · interval_cases n <;> simp_all
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 10 := ⟨n - 10, by omega⟩
    have hr := recurrence (q + 10) (by omega)
    simp only [show q + 10 - 1 = q + 9 by omega, show q + 10 - 2 = q + 8 by omega, show q + 10 - 3 = q + 7 by omega, show q + 10 - 4 = q + 6 by omega, show q + 10 - 5 = q + 5 by omega, show q + 10 - 6 = q + 4 by omega, show q + 10 - 7 = q + 3 by omega, show q + 10 - 8 = q + 2 by omega, show q + 10 - 9 = q + 1 by omega] at hr ⊢
    simp only [show ¬ q + 1 = 0 by omega, show ¬ q + 2 = 0 by omega, show ¬ q + 3 = 0 by omega, show ¬ q + 4 = 0 by omega, show ¬ q + 5 = 0 by omega, show ¬ q + 6 = 0 by omega, show ¬ q + 7 = 0 by omega, show ¬ q + 8 = 0 by omega, show ¬ q + 9 = 0 by omega, show ¬ q + 10 = 0 by omega, show 1 ≤ q + 10 by omega, show 2 ≤ q + 10 by omega, show 3 ≤ q + 10 by omega, show 4 ≤ q + 10 by omega, show 5 ≤ q + 10 by omega, show 6 ≤ q + 10 by omega, show 7 ≤ q + 10 by omega, show 8 ≤ q + 10 by omega, show 9 ≤ q + 10 by omega, show ¬ q + 10 = 0 by omega, show ¬ q + 10 = 1 by omega, show ¬ q + 10 = 2 by omega, show ¬ q + 10 = 3 by omega, show ¬ q + 10 = 4 by omega, show ¬ q + 10 = 5 by omega, show ¬ q + 10 = 6 by omega, show ¬ q + 10 = 7 by omega, show ¬ q + 10 = 8 by omega, show ¬ q + 10 = 9 by omega, if_true, if_false]
    rw [hr]
    ring

theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 9 =
      X * (160000 - 1166317 * X + 3778651 * X ^ 2 - 7066186 * X ^ 3 + 8314586 * X ^ 4 - 6291988 * X ^ 5 + 2987174 * X ^ 6 - 812969 * X ^ 7 + 97073 * X ^ 8) ∧
    ∀ n : ℕ, 9 < n → (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) :=
  ⟨gf, recurrence⟩

end OMA.S_oeis_a202936

theorem OMA.solution : type_of% @OMA.S_oeis_a202936.main :=
  OMA.S_oeis_a202936.conjecture
