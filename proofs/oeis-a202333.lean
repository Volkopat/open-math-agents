import OMAStatements.S_oeis_a202333

/-!
Proof of the two conjectures of the statement. Our own argument: a column (or row) of bits is good
exactly when a 1 forces 1s at the next two positions (when there are two of them), so an array is a
chain of good rows below each other plus two free good rows at the bottom; the transfer over the good
rows is unipotent. The array is first carried to Bool entries, where the transfer is done. The g.f.
step follows the pattern of the merged proof of oeis-a202456 by @jleguina.
-/

namespace OMA.S_oeis_a202333

open PowerSeries





def win (b0 b1 : Bool) : ℕ := 2 * b0.toNat + b1.toNat


def windowsOK : List Bool → Bool
  | b0 :: b1 :: b2 :: rest => decide (win b0 b1 ≤ win b1 b2) && windowsOK (b1 :: b2 :: rest)
  | _ => true


def good {r : ℕ} (x : Fin r → Fin 7 → Bool) : Bool :=
  decide (∀ i, windowsOK (List.ofFn (x i)) = true) && decide (∀ j, windowsOK (List.ofFn fun i => x i j) = true)


def aB (n : ℕ) : ℕ := (Finset.univ.filter fun x : Fin (n + 1) → Fin 7 → Bool => good x = true).card


theorem wOK_short : ∀ l : List Bool, l.length ≤ 2 → windowsOK l = true
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | _ :: _ :: _ :: _, h => by simp only [List.length_cons] at h; omega

theorem wOK_cons (b : Bool) (l : List Bool) (hl : 2 ≤ l.length) :
    windowsOK (b :: l) = true ↔ windowsOK l = true ∧ (b = true → ∀ x ∈ l.take 2, x = true) := by
  match l, hl with
  | c0 :: c1 :: rest, _ =>
    show (decide (win b c0 ≤ win c0 c1) && windowsOK (c0 :: c1 :: rest)) = true ↔ _
    rw [Bool.and_eq_true, decide_eq_true_eq, and_comm]
    apply and_congr_right
    intro _
    simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil, or_false]
    cases b <;> cases c0 <;> cases c1 <;> simp [win]
  | [], h => simp at h
  | [_], h => simp at h

abbrev Row := Fin 7 → Bool


def sub (s r : Row) : Prop := ∀ j, s j = true → r j = true

instance (s r : Row) : Decidable (sub s r) := by unfold sub; infer_instance


def Above (s : Row) {m : ℕ} (y : Fin m → Row) : Prop :=
  ∀ j, s j = true → ∀ x ∈ (List.ofFn fun i => y i j).take 2, x = true

instance (s : Row) {m : ℕ} (y : Fin m → Row) : Decidable (Above s y) := by unfold Above; infer_instance

theorem good_iff {m : ℕ} (x : Fin m → Row) :
    good x = true ↔ (∀ i, windowsOK (List.ofFn (x i)) = true) ∧ ∀ j, windowsOK (List.ofFn fun i => x i j) = true := by
  simp only [good, Bool.and_eq_true, decide_eq_true_eq]

theorem col_cons {m : ℕ} (r : Row) (y : Fin m → Row) (j : Fin 7) :
    (List.ofFn fun i : Fin (m + 1) => (Fin.cons r y : Fin (m + 1) → Row) i j) = r j :: List.ofFn fun i => y i j := by
  rw [List.ofFn_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

theorem good_cons {t : ℕ} (r : Row) (y : Fin (t + 2) → Row) :
    good (Fin.cons r y : Fin (t + 2 + 1) → Row) = true ↔
      windowsOK (List.ofFn r) = true ∧ good y = true ∧ Above r y := by
  rw [good_iff, good_iff, Fin.forall_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, col_cons]
  have hc : ∀ j, windowsOK (r j :: List.ofFn fun i => y i j) = true ↔
      windowsOK (List.ofFn fun i => y i j) = true ∧ (r j = true → ∀ x ∈ (List.ofFn fun i => y i j).take 2, x = true) :=
    fun j => wOK_cons _ _ (by simp)
  simp only [hc, forall_and, Above]
  tauto

theorem Above_cons {t : ℕ} (s r : Row) (y : Fin (t + 2) → Row) (h : Above r y) :
    Above s (Fin.cons r y : Fin (t + 2 + 1) → Row) ↔ sub s r := by
  unfold Above sub
  simp only [col_cons, List.take_succ_cons, List.mem_cons, forall_eq_or_imp]
  constructor
  · intro hs j hj
    exact (hs j hj).1
  · intro hs j hj
    refine ⟨hs j hj, fun x hx => h j (hs j hj) x ?_⟩
    have : (List.ofFn fun i => y i j).take 1 = ((List.ofFn fun i => y i j).take 2).take 1 := by
      rw [List.take_take]; rfl
    rw [this] at hx
    exact List.mem_of_mem_take hx


def H (t : ℕ) (s : Row) : ℕ :=
  (Finset.univ.filter fun y : Fin (t + 2) → Row => good y = true ∧ Above s y).card

theorem H_succ (t : ℕ) (s : Row) :
    H (t + 1) s = ∑ r : Row, if windowsOK (List.ofFn r) = true ∧ sub s r then H t r else 0 := by
  unfold H
  rw [Finset.card_filter]
  rw [show (∑ x : Fin (t + 1 + 2) → Row, if good x = true ∧ Above s x then 1 else 0) =
      ∑ x : Fin (t + 2 + 1) → Row, if good x = true ∧ Above s x then 1 else 0 from rfl]
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
    H 0 s = ((Finset.univ.filter fun r : Row => windowsOK (List.ofFn r) = true ∧ sub s r).card) ^ 2 := by
  unfold H
  rw [show (Finset.univ.filter fun y : Fin (0 + 2) → Row => good y = true ∧ Above s y) =
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
  have htake : ∀ j, (List.ofFn fun i => y i j).take 2 = List.ofFn fun i => y i j :=
    fun j => List.take_of_length_le (by simp)
  simp only [hcol, htake, List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff, implies_true, and_true]
  constructor
  · rintro ⟨h1, h2⟩ i
    exact ⟨h1 i, fun j hj => h2 j hj i⟩
  · intro h
    exact ⟨fun i => (h i).1, fun j hj i => (h i).2 j hj⟩


def vr : Fin 9 → Row :=
  ![![false, false, false, false, false, false, false],
    ![false, false, false, false, false, false, true],
    ![false, false, false, false, false, true, false],
    ![false, false, false, false, false, true, true],
    ![false, false, false, false, true, true, true],
    ![false, false, false, true, true, true, true],
    ![false, false, true, true, true, true, true],
    ![false, true, true, true, true, true, true],
    ![true, true, true, true, true, true, true]]

theorem rowE : ∀ r : Row, windowsOK (List.ofFn r) = true ↔ ∃ i, vr i = r := by
  decide +kernel

theorem vr_inj : Function.Injective vr := by
  decide +kernel

theorem sum_rows (f : Row → ℕ) (P : Row → Prop) [DecidablePred P] :
    (∑ r : Row, if windowsOK (List.ofFn r) = true ∧ P r then f r else 0) =
      ∑ i : Fin 9, if P (vr i) then f (vr i) else 0 := by
  rw [← Finset.sum_image (f := fun r => if P r then f r else 0) (fun i _ j _ h => vr_inj h)]
  rw [← Finset.sum_filter]
  rw [← Finset.sum_filter]
  congr 1
  ext r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, rowE]


def h (t : ℕ) (i : Fin 9) : ℕ := H t (vr i)

theorem h_succ (t : ℕ) (i : Fin 9) :
    h (t + 1) i = ∑ i' : Fin 9, if sub (vr i) (vr i') then h t i' else 0 := by
  unfold h
  rw [H_succ, sum_rows (fun r => H t r) (sub (vr i))]

theorem h_zero (i : Fin 9) :
    h 0 i = (∑ i' : Fin 9, if sub (vr i) (vr i') then 1 else 0) ^ 2 := by
  unfold h
  rw [H_zero, Finset.card_filter, sum_rows (fun _ => 1) (sub (vr i))]

theorem a_h (t : ℕ) : aB (t + 1) = h t 0 := by
  unfold aB h H
  show (Finset.univ.filter fun x : Fin (t + 2) → Row => good x = true).card = _
  congr 1
  apply Finset.filter_congr
  intro y _
  have hz : ∀ j, vr 0 j = false := by decide
  simp [Above, hz]


def tb0 : Fin 9 → ℕ := ![81, 49, 49, 36, 25, 16, 9, 4, 1]


def tb1 : Fin 9 → ℕ := ![270, 140, 140, 91, 55, 30, 14, 5, 1]


def tb2 : Fin 9 → ℕ := ![746, 336, 336, 196, 105, 50, 20, 6, 1]


def tb3 : Fin 9 → ℕ := ![1796, 714, 714, 378, 182, 77, 27, 7, 1]


def tb4 : Fin 9 → ℕ := ![3896, 1386, 1386, 672, 294, 112, 35, 8, 1]


def tb5 : Fin 9 → ℕ := ![7790, 2508, 2508, 1122, 450, 156, 44, 9, 1]


def tb6 : Fin 9 → ℕ := ![14588, 4290, 4290, 1782, 660, 210, 54, 10, 1]


def tb7 : Fin 9 → ℕ := ![25885, 7007, 7007, 2717, 935, 275, 65, 11, 1]


def tb8 : Fin 9 → ℕ := ![43903, 11011, 11011, 4004, 1287, 352, 77, 12, 1]

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

theorem h_rec (t : ℕ) : ∀ i, (h (t + 8) i : ℤ) = 8 * (h (t + 7) i : ℤ) - 28 * (h (t + 6) i : ℤ) + 56 * (h (t + 5) i : ℤ) - 70 * (h (t + 4) i : ℤ) + 56 * (h (t + 3) i : ℤ) - 28 * (h (t + 2) i : ℤ) + 8 * (h (t + 1) i : ℤ) - (h (t) i : ℤ) := by
  induction t with
  | zero =>
    intro i
    simp only [Nat.zero_add]
    rw [hT8 i, hT7 i, hT6 i, hT5 i, hT4 i, hT3 i, hT2 i, hT1 i, hT0 i]
    revert i
    decide +kernel
  | succ t ih =>
    intro i
    rw [show t + 1 + 8 = t + 8 + 1 from rfl, show t + 1 + 1 = t + 1 + 1 from rfl, show t + 1 + 2 = t + 2 + 1 from rfl, show t + 1 + 3 = t + 3 + 1 from rfl, show t + 1 + 4 = t + 4 + 1 from rfl, show t + 1 + 5 = t + 5 + 1 from rfl, show t + 1 + 6 = t + 6 + 1 from rfl, show t + 1 + 7 = t + 7 + 1 from rfl]
    rw [h_succ (t + 8) i, h_succ (t + 7) i, h_succ (t + 6) i, h_succ (t + 5) i, h_succ (t + 4) i, h_succ (t + 3) i, h_succ (t + 2) i, h_succ (t + 1) i, h_succ t i]
    push_cast
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i' _ => ?_)
    split_ifs
    · exact ih i'
    · simp

theorem recurrence (n : ℕ) (hn : 8 < n) : (aB n : ℤ) = 8 * aB (n - 1) - 28 * aB (n - 2) + 56 * aB (n - 3) - 70 * aB (n - 4) + 56 * aB (n - 5) - 28 * aB (n - 6) + 8 * aB (n - 7) - aB (n - 8) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
  rw [show k + 9 - 1 = (k + 7) + 1 from by omega, show k + 9 - 2 = (k + 6) + 1 from by omega, show k + 9 - 3 = (k + 5) + 1 from by omega, show k + 9 - 4 = (k + 4) + 1 from by omega, show k + 9 - 5 = (k + 3) + 1 from by omega, show k + 9 - 6 = (k + 2) + 1 from by omega, show k + 9 - 7 = (k + 1) + 1 from by omega, show k + 9 - 8 = (k + 0) + 1 from by omega]
  rw [show k + 9 = (k + 8) + 1 from rfl]
  simp only [a_h]
  rw [h_rec k]

theorem values : aB 1 = 81 ∧ aB 2 = 270 ∧ aB 3 = 746 ∧ aB 4 = 1796 ∧ aB 5 = 3896 ∧ aB 6 = 7790 ∧ aB 7 = 14588 ∧ aB 8 = 25885 :=
  ⟨by rw [a_h, hT0]; rfl, by rw [a_h, hT1]; rfl, by rw [a_h, hT2]; rfl, by rw [a_h, hT3]; rfl, by rw [a_h, hT4]; rfl, by rw [a_h, hT5]; rfl, by rw [a_h, hT6]; rfl, by rw [a_h, hT7]; rfl⟩

theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else aB n) * (1 - X) ^ 8 =
    X * (81 - 378 * X + 854 * X ^ 2 - 1148 * X ^ 3 + 966 * X ^ 4 - 502 * X ^ 5 + 148 * X ^ 6 - 19 * X ^ 7) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else aB n) with hA
  have e1 : A * (1 - X) ^ 8 = A - C 8 * (A * X ^ 1) + C 28 * (A * X ^ 2) - C 56 * (A * X ^ 3) + C 70 * (A * X ^ 4) - C 56 * (A * X ^ 5) + C 28 * (A * X ^ 6) - C 8 * (A * X ^ 7) + (A * X ^ 8) := by
    simp only [map_ofNat]; ring
  have e2 : (X * (81 - 378 * X + 854 * X ^ 2 - 1148 * X ^ 3 + 966 * X ^ 4 - 502 * X ^ 5 + 148 * X ^ 6 - 19 * X ^ 7) : ℤ⟦X⟧) = X ^ 1 * C 81 - X ^ 2 * C 378 + X ^ 3 * C 854 - X ^ 4 * C 1148 + X ^ 5 * C 966 - X ^ 6 * C 502 + X ^ 7 * C 148 - X ^ 8 * C 19 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else aB k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  have v := values
  rcases Nat.lt_or_ge n 9 with hn | hn
  · interval_cases n <;> simp_all
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 9 := ⟨n - 9, by omega⟩
    have hr := recurrence (q + 9) (by omega)
    simp only [show q + 9 - 1 = q + 8 by omega, show q + 9 - 2 = q + 7 by omega, show q + 9 - 3 = q + 6 by omega, show q + 9 - 4 = q + 5 by omega, show q + 9 - 5 = q + 4 by omega, show q + 9 - 6 = q + 3 by omega, show q + 9 - 7 = q + 2 by omega, show q + 9 - 8 = q + 1 by omega] at hr ⊢
    simp only [show ¬ q + 1 = 0 by omega, show ¬ q + 2 = 0 by omega, show ¬ q + 3 = 0 by omega, show ¬ q + 4 = 0 by omega, show ¬ q + 5 = 0 by omega, show ¬ q + 6 = 0 by omega, show ¬ q + 7 = 0 by omega, show ¬ q + 8 = 0 by omega, show ¬ q + 9 = 0 by omega, show 1 ≤ q + 9 by omega, show 2 ≤ q + 9 by omega, show 3 ≤ q + 9 by omega, show 4 ≤ q + 9 by omega, show 5 ≤ q + 9 by omega, show 6 ≤ q + 9 by omega, show 7 ≤ q + 9 by omega, show 8 ≤ q + 9 by omega, show ¬ q + 9 = 0 by omega, show ¬ q + 9 = 1 by omega, show ¬ q + 9 = 2 by omega, show ¬ q + 9 = 3 by omega, show ¬ q + 9 = 4 by omega, show ¬ q + 9 = 5 by omega, show ¬ q + 9 = 6 by omega, show ¬ q + 9 = 7 by omega, show ¬ q + 9 = 8 by omega, if_true, if_false]
    rw [hr]
    ring


theorem wOK_idx : ∀ l : List Bool, windowsOK l = true ↔
    ∀ i (h : i + 2 < l.length), win l[i] l[i + 1] ≤ win l[i + 1] l[i + 2]
  | b0 :: b1 :: b2 :: rest => by
    have ih := wOK_idx (b1 :: b2 :: rest)
    show (decide (win b0 b1 ≤ win b1 b2) && windowsOK (b1 :: b2 :: rest)) = true ↔ _
    rw [Bool.and_eq_true, decide_eq_true_eq, ih]
    constructor
    · rintro ⟨h0, h⟩ i hi
      cases i with
      | zero => exact h0
      | succ i => exact h i (by simp only [List.length_cons] at hi ⊢; omega)
    · intro h
      refine ⟨h 0 (by simp), fun i hi => ?_⟩
      exact h (i + 1) (by simp only [List.length_cons] at hi ⊢; omega)
  | [] => by simp [windowsOK]
  | [_] => by simp [windowsOK]
  | [_, _] => by simp [windowsOK]

theorem wOK_fn {L : ℕ} (v : Fin L → Bool) : windowsOK (List.ofFn v) = true ↔
    ∀ i (h : i + 2 < L), win (v ⟨i, by omega⟩) (v ⟨i + 1, by omega⟩) ≤ win (v ⟨i + 1, by omega⟩) (v ⟨i + 2, h⟩) := by
  rw [wOK_idx]
  simp only [List.length_ofFn, List.getElem_ofFn]

/-- Entries 0..1 as Booleans. -/
def eB (b : Fin 2) : Bool := decide (b = 1)

theorem eB_toNat (b : Fin 2) : (eB b).toNat = b.val := by
  fin_cases b <;> rfl

theorem win2_iff (b0 b1 b2 : Fin 2) : win2Ok b0 b1 b2 ↔ win (eB b0) (eB b1) ≤ win (eB b1) (eB b2) := by
  unfold win2Ok win
  rw [eB_toNat, eB_toNat, eB_toNat]

theorem valid_iff (n : ℕ) (A : Fin (n + 1) → Fin 7 → Fin 2) :
    isValid n A ↔ good (fun i j => eB (A i j)) = true := by
  unfold isValid
  rw [good_iff]
  simp only [wOK_fn, win2_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun r i hi => h1 r ⟨i, by omega⟩, fun c i hi => h2 c ⟨i, by omega⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun r c => h1 r c.1 (by omega), fun c r => h2 c r.1 (by omega)⟩

theorem a_eq (n : ℕ) : a (n + 1) = aB (n + 1) := by
  unfold a aB
  rw [if_neg (by omega), Fintype.card_subtype]
  let E : (Fin (n + 1 + 1) → Fin 7 → Fin 2) ≃ (Fin (n + 1 + 1) → Fin 7 → Bool) :=
    Equiv.arrowCongr (Equiv.refl _) (Equiv.arrowCongr (Equiv.refl _) finTwoEquiv)
  have hE : ∀ A, E A = fun i j => eB (A i j) := by
    intro A; funext i j
    show finTwoEquiv (A i j) = eB (A i j)
    generalize A i j = b
    fin_cases b <;> rfl
  apply Finset.card_bij (fun A _ => E A)
  · intro A hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
    rw [hE]; exact (valid_iff _ A).1 hA
  · intro A₁ _ A₂ _ h
    exact E.injective h
  · intro x hx
    refine ⟨E.symm x, ?_, E.apply_symm_apply x⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [valid_iff, ← hE, E.apply_symm_apply]
    exact hx

theorem a_zero : a 0 = 0 := by
  unfold a; rw [if_pos rfl]

theorem recV (n : ℕ) (hn : 8 < n) : (a n : ℤ) = 8 * (a (n - 1) : ℤ) - 28 * (a (n - 2) : ℤ) + 56 * (a (n - 3) : ℤ) - 70 * (a (n - 4) : ℤ) + 56 * (a (n - 5) : ℤ) - 28 * (a (n - 6) : ℤ) + 8 * (a (n - 7) : ℤ) - (a (n - 8) : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
  have h := recurrence (k + 9) hn
  rw [show k + 9 - 1 = (k + 7) + 1 from by omega, show k + 9 - 2 = (k + 6) + 1 from by omega, show k + 9 - 3 = (k + 5) + 1 from by omega, show k + 9 - 4 = (k + 4) + 1 from by omega, show k + 9 - 5 = (k + 3) + 1 from by omega, show k + 9 - 6 = (k + 2) + 1 from by omega, show k + 9 - 7 = (k + 1) + 1 from by omega, show k + 9 - 8 = (k + 0) + 1 from by omega] at h ⊢
  rw [show k + 9 = (k + 8) + 1 from rfl] at h ⊢
  simp only [a_eq]
  exact h

theorem valsV : a 1 = 81 ∧ a 2 = 270 ∧ a 3 = 746 ∧ a 4 = 1796 ∧ a 5 = 3896 ∧ a 6 = 7790 ∧ a 7 = 14588 ∧ a 8 = 25885 := by
  have v := values
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | (rw [show (1 : ℕ) = 0 + 1 from rfl, a_eq]; exact v.1) | (rw [show (2 : ℕ) = 1 + 1 from rfl, a_eq]; exact v.2.1) | (rw [show (3 : ℕ) = 2 + 1 from rfl, a_eq]; exact v.2.2.1) | (rw [show (4 : ℕ) = 3 + 1 from rfl, a_eq]; exact v.2.2.2.1) | (rw [show (5 : ℕ) = 4 + 1 from rfl, a_eq]; exact v.2.2.2.2.1) | (rw [show (6 : ℕ) = 5 + 1 from rfl, a_eq]; exact v.2.2.2.2.2.1) | (rw [show (7 : ℕ) = 6 + 1 from rfl, a_eq]; exact v.2.2.2.2.2.2.1) | (rw [show (8 : ℕ) = 7 + 1 from rfl, a_eq]; exact v.2.2.2.2.2.2.2)

theorem gfV : (PowerSeries.mk fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 8 =
    PowerSeries.X * (81 - 378 * PowerSeries.X + 854 * PowerSeries.X ^ 2 - 1148 * PowerSeries.X ^ 3 + 966 * PowerSeries.X ^ 4 - 502 * PowerSeries.X ^ 5 + 148 * PowerSeries.X ^ 6 - 19 * PowerSeries.X ^ 7) := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ)) with hA
  have e1 : A * (1 - X) ^ 8 = A  - C 8 * (A * X ^ 1)  + C 28 * (A * X ^ 2)  - C 56 * (A * X ^ 3)  + C 70 * (A * X ^ 4)  - C 56 * (A * X ^ 5)  + C 28 * (A * X ^ 6)  - C 8 * (A * X ^ 7)  + (A * X ^ 8) := by
    simp only [map_ofNat]; ring
  have e2 : (X * (81 - 378 * X + 854 * X ^ 2 - 1148 * X ^ 3 + 966 * X ^ 4 - 502 * X ^ 5 + 148 * X ^ 6 - 19 * X ^ 7) : ℚ⟦X⟧) = X ^ 1 * C 81 - X ^ 2 * C 378 + X ^ 3 * C 854 - X ^ 4 * C 1148 + X ^ 5 * C 966 - X ^ 6 * C 502 + X ^ 7 * C 148 - X ^ 8 * C 19 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = (a k : ℚ) := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  have v := valsV
  have v0 := a_zero
  rcases Nat.lt_or_ge n 9 with hn | hn
  · interval_cases n <;> simp_all <;> norm_num
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 9 := ⟨n - 9, by omega⟩
    have hr := recV (q + 9) (by omega)
    simp only [show q + 9 - 1 = q + 8 by omega, show q + 9 - 2 = q + 7 by omega, show q + 9 - 3 = q + 6 by omega, show q + 9 - 4 = q + 5 by omega, show q + 9 - 5 = q + 4 by omega, show q + 9 - 6 = q + 3 by omega, show q + 9 - 7 = q + 2 by omega, show q + 9 - 8 = q + 1 by omega] at hr ⊢
    have hr' : (a (q + 9) : ℚ) = 8 * (a (q + 8) : ℚ) - 28 * (a (q + 7) : ℚ) + 56 * (a (q + 6) : ℚ) - 70 * (a (q + 5) : ℚ) + 56 * (a (q + 4) : ℚ) - 28 * (a (q + 3) : ℚ) + 8 * (a (q + 2) : ℚ) - (a (q + 1) : ℚ) := by
      exact_mod_cast hr
    simp only [show 1 ≤ q + 9 by omega, show 2 ≤ q + 9 by omega, show 3 ≤ q + 9 by omega, show 4 ≤ q + 9 by omega, show 5 ≤ q + 9 by omega, show 6 ≤ q + 9 by omega, show 7 ≤ q + 9 by omega, show 8 ≤ q + 9 by omega, show ¬ q + 9 = 0 by omega, show ¬ q + 9 = 1 by omega, show ¬ q + 9 = 2 by omega, show ¬ q + 9 = 3 by omega, show ¬ q + 9 = 4 by omega, show ¬ q + 9 = 5 by omega, show ¬ q + 9 = 6 by omega, show ¬ q + 9 = 7 by omega, show ¬ q + 9 = 8 by omega, if_true, if_false]
    rw [hr']
    ring

theorem conjectureV :
    (PowerSeries.mk fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 8 =
      PowerSeries.X * (81 - 378 * PowerSeries.X + 854 * PowerSeries.X ^ 2 - 1148 * PowerSeries.X ^ 3 + 966 * PowerSeries.X ^ 4 - 502 * PowerSeries.X ^ 5 + 148 * PowerSeries.X ^ 6 - 19 * PowerSeries.X ^ 7) ∧
    ∀ n : ℕ, 8 < n → (a n : ℤ) = 8 * (a (n - 1) : ℤ) - 28 * (a (n - 2) : ℤ) + 56 * (a (n - 3) : ℤ) - 70 * (a (n - 4) : ℤ) + 56 * (a (n - 5) : ℤ) - 28 * (a (n - 6) : ℤ) + 8 * (a (n - 7) : ℤ) - (a (n - 8) : ℤ) :=
  ⟨gfV, recV⟩

end OMA.S_oeis_a202333

theorem OMA.solution : type_of% @OMA.S_oeis_a202333.main :=
  OMA.S_oeis_a202333.conjectureV
