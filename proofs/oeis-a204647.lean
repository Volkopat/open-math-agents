import OMAStatements.S_oeis_a204647

namespace OMA.S_oeis_a204647

open PowerSeries Finset


/-- A row. -/
abbrev S := Fin 5 → Fin 2

/-- Row s may follow row r. -/
def step (r s : S) : Prop :=
  ∀ j j' : Fin 5, j'.val = j.val + 1 →
    (r j').val + (r j).val ≤ (s j').val + (s j).val ∧ (s j).val + (r j).val ≤ (s j').val + (r j').val

instance : DecidableRel step := fun r s => by unfold step; infer_instance

/-- A valid sequence of rows. -/
def Valid {n : ℕ} (g : Fin n → S) : Prop :=
  ∀ i i' : Fin n, i'.val = i.val + 1 → step (g i) (g i')

instance {n : ℕ} : DecidablePred (@Valid n) := fun g => by unfold Valid; infer_instance

lemma a_eq (n : ℕ) : a n = ((univ : Finset (Fin (n + 1) → S)).filter Valid).card := by
  unfold a Valid step
  rfl

/-- W(n, r): valid sequences of n + 1 rows whose first row is r. -/
def W (n : ℕ) (r : S) : ℕ :=
  ((univ : Finset (Fin (n + 1) → S)).filter (fun g => Valid g ∧ g 0 = r)).card

lemma valid_cons {n : ℕ} (r : S) (g : Fin (n + 1) → S) :
    Valid (Fin.cons r g : Fin (n + 2) → S) ↔ step r (g 0) ∧ Valid g := by
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

lemma a_sum (n : ℕ) : a n = ∑ r : S, W n r := by
  rw [a_eq]
  unfold W
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g => g 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  congr 1
  ext g
  simp

lemma W_zero (r : S) : W 0 r = 1 := by
  unfold W
  rw [Finset.card_eq_one]
  refine ⟨fun _ => r, ?_⟩
  ext g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨_, hg⟩
    funext i
    rw [Fin.fin_one_eq_zero i, hg]
  · rintro rfl
    refine ⟨?_, rfl⟩
    intro i j hij
    have := j.isLt
    omega

/-- Prepending the row r. -/
def consEmb (n : ℕ) (r : S) : (Fin (n + 1) → S) ↪ (Fin (n + 2) → S) where
  toFun g := Fin.cons r g
  inj' g g' h := by
    funext i
    have := congrFun h i.succ
    simpa using this

lemma consEmb_apply (n : ℕ) (r : S) (g : Fin (n + 1) → S) :
    consEmb n r g = Fin.cons r g := rfl

lemma W_succ (n : ℕ) (r : S) :
    W (n + 1) r = ∑ s : S, if step r s then W n s else 0 := by
  have e : ((univ : Finset (Fin (n + 2) → S)).filter (fun g => Valid g ∧ g 0 = r)) =
      (((univ : Finset (Fin (n + 1) → S)).filter (fun g => step r (g 0) ∧ Valid g)).map
        (consEmb n r)) := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, consEmb_apply]
    constructor
    · rintro ⟨hv, h0⟩
      refine ⟨Fin.tail g, ?_, ?_⟩
      · have hg : g = Fin.cons r (Fin.tail g) := by
          rw [← h0]; exact (Fin.cons_self_tail g).symm
        rw [hg, valid_cons] at hv
        exact hv
      · rw [← h0]; exact Fin.cons_self_tail g
    · rintro ⟨g', hg', rfl⟩
      exact ⟨(valid_cons r g').2 hg', by simp⟩
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
    rintro ⟨⟨hst, _⟩, h0⟩
    exact hrs (h0 ▸ hst)

/-- The index of a row r in the tables below: the binary number r 0 r 1 ... r 4. -/
def idx (r : S) : ℕ := 16 * (r 0).val + 8 * (r 1).val + 4 * (r 2).val + 2 * (r 3).val + (r 4).val

def t1 (r : S) : ℕ := [6, 9, 3, 4, 2, 4, 0, 3, 1, 2, 1, 1, 0, 0, 0, 2, 1, 2, 1, 1, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1].getD (idx r) 0

def t2 (r : S) : ℕ := [25, 22, 4, 10, 1, 2, 0, 6, 1, 1, 2, 1, 0, 0, 0, 3, 2, 2, 0, 2, 1, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1].getD (idx r) 0

def t3 (r : S) : ℕ := [67, 46, 2, 20, 1, 3, 0, 10, 2, 2, 2, 2, 0, 0, 0, 4, 3, 3, 0, 3, 1, 3, 0, 3, 0, 0, 0, 0, 0, 0, 0, 1].getD (idx r) 0

def t4 (r : S) : ℕ := [148, 83, 3, 35, 2, 4, 0, 15, 3, 3, 3, 3, 0, 0, 0, 5, 4, 4, 0, 4, 2, 4, 0, 4, 0, 0, 0, 0, 0, 0, 0, 1].getD (idx r) 0

def t5 (r : S) : ℕ := [287, 142, 4, 56, 3, 6, 0, 21, 4, 4, 4, 4, 0, 0, 0, 6, 5, 5, 0, 5, 3, 6, 0, 5, 0, 0, 0, 0, 0, 0, 0, 1].getD (idx r) 0

def t6 (r : S) : ℕ := [513, 230, 6, 84, 4, 8, 0, 28, 5, 5, 6, 5, 0, 0, 0, 7, 6, 6, 0, 6, 4, 8, 0, 6, 0, 0, 0, 0, 0, 0, 0, 1].getD (idx r) 0

def t7 (r : S) : ℕ := [863, 356, 8, 120, 5, 11, 0, 36, 6, 6, 8, 6, 0, 0, 0, 8, 7, 7, 0, 7, 5, 11, 0, 7, 0, 0, 0, 0, 0, 0, 0, 1].getD (idx r) 0

def t8 (r : S) : ℕ := [1384, 529, 11, 165, 6, 14, 0, 45, 7, 7, 11, 7, 0, 0, 0, 9, 8, 8, 0, 8, 6, 14, 0, 8, 0, 0, 0, 0, 0, 0, 0, 1].getD (idx r) 0

def t9 (r : S) : ℕ := [2133, 760, 14, 220, 7, 18, 0, 55, 8, 8, 14, 8, 0, 0, 0, 10, 9, 9, 0, 9, 7, 18, 0, 9, 0, 0, 0, 0, 0, 0, 0, 1].getD (idx r) 0

def t10 (r : S) : ℕ := [3179, 1060, 18, 286, 8, 22, 0, 66, 9, 9, 18, 9, 0, 0, 0, 11, 10, 10, 0, 10, 8, 22, 0, 10, 0, 0, 0, 0, 0, 0, 0, 1].getD (idx r) 0

lemma W1 (r : S) : W 1 r = t1 r := by
  rw [W_succ]; simp only [W_zero]; revert r; decide +kernel

lemma W2 (r : S) : W 2 r = t2 r := by
  rw [W_succ]; simp only [W1]; revert r; decide +kernel

lemma W3 (r : S) : W 3 r = t3 r := by
  rw [W_succ]; simp only [W2]; revert r; decide +kernel

lemma W4 (r : S) : W 4 r = t4 r := by
  rw [W_succ]; simp only [W3]; revert r; decide +kernel

lemma W5 (r : S) : W 5 r = t5 r := by
  rw [W_succ]; simp only [W4]; revert r; decide +kernel

lemma W6 (r : S) : W 6 r = t6 r := by
  rw [W_succ]; simp only [W5]; revert r; decide +kernel

lemma W7 (r : S) : W 7 r = t7 r := by
  rw [W_succ]; simp only [W6]; revert r; decide +kernel

lemma W8 (r : S) : W 8 r = t8 r := by
  rw [W_succ]; simp only [W7]; revert r; decide +kernel

lemma W9 (r : S) : W 9 r = t9 r := by
  rw [W_succ]; simp only [W8]; revert r; decide +kernel

lemma W10 (r : S) : W 10 r = t10 r := by
  rw [W_succ]; simp only [W9]; revert r; decide +kernel

/-- The per-row relation. -/
lemma W_rec (k : ℕ) (r : S) :
    W (k + 10) r + 9 * W (k + 8) r + 9 * W (k + 5) r + W (k + 3) r =
      5 * W (k + 9) r + 5 * W (k + 7) r + 5 * W (k + 6) r + 5 * W (k + 4) r := by
  induction k generalizing r with
  | zero =>
    rw [W10, W9, W8, W7, W6, W5, W4, W3]
    revert r
    decide +kernel
  | succ k ih =>
    rw [W_succ (k + 10), W_succ (k + 9), W_succ (k + 8), W_succ (k + 7), W_succ (k + 6), W_succ (k + 5), W_succ (k + 4), W_succ (k + 3)]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    split_ifs
    · exact ih s
    · simp

lemma a_rec (k : ℕ) :
    a (k + 10) + 9 * a (k + 8) + 9 * a (k + 5) + a (k + 3) =
      5 * a (k + 9) + 5 * a (k + 7) + 5 * a (k + 6) + 5 * a (k + 4) := by
  rw [a_sum, a_sum, a_sum, a_sum, a_sum, a_sum, a_sum, a_sum]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun r _ => W_rec k r)

lemma a1 : a 1 = 48 := by rw [a_sum]; simp only [W1]; decide +kernel
lemma a2 : a 2 = 90 := by rw [a_sum]; simp only [W2]; decide +kernel
lemma a3 : a 3 = 178 := by rw [a_sum]; simp only [W3]; decide +kernel
lemma a4 : a 4 = 330 := by rw [a_sum]; simp only [W4]; decide +kernel
lemma a5 : a 5 = 571 := by rw [a_sum]; simp only [W5]; decide +kernel
lemma a6 : a 6 = 938 := by rw [a_sum]; simp only [W6]; decide +kernel
lemma a7 : a 7 = 1478 := by rw [a_sum]; simp only [W7]; decide +kernel
lemma a8 : a 8 = 2248 := by rw [a_sum]; simp only [W8]; decide +kernel
lemma a9 : a 9 = 3317 := by rw [a_sum]; simp only [W9]; decide +kernel

/-- The closed forms as one quasi-polynomial. -/
def Q (n : ℕ) : ℚ :=
  ((if n % 2 = 0 then (1920 : ℚ) else 1950) + 9776 * n + 3480 * n ^ 2 + 540 * n ^ 3 + 90 * n ^ 4 + 4 * n ^ 5) / 480

lemma Q_rec (m : ℕ) :
    Q (m + 10) + 9 * Q (m + 8) + 9 * Q (m + 5) + Q (m + 3) = 5 * Q (m + 9) + 5 * Q (m + 7) + 5 * Q (m + 6) + 5 * Q (m + 4) := by
  unfold Q
  rcases Nat.mod_two_eq_zero_or_one m with h | h
  · rw [if_pos (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), if_pos (by omega)]
    push_cast
    ring
  · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega)]
    push_cast
    ring

lemma a_eq_Q (n : ℕ) (hn : 3 ≤ n) : (a n : ℚ) = Q n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 10 with h7 | h7
    · interval_cases n
      · rw [a3]; norm_num [Q]
      · rw [a4]; norm_num [Q]
      · rw [a5]; norm_num [Q]
      · rw [a6]; norm_num [Q]
      · rw [a7]; norm_num [Q]
      · rw [a8]; norm_num [Q]
      · rw [a9]; norm_num [Q]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
      have h := a_rec m
      have h' : (a (m + 10) : ℚ) + 9 * a (m + 8) + 9 * a (m + 5) + a (m + 3) =
          5 * a (m + 9) + 5 * a (m + 7) + 5 * a (m + 6) + 5 * a (m + 4) := by exact_mod_cast h
      rw [ih (m + 8) (by omega) (by omega), ih (m + 5) (by omega) (by omega), ih (m + 3) (by omega) (by omega), ih (m + 9) (by omega) (by omega), ih (m + 7) (by omega) (by omega), ih (m + 6) (by omega) (by omega), ih (m + 4) (by omega) (by omega)] at h'
      have hq := Q_rec m
      linarith

/-- Barker's g.f.: Sum_{n >= 1} a(n) x^n * D = N. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - X) ^ 6 * (1 + X)) = X * (48 - 150 * X + 160 * X ^ 2 + 10 * X ^ 3 - 167 * X ^ 4 + 145 * X ^ 5 - 43 * X ^ 6 - 5 * X ^ 7 + 4 * X ^ 8) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - X) ^ 6 * (1 + X)) = A - C (5 : ℚ) * (A * X ^ 1) + C (9 : ℚ) * (A * X ^ 2) - C (5 : ℚ) * (A * X ^ 3) - C (5 : ℚ) * (A * X ^ 4) + C (9 : ℚ) * (A * X ^ 5) - C (5 : ℚ) * (A * X ^ 6) + A * X ^ 7 := by
    rw [show (C (5 : ℚ) : ℚ⟦X⟧) = 5 from map_ofNat C 5, show (C (9 : ℚ) : ℚ⟦X⟧) = 9 from map_ofNat C 9]
    ring
  have e2 : (X : ℚ⟦X⟧) * (48 - 150 * X + 160 * X ^ 2 + 10 * X ^ 3 - 167 * X ^ 4 + 145 * X ^ 5 - 43 * X ^ 6 - 5 * X ^ 7 + 4 * X ^ 8) = C (48 : ℚ) * X ^ 1 - C (150 : ℚ) * X ^ 2 + C (160 : ℚ) * X ^ 3 + C (10 : ℚ) * X ^ 4 - C (167 : ℚ) * X ^ 5 + C (145 : ℚ) * X ^ 6 - C (43 : ℚ) * X ^ 7 - C (5 : ℚ) * X ^ 8 + C (4 : ℚ) * X ^ 9 := by
    rw [show (C (4 : ℚ) : ℚ⟦X⟧) = 4 from map_ofNat C 4, show (C (5 : ℚ) : ℚ⟦X⟧) = 5 from map_ofNat C 5, show (C (10 : ℚ) : ℚ⟦X⟧) = 10 from map_ofNat C 10, show (C (43 : ℚ) : ℚ⟦X⟧) = 43 from map_ofNat C 43, show (C (48 : ℚ) : ℚ⟦X⟧) = 48 from map_ofNat C 48, show (C (145 : ℚ) : ℚ⟦X⟧) = 145 from map_ofNat C 145, show (C (150 : ℚ) : ℚ⟦X⟧) = 150 from map_ofNat C 150, show (C (160 : ℚ) : ℚ⟦X⟧) = 160 from map_ofNat C 160, show (C (167 : ℚ) : ℚ⟦X⟧) = 167 from map_ofNat C 167]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_C, hA,
    coeff_mk]
  rcases Nat.lt_or_ge n 10 with hn | hn
  · interval_cases n <;> simp [a1, a2, a3, a4, a5, a6, a7, a8, a9] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
    have h' : (a (m + 10) : ℚ) + 9 * a (m + 8) + 9 * a (m + 5) + a (m + 3) =
        5 * a (m + 9) + 5 * a (m + 7) + 5 * a (m + 6) + 5 * a (m + 4) := by exact_mod_cast a_rec m
    simp only [show m + 10 - 1 = m + 9 by omega, show 1 ≤ m + 10 by omega, show m + 10 - 2 = m + 8 by omega, show 2 ≤ m + 10 by omega, show m + 10 - 3 = m + 7 by omega, show 3 ≤ m + 10 by omega, show m + 10 - 4 = m + 6 by omega, show 4 ≤ m + 10 by omega, show m + 10 - 5 = m + 5 by omega, show 5 ≤ m + 10 by omega, show m + 10 - 6 = m + 4 by omega, show 6 ≤ m + 10 by omega, show m + 10 - 7 = m + 3 by omega, show 7 ≤ m + 10 by omega, show m + 10 - 8 = m + 2 by omega, show 8 ≤ m + 10 by omega, show m + 10 - 9 = m + 1 by omega, show 9 ≤ m + 10 by omega, show ¬ m + 10 = 0 by omega, show ¬ m + 10 = 1 by omega, show ¬ m + 10 = 2 by omega, show ¬ m + 10 = 3 by omega, show ¬ m + 10 = 4 by omega, show ¬ m + 10 = 5 by omega, show ¬ m + 10 = 6 by omega, show ¬ m + 10 = 7 by omega, show ¬ m + 10 = 8 by omega, show ¬ m + 10 = 9 by omega, show ¬ m + 9 = 0 by omega, show ¬ m + 8 = 0 by omega, show ¬ m + 7 = 0 by omega, show ¬ m + 6 = 0 by omega, show ¬ m + 5 = 0 by omega, show ¬ m + 4 = 0 by omega, show ¬ m + 3 = 0 by omega, show ¬ m + 2 = 0 by omega, show ¬ m + 1 = 0 by omega, if_true, if_false]
    linear_combination h'

/-- Barker's closed forms, for n > 2. -/
theorem closed_even : ∀ n : ℕ, 2 < n → n % 2 = 0 →
    (a n : ℚ) = (1920 + 9776 * n + 3480 * n ^ 2 + 540 * n ^ 3 + 90 * n ^ 4 + 4 * n ^ 5) / 480 := by
  intro n hn he
  rw [a_eq_Q n (by omega), Q, if_pos he]

theorem closed_odd : ∀ n : ℕ, 2 < n → n % 2 = 1 →
    (a n : ℚ) = (1950 + 9776 * n + 3480 * n ^ 2 + 540 * n ^ 3 + 90 * n ^ 4 + 4 * n ^ 5) / 480 := by
  intro n hn ho
  rw [a_eq_Q n (by omega), Q, if_neg (by omega)]

/-- All of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * ((1 - X) ^ 6 * (1 + X)) =
      X * (48 - 150 * X + 160 * X ^ 2 + 10 * X ^ 3 - 167 * X ^ 4 + 145 * X ^ 5 - 43 * X ^ 6 - 5 * X ^ 7 + 4 * X ^ 8) ∧
    (∀ n : ℕ, 2 < n → n % 2 = 0 →
      (a n : ℚ) = (1920 + 9776 * n + 3480 * n ^ 2 + 540 * n ^ 3 + 90 * n ^ 4 + 4 * n ^ 5) / 480) ∧
    (∀ n : ℕ, 2 < n → n % 2 = 1 →
      (a n : ℚ) = (1950 + 9776 * n + 3480 * n ^ 2 + 540 * n ^ 3 + 90 * n ^ 4 + 4 * n ^ 5) / 480) :=
  ⟨gf, closed_even, closed_odd⟩

end OMA.S_oeis_a204647

theorem OMA.solution : type_of% @OMA.S_oeis_a204647.main :=
  OMA.S_oeis_a204647.conjecture
