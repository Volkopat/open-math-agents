import OMAStatements.S_oeis_a204646

namespace OMA.S_oeis_a204646

open PowerSeries Finset


/-- A row. -/
abbrev S := Fin 4 → Fin 2

/-- Row s may follow row r. -/
def step (r s : S) : Prop :=
  ∀ j j' : Fin 4, j'.val = j.val + 1 →
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

/-- The index of a row r in the tables below: the binary number r 0 r 1 ... r 3. -/
def idx (r : S) : ℕ := 8 * (r 0).val + 4 * (r 1).val + 2 * (r 2).val + (r 3).val

def t1 (r : S) : ℕ := [5, 7, 2, 3, 1, 2, 0, 2, 1, 2, 1, 1, 0, 0, 0, 1].getD (idx r) 0

def t2 (r : S) : ℕ := [18, 15, 2, 6, 1, 2, 0, 3, 2, 2, 2, 2, 0, 0, 0, 1].getD (idx r) 0

def t3 (r : S) : ℕ := [43, 27, 2, 10, 2, 4, 0, 4, 3, 3, 2, 3, 0, 0, 0, 1].getD (idx r) 0

def t4 (r : S) : ℕ := [85, 44, 4, 15, 3, 5, 0, 5, 4, 4, 4, 4, 0, 0, 0, 1].getD (idx r) 0

def t5 (r : S) : ℕ := [150, 69, 5, 21, 4, 8, 0, 6, 5, 5, 5, 5, 0, 0, 0, 1].getD (idx r) 0

def t6 (r : S) : ℕ := [247, 102, 8, 28, 5, 10, 0, 7, 6, 6, 8, 6, 0, 0, 0, 1].getD (idx r) 0

def t7 (r : S) : ℕ := [385, 146, 10, 36, 6, 14, 0, 8, 7, 7, 10, 7, 0, 0, 0, 1].getD (idx r) 0

def t8 (r : S) : ℕ := [576, 201, 14, 45, 7, 17, 0, 9, 8, 8, 14, 8, 0, 0, 0, 1].getD (idx r) 0

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

/-- The per-row relation. -/
lemma W_rec (k : ℕ) (r : S) :
    W (k + 8) r + 5 * W (k + 6) r + 4 * W (k + 3) r =
      4 * W (k + 7) r + 5 * W (k + 4) r + W (k + 2) r := by
  induction k generalizing r with
  | zero =>
    rw [W8, W7, W6, W4, W3, W2]
    revert r
    decide +kernel
  | succ k ih =>
    rw [W_succ (k + 8), W_succ (k + 7), W_succ (k + 6), W_succ (k + 4), W_succ (k + 3), W_succ (k + 2)]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    split_ifs
    · exact ih s
    · simp

lemma a_rec (k : ℕ) :
    a (k + 8) + 5 * a (k + 6) + 4 * a (k + 3) =
      4 * a (k + 7) + 5 * a (k + 4) + a (k + 2) := by
  rw [a_sum, a_sum, a_sum, a_sum, a_sum, a_sum]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun r _ => W_rec k r)

lemma a1 : a 1 = 28 := by rw [a_sum]; simp only [W1]; decide +kernel
lemma a2 : a 2 = 56 := by rw [a_sum]; simp only [W2]; decide +kernel
lemma a3 : a 3 = 104 := by rw [a_sum]; simp only [W3]; decide +kernel
lemma a4 : a 4 = 178 := by rw [a_sum]; simp only [W4]; decide +kernel
lemma a5 : a 5 = 284 := by rw [a_sum]; simp only [W5]; decide +kernel
lemma a6 : a 6 = 434 := by rw [a_sum]; simp only [W6]; decide +kernel
lemma a7 : a 7 = 637 := by rw [a_sum]; simp only [W7]; decide +kernel

/-- The closed forms as one quasi-polynomial. -/
def Q (n : ℕ) : ℚ :=
  ((if n % 2 = 0 then (256 : ℚ) else 238) + 400 * n + 144 * n ^ 2 + 16 * n ^ 3 + 2 * n ^ 4) / 32

lemma Q_rec (m : ℕ) :
    Q (m + 8) + 5 * Q (m + 6) + 4 * Q (m + 3) = 4 * Q (m + 7) + 5 * Q (m + 4) + Q (m + 2) := by
  unfold Q
  rcases Nat.mod_two_eq_zero_or_one m with h | h
  · rw [if_pos (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), if_pos (by omega)]
    push_cast
    ring
  · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega)]
    push_cast
    ring

lemma a_eq_Q (n : ℕ) (hn : 2 ≤ n) : (a n : ℚ) = Q n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 8 with h7 | h7
    · interval_cases n
      · rw [a2]; norm_num [Q]
      · rw [a3]; norm_num [Q]
      · rw [a4]; norm_num [Q]
      · rw [a5]; norm_num [Q]
      · rw [a6]; norm_num [Q]
      · rw [a7]; norm_num [Q]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
      have h := a_rec m
      have h' : (a (m + 8) : ℚ) + 5 * a (m + 6) + 4 * a (m + 3) =
          4 * a (m + 7) + 5 * a (m + 4) + a (m + 2) := by exact_mod_cast h
      rw [ih (m + 6) (by omega) (by omega), ih (m + 3) (by omega) (by omega), ih (m + 7) (by omega) (by omega), ih (m + 4) (by omega) (by omega), ih (m + 2) (by omega) (by omega)] at h'
      have hq := Q_rec m
      linarith

/-- Barker's g.f.: Sum_{n >= 1} a(n) x^n * D = N. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - X) ^ 5 * (1 + X)) = X * (28 - 56 * X + 20 * X ^ 2 + 42 * X ^ 3 - 48 * X ^ 4 + 20 * X ^ 5 - 3 * X ^ 6) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - X) ^ 5 * (1 + X)) = A - C (4 : ℚ) * (A * X ^ 1) + C (5 : ℚ) * (A * X ^ 2) - C (5 : ℚ) * (A * X ^ 4) + C (4 : ℚ) * (A * X ^ 5) - A * X ^ 6 := by
    rw [show (C (4 : ℚ) : ℚ⟦X⟧) = 4 from map_ofNat C 4, show (C (5 : ℚ) : ℚ⟦X⟧) = 5 from map_ofNat C 5]
    ring
  have e2 : (X : ℚ⟦X⟧) * (28 - 56 * X + 20 * X ^ 2 + 42 * X ^ 3 - 48 * X ^ 4 + 20 * X ^ 5 - 3 * X ^ 6) = C (28 : ℚ) * X ^ 1 - C (56 : ℚ) * X ^ 2 + C (20 : ℚ) * X ^ 3 + C (42 : ℚ) * X ^ 4 - C (48 : ℚ) * X ^ 5 + C (20 : ℚ) * X ^ 6 - C (3 : ℚ) * X ^ 7 := by
    rw [show (C (3 : ℚ) : ℚ⟦X⟧) = 3 from map_ofNat C 3, show (C (20 : ℚ) : ℚ⟦X⟧) = 20 from map_ofNat C 20, show (C (28 : ℚ) : ℚ⟦X⟧) = 28 from map_ofNat C 28, show (C (42 : ℚ) : ℚ⟦X⟧) = 42 from map_ofNat C 42, show (C (48 : ℚ) : ℚ⟦X⟧) = 48 from map_ofNat C 48, show (C (56 : ℚ) : ℚ⟦X⟧) = 56 from map_ofNat C 56]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_C, hA,
    coeff_mk]
  rcases Nat.lt_or_ge n 8 with hn | hn
  · interval_cases n <;> simp [a1, a2, a3, a4, a5, a6, a7] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    have h' : (a (m + 8) : ℚ) + 5 * a (m + 6) + 4 * a (m + 3) =
        4 * a (m + 7) + 5 * a (m + 4) + a (m + 2) := by exact_mod_cast a_rec m
    simp only [show m + 8 - 1 = m + 7 by omega, show 1 ≤ m + 8 by omega, show m + 8 - 2 = m + 6 by omega, show 2 ≤ m + 8 by omega, show m + 8 - 3 = m + 5 by omega, show 3 ≤ m + 8 by omega, show m + 8 - 4 = m + 4 by omega, show 4 ≤ m + 8 by omega, show m + 8 - 5 = m + 3 by omega, show 5 ≤ m + 8 by omega, show m + 8 - 6 = m + 2 by omega, show 6 ≤ m + 8 by omega, show m + 8 - 7 = m + 1 by omega, show 7 ≤ m + 8 by omega, show ¬ m + 8 = 0 by omega, show ¬ m + 8 = 1 by omega, show ¬ m + 8 = 2 by omega, show ¬ m + 8 = 3 by omega, show ¬ m + 8 = 4 by omega, show ¬ m + 8 = 5 by omega, show ¬ m + 8 = 6 by omega, show ¬ m + 8 = 7 by omega, show ¬ m + 7 = 0 by omega, show ¬ m + 6 = 0 by omega, show ¬ m + 5 = 0 by omega, show ¬ m + 4 = 0 by omega, show ¬ m + 3 = 0 by omega, show ¬ m + 2 = 0 by omega, show ¬ m + 1 = 0 by omega, if_true, if_false]
    linear_combination h'

/-- Barker's closed forms, for n > 1. -/
theorem closed_even : ∀ n : ℕ, 1 < n → n % 2 = 0 →
    (a n : ℚ) = (256 + 400 * n + 144 * n ^ 2 + 16 * n ^ 3 + 2 * n ^ 4) / 32 := by
  intro n hn he
  rw [a_eq_Q n (by omega), Q, if_pos he]

theorem closed_odd : ∀ n : ℕ, 1 < n → n % 2 = 1 →
    (a n : ℚ) = (238 + 400 * n + 144 * n ^ 2 + 16 * n ^ 3 + 2 * n ^ 4) / 32 := by
  intro n hn ho
  rw [a_eq_Q n (by omega), Q, if_neg (by omega)]

/-- All of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * ((1 - X) ^ 5 * (1 + X)) =
      X * (28 - 56 * X + 20 * X ^ 2 + 42 * X ^ 3 - 48 * X ^ 4 + 20 * X ^ 5 - 3 * X ^ 6) ∧
    (∀ n : ℕ, 1 < n → n % 2 = 0 →
      (a n : ℚ) = (256 + 400 * n + 144 * n ^ 2 + 16 * n ^ 3 + 2 * n ^ 4) / 32) ∧
    (∀ n : ℕ, 1 < n → n % 2 = 1 →
      (a n : ℚ) = (238 + 400 * n + 144 * n ^ 2 + 16 * n ^ 3 + 2 * n ^ 4) / 32) :=
  ⟨gf, closed_even, closed_odd⟩

end OMA.S_oeis_a204646

theorem OMA.solution : type_of% @OMA.S_oeis_a204646.main :=
  OMA.S_oeis_a204646.conjecture
