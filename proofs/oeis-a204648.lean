import OMAStatements.S_oeis_a204648

namespace OMA.S_oeis_a204648

open PowerSeries Finset


/-- Row s may follow row r. -/
def rowStep (r s : Fin 6 → Fin 2) : Prop :=
  ∀ j j' : Fin 6, j'.val = j.val + 1 →
    (r j').val + (r j).val ≤ (s j').val + (s j).val ∧ (s j).val + (r j).val ≤ (s j').val + (r j').val

/-- A row, encoded as the number with binary digits r 0, r 1, ... (least significant first). -/
abbrev S := Fin (2 ^ 6)

/-- Binary digit j of an encoded row. -/
def bit (k : S) (j : ℕ) : ℕ := k.val / 2 ^ j % 2

/-- Row l may follow row k, on the encoded rows. -/
def step (k l : S) : Prop :=
  ∀ j : Fin 5, bit k (j.val + 1) + bit k j.val ≤ bit l (j.val + 1) + bit l j.val ∧
    bit l j.val + bit k j.val ≤ bit l (j.val + 1) + bit k (j.val + 1)

instance : DecidableRel step := fun k l => by unfold step; infer_instance

lemma bit_eq (k : S) (j : Fin 6) : ((finFunctionFinEquiv.symm k j : Fin 2) : ℕ) = bit k j.val := by
  rw [finFunctionFinEquiv_symm_apply_val]
  rfl

lemma step_iff (k l : S) :
    step k l ↔ rowStep (finFunctionFinEquiv.symm k) (finFunctionFinEquiv.symm l) := by
  unfold step rowStep
  constructor
  · intro h j j' hj
    rw [bit_eq, bit_eq, bit_eq, bit_eq, hj]
    exact h ⟨j.val, by omega⟩
  · intro h j
    have := h ⟨j.val, by omega⟩ ⟨j.val + 1, by omega⟩ rfl
    rw [bit_eq, bit_eq, bit_eq, bit_eq] at this
    exact this

/-- A valid sequence of rows. -/
def Valid {n : ℕ} (g : Fin n → S) : Prop :=
  ∀ i i' : Fin n, i'.val = i.val + 1 → step (g i) (g i')

instance {n : ℕ} : DecidablePred (@Valid n) := fun g => by unfold Valid; infer_instance

lemma a_eq (n : ℕ) : a n = ((univ : Finset (Fin (n + 1) → S)).filter Valid).card := by
  unfold a
  apply Finset.card_bij (fun f _ => fun i => finFunctionFinEquiv (f i))
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    intro i i' hii
    rw [step_iff, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact hf i i' hii
  · intro f _ f' _ h
    funext i
    exact finFunctionFinEquiv.injective (congrFun h i)
  · intro g hg
    refine ⟨fun i => finFunctionFinEquiv.symm (g i), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      intro i i' hii
      exact (step_iff _ _).1 (hg i i' hii)
    · funext i
      simp

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

def t1 (r : S) : ℕ := [7, 1, 1, 0, 2, 1, 0, 0, 3, 1, 1, 0, 0, 0, 0, 0, 4, 1, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 2, 2, 0, 4, 2, 0, 0, 6, 2, 2, 0, 0, 0, 0, 0, 5, 1, 1, 0, 2, 1, 0, 0, 4, 1, 1, 0, 3, 1, 2, 1].getD r.val 0

def t2 (r : S) : ℕ := [33, 2, 1, 0, 1, 1, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 6, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30, 2, 1, 0, 1, 1, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 15, 2, 1, 0, 1, 1, 0, 0, 10, 2, 1, 0, 6, 2, 3, 1].getD r.val 0

def t3 (r : S) : ℕ := [98, 3, 2, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 4, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 71, 3, 2, 0, 1, 1, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 35, 3, 2, 0, 1, 1, 0, 0, 20, 3, 2, 0, 10, 3, 4, 1].getD r.val 0

def t4 (r : S) : ℕ := [239, 4, 3, 0, 2, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 3, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 145, 4, 3, 0, 2, 2, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 70, 4, 3, 0, 2, 2, 0, 0, 35, 4, 3, 0, 15, 4, 5, 1].getD r.val 0

def t5 (r : S) : ℕ := [510, 5, 4, 0, 3, 3, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 274, 5, 4, 0, 3, 3, 0, 0, 5, 0, 5, 0, 0, 0, 0, 0, 126, 5, 4, 0, 3, 3, 0, 0, 56, 5, 4, 0, 21, 5, 6, 1].getD r.val 0

def t6 (r : S) : ℕ := [994, 6, 5, 0, 4, 4, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 5, 0, 0, 0, 5, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 487, 6, 5, 0, 4, 4, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 210, 6, 5, 0, 4, 4, 0, 0, 84, 6, 5, 0, 28, 6, 7, 1].getD r.val 0

def t7 (r : S) : ℕ := [1811, 7, 6, 0, 5, 5, 0, 0, 4, 0, 4, 0, 0, 0, 0, 0, 6, 0, 0, 0, 6, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 822, 7, 6, 0, 5, 5, 0, 0, 9, 0, 9, 0, 0, 0, 0, 0, 330, 7, 6, 0, 5, 5, 0, 0, 120, 7, 6, 0, 36, 7, 8, 1].getD r.val 0

def t8 (r : S) : ℕ := [3128, 8, 7, 0, 6, 6, 0, 0, 5, 0, 5, 0, 0, 0, 0, 0, 9, 0, 0, 0, 9, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1323, 8, 7, 0, 6, 6, 0, 0, 11, 0, 11, 0, 0, 0, 0, 0, 495, 8, 7, 0, 6, 6, 0, 0, 165, 8, 7, 0, 45, 8, 9, 1].getD r.val 0

def t9 (r : S) : ℕ := [5166, 9, 8, 0, 7, 7, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 11, 0, 0, 0, 11, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2047, 9, 8, 0, 7, 7, 0, 0, 15, 0, 15, 0, 0, 0, 0, 0, 715, 9, 8, 0, 7, 7, 0, 0, 220, 9, 8, 0, 55, 9, 10, 1].getD r.val 0

def t10 (r : S) : ℕ := [8214, 10, 9, 0, 8, 8, 0, 0, 7, 0, 7, 0, 0, 0, 0, 0, 15, 0, 0, 0, 15, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3059, 10, 9, 0, 8, 8, 0, 0, 18, 0, 18, 0, 0, 0, 0, 0, 1001, 10, 9, 0, 8, 8, 0, 0, 286, 10, 9, 0, 66, 10, 11, 1].getD r.val 0

def t11 (r : S) : ℕ := [12638, 11, 10, 0, 9, 9, 0, 0, 8, 0, 8, 0, 0, 0, 0, 0, 18, 0, 0, 0, 18, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4439, 11, 10, 0, 9, 9, 0, 0, 23, 0, 23, 0, 0, 0, 0, 0, 1365, 11, 10, 0, 9, 9, 0, 0, 364, 11, 10, 0, 78, 11, 12, 1].getD r.val 0

def t12 (r : S) : ℕ := [18897, 12, 11, 0, 10, 10, 0, 0, 9, 0, 9, 0, 0, 0, 0, 0, 23, 0, 0, 0, 23, 23, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6277, 12, 11, 0, 10, 10, 0, 0, 27, 0, 27, 0, 0, 0, 0, 0, 1820, 12, 11, 0, 10, 10, 0, 0, 455, 12, 11, 0, 91, 12, 13, 1].getD r.val 0

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

lemma W11 (r : S) : W 11 r = t11 r := by
  rw [W_succ]; simp only [W10]; revert r; decide +kernel

lemma W12 (r : S) : W 12 r = t12 r := by
  rw [W_succ]; simp only [W11]; revert r; decide +kernel

/-- The per-row relation. -/
lemma W_rec (k : ℕ) (r : S) :
    W (k + 12) r + 14 * W (k + 10) r + 14 * W (k + 7) r + 6 * W (k + 5) r =
      6 * W (k + 11) r + 14 * W (k + 9) r + 14 * W (k + 6) r + W (k + 4) r := by
  induction k generalizing r with
  | zero =>
    rw [W12, W11, W10, W9, W7, W6, W5, W4]
    revert r
    decide +kernel
  | succ k ih =>
    rw [W_succ (k + 12), W_succ (k + 11), W_succ (k + 10), W_succ (k + 9), W_succ (k + 7), W_succ (k + 6), W_succ (k + 5), W_succ (k + 4)]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    split_ifs
    · exact ih s
    · simp

lemma a_rec (k : ℕ) :
    a (k + 12) + 14 * a (k + 10) + 14 * a (k + 7) + 6 * a (k + 5) =
      6 * a (k + 11) + 14 * a (k + 9) + 14 * a (k + 6) + a (k + 4) := by
  rw [a_sum, a_sum, a_sum, a_sum, a_sum, a_sum, a_sum, a_sum]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun r _ => W_rec k r)

lemma a1 : a 1 = 80 := by rw [a_sum]; simp only [W1]; decide +kernel
lemma a2 : a 2 = 137 := by rw [a_sum]; simp only [W2]; decide +kernel
lemma a3 : a 3 = 284 := by rw [a_sum]; simp only [W3]; decide +kernel
lemma a4 : a 4 = 571 := by rw [a_sum]; simp only [W4]; decide +kernel
lemma a5 : a 5 = 1076 := by rw [a_sum]; simp only [W5]; decide +kernel
lemma a6 : a 6 = 1918 := by rw [a_sum]; simp only [W6]; decide +kernel
lemma a7 : a 7 = 3261 := by rw [a_sum]; simp only [W7]; decide +kernel
lemma a8 : a 8 = 5329 := by rw [a_sum]; simp only [W8]; decide +kernel
lemma a9 : a 9 = 8408 := by rw [a_sum]; simp only [W9]; decide +kernel
lemma a10 : a 10 = 12867 := by rw [a_sum]; simp only [W10]; decide +kernel
lemma a11 : a 11 = 19162 := by rw [a_sum]; simp only [W11]; decide +kernel

/-- The closed forms as one quasi-polynomial. -/
def Q (n : ℕ) : ℚ :=
  ((if n % 2 = 0 then (-10080 : ℚ) else -10890) + 43776 * n + 15308 * n ^ 2 + 2970 * n ^ 3 + 620 * n ^ 4 + 54 * n ^ 5 + 2 * n ^ 6) / 1440

lemma Q_rec (m : ℕ) :
    Q (m + 12) + 14 * Q (m + 10) + 14 * Q (m + 7) + 6 * Q (m + 5) = 6 * Q (m + 11) + 14 * Q (m + 9) + 14 * Q (m + 6) + Q (m + 4) := by
  unfold Q
  rcases Nat.mod_two_eq_zero_or_one m with h | h
  · rw [if_pos (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), if_pos (by omega)]
    push_cast
    ring
  · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega)]
    push_cast
    ring

lemma a_eq_Q (n : ℕ) (hn : 4 ≤ n) : (a n : ℚ) = Q n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 12 with h7 | h7
    · interval_cases n
      · rw [a4]; norm_num [Q]
      · rw [a5]; norm_num [Q]
      · rw [a6]; norm_num [Q]
      · rw [a7]; norm_num [Q]
      · rw [a8]; norm_num [Q]
      · rw [a9]; norm_num [Q]
      · rw [a10]; norm_num [Q]
      · rw [a11]; norm_num [Q]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
      have h := a_rec m
      have h' : (a (m + 12) : ℚ) + 14 * a (m + 10) + 14 * a (m + 7) + 6 * a (m + 5) =
          6 * a (m + 11) + 14 * a (m + 9) + 14 * a (m + 6) + a (m + 4) := by exact_mod_cast h
      rw [ih (m + 10) (by omega) (by omega), ih (m + 7) (by omega) (by omega), ih (m + 5) (by omega) (by omega), ih (m + 11) (by omega) (by omega), ih (m + 9) (by omega) (by omega), ih (m + 6) (by omega) (by omega), ih (m + 4) (by omega) (by omega)] at h'
      have hq := Q_rec m
      linarith

/-- Controls: the entry's data a(1..26). -/
theorem controls : a 1 = 80 ∧ a 2 = 137 ∧ a 3 = 284 ∧ a 4 = 571 ∧ a 5 = 1076 ∧ a 6 = 1918 ∧ a 7 = 3261 ∧ a 8 = 5329 ∧ a 9 = 8408 ∧ a 10 = 12867 ∧ a 11 = 19162 ∧ a 12 = 27859 ∧ a 13 = 39640 ∧ a 14 = 55328 ∧ a 15 = 75895 ∧ a 16 = 102489 ∧ a 17 = 136444 ∧ a 18 = 179309 ∧ a 19 = 232860 ∧ a 20 = 299131 ∧ a 21 = 380428 ∧ a 22 = 479362 ∧ a 23 = 598865 ∧ a 24 = 742225 ∧ a 25 = 913104 ∧ a 26 = 1115575 := by
  have c1 := a1
  have c2 := a2
  have c3 := a3
  have c4 := a4
  have c5 := a5
  have c6 := a6
  have c7 := a7
  have c8 := a8
  have c9 := a9
  have c10 := a10
  have c11 := a11
  have c12 : a 12 = 27859 := by
    have h := a_eq_Q 12 (by norm_num); generalize a 12 = x at h ⊢
    norm_num [Q] at h; exact_mod_cast h
  have c13 : a 13 = 39640 := by
    have h := a_eq_Q 13 (by norm_num); generalize a 13 = x at h ⊢
    norm_num [Q] at h; exact_mod_cast h
  have c14 : a 14 = 55328 := by
    have h := a_eq_Q 14 (by norm_num); generalize a 14 = x at h ⊢
    norm_num [Q] at h; exact_mod_cast h
  have c15 : a 15 = 75895 := by
    have h := a_eq_Q 15 (by norm_num); generalize a 15 = x at h ⊢
    norm_num [Q] at h; exact_mod_cast h
  have c16 : a 16 = 102489 := by
    have h := a_eq_Q 16 (by norm_num); generalize a 16 = x at h ⊢
    norm_num [Q] at h; exact_mod_cast h
  have c17 : a 17 = 136444 := by
    have h := a_eq_Q 17 (by norm_num); generalize a 17 = x at h ⊢
    norm_num [Q] at h; exact_mod_cast h
  have c18 : a 18 = 179309 := by
    have h := a_eq_Q 18 (by norm_num); generalize a 18 = x at h ⊢
    norm_num [Q] at h; exact_mod_cast h
  have c19 : a 19 = 232860 := by
    have h := a_eq_Q 19 (by norm_num); generalize a 19 = x at h ⊢
    norm_num [Q] at h; exact_mod_cast h
  have c20 : a 20 = 299131 := by
    have h := a_eq_Q 20 (by norm_num); generalize a 20 = x at h ⊢
    norm_num [Q] at h; exact_mod_cast h
  have c21 : a 21 = 380428 := by
    have h := a_eq_Q 21 (by norm_num); generalize a 21 = x at h ⊢
    norm_num [Q] at h; exact_mod_cast h
  have c22 : a 22 = 479362 := by
    have h := a_eq_Q 22 (by norm_num); generalize a 22 = x at h ⊢
    norm_num [Q] at h; exact_mod_cast h
  have c23 : a 23 = 598865 := by
    have h := a_eq_Q 23 (by norm_num); generalize a 23 = x at h ⊢
    norm_num [Q] at h; exact_mod_cast h
  have c24 : a 24 = 742225 := by
    have h := a_eq_Q 24 (by norm_num); generalize a 24 = x at h ⊢
    norm_num [Q] at h; exact_mod_cast h
  have c25 : a 25 = 913104 := by
    have h := a_eq_Q 25 (by norm_num); generalize a 25 = x at h ⊢
    norm_num [Q] at h; exact_mod_cast h
  have c26 : a 26 = 1115575 := by
    have h := a_eq_Q 26 (by norm_num); generalize a 26 = x at h ⊢
    norm_num [Q] at h; exact_mod_cast h
  exact ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26⟩

/-- Barker's g.f.: Sum_{n >= 1} a(n) x^n * D = N. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - X) ^ 7 * (1 + X)) = X * (80 - 343 * X + 582 * X ^ 2 - 335 * X ^ 3 - 292 * X ^ 4 + 600 * X ^ 5 - 379 * X ^ 6 + 89 * X ^ 7 - 4 * X ^ 8 + 8 * X ^ 9 - 4 * X ^ 10) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - X) ^ 7 * (1 + X)) = A - C (6 : ℚ) * (A * X ^ 1) + C (14 : ℚ) * (A * X ^ 2) - C (14 : ℚ) * (A * X ^ 3) + C (14 : ℚ) * (A * X ^ 5) - C (14 : ℚ) * (A * X ^ 6) + C (6 : ℚ) * (A * X ^ 7) - A * X ^ 8 := by
    rw [show (C (6 : ℚ) : ℚ⟦X⟧) = 6 from map_ofNat C 6, show (C (14 : ℚ) : ℚ⟦X⟧) = 14 from map_ofNat C 14]
    ring
  have e2 : (X : ℚ⟦X⟧) * (80 - 343 * X + 582 * X ^ 2 - 335 * X ^ 3 - 292 * X ^ 4 + 600 * X ^ 5 - 379 * X ^ 6 + 89 * X ^ 7 - 4 * X ^ 8 + 8 * X ^ 9 - 4 * X ^ 10) = C (80 : ℚ) * X ^ 1 - C (343 : ℚ) * X ^ 2 + C (582 : ℚ) * X ^ 3 - C (335 : ℚ) * X ^ 4 - C (292 : ℚ) * X ^ 5 + C (600 : ℚ) * X ^ 6 - C (379 : ℚ) * X ^ 7 + C (89 : ℚ) * X ^ 8 - C (4 : ℚ) * X ^ 9 + C (8 : ℚ) * X ^ 10 - C (4 : ℚ) * X ^ 11 := by
    rw [show (C (4 : ℚ) : ℚ⟦X⟧) = 4 from map_ofNat C 4, show (C (8 : ℚ) : ℚ⟦X⟧) = 8 from map_ofNat C 8, show (C (80 : ℚ) : ℚ⟦X⟧) = 80 from map_ofNat C 80, show (C (89 : ℚ) : ℚ⟦X⟧) = 89 from map_ofNat C 89, show (C (292 : ℚ) : ℚ⟦X⟧) = 292 from map_ofNat C 292, show (C (335 : ℚ) : ℚ⟦X⟧) = 335 from map_ofNat C 335, show (C (343 : ℚ) : ℚ⟦X⟧) = 343 from map_ofNat C 343, show (C (379 : ℚ) : ℚ⟦X⟧) = 379 from map_ofNat C 379, show (C (582 : ℚ) : ℚ⟦X⟧) = 582 from map_ofNat C 582, show (C (600 : ℚ) : ℚ⟦X⟧) = 600 from map_ofNat C 600]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_C, hA,
    coeff_mk]
  rcases Nat.lt_or_ge n 12 with hn | hn
  · interval_cases n <;> simp [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
    have h' : (a (m + 12) : ℚ) + 14 * a (m + 10) + 14 * a (m + 7) + 6 * a (m + 5) =
        6 * a (m + 11) + 14 * a (m + 9) + 14 * a (m + 6) + a (m + 4) := by exact_mod_cast a_rec m
    simp only [show m + 12 - 1 = m + 11 by omega, show 1 ≤ m + 12 by omega, show m + 12 - 2 = m + 10 by omega, show 2 ≤ m + 12 by omega, show m + 12 - 3 = m + 9 by omega, show 3 ≤ m + 12 by omega, show m + 12 - 4 = m + 8 by omega, show 4 ≤ m + 12 by omega, show m + 12 - 5 = m + 7 by omega, show 5 ≤ m + 12 by omega, show m + 12 - 6 = m + 6 by omega, show 6 ≤ m + 12 by omega, show m + 12 - 7 = m + 5 by omega, show 7 ≤ m + 12 by omega, show m + 12 - 8 = m + 4 by omega, show 8 ≤ m + 12 by omega, show m + 12 - 9 = m + 3 by omega, show 9 ≤ m + 12 by omega, show m + 12 - 10 = m + 2 by omega, show 10 ≤ m + 12 by omega, show m + 12 - 11 = m + 1 by omega, show 11 ≤ m + 12 by omega, show ¬ m + 12 = 0 by omega, show ¬ m + 12 = 1 by omega, show ¬ m + 12 = 2 by omega, show ¬ m + 12 = 3 by omega, show ¬ m + 12 = 4 by omega, show ¬ m + 12 = 5 by omega, show ¬ m + 12 = 6 by omega, show ¬ m + 12 = 7 by omega, show ¬ m + 12 = 8 by omega, show ¬ m + 12 = 9 by omega, show ¬ m + 12 = 10 by omega, show ¬ m + 12 = 11 by omega, show ¬ m + 11 = 0 by omega, show ¬ m + 10 = 0 by omega, show ¬ m + 9 = 0 by omega, show ¬ m + 8 = 0 by omega, show ¬ m + 7 = 0 by omega, show ¬ m + 6 = 0 by omega, show ¬ m + 5 = 0 by omega, show ¬ m + 4 = 0 by omega, show ¬ m + 3 = 0 by omega, show ¬ m + 2 = 0 by omega, show ¬ m + 1 = 0 by omega, if_true, if_false]
    linear_combination h'

/-- Barker's closed forms, for n > 3. -/
theorem closed_even : ∀ n : ℕ, 3 < n → n % 2 = 0 →
    (a n : ℚ) = (-10080 + 43776 * n + 15308 * n ^ 2 + 2970 * n ^ 3 + 620 * n ^ 4 + 54 * n ^ 5 + 2 * n ^ 6) / 1440 := by
  intro n hn he
  rw [a_eq_Q n (by omega), Q, if_pos he]

theorem closed_odd : ∀ n : ℕ, 3 < n → n % 2 = 1 →
    (a n : ℚ) = (-10890 + 43776 * n + 15308 * n ^ 2 + 2970 * n ^ 3 + 620 * n ^ 4 + 54 * n ^ 5 + 2 * n ^ 6) / 1440 := by
  intro n hn ho
  rw [a_eq_Q n (by omega), Q, if_neg (by omega)]

/-- All of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * ((1 - X) ^ 7 * (1 + X)) =
      X * (80 - 343 * X + 582 * X ^ 2 - 335 * X ^ 3 - 292 * X ^ 4 + 600 * X ^ 5 - 379 * X ^ 6 + 89 * X ^ 7 - 4 * X ^ 8 + 8 * X ^ 9 - 4 * X ^ 10) ∧
    (∀ n : ℕ, 3 < n → n % 2 = 0 →
      (a n : ℚ) = (-10080 + 43776 * n + 15308 * n ^ 2 + 2970 * n ^ 3 + 620 * n ^ 4 + 54 * n ^ 5 + 2 * n ^ 6) / 1440) ∧
    (∀ n : ℕ, 3 < n → n % 2 = 1 →
      (a n : ℚ) = (-10890 + 43776 * n + 15308 * n ^ 2 + 2970 * n ^ 3 + 620 * n ^ 4 + 54 * n ^ 5 + 2 * n ^ 6) / 1440) :=
  ⟨gf, closed_even, closed_odd⟩

end OMA.S_oeis_a204648

theorem OMA.solution : type_of% @OMA.S_oeis_a204648.main :=
  OMA.S_oeis_a204648.conjecture
