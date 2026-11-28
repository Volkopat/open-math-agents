import OMAStatements.S_oeis_a208316

open OMA.S_oeis_a208316 PowerSeries

namespace A208316Proof

-- A row of the array: one letter of the row by row scan.
abbrev Row := Fin 2 → Fin 3

-- Contribution of the row above (none for the top row) to the count at column j:
-- the upward and the left-upward diagonal neighbors.
def upInd (p : Option Row) (r : Row) (j : Fin 2) : ℕ :=
  match p with
  | none => 0
  | some q => (if q j = r j then 1 else 0) +
      (if ∃ j' : Fin 2, j'.val + 1 = j.val ∧ q j' = r j then 1 else 0)

def rowLeft (r : Row) (j : Fin 2) : Prop := ∃ j' : Fin 2, j'.val + 1 = j.val ∧ r j' = r j

instance (r : Row) (j : Fin 2) : Decidable (rowLeft r j) := by unfold rowLeft; infer_instance

-- A new row r below the row p, when the values below t have been seen already.
def rowOK (t : ℕ) (p : Option Row) (r : Row) : Prop :=
  (∀ j, ∀ v < r j, v.val < t ∨ ∃ j' < j, r j' = v) ∧
  (∀ j, (if rowLeft r j then 1 else 0) + upInd p r j ≤ 2)

instance (t : ℕ) (p : Option Row) (r : Row) : Decidable (rowOK t p r) := by
  unfold rowOK; infer_instance

-- The number of values seen after the row r.
def newT (t : ℕ) (r : Row) : ℕ := max t (Finset.univ.sup fun j => (r j).val + 1)

-- The conditions on a block of rows below the row p, the values below t being seen already.
def ExtOK (t : ℕ) (p : Option Row) {n : ℕ} (A : Fin n → Row) : Prop :=
  (∀ i j, ∀ v < A i j, v.val < t ∨ ∃ i' j', (i' < i ∨ (i' = i ∧ j' < j)) ∧ A i' j' = v) ∧
  (∀ i j, (if LeftEq A i j then 1 else 0) +
    (if i.val = 0 then upInd p (A i) j else
      (if UpEq A i j then 1 else 0) + (if UpLeftEq A i j then 1 else 0)) ≤ 2)

instance (t : ℕ) (p : Option Row) {n : ℕ} (A : Fin n → Row) : Decidable (ExtOK t p A) := by
  unfold ExtOK; infer_instance

theorem valid_iff {n : ℕ} (A : Fin n → Row) : Valid A ↔ ExtOK 0 none A := by
  have h : ∀ i j, (if i.val = 0 then upInd none (A i) j else
      (if UpEq A i j then 1 else 0) + (if UpLeftEq A i j then 1 else 0)) =
      (if UpEq A i j then 1 else 0) + (if UpLeftEq A i j then 1 else 0) := by
    intro i j
    by_cases hi : i.val = 0
    · have h1 : ¬ UpEq A i j := by rintro ⟨i', hi', _⟩; omega
      have h2 : ¬ UpLeftEq A i j := by rintro ⟨i', j', hi', _⟩; omega
      simp [hi, h1, h2, upInd]
    · simp [hi]
  simp only [Valid, ExtOK, NewValuesInOrder, numEqNeighbors, h, add_assoc]
  simp

theorem nv_cons (t : ℕ) {n : ℕ} (r : Row) (B : Fin n → Row) :
    (∀ (i : Fin (n + 1)) j, ∀ v < (Fin.cons r B : Fin (n + 1) → Row) i j, v.val < t ∨
      ∃ i' j', (i' < i ∨ (i' = i ∧ j' < j)) ∧ (Fin.cons r B : Fin (n + 1) → Row) i' j' = v) ↔
    (∀ j, ∀ v < r j, v.val < t ∨ ∃ j' < j, r j' = v) ∧
    (∀ i j, ∀ v < B i j, (v.val < t ∨ ∃ j', r j' = v) ∨
      ∃ i' j', (i' < i ∨ (i' = i ∧ j' < j)) ∧ B i' j' = v) := by
  simp only [Fin.forall_fin_succ (n := n), Fin.exists_fin_succ (n := n), Fin.cons_zero,
    Fin.cons_succ]
  simp [Fin.succ_lt_succ_iff, Fin.succ_pos, or_assoc]

theorem leftEq_cons_zero {n : ℕ} (r : Row) (B : Fin n → Row) (j : Fin 2) :
    LeftEq (Fin.cons r B : Fin (n + 1) → Row) 0 j ↔ rowLeft r j := by
  simp [LeftEq, rowLeft]

theorem leftEq_cons_succ {n : ℕ} (r : Row) (B : Fin n → Row) (i : Fin n) (j : Fin 2) :
    LeftEq (Fin.cons r B : Fin (n + 1) → Row) i.succ j ↔ LeftEq B i j := by
  simp [LeftEq]

theorem upEq_cons_succ {n : ℕ} (r : Row) (B : Fin n → Row) (i : Fin n) (j : Fin 2) :
    (if UpEq (Fin.cons r B : Fin (n + 1) → Row) i.succ j then 1 else 0) +
      (if UpLeftEq (Fin.cons r B : Fin (n + 1) → Row) i.succ j then 1 else 0) =
      (if i.val = 0 then upInd (some r) (B i) j else
        (if UpEq B i j then 1 else 0) + (if UpLeftEq B i j then 1 else 0)) := by
  have h : UpEq (Fin.cons r B : Fin (n + 1) → Row) i.succ j ↔
      (i.val = 0 ∧ r j = B i j) ∨ UpEq B i j := by
    simp only [UpEq, Fin.exists_fin_succ (n := n), Fin.cons_zero, Fin.cons_succ, Fin.val_zero,
      Fin.val_succ]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨i', h1, h2⟩)
      · exact Or.inl ⟨by omega, h2⟩
      · exact Or.inr ⟨i', by omega, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨i', h1, h2⟩)
      · exact Or.inl ⟨by omega, h2⟩
      · exact Or.inr ⟨i', by omega, h2⟩
  have h' : UpLeftEq (Fin.cons r B : Fin (n + 1) → Row) i.succ j ↔
      (i.val = 0 ∧ ∃ j' : Fin 2, j'.val + 1 = j.val ∧ r j' = B i j) ∨ UpLeftEq B i j := by
    simp only [UpLeftEq, Fin.exists_fin_succ (n := n), Fin.cons_zero, Fin.cons_succ,
      Fin.val_zero, Fin.val_succ]
    constructor
    · rintro (⟨j', h1, h2, h3⟩ | ⟨i', j', h1, h2, h3⟩)
      · exact Or.inl ⟨by omega, j', h2, h3⟩
      · exact Or.inr ⟨i', j', by omega, h2, h3⟩
    · rintro (⟨h1, j', h2, h3⟩ | ⟨i', j', h1, h2, h3⟩)
      · exact Or.inl ⟨j', by omega, h2, h3⟩
      · exact Or.inr ⟨i', j', by omega, h2, h3⟩
  by_cases hi : i.val = 0
  · have h1 : ¬ UpEq B i j := by rintro ⟨i', hi', _⟩; omega
    have h2 : ¬ UpLeftEq B i j := by rintro ⟨i', j', hi', _⟩; omega
    simp [h, h', hi, h1, h2, upInd]
  · simp [h, h', hi]

theorem nb_cons (p : Option Row) {n : ℕ} (r : Row) (B : Fin n → Row) :
    (∀ (i : Fin (n + 1)) j, (if LeftEq (Fin.cons r B : Fin (n + 1) → Row) i j then 1 else 0) +
      (if i.val = 0 then upInd p ((Fin.cons r B : Fin (n + 1) → Row) i) j
        else (if UpEq (Fin.cons r B : Fin (n + 1) → Row) i j then 1 else 0) +
          (if UpLeftEq (Fin.cons r B : Fin (n + 1) → Row) i j then 1 else 0)) ≤ 2) ↔
    (∀ j, (if rowLeft r j then 1 else 0) + upInd p r j ≤ 2) ∧
    (∀ i j, (if LeftEq B i j then 1 else 0) +
      (if i.val = 0 then upInd (some r) (B i) j else
        (if UpEq B i j then 1 else 0) + (if UpLeftEq B i j then 1 else 0)) ≤ 2) := by
  rw [Fin.forall_fin_succ (n := n)]
  simp only [leftEq_cons_zero, leftEq_cons_succ, Fin.cons_zero, Fin.val_zero, if_true,
    Fin.val_succ, Nat.add_one_ne_zero, if_false, upEq_cons_succ]

theorem newT_spec (t : ℕ) (r : Row) (h : ∀ j, ∀ v < r j, v.val < t ∨ ∃ j' < j, r j' = v)
    (v : Fin 3) : (v.val < t ∨ ∃ j', r j' = v) ↔ v.val < newT t r := by
  by_cases ht : 3 ≤ t
  · have : t ≤ newT t r := le_max_left _ _
    have := v.isLt
    exact ⟨fun _ => by omega, fun _ => Or.inl (by omega)⟩
  · have key : ∀ t : Fin 3, ∀ r : Row, (∀ j, ∀ v < r j, v.val < t.val ∨ ∃ j' < j, r j' = v) →
        ∀ v : Fin 3, ((v.val < t.val ∨ ∃ j', r j' = v) ↔ v.val < newT t.val r) := by
      decide +kernel
    exact key ⟨t, by omega⟩ r h v

theorem ext_cons (t : ℕ) (p : Option Row) {n : ℕ} (r : Row) (B : Fin n → Row) :
    ExtOK t p (Fin.cons r B : Fin (n + 1) → Row) ↔ rowOK t p r ∧ ExtOK (newT t r) (some r) B := by
  unfold ExtOK
  rw [nv_cons, nb_cons]
  unfold rowOK
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨⟨h1, h3⟩, fun i j v hv => ?_, h4⟩
    rcases h2 i j v hv with h | h
    · exact Or.inl ((newT_spec t r h1 v).1 h)
    · exact Or.inr h
  · rintro ⟨⟨h1, h3⟩, h2, h4⟩
    refine ⟨⟨h1, fun i j v hv => ?_⟩, h3, h4⟩
    rcases h2 i j v hv with h | h
    · exact Or.inl ((newT_spec t r h1 v).2 h)
    · exact Or.inr h

def F (t : ℕ) (p : Option Row) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun A : Fin n → Row => ExtOK t p A).card

theorem F_succ (t : ℕ) (p : Option Row) (n : ℕ) :
    F t p (n + 1) = ∑ r : Row, if rowOK t p r then F (newT t r) (some r) n else 0 := by
  rw [F, Finset.card_filter, ← (Fin.consEquiv fun _ => Row).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, ext_cons]
  by_cases h : rowOK t p r
  · rw [if_pos h, F, Finset.card_filter]
    exact Finset.sum_congr rfl fun B _ => by simp [h]
  · simp [h]

def cnt : ℕ → ℕ → Option Row → ℕ
  | 0, _, _ => 1
  | n + 1, t, p => ∑ r : Row, if rowOK t p r then cnt n (newT t r) (some r) else 0

theorem cnt_succ (n t : ℕ) (p : Option Row) :
    cnt (n + 1) t p = ∑ r : Row, if rowOK t p r then cnt n (newT t r) (some r) else 0 := by
  rw [cnt]

theorem F_eq (n : ℕ) : ∀ t p, F t p n = cnt n t p := by
  induction n with
  | zero =>
    intro t p
    rw [F, Finset.filter_true_of_mem (fun A _ => ⟨fun i => i.elim0, fun i => i.elim0⟩)]
    simp [cnt]
  | succ n ih =>
    intro t p
    rw [F_succ, cnt_succ]
    simp only [ih]

theorem a_eq (n : ℕ) : a n = cnt n 0 none := by
  rw [← F_eq, a, F, Finset.filter_congr (fun A _ => valid_iff A)]

def W (n t : ℕ) (p : Option Row) : ℤ :=
  (cnt (n + 2) t p : ℤ) - 8 * cnt (n + 1) t p - 6 * cnt n t p

theorem W_succ (n t : ℕ) (p : Option Row) :
    W (n + 1) t p = ∑ r : Row, if rowOK t p r then W n (newT t r) (some r) else 0 := by
  simp only [W, show n + 1 + 2 = n + 2 + 1 by ring]
  rw [cnt_succ (n + 2) t p, cnt_succ (n + 1) t p, cnt_succ n t p]
  push_cast [Nat.cast_sum, Nat.cast_ite]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases h : rowOK t p r
  · simp only [if_pos h]
  · simp only [if_neg h]; ring

theorem W_base : ∀ t : Fin 3, ∀ q : Row, W 2 (t.val + 1) (some q) = 0 := by
  decide +kernel

theorem newT_ge (t : ℕ) (r : Row) : 1 ≤ newT t r :=
  le_trans (Finset.le_sup (f := fun j => (r j).val + 1) (Finset.mem_univ 0) |> le_trans
    (Nat.le_add_left 1 _)) (le_max_right _ _)

theorem newT_le (t : ℕ) (r : Row) (ht : t ≤ 3) : newT t r ≤ 3 :=
  max_le ht (Finset.sup_le fun j _ => (r j).isLt)

theorem W_zero (n : ℕ) : ∀ t q, 1 ≤ t → t ≤ 3 → W (n + 2) t (some q) = 0 := by
  induction n with
  | zero =>
    intro t q h1 h2
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    exact W_base ⟨s, by omega⟩ q
  | succ n ih =>
    intro t q h1 h2
    rw [show n + 1 + 2 = n + 2 + 1 by ring, W_succ]
    refine Finset.sum_eq_zero fun r _ => ?_
    split_ifs
    · exact ih _ _ (newT_ge t r) (newT_le t r h2)
    · rfl

theorem a1 : a 1 = 2 := by rw [a_eq]; decide +kernel
theorem a2 : a 2 = 13 := by rw [a_eq]; decide +kernel
theorem a3 : a 3 = 113 := by rw [a_eq]; decide +kernel
theorem a4 : a 4 = 982 := by rw [a_eq]; decide +kernel

theorem a_rec (n : ℕ) : (a (n + 4) : ℤ) = 8 * a (n + 3) + 6 * a (n + 2) := by
  rcases n with _ | n
  · rw [a2, a3, a4]; norm_num
  have h : W (n + 3) 0 none = 0 := by
    rw [W_succ]
    refine Finset.sum_eq_zero fun r _ => ?_
    split_ifs
    · exact W_zero n _ _ (newT_ge 0 r) (newT_le 0 r (by norm_num))
    · rfl
  simp only [W] at h
  rw [a_eq, a_eq, a_eq]
  rw [show n + 1 + 4 = n + 3 + 2 by ring, show n + 1 + 3 = n + 3 + 1 by ring,
    show n + 1 + 2 = n + 3 by ring]
  linarith

theorem gf :
    (1 - 8 * X - 6 * X ^ 2) * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (X * (2 - 3 * X - 3 * X ^ 2) : PowerSeries ℤ) := by
  set s : PowerSeries ℤ := mk (fun n => if n = 0 then 0 else (a n : ℤ)) with hs
  have hd : (1 - 8 * X - 6 * X ^ 2) * s =
      s - (s * C (8 : ℤ)) * X ^ 1 - (s * C (6 : ℤ)) * X ^ 2 := by
    simp only [pow_one, map_ofNat]
    ring
  have hn : (X * (2 - 3 * X - 3 * X ^ 2) : PowerSeries ℤ) =
      C (2 : ℤ) * X ^ 1 - C (3 : ℤ) * X ^ 2 - C (3 : ℤ) * X ^ 3 := by
    simp only [pow_one, map_ofNat]
    ring
  rw [hd, hn]
  ext n
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_mul_C, coeff_C, hs, coeff_mk]
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ 4 ≤ n) with h | h | h | h | h
  · subst h; simp
  · subst h; simp [a1]
  · subst h; simp [a1, a2]
  · subst h; simp [a1, a2, a3]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have := a_rec m
    simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega]
    simp
    omega

noncomputable def R (n : ℕ) : ℝ :=
  ((4 - Real.sqrt 22) ^ n * (-5 + Real.sqrt 22) +
    (4 + Real.sqrt 22) ^ n * (5 + Real.sqrt 22)) / (12 * Real.sqrt 22)

theorem root_step (x : ℝ) (h : x ^ 2 = 8 * x + 6) (j : ℕ) :
    x ^ (j + 2) = 8 * x ^ (j + 1) + 6 * x ^ j := by
  linear_combination x ^ j * h

theorem R_rec (j : ℕ) : R (j + 2) = 8 * R (j + 1) + 6 * R j := by
  have hs : Real.sqrt 22 ^ 2 = 22 := Real.sq_sqrt (by norm_num)
  have h1 := root_step (4 - Real.sqrt 22) (by linear_combination hs) j
  have h2 := root_step (4 + Real.sqrt 22) (by linear_combination hs) j
  unfold R
  rw [h1, h2]
  ring

theorem closed (m : ℕ) : (a (m + 2) : ℝ) = R (m + 2) ∧ (a (m + 3) : ℝ) = R (m + 3) := by
  have hs : Real.sqrt 22 ^ 2 = 22 := Real.sq_sqrt (by norm_num)
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [a2, R, eq_div_iff (by positivity)]; push_cast
      linear_combination (-(2 * Real.sqrt 22)) * hs
    · rw [a3, R, eq_div_iff (by positivity)]; push_cast
      linear_combination (-(34 * Real.sqrt 22)) * hs
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨h2, ?_⟩
    have hr : (a (m + 4) : ℝ) = 8 * (a (m + 3) : ℝ) + 6 * (a (m + 2) : ℝ) := by
      exact_mod_cast a_rec m
    rw [show m + 1 + 3 = m + 4 by ring, hr, show m + 4 = (m + 2) + 2 by ring, R_rec,
      show m + 2 + 1 = m + 3 by ring, h1, h2]

end A208316Proof

open A208316Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a208316.main := by
  refine ⟨gf, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact (closed m).1


