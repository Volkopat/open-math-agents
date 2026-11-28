import OMAStatements.S_oeis_a204070

namespace OMA.P_oeis_a204070

open OMA.S_oeis_a204070 PowerSeries Finset

/-- A row of the array. -/
abbrev R := Fin 3 → Fin 3

/-- The new-values condition inside one row, given the set `S` of values in earlier rows. -/
def rowOK (S : Finset (Fin 3)) (c : R) : Prop :=
  ∀ (j : Fin 3) (w : Fin 3), w < c j → w ∈ S ∨ ∃ j' : Fin 3, j' < j ∧ c j' = w

instance (S : Finset (Fin 3)) : DecidablePred (rowOK S) := fun c => by
  unfold rowOK; infer_instance

/-- The subblock condition between a row `r` (if any) and the next row `c`. -/
def pairOK : Option R → R → Prop
  | none, _ => True
  | some r, c => ∀ j : Fin 2, r j.castSucc = c j.succ ∨ r j.succ = c j.castSucc

instance : ∀ (p : Option R), DecidablePred (pairOK p)
  | none => fun _ => isTrue trivial
  | some r => fun c => by unfold pairOK; infer_instance

/-- The values of a row. -/
def vals (c : R) : Finset (Fin 3) := univ.image c

/-- The row of `y` at a natural index, or `none` outside. -/
def rowN {m : ℕ} (y : Fin m → R) (k : ℕ) : Option R := if h : k < m then some (y ⟨k, h⟩) else none

/-- The row before row `i` of `y`, where `p` is the row before the first one. -/
def prev {m : ℕ} (p : Option R) (y : Fin m → R) (i : Fin m) : Option R :=
  if (i : ℕ) = 0 then p else rowN y (i - 1)

/-- The new-values condition for an array whose earlier rows have value set `S`. -/
def NVS {m : ℕ} (S : Finset (Fin 3)) (y : Fin m → R) : Prop :=
  ∀ (i : Fin m) (j : Fin 3) (w : Fin 3), w < y i j →
    w ∈ S ∨ ∃ (i' : Fin m) (j' : Fin 3), 3 * (i' : ℕ) + j' < 3 * (i : ℕ) + j ∧ y i' j' = w

/-- The subblock condition for an array whose previous row is `p`. -/
def BLP {m : ℕ} (p : Option R) (y : Fin m → R) : Prop := ∀ i : Fin m, pairOK (prev p y i) (y i)

instance {m : ℕ} (S : Finset (Fin 3)) : DecidablePred (NVS (m := m) S) := fun y => by
  unfold NVS; infer_instance

instance {m : ℕ} (p : Option R) : DecidablePred (BLP (m := m) p) := fun y => by
  unfold BLP; infer_instance

lemma prev_cons_zero {m : ℕ} (p : Option R) (c : R) (x : Fin m → R) :
    prev p (Fin.cons c x : Fin (m + 1) → R) 0 = p := by
  simp [prev]

lemma prev_cons_succ {m : ℕ} (p : Option R) (c : R) (x : Fin m → R) (i : Fin m) :
    prev p (Fin.cons c x : Fin (m + 1) → R) i.succ = prev (some c) x i := by
  unfold prev rowN
  have hi : ¬ ((i.succ : ℕ) = 0) := by simp
  rw [if_neg hi, dif_pos (by simp)]
  by_cases h : (i : ℕ) = 0
  · rw [if_pos h]
    have e : (⟨(i.succ : ℕ) - 1, by simp⟩ : Fin (m + 1)) = 0 := by ext; simp [h]
    rw [e, Fin.cons_zero]
  · rw [if_neg h, dif_pos (by omega)]
    have e : (⟨(i.succ : ℕ) - 1, by simp⟩ : Fin (m + 1)) = Fin.succ ⟨(i : ℕ) - 1, by omega⟩ := by
      ext; simp; omega
    rw [e, Fin.cons_succ]

lemma BLP_cons {m : ℕ} (p : Option R) (c : R) (x : Fin m → R) :
    BLP p (Fin.cons c x : Fin (m + 1) → R) ↔ pairOK p c ∧ BLP (some c) x := by
  unfold BLP
  rw [Fin.forall_fin_succ]
  simp only [prev_cons_zero, prev_cons_succ, Fin.cons_zero, Fin.cons_succ]

lemma NVS_cons {m : ℕ} (S : Finset (Fin 3)) (c : R) (x : Fin m → R) :
    NVS S (Fin.cons c x : Fin (m + 1) → R) ↔ rowOK S c ∧ NVS (S ∪ vals c) x := by
  unfold NVS rowOK
  rw [Fin.forall_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ]
  apply and_congr
  · apply forall_congr'; intro j; apply forall_congr'; intro w; apply imp_congr_right; intro _
    apply or_congr_right
    constructor
    · rintro ⟨i', j', h1, h2⟩
      refine Fin.cases (motive := fun i' => 3 * (i' : ℕ) + j' < 3 * 0 + j →
        (Fin.cons c x : Fin (m + 1) → R) i' j' = w → ∃ j' : Fin 3, j' < j ∧ c j' = w)
        ?_ ?_ i' h1 h2
      · intro h1 h2
        exact ⟨j', by simp at h1; exact h1, by simpa using h2⟩
      · intro i'' h1 _
        simp at h1; omega
    · rintro ⟨j', h1, h2⟩
      exact ⟨0, j', by simp; exact h1, by simpa using h2⟩
  · apply forall_congr'; intro i; apply forall_congr'; intro j; apply forall_congr'; intro w
    apply imp_congr_right; intro _
    constructor
    · rintro (h | ⟨i', j', h1, h2⟩)
      · exact Or.inl (mem_union_left _ h)
      · refine Fin.cases (motive := fun i' => 3 * (i' : ℕ) + j' < 3 * ((i : ℕ) + 1) + j →
          (Fin.cons c x : Fin (m + 1) → R) i' j' = w →
          w ∈ S ∪ vals c ∨ ∃ (i' : Fin m) (j' : Fin 3), 3 * (i' : ℕ) + j' < 3 * (i : ℕ) + j ∧
            x i' j' = w) ?_ ?_ i' h1 h2
        · intro _ h2
          exact Or.inl (mem_union_right _ (mem_image.2 ⟨j', mem_univ _, by simpa using h2⟩))
        · intro i'' h1 h2
          exact Or.inr ⟨i'', j', by simp at h1; omega, by simpa using h2⟩
    · rintro (h | ⟨i', j', h1, h2⟩)
      · rcases mem_union.1 h with h | h
        · exact Or.inl h
        · obtain ⟨j', -, hj⟩ := mem_image.1 h
          exact Or.inr ⟨0, j', by simp; omega, by simpa using hj⟩
      · exact Or.inr ⟨i'.succ, j', by simp; omega, by simpa using h2⟩

/-- Completions of length `n` after earlier rows with value set `S` and last row `p`. -/
def F (S : Finset (Fin 3)) (p : Option R) (n : ℕ) : ℕ :=
  (univ.filter fun x : Fin n → R => NVS S x ∧ BLP p x).card

lemma card_cons' {n : ℕ} (P : (Fin (n + 1) → R) → Prop) [DecidablePred P] :
    (univ.filter P).card = ∑ d : R, (univ.filter fun x : Fin n → R => P (Fin.cons d x)).card := by
  simp only [card_filter]
  rw [← (Fin.consEquiv fun _ => R).sum_comp, Fintype.sum_prod_type]
  rfl

lemma F_zero (S : Finset (Fin 3)) (p : Option R) : F S p 0 = 1 := by
  unfold F
  rw [card_filter, Fintype.sum_unique]
  simp [NVS, BLP]

lemma F_succ (S : Finset (Fin 3)) (p : Option R) (n : ℕ) :
    F S p (n + 1) = ∑ c : R, if rowOK S c ∧ pairOK p c then F (S ∪ vals c) (some c) n else 0 := by
  unfold F
  rw [card_cons']
  refine sum_congr rfl fun c _ => ?_
  simp only [NVS_cons, BLP_cons]
  split_ifs with h
  · congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and]
    tauto
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro x _ hx
    exact h ⟨hx.1.1, hx.2.1⟩

lemma block_iff {n : ℕ} (A : Fin (n + 1) → R) : SubblockCondition A ↔ BLP none A := by
  unfold SubblockCondition BLP
  rw [Fin.forall_fin_succ]
  have h0 : prev none A 0 = none := by simp [prev]
  have hs : ∀ i : Fin n, prev none A i.succ = some (A i.castSucc) := by
    intro i
    unfold prev rowN
    simp only [Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false,
      Nat.add_sub_cancel]
    rw [dif_pos (by omega)]
    rfl
  simp only [h0, hs, pairOK, true_and]

lemma a_eq (n : ℕ) : a n = F ∅ none (n + 1) := by
  unfold a F
  congr 1
  ext A
  simp only [mem_filter, mem_univ, true_and, block_iff]
  have : NewValuesInOrder A ↔ NVS ∅ A := by
    simp [NewValuesInOrder, NVS]
  rw [this, and_comm]

/-- The value set `{0, ..., k - 1}`. -/
def rangeF (k : Fin 4) : Finset (Fin 3) := univ.filter fun v => (v : ℕ) < k

/-- The number of values seen after a row `c`, when `k` values were seen before. -/
def nk (k : Fin 4) (c : R) : Fin 4 :=
  ⟨max (k : ℕ) (max ((c 0 : ℕ) + 1) (max ((c 1 : ℕ) + 1) ((c 2 : ℕ) + 1))), by omega⟩

lemma seen_check : ∀ (k : Fin 4) (c : R), rowOK (rangeF k) c → rangeF k ∪ vals c = rangeF (nk k c) := by
  decide +kernel

/-- A code for a row. -/
def code (r : R) : ℕ := (r 0 : ℕ) + 3 * r 1 + 9 * r 2

/-- A code for an optional row. -/
def codeO : Option R → ℕ
  | none => 0
  | some r => code r + 1

/-- The class table of the states. -/
def tbl : List (Fin 21) := [4, 20, 20, 20, 17, 0, 14, 17, 0, 14, 3, 3, 3, 0, 2, 14, 14, 2, 14, 16, 16, 16, 0, 0, 14, 14, 0, 14, 15, 7, 3, 3, 11, 9, 6, 4, 18, 0, 4, 10, 4, 9, 12, 6, 0, 8, 0, 20, 20, 5, 9, 9, 6, 0, 18, 2, 19, 1, 13, 13, 1, 13, 13, 1, 13, 13, 13, 1, 13, 13, 1, 13, 13, 1, 13, 13, 13, 1, 13, 13, 1, 13, 13, 1, 19, 1, 13, 13, 1, 13, 13, 1, 13, 13, 13, 1, 13, 13, 1, 13, 13, 1, 13, 13, 13, 1, 13, 13, 1, 13, 13, 1]

/-- The class of the state (number of values seen, previous row). -/
def cls (k : Fin 4) (p : Option R) : Fin 21 := tbl.getD ((k : ℕ) * 28 + codeO p) 0

/-- Class transition counts. -/
def B : Fin 21 → Fin 21 → ℕ := ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
  ![0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0],
  ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0],
  ![0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0],
  ![0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0],
  ![0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0],
  ![0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0],
  ![0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0],
  ![0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0],
  ![0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0],
  ![0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0],
  ![0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0],
  ![0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0],
  ![0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0],
  ![0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0],
  ![0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0],
  ![0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]]

/-- Class counts. -/
def cnt : ℕ → Fin 21 → ℕ
  | 0 => fun _ => 1
  | n + 1 => fun i => ∑ j, B i j * cnt n j

lemma step_check : ∀ (k : Fin 4) (p : Option R) (j : Fin 21),
    (univ.filter fun c : R => rowOK (rangeF k) c ∧ pairOK p c ∧ cls (nk k c) (some c) = j).card =
      B (cls k p) j := by
  decide +kernel

lemma sum_ite_card {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P] (v : ℕ) :
    (∑ d : α, if P d then v else 0) = (univ.filter P).card * v := by
  rw [← sum_filter, sum_const, smul_eq_mul]

lemma F_cls (n : ℕ) : ∀ (k : Fin 4) (p : Option R), F (rangeF k) p n = cnt n (cls k p) := by
  induction n with
  | zero => intro k p; rw [F_zero]; rfl
  | succ n ih =>
    intro k p
    rw [F_succ]
    have hd : ∀ c : R, (if rowOK (rangeF k) c ∧ pairOK p c then
        F (rangeF k ∪ vals c) (some c) n else 0) =
        ∑ j : Fin 21, if (rowOK (rangeF k) c ∧ pairOK p c ∧ cls (nk k c) (some c) = j)
          then cnt n j else 0 := by
      intro c
      split_ifs with h
      · rw [seen_check k c h.1, ih]
        simp [h]
      · simp only [not_and] at h
        symm
        apply sum_eq_zero
        intro j _
        rw [if_neg]
        rintro ⟨h1, h2, -⟩
        exact h h1 h2
    rw [sum_congr rfl (fun c _ => hd c), sum_comm]
    show _ = ∑ j, B (cls k p) j * cnt n j
    refine sum_congr rfl fun j _ => ?_
    rw [sum_ite_card, step_check]

lemma a_cnt (n : ℕ) : a n = cnt (n + 1) 4 := by
  rw [a_eq, show (∅ : Finset (Fin 3)) = rangeF 0 by decide, F_cls]
  rfl

lemma a_rec (m : ℕ) : (a (m + 4) : ℤ) - 10 * a (m + 3) + 11 * a (m + 2) - 2 * a (m + 1) = 0 := by
  rw [a_cnt, a_cnt, a_cnt, a_cnt]
  simp [cnt, B, Fin.sum_univ_succ]
  ring

lemma a1 : a 1 = 38 := by rw [a_cnt]; decide
lemma a2 : a 2 = 329 := by rw [a_cnt]; decide
lemma a3 : a 3 = 2882 := by rw [a_cnt]; decide

theorem gf :
    (1 - X) * (1 - 9 * X + 2 * X ^ 2) * PowerSeries.mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (X * (38 - 51 * X + 10 * X ^ 2) : PowerSeries ℤ) := by
  set s : PowerSeries ℤ := PowerSeries.mk (fun n => if n = 0 then 0 else (a n : ℤ)) with hs
  have hd : (1 - X) * (1 - 9 * X + 2 * X ^ 2) * s = s - (s * C (10 : ℤ)) * X ^ 1 +
      (s * C (11 : ℤ)) * X ^ 2 - (s * C (2 : ℤ)) * X ^ 3 := by
    simp only [pow_one, map_ofNat]
    ring
  have hn : (X * (38 - 51 * X + 10 * X ^ 2) : PowerSeries ℤ) =
      C (38 : ℤ) * X ^ 1 - C (51 : ℤ) * X ^ 2 + C (10 : ℤ) * X ^ 3 := by
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
    simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
      show m + 4 - 3 = m + 1 by omega]
    simp
    omega

/-- The closed form, written with the roots `(9 ± √73) / 2` and without division by `√73`. -/
noncomputable def T (n : ℕ) : ℝ :=
  1 / 2 + (3 * ((9 + Real.sqrt 73) / 2) ^ n * (23 * Real.sqrt 73 + 219) +
    ((9 - Real.sqrt 73) / 2) ^ n * (657 - 69 * Real.sqrt 73)) / 292

lemma pow_step (x : ℝ) (h : x ^ 2 = 9 * x - 2) (j : ℕ) :
    x ^ (j + 3) = 10 * x ^ (j + 2) - 11 * x ^ (j + 1) + 2 * x ^ j := by
  linear_combination (x ^ j * (x - 1)) * h

lemma T_rec (j : ℕ) : T (j + 3) = 10 * T (j + 2) - 11 * T (j + 1) + 2 * T j := by
  have hs : Real.sqrt 73 ^ 2 = 73 := Real.sq_sqrt (by norm_num)
  have ha : ((9 + Real.sqrt 73) / 2) ^ 2 = 9 * ((9 + Real.sqrt 73) / 2) - 2 := by
    linear_combination hs / 4
  have hb : ((9 - Real.sqrt 73) / 2) ^ 2 = 9 * ((9 - Real.sqrt 73) / 2) - 2 := by
    linear_combination hs / 4
  have e1 := pow_step _ ha j
  have e2 := pow_step _ hb j
  unfold T
  linear_combination (3 * (23 * Real.sqrt 73 + 219) / 292) * e1 +
    ((657 - 69 * Real.sqrt 73) / 292) * e2

lemma closed (m : ℕ) : (a (m + 1) : ℝ) = T (m + 1) ∧ (a (m + 2) : ℝ) = T (m + 2) ∧
    (a (m + 3) : ℝ) = T (m + 3) := by
  have hs : Real.sqrt 73 ^ 2 = 73 := Real.sq_sqrt (by norm_num)
  induction m with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · rw [a1, T]; push_cast; linear_combination (-69 / 292 : ℝ) * hs
    · rw [a2, T]; push_cast; linear_combination (-1899 / 584 : ℝ) * hs
    · rw [a3, T]; push_cast
      linear_combination (-69 * Real.sqrt 73 ^ 2 / 1168 - 39543 / 1168 : ℝ) * hs
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨h2, h3, ?_⟩
    have hr : (a (m + 4) : ℝ) = 10 * a (m + 3) - 11 * a (m + 2) + 2 * a (m + 1) := by
      have := a_rec m
      have h' : (a (m + 4) : ℤ) = 10 * a (m + 3) - 11 * a (m + 2) + 2 * a (m + 1) := by
        linarith
      exact_mod_cast h'
    rw [T_rec (m + 1)]
    rw [show m + 1 + 3 = m + 4 by ring, hr, show m + 1 + 2 = m + 3 by ring,
      show m + 1 + 1 = m + 2 by ring, h1, h2, h3]

lemma T_eq (n : ℕ) : T n = 1 / 2 + (2 ^ (-2 - (n : ℤ)) * (3 * (9 + Real.sqrt 73) ^ n *
    (23 + 3 * Real.sqrt 73) + (9 - Real.sqrt 73) ^ n * (-69 + 9 * Real.sqrt 73))) /
    Real.sqrt 73 := by
  have hs : Real.sqrt 73 ^ 2 = 73 := Real.sq_sqrt (by norm_num)
  have h0 : Real.sqrt 73 ≠ 0 := by positivity
  have hz : (2 : ℝ) ^ (-2 - (n : ℤ)) = (2 ^ n)⁻¹ / 4 := by
    rw [show (-2 - (n : ℤ)) = -(n : ℤ) + (-2) by ring, zpow_add₀ two_ne_zero, zpow_neg,
      zpow_natCast]
    norm_num
    ring
  have hdiv : ∀ x : ℝ, x / Real.sqrt 73 = x * Real.sqrt 73 / 73 := by
    intro x
    rw [div_eq_div_iff h0 (by norm_num)]
    linear_combination (-x) * hs
  rw [T, hz, div_pow, div_pow, hdiv]
  linear_combination (-9 * (2 ^ n)⁻¹ * ((9 + Real.sqrt 73) ^ n + (9 - Real.sqrt 73) ^ n) / 292) * hs

end OMA.P_oeis_a204070

theorem OMA.solution : type_of% @OMA.S_oeis_a204070.main := by
  refine ⟨OMA.P_oeis_a204070.gf, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [(OMA.P_oeis_a204070.closed m).1, OMA.P_oeis_a204070.T_eq]

