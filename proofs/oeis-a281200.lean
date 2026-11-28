import OMAStatements.S_oeis_a281200

namespace OMA.P_oeis_a281200

open OMA.S_oeis_a281200 PowerSeries Finset

/-- A row of the array. -/
abbrev R := Fin 3 → Fin 2

/-- The element of a row at an integer column, or `none` outside. -/
def col (r : R) (c : ℤ) : Option (Fin 2) :=
  if h : 0 ≤ c ∧ c < 3 then some (r ⟨c.toNat, by omega⟩) else none

/-- The row of an array at an integer index, or `none` outside. -/
def rowAt {m : ℕ} (A : Fin m → R) (r : ℤ) : Option R :=
  if h : 0 ≤ r ∧ r < m then some (A ⟨r.toNat, by omega⟩) else none

lemma entry_eq {m : ℕ} (A : Fin m → R) (r c : ℤ) :
    entry A r c = (rowAt A r).bind (col · c) := by
  unfold entry rowAt col
  by_cases h1 : 0 ≤ r ∧ r < m
  · by_cases h2 : 0 ≤ c ∧ c < 3
    · rw [dif_pos ⟨h1.1, h1.2, h2⟩, dif_pos h1, Option.bind_some, dif_pos h2]
    · rw [dif_neg (by tauto), dif_pos h1, Option.bind_some, dif_neg h2]
  · rw [dif_neg (by tauto), dif_neg h1, Option.bind_none]

lemma rowAt_self {m : ℕ} (A : Fin m → R) (i : Fin m) : rowAt A (i : ℤ) = some (A i) := by
  unfold rowAt
  rw [dif_pos (by omega)]
  congr 2

/-- The row at offset `dr` from the current row `c`, given the rows `p` above and `q` below. -/
def sel (p : Option R) (c : R) (q : Option R) (dr : ℤ) : Option R :=
  if dr = -1 then p else if dr = 0 then some c else q

/-- The number of neighbours of column `j` of row `c` equal to it, given the rows around. -/
def loc (p : Option R) (c : R) (q : Option R) (j : Fin 3) : ℕ :=
  (offsets.filter fun d => (sel p c q d.1).bind (col · (j + d.2)) = some (c j)).length

lemma eqN {m : ℕ} (A : Fin m → R) (i : Fin m) (j : Fin 3) :
    equalNeighbours A i j = loc (rowAt A ((i : ℤ) - 1)) (A i) (rowAt A ((i : ℤ) + 1)) j := by
  unfold equalNeighbours loc
  congr 1
  apply List.filter_congr
  intro d hd
  simp only [offsets, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl <;>
    simp [entry_eq, sel, rowAt_self, sub_eq_add_neg]

/-- The number of exceptions in row `c`, given the rows around. -/
def g (p : Option R) (c : R) (q : Option R) : ℕ :=
  (univ.filter fun j : Fin 3 => 1 < loc p c q j).card

/-- The number of exceptions of an array whose row above the first is `p`. -/
def Wt {m : ℕ} (p : Option R) (y : Fin m → R) : ℕ :=
  ∑ i : Fin m, g (if (i : ℕ) = 0 then p else rowAt y ((i : ℤ) - 1)) (y i) (rowAt y ((i : ℤ) + 1))

lemma rowAt_neg {m : ℕ} (A : Fin m → R) (r : ℤ) (h : r < 0) : rowAt A r = none := by
  unfold rowAt; rw [dif_neg (by omega)]

lemma card_exceptions {m : ℕ} (A : Fin m → R) : (exceptions A).card = Wt none A := by
  unfold exceptions Wt
  rw [card_filter, Fintype.sum_prod_type]
  refine sum_congr rfl fun i _ => ?_
  have hp : (if (i : ℕ) = 0 then (none : Option R) else rowAt A ((i : ℤ) - 1)) =
      rowAt A ((i : ℤ) - 1) := by
    split_ifs with h
    · rw [rowAt_neg]; omega
    · rfl
  rw [hp, g, card_filter]
  simp only [eqN]

lemma rowAt_cons {m : ℕ} (c : R) (x : Fin m → R) (k : ℤ) (hk : 0 ≤ k) :
    rowAt (Fin.cons c x : Fin (m + 1) → R) (k + 1) = rowAt x k := by
  unfold rowAt
  by_cases h : k < m
  · rw [dif_pos (by omega), dif_pos (by omega)]
    have e : (⟨(k + 1).toNat, by omega⟩ : Fin (m + 1)) = Fin.succ ⟨k.toNat, by omega⟩ := by
      ext; simp; omega
    rw [e, Fin.cons_succ]
  · rw [dif_neg (by push_cast; omega), dif_neg (by omega)]

lemma rowAt_cons_zero {m : ℕ} (c : R) (x : Fin m → R) :
    rowAt (Fin.cons c x : Fin (m + 1) → R) 0 = some c := by
  have := rowAt_self (Fin.cons c x : Fin (m + 1) → R) 0
  simpa using this

lemma Wt_cons {m : ℕ} (p : Option R) (c : R) (x : Fin m → R) :
    Wt p (Fin.cons c x : Fin (m + 1) → R) = g p c (rowAt x 0) + Wt (some c) x := by
  unfold Wt
  rw [Fin.sum_univ_succ]
  refine congrArg₂ (· + ·) ?_ ?_
  · simp only [if_true, Fin.cons_zero, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
      Nat.cast_zero]
    rw [show (0 : ℤ) + 1 = 0 + 1 from rfl, rowAt_cons c x 0 le_rfl]
  · refine sum_congr rfl fun i _ => ?_
    simp only [Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false,
      Fin.cons_succ, Nat.cast_add, Nat.cast_one]
    refine congrArg₂ (fun u v => g u (x i) v) ?_ ?_
    · split_ifs with h
      · have : (i : ℤ) = 0 := by exact_mod_cast h
        rw [this, show (0 : ℤ) + 1 - 1 = 0 by ring, rowAt_cons_zero]
      · rw [show (i : ℤ) + 1 - 1 = ((i : ℤ) - 1) + 1 by ring, rowAt_cons c x _ (by omega)]
    · rw [rowAt_cons c x _ (by omega)]


/-- Completions of length `n` after rows `p`, `c` with exactly `k` further exceptions. -/
def F (p : Option R) (c : R) (k n : ℕ) : ℕ :=
  (univ.filter fun x : Fin n → R => g p c (rowAt x 0) + Wt (some c) x = k).card

lemma F_zero (p : Option R) (c : R) (k : ℕ) : F p c k 0 = if g p c none = k then 1 else 0 := by
  unfold F
  rw [card_filter, Fintype.sum_unique]
  simp [Wt, rowAt]

lemma card_cons' {n : ℕ} (P : (Fin (n + 1) → R) → Prop) [DecidablePred P] :
    (univ.filter P).card = ∑ d : R, (univ.filter fun x : Fin n → R => P (Fin.cons d x)).card := by
  simp only [card_filter]
  rw [← (Fin.consEquiv fun _ => R).sum_comp, Fintype.sum_prod_type]
  rfl

lemma F_succ (p : Option R) (c : R) (k n : ℕ) :
    F p c k (n + 1) = ∑ d : R,
      if g p c (some d) ≤ k then F (some c) d (k - g p c (some d)) n else 0 := by
  unfold F
  rw [card_cons']
  refine sum_congr rfl fun d _ => ?_
  simp only [rowAt_cons_zero, Wt_cons]
  split_ifs with h
  · congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and]
    omega
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro x _
    omega

lemma nvio_iff {n : ℕ} (A : Fin (n + 1) → R) : NewValuesInOrder A ↔ A 0 0 = 0 := by
  constructor
  · intro h
    by_contra h0
    have h1 : (0 : Fin 2) < A 0 0 := by
      rcases Fin.exists_fin_two.mp ⟨A 0 0, rfl⟩ with e | e <;> simp_all
    obtain ⟨i', j', hlt, -⟩ := h 0 0 0 h1
    simp at hlt
  · intro h i j w hw
    refine ⟨0, 0, ?_, ?_⟩
    · have e1 : ((0 : Fin (n + 1)) : ℕ) = 0 := rfl
      have e2 : ((0 : Fin 3) : ℕ) = 0 := rfl
      rw [e1, e2]
      by_contra hc
      have hi : i = 0 := by ext; simp; omega
      have hj : j = 0 := by ext; simp; omega
      subst hi hj
      rw [h] at hw
      exact absurd hw (Fin.not_lt_zero w)
    · have hw1 : (w : ℕ) < A i j := hw
      have : (A i j : ℕ) < 2 := (A i j).isLt
      ext; simp [h]; omega

lemma a_succ (n : ℕ) : a (n + 1) = ∑ c : R, if c 0 = 0 then F none c 1 n else 0 := by
  unfold a
  simp only [nvio_iff, card_exceptions]
  rw [card_cons']
  refine sum_congr rfl fun c _ => ?_
  simp only [Fin.cons_zero, Wt_cons]
  split_ifs with h
  · unfold F; simp only [h, true_and]
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro x _ hx
    exact h hx.1


/-- A code for a row. -/
def code (r : R) : ℕ := (r 0 : ℕ) + 2 * r 1 + 4 * r 2

/-- A code for an optional row. -/
def codeO : Option R → ℕ
  | none => 0
  | some r => code r + 1

/-- The class table of the states. -/
def tbl : List (Fin 8) := [3, 5, 4, 0, 7, 1, 6, 2, 6, 2, 7, 1, 4, 0, 3, 5, 3, 3, 3, 5, 7, 1, 6, 2, 3, 3, 6, 2, 4, 0, 3, 5, 3, 3, 3, 5, 7, 1, 6, 2, 3, 3, 6, 2, 4, 0, 3, 5, 3, 5, 3, 5, 7, 1, 3, 6, 3, 7, 6, 2, 4, 0, 3, 3, 3, 5, 3, 5, 7, 1, 3, 6, 3, 7, 6, 2, 4, 0, 3, 3, 3, 3, 4, 0, 6, 2, 3, 7, 3, 6, 7, 1, 3, 5, 3, 5, 3, 3, 4, 0, 6, 2, 3, 7, 3, 6, 7, 1, 3, 5, 3, 5, 3, 5, 4, 0, 6, 2, 3, 3, 6, 2, 7, 1, 3, 5, 3, 3, 3, 5, 4, 0, 6, 2, 3, 3, 6, 2, 7, 1, 3, 5, 3, 3]

/-- The class of the state (row above, current row, exceptions still allowed). -/
def cls (p : Option R) (c : R) (k : ℕ) : Fin 8 := tbl.getD ((codeO p * 8 + code c) * 2 + k) 0

/-- Class transition counts. -/
def B : Fin 8 → Fin 8 → ℕ := ![![0, 0, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 0, 2, 1, 1],
  ![1, 1, 0, 3, 0, 1, 1, 1], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 1, 0],
  ![0, 0, 0, 1, 1, 0, 1, 1], ![0, 0, 0, 2, 1, 0, 0, 1], ![0, 0, 0, 5, 1, 0, 1, 1]]

/-- Class counts for completions of length zero. -/
def init : Fin 8 → ℕ := ![0, 0, 0, 0, 1, 1, 1, 1]

/-- Number of admissible first rows in each class. -/
def U : Fin 8 → ℕ := ![1, 1, 1, 0, 0, 1, 0, 0]

/-- Class counts. -/
def cnt : ℕ → Fin 8 → ℕ
  | 0 => init
  | n + 1 => fun i => ∑ j, B i j * cnt n j

lemma base_check : ∀ (p : Option R) (c : R) (k : Fin 2),
    (if g p c none = (k : ℕ) then 1 else 0) = init (cls p c k) := by
  decide +kernel

lemma step_check : ∀ (p : Option R) (c : R) (k : Fin 2) (j : Fin 8),
    (univ.filter fun d : R => g p c (some d) ≤ k ∧
      cls (some c) d (k - g p c (some d)) = j).card = B (cls p c k) j := by
  decide +kernel

lemma u_check : ∀ j : Fin 8, (univ.filter fun c : R => c 0 = 0 ∧ cls none c 1 = j).card = U j := by
  decide +kernel

lemma sum_ite_card {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P] (v : ℕ) :
    (∑ d : α, if P d then v else 0) = (univ.filter P).card * v := by
  rw [← sum_filter, sum_const, smul_eq_mul]

lemma F_cls (n : ℕ) : ∀ (p : Option R) (c : R) (k : Fin 2), F p c k n = cnt n (cls p c k) := by
  induction n with
  | zero => intro p c k; rw [F_zero, base_check]; rfl
  | succ n ih =>
    intro p c k
    rw [F_succ]
    have hd : ∀ d : R, (if g p c (some d) ≤ k then F (some c) d (k - g p c (some d)) n else 0) =
        ∑ j : Fin 8, if (g p c (some d) ≤ k ∧ cls (some c) d (k - g p c (some d)) = j)
          then cnt n j else 0 := by
      intro d
      split_ifs with h
      · rw [show F (some c) d (k - g p c (some d)) n = cnt n (cls (some c) d (k - g p c (some d)))
          from ih (some c) d ⟨_, by omega⟩]
        simp [h]
      · simp [h]
    rw [sum_congr rfl (fun d _ => hd d), sum_comm]
    show _ = ∑ j, B (cls p c k) j * cnt n j
    refine sum_congr rfl fun j _ => ?_
    rw [sum_ite_card, step_check]

lemma a_cnt (n : ℕ) : a (n + 1) = ∑ j, U j * cnt n j := by
  rw [a_succ]
  have hc : ∀ c : R, (if c 0 = 0 then F none c 1 n else 0) =
      ∑ j : Fin 8, if (c 0 = 0 ∧ cls none c 1 = j) then cnt n j else 0 := by
    intro c
    split_ifs with h
    · rw [show F none c 1 n = cnt n (cls none c 1) from F_cls n none c 1]
      simp [h]
    · simp [h]
  rw [sum_congr rfl (fun c _ => hc c), sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [sum_ite_card, u_check]


lemma cnt3 (n : ℕ) : cnt n 3 = 0 := by
  cases n with
  | zero => rfl
  | succ n => simp [cnt, B, Fin.sum_univ_succ]

lemma cnt_inv (n : ℕ) : (cnt n 4 : ℤ) - 2 * cnt n 6 + cnt n 7 = 0 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h3 := cnt3 n
    simp only [cnt, B, Fin.sum_univ_succ] at ih ⊢
    simp at ih ⊢
    have h3' : (cnt n 3 : ℤ) = 0 := by exact_mod_cast h3
    linear_combination (-1 : ℤ) * ih + 2 * h3'

lemma a_rec (m : ℕ) : (a (m + 4) : ℤ) - 4 * a (m + 3) + 4 * a (m + 2) = 0 := by
  have h3' : (cnt m 3 : ℤ) = 0 := by exact_mod_cast cnt3 m
  have hi := cnt_inv m
  rw [a_cnt, a_cnt, a_cnt]
  simp [cnt, B, U, Fin.sum_univ_succ]
  linear_combination 12 * h3' - 2 * hi

lemma a1 : a 1 = 1 := by rw [a_cnt]; decide
lemma a2 : a 2 = 14 := by rw [a_cnt]; decide
lemma a3 : a 3 = 56 := by rw [a_cnt]; decide

theorem gf :
    (1 - 2 * X) ^ 2 * PowerSeries.mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (X * (1 + 10 * X + 4 * X ^ 2) : PowerSeries ℤ) := by
  set s : PowerSeries ℤ := PowerSeries.mk (fun n => if n = 0 then 0 else (a n : ℤ)) with hs
  have hd : (1 - 2 * X) ^ 2 * s = s - (s * C (4 : ℤ)) * X ^ 1 + (s * C (4 : ℤ)) * X ^ 2 := by
    simp only [pow_one, map_ofNat]
    ring
  have hn : (X * (1 + 10 * X + 4 * X ^ 2) : PowerSeries ℤ) =
      C (1 : ℤ) * X ^ 1 + C (10 : ℤ) * X ^ 2 + C (4 : ℤ) * X ^ 3 := by
    simp only [pow_one, map_ofNat, map_one]
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

theorem closed (m : ℕ) : (a (m + 2) : ℚ) = 7 * 2 ^ (m + 1) * ((m : ℚ) + 1) ∧
    (a (m + 3) : ℚ) = 7 * 2 ^ (m + 2) * ((m : ℚ) + 2) := by
  induction m with
  | zero => rw [a2, a3]; norm_num
  | succ m ih =>
    refine ⟨by rw [ih.2]; push_cast; ring, ?_⟩
    have h : (a (m + 4) : ℚ) = 4 * a (m + 3) - 4 * a (m + 2) := by
      have := a_rec m
      have : ((a (m + 4) : ℤ) : ℚ) = 4 * ((a (m + 3) : ℤ) : ℚ) - 4 * ((a (m + 2) : ℤ) : ℚ) := by
        exact_mod_cast (by linarith : (a (m + 4) : ℤ) = 4 * a (m + 3) - 4 * a (m + 2))
      exact_mod_cast this
    rw [show m + 1 + 3 = m + 4 by ring, h, ih.1, ih.2]
    push_cast
    ring

end OMA.P_oeis_a281200

theorem OMA.solution : type_of% @OMA.S_oeis_a281200.main := by
  refine ⟨OMA.P_oeis_a281200.gf, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [(OMA.P_oeis_a281200.closed m).1, show m + 2 - 1 = m + 1 by omega]
  push_cast
  ring

