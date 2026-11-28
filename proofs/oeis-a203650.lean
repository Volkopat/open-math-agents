import OMAStatements.S_oeis_a203650

namespace OMA.P_oeis_a203650

open OMA.S_oeis_a203650 PowerSeries Finset

/-- A row of the array. -/
abbrev R := Fin 3 → Fin 5

/-- The subblock condition between a row `r` (if any) and the next row `c`. -/
def pairOK : Option R → R → Prop
  | none, _ => True
  | some r, c => ∀ j : Fin 2, r j.castSucc = c j.succ ∨ r j.succ = c j.castSucc

instance : ∀ (p : Option R), DecidablePred (pairOK p)
  | none => fun _ => isTrue trivial
  | some r => fun c => by unfold pairOK; infer_instance

/-- The row of `y` at a natural index, or `none` outside. -/
def rowN {m : ℕ} (y : Fin m → R) (k : ℕ) : Option R := if h : k < m then some (y ⟨k, h⟩) else none

/-- The row before row `i` of `y`, where `p` is the row before the first one. -/
def prev {m : ℕ} (p : Option R) (y : Fin m → R) (i : Fin m) : Option R :=
  if (i : ℕ) = 0 then p else rowN y (i - 1)

/-- The subblock condition for an array whose previous row is `p`. -/
def BLP {m : ℕ} (p : Option R) (y : Fin m → R) : Prop := ∀ i : Fin m, pairOK (prev p y i) (y i)

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

/-- Completions of length `n` after the row `p`. -/
def F (p : Option R) (n : ℕ) : ℕ := (univ.filter fun x : Fin n → R => BLP p x).card

lemma card_cons' {n : ℕ} (P : (Fin (n + 1) → R) → Prop) [DecidablePred P] :
    (univ.filter P).card = ∑ d : R, (univ.filter fun x : Fin n → R => P (Fin.cons d x)).card := by
  simp only [card_filter]
  rw [← (Fin.consEquiv fun _ => R).sum_comp, Fintype.sum_prod_type]
  rfl

lemma F_zero (p : Option R) : F p 0 = 1 := by
  unfold F
  rw [card_filter, Fintype.sum_unique]
  simp [BLP]

lemma F_succ (p : Option R) (n : ℕ) :
    F p (n + 1) = ∑ c : R, if pairOK p c then F (some c) n else 0 := by
  unfold F
  rw [card_cons']
  refine sum_congr rfl fun c _ => ?_
  simp only [BLP_cons]
  split_ifs with h
  · congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and]
    tauto
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro x _ hx
    exact h hx.1

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

lemma a_eq (n : ℕ) : a n = (F none (n + 1) : ℚ) / 25 := by
  unfold a F
  congr 3
  ext A
  simp only [mem_filter, mem_univ, true_and, block_iff]

/-- A code for a row. -/
def code (r : R) : ℕ := (r 0 : ℕ) + 5 * r 1 + 25 * r 2

/-- A code for an optional row. -/
def codeO : Option R → ℕ
  | none => 0
  | some r => code r + 1

/-- The class table of the states. -/
def tbl : List (Fin 3) := [0, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2]

/-- The class of the state (previous row). -/
def cls (p : Option R) : Fin 3 := tbl.getD (codeO p) 0

/-- Class transition counts. -/
def B : Fin 3 → Fin 3 → ℕ := ![![0, 100, 25], ![0, 8, 5], ![0, 20, 9]]

/-- Class counts. -/
def cnt : ℕ → Fin 3 → ℕ
  | 0 => fun _ => 1
  | n + 1 => fun i => ∑ j, B i j * cnt n j

lemma step_check : ∀ (p : Option R) (j : Fin 3),
    (univ.filter fun c : R => pairOK p c ∧ cls (some c) = j).card = B (cls p) j := by
  decide +kernel

lemma sum_ite_card {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P] (v : ℕ) :
    (∑ d : α, if P d then v else 0) = (univ.filter P).card * v := by
  rw [← sum_filter, sum_const, smul_eq_mul]

lemma F_cls (n : ℕ) : ∀ (p : Option R), F p n = cnt n (cls p) := by
  induction n with
  | zero => intro p; rw [F_zero]; rfl
  | succ n ih =>
    intro p
    rw [F_succ]
    have hd : ∀ c : R, (if pairOK p c then F (some c) n else 0) =
        ∑ j : Fin 3, if (pairOK p c ∧ cls (some c) = j) then cnt n j else 0 := by
      intro c
      split_ifs with h
      · rw [ih]
        simp [h]
      · symm
        apply sum_eq_zero
        intro j _
        rw [if_neg]
        rintro ⟨h1, -⟩
        exact h h1
    rw [sum_congr rfl (fun c _ => hd c), sum_comm]
    show _ = ∑ j, B (cls p) j * cnt n j
    refine sum_congr rfl fun j _ => ?_
    rw [sum_ite_card, step_check]

lemma a_cnt (n : ℕ) : a n = (cnt (n + 1) 0 : ℚ) / 25 := by
  rw [a_eq, F_cls]
  rfl

lemma a_rec (m : ℕ) : a (m + 3) - 17 * a (m + 2) - 28 * a (m + 1) = 0 := by
  rw [a_cnt, a_cnt, a_cnt]
  simp [cnt, B, Fin.sum_univ_succ]
  ring

lemma a1 : a 1 = 81 := by rw [a_cnt]; norm_num [cnt, B, Fin.sum_univ_succ]
lemma a2 : a 2 = 1517 := by rw [a_cnt]; norm_num [cnt, B, Fin.sum_univ_succ]

theorem gf :
    (1 - 17 * X - 28 * X ^ 2) * PowerSeries.mk (fun n => if n = 0 then 0 else a n) =
      (X * (81 + 140 * X) : PowerSeries ℚ) := by
  set s : PowerSeries ℚ := PowerSeries.mk (fun n => if n = 0 then 0 else a n) with hs
  have hd : (1 - 17 * X - 28 * X ^ 2) * s = s - (s * C (17 : ℚ)) * X ^ 1 -
      (s * C (28 : ℚ)) * X ^ 2 := by
    simp only [pow_one, map_ofNat]
    ring
  have hn : (X * (81 + 140 * X) : PowerSeries ℚ) = C (81 : ℚ) * X ^ 1 + C (140 : ℚ) * X ^ 2 := by
    simp only [pow_one, map_ofNat]
    ring
  rw [hd, hn]
  ext n
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_mul_C, coeff_C, hs, coeff_mk]
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ 3 ≤ n) with h | h | h | h
  · subst h; simp
  · subst h; simp [a1]
  · subst h; norm_num [a1, a2]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have := a_rec m
    simp only [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega]
    simp
    linarith

/-- The closed form, written with the roots `(17 ± √401) / 2` and without division by `√401`. -/
noncomputable def T (n : ℕ) : ℝ :=
  (((17 + Real.sqrt 401) / 2) ^ n * (77 * Real.sqrt 401 + 2005) +
    ((17 - Real.sqrt 401) / 2) ^ n * (2005 - 77 * Real.sqrt 401)) / 802

lemma pow_step (x : ℝ) (h : x ^ 2 = 17 * x + 28) (j : ℕ) :
    x ^ (j + 2) = 17 * x ^ (j + 1) + 28 * x ^ j := by
  linear_combination (x ^ j) * h

lemma T_rec (j : ℕ) : T (j + 2) = 17 * T (j + 1) + 28 * T j := by
  have hs : Real.sqrt 401 ^ 2 = 401 := Real.sq_sqrt (by norm_num)
  have ha : ((17 + Real.sqrt 401) / 2) ^ 2 = 17 * ((17 + Real.sqrt 401) / 2) + 28 := by
    linear_combination hs / 4
  have hb : ((17 - Real.sqrt 401) / 2) ^ 2 = 17 * ((17 - Real.sqrt 401) / 2) + 28 := by
    linear_combination hs / 4
  have e1 := pow_step _ ha j
  have e2 := pow_step _ hb j
  unfold T
  linear_combination ((77 * Real.sqrt 401 + 2005) / 802) * e1 +
    ((2005 - 77 * Real.sqrt 401) / 802) * e2

lemma closed (m : ℕ) : (a (m + 1) : ℝ) = T (m + 1) ∧ (a (m + 2) : ℝ) = T (m + 2) := by
  have hs : Real.sqrt 401 ^ 2 = 401 := Real.sq_sqrt (by norm_num)
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [a1, T]; push_cast; linear_combination (-77 / 802 : ℝ) * hs
    · rw [a2, T]; push_cast; linear_combination (-4623 / 1604 : ℝ) * hs
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨h2, ?_⟩
    have hr : (a (m + 3) : ℝ) = 17 * a (m + 2) + 28 * a (m + 1) := by
      have := a_rec m
      have h' : a (m + 3) = 17 * a (m + 2) + 28 * a (m + 1) := by linarith
      rw [h']
      push_cast
      ring
    rw [T_rec (m + 1)]
    rw [show m + 1 + 2 = m + 3 by ring, hr, show m + 1 + 1 = m + 2 by ring, h1, h2]

lemma T_eq (n : ℕ) : T n = (2 ^ (-1 - (n : ℤ)) * ((17 - Real.sqrt 401) ^ n *
    (-77 + 5 * Real.sqrt 401) + (17 + Real.sqrt 401) ^ n * (77 + 5 * Real.sqrt 401))) /
    Real.sqrt 401 := by
  have hs : Real.sqrt 401 ^ 2 = 401 := Real.sq_sqrt (by norm_num)
  have h0 : Real.sqrt 401 ≠ 0 := by positivity
  have hz : (2 : ℝ) ^ (-1 - (n : ℤ)) = (2 ^ n)⁻¹ / 2 := by
    rw [show (-1 - (n : ℤ)) = -(n : ℤ) + (-1) by ring, zpow_add₀ two_ne_zero, zpow_neg,
      zpow_natCast]
    norm_num
    ring
  have hdiv : ∀ x : ℝ, x / Real.sqrt 401 = x * Real.sqrt 401 / 401 := by
    intro x
    rw [div_eq_div_iff h0 (by norm_num)]
    linear_combination (-x) * hs
  rw [T, hz, div_pow, div_pow, hdiv]
  linear_combination (-5 * (2 ^ n)⁻¹ * ((17 + Real.sqrt 401) ^ n + (17 - Real.sqrt 401) ^ n) / 802) * hs

end OMA.P_oeis_a203650

theorem OMA.solution : type_of% @OMA.S_oeis_a203650.main := by
  refine ⟨OMA.P_oeis_a203650.gf, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [(OMA.P_oeis_a203650.closed m).1, OMA.P_oeis_a203650.T_eq]

