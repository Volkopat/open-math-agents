import OMAStatements.S_oeis_a259215

-- Original proof by @ceejcake.

open OMA.S_oeis_a259215 PowerSeries

private abbrev Row := Fin 2 → Fin 2

private def Tr (p c : Row) : Prop := goodPattern [p 0, p 1, c 1, c 0]

private instance (p c : Row) : Decidable (Tr p c) := by unfold Tr; infer_instance

private theorem card_cons {α : Type} [Fintype α] [DecidableEq α] (n : ℕ)
    (P : (Fin (n + 1) → α) → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
      ∑ c : α, (Finset.univ.filter fun y : Fin n → α => P (Fin.cons c y)).card := by
  simp only [Finset.card_filter]
  rw [← (Fin.consEquiv fun _ => α).sum_comp, Fintype.sum_prod_type]
  simp [Fin.consEquiv]
  simp only [Finset.card_filter]
  congr! 3

private theorem valid_cons (n : ℕ) (c : Row) (y : Fin (n + 1) → Row) :
    valid (n + 1) (Fin.cons c y) ↔ Tr c (y 0) ∧ valid n y := by
  unfold valid Tr
  rw [Fin.forall_fin_succ]
  simp [Fin.cons_succ]

private theorem valid_zero (y : Fin 1 → Row) : valid 0 y := fun i => i.elim0

-- Number of continuations y of length n + 1 after the row p.
private def D (n : ℕ) (p : Row) : ℕ :=
  (Finset.univ.filter fun y : Fin (n + 1) → Row => Tr p (y 0) ∧ valid n y).card

private theorem sum_row (g : Row → ℕ) :
    ∑ c : Row, g c = g ![0, 0] + g ![0, 1] + g ![1, 0] + g ![1, 1] := by
  have h : (Finset.univ : Finset Row) = {![0, 0], ![0, 1], ![1, 0], ![1, 1]} := by decide
  rw [h, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

private def cnt : ℕ → ℕ × ℕ × ℕ
  | 0 => (1, 1, 1)
  | n + 1 => ((cnt n).1 + (cnt n).2.1, (cnt n).1, 2 * (cnt n).2.2)

private def val (n : ℕ) (p : Row) : ℕ :=
  if p = ![0, 0] then (cnt n).1 else if p = ![1, 1] then (cnt n).2.1 else (cnt n).2.2

private theorem row_cases (p : Row) :
    p = ![0, 0] ∨ p = ![0, 1] ∨ p = ![1, 0] ∨ p = ![1, 1] := by
  revert p; decide

/-- Adjacent rows agree in whether their bits match, and cannot both be 11. -/
private theorem tr_iff : ∀ p c : Row, Tr p c ↔
    (p 0 = p 1 ↔ c 0 = c 1) ∧ (p 0 = 0 ∨ p 1 = 0 ∨ c 0 = 0 ∨ c 1 = 0) := by
  decide

private theorem v00 (m : ℕ) : val m ![0, 0] = (cnt m).1 := by rw [val, if_pos rfl]
private theorem v11 (m : ℕ) : val m ![1, 1] = (cnt m).2.1 := by
  rw [val, if_neg (by decide), if_pos rfl]
private theorem v01 (m : ℕ) : val m ![0, 1] = (cnt m).2.2 := by
  rw [val, if_neg (by decide), if_neg (by decide)]
private theorem v10 (m : ℕ) : val m ![1, 0] = (cnt m).2.2 := by
  rw [val, if_neg (by decide), if_neg (by decide)]

private theorem step (m : ℕ) (p : Row) :
    ∑ c : Row, (if Tr p c then val m c else 0) = val (m + 1) p := by
  rw [sum_row]
  rcases row_cases p with rfl | rfl | rfl | rfl <;>
    simp [tr_iff, v00, v01, v10, v11, cnt] <;> omega

private theorem D_succ (n : ℕ) (p : Row) :
    D (n + 1) p = ∑ c : Row, (if Tr p c then D n c else 0) := by
  rw [D, card_cons]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [Fin.cons_zero, valid_cons]
  by_cases h : Tr p c
  · simp [h, D]
  · simp [h]

private theorem D_eq (n : ℕ) : ∀ p : Row, D n p = val (n + 1) p := by
  induction n with
  | zero =>
    intro p
    rw [← step, D, card_cons]
    refine Finset.sum_congr rfl fun c _ => ?_
    have h1 : val 0 c = 1 := by unfold val; split_ifs <;> rfl
    rw [h1]
    by_cases h : Tr p c
    · simp [h, valid_zero]
    · simp [h]
  | succ n ih =>
    intro p
    rw [D_succ, ← step]
    simp only [ih]

private def A' (m : ℕ) : ℕ := (cnt m).1 + (cnt m).2.1 + 2 * (cnt m).2.2

private theorem a_succ (n : ℕ) : a (n + 1) = A' (n + 1) := by
  rw [a, card_cons]
  have h : ∀ c : Row, (Finset.univ.filter fun y : Fin (n + 1) → Row =>
      valid (n + 1) (Fin.cons c y)).card = val (n + 1) c := by
    intro c
    rw [← D_eq]
    simp only [valid_cons, D]
  simp only [h]
  rw [sum_row]
  simp only [v00, v01, v10, v11, A']
  ring

private theorem A'_rec (m : ℕ) : A' (m + 3) + A' (m + 1) + 2 * A' m = 3 * A' (m + 2) := by
  simp only [A', cnt]
  ring

private theorem a_rec (m : ℕ) : a (m + 4) + a (m + 2) + 2 * a (m + 1) = 3 * a (m + 3) := by
  rw [a_succ, a_succ, a_succ, a_succ]
  exact A'_rec (m + 1)

private theorem a1 : a 1 = 7 := by rw [a_succ]; rfl
private theorem a2 : a 2 = 13 := by rw [a_succ]; rfl
private theorem a3 : a 3 = 24 := by rw [a_succ]; rfl

private theorem gf :
    (1 - 2 * X) * (1 - X - X ^ 2) * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (X * (7 - 8 * X - 8 * X ^ 2) : PowerSeries ℤ) := by
  set s : PowerSeries ℤ := mk (fun n => if n = 0 then 0 else (a n : ℤ)) with hs
  have hd : (1 - 2 * X) * (1 - X - X ^ 2) * s =
      s - (s * C (3 : ℤ)) * X ^ 1 + s * X ^ 2 + (s * C (2 : ℤ)) * X ^ 3 := by
    simp only [pow_one, map_ofNat]
    ring
  have hn : (X * (7 - 8 * X - 8 * X ^ 2) : PowerSeries ℤ) =
      C (7 : ℤ) * X ^ 1 - C (8 : ℤ) * X ^ 2 - C (8 : ℤ) * X ^ 3 := by
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


private noncomputable def T (n : ℕ) : ℝ :=
  2 ^ (1 + n) + (((1 - Real.sqrt 5) / 2) ^ n * (-2 + Real.sqrt 5) +
    ((1 + Real.sqrt 5) / 2) ^ n * (2 + Real.sqrt 5)) / Real.sqrt 5

private theorem T_eq (n : ℕ) :
    2 ^ (1 + n) + ((2 : ℝ) ^ (-(n : ℤ)) * ((1 - Real.sqrt 5) ^ n * (-2 + Real.sqrt 5) +
      (1 + Real.sqrt 5) ^ n * (2 + Real.sqrt 5))) / Real.sqrt 5 = T n := by
  rw [T, zpow_neg, zpow_natCast, div_pow, div_pow]
  ring

private theorem root_step (x : ℝ) (h : x ^ 2 = x + 1) (j : ℕ) :
    x ^ (j + 3) = 3 * x ^ (j + 2) - x ^ (j + 1) - 2 * x ^ j := by
  linear_combination (x ^ j * (x - 2)) * h

private theorem T_rec (j : ℕ) : T (j + 3) = 3 * T (j + 2) - T (j + 1) - 2 * T j := by
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h1 := root_step ((1 - Real.sqrt 5) / 2) (by linear_combination hs / 4) j
  have h2 := root_step ((1 + Real.sqrt 5) / 2) (by linear_combination hs / 4) j
  unfold T
  rw [h1, h2]
  ring

private theorem T_base (k : ℕ) (c : ℝ) (hc : ((1 - Real.sqrt 5) / 2) ^ k * (-2 + Real.sqrt 5) +
    ((1 + Real.sqrt 5) / 2) ^ k * (2 + Real.sqrt 5) = c * Real.sqrt 5) :
    T k = 2 ^ (1 + k) + c := by
  have h5 : Real.sqrt 5 ≠ 0 := by positivity
  rw [T, hc, mul_div_assoc, div_self h5, mul_one]

private theorem closed (m : ℕ) :
    (a (m + 1) : ℝ) = T (m + 1) ∧ (a (m + 2) : ℝ) = T (m + 2) ∧ (a (m + 3) : ℝ) = T (m + 3) := by
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  induction m with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · rw [a1, T_base 1 3 (by linear_combination 0 * hs)]; norm_num
    · rw [a2, T_base 2 5 (by linear_combination (Real.sqrt 5 / 2) * hs)]; norm_num
    · rw [a3, T_base 3 8 (by linear_combination (5 * Real.sqrt 5 / 4) * hs)]; norm_num
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨h2, h3, ?_⟩
    have hr : (a (m + 4) : ℝ) + (a (m + 2) : ℝ) + 2 * (a (m + 1) : ℝ) = 3 * (a (m + 3) : ℝ) := by
      exact_mod_cast a_rec m
    rw [show m + 1 + 3 = m + 1 + 3 from rfl, T_rec (m + 1)]
    rw [show m + 1 + 2 = m + 3 by ring] at h3 ⊢
    rw [show m + 1 + 1 = m + 2 by ring] at h2 ⊢
    rw [show m + 1 + 3 = m + 4 by ring]
    linarith

theorem OMA.solution : type_of% @OMA.S_oeis_a259215.main := by
  refine ⟨gf, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [T_eq, (closed m).1]
