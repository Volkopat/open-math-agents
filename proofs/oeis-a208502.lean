import OMAStatements.S_oeis_a208502

open OMA.S_oeis_a208502 PowerSeries

private abbrev Col := Fin 4 → Fin 2

private def rowOK (l : List (Fin 2)) : Prop := ¬ [0, 0, 0] <:+: l ∧ ¬ [0, 0, 1] <:+: l

private def colOK (c : Col) : Prop :=
  ¬ [0, 1, 0] <:+: List.ofFn c ∧ ¬ [1, 1, 1] <:+: List.ofFn c

private instance : DecidablePred colOK := fun c => by unfold colOK; infer_instance

-- Two neighbouring columns are compatible when no row has two zeros there.
private def E (p c : Col) : Prop := ∀ i, ¬ (p i = 0 ∧ c i = 0)

private instance (p c : Col) : Decidable (E p c) := by unfold E; infer_instance

-- Column-major validity.
private def V (n : ℕ) (x : Fin n → Col) : Prop :=
  (∀ i : Fin 4, rowOK (List.ofFn fun j => x j i)) ∧ ∀ j, colOK (x j)

private instance (n : ℕ) : DecidablePred (V n) := fun x => by
  unfold V rowOK; infer_instance

private theorem a_eq_V (n : ℕ) : a n = (Finset.univ.filter (V n)).card := by
  rw [a]
  refine Finset.card_equiv (Equiv.piComm fun _ _ => Fin 2) fun A => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, valid, V, rowOK, colOK]
  rfl

private theorem inf3 (x y z a b e : Fin 2) (r : List (Fin 2)) :
    [x, y, z] <:+: a :: b :: e :: r ↔ (x = a ∧ y = b ∧ z = e) ∨ [x, y, z] <:+: b :: e :: r := by
  rw [List.infix_cons_iff]
  simp [List.cons_prefix_cons]

private theorem rowOK_cons3 (a b e : Fin 2) (r : List (Fin 2)) :
    rowOK (a :: b :: e :: r) ↔ ¬ (a = 0 ∧ b = 0) ∧ rowOK (b :: e :: r) := by
  unfold rowOK
  rw [inf3, inf3]
  have he : e = 0 ∨ e = 1 := by fin_cases e <;> simp
  simp only [@eq_comm _ (0 : Fin 2) a, @eq_comm _ (0 : Fin 2) b]
  rcases he with rfl | rfl <;> simp <;> tauto

private theorem rowOK_two (a b : Fin 2) : rowOK [a, b] := by
  unfold rowOK
  constructor <;> intro h <;> have := h.length_le <;> simp at this

private theorem V_cons (m : ℕ) (c : Col) (y : Fin (m + 2) → Col) :
    V (m + 3) (Fin.cons c y) ↔ colOK c ∧ E c (y 0) ∧ V (m + 2) y := by
  have hrow : ∀ i, List.ofFn (fun j => (Fin.cons c y : Fin (m + 3) → Col) j i) =
      c i :: y 0 i :: y 1 i :: List.ofFn (fun j : Fin m => y j.succ.succ i) := by
    intro i; simp [List.ofFn_succ]
  have hrowy : ∀ i, List.ofFn (fun j => y j i) =
      y 0 i :: y 1 i :: List.ofFn (fun j : Fin m => y j.succ.succ i) := by
    intro i; simp [List.ofFn_succ]
  simp only [V, hrow, hrowy, rowOK_cons3, E, Fin.forall_fin_succ (P := fun j => colOK _),
    Fin.cons_zero, Fin.cons_succ, forall_and]
  tauto

private theorem V_two (y : Fin 2 → Col) : V 2 y ↔ colOK (y 0) ∧ colOK (y 1) := by
  simp [V, List.ofFn_succ, rowOK_two, Fin.forall_fin_two]

private theorem card_cons {α : Type} [Fintype α] [DecidableEq α] (n : ℕ)
    (P : (Fin (n + 1) → α) → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
      ∑ c : α, (Finset.univ.filter fun y : Fin n → α => P (Fin.cons c y)).card := by
  simp only [Finset.card_filter]
  rw [← (Fin.consEquiv fun _ => α).sum_comp, Fintype.sum_prod_type]
  simp [Fin.consEquiv]
  simp only [Finset.card_filter]
  congr! 3

-- Lumping a sum over columns by a class function.
private theorem lump {k : ℕ} (cls : Col → Fin k) (P : Col → Prop) [DecidablePred P]
    (g : Fin k → ℕ) :
    ∑ c : Col, (if P c then g (cls c) else 0) =
      ∑ j, (Finset.univ.filter fun c => P c ∧ cls c = j).card * g j := by
  rw [← Finset.sum_fiberwise Finset.univ cls]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_congr rfl (g := fun c => if P c then g j else 0)
    (fun c hc => by rw [(Finset.mem_filter.1 hc).2])]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul,
    Finset.filter_filter]
  congr 2
  ext c
  simp [and_comm]

private def cls (c : Col) : Fin 5 :=
  if c ∈ [![0, 0, 0, 0], ![0, 0, 0, 1], ![1, 0, 0, 0]] then 0
  else if c = ![1, 0, 0, 1] then 1
  else if c ∈ [![0, 0, 1, 1], ![1, 1, 0, 0]] then 2
  else if c = ![0, 1, 1, 0] then 3 else 4

private def T : Fin 5 → Fin 5 → ℕ :=
  ![![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 1, 0, 1], ![0, 1, 0, 0, 2], ![0, 0, 1, 1, 1]]

private def K : Fin 5 → ℕ := ![3, 1, 2, 1, 2]

private theorem hT : ∀ p, colOK p → ∀ j,
    (Finset.univ.filter fun c => (colOK c ∧ E p c) ∧ cls c = j).card = T (cls p) j := by
  decide +kernel

private theorem hK : ∀ j, (Finset.univ.filter fun c => colOK c ∧ cls c = j).card = K j := by
  decide +kernel

private def wf : ℕ → Fin 5 → ℕ
  | 0 => fun _ => 9
  | m + 1 => fun k => ∑ i, T k i * wf m i

private theorem wf_succ (m : ℕ) (k : Fin 5) : wf (m + 1) k = ∑ i, T k i * wf m i := rfl

private def D (m : ℕ) (p : Col) : ℕ :=
  (Finset.univ.filter fun y : Fin (m + 2) → Col => E p (y 0) ∧ V (m + 2) y).card

private theorem D_zero (p : Col) : D 0 p = ∑ c : Col, if colOK c ∧ E p c then 9 else 0 := by
  rw [D]
  show (Finset.univ.filter fun y : Fin 2 → Col => E p (y 0) ∧ V 2 y).card = _
  rw [card_cons]
  refine Finset.sum_congr rfl fun c _ => ?_
  have h9 : (Finset.univ.filter fun z : Fin 1 → Col => colOK (z 0)).card = 9 := by
    decide +kernel
  simp only [Fin.cons_zero, V_two, Fin.cons_one]
  by_cases h1 : colOK c <;> by_cases h2 : E p c <;> simp [h1, h2, h9]

private theorem D_succ (m : ℕ) (p : Col) :
    D (m + 1) p = ∑ c : Col, if colOK c ∧ E p c then D m c else 0 := by
  rw [D, card_cons]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [Fin.cons_zero, V_cons]
  by_cases h1 : colOK c <;> by_cases h2 : E p c <;> simp [h1, h2, D]

private theorem lumpT (m : ℕ) (p : Col) (hp : colOK p) (g : Fin 5 → ℕ)
    (hg : ∀ k, g k = wf m k) :
    ∑ c : Col, (if colOK c ∧ E p c then g (cls c) else 0) = wf (m + 1) (cls p) := by
  rw [lump, wf_succ]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hT p hp j, hg]

private theorem D_eq (m : ℕ) : ∀ p, colOK p → D m p = wf (m + 1) (cls p) := by
  induction m with
  | zero =>
    intro p hp
    rw [D_zero, ← lumpT 0 p hp (fun _ => 9) (fun _ => rfl)]
  | succ m ih =>
    intro p hp
    rw [D_succ, ← lumpT (m + 1) p hp (wf (m + 1)) (fun _ => rfl)]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases h : colOK c ∧ E p c
    · rw [if_pos h, if_pos h, ih c h.1]
    · rw [if_neg h, if_neg h]

private theorem a_succ3 (m : ℕ) : a (m + 3) = ∑ j, K j * wf (m + 1) j := by
  rw [a_eq_V, card_cons]
  rw [Finset.sum_congr rfl (g := fun c => if colOK c then wf (m + 1) (cls c) else 0)
    (fun c _ => by
      simp only [V_cons]
      by_cases h : colOK c
      · rw [if_pos h, ← D_eq m c h]; simp [h, D]
      · simp [h])]
  rw [lump]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hK]

private theorem a1 : a 1 = 9 := by decide +kernel
private theorem a2 : a 2 = 81 := by decide +kernel
private theorem a3 : a 3 = 126 := by rw [a_succ3]; rfl
private theorem a4 : a 4 = 324 := by rw [a_succ3]; rfl

private theorem a_rec (m : ℕ) : a (m + 5) = a (m + 4) + 4 * a (m + 3) := by
  rw [show m + 5 = m + 2 + 3 by ring, show m + 4 = m + 1 + 3 by ring, a_succ3, a_succ3, a_succ3]
  simp only [Fin.sum_univ_five, wf_succ, K, T]
  simp
  ring

private theorem gf :
    (1 - X - 4 * X ^ 2) * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (9 * X * (1 + 8 * X + X ^ 2 - 14 * X ^ 3) : PowerSeries ℤ) := by
  set s : PowerSeries ℤ := mk (fun n => if n = 0 then 0 else (a n : ℤ)) with hs
  have hd : (1 - X - 4 * X ^ 2) * s = s - s * X ^ 1 - (s * C (4 : ℤ)) * X ^ 2 := by
    simp only [pow_one, map_ofNat]
    ring
  have hn : (9 * X * (1 + 8 * X + X ^ 2 - 14 * X ^ 3) : PowerSeries ℤ) =
      C (9 : ℤ) * X ^ 1 + C (72 : ℤ) * X ^ 2 + C (9 : ℤ) * X ^ 3 - C (126 : ℤ) * X ^ 4 := by
    simp only [pow_one, map_ofNat]
    ring
  rw [hd, hn]
  ext n
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_mul_C, coeff_C, hs, coeff_mk]
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n) with h | h | h | h | h | h
  · subst h; simp
  · subst h; simp [a1]
  · subst h; simp [a1, a2]
  · subst h; simp [a1, a2, a3]
  · subst h; simp [a2, a3, a4]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    have := a_rec m
    simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega]
    simp
    omega

private noncomputable def R (n : ℕ) : ℝ :=
  9 / 64 * (((1 - Real.sqrt 17) / 2) ^ n * (-109 + 27 * Real.sqrt 17) +
    ((1 + Real.sqrt 17) / 2) ^ n * (109 + 27 * Real.sqrt 17)) / Real.sqrt 17

private theorem R_eq (n : ℕ) :
    9 * (2 : ℝ) ^ (-6 - (n : ℤ)) * ((1 - Real.sqrt 17) ^ n * (-109 + 27 * Real.sqrt 17) +
      (1 + Real.sqrt 17) ^ n * (109 + 27 * Real.sqrt 17)) / Real.sqrt 17 = R n := by
  rw [show (-6 - (n : ℤ)) = -((6 + n : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
    pow_add, R, div_pow, div_pow]
  ring

private theorem R_rec (j : ℕ) : R (j + 2) = R (j + 1) + 4 * R j := by
  have hs : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have step : ∀ x : ℝ, x ^ 2 = x + 4 → x ^ (j + 2) = x ^ (j + 1) + 4 * x ^ j :=
    fun x h => by linear_combination x ^ j * h
  have h1 := step ((1 - Real.sqrt 17) / 2) (by linear_combination hs / 4)
  have h2 := step ((1 + Real.sqrt 17) / 2) (by linear_combination hs / 4)
  unfold R
  rw [h1, h2]
  ring

private theorem R_base (k : ℕ) (c : ℝ) (hc : ((1 - Real.sqrt 17) / 2) ^ k * (-109 + 27 * Real.sqrt 17) +
    ((1 + Real.sqrt 17) / 2) ^ k * (109 + 27 * Real.sqrt 17) = c * Real.sqrt 17) :
    R k = 9 / 64 * c := by
  have h5 : Real.sqrt 17 ≠ 0 := by positivity
  rw [R, hc]
  field_simp

private theorem closed (m : ℕ) : (a (m + 3) : ℝ) = R (m + 3) ∧ (a (m + 4) : ℝ) = R (m + 4) := by
  have hs : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [a3, R_base 3 896 (by linear_combination (95 * Real.sqrt 17 / 2) * hs)]; norm_num
    · rw [a4, R_base 4 2304 (by
        linear_combination (27 * Real.sqrt 17 ^ 3 / 8 + 1057 * Real.sqrt 17 / 8) * hs)]
      norm_num
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨h2, ?_⟩
    have hr : (a (m + 5) : ℝ) = (a (m + 4) : ℝ) + 4 * (a (m + 3) : ℝ) := by
      exact_mod_cast a_rec m
    rw [show m + 1 + 4 = m + 3 + 2 by ring, R_rec, show m + 1 + 3 = m + 4 by ring]
    rw [show m + 3 + 1 = m + 4 by ring, show m + 3 + 2 = m + 5 by ring, hr, h1, h2]

theorem OMA.solution : type_of% @OMA.S_oeis_a208502.main := by
  refine ⟨gf, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [R_eq, (closed m).1]

