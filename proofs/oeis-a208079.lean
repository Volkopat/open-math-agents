import OMAStatements.S_oeis_a208079

open OMA.S_oeis_a208079 PowerSeries

private abbrev Col := Fin 4 → Fin 2

private def rowOK (l : List (Fin 2)) : Prop := ¬ [0, 0, 0] <:+: l ∧ ¬ [0, 0, 1] <:+: l

private def colOK (c : Col) : Prop :=
  ¬ [0, 0, 0] <:+: List.ofFn c ∧ ¬ [0, 1, 0] <:+: List.ofFn c

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
private theorem lump (cls : Col → Fin 3) (P : Col → Prop) [DecidablePred P] (g : Fin 3 → ℕ) :
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

private def cls (c : Col) : Fin 3 :=
  if (List.ofFn c).count 0 = 0 then 0 else if (List.ofFn c).count 0 = 1 then 1 else 2

private def T : Fin 3 → Fin 3 → ℕ := ![![1, 4, 4], ![1, 3, 2], ![1, 2, 1]]

private theorem hT : ∀ p, colOK p → ∀ j,
    (Finset.univ.filter fun c => (colOK c ∧ E p c) ∧ cls c = j).card = T (cls p) j := by
  decide +kernel

private theorem hK : ∀ j, (Finset.univ.filter fun c => colOK c ∧ cls c = j).card = T 0 j := by
  decide +kernel

private def w : ℕ → ℕ × ℕ × ℕ
  | 0 => (9, 9, 9)
  | m + 1 => ((w m).1 + 4 * (w m).2.1 + 4 * (w m).2.2,
      (w m).1 + 3 * (w m).2.1 + 2 * (w m).2.2, (w m).1 + 2 * (w m).2.1 + (w m).2.2)

private def wf (m : ℕ) : Fin 3 → ℕ := ![(w m).1, (w m).2.1, (w m).2.2]

private theorem wf_succ (m : ℕ) (k : Fin 3) : wf (m + 1) k = ∑ i, T k i * wf m i := by
  fin_cases k <;> simp [wf, w, T, Fin.sum_univ_three]

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

private theorem lumpT (m : ℕ) (p : Col) (hp : colOK p) (g : Fin 3 → ℕ)
    (hg : ∀ k, g k = wf m k) :
    ∑ c : Col, (if colOK c ∧ E p c then g (cls c) else 0) = wf (m + 1) (cls p) := by
  rw [lump, wf_succ]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hT p hp j, hg]

private theorem D_eq (m : ℕ) : ∀ p, colOK p → D m p = wf (m + 1) (cls p) := by
  induction m with
  | zero =>
    intro p hp
    rw [D_zero, ← lumpT 0 p hp (fun _ => 9) (fun k => by fin_cases k <;> rfl)]
  | succ m ih =>
    intro p hp
    rw [D_succ, ← lumpT (m + 1) p hp (wf (m + 1)) (fun _ => rfl)]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases h : colOK c ∧ E p c
    · rw [if_pos h, if_pos h, ih c h.1]
    · rw [if_neg h, if_neg h]

private theorem a_succ3 (m : ℕ) : a (m + 3) = (w (m + 2)).1 := by
  rw [a_eq_V, card_cons]
  rw [Finset.sum_congr rfl (g := fun c => if colOK c then wf (m + 1) (cls c) else 0)
    (fun c _ => by
      simp only [V_cons]
      by_cases h : colOK c
      · rw [if_pos h, ← D_eq m c h]; simp [h, D]
      · simp [h])]
  rw [lump, show (w (m + 2)).1 = wf (m + 2) 0 from rfl, wf_succ]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hK]

private theorem a1 : a 1 = 9 := by decide +kernel
private theorem a2 : a 2 = 81 := by decide +kernel

private theorem a_succ (n : ℕ) : a (n + 1) = (w n).1 := by
  rcases n with _ | _ | m
  · exact a1
  · exact a2
  · exact a_succ3 m

private theorem a_rec (m : ℕ) : a (m + 4) + a (m + 1) = 5 * a (m + 3) + 5 * a (m + 2) := by
  rw [a_succ, a_succ, a_succ, a_succ]
  simp only [w]
  ring

private theorem a3 : a 3 = 441 := by rw [a_succ]; rfl


private theorem gf :
    (1 + X) * (1 - 6 * X + X ^ 2) * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (9 * X * (1 + 4 * X - X ^ 2) : PowerSeries ℤ) := by
  set s : PowerSeries ℤ := mk (fun n => if n = 0 then 0 else (a n : ℤ)) with hs
  have hd : (1 + X) * (1 - 6 * X + X ^ 2) * s =
      s - (s * C (5 : ℤ)) * X ^ 1 - (s * C (5 : ℤ)) * X ^ 2 + s * X ^ 3 := by
    simp only [pow_one, map_ofNat]
    ring
  have hn : (9 * X * (1 + 4 * X - X ^ 2) : PowerSeries ℤ) =
      C (9 : ℤ) * X ^ 1 + C (36 : ℤ) * X ^ 2 - C (9 : ℤ) * X ^ 3 := by
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

private noncomputable def R (n : ℕ) : ℝ :=
  9 / 4 * (2 * (-1) ^ n + (3 - 2 * Real.sqrt 2) ^ n + (3 + 2 * Real.sqrt 2) ^ n)

private theorem root_step (x : ℝ) (h : x ^ 2 = 6 * x - 1) (j : ℕ) :
    x ^ (j + 3) = 5 * x ^ (j + 2) + 5 * x ^ (j + 1) - x ^ j := by
  linear_combination (x ^ j * (x + 1)) * h

private theorem R_rec (j : ℕ) : R (j + 3) = 5 * R (j + 2) + 5 * R (j + 1) - R j := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h1 := root_step (3 - 2 * Real.sqrt 2) (by linear_combination 4 * hs) j
  have h2 := root_step (3 + 2 * Real.sqrt 2) (by linear_combination 4 * hs) j
  unfold R
  rw [h1, h2]
  ring

private theorem closed (m : ℕ) :
    (a (m + 1) : ℝ) = R (m + 1) ∧ (a (m + 2) : ℝ) = R (m + 2) ∧ (a (m + 3) : ℝ) = R (m + 3) := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  induction m with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · rw [a1, R]; push_cast; linear_combination 0 * hs
    · rw [a2, R]; push_cast; linear_combination (-18) * hs
    · rw [a3, R]; push_cast; linear_combination (-162) * hs
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨h2, h3, ?_⟩
    have hr : (a (m + 4) : ℝ) + (a (m + 1) : ℝ) = 5 * (a (m + 3) : ℝ) + 5 * (a (m + 2) : ℝ) := by
      exact_mod_cast a_rec m
    rw [show m + 1 + 3 = m + 1 + 3 from rfl, R_rec (m + 1)]
    rw [show m + 1 + 2 = m + 3 by ring] at h3 ⊢
    rw [show m + 1 + 1 = m + 2 by ring] at h2 ⊢
    rw [show m + 1 + 3 = m + 4 by ring]
    linarith

theorem OMA.solution : type_of% @OMA.S_oeis_a208079.main := by
  refine ⟨gf, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [(closed m).1, R]

