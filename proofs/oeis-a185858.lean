import OMAStatements.S_oeis_a185858

open OMA.S_oeis_a185858 PowerSeries

private abbrev Row := Fin 3 → Fin 2

-- Only vertical neighbours exist (one subblock per band of three rows).
private def VV (n : ℕ) (A : Fin (n + 2) → Row) : Prop :=
  ∀ i, i + 1 < n → trace A i 0 ≠ trace A (i + 1) 0

private noncomputable instance (n : ℕ) : DecidablePred (VV n) := Classical.decPred _

private theorem valid_iff (n : ℕ) (A : Fin (n + 2) → Row) : valid n A ↔ VV n A := by
  constructor
  · intro h i hi
    exact h ⟨i, by omega⟩ 0 ⟨i + 1, hi⟩ 0 (Or.inr ⟨rfl, Or.inl rfl⟩)
  · intro h i j i' j' hn
    have := i.isLt; have := i'.isLt; have := j.isLt; have := j'.isLt
    have hj : (j : ℕ) = 0 := by omega
    have hj' : (j' : ℕ) = 0 := by omega
    rw [hj, hj']
    rcases hn with ⟨_, h1 | h1⟩ | ⟨_, h1 | h1⟩
    · omega
    · omega
    · rw [← h1]; exact h i (by omega)
    · rw [← h1]; exact (h i' (by omega)).symm

-- The trace of the first subblock of three given rows.
private def tr (r c d : Row) : ℕ := (r 0).val + (c 1).val + (d 2).val

private theorem entry_shift {k : ℕ} (r : Row) (y : Fin (k + 2) → Row) (i j : ℕ) :
    entry (Fin.cons r y : Fin (k + 1 + 2) → Row) (i + 1) j = entry y i j := by
  unfold entry
  by_cases h : i < k + 2 ∧ j < 3
  · rw [dif_pos (by omega), dif_pos h]; rfl
  · rw [dif_neg (by omega), dif_neg h]

private theorem trace_shift {k : ℕ} (r : Row) (y : Fin (k + 2) → Row) (i j : ℕ) :
    trace (Fin.cons r y : Fin (k + 1 + 2) → Row) (i + 1) j = trace y i j := by
  unfold trace
  rw [show i + 1 + 2 = (i + 2) + 1 by ring, entry_shift, entry_shift, entry_shift]

private theorem trace0 {k : ℕ} (r c d : Row) (w : Fin k → Row) :
    trace (Fin.cons r (Fin.cons c (Fin.cons d w)) : Fin (k + 1 + 2) → Row) 0 0 = tr r c d := by
  unfold trace entry
  rw [dif_pos (by omega), dif_pos (by omega), dif_pos (by omega)]
  rfl

private theorem VV_cons (m : ℕ) (r c d e : Row) (z : Fin m → Row) :
    VV (m + 2) (Fin.cons r (Fin.cons c (Fin.cons d (Fin.cons e z)))) ↔
      tr r c d ≠ tr c d e ∧ VV (m + 1) (Fin.cons c (Fin.cons d (Fin.cons e z))) := by
  unfold VV
  constructor
  · intro h
    refine ⟨?_, fun i hi => ?_⟩
    · have := h 0 (by omega)
      rwa [trace0, trace_shift, trace0] at this
    · have := h (i + 1) (by omega)
      rwa [trace_shift, trace_shift] at this
  · rintro ⟨h0, h⟩ i hi
    cases i with
    | zero => rw [trace0, trace_shift, trace0]; exact h0
    | succ i => rw [trace_shift, trace_shift]; exact h i (by omega)

private theorem card_cons {α : Type} [Fintype α] [DecidableEq α] (n : ℕ)
    (P : (Fin (n + 1) → α) → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
      ∑ c : α, (Finset.univ.filter fun y : Fin n → α => P (Fin.cons c y)).card := by
  simp only [Finset.card_filter]
  rw [← (Fin.consEquiv fun _ => α).sum_comp, Fintype.sum_prod_type]
  simp [Fin.consEquiv]
  simp only [Finset.card_filter]
  congr! 3

private theorem lump {α : Type} [Fintype α] {k : ℕ} (f : α → Fin k) (P : α → Prop)
    [DecidablePred P] (g : Fin k → ℕ) :
    ∑ c : α, (if P c then g (f c) else 0) =
      ∑ j, (Finset.univ.filter fun c => P c ∧ f c = j).card * g j := by
  rw [← Finset.sum_fiberwise Finset.univ f]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_congr rfl (g := fun c => if P c then g j else 0)
    (fun c hc => by rw [(Finset.mem_filter.1 hc).2])]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul,
    Finset.filter_filter]
  congr 2
  ext c
  simp [and_comm]

private abbrev St := Row × Row × Row

private def Cnd (s : St) (e : Row) : Prop := tr s.1 s.2.1 s.2.2 ≠ tr s.2.1 s.2.2 e

private instance (s : St) : DecidablePred (Cnd s) := fun e => by unfold Cnd; infer_instance

-- The class of three consecutive rows: their trace t, the partial trace p of the last two
-- rows and the entry q of the last row that the next two traces see, lumped to 7 classes.
private def tab : List (Fin 7) :=
  [2, 0, 5, 5, 4, 6, 1, 3, 0, 2, 4, 6, 6, 4, 2, 0, 3, 1, 6, 4, 5, 5, 0, 2]

private def cls (s : St) : Fin 7 :=
  tab.getD (6 * tr s.1 s.2.1 s.2.2 + 2 * ((s.2.1 0).val + (s.2.2 1).val) + (s.2.2 0).val) 0

private def T : Fin 7 → Fin 7 → ℕ :=
  ![![1, 0, 1, 0, 1, 0, 1], ![1, 0, 1, 0, 0, 2, 0], ![1, 1, 1, 1, 0, 0, 0],
    ![0, 0, 0, 0, 1, 2, 1], ![1, 0, 1, 0, 2, 2, 2], ![2, 1, 2, 1, 1, 0, 1],
    ![2, 1, 2, 1, 0, 2, 0]]

private def K : Fin 7 → ℕ := ![112, 48, 112, 48, 64, 64, 64]

private theorem hT : ∀ (s : St) (j : Fin 7),
    (Finset.univ.filter fun e => Cnd s e ∧ cls (s.2.1, s.2.2, e) = j).card = T (cls s) j := by
  decide +kernel

private theorem hK : ∀ j : Fin 7, (Finset.univ.filter fun s : St => True ∧ cls s = j).card = K j := by
  decide +kernel

private def g : ℕ → Fin 7 → ℕ
  | 0 => fun _ => 1
  | m + 1 => fun k => ∑ i, T k i * g m i

private noncomputable def G (m : ℕ) (s : St) : ℕ :=
  (Finset.univ.filter fun z : Fin m → Row =>
    VV (m + 1) (Fin.cons s.1 (Fin.cons s.2.1 (Fin.cons s.2.2 z)))).card

private theorem G_succ (m : ℕ) (s : St) :
    G (m + 1) s = ∑ e : Row, if Cnd s e then G m (s.2.1, s.2.2, e) else 0 := by
  rw [G, card_cons]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [VV_cons]
  by_cases h : Cnd s e
  · rw [if_pos h]; simp only [Cnd] at h; simp [h, G]
  · rw [if_neg h]; simp only [Cnd, not_not] at h; simp [h]

private theorem G_eq (m : ℕ) : ∀ s, G m s = g m (cls s) := by
  induction m with
  | zero =>
    intro s
    simp [G, VV, g]
  | succ m ih =>
    intro s
    rw [G_succ, Finset.sum_congr rfl (g := fun e => if Cnd s e then
        g m (cls (s.2.1, s.2.2, e)) else 0) (fun e _ => by rw [ih]),
      lump (fun e => cls (s.2.1, s.2.2, e)), g]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hT, mul_comm]

private def h (m : ℕ) : ℕ := ∑ j, K j * g m j

private theorem card_eq (m : ℕ) : (Finset.univ.filter (valid (m + 1))).card = h m := by
  rw [Finset.filter_congr (fun A _ => valid_iff (m + 1) A)]
  show (Finset.univ.filter fun A : Fin (m + 2 + 1) → Row => VV (m + 1) A).card = h m
  rw [card_cons]
  simp only [card_cons (n := m + 1)]
  simp only [card_cons (n := m)]
  rw [show (∑ r : Row, ∑ c : Row, ∑ d : Row, (Finset.univ.filter fun z : Fin m → Row =>
      VV (m + 1) (Fin.cons r (Fin.cons c (Fin.cons d z)))).card) = ∑ s : St, G m s by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Fintype.sum_prod_type]
    rfl]
  rw [Finset.sum_congr rfl (g := fun s => if True then g m (cls s) else 0)
    (fun s _ => by rw [G_eq, if_pos trivial]), lump, h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hK]

private theorem a_succ (m : ℕ) : a (m + 1) = h m / 128 := by
  rw [a, card_eq]

private theorem h_rec (m : ℕ) : h (m + 2) = 4 * h (m + 1) + 9 * h m := by
  simp only [h, g, Fin.sum_univ_seven, K, T]
  simp
  ring

private theorem h_dvd (m : ℕ) : 128 ∣ h m ∧ 128 ∣ h (m + 1) := by
  induction m with
  | zero => exact ⟨⟨4, by decide⟩, ⟨22, by decide⟩⟩
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    rw [h_rec]
    exact Nat.dvd_add (Dvd.dvd.mul_left ih.2 _) (Dvd.dvd.mul_left ih.1 _)

private theorem a_rec (m : ℕ) : a (m + 3) = 4 * a (m + 2) + 9 * a (m + 1) := by
  rw [a_succ, a_succ, a_succ, h_rec]
  have h1 := (h_dvd m).1
  have h2 := (h_dvd m).2
  omega

private theorem a1 : a 1 = 4 := by rw [a_succ]; decide
private theorem a2 : a 2 = 22 := by rw [a_succ]; decide


private theorem gf :
    (1 - 4 * X - 9 * X ^ 2) * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (2 * X * (2 + 3 * X) : PowerSeries ℤ) := by
  set s : PowerSeries ℤ := mk (fun n => if n = 0 then 0 else (a n : ℤ)) with hs
  have hd : (1 - 4 * X - 9 * X ^ 2) * s =
      s - (s * C (4 : ℤ)) * X ^ 1 - (s * C (9 : ℤ)) * X ^ 2 := by
    simp only [pow_one, map_ofNat]
    ring
  have hn : (2 * X * (2 + 3 * X) : PowerSeries ℤ) = C (4 : ℤ) * X ^ 1 + C (6 : ℤ) * X ^ 2 := by
    simp only [pow_one, map_ofNat]
    ring
  rw [hd, hn]
  ext n
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_mul_C, coeff_C, hs, coeff_mk]
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ 3 ≤ n) with h | h | h | h
  · subst h; simp
  · subst h; simp [a1]
  · subst h; simp [a1, a2]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have := a_rec m
    simp only [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega]
    simp
    omega

private noncomputable def R (n : ℕ) : ℝ :=
  ((2 - Real.sqrt 13) ^ n * (-4 + Real.sqrt 13) + (2 + Real.sqrt 13) ^ n * (4 + Real.sqrt 13)) /
    (3 * Real.sqrt 13)

private theorem R_rec (j : ℕ) : R (j + 2) = 4 * R (j + 1) + 9 * R j := by
  have hs : Real.sqrt 13 ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  have step : ∀ x : ℝ, x ^ 2 = 4 * x + 9 → x ^ (j + 2) = 4 * x ^ (j + 1) + 9 * x ^ j :=
    fun x h => by linear_combination x ^ j * h
  have h1 := step (2 - Real.sqrt 13) (by linear_combination hs)
  have h2 := step (2 + Real.sqrt 13) (by linear_combination hs)
  unfold R
  rw [h1, h2]
  ring

private theorem R_base (k : ℕ) (c : ℝ) (hc : (2 - Real.sqrt 13) ^ k * (-4 + Real.sqrt 13) +
    (2 + Real.sqrt 13) ^ k * (4 + Real.sqrt 13) = c * Real.sqrt 13) : R k = c / 3 := by
  have h5 : Real.sqrt 13 ≠ 0 := by positivity
  rw [R, hc]
  field_simp

private theorem closed (m : ℕ) : (a (m + 1) : ℝ) = R (m + 1) ∧ (a (m + 2) : ℝ) = R (m + 2) := by
  have hs : Real.sqrt 13 ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [a1, R_base 1 12 (by linear_combination 0 * hs)]; norm_num
    · rw [a2, R_base 2 66 (by linear_combination (2 * Real.sqrt 13) * hs)]; norm_num
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨h2, ?_⟩
    have hr : (a (m + 3) : ℝ) = 4 * (a (m + 2) : ℝ) + 9 * (a (m + 1) : ℝ) := by
      exact_mod_cast a_rec m
    rw [show m + 1 + 2 = m + 1 + 2 from rfl, R_rec (m + 1), show m + 1 + 1 = m + 2 by ring,
      show m + 1 + 2 = m + 3 by ring, hr, h1, h2]

theorem OMA.solution : type_of% @OMA.S_oeis_a185858.main := by
  refine ⟨gf, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [(closed m).1, R]

