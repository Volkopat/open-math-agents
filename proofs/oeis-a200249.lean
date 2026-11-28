import OMAStatements.S_oeis_a200249

namespace OMA.S_oeis_a200249

open PowerSeries Finset




lemma sum_Iio {m : ℕ} (j : Fin m) (h : Fin m → ℕ) :
    ∑ x ∈ Iio j, h x = ∑ x, if x < j then h x else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext x
  simp

lemma sum_Iio_zero {m : ℕ} (h : Fin (m + 1) → ℕ) : ∑ x ∈ Iio (0 : Fin (m + 1)), h x = 0 := by
  rw [sum_Iio]
  simp [Fin.not_lt_zero]

lemma sum_Iio_succ {m : ℕ} (t : Fin m) (h : Fin (m + 1) → ℕ) :
    ∑ x ∈ Iio t.succ, h x = h 0 + ∑ x ∈ Iio t, h x.succ := by
  rw [sum_Iio, sum_Iio, Fin.sum_univ_succ]
  simp only [Fin.succ_pos, if_true, Fin.succ_lt_succ_iff]

/-- An array is valid after a prefix with sum s (mod 6). -/
def V (s : Fin 6) {m : ℕ} (x : Fin m → Fin 6) : Prop :=
  ∀ i, (s.val + ∑ j ∈ Iio i, (x j).val) % 6 ≤ (x i).val

instance (s : Fin 6) {m : ℕ} : DecidablePred (@V s m) := fun x => by
  unfold V; infer_instance

lemma V_cons (s : Fin 6) {m : ℕ} (v : Fin 6) (x : Fin m → Fin 6) :
    V s (Fin.cons v x : Fin (m + 1) → Fin 6) ↔ s.val ≤ v.val ∧ V (s + v) x := by
  have key : ∀ t : Fin m,
      (s.val + ∑ j ∈ Iio t.succ, ((Fin.cons v x : Fin (m + 1) → Fin 6) j).val) % 6 =
      ((s + v).val + ∑ j ∈ Iio t, (x j).val) % 6 := by
    intro t
    rw [sum_Iio_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_add]
    omega
  have key0 :
      (s.val + ∑ j ∈ Iio (0 : Fin (m + 1)), ((Fin.cons v x : Fin (m + 1) → Fin 6) j).val) % 6 =
      s.val := by
    rw [sum_Iio_zero, Nat.add_zero]
    exact Nat.mod_eq_of_lt s.isLt
  constructor
  · intro h
    refine ⟨?_, fun t => ?_⟩
    · have e := h 0
      rw [key0] at e
      simpa using e
    · have e := h t.succ
      rw [key] at e
      simpa using e
  · rintro ⟨h0, h1⟩ t
    induction t using Fin.cases with
    | zero =>
      rw [key0]
      simpa using h0
    | succ t =>
      rw [key]
      simpa using h1 t

/-- W(m, s): the arrays of length m valid after a prefix with sum s. -/
def W (m : ℕ) (s : Fin 6) : ℕ := ((univ : Finset (Fin m → Fin 6)).filter (V s)).card

lemma W_zero (s : Fin 6) : W 0 s = 1 := by
  have e : (univ : Finset (Fin 0 → Fin 6)).filter (V s) = univ :=
    Finset.filter_true_of_mem (fun x _ t => Fin.elim0 t)
  rw [W, e]
  simp

lemma W_succ (m : ℕ) (s : Fin 6) :
    W (m + 1) s = ∑ v : Fin 6, if s.val ≤ v.val then W m (s + v) else 0 := by
  unfold W
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x => x 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  split_ifs with hv
  · refine Finset.card_bij' (fun x _ => Fin.tail x) (fun x' _ => Fin.cons v x') ?_ ?_ ?_ ?_
    · intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx ⊢
      have e : x = Fin.cons v (Fin.tail x) := by
        rw [← hx.2]
        exact (Fin.cons_self_tail x).symm
      have h1 := hx.1
      rw [e, V_cons] at h1
      exact h1.2
    · intro x' hx'
      simp only [mem_filter, mem_univ, true_and] at hx' ⊢
      exact ⟨(V_cons s v x').2 ⟨hv, hx'⟩, by simp⟩
    · intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx
      rw [← hx.2]
      exact Fin.cons_self_tail x
    · intro x' _
      simp
  · rw [Finset.card_eq_zero]
    ext x
    simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false, not_and]
    intro hx h0
    have e : x = Fin.cons v (Fin.tail x) := by
      rw [← h0]
      exact (Fin.cons_self_tail x).symm
    rw [e, V_cons] at hx
    exact hv hx.1

lemma a_eq (n : ℕ) : a n = W n 0 := by
  unfold a W
  congr 1
  ext x
  simp [good, V]

def T1 : Fin 6 → ℕ := ![6, 5, 4, 3, 2, 1]
def T2 : Fin 6 → ℕ := ![21, 16, 14, 15, 7, 2]
def T3 : Fin 6 → ℕ := ![75, 59, 46, 51, 29, 7]
def T4 : Fin 6 → ℕ := ![267, 208, 170, 180, 97, 29]
def T5 : Fin 6 → ℕ := ![951, 743, 601, 645, 350, 97]

/-- Every kernel computation in one theorem: the tables are W(1), ..., W(5), and the order 5
relation holds at n = 0. -/
lemma check_all : ∀ s : Fin 6,
    (∑ v : Fin 6, (if s.val ≤ v.val then 1 else 0)) = T1 s ∧
    (∑ v : Fin 6, (if s.val ≤ v.val then T1 (s + v) else 0)) = T2 s ∧
    (∑ v : Fin 6, (if s.val ≤ v.val then T2 (s + v) else 0)) = T3 s ∧
    (∑ v : Fin 6, (if s.val ≤ v.val then T3 (s + v) else 0)) = T4 s ∧
    (∑ v : Fin 6, (if s.val ≤ v.val then T4 (s + v) else 0)) = T5 s ∧
    (∑ v : Fin 6, (if s.val ≤ v.val then T5 (s + v) else 0)) =
      2 * T1 s + 7 * T2 s + 9 * T3 s + 6 * T4 s + T5 s := by
  decide +kernel

lemma W1 (s : Fin 6) : W 1 s = T1 s := by
  rw [W_succ]
  simp only [W_zero]
  exact (check_all s).1

lemma W2 (s : Fin 6) : W 2 s = T2 s := by
  rw [W_succ]
  simp only [W1]
  exact (check_all s).2.1

lemma W3 (s : Fin 6) : W 3 s = T3 s := by
  rw [W_succ]
  simp only [W2]
  exact (check_all s).2.2.1

lemma W4 (s : Fin 6) : W 4 s = T4 s := by
  rw [W_succ]
  simp only [W3]
  exact (check_all s).2.2.2.1

lemma W5 (s : Fin 6) : W 5 s = T5 s := by
  rw [W_succ]
  simp only [W4]
  exact (check_all s).2.2.2.2.1

lemma W_rec (n : ℕ) (s : Fin 6) :
    W (n + 6) s = 2 * W (n + 1) s + 7 * W (n + 2) s + 9 * W (n + 3) s + 6 * W (n + 4) s +
      W (n + 5) s := by
  induction n generalizing s with
  | zero =>
    rw [show (0 : ℕ) + 6 = 5 + 1 from rfl, W_succ]
    simp only [W5, Nat.zero_add, W1, W2, W3, W4]
    exact (check_all s).2.2.2.2.2
  | succ n ih =>
    rw [W_succ (n + 6), W_succ (n + 1), W_succ (n + 2), W_succ (n + 3), W_succ (n + 4),
      W_succ (n + 5)]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    by_cases hv : s.val ≤ v.val
    · simp only [if_pos hv]
      exact ih _
    · simp [hv]

lemma a_rec (n : ℕ) :
    a (n + 6) = 2 * a (n + 1) + 7 * a (n + 2) + 9 * a (n + 3) + 6 * a (n + 4) + a (n + 5) := by
  rw [a_eq, a_eq, a_eq, a_eq, a_eq, a_eq]
  exact W_rec n 0

lemma a_1 : a 1 = 6 := by rw [a_eq, W1]; rfl
lemma a_2 : a 2 = 21 := by rw [a_eq, W2]; rfl
lemma a_3 : a 3 = 75 := by rw [a_eq, W3]; rfl
lemma a_4 : a 4 = 267 := by rw [a_eq, W4]; rfl
lemma a_5 : a 5 = 951 := by rw [a_eq, W5]; rfl
lemma a_6 : a 6 = 3387 := by
  have h := a_rec 0
  simp only [Nat.zero_add, a_1, a_2, a_3, a_4, a_5] at h
  omega
lemma a_7 : a 7 = 12063 := by
  have h := a_rec 1
  simp only [show 1 + 6 = 7 from rfl, show 1 + 1 = 2 from rfl, show 1 + 2 = 3 from rfl,
    show 1 + 3 = 4 from rfl, show 1 + 4 = 5 from rfl, show 1 + 5 = 6 from rfl, a_2, a_3, a_4, a_5,
    a_6] at h
  omega

/-- The second order recurrence: b(m) = a(m + 3) - 3 a(m + 2) - 2 a(m + 1) vanishes, because it
satisfies the order 5 recurrence and vanishes for m = 0..4. -/
lemma rec2 : ∀ m, (a (m + 3) : ℤ) = 3 * a (m + 2) + 2 * a (m + 1) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.lt_or_ge m 5 with hm | hm
    · interval_cases m
      · simp [a_1, a_2, a_3]
      · simp [a_2, a_3, a_4]
      · simp [a_3, a_4, a_5]
      · simp [a_4, a_5, a_6]
      · simp [a_5, a_6, a_7]
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 5 := ⟨m - 5, by omega⟩
      have r0 : (a (j + 8) : ℤ) = 2 * a (j + 3) + 7 * a (j + 4) + 9 * a (j + 5) + 6 * a (j + 6) +
          a (j + 7) := by exact_mod_cast a_rec (j + 2)
      have r1 : (a (j + 7) : ℤ) = 2 * a (j + 2) + 7 * a (j + 3) + 9 * a (j + 4) + 6 * a (j + 5) +
          a (j + 6) := by exact_mod_cast a_rec (j + 1)
      have r2 : (a (j + 6) : ℤ) = 2 * a (j + 1) + 7 * a (j + 2) + 9 * a (j + 3) + 6 * a (j + 4) +
          a (j + 5) := by exact_mod_cast a_rec j
      have i0 := ih j (by omega)
      have i1 := ih (j + 1) (by omega)
      have i2 := ih (j + 2) (by omega)
      have i3 := ih (j + 3) (by omega)
      have i4 := ih (j + 4) (by omega)
      simp only [show j + 1 + 3 = j + 4 by omega, show j + 1 + 2 = j + 3 by omega,
        show j + 1 + 1 = j + 2 by omega, show j + 2 + 3 = j + 5 by omega,
        show j + 2 + 2 = j + 4 by omega, show j + 2 + 1 = j + 3 by omega,
        show j + 3 + 3 = j + 6 by omega, show j + 3 + 2 = j + 5 by omega,
        show j + 3 + 1 = j + 4 by omega, show j + 4 + 3 = j + 7 by omega,
        show j + 4 + 2 = j + 6 by omega, show j + 4 + 1 = j + 5 by omega] at i1 i2 i3 i4
      rw [show j + 5 + 3 = j + 8 by omega, show j + 5 + 2 = j + 7 by omega,
        show j + 5 + 1 = j + 6 by omega]
      linear_combination r0 - 3 * r1 - 2 * r2 + 2 * i0 + 7 * i1 + 9 * i2 + 6 * i3 + i4

/-- Barker's g.f. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    (1 - 3 * X - 2 * X ^ 2) = 3 * X * (2 + X) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - 3 * X - 2 * X ^ 2) = A - A * X ^ 1 * C 3 - A * X ^ 2 * C 2 := by
    rw [show (C (3 : ℚ) : ℚ⟦X⟧) = 3 from map_ofNat C 3, show (C (2 : ℚ) : ℚ⟦X⟧) = 2 from map_ofNat C 2]
    ring
  have e2 : (3 * X * (2 + X) : ℚ⟦X⟧) = X ^ 1 * C 6 + X ^ 2 * C 3 := by
    rw [show (C (6 : ℚ) : ℚ⟦X⟧) = 6 from map_ofNat C 6, show (C (3 : ℚ) : ℚ⟦X⟧) = 3 from map_ofNat C 3]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk]
  rcases n with _ | _ | _ | n
  · simp
  · simp [a_1]
  · simp [a_1, a_2]
    norm_num
  · have h := rec2 n
    have hq : (a (n + 3) : ℚ) = 3 * a (n + 2) + 2 * a (n + 1) := by exact_mod_cast h
    simp only [show ¬ (n + 1 + 1 + 1 = 0) by omega, show 1 ≤ n + 1 + 1 + 1 by omega,
      show ¬ (n + 1 + 1 + 1 - 1 = 0) by omega, show n + 1 + 1 + 1 - 1 = n + 2 by omega,
      show 2 ≤ n + 1 + 1 + 1 by omega, show n + 1 + 1 + 1 - 2 = n + 1 by omega,
      show ¬ (n + 1 = 0) by omega, show ¬ (n + 2 = 0) by omega, show ¬ (n + 1 + 1 + 1 = 1) by omega,
      show ¬ (n + 1 + 1 + 1 = 2) by omega, if_false, if_true,
      show n + 1 + 1 + 1 = n + 3 by omega]
    linear_combination hq

/-- The closed form of the entry, as a real function of n. -/
noncomputable def c (n : ℕ) : ℝ :=
  3 * (2 : ℝ) ^ (-2 - (n : ℤ)) * ((3 - √17) ^ n * (-5 + √17) + (3 + √17) ^ n * (5 + √17)) / √17

lemma c_rec (n : ℕ) : c (n + 2) = 3 * c (n + 1) + 2 * c n := by
  have h1 : (2 : ℝ) ^ (-2 - ((n + 1 : ℕ) : ℤ)) = (2 : ℝ) ^ (-2 - (n : ℤ)) / 2 := by
    rw [show (-2 - ((n + 1 : ℕ) : ℤ)) = (-2 - (n : ℤ)) - 1 by push_cast; ring,
      zpow_sub₀ two_ne_zero, zpow_one]
  have h2 : (2 : ℝ) ^ (-2 - ((n + 2 : ℕ) : ℤ)) = (2 : ℝ) ^ (-2 - (n : ℤ)) / 4 := by
    rw [show (-2 - ((n + 2 : ℕ) : ℤ)) = (-2 - (n : ℤ)) - 2 by push_cast; ring,
      zpow_sub₀ two_ne_zero]
    norm_num
  have hs : √17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have hu : (3 - √17) ^ 2 = 6 * (3 - √17) + 8 := by linear_combination hs
  have hw : (3 + √17) ^ 2 = 6 * (3 + √17) + 8 := by linear_combination hs
  unfold c
  rw [h1, h2, pow_add (3 - √17) n 2, pow_add (3 + √17) n 2, pow_succ (3 - √17) n,
    pow_succ (3 + √17) n, hu, hw]
  ring

lemma c_one : c 1 = 6 := by
  have hs : √17 ≠ 0 := by positivity
  unfold c
  rw [show (-2 - ((1 : ℕ) : ℤ)) = -3 by norm_num]
  field_simp
  norm_num
  ring

lemma c_two : c 2 = 21 := by
  have hs : √17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have hs0 : √17 ≠ 0 := by positivity
  unfold c
  rw [show (-2 - ((2 : ℕ) : ℤ)) = -4 by norm_num]
  field_simp
  norm_num
  linear_combination (6 * √17) * hs

/-- The closed form of the entry, for every n >= 1. -/
theorem closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℝ) = 3 * (2 : ℝ) ^ (-2 - (n : ℤ)) *
    ((3 - √17) ^ n * (-5 + √17) + (3 + √17) ^ n * (5 + √17)) / √17 := by
  have key : ∀ m, (a (m + 1) : ℝ) = c (m + 1) ∧ (a (m + 2) : ℝ) = c (m + 2) := by
    intro m
    induction m with
    | zero => exact ⟨by rw [c_one, a_1]; norm_num, by rw [c_two, a_2]; norm_num⟩
    | succ m ih =>
      refine ⟨ih.2, ?_⟩
      have h := rec2 m
      have hr : (a (m + 3) : ℝ) = 3 * a (m + 2) + 2 * a (m + 1) := by exact_mod_cast h
      rw [show m + 1 + 2 = m + 3 by omega, hr, ih.1, ih.2, show m + 3 = (m + 1) + 2 by omega,
        c_rec (m + 1)]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (key m).1

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - 3 * X - 2 * X ^ 2) =
      3 * X * (2 + X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) = 3 * (2 : ℝ) ^ (-2 - (n : ℤ)) *
      ((3 - √17) ^ n * (-5 + √17) + (3 + √17) ^ n * (5 + √17)) / √17 :=
  ⟨gf, closed⟩

end OMA.S_oeis_a200249

theorem OMA.solution : type_of% @OMA.S_oeis_a200249.main :=
  OMA.S_oeis_a200249.conjecture
