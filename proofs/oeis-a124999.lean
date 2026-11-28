import OMAStatements.S_oeis_a124999

-- Problem: A124999: Number of base 5 circular n-digit numbers with adjacent digits differing by 3 or less.
-- Upstream: formal-conjectures statements/oeis-a124999.lean:0 (declaration OMA.S_oeis_a124999.main)
-- Credit: @minimumnz (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.Circ

variable {k : ℕ}

def W (A : Matrix (Fin k) (Fin k) ℤ) : (m : ℕ) → Fin k → (Fin m → Fin k) → Fin k → ℤ
  | 0, x, _, y => A x y
  | m + 1, x, t, y => A x (t 0) * W A m (t 0) (Fin.tail t) y

theorem W_sum (A : Matrix (Fin k) (Fin k) ℤ) : ∀ (m : ℕ) (x y : Fin k),
    ∑ t : Fin m → Fin k, W A m x t y = (A ^ (m + 1)) x y := by
  intro m
  induction m with
  | zero => intro x y; simp [W]
  | succ m ih =>
    intro x y
    rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => Fin k)).sum_comp, Fintype.sum_prod_type,
      pow_succ' A (m + 1), Matrix.mul_apply]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← ih z y, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp [W, Fin.consEquiv]

theorem cyc_prod (A : Matrix (Fin k) (Fin k) ℤ) : ∀ (m : ℕ) (s : Fin (m + 1) → Fin k) (y : Fin k),
    ∏ i : Fin (m + 1), A (s i) (if h : i.val + 1 < m + 1 then s ⟨i.val + 1, h⟩ else y)
      = W A m (s 0) (Fin.tail s) y := by
  intro m
  induction m with
  | zero => intro s y; simp [W]
  | succ m ih =>
    intro s y
    rw [Fin.prod_univ_succ, W, ← ih (Fin.tail s) y]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases h : i.val + 1 < m + 1
    · have h' : (i.succ).val + 1 < m + 1 + 1 := by simp; omega
      rw [dif_pos h, dif_pos h']
      rfl
    · have h' : ¬ (i.succ).val + 1 < m + 1 + 1 := by simp; omega
      rw [dif_neg h, dif_neg h']
      rfl

theorem card_eq_trace (A : Matrix (Fin k) (Fin k) ℤ) (R : Fin k → Fin k → Prop) [DecidableRel R]
    (hA : ∀ x y, A x y = if R x y then 1 else 0) (m : ℕ) :
    (((Finset.univ : Finset (Fin (m + 1) → Fin k)).filter (fun s =>
      ∀ i : Fin (m + 1), R (s i)
        (s ⟨(i.val + 1) % (m + 1), Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩))).card : ℤ)
      = Matrix.trace (A ^ (m + 1)) := by
  rw [Finset.card_filter]
  push_cast
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  simp_rw [← W_sum A m]
  rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => Fin k)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun t _ => ?_
  have key := cyc_prod A m (Fin.cons x t) x
  simp only [Fin.cons_zero, Fin.tail_cons] at key
  rw [← key]
  simp only [hA]
  rw [Finset.prod_ite_zero]
  simp only [Finset.prod_const_one, Fin.consEquiv, Equiv.coe_fn_mk]
  refine if_congr ?_ rfl rfl
  refine forall_congr' fun i => ?_
  simp only [Finset.mem_univ, forall_true_left]
  by_cases h : i.val + 1 < m + 1
  · rw [dif_pos h]
    have : (i.val + 1) % (m + 1) = i.val + 1 := Nat.mod_eq_of_lt h
    simp only [this]
  · rw [dif_neg h]
    have : (i.val + 1) % (m + 1) = 0 := by
      have : i.val + 1 = m + 1 := by omega
      rw [this]; exact Nat.mod_self _
    simp only [this]
    rfl

end OMA.Circ

namespace OMA.P124999
open OMA.S_oeis_a124999

def A : Matrix (Fin 5) (Fin 5) ℤ := fun x y => if adjOk x y then 1 else 0

theorem a_eq (m : ℕ) : (a (m + 1) : ℤ) = Matrix.trace (A ^ (m + 1)) :=
  OMA.Circ.card_eq_trace A adjOk (fun _ _ => rfl) m

theorem a0 : a 0 = 1 := by decide

set_option maxRecDepth 100000 in
theorem Arec : A ^ 4 = (5 : ℤ) • A ^ 3 - A ^ 2 - (3 : ℤ) • A := by decide

set_option maxRecDepth 100000 in
theorem tr1 : Matrix.trace (A ^ 1) = 5 ∧ Matrix.trace (A ^ 2) = 23 ∧ Matrix.trace (A ^ 3) = 101 := by
  decide

theorem a1 : a 1 = 5 := by
  have h := a_eq 0
  rw [tr1.1] at h
  exact_mod_cast h

theorem a2 : a 2 = 23 := by
  have h := a_eq 1
  rw [tr1.2.1] at h
  exact_mod_cast h

theorem a3 : a 3 = 101 := by
  have h := a_eq 2
  rw [tr1.2.2] at h
  exact_mod_cast h

theorem rec (m : ℕ) : (a (m + 4) : ℤ) = 5 * a (m + 3) - a (m + 2) - 3 * a (m + 1) := by
  rw [a_eq (m + 3), a_eq (m + 2), a_eq (m + 1), a_eq m]
  have h : A ^ (m + 3 + 1) = (5 : ℤ) • A ^ (m + 2 + 1) - A ^ (m + 1 + 1) - (3 : ℤ) • A ^ (m + 1) := by
    have e1 : A ^ (m + 3 + 1) = A ^ m * A ^ 4 := by rw [← pow_add]
    have e2 : A ^ (m + 2 + 1) = A ^ m * A ^ 3 := by rw [← pow_add]
    have e3 : A ^ (m + 1 + 1) = A ^ m * A ^ 2 := by rw [← pow_add]
    have e4 : A ^ (m + 1) = A ^ m * A := by rw [pow_succ]
    rw [e1, e2, e3, e4, Arec, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul]
  rw [h, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul]
  simp

theorem closed : ∀ m : ℕ,
    ((a (m + 1) : ℝ) = 1 + (2 - Real.sqrt 7) ^ (m + 1) + (2 + Real.sqrt 7) ^ (m + 1)) ∧
    ((a (m + 2) : ℝ) = 1 + (2 - Real.sqrt 7) ^ (m + 2) + (2 + Real.sqrt 7) ^ (m + 2)) ∧
    ((a (m + 3) : ℝ) = 1 + (2 - Real.sqrt 7) ^ (m + 3) + (2 + Real.sqrt 7) ^ (m + 3)) := by
  have hs : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have e1 : (2 - Real.sqrt 7) ^ 2 = 4 * (2 - Real.sqrt 7) + 3 := by linear_combination hs
  have e2 : (2 + Real.sqrt 7) ^ 2 = 4 * (2 + Real.sqrt 7) + 3 := by linear_combination hs
  intro m
  induction m with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · rw [a1]; push_cast; ring
    · rw [a2]; push_cast; linear_combination (-1 : ℝ) * e1 - e2
    · rw [a3]; push_cast
      linear_combination (-(2 - Real.sqrt 7) - 4) * e1 + (-(2 + Real.sqrt 7) - 4) * e2
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨h2, h3, ?_⟩
    have hr : (a (m + 4) : ℝ) = 5 * a (m + 3) - a (m + 2) - 3 * a (m + 1) := by
      exact_mod_cast rec m
    rw [show m + 1 + 3 = m + 4 from rfl, hr, h1, h2, h3]
    linear_combination (-(2 - Real.sqrt 7) ^ (m + 1) * ((2 - Real.sqrt 7) - 1)) * e1
      + (-(2 + Real.sqrt 7) ^ (m + 1) * ((2 + Real.sqrt 7) - 1)) * e2

end OMA.P124999

theorem OMA.solution : type_of% @OMA.S_oeis_a124999.main := by
  refine ⟨?_, ?_, ?_⟩
  · have hD : ((1 - PowerSeries.X) * (1 - 4 * PowerSeries.X - 3 * PowerSeries.X ^ 2) : PowerSeries ℚ)
        = 1 - PowerSeries.C (5 : ℚ) * PowerSeries.X + PowerSeries.X ^ 2 + PowerSeries.C (3 : ℚ) * PowerSeries.X ^ 3 := by
      simp only [map_ofNat]; ring
    have hN : ((1 - 2 * PowerSeries.X) * (1 + 2 * PowerSeries.X + 3 * PowerSeries.X ^ 2) : PowerSeries ℚ)
        = 1 - PowerSeries.X ^ 2 - PowerSeries.C (6 : ℚ) * PowerSeries.X ^ 3 := by
      simp only [map_ofNat]; ring
    rw [hD, hN]
    have hE : PowerSeries.mk (fun n => (OMA.S_oeis_a124999.a n : ℚ)) *
        (1 - PowerSeries.C (5 : ℚ) * PowerSeries.X + PowerSeries.X ^ 2 + PowerSeries.C (3 : ℚ) * PowerSeries.X ^ 3)
        = PowerSeries.mk (fun n => (OMA.S_oeis_a124999.a n : ℚ))
          - PowerSeries.C (5 : ℚ) * (PowerSeries.mk (fun n => (OMA.S_oeis_a124999.a n : ℚ)) * PowerSeries.X)
          + PowerSeries.mk (fun n => (OMA.S_oeis_a124999.a n : ℚ)) * PowerSeries.X ^ 2
          + PowerSeries.C (3 : ℚ) * (PowerSeries.mk (fun n => (OMA.S_oeis_a124999.a n : ℚ)) * PowerSeries.X ^ 3) := by
      ring
    rw [hE]
    ext n
    have hr : ∀ m : ℕ, (OMA.S_oeis_a124999.a (m + 4) : ℚ)
        = 5 * OMA.S_oeis_a124999.a (m + 3) - OMA.S_oeis_a124999.a (m + 2)
          - 3 * OMA.S_oeis_a124999.a (m + 1) := by
      intro m; exact_mod_cast OMA.P124999.rec m
    rcases n with _ | _ | _ | _ | m
    · simp [OMA.P124999.a0, PowerSeries.coeff_X_pow]
    · simp [OMA.P124999.a0, OMA.P124999.a1, PowerSeries.coeff_X_pow, PowerSeries.coeff_mul_X_pow']
    · simp [OMA.P124999.a0, OMA.P124999.a1, OMA.P124999.a2, PowerSeries.coeff_X_pow,
        PowerSeries.coeff_mul_X_pow']
      norm_num
    · simp [OMA.P124999.a0, OMA.P124999.a1, OMA.P124999.a2, OMA.P124999.a3,
        PowerSeries.coeff_X_pow, PowerSeries.coeff_mul_X_pow']
      norm_num
    · simp [PowerSeries.coeff_X_pow, PowerSeries.coeff_mul_X_pow', hr m]
      ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact (OMA.P124999.closed m).1
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    exact OMA.P124999.rec m
