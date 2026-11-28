import OMAStatements.S_oeis_a125468

namespace OMA.CircularWords11

open OMA.S_oeis_a125468 Finset PowerSeries

private abbrev Digit := Fin 11

private abbrev cons {n : ℕ} (u : Digit) (w : Fin n → Digit) : Fin (n + 1) → Digit :=
  @Fin.cons n (fun _ ↦ Digit) u w

private abbrev snoc {n : ℕ} (w : Fin n → Digit) (v : Digit) : Fin (n + 1) → Digit :=
  @Fin.snoc n (fun _ ↦ Digit) w v

private abbrev Edge := adjOk

private def matrix : Matrix Digit Digit ℚ := fun u v ↦ if Edge u v then 1 else 0

private def Path {n : ℕ} (u v : Digit) (w : Fin n → Digit) : Prop :=
  ∀ i : Fin (n + 1),
    Edge (snoc (cons u w) v i.castSucc) (snoc (cons u w) v i.succ)

private instance {n : ℕ} (u v : Digit) (w : Fin n → Digit) : Decidable (Path u v w) := by
  unfold Path
  infer_instance

private lemma path_empty (u v : Digit) (w : Fin 0 → Digit) : Path u v w ↔ Edge u v := by
  have h0 : Edge (snoc (cons u w) v (0 : Fin 1).castSucc)
      (snoc (cons u w) v (Fin.last 1)) ↔ Edge u v := by
    rw [show snoc (cons u w) v (Fin.last 1) = v from Fin.snoc_last ..,
      show snoc (cons u w) v (0 : Fin 1).castSucc = u from
        (Fin.snoc_castSucc ..).trans (Fin.cons_zero ..)]
  constructor
  · intro h
    exact h0.1 (h 0)
  · intro h i
    have hi : i = 0 := Fin.ext (by have hi := i.isLt; simp at hi; omega)
    subst i
    exact h0.2 h

private lemma path_cons {n : ℕ} (u v x : Digit) (w : Fin n → Digit) :
    Path u v (cons x w) ↔ Edge u x ∧ Path x v w := by
  unfold Path
  have hs : snoc (cons u (cons x w)) v = cons u (snoc (cons x w) v) :=
    (Fin.cons_snoc_eq_snoc_cons u (cons x w) v).symm
  rw [hs, Fin.forall_fin_succ]
  have hcast (i : Fin (n + 1)) : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
  have hzero : snoc (cons x w) v 0 = x := by
    change snoc (cons x w) v (0 : Fin (n + 1)).castSucc = x
    simp [snoc, cons]
  simp only [Fin.castSucc_zero, cons, Fin.cons_zero, Fin.cons_succ, hcast]
  change (Edge u (snoc (cons x w) v 0) ∧ _) ↔ _
  rw [hzero]

private lemma path_sum (n : ℕ) (u v : Digit) :
    (∑ w : Fin n → Digit, (if Path u v w then 1 else 0 : ℚ)) = (matrix ^ (n + 1)) u v := by
  induction n generalizing u v with
  | zero =>
    simp only [path_empty, Fintype.sum_unique, Nat.zero_add, pow_one, matrix]
  | succ n ih =>
    let e := Fin.consEquiv (fun _ : Fin (n + 1) ↦ Digit)
    have hs :
        (∑ w : Fin (n + 1) → Digit, (if Path u v w then 1 else 0 : ℚ)) =
          ∑ p : Digit × (Fin n → Digit), (if Path u v (cons p.1 p.2) then 1 else 0 : ℚ) := by
      exact (Fintype.sum_equiv e _ _ fun p ↦ rfl).symm
    rw [hs, Fintype.sum_prod_type, pow_succ', Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro x _
    simp only [path_cons]
    by_cases hx : Edge u x
    · simp only [hx, true_and, matrix, if_true, one_mul]
      exact ih x v
    · simp only [hx, false_and, if_false, sum_const_zero, matrix, zero_mul]

private lemma snoc_next {n : ℕ} (w : Fin (n + 1) → Digit) (i : Fin (n + 1)) :
    snoc w (w 0) i.succ = w ⟨(i.val + 1) % (n + 1), Nat.mod_lt _ (by omega)⟩ := by
  by_cases h : i.val + 1 < n + 1
  · have heq : i.succ = (⟨(i.val + 1) % (n + 1), Nat.mod_lt _ (by omega)⟩ : Fin (n + 1)).castSucc :=
      Fin.ext (by simp [Nat.mod_eq_of_lt h])
    rw [heq]
    exact Fin.snoc_castSucc ..
  · have hv : i.val + 1 = n + 1 := by omega
    have heq : i.succ = Fin.last (n + 1) := Fin.ext hv
    rw [heq, show snoc w (w 0) (Fin.last (n + 1)) = w 0 from Fin.snoc_last ..]
    congr 1
    exact Fin.ext (by simp [hv])

private lemma path_cycle {n : ℕ} (u : Digit) (w : Fin n → Digit) :
    Path u u w ↔ ∀ i : Fin (n + 1),
      Edge ((cons u w) i)
        ((cons u w) ⟨(i.val + 1) % (n + 1), Nat.mod_lt _ (by omega)⟩) := by
  unfold Path
  apply forall_congr'
  intro i
  have h0 : snoc (cons u w) u i.castSucc = (cons u w) i := Fin.snoc_castSucc ..
  have hn : snoc (cons u w) u i.succ =
      (cons u w) ⟨(i.val + 1) % (n + 1), Nat.mod_lt _ (by omega)⟩ := by
    simpa only [cons, Fin.cons_zero] using snoc_next (cons u w) i
  rw [h0, hn]

private lemma count_as_trace (n : ℕ) :
    (a (n + 1) : ℚ) = Matrix.trace (matrix ^ (n + 1)) := by
  classical
  let e := Fin.consEquiv (fun _ : Fin (n + 1) ↦ Digit)
  have hs :
      (∑ w : Fin (n + 1) → Digit, (if ∀ i : Fin (n + 1),
        Edge (w i) (w ⟨(i.val + 1) % (n + 1), Nat.mod_lt _ (by omega)⟩) then 1 else 0 : ℚ)) =
      ∑ p : Digit × (Fin n → Digit), (if Path p.1 p.1 p.2 then 1 else 0 : ℚ) := by
    symm
    apply Fintype.sum_equiv e
    intro p
    simp only [path_cycle]
    rfl
  rw [Fintype.sum_prod_type] at hs
  simp_rw [path_sum] at hs
  rw [Matrix.trace]
  change _ = ∑ x, (matrix ^ (n + 1)) x x
  rw [← hs]
  simp only [a, isValid, Edge]
  exact (Finset.sum_boole _ _).symm

private lemma matrix_relation :
    matrix ^ 4 = (11 : ℚ) • matrix ^ 3 - matrix ^ 2 - (9 : ℚ) • matrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

private lemma recurrence (n : ℕ) (hn : 4 ≤ n) :
    (a n : ℚ) = 11 * a (n - 1) - a (n - 2) - 9 * a (n - 3) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have H := congrArg (fun A : Matrix Digit Digit ℚ ↦ Matrix.trace (matrix ^ k * A)) matrix_relation
  simp only [mul_sub, mul_smul_comm, ← pow_add, ← pow_succ,
    Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul] at H
  rw [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
    show k + 4 - 3 = k + 1 by omega]
  exact (count_as_trace (k + 3)).trans (H.trans (by
    rw [count_as_trace (k + 2), count_as_trace (k + 1), count_as_trace k]))

private lemma v0 : a 0 = 1 := by decide +kernel
private lemma v1 : a 1 = 11 := by decide +kernel
private lemma v2 : a 2 = 119 := by decide +kernel
private lemma v3 : a 3 = 1271 := by decide +kernel

private lemma gf :
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 10 * X - 9 * X ^ 2)) =
      1 - X ^ 2 - 18 * X ^ 3) := by
  let F : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ))
  change F * _ = _
  have hmul : F * ((1 - X) * (1 - 10 * X - 9 * X ^ 2)) =
      F - C 11 * (X ^ 1 * F) + X ^ 2 * F + C 9 * (X ^ 3 * F) := by
    simp only [map_ofNat]
    ring
  have hnum : (1 - X ^ 2 - 18 * X ^ 3 : PowerSeries ℚ) =
      1 - X ^ 2 - C 18 * X ^ 3 := by simp only [map_ofNat]
  rw [hmul, hnum]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow, coeff_one, F, coeff_mk]
  by_cases hn : 4 ≤ n
  · simp only [if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega),
      if_pos (show 3 ≤ n by omega), if_neg (show n ≠ 0 by omega),
      if_neg (show n ≠ 2 by omega), if_neg (show n ≠ 3 by omega), mul_zero, sub_zero]
    linarith [recurrence n hn]
  · interval_cases n <;> norm_num [v0, v1, v2, v3]

private noncomputable def alpha : ℝ := 5 - Real.sqrt 34
private noncomputable def beta : ℝ := 5 + Real.sqrt 34

private noncomputable def closed (n : ℕ) : ℝ := 1 + alpha ^ n + beta ^ n

private lemma power_recurrence (r : ℝ) (hr : r ^ 3 - 11 * r ^ 2 + r + 9 = 0) (k : ℕ) :
    r ^ (k + 3) = 11 * r ^ (k + 2) - r ^ (k + 1) - 9 * r ^ k := by
  simp only [pow_add, pow_one]
  linear_combination r ^ k * hr

private lemma closed_recurrence (n : ℕ) (hn : 4 ≤ n) :
    closed n = 11 * closed (n - 1) - closed (n - 2) - 9 * closed (n - 3) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 34)
  have ha : alpha ^ 2 - 10 * alpha - 9 = 0 := by unfold alpha; nlinarith [hs]
  have hb : beta ^ 2 - 10 * beta - 9 = 0 := by unfold beta; nlinarith [hs]
  have har : alpha ^ 3 - 11 * alpha ^ 2 + alpha + 9 = 0 := by
    linear_combination (alpha - 1) * ha
  have hbr : beta ^ 3 - 11 * beta ^ 2 + beta + 9 = 0 := by
    linear_combination (beta - 1) * hb
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  rw [show k + 4 = (k + 1) + 3 by omega, show k + 1 + 3 - 1 = (k + 1) + 2 by omega,
    show k + 1 + 3 - 2 = (k + 1) + 1 by omega, show k + 1 + 3 - 3 = k + 1 by omega]
  unfold closed
  linarith [power_recurrence alpha har (k + 1), power_recurrence beta hbr (k + 1)]

private lemma integer_rec (n : ℕ) (hn : 4 ≤ n) :
    (a n : ℤ) = 11 * a (n - 1) - a (n - 2) - 9 * a (n - 3) := by
  exact_mod_cast recurrence n hn

private lemma closed_formula (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℝ) = closed n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : 4 ≤ n
    · have hr : (a n : ℝ) = 11 * a (n - 1) - a (n - 2) - 9 * a (n - 3) := by
        exact_mod_cast integer_rec n h
      rw [hr, closed_recurrence n h, ih (n - 1) (by omega) (by omega),
        ih (n - 2) (by omega) (by omega), ih (n - 3) (by omega) (by omega)]
    · have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 34)
      interval_cases n <;> norm_num [v1, v2, v3, closed, alpha, beta] <;> nlinarith [hs]

theorem result : type_of% @OMA.S_oeis_a125468.main :=
  ⟨gf, closed_formula, integer_rec⟩

end OMA.CircularWords11

theorem OMA.solution : type_of% @OMA.S_oeis_a125468.main := OMA.CircularWords11.result
