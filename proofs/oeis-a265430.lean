import OMAStatements.S_oeis_a265430

namespace OMA.S_oeis_a265430




/-- The row structure. -/
def P (t : ℕ) (j : ℤ) : Prop := 0 ≤ j ∧ j ≤ t ∧ ¬ (1 ≤ j ∧ (j + t) % 4 = 3)

instance (t : ℕ) (j : ℤ) : Decidable (P t j) := by unfold P; infer_instance

lemma step (t : ℕ) (i : ℤ) :
    rule (decide (P t (i - 1))) (decide (P t i)) (decide (P t (i + 1))) = decide (P (t + 1) i) := by
  by_cases h1 : P t (i - 1) <;> by_cases h2 : P t i <;> by_cases h3 : P t (i + 1) <;>
    by_cases h4 : P (t + 1) i <;>
    simp only [h1, h2, h3, h4, decide_true, decide_false] <;>
    first
      | decide
      | (exfalso; unfold P at h1 h2 h3 h4; push_cast at h1 h2 h3 h4; omega)

lemma pattern (t : ℕ) : ∀ i, state t i = decide (P t i) := by
  induction t with
  | zero =>
    intro i
    show decide (i = 0) = _
    exact decide_eq_decide.mpr (by unfold P; push_cast; omega)
  | succ t ih =>
    intro i
    show rule (state t (i - 1)) (state t i) (state t (i + 1)) = _
    rw [ih, ih, ih, step]

lemma values : a 0 = 0 ∧ a 1 = 1 ∧ a 2 = 3 ∧ a 3 = 3 ∧ a 4 = 5 := by
  decide

/-- The OFF cells of row `n` inside `-n..n`. -/
noncomputable def S (n : ℕ) : Finset ℤ :=
  (Finset.Icc (-(n : ℤ)) n).filter (fun i => i < 0 ∨ (1 ≤ i ∧ (i + n) % 4 = 3))

lemma a_eq_S (n : ℕ) : a n = (S n).card := by
  unfold a S
  congr 1
  refine Finset.filter_congr fun i hi => ?_
  have key : (state n i = false) ↔ ¬ P n i := by rw [pattern]; exact decide_eq_false_iff_not
  rw [key]
  have hi' := Finset.mem_Icc.mp hi
  unfold P
  omega

lemma S_succ4 (n : ℕ) : S (n + 4) = S n ∪ (Finset.Icc (-((n : ℤ) + 4)) (-((n : ℤ) + 1)) ∪
    {if n % 2 = 0 then (n : ℤ) + 3 else (n : ℤ) + 1}) := by
  ext i
  simp only [S, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
  push_cast
  split_ifs with h <;> omega

lemma a_succ4 (n : ℕ) : a (n + 4) = a n + 5 := by
  rw [a_eq_S, a_eq_S, S_succ4, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
    Int.card_Icc, Finset.card_singleton]
  · omega
  · rw [Finset.disjoint_singleton_right]
    simp only [Finset.mem_Icc]
    split_ifs <;> omega
  · rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [S, Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton] at hi hi'
    split_ifs at hi' <;> omega

/-- Barker's recurrence, for every `n > 4`. -/
theorem recurrence (n : ℕ) (hn : 4 < n) : (a n : ℤ) = a (n - 1) + a (n - 4) - a (n - 5) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have h1 := a_succ4 (m + 1)
  have h2 := a_succ4 m
  simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 4 = m + 1 by omega,
    show m + 5 - 5 = m by omega]
  rw [show m + 5 = m + 1 + 4 by ring, h1, h2]
  push_cast
  ring

lemma a_quasi (q r : ℕ) (hr : r < 4) : a (4 * q + r) = 5 * q + [0, 1, 3, 3].getD r 0 := by
  obtain ⟨h0, h1, h2, h3, -⟩ := values
  induction q with
  | zero => interval_cases r <;> simp [h0, h1, h2, h3]
  | succ q ih =>
    rw [show 4 * (q + 1) + r = (4 * q + r) + 4 by ring, a_succ4, ih]
    ring

/-- Barker's closed form `a(n) = (10n + 3(-1)^n - (1-i)(-i)^n - (1+i)i^n - 1)/8`, in `ℂ`. -/
theorem closed_form (n : ℕ) :
    (a n : ℂ) = (10 * n + 3 * (-1) ^ n - (1 - Complex.I) * (-Complex.I) ^ n
      - (1 + Complex.I) * Complex.I ^ n - 1) / 8 := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 4 ∧ n = 4 * q + r :=
    ⟨n / 4, n % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 4).symm⟩
  have hI4 : Complex.I ^ 4 = 1 := Complex.I_pow_four
  have hmI4 : (-Complex.I) ^ 4 = 1 := by rw [neg_pow, hI4]; norm_num
  have hm14 : (-1 : ℂ) ^ 4 = 1 := by norm_num
  rw [a_quasi q r hr, pow_add, pow_add, pow_add, pow_mul, pow_mul, pow_mul, hI4, hmI4, hm14]
  simp only [one_pow, one_mul]
  interval_cases r <;>
    simp [pow_succ, Complex.ext_iff, Complex.I_mul_I] <;> ring

open PowerSeries in
/-- Barker's g.f. `x(1+2x+2x^3)/((1-x)^2(1+x)(1+x^2))`, as an identity in `ℚ⟦X⟧`. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) =
    (X * (1 + 2 * X + 2 * X ^ 3)) * ((1 - X) ^ 2 * (1 + X) * (1 + X ^ 2))⁻¹ := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ))
  have hden : constantCoeff ((1 - X) ^ 2 * (1 + X) * (1 + X ^ 2) : ℚ⟦X⟧) ≠ 0 := by simp
  have key : A * ((1 - X) ^ 2 * (1 + X) * (1 + X ^ 2)) = X ^ 1 + X ^ 2 + X ^ 2 + X ^ 4 + X ^ 4 := by
    have e1 : A * ((1 - X) ^ 2 * (1 + X) * (1 + X ^ 2)) = A - A * X ^ 1 - A * X ^ 4 + A * X ^ 5 := by
      ring
    rw [e1]
    ext n
    simp only [map_sub, map_add, coeff_mul_X_pow', coeff_X_pow, A, coeff_mk]
    obtain ⟨h0, h1, h2, h3, h4⟩ := values
    rcases Nat.lt_or_ge n 5 with hn | hn
    · interval_cases n <;> simp [h0, h1, h2, h3, h4] <;> norm_num
    · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
      simp only [show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 4 by omega, if_false]
      have hr := recurrence n (by omega)
      have : (a n : ℚ) = a (n - 1) + a (n - 4) - a (n - 5) := by exact_mod_cast hr
      rw [this]; ring
  have hN : (X * (1 + 2 * X + 2 * X ^ 3) : ℚ⟦X⟧) = X ^ 1 + X ^ 2 + X ^ 2 + X ^ 4 + X ^ 4 := by ring
  rw [hN, ← key, mul_assoc, PowerSeries.mul_inv_cancel _ hden, mul_one]

end OMA.S_oeis_a265430

theorem OMA.solution : type_of% @OMA.S_oeis_a265430.main :=
  ⟨fun n => OMA.S_oeis_a265430.closed_form n,
    fun n hn => OMA.S_oeis_a265430.recurrence n hn, OMA.S_oeis_a265430.gf⟩
