import OMAStatements.S_oeis_a307663

namespace OMA.S_oeis_a307663

/-- Helper: `c i = Sum_{j=1..i} binomial(i,j)/j`, indexed over `range`. -/
def c (i : ℕ) : ℚ := ∑ j ∈ Finset.range i, (i.choose (j + 1) : ℚ) / ((j : ℚ) + 1)

lemma shift (f : ℕ → ℚ) (i : ℕ) :
    ∑ j ∈ Finset.Icc 1 i, f j = ∑ j ∈ Finset.range i, f (j + 1) := by
  induction i with
  | zero => simp
  | succ k ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

lemma c_succ (i : ℕ) : c (i + 1) = c i + (2 ^ (i + 1) - 1) / ((i : ℚ) + 1) := by
  have h1 : ∀ j ∈ Finset.range (i + 1),
      (((i + 1).choose (j + 1) : ℕ) : ℚ) / ((j : ℚ) + 1)
        = (i.choose j : ℚ) / ((j : ℚ) + 1) + (i.choose (j + 1) : ℚ) / ((j : ℚ) + 1) := by
    intro j _
    rw [Nat.choose_succ_succ', Nat.cast_add, add_div]
  have h2 : ∀ j ∈ Finset.range (i + 1),
      (i.choose j : ℚ) / ((j : ℚ) + 1) = ((i + 1).choose (j + 1) : ℚ) / ((i : ℚ) + 1) := by
    intro j _
    have h0 : (i + 1) * i.choose j = (i + 1).choose (j + 1) * (j + 1) := by
      first
        | exact Nat.add_one_mul_choose_eq i j
        | exact Nat.succ_mul_choose_eq i j
        | (rw [Nat.choose_succ_right_eq, Nat.choose_succ_succ', Nat.succ_sub_succ]; ring_nf; omega)
    have hq : ((i : ℚ) + 1) * (i.choose j : ℚ) = ((i + 1).choose (j + 1) : ℚ) * ((j : ℚ) + 1) := by
      exact_mod_cast h0
    rw [div_eq_div_iff (by positivity) (by positivity)]
    linear_combination hq
  have h3 : (∑ j ∈ Finset.range (i + 1), ((i + 1).choose (j + 1) : ℚ)) = 2 ^ (i + 1) - 1 := by
    have h4 := Nat.sum_range_choose (i + 1)
    rw [Finset.sum_range_succ'] at h4
    simp only [Nat.choose_zero_right] at h4
    have h5 : ((∑ j ∈ Finset.range (i + 1), (i + 1).choose (j + 1) : ℕ) : ℚ) + 1
        = 2 ^ (i + 1) := by exact_mod_cast h4
    push_cast at h5
    linarith
  unfold c
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_congr rfl h2,
    ← Finset.sum_div, h3,
    Finset.sum_range_succ (fun j => (i.choose (j + 1) : ℚ) / ((j : ℚ) + 1)),
    Nat.choose_succ_self]
  simp only [Nat.cast_zero, zero_div, add_zero]
  ring

lemma inner (i : ℕ) :
    ∑ j ∈ Finset.Icc 1 i, (i.choose j : ℚ) * (i : ℚ) / (j : ℚ) = (i : ℚ) * c i := by
  rw [shift]
  unfold c
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  push_cast
  ring

lemma outer (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 i, (i.choose j : ℚ) * (i : ℚ) / (j : ℚ)
      = ∑ i ∈ Finset.range n, ((i : ℚ) + 1) * c (i + 1) := by
  rw [shift]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [inner]
  push_cast
  ring

lemma closed (n : ℕ) :
    ∑ i ∈ Finset.range n, ((i : ℚ) + 1) * c (i + 1)
      = (n : ℚ) * ((n : ℚ) + 1) / 2 * c n - ((n : ℚ) - 2) * 2 ^ n - 2
        + (n : ℚ) * ((n : ℚ) - 1) / 4 := by
  induction n with
  | zero => norm_num [c]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, c_succ]
    have hk : (k : ℚ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    ring

lemma a_eq (n : ℕ) :
    a n = ((n - 1).factorial : ℚ) * ((n : ℚ) * ((n : ℚ) + 1) / 2 * c n
      - ((n : ℚ) - 2) * 2 ^ n - 2 + (n : ℚ) * ((n : ℚ) - 1) / 4) := by
  unfold a
  rw [outer n, closed n]

theorem recur_thm : ∀ n : ℕ, 1 ≤ n →
    2 * ((n : ℚ) + 3) * ((n : ℚ) + 2) * (n : ℚ) * ((n : ℚ) - 2) * a n
      - ((n : ℚ) + 3) * (5 * (n : ℚ) ^ 2 - 6 * (n : ℚ) - 17) * a (n + 1)
      + (4 * (n : ℚ) ^ 2 - (n : ℚ) - 29) * a (n + 2)
      - ((n : ℚ) - 3) * a (n + 3) = 0 := by
  intro n _
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [show m + 1 + 2 = m + 1 + 1 + 1 by omega, show m + 1 + 3 = m + 1 + 1 + 1 + 1 by omega]
  rw [a_eq (m + 1), a_eq (m + 1 + 1), a_eq (m + 1 + 1 + 1), a_eq (m + 1 + 1 + 1 + 1)]
  simp only [Nat.add_sub_cancel, Nat.factorial_succ]
  rw [c_succ (m + 1 + 1 + 1), c_succ (m + 1 + 1), c_succ (m + 1)]
  have h1 : (m : ℚ) + 1 ≠ 0 := by positivity
  have h2 : (m : ℚ) + 1 + 1 ≠ 0 := by positivity
  have h3 : (m : ℚ) + 1 + 1 + 1 ≠ 0 := by positivity
  have h4 : (m : ℚ) + 1 + 1 + 1 + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

end OMA.S_oeis_a307663

theorem OMA.solution : type_of% @OMA.S_oeis_a307663.main := OMA.S_oeis_a307663.recur_thm
