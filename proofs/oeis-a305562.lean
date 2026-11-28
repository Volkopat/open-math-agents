import OMAStatements.S_oeis_a305562

theorem bc_tri_succ (n : ℕ) :
    OMA.S_oeis_a305562.tri (n + 1) = OMA.S_oeis_a305562.tri n + n := rfl

theorem bc_tri_mono {i j : ℕ} (h : i ≤ j) :
    OMA.S_oeis_a305562.tri i ≤ OMA.S_oeis_a305562.tri j := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => rw [bc_tri_succ]; omega

theorem bc_row_ss (n k : ℕ) : OMA.S_oeis_a305562.row (n + 1) (k + 1) =
    OMA.S_oeis_a305562.row (n + 1) k / 2 + OMA.S_oeis_a305562.row n k := by
  first
  | rw [OMA.S_oeis_a305562.row]
  | simp [OMA.S_oeis_a305562.row]

theorem bc_row_s0 (n : ℕ) :
    OMA.S_oeis_a305562.row (n + 1) 0 = OMA.S_oeis_a305562.row n n := by
  first
  | rw [OMA.S_oeis_a305562.row]
  | simp [OMA.S_oeis_a305562.row]

theorem bc_row_00 : OMA.S_oeis_a305562.row 0 0 = 1 := by
  first
  | (rw [OMA.S_oeis_a305562.row] <;> simp)
  | simp [OMA.S_oeis_a305562.row]

theorem bc_a_succ (n : ℕ) : OMA.S_oeis_a305562.a (n + 1) =
    ∑ j ∈ Finset.range (n + 1), n.choose j * OMA.S_oeis_a305562.a j *
      2 ^ (OMA.S_oeis_a305562.tri (n + 1) - OMA.S_oeis_a305562.tri (j + 1)) := by
  rw [OMA.S_oeis_a305562.a]
  exact Fin.sum_univ_eq_sum_range (fun j => n.choose j * OMA.S_oeis_a305562.a j *
      2 ^ (OMA.S_oeis_a305562.tri (n + 1) - OMA.S_oeis_a305562.tri (j + 1))) (n + 1)

theorem bc_a_zero : OMA.S_oeis_a305562.a 0 = 1 := by
  rw [OMA.S_oeis_a305562.a]

def bcU (m k : ℕ) : ℚ := 2 ^ k * OMA.S_oeis_a305562.row m k

theorem bc_rec (m k : ℕ) : bcU (m + 1) (k + 1) = bcU (m + 1) k + 2 * bcU m k := by
  unfold bcU
  rw [bc_row_ss]
  ring

theorem bc_newton (k : ℕ) : ∀ m : ℕ, k ≤ m →
    bcU m k = ∑ j ∈ Finset.range (k + 1), (k.choose j : ℚ) * 2 ^ j * bcU (m - j) 0 := by
  induction k with
  | zero => intro m _; simp
  | succ k ih =>
    intro m hm
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [bc_rec, ih (m' + 1) (by omega), ih m' (by omega)]
    have h1 : ∑ j ∈ Finset.range (k + 1 + 1), ((k + 1).choose j : ℚ) * 2 ^ j * bcU (m' + 1 - j) 0 =
        bcU (m' + 1) 0 + ∑ i ∈ Finset.range (k + 1),
          ((k + 1).choose (i + 1) : ℚ) * 2 ^ (i + 1) * bcU (m' - i) 0 := by
      rw [Finset.sum_range_succ'
        (fun j => ((k + 1).choose j : ℚ) * 2 ^ j * bcU (m' + 1 - j) 0) (k + 1)]
      simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, mul_one, Nat.sub_zero,
        Nat.add_sub_add_right]
      try ring
    have h2 : ∑ j ∈ Finset.range (k + 1), (k.choose j : ℚ) * 2 ^ j * bcU (m' + 1 - j) 0 =
        bcU (m' + 1) 0 + ∑ i ∈ Finset.range (k + 1),
          (k.choose (i + 1) : ℚ) * 2 ^ (i + 1) * bcU (m' - i) 0 := by
      rw [Finset.sum_range_succ' (fun j => (k.choose j : ℚ) * 2 ^ j * bcU (m' + 1 - j) 0) k,
        Finset.sum_range_succ (fun i => (k.choose (i + 1) : ℚ) * 2 ^ (i + 1) * bcU (m' - i) 0) k]
      simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, mul_one, Nat.sub_zero,
        Nat.add_sub_add_right, Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero]
      try ring
    have h3 : ∑ i ∈ Finset.range (k + 1), ((k + 1).choose (i + 1) : ℚ) * 2 ^ (i + 1) * bcU (m' - i) 0 =
        2 * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℚ) * 2 ^ i * bcU (m' - i) 0 +
        ∑ i ∈ Finset.range (k + 1), (k.choose (i + 1) : ℚ) * 2 ^ (i + 1) * bcU (m' - i) 0 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      first
      | rw [Nat.choose_succ_succ]
      | rw [Nat.choose_succ_succ']
      push_cast
      ring
    rw [h1, h2, h3]
    ring

theorem bc_main (m : ℕ) : OMA.S_oeis_a305562.row m m =
    (OMA.S_oeis_a305562.a (m + 1) : ℚ) / 2 ^ OMA.S_oeis_a305562.tri (m + 1) := by
  refine Nat.strong_induction_on m ?_
  intro m ih
  have hU : ∀ i, i ≤ m → bcU i 0 =
      (OMA.S_oeis_a305562.a i : ℚ) / 2 ^ OMA.S_oeis_a305562.tri i := by
    intro i hi
    rcases i with _ | i
    · rw [bcU, bc_row_00, bc_a_zero]
      simp [OMA.S_oeis_a305562.tri]
    · rw [bcU, pow_zero, one_mul, bc_row_s0, ih i (by omega)]
  rcases m with _ | m
  · rw [bc_row_00, bc_a_succ]
    simp [bc_a_zero, OMA.S_oeis_a305562.tri]
  · have hN := bc_newton (m + 1) (m + 1) le_rfl
    have hrow : OMA.S_oeis_a305562.row (m + 1) (m + 1) = bcU (m + 1) (m + 1) / 2 ^ (m + 1) := by
      rw [bcU]
      field_simp
    rw [hrow, hN, bc_a_succ, Finset.sum_div, Nat.cast_sum, Finset.sum_div]
    rw [← Finset.sum_range_reflect (fun j => ((((m + 1).choose j * OMA.S_oeis_a305562.a j *
      2 ^ (OMA.S_oeis_a305562.tri (m + 1 + 1) - OMA.S_oeis_a305562.tri (j + 1)) : ℕ) : ℚ)) /
        2 ^ OMA.S_oeis_a305562.tri (m + 1 + 1)) (m + 1 + 1)]
    apply Finset.sum_congr rfl
    intro j hj
    beta_reduce
    have hj' : j < m + 1 + 1 := Finset.mem_range.1 hj
    obtain ⟨p, hp⟩ : ∃ p, m + 1 = j + p := ⟨m + 1 - j, by omega⟩
    have e1 : m + 1 + 1 - 1 - j = p := by omega
    have e2 : m + 1 - j = p := by omega
    rw [e1, e2, hU p (by omega)]
    have hjle : j ≤ m + 1 := by omega
    have hch : (m + 1).choose p = (m + 1).choose j := by
      rw [← e2]
      exact Nat.choose_symm hjle
    have htle : OMA.S_oeis_a305562.tri (p + 1) ≤ OMA.S_oeis_a305562.tri (m + 1 + 1) :=
      bc_tri_mono (by omega)
    have hpow : (2 : ℚ) ^ (OMA.S_oeis_a305562.tri (m + 1 + 1) - OMA.S_oeis_a305562.tri (p + 1)) =
        2 ^ OMA.S_oeis_a305562.tri (m + 1 + 1) / 2 ^ OMA.S_oeis_a305562.tri (p + 1) :=
      pow_sub₀ (2 : ℚ) (by norm_num) htle
    push_cast
    rw [hch, hpow, bc_tri_succ p, hp, pow_add, pow_add]
    field_simp
    try ring

theorem bc_odd (n : ℕ) : Odd (OMA.S_oeis_a305562.a n) := by
  induction n with
  | zero => rw [bc_a_zero]; exact odd_one
  | succ n ih =>
    rw [bc_a_succ, Finset.sum_range_succ]
    have h1 : 2 ∣ ∑ j ∈ Finset.range n, n.choose j * OMA.S_oeis_a305562.a j *
        2 ^ (OMA.S_oeis_a305562.tri (n + 1) - OMA.S_oeis_a305562.tri (j + 1)) := by
      apply Finset.dvd_sum
      intro j hj
      have hjn : j < n := Finset.mem_range.1 hj
      have hle : OMA.S_oeis_a305562.tri (j + 1) ≤ OMA.S_oeis_a305562.tri n := bc_tri_mono (by omega)
      have hpos : 1 ≤ OMA.S_oeis_a305562.tri (n + 1) - OMA.S_oeis_a305562.tri (j + 1) := by
        rw [bc_tri_succ]
        omega
      exact Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) _
    rw [Nat.choose_self, one_mul, Nat.sub_self, pow_zero, mul_one]
    exact Even.add_odd (even_iff_two_dvd.2 h1) ih

theorem OMA.solution : type_of% @OMA.S_oeis_a305562.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, bc_main m]
  have hodd := bc_odd (m + 1)
  have hc : Nat.Coprime (OMA.S_oeis_a305562.a (m + 1)) (2 ^ OMA.S_oeis_a305562.tri (m + 1)) := by
    apply Nat.Coprime.pow_right
    apply Nat.Coprime.symm
    apply (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
    obtain ⟨r, hr⟩ := hodd
    omega
  have hcop : Nat.Coprime ((OMA.S_oeis_a305562.a (m + 1) : ℤ)).natAbs
      ((2 : ℤ) ^ OMA.S_oeis_a305562.tri (m + 1)).natAbs := by
    simpa [Int.natAbs_pow] using hc
  have e : ((OMA.S_oeis_a305562.a (m + 1) : ℚ) / 2 ^ OMA.S_oeis_a305562.tri (m + 1)) =
      (((OMA.S_oeis_a305562.a (m + 1) : ℤ) : ℚ) /
        (((2 : ℤ) ^ OMA.S_oeis_a305562.tri (m + 1) : ℤ) : ℚ)) := by
    first
    | (simp; done)
    | (norm_num; done)
    | (push_cast; ring)
  rw [e, Rat.num_div_eq_of_coprime (by positivity) hcop]
