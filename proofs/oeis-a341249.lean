import OMAStatements.S_oeis_a341249

open OMA.S_oeis_a341249 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a341249.main) := by
  intro h
  have h2 := (h 2 one_le_two).2
  have ha := Int.floor_le (r * ⌊s * (2 : ℕ)⌋)
  have hf : (⌊s * (2 : ℕ)⌋ : ℝ) ≤ 2 := by
    exact_mod_cast Int.lt_add_one_iff.1 (Int.floor_lt.2 (by
      simp [s]; nlinarith [Real.sq_sqrt zero_le_two, Real.sqrt_nonneg 2]))
  simp only [a, r, s, Nat.cast_ofNat] at *
  nlinarith [Real.sq_sqrt zero_le_two, Real.sqrt_nonneg 2,
    mul_nonneg (sub_nonneg.2 hf) (by positivity : (0 : ℝ) ≤ 2 + √2)]
