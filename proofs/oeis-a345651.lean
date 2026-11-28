import OMAStatements.S_oeis_a345651

open PowerSeries OMA.S_oeis_a345651

/-- The Euler-type operator `(1 + X) D - k`. -/
noncomputable def θ (k : ℚ) (g : ℚ⟦X⟧) : ℚ⟦X⟧ := (1 + X) * d⁄dX ℚ g - C k * g

private lemma hf : (1 + X) * d⁄dX ℚ ((1 + X) * log ℚ) = (1 + X) + (1 + X) * log ℚ := by
  have h : (1 + X) * d⁄dX ℚ (log ℚ) = 1 := by
    ext (_ | n) <;> simp [deriv_log, add_mul, coeff_succ_X_mul, pow_succ]
  simp only [Derivation.leibniz, map_add, derivative_X, Derivation.map_one_eq_zero, smul_eq_mul]
  linear_combination (1 + X) * h

private lemma shift (k : ℚ) (g : ℚ⟦X⟧) : θ k ((1 + X) * g) = (1 + X) * θ (k - 1) g := by
  simp only [θ, Derivation.leibniz, map_add, derivative_X, Derivation.map_one_eq_zero,
    smul_eq_mul, map_sub, map_one]
  ring

private lemma powstep (n : ℕ) :
    θ (n + 1) (((1 + X) * log ℚ) ^ (n + 1)) = C ((n : ℚ) + 1) * ((1 + X) * ((1 + X) * log ℚ) ^ n) := by
  simp only [θ, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
  have e : ((n + 1 : ℕ) : ℚ⟦X⟧) = C ((n : ℚ) + 1) := by simp
  rw [e]
  linear_combination C ((n : ℚ) + 1) * ((1 + X) * log ℚ) ^ n * hf

private lemma lin (k c : ℚ) (g : ℚ⟦X⟧) : θ k (C c * g) = C c * θ k g := by
  simp only [θ, Derivation.leibniz, derivative_C, smul_eq_mul]; ring

private lemma four : θ 4 (θ 4 (θ 4 (θ 4 (((1 + X) * log ℚ) ^ 4)))) = C 24 * (1 + X) ^ 4 := by
  have p4 : θ 4 (((1 + X) * log ℚ) ^ 4) = C 4 * ((1 + X) * ((1 + X) * log ℚ) ^ 3) := by
    have := powstep 3; norm_num at this; exact this
  have p3 : θ 3 (((1 + X) * log ℚ) ^ 3) = C 3 * ((1 + X) * ((1 + X) * log ℚ) ^ 2) := by
    have := powstep 2; norm_num at this; exact this
  have p2 : θ 2 (((1 + X) * log ℚ) ^ 2) = C 2 * ((1 + X) * ((1 + X) * log ℚ)) := by
    have := powstep 1; norm_num at this; exact this
  have p1 : θ 1 ((1 + X) * log ℚ) = 1 + X := by
    have := powstep 0; norm_num at this; exact this
  have q2 : θ 4 ((1 + X) * ((1 + X) * log ℚ) ^ 3) =
      C 3 * ((1 + X) * ((1 + X) * ((1 + X) * log ℚ) ^ 2)) := by
    rw [shift, show (4 : ℚ) - 1 = 3 by norm_num, p3]; ring
  have q3 : θ 4 ((1 + X) * ((1 + X) * ((1 + X) * log ℚ) ^ 2)) =
      C 2 * ((1 + X) * ((1 + X) * ((1 + X) * ((1 + X) * log ℚ)))) := by
    rw [shift, show (4 : ℚ) - 1 = 3 by norm_num, shift, show (3 : ℚ) - 1 = 2 by norm_num, p2]; ring
  have q4 : θ 4 ((1 + X) * ((1 + X) * ((1 + X) * ((1 + X) * log ℚ)))) = (1 + X) ^ 4 := by
    rw [shift, show (4 : ℚ) - 1 = 3 by norm_num, shift, show (3 : ℚ) - 1 = 2 by norm_num,
      shift, show (2 : ℚ) - 1 = 1 by norm_num, p1]; ring
  rw [p4, lin, lin, lin, q2, lin, lin, q3, lin, q4, ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul]
  norm_num

private lemma coeff_theta (k : ℚ) (g : ℚ⟦X⟧) (n : ℕ) :
    (n.factorial : ℚ) * coeff n (θ k g) =
      ((n + 1).factorial : ℚ) * coeff (n + 1) g + ((n : ℚ) - k) * ((n.factorial : ℚ) * coeff n g) := by
  rcases n with _ | n
  · simp only [θ, add_mul, one_mul, map_sub, map_add, coeff_zero_X_mul, coeff_derivative,
      coeff_C_mul]
    simp
    ring
  · simp only [θ, add_mul, one_mul, map_sub, map_add, coeff_succ_X_mul, coeff_derivative,
      coeff_C_mul, Nat.factorial_succ]
    push_cast
    ring

private lemma u4 (r : ℕ) : coeff (r + 5) (((1 : ℚ⟦X⟧) + X) ^ 4) = 0 := by
  rw [show ((1 : ℚ⟦X⟧) + X) ^ 4 = C 1 + X * (C 4 + X * (C 6 + X * (C 4 + X * C 1))) by
    simp only [map_one, map_ofNat]; ring]
  simp [coeff_succ_X_mul, coeff_X]

theorem OMA.solution : type_of% @OMA.S_oeis_a345651.main := by
  intro n hn
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have hz : ((r + 5).factorial : ℚ) * coeff (r + 5) (θ 4 (θ 4 (θ 4 (θ 4 (((1 + X) * log ℚ) ^ 4))))) = 0 := by
    rw [four, coeff_C_mul, u4]; simp
  simp only [coeff_theta] at hz
  norm_num [add_assoc] at hz
  rw [show r + 9 - 1 = r + 8 from rfl, show r + 9 - 2 = r + 7 from rfl, show r + 9 - 3 = r + 6 from rfl,
    show r + 9 - 4 = r + 5 from rfl]
  simp only [a, egf]
  push_cast at hz ⊢
  linear_combination (1 / 24 : ℚ) * hz
