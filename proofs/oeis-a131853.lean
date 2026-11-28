import OMAStatements.S_oeis_a131853

-- Sending i to 2 modulo 5 (2^2 = -1 mod 5) maps z(n) = sum of bits * i^k to n modulo 5.
theorem oeis_a131853_key : ∀ n : ℕ,
    ((OMA.S_oeis_a131853.z n).re + 2 * (OMA.S_oeis_a131853.z n).im - (n : ℤ)) % 5 = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n = 0
    · subst h
      rw [OMA.S_oeis_a131853.z]
      simp
    · have hprev := ih (n / 2) (by omega)
      rw [OMA.S_oeis_a131853.z, dif_neg h]
      dsimp only
      omega

theorem OMA.solution : type_of% @OMA.S_oeis_a131853.main := by
  intro n hz
  have h := oeis_a131853_key n
  rw [hz] at h
  have h0r : (0 : GaussianInt).re = 0 := rfl
  have h0i : (0 : GaussianInt).im = 0 := rfl
  rw [h0r, h0i] at h
  omega
