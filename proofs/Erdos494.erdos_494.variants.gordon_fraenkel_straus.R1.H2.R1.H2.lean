import OMAReductions.R_Erdos494_erdos_494_variants_gordon_fraenkel_straus_R1_H2_R1

/-!
Proof of `OMA.R_Erdos494_erdos_494_variants_gordon_fraenkel_straus_R1_H2_R1.H2`.

Put `x = d b`. Since `a ≠ b`, `|d b - d a| = d |b - a| ≥ d`, so the condition gives
`d < x ^ (1 - ε) = x / x ^ ε`, i.e. `d x ^ ε < x = d b`, hence `x ^ ε < b`.
Raising to the power `1 / ε` gives `d ≤ x < b ^ (1 / ε)`, so only finitely many `d` qualify.
-/

theorem OMA.solution :
    OMA.R_Erdos494_erdos_494_variants_gordon_fraenkel_straus_R1_H2_R1.H2 := by
  intro ε a b hε ha hb hab
  apply (Set.finite_Iio (⌈(b : ℝ) ^ (1 / ε)⌉₊)).subset
  rintro d ⟨hd, hlt⟩
  rw [Set.mem_Iio]
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hxd : ((d * b : ℕ) : ℝ) = (d : ℝ) * b := by push_cast; ring
  have hxpos : (0 : ℝ) < ((d * b : ℕ) : ℝ) := by rw [hxd]; positivity
  have hgap : (d : ℝ) ≤ |((d * b : ℕ) : ℝ) - ((d * a : ℕ) : ℝ)| := by
    have hba : (1 : ℤ) ≤ |(b : ℤ) - a| :=
      Int.one_le_abs (sub_ne_zero.mpr (by exact_mod_cast (Ne.symm hab)))
    have hba' : (1 : ℝ) ≤ |(b : ℝ) - a| := by exact_mod_cast hba
    have hrw : ((d * b : ℕ) : ℝ) - ((d * a : ℕ) : ℝ) = (d : ℝ) * ((b : ℝ) - a) := by
      push_cast; ring
    rw [hrw, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < d)]
    nlinarith
  have h1 : (d : ℝ) < ((d * b : ℕ) : ℝ) ^ (1 - ε) := lt_of_le_of_lt hgap hlt
  have hsplit : ((d * b : ℕ) : ℝ) ^ (1 - ε) = ((d * b : ℕ) : ℝ) / ((d * b : ℕ) : ℝ) ^ ε := by
    rw [Real.rpow_sub hxpos, Real.rpow_one]
  have hxe : 0 < ((d * b : ℕ) : ℝ) ^ ε := Real.rpow_pos_of_pos hxpos ε
  rw [hsplit, lt_div_iff₀ hxe] at h1
  have h2 : ((d * b : ℕ) : ℝ) ^ ε < b := by
    have h1' : (d : ℝ) * ((d * b : ℕ) : ℝ) ^ ε < (d : ℝ) * b := h1.trans_eq hxd
    exact lt_of_mul_lt_mul_left h1' (by positivity)
  have h3 : ((d * b : ℕ) : ℝ) < (b : ℝ) ^ (1 / ε) := by
    have h := Real.rpow_lt_rpow hxe.le h2 (by positivity : (0 : ℝ) < 1 / ε)
    rwa [← Real.rpow_mul hxpos.le, mul_one_div_cancel hε.ne', Real.rpow_one] at h
  have hdx : (d : ℝ) ≤ ((d * b : ℕ) : ℝ) := by rw [hxd]; nlinarith
  have hfin : (d : ℝ) < (⌈(b : ℝ) ^ (1 / ε)⌉₊ : ℝ) :=
    lt_of_lt_of_le (hdx.trans_lt h3) (Nat.le_ceil _)
  exact_mod_cast hfin
