import FormalConjectures.OEIS.«183128»

open PowerSeries OeisA183128

theorem OMA.solution : type_of% @OeisA183128.a_0 := by
  have h (f : ℕ → ℕ → ℤ) : constantCoeff (hannaLog f) = 0 := by simp [hannaLog]
  rw [a, hannaExp, coeff_subst' (.of_constantCoeff_zero' (h _)), finsum_eq_single _ 0] <;> simp [h] <;> omega
