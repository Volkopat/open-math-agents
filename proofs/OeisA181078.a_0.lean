import FormalConjectures.OEIS.«181078»

open PowerSeries OeisA181078

theorem OMA.solution : type_of% @OeisA181078.a_0 := by
  rw [a, hannaExp, coeff_subst' ⟨1, by rfl⟩, finsum_eq_single _ 0] <;>
    simp_all [hannaLog]
