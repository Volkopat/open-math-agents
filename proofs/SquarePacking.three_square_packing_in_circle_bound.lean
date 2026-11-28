import FormalConjectures.Wikipedia.SquarePacking

/-!
# Shorter proof of `SquarePacking.three_square_packing_in_circle_bound`
-/

open SquarePacking

theorem OMA.solution : type_of% @SquarePacking.three_square_packing_in_circle_bound := by
  let f : Fin 3 → EuclideanSpace ℝ (Fin 2) := ![!₂[-1, -13/16], !₂[0, -13/16], !₂[-1/2, 3/16]]
  refine ⟨⟨fun i => .addRight (f i), fun i j h => Set.disjoint_left.mpr ?_, ?_⟩⟩
  · rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, e⟩
    have h0 := congrArg (· 0) e
    have h1 := congrArg (· 1) e
    simp [UnitSquare, Square] at ha hb
    fin_cases i <;> fin_cases j <;> simp [f] at h0 h1 h <;> linarith
  · rintro i _ ⟨a, ha, rfl⟩
    simp [UnitSquare, Square, SquarePacking.Circle, div_pow, mul_pow] at ha ⊢
    fin_cases i <;> simp [f] <;> nlinarith
