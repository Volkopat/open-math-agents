import FormalConjectures.Paper.KaplanskyUInvariant

/-! Shorter proof of `KaplanskyUInvariant.u_invariant_values.variants.not_three`. -/

open QuadraticMap QuadraticForm

theorem OMA.solution : type_of% @KaplanskyUInvariant.u_invariant_values.variants.not_three := by
  rintro ⟨F, _, _, hmax, hub⟩
  obtain ⟨Q, hQ⟩ := mem_anisotropicDims_iff.mp hmax
  have := invertibleOfNonzero (two_ne_zero : (2 : F) ≠ 0)
  obtain ⟨w, ⟨e⟩⟩ := Q.equivalent_weightedSumSquares
  have hW : (weightedSumSquares F w).Anisotropic := fun v hv => by
    have := hQ _ (by rw [← e.map_app (e.symm v)]; simpa using hv); simpa using this
  have hm : Module.finrank F (Fin 3 → F) = 3 := by simp
  generalize Module.finrank F (Fin 3 → F) = m at w hW hm
  subst hm
  set a := w 0; set b := w 1; set c := w 2
  have h3 (x y z : F) (hxyz : a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0) :
      x = 0 ∧ y = 0 ∧ z = 0 := by
    have hv := hW ![x, y, z] (by simp [Fin.sum_univ_three]; linear_combination hxyz)
    exact ⟨by simpa using congr_fun hv 0, by simpa using congr_fun hv 1, by simpa using congr_fun hv 2⟩
  have ha : a ≠ 0 := fun ha0 => one_ne_zero (h3 1 0 0 (by rw [ha0]; ring)).1
  have h4 : 4 ∈ anisotropicDims F :=
    mem_anisotropicDims_iff.mpr ⟨weightedSumSquares F ![a, b, c, a * b * c], fun v hv => by
      simp [Fin.sum_univ_four] at hv
      have heq : a * v 0 ^ 2 + b * v 1 ^ 2 + c * v 2 ^ 2 + a * b * c * v 3 ^ 2 = 0 := by
        linear_combination hv
      by_cases hN : v 2 ^ 2 + a * b * v 3 ^ 2 = 0
      · obtain ⟨hz, hw, -⟩ := h3 (v 2 / a) (v 3) 0 (by
          rw [show a * (v 2 / a) ^ 2 + b * v 3 ^ 2 + c * 0 ^ 2 = (v 2 ^ 2 + a * b * v 3 ^ 2) / a by
            field_simp; ring, hN, zero_div])
        have hz' : v 2 = 0 := (div_eq_zero_iff.mp hz).resolve_right ha
        obtain ⟨hx, hy, -⟩ := h3 (v 0) (v 1) 0 (by rw [hz', hw] at heq; linear_combination heq)
        ext i; fin_cases i <;> assumption
      · exact absurd (h3 (v 0 * v 2 + b * v 1 * v 3) (a * v 0 * v 3 - v 1 * v 2)
          (v 2 ^ 2 + a * b * v 3 ^ 2)
          (by linear_combination (v 2 ^ 2 + a * b * v 3 ^ 2) * heq)).2.2 hN⟩
  have := hub h4; omega
