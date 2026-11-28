import FormalConjectures.Wikipedia.WallSunSun

/-! Obtain a quadratic relation from a basis extending 1, then retain the squarefree normalization. -/

-- Problem: Infinitude of Wall–Sun–Sun primes — exists quadraticAlgebra of isQuadraticExtension
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/WallSunSun.lean:78 (declaration NumberField.exists_quadraticAlgebra_of_isQuadraticExtension)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Polynomial

theorem OMA.solution : type_of% @NumberField.exists_quadraticAlgebra_of_isQuadraticExtension := by
  intro K _ _ _
  have hfr : Module.finrank ℚ K = 2 := Algebra.IsQuadraticExtension.finrank_eq_two ℚ K
  obtain ⟨α, hlin⟩ := exists_linearIndependent_pair_of_one_lt_finrank
    (show 1 < Module.finrank ℚ K by omega) (one_ne_zero : (1 : K) ≠ 0)
  have hα : α ∉ (algebraMap ℚ K).range := by
    rintro ⟨q, hq⟩
    have hh := LinearIndependent.pair_iff.mp hlin q (-1)
      (by simp [Algebra.smul_def, hq])
    norm_num at hh
  let B := Module.Basis.mk hlin
    (hlin.span_eq_top_of_card_eq_finrank (by simp [hfr])).ge
  have hb (i) : B i = ![(1 : K), α] i := by simp [B]
  let c0 := -(B.repr (α ^ 2) 0)
  let c1 := -(B.repr (α ^ 2) 1)
  have hrel : α ^ 2 + algebraMap ℚ K c1 * α + algebraMap ℚ K c0 = 0 := by
    have hs := B.sum_repr (α ^ 2)
    rw [Fin.sum_univ_two, hb, hb] at hs
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Algebra.smul_def, mul_one] at hs
    dsimp [c0, c1]
    rw [map_neg, map_neg]
    linear_combination -hs
  set β : K := 2 * α + algebraMap ℚ K c1 with hβdef
  set r : ℚ := c1 ^ 2 - 4 * c0 with hr
  have hβsq : β ^ 2 = algebraMap ℚ K r := by
    simp only [hβdef, hr, map_sub, map_mul, map_pow, map_ofNat]
    linear_combination 4 * hrel
  have hβ : β ∉ (algebraMap ℚ K).range := by
    rintro ⟨q, hq⟩
    apply hα
    refine ⟨(q - c1) / 2, ?_⟩
    rw [map_div₀, map_sub, hq, map_ofNat]
    simp only [hβdef]
    ring
  set N : ℤ := r.num * r.den with hN
  set δ : K := (r.den : K) * β with hδdef
  have hδsq : δ ^ 2 = (N : K) := by
    rw [hδdef, mul_pow, hβsq, hN]
    rw [show algebraMap ℚ K r = (r : K) from rfl]
    have hden : (r.den : K) ≠ 0 := by exact_mod_cast r.den_ne_zero
    rw [Rat.cast_def]
    push_cast
    field_simp
  have hδ : δ ∉ (algebraMap ℚ K).range := by
    rintro ⟨q, hq⟩
    apply hβ
    refine ⟨q / r.den, ?_⟩
    have hden : (r.den : K) ≠ 0 := by exact_mod_cast r.den_ne_zero
    rw [map_div₀, hq, map_natCast, hδdef]
    field_simp
  have hN0 : N ≠ 0 := by
    intro h0
    apply hδ
    refine ⟨0, ?_⟩
    rw [map_zero]
    have : δ ^ 2 = 0 := by rw [hδsq, h0, Int.cast_zero]
    exact (pow_eq_zero_iff (by norm_num)).mp this |>.symm
  obtain ⟨m, s, hms, hsqf⟩ := Nat.sq_mul_squarefree N.natAbs
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hms
    exact hN0 (Int.natAbs_eq_zero.mp hms.symm)
  set d : ℤ := N.sign * m with hd
  have hNd : N = (s : ℤ) ^ 2 * d := by
    rw [hd]
    conv_lhs => rw [← Int.sign_mul_natAbs N, ← hms]
    push_cast
    ring
  have hdsq : Squarefree d := by
    rw [← Int.squarefree_natAbs, hd, Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hN0, one_mul,
      Int.natAbs_natCast]
    exact hsqf
  have hsK : (s : K) ≠ 0 := by exact_mod_cast hs0
  set γ : K := δ / s with hγdef
  have hγsq : γ * γ = (d : K) := by
    have : γ ^ 2 = (d : K) := by
      rw [hγdef, div_pow, hδsq, hNd]
      push_cast
      field_simp
    rw [← this]; ring
  have hγ : γ ∉ (algebraMap ℚ K).range := by
    rintro ⟨q, hq⟩
    apply hδ
    refine ⟨q * s, ?_⟩
    rw [map_mul, hq, map_natCast, hγdef]
    field_simp
  have hd1 : d ≠ 1 := by
    rintro h1
    rw [h1, Int.cast_one] at hγsq
    have : (γ - 1) * (γ + 1) = 0 := by linear_combination hγsq
    rcases mul_eq_zero.mp this with h | h
    · exact hγ ⟨1, by rw [map_one]; linear_combination -h⟩
    · exact hγ ⟨-1, by rw [map_neg, map_one]; linear_combination -h⟩
  let f : QuadraticAlgebra ℚ (d : ℚ) 0 →ₐ[ℚ] K :=
    QuadraticAlgebra.lift ⟨γ, by
      rw [hγsq, zero_smul, add_zero, Algebra.smul_def, mul_one]
      simp⟩
  have hf : ∀ x : QuadraticAlgebra ℚ (d : ℚ) 0, f x = x.re • 1 + x.im • γ := fun x => rfl
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    rw [hf] at hx
    by_cases him : x.im = 0
    · rw [him, zero_smul, add_zero, Algebra.smul_def, mul_one] at hx
      have hre : x.re = 0 := (algebraMap ℚ K).injective (by rw [hx, map_zero])
      ext <;> simp [hre, him]
    · exfalso
      apply hγ
      refine ⟨-(x.re / x.im), ?_⟩
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hx
      have hK : algebraMap ℚ K x.im ≠ 0 := by simpa using him
      rw [map_neg, map_div₀]
      field_simp
      first | linear_combination hx | linear_combination -hx
  have hsurj : Function.Surjective f := by
    have := LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := f.toLinearMap) (by rw [QuadraticAlgebra.finrank_eq_two, hfr])
    exact this.mp hinj
  exact ⟨d, hd1, hdsq, ⟨(AlgEquiv.ofBijective f ⟨hinj, hsurj⟩).symm.toRingEquiv⟩⟩
