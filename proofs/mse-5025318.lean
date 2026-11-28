import OMAStatements.S_mse_5025318

/-!
Retains @romechenko’s counterexample proof #16491. Standard localization clears
both polynomial denominators simultaneously; the modular collision argument is
unchanged. Statement: @pyaf, #12730.
-/

open MvPolynomial

private theorem clearPair (f g : MvPolynomial (Fin 2) ℚ) :
    ∃ d : ℕ, 0 < d ∧ ∃ F G : MvPolynomial (Fin 2) ℤ,
      map (Int.castRingHom ℚ) F = C (d : ℚ) * f ∧
      map (Int.castRingHom ℚ) G = C (d : ℚ) * g := by
  let := MvPolynomial.algebraMvPolynomial (σ := Fin 2) (R := ℤ) (S := ℚ)
  obtain ⟨⟨_, z, hz, rfl⟩, h⟩ :=
    IsLocalization.exist_integer_multiples_of_finite
      ((nonZeroDivisors ℤ).map (C (σ := Fin 2))) ![f, g]
  obtain ⟨F, hF⟩ := h 0
  obtain ⟨G, hG⟩ := h 1
  have hz0 : z ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hz
  simp only [Algebra.smul_def, MvPolynomial.algebraMap_def, map_C,
    Matrix.cons_val_zero, Matrix.cons_val_one] at hF hG
  change map (Int.castRingHom ℚ) F = C (z : ℚ) * f at hF
  change map (Int.castRingHom ℚ) G = C (z : ℚ) * g at hG
  refine ⟨z.natAbs ^ 2, pow_pos (Int.natAbs_pos.mpr hz0) _, C z * F, C z * G, ?_, ?_⟩
  all_goals
    simp only [map_mul, map_C, hF, hG]
    rw [← mul_assoc, ← map_mul]
    congr 2
    simp [Nat.cast_natAbs, ← sq, sq_abs]

private noncomputable def value (F : MvPolynomial (Fin 2) ℤ) (x y : ℤ) : ℤ :=
  eval ![x, y] F

private theorem value_cast {R : Type*} [CommRing R]
    (F : MvPolynomial (Fin 2) ℤ) (x y : ℤ) :
    (value F x y : R) = eval₂ (Int.castRingHom R) ![(x : R), (y : R)] F := by
  change Int.castRingHom R (eval ![x, y] F) = _
  rw [eval₂_comp]
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem scaledValue {d : ℕ} {F : MvPolynomial (Fin 2) ℤ}
    {f : MvPolynomial (Fin 2) ℚ} (hF : map (Int.castRingHom ℚ) F = C (d : ℚ) * f)
    {x y : ℕ} {a : ℤ} (ha : OMA.S_mse_5025318.ev f x y = a) :
    value F x y = (d : ℤ) * a := by
  apply Int.cast_injective (α := ℚ)
  rw [value_cast, ← eval_map, hF]
  simp only [Int.cast_natCast, map_mul, eval_C, Int.cast_mul]
  change (d : ℚ) * OMA.S_mse_5025318.ev f x y = (d : ℚ) * (a : ℚ)
  rw [ha]

private theorem divisibleAtNegative {d : ℕ} {F : MvPolynomial (Fin 2) ℤ}
    (hF : (d : ℤ) ∣ value F 0 0) : (d : ℤ) ∣ value F (-(d : ℤ)) 0 := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  have hzero := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hF
  rw [value_cast] at hzero ⊢
  simpa only [Int.cast_neg, Int.cast_natCast, Int.cast_zero, ZMod.natCast_self, neg_zero]
    using hzero

private noncomputable def modularPair (q : ℕ) (F G : MvPolynomial (Fin 2) ℤ)
    (p : ZMod q × ZMod q) : ZMod q × ZMod q :=
  (eval₂ (Int.castRingHom (ZMod q)) ![p.1, p.2] F,
    eval₂ (Int.castRingHom (ZMod q)) ![p.1, p.2] G)

private theorem modularPair_value (q : ℕ) (F G : MvPolynomial (Fin 2) ℤ)
    (x y : ℤ) :
    modularPair q F G ((x : ZMod q), (y : ZMod q)) =
      ((value F x y : ZMod q), (value G x y : ZMod q)) := by
  simp only [modularPair, value_cast]

theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_5025318.main) := by
  rintro ⟨f, g, hinteger, hsurj⟩
  obtain ⟨d, hd, F, G, hF, hG⟩ := clearPair f g
  have hscaled (a b : ℤ) :
      ∃ x y : ℕ, value F x y = (d : ℤ) * a ∧ value G x y = (d : ℤ) * b := by
    obtain ⟨x, y, ha, hb⟩ := hsurj a b
    exact ⟨x, y, scaledValue hF ha, scaledValue hG hb⟩
  obtain ⟨a₀, b₀, ha₀, hb₀⟩ := hinteger 0 0
  obtain ⟨a, ha⟩ := divisibleAtNegative ⟨a₀, scaledValue hF ha₀⟩
  obtain ⟨b, hb⟩ := divisibleAtNegative ⟨b₀, scaledValue hG hb₀⟩
  obtain ⟨x, y, hx, hy⟩ := hscaled a b
  let t := x + d + 1
  let q := d * t + 1
  have hq : 0 < q := by dsimp [q]; positivity
  let : NeZero q := ⟨hq.ne'⟩
  have hlarge : x + d < q := by
    have h := Nat.mul_le_mul_right t (show 1 ≤ d by omega)
    simp only [one_mul] at h
    dsimp [q, t] at h ⊢
    omega
  have hunit : (d : ZMod q) * -(t : ZMod q) = 1 := by
    have hz : (d : ZMod q) * (t : ZMod q) + 1 = 0 := by
      calc
        _ = ((q : ℕ) : ZMod q) := by
          change _ = ((d * t + 1 : ℕ) : ZMod q)
          push_cast
          rfl
        _ = 0 := ZMod.natCast_self q
    linear_combination -hz
  have hlift (r : ZMod q) :
      (d : ZMod q) * ((-(t : ℤ) * (r.val : ℤ) : ℤ) : ZMod q) = r := by
    push_cast
    rw [← mul_assoc, hunit, one_mul, ZMod.natCast_zmod_val]
  have hmodSurj : Function.Surjective (modularPair q F G) := by
    rintro ⟨r, s⟩
    obtain ⟨u, v, hu, hv⟩ := hscaled (-(t : ℤ) * r.val) (-(t : ℤ) * s.val)
    refine ⟨((u : ZMod q), (v : ZMod q)), ?_⟩
    rw [← Int.cast_natCast u, ← Int.cast_natCast v, modularPair_value, hu, hv]
    simpa only [Int.cast_mul, Int.cast_natCast] using congrArg₂ Prod.mk (hlift r) (hlift s)
  have hmodInj := Finite.injective_iff_surjective.mpr hmodSurj
  have heq : (((x : ℤ) : ZMod q), ((y : ℤ) : ZMod q)) =
      ((Int.cast (-(d : ℤ)) : ZMod q), ((0 : ℤ) : ZMod q)) := by
    apply hmodInj
    rw [modularPair_value q F G (x : ℤ) (y : ℤ),
      modularPair_value q F G (-(d : ℤ)) 0, hx, hy, ha, hb]
  have hfirst : (x : ZMod q) = -(d : ZMod q) := by
    simpa only [Int.cast_natCast, Int.cast_neg] using congrArg Prod.fst heq
  have hz : ((x + d : ℕ) : ZMod q) = 0 := by
    rw [Nat.cast_add, hfirst, neg_add_cancel]
  exact (not_le_of_gt hlarge) (Nat.le_of_dvd (by omega) ((ZMod.natCast_eq_zero_iff _ _).mp hz))
