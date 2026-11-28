import OMAStatements.S_mse_5025318

open MvPolynomial

private theorem clearDenominators (f : MvPolynomial (Fin 2) ℚ) :
    ∃ d : ℕ, 0 < d ∧ ∃ F : MvPolynomial (Fin 2) ℤ,
      map (Int.castRingHom ℚ) F = C (d : ℚ) * f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    refine ⟨a.den, a.den_pos, C a.num, ?_⟩
    rw [map_C, ← map_mul]
    congr 1
    change (a.num : ℚ) = (a.den : ℚ) * a
    have hd : (a.den : ℚ) ≠ 0 := by positivity
    exact ((div_eq_iff hd).mp a.num_div_den).trans (mul_comm _ _)
  | add f g hf hg =>
    obtain ⟨d, hd, F, hF⟩ := hf
    obtain ⟨e, he, G, hG⟩ := hg
    refine ⟨d * e, Nat.mul_pos hd he, C (e : ℤ) * F + C (d : ℤ) * G, ?_⟩
    simp only [map_add, map_mul, map_C, Int.coe_castRingHom, Int.cast_natCast,
      hF, hG, Nat.cast_mul]
    ring
  | mul_X f i hf =>
    obtain ⟨d, hd, F, hF⟩ := hf
    refine ⟨d, hd, F * X i, ?_⟩
    simp only [map_mul, map_X, hF, mul_assoc]

private theorem clearPair (f g : MvPolynomial (Fin 2) ℚ) :
    ∃ d : ℕ, 0 < d ∧ ∃ F G : MvPolynomial (Fin 2) ℤ,
      map (Int.castRingHom ℚ) F = C (d : ℚ) * f ∧
      map (Int.castRingHom ℚ) G = C (d : ℚ) * g := by
  obtain ⟨d, hd, F, hF⟩ := clearDenominators f
  obtain ⟨e, he, G, hG⟩ := clearDenominators g
  refine ⟨d * e, Nat.mul_pos hd he, C (e : ℤ) * F, C (d : ℤ) * G, ?_, ?_⟩
  · simp only [map_mul, map_C, Int.coe_castRingHom, Int.cast_natCast, hF, Nat.cast_mul]
    ring
  · simp only [map_mul, map_C, Int.coe_castRingHom, Int.cast_natCast, hG, Nat.cast_mul]
    ring

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
