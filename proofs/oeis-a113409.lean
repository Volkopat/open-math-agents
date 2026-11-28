import OMAStatements.S_oeis_a113409

/-!
# A recurrence for OEIS A113409

Source: https://oeis.org/A113409/internal
The recurrence is due to R. J. Mathar (Nov 07 2012).
The upstream formal statement is by @hermitokatt.
Proof: @grp06.
-/

namespace OMAA113409

open PowerSeries
open scoped BigOperators

noncomputable section

private abbrev Series := PowerSeries ℤ

private def S : Series := PowerSeries.mk (fun _ => 1)
private def t : Series := (PowerSeries.X : Series) ^ 2 * S
private def c (k : ℕ) : ℤ := (k.choose (k / 2) : ℤ)
private def G : Series := PowerSeries.mk c
private def F : Series := PowerSeries.mk (fun k => (Nat.centralBinom k : ℤ))
private def A : Series := S * G.subst t
private def B : Series := 1 + 2 * ((PowerSeries.X : Series) ^ 2 * A)

private theorem coeff_two (n : ℕ) (P : Series) :
    coeff n (2 * P) = 2 * coeff n P := by
  have h : C (2 : ℤ) = (2 : Series) := map_ofNat C 2
  rw [← h, coeff_C_mul]

private theorem coeff_four (n : ℕ) (P : Series) :
    coeff n (4 * P) = 4 * coeff n P := by
  have h : C (4 : ℤ) = (4 : Series) := map_ofNat C 4
  rw [← h, coeff_C_mul]

private theorem coeff_S (n : ℕ) : coeff n S = 1 := coeff_mk _ _

private theorem geom : (1 - (PowerSeries.X : Series)) * S = 1 := by
  apply PowerSeries.ext
  intro n
  rw [sub_mul, one_mul, map_sub, coeff_S]
  cases n with
  | zero => simp [coeff_zero_X_mul, coeff_one]
  | succ n => simp [coeff_succ_X_mul, coeff_S, coeff_one]

private theorem coeff_geom_pow (k n : ℕ) :
    coeff n (S ^ (k + 1)) = ((n + k).choose k : ℤ) := by
  induction k generalizing n with
  | zero => simp [coeff_S]
  | succ k ih =>
    rw [pow_succ, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [coeff_S, mul_one, ih]
    have h := congrArg (fun z : ℕ => (z : ℤ)) (Nat.sum_range_add_choose n k)
    simpa only [Nat.cast_sum, Nat.succ_eq_add_one, Nat.add_assoc] using h

private theorem has_t : HasSubst t := by
  apply HasSubst.of_constantCoeff_zero'
  simp [t]

private theorem has_t_sq : HasSubst (t ^ 2) := by
  apply HasSubst.of_constantCoeff_zero'
  simp [t]

private theorem t_pow (k : ℕ) : t ^ k = (PowerSeries.X : Series) ^ (2 * k) * S ^ k := by
  rw [t, mul_pow, pow_mul]

private theorem coeff_t_pow_of_lt (n k : ℕ) (h : n < 2 * k) :
    coeff n (t ^ k) = 0 := by
  rw [t_pow, coeff_X_pow_mul', if_neg (by omega)]

private theorem coeff_A (n : ℕ) :
    coeff n A = OMA.S_oeis_a113409.a n := by
  let P : Series := ∑ k ∈ Finset.range (n / 2 + 1), C (c k) * t ^ k
  have hP (j : ℕ) (hj : j ≤ n) : coeff j (G.subst t) = coeff j P := by
    rw [coeff_subst' has_t, finsum_eq_sum_of_support_subset
      (s := Finset.range (n / 2 + 1))]
    · simp only [P, map_sum, coeff_C_mul, G, coeff_mk, smul_eq_mul]
    · intro k hk
      apply Finset.mem_coe.mpr
      rw [Finset.mem_range]
      by_contra! h
      have hz := coeff_t_pow_of_lt j k (by omega)
      exact (Function.mem_support.mp hk) (by rw [hz, smul_zero])
  have heq : coeff n A = coeff n (S * P) := by
    rw [A, coeff_mul, coeff_mul]
    apply Finset.sum_congr rfl
    intro ij hij
    rw [hP ij.2 (by have h := Finset.HasAntidiagonal.mem_antidiagonal.mp hij; omega)]
  rw [heq]
  change coeff n (S * (∑ k ∈ Finset.range (n / 2 + 1), C (c k) * t ^ k)) = _
  rw [Finset.mul_sum, map_sum, OMA.S_oeis_a113409.a]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < n / 2 + 1 := Finset.mem_range.mp hk
  have hkn : 2 * k ≤ n := by omega
  rw [show S * (C (c k) * t ^ k) =
      C (c k) * ((PowerSeries.X : Series) ^ (2 * k) * S ^ (k + 1)) by rw [t_pow, pow_succ]; ring]
  rw [coeff_C_mul, coeff_X_pow_mul', if_pos hkn, coeff_geom_pow]
  rw [show n - 2 * k + k = n - k by omega, c, mul_comm]

private theorem central_step (n : ℕ) :
    ((n : ℤ) + 1) * (Nat.centralBinom (n + 1) : ℤ) =
      2 * (2 * (n : ℤ) + 1) * (Nat.centralBinom n : ℤ) := by
  exact_mod_cast Nat.succ_mul_centralBinom_succ n

private theorem F_ode : (1 - 4 * (PowerSeries.X : Series)) * (PowerSeries.derivative ℤ) F = 2 * F := by
  apply PowerSeries.ext
  intro n
  rw [sub_mul, one_mul, mul_assoc, map_sub, coeff_four, coeff_two]
  cases n with
  | zero =>
    norm_num [coeff_zero_X_mul, coeff_derivative, F, Nat.centralBinom, Nat.choose]
  | succ n =>
    rw [coeff_succ_X_mul]
    simp only [coeff_derivative, F, coeff_mk, Nat.cast_succ]
    have h := central_step (n + 1)
    push_cast at h
    linear_combination h

private theorem c_even (k : ℕ) : c (2 * k) = (Nat.centralBinom k : ℤ) := by
  rw [c, show 2 * k / 2 = k by omega, Nat.centralBinom]

private theorem c_odd (k : ℕ) : 2 * c (2 * k + 1) = (Nat.centralBinom (k + 1) : ℤ) := by
  rw [c, show (2 * k + 1) / 2 = k by omega, Nat.centralBinom,
    show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
    Nat.choose_succ_succ', Nat.choose_symm_half, Nat.cast_add]
  ring

private def E : Series := F.subst ((PowerSeries.X : Series) ^ 2)

private theorem coeff_E_even (k : ℕ) : coeff (2 * k) E = (Nat.centralBinom k : ℤ) := by
  rw [E, coeff_subst_X_pow (by decide : (2 : ℕ) ≠ 0), if_pos (dvd_mul_right 2 k),
    show 2 * k / 2 = k by omega, F, coeff_mk, Algebra.algebraMap_self, RingHom.id_apply]

private theorem coeff_E_odd (k : ℕ) : coeff (2 * k + 1) E = 0 := by
  rw [E, coeff_subst_X_pow (by decide : (2 : ℕ) ≠ 0), if_neg]
  rw [Nat.dvd_iff_mod_eq_zero]
  omega

private theorem parity_series : 1 + 2 * ((PowerSeries.X : Series) * G) = (1 + 2 * (PowerSeries.X : Series)) * E := by
  apply PowerSeries.ext
  intro n
  rw [add_mul, one_mul, mul_assoc, map_add, map_add, coeff_two, coeff_two, coeff_one]
  cases n with
  | zero =>
    have h : coeff 0 E = 1 := by
      simpa [Nat.centralBinom, Nat.choose] using coeff_E_even 0
    simp only [coeff_zero_X_mul, if_true, mul_zero, add_zero, h]
  | succ n =>
    rw [coeff_succ_X_mul, coeff_succ_X_mul]
    simp only [Nat.succ_ne_zero, if_false, zero_add, G, coeff_mk]
    by_cases h : n % 2 = 0
    · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
      rw [coeff_E_even, coeff_E_odd, c_even, zero_add]
    · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
      rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega,
        coeff_E_even, coeff_E_odd, c_odd, mul_zero, add_zero]

private def H : Series := F.subst (t ^ 2)

private theorem B_factor : B = (1 + 2 * t) * H := by
  have h := congrArg (substAlgHom (R := ℤ) has_t) parity_series
  change substAlgHom (R := ℤ) has_t (1 + 2 * ((PowerSeries.X : Series) * G)) =
    substAlgHom (R := ℤ) has_t ((1 + 2 * (PowerSeries.X : Series)) * E) at h
  simp only [map_add, map_one, map_ofNat, map_mul, substAlgHom_X] at h
  simp only [E, coe_substAlgHom,
    subst_comp_subst_apply (HasSubst.X_pow (by decide : (2 : ℕ) ≠ 0)) has_t,
    subst_pow has_t, subst_X has_t] at h
  simpa only [B, A, H, t, mul_assoc] using h

private theorem Dmul (P Q : Series) : (PowerSeries.derivative ℤ) (P * Q) = P * (PowerSeries.derivative ℤ) Q + Q * (PowerSeries.derivative ℤ) P := by
  simpa only [smul_eq_mul] using Derivation.leibniz (PowerSeries.derivative ℤ) P Q

private theorem Dtwo : (PowerSeries.derivative ℤ) (2 : Series) = 0 := Derivation.map_natCast (PowerSeries.derivative ℤ) 2

private theorem Dsq (P : Series) : (PowerSeries.derivative ℤ) (P ^ 2) = 2 * P * (PowerSeries.derivative ℤ) P := by
  have h := PowerSeries.derivative_pow P 2
  change (PowerSeries.derivative ℤ) (P ^ 2) = 2 * P ^ 1 * (PowerSeries.derivative ℤ) P at h
  simpa only [pow_one] using h

private theorem H_ode : (1 - 4 * t ^ 2) * (PowerSeries.derivative ℤ) H = 4 * t * (PowerSeries.derivative ℤ) t * H := by
  have h := congrArg (substAlgHom (R := ℤ) has_t_sq) F_ode
  change substAlgHom (R := ℤ) has_t_sq ((1 - 4 * (PowerSeries.X : Series)) * (PowerSeries.derivative ℤ) F) =
    substAlgHom (R := ℤ) has_t_sq (2 * F) at h
  simp only [map_sub, map_one, map_ofNat, map_mul, substAlgHom_X] at h
  simp only [coe_substAlgHom] at h
  rw [H, derivative_subst has_t_sq, Dsq, ← mul_assoc, h]
  ring

private theorem B_ode_t : (1 - 4 * t ^ 2) * (PowerSeries.derivative ℤ) B = 2 * (PowerSeries.derivative ℤ) t * B := by
  have hD : (PowerSeries.derivative ℤ) (1 + 2 * t) = 2 * (PowerSeries.derivative ℤ) t := by
    rw [map_add, derivative_one, Dmul, Dtwo, mul_zero, add_zero, zero_add]
  calc
    (1 - 4 * t ^ 2) * (PowerSeries.derivative ℤ) B =
        (1 + 2 * t) * ((1 - 4 * t ^ 2) * (PowerSeries.derivative ℤ) H) +
        (1 - 4 * t ^ 2) * H * (2 * (PowerSeries.derivative ℤ) t) := by rw [B_factor, Dmul, hD]; ring
    _ = 2 * (PowerSeries.derivative ℤ) t * B := by rw [H_ode, B_factor]; ring

private theorem geom_sq : (1 - (PowerSeries.X : Series)) ^ 2 * S ^ 2 = 1 := by
  rw [← mul_pow, geom, one_pow]

private theorem Dgeom : (PowerSeries.derivative ℤ) S = S ^ 2 := by
  have h : S * (1 - (PowerSeries.X : Series)) = 1 := by rw [mul_comm, geom]
  simpa only [smul_eq_mul, map_sub, derivative_one, derivative_X, zero_sub,
    mul_neg, mul_one, neg_neg] using Derivation.leibniz_of_mul_eq_one (PowerSeries.derivative ℤ) h

private theorem t_ode : (1 - (PowerSeries.X : Series)) ^ 2 * (PowerSeries.derivative ℤ) t = 2 * (PowerSeries.X : Series) - (PowerSeries.X : Series) ^ 2 := by
  calc
    (1 - (PowerSeries.X : Series)) ^ 2 * (PowerSeries.derivative ℤ) t =
        (2 * (PowerSeries.X : Series) * (1 - (PowerSeries.X : Series))) * ((1 - (PowerSeries.X : Series)) * S) +
          (PowerSeries.X : Series) ^ 2 * ((1 - (PowerSeries.X : Series)) ^ 2 * S ^ 2) := by
      rw [t, Dmul, Dgeom, Dsq, derivative_X]
      ring
    _ = _ := by rw [geom, geom_sq]; ring

private theorem B_ode : (1 - 2 * (PowerSeries.X : Series) + (PowerSeries.X : Series) ^ 2 - 4 * (PowerSeries.X : Series) ^ 4) * (PowerSeries.derivative ℤ) B =
    (4 * (PowerSeries.X : Series) - 2 * (PowerSeries.X : Series) ^ 2) * B := by
  have h : (1 - (PowerSeries.X : Series)) ^ 2 * (1 - 4 * t ^ 2) = 1 - 2 * (PowerSeries.X : Series) + (PowerSeries.X : Series) ^ 2 - 4 * (PowerSeries.X : Series) ^ 4 := by
    calc
      (1 - (PowerSeries.X : Series)) ^ 2 * (1 - 4 * t ^ 2) =
          (1 - (PowerSeries.X : Series)) ^ 2 - 4 * (PowerSeries.X : Series) ^ 4 * ((1 - (PowerSeries.X : Series)) ^ 2 * S ^ 2) := by rw [t]; ring
      _ = _ := by rw [geom_sq]; ring
  calc
    _ = (1 - (PowerSeries.X : Series)) ^ 2 * ((1 - 4 * t ^ 2) * (PowerSeries.derivative ℤ) B) := by rw [← h, mul_assoc]
    _ = (2 * ((1 - (PowerSeries.X : Series)) ^ 2 * (PowerSeries.derivative ℤ) t)) * B := by rw [B_ode_t]; ring
    _ = _ := by rw [t_ode]; ring

private theorem coeff_B (k : ℕ) :
    coeff (k + 2) B = 2 * OMA.S_oeis_a113409.a k := by
  rw [B, map_add, coeff_one, if_neg (by omega), zero_add, coeff_two,
    coeff_X_pow_mul, coeff_A]

private theorem recurrence (n : ℕ) (hn : 4 ≤ n) :
    ((n : ℤ) + 2) * OMA.S_oeis_a113409.a n -
      2 * ((n : ℤ) + 1) * OMA.S_oeis_a113409.a (n - 1) +
      ((n : ℤ) - 4) * OMA.S_oeis_a113409.a (n - 2) +
      2 * OMA.S_oeis_a113409.a (n - 3) +
      4 * (2 - (n : ℤ)) * OMA.S_oeis_a113409.a (n - 4) = 0 := by
  have cb (j k : ℕ) (hjk : j = k + 2) :
      coeff j B = 2 * OMA.S_oeis_a113409.a k := by
    rw [hjk, coeff_B]
  have h := congrArg (coeff (R := ℤ) (n + 1)) B_ode
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub, coeff_two, coeff_four,
    coeff_succ_X_mul, coeff_X_pow_mul', if_pos (show 2 ≤ n + 1 by omega),
    if_pos (show 4 ≤ n + 1 by omega), coeff_derivative] at h
  rw [cb (n + 1 + 1) n rfl,
    cb (n + 1) (n - 1) (by omega),
    cb (n + 1 - 2 + 1) (n - 2) (by omega),
    cb (n + 1 - 4 + 1) (n - 4) (by omega),
    cb n (n - 2) (by omega),
    cb (n + 1 - 2) (n - 3) (by omega)] at h
  simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_sub (show 2 ≤ n + 1 by omega),
    Nat.cast_sub (show 4 ≤ n + 1 by omega), Nat.cast_one] at h
  apply mul_left_cancel₀ (show (2 : ℤ) ≠ 0 by decide)
  linear_combination h

end

end OMAA113409

theorem OMA.solution : type_of% @OMA.S_oeis_a113409.main := by
  exact OMAA113409.recurrence
