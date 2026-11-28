import OMAStatements.S_oeis_a007820

/-!
# Bala's divisibility conjecture for A007820

Peter Bala conjectured on March 30, 2025 that the Stirling number
`S(2m,m)` is divisible by `m^2` for every positive odd `m`.
Sources: https://oeis.org/A007820 and https://oeis.org/A007820/internal
Formal statement credit: @divmxnd0x
Proof credit: @grp06
-/

noncomputable section

open scoped BigOperators

namespace A007820Proof

open PowerSeries

private def stirlingSeries (R : Type*) [CommRing R] (m : ℕ) : PowerSeries R :=
  PowerSeries.mk fun k => (Nat.stirlingSecond (m + k) m : R)

private def factor (R : Type*) [CommRing R] (i : ℕ) : PowerSeries R :=
  1 - C (i : R) * X

private def denominator (R : Type*) [CommRing R] (m : ℕ) : PowerSeries R :=
  ∏ i ∈ Finset.range m, factor R (i + 1)

private theorem stirling_step (R : Type*) [CommRing R] (m : ℕ) :
    factor R (m + 1) * stirlingSeries R (m + 1) = stirlingSeries R m := by
  apply PowerSeries.ext
  intro k
  simp only [factor, sub_mul, one_mul, map_sub, mul_assoc, coeff_C_mul]
  cases k with
  | zero =>
    simp [stirlingSeries, Nat.stirlingSecond_self]
  | succ k =>
    simp only [coeff_succ_X_mul, stirlingSeries, coeff_mk]
    have hi : m + 1 + (k + 1) = (m + 1 + k) + 1 := by omega
    have hj : m + 1 + k = m + (k + 1) := by omega
    rw [hi, Nat.stirlingSecond_succ_succ, Nat.cast_add, Nat.cast_mul]
    rw [add_sub_cancel_left, hj]

private theorem stirling_denominator (R : Type*) [CommRing R] (m : ℕ) :
    denominator R m * stirlingSeries R m = 1 := by
  induction m with
  | zero =>
    change (∏ i ∈ Finset.range 0, factor R (i + 1)) * stirlingSeries R 0 = 1
    rw [Finset.prod_range_zero, one_mul]
    apply PowerSeries.ext
    intro k
    cases k <;> simp [stirlingSeries, Nat.stirlingSecond_succ_zero]
  | succ m ih =>
    simp only [denominator, Finset.prod_range_succ, mul_assoc, stirling_step]
    exact ih

private theorem linear_pow {R : Type*} [CommRing R] (c : R) (hc : c * c = 0)
    (j : ℕ) :
    (1 + C c * X : PowerSeries R) ^ j = 1 + C ((j : R) * c) * X := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, ih, Nat.cast_succ, add_mul (j : R) 1 c, one_mul, map_add]
    have hz : (C ((j : R) * c) : PowerSeries R) * C c = 0 := by
      rw [← map_mul, mul_assoc, hc, mul_zero, map_zero]
    calc
      (1 + C ((j : R) * c) * X) * (1 + C c * X) =
          1 + (C ((j : R) * c) + C c) * X +
            (C ((j : R) * c) * C c) * X ^ 2 := by ring
      _ = _ := by rw [hz, zero_mul, add_zero]

private theorem odd_coefficient {R : Type*} [CommRing R] (r : ℕ) (c : R)
    (hc : c * c = 0) (hm : ((2 * r + 1 : ℕ) : R) * c = 0)
    (E : PowerSeries R) :
    coeff (2 * r + 1)
      ((1 + C c * X) ^ (r + 1) * E.subst (X ^ 2 * (1 + C c * X))) = 0 := by
  let Q : PowerSeries R := 1 + C c * X
  let T : PowerSeries R := X ^ 2 * Q
  let P : PowerSeries R := ∑ j ∈ Finset.range (r + 1), C (coeff j E) * T ^ j
  change coeff (2 * r + 1) (Q ^ (r + 1) * E.subst T) = 0
  have hT : HasSubst T :=
    (PowerSeries.HasSubst.X_pow (R := R) (by decide : (2 : ℕ) ≠ 0)).mul_left
  have hTp (j : ℕ) : T ^ j = X ^ (2 * j) * Q ^ j := by
    change (X ^ 2 * Q) ^ j = X ^ (2 * j) * Q ^ j
    rw [mul_pow, pow_mul X 2 j]
  have htrunc (k : ℕ) (hk : k ≤ 2 * r + 1) :
      coeff k (E.subst T) = coeff k P := by
    rw [coeff_subst' hT, finsum_eq_sum_of_support_subset
      (s := Finset.range (r + 1))]
    · simp [P, map_sum, smul_eq_mul]
    · intro j hj
      by_contra hout
      have hlt : k < 2 * j := by
        simp only [Finset.mem_coe, Finset.mem_range, not_lt] at hout
        omega
      change (coeff j E • coeff k (T ^ j)) ≠ 0 at hj
      rw [hTp, coeff_X_pow_mul', if_neg (Nat.not_le_of_lt hlt), smul_zero] at hj
      exact hj rfl
  have hmul :
      coeff (2 * r + 1) (Q ^ (r + 1) * E.subst T) =
        coeff (2 * r + 1) (Q ^ (r + 1) * P) := by
    simp only [coeff_mul]
    apply Finset.sum_congr rfl
    intro p hp
    have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    rw [htrunc p.2 (by omega)]
  rw [hmul]
  simp only [P, Finset.mul_sum, map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  have hjle : j ≤ r := by
    have := Finset.mem_range.mp hj
    omega
  rw [hTp]
  have hmove :
      Q ^ (r + 1) * (C (coeff j E) * (X ^ (2 * j) * Q ^ j)) =
        C (coeff j E) * (X ^ (2 * j) * Q ^ (r + 1 + j)) := by
    rw [pow_add Q (r + 1) j]
    ac_rfl
  rw [hmove, coeff_C_mul, coeff_X_pow_mul', if_pos (by omega), show
    Q ^ (r + 1 + j) = 1 + C (((r + 1 + j : ℕ) : R) * c) * X from
      linear_pow c hc _]
  by_cases he : j = r
  · subst j
    have hdeg : 2 * r + 1 - 2 * r = 1 := by omega
    have hexp : r + 1 + r = 2 * r + 1 := by omega
    rw [hdeg, hexp, hm]
    simp
  · have h0 : 2 * r + 1 - 2 * j ≠ 0 := by omega
    have h1 : 2 * r + 1 - 2 * j ≠ 1 := by omega
    simp only [map_add, coeff_one, if_neg h0, zero_add, coeff_C_mul, coeff_X,
      if_neg h1, mul_zero]

private theorem paired_denominator {R : Type*} [CommRing R] (r : ℕ)
    (hc : ((2 * r + 1 : ℕ) : R) * ((2 * r + 1 : ℕ) : R) = 0) :
    let c : R := ((2 * r + 1 : ℕ) : R)
    let Q : PowerSeries R := 1 + C c * X
    let T : PowerSeries R := X ^ 2 * Q
    let D : PowerSeries R := ∏ i ∈ Finset.range r,
      (1 + C (((i + 1 : ℕ) : R) * ((2 * r - i : ℕ) : R)) * X)
    denominator R (2 * r + 1) * Q ^ (r + 1) = D.subst T := by
  dsimp only
  let c : R := ((2 * r + 1 : ℕ) : R)
  let Q : PowerSeries R := 1 + C c * X
  let T : PowerSeries R := X ^ 2 * Q
  let b (i : ℕ) : R := ((i + 1 : ℕ) : R) * ((2 * r - i : ℕ) : R)
  change denominator R (2 * r + 1) * Q ^ (r + 1) =
    (∏ i ∈ Finset.range r, (1 + C (b i) * X)).subst T
  have hcC : (C c : PowerSeries R) * C c = 0 := by
    rw [← map_mul, show c * c = 0 from hc, map_zero]
  have hlast : factor R (2 * r + 1) * Q = 1 := by
    change (1 - C c * X) * (1 + C c * X) = 1
    calc
      _ = 1 - (C c * C c) * X ^ 2 := by ring
      _ = 1 := by rw [hcC, zero_mul, sub_zero]
  have hpair (i : ℕ) (hi : i ∈ Finset.range r) :
      factor R (i + 1) * factor R (2 * r - i) * Q = 1 + C (b i) * T := by
    have hi' := Finset.mem_range.mp hi
    have hsum : (i + 1) + (2 * r - i) = 2 * r + 1 := by omega
    have hC : (C (((i + 1 : ℕ) : R)) : PowerSeries R) +
        C (((2 * r - i : ℕ) : R)) = C c := by
      rw [← map_add, ← Nat.cast_add, hsum]
    have hp : (C (((i + 1 : ℕ) : R)) : PowerSeries R) *
        C (((2 * r - i : ℕ) : R)) = C (b i) := by
      rw [← map_mul]
    calc
      _ = (1 - (C (((i + 1 : ℕ) : R)) + C (((2 * r - i : ℕ) : R))) * X) * Q +
          (C (((i + 1 : ℕ) : R)) * C (((2 * r - i : ℕ) : R))) * T := by
        unfold factor T
        ring
      _ = _ := by rw [hC, hp, show (1 - C c * X) * Q = 1 from hlast]
  have hreflect :
      (∏ i ∈ Finset.range r, factor R (r + i + 1)) =
        ∏ i ∈ Finset.range r, factor R (2 * r - i) := by
    rw [← Finset.prod_range_reflect (fun i => factor R (r + i + 1)) r]
    apply Finset.prod_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [show r + (r - 1 - i) + 1 = 2 * r - i by omega]
  have hden :
      denominator R (2 * r + 1) =
        (∏ i ∈ Finset.range r, (factor R (i + 1) * factor R (2 * r - i))) *
          factor R (2 * r + 1) := by
    unfold denominator
    rw [Finset.prod_range_succ, show 2 * r = r + r by omega, Finset.prod_range_add,
      hreflect, ← Finset.prod_mul_distrib, show r + r = 2 * r by omega]
  have hT : HasSubst T :=
    (PowerSeries.HasSubst.X_pow (R := R) (by decide : (2 : ℕ) ≠ 0)).mul_left
  let σ : PowerSeries R →ₐ[R] PowerSeries R := substAlgHom hT
  rw [← PowerSeries.coe_substAlgHom hT]
  change denominator R (2 * r + 1) * Q ^ (r + 1) =
    σ (∏ i ∈ Finset.range r, (1 + C (b i) * X))
  rw [hden, pow_succ, map_prod]
  calc
    _ = ((∏ i ∈ Finset.range r, (factor R (i + 1) * factor R (2 * r - i))) *
         Q ^ r) * (factor R (2 * r + 1) * Q) := by ac_rfl
    _ = ∏ i ∈ Finset.range r, (factor R (i + 1) * factor R (2 * r - i) * Q) := by
      rw [hlast, mul_one]
      symm
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [hpair i hi]
      have hσC : σ (C (b i)) = C (b i) := by
        change substAlgHom hT (C (b i)) = C (b i)
        rw [PowerSeries.coe_substAlgHom hT]
        exact PowerSeries.subst_C _
      have hσX : σ X = T := PowerSeries.substAlgHom_X hT
      rw [map_add σ 1 (C (b i) * X), map_one σ, map_mul σ (C (b i)) X, hσC, hσX]

theorem divisibility (r : ℕ) :
    (2 * r + 1) ^ 2 ∣ Nat.stirlingSecond (2 * (2 * r + 1)) (2 * r + 1) := by
  let m := 2 * r + 1
  let R := ZMod (m ^ 2)
  let Q : PowerSeries R := 1 + C (m : R) * X
  let T : PowerSeries R := X ^ 2 * Q
  let D : PowerSeries R := ∏ i ∈ Finset.range r,
    (1 + C (((i + 1 : ℕ) : R) * ((2 * r - i : ℕ) : R)) * X)
  let E := D.invOfUnit 1
  have hc : (m : R) * (m : R) = 0 := by
    rw [← Nat.cast_mul]
    exact (ZMod.natCast_eq_zero_iff (m * m) (m ^ 2)).2 (by rw [pow_two])
  have hT : HasSubst T :=
    (PowerSeries.HasSubst.X_pow (R := R) (by decide : (2 : ℕ) ≠ 0)).mul_left
  have hD : constantCoeff D = (↑(1 : Rˣ) : R) := by simp [D, map_prod]
  have hDE : D * E = 1 := PowerSeries.mul_invOfUnit D 1 hD
  have hsubst : D.subst T * E.subst T = 1 := by
    rw [← PowerSeries.subst_mul hT, hDE, ← PowerSeries.coe_substAlgHom hT, map_one]
  have hden : denominator R m * Q ^ (r + 1) = D.subst T :=
    paired_denominator r hc
  have hprod : denominator R m * (Q ^ (r + 1) * E.subst T) = 1 := by
    rw [← mul_assoc, hden, hsubst]
  have hseries : stirlingSeries R m = Q ^ (r + 1) * E.subst T := by
    calc
      _ = stirlingSeries R m * 1 := (mul_one _).symm
      _ = stirlingSeries R m * (denominator R m * (Q ^ (r + 1) * E.subst T)) :=
        congrArg (stirlingSeries R m * ·) hprod.symm
      _ = (denominator R m * stirlingSeries R m) * (Q ^ (r + 1) * E.subst T) := by
        ac_rfl
      _ = _ := by rw [stirling_denominator, one_mul]
  have hz : coeff m (stirlingSeries R m) = 0 := by
    rw [hseries]
    exact odd_coefficient r (m : R) hc hc E
  change m ^ 2 ∣ Nat.stirlingSecond (2 * m) m
  apply (ZMod.natCast_eq_zero_iff _ _).1
  simpa only [stirlingSeries, coeff_mk, two_mul] using hz

end A007820Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a007820.main := by
  change ∀ n : ℕ, (2 * n + 1) ^ 2 ∣ Nat.stirlingSecond (2 * (2 * n + 1)) (2 * n + 1)
  exact A007820Proof.divisibility

end
