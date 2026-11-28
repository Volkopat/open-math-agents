import OMAStatements.S_mo_140378
import Mathlib

namespace OMA.Helpers_mo_140378

open OMA.S_mo_140378 PowerSeries

noncomputable section

/-- the Euler operator `X d/dX` -/
def θ (F : PS) : PS := PowerSeries.mk fun n => (n : LP) * coeff n F

lemma coeff_θ (F : PS) (n : ℕ) : coeff n (θ F) = (n : LP) * coeff n F := by
  simp [θ]

lemma θ_mul (F G : PS) : θ (F * G) = θ F * G + F * θ G := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_θ, map_add, coeff_mul, coeff_mul, coeff_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [coeff_θ, coeff_θ, ← hp]
  push_cast; ring

lemma θ_sub (F G : PS) : θ (F - G) = θ F - θ G := by
  refine PowerSeries.ext fun n => ?_
  rw [map_sub, coeff_θ, coeff_θ, coeff_θ, map_sub, mul_sub]

lemma θ_one : θ 1 = 0 := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_θ, coeff_one, map_zero]; split_ifs with h <;> simp [h]

lemma θ_mono (a : LP) (e : ℕ) : θ (C a * X ^ e) = (e : LP) • (C a * X ^ e) := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_θ, coeff_smul, coeff_C_mul_X_pow, smul_eq_mul]
  split_ifs with h
  · subst h; rfl
  · simp

lemma base_mul (s : ℤ) : (PowerSeries.mk (fun k : ℕ => LaurentPolynomial.T (s * k)) : PS) *
    (1 - C (LaurentPolynomial.T s) * X) = 1 := by
  refine PowerSeries.ext fun n => ?_
  rw [mul_sub, mul_one, map_sub, show (PowerSeries.mk (fun k : ℕ => LaurentPolynomial.T (s * k)) : PS) *
    (C (LaurentPolynomial.T s) * X) = C (LaurentPolynomial.T s) *
      (PowerSeries.mk (fun k : ℕ => LaurentPolynomial.T (s * k)) * X) by ring, coeff_C_mul, coeff_one]
  rcases n with _ | k
  · simp [LaurentPolynomial.T_zero]
  · rw [coeff_succ_mul_X, coeff_mk, coeff_mk, ← LaurentPolynomial.T_add]
    simp only [Nat.succ_ne_zero, if_false]
    push_cast
    rw [show s * ((k : ℤ) + 1) = s + s * k by ring, sub_self]

lemma geom_mul (d : ℕ) (s : ℤ) : geom d s * (1 - C (LaurentPolynomial.T s) * X ^ (d + 1)) = 1 := by
  have := congrArg (expand (d + 1) (by omega)) (base_mul s)
  simpa [geom, map_mul, map_sub, expand_C, expand_X] using this

lemma θ_geom (d : ℕ) (s : ℤ) : θ (geom d s) =
    geom d s * (C ((d + 1 : ℕ) : LP) * (C (LaurentPolynomial.T s) * X ^ (d + 1) * geom d s)) := by
  set u : PS := C (LaurentPolynomial.T s) * X ^ (d + 1) with hu
  have h1 : geom d s * (1 - u) = 1 := geom_mul d s
  have h2 : θ (geom d s) * (1 - u) = geom d s * (C ((d + 1 : ℕ) : LP) * u) := by
    have := congrArg θ h1
    rw [θ_mul, θ_one, θ_sub, θ_one, hu, θ_mono, smul_eq_C_mul] at this
    rw [hu]; linear_combination this
  calc θ (geom d s) = θ (geom d s) * ((1 - u) * geom d s) := by
        rw [mul_comm (1 - u), h1, mul_one]
    _ = _ := by rw [← mul_assoc, h2]; ring

def ℓ (d : ℕ) (s : ℤ) : PS :=
  C ((d + 1 : ℕ) : LP) * (C (LaurentPolynomial.T s) * X ^ (d + 1) * geom d s)

def L (m : ℕ) : PS := ∑ d ∈ Finset.range m, (ℓ d 1 + ℓ d (-1))

lemma θ_P (m : ℕ) : θ (partitionProduct m) = partitionProduct m * L m := by
  induction m with
  | zero => simp [partitionProduct, L, θ_one]
  | succ m ih =>
    rw [partitionProduct, Finset.prod_range_succ, ← partitionProduct, θ_mul, θ_mul, ih,
      θ_geom, θ_geom]
    simp only [L, Finset.sum_range_succ, ℓ]
    ring

lemma coeff_geom (d : ℕ) (s : ℤ) (j : ℕ) :
    coeff j (geom d s) = if (d + 1) ∣ j then LaurentPolynomial.T (s * (j / (d + 1) : ℕ)) else 0 := by
  rw [geom, coeff_expand, coeff_mk]

lemma coeff_ℓ (d : ℕ) (s : ℤ) (n : ℕ) :
    coeff n (ℓ d s) = if (d + 1) ∣ n ∧ 0 < n then
      ((d + 1 : ℕ) : LP) * LaurentPolynomial.T (s * (n / (d + 1) : ℕ)) else 0 := by
  rw [ℓ, show C ((d + 1 : ℕ) : LP) * (C (LaurentPolynomial.T s) * X ^ (d + 1) * geom d s) =
    C (((d + 1 : ℕ) : LP) * LaurentPolynomial.T s) * (X ^ (d + 1) * geom d s) by
      rw [map_mul]; ring, coeff_C_mul, coeff_X_pow_mul', coeff_geom]
  by_cases h : (d + 1) ∣ n ∧ 0 < n
  · obtain ⟨⟨q, rfl⟩, hpos⟩ := h
    have hq : 1 ≤ q := by
      rcases q with _ | q
      · simp at hpos
      · omega
    rw [if_pos (by nlinarith), if_pos (by
        rw [show (d + 1) * q - (d + 1) = (d + 1) * (q - 1) by
          rw [Nat.mul_sub, mul_one]]; exact Dvd.intro _ rfl),
      if_pos ⟨Dvd.intro _ rfl, hpos⟩,
      show (d + 1) * q - (d + 1) = (d + 1) * (q - 1) by rw [Nat.mul_sub, mul_one],
      Nat.mul_div_cancel_left _ (by omega), Nat.mul_div_cancel_left _ (by omega), mul_assoc,
      ← LaurentPolynomial.T_add]
    congr 3
    push_cast [Nat.cast_sub hq]
    ring
  · rw [if_neg h]
    split_ifs with h1 h2
    · exfalso; apply h
      refine ⟨?_, by omega⟩
      have := Nat.dvd_add h2 (dvd_refl (d + 1))
      rwa [Nat.sub_add_cancel h1] at this
    · simp
    · simp

lemma geom_eq (d : ℕ) (s : ℤ) :
    geom d s = 1 + X ^ (d + 1) * (C (LaurentPolynomial.T s) * geom d s) := by
  have h1 := geom_mul d s
  linear_combination h1

lemma trunc (m k j : ℕ) (hj : j ≤ m) :
    coeff j (partitionProduct (m + k)) = coeff j (partitionProduct m) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← ih, show m + (k + 1) = (m + k) + 1 by omega, partitionProduct, Finset.prod_range_succ,
      ← partitionProduct, geom_eq (m + k) 1, geom_eq (m + k) (-1)]
    rw [show partitionProduct (m + k) * ((1 + X ^ (m + k + 1) * (C (LaurentPolynomial.T 1) * geom (m + k) 1)) *
        (1 + X ^ (m + k + 1) * (C (LaurentPolynomial.T (-1)) * geom (m + k) (-1)))) =
        partitionProduct (m + k) + X ^ (m + k + 1) * (partitionProduct (m + k) *
          (C (LaurentPolynomial.T 1) * geom (m + k) 1 + C (LaurentPolynomial.T (-1)) * geom (m + k) (-1) +
            X ^ (m + k + 1) * (C (LaurentPolynomial.T 1) * geom (m + k) 1) *
              (C (LaurentPolynomial.T (-1)) * geom (m + k) (-1)))) by ring]
    rw [map_add, coeff_X_pow_mul', if_neg (by omega), add_zero]

lemma cz_natCast_mul (n : ℕ) (c : LP) (z : ℤ) : ((n : LP) * c).coeff z = n * c.coeff z := by
  rw [← nsmul_eq_mul, AddMonoidAlgebra.coeff_smul_apply, nsmul_eq_mul]

lemma cz_mul_T (c : LP) (k z : ℤ) : (c * LaurentPolynomial.T k).coeff z = c.coeff (z - k) := by
  rw [LaurentPolynomial.T, AddMonoidAlgebra.coeff_mul_single_apply, mul_one, sub_eq_add_neg]

lemma count_eq (m j : ℕ) (hj : j ≤ m) (z : ℤ) :
    (coeff j (partitionProduct m)).coeff z = count j z := by
  unfold count
  rw [show m = j + (m - j) by omega, trunc j (m - j) j le_rfl]

lemma term (m r : ℕ) (hr : r < m) (z : ℤ) :
    (coeff (m - (r + 1)) (partitionProduct m) * coeff (r + 1) (L m)).coeff z =
      ∑ d ∈ Finset.range m, if d + 1 ∣ r + 1 then ((d + 1 : ℕ) : ℤ) *
        (count (m - (r + 1)) (z - ((r + 1) / (d + 1) : ℕ)) +
          count (m - (r + 1)) (z + ((r + 1) / (d + 1) : ℕ))) else 0 := by
  rw [L, map_sum, Finset.mul_sum, AddMonoidAlgebra.coeff_sum, Finset.sum_apply']
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [map_add, coeff_ℓ, coeff_ℓ]
  by_cases h : d + 1 ∣ r + 1
  · rw [if_pos ⟨h, by omega⟩, if_pos ⟨h, by omega⟩, if_pos h, mul_add, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply, mul_left_comm, mul_left_comm (coeff (m - (r + 1)) (partitionProduct m)),
      cz_natCast_mul, cz_natCast_mul, cz_mul_T, cz_mul_T, count_eq m _ (by omega),
      count_eq m _ (by omega)]
    push_cast
    ring_nf
  · rw [if_neg (by tauto), if_neg (by tauto), if_neg h]
    simp

end

end OMA.Helpers_mo_140378

open OMA.Helpers_mo_140378 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_mo_140378.main := by
  refine ⟨by simp [OMA.S_mo_140378.count, OMA.S_mo_140378.partitionProduct], fun m z hm => ?_⟩
  have key : (m : OMA.S_mo_140378.LP) * coeff m (OMA.S_mo_140378.partitionProduct m) =
      coeff m (L m * OMA.S_mo_140378.partitionProduct m) := by
    rw [mul_comm (L m), ← θ_P, coeff_θ]
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i (L m) *
    coeff j (OMA.S_mo_140378.partitionProduct m)), Finset.sum_range_succ'] at key
  have h0 : coeff 0 (L m) = 0 := by
    rw [L, map_sum]; exact Finset.sum_eq_zero fun d _ => by rw [map_add, coeff_ℓ, coeff_ℓ]; simp
  rw [h0, zero_mul, add_zero] at key
  have := congrArg (fun c : OMA.S_mo_140378.LP => c.coeff z) key
  rw [cz_natCast_mul, count_eq m m le_rfl, AddMonoidAlgebra.coeff_sum, Finset.sum_apply'] at this
  rw [this, Finset.sum_comm]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Finset.mem_range] at hr
  rw [mul_comm, show m - (r + 1) = m - (r + 1) from rfl, term m r hr z]

