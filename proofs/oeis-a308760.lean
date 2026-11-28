import OMAStatements.S_oeis_a308760
import Mathlib

namespace OMA.S_oeis_a308760

open PowerSeries

private theorem acc_add (d : ℕ) (hd : 0 < d) (f : ℕ → ℤ) (n : ℕ) :
    accumulate d f (n+d) = f (n+d) + accumulate d f n := by
  unfold accumulate
  rw [Nat.add_div_right n hd, Finset.sum_range_succ']
  simp only [Nat.mul_zero, Nat.sub_zero, Nat.mul_succ, Nat.add_sub_add_right]
  rw [add_comm]

private theorem weight_add (d : ℕ) (hd : 0 < d) (f : ℕ → ℤ) (n : ℕ) :
    weighted d f (n+d) = weighted d f n + accumulate d f n := by
  unfold weighted accumulate
  rw [Nat.add_div_right n hd, Finset.sum_range_succ']
  simp only [Nat.mul_zero, Nat.sub_zero, Nat.mul_succ, Nat.add_sub_add_right,
    Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, add_zero]
  simp_rw [add_mul, one_mul]
  rw [Finset.sum_add_distrib]

theorem acc_series (d : ℕ) (hd : 0 < d) (f : ℕ → ℤ) :
    mk (accumulate d f) * (1-X^d) = mk f := by
  rw [mul_sub, mul_one]
  ext n
  simp only [map_sub, coeff_mk, coeff_mul_X_pow']
  by_cases hn : d ≤ n
  · simp [hn]
    simpa [Nat.sub_add_cancel hn, add_comm] using
      sub_eq_iff_eq_add.mpr (acc_add d hd f (n-d))
  · simp [hn, accumulate, Nat.div_eq_of_lt (by omega : n < d)]

theorem weighted_series (d : ℕ) (hd : 0 < d) (f : ℕ → ℤ) :
    mk (weighted d f) * (1-X^d)^2 = X^d * mk f := by
  have step : mk (weighted d f) * (1-X^d) = mk (accumulate d f) * X^d := by
    rw [mul_sub, mul_one]
    ext n
    simp only [map_sub, coeff_mk, coeff_mul_X_pow']
    by_cases hn : d ≤ n
    · simp [hn]
      have h := weight_add d hd f (n-d)
      rw [Nat.sub_add_cancel hn] at h
      omega
    · simp [hn, weighted, Nat.div_eq_of_lt (by omega : n < d)]
  rw [pow_two, ← mul_assoc, step, mul_right_comm, acc_series d hd, mul_comm]



private theorem countOnes : mk ones * (1-X) = 1 := by
  rw [mul_sub, mul_one, ← pow_one (X : ℤ⟦X⟧)]
  ext n
  cases n <;> simp [ones]

private theorem countDigit : mk digitValue * (1-X)^2 = X := by
  have step : mk digitValue * (1-X) = mk ones * X := by
    rw [mul_sub, mul_one, ← pow_one (X : ℤ⟦X⟧)]
    ext n
    cases n <;> simp [digitValue, ones]
  calc
    _ = (mk digitValue * (1-X)) * (1-X) := by ring
    _ = (mk ones * (1-X)) * X := by rw [step]; ring
    _ = _ := by rw [countOnes,one_mul]

private theorem accumCount (d : ℕ) (hd : 0<d) {f : ℕ → ℤ} {den num : ℤ⟦X⟧}
    (h : mk f * den = num) : mk (accumulate d f) * ((1-X^d)*den) = num := by
  rw [← mul_assoc, acc_series d hd f, h]

private theorem weightedCount (d : ℕ) (hd : 0<d) {f : ℕ → ℤ} {den num : ℤ⟦X⟧}
    (h : mk f * den = num) : mk (weighted d f) * ((1-X^d)^2*den) = X^d*num := by
  rw [← mul_assoc, weighted_series d hd f, mul_assoc, h]

private theorem commonDen {t den num D : ℤ⟦X⟧} (h : t*den=num) (q : ℤ⟦X⟧)
    (hq : D = den*q) : D*t = num*q := by rw [hq, ← h]; ring

theorem largestSeries :
    ((1-X)^5*(1+X)^3*(1+X^2)^2*(1+X+X^2)^2) * mk a =
      X^4*(1+2*X+4*X^2+5*X^3+6*X^4+4*X^5+3*X^6) := by
  let D : ℤ⟦X⟧ := (1-X)^5*(1+X)^3*(1+X^2)^2*(1+X+X^2)^2
  change D * mk a = _
  have shifted : mk a = (mk partCount + mk pWeight + mk qWeight + mk rWeight + mk sWeight) * X^4 := by
    ext n
    simp only [coeff_mk, coeff_mul_X_pow', map_add, a]
  have pairCount := accumCount 2 (by decide) countOnes
  have tripleCount := accumCount 3 (by decide) pairCount
  have b := commonDen (D := D) (accumCount 4 (by decide) tripleCount)
    ((1-X^4)*(1+X+X^2)) (by dsimp [D]; ring)
  have p := commonDen (D := D) (weightedCount 4 (by decide) tripleCount)
    (1+X+X^2) (by dsimp [D]; ring)
  have q := commonDen (D := D) (accumCount 4 (by decide) (weightedCount 3 (by decide) pairCount))
    (1+X+X^2+X^3) (by dsimp [D]; ring)
  have r := commonDen (D := D) (accumCount 4 (by decide) (accumCount 3 (by decide)
    (weightedCount 2 (by decide) countOnes))) ((1+X^2)*(1+X+X^2)) (by dsimp [D]; ring)
  have s := commonDen (D := D) (accumCount 4 (by decide) (accumCount 3 (by decide)
    (accumCount 2 (by decide) countDigit))) ((1+X+X^2+X^3)*(1+X+X^2)) (by dsimp [D]; ring)
  rw [shifted, ← mul_assoc]
  simp only [mul_add, partCount, pWeight, qWeight, rWeight, sWeight, triples, pairs]
  rw [b,p,q,r,s]
  ring


open PowerSeries in
theorem recurrence_of_series
    (h : ((1-X)^5*(1+X)^3*(1+X^2)^2*(1+X+X^2)^2) * mk a =
        X^4*(1+2*X+4*X^2+5*X^3+6*X^4+4*X^5+3*X^6)) :
    ∀ n : ℕ, 15 < n →
      a n = a (n-2) + 2*a (n-3) + 2*a (n-4) - 2*a (n-5) - 3*a (n-6) - 4*a (n-7)
        + 4*a (n-9) + 3*a (n-10) + 2*a (n-11) - 2*a (n-12) - 2*a (n-13)
        - a (n-14) + a (n-16) := by
  intro n hn
  let A := mk a
  change _ * A = _ at h
  rw [show ((1-X)^5*(1+X)^3*(1+X^2)^2*(1+X+X^2)^2) * A =
      A - A*X^2 - C 2*(A*X^3) - C 2*(A*X^4) + C 2*(A*X^5) + C 3*(A*X^6)
        + C 4*(A*X^7) - C 4*(A*X^9) - C 3*(A*X^10) - C 2*(A*X^11)
        + C 2*(A*X^12) + C 2*(A*X^13) + A*X^14 - A*X^16 by simp only [map_ofNat]; ring,
      show (X : PowerSeries ℤ)^4*(1+2*X+4*X^2+5*X^3+6*X^4+4*X^5+3*X^6) =
        X^4 + C 2*X^5 + C 4*X^6 + C 5*X^7 + C 6*X^8 + C 4*X^9 + C 3*X^10 by
          simp only [map_ofNat]; ring] at h
  have hc := congrArg (coeff (R := ℤ) n) h
  simp (disch := omega) only [map_add, map_sub, coeff_C_mul, coeff_X_pow, coeff_mul_X_pow',
    A, coeff_mk, coeff_C, if_pos, if_neg, add_zero] at hc
  linarith

end OMA.S_oeis_a308760

open OMA.S_oeis_a308760 in
theorem OMA.solution : type_of% @OMA.S_oeis_a308760.main :=
  ⟨largestSeries, recurrence_of_series largestSeries⟩
