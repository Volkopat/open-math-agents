import OMAStatements.S_oeis_a082758

/-! Proof. Both sides satisfy the same order-2 P-recurrence
`n(2n-1)(4n-5) x(n) = (4n-3)(20n²-30n+7) x(n-1) - 9(n-1)(2n-3)(4n-1) x(n-2)`
and agree at `n = 0, 1, 2`.
* Left side: by symmetry `∑ T(n,k)² = T(2n,2n)`, the central coefficient of `(1+x+x²)^(2n)`; the
  coefficients of `(1+x+x²)^m` satisfy a Pascal-type rule and `P·(P^m)' = m·P'·P^m`.
* Right side: the coefficients of `F^m` satisfy `(1-x)²F^(m+1) = (1+x+x³+x⁴)F^m` and
  `(1-x)(1+x+x³+x⁴)(F^m)' = m(3+x+3x²+3x³-2x⁴)F^m`.
Each recurrence is a fixed polynomial combination of these relations. -/

namespace OMA.S_oeis_a082758

section U
open Polynomial Finset

noncomputable def P : ℤ[X] := 1 + X + X^2
noncomputable def T (m k : ℕ) : ℤ := (P^m).coeff k

lemma pas (m k : ℕ) : T (m+1) (k+2) = T m (k+2) + T m (k+1) + T m k := by
  unfold T
  rw [pow_succ', P]
  simp only [add_mul, one_mul, coeff_add, coeff_X_mul, coeff_X_pow_mul]

lemma Rr (m k : ℕ) : ((k:ℤ)+3) * T m (k+3) + ((k:ℤ)+2) * T m (k+2) + ((k:ℤ)+1) * T m (k+1)
    = (m:ℤ) * (T m (k+2) + 2 * T m (k+1)) := by
  have hd : P * derivative (P^m) = (m:ℤ[X]) * (derivative P * P^m) := by
    rcases m with _ | m
    · simp
    · rw [derivative_pow, Nat.add_sub_cancel, ← C_eq_natCast]; ring
  have hP : derivative P = 1 + 2 * X := by
    simp [P]
  have h := congrArg (fun q => q.coeff (k+2)) hd
  rw [hP, ← C_eq_natCast, coeff_C_mul] at h
  unfold T
  have e1 : ∀ q : ℤ[X], (P * q).coeff (k+2) = q.coeff (k+2) + q.coeff (k+1) + q.coeff k := by
    intro q
    rw [P]; simp only [add_mul, one_mul, coeff_add, coeff_X_mul, coeff_X_pow_mul]
  have e2 : ∀ q : ℤ[X], ((1 + 2*X) * q).coeff (k+2) = q.coeff (k+2) + 2 * q.coeff (k+1) := by
    intro q
    simp only [add_mul, one_mul, coeff_add, mul_assoc]
    rw [show (2:ℤ[X]) = C 2 by simp, coeff_C_mul, coeff_X_mul]
  rw [e1, e2] at h
  simp only [coeff_derivative] at h
  push_cast at h
  linear_combination h

lemma natDeg_pow (n : ℕ) : (P^n).natDegree ≤ 2*n := by
  have : P.natDegree ≤ 2 := by unfold P; compute_degree
  calc (P^n).natDegree ≤ n * P.natDegree := natDegree_pow_le
    _ ≤ n * 2 := Nat.mul_le_mul_left n this
    _ = 2 * n := by ring

lemma reflP (n : ℕ) : reflect (2*n) (P^n) = P^n := by
  have hr : reflect 2 P = P := by
    ext i
    rw [coeff_reflect]
    rcases i with _ | _ | _ | i
    · rw [revAt_le (by norm_num)]; simp [P, coeff_X, coeff_one, coeff_X_pow]
    · rw [revAt_le (by norm_num)]
    · rw [revAt_le (by norm_num)]; simp [P, coeff_X, coeff_one, coeff_X_pow]
    · rw [revAt_eq_self_of_lt (by omega)]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, show 2*(n+1) = 2*n + 2 by ring, reflect_mul _ _ (natDeg_pow n) (by unfold P; compute_degree),
      ih, hr]

lemma sym (n k : ℕ) (hk : k ≤ 2*n) : T n k = T n (2*n - k) := by
  unfold T
  conv_lhs => rw [← reflP n]
  rw [coeff_reflect, revAt_le hk]

lemma aU (n : ℕ) : a n = T (2*n) (2*n) := by
  unfold T
  rw [show 2*n = n + n by ring, pow_add, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => (P^n).coeff i * (P^n).coeff j) (n+n)]
  unfold a
  rw [show 2*n = n + n by ring]
  refine sum_congr rfl (fun k hk => ?_)
  simp at hk
  have := sym n k (by omega)
  unfold T at this
  rw [show n + n = 2 * n by ring, ← this, sq]; rfl

lemma abase : a 0 = 1 ∧ a 1 = 3 ∧ a 2 = 19 := by
  have h2 : (1 + X + X^2 : ℤ[X])^2 = C 1 * X^0 + C 2 * X^1 + C 3 * X^2 + C 2 * X^3 + C 1 * X^4 := by
    simp only [map_one, map_ofNat]; ring
  refine ⟨by simp [a], ?_, ?_⟩
  · simp [a, Finset.sum_range_succ, coeff_X, coeff_one]
  · unfold a; rw [h2]
    simp [Finset.sum_range_succ, coeff_X, coeff_one, coeff_X_pow]

end U

lemma recU (N : ℕ) : 2 * (((N:ℤ)+2) * (2*((N:ℤ)+2)-1) * (4*((N:ℤ)+2)-5) * T (2*(N+2)) (2*(N+2))
    - (4*((N:ℤ)+2)-3) * (20*((N:ℤ)+2)^2-30*((N:ℤ)+2)+7) * T (2*(N+1)) (2*(N+1))
    + 9*((N:ℤ)+2-1)*(2*((N:ℤ)+2)-3)*(4*((N:ℤ)+2)-1) * T (2*N) (2*N)) = 0 := by
  have h0 := Rr (2*N+0) (2*N+0)
  have h1 := Rr (2*N+0) (2*N+1)
  have h2 := Rr (2*N+1) (2*N+0)
  have h3 := Rr (2*N+1) (2*N+1)
  have h4 := Rr (2*N+2) (2*N+0)
  have h5 := Rr (2*N+2) (2*N+1)
  have h6 := Rr (2*N+3) (2*N+1)
  have h7 := pas (2*N+0) (2*N+0)
  have h8 := pas (2*N+0) (2*N+1)
  have h9 := pas (2*N+0) (2*N+2)
  have h10 := pas (2*N+1) (2*N+1)
  have h11 := pas (2*N+1) (2*N+2)
  have h12 := pas (2*N+2) (2*N+1)
  have h13 := pas (2*N+2) (2*N+2)
  have h14 := pas (2*N+3) (2*N+2)
  push_cast at *
  ring_nf at *
  linear_combination (48*(N:ℤ)^2 + 132*(N:ℤ) + 84) * h0 + (24*(N:ℤ)^2 + 66*(N:ℤ) + 42) * h1 + (-32*(N:ℤ)^2 - 92*(N:ℤ) - 63) * h2 + (-64*(N:ℤ)^2 - 172*(N:ℤ) - 105) * h3 + (-8*(N:ℤ)^2 - 22*(N:ℤ) - 12) * h4 + (56*(N:ℤ)^2 + 142*(N:ℤ) + 81) * h5 + (-8*(N:ℤ)^2 - 18*(N:ℤ) - 9) * h6 + (-144*(N:ℤ)^3 - 468*(N:ℤ)^2 - 450*(N:ℤ) - 126) * h7 + (48*(N:ℤ)^3 + 252*(N:ℤ)^2 + 414*(N:ℤ) + 210) * h8 + (48*(N:ℤ)^3 + 228*(N:ℤ)^2 + 348*(N:ℤ) + 168) * h9 + (64*(N:ℤ)^3 + 216*(N:ℤ)^2 + 218*(N:ℤ) + 63) * h10 + (-80*(N:ℤ)^3 - 372*(N:ℤ)^2 - 550*(N:ℤ) - 252) * h11 + (16*(N:ℤ)^3 + 68*(N:ℤ)^2 + 90*(N:ℤ) + 36) * h12 + (32*(N:ℤ)^3 + 136*(N:ℤ)^2 + 180*(N:ℤ) + 72) * h13 + (16*(N:ℤ)^3 + 68*(N:ℤ)^2 + 90*(N:ℤ) + 36) * h14

section D
open PowerSeries

noncomputable def Cf (m k : ℕ) : ℤ := coeff k (F ^ m)

lemma hI : (1 - X : ℤ⟦X⟧) ^ 2 * invOfUnit ((1 - X) ^ 2) 1 = 1 :=
  mul_invOfUnit _ _ (by simp)

lemma hQ (m : ℕ) : (1 - X : ℤ⟦X⟧) ^ 2 * F ^ (m+1) = (1 + X + X ^ 3 + X ^ 4) * F ^ m := by
  rw [pow_succ]; unfold F
  linear_combination ((1 + X + X ^ 3 + X ^ 4) * ((1 + X + X ^ 3 + X ^ 4) * invOfUnit ((1 - X) ^ 2) 1) ^ m) * hI

lemma hdI : (1 - X : ℤ⟦X⟧) * d⁄dX ℤ (invOfUnit ((1 - X) ^ 2) 1) = 2 * invOfUnit ((1 - X) ^ 2) 1 := by
  have h := congrArg (d⁄dX ℤ) hI
  simp only [Derivation.leibniz, Derivation.leibniz_pow, map_sub, derivative_X, Derivation.map_one_eq_zero,
    smul_eq_mul, nsmul_eq_mul] at h
  push_cast at h
  linear_combination (-(1 - X) * d⁄dX ℤ (invOfUnit ((1 - X : ℤ⟦X⟧) ^ 2) 1)
    + 2 * invOfUnit ((1 - X : ℤ⟦X⟧) ^ 2) 1) * hI + ((1 - X) * invOfUnit ((1 - X : ℤ⟦X⟧) ^ 2) 1) * h

lemma hF' : (1 - X : ℤ⟦X⟧) * (1 + X + X ^ 3 + X ^ 4) * d⁄dX ℤ F =
    ((1 + 3 * X ^ 2 + 4 * X ^ 3) * (1 - X) + 2 * (1 + X + X ^ 3 + X ^ 4)) * F := by
  unfold F
  set I := invOfUnit ((1 - X : ℤ⟦X⟧) ^ 2) 1
  simp only [Derivation.leibniz, Derivation.leibniz_pow, map_add, derivative_X, Derivation.map_one_eq_zero,
    smul_eq_mul, nsmul_eq_mul]
  push_cast
  linear_combination ((1 + X + X ^ 3 + X ^ 4) ^ 2) * hdI

lemma hD (m : ℕ) : (1 - X ^ 2 + X ^ 3 - X ^ 5 : ℤ⟦X⟧) * d⁄dX ℤ (F ^ m) =
    (m : ℤ⟦X⟧) * ((3 + X + 3 * X ^ 2 + 3 * X ^ 3 - 2 * X ^ 4) * F ^ m) := by
  rcases m with _ | m
  · simp
  · rw [Derivation.leibniz_pow]
    simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
    push_cast
    linear_combination ((m + 1 : ℤ⟦X⟧) * F ^ m) * hF'

lemma cX (G : ℤ⟦X⟧) (j e : ℕ) : coeff (e + j) (X ^ j * G) = coeff e G := by
  rw [coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel]

lemma cQ (m k : ℕ) : Cf (m+1) (k+4) - 2 * Cf (m+1) (k+3) + Cf (m+1) (k+2) =
    Cf m (k+4) + Cf m (k+3) + Cf m (k+1) + Cf m k := by
  have h := congrArg (coeff (k+4)) (hQ m)
  have e1 : (1 - X : ℤ⟦X⟧) ^ 2 * F ^ (m+1) = F ^ (m+1) - X ^ 1 * F ^ (m+1) - X ^ 1 * F ^ (m+1) + X ^ 2 * F ^ (m+1) := by ring
  have e2 : (1 + X + X ^ 3 + X ^ 4 : ℤ⟦X⟧) * F ^ m = F ^ m + X ^ 1 * F ^ m + X ^ 3 * F ^ m + X ^ 4 * F ^ m := by ring
  rw [e1, e2] at h
  simp only [map_add, map_sub] at h
  have a1 : coeff (k+4) (X^1 * F^(m+1)) = coeff (k+3) (F^(m+1)) := cX _ 1 (k+3)
  have a2 : coeff (k+4) (X^2 * F^(m+1)) = coeff (k+2) (F^(m+1)) := cX _ 2 (k+2)
  have a3 : coeff (k+4) (X^1 * F^m) = coeff (k+3) (F^m) := cX _ 1 (k+3)
  have a4 : coeff (k+4) (X^3 * F^m) = coeff (k+1) (F^m) := cX _ 3 (k+1)
  have a5 : coeff (k+4) (X^4 * F^m) = coeff k (F^m) := cX _ 4 k
  rw [a1, a2, a3, a4, a5] at h
  unfold Cf
  linear_combination h

lemma cD (m k : ℕ) : ((k:ℤ)+6) * Cf m (k+6) - ((k:ℤ)+4) * Cf m (k+4) + ((k:ℤ)+3) * Cf m (k+3)
    - ((k:ℤ)+1) * Cf m (k+1) = (m:ℤ) * (3 * Cf m (k+5) + Cf m (k+4) + 3 * Cf m (k+3) + 3 * Cf m (k+2)
      - 2 * Cf m (k+1)) := by
  have h := congrArg (coeff (k+5)) (hD m)
  set G := d⁄dX ℤ (F ^ m)
  set H := F ^ m
  have e1 : (1 - X ^ 2 + X ^ 3 - X ^ 5 : ℤ⟦X⟧) * G = X ^ 0 * G - X ^ 2 * G + X ^ 3 * G - X ^ 5 * G := by ring
  have e2 : (m : ℤ⟦X⟧) * ((3 + X + 3 * X ^ 2 + 3 * X ^ 3 - 2 * X ^ 4) * H) =
      C (3 * m : ℤ) * (X ^ 0 * H) + C (m : ℤ) * (X ^ 1 * H) + C (3 * m : ℤ) * (X ^ 2 * H)
        + C (3 * m : ℤ) * (X ^ 3 * H) - C (2 * m : ℤ) * (X ^ 4 * H) := by
    simp only [map_mul, map_natCast, map_ofNat]; ring
  rw [e1, e2] at h
  simp only [map_add, map_sub, coeff_C_mul] at h
  have b0 : coeff (k+5) (X^0 * G) = coeff (k+5) G := cX _ 0 (k+5)
  have b2 : coeff (k+5) (X^2 * G) = coeff (k+3) G := cX _ 2 (k+3)
  have b3 : coeff (k+5) (X^3 * G) = coeff (k+2) G := cX _ 3 (k+2)
  have b5 : coeff (k+5) (X^5 * G) = coeff k G := cX _ 5 k
  have d0 : coeff (k+5) (X^0 * H) = coeff (k+5) H := cX _ 0 (k+5)
  have d1 : coeff (k+5) (X^1 * H) = coeff (k+4) H := cX _ 1 (k+4)
  have d2 : coeff (k+5) (X^2 * H) = coeff (k+3) H := cX _ 2 (k+3)
  have d3 : coeff (k+5) (X^3 * H) = coeff (k+2) H := cX _ 3 (k+2)
  have d4 : coeff (k+5) (X^4 * H) = coeff (k+1) H := cX _ 4 (k+1)
  rw [b0, b2, b3, b5, d0, d1, d2, d3, d4] at h
  simp only [G, coeff_derivative] at h
  unfold Cf
  push_cast at h
  linear_combination h

lemma low (m : ℕ) : Cf (m+1) 0 = Cf m 0 ∧ Cf (m+1) 1 - 2 * Cf (m+1) 0 = Cf m 1 + Cf m 0 ∧
    Cf (m+1) 2 - 2 * Cf (m+1) 1 + Cf (m+1) 0 = Cf m 2 + Cf m 1 := by
  have e1 : (1 - X : ℤ⟦X⟧) ^ 2 * F ^ (m+1) = F ^ (m+1) - X ^ 1 * F ^ (m+1) - X ^ 1 * F ^ (m+1) + X ^ 2 * F ^ (m+1) := by ring
  have e2 : (1 + X + X ^ 3 + X ^ 4 : ℤ⟦X⟧) * F ^ m = F ^ m + X ^ 1 * F ^ m + X ^ 3 * F ^ m + X ^ 4 * F ^ m := by ring
  have h := hQ m
  rw [e1, e2] at h
  have h0 := congrArg (coeff 0) h
  have h1 := congrArg (coeff 1) h
  have h2 := congrArg (coeff 2) h
  simp only [map_add, map_sub, coeff_X_pow_mul'] at h0 h1 h2
  norm_num [-map_pow, -coeff_zero_eq_constantCoeff] at h0 h1 h2
  unfold Cf
  refine ⟨by linear_combination h0, by linear_combination h1, by linear_combination h2⟩

lemma C0 (k : ℕ) : Cf 0 k = if k = 0 then 1 else 0 := by simp [Cf, coeff_one]

lemma dbase : Cf 0 0 = 1 ∧ Cf 1 1 = 3 ∧ Cf 2 2 = 19 := by
  have l0 := low 0
  have l1 := low 1
  simp only [C0] at l0
  norm_num at l0
  obtain ⟨a0, a1, a2⟩ := l0
  obtain ⟨b0, b1, b2⟩ := l1
  norm_num at b0 b1 b2
  refine ⟨by simp [C0], by linarith, by linarith⟩

end D

lemma recD (N : ℕ) : 8 * (((N:ℤ)+3) * (2*((N:ℤ)+3)-1) * (4*((N:ℤ)+3)-5) * Cf (N+3) (N+3)
    - (4*((N:ℤ)+3)-3) * (20*((N:ℤ)+3)^2-30*((N:ℤ)+3)+7) * Cf (N+2) (N+2)
    + 9*((N:ℤ)+3-1)*(2*((N:ℤ)+3)-3)*(4*((N:ℤ)+3)-1) * Cf (N+1) (N+1)) = 0 := by
  have h0 := cD (N+0) (N+0)
  have h1 := cD (N+0) (N+3)
  have h2 := cD (N+1) (N+0)
  have h3 := cD (N+1) (N+1)
  have h4 := cD (N+1) (N+2)
  have h5 := cD (N+1) (N+3)
  have h6 := cD (N+2) (N+0)
  have h7 := cD (N+2) (N+1)
  have h8 := cD (N+2) (N+2)
  have h9 := cD (N+2) (N+3)
  have h10 := cD (N+3) (N+2)
  have h11 := cD (N+3) (N+3)
  have h12 := cQ (N+0) (N+1)
  have h13 := cQ (N+0) (N+2)
  have h14 := cQ (N+0) (N+3)
  have h15 := cQ (N+0) (N+4)
  have h16 := cQ (N+0) (N+5)
  have h17 := cQ (N+1) (N+1)
  have h18 := cQ (N+1) (N+2)
  have h19 := cQ (N+1) (N+3)
  have h20 := cQ (N+1) (N+4)
  have h21 := cQ (N+1) (N+5)
  have h22 := cQ (N+2) (N+1)
  have h23 := cQ (N+2) (N+2)
  have h24 := cQ (N+2) (N+3)
  have h25 := cQ (N+2) (N+4)
  have h26 := cQ (N+2) (N+5)
  push_cast at *
  ring_nf at *
  linear_combination (12*(N:ℤ)^2 + 57*(N:ℤ) + 66) * h0 + (12*(N:ℤ)^2 + 57*(N:ℤ) + 66) * h1 + (200*(N:ℤ)^2 + 926*(N:ℤ) + 1035) * h2 + (-16*(N:ℤ)^2 - 108*(N:ℤ) - 176) * h3 + (84*(N:ℤ)^2 + 399*(N:ℤ) + 462) * h4 + (60*(N:ℤ)^2 + 293*(N:ℤ) + 353) * h5 + (92*(N:ℤ)^2 + 405*(N:ℤ) + 427) * h6 + (-192*(N:ℤ)^2 - 912*(N:ℤ) - 1056) * h7 + (136*(N:ℤ)^2 + 670*(N:ℤ) + 825) * h8 + (-92*(N:ℤ)^2 - 445*(N:ℤ) - 524) * h9 + (-28*(N:ℤ)^2 - 133*(N:ℤ) - 147) * h10 + (20*(N:ℤ)^2 + 95*(N:ℤ) + 105) * h11 + (12*(N:ℤ)^3 + 45*(N:ℤ)^2 + 9*(N:ℤ) - 66) * h12 + (-48*(N:ℤ)^3 - 216*(N:ℤ)^2 - 207*(N:ℤ) + 66) * h13 + (24*(N:ℤ)^3 + 138*(N:ℤ)^2 + 246*(N:ℤ) + 132) * h14 + (-48*(N:ℤ)^3 - 336*(N:ℤ)^2 - 777*(N:ℤ) - 594) * h15 + (12*(N:ℤ)^3 + 165*(N:ℤ)^2 + 579*(N:ℤ) + 594) * h16 + (-376*(N:ℤ)^3 - 2474*(N:ℤ)^2 - 5311*(N:ℤ) - 3717) * h17 + (-240*(N:ℤ)^3 - 1012*(N:ℤ)^2 - 748*(N:ℤ) + 612) * h18 + (-16*(N:ℤ)^3 - 108*(N:ℤ)^2 - 398*(N:ℤ) - 612) * h19 + (-240*(N:ℤ)^3 - 1652*(N:ℤ)^2 - 3788*(N:ℤ) - 2916) * h20 + (72*(N:ℤ)^3 + 998*(N:ℤ)^2 + 3569*(N:ℤ) + 3771) * h21 + (92*(N:ℤ)^3 + 681*(N:ℤ)^2 + 1642*(N:ℤ) + 1281) * h22 + (80*(N:ℤ)^3 + 576*(N:ℤ)^2 + 1351*(N:ℤ) + 1029) * h23 + (72*(N:ℤ)^3 + 558*(N:ℤ)^2 + 1404*(N:ℤ) + 1134) * h24 + (48*(N:ℤ)^3 + 272*(N:ℤ)^2 + 461*(N:ℤ) + 231) * h25 + (-20*(N:ℤ)^3 - 275*(N:ℤ)^2 - 960*(N:ℤ) - 945) * h26

lemma ud : ∀ n : ℕ, T (2*n) (2*n) = Cf n n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [← aU, dbase.1]; exact abase.1
    | 1 => rw [← aU, dbase.2.1]; exact abase.2.1
    | 2 => rw [← aU, dbase.2.2]; exact abase.2.2
    | M + 3 =>
      have hu := recU (M+1)
      have hd := recD M
      have i1 := ih (M+2) (by omega)
      have i2 := ih (M+1) (by omega)
      simp only [show M + 1 + 2 = M + 3 by ring, show M + 1 + 1 = M + 2 by ring] at hu
      push_cast at hu
      have hlead : ((M:ℤ)+3) * (2*((M:ℤ)+3)-1) * (4*((M:ℤ)+3)-5) ≠ 0 := by
        have : (0:ℤ) < ((M:ℤ)+3) * (2*((M:ℤ)+3)-1) * (4*((M:ℤ)+3)-5) := by
          apply mul_pos; apply mul_pos <;> linarith
          linarith
        exact this.ne'
      have key : (8:ℤ) * (((M:ℤ)+3) * (2*((M:ℤ)+3)-1) * (4*((M:ℤ)+3)-5) * (T (2*(M+3)) (2*(M+3)) - Cf (M+3) (M+3))) = 0 := by
        rw [i1, i2] at hu
        linear_combination 4 * hu - hd
      have := (mul_eq_zero.mp ((mul_eq_zero.mp key).resolve_left (by norm_num))).resolve_left hlead
      linarith

theorem solution_main : ∀ n : ℕ, a n = PowerSeries.coeff n (F ^ n) := by
  intro n
  rw [aU, ud]; rfl

end OMA.S_oeis_a082758

theorem OMA.solution : type_of% @OMA.S_oeis_a082758.main := OMA.S_oeis_a082758.solution_main
