import OMAStatements.S_oeis_a156894

/-! Proof. `a(n) = [xⁿ] Gⁿ` with `G = (1+x)/(1-x)²` (convolve `(1+x)ⁿ` with `(1-x)^(-2n)`).
The coefficients of `G^m` satisfy `(1-x)² G^(m+1) = (1+x) G^m` and `(1-x²)(G^m)' = m(3+x)G^m`;
the order-2 recurrence (third clause) is a fixed polynomial combination of these. The order-4 and
order-3 recurrences are polynomial combinations of shifts of the order-2 one, divided by
`17n²-52n+39` and `17n²-86n+108`, which never vanish on integers. -/

namespace OMA.S_oeis_a156894
open PowerSeries

noncomputable def G : ℤ⟦X⟧ := (1 + X) * invOfUnit ((1 - X) ^ 2) 1
noncomputable def Cg (m k : ℕ) : ℤ := coeff k (G ^ m)

lemma hI : (1 - X : ℤ⟦X⟧) ^ 2 * invOfUnit ((1 - X) ^ 2) 1 = 1 :=
  mul_invOfUnit _ _ (by simp)

lemma hQ (m : ℕ) : (1 - X : ℤ⟦X⟧) ^ 2 * G ^ (m+1) = (1 + X) * G ^ m := by
  rw [pow_succ]; unfold G
  linear_combination ((1 + X) * ((1 + X) * invOfUnit ((1 - X : ℤ⟦X⟧) ^ 2) 1) ^ m) * hI

lemma hdI : (1 - X : ℤ⟦X⟧) * d⁄dX ℤ (invOfUnit ((1 - X) ^ 2) 1) = 2 * invOfUnit ((1 - X) ^ 2) 1 := by
  have h := congrArg (d⁄dX ℤ) hI
  simp only [Derivation.leibniz, Derivation.leibniz_pow, map_sub, derivative_X, Derivation.map_one_eq_zero,
    smul_eq_mul, nsmul_eq_mul] at h
  push_cast at h
  linear_combination (-(1 - X) * d⁄dX ℤ (invOfUnit ((1 - X : ℤ⟦X⟧) ^ 2) 1)
    + 2 * invOfUnit ((1 - X : ℤ⟦X⟧) ^ 2) 1) * hI + ((1 - X) * invOfUnit ((1 - X : ℤ⟦X⟧) ^ 2) 1) * h

lemma hG' : (1 - X : ℤ⟦X⟧) * (1 + X) * d⁄dX ℤ G = (3 + X) * G := by
  unfold G
  simp only [Derivation.leibniz, map_add, derivative_X, Derivation.map_one_eq_zero, smul_eq_mul]
  linear_combination ((1 + X : ℤ⟦X⟧) ^ 2) * hdI

lemma hD (m : ℕ) : (1 - X ^ 2 : ℤ⟦X⟧) * d⁄dX ℤ (G ^ m) = (m : ℤ⟦X⟧) * ((3 + X) * G ^ m) := by
  rcases m with _ | m
  · simp
  · rw [Derivation.leibniz_pow]
    simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
    push_cast
    linear_combination ((m + 1 : ℤ⟦X⟧) * G ^ m) * hG'

lemma cX (H : ℤ⟦X⟧) (j e : ℕ) : coeff (e + j) (X ^ j * H) = coeff e H := by
  rw [coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel]

lemma cQ (m k : ℕ) : Cg (m+1) (k+2) - 2 * Cg (m+1) (k+1) + Cg (m+1) k = Cg m (k+2) + Cg m (k+1) := by
  have h := congrArg (coeff (k+2)) (hQ m)
  have e1 : (1 - X : ℤ⟦X⟧) ^ 2 * G ^ (m+1) = G ^ (m+1) - X ^ 1 * G ^ (m+1) - X ^ 1 * G ^ (m+1) + X ^ 2 * G ^ (m+1) := by ring
  have e2 : (1 + X : ℤ⟦X⟧) * G ^ m = G ^ m + X ^ 1 * G ^ m := by ring
  rw [e1, e2] at h
  simp only [map_add, map_sub] at h
  have a1 : coeff (k+2) (X^1 * G^(m+1)) = coeff (k+1) (G^(m+1)) := cX _ 1 (k+1)
  have a2 : coeff (k+2) (X^2 * G^(m+1)) = coeff k (G^(m+1)) := cX _ 2 k
  have a3 : coeff (k+2) (X^1 * G^m) = coeff (k+1) (G^m) := cX _ 1 (k+1)
  rw [a1, a2, a3] at h
  unfold Cg
  linear_combination h

lemma cD (m k : ℕ) : ((k:ℤ)+3) * Cg m (k+3) - ((k:ℤ)+1) * Cg m (k+1) =
    (m:ℤ) * (3 * Cg m (k+2) + Cg m (k+1)) := by
  have h := congrArg (coeff (k+2)) (hD m)
  set H := G ^ m
  set D := d⁄dX ℤ H
  have e1 : (1 - X ^ 2 : ℤ⟦X⟧) * D = X ^ 0 * D - X ^ 2 * D := by ring
  have e2 : (m : ℤ⟦X⟧) * ((3 + X) * H) = C (3 * m : ℤ) * (X ^ 0 * H) + C (m : ℤ) * (X ^ 1 * H) := by
    simp only [map_mul, map_natCast, map_ofNat]; ring
  rw [e1, e2] at h
  simp only [map_add, map_sub, coeff_C_mul] at h
  have b0 : coeff (k+2) (X^0 * D) = coeff (k+2) D := cX _ 0 (k+2)
  have b2 : coeff (k+2) (X^2 * D) = coeff k D := cX _ 2 k
  have d0 : coeff (k+2) (X^0 * H) = coeff (k+2) H := cX _ 0 (k+2)
  have d1 : coeff (k+2) (X^1 * H) = coeff (k+1) H := cX _ 1 (k+1)
  rw [b0, b2, d0, d1] at h
  simp only [D, coeff_derivative] at h
  unfold Cg
  push_cast at h
  linear_combination h

lemma aG (N : ℕ) : (a (N+1) : ℤ) = Cg (N+1) (N+1) := by
  set I := invOfUnit ((1 - X : ℤ⟦X⟧) ^ 2) 1 with hIdef
  have hV : I ^ (N+1) = mk fun j => (((2*N+1+j).choose (2*N+1) : ℕ) : ℤ) := by
    have h1 := (invOneSubPow ℤ (2*N+1+1)).val_inv
    rw [invOneSubPow_inv_eq_one_sub_pow, invOneSubPow_val_succ_eq_mk_add_choose] at h1
    have h2 : I ^ (N+1) * (1 - X) ^ (2*N+1+1) = 1 := by
      rw [show 2*N+1+1 = 2*(N+1) by ring, pow_mul, ← mul_pow, mul_comm, hI, one_pow]
    linear_combination (mk fun j => (((2*N+1+j).choose (2*N+1) : ℕ) : ℤ)) * h2 - I ^ (N+1) * h1
  have hP : (1 + X : ℤ⟦X⟧) ^ (N+1) = (((1 + Polynomial.X) ^ (N+1) : Polynomial ℤ) : ℤ⟦X⟧) := by
    simp [Polynomial.coe_pow]
  unfold Cg G
  rw [mul_pow, ← hIdef, hV, mul_comm, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i (mk fun j => (((2*N+1+j).choose (2*N+1) : ℕ) : ℤ)) * coeff j ((1 + X : ℤ⟦X⟧) ^ (N+1)))]
  unfold a
  push_cast
  refine Finset.sum_congr rfl (fun k hk => ?_)
  simp only [Finset.mem_range] at hk
  rw [coeff_mk, hP, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow, Nat.choose_symm (by omega),
    show 2 * (N + 1) + k - 1 = 2*N+1+k by omega, Nat.choose_symm_add]
  ring

lemma R2 (N : ℕ) : 4 * ((N:ℤ)+2) * (2 * ((N:ℤ)+2) - 1) * (17 * ((N:ℤ)+2) ^ 2 - 52 * ((N:ℤ)+2) + 39) * a (N+2) -
    (1207 * ((N:ℤ)+2) ^ 4 - 4899 * ((N:ℤ)+2) ^ 3 + 6692 * ((N:ℤ)+2) ^ 2 - 3504 * ((N:ℤ)+2) + 576) * a (N+1) +
    2 * (((N:ℤ)+2) - 2) * (2 * ((N:ℤ)+2) - 3) * (17 * ((N:ℤ)+2) ^ 2 - 18 * ((N:ℤ)+2) + 4) * a N = 0 := by
  rcases N with _ | N
  · norm_num [a, Finset.sum_range_succ, Nat.choose]
  rw [aG (N+1), aG N, aG (N+1+1)]
  refine (mul_eq_zero.mp (?_ : (2 * ((N:ℤ)+2)) * _ = 0)).resolve_left (by positivity)
  have h0 := cD (N+1) (N+0)
  have h1 := cD (N+1) (N+1)
  have h2 := cD (N+2) (N+0)
  have h3 := cD (N+2) (N+1)
  have h4 := cD (N+3) (N+0)
  have h5 := cD (N+3) (N+1)
  have h6 := cQ (N+1) (N+1)
  have h7 := cQ (N+1) (N+2)
  have h8 := cQ (N+2) (N+1)
  have h9 := cQ (N+2) (N+2)
  push_cast at *
  ring_nf at *
  linear_combination (-68*(N:ℤ)^4 - 574*(N:ℤ)^3 - 1792*(N:ℤ)^2 - 2450*(N:ℤ) - 1236) * h0 + (-136*(N:ℤ)^4 - 1080*(N:ℤ)^3 - 3146*(N:ℤ)^2 - 3984*(N:ℤ) - 1854) * h1 + (238*(N:ℤ)^4 + 1890*(N:ℤ)^3 + 5480*(N:ℤ)^2 + 6846*(N:ℤ) + 3090) * h2 + (255*(N:ℤ)^4 + 2076*(N:ℤ)^3 + 6165*(N:ℤ)^2 + 7902*(N:ℤ) + 3690) * h3 + (51*(N:ℤ)^4 + 456*(N:ℤ)^3 + 1467*(N:ℤ)^2 + 1998*(N:ℤ) + 972) * h4 + (-119*(N:ℤ)^4 - 996*(N:ℤ)^3 - 3019*(N:ℤ)^2 - 3918*(N:ℤ) - 1836) * h5 + (476*(N:ℤ)^5 + 4494*(N:ℤ)^4 + 16630*(N:ℤ)^3 + 30132*(N:ℤ)^2 + 26718*(N:ℤ) + 9270) * h6 + (-136*(N:ℤ)^5 - 1624*(N:ℤ)^4 - 7466*(N:ℤ)^3 - 16568*(N:ℤ)^2 - 17790*(N:ℤ) - 7416) * h7 + (102*(N:ℤ)^5 + 1116*(N:ℤ)^4 + 4758*(N:ℤ)^3 + 9864*(N:ℤ)^2 + 9936*(N:ℤ) + 3888) * h8 + (119*(N:ℤ)^5 + 1472*(N:ℤ)^4 + 7003*(N:ℤ)^3 + 15994*(N:ℤ)^2 + 17508*(N:ℤ) + 7344) * h9

theorem solution_main :
    (∀ n : ℕ, 4 ≤ n →
      64 * (n : ℤ) * (2 * n - 1) * a n - 16 * (89 * (n : ℤ) ^ 2 - 134 * n + 63) * a (n - 1) +
        4 * (661 * (n : ℤ) ^ 2 - 2619 * n + 2576) * a (n - 2) -
        3 * (119 * (n : ℤ) ^ 2 - 713 * n + 1092) * a (n - 3) +
        6 * (2 * (n : ℤ) - 7) * ((n : ℤ) - 4) * a (n - 4) = 0) ∧
    (∀ n : ℕ, 3 ≤ n →
      16 * (n : ℤ) * (782 * n + 5365) * (2 * n - 1) * a n +
        8 * (3128 * (n : ℤ) ^ 3 - 362053 * n ^ 2 + 593930 * n - 290328) * a (n - 1) -
        3 * (726869 * (n : ℤ) ^ 3 - 5105981 * n ^ 2 + 11667946 * n - 8715544) * a (n - 2) +
        158 * (2 * (n : ℤ) - 5) * ((n : ℤ) - 3) * (391 * n - 764) * a (n - 3) = 0) ∧
    (∀ n : ℕ, 2 ≤ n →
      4 * (n : ℤ) * (2 * n - 1) * (17 * n ^ 2 - 52 * n + 39) * a n -
        (1207 * (n : ℤ) ^ 4 - 4899 * n ^ 3 + 6692 * n ^ 2 - 3504 * n + 576) * a (n - 1) +
        2 * ((n : ℤ) - 2) * (2 * n - 3) * (17 * n ^ 2 - 18 * n + 4) * a (n - 2) = 0) := by
  have q1 : ∀ x : ℤ, 17 * x ^ 2 - 52 * x + 39 ≠ 0 := by
    intro x; have : 0 < 17 * x ^ 2 - 52 * x + 39 := by
      rcases le_or_gt x 1 with h | h <;> nlinarith
    exact this.ne'
  have q2 : ∀ x : ℤ, 17 * x ^ 2 - 86 * x + 108 ≠ 0 := by
    intro x; have : 0 < 17 * x ^ 2 - 86 * x + 108 := by
      rcases le_or_gt x 2 with h | h <;> nlinarith
    exact this.ne'
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨N, rfl⟩ : ∃ N, n = N + 4 := ⟨n - 4, by omega⟩
    simp only [show N + 4 - 1 = N + 3 by omega, show N + 4 - 2 = N + 2 by omega,
      show N + 4 - 3 = N + 1 by omega, show N + 4 - 4 = N by omega]
    have r0 := R2 (N+2)
    have r1 := R2 (N+1)
    have r2 := R2 N
    simp only [show N + 2 + 2 = N + 4 by ring, show N + 2 + 1 = N + 3 by ring, show N + 1 + 2 = N + 3 by ring,
      show N + 1 + 1 = N + 2 by ring] at r0 r1 r2
    have key : (17 * ((N:ℤ)+4) ^ 2 - 52 * ((N:ℤ)+4) + 39) * ((17 * ((N:ℤ)+4) ^ 2 - 86 * ((N:ℤ)+4) + 108) *
      (64 * ((N + 4 : ℕ) : ℤ) * (2 * ((N + 4 : ℕ) : ℤ) - 1) * a (N + 4) - 16 * (89 * ((N + 4 : ℕ) : ℤ) ^ 2 - 134 * ((N + 4 : ℕ) : ℤ) + 63) * a (N + 3) +
        4 * (661 * ((N + 4 : ℕ) : ℤ) ^ 2 - 2619 * ((N + 4 : ℕ) : ℤ) + 2576) * a (N + 2) -
        3 * (119 * ((N + 4 : ℕ) : ℤ) ^ 2 - 713 * ((N + 4 : ℕ) : ℤ) + 1092) * a (N + 1) +
        6 * (2 * ((N + 4 : ℕ) : ℤ) - 7) * (((N + 4 : ℕ) : ℤ) - 4) * a N)) = 0 := by
      push_cast at r0 r1 r2 ⊢
      linear_combination 16 * (17 * ((N:ℤ)+4) ^ 2 - 86 * ((N:ℤ)+4) + 108) * r0
        - 12 * (51 * ((N:ℤ)+4) ^ 2 - 207 * ((N:ℤ)+4) + 209) * r1 + 3 * (17 * ((N:ℤ)+4) ^ 2 - 52 * ((N:ℤ)+4) + 39) * r2
    exact (mul_eq_zero.mp ((mul_eq_zero.mp key).resolve_left (q1 _))).resolve_left (q2 _)
  · intro n hn
    obtain ⟨N, rfl⟩ : ∃ N, n = N + 3 := ⟨n - 3, by omega⟩
    simp only [show N + 3 - 1 = N + 2 by omega, show N + 3 - 2 = N + 1 by omega,
      show N + 3 - 3 = N by omega]
    have r0 := R2 (N+1)
    have r1 := R2 N
    simp only [show N + 1 + 2 = N + 3 by ring, show N + 1 + 1 = N + 2 by ring] at r0 r1
    have key : (17 * ((N:ℤ)+3) ^ 2 - 52 * ((N:ℤ)+3) + 39) *
      (16 * ((N + 3 : ℕ) : ℤ) * (782 * ((N + 3 : ℕ) : ℤ) + 5365) * (2 * ((N + 3 : ℕ) : ℤ) - 1) * a (N + 3) +
        8 * (3128 * ((N + 3 : ℕ) : ℤ) ^ 3 - 362053 * ((N + 3 : ℕ) : ℤ) ^ 2 + 593930 * ((N + 3 : ℕ) : ℤ) - 290328) * a (N + 2) -
        3 * (726869 * ((N + 3 : ℕ) : ℤ) ^ 3 - 5105981 * ((N + 3 : ℕ) : ℤ) ^ 2 + 11667946 * ((N + 3 : ℕ) : ℤ) - 8715544) * a (N + 1) +
        158 * (2 * ((N + 3 : ℕ) : ℤ) - 5) * (((N + 3 : ℕ) : ℤ) - 3) * (391 * ((N + 3 : ℕ) : ℤ) - 764) * a N) = 0 := by
      push_cast at r0 r1 ⊢
      linear_combination 4 * (782 * ((N:ℤ)+3) + 5365) * r0 + 79 * (391 * ((N:ℤ)+3) - 764) * r1
    exact (mul_eq_zero.mp key).resolve_left (q1 _)
  · intro n hn
    obtain ⟨N, rfl⟩ : ∃ N, n = N + 2 := ⟨n - 2, by omega⟩
    simp only [show N + 2 - 1 = N + 1 by omega, show N + 2 - 2 = N by omega]
    have := R2 N
    push_cast
    linear_combination this

end OMA.S_oeis_a156894

theorem OMA.solution : type_of% @OMA.S_oeis_a156894.main := OMA.S_oeis_a156894.solution_main
