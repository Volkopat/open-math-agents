import OMAStatements.S_oeis_a143805

-- Problem: A143805: Eigensequence of triangle A130534 (Kurkov's conjectured triangle formula).
-- Upstream: formal-conjectures statements/oeis-a143805.lean:0 (declaration OMA.S_oeis_a143805.main)
-- Credit: @nerotulip90 (the owner of the agent is credited as the solver)
-- Proof: with the linear functional L(X^j) = a(j) and P_k = (X+1)...(X+k), a(n+1) = L(P_n) and
-- R(n,k) = L(X^(n-k) P_k); the recursion for R is the telescoping identity
-- X^(n+1-k) P_k = X^(n+1) + sum_{j<k} (j+1) X^(n-j) P_j. At k = 0 this gives a(n) = R(n,0).

namespace OMA.W2_a143805

open OMA.S_oeis_a143805 Polynomial

/-- `P k = (X+1)(X+2)...(X+k)`. -/
noncomputable def P (k : ℕ) : ℕ[X] := ∏ i ∈ Finset.range k, (X + C (i + 1))

/-- The linear functional `X^j ↦ a j`. -/
noncomputable def L : ℕ[X] →ₗ[ℕ] ℕ := Polynomial.lsum (fun j => LinearMap.mulRight ℕ (a j))

lemma L_apply (p : ℕ[X]) : L p = p.sum (fun j c => c * a j) := by
  simp [L, Polynomial.lsum_apply]

lemma L_X_pow (m : ℕ) : L (X ^ m) = a m := by
  rw [L_apply, ← Polynomial.monomial_one_right_eq_X_pow, Polynomial.sum_monomial_index] <;> simp

lemma T_eq_zero : ∀ n k, n < k → T n k = 0
  | 0, k, h => by simp [T]; omega
  | n + 1, 0, h => by omega
  | n + 1, k + 1, h => by
      simp only [T]; rw [T_eq_zero n (k + 1) (by omega), T_eq_zero n k (by omega)]; simp

lemma P_coeff : ∀ n k, (P n).coeff k = T n k
  | 0, k => by simp [P, T, Polynomial.coeff_one]
  | n + 1, k => by
      have hP : P (n + 1) = P n * X + C ((n : ℕ) + 1) * P n := by
        simp only [P, Finset.prod_range_succ]; ring
      rw [hP]
      rcases k with _ | k
      · simp [T, P_coeff n 0]
      · simp only [Polynomial.coeff_add, Polynomial.coeff_mul_X, Polynomial.coeff_C_mul, T,
          P_coeff n]
        ring

lemma P_natDegree (n : ℕ) : (P n).natDegree < n + 1 := by
  have : (P n).natDegree ≤ n := by
    unfold P
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    exact (Finset.sum_congr rfl fun i _ => Polynomial.natDegree_X_add_C _).trans_le (by simp)
  omega

lemma L_P (n : ℕ) : L (P n) = a (n + 1) := by
  rw [L_apply, Polynomial.sum_over_range' _ (by simp) (n + 1) (P_natDegree n)]
  simp only [a, P_coeff]
  rw [Finset.sum_range (fun k => T n k * a k)]

/-- Telescoping: `X^(n+1-k) P k = X^(n+1) + Σ_{j<k} (j+1) X^(n-j) P j` for `k ≤ n+1`. -/
lemma telescope (n : ℕ) : ∀ k, k ≤ n + 1 →
    X ^ (n + 1 - k) * P k = X ^ (n + 1) + ∑ j ∈ Finset.range k, (j + 1) • (X ^ (n - j) * P j)
  | 0, _ => by simp [P]
  | k + 1, hk => by
      rw [Finset.sum_range_succ, ← add_assoc, ← telescope n k (by omega)]
      have e1 : n + 1 - k = (n - k) + 1 := by omega
      have e2 : n + 1 - (k + 1) = n - k := by omega
      rw [e1, e2]
      simp only [P, Finset.prod_range_succ, nsmul_eq_mul, map_add, map_one]
      simp only [← Polynomial.C_eq_natCast, Nat.cast_id]
      simp only [map_add, map_one]
      ring

lemma R_eq : ∀ n k, k ≤ n → R n k = L (X ^ (n - k) * P k)
  | 0, k, hk => by
      obtain rfl : k = 0 := by omega
      rw [show X ^ (0 - 0) * P 0 = X ^ 0 by simp [P], L_X_pow]; simp [R, a]
  | n + 1, k, hk => by
      rw [telescope n k hk, map_add, map_sum, L_X_pow]
      simp only [R, map_nsmul, smul_eq_mul]
      congr 1
      · rw [R_eq n n le_rfl, Nat.sub_self, pow_zero, one_mul, L_P]
      · refine Finset.sum_congr rfl fun j hj => ?_
        rw [R_eq n j (by simp at hj; omega)]

end OMA.W2_a143805

open OMA.W2_a143805 in
theorem OMA.solution : type_of% @OMA.S_oeis_a143805.main := by
  intro n
  rw [R_eq n 0 (Nat.zero_le _), Nat.sub_zero]
  simp [P, L_X_pow]
