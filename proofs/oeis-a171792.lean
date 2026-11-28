import OMAStatements.S_oeis_a171792

-- Problem: OEIS A171792, Marcus's conjecture a(n) = Sum_{r=ceiling(n/2)..n-1} C(r,n-r) a(r)
-- Statement: statements/oeis-a171792.lean (declaration OMA.S_oeis_a171792.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. (x + x^2)^d = x^d (1 + x)^d, so the coefficient of x^n in A(x + x^2) is
-- Sum_{d <= n} a(d) C(d, n-d). The functional equation 2 A(x) = x + A(x + x^2) gives
--     2 a(n) = [n = 1] + a(n) + Sum_{d < n} a(d) C(d, n-d).
-- For n = 1 this is a(1) = 1. For n >= 2 it is the recurrence, because C(d, n-d) = 0 when
-- 2d < n.

namespace OMA.A171792

open PowerSeries

lemma coeff_one_add_X_pow (d k : ℕ) :
    coeff k (((1 : ℚ⟦X⟧) + X) ^ d) = (d.choose k : ℚ) := by
  have h : ((1 : ℚ⟦X⟧) + X) ^ d
      = (((1 : Polynomial ℚ) + Polynomial.X) ^ d).toPowerSeries := by
    simp
  rw [h, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

lemma coeff_pow (n d : ℕ) :
    coeff n (((X : ℚ⟦X⟧) + X ^ 2) ^ d) = if d ≤ n then ((d.choose (n - d) : ℕ) : ℚ) else 0 := by
  have h : ((X : ℚ⟦X⟧) + X ^ 2) ^ d = X ^ d * ((1 : ℚ⟦X⟧) + X) ^ d := by
    rw [← mul_pow]
    ring
  rw [h, coeff_X_pow_mul', coeff_one_add_X_pow]

lemma hasSubst : HasSubst ((X : ℚ⟦X⟧) + X ^ 2) := by
  apply HasSubst.of_constantCoeff_zero'
  simp

/-- The coefficients of `A (x + x ^ 2)`. -/
lemma coeff_comp (A : ℚ⟦X⟧) (n : ℕ) :
    coeff n (A.subst ((X : ℚ⟦X⟧) + X ^ 2))
      = ∑ d ∈ Finset.range (n + 1), coeff d A * ((d.choose (n - d) : ℕ) : ℚ) := by
  rw [coeff_subst' hasSubst]
  rw [finsum_eq_sum_of_support_subset (s := Finset.range (n + 1))]
  · refine Finset.sum_congr rfl fun d hd => ?_
    rw [coeff_pow, if_pos (by simpa [Nat.lt_succ_iff] using hd), smul_eq_mul]
  · intro d hd
    simp only [Function.mem_support, ne_eq] at hd
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hcon
    apply hd
    rw [coeff_pow, if_neg (by omega), smul_zero]

theorem recurrence (A : ℚ⟦X⟧) (h0 : constantCoeff A = 0)
    (hA : A = (1 / 2 : ℚ) • (X + A.subst (X + X ^ 2 : ℚ⟦X⟧))) :
    coeff 1 A = 1 ∧ ∀ n : ℕ, 2 ≤ n →
      coeff n A = ∑ r ∈ Finset.Icc ((n + 1) / 2) (n - 1), (r.choose (n - r) : ℚ) * coeff r A := by
  have hc0 : coeff 0 A = 0 := by
    rw [coeff_zero_eq_constantCoeff_apply]
    exact h0
  have key : ∀ n : ℕ, 2 * coeff n A
      = coeff n (X : ℚ⟦X⟧) + ∑ d ∈ Finset.range (n + 1), coeff d A * ((d.choose (n - d) : ℕ) : ℚ) := by
    intro n
    have h := congrArg (coeff n) hA
    rw [coeff_smul, map_add, coeff_comp, smul_eq_mul] at h
    linarith
  constructor
  · have h := key 1
    rw [Finset.sum_range_succ, Finset.sum_range_one, hc0, coeff_one_X] at h
    simp at h
    linarith
  · intro n hn
    have h := key n
    rw [Finset.sum_range_succ, coeff_X, if_neg (by omega)] at h
    simp only [Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, mul_one, zero_add] at h
    have h' : coeff n A = ∑ d ∈ Finset.range n, coeff d A * ((d.choose (n - d) : ℕ) : ℚ) := by
      linarith
    rw [h']
    have hsub : Finset.Icc ((n + 1) / 2) (n - 1) ⊆ Finset.range n := by
      intro r hr
      simp only [Finset.mem_Icc] at hr
      simp only [Finset.mem_range]
      omega
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun r _ => ?_
      ring
    · intro r hr hnot
      simp only [Finset.mem_range] at hr
      simp only [Finset.mem_Icc, not_and, not_le] at hnot
      have hlt : r < n - r := by
        by_contra hcon
        have := hnot (by omega)
        omega
      rw [Nat.choose_eq_zero_of_lt hlt]
      simp

end OMA.A171792

theorem OMA.solution : type_of% @OMA.S_oeis_a171792.main :=
  fun A h0 hA => OMA.A171792.recurrence A h0 hA
