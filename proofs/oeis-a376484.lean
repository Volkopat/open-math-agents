import OMAStatements.S_oeis_a376484

open scoped BigOperators
open Finset

namespace OMA.RootPowerSums

private theorem polynomial_sum (m : ℕ) (w : ℂ) (hw : w ^ m = 1) (p : Polynomial ℤ) :
    ∃ z : ℤ, (∑ j ∈ range m, p.eval₂ (Int.castRingHom ℂ) (w ^ j)) = (z : ℂ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hq
      refine ⟨a + b, ?_⟩
      simp only [Polynomial.eval₂_add, Finset.sum_add_distrib, ha, hb, Int.cast_add]
  | monomial d a =>
      have comm (j : ℕ) : (w ^ j) ^ d = (w ^ d) ^ j := by
        rw [← pow_mul, Nat.mul_comm j d, pow_mul]
      simp only [Polynomial.eval₂_monomial, comm, ← Finset.mul_sum]
      by_cases h : w ^ d = 1
      · exact ⟨a * (m : ℤ), by simp [h]⟩
      · have hp : (w ^ d) ^ m = 1 := by
          rw [← pow_mul, Nat.mul_comm d m, pow_mul, hw, one_pow]
        have hz := geom_sum_mul (w ^ d) m
        rw [hp, sub_self] at hz
        have hs : (∑ j ∈ range m, (w ^ d) ^ j) = 0 :=
          (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr h)
        exact ⟨0, by simp [hs]⟩

private theorem result (n k : ℕ) : ∃ z : ℤ, OMA.S_oeis_a376484.entry n k = z := by
  let m := 2 * n + 1
  have hm : 0 < m := by dsimp [m]; omega
  have hmr : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  let t (j : ℕ) : ℝ := 2 * (j : ℝ) * Real.pi / m
  let F (j : ℕ) : ℝ := 4 ^ k * Real.sin (t j) ^ (2 * k)
  let w := Complex.exp ((↑(2 * t 1) : ℂ) * Complex.I)
  have hExp (j : ℕ) : w ^ j = Complex.exp ((↑(2 * t j) : ℂ) * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    dsimp [t]
    push_cast
    ring
  have hw : w ^ m = 1 := by
    rw [hExp]
    have ha : (↑(2 * t m) : ℂ) * Complex.I =
        ((2 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      dsimp [t]
      push_cast
      field_simp
    rw [ha, Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]
  have hjw (j : ℕ) : (w ^ j) ^ m = 1 := by
    rw [← pow_mul, Nat.mul_comm j m, pow_mul, hw, one_pow]
  have hF (j : ℕ) : (F j : ℂ) = (2 - w ^ j - (w ^ j) ^ (m - 1)) ^ k := by
    have hi : (w ^ j) ^ (m - 1) = (w ^ j)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ m), hjw])
    have hbase : ((4 * Real.sin (t j) ^ 2 : ℝ) : ℂ) = 2 - w ^ j - (w ^ j) ^ (m - 1) := by
      rw [hi, hExp, ← Complex.exp_neg]
      rw [show -(((2 * t j : ℝ) : ℂ) * Complex.I) = (-((2 * t j : ℝ) : ℂ)) * Complex.I by ring]
      rw [Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
      push_cast
      rw [Complex.cos_two_mul_eq_one_sub]
      ring
    change ((4 ^ k * Real.sin (t j) ^ (2 * k) : ℝ) : ℂ) = _
    rw [pow_mul, ← mul_pow, Complex.ofReal_pow, hbase]
  have hhalf : (∑ j ∈ range n, F (j + 1)) = OMA.S_oeis_a376484.entry n k := by
    unfold OMA.S_oeis_a376484.entry
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [F, t, OMA.S_oeis_a376484.angle, Nat.cast_add, Nat.cast_one, m, Nat.cast_mul, Nat.cast_ofNat]
  have hreflect (j : ℕ) (h : j ≤ m) : F (m - j) = F j := by
    have hangle : t (m - j) = 2 * Real.pi - t j := by
      dsimp [t]
      rw [Nat.cast_sub h]
      field_simp
    have hs : Real.sin (t (m - j)) = -Real.sin (t j) := by
      rw [hangle, Real.sin_sub, Real.sin_two_pi, Real.cos_two_pi]
      ring
    simp only [F, pow_mul _ 2, hs, neg_sq]
  have hsecond : (∑ j ∈ range n, F (n + 1 + j)) = ∑ j ∈ range n, F (j + 1) := by
    rw [← Finset.sum_range_reflect (fun j => F (n + 1 + j)) n]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn := Finset.mem_range.mp hj
    have hind : n + 1 + (n - 1 - j) = m - (j + 1) := by dsimp [m]; omega
    rw [hind, hreflect (j + 1) (by dsimp [m]; omega)]
  have hsplit : (∑ j ∈ range m, F j) = F 0 + 2 * OMA.S_oeis_a376484.entry n k := by
    rw [show m = n + 1 + n by dsimp [m]; omega, Finset.sum_range_add,
      Finset.sum_range_succ', hsecond, hhalf]
    ring
  let p : Polynomial ℤ := (2 - Polynomial.X - Polynomial.X ^ (m - 1)) ^ k
  have heval (j : ℕ) : p.eval₂ (Int.castRingHom ℂ) (w ^ j) = (F j : ℂ) := by
    rw [hF]
    simp only [p, Polynomial.eval₂_pow, Polynomial.eval₂_sub, Polynomial.eval₂_X,
      Polynomial.eval₂_ofNat]
  obtain ⟨z, hz⟩ := polynomial_sum m w hw p
  simp only [heval] at hz
  let z₀ : ℤ := if k = 0 then 1 else 0
  have hzero : F 0 = (z₀ : ℝ) := by
    by_cases hk : k = 0
    · simp [F, z₀, hk]
    · have hpos : 2 * k ≠ 0 := by omega
      simp [F, t, z₀, hk, hpos]
  have hfull : (z : ℂ) = (z₀ : ℂ) + 2 * (OMA.S_oeis_a376484.entry n k : ℂ) := by
    simpa only [hzero, Complex.ofReal_sum, Complex.ofReal_add, Complex.ofReal_mul,
      Complex.ofReal_intCast, Complex.ofReal_ofNat, hz]
      using congrArg (fun x : ℝ => (x : ℂ)) hsplit
  have hint : IsIntegral ℤ (OMA.S_oeis_a376484.entry n k : ℂ) := by
    rw [← hhalf, Complex.ofReal_sum]
    apply IsIntegral.sum
    intro j _
    rw [hF]
    have hwi : IsIntegral ℤ (w ^ (j + 1)) := IsIntegral.of_pow hm (by rw [hjw]; exact isIntegral_one)
    have htwo : IsIntegral ℤ (2 : ℂ) := by
      simpa using (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (2 : ℤ)))
    exact ((htwo.sub hwi).sub (hwi.pow (m - 1))).pow k
  let q : ℚ := ((z : ℚ) - (z₀ : ℚ)) / 2
  have hq : algebraMap ℚ ℂ q = (OMA.S_oeis_a376484.entry n k : ℂ) := by
    change (q : ℂ) = _
    dsimp [q]
    push_cast
    apply (div_eq_iff (by norm_num : (2 : ℂ) ≠ 0)).mpr
    linear_combination hfull
  have hqi : IsIntegral ℤ q :=
    (isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).mp (hq ▸ hint)
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hqi
  refine ⟨a, Complex.ofReal_injective ?_⟩
  rw [Complex.ofReal_intCast, ← hq, ← ha]
  simp

end OMA.RootPowerSums

theorem OMA.solution : type_of% @OMA.S_oeis_a376484.main := OMA.RootPowerSums.result