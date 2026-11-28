import OMAReductions.R_EllipticDivisibilitySequence_silverman_eds_primitive_prime_divisors_R1_H2_R1

/-!
# Proof of `EllipticDivisibilitySequence.silverman_eds_primitive_prime_divisors.R1.H2.R1.H2`

For any non-periodic normalized nonsingular elliptic divisibility sequence `W` attached to a
rational point `P = (x, y)` on a nonsingular Weierstrass curve `E / ℚ`, we show that for every
`p : ℕ`, `((d n).factorization p : ℝ) / n^2 → 0` as `n → ∞`, where `d n` is the reduced
denominator of `W(n+1) * W(n-1) / W(n)^2`.

The proof works uniformly for every prime `p` (including `p = 2, 3` and bad-reduction primes):
1. By induction using Ward's elliptic recurrence, for every `n ≥ 1`, `n • P = .some x_n y_n`
   with `x_n - x = -W(n+1) W(n-1) / W(n)^2`, so `d n = (x_n - x).den`.
2. Scaling `E` by `u = p^M` yields an isomorphic curve `E'` whose Weierstrass coefficients all
   have `p`-adic valuation `≥ 1` (whenever nonzero).
3. On `E'`, the filtration `E'_r = {0} ∪ {(x', y') : v_p(x') ≤ -2r}` (`r ≥ 1`) with formal-group
   parameter `t = -x'/y'` satisfies `v_p(t(Q₁ + Q₂) - t(Q₁) - t(Q₂)) ≥ 2r + 1`.
4. Hence `H = {n : ℤ | n • P' ∈ E'_1}` is a subgroup of `ℤ` on which `v_p(t(k • R)) = v_p(t(R)) + v_p(k)`,
   giving `(d n).factorization p ≤ C + 2 * n` for all `n ≥ 2` and therefore `((d n).factorization p : ℝ) / n^2 → 0`.
-/

-- Step EllipticDivisibilitySequence.silverman_eds_primitive_prime_divisors.R1.H2.R1.H2
-- Credit: @KevinBigham

namespace SilvermanEDSR1H2R1H2

open EllipticDivisibilitySequence Filter Real

/- ### Part 1: Coordinates of `n • P` in terms of `W` -/

private lemma W_zero_and_neg {W : ℤ → ℤ} (hw : IsNonsingularEDS W) :
    W 0 = 0 ∧ ∀ m : ℤ, W (-m) = -W m := by
  obtain ⟨_, _, E, x, y, _, _, hψ⟩ := hw
  constructor
  · have h0 : (W 0 : ℚ) = 0 := by
      rw [hψ 0, WeierstrassCurve.ψ_zero]
      simp [Polynomial.evalEval]
    exact_mod_cast h0
  · intro m
    have hm : (W (-m) : ℚ) = -(W m : ℚ) := by
      rw [hψ (-m), hψ m, WeierstrassCurve.ψ_neg]
      simp [Polynomial.evalEval]
    exact_mod_cast hm

private lemma ward_rel {W : ℤ → ℤ} (hw : IsEllipticDvdSequence W) (h1 : W 1 = 1) (a b : ℤ) :
    W (a + b) * W (a - b) =
      W (a + 1) * W (a - 1) * W b ^ 2 - W (b + 1) * W (b - 1) * W a ^ 2 := by
  have rel := hw.1 a b 1
  simp only [IsEllipticNet.rel, add_zero, h1, mul_one] at rel
  linear_combination rel

private lemma evalEval_ψ_two (E : WeierstrassCurve ℚ) (x y : ℚ) :
    (E.ψ 2).evalEval x y = 2 * y + E.a₁ * x + E.a₃ := by
  rw [WeierstrassCurve.ψ_two, WeierstrassCurve.ψ₂]
  simp [Polynomial.evalEval, WeierstrassCurve.Affine.polynomialY]
  ring

private lemma evalEval_ψ_three (E : WeierstrassCurve ℚ) (x y : ℚ) :
    (E.ψ 3).evalEval x y =
      3 * x ^ 4 + E.b₂ * x ^ 3 + 3 * E.b₄ * x ^ 2 + 3 * E.b₆ * x + E.b₈ := by
  rw [WeierstrassCurve.ψ_three, Polynomial.evalEval_C, WeierstrassCurve.Ψ₃]
  simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_ofNat]

private lemma evalEval_ψ_four (E : WeierstrassCurve ℚ) (x y : ℚ) :
    (E.ψ 4).evalEval x y =
      (2 * y + E.a₁ * x + E.a₃) *
        (2 * x ^ 6 + E.b₂ * x ^ 5 + 5 * E.b₄ * x ^ 4 + 10 * E.b₆ * x ^ 3 +
          10 * E.b₈ * x ^ 2 + (E.b₂ * E.b₈ - E.b₄ * E.b₆) * x + (E.b₄ * E.b₈ - E.b₆ ^ 2)) := by
  rw [WeierstrassCurve.ψ_four, Polynomial.evalEval_mul, Polynomial.evalEval_C,
    WeierstrassCurve.preΨ₄, WeierstrassCurve.ψ₂]
  simp [Polynomial.evalEval, WeierstrassCurve.Affine.polynomialY,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat]
  ring

private lemma nsmul_coords {W : ℤ → ℤ} (hw : IsEllipticDvdSequence W) (h1 : W 1 = 1)
    (h0 : W 0 = 0) (hneg : ∀ m : ℤ, W (-m) = -W m)
    (hW : ∀ i : ℤ, i ≠ 0 → W i ≠ 0)
    (E : WeierstrassCurve ℚ) (x y : ℚ) (hΔ : E.Δ ≠ 0) (hEq : E.toAffine.Equation x y)
    (hψ : ∀ n : ℤ, (W n : ℚ) = (E.ψ n).evalEval x y) :
    let hns : E.toAffine.Nonsingular x y :=
      (E.toAffine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp hEq
    let P : E.toAffine.Point := WeierstrassCurve.Affine.Point.some x y hns
    ∀ n : ℕ, 1 ≤ n →
      ∃ (xn yn : ℚ) (hnsn : E.toAffine.Nonsingular xn yn),
        n • P = WeierstrassCurve.Affine.Point.some xn yn hnsn ∧
        xn = x - ((W ((n : ℤ) + 1) : ℚ) * (W ((n : ℤ) - 1) : ℚ)) / (W (n : ℤ) : ℚ) ^ 2 ∧
        2 * yn + E.a₁ * xn + E.a₃ =
          ((W ((n : ℤ) + 2) : ℚ) * (W ((n : ℤ) - 1) : ℚ) ^ 2 -
            (W ((n : ℤ) - 2) : ℚ) * (W ((n : ℤ) + 1) : ℚ) ^ 2) /
          ((W 2 : ℚ) * (W (n : ℤ) : ℚ) ^ 3) := by
  intro hns P
  have hWq : ∀ i : ℤ, i ≠ 0 → (W i : ℚ) ≠ 0 := fun i hi => Int.cast_ne_zero.mpr (hW i hi)
  have hW2 : (W 2 : ℚ) = 2 * y + E.a₁ * x + E.a₃ := by
    rw [hψ 2, evalEval_ψ_two]
  have hW3 : (W 3 : ℚ) = 3 * x ^ 4 + E.b₂ * x ^ 3 + 3 * E.b₄ * x ^ 2 + 3 * E.b₆ * x + E.b₈ := by
    rw [hψ 3, evalEval_ψ_three]
  have hW4 : (W 4 : ℚ) = (2 * y + E.a₁ * x + E.a₃) *
      (2 * x ^ 6 + E.b₂ * x ^ 5 + 5 * E.b₄ * x ^ 4 + 10 * E.b₆ * x ^ 3 +
        10 * E.b₈ * x ^ 2 + (E.b₂ * E.b₈ - E.b₄ * E.b₆) * x + (E.b₄ * E.b₈ - E.b₆ ^ 2)) := by
    rw [hψ 4, evalEval_ψ_four]
  have hEq' : y ^ 2 + E.a₁ * x * y + E.a₃ * y = x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆ := by
    simpa [WeierstrassCurve.Affine.equation_iff] using hEq
  have hW2_ne : (W 2 : ℚ) ≠ 0 := hWq 2 (by decide)
  have hy_ne_neg : y ≠ E.toAffine.negY x y := by
    intro h
    rw [WeierstrassCurve.Affine.negY] at h
    apply hW2_ne
    rw [hW2]
    linarith
  have hbase1 : ∃ (xn yn : ℚ) (hnsn : E.toAffine.Nonsingular xn yn),
      (1 : ℕ) • P = WeierstrassCurve.Affine.Point.some xn yn hnsn ∧
      xn = x - ((W ((1 : ℤ) + 1) : ℚ) * (W ((1 : ℤ) - 1) : ℚ)) / (W (1 : ℤ) : ℚ) ^ 2 ∧
      2 * yn + E.a₁ * xn + E.a₃ =
        ((W ((1 : ℤ) + 2) : ℚ) * (W ((1 : ℤ) - 1) : ℚ) ^ 2 -
          (W ((1 : ℤ) - 2) : ℚ) * (W ((1 : ℤ) + 1) : ℚ) ^ 2) /
        ((W 2 : ℚ) * (W (1 : ℤ) : ℚ) ^ 3) := by
    refine ⟨x, y, hns, one_smul ℕ P, ?_, ?_⟩
    · norm_num [h0, h1]
    · have hm1 : W (-1) = -1 := by rw [hneg 1, h1]
      norm_num [h0, h1, hm1]
      field_simp [hW2_ne]
      linarith [hW2]
  have hbase2 : ∃ (xn yn : ℚ) (hnsn : E.toAffine.Nonsingular xn yn),
      (2 : ℕ) • P = WeierstrassCurve.Affine.Point.some xn yn hnsn ∧
      xn = x - ((W ((2 : ℤ) + 1) : ℚ) * (W ((2 : ℤ) - 1) : ℚ)) / (W (2 : ℤ) : ℚ) ^ 2 ∧
      2 * yn + E.a₁ * xn + E.a₃ =
        ((W ((2 : ℤ) + 2) : ℚ) * (W ((2 : ℤ) - 1) : ℚ) ^ 2 -
          (W ((2 : ℤ) - 2) : ℚ) * (W ((2 : ℤ) + 1) : ℚ) ^ 2) /
        ((W 2 : ℚ) * (W (2 : ℤ) : ℚ) ^ 3) := by
    have h2P : (2 : ℕ) • P = P + P := two_nsmul P
    rw [h2P, WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy_ne_neg]
    refine ⟨_, _, _, rfl, ?_, ?_⟩
    · have hL : E.toAffine.slope x x y y =
          (3 * x ^ 2 + 2 * E.a₂ * x + E.a₄ - E.a₁ * y) / (W 2 : ℚ) := by
        rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy_ne_neg, WeierstrassCurve.Affine.negY, hW2]
        congr 1; ring
      simp only [WeierstrassCurve.Affine.addX, hL]
      norm_num [h1]
      field_simp [hW2_ne]
      rw [hW3, hW2]
      simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      linear_combination
        -(E.a₁ ^ 2 + 4 * E.a₂ + 12 * x) * hEq'
    · have hL : E.toAffine.slope x x y y =
          (3 * x ^ 2 + 2 * E.a₂ * x + E.a₄ - E.a₁ * y) / (W 2 : ℚ) := by
        rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy_ne_neg, WeierstrassCurve.Affine.negY, hW2]
        congr 1; ring
      have hx2 : E.toAffine.addX x x (E.toAffine.slope x x y y) - x = -(W 3 : ℚ) / (W 2 : ℚ) ^ 2 := by
        simp only [WeierstrassCurve.Affine.addX, hL]
        field_simp [hW2_ne]
        rw [hW3, hW2]
        simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
        linear_combination -(E.a₁ ^ 2 + 4 * E.a₂ + 12 * x) * hEq'
      have hline2 :
          2 * E.toAffine.addY x x y (E.toAffine.slope x x y y) +
            E.a₁ * E.toAffine.addX x x (E.toAffine.slope x x y y) + E.a₃ =
          -(2 * E.toAffine.slope x x y y + E.a₁) *
            (E.toAffine.addX x x (E.toAffine.slope x x y y) - x) - (W 2 : ℚ) := by
        simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
          WeierstrassCurve.Affine.negAddY, hW2]
        ring
      rw [hline2, hx2, hL]
      norm_num [h0, h1]
      field_simp [hW2_ne]
      have h2A : 2 * (3 * x ^ 2 + 2 * E.a₂ * x + E.a₄ - E.a₁ * y) + E.a₁ * (W 2 : ℚ) =
          6 * x ^ 2 + E.b₂ * x + E.b₄ := by
        rw [hW2]
        simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄]
        ring
      have hW2sq : (W 2 : ℚ) ^ 2 = 4 * x ^ 3 + E.b₂ * x ^ 2 + 2 * E.b₄ * x + E.b₆ := by
        rw [hW2]
        simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
        linear_combination 4 * hEq'
      have hb_rel : E.b₂ * E.b₆ - E.b₄ ^ 2 = 4 * E.b₈ := by
        simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
        ring
      have hpre4 : (6 * x ^ 2 + E.b₂ * x + E.b₄) * (W 3 : ℚ) - (W 2 : ℚ) ^ 4 =
          2 * x ^ 6 + E.b₂ * x ^ 5 + 5 * E.b₄ * x ^ 4 + 10 * E.b₆ * x ^ 3 +
            10 * E.b₈ * x ^ 2 + (E.b₂ * E.b₈ - E.b₄ * E.b₆) * x + (E.b₄ * E.b₈ - E.b₆ ^ 2) := by
        rw [hW3, show (W 2 : ℚ) ^ 4 = ((W 2 : ℚ) ^ 2) ^ 2 by ring, hW2sq]
        linear_combination x ^ 2 * hb_rel
      rw [hW4, ← hW2, ← hpre4]
      linear_combination (W 2 : ℚ) * (W 3 : ℚ) * h2A
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases eq_or_lt_of_le hn with rfl | hn2
    · exact hbase1
    rcases eq_or_lt_of_le (show 2 ≤ n by omega) with rfl | hn3
    · exact hbase2
    -- Now n ≥ 3, write n = k + 1 with k ≥ 2
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hk2 : 2 ≤ k := by omega
    obtain ⟨xk, yk, hnsk, hPk, hxk, hyk⟩ := ih k (by omega) (by omega)
    obtain ⟨xkm1, ykm1, hnskm1, hPkm1, hxkm1, _⟩ := ih (k - 1) (by omega) (by omega)
    have hWk_ne : (W (k : ℤ) : ℚ) ≠ 0 := hWq k (by omega)
    have hWkp1_ne : (W ((k : ℤ) + 1) : ℚ) ≠ 0 := hWq ((k : ℤ) + 1) (by omega)
    have hWkm1_ne : (W ((k : ℤ) - 1) : ℚ) ≠ 0 := hWq ((k : ℤ) - 1) (by omega)
    have hxk_ne : xk ≠ x := by
      rw [hxk]
      intro h
      have hzero : ((W ((k : ℤ) + 1) : ℚ) * (W ((k : ℤ) - 1) : ℚ)) / (W (k : ℤ) : ℚ) ^ 2 = 0 := by
        linarith
      have := div_eq_zero_iff.mp hzero
      rcases this with hnum | hden
      · rcases mul_eq_zero.mp hnum with h1' | h2'
        · exact hWkp1_ne h1'
        · exact hWkm1_ne h2'
      · exact pow_ne_zero 2 hWk_ne hden
    have hPkp1 : (k + 1) • P = k • P + P := add_nsmul P k 1
    rw [hPkp1, hPk, WeierstrassCurve.Affine.Point.add_of_X_ne hxk_ne]
    refine ⟨_, _, _, rfl, ?_, ?_⟩
    · -- Compute x_{k+1} via x(Q + P) - x(Q - P) = -W(2)*(2y_k + a1 x_k + a3)/(x_k - x)^2
      clear hbase1 hbase2 ih
      have hPkm1_eq : k • P + (-P) = (k - 1) • P := by
        have hksub : (k - 1) + 1 = k := by omega
        calc k • P + (-P) = ((k - 1) + 1) • P + (-P) := by rw [hksub]
          _ = (k - 1) • P + P + (-P) := by rw [add_nsmul, one_smul]
          _ = (k - 1) • P := by abel
      rw [hPk, WeierstrassCurve.Affine.Point.neg_some,
        WeierstrassCurve.Affine.Point.add_of_X_ne hxk_ne, hPkm1] at hPkm1_eq
      have hxkm1_add : E.toAffine.addX xk x (E.toAffine.slope xk x yk (E.toAffine.negY x y)) = xkm1 := by
        exact (WeierstrassCurve.Affine.Point.some.inj hPkm1_eq).1
      let Lp := E.toAffine.slope xk x yk y
      let Lm := E.toAffine.slope xk x yk (E.toAffine.negY x y)
      have hLp : Lp = (yk - y) / (xk - x) := WeierstrassCurve.Affine.slope_of_X_ne hxk_ne
      have hLm : Lm = (yk - E.toAffine.negY x y) / (xk - x) :=
        WeierstrassCurve.Affine.slope_of_X_ne hxk_ne
      have hdiff : E.toAffine.addX xk x Lp - xkm1 =
          -(W 2 : ℚ) * (2 * yk + E.a₁ * xk + E.a₃) / (xk - x) ^ 2 := by
        rw [← hxkm1_add]
        change E.toAffine.addX xk x Lp - E.toAffine.addX xk x Lm = _
        simp only [WeierstrassCurve.Affine.addX, hLp, hLm, WeierstrassCurve.Affine.negY, hW2]
        have hsub_ne : xk - x ≠ 0 := sub_ne_zero.mpr hxk_ne
        field_simp [hsub_ne]
        ring
      have hcast_km1 : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
      have hxkm1' : xkm1 = x - ((W (k : ℤ) : ℚ) * (W ((k : ℤ) - 2) : ℚ)) / (W ((k : ℤ) - 1) : ℚ) ^ 2 := by
        rw [hxkm1, hcast_km1]
        have h1' : (k : ℤ) - 1 + 1 = (k : ℤ) := by ring
        have h2' : (k : ℤ) - 1 - 1 = (k : ℤ) - 2 := by ring
        rw [h1', h2']
      have hcast_kp1 : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by omega
      rw [hcast_kp1]
      have h1' : (k : ℤ) + 1 + 1 = (k : ℤ) + 2 := by ring
      have h2' : (k : ℤ) + 1 - 1 = (k : ℤ) := by ring
      rw [h1', h2']
      have hsub_eq : xk - x = -((W ((k : ℤ) + 1) : ℚ) * (W ((k : ℤ) - 1) : ℚ)) / (W (k : ℤ) : ℚ) ^ 2 := by
        rw [hxk]; ring
      have hsub_ne : xk - x ≠ 0 := sub_ne_zero.mpr hxk_ne
      have hgoal : E.toAffine.addX xk x Lp = xkm1 - (W 2 : ℚ) * (2 * yk + E.a₁ * xk + E.a₃) / (xk - x) ^ 2 := by
        rw [neg_mul, neg_div] at hdiff
        linarith [hdiff]
      change E.toAffine.addX xk x Lp = _
      rw [hgoal, hxkm1', hyk, hsub_eq]
      field_simp [hWk_ne, hWkp1_ne, hWkm1_ne, hW2_ne]
      ring
    · -- Compute 2 y_{k+1} + a1 x_{k+1} + a3 using the chord line and two Ward relations
      clear hbase1 hbase2 ih
      let Lp := E.toAffine.slope xk x yk y
      let xkp1 := E.toAffine.addX xk x Lp
      have hLp : Lp = (yk - y) / (xk - x) := WeierstrassCurve.Affine.slope_of_X_ne hxk_ne
      have hPkm1_eq : k • P + (-P) = (k - 1) • P := by
        have hksub : (k - 1) + 1 = k := by omega
        calc k • P + (-P) = ((k - 1) + 1) • P + (-P) := by rw [hksub]
          _ = (k - 1) • P + P + (-P) := by rw [add_nsmul, one_smul]
          _ = (k - 1) • P := by abel
      rw [hPk, WeierstrassCurve.Affine.Point.neg_some,
        WeierstrassCurve.Affine.Point.add_of_X_ne hxk_ne, hPkm1] at hPkm1_eq
      have hxkm1_add : E.toAffine.addX xk x (E.toAffine.slope xk x yk (E.toAffine.negY x y)) = xkm1 :=
        (WeierstrassCurve.Affine.Point.some.inj hPkm1_eq).1
      have hLm : E.toAffine.slope xk x yk (E.toAffine.negY x y) =
          (yk - E.toAffine.negY x y) / (xk - x) := WeierstrassCurve.Affine.slope_of_X_ne hxk_ne
      have hsub_ne : xk - x ≠ 0 := sub_ne_zero.mpr hxk_ne
      have hcast_km1 : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
      have hxkm1' : xkm1 = x - ((W (k : ℤ) : ℚ) * (W ((k : ℤ) - 2) : ℚ)) / (W ((k : ℤ) - 1) : ℚ) ^ 2 := by
        rw [hxkm1, hcast_km1]
        have h1' : (k : ℤ) - 1 + 1 = (k : ℤ) := by ring
        have h2' : (k : ℤ) - 1 - 1 = (k : ℤ) - 2 := by ring
        rw [h1', h2']
      have hxkp1 : xkp1 = x - ((W ((k : ℤ) + 2) : ℚ) * (W (k : ℤ) : ℚ)) / (W ((k : ℤ) + 1) : ℚ) ^ 2 := by
        have hdiff : xkp1 - xkm1 = -(W 2 : ℚ) * (2 * yk + E.a₁ * xk + E.a₃) / (xk - x) ^ 2 := by
          dsimp only [xkp1]
          rw [← hxkm1_add, hLm, hLp]
          simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY, hW2]
          field_simp [hsub_ne]
          ring
        have hsub_eq : xk - x = -((W ((k : ℤ) + 1) : ℚ) * (W ((k : ℤ) - 1) : ℚ)) / (W (k : ℤ) : ℚ) ^ 2 := by
          rw [hxk]; ring
        have hgoal : xkp1 = xkm1 - (W 2 : ℚ) * (2 * yk + E.a₁ * xk + E.a₃) / (xk - x) ^ 2 := by
          rw [neg_mul, neg_div] at hdiff
          linarith [hdiff]
        rw [hgoal, hxkm1', hyk, hsub_eq]
        field_simp [hWk_ne, hWkp1_ne, hWkm1_ne, hW2_ne]
        ring
      have hcast_kp1 : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by omega
      rw [hcast_kp1]
      have h3' : (k : ℤ) + 1 + 2 = (k : ℤ) + 3 := by ring
      have h4' : (k : ℤ) + 1 - 1 = (k : ℤ) := by ring
      have h5' : (k : ℤ) + 1 - 2 = (k : ℤ) - 1 := by ring
      have h6' : (k : ℤ) + 1 + 1 = (k : ℤ) + 2 := by ring
      rw [h3', h4', h5', h6']
      have hline : 2 * E.toAffine.addY xk x yk Lp + E.a₁ * xkp1 + E.a₃ =
          -((2 * yk + E.a₁ * xk + E.a₃ - (W 2 : ℚ)) / (xk - x) * (xkp1 - x) + (W 2 : ℚ)) := by
        dsimp only [xkp1]
        simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
          WeierstrassCurve.Affine.negAddY, hLp, hW2]
        field_simp [hsub_ne]
        ring
      rw [hline, hyk]
      have hsubk : xk - x = -((W ((k : ℤ) + 1) : ℚ) * (W ((k : ℤ) - 1) : ℚ)) / (W (k : ℤ) : ℚ) ^ 2 := by
        rw [hxk]; ring
      have hsubkp1 : xkp1 - x = -((W ((k : ℤ) + 2) : ℚ) * (W (k : ℤ) : ℚ)) / (W ((k : ℤ) + 1) : ℚ) ^ 2 := by
        rw [hxkp1]; ring
      rw [hsubk, hsubkp1]
      have hR1 : (W ((k : ℤ) + 2) : ℚ) * (W ((k : ℤ) - 2) : ℚ) =
          (W ((k : ℤ) + 1) : ℚ) * (W ((k : ℤ) - 1) : ℚ) * (W 2 : ℚ) ^ 2 -
            (W 3 : ℚ) * (W (k : ℤ) : ℚ) ^ 2 := by
        have r := ward_rel hw h1 (k : ℤ) 2
        norm_num [h1] at r
        exact_mod_cast r
      have hR2 : (W ((k : ℤ) + 3) : ℚ) * (W ((k : ℤ) - 1) : ℚ) =
          (W ((k : ℤ) + 2) : ℚ) * (W (k : ℤ) : ℚ) * (W 2 : ℚ) ^ 2 -
            (W 3 : ℚ) * (W ((k : ℤ) + 1) : ℚ) ^ 2 := by
        have r := ward_rel hw h1 ((k : ℤ) + 1) 2
        have ha1 : (k : ℤ) + 1 + 2 = (k : ℤ) + 3 := by ring
        have ha2 : (k : ℤ) + 1 - 2 = (k : ℤ) - 1 := by ring
        have ha3 : (k : ℤ) + 1 + 1 = (k : ℤ) + 2 := by ring
        have ha4 : (k : ℤ) + 1 - 1 = (k : ℤ) := by ring
        rw [ha1, ha2, ha3, ha4] at r
        norm_num [h1] at r
        exact_mod_cast r
      field_simp [hWk_ne, hWkp1_ne, hWkm1_ne, hW2_ne]
      linear_combination
        (W ((k : ℤ) + 1) : ℚ) ^ 2 * hR1 - (W (k : ℤ) : ℚ) ^ 2 * hR2

/- ### Part 2: `p`-adic valuation helper predicate `ValGe` -/

private def ValGe (p : ℕ) (k : ℤ) (q : ℚ) : Prop :=
  q = 0 ∨ k ≤ padicValRat p q

private lemma valGe_zero (p : ℕ) (k : ℤ) : ValGe p k 0 := Or.inl rfl

private lemma valGe_mono {p : ℕ} {k₁ k₂ : ℤ} {q : ℚ} (h : k₁ ≤ k₂) (hq : ValGe p k₂ q) :
    ValGe p k₁ q :=
  hq.imp_right (le_trans h)

private lemma valGe_neg {p : ℕ} {k : ℤ} {q : ℚ} (hq : ValGe p k q) : ValGe p k (-q) := by
  rcases hq with rfl | hq
  · exact Or.inl neg_zero
  · right; rwa [padicValRat.neg]

private lemma valGe_add {p : ℕ} [Fact p.Prime] {k : ℤ} {q r : ℚ}
    (hq : ValGe p k q) (hr : ValGe p k r) : ValGe p k (q + r) := by
  by_cases hqr : q + r = 0
  · exact Or.inl hqr
  rcases hq with rfl | hq
  · simpa using hr
  rcases hr with rfl | hr
  · rw [add_zero]; exact Or.inr hq
  right
  exact (le_min hq hr).trans (padicValRat.min_le_padicValRat_add hqr)

private lemma valGe_sub {p : ℕ} [Fact p.Prime] {k : ℤ} {q r : ℚ}
    (hq : ValGe p k q) (hr : ValGe p k r) : ValGe p k (q - r) := by
  rw [sub_eq_add_neg]
  exact valGe_add hq (valGe_neg hr)

private lemma valGe_mul {p : ℕ} [Fact p.Prime] {k₁ k₂ : ℤ} {q r : ℚ}
    (hq : ValGe p k₁ q) (hr : ValGe p k₂ r) : ValGe p (k₁ + k₂) (q * r) := by
  rcases hq with rfl | hq
  · simp [ValGe]
  rcases hr with rfl | hr
  · simp [ValGe]
  by_cases hq0 : q = 0
  · simp [ValGe, hq0]
  by_cases hr0 : r = 0
  · simp [ValGe, hr0]
  right
  rw [padicValRat.mul hq0 hr0]
  omega

private lemma valGe_pow {p : ℕ} [Fact p.Prime] {k : ℤ} {q : ℚ} (m : ℕ) (hq : ValGe p k q) :
    ValGe p ((m : ℤ) * k) (q ^ m) := by
  induction m with
  | zero =>
    right; simp [padicValRat.one]
  | succ m ih =>
    rw [pow_succ]
    have hm : ((m + 1 : ℕ) : ℤ) * k = (m : ℤ) * k + k := by push_cast; ring
    rw [hm]
    exact valGe_mul ih hq

private lemma valGe_of_nat (p : ℕ) [Fact p.Prime] (n : ℕ) : ValGe p 0 (n : ℚ) := by
  right; rw [padicValRat.of_nat]; exact Nat.cast_nonneg _

private lemma val_add_eq_of_valGe_gt {p : ℕ} [Fact p.Prime] {q r : ℚ}
    (hq : q ≠ 0) (hr : ValGe p (padicValRat p q + 1) r) :
    q + r ≠ 0 ∧ padicValRat p (q + r) = padicValRat p q := by
  rcases hr with rfl | hr
  · simp [hq]
  by_cases hr0 : r = 0
  · simp [hr0, hq]
  have hqr : q + r ≠ 0 := by
    intro h
    have hqeq : q = -r := eq_neg_of_add_eq_zero_left h
    have hv : padicValRat p q = padicValRat p r := by rw [hqeq, padicValRat.neg]
    omega
  refine ⟨hqr, le_antisymm ?_ ?_⟩
  · have hq_eq : q = (q + r) + (-r) := by ring
    have hmin := padicValRat.min_le_padicValRat_add (p := p) (q := q + r) (r := -r)
      (by rwa [← hq_eq])
    rw [← hq_eq, padicValRat.neg] at hmin
    omega
  · have hmin := padicValRat.min_le_padicValRat_add (p := p) hqr
    omega

private lemma val_one_sub_of_valGe_pos {p : ℕ} [Fact p.Prime] {r : ℚ} (hr : ValGe p 1 r) :
    1 - r ≠ 0 ∧ padicValRat p (1 - r) = 0 := by
  rw [sub_eq_add_neg]
  have h := val_add_eq_of_valGe_gt (p := p) (q := (1 : ℚ)) (r := -r) one_ne_zero
    (by rw [padicValRat.one]; simpa using valGe_neg hr)
  simpa [padicValRat.one] using h

private lemma val_one_add_of_valGe_pos {p : ℕ} [Fact p.Prime] {r : ℚ} (hr : ValGe p 1 r) :
    1 + r ≠ 0 ∧ padicValRat p (1 + r) = 0 := by
  have h := val_add_eq_of_valGe_gt (p := p) (q := (1 : ℚ)) (r := r) one_ne_zero
    (by rw [padicValRat.one]; simpa using hr)
  simpa [padicValRat.one] using h

private lemma valGe_div_of_val_zero {p : ℕ} [Fact p.Prime] {k : ℤ} {q r : ℚ}
    (hq : ValGe p k q) (hr0 : r ≠ 0) (hr : padicValRat p r = 0) :
    ValGe p k (q / r) := by
  rcases hq with rfl | hq
  · simp [ValGe]
  by_cases hq0 : q = 0
  · simp [ValGe, hq0]
  right
  rw [padicValRat.div hq0 hr0, hr, sub_zero]
  exact hq

/- ### Part 3: Scaling `E` to a `p`-integral model `E'` with `v_p(a'_i) ≥ 1` -/

private def scaleCurve (E : WeierstrassCurve ℚ) (u : ℚ) : WeierstrassCurve ℚ :=
  ⟨u * E.a₁, u ^ 2 * E.a₂, u ^ 3 * E.a₃, u ^ 4 * E.a₄, u ^ 6 * E.a₆⟩

private lemma scaleCurve_equation (E : WeierstrassCurve ℚ) (u : ℚ) (hu : u ≠ 0) (x y : ℚ) :
    (scaleCurve E u).toAffine.Equation (u ^ 2 * x) (u ^ 3 * y) ↔ E.toAffine.Equation x y := by
  simp only [WeierstrassCurve.Affine.equation_iff, scaleCurve]
  constructor
  · intro h
    have h6 : u ^ 6 ≠ 0 := pow_ne_zero 6 hu
    apply mul_left_cancel₀ h6
    linear_combination h
  · intro h
    linear_combination u ^ 6 * h

private lemma scaleCurve_Δ (E : WeierstrassCurve ℚ) (u : ℚ) :
    (scaleCurve E u).Δ = u ^ 12 * E.Δ := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, scaleCurve]
  ring

private noncomputable def scalePointHom (E : WeierstrassCurve ℚ) (u : ℚ) (hu : u ≠ 0)
    (hΔ : E.Δ ≠ 0) : E.toAffine.Point →+ (scaleCurve E u).toAffine.Point := by
  have hΔ' : (scaleCurve E u).Δ ≠ 0 := by
    rw [scaleCurve_Δ]; exact mul_ne_zero (pow_ne_zero 12 hu) hΔ
  have hns_map : ∀ {x y : ℚ}, E.toAffine.Nonsingular x y →
      (scaleCurve E u).toAffine.Nonsingular (u ^ 2 * x) (u ^ 3 * y) := by
    intro x y h
    exact ((scaleCurve E u).toAffine.equation_iff_nonsingular_of_Δ_ne_zero hΔ').mp
      ((scaleCurve_equation E u hu x y).mpr h.1)
  refine
    { toFun := fun P => match P with
        | 0 => 0
        | WeierstrassCurve.Affine.Point.some x y h =>
            WeierstrassCurve.Affine.Point.some (u ^ 2 * x) (u ^ 3 * y) (hns_map h)
      map_zero' := rfl
      map_add' := ?_ }
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
  · rfl
  · rfl
  · rfl
  · have hnegY : (scaleCurve E u).toAffine.negY (u ^ 2 * x₂) (u ^ 3 * y₂) =
        u ^ 3 * E.toAffine.negY x₂ y₂ := by
      simp only [WeierstrassCurve.Affine.negY, scaleCurve]; ring
    by_cases hxy : x₁ = x₂ ∧ y₁ = E.toAffine.negY x₂ y₂
    · have h1' : u ^ 2 * x₁ = u ^ 2 * x₂ := by rw [hxy.1]
      have h2' : u ^ 3 * y₁ = (scaleCurve E u).toAffine.negY (u ^ 2 * x₂) (u ^ 3 * y₂) := by
        rw [hnegY, hxy.2]
      rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hxy.1 hxy.2,
        WeierstrassCurve.Affine.Point.add_of_Y_eq h1' h2']
    · have hxy' : ¬(u ^ 2 * x₁ = u ^ 2 * x₂ ∧
          u ^ 3 * y₁ = (scaleCurve E u).toAffine.negY (u ^ 2 * x₂) (u ^ 3 * y₂)) := by
        rintro ⟨hx', hy'⟩
        rw [hnegY] at hy'
        exact hxy ⟨mul_left_cancel₀ (pow_ne_zero 2 hu) hx',
          mul_left_cancel₀ (pow_ne_zero 3 hu) hy'⟩
      rw [WeierstrassCurve.Affine.Point.add_some hxy, WeierstrassCurve.Affine.Point.add_some hxy']
      have hslope : (scaleCurve E u).toAffine.slope (u ^ 2 * x₁) (u ^ 2 * x₂)
          (u ^ 3 * y₁) (u ^ 3 * y₂) = u * E.toAffine.slope x₁ x₂ y₁ y₂ := by
        by_cases hx : x₁ = x₂
        · have hy : y₁ ≠ E.toAffine.negY x₂ y₂ := fun h => hxy ⟨hx, h⟩
          have hx' : u ^ 2 * x₁ = u ^ 2 * x₂ := by rw [hx]
          have hy' : u ^ 3 * y₁ ≠ (scaleCurve E u).toAffine.negY (u ^ 2 * x₂) (u ^ 3 * y₂) := by
            rw [hnegY]; exact fun h => hy (mul_left_cancel₀ (pow_ne_zero 3 hu) h)
          rw [WeierstrassCurve.Affine.slope_of_Y_ne hx hy,
            WeierstrassCurve.Affine.slope_of_Y_ne hx' hy']
          simp only [WeierstrassCurve.Affine.negY, scaleCurve]
          field_simp [hu]
        · have hx' : u ^ 2 * x₁ ≠ u ^ 2 * x₂ :=
            fun h => hx (mul_left_cancel₀ (pow_ne_zero 2 hu) h)
          rw [WeierstrassCurve.Affine.slope_of_X_ne hx, WeierstrassCurve.Affine.slope_of_X_ne hx']
          field_simp [hu]
      dsimp only
      congr 1
      · rw [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addX, hslope]
        simp only [scaleCurve]; ring
      · rw [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.addY,
          WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.negY,
          WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negAddY,
          WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addX, hslope]
        simp only [scaleCurve]; ring

/- ### Part 4: Formal-group filtration on a `p`-integral curve with `v_p(a_i) ≥ 1` -/

private structure PIntegralCurve (E : WeierstrassCurve ℚ) (p : ℕ) : Prop where
  a1 : ValGe p 1 E.a₁
  a2 : ValGe p 1 E.a₂
  a3 : ValGe p 1 E.a₃
  a4 : ValGe p 1 E.a₄
  a6 : ValGe p 1 E.a₆

private lemma val_x_y_of_neg {E : WeierstrassCurve ℚ} {p : ℕ} [Fact p.Prime]
    (hE : PIntegralCurve E p) {x y : ℚ} (hEq : E.toAffine.Equation x y)
    (hx0 : x ≠ 0) (hxneg : padicValRat p x < 0) :
    y ≠ 0 ∧ ∃ r : ℕ, 1 ≤ r ∧
      padicValRat p x = -2 * (r : ℤ) ∧ padicValRat p y = -3 * (r : ℤ) := by
  have hEq' : y ^ 2 + E.a₁ * x * y + E.a₃ * y = x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆ := by
    simpa [WeierstrassCurve.Affine.equation_iff] using hEq
  set u := padicValRat p x
  have hx3 : x ^ 3 ≠ 0 := pow_ne_zero 3 hx0
  have hvx3 : padicValRat p (x ^ 3) = 3 * u := by rw [padicValRat.pow x]; ring
  have hrhs_tail : ValGe p (3 * u + 1) (E.a₂ * x ^ 2 + E.a₄ * x + E.a₆) := by
    have h1 : ValGe p (3 * u + 1) (E.a₂ * x ^ 2) := by
      have := valGe_mul hE.a2 (valGe_pow 2 (Or.inr (le_refl u) : ValGe p u x))
      exact valGe_mono (by omega) this
    have h2 : ValGe p (3 * u + 1) (E.a₄ * x) := by
      have := valGe_mul hE.a4 (Or.inr (le_refl u) : ValGe p u x)
      exact valGe_mono (by omega) this
    have h3 : ValGe p (3 * u + 1) E.a₆ := valGe_mono (by omega) hE.a6
    exact valGe_add (valGe_add h1 h2) h3
  have hrhs_val : x ^ 3 + (E.a₂ * x ^ 2 + E.a₄ * x + E.a₆) ≠ 0 ∧
      padicValRat p (x ^ 3 + (E.a₂ * x ^ 2 + E.a₄ * x + E.a₆)) = 3 * u := by
    have := val_add_eq_of_valGe_gt hx3 (by rwa [hvx3])
    rwa [hvx3] at this
  have hlhs_eq : y ^ 2 + E.a₁ * x * y + E.a₃ * y = x ^ 3 + (E.a₂ * x ^ 2 + E.a₄ * x + E.a₆) := by
    linarith [hEq']
  have hy0 : y ≠ 0 := by
    intro hy
    rw [hy] at hlhs_eq
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero] at hlhs_eq
    exact hrhs_val.1 hlhs_eq.symm
  set v := padicValRat p y
  have h2v_eq : 2 * v = 3 * u := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- 2v < 3u implies v < u < 0, so LHS has valuation 2v ≠ 3u
      have hvy2 : padicValRat p (y ^ 2) = 2 * v := by rw [padicValRat.pow y]; ring
      have htail : ValGe p (2 * v + 1) (E.a₁ * x * y + E.a₃ * y) := by
        have h1 : ValGe p (2 * v + 1) (E.a₁ * x * y) := by
          have := valGe_mul (valGe_mul hE.a1 (Or.inr (le_refl u) : ValGe p u x))
            (Or.inr (le_refl v) : ValGe p v y)
          exact valGe_mono (by omega) this
        have h2 : ValGe p (2 * v + 1) (E.a₃ * y) := by
          have := valGe_mul hE.a3 (Or.inr (le_refl v) : ValGe p v y)
          exact valGe_mono (by omega) this
        exact valGe_add h1 h2
      have hlhs_val := val_add_eq_of_valGe_gt (pow_ne_zero 2 hy0) (by rwa [hvy2])
      have heq_add : y ^ 2 + (E.a₁ * x * y + E.a₃ * y) = x ^ 3 + (E.a₂ * x ^ 2 + E.a₄ * x + E.a₆) := by
        linarith [hlhs_eq]
      rw [heq_add, hrhs_val.2, hvy2] at hlhs_val
      omega
    · -- 2v > 3u implies every term of LHS has valuation ≥ 3u + 1
      have h1 : ValGe p (3 * u + 1) (y ^ 2) := by
        right; rw [padicValRat.pow y]; omega
      have h2 : ValGe p (3 * u + 1) (E.a₁ * x * y) := by
        have := valGe_mul (valGe_mul hE.a1 (Or.inr (le_refl u) : ValGe p u x))
          (Or.inr (le_refl v) : ValGe p v y)
        exact valGe_mono (by omega) this
      have h3 : ValGe p (3 * u + 1) (E.a₃ * y) := by
        have := valGe_mul hE.a3 (Or.inr (le_refl v) : ValGe p v y)
        exact valGe_mono (by omega) this
      have hlhs_ge := valGe_add (valGe_add h1 h2) h3
      rw [hlhs_eq] at hlhs_ge
      rcases hlhs_ge with hzero | hge
      · exact hrhs_val.1 hzero
      · rw [hrhs_val.2] at hge; omega
  have hr_pos : 0 < (-u) / 2 := by omega
  refine ⟨hy0, ((-u) / 2).toNat, by omega, by omega, by omega⟩

private def InFilt (E : WeierstrassCurve ℚ) (p r : ℕ) (Q : E.toAffine.Point) : Prop :=
  Q = 0 ∨ ∃ x y h, Q = WeierstrassCurve.Affine.Point.some x y h ∧
    x ≠ 0 ∧ padicValRat p x ≤ -2 * (r : ℤ)

private def param {E : WeierstrassCurve ℚ} : E.toAffine.Point → ℚ
  | 0 => 0
  | WeierstrassCurve.Affine.Point.some x y _ => -x / y

private lemma inFilt_mono {E : WeierstrassCurve ℚ} {p r₁ r₂ : ℕ} (h : r₁ ≤ r₂)
    {Q : E.toAffine.Point} (hQ : InFilt E p r₂ Q) : InFilt E p r₁ Q := by
  rcases hQ with rfl | ⟨x, y, hns, rfl, hx0, hval⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨x, y, hns, rfl, hx0, by omega⟩

private lemma param_val_of_inFilt {E : WeierstrassCurve ℚ} {p : ℕ} [Fact p.Prime]
    (hE : PIntegralCurve E p) {r : ℕ} (hr : 1 ≤ r)
    {x y : ℚ} (hns : E.toAffine.Nonsingular x y)
    (hx0 : x ≠ 0) (hxval : padicValRat p x ≤ -2 * (r : ℤ)) :
    y ≠ 0 ∧ (-x / y) ≠ 0 ∧ (-1 / y) ≠ 0 ∧
      (r : ℤ) ≤ padicValRat p (-x / y) ∧
      padicValRat p x = -2 * padicValRat p (-x / y) ∧
      padicValRat p y = -3 * padicValRat p (-x / y) ∧
      padicValRat p (-1 / y) = 3 * padicValRat p (-x / y) := by
  obtain ⟨hy0, s, hs1, hxs, hys⟩ := val_x_y_of_neg hE hns.1 hx0 (by omega)
  have ht0 : -x / y ≠ 0 := div_ne_zero (neg_ne_zero.mpr hx0) hy0
  have hw0 : -1 / y ≠ 0 := div_ne_zero (by norm_num) hy0
  have hvt : padicValRat p (-x / y) = (s : ℤ) := by
    rw [padicValRat.div (neg_ne_zero.mpr hx0) hy0, padicValRat.neg, hxs, hys]; ring
  have hvw : padicValRat p (-1 / y) = 3 * (s : ℤ) := by
    rw [padicValRat.div (by norm_num) hy0, padicValRat.neg, padicValRat.one, hys]; ring
  refine ⟨hy0, ht0, hw0, by omega, by omega, by omega, by omega⟩

private lemma tw_curve_eq {E : WeierstrassCurve ℚ} {x y : ℚ}
    (hEq : E.toAffine.Equation x y) (hy0 : y ≠ 0) :
    let t := -x / y
    let w := -1 / y
    w = t ^ 3 + E.a₁ * t * w + E.a₂ * t ^ 2 * w + E.a₃ * w ^ 2 +
      E.a₄ * t * w ^ 2 + E.a₆ * w ^ 3 := by
  have hEq' : y ^ 2 + E.a₁ * x * y + E.a₃ * y = x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆ := by
    simpa [WeierstrassCurve.Affine.equation_iff] using hEq
  dsimp only
  field_simp [hy0]
  linear_combination -hEq'

private lemma neg_inFilt_and_param {E : WeierstrassCurve ℚ} {p : ℕ} [Fact p.Prime]
    (hE : PIntegralCurve E p) {r : ℕ} (hr : 1 ≤ r) {Q : E.toAffine.Point}
    (hQ : InFilt E p r Q) :
    InFilt E p r (-Q) ∧ ValGe p (2 * (r : ℤ) + 1) (param (-Q) + param Q) := by
  rcases hQ with rfl | ⟨x, y, hns, rfl, hx0, hxval⟩
  · exact ⟨Or.inl WeierstrassCurve.Affine.Point.neg_zero, by simp [param, ValGe]⟩
  obtain ⟨hy0, ht0, hw0, hvt_ge, _, _, hvw⟩ := param_val_of_inFilt hE hr hns hx0 hxval
  set t := -x / y
  set w := -1 / y
  have hvt : ValGe p (r : ℤ) t := Or.inr hvt_ge
  have hvw' : ValGe p (3 * (r : ℤ)) w := Or.inr (by omega)
  set U := 1 - E.a₁ * t - E.a₃ * w
  have hU_tail : ValGe p (1 + (r : ℤ)) (E.a₁ * t + E.a₃ * w) :=
    valGe_add (valGe_mul hE.a1 hvt) (valGe_mono (by omega) (valGe_mul hE.a3 hvw'))
  have hU_val : U ≠ 0 ∧ padicValRat p U = 0 := by
    have hUeq : U = 1 - (E.a₁ * t + E.a₃ * w) := by dsimp only [U]; ring
    rw [hUeq]
    exact val_one_sub_of_valGe_pos (valGe_mono (by omega) hU_tail)
  have hnegY : E.toAffine.negY x y = U / w := by
    dsimp only [U, t, w]
    rw [WeierstrassCurve.Affine.negY]
    field_simp [hy0]
    ring
  have hsum : param (-WeierstrassCurve.Affine.Point.some x y hns) +
      param (WeierstrassCurve.Affine.Point.some x y hns) =
      t * (-(E.a₁ * t + E.a₃ * w)) / U := by
    rw [WeierstrassCurve.Affine.Point.neg_some]
    change -x / E.toAffine.negY x y + (-x / y) = _
    have hx_eq : x = t / w := by dsimp only [t, w]; field_simp [hy0]
    have hsecond : -x / y = t := rfl
    rw [hsecond, hnegY, hx_eq]
    field_simp [hw0, hU_val.1]
    dsimp only [U]
    ring
  refine ⟨Or.inr ⟨x, E.toAffine.negY x y, _, WeierstrassCurve.Affine.Point.neg_some hns, hx0, hxval⟩, ?_⟩
  rw [hsum]
  exact valGe_div_of_val_zero
    (valGe_mono (by omega) (valGe_mul hvt (valGe_neg hU_tail))) hU_val.1 hU_val.2

private lemma cubic_vieta_identities {a₁ a₂ a₃ a₄ a₆ t₁ t₂ w₁ w₂ lam nu : ℚ}
    (h1 : w₁ = t₁ ^ 3 + a₁ * t₁ * w₁ + a₂ * t₁ ^ 2 * w₁ + a₃ * w₁ ^ 2 + a₄ * t₁ * w₁ ^ 2 + a₆ * w₁ ^ 3)
    (h2 : w₂ = t₂ ^ 3 + a₁ * t₂ * w₂ + a₂ * t₂ ^ 2 * w₂ + a₃ * w₂ ^ 2 + a₄ * t₂ * w₂ ^ 2 + a₆ * w₂ ^ 3)
    (hl1 : w₁ = lam * t₁ + nu) (hl2 : w₂ = lam * t₂ + nu)
    (htan : t₁ = t₂ →
      lam * (1 - a₁ * t₁ - a₂ * t₁ ^ 2 - 2 * a₃ * w₁ - 2 * a₄ * t₁ * w₁ - 3 * a₆ * w₁ ^ 2) =
        3 * t₁ ^ 2 + a₁ * w₁ + 2 * a₂ * t₁ * w₁ + a₄ * w₁ ^ 2)
    (hc3 : 1 + a₂ * lam + a₄ * lam ^ 2 + a₆ * lam ^ 3 ≠ 0) :
    let c3 := 1 + a₂ * lam + a₄ * lam ^ 2 + a₆ * lam ^ 3
    let c2 := a₁ * lam + a₂ * nu + a₃ * lam ^ 2 + 2 * a₄ * lam * nu + 3 * a₆ * lam ^ 2 * nu
    let c1 := a₁ * nu + 2 * a₃ * lam * nu + a₄ * nu ^ 2 + 3 * a₆ * lam * nu ^ 2 - lam
    let c0 := a₃ * nu ^ 2 + a₆ * nu ^ 3 - nu
    let t₃ := -t₁ - t₂ - c2 / c3
    let w₃ := lam * t₃ + nu
    c1 = c3 * (t₁ * t₂ + t₂ * t₃ + t₃ * t₁) ∧
    c0 = -c3 * (t₁ * t₂ * t₃) ∧
    w₃ = t₃ ^ 3 + a₁ * t₃ * w₃ + a₂ * t₃ ^ 2 * w₃ + a₃ * w₃ ^ 2 + a₄ * t₃ * w₃ ^ 2 + a₆ * w₃ ^ 3 ∧
    nu ^ 3 = c3 * w₁ * w₂ * w₃ ∧
    -(nu * lam ^ 2 + a₁ * nu ^ 2 * lam - a₂ * nu ^ 3) =
      -c3 * (t₁ * w₂ * w₃ + w₁ * t₂ * w₃ + w₁ * w₂ * t₃) := by
  intro c3 c2 c1 c0 t₃ w₃
  have hc3' : c3 ≠ 0 := hc3
  have hc2 : c2 = -c3 * (t₁ + t₂ + t₃) := by
    dsimp only [t₃]; field_simp [hc3']; ring
  -- Evaluate the cubic P(t) = c3 t^3 + c2 t^2 + c1 t + c0 at t₁ and t₂
  have hP1 : c3 * t₁ ^ 3 + c2 * t₁ ^ 2 + c1 * t₁ + c0 = 0 := by
    dsimp only [c3, c2, c1, c0]
    have hnu1 : nu = w₁ - lam * t₁ := by linarith [hl1]
    rw [hnu1]
    linear_combination -h1
  have hP2 : c3 * t₂ ^ 3 + c2 * t₂ ^ 2 + c1 * t₂ + c0 = 0 := by
    dsimp only [c3, c2, c1, c0]
    have hnu2 : nu = w₂ - lam * t₂ := by linarith [hl2]
    rw [hnu2]
    linear_combination -h2
  have hc1_c0 : c1 = c3 * (t₁ * t₂ + t₂ * t₃ + t₃ * t₁) ∧ c0 = -c3 * (t₁ * t₂ * t₃) := by
    by_cases hteq : t₁ = t₂
    · have htan' := htan hteq
      have hP'1 : 3 * c3 * t₁ ^ 2 + 2 * c2 * t₁ + c1 = 0 := by
        dsimp only [c3, c2, c1]
        have hnu1 : nu = w₁ - lam * t₁ := by linarith [hl1]
        rw [hnu1]
        linear_combination -htan'
      have hc1 : c1 = c3 * (t₁ * t₂ + t₂ * t₃ + t₃ * t₁) := by
        subst hteq
        linear_combination hP'1 - 2 * t₁ * hc2
      have hc0 : c0 = -c3 * (t₁ * t₂ * t₃) := by
        subst hteq
        linear_combination hP1 - t₁ ^ 2 * hc2 - t₁ * hc1
      exact ⟨hc1, hc0⟩
    · have hsub : (t₁ - t₂) * (c1 - c3 * (t₁ * t₂ + t₂ * t₃ + t₃ * t₁)) = 0 := by
        linear_combination (hP1 - hP2) - (t₁ ^ 2 - t₂ ^ 2) * hc2
      have hc1 : c1 = c3 * (t₁ * t₂ + t₂ * t₃ + t₃ * t₁) :=
        sub_eq_zero.mp ((mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hteq))
      have hc0 : c0 = -c3 * (t₁ * t₂ * t₃) := by
        linear_combination hP1 - t₁ ^ 2 * hc2 - t₁ * hc1
      exact ⟨hc1, hc0⟩
  rcases hc1_c0 with ⟨hc1, hc0⟩
  refine ⟨hc1, hc0, ?_, ?_, ?_⟩
  · have hP3 : c3 * t₃ ^ 3 + c2 * t₃ ^ 2 + c1 * t₃ + c0 = 0 := by
      linear_combination t₃ ^ 2 * hc2 + t₃ * hc1 + hc0
    dsimp only [c3, c2, c1, c0, w₃] at hP3 ⊢
    linear_combination -hP3
  · have hlhs : c3 * nu ^ 3 - c2 * nu ^ 2 * lam + c1 * nu * lam ^ 2 - c0 * lam ^ 3 = nu ^ 3 := by
      dsimp only [c3, c2, c1, c0]; ring
    have hrhs : c3 * nu ^ 3 - c2 * nu ^ 2 * lam + c1 * nu * lam ^ 2 - c0 * lam ^ 3 =
        c3 * w₁ * w₂ * w₃ := by
      rw [hl1, hl2]
      dsimp only [w₃]
      linear_combination -nu ^ 2 * lam * hc2 + nu * lam ^ 2 * hc1 - lam ^ 3 * hc0
    exact hlhs.symm.trans hrhs
  · have hlhs : c2 * nu ^ 2 - 2 * c1 * nu * lam + 3 * c0 * lam ^ 2 =
        -(nu * lam ^ 2 + a₁ * nu ^ 2 * lam - a₂ * nu ^ 3) := by
      dsimp only [c2, c1, c0]; ring
    have hrhs : c2 * nu ^ 2 - 2 * c1 * nu * lam + 3 * c0 * lam ^ 2 =
        -c3 * (t₁ * w₂ * w₃ + w₁ * t₂ * w₃ + w₁ * w₂ * t₃) := by
      rw [hl1, hl2]
      dsimp only [w₃]
      linear_combination nu ^ 2 * hc2 - 2 * nu * lam * hc1 + 3 * lam ^ 2 * hc0
    exact hlhs.symm.trans hrhs

private lemma add_inFilt_finish {E : WeierstrassCurve ℚ} {p : ℕ} [Fact p.Prime]
    (hE : PIntegralCurve E p) {r : ℕ} (hr : 1 ≤ r)
    {x₁ y₁ x₂ y₂ t₁ w₁ t₂ w₂ lam nu c3 c2 t₃ w₃ : ℚ}
    (hns₁ : E.toAffine.Nonsingular x₁ y₁) (hns₂ : E.toAffine.Nonsingular x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = E.toAffine.negY x₂ y₂))
    (ht₁_def : t₁ = -x₁ / y₁) (hw₁_def : w₁ = -1 / y₁)
    (ht₂_def : t₂ = -x₂ / y₂) (hw₂_def : w₂ = -1 / y₂)
    (hy₁0 : y₁ ≠ 0) (hy₂0 : y₂ ≠ 0) (hw₁0 : w₁ ≠ 0) (hw₂0 : w₂ ≠ 0)
    (hvt₁ : ValGe p (r : ℤ) t₁) (hvt₂ : ValGe p (r : ℤ) t₂)
    (hlam_ge : ValGe p (2 * (r : ℤ)) lam) (hnu_ge : ValGe p (3 * (r : ℤ)) nu)
    (hnu_ne : nu ≠ 0) (hslope : E.toAffine.slope x₁ x₂ y₁ y₂ = lam / nu)
    (hc3_val : c3 ≠ 0 ∧ padicValRat p c3 = 0)
    (hc2_ge : ValGe p (2 * (r : ℤ) + 1) c2)
    (ht₃_def : t₃ = -t₁ - t₂ - c2 / c3) (hw₃_def : w₃ = lam * t₃ + nu)
    (hl1 : w₁ = lam * t₁ + nu)
    (heq3 : w₃ = t₃ ^ 3 + E.a₁ * t₃ * w₃ + E.a₂ * t₃ ^ 2 * w₃ +
      E.a₃ * w₃ ^ 2 + E.a₄ * t₃ * w₃ ^ 2 + E.a₆ * w₃ ^ 3)
    (hnu3 : nu ^ 3 = c3 * w₁ * w₂ * w₃)
    (hsumx : -(nu * lam ^ 2 + E.a₁ * nu ^ 2 * lam - E.a₂ * nu ^ 3) =
      -c3 * (t₁ * w₂ * w₃ + w₁ * t₂ * w₃ + w₁ * w₂ * t₃)) :
    InFilt E p r (WeierstrassCurve.Affine.Point.some x₁ y₁ hns₁ +
        WeierstrassCurve.Affine.Point.some x₂ y₂ hns₂) ∧
      ValGe p (2 * (r : ℤ) + 1)
        (param (WeierstrassCurve.Affine.Point.some x₁ y₁ hns₁ +
            WeierstrassCurve.Affine.Point.some x₂ y₂ hns₂) -
          (param (WeierstrassCurve.Affine.Point.some x₁ y₁ hns₁) +
            param (WeierstrassCurve.Affine.Point.some x₂ y₂ hns₂))) := by
  have hw₃_ne : w₃ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hnu3
    exact pow_ne_zero 3 hnu_ne hnu3
  have hvt₃_ge : ValGe p (r : ℤ) t₃ := by
    rw [ht₃_def]
    have hdiv : ValGe p (2 * (r : ℤ) + 1) (c2 / c3) :=
      valGe_div_of_val_zero hc2_ge hc3_val.1 hc3_val.2
    exact valGe_sub (valGe_sub (valGe_neg hvt₁) hvt₂) (valGe_mono (by omega) hdiv)
  have hvw₃_ge : ValGe p (3 * (r : ℤ)) w₃ := by
    rw [hw₃_def]
    exact valGe_add (valGe_mono (by omega) (valGe_mul hlam_ge hvt₃_ge)) hnu_ge
  let D3 := 1 - E.a₁ * t₃ - E.a₂ * t₃ ^ 2 - E.a₃ * w₃ - E.a₄ * t₃ * w₃ - E.a₆ * w₃ ^ 2
  have hD3_val : D3 ≠ 0 ∧ padicValRat p D3 = 0 := by
    have hD3_eq : D3 = 1 - (E.a₁ * t₃ + E.a₂ * t₃ ^ 2 + E.a₃ * w₃ + E.a₄ * t₃ * w₃ + E.a₆ * w₃ ^ 2) := by
      dsimp only [D3]; ring
    rw [hD3_eq]
    apply val_one_sub_of_valGe_pos
    have g1 : ValGe p 1 (E.a₁ * t₃) := valGe_mono (by omega) (valGe_mul hE.a1 hvt₃_ge)
    have g2 : ValGe p 1 (E.a₂ * t₃ ^ 2) := valGe_mono (by omega) (valGe_mul hE.a2 (valGe_pow 2 hvt₃_ge))
    have g3 : ValGe p 1 (E.a₃ * w₃) := valGe_mono (by omega) (valGe_mul hE.a3 hvw₃_ge)
    have g4 : ValGe p 1 (E.a₄ * t₃ * w₃) :=
      valGe_mono (by omega) (valGe_mul (valGe_mul hE.a4 hvt₃_ge) hvw₃_ge)
    have g5 : ValGe p 1 (E.a₆ * w₃ ^ 2) :=
      valGe_mono (by omega) (valGe_mul hE.a6 (valGe_pow 2 hvw₃_ge))
    exact valGe_add (valGe_add (valGe_add (valGe_add g1 g2) g3) g4) g5
  have hw₃D3 : w₃ * D3 = t₃ ^ 3 := by dsimp only [D3]; linear_combination heq3
  have ht₃_ne : t₃ ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by decide)] at hw₃D3
    exact mul_ne_zero hw₃_ne hD3_val.1 hw₃D3
  have hvw₃_eq : padicValRat p w₃ = 3 * padicValRat p t₃ := by
    have h1 := congrArg (padicValRat p) hw₃D3
    rw [padicValRat.mul hw₃_ne hD3_val.1, hD3_val.2, add_zero, padicValRat.pow t₃] at h1
    norm_num at h1
    exact h1
  have hvt₃_int : (r : ℤ) ≤ padicValRat p t₃ := hvt₃_ge.resolve_left ht₃_ne
  let L := E.toAffine.slope x₁ x₂ y₁ y₂
  have hx1 : x₁ = t₁ / w₁ := by rw [ht₁_def, hw₁_def]; field_simp [hy₁0]
  have hx2 : x₂ = t₂ / w₂ := by rw [ht₂_def, hw₂_def]; field_simp [hy₂0]
  have hy1 : y₁ = -1 / w₁ := by rw [hw₁_def]; field_simp [hy₁0]
  have haddX : E.toAffine.addX x₁ x₂ L = t₃ / w₃ := by
    simp only [WeierstrassCurve.Affine.addX, L, hslope]
    rw [hx1, hx2]
    have hc3w_ne : c3 * w₁ * w₂ * w₃ ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero hc3_val.1 hw₁0) hw₂0) hw₃_ne
    have h1 : (lam / nu) ^ 2 + E.a₁ * (lam / nu) - E.a₂ = t₁ / w₁ + t₂ / w₂ + t₃ / w₃ := by
      have h2 : nu ^ 3 * ((lam / nu) ^ 2 + E.a₁ * (lam / nu) - E.a₂) =
          c3 * w₁ * w₂ * w₃ * (t₁ / w₁ + t₂ / w₂ + t₃ / w₃) := by
        have hl : nu ^ 3 * ((lam / nu) ^ 2 + E.a₁ * (lam / nu) - E.a₂) =
            nu * lam ^ 2 + E.a₁ * nu ^ 2 * lam - E.a₂ * nu ^ 3 := by
          field_simp [hnu_ne]
        have hr' : c3 * w₁ * w₂ * w₃ * (t₁ / w₁ + t₂ / w₂ + t₃ / w₃) =
            c3 * (t₁ * w₂ * w₃ + w₁ * t₂ * w₃ + w₁ * w₂ * t₃) := by
          field_simp [hw₁0, hw₂0, hw₃_ne]
        rw [hl, hr']
        linear_combination -hsumx
      rw [hnu3] at h2
      exact mul_left_cancel₀ hc3w_ne h2
    linarith
  have hnegAddY : E.toAffine.negAddY x₁ x₂ y₁ L = -1 / w₃ := by
    rw [WeierstrassCurve.Affine.negAddY, haddX, hx1, hy1]
    dsimp only [L]
    rw [hslope]
    field_simp [hnu_ne, hw₁0, hw₃_ne]
    rw [hl1, hw₃_def]
    ring
  let U3 := 1 - E.a₁ * t₃ - E.a₃ * w₃
  have hU3_tail : ValGe p (1 + (r : ℤ)) (E.a₁ * t₃ + E.a₃ * w₃) :=
    valGe_add (valGe_mul hE.a1 hvt₃_ge) (valGe_mono (by omega) (valGe_mul hE.a3 hvw₃_ge))
  have hU3_val : U3 ≠ 0 ∧ padicValRat p U3 = 0 := by
    have hU3_eq : U3 = 1 - (E.a₁ * t₃ + E.a₃ * w₃) := by dsimp only [U3]; ring
    rw [hU3_eq]
    exact val_one_sub_of_valGe_pos (valGe_mono (by omega) hU3_tail)
  have haddY : E.toAffine.addY x₁ x₂ y₁ L = U3 / w₃ := by
    rw [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY, haddX, hnegAddY]
    dsimp only [U3]
    field_simp [hw₃_ne]
  rw [WeierstrassCurve.Affine.Point.add_some hxy]
  have hx3_ne : E.toAffine.addX x₁ x₂ L ≠ 0 := by
    rw [haddX]; exact div_ne_zero ht₃_ne hw₃_ne
  have hx3_val : padicValRat p (E.toAffine.addX x₁ x₂ L) ≤ -2 * (r : ℤ) := by
    rw [haddX, padicValRat.div ht₃_ne hw₃_ne, hvw₃_eq]; omega
  refine ⟨Or.inr ⟨_, _, _, rfl, hx3_ne, hx3_val⟩, ?_⟩
  have hparam_diff : param (WeierstrassCurve.Affine.Point.some _ _
      (WeierstrassCurve.Affine.nonsingular_add hns₁ hns₂ hxy)) -
      (param (WeierstrassCurve.Affine.Point.some x₁ y₁ hns₁) +
        param (WeierstrassCurve.Affine.Point.some x₂ y₂ hns₂)) =
      (c2 / c3 + (t₁ + t₂) * (E.a₁ * t₃ + E.a₃ * w₃)) / U3 := by
    change -(E.toAffine.addX x₁ x₂ L) / (E.toAffine.addY x₁ x₂ y₁ L) - (-x₁ / y₁ + -x₂ / y₂) = _
    rw [← ht₁_def, ← ht₂_def, haddX, haddY]
    field_simp [hw₃_ne, hU3_val.1]
    dsimp only [U3]
    have ht3' : t₃ + t₁ + t₂ = -(c2 / c3) := by linarith [ht₃_def]
    field_simp [hc3_val.1] at ht3' ⊢
    linear_combination -ht3'
  rw [hparam_diff]
  exact valGe_div_of_val_zero
    (valGe_add (valGe_div_of_val_zero hc2_ge hc3_val.1 hc3_val.2)
      (valGe_mono (by omega) (valGe_mul (valGe_add hvt₁ hvt₂) hU3_tail)))
    hU3_val.1 hU3_val.2

private lemma add_inFilt_and_param {E : WeierstrassCurve ℚ} {p : ℕ} [Fact p.Prime]
    (hE : PIntegralCurve E p) {r : ℕ} (hr : 1 ≤ r) {Q₁ Q₂ : E.toAffine.Point}
    (hQ₁ : InFilt E p r Q₁) (hQ₂ : InFilt E p r Q₂) :
    InFilt E p r (Q₁ + Q₂) ∧
      ValGe p (2 * (r : ℤ) + 1) (param (Q₁ + Q₂) - (param Q₁ + param Q₂)) := by
  rcases hQ₁ with rfl | ⟨x₁, y₁, hns₁, rfl, hx₁0, hx₁val⟩
  · refine ⟨by simpa using hQ₂, ?_⟩
    simp [param, ValGe]
  rcases hQ₂ with rfl | ⟨x₂, y₂, hns₂, rfl, hx₂0, hx₂val⟩
  · refine ⟨by rw [add_zero]; exact Or.inr ⟨x₁, y₁, hns₁, rfl, hx₁0, hx₁val⟩, ?_⟩
    simp [param, ValGe]
  by_cases hxy : x₁ = x₂ ∧ y₁ = E.toAffine.negY x₂ y₂
  · rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hxy.1 hxy.2]
    refine ⟨Or.inl rfl, ?_⟩
    have hP1 : WeierstrassCurve.Affine.Point.some x₁ y₁ hns₁ =
        -WeierstrassCurve.Affine.Point.some x₂ y₂ hns₂ := by
      rw [WeierstrassCurve.Affine.Point.neg_some]
      congr 1
      exact hxy.1
      exact hxy.2
    rw [hP1]
    have hneg := (neg_inFilt_and_param hE hr (Or.inr ⟨x₂, y₂, hns₂, rfl, hx₂0, hx₂val⟩)).2
    have h0 : param (0 : E.toAffine.Point) = 0 := rfl
    rw [h0, zero_sub]
    exact valGe_neg hneg
  · -- Non-cancelling addition of two points in E'_r
    obtain ⟨hy₁0, ht₁0, hw₁0, hvt₁_ge, _, _, hvw₁⟩ := param_val_of_inFilt hE hr hns₁ hx₁0 hx₁val
    obtain ⟨hy₂0, ht₂0, hw₂0, hvt₂_ge, _, _, hvw₂⟩ := param_val_of_inFilt hE hr hns₂ hx₂0 hx₂val
    set t₁ := -x₁ / y₁
    set w₁ := -1 / y₁
    set t₂ := -x₂ / y₂
    set w₂ := -1 / y₂
    have hvt₁ : ValGe p (r : ℤ) t₁ := Or.inr hvt₁_ge
    have hvt₂ : ValGe p (r : ℤ) t₂ := Or.inr hvt₂_ge
    have hvw₁' : ValGe p (3 * (r : ℤ)) w₁ := Or.inr (by omega)
    have hvw₂' : ValGe p (3 * (r : ℤ)) w₂ := Or.inr (by omega)
    have heq1 : w₁ = t₁ ^ 3 + E.a₁ * t₁ * w₁ + E.a₂ * t₁ ^ 2 * w₁ + E.a₃ * w₁ ^ 2 +
        E.a₄ * t₁ * w₁ ^ 2 + E.a₆ * w₁ ^ 3 := tw_curve_eq hns₁.1 hy₁0
    have heq2 : w₂ = t₂ ^ 3 + E.a₁ * t₂ * w₂ + E.a₂ * t₂ ^ 2 * w₂ + E.a₃ * w₂ ^ 2 +
        E.a₄ * t₂ * w₂ ^ 2 + E.a₆ * w₂ ^ 3 := tw_curve_eq hns₂.1 hy₂0
    set A := 1 - E.a₁ * t₂ - E.a₂ * t₂ ^ 2 - E.a₃ * (w₁ + w₂) -
      E.a₄ * t₂ * (w₁ + w₂) - E.a₆ * (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2)
    set B := t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2 + E.a₁ * w₁ + E.a₂ * (t₁ + t₂) * w₁ + E.a₄ * w₁ ^ 2
    have hAB : (w₂ - w₁) * A = (t₂ - t₁) * B := by
      dsimp only [A, B]
      linear_combination heq2 - heq1
    have hA_val : A ≠ 0 ∧ padicValRat p A = 0 := by
      have hA_eq : A = 1 - (E.a₁ * t₂ + E.a₂ * t₂ ^ 2 + E.a₃ * (w₁ + w₂) +
          E.a₄ * t₂ * (w₁ + w₂) + E.a₆ * (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2)) := by
        dsimp only [A]; ring
      rw [hA_eq]
      apply val_one_sub_of_valGe_pos
      have g1 : ValGe p 1 (E.a₁ * t₂) := valGe_mono (by omega) (valGe_mul hE.a1 hvt₂)
      have g2 : ValGe p 1 (E.a₂ * t₂ ^ 2) := valGe_mono (by omega) (valGe_mul hE.a2 (valGe_pow 2 hvt₂))
      have hw12 : ValGe p (3 * (r : ℤ)) (w₁ + w₂) := valGe_add hvw₁' hvw₂'
      have g3 : ValGe p 1 (E.a₃ * (w₁ + w₂)) := valGe_mono (by omega) (valGe_mul hE.a3 hw12)
      have g4 : ValGe p 1 (E.a₄ * t₂ * (w₁ + w₂)) :=
        valGe_mono (by omega) (valGe_mul (valGe_mul hE.a4 hvt₂) hw12)
      have hwsq : ValGe p (6 * (r : ℤ)) (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2) :=
        valGe_add (valGe_add (valGe_mono (by omega) (valGe_pow 2 hvw₁'))
          (valGe_mono (by omega) (valGe_mul hvw₁' hvw₂')))
          (valGe_mono (by omega) (valGe_pow 2 hvw₂'))
      have g5 : ValGe p 1 (E.a₆ * (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2)) :=
        valGe_mono (by omega) (valGe_mul hE.a6 hwsq)
      exact valGe_add (valGe_add (valGe_add (valGe_add g1 g2) g3) g4) g5
    have hB_ge : ValGe p (2 * (r : ℤ)) B := by
      have g1 : ValGe p (2 * (r : ℤ)) (t₁ ^ 2) := valGe_mono (by omega) (valGe_pow 2 hvt₁)
      have g2 : ValGe p (2 * (r : ℤ)) (t₁ * t₂) := valGe_mono (by omega) (valGe_mul hvt₁ hvt₂)
      have g3 : ValGe p (2 * (r : ℤ)) (t₂ ^ 2) := valGe_mono (by omega) (valGe_pow 2 hvt₂)
      have g4 : ValGe p (2 * (r : ℤ)) (E.a₁ * w₁) := valGe_mono (by omega) (valGe_mul hE.a1 hvw₁')
      have g5 : ValGe p (2 * (r : ℤ)) (E.a₂ * (t₁ + t₂) * w₁) :=
        valGe_mono (by omega) (valGe_mul (valGe_mul hE.a2 (valGe_add hvt₁ hvt₂)) hvw₁')
      have g6 : ValGe p (2 * (r : ℤ)) (E.a₄ * w₁ ^ 2) :=
        valGe_mono (by omega) (valGe_mul hE.a4 (valGe_pow 2 hvw₁'))
      exact valGe_add (valGe_add (valGe_add (valGe_add (valGe_add g1 g2) g3) g4) g5) g6
    set lam := B / A
    set nu := w₁ - lam * t₁
    have hlam_ge : ValGe p (2 * (r : ℤ)) lam := valGe_div_of_val_zero hB_ge hA_val.1 hA_val.2
    have hnu_ge : ValGe p (3 * (r : ℤ)) nu :=
      valGe_sub hvw₁' (valGe_mono (by omega) (valGe_mul hlam_ge hvt₁))
    have hl1 : w₁ = lam * t₁ + nu := by dsimp only [nu]; ring
    have hl2 : w₂ = lam * t₂ + nu := by
      have hdiff : w₂ - w₁ = lam * (t₂ - t₁) := by
        dsimp only [lam]; field_simp [hA_val.1]; linear_combination hAB
      linarith [hl1, hdiff]
    have htan : t₁ = t₂ →
        lam * (1 - E.a₁ * t₁ - E.a₂ * t₁ ^ 2 - 2 * E.a₃ * w₁ - 2 * E.a₄ * t₁ * w₁ - 3 * E.a₆ * w₁ ^ 2) =
          3 * t₁ ^ 2 + E.a₁ * w₁ + 2 * E.a₂ * t₁ * w₁ + E.a₄ * w₁ ^ 2 := by
      intro hteq
      have hweq : w₁ = w₂ := by
        have h0 : (w₂ - w₁) * A = 0 := by rw [hAB, hteq, sub_self, zero_mul]
        linarith [(mul_eq_zero.mp h0).resolve_right hA_val.1]
      dsimp only [lam]
      have hA_eq : A = 1 - E.a₁ * t₁ - E.a₂ * t₁ ^ 2 - 2 * E.a₃ * w₁ -
          2 * E.a₄ * t₁ * w₁ - 3 * E.a₆ * w₁ ^ 2 := by
        dsimp only [A]; rw [← hteq, ← hweq]; ring
      have hB_eq : B = 3 * t₁ ^ 2 + E.a₁ * w₁ + 2 * E.a₂ * t₁ * w₁ + E.a₄ * w₁ ^ 2 := by
        dsimp only [B]; rw [← hteq]; ring
      rw [← hA_eq, ← hB_eq, div_mul_cancel₀ _ hA_val.1]
    -- Show nu ≠ 0 and slope = lam / nu
    have hnu_ne_and_slope : nu ≠ 0 ∧ E.toAffine.slope x₁ x₂ y₁ y₂ = lam / nu := by
      by_cases hx : x₁ = x₂
      · have hy : y₁ ≠ E.toAffine.negY x₂ y₂ := fun h => hxy ⟨hx, h⟩
        have hy12 : y₁ = y₂ := WeierstrassCurve.Affine.Y_eq_of_Y_ne hns₁.1 hns₂.1 hx hy
        have hteq : t₁ = t₂ := by dsimp only [t₁, t₂]; rw [hx, hy12]
        have hweq : w₁ = w₂ := by dsimp only [w₁, w₂]; rw [hy12]
        have hA_eq : A = 1 - E.a₁ * t₁ - E.a₂ * t₁ ^ 2 - 2 * E.a₃ * w₁ -
            2 * E.a₄ * t₁ * w₁ - 3 * E.a₆ * w₁ ^ 2 := by
          dsimp only [A]; rw [← hteq, ← hweq]; ring
        have hB_eq : B = 3 * t₁ ^ 2 + E.a₁ * w₁ + 2 * E.a₂ * t₁ * w₁ + E.a₄ * w₁ ^ 2 := by
          dsimp only [B]; rw [← hteq]; ring
        have hnu_id : nu * A = w₁ ^ 2 * (y₁ - E.toAffine.negY x₁ y₁) := by
          have hnuA : nu * A = w₁ * A - t₁ * B := by
            dsimp only [nu, lam]; field_simp [hA_val.1]
          rw [hnuA, hA_eq, hB_eq, WeierstrassCurve.Affine.negY]
          dsimp only [t₁, w₁]
          have hEq1' : y₁ ^ 2 + E.a₁ * x₁ * y₁ + E.a₃ * y₁ =
              x₁ ^ 3 + E.a₂ * x₁ ^ 2 + E.a₄ * x₁ + E.a₆ := by
            simpa [WeierstrassCurve.Affine.equation_iff] using hns₁.1
          field_simp [hy₁0]
          linear_combination -3 * hEq1'
        have hyneneg1 : y₁ - E.toAffine.negY x₁ y₁ ≠ 0 := by
          rw [← hx, ← hy12] at hy
          exact sub_ne_zero.mpr hy
        have hnu_ne : nu ≠ 0 := by
          intro h0
          rw [h0, zero_mul] at hnu_id
          exact mul_ne_zero (pow_ne_zero 2 hw₁0) hyneneg1 hnu_id.symm
        refine ⟨hnu_ne, ?_⟩
        rw [WeierstrassCurve.Affine.slope_of_Y_ne hx hy]
        have hB_xy : B = w₁ ^ 2 * (3 * x₁ ^ 2 + 2 * E.a₂ * x₁ + E.a₄ - E.a₁ * y₁) := by
          rw [hB_eq]; dsimp only [t₁, w₁]; field_simp [hy₁0]; ring
        dsimp only [lam]
        have : B / A / nu = B / (nu * A) := by ring
        rw [this, hnu_id, hB_xy]
        field_simp [hw₁0, hyneneg1]
      · have hx1 : x₁ = t₁ / w₁ := by dsimp only [t₁, w₁]; field_simp [hy₁0]
        have hx2 : x₂ = t₂ / w₂ := by dsimp only [t₂, w₂]; field_simp [hy₂0]
        have hy1 : y₁ = -1 / w₁ := by dsimp only [w₁]; field_simp [hy₁0]
        have hy2 : y₂ = -1 / w₂ := by dsimp only [w₂]; field_simp [hy₂0]
        have hdx : x₁ - x₂ = nu * (t₁ - t₂) / (w₁ * w₂) := by
          rw [hx1, hx2]
          field_simp [hw₁0, hw₂0]
          rw [hl1, hl2]
          ring
        have hdy : y₁ - y₂ = lam * (t₁ - t₂) / (w₁ * w₂) := by
          rw [hy1, hy2]
          field_simp [hw₁0, hw₂0]
          rw [hl1, hl2]
          ring
        have hnu_ne : nu ≠ 0 := by
          intro h0
          rw [h0, zero_mul, zero_div] at hdx
          exact sub_ne_zero.mpr hx hdx
        have ht_ne : t₁ - t₂ ≠ 0 := by
          intro h0
          rw [h0, mul_zero, zero_div] at hdx
          exact sub_ne_zero.mpr hx hdx
        refine ⟨hnu_ne, ?_⟩
        rw [WeierstrassCurve.Affine.slope_of_X_ne hx, hdx, hdy]
        field_simp [hw₁0, hw₂0, hnu_ne, ht_ne]
    rcases hnu_ne_and_slope with ⟨hnu_ne, hslope⟩
    set c3 := 1 + E.a₂ * lam + E.a₄ * lam ^ 2 + E.a₆ * lam ^ 3
    set c2 := E.a₁ * lam + E.a₂ * nu + E.a₃ * lam ^ 2 + 2 * E.a₄ * lam * nu + 3 * E.a₆ * lam ^ 2 * nu
    have hc3_val : c3 ≠ 0 ∧ padicValRat p c3 = 0 := by
      have hc3_eq : c3 = 1 + (E.a₂ * lam + E.a₄ * lam ^ 2 + E.a₆ * lam ^ 3) := by
        dsimp only [c3]; ring
      rw [hc3_eq]
      apply val_one_add_of_valGe_pos
      have g1 : ValGe p 1 (E.a₂ * lam) := valGe_mono (by omega) (valGe_mul hE.a2 hlam_ge)
      have g2 : ValGe p 1 (E.a₄ * lam ^ 2) := valGe_mono (by omega) (valGe_mul hE.a4 (valGe_pow 2 hlam_ge))
      have g3 : ValGe p 1 (E.a₆ * lam ^ 3) := valGe_mono (by omega) (valGe_mul hE.a6 (valGe_pow 3 hlam_ge))
      exact valGe_add (valGe_add g1 g2) g3
    have hc2_ge : ValGe p (2 * (r : ℤ) + 1) c2 := by
      have g1 : ValGe p (2 * (r : ℤ) + 1) (E.a₁ * lam) :=
        valGe_mono (by omega) (valGe_mul hE.a1 hlam_ge)
      have g2 : ValGe p (2 * (r : ℤ) + 1) (E.a₂ * nu) :=
        valGe_mono (by omega) (valGe_mul hE.a2 hnu_ge)
      have g3 : ValGe p (2 * (r : ℤ) + 1) (E.a₃ * lam ^ 2) :=
        valGe_mono (by omega) (valGe_mul hE.a3 (valGe_pow 2 hlam_ge))
      have g4 : ValGe p (2 * (r : ℤ) + 1) (2 * E.a₄ * lam * nu) :=
        valGe_mono (by omega) (valGe_mul (valGe_mul (valGe_mul (valGe_of_nat p 2) hE.a4) hlam_ge) hnu_ge)
      have g5 : ValGe p (2 * (r : ℤ) + 1) (3 * E.a₆ * lam ^ 2 * nu) :=
        valGe_mono (by omega) (valGe_mul (valGe_mul (valGe_mul (valGe_of_nat p 3) hE.a6) (valGe_pow 2 hlam_ge)) hnu_ge)
      exact valGe_add (valGe_add (valGe_add (valGe_add g1 g2) g3) g4) g5
    set t₃ := -t₁ - t₂ - c2 / c3
    set w₃ := lam * t₃ + nu
    obtain ⟨_, _, heq3, hnu3, hsumx⟩ :=
      cubic_vieta_identities heq1 heq2 hl1 hl2 htan hc3_val.1
    exact add_inFilt_finish hE hr hns₁ hns₂ hxy rfl rfl rfl rfl hy₁0 hy₂0 hw₁0 hw₂0
      hvt₁ hvt₂ hlam_ge hnu_ge hnu_ne hslope hc3_val hc2_ge rfl rfl hl1 heq3 hnu3 hsumx

private lemma nsmul_inFilt_and_param {E : WeierstrassCurve ℚ} {p : ℕ} [Fact p.Prime]
    (hE : PIntegralCurve E p) {r : ℕ} (hr : 1 ≤ r) {Q : E.toAffine.Point}
    (hQ : InFilt E p r Q) (a : ℕ) :
    InFilt E p r (a • Q) ∧ ValGe p (2 * (r : ℤ) + 1) (param (a • Q) - (a : ℚ) * param Q) := by
  induction a with
  | zero =>
    refine ⟨Or.inl rfl, ?_⟩
    simp [param, ValGe]
  | succ a ih =>
    rw [add_nsmul, one_smul]
    obtain ⟨h1, h2⟩ := add_inFilt_and_param hE hr ih.1 hQ
    refine ⟨h1, ?_⟩
    have hsplit : param (a • Q + Q) - ((a + 1 : ℕ) : ℚ) * param Q =
        (param (a • Q + Q) - (param (a • Q) + param Q)) +
        (param (a • Q) - (a : ℚ) * param Q) := by push_cast; ring
    rw [hsplit]
    exact valGe_add h2 ih.2

private lemma param_val_nsmul {E : WeierstrassCurve ℚ} {p : ℕ} [Fact p.Prime]
    (hE : PIntegralCurve E p) {Q : E.toAffine.Point}
    (hQ : InFilt E p 1 Q) (hQ0 : Q ≠ 0) :
    ∀ k : ℕ, 0 < k →
      InFilt E p 1 (k • Q) ∧
      (k • Q ≠ 0 → padicValRat p (param (k • Q)) =
        padicValRat p (param Q) + (k.factorization p : ℤ)) := by
  have hbase : ∀ (R : E.toAffine.Point), InFilt E p 1 R → R ≠ 0 →
      ∀ (a : ℕ), 0 < a → Nat.Coprime p a →
        InFilt E p 1 (a • R) ∧
        (a • R ≠ 0 → padicValRat p (param (a • R)) = padicValRat p (param R)) := by
    intro R hR hR0 a ha hcop
    rcases hR with rfl | ⟨x, y, hns, rfl, hx0, hxval⟩
    · exact (hR0 rfl).elim
    obtain ⟨_, ht0, _, hvt1, hx_eq, _, _⟩ := param_val_of_inFilt hE le_rfl hns hx0 hxval
    have hp_eq : param (WeierstrassCurve.Affine.Point.some x y hns) = -x / y := rfl
    set r := (padicValRat p (-x / y)).toNat
    have hr1 : 1 ≤ r := by omega
    have hvr : padicValRat p (-x / y) = (r : ℤ) := by omega
    have hRr : InFilt E p r (WeierstrassCurve.Affine.Point.some x y hns) :=
      Or.inr ⟨x, y, hns, rfl, hx0, by omega⟩
    obtain ⟨hinf, herr⟩ := nsmul_inFilt_and_param hE hr1 hRr a
    refine ⟨inFilt_mono hr1 hinf, fun _ => ?_⟩
    have ha0 : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
    have hva : padicValRat p (a : ℚ) = 0 := by
      rw [padicValRat.of_nat]
      have hndvd : ¬ p ∣ a := (Fact.out : p.Prime).coprime_iff_not_dvd.mp hcop
      simp [padicValNat.eq_zero_of_not_dvd hndvd]
    rw [hp_eq] at herr ⊢
    have hq0 : (a : ℚ) * (-x / y) ≠ 0 := mul_ne_zero ha0 ht0
    have hvq : padicValRat p ((a : ℚ) * (-x / y)) = (r : ℤ) := by
      rw [padicValRat.mul ha0 ht0, hva, zero_add, hvr]
    have hsplit : param (a • WeierstrassCurve.Affine.Point.some x y hns) =
        (a : ℚ) * (-x / y) +
        (param (a • WeierstrassCurve.Affine.Point.some x y hns) - (a : ℚ) * (-x / y)) := by ring
    rw [hsplit]
    have hres := val_add_eq_of_valGe_gt hq0 (valGe_mono (by omega) herr)
    rw [hres.2, hvq, hvr]
  have hstep_p : ∀ (R : E.toAffine.Point), InFilt E p 1 R → R ≠ 0 →
      InFilt E p 1 (p • R) ∧ p • R ≠ 0 ∧
      padicValRat p (param (p • R)) = padicValRat p (param R) + 1 := by
    intro R hR hR0
    rcases hR with rfl | ⟨x, y, hns, rfl, hx0, hxval⟩
    · exact (hR0 rfl).elim
    obtain ⟨_, ht0, _, hvt1, hx_eq, _, _⟩ := param_val_of_inFilt hE le_rfl hns hx0 hxval
    have hp_eq : param (WeierstrassCurve.Affine.Point.some x y hns) = -x / y := rfl
    set r := (padicValRat p (-x / y)).toNat
    have hr1 : 1 ≤ r := by omega
    have hvr : padicValRat p (-x / y) = (r : ℤ) := by omega
    have hRr : InFilt E p r (WeierstrassCurve.Affine.Point.some x y hns) :=
      Or.inr ⟨x, y, hns, rfl, hx0, by omega⟩
    obtain ⟨hinf, herr⟩ := nsmul_inFilt_and_param hE hr1 hRr p
    have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    have hvp : padicValRat p (p : ℚ) = 1 := padicValRat.self (Fact.out : p.Prime).one_lt
    rw [hp_eq] at herr ⊢
    have hq0 : (p : ℚ) * (-x / y) ≠ 0 := mul_ne_zero hp0 ht0
    have hvq : padicValRat p ((p : ℚ) * (-x / y)) = (r : ℤ) + 1 := by
      rw [padicValRat.mul hp0 ht0, hvp, hvr]; ring
    have hsplit : param (p • WeierstrassCurve.Affine.Point.some x y hns) =
        (p : ℚ) * (-x / y) +
        (param (p • WeierstrassCurve.Affine.Point.some x y hns) - (p : ℚ) * (-x / y)) := by ring
    have hres := val_add_eq_of_valGe_gt hq0 (valGe_mono (by omega) herr)
    rw [← hsplit] at hres
    refine ⟨inFilt_mono hr1 hinf, ?_, ?_⟩
    · intro hzero
      rw [hzero] at hres
      exact hres.1 rfl
    · rw [hres.2, hvq, hvr]
  have hpow : ∀ e : ℕ, InFilt E p 1 ((p ^ e) • Q) ∧ (p ^ e) • Q ≠ 0 ∧
      padicValRat p (param ((p ^ e) • Q)) = padicValRat p (param Q) + (e : ℤ) := by
    intro e
    induction e with
    | zero =>
      simp [hQ, hQ0]
    | succ e ih =>
      rw [pow_succ', mul_smul]
      obtain ⟨h1, h2, h3⟩ := hstep_p _ ih.1 ih.2.1
      refine ⟨h1, h2, ?_⟩
      rw [h3, ih.2.2]
      push_cast; ring
  intro k hk
  set e := k.factorization p
  set c := ordCompl[p] k
  have hdecomp : p ^ e * c = k := Nat.ordProj_mul_ordCompl_eq_self k p
  have hc_pos : 0 < c := Nat.ordCompl_pos p hk.ne'
  have hcop : Nat.Coprime p c := Nat.coprime_ordCompl (Fact.out : p.Prime) hk.ne'
  obtain ⟨h1, h2, h3⟩ := hpow e
  obtain ⟨h4, h5⟩ := hbase ((p ^ e) • Q) h1 h2 c hc_pos hcop
  have hsmul : k • Q = c • ((p ^ e) • Q) := by
    rw [← mul_smul, mul_comm, hdecomp]
  rw [hsmul]
  refine ⟨h4, fun hne => ?_⟩
  rw [h5 hne, h3]

/- ### Part 5: Denominator valuation bound and final limit -/

private lemma rat_den_factorization_le {p : ℕ} [Fact p.Prime] {q : ℚ} (hq : q ≠ 0) :
    (q.den.factorization p : ℤ) ≤ max 0 (-padicValRat p q) := by
  have hdef : padicValRat p q = (padicValInt p q.num : ℤ) - (padicValNat p q.den : ℤ) := by
    rw [padicValRat_def]
  have hden_pos : q.den ≠ 0 := q.den_nz
  have hnum_ne : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
  have hfac_den : q.den.factorization p = padicValNat p q.den :=
    Nat.factorization_def q.den Fact.out
  have hfac_num : q.num.natAbs.factorization p = padicValNat p q.num.natAbs :=
    Nat.factorization_def q.num.natAbs Fact.out
  have hpadic_int : padicValInt p q.num = padicValNat p q.num.natAbs := rfl
  have hcop : Nat.Coprime q.num.natAbs q.den := q.reduced
  by_cases hdvd : p ∣ q.den
  · have hndvd : ¬ p ∣ q.num.natAbs := by
      intro h
      exact (Fact.out : p.Prime).not_dvd_one (hcop ▸ Nat.dvd_gcd h hdvd)
    have hz : padicValNat p q.num.natAbs = 0 := padicValNat.eq_zero_of_not_dvd hndvd
    rw [hfac_den]
    have hval : padicValRat p q = -(padicValNat p q.den : ℤ) := by
      rw [hdef, hpadic_int, hz]; simp
    rw [hval]
    omega
  · rw [hfac_den, padicValNat.eq_zero_of_not_dvd hdvd]
    simp

theorem main_proof :
    OMA.R_EllipticDivisibilitySequence_silverman_eds_primitive_prime_divisors_R1_H2_R1.H2 := by
  classical
  intro W hw hW d p
  dsimp only [d]
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    obtain ⟨h0, hneg⟩ := W_zero_and_neg hw
    obtain ⟨hdvd, h1, E, x, y, hΔ, hEq, hψ⟩ := hw
    have hns : E.toAffine.Nonsingular x y :=
      (E.toAffine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp hEq
    set P : E.toAffine.Point := WeierstrassCurve.Affine.Point.some x y hns
    -- Choose scaling exponent M so E' = scaleCurve E (p^M) has v_p(a'_i) ≥ 1
    set m0 : ℤ := min (min (min (min (padicValRat p E.a₁) (padicValRat p E.a₂))
      (padicValRat p E.a₃)) (padicValRat p E.a₄)) (padicValRat p E.a₆)
    set M : ℕ := (1 - min 0 m0).toNat
    have hM1 : 1 ≤ (M : ℤ) + padicValRat p E.a₁ := by omega
    have hM2 : 1 ≤ (M : ℤ) + padicValRat p E.a₂ := by omega
    have hM3 : 1 ≤ (M : ℤ) + padicValRat p E.a₃ := by omega
    have hM4 : 1 ≤ (M : ℤ) + padicValRat p E.a₄ := by omega
    have hM6 : 1 ≤ (M : ℤ) + padicValRat p E.a₆ := by omega
    set u : ℚ := (p : ℚ) ^ M
    have hu_ne : u ≠ 0 := pow_ne_zero M (Nat.cast_ne_zero.mpr hp.ne_zero)
    have hvu : padicValRat p u = (M : ℤ) := by
      dsimp only [u]
      rw [padicValRat.pow (p : ℚ), padicValRat.self hp.one_lt, mul_one]
    set E' := scaleCurve E u
    have hE' : PIntegralCurve E' p := by
      have mk_ge : ∀ (k : ℕ) (hk : 1 ≤ k) (c : ℚ), 1 ≤ (M : ℤ) + padicValRat p c →
          ValGe p 1 (u ^ k * c) := by
        intro k hk c hc
        by_cases hc0 : c = 0
        · simp [ValGe, hc0]
        right
        rw [padicValRat.mul (pow_ne_zero k hu_ne) hc0, padicValRat.pow u, hvu]
        have hM_nonneg : (0 : ℤ) ≤ M := Nat.cast_nonneg M
        nlinarith
      exact ⟨by simpa only [E', scaleCurve, pow_one] using mk_ge 1 (by decide) E.a₁ hM1,
        mk_ge 2 (by decide) E.a₂ hM2,
        mk_ge 3 (by decide) E.a₃ hM3, mk_ge 4 (by decide) E.a₄ hM4,
        mk_ge 6 (by decide) E.a₆ hM6⟩
    set φ := scalePointHom E u hu_ne hΔ
    set P' : E'.toAffine.Point := φ P
    -- Every n ≥ 1 has n • P' = some (u^2 * x_n) (u^3 * y_n) with x_n - x = -W(n+1)W(n-1)/W(n)^2
    have hcoords := nsmul_coords hdvd h1 h0 hneg hW E x y hΔ hEq hψ
    -- Bound -v_p(x'_n) ≤ C₁ + 2*n for all n ≥ 1
    have hbound_x' : ∃ C₁ : ℕ, ∀ n : ℕ, 1 ≤ n →
        ∀ (xn yn : ℚ) (hnsn : E'.toAffine.Nonsingular xn yn),
          n • P' = WeierstrassCurve.Affine.Point.some xn yn hnsn →
          xn ≠ 0 → -padicValRat p xn ≤ (C₁ : ℤ) + 2 * (n : ℤ) := by
      -- Subgroup H = {n : ℤ | InFilt E' p 1 (n • P')}
      have hH_add : ∀ a b : ℤ, InFilt E' p 1 (a • P') → InFilt E' p 1 (b • P') →
          InFilt E' p 1 ((a + b) • P') := by
        intro a b ha hb
        rw [add_zsmul]
        exact (add_inFilt_and_param hE' le_rfl ha hb).1
      have hH_neg : ∀ a : ℤ, InFilt E' p 1 (a • P') → InFilt E' p 1 ((-a) • P') := by
        intro a ha
        rw [neg_zsmul]
        exact (neg_inFilt_and_param hE' le_rfl ha).1
      by_cases hex : ∃ m : ℕ, 0 < m ∧ InFilt E' p 1 (m • P')
      · set m := Nat.find hex
        have hm_spec : 0 < m ∧ InFilt E' p 1 (m • P') := Nat.find_spec hex
        have hm_min : ∀ j : ℕ, j < m → ¬ (0 < j ∧ InFilt E' p 1 (j • P')) :=
          fun j hj => Nat.find_min hex hj
        -- m • P' ≠ 0 because m • P = some ...
        have hmP'_ne : m • P' ≠ 0 := by
          obtain ⟨xm, ym, hnsm, hPm, _, _⟩ := hcoords m hm_spec.1
          have h1' : m • P' = φ (m • P) := (map_nsmul φ m P).symm
          rw [h1', hPm]
          exact WeierstrassCurve.Affine.Point.some_ne_zero _
        -- Extract base valuation r₀
        have hr0_def : 0 ≤ padicValRat p (param (m • P')) := by
          rcases hm_spec.2 with hzero | ⟨xm, ym, hnsm, hEqm, hxm0, hxmval⟩
          · exact (hmP'_ne hzero).elim
          rw [hEqm]
          obtain ⟨_, _, _, hvt1, _, _, _⟩ := param_val_of_inFilt hE' le_rfl hnsm hxm0 hxmval
          change 0 ≤ padicValRat p (-xm / ym)
          omega
        set r₀ : ℕ := (padicValRat p (param (m • P'))).toNat
        have hr0_eq : padicValRat p (param (m • P')) = (r₀ : ℤ) := by omega
        refine ⟨2 * r₀, fun n hn xn yn hnsn hPn hxn0 => ?_⟩
        by_cases hneg_val : padicValRat p xn < 0
        · -- Then n • P' ∈ E'_1, so m ∣ n!
          have hn_in : InFilt E' p 1 (n • P') := by
            obtain ⟨_, s, hs1, hxs, _⟩ := val_x_y_of_neg hE' hnsn.1 hxn0 hneg_val
            exact Or.inr ⟨xn, yn, hnsn, hPn, hxn0, by omega⟩
          have hm_dvd : m ∣ n := by
            by_contra hndvd
            set q := n / m
            set rem := n % m
            have hrem_pos : 0 < rem := Nat.pos_of_ne_zero (fun h => hndvd (Nat.dvd_of_mod_eq_zero h))
            have hrem_lt : rem < m := Nat.mod_lt n hm_spec.1
            have hrem_eq : (rem : ℤ) = (n : ℤ) + (-(q : ℤ) * (m : ℤ)) := by
              have hdm : (m : ℤ) * (q : ℤ) + (rem : ℤ) = (n : ℤ) := by
                exact_mod_cast Nat.div_add_mod n m
              linarith
            have hqm_in : InFilt E' p 1 (((q : ℤ) * (m : ℤ)) • P') := by
              have h1' : ((q : ℤ) * (m : ℤ)) • P' = q • (m • P') := by
                rw [mul_zsmul, natCast_zsmul, natCast_zsmul]
              rw [h1']
              exact (nsmul_inFilt_and_param hE' le_rfl hm_spec.2 q).1
            have hrem_in : InFilt E' p 1 (rem • P') := by
              have hrem_cast : rem • P' = (rem : ℤ) • P' := (natCast_zsmul P' rem).symm
              rw [hrem_cast, hrem_eq]
              have : -(q : ℤ) * (m : ℤ) = -((q : ℤ) * (m : ℤ)) := by ring
              rw [this]
              exact hH_add (n : ℤ) (-((q : ℤ) * (m : ℤ)))
                (by rwa [natCast_zsmul]) (hH_neg _ hqm_in)
            exact hm_min rem hrem_lt ⟨hrem_pos, hrem_in⟩
          obtain ⟨k, rfl⟩ := hm_dvd
          have hk_pos : 0 < k := by
            rcases Nat.eq_zero_or_pos k with rfl | hk
            · simp at hn
            · exact hk
          have hk_smul : (m * k) • P' = k • (m • P') := by rw [mul_comm, mul_smul]
          have hP'_ne : k • (m • P') ≠ 0 := by
            rw [← hk_smul, hPn]; exact WeierstrassCurve.Affine.Point.some_ne_zero _
          have hval_param := (param_val_nsmul hE' hm_spec.2 hmP'_ne k hk_pos).2 hP'_ne
          rw [← hk_smul, hPn] at hval_param
          have hpeq : param (WeierstrassCurve.Affine.Point.some xn yn hnsn) = -xn / yn := rfl
          rw [hpeq] at hval_param
          obtain ⟨_, _, _, _, hxeq, _, _⟩ :=
            param_val_of_inFilt hE' le_rfl hnsn hxn0 (by
              obtain ⟨_, s, hs1, hxs, _⟩ := val_x_y_of_neg hE' hnsn.1 hxn0 hneg_val
              omega)
          have hfac_le : k.factorization p ≤ m * k := by
            have h1' : p ^ k.factorization p ∣ k := Nat.ordProj_dvd k p
            have h2' : p ^ k.factorization p ≤ k := Nat.le_of_dvd hk_pos h1'
            have h3' : k.factorization p < 2 ^ k.factorization p := Nat.lt_two_pow_self
            have h4' : 2 ^ k.factorization p ≤ p ^ k.factorization p :=
              Nat.pow_le_pow_left hp.two_le _
            have h5' : k ≤ m * k := Nat.le_mul_of_pos_left k hm_spec.1
            omega
          omega
        · omega
      · refine ⟨0, fun n hn xn yn hnsn hPn hxn0 => ?_⟩
        by_contra hlt
        have hneg_val : padicValRat p xn < 0 := by omega
        obtain ⟨_, s, hs1, hxs, _⟩ := val_x_y_of_neg hE' hnsn.1 hxn0 hneg_val
        exact hex ⟨n, by omega, Or.inr ⟨xn, yn, hnsn, hPn, hxn0, by omega⟩⟩
    obtain ⟨C₁, hC₁⟩ := hbound_x'
    -- Translate bound on -v_p(x'_n) to bound on (d n).factorization p
    set C₂ : ℕ := (max 0 (-padicValRat p x)).toNat
    set C : ℕ := max C₂ (2 * M + C₁)
    have hbound_d : ∀ n : ℕ, 2 ≤ n →
        ((W (n : ℤ)).natAbs ^ 2 /
          Nat.gcd ((W (↑(n + 1) : ℤ)).natAbs * (W (↑(n - 1) : ℤ)).natAbs)
            ((W (n : ℤ)).natAbs ^ 2)).factorization p ≤ C + 2 * n := by
      intro n hn2
      obtain ⟨xn, yn, hnsn, hPn, hxn, _⟩ := hcoords n (by omega)
      set q : ℚ := xn - x
      have hq_eq : q = -((W ((n : ℤ) + 1) : ℚ) * (W ((n : ℤ) - 1) : ℚ)) / (W (n : ℤ) : ℚ) ^ 2 := by
        dsimp only [q]; rw [hxn]; ring
      have hWn_ne : W (n : ℤ) ≠ 0 := hW n (by omega)
      have hWnp1_ne : W ((n : ℤ) + 1) ≠ 0 := hW ((n : ℤ) + 1) (by omega)
      have hWnm1_ne : W ((n : ℤ) - 1) ≠ 0 := hW ((n : ℤ) - 1) (by omega)
      have hq_ne : q ≠ 0 := by
        rw [hq_eq]
        exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (Int.cast_ne_zero.mpr hWnp1_ne)
          (Int.cast_ne_zero.mpr hWnm1_ne))) (pow_ne_zero 2 (Int.cast_ne_zero.mpr hWn_ne))
      -- Identify q.den with d n
      have hcast_np1 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by omega
      have hcast_nm1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
      have hden_eq : q.den =
          (W (n : ℤ)).natAbs ^ 2 /
            Nat.gcd ((W (↑(n + 1) : ℤ)).natAbs * (W (↑(n - 1) : ℤ)).natAbs)
              ((W (n : ℤ)).natAbs ^ 2) := by
        set a : ℤ := -(W ((n : ℤ) + 1) * W ((n : ℤ) - 1))
        set b : ℕ := (W (n : ℤ)).natAbs ^ 2
        have hb_pos : 0 < b := pow_pos (Int.natAbs_pos.mpr hWn_ne) 2
        have hq_div : q = (a : ℚ) / (b : ℚ) := by
          rw [hq_eq]
          dsimp only [a, b]
          push_cast
          have hsq : ((W (n : ℤ)).natAbs : ℚ) ^ 2 = (W (n : ℤ) : ℚ) ^ 2 := by
            have h1' : (((W (n : ℤ)).natAbs : ℤ) ^ 2 : ℤ) = W (n : ℤ) ^ 2 := Int.natAbs_sq _
            have h2' := congrArg (Int.cast : ℤ → ℚ) h1'
            simp only [Int.cast_pow, Int.cast_natCast] at h2'
            exact h2'
          rw [hsq]
        have hnum_den : q.num * (b : ℤ) = a * (q.den : ℤ) := by
          have h1 : (q.num : ℚ) / (q.den : ℚ) = (a : ℚ) / (b : ℚ) := by
            rw [Rat.num_div_den]; exact hq_div
          have h2 : (q.num : ℚ) * (b : ℚ) = (a : ℚ) * (q.den : ℚ) := by
            have hd0 : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
            have hb0 : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb_pos.ne'
            field_simp [hd0, hb0] at h1
            linarith
          exact_mod_cast h2
        have habs : q.num.natAbs * b = a.natAbs * q.den := by
          have := congrArg Int.natAbs hnum_den
          simpa [Int.natAbs_mul] using this
        have hdvd_b : q.den ∣ b := by
          have h1 : q.den ∣ q.num.natAbs * b := ⟨a.natAbs, by linarith⟩
          exact q.reduced.symm.dvd_of_dvd_mul_left h1
        obtain ⟨k, hk_eq⟩ := hdvd_b
        have hk_pos : 0 < k := by
          rcases Nat.eq_zero_or_pos k with rfl | hk
          · simp at hk_eq; omega
          · exact hk
        have ha_eq : a.natAbs = q.num.natAbs * k := by
          have h1 : q.num.natAbs * (q.den * k) = a.natAbs * q.den := by rwa [← hk_eq]
          have h2 : (q.num.natAbs * k) * q.den = a.natAbs * q.den := by linarith
          exact (Nat.mul_right_cancel (Nat.pos_of_ne_zero q.den_nz) h2).symm
        have ha_natAbs : a.natAbs = (W (↑(n + 1) : ℤ)).natAbs * (W (↑(n - 1) : ℤ)).natAbs := by
          dsimp only [a]
          rw [Int.natAbs_neg, Int.natAbs_mul, hcast_np1, hcast_nm1]
        have hgcd : Nat.gcd a.natAbs b = k := by
          rw [ha_eq, hk_eq, Nat.mul_comm q.num.natAbs k, Nat.mul_comm q.den k,
            Nat.gcd_mul_left, q.reduced, mul_one]
        rw [← ha_natAbs]
        change q.den = b / Nat.gcd a.natAbs b
        rw [hgcd, hk_eq, Nat.mul_div_cancel _ hk_pos]
      rw [← hden_eq]
      have hfac_le := rat_den_factorization_le (p := p) hq_ne
      -- Bound -padicValRat p (xn - x)
      have hval_xn : xn ≠ 0 → -padicValRat p xn ≤ 2 * (M : ℤ) + (C₁ : ℤ) + 2 * (n : ℤ) := by
        intro hxn0
        have hPn' : n • P' = φ (n • P) := (map_nsmul φ n P).symm
        rw [hPn] at hPn'
        have hxn'_ne : u ^ 2 * xn ≠ 0 := mul_ne_zero (pow_ne_zero 2 hu_ne) hxn0
        have hbound' := hC₁ n (by omega) (u ^ 2 * xn) (u ^ 3 * yn) _ hPn' hxn'_ne
        rw [padicValRat.mul (pow_ne_zero 2 hu_ne) hxn0, padicValRat.pow u, hvu] at hbound'
        omega
      have hval_q : -padicValRat p q ≤ (C : ℤ) + 2 * (n : ℤ) := by
        dsimp only [q]
        by_cases hxn0 : xn = 0
        · rw [hxn0, zero_sub, padicValRat.neg]; omega
        by_cases hx0 : x = 0
        · rw [hx0, sub_zero]; have := hval_xn hxn0; omega
        have hq_ne' : xn + -x ≠ 0 := by
          dsimp only [q] at hq_ne
          rwa [← sub_eq_add_neg]
        have hmin := padicValRat.min_le_padicValRat_add (p := p) (q := xn) (r := -x) hq_ne'
        rw [← sub_eq_add_neg, padicValRat.neg] at hmin
        have := hval_xn hxn0
        omega
      omega
    -- Conclude Tendsto ... atTop (nhds 0) via squeeze theorem
    have hupper : Tendsto (fun n : ℕ => ((C : ℝ) + 2 * (n : ℝ)) / (n : ℝ) ^ 2) atTop (nhds 0) := by
      have h1 : Tendsto (fun n : ℕ => (C : ℝ) / (n : ℝ) ^ 2) atTop (nhds 0) := by
        have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ 2) atTop atTop :=
          (tendsto_pow_atTop (by decide : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop
        exact tendsto_const_nhds.div_atTop hpow
      have h2 : Tendsto (fun n : ℕ => (2 : ℝ) / (n : ℝ)) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      have hsum := h1.add h2
      rw [add_zero] at hsum
      refine hsum.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp [hnR]
    refine squeeze_zero' ?_ ?_ hupper
    · filter_upwards with n
      positivity
    · filter_upwards [eventually_ge_atTop 2] with n hn
      have hle : (((W (n : ℤ)).natAbs ^ 2 /
          Nat.gcd ((W (↑(n + 1) : ℤ)).natAbs * (W (↑(n - 1) : ℤ)).natAbs)
            ((W (n : ℤ)).natAbs ^ 2)).factorization p : ℝ) ≤ (C : ℝ) + 2 * (n : ℝ) := by
        exact_mod_cast hbound_d n hn
      exact div_le_div_of_nonneg_right hle (by positivity)
  · -- Non-prime p: factorization p is identically 0
    have hzero : (fun n : ℕ =>
        (((W (n : ℤ)).natAbs ^ 2 /
          Nat.gcd ((W (↑(n + 1) : ℤ)).natAbs * (W (↑(n - 1) : ℤ)).natAbs)
            ((W (n : ℤ)).natAbs ^ 2)).factorization p : ℝ) / (n : ℝ) ^ 2) = fun _ => 0 := by
      funext n
      rw [Nat.factorization_eq_zero_of_not_prime _ hp]
      simp
    rw [hzero]
    exact tendsto_const_nhds

end SilvermanEDSR1H2R1H2

theorem OMA.solution :
    OMA.R_EllipticDivisibilitySequence_silverman_eds_primitive_prime_divisors_R1_H2_R1.H2 :=
  SilvermanEDSR1H2R1H2.main_proof
