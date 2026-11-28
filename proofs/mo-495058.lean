import OMAStatements.S_mo_495058

namespace OMA.P_mo_495058

open Matrix Finset Set
open scoped Matrix.Norms.L2Operator
open OMA.S_mo_495058

private lemma norm_toLp_sq {m : ℕ} (x : Fin m → ℝ) :
    ‖WithLp.toLp 2 x‖ ^ 2 = ∑ j, (x j) ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]

private lemma l2_norm_le_iff {n m : ℕ} (A : Rect n m) {C : ℝ} (hC : 0 ≤ C) :
    ‖A‖ ≤ C ↔ ∀ x : Fin m → ℝ, ∑ i, (∑ j, A i j * x j) ^ 2 ≤ C ^ 2 * ∑ j, (x j) ^ 2 := by
  rw [Matrix.l2_opNorm_def, ContinuousLinearMap.opNorm_le_iff hC]
  constructor
  · intro h x
    have hv := h (WithLp.toLp 2 x)
    have hsq := sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _)) |>.mpr hv
    rw [mul_pow, norm_toLp_sq] at hsq
    have htv : ((toEuclideanLin (𝕜 := ℝ) (m := Fin n) (n := Fin m)).trans
        LinearMap.toContinuousLinearMap A) (WithLp.toLp 2 x) = WithLp.toLp 2 (A *ᵥ x) := by
      rfl
    rw [htv, norm_toLp_sq] at hsq
    simpa [Matrix.mulVec, dotProduct] using hsq
  · intro h v
    have hx := h v.ofLp
    have htv : ((toEuclideanLin (𝕜 := ℝ) (m := Fin n) (n := Fin m)).trans
        LinearMap.toContinuousLinearMap A) v = WithLp.toLp 2 (A *ᵥ v.ofLp) := by
      rfl
    rw [htv]
    refine (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp ?_
    rw [mul_pow, norm_toLp_sq]
    have hv : ‖v‖ ^ 2 = ∑ j, (v.ofLp j) ^ 2 := by
      simpa using norm_toLp_sq v.ofLp
    rw [hv]
    simpa [Matrix.mulVec, dotProduct] using hx

private lemma l2_norm_sq_mulVec_le {n m : ℕ} (A : Rect n m) (x : Fin m → ℝ) :
    ∑ i, (∑ j, A i j * x j) ^ 2 ≤ ‖A‖ ^ 2 * ∑ j, (x j) ^ 2 :=
  (l2_norm_le_iff A (norm_nonneg A)).mp le_rfl x

private lemma l2_norm_sq_le_of_forall {n m : ℕ} (A : Rect n m) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ x : Fin m → ℝ, ∑ i, (∑ j, A i j * x j) ^ 2 ≤ M * ∑ j, (x j) ^ 2) :
    ‖A‖ ^ 2 ≤ M := by
  have h1 : ‖A‖ ≤ Real.sqrt M := by
    rw [l2_norm_le_iff A (Real.sqrt_nonneg M), Real.sq_sqrt hM]
    exact h
  have h2 := sq_le_sq₀ (norm_nonneg A) (Real.sqrt_nonneg M) |>.mpr h1
  rwa [Real.sq_sqrt hM] at h2

private lemma rowSq_nonneg {m : ℕ} (r : Fin m → ℝ) : 0 ≤ rowSq r :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private lemma l2_norm_sq_le_frobenius {n m : ℕ} (A : Rect n m) :
    ‖A‖ ^ 2 ≤ ∑ i, rowSq (A i) := by
  refine l2_norm_sq_le_of_forall A (Finset.sum_nonneg fun i _ => rowSq_nonneg (A i)) fun x => ?_
  calc
    ∑ i, (∑ j, A i j * x j) ^ 2
        ≤ ∑ i, (∑ j, (A i j) ^ 2) * (∑ j, (x j) ^ 2) :=
          Finset.sum_le_sum fun i _ => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (A i) x
    _ = (∑ i, rowSq (A i)) * ∑ j, (x j) ^ 2 := by
          rw [Finset.sum_mul]
          rfl

private lemma rowSq_le_l2_norm_sq {n m : ℕ} (A : Rect n m) (i : Fin n) :
    rowSq (A i) ≤ ‖A‖ ^ 2 := by
  have h := l2_norm_sq_mulVec_le A (A i)
  have h1 : (∑ j, A i j * A i j) ^ 2 ≤ ∑ k, (∑ j, A k j * A i j) ^ 2 :=
    Finset.single_le_sum (f := fun k => (∑ j, A k j * A i j) ^ 2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 : ∑ j, A i j * A i j = rowSq (A i) := by
    simp only [rowSq, sq]
  rw [h2] at h1
  have h3 : (rowSq (A i)) ^ 2 ≤ ‖A‖ ^ 2 * rowSq (A i) := le_trans h1 h
  rcases eq_or_lt_of_le (rowSq_nonneg (A i)) with hzero | hpos
  · rw [← hzero]; positivity
  · nlinarith

private lemma part1 (n m : ℕ) (A : Rect n m) :
    ‖A‖ ≤ 1 ↔ (fromBlocks (1 : Mat n) A A.transpose (1 : Mat m)).PosSemidef := by
  have hAt : A.transpose = Aᴴ := by
    ext i j; simp
  rw [hAt]
  let : Invertible (1 : Mat n) := invertibleOne
  rw [Matrix.PosDef.fromBlocks₁₁ A (1 : Mat m) Matrix.PosDef.one]
  have h1inv : (1 : Mat n)⁻¹ = 1 := Matrix.inv_eq_left_inv (one_mul (1 : Mat n))
  rw [h1inv, Matrix.mul_one, Matrix.posSemidef_iff_dotProduct_mulVec]
  have hHerm : ((1 : Mat m) - Aᴴ * A).IsHermitian :=
    Matrix.isHermitian_one.sub (Matrix.isHermitian_conjTranspose_mul_self A)
  rw [and_iff_right hHerm, l2_norm_le_iff A zero_le_one]
  constructor
  · intro h x
    have hx := h x
    have hdot : star x ⬝ᵥ (((1 : Mat m) - Aᴴ * A) *ᵥ x) =
        (∑ j, (x j) ^ 2) - ∑ i, (∑ j, A i j * x j) ^ 2 := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub]
      have hxx : star x ⬝ᵥ x = ∑ j, (x j) ^ 2 := by
        simp [dotProduct, sq]
      have hAx : star x ⬝ᵥ ((Aᴴ * A) *ᵥ x) = ∑ i, (∑ j, A i j * x j) ^ 2 := by
        rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
        have hvec : star x ᵥ* Aᴴ = A *ᵥ x := by
          ext i
          simp [Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]
        rw [hvec]
        simp [Matrix.mulVec, dotProduct, sq]
      rw [hxx, hAx]
    rw [hdot]
    linarith
  · intro h x
    have hx := h x
    have hdot : star x ⬝ᵥ (((1 : Mat m) - Aᴴ * A) *ᵥ x) =
        (∑ j, (x j) ^ 2) - ∑ i, (∑ j, A i j * x j) ^ 2 := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub]
      have hxx : star x ⬝ᵥ x = ∑ j, (x j) ^ 2 := by
        simp [dotProduct, sq]
      have hAx : star x ⬝ᵥ ((Aᴴ * A) *ᵥ x) = ∑ i, (∑ j, A i j * x j) ^ 2 := by
        rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
        have hvec : star x ᵥ* Aᴴ = A *ᵥ x := by
          ext i
          simp [Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]
        rw [hvec]
        simp [Matrix.mulVec, dotProduct, sq]
      rw [hxx, hAx]
    rw [hdot] at hx
    linarith

private lemma l2_norm_one_le {n : ℕ} : ‖(1 : Mat n)‖ ≤ 1 := by
  rw [l2_norm_le_iff (1 : Mat n) zero_le_one]
  intro x
  have h : ∀ i : Fin n, ∑ j : Fin n, (1 : Mat n) i j * x j = x i := by
    intro i
    simp [Matrix.one_apply]
  simp [h]

private lemma l2_norm_unitary_le_one {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℝ) :
    ‖(U : Mat n)‖ ≤ 1 := by
  have h1 : ‖(U : Mat n)‖ * ‖(U : Mat n)‖ = ‖(U : Mat n)ᴴ * (U : Mat n)‖ :=
    (Matrix.l2_opNorm_conjTranspose_mul_self (U : Mat n)).symm
  have h2 : (U : Mat n)ᴴ * (U : Mat n) = 1 := Unitary.coe_star_mul_self U
  rw [h2] at h1
  have h3 : ‖(U : Mat n)‖ * ‖(U : Mat n)‖ ≤ 1 := h1.trans_le l2_norm_one_le
  nlinarith [norm_nonneg (U : Mat n)]

private lemma l2_norm_conjStarAlgAut {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℝ) (X : Mat n) :
    ‖Unitary.conjStarAlgAut ℝ (Mat n) U X‖ = ‖X‖ := by
  have hle : ∀ (V : Matrix.unitaryGroup (Fin n) ℝ) (Y : Mat n),
      ‖Unitary.conjStarAlgAut ℝ (Mat n) V Y‖ ≤ ‖Y‖ := by
    intro V Y
    rw [Unitary.conjStarAlgAut_apply]
    calc
      ‖(V : Mat n) * Y * (star V : Mat n)‖
          ≤ ‖(V : Mat n) * Y‖ * ‖(star V : Mat n)‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖(V : Mat n)‖ * ‖Y‖) * ‖(star V : Mat n)‖ :=
          mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ ≤ (1 * ‖Y‖) * 1 := by
          have hV := l2_norm_unitary_le_one V
          have hVs : ‖star (V : Mat n)‖ ≤ 1 := by
            simpa using l2_norm_unitary_le_one (star V)
          have hY := norm_nonneg Y
          have h1 : ‖(V : Mat n)‖ * ‖Y‖ ≤ 1 * ‖Y‖ := mul_le_mul_of_nonneg_right hV hY
          have h2 : (‖(V : Mat n)‖ * ‖Y‖) * ‖star (V : Mat n)‖ ≤ (1 * ‖Y‖) * ‖star (V : Mat n)‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
          exact le_trans h2 (mul_le_mul_of_nonneg_left hVs (by linarith))
      _ = ‖Y‖ := by ring
  refine le_antisymm (hle U X) ?_
  have hback : Unitary.conjStarAlgAut ℝ (Mat n) (star U)
      (Unitary.conjStarAlgAut ℝ (Mat n) U X) = X := by
    rw [← Unitary.conjStarAlgAut_mul_apply]
    simp
  have hrev := hle (star U) (Unitary.conjStarAlgAut ℝ (Mat n) U X)
  rwa [hback] at hrev

private lemma part2 (n : ℕ) (H : Mat n) (hH : H.IsHermitian) :
    H.PosSemidef ↔ ‖(1 : Mat n) - (decisionScale H)⁻¹ • H‖ ≤ 1 := by
  set s := decisionScale H
  have hs_pos : 0 < s := by
    dsimp only [s, decisionScale]
    have : 0 ≤ Real.sqrt (∑ i, ∑ j, (H i j) ^ 2) := Real.sqrt_nonneg _
    linarith
  have hH_lt_s : ‖H‖ < s := by
    have hF : ‖H‖ ^ 2 ≤ ∑ i, ∑ j, (H i j) ^ 2 := l2_norm_sq_le_frobenius H
    have hsqrt : ‖H‖ ≤ Real.sqrt (∑ i, ∑ j, (H i j) ^ 2) :=
      Real.le_sqrt_of_sq_le hF
    dsimp only [s, decisionScale]
    linarith
  let U := hH.eigenvectorUnitary
  let μ := hH.eigenvalues
  have hspec : H = Unitary.conjStarAlgAut ℝ (Mat n) U (diagonal μ) := by
    simpa [U, μ, Function.comp_def] using hH.spectral_theorem
  have hnormH : ‖H‖ = ‖μ‖ := by
    rw [hspec, l2_norm_conjStarAlgAut, Matrix.l2_opNorm_diagonal]
  have hmu_lt_s : ∀ i, |μ i| < s := by
    intro i
    have hi : |μ i| ≤ ‖μ‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm μ i
    linarith
  have hconj : (1 : Mat n) - s⁻¹ • H =
      Unitary.conjStarAlgAut ℝ (Mat n) U (diagonal fun i => 1 - s⁻¹ * μ i) := by
    have hdiag : (1 : Mat n) - s⁻¹ • diagonal μ = diagonal (fun i => 1 - s⁻¹ * μ i) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [← hdiag, map_sub, map_one, map_smul, ← hspec]
  rw [hconj, l2_norm_conjStarAlgAut, Matrix.l2_opNorm_diagonal,
    pi_norm_le_iff_of_nonneg zero_le_one, hH.posSemidef_iff_eigenvalues_nonneg]
  constructor
  · intro h i
    have hi : 0 ≤ μ i := h i
    have hlt := hmu_lt_s i
    have hdiv_lt : s⁻¹ * μ i < 1 := by
      rw [inv_mul_lt_iff₀ hs_pos]
      have : μ i ≤ |μ i| := le_abs_self _
      linarith
    have hdiv_nonneg : 0 ≤ s⁻¹ * μ i := mul_nonneg (inv_nonneg.mpr hs_pos.le) hi
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  · intro h i
    have hi := h i
    rw [Real.norm_eq_abs, abs_le] at hi
    have hdiv_nonneg : 0 ≤ s⁻¹ * μ i := by linarith
    have : 0 ≤ s * (s⁻¹ * μ i) := mul_nonneg hs_pos.le hdiv_nonneg
    rwa [← mul_assoc, mul_inv_cancel₀ hs_pos.ne', one_mul] at this

private lemma pairTop_ge_left {m : ℕ} (r s : Fin m → ℝ) :
    rowSq r ≤ pairTop r s := by
  dsimp only [pairTop]
  have h1 : (rowSq r - rowSq s) ^ 2 ≤ (rowSq r - rowSq s) ^ 2 + 4 * (rowDot r s) ^ 2 := by
    linarith [sq_nonneg (rowDot r s)]
  have h2 : |rowSq r - rowSq s| ≤ Real.sqrt ((rowSq r - rowSq s) ^ 2 + 4 * (rowDot r s) ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt h1
  have h3 : rowSq r - rowSq s ≤ |rowSq r - rowSq s| := le_abs_self _
  linarith

private lemma pairTop_ge_right {m : ℕ} (r s : Fin m → ℝ) :
    rowSq s ≤ pairTop r s := by
  dsimp only [pairTop]
  have h1 : (rowSq r - rowSq s) ^ 2 ≤ (rowSq r - rowSq s) ^ 2 + 4 * (rowDot r s) ^ 2 := by
    linarith [sq_nonneg (rowDot r s)]
  have h2 : |rowSq r - rowSq s| ≤ Real.sqrt ((rowSq r - rowSq s) ^ 2 + 4 * (rowDot r s) ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt h1
  have h3 : rowSq s - rowSq r ≤ |rowSq r - rowSq s| := by
    simpa [abs_sub_comm] using le_abs_self (rowSq s - rowSq r)
  linarith

private lemma pairTop_nonneg {m : ℕ} (r s : Fin m → ℝ) : 0 ≤ pairTop r s :=
  le_trans (rowSq_nonneg r) (pairTop_ge_left r s)

private lemma pairTop_char_eq {m : ℕ} (r s : Fin m → ℝ) :
    (pairTop r s - rowSq r) * (pairTop r s - rowSq s) = (rowDot r s) ^ 2 := by
  dsimp only [pairTop]
  set a := rowSq r
  set c := rowSq s
  set b := rowDot r s
  have hnonneg : 0 ≤ (a - c) ^ 2 + 4 * b ^ 2 := by positivity
  have hsq : Real.sqrt ((a - c) ^ 2 + 4 * b ^ 2) ^ 2 = (a - c) ^ 2 + 4 * b ^ 2 :=
    Real.sq_sqrt hnonneg
  nlinarith

private lemma pairTop_comb_le {m : ℕ} (r s : Fin m → ℝ) (y₁ y₂ : ℝ) :
    ∑ j, (y₁ * r j + y₂ * s j) ^ 2 ≤ pairTop r s * (y₁ ^ 2 + y₂ ^ 2) := by
  have hexp : ∑ j, (y₁ * r j + y₂ * s j) ^ 2 =
      rowSq r * y₁ ^ 2 + 2 * rowDot r s * y₁ * y₂ + rowSq s * y₂ ^ 2 := by
    have hterm : ∀ j, (y₁ * r j + y₂ * s j) ^ 2 =
        y₁ ^ 2 * (r j) ^ 2 + 2 * y₁ * y₂ * (r j * s j) + y₂ ^ 2 * (s j) ^ 2 := by
      intro j; ring
    simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
    dsimp only [rowSq, rowDot]
    ring
  rw [hexp]
  set p := pairTop r s
  set a := rowSq r
  set c := rowSq s
  set b := rowDot r s
  have hpa : 0 ≤ p - a := sub_nonneg.mpr (pairTop_ge_left r s)
  have hpc : 0 ≤ p - c := sub_nonneg.mpr (pairTop_ge_right r s)
  have hchar : (p - a) * (p - c) = b ^ 2 := pairTop_char_eq r s
  rcases eq_or_lt_of_le hpa with hzero | hpos
  · have hpa_eq : p = a := by linarith
    have hb : b = 0 := by nlinarith
    have hpc_y2 : 0 ≤ (p - c) * y₂ ^ 2 := mul_nonneg hpc (sq_nonneg y₂)
    rw [← hpa_eq, hb]
    linarith
  · have hmul : 0 ≤ (p - a) * ((p - a) * y₁ ^ 2 - 2 * b * y₁ * y₂ + (p - c) * y₂ ^ 2) := by
      have hid : (p - a) * ((p - a) * y₁ ^ 2 - 2 * b * y₁ * y₂ + (p - c) * y₂ ^ 2) =
          ((p - a) * y₁ - b * y₂) ^ 2 := by
        nlinarith
      rw [hid]
      exact sq_nonneg _
    nlinarith

private lemma pairTop_dot_sq_le {m : ℕ} (r s x : Fin m → ℝ) :
    (∑ j, r j * x j) ^ 2 + (∑ j, s j * x j) ^ 2 ≤ pairTop r s * ∑ j, (x j) ^ 2 := by
  set y₁ := ∑ j, r j * x j
  set y₂ := ∑ j, s j * x j
  have hid : y₁ ^ 2 + y₂ ^ 2 = ∑ j, (y₁ * r j + y₂ * s j) * x j := by
    have hterm : ∀ j, (y₁ * r j + y₂ * s j) * x j = y₁ * (r j * x j) + y₂ * (s j * x j) := by
      intro j; ring
    simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => y₁ * r j + y₂ * s j) x
  rw [← hid] at hcs
  have hcomb := pairTop_comb_le r s y₁ y₂
  have hx_nonneg : 0 ≤ ∑ j, (x j) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hbound : (y₁ ^ 2 + y₂ ^ 2) ^ 2 ≤ pairTop r s * (y₁ ^ 2 + y₂ ^ 2) * ∑ j, (x j) ^ 2 :=
    le_trans hcs (mul_le_mul_of_nonneg_right hcomb hx_nonneg)
  rcases eq_or_lt_of_le (add_nonneg (sq_nonneg y₁) (sq_nonneg y₂)) with hzero | hpos
  · rw [← hzero]
    exact mul_nonneg (pairTop_nonneg r s) hx_nonneg
  · nlinarith

private lemma pairTop_le_l2_norm_sq {n m : ℕ} (A : Rect (n + 2) m) :
    pairTop (A 0) (A 1) ≤ ‖A‖ ^ 2 := by
  set r := A 0
  set s := A 1
  set p := pairTop r s
  set a := rowSq r
  set c := rowSq s
  set b := rowDot r s
  rcases eq_or_lt_of_le (pairTop_nonneg r s) with hp0 | hp_pos
  · have hpz : p = 0 := hp0.symm
    rw [hpz]; positivity
  · have hpa : 0 ≤ p - a := sub_nonneg.mpr (pairTop_ge_left r s)
    have hchar : (p - a) * (p - c) = b ^ 2 := pairTop_char_eq r s
    have hex : ∃ y₁ y₂ : ℝ, 0 < y₁ ^ 2 + y₂ ^ 2 ∧
        ∑ j, (y₁ * r j + y₂ * s j) ^ 2 = p * (y₁ ^ 2 + y₂ ^ 2) := by
      have hexp : ∀ y₁ y₂ : ℝ, ∑ j, (y₁ * r j + y₂ * s j) ^ 2 =
          a * y₁ ^ 2 + 2 * b * y₁ * y₂ + c * y₂ ^ 2 := by
        intro y₁ y₂
        have hterm : ∀ j, (y₁ * r j + y₂ * s j) ^ 2 =
            y₁ ^ 2 * (r j) ^ 2 + 2 * y₁ * y₂ * (r j * s j) + y₂ ^ 2 * (s j) ^ 2 := by
          intro j; ring
        simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
        dsimp only [a, c, b, rowSq, rowDot]
        ring
      rcases eq_or_lt_of_le hpa with hzero | hpos
      · refine ⟨1, 0, by norm_num, ?_⟩
        rw [hexp]
        nlinarith
      · refine ⟨b, p - a, by nlinarith, ?_⟩
        rw [hexp]
        nlinarith
    obtain ⟨y₁, y₂, hy_pos, hyeq⟩ := hex
    let x : Fin m → ℝ := fun j => y₁ * r j + y₂ * s j
    have hxsq : ∑ j, (x j) ^ 2 = p * (y₁ ^ 2 + y₂ ^ 2) := hyeq
    have hlin : y₁ * (∑ j, r j * x j) + y₂ * (∑ j, s j * x j) = ∑ j, (x j) ^ 2 := by
      simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      dsimp only [x]
      ring
    set u := ∑ j, r j * x j
    set v := ∑ j, s j * x j
    have hcs2 : (y₁ * u + y₂ * v) ^ 2 ≤ (y₁ ^ 2 + y₂ ^ 2) * (u ^ 2 + v ^ 2) := by
      nlinarith [sq_nonneg (y₁ * v - y₂ * u)]
    rw [hlin] at hcs2
    have hsum_ge : u ^ 2 + v ^ 2 ≤ ∑ i : Fin (n + 2), (∑ j, A i j * x j) ^ 2 := by
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      have htail : 0 ≤ ∑ i : Fin n, (∑ j, A i.succ.succ j * x j) ^ 2 :=
        Finset.sum_nonneg fun _ _ => sq_nonneg _
      have h0 : A 0 = r := rfl
      have h1 : A (0 : Fin (n + 1)).succ = s := rfl
      rw [h0, h1]
      linarith
    have hnorm := l2_norm_sq_mulVec_le A x
    have hcomb : (∑ j, (x j) ^ 2) ^ 2 ≤ (y₁ ^ 2 + y₂ ^ 2) * (‖A‖ ^ 2 * ∑ j, (x j) ^ 2) := by
      calc
        (∑ j, (x j) ^ 2) ^ 2 ≤ (y₁ ^ 2 + y₂ ^ 2) * (u ^ 2 + v ^ 2) := hcs2
        _ ≤ (y₁ ^ 2 + y₂ ^ 2) * ∑ i : Fin (n + 2), (∑ j, A i j * x j) ^ 2 :=
          mul_le_mul_of_nonneg_left hsum_ge hy_pos.le
        _ ≤ (y₁ ^ 2 + y₂ ^ 2) * (‖A‖ ^ 2 * ∑ j, (x j) ^ 2) :=
          mul_le_mul_of_nonneg_left hnorm hy_pos.le
    rw [hxsq] at hcomb
    have hprod_pos : 0 < p * (y₁ ^ 2 + y₂ ^ 2) ^ 2 := mul_pos hp_pos (sq_pos_of_pos hy_pos)
    nlinarith

private lemma upperSq_nonneg {m : ℕ} : ∀ {n : ℕ} (A : Rect n m), 0 ≤ upperSq A
  | 0, _ => le_rfl
  | 1, A => rowSq_nonneg (A 0)
  | n + 2, A => add_nonneg (pairTop_nonneg (A 0) (A 1))
      (upperSq_nonneg (n := n) (fun i j => A i.succ.succ j))

private lemma part3 {m : ℕ} : ∀ {n : ℕ} (A : Rect n m),
    ‖A‖ ^ 2 ≤ upperSq A ∧ upperSq A ≤ (((n + 1) / 2 : ℕ) : ℝ) * ‖A‖ ^ 2
  | 0, A => by
    have h0 : ‖A‖ ≤ 0 := by
      rw [l2_norm_le_iff A le_rfl]
      intro x
      simp
    have hnorm0 : ‖A‖ = 0 := le_antisymm h0 (norm_nonneg A)
    simp [upperSq, hnorm0]
  | 1, A => by
    constructor
    · have h := l2_norm_sq_le_frobenius A
      simpa [upperSq] using h
    · have h := rowSq_le_l2_norm_sq A 0
      simpa [upperSq] using h
  | n + 2, A => by
    let A' : Rect n m := fun i j => A i.succ.succ j
    have ih := part3 (n := n) A'
    have hA'_le : ‖A'‖ ^ 2 ≤ ‖A‖ ^ 2 := by
      refine l2_norm_sq_le_of_forall A' (sq_nonneg ‖A‖) fun x => ?_
      have h1 : ∑ i : Fin n, (∑ j, A' i j * x j) ^ 2 ≤
          ∑ i : Fin (n + 2), (∑ j, A i j * x j) ^ 2 := by
        rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
        have h0 : 0 ≤ (∑ j, A 0 j * x j) ^ 2 := sq_nonneg _
        have h1' : 0 ≤ (∑ j, A (0 : Fin (n + 1)).succ j * x j) ^ 2 := sq_nonneg _
        dsimp only [A']
        linarith
      exact le_trans h1 (l2_norm_sq_mulVec_le A x)
    constructor
    · refine l2_norm_sq_le_of_forall A (upperSq_nonneg A) fun x => ?_
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      have hpair := pairTop_dot_sq_le (A 0) (A 1) x
      have htail : ∑ i : Fin n, (∑ j, A i.succ.succ j * x j) ^ 2 ≤
          upperSq A' * ∑ j, (x j) ^ 2 := by
        calc
          ∑ i : Fin n, (∑ j, A' i j * x j) ^ 2
              ≤ ‖A'‖ ^ 2 * ∑ j, (x j) ^ 2 := l2_norm_sq_mulVec_le A' x
          _ ≤ upperSq A' * ∑ j, (x j) ^ 2 :=
              mul_le_mul_of_nonneg_right ih.1 (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      have h1eq : (0 : Fin (n + 1)).succ = (1 : Fin (n + 2)) := rfl
      rw [h1eq]
      change (∑ j, A 0 j * x j) ^ 2 + ((∑ j, A 1 j * x j) ^ 2 +
          ∑ i : Fin n, (∑ j, A' i j * x j) ^ 2) ≤
          (pairTop (A 0) (A 1) + upperSq A') * ∑ j, (x j) ^ 2
      linarith
    · have hpair := pairTop_le_l2_norm_sq A
      have hdiv : (n + 2 + 1) / 2 = (n + 1) / 2 + 1 := by omega
      rw [hdiv]
      push_cast
      change pairTop (A 0) (A 1) + upperSq A' ≤ (((n + 1) / 2 : ℕ) + 1 : ℝ) * ‖A‖ ^ 2
      have htail : upperSq A' ≤ (((n + 1) / 2 : ℕ) : ℝ) * ‖A‖ ^ 2 := by
        calc
          upperSq A' ≤ (((n + 1) / 2 : ℕ) : ℝ) * ‖A'‖ ^ 2 := ih.2
          _ ≤ (((n + 1) / 2 : ℕ) : ℝ) * ‖A‖ ^ 2 :=
            mul_le_mul_of_nonneg_left hA'_le (Nat.cast_nonneg _)
      linarith

private lemma upperSq_orthonormal {m : ℕ} : ∀ {n : ℕ} (A : Rect n m),
    (∀ i, rowSq (A i) = 1) → (∀ i j, i ≠ j → rowDot (A i) (A j) = 0) →
    upperSq A = (((n + 1) / 2 : ℕ) : ℝ)
  | 0, _, _, _ => by simp [upperSq]
  | 1, A, h1, _ => by simp [upperSq, h1 0]
  | n + 2, A, h1, h2 => by
    have h01 : (0 : Fin (n + 2)) ≠ 1 := by simp
    have hp : pairTop (A 0) (A 1) = 1 := by
      dsimp only [pairTop]
      rw [h1 0, h1 1, h2 0 1 h01]
      norm_num
    let A' : Rect n m := fun i j => A i.succ.succ j
    have hA'1 : ∀ i, rowSq (A' i) = 1 := fun i => h1 i.succ.succ
    have hA'2 : ∀ i j, i ≠ j → rowDot (A' i) (A' j) = 0 := fun i j hij =>
      h2 i.succ.succ j.succ.succ (fun h => hij (Fin.succ_injective _ (Fin.succ_injective _ h)))
    have ih := upperSq_orthonormal (n := n) A' hA'1 hA'2
    have hdiv : (n + 2 + 1) / 2 = (n + 1) / 2 + 1 := by omega
    rw [hdiv]
    push_cast
    change pairTop (A 0) (A 1) + upperSq A' = (((n + 1) / 2 : ℕ) : ℝ) + 1
    linarith

private lemma part4 (n : ℕ) : upperSq (1 : Mat n) = (((n + 1) / 2 : ℕ) : ℝ) := by
  refine upperSq_orthonormal (1 : Mat n) ?_ ?_
  · intro i
    dsimp only [rowSq]
    have : ∀ j : Fin n, ((1 : Mat n) i j) ^ 2 = if i = j then 1 else 0 := by
      intro j
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    simp_rw [this]
    simp
  · intro i j hij
    dsimp only [rowDot]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hik : i = k
    · have hjk : j ≠ k := fun h => hij (hik.trans h.symm)
      simp [Matrix.one_apply, hjk]
    · simp [Matrix.one_apply, hik]

private lemma part5 (n : ℕ) (A : Mat n) : maxRow n A ≤ ‖A‖ := by
  dsimp only [maxRow]
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg A)]
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_iff.mpr ⟨norm_nonneg A, rowSq_le_l2_norm_sq A i⟩

private lemma part6 (n : ℕ) (d c : Fin n → ℝ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hd : ∀ i, a ≤ |d i|) (hc : ∀ j, b ≤ |c j|) (A : Mat n) :
    a * b * ‖A‖ ≤ ‖scale d c A‖ := by
  have hab : 0 < a * b := mul_pos ha hb
  have hbound : ‖A‖ ≤ ‖scale d c A‖ / (a * b) := by
    rw [l2_norm_le_iff A (div_nonneg (norm_nonneg _) hab.le)]
    intro x
    let y : Fin n → ℝ := fun j => x j / c j
    have hscale_entry : ∀ i j, scale d c A i j = d i * A i j * c j := by
      intro i j
      simp [scale, Matrix.mul_apply, Matrix.diagonal_apply]
    have hrow : ∀ i, ∑ j, scale d c A i j * y j = d i * ∑ j, A i j * x j := by
      intro i
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hcj : c j ≠ 0 := by
        intro h0
        have := hc j
        rw [h0, abs_zero] at this
        linarith
      rw [hscale_entry]
      dsimp only [y]
      field_simp [hcj]
    have h1 : a ^ 2 * ∑ i, (∑ j, A i j * x j) ^ 2 ≤
        ∑ i, (∑ j, scale d c A i j * y j) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [hrow i, mul_pow]
      have hdi : a ^ 2 ≤ (d i) ^ 2 := by
        have := sq_le_sq₀ ha.le (abs_nonneg (d i)) |>.mpr (hd i)
        simpa [sq_abs] using this
      exact mul_le_mul_of_nonneg_right hdi (sq_nonneg _)
    have h2 : ∑ i, (∑ j, scale d c A i j * y j) ^ 2 ≤
        ‖scale d c A‖ ^ 2 * ∑ j, (y j) ^ 2 := l2_norm_sq_mulVec_le (scale d c A) y
    have h3 : ∑ j, (y j) ^ 2 ≤ (b ^ 2)⁻¹ * ∑ j, (x j) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      dsimp only [y]
      rw [div_pow, div_eq_inv_mul]
      have hcj : b ^ 2 ≤ (c j) ^ 2 := by
        have := sq_le_sq₀ hb.le (abs_nonneg (c j)) |>.mpr (hc j)
        simpa [sq_abs] using this
      have hinv : ((c j) ^ 2)⁻¹ ≤ (b ^ 2)⁻¹ :=
        inv_anti₀ (sq_pos_of_pos hb) hcj
      exact mul_le_mul_of_nonneg_right hinv (sq_nonneg _)
    have h4 : a ^ 2 * ∑ i, (∑ j, A i j * x j) ^ 2 ≤
        ‖scale d c A‖ ^ 2 * ((b ^ 2)⁻¹ * ∑ j, (x j) ^ 2) :=
      le_trans h1 (le_trans h2 (mul_le_mul_of_nonneg_left h3 (sq_nonneg _)))
    have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
    have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
    have h5 : (‖scale d c A‖ / (a * b)) ^ 2 =
        (a ^ 2)⁻¹ * (‖scale d c A‖ ^ 2 * (b ^ 2)⁻¹) := by
      field_simp [ha.ne', hb.ne']
    rw [h5, mul_assoc]
    have h6 := mul_le_mul_of_nonneg_left h4 (inv_nonneg.mpr ha2.le)
    rw [← mul_assoc, inv_mul_cancel₀ ha2.ne', one_mul] at h6
    linarith
  exact (le_div_iff₀' hab).mp hbound

private lemma part7 (n : ℕ) (d c : Fin n → ℝ) (i j : Fin n) :
    ∃ A : Mat n, ‖A‖ = 1 ∧ ‖scale d c A‖ = |d i| * |c j| := by
  let A : Mat n := Matrix.of fun k l => if k = i ∧ l = j then 1 else 0
  refine ⟨A, ?_, ?_⟩
  · refine le_antisymm ?_ ?_
    · rw [l2_norm_le_iff A zero_le_one]
      intro x
      rw [one_pow, one_mul]
      have hterm : ∀ k : Fin n, (∑ l : Fin n, A k l * x l) ^ 2 =
          if k = i then (x j) ^ 2 else 0 := by
        intro k
        by_cases hki : k = i
        · subst hki
          simp [A]
        · simp [A, hki]
      simp_rw [hterm]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      exact Finset.single_le_sum (fun l _ => sq_nonneg (x l)) (Finset.mem_univ j)
    · have hrow : rowSq (A i) = 1 := by
        dsimp only [rowSq, A]
        simp
      have hsq : 1 ≤ ‖A‖ ^ 2 := by
        simpa [hrow] using rowSq_le_l2_norm_sq A i
      nlinarith [norm_nonneg A]
  · have hA1 : ‖A‖ = 1 := by
      refine le_antisymm ?_ ?_
      · rw [l2_norm_le_iff A zero_le_one]
        intro x
        rw [one_pow, one_mul]
        have hterm : ∀ k : Fin n, (∑ l : Fin n, A k l * x l) ^ 2 =
            if k = i then (x j) ^ 2 else 0 := by
          intro k
          by_cases hki : k = i
          · subst hki; simp [A]
          · simp [A, hki]
        simp_rw [hterm]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        exact Finset.single_le_sum (fun l _ => sq_nonneg (x l)) (Finset.mem_univ j)
      · have hrow : rowSq (A i) = 1 := by dsimp only [rowSq, A]; simp
        have hsq : 1 ≤ ‖A‖ ^ 2 := by simpa [hrow] using rowSq_le_l2_norm_sq A i
        nlinarith [norm_nonneg A]
    have hsc : scale d c A = (d i * c j) • A := by
      ext k l
      simp only [scale, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.smul_apply, smul_eq_mul]
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
        mul_ite, mul_zero]
      by_cases hkl : k = i ∧ l = j
      · rcases hkl with ⟨rfl, rfl⟩
        simp [A]
      · simp [A, hkl]
    rw [hsc, norm_smul, hA1, mul_one, Real.norm_eq_abs, abs_mul]

private lemma part8 (n : ℕ) (hn : 0 < n) (A : Mat n) (ε : ℝ) (hε : 0 < ε) :
    ∃ i : Fin n, Real.sqrt (rowSq (A i)) = maxRow n A ∧
      let d : Fin n → ℝ := fun j => if j = i then 2 + 2 * n / ε else 2
      (∀ j, 2 ≤ d j) ∧ ‖scale d (fun _ => 2) A‖ ≤ (1 + ε) * maxRow n (scale d (fun _ => 2) A) := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  obtain ⟨i, _, hi_max⟩ := Finset.exists_max_image Finset.univ
    (fun k : Fin n => Real.sqrt (rowSq (A k))) Finset.univ_nonempty
  set M := Real.sqrt (rowSq (A i))
  have hM_nonneg : 0 ≤ M := Real.sqrt_nonneg _
  have hM_eq : M = maxRow n A := by
    refine le_antisymm ?_ ?_
    · have := norm_le_pi_norm (fun k : Fin n => Real.sqrt (rowSq (A k))) i
      simpa [maxRow, M, Real.norm_eq_abs, abs_of_nonneg hM_nonneg] using this
    · dsimp only [maxRow]
      rw [pi_norm_le_iff_of_nonneg hM_nonneg]
      intro k
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact hi_max k (Finset.mem_univ k)
  refine ⟨i, hM_eq, ?_, ?_⟩
  · intro j
    by_cases hji : j = i
    · simp only [hji, ↓reduceIte]
      have : 0 ≤ 2 * (n : ℝ) / ε := by positivity
      linarith
    · simp [hji]
  · set d : Fin n → ℝ := fun j => if j = i then 2 + 2 * (n : ℝ) / ε else 2
    set B := scale d (fun _ => 2) A
    have hB_rowSq : ∀ k, rowSq (B k) = (2 * d k) ^ 2 * rowSq (A k) := by
      intro k
      dsimp only [rowSq, B, scale]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp [Matrix.mul_apply, Matrix.diagonal_apply]
      ring
    have hrow_le_M2 : ∀ k, rowSq (A k) ≤ M ^ 2 := by
      intro k
      have hk := hi_max k (Finset.mem_univ k)
      have hsq := sq_le_sq₀ (Real.sqrt_nonneg _) hM_nonneg |>.mpr hk
      rwa [Real.sq_sqrt (rowSq_nonneg (A k))] at hsq
    have hdi_eq : d i = 2 + 2 * (n : ℝ) / ε := by simp [d]
    have hdi_ge2 : 2 ≤ d i := by
      rw [hdi_eq]
      have : 0 ≤ 2 * (n : ℝ) / ε := by positivity
      linarith
    have hBi_sqrt : Real.sqrt (rowSq (B i)) = 2 * d i * M := by
      rw [hB_rowSq i, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)]
    have hmaxB_ge : 2 * d i * M ≤ maxRow n B := by
      have hle := norm_le_pi_norm (fun k : Fin n => Real.sqrt (rowSq (B k))) i
      rw [hBi_sqrt, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hle
      exact hle
    have hFrob : ‖B‖ ^ 2 ≤ ∑ k, rowSq (B k) := l2_norm_sq_le_frobenius B
    have hsplit : ∑ k, rowSq (B k) =
        rowSq (B i) + ∑ k ∈ Finset.univ.erase i, rowSq (B k) :=
      (Finset.add_sum_erase Finset.univ (fun k => rowSq (B k)) (Finset.mem_univ i)).symm
    have hBi_eq : rowSq (B i) = (2 * d i) ^ 2 * M ^ 2 := by
      rw [hB_rowSq i, Real.sq_sqrt (rowSq_nonneg (A i))]
    have herase : ∑ k ∈ Finset.univ.erase i, rowSq (B k) ≤ 16 * (n : ℝ) * M ^ 2 := by
      calc
        ∑ k ∈ Finset.univ.erase i, rowSq (B k)
            ≤ ∑ _k ∈ Finset.univ.erase i, (16 * M ^ 2) := by
              refine Finset.sum_le_sum fun k hk => ?_
              have hki : k ≠ i := (Finset.mem_erase.mp hk).1
              rw [hB_rowSq k]
              have hdk : d k = 2 := by simp [d, hki]
              rw [hdk]
              have h16 : (2 * (2 : ℝ)) ^ 2 = 16 := by norm_num
              rw [h16]
              exact mul_le_mul_of_nonneg_left (hrow_le_M2 k) (by norm_num)
        _ = ((Finset.univ.erase i).card : ℝ) * (16 * M ^ 2) := by
              simp
        _ ≤ (n : ℝ) * (16 * M ^ 2) := by
              have hcard : (Finset.univ.erase i).card ≤ n := by
                calc
                  (Finset.univ.erase i).card ≤ (Finset.univ : Finset (Fin n)).card :=
                    Finset.card_erase_le
                  _ = n := by simp
              have hcardR : ((Finset.univ.erase i).card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcard
              exact mul_le_mul_of_nonneg_right hcardR (by positivity)
        _ = 16 * (n : ℝ) * M ^ 2 := by ring
    have hBsq : ‖B‖ ^ 2 ≤ ((1 + ε) * (2 * d i * M)) ^ 2 := by
      have hcoeff : (2 * d i) ^ 2 + 16 * (n : ℝ) ≤ (1 + ε) ^ 2 * (2 * d i) ^ 2 := by
        have hεd : ε * d i = 2 * ε + 2 * (n : ℝ) := by
          rw [hdi_eq]
          field_simp [hε.ne']
        have h1 : 16 * (n : ℝ) ≤ 8 * (ε * d i) * d i := by nlinarith
        nlinarith [sq_nonneg (ε * d i)]
      have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
      have hmul := mul_le_mul_of_nonneg_right hcoeff hM2
      calc
        ‖B‖ ^ 2 ≤ rowSq (B i) + ∑ k ∈ Finset.univ.erase i, rowSq (B k) := by
          rw [← hsplit]; exact hFrob
        _ ≤ (2 * d i) ^ 2 * M ^ 2 + 16 * (n : ℝ) * M ^ 2 := by
          rw [hBi_eq]; linarith
        _ = ((2 * d i) ^ 2 + 16 * (n : ℝ)) * M ^ 2 := by ring
        _ ≤ (1 + ε) ^ 2 * (2 * d i) ^ 2 * M ^ 2 := hmul
        _ = ((1 + ε) * (2 * d i * M)) ^ 2 := by ring
    have hB_le : ‖B‖ ≤ (1 + ε) * (2 * d i * M) := by
      have hrhs_nonneg : 0 ≤ (1 + ε) * (2 * d i * M) := by positivity
      exact (sq_le_sq₀ (norm_nonneg B) hrhs_nonneg).mp hBsq
    exact le_trans hB_le (mul_le_mul_of_nonneg_left hmaxB_ge (by linarith))

end OMA.P_mo_495058

theorem OMA.solution : type_of% @OMA.S_mo_495058.main :=
  ⟨OMA.P_mo_495058.part1,
   OMA.P_mo_495058.part2,
   fun _ _ A => OMA.P_mo_495058.part3 A,
   OMA.P_mo_495058.part4,
   OMA.P_mo_495058.part5,
   OMA.P_mo_495058.part6,
   OMA.P_mo_495058.part7,
   OMA.P_mo_495058.part8⟩
