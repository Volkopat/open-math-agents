import OMAStatements.S_mse_2922967

namespace OMA.S_mse_2922967_Proof

open OMA.S_mse_2922967 Matrix
open scoped Matrix.Norms.Elementwise Pointwise

/-! ### Part 1: Basic properties of Hurwitz matrices -/

private lemma isHurwitz_transpose {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsHurwitz A) : IsHurwitz Aᵀ := by
  intro μ hμ
  have hmap : Aᵀ.map Complex.ofReal = (A.map Complex.ofReal)ᵀ := by
    ext i j; rfl
  rw [hmap, Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_transpose,
    ← Matrix.mem_spectrum_iff_isRoot_charpoly] at hμ
  exact hA μ hμ

private lemma isHurwitz_sub_smul {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsHurwitz A) {s : ℝ} (hs : 0 ≤ s) : IsHurwitz (A - s • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  intro μ hμ
  have hmem : μ + (s : ℂ) ∈ spectrum ℂ (A.map Complex.ofReal) := by
    rw [spectrum.mem_iff] at hμ ⊢
    have heq : algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) (μ + (s : ℂ)) - A.map Complex.ofReal =
        algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) μ -
          (A - s • (1 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofReal := by
      ext i j
      by_cases h : i = j
      · subst h; simp [Matrix.algebraMap_eq_diagonal]; ring
      · simp [Matrix.algebraMap_eq_diagonal, h]
    rw [heq]
    exact hμ
  have hlt := hA (μ + (s : ℂ)) hmem
  simp only [Complex.add_re, Complex.ofReal_re] at hlt
  linarith

private lemma trace_neg_of_isHurwitz {n : ℕ} (hn : 0 < n) {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsHurwitz A) : A.trace < 0 := by
  let Ac : Matrix (Fin n) (Fin n) ℂ := A.map Complex.ofReal
  have htr : (A.trace : ℂ) = Ac.trace := by
    simp [Ac, Matrix.trace]
  have hroots : Ac.trace = Ac.charpoly.roots.sum := Matrix.trace_eq_sum_roots_charpoly Ac
  have hre_ms : ∀ s : Multiset ℂ, s.sum.re = (s.map Complex.re).sum := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih => simp [ih]
  have hre : A.trace = (Ac.charpoly.roots.map Complex.re).sum := by
    have h1 := congrArg Complex.re (htr.trans hroots)
    simpa [hre_ms] using h1
  have hcard : Ac.charpoly.roots.card = n := by
    have hsp := IsAlgClosed.splits Ac.charpoly
    have hdeg : Ac.charpoly.natDegree = n := by
      simpa using Matrix.charpoly_natDegree_eq_dim Ac
    exact (Polynomial.Splits.natDegree_eq_card_roots hsp).symm.trans hdeg
  have hne : Ac.charpoly.roots ≠ 0 := by
    intro h0
    rw [h0, Multiset.card_zero] at hcard
    omega
  have hall : ∀ μ ∈ Ac.charpoly.roots, μ.re < 0 := by
    intro μ hμ
    have hroot : Ac.charpoly.IsRoot μ := Polynomial.isRoot_of_mem_roots hμ
    exact hA μ (Matrix.mem_spectrum_of_isRoot_charpoly hroot)
  rw [hre]
  obtain ⟨μ₀, hμ₀⟩ := Multiset.exists_mem_of_ne_zero hne
  obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem hμ₀
  rw [ht, Multiset.map_cons, Multiset.sum_cons]
  have h0 : μ₀.re < 0 := hall μ₀ hμ₀
  have hrest : (t.map Complex.re).sum ≤ 0 := by
    have hle : ∀ r ∈ t.map Complex.re, r ≤ 0 := by
      intro r hr
      rcases Multiset.mem_map.mp hr with ⟨μ, hμ, rfl⟩
      exact le_of_lt (hall μ (by rw [ht]; exact Multiset.mem_cons_of_mem hμ))
    clear h0 hne hcard hre hroots htr ht
    revert hle
    induction t using Multiset.induction_on with
    | empty => intro _; simp
    | cons a s ih =>
      intro hle
      rw [Multiset.map_cons, Multiset.sum_cons]
      have ha : a.re ≤ 0 := hle a.re (by simp)
      have hs : (s.map Complex.re).sum ≤ 0 := ih fun r hr => by
        rcases Multiset.mem_map.mp hr with ⟨μ, hμ, rfl⟩
        exact hle μ.re (Multiset.mem_map.mpr ⟨μ, Multiset.mem_cons_of_mem hμ, rfl⟩)
      linarith
  linarith

/-! ### Part 2: Invertibility and adjointness of the Lyapunov operator -/

private def lyapOp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun W := -(A * W + W * Aᵀ)
  map_add' W₁ W₂ := by
    simp only [mul_add, add_mul]
    abel
  map_smul' c W := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_neg, RingHom.id_apply]

private lemma aeval_mul_comm_of_mul_eq {n : ℕ} {B C W : Matrix (Fin n) (Fin n) ℂ}
    (h : B * W = W * C) (p : Polynomial ℂ) :
    Polynomial.aeval B p * W = W * Polynomial.aeval C p := by
  induction p using Polynomial.induction_on' with
  | add p q ihp ihq =>
    simp only [map_add, add_mul, mul_add, ihp, ihq]
  | monomial k a =>
    simp only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul,
      Matrix.mul_smul, one_mul, mul_one]
    congr 1
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_succ, mul_assoc, h, ← mul_assoc, ih, mul_assoc]

private lemma lyapOp_injective {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsHurwitz A) : Function.Injective (lyapOp A) := by
  rw [injective_iff_map_eq_zero]
  intro W hW
  have hAW : A * W = W * (-Aᵀ) := by
    have h0 : -(A * W + W * Aᵀ) = 0 := hW
    have h1 : A * W + W * Aᵀ = 0 := neg_eq_zero.mp h0
    rw [Matrix.mul_neg]
    exact eq_neg_of_add_eq_zero_left h1
  let Ac : Matrix (Fin n) (Fin n) ℂ := A.map Complex.ofReal
  let Wc : Matrix (Fin n) (Fin n) ℂ := W.map Complex.ofReal
  have hAWc : Ac * Wc = Wc * (-Acᵀ) := by
    ext i j
    have hij := congrArg Complex.ofReal (congrFun (congrFun hAW i) j)
    simpa [Ac, Wc, Matrix.mul_apply, Matrix.transpose_apply] using hij
  have hCH : Wc * Polynomial.aeval (-Acᵀ) Ac.charpoly = 0 := by
    have hcomm := aeval_mul_comm_of_mul_eq hAWc Ac.charpoly
    rw [Matrix.aeval_self_charpoly Ac, zero_mul] at hcomm
    exact hcomm.symm
  have hunit : IsUnit (Polynomial.aeval (-Acᵀ) Ac.charpoly) := by
    have hfac : Ac.charpoly = (Ac.charpoly.roots.map (fun μ => Polynomial.X - Polynomial.C μ)).prod :=
      (IsAlgClosed.splits Ac.charpoly).eq_prod_roots_of_monic Ac.charpoly_monic
    have hfac_unit : ∀ μ ∈ Ac.charpoly.roots,
        IsUnit (Polynomial.aeval (-Acᵀ) (Polynomial.X - Polynomial.C μ)) := by
      intro μ hμ
      have hμ_spec : μ ∈ spectrum ℂ Ac :=
        Matrix.mem_spectrum_of_isRoot_charpoly (Polynomial.isRoot_of_mem_roots hμ)
      have hμ_neg : μ.re < 0 := hA μ hμ_spec
      have hneg_not : -μ ∉ spectrum ℂ Acᵀ := by
        intro hmem
        rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_transpose,
          ← Matrix.mem_spectrum_iff_isRoot_charpoly] at hmem
        have := hA (-μ) hmem
        simp only [Complex.neg_re] at this
        linarith
      rw [spectrum.mem_iff, not_not] at hneg_not
      have heq : Polynomial.aeval (-Acᵀ) (Polynomial.X - Polynomial.C μ) =
          algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) (-μ) - Acᵀ := by
        simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, map_neg]
        abel
      rw [heq]
      exact hneg_not
    obtain ⟨l, hl⟩ := Quotient.exists_rep Ac.charpoly.roots
    have hl' : Ac.charpoly.roots = ↑l := hl.symm
    rw [hfac, hl', Multiset.map_coe, Multiset.prod_coe, map_list_prod]
    have hprod_unit : ∀ (L : List ℂ),
        (∀ μ ∈ L, IsUnit (Polynomial.aeval (-Acᵀ) (Polynomial.X - Polynomial.C μ))) →
        IsUnit (L.map (fun μ => Polynomial.aeval (-Acᵀ) (Polynomial.X - Polynomial.C μ))).prod := by
      intro L
      induction L with
      | nil => intro _; simp
      | cons a s ih =>
        intro hs
        rw [List.map_cons, List.prod_cons]
        exact (hs a (by simp)).mul (ih (fun μ hμ => hs μ (List.mem_cons_of_mem a hμ)))
    rw [List.map_map]
    exact hprod_unit l (fun μ hμ => hfac_unit μ (by rw [hl']; exact hμ))
  obtain ⟨u, hu⟩ := hunit
  rw [← hu] at hCH
  have hWc0 : Wc = 0 := by
    have := congrArg (· * (↑u⁻¹ : Matrix (Fin n) (Fin n) ℂ)) hCH
    simpa [mul_assoc] using this
  ext i j
  have hij := congrFun (congrFun hWc0 i) j
  simpa [Wc] using hij

private noncomputable def lyapEquiv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsHurwitz A) : Matrix (Fin n) (Fin n) ℝ ≃ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  LinearEquiv.ofInjectiveEndo (lyapOp A) (lyapOp_injective hA)

private lemma lyapEquiv_symm_transpose {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsHurwitz A) {U : Matrix (Fin n) (Fin n) ℝ} (hU : Uᵀ = U) :
    ((lyapEquiv A hA).symm U)ᵀ = (lyapEquiv A hA).symm U := by
  let W := (lyapEquiv A hA).symm U
  have hW : lyapOp A W = U := (lyapEquiv A hA).apply_symm_apply U
  have hWT : lyapOp A Wᵀ = U := by
    dsimp [lyapOp] at hW ⊢
    calc -(A * Wᵀ + Wᵀ * Aᵀ) = (-(A * W + W * Aᵀ))ᵀ := by
          simp [Matrix.transpose_add, Matrix.transpose_mul, add_comm]
      _ = Uᵀ := congrArg Matrix.transpose hW
      _ = U := hU
  exact lyapOp_injective hA (hWT.trans hW.symm)

private lemma trace_lyapOp_adj {n : ℕ} (A R W : Matrix (Fin n) (Fin n) ℝ) :
    (lyapOp Aᵀ R * W).trace = (R * lyapOp A W).trace := by
  dsimp [lyapOp]
  simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.add_mul, Matrix.mul_add,
    Matrix.trace_neg, Matrix.trace_add, Matrix.transpose_transpose]
  rw [Matrix.mul_assoc Aᵀ R W, Matrix.trace_mul_comm Aᵀ (R * W), Matrix.mul_assoc R W Aᵀ,
    Matrix.mul_assoc R A W]
  ring

private lemma trace_lyapEquiv_symm_adj {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsHurwitz A) (R U : Matrix (Fin n) (Fin n) ℝ) :
    (R * (lyapEquiv A hA).symm U).trace =
      ((lyapEquiv Aᵀ (isHurwitz_transpose hA)).symm R * U).trace := by
  let Y := (lyapEquiv Aᵀ (isHurwitz_transpose hA)).symm R
  let W := (lyapEquiv A hA).symm U
  have hY : lyapOp Aᵀ Y = R := (lyapEquiv Aᵀ (isHurwitz_transpose hA)).apply_symm_apply R
  have hW : lyapOp A W = U := (lyapEquiv A hA).apply_symm_apply U
  calc (R * W).trace = (lyapOp Aᵀ Y * W).trace := by rw [hY]
    _ = (Y * lyapOp A W).trace := trace_lyapOp_adj A Y W
    _ = (Y * U).trace := by rw [hW]

/-! ### Part 3: Homotopy proof that `lyapEquiv.symm` preserves `PosDef` and `PosSemidef` -/

private lemma abs_dotProduct_mulVec_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) (hv : v ⬝ᵥ v = 1) :
    |v ⬝ᵥ (M *ᵥ v)| ≤ (n : ℝ) ^ 2 * ‖M‖ := by
  have hvi : ∀ i, |v i| ≤ 1 := by
    intro i
    have hsq : (v i) ^ 2 ≤ 1 := by
      have h1 : (v i) ^ 2 ≤ ∑ j, (v j) ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
      have hdot : v ⬝ᵥ v = ∑ j, (v j) ^ 2 := by
        simp [dotProduct, sq]
      linarith
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have hsum : v ⬝ᵥ (M *ᵥ v) = ∑ i : Fin n, ∑ j : Fin n, v i * (M i j * v j) := by
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [hsum]
  calc |∑ i : Fin n, ∑ j : Fin n, v i * (M i j * v j)|
      ≤ ∑ i : Fin n, |∑ j : Fin n, v i * (M i j * v j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, |v i * (M i j * v j)| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, ‖M‖ := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul, abs_mul]
        have hMij : |M i j| ≤ ‖M‖ := by
          have : ‖M i j‖ ≤ ‖M‖ := Matrix.norm_entry_le_entrywise_sup_norm M
          simpa [Real.norm_eq_abs] using this
        have h1 : |M i j| * |v j| ≤ ‖M‖ * 1 :=
          mul_le_mul hMij (hvi j) (abs_nonneg _) (norm_nonneg M)
        have h2 : |v i| * (|M i j| * |v j|) ≤ 1 * (‖M‖ * 1) :=
          mul_le_mul (hvi i) h1 (by positivity) (by norm_num)
        linarith
    _ = (n : ℝ) ^ 2 * ‖M‖ := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring

private lemma posDef_iff_unit_sphere {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hH : M.IsHermitian) :
    M.PosDef ↔ ∀ v : Fin n → ℝ, v ⬝ᵥ v = 1 → 0 < v ⬝ᵥ (M *ᵥ v) := by
  constructor
  · intro hM v hv
    have hvne : v ≠ 0 := by
      intro h0; rw [h0] at hv; simp at hv
    simpa [star] using hM.dotProduct_mulVec_pos hvne
  · intro h
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hH fun v hv => ?_
    have hdot_pos : 0 < v ⬝ᵥ v := by
      have h1 : ∃ i, v i ≠ 0 := Function.ne_iff.mp hv
      rcases h1 with ⟨i, hi⟩
      have hsq : 0 < (v i) ^ 2 := sq_pos_of_ne_zero hi
      have hle : (v i) ^ 2 ≤ ∑ j, (v j) ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
      have hdot : v ⬝ᵥ v = ∑ j, (v j) ^ 2 := by simp [dotProduct, sq]
      linarith
    let c := Real.sqrt (v ⬝ᵥ v)
    have hc : 0 < c := Real.sqrt_pos.mpr hdot_pos
    let u := c⁻¹ • v
    have hu : u ⬝ᵥ u = 1 := by
      simp only [u, dotProduct_smul, smul_dotProduct, smul_eq_mul]
      rw [← mul_assoc, ← mul_inv, Real.mul_self_sqrt (le_of_lt hdot_pos),
        inv_mul_cancel₀ (ne_of_gt hdot_pos)]
    have hpos := h u hu
    have heq : u ⬝ᵥ (M *ᵥ u) = c⁻¹ ^ 2 * (v ⬝ᵥ (M *ᵥ v)) := by
      simp only [u, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
      ring
    rw [heq] at hpos
    have hc2 : 0 < c⁻¹ ^ 2 := by positivity
    have hres : 0 < v ⬝ᵥ (M *ᵥ v) := pos_of_mul_pos_right hpos (le_of_lt hc2)
    simpa [star] using hres

private lemma unit_sphere_isCompact (n : ℕ) :
    IsCompact {v : Fin n → ℝ | v ⬝ᵥ v = 1} := by
  have hclosed : IsClosed {v : Fin n → ℝ | v ⬝ᵥ v = 1} := by
    have hcont : Continuous (fun v : Fin n → ℝ => v ⬝ᵥ v) := by
      simp only [dotProduct]
      fun_prop
    exact isClosed_eq hcont continuous_const
  have hbdd : Bornology.IsBounded {v : Fin n → ℝ | v ⬝ᵥ v = 1} := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨1, fun v hv => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    rw [Real.norm_eq_abs]
    have hsq : (v i) ^ 2 ≤ 1 := by
      have h1 : (v i) ^ 2 ≤ ∑ j, (v j) ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
      have hdot : v ⬝ᵥ v = ∑ j, (v j) ^ 2 := by simp [dotProduct, sq]
      rw [hv] at hdot
      linarith
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  exact Metric.isCompact_of_isClosed_isBounded hclosed hbdd

private lemma posDef_exists_margin {n : ℕ} (hn : 0 < n) {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosDef) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v : Fin n → ℝ, v ⬝ᵥ v = 1 → δ ≤ v ⬝ᵥ (M *ᵥ v) := by
  let S := {v : Fin n → ℝ | v ⬝ᵥ v = 1}
  have hne : S.Nonempty := by
    refine ⟨Pi.single ⟨0, hn⟩ 1, ?_⟩
    simp [S, dotProduct, Pi.single_apply]
  have hcont : ContinuousOn (fun v : Fin n → ℝ => v ⬝ᵥ (M *ᵥ v)) S := by
    have : Continuous (fun v : Fin n → ℝ => v ⬝ᵥ (M *ᵥ v)) := by
      simp only [dotProduct, Matrix.mulVec]
      fun_prop
    exact this.continuousOn
  obtain ⟨v₀, hv₀, hmin⟩ := (unit_sphere_isCompact n).exists_isMinOn hne hcont
  refine ⟨v₀ ⬝ᵥ (M *ᵥ v₀), (posDef_iff_unit_sphere hM.isHermitian).mp hM v₀ hv₀, fun v hv => hmin hv⟩

private lemma mulVec_eq_zero_of_posSemidef_quad_eq_zero {n : ℕ}
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosSemidef) {v : Fin n → ℝ}
    (hv : v ⬝ᵥ (M *ᵥ v) = 0) : M *ᵥ v = 0 := by
  have hsym : Mᵀ = M := by simpa [Matrix.IsHermitian] using hM.isHermitian
  have horth : ∀ w : Fin n → ℝ, w ⬝ᵥ (M *ᵥ v) = 0 := by
    intro w
    by_contra hne
    let a := w ⬝ᵥ (M *ᵥ w)
    let b := w ⬝ᵥ (M *ᵥ v)
    have hquad : ∀ t : ℝ, 0 ≤ t ^ 2 * a + 2 * t * b := by
      intro t
      have h0 : 0 ≤ (v + t • w) ⬝ᵥ (M *ᵥ (v + t • w)) := by
        simpa only [star_trivial] using hM.dotProduct_mulVec_nonneg (v + t • w)
      have hvw : v ⬝ᵥ (M *ᵥ w) = w ⬝ᵥ (M *ᵥ v) := by
        simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        have hij : M j i = M i j := (congrFun (congrFun hsym j) i).symm
        rw [hij]; ring
      have hexp : (v + t • w) ⬝ᵥ (M *ᵥ (v + t • w)) =
          v ⬝ᵥ (M *ᵥ v) + t * (v ⬝ᵥ (M *ᵥ w)) + t * (w ⬝ᵥ (M *ᵥ v)) + t ^ 2 * (w ⬝ᵥ (M *ᵥ w)) := by
        simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
          dotProduct_smul, smul_dotProduct, smul_eq_mul]
        ring
      rw [hexp, hv, hvw] at h0
      dsimp [a, b]
      linarith
    have ha : 0 ≤ a := by simpa only [a, star_trivial] using hM.dotProduct_mulVec_nonneg w
    by_cases ha0 : a = 0
    · have h1 := hquad (-b)
      rw [ha0] at h1
      nlinarith [sq_pos_of_ne_zero hne]
    · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have h1 := hquad (-b / a)
      have hcalc : (-b / a) ^ 2 * a + 2 * (-b / a) * b = -(b ^ 2 / a) := by
        field_simp
        ring
      rw [hcalc] at h1
      have hpos : 0 < b ^ 2 / a := div_pos (sq_pos_of_ne_zero hne) hap
      linarith
  ext i
  have := horth (Pi.single i 1)
  simpa [dotProduct, Pi.single_apply] using this

private lemma linearMap_matrix_norm_bound {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : Matrix (Fin n) (Fin n) ℝ, ‖T M‖ ≤ C * ‖M‖ := by
  refine ⟨∑ i : Fin n, ∑ j : Fin n, ‖T (Matrix.single i j 1)‖,
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _, fun M => ?_⟩
  have hdecomp : M = ∑ i : Fin n, ∑ j : Fin n, M i j • Matrix.single i j (1 : ℝ) := by
    ext a b
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.single_apply]
    rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single b]
      · simp
      · intro j _ hjb; split_ifs <;> simp_all
      · intro hb; exact absurd (Finset.mem_univ b) hb
    · intro i _ hia
      refine Finset.sum_eq_zero fun j _ => ?_
      split_ifs <;> simp_all
    · intro ha; exact absurd (Finset.mem_univ a) ha
  conv_lhs => rw [hdecomp]
  rw [map_sum]
  calc ‖∑ i : Fin n, T (∑ j : Fin n, M i j • Matrix.single i j 1)‖
      ≤ ∑ i : Fin n, ‖T (∑ j : Fin n, M i j • Matrix.single i j 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, ‖M i j • T (Matrix.single i j 1)‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [map_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [map_smul]
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, ‖M‖ * ‖T (Matrix.single i j 1)‖ := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (Matrix.norm_entry_le_entrywise_sup_norm M) (norm_nonneg _)
    _ = (∑ i : Fin n, ∑ j : Fin n, ‖T (Matrix.single i j 1)‖) * ‖M‖ := by
        simp only [← Finset.mul_sum]
        ring

private lemma lyapEquiv_symm_posDef {n : ℕ} (hn : 0 < n) {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsHurwitz A) {U : Matrix (Fin n) (Fin n) ℝ} (hU : U.PosDef) :
    ((lyapEquiv A hA).symm U).PosDef := by
  let W : ℝ → Matrix (Fin n) (Fin n) ℝ := fun s =>
    if hs : 0 ≤ s then (lyapEquiv (A - s • 1) (isHurwitz_sub_smul hA hs)).symm U else 0
  have hW_eq : ∀ s : ℝ, (hs : 0 ≤ s) → lyapOp A (W s) + (2 * s) • W s = U := by
    intro s hs
    have h1 : lyapOp (A - s • 1) (W s) = U := by
      simp only [W, dif_pos hs]
      exact (lyapEquiv (A - s • 1) (isHurwitz_sub_smul hA hs)).apply_symm_apply U
    have h2 : lyapOp (A - s • 1) (W s) = lyapOp A (W s) + (2 * s) • W s := by
      dsimp [lyapOp]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.transpose_sub, Matrix.transpose_smul,
        Matrix.transpose_one, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, two_mul,
        add_smul]
      abel
    rw [← h2]
    exact h1
  have hW_sym : ∀ s : ℝ, 0 ≤ s → (W s).IsHermitian := by
    intro s hs
    simp only [W, dif_pos hs]
    have hUsym : Uᵀ = U := by simpa [Matrix.IsHermitian] using hU.isHermitian
    have hT := lyapEquiv_symm_transpose (isHurwitz_sub_smul hA hs) hUsym
    simpa [Matrix.IsHermitian] using hT
  have hW_cont_norm : ∀ s ∈ Set.Ici (0 : ℝ), ∀ ε > 0, ∃ δ > 0,
      ∀ t ∈ Set.Ici (0 : ℝ), |t - s| < δ → ‖W t - W s‖ < ε := by
    intro s hs ε hε
    let invL := (lyapEquiv (A - s • 1) (isHurwitz_sub_smul hA hs)).symm.toLinearMap
    obtain ⟨C₀, hC₀_nn, hinvL_bdd⟩ := linearMap_matrix_norm_bound invL
    let C := C₀ + 1
    have hC : 0 < C := by positivity
    let δ := min (1 / (4 * C)) (ε / (4 * C * (‖W s‖ + 1)))
    have hδ : 0 < δ := lt_min (by positivity) (by positivity)
    refine ⟨δ, hδ, fun t ht hdist => ?_⟩
    have hdiff_op : lyapOp (A - s • 1) (W t - W s) = (2 * (s - t)) • W t := by
      have hts : lyapOp A (W t) + (2 * t) • W t = U := hW_eq t ht
      have hss : lyapOp A (W s) + (2 * s) • W s = U := hW_eq s hs
      have hexp : ∀ M, lyapOp (A - s • 1) M = lyapOp A M + (2 * s) • M := by
        intro M
        dsimp [lyapOp]
        simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.transpose_sub, Matrix.transpose_smul,
          Matrix.transpose_one, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, two_mul,
          add_smul]
        abel
      rw [map_sub, hexp, hexp, hss]
      have hsub : lyapOp A (W t) = U - (2 * t) • W t := eq_sub_of_add_eq hts
      rw [hsub]
      calc U - (2 * t) • W t + (2 * s) • W t - U = (2 * s - 2 * t) • W t := by
            rw [sub_smul]; abel
        _ = (2 * (s - t)) • W t := by congr 1; ring
    have hdiff : W t - W s = (2 * (s - t)) • invL (W t) := by
      have h1 := congrArg (lyapEquiv (A - s • 1) (isHurwitz_sub_smul hA hs)).symm hdiff_op
      change (lyapEquiv (A - s • 1) (isHurwitz_sub_smul hA hs)).symm
        ((lyapEquiv (A - s • 1) (isHurwitz_sub_smul hA hs)) (W t - W s)) = _ at h1
      rw [(lyapEquiv (A - s • 1) (isHurwitz_sub_smul hA hs)).symm_apply_apply, map_smul] at h1
      exact h1
    have hst : |s - t| < δ := by rwa [abs_sub_comm]
    have hnorm_diff : ‖W t - W s‖ ≤ 2 * |s - t| * C * ‖W t‖ := by
      rw [hdiff, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have h1 : ‖invL (W t)‖ ≤ C₀ * ‖W t‖ := hinvL_bdd (W t)
      have h2 : C₀ * ‖W t‖ ≤ C * ‖W t‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      have h3 : 2 * |s - t| * ‖invL (W t)‖ ≤ 2 * |s - t| * (C * ‖W t‖) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
      linarith
    have h2C : 2 * |s - t| * C ≤ 1 / 2 := by
      have h1 : |s - t| ≤ 1 / (4 * C) := le_trans (le_of_lt hst) (min_le_left _ _)
      have h2 : 2 * |s - t| * C ≤ 2 * (1 / (4 * C)) * C := by
        have : 0 ≤ 2 * C := by positivity
        nlinarith
      have h3 : 2 * (1 / (4 * C)) * C = 1 / 2 := by field_simp; ring
      linarith
    have hWt_le : ‖W t‖ ≤ 2 * ‖W s‖ := by
      have htri : ‖W t‖ ≤ ‖W t - W s‖ + ‖W s‖ := by
        simpa [sub_add_cancel] using norm_add_le (W t - W s) (W s)
      have hhalf : ‖W t - W s‖ ≤ (1 / 2) * ‖W t‖ :=
        hnorm_diff.trans (mul_le_mul_of_nonneg_right h2C (norm_nonneg _))
      linarith
    have hbound : ‖W t - W s‖ < ε := by
      have h1 : |s - t| < ε / (4 * C * (‖W s‖ + 1)) := lt_of_lt_of_le hst (min_le_right _ _)
      have hden : 0 < 4 * C * (‖W s‖ + 1) := by positivity
      have h2 : |s - t| * (4 * C * (‖W s‖ + 1)) < ε := (lt_div_iff₀ hden).mp h1
      have h3 : 2 * |s - t| * C * ‖W t‖ ≤ |s - t| * (4 * C * (‖W s‖ + 1)) := by
        have h4 : 0 ≤ 2 * |s - t| * C := by positivity
        nlinarith [norm_nonneg (W s)]
      linarith
    exact hbound
  have hW_cont : ContinuousOn W (Set.Ici 0) := by
    refine continuousOn_pi.mpr fun i => continuousOn_pi.mpr fun j => ?_
    rw [Metric.continuousOn_iff]
    intro s hs ε hε
    obtain ⟨δ, hδ, h⟩ := hW_cont_norm s hs ε hε
    refine ⟨δ, hδ, fun t ht hdist => ?_⟩
    rw [Real.dist_eq] at hdist ⊢
    have h1 : ‖(W t - W s) i j‖ ≤ ‖W t - W s‖ := Matrix.norm_entry_le_entrywise_sup_norm (W t - W s)
    have h2 : |W t i j - W s i j| ≤ ‖W t - W s‖ := by
      simpa [Real.norm_eq_abs, Matrix.sub_apply] using h1
    exact lt_of_le_of_lt h2 (h t ht hdist)
  -- Step 1: For sufficiently large s₀ > 0, (W s₀).PosDef
  obtain ⟨δU, hδU_pos, hδU⟩ := posDef_exists_margin hn hU
  obtain ⟨CL, hCL_nn, hL_bdd⟩ := linearMap_matrix_norm_bound (lyapOp A)
  have hn_pos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  let s₀ : ℝ := max (CL + 1) ((CL + 1) * (‖U‖ + 1) * (n : ℝ) ^ 2 / δU + CL)
  have hs₀_pos : 0 < s₀ := by
    have : 0 < CL + 1 := by positivity
    exact lt_of_lt_of_le this (le_max_left _ _)
  have hs₀_gt_CL : CL < 2 * s₀ := by
    have : CL + 1 ≤ s₀ := le_max_left _ _
    linarith
  have hs₀_posDef : (W s₀).PosDef := by
    have hscaled : ((2 * s₀) • W s₀).PosDef := by
      rw [posDef_iff_unit_sphere]
      · intro v hv
        have heq : (2 * s₀) • W s₀ - U = -(lyapOp A (W s₀)) := by
          have h1 := hW_eq s₀ (le_of_lt hs₀_pos)
          exact eq_neg_of_add_eq_zero_left (by rw [sub_add_eq_add_sub, add_comm, h1, sub_self])
        have hnorm_W : ‖W s₀‖ ≤ ‖U‖ / (2 * s₀ - CL) := by
          have h1 : (2 * s₀) * ‖W s₀‖ ≤ ‖U‖ + CL * ‖W s₀‖ := by
            have h2 : (2 * s₀) • W s₀ = U - lyapOp A (W s₀) := by
              have := hW_eq s₀ (le_of_lt hs₀_pos)
              exact eq_sub_of_add_eq' this
            have h3 : ‖(2 * s₀) • W s₀‖ ≤ ‖U‖ + ‖lyapOp A (W s₀)‖ := by
              rw [h2]; exact norm_sub_le U (lyapOp A (W s₀))
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)] at h3
            have h4 : ‖lyapOp A (W s₀)‖ ≤ CL * ‖W s₀‖ := hL_bdd (W s₀)
            linarith
          have hden : 0 < 2 * s₀ - CL := by linarith
          rw [le_div_iff₀ hden]
          linarith
        have hnorm_err : ‖(2 * s₀) • W s₀ - U‖ < δU / (n : ℝ) ^ 2 := by
          rw [heq, norm_neg]
          have h1 : ‖lyapOp A (W s₀)‖ ≤ CL * ‖W s₀‖ := hL_bdd (W s₀)
          have hden : 0 < 2 * s₀ - CL := by linarith
          have h2 : CL * ‖W s₀‖ ≤ CL * (‖U‖ / (2 * s₀ - CL)) :=
            mul_le_mul_of_nonneg_left hnorm_W hCL_nn
          have h3 : (CL + 1) * (‖U‖ + 1) * (n : ℝ) ^ 2 / δU ≤ 2 * s₀ - CL := by
            have hmax : (CL + 1) * (‖U‖ + 1) * (n : ℝ) ^ 2 / δU + CL ≤ s₀ := le_max_right _ _
            linarith
          have h4 : CL * ‖U‖ * (n : ℝ) ^ 2 < δU * (2 * s₀ - CL) := by
            have h5 : (CL + 1) * (‖U‖ + 1) * (n : ℝ) ^ 2 ≤ (2 * s₀ - CL) * δU :=
              (div_le_iff₀ hδU_pos).mp h3
            have h6 : CL * ‖U‖ < (CL + 1) * (‖U‖ + 1) := by nlinarith [hCL_nn, norm_nonneg U]
            nlinarith
          have h5 : CL * (‖U‖ / (2 * s₀ - CL)) < δU / (n : ℝ) ^ 2 := by
            rw [← mul_div_assoc, div_lt_div_iff₀ hden hn_pos]
            exact h4
          linarith
        have herr := abs_dotProduct_mulVec_le ((2 * s₀) • W s₀ - U) v hv
        have hquad_err : |v ⬝ᵥ (((2 * s₀) • W s₀ - U) *ᵥ v)| < δU := by
          have h1 : (n : ℝ) ^ 2 * ‖(2 * s₀) • W s₀ - U‖ < (n : ℝ) ^ 2 * (δU / (n : ℝ) ^ 2) :=
            mul_lt_mul_of_pos_left hnorm_err hn_pos
          rw [mul_div_cancel₀ _ (ne_of_gt hn_pos)] at h1
          linarith
        have hsplit : v ⬝ᵥ (((2 * s₀) • W s₀) *ᵥ v) =
            v ⬝ᵥ (U *ᵥ v) + v ⬝ᵥ (((2 * s₀) • W s₀ - U) *ᵥ v) := by
          simp only [Matrix.sub_mulVec, dotProduct_sub]
          ring
        have hUlb := hδU v hv
        linarith [(abs_lt.mp hquad_err).1]
      · ext i j
        have hij : W s₀ j i = W s₀ i j := by
          simpa [Matrix.conjTranspose_apply] using congrFun (congrFun (hW_sym s₀ (le_of_lt hs₀_pos)).eq i) j
        simp [Matrix.conjTranspose_apply, hij]
    have hinv : (2 * s₀)⁻¹ • ((2 * s₀) • W s₀) = W s₀ := by
      rw [smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
    rw [← hinv]
    exact hscaled.smul (by positivity)
  -- Step 2: Connectedness on [0, s₀]
  let I := Set.Icc (0 : ℝ) s₀
  have hI_conn : IsConnected I := isConnected_Icc (le_of_lt hs₀_pos)
  haveI : ConnectedSpace I := Subtype.connectedSpace hI_conn
  let O₁ : Set I := {s | (W s.1).PosDef}
  let O₂ : Set I := {s | ∃ v : Fin n → ℝ, v ⬝ᵥ (W s.1 *ᵥ v) < 0}
  have hW_sub_cont : Continuous (fun s : I => W s.1) :=
    (hW_cont.mono (fun x hx => hx.1)).restrict
  have hO₁_open : IsOpen O₁ := by
    rw [Metric.isOpen_iff]
    intro s hs
    obtain ⟨δ, hδ_pos, hδ⟩ := posDef_exists_margin hn hs
    obtain ⟨r, hr_pos, hr⟩ := hW_cont_norm s.1 s.2.1 (δ / (n : ℝ) ^ 2) (by positivity)
    refine ⟨r, hr_pos, fun t ht => ?_⟩
    have hdist : ‖W t.1 - W s.1‖ < δ / (n : ℝ) ^ 2 := by
      have hts : |t.1 - s.1| < r := by simpa [Subtype.dist_eq, Real.dist_eq] using ht
      exact hr t.1 t.2.1 hts
    change (W t.1).PosDef
    rw [posDef_iff_unit_sphere (hW_sym t.1 t.2.1)]
    intro v hv
    have herr := abs_dotProduct_mulVec_le (W t.1 - W s.1) v hv
    have hlt : |v ⬝ᵥ ((W t.1 - W s.1) *ᵥ v)| < δ := by
      have h1 : (n : ℝ) ^ 2 * ‖W t.1 - W s.1‖ < (n : ℝ) ^ 2 * (δ / (n : ℝ) ^ 2) :=
        mul_lt_mul_of_pos_left hdist hn_pos
      rw [mul_div_cancel₀ _ (ne_of_gt hn_pos)] at h1
      linarith
    have hsplit : v ⬝ᵥ (W t.1 *ᵥ v) = v ⬝ᵥ (W s.1 *ᵥ v) + v ⬝ᵥ ((W t.1 - W s.1) *ᵥ v) := by
      simp only [Matrix.sub_mulVec, dotProduct_sub]
      ring
    linarith [hδ v hv, (abs_lt.mp hlt).1]
  have hO₂_open : IsOpen O₂ := by
    rw [isOpen_iff_mem_nhds]
    intro s hs
    rcases hs with ⟨v, hv⟩
    have hcont_v : Continuous (fun t : I => v ⬝ᵥ (W t.1 *ᵥ v)) := by
      have h1 : Continuous (fun M : Matrix (Fin n) (Fin n) ℝ => v ⬝ᵥ (M *ᵥ v)) := by
        simp only [dotProduct, Matrix.mulVec]
        fun_prop
      exact h1.comp hW_sub_cont
    have hopen : IsOpen {t : I | v ⬝ᵥ (W t.1 *ᵥ v) < 0} := isOpen_lt hcont_v continuous_const
    exact Filter.mem_of_superset (hopen.mem_nhds hv) (fun t ht => ⟨v, ht⟩)
  have hdisj : Disjoint O₁ O₂ := by
    rw [Set.disjoint_left]
    intro s hs1 hs2
    rcases hs2 with ⟨v, hv⟩
    have hge : 0 ≤ v ⬝ᵥ (W s.1 *ᵥ v) := by simpa [star] using hs1.posSemidef.dotProduct_mulVec_nonneg v
    linarith
  have hcover : O₁ ∪ O₂ = Set.univ := by
    ext s
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    by_cases h2 : s ∈ O₂
    · exact Or.inr h2
    · left
      have hnonneg : ∀ v : Fin n → ℝ, 0 ≤ v ⬝ᵥ (W s.1 *ᵥ v) := by
        intro v
        by_contra hlt
        push Not at hlt
        exact h2 ⟨v, hlt⟩
      have hpsd : (W s.1).PosSemidef := Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hW_sym s.1 s.2.1) (fun v => by simpa [star] using hnonneg v)
      refine Matrix.PosDef.of_dotProduct_mulVec_pos (hW_sym s.1 s.2.1) fun v hvne => ?_
      have hge := hnonneg v
      rcases lt_or_eq_of_le hge with hpos | heq0
      · simpa [star] using hpos
      · exfalso
        have hWv : W s.1 *ᵥ v = 0 := mulVec_eq_zero_of_posSemidef_quad_eq_zero hpsd heq0.symm
        have hAs : lyapOp (A - s.1 • 1) (W s.1) = U := by
          simp only [W, dif_pos s.2.1]
          exact (lyapEquiv (A - s.1 • 1) (isHurwitz_sub_smul hA s.2.1)).apply_symm_apply U
        have hU0 : v ⬝ᵥ (U *ᵥ v) = 0 := by
          rw [← hAs]
          dsimp [lyapOp]
          simp only [Matrix.neg_mulVec, Matrix.add_mulVec, dotProduct_neg, dotProduct_add,
            ← Matrix.mulVec_mulVec, hWv, Matrix.mulVec_zero, dotProduct_zero, zero_add]
          have hsym : (W s.1)ᵀ = W s.1 := by simpa [Matrix.IsHermitian] using hW_sym s.1 s.2.1
          have h1 : v ⬝ᵥ (W s.1 *ᵥ ((A - s.1 • 1)ᵀ *ᵥ v)) =
              ((A - s.1 • 1)ᵀ *ᵥ v) ⬝ᵥ (W s.1 *ᵥ v) := by
            let w := (A - s.1 • 1)ᵀ *ᵥ v
            change v ⬝ᵥ (W s.1 *ᵥ w) = w ⬝ᵥ (W s.1 *ᵥ v)
            simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            have hij : (W s.1) j i = (W s.1) i j := (congrFun (congrFun hsym j) i).symm
            rw [hij]; ring
          rw [h1, hWv, dotProduct_zero, neg_zero]
        have hUpos : 0 < v ⬝ᵥ (U *ᵥ v) := by simpa [star] using hU.dotProduct_mulVec_pos hvne
        linarith
  have hO₁_clopen : IsClopen O₁ := by
    refine ⟨?_, hO₁_open⟩
    have hcompl : O₁ᶜ = O₂ := by
      ext s
      constructor
      · intro hnot
        have : s ∈ O₁ ∪ O₂ := by rw [hcover]; trivial
        exact this.resolve_left hnot
      · intro hs2 hs1
        exact Set.disjoint_left.mp hdisj hs1 hs2
    rw [← isOpen_compl_iff, hcompl]
    exact hO₂_open
  have hO₁_ne : O₁.Nonempty := ⟨⟨s₀, le_of_lt hs₀_pos, le_rfl⟩, hs₀_posDef⟩
  have hO₁_univ : O₁ = Set.univ := hO₁_clopen.eq_univ hO₁_ne
  have h0_mem : (⟨0, le_rfl, le_of_lt hs₀_pos⟩ : I) ∈ O₁ := by rw [hO₁_univ]; trivial
  have hW0 : W 0 = (lyapEquiv A hA).symm U := by
    simp only [W, dif_pos (le_refl (0 : ℝ))]
    have hA0 : A - (0 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) = A := by simp
    apply lyapOp_injective hA
    have h1 : lyapOp (A - (0 : ℝ) • 1)
        ((lyapEquiv (A - (0 : ℝ) • 1) (isHurwitz_sub_smul hA le_rfl)).symm U) = U :=
      (lyapEquiv (A - (0 : ℝ) • 1) (isHurwitz_sub_smul hA le_rfl)).apply_symm_apply U
    have hlyap : ∀ X, lyapOp A X = lyapOp (A - (0 : ℝ) • 1) X := fun X => by rw [hA0]
    have h1' : lyapOp A
        ((lyapEquiv (A - (0 : ℝ) • 1) (isHurwitz_sub_smul hA le_rfl)).symm U) = U := by
      rw [hlyap]; exact h1
    have h2 : lyapOp A ((lyapEquiv A hA).symm U) = U :=
      (lyapEquiv A hA).apply_symm_apply U
    exact h1'.trans h2.symm
  rw [← hW0]
  exact h0_mem

private lemma lyapEquiv_symm_posSemidef {n : ℕ} (hn : 0 < n) {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsHurwitz A) {U : Matrix (Fin n) (Fin n) ℝ} (hU : U.PosSemidef) :
    ((lyapEquiv A hA).symm U).PosSemidef := by
  have hUsym : Uᵀ = U := by simpa [Matrix.IsHermitian] using hU.isHermitian
  have hsym : ((lyapEquiv A hA).symm U).IsHermitian := by
    simpa [Matrix.IsHermitian] using lyapEquiv_symm_transpose hA hUsym
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hsym fun v => ?_
  have hquad : 0 ≤ v ⬝ᵥ ((lyapEquiv A hA).symm U *ᵥ v) := by
    by_contra hlt
    push Not at hlt
    let a := v ⬝ᵥ ((lyapEquiv A hA).symm U *ᵥ v)
    let b := v ⬝ᵥ ((lyapEquiv A hA).symm 1 *ᵥ v)
    have h1pos : (1 : Matrix (Fin n) (Fin n) ℝ).PosDef := Matrix.PosDef.one
    have hP1 : ((lyapEquiv A hA).symm 1).PosDef := lyapEquiv_symm_posDef hn hA h1pos
    have hb : 0 ≤ b := by simpa [b, star] using hP1.posSemidef.dotProduct_mulVec_nonneg v
    let ε := (-a) / (2 * (b + 1))
    have hε : 0 < ε := div_pos (by dsimp [a]; linarith) (by linarith)
    have hUe : (U + ε • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef := by
      have hUe_sym : (U + ε • (1 : Matrix (Fin n) (Fin n) ℝ)).IsHermitian := by
        ext i j
        have hij : U j i = U i j := by
          simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hU.isHermitian.eq i) j
        by_cases h : i = j
        · subst h; simp [Matrix.conjTranspose_apply]
        · simp [Matrix.conjTranspose_apply, Matrix.one_apply, h, Ne.symm h, hij]
      refine Matrix.PosDef.of_dotProduct_mulVec_pos hUe_sym fun w hw => ?_
      have hw1 : 0 ≤ w ⬝ᵥ (U *ᵥ w) := by simpa [star] using hU.dotProduct_mulVec_nonneg w
      have hw2 : 0 < w ⬝ᵥ ((1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ w) := by simpa [star] using h1pos.dotProduct_mulVec_pos hw
      have hexp : w ⬝ᵥ ((U + ε • 1) *ᵥ w) = w ⬝ᵥ (U *ᵥ w) + ε * (w ⬝ᵥ ((1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ w)) := by
        simp [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul]
      simpa [star, hexp] using add_pos_of_nonneg_of_pos hw1 (mul_pos hε hw2)
    have hPe := lyapEquiv_symm_posDef hn hA hUe
    have hge : 0 ≤ v ⬝ᵥ ((lyapEquiv A hA).symm (U + ε • 1) *ᵥ v) := by
      simpa [star] using hPe.posSemidef.dotProduct_mulVec_nonneg v
    rw [map_add, map_smul, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul,
      smul_eq_mul] at hge
    have hcalc : ε * b < -a := by
      dsimp [ε]
      have hden : 0 < 2 * (b + 1) := by linarith
      rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
      nlinarith
    dsimp [a, b] at hcalc
    linarith
  simpa [star] using hquad

/-! ### Part 4: Spectral, trace, and 2-norm inequalities -/

private lemma posSemidef_trace_mul_nonneg {n : ℕ} {M N : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosSemidef) (hN : N.PosSemidef) : 0 ≤ (M * N).trace := by
  let U : Matrix (Fin n) (Fin n) ℝ := (hM.isHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
  let d : Fin n → ℝ := hM.isHermitian.eigenvalues
  have hU_star : star U = Uᵀ := by
    simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hspec : M = U * diagonal d * Uᵀ := by
    have h := hM.isHermitian.spectral_theorem
    simpa [U, d, Unitary.conjStarAlgAut_apply, Function.comp_def, hU_star] using h
  have hcyc : (M * N).trace = (diagonal d * (Uᵀ * N * U)).trace := by
    rw [hspec, Matrix.mul_assoc U (diagonal d) Uᵀ, Matrix.mul_assoc U, Matrix.trace_mul_comm U]
    simp only [Matrix.mul_assoc]
  rw [hcyc]
  have htr : (diagonal d * (Uᵀ * N * U)).trace = ∑ i : Fin n, d i * (Uᵀ * N * U) i i := by
    simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal]
  rw [htr]
  refine Finset.sum_nonneg fun i _ => mul_nonneg (hM.eigenvalues_nonneg i) ?_
  have hdiag : (Uᵀ * N * U) i i = (Uᵀ i) ⬝ᵥ (N *ᵥ (Uᵀ i)) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hdiag]
  simpa only [star_trivial] using hN.dotProduct_mulVec_nonneg (Uᵀ i)

private lemma posDef_inv_spectral {n : ℕ} {Y : Matrix (Fin n) (Fin n) ℝ}
    (hY : Y.PosDef) :
    let U : Matrix (Fin n) (Fin n) ℝ := (hY.isHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
    let d : Fin n → ℝ := hY.isHermitian.eigenvalues
    Y⁻¹ = U * diagonal (fun i => (d i)⁻¹) * Uᵀ := by
  intro U d
  have hU_star : star U = Uᵀ := by
    simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hspec : Y = U * diagonal d * Uᵀ := by
    have h := hY.isHermitian.spectral_theorem
    simpa [U, d, Unitary.conjStarAlgAut_apply, Function.comp_def, hU_star] using h
  have hU_mul : Uᵀ * U = 1 := by
    rw [← hU_star]; exact Unitary.coe_star_mul_self hY.isHermitian.eigenvectorUnitary
  have hU_mul' : U * Uᵀ = 1 := by
    rw [← hU_star]; exact Unitary.coe_mul_star_self hY.isHermitian.eigenvectorUnitary
  have hmul : Y * (U * diagonal (fun i => (d i)⁻¹) * Uᵀ) = 1 := by
    rw [hspec]
    calc U * diagonal d * Uᵀ * (U * diagonal (fun i => (d i)⁻¹) * Uᵀ)
        = U * diagonal d * (Uᵀ * U) * diagonal (fun i => (d i)⁻¹) * Uᵀ := by
          simp only [Matrix.mul_assoc]
      _ = U * (diagonal d * diagonal (fun i => (d i)⁻¹)) * Uᵀ := by
          rw [hU_mul, mul_one]; simp only [Matrix.mul_assoc]
      _ = U * 1 * Uᵀ := by
          congr 2
          rw [Matrix.diagonal_mul_diagonal]
          ext i j
          by_cases h : i = j
          · subst h
            have hpos : 0 < d i := hY.eigenvalues_pos i
            simp [mul_inv_cancel₀ (ne_of_gt hpos)]
          · simp [h]
      _ = 1 := by rw [mul_one, hU_mul']
  exact Matrix.inv_eq_right_inv hmul

private lemma posSemidef_one_sub_inv {n : ℕ} {Y : Matrix (Fin n) (Fin n) ℝ}
    (hY : Y.PosDef) (hge : (Y - 1).PosSemidef) : (1 - Y⁻¹).PosSemidef := by
  let U : Matrix (Fin n) (Fin n) ℝ := (hY.isHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
  let d : Fin n → ℝ := hY.isHermitian.eigenvalues
  have hU_star : star U = Uᵀ := by
    simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hspec : Y = U * diagonal d * Uᵀ := by
    have h := hY.isHermitian.spectral_theorem
    simpa [U, d, Unitary.conjStarAlgAut_apply, Function.comp_def, hU_star] using h
  have hU_mul : Uᵀ * U = 1 := by
    rw [← hU_star]; exact Unitary.coe_star_mul_self hY.isHermitian.eigenvectorUnitary
  have hU_mul' : U * Uᵀ = 1 := by
    rw [← hU_star]; exact Unitary.coe_mul_star_self hY.isHermitian.eigenvectorUnitary
  have hinv := posDef_inv_spectral hY
  have hd_ge : ∀ i, 1 ≤ d i := by
    intro i
    have h1 : 0 ≤ (Uᵀ i) ⬝ᵥ ((Y - 1) *ᵥ (Uᵀ i)) := by
      simpa only [star_trivial] using hge.dotProduct_mulVec_nonneg (Uᵀ i)
    have hdiag : (Uᵀ * (Y - 1) * U) i i = (Uᵀ i) ⬝ᵥ ((Y - 1) *ᵥ (Uᵀ i)) := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    have hsim : Uᵀ * (Y - 1) * U = diagonal d - 1 := by
      rw [hspec, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU_mul]
      calc Uᵀ * (U * diagonal d * Uᵀ) * U - 1
          = (Uᵀ * U) * diagonal d * (Uᵀ * U) - 1 := by simp only [Matrix.mul_assoc]
        _ = diagonal d - 1 := by rw [hU_mul, one_mul, mul_one]
    rw [← hdiag, hsim] at h1
    simp only [Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h1
    linarith
  have heq : 1 - Y⁻¹ = U * diagonal (fun i => 1 - (d i)⁻¹) * Uᵀ := by
    rw [hinv]
    calc (1 : Matrix (Fin n) (Fin n) ℝ) - U * diagonal (fun i => (d i)⁻¹) * Uᵀ
        = U * 1 * Uᵀ - U * diagonal (fun i => (d i)⁻¹) * Uᵀ := by rw [mul_one, hU_mul']
      _ = U * (1 - diagonal (fun i => (d i)⁻¹)) * Uᵀ := by
          rw [Matrix.mul_sub, Matrix.sub_mul]
      _ = U * diagonal (fun i => 1 - (d i)⁻¹) * Uᵀ := by
          congr 2
          ext i j
          by_cases h : i = j <;> simp [h]
  rw [heq]
  have hdiag_psd : (diagonal (fun i => 1 - (d i)⁻¹)).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    change 0 ≤ 1 - (d i)⁻¹
    have h1 : 1 ≤ d i := hd_ge i
    have h2 : (d i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    linarith
  have hconj := hdiag_psd.conjTranspose_mul_mul_same Uᵀ
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] using hconj

private lemma posSemidef_smul_inv_sub_one {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : P.PosDef) {α : ℝ} (hα : (α • 1 - P).PosSemidef) : (α • P⁻¹ - 1).PosSemidef := by
  let U : Matrix (Fin n) (Fin n) ℝ := (hP.isHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
  let d : Fin n → ℝ := hP.isHermitian.eigenvalues
  have hU_star : star U = Uᵀ := by
    simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hspec : P = U * diagonal d * Uᵀ := by
    have h := hP.isHermitian.spectral_theorem
    simpa [U, d, Unitary.conjStarAlgAut_apply, Function.comp_def, hU_star] using h
  have hU_mul : Uᵀ * U = 1 := by
    rw [← hU_star]; exact Unitary.coe_star_mul_self hP.isHermitian.eigenvectorUnitary
  have hU_mul' : U * Uᵀ = 1 := by
    rw [← hU_star]; exact Unitary.coe_mul_star_self hP.isHermitian.eigenvectorUnitary
  have hinv := posDef_inv_spectral hP
  have hd_le : ∀ i, d i ≤ α := by
    intro i
    have h1 : 0 ≤ (Uᵀ i) ⬝ᵥ ((α • 1 - P) *ᵥ (Uᵀ i)) := by
      simpa only [star_trivial] using hα.dotProduct_mulVec_nonneg (Uᵀ i)
    have hdiag : (Uᵀ * (α • 1 - P) * U) i i = (Uᵀ i) ⬝ᵥ ((α • 1 - P) *ᵥ (Uᵀ i)) := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    have hsim : Uᵀ * (α • 1 - P) * U = α • 1 - diagonal d := by
      rw [hspec, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU_mul]
      calc α • (1 : Matrix (Fin n) (Fin n) ℝ) - Uᵀ * (U * diagonal d * Uᵀ) * U
          = α • 1 - (Uᵀ * U) * diagonal d * (Uᵀ * U) := by simp only [Matrix.mul_assoc]
        _ = α • 1 - diagonal d := by rw [hU_mul, one_mul, mul_one]
    rw [← hdiag, hsim] at h1
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq,
      smul_eq_mul, mul_one] at h1
    linarith
  have heq : α • P⁻¹ - 1 = U * diagonal (fun i => α * (d i)⁻¹ - 1) * Uᵀ := by
    rw [hinv]
    calc α • (U * diagonal (fun i => (d i)⁻¹) * Uᵀ) - (1 : Matrix (Fin n) (Fin n) ℝ)
        = U * (α • diagonal (fun i => (d i)⁻¹)) * Uᵀ - U * 1 * Uᵀ := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, mul_one, hU_mul']
      _ = U * (α • diagonal (fun i => (d i)⁻¹) - 1) * Uᵀ := by
          rw [Matrix.mul_sub, Matrix.sub_mul]
      _ = U * diagonal (fun i => α * (d i)⁻¹ - 1) * Uᵀ := by
          congr 2
          ext i j
          by_cases h : i = j <;> simp [h]
  rw [heq]
  have hdiag_psd : (diagonal (fun i => α * (d i)⁻¹ - 1)).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    change 0 ≤ α * (d i)⁻¹ - 1
    have hpos : 0 < d i := hP.eigenvalues_pos i
    have hle : d i ≤ α := hd_le i
    have h1 : 1 ≤ α * (d i)⁻¹ := by
      rw [← div_eq_mul_inv, one_le_div hpos]
      exact hle
    linarith
  have hconj := hdiag_psd.conjTranspose_mul_mul_same Uᵀ
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] using hconj

private lemma matrixTwoNorm_le_of_posSemidef {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : P.PosSemidef) {α : ℝ} (hα : 0 ≤ α) (hle : (α • 1 - P).PosSemidef) :
    matrixTwoNorm P ≤ α := by
  unfold matrixTwoNorm
  refine ContinuousLinearMap.opNorm_le_bound _ hα (fun x => ?_)
  let b := hP.isHermitian.eigenvectorBasis
  let d := hP.isHermitian.eigenvalues
  have hd_le : ∀ i, d i ≤ α := by
    intro i
    let U : Matrix (Fin n) (Fin n) ℝ := (hP.isHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
    have hU_star : star U = Uᵀ := by
      simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    have hspec : P = U * diagonal d * Uᵀ := by
      simpa [U, d, Unitary.conjStarAlgAut_apply, Function.comp_def, hU_star] using hP.isHermitian.spectral_theorem
    have hU_mul : Uᵀ * U = 1 := by
      rw [← hU_star]; exact Unitary.coe_star_mul_self hP.isHermitian.eigenvectorUnitary
    have h1 : 0 ≤ (Uᵀ i) ⬝ᵥ ((α • 1 - P) *ᵥ (Uᵀ i)) := by
      simpa only [star_trivial] using hle.dotProduct_mulVec_nonneg (Uᵀ i)
    have hdiag : (Uᵀ * (α • 1 - P) * U) i i = (Uᵀ i) ⬝ᵥ ((α • 1 - P) *ᵥ (Uᵀ i)) := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    have hsim : Uᵀ * (α • 1 - P) * U = α • 1 - diagonal d := by
      rw [hspec, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU_mul]
      calc α • (1 : Matrix (Fin n) (Fin n) ℝ) - Uᵀ * (U * diagonal d * Uᵀ) * U
          = α • 1 - (Uᵀ * U) * diagonal d * (Uᵀ * U) := by simp only [Matrix.mul_assoc]
        _ = α • 1 - diagonal d := by rw [hU_mul, one_mul, mul_one]
    rw [← hdiag, hsim] at h1
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq,
      smul_eq_mul, mul_one] at h1
    linarith
  have hsq : ‖(Matrix.toEuclideanLin P).toContinuousLinearMap x‖ ^ 2 ≤ (α * ‖x‖) ^ 2 := by
    have hnorm_Px : ‖Matrix.toEuclideanLin P x‖ ^ 2 = ∑ i, ‖@inner ℝ _ _ (b i) (Matrix.toEuclideanLin P x)‖ ^ 2 := by
      simpa [Real.norm_eq_abs, sq_abs] using (b.sum_sq_norm_inner_right (Matrix.toEuclideanLin P x)).symm
    have hnorm_x : ‖x‖ ^ 2 = ∑ i, ‖@inner ℝ _ _ (b i) x‖ ^ 2 := by
      simpa [Real.norm_eq_abs, sq_abs] using (b.sum_sq_norm_inner_right x).symm
    change ‖Matrix.toEuclideanLin P x‖ ^ 2 ≤ (α * ‖x‖) ^ 2
    rw [hnorm_Px, mul_pow, hnorm_x, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hsym_lin : (Matrix.toEuclideanLin P).IsSymmetric :=
      Matrix.isSymmetric_toEuclideanLin_iff.mpr hP.isHermitian
    have heig : Matrix.toEuclideanLin P (b i) = (d i) • b i := by
      ext k
      simpa [Matrix.toEuclideanLin_apply, b, d] using
        congrFun (hP.isHermitian.mulVec_eigenvectorBasis i) k
    have hinner : @inner ℝ _ _ (b i) (Matrix.toEuclideanLin P x) = d i * @inner ℝ _ _ (b i) x := by
      rw [← hsym_lin (b i) x, heig, inner_smul_left]
      simp
    rw [hinner, norm_mul, mul_pow, Real.norm_eq_abs, sq_abs]
    have hd_nn : 0 ≤ d i := hP.eigenvalues_nonneg i
    have hd_sq : (d i) ^ 2 ≤ α ^ 2 := by nlinarith [hd_le i]
    exact mul_le_mul_of_nonneg_right hd_sq (sq_nonneg _)
  have hnonneg : 0 ≤ α * ‖x‖ := mul_nonneg hα (norm_nonneg x)
  nlinarith [norm_nonneg ((Matrix.toEuclideanLin P).toContinuousLinearMap x)]

private lemma posSemidef_matrixTwoNorm_smul_one_sub {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : P.PosSemidef) : (matrixTwoNorm P • 1 - P).PosSemidef := by
  have hsym : (matrixTwoNorm P • (1 : Matrix (Fin n) (Fin n) ℝ) - P).IsHermitian := by
    ext i j
    have hij : P j i = P i j := by
      simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hP.isHermitian.eq i) j
    by_cases h : i = j
    · subst h; simp [Matrix.conjTranspose_apply]
    · simp [Matrix.conjTranspose_apply, Matrix.one_apply, h, Ne.symm h, hij]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hsym fun v => ?_
  let x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 v
  have hdot_x : v ⬝ᵥ v = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    simp [x, dotProduct, sq]
  have hdot_Px : v ⬝ᵥ (P *ᵥ v) = @inner ℝ _ _ x (Matrix.toEuclideanLin P x) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [x, Matrix.toEuclideanLin_apply, dotProduct_comm]
  have hle : v ⬝ᵥ (P *ᵥ v) ≤ matrixTwoNorm P * (v ⬝ᵥ v) := by
    rw [hdot_Px, hdot_x]
    calc @inner ℝ _ _ x (Matrix.toEuclideanLin P x)
        ≤ |@inner ℝ _ _ x (Matrix.toEuclideanLin P x)| := le_abs_self _
      _ ≤ ‖x‖ * ‖Matrix.toEuclideanLin P x‖ := abs_real_inner_le_norm x _
      _ ≤ ‖x‖ * (matrixTwoNorm P * ‖x‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg x)
          exact (Matrix.toEuclideanLin P).toContinuousLinearMap.le_opNorm x
      _ = matrixTwoNorm P * ‖x‖ ^ 2 := by ring
  have hgoal : v ⬝ᵥ ((matrixTwoNorm P • 1 - P) *ᵥ v) = matrixTwoNorm P * (v ⬝ᵥ v) - v ⬝ᵥ (P *ᵥ v) := by
    simp [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul]
  simpa [star, hgoal] using sub_nonneg.mpr hle

/-! ### Part 5: Main Hahn–Banach separation proof -/

theorem main_proof :
    ∀ (n : ℕ), 0 < n →
    ∀ (A : Matrix (Fin n) (Fin n) ℝ), IsHurwitz A →
      ∃ (X P : Matrix (Fin n) (Fin n) ℝ),
        X.PosSemidef ∧
        X.trace = 1 ∧
        P.PosSemidef ∧
        A * P + P * A.transpose = -X ∧
        matrixTwoNorm P = 1 / (-2 * A.trace) := by
  intro n hn A hA
  let c : ℝ := -2 * A.trace
  have hc_pos : 0 < c := by
    have := trace_neg_of_isHurwitz hn hA
    dsimp [c]; linarith
  let E := Fin n → Fin n → ℝ
  let toE : Matrix (Fin n) (Fin n) ℝ ≃ₗ[ℝ] E :=
    { toFun := fun M i j => M i j
      invFun := Matrix.of
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let Φ : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    (lyapEquiv A hA).symm.toLinearMap
  have hΦ_apply : ∀ U, Φ U = (lyapEquiv A hA).symm U := fun _ => rfl
  let ΦE : E →L[ℝ] E :=
    ((toE.toLinearMap.comp Φ).comp toE.symm.toLinearMap).toContinuousLinearMap
  have hΦE_apply : ∀ M : Matrix (Fin n) (Fin n) ℝ, ΦE (toE M) = toE (Φ M) := fun _ => rfl
  let PSD : Set E := {Z | (Matrix.of Z).PosSemidef}
  let Δ : Set E := {U | (Matrix.of U).PosSemidef ∧ (Matrix.of U).trace = 1}
  have hPSD_conv : Convex ℝ PSD := by
    intro Z₁ hZ₁ Z₂ hZ₂ a b ha hb _
    change (a • Matrix.of Z₁ + b • Matrix.of Z₂).PosSemidef
    exact (hZ₁.smul ha).add (hZ₂.smul hb)
  have hPSD_closed : IsClosed PSD := by
    have hEq : PSD = ({Z : E | (Matrix.of Z)ᵀ = Matrix.of Z} ∩
        ⋂ v : Fin n → ℝ, {Z : E | 0 ≤ v ⬝ᵥ ((Matrix.of Z) *ᵥ v)}) := by
      ext Z
      simp only [PSD, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
      constructor
      · intro hZ
        exact ⟨by simpa [Matrix.IsHermitian] using hZ.isHermitian,
          fun v => by simpa [star] using hZ.dotProduct_mulVec_nonneg v⟩
      · rintro ⟨hT, hv⟩
        exact Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
          (by simpa [Matrix.IsHermitian] using hT) (fun v => by simpa [star] using hv v)
    rw [hEq]
    refine IsClosed.inter ?_ (isClosed_iInter fun v => ?_)
    · have hEqT : {Z : E | (Matrix.of Z)ᵀ = Matrix.of Z} =
          ⋂ i : Fin n, ⋂ j : Fin n, {Z : E | Z j i = Z i j} := by
        ext Z
        simp only [Set.mem_setOf_eq, Set.mem_iInter]
        constructor
        · intro h i j; exact congrFun (congrFun h i) j
        · intro h; ext i j; exact h i j
      rw [hEqT]
      refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
      exact isClosed_eq ((continuous_apply i).comp (continuous_apply j))
        ((continuous_apply j).comp (continuous_apply i))
    · have hcont : Continuous (fun Z : E => v ⬝ᵥ ((Matrix.of Z) *ᵥ v)) := by
        simp only [dotProduct, Matrix.mulVec, Matrix.of_apply]
        fun_prop
      exact isClosed_le continuous_const hcont
  have hΔ_conv : Convex ℝ Δ := by
    intro U₁ hU₁ U₂ hU₂ a b ha hb hab
    refine ⟨hPSD_conv hU₁.1 hU₂.1 ha hb hab, ?_⟩
    change (a • Matrix.of U₁ + b • Matrix.of U₂).trace = 1
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hU₁.2, hU₂.2]
    simp [hab]
  have hΔ_closed : IsClosed Δ := by
    have hEq : Δ = PSD ∩ {U : E | (Matrix.of U).trace = 1} := rfl
    rw [hEq]
    refine hPSD_closed.inter (isClosed_eq ?_ continuous_const)
    have hcont : Continuous (fun U : E => ∑ i : Fin n, U i i) := by fun_prop
    exact hcont
  have hΔ_compact : IsCompact Δ := by
    have hbdd : Bornology.IsBounded Δ := by
      rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨1, fun U hU => ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by norm_num)]
      intro i
      rw [pi_norm_le_iff_of_nonneg (by norm_num)]
      intro j
      rw [Real.norm_eq_abs]
      let Um : Matrix (Fin n) (Fin n) ℝ := Matrix.of U
      have hdiag_nn : ∀ k, 0 ≤ Um k k := fun k => by
        have := hU.1.dotProduct_mulVec_nonneg (Pi.single k 1)
        simpa [Um, star, dotProduct, Matrix.mulVec, Pi.single_apply] using this
      have hdiag_le : ∀ k, Um k k ≤ 1 := fun k => by
        have h1 : Um k k ≤ ∑ l, Um l l :=
          Finset.single_le_sum (fun l _ => hdiag_nn l) (Finset.mem_univ k)
        have h2 : ∑ l, Um l l = 1 := hU.2
        linarith
      have hsym : Um j i = Um i j := by
        have hT : Umᵀ = Um := by simpa [Um, Matrix.IsHermitian] using hU.1.isHermitian
        exact congrFun (congrFun hT i) j
      have hplus : 0 ≤ Um i i + Um j j + 2 * Um i j := by
        have h1 := hU.1.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j 1)
        have h2 : (Pi.single i (1 : ℝ) + Pi.single j 1) ⬝ᵥ
            (Um *ᵥ (Pi.single i 1 + Pi.single j 1)) = Um i i + Um i j + Um j i + Um j j := by
          simp [dotProduct, Matrix.mulVec, Pi.single_apply, Finset.sum_add_distrib,
            Finset.mul_sum, add_mul, mul_add]
          ring
        have h1' : 0 ≤ (Pi.single i (1 : ℝ) + Pi.single j 1) ⬝ᵥ
            (Um *ᵥ (Pi.single i 1 + Pi.single j 1)) := by simpa only [Um, star_trivial] using h1
        rw [h2, hsym] at h1'
        linarith
      have hminus : 0 ≤ Um i i + Um j j - 2 * Um i j := by
        have h1 := hU.1.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
        have h2 : (Pi.single i (1 : ℝ) - Pi.single j 1) ⬝ᵥ
            (Um *ᵥ (Pi.single i 1 - Pi.single j 1)) = Um i i - Um i j - Um j i + Um j j := by
          simp [dotProduct, Matrix.mulVec, Pi.single_apply, Finset.sum_sub_distrib,
            Finset.mul_sum, sub_mul, mul_sub]
          ring
        have h1' : 0 ≤ (Pi.single i (1 : ℝ) - Pi.single j 1) ⬝ᵥ
            (Um *ᵥ (Pi.single i 1 - Pi.single j 1)) := by simpa only [Um, star_trivial] using h1
        rw [h2, hsym] at h1'
        linarith
      change |Um i j| ≤ 1
      rw [abs_le]
      constructor <;> linarith [hdiag_le i, hdiag_le j]
    exact Metric.isCompact_of_isClosed_isBounded hΔ_closed hbdd
  let K : Set E := (ΦE '' Δ) + PSD
  have hK_conv : Convex ℝ K := (hΔ_conv.linear_image ΦE.toLinearMap).add hPSD_conv
  have hK_closed : IsClosed K := hPSD_closed.add_left_of_isCompact (hΔ_compact.image ΦE.continuous)
  have hmem : toE (c⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)) ∈ K := by
    by_contra hnot
    obtain ⟨f, α, hlt, hgt⟩ := geometric_hahn_banach_point_closed hK_conv hK_closed hnot
    -- Represent f by a symmetric matrix R
    let R₀ : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => f (toE (Matrix.single j i 1))
    have hf_eq : ∀ M : Matrix (Fin n) (Fin n) ℝ, f (toE M) = (R₀ * M).trace := by
      intro M
      have hM : M = ∑ i : Fin n, ∑ j : Fin n, M i j • Matrix.single i j (1 : ℝ) := by
        ext a b
        simp [Matrix.sum_apply, Matrix.single_apply, ite_and]
      conv_lhs => rw [hM]
      simp only [map_sum, map_smul, smul_eq_mul]
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, R₀, Matrix.of_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    let R : Matrix (Fin n) (Fin n) ℝ := (2 : ℝ)⁻¹ • (R₀ + R₀ᵀ)
    have hR_sym : Rᵀ = R := by
      simp [R, Matrix.transpose_smul, Matrix.transpose_add, add_comm]
    have hf_sym : ∀ M : Matrix (Fin n) (Fin n) ℝ, Mᵀ = M → f (toE M) = (R * M).trace := by
      intro M hM
      rw [hf_eq M]
      have h1 : (R₀ᵀ * M).trace = (R₀ * M).trace := by
        calc (R₀ᵀ * M).trace = ((R₀ᵀ * M)ᵀ).trace := (Matrix.trace_transpose _).symm
          _ = (Mᵀ * R₀).trace := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
          _ = (M * R₀).trace := by rw [hM]
          _ = (R₀ * M).trace := Matrix.trace_mul_comm M R₀
      simp only [R, Matrix.smul_mul, Matrix.add_mul, Matrix.trace_smul, Matrix.trace_add, h1,
        smul_eq_mul]
      ring
    have hlt' : c⁻¹ * R.trace < α := by
      have h1 : f (toE (c⁻¹ • 1)) = (R * (c⁻¹ • 1)).trace :=
        hf_sym _ (by simp)
      rw [h1, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul] at hlt
      exact hlt
    have hgt' : ∀ U : Matrix (Fin n) (Fin n) ℝ, U.PosSemidef ∧ U.trace = 1 →
        ∀ Z : Matrix (Fin n) (Fin n) ℝ, Z.PosSemidef →
        α < (R * Φ U).trace + (R * Z).trace := by
      intro U hU Z hZ
      have hmemK : toE (Φ U + Z) ∈ K := by
        have h1 : toE (Φ U + Z) = ΦE (toE U) + toE Z := rfl
        rw [h1]
        exact Set.add_mem_add (Set.mem_image_of_mem ΦE hU) hZ
      have hsymK : (Φ U + Z)ᵀ = Φ U + Z := by
        rw [Matrix.transpose_add]
        have hUsym : Uᵀ = U := by simpa [Matrix.IsHermitian] using hU.1.isHermitian
        have hZsym : Zᵀ = Z := by simpa [Matrix.IsHermitian] using hZ.isHermitian
        rw [hΦ_apply, lyapEquiv_symm_transpose hA hUsym, hZsym]
      have h1 := hgt (toE (Φ U + Z)) hmemK
      rw [hf_sym _ hsymK, Matrix.mul_add, Matrix.trace_add] at h1
      exact h1
    -- Pick a witness U₀
    let U₀ : Matrix (Fin n) (Fin n) ℝ := ((n : ℝ)⁻¹) • 1
    have hU₀ : U₀.PosSemidef ∧ U₀.trace = 1 := by
      refine ⟨Matrix.PosSemidef.one.smul (by positivity), ?_⟩
      simp [U₀, Matrix.trace_smul, Matrix.trace_one, Finset.card_univ, Fintype.card_fin,
        inv_mul_cancel₀ (by positivity : (n : ℝ) ≠ 0)]
    -- R is PosSemidef
    have hR_psd : R.PosSemidef := by
      refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (by simpa [Matrix.IsHermitian] using hR_sym) fun v => ?_
      let Zv : Matrix (Fin n) (Fin n) ℝ := Matrix.vecMulVec v v
      have hZv : Zv.PosSemidef := by
        refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun w => ?_
        · ext i j; simp [Zv, Matrix.vecMulVec_apply, mul_comm]
        · have h1 : w ⬝ᵥ (Zv *ᵥ w) = (w ⬝ᵥ v) ^ 2 := by
            simp [Zv, dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, sq, Finset.mul_sum,
              Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            ring
          simpa [star, h1] using sq_nonneg (w ⬝ᵥ v)
      have htr_Zv : (R * Zv).trace = v ⬝ᵥ (R *ᵥ v) := by
        simp [Zv, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply,
          dotProduct, Matrix.mulVec, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        have hij : R j i = R i j := congrFun (congrFun hR_sym i) j
        rw [hij]
        ring
      have hnn : 0 ≤ v ⬝ᵥ (R *ᵥ v) := by
        by_contra hneg
        push Not at hneg
        let b := (R * Φ U₀).trace
        let t := (|b| + |α| + 1) / (-(v ⬝ᵥ (R *ᵥ v)))
        have ht : 0 ≤ t := div_nonneg (by positivity) (by linarith)
        have hgt_t := hgt' U₀ hU₀ (t • Zv) (hZv.smul ht)
        rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, htr_Zv] at hgt_t
        have hcalc : t * (v ⬝ᵥ (R *ᵥ v)) = -(|b| + |α| + 1) := by
          dsimp [t]
          have hne : v ⬝ᵥ (R *ᵥ v) ≠ 0 := ne_of_lt hneg
          field_simp
        rw [hcalc] at hgt_t
        have hb_le : b ≤ |b| := le_abs_self b
        have hα_le : -α ≤ |α| := neg_le_abs α
        dsimp [b] at hb_le
        linarith
      simpa [star] using hnn
    -- α > 0
    have hR_tr_nn : 0 ≤ R.trace := by
      have h1 : (R * 1).trace = R.trace := by simp
      rw [← h1]
      exact posSemidef_trace_mul_nonneg hR_psd Matrix.PosSemidef.one
    have hα_pos : 0 < α := lt_of_le_of_lt (mul_nonneg (inv_nonneg.mpr (le_of_lt hc_pos)) hR_tr_nn) hlt'
    -- Define Y = (lyapEquiv Aᵀ).symm R
    let Y := (lyapEquiv Aᵀ (isHurwitz_transpose hA)).symm R
    have hY_eq : -(Aᵀ * Y + Y * A) = R := by
      have h1 := (lyapEquiv Aᵀ (isHurwitz_transpose hA)).apply_symm_apply R
      change -(Aᵀ * Y + Y * Aᵀᵀ) = R at h1
      simpa [Matrix.transpose_transpose] using h1
    have hY_sym : Yᵀ = Y := lyapEquiv_symm_transpose (isHurwitz_transpose hA) hR_sym
    -- Every unit vector v satisfies α < v ⬝ᵥ (Y *ᵥ v)
    have hY_gt : ∀ v : Fin n → ℝ, v ⬝ᵥ v = 1 → α < v ⬝ᵥ (Y *ᵥ v) := by
      intro v hv
      let Uv : Matrix (Fin n) (Fin n) ℝ := Matrix.vecMulVec v v
      have hUv : Uv.PosSemidef ∧ Uv.trace = 1 := by
        refine ⟨Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun w => ?_, ?_⟩
        · ext i j; simp [Uv, Matrix.vecMulVec_apply, mul_comm]
        · have h1 : w ⬝ᵥ (Uv *ᵥ w) = (w ⬝ᵥ v) ^ 2 := by
            simp [Uv, dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, sq, Finset.mul_sum,
              Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            ring
          simpa [star, h1] using sq_nonneg (w ⬝ᵥ v)
        · simpa [Uv, Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, dotProduct] using hv
      have h1 := hgt' Uv hUv 0 Matrix.PosSemidef.zero
      rw [Matrix.mul_zero, Matrix.trace_zero, add_zero, hΦ_apply,
        trace_lyapEquiv_symm_adj hA R Uv] at h1
      have htr : (Y * Uv).trace = v ⬝ᵥ (Y *ᵥ v) := by
        simp [Uv, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply,
          dotProduct, Matrix.mulVec, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        have hij : Y j i = Y i j := by
          simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hY_sym i) j
        rw [hij]
        ring
      rwa [htr] at h1
    -- Scale by α⁻¹: Ỹ = α⁻¹ • Y, R̃ = α⁻¹ • R
    let Yt := α⁻¹ • Y
    let Rt := α⁻¹ • R
    have hYt_sym : Yt.IsHermitian := by
      simpa [Matrix.IsHermitian, Yt, Matrix.transpose_smul] using congrArg (α⁻¹ • ·) hY_sym
    have hYt_posDef : Yt.PosDef := by
      rw [posDef_iff_unit_sphere hYt_sym]
      intro v hv
      have h1 := hY_gt v hv
      have h2 : v ⬝ᵥ (Yt *ᵥ v) = α⁻¹ * (v ⬝ᵥ (Y *ᵥ v)) := by
        simp [Yt, Matrix.smul_mulVec, dotProduct_smul]
      rw [h2]
      exact mul_pos (inv_pos.mpr hα_pos) (lt_trans hα_pos h1)
    have hYt_ge_one : (Yt - 1).PosSemidef := by
      refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hYt_sym.sub Matrix.isHermitian_one) fun v => ?_
      by_cases hv0 : v = 0
      · subst hv0; simp
      · have hdot_pos : 0 < v ⬝ᵥ v := by
          obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
          have h1 : (v i) ^ 2 ≤ ∑ j, (v j) ^ 2 :=
            Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
          have h2 : v ⬝ᵥ v = ∑ j, (v j) ^ 2 := by simp [dotProduct, sq]
          linarith [sq_pos_of_ne_zero hi]
        let r := Real.sqrt (v ⬝ᵥ v)
        have hr : 0 < r := Real.sqrt_pos.mpr hdot_pos
        let u := r⁻¹ • v
        have hu : u ⬝ᵥ u = 1 := by
          simp only [u, dotProduct_smul, smul_dotProduct, smul_eq_mul]
          have hrr : r * r = v ⬝ᵥ v := Real.mul_self_sqrt (le_of_lt hdot_pos)
          rw [← hrr]
          field_simp [ne_of_gt hr]
        have h1 : 1 < u ⬝ᵥ (Yt *ᵥ u) := by
          have h2 := hY_gt u hu
          have h3 : u ⬝ᵥ (Yt *ᵥ u) = α⁻¹ * (u ⬝ᵥ (Y *ᵥ u)) := by
            simp [Yt, Matrix.smul_mulVec, dotProduct_smul]
          rw [h3]
          calc 1 = α⁻¹ * α := (inv_mul_cancel₀ (ne_of_gt hα_pos)).symm
            _ < α⁻¹ * (u ⬝ᵥ (Y *ᵥ u)) := mul_lt_mul_of_pos_left h2 (inv_pos.mpr hα_pos)
        have h4 : 0 ≤ u ⬝ᵥ ((Yt - 1) *ᵥ u) := by
          simp only [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, hu]
          linarith
        have h5 : v ⬝ᵥ ((Yt - 1) *ᵥ v) = r ^ 2 * (u ⬝ᵥ ((Yt - 1) *ᵥ u)) := by
          simp only [u, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
          have hrr : r ^ 2 * (r⁻¹ * r⁻¹) = 1 := by
            field_simp [ne_of_gt hr]
          calc v ⬝ᵥ ((Yt - 1) *ᵥ v)
              = 1 * (v ⬝ᵥ ((Yt - 1) *ᵥ v)) := (one_mul _).symm
            _ = (r ^ 2 * (r⁻¹ * r⁻¹)) * (v ⬝ᵥ ((Yt - 1) *ᵥ v)) := by rw [hrr]
            _ = r ^ 2 * (r⁻¹ * (r⁻¹ * (v ⬝ᵥ ((Yt - 1) *ᵥ v)))) := by ring
        simpa [star, h5] using mul_nonneg (sq_nonneg r) h4
    have hRt_psd : Rt.PosSemidef := hR_psd.smul (inv_nonneg.mpr (le_of_lt hα_pos))
    have hRt_eq : -(Aᵀ * Yt + Yt * A) = Rt := by
      simp only [Yt, Rt, Matrix.mul_smul, Matrix.smul_mul, ← smul_add, ← smul_neg, hY_eq]
    have hRt_tr_lt : Rt.trace < c := by
      rw [Matrix.trace_smul, smul_eq_mul]
      have h1 : R.trace < α * c := by
        have := (mul_lt_mul_of_pos_left hlt' hc_pos)
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hc_pos), one_mul] at this
        linarith
      calc α⁻¹ * R.trace < α⁻¹ * (α * c) := mul_lt_mul_of_pos_left h1 (inv_pos.mpr hα_pos)
        _ = c := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hα_pos), one_mul]
    -- Contradiction via trace((1 - Yt⁻¹) * Rt) >= 0
    have htr_nn : 0 ≤ ((1 - Yt⁻¹) * Rt).trace :=
      posSemidef_trace_mul_nonneg (posSemidef_one_sub_inv hYt_posDef hYt_ge_one) hRt_psd
    have hYt_det_unit : IsUnit Yt.det := isUnit_iff_ne_zero.mpr hYt_posDef.det_pos.ne'
    have hYt_inv_mul : Yt⁻¹ * Yt = 1 := Matrix.nonsing_inv_mul Yt hYt_det_unit
    have hYt_mul_inv : Yt * Yt⁻¹ = 1 := Matrix.mul_nonsing_inv Yt hYt_det_unit
    have htr_inv : (Yt⁻¹ * Rt).trace = c := by
      rw [← hRt_eq, Matrix.mul_neg, Matrix.mul_add, Matrix.trace_neg, Matrix.trace_add]
      rw [← Matrix.mul_assoc Yt⁻¹ Yt A, hYt_inv_mul, one_mul]
      rw [← Matrix.mul_assoc Yt⁻¹ Aᵀ Yt, Matrix.trace_mul_cycle Yt⁻¹ Aᵀ Yt, hYt_mul_inv,
        Matrix.one_mul, Matrix.trace_transpose]
      dsimp [c]; ring
    rw [Matrix.sub_mul, one_mul, Matrix.trace_sub, htr_inv] at htr_nn
    linarith
  -- Extract X ∈ Δ and Z ∈ PSD with Φ X + Z = c⁻¹ • 1
  rcases Set.mem_add.mp hmem with ⟨_, ⟨U, hU, rfl⟩, Z, hZ, hsum⟩
  let X : Matrix (Fin n) (Fin n) ℝ := Matrix.of U
  let Zm : Matrix (Fin n) (Fin n) ℝ := Matrix.of Z
  have hX : X.PosSemidef ∧ X.trace = 1 := hU
  have hZm : Zm.PosSemidef := hZ
  have hsumM : Φ X + Zm = c⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    exact congrFun (congrFun hsum i) j
  let P := Φ X
  have hP_psd : P.PosSemidef := lyapEquiv_symm_posSemidef hn hA hX.1
  have hlyap : A * P + P * Aᵀ = -X := by
    have h1 : lyapOp A P = X := (lyapEquiv A hA).apply_symm_apply X
    dsimp [lyapOp] at h1
    exact neg_eq_iff_eq_neg.mp h1
  have hnorm_le : matrixTwoNorm P ≤ c⁻¹ := by
    have hsub : c⁻¹ • 1 - P = Zm := (eq_sub_of_add_eq' hsumM).symm
    exact matrixTwoNorm_le_of_posSemidef hP_psd (inv_nonneg.mpr (le_of_lt hc_pos)) (by rw [hsub]; exact hZm)
  have hnorm_ge : c⁻¹ ≤ matrixTwoNorm P := by
    by_contra hlt
    push Not at hlt
    let P₀ := Φ 1
    have hP₀_posDef : P₀.PosDef := lyapEquiv_symm_posDef hn hA Matrix.PosDef.one
    have hgap : 0 < 1 - c * matrixTwoNorm P := by
      have h1 : c * matrixTwoNorm P < c * c⁻¹ := mul_lt_mul_of_pos_left hlt hc_pos
      rw [mul_inv_cancel₀ (ne_of_gt hc_pos)] at h1
      linarith
    let ε := (1 - c * matrixTwoNorm P) / (2 * (c * matrixTwoNorm P₀ + 1))
    have hε_pos : 0 < ε := by
      have : 0 ≤ matrixTwoNorm P₀ := norm_nonneg _
      positivity
    let Pε := P + ε • P₀
    let Xε := X + ε • (1 : Matrix (Fin n) (Fin n) ℝ)
    have hPε_posDef : Pε.PosDef := by
      refine Matrix.PosDef.of_dotProduct_mulVec_pos
        (hP_psd.isHermitian.add (hP₀_posDef.posSemidef.smul (le_of_lt hε_pos)).isHermitian) fun v hv => ?_
      have h1 : 0 ≤ v ⬝ᵥ (P *ᵥ v) := by simpa [star] using hP_psd.dotProduct_mulVec_nonneg v
      have h2 : 0 < v ⬝ᵥ (P₀ *ᵥ v) := by simpa [star] using hP₀_posDef.dotProduct_mulVec_pos hv
      have h3 : v ⬝ᵥ (Pε *ᵥ v) = v ⬝ᵥ (P *ᵥ v) + ε * (v ⬝ᵥ (P₀ *ᵥ v)) := by
        simp [Pε, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul]
      simpa [star, h3] using add_pos_of_nonneg_of_pos h1 (mul_pos hε_pos h2)
    have hXε_psd : Xε.PosSemidef := hX.1.add (Matrix.PosSemidef.one.smul (le_of_lt hε_pos))
    have hlyap_ε : -(A * Pε + Pε * Aᵀ) = Xε := by
      have h1 : lyapOp A P₀ = 1 := (lyapEquiv A hA).apply_symm_apply 1
      have h2 : lyapOp A P = X := (lyapEquiv A hA).apply_symm_apply X
      have h3 : lyapOp A Pε = Xε := by
        dsimp [Pε, Xε]
        rw [map_add, map_smul, h2, h1]
      exact h3
    have hPε_det_unit : IsUnit Pε.det := isUnit_iff_ne_zero.mpr hPε_posDef.det_pos.ne'
    have hPε_inv_mul : Pε⁻¹ * Pε = 1 := Matrix.nonsing_inv_mul Pε hPε_det_unit
    have hPε_mul_inv : Pε * Pε⁻¹ = 1 := Matrix.mul_nonsing_inv Pε hPε_det_unit
    have htr_Pε : (Pε⁻¹ * Xε).trace = c := by
      rw [← hlyap_ε, Matrix.mul_neg, Matrix.mul_add, Matrix.trace_neg, Matrix.trace_add]
      rw [← Matrix.mul_assoc Pε⁻¹ Pε Aᵀ, hPε_inv_mul, one_mul, Matrix.trace_transpose]
      rw [← Matrix.mul_assoc Pε⁻¹ A Pε, Matrix.trace_mul_cycle Pε⁻¹ A Pε, hPε_mul_inv, one_mul]
      dsimp [c]; ring
    have htr_nn : 0 ≤ ((matrixTwoNorm Pε • Pε⁻¹ - 1) * Xε).trace :=
      posSemidef_trace_mul_nonneg
        (posSemidef_smul_inv_sub_one hPε_posDef
          (posSemidef_matrixTwoNorm_smul_one_sub hPε_posDef.posSemidef))
        hXε_psd
    rw [Matrix.sub_mul, Matrix.smul_mul, one_mul, Matrix.trace_sub, Matrix.trace_smul,
      smul_eq_mul, htr_Pε] at htr_nn
    have hXε_tr : 1 ≤ Xε.trace := by
      simp only [Xε, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, hX.2,
        Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      have : 0 ≤ ε * (n : ℝ) := by positivity
      linarith
    have htri : matrixTwoNorm Pε ≤ matrixTwoNorm P + ε * matrixTwoNorm P₀ := by
      unfold matrixTwoNorm
      have hlin : (Matrix.toEuclideanLin Pε).toContinuousLinearMap =
          (Matrix.toEuclideanLin P).toContinuousLinearMap +
            ε • (Matrix.toEuclideanLin P₀).toContinuousLinearMap := by
        ext x i
        simp [Pε, Matrix.toEuclideanLin_apply, Matrix.add_mulVec, Matrix.smul_mulVec]
      rw [hlin]
      calc ‖(Matrix.toEuclideanLin P).toContinuousLinearMap +
            ε • (Matrix.toEuclideanLin P₀).toContinuousLinearMap‖
          ≤ ‖(Matrix.toEuclideanLin P).toContinuousLinearMap‖ +
            ‖ε • (Matrix.toEuclideanLin P₀).toContinuousLinearMap‖ := norm_add_le _ _
        _ = ‖(Matrix.toEuclideanLin P).toContinuousLinearMap‖ +
            ε * ‖(Matrix.toEuclideanLin P₀).toContinuousLinearMap‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε_pos]
    have hbound : c * matrixTwoNorm Pε ≤ c * matrixTwoNorm P + c * (ε * matrixTwoNorm P₀) := by
      nlinarith
    have hε_small : c * (ε * matrixTwoNorm P₀) < 1 - c * matrixTwoNorm P := by
      dsimp [ε]
      have hnn : 0 ≤ c * matrixTwoNorm P₀ := mul_nonneg (le_of_lt hc_pos) (norm_nonneg _)
      have hden : 0 < 2 * (c * matrixTwoNorm P₀ + 1) := by linarith
      have h1 : c * ((1 - c * matrixTwoNorm P) / (2 * (c * matrixTwoNorm P₀ + 1)) * matrixTwoNorm P₀) =
          (1 - c * matrixTwoNorm P) * (c * matrixTwoNorm P₀) / (2 * (c * matrixTwoNorm P₀ + 1)) := by ring
      rw [h1, div_lt_iff₀ hden]
      nlinarith
    linarith
  have hnorm_eq : matrixTwoNorm P = 1 / (-2 * A.trace) := by
    rw [one_div]
    exact le_antisymm hnorm_le hnorm_ge
  exact ⟨X, P, hX.1, hX.2, hP_psd, hlyap, hnorm_eq⟩

end OMA.S_mse_2922967_Proof

theorem OMA.solution : type_of% @OMA.S_mse_2922967.main :=
  OMA.S_mse_2922967_Proof.main_proof
