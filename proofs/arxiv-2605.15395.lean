import OMAStatements.S_arxiv_2605_15395

/-!
# Proof of arXiv:2605.15395 — Equivalence and Separation for Multivariate Matrix-Exponential and Phase-Type Distribution Classes

Complete formalization of Oscar Peralta's results:
1. Self-contained multivariate Fornasini–Marchesini realization + `lem-input-one` + `lem-diag` + `lem-invert`
   proving `MVME_n = MME*_n` (Theorem 3.4 & Remark 2.4).
2. M-matrix principal minor positivity + diagonal-shift determinant expansion + `MvPolynomial` UFD leading-form
   factorization proving the `MPH*_n` factorization criterion (Theorem 4.2).
3. Explicit `2 × 2` Wishart trace law tensored with `Exp(1)` marginals proving `MPH*_n ⊂neq MVPH_n` for all `n ≥ 3`
   (Theorems 4.4, 4.5, and Corollary 4.6).
-/

namespace OMA.P_arxiv_2605_15395

open OMA.S_arxiv_2605_15395
open Matrix MvPolynomial MeasureTheory Polynomial

/-! ### Section 1: Characteristic Polynomial Evaluation, Hurwitz Stability, and M-Matrix Principal Minors -/

private lemma eval_charpoly_eq_det {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (M : Matrix ι ι R) (x : R) :
    Polynomial.eval x M.charpoly = (x • (1 : Matrix ι ι R) - M).det := by
  have hmap := RingHom.map_det (Polynomial.evalRingHom x) M.charmatrix
  change Polynomial.eval x M.charpoly = (M.charmatrix.map (Polynomial.evalRingHom x)).det at hmap
  rw [hmap]
  congr 1
  ext i j
  simp only [Matrix.map_apply, Matrix.charmatrix, Matrix.sub_apply, Matrix.scalar_apply,
    Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    Polynomial.coe_evalRingHom]
  split_ifs <;> simp

private lemma hurwitz_det_ne_zero {m : ℕ} {T : Matrix (Fin m) (Fin m) ℝ} (hH : IsHurwitzStable T) :
    T.det ≠ 0 := by
  intro h0
  have hdetc : (T.map Complex.ofReal).det = (T.det : ℂ) := (RingHom.map_det Complex.ofRealHom T).symm
  have hroot : (T.map Complex.ofReal).charpoly.IsRoot 0 := by
    rw [Polynomial.IsRoot, eval_charpoly_eq_det, zero_smul, zero_sub, Matrix.det_neg,
        hdetc, h0, Complex.ofReal_zero, mul_zero]
  have hlt := hH 0 hroot
  simp at hlt

private lemma hurwitz_neg_det_ne_zero {m : ℕ} {T : Matrix (Fin m) (Fin m) ℝ} (hH : IsHurwitzStable T) :
    (-T).det ≠ 0 := by
  rw [Matrix.det_neg]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (hurwitz_det_ne_zero hH)

private lemma det_ne_zero_of_strictDiagDom {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hdom : ∀ i : ι, ∑ j ∈ Finset.univ.erase i, |A i j| < A i i) :
    A.det ≠ 0 := by
  intro hdet0
  obtain ⟨v, hv_ne, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet0
  have hne_univ : (Finset.univ : Finset ι).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    exact hv_ne (funext fun i => absurd (Finset.mem_univ i) (hemp ▸ Finset.notMem_empty i))
  obtain ⟨i, _, hi_max⟩ := Finset.exists_max_image Finset.univ (fun j => |v j|) hne_univ
  have hvi_pos : 0 < |v i| := by
    by_contra hle
    have h0 : |v i| = 0 := le_antisymm (not_lt.mp hle) (abs_nonneg _)
    exact hv_ne (funext fun j => abs_eq_zero.mp (le_antisymm (h0 ▸ hi_max j (Finset.mem_univ j)) (abs_nonneg _)))
  have hrow : A i i * v i + ∑ j ∈ Finset.univ.erase i, A i j * v j = 0 := by
    have := congrFun hv0 i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
    rwa [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at this
  have hAi_pos : 0 < A i i := lt_of_le_of_lt (Finset.sum_nonneg fun j _ => abs_nonneg _) (hdom i)
  have h1 : A i i * |v i| = |∑ j ∈ Finset.univ.erase i, A i j * v j| := by
    have heq : A i i * v i = -(∑ j ∈ Finset.univ.erase i, A i j * v j) := eq_neg_of_add_eq_zero_left hrow
    rw [← abs_of_pos hAi_pos, ← abs_mul, heq, abs_neg]
  have h2 : |∑ j ∈ Finset.univ.erase i, A i j * v j| ≤ (∑ j ∈ Finset.univ.erase i, |A i j|) * |v i| := by
    calc |∑ j ∈ Finset.univ.erase i, A i j * v j|
        ≤ ∑ j ∈ Finset.univ.erase i, |A i j * v j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j ∈ Finset.univ.erase i, |A i j| * |v j| := by simp_rw [abs_mul]
      _ ≤ ∑ j ∈ Finset.univ.erase i, |A i j| * |v i| :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hi_max j (Finset.mem_univ j)) (abs_nonneg _)
      _ = (∑ j ∈ Finset.univ.erase i, |A i j|) * |v i| := (Finset.sum_mul _ _ _).symm
  have h3 : (∑ j ∈ Finset.univ.erase i, |A i j|) * |v i| < A i i * |v i| :=
    mul_lt_mul_of_pos_right (hdom i) hvi_pos
  linarith

private lemma transient_principal_det_ne_zero {m : ℕ} {T : Matrix (Fin m) (Fin m) ℝ}
    (hT : IsTransientSubgenerator T) (S : Finset (Fin m)) :
    ((-T).submatrix (Subtype.val : { i : Fin m // i ∈ S } → Fin m) Subtype.val).det ≠ 0 := by
  classical
  rcases hT with ⟨hH, hdiag, hoff, hrow⟩
  intro hdet0
  obtain ⟨v, hv_ne, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet0
  -- Extend `|v|` by zero outside `S`.
  let w : Fin m → ℝ := fun i => if hi : i ∈ S then |v ⟨i, hi⟩| else 0
  have hw_nonneg : ∀ i, 0 ≤ w i := fun i => by dsimp [w]; split_ifs; exact abs_nonneg _; exact le_rfl
  have hw_ne : ∃ i, 0 < w i := by
    have : ∃ x : { i : Fin m // i ∈ S }, v x ≠ 0 := by
      by_contra hall; push Not at hall; exact hv_ne (funext hall)
    obtain ⟨⟨i, hi⟩, hvi⟩ := this
    exact ⟨i, by simp only [w, dif_pos hi]; exact abs_pos.mpr hvi⟩
  -- `(T.mulVec w) i ≥ 0` for all `i : Fin m`.
  have hTw_nonneg : ∀ i : Fin m, 0 ≤ (T.mulVec w) i := by
    intro i
    by_cases hi : i ∈ S
    · have hrow_v := congrFun hv0 ⟨i, hi⟩
      simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Matrix.neg_apply, Pi.zero_apply] at hrow_v
      have hsplit := Finset.add_sum_erase (s := (Finset.univ : Finset { j : Fin m // j ∈ S }))
        (f := fun j => -T i j.val * v j) (Finset.mem_univ ⟨i, hi⟩)
      rw [hrow_v] at hsplit
      have hdiag_eq : (-T i i) * v ⟨i, hi⟩ = ∑ j ∈ Finset.univ.erase ⟨i, hi⟩, T i j.val * v j := by
        have : -T i i * v ⟨i, hi⟩ + ∑ x ∈ Finset.univ.erase ⟨i, hi⟩, -T i x.val * v x = 0 := hsplit
        have hneg : ∑ x ∈ Finset.univ.erase ⟨i, hi⟩, -T i x.val * v x =
            -(∑ x ∈ Finset.univ.erase ⟨i, hi⟩, T i x.val * v x) := by
          rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun x _ => by ring
        linarith
      have hle : (-T i i) * |v ⟨i, hi⟩| ≤ ∑ j ∈ Finset.univ.erase ⟨i, hi⟩, T i j.val * |v j| := by
        calc (-T i i) * |v ⟨i, hi⟩|
            = |(-T i i) * v ⟨i, hi⟩| := by rw [abs_mul, abs_of_pos (neg_pos.mpr (hdiag i))]
          _ = |∑ j ∈ Finset.univ.erase ⟨i, hi⟩, T i j.val * v j| := by rw [hdiag_eq]
          _ ≤ ∑ j ∈ Finset.univ.erase ⟨i, hi⟩, |T i j.val * v j| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ j ∈ Finset.univ.erase ⟨i, hi⟩, T i j.val * |v j| := by
              refine Finset.sum_congr rfl fun j hj => ?_
              have hne : i ≠ j.val := fun h => (Finset.mem_erase.mp hj).1 (Subtype.ext h.symm)
              rw [abs_mul, abs_of_nonneg (hoff i j.val hne)]
      have hsum_eq : ∑ j ∈ Finset.univ.erase i, T i j * w j =
          ∑ j ∈ Finset.univ.erase ⟨i, hi⟩, T i j.val * |v j| := by
        have h1 : ∑ j ∈ Finset.univ.erase i, T i j * w j =
            ∑ j ∈ (Finset.univ.erase i).filter (· ∈ S), T i j * w j := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun j _ => ?_
          by_cases hj : j ∈ S
          · rw [if_pos hj]
          · rw [if_neg hj]; simp [w, hj]
        rw [h1]
        refine Finset.sum_bij (fun j hj => ⟨j, (Finset.mem_filter.mp hj).2⟩) ?_ ?_ ?_ ?_
        · intro j hj; exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp (Finset.mem_filter.mp hj).1).1 (congrArg Subtype.val h), Finset.mem_univ _⟩
        · intro j₁ _ j₂ _ h; exact congrArg Subtype.val h
        · intro j hj; exact ⟨j.val, Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hj).1 (Subtype.ext h), Finset.mem_univ _⟩, j.prop⟩, Subtype.ext rfl⟩
        · intro j hj; simp [w, (Finset.mem_filter.mp hj).2]
      have hmul : (T.mulVec w) i = T i i * w i + ∑ j ∈ Finset.univ.erase i, T i j * w j := by
        simp only [Matrix.mulVec, dotProduct]; rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      rw [hmul, hsum_eq]
      have hwi : w i = |v ⟨i, hi⟩| := dif_pos hi
      rw [hwi]; linarith
    · have hwi0 : w i = 0 := dif_neg hi
      have hmul : (T.mulVec w) i = T i i * w i + ∑ j ∈ Finset.univ.erase i, T i j * w j := by
        simp only [Matrix.mulVec, dotProduct]; rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      rw [hmul, hwi0, mul_zero, zero_add]
      exact Finset.sum_nonneg fun j hj =>
        mul_nonneg (hoff i j (Finset.mem_erase.mp hj).1.symm) (hw_nonneg j)
  -- Take `M = max_i w i > 0` and `K = {i | w i = M}` (nonempty).
  obtain ⟨i0, hi0_pos⟩ := hw_ne
  obtain ⟨imax, _, himax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin m)) w ⟨i0, Finset.mem_univ i0⟩
  set M := w imax
  have hM_pos : 0 < M := lt_of_lt_of_le hi0_pos (himax i0 (Finset.mem_univ i0))
  let K : Finset (Fin m) := Finset.univ.filter fun i => w i = M
  have hKne : K.Nonempty := ⟨imax, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  -- For every `i ∈ K`, `∑ j, T i j = 0` and `∀ j ∉ K, T i j = 0`.
  have hK_prop : ∀ i ∈ K, (∑ j : Fin m, T i j = 0) ∧ (∀ j, j ∉ K → T i j = 0) := by
    intro i hiK
    have hwi : w i = M := (Finset.mem_filter.mp hiK).2
    have hge0 : 0 ≤ (T.mulVec w) i := hTw_nonneg i
    have hdiff_nonneg : ∀ j ∈ Finset.univ.erase i, 0 ≤ T i j * (M - w j) := fun j hj =>
      mul_nonneg (hoff i j (Finset.mem_erase.mp hj).1.symm) (sub_nonneg.mpr (himax j (Finset.mem_univ j)))
    have hsum_id : (∑ j : Fin m, T i j) * M - (T.mulVec w) i =
        ∑ j ∈ Finset.univ.erase i, T i j * (M - w j) := by
      simp only [Matrix.mulVec, dotProduct]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
          ← Finset.add_sum_erase (f := fun j => T i j * w j) _ (Finset.mem_univ i),
          hwi, add_mul, Finset.sum_mul]
      rw [show T i i * M + ∑ j ∈ Finset.univ.erase i, T i j * M -
            (T i i * M + ∑ j ∈ Finset.univ.erase i, T i j * w j) =
            ∑ j ∈ Finset.univ.erase i, (T i j * M - T i j * w j) by
          rw [Finset.sum_sub_distrib]; ring]
      refine Finset.sum_congr rfl fun j _ => by ring
    have hrow_le : (∑ j : Fin m, T i j) * M ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (hrow i) (le_of_lt hM_pos)
    have hsum_ge0 : 0 ≤ ∑ j ∈ Finset.univ.erase i, T i j * (M - w j) := Finset.sum_nonneg hdiff_nonneg
    have hsum0 : ∑ j ∈ Finset.univ.erase i, T i j * (M - w j) = 0 := by linarith
    have hrow0 : ∑ j : Fin m, T i j = 0 := by
      have : (∑ j : Fin m, T i j) * M = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_right (ne_of_gt hM_pos)
    refine ⟨hrow0, fun j hjK => ?_⟩
    have hji : j ≠ i := fun h => hjK (h ▸ hiK)
    have hj_in : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩
    have hterm0 := (Finset.sum_eq_zero_iff_of_nonneg hdiff_nonneg).mp hsum0 j hj_in
    have hwj_lt : M - w j ≠ 0 := by
      intro h0
      exact hjK (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by linarith⟩)
    exact (mul_eq_zero.mp hterm0).resolve_right hwj_lt
  -- Reindex `Fin m ≃ {i // i ∈ K} ⊕ {i // i ∉ K}`: `T` is block lower-triangular with singular `K × K` block!
  let e : { i : Fin m // i ∈ K } ⊕ { i : Fin m // i ∉ K } ≃ Fin m :=
    (Equiv.sumCompl (· ∈ K))
  let B := T.submatrix e e
  have hdet_eq : B.det = T.det := Matrix.det_submatrix_equiv_self e T
  have hblock : Matrix.toBlocks₁₂ B = 0 := by
    ext i j
    simp only [B, Matrix.toBlocks₁₂, Matrix.submatrix_apply, Matrix.zero_apply, Matrix.of_apply, e, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr]
    exact (hK_prop i.val i.prop).2 j.val j.prop
  have hdet_mul : B.det = (Matrix.toBlocks₁₁ B).det * (Matrix.toBlocks₂₂ B).det := by
    calc B.det = (Matrix.fromBlocks (Matrix.toBlocks₁₁ B) (Matrix.toBlocks₁₂ B) (Matrix.toBlocks₂₁ B) (Matrix.toBlocks₂₂ B)).det := by
          rw [Matrix.fromBlocks_toBlocks]
      _ = (Matrix.fromBlocks (Matrix.toBlocks₁₁ B) 0 (Matrix.toBlocks₂₁ B) (Matrix.toBlocks₂₂ B)).det := by
          rw [hblock]
      _ = (Matrix.toBlocks₁₁ B).det * (Matrix.toBlocks₂₂ B).det := Matrix.det_fromBlocks_zero₁₂ _ _ _
  have hdet11_zero : (Matrix.toBlocks₁₁ B).det = 0 := by
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨fun _ => 1, ?_, ?_⟩
    · intro h0
      obtain ⟨k, hk⟩ := hKne
      have := congrFun h0 ⟨k, hk⟩
      simp at this
    · ext i
      simp only [Matrix.mulVec, dotProduct, Matrix.toBlocks₁₁, Matrix.submatrix_apply, Matrix.of_apply,
        B, e, Equiv.sumCompl_apply_inl, mul_one, Pi.zero_apply]
      have hfull := (hK_prop i.val i.prop).1
      have hsub : ∑ x : { j : Fin m // j ∈ K }, T i.val x.val = ∑ j ∈ K, T i.val j :=
        Finset.sum_coe_sort K (fun j => T i.val j)
      rw [hsub, ← hfull]
      rw [← Finset.sum_subset (Finset.subset_univ K)]
      intro j _ hjK
      exact (hK_prop i.val i.prop).2 j hjK
  have hT0 : T.det = 0 := by rw [← hdet_eq, hdet_mul, hdet11_zero, zero_mul]
  exact hurwitz_det_ne_zero hH hT0

private lemma transient_principal_det_pos {m : ℕ} {T : Matrix (Fin m) (Fin m) ℝ}
    (hT : IsTransientSubgenerator T) (S : Finset (Fin m)) :
    0 < ((-T).submatrix (Subtype.val : { i : Fin m // i ∈ S } → Fin m) Subtype.val).det := by
  let A : Matrix { i : Fin m // i ∈ S } { i : Fin m // i ∈ S } ℝ :=
    (-T).submatrix Subtype.val Subtype.val
  let I_S : Matrix { i : Fin m // i ∈ S } { i : Fin m // i ∈ S } ℝ := 1
  have hne0 : A.det ≠ 0 := transient_principal_det_ne_zero hT S
  -- Consider `f(t) = (t • 1 + A).det = Polynomial.eval t (-A).charpoly`.
  let f : ℝ → ℝ := fun t => Polynomial.eval t (-A).charpoly
  have hf_eq : ∀ t : ℝ, f t = (t • I_S + A).det := fun t => by
    simp only [f, I_S, eval_charpoly_eq_det, sub_neg_eq_add]
  have hf_ne : ∀ t : ℝ, 0 < t → f t ≠ 0 := fun t ht => by
    rw [hf_eq]
    apply det_ne_zero_of_strictDiagDom
    intro i
    have hdiag_t : (t • I_S + A) i i = t + (-T i.val i.val) := by
      simp only [I_S, A, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq,
        Matrix.submatrix_apply, Matrix.neg_apply, smul_eq_mul, mul_one]
    rw [hdiag_t]
    have hsum_le : ∑ j ∈ Finset.univ.erase i, |(t • I_S + A) i j| ≤
        ∑ j ∈ Finset.univ.erase i.val, T i.val j := by
      have h1 : ∑ j ∈ Finset.univ.erase i, |(t • I_S + A) i j| =
          ∑ j ∈ Finset.univ.erase i, T i.val j.val := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hne : i ≠ j := (Finset.mem_erase.mp hj).1.symm
        have hne' : i.val ≠ j.val := fun h => hne (Subtype.ext h)
        simp only [I_S, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, if_neg hne, smul_zero,
          zero_add, A, Matrix.submatrix_apply, Matrix.neg_apply, abs_neg,
          abs_of_nonneg (hT.2.2.1 i.val j.val hne')]
      rw [h1]
      have h2 : ∑ j ∈ Finset.univ.erase i, T i.val j.val =
          ∑ j ∈ S.erase i.val, T i.val j := by
        refine Finset.sum_bij (fun j _ => j.val) ?_ ?_ ?_ ?_
        · intro j hj; exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hj).1 (Subtype.ext h), j.prop⟩
        · intro j₁ _ j₂ _ h; exact Subtype.ext h
        · intro j hj; exact ⟨⟨j, (Finset.mem_erase.mp hj).2⟩, Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hj).1 (congrArg Subtype.val h), Finset.mem_univ _⟩, rfl⟩
        · intro _ _; rfl
      rw [h2]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset_erase _ (Finset.subset_univ S))
        fun j hj _ => hT.2.2.1 i.val j (Finset.mem_erase.mp hj).1.symm
    have hrow_i := hT.2.2.2 i.val
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i.val)] at hrow_i
    linarith
  -- For large `t > 0`, `f t > 0` because `(-A).charpoly` is monic.
  have hf_large : ∃ R : ℝ, 0 < R ∧ 0 < f R := by
    by_cases hdeg : (-A).charpoly.natDegree = 0
    · have hmon := Matrix.charpoly_monic (-A)
      have h1 : (-A).charpoly = 1 := Polynomial.eq_one_of_monic_natDegree_zero hmon hdeg
      exact ⟨1, zero_lt_one, by simp [f, h1]⟩
    · have htend : Filter.Tendsto f Filter.atTop Filter.atTop := by
        have hlc : 0 < (-A).charpoly.leadingCoeff := by rw [(Matrix.charpoly_monic (-A)).leadingCoeff]; exact zero_lt_one
        have hdeg_pos : 0 < (-A).charpoly.degree := by
          rw [Polynomial.degree_eq_natDegree (Matrix.charpoly_monic (-A)).ne_zero]
          exact_mod_cast Nat.pos_of_ne_zero hdeg
        exact Polynomial.tendsto_atTop_of_leadingCoeff_nonneg _ hdeg_pos (le_of_lt hlc)
      have hev := (Filter.tendsto_atTop.mp htend) 1
      obtain ⟨R0, hR0⟩ := Filter.eventually_atTop.mp hev
      exact ⟨max R0 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), lt_of_lt_of_le zero_lt_one (hR0 _ (le_max_left _ _))⟩
  obtain ⟨R, hR_pos, hR_fpos⟩ := hf_large
  -- By IVT, `f t > 0` for all `t > 0`.
  have hf_pos : ∀ t : ℝ, 0 < t → 0 < f t := by
    intro t ht
    by_contra hle
    have hlt : f t < 0 := lt_of_le_of_ne (not_lt.mp hle) (hf_ne t ht)
    by_cases htR : t ≤ R
    · have hmem : (0 : ℝ) ∈ Set.Icc (f t) (f R) := ⟨le_of_lt hlt, le_of_lt hR_fpos⟩
      obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc htR (Polynomial.continuous (-A).charpoly).continuousOn hmem
      exact hf_ne c (lt_of_lt_of_le ht hc.1) hfc
    · have hRt : R ≤ t := le_of_not_ge htR
      have hmem : (0 : ℝ) ∈ Set.Icc (f t) (f R) := ⟨le_of_lt hlt, le_of_lt hR_fpos⟩
      obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc' hRt (Polynomial.continuous (-A).charpoly).continuousOn hmem
      exact hf_ne c (lt_of_lt_of_le hR_pos hc.1) hfc
  -- By continuity at `t = 0`, `f 0 ≥ 0`; since `f 0 = A.det ≠ 0`, `0 < A.det`.
  have hf0_nonneg : 0 ≤ f 0 := by
    have hcont : Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds (f 0)) :=
      (Polynomial.continuous (-A).charpoly).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact ge_of_tendsto hcont (eventually_nhdsWithin_of_forall fun t ht => le_of_lt (hf_pos t ht))
  have hf0_eq : f 0 = A.det := by rw [hf_eq, zero_smul, zero_add]
  rw [hf0_eq] at hf0_nonneg
  exact lt_of_le_of_ne hf0_nonneg hne0.symm

/-! ### Section 2: Multivariate Fornasini–Marchesini Realization and `MVME_n = MME*_n` (Theorem 3.4) -/

/-- A function `f : (Fin n → ℝ) → ℝ` has a zero-at-origin Fornasini–Marchesini realization on an open
neighborhood of `0` if `f(s) = ηᵀ (I - ∑ s_j A_j)⁻¹ (∑ s_j c_j)`. -/
private def HasZeroFM {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (N : ℕ) (η : Fin N → ℝ) (A : Fin n → Matrix (Fin N) (Fin N) ℝ) (c : Fin n → Fin N → ℝ)
    (U : Set (Fin n → ℝ)),
    IsOpen U ∧ (0 : Fin n → ℝ) ∈ U ∧
    ∀ s ∈ U,
      IsUnit (1 - ∑ j : Fin n, s j • A j).det ∧
      f s = dotProduct η ((1 - ∑ j : Fin n, s j • A j)⁻¹.mulVec (∑ j : Fin n, s j • c j))

private lemma hasZeroFM_zero (n : ℕ) : HasZeroFM (fun _ : Fin n → ℝ => (0 : ℝ)) :=
  ⟨1, 0, 0, 0, Set.univ, isOpen_univ, trivial, fun _ _ => by simp⟩

private lemma submatrix_mul_submatrix {ι κ R : Type*} [Fintype ι] [Fintype κ] [Semiring R]
    (e : ι ≃ κ) (M N : Matrix ι ι R) :
    M.submatrix e.symm e.symm * N.submatrix e.symm e.symm = (M * N).submatrix e.symm e.symm := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp e.symm (fun k => M (e.symm x) k * N k (e.symm y))

private lemma hasZeroFM_var {n : ℕ} (k : Fin n) : HasZeroFM (fun s : Fin n → ℝ => s k) := by
  refine ⟨1, fun _ => 1, 0, fun j _ => if j = k then 1 else 0, Set.univ, isOpen_univ, trivial, fun s _ => ?_⟩
  have h1 : (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ = 1 := Matrix.inv_eq_right_inv (Matrix.mul_one 1)
  simp only [Pi.zero_apply, smul_zero, Finset.sum_const_zero, sub_zero, Matrix.det_one, isUnit_one,
    h1, Matrix.one_mulVec, dotProduct, Fin.sum_univ_one, one_mul, true_and]
  rw [Finset.sum_apply, Finset.sum_eq_single k]
  · simp
  · intro j _ hjk; simp [hjk]
  · intro hk; exact absurd (Finset.mem_univ k) hk

private lemma hasZeroFM_smul {n : ℕ} (r : ℝ) {f : (Fin n → ℝ) → ℝ} (hf : HasZeroFM f) :
    HasZeroFM (fun s => r * f s) := by
  obtain ⟨N, η, A, c, U, hUo, hU0, hU⟩ := hf
  refine ⟨N, r • η, A, c, U, hUo, hU0, fun s hs => ?_⟩
  obtain ⟨hu, heq⟩ := hU s hs
  exact ⟨hu, by dsimp only; rw [heq, smul_dotProduct, smul_eq_mul]⟩

private lemma hasZeroFM_add {n : ℕ} {f g : (Fin n → ℝ) → ℝ} (hf : HasZeroFM f) (hg : HasZeroFM g) :
    HasZeroFM (fun s => f s + g s) := by
  obtain ⟨N₁, η₁, A₁, c₁, U₁, hU₁o, hU₁0, hU₁⟩ := hf
  obtain ⟨N₂, η₂, A₂, c₂, U₂, hU₂o, hU₂0, hU₂⟩ := hg
  let e : Fin N₁ ⊕ Fin N₂ ≃ Fin (N₁ + N₂) := finSumFinEquiv
  let η : Fin (N₁ + N₂) → ℝ := Sum.elim η₁ η₂ ∘ e.symm
  let A : Fin n → Matrix (Fin (N₁ + N₂)) (Fin (N₁ + N₂)) ℝ := fun j =>
    (Matrix.fromBlocks (A₁ j) 0 0 (A₂ j)).submatrix e.symm e.symm
  let c : Fin n → Fin (N₁ + N₂) → ℝ := fun j => Sum.elim (c₁ j) (c₂ j) ∘ e.symm
  refine ⟨N₁ + N₂, η, A, c, U₁ ∩ U₂, hU₁o.inter hU₂o, ⟨hU₁0, hU₂0⟩, fun s hs => ?_⟩
  obtain ⟨hu₁, hf_s⟩ := hU₁ s hs.1
  obtain ⟨hu₂, hg_s⟩ := hU₂ s hs.2
  let M₁ := 1 - ∑ j : Fin n, s j • A₁ j
  let M₂ := 1 - ∑ j : Fin n, s j • A₂ j
  let M := 1 - ∑ j : Fin n, s j • A j
  have hM_eq : M = (Matrix.fromBlocks M₁ 0 0 M₂).submatrix e.symm e.symm := by
    ext p q
    obtain ⟨p', rfl⟩ := e.surjective p
    obtain ⟨q', rfl⟩ := e.surjective q
    cases p' <;> cases q' <;>
      simp [M, M₁, M₂, A, Matrix.sum_apply, Matrix.one_apply, e.symm_apply_apply]
  have hdet : M.det = M₁.det * M₂.det := by
    rw [hM_eq, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₁₂]
  have hu : IsUnit M.det := hdet ▸ hu₁.mul hu₂
  refine ⟨hu, ?_⟩
  have hinv : M⁻¹ = (Matrix.fromBlocks M₁⁻¹ 0 0 M₂⁻¹).submatrix e.symm e.symm := by
    apply Matrix.inv_eq_right_inv
    rw [hM_eq, submatrix_mul_submatrix, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
        Matrix.mul_nonsing_inv M₁ hu₁, Matrix.mul_nonsing_inv M₂ hu₂]
    ext p q
    obtain ⟨p', rfl⟩ := e.surjective p
    obtain ⟨q', rfl⟩ := e.surjective q
    cases p' <;> cases q' <;> simp [Matrix.one_apply, e.symm_apply_apply]
  have hv : ∑ j : Fin n, s j • c j = Sum.elim (∑ j : Fin n, s j • c₁ j) (∑ j : Fin n, s j • c₂ j) ∘ e.symm := by
    ext p; obtain ⟨p', rfl⟩ := e.surjective p
    cases p' <;> simp [c, Finset.sum_apply, e.symm_apply_apply]
  have hmv : M⁻¹.mulVec (∑ j : Fin n, s j • c j) =
      Sum.elim (M₁⁻¹.mulVec (∑ j : Fin n, s j • c₁ j)) (M₂⁻¹.mulVec (∑ j : Fin n, s j • c₂ j)) ∘ e.symm := by
    rw [hinv, hv]
    ext p; obtain ⟨p', rfl⟩ := e.surjective p
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Function.comp_apply]
    rw [← e.sum_comp]
    cases p' <;> simp [Fintype.sum_sum_type, e.symm_apply_apply, Matrix.mulVec, dotProduct, Finset.sum_apply]
  dsimp only
  rw [show (1 - ∑ j : Fin n, s j • A j)⁻¹ = M⁻¹ from rfl, hmv, hf_s, hg_s]
  simp only [dotProduct, η, Function.comp_apply]
  rw [← e.sum_comp]
  simp [Fintype.sum_sum_type, e.symm_apply_apply, M₁, M₂]

private lemma hasZeroFM_mul {n : ℕ} {f g : (Fin n → ℝ) → ℝ} (hf : HasZeroFM f) (hg : HasZeroFM g) :
    HasZeroFM (fun s => f s * g s) := by
  obtain ⟨N₁, η₁, A₁, c₁, U₁, hU₁o, hU₁0, hU₁⟩ := hf
  obtain ⟨N₂, η₂, A₂, c₂, U₂, hU₂o, hU₂0, hU₂⟩ := hg
  let e : Fin N₁ ⊕ Fin N₂ ≃ Fin (N₁ + N₂) := finSumFinEquiv
  let η : Fin (N₁ + N₂) → ℝ := Sum.elim η₁ (0 : Fin N₂ → ℝ) ∘ e.symm
  let A : Fin n → Matrix (Fin (N₁ + N₂)) (Fin (N₁ + N₂)) ℝ := fun j =>
    (Matrix.fromBlocks (A₁ j) (Matrix.vecMulVec (c₁ j) η₂) 0 (A₂ j)).submatrix e.symm e.symm
  let c : Fin n → Fin (N₁ + N₂) → ℝ := fun j => Sum.elim (0 : Fin N₁ → ℝ) (c₂ j) ∘ e.symm
  refine ⟨N₁ + N₂, η, A, c, U₁ ∩ U₂, hU₁o.inter hU₂o, ⟨hU₁0, hU₂0⟩, fun s hs => ?_⟩
  obtain ⟨hu₁, hf_s⟩ := hU₁ s hs.1
  obtain ⟨hu₂, hg_s⟩ := hU₂ s hs.2
  let M₁ := 1 - ∑ j : Fin n, s j • A₁ j
  let M₂ := 1 - ∑ j : Fin n, s j • A₂ j
  let v₁ := ∑ j : Fin n, s j • c₁ j
  let v₂ := ∑ j : Fin n, s j • c₂ j
  let B₁₂ : Matrix (Fin N₁) (Fin N₂) ℝ := -(Matrix.vecMulVec v₁ η₂)
  let M := 1 - ∑ j : Fin n, s j • A j
  have hM_eq : M = (Matrix.fromBlocks M₁ B₁₂ 0 M₂).submatrix e.symm e.symm := by
    ext p q
    obtain ⟨p', rfl⟩ := e.surjective p
    obtain ⟨q', rfl⟩ := e.surjective q
    cases p' <;> cases q' <;>
      simp [M, M₁, M₂, B₁₂, v₁, A, Matrix.sum_apply, Matrix.one_apply, Matrix.vecMulVec_apply,
        Finset.sum_apply, Finset.sum_mul, e.symm_apply_apply, mul_assoc]
  have hdet : M.det = M₁.det * M₂.det := by
    rw [hM_eq, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
  have hu : IsUnit M.det := hdet ▸ hu₁.mul hu₂
  refine ⟨hu, ?_⟩
  let R : Matrix (Fin N₁) (Fin N₂) ℝ := -(M₁⁻¹ * B₁₂ * M₂⁻¹)
  have hinv : M⁻¹ = (Matrix.fromBlocks M₁⁻¹ R 0 M₂⁻¹).submatrix e.symm e.symm := by
    apply Matrix.inv_eq_right_inv
    rw [hM_eq, submatrix_mul_submatrix, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
        Matrix.mul_nonsing_inv M₁ hu₁, Matrix.mul_nonsing_inv M₂ hu₂]
    have h12 : M₁ * R + B₁₂ * M₂⁻¹ = 0 := by
      dsimp only [R]
      rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv M₁ hu₁, Matrix.one_mul, neg_add_cancel]
    rw [h12]
    ext p q; obtain ⟨p', rfl⟩ := e.surjective p; obtain ⟨q', rfl⟩ := e.surjective q
    cases p' <;> cases q' <;> simp [Matrix.one_apply, e.symm_apply_apply]
  have hv : ∑ j : Fin n, s j • c j = Sum.elim (0 : Fin N₁ → ℝ) v₂ ∘ e.symm := by
    ext p; obtain ⟨p', rfl⟩ := e.surjective p
    cases p' <;> simp [c, v₂, Finset.sum_apply, e.symm_apply_apply]
  have hmv : M⁻¹.mulVec (∑ j : Fin n, s j • c j) = Sum.elim (R.mulVec v₂) (M₂⁻¹.mulVec v₂) ∘ e.symm := by
    rw [hinv, hv]
    ext p; obtain ⟨p', rfl⟩ := e.surjective p
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Function.comp_apply]
    rw [← e.sum_comp]
    cases p' <;> simp [Fintype.sum_sum_type, e.symm_apply_apply, Matrix.mulVec, dotProduct]
  dsimp only
  rw [show (1 - ∑ j : Fin n, s j • A j)⁻¹ = M⁻¹ from rfl, hmv, hf_s, hg_s]
  have hdot : dotProduct η (Sum.elim (R.mulVec v₂) (M₂⁻¹.mulVec v₂) ∘ e.symm) = dotProduct η₁ (R.mulVec v₂) := by
    simp only [dotProduct, η, Function.comp_apply]
    rw [← e.sum_comp]; simp [Fintype.sum_sum_type, e.symm_apply_apply]
  rw [hdot]
  have hR_mv : R.mulVec v₂ = dotProduct η₂ (M₂⁻¹.mulVec v₂) • M₁⁻¹.mulVec v₁ := by
    dsimp only [R, B₁₂]
    rw [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have hvmv : (Matrix.vecMulVec v₁ η₂).mulVec (M₂⁻¹.mulVec v₂) = dotProduct η₂ (M₂⁻¹.mulVec v₂) • v₁ := by
      ext i; simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => by ring
    rw [hvmv, Matrix.mulVec_smul]
  rw [hR_mv, dotProduct_smul, smul_eq_mul, mul_comm]

private lemma hasZeroFM_inv_sub {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : HasZeroFM f) :
    HasZeroFM (fun s => f s / (1 - f s)) := by
  obtain ⟨N, η, A, c, U, hUo, hU0, hU⟩ := hf
  let A' : Fin n → Matrix (Fin N) (Fin N) ℝ := fun j => A j + Matrix.vecMulVec (c j) η
  -- `U' = U ∩ {s | 1 - f s ≠ 0}` is open and contains `0`.
  let g : (Fin n → ℝ) → ℝ := fun s => 1 - dotProduct η ((1 - ∑ j : Fin n, s j • A j)⁻¹.mulVec (∑ j : Fin n, s j • c j))
  have hg_cont : ContinuousOn g U := by
    change ContinuousOn (fun s : Fin n → ℝ => 1 - ∑ i : Fin N, η i * ∑ k : Fin N,
        ((1 - ∑ j : Fin n, s j • A j)⁻¹ i k * (∑ j : Fin n, s j • c j) k)) U
    refine continuousOn_const.sub ?_
    refine continuousOn_finsetSum Finset.univ fun i _ => continuousOn_const.mul ?_
    refine continuousOn_finsetSum Finset.univ fun k _ => ?_
    have hM_cont : Continuous (fun s : Fin n → ℝ => (1 : Matrix (Fin N) (Fin N) ℝ) - ∑ j : Fin n, s j • A j) :=
      continuous_const.sub (continuous_finsetSum _ fun j _ => (continuous_apply j).smul continuous_const)
    have hinv_cont : ContinuousOn (fun s : Fin n → ℝ => ((1 : Matrix (Fin N) (Fin N) ℝ) - ∑ j : Fin n, s j • A j)⁻¹ i k) U := by
      have h1 : ∀ s ∈ U, ((1 : Matrix (Fin N) (Fin N) ℝ) - ∑ j : Fin n, s j • A j)⁻¹ i k =
          ((1 - ∑ j : Fin n, s j • A j).det)⁻¹ * ((1 - ∑ j : Fin n, s j • A j).adjugate i k) := fun s _ => by
        rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
      refine ContinuousOn.congr ?_ h1
      refine ContinuousOn.mul ?_ ?_
      · exact (hM_cont.matrix_det.continuousOn).inv₀ fun s hs => (hU s hs).1.ne_zero
      · exact ((continuous_apply k).comp ((continuous_apply i).comp hM_cont.matrix_adjugate)).continuousOn
    exact hinv_cont.mul ((continuous_apply k).comp (continuous_finsetSum _ fun j _ => (continuous_apply j).smul continuous_const)).continuousOn
  let U' : Set (Fin n → ℝ) := U ∩ { s | g s ≠ 0 }
  have hU'o : IsOpen U' := by
    have : U' = U ∩ g ⁻¹' {0}ᶜ := rfl
    rw [this]
    exact hg_cont.isOpen_inter_preimage hUo isClosed_singleton.isOpen_compl
  have hU'0 : (0 : Fin n → ℝ) ∈ U' := by
    refine ⟨hU0, ?_⟩
    simp [g]
  refine ⟨N, η, A', c, U', hU'o, hU'0, fun s hs => ?_⟩
  obtain ⟨hu, hf_s⟩ := hU s hs.1
  have hgs : 1 - f s ≠ 0 := by
    have : g s = 1 - f s := by dsimp [g]; rw [hf_s]
    rw [← this]; exact hs.2
  let M := (1 : Matrix (Fin N) (Fin N) ℝ) - ∑ j : Fin n, s j • A j
  let v := ∑ j : Fin n, s j • c j
  let M' := (1 : Matrix (Fin N) (Fin N) ℝ) - ∑ j : Fin n, s j • A' j
  have hM'_eq : M' = M - Matrix.vecMulVec v η := by
    ext i k
    simp only [M', M, A', v, Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.add_apply,
      Matrix.vecMulVec_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_add,
      Finset.sum_add_distrib, Finset.sum_mul, mul_assoc]
    ring
  let w := M⁻¹.mulVec v
  let B : Matrix (Fin N) (Fin N) ℝ := M⁻¹ + (1 - f s)⁻¹ • Matrix.vecMulVec w (Matrix.vecMul η M⁻¹)
  have hM'B : M' * B = 1 := by
    rw [hM'_eq]
    dsimp only [B]
    rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_nonsing_inv M hu,
        Matrix.mul_smul, Matrix.mul_smul]
    have h1 : M * Matrix.vecMulVec w (Matrix.vecMul η M⁻¹) = Matrix.vecMulVec v (Matrix.vecMul η M⁻¹) := by
      ext i k
      simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, w]
      have : ∑ x, M i x * (M⁻¹.mulVec v x * Matrix.vecMul η M⁻¹ k) =
          (M.mulVec (M⁻¹.mulVec v)) i * Matrix.vecMul η M⁻¹ k := by
        simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]
      rw [this, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hu, Matrix.one_mulVec]
    have h2 : Matrix.vecMulVec v η * M⁻¹ = Matrix.vecMulVec v (Matrix.vecMul η M⁻¹) := by
      ext i k
      simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.vecMul, dotProduct, Finset.mul_sum, mul_assoc]
    have h3 : Matrix.vecMulVec v η * Matrix.vecMulVec w (Matrix.vecMul η M⁻¹) =
        f s • Matrix.vecMulVec v (Matrix.vecMul η M⁻¹) := by
      ext i k
      simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul]
      have : ∑ x, v i * η x * (w x * Matrix.vecMul η M⁻¹ k) =
          dotProduct η w * (v i * Matrix.vecMul η M⁻¹ k) := by
        simp only [dotProduct, Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => by ring
      rw [this, ← hf_s]
    rw [h1, h2, h3, smul_smul]
    ext i k
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    field_simp [hgs]
    ring
  have hu' : IsUnit M'.det := by
    have h := congrArg Matrix.det hM'B
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact isUnit_iff_ne_zero.mpr fun h0 => by rw [h0, zero_mul] at h; exact zero_ne_one h
  have hinv' : M'⁻¹ = B := Matrix.inv_eq_right_inv hM'B
  refine ⟨hu', ?_⟩
  rw [show (1 - ∑ j : Fin n, s j • A' j)⁻¹ = M'⁻¹ from rfl, hinv']
  dsimp only [B]
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
  have hvm : (Matrix.vecMulVec w (Matrix.vecMul η M⁻¹)).mulVec v = f s • w := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Matrix.vecMul, Pi.smul_apply, smul_eq_mul]
    have hassoc : dotProduct (Matrix.vecMul η M⁻¹) v = dotProduct η w := by
      simp only [dotProduct, Matrix.vecMul, w, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    calc ∑ x, w i * Matrix.vecMul η M⁻¹ x * v x
        = w i * dotProduct (Matrix.vecMul η M⁻¹) v := by simp only [dotProduct, Finset.mul_sum, mul_assoc]
      _ = w i * dotProduct η w := by rw [hassoc]
      _ = f s * w i := by rw [← hf_s, mul_comm]
  rw [hvm, dotProduct_smul, smul_eq_mul, ← hf_s]
  field_simp [hgs]
  ring

private lemma hasZeroFM_poly {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    HasZeroFM (fun s => MvPolynomial.eval s P - MvPolynomial.eval 0 P) := by
  induction P using MvPolynomial.induction_on' with
  | add p q hp hq =>
    have heq : (fun s => MvPolynomial.eval s (p + q) - MvPolynomial.eval 0 (p + q)) =
        (fun s => (MvPolynomial.eval s p - MvPolynomial.eval 0 p) + (MvPolynomial.eval s q - MvPolynomial.eval 0 q)) := by
      ext s; simp; ring
    rw [heq]; exact hasZeroFM_add hp hq
  | monomial d r =>
    by_cases hd : d = 0
    · subst hd
      have heq : (fun s : Fin n → ℝ => MvPolynomial.eval s (MvPolynomial.monomial (0 : Fin n →₀ ℕ) r) -
            MvPolynomial.eval 0 (MvPolynomial.monomial (0 : Fin n →₀ ℕ) r)) = fun _ => 0 := by
        ext s; simp
      rw [heq]; exact hasZeroFM_zero n
    · have heval0 : MvPolynomial.eval 0 (monomial d r) = 0 := by
        rw [MvPolynomial.eval_monomial]
        have hex : ∃ j : Fin n, d j ≠ 0 := by
          by_contra hall; push Not at hall; exact hd (Finsupp.ext hall)
        obtain ⟨j, hj⟩ := hex
        rw [Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hj) (zero_pow hj), mul_zero]
      have heq : (fun s : Fin n → ℝ => MvPolynomial.eval s (monomial d r) - MvPolynomial.eval 0 (monomial d r)) =
          fun s => r * (d.prod fun j k => s j ^ k) := by
        ext s; rw [heval0, sub_zero, MvPolynomial.eval_monomial]
      rw [heq]
      apply hasZeroFM_smul
      -- Prove `HasZeroFM (fun s => d.prod fun j k => s j ^ k)` for `d ≠ 0` by induction on `d.sum (fun _ k => k)`.
      generalize hm : d.sum (fun _ k => k) = m
      have hm_pos : 0 < m := by
        rw [← hm]
        have hex : ∃ j : Fin n, d j ≠ 0 := by
          by_contra hall; push Not at hall; exact hd (Finsupp.ext hall)
        obtain ⟨j, hj⟩ := hex
        exact lt_of_lt_of_le (Nat.pos_of_ne_zero hj)
          (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finsupp.mem_support_iff.mpr hj))
      clear hd r heval0 heq
      induction m generalizing d with
      | zero => omega
      | succ m ih =>
        obtain ⟨j0, hj0⟩ : ∃ j : Fin n, 0 < d j := by
          by_contra hall; push Not at hall
          have h0 : d = 0 := Finsupp.ext fun j => Nat.le_zero.mp (hall j)
          rw [h0] at hm; simp at hm
        by_cases hm0 : m = 0
        · subst hm0
          have hd_eq : d = Finsupp.single j0 1 := by
            have hdj0 : d j0 = 1 := by
              have hle := Finset.single_le_sum (f := fun j => d j) (fun _ _ => Nat.zero_le _) (Finsupp.mem_support_iff.mpr (ne_of_gt hj0))
              change d j0 ≤ d.sum (fun _ k => k) at hle; omega
            ext j
            by_cases hjj : j = j0
            · subst hjj; simp only [Finsupp.single_eq_same]; exact hdj0
            · simp only [Finsupp.single_apply, if_neg (Ne.symm hjj)]
              by_contra hne
              have hsum : d j0 + d j ≤ d.sum (fun _ k => k) := by
                have hpair : ({j0, j} : Finset (Fin n)) ⊆ d.support := by
                  intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                  rcases hx with rfl | rfl <;> exact Finsupp.mem_support_iff.mpr (by omega)
                calc d j0 + d j = ∑ x ∈ ({j0, j} : Finset (Fin n)), d x := (Finset.sum_pair (Ne.symm hjj)).symm
                  _ ≤ ∑ x ∈ d.support, d x := Finset.sum_le_sum_of_subset_of_nonneg hpair fun _ _ _ => Nat.zero_le _
              omega
          have hprod : (fun s : Fin n → ℝ => d.prod fun j k => s j ^ k) = fun s => s j0 := by
            ext s; rw [hd_eq, Finsupp.prod_single_index (h := fun j k => s j ^ k) (pow_zero _), pow_one]
          rw [hprod]; exact hasZeroFM_var j0
        · let d' : Fin n →₀ ℕ := d - Finsupp.single j0 1
          have hd_eq : d = d' + Finsupp.single j0 1 := by
            ext j; simp only [d', Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
            split_ifs with h
            · subst h; omega
            · omega
          have hsum' : d'.sum (fun _ k => k) = m := by
            have h1 : d.sum (fun _ k => k) = d'.sum (fun _ k => k) + (Finsupp.single j0 1).sum (fun _ k => k) := by
              rw [hd_eq, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
            rw [Finsupp.sum_single_index rfl] at h1; omega
          have hprod : (fun s : Fin n → ℝ => d.prod fun j k => s j ^ k) =
              fun s => (d'.prod fun j k => s j ^ k) * s j0 := by
            ext s
            rw [hd_eq, Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
                Finsupp.prod_single_index (h := fun j k => s j ^ k) (pow_zero _), pow_one]
          rw [hprod]
          exact hasZeroFM_mul (ih d' hsum' (by omega)) (hasZeroFM_var j0)

private lemma hasZeroFM_rat {n : ℕ} (P Q : MvPolynomial (Fin n) ℝ) (hQ0 : MvPolynomial.eval 0 Q ≠ 0) :
    HasZeroFM (fun s => MvPolynomial.eval s P / MvPolynomial.eval s Q - MvPolynomial.eval 0 P / MvPolynomial.eval 0 Q) := by
  let P₀ : (Fin n → ℝ) → ℝ := fun s => MvPolynomial.eval s P - MvPolynomial.eval 0 P
  let R₀ : (Fin n → ℝ) → ℝ := fun s => (-(MvPolynomial.eval 0 Q)⁻¹) * (MvPolynomial.eval s Q - MvPolynomial.eval 0 Q)
  have hP₀ : HasZeroFM P₀ := hasZeroFM_poly P
  have hR₀ : HasZeroFM R₀ := hasZeroFM_smul _ (hasZeroFM_poly Q)
  have hinvR : HasZeroFM (fun s => R₀ s / (1 - R₀ s)) := hasZeroFM_inv_sub hR₀
  have hcomb : HasZeroFM (fun s =>
      (MvPolynomial.eval 0 Q)⁻¹ * P₀ s +
      (MvPolynomial.eval 0 P / MvPolynomial.eval 0 Q) * (R₀ s / (1 - R₀ s)) +
      (MvPolynomial.eval 0 Q)⁻¹ * (P₀ s * (R₀ s / (1 - R₀ s)))) :=
    hasZeroFM_add (hasZeroFM_add (hasZeroFM_smul _ hP₀) (hasZeroFM_smul _ hinvR))
      (hasZeroFM_smul _ (hasZeroFM_mul hP₀ hinvR))
  obtain ⟨N, η, A, c, U, hUo, hU0, hU⟩ := hcomb
  let U' := U ∩ { s | MvPolynomial.eval s Q ≠ 0 }
  have hU'o : IsOpen U' := hUo.inter (isClosed_singleton.isOpen_compl.preimage (MvPolynomial.continuous_eval Q))
  have hU'0 : (0 : Fin n → ℝ) ∈ U' := ⟨hU0, hQ0⟩
  refine ⟨N, η, A, c, U', hU'o, hU'0, fun s hs => ?_⟩
  obtain ⟨hu, heq⟩ := hU s hs.1
  refine ⟨hu, ?_⟩
  rw [← heq]
  have hQs : MvPolynomial.eval s Q ≠ 0 := hs.2
  have h1R : 1 - R₀ s = MvPolynomial.eval s Q / MvPolynomial.eval 0 Q := by
    dsimp [R₀]; field_simp [hQ0]; ring
  have h1R_ne : 1 - R₀ s ≠ 0 := by rw [h1R]; exact div_ne_zero hQs hQ0
  dsimp [P₀]
  rw [h1R]
  dsimp [R₀]
  field_simp [hQ0, hQs]
  ring

/-- Lemma 3.4 helper: the `2q × 2q` block augmentation `Tmat` of `Umat` is invertible with
inverse `Bmat` and is Hurwitz-stable (every eigenvalue equals `-1`). -/
private lemma hurwitz_aug_props {q : ℕ} (Umat : Matrix (Fin q) (Fin q) ℝ) :
    let e2 : Fin q ⊕ Fin q ≃ Fin (q + q) := finSumFinEquiv
    let Bmat : Matrix (Fin (q + q)) (Fin (q + q)) ℝ :=
      (Matrix.fromBlocks Umat (-1) ((Umat + 1) ^ 2) (-Umat - 2)).submatrix e2.symm e2.symm
    let Tmat : Matrix (Fin (q + q)) (Fin (q + q)) ℝ :=
      (Matrix.fromBlocks (-Umat - 2) 1 (-((Umat + 1) ^ 2)) Umat).submatrix e2.symm e2.symm
    Bmat * Tmat = 1 ∧ Tmat * Bmat = 1 ∧ IsHurwitzStable Tmat := by
  intro e2 Bmat Tmat
  have h2_eq : (2 : Matrix (Fin q) (Fin q) ℝ) = 1 + 1 := one_add_one_eq_two.symm
  have hBT : Bmat * Tmat = 1 := by
    rw [show Bmat * Tmat = _ from submatrix_mul_submatrix e2 _ _, Matrix.fromBlocks_multiply]
    have h11 : Umat * (-Umat - 2) + (-1 : Matrix (Fin q) (Fin q) ℝ) * -((Umat + 1) ^ 2) = 1 := by
      simp only [sq]; noncomm_ring
    have h12 : Umat * 1 + (-1 : Matrix (Fin q) (Fin q) ℝ) * Umat = 0 := by noncomm_ring
    have h21 : (Umat + 1) ^ 2 * (-Umat - 2) + (-Umat - 2) * -((Umat + 1) ^ 2) = 0 := by
      simp only [sq]; noncomm_ring; rw [h2_eq]; simp only [neg_smul, two_smul]; abel
    have h22 : (Umat + 1) ^ 2 * 1 + (-Umat - 2) * Umat = 1 := by
      simp only [sq]; noncomm_ring
    rw [h11, h12, h21, h22]
    ext p r; obtain ⟨p', rfl⟩ := e2.surjective p; obtain ⟨r', rfl⟩ := e2.surjective r
    cases p' <;> cases r' <;> simp [Matrix.one_apply, e2.symm_apply_apply]
  have hTB : Tmat * Bmat = 1 := by
    rw [show Tmat * Bmat = _ from submatrix_mul_submatrix e2 _ _, Matrix.fromBlocks_multiply]
    have h11 : (-Umat - 2) * Umat + 1 * (Umat + 1) ^ 2 = 1 := by simp only [sq]; noncomm_ring
    have h12 : (-Umat - 2) * (-1) + 1 * (-Umat - 2) = 0 := by
      noncomm_ring; rw [h2_eq]; simp only [neg_smul, two_smul]; abel
    have h21 : -((Umat + 1) ^ 2) * Umat + Umat * (Umat + 1) ^ 2 = 0 := by simp only [sq]; noncomm_ring
    have h22 : -((Umat + 1) ^ 2) * (-1) + Umat * (-Umat - 2) = 1 := by simp only [sq]; noncomm_ring
    rw [h11, h12, h21, h22]
    ext p r; obtain ⟨p', rfl⟩ := e2.surjective p; obtain ⟨r', rfl⟩ := e2.surjective r
    cases p' <;> cases r' <;> simp [Matrix.one_apply, e2.symm_apply_apply]
  have hT_hurwitz : IsHurwitzStable Tmat := by
    intro μ hμ
    rw [Polynomial.IsRoot, eval_charpoly_eq_det] at hμ
    let Uc : Matrix (Fin q) (Fin q) ℂ := Umat.map Complex.ofReal
    have hsub : μ • (1 : Matrix (Fin (q + q)) (Fin (q + q)) ℂ) - Tmat.map Complex.ofReal =
        (Matrix.fromBlocks ((μ + 2) • 1 + Uc) (-1) ((Uc + 1) ^ 2) (μ • 1 - Uc)).submatrix e2.symm e2.symm := by
      have hsq : ((Umat + 1) ^ 2).map Complex.ofReal = (Uc + 1) ^ 2 := by
        change Complex.ofRealHom.mapMatrix ((Umat + 1) ^ 2) = (Complex.ofRealHom.mapMatrix Umat + 1) ^ 2
        simp only [map_pow, map_add, map_one]
      ext p r; obtain ⟨p', rfl⟩ := e2.surjective p; obtain ⟨r', rfl⟩ := e2.surjective r
      cases p' with
      | inl i =>
        cases r' with
        | inl j =>
          simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.map_apply,
            Matrix.submatrix_apply, Tmat, Matrix.fromBlocks_apply₁₁, Matrix.neg_apply,
            Matrix.add_apply, Uc, e2.symm_apply_apply, e2.injective.eq_iff, Sum.inl.injEq,
            smul_eq_mul, h2_eq]
          split_ifs <;> push_cast <;> ring
        | inr j =>
          simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.map_apply,
            Matrix.submatrix_apply, Tmat, Matrix.fromBlocks_apply₁₂, Matrix.neg_apply,
            e2.symm_apply_apply, e2.injective.eq_iff, reduceCtorEq, ↓reduceIte, smul_zero,
            zero_sub, neg_inj]
          split_ifs <;> simp
      | inr i =>
        cases r' with
        | inl j =>
          simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.map_apply,
            Matrix.submatrix_apply, Tmat, Matrix.fromBlocks_apply₂₁, Matrix.neg_apply,
            e2.symm_apply_apply, e2.injective.eq_iff, reduceCtorEq, ↓reduceIte, smul_zero,
            zero_sub, neg_neg, Complex.ofReal_neg]
          exact congrArg (fun M : Matrix (Fin q) (Fin q) ℂ => M i j) hsq
        | inr j =>
          simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.map_apply,
            Matrix.submatrix_apply, Tmat, Matrix.fromBlocks_apply₂₂, Uc, e2.symm_apply_apply,
            e2.injective.eq_iff, Sum.inr.injEq, smul_eq_mul]
    rw [hsub, Matrix.det_submatrix_equiv_self] at hμ
    have hblock_det : (Matrix.fromBlocks ((μ + 2) • 1 + Uc) (-1) ((Uc + 1) ^ 2) (μ • 1 - Uc)).det =
        ((μ + 1) ^ 2 • (1 : Matrix (Fin q) (Fin q) ℂ)).det := by
      have hprod : Matrix.fromBlocks (1 : Matrix (Fin q) (Fin q) ℂ) 0 (μ • 1 - Uc) 1 *
          Matrix.fromBlocks ((μ + 2) • 1 + Uc) (-1) ((Uc + 1) ^ 2) (μ • 1 - Uc) =
          Matrix.fromBlocks ((μ + 2) • 1 + Uc) (-1) ((μ + 1) ^ 2 • 1) 0 := by
        rw [Matrix.fromBlocks_multiply]
        congr 1
        · simp
        · simp
        · simp only [Matrix.one_mul, sq]
          ext i j; simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply,
            Matrix.one_apply, smul_eq_mul]
          have h1 : ∑ x, ((if i = x then μ else 0) - Uc i x) * ((if x = j then μ + 2 else 0) + Uc x j) =
              (if i = j then μ * (μ + 2) else 0) + μ * Uc i j - (μ + 2) * Uc i j - ∑ x, Uc i x * Uc x j := by
            have hexp : ∀ x, ((if i = x then μ else 0) - Uc i x) * ((if x = j then μ + 2 else 0) + Uc x j) =
                (if i = x then μ else 0) * (if x = j then μ + 2 else 0) +
                (if i = x then μ else 0) * Uc x j -
                Uc i x * (if x = j then μ + 2 else 0) - Uc i x * Uc x j := fun x => by ring
            simp_rw [hexp, Finset.sum_sub_distrib, Finset.sum_add_distrib]
            simp only [ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
              Finset.mem_univ, ↓reduceIte]
            split_ifs <;> ring
          have h2 : ∑ x, (Uc i x + if i = x then 1 else 0) * (Uc x j + if x = j then 1 else 0) =
              (∑ x, Uc i x * Uc x j) + 2 * Uc i j + if i = j then 1 else 0 := by
            have hexp : ∀ x, (Uc i x + if i = x then 1 else 0) * (Uc x j + if x = j then 1 else 0) =
                Uc i x * Uc x j + Uc i x * (if x = j then 1 else 0) +
                (if i = x then 1 else 0) * Uc x j + (if i = x then 1 else 0) * (if x = j then 1 else 0) := fun x => by ring
            simp_rw [hexp, Finset.sum_add_distrib]
            simp only [ite_mul, zero_mul, one_mul, mul_ite, mul_zero, mul_one, Finset.sum_ite_eq,
              Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
            split_ifs <;> ring
          simp only [mul_ite, mul_one, mul_zero]
          rw [h1, h2]; split_ifs <;> ring
        · simp
      have hd := congrArg Matrix.det hprod
      rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one, one_mul] at hd
      let sw : Fin q ⊕ Fin q ≃ Fin q ⊕ Fin q := Equiv.sumComm (Fin q) (Fin q)
      have hsw : (Matrix.fromBlocks ((μ + 2) • (1 : Matrix (Fin q) (Fin q) ℂ) + Uc)
            (-1 : Matrix (Fin q) (Fin q) ℂ) ((μ + 1) ^ 2 • (1 : Matrix (Fin q) (Fin q) ℂ))
            (0 : Matrix (Fin q) (Fin q) ℂ)).det =
          ((μ + 1) ^ 2 • (1 : Matrix (Fin q) (Fin q) ℂ)).det := by
        let J : Matrix (Fin q ⊕ Fin q) (Fin q ⊕ Fin q) ℂ :=
          Matrix.fromBlocks (0 : Matrix (Fin q) (Fin q) ℂ) (1 : Matrix (Fin q) (Fin q) ℂ)
            (1 : Matrix (Fin q) (Fin q) ℂ) (0 : Matrix (Fin q) (Fin q) ℂ)
        have hJM : J * Matrix.fromBlocks ((μ + 2) • (1 : Matrix (Fin q) (Fin q) ℂ) + Uc) (-1 : Matrix (Fin q) (Fin q) ℂ) ((μ + 1) ^ 2 • (1 : Matrix (Fin q) (Fin q) ℂ)) (0 : Matrix (Fin q) (Fin q) ℂ) =
            Matrix.fromBlocks ((μ + 1) ^ 2 • (1 : Matrix (Fin q) (Fin q) ℂ)) (0 : Matrix (Fin q) (Fin q) ℂ) ((μ + 2) • (1 : Matrix (Fin q) (Fin q) ℂ) + Uc) (-1 : Matrix (Fin q) (Fin q) ℂ) := by
          rw [Matrix.fromBlocks_multiply]; congr 1 <;> simp
        have hdJM := congrArg Matrix.det hJM
        rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_neg, Matrix.det_one, mul_one] at hdJM
        have hJdet : J.det = (-1 : ℂ) ^ q := by
          have hperm : J = Matrix.of fun a b => if sw a = b then (1 : ℂ) else 0 := by
            ext a b; cases a <;> cases b <;> simp [J, sw, Matrix.one_apply, eq_comm]
          have hdet_p : J.det = (Equiv.Perm.sign sw : ℂ) := by
            rw [hperm, Matrix.det_apply]
            rw [Finset.sum_eq_single sw]
            · simp [sw, Units.smul_def]
            · intro σ _ hσ
              have hex : ∃ a, sw a ≠ σ a := by
                by_contra hall; push Not at hall; exact hσ (Equiv.ext fun a => (hall a).symm)
              obtain ⟨a, ha⟩ := hex
              have ha' : sw (σ a) ≠ a := fun heq => ha (by
                have hinv : sw (sw (σ a)) = σ a := by cases σ a <;> rfl
                rw [← hinv, heq])
              rw [Finset.prod_eq_zero (Finset.mem_univ a) (by simp [ha']), smul_zero]
            · intro h; exact absurd (Finset.mem_univ _) h
          have hsign : (Equiv.Perm.sign sw : ℂ) = (-1 : ℂ) ^ q := by
            have hsw_prod : sw = (List.finRange q).foldr
                (fun i τ => Equiv.swap (Sum.inl i) (Sum.inr i) * τ) 1 := by
              have hgen : ∀ (L : List (Fin q)) (hnd : L.Nodup) (x : Fin q ⊕ Fin q),
                  (L.foldr (fun i τ => Equiv.swap (Sum.inl i) (Sum.inr i) * τ) 1) x =
                  match x with
                  | Sum.inl i => if i ∈ L then Sum.inr i else Sum.inl i
                  | Sum.inr i => if i ∈ L then Sum.inl i else Sum.inr i := by
                intro L
                induction L with
                | nil => intro _ x; cases x <;> simp
                | cons a L ih =>
                  intro hnd x
                  obtain ⟨haL, hndL⟩ := List.nodup_cons.mp hnd
                  simp only [List.foldr_cons, Equiv.Perm.coe_mul, Function.comp_apply, ih hndL]
                  cases x with
                  | inl i =>
                    by_cases hia : i = a
                    · subst hia; simp [haL]
                    · by_cases hiL : i ∈ L
                      · simp [hiL, hia, Equiv.swap_apply_of_ne_of_ne]
                      · simp [hiL, hia, Equiv.swap_apply_of_ne_of_ne]
                  | inr i =>
                    by_cases hia : i = a
                    · subst hia; simp [haL]
                    · by_cases hiL : i ∈ L
                      · simp [hiL, hia, Equiv.swap_apply_of_ne_of_ne]
                      · simp [hiL, hia, Equiv.swap_apply_of_ne_of_ne]
              ext x
              rw [hgen (List.finRange q) (List.nodup_finRange q) x]
              cases x <;> simp [sw]
            rw [hsw_prod]
            have hfold_sign : ∀ (L : List (Fin q)),
                ((Equiv.Perm.sign (L.foldr (fun i τ => Equiv.swap (Sum.inl i) (Sum.inr i) * τ) 1) : ℤ) : ℂ) =
                (-1 : ℂ) ^ L.length := by
              intro L; induction L with
              | nil => simp
              | cons a L ih =>
                simp only [List.foldr_cons, map_mul, List.length_cons, pow_succ, Units.val_mul, Int.cast_mul, ih]
                have hne : (Sum.inl a : Fin q ⊕ Fin q) ≠ Sum.inr a := Sum.inl_ne_inr
                rw [Equiv.Perm.sign_swap hne]
                simp [mul_comm]
            simpa [List.length_finRange] using hfold_sign (List.finRange q)
          rw [hdet_p, hsign]
        rw [hJdet, Fintype.card_fin] at hdJM
        exact mul_left_cancel₀ (pow_ne_zero q (by norm_num : (-1 : ℂ) ≠ 0)) (by rw [hdJM, mul_comm])
      rw [hd, hsw]
    rw [hblock_det, Matrix.det_smul, Fintype.card_fin, Matrix.det_one, mul_one] at hμ
    have hμ1 : μ + 1 = 0 := eq_zero_of_pow_eq_zero (eq_zero_of_pow_eq_zero hμ)
    have hμeq : μ = -1 := eq_neg_of_add_eq_zero_left hμ1
    rw [hμeq]; simp
  exact ⟨hBT, hTB, hT_hurwitz⟩

/-- Step 1 of Theorem 3.4: constant-input realization `P(s)/Q(s) - p₀ = η (I_N - ∑ s_j A_j)⁻¹ 1_N`. -/
private lemma mvme_step1_const_input (n : ℕ) (P Q : MvPolynomial (Fin n) ℝ) (p₀ : ℝ)
    (hQ0 : MvPolynomial.eval 0 Q ≠ 0) (hPQ0 : MvPolynomial.eval 0 P = MvPolynomial.eval 0 Q) :
    ∃ (N : ℕ) (_ : 1 ≤ N) (η : Fin N → ℝ) (A : Fin n → Matrix (Fin N) (Fin N) ℝ)
      (U1 : Set (Fin n → ℝ)), IsOpen U1 ∧ (0 : Fin n → ℝ) ∈ U1 ∧
      (∀ s ∈ U1, MvPolynomial.eval s Q ≠ 0) ∧
      ∀ s ∈ U1,
        IsUnit ((1 : Matrix (Fin N) (Fin N) ℝ) - ∑ j : Fin n, s j • A j).det ∧
        MvPolynomial.eval s P / MvPolynomial.eval s Q - p₀ =
          dotProduct η (((1 : Matrix (Fin N) (Fin N) ℝ) - ∑ j : Fin n, s j • A j)⁻¹.mulVec 1) := by
  obtain ⟨ρ, η0, R, b0, U0, hU0o, hU00, hU0⟩ := hasZeroFM_rat P Q hQ0
  let N := ρ + 1
  let e1 : Fin 1 ⊕ Fin ρ ≃ Fin N := (finSumFinEquiv).trans (finCongr (Nat.add_comm 1 ρ))
  let A1 : Fin n → Matrix (Fin N) (Fin N) ℝ := fun j =>
    (Matrix.fromBlocks (0 : Matrix (Fin 1) (Fin 1) ℝ) 0 (Matrix.of fun i _ => b0 j i) (R j)).submatrix e1.symm e1.symm
  let η1 : Fin N → ℝ := Sum.elim (fun _ => 1 - p₀) η0 ∘ e1.symm
  let b1 : Fin N → ℝ := Sum.elim (fun _ => 1) 0 ∘ e1.symm
  let H : Matrix (Fin N) (Fin N) ℝ :=
    (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 (Matrix.of fun _ _ => (1 : ℝ)) (1 : Matrix (Fin ρ) (Fin ρ) ℝ)).submatrix e1.symm e1.symm
  let Hinv : Matrix (Fin N) (Fin N) ℝ :=
    (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 (Matrix.of fun _ _ => (-1 : ℝ)) (1 : Matrix (Fin ρ) (Fin ρ) ℝ)).submatrix e1.symm e1.symm
  have hHHinv : H * Hinv = 1 := by
    rw [show H * Hinv = _ from submatrix_mul_submatrix e1 _ _, Matrix.fromBlocks_multiply]
    ext p q; obtain ⟨p', rfl⟩ := e1.surjective p; obtain ⟨q', rfl⟩ := e1.surjective q
    cases p' <;> cases q' <;> simp [Matrix.one_apply, e1.symm_apply_apply]
  have hHinvH : Hinv * H = 1 := by
    rw [show Hinv * H = _ from submatrix_mul_submatrix e1 _ _, Matrix.fromBlocks_multiply]
    ext p q; obtain ⟨p', rfl⟩ := e1.surjective p; obtain ⟨q', rfl⟩ := e1.surjective q
    cases p' <;> cases q' <;> simp [Matrix.one_apply, e1.symm_apply_apply]
  have hHb1 : H.mulVec b1 = (1 : Fin N → ℝ) := by
    ext p; obtain ⟨p', rfl⟩ := e1.surjective p
    simp only [Matrix.mulVec, dotProduct, H, b1, Matrix.submatrix_apply, Function.comp_apply, Pi.one_apply]
    rw [← e1.sum_comp]
    cases p' with
    | inl i => simp [Fin.eq_zero i, Fintype.sum_sum_type, e1.symm_apply_apply]
    | inr i => simp [Fintype.sum_sum_type, e1.symm_apply_apply]
  let A : Fin n → Matrix (Fin N) (Fin N) ℝ := fun j => H * A1 j * Hinv
  let η : Fin N → ℝ := Matrix.vecMul η1 Hinv
  let U1 : Set (Fin n → ℝ) := U0 ∩ { s | MvPolynomial.eval s Q ≠ 0 }
  have hU1o : IsOpen U1 := hU0o.inter (isClosed_singleton.isOpen_compl.preimage (MvPolynomial.continuous_eval Q))
  have hU10 : (0 : Fin n → ℝ) ∈ U1 := ⟨hU00, hQ0⟩
  refine ⟨N, Nat.succ_pos ρ, η, A, U1, hU1o, hU10, fun _ hs => hs.2, fun s hs => ?_⟩
  obtain ⟨hu0, hrat⟩ := hU0 s hs.1
  let M0 : Matrix (Fin ρ) (Fin ρ) ℝ := 1 - ∑ j : Fin n, s j • R j
  let v0 : Fin ρ → ℝ := ∑ j : Fin n, s j • b0 j
  let M1 : Matrix (Fin N) (Fin N) ℝ := 1 - ∑ j : Fin n, s j • A1 j
  let M : Matrix (Fin N) (Fin N) ℝ := 1 - ∑ j : Fin n, s j • A j
  have hM1_eq : M1 = (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 (Matrix.of fun i _ => -v0 i) M0).submatrix e1.symm e1.symm := by
    ext p q; obtain ⟨p', rfl⟩ := e1.surjective p; obtain ⟨q', rfl⟩ := e1.surjective q
    cases p' <;> cases q' <;>
      simp [M1, M0, v0, A1, Matrix.sum_apply, Matrix.one_apply, Finset.sum_apply, e1.symm_apply_apply]
  have hdet1 : M1.det = M0.det := by
    rw [hM1_eq, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul]
  have hu1 : IsUnit M1.det := hdet1 ▸ hu0
  have hM_conj : M = H * M1 * Hinv := by
    dsimp only [M, M1, A]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hHHinv, Matrix.mul_sum, Matrix.sum_mul]
    congr 1; refine Finset.sum_congr rfl fun j _ => by simp only [Matrix.mul_smul, Matrix.smul_mul]
  have hdetM : M.det = M1.det := by
    rw [hM_conj, Matrix.det_mul, Matrix.det_mul, mul_comm (H.det * M1.det), ← mul_assoc, ← Matrix.det_mul, hHinvH, Matrix.det_one, one_mul]
  have huM : IsUnit M.det := hdetM ▸ hu1
  have hM1_inv : M1⁻¹ = (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 (Matrix.of fun i _ => M0⁻¹.mulVec v0 i) M0⁻¹).submatrix e1.symm e1.symm := by
    apply Matrix.inv_eq_right_inv
    rw [hM1_eq, submatrix_mul_submatrix, Matrix.fromBlocks_multiply, Matrix.mul_nonsing_inv M0 hu0]
    ext p q; obtain ⟨p', rfl⟩ := e1.surjective p; obtain ⟨q', rfl⟩ := e1.surjective q
    cases p' <;> cases q' <;> simp [Matrix.one_apply, e1.symm_apply_apply]
    · rename_i i j
      have hmv : (M0 * Matrix.of fun (r : Fin ρ) (_ : Fin 1) => M0⁻¹.mulVec v0 r) i j = v0 i := by
        simp only [Matrix.mul_apply, Matrix.of_apply]
        have : ∑ x, M0 i x * M0⁻¹.mulVec v0 x = (M0.mulVec (M0⁻¹.mulVec v0)) i := rfl
        rw [this, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M0 hu0, Matrix.one_mulVec]
      rw [hmv, neg_add_cancel]
  have hM_inv : M⁻¹ = H * M1⁻¹ * Hinv := by
    apply Matrix.inv_eq_right_inv
    rw [hM_conj]
    calc H * M1 * Hinv * (H * M1⁻¹ * Hinv)
        = H * M1 * (Hinv * H) * M1⁻¹ * Hinv := by simp only [Matrix.mul_assoc]
      _ = H * (M1 * M1⁻¹) * Hinv := by rw [hHinvH, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.mul_nonsing_inv M1 hu1, Matrix.mul_one, hHHinv]
  refine ⟨huM, ?_⟩
  rw [show (1 - ∑ j : Fin n, s j • A j)⁻¹ = M⁻¹ from rfl, hM_inv, ← hHb1,
      Matrix.mulVec_mulVec, Matrix.mul_assoc (H * M1⁻¹) Hinv H,
      hHinvH, Matrix.mul_one, ← Matrix.mulVec_mulVec]
  have hdot : dotProduct η (H.mulVec (M1⁻¹.mulVec b1)) = dotProduct η1 (M1⁻¹.mulVec b1) := by
    rw [show η = Matrix.vecMul η1 Hinv from rfl, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hHinvH, Matrix.vecMul_one]
  rw [hdot]
  have hmv1 : M1⁻¹.mulVec b1 = Sum.elim (fun _ => 1) (M0⁻¹.mulVec v0) ∘ e1.symm := by
    rw [hM1_inv]
    ext p; obtain ⟨p', rfl⟩ := e1.surjective p
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, b1, Function.comp_apply]
    rw [← e1.sum_comp]
    cases p' with
    | inl i => simp [Fin.eq_zero i, Fintype.sum_sum_type, e1.symm_apply_apply, Matrix.one_apply]
    | inr i => simp [Fintype.sum_sum_type, e1.symm_apply_apply, Matrix.mulVec, dotProduct]
  rw [hmv1]
  have hdot1 : dotProduct η1 (Sum.elim (fun _ => 1) (M0⁻¹.mulVec v0) ∘ e1.symm) =
      (1 - p₀) + dotProduct η0 (M0⁻¹.mulVec v0) := by
    simp only [dotProduct, η1, Function.comp_apply]
    rw [← e1.sum_comp]; simp [Fintype.sum_sum_type, e1.symm_apply_apply]
  rw [hdot1, ← hrat, hPQ0, div_self hQ0]
  ring

/-- Theorem 3.4 (`thm-mvme`): `MVME_n ⊆ MME*_n` with normalized `K ≥ 0`, `t = -T 1`, `0 ≤ α 1 ≤ 1`. -/
private lemma mvme_subset_mme (n : ℕ) (hn : 2 ≤ n) (P Q : MvPolynomial (Fin n) ℝ) (p₀ : ℝ)
    (hQ0 : MvPolynomial.eval 0 Q ≠ 0) (hPQ0 : MvPolynomial.eval 0 P = MvPolynomial.eval 0 Q)
    (hp₀_0 : 0 ≤ p₀) (hp₀_1 : p₀ ≤ 1) :
    ∃ (m : ℕ) (_ : 1 ≤ m) (α : Fin m → ℝ) (T : Matrix (Fin m) (Fin m) ℝ)
      (K : Matrix (Fin m) (Fin n) ℝ),
      IsHurwitzStable T ∧
      (∀ i j, 0 ≤ K i j) ∧
      p₀ = 1 - ∑ i, α i ∧
      0 ≤ ∑ i, α i ∧ ∑ i, α i ≤ 1 ∧
      ∃ U : Set (Fin n → ℝ), IsOpen U ∧ (0 : Fin n → ℝ) ∈ U ∧
        ∀ s ∈ U,
          MvPolynomial.eval s Q ≠ 0 ∧
          IsUnit (-T + Matrix.diagonal (K.mulVec s)).det ∧
          MvPolynomial.eval s P / MvPolynomial.eval s Q =
            kulkarniEval p₀ α T K (-(T.mulVec 1)) s := by
  obtain ⟨N, hN_pos, η, A, U1, hU1o, hU10, hU1Q, hL_real⟩ := mvme_step1_const_input n P Q p₀ hQ0 hPQ0
  -- Step 2: Diagonalization (Lemma 3.3): `q = n * N`, `S(s) = diag(s_j I_N)`, `U` with all block rows `[A_1, ..., A_n]`.
  let q := n * N
  let eq_idx : Fin n × Fin N ≃ Fin q := finProdFinEquiv
  let Umat : Matrix (Fin q) (Fin q) ℝ := Matrix.of fun p r =>
    let (_, i) := eq_idx.symm p
    let (j, k) := eq_idx.symm r
    A j i k
  let Smat : (Fin n → ℝ) → Matrix (Fin q) (Fin q) ℝ := fun s =>
    Matrix.diagonal fun p => s (eq_idx.symm p).1
  let α₀ : Fin q → ℝ := fun p => if (eq_idx.symm p).1 = ⟨0, by omega⟩ then η (eq_idx.symm p).2 else 0
  let Emat : Matrix (Fin q) (Fin N) ℝ := Matrix.of fun p k => if (eq_idx.symm p).2 = k then 1 else 0
  -- Verify Lemma 3.3 intertwining and determinant identity on `U1`:
  have hUS_E : ∀ s : Fin n → ℝ, (1 - Umat * Smat s) * Emat = Emat * (1 - ∑ j : Fin n, s j • A j) := by
    intro s
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
    ext p k
    obtain ⟨⟨j0, i0⟩, rfl⟩ := eq_idx.surjective p
    simp only [Matrix.sub_apply, Matrix.mul_apply, Umat, Smat, Emat, Matrix.of_apply,
      Matrix.diagonal_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    have hL : ∑ p1 : Fin q,
        (∑ p2 : Fin q, A (eq_idx.symm p2).1 i0 (eq_idx.symm p2).2 *
          (if p2 = p1 then s (eq_idx.symm p2).1 else 0)) * (if (eq_idx.symm p1).2 = k then 1 else 0) =
        ∑ j : Fin n, A j i0 k * s j := by
      rw [← eq_idx.sum_comp]
      simp only [Fintype.sum_prod_type, Equiv.symm_apply_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_eq_single k]
      · simp only [↓reduceIte, mul_one]
        rw [Finset.sum_eq_single (eq_idx (j, k))]
        · simp [eq_idx.symm_apply_apply]
        · intro p2 _ hp2; simp [hp2]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro r _ hrk; simp [hrk]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hR : ∑ x : Fin N, (if i0 = x then 1 else 0) * ∑ j : Fin n, s j * A j x k =
        ∑ j : Fin n, s j * A j i0 k := by
      rw [Finset.sum_eq_single i0]
      · simp
      · intro x _ hxi; simp [Ne.symm hxi]
      · intro h; exact absurd (Finset.mem_univ _) h
    simp only [eq_idx.symm_apply_apply]
    rw [hL, hR]
    congr 1; refine Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hdet_US : ∀ s : Fin n → ℝ, (1 - Umat * Smat s).det = (1 - ∑ j : Fin n, s j • A j).det := by
    intro s
    -- Factor `Umat * Smat s = Emat * Dmat` where `Dmat (i, p) = s j * A j i k` (for `p = (j, k)`),
    -- then apply Sylvester's identity `det (1 - E * D) = det (1 - D * E)`!
    let Dmat : Matrix (Fin N) (Fin q) ℝ := Matrix.of fun i r =>
      let (j, k) := eq_idx.symm r
      s j * A j i k
    have hED : Emat * Dmat = Umat * Smat s := by
      ext p r
      obtain ⟨⟨j0, i0⟩, rfl⟩ := eq_idx.surjective p
      obtain ⟨⟨j1, k1⟩, rfl⟩ := eq_idx.surjective r
      simp only [Matrix.mul_apply, Emat, Dmat, Umat, Smat, Matrix.of_apply, Matrix.diagonal_apply,
        eq_idx.symm_apply_apply]
      rw [Finset.sum_eq_single i0]
      · rw [Finset.sum_eq_single (eq_idx (j1, k1))]
        · simp [eq_idx.symm_apply_apply, mul_comm]
        · intro x _ hx; simp [hx]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro x _ hxi; simp [Ne.symm hxi]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hDE : Dmat * Emat = ∑ j : Fin n, s j • A j := by
      ext i k
      simp only [Matrix.mul_apply, Dmat, Emat, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
      rw [← eq_idx.sum_comp]
      simp only [Fintype.sum_prod_type, eq_idx.symm_apply_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_eq_single k]
      · simp
      · intro r _ hrk; simp [hrk]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [← hED, ← hDE]
    -- Sylvester's determinant identity: `det (1 - E * D) = det (1 - D * E)` via `fromBlocks`!
    have h1 : (Matrix.fromBlocks (1 : Matrix (Fin q) (Fin q) ℝ) Emat Dmat (1 : Matrix (Fin N) (Fin N) ℝ) *
        Matrix.fromBlocks (1 : Matrix (Fin q) (Fin q) ℝ) 0 (-Dmat) (1 : Matrix (Fin N) (Fin N) ℝ)) =
        Matrix.fromBlocks (1 - Emat * Dmat) Emat 0 1 := by
      rw [Matrix.fromBlocks_multiply]; congr 1 <;> simp [sub_eq_add_neg]
    have h2 : (Matrix.fromBlocks (1 : Matrix (Fin q) (Fin q) ℝ) (-Emat) 0 (1 : Matrix (Fin N) (Fin N) ℝ) *
        Matrix.fromBlocks (1 : Matrix (Fin q) (Fin q) ℝ) Emat Dmat (1 : Matrix (Fin N) (Fin N) ℝ)) =
        Matrix.fromBlocks (1 - Emat * Dmat) 0 Dmat 1 := by
      rw [Matrix.fromBlocks_multiply]; congr 1 <;> simp [sub_eq_add_neg]
    have h3 : (Matrix.fromBlocks (1 : Matrix (Fin q) (Fin q) ℝ) Emat Dmat (1 : Matrix (Fin N) (Fin N) ℝ) *
        Matrix.fromBlocks (1 : Matrix (Fin q) (Fin q) ℝ) (-Emat) 0 (1 : Matrix (Fin N) (Fin N) ℝ)) =
        Matrix.fromBlocks 1 0 Dmat (1 - Dmat * Emat) := by
      rw [Matrix.fromBlocks_multiply]; congr 1 <;> simp [sub_eq_add_neg, add_comm]
    have hd1 := congrArg Matrix.det h1
    have hd3 := congrArg Matrix.det h3
    rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₂₁,
        Matrix.det_one, Matrix.det_one, mul_one, mul_one, mul_one] at hd1
    rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂,
        Matrix.det_one, Matrix.det_one, mul_one, one_mul, mul_one] at hd3
    exact hd1.symm.trans hd3
  -- Step 3: Hurwitz-stable augmentation (Lemma 3.4): `ℓ = 2 * q`, `T = B⁻¹`, `K ≥ 0`.
  let ℓ := q + q
  have hℓ_pos : 1 ≤ ℓ := by dsimp [ℓ, q]; nlinarith
  let e2 : Fin q ⊕ Fin q ≃ Fin ℓ := finSumFinEquiv
  let Bmat : Matrix (Fin ℓ) (Fin ℓ) ℝ :=
    (Matrix.fromBlocks Umat (-1) ((Umat + 1) ^ 2) (-Umat - 2)).submatrix e2.symm e2.symm
  let Tmat : Matrix (Fin ℓ) (Fin ℓ) ℝ :=
    (Matrix.fromBlocks (-Umat - 2) 1 (-((Umat + 1) ^ 2)) Umat).submatrix e2.symm e2.symm
  obtain ⟨hBT, hTB, hT_hurwitz⟩ := hurwitz_aug_props Umat
  let αhat : Fin ℓ → ℝ := Sum.elim α₀ 0 ∘ e2.symm
  let Kmat : Matrix (Fin ℓ) (Fin n) ℝ := Matrix.of fun p j =>
    match e2.symm p with
    | Sum.inl r => if (eq_idx.symm r).1 = j then 1 else 0
    | Sum.inr _ => 0
  have hK_nonneg : ∀ p j, 0 ≤ Kmat p j := fun p j => by
    dsimp only [Kmat, Matrix.of_apply]
    cases e2.symm p with
    | inl r => dsimp only; split_ifs <;> norm_num
    | inr _ => exact le_refl 0
  have hK_diag : ∀ s : Fin n → ℝ, Matrix.diagonal (Kmat.mulVec s) =
      (Matrix.fromBlocks (Smat s) 0 0 0).submatrix e2.symm e2.symm := by
    intro s
    ext p r
    obtain ⟨p', rfl⟩ := e2.surjective p; obtain ⟨r', rfl⟩ := e2.surjective r
    cases p' <;> cases r' <;> simp [Matrix.diagonal_apply, Kmat, Smat, Matrix.mulVec, dotProduct, e2.symm_apply_apply]
  -- Verify Kulkarni formula on `U1`:
  have hKulk : ∀ s ∈ U1,
      IsUnit (-Tmat + Matrix.diagonal (Kmat.mulVec s)).det ∧
      MvPolynomial.eval s P / MvPolynomial.eval s Q =
        kulkarniEval p₀ αhat Tmat Kmat (-(Tmat.mulVec 1)) s := by
    intro s hs
    obtain ⟨huM, hL⟩ := hL_real s hs
    have huUS : IsUnit (1 - Umat * Smat s).det := (hdet_US s).symm ▸ huM
    let Daug := Matrix.diagonal (Kmat.mulVec s)
    have hfactor : -Tmat + Daug = -Tmat * (1 - Bmat * Daug) := by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.neg_mul, sub_neg_eq_add, ← Matrix.mul_assoc, hTB, Matrix.one_mul]
    have hIBD : 1 - Bmat * Daug =
        (Matrix.fromBlocks (1 - Umat * Smat s) 0 (-((Umat + 1) ^ 2 * Smat s)) 1).submatrix e2.symm e2.symm := by
      dsimp only [Daug]
      rw [hK_diag s, show Bmat * (Matrix.fromBlocks (Smat s) 0 0 0).submatrix e2.symm e2.symm = _ from submatrix_mul_submatrix e2 _ _, Matrix.fromBlocks_multiply]
      ext p r; obtain ⟨p', rfl⟩ := e2.surjective p; obtain ⟨r', rfl⟩ := e2.surjective r
      cases p' <;> cases r' <;> simp [Matrix.one_apply, e2.symm_apply_apply]
    have hdet_IBD : (1 - Bmat * Daug).det = (1 - Umat * Smat s).det := by
      rw [hIBD, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]
    have huT : IsUnit (-Tmat).det := isUnit_iff_ne_zero.mpr (hurwitz_neg_det_ne_zero hT_hurwitz)
    have hu_full : IsUnit (-Tmat + Daug).det := by
      rw [hfactor, Matrix.det_mul, hdet_IBD]; exact huT.mul huUS
    refine ⟨hu_full, ?_⟩
    have hIBD_inv : (1 - Bmat * Daug)⁻¹ =
        (Matrix.fromBlocks (1 - Umat * Smat s)⁻¹ 0 ((Umat + 1) ^ 2 * Smat s * (1 - Umat * Smat s)⁻¹) 1).submatrix e2.symm e2.symm := by
      apply Matrix.inv_eq_right_inv
      rw [hIBD, submatrix_mul_submatrix, Matrix.fromBlocks_multiply, Matrix.mul_nonsing_inv _ huUS]
      ext p r; obtain ⟨p', rfl⟩ := e2.surjective p; obtain ⟨r', rfl⟩ := e2.surjective r
      cases p' <;> cases r' <;> simp [Matrix.one_apply, e2.symm_apply_apply]
    have hfull_inv : (-Tmat + Daug)⁻¹ * (-Tmat) = (1 - Bmat * Daug)⁻¹ := by
      have huIBD : IsUnit (1 - Bmat * Daug).det := hdet_IBD.symm ▸ huUS
      calc (-Tmat + Daug)⁻¹ * (-Tmat)
          = (-Tmat + Daug)⁻¹ * (-Tmat) * ((1 - Bmat * Daug) * (1 - Bmat * Daug)⁻¹) := by
            rw [Matrix.mul_nonsing_inv _ huIBD, Matrix.mul_one]
        _ = (-Tmat + Daug)⁻¹ * (-Tmat * (1 - Bmat * Daug)) * (1 - Bmat * Daug)⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = (-Tmat + Daug)⁻¹ * (-Tmat + Daug) * (1 - Bmat * Daug)⁻¹ := by rw [← hfactor]
        _ = (1 - Bmat * Daug)⁻¹ := by rw [Matrix.nonsing_inv_mul _ hu_full, Matrix.one_mul]
    dsimp only [kulkarniEval]
    have hmv_eq : (-Tmat + Daug)⁻¹.mulVec (-(Tmat.mulVec 1)) = (1 - Bmat * Daug)⁻¹.mulVec 1 := by
      have : -(Tmat.mulVec 1) = (-Tmat).mulVec 1 := by simp [Matrix.neg_mulVec]
      rw [this, Matrix.mulVec_mulVec, hfull_inv]
    rw [hmv_eq, hIBD_inv]
    have hstep1 : dotProduct αhat (((Matrix.fromBlocks (1 - Umat * Smat s)⁻¹ 0 ((Umat + 1) ^ 2 * Smat s * (1 - Umat * Smat s)⁻¹) 1).submatrix e2.symm e2.symm).mulVec 1) =
        dotProduct α₀ ((1 - Umat * Smat s)⁻¹.mulVec 1) := by
      simp only [dotProduct, αhat, Matrix.mulVec, Matrix.submatrix_apply, Function.comp_apply, Pi.one_apply, mul_one]
      rw [← e2.sum_comp]
      simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zero_mul,
        Finset.sum_const_zero, add_zero, e2.symm_apply_apply]
      refine Finset.sum_congr rfl fun r _ => ?_
      congr 1; rw [← e2.sum_comp]; simp [Fintype.sum_sum_type, e2.symm_apply_apply]
    rw [hstep1]
    -- Now use intertwining `(1 - U S)⁻¹ E = E (1 - ∑ s_j A_j)⁻¹`, `E 1_N = 1_q`, `α₀ᵀ E = ηᵀ`!
    have hkey : (1 - Umat * Smat s)⁻¹ * Emat = Emat * (1 - ∑ j : Fin n, s j • A j)⁻¹ := by
      calc (1 - Umat * Smat s)⁻¹ * Emat
          = (1 - Umat * Smat s)⁻¹ * Emat * ((1 - ∑ j : Fin n, s j • A j) * (1 - ∑ j : Fin n, s j • A j)⁻¹) := by
            rw [Matrix.mul_nonsing_inv _ huM, Matrix.mul_one]
        _ = (1 - Umat * Smat s)⁻¹ * (Emat * (1 - ∑ j : Fin n, s j • A j)) * (1 - ∑ j : Fin n, s j • A j)⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = (1 - Umat * Smat s)⁻¹ * ((1 - Umat * Smat s) * Emat) * (1 - ∑ j : Fin n, s j • A j)⁻¹ := by
            rw [← hUS_E s]
        _ = Emat * (1 - ∑ j : Fin n, s j • A j)⁻¹ := by
            rw [← Matrix.mul_assoc (1 - Umat * Smat s)⁻¹, Matrix.nonsing_inv_mul _ huUS, Matrix.one_mul]
    have hE1 : Emat.mulVec (1 : Fin N → ℝ) = (1 : Fin q → ℝ) := by
      ext p; simp only [Matrix.mulVec, dotProduct, Emat, Matrix.of_apply, Pi.one_apply, mul_one]
      rw [Finset.sum_eq_single (eq_idx.symm p).2]
      · simp
      · intro k _ hk; simp [Ne.symm hk]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hαE : Matrix.vecMul α₀ Emat = η := by
      ext k; simp only [Matrix.vecMul, dotProduct, α₀, Emat, Matrix.of_apply]
      rw [← eq_idx.sum_comp]; simp only [Fintype.sum_prod_type, eq_idx.symm_apply_apply]
      rw [Finset.sum_eq_single ⟨0, by omega⟩]
      · simp only [↓reduceIte]
        rw [Finset.sum_eq_single k]
        · simp
        · intro r _ hrk; simp [hrk]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro j _ hj; simp [hj]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [← hE1, Matrix.mulVec_mulVec, hkey, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hαE, ← hL]
    ring
  -- Check `p₀ = 1 - ∑ αhat` by evaluating at `s = 0`!
  have hp₀_eq : p₀ = 1 - ∑ i, αhat i := by
    have h0 := (hKulk 0 hU10).2
    rw [hPQ0, div_self hQ0] at h0
    dsimp only [kulkarniEval] at h0
    have hdiag0 : Matrix.diagonal (Kmat.mulVec 0) = 0 := by simp
    have huT : IsUnit (-Tmat).det := isUnit_iff_ne_zero.mpr (hurwitz_neg_det_ne_zero hT_hurwitz)
    have hmv0 : (-Tmat)⁻¹.mulVec (-(Tmat.mulVec 1)) = 1 := by
      rw [show -(Tmat.mulVec 1) = (-Tmat).mulVec 1 by simp [Matrix.neg_mulVec],
          Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ huT, Matrix.one_mulVec]
    rw [hdiag0, add_zero, hmv0] at h0
    have hdot1 : dotProduct αhat 1 = ∑ i, αhat i := by simp [dotProduct]
    rw [hdot1] at h0
    linarith
  refine ⟨ℓ, hℓ_pos, αhat, Tmat, Kmat, hT_hurwitz, hK_nonneg, hp₀_eq, by linarith, by linarith,
    U1, hU1o, hU10, fun s hs => ⟨hU1Q s hs, (hKulk s hs).1, (hKulk s hs).2⟩⟩

/-- Remark 2.4 (`MME*_n ⊆ MVME_n`): Every Kulkarni resolvent defines a rational function analytic at `0`. -/
private lemma mme_subset_mvme (n m : ℕ) (p₀ : ℝ) (α : Fin m → ℝ)
    (T : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin m) (Fin n) ℝ) (t : Fin m → ℝ)
    (hT : IsHurwitzStable T) :
    ∃ P Q : MvPolynomial (Fin n) ℝ,
      MvPolynomial.eval 0 Q ≠ 0 ∧
      ∀ s : Fin n → ℝ, IsUnit (-T + Matrix.diagonal (K.mulVec s)).det →
        MvPolynomial.eval s Q ≠ 0 ∧
        kulkarniEval p₀ α T K t s = MvPolynomial.eval s P / MvPolynomial.eval s Q := by
  let Mpoly : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ) :=
    (-T).map MvPolynomial.C + Matrix.diagonal fun i => ∑ j : Fin n, MvPolynomial.C (K i j) * MvPolynomial.X j
  let Q : MvPolynomial (Fin n) ℝ := Mpoly.det
  let P : MvPolynomial (Fin n) ℝ :=
    MvPolynomial.C p₀ * Q + ∑ i : Fin m, ∑ k : Fin m, MvPolynomial.C (α i) * Mpoly.adjugate i k * MvPolynomial.C (t k)
  have hM_eval : ∀ s : Fin n → ℝ, Mpoly.map (MvPolynomial.eval s) = -T + Matrix.diagonal (K.mulVec s) := fun s => by
    ext i k
    simp only [Mpoly, Matrix.map_apply, Matrix.add_apply, Matrix.neg_apply, Matrix.diagonal_apply,
      map_add, MvPolynomial.eval_C, Matrix.mulVec, dotProduct]
    split_ifs <;> simp
  have hQ_eval : ∀ s : Fin n → ℝ, MvPolynomial.eval s Q = (-T + Matrix.diagonal (K.mulVec s)).det := fun s => by
    simpa [Q, RingHom.mapMatrix_apply, hM_eval s] using RingHom.map_det (MvPolynomial.eval s) Mpoly
  refine ⟨P, Q, ?_, fun s hu => ?_⟩
  · rw [hQ_eval 0]; simp [hurwitz_neg_det_ne_zero hT]
  · have hQs : MvPolynomial.eval s Q ≠ 0 := (hQ_eval s).symm ▸ hu.ne_zero
    refine ⟨hQs, ?_⟩
    have hadj : Mpoly.adjugate.map (MvPolynomial.eval s) = (-T + Matrix.diagonal (K.mulVec s)).adjugate := by
      simpa [RingHom.mapMatrix_apply, hM_eval s] using RingHom.map_adjugate (MvPolynomial.eval s) Mpoly
    have hP_eval : MvPolynomial.eval s P =
        p₀ * (-T + Matrix.diagonal (K.mulVec s)).det +
        dotProduct α ((-T + Matrix.diagonal (K.mulVec s)).adjugate.mulVec t) := by
      simp only [P, map_add, map_mul, map_sum, MvPolynomial.eval_C, hQ_eval s, dotProduct, Matrix.mulVec,
        Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      have hik : MvPolynomial.eval s (Mpoly.adjugate i k) = (-T + Matrix.diagonal (K.mulVec s)).adjugate i k :=
        congrArg (fun X => X i k) hadj
      rw [hik]; ring
    rw [hP_eval, hQ_eval s]
    dsimp only [kulkarniEval]
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    have hdne : (-T + Matrix.diagonal (K.mulVec s)).det ≠ 0 := hu.ne_zero
    field_simp [hdne]

/-! ### Section 3: Diagonal-Shift Determinant Expansion and `MPH*_n` Factorization (Theorem 4.2) -/

/-- Determinant of `A + diag(d_i | i ∈ S)` expands over subsets `J ⊆ S` as
`∑ J ⊆ S, det(A_{J^c, J^c}) * ∏ i ∈ J, d i`. -/
private lemma det_add_diagOn_aux {R : Type*} [CommRing R] :
    ∀ (k : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
      (A : Matrix ι ι R) (d : ι → R) (S : Finset ι), S.card = k →
    (A + Matrix.diagonal fun i => if i ∈ S then d i else 0).det =
      ∑ J ∈ S.powerset,
        (A.submatrix (Subtype.val : { i : ι // i ∉ J } → ι) Subtype.val).det * ∏ i ∈ J, d i := by
  intro k
  induction k with
  | zero =>
    intro ι _ _ A d S hk
    rw [Finset.card_eq_zero.mp hk]
    simp only [Finset.notMem_empty, ↓reduceIte, Matrix.diagonal_zero, add_zero,
      Finset.powerset_empty, Finset.sum_singleton, Finset.prod_empty, mul_one]
    let e : { i : ι // i ∉ (∅ : Finset ι) } ≃ ι := Equiv.subtypeUnivEquiv (fun _ => Finset.notMem_empty _)
    exact (Matrix.det_submatrix_equiv_self e A).symm
  | succ k ih =>
    intro ι _ _ A d S hk
    obtain ⟨a, S', ha, rfl, hcard'⟩ := Finset.card_eq_succ.mp hk
    -- Split `det (B + diag (Pi.single a (d a))) = det B + d a * det (B_{a^c, a^c})`.
    let B : Matrix ι ι R := A + Matrix.diagonal fun i => if i ∈ S' then d i else 0
    have hsplit_mat : A + Matrix.diagonal (fun i => if i ∈ insert a S' then d i else 0) =
        B.updateRow a (B a + d a • Pi.single a 1) := by
      ext i j
      by_cases hi : i = a
      · subst hi
        simp only [B, Matrix.updateRow_self, Matrix.add_apply, Matrix.diagonal_apply, Pi.add_apply,
          Pi.smul_apply, Pi.single_apply, smul_eq_mul, Finset.mem_insert_self, ↓reduceIte, ha]
        by_cases hj : i = j
        · subst hj; simp
        · simp [hj, Ne.symm hj]
      · simp only [B, Matrix.updateRow_ne hi, Matrix.add_apply, Matrix.diagonal_apply,
          Finset.mem_insert, hi, false_or]
    have hdet_row : (B.updateRow a (B a + d a • Pi.single a 1)).det =
        B.det + d a * (B.submatrix (Subtype.val : { i : ι // i ≠ a } → ι) Subtype.val).det := by
      rw [Matrix.det_updateRow_add, Matrix.updateRow_eq_self, Matrix.det_updateRow_smul]
      congr 1; congr 1
      let ea : Unit ⊕ { i : ι // i ≠ a } ≃ ι :=
        { toFun := Sum.elim (fun _ => a) Subtype.val
          invFun := fun i => if h : i = a then Sum.inl () else Sum.inr ⟨i, h⟩
          left_inv := fun x => by cases x with | inl u => simp | inr y => simp [y.prop]
          right_inv := fun i => by dsimp only; split_ifs with h; exact h.symm; rfl }
      rw [← Matrix.det_submatrix_equiv_self ea]
      have hblk : (B.updateRow a (Pi.single a 1)).submatrix ea ea =
          Matrix.fromBlocks (1 : Matrix Unit Unit R) 0
            (Matrix.of fun i _ => B i.val a)
            (B.submatrix (Subtype.val : { i : ι // i ≠ a } → ι) Subtype.val) := by
        ext x y
        cases x with
        | inl _ =>
          cases y with
          | inl _ => simp [ea]
          | inr y => simp [ea, y.prop]
        | inr x =>
          cases y with
          | inl _ => simp [ea, Matrix.updateRow_ne x.prop]
          | inr y => simp [ea, Matrix.updateRow_ne x.prop]
      rw [hblk, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul]
    rw [hsplit_mat, hdet_row]
    have hB_det : B.det = ∑ J ∈ S'.powerset,
        (A.submatrix (Subtype.val : { i : ι // i ∉ J } → ι) Subtype.val).det * ∏ i ∈ J, d i :=
      ih A d S' hcard'
    let S'sub : Finset { i : ι // i ≠ a } := S'.subtype (· ≠ a)
    have hS'sub_card : S'sub.card = k := by
      rw [← hcard']
      exact Finset.card_bij (fun x _ => x.val) (fun x hx => Finset.mem_subtype.mp hx)
        (fun _ _ _ _ h => Subtype.ext h)
        (fun x hx => ⟨⟨x, fun h => ha (h ▸ hx)⟩, Finset.mem_subtype.mpr hx, rfl⟩)
    have hBsub_eq : B.submatrix (Subtype.val : { i : ι // i ≠ a } → ι) Subtype.val =
        A.submatrix Subtype.val Subtype.val +
        Matrix.diagonal (fun i : { i : ι // i ≠ a } => if i ∈ S'sub then d i.val else 0) := by
      ext i j
      simp only [B, Matrix.submatrix_apply, Matrix.add_apply, Matrix.diagonal_apply, S'sub, Finset.mem_subtype]
      by_cases hij : i = j
      · subst hij; simp
      · have hij' : i.val ≠ j.val := fun h => hij (Subtype.ext h)
        simp [hij, hij']
    have hBsub_det := ih (A.submatrix (Subtype.val : { i : ι // i ≠ a } → ι) Subtype.val) (fun i => d i.val) S'sub hS'sub_card
    rw [← hBsub_eq] at hBsub_det
    rw [hB_det, hBsub_det, Finset.mul_sum, Finset.powerset_insert, Finset.sum_union]
    · congr 1
      rw [Finset.sum_image (fun J₁ hJ₁ J₂ hJ₂ heq => by
        have ha1 : a ∉ J₁ := fun h => ha (Finset.mem_powerset.mp hJ₁ h)
        have ha2 : a ∉ J₂ := fun h => ha (Finset.mem_powerset.mp hJ₂ h)
        ext x; by_cases hxa : x = a
        · subst hxa; simp [ha1, ha2]
        · have := congrArg (x ∈ ·) heq; simp [hxa] at this; exact this)]
      refine Finset.sum_bij (fun J _ => J.map ⟨Subtype.val, Subtype.val_injective⟩) ?_ ?_ ?_ ?_
      · intro J hJ
        rw [Finset.mem_powerset] at hJ ⊢
        intro x hx; obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
        exact (Finset.mem_subtype.mp (hJ hy))
      · intro J₁ _ J₂ _ h
        ext x; have := congrArg (x.val ∈ ·) h; simpa using this
      · intro J hJ
        have hsub : J ⊆ S' := Finset.mem_powerset.mp hJ
        refine ⟨J.subtype (· ≠ a), Finset.mem_powerset.mpr (fun x hx => Finset.mem_subtype.mpr (hsub (Finset.mem_subtype.mp hx))), ?_⟩
        ext x; simp only [Finset.mem_map, Finset.mem_subtype, Function.Embedding.coeFn_mk]
        constructor
        · rintro ⟨y, hy, rfl⟩; exact hy
        · intro hx; exact ⟨⟨x, fun h => ha (h ▸ hsub hx)⟩, hx, rfl⟩
      · intro J hJ
        have hJmap_a : a ∉ J.map ⟨Subtype.val, Subtype.val_injective⟩ := by
          simp only [Finset.mem_map, Function.Embedding.coeFn_mk, not_exists, not_and]
          intro y _; exact y.prop
        rw [Finset.prod_insert hJmap_a, Finset.prod_map]
        have hdet_congr :
            ((A.submatrix (Subtype.val : { i : ι // i ≠ a } → ι) Subtype.val).submatrix
              (Subtype.val : { x : { i : ι // i ≠ a } // x ∉ J } → { i : ι // i ≠ a }) Subtype.val).det =
            (A.submatrix (Subtype.val : { i : ι // i ∉ insert a (J.map ⟨Subtype.val, Subtype.val_injective⟩) } → ι) Subtype.val).det := by
          let eJ : { x : { i : ι // i ≠ a } // x ∉ J } ≃
              { i : ι // i ∉ insert a (J.map ⟨Subtype.val, Subtype.val_injective⟩) } :=
            { toFun := fun x => ⟨x.val.val, by
                simp only [Finset.mem_insert, Finset.mem_map, Function.Embedding.coeFn_mk, not_or, not_exists, not_and]
                exact ⟨x.val.prop, fun y hy hEq => x.prop (Subtype.ext hEq ▸ hy)⟩⟩
              invFun := fun i => ⟨⟨i.val, fun h => i.prop (Finset.mem_insert.mpr (Or.inl h))⟩, fun h =>
                i.prop (Finset.mem_insert.mpr (Or.inr (Finset.mem_map.mpr ⟨_, h, rfl⟩)))⟩
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl }
          rw [← Matrix.det_submatrix_equiv_self eJ]
          rfl
        simp only [Function.Embedding.coeFn_mk]
        rw [hdet_congr]; ring
    · rw [Finset.disjoint_left]
      intro J hJ1 hJ2
      obtain ⟨J', _, rfl⟩ := Finset.mem_image.mp hJ2
      exact ha (Finset.mem_powerset.mp hJ1 (Finset.mem_insert_self a J'))

private lemma det_add_diagonal_expansion {m : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin m) (Fin m) R) (d : Fin m → R) :
    (A + Matrix.diagonal d).det =
      ∑ J : Finset (Fin m),
        (A.submatrix (Subtype.val : { i : Fin m // i ∉ J } → Fin m) Subtype.val).det * ∏ i ∈ J, d i := by
  have h := det_add_diagOn_aux (Finset.univ : Finset (Fin m)).card A d Finset.univ rfl
  simp only [Finset.mem_univ, ↓reduceIte, Finset.powerset_univ] at h
  exact h

private lemma leadingHomog_ne_zero {n : ℕ} {F : MvPolynomial (Fin n) ℝ} (hF : F ≠ 0) :
    leadingHomog F ≠ 0 := by
  have hex : ∃ d ∈ F.support, Finsupp.degree d = F.totalDegree := by
    have hne : F.support.Nonempty := MvPolynomial.support_nonempty.mpr hF
    obtain ⟨d, hd, hmax⟩ := Finset.exists_max_image F.support (fun d => d.sum fun _ k => k) hne
    refine ⟨d, hd, le_antisymm (MvPolynomial.le_totalDegree hd) ?_⟩
    exact Finset.sup_le fun d' hd' => hmax d' hd'
  obtain ⟨d, hd, hdeg⟩ := hex
  intro h0
  have hcoeff := congrArg (MvPolynomial.coeff d) h0
  rw [leadingHomog, MvPolynomial.coeff_homogeneousComponent, if_pos hdeg, MvPolynomial.coeff_zero] at hcoeff
  exact (MvPolynomial.mem_support_iff.mp hd) hcoeff

private lemma homogeneousComponent_mul_top {n : ℕ} (F G : MvPolynomial (Fin n) ℝ) :
    (F * G).homogeneousComponent (F.totalDegree + G.totalDegree) = leadingHomog F * leadingHomog G := by
  ext d
  rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_mul, MvPolynomial.coeff_mul]
  by_cases hdeg : Finsupp.degree d = F.totalDegree + G.totalDegree
  · rw [if_pos hdeg]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hadd : x.1 + x.2 = d := by simpa using hx
    have hdeg_add : Finsupp.degree x.1 + Finsupp.degree x.2 = F.totalDegree + G.totalDegree := by
      rw [← hdeg, ← hadd, map_add]
    rw [leadingHomog, leadingHomog, MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_homogeneousComponent]
    by_cases h1 : MvPolynomial.coeff x.1 F = 0
    · simp [h1]
    · by_cases h2 : MvPolynomial.coeff x.2 G = 0
      · simp [h2]
      · have hle1 : Finsupp.degree x.1 ≤ F.totalDegree := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr h1)
        have hle2 : Finsupp.degree x.2 ≤ G.totalDegree := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr h2)
        have heq1 : Finsupp.degree x.1 = F.totalDegree := by omega
        have heq2 : Finsupp.degree x.2 = G.totalDegree := by omega
        simp [heq1, heq2]
  · rw [if_neg hdeg]
    symm
    refine Finset.sum_eq_zero fun x hx => ?_
    have hadd : x.1 + x.2 = d := by simpa using hx
    rw [leadingHomog, leadingHomog, MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_homogeneousComponent]
    split_ifs with h1 h2
    · exfalso; apply hdeg
      rw [← hadd, map_add, h1, h2]
    · simp
    · simp
    · simp

private lemma leadingHomog_mul {n : ℕ} {F G : MvPolynomial (Fin n) ℝ} (hF : F ≠ 0) (hG : G ≠ 0) :
    leadingHomog (F * G) = leadingHomog F * leadingHomog G := by
  have hdeg_le : (F * G).totalDegree ≤ F.totalDegree + G.totalDegree := MvPolynomial.totalDegree_mul F G
  have hprod_ne : leadingHomog F * leadingHomog G ≠ 0 := mul_ne_zero (leadingHomog_ne_zero hF) (leadingHomog_ne_zero hG)
  have hcomp_eq : (F * G).homogeneousComponent (F.totalDegree + G.totalDegree) = leadingHomog F * leadingHomog G :=
    homogeneousComponent_mul_top F G
  have hdeg_ge : F.totalDegree + G.totalDegree ≤ (F * G).totalDegree := by
    by_contra hlt
    have h0 := MvPolynomial.homogeneousComponent_eq_zero (F.totalDegree + G.totalDegree) (F * G) (not_le.mp hlt)
    rw [hcomp_eq] at h0; exact hprod_ne h0
  have hdeg : (F * G).totalDegree = F.totalDegree + G.totalDegree := le_antisymm hdeg_le hdeg_ge
  rw [leadingHomog, hdeg, hcomp_eq]

private lemma totalDegree_mul_eq {n : ℕ} {F G : MvPolynomial (Fin n) ℝ} (hF : F ≠ 0) (hG : G ≠ 0) :
    (F * G).totalDegree = F.totalDegree + G.totalDegree := by
  have hle := MvPolynomial.totalDegree_mul F G
  have hprod_ne : leadingHomog F * leadingHomog G ≠ 0 := mul_ne_zero (leadingHomog_ne_zero hF) (leadingHomog_ne_zero hG)
  have hcomp_eq := homogeneousComponent_mul_top F G
  have hge : F.totalDegree + G.totalDegree ≤ (F * G).totalDegree := by
    by_contra hlt
    exact hprod_ne (hcomp_eq ▸ MvPolynomial.homogeneousComponent_eq_zero _ _ (not_le.mp hlt))
  exact le_antisymm hle hge

private lemma isUnit_mvPoly_iff {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    IsUnit P ↔ ∃ c : ℝ, c ≠ 0 ∧ P = MvPolynomial.C c := by
  constructor
  · intro hu
    obtain ⟨Q, hQ⟩ := hu.exists_right_inv
    have hPne : P ≠ 0 := hu.ne_zero
    have hQne : Q ≠ 0 := fun h => by rw [h, mul_zero] at hQ; exact one_ne_zero hQ.symm
    have hdeg := congrArg MvPolynomial.totalDegree hQ
    rw [totalDegree_mul_eq hPne hQne, MvPolynomial.totalDegree_one] at hdeg
    have hP0 : P.totalDegree = 0 := by omega
    refine ⟨MvPolynomial.coeff 0 P, ?_, ?_⟩
    · intro hc0
      apply hPne
      ext d
      by_cases hd : d = 0
      · subst hd; simp [hc0]
      · by_contra hne
        have hle := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hne)
        have hpos : 0 < d.sum (fun _ k => k) := by
          obtain ⟨j, hj⟩ : ∃ j, d j ≠ 0 := by by_contra hall; push Not at hall; exact hd (Finsupp.ext hall)
          exact lt_of_lt_of_le (Nat.pos_of_ne_zero hj)
            (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finsupp.mem_support_iff.mpr hj))
        omega
    · ext d
      by_cases hd : d = 0
      · subst hd; simp
      · simp only [MvPolynomial.coeff_C, if_neg (Ne.symm hd)]
        by_contra hne
        have hle := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hne)
        have hpos : 0 < d.sum (fun _ k => k) := by
          obtain ⟨j, hj⟩ : ∃ j, d j ≠ 0 := by by_contra hall; push Not at hall; exact hd (Finsupp.ext hall)
          exact lt_of_lt_of_le (Nat.pos_of_ne_zero hj)
            (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finsupp.mem_support_iff.mpr hj))
        omega
  · rintro ⟨c, hc, rfl⟩
    exact ⟨⟨MvPolynomial.C c, MvPolynomial.C c⁻¹,
      by rw [← map_mul, mul_inv_cancel₀ hc, map_one],
      by rw [← map_mul, inv_mul_cancel₀ hc, map_one]⟩, rfl⟩

private lemma prime_of_totalDegree_one {n : ℕ} {L : MvPolynomial (Fin n) ℝ} (hdeg : L.totalDegree = 1) :
    Prime L := by
  have hirr : Irreducible L := by
    refine ⟨fun hu => ?_, fun a b hab => ?_⟩
    · obtain ⟨c, _, rfl⟩ := (isUnit_mvPoly_iff L).mp hu
      rw [MvPolynomial.totalDegree_C] at hdeg; omega
    · have hLne : L ≠ 0 := fun h => by rw [h, MvPolynomial.totalDegree_zero] at hdeg; omega
      have ha : a ≠ 0 := fun h => hLne (by rw [hab, h, zero_mul])
      have hb : b ≠ 0 := fun h => hLne (by rw [hab, h, mul_zero])
      have hd := congrArg MvPolynomial.totalDegree hab
      rw [hdeg, totalDegree_mul_eq ha hb] at hd
      have h0 : a.totalDegree = 0 ∨ b.totalDegree = 0 := by omega
      rcases h0 with ha0 | hb0
      · left
        have ha_eq : a = MvPolynomial.C (MvPolynomial.coeff 0 a) := by
          ext d; by_cases hd0 : d = 0
          · subst hd0; simp
          · simp only [MvPolynomial.coeff_C, if_neg (Ne.symm hd0)]
            by_contra hne
            have hle := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hne)
            have hpos : 0 < d.sum (fun _ k => k) := by
              obtain ⟨j, hj⟩ : ∃ j, d j ≠ 0 := by by_contra hall; push Not at hall; exact hd0 (Finsupp.ext hall)
              exact lt_of_lt_of_le (Nat.pos_of_ne_zero hj)
                (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finsupp.mem_support_iff.mpr hj))
            omega
        exact (isUnit_mvPoly_iff a).mpr ⟨MvPolynomial.coeff 0 a, fun h => ha (by rw [ha_eq, h, map_zero]), ha_eq⟩
      · right
        have hb_eq : b = MvPolynomial.C (MvPolynomial.coeff 0 b) := by
          ext d; by_cases hd0 : d = 0
          · subst hd0; simp
          · simp only [MvPolynomial.coeff_C, if_neg (Ne.symm hd0)]
            by_contra hne
            have hle := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hne)
            have hpos : 0 < d.sum (fun _ k => k) := by
              obtain ⟨j, hj⟩ : ∃ j, d j ≠ 0 := by by_contra hall; push Not at hall; exact hd0 (Finsupp.ext hall)
              exact lt_of_lt_of_le (Nat.pos_of_ne_zero hj)
                (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finsupp.mem_support_iff.mpr hj))
            omega
        exact (isUnit_mvPoly_iff b).mpr ⟨MvPolynomial.coeff 0 b, fun h => hb (by rw [hb_eq, h, map_zero]), hb_eq⟩
  exact UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr

/-- If a multivariate polynomial over `ℝ` vanishes on the non-negative orthant `[0, ∞)^n`, it is zero. -/
private lemma mvPoly_eq_zero_of_eval_nonneg {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : ∀ s : Fin n → ℝ, (∀ j, 0 ≤ s j) → MvPolynomial.eval s P = 0) : P = 0 := by
  induction n with
  | zero =>
    have h0 := hP Fin.elim0 (fun j => j.elim0)
    have hPeq : P = MvPolynomial.C (MvPolynomial.coeff 0 P) := by
      ext d
      have hd : d = 0 := Finsupp.ext fun j => j.elim0
      subst hd; simp
    rw [hPeq, MvPolynomial.eval_C] at h0
    rw [hPeq, h0, map_zero]
  | succ n ih =>
    -- View `P` as a univariate polynomial in `X 0` over `MvPolynomial (Fin n) ℝ` via `finSuccEquiv`.
    let Q := MvPolynomial.finSuccEquiv ℝ n P
    have hQ0 : Q = 0 := by
      apply Polynomial.ext
      intro k
      simp only [Polynomial.coeff_zero]
      apply ih
      intro s hs
      -- For fixed `s ≥ 0`, `t ↦ eval t (Q.map (eval s))` vanishes for all `t ≥ 0`, so every coeff is 0!
      let q : ℝ[X] := Q.map (MvPolynomial.eval s)
      have hq_roots : ∀ t : ℝ, 0 ≤ t → q.eval t = 0 := fun t ht => by
        have hev := MvPolynomial.eval_eq_eval_mv_eval' s t P
        have hcons : ∀ j : Fin (n + 1), 0 ≤ (Fin.cons t s : Fin (n + 1) → ℝ) j :=
          fun j => Fin.cases ht hs j
        have h0 := hP (Fin.cons t s) hcons
        rw [hev] at h0
        simpa [q, Q, MvPolynomial.eval_map] using h0
      have hq0 : q = 0 := by
        by_contra hne
        have hfin : (q.roots.toFinset : Set ℝ).Finite := Set.toFinite _
        have hsub : Set.Ici (0 : ℝ) ⊆ (q.roots.toFinset : Set ℝ) := fun t ht => by
          simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot]
          exact hq_roots t ht
        exact (Set.Ici_infinite (0 : ℝ)) (hfin.subset hsub)
      have := congrArg (fun f : ℝ[X] => f.coeff k) hq0
      simpa [q, Polynomial.coeff_map] using this
    exact (MvPolynomial.finSuccEquiv ℝ n).injective (by simpa [Q] using hQ0)

/-- Theorem 4.2 (`thm-invariant`): Leading homogeneous part of minimal denominator of an `MPH*_n`
transform factors into real linear forms with non-negative coefficients. -/
private lemma mph_factorization {n : ℕ} (P Q : MvPolynomial (Fin n) ℝ)
    (hQne : Q ≠ 0)
    (hcop : ∀ D : MvPolynomial (Fin n) ℝ, D ∣ P → D ∣ Q → IsUnit D)
    (hrep : ∃ (m : ℕ) (_ : 1 ≤ m) (α : Fin m → ℝ) (T : Matrix (Fin m) (Fin m) ℝ)
      (K : Matrix (Fin m) (Fin n) ℝ),
      IsTransientSubgenerator T ∧
      (∀ i, 0 ≤ α i) ∧ (∑ i, α i ≤ 1) ∧ (∀ i j, 0 ≤ K i j) ∧
      ∀ s : Fin n → ℝ, (∀ j, 0 ≤ s j) →
        MvPolynomial.eval s Q ≠ 0 ∧
        IsUnit (-T + Matrix.diagonal (K.mulVec s)).det ∧
        MvPolynomial.eval s P / MvPolynomial.eval s Q =
          kulkarniEval (1 - ∑ i, α i) α T K (-(T.mulVec 1)) s) :
    ∃ (c : ℝ) (_ : c ≠ 0) (c₀ : ℝ) (_ : 0 < c₀) (ν : ℕ) (lam : Fin ν → Fin n → ℝ),
      (∀ i j, 0 ≤ lam i j) ∧
      MvPolynomial.C c * leadingHomog Q =
        MvPolynomial.C c₀ * ∏ i : Fin ν, ∑ j : Fin n, MvPolynomial.C (lam i j) * MvPolynomial.X j := by
  classical
  obtain ⟨m, _, α, T, K, hT, _, _, hK_nonneg, hEq⟩ := hrep
  let κ : Fin m → MvPolynomial (Fin n) ℝ := fun i =>
    ∑ j : Fin n, MvPolynomial.C (K i j) * MvPolynomial.X j
  let Mpoly : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ) :=
    (-T).map MvPolynomial.C + Matrix.diagonal κ
  let F : MvPolynomial (Fin n) ℝ := Mpoly.det
  let N : MvPolynomial (Fin n) ℝ :=
    MvPolynomial.C (1 - ∑ i, α i) * F +
    ∑ i : Fin m, ∑ k : Fin m, MvPolynomial.C (α i) * Mpoly.adjugate i k * MvPolynomial.C (-(T.mulVec 1) k)
  -- Show `P * F = Q * N` by evaluating on `[0, ∞)^n`.
  have hPF_eq_QN : P * F = Q * N := by
    apply sub_eq_zero.mp
    apply mvPoly_eq_zero_of_eval_nonneg
    intro s hs
    obtain ⟨hQs, hu, hrat⟩ := hEq s hs
    have hM_eval : Mpoly.map (MvPolynomial.eval s) = -T + Matrix.diagonal (K.mulVec s) := by
      ext i k
      simp only [Mpoly, κ, Matrix.map_apply, Matrix.add_apply, Matrix.neg_apply, Matrix.diagonal_apply,
        map_add, MvPolynomial.eval_C, Matrix.mulVec, dotProduct]
      split_ifs <;> simp
    have hF_eval : MvPolynomial.eval s F = (-T + Matrix.diagonal (K.mulVec s)).det := by
      simpa [F, RingHom.mapMatrix_apply, hM_eval] using RingHom.map_det (MvPolynomial.eval s) Mpoly
    have hadj : Mpoly.adjugate.map (MvPolynomial.eval s) = (-T + Matrix.diagonal (K.mulVec s)).adjugate := by
      simpa [RingHom.mapMatrix_apply, hM_eval] using RingHom.map_adjugate (MvPolynomial.eval s) Mpoly
    have hN_eval : MvPolynomial.eval s N =
        (1 - ∑ i, α i) * (-T + Matrix.diagonal (K.mulVec s)).det +
        dotProduct α ((-T + Matrix.diagonal (K.mulVec s)).adjugate.mulVec (-(T.mulVec 1))) := by
      simp only [N, map_add, map_mul, map_sum, MvPolynomial.eval_C, hF_eval, dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.neg_apply]
      congr 1; refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      have hik : MvPolynomial.eval s (Mpoly.adjugate i k) = (-T + Matrix.diagonal (K.mulVec s)).adjugate i k :=
        congrArg (fun X => X i k) hadj
      rw [hik]; ring
    have hFs : MvPolynomial.eval s F ≠ 0 := hF_eval.symm ▸ hu.ne_zero
    have hrat2 : MvPolynomial.eval s P / MvPolynomial.eval s Q = MvPolynomial.eval s N / MvPolynomial.eval s F := by
      rw [hrat, hN_eval, hF_eval]
      dsimp only [kulkarniEval]
      rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
      have hdne : (-T + Matrix.diagonal (K.mulVec s)).det ≠ 0 := hu.ne_zero
      field_simp [hdne]
    simp only [map_sub, map_mul]
    have := (div_eq_div_iff hQs hFs).mp hrat2
    linarith
  -- Since `P` and `Q` are coprime in the UFD `MvPolynomial (Fin n) ℝ`, `Q ∣ F`!
  have hQ_dvd_F : Q ∣ F := by
    have hrel : IsRelPrime Q P := fun D hDQ hDP => hcop D hDP hDQ
    exact hrel.dvd_of_dvd_mul_left ⟨N, hPF_eq_QN⟩
  -- Compute `F_top = C (det ((-T)_{I^c, I^c})) * ∏ i ∈ I, κ i` where `I = {i | κ i ≠ 0}`!
  let I : Finset (Fin m) := Finset.univ.filter fun i => κ i ≠ 0
  have hF_exp : F = ∑ J : Finset (Fin m),
      MvPolynomial.C (((-T).submatrix (Subtype.val : { i : Fin m // i ∉ J } → Fin m) Subtype.val).det) *
      ∏ i ∈ J, κ i := by
    have h := det_add_diagonal_expansion ((-T).map MvPolynomial.C) κ
    change F = _ at h
    rw [h]
    refine Finset.sum_congr rfl fun J _ => ?_
    congr 1
    have hsub : ((-T).map (MvPolynomial.C : ℝ →+* MvPolynomial (Fin n) ℝ)).submatrix
        (Subtype.val : { i : Fin m // i ∉ J } → Fin m) (Subtype.val : { i : Fin m // i ∉ J } → Fin m) =
        ((-T).submatrix (Subtype.val : { i : Fin m // i ∉ J } → Fin m)
          (Subtype.val : { i : Fin m // i ∉ J } → Fin m)).map (MvPolynomial.C : ℝ →+* MvPolynomial (Fin n) ℝ) := rfl
    rw [hsub]
    exact (RingHom.map_det (MvPolynomial.C : ℝ →+* MvPolynomial (Fin n) ℝ) _).symm
  have hwt_eq : ∀ d : Fin n →₀ ℕ, d.sum (fun _ e => e) = (Finsupp.weight (1 : Fin n → ℕ)) d := fun d => by
    simp [Finsupp.weight_apply, Finsupp.sum]
  have hκ_deg : ∀ i ∈ I, (κ i).totalDegree = 1 := by
    intro i hi
    have hne : κ i ≠ 0 := (Finset.mem_filter.mp hi).2
    have hhom : (κ i).IsHomogeneous 1 := by
      refine MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ => ?_
      simpa using (MvPolynomial.isHomogeneous_C (Fin n) (K i j)).mul (MvPolynomial.isHomogeneous_X ℝ j)
    apply le_antisymm
    · exact Finset.sup_le fun d hd => by rw [hwt_eq d, hhom (MvPolynomial.mem_support_iff.mp hd)]
    · obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hne
      have h1 : d.sum (fun _ e => e) = 1 := by rw [hwt_eq d]; exact hhom (MvPolynomial.mem_support_iff.mp hd)
      rw [← h1]; exact MvPolynomial.le_totalDegree hd
  have hκ_hom : ∀ i ∈ I, (κ i).IsHomogeneous 1 := fun i _ =>
    MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ => by
      simpa using (MvPolynomial.isHomogeneous_C (Fin n) (K i j)).mul (MvPolynomial.isHomogeneous_X ℝ j)
  let cI : ℝ := ((-T).submatrix (Subtype.val : { i : Fin m // i ∉ I } → Fin m) Subtype.val).det
  have hcI_pos : 0 < cI := by
    have hsub_eq : ((-T).submatrix (Subtype.val : { i : Fin m // i ∉ I } → Fin m) Subtype.val).det =
        ((-T).submatrix (Subtype.val : { i : Fin m // i ∈ Iᶜ } → Fin m) Subtype.val).det := by
      let eI : { i : Fin m // i ∉ I } ≃ { i : Fin m // i ∈ Iᶜ } :=
        { toFun := fun x => ⟨x.val, Finset.mem_compl.mpr x.prop⟩
          invFun := fun x => ⟨x.val, Finset.mem_compl.mp x.prop⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [← Matrix.det_submatrix_equiv_self eI]; rfl
    change 0 < ((-T).submatrix (Subtype.val : { i : Fin m // i ∉ I } → Fin m) Subtype.val).det
    rw [hsub_eq]
    exact transient_principal_det_pos hT Iᶜ
  have hprodI_hom : (MvPolynomial.C cI * ∏ i ∈ I, κ i).IsHomogeneous I.card := by
    have h1 : (∏ i ∈ I, κ i).IsHomogeneous I.card := by
      have : (∏ i ∈ I, κ i).IsHomogeneous (∑ _i ∈ I, 1) :=
        MvPolynomial.IsHomogeneous.prod I κ (fun _ => 1) fun i hi => hκ_hom i hi
      simpa using this
    simpa using (MvPolynomial.isHomogeneous_C (Fin n) cI).mul h1
  have hprodI_ne : MvPolynomial.C cI * ∏ i ∈ I, κ i ≠ 0 := by
    refine mul_ne_zero (by simp [ne_of_gt hcI_pos]) (Finset.prod_ne_zero_iff.mpr fun i hi => (Finset.mem_filter.mp hi).2)
  have hF_top : leadingHomog F = MvPolynomial.C cI * ∏ i ∈ I, κ i := by
    have hdeg_term : ∀ J : Finset (Fin m), J ≠ I →
        (MvPolynomial.C (((-T).submatrix (Subtype.val : { i : Fin m // i ∉ J } → Fin m) Subtype.val).det) *
          ∏ i ∈ J, κ i).totalDegree < I.card ∨
        MvPolynomial.C (((-T).submatrix (Subtype.val : { i : Fin m // i ∉ J } → Fin m) Subtype.val).det) *
          ∏ i ∈ J, κ i = 0 := by
      intro J hJI
      by_cases hsub : J ⊆ I
      · left
        have hlt : J.card < I.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hJI⟩)
        calc (MvPolynomial.C _ * ∏ i ∈ J, κ i).totalDegree
            ≤ (MvPolynomial.C _).totalDegree + (∏ i ∈ J, κ i).totalDegree := MvPolynomial.totalDegree_mul _ _
          _ = (∏ i ∈ J, κ i).totalDegree := by rw [MvPolynomial.totalDegree_C, zero_add]
          _ ≤ ∑ i ∈ J, (κ i).totalDegree := MvPolynomial.totalDegree_finsetProd J κ
          _ = J.card := by rw [Finset.sum_congr rfl fun i hi => hκ_deg i (hsub hi)]; simp
          _ < I.card := hlt
      · right
        obtain ⟨i0, hi0J, hi0I⟩ := Finset.not_subset.mp hsub
        have hκ0 : κ i0 = 0 := by
          by_contra hne; exact hi0I (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
        rw [Finset.prod_eq_zero hi0J hκ0, mul_zero]
    have hF_comp : F.homogeneousComponent I.card = MvPolynomial.C cI * ∏ i ∈ I, κ i := by
      rw [hF_exp, map_sum, Finset.sum_eq_single I]
      · change (MvPolynomial.C cI * ∏ i ∈ I, κ i).homogeneousComponent I.card = _
        ext d
        rw [MvPolynomial.coeff_homogeneousComponent]
        by_cases hc : MvPolynomial.coeff d (MvPolynomial.C cI * ∏ i ∈ I, κ i) = 0
        · simp [hc]
        · have hd : Finsupp.degree d = I.card := by
            change d.sum (fun _ e => e) = I.card
            rw [hwt_eq d]; exact hprodI_hom hc
          simp [hd]
      · intro J _ hJI
        rcases hdeg_term J hJI with hlt | h0
        · exact MvPolynomial.homogeneousComponent_eq_zero _ _ hlt
        · rw [h0, map_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hF_deg_le : F.totalDegree ≤ I.card := by
      rw [hF_exp]
      refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) (Finset.sup_le fun J _ => ?_)
      by_cases hJI : J = I
      · subst hJI
        refine Finset.sup_le fun d hd => ?_
        rw [hwt_eq d, hprodI_hom (MvPolynomial.mem_support_iff.mp hd)]
      · rcases hdeg_term J hJI with hlt | h0
        · exact le_of_lt hlt
        · rw [h0, MvPolynomial.totalDegree_zero]; exact Nat.zero_le _
    have hF_deg_ge : I.card ≤ F.totalDegree := by
      by_contra hlt
      exact hprodI_ne (hF_comp ▸ MvPolynomial.homogeneousComponent_eq_zero _ _ (not_le.mp hlt))
    rw [leadingHomog, le_antisymm hF_deg_le hF_deg_ge, hF_comp]
  -- Since `Q ∣ F` and `F ≠ 0`, `leadingHomog Q ∣ leadingHomog F = C cI * ∏ i ∈ I, κ i`!
  have hF_ne : F ≠ 0 := fun h => hprodI_ne (by rw [← hF_top, h, leadingHomog, MvPolynomial.totalDegree_zero, map_zero])
  obtain ⟨H, hFH⟩ := hQ_dvd_F
  have hH_ne : H ≠ 0 := fun h => hF_ne (by rw [hFH, h, mul_zero])
  have hdvd_top : leadingHomog Q ∣ MvPolynomial.C cI * ∏ i ∈ I, κ i :=
    ⟨leadingHomog H, by rw [← hF_top, hFH, leadingHomog_mul hQne hH_ne]⟩
  -- Since each `κ i` (`i ∈ I`) is prime, any divisor of `C cI * ∏ i ∈ I, κ i` is a nonzero scalar times a subproduct!
  have hdvd_subprod : ∀ (S : Finset (Fin m)), S ⊆ I →
      ∀ D : MvPolynomial (Fin n) ℝ, D ∣ MvPolynomial.C cI * ∏ i ∈ S, κ i →
      ∃ (J : Finset (Fin m)) (u : ℝ), J ⊆ S ∧ u ≠ 0 ∧ D = MvPolynomial.C u * ∏ i ∈ J, κ i := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _ D hD
      simp only [Finset.prod_empty, mul_one] at hD
      have hu : IsUnit D := isUnit_of_dvd_unit hD ((isUnit_mvPoly_iff _).mpr ⟨cI, ne_of_gt hcI_pos, rfl⟩)
      obtain ⟨u, hu0, rfl⟩ := (isUnit_mvPoly_iff D).mp hu
      exact ⟨∅, u, Finset.empty_subset _, hu0, by simp⟩
    | @insert a S' ha ih =>
      intro hsub D hD
      have haI : a ∈ I := hsub (Finset.mem_insert_self a S')
      have hS'I : S' ⊆ I := fun x hx => hsub (Finset.mem_insert_of_mem hx)
      have hprime : Prime (κ a) := prime_of_totalDegree_one (hκ_deg a haI)
      rw [Finset.prod_insert ha] at hD
      have hD' : D ∣ κ a * (MvPolynomial.C cI * ∏ i ∈ S', κ i) := by
        obtain ⟨R, hR⟩ := hD; exact ⟨R, by rw [← hR]; ring⟩
      obtain ⟨R, hR⟩ := hD'
      have hpa : κ a ∣ D * R := ⟨MvPolynomial.C cI * ∏ i ∈ S', κ i, hR.symm⟩
      rcases hprime.dvd_or_dvd hpa with ⟨D', rfl⟩ | ⟨R', rfl⟩
      · have hD'_dvd : D' ∣ MvPolynomial.C cI * ∏ i ∈ S', κ i :=
          ⟨R, mul_left_cancel₀ hprime.ne_zero (by linear_combination hR)⟩
        obtain ⟨J, u, hJS', hu0, rfl⟩ := ih hS'I D' hD'_dvd
        refine ⟨insert a J, u, Finset.insert_subset_insert a hJS', hu0, ?_⟩
        rw [Finset.prod_insert (fun h => ha (hJS' h))]; ring
      · have hD_dvd : D ∣ MvPolynomial.C cI * ∏ i ∈ S', κ i :=
          ⟨R', mul_left_cancel₀ hprime.ne_zero (by linear_combination hR)⟩
        obtain ⟨J, u, hJS', hu0, rfl⟩ := ih hS'I D hD_dvd
        exact ⟨J, u, Finset.Subset.trans hJS' (Finset.subset_insert a S'), hu0, rfl⟩
  obtain ⟨J, u, _, hu0, hQtop_eq⟩ := hdvd_subprod I (Finset.Subset.refl I) (leadingHomog Q) hdvd_top
  let eJ : Fin J.card ≃ J := (Fintype.equivFinOfCardEq (Fintype.card_coe J)).symm
  refine ⟨u⁻¹, inv_ne_zero hu0, 1, zero_lt_one, J.card, fun i j => K (eJ i).val j,
    fun i j => hK_nonneg (eJ i).val j, ?_⟩
  rw [hQtop_eq, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hu0, map_one, one_mul, one_mul]
  rw [← Finset.prod_coe_sort J κ]
  exact (Equiv.prod_comp eJ (fun x : J => κ x.val)).symm

/-! ### Section 4: Wishart Trace Law and Strict Separation `MPH*_n ⊂neq MVPH_n` (`n ≥ 3`) -/

/-- Exact 1D Gaussian integral: `∫ x, exp (-a * x^2 / 2) = √(2π / a)` for `a > 0`. -/
private lemma integral_gaussian_half {a : ℝ} (ha : 0 < a) :
    ∫ x : ℝ, Real.exp (-(a * x ^ 2 / 2)) = Real.sqrt (2 * Real.pi / a) := by
  have h := integral_gaussian (a / 2)
  have heq : (fun x : ℝ => Real.exp (-(a * x ^ 2 / 2))) = fun x => Real.exp (-(a / 2) * x ^ 2) := by
    ext x; congr 1; ring
  rw [heq, h]
  congr 1; field_simp [ne_of_gt ha]

/-- Exact 2D Gaussian integral for positive definite `2 × 2` quadratic form:
`(2π)⁻¹ ∫∫ exp (-((a * u^2 + 2 * b * u * v + c * v^2) / 2)) = (a * c - b^2) ^ (-(1/2))`
(expressed as `(Real.sqrt (a * c - b^2))⁻¹`). -/
private lemma integral_gaussian_2d {a b c : ℝ} (ha : 0 < a) (hdet : 0 < a * c - b ^ 2) :
    ∫ p : ℝ × ℝ, Real.exp (-((a * p.1 ^ 2 + 2 * b * p.1 * p.2 + c * p.2 ^ 2) / 2)) ∂(volume.prod volume) =
      2 * Real.pi / Real.sqrt (a * c - b ^ 2) := by
  let d := (a * c - b ^ 2) / a
  have hd : 0 < d := div_pos hdet ha
  have hdecomp : ∀ u v : ℝ,
      a * u ^ 2 + 2 * b * u * v + c * v ^ 2 = a * (u + (b / a) * v) ^ 2 + d * v ^ 2 := fun u v => by
    dsimp [d]; field_simp [ne_of_gt ha]; ring
  have hinner : ∀ v : ℝ,
      ∫ u : ℝ, Real.exp (-((a * u ^ 2 + 2 * b * u * v + c * v ^ 2) / 2)) =
        Real.exp (-(d * v ^ 2 / 2)) * Real.sqrt (2 * Real.pi / a) := by
    intro v
    have heq : (fun u : ℝ => Real.exp (-((a * u ^ 2 + 2 * b * u * v + c * v ^ 2) / 2))) =
        fun u => Real.exp (-(d * v ^ 2 / 2)) * Real.exp (-(a * (u + (b / a) * v) ^ 2 / 2)) := by
      ext u; rw [hdecomp u v, ← Real.exp_add]; congr 1; ring
    have hshift := MeasureTheory.integral_add_right_eq_self (μ := volume) (fun u : ℝ => Real.exp (-(a * u ^ 2 / 2))) ((b / a) * v)
    rw [heq, MeasureTheory.integral_const_mul, hshift, integral_gaussian_half ha]
  have hint : Integrable (fun p : ℝ × ℝ => Real.exp (-((a * p.1 ^ 2 + 2 * b * p.1 * p.2 + c * p.2 ^ 2) / 2)))
      (volume.prod volume) := by
    refine (MeasureTheory.integrable_prod_iff' ?_).mpr ⟨?_, ?_⟩
    · exact (Continuous.aestronglyMeasurable (by fun_prop))
    · refine Filter.Eventually.of_forall fun v => ?_
      have heq : (fun u : ℝ => Real.exp (-((a * u ^ 2 + 2 * b * u * v + c * v ^ 2) / 2))) =
          fun u => Real.exp (-(d * v ^ 2 / 2)) * Real.exp (-(a / 2) * (u + (b / a) * v) ^ 2) := by
        ext u; rw [hdecomp u v, ← Real.exp_add]; congr 1; ring
      rw [heq]
      exact ((integrable_exp_neg_mul_sq (by linarith : 0 < a / 2)).comp_add_right _).const_mul _
    · simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have heq : (fun v : ℝ => ∫ u : ℝ, Real.exp (-((a * u ^ 2 + 2 * b * u * v + c * v ^ 2) / 2))) =
          fun v => Real.sqrt (2 * Real.pi / a) * Real.exp (-(d / 2) * v ^ 2) := by
        ext v; rw [hinner v, mul_comm]; congr 2; ring
      rw [heq]
      exact (integrable_exp_neg_mul_sq (by linarith : 0 < d / 2)).const_mul _
  -- Swap `prod` integral order: `∫ (u, v), f u v = ∫ v, ∫ u, f u v`!
  rw [MeasureTheory.integral_prod_symm _ hint]
  simp_rw [hinner]
  rw [MeasureTheory.integral_mul_const, integral_gaussian_half hd]
  have hpi : 0 < 2 * Real.pi := by positivity
  rw [← Real.sqrt_mul (div_nonneg (le_of_lt hpi) (le_of_lt hd))]
  have hmul : (2 * Real.pi / d) * (2 * Real.pi / a) = (2 * Real.pi) ^ 2 / (a * c - b ^ 2) := by
    dsimp [d]; field_simp [ne_of_gt ha, ne_of_gt hdet]
  rw [hmul, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (le_of_lt hpi)]

/-- Standard 1D exponential probability measure `Exp(1)` on `ℝ`. -/
private noncomputable def expOneMeasure : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (if 0 ≤ x then Real.exp (-x) else 0)

private lemma integral_exp_neg_mul_Ioi {r : ℝ} (hr : 0 < r) :
    ∫ x : ℝ in Set.Ioi (0 : ℝ), Real.exp (-(r * x)) = r⁻¹ := by
  have h := integral_exp_mul_Ioi (a := -r) (neg_lt_zero.mpr hr) 0
  have heq : (fun x : ℝ => Real.exp (-(r * x))) = fun x => Real.exp (-r * x) := by
    ext x; congr 1; ring
  rw [heq, h]
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq, one_div]

private lemma isProbabilityMeasure_expOne : IsProbabilityMeasure expOneMeasure := by
  refine ⟨?_⟩
  rw [expOneMeasure, MeasureTheory.withDensity_apply _ MeasurableSet.univ, MeasureTheory.Measure.restrict_univ]
  have hnn : ∀ x : ℝ, 0 ≤ (if 0 ≤ x then Real.exp (-x) else 0) := fun x => by split_ifs; exact le_of_lt (Real.exp_pos _); exact le_rfl
  have hint : Integrable (fun x : ℝ => if 0 ≤ x then Real.exp (-x) else 0) volume := by
    have heq : (fun x : ℝ => if 0 ≤ x then Real.exp (-x) else 0) =
        (Set.Ici (0 : ℝ)).indicator (fun x => Real.exp ((-1 : ℝ) * x)) := by
      ext x; simp [Set.indicator, Set.mem_Ici]
    rw [heq, MeasureTheory.integrable_indicator_iff measurableSet_Ici]
    have h1 : IntegrableOn (fun x : ℝ => Real.exp ((-1 : ℝ) * x)) (Set.Ioi 0) volume :=
      integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0
    rw [MeasureTheory.IntegrableOn, ← MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioi_ae_eq_Ici]
    exact h1
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn)]
  have heq : ∫ x : ℝ, (if 0 ≤ x then Real.exp (-x) else 0) = ∫ x in Set.Ioi (0 : ℝ), Real.exp (-(1 * x)) := by
    rw [← MeasureTheory.integral_Ici_eq_integral_Ioi]
    have : (fun x : ℝ => if 0 ≤ x then Real.exp (-x) else 0) =
        (Set.Ici (0 : ℝ)).indicator (fun x => Real.exp (-(1 * x))) := by
      ext x; simp [Set.indicator, Set.mem_Ici]
    rw [this, MeasureTheory.integral_indicator measurableSet_Ici]
  rw [heq, integral_exp_neg_mul_Ioi zero_lt_one, inv_one, ENNReal.ofReal_one]

private lemma expOne_ae_nonneg : ∀ᵐ x ∂expOneMeasure, 0 ≤ x := by
  have hset : {x : ℝ | ¬ 0 ≤ x} = (Set.Ici (0 : ℝ))ᶜ := rfl
  rw [MeasureTheory.ae_iff, hset, expOneMeasure, MeasureTheory.withDensity_apply _ measurableSet_Ici.compl]
  have h0 : ∀ x ∈ (Set.Ici (0 : ℝ))ᶜ, ENNReal.ofReal (if 0 ≤ x then Real.exp (-x) else 0) = 0 := fun x hx => by
    have hx' : ¬ 0 ≤ x := by simpa [Set.mem_Ici] using hx
    simp [hx']
  rw [MeasureTheory.setLIntegral_congr_fun measurableSet_Ici.compl h0]
  simp

private lemma integral_expOne_laplace {s : ℝ} (hs : 0 ≤ s) :
    ∫ x : ℝ, Real.exp (-(s * x)) ∂expOneMeasure = (1 + s)⁻¹ := by
  have hmeas : Measurable fun x : ℝ => if 0 ≤ x then Real.exp (-x) else 0 :=
    Measurable.ite measurableSet_Ici (by fun_prop) measurable_const
  rw [expOneMeasure, integral_withDensity_eq_integral_toReal_smul (hmeas.ennreal_ofReal)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hsimpl : (fun x : ℝ => (ENNReal.ofReal (if 0 ≤ x then Real.exp (-x) else 0)).toReal • Real.exp (-(s * x))) =
      (Set.Ici (0 : ℝ)).indicator (fun x => Real.exp (-((1 + s) * x))) := by
    ext x
    by_cases hx : 0 ≤ x
    · simp only [if_pos hx, ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _)), smul_eq_mul,
        Set.indicator_of_mem (Set.mem_Ici.mpr hx), ← Real.exp_add]
      congr 1; ring
    · simp [hx, Set.indicator_of_notMem]
  rw [hsimpl, MeasureTheory.integral_indicator measurableSet_Ici, MeasureTheory.integral_Ici_eq_integral_Ioi,
      integral_exp_neg_mul_Ioi (by linarith)]

/-- Standard 1D Gaussian probability measure `N(0, 1)` on `ℝ` written directly via `withDensity`. -/
private noncomputable def stdGaussMeasure : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2)))

private lemma isProbabilityMeasure_stdGauss : IsProbabilityMeasure stdGaussMeasure := by
  refine ⟨?_⟩
  rw [stdGaussMeasure, MeasureTheory.withDensity_apply _ MeasurableSet.univ, MeasureTheory.Measure.restrict_univ]
  have hpi : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hint : Integrable (fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2))) volume := by
    have : (fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2))) =
        fun x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2) * x ^ 2) := by
      ext x; congr 2; ring
    rw [this]; exact (integrable_exp_neg_mul_sq (by norm_num)).const_mul _
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => mul_nonneg (inv_nonneg.mpr (le_of_lt hpi)) (le_of_lt (Real.exp_pos _)))]
  rw [MeasureTheory.integral_const_mul]
  have h1 : ∫ x : ℝ, Real.exp (-(x ^ 2 / 2)) = Real.sqrt (2 * Real.pi) := by
    simpa using integral_gaussian_half (a := 1) zero_lt_one
  rw [h1, inv_mul_cancel₀ (ne_of_gt hpi), ENNReal.ofReal_one]

/-- Every finite product of exponential transforms `∏_{k=0}^{m-1} (1 + u * r_k)⁻¹` (`m ≥ 1`, `r_k > 0`)
is a univariate phase-type Laplace transform! -/
private lemma prod_exp_isUnivariatePH {m : ℕ} (hm : 1 ≤ m) (r : Fin m → ℝ) (hr : ∀ k, 0 < r k) :
    IsUnivariatePHTransform (fun u => ∏ k : Fin m, (1 + u * r k)⁻¹) := by
  -- Tandem Markov chain with rates `λ_k = (r k)⁻¹ > 0`:
  -- `T i i = -λ_i`, `T i (i + 1) = λ_i`, `0` elsewhere; `α = Pi.single 0 1`.
  let lam : Fin m → ℝ := fun k => (r k)⁻¹
  have hlam : ∀ k, 0 < lam k := fun k => inv_pos.mpr (hr k)
  let T : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun i j =>
    if i = j then -lam i else if i.val + 1 = j.val then lam i else 0
  let α : Fin m → ℝ := Pi.single ⟨0, by omega⟩ 1
  -- `T` is upper triangular with diagonal `-lam i < 0`, so its charpoly is `∏ (X + lam i)`!
  have hT_hurwitz : IsHurwitzStable T := by
    intro μ hμ
    rw [Polynomial.IsRoot, eval_charpoly_eq_det] at hμ
    have htri : (μ • (1 : Matrix (Fin m) (Fin m) ℂ) - T.map Complex.ofReal).IsUpperTriangular := by
      intro i j hij
      have hne : i ≠ j := ne_of_gt hij
      have hne1 : i.val + 1 ≠ j.val := by have : j.val < i.val := hij; omega
      simp [T, hne, hne1]
    rw [Matrix.det_of_isUpperTriangular htri, Finset.prod_eq_zero_iff] at hμ
    obtain ⟨i, _, hi⟩ := hμ
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
      Matrix.map_apply, T, Matrix.of_apply, ↓reduceIte, Complex.ofReal_neg, sub_neg_eq_add] at hi
    have hμ_eq : μ = -(lam i : ℂ) := eq_neg_of_add_eq_zero_left hi
    rw [hμ_eq, Complex.neg_re, Complex.ofReal_re]
    exact neg_lt_zero.mpr (hlam i)
  have hT_sub : IsTransientSubgenerator T := by
    refine ⟨hT_hurwitz, fun i => by simp [T, hlam i], fun i j hij => ?_, fun i => ?_⟩
    · simp only [T, Matrix.of_apply, if_neg hij]; split_ifs; exact le_of_lt (hlam i); exact le_rfl
    · by_cases hi : i.val + 1 < m
      · let j1 : Fin m := ⟨i.val + 1, hi⟩
        have hij1 : i ≠ j1 := fun h => by have := congrArg Fin.val h; dsimp [j1] at this; omega
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
            ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hij1.symm, Finset.mem_univ j1⟩)]
        have hrest : ∑ x ∈ (Finset.univ.erase i).erase j1, T i x = 0 := by
          apply Finset.sum_eq_zero; intro x hx
          have hx1 : x ≠ j1 := (Finset.mem_erase.mp hx).1
          have hx2 : x ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
          have hne1 : i.val + 1 ≠ x.val := fun h => hx1 (Fin.ext h.symm)
          simp [T, hx2.symm, hne1]
        rw [hrest, add_zero]
        simp [T, hij1, j1]
      · rw [Finset.sum_eq_single i]
        · simp [T]; exact le_of_lt (hlam i)
        · intro x _ hxi
          have hne1 : i.val + 1 ≠ x.val := by have := x.isLt; omega
          simp [T, hxi.symm, hne1]
        · intro h; exact absurd (Finset.mem_univ _) h
  refine ⟨m, hm, α, T, hT_sub, fun i => by simp [α, Pi.single_apply]; split_ifs <;> norm_num, ?_, fun u hu => ?_⟩
  · simp [α]
  · -- For `u ≥ 0`, `u • 1 - T` is upper triangular with positive diagonal `u + lam i > 0`!
    have htri_u : (u • (1 : Matrix (Fin m) (Fin m) ℝ) - T).IsUpperTriangular := by
      intro i j hij
      have hne : i ≠ j := ne_of_gt hij
      have hne1 : i.val + 1 ≠ j.val := by have : j.val < i.val := hij; omega
      simp [T, hne, hne1]
    have hdet_u : (u • (1 : Matrix (Fin m) (Fin m) ℝ) - T).det = ∏ i : Fin m, (u + lam i) := by
      rw [Matrix.det_of_isUpperTriangular htri_u]
      refine Finset.prod_congr rfl fun i _ => by simp [T]
    have hu_det : IsUnit (u • (1 : Matrix (Fin m) (Fin m) ℝ) - T).det := by
      rw [hdet_u, isUnit_iff_ne_zero]
      exact Finset.prod_ne_zero_iff.mpr fun i _ => ne_of_gt (by linarith [hlam i])
    refine ⟨hu_det, ?_⟩
    -- Explicit solution `v i = ∏_{k ≥ i} (1 + u * r k)⁻¹` satisfies `(u • 1 - T) * v = -T 1`!
    let v : Fin m → ℝ := fun i => ∏ k ∈ Finset.univ.filter (fun k : Fin m => i.val ≤ k.val), (1 + u * r k)⁻¹
    have hv_eq : (u • (1 : Matrix (Fin m) (Fin m) ℝ) - T).mulVec v = -(T.mulVec 1) := by
      ext i
      have h1ur : 1 + u * r i ≠ 0 := ne_of_gt (by nlinarith [hr i])
      have hT1 : (-(T.mulVec 1)) i = if i.val + 1 < m then 0 else lam i := by
        simp only [Matrix.mulVec, dotProduct, Pi.neg_apply, Pi.one_apply, mul_one]
        by_cases hi : i.val + 1 < m
        · rw [if_pos hi]
          let j1 : Fin m := ⟨i.val + 1, hi⟩
          have hij1 : i ≠ j1 := fun h => by have := congrArg Fin.val h; dsimp [j1] at this; omega
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
              ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hij1.symm, Finset.mem_univ j1⟩)]
          have hrest : ∑ x ∈ (Finset.univ.erase i).erase j1, T i x = 0 := by
            apply Finset.sum_eq_zero; intro x hx
            have hx1 : x ≠ j1 := (Finset.mem_erase.mp hx).1
            have hx2 : x ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
            have hne1 : i.val + 1 ≠ x.val := fun h => hx1 (Fin.ext h.symm)
            simp [T, hx2.symm, hne1]
          rw [hrest, add_zero]; simp [T, hij1, j1]
        · rw [if_neg hi, Finset.sum_eq_single i]
          · simp [T]
          · intro x _ hxi; have hne1 : i.val + 1 ≠ x.val := by have := x.isLt; omega
            simp [T, hxi.symm, hne1]
          · intro h; exact absurd (Finset.mem_univ _) h
      rw [hT1]
      simp only [Matrix.mulVec, dotProduct]
      by_cases hi : i.val + 1 < m
      · rw [if_pos hi]
        let j1 : Fin m := ⟨i.val + 1, hi⟩
        have hij1 : i ≠ j1 := fun h => by have := congrArg Fin.val h; dsimp [j1] at this; omega
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
            ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hij1.symm, Finset.mem_univ j1⟩)]
        have hrest : ∑ x ∈ (Finset.univ.erase i).erase j1, (u • (1 : Matrix (Fin m) (Fin m) ℝ) - T) i x * v x = 0 := by
          apply Finset.sum_eq_zero; intro x hx
          have hx1 : x ≠ j1 := (Finset.mem_erase.mp hx).1
          have hx2 : x ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
          have hne1 : i.val + 1 ≠ x.val := fun h => hx1 (Fin.ext h.symm)
          simp [T, hx2.symm, hne1]
        rw [hrest, add_zero]
        have hfilt : Finset.univ.filter (fun k : Fin m => i.val ≤ k.val) =
            insert i (Finset.univ.filter (fun k : Fin m => j1.val ≤ k.val)) := by
          ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, j1]; constructor
          · intro hk; by_cases hki : k = i; exact Or.inl hki; right; have : k.val ≠ i.val := fun h => hki (Fin.ext h); omega
          · rintro (rfl | hk); exact le_rfl; omega
        have hi_not : i ∉ Finset.univ.filter (fun k : Fin m => j1.val ≤ k.val) := by simp [j1]
        have hvi : v i = (1 + u * r i)⁻¹ * v j1 := by
          dsimp only [v]; rw [hfilt, Finset.prod_insert hi_not]
        simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, ↓reduceIte, if_neg hij1,
          smul_eq_mul, mul_one, T, Matrix.of_apply, j1, sub_neg_eq_add]
        rw [hvi]
        dsimp only [lam]
        have hri : r i ≠ 0 := ne_of_gt (hr i)
        field_simp [hri, h1ur]; ring
      · rw [if_neg hi, Finset.sum_eq_single i]
        · have hfilt : Finset.univ.filter (fun k : Fin m => i.val ≤ k.val) = {i} := by
            ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
            constructor
            · intro hk; exact Fin.ext (by have := k.isLt; omega)
            · rintro rfl; exact le_rfl
          have hvi : v i = (1 + u * r i)⁻¹ := by dsimp only [v]; rw [hfilt, Finset.prod_singleton]
          simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
            T, Matrix.of_apply, ↓reduceIte, sub_neg_eq_add, hvi]
          dsimp only [lam]
          have hri : r i ≠ 0 := ne_of_gt (hr i)
          field_simp [hri, h1ur]; ring
        · intro x _ hxi
          have hne1 : i.val + 1 ≠ x.val := by have := x.isLt; omega
          simp [T, hxi.symm, hne1]
        · intro h; exact absurd (Finset.mem_univ _) h
    have hinv_v : (u • (1 : Matrix (Fin m) (Fin m) ℝ) - T)⁻¹.mulVec (-(T.mulVec 1)) = v := by
      rw [← hv_eq, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu_det, Matrix.one_mulVec]
    rw [hinv_v]
    have hα_sum : ∑ i : Fin m, α i = 1 := by simp [α]
    rw [hα_sum, sub_self, zero_add]
    have hdot : dotProduct α v = v ⟨0, by omega⟩ := by
      simp only [dotProduct, α, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [hdot]
    dsimp only [v]
    congr 1; ext k; simp

/-- Irreducibility of the Wishart leading form `Q2 = x^2 + 4xy + 4xz + 3y^2 + 8yz + 3z^2`
over `ℝ[x, y, z]`: it cannot factor as a nonzero scalar times a product of linear forms. -/
private lemma wishart_Q2_not_linear_factor
    (c c₀ : ℝ) (hc0 : c ≠ 0) (hc₀_pos : 0 < c₀) (ν : ℕ) (lam : Fin ν → Fin 3 → ℝ)
    (hfac : MvPolynomial.C c *
      (MvPolynomial.X (0 : Fin 3) ^ 2 + MvPolynomial.C 4 * MvPolynomial.X 0 * MvPolynomial.X 1 +
       MvPolynomial.C 4 * MvPolynomial.X 0 * MvPolynomial.X 2 +
       MvPolynomial.C 3 * MvPolynomial.X 1 ^ 2 +
       MvPolynomial.C 8 * MvPolynomial.X 1 * MvPolynomial.X 2 +
       MvPolynomial.C 3 * MvPolynomial.X 2 ^ 2) =
      MvPolynomial.C c₀ * ∏ i : Fin ν, ∑ j : Fin 3, MvPolynomial.C (lam i j) * MvPolynomial.X j) :
    False := by
  let Q2 : MvPolynomial (Fin 3) ℝ :=
    MvPolynomial.X 0 ^ 2 + MvPolynomial.C 4 * MvPolynomial.X 0 * MvPolynomial.X 1 +
    MvPolynomial.C 4 * MvPolynomial.X 0 * MvPolynomial.X 2 +
    MvPolynomial.C 3 * MvPolynomial.X 1 ^ 2 +
    MvPolynomial.C 8 * MvPolynomial.X 1 * MvPolynomial.X 2 +
    MvPolynomial.C 3 * MvPolynomial.X 2 ^ 2
  have hwt3 : ∀ d : Fin 3 →₀ ℕ, d.sum (fun _ e => e) = Finsupp.weight (1 : Fin 3 → ℕ) d := fun d => by
    simp [Finsupp.weight_apply, Finsupp.sum]
  have hQ2_hom : Q2.IsHomogeneous 2 := by
    dsimp [Q2]
    have hX : ∀ i : Fin 3, (MvPolynomial.X i : MvPolynomial (Fin 3) ℝ).IsHomogeneous 1 :=
      fun i => MvPolynomial.isHomogeneous_X ℝ i
    have hC : ∀ r : ℝ, (MvPolynomial.C r : MvPolynomial (Fin 3) ℝ).IsHomogeneous 0 :=
      fun r => MvPolynomial.isHomogeneous_C (Fin 3) r
    have ht1 : (MvPolynomial.X (0 : Fin 3) ^ 2 : MvPolynomial (Fin 3) ℝ).IsHomogeneous 2 := by
      simpa [sq] using (hX 0).mul (hX 0)
    have ht2 : (MvPolynomial.C 4 * MvPolynomial.X (0 : Fin 3) * MvPolynomial.X (1 : Fin 3) : MvPolynomial (Fin 3) ℝ).IsHomogeneous 2 := by
      simpa using ((hC 4).mul (hX 0)).mul (hX 1)
    have ht3 : (MvPolynomial.C 4 * MvPolynomial.X (0 : Fin 3) * MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) ℝ).IsHomogeneous 2 := by
      simpa using ((hC 4).mul (hX 0)).mul (hX 2)
    have ht4 : (MvPolynomial.C 3 * MvPolynomial.X (1 : Fin 3) ^ 2 : MvPolynomial (Fin 3) ℝ).IsHomogeneous 2 := by
      simpa [sq] using (hC 3).mul ((hX 1).mul (hX 1))
    have ht5 : (MvPolynomial.C 8 * MvPolynomial.X (1 : Fin 3) * MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) ℝ).IsHomogeneous 2 := by
      simpa using ((hC 8).mul (hX 1)).mul (hX 2)
    have ht6 : (MvPolynomial.C 3 * MvPolynomial.X (2 : Fin 3) ^ 2 : MvPolynomial (Fin 3) ℝ).IsHomogeneous 2 := by
      simpa [sq] using (hC 3).mul ((hX 2).mul (hX 2))
    exact ((((ht1.add ht2).add ht3).add ht4).add ht5).add ht6
  have hQ2_ne : Q2 ≠ 0 := fun h => by
    have := congrArg (MvPolynomial.eval ![1, 0, 0]) h
    simp [Q2] at this
  let ℓ : Fin ν → MvPolynomial (Fin 3) ℝ := fun i =>
    ∑ j : Fin 3, MvPolynomial.C (lam i j) * MvPolynomial.X j
  have hfac' : MvPolynomial.C c * Q2 = MvPolynomial.C c₀ * ∏ i : Fin ν, ℓ i := hfac
  have hprod_ne : MvPolynomial.C c₀ * ∏ i : Fin ν, ℓ i ≠ 0 := by
    rw [← hfac']; exact mul_ne_zero (by simp [hc0]) hQ2_ne
  have hℓ_ne : ∀ i : Fin ν, ℓ i ≠ 0 := fun i h0 =>
    hprod_ne (by rw [Finset.prod_eq_zero (Finset.mem_univ i) h0, mul_zero])
  have hℓ_deg : ∀ i : Fin ν, (ℓ i).totalDegree = 1 := fun i => by
    have hhom : (ℓ i).IsHomogeneous 1 :=
      MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ => by
        simpa using (MvPolynomial.isHomogeneous_C (Fin 3) (lam i j)).mul (MvPolynomial.isHomogeneous_X ℝ j)
    apply le_antisymm
    · exact Finset.sup_le fun d hd => by rw [hwt3 d, hhom (MvPolynomial.mem_support_iff.mp hd)]
    · obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr (hℓ_ne i)
      have h1 : d.sum (fun _ e => e) = 1 := by rw [hwt3 d]; exact hhom (MvPolynomial.mem_support_iff.mp hd)
      rw [← h1]; exact MvPolynomial.le_totalDegree hd
  have hQ2_deg : Q2.totalDegree = 2 := by
    apply le_antisymm
    · exact Finset.sup_le fun d hd => by rw [hwt3 d, hQ2_hom (MvPolynomial.mem_support_iff.mp hd)]
    · obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hQ2_ne
      have h2 : d.sum (fun _ e => e) = 2 := by rw [hwt3 d]; exact hQ2_hom (MvPolynomial.mem_support_iff.mp hd)
      rw [← h2]; exact MvPolynomial.le_totalDegree hd
  have hdeg_eq := congrArg MvPolynomial.totalDegree hfac'
  have hdeg_L : (MvPolynomial.C c * Q2).totalDegree = 2 := by
    rw [totalDegree_mul_eq (by simp [hc0]) hQ2_ne, MvPolynomial.totalDegree_C, zero_add, hQ2_deg]
  have hdeg_R : (MvPolynomial.C c₀ * ∏ i : Fin ν, ℓ i).totalDegree = ν := by
    have hprod_ne' : ∏ i : Fin ν, ℓ i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hℓ_ne i
    rw [totalDegree_mul_eq (by simp [ne_of_gt hc₀_pos]) hprod_ne', MvPolynomial.totalDegree_C, zero_add]
    have hdeg_prod : ∀ S : Finset (Fin ν), (∏ i ∈ S, ℓ i).totalDegree = S.card := by
      intro S; induction S using Finset.induction_on with
      | empty => simp
      | @insert a S' ha ih =>
        rw [Finset.prod_insert ha, totalDegree_mul_eq (hℓ_ne a) (Finset.prod_ne_zero_iff.mpr fun i _ => hℓ_ne i),
            hℓ_deg a, ih, Finset.card_insert_of_notMem ha]; omega
    simpa using hdeg_prod Finset.univ
  have hν2 : ν = 2 := by rw [hdeg_L, hdeg_R] at hdeg_eq; exact hdeg_eq.symm
  subst hν2
  have hev : ∀ x y z : ℝ,
      c * (x ^ 2 + 4 * x * y + 4 * x * z + 3 * y ^ 2 + 8 * y * z + 3 * z ^ 2) =
      c₀ * (lam 0 0 * x + lam 0 1 * y + lam 0 2 * z) * (lam 1 0 * x + lam 1 1 * y + lam 1 2 * z) := by
    intro x y z
    have h := congrArg (MvPolynomial.eval ![x, y, z]) hfac'
    simp only [Q2, ℓ, map_mul, map_add, map_pow, MvPolynomial.eval_C, MvPolynomial.eval_X,
      Fin.prod_univ_two, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val] at h
    linarith
  have h100 := hev 1 0 0
  have h010 := hev 0 1 0
  have h001 := hev 0 0 1
  have h110 := hev 1 1 0
  have h101 := hev 1 0 1
  have h011 := hev 0 1 1
  have hlam0_ne : lam 0 0 ≠ 0 := fun h0 => by rw [h0] at h100; simp at h100; exact hc0 h100
  have hlam1_ne : lam 1 0 ≠ 0 := fun h0 => by rw [h0] at h100; simp at h100; exact hc0 h100
  let u := lam 0 1 / lam 0 0
  let r := lam 1 1 / lam 1 0
  let v := lam 0 2 / lam 0 0
  let t := lam 1 2 / lam 1 0
  have hc_eq : c = c₀ * lam 0 0 * lam 1 0 := by linarith
  have hur_prod : u * r = 3 := by
    dsimp [u, r]; field_simp [hlam0_ne, hlam1_ne]
    have : c₀ * (lam 0 1 * lam 1 1) = 3 * (c₀ * lam 0 0 * lam 1 0) := by linarith
    exact mul_left_cancel₀ (ne_of_gt hc₀_pos) (by linarith)
  have hvt_prod : v * t = 3 := by
    dsimp [v, t]; field_simp [hlam0_ne, hlam1_ne]
    have : c₀ * (lam 0 2 * lam 1 2) = 3 * (c₀ * lam 0 0 * lam 1 0) := by linarith
    exact mul_left_cancel₀ (ne_of_gt hc₀_pos) (by linarith)
  have hur_sum : u + r = 4 := by
    dsimp [u, r]; field_simp [hlam0_ne, hlam1_ne]
    have : c₀ * (lam 0 1 * lam 1 0 + lam 0 0 * lam 1 1) = 4 * (c₀ * lam 0 0 * lam 1 0) := by linarith
    exact mul_left_cancel₀ (ne_of_gt hc₀_pos) (by linarith)
  have hvt_sum : v + t = 4 := by
    dsimp [v, t]; field_simp [hlam0_ne, hlam1_ne]
    have : c₀ * (lam 0 2 * lam 1 0 + lam 0 0 * lam 1 2) = 4 * (c₀ * lam 0 0 * lam 1 0) := by linarith
    exact mul_left_cancel₀ (ne_of_gt hc₀_pos) (by linarith)
  have hmix : u * t + v * r = 8 := by
    dsimp [u, r, v, t]; field_simp [hlam0_ne, hlam1_ne]
    have : c₀ * (lam 0 1 * lam 1 2 + lam 0 2 * lam 1 1) = 8 * (c₀ * lam 0 0 * lam 1 0) := by linarith
    exact mul_left_cancel₀ (ne_of_gt hc₀_pos) (by linarith)
  have hu_eq : (u - 1) * (u - 3) = 0 := by
    have h : (u - 1) * (u - 3) = u * (u + r - 4) - (u * r - 3) := by ring
    rw [hur_sum, hur_prod] at h; linarith
  have hv_eq : (v - 1) * (v - 3) = 0 := by
    have h : (v - 1) * (v - 3) = v * (v + t - 4) - (v * t - 3) := by ring
    rw [hvt_sum, hvt_prod] at h; linarith
  rcases mul_eq_zero.mp hu_eq with hu1 | hu3 <;> rcases mul_eq_zero.mp hv_eq with hv1 | hv3
  · have hu : u = 1 := by linarith
    have hv : v = 1 := by linarith
    have hr : r = 3 := by linarith
    have ht : t = 3 := by linarith
    rw [hu, hv, hr, ht] at hmix; norm_num at hmix
  · have hu : u = 1 := by linarith
    have hv : v = 3 := by linarith
    have hr : r = 3 := by linarith
    have ht : t = 1 := by linarith
    rw [hu, hv, hr, ht] at hmix; norm_num at hmix
  · have hu : u = 3 := by linarith
    have hv : v = 1 := by linarith
    have hr : r = 1 := by linarith
    have ht : t = 3 := by linarith
    rw [hu, hv, hr, ht] at hmix; norm_num at hmix
  · have hu : u = 3 := by linarith
    have hv : v = 3 := by linarith
    have hr : r = 1 := by linarith
    have ht : t = 1 := by linarith
    rw [hu, hv, hr, ht] at hmix; norm_num at hmix

/-- Theorem 4.4, 4.5 & Corollary 4.6: For every `n ≥ 3`, there exists a probability measure `μ`
on `[0, ∞)^n` in `MVPH_n \ MPH*_n`. -/
private lemma mvph_strict_separation (n : ℕ) (hn : 3 ≤ n) :
    ∃ μ : Measure (Fin n → ℝ),
      IsProbabilityMeasure μ ∧
      (∀ᵐ x ∂μ, ∀ j : Fin n, 0 ≤ x j) ∧
      (∀ a : Fin n → ℝ, (∀ j, 0 ≤ a j) → a ≠ 0 →
        IsUnivariatePHTransform (fun u => laplaceTransform μ (u • a))) ∧
      ¬ HasMPHRep (laplaceTransform μ) := by
  -- Construct `μ` as pushforward of `(N(0,1)^2 × N(0,1)^2) × Exp(1)^(n-3)` under the Wishart trace map!
  let G2 : Measure (ℝ × ℝ) := stdGaussMeasure.prod stdGaussMeasure
  have : IsProbabilityMeasure stdGaussMeasure := isProbabilityMeasure_stdGauss
  have : IsProbabilityMeasure expOneMeasure := isProbabilityMeasure_expOne
  let G4 : Measure ((ℝ × ℝ) × (ℝ × ℝ)) := G2.prod G2
  let E_tail : Measure (Fin (n - 3) → ℝ) := Measure.pi fun _ : Fin (n - 3) => expOneMeasure
  let Ω := ((ℝ × ℝ) × (ℝ × ℝ)) × (Fin (n - 3) → ℝ)
  let base : Measure Ω := G4.prod E_tail
  let Φ : Ω → (Fin n → ℝ) := fun ω j =>
    let u₁ := ω.1.1.1; let v₁ := ω.1.1.2; let u₂ := ω.1.2.1; let v₂ := ω.1.2.2
    if h0 : j.val = 0 then (u₁ ^ 2 + v₁ ^ 2 + u₂ ^ 2 + v₂ ^ 2) / 2
    else if h1 : j.val = 1 then (2 * u₁ ^ 2 + 2 * u₁ * v₁ + 2 * v₁ ^ 2 + 2 * u₂ ^ 2 + 2 * u₂ * v₂ + 2 * v₂ ^ 2) / 2
    else if h2 : j.val = 2 then (3 * u₁ ^ 2 + v₁ ^ 2 + 3 * u₂ ^ 2 + v₂ ^ 2) / 2
    else ω.2 ⟨j.val - 3, by omega⟩
  have hΦ_meas : Measurable Φ := by
    apply measurable_pi_lambda
    intro j
    dsimp only [Φ, Ω]
    split_ifs <;> fun_prop
  let μ : Measure (Fin n → ℝ) := base.map Φ
  have hμ_prob : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hΦ_meas.aemeasurable
  have hμ_nonneg : ∀ᵐ x ∂μ, ∀ j : Fin n, 0 ≤ x j := by
    have hset : MeasurableSet { x : Fin n → ℝ | ∀ j : Fin n, 0 ≤ x j } := by
      have : { x : Fin n → ℝ | ∀ j : Fin n, 0 ≤ x j } = ⋂ j : Fin n, { x : Fin n → ℝ | 0 ≤ x j } := by
        ext x; simp
      rw [this]
      exact MeasurableSet.iInter fun j => (isClosed_le continuous_const (continuous_apply j)).measurableSet
    dsimp only [μ]
    rw [MeasureTheory.ae_map_iff hΦ_meas.aemeasurable hset]
    have hE_nn : ∀ᵐ e ∂E_tail, ∀ k : Fin (n - 3), 0 ≤ e k := by
      rw [MeasureTheory.ae_all_iff]
      intro k
      have h1 : ∀ᵐ x ∂(E_tail.map fun e => e k), 0 ≤ x := by
        have hproj : E_tail.map (fun e : Fin (n - 3) → ℝ => e k) = expOneMeasure :=
          (MeasureTheory.measurePreserving_eval (fun _ : Fin (n - 3) => expOneMeasure) k).map_eq
        rw [hproj]; exact expOne_ae_nonneg
      exact (MeasureTheory.ae_map_iff (measurable_pi_apply k).aemeasurable
        (isClosed_le continuous_const continuous_id).measurableSet).mp h1
    have hbase_nn : ∀ᵐ ω ∂base, ∀ k : Fin (n - 3), 0 ≤ ω.2 k :=
      MeasureTheory.Measure.QuasiMeasurePreserving.ae MeasureTheory.Measure.quasiMeasurePreserving_snd hE_nn
    filter_upwards [hbase_nn] with ω hω j
    dsimp only [Φ]
    split_ifs with h0 h1 h2
    · positivity
    · have : 2 * ω.1.1.1 ^ 2 + 2 * ω.1.1.1 * ω.1.1.2 + 2 * ω.1.1.2 ^ 2 +
          2 * ω.1.2.1 ^ 2 + 2 * ω.1.2.1 * ω.1.2.2 + 2 * ω.1.2.2 ^ 2 =
          (ω.1.1.1 + ω.1.1.2) ^ 2 + ω.1.1.1 ^ 2 + ω.1.1.2 ^ 2 +
          (ω.1.2.1 + ω.1.2.2) ^ 2 + ω.1.2.1 ^ 2 + ω.1.2.2 ^ 2 := by ring
      rw [this]; positivity
    · positivity
    · exact hω ⟨j.val - 3, by omega⟩
  -- Compute exact Laplace transform of `μ` on `[0, ∞)^n`:
  let Q3 : (Fin 3 → ℝ) → ℝ := fun s =>
    (1 + s 0 + 2 * s 1 + 3 * s 2) * (1 + s 0 + 2 * s 1 + s 2) - s 1 ^ 2
  have hQ3_pos : ∀ s0 s1 s2 : ℝ, 0 ≤ s0 → 0 ≤ s1 → 0 ≤ s2 → 0 < Q3 ![s0, s1, s2] := by
    intro s0 s1 s2 h0 h1 h2
    simp only [Q3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    nlinarith
  have hL_exact : ∀ s : Fin n → ℝ, (∀ j, 0 ≤ s j) →
      laplaceTransform μ s =
        (Q3 ![s ⟨0, by omega⟩, s ⟨1, by omega⟩, s ⟨2, by omega⟩])⁻¹ *
        ∏ k : Fin (n - 3), (1 + s ⟨k.val + 3, by omega⟩)⁻¹ := by
    intro s hs
    have hs0 : 0 ≤ s ⟨0, by omega⟩ := hs _
    have hs1 : 0 ≤ s ⟨1, by omega⟩ := hs _
    have hs2 : 0 ≤ s ⟨2, by omega⟩ := hs _
    rw [laplaceTransform, MeasureTheory.integral_map hΦ_meas.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]
    -- Split `exp(-⟨s, Φ ω⟩)` into `f_G(ω.1.1) * f_G(ω.1.2) * ∏_k exp(-s_{k+3} * ω.2 k)`!
    let a0 := 1 + s ⟨0, by omega⟩ + 2 * s ⟨1, by omega⟩ + 3 * s ⟨2, by omega⟩
    let b0 := s ⟨1, by omega⟩
    let c0 := 1 + s ⟨0, by omega⟩ + 2 * s ⟨1, by omega⟩ + s ⟨2, by omega⟩
    let fG : ℝ × ℝ → ℝ := fun p =>
      Real.exp (-(((s ⟨0, by omega⟩ + 2 * s ⟨1, by omega⟩ + 3 * s ⟨2, by omega⟩) * p.1 ^ 2 +
        2 * s ⟨1, by omega⟩ * p.1 * p.2 +
        (s ⟨0, by omega⟩ + 2 * s ⟨1, by omega⟩ + s ⟨2, by omega⟩) * p.2 ^ 2) / 2))
    let fE : (Fin (n - 3) → ℝ) → ℝ := fun e => ∏ k : Fin (n - 3), Real.exp (-(s ⟨k.val + 3, by omega⟩ * e k))
    have hsplit : ∀ ω : Ω, Real.exp (-(∑ j : Fin n, s j * Φ ω j)) =
        (fG ω.1.1 * fG ω.1.2) * fE ω.2 := by
      intro ω
      -- Split `∑ j : Fin n` into `j = 0, 1, 2` and `j ≥ 3`!
      let j0 : Fin n := ⟨0, by omega⟩
      let j1 : Fin n := ⟨1, by omega⟩
      let j2 : Fin n := ⟨2, by omega⟩
      have h01 : j0 ≠ j1 := by intro h; have := congrArg Fin.val h; simp [j0, j1] at this
      have h02 : j0 ≠ j2 := by intro h; have := congrArg Fin.val h; simp [j0, j2] at this
      have h12 : j1 ≠ j2 := by intro h; have := congrArg Fin.val h; simp [j1, j2] at this
      have hsum_split : ∑ j : Fin n, s j * Φ ω j =
          s j0 * Φ ω j0 + s j1 * Φ ω j1 + s j2 * Φ ω j2 +
          ∑ k : Fin (n - 3), s ⟨k.val + 3, by omega⟩ * ω.2 k := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j0),
            ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ j1⟩),
            ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨h12.symm, Finset.mem_erase.mpr ⟨h02.symm, Finset.mem_univ j2⟩⟩)]
        have htail : ∑ j ∈ ((Finset.univ.erase j0).erase j1).erase j2, s j * Φ ω j =
            ∑ k : Fin (n - 3), s ⟨k.val + 3, by omega⟩ * ω.2 k := by
          refine Finset.sum_bij (fun j hj => ⟨j.val - 3, by
            have hj2 : j ≠ j2 := (Finset.mem_erase.mp hj).1
            have hj1 : j ≠ j1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
            have hj0 : j ≠ j0 := (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).2).1
            have : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
            have : j.val ≠ 1 := fun h => hj1 (Fin.ext h)
            have : j.val ≠ 2 := fun h => hj2 (Fin.ext h)
            have := j.isLt; omega⟩) ?_ ?_ ?_ ?_
          · intro _ _; exact Finset.mem_univ _
          · intro x hx y hy hxy
            have hx2 : x ≠ j2 := (Finset.mem_erase.mp hx).1
            have hx1 : x ≠ j1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
            have hx0 : x ≠ j0 := (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).2).1
            have hy2 : y ≠ j2 := (Finset.mem_erase.mp hy).1
            have hy1 : y ≠ j1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hy).2).1
            have hy0 : y ≠ j0 := (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hy).2).2).1
            have hxv : 3 ≤ x.val := by
              have : x.val ≠ 0 := fun h => hx0 (Fin.ext h)
              have : x.val ≠ 1 := fun h => hx1 (Fin.ext h)
              have : x.val ≠ 2 := fun h => hx2 (Fin.ext h)
              omega
            have hyv : 3 ≤ y.val := by
              have : y.val ≠ 0 := fun h => hy0 (Fin.ext h)
              have : y.val ≠ 1 := fun h => hy1 (Fin.ext h)
              have : y.val ≠ 2 := fun h => hy2 (Fin.ext h)
              omega
            have := congrArg Fin.val hxy; dsimp only at this; exact Fin.ext (by omega)
          · intro k _
            refine ⟨⟨k.val + 3, by omega⟩, ?_, Fin.ext (by dsimp only; omega)⟩
            simp only [Finset.mem_erase, Finset.mem_univ, and_true]
            refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
              { have := congrArg Fin.val h; simp [j0, j1, j2] at this }
          · intro x hx
            have hx2 : x ≠ j2 := (Finset.mem_erase.mp hx).1
            have hx1 : x ≠ j1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
            have hx0 : x ≠ j0 := (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).2).1
            have hxv0 : x.val ≠ 0 := fun h => hx0 (Fin.ext h)
            have hxv1 : x.val ≠ 1 := fun h => hx1 (Fin.ext h)
            have hxv2 : x.val ≠ 2 := fun h => hx2 (Fin.ext h)
            have hx_eq : (⟨x.val - 3 + 3, by omega⟩ : Fin n) = x := Fin.ext (by dsimp only; omega)
            rw [hx_eq]
            simp only [Φ, dif_neg hxv0, dif_neg hxv1, dif_neg hxv2]
        rw [htail]; ring
      rw [hsum_split]
      dsimp only [fG, fE]
      rw [← Real.exp_sum, ← Real.exp_add, ← Real.exp_add]
      congr 1
      simp only [Φ, j0, j1, j2, ↓reduceDIte, show (1 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 0 by decide,
        show (2 : ℕ) ≠ 1 by decide, Finset.sum_neg_distrib]
      ring
    simp_rw [hsplit]
    dsimp only [base, G4]
    rw [MeasureTheory.integral_prod_mul (f := fun p : (ℝ × ℝ) × (ℝ × ℝ) => fG p.1 * fG p.2) (g := fE),
        MeasureTheory.integral_prod_mul]
    -- Compute `∫ p, fG p ∂G2 = (Real.sqrt (Q3 ![s 0, s 1, s 2]))⁻¹`!
    have hG2_int : ∫ p : ℝ × ℝ, fG p ∂G2 = (Real.sqrt (Q3 ![s ⟨0, by omega⟩, s ⟨1, by omega⟩, s ⟨2, by omega⟩]))⁻¹ := by
      have hfG_int : Integrable fG G2 := by
        refine Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 1 (Filter.Eventually.of_forall fun p => ?_)
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        refine Real.exp_le_one_iff.mpr ?_
        have hq : 0 ≤ (s ⟨0, by omega⟩ + 2 * s ⟨1, by omega⟩ + 3 * s ⟨2, by omega⟩) * p.1 ^ 2 +
            2 * s ⟨1, by omega⟩ * p.1 * p.2 +
            (s ⟨0, by omega⟩ + 2 * s ⟨1, by omega⟩ + s ⟨2, by omega⟩) * p.2 ^ 2 := by
          have : (s ⟨0, by omega⟩ + 2 * s ⟨1, by omega⟩ + 3 * s ⟨2, by omega⟩) * p.1 ^ 2 +
              2 * s ⟨1, by omega⟩ * p.1 * p.2 +
              (s ⟨0, by omega⟩ + 2 * s ⟨1, by omega⟩ + s ⟨2, by omega⟩) * p.2 ^ 2 =
              s ⟨0, by omega⟩ * (p.1 ^ 2 + p.2 ^ 2) +
              s ⟨1, by omega⟩ * ((p.1 + p.2) ^ 2 + p.1 ^ 2 + p.2 ^ 2) +
              s ⟨2, by omega⟩ * (3 * p.1 ^ 2 + p.2 ^ 2) := by ring
          rw [this]; positivity
        linarith
      dsimp only [G2]
      rw [MeasureTheory.integral_prod fG hfG_int]
      have hdens_meas : Measurable fun x : ℝ => ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2))) :=
        Measurable.ennreal_ofReal (by fun_prop)
      have hdens_lt : ∀ᵐ x ∂volume, ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2))) < ⊤ :=
        Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
      have hdens_nn : ∀ x : ℝ, 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2)) := fun x => by positivity
      have hpi_pos : 0 < 2 * Real.pi := by positivity
      have hinner_eq : ∀ u : ℝ,
          ∫ v : ℝ, fG (u, v) ∂stdGaussMeasure =
            ∫ v : ℝ, ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(v ^ 2 / 2))) * fG (u, v) := fun u => by
        rw [stdGaussMeasure, integral_withDensity_eq_integral_toReal_smul hdens_meas hdens_lt]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
        dsimp only; rw [ENNReal.toReal_ofReal (hdens_nn v), smul_eq_mul]
      simp_rw [hinner_eq]
      rw [stdGaussMeasure, integral_withDensity_eq_integral_toReal_smul hdens_meas hdens_lt]
      have houter_eq : (fun u : ℝ =>
          (ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(u ^ 2 / 2)))).toReal •
            ∫ v : ℝ, ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(v ^ 2 / 2))) * fG (u, v)) =
          fun u : ℝ => ∫ v : ℝ, (2 * Real.pi)⁻¹ * Real.exp (-((a0 * u ^ 2 + 2 * b0 * u * v + c0 * v ^ 2) / 2)) := by
        ext u
        rw [ENNReal.toReal_ofReal (hdens_nn u), smul_eq_mul, ← MeasureTheory.integral_const_mul]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
        dsimp only [fG, a0, b0, c0]
        rw [show (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(u ^ 2 / 2)) *
              (((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(v ^ 2 / 2))) *
                Real.exp (-(((s ⟨0, by omega⟩ + 2 * s ⟨1, by omega⟩ + 3 * s ⟨2, by omega⟩) * u ^ 2 +
                  2 * s ⟨1, by omega⟩ * u * v +
                  (s ⟨0, by omega⟩ + 2 * s ⟨1, by omega⟩ + s ⟨2, by omega⟩) * v ^ 2) / 2))) =
              (Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi))⁻¹ *
              (Real.exp (-(u ^ 2 / 2)) * Real.exp (-(v ^ 2 / 2)) *
                Real.exp (-(((s ⟨0, by omega⟩ + 2 * s ⟨1, by omega⟩ + 3 * s ⟨2, by omega⟩) * u ^ 2 +
                  2 * s ⟨1, by omega⟩ * u * v +
                  (s ⟨0, by omega⟩ + 2 * s ⟨1, by omega⟩ + s ⟨2, by omega⟩) * v ^ 2) / 2))) by ring,
            Real.mul_self_sqrt (le_of_lt hpi_pos), ← Real.exp_add, ← Real.exp_add]
        congr 2; ring
      rw [houter_eq]
      have hdet_pos : 0 < a0 * c0 - b0 ^ 2 := by
        simpa [Q3, a0, b0, c0] using hQ3_pos _ _ _ hs0 hs1 hs2
      have ha0_pos : 0 < a0 := by dsimp [a0]; linarith
      have hc0_pos : 0 < c0 := by dsimp [c0]; linarith
      have hint_2d : Integrable
          (fun p : ℝ × ℝ => (2 * Real.pi)⁻¹ * Real.exp (-((a0 * p.1 ^ 2 + 2 * b0 * p.1 * p.2 + c0 * p.2 ^ 2) / 2)))
          (volume.prod volume) := by
        refine (MeasureTheory.integrable_prod_iff' (Continuous.aestronglyMeasurable (by fun_prop))).mpr ⟨?_, ?_⟩
        · refine Filter.Eventually.of_forall fun v => ?_
          have hdec : ∀ u : ℝ, a0 * u ^ 2 + 2 * b0 * u * v + c0 * v ^ 2 =
              a0 * (u + (b0 / a0) * v) ^ 2 + ((a0 * c0 - b0 ^ 2) / a0) * v ^ 2 := fun u => by
            field_simp [ne_of_gt ha0_pos]; ring
          have heq : (fun u : ℝ => (2 * Real.pi)⁻¹ * Real.exp (-((a0 * u ^ 2 + 2 * b0 * u * v + c0 * v ^ 2) / 2))) =
              fun u => ((2 * Real.pi)⁻¹ * Real.exp (-(((a0 * c0 - b0 ^ 2) / a0) * v ^ 2 / 2))) *
                Real.exp (-(a0 / 2) * (u + (b0 / a0) * v) ^ 2) := by
            ext u; rw [hdec u, mul_assoc, ← Real.exp_add]; congr 2; ring
          rw [heq]
          exact ((integrable_exp_neg_mul_sq (by linarith : 0 < a0 / 2)).comp_add_right _).const_mul _
        · simp only [Real.norm_eq_abs, abs_of_pos (mul_pos (inv_pos.mpr hpi_pos) (Real.exp_pos _))]
          have heq : (fun v : ℝ => ∫ u : ℝ, (2 * Real.pi)⁻¹ * Real.exp (-((a0 * u ^ 2 + 2 * b0 * u * v + c0 * v ^ 2) / 2))) =
              fun v => ((2 * Real.pi)⁻¹ * Real.sqrt (2 * Real.pi / a0)) *
                Real.exp (-(((a0 * c0 - b0 ^ 2) / a0) / 2) * v ^ 2) := by
            ext v
            have hdec : ∀ u : ℝ, a0 * u ^ 2 + 2 * b0 * u * v + c0 * v ^ 2 =
                a0 * (u + (b0 / a0) * v) ^ 2 + ((a0 * c0 - b0 ^ 2) / a0) * v ^ 2 := fun u => by
              field_simp [ne_of_gt ha0_pos]; ring
            have heq' : (fun u : ℝ => (2 * Real.pi)⁻¹ * Real.exp (-((a0 * u ^ 2 + 2 * b0 * u * v + c0 * v ^ 2) / 2))) =
                fun u => ((2 * Real.pi)⁻¹ * Real.exp (-(((a0 * c0 - b0 ^ 2) / a0) * v ^ 2 / 2))) *
                  Real.exp (-(a0 * (u + (b0 / a0) * v) ^ 2 / 2)) := by
              ext u; rw [hdec u, mul_assoc, ← Real.exp_add]; congr 2; ring
            have hshift := MeasureTheory.integral_add_right_eq_self (μ := volume)
              (fun u : ℝ => Real.exp (-(a0 * u ^ 2 / 2))) ((b0 / a0) * v)
            rw [heq', MeasureTheory.integral_const_mul, hshift, integral_gaussian_half ha0_pos]
            have hexp : -(((a0 * c0 - b0 ^ 2) / a0) * v ^ 2 / 2) = -(((a0 * c0 - b0 ^ 2) / a0) / 2) * v ^ 2 := by ring
            rw [hexp]; ring
          rw [heq]
          exact (integrable_exp_neg_mul_sq (div_pos (div_pos hdet_pos ha0_pos) two_pos)).const_mul _
      rw [← MeasureTheory.integral_prod _ hint_2d, MeasureTheory.integral_const_mul,
          integral_gaussian_2d ha0_pos hdet_pos]
      have hpi : 2 * Real.pi ≠ 0 := ne_of_gt hpi_pos
      have hdet_eq : a0 * c0 - b0 ^ 2 = Q3 ![s ⟨0, by omega⟩, s ⟨1, by omega⟩, s ⟨2, by omega⟩] := by
        simp [Q3, a0, b0, c0]
      rw [hdet_eq]; field_simp [hpi]
    -- Compute `∫ e, fE e ∂E_tail = ∏ k, (1 + s_{k+3})⁻¹` via `integral_fintype_prod_eq_prod`!
    have hE_int : ∫ e : Fin (n - 3) → ℝ, fE e ∂E_tail =
        ∏ k : Fin (n - 3), (1 + s ⟨k.val + 3, by omega⟩)⁻¹ := by
      dsimp only [fE, E_tail]
      exact (MeasureTheory.integral_fintype_prod_eq_prod
          (μ := fun _ : Fin (n - 3) => expOneMeasure)
          (fun k x => Real.exp (-(s ⟨k.val + 3, by omega⟩ * x)))).trans
        (Finset.prod_congr rfl fun k _ => integral_expOne_laplace (hs _))
    rw [hG2_int, hE_int, ← mul_inv, Real.mul_self_sqrt (le_of_lt (hQ3_pos _ _ _ hs0 hs1 hs2))]
  refine ⟨μ, hμ_prob, hμ_nonneg, ?_, ?_⟩
  · -- Part A: Every positive projection `⟨a, X⟩` (`a ≥ 0, a ≠ 0`) is univariate PH!
    intro a ha ha_ne
    -- Factor `Q3(u a₀, u a₁, u a₂) = (1 + u λ₁)(1 + u λ₂)` where `λ₁, λ₂ ≥ 0` are eigenvalues of `H(a)`!
    let a0 := a ⟨0, by omega⟩
    let a1 := a ⟨1, by omega⟩
    let a2 := a ⟨2, by omega⟩
    have ha0 : 0 ≤ a0 := ha _; have ha1 : 0 ≤ a1 := ha _; have ha2 : 0 ≤ a2 := ha _
    let α := a0 + 2 * a1 + 3 * a2
    let β := a0 + 2 * a1 + a2
    let disc := (α - β) ^ 2 + 4 * a1 ^ 2
    have hdisc : 0 ≤ disc := by dsimp [disc]; positivity
    let lam1 := (α + β + Real.sqrt disc) / 2
    let lam2 := (α + β - Real.sqrt disc) / 2
    have hsum_lam : lam1 + lam2 = α + β := by dsimp [lam1, lam2]; ring
    have hprod_lam : lam1 * lam2 = α * β - a1 ^ 2 := by
      dsimp [lam1, lam2]
      have hsq : Real.sqrt disc ^ 2 = disc := Real.sq_sqrt hdisc
      have : ((α + β + Real.sqrt disc) / 2) * ((α + β - Real.sqrt disc) / 2) =
          ((α + β) ^ 2 - Real.sqrt disc ^ 2) / 4 := by ring
      rw [this, hsq]; dsimp [disc]; ring
    have hdet_nn : 0 ≤ α * β - a1 ^ 2 := by dsimp [α, β]; nlinarith
    have hlam1_nn : 0 ≤ lam1 := by dsimp [lam1, α, β]; linarith [Real.sqrt_nonneg disc]
    have hlam2_nn : 0 ≤ lam2 := by
      by_cases h0 : lam1 = 0
      · have : α + β = 0 := by dsimp [lam1] at h0; linarith [Real.sqrt_nonneg disc]
        linarith [hsum_lam]
      · have hpos : 0 < lam1 := lt_of_le_of_ne hlam1_nn (Ne.symm h0)
        nlinarith [hprod_lam, hdet_nn]
    have hQ3_fac : ∀ u : ℝ, Q3 ![u * a0, u * a1, u * a2] = (1 + u * lam1) * (1 + u * lam2) := fun u => by
      simp only [Q3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      have : (1 + u * lam1) * (1 + u * lam2) = 1 + u * (lam1 + lam2) + u ^ 2 * (lam1 * lam2) := by ring
      rw [this, hsum_lam, hprod_lam]; dsimp [α, β]; ring
    -- Collect the positive parameters from `[lam1, lam2] ++ [a ⟨k+3, _⟩ | k : Fin (n-3)]`!
    let allR : Fin (2 + (n - 3)) → ℝ := fun idx =>
      if h0 : idx.val = 0 then lam1
      else if h1 : idx.val = 1 then lam2
      else a ⟨idx.val + 1, by omega⟩
    have hallR_nn : ∀ idx, 0 ≤ allR idx := fun idx => by
      dsimp [allR]; split_ifs; exact hlam1_nn; exact hlam2_nn; exact ha _
    let posSet : Finset (Fin (2 + (n - 3))) := Finset.univ.filter fun idx => 0 < allR idx
    have hpos_ne : posSet.Nonempty := by
      have hex : ∃ j : Fin n, 0 < a j := by
        by_contra hall; push Not at hall
        exact ha_ne (funext fun j => le_antisymm (hall j) (ha j))
      obtain ⟨j, hj⟩ := hex
      by_cases hj3 : j.val < 3
      · refine ⟨⟨0, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        simp only [allR, ↓reduceDIte]
        have hαβ : 0 < α + β := by
          dsimp [α, β, a0, a1, a2]
          have : j = ⟨0, by omega⟩ ∨ j = ⟨1, by omega⟩ ∨ j = ⟨2, by omega⟩ := by
            have := j.isLt; interval_cases hv : j.val <;> [left; (right; left); (right; right)] <;> exact Fin.ext hv
          rcases this with h0 | h1 | h2
          · rw [h0] at hj; linarith
          · rw [h1] at hj; linarith
          · rw [h2] at hj; linarith
        dsimp [lam1]; linarith [Real.sqrt_nonneg disc]
      · refine ⟨⟨j.val - 1, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        simp only [allR, show ¬ (j.val - 1 = 0) by omega, ↓reduceDIte, show ¬ (j.val - 1 = 1) by omega]
        have hjeq : (⟨j.val - 1 + 1, by omega⟩ : Fin n) = j := Fin.ext (by dsimp only; omega)
        rw [hjeq]; exact hj
    let ePos : Fin posSet.card ≃ posSet := (Fintype.equivFinOfCardEq (Fintype.card_coe posSet)).symm
    have hcard_pos : 1 ≤ posSet.card := Finset.one_le_card.mpr hpos_ne
    have hPH := prod_exp_isUnivariatePH hcard_pos (fun k => allR (ePos k).val)
      (fun k => (Finset.mem_filter.mp (ePos k).prop).2)
    -- Show `laplaceTransform μ (u • a) = ∏ k : Fin posSet.card, (1 + u * allR (ePos k))⁻¹` for all `u ≥ 0`!
    rcases hPH with ⟨m, hm, αp, Tp, hTp, hαp_nn, hαp_sum, hTp_eq⟩
    refine ⟨m, hm, αp, Tp, hTp, hαp_nn, hαp_sum, fun u hu => ?_⟩
    obtain ⟨hu_det, hu_val⟩ := hTp_eq u hu
    refine ⟨hu_det, ?_⟩
    dsimp only at hu_val ⊢
    rw [← hu_val, hL_exact (u • a) (fun j => mul_nonneg hu (ha j))]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hQ3_fac u, mul_inv]
    -- Show the full product over `Fin (2 + (n - 3))` equals the product over `posSet` (zero entries give `(1 + 0)⁻¹ = 1`)!
    have hprod_all : (1 + u * lam1)⁻¹ * (1 + u * lam2)⁻¹ * ∏ k : Fin (n - 3), (1 + u * a ⟨k.val + 3, by omega⟩)⁻¹ =
        ∏ idx : Fin (2 + (n - 3)), (1 + u * allR idx)⁻¹ := by
      let i0 : Fin (2 + (n - 3)) := ⟨0, by omega⟩
      let i1 : Fin (2 + (n - 3)) := ⟨1, by omega⟩
      have h01 : i0 ≠ i1 := by intro h; have := congrArg Fin.val h; simp [i0, i1] at this
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i0),
          ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ i1⟩), ← mul_assoc]
      refine congrArg₂ (· * ·) (by simp [allR, i0, i1]) ?_
      refine Finset.prod_bij (fun k _ => ⟨k.val + 2, by omega⟩) ?_ ?_ ?_ ?_
      · intro k _; simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        refine ⟨fun h => ?_, fun h => ?_⟩ <;> { have := congrArg Fin.val h; simp [i0, i1] at this }
      · intro k₁ _ k₂ _ h; have := congrArg (Fin.val : Fin (2 + (n - 3)) → ℕ) h; dsimp only at this; exact Fin.ext (by omega)
      · intro idx hidx
        have h1 : idx ≠ i1 := (Finset.mem_erase.mp hidx).1
        have h0 : idx ≠ i0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hidx).2).1
        have hv0 : idx.val ≠ 0 := fun h => h0 (Fin.ext h)
        have hv1 : idx.val ≠ 1 := fun h => h1 (Fin.ext h)
        exact ⟨⟨idx.val - 2, by omega⟩, Finset.mem_univ _, Fin.ext (by dsimp only; omega)⟩
      · intro k _
        simp only [allR, show ¬ (k.val + 2 = 0) by omega, ↓reduceDIte, show ¬ (k.val + 2 = 1) by omega]
    rw [hprod_all]
    have hprod_pos : ∏ idx : Fin (2 + (n - 3)), (1 + u * allR idx)⁻¹ =
        ∏ idx ∈ posSet, (1 + u * allR idx)⁻¹ := by
      rw [← Finset.prod_subset (Finset.subset_univ posSet)]
      intro idx _ hnot
      have hle : allR idx ≤ 0 := not_lt.mp (fun h => hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
      have h0 : allR idx = 0 := le_antisymm hle (hallR_nn idx)
      simp [h0]
    rw [hprod_pos, ← Finset.prod_coe_sort posSet (fun idx => (1 + u * allR idx)⁻¹)]
    exact (Equiv.prod_comp ePos (fun x : posSet => (1 + u * allR x.val)⁻¹)).symm
  · -- Part B: `¬ HasMPHRep (laplaceTransform μ)` via Theorem 4.2 + irreducibility of `Q₂`!
    rintro ⟨m, hm, α, T, K, hT, hα_nn, hα_sum, hK_nn, hK_rep⟩
    -- Restrict to the first 3 variables by setting `s_j = 0` for `j ≥ 3`!
    let K3 : Matrix (Fin m) (Fin 3) ℝ := Matrix.of fun i j => K i ⟨j.val, by omega⟩
    let Qp : MvPolynomial (Fin 3) ℝ :=
      (1 + MvPolynomial.X 0 + MvPolynomial.C 2 * MvPolynomial.X 1 + MvPolynomial.C 3 * MvPolynomial.X 2) *
      (1 + MvPolynomial.X 0 + MvPolynomial.C 2 * MvPolynomial.X 1 + MvPolynomial.X 2) -
      MvPolynomial.X 1 ^ 2
    have hQp_eval : ∀ s : Fin 3 → ℝ, MvPolynomial.eval s Qp = Q3 s := fun s => by
      simp [Qp, Q3]
    have hQp_ne : Qp ≠ 0 := fun h => by
      have h0 := congrArg (MvPolynomial.eval 0) h
      rw [hQp_eval 0, map_zero] at h0
      simp [Q3] at h0
    have hrep3 : ∃ (m : ℕ) (_ : 1 ≤ m) (α : Fin m → ℝ) (T : Matrix (Fin m) (Fin m) ℝ)
        (K3 : Matrix (Fin m) (Fin 3) ℝ),
        IsTransientSubgenerator T ∧
        (∀ i, 0 ≤ α i) ∧ (∑ i, α i ≤ 1) ∧ (∀ i j, 0 ≤ K3 i j) ∧
        ∀ s : Fin 3 → ℝ, (∀ j, 0 ≤ s j) →
          MvPolynomial.eval s Qp ≠ 0 ∧
          IsUnit (-T + Matrix.diagonal (K3.mulVec s)).det ∧
          MvPolynomial.eval s (1 : MvPolynomial (Fin 3) ℝ) / MvPolynomial.eval s Qp =
            kulkarniEval (1 - ∑ i, α i) α T K3 (-(T.mulVec 1)) s := by
      refine ⟨m, hm, α, T, K3, hT, hα_nn, hα_sum, fun i j => hK_nn i ⟨j.val, by omega⟩, fun s hs => ?_⟩
      let sN : Fin n → ℝ := fun j => if h : j.val < 3 then s ⟨j.val, h⟩ else 0
      have hsN : ∀ j, 0 ≤ sN j := fun j => by dsimp [sN]; split_ifs; exact hs _; exact le_rfl
      obtain ⟨hu, hK_eq⟩ := hK_rep sN hsN
      have hK3_mv : K3.mulVec s = K.mulVec sN := by
        ext i
        simp only [Matrix.mulVec, dotProduct, K3, Matrix.of_apply, sN]
        symm
        have hsub : ∑ j : Fin n, K i j * (if h : j.val < 3 then s ⟨j.val, h⟩ else 0) =
            ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < 3),
              K i j * (if h : j.val < 3 then s ⟨j.val, h⟩ else 0) := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
        rw [hsub]
        refine Finset.sum_bij (fun j hj => ⟨j.val, (Finset.mem_filter.mp hj).2⟩) ?_ ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro j₁ _ j₂ _ h; have hv : j₁.val = j₂.val := congrArg (Fin.val : Fin 3 → ℕ) h; exact Fin.ext hv
        · intro j _; exact ⟨⟨j.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt⟩, Fin.ext rfl⟩
        · intro j hj; simp [(Finset.mem_filter.mp hj).2]
      have hQp_pos : 0 < MvPolynomial.eval s Qp := by
        rw [hQp_eval s]
        have heq : s = ![s 0, s 1, s 2] := by ext j; fin_cases j <;> rfl
        rw [heq]; exact hQ3_pos _ _ _ (hs 0) (hs 1) (hs 2)
      refine ⟨ne_of_gt hQp_pos, hK3_mv.symm ▸ hu, ?_⟩
      have hL3 := hL_exact sN hsN
      have htail1 : ∏ k : Fin (n - 3), (1 + sN ⟨k.val + 3, by omega⟩)⁻¹ = 1 :=
        Finset.prod_eq_one fun k _ => by simp [sN, show ¬ (k.val + 3 < 3) by omega]
      have hsN3 : ![sN ⟨0, by omega⟩, sN ⟨1, by omega⟩, sN ⟨2, by omega⟩] = s := by
        ext j; fin_cases j <;> simp [sN]
      rw [htail1, mul_one, hsN3] at hL3
      rw [hL3] at hK_eq
      rw [map_one, one_div, hQp_eval s, hK_eq]
      dsimp only [kulkarniEval]; rw [hK3_mv]
    -- Apply Theorem 4.2 (`mph_factorization`) to `(P = 1, Q = Qp)`!
    obtain ⟨c, hc0, c₀, hc₀_pos, ν, lam, _, hfac⟩ :=
      mph_factorization 1 Qp hQp_ne (fun D hD1 _ => isUnit_of_dvd_one hD1) hrep3
    -- Compute `leadingHomog Qp = X₀² + 4 X₀ X₁ + 4 X₀ X₂ + 3 X₁² + 8 X₁ X₂ + 3 X₂²`!
    let Q2 : MvPolynomial (Fin 3) ℝ :=
      MvPolynomial.X 0 ^ 2 + MvPolynomial.C 4 * MvPolynomial.X 0 * MvPolynomial.X 1 +
      MvPolynomial.C 4 * MvPolynomial.X 0 * MvPolynomial.X 2 +
      MvPolynomial.C 3 * MvPolynomial.X 1 ^ 2 +
      MvPolynomial.C 8 * MvPolynomial.X 1 * MvPolynomial.X 2 +
      MvPolynomial.C 3 * MvPolynomial.X 2 ^ 2
    let Q1 : MvPolynomial (Fin 3) ℝ :=
      1 + MvPolynomial.C 2 * MvPolynomial.X 0 + MvPolynomial.C 4 * MvPolynomial.X 1 + MvPolynomial.C 4 * MvPolynomial.X 2
    have hQp_split : Qp = Q2 + Q1 := by dsimp [Qp, Q2, Q1]; simp only [map_ofNat]; ring
    have hQ2_hom : Q2.IsHomogeneous 2 := by
      dsimp [Q2]
      have hX : ∀ i : Fin 3, (MvPolynomial.X i : MvPolynomial (Fin 3) ℝ).IsHomogeneous 1 :=
        fun i => MvPolynomial.isHomogeneous_X ℝ i
      have hC : ∀ r : ℝ, (MvPolynomial.C r : MvPolynomial (Fin 3) ℝ).IsHomogeneous 0 :=
        fun r => MvPolynomial.isHomogeneous_C (Fin 3) r
      have ht1 : (MvPolynomial.X (0 : Fin 3) ^ 2 : MvPolynomial (Fin 3) ℝ).IsHomogeneous 2 := by
        simpa [sq] using (hX 0).mul (hX 0)
      have ht2 : (MvPolynomial.C 4 * MvPolynomial.X (0 : Fin 3) * MvPolynomial.X (1 : Fin 3) : MvPolynomial (Fin 3) ℝ).IsHomogeneous 2 := by
        simpa using ((hC 4).mul (hX 0)).mul (hX 1)
      have ht3 : (MvPolynomial.C 4 * MvPolynomial.X (0 : Fin 3) * MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) ℝ).IsHomogeneous 2 := by
        simpa using ((hC 4).mul (hX 0)).mul (hX 2)
      have ht4 : (MvPolynomial.C 3 * MvPolynomial.X (1 : Fin 3) ^ 2 : MvPolynomial (Fin 3) ℝ).IsHomogeneous 2 := by
        simpa [sq] using (hC 3).mul ((hX 1).mul (hX 1))
      have ht5 : (MvPolynomial.C 8 * MvPolynomial.X (1 : Fin 3) * MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) ℝ).IsHomogeneous 2 := by
        simpa using ((hC 8).mul (hX 1)).mul (hX 2)
      have ht6 : (MvPolynomial.C 3 * MvPolynomial.X (2 : Fin 3) ^ 2 : MvPolynomial (Fin 3) ℝ).IsHomogeneous 2 := by
        simpa [sq] using (hC 3).mul ((hX 2).mul (hX 2))
      exact ((((ht1.add ht2).add ht3).add ht4).add ht5).add ht6
    have hQ1_deg : Q1.totalDegree < 2 := by
      have h1 : (1 : MvPolynomial (Fin 3) ℝ).totalDegree ≤ 1 := by simp
      have hX0 : (MvPolynomial.C 2 * MvPolynomial.X (0 : Fin 3) : MvPolynomial (Fin 3) ℝ).totalDegree ≤ 1 :=
        le_trans (MvPolynomial.totalDegree_mul _ _) (by simp)
      have hX1 : (MvPolynomial.C 4 * MvPolynomial.X (1 : Fin 3) : MvPolynomial (Fin 3) ℝ).totalDegree ≤ 1 :=
        le_trans (MvPolynomial.totalDegree_mul _ _) (by simp)
      have hX2 : (MvPolynomial.C 4 * MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) ℝ).totalDegree ≤ 1 :=
        le_trans (MvPolynomial.totalDegree_mul _ _) (by simp)
      have hle : Q1.totalDegree ≤ 1 :=
        le_trans (MvPolynomial.totalDegree_add _ _) (max_le
          (le_trans (MvPolynomial.totalDegree_add _ _) (max_le
            (le_trans (MvPolynomial.totalDegree_add _ _) (max_le h1 hX0)) hX1)) hX2)
      omega
    have hQ2_ne : Q2 ≠ 0 := fun h => by
      have := congrArg (MvPolynomial.eval ![1, 0, 0]) h
      simp [Q2] at this
    have hQp_top : leadingHomog Qp = Q2 := by
      have hwt3 : ∀ d : Fin 3 →₀ ℕ, d.sum (fun _ e => e) = Finsupp.weight (1 : Fin 3 → ℕ) d := fun d => by
        simp [Finsupp.weight_apply, Finsupp.sum]
      have hQ2_self : Q2.homogeneousComponent 2 = Q2 := by
        ext d; rw [MvPolynomial.coeff_homogeneousComponent]
        by_cases hc : MvPolynomial.coeff d Q2 = 0
        · simp [hc]
        · have hd : Finsupp.degree d = 2 := by
            change d.sum (fun _ e => e) = 2
            rw [hwt3 d]; exact hQ2_hom hc
          simp [hd]
      have hcomp2 : Qp.homogeneousComponent 2 = Q2 := by
        rw [hQp_split, map_add, hQ2_self,
            MvPolynomial.homogeneousComponent_eq_zero 2 Q1 hQ1_deg, add_zero]
      have hle2 : Qp.totalDegree ≤ 2 := by
        rw [hQp_split]
        refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ (le_of_lt hQ1_deg))
        exact Finset.sup_le fun d hd => by rw [hwt3 d, hQ2_hom (MvPolynomial.mem_support_iff.mp hd)]
      have hge2 : 2 ≤ Qp.totalDegree := by
        by_contra hlt
        exact hQ2_ne (hcomp2 ▸ MvPolynomial.homogeneousComponent_eq_zero 2 Qp (not_le.mp hlt))
      rw [leadingHomog, le_antisymm hle2 hge2, hcomp2]
    rw [hQp_top] at hfac
    exact wishart_Q2_not_linear_factor c c₀ hc0 hc₀_pos ν lam hfac

/-! ### Section 5: Assemble Main Theorem -/

private theorem main_proof :
    (∀ (n : ℕ), 2 ≤ n →
      ∀ (P Q : MvPolynomial (Fin n) ℝ) (p₀ : ℝ),
        MvPolynomial.eval 0 Q ≠ 0 →
        MvPolynomial.eval 0 P = MvPolynomial.eval 0 Q →
        0 ≤ p₀ → p₀ ≤ 1 →
        ∃ (m : ℕ) (_ : 1 ≤ m) (α : Fin m → ℝ) (T : Matrix (Fin m) (Fin m) ℝ)
          (K : Matrix (Fin m) (Fin n) ℝ),
          IsHurwitzStable T ∧
          (∀ i j, 0 ≤ K i j) ∧
          p₀ = 1 - ∑ i, α i ∧
          0 ≤ ∑ i, α i ∧ ∑ i, α i ≤ 1 ∧
          ∃ U : Set (Fin n → ℝ), IsOpen U ∧ (0 : Fin n → ℝ) ∈ U ∧
            ∀ s ∈ U,
              MvPolynomial.eval s Q ≠ 0 ∧
              IsUnit (-T + Matrix.diagonal (K.mulVec s)).det ∧
              MvPolynomial.eval s P / MvPolynomial.eval s Q =
                kulkarniEval p₀ α T K (-(T.mulVec 1)) s) ∧
    (∀ (n m : ℕ) (p₀ : ℝ) (α : Fin m → ℝ) (T : Matrix (Fin m) (Fin m) ℝ)
      (K : Matrix (Fin m) (Fin n) ℝ) (t : Fin m → ℝ),
      IsHurwitzStable T →
      ∃ P Q : MvPolynomial (Fin n) ℝ,
        MvPolynomial.eval 0 Q ≠ 0 ∧
        ∀ s : Fin n → ℝ, IsUnit (-T + Matrix.diagonal (K.mulVec s)).det →
          MvPolynomial.eval s Q ≠ 0 ∧
          kulkarniEval p₀ α T K t s = MvPolynomial.eval s P / MvPolynomial.eval s Q) ∧
    (∀ (n : ℕ) (P Q : MvPolynomial (Fin n) ℝ),
      Q ≠ 0 →
      (∀ D : MvPolynomial (Fin n) ℝ, D ∣ P → D ∣ Q → IsUnit D) →
      (∃ (m : ℕ) (_ : 1 ≤ m) (α : Fin m → ℝ) (T : Matrix (Fin m) (Fin m) ℝ)
        (K : Matrix (Fin m) (Fin n) ℝ),
        IsTransientSubgenerator T ∧
        (∀ i, 0 ≤ α i) ∧
        (∑ i, α i ≤ 1) ∧
        (∀ i j, 0 ≤ K i j) ∧
        ∀ s : Fin n → ℝ, (∀ j, 0 ≤ s j) →
          MvPolynomial.eval s Q ≠ 0 ∧
          IsUnit (-T + Matrix.diagonal (K.mulVec s)).det ∧
          MvPolynomial.eval s P / MvPolynomial.eval s Q =
            kulkarniEval (1 - ∑ i, α i) α T K (-(T.mulVec 1)) s) →
      ∃ (c : ℝ) (_ : c ≠ 0) (c₀ : ℝ) (_ : 0 < c₀) (ν : ℕ) (lam : Fin ν → Fin n → ℝ),
        (∀ i j, 0 ≤ lam i j) ∧
        MvPolynomial.C c * leadingHomog Q =
          MvPolynomial.C c₀ * ∏ i : Fin ν, ∑ j : Fin n, MvPolynomial.C (lam i j) * MvPolynomial.X j) ∧
    (∀ (n : ℕ), 3 ≤ n →
      ∃ μ : Measure (Fin n → ℝ),
        IsProbabilityMeasure μ ∧
        (∀ᵐ x ∂μ, ∀ j : Fin n, 0 ≤ x j) ∧
        (∀ a : Fin n → ℝ, (∀ j, 0 ≤ a j) → a ≠ 0 →
          IsUnivariatePHTransform (fun u => laplaceTransform μ (u • a))) ∧
        ¬ HasMPHRep (laplaceTransform μ)) :=
  ⟨mvme_subset_mme, mme_subset_mvme, fun _ P Q hQ hcop hrep => mph_factorization P Q hQ hcop hrep,
    mvph_strict_separation⟩

end OMA.P_arxiv_2605_15395

theorem OMA.solution : type_of% @OMA.S_arxiv_2605_15395.main :=
  OMA.P_arxiv_2605_15395.main_proof
