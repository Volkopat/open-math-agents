import OMAStatements.S_mo_402743

namespace OMA.S_mo_402743_Proof

open Polynomial Set OMA.S_mo_402743

/-! ### Part 1: Basic properties of `unordered`, `rootPoly`, and `derivMap` -/

private lemma unordered_val_eq {n : ℕ} (x : Fin n → ℂ) :
    (unordered x).val = Finset.univ.val.map x := by
  change ((List.ofFn x : List ℂ) : Multiset ℂ) = _
  rw [List.ofFn_eq_map]
  rfl

private lemma unordered_surjective (n : ℕ) : Function.Surjective (@unordered n) := by
  intro S
  obtain ⟨l, hl⟩ := Quotient.exists_rep S.val
  have hlen : l.length = n := by
    have hcard : S.val.card = n := S.2
    rw [← hl] at hcard
    simpa using hcard
  refine ⟨fun i => l[i.val]'(by omega), ?_⟩
  apply Subtype.ext
  change ((List.ofFn (fun i : Fin n => l[i.val]'(by omega)) : List ℂ) : Multiset ℂ) = S.val
  rw [← hl]
  congr 1
  apply List.ext_getElem
  · simp [hlen]
  · intro i h1 h2
    simp

private lemma rootPoly_monic {n : ℕ} (S : Config n) : (rootPoly S).Monic := by
  unfold rootPoly
  exact Polynomial.monic_multiset_prod_of_monic _ _ fun z _ => Polynomial.monic_X_sub_C z

private lemma rootPoly_ne_zero {n : ℕ} (S : Config n) : rootPoly S ≠ 0 :=
  (rootPoly_monic S).ne_zero

private lemma rootPoly_roots {n : ℕ} (S : Config n) : (rootPoly S).roots = S.val :=
  Polynomial.roots_multiset_prod_X_sub_C S.val

private lemma rootPoly_natDegree {n : ℕ} (S : Config n) : (rootPoly S).natDegree = n := by
  have h := IsAlgClosed.card_roots_eq_natDegree (p := rootPoly S)
  rw [rootPoly_roots] at h
  exact h.symm.trans S.2

private lemma rootPoly_unordered {n : ℕ} (x : Fin n → ℂ) :
    rootPoly (unordered x) = ∏ i : Fin n, (X - C (x i)) := by
  unfold rootPoly
  rw [unordered_val_eq, Multiset.map_map]
  rfl

private lemma rootPoly_derivative_natDegree {n : ℕ} (S : Config (n + 1)) :
    (rootPoly S).derivative.natDegree = n := by
  rw [Polynomial.natDegree_derivative, rootPoly_natDegree]
  simp

private lemma rootPoly_derivative_roots_card {n : ℕ} (S : Config (n + 1)) :
    (rootPoly S).derivative.roots.card = n := by
  rw [IsAlgClosed.card_roots_eq_natDegree, rootPoly_derivative_natDegree]

private noncomputable def derivMap (n : ℕ) : Config (n + 1) → Config n :=
  fun S => ⟨(rootPoly S).derivative.roots, rootPoly_derivative_roots_card S⟩

private lemma derivMap_differentiates (n : ℕ) : differentiates (derivMap n) :=
  fun _ => rfl

/-! ### Part 2: Vieta homeomorphism `Config n ≃ₜ (Fin n → ℂ)` -/

private noncomputable def vieta (n : ℕ) (S : Config n) : Fin n → ℂ :=
  fun i => (rootPoly S).coeff i.val

private noncomputable def polyOfCoeff (n : ℕ) (a : Fin n → ℂ) : ℂ[X] :=
  X ^ n + ∑ i : Fin n, C (a i) * X ^ i.val

private lemma coeff_polyOfCoeff {n : ℕ} (a : Fin n → ℂ) (j : ℕ) :
    (polyOfCoeff n a).coeff j =
      if h : j < n then a ⟨j, h⟩ else if j = n then 1 else 0 := by
  unfold polyOfCoeff
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff]
  have hsum :
      (∑ i : Fin n, (C (a i) * X ^ i.val).coeff j) =
        if h : j < n then a ⟨j, h⟩ else 0 := by
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨j, h⟩]
      · simp
      · intro i _ hi
        have hne : j ≠ i.val := fun heq => hi (Fin.ext heq.symm)
        simp [hne]
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    · apply Finset.sum_eq_zero
      intro i _
      have hne : j ≠ i.val := by omega
      simp [hne]
  rw [hsum]
  split_ifs with h1 h2
  · omega
  · simp
  · simp
  · simp

private lemma polyOfCoeff_natDegree {n : ℕ} (a : Fin n → ℂ) :
    (polyOfCoeff n a).natDegree = n := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro j hj
    rw [coeff_polyOfCoeff]
    split_ifs with h1 h2
    · omega
    · omega
    · rfl
  · rw [coeff_polyOfCoeff]
    simp

private lemma polyOfCoeff_monic {n : ℕ} (a : Fin n → ℂ) :
    (polyOfCoeff n a).Monic := by
  rw [Polynomial.Monic, Polynomial.leadingCoeff, polyOfCoeff_natDegree, coeff_polyOfCoeff]
  simp

private noncomputable def fromCoeff (n : ℕ) (a : Fin n → ℂ) : Config n :=
  ⟨(polyOfCoeff n a).roots, by rw [IsAlgClosed.card_roots_eq_natDegree, polyOfCoeff_natDegree]⟩

private lemma polyOfCoeff_vieta {n : ℕ} (S : Config n) :
    polyOfCoeff n (vieta n S) = rootPoly S := by
  ext j
  rw [coeff_polyOfCoeff]
  split_ifs with h1 h2
  · rfl
  · subst h2
    have hmon := rootPoly_monic S
    rw [Polynomial.Monic, Polynomial.leadingCoeff, rootPoly_natDegree] at hmon
    exact hmon.symm
  · symm
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    rw [rootPoly_natDegree]
    omega

private lemma fromCoeff_vieta {n : ℕ} (S : Config n) : fromCoeff n (vieta n S) = S := by
  apply Subtype.ext
  change (polyOfCoeff n (vieta n S)).roots = S.val
  rw [polyOfCoeff_vieta, rootPoly_roots]

private lemma rootPoly_fromCoeff {n : ℕ} (a : Fin n → ℂ) :
    rootPoly (fromCoeff n a) = polyOfCoeff n a := by
  unfold rootPoly fromCoeff
  exact Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq
    (polyOfCoeff_monic a) IsAlgClosed.card_roots_eq_natDegree

private lemma vieta_fromCoeff {n : ℕ} (a : Fin n → ℂ) : vieta n (fromCoeff n a) = a := by
  ext i
  unfold vieta
  rw [rootPoly_fromCoeff, coeff_polyOfCoeff]
  simp [i.isLt]

private lemma continuous_coeff_prod_X_sub_C {n : ℕ} (s : Finset (Fin n)) (k : ℕ) :
    Continuous (fun x : Fin n → ℂ => (∏ j ∈ s, (X - C (x j))).coeff k) := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty =>
    simpa using continuous_const
  | insert a s ha ih =>
    have hfun :
        (fun x : Fin n → ℂ => (∏ j ∈ insert a s, (X - C (x j))).coeff k) =
          fun x => (if k = 0 then (0 : ℂ) else (∏ j ∈ s, (X - C (x j))).coeff (k - 1)) -
            x a * (∏ j ∈ s, (X - C (x j))).coeff k := by
      ext x
      rw [Finset.prod_insert ha, sub_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
      cases k with
      | zero => simp
      | succ m => simp [Polynomial.coeff_X_mul]
    rw [hfun]
    apply Continuous.sub
    · cases k with
      | zero => simpa using continuous_const
      | succ m => simpa using ih m
    · exact (continuous_apply a).mul (ih k)

private lemma continuous_vieta_comp_unordered (n : ℕ) :
    Continuous (vieta n ∘ @unordered n) := by
  apply continuous_pi
  intro i
  dsimp only [Function.comp_apply]
  have hfun : (fun x : Fin n → ℂ => (vieta n (unordered x)) i) =
      fun x => (∏ j : Fin n, (X - C (x j))).coeff i.val := by
    ext x
    simp [vieta, rootPoly_unordered]
  rw [hfun]
  exact continuous_coeff_prod_X_sub_C Finset.univ i.val

private lemma continuous_vieta (n : ℕ) : Continuous (vieta n) :=
  continuous_coinduced_dom.mpr (continuous_vieta_comp_unordered n)

private lemma cauchy_root_bound {n : ℕ} {P : ℂ[X]} (hmon : P.Monic) (hdeg : P.natDegree = n)
    {R : ℝ} (hR : 0 ≤ R) (hcoeff : ∀ i : Fin n, ‖P.coeff i.val‖ ≤ R)
    {z : ℂ} (hz : P.eval z = 0) : ‖z‖ ≤ 1 + n * R := by
  by_cases h1 : ‖z‖ ≤ 1
  · have : (0 : ℝ) ≤ n * R := mul_nonneg (Nat.cast_nonneg n) hR
    linarith
  · push Not at h1
    have hnpos : 1 ≤ n := by
      by_contra h0
      have hn0 : n = 0 := by omega
      subst hn0
      have hP1 : P = 1 := Polynomial.eq_one_of_monic_natDegree_zero hmon hdeg
      rw [hP1, Polynomial.eval_one] at hz
      exact one_ne_zero hz
    have hsplit : z ^ n = - ∑ i : Fin n, P.coeff i.val * z ^ i.val := by
      have hval : P.eval z = z ^ n + ∑ i : Fin n, P.coeff i.val * z ^ i.val := by
        rw [Polynomial.eval_eq_sum_range, hdeg, Finset.sum_range_succ]
        have hlc : P.coeff n = 1 := by
          rw [← hdeg]
          exact hmon.leadingCoeff
        rw [hlc, one_mul, add_comm, ← Fin.sum_univ_eq_sum_range]
      rw [hval] at hz
      exact eq_neg_of_add_eq_zero_left hz
    have hnorm : ‖z‖ ^ n ≤ (n * R) * ‖z‖ ^ (n - 1) := by
      calc
        ‖z‖ ^ n = ‖z ^ n‖ := (norm_pow z n).symm
        _ = ‖- ∑ i : Fin n, P.coeff i.val * z ^ i.val‖ := by rw [hsplit]
        _ = ‖∑ i : Fin n, P.coeff i.val * z ^ i.val‖ := norm_neg _
        _ ≤ ∑ i : Fin n, ‖P.coeff i.val * z ^ i.val‖ := norm_sum_le _ _
        _ ≤ ∑ _i : Fin n, R * ‖z‖ ^ (n - 1) := by
          apply Finset.sum_le_sum
          intro i _
          rw [norm_mul, norm_pow]
          have hpow : ‖z‖ ^ i.val ≤ ‖z‖ ^ (n - 1) :=
            pow_le_pow_right₀ (le_of_lt h1) (by omega)
          exact mul_le_mul (hcoeff i) hpow (pow_nonneg (norm_nonneg z) _) hR
        _ = (n * R) * ‖z‖ ^ (n - 1) := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]
    have hpow_pos : (0 : ℝ) < ‖z‖ ^ (n - 1) := pow_pos (by linarith) _
    have hmul : ‖z‖ * ‖z‖ ^ (n - 1) ≤ (n * R) * ‖z‖ ^ (n - 1) := by
      have hexp : ‖z‖ * ‖z‖ ^ (n - 1) = ‖z‖ ^ n := by
        rw [← pow_succ', Nat.sub_add_cancel hnpos]
      linarith
    have hle : ‖z‖ ≤ n * R := le_of_mul_le_mul_right hmul hpow_pos
    linarith

private lemma isProperMap_vieta_comp_unordered (n : ℕ) :
    IsProperMap (vieta n ∘ @unordered n) := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨continuous_vieta_comp_unordered n, fun K hK => ?_⟩
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Fin n → ℂ)
  set R' := max R 0
  have hR'0 : 0 ≤ R' := le_max_right R 0
  have hsub : (vieta n ∘ @unordered n) ⁻¹' K ⊆
      Metric.closedBall (0 : Fin n → ℂ) (1 + n * R') := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by positivity)]
    intro j
    have hy : vieta n (unordered x) ∈ Metric.closedBall (0 : Fin n → ℂ) R := hR hx
    rw [Metric.mem_closedBall, dist_zero_right] at hy
    have hcoeff : ∀ i : Fin n, ‖(rootPoly (unordered x)).coeff i.val‖ ≤ R' := by
      intro i
      have hi : ‖vieta n (unordered x) i‖ ≤ R := (norm_le_pi_norm _ i).trans hy
      exact hi.trans (le_max_left R 0)
    have hroot : (rootPoly (unordered x)).eval (x j) = 0 := by
      rw [rootPoly_unordered, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp)
    exact cauchy_root_bound (rootPoly_monic _) (rootPoly_natDegree _) hR'0 hcoeff hroot
  have hclosed : IsClosed ((vieta n ∘ @unordered n) ⁻¹' K) :=
    hK.isClosed.preimage (continuous_vieta_comp_unordered n)
  exact (isCompact_closedBall (0 : Fin n → ℂ) (1 + n * R')).of_isClosed_subset hclosed hsub

private lemma continuous_fromCoeff (n : ℕ) : Continuous (fromCoeff n) := by
  have hcont := continuous_vieta_comp_unordered n
  have hclosed := (isProperMap_vieta_comp_unordered n).isClosedMap
  have hsurj : Function.Surjective (vieta n ∘ @unordered n) := by
    intro a
    obtain ⟨x, hx⟩ := unordered_surjective n (fromCoeff n a)
    exact ⟨x, by simp [hx, vieta_fromCoeff]⟩
  have hquot : Topology.IsQuotientMap (vieta n ∘ @unordered n) :=
    hclosed.isQuotientMap hcont hsurj
  rw [continuous_def]
  intro U hU
  rw [← hquot.isOpen_preimage]
  have hpre : (vieta n ∘ @unordered n) ⁻¹' (fromCoeff n ⁻¹' U) = unordered ⁻¹' U := by
    ext x
    simp [fromCoeff_vieta]
  rw [hpre]
  exact isOpen_coinduced.mp hU

/-! ### Part 3: Admissibility of `derivMap` -/

private lemma rootPoly_derivMap {n : ℕ} (S : Config (n + 1)) :
    rootPoly (derivMap n S) = C ((n + 1 : ℂ)⁻¹) * (rootPoly S).derivative := by
  have hne : ((n + 1 : ℂ)⁻¹) ≠ 0 := by
    exact inv_ne_zero (Nat.cast_add_one_ne_zero n)
  set Q := C ((n + 1 : ℂ)⁻¹) * (rootPoly S).derivative
  have hQroots : Q.roots = (rootPoly S).derivative.roots :=
    Polynomial.roots_C_mul _ hne
  have hQdeg : Q.natDegree = n := by
    rw [Polynomial.natDegree_C_mul hne, rootPoly_derivative_natDegree]
  have hQmon : Q.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hQdeg, Polynomial.coeff_C_mul,
      Polynomial.coeff_derivative]
    have hlc : (rootPoly S).coeff (n + 1) = 1 := by
      have hmon := rootPoly_monic S
      rw [Polynomial.Monic, Polynomial.leadingCoeff, rootPoly_natDegree] at hmon
      exact hmon
    rw [hlc, one_mul]
    exact inv_mul_cancel₀ (Nat.cast_add_one_ne_zero n)
  have hcard : Q.roots.card = Q.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hprod := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hQmon hcard
  rw [hQroots] at hprod
  exact hprod

private noncomputable def derivCoeffMap (n : ℕ) (a : Fin (n + 1) → ℂ) : Fin n → ℂ :=
  fun i => ((i.val + 1 : ℂ) / (n + 1 : ℂ)) * a i.succ

private lemma vieta_derivMap {n : ℕ} (S : Config (n + 1)) :
    vieta n (derivMap n S) = derivCoeffMap n (vieta (n + 1) S) := by
  ext i
  simp only [vieta, derivCoeffMap, rootPoly_derivMap, Polynomial.coeff_C_mul,
    Polynomial.coeff_derivative, Fin.val_succ]
  ring

private lemma derivMap_eq_comp (n : ℕ) :
    derivMap n = fromCoeff n ∘ derivCoeffMap n ∘ vieta (n + 1) := by
  ext S : 1
  simp only [Function.comp_apply, ← vieta_derivMap, fromCoeff_vieta]

private lemma derivMap_continuous (n : ℕ) : Continuous (derivMap n) := by
  rw [derivMap_eq_comp]
  refine (continuous_fromCoeff n).comp (Continuous.comp ?_ (continuous_vieta (n + 1)))
  apply continuous_pi
  intro i
  exact continuous_const.mul (continuous_apply i.succ)

private lemma derivMap_surjective (n : ℕ) : Function.Surjective (derivMap n) := by
  intro T
  let b := vieta n T
  let a : Fin (n + 1) → ℂ :=
    Fin.cases 0 (fun i => ((n + 1 : ℂ) / (i.val + 1 : ℂ)) * b i)
  refine ⟨fromCoeff (n + 1) a, ?_⟩
  rw [derivMap_eq_comp, Function.comp_apply, Function.comp_apply, vieta_fromCoeff]
  have hda : derivCoeffMap n a = b := by
    ext i
    simp only [derivCoeffMap, a, Fin.cases_succ]
    have h1 : (n + 1 : ℂ) ≠ 0 := Nat.cast_add_one_ne_zero n
    have h2 : (i.val + 1 : ℂ) ≠ 0 := Nat.cast_add_one_ne_zero i.val
    field_simp [h1, h2]
  rw [hda, fromCoeff_vieta]

private lemma derivMap_convexHull {n : ℕ} (S : Config (n + 1)) :
    convexHull ℝ (points (derivMap n S)) ⊆ convexHull ℝ (points S) := by
  apply convexHull_min _ (convex_convexHull ℝ (points S))
  intro z hz
  change z ∈ (rootPoly S).derivative.roots at hz
  have hP'ne : (rootPoly S).derivative ≠ 0 := by
    intro h0
    rw [h0, Polynomial.roots_zero] at hz
    simp at hz
  have hz_root : (rootPoly S).derivative.eval z = 0 :=
    (Polynomial.mem_roots hP'ne).mp hz
  by_cases hmem : z ∈ S
  · exact subset_convexHull ℝ (points S) hmem
  · obtain ⟨x, rfl⟩ := unordered_surjective (n + 1) S
    have hne : ∀ i : Fin (n + 1), z - x i ≠ 0 := by
      intro i h0
      apply hmem
      have hzi : z = x i := sub_eq_zero.mp h0
      rw [hzi]
      change x i ∈ (unordered x).val
      rw [unordered_val_eq]
      exact Multiset.mem_map_of_mem x (Finset.mem_univ i)
    have hPne : (∏ i : Fin (n + 1), (z - x i)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => hne i
    have hderiv :
        (rootPoly (unordered x)).derivative.eval z =
          ∑ i : Fin (n + 1), ∏ j ∈ Finset.univ.erase i, (z - x j) := by
      rw [rootPoly_unordered, Polynomial.derivative_prod_finset, Polynomial.eval_finsetSum]
      apply Finset.sum_congr rfl
      intro i _
      simp [Polynomial.eval_prod]
    have hsum_inv : (∑ i : Fin (n + 1), (z - x i)⁻¹) = 0 := by
      have hmul : (∏ j : Fin (n + 1), (z - x j)) * ∑ i : Fin (n + 1), (z - x i)⁻¹ = 0 := by
        rw [Finset.mul_sum]
        have hterm :
            ∑ i : Fin (n + 1), (∏ j : Fin (n + 1), (z - x j)) * (z - x i)⁻¹ =
              ∑ i : Fin (n + 1), ∏ j ∈ Finset.univ.erase i, (z - x j) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← Finset.mul_prod_erase Finset.univ (fun j => z - x j) (Finset.mem_univ i)]
          have hi := hne i
          field_simp [hi]
        rw [hterm, ← hderiv, hz_root]
      exact (mul_eq_zero.mp hmul).resolve_left hPne
    let w : Fin (n + 1) → ℝ := fun i => (Complex.normSq (z - x i))⁻¹
    have hw_pos : ∀ i : Fin (n + 1), 0 < w i := fun i =>
      inv_pos.mpr (Complex.normSq_pos.mpr (hne i))
    have hW_pos : 0 < ∑ i : Fin (n + 1), w i :=
      Finset.sum_pos (fun i _ => hw_pos i) Finset.univ_nonempty
    have hconj : (∑ i : Fin (n + 1), (w i : ℂ) * (z - x i)) = 0 := by
      have h1 : star (∑ i : Fin (n + 1), (z - x i)⁻¹) = 0 := by
        rw [hsum_inv, star_zero]
      rw [star_sum] at h1
      convert h1 using 1
      apply Finset.sum_congr rfl
      intro i _
      have hi : z - x i ≠ 0 := hne i
      have hns : (Complex.normSq (z - x i) : ℂ) = (z - x i) * star (z - x i) := by
        rw [Complex.star_def, Complex.mul_conj]
      have hns_ne : (Complex.normSq (z - x i) : ℂ) ≠ 0 := by
        exact_mod_cast (Complex.normSq_pos.mpr hi).ne'
      simp only [w, Complex.ofReal_inv, star_inv₀]
      rw [hns]
      have hs_ne : star (z - x i) ≠ 0 := star_ne_zero.mpr hi
      field_simp [hi, hs_ne]
    have hcenter : Finset.univ.centerMass w x = z := by
      rw [Finset.centerMass]
      have hsum_eq : (∑ i : Fin (n + 1), w i • x i) = (∑ i : Fin (n + 1), w i) • z := by
        have hsub : (∑ i : Fin (n + 1), (w i : ℂ) * z) -
            (∑ i : Fin (n + 1), (w i : ℂ) * x i) = 0 := by
          rw [← Finset.sum_sub_distrib]
          simpa [mul_sub] using hconj
        have heq := sub_eq_zero.mp hsub
        rw [← Finset.sum_mul] at heq
        simpa [Complex.real_smul, Complex.ofReal_sum] using heq.symm
      rw [hsum_eq, smul_smul, inv_mul_cancel₀ hW_pos.ne', one_smul]
    rw [← hcenter]
    apply Finset.centerMass_mem_convexHull Finset.univ
    · intro i _; exact le_of_lt (hw_pos i)
    · exact hW_pos
    · intro i _
      change x i ∈ (unordered x).val
      rw [unordered_val_eq]
      exact Multiset.mem_map_of_mem x (Finset.mem_univ i)

private lemma derivMap_mult {n : ℕ} (S : Config (n + 1)) (z : ℂ) (hz : z ∈ S) :
    (derivMap n S).val.count z + 1 = S.val.count z := by
  have hP := rootPoly_ne_zero S
  have hcountS : S.val.count z = (rootPoly S).rootMultiplicity z := by
    rw [← rootPoly_roots S, Polynomial.count_roots]
  have hcountD : (derivMap n S).val.count z = (rootPoly S).derivative.rootMultiplicity z := by
    change (rootPoly S).derivative.roots.count z = _
    rw [Polynomial.count_roots]
  have hpos : 0 < (rootPoly S).rootMultiplicity z := by
    rw [← hcountS]
    exact Multiset.count_pos.mpr hz
  have hroot : (rootPoly S).IsRoot z := (Polynomial.rootMultiplicity_pos hP).mp hpos
  have hnzd : ((rootPoly S).rootMultiplicity z : ℂ) ∈ nonZeroDivisors ℂ := by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    exact Nat.cast_ne_zero.mpr hpos.ne'
  rw [hcountD, hcountS, Polynomial.derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors hroot hnzd]
  omega

private lemma derivMap_admissible (n : ℕ) : admissible (derivMap n) :=
  ⟨derivMap_continuous n, derivMap_surjective n, derivMap_convexHull, derivMap_mult⟩

/-! ### Part 4: Biased midpoint counterexample for `n = 1` -/

private noncomputable def weight (z : ℂ) : ℝ := 1 + Complex.normSq z

private lemma weight_pos (z : ℂ) : 0 < weight z := by
  unfold weight
  have := Complex.normSq_nonneg z
  linarith

private lemma continuous_weight : Continuous weight :=
  continuous_const.add Complex.continuous_normSq

private noncomputable def biasedMid (S : Config 2) : ℂ :=
  ((S.val.map weight).sum)⁻¹ • (S.val.map (fun z => weight z • z)).sum

private noncomputable def F1 : Config 2 → Config 1 :=
  fun S => ⟨{biasedMid S}, by simp⟩

private lemma unordered_fin2_val (x : Fin 2 → ℂ) :
    (unordered x).val = {x 0, x 1} := by
  change ((List.ofFn x : List ℂ) : Multiset ℂ) = _
  rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  rfl

private lemma biasedMid_unordered (x : Fin 2 → ℂ) :
    biasedMid (unordered x) =
      (weight (x 0) + weight (x 1))⁻¹ • (weight (x 0) • x 0 + weight (x 1) • x 1) := by
  unfold biasedMid
  rw [unordered_fin2_val]
  simp

private lemma F1_continuous : Continuous F1 := by
  rw [continuous_coinduced_dom]
  have hcomp : F1 ∘ @unordered 2 =
      @unordered 1 ∘ (fun (x : Fin 2 → ℂ) (_ : Fin 1) => biasedMid (unordered x)) := by
    ext x : 1
    apply Subtype.ext
    simp [F1, unordered, List.ofFn_succ]
  rw [hcomp]
  apply continuous_coinduced_rng.comp
  apply continuous_pi
  intro _
  have hfun : (fun x : Fin 2 → ℂ => biasedMid (unordered x)) =
      fun x => (weight (x 0) + weight (x 1))⁻¹ • (weight (x 0) • x 0 + weight (x 1) • x 1) := by
    ext x
    exact biasedMid_unordered x
  rw [hfun]
  have hden : Continuous (fun x : Fin 2 → ℂ => (weight (x 0) + weight (x 1))⁻¹) := by
    apply Continuous.inv₀
    · exact (continuous_weight.comp (continuous_apply 0)).add
        (continuous_weight.comp (continuous_apply 1))
    · intro x
      linarith [weight_pos (x 0), weight_pos (x 1)]
  have hnum : Continuous (fun x : Fin 2 → ℂ => weight (x 0) • x 0 + weight (x 1) • x 1) :=
    ((continuous_weight.comp (continuous_apply 0)).smul (continuous_apply 0)).add
      ((continuous_weight.comp (continuous_apply 1)).smul (continuous_apply 1))
  exact hden.smul hnum

private lemma F1_surjective : Function.Surjective F1 := by
  intro T
  obtain ⟨y, rfl⟩ := unordered_surjective 1 T
  refine ⟨unordered (fun _ : Fin 2 => y 0), ?_⟩
  apply Subtype.ext
  have hbm : biasedMid (unordered (fun _ : Fin 2 => y 0)) = y 0 := by
    rw [biasedMid_unordered]
    have hw : weight (y 0) + weight (y 0) ≠ 0 := by linarith [weight_pos (y 0)]
    rw [← add_smul, smul_smul, inv_mul_cancel₀ hw, one_smul]
  change ({biasedMid (unordered (fun _ : Fin 2 => y 0))} : Multiset ℂ) = (List.ofFn y : Multiset ℂ)
  rw [hbm, List.ofFn_succ, List.ofFn_zero]
  rfl

private lemma F1_convexHull (S : Config 2) :
    convexHull ℝ (points (F1 S)) ⊆ convexHull ℝ (points S) := by
  apply convexHull_min _ (convex_convexHull ℝ (points S))
  intro z hz
  have hz' : z = biasedMid S := by
    simpa [points, F1] using hz
  subst hz'
  obtain ⟨x, rfl⟩ := unordered_surjective 2 S
  have hcenter : Finset.univ.centerMass (fun i : Fin 2 => weight (x i)) x =
      biasedMid (unordered x) := by
    rw [Finset.centerMass, biasedMid_unordered]
    simp [Fin.sum_univ_two]
  rw [← hcenter]
  apply Finset.centerMass_mem_convexHull Finset.univ
  · intro i _; exact le_of_lt (weight_pos (x i))
  · exact Finset.sum_pos (fun i _ => weight_pos (x i)) Finset.univ_nonempty
  · intro i _
    change x i ∈ (unordered x).val
    rw [unordered_val_eq]
    exact Multiset.mem_map_of_mem x (Finset.mem_univ i)

private lemma F1_mult (S : Config 2) (z : ℂ) (hz : z ∈ S) :
    (F1 S).val.count z + 1 = S.val.count z := by
  obtain ⟨x, rfl⟩ := unordered_surjective 2 S
  have hval : (unordered x).val = {x 0, x 1} := unordered_fin2_val x
  have hbm : biasedMid (unordered x) =
      (weight (x 0) + weight (x 1))⁻¹ • (weight (x 0) • x 0 + weight (x 1) • x 1) :=
    biasedMid_unordered x
  have hden_pos : 0 < weight (x 0) + weight (x 1) := by
    linarith [weight_pos (x 0), weight_pos (x 1)]
  have hmem : z = x 0 ∨ z = x 1 := by
    change z ∈ (unordered x).val at hz
    rw [hval] at hz
    simpa using hz
  by_cases heq : x 0 = x 1
  · have hz0 : z = x 0 := by rcases hmem with rfl | rfl <;> [rfl; exact heq.symm]
    subst hz0
    have hbm' : biasedMid (unordered x) = x 0 := by
      rw [hbm, ← heq, ← add_smul, smul_smul]
      have hne : weight (x 0) + weight (x 0) ≠ 0 := by linarith [weight_pos (x 0)]
      rw [inv_mul_cancel₀ hne, one_smul]
    change ({biasedMid (unordered x)} : Multiset ℂ).count (x 0) + 1 = (unordered x).val.count (x 0)
    rw [hbm', hval, ← heq]
    simp
  · have hne0 : biasedMid (unordered x) ≠ x 0 := by
      intro h0
      have h1 : weight (x 0) • x 0 + weight (x 1) • x 1 =
          (weight (x 0) + weight (x 1)) • x 0 := by
        calc
          weight (x 0) • x 0 + weight (x 1) • x 1
              = (weight (x 0) + weight (x 1)) • biasedMid (unordered x) := by
                rw [hbm, smul_smul, mul_inv_cancel₀ hden_pos.ne', one_smul]
          _ = (weight (x 0) + weight (x 1)) • x 0 := by rw [h0]
      rw [add_smul] at h1
      have h2 : weight (x 1) • x 1 = weight (x 1) • x 0 := add_left_cancel h1
      have h3 : weight (x 1) • (x 1 - x 0) = 0 := by rw [smul_sub, h2, sub_self]
      rcases smul_eq_zero.mp h3 with hw | hdiff
      · exact (weight_pos (x 1)).ne' hw
      · exact heq (sub_eq_zero.mp hdiff).symm
    have hne1 : biasedMid (unordered x) ≠ x 1 := by
      intro h1
      have h2 : weight (x 0) • x 0 + weight (x 1) • x 1 =
          (weight (x 0) + weight (x 1)) • x 1 := by
        calc
          weight (x 0) • x 0 + weight (x 1) • x 1
              = (weight (x 0) + weight (x 1)) • biasedMid (unordered x) := by
                rw [hbm, smul_smul, mul_inv_cancel₀ hden_pos.ne', one_smul]
          _ = (weight (x 0) + weight (x 1)) • x 1 := by rw [h1]
      rw [add_smul] at h2
      have h3 : weight (x 0) • x 0 = weight (x 0) • x 1 := add_right_cancel h2
      have h4 : weight (x 0) • (x 0 - x 1) = 0 := by rw [smul_sub, h3, sub_self]
      rcases smul_eq_zero.mp h4 with hw | hdiff
      · exact (weight_pos (x 0)).ne' hw
      · exact heq (sub_eq_zero.mp hdiff)
    rcases hmem with rfl | rfl
    · have hc1 : ({biasedMid (unordered x)} : Multiset ℂ).count (x 0) = 0 :=
        Multiset.count_eq_zero.mpr (by simpa using hne0.symm)
      have hc2 : ({x 0, x 1} : Multiset ℂ).count (x 0) = 1 := by
        simp [heq]
      change ({biasedMid (unordered x)} : Multiset ℂ).count (x 0) + 1 = _
      rw [hc1, hval, hc2]
    · have hc1 : ({biasedMid (unordered x)} : Multiset ℂ).count (x 1) = 0 :=
        Multiset.count_eq_zero.mpr (by simpa using hne1.symm)
      have hc2 : ({x 0, x 1} : Multiset ℂ).count (x 1) = 1 := by
        simp [Ne.symm heq]
      change ({biasedMid (unordered x)} : Multiset ℂ).count (x 1) + 1 = _
      rw [hc1, hval, hc2]

private lemma F1_admissible : admissible F1 :=
  ⟨F1_continuous, F1_surjective, F1_convexHull, F1_mult⟩

private lemma F1_not_differentiates : ¬ differentiates F1 := by
  intro hdiff
  let x : Fin 2 → ℂ := ![0, 1]
  let S : Config 2 := unordered x
  have hS := hdiff S
  have hmem : biasedMid S ∈ (rootPoly S).derivative.roots := by
    rw [← hS]
    simp [F1]
  have hP'ne : (rootPoly S).derivative ≠ 0 := by
    intro h0
    rw [h0, Polynomial.roots_zero] at hmem
    simp at hmem
  have hroot : (rootPoly S).derivative.eval (biasedMid S) = 0 :=
    (Polynomial.mem_roots hP'ne).mp hmem
  have hP : rootPoly S = X * (X - 1) := by
    rw [rootPoly_unordered, Fin.prod_univ_two]
    simp [x]
  have hP' : (rootPoly S).derivative = 2 * X - 1 := by
    rw [hP]
    simp [Polynomial.derivative_mul]
    ring
  have hbm : biasedMid S = (2 / 3 : ℂ) := by
    rw [biasedMid_unordered]
    simp only [x, Matrix.cons_val_zero, Matrix.cons_val_one, weight, map_zero, map_one,
      add_zero, smul_zero, zero_add, Complex.real_smul]
    norm_num
  rw [hP', hbm] at hroot
  simp at hroot
  norm_num at hroot

/-! ### Part 5: Anisotropic stretch counterexample for `n ≥ 2` -/

private def stretchLin : ℂ →ₗ[ℝ] ℂ where
  toFun z := ⟨2 * z.re, z.im⟩
  map_add' z w := by apply Complex.ext; (simp; ring); simp
  map_smul' r z := by apply Complex.ext; (simp; ring); simp

private noncomputable def unstretchLin : ℂ →ₗ[ℝ] ℂ where
  toFun z := ⟨z.re / 2, z.im⟩
  map_add' z w := by apply Complex.ext; (simp; ring); simp
  map_smul' r z := by apply Complex.ext; (simp; ring); simp

private lemma stretch_unstretch (z : ℂ) : stretchLin (unstretchLin z) = z := by
  apply Complex.ext
  · simp [stretchLin, unstretchLin]
    ring
  · simp [stretchLin, unstretchLin]

private lemma unstretch_stretch (z : ℂ) : unstretchLin (stretchLin z) = z := by
  apply Complex.ext <;> simp [stretchLin, unstretchLin]

private lemma stretch_continuous : Continuous stretchLin := by
  have h : (stretchLin : ℂ → ℂ) = fun z => ((2 * z.re : ℝ) : ℂ) + ((z.im : ℝ) : ℂ) * Complex.I := by
    ext z
    apply Complex.ext <;> simp [stretchLin]
  rw [h]
  exact (Complex.continuous_ofReal.comp (continuous_const.mul Complex.continuous_re)).add
    ((Complex.continuous_ofReal.comp Complex.continuous_im).mul continuous_const)

private lemma unstretch_continuous : Continuous unstretchLin := by
  have h : (unstretchLin : ℂ → ℂ) = fun z => ((z.re / 2 : ℝ) : ℂ) + ((z.im : ℝ) : ℂ) * Complex.I := by
    ext z
    apply Complex.ext <;> simp [unstretchLin]
  rw [h]
  exact (Complex.continuous_ofReal.comp (Complex.continuous_re.div_const 2)).add
    ((Complex.continuous_ofReal.comp Complex.continuous_im).mul continuous_const)

private def mapConfig (f : ℂ → ℂ) {k : ℕ} (S : Config k) : Config k :=
  ⟨S.val.map f, by simp⟩

private lemma mapConfig_continuous {f : ℂ → ℂ} (hf : Continuous f) (k : ℕ) :
    Continuous (mapConfig f (k := k)) := by
  rw [continuous_coinduced_dom]
  have hcomp : mapConfig f ∘ @unordered k = @unordered k ∘ (fun (x : Fin k → ℂ) i => f (x i)) := by
    ext x : 1
    apply Subtype.ext
    change (unordered x).val.map f = (unordered (fun i => f (x i))).val
    rw [unordered_val_eq, unordered_val_eq, Multiset.map_map]
    rfl
  rw [hcomp]
  exact continuous_coinduced_rng.comp (continuous_pi fun i => hf.comp (continuous_apply i))

private lemma points_mapConfig (f : ℂ → ℂ) {k : ℕ} (S : Config k) :
    points (mapConfig f S) = f '' points S := by
  ext w
  simp [points, mapConfig]

private noncomputable def F2 (n : ℕ) : Config (n + 1) → Config n :=
  fun S => mapConfig unstretchLin (derivMap n (mapConfig stretchLin S))

private lemma F2_admissible (n : ℕ) : admissible (F2 n) := by
  have hSinj : Function.Injective stretchLin :=
    Function.LeftInverse.injective unstretch_stretch
  have hUinj : Function.Injective unstretchLin :=
    Function.LeftInverse.injective stretch_unstretch
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (mapConfig_continuous unstretch_continuous n).comp
      ((derivMap_continuous n).comp (mapConfig_continuous stretch_continuous (n + 1)))
  · intro T
    obtain ⟨S', hS'⟩ := derivMap_surjective n (mapConfig stretchLin T)
    refine ⟨mapConfig unstretchLin S', ?_⟩
    have h1 : mapConfig stretchLin (mapConfig unstretchLin S') = S' := by
      apply Subtype.ext
      simp [mapConfig, stretch_unstretch]
    have h2 : mapConfig unstretchLin (mapConfig stretchLin T) = T := by
      apply Subtype.ext
      simp [mapConfig, unstretch_stretch]
    simp [F2, h1, hS', h2]
  · intro S
    have hch := derivMap_convexHull (mapConfig stretchLin S)
    rw [F2, points_mapConfig, ← unstretchLin.image_convexHull]
    have hsub := Set.image_mono (f := unstretchLin) hch
    refine hsub.trans ?_
    rw [points_mapConfig, ← stretchLin.image_convexHull, ← Set.image_comp]
    have hcomp : (unstretchLin : ℂ → ℂ) ∘ stretchLin = id := funext unstretch_stretch
    rw [hcomp, Set.image_id]
  · intro S z hz
    have hAz : stretchLin z ∈ mapConfig stretchLin S :=
      Multiset.mem_map_of_mem stretchLin hz
    have hmult := derivMap_mult (mapConfig stretchLin S) (stretchLin z) hAz
    change ((derivMap n (mapConfig stretchLin S)).val.map unstretchLin).count z + 1 = S.val.count z
    have h1 : ((derivMap n (mapConfig stretchLin S)).val.map unstretchLin).count z =
        (derivMap n (mapConfig stretchLin S)).val.count (stretchLin z) := by
      conv_lhs => rw [← unstretch_stretch z]
      exact Multiset.count_map_eq_count' unstretchLin _ hUinj (stretchLin z)
    have h2 : (mapConfig stretchLin S).val.count (stretchLin z) = S.val.count z :=
      Multiset.count_map_eq_count' stretchLin S.val hSinj z
    rw [h1, hmult, h2]

/-! ### Newton / Vieta helper for sum of squares of roots -/

private lemma multiset_prod_X_sub_C_coeffs (s : Multiset ℂ) :
    ((s.map (fun z => X - C z)).prod.coeff s.card = 1) ∧
    (1 ≤ s.card → (s.map (fun z => X - C z)).prod.coeff (s.card - 1) = - s.sum) ∧
    (2 ≤ s.card → 2 * (s.map (fun z => X - C z)).prod.coeff (s.card - 2) =
      s.sum ^ 2 - (s.map (fun z => z ^ 2)).sum) := by
  induction s using Multiset.induction_on with
  | empty =>
    simp
  | cons a s ih =>
    rcases ih with ⟨hlead, h1, h2⟩
    set P := (s.map (fun z => X - C z)).prod
    have hcons : ((a ::ₘ s).map (fun z => X - C z)).prod = (X - C a) * P := by
      simp [P]
    have hcard : (a ::ₘ s).card = s.card + 1 := Multiset.card_cons a s
    refine ⟨?_, ?_, ?_⟩
    · rw [hcons, hcard, sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul,
        Polynomial.coeff_C_mul, hlead]
      have hzero : P.coeff (s.card + 1) = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        have hdeg : P.natDegree = s.card := by
          have := IsAlgClosed.card_roots_eq_natDegree (p := P)
          rw [Polynomial.roots_multiset_prod_X_sub_C] at this
          exact this.symm
        omega
      rw [hzero, mul_zero, sub_zero]
    · intro _
      rw [hcons, hcard, Nat.add_sub_cancel, sub_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
        hlead, mul_one, Multiset.sum_cons]
      cases hsc : s.card with
      | zero =>
        have hs0 : s = 0 := Multiset.card_eq_zero.mp hsc
        subst hs0
        simp [P]
      | succ m =>
        rw [Polynomial.coeff_X_mul]
        have hm := h1 (by omega)
        rw [hsc, Nat.add_sub_cancel] at hm
        rw [hm]
        ring
    · intro hge
      rw [hcons, hcard]
      have hsc_pos : 1 ≤ s.card := by omega
      have hidx : s.card + 1 - 2 = s.card - 1 := by omega
      rw [hidx, sub_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Multiset.sum_cons,
        Multiset.map_cons, Multiset.sum_cons]
      cases hsc : s.card with
      | zero => omega
      | succ m =>
        cases m with
        | zero =>
          rw [Nat.sub_self, Polynomial.coeff_X_mul_zero]
          have hm := h1 (by omega)
          rw [hsc, Nat.sub_self] at hm
          rw [hm]
          obtain ⟨b, rfl⟩ := Multiset.card_eq_one.mp hsc
          simp
          ring
        | succ k =>
          have hsub : k + 1 + 1 - 1 = k + 1 := by omega
          rw [hsub, Polynomial.coeff_X_mul]
          have hm1 := h1 (by omega)
          have hm2 := h2 (by omega)
          rw [hsc] at hm1 hm2
          simp only [Nat.add_sub_cancel] at hm1
          have hsub2 : k + 1 + 1 - 2 = k := by omega
          rw [hsub2] at hm2
          rw [hm1]
          linear_combination hm2

private lemma stretch_eq_comb (z : ℂ) :
    stretchLin z = (3 / 2 : ℂ) * z + (1 / 2 : ℂ) * star z := by
  apply Complex.ext
  · simp [stretchLin]
    ring
  · simp [stretchLin]
    ring

private lemma F2_not_differentiates (n : ℕ) (hn : 2 ≤ n) : ¬ differentiates (F2 n) := by
  intro hdiff
  set m := n + 1
  have hm3 : 3 ≤ m := by omega
  have hm0 : m ≠ 0 := by omega
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / m)
  have hζ : IsPrimitiveRoot ζ m := Complex.isPrimitiveRoot_exp m hm0
  let x : Fin m → ℂ := fun k => ζ ^ k.val
  let S : Config m := unordered x
  have hP_roots : S.val = (X ^ m - 1 : ℂ[X]).roots := by
    have hPne : (X ^ m - 1 : ℂ[X]) ≠ 0 := by
      intro h0
      have := congrArg (fun p : ℂ[X] => p.coeff m) h0
      simp [Polynomial.coeff_one] at this
    have hPdeg : (X ^ m - 1 : ℂ[X]).natDegree = m := Polynomial.natDegree_X_pow_sub_C
    have hPcard : (X ^ m - 1 : ℂ[X]).roots.card = m := by
      rw [IsAlgClosed.card_roots_eq_natDegree, hPdeg]
    have hnodup : S.val.Nodup := by
      rw [unordered_val_eq]
      apply Multiset.Nodup.map_on
      · intro i _ j _ hij
        exact Fin.ext (hζ.injOn_pow
          (Finset.mem_coe.mpr (Finset.mem_range.mpr i.isLt))
          (Finset.mem_coe.mpr (Finset.mem_range.mpr j.isLt)) hij)
      · exact Finset.univ.nodup
    have hle : S.val ≤ (X ^ m - 1 : ℂ[X]).roots := by
      rw [Multiset.le_iff_subset hnodup]
      intro z hz
      rw [unordered_val_eq, Multiset.mem_map] at hz
      rcases hz with ⟨k, _, rfl⟩
      rw [Polynomial.mem_roots hPne, Polynomial.IsRoot.def]
      simp only [x, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, sub_self]
    exact Multiset.eq_of_le_of_card_le hle (by rw [hPcard, S.2])
  have hP : rootPoly S = X ^ m - 1 := by
    unfold rootPoly
    rw [hP_roots]
    exact Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq
      (Polynomial.monic_X_pow_sub_C 1 hm0) IsAlgClosed.card_roots_eq_natDegree
  have hP'_roots : (rootPoly S).derivative.roots = Multiset.replicate n 0 := by
    rw [hP, Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_one,
      sub_zero, Polynomial.roots_C_mul _ (Nat.cast_ne_zero.mpr hm0), Polynomial.roots_X_pow]
    simpa [m] using Multiset.nsmul_singleton (0 : ℂ) n
  have hFS : (F2 n S).val = Multiset.replicate n 0 := by
    rw [hdiff S, hP'_roots]
  have hDAS : (derivMap n (mapConfig stretchLin S)).val = Multiset.replicate n 0 := by
    have hmap := congrArg (Multiset.map stretchLin) hFS
    simpa [F2, mapConfig, Multiset.map_map, stretch_unstretch] using hmap
  set Q := rootPoly (mapConfig stretchLin S)
  have hQ'_roots : Q.derivative.roots = Multiset.replicate n 0 := hDAS
  have hQ'_eq : C ((m : ℂ)⁻¹) * Q.derivative = X ^ n := by
    have h1 := rootPoly_derivMap (mapConfig stretchLin S)
    have h2 : rootPoly (derivMap n (mapConfig stretchLin S)) = X ^ n := by
      unfold rootPoly
      rw [hDAS, Multiset.map_replicate, Multiset.prod_replicate]
      simp
    rw [h2] at h1
    simpa [m, Q] using h1.symm
  have hQ' : Q.derivative = C (m : ℂ) * X ^ n := by
    have hm_ne : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm0
    calc
      Q.derivative = C (m : ℂ) * (C ((m : ℂ)⁻¹) * Q.derivative) := by
        rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hm_ne, map_one, one_mul]
      _ = C (m : ℂ) * X ^ n := by rw [hQ'_eq]
  have hQn : Q.coeff n = 0 := by
    have hc := congrArg (fun p : ℂ[X] => p.coeff (n - 1)) hQ'
    rw [Polynomial.coeff_derivative, Nat.sub_add_cancel (by omega : 1 ≤ n),
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] at hc
    have hne_idx : n - 1 ≠ n := by omega
    simp only [hne_idx, ↓reduceIte, mul_zero] at hc
    have hn_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hcast : ((n - 1 : ℕ) : ℂ) + 1 = (n : ℂ) := by
      exact_mod_cast (show n - 1 + 1 = n by omega)
    rw [hcast] at hc
    exact (mul_eq_zero.mp (by simpa [mul_comm] using hc)).resolve_left hn_ne
  have hQn1 : Q.coeff (n - 1) = 0 := by
    have hc := congrArg (fun p : ℂ[X] => p.coeff (n - 2)) hQ'
    rw [Polynomial.coeff_derivative,
      show n - 2 + 1 = n - 1 by omega,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] at hc
    have hne_idx : n - 2 ≠ n := by omega
    simp only [hne_idx, ↓reduceIte, mul_zero] at hc
    have hn1_ne : ((n - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hcast : ((n - 2 : ℕ) : ℂ) + 1 = ((n - 1 : ℕ) : ℂ) := by
      exact_mod_cast (show n - 2 + 1 = n - 1 by omega)
    rw [hcast] at hc
    exact (mul_eq_zero.mp (by simpa [mul_comm] using hc)).resolve_left hn1_ne
  set T : Multiset ℂ := (mapConfig stretchLin S).val
  have hTcard : T.card = m := (mapConfig stretchLin S).2
  have hvieta := multiset_prod_X_sub_C_coeffs T
  have hTsum : T.sum = 0 := by
    have hv1 := hvieta.2.1 (by omega)
    rw [hTcard, show m - 1 = n by omega] at hv1
    change Q.coeff n = - T.sum at hv1
    rw [hQn] at hv1
    exact neg_eq_zero.mp hv1.symm
  have hTsq : (T.map (fun z => z ^ 2)).sum = 0 := by
    have hv2 := hvieta.2.2 (by omega)
    rw [hTcard, show m - 2 = n - 1 by omega] at hv2
    change 2 * Q.coeff (n - 1) = T.sum ^ 2 - (T.map (fun z => z ^ 2)).sum at hv2
    rw [hQn1, hTsum] at hv2
    linear_combination hv2
  have hTsq_fin : (∑ k : Fin m, (stretchLin (ζ ^ k.val)) ^ 2) = 0 := by
    have hTval : T = Finset.univ.val.map (fun k : Fin m => stretchLin (ζ ^ k.val)) := by
      change (unordered x).val.map stretchLin = _
      rw [unordered_val_eq, Multiset.map_map]
      rfl
    rw [hTval, Multiset.map_map] at hTsq
    exact hTsq
  have hζ_norm : ‖ζ‖ = 1 := by
    have harg : (2 * Real.pi * Complex.I / m : ℂ) = (((2 * Real.pi / m : ℝ) : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [show ζ = Complex.exp (2 * Real.pi * Complex.I / m) from rfl, harg]
    exact Complex.norm_exp_ofReal_mul_I _
  have hζ_star : star ζ = ζ⁻¹ := by
    have hmul : ζ * star ζ = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ_norm]
      simp
    have hne : ζ ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hζ_norm
      norm_num at hζ_norm
    exact eq_inv_of_mul_eq_one_right hmul
  have hgeom : ∀ r : ℂ, r ≠ 1 → r ^ m = 1 → (∑ k : Fin m, r ^ k.val) = 0 := by
    intro r hr1 hrm
    rw [Fin.sum_univ_eq_sum_range]
    have hmul := geom_sum_mul r m
    rw [hrm, sub_self] at hmul
    exact (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr hr1)
  have hζ2_ne : ζ ^ 2 ≠ 1 := by
    intro h1
    have hdvd : m ∣ 2 := hζ.dvd_of_pow_eq_one 2 h1
    have hle : m ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hζ2_pow : (ζ ^ 2) ^ m = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hζi2_ne : (ζ⁻¹) ^ 2 ≠ 1 := by
    intro h1
    apply hζ2_ne
    rw [inv_pow] at h1
    exact inv_eq_one.mp h1
  have hζi2_pow : ((ζ⁻¹) ^ 2) ^ m = 1 := by
    rw [inv_pow, inv_pow, hζ2_pow, inv_one]
  have hcalc : (∑ k : Fin m, (stretchLin (ζ ^ k.val)) ^ 2) = (m : ℂ) * (3 / 2 : ℂ) := by
    have hterm : ∀ k : Fin m,
        (stretchLin (ζ ^ k.val)) ^ 2 =
          (9 / 4 : ℂ) * (ζ ^ 2) ^ k.val + (3 / 2 : ℂ) + (1 / 4 : ℂ) * ((ζ⁻¹) ^ 2) ^ k.val := by
      intro k
      rw [stretch_eq_comb, star_pow, hζ_star]
      have hζne : ζ ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hζ_norm
        norm_num at hζ_norm
      have hprod : ζ ^ k.val * (ζ⁻¹) ^ k.val = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ hζne, one_pow]
      have hp1 : (ζ ^ k.val) ^ 2 = (ζ ^ 2) ^ k.val := by
        rw [← pow_mul, mul_comm, pow_mul]
      have hp2 : ((ζ⁻¹) ^ k.val) ^ 2 = ((ζ⁻¹) ^ 2) ^ k.val := by
        rw [← pow_mul, mul_comm, pow_mul]
      calc
        ((3 / 2 : ℂ) * ζ ^ k.val + (1 / 2 : ℂ) * (ζ⁻¹) ^ k.val) ^ 2
            = (9 / 4 : ℂ) * (ζ ^ k.val) ^ 2 + (3 / 2 : ℂ) * (ζ ^ k.val * (ζ⁻¹) ^ k.val) +
                (1 / 4 : ℂ) * ((ζ⁻¹) ^ k.val) ^ 2 := by ring
        _ = (9 / 4 : ℂ) * (ζ ^ 2) ^ k.val + (3 / 2 : ℂ) + (1 / 4 : ℂ) * ((ζ⁻¹) ^ 2) ^ k.val := by
            rw [hp1, hp2, hprod, mul_one]
    simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hgeom (ζ ^ 2) hζ2_ne hζ2_pow, hgeom ((ζ⁻¹) ^ 2) hζi2_ne hζi2_pow]
    simp
  rw [hcalc] at hTsq_fin
  have hm_ne : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm0
  have h32 : (3 / 2 : ℂ) ≠ 0 := by norm_num
  exact mul_ne_zero hm_ne h32 hTsq_fin

end OMA.S_mo_402743_Proof

theorem OMA.solution : type_of% @OMA.S_mo_402743.main := by
  intro n hn
  by_cases h1 : n = 1
  · subst h1
    exact ⟨OMA.S_mo_402743_Proof.derivMap 1, OMA.S_mo_402743_Proof.F1,
      OMA.S_mo_402743_Proof.derivMap_admissible 1,
      OMA.S_mo_402743_Proof.derivMap_differentiates 1,
      OMA.S_mo_402743_Proof.F1_admissible,
      OMA.S_mo_402743_Proof.F1_not_differentiates⟩
  · have hn2 : 2 ≤ n := by omega
    exact ⟨OMA.S_mo_402743_Proof.derivMap n, OMA.S_mo_402743_Proof.F2 n,
      OMA.S_mo_402743_Proof.derivMap_admissible n,
      OMA.S_mo_402743_Proof.derivMap_differentiates n,
      OMA.S_mo_402743_Proof.F2_admissible n,
      OMA.S_mo_402743_Proof.F2_not_differentiates n hn2⟩
