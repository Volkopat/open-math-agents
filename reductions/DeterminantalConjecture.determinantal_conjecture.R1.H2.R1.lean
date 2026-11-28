import OMAReductions.R_DeterminantalConjecture_determinantal_conjecture_R1

/-!
The H2 support problem reduces to a fixed real-direction test after erasing one row.
A reciprocal change of eigenvalues fills the erased row, while a rescaled limit
recovers any retained row set. The three-dimensional case is proved directly.
-/

open scoped BigOperators

namespace OMA.R_DeterminantalConjecture_determinantal_conjecture_R1_H2_R1


private theorem hull_of_family_eq_image {ι : Type} [Fintype ι]
    (v : ι → ℂ) :
    convexHull ℝ (Set.range v) =
      Set.range (fun t : stdSimplex ℝ ι => ∑ i, (t.val i) • v i) := by
  classical
  let L : (ι → ℝ) →ₗ[ℝ] ℂ :=
    ∑ i, (LinearMap.proj (R := ℝ) i).smulRight (v i)
  have happ (t : ι → ℝ) : L t = ∑ i, t i • v i := by
    simp [L, LinearMap.sum_apply]
  have he (i : ι) : L (fun j => if i = j then (1 : ℝ) else 0) = v i := by
    rw [happ]
    simp [ite_smul]
  calc
    convexHull ℝ (Set.range v) = L '' stdSimplex ℝ ι := by
      rw [← convexHull_basis_eq_stdSimplex ℝ ι, L.image_convexHull, ← Set.range_comp]
      rw [show (L ∘ fun (i : ι) (j : ι) => if i = j then (1 : ℝ) else 0) = v from funext he]
    _ = _ := by
      rw [Set.image_eq_range]
      simp only [happ]

private theorem isClosed_in_finite_hull {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (v : X → ι → ℂ) (contv : ∀ i, Continuous (v · i))
    (y : X → ℂ) (conty : Continuous y) :
    IsClosed {x | y x ∈ convexHull ℝ (Set.range (v x))} := by
  rw [show {x | y x ∈ convexHull ℝ (Set.range (v x))} =
      Prod.fst '' {p : X × stdSimplex ℝ ι | y p.1 = ∑ i, (p.2.val i) • v p.1 i} by
    ext x
    simp only [Set.mem_ofPred_eq, hull_of_family_eq_image, Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨(x,t), ht.symm, rfl⟩
    · rintro ⟨⟨z,t⟩, ht, rfl⟩
      exact ⟨t, ht.symm⟩]
  apply isClosedMap_fst_of_compactSpace
  apply isClosed_eq (conty.comp continuous_fst)
  exact continuous_finsetSum _ fun i _ =>
    (((continuous_apply i).comp continuous_subtype_val).comp continuous_snd).smul
      ((contv i).comp continuous_fst)

/-- A limit of rescaled full products gives the product on any retained row set. -/
theorem retained_of_full {n : Type} [Fintype n] [DecidableEq n]
    (w : Equiv.Perm n → ℝ)
    (h : ∀ a b : n → ℂ, (∑ σ, w σ • (∏ i, (a i + b (σ i))))
      ∈ convexHull ℝ (Set.range fun (σ : Equiv.Perm n) => ∏ i, (a i + b (σ i))))
    (a b : n → ℂ) (T : Finset n) :
    (∑ σ, w σ • (∏ i ∈ T, (a i + b (σ i)))) ∈
      convexHull ℝ (Set.range fun (σ : Equiv.Perm n) => ∏ i ∈ T, (a i + b (σ i))) := by
  classical
  let p (t : ℂ) (σ : Equiv.Perm n) :=
    ∏ i, if i ∈ T then a i + b (σ i) else 1 + t * b (σ i)
  let y (t : ℂ) := ∑ σ, w σ • p t σ
  let good : Set ℂ := {t | y t ∈ convexHull ℝ (Set.range (p t))}
  have hcont (σ : Equiv.Perm n) : Continuous (p · σ) := by
    apply continuous_finsetProd
    intro i _
    by_cases hi : i ∈ T
    · simp only [hi, if_true]
      exact continuous_const
    · simp only [hi, if_false]
      fun_prop
  have hc : IsClosed good := isClosed_in_finite_hull p hcont y <|
    continuous_finsetSum _ fun σ _ => (hcont σ).const_smul (w σ)
  have hgood : ({0} : Set ℂ)ᶜ ⊆ good := by
    intro t ht
    have ht' : t ≠ 0 := ht
    let A (i : n) := if i ∈ T then a i else t⁻¹
    let C : ℂ := ∏ i : n, if i ∈ T then 1 else t
    let L := LinearMap.mulLeft ℝ C
    let Z (σ : Equiv.Perm n) := ∏ i, (A i + b (σ i))
    have hp (σ : Equiv.Perm n) : p t σ = L (Z σ) := by
      change (∏ i, if i ∈ T then a i + b (σ i) else 1 + t * b (σ i)) =
        (∏ i : n, if i ∈ T then 1 else t) * ∏ i, ((if i ∈ T then a i else t⁻¹) + b (σ i))
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      by_cases hi : i ∈ T
      · simp [hi]
      · simp [hi, mul_add, ht']
    change (∑ σ, w σ • p t σ) ∈ convexHull ℝ (Set.range (p t))
    simp_rw [hp, ← map_smul, ← map_sum]
    rw [show p t = L ∘ Z from funext hp, Set.range_comp, ← L.image_convexHull]
    exact ⟨_, h A b, rfl⟩
  have hd : Dense (({0} : Set ℂ)ᶜ) := (Set.countable_singleton _).dense_compl ℝ
  have hm := closure_minimal hgood hc (hd (0 : ℂ))
  have hp0 (σ : Equiv.Perm n) : p 0 σ = ∏ i ∈ T, (a i + b (σ i)) := by
    simp [p, Finset.prod_ite_mem]
  simpa only [good, Set.mem_ofPred_eq, y, hp0,
    show p 0 = _ from funext hp0] using hm

private theorem real_linear_complex (f : ℂ →ₗ[ℝ] ℝ) (z : ℂ) :
    f z = ((⟨f 1, -f Complex.I⟩ : ℂ) * z).re := by
  have hz : z.re • (1 : ℂ) + z.im • Complex.I = z := by
    apply Complex.ext <;> simp
  calc
    f z = f (z.re • (1 : ℂ) + z.im • Complex.I) := congrArg f hz.symm
    _ = _ := by
      rw [map_add, map_smul, map_smul]
      simp [Complex.mul_re, smul_eq_mul]; ring

/-- A real linear functional which sees the second complex coordinate factors
through evaluation at one complex scalar. -/
theorem factor_support (f : (ℂ × ℂ) →ₗ[ℝ] ℝ) (hf : ∃ z : ℂ, f (0,z) ≠ 0) :
    ∃ c : ℂ, ∃ g : ℂ →ₗ[ℝ] ℝ, ∀ p q : ℂ, f (p,q) = g (c * p + q) := by
  let f₁ := f.comp (LinearMap.inl ℝ ℂ ℂ)
  let f₂ := f.comp (LinearMap.inr ℝ ℂ ℂ)
  let α : ℂ := ⟨f₁ 1, -f₁ Complex.I⟩
  let β : ℂ := ⟨f₂ 1, -f₂ Complex.I⟩
  have hα (z : ℂ) : f (z,0) = (α * z).re := real_linear_complex f₁ z
  have hβ (z : ℂ) : f (0,z) = (β * z).re := real_linear_complex f₂ z
  have hβ₀ : β ≠ 0 := by
    obtain ⟨z, hz⟩ := hf
    intro h
    exact hz (by rw [hβ, h]; simp)
  let g := Complex.reLm.comp (LinearMap.mulLeft ℝ β)
  refine ⟨α / β, g, fun p q => ?_⟩
  have hpq : (p,q) = (p,0) + (0,q) := by simp
  conv_lhs => rw [hpq, map_add, hα, hβ, ← Complex.add_re]
  change (α * p + β * q).re = (β * (α / β * p + q)).re
  congr 1
  field_simp [hβ₀]

theorem signed_mass_one {n : Type} [Fintype n] [DecidableEq n]
    (U : unitary (Matrix n n ℂ)) :
    (∑ σ : Equiv.Perm n,
      (((Equiv.Perm.sign σ : ℤ) : ℂ) * (∏ i, U.val i (σ i)) * (star U.val).det).re) = 1 := by
  have h := congrArg Matrix.det (Unitary.coe_mul_star_self U)
  simp only [Matrix.det_mul, Matrix.det_one] at h
  rw [← Matrix.det_transpose U.val, Matrix.det_apply', Finset.sum_mul] at h
  simpa only [Complex.re_sum, Matrix.transpose_apply, Complex.one_re, mul_assoc,
    Unitary.coe_star] using
    congrArg Complex.re h

/-- The retained-row signed hull statement implies every H2 test, by taking
the supporting functional at the eigenvalue encoded by its complex slope. -/
theorem H2_of_retained
    (h : ∀ (n : Type) [Fintype n] [DecidableEq n], 3 ≤ Fintype.card n →
      ∀ (U : unitary (Matrix n n ℂ)) (_k : n)
      (a b : n → ℂ) (T : Finset n),
      let w (σ : Equiv.Perm n) :=
        (((Equiv.Perm.sign σ : ℤ) : ℂ) * (∏ i, U.val i (σ i)) * (star U.val).det).re
      (∑ σ, w σ • (∏ i ∈ T, (a i + b (σ i)))) ∈
        convexHull ℝ (Set.range fun (σ : Equiv.Perm n) => ∏ i ∈ T, (a i + b (σ i)))) :
    OMA.R_DeterminantalConjecture_determinantal_conjecture_R1.H2 := by
  classical
  intro n _ _ a b U T k hT hk
  have hn : 3 ≤ Fintype.card n := hT.trans (Finset.card_le_univ T)
  dsimp only
  intro f s hf hmax _ _ _
  let p (σ : Equiv.Perm n) := ∏ i ∈ T.erase k, (a i + b (σ i))
  let v (σ : Equiv.Perm n) := (p σ, b (σ k) * p σ)
  let w (σ : Equiv.Perm n) :=
    (((Equiv.Perm.sign σ : ℤ) : ℂ) * (∏ i, U.val i (σ i)) * (star U.val).det).re
  change ∀ σ, f (v σ) ≤ f (v s) at hmax
  change 0 ≤ ∑ σ, w σ * (f (v s) - f (v σ))
  obtain ⟨c, g, hg⟩ := factor_support f hf
  let A := Function.update a k c
  let z (σ : Equiv.Perm n) := ∏ i ∈ T, (A i + b (σ i))
  have heval (σ : Equiv.Perm n) : g (z σ) = f (v σ) := by
    rw [show z σ = (A k + b (σ k)) * ∏ i ∈ T.erase k, (A i + b (σ i)) from
      (Finset.mul_prod_erase _ _ hk).symm]
    have hp : (∏ i ∈ T.erase k, (A i + b (σ i))) = p σ :=
      Finset.prod_congr rfl (fun i hi => by
        simp [A, Function.update_of_ne (Finset.ne_of_mem_erase hi)])
    rw [hp, show A k = c from Function.update_self _ _ _, add_mul]
    exact (hg _ _).symm
  have hmem : (∑ σ, w σ • z σ) ∈ convexHull ℝ (Set.range z) := h n hn U k A b T
  let S : Set ℂ := {x | g x ≤ f (v s)}
  have hS : Set.range z ⊆ S := by
    rintro _ ⟨σ, rfl⟩
    exact (heval σ).trans_le (hmax σ)
  have hgood : g (∑ σ, w σ • z σ) ≤ f (v s) :=
    convexHull_min hS (convex_halfSpace_le g.isLinear _) hmem
  rw [map_sum] at hgood
  simp only [map_smul, smul_eq_mul, heval] at hgood
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    show (∑ σ, w σ) = 1 from signed_mass_one U, one_mul]
  exact sub_nonneg.mpr hgood

/-- For a nonempty set of retained rows, one fixed real-part inequality for
all spectra suffices to control every real direction by simultaneous scaling. -/
theorem hull_of_real_support {n : Type} [Fintype n] [DecidableEq n]
    (w : Equiv.Perm n → ℝ) (T : Finset n) (hT : 0 < T.card)
    (h : ∀ a b : n → ℂ, ∃ σ : Equiv.Perm n,
      (∑ τ, w τ • (∏ i ∈ T, (a i + b (τ i)))).re ≤
        (∏ i ∈ T, (a i + b (σ i))).re)
    (a b : n → ℂ) :
    (∑ σ, w σ • (∏ i ∈ T, (a i + b (σ i)))) ∈ convexHull ℝ
      (Set.range fun (σ : Equiv.Perm n) => ∏ i ∈ T, (a i + b (σ i))) := by
  classical
  let p (σ : Equiv.Perm n) : ℂ := ∏ i ∈ T, (a i + b (σ i))
  let z : ℂ := ∑ σ, w σ • p σ
  change z ∈ convexHull ℝ (Set.range p)
  by_contra hz
  obtain ⟨F, u, hvertices, hu⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (Set.range p)) ((Set.finite_range p).isCompact_convexHull ℝ).isClosed hz
  let c : ℂ := ⟨F 1, -F Complex.I⟩
  have heval (v : ℂ) : F v = (c * v).re := real_linear_complex F.toLinearMap v
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq c hT
  let L := LinearMap.mulLeft ℝ c
  have hp (σ : Equiv.Perm n) :
      (∏ i ∈ T, (r * a i + r * b (σ i))) = L (p σ) := by
    change (∏ i ∈ T, (r * a i + r * b (σ i))) = c * (∏ i ∈ T, (a i + b (σ i)))
    simp_rw [← mul_add]
    rw [Finset.prod_mul_distrib, Finset.prod_const, hr]
  obtain ⟨σ, hσ⟩ := h (fun i => r * a i) (fun i => r * b i)
  simp only [hp, ← map_smul, ← map_sum] at hσ
  change (c * z).re ≤ (c * p σ).re at hσ
  rw [← heval, ← heval] at hσ
  exact (not_le_of_gt ((hvertices (p σ) (subset_convexHull ℝ _ ⟨σ, rfl⟩)).trans hu)) hσ

private theorem reciprocal_product {n : Type} [Fintype n] [DecidableEq n]
    (a b : n → ℂ) (k : n) (ha : ∀ i ≠ k, a i ≠ a k)
    (hb : ∀ j, b j + a k ≠ 0) (σ : Equiv.Perm n) :
    (∏ i, (a i + b (σ i))) =
      ((∏ i ∈ Finset.univ.erase k, (a i - a k)) * (∏ j, (b j + a k))) *
        ∏ i ∈ Finset.univ.erase k, ((a i - a k)⁻¹ + (b (σ i) + a k)⁻¹) := by
  classical
  let C (i : n) := a i - a k
  let D (i : n) := b i + a k
  change (∏ i, (a i + b (σ i))) =
    ((∏ i ∈ Finset.univ.erase k, C i) * (∏ j, D j)) *
      ∏ i ∈ Finset.univ.erase k, ((C i)⁻¹ + (D (σ i))⁻¹)
  have he (i : n) (hi : i ∈ Finset.univ.erase k) :
      a i + b (σ i) = (C i * D (σ i)) * ((C i)⁻¹ + (D (σ i))⁻¹) := by
    have hc : C i ≠ 0 := sub_ne_zero.mpr (ha i (Finset.ne_of_mem_erase hi))
    have hd : D (σ i) ≠ 0 := hb _
    calc
      a i + b (σ i) = C i + D (σ i) := by unfold C D; ring
      _ = _ := by field_simp; exact add_comm _ _
  rw [← Equiv.prod_comp σ D,
    ← Finset.mul_prod_erase _ (fun i => D (σ i)) (Finset.mem_univ k),
    ← Finset.mul_prod_erase _ (fun i => a i + b (σ i)) (Finset.mem_univ k)]
  have hk : a k + b (σ k) = D (σ k) := add_comm _ _
  rw [hk]
  rw [Finset.prod_congr rfl (fun i hi => he i hi)]
  simp only [Finset.prod_mul_distrib]
  ring

private theorem hull_reciprocal_generic {n : Type} [Fintype n] [DecidableEq n]
    (a b : n → ℂ) (w : Equiv.Perm n → ℝ) (k : n)
    (ha : ∀ i ≠ k, a i ≠ a k) (hb : ∀ j, b j + a k ≠ 0)
    (h : ∑ σ, w σ • (∏ i ∈ Finset.univ.erase k,
      ((a i - a k)⁻¹ + (b (σ i) + a k)⁻¹)) ∈ convexHull ℝ
        (Set.range fun (σ : Equiv.Perm n) =>
          ∏ i ∈ Finset.univ.erase k, ((a i - a k)⁻¹ + (b (σ i) + a k)⁻¹))) :
    (∑ σ, w σ • (∏ i, (a i + b (σ i)))) ∈ convexHull ℝ
      (Set.range fun (σ : Equiv.Perm n) => ∏ i, (a i + b (σ i))) := by
  let C := ((∏ i ∈ Finset.univ.erase k, (a i - a k)) * (∏ j, (b j + a k)))
  let p (σ : Equiv.Perm n) := ∏ i ∈ Finset.univ.erase k, ((a i - a k)⁻¹ + (b (σ i) + a k)⁻¹)
  let L : ℂ →ₗ[ℝ] ℂ := LinearMap.mulLeft ℝ C
  have hp (σ : Equiv.Perm n) : (∏ i, (a i + b (σ i))) = L (p σ) :=
    reciprocal_product a b k ha hb σ
  simp_rw [hp, ← map_smul, ← map_sum]
  rw [← Function.comp_def L p, Set.range_comp, ← L.image_convexHull]
  exact ⟨_, h, rfl⟩

theorem hull_of_one_erased_row {n : Type} [Fintype n] [DecidableEq n]
    (w : Equiv.Perm n → ℝ) (k : n)
    (h : ∀ a b : n → ℂ, (∑ σ, w σ • (∏ i ∈ Finset.univ.erase k, (a i + b (σ i))))
      ∈ convexHull ℝ (Set.range fun (σ : Equiv.Perm n) =>
        ∏ i ∈ Finset.univ.erase k, (a i + b (σ i)))) :
    ∀ a b : n → ℂ,
      (∑ σ, w σ • (∏ i, (a i + b (σ i)))) ∈ convexHull ℝ
        (Set.range fun (σ : Equiv.Perm n) => ∏ i, (a i + b (σ i))) := by
  intro a b
  let p (z : ℂ) (σ : Equiv.Perm n) := ∏ i, (Function.update a k z i + b (σ i))
  let y (z : ℂ) := ∑ σ, w σ • p z σ
  let excluded : Set ℂ :=
    (Finset.univ.erase k).image a ∪ (Finset.univ.image fun j => - b j)
  let admitted : Set ℂ := {z | y z ∈ convexHull ℝ (Set.range (p z))}
  have hd : Dense excludedᶜ := by
    apply Set.Countable.dense_compl ℝ
    exact (Finset.finite_toSet _).union (Finset.finite_toSet _) |>.countable
  have hcont (σ : Equiv.Perm n) : Continuous (p · σ) := by
    apply continuous_finsetProd
    intro i _
    apply Continuous.add _ continuous_const
    by_cases hi : i = k
    · subst i
      simp only [Function.update_self]
      change Continuous (id : ℂ → ℂ)
      exact continuous_id
    · simpa only [Function.update_of_ne hi] using
        (continuous_const : Continuous fun _ : ℂ => a i)
  have hc : IsClosed admitted := isClosed_in_finite_hull p hcont y <|
    continuous_finsetSum _ fun σ _ => (hcont σ).const_smul (w σ)
  have hreg : excludedᶜ ⊆ admitted := by
    intro z hz
    have ha (i : n) (hi : i ≠ k) : Function.update a k z i ≠ Function.update a k z k := by
      rw [Function.update_of_ne hi, Function.update_self]
      intro e
      apply hz
      exact Or.inl (Finset.mem_image.mpr ⟨i, by simp [hi], e⟩)
    have hb (j : n) : b j + Function.update a k z k ≠ 0 := by
      rw [Function.update_self]
      intro e
      apply hz
      refine Or.inr (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩)
      exact (eq_neg_of_add_eq_zero_right e).symm
    exact hull_reciprocal_generic (Function.update a k z) b w k ha hb
      (h (fun i => (Function.update a k z i - Function.update a k z k)⁻¹)
        (fun j => (b j + Function.update a k z k)⁻¹))
  have hm := closure_minimal hreg hc (hd (a k))
  simpa only [admitted, Set.mem_ofPred_eq, y, p, Function.update_eq_self] using hm

namespace OMAH2Three

private theorem opposite_pair :
    ∀ e o : Equiv.Perm (Fin 3), e 1 = e 0 + 1 → o 1 ≠ o 0 + 1 →
      ∃ i : Fin 3, Finset.univ.filter (fun p : Equiv.Perm (Fin 3) => p i = e i) = {e, o} := by
  decide

private theorem signed_image_count :
    ∀ S J : Finset (Fin 3), (∑ σ : Equiv.Perm (Fin 3),
      if S.image σ = J then (if σ 1 = σ 0 + 1 then (1 : ℤ) else -1) else 0) = 0 := by
  decide

private theorem signed_image_count_real (S J : Finset (Fin 3)) :
    (∑ σ : Equiv.Perm (Fin 3),
      if S.image σ = J then (if σ 1 = σ 0 + 1 then (1 : ℝ) else -1) else 0) = 0 := by
  exact_mod_cast signed_image_count S J

private theorem even_identity : (1 : Equiv.Perm (Fin 3)) 1 = (1 : Equiv.Perm (Fin 3)) 0 + 1 := by decide

private theorem coupling_fin_three
    (w : Equiv.Perm (Fin 3) → ℝ) (hw₁ : (∑ σ, w σ) = 1)
    (hw : ∀ i j : Fin 3, 0 ≤ ∑ σ : Equiv.Perm (Fin 3), if σ i = j then w σ else 0) :
    ∃ t : Equiv.Perm (Fin 3) → ℝ, (∀ σ, 0 ≤ t σ) ∧ (∑ σ, t σ) = 1 ∧
      ∀ S J : Finset (Fin 3),
        (∑ σ : Equiv.Perm (Fin 3), if S.image σ = J then w σ else 0) =
        ∑ σ : Equiv.Perm (Fin 3), if S.image σ = J then t σ else 0 := by
  classical
  let es := Finset.univ.filter (fun σ : Equiv.Perm (Fin 3) => σ 1 = σ 0 + 1)
  obtain ⟨e, he, hm⟩ := es.exists_min_image w ⟨1, by simp [es, even_identity]⟩
  have heven : e 1 = e 0 + 1 := (Finset.mem_filter.mp he).2
  let η (σ : Equiv.Perm (Fin 3)) : ℝ := if σ 1 = σ 0 + 1 then 1 else -1
  let t (σ : Equiv.Perm (Fin 3)) := w σ - w e * η σ
  have hnonneg (σ : Equiv.Perm (Fin 3)) : 0 ≤ t σ := by
    by_cases hs : σ 1 = σ 0 + 1
    · have hle := hm σ (by simp [es, hs])
      simpa [t, η, hs] using sub_nonneg.mpr hle
    · obtain ⟨i, hi⟩ := opposite_pair e σ heven hs
      have hsum := hw i (e i)
      rw [← Finset.sum_filter, hi] at hsum
      have hne : e ≠ σ := fun h => hs (h ▸ heven)
      simp [Finset.sum_pair hne] at hsum
      simp only [t, η, if_neg hs, mul_neg_one]
      linarith only [hsum]
  have hfib (S J : Finset (Fin 3)) :
      (∑ σ : Equiv.Perm (Fin 3), if S.image σ = J then w σ else 0) =
      ∑ σ : Equiv.Perm (Fin 3), if S.image σ = J then t σ else 0 := by
    have heq (σ : Equiv.Perm (Fin 3)) :
      (if S.image σ = J then t σ else 0) = (if S.image σ = J then w σ else 0) -
        w e * (if S.image σ = J then η σ else 0) := by
      split <;> simp [* , t]
    simp_rw [heq, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hzero := signed_image_count_real S J
    change (∑ σ : Equiv.Perm (Fin 3), if S.image σ = J then η σ else 0) = 0 at hzero
    rw [hzero, mul_zero, sub_zero]
  refine ⟨t, hnonneg, ?_, hfib⟩
  have hzero := hfib ∅ ∅
  simp only [Finset.image_empty, ite_true] at hzero
  exact hzero.symm.trans hw₁

theorem coupling_of_card_three {n : Type} [Fintype n] [DecidableEq n]
    (hn : Fintype.card n = 3) (w : Equiv.Perm n → ℝ)
    (hw₁ : (∑ σ, w σ) = 1)
    (hw : ∀ I J : Finset n, 0 ≤ ∑ σ : Equiv.Perm n,
      w σ * (if ∀ i ∈ I, σ i ∈ J then (1 : ℝ) else 0)) :
    ∃ t : Equiv.Perm n → ℝ, (∀ σ, 0 ≤ t σ) ∧ (∑ σ, t σ) = 1 ∧
      ∀ S J : Finset n,
        (∑ σ : Equiv.Perm n, if S.image σ = J then w σ else 0) =
        ∑ σ : Equiv.Perm n, if S.image σ = J then t σ else 0 := by
  classical
  let e := Fintype.equivFinOfCardEq hn
  let p := e.permCongr
  let W (τ : Equiv.Perm (Fin 3)) := w (p.symm τ)
  have hW₁ : (∑ τ, W τ) = 1 := (Equiv.sum_comp p.symm w).trans hw₁
  have hW (i j : Fin 3) : 0 ≤ ∑ τ : Equiv.Perm (Fin 3), if τ i = j then W τ else 0 := by
    rw [← Equiv.sum_comp p (fun τ => if τ i = j then W τ else 0)]
    have htest (σ : Equiv.Perm n) : p σ i = j ↔ σ (e.symm i) = e.symm j := by
      change e (σ (e.symm i)) = j ↔ _
      rw [← e.apply_eq_iff_eq, e.apply_symm_apply]
    simpa [W, htest, mul_ite] using hw {e.symm i} {e.symm j}
  obtain ⟨T, hT, hT₁, hTF⟩ := coupling_fin_three W hW₁ hW
  let t (σ : Equiv.Perm n) := T (p σ)
  refine ⟨t, fun σ => hT (p σ), (Equiv.sum_comp p T).trans hT₁, ?_⟩
  intro S J
  have hF := hTF (S.image e) (J.image e)
  rw [← Equiv.sum_comp p (fun τ => if (S.image e).image τ = J.image e then W τ else 0),
      ← Equiv.sum_comp p (fun τ => if (S.image e).image τ = J.image e then T τ else 0)] at hF
  have hImage (σ : Equiv.Perm n) :
      (S.image e).image (p σ) = J.image e ↔ S.image σ = J := by
    have hcomp : (p σ : Fin 3 → Fin 3) ∘ e = e ∘ σ := by
      funext i
      simp [p, Equiv.permCongr_apply]
    rw [Finset.image_image, hcomp, ← Finset.image_image]
    exact (Finset.image_injective e.injective).eq_iff
  simpa only [hImage, W, Equiv.symm_apply_apply, t] using hF

end OMAH2Three

open Matrix

open scoped ComplexConjugate

private theorem mask_transpose {n : Type} [Fintype n] [DecidableEq n]
    (S : Finset n) (A : Matrix n n ℂ) :
    Matrix.det (fun i => if i ∈ S then A.transpose i else (1 : Matrix n n ℂ) i) =
      Matrix.det (fun i => if i ∈ S then A i else (1 : Matrix n n ℂ) i) := by
  let P : Matrix n n ℂ := diagonal (fun i => if i ∈ S then 1 else 0)
  have mask (M : Matrix n n ℂ) :
      ((fun i => if i ∈ S then M i else (1 : Matrix n n ℂ) i) : Matrix n n ℂ) =
        (1 : Matrix n n ℂ) + P * (M - (1 : Matrix n n ℂ)) := by
    ext i j
    by_cases hi : i ∈ S <;> simp [P, diagonal_mul, hi]
  have hP : P.transpose = P := diagonal_transpose _
  rw [mask, mask, det_one_add_mul_comm, ← det_transpose (1 + (A.transpose - 1) * P)]
  simp only [transpose_add, transpose_one, transpose_mul, transpose_sub, transpose_transpose, hP]

private theorem signed_expansion_complex {n : Type} [Fintype n] [DecidableEq n]
    (V W : Matrix n n ℂ) (hWV : W * V = 1) (a b : n → ℂ) (S : Finset n) :
    let M : Matrix n n ℂ := fun i => if i ∈ S then (diagonal a + V * diagonal b * W) i else (1 : Matrix n n ℂ) i
    M.det = ∑ σ : Equiv.Perm n, (((Equiv.Perm.sign σ : ℤ) : ℂ) *
      (∏ i, V i (σ i)) * W.det) * ∏ i ∈ S, (a i + b (σ i)) := by
  classical
  intro M
  have entries (i j : n) : (M * V) i j = (if i ∈ S then a i + b j else 1) * V i j := by
    have e : (diagonal a + V * diagonal b * W) * V = diagonal a * V + V * diagonal b := by
      rw [add_mul, Matrix.mul_assoc (V * diagonal b), hWV, mul_one]
    by_cases hi : i ∈ S
    · calc
        (M * V) i j = ((diagonal a + V * diagonal b * W) * V) i j := by rw [Matrix.mul_apply, Matrix.mul_apply]; simp only [M, hi, if_true]
        _ = _ := by rw [e]; simp [hi, Matrix.diagonal_mul, Matrix.mul_diagonal]; ring
    · calc
        (M * V) i j = ((1 : Matrix n n ℂ) * V) i j := by rw [Matrix.mul_apply, Matrix.mul_apply]; simp only [M, hi, if_false]
        _ = _ := by simp [hi]
  have hv := congrArg Matrix.det hWV
  simp only [det_mul, det_one] at hv
  calc
    M.det = (M * V).transpose.det * W.det := by rw [det_transpose, det_mul]; linear_combination -M.det * hv
    _ = _ := by
      rw [det_apply', Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro σ _
      simp only [transpose_apply, entries, Finset.prod_mul_distrib]
      rw [Finset.prod_ite_mem]
      simp
      ring

private theorem signed_compression {n : Type} [Fintype n] [DecidableEq n]
    (U : unitary (Matrix n n ℂ)) :
    let w (σ : Equiv.Perm n) :=
      (((Equiv.Perm.sign σ : ℤ) : ℂ) * (∏ i, U.val i (σ i)) * (star U.val).det).re
    (∑ σ, w σ) = 1 ∧
      ∀ (a b : n → ℂ) (S : Finset n),
      let M : Matrix n n ℂ := fun i =>
        if i ∈ S then (diagonal a + U.val * diagonal b * star U.val) i else (1 : Matrix n n ℂ) i
      M.det = ∑ σ, w σ • (∏ i ∈ S, (a i + b (σ i))) := by
  classical
  let V := U.val
  let W := star U.val
  let h (σ : Equiv.Perm n) : ℂ := ((Equiv.Perm.sign σ : ℤ) : ℂ) * (∏ i, V i (σ i)) * W.det
  have hWV : W * V = 1 := Unitary.coe_star_mul_self U
  have hs : ∑ σ, h σ = 1 := by
    have e := signed_expansion_complex V W hWV (fun _ => 0) (fun _ => 0) ∅
    simpa [h] using e.symm
  change (∑ σ, (h σ).re) = 1 ∧ _
  constructor
  · simpa only [Complex.re_sum, Complex.one_re] using congrArg Complex.re hs
  intro a b S M
  let Z (σ : Equiv.Perm n) := ∏ i ∈ S, (a i + b (σ i))
  change M.det = ∑ σ, (h σ).re • Z σ
  have e : M.det = ∑ σ, h σ * Z σ := signed_expansion_complex V W hWV a b S
  have et := signed_expansion_complex W.transpose V.transpose
    (show V.transpose * W.transpose = 1 by rw [← transpose_mul, hWV, transpose_one]) a b S
  have ht : diagonal a + W.transpose * diagonal b * V.transpose =
      (diagonal a + V * diagonal b * W).transpose := by
    simp only [transpose_add, transpose_mul, diagonal_transpose, Matrix.mul_assoc]
  dsimp only at et
  rw [ht, mask_transpose] at et
  have hw (σ : Equiv.Perm n) :
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * (∏ i, W.transpose i (σ i)) * V.transpose.det = conj (h σ) := by
    simp only [h, V, W, Matrix.star_eq_conjTranspose, transpose_apply, conjTranspose_apply,
      det_transpose, det_conjTranspose, map_mul, map_prod, map_intCast, Complex.star_def, Complex.conj_conj]
  change M.det = ∑ σ : Equiv.Perm n, _ * Z σ at et
  simp_rw [hw] at et
  apply (mul_right_inj' (show (2 : ℂ) ≠ 0 by norm_num)).mp
  calc
    2 * M.det = (∑ σ, h σ * Z σ) + (∑ σ, conj (h σ) * Z σ) := by rw [← e, ← et]; ring
    _ = _ := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      rw [← add_mul, Complex.add_conj]
      simp [Complex.real_smul, Z, mul_assoc]

open scoped ComplexOrder NNReal

private theorem compression_nonneg {n : Type} [Fintype n] [DecidableEq n]
    (S : Finset n) (A : Matrix n n ℂ) (ha : A.PosSemidef) :
    0 ≤ Matrix.det (fun i => if i ∈ S then A i else (1 : Matrix n n ℂ) i) := by
  let P : Matrix n n ℂ := diagonal (fun i => if i ∈ S then 1 else 0)
  let Q : Matrix n n ℂ := diagonal (fun i => if i ∈ S then 0 else 1)
  have hPP : P * P = P := by
    ext i j
    by_cases he : i = j
    · subst j; by_cases hi : i ∈ S <;> simp [P, hi]
    · simp [P, he]
  have hQ : Q.PosSemidef := posSemidef_diagonal_iff.mpr (fun i => by split <;> simp)
  have hPstar : P.conjTranspose = P := by
    ext i j
    by_cases he : i = j
    · subst j; by_cases hi : i ∈ S <;> simp [P, hi]
    · simp [P, conjTranspose_apply, he, Ne.symm he]
  have hQP : (1 : Matrix n n ℂ) - P = Q := by
    ext i j
    by_cases he : i = j
    · subst j; by_cases hi : i ∈ S <;> simp [P, Q, hi]
    · simp [P, Q, one_apply, he]
  have m : ((fun i => if i ∈ S then A i else (1 : Matrix n n ℂ) i) : Matrix n n ℂ) =
      (1 : Matrix n n ℂ) + P * (A - (1 : Matrix n n ℂ)) := by
    ext i j
    by_cases hi : i ∈ S <;> simp [P, diagonal_mul, hi]
  rw [m]
  have hswap : det (1 + P * (A - 1)) = det (1 + P * (A - 1) * P) := by
    rw [det_one_add_mul_comm (P * (A - 1)) P, ← Matrix.mul_assoc P P, hPP]
  have he : 1 + P * (A - 1) * P = Q + P * A * P := by
    rw [mul_sub, sub_mul, mul_one, hPP, ← hQP]
    abel
  rw [hswap, he]
  simpa only [hPstar] using (hQ.add (ha.conjTranspose_mul_mul_same P)).det_nonneg

private theorem block_marginals {n : Type} [Fintype n] [DecidableEq n]
    (U : unitary (Matrix n n ℂ)) (w : Equiv.Perm n → ℝ)
    (hexp : ∀ (a b : n → ℂ) (S : Finset n),
      let M : Matrix n n ℂ := fun i =>
        if i ∈ S then (diagonal a + U.val * diagonal b * star U.val) i else (1 : Matrix n n ℂ) i
      M.det = ∑ σ, w σ • (∏ i ∈ S, (a i + b (σ i)))) (I J : Finset n) :
    0 ≤ ∑ σ : Equiv.Perm n, w σ * (if ∀ i ∈ I, σ i ∈ J then (1 : ℝ) else 0) := by
  classical
  let b (i : n) : ℂ := if i ∈ J then 1 else 0
  have hd : (diagonal b).PosSemidef := posSemidef_diagonal_iff.mpr (fun i => by simp [b]; split <;> simp)
  have h := compression_nonneg I _ (hd.mul_mul_conjTranspose_same U.val)
  have e := hexp (fun _ => 0) b I
  simp only [diagonal_zero, zero_add, Matrix.star_eq_conjTranspose] at e
  rw [e] at h
  have r := (Complex.nonneg_iff.mp h).1
  simp only [b, Finset.prod_boole, Complex.re_sum, Complex.real_smul] at r
  convert r using 1
  apply Finset.sum_congr rfl
  intro σ _
  split <;> simp_all

private theorem fiber_sum {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (v : ι → κ) (F : κ → ℂ) (w : ι → ℝ) :
    (∑ i, w i • F (v i)) = ∑ j, (∑ i, if v i = j then w i else 0) • F j := by
  simp_rw [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

private theorem products_of_marginals {n : Type} [Fintype n] [DecidableEq n]
    (T : Finset n) (w t : Equiv.Perm n → ℝ)
    (h : ∀ S ⊆ T, ∀ J : Finset n, (∑ σ : Equiv.Perm n, if S.image σ = J then w σ else 0) =
      ∑ σ : Equiv.Perm n, if S.image σ = J then t σ else 0) (a b : n → ℂ) :
    (∑ σ, w σ • (∏ i ∈ T, (a i + b (σ i)))) =
      ∑ σ, t σ • (∏ i ∈ T, (a i + b (σ i))) := by
  classical
  let F (S J : Finset n) : ℂ := (∏ i ∈ S, a i) * ∏ j ∈ J, b j
  have expn (σ : Equiv.Perm n) : (∏ i ∈ T, (a i + b (σ i))) =
      ∑ S ∈ T.powerset, F S ((T \ S).image σ) := by
    rw [Finset.prod_add]
    apply Finset.sum_congr rfl
    intro S _
    simp only [F, Finset.prod_image σ.injective.injOn]
  simp_rw [expn, Finset.smul_sum]
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ) (t := T.powerset)]
  apply Finset.sum_congr rfl
  intro S _
  rw [fiber_sum (fun σ : Equiv.Perm n => (T \ S).image σ) (F S) w,
      fiber_sum (fun σ : Equiv.Perm n => (T \ S).image σ) (F S) t]
  simp_rw [h (T \ S) Finset.sdiff_subset]


private theorem signed_hull_card_three {n : Type} [Fintype n] [DecidableEq n]
    (hn : Fintype.card n = 3) (U : unitary (Matrix n n ℂ)) (a b : n → ℂ) (T : Finset n) :
    let w (σ : Equiv.Perm n) :=
      (((Equiv.Perm.sign σ : ℤ) : ℂ) * (∏ i, U.val i (σ i)) * (star U.val).det).re
    (∑ σ, w σ • (∏ i ∈ T, (a i + b (σ i)))) ∈ convexHull ℝ
      (Set.range fun (σ : Equiv.Perm n) => ∏ i ∈ T, (a i + b (σ i))) := by
  classical
  intro w
  obtain ⟨hs, hdet⟩ := signed_compression U
  change (∑ σ, w σ) = 1 at hs
  obtain ⟨t, ht, ht₁, hf⟩ := OMAH2Three.coupling_of_card_three hn w hs (block_marginals U w hdet)
  rw [products_of_marginals T w t (fun S _ => hf S)]
  exact (convex_convexHull ℝ _).sum_mem (fun σ _ => ht σ) ht₁
    (fun σ _ => subset_convexHull ℝ _ ⟨σ, rfl⟩)

/-- Four-dimensional unitaries. It suffices to retain three rows and prove
an upper support inequality in the fixed real direction. -/
def H1 : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n], Fintype.card n = 4 →
    ∀ U : unitary (Matrix n n ℂ), ∃ k : n,
      let w (σ : Equiv.Perm n) :=
        (((Equiv.Perm.sign σ : ℤ) : ℂ) * (∏ i, U.val i (σ i)) * (star U.val).det).re
      ∀ a b : n → ℂ,
        let p (σ : Equiv.Perm n) := ∏ i ∈ Finset.univ.erase k, (a i + b (σ i))
        ∃ σ : Equiv.Perm n, (∑ τ, w τ • p τ).re ≤ (p σ).re

/-- Higher dimensions. For each unitary, one row may be erased before testing
the same real upper support inequality. -/
def H2 : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n], 5 ≤ Fintype.card n →
    ∀ U : unitary (Matrix n n ℂ), ∃ k : n,
      let w (σ : Equiv.Perm n) :=
        (((Equiv.Perm.sign σ : ℤ) : ℂ) * (∏ i, U.val i (σ i)) * (star U.val).det).re
      ∀ a b : n → ℂ,
        let p (σ : Equiv.Perm n) := ∏ i ∈ Finset.univ.erase k, (a i + b (σ i))
        ∃ σ : Equiv.Perm n, (∑ τ, w τ • p τ).re ≤ (p σ).re

theorem main : H1 → H2 → OMA.R_DeterminantalConjecture_determinantal_conjecture_R1.H2 := by
  classical
  intro hFour hLarge
  apply H2_of_retained
  intro n _ _ hn U _ a b T
  by_cases hThree : Fintype.card n = 3
  · exact signed_hull_card_three hThree U a b T
  let w (σ : Equiv.Perm n) :=
    (((Equiv.Perm.sign σ : ℤ) : ℂ) * (∏ i, U.val i (σ i)) * (star U.val).det).re
  obtain ⟨k, hk⟩ : ∃ k : n, ∀ a' b' : n → ℂ,
      ∃ σ : Equiv.Perm n,
        (∑ τ, w τ • (∏ i ∈ Finset.univ.erase k, (a' i + b' (τ i)))).re ≤
          (∏ i ∈ Finset.univ.erase k, (a' i + b' (σ i))).re := by
    by_cases h : Fintype.card n = 4
    · exact hFour n h U
    · exact hLarge n (by omega) U
  have hCard : 0 < (Finset.univ.erase k).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ]
    omega
  exact retained_of_full w
    (hull_of_one_erased_row w k (hull_of_real_support w _ hCard hk)) a b T

end OMA.R_DeterminantalConjecture_determinantal_conjecture_R1_H2_R1
