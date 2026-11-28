import FormalConjectures.Wikipedia.ResolutionOfSingularities
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.Algebra.Polynomial.Taylor

/-! The spectrum of an inseparable simple extension cannot admit a smooth resolution. -/

open AlgebraicGeometry CategoryTheory Polynomial

theorem OMA.solution : type_of% @AlgebraicGeometry.exists_not_hasResolution_of_not_perfectField := by
  intro k _ hk
  classical
  obtain ⟨p, hp, hderiv⟩ : ∃ p : k[X], Irreducible p ∧ p.derivative = 0 := by
    by_contra! h; exact hk ⟨fun {p} hp => (separable_iff_derivative_ne_zero hp).2 (h p hp)⟩
  let : Fact (Irreducible p) := ⟨hp⟩
  let L := AdjoinRoot p
  let S := Spec (CommRingCat.of L)
  let s : S ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom (algebraMap k L))
  have hft : LocallyOfFiniteType s :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2
      (RingHom.finiteType_algebraMap.2 inferInstance)
  refine ⟨S, s, inferInstance, hft, inferInstance, inferInstance, ?_, fun ⟨Y, f, _, _, _, g, hg⟩ => ?_⟩
  · change topologicalKrullDim (PrimeSpectrum L) = 0
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]
  · have : Subsingleton S := inferInstanceAs (Subsingleton (PrimeSpectrum L))
    have ht : g.target = ⊤ := by
      obtain ⟨x, hx⟩ := g.dense_target.nonempty
      exact top_unique fun y _ => by change y ∈ (g.target : Set S); simpa only [Subsingleton.elim y x] using hx
    have hι : IsIso g.target.ι := by rw [ht, ← Scheme.topIso_hom]; infer_instance
    have hcomp : Smooth (g.iso.hom ≫ g.target.ι ≫ s) := by
      have heq : (g.iso.hom ≫ g.target.ι) = (g.source.ι ≫ f) := by
        simpa only [Scheme.PartialIso.IsOver, Category.comp_id] using hg
      rw [← Category.assoc, heq, Category.assoc]; infer_instance
    have hfull : Smooth (inv g.target.ι ≫ g.iso.inv ≫ g.iso.hom ≫ g.target.ι ≫ s) := inferInstance
    have hsm : Smooth s := by simpa only [Iso.inv_hom_id_assoc, IsIso.inv_hom_id_assoc] using hfull
    have hAlg : Algebra.Smooth k L :=
      RingHom.smooth_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Smooth)).1 hsm)
    let π := AdjoinRoot.mkₐ p
    let J := RingHom.ker π.toRingHom
    let q : k[X] →ₐ[k] k[X] ⧸ J ^ 2 := Ideal.Quotient.mkₐ k _
    obtain ⟨σ, hσ⟩ := (Algebra.FormallySmooth.iff_split_surjection π AdjoinRoot.mk_surjective).1
      (inferInstance : Algebra.FormallySmooth k L)
    let x := q X
    let e := σ (AdjoinRoot.root p) - x
    have he : e ∈ RingHom.ker π.kerSquareLift.toRingHom := by
      change π.kerSquareLift (σ (AdjoinRoot.root p) - q X) = 0
      rw [map_sub, sub_eq_zero]
      exact (DFunLike.congr_fun hσ (AdjoinRoot.root p)).trans (π.kerSquareLift_mk X).symm
    have he2 : e ^ 2 = 0 := by
      simpa only [AlgHom.ker_kerSquareLift, Ideal.cotangentIdeal_square, Ideal.mem_bot] using
        Ideal.pow_mem_pow he 2
    have hroot : aeval (x + e) p = 0 := by
      rw [show x + e = σ (AdjoinRoot.root p) by rw [add_comm, show e = σ (AdjoinRoot.root p) - x from rfl, sub_add_cancel]]
      exact AdjoinRoot.aeval_algHom_eq_zero p σ
    rw [aeval_add_of_sq_eq_zero p x e he2, hderiv, map_zero, zero_mul, add_zero,
      show aeval x = q from Polynomial.algHom_ext (by simp [x])] at hroot
    have hm : p ∈ J ^ 2 := Ideal.Quotient.eq_zero_iff_mem.1 hroot
    have hJ : J = Ideal.span {p} := Ideal.ext fun _ =>
      (AdjoinRoot.mk_eq_zero (f := p)).trans Ideal.mem_span_singleton.symm
    rw [hJ, Ideal.span_singleton_pow] at hm
    have := (pow_dvd_pow_iff hp.ne_zero hp.not_isUnit).1
      (by simpa using Ideal.mem_span_singleton.1 hm : p ^ 2 ∣ p ^ 1)
    omega
