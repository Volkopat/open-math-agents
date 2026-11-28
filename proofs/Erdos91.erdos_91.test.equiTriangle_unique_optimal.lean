import FormalConjectures.ErdosProblems.«91»
import Mathlib.Analysis.Normed.Field.Lemmas

/-!
# Uniqueness of the optimal three-point configuration

The reference triangle realizes one distance. In complex coordinates any other optimal
triangle can be translated and rescaled so that two vertices are 0 and 1. Its third
vertex has unit distance from both, which determines it up to complex conjugation.
-/

-- Credit: @Genbox

open Erdos91 EuclideanGeometry

private theorem equiTriangle_distinctDistances_le : distinctDistances equiTriangle ≤ 1 := by
  classical
  let a : ℝ² := !₂[0, 0]
  let b : ℝ² := !₂[1, 0]
  let c : ℝ² := !₂[1 / 2, Real.sqrt 3 / 2]
  have hsq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hab : dist a b = 1 := by
    apply (sq_eq_sq₀ dist_nonneg zero_le_one).mp
    norm_num [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs, a, b]
  have hac : dist a c = 1 := by
    apply (sq_eq_sq₀ dist_nonneg zero_le_one).mp
    norm_num [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs, a, c]
    nlinarith
  have hbc : dist b c = 1 := by
    apply (sq_eq_sq₀ dist_nonneg zero_le_one).mp
    norm_num [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs, b, c]
    nlinarith
  change (distanceSet {a, b, c}).card ≤ 1
  suffices h : distanceSet {a, b, c} ⊆ {1} by
    simpa using Finset.card_le_card h
  intro d hd
  obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨hx, hy, hne⟩ := Finset.mem_offDiag.mp hxy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    simp_all [dist_comm]

private theorem equilateral_complex_normalization {z : ℂ}
    (hz : ‖z‖ = 1) (hz1 : ‖z - 1‖ = 1) :
    z = ⟨1 / 2, Real.sqrt 3 / 2⟩ ∨
      starRingEnd ℂ z = ⟨1 / 2, Real.sqrt 3 / 2⟩ := by
  have h0 := congrArg (fun x : ℝ => x ^ 2) hz
  have h1 := congrArg (fun x : ℝ => x ^ 2) hz1
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, sub_zero, one_pow] at h0 h1
  have hre : z.re = 1 / 2 := by nlinarith
  have hsqrt : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hf : (z.im - Real.sqrt 3 / 2) * (z.im + Real.sqrt 3 / 2) = 0 := by
    rw [hre] at h0
    nlinarith
  rcases mul_eq_zero.mp hf with hi | hi
  · exact Or.inl (Complex.ext hre (by dsimp; linarith))
  · exact Or.inr (Complex.ext (by simpa only [Complex.conj_re] using hre)
      (by change -z.im = Real.sqrt 3 / 2; linarith))

theorem OMA.solution : type_of% @Erdos91.erdos_91.test.equiTriangle_unique_optimal := by
  classical
  intro A hA
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hA.1
  have hcard : (distanceSet ({a, b, c} : Finset ℝ²)).card ≤ 1 :=
    hA.2.trans_le (Erdos91.erdos_91.test.equiTriangle_optimal.2.symm.trans_le
      equiTriangle_distinctDistances_le)
  have hmem {x y : ℝ²} (hx : x ∈ ({a, b, c} : Finset ℝ²))
      (hy : y ∈ ({a, b, c} : Finset ℝ²)) (hne : x ≠ y) :
      dist x y ∈ distanceSet ({a, b, c} : Finset ℝ²) :=
    Finset.mem_image.mpr ⟨(x, y), Finset.mem_offDiag.mpr ⟨hx, hy, hne⟩, rfl⟩
  have hmab := hmem (x := b) (y := a) (by simp) (by simp) hab.symm
  have hmac := hmem (x := c) (y := a) (by simp) (by simp) hac.symm
  have hmbc := hmem (x := c) (y := b) (by simp) (by simp) hbc.symm
  have hca : dist c a = dist b a := Finset.card_le_one.mp hcard _ hmac _ hmab
  have hcb : dist c b = dist b a := Finset.card_le_one.mp hcard _ hmbc _ hmab
  let e := Complex.orthonormalBasisOneI.repr.symm.toIsometryEquiv
  let v := e b - e a
  have hv : v ≠ 0 := sub_ne_zero.mpr (fun h => hab.symm (e.injective h))
  have hnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  let z := (e c - e a) / v
  have h0 : ‖z‖ = 1 := by
    have h := e.isometry.dist_eq c a
    rw [dist_eq_norm] at h
    have h' := e.isometry.dist_eq b a
    rw [dist_eq_norm] at h'
    change ‖(e c - e a) / v‖ = 1
    rw [norm_div, h, hca, ← h']
    exact div_self hnorm
  have h1 : ‖z - 1‖ = 1 := by
    have h : z - 1 = (e c - e b) / v := by
      dsimp [z]
      field_simp
      dsimp [v]
      ring
    have hc' := e.isometry.dist_eq c b
    rw [dist_eq_norm] at hc'
    have hb' := e.isometry.dist_eq b a
    rw [dist_eq_norm] at hb'
    rw [h, norm_div, hc', hcb, ← hb']
    exact div_self hnorm
  let f : ℝ² ≃ᵈ ℂ := (e.toDilationEquiv.trans
    (IsometryEquiv.vaddConst (-e a)).toDilationEquiv).trans
    (DilationEquiv.mulRight v⁻¹ (inv_ne_zero hv))
  have hf (x : ℝ²) : f x = (e x - e a) / v := by
    change (e x + -e a) * v⁻¹ = _
    rw [sub_eq_add_neg, div_eq_mul_inv]
  have fa : f a = 0 := by simp [hf]
  have fb : f b = 1 := by rw [hf]; exact div_self hv
  have fc : f c = z := hf c
  let w : ℂ := ⟨1 / 2, Real.sqrt 3 / 2⟩
  obtain ⟨g, ga, gb, gc⟩ :
      ∃ g : ℝ² ≃ᵈ ℂ, g a = 0 ∧ g b = 1 ∧ g c = w := by
    rcases equilateral_complex_normalization h0 h1 with hp | hm
    · exact ⟨f, fa, fb, fc.trans hp⟩
    · refine ⟨f.trans Complex.conjLIE.toIsometryEquiv.toDilationEquiv, ?_, ?_, ?_⟩
      · simp [DilationEquiv.trans_apply, fa]
      · simp [DilationEquiv.trans_apply, fb]
      · simpa [DilationEquiv.trans_apply, fc, w] using hm
  refine ⟨g.trans e.symm.toDilationEquiv, ?_⟩
  have ha' : e.symm 0 = !₂[0, 0] := by apply e.injective; simp [e]
  have hb' : e.symm 1 = !₂[1, 0] := by apply e.injective; simp [e]
  have hc' : e.symm w = !₂[1 / 2, Real.sqrt 3 / 2] := by
    apply e.injective
    simp only [IsometryEquiv.apply_symm_apply]
    apply Complex.ext <;> norm_num [e, w, Complex.mul_re, Complex.mul_im]
  simp only [equiTriangle, Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq,
    Set.image_singleton, DilationEquiv.trans_apply, Function.comp_apply,
    IsometryEquiv.toDilationEquiv_apply, ga, gb, gc, ha', hb', hc']
