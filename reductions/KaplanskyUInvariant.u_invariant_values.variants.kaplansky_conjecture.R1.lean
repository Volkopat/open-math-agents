import FormalConjectures.Paper.KaplanskyUInvariant

/-!
# Reduction of Kaplansky's conjecture to Merkurjev's biquaternion index-preservation theorem

Kaplansky conjectured that every finite $u$-invariant of a field of characteristic not $2$ is a
power of $2$. Merkurjev disproved this by constructing a field of $u$-invariant $6$ via an
iterated tower of function fields of $7$-dimensional quadrics preserving a biquaternion division
algebra.

This reduction formalizes the complete Merkurjev tower construction in `main`: starting from a
countable field with a biquaternion division algebra (`H1`) and Merkurjev's one-step index
preservation theorem over $7$-dimensional diagonal forms (`H2`), we extract countable subfields
along an $\omega$-chain killing all $7$-dimensional forms by Cantor dovetailing, pass to the
direct limit field, show the biquaternion algebra remains a division algebra over the direct limit
(hence its $6$-dimensional Albert form is anisotropic), show every form of dimension $\ge 7$ is
isotropic, deduce `IsUInvariant 6`, and observe that $6$ is not a power of $2$.
-/

namespace OMA.R_KaplanskyUInvariant_u_invariant_values_variants_kaplansky_conjecture_R1

open KaplanskyUInvariant QuadraticMap QuadraticForm
open scoped TensorProduct

/-- Existence of a countable field `F` of characteristic not `2` carrying a biquaternion division
algebra `QuaternionAlgebra F a 0 b ⊗[F] QuaternionAlgebra F c 0 d` (i.e., with no zero divisors),
such as `ℚ(t₁, t₂, t₃, t₄)` with `a = t₁, b = t₂, c = t₃, d = t₄`. -/
def H1 : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : NeZero (2 : F)) (_ : Countable F) (a b c d : F),
    NoZeroDivisors (QuaternionAlgebra F a 0 b ⊗[F] QuaternionAlgebra F c 0 d)

/-- Merkurjev's index preservation theorem [Merkurjev1989]: if `QuaternionAlgebra K a 0 b ⊗[K]
QuaternionAlgebra K c 0 d` has no zero divisors over a field `K` of characteristic not `2`, then for
every `7`-dimensional diagonal quadratic form `∑ i, w i * x_i ^ 2` over `K`, there exists a field
extension `L / K` in which this `7`-dimensional form becomes isotropic while the base-changed
biquaternion algebra still has no zero divisors. -/
def H2 : Prop :=
  ∀ (K : Type) [Field K] [NeZero (2 : K)] (a b c d : K),
    NoZeroDivisors (QuaternionAlgebra K a 0 b ⊗[K] QuaternionAlgebra K c 0 d) →
    ∀ w : Fin 7 → K,
      ∃ (L : Type) (_ : Field L) (f : K →+* L),
        (∃ v : Fin 7 → L, v ≠ 0 ∧ ∑ i : Fin 7, f (w i) * v i ^ 2 = 0) ∧
        NoZeroDivisors (QuaternionAlgebra L (f a) 0 (f b) ⊗[L] QuaternionAlgebra L (f c) 0 (f d))

lemma albert_anisotropic_of_noZeroDivisors {F : Type} [Field F] (a b c d : F)
    (hD : NoZeroDivisors (QuaternionAlgebra F a 0 b ⊗[F] QuaternionAlgebra F c 0 d)) :
    ∀ v : Fin 6 → F,
      a * v 0 ^ 2 + b * v 1 ^ 2 - a * b * v 2 ^ 2 -
        c * v 3 ^ 2 - d * v 4 ^ 2 + c * d * v 5 ^ 2 = 0 → v = 0 := by
  intro v hv
  let u : QuaternionAlgebra F a 0 b := ⟨0, v 0, v 1, v 2⟩
  let w : QuaternionAlgebra F c 0 d := ⟨0, v 3, v 4, v 5⟩
  have hu : u * u = algebraMap F (QuaternionAlgebra F a 0 b)
      (a * v 0 ^ 2 + b * v 1 ^ 2 - a * b * v 2 ^ 2) := by
    ext <;> simp [u, QuaternionAlgebra.algebraMap_eq] <;> ring
  have hw : w * w = algebraMap F (QuaternionAlgebra F c 0 d)
      (c * v 3 ^ 2 + d * v 4 ^ 2 - c * d * v 5 ^ 2) := by
    ext <;> simp [w, QuaternionAlgebra.algebraMap_eq] <;> ring
  let x₁ : QuaternionAlgebra F a 0 b ⊗[F] QuaternionAlgebra F c 0 d :=
    u ⊗ₜ[F] (1 : QuaternionAlgebra F c 0 d) - (1 : QuaternionAlgebra F a 0 b) ⊗ₜ[F] w
  let x₂ : QuaternionAlgebra F a 0 b ⊗[F] QuaternionAlgebra F c 0 d :=
    u ⊗ₜ[F] (1 : QuaternionAlgebra F c 0 d) + (1 : QuaternionAlgebra F a 0 b) ⊗ₜ[F] w
  have hmul : x₁ * x₂ = 0 := by
    have h1 : x₁ * x₂ = (u * u) ⊗ₜ[F] (1 : QuaternionAlgebra F c 0 d) -
        (1 : QuaternionAlgebra F a 0 b) ⊗ₜ[F] (w * w) := by
      simp only [x₁, x₂, sub_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      abel
    rw [h1, hu, hw, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul, TensorProduct.tmul_smul, TensorProduct.tmul_smul, ← sub_smul]
    have hcoeff : (a * v 0 ^ 2 + b * v 1 ^ 2 - a * b * v 2 ^ 2) -
        (c * v 3 ^ 2 + d * v 4 ^ 2 - c * d * v 5 ^ 2) = 0 := by
      linear_combination hv
    rw [hcoeff, zero_smul]
  let B := (QuaternionAlgebra.basisOneIJK a 0 b).tensorProduct (QuaternionAlgebra.basisOneIJK c 0 d)
  have hcoord : ∀ s : F,
      u ⊗ₜ[F] (1 : QuaternionAlgebra F c 0 d) + s • ((1 : QuaternionAlgebra F a 0 b) ⊗ₜ[F] w) = 0 →
      s = 1 ∨ s = -1 → v = 0 := by
    intro s hs hpm
    have hAt : ∀ i j : Fin 4,
        B.repr (u ⊗ₜ[F] (1 : QuaternionAlgebra F c 0 d) +
          s • ((1 : QuaternionAlgebra F a 0 b) ⊗ₜ[F] w)) (i, j) = 0 := fun i j => by
      rw [hs, map_zero]; rfl
    have hv0 : v 0 = 0 := by
      have h := hAt 1 0
      simp only [B, map_add, map_smul, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply,
        Pi.smul_apply, Module.Basis.tensorProduct_repr_tmul_apply,
        QuaternionAlgebra.coe_basisOneIJK_repr, smul_eq_mul, u, w] at h
      simpa using h
    have hv1 : v 1 = 0 := by
      have h := hAt 2 0
      simp only [B, map_add, map_smul, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply,
        Pi.smul_apply, Module.Basis.tensorProduct_repr_tmul_apply,
        QuaternionAlgebra.coe_basisOneIJK_repr, smul_eq_mul, u, w] at h
      simpa using h
    have hv2 : v 2 = 0 := by
      have h := hAt 3 0
      simp only [B, map_add, map_smul, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply,
        Pi.smul_apply, Module.Basis.tensorProduct_repr_tmul_apply,
        QuaternionAlgebra.coe_basisOneIJK_repr, smul_eq_mul, u, w] at h
      simpa using h
    have hv3 : v 3 = 0 := by
      have h := hAt 0 1
      simp only [B, map_add, map_smul, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply,
        Pi.smul_apply, Module.Basis.tensorProduct_repr_tmul_apply,
        QuaternionAlgebra.coe_basisOneIJK_repr, smul_eq_mul, u, w] at h
      rcases hpm with rfl | rfl <;> simpa using h
    have hv4 : v 4 = 0 := by
      have h := hAt 0 2
      simp only [B, map_add, map_smul, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply,
        Pi.smul_apply, Module.Basis.tensorProduct_repr_tmul_apply,
        QuaternionAlgebra.coe_basisOneIJK_repr, smul_eq_mul, u, w] at h
      rcases hpm with rfl | rfl <;> simpa using h
    have hv5 : v 5 = 0 := by
      have h := hAt 0 3
      simp only [B, map_add, map_smul, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply,
        Pi.smul_apply, Module.Basis.tensorProduct_repr_tmul_apply,
        QuaternionAlgebra.coe_basisOneIJK_repr, smul_eq_mul, u, w] at h
      rcases hpm with rfl | rfl <;> simpa using h
    funext i
    fin_cases i <;> assumption
  rcases hD.eq_zero_or_eq_zero_of_mul_eq_zero hmul with hx1 | hx2
  · exact hcoord (-1) (by simpa [x₁, sub_eq_add_neg] using hx1) (Or.inr rfl)
  · exact hcoord 1 (by simpa [x₂] using hx2) (Or.inl rfl)

lemma six_mem_anisotropicDims_of_noZeroDivisors {F : Type} [Field F] [NeZero (2 : F)]
    (a b c d : F)
    (hD : NoZeroDivisors (QuaternionAlgebra F a 0 b ⊗[F] QuaternionAlgebra F c 0 d)) :
    6 ∈ anisotropicDims F := by
  refine mem_anisotropicDims_iff.mpr ⟨weightedSumSquares F ![a, b, -(a * b), -c, -d, c * d], ?_⟩
  intro v hv
  simp only [weightedSumSquares_apply, Fin.sum_univ_six, smul_eq_mul] at hv
  have h0 : (![a, b, -(a * b), -c, -d, c * d] : Fin 6 → F) 0 = a := rfl
  have h1 : (![a, b, -(a * b), -c, -d, c * d] : Fin 6 → F) 1 = b := rfl
  have h2 : (![a, b, -(a * b), -c, -d, c * d] : Fin 6 → F) 2 = -(a * b) := rfl
  have h3 : (![a, b, -(a * b), -c, -d, c * d] : Fin 6 → F) 3 = -c := rfl
  have h4 : (![a, b, -(a * b), -c, -d, c * d] : Fin 6 → F) 4 = -d := rfl
  have h5 : (![a, b, -(a * b), -c, -d, c * d] : Fin 6 → F) 5 = c * d := rfl
  rw [h0, h1, h2, h3, h4, h5] at hv
  exact albert_anisotropic_of_noZeroDivisors a b c d hD v (by linear_combination hv)

lemma exists_biquat_ringHom {K L : Type} [Field K] [Field L] (f : K →+* L) (a b c d : K) :
    ∃ φ : (QuaternionAlgebra K a 0 b ⊗[K] QuaternionAlgebra K c 0 d) →+*
          (QuaternionAlgebra L (f a) 0 (f b) ⊗[L] QuaternionAlgebra L (f c) 0 (f d)),
      Function.Injective φ ∧
      ∀ x i j,
        ((QuaternionAlgebra.basisOneIJK (f a) 0 (f b)).tensorProduct
          (QuaternionAlgebra.basisOneIJK (f c) 0 (f d))).repr (φ x) (i, j) =
        f (((QuaternionAlgebra.basisOneIJK a 0 b).tensorProduct
          (QuaternionAlgebra.basisOneIJK c 0 d)).repr x (i, j)) := by
  let A_L := QuaternionAlgebra L (f a) 0 (f b) ⊗[L] QuaternionAlgebra L (f c) 0 (f d)
  letI : Algebra K A_L := Algebra.compHom A_L f
  let ψ₁ : QuaternionAlgebra K a 0 b →ₐ[K] A_L :=
    { toFun := fun q =>
        (⟨f q.1, f q.2, f q.3, f q.4⟩ : QuaternionAlgebra L (f a) 0 (f b)) ⊗ₜ[L]
          (1 : QuaternionAlgebra L (f c) 0 (f d))
      map_one' := by
        have h1 : (⟨f (1 : QuaternionAlgebra K a 0 b).re, f (1 : QuaternionAlgebra K a 0 b).imI,
            f (1 : QuaternionAlgebra K a 0 b).imJ, f (1 : QuaternionAlgebra K a 0 b).imK⟩ :
            QuaternionAlgebra L (f a) 0 (f b)) = 1 := by
          ext <;> simp
        change _ ⊗ₜ[L] _ = (1 : QuaternionAlgebra L (f a) 0 (f b)) ⊗ₜ[L] 1
        rw [h1]
      map_mul' := fun x y => by
        change (⟨f (x * y).1, f (x * y).2, f (x * y).3, f (x * y).4⟩ :
            QuaternionAlgebra L (f a) 0 (f b)) ⊗ₜ[L] 1 = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        congr 1
        ext <;> simp <;> ring
      map_zero' := by
        have h0 : (⟨f (0 : QuaternionAlgebra K a 0 b).re, f (0 : QuaternionAlgebra K a 0 b).imI,
            f (0 : QuaternionAlgebra K a 0 b).imJ, f (0 : QuaternionAlgebra K a 0 b).imK⟩ :
            QuaternionAlgebra L (f a) 0 (f b)) = 0 := by
          ext <;> simp
        change _ ⊗ₜ[L] _ = 0
        rw [h0, TensorProduct.zero_tmul]
      map_add' := fun x y => by
        rw [← TensorProduct.add_tmul]
        congr 1
        ext <;> simp
      commutes' := fun r => by
        change (⟨f r, f 0, f 0, f 0⟩ : QuaternionAlgebra L (f a) 0 (f b)) ⊗ₜ[L] 1 =
          algebraMap L A_L (f r)
        have hr : (⟨f r, f 0, f 0, f 0⟩ : QuaternionAlgebra L (f a) 0 (f b)) =
            algebraMap L (QuaternionAlgebra L (f a) 0 (f b)) (f r) := by
          ext <;> simp [QuaternionAlgebra.algebraMap_eq]
        rw [hr, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, TensorProduct.tmul_smul,
          Algebra.algebraMap_eq_smul_one]
        rfl }
  let ψ₂ : QuaternionAlgebra K c 0 d →ₐ[K] A_L :=
    { toFun := fun q =>
        (1 : QuaternionAlgebra L (f a) 0 (f b)) ⊗ₜ[L]
          (⟨f q.1, f q.2, f q.3, f q.4⟩ : QuaternionAlgebra L (f c) 0 (f d))
      map_one' := by
        have h1 : (⟨f (1 : QuaternionAlgebra K c 0 d).re, f (1 : QuaternionAlgebra K c 0 d).imI,
            f (1 : QuaternionAlgebra K c 0 d).imJ, f (1 : QuaternionAlgebra K c 0 d).imK⟩ :
            QuaternionAlgebra L (f c) 0 (f d)) = 1 := by
          ext <;> simp
        change _ ⊗ₜ[L] _ = (1 : QuaternionAlgebra L (f a) 0 (f b)) ⊗ₜ[L] 1
        rw [h1]
      map_mul' := fun x y => by
        change (1 : QuaternionAlgebra L (f a) 0 (f b)) ⊗ₜ[L]
          (⟨f (x * y).1, f (x * y).2, f (x * y).3, f (x * y).4⟩ :
            QuaternionAlgebra L (f c) 0 (f d)) = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        congr 1
        ext <;> simp <;> ring
      map_zero' := by
        have h0 : (⟨f (0 : QuaternionAlgebra K c 0 d).re, f (0 : QuaternionAlgebra K c 0 d).imI,
            f (0 : QuaternionAlgebra K c 0 d).imJ, f (0 : QuaternionAlgebra K c 0 d).imK⟩ :
            QuaternionAlgebra L (f c) 0 (f d)) = 0 := by
          ext <;> simp
        change _ ⊗ₜ[L] _ = 0
        rw [h0, TensorProduct.tmul_zero]
      map_add' := fun x y => by
        rw [← TensorProduct.tmul_add]
        congr 1
        ext <;> simp
      commutes' := fun r => by
        change (1 : QuaternionAlgebra L (f a) 0 (f b)) ⊗ₜ[L]
          (⟨f r, f 0, f 0, f 0⟩ : QuaternionAlgebra L (f c) 0 (f d)) =
          algebraMap L A_L (f r)
        have hr : (⟨f r, f 0, f 0, f 0⟩ : QuaternionAlgebra L (f c) 0 (f d)) =
            algebraMap L (QuaternionAlgebra L (f c) 0 (f d)) (f r) := by
          ext <;> simp [QuaternionAlgebra.algebraMap_eq]
        rw [hr, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
          Algebra.algebraMap_eq_smul_one]
        rfl }
  have hcomm : ∀ x y, Commute (ψ₁ x) (ψ₂ y) := fun x y => by
    change ψ₁ x * ψ₂ y = ψ₂ y * ψ₁ x
    dsimp [ψ₁, ψ₂]
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, one_mul, mul_one, one_mul]
  let φAlg := Algebra.TensorProduct.lift ψ₁ ψ₂ hcomm
  let φ : (QuaternionAlgebra K a 0 b ⊗[K] QuaternionAlgebra K c 0 d) →+* A_L := φAlg.toRingHom
  have hrepr : ∀ x i j,
      ((QuaternionAlgebra.basisOneIJK (f a) 0 (f b)).tensorProduct
        (QuaternionAlgebra.basisOneIJK (f c) 0 (f d))).repr (φ x) (i, j) =
      f (((QuaternionAlgebra.basisOneIJK a 0 b).tensorProduct
        (QuaternionAlgebra.basisOneIJK c 0 d)).repr x (i, j)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero =>
      intro i j
      simp
    | tmul x₁ x₂ =>
      intro i j
      have htmul : φ (x₁ ⊗ₜ[K] x₂) =
          (⟨f x₁.1, f x₁.2, f x₁.3, f x₁.4⟩ : QuaternionAlgebra L (f a) 0 (f b)) ⊗ₜ[L]
          (⟨f x₂.1, f x₂.2, f x₂.3, f x₂.4⟩ : QuaternionAlgebra L (f c) 0 (f d)) := by
        change φAlg (x₁ ⊗ₜ[K] x₂) = _
        simp only [φAlg, Algebra.TensorProduct.lift_tmul, ψ₁, ψ₂, AlgHom.coe_mk, RingHom.coe_mk,
          MonoidHom.coe_mk, OneHom.coe_mk]
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [htmul]
      simp only [Module.Basis.tensorProduct_repr_tmul_apply, QuaternionAlgebra.coe_basisOneIJK_repr,
        smul_eq_mul]
      fin_cases i <;> fin_cases j <;> simp [map_mul]
    | add x y hx hy =>
      intro i j
      simp only [map_add, Finsupp.coe_add, Pi.add_apply, hx i j, hy i j]
  refine ⟨φ, ?_, hrepr⟩
  intro x y hxy
  apply ((QuaternionAlgebra.basisOneIJK a 0 b).tensorProduct
    (QuaternionAlgebra.basisOneIJK c 0 d)).repr.injective
  ext ⟨i, j⟩
  apply f.injective
  rw [← hrepr x i j, ← hrepr y i j, hxy]

lemma noZeroDivisors_biquat_of_ringHom {K L : Type} [Field K] [Field L] (f : K →+* L)
    (a b c d : K)
    (hL : NoZeroDivisors (QuaternionAlgebra L (f a) 0 (f b) ⊗[L] QuaternionAlgebra L (f c) 0 (f d))) :
    NoZeroDivisors (QuaternionAlgebra K a 0 b ⊗[K] QuaternionAlgebra K c 0 d) := by
  obtain ⟨φ, hφ_inj, _⟩ := exists_biquat_ringHom f a b c d
  exact Function.Injective.noZeroDivisors φ hφ_inj (map_zero φ) (map_mul φ)

lemma infinite_of_noZeroDivisors_biquat {F : Type} [Field F] [NeZero (2 : F)]
    (a b c d : F)
    (hD : NoZeroDivisors (QuaternionAlgebra F a 0 b ⊗[F] QuaternionAlgebra F c 0 d)) :
    Infinite F := by
  by_contra hinf
  rw [not_infinite_iff_finite] at hinf
  letI : Fintype F := Fintype.ofFinite F
  classical
  have halbert := albert_anisotropic_of_noZeroDivisors a b c d hD
  have ha : a ≠ 0 := by
    intro ha0
    have h := congr_fun (halbert ![1, 0, 0, 0, 0, 0] (by simp [ha0])) 0
    exact one_ne_zero h
  have hb : b ≠ 0 := by
    intro hb0
    have h := congr_fun (halbert ![0, 1, 0, 0, 0, 0] (by simp [hb0])) 1
    exact one_ne_zero h
  have hsq : ∀ k : F, k ≠ 0 →
      Fintype.card F + 1 ≤ 2 * (Finset.univ.image (fun x : F => k * x ^ 2)).card := by
    intro k hk
    let S := Finset.univ.image (fun x : F => k * x ^ 2)
    change Fintype.card F + 1 ≤ 2 * S.card
    have h0S : (0 : F) ∈ S := Finset.mem_image.mpr ⟨0, Finset.mem_univ _, by simp⟩
    have hpart : Fintype.card F =
        ∑ s ∈ S, (Finset.univ.filter (fun x : F => k * x ^ 2 = s)).card := by
      have := Finset.card_eq_sum_card_fiberwise
        (f := fun x : F => k * x ^ 2) (s := Finset.univ) (t := S)
        (fun x _ => Finset.mem_image_of_mem _ (Finset.mem_univ x))
      simpa using this
    have hfib0 : (Finset.univ.filter (fun x : F => k * x ^ 2 = 0)).card ≤ 1 := by
      have hsub : Finset.univ.filter (fun x : F => k * x ^ 2 = 0) ⊆ {0} := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, mul_eq_zero, sq_eq_zero_iff] at hx
        simp [hx.resolve_left hk]
      exact (Finset.card_le_card hsub).trans (by simp)
    have hfib : ∀ s ∈ S.erase 0, (Finset.univ.filter (fun x : F => k * x ^ 2 = s)).card ≤ 2 := by
      intro s hs
      obtain ⟨x₀, _, hx₀⟩ := Finset.mem_image.mp (Finset.mem_of_mem_erase hs)
      have hsub : Finset.univ.filter (fun x : F => k * x ^ 2 = s) ⊆ {x₀, -x₀} := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        have hsqeq : x ^ 2 = x₀ ^ 2 := mul_left_cancel₀ hk (hx.trans hx₀.symm)
        have := sq_eq_sq_iff_eq_or_eq_neg.mp hsqeq
        simpa using this
      exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
    rw [hpart, ← Finset.add_sum_erase _ _ h0S]
    have hsum : ∑ s ∈ S.erase 0, (Finset.univ.filter (fun x : F => k * x ^ 2 = s)).card ≤
        ∑ _s ∈ S.erase 0, 2 := Finset.sum_le_sum hfib
    rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem h0S] at hsum
    have hpos : 1 ≤ S.card := Finset.one_le_card.mpr ⟨0, h0S⟩
    omega
  let S₁ := Finset.univ.image (fun x : F => a * x ^ 2)
  let S₂ := Finset.univ.image (fun y : F => c - b * y ^ 2)
  have hS₁ : Fintype.card F + 1 ≤ 2 * S₁.card := hsq a ha
  have hS₂eq : S₂.card = (Finset.univ.image (fun y : F => b * y ^ 2)).card := by
    have : S₂ = (Finset.univ.image (fun y : F => b * y ^ 2)).image (fun z : F => c - z) := by
      ext z; simp [S₂]
    rw [this, Finset.card_image_of_injective _ (sub_right_injective)]
  have hS₂ : Fintype.card F + 1 ≤ 2 * S₂.card := by rw [hS₂eq]; exact hsq b hb
  have hinter : 0 < (S₁ ∩ S₂).card := by
    have hu := Finset.card_union_add_card_inter S₁ S₂
    have hle : (S₁ ∪ S₂).card ≤ Fintype.card F := Finset.card_le_univ _
    omega
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hinter
  rw [Finset.mem_inter] at hz
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hz.1
  obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hz.2
  have h0 : a * x ^ 2 + b * y ^ 2 - a * b * 0 ^ 2 - c * 1 ^ 2 - d * 0 ^ 2 + c * d * 0 ^ 2 = 0 := by
    have : a * x ^ 2 = c - b * y ^ 2 := hx.trans hy.symm
    linear_combination this
  have hvec := halbert ![x, y, 0, 1, 0, 0] (by
    have h0' : (![x, y, 0, 1, 0, 0] : Fin 6 → F) 0 = x := rfl
    have h1' : (![x, y, 0, 1, 0, 0] : Fin 6 → F) 1 = y := rfl
    have h2' : (![x, y, 0, 1, 0, 0] : Fin 6 → F) 2 = 0 := rfl
    have h3' : (![x, y, 0, 1, 0, 0] : Fin 6 → F) 3 = 1 := rfl
    have h4' : (![x, y, 0, 1, 0, 0] : Fin 6 → F) 4 = 0 := rfl
    have h5' : (![x, y, 0, 1, 0, 0] : Fin 6 → F) 5 = 0 := rfl
    rw [h0', h1', h2', h3', h4', h5']
    exact h0)
  have h10 : (![x, y, 0, 1, 0, 0] : Fin 6 → F) 3 = 0 := congr_fun hvec 3
  exact one_ne_zero h10

lemma countable_subfield_closure {L : Type} [Field L] {S : Set L} (hS : S.Countable) :
    Countable (Subfield.closure S) := by
  let step : Set L → Set L := fun A =>
    A ∪ ((fun p : L × L => p.1 + p.2) '' (A ×ˢ A))
      ∪ ((fun x : L => -x) '' A)
      ∪ ((fun p : L × L => p.1 * p.2) '' (A ×ˢ A))
      ∪ ((fun x : L => x⁻¹) '' A)
  let T : ℕ → Set L := fun n => Nat.rec (S ∪ ({0, 1} : Set L)) (fun _ A => step A) n
  have hT0 : (T 0).Countable := by
    change (S ∪ ({0, 1} : Set L)).Countable
    exact hS.union (by simp)
  have hstep : ∀ A : Set L, A.Countable → (step A).Countable := by
    intro A hA
    have hadd : ((fun p : L × L => p.1 + p.2) '' (A ×ˢ A)).Countable :=
      Set.Countable.image (Set.Countable.prod hA hA) _
    have hneg : ((fun x : L => -x) '' A).Countable := Set.Countable.image hA _
    have hmul : ((fun p : L × L => p.1 * p.2) '' (A ×ˢ A)).Countable :=
      Set.Countable.image (Set.Countable.prod hA hA) _
    have hinv : ((fun x : L => x⁻¹) '' A).Countable := Set.Countable.image hA _
    exact (((hA.union hadd).union hneg).union hmul).union hinv
  have hT : ∀ n, (T n).Countable := by
    intro n
    induction n with
    | zero => exact hT0
    | succ n ih =>
      change (step (T n)).Countable
      exact hstep (T n) ih
  let U : Set L := ⋃ n, T n
  have hU : U.Countable := by
    change (⋃ n, T n).Countable
    exact Set.countable_iUnion (fun n => hT n)
  have hmono : ∀ n, T n ⊆ T (n + 1) := by
    intro n
    change T n ⊆ step (T n)
    intro x hx
    simp only [step, Set.mem_union]
    tauto
  have hmono_le : ∀ {m k : ℕ}, m ≤ k → T m ⊆ T k := by
    intro m k h
    induction h with
    | refl => exact fun _ hx => hx
    | step h ih => exact ih.trans (hmono _)
  have hmemU : ∀ x ∈ S, x ∈ U := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨0, ?_⟩
    change x ∈ (S ∪ ({0, 1} : Set L))
    exact Or.inl hx
  have hone : (1 : L) ∈ U := by
    refine Set.mem_iUnion.mpr ⟨0, ?_⟩
    change (1 : L) ∈ (S ∪ ({0, 1} : Set L))
    exact Or.inr (by simp)
  have hadd : ∀ x y : L, x ∈ U → y ∈ U → x + y ∈ U := by
    intro x y hx hy
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hy
    have hm' : x ∈ T (max m k) := hmono_le (Nat.le_max_left _ _) hm
    have hk' : y ∈ T (max m k) := hmono_le (Nat.le_max_right _ _) hk
    refine Set.mem_iUnion.mpr ⟨max m k + 1, ?_⟩
    change x + y ∈ step (T (max m k))
    have himg : x + y ∈
        (fun p : L × L => p.1 + p.2) '' (T (max m k) ×ˢ T (max m k)) :=
      Set.mem_image_of_mem _ (Set.mk_mem_prod hm' hk')
    simp only [step, Set.mem_union]
    tauto
  have hneg : ∀ x : L, x ∈ U → -x ∈ U := by
    intro x hx
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
    refine Set.mem_iUnion.mpr ⟨m + 1, ?_⟩
    change -x ∈ step (T m)
    have himg : -x ∈ (fun y : L => -y) '' T m := Set.mem_image_of_mem _ hm
    simp only [step, Set.mem_union]
    tauto
  have hmul : ∀ x y : L, x ∈ U → y ∈ U → x * y ∈ U := by
    intro x y hx hy
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hy
    have hm' : x ∈ T (max m k) := hmono_le (Nat.le_max_left _ _) hm
    have hk' : y ∈ T (max m k) := hmono_le (Nat.le_max_right _ _) hk
    refine Set.mem_iUnion.mpr ⟨max m k + 1, ?_⟩
    change x * y ∈ step (T (max m k))
    have himg : x * y ∈
        (fun p : L × L => p.1 * p.2) '' (T (max m k) ×ˢ T (max m k)) :=
      Set.mem_image_of_mem _ (Set.mk_mem_prod hm' hk')
    simp only [step, Set.mem_union]
    tauto
  have hinv : ∀ x : L, x ∈ U → x⁻¹ ∈ U := by
    intro x hx
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
    refine Set.mem_iUnion.mpr ⟨m + 1, ?_⟩
    change x⁻¹ ∈ step (T m)
    have himg : x⁻¹ ∈ (fun y : L => y⁻¹) '' T m := Set.mem_image_of_mem _ hm
    simp only [step, Set.mem_union]
    tauto
  have hSU : (Subfield.closure S : Set L) ⊆ U := by
    intro x hx
    exact Subfield.closure_induction
      (p := fun x _ => x ∈ U)
      (fun x hx => hmemU x hx) hone
      (fun x y _ _ hxU hyU => hadd x y hxU hyU)
      (fun x _ hxU => hneg x hxU)
      (fun x _ hxU => hinv x hxU)
      (fun x y _ _ hxU hyU => hmul x y hxU hyU)
      hx
  exact hU.mono hSU

lemma not_mem_anisotropicDims_of_ge_seven {F : Type} [Field F] [NeZero (2 : F)]
    (h7 : ∀ w : Fin 7 → F, ∃ v : Fin 7 → F, v ≠ 0 ∧ ∑ i : Fin 7, w i * v i ^ 2 = 0)
    {n : ℕ} (hn : 7 ≤ n) : n ∉ anisotropicDims F := by
  intro hmem
  obtain ⟨Q, hQ⟩ := mem_anisotropicDims_iff.mp hmem
  have := invertibleOfNonzero (two_ne_zero : (2 : F) ≠ 0)
  obtain ⟨w, ⟨e⟩⟩ := Q.equivalent_weightedSumSquares
  have hW : (weightedSumSquares F w).Anisotropic := by
    intro v hv
    have h0 : Q (e.symm v) = 0 := by
      rw [← e.map_app (e.symm v)]
      simpa using hv
    simpa using hQ _ h0
  have hm : Module.finrank F (Fin n → F) = n := by simp
  generalize Module.finrank F (Fin n → F) = m at w hW hm
  subst m
  let w7 : Fin 7 → F := fun i => w ⟨i.1, by omega⟩
  obtain ⟨v, hv0, hvsum⟩ := h7 w7
  let u : Fin n → F := fun j => if h : j.1 < 7 then v ⟨j.1, h⟩ else 0
  have hu0 : u ≠ 0 := by
    intro hu
    apply hv0
    funext i
    have h := congr_fun hu ⟨i.1, by omega⟩
    simpa [u, i.2] using h
  have huW : weightedSumSquares F w u = 0 := by
    simp only [weightedSumSquares_apply, smul_eq_mul]
    let f7 : Fin 7 → Fin n := fun i => ⟨i.1, by omega⟩
    have hf7 : Function.Injective f7 := fun i₁ i₂ h => by ext; simpa [f7] using congr_arg Fin.val h
    have hsplit : ∑ j : Fin n, w j * (u j * u j) =
        ∑ i : Fin 7, w7 i * v i ^ 2 := by
      rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image f7))]
      · rw [Finset.sum_image (fun i₁ _ i₂ _ h => hf7 h)]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [f7, u, w7, i.2, _root_.sq]
      · intro j _ hj
        have hge : ¬ j.1 < 7 := by
          intro hlt
          exact hj (Finset.mem_image.mpr ⟨⟨j.1, hlt⟩, Finset.mem_univ _, by ext; rfl⟩)
        simp [u, hge]
    rw [hsplit, hvsum]
  exact hu0 (hW u huW)

lemma neZero_two_of_isHom {α β : Type} [Field α] [Field β] (g : α → β)
    (h1 : g 1 = 1)
    (ha : ∀ x y, g (x + y) = g x + g y)
    (hm : ∀ x y, g (x * y) = g x * g y)
    [h2K : NeZero (2 : α)] :
    NeZero (2 : β) := by
  have h11 : (1 : α) + 1 ≠ 0 := by rw [one_add_one_eq_two]; exact h2K.out
  have hu : ((1 : α) + 1) * ((1 : α) + 1)⁻¹ = 1 := mul_inv_cancel₀ h11
  refine ⟨fun h2 => ?_⟩
  have h11L : (1 : β) + 1 = 0 := by rw [one_add_one_eq_two]; exact h2
  have hg1 : g (((1 : α) + 1) * ((1 : α) + 1)⁻¹) = 1 := by rw [hu, h1]
  rw [hm, ha, h1, h11L, zero_mul] at hg1
  exact zero_ne_one hg1

lemma countable_step_on_option_nat (h2 : H2)
    (instK : Field (Option ℕ))
    (h2K : letI := instK; NeZero (2 : Option ℕ))
    (a b c d : Option ℕ)
    (hDK : letI := instK; NoZeroDivisors (QuaternionAlgebra (Option ℕ) a 0 b ⊗[Option ℕ] QuaternionAlgebra (Option ℕ) c 0 d))
    (w : Fin 7 → Option ℕ) :
    ∃ (instL : Field (Option ℕ))
      (g : @RingHom (Option ℕ) (Option ℕ) instK.toNonAssocSemiring instL.toNonAssocSemiring),
      letI := instL
      (∃ v : Fin 7 → Option ℕ, v ≠ 0 ∧ ∑ i : Fin 7, g (w i) * v i ^ 2 = 0) ∧
      NoZeroDivisors (QuaternionAlgebra (Option ℕ) (g a) 0 (g b) ⊗[Option ℕ] QuaternionAlgebra (Option ℕ) (g c) 0 (g d)) := by
  obtain ⟨L, instL, f, ⟨v, hv0, hvsum⟩, hDL⟩ := @h2 (Option ℕ) instK h2K a b c d hDK w
  let S : Set L := Set.range f ∪ Set.range v
  have hS : S.Countable := (Set.countable_range f).union (Set.countable_range v)
  let L' : Subfield L := Subfield.closure S
  haveI : Countable L' := countable_subfield_closure hS
  have hf_mem : ∀ x : Option ℕ, f x ∈ L' := fun x => Subfield.subset_closure (Or.inl ⟨x, rfl⟩)
  have hv_mem : ∀ i : Fin 7, v i ∈ L' := fun i => Subfield.subset_closure (Or.inr ⟨i, rfl⟩)
  let f_sub : @RingHom (Option ℕ) L' instK.toNonAssocSemiring inferInstance := by
    letI := instK
    exact
      { toFun := fun x => ⟨f x, hf_mem x⟩
        map_one' := Subtype.ext f.map_one
        map_mul' := fun x y => Subtype.ext (f.map_mul x y)
        map_zero' := Subtype.ext f.map_zero
        map_add' := fun x y => Subtype.ext (f.map_add x y) }
  have hf_inj : Function.Injective f := by
    letI := instK
    exact f.injective
  haveI : Infinite L' := by
    refine Infinite.of_injective (fun x : Option ℕ => (⟨f x, hf_mem x⟩ : L')) ?_
    intro x y hxy
    exact hf_inj (congr_arg Subtype.val hxy)
  letI : Encodable L' := Encodable.ofCountable L'
  letI : Denumerable L' := Denumerable.ofEncodableOfInfinite L'
  let e : Option ℕ ≃ L' := (Denumerable.eqv (Option ℕ)).trans (Denumerable.eqv L').symm
  let instNext : Field (Option ℕ) := e.field
  let j : @RingHom (Option ℕ) L instNext.toNonAssocSemiring instL.toNonAssocSemiring := by
    letI := instNext
    exact
      { toFun := fun x => (e x : L)
        map_one' := by
          change (e (e.symm 1) : L) = 1
          rw [e.apply_symm_apply]; rfl
        map_mul' := fun x y => by
          change (e (e.symm (e x * e y)) : L) = (e x : L) * (e y : L)
          rw [e.apply_symm_apply]; rfl
        map_zero' := by
          change (e (e.symm 0) : L) = 0
          rw [e.apply_symm_apply]; rfl
        map_add' := fun x y => by
          change (e (e.symm (e x + e y)) : L) = (e x : L) + (e y : L)
          rw [e.apply_symm_apply]; rfl }
  let e_symm_hom : @RingHom L' (Option ℕ) inferInstance instNext.toNonAssocSemiring := by
    letI := instNext
    exact
      { toFun := e.symm
        map_one' := rfl
        map_mul' := fun x y => by
          change e.symm (x * y) = e.symm (e (e.symm x) * e (e.symm y))
          rw [e.apply_symm_apply, e.apply_symm_apply]
        map_zero' := rfl
        map_add' := fun x y => by
          change e.symm (x + y) = e.symm (e (e.symm x) + e (e.symm y))
          rw [e.apply_symm_apply, e.apply_symm_apply] }
  let g : @RingHom (Option ℕ) (Option ℕ) instK.toNonAssocSemiring instNext.toNonAssocSemiring :=
    @RingHom.comp (Option ℕ) L' (Option ℕ) instK.toNonAssocSemiring inferInstance
      instNext.toNonAssocSemiring e_symm_hom f_sub
  have hjg : ∀ x, j (g x) = f x := fun x => by
    change (e (e.symm ⟨f x, hf_mem x⟩) : L) = f x
    rw [e.apply_symm_apply]
  refine ⟨instNext, g, ?_, ?_⟩
  · letI := instNext
    let v' : Fin 7 → Option ℕ := fun i => e.symm ⟨v i, hv_mem i⟩
    have hjv : ∀ i, j (v' i) = v i := fun i => by
      change (e (e.symm ⟨v i, hv_mem i⟩) : L) = v i
      rw [e.apply_symm_apply]
    refine ⟨v', ?_, ?_⟩
    · intro hv'0
      apply hv0
      funext i
      rw [← hjv i, congr_fun hv'0 i]
      exact j.map_zero
    · apply j.injective
      rw [map_sum, map_zero]
      convert hvsum using 2 with i
      rw [map_mul, map_pow, hjg, hjv]
  · letI := instNext
    have hDL' : NoZeroDivisors
        (QuaternionAlgebra L (j (g a)) 0 (j (g b)) ⊗[L] QuaternionAlgebra L (j (g c)) 0 (j (g d))) := by
      rw [hjg, hjg, hjg, hjg]
      exact hDL
    exact noZeroDivisors_biquat_of_ringHom j (g a) (g b) (g c) (g d) hDL'

lemma exists_tower_of_hyps (h1 : H1) (h2 : H2) :
    ∃ (G : ℕ → Type) (_ : ∀ n, Field (G n))
      (trans : ∀ i j, i ≤ j → G i →+* G j)
      (_ : DirectedSystem G (fun i j h => trans i j h))
      (a b c d : G 0),
      NeZero (2 : G 0) ∧
      (∀ n, NoZeroDivisors
        (QuaternionAlgebra (G n) (trans 0 n (Nat.zero_le n) a) 0 (trans 0 n (Nat.zero_le n) b) ⊗[G n]
         QuaternionAlgebra (G n) (trans 0 n (Nat.zero_le n) c) 0 (trans 0 n (Nat.zero_le n) d))) ∧
      (∀ (i : ℕ) (w : Fin 7 → G i), ∃ (m : ℕ) (him : i ≤ m) (v : Fin 7 → G m),
        v ≠ 0 ∧ ∑ r : Fin 7, trans i m him (w r) * v r ^ 2 = 0) := by
  obtain ⟨F₀, instF₀, h2₀, hC₀, a₀, b₀, c₀, d₀, hD₀⟩ := h1
  haveI : Infinite F₀ := infinite_of_noZeroDivisors_biquat a₀ b₀ c₀ d₀ hD₀
  letI : Encodable F₀ := Encodable.ofCountable F₀
  letI : Denumerable F₀ := Denumerable.ofEncodableOfInfinite F₀
  let e₀ : Option ℕ ≃ F₀ := (Denumerable.eqv (Option ℕ)).trans (Denumerable.eqv F₀).symm
  let inst₀ : Field (Option ℕ) := e₀.field
  let j₀ : @RingHom (Option ℕ) F₀ inst₀.toNonAssocSemiring instF₀.toNonAssocSemiring :=
    { toFun := fun x => e₀ x
      map_one' := e₀.apply_symm_apply 1
      map_mul' := fun x y => e₀.apply_symm_apply (e₀ x * e₀ y)
      map_zero' := e₀.apply_symm_apply 0
      map_add' := fun x y => e₀.apply_symm_apply (e₀ x + e₀ y) }
  let a' : Option ℕ := e₀.symm a₀
  let b' : Option ℕ := e₀.symm b₀
  let c' : Option ℕ := e₀.symm c₀
  let d' : Option ℕ := e₀.symm d₀
  have hj₀a : j₀ a' = a₀ := e₀.apply_symm_apply a₀
  have hj₀b : j₀ b' = b₀ := e₀.apply_symm_apply b₀
  have hj₀c : j₀ c' = c₀ := e₀.apply_symm_apply c₀
  have hj₀d : j₀ d' = d₀ := e₀.apply_symm_apply d₀
  have h2₀' : letI := inst₀; NeZero (2 : Option ℕ) := by
    letI := inst₀
    refine ⟨fun h => ?_⟩
    have := congr_arg j₀ h
    rw [map_ofNat, map_zero] at this
    exact NeZero.ne (2 : F₀) this
  have hD₀' : letI := inst₀
      NoZeroDivisors (QuaternionAlgebra (Option ℕ) a' 0 b' ⊗[Option ℕ] QuaternionAlgebra (Option ℕ) c' 0 d') := by
    letI := inst₀
    have hDL : NoZeroDivisors
        (QuaternionAlgebra F₀ (j₀ a') 0 (j₀ b') ⊗[F₀] QuaternionAlgebra F₀ (j₀ c') 0 (j₀ d')) := by
      rw [hj₀a, hj₀b, hj₀c, hj₀d]
      exact hD₀
    exact noZeroDivisors_biquat_of_ringHom j₀ a' b' c' d' hDL
  obtain ⟨enum7, henum7⟩ := exists_surjective_nat (Fin 7 → Option ℕ)
  -- Helper: iterate a sequence of bare functions `steps : ℕ → Option ℕ → Option ℕ` from `i` to `j`.
  let iter (steps : ℕ → Option ℕ → Option ℕ) (i j : ℕ) : Option ℕ → Option ℕ :=
    Nat.rec id (fun k acc => steps (i + k) ∘ acc) (j - i)
  have hiter_self : ∀ steps i x, iter steps i i x = x := fun steps i x => by
    simp [iter]
  have hiter_succ : ∀ steps i j, i ≤ j → ∀ x,
      iter steps i (j + 1) x = steps j (iter steps i j x) := fun steps i j hij x => by
    have hsub : j + 1 - i = (j - i) + 1 := by omega
    have hadd : i + (j - i) = j := by omega
    simp only [iter, hsub, Function.comp_apply, hadd]
  have hiter_congr : ∀ steps₁ steps₂ n, (∀ k < n, steps₁ k = steps₂ k) →
      ∀ i j, i ≤ j → j ≤ n → ∀ x, iter steps₁ i j x = iter steps₂ i j x := by
    intro steps₁ steps₂ n hagree i j hij hjn
    induction j with
    | zero =>
      have hi : i = 0 := by omega
      subst hi; intro x; simp [hiter_self]
    | succ j ih =>
      rcases eq_or_lt_of_le hij with rfl | hlt
      · intro x; simp [hiter_self]
      · have hij' : i ≤ j := by omega
        intro x
        rw [hiter_succ _ i j hij', hiter_succ _ i j hij', hagree j (by omega),
          ih hij' (by omega)]
  have hiter_comp : ∀ steps i j k, i ≤ j → j ≤ k → ∀ x,
      iter steps j k (iter steps i j x) = iter steps i k x := by
    intro steps i j k hij hjk
    induction k with
    | zero =>
      have hj : j = 0 := by omega
      have hi : i = 0 := by omega
      subst hi; subst hj; intro x; simp [hiter_self]
    | succ k ih =>
      rcases eq_or_lt_of_le hjk with rfl | hlt
      · intro x; simp [hiter_self]
      · have hjk' : j ≤ k := by omega
        intro x
        rw [hiter_succ _ j k hjk', hiter_succ _ i k (by omega), ih hjk']
  let IsHom (iK iL : Field (Option ℕ)) (g : Option ℕ → Option ℕ) : Prop :=
    g (@Zero.zero _ iK.toZero) = @Zero.zero _ iL.toZero ∧
    g (@One.one _ iK.toOne) = @One.one _ iL.toOne ∧
    (∀ x y, g (@HAdd.hAdd _ _ _ (@instHAdd _ iK.toAdd) x y) =
      @HAdd.hAdd _ _ _ (@instHAdd _ iL.toAdd) (g x) (g y)) ∧
    (∀ x y, g (@HMul.hMul _ _ _ (@instHMul _ iK.toMul) x y) =
      @HMul.hMul _ _ _ (@instHMul _ iL.toMul) (g x) (g y))
  have hiter_hom : ∀ (insts : ℕ → Field (Option ℕ)) (steps : ℕ → Option ℕ → Option ℕ) n,
      (∀ k < n, IsHom (insts k) (insts (k + 1)) (steps k)) →
      ∀ i j, i ≤ j → j ≤ n → IsHom (insts i) (insts j) (iter steps i j) := by
    intro insts steps n hhom i j hij hjn
    induction j with
    | zero =>
      have hi : i = 0 := by omega
      subst hi
      refine ⟨hiter_self steps 0 _, hiter_self steps 0 _, fun x y => by simp [hiter_self],
        fun x y => by simp [hiter_self]⟩
    | succ j ih =>
      rcases eq_or_lt_of_le hij with rfl | hlt
      · refine ⟨hiter_self steps (j + 1) _, hiter_self steps (j + 1) _,
          fun x y => by simp [hiter_self], fun x y => by simp [hiter_self]⟩
      · have hij' : i ≤ j := by omega
        obtain ⟨h0a, h1a, hadda, hmula⟩ := ih hij' (by omega)
        obtain ⟨h0b, h1b, haddb, hmulb⟩ := hhom j (by omega)
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hiter_succ steps i j hij', h0a, h0b]
        · rw [hiter_succ steps i j hij', h1a, h1b]
        · intro x y; rw [hiter_succ steps i j hij', hadda, haddb, ← hiter_succ steps i j hij',
            ← hiter_succ steps i j hij']
        · intro x y; rw [hiter_succ steps i j hij', hmula, hmulb, ← hiter_succ steps i j hij',
            ← hiter_succ steps i j hij']
  let Valid (n : ℕ) (insts : ℕ → Field (Option ℕ)) (steps : ℕ → Option ℕ → Option ℕ) : Prop :=
    insts 0 = inst₀ ∧
    (∀ k < n, IsHom (insts k) (insts (k + 1)) (steps k)) ∧
    (∀ k ≤ n, letI := insts k
      NoZeroDivisors
        (QuaternionAlgebra (Option ℕ) (iter steps 0 k a') 0 (iter steps 0 k b') ⊗[Option ℕ]
         QuaternionAlgebra (Option ℕ) (iter steps 0 k c') 0 (iter steps 0 k d'))) ∧
    (∀ m < n, letI := insts (m + 1)
      ∃ v : Fin 7 → Option ℕ, v ≠ 0 ∧
        ∑ r : Fin 7, iter steps (Nat.unpair m).1 (m + 1) (enum7 (Nat.unpair m).2 r) * v r ^ 2 = 0)
  have hstep : ∀ n (p : { p : (ℕ → Field (Option ℕ)) × (ℕ → Option ℕ → Option ℕ) // Valid n p.1 p.2 }),
      ∃ q : { p : (ℕ → Field (Option ℕ)) × (ℕ → Option ℕ → Option ℕ) // Valid (n + 1) p.1 p.2 },
        (∀ k ≤ n, q.val.1 k = p.val.1 k) ∧ (∀ k < n, q.val.2 k = p.val.2 k) := by
    intro n ⟨⟨insts, steps⟩, h0eq, hhom, hdiv, hiso⟩
    dsimp only at h0eq hhom hdiv hiso
    have h2n : letI := insts n; NeZero (2 : Option ℕ) := by
      obtain ⟨_, ho, ha, hm⟩ := hiter_hom insts steps n hhom 0 n (Nat.zero_le n) le_rfl
      have h20 : letI := insts 0; NeZero (2 : Option ℕ) := by rw [h0eq]; exact h2₀'
      exact @neZero_two_of_isHom (Option ℕ) (Option ℕ) (insts 0) (insts n)
        (iter steps 0 n) ho ha hm h20
    let i := (Nat.unpair n).1
    let j := (Nat.unpair n).2
    have hin : i ≤ n := Nat.unpair_left_le n
    let w : Fin 7 → Option ℕ := fun r => iter steps i n (enum7 j r)
    have hspec := countable_step_on_option_nat h2 (insts n) h2n
      (iter steps 0 n a') (iter steps 0 n b') (iter steps 0 n c') (iter steps 0 n d')
      (hdiv n le_rfl) w
    let instNext := Classical.choose hspec
    let g := Classical.choose (Classical.choose_spec hspec)
    have hg_spec := Classical.choose_spec (Classical.choose_spec hspec)
    let insts' := Function.update insts (n + 1) instNext
    let steps' := Function.update steps n (g : Option ℕ → Option ℕ)
    have hinsts_le : ∀ k ≤ n, insts' k = insts k := fun k hk =>
      Function.update_of_ne (by omega) _ _
    have hsteps_lt : ∀ k < n, steps' k = steps k := fun k hk =>
      Function.update_of_ne (by omega) _ _
    have hiter_eq : ∀ u v, u ≤ v → v ≤ n → ∀ x, iter steps' u v x = iter steps u v x :=
      hiter_congr steps' steps n hsteps_lt
    have hvalid' : Valid (n + 1) insts' steps' := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hinsts_le 0 (Nat.zero_le n), h0eq]
      · intro k hk
        rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hk) with hkn | hlt
        · subst k
          rw [hinsts_le n le_rfl]
          have h1 : insts' (n + 1) = instNext := Function.update_self (n + 1) instNext insts
          have h2 : steps' n = (g : Option ℕ → Option ℕ) := Function.update_self n _ steps
          rw [h1, h2]
          exact ⟨g.map_zero, g.map_one, g.map_add, g.map_mul⟩
        · rw [hinsts_le k (by omega), hinsts_le (k + 1) (by omega), hsteps_lt k hlt]
          exact hhom k hlt
      · intro k hk
        rcases eq_or_lt_of_le hk with hkn | hlt
        · subst k
          have h1 : insts' (n + 1) = instNext := Function.update_self (n + 1) instNext insts
          have h2 : steps' n = (g : Option ℕ → Option ℕ) := Function.update_self n _ steps
          have hstep_a : iter steps' 0 (n + 1) a' = g (iter steps 0 n a') := by
            rw [hiter_succ steps' 0 n (Nat.zero_le n), h2, hiter_eq 0 n (Nat.zero_le n) le_rfl]
          have hstep_b : iter steps' 0 (n + 1) b' = g (iter steps 0 n b') := by
            rw [hiter_succ steps' 0 n (Nat.zero_le n), h2, hiter_eq 0 n (Nat.zero_le n) le_rfl]
          have hstep_c : iter steps' 0 (n + 1) c' = g (iter steps 0 n c') := by
            rw [hiter_succ steps' 0 n (Nat.zero_le n), h2, hiter_eq 0 n (Nat.zero_le n) le_rfl]
          have hstep_d : iter steps' 0 (n + 1) d' = g (iter steps 0 n d') := by
            rw [hiter_succ steps' 0 n (Nat.zero_le n), h2, hiter_eq 0 n (Nat.zero_le n) le_rfl]
          rw [hstep_a, hstep_b, hstep_c, hstep_d, h1]
          exact hg_spec.2
        · have hk' : k ≤ n := by omega
          rw [hinsts_le k hk', hiter_eq 0 k (Nat.zero_le k) hk', hiter_eq 0 k (Nat.zero_le k) hk',
            hiter_eq 0 k (Nat.zero_le k) hk', hiter_eq 0 k (Nat.zero_le k) hk']
          exact hdiv k hk'
      · intro m hm
        rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hm) with hmn | hlt
        · subst m
          have h1 : insts' (n + 1) = instNext := Function.update_self (n + 1) instNext insts
          have h2 : steps' n = (g : Option ℕ → Option ℕ) := Function.update_self n _ steps
          rw [h1]
          obtain ⟨v, hv0, hvsum⟩ := hg_spec.1
          refine ⟨v, hv0, ?_⟩
          have hterms : ∀ r : Fin 7,
              iter steps' (Nat.unpair n).1 (n + 1) (enum7 (Nat.unpair n).2 r) = g (w r) := by
            intro r
            change iter steps' i (n + 1) (enum7 j r) = g (iter steps i n (enum7 j r))
            rw [hiter_succ steps' i n hin, h2, hiter_eq i n hin le_rfl]
          have hsum :
              (letI := instNext
                ∑ r : Fin 7, iter steps' (Nat.unpair n).1 (n + 1) (enum7 (Nat.unpair n).2 r) * v r ^ 2) =
              (letI := instNext
                ∑ r : Fin 7, g (w r) * v r ^ 2) :=
            Finset.sum_congr rfl fun r _ => by rw [hterms r]
          rw [hsum]
          exact hvsum
        · have hmu : (Nat.unpair m).1 ≤ m := Nat.unpair_left_le m
          rw [hinsts_le (m + 1) (by omega)]
          obtain ⟨v, hv0, hvsum⟩ := hiso m hlt
          refine ⟨v, hv0, ?_⟩
          have hterms : ∀ r : Fin 7,
              iter steps' (Nat.unpair m).1 (m + 1) (enum7 (Nat.unpair m).2 r) =
              iter steps (Nat.unpair m).1 (m + 1) (enum7 (Nat.unpair m).2 r) := fun r =>
            hiter_eq (Nat.unpair m).1 (m + 1) (by omega) (by omega) _
          have hsum :
              letI := insts (m + 1)
              ∑ r : Fin 7, iter steps' (Nat.unpair m).1 (m + 1) (enum7 (Nat.unpair m).2 r) * v r ^ 2 =
              ∑ r : Fin 7, iter steps (Nat.unpair m).1 (m + 1) (enum7 (Nat.unpair m).2 r) * v r ^ 2 := by
            letI := insts (m + 1)
            exact Finset.sum_congr rfl fun r _ => by rw [hterms r]
          rw [hsum]
          exact hvsum
    exact ⟨⟨⟨insts', steps'⟩, hvalid'⟩, hinsts_le, hsteps_lt⟩
  have hbase : Valid 0 (fun _ => inst₀) (fun _ => id) := by
    refine ⟨rfl, fun k hk => by omega, ?_, fun m hm => by omega⟩
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    exact hD₀'
  let stepRec : ∀ n,
      { p : (ℕ → Field (Option ℕ)) × (ℕ → Option ℕ → Option ℕ) // Valid n p.1 p.2 } →
      { p : (ℕ → Field (Option ℕ)) × (ℕ → Option ℕ → Option ℕ) // Valid (n + 1) p.1 p.2 } :=
    fun n p => Classical.choose (hstep n p)
  let P : ∀ n, { p : (ℕ → Field (Option ℕ)) × (ℕ → Option ℕ → Option ℕ) // Valid n p.1 p.2 } :=
    fun n => Nat.rec ⟨⟨fun _ => inst₀, fun _ => id⟩, hbase⟩ stepRec n
  have hP_inst_step : ∀ n k, k ≤ n → (P (n + 1)).val.1 k = (P n).val.1 k := fun n k hk =>
    (Classical.choose_spec (hstep n (P n))).1 k hk
  have hP_steps_step : ∀ n k, k < n → (P (n + 1)).val.2 k = (P n).val.2 k := fun n k hk =>
    (Classical.choose_spec (hstep n (P n))).2 k hk
  have hP_inst_stable : ∀ k n, k ≤ n → (P n).val.1 k = (P k).val.1 k := by
    intro k n hkn
    induction n with
    | zero =>
      have hk : k = 0 := by omega
      subst hk
      rfl
    | succ n ih =>
      rcases eq_or_lt_of_le hkn with rfl | hlt
      · rfl
      · rw [hP_inst_step n k (by omega), ih (by omega)]
  have hP_steps_stable : ∀ k n, k < n → (P n).val.2 k = (P (k + 1)).val.2 k := by
    intro k n hkn
    induction n with
    | zero => omega
    | succ n ih =>
      rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hkn) with rfl | hlt
      · rfl
      · rw [hP_steps_step n k hlt, ih hlt]
  let F_inst : ℕ → Field (Option ℕ) := fun k => (P k).val.1 k
  let F_step : ℕ → Option ℕ → Option ℕ := fun k => (P (k + 1)).val.2 k
  have hF_step_hom : ∀ k, IsHom (F_inst k) (F_inst (k + 1)) (F_step k) := fun k => by
    have h := (P (k + 1)).property.2.1 k (Nat.lt_succ_self k)
    rw [hP_inst_stable k (k + 1) (Nat.le_succ k)] at h
    exact h
  have hF_iter_eq : ∀ n i j, i ≤ j → j ≤ n → ∀ x,
      iter F_step i j x = iter (P n).val.2 i j x := fun n i j hij hjn =>
    hiter_congr F_step (P n).val.2 n (fun k hk => (hP_steps_stable k n hk).symm) i j hij hjn
  -- Wrap each stage as a distinct type `G n` so `Field (G n)` synthesizes cleanly.
  let G : ℕ → Type := fun n => { _x : Option ℕ // n = n }
  let eG : ∀ n, G n ≃ Option ℕ := fun n =>
    { toFun := Subtype.val, invFun := fun x => ⟨x, rfl⟩,
      left_inv := fun ⟨_, _⟩ => rfl, right_inv := fun _ => rfl }
  let instG : ∀ n, Field (G n) := fun n => @Equiv.field (G n) (Option ℕ) (eG n) (F_inst n)
  letI : ∀ n, Field (G n) := instG
  let trans : ∀ i j, i ≤ j → G i →+* G j := fun i j hij =>
    have hhom := hiter_hom F_inst F_step j (fun k _ => hF_step_hom k) i j hij le_rfl
    { toFun := fun x => ⟨iter F_step i j x.val, rfl⟩
      map_one' := Subtype.ext hhom.2.1
      map_mul' := fun x y => Subtype.ext (hhom.2.2.2 x.val y.val)
      map_zero' := Subtype.ext hhom.1
      map_add' := fun x y => Subtype.ext (hhom.2.2.1 x.val y.val) }
  have hsys : DirectedSystem G (fun i j h => trans i j h) :=
    { map_self := fun i x => Subtype.ext (hiter_self F_step i x.val)
      map_map := by
        intro i j k h1 h2 x
        first
        | exact Subtype.ext (hiter_comp F_step _ _ _ h1 h2 x.val)
        | exact Subtype.ext (hiter_comp F_step _ _ _ h2 h1 x.val) }
  let heG_hom : ∀ n, @RingHom (G n) (Option ℕ) (instG n).toNonAssocSemiring (F_inst n).toNonAssocSemiring :=
    fun n => by
      letI := F_inst n
      exact
        { toFun := fun x => x.val
          map_one' := rfl
          map_mul' := fun _ _ => rfl
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
  refine ⟨G, instG, trans, hsys, ⟨a', rfl⟩, ⟨b', rfl⟩, ⟨c', rfl⟩, ⟨d', rfl⟩, ?_, ?_, ?_⟩
  · have h0eq : F_inst 0 = inst₀ := (P 0).property.1
    have h2F0 : letI := F_inst 0; NeZero (2 : Option ℕ) := by rw [h0eq]; exact h2₀'
    letI := F_inst 0
    refine ⟨fun h => ?_⟩
    have hv := congr_arg (heG_hom 0) h
    rw [map_ofNat, map_zero] at hv
    exact h2F0.out hv
  · intro n
    have hDn := (P n).property.2.2.1 n le_rfl
    have heq_a : heG_hom n (trans 0 n (Nat.zero_le n) ⟨a', rfl⟩) = iter (P n).val.2 0 n a' :=
      hF_iter_eq n 0 n (Nat.zero_le n) le_rfl a'
    have heq_b : heG_hom n (trans 0 n (Nat.zero_le n) ⟨b', rfl⟩) = iter (P n).val.2 0 n b' :=
      hF_iter_eq n 0 n (Nat.zero_le n) le_rfl b'
    have heq_c : heG_hom n (trans 0 n (Nat.zero_le n) ⟨c', rfl⟩) = iter (P n).val.2 0 n c' :=
      hF_iter_eq n 0 n (Nat.zero_le n) le_rfl c'
    have heq_d : heG_hom n (trans 0 n (Nat.zero_le n) ⟨d', rfl⟩) = iter (P n).val.2 0 n d' :=
      hF_iter_eq n 0 n (Nat.zero_le n) le_rfl d'
    have hDn' : letI := F_inst n
        NoZeroDivisors
          (QuaternionAlgebra (Option ℕ) (heG_hom n (trans 0 n (Nat.zero_le n) ⟨a', rfl⟩)) 0
            (heG_hom n (trans 0 n (Nat.zero_le n) ⟨b', rfl⟩)) ⊗[Option ℕ]
           QuaternionAlgebra (Option ℕ) (heG_hom n (trans 0 n (Nat.zero_le n) ⟨c', rfl⟩)) 0
            (heG_hom n (trans 0 n (Nat.zero_le n) ⟨d', rfl⟩))) := by
      rw [heq_a, heq_b, heq_c, heq_d]
      exact hDn
    exact @noZeroDivisors_biquat_of_ringHom (G n) (Option ℕ) (instG n) (F_inst n)
      (heG_hom n) _ _ _ _ hDn'
  · intro i w
    obtain ⟨j, hj⟩ := henum7 (fun r => (w r).val)
    let m0 := Nat.pair i j
    have him0 : i ≤ m0 := by
      have := Nat.unpair_left_le m0
      simpa [m0, Nat.unpair_pair] using this
    have hiso_m := (P (m0 + 1)).property.2.2.2 m0 (Nat.lt_succ_self m0)
    simp only [m0, Nat.unpair_pair, hj] at hiso_m
    obtain ⟨v, hv0, hvsum⟩ := hiso_m
    refine ⟨m0 + 1, by omega, fun r => ⟨v r, rfl⟩, ?_, ?_⟩
    · intro hv'
      apply hv0
      funext r
      exact congr_arg Subtype.val (congr_fun hv' r)
    · letI := F_inst (m0 + 1)
      apply (heG_hom (m0 + 1)).injective
      rw [map_sum, map_zero]
      have hterms : ∀ r : Fin 7,
          heG_hom (m0 + 1) (trans i (m0 + 1) (by omega) (w r) * (⟨v r, rfl⟩ : G (m0 + 1)) ^ 2) =
          iter (P (m0 + 1)).val.2 i (m0 + 1) (w r).val * v r ^ 2 := fun r => by
        rw [map_mul, map_pow]
        congr 1
        exact hF_iter_eq (m0 + 1) i (m0 + 1) (by omega) le_rfl (w r).val
      rw [Finset.sum_congr rfl fun r _ => hterms r]
      exact hvsum

lemma isUInvariant_six_of_tower
    (G : ℕ → Type) [∀ n, Field (G n)]
    (trans : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h => trans i j h)]
    (a b c d : G 0) [NeZero (2 : G 0)]
    (hdiv : ∀ n, NoZeroDivisors
      (QuaternionAlgebra (G n) (trans 0 n (Nat.zero_le n) a) 0 (trans 0 n (Nat.zero_le n) b) ⊗[G n]
       QuaternionAlgebra (G n) (trans 0 n (Nat.zero_le n) c) 0 (trans 0 n (Nat.zero_le n) d)))
    (hiso : ∀ (i : ℕ) (w : Fin 7 → G i), ∃ (m : ℕ) (him : i ≤ m) (v : Fin 7 → G m),
      v ≠ 0 ∧ ∑ r : Fin 7, trans i m him (w r) * v r ^ 2 = 0) :
    IsUInvariant 6 := by
  let FLim : Type := DirectLimit G trans
  let of : ∀ n, G n →+* FLim := fun n => DirectLimit.Ring.of G trans n
  haveI h2Lim : NeZero (2 : FLim) := by
    refine ⟨fun h => ?_⟩
    have h' : of 0 2 = of 0 0 := by rw [map_ofNat, map_zero]; exact h
    exact NeZero.ne (2 : G 0) ((of 0).injective h')
  have hlift : ∀ {ι : Type} [Fintype ι] (u : ι → FLim),
      ∃ (N : ℕ) (uN : ι → G N), ∀ t, of N (uN t) = u t := by
    intro ι _ u
    choose idx val hval using fun t => DirectLimit.exists_eq_mk trans (u t)
    let N := Finset.univ.sup idx
    refine ⟨N, fun t => trans (idx t) N (Finset.le_sup (Finset.mem_univ t)) (val t), fun t => ?_⟩
    change DirectLimit.Ring.of G trans N _ = u t
    rw [DirectLimit.Ring.of_f]
    exact (hval t).symm
  let aLim : FLim := of 0 a
  let bLim : FLim := of 0 b
  let cLim : FLim := of 0 c
  let dLim : FLim := of 0 d
  have hDLim : NoZeroDivisors
      (QuaternionAlgebra FLim aLim 0 bLim ⊗[FLim] QuaternionAlgebra FLim cLim 0 dLim) := by
    refine ⟨fun {x y} hxy => ?_⟩
    let BLim := (QuaternionAlgebra.basisOneIJK aLim 0 bLim).tensorProduct
      (QuaternionAlgebra.basisOneIJK cLim 0 dLim)
    let u : (Fin 4 × Fin 4) ⊕ (Fin 4 × Fin 4) → FLim :=
      Sum.elim (fun p => BLim.repr x p) (fun p => BLim.repr y p)
    obtain ⟨N, uN, huN⟩ := hlift u
    let aN := trans 0 N (Nat.zero_le N) a
    let bN := trans 0 N (Nat.zero_le N) b
    let cN := trans 0 N (Nat.zero_le N) c
    let dN := trans 0 N (Nat.zero_le N) d
    have haN : of N aN = aLim := DirectLimit.Ring.of_f (G := G) (f := trans) (Nat.zero_le N) a
    have hbN : of N bN = bLim := DirectLimit.Ring.of_f (G := G) (f := trans) (Nat.zero_le N) b
    have hcN : of N cN = cLim := DirectLimit.Ring.of_f (G := G) (f := trans) (Nat.zero_le N) c
    have hdN : of N dN = dLim := DirectLimit.Ring.of_f (G := G) (f := trans) (Nat.zero_le N) d
    let BN := (QuaternionAlgebra.basisOneIJK aN 0 bN).tensorProduct
      (QuaternionAlgebra.basisOneIJK cN 0 dN)
    let xN := BN.repr.symm (Finsupp.equivFunOnFinite.symm (fun p => uN (Sum.inl p)))
    let yN := BN.repr.symm (Finsupp.equivFunOnFinite.symm (fun p => uN (Sum.inr p)))
    have hmap := exists_biquat_ringHom (of N) aN bN cN dN
    rw [haN, hbN, hcN, hdN] at hmap
    obtain ⟨φN, hφN_inj, hφN_repr⟩ := hmap
    have hxN : φN xN = x := by
      apply BLim.repr.injective
      ext ⟨i, j⟩
      rw [hφN_repr xN i j]
      have hcoord : BN.repr xN (i, j) = uN (Sum.inl (i, j)) := by
        simp [xN]
      rw [hcoord, huN (Sum.inl (i, j))]
      rfl
    have hyN : φN yN = y := by
      apply BLim.repr.injective
      ext ⟨i, j⟩
      rw [hφN_repr yN i j]
      have hcoord : BN.repr yN (i, j) = uN (Sum.inr (i, j)) := by
        simp [yN]
      rw [hcoord, huN (Sum.inr (i, j))]
      rfl
    have hmulN : xN * yN = 0 := by
      apply hφN_inj
      rw [map_mul, map_zero, hxN, hyN, hxy]
    rcases (hdiv N).eq_zero_or_eq_zero_of_mul_eq_zero hmulN with hx0 | hy0
    · left; rw [← hxN, hx0, map_zero]
    · right; rw [← hyN, hy0, map_zero]
  have h6mem : 6 ∈ anisotropicDims FLim :=
    six_mem_anisotropicDims_of_noZeroDivisors aLim bLim cLim dLim hDLim
  have h7iso : ∀ w : Fin 7 → FLim, ∃ v : Fin 7 → FLim, v ≠ 0 ∧ ∑ r : Fin 7, w r * v r ^ 2 = 0 := by
    intro w
    obtain ⟨i, wi, hwi⟩ := hlift w
    obtain ⟨m, him, v, hv0, hvsum⟩ := hiso i wi
    refine ⟨fun r => of m (v r), ?_, ?_⟩
    · intro hvLim
      apply hv0
      funext r
      apply (of m).injective
      change of m (v r) = of m 0
      rw [map_zero]
      simpa using congr_fun hvLim r
    · have hsum : ∑ r : Fin 7, w r * (of m (v r)) ^ 2 =
          of m (∑ r : Fin 7, trans i m him (wi r) * v r ^ 2) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [map_mul, map_pow, ← hwi r]
        congr 1
        exact (DirectLimit.Ring.of_f (G := G) (f := trans) him (wi r)).symm
      rw [hsum, hvsum, map_zero]
  have h6ub : 6 ∈ upperBounds (anisotropicDims FLim) := by
    intro n hn
    by_contra hgt
    exact not_mem_anisotropicDims_of_ge_seven h7iso (by omega : 7 ≤ n) hn
  exact ⟨FLim, inferInstance, h2Lim, h6mem, h6ub⟩

theorem main : H1 → H2 →
    type_of% @KaplanskyUInvariant.u_invariant_values.variants.kaplansky_conjecture := by
  intro h1 h2 hkap
  obtain ⟨G, instF, trans, hsys, a, b, c, d, h20, hdiv, hiso⟩ := exists_tower_of_hyps h1 h2
  have h6 : IsUInvariant 6 := isUInvariant_six_of_tower G trans a b c d hdiv hiso
  obtain ⟨k, hk⟩ := hkap 6 h6
  rcases Nat.lt_or_ge k 3 with hklt | hkge
  · interval_cases k <;> omega
  · have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hkge
    omega

end OMA.R_KaplanskyUInvariant_u_invariant_values_variants_kaplansky_conjecture_R1
