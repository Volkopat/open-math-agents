import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H2_R1_H3_R2
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.GroupExtension.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.GroupTheory.Sylow
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Tactic.Abel
import Mathlib.RingTheory.Artinian.Algebra
import Mathlib.RingTheory.Jacobson.Semiprimary
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Module.ZMod
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Order.WellFounded
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring
import Mathlib.GroupTheory.Index
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Category.Grp.FiniteGrp
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.FieldTheory.Finiteness
import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Data.Set.Finite.Range
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finite.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-
The prescribed-Sylow bound follows by counting groups with marked Sylow
subgroups along elementary abelian chief factors. The coefficient E = 10
comes from charging each stage to the drop in the binary logarithm of the order.
The multiplication-table encoding and simple-summand dimension argument
are adapted from @wispiANt's work in PR #18023.
-/

open scoped BigOperators

namespace Erdos1160ChiefSeries

variable {G M : Type*} [Group G] [AddCommGroup M] [DistribMulAction G M]

private def d₁ (b : G → G → M) (x y z : G) : M := b y z - b x z + b x y

private def d₂ (c : G → G → G → M) (w x y z : G) : M :=
  c x y z - c w y z + c w x z - c w x y

private theorem extend_primitive (P : Subgroup G) (c : G → G → G → M)
    (equiv_c : ∀ g x y z, c (g*x) (g*y) (g*z) = g • c x y z)
    (closed : ∀ w x y z, d₂ c w x y z = 0)
    (b : P → P → M)
    (equiv_b : ∀ (g x y : P), b (g*x) (g*y) = (g : G) • b x y)
    (primitive : ∀ x y z : P, d₁ b x y z = c x y z) :
    ∃ B : G → G → M,
      (∀ (g : P) (x y : G), B (g*x) (g*y) = (g : G) • B x y) ∧
      (∀ x y z, d₁ B x y z = c x y z) := by
  classical
  let r (x : G) : P := ⟨x * (QuotientGroup.mk x⁻¹ : G ⧸ P).out, by
    have h := (QuotientGroup.out_eq' (QuotientGroup.mk x⁻¹ : G ⧸ P)).symm
    simpa only [inv_inv] using QuotientGroup.eq.mp h⟩
  have equiv_r (g : P) (x : G) : r ((g:G)*x) = g * r x := by
    apply Subtype.ext
    have hq : (QuotientGroup.mk ((g:G)*x)⁻¹ : G ⧸ P) = QuotientGroup.mk x⁻¹ := by
      apply QuotientGroup.eq.mpr
      simp [mul_assoc, g.property]
    change ((g : G)*x) * (QuotientGroup.mk ((g:G)*x)⁻¹ : G ⧸ P).out =
      (g : G) * (x * (QuotientGroup.mk x⁻¹ : G ⧸ P).out)
    rw [hq, mul_assoc]
  let B (x y : G) := b (r x) (r y) + c (r x) x y - c (r x) (r y) y
  refine ⟨B, ?_, ?_⟩
  · intro g x y
    simp only [B, equiv_r, equiv_b, Subgroup.coe_mul, equiv_c, smul_add, smul_sub]
  · intro x y z
    have h₁ := closed (r x) x y z
    have h₂ := closed (r x) (r y) y z
    have h₃ := closed (r x) (r y) (r z) z
    have h₄ := primitive (r x) (r y) (r z)
    unfold d₂ at h₁ h₂ h₃
    unfold d₁ at h₄ ⊢
    change B y z - B x z + B x y = _
    calc
      _ = (b (r y) (r z) - b (r x) (r z) + b (r x) (r y)) +
          (c x y z - c (r x) (r y) (r z)) -
          (c x y z - c (r x) y z + c (r x) x z - c (r x) x y) +
          (c (r y) y z - c (r x) y z + c (r x) (r y) z - c (r x) (r y) y) -
          (c (r y) (r z) z - c (r x) (r z) z + c (r x) (r y) z -
            c (r x) (r y) (r z)) := by dsimp [B]; abel
      _ = _ := by rw [h₁, h₂, h₃, h₄]; abel

private theorem average_primitive (P : Subgroup G) [Fintype (G ⧸ P)] (c : G → G → G → M)
    (equiv_c : ∀ g x y z, c (g*x) (g*y) (g*z) = g • c x y z)
    (b : G → G → M)
    (equiv_b : ∀ (g : P) (x y : G), b (g*x) (g*y) = (g : G) • b x y)
    (primitive : ∀ x y z, d₁ b x y z = c x y z) :
    ∃ B : G → G → M,
      (∀ (g x y : G), B (g*x) (g*y) = g • B x y) ∧
      (∀ x y z, d₁ B x y z = Fintype.card (G ⧸ P) • c x y z) := by
  classical
  let t (g x y : G) := g • b (g⁻¹*x) (g⁻¹*y)
  let f (q : G ⧸ P) (x y : G) := t q.out x y
  have ht (g h x y : G) : t (g*h) (g*x) (g*y) = g • t h x y := by
    simp [t, mul_smul, mul_assoc]
  have hf (g x y : G) : f (QuotientGroup.mk g) x y = t g x y := by
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (s := P) g
    change t (QuotientGroup.mk g : G ⧸ P).out x y = _
    rw [hh]
    simp only [t, mul_inv_rev, mul_assoc, mul_smul]
    exact congrArg (g • ·) (by
      have h' := equiv_b h⁻¹ (g⁻¹*x) (g⁻¹*y)
      change b ((h : G)⁻¹*(g⁻¹*x)) ((h : G)⁻¹*(g⁻¹*y)) =
        (h : G)⁻¹ • b (g⁻¹*x) (g⁻¹*y) at h'
      rw [h']
      simp)
  let B (x y : G) := ∑ q : G ⧸ P, f q x y
  refine ⟨B, ?_, ?_⟩
  · intro g x y
    have transport (q : G ⧸ P) : f (g • q) (g*x) (g*y) = g • f q x y := by
      induction q using Quotient.inductionOn' with
      | _ h =>
        change f (QuotientGroup.mk (g*h)) (g*x) (g*y) = g • f (QuotientGroup.mk h) x y
        rw [hf, hf, ht]
    calc
      B (g*x) (g*y) = ∑ q : G ⧸ P, f (g • q) (g*x) (g*y) :=
        (Equiv.sum_comp (MulAction.toPerm g : (G ⧸ P) ≃ (G ⧸ P))
          (fun q => f q (g*x) (g*y))).symm
      _ = g • B x y := by simp only [transport, B, Finset.smul_sum]
  · intro x y z
    unfold d₁
    change (∑ q : G ⧸ P, f q y z) - (∑ q : G ⧸ P, f q x z) +
      (∑ q : G ⧸ P, f q x y) = _
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    have local_eq (q : G ⧸ P) : f q y z - f q x z + f q x y = c x y z := by
      change t q.out y z - t q.out x z + t q.out x y = _
      simp only [t, ← smul_sub, ← smul_add]
      rw [← d₁, primitive, ← equiv_c]
      simp
    simp [local_eq]

theorem scaled_primitive_of_restriction (P : Subgroup G) [Fintype (G ⧸ P)]
    (c : G → G → G → M)
    (equiv_c : ∀ g x y z, c (g*x) (g*y) (g*z) = g • c x y z)
    (closed : ∀ w x y z, d₂ c w x y z = 0)
    (b : P → P → M)
    (equiv_b : ∀ (g x y : P), b (g*x) (g*y) = (g : G) • b x y)
    (primitive : ∀ x y z : P, d₁ b x y z = c x y z) :
    ∃ B : G → G → M,
      (∀ (g x y : G), B (g*x) (g*y) = g • B x y) ∧
      (∀ x y z, d₁ B x y z = Fintype.card (G ⧸ P) • c x y z) := by
  obtain ⟨B, equiv_B, primitive_B⟩ := extend_primitive P c equiv_c closed b equiv_b primitive
  exact average_primitive P c equiv_c B equiv_B primitive_B

/-- A homogeneous coboundary on a subgroup lifts when the index is invertible on the coefficients. -/
theorem primitive_of_restriction (P : Subgroup G) [Fintype (G ⧸ P)]
    (index_invertible : Function.Bijective (fun z : M => Fintype.card (G ⧸ P) • z))
    (c : G → G → G → M)
    (equiv_c : ∀ g x y z, c (g*x) (g*y) (g*z) = g • c x y z)
    (closed : ∀ w x y z, d₂ c w x y z = 0)
    (b : P → P → M)
    (equiv_b : ∀ (g x y : P), b (g*x) (g*y) = (g : G) • b x y)
    (primitive : ∀ x y z : P, d₁ b x y z = c x y z) :
    ∃ B : G → G → M,
      (∀ (g x y : G), B (g*x) (g*y) = g • B x y) ∧
      (∀ x y z, d₁ B x y z = c x y z) := by
  classical
  let n := Fintype.card (G ⧸ P)
  obtain ⟨B, equiv_B, primitive_B⟩ := scaled_primitive_of_restriction P c equiv_c closed b equiv_b primitive
  have preimage (x y : G) : ∃ m : M, n • m = B x y := index_invertible.2 (B x y)
  choose A hA using preimage
  refine ⟨A, ?_, ?_⟩
  · intro g x y
    apply index_invertible.1
    change n • A (g*x) (g*y) = n • (g • A x y)
    rw [hA, smul_comm n g, hA, equiv_B]
  · intro x y z
    apply index_invertible.1
    change n • (A y z - A x z + A x y) = n • c x y z
    rw [nsmul_add, nsmul_sub, hA, hA, hA]
    exact primitive_B x y z

/-- In degree two, a coboundary on a subgroup of invertible index is a global coboundary. -/
theorem two_cocycle_coboundary_of_restriction (P : Subgroup G) [Fintype (G ⧸ P)]
    (index_invertible : Function.Bijective (fun z : M => Fintype.card (G ⧸ P) • z))
    (c : G → G → M)
    (cocycle : ∀ x y z, x • c y z - c (x*y) z + c x (y*z) - c x y = 0)
    (b : P → M)
    (local_coboundary : ∀ x y : P, (x : G) • b y - b (x*y) + b x = c x y) :
    ∃ B : G → M, ∀ x y, x • B y - B (x*y) + B x = c x y := by
  let C (x y z : G) := x • c (x⁻¹*y) (y⁻¹*z)
  let bP (x y : P) := (x : G) • b (x⁻¹*y)
  have equiv_C (g x y z : G) : C (g*x) (g*y) (g*z) = g • C x y z := by
    simp [C, mul_assoc, mul_smul]
  have closed_C (w x y z : G) : d₂ C w x y z = 0 := by
    have h := congrArg (w • ·) (cocycle (w⁻¹*x) (x⁻¹*y) (y⁻¹*z))
    simpa [d₂, C, smul_sub, smul_add, ← mul_smul, mul_assoc] using h
  have equiv_bP (g x y : P) : bP (g*x) (g*y) = (g : G) • bP x y := by
    simp [bP, Subgroup.coe_mul, mul_assoc, mul_smul]
  have primitive_bP (x y z : P) : d₁ bP x y z = C x y z := by
    have h := congrArg ((x : G) • ·) (local_coboundary (x⁻¹*y) (y⁻¹*z))
    simpa [d₁, C, bP, Subgroup.coe_mul, smul_sub, smul_add, ← mul_smul, mul_assoc] using h
  obtain ⟨B, equiv_B, hB⟩ := primitive_of_restriction P index_invertible C equiv_C closed_C
    bP equiv_bP primitive_bP
  refine ⟨B 1, fun x y => ?_⟩
  have h := hB 1 x (x*y)
  have hxy : B x (x*y) = x • B 1 y := by simpa using equiv_B x 1 y
  simpa [d₁, C, hxy] using h

private theorem two_cocycles_equiv_of_restriction (P : Subgroup G) [Fintype (G ⧸ P)]
    (index_invertible : Function.Bijective (fun z : M => Fintype.card (G ⧸ P) • z))
    (c₁ c₂ : G → G → M)
    (closed₁ : ∀ x y z, x • c₁ y z - c₁ (x*y) z + c₁ x (y*z) - c₁ x y = 0)
    (closed₂ : ∀ x y z, x • c₂ y z - c₂ (x*y) z + c₂ x (y*z) - c₂ x y = 0)
    (b : P → M)
    (same : ∀ x y : P, (x : G) • b y - b (x*y) + b x = c₁ x y - c₂ x y) :
    ∃ B : G → M, ∀ x y, x • B y - B (x*y) + B x = c₁ x y - c₂ x y := by
  apply two_cocycle_coboundary_of_restriction P index_invertible (fun x y => c₁ x y - c₂ x y)
    _ b same
  intro x y z
  simp only [smul_sub]
  calc
    _ = (x • c₁ y z - c₁ (x*y) z + c₁ x (y*z) - c₁ x y) -
        (x • c₂ y z - c₂ (x*y) z + c₂ x (y*z) - c₂ x y) := by abel
    _ = 0 := by rw [closed₁, closed₂, sub_zero]

private theorem crossed_products_comparison {X Y : Type*} [Group X] [Group Y]
    (P : Subgroup G) [Fintype (G ⧸ P)]
    (index_invertible : Function.Bijective (fun z : M => Fintype.card (G ⧸ P) • z))
    (coordX : X ≃ M × G) (coordY : Y ≃ M × G)
    (c₁ c₂ : G → G → M)
    (closed₁ : ∀ x y z, x • c₁ y z - c₁ (x*y) z + c₁ x (y*z) - c₁ x y = 0)
    (closed₂ : ∀ x y z, x • c₂ y z - c₂ (x*y) z + c₂ x (y*z) - c₂ x y = 0)
    (mulX : ∀ x y,
      coordX (x*y) = let a := coordX x; let b := coordX y;
        (a.1 + a.2 • b.1 + c₁ a.2 b.2, a.2*b.2))
    (mulY : ∀ x y,
      coordY (x*y) = let a := coordY x; let b := coordY y;
        (a.1 + a.2 • b.1 + c₂ a.2 b.2, a.2*b.2))
    (b : P → M)
    (same : ∀ x y : P, (x : G) • b y - b (x*y) + b x = c₁ x y - c₂ x y) :
    ∃ e : X ≃* Y, ∃ B : G → M,
      (∀ g h, g • B h - B (g*h) + B g = c₁ g h - c₂ g h) ∧
      (∀ x, coordY (e x) = ((coordX x).1 + B (coordX x).2, (coordX x).2)) := by
  obtain ⟨B, hB⟩ := two_cocycles_equiv_of_restriction P index_invertible c₁ c₂ closed₁ closed₂ b same
  let shift : (M × G) ≃ (M × G) :=
    { toFun := fun x => (x.1 + B x.2, x.2)
      invFun := fun x => (x.1 - B x.2, x.2)
      left_inv := fun (a,g) => by simp
      right_inv := fun (a,g) => by simp }
  let e := coordX.trans (shift.trans coordY.symm)
  let eMul : X ≃* Y :=
    { toEquiv := e
      map_mul' := by
        intro x y
        apply coordY.injective
        change coordY (e (x*y)) = coordY (e x * e y)
        rw [mulY]
        simp only [e, Equiv.trans_apply, Equiv.apply_symm_apply, mulX, shift, Equiv.coe_fn_mk]
        congr 1
        rw [smul_add]
        have h := hB (coordX x).2 (coordX y).2
        have hc : c₁ (coordX x).2 (coordX y).2 =
            (coordX x).2 • B (coordX y).2 - B ((coordX x).2*(coordX y).2) +
              B (coordX x).2 + c₂ (coordX x).2 (coordX y).2 := by
          rw [h, sub_add_cancel]
        rw [hc]
        abel }
  exact ⟨eMul, B, hB, fun x => by simp [eMul, e, shift]⟩

section Extensions

variable {X : Type*} [Group X]
variable (S : GroupExtension (Multiplicative M) X G) (σ : S.Section)

private def normalForm (a : M × G) : X := S.inl (Multiplicative.ofAdd a.1) * σ a.2

omit [DistribMulAction G M] in
private theorem normalForm_bijective : Function.Bijective (normalForm S σ) := by
  constructor
  · rintro ⟨a,g⟩ ⟨b,h⟩ eq
    have eq' := congrArg S.rightHom eq
    have hg : g = h := by simpa [normalForm] using eq'
    subst h
    have ab : S.inl (Multiplicative.ofAdd a) = S.inl (Multiplicative.ofAdd b) :=
      mul_right_cancel eq
    exact Prod.ext (congrArg Multiplicative.toAdd (S.inl_injective ab)) rfl
  · intro x
    have mem : x * (σ (S.rightHom x))⁻¹ ∈ S.inl.range := by
      simp [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
    obtain ⟨a,ha⟩ := mem
    exact ⟨(a.toAdd, S.rightHom x), by simp [normalForm, ha]⟩

/-- The factor set of a section of a group extension with abelian kernel. -/
noncomputable def factorSet (g h : G) : M :=
  (Classical.choose (σ.mul_mul_mul_inv_mem_range_inl g h)).toAdd

omit [DistribMulAction G M] in
private theorem factorSet_spec (g h : G) :
    S.inl (Multiplicative.ofAdd (factorSet S σ g h)) * σ (g*h) = σ g * σ h := by
  have h₀ := Classical.choose_spec (σ.mul_mul_mul_inv_mem_range_inl g h)
  change S.inl (Multiplicative.ofAdd (factorSet S σ g h)) = _ at h₀
  simp [h₀]

private theorem normalForm_mul
    (action : ∀ g a, σ g * S.inl (Multiplicative.ofAdd a) =
      S.inl (Multiplicative.ofAdd (g • a)) * σ g)
    (a b : M) (g h : G) :
    normalForm S σ (a,g) * normalForm S σ (b,h) =
      normalForm S σ (a + g • b + factorSet S σ g h, g*h) := by
  change (S.inl (Multiplicative.ofAdd a) * σ g) *
    (S.inl (Multiplicative.ofAdd b) * σ h) = _
  calc
    _ = S.inl (Multiplicative.ofAdd a) * (σ g * S.inl (Multiplicative.ofAdd b)) * σ h := by
      simp [mul_assoc]
    _ = (S.inl (Multiplicative.ofAdd a) * S.inl (Multiplicative.ofAdd (g • b))) *
        (σ g * σ h) := by rw [action]; simp [mul_assoc]
    _ = _ := by
      rw [← factorSet_spec S σ]
      unfold normalForm
      rw [← mul_assoc (S.inl (Multiplicative.ofAdd a) *
        S.inl (Multiplicative.ofAdd (g • b))), ← map_mul, ← map_mul]
      rfl

private theorem factorSet_cocycle
    (action : ∀ g a, σ g * S.inl (Multiplicative.ofAdd a) =
      S.inl (Multiplicative.ofAdd (g • a)) * σ g) (x y z : G) :
    x • factorSet S σ y z - factorSet S σ (x*y) z +
      factorSet S σ x (y*z) - factorSet S σ x y = 0 := by
  have eq := mul_assoc (normalForm S σ (0,x)) (normalForm S σ (0,y)) (normalForm S σ (0,z))
  simp only [normalForm_mul S σ action, smul_zero, zero_add, add_zero] at eq
  have h := congrArg Prod.fst ((normalForm_bijective S σ).1 eq)
  calc
    _ = (x • factorSet S σ y z + factorSet S σ x (y*z)) -
        (factorSet S σ x y + factorSet S σ (x*y) z) := by abel
    _ = 0 := sub_eq_zero.mpr h.symm

private theorem coord_mul
    (action : ∀ g a, σ g * S.inl (Multiplicative.ofAdd a) =
      S.inl (Multiplicative.ofAdd (g • a)) * σ g)
    (x y : X) :
    let coord := (Equiv.ofBijective (normalForm S σ) (normalForm_bijective S σ)).symm
    coord (x*y) = let a := coord x; let b := coord y;
      (a.1 + a.2 • b.1 + factorSet S σ a.2 b.2, a.2*b.2) := by
  let e := Equiv.ofBijective (normalForm S σ) (normalForm_bijective S σ)
  change e.symm (x*y) = _
  apply e.injective
  rw [Equiv.apply_symm_apply]
  change x*y = normalForm S σ _
  rw [← normalForm_mul S σ action]
  exact congrArg₂ (· * ·) (e.apply_symm_apply x).symm (e.apply_symm_apply y).symm

omit [DistribMulAction G M] in
private theorem coord_rightHom (x : X) :
    (((Equiv.ofBijective (normalForm S σ) (normalForm_bijective S σ)).symm x).2) = S.rightHom x := by
  let e := Equiv.ofBijective (normalForm S σ) (normalForm_bijective S σ)
  have h := congrArg S.rightHom (e.apply_symm_apply x)
  change S.rightHom (normalForm S σ (e.symm x)) = S.rightHom x at h
  simpa [normalForm] using h

omit [DistribMulAction G M] in
private theorem coord_inl (a : Multiplicative M) :
    (Equiv.ofBijective (normalForm S σ) (normalForm_bijective S σ)).symm (S.inl a) =
    (a.toAdd - factorSet S σ 1 1, (1:G)) := by
  let e := Equiv.ofBijective (normalForm S σ) (normalForm_bijective S σ)
  change e.symm (S.inl a) = _
  apply e.injective
  rw [Equiv.apply_symm_apply]
  have h : S.inl (Multiplicative.ofAdd (factorSet S σ 1 1)) = σ 1 := by
    apply mul_right_cancel (b := σ 1)
    simpa using factorSet_spec S σ 1 1
  change _ = S.inl (Multiplicative.ofAdd (a.toAdd - factorSet S σ 1 1)) * σ 1
  rw [← h, ← map_mul, ← ofAdd_add, sub_add_cancel]
  rfl

/-- With a common action, group extensions are isomorphic when the selected
    factor sets differ by a coboundary on a subgroup of invertible index. -/
theorem extensions_equiv_of_restriction {Y : Type*} [Group Y]
    (T : GroupExtension (Multiplicative M) Y G) (τ : T.Section)
    (P : Subgroup G) [Fintype (G ⧸ P)]
    (index_invertible : Function.Bijective (fun z : M => Fintype.card (G ⧸ P) • z))
    (actionS : ∀ g a, σ g * S.inl (Multiplicative.ofAdd a) =
      S.inl (Multiplicative.ofAdd (g • a)) * σ g)
    (actionT : ∀ g a, τ g * T.inl (Multiplicative.ofAdd a) =
      T.inl (Multiplicative.ofAdd (g • a)) * τ g)
    (b : P → M)
    (same : ∀ g h : P, (g : G) • b h - b (g*h) + b g =
      factorSet S σ g h - factorSet T τ g h) : Nonempty (S.Equiv T) := by
  let xCoord := (Equiv.ofBijective (normalForm S σ) (normalForm_bijective S σ)).symm
  let yCoord := (Equiv.ofBijective (normalForm T τ) (normalForm_bijective T τ)).symm
  obtain ⟨e, B, hB, coord⟩ := crossed_products_comparison P index_invertible xCoord yCoord
    (factorSet S σ) (factorSet T τ) (factorSet_cocycle S σ actionS) (factorSet_cocycle T τ actionT)
    (coord_mul S σ actionS) (coord_mul T τ actionT) b same
  refine ⟨{ __ := e, inl_comm := ?_, rightHom_comm := ?_ }⟩
  · funext a
    change e (S.inl a) = T.inl a
    apply yCoord.injective
    rw [coord, coord_inl S σ a, coord_inl T τ a]
    have atOne : B 1 = factorSet S σ 1 1 - factorSet T τ 1 1 := by
      simpa using hB 1 1
    simp only [atOne]
    congr 1
    abel
  · funext x
    change T.rightHom (e x) = S.rightHom x
    rw [← coord_rightHom T τ (e x), ← coord_rightHom S σ x, coord]

/-- For a common action on an abelian kernel, a compatible local map determines
    the global extension up to an equivalence preserving the kernel and quotient. -/
theorem extensions_equiv_of_local_map {Y : Type*} [Group Y]
    (T : GroupExtension (Multiplicative M) Y G) (τ : T.Section)
    (P : Subgroup G) [Fintype (G ⧸ P)]
    (index_invertible : Function.Bijective (fun z : M => Fintype.card (G ⧸ P) • z))
    (actionS : ∀ g a, σ g * S.inl (Multiplicative.ofAdd a) =
      S.inl (Multiplicative.ofAdd (g • a)) * σ g)
    (actionT : ∀ g a, τ g * T.inl (Multiplicative.ofAdd a) =
      T.inl (Multiplicative.ofAdd (g • a)) * τ g)
    (f : P.comap S.rightHom →* Y)
    (f_inl : ∀ a : Multiplicative M, f ⟨S.inl a, by
      change S.rightHom (S.inl a) ∈ P
      rw [S.rightHom_inl]
      exact P.one_mem⟩ = T.inl a)
    (f_proj : ∀ x, T.rightHom (f x) = S.rightHom x) : Nonempty (S.Equiv T) := by
  let s (g : P) : P.comap S.rightHom := ⟨σ g, by
    change S.rightHom (σ g) ∈ P
    rw [σ.rightHom_section]
    exact g.property⟩
  have eqInl (g : P) : ∃ a : Multiplicative M, T.inl a * τ g = f (s g) := by
    have hz : f (s g) * (τ g)⁻¹ ∈ T.inl.range := by
      simp [T.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, f_proj, s]
    obtain ⟨a,ha⟩ := hz
    exact ⟨a, by simp [ha]⟩
  choose d hd using eqInl
  let b (g : P) := (d g).toAdd
  have hb (g : P) : normalForm T τ (b g, (g:G)) = f (s g) := hd g
  apply extensions_equiv_of_restriction S σ T τ P index_invertible actionS actionT b
  intro g h
  let kern (a : Multiplicative M) : P.comap S.rightHom := ⟨S.inl a, by
    change S.rightHom (S.inl a) ∈ P
    rw [S.rightHom_inl]
    exact P.one_mem⟩
  have law : kern (Multiplicative.ofAdd (factorSet S σ g h)) * s (g*h) = s g * s h := by
    apply Subtype.ext
    exact factorSet_spec S σ g h
  have law' := congrArg f law
  rw [map_mul, map_mul] at law'
  change f _ * f (s (g*h)) = f (s g) * f (s h) at law'
  rw [show f (kern (Multiplicative.ofAdd (factorSet S σ g h))) = _ from f_inl _,
    ← hb, ← hb, ← hb, normalForm_mul T τ actionT] at law'
  have same : normalForm T τ (factorSet S σ g h + b (g*h), (g:G)*(h:G)) =
      normalForm T τ (b g + (g:G) • b h + factorSet T τ g h, (g:G)*(h:G)) := by
    unfold normalForm
    rw [show Multiplicative.ofAdd (factorSet S σ g h + b (g*h)) =
      Multiplicative.ofAdd (factorSet S σ g h) * Multiplicative.ofAdd (b (g*h)) from rfl,
      map_mul, mul_assoc]
    exact law'
  have he := congrArg Prod.fst ((normalForm_bijective T τ).1 same)
  change factorSet S σ g h + b (g*h) = b g + (g:G) • b h + factorSet T τ g h at he
  calc
    _ = (b g + (g:G) • b h + factorSet T τ g h) - b (g*h) - factorSet T τ g h := by abel
    _ = _ := by rw [← he]; abel

end Extensions

/-- The finite-group averaging argument for crossed homomorphisms. -/
theorem crossed_hom_principal [Fintype G]
    (index_invertible : Function.Bijective (fun z : M => Fintype.card G • z))
    (b : G → M) (crossed : ∀ x y, b (x*y) = b x + x • b y) :
    ∃ a : M, ∀ x, b x = a - x • a := by
  classical
  let S : M := ∑ x : G, b x
  obtain ⟨a, ha⟩ := index_invertible.2 S
  change Fintype.card G • a = S at ha
  refine ⟨a, ?_⟩
  intro x
  have h : Fintype.card G • b x + x • S = S := by
    calc
      _ = ∑ y : G, (b x + x • b y) := by simp [S, Finset.sum_add_distrib, Finset.smul_sum]
      _ = ∑ y : G, b (x*y) := by simp only [crossed]
      _ = S := Equiv.sum_comp (Equiv.mulLeft x) b
  apply index_invertible.1
  change Fintype.card G • b x = Fintype.card G • (a - x • a)
  rw [nsmul_sub, smul_comm (Fintype.card G) x, ha]
  exact eq_sub_of_add_eq h

/-- With the quotient map and a subgroup restriction fixed, each of the
    remaining generators contributes at most one kernel element of choice. -/
theorem marked_lifts_card_le {N X Q U : Type*} [Group N] [Group X] [Group Q] [Group U]
    [Finite N] (S : GroupExtension N X Q) (K : Subgroup U) (mark : K →* X) (proj : U →* Q)
    {d : ℕ} (v : Fin d → U) (generate : Subgroup.closure ((K : Set U) ∪ Set.range v) = ⊤) :
    Nat.card {f : U →* X // (∀ k : K, f k = mark k) ∧ ∀ u, S.rightHom (f u) = proj u} ≤
      Nat.card N ^ d := by
  classical
  let T := {f : U →* X // (∀ k : K, f k = mark k) ∧ ∀ u, S.rightHom (f u) = proj u}
  change Nat.card T ≤ _
  by_cases nonempty : Nonempty T
  · let base := Classical.choice nonempty
    have witness (f : T) (i : Fin d) : ∃ a : N, S.inl a = f.val (v i) * (base.val (v i))⁻¹ := by
      change f.val (v i) * (base.val (v i))⁻¹ ∈ S.inl.range
      rw [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv,
        f.property.2, base.property.2, mul_inv_cancel]
    choose encode hencode using witness
    have injective : Function.Injective encode := by
      intro f g h
      apply Subtype.ext
      apply MonoidHom.eq_of_eqOn_dense generate
      rintro u (hk | ⟨i, rfl⟩)
      · exact (f.property.1 ⟨u,hk⟩).trans (g.property.1 ⟨u,hk⟩).symm
      · apply mul_right_cancel (b := (base.val (v i))⁻¹)
        rw [← hencode f i, ← hencode g i, h]
    simpa only [Nat.card_fun, Nat.card_fin] using Nat.card_le_card_of_injective encode injective
  · have h : IsEmpty T := ⟨fun x => nonempty ⟨x⟩⟩
    rw [Nat.card_eq_zero.mpr (.inl h)]
    exact Nat.zero_le _

omit [DistribMulAction G M] in
/-- The index of a Sylow subgroup acts invertibly on coefficients over the prime field. -/
theorem sylow_index_invertible {p : ℕ} [Fact p.Prime] [Module (ZMod p) M]
    (P : Sylow p G) [Fintype (G ⧸ (P : Subgroup G))] [(P : Subgroup G).FiniteIndex] :
    Function.Bijective (fun z : M => Fintype.card (G ⧸ (P : Subgroup G)) • z) := by
  have hdvd : ¬ p ∣ Fintype.card (G ⧸ (P : Subgroup G)) := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
    exact P.not_dvd_index
  have hn : (Fintype.card (G ⧸ (P : Subgroup G)) : ZMod p) ≠ 0 :=
    fun h => hdvd ((ZMod.natCast_eq_zero_iff _ _).mp h)
  have hu := (isUnit_iff_ne_zero.mpr hn).smul_bijective (β := M)
  simpa only [Nat.cast_smul_eq_nsmul] using hu

end Erdos1160ChiefSeries

namespace Erdos1160ChiefSeries

/-- At most `finrank F U` simple summands of a semisimple finite-dimensional module
are needed to represent all its simple quotients. -/
private theorem quotient_catalogue (F A U : Type*) [Field F] [Ring A] [Algebra F A]
    [AddCommGroup U] [Module A U] [Module F U] [IsScalarTower F A U]
    [Module.Finite F U] [IsSemisimpleModule A U] :
    ∃ C : Finset (Submodule A U), C.card ≤ Module.finrank F U ∧
      ∀ (V : Type) [AddCommGroup V] [Module A V] [IsSimpleModule A V] (f : U →ₗ[A] V),
        f ≠ 0 → ∃ I ∈ C, Nonempty (I ≃ₗ[A] V) := by
  classical
  obtain ⟨S, independent, top, simple⟩ := IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top A U
  have nonzero (I : S) : ∃ v : U, v ∈ I.val ∧ v ≠ 0 := by
    let _ := simple I.val I.property
    let _ := IsSimpleModule.nontrivial A I.val
    obtain ⟨v,hv⟩ := exists_ne (0 : I.val)
    exact ⟨v, v.property, fun h => hv (Subtype.ext h)⟩
  choose v hv hn using nonzero
  have indepF : iSupIndep (fun I : S => I.val.restrictScalars F) := by
    apply iSupIndep_def.mpr
    intro I
    simpa only [← Submodule.restrictScalars_iSup, Submodule.disjoint_restrictScalars_iff] using
      (iSupIndep_def.mp ((sSupIndep_iff S).mp independent) I)
  have lin := indepF.linearIndependent _ hv hn
  let _ : Finite S := lin.finite
  let finite : S.Finite := Set.toFinite _
  let _ := finite.fintype
  refine ⟨finite.toFinset, ?_, ?_⟩
  · simpa using lin.fintype_card_le_finrank
  · intro V _ _ _ f hf
    have nz : ∃ I ∈ S, f.comp I.subtype ≠ 0 := by
      by_contra! hz
      apply hf
      have le : sSup S ≤ LinearMap.ker f := by
        apply sSup_le
        intro I hI x hx
        have e := LinearMap.congr_fun (hz I hI) ⟨x,hx⟩
        exact e
      rw [top] at le
      exact LinearMap.ker_eq_top.mp (top_le_iff.mp le)
    obtain ⟨I,hI,hi⟩ := nz
    let _ := simple I hI
    exact ⟨I, finite.mem_toFinset.mpr hI, ⟨LinearEquiv.ofBijective _ (LinearMap.bijective_of_ne_zero hi)⟩⟩

/-- All simple modules over a finite-dimensional algebra occur in the semisimple top
of its regular module. This works even when the characteristic divides the group order. -/
theorem finite_algebra_simple_catalogue (F A : Type) [Field F] [Ring A] [Algebra F A]
    [Module.Finite F A] :
    ∃ C : Finset (Submodule A (A ⧸ Module.jacobson A A)), C.card ≤ Module.finrank F A ∧
      ∀ (V : Type) [AddCommGroup V] [Module A V] [IsSimpleModule A V],
        ∃ I ∈ C, Nonempty (I ≃ₗ[A] V) := by
  classical
  let J := Module.jacobson A A
  let _ : IsArtinian A A := isArtinian_of_tower F inferInstance
  let _ : IsSemisimpleModule A (A ⧸ J) :=
    (IsArtinian.isSemisimpleModule_iff_jacobson (R := A) (M := A ⧸ J)).mpr
      (Module.jacobson_quotient_jacobson A A)
  obtain ⟨C, size, cover⟩ := quotient_catalogue F A (A ⧸ J)
  refine ⟨C, size.trans ?_, ?_⟩
  · exact LinearMap.finrank_le_finrank_of_surjective (f := J.mkQ.restrictScalars F)
      (Submodule.Quotient.mk_surjective J)
  · intro V _ _ _
    let _ := IsSimpleModule.nontrivial A V
    obtain ⟨v,hv⟩ := exists_ne (0 : V)
    let f : A →ₗ[A] V := LinearMap.toSpanSingleton A V v
    have hJ : J ≤ LinearMap.ker f := IsSemisimpleModule.jacobson_le_ker A A A V f
    let b := J.liftQ f hJ
    have hb : b ≠ 0 := by
      intro h
      apply hv
      have e := LinearMap.congr_fun h (J.mkQ 1)
      change (J.liftQ f hJ) (Submodule.Quotient.mk (1:A)) = 0 at e
      rw [Submodule.liftQ_apply] at e
      change LinearMap.toSpanSingleton A V v 1 = 0 at e
      rwa [LinearMap.toSpanSingleton_apply_one] at e
    exact cover V b hb

/-- Simple group-algebra modules admit a catalogue of size at most the group order. -/
theorem group_algebra_simple_catalogue (F Q : Type) [Field F] [Group Q] [Finite Q] :
    ∃ C : Finset (Submodule (MonoidAlgebra F Q)
        (MonoidAlgebra F Q ⧸ Module.jacobson (MonoidAlgebra F Q) (MonoidAlgebra F Q))),
      C.card ≤ Nat.card Q ∧
      ∀ (V : Type) [AddCommGroup V] [Module (MonoidAlgebra F Q) V]
        [IsSimpleModule (MonoidAlgebra F Q) V], ∃ I ∈ C, Nonempty (I ≃ₗ[MonoidAlgebra F Q] V) := by
  classical
  let _ := Fintype.ofFinite Q
  let basis := MonoidAlgebra.basis Q F
  let _ : Module.Finite F (MonoidAlgebra F Q) := Module.Finite.of_basis basis
  obtain ⟨C,size,cover⟩ := finite_algebra_simple_catalogue F (MonoidAlgebra F Q)
  exact ⟨C, by simpa [Module.finrank_eq_card_basis basis, Nat.card_eq_fintype_card] using size, cover⟩

private noncomputable def comparisonLinearEquiv {F Q V : Type} [Field F] [Group Q]
    [AddCommGroup V] [Module F V] {ρ σ : Representation F Q V}
    (e : ρ.asModule ≃ₗ[MonoidAlgebra F Q] σ.asModule) : V ≃ₗ[F] V :=
  ρ.asModuleEquiv.symm.trans ((e.restrictScalars F).trans σ.asModuleEquiv)

private theorem comparisonLinearEquiv_intertwines {F Q V : Type} [Field F] [Group Q]
    [AddCommGroup V] [Module F V] {ρ σ : Representation F Q V}
    (e : ρ.asModule ≃ₗ[MonoidAlgebra F Q] σ.asModule) (g : Q) (x : V) :
    comparisonLinearEquiv e (ρ g x) = σ g (comparisonLinearEquiv e x) := by
  apply σ.asModuleEquiv.symm.injective
  change σ.asModuleEquiv.symm (σ.asModuleEquiv (e (ρ.asModuleEquiv.symm (ρ g x)))) = _
  rw [LinearEquiv.symm_apply_apply, ρ.asModuleEquiv_symm_map_rho,
    σ.asModuleEquiv_symm_map_rho, LinearEquiv.map_smul]
  simp [comparisonLinearEquiv]
  rfl

private theorem linear_aut_card_bound (F V : Type) [Field F] [AddCommGroup V] [Module F V]
    [Module.Finite F V] [Finite V] : Nat.card (V ≃ₗ[F] V) ≤ Nat.card V ^ Module.finrank F V := by
  classical
  let b := Module.finBasis F V
  let code (e : V ≃ₗ[F] V) (i : Fin (Module.finrank F V)) : V := e (b i)
  have inj : Function.Injective code := by
    intro e f h
    apply LinearEquiv.toLinearMap_injective
    apply b.ext
    intro i
    exact congrFun h i
  simpa only [Nat.card_fun, Nat.card_fin] using Nat.card_le_card_of_injective code inj

/-- Count exact irreducible actions on a specified finite vector space. No coprimality
assumption on the order of the acting group is needed. -/
theorem irreducible_actions_card_bound (F Q V : Type) [Field F] [Group Q] [Finite Q]
    [AddCommGroup V] [Module F V] [Finite V] [Module.Finite F V] :
    Nat.card {ρ : Representation F Q V // IsSimpleModule (MonoidAlgebra F Q) ρ.asModule} ≤
      Nat.card Q * Nat.card V ^ Module.finrank F V := by
  classical
  let A := MonoidAlgebra F Q
  let I := {ρ : Representation F Q V // IsSimpleModule A ρ.asModule}
  change Nat.card I ≤ _
  by_cases nonempty : Nonempty I
  · let defaultAction := Classical.choice nonempty
    obtain ⟨C, size, cover⟩ := group_algebra_simple_catalogue F Q
    have catalogue (i : I) : ∃ L ∈ C, Nonempty (L ≃ₗ[A] i.val.asModule) := by
      let _ := i.property
      exact cover i.val.asModule
    choose label mem iso using catalogue
    let codeClass (i : I) : C := ⟨label i, mem i⟩
    let rep (c : C) : I := if h : ∃ i, codeClass i = c then h.choose else defaultAction
    have rep_class (i : I) : codeClass (rep (codeClass i)) = codeClass i := by
      have h : ∃ j, codeClass j = codeClass i := ⟨i,rfl⟩
      simpa only [rep, dif_pos h] using h.choose_spec
    have same (i : I) : Nonempty ((rep (codeClass i)).val.asModule ≃ₗ[A] i.val.asModule) := by
      have eq : label (rep (codeClass i)) = label i := congrArg Subtype.val (rep_class i)
      have h : Nonempty (label (rep (codeClass i)) ≃ₗ[A] i.val.asModule) := eq.symm ▸ iso i
      exact ⟨(iso (rep (codeClass i))).some.symm.trans h.some⟩
    let enc (i : I) : C × (V ≃ₗ[F] V) := ⟨codeClass i, comparisonLinearEquiv (same i).some⟩
    have compat (i : I) (g : Q) (x : V) :
        (enc i).2 ((rep (enc i).1).val g x) = i.val g ((enc i).2 x) :=
      comparisonLinearEquiv_intertwines (same i).some g x
    have inj : Function.Injective enc := by
      intro i j eq
      apply Subtype.ext
      ext g x
      obtain ⟨y,rfl⟩ := (enc j).2.surjective x
      have h := compat i g y
      rw [eq] at h
      exact h.symm.trans (compat j g y)
    let _ : Finite (V ≃ₗ[F] V) := Finite.of_injective
      (fun e : V ≃ₗ[F] V => (e : V → V)) DFunLike.coe_injective
    calc
      _ ≤ Nat.card (C × (V ≃ₗ[F] V)) := Nat.card_le_card_of_injective enc inj
      _ = C.card * Nat.card (V ≃ₗ[F] V) := by
        rw [Nat.card_prod, Nat.card_eq_fintype_card (α := ↥C), Fintype.card_coe]
      _ ≤ _ := Nat.mul_le_mul size (linear_aut_card_bound F V)
  · have h : IsEmpty I := ⟨fun x => nonempty ⟨x⟩⟩
    rw [Nat.card_eq_zero.mpr (.inl h)]
    exact Nat.zero_le _

end Erdos1160ChiefSeries

namespace Erdos1160ChiefSeries

variable {M G Q : Type} [AddCommGroup M] [Group G] [Group Q]

private theorem conjugation_ker (S : GroupExtension (Multiplicative M) G Q) :
    S.rightHom.ker ≤ S.conjAct.ker := by
  intro x hx
  rw [← S.range_inl_eq_ker_rightHom] at hx
  obtain ⟨a,rfl⟩ := hx
  apply MonoidHom.mem_ker.mpr
  apply MulEquiv.ext
  intro b
  change S.conjAct (S.inl a) b = b
  apply S.inl_injective
  rw [S.inl_conjAct_comm]
  rw [← map_mul, ← map_inv, ← map_mul, mul_comm a b, mul_assoc, mul_inv_cancel, mul_one]

/-- Conjugation on an abelian kernel factors through the quotient. -/
noncomputable def quotientConjugation (S : GroupExtension (Multiplicative M) G Q) :
    Q →* MulAut (Multiplicative M) :=
  S.rightHom.liftOfSurjective S.rightHom_surjective ⟨S.conjAct, conjugation_ker S⟩

@[simp] theorem quotientConjugation_projection (S : GroupExtension (Multiplicative M) G Q) (x : G) :
    quotientConjugation S (S.rightHom x) = S.conjAct x := by
  unfold quotientConjugation
  rw [MonoidHom.liftOfRightInverse_comp_apply]

private def addMap (f : MulAut (Multiplicative M)) : M →+ M where
  toFun x := (f (Multiplicative.ofAdd x)).toAdd
  map_zero' := congrArg Multiplicative.toAdd (map_one f)
  map_add' x y := congrArg Multiplicative.toAdd (map_mul f (Multiplicative.ofAdd x) (Multiplicative.ofAdd y))

variable {p : ℕ} [Module (ZMod p) M]

/-- The representation of the quotient on an elementary abelian kernel. -/
noncomputable def kernelRepresentation (S : GroupExtension (Multiplicative M) G Q) :
    Representation (ZMod p) Q M where
  toFun q := (addMap (quotientConjugation S q)).toZModLinearMap p
  map_one' := by rw [map_one]; ext x; rfl
  map_mul' x y := by rw [map_mul]; ext a; rfl

@[simp] theorem kernelRepresentation_projection (S : GroupExtension (Multiplicative M) G Q)
    (x : G) (a : Multiplicative M) :
    (kernelRepresentation (p := p) S) (S.rightHom x) a.toAdd = (S.conjAct x a).toAdd := by
  change (quotientConjugation S (S.rightHom x) a).toAdd = _
  rw [quotientConjugation_projection]

/-- The associated action is exactly conjugation by a lift of the quotient element. -/
theorem kernelRepresentation_section (S : GroupExtension (Multiplicative M) G Q) (σ : S.Section)
    (q : Q) (a : M) :
    σ q * S.inl (Multiplicative.ofAdd a) =
      S.inl (Multiplicative.ofAdd (kernelRepresentation (p := p) S q a)) * σ q := by
  have eq := kernelRepresentation_projection (p := p) S (σ q) (Multiplicative.ofAdd a)
  rw [σ.rightHom_section] at eq
  change (kernelRepresentation (p := p) S) q a = _ at eq
  rw [eq]
  change σ q * S.inl (Multiplicative.ofAdd a) =
    S.inl (S.conjAct (σ q) (Multiplicative.ofAdd a)) * σ q
  rw [S.inl_conjAct_comm, inv_mul_cancel_right]

/-- The action on a minimal nontrivial normal elementary abelian kernel is simple. -/
theorem kernelRepresentation_simple (S : GroupExtension (Multiplicative M) G Q) [Nontrivial M]
    (minimal : ∀ N : Subgroup G, N.Normal → N ≤ S.inl.range → N = ⊥ ∨ N = S.inl.range) :
    IsSimpleModule (MonoidAlgebra (ZMod p) Q) (kernelRepresentation (p := p) S).asModule := by
  let ρ := kernelRepresentation (p := p) S
  let A := MonoidAlgebra (ZMod p) Q
  apply (isSimpleModule_iff A ρ.asModule).mpr
  have nt : Nontrivial ρ.asModule := ρ.asModuleEquiv.symm.injective.nontrivial
  let _ := nt
  refine { eq_bot_or_eq_top := ?_ }
  intro W
  let K : Subgroup (Multiplicative M) :=
    { carrier := {a | ρ.asModuleEquiv.symm a.toAdd ∈ W}
      one_mem' := by change ρ.asModuleEquiv.symm 0 ∈ W; simp
      mul_mem' := fun {a b} ha hb => by
        change ρ.asModuleEquiv.symm (a.toAdd+b.toAdd) ∈ W
        rw [map_add]
        exact W.add_mem ha hb
      inv_mem' := fun {a} ha => by
        change ρ.asModuleEquiv.symm (-a.toAdd) ∈ W
        rw [map_neg]
        exact W.neg_mem ha }
  let B := K.map S.inl
  have norms : B.Normal := by
    constructor
    intro x hx g
    obtain ⟨a,ha,rfl⟩ := hx
    refine ⟨S.conjAct g a, ?_, S.inl_conjAct_comm⟩
    change ρ.asModuleEquiv.symm ((S.conjAct g a).toAdd) ∈ W
    rw [← kernelRepresentation_projection (p := p) S g a]
    change ρ.asModuleEquiv.symm (ρ (S.rightHom g) a.toAdd) ∈ W
    rw [ρ.asModuleEquiv_symm_map_rho]
    exact W.smul_mem _ ha
  have incl : B ≤ S.inl.range := by rintro _ ⟨a, _, rfl⟩; exact ⟨a,rfl⟩
  obtain zero | full := minimal B norms incl
  · left
    apply le_antisymm ?_ bot_le
    intro v hv
    let a := Multiplicative.ofAdd (ρ.asModuleEquiv v)
    have ha : a ∈ K := by change ρ.asModuleEquiv.symm (ρ.asModuleEquiv v) ∈ W; simpa using hv
    have h := Subgroup.mem_map_of_mem S.inl ha
    change S.inl a ∈ B at h
    rw [zero, Subgroup.mem_bot, ← S.inl.map_one] at h
    have ha1 : a = 1 := S.inl_injective h
    rw [Submodule.mem_bot]
    apply ρ.asModuleEquiv.injective
    simpa [a] using congrArg Multiplicative.toAdd ha1
  · right
    apply le_antisymm le_top ?_
    intro v _
    let a := Multiplicative.ofAdd (ρ.asModuleEquiv v)
    have h : S.inl a ∈ B := full.symm ▸ (show S.inl a ∈ S.inl.range from ⟨a,rfl⟩)
    obtain ⟨a',ha',eq⟩ := h
    have eq' : a' = a := S.inl_injective eq
    rw [eq'] at ha'
    change ρ.asModuleEquiv.symm (ρ.asModuleEquiv v) ∈ W at ha'
    simpa using ha'

end Erdos1160ChiefSeries

open scoped BigOperators

namespace Erdos1160ChiefSeries

/-- In a fixed extension class, transport all markings to one representative.
The product of the cardinalities of the spaces of possible markings bounds the fiber. -/
theorem marked_extension_fiber_bound {A Q ι J : Type*} [Group A] [Group Q]
    [Fintype J] (E : ι → Type*) (P : J → Type*)
    [∀ i, Group (E i)] [∀ i, Finite (E i)] [∀ j, Group (P j)] [∀ j, Finite (P j)]
    (S : ∀ i, GroupExtension A (E i) Q)
    (mark : ∀ i j, P j →* E i)
    (admissible : ∀ i j, (P j →* E i) → Prop)
    (same_extension : ∀ a b, Nonempty ((S a).Equiv (S b)))
    (transport : ∀ a b (e : (S a).Equiv (S b)) j,
      admissible b j (e.toMulEquiv.toMonoidHom.comp (mark a j)))
    (distinct : ∀ a b (e : (S a).Equiv (S b)),
      (∀ j x, e (mark a j x) = mark b j x) → a = b)
    (capacity : J → ℕ)
    (bounds : ∀ i j, Nat.card {f : P j →* E i // admissible i j f} ≤ capacity j) :
    Finite ι ∧ Nat.card ι ≤ ∏ j, capacity j := by
  classical
  by_cases nonempty : Nonempty ι
  · let b := Classical.choice nonempty
    let e (a : ι) := Classical.choice (same_extension a b)
    let L (j : J) := {f : P j →* E b // admissible b j f}
    let (j : J) : Finite (P j →* E b) :=
      Finite.of_injective (fun f : P j →* E b => (f : P j → E b)) DFunLike.coe_injective
    let encode (a : ι) (j : J) : L j :=
      ⟨(e a).toMulEquiv.toMonoidHom.comp (mark a j), transport a b (e a) j⟩
    have injective : Function.Injective encode := by
      intro u v h
      apply distinct u v ((e u).trans (e v).symm)
      intro j x
      have eq := congrArg (fun z : (j : J) → L j => (z j).val x) h
      change (e u) (mark u j x) = (e v) (mark v j x) at eq
      change ((e v).toMulEquiv.symm) ((e u) (mark u j x)) = mark v j x
      rw [eq]
      exact (e v).toMulEquiv.symm_apply_apply (mark v j x)
    refine ⟨Finite.of_injective encode injective, (Nat.card_le_card_of_injective encode injective).trans ?_⟩
    rw [Nat.card_pi]
    exact Finset.prod_le_prod' (fun j _ => bounds b j)
  · have empty : IsEmpty ι := ⟨fun x => nonempty ⟨x⟩⟩
    let _ : IsEmpty ι := empty
    exact ⟨inferInstance, by rw [Nat.card_eq_zero.mpr (.inl empty)]; exact Nat.zero_le _⟩

end Erdos1160ChiefSeries

namespace Erdos1160ChiefSeries

/-- A finite nontrivial solvable group has a minimal nontrivial normal
subgroup that is elementary abelian. -/
theorem exists_elementary_chief_kernel (G : Type*) [Group G] [Finite G] [Nontrivial G]
    [Group.IsSolvable G] :
    ∃ A : Subgroup G, A.Normal ∧ A ≠ ⊥ ∧
      (∀ B : Subgroup G, B.Normal → B ≤ A → B = ⊥ ∨ B = A) ∧
      IsMulCommutative A ∧ ∃ p : ℕ, p.Prime ∧ ∀ x : A, x^p = 1 := by
  classical
  let S := {A : Subgroup G | A.Normal ∧ A ≠ ⊥}
  let _ : Finite (Subgroup G) :=
    Finite.of_injective (fun A : Subgroup G => (A : Set G)) SetLike.coe_injective
  have wf : WellFounded ((· < ·) : Subgroup G → Subgroup G → Prop) :=
    Finite.wellFounded_of_trans_of_irrefl _
  obtain ⟨A, hA, hmin⟩ := wf.has_min S ⟨⊤, inferInstance, top_ne_bot⟩
  have norm : A.Normal := hA.1
  let _ : A.Normal := norm
  have nontriv : A ≠ ⊥ := hA.2
  let _ : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr nontriv
  have minimal (B : Subgroup G) (hB : B.Normal) (le : B ≤ A) : B = ⊥ ∨ B = A := by
    by_cases hb : B = ⊥
    · exact .inl hb
    · right
      by_contra neq
      exact hmin B ⟨hB,hb⟩ (lt_of_le_of_ne le neq)
  have comm : IsMulCommutative A := by
    have lt := Group.IsSolvable.commutator_lt_of_ne_bot nontriv
    obtain eq | eq := minimal ⁅A,A⁆ inferInstance lt.le
    · exact Subgroup.commutator_self_eq_bot_iff.mp eq
    · exact False.elim (lt.ne eq)
  let _ : CommGroup A := { (inferInstance : Group A) with mul_comm := comm.is_comm.comm }
  have A1 : 1 < Nat.card A := (Subgroup.one_lt_card_iff_ne_bot A).mpr nontriv
  obtain ⟨p, hp, dvd⟩ := Nat.exists_prime_and_dvd A1.ne'
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := A) p dvd
  have commute {x y : G} (hx : x ∈ A) (hy : y ∈ A) : Commute x y := by
    let x' : A := ⟨x,hx⟩
    let y' : A := ⟨y,hy⟩
    exact congrArg Subtype.val (mul_comm x' y')
  let T : Subgroup G :=
    { carrier := {x | x ∈ A ∧ x^p = 1}
      one_mem' := ⟨A.one_mem, one_pow _⟩
      mul_mem' := fun hx hy => ⟨A.mul_mem hx.1 hy.1, by
        rw [(commute hx.1 hy.1).mul_pow, hx.2, hy.2, mul_one]⟩
      inv_mem' := fun hx => ⟨A.inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ }
  have Tnorm : T.Normal := by
    constructor
    intro x hx g
    exact ⟨norm.conj_mem x hx.1 g, by
      change (MulAut.conj g x)^p = 1
      rw [← map_pow, hx.2, map_one]⟩
  have uPow : u^p = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have huT : (u:G) ∈ T := ⟨u.property, congrArg Subtype.val uPow⟩
  have Tnontriv : T ≠ ⊥ := by
    intro eq
    have hu1 : u = 1 := Subtype.ext (Subgroup.mem_bot.mp (eq ▸ huT))
    rw [hu1, orderOf_one] at hu
    exact hp.ne_one hu.symm
  have eq : T = A := (minimal T Tnorm (fun _ hx => hx.1)).resolve_left Tnontriv
  refine ⟨A, norm, nontriv, minimal, comm, p, hp, ?_⟩
  intro x
  have hx : (x:G) ∈ T := eq.symm ▸ x.property
  exact Subtype.ext hx.2

open scoped BigOperators

end Erdos1160ChiefSeries

namespace Erdos1160ChiefSeries

/-- Build a generating tuple using at most one generator per doubling of subgroup order. -/
theorem subgroup_generating_tuple (G : Type*) [Group G] [Finite G] (S : Subgroup G) :
    ∃ d : ℕ, ∃ v : Fin d → G, Subgroup.closure (Set.range v) = S ∧ 2^d ≤ Nat.card S := by
  classical
  let _ : Finite (Subgroup G) := Finite.of_injective
    (fun A : Subgroup G => (A : Set G)) SetLike.coe_injective
  have wf : WellFounded ((· < ·) : Subgroup G → Subgroup G → Prop) :=
    Finite.wellFounded_of_trans_of_irrefl _
  apply wf.induction S
  clear S
  intro S ih
  by_cases hs : S = ⊥
  · subst S
    refine ⟨0, Fin.elim0, ?_, ?_⟩ <;> simp
  have wf' : WellFounded ((· > ·) : Subgroup G → Subgroup G → Prop) :=
    Finite.wellFounded_of_trans_of_irrefl _
  obtain ⟨H, hH, maximal⟩ := wf'.has_min {H : Subgroup G | H < S} ⟨⊥, bot_lt_iff_ne_bot.mpr hs⟩
  change H < S at hH
  obtain ⟨x, hxS, hxH⟩ := SetLike.exists_of_lt hH
  obtain ⟨d,v,vd,hd⟩ := ih H hH
  let U := H ⊔ Subgroup.closure ({x} : Set G)
  have hxcl : Subgroup.closure ({x} : Set G) ≤ S := by
    rw [Subgroup.closure_le]
    simpa using hxS
  have huS : U ≤ S := sup_le hH.le hxcl
  have xU : x ∈ U := Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_singleton x))
  have hHU : H < U := lt_of_le_of_ne le_sup_left (fun h => hxH (h.symm ▸ xU))
  have eq : U = S := by
    obtain eq | lt := eq_or_lt_of_le huS
    · exact eq
    · exact False.elim (maximal U lt hHU)
  refine ⟨d+1, Fin.snoc v x, ?_, ?_⟩
  · rw [Fin.range_snoc, Set.insert_eq, Subgroup.closure_union, vd, sup_comm]
    exact eq
  · let K := H.subgroupOf S
    have proper : K ≠ ⊤ := by
      intro h
      exact hH.not_ge ((Subgroup.subgroupOf_eq_top).mp h)
    have idx : 2 ≤ K.index := K.one_lt_index_of_ne_top proper
    have same : Nat.card K = Nat.card H := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH.le).toEquiv
    calc
      2^(d+1) = 2^d*2 := pow_succ ..
      _ ≤ Nat.card H * K.index := Nat.mul_le_mul hd idx
      _ = Nat.card S := by rw [← same, K.card_mul_index]

/-- The kernel choices of size `k` can be numbered by tuples of length `log₂ k`. -/
theorem subgroup_choices_card (G : Type*) [Group G] [Finite G] (k : ℕ) :
    Nat.card {A : Subgroup G // Nat.card A = k} ≤ Nat.card G ^ Nat.log 2 k := by
  classical
  let T := {A : Subgroup G // Nat.card A = k}
  have ex (A : T) : ∃ v : Fin (Nat.log 2 k) → G, Subgroup.closure (Set.range v) = A.val := by
    obtain ⟨d,v,hv,hk⟩ := subgroup_generating_tuple G A.val
    have dl := Nat.le_log_of_pow_le (by decide : 1 < 2) (A.property ▸ hk)
    let w (i : Fin (Nat.log 2 k)) := if h : i.val < d then v ⟨i.val,h⟩ else 1
    refine ⟨w, le_antisymm ?_ ?_⟩
    · rw [Subgroup.closure_le]
      rintro _ ⟨i,rfl⟩
      unfold w
      split
      · rw [← hv]; exact Subgroup.subset_closure (Set.mem_range_self _)
      · exact A.val.one_mem
    · rw [← hv]
      apply Subgroup.closure_mono
      rintro _ ⟨i,rfl⟩
      refine ⟨⟨i.val,i.isLt.trans_le dl⟩, ?_⟩
      simp [w,i.isLt]
  choose code decode using ex
  have inj : Function.Injective code := by
    intro A B h
    apply Subtype.ext
    have eq := congrArg (fun v : Fin (Nat.log 2 k) → G => Subgroup.closure (Set.range v)) h
    rw [decode A, decode B] at eq
    exact eq
  simpa only [Nat.card_fun, Nat.card_fin] using Nat.card_le_card_of_injective code inj

end Erdos1160ChiefSeries

namespace Erdos1160ChiefSeries

variable {P G : Type*} [Group P] [Group G]

/-- A mark of the correct prime-power size identifies a Sylow subgroup. -/
def sylowOfMark [Finite G] {p : ℕ} [Fact p.Prime] (f : P →* G) (hf : Function.Injective f)
    (size : Nat.card P = p^(Nat.card G).factorization p) : Sylow p G :=
  Sylow.ofCard f.range ((Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm.trans size)

/-- A quotient mark has exactly the required Sylow cardinality in the quotient. -/
theorem quotient_sylow_mark_card [Finite G] {p : ℕ} [Fact p.Prime] (f : P →* G)
    (hf : Function.Injective f) (size : Nat.card P = p^(Nat.card G).factorization p)
    (A : Subgroup G) [A.Normal] :
    Nat.card (P ⧸ ((QuotientGroup.mk' A).comp f).ker) = p^(Nat.card (G ⧸ A)).factorization p := by
  let S := sylowOfMark f hf size
  let π := QuotientGroup.mk' A
  let T := S.mapSurjective (QuotientGroup.mk'_surjective A)
  calc
    _ = Nat.card ((π.comp f).range) := Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv
    _ = Nat.card T := by rw [MonoidHom.range_comp]; rfl
    _ = _ := T.card_eq_multiplicity

/-- If the marked subgroup and the kernel have coprime orders, its quotient mark
remains injective and the abstract kernel in that coordinate is trivial. -/
theorem quotient_mark_ker_eq_bot [Finite P] (f : P →* G) (hf : Function.Injective f)
    (A : Subgroup G) [A.Normal] (coprime : (Nat.card P).Coprime (Nat.card A)) :
    ((QuotientGroup.mk' A).comp f).ker = ⊥ := by
  let K := ((QuotientGroup.mk' A).comp f).ker
  let r : K →* A :=
    { toFun := fun x => ⟨f x, by
        have hx := MonoidHom.mem_ker.mp x.property
        exact (QuotientGroup.eq_one_iff (f x)).mp hx⟩
      map_one' := Subtype.ext f.map_one
      map_mul' := fun x y => Subtype.ext (f.map_mul _ _) }
  have inj : Function.Injective r := fun x y h => Subtype.ext (hf (congrArg Subtype.val h))
  have dv : Nat.card K ∣ Nat.card A := by
    rw [Nat.card_congr (MonoidHom.ofInjective inj).toEquiv]
    exact r.range.card_subgroup_dvd_card
  have one : Nat.card K ∣ 1 := coprime.gcd_eq_one ▸ Nat.dvd_gcd K.card_subgroup_dvd_card dv
  exact Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.mp one)

/-- A normal chief kernel is contained in the marked Sylow at its prime. -/
theorem chief_kernel_contained_in_mark [Finite G] {p : ℕ} [Fact p.Prime]
    (f : P →* G) (hf : Function.Injective f) (size : Nat.card P = p^(Nat.card G).factorization p)
    (A : Subgroup G) [A.Normal] (elem : ∀ a : A, a^p = 1) : A ≤ f.range := by
  have pgroup : IsPGroup p A := fun a => ⟨1, by simpa using elem a⟩
  exact pgroup.le_sylow_of_normal (sylowOfMark f hf size)

end Erdos1160ChiefSeries

namespace Erdos1160ChiefSeries

/-- A chief kernel changes exactly one abstract Sylow model. Keeping the full
subgroup tuple avoids transporting the other coordinates. -/
structure KernelLabel {J : Type} (P : J → FiniteGrp.{0}) (j₀ : J) (k : ℕ) where
  K : ∀ j, Subgroup (P j)
  normal : ∀ j, (K j).Normal
  size : Nat.card (K j₀) = k
  trivial : ∀ j ≠ j₀, K j = ⊥

/-- Abstract Sylow models of the resulting quotient. -/
noncomputable def KernelLabel.models {J : Type} {P : J → FiniteGrp.{0}} {j₀ : J} {k : ℕ}
    (L : KernelLabel P j₀ k) (j : J) : FiniteGrp.{0} := by
  let _ := L.normal j
  exact FiniteGrp.of ((P j) ⧸ L.K j)

theorem kernelLabel_finite_card {J : Type} (P : J → FiniteGrp.{0}) (j₀ : J) (k : ℕ) :
    Finite (KernelLabel P j₀ k) ∧ Nat.card (KernelLabel P j₀ k) ≤
      Nat.card (P j₀) ^ Nat.log 2 k := by
  classical
  let T := {K : Subgroup (P j₀) // Nat.card K = k}
  let code (a : KernelLabel P j₀ k) : T := ⟨a.K j₀, a.size⟩
  have inj : Function.Injective code := by
    intro a b e
    have hK : a.K = b.K := by
      funext j
      by_cases h : j=j₀
      · subst j; exact congrArg Subtype.val e
      · rw [a.trivial j h, b.trivial j h]
    cases a
    cases b
    cases hK
    rfl
  let _ : Finite (Subgroup (P j₀)) := Finite.of_injective (fun K : Subgroup (P j₀) => (K : Set (P j₀)))
    SetLike.coe_injective
  exact ⟨Finite.of_injective code inj, (Nat.card_le_card_of_injective code inj).trans
    (subgroup_choices_card (P j₀) k)⟩

/-- A normal kernel contained in a mark is identified with the marked kernel. -/
noncomputable def kernelMarkEquiv {P G : Type*} [Group P] [Group G] (m : P →* G)
    (hm : Function.Injective m) (A : Subgroup G) [A.Normal] (contains : A ≤ m.range) :
    ((QuotientGroup.mk' A).comp m).ker ≃* A := by
  let K := ((QuotientGroup.mk' A).comp m).ker
  let f : K →* A :=
    { toFun := fun x => ⟨m x, by
        have h := MonoidHom.mem_ker.mp x.property
        exact (QuotientGroup.eq_one_iff (m x)).mp h⟩
      map_one' := Subtype.ext m.map_one
      map_mul' := fun x y => Subtype.ext (m.map_mul _ _) }
  refine MulEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    exact Subtype.ext (hm (congrArg Subtype.val h))
  · intro a
    obtain ⟨b,hb⟩ := contains a.property
    have bk : b ∈ K := by
      apply MonoidHom.mem_ker.mpr
      change QuotientGroup.mk' A (m b) = 1
      rw [hb]
      exact (QuotientGroup.eq_one_iff (a:G)).mpr a.property
    exact ⟨⟨b,bk⟩, Subtype.ext hb⟩

/-- Each elementary normal chief kernel determines a label with only its own
prime changed. -/
theorem single_changed_sylow {J : Type} {G : Type} [Group G] [Finite G]
    (P : J → FiniteGrp.{0}) (prime : J → ℕ) (pr : ∀ j, (prime j).Prime)
    (different : Function.Injective prime)
    (cover : ∀ p : ℕ, p.Prime → p ∣ Nat.card G → ∃ j, prime j = p)
    (sz : ∀ j, Nat.card (P j) = (prime j)^(Nat.card G).factorization (prime j))
    (mark : ∀ j, P j →* G) (injective : ∀ j, Function.Injective (mark j))
    (A : Subgroup G) [A.Normal] (nonempty : A ≠ ⊥) {p : ℕ} [Fact p.Prime]
    (elem : ∀ a : A, a^p=1) :
    ∃ j : J, prime j = p ∧ A ≤ (mark j).range ∧
      ∃ L : KernelLabel P j (Nat.card A), ∀ i, L.K i = ((QuotientGroup.mk' A).comp (mark i)).ker := by
  have pg : IsPGroup p A := fun a => ⟨1, by simpa using elem a⟩
  have dp : p ∣ Nat.card A := pg.card_eq_or_dvd.resolve_left
    (fun h => nonempty (Subgroup.eq_bot_of_card_eq A h))
  obtain ⟨j,hjp⟩ := cover p Fact.out (dp.trans A.card_subgroup_dvd_card)
  have jsize : Nat.card (P j) = p^(Nat.card G).factorization p := by simpa [hjp] using sz j
  have contain : A ≤ (mark j).range := chief_kernel_contained_in_mark (mark j) (injective j) jsize A elem
  let K (i : J) := ((QuotientGroup.mk' A).comp (mark i)).ker
  have size : Nat.card (K j) = Nat.card A := Nat.card_congr (kernelMarkEquiv (mark j) (injective j) A contain).toEquiv
  have trivial (i : J) (hne : i ≠ j) : K i = ⊥ := by
    obtain ⟨a,ca⟩ := pg.exists_card_eq
    have diff : prime i ≠ p := fun h => hne (different (h.trans hjp.symm))
    have co : (Nat.card (P i)).Coprime (Nat.card A) := by
      rw [sz, ca]
      exact Nat.coprime_pow_primes _ _ (pr i) Fact.out diff
    exact quotient_mark_ker_eq_bot (mark i) (injective i) A co
  exact ⟨j,hjp,contain,⟨K,fun _ => inferInstance,size,trivial⟩,fun _ => rfl⟩

end Erdos1160ChiefSeries

open scoped BigOperators
namespace Erdos1160ChiefSeries

section ChiefStep

variable {p : ℕ} {Q M : Type} [Fact p.Prime] [Group Q] [AddCommGroup M] [Module (ZMod p) M]

private abbrev representationAction (r : Representation (ZMod p) Q M) : DistribMulAction Q M where
  smul q m := r q m
  one_smul m := by change r 1 m = m; rw [map_one]; rfl
  mul_smul q t m := by change r (q*t) m = r q (r t m); rw [map_mul]; rfl
  smul_zero q := map_zero (r q)
  smul_add q a b := map_add (r q) a b

/-- Count marked chief extensions with one quotient and one abstract kernel.
A common local extension is supplied by the fixed marked Sylow model. -/
theorem fixed_chief_step_bound [Finite Q] [Finite M] [Nontrivial M]
    {ι : Type*} {J : Type} [Fintype J] (E : ι → Type) (P : J → Type)
    [∀ i, Group (E i)] [∀ i, Finite (E i)] [∀ j, Group (P j)] [∀ j, Finite (P j)]
    (S : ∀ i, GroupExtension (Multiplicative M) (E i) Q)
    (minimal : ∀ i (A : Subgroup (E i)), A.Normal → A ≤ (S i).inl.range →
      A = ⊥ ∨ A = (S i).inl.range)
    (L : Sylow p Q)
    (local_map : ∀ i j, ∃ f : ((L : Subgroup Q).comap (S i).rightHom) →* E j,
      (∀ a : Multiplicative M, f ⟨(S i).inl a, by
        change (S i).rightHom ((S i).inl a) ∈ (L : Subgroup Q)
        rw [(S i).rightHom_inl]
        exact (L : Subgroup Q).one_mem⟩ = (S j).inl a) ∧
      (∀ x, (S j).rightHom (f x) = (S i).rightHom x))
    (mark : ∀ i j, P j →* E i) (allowed : ∀ i j, (P j →* E i) → Prop)
    (transport : ∀ a b (e : (S a).Equiv (S b)) j,
      allowed b j (e.toMulEquiv.toMonoidHom.comp (mark a j)))
    (distinct : ∀ a b (e : (S a).Equiv (S b)), (∀ j x, e (mark a j x) = mark b j x) → a = b)
    (capacity : J → ℕ)
    (bounds : ∀ i j, Nat.card {f : P j →* E i // allowed i j f} ≤ capacity j) :
    Finite ι ∧ Nat.card ι ≤
      (Nat.card Q * Nat.card M ^ Module.finrank (ZMod p) M) * ∏ j, capacity j := by
  classical
  let _ : Module.Finite (ZMod p) M := Module.Finite.of_finite (R := ZMod p) (M := M)
  let Z := ZMod p
  let T := {ρ : Representation Z Q M // IsSimpleModule (MonoidAlgebra Z Q) ρ.asModule}
  let act (i : ι) : T := ⟨kernelRepresentation (p := p) (S i), kernelRepresentation_simple (S i) (minimal i)⟩
  let F (t : T) := {i : ι // act i = t}
  let _ : Finite (Representation Z Q M) := Finite.of_injective
    (fun a : Representation Z Q M => fun (q : Q) (v : M) => a q v) (fun _ _ h => by
      ext q v
      exact congrFun (congrFun h q) v)
  let _ : Fintype T := Fintype.ofFinite T
  let _ : Fintype (Q ⧸ (L : Subgroup Q)) := Fintype.ofFinite _
  have fd (q : T) : Finite (F q) ∧ Nat.card (F q) ≤ ∏ j, capacity j := by
    have eq_ext (a b : F q) : Nonempty ((S a.val).Equiv (S b.val)) := by
      let σ := (S a.val).surjInvRightHom
      let τ := (S b.val).surjInvRightHom
      let _ : DistribMulAction Q M := representationAction q.val
      obtain ⟨f, k, red⟩ := local_map a.val b.val
      have eq_a : kernelRepresentation (p := p) (S a.val) = q.val := congrArg Subtype.val a.property
      have eq_b : kernelRepresentation (p := p) (S b.val) = q.val := congrArg Subtype.val b.property
      apply extensions_equiv_of_local_map (S a.val) σ (S b.val) τ (L : Subgroup Q)
        (sylow_index_invertible L) _ _ f k red
      · intro g x
        change σ g * (S a.val).inl (Multiplicative.ofAdd x) =
          (S a.val).inl (Multiplicative.ofAdd (q.val g x)) * σ g
        rw [← eq_a]
        exact kernelRepresentation_section (S a.val) σ g x
      · intro g x
        change τ g * (S b.val).inl (Multiplicative.ofAdd x) =
          (S b.val).inl (Multiplicative.ofAdd (q.val g x)) * τ g
        rw [← eq_b]
        exact kernelRepresentation_section (S b.val) τ g x
    exact marked_extension_fiber_bound (fun i : F q => E i.val) P (fun i : F q => S i.val)
      (fun i : F q => mark i.val) (fun i : F q => allowed i.val) eq_ext
      (fun a b e j => transport a.val b.val e j)
      (fun a b e h => Subtype.ext (distinct a.val b.val e h)) capacity (fun a j => bounds a.val j)
  let (q : T) : Finite (F q) := (fd q).1
  let iso : ι ≃ ((q : T) × F q) :=
    { toFun := fun i => ⟨act i, i, rfl⟩
      invFun := fun x => x.2.val
      left_inv := fun _ => rfl
      right_inv := by rintro ⟨q, i, rfl⟩; rfl }
  refine ⟨Finite.of_injective iso iso.injective, ?_⟩
  calc
    _ = ∑ q : T, Nat.card (F q) := (Nat.card_congr iso).trans Nat.card_sigma
    _ ≤ ∑ _q : T, ∏ j, capacity j := Finset.sum_le_sum (fun q _ => (fd q).2)
    _ = Nat.card T * ∏ j, capacity j := by
      rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
      rfl
    _ ≤ _ := Nat.mul_le_mul_right _ (irreducible_actions_card_bound Z Q M)

end ChiefStep

end Erdos1160ChiefSeries

open scoped BigOperators
namespace Erdos1160ChiefSeries

section CoprimeLifts
variable {G M : Type*} [Group G] [AddCommGroup M] [DistribMulAction G M]

/-- Lifts of a given map into the quotient are conjugate by the abelian kernel
when the domain order acts invertibly on it. -/
theorem lifts_conjugate_of_invertible_card {X Q : Type*} [Group X] [Group Q] [Fintype G]
    (S : GroupExtension (Multiplicative M) X Q)
    (index_invertible : Function.Bijective (fun z : M => Fintype.card G • z))
    (ψ : G →* Q) (f t : G →* X)
    (hf : ∀ x, S.rightHom (f x) = ψ x) (ht : ∀ x, S.rightHom (t x) = ψ x)
    (action : ∀ x a, t x * S.inl (Multiplicative.ofAdd a) =
      S.inl (Multiplicative.ofAdd (x • a)) * t x) :
    ∃ a : Multiplicative M, ∀ x, f x = S.inl a * t x * (S.inl a)⁻¹ := by
  have lift (x : G) : ∃ a : Multiplicative M, f x = S.inl a * t x := by
    have mem : f x * (t x)⁻¹ ∈ S.inl.range := by
      simp [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, hf, ht]
    obtain ⟨a, ha⟩ := mem
    exact ⟨a, by simp [ha]⟩
  choose d hd using lift
  let b (x : G) := (d x).toAdd
  have hb (x : G) : f x = S.inl (Multiplicative.ofAdd (b x)) * t x := hd x
  have crossed (x y : G) : b (x*y) = b x + x • b y := by
    have h : S.inl (Multiplicative.ofAdd (b (x*y))) * t (x*y) =
        S.inl (Multiplicative.ofAdd (b x + x • b y)) * t (x*y) := by
      calc
        _ = f x * f y := by rw [← hb, map_mul]
        _ = (S.inl (Multiplicative.ofAdd (b x)) * (t x *
            S.inl (Multiplicative.ofAdd (b y)))) * t y := by rw [hb x, hb y]; simp [mul_assoc]
        _ = _ := by
          rw [action, ofAdd_add, map_mul, map_mul]
          simp [mul_assoc]
    exact congrArg Multiplicative.toAdd (S.inl_injective (mul_right_cancel h))
  obtain ⟨a,ha⟩ := crossed_hom_principal index_invertible b crossed
  refine ⟨Multiplicative.ofAdd a, fun x => ?_⟩
  rw [hb, ha]
  calc
    _ = S.inl (Multiplicative.ofAdd a) * (S.inl (Multiplicative.ofAdd (x • (-a))) * t x) := by
      simp [sub_eq_add_neg, smul_neg, ofAdd_add, mul_assoc]
    _ = _ := by rw [← action]; simp [mul_assoc]

end CoprimeLifts

section QuotientLifts
variable {p : ℕ} {Q M : Type} [Fact p.Prime] [Group Q] [AddCommGroup M] [Module (ZMod p) M]

/-- Counting lifts over a coprime subgroup uses the abelian kernel rather than the full group. -/
theorem coprime_quotient_lifts_card_le {L E : Type} [Group L] [Finite L] [Group E] [Finite M]
    (S : GroupExtension (Multiplicative M) E Q) (ψ : L →* Q) (coprime : ¬ p ∣ Nat.card L) :
    Nat.card {f : L →* E // ∀ x, S.rightHom (f x) = ψ x} ≤ Nat.card M := by
  classical
  let I := {f : L →* E // ∀ x, S.rightHom (f x) = ψ x}
  change Nat.card I ≤ _
  by_cases h : Nonempty I
  · let t := Classical.choice h
    let _ : Fintype L := Fintype.ofFinite L
    let r : Representation (ZMod p) L M := (kernelRepresentation (p := p) S).comp ψ
    let _ : DistribMulAction L M := representationAction r
    have nz : (Fintype.card L : ZMod p) ≠ 0 := by
      intro hzero
      have hdiv := (ZMod.natCast_eq_zero_iff (Fintype.card L) p).mp hzero
      exact coprime (by simpa only [Nat.card_eq_fintype_card (α := L)] using hdiv)
    have invertible : Function.Bijective (fun a : M => Fintype.card L • a) := by
      simpa only [Nat.cast_smul_eq_nsmul] using (isUnit_iff_ne_zero.mpr nz).smul_bijective (β := M)
    have action (x : L) (a : M) : t.val x * S.inl (Multiplicative.ofAdd a) =
        S.inl (Multiplicative.ofAdd (x • a)) * t.val x := by
      change t.val x * S.inl (Multiplicative.ofAdd a) =
        S.inl (Multiplicative.ofAdd ((kernelRepresentation (p := p) S) (ψ x) a)) * t.val x
      have eq := kernelRepresentation_projection (p := p) S (t.val x) (Multiplicative.ofAdd a)
      rw [t.property x] at eq
      change (kernelRepresentation (p := p) S) (ψ x) a = _ at eq
      rw [eq]
      change t.val x * S.inl (Multiplicative.ofAdd a) =
        S.inl (S.conjAct (t.val x) (Multiplicative.ofAdd a)) * t.val x
      rw [S.inl_conjAct_comm, inv_mul_cancel_right]
    have ex (f : I) : ∃ a : Multiplicative M, ∀ x, f.val x = S.inl a * t.val x * (S.inl a)⁻¹ :=
      lifts_conjugate_of_invertible_card S invertible ψ f.val t.val f.property t.property action
    choose code hc using ex
    apply Nat.card_le_card_of_injective (fun i : I => (code i).toAdd)
    intro i j eq
    apply Subtype.ext
    ext x
    rw [hc i x, hc j x, Multiplicative.toAdd.injective eq]
  · have empty : IsEmpty I := ⟨fun x => h ⟨x⟩⟩
    rw [Nat.card_eq_zero.mpr (.inl empty)]
    exact Nat.zero_le _

/-- All marks over a fixed chief extension fit the step budget. The selected
prime pays for generator images, and each coprime prime pays for one kernel element. -/
theorem chief_mark_lift_budget {J E : Type} [Fintype J] [DecidableEq J] [Group E] [Finite E] [Finite M]
    (S : GroupExtension (Multiplicative M) E Q) (P : J → Type)
    [∀ j, Group (P j)] [∀ j, Finite (P j)]
    (j₀ : J) (r : ℕ) (size : Nat.card (P j₀) ≤ 2^r)
    (coprime : ∀ j ≠ j₀, ¬ p ∣ Nat.card (P j))
    (ψ : ∀ j, P j →* Q) (K : ∀ j, Subgroup (P j))
    (inc : ∀ j, K j →* Multiplicative M) :
    (∀ j, Nat.card {f : P j →* E // (∀ k : K j, f k = S.inl (inc j k)) ∧
       ∀ x, S.rightHom (f x) = ψ j x} ≤ if j=j₀ then Nat.card M^r else Nat.card M) ∧
    (∏ j : J, if j=j₀ then Nat.card M^r else Nat.card M) ≤ Nat.card M^(r+Fintype.card J) := by
  constructor
  · intro j
    by_cases eq : j=j₀
    · subst j
      rw [if_pos rfl]
      obtain ⟨d,v,gen,hd⟩ := subgroup_generating_tuple (P j₀) ⊤
      have gen' : Subgroup.closure ((K j₀ : Set (P j₀)) ∪ Set.range v) = ⊤ := by
        apply le_antisymm le_top
        rw [← gen]
        exact Subgroup.closure_mono Set.subset_union_right
      have hd' : d ≤ r := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
        ((hd.trans (Subgroup.card_top.trans_le size)))
      have markCount := marked_lifts_card_le S (K j₀) (S.inl.comp (inc j₀)) (ψ j₀) v gen'
      have hm : Nat.card (Multiplicative M) = Nat.card M := Nat.card_congr Multiplicative.toAdd
      rw [hm] at markCount
      exact markCount.trans (Nat.pow_le_pow_right Nat.card_pos hd')
    · rw [if_neg eq]
      let _ : Finite (P j →* E) := Finite.of_injective
        (fun f : P j →* E => (f : P j → E)) DFunLike.coe_injective
      let L := {f : P j →* E // ∀ x, S.rightHom (f x) = ψ j x}
      let restrict (f : {f : P j →* E // (∀ k : K j, f k = S.inl (inc j k)) ∧
          ∀ x, S.rightHom (f x) = ψ j x}) : L := ⟨f.val, f.property.2⟩
      have less := Nat.card_le_card_of_injective restrict
        (fun _ _ f => Subtype.ext (congrArg (fun l : L => l.val) f))
      exact less.trans (coprime_quotient_lifts_card_le S (ψ j) (coprime j eq))
  · calc
      _ ≤ ∏ j : J, (if j=j₀ then Nat.card M^r else 1) * Nat.card M := by
        apply Finset.prod_le_prod'
        intro j _
        by_cases eq : j=j₀
        · simp only [eq]
          exact Nat.le_mul_of_pos_right _ Nat.card_pos
        · simp [eq]
      _ = Nat.card M^r * Nat.card M^(Fintype.card J) := by
        rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_const]
        simp
      _ = _ := (pow_add ..).symm

end QuotientLifts

end Erdos1160ChiefSeries

namespace Erdos1160ChiefSeries

variable {P E F Q : Type*} [Group P] [Group E] [Group F] [Group Q]

/-- A marked subgroup containing the extension kernel supplies a model for the
kernel in the abstract marked subgroup. -/
def extensionFromMark (m : P →* E) (π : E →* Q) (hm : Function.Injective m)
    (hπ : Function.Surjective π) (K : Subgroup P) (hK : K = (π.comp m).ker)
    (contains : π.ker ≤ m.range) : GroupExtension K E Q where
  inl := m.comp K.subtype
  rightHom := π
  inl_injective := hm.comp Subtype.val_injective
  rightHom_surjective := hπ
  range_inl_eq_ker_rightHom := by
    apply le_antisymm
    · rintro _ ⟨x,rfl⟩
      have hx := x.property
      change (x : P) ∈ K at hx
      exact hK.le hx
    · intro x hx
      obtain ⟨y,rfl⟩ := contains hx
      refine ⟨⟨y, ?_⟩, rfl⟩
      rw [hK]
      exact hx

/-- The preimage of the image of a marked subgroup is the original subgroup
when it contains the entire kernel. -/
noncomputable def markedPreimage (m : P →* E) (π : E →* Q) (hm : Function.Injective m)
    (contains : π.ker ≤ m.range) : P ≃* (π.comp m).range.comap π := by
  have he : (π.comp m).range.comap π = m.range := by
    rw [MonoidHom.range_comp, Subgroup.comap_map_eq_self contains]
  exact (MonoidHom.ofInjective hm).trans (MulEquiv.subgroupCongr he.symm)

private theorem coe_markedPreimage (m : P →* E) (π : E →* Q) (hm : Function.Injective m)
    (contains : π.ker ≤ m.range) (x : P) :
    (markedPreimage m π hm contains x : E) = m x := by
  simp [markedPreimage, MonoidHom.ofInjective_apply]

/-- Equal marked quotient maps yield the local map needed for the extension
comparison, using only the common abstract marked subgroup. -/
theorem compatible_local_map_of_mark (m : P →* E) (m' : P →* F) (π : E →* Q) (π' : F →* Q)
    (hm : Function.Injective m) (contains : π.ker ≤ m.range) (same : π.comp m = π'.comp m') :
    ∃ f : ((π.comp m).range.comap π) →* F,
      (∀ x : P, f (markedPreimage m π hm contains x) = m' x) ∧
      ∀ x : (π.comp m).range.comap π, π' (f x) = π x := by
  let e := markedPreimage m π hm contains
  let f := m'.comp e.symm.toMonoidHom
  refine ⟨f, ?_, ?_⟩
  · intro x
    change m' (e.symm (e x)) = m' x
    rw [MulEquiv.symm_apply_apply]
  · intro x
    obtain ⟨y,rfl⟩ := e.surjective x
    change π' (m' (e.symm (e y))) = π (e y)
    rw [MulEquiv.symm_apply_apply, coe_markedPreimage]
    exact (DFunLike.congr_fun same y).symm

/-- A factor of size `k` pays for at least `log₂ k` bits of the recursive drop. -/
theorem chief_factor_log_drop {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Nat.log 2 a + Nat.log 2 b ≤ Nat.log 2 (a*b) := by
  apply Nat.le_log_of_pow_le (by decide : 1 < 2)
  rw [pow_add]
  exact Nat.mul_le_mul (Nat.pow_log_le_self _ ha) (Nat.pow_log_le_self _ hb)

end Erdos1160ChiefSeries

open scoped BigOperators
namespace Erdos1160ChiefSeries

/-- Count a family with the same recorded kernel tuple and marked quotient.
The bound charges the possible actions and all choices of marked Sylow lifts. -/
theorem fixed_label_quotient_family_bound {J : Type} {I : Type*} [Fintype J] [DecidableEq J]
    {P : J → FiniteGrp.{0}} {j₀ : J} {k r p : ℕ} [Fact p.Prime] (L : KernelLabel P j₀ k)
    (hkr : k ≤ 2^r) (hk : 1 < k) (hJ : Fintype.card J ≤ r)
    (hP : Nat.card (P j₀) ≤ 2^r) (coprime : ∀ j ≠ j₀, ¬ p ∣ Nat.card (P j))
    (E : I → FiniteGrp.{0}) (Q : FiniteGrp.{0}) (π : ∀ i, E i →* Q)
    (surj : ∀ i, Function.Surjective (π i))
    (mark : ∀ i j, P j →* E i) (marksInj : ∀ i j, Function.Injective (mark i j))
    (markSize : ∀ i, Nat.card (P j₀) = p^(Nat.card (E i)).factorization p)
    (contain : ∀ i, (π i).ker ≤ (mark i j₀).range)
    (kerLabel : ∀ i j, L.K j = ((π i).comp (mark i j)).ker)
    (elementary : ∀ i, IsMulCommutative (π i).ker ∧ ∀ x : (π i).ker, x^p = 1)
    (minimal : ∀ i (B : Subgroup (E i)), B.Normal → B ≤ (π i).ker → B = ⊥ ∨ B = (π i).ker)
    (ψ : ∀ j, P j →* Q) (projection : ∀ i j, (π i).comp (mark i j) = ψ j)
    (distinct : ∀ i i' (e : E i ≃* E i'), (∀ j x, e (mark i j x) = mark i' j x) → i = i') :
    Finite I ∧ Nat.card I ≤ Nat.card Q * k^(3*r) := by
  classical
  by_cases hn : Nonempty I
  swap
  · let empty : IsEmpty I := ⟨fun x => hn ⟨x⟩⟩
    exact ⟨inferInstance, by rw [Nat.card_eq_zero.mpr (.inl empty)]; exact Nat.zero_le _⟩
  let i₀ := Classical.choice hn
  let K := L.K j₀
  let extK (i : I) : GroupExtension K (E i) Q :=
    extensionFromMark (mark i j₀) (π i) (marksInj i j₀) (surj i) K (kerLabel i j₀) (contain i)
  let kernelIso : K ≃* (π i₀).ker :=
    (MonoidHom.ofInjective (extK i₀).inl_injective).trans
      (MulEquiv.subgroupCongr (extK i₀).range_inl_eq_ker_rightHom)
  let _ : IsMulCommutative (π i₀).ker := (elementary i₀).1
  have comm (x y : K) : x*y = y*x := by
    apply kernelIso.injective
    rw [map_mul, map_mul]
    exact IsMulCommutative.is_comm.comm ..
  let _ : CommGroup K := { (inferInstance : Group K) with mul_comm := comm }
  let M := Additive K
  have torsion (a : K) : a^p = 1 := by
    apply kernelIso.injective
    rw [map_pow, map_one]
    exact (elementary i₀).2 _
  letI moduleM : Module (ZMod p) M := AddCommGroup.zmodModule (fun a : M =>
    show (show K from a)^p = 1 from torsion a)
  let _ : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr
    ((Subgroup.one_lt_card_iff_ne_bot K).mp (L.size.symm ▸ hk))
  let _ : Nontrivial M := inferInstanceAs (Nontrivial (Additive K))
  let _ : Finite M := inferInstanceAs (Finite (Additive K))
  letI finiteModuleM : Module.Finite (ZMod p) M := Module.Finite.of_finite (R := ZMod p) (M := M)
  have cardM : Nat.card M = k := (Nat.card_congr Additive.toMul).trans L.size
  let ext (i : I) : GroupExtension (Multiplicative M) (E i) Q := extK i
  have min_ext (i : I) (B : Subgroup (E i)) (hB : B.Normal) (hle : B ≤ (ext i).inl.range) :
      B = ⊥ ∨ B = (ext i).inl.range := by
    rw [(ext i).range_inl_eq_ker_rightHom] at hle ⊢
    exact minimal i B hB hle
  let syl := (sylowOfMark (mark i₀ j₀) (marksInj i₀ j₀) (markSize i₀)).mapSurjective (surj i₀)
  have syl_eq : (syl : Subgroup Q) = (ψ j₀).range := by
    change (mark i₀ j₀).range.map (π i₀) = _
    rw [← MonoidHom.range_comp, projection]
  have localMaps (i i' : I) : ∃ f : ((syl : Subgroup Q).comap (ext i).rightHom) →* E i',
      (∀ a : Multiplicative M, f ⟨(ext i).inl a, by
        change (ext i).rightHom ((ext i).inl a) ∈ (syl : Subgroup Q)
        rw [(ext i).rightHom_inl]
        exact (syl : Subgroup Q).one_mem⟩ = (ext i').inl a) ∧
      (∀ x, (ext i').rightHom (f x) = (ext i).rightHom x) := by
    have hsame := (projection i j₀).trans (projection i' j₀).symm
    obtain ⟨f, lift, proj⟩ := compatible_local_map_of_mark (mark i j₀) (mark i' j₀)
      (π i) (π i') (marksInj i j₀) (contain i) hsame
    have rEq : (syl : Subgroup Q) = ((π i).comp (mark i j₀)).range := by
      rw [syl_eq, projection]
    let tr := MulEquiv.subgroupCongr (congrArg (Subgroup.comap (π i)) rEq)
    refine ⟨f.comp tr.toMonoidHom, ?_, ?_⟩
    · intro a
      have h : tr (⟨(ext i).inl a, by
          change (ext i).rightHom ((ext i).inl a) ∈ (syl : Subgroup Q)
          rw [(ext i).rightHom_inl]
          exact (syl : Subgroup Q).one_mem⟩ : (syl : Subgroup Q).comap (π i)) =
          markedPreimage (mark i j₀) (π i) (marksInj i j₀) (contain i) (a : K).val := by
        apply Subtype.ext
        change (mark i j₀) (a : K).val = _
        rw [coe_markedPreimage]
      change f (tr _) = (ext i').inl a
      exact (congrArg f h).trans (lift (a : K).val)
    · intro x
      exact proj (tr x)
  let inc (j : J) : L.K j →* Multiplicative M :=
    if h : j=j₀ then by subst j; exact MonoidHom.id K else 1
  have restrict_mark (i : I) (j : J) (a : L.K j) : (mark i j) a = (ext i).inl (inc j a) := by
    by_cases eq : j=j₀
    · subst j
      simp only [inc, dif_pos rfl]
      rfl
    · have one : (a : P j) = 1 := Subgroup.mem_bot.mp (L.trivial j eq ▸ a.property)
      simp [inc, eq, one]
  let allowed (i : I) (j : J) (f : P j →* E i) :=
    (∀ a : L.K j, f a = (ext i).inl (inc j a)) ∧ (∀ x, (ext i).rightHom (f x) = ψ j x)
  have transport (a b : I) (e : (ext a).Equiv (ext b)) (j : J) :
      allowed b j (e.toMulEquiv.toMonoidHom.comp (mark a j)) := by
    constructor
    · intro x
      change e (mark a j x) = (ext b).inl (inc j x)
      rw [restrict_mark, e.map_inl]
    · intro x
      change (ext b).rightHom (e (mark a j x)) = _
      rw [e.rightHom_map]
      exact DFunLike.congr_fun (projection a j) x
  let cap (j : J) := if j=j₀ then Nat.card M^r else Nat.card M
  have mark_budget (i : I) := chief_mark_lift_budget (ext i) (fun j => P j) j₀ r hP coprime ψ L.K inc
  obtain ⟨fi, bound⟩ := fixed_chief_step_bound (p := p) (Q := Q) (M := M) (fun i => E i) (fun j => P j) ext min_ext syl localMaps
    mark allowed transport (fun a b e h => distinct a b e.toMulEquiv h) cap
    (fun i j => (mark_budget i).1 j)
  refine ⟨fi, bound.trans ?_⟩
  have dim : Module.finrank (ZMod p) M ≤ r := by
    have hrepr : p^Module.finrank (ZMod p) M = k := by
      calc
        _ = Nat.card (ZMod p) ^ Module.finrank (ZMod p) M :=
          congrArg (fun a : ℕ => a ^ Module.finrank (ZMod p) M) (Nat.card_zmod p).symm
        _ = Nat.card M :=
          (@Module.natCard_eq_pow_finrank (ZMod p) M inferInstance inferInstance moduleM finiteModuleM).symm
        _ = k := cardM
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
      ((Nat.pow_le_pow_left (Fact.out : p.Prime).two_le _).trans (hrepr.trans_le hkr))
  calc
    _ ≤ (Nat.card Q * Nat.card M ^ Module.finrank (ZMod p) M) *
        Nat.card M^(r+Fintype.card J) := Nat.mul_le_mul_left _ (mark_budget i₀).2
    _ = Nat.card Q * k^(Module.finrank (ZMod p) M + (r+Fintype.card J)) := by
      rw [cardM, mul_assoc, ← pow_add]
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))

end Erdos1160ChiefSeries

open CategoryTheory Erdos1160
open scoped BigOperators

namespace Erdos1160ChiefSeries

abbrev IsoClass := Quotient (isIsomorphicSetoid FiniteGrp.{0})

def cls (G : FiniteGrp.{0}) : IsoClass := Quotient.mk _ G

def orderClasses (n : ℕ) : Set IsoClass := cls '' {G : FiniteGrp.{0} | Nat.card G = n}

def solubleClasses (n : ℕ) : Set IsoClass :=
  cls '' {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsSolvable G}

private theorem cls_eq_of_mulEquiv {X Y : FiniteGrp.{0}} (e : X ≃* Y) : cls X = cls Y :=
  Quotient.sound ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp) e.toGrpIso⟩

private noncomputable def classMulEquiv {X Y : FiniteGrp.{0}} (h : cls X = cls Y) : X ≃* Y :=
  ((inducedFunctor FiniteGrp.toGrp).mapIso (Classical.choice (Quotient.exact h))).groupIsoToMulEquiv

/-- Multiplication-table encoding, adapted from @wispiANt's finite_classes in PR #18023. -/
theorem orderClasses_finite (n : ℕ) : (orderClasses n).Finite := by
  classical
  let T := {m : Fin n → Fin n → Fin n // ∃ s : Group (Fin n), s.mul = m}
  let model (t : T) := @FiniteGrp.of (Fin n) t.property.choose inferInstance
  let c (t : T) := cls (model t)
  have cover : orderClasses n ⊆ Set.range c := by
    rintro _ ⟨G, hG, rfl⟩
    let e : Fin n ≃ G := ((Nat.equivFinOfCardPos (α := G) Nat.card_pos.ne').trans
      (finCongr hG)).symm
    let law : Group (Fin n) := e.group
    let t : T := ⟨law.mul, law, rfl⟩
    refine ⟨t, cls_eq_of_mulEquiv ?_⟩
    let f : model t ≃* G :=
      { toEquiv := e
        map_mul' := fun a b =>
          (congrArg e (congrFun (congrFun t.property.choose_spec a) b)).trans
            (e.apply_symm_apply (e a * e b)) }
    exact f
  exact (Set.finite_range c).subset cover

noncomputable def representative {n : ℕ} (x : orderClasses n) : FiniteGrp.{0} :=
  Classical.choose x.property

theorem representative_cls {n : ℕ} (x : orderClasses n) : cls (representative x) = x.val :=
  (Classical.choose_spec x.property).2

theorem representative_card {n : ℕ} (x : orderClasses n) : Nat.card (representative x) = n :=
  (Classical.choose_spec x.property).1

abbrev Profile (n : ℕ) := (p : n.primeFactors) → orderClasses ((p : ℕ)^n.factorization p)

/-- A group with injections identifying the specified abstract Sylow groups in it. -/
structure Marked (n : ℕ) {I : Type} (P : I → FiniteGrp.{0}) where
  group : FiniteGrp.{0}
  size : Nat.card group = n
  soluble : Group.IsSolvable group
  mark : ∀ i : I, P i →* group
  mark_injective : ∀ i, Function.Injective (mark i)

def markedSetoid (n : ℕ) {I : Type} (P : I → FiniteGrp.{0}) : Setoid (Marked n P) where
  r X Y := ∃ e : X.group ≃* Y.group, ∀ i x, e (X.mark i x) = Y.mark i x
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro X
      exact ⟨MulEquiv.refl _, fun _ _ => rfl⟩
    · intro X Y h
      obtain ⟨e,he⟩ := h
      exact ⟨e.symm, fun i x => by rw [← he, MulEquiv.symm_apply_apply]⟩
    · intro X Y Z h₁ h₂
      obtain ⟨e,he⟩ := h₁
      obtain ⟨f,hf⟩ := h₂
      exact ⟨e.trans f, fun i x => by rw [MulEquiv.trans_apply, he, hf]⟩

abbrev MarkedClass (n : ℕ) {I : Type} (P : I → FiniteGrp.{0}) := Quotient (markedSetoid n P)

def forgetMarked {n : ℕ} {I : Type} {P : I → FiniteGrp.{0}} : MarkedClass n P → IsoClass :=
  Quotient.lift (fun X => cls X.group) (fun _ _ e => cls_eq_of_mulEquiv e.choose)

private theorem profile_cover (n : ℕ) : solubleClasses n ⊆
    Set.range (fun z : (p : Profile n) × MarkedClass n (fun i => representative (p i)) =>
      forgetMarked z.2) := by
  classical
  rintro _ ⟨G, ⟨rfl,solvable⟩, rfl⟩
  let syl (p : (Nat.card G).primeFactors) : Sylow (p : ℕ) G := by
    letI : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.property⟩
    exact default
  let p : Profile (Nat.card G) := fun i => by
    letI : Fact (i : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors i.property⟩
    exact ⟨cls (FiniteGrp.of (syl i)), FiniteGrp.of (syl i), (syl i).card_eq_multiplicity, rfl⟩
  let e (i : (Nat.card G).primeFactors) : representative (p i) ≃* (syl i) :=
    classMulEquiv (representative_cls (p i))
  let marked : Marked (Nat.card G) (fun i => representative (p i)) :=
    ⟨G, rfl, solvable, fun i => (syl i).toSubgroup.subtype.comp (e i).toMonoidHom,
      fun i => Subtype.val_injective.comp (e i).injective⟩
  exact ⟨⟨p, Quotient.mk _ marked⟩, rfl⟩

theorem profile_card (q : ℕ) : Nat.card (Profile q) =
    ∏ p ∈ q.primeFactors, g (p^q.factorization p) := by
  rw [Nat.card_pi]
  change (∏ p : q.primeFactors, g (p^q.factorization p)) = _
  exact Finset.prod_finset_coe (fun p => g (p^q.factorization p)) q.primeFactors

/-- The exact project target follows from a uniform bound on each marked profile fiber. -/
theorem project_bound_of_marked_fibers (E : ℕ)
    (bound : ∀ q r : ℕ, Odd q → q < 2^r → ∀ p : Profile q,
      Finite (MarkedClass q (fun i => representative (p i))) ∧
      Nat.card (MarkedClass q (fun i => representative (p i))) ≤ 2^(E*(r+1)^2)) :
    OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H2_R1_H3_R2.H2 := by
  classical
  refine ⟨E, fun q r odd lt => ?_⟩
  let (p : q.primeFactors) : Finite (orderClasses ((p : ℕ)^q.factorization p)) :=
    (orderClasses_finite _).to_subtype
  let _ : Finite (Profile q) := inferInstanceAs (Finite (∀ p : q.primeFactors, orderClasses _))
  let _ := Fintype.ofFinite (Profile q)
  let (p : Profile q) : Finite (MarkedClass q (fun i => representative (p i))) := (bound q r odd lt p).1
  let T := (p : Profile q) × MarkedClass q (fun i => representative (p i))
  let realize (z : T) := forgetMarked z.2
  change (solubleClasses q).ncard ≤ _
  calc
    _ ≤ (Set.range realize).ncard := Set.ncard_le_ncard (profile_cover q) (Set.finite_range _)
    _ ≤ Nat.card T := Nat.card_le_card_of_surjective _ Set.rangeFactorization_surjective
    _ = ∑ p : Profile q, Nat.card (MarkedClass q (fun i => representative (p i))) := Nat.card_sigma
    _ ≤ ∑ _p : Profile q, 2^(E*(r+1)^2) := Finset.sum_le_sum fun p _ => (bound q r odd lt p).2
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm, ← Nat.card_eq_fintype_card, profile_card]
      rfl

end Erdos1160ChiefSeries

namespace Erdos1160ChiefSeries

structure PrescribedSylowSizes {J : Type} (prime : J → ℕ) (n : ℕ) (P : J → FiniteGrp.{0}) : Prop where
  positive : 0 < n
  size : ∀ j, Nat.card (P j) = prime j ^ n.factorization (prime j)
  cover : ∀ p : ℕ, p.Prime → p ∣ n → ∃ j, prime j = p

structure ChiefLabel {J : Type} (n : ℕ) (P : J → FiniteGrp.{0}) where
  coordinate : J
  k : ℕ
  k_gt : 1 < k
  k_le : k ≤ n
  kernels : KernelLabel P coordinate k

noncomputable def ChiefLabel.models {J : Type} {n : ℕ} {P : J → FiniteGrp.{0}}
    (D : ChiefLabel n P) (j : J) : FiniteGrp.{0} := D.kernels.models j

noncomputable def ChiefLabel.quotientMap {J : Type} {n : ℕ} {P : J → FiniteGrp.{0}}
    (D : ChiefLabel n P) (j : J) : P j →* D.models j := by
  let _ := D.kernels.normal j
  exact QuotientGroup.mk' (D.kernels.K j)

/-- Data for one step of the chief-kernel encoding of a marked group. -/
structure ChiefPacket {J : Type} {n : ℕ} {P : J → FiniteGrp.{0}} (prime : J → ℕ)
    (x : MarkedClass n P) (D : ChiefLabel n P) where
  source : Marked n P
  source_class : Quotient.mk (markedSetoid n P) source = x
  target : Marked (n / D.k) D.models
  target_valid : PrescribedSylowSizes prime (n / D.k) D.models
  order_factor : D.k * (n / D.k) = n
  π : source.group →* target.group
  surj : Function.Surjective π
  contain : π.ker ≤ (source.mark D.coordinate).range
  kerLabel : ∀ j, D.kernels.K j = (π.comp (source.mark j)).ker
  elementary : IsMulCommutative π.ker ∧ ∀ a : π.ker, a^(prime D.coordinate) = 1
  minimal : ∀ B : Subgroup source.group, B.Normal → B ≤ π.ker → B = ⊥ ∨ B = π.ker
  mark_project : ∀ j, π.comp (source.mark j) = (target.mark j).comp (D.quotientMap j)

set_option maxHeartbeats 2000000 in
/-- A nontrivial marked solvable group admits a step of the chief-kernel encoding. -/
theorem exists_chief_packet {J : Type} {n : ℕ} {P : J → FiniteGrp.{0}} (prime : J → ℕ)
    (pr : ∀ j, (prime j).Prime) (distinct : Function.Injective prime)
    (valid : PrescribedSylowSizes prime n P) (big : 1 < n) (x : MarkedClass n P) :
    ∃ D : ChiefLabel n P, Nonempty (ChiefPacket prime x D) := by
  classical
  let M := Quotient.out x
  have hcM : Quotient.mk (markedSetoid n P) M = x := Quotient.out_eq' x
  have nt : Nontrivial M.group := not_subsingleton_iff_nontrivial.mp fun hs => by
    have wrong : Nat.card M.group = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hs,inferInstance⟩
    exact big.ne' (M.size.symm.trans wrong)
  let _ : Nontrivial M.group := nt
  let _ : Group.IsSolvable M.group := M.soluble
  obtain ⟨A,normal,notBot,minA,comm,p,pp,elem⟩ := exists_elementary_chief_kernel M.group
  let _ : A.Normal := normal
  let _ : Fact p.Prime := ⟨pp⟩
  have cover (p : ℕ) (hp : p.Prime) (h : p ∣ Nat.card M.group) : ∃ j, prime j=p :=
    valid.cover p hp (M.size ▸ h)
  have cardSylow (j : J) : Nat.card (P j) = prime j ^ (Nat.card M.group).factorization (prime j) := by
    rw [M.size]
    exact valid.size j
  obtain ⟨j₀,jp,contain,L,kerEq⟩ := single_changed_sylow P prime pr distinct cover cardSylow
    M.mark M.mark_injective A notBot elem
  let k := Nat.card A
  have k_gt : 1 < k := (Subgroup.one_lt_card_iff_ne_bot A).mpr notBot
  have k_le : k ≤ n := A.card_le_card_group.trans_eq M.size
  let D : ChiefLabel n P := ⟨j₀,k,k_gt,k_le,L⟩
  have mulOrder : k * A.index = n := A.card_mul_index.trans M.size
  have qOrder : A.index = n/k := by
    have e := congrArg (fun u : ℕ => u/k) mulOrder
    rwa [Nat.mul_div_cancel_left _ (by omega : 0 < k)] at e
  let π := QuotientGroup.mk' A
  let _ (j : J) : (D.kernels.K j).Normal := D.kernels.normal j
  let transport (j : J) := QuotientGroup.quotientMulEquivOfEq (kerEq j)
  let target : Marked (n/D.k) D.models :=
    { group := FiniteGrp.of (M.group ⧸ A)
      size := A.index_eq_card.symm.trans qOrder
      soluble := by change Group.IsSolvable (M.group ⧸ A); infer_instance
      mark := fun j => (QuotientGroup.kerLift (π.comp (M.mark j))).comp (transport j).toMonoidHom
      mark_injective := fun j => (QuotientGroup.kerLift_injective _).comp (transport j).injective }
  have target_positive : 0 < n/D.k := target.size ▸ Nat.card_pos
  have target_cover (l : ℕ) (lp : l.Prime) (dv : l ∣ n/D.k) : ∃ j, prime j=l := by
    apply valid.cover l lp
    have factored : D.k * (n/D.k) = n := qOrder ▸ mulOrder
    exact dv.trans ⟨D.k, factored.symm.trans (Nat.mul_comm _ _)⟩
  have target_shape (j : J) : Nat.card (D.models j) = prime j ^ (n/D.k).factorization (prime j) := by
    let _ : Fact (prime j).Prime := ⟨pr j⟩
    have cardTransport := Nat.card_congr (transport j).toEquiv
    exact cardTransport.trans ((quotient_sylow_mark_card (M.mark j) (M.mark_injective j)
      (cardSylow j) A).trans (by rw [← target.size]; rfl))
  refine ⟨D, ⟨{
    source := M
    source_class := hcM
    target := target
    target_valid := ⟨target_positive,target_shape,target_cover⟩
    order_factor := qOrder ▸ mulOrder
    π := π
    surj := QuotientGroup.mk'_surjective A
    contain := ?_
    kerLabel := kerEq
    elementary := ?_
    minimal := ?_
    mark_project := ?_ }⟩⟩
  · change π.ker ≤ _
    rw [QuotientGroup.ker_mk']
    exact contain
  · change IsMulCommutative π.ker ∧ ∀ a : π.ker, a^(prime j₀) = 1
    rw [QuotientGroup.ker_mk', jp]
    exact ⟨comm,elem⟩
  · change ∀ B : Subgroup M.group, B.Normal → B ≤ π.ker → B = ⊥ ∨ B = π.ker
    rw [QuotientGroup.ker_mk']
    exact minA
  · intro j
    apply MonoidHom.ext
    intro a
    change (π.comp (M.mark j)) a =
      QuotientGroup.kerLift (π.comp (M.mark j)) (transport j (QuotientGroup.mk a))
    rw [QuotientGroup.quotientMulEquivOfEq_mk, QuotientGroup.kerLift_mk]

end Erdos1160ChiefSeries

namespace Erdos1160ChiefSeries

/-- Transport all quotient projections in a packet fiber to one common marked quotient. -/
theorem marked_packet_fiber_bound {J : Type} {I : Type*} [Fintype J] [DecidableEq J]
    {P : J → FiniteGrp.{0}} {n r : ℕ} (prime : J → ℕ) (pr : ∀ j, (prime j).Prime)
    (distinctPrimes : Function.Injective prime) (valid : PrescribedSylowSizes prime n P)
    (bound : n < 2^r) (number : Fintype.card J ≤ r)
    (D : ChiefLabel n P) (x : I → MarkedClass n P) (inj : Function.Injective x)
    (packet : ∀ i : I, ChiefPacket prime (x i) D) (y : MarkedClass (n/D.k) D.models)
    (same : ∀ i : I, Quotient.mk (markedSetoid (n/D.k) D.models) (packet i).target = y) :
    Finite I ∧ Nat.card I ≤ (n/D.k) * D.k^(3*r) := by
  classical
  let Q := Quotient.out y
  have orig : Quotient.mk (markedSetoid (n/D.k) D.models) Q = y := Quotient.out_eq' y
  have equiv (i : I) : ∃ e : (packet i).target.group ≃* Q.group,
      ∀ j a, e ((packet i).target.mark j a) = Q.mark j a :=
    Quotient.exact ((same i).trans orig.symm)
  choose toQ respects using equiv
  let projections (i : I) := (toQ i).toMonoidHom.comp (packet i).π
  let marks (i : I) := (packet i).source.mark
  have proj_surj (i : I) : Function.Surjective (projections i) :=
    (toQ i).surjective.comp (packet i).surj
  have ker_base (i : I) {z : (packet i).source.group} :
      projections i z = 1 ↔ (packet i).π z = 1 := by
    change toQ i ((packet i).π z) = 1 ↔ _
    rw [← (toQ i).map_one, (toQ i).injective.eq_iff]
  have same_ker (i : I) : (projections i).ker = (packet i).π.ker := by
    ext z
    simp only [MonoidHom.mem_ker, ker_base]
  have same_marked_ker (i : I) (j : J) :
      ((projections i).comp (marks i j)).ker = ((packet i).π.comp ((packet i).source.mark j)).ker := by
    ext z
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, marks, ker_base]
  have cardP : Nat.card (P D.coordinate) ≤ 2^r := by
    rw [valid.size]
    exact (Nat.le_of_dvd valid.positive (Nat.ordProj_dvd n _)).trans bound.le
  have cop (j : J) (hj : j ≠ D.coordinate) : ¬ prime D.coordinate ∣ Nat.card (P j) := by
    rw [valid.size]
    have ne : prime D.coordinate ≠ prime j := fun h => hj (distinctPrimes h).symm
    have co := Nat.coprime_pow_primes 1 (n.factorization (prime j)) (pr D.coordinate) (pr j) ne
    apply (pr D.coordinate).coprime_iff_not_dvd.mp
    simpa using co
  let p := prime D.coordinate
  let _ : Fact p.Prime := ⟨pr D.coordinate⟩
  let ψ (j : J) : P j →* Q.group := (Q.mark j).comp (D.quotientMap j)
  have projecting (i : I) (j : J) : (projections i).comp (marks i j) = ψ j := by
    apply MonoidHom.ext
    intro a
    have h := DFunLike.congr_fun ((packet i).mark_project j) a
    change (packet i).π ((packet i).source.mark j a) = (packet i).target.mark j (D.quotientMap j a) at h
    change toQ i ((packet i).π ((packet i).source.mark j a)) = Q.mark j (D.quotientMap j a)
    rw [h, respects]
  have unique (i i' : I) (e : (packet i).source.group ≃* (packet i').source.group)
      (h : ∀ j a, e (marks i j a) = marks i' j a) : i=i' := by
    apply inj
    rw [← (packet i).source_class, ← (packet i').source_class]
    exact Quotient.sound ⟨e,h⟩
  have hsz (i : I) : Nat.card (P D.coordinate) = p^(Nat.card (packet i).source.group).factorization p := by
    rw [(packet i).source.size]
    exact valid.size _
  obtain ⟨fi,count⟩ := fixed_label_quotient_family_bound (p := p) D.kernels (D.k_le.trans bound.le) D.k_gt
    number cardP cop (fun i => (packet i).source.group) Q.group projections proj_surj marks
    (fun i j => (packet i).source.mark_injective j) hsz
    (fun i => (same_ker i).symm ▸ (packet i).contain)
    (fun i j => ((packet i).kerLabel j).trans (same_marked_ker i j).symm)
    (fun i => (same_ker i).symm ▸ (packet i).elementary)
    (fun i => (same_ker i).symm ▸ (packet i).minimal) ψ projecting unique
  exact ⟨fi, by simpa only [Q.size] using count⟩

end Erdos1160ChiefSeries

open scoped BigOperators
namespace Erdos1160ChiefSeries

/-- Cardinality is the sum of the finite fibers of a map into a finite type. -/
private theorem count_by_fibers {X Y : Type*} [Fintype Y] (f : X → Y)
    (fiberFinite : ∀ y, Finite {x : X // f x=y}) :
    Finite X ∧ Nat.card X = ∑ y : Y, Nat.card {x : X // f x=y} := by
  let (y : Y) : Finite {x : X // f x=y} := fiberFinite y
  let e : X ≃ ((y : Y) × {x : X // f x=y}) :=
    { toFun := fun x => ⟨f x,x,rfl⟩
      invFun := fun z => z.2.val
      left_inv := fun _ => rfl
      right_inv := by rintro ⟨y,x,rfl⟩; rfl }
  exact ⟨Finite.of_injective e e.injective, (Nat.card_congr e).trans Nat.card_sigma⟩

private theorem marked_classes_one {J : Type} (P : J → FiniteGrp.{0}) :
    Finite (MarkedClass 1 P) ∧ Nat.card (MarkedClass 1 P) ≤ 1 := by
  have same (U V : Marked 1 P) : (markedSetoid 1 P).r U V := by
    let _ : Subsingleton U.group := (Nat.card_eq_one_iff_unique.mp U.size).1
    let _ : Subsingleton V.group := (Nat.card_eq_one_iff_unique.mp V.size).1
    let e : U.group ≃* V.group := MulEquiv.ofBijective (1 : U.group →* V.group)
      ⟨fun _ _ _ => Subsingleton.elim _ _, fun z => ⟨1, Subsingleton.elim _ z⟩⟩
    exact ⟨e,fun _ _ => Subsingleton.elim _ _⟩
  let _ : Subsingleton (MarkedClass 1 P) := ⟨fun a b =>
    Quotient.inductionOn₂ a b (fun u v => Quotient.sound (same u v))⟩
  exact ⟨inferInstance, Finite.card_le_one_iff_subsingleton.mpr inferInstance⟩

private abbrev ChiefSize (n : ℕ) := { k : Fin (n+1) // 1 < k.val }
private abbrev LabelCode {J : Type} (n : ℕ) (P : J → FiniteGrp.{0}) :=
  (j : J) × ((k : ChiefSize n) × KernelLabel P j k.val.val)

private def labelCodeEquiv {J : Type} (n : ℕ) (P : J → FiniteGrp.{0}) :
    ChiefLabel n P ≃ LabelCode n P where
  toFun d := ⟨d.coordinate,⟨⟨d.k, Nat.lt_succ_of_le d.k_le⟩,d.k_gt⟩,d.kernels⟩
  invFun z := ⟨z.1,z.2.1.val.val,z.2.1.property,Nat.le_of_lt_succ z.2.1.val.isLt,z.2.2⟩
  left_inv := by intro x; cases x; rfl
  right_inv := by rintro ⟨j, ⟨⟨k,hk⟩,g⟩,l⟩; rfl

/-- A logarithmic loss of one chief kernel pays for the count of actions, all
marks, kernel embeddings, and the choice of prime and kernel order. -/
private theorem block_cost_exponent {n k r : ℕ} (k_gt : 1 < k) (k_le : k ≤ n) (hn : n ≤ 2^r) :
    2^(Nat.log 2 k*r) * ((n/k) * k^(3*r) * 2^(10*r*Nat.log 2 (n/k))) * 2^(2*r) ≤
      2^(10*r*Nat.log 2 n) := by
  let a := Nat.log 2 k
  let t := Nat.log 2 (n/k)
  have pos : 0 < n/k := Nat.div_pos k_le (by omega)
  have as : 1 ≤ a := Nat.le_log_of_pow_le (by decide : 1 < 2) (by omega)
  have loss : a+t ≤ Nat.log 2 n :=
    (chief_factor_log_drop (by omega : k ≠ 0) pos.ne').trans
      (Nat.log_mono_right (by simpa [Nat.mul_comm] using Nat.div_mul_le_self n k))
  have ksize : k ≤ 2^(a+1) := (Nat.lt_pow_succ_log_self (by decide : 1 < 2) k).le
  have rsize : n/k ≤ 2^r := (Nat.div_le_self n k).trans hn
  calc
    _ ≤ 2^(a*r) * (2^r * (2^(a+1))^(3*r) * 2^(10*r*t)) * 2^(2*r) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _
        (Nat.mul_le_mul rsize (Nat.pow_le_pow_left ksize _))))
    _ = 2^(a*r+r+(a+1)*(3*r)+10*r*t+2*r) := by
      simp only [← pow_mul, ← pow_add]
      congr 1
      ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by
      nlinarith only [Nat.le_mul_of_pos_right r as, Nat.mul_le_mul_left (10*r) loss])

set_option maxHeartbeats 2000000 in
/-- Strong induction on the marked group order. The logarithmic order drop
pays for the finite quotient fibers and for all kernel choices at each step. -/
theorem marked_profile_recursive_bound {J : Type} [Fintype J] [DecidableEq J]
    (prime : J → ℕ) (pr : ∀ j, (prime j).Prime) (different : Function.Injective prime)
    (r : ℕ) (number : Fintype.card J ≤ r) :
    ∀ n (P : J → FiniteGrp.{0}), PrescribedSylowSizes prime n P → n < 2^r →
      Finite (MarkedClass n P) ∧ Nat.card (MarkedClass n P) ≤ 2^(10*r*Nat.log 2 n) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro P valid lt
    by_cases h1 : n=1
    · subst n
      simpa using marked_classes_one P
    have big : 1 < n := by have := valid.positive; omega
    let X := MarkedClass n P
    let C := LabelCode n P
    let e := labelCodeEquiv n P
    have packets (x : X) := exists_chief_packet prime pr different valid big x
    choose lab labPacket using packets
    let tag (x : X) : C := e (lab x)
    let B (c : C) := {x : X // tag x = c}
    let D (c : C) := e.symm c
    have data (c : C) (x : B c) : ChiefPacket prime x.val (D c) := by
      have eq : lab x.val = D c := by
        have h := congrArg e.symm x.property
        change e.symm (e (lab x.val)) = D c at h
        simpa only [Equiv.symm_apply_apply] using h
      exact eq ▸ (labPacket x.val).some
    have fibers (c : C) : Finite (B c) ∧ Nat.card (B c) ≤
        (n/(D c).k) * (D c).k^(3*r) * 2^(10*r*Nat.log 2 (n/(D c).k)) := by
      by_cases inhabited : Nonempty (B c)
      swap
      · let empty : IsEmpty (B c) := ⟨fun x => inhabited ⟨x⟩⟩
        exact ⟨inferInstance, by rw [Nat.card_eq_zero.mpr (.inl empty)]; exact Nat.zero_le _⟩
      let sample := Classical.choice inhabited
      have smaller : n/(D c).k < n := Nat.div_lt_self valid.positive (D c).k_gt
      have sub := ih _ smaller _ (data c sample).target_valid (smaller.trans lt)
      let Y := MarkedClass (n/(D c).k) (D c).models
      let _ : Finite Y := sub.1
      let _ : Fintype Y := Fintype.ofFinite Y
      let qtag (x : B c) : Y := Quotient.mk _ (data c x).target
      have qfib (y : Y) : Finite {x : B c // qtag x=y} ∧
          Nat.card {x : B c // qtag x=y} ≤ (n/(D c).k) * (D c).k^(3*r) := by
        exact marked_packet_fiber_bound prime pr different valid lt number (D c)
          (fun z : {x : B c // qtag x=y} => z.val.val)
          (fun _ _ h => Subtype.ext (Subtype.ext h)) (fun z => data c z.val) y (fun z => z.property)
      have counts := count_by_fibers qtag (fun y => (qfib y).1)
      refine ⟨counts.1, ?_⟩
      calc
        _ = ∑ y : Y, Nat.card {x : B c // qtag x=y} := counts.2
        _ ≤ ∑ _y : Y, (n/(D c).k) * (D c).k^(3*r) := Finset.sum_le_sum (fun y _ => (qfib y).2)
        _ = ((n/(D c).k) * (D c).k^(3*r)) * Nat.card Y := by
          rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
          simp [mul_comm]
        _ ≤ _ := Nat.mul_le_mul_left _ sub.2
    let (j : J) (k : ChiefSize n) : Finite (KernelLabel P j k.val.val) :=
      (kernelLabel_finite_card P j k.val.val).1
    let (j : J) (k : ChiefSize n) : Fintype (KernelLabel P j k.val.val) := Fintype.ofFinite _
    let _ : Fintype C := inferInstanceAs (Fintype ((j : J) × ((k : ChiefSize n) × KernelLabel P j k.val.val)))
    have total := count_by_fibers tag (fun c => (fibers c).1)
    refine ⟨total.1, ?_⟩
    have block (j : J) (z : ChiefSize n) :
        (∑ K : KernelLabel P j z.val.val, Nat.card (B ⟨j,z,K⟩)) * 2^(2*r) ≤
          2^(10*r*Nat.log 2 n) := by
      let k := z.val.val
      have k_gt : 1 < k := z.property
      have k_le : k ≤ n := Nat.le_of_lt_succ z.val.isLt
      have pcard : Nat.card (P j) ≤ 2^r := by
        rw [valid.size]
        exact (Nat.le_of_dvd valid.positive (Nat.ordProj_dvd n _)).trans lt.le
      have nK : Nat.card (KernelLabel P j k) ≤ 2^(Nat.log 2 k*r) := by
        calc
          _ ≤ Nat.card (P j)^Nat.log 2 k := (kernelLabel_finite_card P j k).2
          _ ≤ (2^r)^Nat.log 2 k := Nat.pow_le_pow_left pcard _
          _ = _ := by rw [← pow_mul, mul_comm r]
      have sumK : (∑ K : KernelLabel P j k, Nat.card (B ⟨j,z,K⟩)) ≤
          2^(Nat.log 2 k*r) * ((n/k) * k^(3*r) * 2^(10*r*Nat.log 2 (n/k))) := by
        calc
          _ ≤ ∑ _K : KernelLabel P j k, (n/k) * k^(3*r) * 2^(10*r*Nat.log 2 (n/k)) :=
            Finset.sum_le_sum (fun K _ => (fibers ⟨j,z,K⟩).2)
          _ = Nat.card (KernelLabel P j k) * ((n/k) * k^(3*r) * 2^(10*r*Nat.log 2 (n/k))) := by
            rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
            rfl
          _ ≤ _ := Nat.mul_le_mul_right _ nK
      exact (Nat.mul_le_mul_right _ sumK).trans (block_cost_exponent k_gt k_le lt.le)
    have hcodes : Nat.card X = ∑ j : J, ∑ z : ChiefSize n,
        ∑ K : KernelLabel P j z.val.val, Nat.card (B ⟨j,z,K⟩) := by
      rw [total.2]
      change (∑ c : (j : J) × ((k : ChiefSize n) × KernelLabel P j k.val.val), Nat.card (B c)) = _
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro j _
      rw [Fintype.sum_sigma]
    have hsz : Fintype.card (ChiefSize n) ≤ 2^r := by
      have h := Fintype.card_subtype_le (fun k : Fin (n+1) => 1 < k.val)
      exact h.trans (by simpa using lt)
    have nout : Fintype.card J * Fintype.card (ChiefSize n) ≤ 2^(2*r) := by
      calc
        _ ≤ 2^r * 2^r := Nat.mul_le_mul (number.trans r.lt_two_pow_self.le) hsz
        _ = _ := by rw [← pow_add, two_mul]
    have hmul : Nat.card X * 2^(2*r) ≤ 2^(10*r*Nat.log 2 n) * 2^(2*r) := by
      rw [hcodes]
      simp only [Finset.sum_mul]
      calc
        _ ≤ ∑ _j : J, ∑ _z : ChiefSize n, 2^(10*r*Nat.log 2 n) := by
          apply Finset.sum_le_sum
          intro j _
          apply Finset.sum_le_sum
          intro z _
          have h := block j z
          simpa only [Finset.sum_mul] using h
        _ = 2^(10*r*Nat.log 2 n) * (Fintype.card J * Fintype.card (ChiefSize n)) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ac_rfl
        _ ≤ _ := Nat.mul_le_mul_left _ nout
    exact Nat.le_of_mul_le_mul_right hmul (Nat.two_pow_pos _)

end Erdos1160ChiefSeries

open scoped BigOperators
namespace Erdos1160ChiefSeries

private theorem prime_indices_bound {q r : ℕ} (hq : 0 < q) (hqr : q < 2^r) :
    Fintype.card q.primeFactors ≤ r := by
  have h : 2^q.primeFactors.card ≤ q := by
    calc
      _ = ∏ p ∈ q.primeFactors, (2:ℕ) := by rw [Finset.prod_const]
      _ ≤ ∏ p ∈ q.primeFactors, p^q.factorization p := by
        apply Finset.prod_le_prod'
        intro p hp
        have pp := Nat.prime_of_mem_primeFactors hp
        have v := pp.factorization_pos_of_dvd hq.ne' (Nat.dvd_of_mem_primeFactors hp)
        exact pp.two_le.trans (by simpa using Nat.pow_le_pow_right pp.pos v)
      _ = q := Nat.prod_factorization_pow_eq_self hq.ne'
  simpa only [Fintype.card_coe] using
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (h.trans hqr.le)

end Erdos1160ChiefSeries

/-- The prescribed-Sylow estimate for soluble groups. -/
theorem OMA.solution : OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H2_R1_H3_R2.H2 := by
  classical
  apply Erdos1160ChiefSeries.project_bound_of_marked_fibers 10
  intro q r odd size profile
  let P (j : q.primeFactors) := Erdos1160ChiefSeries.representative (profile j)
  have qpos : 0 < q := by obtain ⟨a,ha⟩ := odd; omega
  have valid : Erdos1160ChiefSeries.PrescribedSylowSizes (Subtype.val : q.primeFactors → ℕ) q P :=
    { positive := qpos
      size := fun j => Erdos1160ChiefSeries.representative_card (profile j)
      cover := fun p hp dv => ⟨⟨p,Nat.mem_primeFactors.mpr ⟨hp,dv,qpos.ne'⟩⟩,rfl⟩ }
  obtain ⟨fin, h⟩ := Erdos1160ChiefSeries.marked_profile_recursive_bound
    (Subtype.val : q.primeFactors → ℕ) (fun j => Nat.prime_of_mem_primeFactors j.property)
    Subtype.val_injective r (Erdos1160ChiefSeries.prime_indices_bound qpos size) q P valid size
  refine ⟨fin,h.trans (Nat.pow_le_pow_right (by decide) ?_)⟩
  have lr := (Nat.log_lt_of_lt_pow qpos.ne' size).le
  nlinarith only [Nat.mul_le_mul_left (10*r) lr, Nat.zero_le r]
