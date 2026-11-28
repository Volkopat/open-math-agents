import OMAReductions.R_mo_438166_R1
import Mathlib

/- Adapted from OpenAI, openai/math at 3344da59991ed94f9ba711217b29c1d760badfa6 (Apache-2.0). Question by Finitistic dimension, MathOverflow 438166 (CC BY-SA). Pinned Lean 4.33.1 port. -/

section

/- Compatibility lemma for the pinned Mathlib; the zero tensor is a pure tensor. -/
namespace TensorProduct
theorem inductionOn
    {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : M ⊗[R] N → Prop}
    (x : M ⊗[R] N)
    (tmul : ∀ m n, motive (m ⊗ₜ[R] n))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive x := by
  exact TensorProduct.induction_on x (by simpa using tmul 0 0) tmul add
end TensorProduct

end

section

namespace OAI

open scoped TensorProduct
open TensorProduct
noncomputable section
namespace DerivedBar
universe u
variable (k A N : Type u) [Field k] [Ring A] [Algebra k A]
  [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

/-- The augmented bar terms: term 0 is N; term (n+1) is A ⊗ term n. -/
abbrev term : ℕ → ModuleCat k
  | 0 => ModuleCat.of k N
  | n+1 => ModuleCat.of k (A ⊗[k] term n)

abbrev termModule : (n : ℕ) → Module A (term k A N n)
  | 0 => inferInstanceAs (Module A N)
  | n+1 => inferInstanceAs (Module A (A ⊗[k] term k A N n))

instance (n : ℕ) : Module A (term k A N n) := termModule k A N n

instance termTower : (n : ℕ) → IsScalarTower k A (term k A N n)
  | 0 => inferInstanceAs (IsScalarTower k A N)
  | n+1 => inferInstanceAs (IsScalarTower k A (A ⊗[k] term k A N n))


/-- Multiplication/action on the first two positions of an augmented bar word. -/
def action (M : Type u) [AddCommGroup M] [Module k M] [Module A M]
    [IsScalarTower k A M] : A ⊗[k] M →ₗ[A] M :=
  { (TensorProduct.lift (Algebra.lsmul k k M).toLinearMap).toAddHom with
    map_smul' := by
      intro a z
      induction z using TensorProduct.inductionOn with
      | tmul b m => simp [TensorProduct.smul_tmul']
      | add x y hx hy => simp_all [smul_add] }

@[simp] theorem action_tmul (M : Type u) [AddCommGroup M] [Module k M] [Module A M]
    [IsScalarTower k A M] (a : A) (m : M) :
    action k A M (a ⊗ₜ[k] m) = a • m := rfl

/-- Recursive alternating face differential. No A-flatness of N is required. -/
def differential : (n : ℕ) → term k A N (n+1) →ₗ[A] term k A N n
  | 0 => action k A N
  | n+1 => action k A (term k A N (n+1)) -
      AlgebraTensorModule.lTensor A A ((differential n).restrictScalars k)

@[simp] theorem differential_zero_tmul (a : A) (z : N) :
    differential k A N 0 (a ⊗ₜ[k] z) = a • z := rfl

@[simp] theorem differential_succ_tmul (n : ℕ) (a : A) (z : term k A N (n+1)) :
    differential k A N (n+1) (a ⊗ₜ[k] z) =
      a • z - a ⊗ₜ[k] differential k A N n z := rfl

/-- The actual bar differential squares to zero in every degree. -/
theorem differential_sq (n : ℕ) :
    (differential k A N n).comp (differential k A N (n+1)) = 0 := by
  induction n with
  | zero =>
    apply AlgebraTensorModule.ext
    intro a z
    change differential k A N 0 (differential k A N 1 (a ⊗ₜ[k] z)) = 0
    rw [differential_succ_tmul k A N 0 a z, map_sub, map_smul,
      differential_zero_tmul k A N a (differential k A N 0 z), sub_self]
  | succ n ih =>
    apply AlgebraTensorModule.ext
    intro a z
    have hz := LinearMap.congr_fun ih z
    change differential k A N n (differential k A N (n+1) z) = 0 at hz
    change differential k A N (n+1) (differential k A N (n+2) (a ⊗ₜ[k] z)) = 0
    rw [differential_succ_tmul k A N (n+1) a z, map_sub, map_smul,
      differential_succ_tmul k A N n a (differential k A N (n+1) z), hz,
      TensorProduct.tmul_zero, sub_zero, sub_self]

/-- Unit insertion; this is k-linear, generally not A-linear. -/
def contraction (n : ℕ) : term k A N n →ₗ[k] term k A N (n+1) :=
  TensorProduct.mk k A (term k A N n) 1

omit [Module A N] [IsScalarTower k A N] in
@[simp] theorem contraction_apply (n : ℕ) (z : term k A N n) :
    contraction k A N n z = 1 ⊗ₜ[k] z := rfl

/-- The augmented degree-zero contraction identity. -/
theorem contraction_zero (z : N) :
    differential k A N 0 (contraction k A N 0 z) = z := by
  change (1 : A) • z = z
  exact one_smul A z

/-- Contracting homotopy in every positive augmented degree. -/
theorem contraction_identity (n : ℕ) (z : term k A N (n+1)) :
    differential k A N (n+1) (contraction k A N (n+1) z) +
      contraction k A N n (differential k A N n z) = z := by
  change differential k A N (n+1) (1 ⊗ₜ[k] z) + 1 ⊗ₜ[k] differential k A N n z = z
  rw [differential_succ_tmul k A N n 1 z, one_smul, sub_add_cancel]

/-- Exactness of the augmented absolute bar complex as actual A-linear maps. -/
theorem differential_exact (n : ℕ) :
    LinearMap.range (differential k A N (n+1)) =
      LinearMap.ker (differential k A N n) := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    exact LinearMap.congr_fun (differential_sq k A N n) z
  · intro z hz
    refine ⟨contraction k A N (n+1) z, ?_⟩
    have h := contraction_identity k A N n z
    have hz' : differential k A N n z = 0 := hz
    simpa [hz'] using h

/-- The augmented chain complex, including N at homological degree zero. -/
def augmentedComplex : ChainComplex (ModuleCat A) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of A (term k A N n))
    (fun n => ModuleCat.ofHom (differential k A N n))
    (fun n => by exact ModuleCat.hom_ext (differential_sq k A N n))

/-- The unaugmented absolute bar complex, degree n = A ⊗ A^⊗n ⊗ N. -/
def complex : ChainComplex (ModuleCat A) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of A (term k A N (n+1)))
    (fun n => ModuleCat.ofHom (differential k A N (n+1)))
    (fun n => by exact ModuleCat.hom_ext (differential_sq k A N (n+1)))


open CategoryTheory CategoryTheory.Limits

/-- Every unaugmented bar term is free as a left A-module, even for noncommutative A. -/
instance term_free (n : ℕ) : Module.Free A (term k A N (n+1)) :=
  Module.Free.of_basis (Algebra.TensorProduct.basis A (Module.Free.chooseBasis k (term k A N n)))

instance complex_projective (n : ℕ) : Projective ((complex k A N).X n) := by
  change Projective (ModuleCat.of A (term k A N (n+1)))
  exact inferInstance

/-- Surjectivity of the bar augmentation, witnessed by insertion of 1. -/
theorem augmentation_surjective : Function.Surjective (differential k A N 0) := by
  intro z
  exact ⟨contraction k A N 0 z, contraction_zero k A N z⟩

/-- The bar augmentation as a chain map to N concentrated in degree zero. -/
def augmentation : complex k A N ⟶ (ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A N) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨ModuleCat.ofHom (differential k A N 0), by
      change ModuleCat.ofHom (differential k A N 1) ≫
        ModuleCat.ofHom (differential k A N 0) = 0
      exact ModuleCat.hom_ext (differential_sq k A N 0)⟩

/-- All positive-degree homology of the unaugmented bar complex vanishes. -/
theorem complex_exactAt_succ (n : ℕ) : (complex k A N).ExactAt (n+1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n+1+1) (n+1) n (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  simpa only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
    complex, ChainComplex.of_d, ModuleCat.hom_ofHom] using! differential_exact k A N (n+1)

/-- Exactness at the augmentation term, stated in the abelian category of A-modules. -/
theorem augmentation_exact :
    (ShortComplex.mk ((complex k A N).d 1 0) (ModuleCat.ofHom (differential k A N 0))
      (ModuleCat.hom_ext (differential_sq k A N 0))).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  exact differential_exact k A N 0

instance augmentation_epi : Epi (ModuleCat.ofHom (differential k A N 0)) :=
  (ModuleCat.epi_iff_surjective _).mpr (augmentation_surjective k A N)

/-- The absolute algebra bar augmentation is a genuine quasi-isomorphism. -/
instance augmentation_quasiIso : QuasiIso (augmentation k A N) := by
  refine ⟨fun n => ?_⟩
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · dsimp [augmentation]
      exact ⟨augmentation_exact k A N, augmentation_epi k A N⟩
    all_goals rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt']
    · exact complex_exactAt_succ k A N n
    · apply ChainComplex.exactAt_succ_single_obj

/-- Explicit free absolute bar resolution, packaged for derived functor computations. -/
def projectiveResolution : ProjectiveResolution (ModuleCat.of A N) where
  complex := complex k A N
  π := augmentation k A N
end DerivedBar

end

end OAI

end

section

namespace OAI
open scoped TensorProduct
open TensorProduct CategoryTheory
noncomputable section

namespace DerivedBar
namespace FreeBaseChange
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
variable (f : A →ₐ[k] D)
variable (V W U : Type u) [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]

/-- Replace only the free leading algebra coefficient along f. -/
def coefficient : A ⊗[k] V →ₗ[k] D ⊗[k] V :=
  TensorProduct.map f.toLinearMap LinearMap.id

@[simp] theorem coefficient_tmul (a : A) (v : V) :
    coefficient f V (a ⊗ₜ[k] v) = f a ⊗ₜ[k] v := rfl

/-- Coefficient change intertwines the two regular left actions. -/
theorem coefficient_smul (a : A) (z : A ⊗[k] V) :
    coefficient f V (a • z) = f a • coefficient f V z := by
  induction z using TensorProduct.inductionOn with
  | tmul b v => simp [TensorProduct.smul_tmul', map_mul]
  | add x y hx hy => simp_all [smul_add]

/-- Scalar extension of a morphism between explicitly free A-modules. -/
def map (h : A ⊗[k] V →ₗ[A] A ⊗[k] W) : D ⊗[k] V →ₗ[D] D ⊗[k] W :=
  (action k D (D ⊗[k] W)).comp
    (AlgebraTensorModule.lTensor D D
      ((coefficient f W).comp ((h.restrictScalars k).comp (TensorProduct.mk k A V 1))))

@[simp] theorem map_tmul (h : A ⊗[k] V →ₗ[A] A ⊗[k] W) (d : D) (v : V) :
    map f V W h (d ⊗ₜ[k] v) = d • coefficient f W (h (1 ⊗ₜ[k] v)) := rfl

/-- Extension commutes with the map on arbitrary free tensors, not just generators. -/
theorem map_coefficient (h : A ⊗[k] V →ₗ[A] A ⊗[k] W) (z : A ⊗[k] V) :
    map f V W h (coefficient f V z) = coefficient f W (h z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a v =>
    rw [coefficient_tmul, map_tmul]
    have hz : a ⊗ₜ[k] v = a • ((1 : A) ⊗ₜ[k] v) := by
      simp [TensorProduct.smul_tmul']
    rw [hz, h.map_smul, coefficient_smul]
  | add x y hx hy => simp_all

/-- Composition of actual free-module maps is preserved by extension. -/
theorem map_comp (h : A ⊗[k] V →ₗ[A] A ⊗[k] W)
    (g : A ⊗[k] W →ₗ[A] A ⊗[k] U) :
    map f V U (g.comp h) = (map f W U g).comp (map f V W h) := by
  apply AlgebraTensorModule.ext
  intro d v
  change d • coefficient f U (g (h (1 ⊗ₜ[k] v))) =
    map f W U g (d • coefficient f W (h (1 ⊗ₜ[k] v)))
  rw [LinearMap.map_smul, map_coefficient]

@[simp] theorem map_zero : map f V W 0 = 0 := by
  apply AlgebraTensorModule.ext
  intro d v
  simp only [map_tmul, LinearMap.zero_apply, _root_.map_zero, smul_zero]

@[simp] theorem map_id : map f V V LinearMap.id = LinearMap.id := by
  apply AlgebraTensorModule.ext
  intro d v
  simp [map_tmul, TensorProduct.smul_tmul']

end FreeBaseChange

universe u
variable (k A D N : Type u) [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
  [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
variable (f : A →ₐ[k] D)

/-- The two-sided absolute bar differential after changing the free coefficient A to D. -/
def twoSidedDifferential (n : ℕ) :
    D ⊗[k] term k A N (n+1) →ₗ[D] D ⊗[k] term k A N n :=
  FreeBaseChange.map f _ _ (differential k A N (n+1))

/-- The endpoint face minus the remaining absolute bar faces, with their actual signs. -/
theorem twoSidedDifferential_tmul (n : ℕ) (d : D) (z : term k A N (n+1)) :
    twoSidedDifferential k A D N f n (d ⊗ₜ[k] z) =
      d • FreeBaseChange.coefficient f (term k A N n) z -
        d ⊗ₜ[k] differential k A N n z := by
  unfold twoSidedDifferential
  rw [FreeBaseChange.map_tmul, differential_succ_tmul k A N n 1 z,
    one_smul, map_sub, FreeBaseChange.coefficient_tmul, map_one, smul_sub,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem twoSidedDifferential_sq (n : ℕ) :
    (twoSidedDifferential k A D N f n).comp
      (twoSidedDifferential k A D N f (n+1)) = 0 := by
  unfold twoSidedDifferential
  rw [← FreeBaseChange.map_comp, differential_sq, FreeBaseChange.map_zero]

/-- Actual D-linear two-sided bar complex with degree-n term D ⊗_k A^⊗n ⊗_k N. -/
def twoSidedComplex : ChainComplex (ModuleCat D) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of D (D ⊗[k] term k A N n))
    (fun n => ModuleCat.ofHom (twoSidedDifferential k A D N f n))
    (fun n => ModuleCat.hom_ext (twoSidedDifferential_sq k A D N f n))
end DerivedBar

end

end OAI

end

section

namespace OAI
open scoped TensorProduct
open TensorProduct CategoryTheory
noncomputable section

namespace DerivedBar.Balanced
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
variable (f : A →ₐ[k] D)
variable (V : Type u) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]

/-- The balancing relations for the right A-action d·a = d*f(a). -/
def relations : Submodule D (D ⊗[k] V) :=
  Submodule.span D {z | ∃ (d : D) (a : A) (v : V),
    z = (d * f a) ⊗ₜ[k] v - d ⊗ₜ[k] (a • v)}

/-- Noncommutative balanced tensor D ⊗_A V, presented using tensors over the field. -/
abbrev tensor := (D ⊗[k] V) ⧸ relations f V

/-- Its canonical D-linear quotient map. -/
def quotient : D ⊗[k] V →ₗ[D] tensor f V := (relations f V).mkQ

omit [IsScalarTower k A V] in
/-- The defining balanced relation, as an equality in the actual quotient module. -/
theorem balanced (d : D) (a : A) (v : V) :
    quotient f V ((d*f a) ⊗ₜ[k] v) = quotient f V (d ⊗ₜ[k] (a • v)) := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨d, a, v, rfl⟩)

section Maps
variable (W U : Type u) [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
  [AddCommGroup U] [Module k U] [Module A U] [IsScalarTower k A U]

/-- Balanced tensor acts on all A-linear maps. -/
theorem map_relations (h : V →ₗ[A] W) : relations f V ≤
    ((quotient f W).comp (AlgebraTensorModule.lTensor D D (h.restrictScalars k))).ker := by
  apply Submodule.span_le.mpr
  rintro z ⟨d, a, v, rfl⟩
  change quotient f W ((AlgebraTensorModule.lTensor D D (h.restrictScalars k))
    ((d*f a) ⊗ₜ[k] v - d ⊗ₜ[k] (a • v))) = 0
  simp only [map_sub, AlgebraTensorModule.lTensor_tmul, LinearMap.coe_restrictScalars,
    LinearMap.map_smul]
  rw [balanced, sub_self]

def map (h : V →ₗ[A] W) : tensor f V →ₗ[D] tensor f W :=
  (relations f V).liftQ
    ((quotient f W).comp (AlgebraTensorModule.lTensor D D (h.restrictScalars k)))
    (map_relations f V W h)

@[simp] theorem map_quotient_tmul (h : V →ₗ[A] W) (d : D) (v : V) :
    map f V W h (quotient f V (d ⊗ₜ[k] v)) = quotient f W (d ⊗ₜ[k] h v) := rfl

/-- Composition preservation for the actual balanced tensor, proved from its quotient presentation. -/
theorem map_comp (h : V →ₗ[A] W) (g : W →ₗ[A] U) :
    map f V U (g.comp h) = (map f W U g).comp (map f V W h) := by
  apply (relations f V).linearMap_qext
  apply AlgebraTensorModule.ext
  intro d v
  rfl

@[simp] theorem map_zero : map f V W 0 = 0 := by
  apply (relations f V).linearMap_qext
  apply AlgebraTensorModule.ext
  intro d v
  change quotient f W (d ⊗ₜ[k] (0 : W)) = 0
  rw [TensorProduct.tmul_zero, _root_.map_zero]

@[simp] theorem map_id : map f V V LinearMap.id = LinearMap.id := by
  apply (relations f V).linearMap_qext
  apply AlgebraTensorModule.ext
  intro d v
  rfl
end Maps

variable (W : Type u) [AddCommGroup W] [Module k W]

/-- Evaluation of D ⊗_k (A ⊗_k W) on the two leading coefficients. -/
def collapse : D ⊗[k] (A ⊗[k] W) →ₗ[D] D ⊗[k] W :=
  (DerivedBar.action k D (D ⊗[k] W)).comp
    (AlgebraTensorModule.lTensor D D (FreeBaseChange.coefficient f W))

@[simp] theorem collapse_tmul (d : D) (z : A ⊗[k] W) :
    collapse f W (d ⊗ₜ[k] z) = d • FreeBaseChange.coefficient f W z := rfl

/-- The evaluation kills all balancing relations, without commutativity of A or D. -/
theorem relations_le_ker_collapse : relations f (A ⊗[k] W) ≤ (collapse f W).ker := by
  apply Submodule.span_le.mpr
  rintro z ⟨d, a, v, rfl⟩
  change collapse f W ((d*f a) ⊗ₜ[k] v - d ⊗ₜ[k] (a • v)) = 0
  rw [map_sub, collapse_tmul, collapse_tmul, FreeBaseChange.coefficient_smul,
    mul_smul, sub_self]

/-- Descent of coefficient evaluation to the balanced tensor. -/
def descend : tensor f (A ⊗[k] W) →ₗ[D] D ⊗[k] W :=
  (relations f (A ⊗[k] W)).liftQ (collapse f W) (relations_le_ker_collapse f W)

/-- The inverse inserts a unit A coefficient before taking the balanced quotient. -/
def insert : D ⊗[k] W →ₗ[D] tensor f (A ⊗[k] W) :=
  (quotient f (A ⊗[k] W)).comp
    (AlgebraTensorModule.lTensor D D (TensorProduct.mk k A W 1))

@[simp] theorem descend_quotient (z : D ⊗[k] (A ⊗[k] W)) :
    descend f W (quotient f (A ⊗[k] W) z) = collapse f W z := rfl

@[simp] theorem insert_tmul (d : D) (w : W) :
    insert f W (d ⊗ₜ[k] w) = quotient f (A ⊗[k] W) (d ⊗ₜ[k] (1 ⊗ₜ[k] w)) := rfl

/-- One inverse identity of the actual balanced free-module tensor equivalence. -/
theorem descend_insert : (descend f W).comp (insert f W) = LinearMap.id := by
  apply AlgebraTensorModule.ext
  intro d w
  simp [LinearMap.comp_apply, TensorProduct.smul_tmul']

/-- The other inverse identity follows from balancing, not from flatness. -/
theorem insert_descend : (insert f W).comp (descend f W) = LinearMap.id := by
  apply (relations f (A ⊗[k] W)).linearMap_qext
  apply AlgebraTensorModule.ext
  intro d z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp_all [TensorProduct.tmul_add]
  | tmul a w =>
    change insert f W (collapse f W (d ⊗ₜ[k] (a ⊗ₜ[k] w))) =
      quotient f (A ⊗[k] W) (d ⊗ₜ[k] (a ⊗ₜ[k] w))
    rw [collapse_tmul, FreeBaseChange.coefficient_tmul, TensorProduct.smul_tmul',
      smul_eq_mul, insert_tmul, balanced]
    simp [TensorProduct.smul_tmul']

/-- The standard identification D ⊗_A (A ⊗_k W) ≅ D ⊗_k W for arbitrary algebras. -/
def freeEquiv : tensor f (A ⊗[k] W) ≃ₗ[D] D ⊗[k] W :=
  LinearEquiv.ofLinearMap (descend f W) (insert f W) (descend_insert f W) (insert_descend f W)

end DerivedBar.Balanced

end

end OAI

end

section

namespace OAI
open scoped TensorProduct
open TensorProduct CategoryTheory TrivSqZeroExt
noncomputable section

namespace DerivedBar
namespace SquareZero
universe u
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]

/-- (TrivSqZeroExt D X) pure bar word with precisely r factors in the square-zero ideal. -/
inductive Word : (n r : ℕ) → term k (TrivSqZeroExt D X) N n → Prop
  | nil (v : N) : Word 0 0 v
  | base {n r : ℕ} {v : term k (TrivSqZeroExt D X) N n} (d : D) (h : Word n r v) :
      Word (n+1) r ((inl d : (TrivSqZeroExt D X)) ⊗ₜ[k] v)
  | ideal {n r : ℕ} {v : term k (TrivSqZeroExt D X) N n} (x : X) (h : Word n r v) :
      Word (n+1) (r+1) ((inr x : (TrivSqZeroExt D X)) ⊗ₜ[k] v)

/-- The homogeneous subspace, defined by actual tensors rather than formal signs. -/
def weight (n r : ℕ) : Submodule k (term k (TrivSqZeroExt D X) N n) :=
  Submodule.span k {v | Word k D X N n r v}

private theorem map_span_mem {V W : Type u} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (g : V →ₗ[k] W) (s : Set V) (t : Submodule k W)
    (h : ∀ v ∈ s, g v ∈ t) {v : V} (hv : v ∈ Submodule.span k s) : g v ∈ t := by
  have hle : Submodule.span k s ≤ t.comap g := Submodule.span_le.mpr h
  exact hle hv

variable {k D X N}

theorem base_tmul_mem {n r : ℕ} (d : D) {v : term k (TrivSqZeroExt D X) N n}
    (hv : v ∈ weight k D X N n r) :
    (inl d : (TrivSqZeroExt D X)) ⊗ₜ[k] v ∈ weight k D X N (n+1) r :=
  map_span_mem k (TensorProduct.mk k (TrivSqZeroExt D X) (term k (TrivSqZeroExt D X) N n) (inl d)) _ _
    (fun _ h => Submodule.subset_span (Word.base d h)) hv

theorem ideal_tmul_mem {n r : ℕ} (x : X) {v : term k (TrivSqZeroExt D X) N n}
    (hv : v ∈ weight k D X N n r) :
    (inr x : (TrivSqZeroExt D X)) ⊗ₜ[k] v ∈ weight k D X N (n+1) (r+1) :=
  map_span_mem k (TensorProduct.mk k (TrivSqZeroExt D X) (term k (TrivSqZeroExt D X) N n) (inr x)) _ _
    (fun _ h => Submodule.subset_span (Word.ideal x h)) hv

variable [Module (TrivSqZeroExt D X) N] [IsScalarTower k (TrivSqZeroExt D X) N]

/-- Degree-zero multiplication preserves the number of ideal factors. -/
theorem base_smul_mem {n r : ℕ} (d : D) {v : term k (TrivSqZeroExt D X) N n}
    (hv : v ∈ weight k D X N n r) :
    (inl d : (TrivSqZeroExt D X)) • v ∈ weight k D X N n r := by
  apply map_span_mem k (Algebra.lsmul k k (term k (TrivSqZeroExt D X) N n) (inl d)) _ _ _ hv
  intro v h
  cases h with
  | nil v => exact Submodule.subset_span (Word.nil _)
  | base b hb =>
    simp only [Algebra.lsmul_coe, TensorProduct.smul_tmul', smul_eq_mul,
      inl_mul_inl, weight]
    exact Submodule.subset_span (Word.base (d*b) hb)
  | ideal x hx =>
    simp only [Algebra.lsmul_coe, TensorProduct.smul_tmul', smul_eq_mul,
      inl_mul_inr, weight]
    exact Submodule.subset_span (Word.ideal (d • x) hx)

/-- Degree-one multiplication raises the count, with square-zero products vanishing. -/
theorem ideal_smul_mem (hN : ∀ (x : X) (v : N), (inr x : (TrivSqZeroExt D X)) • v = 0)
    {n r : ℕ} (x : X) {v : term k (TrivSqZeroExt D X) N n}
    (hv : v ∈ weight k D X N n r) :
    (inr x : (TrivSqZeroExt D X)) • v ∈ weight k D X N n (r+1) := by
  apply map_span_mem k (Algebra.lsmul k k (term k (TrivSqZeroExt D X) N n) (inr x)) _ _ _ hv
  intro v h
  cases h with
  | nil v =>
    simp only [Algebra.lsmul_coe, hN]

    exact Submodule.zero_mem _
  | base b hb =>
    simp only [Algebra.lsmul_coe, TensorProduct.smul_tmul', smul_eq_mul,
      inr_mul_inl, weight]
    exact Submodule.subset_span (Word.ideal (MulOpposite.op b • x) hb)
  | ideal y hy =>
    simp only [Algebra.lsmul_coe, TensorProduct.smul_tmul', smul_eq_mul,
      inr_mul_inr, TensorProduct.zero_tmul]
    exact Submodule.zero_mem _

/-- Every face of the augmented algebra bar differential preserves the X-count. -/
theorem differential_mem (hN : ∀ (x : X) (v : N), (inr x : (TrivSqZeroExt D X)) • v = 0)
    (n r : ℕ) {v : term k (TrivSqZeroExt D X) N (n+1)} (hv : v ∈ weight k D X N (n+1) r) :
    differential k (TrivSqZeroExt D X) N n v ∈ weight k D X N n r := by
  induction n generalizing r with
  | zero =>
    apply map_span_mem k ((differential k (TrivSqZeroExt D X) N 0).restrictScalars k) _ _ _ hv
    intro v h
    cases h with
    | base d h =>
      cases h with
      | nil v =>
        exact Submodule.subset_span (Word.nil _)
    | ideal x h =>
      cases h with
      | nil v =>
        simp only [LinearMap.coe_restrictScalars,
          differential_zero_tmul k (TrivSqZeroExt D X) N, hN]
        exact Submodule.zero_mem _
  | succ n ih =>
    apply map_span_mem k ((differential k (TrivSqZeroExt D X) N (n+1)).restrictScalars k) _ _ _ hv
    intro v h
    cases h with
    | base d h =>
      rw [LinearMap.coe_restrictScalars, differential_succ_tmul k (TrivSqZeroExt D X) N n]
      exact Submodule.sub_mem _ (base_smul_mem d (Submodule.subset_span h))
        (base_tmul_mem d (ih _ (Submodule.subset_span h)))
    | ideal x h =>
      rw [LinearMap.coe_restrictScalars, differential_succ_tmul k (TrivSqZeroExt D X) N n]
      exact Submodule.sub_mem _ (ideal_smul_mem hN x (Submodule.subset_span h))
        (ideal_tmul_mem x (ih _ (Submodule.subset_span h)))

variable (k D X N)

/-- The actual complex formed by the fixed-count homogeneous bar subspaces. -/
def weightComplex (hN : ∀ (x : X) (v : N), (inr x : (TrivSqZeroExt D X)) • v = 0) (r : ℕ) :
    ChainComplex (ModuleCat k) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of k (weight k D X N n r))
    (fun n => ModuleCat.ofHom
      (((differential k (TrivSqZeroExt D X) N n).restrictScalars k).restrict
        (fun v hv => differential_mem hN n r hv)))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      exact LinearMap.congr_fun (differential_sq k (TrivSqZeroExt D X) N n) v)
end SquareZero
end DerivedBar

end

end OAI

end

section

namespace OAI
open scoped TensorProduct
open TensorProduct CategoryTheory TrivSqZeroExt
noncomputable section

namespace DerivedBar.SquareZero
universe u
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]

/-- Count-r submodule of the two-sided bar term, with the leading D coefficient uncounted. -/
def twoSidedWeight (n r : ℕ) : Submodule D (D ⊗[k] term k (TrivSqZeroExt D X) N n) :=
  Submodule.span D {w | ∃ (d : D) (v : term k (TrivSqZeroExt D X) N n),
    Word k D X N n r v ∧ w = d ⊗ₜ[k] v}

variable {k D X N}

theorem word_count_le {n r : ℕ} {v : term k (TrivSqZeroExt D X) N n}
    (hv : Word k D X N n r v) : r ≤ n := by
  induction hv with
  | nil => exact Nat.le_refl 0
  | base d h ih => exact Nat.le_trans ih (Nat.le_succ _)
  | ideal x h ih => exact Nat.succ_le_succ ih

theorem weight_eq_bot_of_lt {n r : ℕ} (h : n < r) : weight k D X N n r = ⊥ := by
  apply Submodule.span_eq_bot.mpr
  intro v hv
  exact False.elim (Nat.not_le_of_gt h (word_count_le hv))

/-- A count-r two-sided bar term is zero below degree r. -/
theorem twoSidedWeight_eq_bot_of_lt {n r : ℕ} (h : n < r) :
    twoSidedWeight k D X N n r = ⊥ := by
  apply Submodule.span_eq_bot.mpr
  rintro v ⟨d, z, hz, rfl⟩
  exact False.elim (Nat.not_le_of_gt h (word_count_le hz))

theorem tensor_weight_mem {n r : ℕ} (d : D) {v : term k (TrivSqZeroExt D X) N n}
    (hv : v ∈ weight k D X N n r) : d ⊗ₜ[k] v ∈ twoSidedWeight k D X N n r := by
  let g := TensorProduct.mk k D (term k (TrivSqZeroExt D X) N n) d
  have hle : weight k D X N n r ≤
      ((twoSidedWeight k D X N n r).restrictScalars k).comap g := by
    apply Submodule.span_le.mpr
    intro z hz
    exact Submodule.subset_span ⟨d, z, hz, rfl⟩
  exact hle hv

/-- Projection of the leading square-zero coefficient kills an ideal letter and retains a base letter. -/
theorem coefficient_weight_mem {n r : ℕ}
    {v : term k (TrivSqZeroExt D X) N (n+1)} (hv : v ∈ weight k D X N (n+1) r) :
    FreeBaseChange.coefficient (fstHom k D X) (term k (TrivSqZeroExt D X) N n) v ∈
      twoSidedWeight k D X N n r := by
  let g := FreeBaseChange.coefficient (fstHom k D X) (term k (TrivSqZeroExt D X) N n)
  have hle : weight k D X N (n+1) r ≤
      ((twoSidedWeight k D X N n r).restrictScalars k).comap g := by
    apply Submodule.span_le.mpr
    intro z hz
    cases hz with
    | base d h =>
      exact Submodule.subset_span ⟨d, _, h, rfl⟩
    | ideal x h =>
      change (0 : D) ⊗ₜ[k] _ ∈ twoSidedWeight k D X N n _
      rw [TensorProduct.zero_tmul]
      exact Submodule.zero_mem _
  exact hle hv

variable [Module (TrivSqZeroExt D X) N] [IsScalarTower k (TrivSqZeroExt D X) N]

/-- The actual D-linear two-sided differential preserves X-count; no flatness enters the proof. -/
theorem twoSidedDifferential_mem
    (hN : ∀ (x : X) (v : N), (inr x : TrivSqZeroExt D X) • v = 0)
    (n r : ℕ) {v : D ⊗[k] term k (TrivSqZeroExt D X) N (n+1)}
    (hv : v ∈ twoSidedWeight k D X N (n+1) r) :
    twoSidedDifferential k (TrivSqZeroExt D X) D N (fstHom k D X) n v ∈
      twoSidedWeight k D X N n r := by
  have hle : twoSidedWeight k D X N (n+1) r ≤
      (twoSidedWeight k D X N n r).comap
        (twoSidedDifferential k (TrivSqZeroExt D X) D N (fstHom k D X) n) := by
    apply Submodule.span_le.mpr
    rintro v ⟨d, z, hz, rfl⟩
    change twoSidedDifferential k (TrivSqZeroExt D X) D N (fstHom k D X) n
      (d ⊗ₜ[k] z) ∈ twoSidedWeight k D X N n r
    rw [twoSidedDifferential_tmul]
    exact Submodule.sub_mem _
      (Submodule.smul_mem _ d (coefficient_weight_mem (Submodule.subset_span hz)))
      (tensor_weight_mem d (differential_mem hN n r (Submodule.subset_span hz)))
  exact hle hv

variable (k D X N)

/-- A genuine D-module chain complex for each fixed number of square-zero entries. -/
def twoSidedWeightComplex
    (hN : ∀ (x : X) (v : N), (inr x : TrivSqZeroExt D X) • v = 0) (r : ℕ) :
    ChainComplex (ModuleCat D) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of D (twoSidedWeight k D X N n r))
    (fun n => ModuleCat.ofHom
      ((twoSidedDifferential k (TrivSqZeroExt D X) D N (fstHom k D X) n).restrict
        (fun v hv => twoSidedDifferential_mem hN n r hv)))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      exact LinearMap.congr_fun
        (twoSidedDifferential_sq k (TrivSqZeroExt D X) D N (fstHom k D X) n) v)
end DerivedBar.SquareZero

end

end OAI

end

section

namespace OAI
open scoped TensorProduct
open TensorProduct CategoryTheory TrivSqZeroExt
noncomputable section

namespace DerivedBar.SquareZero
universe u
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]

def baseProjection : Module.End k (TrivSqZeroExt D X) :=
  (inlAlgHom k D X).toLinearMap.comp (fstHom k D X).toLinearMap

def idealProjection : Module.End k (TrivSqZeroExt D X) :=
  LinearMap.id - baseProjection k D X

@[simp] theorem baseProjection_inl (d : D) :
    baseProjection k D X (inl d) = inl d := rfl
@[simp] theorem baseProjection_inr (x : X) :
    baseProjection k D X (inr x) = 0 := rfl
@[simp] theorem idealProjection_inl (d : D) :
    idealProjection k D X (inl d) = 0 := by simp [idealProjection]
@[simp] theorem idealProjection_inr (x : X) :
    idealProjection k D X (inr x) = inr x := by simp [idealProjection]

/-- The actual linear projection onto words with a prescribed X-count. -/
def projection : (n r : ℕ) → Module.End k (term k (TrivSqZeroExt D X) N n)
  | 0, 0 => LinearMap.id
  | 0, _+1 => 0
  | n+1, 0 => TensorProduct.map (baseProjection k D X) (projection n 0)
  | n+1, r+1 => TensorProduct.map (baseProjection k D X) (projection n (r+1)) +
      TensorProduct.map (idealProjection k D X) (projection n r)

@[simp] theorem projection_base (n r : ℕ) (d : D)
    (v : term k (TrivSqZeroExt D X) N n) :
    projection k D X N (n+1) r ((inl d : TrivSqZeroExt D X) ⊗ₜ[k] v) =
      (inl d : TrivSqZeroExt D X) ⊗ₜ[k] projection k D X N n r v := by
  cases r <;> simp [projection]

@[simp] theorem projection_ideal_zero (n : ℕ) (x : X)
    (v : term k (TrivSqZeroExt D X) N n) :
    projection k D X N (n+1) 0 ((inr x : TrivSqZeroExt D X) ⊗ₜ[k] v) = 0 := by
  simp [projection]

@[simp] theorem projection_ideal_succ (n r : ℕ) (x : X)
    (v : term k (TrivSqZeroExt D X) N n) :
    projection k D X N (n+1) (r+1) ((inr x : TrivSqZeroExt D X) ⊗ₜ[k] v) =
      (inr x : TrivSqZeroExt D X) ⊗ₜ[k] projection k D X N n r v := by
  simp [projection]

variable {k D X N}

/-- The projections separate homogeneous bar words exactly. -/
theorem projection_word {n s : ℕ} {v : term k (TrivSqZeroExt D X) N n}
    (hv : Word k D X N n s v) (r : ℕ) :
    projection k D X N n r v = if r = s then v else 0 := by
  induction hv generalizing r with
  | nil v => cases r <;> simp [projection]
  | @base n s v d h ih =>
    rw [projection_base, ih]
    split <;> simp_all
  | @ideal n s v x h ih =>
    cases r with
    | zero =>
      rw [projection_ideal_zero k D X N n x v]
      simp
    | succ r =>
      rw [projection_ideal_succ, ih]
      by_cases hrs : r = s <;> simp [hrs]

/-- Identity on the whole homogeneous subspace, not merely on individual words. -/
theorem projection_self {n r : ℕ} {v : term k (TrivSqZeroExt D X) N n}
    (hv : v ∈ weight k D X N n r) : projection k D X N n r v = v := by
  have hle : weight k D X N n r ≤
      (projection k D X N n r - LinearMap.id).ker := by
    apply Submodule.span_le.mpr
    intro z hz
    change projection k D X N n r z - z = 0
    rw [projection_word hz r, if_pos rfl, sub_self]
  have h := hle hv
  change projection k D X N n r v - v = 0 at h
  exact sub_eq_zero.mp h

/-- Distinct counts are annihilated by the projection. -/
theorem projection_other {n r s : ℕ} (hrs : r ≠ s)
    {v : term k (TrivSqZeroExt D X) N n} (hv : v ∈ weight k D X N n s) :
    projection k D X N n r v = 0 := by
  have hle : weight k D X N n s ≤ (projection k D X N n r).ker := by
    apply Submodule.span_le.mpr
    intro z hz
    change projection k D X N n r z = 0
    rw [projection_word hz r, if_neg hrs]
  exact hle hv

/-- Homogeneous bar subspaces with distinct counts have zero intersection. -/
theorem weight_disjoint (n : ℕ) {r s : ℕ} (hrs : r ≠ s) :
    Disjoint (weight k D X N n r) (weight k D X N n s) := by
  rw [Submodule.disjoint_def]
  intro v hr hs
  rw [← projection_self hr, projection_other hrs hs]


variable (k D X N)

/-- Expanding each actual algebra entry as D ⊕ X spans every absolute bar term. -/
theorem all_words_span (n : ℕ) :
    Submodule.span k {v : term k (TrivSqZeroExt D X) N n |
      ∃ r, Word k D X N n r v} = ⊤ := by
  induction n with
  | zero =>
    apply top_unique
    intro v _
    exact Submodule.subset_span ⟨0, Word.nil v⟩
  | succ n ih =>
    apply top_unique
    intro v _
    induction v using TensorProduct.inductionOn with
    | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)
    | tmul a v =>
      let T := Submodule.span k {w : term k (TrivSqZeroExt D X) N (n+1) |
        ∃ r, Word k D X N (n+1) r w}
      let g := TensorProduct.mk k (TrivSqZeroExt D X) (term k (TrivSqZeroExt D X) N n) a
      have hle : Submodule.span k {w | ∃ r, Word k D X N n r w} ≤ T.comap g := by
        apply Submodule.span_le.mpr
        rintro w ⟨r, hw⟩
        change a ⊗ₜ[k] w ∈ T
        rw [← inl_fst_add_inr_snd_eq a, TensorProduct.add_tmul]
        exact Submodule.add_mem _
          (Submodule.subset_span ⟨r, Word.base a.fst hw⟩)
          (Submodule.subset_span ⟨r+1, Word.ideal a.snd hw⟩)
      apply hle
      rw [ih]
      trivial

/-- Every value of the count projection lies in the corresponding homogeneous subspace. -/
theorem projection_mem (n r : ℕ) (v : term k (TrivSqZeroExt D X) N n) :
    projection k D X N n r v ∈ weight k D X N n r := by
  have hle : Submodule.span k {w | ∃ s, Word k D X N n s w} ≤
      (weight k D X N n r).comap (projection k D X N n r) := by
    apply Submodule.span_le.mpr
    rintro w ⟨s, hw⟩
    change projection k D X N n r w ∈ weight k D X N n r
    rw [projection_word hw r]
    split_ifs with h
    · subst s
      exact Submodule.subset_span hw
    · exact Submodule.zero_mem _
  apply hle
  rw [all_words_span]
  trivial

/-- The count subspaces span the entire bar term. -/
theorem weight_iSup (n : ℕ) : (⨆ r, weight k D X N n r) = ⊤ := by
  apply top_unique
  rw [← all_words_span k D X N n]
  apply Submodule.span_le.mpr
  rintro v ⟨r, hr⟩
  exact (le_iSup (fun r => weight k D X N n r) r) (Submodule.subset_span hr)
end DerivedBar.SquareZero

end

end OAI

end

section

namespace OAI
open scoped TensorProduct DirectSum
open TensorProduct CategoryTheory TrivSqZeroExt
noncomputable section

namespace DerivedBar.SquareZero
universe u

private theorem internal_of_projections {R V : Type u} [Ring R] [AddCommGroup V] [Module R V]
    (S : ℕ → Submodule R V) (p : ℕ → Module.End R V)
    (hself : ∀ r v, v ∈ S r → p r v = v)
    (hother : ∀ r s, r ≠ s → ∀ v, v ∈ S s → p r v = 0)
    (htop : iSup S = ⊤) : DirectSum.IsInternal S := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top _ htop
  intro r
  rw [Submodule.disjoint_def]
  intro v hv hrest
  have hle : (⨆ (s : ℕ) (_ : s ≠ r), S s) ≤ (p r).ker := by
    refine iSup_le fun s => iSup_le fun hs => ?_
    intro w hw
    exact hother r s (Ne.symm hs) w hw
  have hz := hle hrest
  change p r v = 0 at hz
  rwa [hself r v hv] at hz

variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]

/-- The homogeneous absolute bar term is an internal direct sum. -/
theorem weight_internal (n : ℕ) : DirectSum.IsInternal (weight k D X N n) :=
  internal_of_projections _ (projection k D X N n)
    (fun _ _ h => projection_self h) (fun _ _ h _ hv => projection_other h hv)
    (weight_iSup k D X N n)

/-- Actual D-linear count projection on the two-sided bar term. -/
def twoSidedProjection (n r : ℕ) : Module.End D (D ⊗[k] term k (TrivSqZeroExt D X) N n) :=
  AlgebraTensorModule.lTensor D D (projection k D X N n r)

@[simp] theorem twoSidedProjection_tmul (n r : ℕ) (d : D)
    (v : term k (TrivSqZeroExt D X) N n) :
    twoSidedProjection k D X N n r (d ⊗ₜ[k] v) = d ⊗ₜ[k] projection k D X N n r v := rfl

variable {k D X N}

theorem twoSidedProjection_self {n r : ℕ}
    {v : D ⊗[k] term k (TrivSqZeroExt D X) N n} (hv : v ∈ twoSidedWeight k D X N n r) :
    twoSidedProjection k D X N n r v = v := by
  have hle : twoSidedWeight k D X N n r ≤
      (twoSidedProjection k D X N n r - LinearMap.id).ker := by
    apply Submodule.span_le.mpr
    rintro w ⟨d, z, hz, rfl⟩
    change d ⊗ₜ[k] projection k D X N n r z - d ⊗ₜ[k] z = 0
    rw [projection_word hz r, if_pos rfl, sub_self]
  have hz := hle hv
  change twoSidedProjection k D X N n r v - v = 0 at hz
  exact sub_eq_zero.mp hz

theorem twoSidedProjection_other {n r s : ℕ} (hrs : r ≠ s)
    {v : D ⊗[k] term k (TrivSqZeroExt D X) N n} (hv : v ∈ twoSidedWeight k D X N n s) :
    twoSidedProjection k D X N n r v = 0 := by
  have hle : twoSidedWeight k D X N n s ≤ (twoSidedProjection k D X N n r).ker := by
    apply Submodule.span_le.mpr
    rintro w ⟨d, z, hz, rfl⟩
    change d ⊗ₜ[k] projection k D X N n r z = 0
    rw [projection_word hz r, if_neg hrs, TensorProduct.tmul_zero]
  exact hle hv

variable (k D X N)

/-- Expansion of internal A entries as D ⊕ X spans the two-sided bar term as a D-module. -/
theorem twoSidedWeight_iSup (n : ℕ) : (⨆ r, twoSidedWeight k D X N n r) = ⊤ := by
  apply top_unique
  intro v hv
  clear hv
  induction v using TensorProduct.inductionOn with
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul d v =>
    let T := (⨆ r, twoSidedWeight k D X N n r)
    let g := TensorProduct.mk k D (term k (TrivSqZeroExt D X) N n) d
    have hle : Submodule.span k {w | ∃ r, Word k D X N n r w} ≤
        (T.restrictScalars k).comap g := by
      apply Submodule.span_le.mpr
      rintro w ⟨r, hw⟩
      exact (le_iSup (twoSidedWeight k D X N n) r)
        (Submodule.subset_span ⟨d, w, hw, rfl⟩)
    apply hle
    rw [all_words_span]
    trivial

/-- The genuine D-module decomposition of each two-sided bar term by X-count. -/
theorem twoSidedWeight_internal (n : ℕ) : DirectSum.IsInternal (twoSidedWeight k D X N n) :=
  internal_of_projections _ (twoSidedProjection k D X N n)
    (fun _ _ h => twoSidedProjection_self h)
    (fun _ _ h _ hv => twoSidedProjection_other h hv)
    (twoSidedWeight_iSup k D X N n)

/-- Canonical sum of homogeneous tensors, as a linear equivalence. -/
def twoSidedWeightEquiv (n : ℕ) :
    (⨁ r : ℕ, twoSidedWeight k D X N n r) ≃ₗ[D]
      D ⊗[k] term k (TrivSqZeroExt D X) N n :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap _) (twoSidedWeight_internal k D X N n)
end DerivedBar.SquareZero

end

end OAI

end

section

namespace OAI
open scoped TensorProduct DirectSum
open TensorProduct CategoryTheory TrivSqZeroExt
noncomputable section

namespace DerivedBar
universe u

/-- The direct sum of module chain complexes, with the componentwise actual differential. -/
def directSumComplex {R : Type u} [Ring R] (C : ℕ → ChainComplex (ModuleCat R) ℕ) :
    ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of R (⨁ r, (C r).X n))
    (fun n => ModuleCat.ofHom (DirectSum.lmap (fun r => ((C r).d (n+1) n).hom)))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      apply DFinsupp.ext
      intro r
      exact LinearMap.congr_fun
        (ModuleCat.hom_ext_iff.mp ((C r).d_comp_d (n+1+1) (n+1) n)) (z r))

namespace SquareZero
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]
  [Module (TrivSqZeroExt D X) N] [IsScalarTower k (TrivSqZeroExt D X) N]
variable (hN : ∀ (x : X) (v : N), (inr x : TrivSqZeroExt D X) • v = 0)

/-- Chain-level count splitting of the actual two-sided absolute bar complex.
This is the first chain isomorphism in the proof of manuscript prop:bar-splitting.
Identification of these summands with derived tensor iterates is a separate dependency. -/
def countSplitting :
    directSumComplex (twoSidedWeightComplex k D X N hN) ≅
      twoSidedComplex k (TrivSqZeroExt D X) D N (fstHom k D X) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (twoSidedWeightEquiv k D X N n).toModuleIso)
    (by
      intro i j hij
      change j+1 = i at hij
      subst i
      apply ModuleCat.hom_ext
      apply DirectSum.linearMap_ext
      intro r
      apply LinearMap.ext
      intro v
      simp only [directSumComplex, twoSidedComplex, ChainComplex.of_d,
        ModuleCat.hom_comp, ModuleCat.hom_ofHom, twoSidedWeightEquiv]
      change twoSidedDifferential k (TrivSqZeroExt D X) D N (fstHom k D X) j
          (DirectSum.coeLinearMap (twoSidedWeight k D X N (j+1))
            (DirectSum.lof D ℕ _ r v)) =
        DirectSum.coeLinearMap (twoSidedWeight k D X N j)
          (DirectSum.lmap (fun r => ((twoSidedWeightComplex k D X N hN r).d (j+1) j).hom)
            (DirectSum.lof D ℕ _ r v))
      rw [DirectSum.lmap_lof]
      erw [DirectSum.coeLinearMap_lof, DirectSum.coeLinearMap_lof]
      simp only [twoSidedWeightComplex, ChainComplex.of_d, ModuleCat.hom_ofHom]
      rfl)
end SquareZero
end DerivedBar

end

end OAI

end

section

namespace OAI
open scoped TensorProduct DirectSum
open TensorProduct CategoryTheory TrivSqZeroExt
noncomputable section

namespace DerivedBar
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
variable (f : A →ₐ[k] D)

/-- The balanced free-tensor equivalence respects arbitrary A-linear maps, including bar faces. -/
theorem freeEquiv_natural (V W : Type u) [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (h : A ⊗[k] V →ₗ[A] A ⊗[k] W) :
    (Balanced.descend f W).comp (Balanced.map f (A ⊗[k] V) (A ⊗[k] W) h) =
      (FreeBaseChange.map f V W h).comp (Balanced.descend f V) := by
  apply (Balanced.relations f (A ⊗[k] V)).linearMap_qext
  apply AlgebraTensorModule.ext
  intro d z
  change d • FreeBaseChange.coefficient f W (h z) =
    FreeBaseChange.map f V W h (d • FreeBaseChange.coefficient f V z)
  rw [LinearMap.map_smul, FreeBaseChange.map_coefficient]

variable (k A D N : Type u) [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
  [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
variable (f : A →ₐ[k] D)

/-- The actual balanced tensor of D with every term and differential of the verified bar resolution. -/
def tensorBarComplex : ChainComplex (ModuleCat D) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of D (Balanced.tensor f (term k A N (n+1))))
    (fun n => ModuleCat.ofHom (Balanced.map f _ _ (differential k A N (n+1))))
    (fun n => by
      apply ModuleCat.hom_ext
      change (Balanced.map f _ _ (differential k A N (n+1))).comp
        (Balanced.map f _ _ (differential k A N (n+1+1))) = 0
      rw [← Balanced.map_comp, differential_sq, Balanced.map_zero])

/-- The explicit two-sided bar is isomorphic to balanced tensor applied to a genuine projective resolution. -/
def tensorBarIso : tensorBarComplex k A D N f ≅ twoSidedComplex k A D N f :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (Balanced.freeEquiv f (term k A N n)).toModuleIso)
    (by
      intro i j hij
      change j+1 = i at hij
      subst i
      apply ModuleCat.hom_ext
      simp only [tensorBarComplex, twoSidedComplex, ChainComplex.of_d,
        ModuleCat.hom_comp, ModuleCat.hom_ofHom]
      exact (freeEquiv_natural f (term k A N (j+1)) (term k A N j)
        (differential k A N (j+1))).symm)

namespace SquareZero
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]
  [Module (TrivSqZeroExt D X) N] [IsScalarTower k (TrivSqZeroExt D X) N]

/-- The tensor of the actual free resolution splits by X-count as a D-module chain complex.
The identification of count r with the shifted r-fold derived tensor remains separate. -/
def tensorCountSplitting
    (hN : ∀ (x : X) (v : N), (inr x : TrivSqZeroExt D X) • v = 0) :
    tensorBarComplex k (TrivSqZeroExt D X) D N (fstHom k D X) ≅
      directSumComplex (twoSidedWeightComplex k D X N hN) :=
  tensorBarIso k (TrivSqZeroExt D X) D N (fstHom k D X) ≪≫
    (countSplitting k D X N hN).symm

end SquareZero
end DerivedBar

end

end OAI

end

section

namespace OAI
open scoped TensorProduct
open TensorProduct
noncomputable section

namespace DerivedBar.BimoduleTensor
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [IsScalarTower k D X]
variable (V : Type u) [AddCommGroup V] [Module k V] [Module D V] [IsScalarTower k D V]

/-- Noncommutative balancing relations for an arbitrary (D,D)-bimodule X. -/
def relations : Submodule D (X ⊗[k] V) :=
  Submodule.span D {z | ∃ (x : X) (d : D) (v : V),
    z = (MulOpposite.op d • x) ⊗ₜ[k] v - x ⊗ₜ[k] (d • v)}

/-- Genuine balanced X ⊗_D V, with its exterior left D-action. -/
abbrev tensor := (X ⊗[k] V) ⧸ relations k D X V

def quotient : X ⊗[k] V →ₗ[D] tensor k D X V := (relations k D X V).mkQ

omit [IsScalarTower k D V] in
theorem balanced (x : X) (d : D) (v : V) :
    quotient k D X V ((MulOpposite.op d • x) ⊗ₜ[k] v) =
      quotient k D X V (x ⊗ₜ[k] (d • v)) := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨x, d, v, rfl⟩)

section Maps
variable (W U : Type u) [AddCommGroup W] [Module k W] [Module D W] [IsScalarTower k D W]
  [AddCommGroup U] [Module k U] [Module D U] [IsScalarTower k D U]

theorem map_relations (h : V →ₗ[D] W) : relations k D X V ≤
    ((quotient k D X W).comp (AlgebraTensorModule.lTensor D X (h.restrictScalars k))).ker := by
  apply Submodule.span_le.mpr
  rintro z ⟨x, d, v, rfl⟩
  change quotient k D X W ((AlgebraTensorModule.lTensor D X (h.restrictScalars k))
    ((MulOpposite.op d • x) ⊗ₜ[k] v - x ⊗ₜ[k] (d • v))) = 0
  simp only [map_sub, AlgebraTensorModule.lTensor_tmul, LinearMap.coe_restrictScalars,
    LinearMap.map_smul]
  rw [balanced, sub_self]

def map (h : V →ₗ[D] W) : tensor k D X V →ₗ[D] tensor k D X W :=
  (relations k D X V).liftQ
    ((quotient k D X W).comp (AlgebraTensorModule.lTensor D X (h.restrictScalars k)))
    (map_relations k D X V W h)

@[simp] theorem map_quotient (h : V →ₗ[D] W) (x : X) (v : V) :
    map k D X V W h (quotient k D X V (x ⊗ₜ[k] v)) =
      quotient k D X W (x ⊗ₜ[k] h v) := rfl

theorem map_comp (h : V →ₗ[D] W) (g : W →ₗ[D] U) :
    map k D X V U (g.comp h) = (map k D X W U g).comp (map k D X V W h) := by
  apply (relations k D X V).linearMap_qext
  apply AlgebraTensorModule.ext
  intro x v
  rfl

@[simp] theorem map_zero : map k D X V W 0 = 0 := by
  apply (relations k D X V).linearMap_qext
  apply AlgebraTensorModule.ext
  intro x v
  change quotient k D X W (x ⊗ₜ[k] (0 : W)) = 0
  rw [TensorProduct.tmul_zero, _root_.map_zero]

@[simp] theorem map_id : map k D X V V LinearMap.id = LinearMap.id := by
  apply (relations k D X V).linearMap_qext
  apply AlgebraTensorModule.ext
  intro x v
  rfl

theorem map_add (h g : V →ₗ[D] W) :
    map k D X V W (h+g) = map k D X V W h + map k D X V W g := by
  apply (relations k D X V).linearMap_qext
  apply AlgebraTensorModule.ext
  intro x v
  change quotient k D X W (x ⊗ₜ[k] (h v + g v)) =
    quotient k D X W (x ⊗ₜ[k] h v) + quotient k D X W (x ⊗ₜ[k] g v)
  rw [TensorProduct.tmul_add, _root_.map_add]
end Maps

variable [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k Dᵐᵒᵖ X]

/-- The bimodule right action, bilinear over the field. -/
def rightMul : X →ₗ[k] D →ₗ[k] X where
  toFun x :=
    { toFun := fun d => MulOpposite.op d • x
      map_add' := by intro a b; simp [add_smul]
      map_smul' := by intro c d; simp [MulOpposite.op_smul, smul_assoc] }
  map_add' := by intro x y; ext d; simp [smul_add]
  map_smul' := by intro c x; ext d; simp [smul_comm (MulOpposite.op d) c]

/-- Multiplication X ⊗_k D → X respects the arbitrary exterior D-action. -/
def rightAction : X ⊗[k] D →ₗ[D] X :=
  { (TensorProduct.lift (rightMul k D X)).toAddHom with
    map_smul' := by
      intro a z
      induction z using TensorProduct.inductionOn with
      | tmul x d =>
        change (TensorProduct.lift (rightMul k D X)) (a • (x ⊗ₜ[k] d)) =
          a • ((TensorProduct.lift (rightMul k D X)) (x ⊗ₜ[k] d))
        rw [TensorProduct.smul_tmul']
        exact (smul_comm a (MulOpposite.op d) x).symm
      | add v w hv hw => simp_all [smul_add] }

@[simp] theorem rightAction_tmul (x : X) (d : D) :
    rightAction k D X (x ⊗ₜ[k] d) = MulOpposite.op d • x := rfl

variable (W : Type u) [AddCommGroup W] [Module k W]

/-- Collapse the first two slots using the right D-action on X. -/
def collapse : X ⊗[k] (D ⊗[k] W) →ₗ[D] X ⊗[k] W :=
  { ((TensorProduct.map ((rightAction k D X).restrictScalars k) LinearMap.id).comp
      (TensorProduct.assoc k X D W).symm.toLinearMap).toAddHom with
    map_smul' := by
      intro a z
      induction z using TensorProduct.inductionOn with
      | tmul x v =>
        induction v using TensorProduct.inductionOn with
        | tmul d w =>
          rw [TensorProduct.smul_tmul']
          change (MulOpposite.op d • (a • x)) ⊗ₜ[k] w =
            a • ((MulOpposite.op d • x) ⊗ₜ[k] w)
          rw [TensorProduct.smul_tmul', ← smul_comm a (MulOpposite.op d) x]
        | add v w hv hw => simp_all [TensorProduct.tmul_add, smul_add]
      | add v w hv hw => simp_all [smul_add] }

@[simp] theorem collapse_tmul (x : X) (d : D) (w : W) :
    collapse k D X W (x ⊗ₜ[k] (d ⊗ₜ[k] w)) = (MulOpposite.op d • x) ⊗ₜ[k] w := rfl

/-- The collapse descends through the actual balancing relations. -/
theorem relations_le_ker_collapse : relations k D X (D ⊗[k] W) ≤ (collapse k D X W).ker := by
  apply Submodule.span_le.mpr
  rintro z ⟨x, d, v, rfl⟩
  change collapse k D X W ((MulOpposite.op d • x) ⊗ₜ[k] v - x ⊗ₜ[k] (d • v)) = 0
  induction v using TensorProduct.inductionOn with
  | tmul a w =>
    rw [_root_.map_sub, collapse_tmul, TensorProduct.smul_tmul', smul_eq_mul, collapse_tmul]
    simp [← mul_smul, ← MulOpposite.op_mul]
  | add v w hv hw =>
    simp only [TensorProduct.tmul_add, smul_add, _root_.map_sub, _root_.map_add] at *
    rw [sub_eq_zero.mp hv, sub_eq_zero.mp hw, sub_self]

def descend : tensor k D X (D ⊗[k] W) →ₗ[D] X ⊗[k] W :=
  (relations k D X (D ⊗[k] W)).liftQ (collapse k D X W) (relations_le_ker_collapse k D X W)

def insert : X ⊗[k] W →ₗ[D] tensor k D X (D ⊗[k] W) :=
  (quotient k D X (D ⊗[k] W)).comp
    (AlgebraTensorModule.lTensor D X (TensorProduct.mk k D W 1))

@[simp] theorem descend_quotient (z : X ⊗[k] (D ⊗[k] W)) :
    descend k D X W (quotient k D X (D ⊗[k] W) z) = collapse k D X W z := rfl

omit [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k Dᵐᵒᵖ X] in
@[simp] theorem insert_tmul (x : X) (w : W) :
    insert k D X W (x ⊗ₜ[k] w) = quotient k D X (D ⊗[k] W) (x ⊗ₜ[k] (1 ⊗ₜ[k] w)) := rfl

theorem descend_insert : (descend k D X W).comp (insert k D X W) = LinearMap.id := by
  apply AlgebraTensorModule.ext
  intro x w
  simp only [LinearMap.comp_apply, insert_tmul, descend_quotient, collapse_tmul,
    MulOpposite.op_one, one_smul, LinearMap.id_apply]

theorem insert_descend : (insert k D X W).comp (descend k D X W) = LinearMap.id := by
  apply (relations k D X (D ⊗[k] W)).linearMap_qext
  apply AlgebraTensorModule.ext
  intro x v
  induction v using TensorProduct.inductionOn with
  | tmul d w =>
    change insert k D X W (collapse k D X W (x ⊗ₜ[k] (d ⊗ₜ[k] w))) =
      quotient k D X (D ⊗[k] W) (x ⊗ₜ[k] (d ⊗ₜ[k] w))
    rw [collapse_tmul, insert_tmul, balanced]
    simp [TensorProduct.smul_tmul']
  | add v w hv hw => simp_all [TensorProduct.tmul_add]

/-- Genuine X ⊗_D (D ⊗_k W) ≅ X ⊗_k W, with no flatness of X. -/
def freeEquiv : tensor k D X (D ⊗[k] W) ≃ₗ[D] X ⊗[k] W :=
  LinearEquiv.ofLinearMap (descend k D X W) (insert k D X W)
    (descend_insert k D X W) (insert_descend k D X W)
end DerivedBar.BimoduleTensor

end

end OAI

end

section

namespace OAI
open scoped TensorProduct
open TensorProduct CategoryTheory
noncomputable section

namespace DerivedBar.BimoduleTensor
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]

section FreeMaps
variable (V W U : Type u) [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]

/-- Balanced tensor on a map of free modules, in the explicit field-tensor coordinates. -/
def freeMap (h : D ⊗[k] V →ₗ[D] D ⊗[k] W) : X ⊗[k] V →ₗ[D] X ⊗[k] W :=
  (descend k D X W).comp ((map k D X _ _ h).comp (insert k D X V))

/-- Coordinate change commutes with every free-module differential. -/
theorem freeMap_descend (h : D ⊗[k] V →ₗ[D] D ⊗[k] W)
    (z : tensor k D X (D ⊗[k] V)) :
    freeMap k D X V W h (descend k D X V z) =
      descend k D X W (map k D X _ _ h z) := by
  change descend k D X W (map k D X _ _ h (insert k D X V (descend k D X V z))) = _
  rw [show insert k D X V (descend k D X V z) = z from
    LinearMap.congr_fun (insert_descend k D X V) z]

theorem freeMap_comp (h : D ⊗[k] V →ₗ[D] D ⊗[k] W)
    (g : D ⊗[k] W →ₗ[D] D ⊗[k] U) :
    freeMap k D X V U (g.comp h) =
      (freeMap k D X W U g).comp (freeMap k D X V W h) := by
  apply LinearMap.ext
  intro z
  change descend k D X U (map k D X _ _ (g.comp h) (insert k D X V z)) =
    freeMap k D X W U g (descend k D X W (map k D X _ _ h (insert k D X V z)))
  rw [freeMap_descend, map_comp]
  rfl

@[simp] theorem freeMap_zero : freeMap k D X V W 0 = 0 := by
  apply LinearMap.ext
  intro z
  simp only [freeMap, LinearMap.comp_apply, map_zero, LinearMap.zero_apply, _root_.map_zero]
end FreeMaps

variable (N : Type u) [AddCommGroup N] [Module k N] [Module D N] [IsScalarTower k D N]

/-- The two-sided bar differential for arbitrary bimodule coefficients X. -/
def barDifferential (n : ℕ) : X ⊗[k] DerivedBar.term k D N (n+1) →ₗ[D]
    X ⊗[k] DerivedBar.term k D N n :=
  freeMap k D X _ _ (DerivedBar.differential k D N (n+1))

/-- Independent endpoint-minus-tail formula, including the noncommutative right action. -/
theorem barDifferential_tmul (n : ℕ) (x : X) (z : DerivedBar.term k D N (n+1)) :
    barDifferential k D X N n (x ⊗ₜ[k] z) =
      collapse k D X (DerivedBar.term k D N n) (x ⊗ₜ[k] z) -
        x ⊗ₜ[k] DerivedBar.differential k D N n z := by
  change descend k D X (DerivedBar.term k D N n)
    (map k D X _ _ (DerivedBar.differential k D N (n+1))
      (insert k D X (DerivedBar.term k D N (n+1)) (x ⊗ₜ[k] z))) = _
  rw [insert_tmul, map_quotient, DerivedBar.differential_succ_tmul, one_smul,
    TensorProduct.tmul_sub, _root_.map_sub, _root_.map_sub,
    descend_quotient, descend_quotient, collapse_tmul, MulOpposite.op_one, one_smul]

theorem barDifferential_sq (n : ℕ) :
    (barDifferential k D X N n).comp (barDifferential k D X N (n+1)) = 0 := by
  unfold barDifferential
  rw [← freeMap_comp, DerivedBar.differential_sq, freeMap_zero]

/-- Balanced X tensor of the actual free projective resolution of N. -/
def tensorResolution : ChainComplex (ModuleCat D) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of D (tensor k D X (DerivedBar.term k D N (n+1))))
    (fun n => ModuleCat.ofHom (map k D X _ _ (DerivedBar.differential k D N (n+1))))
    (fun n => by
      apply ModuleCat.hom_ext
      change (map k D X _ _ (DerivedBar.differential k D N (n+1))).comp
        (map k D X _ _ (DerivedBar.differential k D N (n+1+1))) = 0
      rw [← map_comp, DerivedBar.differential_sq, map_zero])

/-- The explicit two-sided X,D,N bar complex, with no D-flatness assumption. -/
def barComplex : ChainComplex (ModuleCat D) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of D (X ⊗[k] DerivedBar.term k D N n))
    (fun n => ModuleCat.ofHom (barDifferential k D X N n))
    (fun n => ModuleCat.hom_ext (barDifferential_sq k D X N n))

/-- The explicit two-sided bar is isomorphic to genuine balanced tensor of the free resolution. -/
def tensorResolutionIso : tensorResolution k D X N ≅ barComplex k D X N :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (freeEquiv k D X (DerivedBar.term k D N n)).toModuleIso)
    (by
      intro i j hij
      change j+1 = i at hij
      subst i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      simp only [tensorResolution, barComplex, ChainComplex.of_d,
        ModuleCat.hom_comp, ModuleCat.hom_ofHom,
        LinearEquiv.toModuleIso_hom]
      exact freeMap_descend k D X (DerivedBar.term k D N (j+1))
        (DerivedBar.term k D N j) (DerivedBar.differential k D N (j+1)) z)
end DerivedBar.BimoduleTensor

end

end OAI

end

section

namespace OAI
open CategoryTheory
noncomputable section

namespace DerivedBar.BimoduleTensor
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]

/-- The canonical field action on a left D-module. -/
abbrev scalarModule (V : ModuleCat.{u} D) : Module k V := Module.compHom V (algebraMap k D)

local instance (V : ModuleCat.{u} D) : Module k V := scalarModule k D V
local instance (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

/-- Actual balanced tensor by the arbitrary bimodule X, as an additive endofunctor. -/
def tensorFunctor : ModuleCat.{u} D ⥤ ModuleCat.{u} D where
  obj V := ModuleCat.of D (tensor k D X V)
  map h := ModuleCat.ofHom (map k D X _ _ h.hom)
  map_id V := ModuleCat.hom_ext (map_id k D X V)
  map_comp h g := ModuleCat.hom_ext (map_comp k D X _ _ _ h.hom g.hom)

instance tensorFunctor_additive : (tensorFunctor k D X).Additive where
  map_add := by
    intro V W h g
    exact ModuleCat.hom_ext (map_add k D X _ _ h.hom g.hom)

/-- Tensor of X with the verified absolute bar projective resolution.
This construction applies the genuine balanced functor to every differential. -/
def resolvedTensor (N : ModuleCat.{u} D) : ChainComplex (ModuleCat.{u} D) ℕ :=
  ((tensorFunctor k D X).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (DerivedBar.projectiveResolution k D N).complex

/-- The explicit projective bar resolution computes actual derived tensor on modules,
via mathlib's left derived functor to the homotopy category.
Extension to bounded-above complexes and repeated totalization remains separate. -/
def barComputesDerivedTensor (N : ModuleCat.{u} D) :
    (tensorFunctor k D X).leftDerivedToHomotopyCategory.obj N ≅
      (HomotopyCategory.quotient (ModuleCat.{u} D) (ComplexShape.down ℕ)).obj
        (resolvedTensor k D X N) :=
  (DerivedBar.projectiveResolution k D N).isoLeftDerivedToHomotopyCategoryObj
    (tensorFunctor k D X)
end DerivedBar.BimoduleTensor

end

end OAI

end

section

namespace OAI
open CategoryTheory
noncomputable section

namespace DerivedBar.BimoduleTensor
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]

/-- Canonical scalar restriction agrees with every supplied compatible field action. -/
theorem scalarModule_eq (V : Type u) [AddCommGroup V] [Module k V]
    [Module D V] [IsScalarTower k D V] :
    scalarModule k D (ModuleCat.of D V) = (inferInstance : Module k V) := by
  apply Module.ext
  funext c v
  exact IsScalarTower.algebraMap_smul D c v

/-- Coherence between the categorical tensor functor and the literal balancing quotient. -/
def tensorFunctorObjIso (V : Type u) [AddCommGroup V] [Module k V]
    [Module D V] [IsScalarTower k D V] :
    (tensorFunctor k D X).obj (ModuleCat.of D V) ≅ ModuleCat.of D (tensor k D X V) := by
  have h := scalarModule_eq k D V
  cases h
  exact Iso.refl _

omit [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k Dᵐᵒᵖ X] in
/-- The scalar-action coherence is natural for every D-linear map. -/
theorem tensorFunctorObjIso_natural (V W : Type u)
    [AddCommGroup V] [Module k V] [Module D V] [IsScalarTower k D V]
    [AddCommGroup W] [Module k W] [Module D W] [IsScalarTower k D W]
    (h : V →ₗ[D] W) :
    (tensorFunctor k D X).map (ModuleCat.ofHom h) ≫ (tensorFunctorObjIso k D X W).hom =
      (tensorFunctorObjIso k D X V).hom ≫ ModuleCat.ofHom (map k D X V W h) := by
  have hV := scalarModule_eq k D V
  have hW := scalarModule_eq k D W
  cases hV
  cases hW
  rfl

local instance (V : ModuleCat.{u} D) : Module k V := scalarModule k D V
local instance (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

/-- The categorical derived-resolution model and the explicit balanced bar complex agree. -/
def resolvedTensorIso (N : ModuleCat.{u} D) :
    resolvedTensor k D X N ≅ tensorResolution k D X N :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => tensorFunctorObjIso k D X (DerivedBar.term k D N (n+1)))
    (by
      intro i j hij
      change j+1 = i at hij
      subst i
      simp only [tensorResolution, resolvedTensor, DerivedBar.projectiveResolution,
        DerivedBar.complex, ChainComplex.of_d, Functor.mapHomologicalComplex_obj_d]
      exact (tensorFunctorObjIso_natural k D X (DerivedBar.term k D N (j+1+1))
        (DerivedBar.term k D N (j+1)) (DerivedBar.differential k D N (j+1))).symm)

/-- The literal arbitrary-bimodule two-sided bar computes genuine derived tensor of a module.
There is no flatness assumption or ordinary tensor-power replacement. -/
def explicitBarComputesDerivedTensor (N : ModuleCat.{u} D) :
    (tensorFunctor k D X).leftDerivedToHomotopyCategory.obj N ≅
      (HomotopyCategory.quotient (ModuleCat.{u} D) (ComplexShape.down ℕ)).obj
        (barComplex k D X N) :=
  barComputesDerivedTensor k D X N ≪≫
    (HomotopyCategory.quotient (ModuleCat.{u} D) (ComplexShape.down ℕ)).mapIso
      (resolvedTensorIso k D X N ≪≫ tensorResolutionIso k D X N)

/-- Actual left-derived tensor homology (Tor), computed by the explicit two-sided bar. -/
def barHomologyIso (N : ModuleCat.{u} D) (i : ℕ) :
    ((tensorFunctor k D X).leftDerived i).obj N ≅
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} D) (ComplexShape.down ℕ) i).obj
        (barComplex k D X N) :=
  (DerivedBar.projectiveResolution k D N).isoLeftDerivedObj (tensorFunctor k D X) i ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} D) (ComplexShape.down ℕ) i).mapIso
      (resolvedTensorIso k D X N ≪≫ tensorResolutionIso k D X N)
end DerivedBar.BimoduleTensor

end

end OAI

end

section

namespace OAI
open CategoryTheory TensorProduct
open scoped TensorProduct
noncomputable section
namespace DerivedBar.Balanced
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
  (f : A →ₐ[k] D)

local instance (V : ModuleCat.{u} A) : Module k V := BimoduleTensor.scalarModule k A V
local instance (V : ModuleCat.{u} A) : IsScalarTower k A V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

def tensorFunctor : ModuleCat.{u} A ⥤ ModuleCat.{u} D where
  obj V := ModuleCat.of D (tensor f V)
  map h := ModuleCat.ofHom (map f _ _ h.hom)
  map_id V := ModuleCat.hom_ext (map_id f V)
  map_comp h g := ModuleCat.hom_ext (map_comp f _ _ _ h.hom g.hom)

instance tensorFunctor_additive : (tensorFunctor f).Additive where
  map_add := by
    intro V W h g
    apply ModuleCat.hom_ext
    apply (relations f V).linearMap_qext
    apply AlgebraTensorModule.ext
    intro d v
    change quotient f W (d ⊗ₜ[k] (h.hom v + g.hom v)) =
      quotient f W (d ⊗ₜ[k] h.hom v) + quotient f W (d ⊗ₜ[k] g.hom v)
    rw [TensorProduct.tmul_add, map_add]

def tensorFunctorObjIso (V : Type u) [AddCommGroup V] [Module k V]
    [Module A V] [IsScalarTower k A V] :
    (tensorFunctor f).obj (ModuleCat.of A V) ≅ ModuleCat.of D (tensor f V) := by
  have h := BimoduleTensor.scalarModule_eq k A V
  cases h
  exact Iso.refl _

theorem tensorFunctorObjIso_natural (V W : Type u)
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    (h : V →ₗ[A] W) :
    (tensorFunctor f).map (ModuleCat.ofHom h) ≫ (tensorFunctorObjIso f W).hom =
      (tensorFunctorObjIso f V).hom ≫ ModuleCat.ofHom (map f V W h) := by
  have hV := BimoduleTensor.scalarModule_eq k A V
  have hW := BimoduleTensor.scalarModule_eq k A W
  cases hV
  cases hW
  rfl

variable (N : Type u) [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

def resolvedTensorIso :
    ((tensorFunctor f).mapHomologicalComplex (.down ℕ)).obj
      (DerivedBar.projectiveResolution k A N).complex ≅ tensorBarComplex k A D N f :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => tensorFunctorObjIso f (DerivedBar.term k A N (n+1)))
    (by
      intro i j hij
      change j+1=i at hij
      subst i
      simp only [tensorBarComplex, DerivedBar.projectiveResolution,
        DerivedBar.complex, ChainComplex.of_d, Functor.mapHomologicalComplex_obj_d]
      exact (tensorFunctorObjIso_natural f (DerivedBar.term k A N (j+1+1))
          (DerivedBar.term k A N (j+1)) (DerivedBar.differential k A N (j+1))).symm)

/-- The left-derived balanced tensor functor is computed by exactly the
original tensorBarComplex, via the proved free bar projective resolution. -/
def tensorBarComputesLeftDerived :
    (tensorFunctor f).leftDerivedToHomotopyCategory.obj (ModuleCat.of A N) ≅
      (HomotopyCategory.quotient (ModuleCat.{u} D) (.down ℕ)).obj (tensorBarComplex k A D N f) :=
  (DerivedBar.projectiveResolution k A N).isoLeftDerivedToHomotopyCategoryObj (tensorFunctor f) ≪≫
    (HomotopyCategory.quotient (ModuleCat.{u} D) (.down ℕ)).mapIso (resolvedTensorIso f N)

def tensorBarHomologyIso (i : ℕ) :
    ((tensorFunctor f).leftDerived i).obj (ModuleCat.of A N) ≅
      (tensorBarComplex k A D N f).homology i :=
  (DerivedBar.projectiveResolution k A N).isoLeftDerivedObj (tensorFunctor f) i ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} D) (.down ℕ) i).mapIso (resolvedTensorIso f N)
end DerivedBar.Balanced

end

end OAI

end

section
namespace OAI.DerivedBar.Induction
open CategoryTheory TensorProduct
open scoped TensorProduct
noncomputable section
universe u
variable {k R S : Type u} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
variable (i : R →ₐ[k] S)
local instance {B : Type u} [Ring B] [Algebra k B] (V : ModuleCat.{u} B) : Module k V := BimoduleTensor.scalarModule k B V
local instance {B : Type u} [Ring B] [Algebra k B] (V : ModuleCat.{u} B) : IsScalarTower k B V := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
variable {V : ModuleCat.{u} R} {N : ModuleCat.{u} S}
def unit (V : ModuleCat.{u} R) : V ⟶ ((ModuleCat.restrictScalars i.toRingHom)).obj (((Balanced.tensorFunctor i)).obj V) := by
  constructor
  refine {
  toFun v := Balanced.quotient i V ((1:S) ⊗ₜ[k] v)
  map_add' := by intro a b; rw [tmul_add,_root_.map_add]; rfl
  map_smul' := by
    intro r v
    change Balanced.quotient i V (1 ⊗ₜ[k] (r • v)) = i r • Balanced.quotient i V (1 ⊗ₜ[k] v)
    rw [← Balanced.balanced, ← LinearMap.map_smul, smul_tmul', smul_eq_mul, one_mul, mul_one] }

def fieldMap (h : V ⟶ ((ModuleCat.restrictScalars i.toRingHom)).obj N) : V →ₗ[k] N where
  toFun := h.hom
  map_add' := h.hom.map_add
  map_smul' c v := by
    have hh := h.hom.map_smul (algebraMap k R c) v
    change h.hom (_ • v) = i (algebraMap k R c) • (h.hom v : N) at hh
    change h.hom (algebraMap k R c • v) = algebraMap k S c • (h.hom v : N)
    rwa [i.commutes] at hh

def extend (h : V ⟶ ((ModuleCat.restrictScalars i.toRingHom)).obj N) : ((Balanced.tensorFunctor i)).obj V ⟶ N := ModuleCat.ofHom <|
  (Balanced.relations i V).liftQ ((action k S N).comp (AlgebraTensorModule.lTensor S S (fieldMap i h))) (by
    apply Submodule.span_le.mpr
    rintro _ ⟨s,r,v,rfl⟩
    change _ = 0
    simp only [LinearMap.comp_apply, _root_.map_sub, AlgebraTensorModule.lTensor_tmul, action_tmul]
    apply sub_eq_zero.mpr
    exact (mul_smul _ _ _).trans (congrArg (s • ·) (h.hom.map_smul r v).symm))

theorem extend_unit (h : V ⟶ ((ModuleCat.restrictScalars i.toRingHom)).obj N) : unit i V ≫ ((ModuleCat.restrictScalars i.toRingHom)).map (extend i h) = h := by
  ext v
  change (1:S) • (h.hom v : N) = _
  rw [one_smul]

theorem from_ext (f g : ((Balanced.tensorFunctor i)).obj V ⟶ N) (e : unit i V ≫ ((ModuleCat.restrictScalars i.toRingHom)).map f = unit i V ≫ ((ModuleCat.restrictScalars i.toRingHom)).map g) : f = g := by
  apply ModuleCat.hom_ext
  apply (Balanced.relations i V).linearMap_qext
  apply AlgebraTensorModule.ext
  intro s v
  have h := ModuleCat.hom_ext_iff.mp e
  have hv := LinearMap.congr_fun h v
  change f.hom (Balanced.quotient i V (s ⊗ₜ[k] v)) = g.hom (Balanced.quotient i V (s ⊗ₜ[k] v))
  have hs : s ⊗ₜ[k] v = s • ((1:S) ⊗ₜ[k] v) := by rw [smul_tmul',smul_eq_mul,mul_one]
  rw [hs, LinearMap.map_smul]
  exact (f.hom.map_smul s _).trans ((congrArg (s • ·) hv).trans (g.hom.map_smul s _).symm)

theorem projective (V : ModuleCat.{u} R) [Projective V] : Projective (((Balanced.tensorFunctor i)).obj V) where
  factors {E B} f p hp := by
    letI : Epi (((ModuleCat.restrictScalars i.toRingHom)).map p) := (ModuleCat.epi_iff_surjective _).mpr ((ModuleCat.epi_iff_surjective p).mp hp)
    let h := Projective.factorThru (unit i V ≫ ((ModuleCat.restrictScalars i.toRingHom)).map f) (((ModuleCat.restrictScalars i.toRingHom)).map p)
    refine ⟨extend i h, from_ext i _ _ ?_⟩
    rw [Functor.map_comp, ← Category.assoc, extend_unit]
    exact Projective.factorThru_comp _ _

end
end OAI.DerivedBar.Induction

end

section

namespace OAI
noncomputable section
namespace LittleFinitistic.PDSquareZero
open Submodule
universe u
variable {A D : Type u} [Ring A] [Ring D]

/-- A square-zero ideal lies in the actual noncommutative Jacobson radical. -/
theorem squareZero_le_jacobson (I : Ideal A)
    (hI : ∀ a ∈ I, ∀ b ∈ I, a*b=0) : I ≤ Ring.jacobson A := by
  apply le_sInf
  intro L hL
  by_contra hn
  have hlt : L < L ⊔ I := lt_of_le_of_ne le_sup_left (fun he => hn (he ▸ le_sup_right))
  have htop : L ⊔ I = ⊤ := hL.2 _ hlt
  have hone : (1 : A) ∈ L ⊔ I := htop.symm ▸ mem_top
  obtain ⟨l, hl, x, hx, hlx⟩ := Submodule.mem_sup.mp hone
  have hxx : x*x=0 := hI x hx x hx
  have hleq : l=1-x := eq_sub_iff_add_eq.mpr hlx
  have heq : (1+x)*l=1 := by
    simp [hleq, mul_sub, add_mul, hxx]
  have h1 : (1 : A) ∈ L := heq ▸ L.smul_mem (1+x) hl
  exact hL.1 (Ideal.eq_top_of_isUnit_mem L h1 isUnit_one)

/-- A surjection with square-zero kernel pulls back the ring radical exactly. -/
theorem comap_jacobson (f : A →+* D) (hf : Function.Surjective f)
    (hsq : ∀ a ∈ RingHom.ker f, ∀ b ∈ RingHom.ker f, a*b=0) :
    Ideal.comap f (Ring.jacobson D) = Ring.jacobson A := by
  let : RingHomSurjective f := ⟨hf⟩
  exact Module.comap_jacobson_of_ker_le (f := f.toSemilinearMap) hf
    (squareZero_le_jacobson (RingHom.ker f) hsq)

variable {k : Type u} [Field k] [Algebra k D]
variable (X : Type u) [AddCommGroup X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [Module k X]
  [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]

/-- The manuscript's actual split square-zero projection has square-zero kernel. -/
theorem kernel_square_zero (a b : TrivSqZeroExt D X)
    (ha : a ∈ RingHom.ker (TrivSqZeroExt.fstHom k D X).toRingHom)
    (hb : b ∈ RingHom.ker (TrivSqZeroExt.fstHom k D X).toRingHom) : a*b=0 := by
  have ha0 : a.fst=0 := ha
  have hb0 : b.fst=0 := hb
  apply TrivSqZeroExt.ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, ha0, hb0]

/-- rad(D ⋉ X) is the preimage of rad(D), hence consists precisely of pairs
whose D coordinate is in rad(D). The X coordinate is unrestricted. -/
theorem radical_eq_comap :
    Ring.jacobson (TrivSqZeroExt D X) =
      Ideal.comap (TrivSqZeroExt.fstHom k D X).toRingHom (Ring.jacobson D) := by
  symm
  apply comap_jacobson
  · intro d; exact ⟨TrivSqZeroExt.inl d, rfl⟩
  · exact fun a ha b hb => kernel_square_zero X a b ha hb

/-- Every simple A-module is annihilated by the square-zero ideal, as used
when identifying the simple modules with those over D. -/
theorem square_zero_ideal_le_radical :
    RingHom.ker (TrivSqZeroExt.fstHom k D X).toRingHom ≤ Ring.jacobson (TrivSqZeroExt D X) :=
  squareZero_le_jacobson _ (fun a ha b hb => kernel_square_zero X a b ha hb)
end LittleFinitistic.PDSquareZero

end

end OAI

end

section

namespace OAI
noncomputable section
namespace LittleFinitistic.PDSquareZero
universe u
variable {A D : Type u} [Ring A] [Ring D]

/-- The radical quotient is unchanged by a square-zero kernel. -/
def residueQuotientEquiv (f : A →+* D) (hf : Function.Surjective f)
    (hsq : ∀ a ∈ RingHom.ker f, ∀ b ∈ RingHom.ker f, a*b=0) :
    A ⧸ Ring.jacobson A ≃+* D ⧸ Ring.jacobson D := by
  let g := (Ideal.Quotient.mk (Ring.jacobson D)).comp f
  have hk : RingHom.ker g = Ring.jacobson A := by
    ext a
    change Ideal.Quotient.mk (Ring.jacobson D) (f a) = 0 ↔ a ∈ Ring.jacobson A
    rw [Ideal.Quotient.eq_zero_iff_mem]
    change a ∈ Ideal.comap f (Ring.jacobson D) ↔ _
    rw [comap_jacobson f hf hsq]
  exact (Ideal.quotEquivOfEq hk.symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := g) (Ideal.Quotient.mk_surjective.comp hf))

@[simp] theorem residueQuotientEquiv_mk (f : A →+* D) (hf : Function.Surjective f)
    (hsq : ∀ a ∈ RingHom.ker f, ∀ b ∈ RingHom.ker f, a*b=0) (a : A) :
    residueQuotientEquiv f hf hsq (Ideal.Quotient.mk (Ring.jacobson A) a) =
      Ideal.Quotient.mk (Ring.jacobson D) (f a) := by
  simp [residueQuotientEquiv]

/-- The nilpotent ideal annihilates every actual simple left A-module. -/
theorem kernel_annihilates_simple (f : A →+* D)
    (hsq : ∀ a ∈ RingHom.ker f, ∀ b ∈ RingHom.ker f, a*b=0)
    (S : Type u) [AddCommGroup S] [Module A S] [IsSimpleModule A S]
    (a : A) (ha : a ∈ RingHom.ker f) (s : S) : a • s=0 :=
  Module.mem_annihilator.mp
    (IsSemisimpleModule.jacobson_le_annihilator A S
      (squareZero_le_jacobson (RingHom.ker f) hsq ha)) s

variable {k : Type u} [Field k] [Algebra k D]
variable (X : Type u) [AddCommGroup X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [Module k X]
  [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]

/-- The exact quotient-ring isomorphism S in Section 6. -/
def squareZeroResidueEquiv :
    TrivSqZeroExt D X ⧸ Ring.jacobson (TrivSqZeroExt D X) ≃+* D ⧸ Ring.jacobson D :=
  residueQuotientEquiv (TrivSqZeroExt.fstHom k D X).toRingHom
    (fun d => ⟨TrivSqZeroExt.inl d, rfl⟩)
    (fun a ha b hb => kernel_square_zero X a b ha hb)

@[simp] theorem squareZeroResidueEquiv_mk (a : TrivSqZeroExt D X) :
    squareZeroResidueEquiv (k := k) X (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk (Ring.jacobson D) a.fst := residueQuotientEquiv_mk _ _ _ _
end LittleFinitistic.PDSquareZero

end

end OAI

end

section

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.BalancedTensor
universe u v w w' z
variable (k : Type u) [Field k] (A : Type v) [Ring A]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M]
variable (N : Type w') [AddCommGroup N] [Module k N] [Module A N]

/-- Balancing relations for a right A-module and a left A-module, over k. -/
def relations : Submodule k (M ⊗[k] N) := Submodule.span k
  (Set.range fun q : A × M × N =>
    (MulOpposite.op q.1 • q.2.1) ⊗ₜ[k] q.2.2 - q.2.1 ⊗ₜ[k] (q.1 • q.2.2))

/-- Tensor over the possibly noncommutative algebra A. -/
abbrev Tensor := (M ⊗[k] N) ⧸ relations k A M N

def mk : M →ₗ[k] N →ₗ[k] Tensor k A M N :=
  (TensorProduct.mk k M N).compr₂ (relations k A M N).mkQ

variable {k A M N}

theorem balance (a : A) (m : M) (n : N) :
    mk k A M N (MulOpposite.op a • m) n = mk k A M N m (a • n) := by
  apply sub_eq_zero.mp
  change (relations k A M N).mkQ ((MulOpposite.op a • m) ⊗ₜ[k] n) -
    (relations k A M N).mkQ (m ⊗ₜ[k] (a • n)) = 0
  rw [← map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (Submodule.subset_span ⟨(a,m,n),rfl⟩)

variable {V : Type z} [AddCommGroup V] [Module k V]

/-- Universal property for k-bilinear maps satisfying the actual A-balancing equation. -/
def lift (f : M →ₗ[k] N →ₗ[k] V)
    (hf : ∀ (a : A) m n, f (MulOpposite.op a • m) n = f m (a • n)) : Tensor k A M N →ₗ[k] V :=
  (relations k A M N).liftQ (TensorProduct.lift f) (by
    rw [relations, Submodule.span_le]
    rintro _ ⟨⟨a,m,n⟩,rfl⟩
    change TensorProduct.lift f ((MulOpposite.op a • m) ⊗ₜ[k] n - m ⊗ₜ[k] (a • n)) = 0
    simp only [map_sub, TensorProduct.lift.tmul, hf, sub_self])

@[simp] theorem lift_mk (f : M →ₗ[k] N →ₗ[k] V)
    (hf : ∀ (a : A) m n, f (MulOpposite.op a • m) n = f m (a • n)) (m : M) (n : N) :
    lift f hf (mk k A M N m n) = f m n := rfl

theorem induction_on {C : Tensor k A M N → Prop} (x : Tensor k A M N)
    (hz : C 0) (ht : ∀ m n, C (mk k A M N m n))
    (ha : ∀ a b, C a → C b → C (a+b)) : C x := by
  classical
  by_cases zero_tensor : x = 0
  · simpa [zero_tensor] using hz
  clear zero_tensor
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    induction x using TensorProduct.inductionOn with
    | tmul m n => exact ht m n
    | add a b h₁ h₂ => exact ha _ _ h₁ h₂

theorem ext {f g : Tensor k A M N →ₗ[k] V}
    (h : ∀ m n, f (mk k A M N m n) = g (mk k A M N m n)) : f = g := by
  apply LinearMap.ext
  intro x
  induction x using induction_on with
  | hz => simp
  | ht m n => exact h m n
  | ha a b h₁ h₂ => simp [h₁,h₂]
end LittleFinitistic.BalancedTensor

end

end OAI

end

section

namespace OAI
noncomputable section
namespace LittleFinitistic.PDTensor
open LinearMap Submodule
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable (U : Type u) [AddCommGroup U] [Module k U] [Module Aᵐᵒᵖ U]
variable {M N : Type u} [AddCommGroup M] [Module k M] [Module A M]
  [IsScalarTower k A M] [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

def mapRight (f : M →ₗ[A] N) : BalancedTensor.Tensor k A U M →ₗ[k]
    BalancedTensor.Tensor k A U N :=
  BalancedTensor.lift
    ((BalancedTensor.mk k A U N).compl₁₂ LinearMap.id (f.restrictScalars k)) (by
      intro a u m
      change BalancedTensor.mk k A U N (MulOpposite.op a • u) (f m) =
        BalancedTensor.mk k A U N u (f (a • m))
      rw [f.map_smul, BalancedTensor.balance])

@[simp] theorem mapRight_mk (f : M →ₗ[A] N) (u : U) (m : M) :
    mapRight (k := k) U f (BalancedTensor.mk k A U M u m) =
      BalancedTensor.mk k A U N u (f m) := rfl

omit [Algebra k A] [IsScalarTower k A N] in
/-- Radical multiplication is killed by tensor with any right module
annihilated by the ring radical. -/
theorem mk_radical_zero
    (hU : ∀ a ∈ Ring.jacobson A, ∀ u : U, MulOpposite.op a • u = 0)
    (n : N) (hn : n ∈ Ring.jacobson A • (⊤ : Submodule A N)) (u : U) :
    BalancedTensor.mk k A U N u n = 0 := by
  let K : Submodule A N :=
    { carrier := {n | ∀ u : U, BalancedTensor.mk k A U N u n = 0}
      zero_mem' := fun u => map_zero _
      add_mem' := fun hx hy u => by rw [map_add, hx, hy, add_zero]
      smul_mem' := fun a x hx u => by rw [← BalancedTensor.balance]; exact hx _ }
  have hK : Ring.jacobson A • (⊤ : Submodule A N) ≤ K := by
    apply Submodule.smul_le.mpr
    intro a ha x _ u
    rw [← BalancedTensor.balance, hU a ha u]
    exact LinearMap.congr_fun (map_zero (BalancedTensor.mk k A U N)) x
  exact hK hn u

theorem mapRight_radical_zero
    (hU : ∀ a ∈ Ring.jacobson A, ∀ u : U, MulOpposite.op a • u = 0)
    (f : M →ₗ[A] N)
    (hf : LinearMap.range f ≤ Ring.jacobson A • (⊤ : Submodule A N)) :
    mapRight (k := k) U f = 0 := by
  apply BalancedTensor.ext
  intro u m
  exact mk_radical_zero (k := k) U hU (f m) (hf (mem_range_self f m)) u

/-- The actual right radical quotient of the regular module. -/
def rightRadical : Submodule Aᵐᵒᵖ A where
  carrier := Ring.jacobson A
  zero_mem' := (Ring.jacobson A).zero_mem
  add_mem' := (Ring.jacobson A).add_mem
  smul_mem' b _ ha := (Ring.jacobson A).mul_mem_right b.unop ha

abbrev Residue := A ⧸ (rightRadical (A := A))

theorem residue_annihilated (a : A) (ha : a ∈ Ring.jacobson A) (s : Residue (A := A)) :
    MulOpposite.op a • s = 0 := by
  induction s using Submodule.Quotient.induction_on with
  | _ b =>
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact (Ring.jacobson A).mul_mem_left b ha
end LittleFinitistic.PDTensor

end

end OAI

end

section

namespace OAI
noncomputable section
namespace LittleFinitistic.PDRadical
open Module LinearMap Submodule
universe u v
variable {A : Type u} [Ring A]
variable (P : Type v) [AddCommGroup P] [Module A P]

/-- For a finitely generated projective module the module radical is exactly
multiplication by the ring Jacobson radical. No commutativity is assumed. -/
theorem jacobson_eq_smul [Module.Finite A P] [Module.Projective A P] :
    Module.jacobson A P = Ring.jacobson A • (⊤ : Submodule A P) := by
  apply le_antisymm _ (Ring.jacobson_smul_top_le A P)
  intro x hx
  obtain ⟨n, f, g, hf, hg, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A P
  have hcoord (i : Fin n) : g x i ∈ Ring.jacobson A :=
    Module.le_comap_jacobson ((LinearMap.proj i).comp g) hx
  have hsum : g x = ∑ i : Fin n, Pi.single i (g x i) := by
    classical
    ext j
    simp
  have hxsum : x = ∑ i : Fin n, (g x i) • f (Pi.single i 1) := by
    classical
    calc
      x = f (g x) := (DFunLike.congr_fun hfg x).symm
      _ = ∑ i : Fin n, f (Pi.single i (g x i)) := by conv_lhs => rw [hsum, map_sum]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        have he : Pi.single i (g x i) = (g x i) • (Pi.single i 1 : Fin n → A) := by
          ext j
          by_cases hj : i = j
          · subst j; simp
          · simp [Ne.symm hj]
        rw [he, map_smul]
  rw [hxsum]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hcoord i) mem_top

/-- The noncommutative Nakayama step used in the manuscript. -/
theorem quotient_radical_nontrivial [Module.Finite A P] [Nontrivial P] :
    Nontrivial (P ⧸ (Ring.jacobson A • (⊤ : Submodule A P))) := by
  apply Submodule.Quotient.nontrivial_iff.mpr
  exact ne_of_lt (Submodule.jacobson_smul_lt_top (R := A) (M := P) ⊤)

/-- Any map into a simple module annihilates the radical of its domain. -/
theorem simple_map_radical_zero
    {S : Type v} [AddCommGroup S] [Module A S] [IsSimpleModule A S]
    (f : P →ₗ[A] S) (x : P) (hx : x ∈ Module.jacobson A P) : f x = 0 := by
  have h := Module.le_comap_jacobson f hx
  have hs : Module.jacobson A S = ⊥ := by
    apply bot_unique
    exact sInf_le isCoatom_bot
  simpa [hs] using h
end LittleFinitistic.PDRadical

end

end OAI

end

section

namespace OAI
noncomputable section
namespace LittleFinitistic.PDTensor
open LinearMap Submodule
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable (N : Type u) [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

abbrev radicalProduct := Ring.jacobson A • (⊤ : Submodule A N)
abbrev Top := N ⧸ radicalProduct (A := A) N

def residuePair : Residue (A := A) →ₗ[k] N →ₗ[k] Top (A := A) N := by
  let f : A →ₗ[k] N →ₗ[k] Top (A := A) N :=
    { toFun := fun a =>
        { toFun := fun n => (radicalProduct N).mkQ (a • n)
          map_add' := fun x y => by simp [smul_add]
          map_smul' := fun c n => by simp [smul_comm a c] }
      map_add' := fun a b => by ext n; simp [add_smul]
      map_smul' := fun c a => by ext n; simp [smul_assoc] }
  exact ((rightRadical (A := A)).restrictScalars k).liftQ f (by
    intro a ha
    ext n
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact Submodule.smul_mem_smul ha mem_top)

@[simp] theorem residuePair_mk (a : A) (n : N) :
    residuePair (k := k) N (Submodule.Quotient.mk a) n =
      (radicalProduct N).mkQ (a • n) := rfl

def residueEval : BalancedTensor.Tensor k A (Residue (A := A)) N →ₗ[k] Top (A := A) N :=
  BalancedTensor.lift (residuePair (k := k) N) (by
    intro a s n
    induction s using Submodule.Quotient.induction_on with
    | _ b => change (radicalProduct N).mkQ ((b*a) • n) = _; rw [mul_smul]; rfl)

def residueInverse : Top (A := A) N →ₗ[k] BalancedTensor.Tensor k A (Residue (A := A)) N :=
  ((radicalProduct (A := A) N).restrictScalars k).liftQ
    (BalancedTensor.mk k A (Residue (A := A)) N (Submodule.Quotient.mk (1 : A))) (by
      intro n hn
      exact mk_radical_zero (k := k) (Residue (A := A)) residue_annihilated n hn _)

@[simp] theorem residueEval_mk (a : A) (n : N) :
    residueEval (k := k) N (BalancedTensor.mk k A (Residue (A := A)) N
      (Submodule.Quotient.mk a) n) = (radicalProduct N).mkQ (a • n) := rfl

@[simp] theorem residueInverse_mk (n : N) :
    residueInverse (k := k) N ((radicalProduct N).mkQ n) =
      BalancedTensor.mk k A (Residue (A := A)) N (Submodule.Quotient.mk (1 : A)) n := rfl

/-- The actual noncommutative tensor/quotient identification in cor:pd-detection. -/
def residueTensorEquiv : BalancedTensor.Tensor k A (Residue (A := A)) N ≃ₗ[k] Top (A := A) N where
  __ := residueEval (k := k) N
  invFun := residueInverse (k := k) N
  left_inv z := by
    change residueInverse (k := k) N (residueEval (k := k) N z) = z
    induction z using BalancedTensor.induction_on with
    | hz => simp
    | ht s n =>
      induction s using Submodule.Quotient.induction_on with
      | _ a =>
        rw [residueEval_mk, residueInverse_mk, ← BalancedTensor.balance]
        congr 2
        change Submodule.Quotient.mk ((1 : A)*a) = Submodule.Quotient.mk a
        rw [one_mul]
    | ha x y hx hy => simp [hx,hy]
  right_inv z := by
    induction z using Submodule.Quotient.induction_on with
    | _ n =>
      change residueEval (k := k) N (residueInverse (k := k) N ((radicalProduct N).mkQ n)) = _
      rw [residueInverse_mk, residueEval_mk, one_smul]
      rfl

/-- Nakayama proves tensor detection for every finitely generated nonzero module. -/
theorem residueTensor_nontrivial [Module.Finite A N] [Nontrivial N] :
    Nontrivial (BalancedTensor.Tensor k A (Residue (A := A)) N) := by
  have := PDRadical.quotient_radical_nontrivial (A := A) N
  exact (residueTensorEquiv (k := k) N).toEquiv.nontrivial
end LittleFinitistic.PDTensor

end

end OAI

end

section

namespace OAI
noncomputable section
namespace LittleFinitistic.PDTensor
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

/-- The right-module quotient used by tensor detection is the underlying
vector space of the usual quotient ring A/rad A. -/
def residueRingEquiv : Residue (A := A) ≃ₗ[k] A ⧸ Ring.jacobson A :=
  LinearEquiv.refl k _
end LittleFinitistic.PDTensor

end

end OAI

end

section

namespace OAI
noncomputable section
namespace LittleFinitistic.PDTensor
open CategoryTheory
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]

abbrev ScalarModule (M : ModuleCat.{u} A) :=
  (ModuleCat.restrictScalars (algebraMap k A)).obj M

instance scalarModuleTower (M : ModuleCat.{u} A) :
    IsScalarTower k A (ScalarModule k A M) where
  smul_assoc c a m := by
    change (c • a) • (m : M) = algebraMap k A c • (a • (m : M))
    rw [Algebra.smul_def, mul_smul]

variable (U : Type u) [AddCommGroup U] [Module k U] [Module Aᵐᵒᵖ U]

/-- Tensor with a fixed right module, on actual left modules over A. -/
def tensorFunctor : ModuleCat.{u} A ⥤ ModuleCat.{u} k where
  obj M := ModuleCat.of k (BalancedTensor.Tensor k A U (ScalarModule k A M))
  map {M N} f := ModuleCat.ofHom
    (mapRight (k := k) (M := ScalarModule k A M) (N := ScalarModule k A N) U f.hom)
  map_id M := by apply ModuleCat.hom_ext; apply BalancedTensor.ext; intros; rfl
  map_comp f g := by apply ModuleCat.hom_ext; apply BalancedTensor.ext; intros; rfl

instance tensorFunctorAdditive : (tensorFunctor k A U).Additive where
  map_add := by
    intro M N f g
    apply ModuleCat.hom_ext
    apply BalancedTensor.ext
    intro u m
    exact map_add (BalancedTensor.mk k A U (ScalarModule k A N) u) (f.hom m) (g.hom m)
end LittleFinitistic.PDTensor

end

end OAI

end

section

namespace OAI
noncomputable section
namespace LittleFinitistic.PDCovers
open Module LinearMap Submodule
universe u v
variable {A : Type u} [Ring A]
variable {E N : Type v} [AddCommGroup E] [Module A E]
  [AddCommGroup N] [Module A N]

/-- An epimorphism is right minimal if every endomorphism over it is surjective. -/
def RightMinimal (p : E →ₗ[A] N) : Prop :=
  ∀ f : Module.End A E, p.comp f = p → Function.Surjective f

lemma comp_pow_eq {p : E →ₗ[A] N} {f : Module.End A E}
    (h : p.comp f = p) (n : ℕ) : p.comp (f ^ n) = p := by
  induction n with
  | zero => ext x; rfl
  | succ n ih => rw [pow_succ, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ih, h]

/-- Fitting decomposition upgrades minimality among projective submodules to
right minimality of an actual epimorphism. -/
theorem rightMinimal_of_minimal [IsArtinian A E] [IsNoetherian A E]
    (p : E →ₗ[A] N) (S : Submodule A E)
    (hS : Minimal (fun T : Submodule A E =>
      Module.Projective A T ∧ Function.Surjective (p.comp T.subtype)) S) :
    RightMinimal (p.comp S.subtype) := by
  have : Module.Projective A S := hS.1.1
  intro f hf
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp f.eventually_isCompl_ker_pow_range_pow
  let r := f ^ (n+1)
  have hc : IsCompl (LinearMap.range r) (LinearMap.ker r) :=
    (hn (n+1) (by omega)).symm
  let R := LinearMap.range r
  have : Module.Projective A R := Module.Projective.of_split R.subtype
    (R.projectionOnto (LinearMap.ker r) hc) (Submodule.projectionOnto_comp_subtype hc)
  let T := R.map S.subtype
  let i : R →ₗ[A] E := S.subtype.comp R.subtype
  have hi : Function.Injective i := S.injective_subtype.comp R.injective_subtype
  have he : LinearMap.range i = T := by simp [i, T, LinearMap.range_comp]
  let e : R ≃ₗ[A] T := (LinearEquiv.ofInjective i hi).trans (LinearEquiv.ofEq _ _ he)
  have : Module.Projective A T := Module.Projective.of_equiv e
  have hpr : (p.comp S.subtype).comp r = p.comp S.subtype := comp_pow_eq hf _
  have hTsurj : Function.Surjective (p.comp T.subtype) := by
    intro y
    obtain ⟨x, hx⟩ := hS.1.2 y
    refine ⟨⟨S.subtype (r x), ⟨r x, mem_range_self r x, rfl⟩⟩, ?_⟩
    exact (DFunLike.congr_fun hpr x).trans hx
  have hTS : T ≤ S := by
    rintro x ⟨z, hz, rfl⟩
    exact z.property
  have hST : S ≤ T := hS.2 ⟨inferInstance, hTsurj⟩ hTS
  have hr : Function.Surjective r := by
    intro x
    obtain ⟨z, ⟨w, hw⟩, hz⟩ := hST x.property
    refine ⟨w, ?_⟩
    exact hw.trans (Subtype.ext hz)
  intro x
  obtain ⟨y, hy⟩ := hr x
  refine ⟨(f ^ n) y, ?_⟩
  simpa [r, pow_succ', Module.End.mul_eq_comp] using hy

/-- Every projective epimorphism from a finite-length module contains a
projective cover. This proves existence rather than assuming covers. -/
theorem exists_rightMinimal [IsArtinian A E] [IsNoetherian A E]
    [Module.Projective A E] (p : E →ₗ[A] N) (hp : Function.Surjective p) :
    ∃ S : Submodule A E, Module.Projective A S ∧
      Function.Surjective (p.comp S.subtype) ∧ RightMinimal (p.comp S.subtype) := by
  have : Module.Projective A (⊤ : Submodule A E) :=
    Module.Projective.of_equiv (Submodule.topEquiv : (⊤ : Submodule A E) ≃ₗ[A] E).symm
  obtain ⟨S, hS⟩ := WellFoundedLT.exists_minimal (inferInstance : WellFoundedLT (Submodule A E))
    {T : Submodule A E | Module.Projective A T ∧ Function.Surjective (p.comp T.subtype)}
    ⟨⊤, inferInstance, fun y => by obtain ⟨x, hx⟩ := hp y; exact ⟨⟨x, mem_top⟩, hx⟩⟩
  exact ⟨S, hS.1.1, hS.1.2, rightMinimal_of_minimal p S hS⟩
end LittleFinitistic.PDCovers

end

end OAI

end

section

namespace OAI
noncomputable section
namespace LittleFinitistic.PDCovers
open Module LinearMap Submodule
universe u
variable {A : Type u} [Ring A]
variable {E N : Type u} [AddCommGroup E] [Module A E]
  [AddCommGroup N] [Module A N]

/-- A projective right-minimal epimorphism has a superfluous kernel. -/
theorem eq_top_of_sup_ker [Module.Projective A E]
    (p : E →ₗ[A] N) (hp : Function.Surjective p) (hm : RightMinimal p)
    (L : Submodule A E) (hL : L ⊔ LinearMap.ker p = ⊤) : L = ⊤ := by
  have hsurj : Function.Surjective (p.comp L.subtype) := by
    intro y
    obtain ⟨x, hx⟩ := hp y
    have hm : x ∈ L ⊔ LinearMap.ker p := hL.symm ▸ mem_top
    obtain ⟨z, hz, w, hw, hzw⟩ := Submodule.mem_sup.mp hm
    refine ⟨⟨z, hz⟩, ?_⟩
    have hw0 : p w = 0 := hw
    change p z = y
    rw [← hx, ← hzw, map_add, hw0, add_zero]
  obtain ⟨g, hg⟩ := Module.projective_lifting_property (p.comp L.subtype) p hsurj
  have hfg : p.comp (L.subtype.comp g) = p := by rwa [← LinearMap.comp_assoc]
  have hfgsurj := hm (L.subtype.comp g) hfg
  apply top_unique
  intro x _
  obtain ⟨z, hz⟩ := hfgsurj x
  rw [← hz]
  exact (g z).property

/-- Projective-cover kernels lie in the actual module Jacobson radical. -/
theorem ker_le_jacobson [Module.Projective A E]
    (p : E →ₗ[A] N) (hp : Function.Surjective p) (hm : RightMinimal p) :
    LinearMap.ker p ≤ Module.jacobson A E := by
  apply le_sInf
  intro L hL
  by_contra h
  have hlt : L < L ⊔ LinearMap.ker p := lt_of_le_of_ne le_sup_left (fun he => h (he ▸ le_sup_right))
  have htop : L ⊔ LinearMap.ker p = ⊤ := hL.2 _ hlt
  exact hL.1 (eq_top_of_sup_ker p hp hm L htop)

/-- Over a finite-dimensional algebra every finite-dimensional module has an
actual finitely generated projective cover, constructed inside a finite free module. -/
theorem exists_finite_projective_cover
    {k : Type u} [Field k] [Algebra k A] [FiniteDimensional k A]
    [Module k N] [IsScalarTower k A N] [FiniteDimensional k N] :
    ∃ (n : ℕ) (S : Submodule A (Fin n → A)) (p : S →ₗ[A] N),
      Module.Projective A S ∧ Function.Surjective p ∧
      RightMinimal p ∧ LinearMap.ker p ≤ Module.jacobson A S := by
  have : Module.Finite A N := Module.Finite.of_restrictScalars_finite k A N
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' A N
  have : IsArtinian A (Fin n → A) := isArtinian_of_tower k inferInstance
  have : IsNoetherian A (Fin n → A) := isNoetherian_of_tower k inferInstance
  obtain ⟨S, hS, hs, hm⟩ := exists_rightMinimal p hp
  have := hS
  exact ⟨n, S, p.comp S.subtype, hS, hs, hm, ker_le_jacobson _ hs hm⟩
end LittleFinitistic.PDCovers

end

end OAI

end

section

namespace OAI
noncomputable section
namespace LittleFinitistic.PDMinimal
open Module LinearMap Submodule
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]

/-- Finite-dimensional actual left modules, retaining the scalar compatibility. -/
structure FiniteModule where
  carrier : Type u
  [add : AddCommGroup carrier]
  [moduleA : Module A carrier]
  [moduleK : Module k carrier]
  [tower : IsScalarTower k A carrier]
  [finite : FiniteDimensional k carrier]
instance (M : FiniteModule k A) : AddCommGroup M.carrier := M.add
instance (M : FiniteModule k A) : Module A M.carrier := M.moduleA
instance (M : FiniteModule k A) : Module k M.carrier := M.moduleK
instance (M : FiniteModule k A) : IsScalarTower k A M.carrier := M.tower
instance (M : FiniteModule k A) : FiniteDimensional k M.carrier := M.finite
instance : CoeSort (FiniteModule k A) (Type u) := ⟨FiniteModule.carrier⟩

namespace FiniteModule
variable {k A}
abbrev of (M : Type u) [AddCommGroup M] [Module A M] [Module k M]
    [IsScalarTower k A M] [FiniteDimensional k M] : FiniteModule k A := ⟨M⟩
def cat (M : FiniteModule k A) : ModuleCat A := ModuleCat.of A M
instance (M : FiniteModule k A) : Module.Finite A M :=
  Module.Finite.of_restrictScalars_finite k A M
end FiniteModule

variable [FiniteDimensional k A]
/-- Projective covers with their actual maps and radical-kernel property. -/
structure Cover (M : FiniteModule k A) where
  source : FiniteModule k A
  [projective : Module.Projective A source]
  π : source →ₗ[A] M
  surjective : Function.Surjective π
  minimal : PDCovers.RightMinimal π
  radical : LinearMap.ker π ≤ Ring.jacobson A • (⊤ : Submodule A source)
instance {M : FiniteModule k A} (c : Cover k A M) : Module.Projective A c.source := c.projective

variable {k A}
theorem cover_nonempty (M : FiniteModule k A) : Nonempty (Cover k A M) := by
  obtain ⟨n, S, p, hP, hp, hm, hr⟩ := PDCovers.exists_finite_projective_cover (k := k) (A := A) (N := M)
  have := hP
  have : FiniteDimensional k S := Module.Finite.of_injective
    (S.subtype.restrictScalars k) S.injective_subtype
  have : Module.Finite A S := Module.Finite.of_restrictScalars_finite k A S
  refine ⟨⟨FiniteModule.of S, p, hp, hm, ?_⟩⟩
  exact hr.trans (PDRadical.jacobson_eq_smul S).le

def cover (M : FiniteModule k A) : Cover k A M := Classical.choice (cover_nonempty M)

abbrev next (M : FiniteModule k A) : FiniteModule k A := by
  have : FiniteDimensional k (LinearMap.ker (cover M).π) :=
    Module.Finite.of_injective ((LinearMap.ker (cover M).π).subtype.restrictScalars k)
      (Submodule.injective_subtype _)
  exact FiniteModule.of (LinearMap.ker (cover M).π)

abbrev syzygy (M : FiniteModule k A) : ℕ → FiniteModule k A
  | 0 => M
  | n+1 => next (syzygy M n)

abbrev term (M : FiniteModule k A) (n : ℕ) := (cover (syzygy M n)).source
abbrev augment (M : FiniteModule k A) (n : ℕ) := (cover (syzygy M n)).π

def differential (M : FiniteModule k A) (n : ℕ) : term M (n+1) →ₗ[A] term M n :=
  (LinearMap.ker (augment M n)).subtype.comp (augment M (n+1))

@[simp] theorem augment_differential (M : FiniteModule k A) (n : ℕ) :
    (augment M n).comp (differential M n) = 0 := by
  ext x
  exact (augment M (n+1) x).property

@[simp] theorem differential_comp (M : FiniteModule k A) (n : ℕ) :
    (differential M n).comp (differential M (n+1)) = 0 := by
  rw [differential, LinearMap.comp_assoc, augment_differential, LinearMap.comp_zero]

theorem range_differential (M : FiniteModule k A) (n : ℕ) :
    LinearMap.range (differential M n) = LinearMap.ker (augment M n) := by
  rw [differential, LinearMap.range_comp, LinearMap.range_eq_top.mpr (cover _).surjective,
    Submodule.map_top, Submodule.range_subtype]

theorem ker_differential (M : FiniteModule k A) (n : ℕ) :
    LinearMap.ker (differential M n) = LinearMap.ker (augment M (n+1)) := by
  ext x
  change ((augment M (n+1) x : LinearMap.ker (augment M n)) : term M n) = 0 ↔
    augment M (n+1) x = 0
  constructor
  · intro h; exact Subtype.ext h
  · intro h; exact congrArg (fun z : LinearMap.ker (augment M n) => z.val) h

theorem exact_differential (M : FiniteModule k A) (n : ℕ) :
    LinearMap.range (differential M (n+1)) = LinearMap.ker (differential M n) := by
  rw [range_differential, ker_differential]

theorem differential_radical (M : FiniteModule k A) (n : ℕ) :
    LinearMap.range (differential M n) ≤
      Ring.jacobson A • (⊤ : Submodule A (term M n)) := by
  rw [range_differential]
  exact (cover _).radical
end LittleFinitistic.PDMinimal

end

end OAI

end

section

namespace OAI
noncomputable section
namespace LittleFinitistic.PDMinimal
open CategoryTheory CategoryTheory.Limits
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (M : FiniteModule k A)

/-- The actual chain complex of the successive projective covers. -/
def complex : ChainComplex (ModuleCat A) ℕ := ChainComplex.of
  (fun n => (term M n).cat)
  (fun n => ModuleCat.ofHom (differential M n))
  (fun n => ModuleCat.hom_ext (differential_comp M n))

@[simp] theorem complex_d (n : ℕ) :
    (complex M).d (n+1) n = ModuleCat.ofHom (differential M n) := by
  exact ChainComplex.of_d (fun n => (term M n).cat)
    (fun n => ModuleCat.ofHom (differential M n)) n

instance term_projective (n : ℕ) : Projective ((complex M).X n) := by
  exact (IsProjective.iff_projective _).mp (cover (syzygy M n)).projective

lemma complex_exactAt (n : ℕ) : (complex M).ExactAt (n+1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp)]
  apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
  change LinearMap.range ((complex M).d (n+2) (n+1)).hom =
    LinearMap.ker ((complex M).d (n+1) n).hom
  rw [complex_d, complex_d]
  exact exact_differential M n

lemma complex_d_augment : (complex M).d 1 0 ≫ ModuleCat.ofHom (augment M 0) = 0 := by
  rw [complex_d]
  exact ModuleCat.hom_ext (augment_differential M 0)

lemma complex_exact_augment :
    (ShortComplex.mk _ _ (complex_d_augment M)).Exact := by
  apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
  change LinearMap.range ((complex M).d 1 0).hom = LinearMap.ker (augment M 0)
  rw [complex_d]
  exact range_differential M 0

instance augment_epi : Epi (ModuleCat.ofHom (augment M 0)) :=
  (ModuleCat.epi_iff_surjective _).mpr (cover _).surjective

/-- A projective resolution, including its augmentation quasi-isomorphism. -/
def resolution : ProjectiveResolution M.cat where
  complex := complex M
  π := (ChainComplex.toSingle₀Equiv _ _).symm ⟨ModuleCat.ofHom (augment M 0),
    complex_d_augment M⟩
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      ·
        refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2
          ⟨complex_exact_augment M, augment_epi M⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by erw [Category.id_comp])
          (by erw [Category.id_comp])
      all_goals rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact complex_exactAt M n
      · apply ChainComplex.exactAt_succ_single_obj⟩
end LittleFinitistic.PDMinimal

end

end OAI

end

section

namespace OAI
noncomputable section
namespace LittleFinitistic.PDTensor
open CategoryTheory CategoryTheory.Limits
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable (U : Type u) [AddCommGroup U] [Module k U] [Module Aᵐᵒᵖ U]

/-- Tor is the left derived functor of the actual balanced tensor functor. -/
abbrev Tor (M : ModuleCat.{u} A) (n : ℕ) : ModuleCat.{u} k :=
  ((tensorFunctor k A U).leftDerived n).obj M

variable [FiniteDimensional k A] (M : PDMinimal.FiniteModule k A)

def model : ChainComplex (ModuleCat k) ℕ :=
  ((tensorFunctor k A U).mapHomologicalComplex _).obj (PDMinimal.complex M)

/-- The chosen minimal resolution computes this actual derived functor. -/
def torIsoModel (n : ℕ) : Tor (k := k) U M.cat n ≅ (model U M).homology n :=
  (PDMinimal.resolution M).isoLeftDerivedObj (tensorFunctor k A U) n

variable (hU : ∀ a ∈ Ring.jacobson A, ∀ u : U, MulOpposite.op a • u = 0)

include hU in
/-- Minimality annihilates every tensor differential, including non-adjacent ones. -/
theorem model_d_zero (i j : ℕ) : (model U M).d i j = 0 := by
  change (tensorFunctor k A U).map ((PDMinimal.complex M).d i j) = 0
  by_cases h : i = j+1
  · subst i
    rw [PDMinimal.complex_d]
    apply ModuleCat.hom_ext
    exact @mapRight_radical_zero k A _ _ _ U _ _ _
      (ScalarModule k A (PDMinimal.term M (j+1)).cat)
      (ScalarModule k A (PDMinimal.term M j).cat)
      _ _ _ (scalarModuleTower k A (PDMinimal.term M (j+1)).cat)
      _ _ _ (scalarModuleTower k A (PDMinimal.term M j).cat)
      hU (PDMinimal.differential M j) (PDMinimal.differential_radical M j)
  · rw [(PDMinimal.complex M).shape i j (by change ¬ j+1=i; exact Ne.symm h)]
    exact Functor.map_zero _ _ _

/-- Homology of the tensor of a minimal resolution is its term, because all
its differentials have been proved zero. -/
def torIsoTerm (n : ℕ) : Tor (k := k) U M.cat n ≅
    (tensorFunctor k A U).obj (PDMinimal.term M n).cat :=
  torIsoModel U M n ≪≫
    (ShortComplex.LeftHomologyData.ofZeros ((model U M).sc n)
      (model_d_zero U M hU _ _) (model_d_zero U M hU _ _)).homologyIso
end LittleFinitistic.PDTensor

end

end OAI

end

section

namespace OAI
noncomputable section
namespace LittleFinitistic.BalancedTensor
universe u v w w' w'' z
variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
variable {M : Type w} [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M]
variable {M' : Type w'} [AddCommGroup M'] [Module k M'] [Module Aᵐᵒᵖ M']
variable {M'' : Type w''} [AddCommGroup M''] [Module k M''] [Module Aᵐᵒᵖ M'']
variable (N : Type z) [AddCommGroup N] [Module k N] [Module A N]
variable [IsScalarTower k Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M']
  [IsScalarTower k Aᵐᵒᵖ M'']

/-- Tensor an actual right-module homomorphism with the identity. -/
def mapLeft (f : M →ₗ[Aᵐᵒᵖ] M') : Tensor k A M N →ₗ[k] Tensor k A M' N :=
  lift ((mk k A M' N).compl₁₂ (f.restrictScalars k) LinearMap.id) (by
    intro a m n
    change mk k A M' N (f (MulOpposite.op a • m)) n = mk k A M' N (f m) (a • n)
    rw [map_smul]
    exact balance a (f m) n)

@[simp] theorem mapLeft_mk (f : M →ₗ[Aᵐᵒᵖ] M') (m : M) (n : N) :
    mapLeft (k := k) N f (mk k A M N m n) = mk k A M' N (f m) n := rfl

@[simp] theorem mapLeft_id : mapLeft (k := k) N (LinearMap.id : M →ₗ[Aᵐᵒᵖ] M) = LinearMap.id := by
  apply ext
  intro m n
  rfl

@[simp] theorem mapLeft_comp (f : M →ₗ[Aᵐᵒᵖ] M') (g : M' →ₗ[Aᵐᵒᵖ] M'') :
    mapLeft (k := k) N (g.comp f) = (mapLeft (k := k) N g).comp (mapLeft (k := k) N f) := by
  apply ext
  intro m n
  rfl

@[simp] theorem mapLeft_add (f g : M →ₗ[Aᵐᵒᵖ] M') :
    mapLeft (k := k) N (f+g) = mapLeft (k := k) N f + mapLeft (k := k) N g := by
  apply ext
  intro m n
  simp
end LittleFinitistic.BalancedTensor

end

end OAI

end

section

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.PDResidueProjection
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
variable (f : A →ₐ[k] D) (hf : Function.Surjective f)
variable (hsq : ∀ a ∈ RingHom.ker f.toRingHom, ∀ b ∈ RingHom.ker f.toRingHom, a*b=0)

def InflatedResidue (_f : A →ₐ[k] D) := PDTensor.Residue (A := D)
instance : AddCommGroup (InflatedResidue f) := inferInstanceAs (AddCommGroup (PDTensor.Residue (A := D)))
instance : Module k (InflatedResidue f) := inferInstanceAs (Module k (PDTensor.Residue (A := D)))
instance : Module Aᵐᵒᵖ (InflatedResidue f) :=
  Module.compHom (PDTensor.Residue (A := D)) f.toRingHom.op
instance (priority := 50) : Module Dᵐᵒᵖ (InflatedResidue f) :=
  inferInstanceAs (Module Dᵐᵒᵖ (PDTensor.Residue (A := D)))
instance (priority := 50) : IsScalarTower k Dᵐᵒᵖ (InflatedResidue f) :=
  inferInstanceAs (IsScalarTower k Dᵐᵒᵖ (PDTensor.Residue (A := D)))
instance : IsScalarTower k Aᵐᵒᵖ (InflatedResidue f) where
  smul_assoc c a s := by
    change MulOpposite.op (f (c • a.unop)) • (s : PDTensor.Residue (A := D)) =
      c • (MulOpposite.op (f a.unop) • (s : PDTensor.Residue (A := D)))
    rw [map_smul, MulOpposite.op_smul, smul_assoc]

def map : PDTensor.Residue (A := A) →ₗ[k] InflatedResidue f :=
  ((PDTensor.rightRadical (A := A)).restrictScalars k).liftQ
    (((PDTensor.rightRadical (A := D)).restrictScalars k).mkQ.comp f.toLinearMap) (by
      intro a ha
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      have he := PDSquareZero.comap_jacobson f.toRingHom hf hsq
      change a ∈ Ring.jacobson A at ha
      rw [← he] at ha
      exact ha)

@[simp] theorem map_mk (a : A) : map f hf hsq (Submodule.Quotient.mk a) =
    (Submodule.Quotient.mk (f a) : PDTensor.Residue (A := D)) := rfl

/-- The radical quotient-ring comparison also respects the actual k action. -/
def equiv : PDTensor.Residue (A := A) ≃ₗ[k] InflatedResidue f :=
  LinearEquiv.ofBijective (map f hf hsq) (by
    have he : (fun s => map f hf hsq s) =
        (fun s => PDSquareZero.residueQuotientEquiv f.toRingHom hf hsq s) := by
      funext s
      induction s using Submodule.Quotient.induction_on with
      | _ a => exact (PDSquareZero.residueQuotientEquiv_mk f.toRingHom hf hsq a).symm
    change Function.Bijective (fun s => map f hf hsq s)
    rw [he]
    exact (PDSquareZero.residueQuotientEquiv f.toRingHom hf hsq).bijective)

/-- Its right A action is precisely restriction through the canonical projection. -/
def rightEquiv : PDTensor.Residue (A := A) ≃ₗ[Aᵐᵒᵖ] InflatedResidue f where
  __ := (equiv f hf hsq).toAddEquiv
  map_smul' a s := by
    induction s using Submodule.Quotient.induction_on with
    | _ b =>
      change (Submodule.Quotient.mk (f (b*a.unop)) : PDTensor.Residue (A := D)) =
        Submodule.Quotient.mk (f b * f a.unop)
      rw [map_mul]

variable (N : Type u) [AddCommGroup N] [Module k N] [Module A N]

def tensorEquiv : BalancedTensor.Tensor k A (PDTensor.Residue (A := A)) N ≃ₗ[k]
    BalancedTensor.Tensor k A (InflatedResidue f) N :=
  LinearEquiv.ofLinearMap
    (BalancedTensor.mapLeft (k := k) N (rightEquiv f hf hsq).toLinearMap)
    (BalancedTensor.mapLeft (k := k) N (rightEquiv f hf hsq).symm.toLinearMap)
    (by
      apply BalancedTensor.ext
      intro s n
      simp only [LinearMap.comp_apply, BalancedTensor.mapLeft_mk, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply, LinearMap.id_apply])
    (by
      apply BalancedTensor.ext
      intro s n
      simp only [LinearMap.comp_apply, BalancedTensor.mapLeft_mk, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply, LinearMap.id_apply])

/-- The residue projection comparison is natural on all actual left A-modules. -/
def tensorNatIso : PDTensor.tensorFunctor k A (PDTensor.Residue (A := A)) ≅
    PDTensor.tensorFunctor k A (InflatedResidue f) :=
  NatIso.ofComponents (fun M => (tensorEquiv f hf hsq (PDTensor.ScalarModule k A M)).toModuleIso)
    (by
      intro M L h
      apply ModuleCat.hom_ext
      apply BalancedTensor.ext
      intro s n
      rfl)

variable (M : ModuleCat.{u} A) (P : ProjectiveResolution M)
def resolutionIso :
    ((PDTensor.tensorFunctor k A (PDTensor.Residue (A := A))).mapHomologicalComplex _).obj P.complex ≅
    ((PDTensor.tensorFunctor k A (InflatedResidue f)).mapHomologicalComplex _).obj P.complex :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (tensorNatIso f hf hsq).app (P.complex.X n))
    (fun i j _ => ((tensorNatIso f hf hsq).hom.naturality (P.complex.d i j)).symm)

/-- Actual derived residue tensor is unchanged by the proved right-module identification. -/
def torIso (n : ℕ) : PDTensor.Tor (k := k) (PDTensor.Residue (A := A)) M n ≅
    PDTensor.Tor (k := k) (InflatedResidue f) M n :=
  P.isoLeftDerivedObj (PDTensor.tensorFunctor k A (PDTensor.Residue (A := A))) n ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso (resolutionIso f hf hsq M P) ≪≫
    (P.isoLeftDerivedObj (PDTensor.tensorFunctor k A (InflatedResidue f)) n).symm
end LittleFinitistic.PDResidueProjection

end

end OAI

end

section

namespace OAI
noncomputable section
open CategoryTheory TensorProduct
open scoped TensorProduct
namespace LittleFinitistic.PDBarQuotient
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
variable (f : A →ₐ[k] D)

/-- D with the actual right A action through f. -/
def RightBase (_f : A →ₐ[k] D) := D
instance : Ring (RightBase f) := inferInstanceAs (Ring D)
instance : Algebra k (RightBase f) := inferInstanceAs (Algebra k D)
instance : Module Aᵐᵒᵖ (RightBase f) := Module.compHom D f.toRingHom.op

@[simp] theorem right_smul (a : A) (d : RightBase f) :
    MulOpposite.op a • d = (show RightBase f from (show D from d) * f a) := rfl

variable (V : Type u) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]

/-- Quotient map from the detector tensor to the actual left D-linear bar quotient. -/
def forward : BalancedTensor.Tensor k A (RightBase f) V →ₗ[k] DerivedBar.Balanced.tensor f V :=
  BalancedTensor.lift
    ((TensorProduct.mk k (RightBase f) V).compr₂
      ((DerivedBar.Balanced.quotient f V).restrictScalars k))
    (fun a d v => DerivedBar.Balanced.balanced f V d a v)

omit [IsScalarTower k A V] in
/-- Every D-linear balancing relation lies in the detector's k-linear relation
space; the proof retains all left D multiples, rather than assuming the quotients equal. -/
theorem relations_kill : (DerivedBar.Balanced.relations f V).restrictScalars k ≤
    (BalancedTensor.relations k A (RightBase f) V).mkQ.ker := by
  intro z hz
  change (BalancedTensor.relations k A (RightBase f) V).mkQ z = 0
  have h : ∀ d : D, (BalancedTensor.relations k A (RightBase f) V).mkQ (d • z) = 0 := by
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b,a,v,rfl⟩ := hx
      intro d
      rw [smul_sub, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
      change (BalancedTensor.relations k A (RightBase f) V).mkQ
        ((d*(b*f a)) ⊗ₜ[k] v - (d*b) ⊗ₜ[k] (a • v)) = 0
      erw [← mul_assoc, map_sub]
      exact sub_eq_zero.mpr (BalancedTensor.balance (k := k) (M := RightBase f) a (d*b) v)
    | zero => intro d; rw [smul_zero]; exact map_zero _
    | add x y hx hy ihx ihy =>
      intro d
      rw [smul_add]
      exact (map_add _ _ _).trans ((congrArg₂ (· + ·) (ihx d) (ihy d)).trans (add_zero _))
    | smul c x hx ih => intro d; simpa [smul_smul] using ih (d*c)
  simpa only [one_smul] using h 1

def inverse : DerivedBar.Balanced.tensor f V →ₗ[k] BalancedTensor.Tensor k A (RightBase f) V :=
  ((DerivedBar.Balanced.relations f V).restrictScalars k).liftQ
    (BalancedTensor.relations k A (RightBase f) V).mkQ (relations_kill f V)

omit [IsScalarTower k A V] in
@[simp] theorem forward_mk (d : RightBase f) (v : V) :
    forward f V (BalancedTensor.mk k A (RightBase f) V d v) =
      DerivedBar.Balanced.quotient f V (d ⊗ₜ[k] v) := rfl

omit [IsScalarTower k A V] in
@[simp] theorem inverse_quotient (d : D) (v : V) :
    inverse f V (DerivedBar.Balanced.quotient f V (d ⊗ₜ[k] v)) =
      BalancedTensor.mk k A (RightBase f) V d v := rfl

/-- Canonical actual quotient equivalence, on representatives d tensor v. -/
def equiv : BalancedTensor.Tensor k A (RightBase f) V ≃ₗ[k] DerivedBar.Balanced.tensor f V :=
  LinearEquiv.ofLinearMap (forward f V) (inverse f V) (by
    apply ((DerivedBar.Balanced.relations f V).restrictScalars k).linearMap_qext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro d
    apply LinearMap.ext
    intro v
    rfl) (by
    apply BalancedTensor.ext
    intro base vector
    rfl)

variable {V} {W : Type u} [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
theorem natural (h : V →ₗ[A] W) :
    (forward f W).comp (PDTensor.mapRight (k := k) (RightBase f) h) =
      ((DerivedBar.Balanced.map f V W h).restrictScalars k).comp (forward f V) := by
  apply BalancedTensor.ext
  intro d v
  rfl

omit [IsScalarTower k A V] in
/-- Exterior D multiplication agrees on every tensor generator. -/
theorem left_action (d b : D) (v : V) :
    forward f V (BalancedTensor.mk k A (RightBase f) V (d*b) v) =
      d • forward f V (BalancedTensor.mk k A (RightBase f) V b v) := by
  change DerivedBar.Balanced.quotient f V ((d*b) ⊗ₜ[k] v) =
    d • DerivedBar.Balanced.quotient f V (b ⊗ₜ[k] v)
  rw [← LinearMap.map_smul, TensorProduct.smul_tmul']
  rfl
end LittleFinitistic.PDBarQuotient

end

end OAI

end

section

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.PDBarQuotient
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
variable (f : A →ₐ[k] D)
variable (V : Type u) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]

/-- The actual exterior D-action transferred through the proved quotient equivalence. -/
instance leftModule : Module D (BalancedTensor.Tensor k A (RightBase f) V) :=
  (equiv f V).toAddEquiv.module D

instance leftTower : IsScalarTower k D (BalancedTensor.Tensor k A (RightBase f) V) :=
  (equiv f V).isScalarTower (A := D)

def linearEquiv : BalancedTensor.Tensor k A (RightBase f) V ≃ₗ[D]
    DerivedBar.Balanced.tensor f V := (equiv f V).toAddEquiv.linearEquiv D

omit [IsScalarTower k A V] in
/-- The transferred action is the original left regular multiplication. -/
@[simp] theorem smul_mk (d b : D) (v : V) :
    d • BalancedTensor.mk k A (RightBase f) V b v =
      BalancedTensor.mk k A (RightBase f) V (d*b) v := by
  apply (equiv f V).injective
  exact ((linearEquiv f V).map_smul d _).trans (left_action f d b v).symm

omit [IsScalarTower k A V] in
/-- Compatibility with every exterior scalar, on arbitrary balanced tensors. -/
theorem equiv_smul (d : D) (z : BalancedTensor.Tensor k A (RightBase f) V) :
    equiv f V (d • z) = d • equiv f V z := (linearEquiv f V).map_smul d z

variable {V} {W : Type u} [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
def map (h : V →ₗ[A] W) : BalancedTensor.Tensor k A (RightBase f) V →ₗ[D]
    BalancedTensor.Tensor k A (RightBase f) W :=
  (linearEquiv f W).symm.toLinearMap.comp
    ((DerivedBar.Balanced.map f V W h).comp (linearEquiv f V).toLinearMap)

theorem map_eq (h : V →ₗ[A] W) :
    (map f h).restrictScalars k = PDTensor.mapRight (k := k) (RightBase f) h := by
  apply BalancedTensor.ext
  intro d v
  rfl
end LittleFinitistic.PDBarQuotient

end

end OAI

end

section

namespace OAI
noncomputable section
namespace LittleFinitistic.PDTensor
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

include k in
/-- The actual residue right module is semisimple. -/
theorem residue_semisimple : IsSemisimpleModule Aᵐᵒᵖ (Residue (A := A)) := by
  have : IsArtinianRing A := isArtinian_of_tower k inferInstance
  let S := A ⧸ Ring.jacobson A
  let q : A →+* S := Ideal.Quotient.mk (Ring.jacobson A)
  have : IsSemisimpleRing S := inferInstance
  have : IsSemisimpleRing Sᵐᵒᵖ := inferInstance
  have : RingHomSurjective q.op := ⟨fun s => by
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective s.unop
    exact ⟨MulOpposite.op a, congrArg MulOpposite.op ha⟩⟩
  let f : A →ₛₗ[q.op] Sᵐᵒᵖ :=
    { toFun := fun a => MulOpposite.op (q a)
      map_add' := fun a b => by simp
      map_smul' := fun a b => by change MulOpposite.op (q (b*a.unop)) = _; simp }
  let e : Residue (A := A) →ₛₗ[q.op] Sᵐᵒᵖ :=
    (rightRadical (A := A)).liftQ f (by
      intro a ha
      change MulOpposite.op (Ideal.Quotient.mk (Ring.jacobson A) a) = 0
      rw [(Ideal.Quotient.eq_zero_iff_mem).mpr ha, MulOpposite.op_zero])
  have hef : (fun s => e s) = (fun s : Residue (A := A) => MulOpposite.op (residueRingEquiv (k := k) s)) := by
    funext s
    induction s using Submodule.Quotient.induction_on with
    | _ a => rfl
  have he : Function.Bijective e := by
    change Function.Bijective (fun s => e s)
    rw [hef]
    exact MulOpposite.op_bijective.comp (residueRingEquiv (k := k)).bijective
  exact (e.isSemisimpleModule_iff_of_bijective he).mpr inferInstance
end LittleFinitistic.PDTensor

end

end OAI

end

section

namespace OAI
noncomputable section
namespace LittleFinitistic.PDTensor
open CategoryTheory CategoryTheory.Limits
universe u
variable {A : Type u} [Ring A]

/-- For an Artinian ring the left-defined ring radical annihilates every
actual simple right module. The proof uses cyclicity and a genuine inverse;
it does not assume a left/right-radical identification theorem. -/
theorem right_simple_annihilated [IsArtinianRing A]
    (U : Type u) [AddCommGroup U] [Module Aᵐᵒᵖ U] [IsSimpleModule Aᵐᵒᵖ U]
    (a : A) (ha : a ∈ Ring.jacobson A) (u : U) : MulOpposite.op a • u=0 := by
  by_contra hv
  obtain ⟨b, hb⟩ := IsSimpleModule.toSpanSingleton_surjective Aᵐᵒᵖ hv u
  change b • (MulOpposite.op a • u) = u at hb
  have hab : -(a*b.unop) ∈ (⊥ : Ideal A).jacobson := by
    rw [Ideal.jacobson_bot]
    exact (Ring.jacobson A).neg_mem ((Ring.jacobson A).mul_mem_right b.unop ha)
  obtain ⟨z, hz⟩ := Ideal.exists_mul_add_sub_mem_of_mem_jacobson (-(a*b.unop)) hab
  have hz1 : z * (1-a*b.unop)=1 := by
    have h : z * (-(a*b.unop)+1)-1=0 := hz
    simpa [sub_eq_add_neg, add_comm] using sub_eq_zero.mp h
  have hz2 : (1-a*b.unop)*z=1 := mul_eq_one_comm.mp hz1
  have hu : MulOpposite.op (1-a*b.unop) • u=0 := by
    simp [MulOpposite.op_sub, MulOpposite.op_mul, sub_smul, mul_smul, hb]
  have hu0 : u=0 := by
    calc
      u = MulOpposite.op ((1-a*b.unop)*z) • u := by rw [hz2, MulOpposite.op_one, one_smul]
      _ = MulOpposite.op z • (MulOpposite.op (1-a*b.unop) • u) := by
        rw [MulOpposite.op_mul, mul_smul]
      _ = 0 := by rw [hu, smul_zero]
  apply hv
  rw [hu0, smul_zero]

variable {k : Type u} [Field k] [Algebra k A] [FiniteDimensional k A]
variable (U : Type u) [AddCommGroup U] [Module k U] [Module Aᵐᵒᵖ U]
  [IsSimpleModule Aᵐᵒᵖ U]
variable (M : PDMinimal.FiniteModule k A)

/-- The derived tensor with every actual simple right module is the tensor
of that simple module with the n-th minimal projective-resolution term. -/
def simpleTorIsoTerm (n : ℕ) : Tor (k := k) U M.cat n ≅
    (tensorFunctor k A U).obj (PDMinimal.term M n).cat := by
  haveI : IsArtinianRing A := isArtinian_of_tower k inferInstance
  exact torIsoTerm U M (right_simple_annihilated U) n
end LittleFinitistic.PDTensor

end

end OAI

end

section

namespace OAI
noncomputable section
namespace LittleFinitistic.PDMinimal
open CategoryTheory CategoryTheory.Limits
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

lemma cover_subsingleton (M : FiniteModule k A) [Subsingleton M] :
    Subsingleton (cover M).source := by
  have hp : (cover M).π = 0 := Subsingleton.elim _ _
  have hsurj := (cover M).minimal 0 (by simp [hp])
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, ha⟩ := hsurj x
  obtain ⟨b, hb⟩ := hsurj y
  exact ha.symm.trans hb

lemma cover_injective (M : FiniteModule k A) [Module.Projective A M] :
    Function.Injective (cover M).π := by
  obtain ⟨g, hg⟩ := Module.projective_lifting_property (cover M).π LinearMap.id
    (cover M).surjective
  have he : (cover M).π.comp (g.comp (cover M).π) = (cover M).π := by
    rw [← LinearMap.comp_assoc, hg, LinearMap.id_comp]
  have hs := (cover M).minimal _ he
  have hgs : Function.Surjective g := by
    intro x
    obtain ⟨y, hy⟩ := hs x
    exact ⟨(cover M).π y, hy⟩
  have hgp : g.comp (cover M).π = LinearMap.id := by
    ext x
    obtain ⟨y, rfl⟩ := hgs x
    exact congrArg g (DFunLike.congr_fun hg y)
  exact LinearMap.injective_of_comp_eq_id _ _ hgp

lemma next_subsingleton_of_projective (M : FiniteModule k A) [Module.Projective A M] :
    Subsingleton (next M) := by
  have he := LinearMap.ker_eq_bot.mpr (cover_injective M)
  change Subsingleton (LinearMap.ker (cover M).π)
  rw [he]
  infer_instance

/-- Vanishing of a term of the constructed resolution gives the standard
categorical projective-dimension bound. -/
theorem pdLT_of_term_zero (M : FiniteModule k A) (n i : ℕ)
    (hz : Subsingleton (term M (i+n))) :
    HasProjectiveDimensionLT (syzygy M i).cat n := by
  induction n generalizing i with
  | zero =>
    have : Subsingleton (term M i) := by simpa using hz
    have : Subsingleton (syzygy M i) :=
      Function.Surjective.subsingleton (cover _).surjective
    exact (hasProjectiveDimensionLT_zero_iff_isZero _).mpr
      (ModuleCat.isZero_iff_subsingleton.mpr (show Subsingleton (syzygy M i) from inferInstance))
  | succ n ih =>
    have hnext : HasProjectiveDimensionLT (syzygy M (i+1)).cat n :=
      ih (i+1) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hz)
    have hs := LinearMap.shortExact_shortComplexKer (cover (syzygy M i)).surjective
    exact hs.hasProjectiveDimensionLT_X₃ n hnext inferInstance

lemma syzygy_projective (M : FiniteModule k A) (n i : ℕ)
    (h : HasProjectiveDimensionLT (syzygy M i).cat (n+1)) :
    Projective (syzygy M (i+n)).cat := by
  induction n generalizing i with
  | zero =>
    simpa using projective_iff_hasProjectiveDimensionLT_one.mpr h
  | succ n ih =>
    have hs := LinearMap.shortExact_shortComplexKer (cover (syzygy M i)).surjective
    have hn : HasProjectiveDimensionLT (syzygy M (i+1)).cat (n+1) :=
      (hs.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp h
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (i+1) hn

/-- Finite projective dimension forces the minimal resolution to terminate. -/
theorem term_zero_of_pdLE (M : FiniteModule k A) (n : ℕ)
    (h : HasProjectiveDimensionLE M.cat n) : Subsingleton (term M (n+1)) := by
  have hp := syzygy_projective M n 0 h
  rw [Nat.zero_add] at hp
  have : Module.Projective A (syzygy M n) :=
    (IsProjective.iff_projective _).mpr (by simpa only [Nat.zero_add, FiniteModule.cat] using hp)
  have : Subsingleton (syzygy M (n+1)) := next_subsingleton_of_projective (syzygy M n)
  exact cover_subsingleton _

/-- The actual minimal-resolution term criterion, proved from covers and
short-exact-sequence dimension shifting. -/
theorem pdLE_iff_term_zero (M : FiniteModule k A) (n : ℕ) :
    HasProjectiveDimensionLE M.cat n ↔ Subsingleton (term M (n+1)) :=
  ⟨term_zero_of_pdLE M n, fun h => pdLT_of_term_zero M (n+1) 0 (by simpa using h)⟩
end LittleFinitistic.PDMinimal

end

end OAI

end

section

namespace OAI
noncomputable section
namespace LittleFinitistic.PDTensor
open CategoryTheory CategoryTheory.Limits
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

/-- Nakayama detects zero modules using the actual radical-quotient tensor. -/
theorem residueTensor_subsingleton_iff
    (N : Type u) [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
    [Module.Finite A N] :
    Subsingleton (BalancedTensor.Tensor k A (Residue (A := A)) N) ↔ Subsingleton N := by
  constructor
  · intro h
    by_contra hn
    have : Nontrivial N := not_subsingleton_iff_nontrivial.mp hn
    have := residueTensor_nontrivial (k := k) (A := A) N
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (BalancedTensor.Tensor k A (Residue (A := A)) N)
    exact hxy (h.elim x y)
  · intro h
    have := h
    infer_instance

variable [FiniteDimensional k A] (M : PDMinimal.FiniteModule k A)

/-- For the semisimple quotient S, the n-th Tor is zero exactly when the n-th
term of the constructed minimal projective resolution is zero. -/
theorem residueTor_zero_iff_term (n : ℕ) :
    IsZero (Tor (k := k) (Residue (A := A)) M.cat n) ↔
      Subsingleton (PDMinimal.term M n) := by
  let e := torIsoTerm (Residue (A := A)) M residue_annihilated n
  rw [e.isZero_iff]
  change IsZero (ModuleCat.of k (BalancedTensor.Tensor k A (Residue (A := A))
    (ScalarModule k A (PDMinimal.term M n).cat))) ↔ _
  rw [ModuleCat.isZero_iff_subsingleton]
  have : Module.Finite A (ScalarModule k A (PDMinimal.term M n).cat) :=
    show Module.Finite A (PDMinimal.term M n) from inferInstance
  exact residueTensor_subsingleton_iff (k := k) (ScalarModule k A (PDMinimal.term M n).cat)

/-- Projective dimension of a finite-dimensional module over an actual
finite-dimensional algebra is detected by its derived tensor with A/rad A.
No detection theorem is assumed: the proof constructs minimal resolutions. -/
theorem pdLE_iff_residueTor_zero (n : ℕ) :
    HasProjectiveDimensionLE M.cat n ↔
      IsZero (Tor (k := k) (Residue (A := A)) M.cat (n+1)) := by
  rw [PDMinimal.pdLE_iff_term_zero, residueTor_zero_iff_term]

/-- The finite-projective-dimension implication used in cor:pd-detection. -/
theorem finite_pd_of_bounded_residueTor
    (h : ∃ b : ℕ, ∀ n, b < n → IsZero (Tor (k := k) (Residue (A := A)) M.cat n)) :
    ∃ b : ℕ, HasProjectiveDimensionLE M.cat b := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, (pdLE_iff_residueTor_zero M b).mpr (hb (b+1) (by omega))⟩

/-- The conclusion uses mathlib's actual numerical projective dimension. -/
theorem projectiveDimension_le_of_residueTor_zero (n : ℕ)
    (h : IsZero (Tor (k := k) (Residue (A := A)) M.cat (n+1))) :
    projectiveDimension M.cat ≤ n :=
  (projectiveDimension_le_iff _ _).mpr ((pdLE_iff_residueTor_zero M n).mpr h)
end LittleFinitistic.PDTensor

end

end OAI

end

section

namespace OAI
noncomputable section
namespace LittleFinitistic.PDTensor
open CategoryTheory CategoryTheory.Limits
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (U : Type u) [AddCommGroup U] [Module k U] [Module Aᵐᵒᵖ U]
variable (M : PDMinimal.FiniteModule k A)

/-- Any right module detects a lower bound through nonzero Tor; it need not
be flat, finite-dimensional, or annihilated by the radical. -/
theorem tor_zero_of_pdLT (n : ℕ) (h : HasProjectiveDimensionLT M.cat n) :
    IsZero (Tor (k := k) U M.cat n) := by
  have ht : Subsingleton (PDMinimal.term M n) := by
    cases n with
    | zero =>
      have hm := (hasProjectiveDimensionLT_zero_iff_isZero _).mp h
      have : Subsingleton M := ModuleCat.subsingleton_of_isZero hm
      exact PDMinimal.cover_subsingleton M
    | succ n => exact PDMinimal.term_zero_of_pdLE M n h
  have hz : IsZero (PDMinimal.term M n).cat := ModuleCat.isZero_iff_subsingleton.mpr ht
  have hm : IsZero ((model U M).X n) := (tensorFunctor k A U).map_isZero hz
  exact (HomologicalComplex.ExactAt.of_isZero hm).isZero_homology.of_iso (torIsoModel U M n)

theorem le_projectiveDimension_of_nonzero_Tor (n : ℕ)
    (h : ¬ IsZero (Tor (k := k) U M.cat n)) : n ≤ projectiveDimension M.cat := by
  by_contra hn
  exact h (tor_zero_of_pdLT U M n (projectiveDimension_lt_iff.mp (lt_of_not_ge hn)))

theorem lower_bound_of_nonzero_Tor (r n : ℕ) (hrn : r ≤ n)
    (h : ¬ IsZero (Tor (k := k) U M.cat n)) : r ≤ projectiveDimension M.cat := by
  exact le_trans (by exact_mod_cast hrn) (le_projectiveDimension_of_nonzero_Tor U M n h)

/-- Bounded radical-quotient Tor gives finite numerical projective dimension. -/
theorem projectiveDimension_lt_top_of_bounded_residueTor
    (h : ∃ b : ℕ, ∀ n, b < n → IsZero (Tor (k := k) (Residue (A := A)) M.cat n)) :
    projectiveDimension M.cat < ⊤ := by
  obtain ⟨b, hb⟩ := h
  exact lt_of_le_of_lt
    (projectiveDimension_le_of_residueTor_zero M b (hb (b+1) (by omega))) (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top b))
end LittleFinitistic.PDTensor

end

end OAI

end

section

namespace OAI
noncomputable section
namespace LittleFinitistic.PDTensor
open CategoryTheory CategoryTheory.Limits Submodule
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

/-- A nonzero finite module is detected by tensor with an actual simple right
submodule of A/rad A. This is an existence proof, not an assumed simple detector. -/
theorem exists_simple_tensor_nonzero
    (N : Type u) [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
    [Module.Finite A N] [Nontrivial N] :
    ∃ S : Submodule Aᵐᵒᵖ (Residue (A := A)), IsSimpleModule Aᵐᵒᵖ S ∧
      ¬ Subsingleton (BalancedTensor.Tensor k A S N) := by
  have := residue_semisimple (k := k) (A := A)
  by_contra h
  have hS (S : Submodule Aᵐᵒᵖ (Residue (A := A))) (hs : IsSimpleModule Aᵐᵒᵖ S) :
      Subsingleton (BalancedTensor.Tensor k A S N) := by
    by_contra hn
    exact h ⟨S, hs, hn⟩
  let K : Submodule Aᵐᵒᵖ (Residue (A := A)) :=
    { carrier := {u | ∀ n : N, BalancedTensor.mk k A (Residue (A := A)) N u n=0}
      zero_mem' := fun n => LinearMap.congr_fun (map_zero (BalancedTensor.mk k A (Residue (A := A)) N)) n
      add_mem' := fun hu hv n => by
        change (BalancedTensor.mk k A (Residue (A := A)) N ( _ + _)) n=0
        rw [map_add, LinearMap.add_apply, hu, hv, add_zero]
      smul_mem' := fun a u hu n => by
        rw [show a = MulOpposite.op a.unop from rfl, BalancedTensor.balance]
        exact hu _ }
  have hK : (⊤ : Submodule Aᵐᵒᵖ (Residue (A := A))) ≤ K := by
    rw [← IsSemisimpleModule.sSup_simples_eq_top Aᵐᵒᵖ (Residue (A := A))]
    apply sSup_le
    intro S hs u hu n
    let f := BalancedTensor.mapLeft (k := k) N S.subtype
    have hz : BalancedTensor.mk k A S N ⟨u,hu⟩ n = 0 := (hS S hs).elim _ _
    have hz' := congrArg f hz
    simpa [f] using hz'
  have hz (z : BalancedTensor.Tensor k A (Residue (A := A)) N) : z=0 := by
    induction z using BalancedTensor.induction_on with
    | hz => rfl
    | ht u n => exact hK mem_top n
    | ha x y hx hy => rw [hx,hy,add_zero]
  have := residueTensor_nontrivial (k := k) (A := A) N
  obtain ⟨x,y,hxy⟩ := exists_pair_ne (BalancedTensor.Tensor k A (Residue (A := A)) N)
  exact hxy ((hz x).trans (hz y).symm)

variable (M : PDMinimal.FiniteModule k A)

/-- The exact simple-module form of projective-dimension detection. The test
modules here are actual simple right submodules of the fixed radical quotient. -/
theorem pdLE_iff_simpleTor_zero (n : ℕ) :
    HasProjectiveDimensionLE M.cat n ↔
      ∀ S : Submodule Aᵐᵒᵖ (Residue (A := A)), IsSimpleModule Aᵐᵒᵖ S →
        IsZero (Tor (k := k) S M.cat (n+1)) := by
  constructor
  · intro h S _
    exact tor_zero_of_pdLT S M (n+1) h
  · intro h
    apply (PDMinimal.pdLE_iff_term_zero M n).mpr
    by_contra ht
    have : Nontrivial (PDMinimal.term M (n+1)) := not_subsingleton_iff_nontrivial.mp ht
    have : Nontrivial (ScalarModule k A (PDMinimal.term M (n+1)).cat) :=
      show Nontrivial (PDMinimal.term M (n+1)) from inferInstance
    have : Module.Finite A (ScalarModule k A (PDMinimal.term M (n+1)).cat) :=
      show Module.Finite A (PDMinimal.term M (n+1)) from inferInstance
    obtain ⟨S, hS, hnonzero⟩ := exists_simple_tensor_nonzero (k := k) (A := A)
      (ScalarModule k A (PDMinimal.term M (n+1)).cat)
    have := hS
    have hz := (h S hS).of_iso (simpleTorIsoTerm S M (n+1)).symm
    exact hnonzero (ModuleCat.isZero_iff_subsingleton.mp hz)
end LittleFinitistic.PDTensor

end

end OAI

end

section

namespace OAI
noncomputable section
namespace LittleFinitistic.PDTensor
open CategoryTheory CategoryTheory.Limits
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (M : PDMinimal.FiniteModule k A)

theorem bounded_residueTor_of_finite_pd
    (h : ∃ b : ℕ, HasProjectiveDimensionLE M.cat b) :
    ∃ b : ℕ, ∀ n, b < n → IsZero (Tor (k := k) (Residue (A := A)) M.cat n) := by
  obtain ⟨b, hb⟩ := h
  have : HasProjectiveDimensionLT M.cat (b+1) := hb
  refine ⟨b, fun n hn => tor_zero_of_pdLT (Residue (A := A)) M n ?_⟩
  exact hasProjectiveDimensionLT_of_ge M.cat (b+1) n (by omega)

/-- Finite projective dimension is equivalent to bounded actual residue Tor. -/
theorem finite_pd_iff_bounded_residueTor :
    projectiveDimension M.cat ≠ ⊤ ↔
      ∃ b : ℕ, ∀ n, b < n → IsZero (Tor (k := k) (Residue (A := A)) M.cat n) := by
  rw [projectiveDimension_ne_top_iff]
  exact ⟨bounded_residueTor_of_finite_pd M, finite_pd_of_bounded_residueTor M⟩

/-- The upper detector accepts any actual projective resolution, including a
bar resolution once its exactness and projectivity have been proved. -/
theorem finite_pd_of_resolution
    (P : ProjectiveResolution M.cat)
    (h : ∃ b : ℕ, ∀ n, b < n → IsZero
      (((tensorFunctor k A (Residue (A := A))).mapHomologicalComplex _).obj P.complex |>.homology n)) :
    projectiveDimension M.cat < ⊤ := by
  apply projectiveDimension_lt_top_of_bounded_residueTor M
  obtain ⟨b, hb⟩ := h
  exact ⟨b, fun n hn => (hb n hn).of_iso
    (P.isoLeftDerivedObj (tensorFunctor k A (Residue (A := A))) n)⟩

variable (U : Type u) [AddCommGroup U] [Module k U] [Module Aᵐᵒᵖ U]

/-- The lower detector also accepts any actual projective resolution.
The nonzero class can be supplied by a summand of the bar decomposition. -/
theorem lower_bound_of_resolution (P : ProjectiveResolution M.cat) (r n : ℕ) (hrn : r ≤ n)
    (h : ¬ IsZero (((tensorFunctor k A U).mapHomologicalComplex _).obj P.complex |>.homology n)) :
    r ≤ projectiveDimension M.cat := by
  apply lower_bound_of_nonzero_Tor U M r n hrn
  intro hz
  exact h (hz.of_iso (P.isoLeftDerivedObj (tensorFunctor k A U) n).symm)
end LittleFinitistic.PDTensor

end

end OAI

end

section

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.PDBar
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (M : PDMinimal.FiniteModule k A)
variable (U : Type u) [AddCommGroup U] [Module k U] [Module Aᵐᵒᵖ U]

abbrev tensorComplex (P : ProjectiveResolution M.cat) : ChainComplex (ModuleCat k) ℕ :=
  ((PDTensor.tensorFunctor k A U).mapHomologicalComplex _).obj P.complex

/-- Any actual projective resolution computes the same Tor, including the
constructed absolute bar resolution. -/
def torIsoResolution (P : ProjectiveResolution M.cat) (n : ℕ) :
    PDTensor.Tor (k := k) U M.cat n ≅ (tensorComplex M U P).homology n :=
  P.isoLeftDerivedObj (PDTensor.tensorFunctor k A U) n

abbrev resolution : ProjectiveResolution M.cat := DerivedBar.projectiveResolution k A M

/-- No extra identification between the bar augmentation and M is assumed. -/
def torIsoBar (n : ℕ) :
    PDTensor.Tor (k := k) U M.cat n ≅ (tensorComplex M U (resolution M)).homology n :=
  torIsoResolution M U (resolution M) n

variable {U}
theorem pdLE_iff_residue_resolution (P : ProjectiveResolution M.cat) (n : ℕ) :
    HasProjectiveDimensionLE M.cat n ↔
      IsZero ((tensorComplex M (PDTensor.Residue (A := A)) P).homology (n+1)) := by
  rw [PDTensor.pdLE_iff_residueTor_zero M n]
  exact (torIsoResolution M _ P (n+1)).isZero_iff

theorem pdLE_iff_simple_resolution (P : ProjectiveResolution M.cat) (n : ℕ) :
    HasProjectiveDimensionLE M.cat n ↔
      ∀ S : Submodule Aᵐᵒᵖ (PDTensor.Residue (A := A)), IsSimpleModule Aᵐᵒᵖ S →
        IsZero ((tensorComplex M S P).homology (n+1)) := by
  rw [PDTensor.pdLE_iff_simpleTor_zero M n]
  exact forall_congr' fun S => imp_congr_right fun _ =>
    (torIsoResolution M S P (n+1)).isZero_iff
end LittleFinitistic.PDBar

end

end OAI

end

section

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.PDBarQuotient
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
variable (f : A →ₐ[k] D)
variable (V : Type u) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]

/-- The restricted scalar convention in the detector agrees with the original
compatible k action by actual tensor maps in both directions. -/
def scalarEquiv :
    (PDTensor.tensorFunctor k A (RightBase f)).obj (ModuleCat.of A V) ≃ₗ[k]
      BalancedTensor.Tensor k A (RightBase f) V :=
  LinearEquiv.ofLinearMap
    (PDTensor.mapRight (k := k) (M := PDTensor.ScalarModule k A (ModuleCat.of A V))
      (N := V) (RightBase f) LinearMap.id)
    (PDTensor.mapRight (k := k) (M := V)
      (N := PDTensor.ScalarModule k A (ModuleCat.of A V)) (RightBase f) LinearMap.id)
    (by apply BalancedTensor.ext; intros; rfl)
    (by apply BalancedTensor.ext; intros; rfl)

def nativeScalarEquiv : DerivedBar.Balanced.tensor f V ≃ₗ[k]
    (ModuleCat.restrictScalars (algebraMap k D)).obj
      (ModuleCat.of D (DerivedBar.Balanced.tensor f V)) where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' c z := (IsScalarTower.algebraMap_smul D c z).symm

def objectIso :
    (PDTensor.tensorFunctor k A (RightBase f)).obj (ModuleCat.of A V) ≅
      (ModuleCat.restrictScalars (algebraMap k D)).obj
        (ModuleCat.of D (DerivedBar.Balanced.tensor f V)) :=
  (((scalarEquiv f V).trans (equiv f V)).trans (nativeScalarEquiv f V)).toModuleIso

variable {V} {W : Type u} [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
theorem objectIso_natural (h : V →ₗ[A] W) :
    (PDTensor.tensorFunctor k A (RightBase f)).map (ModuleCat.ofHom h) ≫ (objectIso f W).hom =
      (objectIso f V).hom ≫ (ModuleCat.restrictScalars (algebraMap k D)).map
        (ModuleCat.ofHom (DerivedBar.Balanced.map f V W h)) := by
  apply ModuleCat.hom_ext
  apply BalancedTensor.ext
  intro d v
  rfl

variable (N : Type u) [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

/-- The detector's tensor of the actual bar resolution is the bar worker's
balanced complex, after restricting only its exterior scalars. -/
def barQuotientIso :
    ((PDTensor.tensorFunctor k A (RightBase f)).mapHomologicalComplex _).obj
      (DerivedBar.projectiveResolution k A N).complex ≅
    ((ModuleCat.restrictScalars (algebraMap k D)).mapHomologicalComplex _).obj
      (DerivedBar.tensorBarComplex k A D N f) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => objectIso f (DerivedBar.term k A N (n+1))) (by
      intro i j hij
      change j+1=i at hij
      subst i
      simp only [DerivedBar.tensorBarComplex, DerivedBar.projectiveResolution, DerivedBar.complex, ChainComplex.of_d, Functor.mapHomologicalComplex_obj_d]
      exact (objectIso_natural f (DerivedBar.differential k A N (j+1))).symm)

/-- Comparison to the literal two-sided bar complex used in the splitting. -/
def twoSidedIso :
    ((PDTensor.tensorFunctor k A (RightBase f)).mapHomologicalComplex _).obj
      (DerivedBar.projectiveResolution k A N).complex ≅
    ((ModuleCat.restrictScalars (algebraMap k D)).mapHomologicalComplex _).obj
      (DerivedBar.twoSidedComplex k A D N f) :=
  barQuotientIso f N ≪≫
    ((ModuleCat.restrictScalars (algebraMap k D)).mapHomologicalComplex _).mapIso
      (DerivedBar.tensorBarIso k A D N f)

variable [FiniteDimensional k A] [FiniteDimensional k N]
/-- Tor computed by the literal two-sided bar, with no assumed quotient comparison. -/
def torIsoTwoSided (n : ℕ) :
    PDTensor.Tor (k := k) (RightBase f) (ModuleCat.of A N) n ≅
      (((ModuleCat.restrictScalars (algebraMap k D)).mapHomologicalComplex _).obj
        (DerivedBar.twoSidedComplex k A D N f)).homology n :=
  (DerivedBar.projectiveResolution k A N).isoLeftDerivedObj
    (PDTensor.tensorFunctor k A (RightBase f)) n ≪≫
      (HomologicalComplex.homologyFunctor _ _ n).mapIso (twoSidedIso f N)
end LittleFinitistic.PDBarQuotient

end

end OAI

end

section

namespace OAI
noncomputable section
open CategoryTheory TensorProduct
open scoped TensorProduct
namespace LittleFinitistic.PDResidueAssociativity
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
variable (f : A →ₐ[k] D)
variable (V : Type u) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]

def coefficient (s : (PDTensor.Residue (A := D))) : PDBarQuotient.RightBase f →ₗ[k] V →ₗ[k] (BalancedTensor.Tensor k A (PDResidueProjection.InflatedResidue f) V) where
  toFun d := BalancedTensor.mk k A (PDResidueProjection.InflatedResidue f) V (MulOpposite.op (show D from d) • s)
  map_add' a b := by
    ext v
    exact (congrArg (fun x : (PDResidueProjection.InflatedResidue f) => BalancedTensor.mk k A (PDResidueProjection.InflatedResidue f) V x v)
      (add_smul (MulOpposite.op (show D from a))
        (MulOpposite.op (show D from b)) s)).trans
      (LinearMap.congr_fun ((BalancedTensor.mk k A (PDResidueProjection.InflatedResidue f) V).map_add _ _) v)
  map_smul' c d := by
    ext v
    change BalancedTensor.mk k A (PDResidueProjection.InflatedResidue f) V (MulOpposite.op (c • (show D from d)) • s) v = _
    rw [MulOpposite.op_smul, smul_assoc]
    exact LinearMap.congr_fun ((BalancedTensor.mk k A (PDResidueProjection.InflatedResidue f) V).map_smul c _) v

def inner (s : (PDTensor.Residue (A := D))) : (DerivedBar.Balanced.tensor f V) →ₗ[k] (BalancedTensor.Tensor k A (PDResidueProjection.InflatedResidue f) V) :=
  (BalancedTensor.lift (coefficient f V s) (by
    intro a d v
    change BalancedTensor.mk k A (PDResidueProjection.InflatedResidue f) V (MulOpposite.op ((show D from d)*f a) • s) v =
      BalancedTensor.mk k A (PDResidueProjection.InflatedResidue f) V (MulOpposite.op (show D from d) • s) (a • v)
    rw [MulOpposite.op_mul, mul_smul]
    exact BalancedTensor.balance (k := k) (M := (PDResidueProjection.InflatedResidue f)) a _ v)).comp (PDBarQuotient.inverse f V)

omit [IsScalarTower k A V] in
@[simp] theorem inner_mk (s : (PDTensor.Residue (A := D))) (d : D) (v : V) :
    inner f V s (DerivedBar.Balanced.quotient f V (d ⊗ₜ[k] v)) =
      BalancedTensor.mk k A (PDResidueProjection.InflatedResidue f) V (MulOpposite.op d • s) v := rfl

def pair : (PDTensor.Residue (A := D)) →ₗ[k] (DerivedBar.Balanced.tensor f V) →ₗ[k] (BalancedTensor.Tensor k A (PDResidueProjection.InflatedResidue f) V) where
  toFun := inner f V
  map_add' s t := by
    apply ((DerivedBar.Balanced.relations f V).restrictScalars k).linearMap_qext
    apply TensorProduct.ext
    ext d v
    change BalancedTensor.mk k A (PDResidueProjection.InflatedResidue f) V (MulOpposite.op d • (s+t)) v =
      BalancedTensor.mk k A (PDResidueProjection.InflatedResidue f) V (MulOpposite.op d • s) v + BalancedTensor.mk k A (PDResidueProjection.InflatedResidue f) V (MulOpposite.op d • t) v
    rw [smul_add]
    exact LinearMap.congr_fun ((BalancedTensor.mk k A (PDResidueProjection.InflatedResidue f) V).map_add _ _) v
  map_smul' c s := by
    apply ((DerivedBar.Balanced.relations f V).restrictScalars k).linearMap_qext
    apply TensorProduct.ext
    ext d v
    change BalancedTensor.mk k A (PDResidueProjection.InflatedResidue f) V (MulOpposite.op d • (c • s)) v =
      c • BalancedTensor.mk k A (PDResidueProjection.InflatedResidue f) V (MulOpposite.op d • s) v
    rw [smul_comm]
    exact LinearMap.congr_fun ((BalancedTensor.mk k A (PDResidueProjection.InflatedResidue f) V).map_smul c _) v

def forward : BalancedTensor.Tensor k D (PDTensor.Residue (A := D)) (DerivedBar.Balanced.tensor f V) →ₗ[k] (BalancedTensor.Tensor k A (PDResidueProjection.InflatedResidue f) V) :=
  BalancedTensor.lift (pair f V) (by
    intro d s z
    induction z using Submodule.Quotient.induction_on with
    | _ z =>
      induction z using TensorProduct.inductionOn with
      | tmul b v =>
        change inner f V (MulOpposite.op d • s) (DerivedBar.Balanced.quotient f V (b ⊗ₜ[k] v)) =
          inner f V s (d • DerivedBar.Balanced.quotient f V (b ⊗ₜ[k] v))
        rw [inner_mk, ← LinearMap.map_smul, TensorProduct.smul_tmul', inner_mk]
        rw [← mul_smul, ← MulOpposite.op_mul]
        rfl
      | add x y hx hy => simpa only [Submodule.Quotient.mk_add, map_add, smul_add] using congrArg₂ (·+·) hx hy)

def unit : V →ₗ[k] (DerivedBar.Balanced.tensor f V) :=
  ((DerivedBar.Balanced.quotient f V).restrictScalars k).comp (TensorProduct.mk k D V 1)

def inverse : (BalancedTensor.Tensor k A (PDResidueProjection.InflatedResidue f) V) →ₗ[k] BalancedTensor.Tensor k D (PDTensor.Residue (A := D)) (DerivedBar.Balanced.tensor f V) :=
  BalancedTensor.lift ((BalancedTensor.mk k D (PDTensor.Residue (A := D)) (DerivedBar.Balanced.tensor f V)).compl₁₂ LinearMap.id (unit f V)) (by
    intro a s v
    change BalancedTensor.mk k D (PDTensor.Residue (A := D)) (DerivedBar.Balanced.tensor f V) (MulOpposite.op (f a) • s) (unit f V v) =
      BalancedTensor.mk k D (PDTensor.Residue (A := D)) (DerivedBar.Balanced.tensor f V) s (unit f V (a • v))
    erw [BalancedTensor.balance (k := k) (A := D) (M := (PDTensor.Residue (A := D))) (N := (DerivedBar.Balanced.tensor f V))
      (f a) (show (PDTensor.Residue (A := D)) from s) (unit f V v)]
    congr 1
    change f a • DerivedBar.Balanced.quotient f V ((1 : D) ⊗ₜ[k] v) =
      DerivedBar.Balanced.quotient f V ((1 : D) ⊗ₜ[k] (a • v))
    rw [← LinearMap.map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    simpa only [one_mul] using DerivedBar.Balanced.balanced f V (1 : D) a v)

omit [IsScalarTower k A V] in
@[simp] theorem inverse_mk (s : (PDResidueProjection.InflatedResidue f)) (v : V) :
    inverse f V (BalancedTensor.mk k A (PDResidueProjection.InflatedResidue f) V s v) = BalancedTensor.mk k D (PDTensor.Residue (A := D)) (DerivedBar.Balanced.tensor f V) s (unit f V v) := rfl

/-- Actual balanced associativity (PDTensor.Residue (A := D)) tensor_D (D tensor_A V) = (PDTensor.Residue (A := D)) tensor_A V,
with the right A action restricted along f. -/
def equiv : BalancedTensor.Tensor k D (PDTensor.Residue (A := D)) (DerivedBar.Balanced.tensor f V) ≃ₗ[k] (BalancedTensor.Tensor k A (PDResidueProjection.InflatedResidue f) V) :=
  LinearEquiv.ofLinearMap (forward f V) (inverse f V) (by
    apply BalancedTensor.ext
    intro s v
    change BalancedTensor.mk k A (PDResidueProjection.InflatedResidue f) V (MulOpposite.op (1 : D) • s) v = _
    rw [MulOpposite.op_one, one_smul]
    rfl) (by
    apply BalancedTensor.ext
    intro s z
    induction z using Submodule.Quotient.induction_on with
    | _ z =>
      induction z using TensorProduct.inductionOn with
      | tmul d v =>
        change BalancedTensor.mk k D (PDTensor.Residue (A := D)) (DerivedBar.Balanced.tensor f V) (MulOpposite.op d • s) (unit f V v) =
          BalancedTensor.mk k D (PDTensor.Residue (A := D)) (DerivedBar.Balanced.tensor f V) s (DerivedBar.Balanced.quotient f V (d ⊗ₜ[k] v))
        rw [BalancedTensor.balance]
        congr 1
        change d • DerivedBar.Balanced.quotient f V ((1 : D) ⊗ₜ[k] v) = _
        rw [← LinearMap.map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      | add x y hx hy => simpa only [Submodule.Quotient.mk_add, map_add] using congrArg₂ (·+·) hx hy)
end LittleFinitistic.PDResidueAssociativity

end

end OAI

end

section

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.PDBar
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
local instance : HasDerivedCategory.{u+1} (ModuleCat.{u} k) :=
  HasDerivedCategory.standard (ModuleCat.{u} k)

/-- Actual derived object of a nonnegative chain complex, with degree n sent to -n. -/
abbrev derivedObject (C : ChainComplex (ModuleCat.{u} k) ℕ) :=
  DerivedCategory.Q.obj (C.extend ComplexShape.embeddingDownNat)

def derivedHomologyIso (C : ChainComplex (ModuleCat.{u} k) ℕ) (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat k) (-(n : ℤ))).obj (derivedObject C) ≅
      C.homology n :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat k) (-(n : ℤ))).app _ ≪≫
    C.extendHomologyIso ComplexShape.embeddingDownNat rfl

variable (M : PDMinimal.FiniteModule k A) (P : ProjectiveResolution M.cat)

/-- A supplied actual derived bar comparison and bounded residue cohomology
imply finite projective dimension. The comparison is an explicit input. -/
theorem finite_pd_of_derived_iso
    (Z : DerivedCategory (ModuleCat.{u} k))
    (e : derivedObject (tensorComplex M (PDTensor.Residue (A := A)) P) ≅ Z)
    (h : ∃ b : ℕ, ∀ n, b < n → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat k) (-(n : ℤ))).obj Z)) :
    projectiveDimension M.cat < ⊤ := by
  apply PDTensor.finite_pd_of_resolution M P
  obtain ⟨b,hb⟩ := h
  refine ⟨b, fun n hn => ?_⟩
  exact (hb n hn).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat k) (-(n : ℤ))).mapIso e.symm ≪≫
      derivedHomologyIso _ n).symm

variable (U : Type u) [AddCommGroup U] [Module k U] [Module Aᵐᵒᵖ U]

/-- Nonzero cohomology of a retract of the supplied actual derived bar object
provides the lower pd bound. Inclusion and projection retain the summand data. -/
theorem lower_bound_of_derived_retract
    (Z T : DerivedCategory (ModuleCat.{u} k))
    (e : derivedObject (tensorComplex M U P) ≅ Z)
    (i : T ⟶ Z) (p : Z ⟶ T) (hip : i ≫ p = 𝟙 T)
    (r n : ℕ) (hrn : r ≤ n)
    (h : ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat k) (-(n : ℤ))).obj T)) :
    r ≤ projectiveDimension M.cat := by
  apply PDTensor.lower_bound_of_resolution M U P r n hrn
  intro hz
  let F := DerivedCategory.homologyFunctor (ModuleCat k) (-(n : ℤ))
  have hz' : IsZero (F.obj Z) := hz.of_iso
    (F.mapIso e.symm ≪≫ derivedHomologyIso _ n)
  apply h
  apply (IsZero.iff_id_eq_zero _).mpr
  have he : F.map i ≫ F.map p = 𝟙 (F.obj T) := by rw [← F.map_comp, hip, F.map_id]
  rw [← he, hz'.eq_of_tgt (F.map i) 0, zero_comp]
end LittleFinitistic.PDBar

end

end OAI

end

section

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.PDBarQuotient
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
variable (f : A →ₐ[k] D)
variable (N : Type u) [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
variable [FiniteDimensional k A] [FiniteDimensional k N]

/-- Restriction of scalars preserves the actual homology of a D-complex. -/
def restrictHomologyIso (C : ChainComplex (ModuleCat.{u} D) ℕ) (n : ℕ) :
    (((ModuleCat.restrictScalars (algebraMap k D)).mapHomologicalComplex _).obj C).homology n ≅
      (ModuleCat.restrictScalars (algebraMap k D)).obj (C.homology n) :=
  by
    let F : ModuleCat.{u} D ⥤ ModuleCat.{u} k := ModuleCat.restrictScalars (algebraMap k D)
    letI : F.PreservesHomology := Functor.preservesHomology_of_preservesMonos_and_cokernels F
    exact (C.sc n).mapHomologyIso F

/-- Actual nonzero D-module bar homology, with its exterior action intact,
forces the same projective-dimension lower bound over A. -/
theorem lower_bound_of_base_bar (r n : ℕ) (hrn : r ≤ n)
    (h : ¬ IsZero ((DerivedBar.twoSidedComplex k A D N f).homology n)) :
    r ≤ projectiveDimension (ModuleCat.of A N) := by
  apply PDTensor.lower_bound_of_nonzero_Tor (RightBase f) (PDMinimal.FiniteModule.of (k := k) (A := A) N) r n hrn
  intro hz
  have hz' := hz.of_iso ((torIsoTwoSided f N n) ≪≫
    restrictHomologyIso (DerivedBar.twoSidedComplex k A D N f) n).symm
  apply h
  have hs := (ModuleCat.isZero_iff_subsingleton (R := k)).mp hz'
  exact ModuleCat.isZero_iff_subsingleton.mpr hs

local instance : HasDerivedCategory.{u+1} (ModuleCat.{u} D) :=
  HasDerivedCategory.standard (ModuleCat.{u} D)

abbrev baseDerived := DerivedCategory.Q.obj
  ((DerivedBar.twoSidedComplex k A D N f).extend ComplexShape.embeddingDownNat)

def baseDerivedHomologyIso (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat D) (-(n : ℤ))).obj (baseDerived f N) ≅
      (DerivedBar.twoSidedComplex k A D N f).homology n :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat D) (-(n : ℤ))).app _ ≪≫
    (DerivedBar.twoSidedComplex k A D N f).extendHomologyIso ComplexShape.embeddingDownNat rfl

/-- Consumer of an actual D-linear derived bar splitting. No splitting or
nonzero-iterate theorem is assumed implicitly; the iso, retract and class are inputs. -/
theorem lower_bound_of_base_derived_retract
    (Z T : DerivedCategory (ModuleCat.{u} D)) (e : baseDerived f N ≅ Z)
    (i : T ⟶ Z) (p : Z ⟶ T) (hip : i ≫ p = 𝟙 T)
    (r n : ℕ) (hrn : r ≤ n)
    (h : ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat D) (-(n : ℤ))).obj T)) :
    r ≤ projectiveDimension (ModuleCat.of A N) := by
  apply lower_bound_of_base_bar f N r n hrn
  intro hz
  let F := DerivedCategory.homologyFunctor (ModuleCat D) (-(n : ℤ))
  have hz' : IsZero (F.obj Z) := hz.of_iso (F.mapIso e.symm ≪≫ baseDerivedHomologyIso f N n)
  apply h
  apply (IsZero.iff_id_eq_zero _).mpr
  have he : F.map i ≫ F.map p = 𝟙 (F.obj T) := by rw [← F.map_comp, hip, F.map_id]
  rw [← he, hz'.eq_of_tgt (F.map i) 0, zero_comp]
end LittleFinitistic.PDBarQuotient

end

end OAI

end

section

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace DerivedBar.ProjectiveTail
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
variable (K : ChainComplex C ℕ)

abbrev cyclesSequence (i : ℕ) : ShortComplex C :=
  ShortComplex.mk (K.iCycles (i+1)) (K.toCycles (i+1) i) (by
    rw [← cancel_mono (K.iCycles i), Category.assoc, K.toCycles_i,
      K.iCycles_d, zero_comp])

def cyclesSequenceKernel (i : ℕ) :
    IsLimit (KernelFork.ofι (cyclesSequence K i).f (cyclesSequence K i).zero) := by
  refine isLimitAux _ (fun s => K.liftCycles s.ι i (by simp) ?_) ?_ ?_
  · calc
      s.ι ≫ K.d (i+1) i = (s.ι ≫ K.toCycles (i+1) i) ≫ K.iCycles i := by simp only [Category.assoc, K.toCycles_i]
      _ = 0 := by rw [show s.ι ≫ K.toCycles (i+1) i = 0 from s.condition]; simp
  · intro s
    exact K.liftCycles_i _ _ _ _
  · intro s m hm
    apply (cancel_mono (K.iCycles (i+1))).mp
    exact hm.trans (K.liftCycles_i _ _ _ _).symm

theorem cyclesSequence_exact (i : ℕ) : (cyclesSequence K i).Exact :=
  ShortComplex.exact_of_f_is_kernel _ (cyclesSequenceKernel K i)

theorem cyclesSequence_shortExact (i : ℕ) (h : K.ExactAt i) :
    (cyclesSequence K i).ShortExact := by
  have : Epi (K.toCycles (i+1) i) := by
    have hs : (K.sc' (i+1) i ((ComplexShape.down ℕ).next i)).Exact :=
      (K.exactAt_iff' (i+1) i _ (by simp) rfl).mp h
    have hf : K.toCycles (i+1) i ≫
        (K.cyclesIsoSc' (i+1) i _ (by simp) rfl).hom =
        (K.sc' (i+1) i ((ComplexShape.down ℕ).next i)).toCycles := by
      exact K.toCycles_cyclesIsoSc'_hom _ _ _ _ _
    apply (epi_comp_iff_of_isIso (K.toCycles (i+1) i)
      (K.cyclesIsoSc' (i+1) i _ (by simp) rfl).hom).mp
    rw [hf]
    exact hs.epi_toCycles
  have : Mono (cyclesSequence K i).f := inferInstanceAs (Mono (K.iCycles (i+1)))
  have : Epi (cyclesSequence K i).g := inferInstanceAs (Epi (K.toCycles (i+1) i))
  exact ⟨cyclesSequence_exact K i⟩

/-- In an exact tail of projective terms, projective dimension drops by one
at each successive cycle. This does not identify free terms with finite length. -/
theorem cycles_projective (a g : ℕ)
    (he : ∀ i, a ≤ i → K.ExactAt i)
    (hp : ∀ i, Projective (K.X i))
    (hd : HasProjectiveDimensionLE (K.cycles a) g) :
    Projective (K.cycles (a+g)) := by
  induction g generalizing a with
  | zero => simpa using (projective_iff_hasProjectiveDimensionLE_zero _).mpr hd
  | succ g ih =>
    have hs := cyclesSequence_shortExact K a (he a le_rfl)
    have : Projective (cyclesSequence K a).X₂ := hp (a+1)
    have hnext : HasProjectiveDimensionLE (K.cycles (a+1)) g :=
      (hs.hasProjectiveDimensionLT_X₃_iff g inferInstance).mp hd
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (a+1) (fun i hi => he i (by omega)) hnext
end DerivedBar.ProjectiveTail

end

end OAI

end

section

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive CategoryTheory.Category
namespace DerivedBar.ProjectiveTail
universe u v u' v'
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {E : Type u'} [Category.{v'} E] [Abelian E]

/-- A local contracting identity forces exactness, without assumptions on the
first or third term. -/
theorem exact_of_local_contraction (S : ShortComplex C)
    (a : S.X₂ ⟶ S.X₁) (b : S.X₃ ⟶ S.X₂)
    (h : a ≫ S.f + S.g ≫ b = 𝟙 _) : S.Exact := by
  apply S.exact_iff_epi_toCycles.mpr
  have : IsSplitEpi S.toCycles := ⟨⟨{
    section_ := S.iCycles ≫ a
    id := by
      apply (cancel_mono S.iCycles).mp
      rw [Category.assoc, S.toCycles_i]
      have hh := congrArg (fun f => S.iCycles ≫ f) h
      simpa only [comp_add, Category.assoc, S.iCycles_g_assoc, zero_comp,
        add_zero, comp_id, id_comp] using hh }⟩⟩
  infer_instance

variable (K : ChainComplex C ℕ)

/-- Three adjacent split cycle sequences contract the middle degree. -/
theorem contraction_of_splittings (n : ℕ)
    (s0 : (cyclesSequence K n).Splitting)
    (s1 : (cyclesSequence K (n+1)).Splitting)
    (s2 : (cyclesSequence K (n+2)).Splitting) :
    (s1.r ≫ s2.s) ≫ K.d (n+3) (n+2) +
      K.d (n+2) (n+1) ≫ (s0.r ≫ s1.s) = 𝟙 (K.X (n+2)) := by
  have hleft : (s1.r ≫ s2.s) ≫ K.d (n+3) (n+2) =
      s1.r ≫ (cyclesSequence K (n+1)).f := by
    rw [← K.toCycles_i (n+3) (n+2)]
    change (s1.r ≫ s2.s) ≫ (cyclesSequence K (n+2)).g ≫
      (cyclesSequence K (n+1)).f = _
    simp only [Category.assoc, s2.s_g_assoc]
  have hright : K.d (n+2) (n+1) ≫ (s0.r ≫ s1.s) =
      (cyclesSequence K (n+1)).g ≫ s1.s := by
    rw [← K.toCycles_i (n+2) (n+1)]
    change ((cyclesSequence K (n+1)).g ≫ (cyclesSequence K n).f) ≫
      (s0.r ≫ s1.s) = _
    simp only [Category.assoc, s0.f_r_assoc]
  rw [hleft, hright]
  exact s1.id

/-- Every additive functor preserves exactness in such a split tail. -/
theorem map_exact_of_splittings (F : C ⥤ E) [F.Additive] (n : ℕ)
    (s0 : (cyclesSequence K n).Splitting)
    (s1 : (cyclesSequence K (n+1)).Splitting)
    (s2 : (cyclesSequence K (n+2)).Splitting) :
    ((F.mapHomologicalComplex (.down ℕ)).obj K).ExactAt (n+2) := by
  let L := (F.mapHomologicalComplex (.down ℕ)).obj K
  apply (L.exactAt_iff' (n+3) (n+2) (n+1) (by simp) (by simp)).mpr
  apply exact_of_local_contraction _ (F.map (s1.r ≫ s2.s)) (F.map (s0.r ≫ s1.s))
  change F.map (s1.r ≫ s2.s) ≫ F.map (K.d (n+3) (n+2)) +
    F.map (K.d (n+2) (n+1)) ≫ F.map (s0.r ≫ s1.s) = 𝟙 _
  rw [← F.map_comp, ← F.map_comp, ← F.map_add, contraction_of_splittings K n s0 s1 s2,
    F.map_id]

/-- A global dimension bound makes the exact projective tail split, uniformly
for every additive functor. The harmless two-degree allowance avoids boundary
conventions and suffices for finite cohomological amplitude. -/
theorem map_exact_tail (F : C ⥤ E) [F.Additive] (a g : ℕ)
    (he : ∀ i, a ≤ i → K.ExactAt i)
    (hp : ∀ i, Projective (K.X i))
    (hg : ∀ M : C, HasProjectiveDimensionLE M g)
    (n : ℕ) (hn : a+g+2 ≤ n) :
    ((F.mapHomologicalComplex (.down ℕ)).obj K).ExactAt n := by
  have hc (i : ℕ) (hi : a+g ≤ i) : Projective (K.cycles i) := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hi
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      cycles_projective K (a+t) g (fun j hj => he j (by omega)) hp (hg _)
  let split (i : ℕ) (hi : a+g ≤ i) : (cyclesSequence K i).Splitting := by
    haveI : Projective (cyclesSequence K i).X₃ := hc i hi
    exact (cyclesSequence_shortExact K i (he i (by omega))).splittingOfProjective
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    map_exact_of_splittings K F (a+g+t)
      (split _ (by omega)) (split _ (by omega)) (split _ (by omega))
end DerivedBar.ProjectiveTail

end

end OAI

end

section

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits TensorProduct
open scoped TensorProduct
namespace LittleFinitistic.PDResidueAssociativity
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]

/-- Scalar restriction coherence for an arbitrary right tensor factor. -/
def scalarTensorEquiv {R : Type u} [Ring R] [Algebra k R]
    (U V : Type u) [AddCommGroup U] [Module k U] [Module Rᵐᵒᵖ U]
    [AddCommGroup V] [Module k V] [Module R V] [IsScalarTower k R V] :
    (PDTensor.tensorFunctor k R U).obj (ModuleCat.of R V) ≃ₗ[k] BalancedTensor.Tensor k R U V :=
  LinearEquiv.ofLinearMap
    (PDTensor.mapRight (k := k) (M := PDTensor.ScalarModule k R (ModuleCat.of R V)) (N := V) U LinearMap.id)
    (PDTensor.mapRight (k := k) (M := V) (N := PDTensor.ScalarModule k R (ModuleCat.of R V)) U LinearMap.id)
    (by apply BalancedTensor.ext; intros; rfl) (by apply BalancedTensor.ext; intros; rfl)

variable (f : A →ₐ[k] D)
variable (V : Type u) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]

def objectIso : (PDTensor.tensorFunctor k A (PDResidueProjection.InflatedResidue f)).obj (ModuleCat.of A V) ≅
    (PDTensor.tensorFunctor k D (PDTensor.Residue (A := D))).obj (ModuleCat.of D (DerivedBar.Balanced.tensor f V)) :=
  (((scalarTensorEquiv (PDResidueProjection.InflatedResidue f) V).trans (equiv f V).symm).trans
    (scalarTensorEquiv (PDTensor.Residue (A := D)) (DerivedBar.Balanced.tensor f V)).symm).toModuleIso

variable {V} {W : Type u} [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
theorem objectIso_natural (h : V →ₗ[A] W) :
    (PDTensor.tensorFunctor k A (PDResidueProjection.InflatedResidue f)).map (ModuleCat.ofHom h) ≫ (objectIso f W).hom =
      (objectIso f V).hom ≫ (PDTensor.tensorFunctor k D (PDTensor.Residue (A := D))).map
        (ModuleCat.ofHom (DerivedBar.Balanced.map f V W h)) := by
  apply ModuleCat.hom_ext
  apply BalancedTensor.ext
  intro s v
  rfl

variable (N : Type u) [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

def barIso :
    ((PDTensor.tensorFunctor k A (PDResidueProjection.InflatedResidue f)).mapHomologicalComplex _).obj (DerivedBar.projectiveResolution k A N).complex ≅
      ((PDTensor.tensorFunctor k D (PDTensor.Residue (A := D))).mapHomologicalComplex _).obj (DerivedBar.tensorBarComplex k A D N f) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => objectIso f (DerivedBar.term k A N (n+1))) (by
    intro i j hij
    change j+1=i at hij
    subst i
    simp only [DerivedBar.tensorBarComplex, DerivedBar.projectiveResolution, DerivedBar.complex,
      ChainComplex.of_d, Functor.mapHomologicalComplex_obj_d]
    exact (objectIso_natural f (DerivedBar.differential k A N (j+1))).symm)

def twoSidedIso :
    ((PDTensor.tensorFunctor k A (PDResidueProjection.InflatedResidue f)).mapHomologicalComplex _).obj (DerivedBar.projectiveResolution k A N).complex ≅
      ((PDTensor.tensorFunctor k D (PDTensor.Residue (A := D))).mapHomologicalComplex _).obj (DerivedBar.twoSidedComplex k A D N f) :=
  barIso f N ≪≫ ((PDTensor.tensorFunctor k D (PDTensor.Residue (A := D))).mapHomologicalComplex _).mapIso
    (DerivedBar.tensorBarIso k A D N f)

variable (hf : Function.Surjective f)
variable (hsq : ∀ a ∈ RingHom.ker f.toRingHom, ∀ b ∈ RingHom.ker f.toRingHom, a*b=0)

/-- Actual residue Tor is computed by tensoring the free D-bar with D/rad D.
This proves the needed change-of-rings comparison on the actual models. -/
def residueTorIso (n : ℕ) : PDTensor.Tor (k := k) (PDTensor.Residue (A := A)) (ModuleCat.of A N) n ≅
    (((PDTensor.tensorFunctor k D (PDTensor.Residue (A := D))).mapHomologicalComplex _).obj
      (DerivedBar.twoSidedComplex k A D N f)).homology n :=
  PDResidueProjection.torIso f hf hsq (ModuleCat.of A N) (DerivedBar.projectiveResolution k A N) n ≪≫
    (DerivedBar.projectiveResolution k A N).isoLeftDerivedObj (PDTensor.tensorFunctor k A (PDResidueProjection.InflatedResidue f)) n ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso (twoSidedIso f N)

/-- The actual D-bar has projective terms, even when its length is infinite. -/
theorem twoSided_projective (n : ℕ) : Projective ((DerivedBar.twoSidedComplex k A D N f).X n) := by
  have : Module.Free D (D ⊗[k] DerivedBar.term k A N n) :=
    Module.Free.of_basis (Algebra.TensorProduct.basis D (Module.Free.chooseBasis k (DerivedBar.term k A N n)))
  change Projective (ModuleCat.of D (D ⊗[k] DerivedBar.term k A N n))
  infer_instance

include hf hsq

variable [FiniteDimensional k A] [FiniteDimensional k N]

/-- Bounded D-derived bar homology suffices for finite pd over A. The
exact-tail theorem supplies the amplitude after residue tensor. -/
theorem finite_pd_of_bounded_base_bar (g : ℕ) (hg : ∀ M : ModuleCat.{u} D, HasProjectiveDimensionLE M g)
    (h : ∃ b : ℕ, ∀ n, b < n → IsZero ((DerivedBar.twoSidedComplex k A D N f).homology n)) :
    projectiveDimension (ModuleCat.of A N) < ⊤ := by
  apply PDTensor.projectiveDimension_lt_top_of_bounded_residueTor (PDMinimal.FiniteModule.of (k := k) (A := A) N)
  obtain ⟨b,hb⟩ := h
  refine ⟨b+g+3, fun n hn => ?_⟩
  have he : ∀ i, b+1 ≤ i → (DerivedBar.twoSidedComplex k A D N f).ExactAt i := by
    intro i hi
    exact ((DerivedBar.twoSidedComplex k A D N f).exactAt_iff_isZero_homology i).mpr (hb i (by omega))
  have ht := DerivedBar.ProjectiveTail.map_exact_tail (DerivedBar.twoSidedComplex k A D N f)
    (PDTensor.tensorFunctor k D (PDTensor.Residue (A := D))) (b+1) g he (twoSided_projective f N) hg n (by omega)
  exact ht.isZero_homology.of_iso (residueTorIso f N hf hsq n)

local instance : HasDerivedCategory.{u+1} (ModuleCat.{u} D) := HasDerivedCategory.standard (ModuleCat.{u} D)

theorem finite_pd_of_base_derived_iso (g : ℕ) (hg : ∀ M : ModuleCat.{u} D, HasProjectiveDimensionLE M g)
    (Z : DerivedCategory (ModuleCat.{u} D)) (e : PDBarQuotient.baseDerived f N ≅ Z)
    (h : ∃ b : ℕ, ∀ n, b < n → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat D) (-(n : ℤ))).obj Z)) :
    projectiveDimension (ModuleCat.of A N) < ⊤ := by
  apply finite_pd_of_bounded_base_bar f N hf hsq g hg
  obtain ⟨b,hb⟩ := h
  refine ⟨b,fun n hn => ?_⟩
  exact (hb n hn).of_iso
    (((DerivedCategory.homologyFunctor (ModuleCat D) (-(n : ℤ))).mapIso e.symm) ≪≫
      PDBarQuotient.baseDerivedHomologyIso f N n).symm
end LittleFinitistic.PDResidueAssociativity

end

end OAI

end

section

/- Upper detector leaf H2 of the mo-438166 reduction. Uses OpenAI,
openai/math at 3344da59 (Apache-2.0) via the private port; MathOverflow
question 438166 by Finitistic dimension (CC BY-SA). -/
namespace OMA.R_mo_438166_R1.Upper
open CategoryTheory CategoryTheory.Limits OAI
noncomputable section

section Adj
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (i : R →ₐ[k] S)

theorem unit_natural {V W : ModuleCat.{0} R} (h : V ⟶ W) :
    DerivedBar.Induction.unit i V ≫
        (ModuleCat.restrictScalars i.toRingHom).map ((DerivedBar.Balanced.tensorFunctor i).map h) =
      h ≫ DerivedBar.Induction.unit i W := by
  ext v
  rfl

/-- Balanced induction is left adjoint to restriction. -/
def indAdj : DerivedBar.Balanced.tensorFunctor i ⊣ ModuleCat.restrictScalars i.toRingHom :=
  Adjunction.mkOfHomEquiv
  { homEquiv := fun V N =>
      { toFun := fun φ => DerivedBar.Induction.unit i V ≫ (ModuleCat.restrictScalars i.toRingHom).map φ
        invFun := fun h => DerivedBar.Induction.extend i h
        left_inv := fun φ => DerivedBar.Induction.from_ext i _ _ (DerivedBar.Induction.extend_unit i _)
        right_inv := fun h => DerivedBar.Induction.extend_unit i h }
    homEquiv_naturality_left_symm := by
      intro V V' N h g
      apply DerivedBar.Induction.from_ext i
      dsimp only [Equiv.coe_fn_symm_mk]
      rw [DerivedBar.Induction.extend_unit, Functor.map_comp, ← Category.assoc, unit_natural,
        Category.assoc, DerivedBar.Induction.extend_unit]
    homEquiv_naturality_right := by
      intro V N N' φ g
      dsimp only [Equiv.coe_fn_mk]
      rw [Functor.map_comp, Category.assoc] }
end Adj

def derivedIso {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasProjectiveResolutions C] {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ≅ G) (n : ℕ)
    (X : C) : (F.leftDerived n).obj X ≅ (G.leftDerived n).obj X where
  hom := (NatTrans.leftDerived α.hom n).app X
  inv := (NatTrans.leftDerived α.inv n).app X
  hom_inv_id := by
    rw [← NatTrans.comp_app, ← NatTrans.leftDerived_comp, α.hom_inv_id, NatTrans.leftDerived_id]
    rfl
  inv_hom_id := by
    rw [← NatTrans.comp_app, ← NatTrans.leftDerived_comp, α.inv_hom_id, NatTrans.leftDerived_id]
    rfl

theorem upper : H2 := by
  intro A _ _ D _ e g F _ fin surj sq gd adj N hN hb
  obtain ⟨adj⟩ := adj
  obtain ⟨b, hb⟩ := hb
  let _ : Algebra ℂ D := (e.comp (algebraMap ℂ A)).toAlgebra' (by
    intro c d
    obtain ⟨a, rfl⟩ := surj d
    change e (algebraMap ℂ A c) * e a = e a * e (algebraMap ℂ A c)
    rw [← map_mul, ← map_mul, Algebra.commutes])
  let f : A →ₐ[ℂ] D := { e with commutes' := fun _ => rfl }
  let α : F ≅ DerivedBar.Balanced.tensorFunctor f :=
    adj.leftAdjointUniq (indAdj f : DerivedBar.Balanced.tensorFunctor f ⊣ ModuleCat.restrictScalars e)
  let _ : Module ℂ N := DerivedBar.BimoduleTensor.scalarModule ℂ A N
  have : IsScalarTower ℂ A N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  have : FiniteDimensional ℂ A := fin
  have : Module.Finite A N := hN
  have : FiniteDimensional ℂ N := Module.Finite.trans A N
  have hsq : ∀ a ∈ RingHom.ker f.toRingHom, ∀ c ∈ RingHom.ker f.toRingHom, a*c = 0 :=
    fun a ha c hc => sq a c ha hc
  have := LittleFinitistic.PDResidueAssociativity.finite_pd_of_bounded_base_bar f N surj hsq g gd
    ⟨b, fun n hn => (hb n hn).of_iso
      (((derivedIso α n (ModuleCat.of A N)) ≪≫ DerivedBar.Balanced.tensorBarHomologyIso f N n ≪≫
        (HomologicalComplex.homologyFunctor (ModuleCat.{0} D) (.down ℕ) n).mapIso
          (DerivedBar.tensorBarIso ℂ A D N f)).symm)⟩
  exact this

end
end OMA.R_mo_438166_R1.Upper

end

theorem OMA.solution : OMA.R_mo_438166_R1.H2 := OMA.R_mo_438166_R1.Upper.upper
