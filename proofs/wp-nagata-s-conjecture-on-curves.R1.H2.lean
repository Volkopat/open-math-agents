import OMAReductions.R_wp_nagata_s_conjecture_on_curves_R1
import Mathlib
-- Square incidence proof adapted from OpenAI, openai/math 3344da59991ed94f9ba711217b29c1d760badfa6.
noncomputable section
namespace OAI.Nagata.AffineMultiplicity
variable {σ K : Type*} [CommRing K]
noncomputable def pointIdeal (p : σ → K) : Ideal (MvPolynomial σ K) :=
  RingHom.ker (MvPolynomial.eval p)
end OAI.Nagata.AffineMultiplicity

namespace OAI.Nagata.AffineMultiplicity
variable {σ K : Type*} [CommRing K]
def orderAtLeast (p : σ → K) (m : ℕ) (f : MvPolynomial σ K) : Prop :=
  f ∈ pointIdeal p ^ m
end OAI.Nagata.AffineMultiplicity

namespace OAI.Nagata.AffineMultiplicity
variable {σ K : Type*} [CommRing K]
@[simp] theorem orderAtLeast_zero (p : σ → K) (f : MvPolynomial σ K) :
    orderAtLeast p 0 f := by
  simp [orderAtLeast]
end OAI.Nagata.AffineMultiplicity

namespace OAI.Nagata.AffineMultiplicity
variable {σ K : Type*} [CommRing K]
theorem orderAtLeast_mul {p : σ → K} {m n : ℕ} {f g : MvPolynomial σ K}
    (hf : orderAtLeast p m f) (hg : orderAtLeast p n g) :
    orderAtLeast p (m + n) (f * g) := by
  change f * g ∈ pointIdeal p ^ (m + n)
  rw [pow_add]
  exact Ideal.mul_mem_mul hf hg
end OAI.Nagata.AffineMultiplicity

namespace OAI.Nagata.AffineMultiplicity
variable {σ K : Type*} [CommRing K]
theorem orderAtLeast_pow {p : σ → K} {m : ℕ} {f : MvPolynomial σ K}
    (hf : orderAtLeast p m f) (N : ℕ) : orderAtLeast p (m * N) (f ^ N) := by
  change f ^ N ∈ pointIdeal p ^ (m * N)
  rw [pow_mul]
  exact Ideal.pow_mem_pow hf N
end OAI.Nagata.AffineMultiplicity

namespace OAI.Nagata.ProjectiveGeometry
open scoped BigOperators
abbrev PlanePoint := Projectivization ℂ (Fin 3 → ℂ)
end OAI.Nagata.ProjectiveGeometry

namespace OAI.Nagata.ProjectiveGeometry
open scoped BigOperators
abbrev OrderedDistinctPoints (r : ℕ) :=
  {p : Fin r → PlanePoint // Function.Injective p}
end OAI.Nagata.ProjectiveGeometry

namespace OAI.Nagata.ProjectiveGeometry
open scoped BigOperators
abbrev ChartVariables (c : Fin 3) := {j : Fin 3 // j ≠ c}
end OAI.Nagata.ProjectiveGeometry

namespace OAI.Nagata.ProjectiveGeometry
open scoped BigOperators
def dehomogenize (c : Fin 3) (F : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial (ChartVariables c) ℂ :=
  MvPolynomial.eval₂ MvPolynomial.C
    (fun j => if h : j = c then 1 else MvPolynomial.X ⟨j, h⟩) F
end OAI.Nagata.ProjectiveGeometry

namespace OAI.Nagata.ProjectiveGeometry
open scoped BigOperators
def chartCoordinates (c : Fin 3) (p : PlanePoint) : ChartVariables c → ℂ :=
  fun j => p.rep j.val / p.rep c
end OAI.Nagata.ProjectiveGeometry

namespace OAI.Nagata.ProjectiveGeometry
open scoped BigOperators
def multiplicityAtLeast (F : MvPolynomial (Fin 3) ℂ)
    (p : PlanePoint) (m : ℕ) : Prop :=
  ∀ c : Fin 3, p.rep c ≠ 0 →
    AffineMultiplicity.orderAtLeast (chartCoordinates c p) m (dehomogenize c F)
end OAI.Nagata.ProjectiveGeometry

namespace OAI.Nagata.ProjectiveGeometry
open scoped BigOperators
theorem dehomogenize_mul (c : Fin 3) (F G : MvPolynomial (Fin 3) ℂ) :
    dehomogenize c (F * G) = dehomogenize c F * dehomogenize c G := by
  exact MvPolynomial.eval₂_mul _ _
end OAI.Nagata.ProjectiveGeometry

namespace OAI.Nagata.ProjectiveGeometry
open scoped BigOperators
theorem dehomogenize_pow (c : Fin 3) (F : MvPolynomial (Fin 3) ℂ) (N : ℕ) :
    dehomogenize c (F ^ N) = dehomogenize c F ^ N := by
  exact MvPolynomial.eval₂_pow _ _
end OAI.Nagata.ProjectiveGeometry

namespace OAI.Nagata.ProjectiveGeometry
open scoped BigOperators
theorem multiplicityAtLeast_zero (F : MvPolynomial (Fin 3) ℂ)
    (p : PlanePoint) : multiplicityAtLeast F p 0 := by
  intro c hc
  exact AffineMultiplicity.orderAtLeast_zero _ _
end OAI.Nagata.ProjectiveGeometry

namespace OAI.Nagata.ProjectiveGeometry
open scoped BigOperators
theorem multiplicityAtLeast_mul {F G : MvPolynomial (Fin 3) ℂ}
    {p : PlanePoint} {m n : ℕ} (hF : multiplicityAtLeast F p m)
    (hG : multiplicityAtLeast G p n) : multiplicityAtLeast (F * G) p (m + n) := by
  intro c hc
  rw [dehomogenize_mul]
  exact AffineMultiplicity.orderAtLeast_mul (hF c hc) (hG c hc)
end OAI.Nagata.ProjectiveGeometry

namespace OAI.Nagata.ProjectiveGeometry
open scoped BigOperators
theorem multiplicityAtLeast_pow {F : MvPolynomial (Fin 3) ℂ}
    {p : PlanePoint} {m : ℕ} (hF : multiplicityAtLeast F p m) (N : ℕ) :
    multiplicityAtLeast (F ^ N) p (m * N) := by
  intro c hc
  rw [dehomogenize_pow]
  exact AffineMultiplicity.orderAtLeast_pow (hF c hc) N
end OAI.Nagata.ProjectiveGeometry

namespace OAI.Nagata.W16
abbrev PlanePolynomial := MvPolynomial (Fin 3) ℂ
end OAI.Nagata.W16

namespace OAI.Nagata.W16
structure NonzeroHomogeneousForm (d : ℕ) where
  polynomial : PlanePolynomial
  homogeneous : polynomial.IsHomogeneous d
  nonzero : polynomial ≠ 0
end OAI.Nagata.W16

namespace OAI.Nagata.W16.NonzeroHomogeneousForm
def pow {d : ℕ} (F : NonzeroHomogeneousForm d) (N : ℕ) :
    NonzeroHomogeneousForm (d * N) where
  polynomial := F.polynomial ^ N
  homogeneous := F.homogeneous.pow N
  nonzero := pow_ne_zero N F.nonzero
end OAI.Nagata.W16.NonzeroHomogeneousForm

namespace OAI.Nagata.W16
open scoped BigOperators
theorem finite_product_forms {ι : Type*} (s : Finset ι)
    (F : ι → PlanePolynomial) (d : ι → ℕ)
    (hhom : ∀ i ∈ s, (F i).IsHomogeneous (d i))
    (hne : ∀ i ∈ s, F i ≠ 0) :
    (∏ i ∈ s, F i) ≠ 0 ∧
      (∏ i ∈ s, F i).IsHomogeneous (∑ i ∈ s, d i) ∧
      (∏ i ∈ s, F i).totalDegree = ∑ i ∈ s, d i := by
  classical
  have hp : (∏ i ∈ s, F i) ≠ 0 := Finset.prod_ne_zero_iff.mpr hne
  have hh := MvPolynomial.IsHomogeneous.prod s F d hhom
  exact ⟨hp, hh, hh.totalDegree hp⟩
end OAI.Nagata.W16

namespace OAI.Nagata.Workers.W14
theorem multiplicity_sum_pos {r d s : ℕ} (hr : 0 < r) (hd : 0 < d)
    (h : (d : ℝ) * Real.sqrt r ≤ s) : 0 < s := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hs' : (0 : ℝ) < s :=
    lt_of_lt_of_le (mul_pos hd' (Real.sqrt_pos.2 hr')) h
  exact_mod_cast hs'
end OAI.Nagata.Workers.W14

namespace OAI.Nagata.Workers.W14
theorem symmetrized_ratio_le {r d s : ℕ} (hs : 0 < s)
    (h : (d : ℝ) * Real.sqrt r ≤ s) :
    (r : ℝ) * d / s ≤ Real.sqrt r := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  apply (div_le_iff₀ hs').2
  calc
    (r : ℝ) * d = Real.sqrt r * ((d : ℝ) * Real.sqrt r) := by
      calc
        (r : ℝ) * d = (d : ℝ) * (Real.sqrt r * Real.sqrt r) := by
          rw [Real.mul_self_sqrt (Nat.cast_nonneg r)]
          exact mul_comm _ _
        _ = _ := by ac_rfl
    _ ≤ Real.sqrt r * s := mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _)
end OAI.Nagata.Workers.W14

namespace OAI.Nagata.Workers.W14
theorem factorial_ratio_eq {r d s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    ((r.factorial * d : ℕ) : ℝ) / (((r - 1).factorial * s : ℕ) : ℝ) =
      (r : ℝ) * d / s := by
  have hf : ((r - 1).factorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero (r - 1))
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [← Nat.mul_factorial_pred hr.ne']
  push_cast
  apply (div_eq_div_iff (mul_ne_zero hf hs') hs').2
  simp only [mul_assoc, mul_comm, mul_left_comm]
end OAI.Nagata.Workers.W14

namespace OAI.Nagata.Workers.W14
theorem factorial_symmetrization {r d s : ℕ} (hr : 0 < r) (hd : 0 < d)
    (h : (d : ℝ) * Real.sqrt r ≤ s) :
    0 < r.factorial * d ∧ 0 < (r - 1).factorial * s ∧
      ((r.factorial * d : ℕ) : ℝ) / (((r - 1).factorial * s : ℕ) : ℝ) ≤
        Real.sqrt r := by
  have hs := multiplicity_sum_pos hr hd h
  refine ⟨Nat.mul_pos (Nat.factorial_pos _) hd,
    Nat.mul_pos (Nat.factorial_pos _) hs, ?_⟩
  rw [factorial_ratio_eq hr hs]
  exact symmetrized_ratio_le hs h
end OAI.Nagata.Workers.W14

namespace OAI.Nagata.Workers.W14
theorem sqrt_nat_square (k : ℕ) : Real.sqrt ((k * k : ℕ) : ℝ) = k := by
  rw [Nat.cast_mul, Real.sqrt_mul_self (Nat.cast_nonneg k)]
end OAI.Nagata.Workers.W14

namespace OAI.Nagata.Workers.W14
theorem sqrt_nat_eq_iff (r k : ℕ) : Real.sqrt (r : ℝ) = k ↔ r = k * k := by
  constructor
  · intro h
    have hs := Real.mul_self_sqrt (Nat.cast_nonneg r)
    rw [h] at hs
    exact_mod_cast hs.symm
  · rintro rfl
    exact sqrt_nat_square k
end OAI.Nagata.Workers.W14

namespace OAI.Nagata.Workers.W14
theorem square_root_ge_four {r k : ℕ} (hr : 10 ≤ r) (hk : r = k * k) : 4 ≤ k := by
  by_contra h
  have hk3 : k ≤ 3 := Nat.le_of_lt_succ (Nat.lt_of_not_ge h)
  have hs : k * k ≤ 9 := by nlinarith
  omega
end OAI.Nagata.Workers.W14

namespace OAI.Nagata.Workers.W14
theorem square_ratio_le_iff {r k d m : ℕ} (hk : r = k * k) (hm : 0 < m) :
    (d : ℝ) / m ≤ Real.sqrt r ↔ d ≤ k * m := by
  rw [(sqrt_nat_eq_iff r k).2 hk]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [div_le_iff₀ hmR]
  norm_cast
end OAI.Nagata.Workers.W14

namespace OAI.Nagata.W13
open scoped BigOperators
theorem permutation_sum_independent {α : Type*} [Fintype α] [DecidableEq α]
    (m : α → ℕ) (i j : α) :
    (∑ σ : Equiv.Perm α, m (σ i)) = ∑ σ : Equiv.Perm α, m (σ j) := by
  apply Fintype.sum_equiv (Equiv.mulRight (Equiv.swap i j))
  intro σ
  simp [Equiv.Perm.mul_apply]
end OAI.Nagata.W13

namespace OAI.Nagata.W13
open scoped BigOperators
theorem card_mul_permutation_sum {α : Type*} [Fintype α] [DecidableEq α]
    (m : α → ℕ) (i : α) :
    Fintype.card α * (∑ σ : Equiv.Perm α, m (σ i)) =
      (Fintype.card α).factorial * ∑ j, m j := by
  calc
    Fintype.card α * (∑ σ : Equiv.Perm α, m (σ i)) =
        ∑ j : α, ∑ σ : Equiv.Perm α, m (σ j) := by
      simp_rw [← permutation_sum_independent m i]
      simp
    _ = ∑ σ : Equiv.Perm α, ∑ j : α, m (σ j) := Finset.sum_comm
    _ = ∑ _σ : Equiv.Perm α, ∑ j : α, m j := by
      apply Finset.sum_congr rfl
      intro σ _
      exact Equiv.sum_comp σ m
    _ = (Fintype.card α).factorial * ∑ j, m j := by
      simp [Fintype.card_perm]
end OAI.Nagata.W13

namespace OAI.Nagata.W13
open scoped BigOperators
theorem permutation_sum_multiplicity {r : ℕ} (hr : 0 < r)
    (m : Fin r → ℕ) (i : Fin r) :
    (∑ σ : Equiv.Perm (Fin r), m (σ i)) =
      (r - 1).factorial * ∑ j, m j := by
  apply Nat.eq_of_mul_eq_mul_left hr
  have h := card_mul_permutation_sum m i
  simp only [Fintype.card_fin] at h
  have hfac := Nat.factorial_succ (r - 1)
  rw [Nat.sub_add_cancel hr] at hfac
  rw [h, ← Nat.mul_assoc, ← hfac]
end OAI.Nagata.W13

namespace OAI.Nagata.W13
open ProjectiveGeometry
open scoped BigOperators
def UniversalSupport (r d : ℕ) (m : Fin r → ℕ) : Prop :=
  ∀ p : OrderedDistinctPoints r,
    ∃ F : MvPolynomial (Fin 3) ℂ,
      F ≠ 0 ∧ F.IsHomogeneous d ∧
      ∀ i, multiplicityAtLeast F (p.val i) (m i)
end OAI.Nagata.W13

namespace OAI.Nagata.W13
open ProjectiveGeometry
open scoped BigOperators
theorem multiplicityAtLeast_prod {ι : Type*} (s : Finset ι)
    (p : PlanePoint) (m : ι → ℕ) (F : ι → MvPolynomial (Fin 3) ℂ)
    (h : ∀ i ∈ s, multiplicityAtLeast (F i) p (m i)) :
    multiplicityAtLeast (∏ i ∈ s, F i) p (∑ i ∈ s, m i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using multiplicityAtLeast_zero (1 : MvPolynomial (Fin 3) ℂ) p
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, Finset.prod_insert ha]
      exact multiplicityAtLeast_mul (h a (Finset.mem_insert_self a s))
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))
end OAI.Nagata.W13

namespace OAI.Nagata.W13
open ProjectiveGeometry
open scoped BigOperators
theorem universalSupport_permute {r d : ℕ} {m : Fin r → ℕ}
    (h : UniversalSupport r d m) (σ : Equiv.Perm (Fin r)) :
    UniversalSupport r d (fun i => m (σ i)) := by
  intro p
  obtain ⟨F, hne, hhom, hm⟩ := h
    ⟨fun j => p.val (σ.symm j), p.property.comp σ.symm.injective⟩
  refine ⟨F, hne, hhom, ?_⟩
  intro i
  simpa using hm (σ i)
end OAI.Nagata.W13

namespace OAI.Nagata.W13
open ProjectiveGeometry
open scoped BigOperators
theorem universalSupport_symmetrize {r d : ℕ} (hr : 0 < r)
    {m : Fin r → ℕ} (h : UniversalSupport r d m) :
    UniversalSupport r (r.factorial * d)
      (fun _ => (r - 1).factorial * ∑ i, m i) := by
  classical
  intro p
  have hs : ∀ σ : Equiv.Perm (Fin r),
      ∃ F : MvPolynomial (Fin 3) ℂ,
        F ≠ 0 ∧ F.IsHomogeneous d ∧
          ∀ i, multiplicityAtLeast F (p.val i) (m (σ i)) :=
    fun σ => universalSupport_permute h σ p
  let F := fun σ => Classical.choose (hs σ)
  have hne : ∀ σ, F σ ≠ 0 := fun σ => (Classical.choose_spec (hs σ)).1
  have hhom : ∀ σ, (F σ).IsHomogeneous d :=
    fun σ => (Classical.choose_spec (hs σ)).2.1
  have hm : ∀ σ i, multiplicityAtLeast (F σ) (p.val i) (m (σ i)) :=
    fun σ => (Classical.choose_spec (hs σ)).2.2
  have hp := W16.finite_product_forms Finset.univ F (fun _ => d)
    (fun σ _ => hhom σ) (fun σ _ => hne σ)
  refine ⟨∏ σ, F σ, hp.1, ?_, ?_⟩
  · simpa [Fintype.card_perm] using hp.2.1
  · intro i
    have hi := multiplicityAtLeast_prod Finset.univ (p.val i)
      (fun σ => m (σ i)) F (fun σ _ => hm σ i)
    rw [permutation_sum_multiplicity hr m i] at hi
    exact hi
end OAI.Nagata.W13

namespace OAI.Nagata.W13
open ProjectiveGeometry
open scoped BigOperators
theorem universalSupport_pow {r d : ℕ} {m : Fin r → ℕ}
    (h : UniversalSupport r d m) (N : ℕ) :
    UniversalSupport r (d * N) (fun i => m i * N) := by
  intro p
  obtain ⟨F, hne, hhom, hm⟩ := h p
  exact ⟨F ^ N, pow_ne_zero N hne, hhom.pow N,
    fun i => multiplicityAtLeast_pow (hm i) N⟩
end OAI.Nagata.W13

end
-- Adapted from OpenAI, openai/math 3344da59991ed94f9ba711217b29c1d760badfa6.
-- AffineMultiplicity
namespace OAI
section
namespace Nagata.AffineMultiplicity
variable {σ K : Type*} [CommRing K]
theorem pointIdeal_mem_iff (p : σ → K) (f : MvPolynomial σ K) :
    f ∈ pointIdeal p ↔ MvPolynomial.eval p f = 0 := by
  exact RingHom.mem_ker
theorem pointIdeal_map_of_eval_compatible {τ : Type*}
    (p : σ → K) (q : τ → K)
    (e : MvPolynomial σ K ≃+* MvPolynomial τ K)
    (h : ∀ f, MvPolynomial.eval q (e f) = MvPolynomial.eval p f) :
    Ideal.map e (pointIdeal p) = pointIdeal q := by
  ext g
  rw [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨f, hf, rfl⟩
    rw [pointIdeal_mem_iff, h]
    exact (pointIdeal_mem_iff p f).mp hf
  · intro hg
    refine ⟨e.symm g, ?_, e.apply_symm_apply g⟩
    rw [pointIdeal_mem_iff, ← h, e.apply_symm_apply]
    exact (pointIdeal_mem_iff q g).mp hg
theorem orderAtLeast_equiv_iff {τ : Type*}
    (p : σ → K) (q : τ → K)
    (e : MvPolynomial σ K ≃+* MvPolynomial τ K)
    (h : ∀ f, MvPolynomial.eval q (e f) = MvPolynomial.eval p f)
    (m : ℕ) (f : MvPolynomial σ K) :
    orderAtLeast q m (e f) ↔ orderAtLeast p m f := by
  unfold orderAtLeast
  rw [← pointIdeal_map_of_eval_compatible p q e h, ← Ideal.map_pow]
  exact Ideal.apply_mem_of_equiv_iff
section Field
variable {F : Type*} [Field F]
theorem pointIdeal_isMaximal (p : σ → F) : (pointIdeal p).IsMaximal := by
  apply RingHom.ker_isMaximal_of_surjective (MvPolynomial.eval p)
  intro a
  exact ⟨MvPolynomial.C a, MvPolynomial.eval_C a⟩
end Field
end Nagata.AffineMultiplicity
end
section
namespace Nagata.AffineMultiplicity
section MaximalIdeal
variable {R : Type*} [CommRing R] (I : Ideal R) (hI : I.IsMaximal)
include hI
end MaximalIdeal
section AffinePoint
variable {σ F : Type*} [Field F]
instance pointIdeal_isPrime (p : σ → F) : (pointIdeal p).IsPrime :=
  (pointIdeal_isMaximal p).isPrime
end AffinePoint
end Nagata.AffineMultiplicity
end
end OAI
-- Configuration
namespace OAI
section
noncomputable section
namespace Nagata.ProjectiveGeometry
open scoped BigOperators
theorem chartCoordinates_mk (c : Fin 3) (v : Fin 3 → ℂ) (hv : v ≠ 0) :
    chartCoordinates c (Projectivization.mk ℂ v hv) =
      fun j : ChartVariables c => v j.val / v c := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  funext j
  simp only [chartCoordinates, ← ha, Pi.smul_apply, Units.smul_def, smul_eq_mul]
  exact mul_div_mul_left _ _ a.ne_zero
end Nagata.ProjectiveGeometry
end
end
section
noncomputable section
namespace Nagata
open ProjectiveGeometry
open scoped BigOperators
end Nagata
end
end
section
noncomputable section
namespace Nagata.ProjectiveGeometry
def chartIndexEquiv (c : Fin 3) : Fin 2 ≃ ChartVariables c :=
  Equiv.ofBijective (fun j => ⟨c.succAbove j, Fin.succAbove_ne c j⟩) (by
    constructor
    · intro i j h
      exact Fin.succAbove_right_injective (congrArg Subtype.val h)
    · intro j
      obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq j.property
      exact ⟨i, Subtype.ext hi⟩)
@[simp] theorem chartIndexEquiv_val (c : Fin 3) (j : Fin 2) :
    (chartIndexEquiv c j).val = c.succAbove j := rfl
@[simp] theorem chartIndexEquiv_symm_succAbove (c : Fin 3) (j : Fin 2) :
    (chartIndexEquiv c).symm ⟨c.succAbove j, Fin.succAbove_ne c j⟩ = j :=
  (chartIndexEquiv c).symm_apply_apply j
def chartCoordinates₂ (c : Fin 3) (p : PlanePoint) : Fin 2 → ℂ :=
  fun j => chartCoordinates c p (chartIndexEquiv c j)
def chartDehomogenize₂ (c : Fin 3) (F : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.rename (chartIndexEquiv c).symm (dehomogenize c F)
theorem chartDehomogenize₂_eq_eval₂_insertNth (c : Fin 3)
    (F : MvPolynomial (Fin 3) ℂ) :
    chartDehomogenize₂ c F =
      MvPolynomial.eval₂ MvPolynomial.C (c.insertNth 1 MvPolynomial.X) F := by
  let e : MvPolynomial (Fin 3) ℂ →+* MvPolynomial (Fin 2) ℂ :=
    (MvPolynomial.rename (chartIndexEquiv c).symm).toRingHom.comp
      (MvPolynomial.eval₂Hom MvPolynomial.C
        (fun j => if h : j = c then 1 else MvPolynomial.X ⟨j, h⟩))
  have he : e = MvPolynomial.eval₂Hom MvPolynomial.C (c.insertNth 1 MvPolynomial.X) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [e]
    · intro j
      by_cases hj : j = c
      · subst j
        simp [e]
      · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
        simp [e]
  exact RingHom.congr_fun he F
theorem orderAtLeast_chartDehomogenize₂_iff (c : Fin 3) (p : PlanePoint)
    (F : MvPolynomial (Fin 3) ℂ) (m : ℕ) :
    AffineMultiplicity.orderAtLeast (chartCoordinates₂ c p) m (chartDehomogenize₂ c F) ↔
      AffineMultiplicity.orderAtLeast (chartCoordinates c p) m (dehomogenize c F) := by
  let e := (MvPolynomial.renameEquiv ℂ (chartIndexEquiv c).symm).toRingEquiv
  have he : ∀ f, MvPolynomial.eval (chartCoordinates₂ c p) (e f) =
      MvPolynomial.eval (chartCoordinates c p) f := by
    intro f
    change MvPolynomial.eval (chartCoordinates₂ c p)
      (MvPolynomial.rename (chartIndexEquiv c).symm f) = _
    rw [MvPolynomial.eval_rename]
    have hcoords : chartCoordinates₂ c p ∘ (chartIndexEquiv c).symm =
        chartCoordinates c p := by
      funext j
      simp [chartCoordinates₂]
    rw [hcoords]
  exact AffineMultiplicity.orderAtLeast_equiv_iff
    (chartCoordinates c p) (chartCoordinates₂ c p) e he m (dehomogenize c F)
def chartVector₂ (c : Fin 3) (z : Fin 2 → ℂ) : Fin 3 → ℂ := c.insertNth 1 z
theorem chartVector₂_ne_zero (c : Fin 3) (z : Fin 2 → ℂ) : chartVector₂ c z ≠ 0 := by
  intro h
  have hc := congrFun h c
  simp [chartVector₂] at hc
def chartPoint₂ (c : Fin 3) (z : Fin 2 → ℂ) : PlanePoint :=
  Projectivization.mk ℂ (chartVector₂ c z) (chartVector₂_ne_zero c z)
theorem chartPoint₂_coordinate_ne_zero (c : Fin 3) (z : Fin 2 → ℂ) :
    (chartPoint₂ c z).rep c ≠ 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ
    (chartVector₂ c z) (chartVector₂_ne_zero c z)
  have hcoord : (chartPoint₂ c z).rep c = (a : ℂ) := by
    change (Projectivization.mk ℂ (chartVector₂ c z) (chartVector₂_ne_zero c z)).rep c = _
    rw [← ha]
    simp [chartVector₂, Units.smul_def]
  rw [hcoord]
  exact a.ne_zero
theorem chartCoordinates₂_chartPoint₂ (c : Fin 3) (z : Fin 2 → ℂ) :
    chartCoordinates₂ c (chartPoint₂ c z) = z := by
  funext j
  change chartCoordinates c (Projectivization.mk ℂ (chartVector₂ c z)
    (chartVector₂_ne_zero c z)) (chartIndexEquiv c j) = z j
  rw [chartCoordinates_mk]
  simp [chartVector₂]
theorem chartPoint₂_injective (c : Fin 3) : Function.Injective (chartPoint₂ c) := by
  intro z w h
  have hcoords := congrArg (chartCoordinates₂ c) h
  simpa only [chartCoordinates₂_chartPoint₂] using hcoords
abbrev ConfigurationChart (r : ℕ) := Fin r → Fin 3
def configurationChartEmbedding {r : ℕ} (c : ConfigurationChart r)
    (z : Fin r × Fin 2 → ℂ) : Fin r → PlanePoint :=
  fun i => chartPoint₂ (c i) (fun j => z (i, j))
end Nagata.ProjectiveGeometry
end
end
section
noncomputable section
namespace Nagata.ProjectiveGeometry
open scoped BigOperators
end Nagata.ProjectiveGeometry
end
end
end OAI
-- Forms
namespace OAI
section
noncomputable section
namespace Nagata.W16
theorem homogeneous_eval_scale {σ K : Type*} [CommSemiring K]
    {F : MvPolynomial σ K} {d : ℕ} (hF : F.IsHomogeneous d)
    (x : σ → K) (a : K) :
    MvPolynomial.eval (fun i => a * x i) F = a ^ d * MvPolynomial.eval x F := by
  classical
  simp only [MvPolynomial.eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hF.degree_eq_sum_deg_support hu]
  ac_rfl
namespace NonzeroHomogeneousForm
def mul {d e : ℕ} (F : NonzeroHomogeneousForm d)
    (G : NonzeroHomogeneousForm e) : NonzeroHomogeneousForm (d + e) where
  polynomial := F.polynomial * G.polynomial
  homogeneous := F.homogeneous.mul G.homogeneous
  nonzero := mul_ne_zero F.nonzero G.nonzero
end NonzeroHomogeneousForm
open scoped BigOperators
end Nagata.W16
end
end
section
noncomputable section
namespace Nagata.W16
open scoped BigOperators
def binaryAffine (F : MvPolynomial (Fin 2) ℂ) : Polynomial ℂ :=
  MvPolynomial.eval₂ Polynomial.C (fun i => if i = 0 then Polynomial.X else 1) F
theorem binaryAffine_eq_sum (F : MvPolynomial (Fin 2) ℂ) :
    binaryAffine F = ∑ u ∈ F.support, Polynomial.C (F.coeff u) * Polynomial.X ^ u 0 := by
  classical
  rw [binaryAffine, MvPolynomial.eval₂_eq']
  apply Finset.sum_congr rfl
  intro u _
  simp
theorem binaryAffine_eval (F : MvPolynomial (Fin 2) ℂ) (z : ℂ) :
    (binaryAffine F).eval z = MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z else 1) F := by
  classical
  simp [binaryAffine_eq_sum, MvPolynomial.eval_eq', Polynomial.eval_finsetSum]
theorem binaryAffine_normalized {F : MvPolynomial (Fin 2) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) (x : Fin 2 → ℂ) (hc : x 1 ≠ 0) :
    (binaryAffine F).eval (x 0 / x 1) = (x 1)⁻¹ ^ d * MvPolynomial.eval x F := by
  rw [binaryAffine_eval]
  have hcoords : (fun i : Fin 2 => if i = 0 then x 0 / x 1 else 1) =
      fun i => (x 1)⁻¹ * x i := by
    funext i
    fin_cases i <;> simp [hc, div_eq_mul_inv, mul_comm]
  rw [hcoords]
  exact homogeneous_eval_scale hF x (x 1)⁻¹
theorem binaryAffine_eq_zero_imp {F : MvPolynomial (Fin 2) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) (hf : binaryAffine F = 0) : F = 0 := by
  have hmul : MvPolynomial.X 1 * F = 0 := by
    apply ((MvPolynomial.isHomogeneous_X ℂ (1 : Fin 2)).mul hF).eq_zero_of_forall_eval_eq_zero
    intro x
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_X]
    by_cases hc : x 1 = 0
    · simp [hc]
    · have hval := binaryAffine_normalized hF x hc
      rw [hf, Polynomial.eval_zero] at hval
      have hz : MvPolynomial.eval x F = 0 :=
        (mul_eq_zero.mp hval.symm).resolve_left (pow_ne_zero d (inv_ne_zero hc))
      rw [hz, mul_zero]
  exact (mul_eq_zero.mp hmul).resolve_left (MvPolynomial.X_ne_zero 1)
theorem binaryAffine_ne_zero {F : MvPolynomial (Fin 2) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) (hf : F ≠ 0) : binaryAffine F ≠ 0 := by
  intro hz
  exact hf (binaryAffine_eq_zero_imp hF hz)
end Nagata.W16
end
end
section
namespace Nagata.W16
open Nagata.ProjectiveGeometry
end Nagata.W16
end
section
noncomputable section
namespace Nagata.W16
open Nagata.ProjectiveGeometry
open scoped BigOperators
end Nagata.W16
end
end
end OAI
-- LineObstructions
namespace OAI
section
namespace Nagata.W04.ReducibleSquare
open Polynomial
theorem cycle_products_ne {K : Type*} [Field K] [CharZero K]
    (k t : ℕ) (hk : 0 < k) (ht : 0 < t) :
    (((k : K) + 2) * 3) ^ t ≠ (((k : K) + 3) * 2) ^ t := by
  have hlt : (2 * (k + 3)) ^ t < (3 * (k + 2)) ^ t :=
    Nat.pow_lt_pow_left (by omega) (Nat.ne_of_gt ht)
  intro heq
  have heq' : (3 * (k + 2)) ^ t = (2 * (k + 3)) ^ t := by
    exact_mod_cast (show ((3 : K) * ((k : K) + 2)) ^ t =
      ((2 : K) * ((k : K) + 3)) ^ t by simpa [mul_comm] using heq)
  omega
theorem cycle_coefficients_zero {K : Type*} [Field K] [CharZero K]
    (k t : ℕ) (hk : 0 < k) (ht : 0 < t) (c₀ c₁ c₂ : K)
    (h₀₁ : c₀ * ((k : K) + 2) ^ t = c₁ * 2 ^ t)
    (h₁₂ : c₁ = c₂)
    (h₂₀ : c₂ * 3 ^ t = c₀ * ((k : K) + 3) ^ t) :
    c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 := by
  have hcycle : c₀ * (((k : K) + 2) * 3) ^ t =
      c₀ * (((k : K) + 3) * 2) ^ t := by
    calc
      _ = (c₀ * ((k : K) + 2) ^ t) * 3 ^ t := by rw [mul_pow]; ring
      _ = (c₁ * 2 ^ t) * 3 ^ t := by rw [h₀₁]
      _ = (c₂ * 3 ^ t) * 2 ^ t := by rw [h₁₂]; ring
      _ = (c₀ * ((k : K) + 3) ^ t) * 2 ^ t := by rw [h₂₀]
      _ = _ := by rw [mul_pow]; ring
  have hc₀ : c₀ = 0 := by
    by_contra hn
    exact cycle_products_ne k t hk ht (mul_left_cancel₀ hn hcycle)
  have hc₁ : c₁ = 0 := by
    have hn : (2 : K) ^ t ≠ 0 := pow_ne_zero _ (by norm_num)
    rw [hc₀, zero_mul] at h₀₁
    exact (mul_eq_zero.mp h₀₁.symm).resolve_right hn
  exact ⟨hc₀, hc₁, h₁₂ ▸ hc₁⟩
theorem polynomial_triangle_zero {K : Type*} [Field K] [CharZero K]
    (k t : ℕ) (hk : 0 < k) (ht : 0 < t) (T : K[X])
    (hT₁ : T.eval 1 ≠ 0) (hT₂ : T.eval 2 ≠ 0) (hT₃ : T.eval 3 ≠ 0)
    (c₀ c₁ c₂ : K)
    (h₀₁ : (C c₀ * ((X + C ((k : K) + 1)) * T) ^ t).eval 1 =
      (C c₁ * ((X + C 1) * T) ^ t).eval 1)
    (h₁₂ : (C c₁ * ((X + C 1) * T) ^ t).eval 3 =
      (C c₂ * ((X + C 1) * T) ^ t).eval 3)
    (h₂₀ : (C c₂ * ((X + C 1) * T) ^ t).eval 2 =
      (C c₀ * ((X + C ((k : K) + 1)) * T) ^ t).eval 2) :
    c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 := by
  simp only [eval_mul, eval_C, eval_pow, eval_add, eval_X] at h₀₁ h₁₂ h₂₀
  have h₀₁' : c₀ * ((k : K) + 2) ^ t = c₁ * 2 ^ t := by
    apply mul_right_cancel₀ (pow_ne_zero t hT₁)
    simpa only [show (1 : K) + ((k : K) + 1) = (k : K) + 2 by ring,
      show (1 : K) + 1 = 2 by norm_num, mul_pow, mul_assoc] using h₀₁
  have h₁₂' : c₁ = c₂ := by
    apply mul_right_cancel₀ (pow_ne_zero t (mul_ne_zero (by norm_num : (3 : K) + 1 ≠ 0) hT₃))
    exact h₁₂
  have h₂₀' : c₂ * 3 ^ t = c₀ * ((k : K) + 3) ^ t := by
    apply mul_right_cancel₀ (pow_ne_zero t hT₂)
    simpa only [show (2 : K) + ((k : K) + 1) = (k : K) + 3 by ring,
      show (2 : K) + 1 = 3 by norm_num, mul_pow, mul_assoc] using h₂₀
  exact cycle_coefficients_zero k t hk ht c₀ c₁ c₂ h₀₁' h₁₂' h₂₀'
theorem polynomial_shape_of_mark_divisibility {K : Type*} [Field K]
    (f P : K[X]) (k t : ℕ) (hP : P.Monic) (hdegree : P.natDegree = k)
    (hfdegree : f.natDegree ≤ k * t) (hdiv : P ^ t ∣ f) :
    f = C f.leadingCoeff * P ^ t := by
  apply eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (hP.pow t) hdiv
  simpa [hP.natDegree_pow, hdegree, mul_comm] using hfdegree
end Nagata.W04.ReducibleSquare
end
section
noncomputable section
namespace Nagata.W04.Dimension
open Polynomial
open scoped nonZeroDivisors
variable {R : Type*} [CommRing R] [IsDomain R]
end Nagata.W04.Dimension
end
end
section
noncomputable section
namespace Nagata.W04.Dimension
open MvPolynomial
variable (K : Type*) [Field K] (n : ℕ)
variable {K n}
end Nagata.W04.Dimension
end
end
section
noncomputable section
namespace Nagata.W04.ReducibleSquare
variable {K : Type*} [Field K]
def lineSubstitution (i : K) : Fin 3 → Polynomial K :=
  ![Polynomial.X, Polynomial.C (i ^ 2) - Polynomial.C i * Polynomial.X, 1]
def lineRestriction (i : K) : MvPolynomial (Fin 3) K →+* Polynomial K :=
  MvPolynomial.eval₂Hom Polynomial.C (lineSubstitution i)
theorem lineRestriction_node_gluing (F : MvPolynomial (Fin 3) K) (i j : K) :
    (lineRestriction i F).eval (i + j) = (lineRestriction j F).eval (i + j) := by
  change Polynomial.evalRingHom (i + j) (MvPolynomial.eval₂Hom _ _ F) =
    Polynomial.evalRingHom (i + j) (MvPolynomial.eval₂Hom _ _ F)
  rw [MvPolynomial.map_eval₂Hom, MvPolynomial.map_eval₂Hom]
  have hcoords : (fun v => Polynomial.evalRingHom (i + j) (lineSubstitution i v)) =
      (fun v => Polynomial.evalRingHom (i + j) (lineSubstitution j v)) := by
    funext v
    fin_cases v <;> simp [lineSubstitution]
    ring
  rw [hcoords]
end Nagata.W04.ReducibleSquare
end
end
section
noncomputable section
namespace Nagata.W04.ReducibleSquare
open Polynomial
def markTail {K : Type*} [CommSemiring K] (k : ℕ) : K[X] :=
  ∏ j ∈ Finset.range (k - 1), (X + C ((j + 2 : ℕ) : K))
def firstMark (k i : ℕ) : ℕ := if i = 0 then k + 1 else 1
def markPolynomial {K : Type*} [CommSemiring K] (k i : ℕ) : K[X] :=
  (X + C ((firstMark k i : ℕ) : K)) * markTail k
variable {K : Type*} [Field K]
theorem markTail_monic (k : ℕ) : (markTail k : K[X]).Monic := by
  exact monic_prod_of_monic _ _ (fun j _ => monic_X_add_C _)
theorem markTail_natDegree (k : ℕ) : (markTail k : K[X]).natDegree = k - 1 := by
  unfold markTail
  rw [natDegree_prod_of_monic _ _ (fun j _ => monic_X_add_C _)]
  simp_rw [natDegree_X_add_C]
  simp
theorem markPolynomial_monic (k i : ℕ) : (markPolynomial k i : K[X]).Monic :=
  (monic_X_add_C _).mul (markTail_monic k)
theorem markPolynomial_natDegree (k i : ℕ) (hk : 0 < k) :
    (markPolynomial k i : K[X]).natDegree = k := by
  unfold markPolynomial
  rw [(monic_X_add_C _).natDegree_mul (markTail_monic k), natDegree_X_add_C,
    markTail_natDegree]
  omega
variable [CharZero K]
theorem markTail_eval_nat_ne_zero (k n : ℕ) : (markTail k : K[X]).eval (n : K) ≠ 0 := by
  unfold markTail
  rw [eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  simp only [eval_add, eval_X, eval_C]
  exact_mod_cast (show n + (j + 2) ≠ 0 by omega)
theorem firstMark_pos (k i : ℕ) : 0 < firstMark k i := by
  unfold firstMark
  split <;> omega
theorem markPolynomial_eval_nat_ne_zero (k i n : ℕ) :
    (markPolynomial k i : K[X]).eval (n : K) ≠ 0 := by
  unfold markPolynomial
  rw [eval_mul, eval_add, eval_X, eval_C]
  apply mul_ne_zero _ (markTail_eval_nat_ne_zero k n)
  exact_mod_cast (show n + firstMark k i ≠ 0 by have := firstMark_pos k i; omega)
theorem marked_linear_factors_coprime (u v : ℕ) (huv : u ≠ v) :
    IsCoprime (X + C (u : K)) (X + C (v : K)) := by
  have huv' : -(u : K) ≠ -(v : K) := by
    intro h
    have h' : (u : K) = (v : K) := neg_injective h
    exact huv (Nat.cast_injective h')
  simpa only [C_neg, sub_neg_eq_add] using
    (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr huv').isUnit)
theorem firstMark_ne_tail (k i j : ℕ) (hj : j < k - 1) : firstMark k i ≠ j + 2 := by
  unfold firstMark
  split <;> omega
theorem markPolynomial_pow_dvd (k i t : ℕ) (f : K[X])
    (hfirst : (X + C ((firstMark k i : ℕ) : K)) ^ t ∣ f)
    (htail : ∀ j < k - 1, (X + C ((j + 2 : ℕ) : K)) ^ t ∣ f) :
    (markPolynomial k i : K[X]) ^ t ∣ f := by
  have htaildiv : (markTail k : K[X]) ^ t ∣ f := by
    unfold markTail
    rw [← Finset.prod_pow]
    apply Finset.prod_dvd_of_coprime
    · intro u hu v hv huv
      exact (marked_linear_factors_coprime (u + 2) (v + 2) (by omega)).pow
    · intro j hj
      exact htail j (Finset.mem_range.mp hj)
  have hcop : IsCoprime (X + C ((firstMark k i : ℕ) : K)) (markTail k : K[X]) := by
    apply IsCoprime.prod_right
    intro j hj
    exact marked_linear_factors_coprime _ _ (firstMark_ne_tail k i j (Finset.mem_range.mp hj))
  unfold markPolynomial
  rw [mul_pow]
  exact hcop.pow.mul_dvd hfirst htaildiv
end Nagata.W04.ReducibleSquare
end
end
section
namespace Nagata.W04.ReducibleSquare
open Polynomial
theorem line_family_zero {K : Type*} [Field K] [CharZero K]
    (k t : ℕ) (hk : 3 ≤ k) (ht : 0 < t) (f : ℕ → K[X])
    (hdeg : ∀ i < k, (f i).natDegree ≤ k * t)
    (hdiv : ∀ i < k, (markPolynomial k i : K[X]) ^ t ∣ f i)
    (hglue : ∀ i < k, ∀ j < k, (f i).eval ((i + j : ℕ) : K) =
      (f j).eval ((i + j : ℕ) : K)) :
    ∀ i < k, f i = 0 := by
  have hk₀ : 0 < k := by omega
  have hk₁ : 1 < k := by omega
  have hk₂ : 2 < k := by omega
  have hshape (i : ℕ) (hi : i < k) :
      f i = C (f i).leadingCoeff * (markPolynomial k i : K[X]) ^ t :=
    polynomial_shape_of_mark_divisibility (f i) (markPolynomial k i) k t
      (markPolynomial_monic k i) (markPolynomial_natDegree k i hk₀) (hdeg i hi) (hdiv i hi)
  have h₀₁ := hglue 0 hk₀ 1 hk₁
  have h₁₂ := hglue 1 hk₁ 2 hk₂
  have h₂₀ := hglue 2 hk₂ 0 hk₀
  rw [hshape 0 hk₀, hshape 1 hk₁] at h₀₁
  rw [hshape 1 hk₁, hshape 2 hk₂] at h₁₂
  rw [hshape 2 hk₂, hshape 0 hk₀] at h₂₀
  have hz := polynomial_triangle_zero k t hk₀ ht (markTail k : K[X])
    (by simpa using markTail_eval_nat_ne_zero (K := K) k 1)
    (by simpa using markTail_eval_nat_ne_zero (K := K) k 2)
    (by simpa using markTail_eval_nat_ne_zero (K := K) k 3)
    (f 0).leadingCoeff (f 1).leadingCoeff (f 2).leadingCoeff
    (by simpa [markPolynomial, firstMark] using h₀₁)
    (by simpa [markPolynomial, firstMark] using h₁₂)
    (by simpa [markPolynomial, firstMark] using h₂₀)
  have hf₀ : f 0 = 0 := by rw [hshape 0 hk₀, hz.1]; simp
  intro i hi
  have hnode := hglue i hi 0 hk₀
  rw [hf₀, eval_zero, hshape i hi, eval_mul, eval_C, eval_pow] at hnode
  have hc : (f i).leadingCoeff = 0 :=
    (mul_eq_zero.mp hnode).resolve_right
      (pow_ne_zero t (markPolynomial_eval_nat_ne_zero k i (i + 0)))
  rw [hshape i hi, hc]
  simp
theorem line_family_zero_of_marked_factors {K : Type*} [Field K] [CharZero K]
    (k t : ℕ) (hk : 3 ≤ k) (ht : 0 < t) (f : ℕ → K[X])
    (hdeg : ∀ i < k, (f i).natDegree ≤ k * t)
    (hfirst : ∀ i < k, (X + C ((firstMark k i : ℕ) : K)) ^ t ∣ f i)
    (htail : ∀ i < k, ∀ j < k - 1, (X + C ((j + 2 : ℕ) : K)) ^ t ∣ f i)
    (hglue : ∀ i < k, ∀ j < k, (f i).eval ((i + j : ℕ) : K) =
      (f j).eval ((i + j : ℕ) : K)) :
    ∀ i < k, f i = 0 := by
  apply line_family_zero k t hk ht f hdeg
  · intro i hi
    exact markPolynomial_pow_dvd k i t (f i) (hfirst i hi) (htail i hi)
  · exact hglue
end Nagata.W04.ReducibleSquare
end
section
namespace Nagata.W04.ReducibleSquare
open Polynomial
end Nagata.W04.ReducibleSquare
end
end OAI
-- BinaryForms
namespace OAI
section
noncomputable section
namespace Nagata.W02
theorem natDegree_eval₂_le_totalDegree {σ K : Type*} [CommSemiring K]
    (P : MvPolynomial σ K) (f : σ → Polynomial K)
    (hf : ∀ i, (f i).natDegree ≤ 1) :
    (P.eval₂ Polynomial.C f).natDegree ≤ P.totalDegree := by
  classical
  rw [MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  calc
    (Polynomial.C (P.coeff d) * ∏ i ∈ d.support, f i ^ d i).natDegree ≤
        (Polynomial.C (P.coeff d)).natDegree +
          (∏ i ∈ d.support, f i ^ d i).natDegree := Polynomial.natDegree_mul_le
    _ = (∏ i ∈ d.support, f i ^ d i).natDegree := by simp
    _ ≤ ∑ i ∈ d.support, (f i ^ d i).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i hi
      simpa using Polynomial.natDegree_pow_le_of_le (d i) (hf i)
    _ ≤ P.totalDegree := MvPolynomial.le_totalDegree hd
end Nagata.W02
end
end
section
noncomputable section
namespace Nagata.W02
def DegreeExponent (k : ℕ) := {d : Fin 3 →₀ ℕ // d.degree = k}
instance degreeExponentFintype (k : ℕ) : Fintype (DegreeExponent k) :=
  ((Finsupp.finite_of_degree_le (σ := Fin 3) k).subset
    (fun _ h => le_of_eq h)).fintype
def homogeneousCoefficientEquiv (R : Type*) [CommRing R] (k : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin 3) R k ≃ₗ[R] (DegreeExponent k →₀ R) :=
  (LinearEquiv.ofEq _ _
    (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported (Fin 3) R k)).trans
      (AddMonoidAlgebra.supportedEquivFinsupp {d : Fin 3 →₀ ℕ | d.degree = k})
end Nagata.W02
end
end
section
noncomputable section
namespace Nagata.W02
def degreeExponentEquiv (k : ℕ) :
    DegreeExponent k ≃ ↥(Finset.finsuppAntidiag (Finset.univ : Finset (Fin 3)) k) where
  toFun d := ⟨d.val, by
    rw [Finset.mem_finsuppAntidiag]
    exact ⟨by simpa only [← Finsupp.degree_eq_sum] using d.property,
      Finset.subset_univ _⟩⟩
  invFun d := ⟨d.val, by
    have hd := (Finset.mem_finsuppAntidiag.mp d.property).1
    simpa only [← Finsupp.degree_eq_sum] using hd⟩
  left_inv _ := rfl
  right_inv _ := rfl
theorem card_degreeExponent (k : ℕ) :
    Fintype.card (DegreeExponent k) = (k + 2).choose 2 := by
  rw [Fintype.card_congr (degreeExponentEquiv k), Fintype.card_coe,
    Finset.card_finsuppAntidiag_nat_eq_choose]
  simp only [Finset.card_univ, Fintype.card_fin]
  have he : 3 + k - 1 = k + 2 := by omega
  rw [he]
  exact Nat.choose_symm_add
instance homogeneousFiniteDimensional (K : Type*) [Field K] (k : ℕ) :
    FiniteDimensional K (MvPolynomial.homogeneousSubmodule (Fin 3) K k) :=
  (homogeneousCoefficientEquiv K k).symm.finiteDimensional
theorem finrank_homogeneousSubmodule (K : Type*) [Field K] (k : ℕ) :
    Module.finrank K (MvPolynomial.homogeneousSubmodule (Fin 3) K k) =
      (k + 2).choose 2 := by
  rw [(homogeneousCoefficientEquiv K k).finrank_eq,
    Module.finrank_finsupp_self, card_degreeExponent]
end Nagata.W02
end
end
section
noncomputable section
namespace Nagata.W02
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]
end Nagata.W02
end
end
section
noncomputable section
namespace Nagata.W02
open MvPolynomial
end Nagata.W02
end
end
section
noncomputable section
namespace Nagata.W02
open Nagata.W04.ReducibleSquare
theorem lineSubstitution_natDegree_le {K : Type*} [Field K] (i : K) (j : Fin 3) :
    (lineSubstitution i j).natDegree ≤ 1 := by
  fin_cases j
  · simp [lineSubstitution]
  · change (Polynomial.C (i ^ 2) - Polynomial.C i * Polynomial.X).natDegree ≤ 1
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · simp
    · exact (Polynomial.natDegree_mul_le).trans (by simp)
  · simp [lineSubstitution]
theorem lineRestriction_natDegree_le_totalDegree {K : Type*} [Field K]
    (i : K) (P : MvPolynomial (Fin 3) K) :
    (lineRestriction i P).natDegree ≤ P.totalDegree :=
  natDegree_eval₂_le_totalDegree P (lineSubstitution i) (lineSubstitution_natDegree_le i)
end Nagata.W02
end
end
section
noncomputable section
namespace Nagata.W02
open MvPolynomial
end Nagata.W02
end
end
section
namespace Nagata.W02
open Nagata.W04.ReducibleSquare
theorem lineRestriction_natDegree_le {K : Type*} [Field K]
    (i : K) (P : MvPolynomial (Fin 3) K) (d : ℕ) (hP : P.IsHomogeneous d) :
    (lineRestriction i P).natDegree ≤ d :=
  (lineRestriction_natDegree_le_totalDegree i P).trans hP.totalDegree_le
end Nagata.W02
end
end OAI
-- PolynomialJets
namespace OAI
section
namespace Nagata.Workers.W30
open scoped BigOperators
abbrev JetIndex (q m : ℕ) := Σ b : Fin m, Fin (q * (m - b.val))
def jetIndexPair {q m : ℕ} (x : JetIndex q m) : ℕ × ℕ :=
  (x.2.val, x.1.val)
@[simp] theorem jetIndexPair_bounds {q m : ℕ} (x : JetIndex q m) :
    (jetIndexPair x).2 < m ∧ (jetIndexPair x).1 < q * (m - (jetIndexPair x).2) :=
  ⟨x.1.isLt, x.2.isLt⟩
def jetIndexEquivPairs (q m : ℕ) :
    JetIndex q m ≃ {p : ℕ × ℕ // p.2 < m ∧ p.1 < q * (m - p.2)} where
  toFun x := ⟨jetIndexPair x, jetIndexPair_bounds x⟩
  invFun x := ⟨⟨x.1.2, x.2.1⟩, ⟨x.1.1, x.2.2⟩⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
open MvPolynomial
open scoped Pointwise
variable {σ R : Type*} [CommRing R]
theorem mem_monomial_span_iff {p : MvPolynomial σ R} {s : Set (σ →₀ ℕ)} :
    p ∈ Ideal.span ((fun a => monomial a (1 : R)) '' s) ↔
      ∀ a ∈ p.support, ∃ g ∈ s, g ≤ a := by
  classical
  let J : Ideal (MvPolynomial σ R) :=
    { carrier := {f | ∀ a ∈ f.support, ∃ g ∈ s, g ≤ a}
      add_mem' {x y} hx hy a ha :=
        (Finset.mem_union.mp (Finsupp.support_add ha)).elim (hx a) (hy a)
      zero_mem' := by simp
      smul_mem' x y hy a ha := by
        change a ∈ (x*y).support at ha
        obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp (support_mul x y ha)
        obtain ⟨g,hg,hgv⟩ := hy v hv
        exact ⟨g,hg,hgv.trans (le_add_of_nonneg_left zero_le)⟩ }
  change _ ↔ p ∈ J
  constructor
  · suffices Ideal.span ((fun a => monomial a (1 : R)) '' s) ≤ J from @this p
    rw [Ideal.span_le]
    rintro _ ⟨g,hg,rfl⟩ a ha
    have heq : a = g := Finset.mem_singleton.mp (support_monomial_subset ha)
    exact ⟨g,hg,heq ▸ le_rfl⟩
  · intro hp
    rw [p.as_sum]
    apply Submodule.sum_mem _
    intro a ha
    obtain ⟨g,hg,hga⟩ := hp a ha
    obtain ⟨c,hc⟩ := le_iff_exists_add.mp hga
    have hgen : monomial g (1:R) ∈ Ideal.span ((fun a => monomial a (1:R)) '' s) :=
      Ideal.subset_span ⟨g,hg,rfl⟩
    have hprod := Ideal.mul_mem_left _ (monomial c (p.coeff a)) hgen
    simpa [MvPolynomial.monomial_mul, hc, add_comm] using hprod
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
def GeneratorDivides (q m ell b : Nat) : Prop :=
  ∃ k : Nat, k ≤ m ∧ q * (m - k) ≤ ell ∧ k ≤ b
theorem generatorDivides_iff {q m ell b : Nat} :
    GeneratorDivides q m ell b ↔ m ≤ b ∨ q * (m - b) ≤ ell := by
  constructor
  · rintro ⟨k, hkm, hell, hkb⟩
    right
    have hsub : m - b ≤ m - k := by omega
    exact Nat.le_trans (Nat.mul_le_mul_left q hsub) hell
  · rintro (hmb | hell)
    · exact ⟨m, Nat.le_refl m, by simp, hmb⟩
    · by_cases hbm : b ≤ m
      · exact ⟨b, hbm, hell, Nat.le_refl b⟩
      · exact ⟨m, Nat.le_refl m, by simp, by omega⟩
theorem not_generatorDivides_iff {q m ell b : Nat} :
    ¬ GeneratorDivides q m ell b ↔ b < m ∧ ell < q * (m - b) := by
  rw [generatorDivides_iff]
  omega
theorem GeneratorDivides.add {q m ell b c d : Nat}
    (h : GeneratorDivides q m ell b) : GeneratorDivides q m (ell + c) (b + d) := by
  rcases h with ⟨k, hkm, hell, hkb⟩
  exact ⟨k, hkm, by omega, by omega⟩
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
open scoped Pointwise
variable {A : Type*} [CommRing A]
theorem pair_set_pow (x y : A) (m : ℕ) :
    ({x,y} : Set A) ^ m = {z | ∃ k ≤ m, z = x ^ (m - k) * y ^ k} := by
  induction m with
  | zero =>
    ext z
    simp
  | succ m ih =>
    rw [pow_succ, ih]
    ext z
    simp only [Set.mem_mul, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨a, ⟨k, hk, rfl⟩, c, hc, rfl⟩
      rcases hc with rfl | rfl
      · refine ⟨k, by omega, ?_⟩
        have hsub : m + 1 - k = (m - k) + 1 := by omega
        rw [hsub, pow_succ]
        ac_rfl
      · refine ⟨k + 1, by omega, ?_⟩
        rw [Nat.add_sub_add_right, pow_succ]
        ac_rfl
    · rintro ⟨k, hk, rfl⟩
      cases k with
      | zero =>
        refine ⟨x ^ m * y ^ 0, ⟨0, Nat.zero_le m, by simp⟩, x, Or.inl rfl, ?_⟩
        simp [pow_succ]
      | succ k =>
        refine ⟨x ^ (m - k) * y ^ k, ⟨k, by omega, rfl⟩, y, Or.inr rfl, ?_⟩
        rw [Nat.add_sub_add_right, pow_succ]
        ac_rfl
theorem pair_ideal_pow (x y : A) (m : ℕ) :
    (Ideal.span {x,y}) ^ m =
      Ideal.span {z | ∃ k ≤ m, z = x ^ (m - k) * y ^ k} := by
  rw [Ideal.span, Submodule.span_pow, pair_set_pow]
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
noncomputable def exponentPair (ell b : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 ell + Finsupp.single 1 b
@[simp] theorem exponentPair_zero (ell b : ℕ) : exponentPair ell b 0 = ell := by
  simp [exponentPair]
@[simp] theorem exponentPair_one (ell b : ℕ) : exponentPair ell b 1 = b := by
  simp [exponentPair]
lemma exponentPair_eta (a : Fin 2 →₀ ℕ) : exponentPair (a 0) (a 1) = a := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simp
lemma exponentPair_le_iff {ell b : ℕ} {a : Fin 2 →₀ ℕ} :
    exponentPair ell b ≤ a ↔ ell ≤ a 0 ∧ b ≤ a 1 := by
  constructor
  · intro h
    exact ⟨by simpa using h 0, by simpa using h 1⟩
  · rintro ⟨h0,h1⟩ i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using h0
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simpa using h1
lemma exponentPair_injective : Function.Injective (fun p : ℕ × ℕ => exponentPair p.1 p.2) := by
  intro p t h
  apply Prod.ext
  · simpa using congrArg (fun a : Fin 2 →₀ ℕ => a 0) h
  · simpa using congrArg (fun a : Fin 2 →₀ ℕ => a 1) h
noncomputable def jetExponent {q m : ℕ} (i : JetIndex q m) : Fin 2 →₀ ℕ :=
  exponentPair i.2.val i.1.val
theorem jetIndexPair_injective {q m : ℕ} :
    Function.Injective (@jetIndexPair q m) := by
  intro i j h
  apply (jetIndexEquivPairs q m).injective
  exact Subtype.ext h
theorem jetExponent_injective {q m : ℕ} :
    Function.Injective (@jetExponent q m) := by
  intro i j h
  apply jetIndexPair_injective
  exact exponentPair_injective h
@[simp] theorem jetExponent_inj {q m : ℕ} (i j : JetIndex q m) :
    jetExponent i = jetExponent j ↔ i = j :=
  jetExponent_injective.eq_iff
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
open MvPolynomial
open scoped BigOperators
variable (R : Type*) [CommRing R] (q m : ℕ)
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
open MvPolynomial
variable {R : Type*} [CommRing R]
abbrev Bivariate (R : Type*) [CommRing R] := MvPolynomial (Fin 2) R
noncomputable def collisionIdeal (R : Type*) [CommRing R] (q m : ℕ) : Ideal (Bivariate R) :=
  (Ideal.span {X (0 : Fin 2) ^ q, X (1 : Fin 2)}) ^ m
lemma monomial_exponentPair (ell b : ℕ) :
    (monomial (exponentPair ell b) 1 : Bivariate R) = X 0 ^ ell * X 1 ^ b := by
  rw [exponentPair, monomial_add_single, ← X_pow_eq_monomial]
def collisionGenerators (q m : ℕ) : Set (Fin 2 →₀ ℕ) :=
  {a | ∃ k ≤ m, a = exponentPair (q * (m - k)) k}
theorem collisionIdeal_eq_monomial_span (q m : ℕ) :
    collisionIdeal R q m =
      Ideal.span ((fun a => monomial a (1 : R)) '' collisionGenerators q m) := by
  rw [collisionIdeal, pair_ideal_pow]
  congr 1
  ext p
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨exponentPair (q * (m-k)) k, ⟨k,hk,rfl⟩, ?_⟩
    simp only [monomial_exponentPair, pow_mul]
  · rintro ⟨a, ⟨k,hk,rfl⟩, rfl⟩
    exact ⟨k,hk, by simp only [monomial_exponentPair, pow_mul]⟩
lemma exists_collisionGenerator_le_iff (q m : ℕ) (a : Fin 2 →₀ ℕ) :
    (∃ g ∈ collisionGenerators q m, g ≤ a) ↔ GeneratorDivides q m (a 0) (a 1) := by
  constructor
  · rintro ⟨g, ⟨k,hk,rfl⟩, hle⟩
    exact ⟨k,hk,(exponentPair_le_iff.mp hle).1,(exponentPair_le_iff.mp hle).2⟩
  · rintro ⟨k,hk,h0,h1⟩
    exact ⟨exponentPair (q*(m-k)) k, ⟨k,hk,rfl⟩, exponentPair_le_iff.mpr ⟨h0,h1⟩⟩
theorem mem_collisionIdeal_iff_support (q m : ℕ) (p : Bivariate R) :
    p ∈ collisionIdeal R q m ↔
      ∀ a ∈ p.support, GeneratorDivides q m (a 0) (a 1) := by
  rw [collisionIdeal_eq_monomial_span, mem_monomial_span_iff]
  simp only [exists_collisionGenerator_le_iff]
theorem mem_collisionIdeal_iff_coefficients (q m : ℕ) (p : Bivariate R) :
    p ∈ collisionIdeal R q m ↔
      ∀ b < m, ∀ ell < q * (m-b), p.coeff (exponentPair ell b) = 0 := by
  rw [mem_collisionIdeal_iff_support]
  constructor
  · intro h b hb ell hell
    by_contra hne
    have hm := h (exponentPair ell b) (mem_support_iff.mpr hne)
    exact (not_generatorDivides_iff.mpr ⟨hb,hell⟩) (by simpa using hm)
  · intro h a ha
    by_contra hn
    obtain ⟨hb,hell⟩ := not_generatorDivides_iff.mp hn
    have heq := h (a 1) hb (a 0) hell
    rw [exponentPair_eta] at heq
    exact (mem_support_iff.mp ha) heq
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
open MvPolynomial
variable {R : Type*} [CommRing R]
lemma range_X_fin_two :
    Set.range (X : Fin 2 → Bivariate R) = {X 0, X 1} := by
  ext p
  constructor
  · rintro ⟨i,rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Or.inl rfl
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
theorem mem_originIdeal_pow_iff (m : ℕ) (p : Bivariate R) :
    p ∈ (Ideal.span (Set.range (X : Fin 2 → Bivariate R))) ^ m ↔
      ∀ ell b : ℕ, ell + b < m → p.coeff (exponentPair ell b) = 0 := by
  have hbase := mem_collisionIdeal_iff_coefficients (R := R) 1 m p
  simp only [collisionIdeal, pow_one, Nat.one_mul, range_X_fin_two] at hbase ⊢
  rw [hbase]
  constructor
  · intro h ell b hlt
    exact h b (by omega) ell (by omega)
  · intro h b hb ell hell
    exact h ell b (by omega)
end Nagata.Workers.W30
end
end OAI
-- TaylorMultiplicity
namespace OAI
section
namespace Nagata.AffineMultiplicity
variable {R : Type*} [CommRing R]
end Nagata.AffineMultiplicity
end
section
namespace Nagata.AffineMultiplicity
variable {σ R : Type*} [CommRing R]
noncomputable def translateHom (p : σ → R) : MvPolynomial σ R →+* MvPolynomial σ R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i => MvPolynomial.X i + MvPolynomial.C (p i))
@[simp] theorem translateHom_C (p : σ → R) (a : R) :
    translateHom p (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [translateHom]
@[simp] theorem translateHom_X (p : σ → R) (i : σ) :
    translateHom p (MvPolynomial.X i) = MvPolynomial.X i + MvPolynomial.C (p i) := by
  simp [translateHom]
theorem translateHom_neg_comp (p : σ → R) :
    (translateHom (-p)).comp (translateHom p) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro a; simp
  · intro i; simp [add_assoc]
theorem translateHom_comp_neg (p : σ → R) :
    (translateHom p).comp (translateHom (-p)) = RingHom.id _ := by
  simpa only [neg_neg] using translateHom_neg_comp (-p)
noncomputable def translateEquiv (p : σ → R) : MvPolynomial σ R ≃+* MvPolynomial σ R :=
  { translateHom p with
    invFun := translateHom (-p)
    left_inv := fun f => RingHom.congr_fun (translateHom_neg_comp p) f
    right_inv := fun f => RingHom.congr_fun (translateHom_comp_neg p) f }
theorem eval_zero_translate (p : σ → R) (f : MvPolynomial σ R) :
    MvPolynomial.eval (0 : σ → R) (translateHom p f) = MvPolynomial.eval p f := by
  have h : (MvPolynomial.eval (0 : σ → R)).comp (translateHom p) =
      MvPolynomial.eval p := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp
    · intro i; simp
  exact RingHom.congr_fun h f
end Nagata.AffineMultiplicity
end
section
namespace Nagata.AffineMultiplicity
variable {σ R : Type*} [CommRing R]
theorem eval_translate (p x : σ → R) (f : MvPolynomial σ R) :
    MvPolynomial.eval x (translateHom p f) = MvPolynomial.eval (x + p) f := by
  have h : (MvPolynomial.eval x).comp (translateHom p) =
      MvPolynomial.eval (x + p) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp
    · intro i; simp
  exact RingHom.congr_fun h f
end Nagata.AffineMultiplicity
end
section
namespace Nagata.AffineMultiplicity
variable {σ R : Type*} [CommRing R]
end Nagata.AffineMultiplicity
end
section
namespace Nagata.AffineMultiplicity
variable {σ R : Type*} [CommRing R]
section Field
variable {F : Type*} [Field F]
end Field
end Nagata.AffineMultiplicity
end
section
namespace Nagata.AffineMultiplicity
variable {R : Type*} [CommRing R]
theorem pointIdeal_finTwo_zero :
    pointIdeal (0 : Fin 2 → R) =
      Ideal.span (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) R)) := by
  ext f
  rw [pointIdeal_mem_iff, MvPolynomial.eval_zero]
  change f.coeff 0 = 0 ↔ _
  have h := Nagata.Workers.W30.mem_originIdeal_pow_iff 1 f
  simp only [pow_one] at h
  rw [h]
  constructor
  · intro hf ell b hlt
    have he : ell = 0 := by omega
    have hb : b = 0 := by omega
    subst ell
    subst b
    simpa [Nagata.Workers.W30.exponentPair] using hf
  · intro hf
    simpa [Nagata.Workers.W30.exponentPair] using hf 0 0 (by decide)
theorem orderAtLeast_finTwo_iff_taylor_coeff
    (p : Fin 2 → R) (m : ℕ) (f : MvPolynomial (Fin 2) R) :
    orderAtLeast p m f ↔ ∀ ell b : ℕ, ell + b < m →
      (translateHom p f).coeff (Nagata.Workers.W30.exponentPair ell b) = 0 := by
  have h := orderAtLeast_equiv_iff p (0 : Fin 2 → R) (translateEquiv p)
    (fun g => eval_zero_translate p g) m f
  rw [← h]
  unfold orderAtLeast
  rw [pointIdeal_finTwo_zero]
  exact Nagata.Workers.W30.mem_originIdeal_pow_iff m (translateHom p f)
end Nagata.AffineMultiplicity
end
end OAI
-- ChartJets
namespace OAI
section
namespace Nagata.W27
noncomputable section
open MvPolynomial
abbrev PlaneJet (r : ℕ) (m : Fin r → ℕ) :=
  (i : Fin r) × {ab : Fin (m i) × Fin (m i) // ab.1.val + ab.2.val < m i}
section Entries
variable {R : Type*} [CommRing R]
variable {ι : Type*}
end Entries
end
end Nagata.W27
end
section
noncomputable section
namespace Nagata.W27
open scoped BigOperators
open MvPolynomial
section MatrixEntries
variable {R : Type*} [CommRing R]
end MatrixEntries
section LinearEquations
variable {R : Type*} [CommRing R]
variable {σ κ ρ : Type*} [Fintype κ]
def coefficientEquation (A : Matrix ρ κ (MvPolynomial σ R))
    (p : σ → R) (c : κ → R) (row : ρ) : R :=
  ∑ col, eval p (A row col) * c col
theorem coefficientEquation_add (A : Matrix ρ κ (MvPolynomial σ R))
    (p : σ → R) (c c' : κ → R) (row : ρ) :
    coefficientEquation A p (c + c') row =
      coefficientEquation A p c row + coefficientEquation A p c' row := by
  simp [coefficientEquation, mul_add, Finset.sum_add_distrib]
theorem coefficientEquation_smul (A : Matrix ρ κ (MvPolynomial σ R))
    (p : σ → R) (a : R) (c : κ → R) (row : ρ) :
    coefficientEquation A p (a • c) row = a * coefficientEquation A p c row := by
  simp only [coefficientEquation, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro col _
  exact mul_left_comm _ _ _
def coefficientLinearMap (A : Matrix ρ κ (MvPolynomial σ R)) (p : σ → R) :
    (κ → R) →ₗ[R] (ρ → R) where
  toFun c row := coefficientEquation A p c row
  map_add' c c' := funext (coefficientEquation_add A p c c')
  map_smul' a c := funext (coefficientEquation_smul A p a c)
end LinearEquations
end Nagata.W27
end
end
section
noncomputable section
namespace Nagata.W27
open MvPolynomial
open Classical
abbrev HomogeneousMonomial (d : ℕ) := Nagata.W02.DegreeExponent d
variable {R : Type*} [CommRing R]
def homogeneousCoordinates (d : ℕ) :
    homogeneousSubmodule (Fin 3) R d ≃ₗ[R] (HomogeneousMonomial d → R) :=
  (Nagata.W02.homogeneousCoefficientEquiv R d).trans
    (Finsupp.linearEquivFunOnFinite R R (HomogeneousMonomial d))
theorem homogeneousCoordinates_ne_zero_iff (d : ℕ)
    (F : homogeneousSubmodule (Fin 3) R d) :
    homogeneousCoordinates d F ≠ 0 ↔ F.val ≠ 0 := by
  constructor
  · intro h hz
    apply h
    have hF : F = 0 := Subtype.ext hz
    rw [hF, map_zero]
  · intro h hz
    apply h
    have hF : F = 0 := (homogeneousCoordinates d).injective
      (hz.trans (map_zero (homogeneousCoordinates d)).symm)
    exact congrArg Subtype.val hF
theorem homogeneousCoordinates_symm_ne_zero_iff (d : ℕ)
    (c : HomogeneousMonomial d → R) :
    ((homogeneousCoordinates d).symm c).val ≠ 0 ↔ c ≠ 0 := by
  rw [← homogeneousCoordinates_ne_zero_iff]
  rw [LinearEquiv.apply_symm_apply]
end Nagata.W27
end
end
section
noncomputable section
namespace Nagata.W27
open MvPolynomial
variable {ι R : Type*} [CommRing R]
def universalTranslate (i : ι) :
    MvPolynomial (Fin 2) R →+*
      MvPolynomial (Fin 2) (MvPolynomial (ι × Fin 2) R) :=
  eval₂Hom (C.comp C) (fun j => X j + C (X (i, j)))
def universalJetCoefficient (i : ι) (s : Fin 2 →₀ ℕ)
    (f : MvPolynomial (Fin 2) R) : MvPolynomial (ι × Fin 2) R :=
  (universalTranslate i f).coeff s
theorem map_universalTranslate (p : ι × Fin 2 → R) (i : ι)
    (f : MvPolynomial (Fin 2) R) :
    MvPolynomial.map (eval p) (universalTranslate i f) =
      eval₂Hom C (fun j => X j + C (p (i, j))) f := by
  have h : (MvPolynomial.map (eval p)).comp (universalTranslate i) =
      eval₂Hom C (fun j => X j + C (p (i, j))) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [universalTranslate]
    · intro j
      simp [universalTranslate]
  exact RingHom.congr_fun h f
theorem eval_universalJetCoefficient (p : ι × Fin 2 → R) (i : ι)
    (s : Fin 2 →₀ ℕ) (f : MvPolynomial (Fin 2) R) :
    eval p (universalJetCoefficient i s f) =
      (eval₂Hom C (fun j => X j + C (p (i, j))) f).coeff s := by
  rw [universalJetCoefficient, ← coeff_map, map_universalTranslate]
theorem universalJetCoefficient_add (i : ι) (s : Fin 2 →₀ ℕ)
    (f g : MvPolynomial (Fin 2) R) :
    universalJetCoefficient i s (f + g) =
      universalJetCoefficient i s f + universalJetCoefficient i s g := by
  simp [universalJetCoefficient]
theorem universalJetCoefficient_C_mul (i : ι) (s : Fin 2 →₀ ℕ)
    (a : R) (f : MvPolynomial (Fin 2) R) :
    universalJetCoefficient i s (C a * f) =
      C a * universalJetCoefficient i s f := by
  simp [universalJetCoefficient, universalTranslate, coeff_C_mul]
end Nagata.W27
end
end
section
namespace Nagata.W27
noncomputable section
open scoped BigOperators
open MvPolynomial
section Determinants
variable {R : Type*} [CommRing R]
variable {σ κ ρ : Type*} [Fintype κ] [DecidableEq κ]
end Determinants
end
end Nagata.W27
end
section
noncomputable section
namespace Nagata.W27
open MvPolynomial
end Nagata.W27
end
end
section
noncomputable section
namespace Nagata.W27
open scoped BigOperators
open MvPolynomial
variable {R σ : Type*} [CommRing R]
end Nagata.W27
end
end
section
noncomputable section
namespace Nagata.W27
open scoped BigOperators
open MvPolynomial
variable {R : Type*} [CommRing R]
def directChartHom (c : Fin 3) : MvPolynomial (Fin 3) R →+* MvPolynomial (Fin 2) R :=
  eval₂Hom C (Fin.insertNth (α := fun _ : Fin 3 => MvPolynomial (Fin 2) R) c 1 X)
def directChartLinearMap (c : Fin 3) :
    MvPolynomial (Fin 3) R →ₗ[R] MvPolynomial (Fin 2) R where
  toFun := directChartHom c
  map_add' := (directChartHom c).map_add
  map_smul' a f := by simp [smul_eq_C_mul, directChartHom]
def universalJetLinearMap {ι : Type*} (i : ι) (s : Fin 2 →₀ ℕ) :
    MvPolynomial (Fin 2) R →ₗ[R] MvPolynomial (ι × Fin 2) R where
  toFun := universalJetCoefficient i s
  map_add' := universalJetCoefficient_add i s
  map_smul' a f := by
    simp only [smul_eq_C_mul, universalJetCoefficient_C_mul, RingHom.id_apply]
theorem linearMap_eq_sum_basis {κ M : Type*} [Fintype κ] [DecidableEq κ]
    [AddCommMonoid M] [Module R M] (L : (κ → R) →ₗ[R] M) (x : κ → R) :
    L x = ∑ j, x j • L (Pi.single j 1) := by
  classical
  have hx : x = ∑ j, x j • (Pi.single j (1 : R) : κ → R) := by
    funext j
    simp [Pi.single_apply]
  conv_lhs => rw [hx]
  simp only [map_sum, map_smul]
end Nagata.W27
end
end
section
namespace Nagata.W27
noncomputable section
open MvPolynomial
end
end Nagata.W27
end
section
noncomputable section
namespace Nagata.W27
open MvPolynomial
variable {R : Type*} [CommRing R]
end Nagata.W27
end
end
section
noncomputable section
namespace Nagata.W27
open MvPolynomial
variable {σ ρ κ K : Type*} [Field K]
variable [Fintype ρ] [Fintype κ] [DecidableEq κ]
end Nagata.W27
end
end
section
noncomputable section
namespace Nagata.W27
open MvPolynomial
variable {r : ℕ} {R : Type*} [CommRing R]
def planeJetExponent {m : Fin r → ℕ} (row : PlaneJet r m) : Fin 2 →₀ ℕ :=
  Nagata.Workers.W30.exponentPair row.2.val.1.val row.2.val.2.val
theorem all_orders_iff_universal_jets (p : Fin r × Fin 2 → R)
    (m : Fin r → ℕ) (f : Fin r → MvPolynomial (Fin 2) R) :
    (∀ i, Nagata.AffineMultiplicity.orderAtLeast (fun j => p (i, j)) (m i) (f i)) ↔
      ∀ row : PlaneJet r m,
        eval p (universalJetCoefficient row.1 (planeJetExponent row) (f row.1)) = 0 := by
  constructor
  · intro h row
    rw [eval_universalJetCoefficient]
    exact (Nagata.AffineMultiplicity.orderAtLeast_finTwo_iff_taylor_coeff
      _ _ _).mp (h row.1) row.2.val.1.val row.2.val.2.val row.2.property
  · intro h i
    apply (Nagata.AffineMultiplicity.orderAtLeast_finTwo_iff_taylor_coeff _ _ _).mpr
    intro u v huv
    have hu : u < m i := by omega
    have hv : v < m i := by omega
    let row : PlaneJet r m := ⟨i, ⟨(⟨u, hu⟩, ⟨v, hv⟩), huv⟩⟩
    have hr := h row
    rw [eval_universalJetCoefficient] at hr
    exact hr
end Nagata.W27
end
end
section
noncomputable section
namespace Nagata.W27
open scoped BigOperators
open MvPolynomial
open Classical
variable {R : Type*} [CommRing R]
variable {r : ℕ}
def chartJetPolynomialMap (c : Fin r → Fin 3) (d : ℕ) (m : Fin r → ℕ)
    (row : PlaneJet r m) :
    homogeneousSubmodule (Fin 3) R d →ₗ[R] MvPolynomial (Fin r × Fin 2) R :=
  (universalJetLinearMap row.1 (planeJetExponent row)).comp
    ((directChartLinearMap (c row.1)).comp (homogeneousSubmodule (Fin 3) R d).subtype)
def chartPlaneJetMatrix (c : Fin r → Fin 3) (d : ℕ) (m : Fin r → ℕ) :
    Matrix (PlaneJet r m) (HomogeneousMonomial d) (MvPolynomial (Fin r × Fin 2) R) :=
  fun row col => chartJetPolynomialMap c d m row
    ((homogeneousCoordinates d).symm (Pi.single col 1))
theorem coefficientEquation_chartPlaneJetMatrix (c : Fin r → Fin 3)
    (d : ℕ) (m : Fin r → ℕ) (p : Fin r × Fin 2 → R)
    (F : homogeneousSubmodule (Fin 3) R d) (row : PlaneJet r m) :
    coefficientEquation (chartPlaneJetMatrix c d m) p (homogeneousCoordinates d F) row =
      eval p (universalJetCoefficient row.1 (planeJetExponent row)
        (directChartHom (c row.1) F.val)) := by
  classical
  have h := linearMap_eq_sum_basis
    ((chartJetPolynomialMap c d m row).comp (homogeneousCoordinates d).symm.toLinearMap)
    (homogeneousCoordinates d F)
  have he := congrArg (eval p) h
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, map_sum, smul_eval,
    chartPlaneJetMatrix, chartJetPolynomialMap, universalJetLinearMap,
    directChartLinearMap, Submodule.coe_subtype, LinearMap.coe_mk,
    AddHom.coe_mk, coefficientEquation, mul_comm] using he.symm
theorem chart_orders_iff_kernel (c : Fin r → Fin 3)
    (d : ℕ) (m : Fin r → ℕ) (p : Fin r × Fin 2 → R)
    (F : homogeneousSubmodule (Fin 3) R d) :
    (∀ i, Nagata.AffineMultiplicity.orderAtLeast (fun j => p (i, j)) (m i)
      (directChartHom (c i) F.val)) ↔
      coefficientLinearMap (chartPlaneJetMatrix c d m) p (homogeneousCoordinates d F) = 0 := by
  rw [all_orders_iff_universal_jets]
  change (∀ row, _) ↔ (fun row => coefficientEquation _ _ _ row) = (fun _ => 0)
  rw [funext_iff]
  exact forall_congr' fun row => by rw [coefficientEquation_chartPlaneJetMatrix]
theorem exists_nonzero_form_iff_chart_kernel (c : Fin r → Fin 3)
    (d : ℕ) (m : Fin r → ℕ) (p : Fin r × Fin 2 → R) :
    (∃ F : homogeneousSubmodule (Fin 3) R d, F.val ≠ 0 ∧
      ∀ i, Nagata.AffineMultiplicity.orderAtLeast (fun j => p (i, j)) (m i)
        (directChartHom (c i) F.val)) ↔
      ∃ v : HomogeneousMonomial d → R, v ≠ 0 ∧
        coefficientLinearMap (chartPlaneJetMatrix c d m) p v = 0 := by
  constructor
  · rintro ⟨F, hF, horder⟩
    exact ⟨homogeneousCoordinates d F,
      (homogeneousCoordinates_ne_zero_iff d F).mpr hF,
      (chart_orders_iff_kernel c d m p F).mp horder⟩
  · rintro ⟨v, hv, hker⟩
    refine ⟨(homogeneousCoordinates d).symm v,
      (homogeneousCoordinates_symm_ne_zero_iff d v).mpr hv, ?_⟩
    apply (chart_orders_iff_kernel c d m p _).mpr
    simpa only [LinearEquiv.apply_symm_apply] using hker
end Nagata.W27
end
end
section
noncomputable section
namespace Nagata.W27
open MvPolynomial
open Classical
variable {r : ℕ} {K : Type*} [Field K]
end Nagata.W27
end
end
end OAI
-- AnalyticScaling
namespace OAI
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology
variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
theorem comp_coeff_eq_zero_below
    (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F)
    (m : ℕ) (hq : ∀ n < m, q n = 0) :
    ∀ n < m, (q.comp p) n = 0 := by
  intro n hn
  ext v
  simp only [FormalMultilinearSeries.comp, sum_apply,
    FormalMultilinearSeries.compAlongComposition_apply,
    zero_apply]
  apply Finset.sum_eq_zero
  intro c hc
  rw [hq c.length (lt_of_le_of_lt c.length_le hn)]
  rfl
def HasAnalyticOrderAtLeast (f : E → F) (x : E) (m : ℕ) : Prop :=
  ∃ p : FormalMultilinearSeries 𝕜 E F,
    HasFPowerSeriesAt f p x ∧ ∀ n < m, p n = 0
theorem HasAnalyticOrderAtLeast.comp {g : F → G} {f : E → F} {x : E} {m : ℕ}
    (hg : HasAnalyticOrderAtLeast (𝕜 := 𝕜) g (f x) m)
    (hf : AnalyticAt 𝕜 f x) :
    HasAnalyticOrderAtLeast (𝕜 := 𝕜) (g ∘ f) x m := by
  obtain ⟨q, hq, hzero⟩ := hg
  obtain ⟨p, hp⟩ := hf
  exact ⟨q.comp p, hq.comp hp, comp_coeff_eq_zero_below q p m hzero⟩
theorem HasAnalyticOrderAtLeast.congr {f g : E → F} {x : E} {m : ℕ}
    (hf : HasAnalyticOrderAtLeast (𝕜 := 𝕜) f x m)
    (hfg : f =ᶠ[𝓝 x] g) : HasAnalyticOrderAtLeast (𝕜 := 𝕜) g x m := by
  obtain ⟨p, hp, hzero⟩ := hf
  exact ⟨p, hp.congr hfg, hzero⟩
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology
theorem normal_equation_affine_velocity_limit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (G : E → ℂ) (L : E →L[ℂ] ℂ) (p V : E)
    (hG : HasFDerivAt G L p) (hp : G p = 0) :
    Filter.Tendsto (fun s : ℂ => s⁻¹ * G (p + s • V)) (𝓝[≠] 0) (𝓝 (L V)) := by
  have hm : HasDerivAt (fun s : ℂ => p + s • V) V 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const V).const_add p
  have hd : HasDerivAt (fun s : ℂ => G (p + s • V)) (L V) 0 := by
    have hh : HasFDerivAt G L (p + (0 : ℂ) • V) := by simpa using hG
    exact hh.comp_hasDerivAt 0 hm
  simpa only [zero_add, zero_smul, add_zero, hp, sub_zero, smul_eq_mul] using
    hd.tendsto_slope_zero
end Nagata.Workers.W28
end
end
section
namespace Nagata.VariableUnitOrder
open scoped Topology
open Nagata.Workers.W28
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end Nagata.VariableUnitOrder
end
section
noncomputable section
namespace Nagata.Workers.W28
def analyticNormalScale (s : ℂ) (x : ℂ × ℂ) : ℂ × ℂ := (x.1, s * x.2)
theorem analyticNormalScale_analyticAt (s : ℂ) (x : ℂ × ℂ) :
    AnalyticAt ℂ (analyticNormalScale s) x := by
  have hh := ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt x).const_smul (c := s)
  exact ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt x).prod (by
    simpa only [Pi.smul_def, smul_eq_mul, ContinuousLinearMap.coe_snd'] using hh)
end Nagata.Workers.W28
end
end
end OAI
-- AnalyticJets
namespace OAI
section
namespace Nagata.Workers.W17
open Filter
open scoped Topology
variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜]
    [TopologicalSpace V] [T2Space V] [Zero V]
theorem continuous_value_zero_of_eventually_cofinite
    (f : 𝕜 → V) (x : 𝕜) (exceptional : Finset 𝕜)
    (hf : ContinuousAt f x)
    (hzero : ∀ᶠ s in 𝓝 x, s ∉ exceptional → f s = 0) : f x = 0 := by
  have he : ∀ᶠ s in 𝓝[≠] x, s ∉ exceptional :=
    exceptional.eventually_cofinite_notMem.filter_mono (nhdsNE_le_cofinite x)
  have hlocal : ∀ᶠ s in 𝓝[≠] x, s ∉ exceptional → f s = 0 :=
    hzero.filter_mono nhdsWithin_le_nhds
  have hz : f =ᶠ[𝓝[≠] x] fun _ => 0 :=
    (he.and hlocal).mono fun s hs => hs.2 hs.1
  exact tendsto_nhds_unique_of_eventuallyEq
    (hf.mono_left nhdsWithin_le_nhds) tendsto_const_nhds hz
variable {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
theorem local_cofinite_moving_derivative_jets
    (family : 𝕜 → E → F) (center : 𝕜 → E) (x : 𝕜)
    (exceptional : Finset 𝕜) (m : Nat)
    (hcontinuous : ∀ n < m,
      ContinuousAt (fun s => iteratedFDeriv 𝕜 n (family s) (center s)) x)
    (hjets : ∀ᶠ s in 𝓝 x, s ∉ exceptional → ∀ n < m,
      iteratedFDeriv 𝕜 n (family s) (center s) = 0) :
    ∀ n < m, iteratedFDeriv 𝕜 n (family x) (center x) = 0 := by
  intro n hn
  exact continuous_value_zero_of_eventually_cofinite
    (fun s => iteratedFDeriv 𝕜 n (family s) (center s)) x exceptional
    (hcontinuous n hn) (hjets.mono fun s hs hE => hs hE n hn)
end Nagata.Workers.W17
end
section
noncomputable section
namespace Nagata.Workers.W17
open Nagata.Workers.W28
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
theorem powerSeries_diagonal_zero_of_iteratedFDeriv_zero
    {f : E → F} {x : E} {p : FormalMultilinearSeries 𝕜 E F} {n : ℕ}
    (hp : HasFPowerSeriesAt f p x) (hn : iteratedFDeriv 𝕜 n f x = 0) (v : E) :
    p n (fun _ => v) = 0 := by
  obtain ⟨r, hr⟩ := hp
  have he := hr.iteratedFDeriv_eq_sum_of_completeSpace (fun _ : Fin n => v)
  have hz : n.factorial • p n (fun _ => v) = 0 := by
    simpa only [hn, zero_apply, Finset.sum_const,
      Finset.card_univ, Fintype.card_perm, Fintype.card_fin] using he.symm
  have hz' : (n.factorial : 𝕜) • p n (fun _ => v) = 0 := by
    simpa only [Nat.cast_smul_eq_nsmul] using hz
  exact (smul_eq_zero.mp hz').resolve_left (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
theorem analytic_order_of_iteratedFDeriv_zero
    {f : E → F} {x : E} (hf : AnalyticAt 𝕜 f x) (m : ℕ)
    (hz : ∀ n < m, iteratedFDeriv 𝕜 n f x = 0) :
    HasAnalyticOrderAtLeast (𝕜 := 𝕜) f x m := by
  obtain ⟨p, r, hp⟩ := hf
  let q : FormalMultilinearSeries 𝕜 E F := fun n => if n < m then 0 else p n
  have hnorm : ∀ n, ‖q n‖ ≤ ‖p n‖ := by
    intro n
    by_cases hn : n < m
    · simp [q, hn]
    · simp [q, hn]
  have hdiag : ∀ n v, q n (fun _ => v) = p n (fun _ => v) := by
    intro n v
    by_cases hn : n < m
    · simp [q, hn, powerSeries_diagonal_zero_of_iteratedFDeriv_zero
        hp.hasFPowerSeriesAt (hz n hn) v]
    · simp [q, hn]
  refine ⟨q, ⟨r, ?_⟩, ?_⟩
  · refine ⟨hp.r_le.trans (FormalMultilinearSeries.radius_le_of_le hnorm), hp.r_pos, ?_⟩
    intro y hy
    simpa only [hdiag] using hp.hasSum hy
  · intro n hn
    simp [q, hn]
end Nagata.Workers.W17
end
end
section
namespace Nagata.Workers.W17
open Nagata.Workers.W28
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
theorem analytic_order_const_smul {f : E → F} {x : E} {m : Nat}
    (hf : HasAnalyticOrderAtLeast (𝕜 := 𝕜) f x m) (c : 𝕜) :
    HasAnalyticOrderAtLeast (𝕜 := 𝕜) (c • f) x m := by
  obtain ⟨p, hp, hz⟩ := hf
  refine ⟨c • p, hp.const_smul, ?_⟩
  intro n hn
  simp [hz n hn]
theorem analytic_order_const_smul_iff (f : E → F) (x : E) (m : Nat)
    (c : 𝕜) (hc : c ≠ 0) :
    HasAnalyticOrderAtLeast (𝕜 := 𝕜) (c • f) x m ↔
      HasAnalyticOrderAtLeast (𝕜 := 𝕜) f x m := by
  constructor
  · intro h
    have hi := analytic_order_const_smul h c⁻¹
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hi
  · intro h
    exact analytic_order_const_smul h c
theorem analytic_order_const_mul_iff (f : E → 𝕜) (x : E) (m : Nat)
    (c : 𝕜) (hc : c ≠ 0) :
    HasAnalyticOrderAtLeast (𝕜 := 𝕜) (fun y => c * f y) x m ↔
      HasAnalyticOrderAtLeast (𝕜 := 𝕜) f x m :=
  analytic_order_const_smul_iff f x m c hc
end Nagata.Workers.W17
end
section
namespace Nagata.Workers.W17
open scoped ContDiff
variable {𝕜 P E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup P] [NormedSpace 𝕜 P]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
theorem contDiffAt_parameter_iteratedFDeriv
    (family : P → E → F) (p : P × E)
    (hf : ContDiffAt 𝕜 ∞ (Function.uncurry family) p) (n : Nat) :
    ContDiffAt 𝕜 ∞ (fun q : P × E => iteratedFDeriv 𝕜 n (family q.1) q.2) p := by
  induction n with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def,
      LinearIsometryEquiv.coe_coe'', Function.uncurry_def] using
      hf.continuousLinearMap_comp
        ((continuousMultilinearCurryFin0 𝕜 E F).symm :
          F →L[𝕜] E [×0]→L[𝕜] F)
  | succ n ih =>
    have hprojection : ContDiffAt 𝕜 ∞
        (fun q : (P × E) × E => (q.1.1, q.2)) (p, p.2) :=
      contDiffAt_fst.fst.prodMk contDiffAt_snd
    have hjoint : ContDiffAt 𝕜 ∞
        (fun q : (P × E) × E => iteratedFDeriv 𝕜 n (family q.1.1) q.2) (p, p.2) :=
      by
        have ih' : ContDiffAt 𝕜 ∞
            (fun q : P × E => iteratedFDeriv 𝕜 n (family q.1) q.2) (p.1, p.2) := by
          simpa only [Prod.eta] using ih
        simpa only [Function.comp_def] using ih'.comp (p, p.2) hprojection
    have hd : ContDiffAt 𝕜 ∞
        (fun q : P × E => fderiv 𝕜 (iteratedFDeriv 𝕜 n (family q.1)) q.2) p :=
      hjoint.fderiv contDiffAt_snd (by simp)
    simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_def] using
      (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) F).symm.contDiff.contDiffAt.comp
        p hd
theorem analytic_moving_derivative_continuousAt [CompleteSpace F]
    (family : P → E → F) (center : P → E) (s₀ : P)
    (hf : AnalyticAt 𝕜 (Function.uncurry family) (s₀, center s₀))
    (hc : ContinuousAt center s₀) (n : Nat) :
    ContinuousAt (fun s => iteratedFDeriv 𝕜 n (family s) (center s)) s₀ := by
  have hpartial : ContinuousAt
      (fun q : P × E => iteratedFDeriv 𝕜 n (family q.1) q.2) (s₀, center s₀) :=
    (contDiffAt_parameter_iteratedFDeriv family (s₀, center s₀) hf.contDiffAt n).continuousAt
  have hcurve : ContinuousAt (fun s : P => (s, center s)) s₀ :=
    continuousAt_id.prodMk hc
  simpa only [Function.comp_def] using hpartial.comp (f := fun s : P => (s, center s)) hcurve
theorem analytic_local_cofinite_moving_derivative_jets [CompleteSpace F]
    (family : 𝕜 → E → F) (center : 𝕜 → E) (s₀ : 𝕜)
    (exceptional : Finset 𝕜) (m : Nat)
    (hf : AnalyticAt 𝕜 (Function.uncurry family) (s₀, center s₀))
    (hc : ContinuousAt center s₀)
    (hjets : ∀ᶠ s in nhds s₀, s ∉ exceptional → ∀ n < m,
      iteratedFDeriv 𝕜 n (family s) (center s) = 0) :
    ∀ n < m, iteratedFDeriv 𝕜 n (family s₀) (center s₀) = 0 := by
  exact local_cofinite_moving_derivative_jets family center s₀ exceptional m
    (fun n _ => analytic_moving_derivative_continuousAt family center s₀ hf hc n) hjets
end Nagata.Workers.W17
end
end OAI
-- FrechetMultiplicity
namespace OAI
section
namespace Nagata.W19
open scoped Topology
open Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
theorem directional_derivative_taylor_vanishing
    {H : E → ℂ} {p : E} (hH : AnalyticAt ℂ H p) (v : E) (m : ℕ)
    (hvan : ∀ n < m, iteratedFDeriv ℂ n H p = 0) :
    ∀ n, n + 1 < m →
      iteratedFDeriv ℂ n (fun z => fderiv ℂ H z v) p = 0 := by
  intro n hn
  have hz : iteratedFDeriv ℂ n (fderiv ℂ H) p = 0 := by
    apply norm_eq_zero.mp
    rw [norm_iteratedFDeriv_fderiv, hvan (n + 1) hn, norm_zero]
  change iteratedFDeriv ℂ n ((ContinuousLinearMap.apply ℂ ℂ v) ∘ fderiv ℂ H) p = 0
  rw [(ContinuousLinearMap.apply ℂ ℂ v).iteratedFDeriv_comp_left
    (hH.fderiv.contDiffAt (n := (n : WithTop ℕ∞))) le_rfl, hz]
  ext w
  simp
noncomputable def directionalIterate (v : E) : ℕ → (E → ℂ) → E → ℂ
  | 0, H => H
  | b + 1, H => directionalIterate v b (fun z => fderiv ℂ H z v)
theorem directionalIterate_analyticAt {H : E → ℂ} {p : E}
    (hH : AnalyticAt ℂ H p) (v : E) (b : ℕ) :
    AnalyticAt ℂ (directionalIterate v b H) p := by
  induction b generalizing H with
  | zero => exact hH
  | succ b ih =>
    apply ih
    exact ((ContinuousLinearMap.apply ℂ ℂ v).analyticAt _).comp hH.fderiv
theorem directionalIterate_taylor_vanishing {H : E → ℂ} {p : E}
    (hH : AnalyticAt ℂ H p) (v : E) (m b : ℕ)
    (hvan : ∀ n < m, iteratedFDeriv ℂ n H p = 0) :
    ∀ n, n + b < m → iteratedFDeriv ℂ n (directionalIterate v b H) p = 0 := by
  induction b generalizing H m with
  | zero => simpa [directionalIterate] using hvan
  | succ b ih =>
    have ha : AnalyticAt ℂ (fun z => fderiv ℂ H z v) p :=
      ((ContinuousLinearMap.apply ℂ ℂ v).analyticAt _).comp hH.fderiv
    have hv : ∀ n < m - 1, iteratedFDeriv ℂ n (fun z => fderiv ℂ H z v) p = 0 := by
      intro n hn
      exact directional_derivative_taylor_vanishing hH v m hvan n (by omega)
    intro n hn
    exact ih ha (m - 1) hv n (by omega)
theorem analytic_pullback_taylor_vanishing
    [CompleteSpace E]
    {H : E → ℂ} {p : ℂ} {γ : ℂ → E}
    (hH : AnalyticAt ℂ H (γ p)) (hγ : AnalyticAt ℂ γ p)
    (m : ℕ) (hvan : ∀ n < m, iteratedFDeriv ℂ n H (γ p) = 0) :
    ∀ n < m, iteratedFDeriv ℂ n (H ∘ γ) p = 0 := by
  intro n hn
  rw [iteratedFDeriv_comp (hH.contDiffAt (n := (n : WithTop ℕ∞)))
    (hγ.contDiffAt (n := (n : WithTop ℕ∞))) le_rfl]
  unfold FormalMultilinearSeries.taylorComp
  apply Finset.sum_eq_zero
  intro c _
  ext
  simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply, ftaylorSeries]
  rw [hvan c.length (lt_of_le_of_lt c.length_le hn)]
  simp
theorem transverse_restriction_order_of_total_taylor_vanishing
    {H : (ℂ × ℂ) → ℂ} (ξ : ℂ)
    (hH : AnalyticAt ℂ H (ξ, 0)) (m b : ℕ)
    (hvan : ∀ n < m, iteratedFDeriv ℂ n H (ξ, 0) = 0) :
    (m - b : ℕ) ≤ analyticOrderAt
      (fun x => directionalIterate (0, 1) b H (x, 0)) ξ := by
  let G := directionalIterate (0, 1) b H
  have hG : AnalyticAt ℂ G (ξ, 0) := directionalIterate_analyticAt hH (0, 1) b
  have hγ : AnalyticAt ℂ (fun x : ℂ => (x, (0 : ℂ))) ξ := by fun_prop
  apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hG.comp (f := fun x : ℂ => (x, (0 : ℂ))) (x := ξ) hγ)).mpr
  intro n hn
  rw [iteratedDeriv_eq_iteratedFDeriv]
  have hv : ∀ j < m - b, iteratedFDeriv ℂ j G (ξ, 0) = 0 := by
    intro j hj
    exact directionalIterate_taylor_vanishing hH (0, 1) m b hvan j (by omega)
  have hz := analytic_pullback_taylor_vanishing (γ := fun x : ℂ => (x, (0 : ℂ))) (p := ξ) hG hγ (m - b) hv n hn
  simpa only [Function.comp_def, zero_apply] using congrArg (fun L => L (fun _ => (1 : ℂ))) hz
theorem directionalIterate_vertical_eq_iteratedDeriv
    {H : (ℂ × ℂ) → ℂ} {x y : ℂ} (hH : AnalyticAt ℂ H (x, y)) (b : ℕ) :
    directionalIterate (0, 1) b H (x, y) =
      iteratedDeriv b (fun t => H (x, t)) y := by
  induction b generalizing H with
  | zero => simp [directionalIterate]
  | succ b ih =>
    let G : (ℂ × ℂ) → ℂ := fun z => fderiv ℂ H z (0, 1)
    have hG : AnalyticAt ℂ G (x, y) := by
      change AnalyticAt ℂ ((ContinuousLinearMap.apply ℂ ℂ ((0, 1) : ℂ × ℂ)) ∘
        fderiv ℂ H) (x, y)
      exact ((ContinuousLinearMap.apply ℂ ℂ ((0, 1) : ℂ × ℂ)).analyticAt _).comp hH.fderiv
    have hc : ContinuousAt (fun t : ℂ => (x, t)) y := by fun_prop
    have hev : ∀ᶠ t in 𝓝 y, AnalyticAt ℂ H (x, t) :=
      hc.tendsto.eventually hH.eventually_analyticAt
    have heq : (fun t => deriv (fun u => H (x, u)) t) =ᶠ[𝓝 y]
        (fun t => G (x, t)) := by
      filter_upwards [hev] with t ht
      have hline : HasDerivAt (fun u : ℂ => (x, u)) (0, 1) t :=
        by simpa using ((hasFDerivAt_const (𝕜 := ℂ) x t).prodMk
          (hasFDerivAt_id t)).hasDerivAt
      exact (ht.differentiableAt.hasFDerivAt.comp_hasDerivAt t hline).deriv
    change directionalIterate (0, 1) b G (x, y) = _
    rw [ih hG, iteratedDeriv_succ']
    exact (Filter.EventuallyEq.iteratedDeriv_eq b heq).symm
theorem transverse_iteratedDeriv_order_of_total_taylor_vanishing
    {H : (ℂ × ℂ) → ℂ} (ξ : ℂ)
    (hH : AnalyticAt ℂ H (ξ, 0)) (m b : ℕ)
    (hvan : ∀ n < m, iteratedFDeriv ℂ n H (ξ, 0) = 0) :
    (m - b : ℕ) ≤ analyticOrderAt
      (fun x => iteratedDeriv b (fun y => H (x, y)) 0) ξ := by
  have hc : ContinuousAt (fun x : ℂ => (x, (0 : ℂ))) ξ := by fun_prop
  have hev : ∀ᶠ x in 𝓝 ξ, AnalyticAt ℂ H (x, 0) :=
    hc.tendsto.eventually hH.eventually_analyticAt
  have heq : (fun x => directionalIterate (0, 1) b H (x, 0)) =ᶠ[𝓝 ξ]
      (fun x => iteratedDeriv b (fun y => H (x, y)) 0) := by
    filter_upwards [hev] with x hx
    exact directionalIterate_vertical_eq_iteratedDeriv hx b
  rw [← analyticOrderAt_congr heq]
  exact transverse_restriction_order_of_total_taylor_vanishing ξ hH m b hvan
end Nagata.W19
end
section
namespace Nagata.W19
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
private theorem derivSeries_coeff_zero
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (P : FormalMultilinearSeries ℂ E F) (n : ℕ) (hzero : P (n + 1) = 0) :
    P.derivSeries n = 0 := by
  have hz' : ∀ j, j = n + 1 → P j = 0 := by
    intro j hj
    subst j
    exact hzero
  have hz : P (1 + n) = 0 := hz' (1 + n) (Nat.add_comm 1 n)
  ext v w
  simp [FormalMultilinearSeries.derivSeries,
    ContinuousLinearMap.compFormalMultilinearSeries_apply,
    FormalMultilinearSeries.changeOriginSeries,
    FormalMultilinearSeries.changeOriginSeriesTerm, hz]
private theorem iteratedFDeriv_zero_of_series_coeff (n : ℕ) :
    ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
      {H : E → F} {p : E} {P : FormalMultilinearSeries ℂ E F},
      HasFPowerSeriesAt H P p → P n = 0 → iteratedFDeriv ℂ n H p = 0 := by
  induction n with
  | zero =>
    intro F _ _ _ H p P hP hzero
    ext v
    simpa [hzero] using (hP.coeff_zero v).symm
  | succ n ih =>
    intro F _ _ _ H p P hP hzero
    obtain ⟨r, hr⟩ := hP
    have hd : P.derivSeries n = 0 := derivSeries_coeff_zero P n hzero
    have hi := ih (F := E →L[ℂ] F) hr.fderiv.hasFPowerSeriesAt hd
    apply norm_eq_zero.mp
    rw [← norm_iteratedFDeriv_fderiv, hi, norm_zero]
theorem total_taylor_vanishing_of_powerSeries
    {H : E → ℂ} {p : E} {P : FormalMultilinearSeries ℂ E ℂ}
    (hP : HasFPowerSeriesAt H P p) (m : ℕ) (hzero : ∀ n < m, P n = 0) :
    ∀ n < m, iteratedFDeriv ℂ n H p = 0 := by
  intro n hn
  exact iteratedFDeriv_zero_of_series_coeff n hP (hzero n hn)
theorem transverse_iteratedDeriv_order_of_powerSeries
    {H : (ℂ × ℂ) → ℂ} {P : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ}
    (ξ : ℂ) (hP : HasFPowerSeriesAt H P (ξ, 0))
    (m b : ℕ) (hzero : ∀ n < m, P n = 0) :
    (m - b : ℕ) ≤ analyticOrderAt
      (fun x => iteratedDeriv b (fun y => H (x, y)) 0) ξ := by
  apply transverse_iteratedDeriv_order_of_total_taylor_vanishing ξ ⟨P, hP⟩ m b
  exact total_taylor_vanishing_of_powerSeries hP m hzero
end Nagata.W19
end
section
namespace Nagata.W19
open scoped Topology
open Filter
theorem analyticAt_transverse_iteratedDeriv
    {H : (ℂ × ℂ) → ℂ} (ξ : ℂ) (hH : AnalyticAt ℂ H (ξ, 0)) (b : ℕ) :
    AnalyticAt ℂ (fun x => iteratedDeriv b (fun y => H (x, y)) 0) ξ := by
  have hγ : AnalyticAt ℂ (fun x : ℂ => (x, (0 : ℂ))) ξ := by fun_prop
  have hG := (directionalIterate_analyticAt hH (0, 1) b).comp
    (f := fun x : ℂ => (x, (0 : ℂ))) (x := ξ) hγ
  apply hG.congr
  have hev : ∀ᶠ x in 𝓝 ξ, AnalyticAt ℂ H (x, 0) :=
    hγ.continuousAt.tendsto.eventually hH.eventually_analyticAt
  filter_upwards [hev] with x hx
  exact directionalIterate_vertical_eq_iteratedDeriv hx b
theorem mixed_iteratedDeriv_zero_of_powerSeries
    {H : (ℂ × ℂ) → ℂ} {P : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ}
    (ξ : ℂ) (hP : HasFPowerSeriesAt H P (ξ, 0)) (m : ℕ)
    (hzero : ∀ n < m, P n = 0) (ell b : ℕ) (hlt : ell + b < m) :
    iteratedDeriv ell (fun x => iteratedDeriv b (fun y => H (x, y)) 0) ξ = 0 := by
  have ha := analyticAt_transverse_iteratedDeriv ξ ⟨P, hP⟩ b
  have ho := transverse_iteratedDeriv_order_of_powerSeries ξ hP m b hzero
  exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ha).mp ho ell (by omega)
end Nagata.W19
end
end OAI
-- AnalyticTaylor
namespace OAI
section
noncomputable section
namespace Nagata.Workers.W28
open scoped BigOperators
private theorem analytic_order_zero (m : ℕ) :
    HasAnalyticOrderAtLeast (𝕜 := ℂ) (fun _ : ℂ × ℂ => (0 : ℂ)) 0 m := by
  refine ⟨constFormalMultilinearSeries ℂ (ℂ × ℂ) 0, hasFPowerSeriesAt_const, ?_⟩
  intro n hn
  cases n <;> ext v <;> rfl
private theorem analytic_order_add {f g : ℂ × ℂ → ℂ} {m : ℕ}
    (hf : HasAnalyticOrderAtLeast (𝕜 := ℂ) f 0 m)
    (hg : HasAnalyticOrderAtLeast (𝕜 := ℂ) g 0 m) :
    HasAnalyticOrderAtLeast (𝕜 := ℂ) (f + g) 0 m := by
  obtain ⟨p, hp, hz⟩ := hf
  obtain ⟨q, hq, hqz⟩ := hg
  refine ⟨p + q, hp.add hq, ?_⟩
  intro n hn
  simp [hz n hn, hqz n hn]
theorem analytic_order_const_smul {f : ℂ × ℂ → ℂ} {m : ℕ}
    (hf : HasAnalyticOrderAtLeast (𝕜 := ℂ) f 0 m) (c : ℂ) :
    HasAnalyticOrderAtLeast (𝕜 := ℂ) (c • f) 0 m := by
  obtain ⟨p, hp, hz⟩ := hf
  refine ⟨c • p, hp.const_smul, ?_⟩
  intro n hn
  simp [hz n hn]
theorem monomial_hasAnalyticOrderAtLeast (a b m : ℕ) (hm : m ≤ a + b) :
    HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun x : ℂ × ℂ => x.1 ^ a * x.2 ^ b) 0 m := by
  let q := ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin (a + b)) ℂ
  let u : (ℂ × ℂ) →L[ℂ] (Fin (a + b) → ℂ) :=
    ContinuousLinearMap.pi (fun i =>
      if i.val < a then ContinuousLinearMap.fst ℂ ℂ ℂ else ContinuousLinearMap.snd ℂ ℂ ℂ)
  have hq : HasFPowerSeriesAt q q.toFormalMultilinearSeries (u 0) := by
    simpa only [map_zero] using q.hasFiniteFPowerSeriesOnBall.toHasFPowerSeriesOnBall.hasFPowerSeriesAt
  have hfun : (q ∘ u) = (fun x : ℂ × ℂ => x.1 ^ a * x.2 ^ b) := by
    funext x
    simp only [q, u, Function.comp_apply, ContinuousMultilinearMap.mkPiAlgebra_apply,
      ContinuousLinearMap.pi_apply]
    rw [Fin.prod_univ_add]
    simp
  refine ⟨q.toFormalMultilinearSeries.compContinuousLinearMap u, ?_, ?_⟩
  · rw [← hfun]
    exact hq.compContinuousLinearMap
  · intro n hn
    have hne : a + b ≠ n := by omega
    ext v
    simp [FormalMultilinearSeries.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.toFormalMultilinearSeries, hne]
theorem analytic_order_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → ℂ × ℂ → ℂ) (m : ℕ)
    (hf : ∀ i ∈ s, HasAnalyticOrderAtLeast (𝕜 := ℂ) (f i) 0 m) :
    HasAnalyticOrderAtLeast (𝕜 := ℂ) (fun x => ∑ i ∈ s, f i x) 0 m := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using analytic_order_zero m
  | @insert i s hi ih =>
      have hsum := analytic_order_add (hf i (Finset.mem_insert_self i s))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
      simpa only [Finset.sum_insert hi, Pi.add_def] using hsum
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
open scoped BigOperators
theorem eval_hasAnalyticOrderAtLeast_of_coeff
    (P : MvPolynomial (Fin 2) ℂ) (m : ℕ)
    (hcoeff : ∀ ell b, ell + b < m → P.coeff (Nagata.Workers.W30.exponentPair ell b) = 0) :
    HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun x : ℂ × ℂ => MvPolynomial.eval (fun i => if i = 0 then x.1 else x.2) P) 0 m := by
  have hterm (d : Fin 2 →₀ ℕ) (hd : d ∈ P.support) :
      HasAnalyticOrderAtLeast (𝕜 := ℂ)
        (fun x : ℂ × ℂ => P.coeff d * (x.1 ^ d 0 * x.2 ^ d 1)) 0 m := by
    have hdegree : m ≤ d 0 + d 1 := by
      have hnonzero : P.coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
      have hnot : ¬d 0 + d 1 < m := by
        intro h
        apply hnonzero
        simpa only [Nagata.Workers.W30.exponentPair_eta] using hcoeff (d 0) (d 1) h
      omega
    simpa only [Pi.smul_def, smul_eq_mul] using
      analytic_order_const_smul (monomial_hasAnalyticOrderAtLeast (d 0) (d 1) m hdegree) (P.coeff d)
  have hsum := analytic_order_finset_sum P.support
    (fun d (x : ℂ × ℂ) => P.coeff d * (x.1 ^ d 0 * x.2 ^ d 1)) m hterm
  convert hsum using 1
  funext x
  rw [MvPolynomial.eval_eq']
  simp [Fin.prod_univ_two]
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
theorem polynomial_order_implies_analytic_order
    (P : MvPolynomial (Fin 2) ℂ) (p : ℂ × ℂ) (m : ℕ)
    (hP : Nagata.AffineMultiplicity.orderAtLeast
      (fun i : Fin 2 => if i = 0 then p.1 else p.2) m P) :
    HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun x : ℂ × ℂ => MvPolynomial.eval (fun i => if i = 0 then x.1 else x.2) P) p m := by
  let pv : Fin 2 → ℂ := fun i => if i = 0 then p.1 else p.2
  have hc := (Nagata.AffineMultiplicity.orderAtLeast_finTwo_iff_taylor_coeff pv m P).mp hP
  obtain ⟨q, hq, hz⟩ := eval_hasAnalyticOrderAtLeast_of_coeff
    (Nagata.AffineMultiplicity.translateHom pv P) m hc
  refine ⟨q, ?_, hz⟩
  have hs := hq.comp_sub p
  simp only [zero_add] at hs
  apply hs.congr
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [Nagata.AffineMultiplicity.eval_translate]
    apply congrArg (fun v : Fin 2 → ℂ => MvPolynomial.eval v P)
    funext i
    by_cases hi : i = 0 <;> simp [pv, hi]
end Nagata.Workers.W28
end
end
end OAI
-- NormalCharts
namespace OAI
section
noncomputable section
namespace Nagata.Workers.W28
abbrev ComplexPlane := ℂ × ℂ
def planePolynomialEval (G : MvPolynomial (Fin 2) ℂ) (z : ComplexPlane) : ℂ :=
  MvPolynomial.eval (fun i => if i = 0 then z.1 else z.2) G
def polynomialNormalCoordinates (G : MvPolynomial (Fin 2) ℂ)
    (z : ComplexPlane) : ComplexPlane := (z.1, planePolynomialEval G z)
theorem planePolynomialEval_analyticAt (G : MvPolynomial (Fin 2) ℂ)
    (p : ComplexPlane) : AnalyticAt ℂ (planePolynomialEval G) p := by
  obtain ⟨q, hq, hz⟩ := polynomial_order_implies_analytic_order G p 0
    (Nagata.AffineMultiplicity.orderAtLeast_zero _ _)
  exact hq.analyticAt
theorem polynomialNormalCoordinates_analyticAt (G : MvPolynomial (Fin 2) ℂ)
    (p : ComplexPlane) : AnalyticAt ℂ (polynomialNormalCoordinates G) p := by
  exact ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt p).prod
    (planePolynomialEval_analyticAt G p)
theorem exists_analytic_normal_chart
    (G : MvPolynomial (Fin 2) ℂ) (p : ComplexPlane)
    (hdet : (fderiv ℂ (polynomialNormalCoordinates G) p).det ≠ 0) :
    ∃ e : OpenPartialHomeomorph ComplexPlane ComplexPlane,
      (e : ComplexPlane → ComplexPlane) = polynomialNormalCoordinates G ∧
      p ∈ e.source ∧
      AnalyticAt ℂ e.symm (polynomialNormalCoordinates G p) := by
  let D := fderiv ℂ (polynomialNormalCoordinates G) p
  let L : ComplexPlane ≃L[ℂ] ComplexPlane :=
    D.toContinuousLinearEquivOfDetNeZero hdet
  have hL : (L : ComplexPlane →L[ℂ] ComplexPlane) = D :=
    D.coe_toContinuousLinearEquivOfDetNeZero hdet
  have ha := polynomialNormalCoordinates_analyticAt G p
  have hd : HasStrictFDerivAt (polynomialNormalCoordinates G)
      (L : ComplexPlane →L[ℂ] ComplexPlane) p := by
    rw [hL]
    exact ha.hasStrictFDerivAt
  let e := hd.toOpenPartialHomeomorph (polynomialNormalCoordinates G)
  have he : (e : ComplexPlane → ComplexPlane) = polynomialNormalCoordinates G := rfl
  have hp : p ∈ e.source := hd.mem_toOpenPartialHomeomorph_source
  refine ⟨e, he, hp, ?_⟩
  have hi : AnalyticAt ℂ e.symm (e p) :=
    e.analyticAt_symm' hp (by simpa only [he] using ha) (by simpa only [he] using hL.symm)
  simpa only [he] using hi
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology
theorem polynomial_order_in_rescaled_inverse_chart
    (P : MvPolynomial (Fin 2) ℂ)
    (e : OpenPartialHomeomorph ComplexPlane ComplexPlane)
    (s : ℂ) (q : ComplexPlane) (m : ℕ)
    (he : AnalyticAt ℂ e.symm (analyticNormalScale s q))
    (hP : Nagata.AffineMultiplicity.orderAtLeast
      (fun i : Fin 2 => if i = 0 then (e.symm (analyticNormalScale s q)).1
        else (e.symm (analyticNormalScale s q)).2) m P) :
    HasAnalyticOrderAtLeast (𝕜 := ℂ)
      ((planePolynomialEval P ∘ e.symm) ∘ analyticNormalScale s) q m := by
  have h := polynomial_order_implies_analytic_order P (e.symm (analyticNormalScale s q)) m hP
  exact (h.comp he).comp (analyticNormalScale_analyticAt s q)
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
def polynomialGradient (G : MvPolynomial (Fin 2) ℂ) (p : ComplexPlane) :
    ComplexPlane →L[ℂ] ℂ :=
  planePolynomialEval (MvPolynomial.pderiv 0 G) p • ContinuousLinearMap.fst ℂ ℂ ℂ +
  planePolynomialEval (MvPolynomial.pderiv 1 G) p • ContinuousLinearMap.snd ℂ ℂ ℂ
theorem planePolynomialEval_hasFDerivAt (G : MvPolynomial (Fin 2) ℂ)
    (p : ComplexPlane) :
    HasFDerivAt (planePolynomialEval G) (polynomialGradient G p) p := by
  induction G using MvPolynomial.induction_on with
  | C a =>
      have hf : planePolynomialEval (MvPolynomial.C a) = fun _ : ComplexPlane => a := by
        funext z
        simp [planePolynomialEval]
      have hg : polynomialGradient (MvPolynomial.C a) p = 0 := by
        apply ContinuousLinearMap.ext
        intro z
        simp [polynomialGradient, planePolynomialEval]
      rw [hf, hg]
      exact hasFDerivAt_const (𝕜 := ℂ) a p
  | add P Q hP hQ =>
      have hf : planePolynomialEval (P + Q) = fun z => planePolynomialEval P z + planePolynomialEval Q z := by
        funext z
        simp [planePolynomialEval]
      have hg : polynomialGradient (P + Q) p = polynomialGradient P p + polynomialGradient Q p := by
        apply ContinuousLinearMap.ext
        intro z
        simp [polynomialGradient, planePolynomialEval]
        ring
      rw [hf, hg]
      exact hP.add hQ
  | mul_X P i hP =>
      fin_cases i
      · have hf : planePolynomialEval (P * MvPolynomial.X 0) = fun z => planePolynomialEval P z * z.1 := by
          funext z
          simp [planePolynomialEval]
        have hg : polynomialGradient (P * MvPolynomial.X 0) p =
            planePolynomialEval P p • ContinuousLinearMap.fst ℂ ℂ ℂ +
              p.1 • polynomialGradient P p := by
          apply ContinuousLinearMap.ext
          intro z
          simp [polynomialGradient, planePolynomialEval]
          ring
        change HasFDerivAt (planePolynomialEval (P * MvPolynomial.X (0 : Fin 2))) (polynomialGradient (P * MvPolynomial.X (0 : Fin 2)) p) p
        rw [hf, hg]
        exact hP.mul ((ContinuousLinearMap.fst ℂ ℂ ℂ).hasFDerivAt (x := p))
      · have hf : planePolynomialEval (P * MvPolynomial.X 1) = fun z => planePolynomialEval P z * z.2 := by
          funext z
          simp [planePolynomialEval]
        have hg : polynomialGradient (P * MvPolynomial.X 1) p =
            planePolynomialEval P p • ContinuousLinearMap.snd ℂ ℂ ℂ +
              p.2 • polynomialGradient P p := by
          apply ContinuousLinearMap.ext
          intro z
          simp [polynomialGradient, planePolynomialEval]
          ring
        change HasFDerivAt (planePolynomialEval (P * MvPolynomial.X (1 : Fin 2))) (polynomialGradient (P * MvPolynomial.X (1 : Fin 2)) p) p
        rw [hf, hg]
        exact hP.mul ((ContinuousLinearMap.snd ℂ ℂ ℂ).hasFDerivAt (x := p))
theorem polynomialNormalCoordinates_hasFDerivAt
    (G : MvPolynomial (Fin 2) ℂ) (p : ComplexPlane) :
    HasFDerivAt (polynomialNormalCoordinates G)
      ((ContinuousLinearMap.fst ℂ ℂ ℂ).prod (polynomialGradient G p)) p :=
  ((ContinuousLinearMap.fst ℂ ℂ ℂ).hasFDerivAt).prodMk
    (planePolynomialEval_hasFDerivAt G p)
theorem polynomialNormalCoordinates_det
    (G : MvPolynomial (Fin 2) ℂ) (p : ComplexPlane) :
    (fderiv ℂ (polynomialNormalCoordinates G) p).det =
      planePolynomialEval (MvPolynomial.pderiv 1 G) p := by
  rw [(polynomialNormalCoordinates_hasFDerivAt G p).fderiv]
  change LinearMap.det
    (((ContinuousLinearMap.fst ℂ ℂ ℂ).prod (polynomialGradient G p)).toLinearMap) = _
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℂ)]
  rw [Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, polynomialGradient,
    Module.Basis.coe_finTwoProd_repr]
theorem exists_analytic_normal_chart_of_partial_ne_zero
    (G : MvPolynomial (Fin 2) ℂ) (p : ComplexPlane)
    (hpartial : planePolynomialEval (MvPolynomial.pderiv 1 G) p ≠ 0) :
    ∃ e : OpenPartialHomeomorph ComplexPlane ComplexPlane,
      (e : ComplexPlane → ComplexPlane) = polynomialNormalCoordinates G ∧
      p ∈ e.source ∧
      AnalyticAt ℂ e.symm (polynomialNormalCoordinates G p) := by
  apply exists_analytic_normal_chart G p
  rwa [polynomialNormalCoordinates_det]
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
theorem inverse_normal_chart_equation
    (G : MvPolynomial (Fin 2) ℂ)
    (e : OpenPartialHomeomorph ComplexPlane ComplexPlane)
    (he : (e : ComplexPlane → ComplexPlane) = polynomialNormalCoordinates G)
    (q : ComplexPlane) (hq : q ∈ e.target) : planePolynomialEval G (e.symm q) = q.2 := by
  have h := congrArg Prod.snd (e.right_inv hq)
  simpa only [he, polynomialNormalCoordinates] using h
theorem rescaled_inverse_normal_chart_equation
    (G : MvPolynomial (Fin 2) ℂ)
    (e : OpenPartialHomeomorph ComplexPlane ComplexPlane)
    (he : (e : ComplexPlane → ComplexPlane) = polynomialNormalCoordinates G)
    (s : ℂ) (q : ComplexPlane) (hq : analyticNormalScale s q ∈ e.target) :
    planePolynomialEval G (e.symm (analyticNormalScale s q)) = s * q.2 :=
  inverse_normal_chart_equation G e he (analyticNormalScale s q) hq
end Nagata.Workers.W28
end
end
end OAI
-- DividedFamilies
namespace OAI
section
noncomputable section
namespace Nagata.Workers.W28
open scoped BigOperators
def normalFamilyArgument (z : ℂ × ComplexPlane) : ComplexPlane := (z.2.1, z.1 * z.2.2)
def dividedAnalyticFamily (I : Finset ℕ) (j : ℕ → ℕ)
    (R : ℕ → MvPolynomial (Fin 2) ℂ) (u : ℕ) (κ : ComplexPlane → ComplexPlane)
    (z : ℂ × ComplexPlane) : ℂ :=
  ∑ α ∈ I, z.1 ^ (α + j α - u) * z.2.2 ^ j α *
    planePolynomialEval (R α) (κ (normalFamilyArgument z))
theorem normalFamilyArgument_analyticAt (z : ℂ × ComplexPlane) :
    AnalyticAt ℂ normalFamilyArgument z := by
  have hs := (ContinuousLinearMap.fst ℂ ℂ ComplexPlane).analyticAt z
  have hq := (ContinuousLinearMap.snd ℂ ℂ ComplexPlane).analyticAt z
  have hu := ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt z.2).comp hq
  have hw := ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt z.2).comp hq
  exact hu.prod (hs.mul hw)
theorem dividedAnalyticFamily_analyticAt
    (I : Finset ℕ) (j : ℕ → ℕ) (R : ℕ → MvPolynomial (Fin 2) ℂ)
    (u : ℕ) (κ : ComplexPlane → ComplexPlane) (z : ℂ × ComplexPlane)
    (hκ : AnalyticAt ℂ κ (normalFamilyArgument z)) :
    AnalyticAt ℂ (dividedAnalyticFamily I j R u κ) z := by
  have hs := (ContinuousLinearMap.fst ℂ ℂ ComplexPlane).analyticAt z
  have hq := (ContinuousLinearMap.snd ℂ ℂ ComplexPlane).analyticAt z
  have hw := ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt z.2).comp hq
  have hc := hκ.comp (normalFamilyArgument_analyticAt z)
  apply I.analyticAt_fun_sum
  intro α hα
  exact ((hs.pow (α + j α - u)).mul (hw.pow (j α))).mul
    ((planePolynomialEval_analyticAt (R α) (κ (normalFamilyArgument z))).comp (f := κ ∘ normalFamilyArgument) hc)
theorem originalFamily_eq_power_mul_divided
    (I : Finset ℕ) (j : ℕ → ℕ) (R : ℕ → MvPolynomial (Fin 2) ℂ)
    (u : ℕ) (hmin : ∀ α ∈ I, u ≤ α + j α)
    (G : MvPolynomial (Fin 2) ℂ) (κ : ComplexPlane → ComplexPlane)
    (z : ℂ × ComplexPlane)
    (hG : planePolynomialEval G (κ (normalFamilyArgument z)) = z.1 * z.2.2) :
    (∑ α ∈ I, z.1 ^ α * planePolynomialEval G (κ (normalFamilyArgument z)) ^ j α *
      planePolynomialEval (R α) (κ (normalFamilyArgument z))) =
      z.1 ^ u * dividedAnalyticFamily I j R u κ z := by
  classical
  unfold dividedAnalyticFamily
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α hα
  have hw : u + (α + j α - u) = α + j α := Nat.add_sub_of_le (hmin α hα)
  rw [hG, mul_pow]
  simp only [← mul_assoc, ← pow_add, hw]
theorem dividedAnalyticFamily_zero
    (I : Finset ℕ) (j : ℕ → ℕ) (R : ℕ → MvPolynomial (Fin 2) ℂ)
    (u : ℕ) (hmin : ∀ α ∈ I, u ≤ α + j α)
    (κ : ComplexPlane → ComplexPlane) (q : ComplexPlane) :
    dividedAnalyticFamily I j R u κ (0, q) =
      ∑ α ∈ I.filter (fun α => α + j α = u),
        q.2 ^ j α * planePolynomialEval (R α) (κ (q.1, 0)) := by
  classical
  unfold dividedAnalyticFamily
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro α hα
  by_cases heq : α + j α = u
  · simp [heq, normalFamilyArgument]
  · have hpos : 0 < α + j α - u := Nat.sub_pos_of_lt
      (lt_of_le_of_ne (hmin α hα) (Ne.symm heq))
    simp [heq, zero_pow (Nat.ne_of_gt hpos)]
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology
def dividedNormalCoordinate (G : ComplexPlane → ℂ) (L : ComplexPlane →L[ℂ] ℂ)
    (p V : ComplexPlane) : ℂ → ℂ :=
  Function.update (fun s : ℂ => s⁻¹ * G (p + s • V)) 0 (L V)
def dividedNormalCenter (G : ComplexPlane → ℂ) (L : ComplexPlane →L[ℂ] ℂ)
    (p V : ComplexPlane) (s : ℂ) : ComplexPlane :=
  ((p + s • V).1, dividedNormalCoordinate G L p V s)
theorem dividedNormalCenter_zero (G : ComplexPlane → ℂ)
    (L : ComplexPlane →L[ℂ] ℂ) (p V : ComplexPlane) :
    dividedNormalCenter G L p V 0 = (p.1, L V) := by
  simp [dividedNormalCenter, dividedNormalCoordinate]
theorem dividedNormalCenter_continuousAt
    (G : ComplexPlane → ℂ) (L : ComplexPlane →L[ℂ] ℂ) (p V : ComplexPlane)
    (hG : HasFDerivAt G L p) (hp : G p = 0) :
    ContinuousAt (dividedNormalCenter G L p V) 0 := by
  have hn : ContinuousAt (dividedNormalCoordinate G L p V) 0 :=
    continuousAt_update_same.mpr (normal_equation_affine_velocity_limit G L p V hG hp)
  exact ((continuous_const.add (continuous_id.smul continuous_const)).fst.continuousAt).prodMk hn
theorem scale_dividedNormalCenter
    (G : MvPolynomial (Fin 2) ℂ) (L : ComplexPlane →L[ℂ] ℂ)
    (p V : ComplexPlane) (s : ℂ) (hs : s ≠ 0) :
    analyticNormalScale s (dividedNormalCenter (planePolynomialEval G) L p V s) =
      polynomialNormalCoordinates G (p + s • V) := by
  ext <;> simp [analyticNormalScale, dividedNormalCenter, dividedNormalCoordinate,
    polynomialNormalCoordinates, hs]
theorem inverse_at_dividedNormalCenter
    (G : MvPolynomial (Fin 2) ℂ)
    (e : OpenPartialHomeomorph ComplexPlane ComplexPlane)
    (he : (e : ComplexPlane → ComplexPlane) = polynomialNormalCoordinates G)
    (L : ComplexPlane →L[ℂ] ℂ) (p V : ComplexPlane) (s : ℂ) (hs : s ≠ 0)
    (hsource : p + s • V ∈ e.source) :
    e.symm (analyticNormalScale s (dividedNormalCenter (planePolynomialEval G) L p V s)) =
      p + s • V := by
  rw [scale_dividedNormalCenter G L p V s hs, ← he]
  exact e.left_inv hsource
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology
theorem eventually_divided_center_chart_conditions
    (G : MvPolynomial (Fin 2) ℂ)
    (e : OpenPartialHomeomorph ComplexPlane ComplexPlane)
    (he : (e : ComplexPlane → ComplexPlane) = polynomialNormalCoordinates G)
    (L : ComplexPlane →L[ℂ] ℂ) (p V : ComplexPlane)
    (hp : p ∈ e.source) (hi : AnalyticAt ℂ e.symm (e p)) :
    ∀ᶠ s : ℂ in 𝓝 0, s ≠ 0 →
      p + s • V ∈ e.source ∧
      analyticNormalScale s (dividedNormalCenter (planePolynomialEval G) L p V s) ∈ e.target ∧
      AnalyticAt ℂ e.symm
        (analyticNormalScale s (dividedNormalCenter (planePolynomialEval G) L p V s)) := by
  have hm : ContinuousAt (fun s : ℂ => p + s • V) 0 :=
    (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
  have hs : ∀ᶠ s : ℂ in 𝓝 0, p + s • V ∈ e.source := by
    apply hm.preimage_mem_nhds
    simpa only [zero_smul, add_zero] using e.open_source.mem_nhds hp
  have hec : ContinuousAt e p := e.continuousAt hp
  have hm' : ContinuousAt (fun s : ℂ => e (p + s • V)) 0 := by
    have hh : ContinuousAt e (p + (0 : ℂ) • V) := by simpa using hec
    exact hh.comp (f := fun s : ℂ => p + s • V) hm
  have hinv : ∀ᶠ s : ℂ in 𝓝 0, AnalyticAt ℂ e.symm (e (p + s • V)) := by
    have hlocal : ∀ᶠ y in 𝓝 (e (p + (0 : ℂ) • V)), AnalyticAt ℂ e.symm y := by
      simpa only [zero_smul, add_zero] using hi.eventually_analyticAt
    exact hm'.tendsto.eventually hlocal
  filter_upwards [hs, hinv] with s hs hi hs0
  refine ⟨hs, ?_, ?_⟩
  · rw [scale_dividedNormalCenter G L p V s hs0, ← he]
    exact e.map_source hs
  · rwa [scale_dividedNormalCenter G L p V s hs0, ← he]
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators
def factoredPlaneFamily (I : Finset ℕ) (j : ℕ → ℕ)
    (R : ℕ → MvPolynomial (Fin 2) ℂ) (G : MvPolynomial (Fin 2) ℂ)
    (s : ℂ) : MvPolynomial (Fin 2) ℂ :=
  ∑ α ∈ I, MvPolynomial.C (s ^ α) * (G ^ j α * R α)
theorem eval_factoredPlaneFamily (I : Finset ℕ) (j : ℕ → ℕ)
    (R : ℕ → MvPolynomial (Fin 2) ℂ) (G : MvPolynomial (Fin 2) ℂ)
    (s : ℂ) (p : ComplexPlane) :
    planePolynomialEval (factoredPlaneFamily I j R G s) p =
      ∑ α ∈ I, s ^ α * planePolynomialEval G p ^ j α * planePolynomialEval (R α) p := by
  simp [factoredPlaneFamily, planePolynomialEval, mul_assoc]
theorem factored_family_order_implies_divided_order
    (I : Finset ℕ) (j : ℕ → ℕ) (R : ℕ → MvPolynomial (Fin 2) ℂ)
    (u : ℕ) (hmin : ∀ α ∈ I, u ≤ α + j α)
    (G : MvPolynomial (Fin 2) ℂ)
    (e : OpenPartialHomeomorph ComplexPlane ComplexPlane)
    (he : (e : ComplexPlane → ComplexPlane) = polynomialNormalCoordinates G)
    (s : ℂ) (hs : s ≠ 0) (q : ComplexPlane) (m : ℕ)
    (htarget : analyticNormalScale s q ∈ e.target)
    (hei : AnalyticAt ℂ e.symm (analyticNormalScale s q))
    (hP : Nagata.AffineMultiplicity.orderAtLeast
      (fun i : Fin 2 => if i = 0 then (e.symm (analyticNormalScale s q)).1
        else (e.symm (analyticNormalScale s q)).2)
      m (factoredPlaneFamily I j R G s)) :
    HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun x => dividedAnalyticFamily I j R u e.symm (s, x)) q m := by
  have h := polynomial_order_in_rescaled_inverse_chart
    (factoredPlaneFamily I j R G s) e s q m hei hP
  apply (Nagata.Workers.W17.analytic_order_const_mul_iff
    (fun x => dividedAnalyticFamily I j R u e.symm (s, x)) q m
    (s ^ u) (pow_ne_zero _ hs)).mp
  apply h.congr
  have ht : ∀ᶠ x in 𝓝 q, analyticNormalScale s x ∈ e.target :=
    (analyticNormalScale_analyticAt s q).continuousAt.preimage_mem_nhds
      (e.open_target.mem_nhds htarget)
  exact ht.mono fun x hx => by
    change planePolynomialEval (factoredPlaneFamily I j R G s)
      (e.symm (analyticNormalScale s x)) = _
    rw [eval_factoredPlaneFamily]
    apply originalFamily_eq_power_mul_divided I j R u hmin G e.symm (s, x)
    exact rescaled_inverse_normal_chart_equation G e he s x hx
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators
theorem normal_specialization_central_jets
    (I : Finset ℕ) (j : ℕ → ℕ) (R : ℕ → MvPolynomial (Fin 2) ℂ)
    (u : ℕ) (hmin : ∀ α ∈ I, u ≤ α + j α)
    (G : MvPolynomial (Fin 2) ℂ)
    (e : OpenPartialHomeomorph ComplexPlane ComplexPlane)
    (he : (e : ComplexPlane → ComplexPlane) = polynomialNormalCoordinates G)
    (L : ComplexPlane →L[ℂ] ℂ) (p V : ComplexPlane)
    (hsource : p ∈ e.source) (hi : AnalyticAt ℂ e.symm (e p))
    (hG : HasFDerivAt (planePolynomialEval G) L p)
    (hp : planePolynomialEval G p = 0)
    (exceptional : Finset ℂ) (m : ℕ)
    (horders : ∀ᶠ s : ℂ in 𝓝 0, s ∉ exceptional →
      Nagata.AffineMultiplicity.orderAtLeast
        (fun i : Fin 2 => if i = 0 then (p + s • V).1 else (p + s • V).2)
        m (factoredPlaneFamily I j R G s)) :
    ∀ n < m, iteratedFDeriv ℂ n
      (fun q : ComplexPlane =>
        ∑ α ∈ I.filter (fun α => α + j α = u),
          q.2 ^ j α * planePolynomialEval (R α) (e.symm (q.1, 0)))
      (p.1, L V) = 0 := by
  classical
  let center := dividedNormalCenter (planePolynomialEval G) L p V
  let family : ℂ → ComplexPlane → ℂ := fun s q => dividedAnalyticFamily I j R u e.symm (s, q)
  have hc : ContinuousAt center 0 := dividedNormalCenter_continuousAt _ L p V hG hp
  have hc0 : center 0 = (p.1, L V) := dividedNormalCenter_zero _ L p V
  have harg : normalFamilyArgument (0, center 0) = e p := by
    rw [hc0, he]
    simp [normalFamilyArgument, polynomialNormalCoordinates, hp]
  have hf : AnalyticAt ℂ (Function.uncurry family) (0, center 0) := by
    apply dividedAnalyticFamily_analyticAt
    rwa [harg]
  have hchart := eventually_divided_center_chart_conditions G e he L p V hsource hi
  have hjets : ∀ᶠ s : ℂ in 𝓝 0, s ∉ insert 0 exceptional → ∀ n < m,
      iteratedFDeriv ℂ n (family s) (center s) = 0 := by
    filter_upwards [hchart, horders] with s hs ho hex
    have hs0 : s ≠ 0 := fun hz => hex (hz ▸ Finset.mem_insert_self _ _)
    have hexc : s ∉ exceptional := fun h => hex (Finset.mem_insert_of_mem h)
    obtain ⟨hsour, htar, hainv⟩ := hs hs0
    have hpoint := inverse_at_dividedNormalCenter G e he L p V s hs0 hsour
    have hord : Nagata.AffineMultiplicity.orderAtLeast
        (fun i : Fin 2 => if i = 0 then (e.symm (analyticNormalScale s (center s))).1
          else (e.symm (analyticNormalScale s (center s))).2)
        m (factoredPlaneFamily I j R G s) := by
      simpa only [center, hpoint] using ho hexc
    obtain ⟨P, hP, hz⟩ := factored_family_order_implies_divided_order
      I j R u hmin G e he s hs0 (center s) m htar hainv hord
    exact Nagata.W19.total_taylor_vanishing_of_powerSeries hP m hz
  have hlim := Nagata.Workers.W17.analytic_local_cofinite_moving_derivative_jets
    family center 0 (insert 0 exceptional) m hf hc hjets
  intro n hn
  have hh := hlim n hn
  simp only [family, hc0] at hh
  simpa only [dividedAnalyticFamily_zero I j R u hmin] using hh
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators
theorem inverse_normal_chart_eq_graph_locally
    (G : MvPolynomial (Fin 2) ℂ)
    (e : OpenPartialHomeomorph ComplexPlane ComplexPlane)
    (he : (e : ComplexPlane → ComplexPlane) = polynomialNormalCoordinates G)
    (b : ℂ → ℂ) (ξ : ℂ) (hb : ContinuousAt b ξ)
    (hsource : (ξ, b ξ) ∈ e.source)
    (hG : ∀ᶠ z in 𝓝 ξ, planePolynomialEval G (z, b z) = 0) :
    ∀ᶠ z in 𝓝 ξ, e.symm (z, 0) = (z, b z) := by
  have hc : ContinuousAt (fun z => (z, b z)) ξ := continuousAt_id.prodMk hb
  have hs : ∀ᶠ z in 𝓝 ξ, (z, b z) ∈ e.source :=
    hc.preimage_mem_nhds (e.open_source.mem_nhds hsource)
  filter_upwards [hs, hG] with z hz hg
  have hh := e.left_inv hz
  simpa only [he, polynomialNormalCoordinates, hg] using hh
theorem central_expression_eq_graph_locally
    (I : Finset ℕ) (j : ℕ → ℕ) (R : ℕ → MvPolynomial (Fin 2) ℂ) (u : ℕ)
    (G : MvPolynomial (Fin 2) ℂ)
    (e : OpenPartialHomeomorph ComplexPlane ComplexPlane)
    (he : (e : ComplexPlane → ComplexPlane) = polynomialNormalCoordinates G)
    (b : ℂ → ℂ) (ξ c : ℂ) (hb : ContinuousAt b ξ)
    (hsource : (ξ, b ξ) ∈ e.source)
    (hG : ∀ᶠ z in 𝓝 ξ, planePolynomialEval G (z, b z) = 0) :
    (fun q : ComplexPlane => ∑ α ∈ I.filter (fun α => α + j α = u),
      q.2 ^ j α * planePolynomialEval (R α) (e.symm (q.1, 0))) =ᶠ[𝓝 (ξ, c)]
    (fun q : ComplexPlane => ∑ α ∈ I.filter (fun α => α + j α = u),
      q.2 ^ j α * planePolynomialEval (R α) (q.1, b q.1)) := by
  have hgraph := inverse_normal_chart_eq_graph_locally G e he b ξ hb hsource hG
  have hc : ContinuousAt (Prod.fst : ComplexPlane → ℂ) (ξ, c) := continuousAt_fst
  have hh := hc.tendsto.eventually hgraph
  exact hh.mono fun q hq => by simp only [hq]
end Nagata.Workers.W28
end
end
end OAI
-- CoefficientIdeals
namespace OAI
section
open Polynomial
open scoped BigOperators
namespace Nagata.W18
theorem coefficient_dvd_of_coordinate_ideal_power {R : Type*} [CommRing R]
    (g : R) (m : ℕ) (H : Polynomial R)
    (hH : H ∈ (Ideal.span ({C g, X} : Set (Polynomial R))) ^ m) :
    ∀ J : ℕ, g ^ (m - J) ∣ H.coeff J := by
  classical
  rw [Nagata.Workers.W30.pair_ideal_pow] at hH
  induction hH using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨k, hk, rfl⟩ := hz
    intro J
    rw [← C_pow, coeff_C_mul_X_pow]
    by_cases hJ : J = k
    · subst J
      simp
    · simp [hJ]
  | zero => intro J; simp
  | add p q hp hq ihp ihq =>
    intro J
    rw [coeff_add]
    exact dvd_add (ihp J) (ihq J)
  | smul p q hq ih =>
    intro J
    change g ^ (m - J) ∣ (p * q).coeff J
    rw [coeff_mul]
    apply Finset.dvd_sum
    intro ij hij
    have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    have hle : m - J ≤ m - ij.2 := by omega
    exact dvd_mul_of_dvd_right ((pow_dvd_pow g hle).trans (ih ij.2)) _
end Nagata.W18
end
section
noncomputable section
open Polynomial
open scoped BigOperators
namespace Nagata.W18
def nestedPointIdeal {K : Type*} [CommRing K] (a c : K) :
    Ideal (Polynomial (Polynomial K)) :=
  Ideal.span {C (X - C a), X - C (C c)}
theorem map_nestedPointIdeal_taylor {K : Type*} [CommRing K] (a c : K) :
    (nestedPointIdeal a c).map (taylorAlgHom (C c)).toRingHom =
      Ideal.span ({C (X - C a), X} : Set (Polynomial (Polynomial K))) := by
  rw [nestedPointIdeal, Ideal.map_span]
  simp only [Set.image_insert_eq, Set.image_singleton]
  change Ideal.span {taylor (C c) (C (X - C a)), taylor (C c) (X - C (C c))} = _
  simp only [taylor_C, map_sub, taylor_X, add_sub_cancel_right]
theorem top_coefficient_taylor {R : Type*} [CommRing R]
    (H : Polynomial R) (r : R) (J : ℕ) (hJ : H.natDegree ≤ J) :
    (taylor r H).coeff J = H.coeff J := by
  by_cases heq : H.natDegree = J
  · rw [← heq, coeff_taylor_natDegree]
    rfl
  · have hlt : H.natDegree < J := lt_of_le_of_ne hJ heq
    rw [coeff_eq_zero_of_natDegree_lt hlt,
      coeff_eq_zero_of_natDegree_lt (by simpa only [natDegree_taylor] using hlt)]
theorem top_coefficient_base_divisibility {K : Type*} [CommRing K]
    (H : Polynomial (Polynomial K)) (a c : K) (m J : ℕ)
    (hJ : H.natDegree ≤ J) (hH : H ∈ (nestedPointIdeal a c) ^ m) :
    (X - C a) ^ (m - J) ∣ H.coeff J := by
  have h := Ideal.mem_map_of_mem (taylorAlgHom (C c)).toRingHom hH
  rw [Ideal.map_pow, map_nestedPointIdeal_taylor] at h
  have hd := coefficient_dvd_of_coordinate_ideal_power (X - C a) m
    (taylor (C c) H) h J
  rwa [top_coefficient_taylor H (C c) J hJ] at hd
def fiberRestriction {K : Type*} [CommRing K] (a : K) :
    Polynomial (Polynomial K) →+* Polynomial K :=
  mapRingHom (evalRingHom a)
theorem fiberRestriction_coeff {K : Type*} [CommRing K]
    (H : Polynomial (Polynomial K)) (a : K) (j : ℕ) :
    (fiberRestriction a H).coeff j = (H.coeff j).eval a :=
  Polynomial.coeff_map (evalRingHom a) j
theorem fiberRestriction_natDegree_le {K : Type*} [CommRing K]
    (H : Polynomial (Polynomial K)) (a : K) :
    (fiberRestriction a H).natDegree ≤ H.natDegree :=
  Polynomial.natDegree_map_le
theorem fiberRestriction_leadingCoeff {K : Type*} [CommRing K]
    (H : Polynomial (Polynomial K)) (a : K) (J : ℕ)
    (hJ : H.natDegree ≤ J) (hne : (H.coeff J).eval a ≠ 0) :
    (fiberRestriction a H).leadingCoeff = (H.coeff J).eval a := by
  have hdeg : (fiberRestriction a H).natDegree = J :=
    natDegree_eq_of_le_of_coeff_ne_zero ((fiberRestriction_natDegree_le H a).trans hJ)
      (by rwa [fiberRestriction_coeff])
  rw [leadingCoeff, hdeg, fiberRestriction_coeff]
theorem map_nestedPointIdeal_fiber {K : Type*} [CommRing K] (a c : K) :
    (nestedPointIdeal a c).map (fiberRestriction a) =
      Ideal.span ({X - C c} : Set (Polynomial K)) := by
  rw [nestedPointIdeal, Ideal.map_span]
  simp [fiberRestriction, Set.image_insert_eq, Set.image_singleton,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_sub, eval_X, eval_C]
theorem fiber_power_divides_of_surface_order {K : Type*} [CommRing K]
    (H : Polynomial (Polynomial K)) (a c : K) (m : ℕ)
    (hH : H ∈ (nestedPointIdeal a c) ^ m) :
    (X - C c) ^ m ∣ fiberRestriction a H := by
  have h := Ideal.mem_map_of_mem (fiberRestriction a) hH
  rw [Ideal.map_pow, map_nestedPointIdeal_fiber, Ideal.span_singleton_pow] at h
  exact Ideal.mem_span_singleton.mp h
end Nagata.W18
end
end
end OAI
-- RationalKernels
namespace OAI
section
namespace Nagata.W18
open scoped BigOperators
theorem exponent_injective_on_diagonal (s : Finset ℕ) (j : ℕ → ℕ) (u : ℕ)
    (hweight : ∀ a ∈ s, a + j a = u) :
    Set.InjOn j (↑s : Set ℕ) := by
  intro a ha b hb hab
  apply @Nat.add_right_cancel a (j a) b
  calc
    a + j a = u := hweight a ha
    _ = b + j b := (hweight b hb).symm
    _ = b + j a := congrArg (fun n => b + n) hab.symm
theorem coefficient_of_injective_monomial_sum {R : Type*} [Semiring R]
    (s : Finset ℕ) (j : ℕ → ℕ) (c : ℕ → R)
    (hinj : Set.InjOn j (↑s : Set ℕ)) (a : ℕ) (ha : a ∈ s) :
    (∑ b ∈ s, Polynomial.monomial (j b) (c b)).coeff (j a) = c a := by
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single a]
  · exact Polynomial.coeff_monomial_same _ _
  · intro b hb hba
    apply Polynomial.coeff_monomial_of_ne
    intro hab
    exact hba (hinj hb ha hab.symm)
  · intro h
    exact (h ha).elim
theorem injective_monomial_sum_ne_zero {R : Type*} [Semiring R]
    (s : Finset ℕ) (j : ℕ → ℕ) (c : ℕ → R)
    (hinj : Set.InjOn j (↑s : Set ℕ))
    (hcoeff : ∃ a ∈ s, c a ≠ 0) :
    (∑ b ∈ s, Polynomial.monomial (j b) (c b)) ≠ 0 := by
  obtain ⟨a, ha, hca⟩ := hcoeff
  intro hz
  apply hca
  calc
    c a = (∑ b ∈ s, Polynomial.monomial (j b) (c b)).coeff (j a) :=
      (coefficient_of_injective_monomial_sum s j c hinj a ha).symm
    _ = 0 := by rw [hz, Polynomial.coeff_zero]
theorem diagonal_monomial_sum_ne_zero {R : Type*} [Semiring R]
    (s : Finset ℕ) (j : ℕ → ℕ) (c : ℕ → R) (u : ℕ)
    (hweight : ∀ a ∈ s, a + j a = u)
    (hne : s.Nonempty) (hcoeff : ∀ a ∈ s, c a ≠ 0) :
    (∑ b ∈ s, Polynomial.monomial (j b) (c b)) ≠ 0 := by
  obtain ⟨a, ha⟩ := hne
  exact injective_monomial_sum_ne_zero s j c
    (exponent_injective_on_diagonal s j u hweight) ⟨a, ha, hcoeff a ha⟩
theorem exists_lowest_weight_polynomial {R : Type*} [Semiring R]
    (s : Finset ℕ) (j : ℕ → ℕ) (c : ℕ → R)
    (hne : s.Nonempty) (hcoeff : ∀ a ∈ s, c a ≠ 0) :
    ∃ u : ℕ,
      (∀ a ∈ s, u ≤ a + j a) ∧
      (s.filter (fun a => a + j a = u)).Nonempty ∧
      (∑ b ∈ s.filter (fun a => a + j a = u),
        Polynomial.monomial (j b) (c b)) ≠ 0 := by
  obtain ⟨a, ha, hmin⟩ := s.exists_min_image (fun b => b + j b) hne
  let u := a + j a
  have hselected : (s.filter (fun b => b + j b = u)).Nonempty :=
    ⟨a, Finset.mem_filter.mpr ⟨ha, rfl⟩⟩
  refine ⟨u, hmin, hselected, ?_⟩
  apply diagonal_monomial_sum_ne_zero _ j c u
  · intro b hb
    exact (Finset.mem_filter.mp hb).2
  · exact hselected
  · intro b hb
    exact hcoeff b (Finset.mem_filter.mp hb).1
end Nagata.W18
end
section
noncomputable section
namespace Nagata.W18
theorem normalize_parameter_vector {K ι : Type*} [Field K]
    (p : ι → Polynomial K) (hp : p ≠ 0) :
    ∃ n : ℕ, ∃ q : ι → Polynomial K,
      (∀ i, p i = Polynomial.X ^ n * q i) ∧
      ∃ i, (q i).coeff 0 ≠ 0 := by
  classical
  have hex : ∃ n : ℕ, ∃ i, (p i).coeff n ≠ 0 := by
    by_contra h
    apply hp
    funext i
    apply Polynomial.ext
    intro n
    have hn : (p i).coeff n = 0 := by
      by_contra hn
      exact h ⟨n, i, hn⟩
    simpa only [Pi.zero_apply, Polynomial.coeff_zero] using hn
  let n := Nat.find hex
  have hsmall : ∀ k < n, ∀ i, (p i).coeff k = 0 := by
    intro k hk i
    by_contra hki
    exact (Nat.find_min hex hk) ⟨i, hki⟩
  have hdiv : ∀ i, Polynomial.X ^ n ∣ p i := by
    intro i
    exact Polynomial.X_pow_dvd_iff.mpr (fun k hk => hsmall k hk i)
  choose q hq using hdiv
  refine ⟨n, q, hq, ?_⟩
  obtain ⟨i, hi⟩ := Nat.find_spec hex
  refine ⟨i, ?_⟩
  intro hzero
  obtain ⟨r, hr⟩ := Polynomial.X_dvd_iff.mpr hzero
  have hdivsucc : Polynomial.X ^ (n + 1) ∣ p i := by
    refine ⟨r, ?_⟩
    rw [hq i, hr, pow_succ, mul_assoc]
  exact hi (Polynomial.X_pow_dvd_iff.mp hdivsucc n (Nat.lt_succ_self n))
theorem normalize_parameter_kernel {K ι κ : Type*} [Field K] [Fintype ι]
    (A : Matrix κ ι (Polynomial K)) (p : ι → Polynomial K)
    (hp : p ≠ 0) (hAp : A.mulVec p = 0) :
    ∃ n : ℕ, ∃ q : ι → Polynomial K,
      (∀ i, p i = Polynomial.X ^ n * q i) ∧
      (∃ i, (q i).coeff 0 ≠ 0) ∧ A.mulVec q = 0 := by
  obtain ⟨n, q, hq, hqzero⟩ := normalize_parameter_vector p hp
  refine ⟨n, q, hq, hqzero, ?_⟩
  have hpeq : p = (Polynomial.X : Polynomial K) ^ n • q := by
    funext i
    exact hq i
  rw [hpeq, Matrix.mulVec_smul] at hAp
  funext k
  exact (mul_eq_zero.mp (congrFun hAp k)).resolve_left
    (pow_ne_zero n Polynomial.X_ne_zero)
end Nagata.W18
end
end
section
noncomputable section
open scoped BigOperators
namespace Nagata.W18
theorem clear_finite_denominators {R : Type*} [CommRing R] [IsDomain R]
    {ι : Type*} [Finite ι] (v : ι → FractionRing R) :
    ∃ d : R, d ≠ 0 ∧ ∃ p : ι → R,
      ∀ i, algebraMap R (FractionRing R) (p i) =
        algebraMap R (FractionRing R) d * v i := by
  classical
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors R) v
  choose p hp using hd
  refine ⟨d, nonZeroDivisors.coe_ne_zero d, p, ?_⟩
  intro i
  simpa only [Algebra.smul_def] using hp i
theorem map_scalar_identity {R K : Type*} [CommRing R] [CommRing K]
    {ι : Type*} [DecidableEq ι] (f : R →+* K) (d : R) :
    (d • (1 : Matrix ι ι R)).map f = f d • (1 : Matrix ι ι K) := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.map_apply, h, smul_eq_mul]
theorem polynomial_scaled_left_inverse {R : Type*} [CommRing R] [IsDomain R]
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix κ ι R)
    (hinj : Function.Injective (A.map (algebraMap R (FractionRing R))).mulVec) :
    ∃ d : R, d ≠ 0 ∧ ∃ D : Matrix ι κ R, D * A = d • (1 : Matrix ι ι R) := by
  classical
  let f := algebraMap R (FractionRing R)
  obtain ⟨g, hg⟩ := (Matrix.toLin' (A.map f)).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hinj)
  let C := LinearMap.toMatrix' g
  have hC : C * A.map f = 1 := by
    simpa only [C, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
      LinearMap.toMatrix'_id] using congrArg LinearMap.toMatrix' hg
  obtain ⟨d, hd, p, hp⟩ := clear_finite_denominators (fun z : ι × κ => C z.1 z.2)
  let D : Matrix ι κ R := fun i k => p (i, k)
  have hD : D.map f = f d • C := by
    ext i k
    exact hp (i, k)
  refine ⟨d, hd, D, ?_⟩
  apply Matrix.map_injective (IsFractionRing.injective R (FractionRing R))
  change (D * A).map f = (d • (1 : Matrix ι ι R)).map f
  rw [Matrix.map_mul, hD, Matrix.smul_mul, hC, map_scalar_identity]
theorem clear_fraction_kernel {R : Type*} [CommRing R] [IsDomain R]
    {ι κ : Type*} [Fintype ι] (A : Matrix κ ι R)
    (v : ι → FractionRing R) (hv : v ≠ 0)
    (hAv : (A.map (algebraMap R (FractionRing R))).mulVec v = 0) :
    ∃ p : ι → R, p ≠ 0 ∧ A.mulVec p = 0 := by
  classical
  let f := algebraMap R (FractionRing R)
  obtain ⟨d, hd, p, hp⟩ := clear_finite_denominators v
  have hfd : f d ≠ 0 := by
    intro hz
    exact hd (IsFractionRing.injective R (FractionRing R) (by simpa [f] using hz))
  have hmap : f ∘ p = f d • v := by
    funext i
    exact hp i
  refine ⟨p, ?_, ?_⟩
  · intro hpzero
    apply hv
    funext i
    have hi : f d * v i = 0 := by
      rw [← hp i, hpzero]
      exact map_zero f
    exact (mul_eq_zero.mp hi).resolve_left hfd
  · funext k
    apply IsFractionRing.injective R (FractionRing R)
    change f ((A.mulVec p) k) = f 0
    rw [RingHom.map_mulVec, hmap, Matrix.mulVec_smul, hAv]
    simp
theorem specialize_polynomial_kernel {K ι κ : Type*} [Field K] [Fintype ι]
    (A : Matrix κ ι (Polynomial K)) (p : ι → Polynomial K)
    (hp : A.mulVec p = 0) (s : K) :
    (A.map (Polynomial.evalRingHom s)).mulVec (fun i => (p i).eval s) = 0 := by
  funext k
  have h := RingHom.map_mulVec (Polynomial.evalRingHom s) A p k
  rw [hp] at h
  simpa only [Pi.zero_apply, map_zero, Polynomial.coe_evalRingHom,
    Function.comp_def] using h.symm
theorem exists_parameter_avoiding_roots {K : Type*} [Field K] [Infinite K]
    (E : Finset K) (d : Polynomial K) (hd : d ≠ 0) :
    ∃ s : K, s ∉ E ∧ d.eval s ≠ 0 := by
  obtain ⟨s, hs⟩ := (E.finite_toSet.union (Polynomial.finite_setOfPred_isRoot hd)).exists_notMem
  exact ⟨s, fun h => hs (Or.inl h), fun h => hs (Or.inr h)⟩
theorem rational_kernel_of_general_specialized_kernel
    {K : Type*} [Field K] [Infinite K]
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix κ ι (Polynomial K)) (E : Finset K)
    (hkernel : ∀ s ∉ E, ∃ v : ι → K, v ≠ 0 ∧
      (A.map (Polynomial.evalRingHom s)).mulVec v = 0) :
    ∃ v : ι → FractionRing (Polynomial K), v ≠ 0 ∧
      (A.map (algebraMap (Polynomial K) (FractionRing (Polynomial K)))).mulVec v = 0 := by
  classical
  by_contra hnone
  have hinj : Function.Injective
      (A.map (algebraMap (Polynomial K) (FractionRing (Polynomial K)))).mulVec := by
    have hker : LinearMap.ker
        (Matrix.mulVecLin (A.map (algebraMap (Polynomial K)
          (FractionRing (Polynomial K))))) = ⊥ := by
      apply Matrix.ker_mulVecLin_eq_bot_iff.mpr
      intro v hv
      by_contra hne
      exact hnone ⟨v, hne, hv⟩
    exact LinearMap.ker_eq_bot.mp hker
  obtain ⟨d, hd, D, hDA⟩ := polynomial_scaled_left_inverse A hinj
  obtain ⟨s, hsE, hds⟩ := exists_parameter_avoiding_roots E d hd
  obtain ⟨v, hv, hAv⟩ := hkernel s hsE
  let ev := Polynomial.evalRingHom s
  have hDAeval : D.map ev * A.map ev = d.eval s • (1 : Matrix ι ι K) := by
    have h := congrArg (fun M : Matrix ι ι (Polynomial K) => M.map ev) hDA
    change (D * A).map ev = (d • (1 : Matrix ι ι (Polynomial K))).map ev at h
    rw [Matrix.map_mul (f := ev), map_scalar_identity] at h
    exact h
  have hscalar : d.eval s • v = 0 := by
    calc
      d.eval s • v = (d.eval s • (1 : Matrix ι ι K)).mulVec v := by
        rw [Matrix.smul_mulVec, Matrix.one_mulVec]
      _ = (D.map ev * A.map ev).mulVec v := by rw [hDAeval]
      _ = (D.map ev).mulVec ((A.map ev).mulVec v) :=
        (Matrix.mulVec_mulVec _ _ _).symm
      _ = 0 := by rw [hAv, Matrix.mulVec_zero]
  apply hv
  funext i
  exact (mul_eq_zero.mp (congrFun hscalar i)).resolve_left hds
theorem polynomial_kernel_of_general_specialized_kernel
    {K : Type*} [Field K] [Infinite K]
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix κ ι (Polynomial K)) (E : Finset K)
    (hkernel : ∀ s ∉ E, ∃ v : ι → K, v ≠ 0 ∧
      (A.map (Polynomial.evalRingHom s)).mulVec v = 0) :
    ∃ p : ι → Polynomial K, p ≠ 0 ∧ A.mulVec p = 0 := by
  obtain ⟨v, hv, hAv⟩ := rational_kernel_of_general_specialized_kernel A E hkernel
  exact clear_fraction_kernel A v hv hAv
end Nagata.W18
end
end
section
namespace Nagata.W18
theorem normalized_kernel_of_general_specialized_kernel
    {K : Type*} [Field K] [Infinite K]
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix κ ι (Polynomial K)) (E : Finset K)
    (hkernel : ∀ s ∉ E, ∃ v : ι → K, v ≠ 0 ∧
      (A.map (Polynomial.evalRingHom s)).mulVec v = 0) :
    ∃ q : ι → Polynomial K, (∃ i, (q i).coeff 0 ≠ 0) ∧ A.mulVec q = 0 := by
  obtain ⟨p, hp, hAp⟩ := polynomial_kernel_of_general_specialized_kernel A E hkernel
  obtain ⟨n, q, _, hqzero, hAq⟩ := normalize_parameter_kernel A p hp hAp
  exact ⟨q, hqzero, hAq⟩
end Nagata.W18
end
end OAI
-- SquareLinear
namespace OAI
section
namespace Nagata.Workers.W24
theorem ambientDegreeK_dimension_lt (k : ℕ) (hk : 4 ≤ k) :
    (k + 2).choose 2 < k * k := by
  have hmul : 4 * k ≤ k * k := Nat.mul_le_mul_right k hk
  have hquad : 3 * k + 2 < k * k := by omega
  have hnum : (k + 2) * (k + 1) < 2 * (k * k) := by
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one]
    omega
  rw [Nat.choose_two_right]
  have hsub : k + 2 - 1 = k + 1 := by omega
  rw [hsub]
  omega
end Nagata.Workers.W24
end
section
namespace Nagata.Workers.W24
theorem nonzero_smul_outside_range {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) (c : W) (hc : c ∉ f.range) (a : K) (ha : a ≠ 0) :
    a • c ∉ f.range := by
  intro h
  exact hc ((f.range.smul_mem_iff ha).mp h)
theorem evaluation_coefficient_contradiction {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) (c : W) (hc : c ∉ f.range) (a : K) (ha : a ≠ 0)
    (s : V) (heq : f s = a • c) : False := by
  apply nonzero_smul_outside_range f c hc a ha
  exact ⟨s, heq⟩
end Nagata.Workers.W24
end
section
noncomputable section
namespace Nagata.Workers.W24
open Polynomial
def normalResiduePolynomial {A : Type*} [CommRing A] (G : A) (F : A[X]) :
    Polynomial (A ⧸ Ideal.span ({G} : Set A)) :=
  F.map (Ideal.Quotient.mk (Ideal.span ({G} : Set A)))
theorem above_normalResidue_degree_dvd {A : Type*} [CommRing A]
    (G : A) (F : A[X]) (j : ℕ) (hj : (normalResiduePolynomial G F).natDegree < j) :
    G ∣ F.coeff j := by
  have hz := Polynomial.coeff_eq_zero_of_natDegree_lt hj
  rw [normalResiduePolynomial, Polynomial.coeff_map] at hz
  exact (Ideal.Quotient.eq_zero_iff_dvd G (F.coeff j)).mp hz
theorem top_normalResidue_coefficient_not_dvd {A : Type*} [CommRing A]
    (G : A) (F : A[X]) (hne : normalResiduePolynomial G F ≠ 0) :
    ¬ G ∣ F.coeff (normalResiduePolynomial G F).natDegree := by
  intro hdiv
  have hz := (Ideal.Quotient.eq_zero_iff_dvd G _).mpr hdiv
  have hcoeff : (normalResiduePolynomial G F).coeff
      (normalResiduePolynomial G F).natDegree = 0 := by
    simpa only [normalResiduePolynomial, Polynomial.coeff_map] using hz
  exact (Polynomial.leadingCoeff_ne_zero.mpr hne) hcoeff
theorem restriction_natDegree_le_normalResidue_degree {A B : Type*}
    [CommRing A] [CommRing B] (G : A) (F : A[X]) (f : A →+* B) (hG : f G = 0) :
    (F.map f).natDegree ≤ (normalResiduePolynomial G F).natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  obtain ⟨q, hq⟩ := above_normalResidue_degree_dvd G F j hj
  rw [Polynomial.coeff_map, hq, map_mul, hG, zero_mul]
end Nagata.Workers.W24
end
end
section
namespace Nagata.Workers.W24
theorem leadingIndex_le_m (k d m j : Nat) (hk : 0 < k)
    (hdj : k * j ≤ d) (hd : d ≤ k * m) : j ≤ m := by
  apply Nat.le_of_not_gt
  intro hmj
  have hmul := Nat.mul_lt_mul_of_pos_left hmj hk
  omega
theorem penultimate_exponent (k m : Nat) (hm : 0 < m) :
    k * m - k * (m - 1) = k := by
  have hm' : m = (m - 1) + 1 := by omega
  calc
    k * m - k * (m - 1) = k * ((m - 1) + 1) - k * (m - 1) := by rw [← hm']
    _ = k := by simp [Nat.mul_add]
end Nagata.Workers.W24
end
section
namespace Nagata.Workers.W24
open Polynomial
theorem polynomial_eq_leadingCoeff_mul_power {R : Type*} [CommRing R] [Nontrivial R]
    (p : R[X]) (c : R) (m : Nat) (hd : p.natDegree ≤ m)
    (hmult : (X - C c) ^ m ∣ p) :
    p = C p.leadingCoeff * (X - C c) ^ m := by
  apply eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
    ((monic_X_sub_C c).pow m) hmult
  simpa only [(monic_X_sub_C c).natDegree_pow, natDegree_X_sub_C, mul_one] using hd
theorem power_penultimate_coefficient {R : Type*} [CommRing R] [Nontrivial R]
    (c : R) (m : Nat) (hm : 0 < m) :
    ((X - C c) ^ m).coeff (m - 1) = -((m : R) * c) := by
  have hdeg : ((X - C c) ^ m).natDegree = m := by
    rw [(monic_X_sub_C c).natDegree_pow, natDegree_X_sub_C, mul_one]
  have hnext := (monic_X_sub_C c).nextCoeff_pow m
  rw [nextCoeff_of_natDegree_pos (by rw [hdeg]; exact hm), hdeg,
    nextCoeff_X_sub_C] at hnext
  simpa only [nsmul_eq_mul, mul_neg] using hnext
theorem polynomial_penultimate_coefficient {R : Type*} [CommRing R] [Nontrivial R]
    (p : R[X]) (c : R) (m : Nat) (hm : 0 < m) (hd : p.natDegree ≤ m)
    (hmult : (X - C c) ^ m ∣ p) :
    p.coeff (m - 1) = p.leadingCoeff * (-((m : R) * c)) := by
  have heq := polynomial_eq_leadingCoeff_mul_power p c m hd hmult
  have hcoeff := congrArg (fun q : R[X] => q.coeff (m - 1)) heq
  simpa only [coeff_C_mul, power_penultimate_coefficient c m hm] using hcoeff
theorem polynomial_penultimate_coefficient_scalar {R : Type*} [CommRing R] [Nontrivial R]
    (p : R[X]) (c : R) (m : Nat) (hm : 0 < m) (hd : p.natDegree ≤ m)
    (hmult : (X - C c) ^ m ∣ p) :
    p.coeff (m - 1) = (-(m : R) * p.leadingCoeff) * c := by
  rw [polynomial_penultimate_coefficient p c m hm hd hmult]
  simp only [mul_neg, neg_mul, mul_assoc]
  rw [mul_left_comm]
end Nagata.Workers.W24
end
section
noncomputable section
namespace Nagata.Workers.W24
open MvPolynomial
abbrev PlaneForms (n : Nat) := MvPolynomial.homogeneousSubmodule (Fin 3) ℂ n
def homogeneousEvaluation {ι : Type*} (n : Nat) (a : ι → Fin 3 → ℂ) :
    PlaneForms n →ₗ[ℂ] (ι → ℂ) :=
  LinearMap.pi fun i => ((MvPolynomial.aeval (a i)).toLinearMap).comp
    (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ n).subtype
@[simp] theorem homogeneousEvaluation_apply {ι : Type*} (n : Nat)
    (a : ι → Fin 3 → ℂ) (F : PlaneForms n) (i : ι) :
    homogeneousEvaluation n a F i = MvPolynomial.eval (a i) F.val := rfl
theorem degreeZeroForm_eq_constant (F : PlaneForms 0) :
    F.val = MvPolynomial.C (F.val.coeff 0) := by
  apply MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
  exact (MvPolynomial.totalDegree_zero_iff_isHomogeneous _).mpr F.property
end Nagata.Workers.W24
end
end
section
namespace Nagata.Workers.W24
open Module
theorem exists_vector_outside_range {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W)
    (hdim : finrank K V < finrank K W) : ∃ c : W, c ∉ f.range := by
  classical
  have hsurj : ¬ Function.Surjective f := by
    intro hs
    have hle := f.finrank_range_le
    rw [LinearMap.range_eq_top.mpr hs, finrank_top] at hle
    exact (not_lt_of_ge hle) hdim
  simpa only [Function.Surjective, LinearMap.mem_range, not_forall] using hsurj
end Nagata.Workers.W24
end
end OAI
-- NormalCoefficients
namespace OAI
section
namespace Nagata.W18
open scoped BigOperators
theorem residue_ne_zero_of_not_dvd {A : Type*} [CommRing A]
    (G T : A) (hT : ¬G ∣ T) :
    Ideal.Quotient.mk (Ideal.span ({G} : Set A)) T ≠ 0 := by
  intro hz
  exact hT ((Ideal.Quotient.eq_zero_iff_dvd G T).mp hz)
theorem principal_diagonal_polynomial_ne_zero {A : Type*} [CommRing A]
    (s : Finset ℕ) (G : A) (T : ℕ → A) (j : ℕ → ℕ) (u : ℕ)
    (hne : s.Nonempty) (hweight : ∀ a ∈ s, a + j a = u)
    (hT : ∀ a ∈ s, ¬G ∣ T a) :
    (∑ a ∈ s, Polynomial.monomial (j a)
      (Ideal.Quotient.mk (Ideal.span ({G} : Set A)) (T a))) ≠ 0 := by
  apply diagonal_monomial_sum_ne_zero s j _ u hweight hne
  intro a ha
  exact residue_ne_zero_of_not_dvd G (T a) (hT a ha)
end Nagata.W18
end
section
noncomputable section
namespace Nagata.W18
variable {K : Type*} [CommRing K]
def bivariateToNested : MvPolynomial (Fin 2) K →+* Polynomial (Polynomial K) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp Polynomial.C)
    ![Polynomial.C Polynomial.X, Polynomial.X]
def nestedToBivariate : Polynomial (Polynomial K) →+* MvPolynomial (Fin 2) K :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0))
    (MvPolynomial.X 1)
theorem nestedToBivariate_comp_bivariateToNested :
    (nestedToBivariate (K := K)).comp bivariateToNested = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [bivariateToNested, nestedToBivariate]
  · intro i
    fin_cases i <;> simp [bivariateToNested, nestedToBivariate]
theorem bivariateToNested_comp_nestedToBivariate :
    (bivariateToNested (K := K)).comp nestedToBivariate = RingHom.id _ := by
  apply Polynomial.ringHom_ext
  · intro p
    have h : bivariateToNested.comp
        (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (0 : Fin 2))) =
        (Polynomial.C : Polynomial K →+* Polynomial (Polynomial K)) := by
      apply Polynomial.ringHom_ext
      · intro r
        simp [bivariateToNested]
      · simp [bivariateToNested]
    simpa [nestedToBivariate] using RingHom.congr_fun h p
  · simp [nestedToBivariate, bivariateToNested]
def bivariateNestedEquiv : MvPolynomial (Fin 2) K ≃+* Polynomial (Polynomial K) :=
  RingEquiv.ofRingHom bivariateToNested nestedToBivariate
    bivariateToNested_comp_nestedToBivariate nestedToBivariate_comp_bivariateToNested
theorem eval_bivariateToNested (a c : K) (F : MvPolynomial (Fin 2) K) :
    ((bivariateToNested F).eval (Polynomial.C c)).eval a =
      MvPolynomial.eval ![a, c] F := by
  have h : (Polynomial.evalRingHom a).comp
      ((Polynomial.evalRingHom (Polynomial.C c)).comp bivariateToNested) =
      MvPolynomial.eval ![a, c] := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [bivariateToNested]
    · intro i
      fin_cases i <;> simp [bivariateToNested]
  exact RingHom.congr_fun h F
theorem nestedPointIdeal_mem_iff (a c : K) (H : Polynomial (Polynomial K)) :
    H ∈ nestedPointIdeal a c ↔ (H.eval (Polynomial.C c)).eval a = 0 :=
  Polynomial.mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero
theorem pointIdeal_map_bivariateNestedEquiv (a c : K) :
    (Nagata.AffineMultiplicity.pointIdeal ![a, c]).map bivariateNestedEquiv =
      nestedPointIdeal a c := by
  ext H
  rw [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨F, hF, rfl⟩
    rw [nestedPointIdeal_mem_iff]
    exact (eval_bivariateToNested a c F).trans
      ((Nagata.AffineMultiplicity.pointIdeal_mem_iff _ _).mp hF)
  · intro hH
    refine ⟨bivariateNestedEquiv.symm H, ?_, bivariateNestedEquiv.apply_symm_apply H⟩
    rw [Nagata.AffineMultiplicity.pointIdeal_mem_iff,
      ← eval_bivariateToNested a c]
    change ((bivariateNestedEquiv (bivariateNestedEquiv.symm H)).eval
      (Polynomial.C c)).eval a = 0
    rw [bivariateNestedEquiv.apply_symm_apply]
    exact (nestedPointIdeal_mem_iff a c H).mp hH
theorem nested_order_of_affine_order (a c : K) (m : ℕ)
    (F : MvPolynomial (Fin 2) K)
    (hF : Nagata.AffineMultiplicity.orderAtLeast ![a, c] m F) :
    bivariateToNested F ∈ (nestedPointIdeal a c) ^ m := by
  have h := Ideal.mem_map_of_mem bivariateNestedEquiv hF
  rw [Ideal.map_pow, pointIdeal_map_bivariateNestedEquiv] at h
  exact h
end Nagata.W18
end
end
section
noncomputable section
open Polynomial
open scoped BigOperators
namespace Nagata.W18
theorem surface_order_penultimate_coefficient {K : Type*} [Field K]
    (H : Polynomial (Polynomial K)) (a c : K) (m : ℕ) (hm : 0 < m)
    (hdeg : H.natDegree ≤ m) (hH : H ∈ (nestedPointIdeal a c) ^ m)
    (htop : (H.coeff m).eval a ≠ 0) :
    (H.coeff (m - 1)).eval a = (-(m : K) * (H.coeff m).eval a) * c := by
  have h := Nagata.Workers.W24.polynomial_penultimate_coefficient_scalar
    (fiberRestriction a H) c m hm ((fiberRestriction_natDegree_le H a).trans hdeg)
    (fiber_power_divides_of_surface_order H a c m hH)
  rwa [fiberRestriction_coeff, fiberRestriction_leadingCoeff H a m hdeg htop] at h
end Nagata.W18
end
end
end OAI
-- HomogeneousFamilies
namespace OAI
section
namespace Nagata.Workers.W17
variable {K σ : Type*} [CommRing K] [IsDomain K]
theorem homogeneous_factor_degree {P Q : MvPolynomial σ K} {k d : Nat}
    (hP : P.IsHomogeneous k) (hPQ : (P * Q).IsHomogeneous d)
    (hne : P * Q ≠ 0) :
    k ≤ d ∧ Q.IsHomogeneous (d - k) := by
  letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule σ K) := MvPolynomial.gradedAlgebra
  let H := MvPolynomial.homogeneousSubmodule σ K
  have hsame : (DirectSum.decompose H (P * Q) d : MvPolynomial σ K) = P * Q :=
    DirectSum.decompose_of_mem_same H hPQ
  have hkd : k ≤ d := by
    by_contra hk
    have hzero : (DirectSum.decompose H (P * Q) d : MvPolynomial σ K) = 0 :=
      DirectSum.coe_decompose_mul_of_left_mem_of_not_le H hP hk
    exact hne (hsame.symm.trans hzero)
  have hpart : (DirectSum.decompose H (P * Q) d : MvPolynomial σ K) =
      P * (DirectSum.decompose H Q (d - k) : MvPolynomial σ K) :=
    DirectSum.coe_decompose_mul_of_left_mem_of_le H hP hkd
  have hQ : Q = (DirectSum.decompose H Q (d - k) : MvPolynomial σ K) :=
    mul_left_cancel₀ (left_ne_zero_of_mul hne) (hsame.symm.trans hpart)
  refine ⟨hkd, ?_⟩
  change Q ∈ H (d - k)
  rw [hQ]
  exact (DirectSum.decompose H Q (d - k)).property
theorem homogeneous_power_remainder {S G T : MvPolynomial σ K} {d k j : Nat}
    (hS : S.IsHomogeneous d) (hG : G.IsHomogeneous k)
    (hne : S ≠ 0) (hfactor : S = G ^ j * T) :
    k * j ≤ d ∧ T.IsHomogeneous (d - k * j) := by
  apply homogeneous_factor_degree (hG.pow j)
  · rwa [← hfactor]
  · rwa [← hfactor]
theorem homogeneous_power_exponent_bound {S G T : MvPolynomial σ K} {d k j : Nat}
    (hS : S.IsHomogeneous d) (hG : G.IsHomogeneous k)
    (hne : S ≠ 0) (hfactor : S = G ^ j * T) (hk : 0 < k) :
    j ≤ d / k := by
  apply (Nat.le_div_iff_mul_le hk).mpr
  simpa [Nat.mul_comm] using (homogeneous_power_remainder hS hG hne hfactor).1
end Nagata.Workers.W17
end
section
namespace Nagata.Workers.W17
theorem positive_homogeneous_not_isUnit {K σ : Type*} [CommRing K] [Nontrivial K]
    {G : MvPolynomial σ K} {k : ℕ} (hG : G.IsHomogeneous k) (hk : 0 < k) :
    ¬IsUnit G := by
  have hzero : MvPolynomial.eval (0 : σ → K) G = 0 := by
    rw [MvPolynomial.eval_zero]
    exact hG.coeff_eq_zero (by simpa using Nat.ne_of_lt hk)
  intro hu
  have hi := hu.map (MvPolynomial.eval (0 : σ → K))
  rw [hzero] at hi
  exact not_isUnit_zero hi
end Nagata.Workers.W17
end
section
namespace Nagata.Workers.W17
open scoped BigOperators
variable {A : Type*} [CommRing A] [WfDvdMonoid A]
theorem exists_factored_coefficients (S : Polynomial A) (G : A)
    (hG : ¬IsUnit G) :
    ∃ (j : Nat → Nat) (T : Nat → A),
      (∀ α, S.coeff α = G ^ j α * T α) ∧
      (∀ α, S.coeff α ≠ 0 → ¬G ∣ T α) := by
  classical
  have hfactor : ∀ α : Nat, ∃ n : Nat, ∃ t : A,
      S.coeff α = G ^ n * t ∧ (S.coeff α ≠ 0 → ¬G ∣ t) := by
    intro α
    by_cases hα : S.coeff α = 0
    · exact ⟨0, 0, by simp [hα], fun hn => (hn hα).elim⟩
    · obtain ⟨n, t, hnot, heq⟩ := WfDvdMonoid.max_power_factor' hα hG
      exact ⟨n, t, heq, fun _ => hnot⟩
  choose j T hfac hnot using hfactor
  exact ⟨j, T, hfac, hnot⟩
theorem exists_nonzero_normal_initial
    (S : Polynomial A) (G : A) (hS : S ≠ 0) (hG : ¬IsUnit G) :
    ∃ (j : Nat → Nat) (T : Nat → A) (u : Nat),
      (∀ α, S.coeff α = G ^ j α * T α) ∧
      (∀ α ∈ S.support, ¬G ∣ T α) ∧
      (∀ α ∈ S.support, u ≤ α + j α) ∧
      (S.support.filter (fun α => α + j α = u)).Nonempty ∧
      (∑ α ∈ S.support.filter (fun α => α + j α = u),
        Polynomial.monomial (j α)
          (Ideal.Quotient.mk (Ideal.span ({G} : Set A)) (T α))) ≠ 0 := by
  classical
  obtain ⟨j, T, hfactor, hnot⟩ := exists_factored_coefficients S G hG
  have hnonzero : ∀ α ∈ S.support,
      Ideal.Quotient.mk (Ideal.span ({G} : Set A)) (T α) ≠ 0 := by
    intro α hα hz
    exact hnot α (Polynomial.mem_support_iff.mp hα)
      ((Ideal.Quotient.eq_zero_iff_dvd G (T α)).mp hz)
  obtain ⟨u, hmin, hselected, hinitial⟩ :=
    Nagata.W18.exists_lowest_weight_polynomial S.support j
      (fun α => Ideal.Quotient.mk (Ideal.span ({G} : Set A)) (T α))
      (Polynomial.support_nonempty.mpr hS) hnonzero
  exact ⟨j, T, u, hfactor, fun α hα => hnot α (Polynomial.mem_support_iff.mp hα),
    hmin, hselected, hinitial⟩
omit [WfDvdMonoid A] in
theorem initial_weight_bound_from_constant (S : Polynomial A)
    (j : Nat → Nat) (u : Nat) (hzero : S.coeff 0 ≠ 0)
    (hmin : ∀ α ∈ S.support, u ≤ α + j α) : u ≤ j 0 := by
  simpa using hmin 0 (Polynomial.mem_support_iff.mpr hzero)
end Nagata.Workers.W17
end
section
namespace Nagata.Workers.W17
open scoped BigOperators
variable {A : Type*} [CommRing A]
noncomputable def liftedNormalPolynomial
    (indices : Finset Nat) (j : Nat → Nat) (T : Nat → A) : Polynomial A :=
  ∑ α ∈ indices, Polynomial.monomial (j α) (T α)
theorem coeff_liftedNormalPolynomial
    (indices : Finset Nat) (j : Nat → Nat) (T : Nat → A) (n : Nat) :
    (liftedNormalPolynomial indices j T).coeff n =
      ∑ α ∈ indices.filter (fun α => j α = n), T α := by
  classical
  simp only [liftedNormalPolynomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial, Finset.sum_filter]
theorem map_liftedNormalPolynomial {B : Type*} [CommRing B]
    (indices : Finset Nat) (j : Nat → Nat) (T : Nat → A) (f : A →+* B) :
    (liftedNormalPolynomial indices j T).map f =
      ∑ α ∈ indices, Polynomial.monomial (j α) (f (T α)) := by
  simp only [liftedNormalPolynomial, Polynomial.map_sum, Polynomial.map_monomial]
theorem quotient_liftedNormalPolynomial_ne_zero
    (indices : Finset Nat) (j : Nat → Nat) (T : Nat → A) (G : A) (u : Nat)
    (hne : indices.Nonempty) (hweight : ∀ α ∈ indices, α + j α = u)
    (hnot : ∀ α ∈ indices, ¬G ∣ T α) :
    (liftedNormalPolynomial indices j T).map
      (Ideal.Quotient.mk (Ideal.span ({G} : Set A))) ≠ 0 := by
  rw [map_liftedNormalPolynomial]
  exact Nagata.W18.principal_diagonal_polynomial_ne_zero
    indices G T j u hne hweight hnot
theorem coeff_liftedNormalPolynomial_eq_zero_above
    (indices : Finset Nat) (j : Nat → Nat) (T : Nat → A) (bound n : Nat)
    (hbound : ∀ α ∈ indices, j α ≤ bound) (hn : bound < n) :
    (liftedNormalPolynomial indices j T).coeff n = 0 := by
  classical
  have hempty : indices.filter (fun α => j α = n) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro α hα heq
    have hle : n ≤ bound := heq ▸ hbound α hα
    exact (Nat.not_lt_of_ge hle) hn
  rw [coeff_liftedNormalPolynomial, hempty, Finset.sum_empty]
end Nagata.Workers.W17
end
section
namespace Nagata.Workers.W17
open scoped BigOperators
open Nagata.W27
variable {K : Type*} [CommRing K]
noncomputable def indexedPlaneFamily (d : Nat)
    (q : HomogeneousMonomial d → Polynomial K) : Polynomial (MvPolynomial (Fin 3) K) :=
  ∑ ν : HomogeneousMonomial d, (q ν).map MvPolynomial.C *
    Polynomial.C (MvPolynomial.monomial ν.val (1 : K))
theorem coeff_indexedPlaneFamily (d : Nat)
    (q : HomogeneousMonomial d → Polynomial K) (α : Nat) :
    (indexedPlaneFamily d q).coeff α =
      ∑ ν : HomogeneousMonomial d, MvPolynomial.monomial ν.val ((q ν).coeff α) := by
  classical
  unfold indexedPlaneFamily
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro ν hν
  rw [Polynomial.coeff_mul_C, Polynomial.coeff_map, MvPolynomial.C_mul_monomial, mul_one]
theorem monomial_coeff_indexedPlaneFamily (d : Nat)
    (q : HomogeneousMonomial d → Polynomial K) (α : Nat) (ν : HomogeneousMonomial d) :
    ((indexedPlaneFamily d q).coeff α).coeff ν.val = (q ν).coeff α := by
  classical
  rw [coeff_indexedPlaneFamily, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single ν]
  · simp
  · intro b hb hne
    simp only [ite_eq_right_iff]
    intro he
    exact (hne (Subtype.ext he)).elim
  · simp
theorem indexedPlaneFamily_homogeneous (d : Nat)
    (q : HomogeneousMonomial d → Polynomial K) (α : Nat) :
    ((indexedPlaneFamily d q).coeff α).IsHomogeneous d := by
  rw [coeff_indexedPlaneFamily]
  apply MvPolynomial.IsHomogeneous.sum
  intro ν hν
  exact MvPolynomial.isHomogeneous_monomial _ ν.property
theorem indexedPlaneFamily_constant_ne_zero (d : Nat)
    (q : HomogeneousMonomial d → Polynomial K)
    (hq : ∃ ν, (q ν).coeff 0 ≠ 0) :
    (indexedPlaneFamily d q).coeff 0 ≠ 0 := by
  obtain ⟨ν, hν⟩ := hq
  intro hz
  have h := monomial_coeff_indexedPlaneFamily d q 0 ν
  rw [hz, MvPolynomial.coeff_zero] at h
  exact hν h.symm
theorem eval_indexedPlaneFamily (d : Nat)
    (q : HomogeneousMonomial d → Polynomial K) (s : K) :
    (indexedPlaneFamily d q).eval (MvPolynomial.C s) =
      ∑ ν : HomogeneousMonomial d, MvPolynomial.monomial ν.val ((q ν).eval s) := by
  classical
  unfold indexedPlaneFamily
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro ν hν
  rw [Polynomial.eval_mul, Polynomial.eval_map_apply, Polynomial.eval_C,
    MvPolynomial.C_mul_monomial, mul_one]
theorem eval_indexedPlaneFamily_eq_coordinates_symm (d : Nat)
    (q : HomogeneousMonomial d → Polynomial K) (s : K) :
    (indexedPlaneFamily d q).eval (MvPolynomial.C s) =
      ((homogeneousCoordinates d).symm (fun ν => (q ν).eval s)).val := by
  classical
  rw [eval_indexedPlaneFamily]
  let F : MvPolynomial.homogeneousSubmodule (Fin 3) K d :=
    ⟨∑ ν : HomogeneousMonomial d, MvPolynomial.monomial ν.val ((q ν).eval s),
      MvPolynomial.IsHomogeneous.sum _ _ _
        (fun ν _ => MvPolynomial.isHomogeneous_monomial _ ν.property)⟩
  have hcoord : homogeneousCoordinates d F = fun ν => (q ν).eval s := by
    funext ν
    change F.val.coeff ν.val = (q ν).eval s
    dsimp only [F]
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    rw [Finset.sum_eq_single ν]
    · simp
    · intro b hb hne
      simp only [ite_eq_right_iff]
      intro he
      exact (hne (Subtype.ext he)).elim
    · simp
  have hF : F = (homogeneousCoordinates d).symm (fun ν => (q ν).eval s) := by
    apply (homogeneousCoordinates d).injective
    rw [LinearEquiv.apply_symm_apply]
    exact hcoord
  exact congrArg Subtype.val hF
end Nagata.Workers.W17
end
section
namespace Nagata.Workers.W17
open scoped BigOperators
variable {K : Type*} [Field K]
theorem exists_degree_bounded_plane_initial
    (S : Polynomial (MvPolynomial (Fin 3) K))
    (G : MvPolynomial (Fin 3) K) (d k : Nat)
    (hcoeff : ∀ α, (S.coeff α).IsHomogeneous d)
    (hG : G.IsHomogeneous k) (hunit : ¬IsUnit G) (hk : 0 < k)
    (hzero : S.coeff 0 ≠ 0) :
    ∃ (j : Nat → Nat) (T : Nat → MvPolynomial (Fin 3) K) (u : Nat),
      (∀ α, S.coeff α = G ^ j α * T α) ∧
      (∀ α ∈ S.support, ¬G ∣ T α) ∧
      (∀ α ∈ S.support, j α ≤ d / k ∧ (T α).IsHomogeneous (d - k * j α)) ∧
      (∀ α ∈ S.support, u ≤ α + j α) ∧
      u ≤ d / k ∧
      (S.support.filter (fun α => α + j α = u)).Nonempty ∧
      (∑ α ∈ S.support.filter (fun α => α + j α = u),
        Polynomial.monomial (j α)
          (Ideal.Quotient.mk
            (Ideal.span ({G} : Set (MvPolynomial (Fin 3) K))) (T α))) ≠ 0 := by
  classical
  have hS : S ≠ 0 := by
    intro hS
    apply hzero
    rw [hS, Polynomial.coeff_zero]
  obtain ⟨j, T, u, hfactor, hnot, hmin, hselected, hinitial⟩ :=
    exists_nonzero_normal_initial S G hS hunit
  have hdegree : ∀ α ∈ S.support,
      j α ≤ d / k ∧ (T α).IsHomogeneous (d - k * j α) := by
    intro α hα
    have hn : S.coeff α ≠ 0 := Polynomial.mem_support_iff.mp hα
    exact ⟨homogeneous_power_exponent_bound (hcoeff α) hG hn (hfactor α) hk,
      (homogeneous_power_remainder (hcoeff α) hG hn (hfactor α)).2⟩
  have hu : u ≤ d / k :=
    (initial_weight_bound_from_constant S j u hzero hmin).trans
      (hdegree 0 (Polynomial.mem_support_iff.mpr hzero)).1
  exact ⟨j, T, u, hfactor, hnot, hdegree, hmin, hu, hselected, hinitial⟩
end Nagata.Workers.W17
end
section
namespace Nagata.Workers.W17
variable {K σ : Type*} [CommRing K]
theorem homogeneous_coeff_liftedNormalPolynomial
    (indices : Finset Nat) (j : Nat → Nat) (T : Nat → MvPolynomial σ K)
    (d k : Nat) (hT : ∀ α ∈ indices, (T α).IsHomogeneous (d - k * j α))
    (n : Nat) :
    ((liftedNormalPolynomial indices j T).coeff n).IsHomogeneous (d - k * n) := by
  rw [coeff_liftedNormalPolynomial]
  apply MvPolynomial.IsHomogeneous.sum
  intro α hα
  have hmem := (Finset.mem_filter.mp hα).1
  have heq := (Finset.mem_filter.mp hα).2
  simpa only [heq] using hT α hmem
theorem nonzero_coeff_liftedNormalPolynomial_bound
    (indices : Finset Nat) (j : Nat → Nat) (T : Nat → MvPolynomial σ K)
    (bound n : Nat) (hbound : ∀ α ∈ indices, j α ≤ bound)
    (hne : (liftedNormalPolynomial indices j T).coeff n ≠ 0) : n ≤ bound := by
  apply Nat.le_of_not_gt
  intro hn
  exact hne (coeff_liftedNormalPolynomial_eq_zero_above indices j T bound n hbound hn)
end Nagata.Workers.W17
end
section
namespace Nagata.Workers.W17
open scoped BigOperators
theorem directChart_factored_family
    (S : Polynomial (MvPolynomial (Fin 3) ℂ))
    (G : MvPolynomial (Fin 3) ℂ) (j : ℕ → ℕ)
    (T : ℕ → MvPolynomial (Fin 3) ℂ)
    (hfactor : ∀ α, S.coeff α = G ^ j α * T α)
    (c : Fin 3) (s : ℂ) :
    Nagata.W27.directChartHom c (S.eval (MvPolynomial.C s)) =
      Nagata.Workers.W28.factoredPlaneFamily S.support j
        (fun α => Nagata.W27.directChartHom c (T α))
        (Nagata.W27.directChartHom c G) s := by
  classical
  rw [Polynomial.eval_eq_sum]
  unfold Polynomial.sum Nagata.Workers.W28.factoredPlaneFamily
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro α hα
  rw [hfactor, map_mul, map_mul, map_pow, map_pow]
  simp only [Nagata.W27.directChartHom, MvPolynomial.eval₂Hom_C, map_pow]
  ring
end Nagata.Workers.W17
end
end OAI
-- MixedDerivatives
namespace OAI
section
namespace Nagata.Workers.W30
open MvPolynomial
open scoped BigOperators
def planePoint (x y : ℂ) : Fin 2 → ℂ := Fin.cases x (fun _ => y)
noncomputable def planeValue (p : Bivariate ℂ) (x y : ℂ) : ℂ :=
  eval (planePoint x y) p
lemma planeValue_monomial (a : Fin 2 →₀ ℕ) (c x y : ℂ) :
    planeValue (monomial a c) x y = c * x ^ (a 0) * y ^ (a 1) := by
  have hmon : (monomial a c : Bivariate ℂ) = C c * monomial a 1 := by
    rw [C_mul_monomial, mul_one]
  rw [planeValue, hmon, ← exponentPair_eta a, monomial_exponentPair]
  simp [mul_assoc, show planePoint x y 0 = x by rfl, show planePoint x y 1 = y by rfl]
lemma planeValue_sum (p : Bivariate ℂ) (x y : ℂ) :
    planeValue p x y = ∑ a ∈ p.support, p.coeff a * x ^ (a 0) * y ^ (a 1) := by
  conv_lhs => rw [p.as_sum]
  simp only [planeValue, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact planeValue_monomial a (p.coeff a) x y
lemma innerDerivative_zero (p : Bivariate ℂ) (b : ℕ) (x : ℂ) :
    iteratedDeriv b (fun y => planeValue p x y) 0 =
      ∑ a ∈ p.support, p.coeff a * x ^ (a 0) *
        (if b = a 1 then ((a 1).factorial : ℂ) else 0) := by
  classical
  simp_rw [planeValue_sum]
  rw [iteratedDeriv_fun_sum (fun a _ => contDiffAt_const.mul (contDiffAt_id.pow (a 1)))]
  simp only [iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : b = a 1 <;> simp [h]
noncomputable def mixedDerivative (ell b : ℕ) (p : Bivariate ℂ) (x y : ℂ) : ℂ :=
  iteratedDeriv ell (fun z => iteratedDeriv b (fun w => planeValue p z w) y) x
theorem mixedDerivative_zero (ell b : ℕ) (p : Bivariate ℂ) :
    mixedDerivative ell b p 0 0 =
      (ell.factorial : ℂ) * (b.factorial : ℂ) * p.coeff (exponentPair ell b) := by
  classical
  unfold mixedDerivative
  simp_rw [innerDerivative_zero]
  rw [iteratedDeriv_fun_sum (fun a _ =>
    (contDiffAt_const.mul (contDiffAt_id.pow (a 0))).mul contDiffAt_const)]
  simp only [iteratedDeriv_mul_const_field, iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_pow_zero]
  rw [Finset.sum_eq_single (exponentPair ell b)]
  · simp [mul_comm, mul_left_comm, mul_assoc]
  · intro a ha hne
    by_cases h0 : ell = a 0
    · by_cases h1 : b = a 1
      · exfalso
        apply hne
        simpa [← h0, ← h1] using (exponentPair_eta a).symm
      · simp [h1]
    · simp [h0]
  · intro hnot
    have hc : p.coeff (exponentPair ell b) = 0 := by
      simpa only [mem_support_iff, not_not] using hnot
    simp [hc]
lemma planePoint_add (x y u v : ℂ) :
    planePoint x y + planePoint u v = planePoint (x+u) (y+v) := by
  funext i
  refine Fin.cases rfl (fun _ => rfl) i
lemma planeValue_translate (p : Bivariate ℂ) (x y u v : ℂ) :
    planeValue (Nagata.AffineMultiplicity.translateHom (planePoint x y) p) u v =
      planeValue p (u+x) (v+y) := by
  unfold planeValue
  rw [Nagata.AffineMultiplicity.eval_translate, planePoint_add]
end Nagata.Workers.W30
end
end OAI
-- AnalyticOrder
namespace OAI
section
noncomputable section
namespace Nagata.W18
end Nagata.W18
end
end
section
noncomputable section
namespace Nagata.W18
open Nagata.Workers.W30
open Nagata.AffineMultiplicity
open Nagata.Workers.W28
theorem polynomial_coeff_zero_of_centered_powerSeries
    (P : MvPolynomial (Fin 2) ℂ)
    (S : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ)
    (hS : HasFPowerSeriesAt (fun z : ℂ × ℂ => planeValue P z.1 z.2) S 0)
    (m : ℕ) (hzero : ∀ n < m, S n = 0) :
    ∀ ell b : ℕ, ell + b < m → P.coeff (exponentPair ell b) = 0 := by
  intro ell b hlt
  have hd := Nagata.W19.mixed_iteratedDeriv_zero_of_powerSeries 0 hS m hzero ell b hlt
  change mixedDerivative ell b P 0 0 = 0 at hd
  rw [mixedDerivative_zero] at hd
  have hfac : (ell.factorial : ℂ) * (b.factorial : ℂ) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero ell))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero b))
  exact (mul_eq_zero.mp hd).resolve_left hfac
theorem polynomial_ideal_order_of_powerSeries
    (P : MvPolynomial (Fin 2) ℂ) (p : ℂ × ℂ)
    (S : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ)
    (hS : HasFPowerSeriesAt (fun z : ℂ × ℂ => planeValue P z.1 z.2) S p)
    (m : ℕ) (hzero : ∀ n < m, S n = 0) :
    orderAtLeast (planePoint p.1 p.2) m P := by
  have hshift := hS.comp_sub (-p)
  simp only [add_neg_cancel] at hshift
  have htranslated : HasFPowerSeriesAt
      (fun z : ℂ × ℂ => planeValue (translateHom (planePoint p.1 p.2) P) z.1 z.2)
      S 0 := by
    apply hshift.congr
    exact Filter.Eventually.of_forall fun z => by
      dsimp only
      rw [planeValue_translate]
      simp only [sub_neg_eq_add, Prod.fst_add, Prod.snd_add]
  apply (orderAtLeast_finTwo_iff_taylor_coeff (planePoint p.1 p.2) m P).mpr
  exact polynomial_coeff_zero_of_centered_powerSeries _ S htranslated m hzero
theorem planePoint_eq_coordinate_function (p : ℂ × ℂ) :
    planePoint p.1 p.2 = (fun i : Fin 2 => if i = 0 then p.1 else p.2) := by
  funext i
  fin_cases i <;> rfl
theorem polynomial_analytic_order_implies_ideal_order
    (P : MvPolynomial (Fin 2) ℂ) (p : ℂ × ℂ) (m : ℕ)
    (hP : HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun z : ℂ × ℂ => MvPolynomial.eval
        (fun i => if i = 0 then z.1 else z.2) P) p m) :
    orderAtLeast (fun i : Fin 2 => if i = 0 then p.1 else p.2) m P := by
  obtain ⟨S, hS, hzero⟩ := hP
  have hseries : HasFPowerSeriesAt (fun z : ℂ × ℂ => planeValue P z.1 z.2) S p := by
    simpa only [planeValue, planePoint_eq_coordinate_function] using hS
  have h := polynomial_ideal_order_of_powerSeries P p S hseries m hzero
  rwa [planePoint_eq_coordinate_function] at h
theorem nested_ideal_order_of_analytic_order
    (P : MvPolynomial (Fin 2) ℂ) (a c : ℂ) (m : ℕ)
    (hP : HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun z : ℂ × ℂ => MvPolynomial.eval
        (fun i => if i = 0 then z.1 else z.2) P) (a, c) m) :
    bivariateToNested P ∈ (nestedPointIdeal a c) ^ m := by
  apply nested_order_of_affine_order a c m P
  have h := polynomial_analytic_order_implies_ideal_order P (a, c) m hP
  convert h using 1
  funext i
  fin_cases i <;> rfl
end Nagata.W18
end
end
section
noncomputable section
namespace Nagata.W18
open Nagata.Workers.W28
theorem nestedEvaluation_eq_polynomialEvaluation
    (H : Polynomial (Polynomial ℂ)) (z : ℂ × ℂ) :
    (H.eval (Polynomial.C z.2)).eval z.1 =
      MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z.1 else z.2)
        (nestedToBivariate H) := by
  have h := eval_bivariateToNested z.1 z.2 (nestedToBivariate H)
  have hinv : bivariateToNested (nestedToBivariate H) = H :=
    RingHom.congr_fun bivariateToNested_comp_nestedToBivariate H
  rw [hinv] at h
  have hcoords : ![z.1, z.2] = (fun i : Fin 2 => if i = 0 then z.1 else z.2) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hcoords] using h
theorem nested_polynomial_ideal_order_of_analytic_order
    (H : Polynomial (Polynomial ℂ)) (a c : ℂ) (m : ℕ)
    (hH : HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun z : ℂ × ℂ => (H.eval (Polynomial.C z.2)).eval z.1) (a, c) m) :
    H ∈ (nestedPointIdeal a c) ^ m := by
  have hP : HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun z : ℂ × ℂ => MvPolynomial.eval
        (fun i => if i = 0 then z.1 else z.2) (nestedToBivariate H)) (a, c) m := by
    simpa only [nestedEvaluation_eq_polynomialEvaluation] using hH
  have h := nested_ideal_order_of_analytic_order (nestedToBivariate H) a c m hP
  have hinv : bivariateToNested (nestedToBivariate H) = H :=
    RingHom.congr_fun bivariateToNested_comp_nestedToBivariate H
  rwa [hinv] at h
end Nagata.W18
end
end
end OAI
-- CycleMultiplicity
namespace OAI
section
namespace Nagata.AffineMultiplicity
variable {σ R : Type*} [CommRing R]
end Nagata.AffineMultiplicity
end
section
namespace Nagata.W04.ReducibleSquare
variable {K : Type*} [Field K]
theorem lineRestriction_eval (i a : K) (F : MvPolynomial (Fin 3) K) :
    (lineRestriction i F).eval a =
      MvPolynomial.eval ![a, i ^ 2 - i * a, 1] F := by
  have h : (Polynomial.evalRingHom a).comp (lineRestriction i) =
      MvPolynomial.eval ![a, i ^ 2 - i * a, 1] := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [lineRestriction]
    · intro j
      fin_cases j <;> simp [lineRestriction, lineSubstitution]
  exact RingHom.congr_fun h F
end Nagata.W04.ReducibleSquare
end
section
namespace Nagata.AffineMultiplicity
variable {σ R : Type*} [CommRing R]
end Nagata.AffineMultiplicity
end
section
namespace Nagata.ProjectiveGeometry
end Nagata.ProjectiveGeometry
end
section
noncomputable section
open scoped BigOperators
namespace Nagata.AffineMultiplicity
end Nagata.AffineMultiplicity
namespace Nagata.W15
open Nagata.ProjectiveGeometry
end Nagata.W15
end
end
section
noncomputable section
open scoped BigOperators
namespace Nagata.W15
open Nagata.Workers.W30 Nagata.ProjectiveGeometry
end Nagata.W15
end
end
section
noncomputable section
open scoped BigOperators
namespace Nagata.W15
open Nagata.Workers.W30 Nagata.ProjectiveGeometry
end Nagata.W15
end
end
end OAI
-- LineRestriction
namespace OAI
section
noncomputable section
namespace Nagata.Workers.W24
open Polynomial
open scoped BigOperators
theorem product_linear_factors_dvd_of_eval_zero {A ι : Type*} [CommRing A] [IsDomain A]
    (a : ι → A) (ha : Function.Injective a) (s : Finset ι) (R : A[X])
    (hzero : ∀ i ∈ s, R.eval (a i) = 0) :
    (∏ i ∈ s, (X - C (a i))) ∣ R := by
  classical
  induction s using Finset.induction_on generalizing R with
  | empty => simp
  | @insert i s hi ih =>
    have hroot : (X - C (a i)) ∣ R :=
      Polynomial.dvd_iff_isRoot.mpr (hzero i (Finset.mem_insert_self i s))
    obtain ⟨T, hRT⟩ := hroot
    have hTzero : ∀ j ∈ s, T.eval (a j) = 0 := by
      intro j hj
      have hz := hzero j (Finset.mem_insert_of_mem hj)
      rw [hRT, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C] at hz
      have hne : a j - a i ≠ 0 := by
        apply sub_ne_zero.mpr
        intro heq
        exact hi (ha heq ▸ hj)
      exact (mul_eq_zero.mp hz).resolve_left hne
    obtain ⟨Q, hTQ⟩ := ih T hTzero
    refine ⟨Q, ?_⟩
    rw [Finset.prod_insert hi, hRT, hTQ, mul_assoc]
def affineLineGraph (K : Type*) [CommRing K] (i : ℕ) : K[X] :=
  C ((i : K) ^ 2) - C (i : K) * X
def lineUnionEquation (K : Type*) [CommRing K] (k : ℕ) : Polynomial (Polynomial K) :=
  ∏ i : Fin k, (X - C (affineLineGraph K i.val))
def lineRestriction {K : Type*} [CommRing K] (R : Polynomial (Polynomial K))
    (i : ℕ) : Polynomial K := R.eval (affineLineGraph K i)
end Nagata.Workers.W24
end
end
section
namespace Nagata.Workers.W24
open Polynomial
open scoped BigOperators
theorem linear_product_dvd_iff {A ι : Type*} [CommRing A] [IsDomain A] [Fintype ι]
    (a : ι → A) (ha : Function.Injective a) (R : A[X]) :
    (∏ i, (X - C (a i))) ∣ R ↔ ∀ i, R.eval (a i) = 0 := by
  classical
  constructor
  · intro h i
    exact Polynomial.dvd_iff_isRoot.mp
      ((Finset.dvd_prod_of_mem (fun i => X - C (a i)) (Finset.mem_univ i)).trans h)
  · intro h
    exact product_linear_factors_dvd_of_eval_zero a ha Finset.univ R (fun i _ => h i)
end Nagata.Workers.W24
end
section
noncomputable section
namespace Nagata.Workers.W24
open scoped BigOperators
private theorem finThreeCases_one {A : Type*} (a : A) (f : Fin 2 → A) :
    Fin.cases a f (1 : Fin 3) = f 0 := rfl
private theorem finThreeCases_two {A : Type*} (a : A) (f : Fin 2 → A) :
    Fin.cases a f (2 : Fin 3) = f 1 := rfl
def homogeneousLineGraph (K : Type*) [CommRing K] (i : ℕ) : MvPolynomial (Fin 2) K :=
  MvPolynomial.C ((i : K) ^ 2) * MvPolynomial.X 1 -
    MvPolynomial.C (i : K) * MvPolynomial.X 0
def homogeneousLineEquation (K : Type*) [CommRing K] (i : ℕ) : MvPolynomial (Fin 3) K :=
  MvPolynomial.X 1 - (MvPolynomial.C ((i : K) ^ 2) * MvPolynomial.X 2 -
    MvPolynomial.C (i : K) * MvPolynomial.X 0)
def ternaryAsPolynomialInY (K : Type*) [CommSemiring K] :
    MvPolynomial (Fin 3) K ≃ₐ[K] Polynomial (MvPolynomial (Fin 2) K) :=
  (MvPolynomial.renameEquiv K (Equiv.swap (0 : Fin 3) 1)).trans
    (MvPolynomial.finSuccEquiv K 2)
def homogeneousLineRestriction {K : Type*} [CommRing K]
    (R : MvPolynomial (Fin 3) K) (i : ℕ) : MvPolynomial (Fin 2) K :=
  (ternaryAsPolynomialInY K R).eval (homogeneousLineGraph K i)
def homogeneousLineSubstitution (K : Type*) [CommRing K] (i : ℕ) :
    Fin 3 → MvPolynomial (Fin 2) K :=
  ![MvPolynomial.X 0, homogeneousLineGraph K i, MvPolynomial.X 1]
def homogeneousLineUnion (K : Type*) [CommRing K] (k : ℕ) : MvPolynomial (Fin 3) K :=
  ∏ i : Fin k, homogeneousLineEquation K i.val
theorem homogeneousLineGraph_homogeneous {K : Type*} [CommRing K] (i : ℕ) :
    (homogeneousLineGraph K i).IsHomogeneous 1 := by
  exact ((MvPolynomial.isHomogeneous_X K 1).C_mul ((i : K) ^ 2)).sub
    ((MvPolynomial.isHomogeneous_X K 0).C_mul (i : K))
theorem homogeneousLineRestriction_eq_eval₂ {K : Type*} [CommRing K]
    (R : MvPolynomial (Fin 3) K) (i : ℕ) :
    homogeneousLineRestriction R i = MvPolynomial.eval₂ MvPolynomial.C
      (homogeneousLineSubstitution K i) R := by
  have h : (Polynomial.evalRingHom (homogeneousLineGraph K i)).comp
      (ternaryAsPolynomialInY K).toRingHom =
      MvPolynomial.eval₂Hom MvPolynomial.C (homogeneousLineSubstitution K i) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [ternaryAsPolynomialInY, MvPolynomial.renameEquiv_apply,
        MvPolynomial.finSuccEquiv_apply]
    · intro j
      fin_cases j <;>
        simp [ternaryAsPolynomialInY, homogeneousLineSubstitution,
          MvPolynomial.renameEquiv_apply, MvPolynomial.finSuccEquiv_apply,
          Equiv.swap_apply_def, finThreeCases_one, finThreeCases_two]
  exact congrArg (fun f : MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 2) K => f R) h
theorem homogeneousLineRestriction_homogeneous {K : Type*} [CommRing K]
    (R : MvPolynomial (Fin 3) K) (i d : ℕ) (hR : R.IsHomogeneous d) :
    (homogeneousLineRestriction R i).IsHomogeneous d := by
  rw [homogeneousLineRestriction_eq_eval₂]
  have hcoords : ∀ j, (homogeneousLineSubstitution K i j).IsHomogeneous 1 := by
    intro j
    fin_cases j
    · exact MvPolynomial.isHomogeneous_X K 0
    · exact homogeneousLineGraph_homogeneous i
    · exact MvPolynomial.isHomogeneous_X K 1
  simpa only [one_mul] using hR.eval₂ MvPolynomial.C
    (homogeneousLineSubstitution K i) (fun r => MvPolynomial.isHomogeneous_C (Fin 2) r) hcoords
theorem homogeneousLineEquation_homogeneous {K : Type*} [CommRing K] (i : ℕ) :
    (homogeneousLineEquation K i).IsHomogeneous 1 := by
  exact (MvPolynomial.isHomogeneous_X K 1).sub
    (((MvPolynomial.isHomogeneous_X K 2).C_mul ((i : K) ^ 2)).sub
      ((MvPolynomial.isHomogeneous_X K 0).C_mul (i : K)))
theorem homogeneousLineUnion_homogeneous {K : Type*} [CommRing K] (k : ℕ) :
    (homogeneousLineUnion K k).IsHomogeneous k := by
  simpa only [homogeneousLineUnion, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one]
    using MvPolynomial.IsHomogeneous.prod Finset.univ
      (fun i : Fin k => homogeneousLineEquation K i.val) (fun _ => 1)
      (fun i _ => homogeneousLineEquation_homogeneous i.val)
theorem homogeneousLineGraph_injective {K : Type*} [CommRing K] [CharZero K] :
    Function.Injective (homogeneousLineGraph K) := by
  intro i j h
  have he := congrArg (MvPolynomial.eval (fun v : Fin 2 => if v = 0 then (1 : K) else 0)) h
  simpa [homogeneousLineGraph] using he
theorem ternaryAsPolynomialInY_line {K : Type*} [CommRing K] (i : ℕ) :
    ternaryAsPolynomialInY K (homogeneousLineEquation K i) =
      Polynomial.X - Polynomial.C (homogeneousLineGraph K i) := by
  simp [ternaryAsPolynomialInY, homogeneousLineEquation, homogeneousLineGraph,
    MvPolynomial.renameEquiv_apply, MvPolynomial.finSuccEquiv_apply,
    Equiv.swap_apply_def, finThreeCases_one, finThreeCases_two]
theorem ternaryAsPolynomialInY_union {K : Type*} [CommRing K] (k : ℕ) :
    ternaryAsPolynomialInY K (homogeneousLineUnion K k) =
      ∏ i : Fin k, (Polynomial.X - Polynomial.C (homogeneousLineGraph K i.val)) := by
  simp only [homogeneousLineUnion, map_prod, ternaryAsPolynomialInY_line]
theorem homogeneousUnion_dvd_iff_restrictions_zero {K : Type*} [Field K] [CharZero K]
    (k : ℕ) (R : MvPolynomial (Fin 3) K) :
    homogeneousLineUnion K k ∣ R ↔ ∀ i : Fin k, homogeneousLineRestriction R i.val = 0 := by
  rw [← map_dvd_iff (ternaryAsPolynomialInY K), ternaryAsPolynomialInY_union]
  exact linear_product_dvd_iff (fun i : Fin k => homogeneousLineGraph K i.val)
    (homogeneousLineGraph_injective.comp Fin.val_injective) (ternaryAsPolynomialInY K R)
theorem exists_nonzero_homogeneousLineRestriction {K : Type*} [Field K] [CharZero K]
    (k : ℕ) (R : MvPolynomial (Fin 3) K) (hR : ¬ homogeneousLineUnion K k ∣ R) :
    ∃ i : Fin k, homogeneousLineRestriction R i.val ≠ 0 := by
  classical
  simpa only [not_forall] using mt (homogeneousUnion_dvd_iff_restrictions_zero k R).mpr hR
end Nagata.Workers.W24
end
end
section
noncomputable section
namespace Nagata.Workers.W24
theorem binaryAffine_homogeneousLineRestriction
    (R : MvPolynomial (Fin 3) ℂ) (i : ℕ) :
    Nagata.W16.binaryAffine (homogeneousLineRestriction R i) =
      Nagata.W04.ReducibleSquare.lineRestriction (i : ℂ) R := by
  rw [homogeneousLineRestriction_eq_eval₂]
  let f : MvPolynomial (Fin 2) ℂ →+* Polynomial ℂ :=
    MvPolynomial.eval₂Hom Polynomial.C (fun j => if j = 0 then Polynomial.X else 1)
  change f (MvPolynomial.eval₂Hom MvPolynomial.C (homogeneousLineSubstitution ℂ i) R) = _
  rw [MvPolynomial.map_eval₂Hom]
  have hC : f.comp MvPolynomial.C = Polynomial.C := by
    ext c
    simp [f]
  have hcoords : (fun j => f (homogeneousLineSubstitution ℂ i j)) =
      Nagata.W04.ReducibleSquare.lineSubstitution (i : ℂ) := by
    funext j
    fin_cases j <;>
      simp [f, homogeneousLineSubstitution, homogeneousLineGraph,
        Nagata.W04.ReducibleSquare.lineSubstitution]
  rw [hC, hcoords]
  rfl
theorem affine_lineRestriction_eq_zero_iff
    (R : MvPolynomial (Fin 3) ℂ) (i d : ℕ) (hR : R.IsHomogeneous d) :
    Nagata.W04.ReducibleSquare.lineRestriction (i : ℂ) R = 0 ↔
      homogeneousLineRestriction R i = 0 := by
  rw [← binaryAffine_homogeneousLineRestriction]
  constructor
  · exact Nagata.W16.binaryAffine_eq_zero_imp
      (homogeneousLineRestriction_homogeneous R i d hR)
  · intro hz
    rw [hz]
    simp [Nagata.W16.binaryAffine]
theorem exists_nonzero_affine_lineRestriction
    (k d : ℕ) (R : MvPolynomial (Fin 3) ℂ) (hR : R.IsHomogeneous d)
    (hnotdvd : ¬ homogeneousLineUnion ℂ k ∣ R) :
    ∃ i : Fin k, Nagata.W04.ReducibleSquare.lineRestriction (i.val : ℂ) R ≠ 0 := by
  obtain ⟨i, hi⟩ := exists_nonzero_homogeneousLineRestriction k R hnotdvd
  refine ⟨i, ?_⟩
  rw [← binaryAffine_homogeneousLineRestriction]
  exact Nagata.W16.binaryAffine_ne_zero
    (homogeneousLineRestriction_homogeneous R i.val d hR) hi
end Nagata.Workers.W24
end
end
section
namespace Nagata.Workers.W24
theorem bivariateToNested_directChart_line (i : ℕ) :
    Nagata.W18.bivariateToNested (Nagata.W27.directChartHom 2 (homogeneousLineEquation ℂ i)) =
      Polynomial.X - Polynomial.C (affineLineGraph ℂ i) := by
  simp [Nagata.W27.directChartHom, homogeneousLineEquation,
    Fin.insertNth_apply_below (show (0 : Fin 3) < 2 from by decide),
    Fin.insertNth_apply_below (show (1 : Fin 3) < 2 from by decide),
    Nagata.W18.bivariateToNested, affineLineGraph]
theorem bivariateToNested_directChart_union (k : ℕ) :
    Nagata.W18.bivariateToNested (Nagata.W27.directChartHom 2 (homogeneousLineUnion ℂ k)) =
      lineUnionEquation ℂ k := by
  simp only [homogeneousLineUnion, map_prod, bivariateToNested_directChart_line,
    lineUnionEquation]
theorem directChart_union_eq_nestedToBivariate (k : ℕ) :
    Nagata.W27.directChartHom 2 (homogeneousLineUnion ℂ k) =
      Nagata.W18.nestedToBivariate (lineUnionEquation ℂ k) := by
  have h := congrArg (Nagata.W18.nestedToBivariate (K := ℂ))
    (bivariateToNested_directChart_union k)
  have hinv := RingHom.congr_fun
    (Nagata.W18.nestedToBivariate_comp_bivariateToNested (K := ℂ))
    (Nagata.W27.directChartHom 2 (homogeneousLineUnion ℂ k))
  simp only [RingHom.comp_apply, RingHom.id_apply] at hinv
  change Nagata.W18.nestedToBivariate
    (Nagata.W18.bivariateToNested (Nagata.W27.directChartHom 2 (homogeneousLineUnion ℂ k))) = _ at h
  rw [hinv] at h
  exact h
end Nagata.Workers.W24
end
section
namespace Nagata.Workers.W24
open MvPolynomial
theorem planePolynomialEval_directChart (R : MvPolynomial (Fin 3) ℂ) (u y : ℂ) :
    Nagata.Workers.W28.planePolynomialEval (Nagata.W27.directChartHom 2 R) (u, y) =
      MvPolynomial.eval ![u, y, 1] R := by
  have h : (MvPolynomial.eval (fun j : Fin 2 => if j = 0 then u else y)).comp
      (Nagata.W27.directChartHom 2) = MvPolynomial.eval ![u, y, 1] := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [Nagata.W27.directChartHom]
    · intro j
      fin_cases j <;>
        simp [Nagata.W27.directChartHom,
          Fin.insertNth_apply_below (show (0 : Fin 3) < 2 from by decide),
          Fin.insertNth_apply_below (show (1 : Fin 3) < 2 from by decide)]
  exact RingHom.congr_fun h R
theorem planePolynomialEval_directChart_on_line
    (R : MvPolynomial (Fin 3) ℂ) (i u : ℂ) :
    Nagata.Workers.W28.planePolynomialEval (Nagata.W27.directChartHom 2 R)
      (u, i ^ 2 - i * u) =
        (Nagata.W04.ReducibleSquare.lineRestriction i R).eval u := by
  rw [planePolynomialEval_directChart, Nagata.W04.ReducibleSquare.lineRestriction_eval]
end Nagata.Workers.W24
end
end OAI
-- GraphOrder
namespace OAI
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators
theorem central_expression_analyticAt
    (I : Finset ℕ) (j : ℕ → ℕ) (R : ℕ → MvPolynomial (Fin 2) ℂ) (u : ℕ)
    (κ : ComplexPlane → ComplexPlane) (ξ c : ℂ)
    (hκ : AnalyticAt ℂ κ (ξ, 0)) :
    AnalyticAt ℂ
      (fun q : ComplexPlane => ∑ α ∈ I.filter (fun α => α + j α = u),
        q.2 ^ j α * planePolynomialEval (R α) (κ (q.1, 0))) (ξ, c) := by
  have hf := (ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt (ξ, c)
  have hw := (ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt (ξ, c)
  have harg : AnalyticAt ℂ (fun q : ComplexPlane => (q.1, (0 : ℂ))) (ξ, c) :=
    hf.prod analyticAt_const
  have hc := hκ.comp (f := fun q : ComplexPlane => (q.1, (0 : ℂ))) harg
  apply Finset.analyticAt_fun_sum
  intro α hα
  have hr : AnalyticAt ℂ (fun q : ComplexPlane => planePolynomialEval (R α) (κ (q.1, 0))) (ξ, c) :=
    AnalyticAt.comp (g := planePolynomialEval (R α))
      (f := fun q : ComplexPlane => κ (q.1, 0))
      (planePolynomialEval_analyticAt (R α) (κ (ξ, 0))) hc
  exact (hw.pow (j α)).mul hr
theorem graph_expression_order_of_central_jets
    (I : Finset ℕ) (j : ℕ → ℕ) (R : ℕ → MvPolynomial (Fin 2) ℂ) (u : ℕ)
    (G : MvPolynomial (Fin 2) ℂ)
    (e : OpenPartialHomeomorph ComplexPlane ComplexPlane)
    (he : (e : ComplexPlane → ComplexPlane) = polynomialNormalCoordinates G)
    (b : ℂ → ℂ) (ξ c : ℂ) (hb : ContinuousAt b ξ)
    (hsource : (ξ, b ξ) ∈ e.source)
    (hG : ∀ᶠ z in 𝓝 ξ, planePolynomialEval G (z, b z) = 0)
    (hi : AnalyticAt ℂ e.symm (ξ, 0)) (m : ℕ)
    (hjets : ∀ n < m, iteratedFDeriv ℂ n
      (fun q : ComplexPlane => ∑ α ∈ I.filter (fun α => α + j α = u),
        q.2 ^ j α * planePolynomialEval (R α) (e.symm (q.1, 0))) (ξ, c) = 0) :
    HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun q : ComplexPlane => ∑ α ∈ I.filter (fun α => α + j α = u),
        q.2 ^ j α * planePolynomialEval (R α) (q.1, b q.1)) (ξ, c) m := by
  have h := Nagata.Workers.W17.analytic_order_of_iteratedFDeriv_zero
    (central_expression_analyticAt I j R u e.symm ξ c hi) m hjets
  exact h.congr (central_expression_eq_graph_locally I j R u G e he b ξ c hb hsource hG)
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators
def selectedGraphPolynomial (I : Finset ℕ) (j : ℕ → ℕ)
    (B : ℕ → Polynomial ℂ) (u : ℕ) : Polynomial (Polynomial ℂ) :=
  ∑ α ∈ I.filter (fun α => α + j α = u), Polynomial.monomial (j α) (B α)
theorem eval_selectedGraphPolynomial
    (I : Finset ℕ) (j : ℕ → ℕ) (B : ℕ → Polynomial ℂ) (u : ℕ) (q : ComplexPlane) :
    ((selectedGraphPolynomial I j B u).eval (Polynomial.C q.2)).eval q.1 =
      ∑ α ∈ I.filter (fun α => α + j α = u), q.2 ^ j α * (B α).eval q.1 := by
  simp [selectedGraphPolynomial, Polynomial.eval_finsetSum, mul_comm]
theorem selectedGraphPolynomial_order_of_graph_order
    (I : Finset ℕ) (j : ℕ → ℕ) (R : ℕ → MvPolynomial (Fin 2) ℂ)
    (B : ℕ → Polynomial ℂ) (u : ℕ) (b : ℂ → ℂ) (ξ c : ℂ) (m : ℕ)
    (hR : ∀ α ∈ I.filter (fun α => α + j α = u), ∀ z : ℂ,
      planePolynomialEval (R α) (z, b z) = (B α).eval z)
    (horder : HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun q : ComplexPlane => ∑ α ∈ I.filter (fun α => α + j α = u),
        q.2 ^ j α * planePolynomialEval (R α) (q.1, b q.1)) (ξ, c) m) :
    selectedGraphPolynomial I j B u ∈ (Nagata.W18.nestedPointIdeal ξ c) ^ m := by
  apply Nagata.W18.nested_polynomial_ideal_order_of_analytic_order _ ξ c m
  apply horder.congr
  exact Filter.Eventually.of_forall fun q => by
    dsimp only
    rw [eval_selectedGraphPolynomial]
    apply Finset.sum_congr rfl
    intro α hα
    rw [hR α hα q.1]
theorem map_selected_monomial_sum
    {A : Type*} [CommRing A] (φ : A →+* Polynomial ℂ)
    (I : Finset ℕ) (j : ℕ → ℕ) (T : ℕ → A) (u : ℕ) :
    Polynomial.map φ
      (∑ α ∈ I.filter (fun α => α + j α = u), Polynomial.monomial (j α) (T α)) =
        selectedGraphPolynomial I j (fun α => φ (T α)) u := by
  simp [selectedGraphPolynomial, Polynomial.map_sum]
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators
theorem line_restricted_initial_order
    (I : Finset ℕ) (j : ℕ → ℕ) (T : ℕ → MvPolynomial (Fin 3) ℂ) (u : ℕ)
    (G : MvPolynomial (Fin 3) ℂ) (i ξ c : ℂ)
    (hline : Nagata.W04.ReducibleSquare.lineRestriction i G = 0)
    (e : OpenPartialHomeomorph ComplexPlane ComplexPlane)
    (he : (e : ComplexPlane → ComplexPlane) =
      polynomialNormalCoordinates (Nagata.W27.directChartHom (2 : Fin 3) G))
    (hsource : (ξ, i ^ 2 - i * ξ) ∈ e.source)
    (hi : AnalyticAt ℂ e.symm (ξ, 0)) (m : ℕ)
    (hjets : ∀ n < m, iteratedFDeriv ℂ n
      (fun q : ComplexPlane => ∑ α ∈ I.filter (fun α => α + j α = u),
        q.2 ^ j α * planePolynomialEval (Nagata.W27.directChartHom (2 : Fin 3) (T α))
          (e.symm (q.1, 0))) (ξ, c) = 0) :
    Polynomial.map (Nagata.W04.ReducibleSquare.lineRestriction i)
      (∑ α ∈ I.filter (fun α => α + j α = u), Polynomial.monomial (j α) (T α)) ∈
      (Nagata.W18.nestedPointIdeal ξ c) ^ m := by
  let R : ℕ → MvPolynomial (Fin 2) ℂ := fun α => Nagata.W27.directChartHom (2 : Fin 3) (T α)
  let b : ℂ → ℂ := fun z => i ^ 2 - i * z
  have hb : ContinuousAt b ξ :=
    (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt
  have hg : ∀ᶠ z in 𝓝 ξ,
      planePolynomialEval (Nagata.W27.directChartHom (2 : Fin 3) G) (z, b z) = 0 := by
    exact Filter.Eventually.of_forall fun z => by
      change planePolynomialEval (Nagata.W27.directChartHom (2 : Fin 3) G) (z, i ^ 2 - i * z) = 0
      rw [Nagata.Workers.W24.planePolynomialEval_directChart_on_line, hline]
      simp
  have horder := graph_expression_order_of_central_jets I j R u
    (Nagata.W27.directChartHom (2 : Fin 3) G) e he b ξ c hb hsource hg hi m hjets
  rw [map_selected_monomial_sum]
  apply selectedGraphPolynomial_order_of_graph_order I j R
    (fun α => Nagata.W04.ReducibleSquare.lineRestriction i (T α)) u b ξ c m _ horder
  intro α hα z
  exact Nagata.Workers.W24.planePolynomialEval_directChart_on_line (T α) i z
end Nagata.Workers.W28
end
end
end OAI
-- AssociatedBundles
namespace OAI
section
noncomputable section
namespace Nagata.W16.AssociatedBundle
open Nagata.ProjectiveGeometry
variable {n : ℕ} (G : NonzeroHomogeneousForm n)
structure BundleVector (k : ℕ) where
  x : Fin 3 → ℂ
  x_ne_zero : x ≠ 0
  on_curve : MvPolynomial.eval x G.polynomial = 0
  w : ℂ
variable {G}
def Equivalent {k : ℕ} (a b : BundleVector G k) : Prop :=
  ∃ u : ℂˣ, a.x = (u : ℂ) • b.x ∧ a.w = (u : ℂ) ^ k * b.w
theorem equivalent_refl {k : ℕ} (a : BundleVector G k) : Equivalent a a := by
  exact ⟨1, by simp, by simp⟩
theorem equivalent_symm {k : ℕ} {a b : BundleVector G k}
    (h : Equivalent a b) : Equivalent b a := by
  obtain ⟨u, hx, hw⟩ := h
  refine ⟨u⁻¹, ?_, ?_⟩
  · rw [hx, smul_smul]
    simp
  · rw [hw, ← mul_assoc, ← mul_pow]
    simp
theorem equivalent_trans {k : ℕ} {a b c : BundleVector G k}
    (hab : Equivalent a b) (hbc : Equivalent b c) : Equivalent a c := by
  obtain ⟨u, hux, huw⟩ := hab
  obtain ⟨v, hvx, hvw⟩ := hbc
  refine ⟨u * v, ?_, ?_⟩
  · rw [hux, hvx, smul_smul]
    rfl
  · rw [huw, hvw]
    simp [mul_pow, mul_assoc]
def bundleSetoid (G : NonzeroHomogeneousForm n) (k : ℕ) : Setoid (BundleVector G k) where
  r := Equivalent
  iseqv := ⟨equivalent_refl, equivalent_symm, equivalent_trans⟩
def TotalSpace (G : NonzeroHomogeneousForm n) (k : ℕ) := Quotient (bundleSetoid G k)
def mk {k : ℕ} (a : BundleVector G k) : TotalSpace G k := Quotient.mk _ a
theorem mk_eq_mk_iff {k : ℕ} (a b : BundleVector G k) : mk a = mk b ↔ Equivalent a b :=
  Quotient.eq
def base {k : ℕ} : TotalSpace G k → PlanePoint :=
  Quotient.lift (fun a => Projectivization.mk ℂ a.x a.x_ne_zero) (by
    intro a b h
    obtain ⟨u, hx, _⟩ := h
    exact (Projectivization.mk_eq_mk_iff ℂ a.x b.x a.x_ne_zero b.x_ne_zero).mpr
      ⟨u, by simpa [Units.smul_def] using hx.symm⟩)
open scoped BigOperators
end Nagata.W16.AssociatedBundle
end
end
end OAI
-- LineConfigurations
namespace OAI
section
noncomputable section
namespace Nagata.W06.LineArrangement
open scoped BigOperators
def markedCoordinate (k i : ℕ) (s : Fin k) : ℕ :=
  if s.val = 0 then Nagata.W04.ReducibleSquare.firstMark k i else s.val + 1
theorem markedCoordinate_pos (k i : ℕ) (s : Fin k) : 0 < markedCoordinate k i s := by
  unfold markedCoordinate
  split_ifs
  · exact Nagata.W04.ReducibleSquare.firstMark_pos k i
  · omega
theorem markedCoordinate_zero (k i : ℕ) (hk : 0 < k) :
    markedCoordinate k i ⟨0, hk⟩ = Nagata.W04.ReducibleSquare.firstMark k i := by
  simp [markedCoordinate]
theorem markedCoordinate_of_ne_zero (k i : ℕ) (s : Fin k) (hs : s.val ≠ 0) :
    markedCoordinate k i s = s.val + 1 := by
  simp [markedCoordinate, hs]
theorem markedCoordinate_injective (k i : ℕ) :
    Function.Injective (markedCoordinate k i) := by
  intro s t h
  apply Fin.ext
  dsimp [markedCoordinate, Nagata.W04.ReducibleSquare.firstMark] at h
  split_ifs at h <;> omega
variable {K : Type*} [Field K]
def graphValue (i : ℕ) (U : K) : K := (i : K) ^ 2 - (i : K) * U
def lineValue (i : ℕ) (U Y : K) : K := Y - graphValue i U
def markedPoint (K : Type*) [Field K] (k : ℕ) (i s : Fin k) : K × K :=
  let U : K := -(markedCoordinate k i.val s : K)
  (U, graphValue i.val U)
theorem graphValue_sub (i j : ℕ) (U : K) :
    graphValue i U - graphValue j U =
      ((i : K) - (j : K)) * ((i : K) + (j : K) - U) := by
  unfold graphValue
  ring
variable [CharZero K]
theorem negative_mark_avoids_other_line (i j v : ℕ) (hij : i ≠ j) (hv : 0 < v) :
    lineValue j (-(v : K)) (graphValue i (-(v : K))) ≠ 0 := by
  unfold lineValue
  rw [graphValue_sub, sub_neg_eq_add]
  apply mul_ne_zero
  · exact sub_ne_zero.mpr (by exact_mod_cast hij)
  · exact_mod_cast (show i + j + v ≠ 0 by omega)
omit [CharZero K] in
theorem markedPoint_on_line (k : ℕ) (i s : Fin k) :
    lineValue i.val (markedPoint K k i s).1 (markedPoint K k i s).2 = 0 := by
  simp [markedPoint, lineValue]
theorem markedPoint_avoids_other_line (k : ℕ) (i j s : Fin k) (hij : i ≠ j) :
    lineValue j.val (markedPoint K k i s).1 (markedPoint K k i s).2 ≠ 0 := by
  exact negative_mark_avoids_other_line i.val j.val (markedCoordinate k i.val s)
    (fun h => hij (Fin.ext h)) (markedCoordinate_pos k i.val s)
theorem markedPoint_injective (k : ℕ) :
    Function.Injective (fun p : Fin k × Fin k => markedPoint K k p.1 p.2) := by
  rintro ⟨i, s⟩ ⟨j, t⟩ h
  dsimp only at h
  have hij : i = j := by
    by_contra hij
    have hn := markedPoint_avoids_other_line (K := K) k i j s hij
    apply hn
    rw [h]
    exact markedPoint_on_line k j t
  apply Prod.ext hij
  have hU := congrArg Prod.fst h
  have hcoord : markedCoordinate k i.val s = markedCoordinate k j.val t := by
    exact Nat.cast_injective (neg_injective hU)
  rw [hij] at hcoord
  exact markedCoordinate_injective k j.val hcoord
end Nagata.W06.LineArrangement
end
end
section
noncomputable section
namespace Nagata.W06.LineArrangement
variable {K : Type*} [Field K] [CharZero K]
end Nagata.W06.LineArrangement
end
end
end OAI
-- LineSmoothness
namespace OAI
section
noncomputable section
namespace Nagata.W06.LineArrangement
open Polynomial
open scoped BigOperators
def planeEval {K : Type*} [CommRing K] (P : Polynomial (Polynomial K)) (U Y : K) : K :=
  P.eval₂ (Polynomial.evalRingHom U) Y
theorem derivative_prod_eval₂_root {A B ι : Type*} [CommRing A] [CommRing B]
    [Fintype ι] [DecidableEq ι] (f : A →+* B) (a : ι → A) (i : ι) :
    (∏ j : ι, (X - C (a j))).derivative.eval₂ f (f (a i)) =
      ∏ j ∈ Finset.univ.erase i, (f (a i) - f (a j)) := by
  rw [← Finset.mul_prod_erase Finset.univ (fun j => (X - C (a j))) (Finset.mem_univ i)]
  simp only [derivative_mul, derivative_X_sub_C, eval₂_add, eval₂_mul,
    eval₂_sub, eval₂_X, eval₂_C, sub_self, zero_mul, one_mul,
    add_zero, eval₂_finsetProd]
variable {K : Type*} [Field K]
@[simp] theorem eval_affineLineGraph (i : ℕ) (U : K) :
    (Nagata.Workers.W24.affineLineGraph K i).eval U = graphValue i U := by
  simp [Nagata.Workers.W24.affineLineGraph, graphValue]
variable [CharZero K]
theorem partialY_lineUnion_negative_mark (k : ℕ) (i : Fin k) (v : ℕ) (hv : 0 < v) :
    planeEval (Nagata.Workers.W24.lineUnionEquation K k).derivative
      (-(v : K)) (graphValue i.val (-(v : K))) ≠ 0 := by
  have hgraph : Polynomial.evalRingHom (-(v : K))
      (Nagata.Workers.W24.affineLineGraph K i.val) = graphValue i.val (-(v : K)) := by
    exact eval_affineLineGraph i.val _
  unfold planeEval Nagata.Workers.W24.lineUnionEquation
  rw [← hgraph]
  rw [derivative_prod_eval₂_root (Polynomial.evalRingHom (-(v : K)))
    (fun j : Fin k => Nagata.Workers.W24.affineLineGraph K j.val) i]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hij : i.val ≠ j.val := by
    intro h
    exact (Finset.mem_erase.mp hj).1 (Fin.ext h).symm
  change (Nagata.Workers.W24.affineLineGraph K i.val).eval (-(v : K)) -
    (Nagata.Workers.W24.affineLineGraph K j.val).eval (-(v : K)) ≠ 0
  rw [eval_affineLineGraph, eval_affineLineGraph]
  exact negative_mark_avoids_other_line (K := K) i.val j.val v hij hv
theorem partialY_lineUnion_at_mark (k : ℕ) (i s : Fin k) :
    planeEval (Nagata.Workers.W24.lineUnionEquation K k).derivative
      (markedPoint K k i s).1 (markedPoint K k i s).2 ≠ 0 := by
  exact partialY_lineUnion_negative_mark k i (markedCoordinate k i.val s)
    (markedCoordinate_pos k i.val s)
end Nagata.W06.LineArrangement
end
end
end OAI
-- NormalSpecialization
namespace OAI
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators
theorem exists_normal_specialization_from_partial
    (I : Finset ℕ) (j : ℕ → ℕ) (R : ℕ → MvPolynomial (Fin 2) ℂ)
    (u : ℕ) (hmin : ∀ α ∈ I, u ≤ α + j α)
    (G : MvPolynomial (Fin 2) ℂ) (p V : ComplexPlane)
    (hp : planePolynomialEval G p = 0)
    (hpartial : planePolynomialEval (MvPolynomial.pderiv 1 G) p ≠ 0)
    (exceptional : Finset ℂ) (m : ℕ)
    (horders : ∀ᶠ s : ℂ in 𝓝 0, s ∉ exceptional →
      Nagata.AffineMultiplicity.orderAtLeast
        (fun i : Fin 2 => if i = 0 then (p + s • V).1 else (p + s • V).2)
        m (factoredPlaneFamily I j R G s)) :
    ∃ e : OpenPartialHomeomorph ComplexPlane ComplexPlane,
      (e : ComplexPlane → ComplexPlane) = polynomialNormalCoordinates G ∧
      p ∈ e.source ∧ AnalyticAt ℂ e.symm (e p) ∧
      ∀ n < m, iteratedFDeriv ℂ n
        (fun q : ComplexPlane =>
          ∑ α ∈ I.filter (fun α => α + j α = u),
            q.2 ^ j α * planePolynomialEval (R α) (e.symm (q.1, 0)))
        (p.1, polynomialGradient G p V) = 0 := by
  obtain ⟨e, he, hsource, hi⟩ := exists_analytic_normal_chart_of_partial_ne_zero G p hpartial
  have hi' : AnalyticAt ℂ e.symm (e p) := by simpa only [he] using hi
  refine ⟨e, he, hsource, hi', ?_⟩
  exact normal_specialization_central_jets I j R u hmin G e he
    (polynomialGradient G p) p V hsource hi' (planePolynomialEval_hasFDerivAt G p)
    hp exceptional m horders
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators
theorem line_normal_specialization
    (I : Finset ℕ) (j : ℕ → ℕ) (T : ℕ → MvPolynomial (Fin 3) ℂ)
    (u : ℕ) (hmin : ∀ α ∈ I, u ≤ α + j α)
    (G : MvPolynomial (Fin 3) ℂ) (i ξ : ℂ) (V : ComplexPlane)
    (hline : Nagata.W04.ReducibleSquare.lineRestriction i G = 0)
    (hpartial : planePolynomialEval
      (MvPolynomial.pderiv 1 (Nagata.W27.directChartHom (2 : Fin 3) G))
      (ξ, i ^ 2 - i * ξ) ≠ 0)
    (exceptional : Finset ℂ) (m : ℕ)
    (horders : ∀ᶠ s : ℂ in 𝓝 0, s ∉ exceptional →
      Nagata.AffineMultiplicity.orderAtLeast
        (fun a : Fin 2 => if a = 0 then ((ξ, i ^ 2 - i * ξ) + s • V).1
          else ((ξ, i ^ 2 - i * ξ) + s • V).2)
        m (factoredPlaneFamily I j (fun α => Nagata.W27.directChartHom (2 : Fin 3) (T α))
          (Nagata.W27.directChartHom (2 : Fin 3) G) s)) :
    Polynomial.map (Nagata.W04.ReducibleSquare.lineRestriction i)
      (∑ α ∈ I.filter (fun α => α + j α = u), Polynomial.monomial (j α) (T α)) ∈
      (Nagata.W18.nestedPointIdeal ξ
        (polynomialGradient (Nagata.W27.directChartHom (2 : Fin 3) G)
          (ξ, i ^ 2 - i * ξ) V)) ^ m := by
  let p : ComplexPlane := (ξ, i ^ 2 - i * ξ)
  let A := Nagata.W27.directChartHom (2 : Fin 3) G
  let R : ℕ → MvPolynomial (Fin 2) ℂ := fun α => Nagata.W27.directChartHom (2 : Fin 3) (T α)
  have hp : planePolynomialEval A p = 0 := by
    dsimp [A, p]
    rw [Nagata.Workers.W24.planePolynomialEval_directChart_on_line, hline]
    simp
  obtain ⟨e, he, hs, hi, hjets⟩ := exists_normal_specialization_from_partial
    I j R u hmin A p V hp hpartial exceptional m horders
  have hi' : AnalyticAt ℂ e.symm (ξ, 0) := by
    have hep : e p = (ξ, (0 : ℂ)) := by
      rw [he]
      change (p.1, planePolynomialEval A p) = (ξ, 0)
      rw [hp]
    rwa [hep] at hi
  exact line_restricted_initial_order I j T u G i ξ
    (polynomialGradient A p V) hline e he hs hi' m hjets
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators
end Nagata.Workers.W28
end
end
end OAI
-- Interpolation
namespace OAI
section
noncomputable section
open scoped BigOperators
open Polynomial
namespace Nagata.W01.RowLagrange
variable {F : Type*} [Field F]
local instance : DecidableEq F := Classical.decEq F
end Nagata.W01.RowLagrange
end
end
section
noncomputable section
open scoped BigOperators
open Polynomial
namespace Nagata.W01
abbrev Plane := ℂ × ℂ
def monomial (b l : ℕ) : Plane → ℂ := fun z => z.1 ^ b * z.2 ^ l
def planeEval (p : MvPolynomial (Fin 2) ℂ) : Plane → ℂ :=
  fun z => MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z.1 else z.2) p
end Nagata.W01
end
end
end OAI
-- LineGeometry
namespace OAI
section
namespace Nagata.Workers.W14
end Nagata.Workers.W14
end
section
noncomputable section
namespace Nagata.Workers.W14
theorem exists_smul_of_all_minors_zero {K ι : Type*} [Field K]
    (u v : ι → K) (hv : v ≠ 0)
    (hminor : ∀ a b, u a * v b - u b * v a = 0) :
    ∃ c : K, c • v = u := by
  classical
  obtain ⟨b, hb⟩ : ∃ b, v b ≠ 0 := by
    by_contra hnone
    apply hv
    funext b
    exact Classical.not_not.mp (fun hb => hnone ⟨b, hb⟩)
  refine ⟨u b / v b, ?_⟩
  funext a
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [div_mul_eq_mul_div]
  exact (div_eq_iff hb).2 (sub_eq_zero.mp (hminor b a))
theorem minor_zero_of_smul {K ι : Type*} [Field K]
    (u v : ι → K) (c : K) (hc : c • v = u) (a b : ι) :
    u a * v b - u b * v a = 0 := by
  have ha : c * v a = u a := congrFun hc a
  have hb : c * v b = u b := congrFun hc b
  rw [← ha, ← hb]
  ring
end Nagata.Workers.W14
end
end
section
noncomputable section
namespace Nagata.Workers.W14
open scoped BigOperators
end Nagata.Workers.W14
end
end
section
noncomputable section
namespace Nagata.Workers.W14
theorem exists_minor_ne_zero_of_projective_ne {K ι : Type*} [Field K]
    (u v : ι → K) (hu : u ≠ 0) (hv : v ≠ 0)
    (h : Projectivization.mk K u hu ≠ Projectivization.mk K v hv) :
    ∃ a b, u a * v b - u b * v a ≠ 0 := by
  classical
  by_contra hn
  have hminor : ∀ a b, u a * v b - u b * v a = 0 := by
    intro a b
    exact Classical.not_not.mp (fun hh => hn ⟨a, b, hh⟩)
  apply h
  exact (Projectivization.mk_eq_mk_iff' K u v hu hv).2
    (exists_smul_of_all_minors_zero u v hv hminor)
theorem projective_ne_of_minor_ne_zero {K ι : Type*} [Field K]
    (u v : ι → K) (hu : u ≠ 0) (hv : v ≠ 0) (a b : ι)
    (hminor : u a * v b - u b * v a ≠ 0) :
    Projectivization.mk K u hu ≠ Projectivization.mk K v hv := by
  intro heq
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' K u v hu hv).1 heq
  exact hminor (minor_zero_of_smul u v c hc a b)
end Nagata.Workers.W14
end
end
section
noncomputable section
namespace Nagata.Workers.W14
end Nagata.Workers.W14
end
end
end OAI
-- MovingConfigurations
namespace OAI
section
noncomputable section
namespace Nagata.Workers.W14
theorem finite_polynomial_exceptions {K ι : Type*} [Field K] [Fintype ι]
    (P : ι → Polynomial K) (hP : ∀ i, (P i).eval 0 ≠ 0) :
    ∃ E : Finset K, 0 ∉ E ∧ ∀ s ∉ E, ∀ i, (P i).eval s ≠ 0 := by
  classical
  have hne : ∀ i, P i ≠ 0 := by
    intro i hi
    exact hP i (by simp [hi])
  let E : Finset K := Finset.univ.biUnion (fun i => (P i).roots.toFinset)
  have hmem : ∀ s, s ∈ E ↔ ∃ i, (P i).eval s = 0 := by
    intro s
    constructor
    · intro hs
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hs
      exact ⟨i, (Polynomial.mem_roots (hne i)).mp (Multiset.mem_toFinset.mp hi)⟩
    · rintro ⟨i, hi⟩
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
        Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (hne i)).mpr hi)⟩
  refine ⟨E, ?_, ?_⟩
  · intro hz
    obtain ⟨i, hi⟩ := (hmem 0).1 hz
    exact hP i hi
  · intro s hs i hi
    exact hs ((hmem s).2 ⟨i, hi⟩)
end Nagata.Workers.W14
end
end
section
noncomputable section
namespace Nagata.Workers.W14
def evaluateMotion {K : Type*} [Field K] {r n : ℕ}
    (P : Fin r → Fin n → Polynomial K) (s : K) (i : Fin r) : Fin n → K :=
  fun c => (P i c).eval s
theorem polynomial_motion_separated_cofinite {K : Type*} [Field K] {r n : ℕ}
    (P : Fin r → Fin n → Polynomial K)
    (hzero : ∀ i, evaluateMotion P 0 i ≠ 0)
    (hsep : ∀ i j, i ≠ j → ∃ a b,
      evaluateMotion P 0 i a * evaluateMotion P 0 j b -
        evaluateMotion P 0 i b * evaluateMotion P 0 j a ≠ 0) :
    ∃ E : Finset K, 0 ∉ E ∧
      (∀ s ∉ E, ∀ i, evaluateMotion P s i ≠ 0) ∧
      ∀ s ∉ E, ∀ i j, i ≠ j → ∃ a b,
        evaluateMotion P s i a * evaluateMotion P s j b -
          evaluateMotion P s i b * evaluateMotion P s j a ≠ 0 := by
  classical
  have hcoord : ∀ i, ∃ c, evaluateMotion P 0 i c ≠ 0 := by
    intro i
    by_contra hn
    apply hzero i
    funext c
    exact Classical.not_not.mp (fun hc => hn ⟨c, hc⟩)
  choose c hc using hcoord
  let Pairs := {z : Fin r × Fin r // z.1 ≠ z.2}
  have hpairs : ∀ z : Pairs, ∃ a b,
      evaluateMotion P 0 z.val.1 a * evaluateMotion P 0 z.val.2 b -
        evaluateMotion P 0 z.val.1 b * evaluateMotion P 0 z.val.2 a ≠ 0 :=
    fun z => hsep z.val.1 z.val.2 z.property
  choose a b hab using hpairs
  let tests : Fin r ⊕ Pairs → Polynomial K := Sum.elim
    (fun i => P i (c i))
    (fun z => P z.val.1 (a z) * P z.val.2 (b z) -
      P z.val.1 (b z) * P z.val.2 (a z))
  have htests : ∀ z, (tests z).eval 0 ≠ 0 := by
    intro z
    cases z with
    | inl i => exact hc i
    | inr z => simpa [tests, evaluateMotion] using hab z
  obtain ⟨E, hE0, hE⟩ := finite_polynomial_exceptions tests htests
  refine ⟨E, hE0, ?_, ?_⟩
  · intro s hs i hz
    apply hE s hs (Sum.inl i)
    exact congrFun hz (c i)
  · intro s hs i j hne
    let z : Pairs := ⟨(i, j), hne⟩
    refine ⟨a z, b z, ?_⟩
    simpa [tests, evaluateMotion, z] using hE s hs (Sum.inr z)
end Nagata.Workers.W14
end
end
section
noncomputable section
namespace Nagata.Workers.W14
theorem polynomial_projective_motion_cofinite {K : Type*} [Field K] {r n : ℕ}
    (P : Fin r → Fin n → Polynomial K)
    (hzero : ∀ i, evaluateMotion P 0 i ≠ 0)
    (hinj : Function.Injective
      (fun i => Projectivization.mk K (evaluateMotion P 0 i) (hzero i))) :
    ∃ E : Finset K, 0 ∉ E ∧
      ∃ hvalid : ∀ s ∉ E, ∀ i, evaluateMotion P s i ≠ 0,
        ∀ s (hs : s ∉ E), Function.Injective
          (fun i => Projectivization.mk K (evaluateMotion P s i) (hvalid s hs i)) := by
  have hsep : ∀ i j, i ≠ j → ∃ a b,
      evaluateMotion P 0 i a * evaluateMotion P 0 j b -
        evaluateMotion P 0 i b * evaluateMotion P 0 j a ≠ 0 := by
    intro i j hne
    exact exists_minor_ne_zero_of_projective_ne _ _ (hzero i) (hzero j)
      (fun he => hne (hinj he))
  obtain ⟨E, hE0, hvalid, hseparated⟩ :=
    polynomial_motion_separated_cofinite P hzero hsep
  refine ⟨E, hE0, hvalid, ?_⟩
  intro s hs i j hij
  by_contra hne
  obtain ⟨a, b, hm⟩ := hseparated s hs i j hne
  exact projective_ne_of_minor_ne_zero (evaluateMotion P s i)
    (evaluateMotion P s j) (hvalid s hs i) (hvalid s hs j) a b hm hij
end Nagata.Workers.W14
end
end
section
noncomputable section
namespace Nagata.Workers.W14
open scoped BigOperators
end Nagata.Workers.W14
end
end
section
noncomputable section
namespace Nagata.Workers.W14
open Nagata.ProjectiveGeometry
def chartPolynomialRepresentatives {r : ℕ} (c : Fin r → Fin 3)
    (p : Fin r × Fin 2 → Polynomial ℂ) : Fin r → Fin 3 → Polynomial ℂ :=
  fun i => (c i).insertNth 1 (fun j => p (i, j))
theorem evaluate_chartPolynomialRepresentatives {r : ℕ} (c : Fin r → Fin 3)
    (p : Fin r × Fin 2 → Polynomial ℂ) (s : ℂ) (i : Fin r) :
    evaluateMotion (chartPolynomialRepresentatives c p) s i =
      chartVector₂ (c i) (fun j => (p (i, j)).eval s) := by
  funext j
  by_cases hj : j = c i
  · subst j
    simp [evaluateMotion, chartPolynomialRepresentatives, chartVector₂]
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    simp [evaluateMotion, chartPolynomialRepresentatives, chartVector₂]
theorem chart_polynomial_motion_cofinite {r : ℕ} (c : Fin r → Fin 3)
    (p : Fin r × Fin 2 → Polynomial ℂ)
    (hbase : Function.Injective
      (configurationChartEmbedding c (fun ij => (p ij).eval 0))) :
    ∃ E : Finset ℂ, 0 ∉ E ∧ ∀ s ∉ E, Function.Injective
      (configurationChartEmbedding c (fun ij => (p ij).eval s)) := by
  let P := chartPolynomialRepresentatives c p
  have hzero : ∀ i, evaluateMotion P 0 i ≠ 0 := by
    intro i
    rw [evaluate_chartPolynomialRepresentatives]
    exact chartVector₂_ne_zero _ _
  have hinj : Function.Injective
      (fun i => Projectivization.mk ℂ (evaluateMotion P 0 i) (hzero i)) := by
    unfold configurationChartEmbedding chartPoint₂ at hbase
    simpa only [P, evaluate_chartPolynomialRepresentatives] using hbase
  obtain ⟨E, hE0, hvalid, hdistinct⟩ := polynomial_projective_motion_cofinite P hzero hinj
  refine ⟨E, hE0, ?_⟩
  intro s hs
  unfold configurationChartEmbedding chartPoint₂
  simpa only [P, evaluate_chartPolynomialRepresentatives] using hdistinct s hs
theorem order_directChart_of_multiplicity {F : MvPolynomial (Fin 3) ℂ}
    (c : Fin 3) (z : Fin 2 → ℂ) (m : ℕ)
    (h : multiplicityAtLeast F (chartPoint₂ c z) m) :
    Nagata.AffineMultiplicity.orderAtLeast z m (Nagata.W27.directChartHom c F) := by
  have hchart := h c (chartPoint₂_coordinate_ne_zero c z)
  have htwo := (orderAtLeast_chartDehomogenize₂_iff c (chartPoint₂ c z) F m).2 hchart
  rw [chartCoordinates₂_chartPoint₂, chartDehomogenize₂_eq_eval₂_insertNth] at htwo
  exact htwo
end Nagata.Workers.W14
end
end
section
noncomputable section
namespace Nagata.Workers.W14
open Module
open scoped BigOperators
end Nagata.Workers.W14
end
end
end OAI
-- UniversalFamilies
namespace OAI
section
noncomputable section
namespace Nagata.Workers.W14
def parameterMatrix {K σ ρ κ : Type*} [CommRing K]
    (A : Matrix ρ κ (MvPolynomial σ K)) (p : σ → Polynomial K) :
    Matrix ρ κ (Polynomial K) :=
  fun row col => MvPolynomial.eval₂ Polynomial.C p (A row col)
theorem specialize_parameterMatrix {K σ ρ κ : Type*} [CommRing K]
    (A : Matrix ρ κ (MvPolynomial σ K)) (p : σ → Polynomial K) (s : K) :
    (parameterMatrix A p).map (Polynomial.evalRingHom s) =
      A.map (MvPolynomial.eval (fun j => (p j).eval s)) := by
  have hc : (Polynomial.evalRingHom s).comp (Polynomial.C : K →+* Polynomial K) =
      RingHom.id K := by
    ext x
    simp
  funext row col
  change (Polynomial.evalRingHom s)
      (MvPolynomial.eval₂Hom Polynomial.C p (A row col)) = _
  rw [MvPolynomial.map_eval₂Hom, hc]
  rfl
theorem parameterMatrix_mulVec {K σ ρ κ : Type*} [CommRing K] [Fintype κ]
    (A : Matrix ρ κ (MvPolynomial σ K)) (p : σ → Polynomial K)
    (s : K) (v : κ → K) :
    ((parameterMatrix A p).map (Polynomial.evalRingHom s)).mulVec v =
      Nagata.W27.coefficientLinearMap A (fun j => (p j).eval s) v := by
  rw [specialize_parameterMatrix]
  rfl
theorem normalized_kernel_of_parameter_equations
    {K σ ρ κ : Type*} [Field K] [Infinite K]
    [Fintype κ] [Fintype ρ] [DecidableEq κ] [DecidableEq ρ]
    (A : Matrix ρ κ (MvPolynomial σ K)) (p : σ → Polynomial K) (E : Finset K)
    (hkernel : ∀ s ∉ E, ∃ v : κ → K, v ≠ 0 ∧
      Nagata.W27.coefficientLinearMap A (fun j => (p j).eval s) v = 0) :
    ∃ q : κ → Polynomial K, (∃ i, (q i).coeff 0 ≠ 0) ∧
      (parameterMatrix A p).mulVec q = 0 := by
  apply Nagata.W18.normalized_kernel_of_general_specialized_kernel (parameterMatrix A p) E
  intro s hs
  obtain ⟨v, hv, heq⟩ := hkernel s hs
  exact ⟨v, hv, by rw [parameterMatrix_mulVec]; exact heq⟩
end Nagata.Workers.W14
end
end
section
noncomputable section
namespace Nagata.Workers.W14
open Nagata.ProjectiveGeometry
theorem universalSupport_general_chart_kernels {r d : ℕ} {m : Fin r → ℕ}
    (hU : Nagata.W13.UniversalSupport r d m)
    (c : Fin r → Fin 3) (p : Fin r × Fin 2 → Polynomial ℂ)
    (hbase : Function.Injective
      (configurationChartEmbedding c (fun ij => (p ij).eval 0))) :
    ∃ E : Finset ℂ, 0 ∉ E ∧ ∀ s ∉ E,
      ∃ v : Nagata.W27.HomogeneousMonomial d → ℂ, v ≠ 0 ∧
        Nagata.W27.coefficientLinearMap (Nagata.W27.chartPlaneJetMatrix c d m)
          (fun ij => (p ij).eval s) v = 0 := by
  obtain ⟨E, hE0, hE⟩ := chart_polynomial_motion_cofinite c p hbase
  refine ⟨E, hE0, ?_⟩
  intro s hs
  obtain ⟨F, hF, hhom, hmult⟩ := hU
    ⟨configurationChartEmbedding c (fun ij => (p ij).eval s), hE s hs⟩
  apply (Nagata.W27.exists_nonzero_form_iff_chart_kernel c d m
    (fun ij => (p ij).eval s)).1
  refine ⟨⟨F, hhom⟩, hF, ?_⟩
  intro i
  exact order_directChart_of_multiplicity (c i) (fun j => (p (i, j)).eval s) (m i) (hmult i)
theorem universalSupport_normalized_parameter_family {r d : ℕ} {m : Fin r → ℕ}
    (hU : Nagata.W13.UniversalSupport r d m)
    (c : Fin r → Fin 3) (p : Fin r × Fin 2 → Polynomial ℂ)
    (hbase : Function.Injective
      (configurationChartEmbedding c (fun ij => (p ij).eval 0))) :
    ∃ q : Nagata.W27.HomogeneousMonomial d → Polynomial ℂ,
      (∃ i, (q i).coeff 0 ≠ 0) ∧
      (parameterMatrix (Nagata.W27.chartPlaneJetMatrix c d m) p).mulVec q = 0 := by
  classical
  obtain ⟨E, _, hE⟩ := universalSupport_general_chart_kernels hU c p hbase
  exact normalized_kernel_of_parameter_equations
    (Nagata.W27.chartPlaneJetMatrix c d m) p E hE
end Nagata.Workers.W14
end
end
section
noncomputable section
namespace Nagata.Workers.W14
open Nagata.ProjectiveGeometry
end Nagata.Workers.W14
end
end
end OAI
-- CoverNormal
namespace OAI
section
namespace Nagata.Workers.W17
open Nagata.W27 Nagata.Workers.W14 Nagata.ProjectiveGeometry
theorem indexedPlaneFamily_chart_orders {r d : ℕ} (m : Fin r → ℕ)
    (c : Fin r → Fin 3) (p : Fin r × Fin 2 → Polynomial ℂ)
    (q : HomogeneousMonomial d → Polynomial ℂ)
    (hq : (parameterMatrix (chartPlaneJetMatrix c d m) p).mulVec q = 0)
    (s : ℂ) :
    ∀ i, Nagata.AffineMultiplicity.orderAtLeast (fun j => (p (i,j)).eval s) (m i)
      (directChartHom (c i) ((indexedPlaneFamily d q).eval (MvPolynomial.C s))) := by
  have hspec := Nagata.W18.specialize_polynomial_kernel
    (parameterMatrix (chartPlaneJetMatrix c d m) p) q hq s
  rw [parameterMatrix_mulVec] at hspec
  let F := (homogeneousCoordinates (R := ℂ) d).symm (fun ν => (q ν).eval s)
  have hcoord : homogeneousCoordinates d F = fun ν => (q ν).eval s :=
    (homogeneousCoordinates d).apply_symm_apply _
  have horders := (chart_orders_iff_kernel c d m (fun ij => (p ij).eval s) F).mpr
    (by rw [hcoord]; exact hspec)
  simpa only [eval_indexedPlaneFamily_eq_coordinates_symm, F] using horders
theorem universalSupport_polynomial_family {r d : ℕ} {m : Fin r → ℕ}
    (hU : Nagata.W13.UniversalSupport r d m)
    (c : Fin r → Fin 3) (p : Fin r × Fin 2 → Polynomial ℂ)
    (hbase : Function.Injective
      (configurationChartEmbedding c (fun ij => (p ij).eval 0))) :
    ∃ S : Polynomial (MvPolynomial (Fin 3) ℂ),
      S.coeff 0 ≠ 0 ∧ (∀ α, (S.coeff α).IsHomogeneous d) ∧
      ∀ s i, Nagata.AffineMultiplicity.orderAtLeast (fun j => (p (i,j)).eval s) (m i)
        (directChartHom (c i) (S.eval (MvPolynomial.C s))) := by
  obtain ⟨q, hzero, hq⟩ := universalSupport_normalized_parameter_family hU c p hbase
  exact ⟨indexedPlaneFamily d q, indexedPlaneFamily_constant_ne_zero d q hzero,
    indexedPlaneFamily_homogeneous d q, indexedPlaneFamily_chart_orders m c p q hq⟩
end Nagata.Workers.W17
end
section
namespace Nagata.Workers.W17
open scoped BigOperators
open Nagata.ProjectiveGeometry
theorem universalSupport_degree_bounded_normal_data {r d : ℕ} {m : Fin r → ℕ}
    (hU : Nagata.W13.UniversalSupport r d m)
    (c : Fin r → Fin 3) (p : Fin r × Fin 2 → Polynomial ℂ)
    (hbase : Function.Injective
      (configurationChartEmbedding c (fun ij => (p ij).eval 0)))
    (G : MvPolynomial (Fin 3) ℂ) (k : ℕ)
    (hG : G.IsHomogeneous k) (hunit : ¬IsUnit G) (hk : 0 < k) :
    ∃ (I : Finset ℕ) (j : ℕ → ℕ) (T : ℕ → MvPolynomial (Fin 3) ℂ) (u : ℕ),
      (∀ α ∈ I, ¬G ∣ T α) ∧
      (∀ α ∈ I, j α ≤ d / k ∧ (T α).IsHomogeneous (d - k * j α)) ∧
      (∀ α ∈ I, u ≤ α + j α) ∧ u ≤ d / k ∧
      (I.filter (fun α => α + j α = u)).Nonempty ∧
      ((liftedNormalPolynomial (I.filter (fun α => α + j α = u)) j T).map
        (Ideal.Quotient.mk (Ideal.span ({G} : Set (MvPolynomial (Fin 3) ℂ))))) ≠ 0 ∧
      ∀ s i, Nagata.AffineMultiplicity.orderAtLeast (fun z => (p (i,z)).eval s) (m i)
        (Nagata.Workers.W28.factoredPlaneFamily I j
          (fun α => Nagata.W27.directChartHom (c i) (T α))
          (Nagata.W27.directChartHom (c i) G) s) := by
  classical
  obtain ⟨S, hzero, hcoeff, horders⟩ := universalSupport_polynomial_family hU c p hbase
  obtain ⟨j, T, u, hfactor, hnot, hdeg, hmin, hu, hsel, hinit⟩ :=
    exists_degree_bounded_plane_initial S G d k hcoeff hG hunit hk hzero
  refine ⟨S.support, j, T, u, hnot, hdeg, hmin, hu, hsel, ?_, ?_⟩
  · simpa only [map_liftedNormalPolynomial] using hinit
  · intro s i
    rw [← directChart_factored_family S G j T hfactor (c i) s]
    exact horders s i
end Nagata.Workers.W17
end
section
noncomputable section
namespace Nagata.Workers.W17
open Nagata.Workers.W28 Nagata.ProjectiveGeometry
end Nagata.Workers.W17
end
end
section
noncomputable section
namespace Nagata.Workers.W17
open scoped Topology BigOperators
open Nagata.ProjectiveGeometry Nagata.Workers.W28
theorem universalSupport_selected_line_data {r d : ℕ} {m : Fin r → ℕ}
    (hU : Nagata.W13.UniversalSupport r d m)
    (G : MvPolynomial (Fin 3) ℂ) (k : ℕ)
    (hG : G.IsHomogeneous k) (hk : 0 < k)
    (line ξ displacement : Fin r → ℂ)
    (hbase : Function.Injective (fun b : Fin r => (ξ b, (line b)^2 - line b * ξ b)))
    (hline : ∀ b, Nagata.W04.ReducibleSquare.lineRestriction (line b) G = 0)
    (hpartial : ∀ b, planePolynomialEval
      (MvPolynomial.pderiv 1 (Nagata.W27.directChartHom (2 : Fin 3) G))
      (ξ b, (line b)^2 - line b * ξ b) ≠ 0) :
    ∃ (indices : Finset ℕ) (j : ℕ → ℕ) (T : ℕ → MvPolynomial (Fin 3) ℂ) (u : ℕ),
      indices.Nonempty ∧ (∀ α ∈ indices, α + j α = u) ∧
      (∀ α ∈ indices, ¬G ∣ T α) ∧
      (∀ α ∈ indices, j α ≤ d / k) ∧
      (∀ α ∈ indices, (T α).IsHomogeneous (d - k * j α)) ∧
      ∀ b, (liftedNormalPolynomial indices j T).map
          (Nagata.W04.ReducibleSquare.lineRestriction (line b)) ∈
        (Nagata.W18.nestedPointIdeal (ξ b) (displacement b)) ^ (m b) := by
  classical
  let A := Nagata.W27.directChartHom (2 : Fin 3) G
  let point : Fin r → ComplexPlane := fun b => (ξ b, (line b)^2 - line b * ξ b)
  let normal : Fin r → ℂ := fun b => planePolynomialEval (MvPolynomial.pderiv 1 A) (point b)
  let V : Fin r → ComplexPlane := fun b => (0, displacement b / normal b)
  let coord : ComplexPlane → Fin 2 → ℂ := fun z a => if a = 0 then z.1 else z.2
  let motion : Fin r × Fin 2 → Polynomial ℂ := fun ba =>
    Polynomial.C (coord (point ba.1) ba.2) +
      Polynomial.X * Polynomial.C (coord (V ba.1) ba.2)
  have hmotion : ∀ b a s, (motion (b,a)).eval s = coord (point b + s • V b) a := by
    intro b a s
    simp only [motion, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X]
    dsimp only [coord]
    split_ifs <;> simp
  have hbase' : Function.Injective
      (configurationChartEmbedding (fun _ : Fin r => (2 : Fin 3))
        (fun ba => (motion ba).eval 0)) := by
    intro b b' heq
    have heq' : coord (point b) = coord (point b') := by
      apply chartPoint₂_injective (2 : Fin 3)
      simpa only [configurationChartEmbedding, hmotion, zero_smul, add_zero] using heq
    apply hbase
    apply Prod.ext
    · have hh := congrFun heq' (0 : Fin 2)
      simpa only [coord, if_pos rfl] using hh
    · have hh := congrFun heq' (1 : Fin 2)
      simpa only [coord, if_neg (show (1 : Fin 2) ≠ 0 by decide)] using hh
  obtain ⟨I, j, T, u, hnot, hdeg, hmin, hu, hsel, hnonzero, horders⟩ :=
    universalSupport_degree_bounded_normal_data hU (fun _ => 2) motion hbase'
      G k hG (positive_homogeneous_not_isUnit hG hk) hk
  let selected := I.filter (fun α => α + j α = u)
  refine ⟨selected, j, T, u, hsel, ?_, ?_, ?_, ?_, ?_⟩
  · intro α hα
    exact (Finset.mem_filter.mp hα).2
  · intro α hα
    exact hnot α (Finset.mem_filter.mp hα).1
  · intro α hα
    exact (hdeg α (Finset.mem_filter.mp hα).1).1
  · intro α hα
    exact (hdeg α (Finset.mem_filter.mp hα).1).2
  · intro b
    have hv : polynomialGradient A (point b) (V b) = displacement b := by
      have hn : normal b ≠ 0 := hpartial b
      change planePolynomialEval (MvPolynomial.pderiv 0 A) (point b) * 0 +
        normal b * (displacement b / normal b) = displacement b
      rw [mul_zero, zero_add]
      exact mul_div_cancel₀ (displacement b) hn
    have ho : ∀ᶠ s : ℂ in 𝓝 0, s ∉ (∅ : Finset ℂ) →
        Nagata.AffineMultiplicity.orderAtLeast (coord (point b + s • V b)) (m b)
          (factoredPlaneFamily I j (fun α => Nagata.W27.directChartHom 2 (T α)) A s) := by
      exact Filter.Eventually.of_forall fun s _ => by
        simpa only [hmotion] using horders s b
    have h := line_normal_specialization I j T u hmin G (line b) (ξ b) (V b)
      (hline b) (hpartial b) ∅ (m b) ho
    change (liftedNormalPolynomial selected j T).map _ ∈
      (Nagata.W18.nestedPointIdeal (ξ b) (polynomialGradient A (point b) (V b))) ^ (m b) at h
    rwa [hv] at h
end Nagata.Workers.W17
end
end
section
noncomputable section
namespace Nagata.Workers.W17
open scoped Topology BigOperators
open Nagata.Workers.W28 Nagata.ProjectiveGeometry
end Nagata.Workers.W17
end
end
section
namespace Nagata.Workers.W17
open Nagata.Workers.W28
theorem universalSupport_line_normal_polynomial {r d : ℕ} {m : Fin r → ℕ}
    (hU : Nagata.W13.UniversalSupport r d m)
    (G : MvPolynomial (Fin 3) ℂ) (k : ℕ)
    (hG : G.IsHomogeneous k) (hk : 0 < k)
    (line ξ displacement : Fin r → ℂ)
    (hbase : Function.Injective (fun b : Fin r => (ξ b, (line b)^2 - line b * ξ b)))
    (hline : ∀ b, Nagata.W04.ReducibleSquare.lineRestriction (line b) G = 0)
    (hpartial : ∀ b, planePolynomialEval
      (MvPolynomial.pderiv 1 (Nagata.W27.directChartHom (2 : Fin 3) G))
      (ξ b, (line b)^2 - line b * ξ b) ≠ 0) :
    ∃ F : Polynomial (MvPolynomial (Fin 3) ℂ),
      (∀ n, (F.coeff n).IsHomogeneous (d - k*n)) ∧
      (∀ n, F.coeff n ≠ 0 → k*n ≤ d) ∧
      F.map (Ideal.Quotient.mk (Ideal.span ({G} : Set (MvPolynomial (Fin 3) ℂ)))) ≠ 0 ∧
      ∀ b, F.map (Nagata.W04.ReducibleSquare.lineRestriction (line b)) ∈
        (Nagata.W18.nestedPointIdeal (ξ b) (displacement b)) ^ (m b) := by
  obtain ⟨I, j, T, u, hne, hweight, hnot, hbound, hhom, horder⟩ :=
    universalSupport_selected_line_data hU G k hG hk line ξ displacement hbase hline hpartial
  refine ⟨liftedNormalPolynomial I j T,
    homogeneous_coeff_liftedNormalPolynomial I j T d k hhom, ?_,
    quotient_liftedNormalPolynomial_ne_zero I j T G u hne hweight hnot, horder⟩
  intro n hn
  have hb := nonzero_coeff_liftedNormalPolynomial_bound I j T (d/k) n hbound hn
  have hh := (Nat.le_div_iff_mul_le hk).mp hb
  simpa only [Nat.mul_comm] using hh
end Nagata.Workers.W17
end
section
noncomputable section
namespace Nagata.Workers.W17
open scoped Topology BigOperators
open Nagata.Workers.W28 Nagata.ProjectiveGeometry
end Nagata.Workers.W17
end
end
end OAI
-- SquareNormal
namespace OAI
section
noncomputable section
namespace Nagata.Workers.W24
theorem exists_displacement_outside_homogeneousEvaluation {ι : Type*} [Fintype ι]
    (k : ℕ) (hk : 4 ≤ k) (hcard : Fintype.card ι = k * k)
    (a : ι → Fin 3 → ℂ) :
    ∃ c : ι → ℂ, c ∉ (homogeneousEvaluation k a).range := by
  apply exists_vector_outside_range
  change Module.finrank ℂ (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ k) <
    Module.finrank ℂ (ι → ℂ)
  rw [Nagata.W02.finrank_homogeneousSubmodule,
    Module.finrank_fintype_fun_eq_card, hcard]
  exact ambientDegreeK_dimension_lt k hk
theorem exists_grid_displacement (k : ℕ) (hk : 4 ≤ k)
    (a : Fin k × Fin k → Fin 3 → ℂ) :
    ∃ c : Fin k × Fin k → ℂ, c ∉ (homogeneousEvaluation k a).range := by
  apply exists_displacement_outside_homogeneousEvaluation k hk
  simp
end Nagata.Workers.W24
end
end
section
noncomputable section
namespace Nagata.Workers.W24
open Polynomial
open Nagata.W04.ReducibleSquare Nagata.W18
theorem normal_top_coefficients_zero {K : Type*} [Field K] [CharZero K]
    (k m J : ℕ) (hk : 3 ≤ k) (hJm : J < m)
    (H : ℕ → Polynomial (Polynomial K))
    (cFirst : ℕ → K) (cTail : ℕ → ℕ → K)
    (hdegree : ∀ i < k, (H i).natDegree ≤ J)
    (hbase : ∀ i < k, ((H i).coeff J).natDegree ≤ k * (m - J))
    (hfirst : ∀ i < k, H i ∈
      (nestedPointIdeal (-((firstMark k i : ℕ) : K)) (cFirst i)) ^ m)
    (htail : ∀ i < k, ∀ s < k - 1, H i ∈
      (nestedPointIdeal (-((s + 2 : ℕ) : K)) (cTail i s)) ^ m)
    (hglue : ∀ i < k, ∀ j < k,
      ((H i).coeff J).eval ((i + j : ℕ) : K) =
      ((H j).coeff J).eval ((i + j : ℕ) : K)) :
    ∀ i < k, (H i).coeff J = 0 := by
  apply line_family_zero_of_marked_factors k (m - J) hk (by omega)
    (fun i => (H i).coeff J) hbase
  · intro i hi
    simpa only [map_neg, sub_neg_eq_add] using
      top_coefficient_base_divisibility (H i) (-((firstMark k i : ℕ) : K))
        (cFirst i) m J (hdegree i hi) (hfirst i hi)
  · intro i hi s hs
    simpa only [map_neg, sub_neg_eq_add] using
      top_coefficient_base_divisibility (H i) (-((s + 2 : ℕ) : K))
        (cTail i s) m J (hdegree i hi) (htail i hi s hs)
  · exact hglue
theorem normal_top_index_eq_and_degree_eq {K : Type*} [Field K] [CharZero K]
    (k d m J : ℕ) (hk : 3 ≤ k) (hd : d ≤ k * m) (hweight : k * J ≤ d)
    (H : ℕ → Polynomial (Polynomial K))
    (cFirst : ℕ → K) (cTail : ℕ → ℕ → K)
    (hdegree : ∀ i < k, (H i).natDegree ≤ J)
    (hbase : ∀ i < k, ((H i).coeff J).natDegree ≤ d - k * J)
    (hfirst : ∀ i < k, H i ∈
      (nestedPointIdeal (-((firstMark k i : ℕ) : K)) (cFirst i)) ^ m)
    (htail : ∀ i < k, ∀ s < k - 1, H i ∈
      (nestedPointIdeal (-((s + 2 : ℕ) : K)) (cTail i s)) ^ m)
    (hglue : ∀ i < k, ∀ j < k,
      ((H i).coeff J).eval ((i + j : ℕ) : K) =
      ((H j).coeff J).eval ((i + j : ℕ) : K))
    (hne : ∃ i < k, (H i).coeff J ≠ 0) : J = m ∧ d = k * m := by
  have hle : J ≤ m := leadingIndex_le_m k d m J (by omega) hweight hd
  have hnot : ¬ J < m := by
    intro hlt
    have hz := normal_top_coefficients_zero k m J hk hlt H cFirst cTail hdegree
      (fun i hi => (hbase i hi).trans (by
        simpa only [Nat.mul_sub_left_distrib] using Nat.sub_le_sub_right hd (k * J)))
      hfirst htail hglue
    obtain ⟨i, hi, hni⟩ := hne
    exact hni (hz i hi)
  have heq : J = m := by omega
  exact ⟨heq, Nat.le_antisymm hd (by simpa only [heq] using hweight)⟩
end Nagata.Workers.W24
end
end
section
namespace Nagata.Workers.W24
open Polynomial Nagata.W18
theorem normal_evaluation_contradiction {K V ι : Type*} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V]
    (E : V →ₗ[K] (ι → K)) (c : ι → K) (hc : c ∉ E.range)
    (m : ℕ) (hm : 0 < m) (a : K) (ha : a ≠ 0)
    (H : ι → Polynomial (Polynomial K)) (base : ι → K)
    (hdegree : ∀ i, (H i).natDegree ≤ m)
    (horder : ∀ i, H i ∈ (nestedPointIdeal (base i) (c i)) ^ m)
    (htop : ∀ i, ((H i).coeff m).eval (base i) = a)
    (s : V) (hprevious : ∀ i, E s i = ((H i).coeff (m - 1)).eval (base i)) :
    False := by
  apply evaluation_coefficient_contradiction E c hc (-(m : K) * a)
    (mul_ne_zero (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))) ha) s
  funext i
  change E s i = (-(m : K) * a) * c i
  rw [hprevious i]
  have h := surface_order_penultimate_coefficient (H i) (base i) (c i) m hm
    (hdegree i) (horder i) (by rw [htop i]; exact ha)
  simpa only [htop i] using h
end Nagata.Workers.W24
end
section
noncomputable section
namespace Nagata.Workers.W24
open Polynomial Nagata.W18
open Nagata.W04.ReducibleSquare
def planeNormalOnLine (F : Polynomial (MvPolynomial (Fin 3) ℂ)) (i : ℕ) :
    Polynomial (Polynomial ℂ) := F.map (Nagata.W04.ReducibleSquare.lineRestriction (i : ℂ))
@[simp] theorem planeNormalOnLine_coeff (F : Polynomial (MvPolynomial (Fin 3) ℂ))
    (i j : ℕ) : (planeNormalOnLine F i).coeff j =
      Nagata.W04.ReducibleSquare.lineRestriction (i : ℂ) (F.coeff j) :=
  Polynomial.coeff_map _ _
theorem lineRestriction_union_zero (k : ℕ) (i : Fin k) :
    Nagata.W04.ReducibleSquare.lineRestriction (i.val : ℂ) (homogeneousLineUnion ℂ k) = 0 := by
  apply (affine_lineRestriction_eq_zero_iff _ i.val k (homogeneousLineUnion_homogeneous k)).mpr
  exact (homogeneousUnion_dvd_iff_restrictions_zero k _).mp dvd_rfl i
theorem plane_normal_top_index_eq_and_degree_eq
    (k d m : ℕ) (hk : 3 ≤ k) (hd : d ≤ k * m)
    (F : Polynomial (MvPolynomial (Fin 3) ℂ))
    (hhom : ∀ j, (F.coeff j).IsHomogeneous (d - k * j))
    (hweight : ∀ j, F.coeff j ≠ 0 → k * j ≤ d)
    (hne : normalResiduePolynomial (homogeneousLineUnion ℂ k) F ≠ 0)
    (cFirst : ℕ → ℂ) (cTail : ℕ → ℕ → ℂ)
    (hfirst : ∀ i < k, planeNormalOnLine F i ∈
      (nestedPointIdeal (-((firstMark k i : ℕ) : ℂ)) (cFirst i)) ^ m)
    (htail : ∀ i < k, ∀ s < k - 1, planeNormalOnLine F i ∈
      (nestedPointIdeal (-((s + 2 : ℕ) : ℂ)) (cTail i s)) ^ m) :
    (normalResiduePolynomial (homogeneousLineUnion ℂ k) F).natDegree = m ∧ d = k * m := by
  let J := (normalResiduePolynomial (homogeneousLineUnion ℂ k) F).natDegree
  have hnot : ¬ homogeneousLineUnion ℂ k ∣ F.coeff J :=
    top_normalResidue_coefficient_not_dvd _ _ hne
  have hcoeff : F.coeff J ≠ 0 := by
    intro hz
    exact hnot (hz ▸ dvd_zero _)
  apply normal_top_index_eq_and_degree_eq k d m J hk hd (hweight J hcoeff)
    (planeNormalOnLine F) cFirst cTail
  · intro i hi
    exact restriction_natDegree_le_normalResidue_degree _ F _
      (lineRestriction_union_zero k ⟨i, hi⟩)
  · intro i hi
    rw [planeNormalOnLine_coeff]
    exact Nagata.W02.lineRestriction_natDegree_le (i : ℂ) (F.coeff J) (d - k * J) (hhom J)
  · exact hfirst
  · exact htail
  · intro i hi j hj
    simp only [planeNormalOnLine_coeff]
    simpa only [Nat.cast_add] using lineRestriction_node_gluing (F.coeff J) (i : ℂ) (j : ℂ)
  · obtain ⟨i, hi⟩ := exists_nonzero_affine_lineRestriction k (d - k * J)
      (F.coeff J) (hhom J) hnot
    exact ⟨i.val, i.isLt, by simpa only [planeNormalOnLine_coeff] using hi⟩
end Nagata.Workers.W24
end
end
section
noncomputable section
namespace Nagata.Workers.W24
open Polynomial Nagata.W18
def componentCoordinates (i : ℕ) (a : ℂ) : Fin 3 → ℂ :=
  ![a, (i : ℂ) ^ 2 - (i : ℂ) * a, 1]
theorem plane_normal_equality_contradiction {ι : Type*}
    (k m : ℕ) (hm : 0 < m)
    (component : ι → Fin k) (base c : ι → ℂ)
    (hc : c ∉ (homogeneousEvaluation k
      (fun i => componentCoordinates (component i).val (base i))).range)
    (F : Polynomial (MvPolynomial (Fin 3) ℂ))
    (hhom : ∀ j, (F.coeff j).IsHomogeneous (k * m - k * j))
    (hne : normalResiduePolynomial (homogeneousLineUnion ℂ k) F ≠ 0)
    (hindex : (normalResiduePolynomial (homogeneousLineUnion ℂ k) F).natDegree = m)
    (horder : ∀ i, planeNormalOnLine F (component i).val ∈
      (nestedPointIdeal (base i) (c i)) ^ m) : False := by
  have hnot : ¬ homogeneousLineUnion ℂ k ∣ F.coeff m := by
    simpa only [hindex] using top_normalResidue_coefficient_not_dvd _ _ hne
  have hcoeff : F.coeff m ≠ 0 := by
    intro hz
    exact hnot (hz ▸ dvd_zero _)
  let T : PlaneForms 0 := ⟨F.coeff m, by
    change (F.coeff m).IsHomogeneous 0
    simpa only [Nat.sub_self] using hhom m⟩
  let a := (F.coeff m).coeff 0
  have hconstant : F.coeff m = MvPolynomial.C a := degreeZeroForm_eq_constant T
  have ha : a ≠ 0 := by
    intro hz
    exact hcoeff (by rw [hconstant, hz, MvPolynomial.C_0])
  let s : PlaneForms k := ⟨F.coeff (m - 1), by
    change (F.coeff (m - 1)).IsHomogeneous k
    simpa only [penultimate_exponent k m hm] using hhom (m - 1)⟩
  refine normal_evaluation_contradiction
    (homogeneousEvaluation k (fun i => componentCoordinates (component i).val (base i)))
    c hc m hm a ha (fun i => planeNormalOnLine F (component i).val) base
    ?_ horder ?_ s ?_
  · intro i
    have h := restriction_natDegree_le_normalResidue_degree (homogeneousLineUnion ℂ k)
      F (Nagata.W04.ReducibleSquare.lineRestriction ((component i).val : ℂ))
      (lineRestriction_union_zero k (component i))
    simpa only [planeNormalOnLine, hindex] using h
  · intro i
    rw [planeNormalOnLine_coeff, hconstant]
    simp [Nagata.W04.ReducibleSquare.lineRestriction]
  · intro i
    rw [homogeneousEvaluation_apply, planeNormalOnLine_coeff,
      Nagata.W04.ReducibleSquare.lineRestriction_eval]
    rfl
end Nagata.Workers.W24
end
end
section
noncomputable section
namespace Nagata.Workers.W24
open Polynomial Nagata.W18
open Nagata.W06.LineArrangement
def squareMarkedBase (k : ℕ) (p : Fin k × Fin k) : ℂ :=
  -(markedCoordinate k p.1.val p.2 : ℂ)
def squareMarkedCoordinates (k : ℕ) (p : Fin k × Fin k) : Fin 3 → ℂ :=
  componentCoordinates p.1.val (squareMarkedBase k p)
theorem square_normal_obstruction (k d m : ℕ) (hk : 4 ≤ k) (hm : 0 < m)
    (hd : d ≤ k * m) (c : Fin k × Fin k → ℂ)
    (hc : c ∉ (homogeneousEvaluation k (squareMarkedCoordinates k)).range)
    (F : Polynomial (MvPolynomial (Fin 3) ℂ))
    (hhom : ∀ j, (F.coeff j).IsHomogeneous (d - k * j))
    (hweight : ∀ j, F.coeff j ≠ 0 → k * j ≤ d)
    (hne : normalResiduePolynomial (homogeneousLineUnion ℂ k) F ≠ 0)
    (horder : ∀ p : Fin k × Fin k, planeNormalOnLine F p.1.val ∈
      (nestedPointIdeal (squareMarkedBase k p) (c p)) ^ m) : False := by
  have hkpos : 0 < k := by omega
  let cFirst : ℕ → ℂ := fun i => if hi : i < k then c (⟨i, hi⟩, ⟨0, hkpos⟩) else 0
  let cTail : ℕ → ℕ → ℂ := fun i s =>
    if hi : i < k then if hs : s + 1 < k then c (⟨i, hi⟩, ⟨s + 1, hs⟩) else 0 else 0
  have hfirst : ∀ i < k, planeNormalOnLine F i ∈
      (nestedPointIdeal (-((Nagata.W04.ReducibleSquare.firstMark k i : ℕ) : ℂ))
        (cFirst i)) ^ m := by
    intro i hi
    simpa only [squareMarkedBase, markedCoordinate_zero, cFirst, dif_pos hi] using
      horder (⟨i, hi⟩, ⟨0, hkpos⟩)
  have htail : ∀ i < k, ∀ s < k - 1, planeNormalOnLine F i ∈
      (nestedPointIdeal (-((s + 2 : ℕ) : ℂ)) (cTail i s)) ^ m := by
    intro i hi s hs
    have hs' : s + 1 < k := by omega
    simpa only [squareMarkedBase, markedCoordinate_of_ne_zero k i ⟨s + 1, hs'⟩
      (by change s + 1 ≠ 0; omega), cTail, dif_pos hi, dif_pos hs', Nat.add_assoc] using
      horder (⟨i, hi⟩, ⟨s + 1, hs'⟩)
  obtain ⟨hindex, hdm⟩ := plane_normal_top_index_eq_and_degree_eq k d m (by omega)
    hd F hhom hweight hne cFirst cTail hfirst htail
  apply plane_normal_equality_contradiction k m hm Prod.fst (squareMarkedBase k) c hc
    F (by simpa only [hdm] using hhom) hne hindex horder
theorem exists_square_normal_obstruction (k : ℕ) (hk : 4 ≤ k) :
    ∃ c : Fin k × Fin k → ℂ, ∀ d m : ℕ, 0 < m → d ≤ k * m →
      ∀ F : Polynomial (MvPolynomial (Fin 3) ℂ),
      (∀ j, (F.coeff j).IsHomogeneous (d - k * j)) →
      (∀ j, F.coeff j ≠ 0 → k * j ≤ d) →
      normalResiduePolynomial (homogeneousLineUnion ℂ k) F ≠ 0 →
      ¬ (∀ p : Fin k × Fin k, planeNormalOnLine F p.1.val ∈
        (nestedPointIdeal (squareMarkedBase k p) (c p)) ^ m) := by
  obtain ⟨c, hc⟩ := exists_grid_displacement k hk (squareMarkedCoordinates k)
  exact ⟨c, fun d m hm hd F hhom hweight hne horder =>
    square_normal_obstruction k d m hk hm hd c hc F hhom hweight hne horder⟩
end Nagata.Workers.W24
end
end
end OAI
-- LineNormalData
namespace OAI
section
noncomputable section
namespace Nagata.Workers.W14
open Nagata.W18
theorem pderiv_one_innerPolynomial {K : Type*} [CommRing K] (P : Polynomial K) :
    MvPolynomial.pderiv (1 : Fin 2)
      (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (0 : Fin 2)) P) = 0 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp [hP, hQ]
  | monomial n a =>
    simp [Polynomial.eval₂_monomial]
theorem pderiv_one_nestedToBivariate {K : Type*} [CommRing K]
    (H : Polynomial (Polynomial K)) :
    MvPolynomial.pderiv (1 : Fin 2) (nestedToBivariate H) =
      nestedToBivariate H.derivative := by
  induction H using Polynomial.induction_on' with
  | add P Q hP hQ => simp [hP, hQ]
  | monomial n a =>
    simp [nestedToBivariate, Polynomial.eval₂_monomial, Polynomial.derivative_monomial,
      pderiv_one_innerPolynomial]
    ring
theorem planePolynomialEval_nestedToBivariate
    (H : Polynomial (Polynomial ℂ)) (p : ℂ × ℂ) :
    Nagata.Workers.W28.planePolynomialEval (nestedToBivariate H) p =
      Nagata.W06.LineArrangement.planeEval H p.1 p.2 := by
  unfold Nagata.Workers.W28.planePolynomialEval
  rw [← Nagata.W18.nestedEvaluation_eq_polynomialEvaluation]
  change (Polynomial.evalRingHom p.1) (H.eval (Polynomial.C p.2)) =
    H.eval₂ (Polynomial.evalRingHom p.1) p.2
  simpa using
    (Polynomial.eval₂_at_apply (p := H) (Polynomial.evalRingHom p.1) (Polynomial.C p.2)).symm
theorem planePolynomialEval_pderiv_one_nestedToBivariate
    (H : Polynomial (Polynomial ℂ)) (p : ℂ × ℂ) :
    Nagata.Workers.W28.planePolynomialEval
      (MvPolynomial.pderiv 1 (nestedToBivariate H)) p =
      Nagata.W06.LineArrangement.planeEval H.derivative p.1 p.2 := by
  rw [pderiv_one_nestedToBivariate, planePolynomialEval_nestedToBivariate]
end Nagata.Workers.W14
end
end
section
noncomputable section
namespace Nagata.Workers.W14
open Nagata.W06.LineArrangement Nagata.Workers.W28
end Nagata.Workers.W14
end
end
end OAI
-- SquareReduction
namespace OAI
section
noncomputable section
namespace Nagata.Workers.W24
open Nagata.W06.LineArrangement
theorem marked_directChart_partial_ne_zero (k : ℕ) (i s : Fin k) :
    Nagata.Workers.W28.planePolynomialEval
      (MvPolynomial.pderiv 1 (Nagata.W27.directChartHom 2 (homogeneousLineUnion ℂ k)))
      (markedPoint ℂ k i s) ≠ 0 := by
  rw [directChart_union_eq_nestedToBivariate,
    Nagata.Workers.W14.planePolynomialEval_pderiv_one_nestedToBivariate]
  exact partialY_lineUnion_at_mark k i s
theorem square_universalSupport_degree_gt (k d m : ℕ) (hk : 4 ≤ k) (hm : 0 < m)
    (hU : Nagata.W13.UniversalSupport (k * k) d (fun _ => m)) : k * m < d := by
  by_contra hgt
  have hd : d ≤ k * m := by omega
  obtain ⟨c, hc⟩ := exists_square_normal_obstruction k hk
  let e : Fin (k * k) ≃ Fin k × Fin k := finProdFinEquiv.symm
  let line : Fin (k * k) → ℂ := fun b => ((e b).1.val : ℂ)
  let ξ : Fin (k * k) → ℂ := fun b => squareMarkedBase k (e b)
  let displacement : Fin (k * k) → ℂ := fun b => c (e b)
  have hbase : Function.Injective (fun b : Fin (k * k) =>
      (ξ b, (line b)^2 - line b * ξ b)) := by
    change Function.Injective (fun b => markedPoint ℂ k (e b).1 (e b).2)
    exact (markedPoint_injective k).comp e.injective
  have hline : ∀ b, Nagata.W04.ReducibleSquare.lineRestriction (line b)
      (homogeneousLineUnion ℂ k) = 0 := by
    intro b
    exact lineRestriction_union_zero k (e b).1
  have hpartial : ∀ b, Nagata.Workers.W28.planePolynomialEval
      (MvPolynomial.pderiv 1 (Nagata.W27.directChartHom 2 (homogeneousLineUnion ℂ k)))
      (ξ b, (line b)^2 - line b * ξ b) ≠ 0 := by
    intro b
    exact marked_directChart_partial_ne_zero k (e b).1 (e b).2
  obtain ⟨F, hhom, hweight, hne, horder⟩ :=
    Nagata.Workers.W17.universalSupport_line_normal_polynomial hU
      (homogeneousLineUnion ℂ k) k (homogeneousLineUnion_homogeneous k) (by omega)
      line ξ displacement hbase hline hpartial
  apply hc d m hm hd F hhom hweight hne
  intro p
  simpa only [line, ξ, displacement, Equiv.apply_symm_apply, planeNormalOnLine] using
    horder (e.symm p)
end Nagata.Workers.W24
end
end
section
noncomputable section
namespace Nagata.Workers.W24
open ProjectiveGeometry
open scoped BigOperators
end Nagata.Workers.W24
end
end
end OAI
namespace OAI.Nagata.W13
theorem square_boundary : ∀ k M : ℕ, 4 ≤ k → 0 < M → ¬ UniversalSupport (k*k) (k*M) (fun _ => M) := by
  intro k M hk hM hu
  exact (Nat.lt_irrefl _) (OAI.Nagata.Workers.W24.square_universalSupport_degree_gt k (k*M) M hk hM hu)
end OAI.Nagata.W13
-- OAI.AlgebraicGeometry.PlaneCurves.AffineMultiplicity
namespace OAI
section
namespace Nagata.AffineMultiplicity
variable {σ K : Type*} [CommRing K]
theorem coordinate_difference_mem (p : σ → K) (i : σ) :
    MvPolynomial.X i - MvPolynomial.C (p i) ∈ pointIdeal p := by
  rw [pointIdeal_mem_iff]
  simp
section Field
variable {F : Type*} [Field F]
end Field
end Nagata.AffineMultiplicity
end
section
namespace Nagata.AffineMultiplicity
section MaximalIdeal
variable {R : Type*} [CommRing R] (I : Ideal R) (hI : I.IsMaximal)
include hI
theorem maximalIdeal_power_radical {m : ℕ} (hm : m ≠ 0) :
    (I ^ m).radical = I := by
  rw [Ideal.radical_pow I hm, hI.isPrime.radical]
theorem maximalIdeal_power_isPrimary {m : ℕ} (hm : m ≠ 0) :
    (I ^ m).IsPrimary := by
  apply Ideal.isPrimary_of_isMaximal_radical
  rwa [maximalIdeal_power_radical I hI hm]
theorem maximalIdeal_power_comap_map
    [I.IsPrime] (S : Type*) [CommRing S] [Algebra R S]
    [IsLocalization.AtPrime S I] (m : ℕ) :
    Ideal.comap (algebraMap R S) (Ideal.map (algebraMap R S) (I ^ m)) = I ^ m := by
  by_cases hm : m = 0
  · simp [hm, Ideal.map_top]
  apply IsLocalization.under_map_of_isPrimary_disjoint I.primeCompl S
    (maximalIdeal_power_isPrimary I hI hm)
  apply Set.disjoint_left.mpr
  intro x hx hxm
  exact hx (Ideal.pow_le_self hm hxm)
theorem maximalIdeal_power_localization_iff
    [I.IsPrime] (S : Type*) [CommRing S] [Algebra R S]
    [IsLocalization.AtPrime S I] [IsLocalRing S] (m : ℕ) (f : R) :
    algebraMap R S f ∈ IsLocalRing.maximalIdeal S ^ m ↔ f ∈ I ^ m := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal I S, ← Ideal.map_pow]
  change f ∈ Ideal.comap (algebraMap R S) (Ideal.map (algebraMap R S) (I ^ m)) ↔ _
  rw [maximalIdeal_power_comap_map I hI S m]
end MaximalIdeal
section AffinePoint
variable {σ F : Type*} [Field F]
abbrev PointLocalRing (p : σ → F) := Localization.AtPrime (pointIdeal p)
noncomputable def residueEval (p : σ → F) : PointLocalRing p →+* F :=
  IsLocalization.lift (M := (pointIdeal p).primeCompl)
    (S := PointLocalRing p) (g := MvPolynomial.eval p) (fun s => by
      apply isUnit_iff_ne_zero.mpr
      intro hs
      exact s.property ((pointIdeal_mem_iff p s).mpr hs))
@[simp] theorem residueEval_algebraMap (p : σ → F) (f : MvPolynomial σ F) :
    residueEval p (algebraMap (MvPolynomial σ F) (PointLocalRing p) f) =
      MvPolynomial.eval p f := by
  exact IsLocalization.lift_eq _ f
theorem residueEval_surjective (p : σ → F) : Function.Surjective (residueEval p) := by
  intro a
  refine ⟨algebraMap (MvPolynomial σ F) (PointLocalRing p) (MvPolynomial.C a), ?_⟩
  simp
theorem ker_residueEval (p : σ → F) :
    RingHom.ker (residueEval p) = IsLocalRing.maximalIdeal (PointLocalRing p) :=
  IsLocalRing.ker_eq_maximalIdeal (residueEval p) (residueEval_surjective p)
theorem residueEval_isUnit (p : σ → F) (x : PointLocalRing p) :
    IsUnit x ↔ residueEval p x ≠ 0 := by
  have h : residueEval p x = 0 ↔ ¬ IsUnit x := by
    rw [← RingHom.mem_ker, ker_residueEval, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff]
  simpa only [not_not] using (not_congr h).symm
def localOrderAtLeast (p : σ → F) (m : ℕ) (f : MvPolynomial σ F) : Prop :=
  algebraMap (MvPolynomial σ F) (PointLocalRing p) f ∈
    IsLocalRing.maximalIdeal (PointLocalRing p) ^ m
theorem localOrderAtLeast_iff (p : σ → F) (m : ℕ) (f : MvPolynomial σ F) :
    localOrderAtLeast p m f ↔ orderAtLeast p m f :=
  maximalIdeal_power_localization_iff (pointIdeal p) (pointIdeal_isMaximal p)
    (PointLocalRing p) m f
end AffinePoint
end Nagata.AffineMultiplicity
end
end OAI
-- OAI.AlgebraicGeometry.PlaneCurves.Configuration
namespace OAI
section
noncomputable section
namespace Nagata.ProjectiveGeometry
open scoped BigOperators
def affinePlaneVector (z : Fin 2 → ℂ) : Fin 3 → ℂ :=
  fun j => if j = 0 then 1 else if j = 1 then z 0 else z 1
theorem affinePlaneVector_ne_zero (z : Fin 2 → ℂ) : affinePlaneVector z ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [affinePlaneVector] at h0
def affinePlanePoint (z : Fin 2 → ℂ) : PlanePoint :=
  Projectivization.mk ℂ (affinePlaneVector z) (affinePlaneVector_ne_zero z)
theorem affinePlanePoint_injective : Function.Injective affinePlanePoint := by
  intro z w h
  obtain ⟨a, ha⟩ :=
    (Projectivization.mk_eq_mk_iff' ℂ (affinePlaneVector z) (affinePlaneVector w)
      (affinePlaneVector_ne_zero z) (affinePlaneVector_ne_zero w)).mp h
  have ha1 : a = 1 := by
    have h0 := congrFun ha 0
    simpa [affinePlaneVector] using h0
  have hzero : w 0 = z 0 := by
    have h1 := congrFun ha 1
    simpa [affinePlaneVector, ha1] using h1
  have hone : w 1 = z 1 := by
    have h2 := congrFun ha 2
    simpa [affinePlaneVector, ha1] using h2
  funext i
  refine Fin.cases hzero.symm ?_ i
  intro j
  have hj : j = 0 := Subsingleton.elim j 0
  subst j
  exact hone.symm
structure MultihomogeneousEquation (r : ℕ) where
  polynomial : MvPolynomial (Fin r × Fin 3) ℂ
  multidegree : Fin r → ℕ
  homogeneous : ∀ a ∈ polynomial.support, ∀ i,
    (∑ j : Fin 3, a (i, j)) = multidegree i
def equationVanishes {r : ℕ} (F : MultihomogeneousEquation r)
    (p : Fin r → PlanePoint) : Prop :=
  ∀ (v : Fin r → Fin 3 → ℂ) (hv : ∀ i, v i ≠ 0),
    (∀ i, Projectivization.mk ℂ (v i) (hv i) = p i) →
    MvPolynomial.eval (fun ij => v ij.1 ij.2) F.polynomial = 0
def IsProductZariskiClosed {r : ℕ} (S : Set (Fin r → PlanePoint)) : Prop :=
  ∃ equations : Set (MultihomogeneousEquation r),
    ∀ p, p ∈ S ↔ ∀ F ∈ equations, equationVanishes F p
def IsConfigurationZariskiClosed {r : ℕ}
    (S : Set (OrderedDistinctPoints r)) : Prop :=
  ∃ T : Set (Fin r → PlanePoint), IsProductZariskiClosed T ∧
    ∀ p, p ∈ S ↔ p.val ∈ T
theorem equationVanishes_rep {r : ℕ} (F : MultihomogeneousEquation r)
    (p : Fin r → PlanePoint) (h : equationVanishes F p) :
    MvPolynomial.eval (fun ij => (p ij.1).rep ij.2) F.polynomial = 0 := by
  exact h (fun i => (p i).rep) (fun i => (p i).rep_nonzero)
    (fun i => Projectivization.mk_rep (p i))
theorem mk_rep_coordinate_ne_zero_iff (v : Fin 3 → ℂ) (hv : v ≠ 0) (c : Fin 3) :
    (Projectivization.mk ℂ v hv).rep c ≠ 0 ↔ v c ≠ 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  rw [← ha]
  simp [Units.smul_def, smul_eq_mul, a.ne_zero]
theorem chart_exists (p : PlanePoint) : ∃ c : Fin 3, p.rep c ≠ 0 := by
  by_contra h
  apply p.rep_nonzero
  funext c
  exact Classical.not_not.mp (fun hc => h ⟨c, hc⟩)
end Nagata.ProjectiveGeometry
end
end
section
noncomputable section
namespace Nagata
open ProjectiveGeometry
open scoped BigOperators
end Nagata
end
end
section
noncomputable section
namespace Nagata.ProjectiveGeometry
def InConfigurationChart {r : ℕ} (c : ConfigurationChart r)
    (p : Fin r → PlanePoint) : Prop := ∀ i, (p i).rep (c i) ≠ 0
def configurationChartCoordinates₂ {r : ℕ} (c : ConfigurationChart r)
    (p : Fin r → PlanePoint) : Fin r × Fin 2 → ℂ :=
  fun ij => (p ij.1).rep ((c ij.1).succAbove ij.2) / (p ij.1).rep (c ij.1)
theorem configurationChart_cover {r : ℕ} (p : Fin r → PlanePoint) :
    ∃ c : ConfigurationChart r, InConfigurationChart c p := by
  let c : Fin r → Fin 3 := fun i => Classical.choose (chart_exists (p i))
  exact ⟨c, fun i => Classical.choose_spec (chart_exists (p i))⟩
end Nagata.ProjectiveGeometry
end
end
section
noncomputable section
namespace Nagata.ProjectiveGeometry
open scoped BigOperators
theorem multihomogeneous_eval_scale {r : ℕ} (F : MultihomogeneousEquation r)
    (a : Fin r → ℂ) (v : Fin r × Fin 3 → ℂ) :
    MvPolynomial.eval (fun ij => a ij.1 * v ij) F.polynomial =
      (∏ i : Fin r, a i ^ F.multidegree i) * MvPolynomial.eval v F.polynomial := by
  classical
  simp only [MvPolynomial.eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [mul_pow, Finset.prod_mul_distrib]
  have hprod : (∏ ij : Fin r × Fin 3, a ij.1 ^ u ij) =
      ∏ i : Fin r, a i ^ F.multidegree i := by
    rw [Fintype.prod_prod_type]
    apply Finset.prod_congr rfl
    intro i hi
    change (∏ j : Fin 3, a i ^ u (i, j)) = a i ^ F.multidegree i
    rw [Finset.prod_pow_eq_pow_sum, F.homogeneous u hu i]
  rw [hprod]
  ac_rfl
theorem equationVanishes_iff_eval_rep {r : ℕ} (F : MultihomogeneousEquation r)
    (p : Fin r → PlanePoint) :
    equationVanishes F p ↔
      MvPolynomial.eval (fun ij => (p ij.1).rep ij.2) F.polynomial = 0 := by
  constructor
  · exact equationVanishes_rep F p
  · intro hrep v hv hp
    have hex : ∀ i : Fin r, ∃ a : ℂ, a • (p i).rep = v i := by
      intro i
      apply (Projectivization.mk_eq_mk_iff' ℂ (v i) (p i).rep
        (hv i) (p i).rep_nonzero).mp
      exact (hp i).trans (Projectivization.mk_rep (p i)).symm
    let a : Fin r → ℂ := fun i => Classical.choose (hex i)
    have ha : ∀ i, a i • (p i).rep = v i := fun i => Classical.choose_spec (hex i)
    have hv_eq : (fun ij : Fin r × Fin 3 => v ij.1 ij.2) =
        fun ij => a ij.1 * (p ij.1).rep ij.2 := by
      funext ij
      simpa only [Pi.smul_apply, smul_eq_mul] using (congrFun (ha ij.1) ij.2).symm
    rw [hv_eq, multihomogeneous_eval_scale, hrep, mul_zero]
end Nagata.ProjectiveGeometry
end
end
end OAI
-- OAI.AlgebraicGeometry.PlaneCurves.PolynomialAvoidance
namespace OAI
section
namespace Nagata.Workers.W25
open MvPolynomial
theorem exists_countable_nonzero_eval_fin (K : Type*) [CommRing K] [IsDomain K]
    [Uncountable K] (n : ℕ) {ι : Type*} [Countable ι] :
    ∀ p : ι → MvPolynomial (Fin n) K, (∀ i, p i ≠ 0) →
      ∃ x : Fin n → K, ∀ i, eval x (p i) ≠ 0 := by
  classical
  induction n with
  | zero =>
      intro p hp
      refine ⟨Fin.elim0, fun i hi => hp i ?_⟩
      apply (isEmptyRingEquiv K (Fin 0)).injective
      rw [map_zero, isEmptyRingEquiv_eq_coeff_zero]
      rw [(p i).eq_C_of_isEmpty, eval_C] at hi
      exact hi
  | succ n ih =>
      intro p hp
      let Q : ι → Polynomial (MvPolynomial (Fin n) K) :=
        fun i => finSuccEquiv K n (p i)
      have hQ : ∀ i, Q i ≠ 0 := by
        intro i hi
        apply hp i
        apply (finSuccEquiv K n).injective
        simpa only [map_zero] using hi
      have hcoeff : ∀ i, ∃ d, (Q i).coeff d ≠ 0 := by
        intro i
        by_contra h
        apply hQ i
        apply Polynomial.ext
        intro d
        simp only [Polynomial.coeff_zero]
        exact Classical.not_not.mp (fun hd => h ⟨d, hd⟩)
      let k : ι → ℕ := fun i => Classical.choose (hcoeff i)
      have hk : ∀ i, (Q i).coeff (k i) ≠ 0 :=
        fun i => Classical.choose_spec (hcoeff i)
      obtain ⟨x, hx⟩ := ih (fun i => (Q i).coeff (k i)) hk
      let q : ι → Polynomial K := fun i => Polynomial.map (eval x) (Q i)
      have hq : ∀ i, q i ≠ 0 := by
        intro i hi
        apply hx i
        have h := congrArg (fun P : Polynomial K => P.coeff (k i)) hi
        simpa only [q, Polynomial.coeff_map, Polynomial.coeff_zero] using h
      let B : Set K := ⋃ i, {y | (q i).IsRoot y}
      have hB : B.Countable := Set.countable_iUnion fun i =>
        (Polynomial.finite_setOfPred_isRoot (hq i)).countable
      have hex : ∃ y : K, y ∉ B := by
        by_contra h
        have hBu : B = Set.univ := Set.eq_univ_of_forall fun y =>
          Classical.not_not.mp (fun hy => h ⟨y, hy⟩)
        exact Set.not_countable_univ (hBu ▸ hB)
      obtain ⟨y, hy⟩ := hex
      refine ⟨Fin.cons y x, fun i hi => hy ?_⟩
      apply Set.mem_iUnion.mpr
      refine ⟨i, ?_⟩
      change Polynomial.eval y (q i) = 0
      simpa only [eval_eq_eval_mv_eval', q, Q] using hi
theorem exists_countable_nonzero_eval (K : Type*) [CommRing K] [IsDomain K]
    [Uncountable K] {σ ι : Type*} [Fintype σ] [Countable ι]
    (p : ι → MvPolynomial σ K) (hp : ∀ i, p i ≠ 0) :
    ∃ x : σ → K, ∀ i, eval x (p i) ≠ 0 := by
  classical
  let e := Fintype.equivFin σ
  have hq : ∀ i, rename e (p i) ≠ 0 := by
    intro i hi
    apply hp i
    apply rename_injective e e.injective
    simpa only [map_zero] using hi
  obtain ⟨x, hx⟩ := exists_countable_nonzero_eval_fin K (Fintype.card σ)
    (fun i => rename e (p i)) hq
  refine ⟨x ∘ e, fun i => ?_⟩
  simpa only [eval_rename] using hx i
end Nagata.Workers.W25
end
section
namespace Nagata.Workers.W25
theorem exists_complex_polynomial_avoidance_direct {σ ι : Type*} [Fintype σ] [Countable ι]
    (p : ι → MvPolynomial σ ℂ) (hp : ∀ i, p i ≠ 0) :
    ∃ x : σ → ℂ, ∀ i, MvPolynomial.eval x (p i) ≠ 0 := by
  let : Uncountable ℂ := Cardinal.aleph0_lt_mk_iff.mp (by
    rw [Cardinal.mk_complex]
    exact Cardinal.cantor Cardinal.aleph0)
  exact exists_countable_nonzero_eval ℂ p hp
end Nagata.Workers.W25
end
section
noncomputable section
namespace Nagata.Workers.W25
open Nagata.ProjectiveGeometry
end Nagata.Workers.W25
end
end
section
namespace Nagata.Workers.W25
theorem complex_polynomial_funext {σ : Type*} [Fintype σ]
    {p q : MvPolynomial σ ℂ}
    (h : ∀ x : σ → ℂ, MvPolynomial.eval x p = MvPolynomial.eval x q) : p = q := by
  apply sub_eq_zero.mp
  by_contra hne
  obtain ⟨x, hx⟩ := exists_complex_polynomial_avoidance_direct
    (fun _ : Unit => p - q) (fun _ => hne)
  apply hx ()
  rw [map_sub, h x, sub_self]
end Nagata.Workers.W25
end
end OAI
-- OAI.AlgebraicGeometry.PlaneCurves.Forms
namespace OAI
section
noncomputable section
namespace Nagata.W16
theorem homogeneous_eval₂_scale {σ K R : Type*} [CommSemiring K] [CommSemiring R]
    {F : MvPolynomial σ K} {d : ℕ} (hF : F.IsHomogeneous d)
    (k : K →+* R) (x : σ → R) (a : R) :
    MvPolynomial.eval₂ k (fun i => a * x i) F =
      a ^ d * MvPolynomial.eval₂ k x F := by
  classical
  simp only [MvPolynomial.eval₂_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hF.degree_eq_sum_deg_support hu]
  ac_rfl
namespace NonzeroHomogeneousForm
end NonzeroHomogeneousForm
open scoped BigOperators
end Nagata.W16
end
end
section
noncomputable section
namespace Nagata.W16
open scoped BigOperators
end Nagata.W16
end
end
section
namespace Nagata.W16
open Nagata.ProjectiveGeometry
end Nagata.W16
end
section
noncomputable section
namespace Nagata.W16
open Nagata.ProjectiveGeometry
open scoped BigOperators
def blockDehomogenize {r : ℕ} (F : MultihomogeneousEquation r) :
    MvPolynomial (Fin r × Fin 2) ℂ :=
  MvPolynomial.eval₂ MvPolynomial.C
    (fun ij => if ij.2 = 0 then 1 else
      if ij.2 = 1 then MvPolynomial.X (ij.1, 0) else MvPolynomial.X (ij.1, 1))
    F.polynomial
theorem multihomogeneous_eval_scale {r : ℕ} (F : MultihomogeneousEquation r)
    (x : Fin r × Fin 3 → ℂ) (a : Fin r → ℂ) :
    MvPolynomial.eval (fun ij => a ij.1 * x ij) F.polynomial =
      (∏ i, a i ^ F.multidegree i) * MvPolynomial.eval x F.polynomial := by
  classical
  simp only [MvPolynomial.eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [mul_pow, Finset.prod_mul_distrib]
  have hdegrees : (∏ ij : Fin r × Fin 3, a ij.1 ^ u ij) =
      ∏ i, a i ^ F.multidegree i := by
    rw [Fintype.prod_prod_type]
    apply Finset.prod_congr rfl
    intro i _
    change (∏ y : Fin 3, a i ^ u (i, y)) = a i ^ F.multidegree i
    rw [Finset.prod_pow_eq_pow_sum, F.homogeneous u hu i]
  rw [hdegrees]
  ac_rfl
theorem eval_blockDehomogenize {r : ℕ} (F : MultihomogeneousEquation r)
    (x : Fin r × Fin 2 → ℂ) :
    MvPolynomial.eval x (blockDehomogenize F) =
      MvPolynomial.eval
        (fun ij => affinePlaneVector (fun j => x (ij.1, j)) ij.2) F.polynomial := by
  classical
  unfold blockDehomogenize
  rw [← MvPolynomial.eval_assoc]
  apply congrArg (fun z : Fin r × Fin 3 → ℂ => MvPolynomial.eval z F.polynomial)
  funext ij
  rcases ij with ⟨i, j⟩
  fin_cases j <;> simp [affinePlaneVector, Function.comp_apply]
theorem eval_blockDehomogenize_normalized {r : ℕ} (F : MultihomogeneousEquation r)
    (x : Fin r × Fin 3 → ℂ) (hc : ∀ i, x (i, 0) ≠ 0) :
    MvPolynomial.eval (fun ij : Fin r × Fin 2 => x (ij.1, ij.2.succ) / x (ij.1, 0))
        (blockDehomogenize F) =
      (∏ i, (x (i, 0))⁻¹ ^ F.multidegree i) * MvPolynomial.eval x F.polynomial := by
  classical
  rw [eval_blockDehomogenize]
  have hcoords :
      (fun ij : Fin r × Fin 3 =>
        affinePlaneVector (fun j => x (ij.1, j.succ) / x (ij.1, 0)) ij.2) =
      fun ij => (x (ij.1, 0))⁻¹ * x ij := by
    funext ij
    rcases ij with ⟨i, j⟩
    fin_cases j <;> simp [affinePlaneVector, hc i, div_eq_mul_inv] <;> ac_rfl
  rw [hcoords]
  exact multihomogeneous_eval_scale F x (fun i => (x (i, 0))⁻¹)
theorem eq_zero_of_blockDehomogenize_eq_zero {r : ℕ}
    (F : MultihomogeneousEquation r) (hchart : blockDehomogenize F = 0) :
    F.polynomial = 0 := by
  classical
  let Q : MvPolynomial (Fin r × Fin 3) ℂ := ∏ i : Fin r, MvPolynomial.X (i, 0)
  have hQ : Q ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact MvPolynomial.X_ne_zero (i, 0)
  have hmul : Q * F.polynomial = 0 := by
    apply Nagata.Workers.W25.complex_polynomial_funext
    intro x
    rw [map_mul, map_zero]
    by_cases hc : ∀ i : Fin r, x (i, 0) ≠ 0
    · have hz := congrArg
        (MvPolynomial.eval (fun ij : Fin r × Fin 2 => x (ij.1, ij.2.succ) / x (ij.1, 0)))
        hchart
      rw [eval_blockDehomogenize_normalized F x hc, map_zero] at hz
      have hn : (∏ i, (x (i, 0))⁻¹ ^ F.multidegree i) ≠ 0 := by
        apply Finset.prod_ne_zero_iff.mpr
        intro i _
        exact pow_ne_zero _ (inv_ne_zero (hc i))
      rw [(mul_eq_zero.mp hz).resolve_left hn, mul_zero]
    · obtain ⟨i, hi⟩ := Classical.not_forall.mp hc
      have hi0 : x (i, 0) = 0 := Classical.not_not.mp hi
      have heval : MvPolynomial.eval x Q = ∏ i : Fin r, x (i, 0) := by
        simp [Q]
      rw [heval, Finset.prod_eq_zero (Finset.mem_univ i) hi0, zero_mul]
  exact (mul_eq_zero.mp hmul).resolve_left hQ
theorem blockDehomogenize_ne_zero {r : ℕ} (F : MultihomogeneousEquation r)
    (hne : F.polynomial ≠ 0) : blockDehomogenize F ≠ 0 := by
  intro hz
  exact hne (eq_zero_of_blockDehomogenize_eq_zero F hz)
end Nagata.W16
end
end
end OAI
-- OAI.AlgebraicGeometry.PlaneCurves.MatrixLimits
namespace OAI
section
noncomputable section
open Module
namespace Nagata.Workers.W11
variable {ι κ V K : Type*} [Field K] [Fintype ι] [AddCommGroup V] [Module K V]
end Nagata.Workers.W11
end
end
section
open Filter Topology
namespace Nagata.Workers.W11
variable {α ι κ : Type*} [Fintype ι] [DecidableEq ι]
end Nagata.Workers.W11
end
section
namespace Nagata.Workers.W11
variable {ρ κ K : Type*} [Fintype ρ] [Fintype κ] [DecidableEq κ]
theorem det_mul_eq_zero_of_all_maximal_minors_zero [CommRing K]
    (A : Matrix ρ κ K) (C : Matrix κ ρ K)
    (hA : ∀ s : κ → ρ, Matrix.det (fun i j => A (s i) j) = 0) :
    (C * A).det = 0 := by
  classical
  let D : MultilinearMap K (fun _ : κ => κ → K) K :=
    Matrix.detRowAlternating.toMultilinearMap
  have hmul : C * A = fun i => ∑ r, C i r • A r := by
    funext i j
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change D (C * A) = 0
  rw [hmul, D.map_sum]
  apply Finset.sum_eq_zero
  intro s _
  rw [D.map_smul_univ]
  change (∏ i, C i (s i)) • Matrix.det (fun i j => A (s i) j) = 0
  rw [hA s, smul_zero]
theorem exists_nonzero_kernel_of_all_maximal_minors_zero [Field K]
    (A : Matrix ρ κ K)
    (hA : ∀ s : κ → ρ, Matrix.det (fun i j => A (s i) j) = 0) :
    ∃ c : κ → K, c ≠ 0 ∧ A.mulVec c = 0 := by
  classical
  by_contra hkernel
  have hker : LinearMap.ker (Matrix.toLin' A) = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro c hc
    by_contra hc0
    exact hkernel ⟨c, hc0, hc⟩
  obtain ⟨g, hg⟩ := (Matrix.toLin' A).exists_leftInverse_of_injective hker
  have hC : LinearMap.toMatrix' g * A = 1 := by
    simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
      LinearMap.toMatrix'_id] using congrArg LinearMap.toMatrix' hg
  have hdet := det_mul_eq_zero_of_all_maximal_minors_zero A (LinearMap.toMatrix' g) hA
  rw [hC, Matrix.det_one] at hdet
  exact one_ne_zero hdet
theorem exists_nonzero_kernel_coordinates_of_all_maximal_minors_zero [Field K]
    (A : Matrix ρ κ K)
    (hA : ∀ s : κ → ρ, Matrix.det (fun i j => A (s i) j) = 0) :
    ∃ c : κ → K, c ≠ 0 ∧ ∀ i, ∑ j, A i j * c j = 0 := by
  obtain ⟨c, hc, hAc⟩ := exists_nonzero_kernel_of_all_maximal_minors_zero A hA
  exact ⟨c, hc, fun i => congrFun hAc i⟩
end Nagata.Workers.W11
end
end OAI
-- OAI.AlgebraicGeometry.PlaneCurves.ChartJets
namespace OAI
section
namespace Nagata.W27
noncomputable section
open MvPolynomial
section Entries
variable {R : Type*} [CommRing R]
variable {ι : Type*}
end Entries
end
end Nagata.W27
end
section
noncomputable section
namespace Nagata.W27
open scoped BigOperators
open MvPolynomial
section MatrixEntries
variable {R : Type*} [CommRing R]
end MatrixEntries
section LinearEquations
variable {R : Type*} [CommRing R]
variable {σ κ ρ : Type*} [Fintype κ]
def polynomialZeroSet {τ : Type*} (f : τ → MvPolynomial σ R) : Set (σ → R) :=
  {p | ∀ t, eval p (f t) = 0}
end LinearEquations
end Nagata.W27
end
end
section
noncomputable section
namespace Nagata.W27
open MvPolynomial
open Classical
variable {R : Type*} [CommRing R]
end Nagata.W27
end
end
section
noncomputable section
namespace Nagata.W27
open MvPolynomial
variable {ι R : Type*} [CommRing R]
end Nagata.W27
end
end
section
namespace Nagata.W27
noncomputable section
open scoped BigOperators
open MvPolynomial
section Determinants
variable {R : Type*} [CommRing R]
variable {σ κ ρ : Type*} [Fintype κ] [DecidableEq κ]
def minorPolynomial (A : Matrix ρ κ (MvPolynomial σ R)) (s : κ → ρ) :
    MvPolynomial σ R :=
  Matrix.det (fun i j => A (s i) j)
theorem eval_minorPolynomial (A : Matrix ρ κ (MvPolynomial σ R))
    (s : κ → ρ) (p : σ → R) :
    eval p (minorPolynomial A s) = Matrix.det (fun i j => eval p (A (s i) j)) := by
  exact (eval p).map_det _
theorem minor_zeroSet_iff (A : Matrix ρ κ (MvPolynomial σ R)) (p : σ → R) :
    p ∈ polynomialZeroSet (minorPolynomial A) ↔
      ∀ s : κ → ρ, Matrix.det (fun i j => eval p (A (s i) j)) = 0 := by
  simp only [polynomialZeroSet, Set.mem_ofPred_eq, eval_minorPolynomial]
theorem minor_eq_zero_of_nonzero_kernel [IsDomain R]
    (A : Matrix ρ κ (MvPolynomial σ R)) (p : σ → R)
    (c : κ → R) (hc : coefficientLinearMap A p c = 0) (hcne : c ≠ 0)
    (s : κ → ρ) : eval p (minorPolynomial A s) = 0 := by
  rw [eval_minorPolynomial]
  apply Matrix.det_eq_zero_of_not_linearIndependent_cols
  intro hli
  have hz : (∑ col, c col • (fun i => eval p (A (s i) col))) = 0 := by
    funext i
    have hrow : coefficientEquation A p c (s i) = 0 := congrFun hc (s i)
    simpa only [coefficientEquation, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply, mul_comm] using hrow
  have hc0 : ∀ col, c col = 0 := Fintype.linearIndependent_iff.mp hli c hz
  exact hcne (funext hc0)
theorem mem_minor_zeroSet_of_nonzero_kernel [IsDomain R]
    (A : Matrix ρ κ (MvPolynomial σ R)) (p : σ → R)
    (c : κ → R) (hc : coefficientLinearMap A p c = 0) (hcne : c ≠ 0) :
    p ∈ polynomialZeroSet (minorPolynomial A) :=
  fun s => minor_eq_zero_of_nonzero_kernel A p c hc hcne s
end Determinants
end
end Nagata.W27
end
section
noncomputable section
namespace Nagata.W27
open MvPolynomial
end Nagata.W27
end
end
section
noncomputable section
namespace Nagata.W27
open scoped BigOperators
open MvPolynomial
variable {R σ : Type*} [CommRing R]
end Nagata.W27
end
end
section
noncomputable section
namespace Nagata.W27
open scoped BigOperators
open MvPolynomial
variable {R : Type*} [CommRing R]
end Nagata.W27
end
end
section
namespace Nagata.W27
noncomputable section
open MvPolynomial
end
end Nagata.W27
end
section
noncomputable section
namespace Nagata.W27
open MvPolynomial
variable {R : Type*} [CommRing R]
end Nagata.W27
end
end
section
noncomputable section
namespace Nagata.W27
open MvPolynomial
variable {σ ρ κ K : Type*} [Field K]
variable [Fintype ρ] [Fintype κ] [DecidableEq κ]
theorem nonzero_kernel_iff_minor_zeroSet
    (A : Matrix ρ κ (MvPolynomial σ K)) (p : σ → K) :
    (∃ c : κ → K, c ≠ 0 ∧ coefficientLinearMap A p c = 0) ↔
      p ∈ polynomialZeroSet (minorPolynomial A) := by
  constructor
  · rintro ⟨c, hc, hAc⟩
    exact mem_minor_zeroSet_of_nonzero_kernel A p c hAc hc
  · intro h
    obtain ⟨c, hc, hAc⟩ :=
      Nagata.Workers.W11.exists_nonzero_kernel_coordinates_of_all_maximal_minors_zero
        (fun i j => eval p (A i j)) ((minor_zeroSet_iff A p).mp h)
    exact ⟨c, hc, funext hAc⟩
end Nagata.W27
end
end
section
noncomputable section
namespace Nagata.W27
open MvPolynomial
variable {r : ℕ} {R : Type*} [CommRing R]
end Nagata.W27
end
end
section
noncomputable section
namespace Nagata.W27
open scoped BigOperators
open MvPolynomial
open Classical
variable {R : Type*} [CommRing R]
variable {r : ℕ}
end Nagata.W27
end
end
section
noncomputable section
namespace Nagata.W27
open MvPolynomial
open Classical
variable {r : ℕ} {K : Type*} [Field K]
theorem exists_nonzero_form_iff_chart_minors (c : Fin r → Fin 3)
    (d : ℕ) (m : Fin r → ℕ) (p : Fin r × Fin 2 → K) :
    (∃ F : homogeneousSubmodule (Fin 3) K d, F.val ≠ 0 ∧
      ∀ i, Nagata.AffineMultiplicity.orderAtLeast (fun j => p (i, j)) (m i)
        (directChartHom (c i) F.val)) ↔
      p ∈ polynomialZeroSet (minorPolynomial (chartPlaneJetMatrix c d m)) := by
  classical
  exact (exists_nonzero_form_iff_chart_kernel c d m p).trans
    (nonzero_kernel_iff_minor_zeroSet (chartPlaneJetMatrix c d m) p)
end Nagata.W27
end
end
end OAI
-- OAI.AlgebraicGeometry.PlaneCurves.ChartMultiplicityBridge
namespace OAI
section
noncomputable section
namespace Nagata.ProjectiveGeometry
abbrev ChartLocalRing (b : Fin 3) (p : PlanePoint) :=
  AffineMultiplicity.PointLocalRing (chartCoordinates b p)
def localHomogeneousCoordinates (b : Fin 3) (p : PlanePoint) :
    Fin 3 → ChartLocalRing b p :=
  fun j => if h : j = b then 1 else
    algebraMap (MvPolynomial (ChartVariables b) ℂ) (ChartLocalRing b p)
      (MvPolynomial.X ⟨j, h⟩)
theorem localHomogeneousCoordinates_isUnit (b c : Fin 3) (p : PlanePoint)
    (hb : p.rep b ≠ 0) (hc : p.rep c ≠ 0) :
    IsUnit (localHomogeneousCoordinates b p c) := by
  by_cases hcb : c = b
  · simp [localHomogeneousCoordinates, hcb]
  · simp only [localHomogeneousCoordinates, dif_neg hcb]
    apply (AffineMultiplicity.residueEval_isUnit (chartCoordinates b p) _).mpr
    simpa [chartCoordinates] using div_ne_zero hc hb
def localChartDenominatorUnit (b c : Fin 3) (p : PlanePoint)
    (hb : p.rep b ≠ 0) (hc : p.rep c ≠ 0) : (ChartLocalRing b p)ˣ :=
  (localHomogeneousCoordinates_isUnit b c p hb hc).unit
theorem localChartDenominatorUnit_val (b c : Fin 3) (p : PlanePoint)
    (hb : p.rep b ≠ 0) (hc : p.rep c ≠ 0) :
    (localChartDenominatorUnit b c p hb hc : ChartLocalRing b p) =
      localHomogeneousCoordinates b p c :=
  (localHomogeneousCoordinates_isUnit b c p hb hc).unit_spec
def chartTransitionToLocalRing (b c : Fin 3) (p : PlanePoint)
    (hb : p.rep b ≠ 0) (hc : p.rep c ≠ 0) :
    MvPolynomial (ChartVariables c) ℂ →+* ChartLocalRing b p :=
  MvPolynomial.eval₂Hom
    ((algebraMap (MvPolynomial (ChartVariables b) ℂ) (ChartLocalRing b p)).comp
      MvPolynomial.C)
    (fun j => (↑((localChartDenominatorUnit b c p hb hc)⁻¹) : ChartLocalRing b p) *
      localHomogeneousCoordinates b p j.val)
theorem eval₂_dehomogenize {R : Type*} [CommSemiring R]
    (k : ℂ →+* R) (x : Fin 3 → R) (c : Fin 3) (hc : x c = 1)
    (F : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial.eval₂ k (fun j : ChartVariables c => x j.val) (dehomogenize c F) =
      MvPolynomial.eval₂ k x F := by
  rw [dehomogenize, ← MvPolynomial.eval₂_assoc]
  congr 1
  funext j
  by_cases hj : j = c
  · subst j
    simp [hc]
  · simp [hj]
theorem eval₂_localHomogeneousCoordinates (b : Fin 3) (p : PlanePoint)
    (F : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial.eval₂
      ((algebraMap (MvPolynomial (ChartVariables b) ℂ) (ChartLocalRing b p)).comp
        MvPolynomial.C)
      (localHomogeneousCoordinates b p) F =
    algebraMap (MvPolynomial (ChartVariables b) ℂ) (ChartLocalRing b p)
      (dehomogenize b F) := by
  rw [dehomogenize, MvPolynomial.eval₂_comp_left]
  congr 1
  funext j
  by_cases hj : j = b
  · simp [localHomogeneousCoordinates, hj]
  · simp [localHomogeneousCoordinates, hj]
theorem chartTransition_dehomogenize {F : MvPolynomial (Fin 3) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) (b c : Fin 3) (p : PlanePoint)
    (hb : p.rep b ≠ 0) (hc : p.rep c ≠ 0) :
    chartTransitionToLocalRing b c p hb hc (dehomogenize c F) =
      (↑((localChartDenominatorUnit b c p hb hc)⁻¹) : ChartLocalRing b p) ^ d *
        algebraMap (MvPolynomial (ChartVariables b) ℂ) (ChartLocalRing b p)
          (dehomogenize b F) := by
  let u := localChartDenominatorUnit b c p hb hc
  have hu : (↑(u⁻¹) : ChartLocalRing b p) * localHomogeneousCoordinates b p c = 1 := by
    rw [← localChartDenominatorUnit_val b c p hb hc]
    exact Units.inv_mul u
  change MvPolynomial.eval₂ _
    (fun j : ChartVariables c => (↑(u⁻¹) : ChartLocalRing b p) *
      localHomogeneousCoordinates b p j.val) (dehomogenize c F) = _
  rw [eval₂_dehomogenize _
    (fun j : Fin 3 => (↑(u⁻¹) : ChartLocalRing b p) * localHomogeneousCoordinates b p j) c hu]
  rw [W16.homogeneous_eval₂_scale hF]
  rw [eval₂_localHomogeneousCoordinates]
theorem residueEval_localHomogeneousCoordinates (b : Fin 3) (p : PlanePoint)
    (hb : p.rep b ≠ 0) (j : Fin 3) :
    AffineMultiplicity.residueEval (chartCoordinates b p)
      (localHomogeneousCoordinates b p j) = p.rep j / p.rep b := by
  by_cases hj : j = b
  · subst j
    simp [localHomogeneousCoordinates, hb]
  · simp [localHomogeneousCoordinates, hj, chartCoordinates]
theorem chartTransition_residueEval (b c : Fin 3) (p : PlanePoint)
    (hb : p.rep b ≠ 0) (hc : p.rep c ≠ 0)
    (f : MvPolynomial (ChartVariables c) ℂ) :
    AffineMultiplicity.residueEval (chartCoordinates b p)
      (chartTransitionToLocalRing b c p hb hc f) =
        MvPolynomial.eval (chartCoordinates c p) f := by
  let ρ := AffineMultiplicity.residueEval (chartCoordinates b p)
  let e := chartTransitionToLocalRing b c p hb hc
  let u := localChartDenominatorUnit b c p hb hc
  have hu : ρ (↑u : ChartLocalRing b p) = p.rep c / p.rep b := by
    rw [localChartDenominatorUnit_val]
    exact residueEval_localHomogeneousCoordinates b p hb c
  have he : ρ.comp e = MvPolynomial.eval (chartCoordinates c p) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [ρ, e, chartTransitionToLocalRing]
    · intro j
      simp only [RingHom.comp_apply, e, chartTransitionToLocalRing,
        MvPolynomial.eval₂Hom_X', MvPolynomial.eval_X]
      change ρ ((↑(u⁻¹) : ChartLocalRing b p) *
        localHomogeneousCoordinates b p j.val) = p.rep j.val / p.rep c
      rw [map_mul, map_units_inv, hu,
        residueEval_localHomogeneousCoordinates b p hb j.val]
      rw [mul_comm, ← div_eq_mul_inv, div_div_div_cancel_right₀ hb]
  exact RingHom.congr_fun he f
theorem orderAtLeast_map_into_kernel {σ K R : Type*} [CommRing K] [CommRing R]
    (p : σ → K) (e : MvPolynomial σ K →+* R) (ρ : R →+* K)
    (he : ∀ f, ρ (e f) = MvPolynomial.eval p f)
    (m : ℕ) (f : MvPolynomial σ K)
    (hf : AffineMultiplicity.orderAtLeast p m f) :
    e f ∈ (RingHom.ker ρ) ^ m := by
  have hle : AffineMultiplicity.pointIdeal p ≤ Ideal.comap e (RingHom.ker ρ) := by
    intro g hg
    change ρ (e g) = 0
    rw [he]
    exact (AffineMultiplicity.pointIdeal_mem_iff p g).mp hg
  have hp : f ∈ (Ideal.comap e (RingHom.ker ρ)) ^ m :=
    Ideal.pow_right_mono hle m hf
  exact Ideal.le_comap_pow e m hp
theorem chart_order_transport_via_residue {F : MvPolynomial (Fin 3) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) (b c : Fin 3) (p : PlanePoint)
    (hb : p.rep b ≠ 0) (hc : p.rep c ≠ 0) (m : ℕ)
    (ρ : ChartLocalRing b p →+* ℂ)
    (hker : RingHom.ker ρ = IsLocalRing.maximalIdeal (ChartLocalRing b p))
    (heval : ∀ f, ρ (chartTransitionToLocalRing b c p hb hc f) =
      MvPolynomial.eval (chartCoordinates c p) f)
    (hf : AffineMultiplicity.orderAtLeast (chartCoordinates c p) m (dehomogenize c F)) :
    AffineMultiplicity.orderAtLeast (chartCoordinates b p) m (dehomogenize b F) := by
  have hmap := orderAtLeast_map_into_kernel (chartCoordinates c p)
    (chartTransitionToLocalRing b c p hb hc) ρ heval m (dehomogenize c F) hf
  rw [hker, chartTransition_dehomogenize hF b c p hb hc] at hmap
  have hunit : IsUnit ((↑((localChartDenominatorUnit b c p hb hc)⁻¹) :
      ChartLocalRing b p) ^ d) :=
    ((localChartDenominatorUnit b c p hb hc)⁻¹).isUnit.pow d
  have hbare := (Ideal.unit_mul_mem_iff_mem
    (IsLocalRing.maximalIdeal (ChartLocalRing b p) ^ m) hunit).mp hmap
  exact (AffineMultiplicity.localOrderAtLeast_iff (chartCoordinates b p) m
    (dehomogenize b F)).mp hbare
theorem chart_order_transport {F : MvPolynomial (Fin 3) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) (b c : Fin 3) (p : PlanePoint)
    (hb : p.rep b ≠ 0) (hc : p.rep c ≠ 0) (m : ℕ)
    (hf : AffineMultiplicity.orderAtLeast (chartCoordinates c p) m (dehomogenize c F)) :
    AffineMultiplicity.orderAtLeast (chartCoordinates b p) m (dehomogenize b F) :=
  chart_order_transport_via_residue hF b c p hb hc m
    (AffineMultiplicity.residueEval (chartCoordinates b p))
    (AffineMultiplicity.ker_residueEval (chartCoordinates b p))
    (chartTransition_residueEval b c p hb hc) hf
theorem multiplicityAtLeast_iff_chart {F : MvPolynomial (Fin 3) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) (p : PlanePoint) (c : Fin 3) (hc : p.rep c ≠ 0) (m : ℕ) :
    multiplicityAtLeast F p m ↔
      AffineMultiplicity.orderAtLeast (chartCoordinates c p) m (dehomogenize c F) := by
  constructor
  · intro h
    exact h c hc
  · intro h b hb
    exact chart_order_transport hF b c p hb hc m h
end Nagata.ProjectiveGeometry
end
end
end OAI
-- OAI.AlgebraicGeometry.PlaneCurves.Homogenization
namespace OAI
section
noncomputable section
namespace Nagata.W27
open scoped BigOperators
open MvPolynomial
variable {r : ℕ} {R : Type*} [CommRing R]
def blockOrder (a : (Fin r × Fin 2) →₀ ℕ) (i : Fin r) : ℕ :=
  a (i, 0) + a (i, 1)
def blockDegreeBound (f : MvPolynomial (Fin r × Fin 2) R) (i : Fin r) : ℕ :=
  f.support.sup (fun a => blockOrder a i)
theorem blockOrder_le_bound (f : MvPolynomial (Fin r × Fin 2) R)
    (a : (Fin r × Fin 2) →₀ ℕ) (ha : a ∈ f.support) (i : Fin r) :
    blockOrder a i ≤ blockDegreeBound f i := by
  exact Finset.le_sup (f := fun a => blockOrder a i) ha
def guardedExponent (c : Fin r → Fin 3) (D : Fin r → ℕ)
    (a : (Fin r × Fin 2) →₀ ℕ) : (Fin r × Fin 3) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun ij : Fin r × Fin 3 =>
    Fin.insertNth (α := fun _ : Fin 3 => ℕ) (c ij.1)
      (D ij.1 - blockOrder a ij.1 + 1)
      (fun j => a (ij.1, j)) ij.2
@[simp] theorem guardedExponent_same (c : Fin r → Fin 3) (D : Fin r → ℕ)
    (a : (Fin r × Fin 2) →₀ ℕ) (i : Fin r) :
    guardedExponent c D a (i, c i) = D i - blockOrder a i + 1 := by
  simp [guardedExponent]
@[simp] theorem guardedExponent_other (c : Fin r → Fin 3) (D : Fin r → ℕ)
    (a : (Fin r × Fin 2) →₀ ℕ) (i : Fin r) (j : Fin 2) :
    guardedExponent c D a (i, (c i).succAbove j) = a (i, j) := by
  simp [guardedExponent]
theorem guardedExponent_block_sum (c : Fin r → Fin 3) (D : Fin r → ℕ)
    (a : (Fin r × Fin 2) →₀ ℕ) (i : Fin r) (ha : blockOrder a i ≤ D i) :
    (∑ j : Fin 3, guardedExponent c D a (i, j)) = D i + 1 := by
  rw [Fin.sum_univ_succAbove _ (c i)]
  simp only [guardedExponent_same, guardedExponent_other, Fin.sum_univ_two]
  unfold blockOrder at *
  omega
def guardedHomogenize (c : Fin r → Fin 3)
    (f : MvPolynomial (Fin r × Fin 2) R) : MvPolynomial (Fin r × Fin 3) R :=
  ∑ a ∈ f.support, monomial (guardedExponent c (blockDegreeBound f) a) (f.coeff a)
theorem guardedHomogenize_homogeneous (c : Fin r → Fin 3)
    (f : MvPolynomial (Fin r × Fin 2) R)
    (b : (Fin r × Fin 3) →₀ ℕ) (hb : b ∈ (guardedHomogenize c f).support)
    (i : Fin r) : (∑ j : Fin 3, b (i, j)) = blockDegreeBound f i + 1 := by
  classical
  have hcoeff : (guardedHomogenize c f).coeff b ≠ 0 := mem_support_iff.mp hb
  simp only [guardedHomogenize, coeff_sum] at hcoeff
  obtain ⟨a, ha, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hcoeff
  have heq : guardedExponent c (blockDegreeBound f) a = b := by
    by_contra hne
    exact hterm (by simp [coeff_monomial, hne])
  rw [← heq]
  exact guardedExponent_block_sum c _ a i (blockOrder_le_bound f a ha i)
theorem eval_guardedHomogenize_zero (c : Fin r → Fin 3)
    (f : MvPolynomial (Fin r × Fin 2) R) (v : Fin r × Fin 3 → R)
    (i : Fin r) (hi : v (i, c i) = 0) :
    eval v (guardedHomogenize c f) = 0 := by
  classical
  simp only [guardedHomogenize, map_sum]
  apply Finset.sum_eq_zero
  intro a ha
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  apply mul_eq_zero_of_right
  apply Finset.prod_eq_zero (Finset.mem_univ (i, c i))
  rw [guardedExponent_same, hi]
  exact zero_pow (by omega)
theorem eval_guardedHomogenize_normalized (c : Fin r → Fin 3)
    (f : MvPolynomial (Fin r × Fin 2) R) (v : Fin r × Fin 3 → R)
    (hv : ∀ i, v (i, c i) = 1) :
    eval v (guardedHomogenize c f) =
      eval (fun ij => v (ij.1, (c ij.1).succAbove ij.2)) f := by
  classical
  rw [eval_eq' _ f]
  simp only [guardedHomogenize, map_sum, eval_monomial]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fintype.prod_prod_type, Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Fin.prod_univ_succAbove _ (c i)]
  simp only [guardedExponent_same, guardedExponent_other, hv, one_pow, one_mul]
theorem eval_guardedHomogenize_scale (c : Fin r → Fin 3)
    (f : MvPolynomial (Fin r × Fin 2) R)
    (a : Fin r → R) (v : Fin r × Fin 3 → R) :
    eval (fun ij => a ij.1 * v ij) (guardedHomogenize c f) =
      (∏ i, a i ^ (blockDegreeBound f i + 1)) * eval v (guardedHomogenize c f) := by
  classical
  simp only [eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [mul_pow, Finset.prod_mul_distrib]
  have hprod : (∏ ij : Fin r × Fin 3, a ij.1 ^ b ij) =
      ∏ i, a i ^ (blockDegreeBound f i + 1) := by
    rw [Fintype.prod_prod_type]
    apply Finset.prod_congr rfl
    intro i hi
    change (∏ j : Fin 3, a i ^ b (i, j)) = a i ^ (blockDegreeBound f i + 1)
    rw [Finset.prod_pow_eq_pow_sum, guardedHomogenize_homogeneous c f b hb i]
  rw [hprod]
  ac_rfl
theorem eval_guardedHomogenize_chart {K : Type*} [Field K]
    (c : Fin r → Fin 3) (f : MvPolynomial (Fin r × Fin 2) K)
    (v : Fin r × Fin 3 → K) (hv : ∀ i, v (i, c i) ≠ 0) :
    eval v (guardedHomogenize c f) =
      (∏ i, v (i, c i) ^ (blockDegreeBound f i + 1)) *
        eval (fun ij => v (ij.1, (c ij.1).succAbove ij.2) / v (ij.1, c ij.1)) f := by
  have h := eval_guardedHomogenize_scale c f
    (fun i => v (i, c i)) (fun ij => v ij / v (ij.1, c ij.1))
  have heq : (fun ij : Fin r × Fin 3 =>
      v (ij.1, c ij.1) * (v ij / v (ij.1, c ij.1))) = v := by
    funext ij
    exact mul_div_cancel₀ _ (hv ij.1)
  rw [heq] at h
  rw [eval_guardedHomogenize_normalized c f
    (fun ij => v ij / v (ij.1, c ij.1)) (fun i => div_self (hv i))] at h
  exact h
theorem eval_guardedHomogenize_eq_zero_iff {K : Type*} [Field K]
    (c : Fin r → Fin 3) (f : MvPolynomial (Fin r × Fin 2) K)
    (v : Fin r × Fin 3 → K) (hv : ∀ i, v (i, c i) ≠ 0) :
    eval v (guardedHomogenize c f) = 0 ↔
      eval (fun ij => v (ij.1, (c ij.1).succAbove ij.2) / v (ij.1, c ij.1)) f = 0 := by
  rw [eval_guardedHomogenize_chart c f v hv]
  have hfactor : (∏ i, v (i, c i) ^ (blockDegreeBound f i + 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (hv i)
  exact mul_eq_zero.trans (or_iff_right hfactor)
end Nagata.W27
end
end
end OAI
-- OAI.AlgebraicGeometry.PlaneCurves.Avoidance
namespace OAI
section
namespace Nagata.Workers.W25
abbrev IncidenceIndex (r : ℕ) := {d : ℕ // 0 < d} × (Fin r → ℕ)
end Nagata.Workers.W25
end
section
noncomputable section
namespace Nagata.Workers.W25
open Nagata.ProjectiveGeometry
theorem exists_nonzero_equation_of_proper_closed {r : ℕ}
    (S : Set (OrderedDistinctPoints r)) (hclosed : IsConfigurationZariskiClosed S)
    (hproper : S ≠ Set.univ) :
    ∃ F : MultihomogeneousEquation r, F.polynomial ≠ 0 ∧
      ∀ P ∈ S, equationVanishes F P.val := by
  classical
  obtain ⟨T, ⟨E, hE⟩, hST⟩ := hclosed
  have hex : ∃ P : OrderedDistinctPoints r, P ∉ S := by
    by_contra h
    apply hproper
    ext P
    simp only [Set.mem_univ, iff_true]
    by_contra hp
    exact h ⟨P, hp⟩
  obtain ⟨P, hP⟩ := hex
  have hnot : ¬ ∀ F ∈ E, equationVanishes F P.val := by
    intro h
    exact hP ((hST P).mpr ((hE P.val).mpr h))
  push Not at hnot
  obtain ⟨F, hFE, hF⟩ := hnot
  refine ⟨F, ?_, fun Q hQ => (hE Q.val).mp ((hST Q).mp hQ) F hFE⟩
  intro hzero
  apply hF
  intro v hv hrep
  simp [hzero]
end Nagata.Workers.W25
end
end
end OAI
-- OAI.AlgebraicGeometry.PlaneCurves.UniversalReduction
namespace OAI
section
namespace Nagata.W13
open scoped BigOperators
end Nagata.W13
end
section
noncomputable section
namespace Nagata.W13
open ProjectiveGeometry
open scoped BigOperators
end Nagata.W13
end
end
section
noncomputable section
namespace Nagata.W13
open ProjectiveGeometry
open scoped BigOperators
def supportLocus (r : ℕ) (i : Workers.W25.IncidenceIndex r) :
    Set (OrderedDistinctPoints r) :=
  {p | ∃ F : MvPolynomial (Fin 3) ℂ,
    F ≠ 0 ∧ F.IsHomogeneous i.1.val ∧
      ∀ j, multiplicityAtLeast F (p.val j) (i.2 j)}
end Nagata.W13
end
end
section
noncomputable section
namespace Nagata.W13
open ProjectiveGeometry
open scoped BigOperators
end Nagata.W13
end
end
end OAI
-- OAI.AlgebraicGeometry.PlaneCurves.Incidence
namespace OAI
section
namespace Nagata.Workers.W25
theorem guarded_chart_gluing {C X : Type*} {I : C → Type*}
    (U : C → X → Prop) (Z : (c : C) → I c → X → Prop) (S : X → Prop)
    (hcover : ∀ x, ∃ c, U c x)
    (houtside : ∀ c e x, ¬ U c x → Z c e x)
    (hlocal : ∀ c x, U c x → (S x ↔ ∀ e, Z c e x)) :
    ∀ x, S x ↔ ∀ c e, Z c e x := by
  intro x
  constructor
  · intro hS c e
    by_cases hU : U c x
    · exact (hlocal c x hU).mp hS e
    · exact houtside c e x hU
  · intro hZ
    obtain ⟨c, hc⟩ := hcover x
    exact (hlocal c x hc).mpr (hZ c)
end Nagata.Workers.W25
end
section
noncomputable section
namespace Nagata.ProjectiveGeometry
open scoped BigOperators
def guardedEquation {r : ℕ} (c : ConfigurationChart r)
    (f : MvPolynomial (Fin r × Fin 2) ℂ) : MultihomogeneousEquation r where
  polynomial := W27.guardedHomogenize c f
  multidegree := fun i => W27.blockDegreeBound f i + 1
  homogeneous := W27.guardedHomogenize_homogeneous c f
theorem guardedEquation_vanishes_outside {r : ℕ} (c : ConfigurationChart r)
    (f : MvPolynomial (Fin r × Fin 2) ℂ) (p : Fin r → PlanePoint)
    (hp : ¬ InConfigurationChart c p) : equationVanishes (guardedEquation c f) p := by
  rw [equationVanishes_iff_eval_rep]
  obtain ⟨i, hi⟩ := Classical.not_forall.mp hp
  exact W27.eval_guardedHomogenize_zero c f (fun ij => (p ij.1).rep ij.2) i
    (Classical.not_not.mp hi)
theorem guardedEquation_vanishes_iff {r : ℕ} (c : ConfigurationChart r)
    (f : MvPolynomial (Fin r × Fin 2) ℂ) (p : Fin r → PlanePoint)
    (hp : InConfigurationChart c p) :
    equationVanishes (guardedEquation c f) p ↔
      MvPolynomial.eval (configurationChartCoordinates₂ c p) f = 0 := by
  rw [equationVanishes_iff_eval_rep]
  exact W27.eval_guardedHomogenize_eq_zero_iff c f
    (fun ij => (p ij.1).rep ij.2) hp
def productCommonZeroLocus {r : ℕ} {ι : Type*}
    (F : ι → MultihomogeneousEquation r) : Set (Fin r → PlanePoint) :=
  {p | ∀ i, equationVanishes (F i) p}
theorem isProductZariskiClosed_commonZeroLocus {r : ℕ} {ι : Type*}
    (F : ι → MultihomogeneousEquation r) :
    IsProductZariskiClosed (productCommonZeroLocus F) := by
  refine ⟨Set.range F, ?_⟩
  intro p
  constructor
  · intro hp G hG
    obtain ⟨i, rfl⟩ := hG
    exact hp i
  · intro hp i
    exact hp (F i) ⟨i, rfl⟩
theorem configurationClosed_of_guarded_equations {r : ℕ}
    {I : ConfigurationChart r → Type*}
    (G : (c : ConfigurationChart r) → I c → MultihomogeneousEquation r)
    (S : Set (OrderedDistinctPoints r))
    (houtside : ∀ c e (p : OrderedDistinctPoints r),
      ¬ InConfigurationChart c p.val → equationVanishes (G c e) p.val)
    (hlocal : ∀ c p, InConfigurationChart c p.val →
      (p ∈ S ↔ ∀ e, equationVanishes (G c e) p.val)) :
    IsConfigurationZariskiClosed S := by
  let F : (Σ c, I c) → MultihomogeneousEquation r := fun ce => G ce.1 ce.2
  refine ⟨productCommonZeroLocus F, isProductZariskiClosed_commonZeroLocus F, ?_⟩
  intro p
  have hglue := Workers.W25.guarded_chart_gluing
    (fun c (q : OrderedDistinctPoints r) => InConfigurationChart c q.val)
    (fun c e (q : OrderedDistinctPoints r) => equationVanishes (G c e) q.val)
    (fun q => q ∈ S)
    (fun q => configurationChart_cover q.val) houtside hlocal p
  constructor
  · intro hp ce
    exact hglue.mp hp ce.1 ce.2
  · intro hp
    exact hglue.mpr (fun c e => hp ⟨c, e⟩)
theorem configurationClosed_of_chart_polynomial_equations {r : ℕ}
    {I : ConfigurationChart r → Type*}
    (f : (c : ConfigurationChart r) → I c → MvPolynomial (Fin r × Fin 2) ℂ)
    (S : Set (OrderedDistinctPoints r))
    (hlocal : ∀ c p, InConfigurationChart c p.val →
      (p ∈ S ↔ ∀ e, MvPolynomial.eval (configurationChartCoordinates₂ c p.val) (f c e) = 0)) :
    IsConfigurationZariskiClosed S := by
  apply configurationClosed_of_guarded_equations (fun c e => guardedEquation c (f c e)) S
  · intro c e p hp
    exact guardedEquation_vanishes_outside c (f c e) p.val hp
  · intro c p hp
    exact (hlocal c p hp).trans
      (forall_congr' fun e => (guardedEquation_vanishes_iff c (f c e) p.val hp).symm)
end Nagata.ProjectiveGeometry
end
end
section
noncomputable section
open Classical
namespace Nagata.ProjectiveGeometry
theorem multiplicityAtLeast_iff_directChart {F : MvPolynomial (Fin 3) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) (p : PlanePoint) (c : Fin 3) (hc : p.rep c ≠ 0) (m : ℕ) :
    multiplicityAtLeast F p m ↔
      AffineMultiplicity.orderAtLeast (chartCoordinates₂ c p) m (W27.directChartHom c F) := by
  apply (multiplicityAtLeast_iff_chart hF p c hc m).trans
  simpa only [chartDehomogenize₂_eq_eval₂_insertNth, W27.directChartHom,
    MvPolynomial.coe_eval₂Hom] using
    (orderAtLeast_chartDehomogenize₂_iff c p F m).symm
theorem supportLocus_iff_chart_minors (r : ℕ) (index : Workers.W25.IncidenceIndex r)
    (c : ConfigurationChart r) (p : OrderedDistinctPoints r)
    (hp : InConfigurationChart c p.val) :
    p ∈ W13.supportLocus r index ↔
      ∀ s : W27.HomogeneousMonomial index.1.val → W27.PlaneJet r index.2,
        MvPolynomial.eval (configurationChartCoordinates₂ c p.val)
          (W27.minorPolynomial (W27.chartPlaneJetMatrix (R := ℂ) c index.1.val index.2) s) = 0 := by
  classical
  have hforms : p ∈ W13.supportLocus r index ↔
      ∃ F : MvPolynomial.homogeneousSubmodule (Fin 3) ℂ index.1.val,
        F.val ≠ 0 ∧ ∀ i,
          AffineMultiplicity.orderAtLeast
            (fun j => configurationChartCoordinates₂ c p.val (i, j)) (index.2 i)
            (W27.directChartHom (c i) F.val) := by
    constructor
    · rintro ⟨F, hFne, hFhom, hForder⟩
      refine ⟨⟨F, hFhom⟩, hFne, ?_⟩
      intro i
      exact (multiplicityAtLeast_iff_directChart hFhom (p.val i) (c i) (hp i)
        (index.2 i)).mp (hForder i)
    · rintro ⟨F, hFne, hForder⟩
      refine ⟨F.val, hFne, F.property, ?_⟩
      intro i
      exact (multiplicityAtLeast_iff_directChart F.property (p.val i) (c i) (hp i)
        (index.2 i)).mpr (hForder i)
  exact hforms.trans (W27.exists_nonzero_form_iff_chart_minors c index.1.val index.2
    (configurationChartCoordinates₂ c p.val))
theorem supportLocus_isConfigurationZariskiClosed (r : ℕ)
    (index : Workers.W25.IncidenceIndex r) :
    IsConfigurationZariskiClosed (W13.supportLocus r index) := by
  classical
  apply configurationClosed_of_chart_polynomial_equations
    (fun c s => W27.minorPolynomial
      (W27.chartPlaneJetMatrix (R := ℂ) c index.1.val index.2) s)
    (W13.supportLocus r index)
  intro c p hp
  exact supportLocus_iff_chart_minors r index c p hp
end Nagata.ProjectiveGeometry
end
end
section
noncomputable section
namespace Nagata.W13
open ProjectiveGeometry
open scoped BigOperators
end Nagata.W13
end
end
end OAI
namespace OAI.Nagata.W13
open Workers.W14
theorem square_exclusion {r d : ℕ} (hr : 10 ≤ r) (sq : IsSquare r) (hd : 0 < d) (m : Fin r → ℕ)
    (hbad : (d : ℝ) * Real.sqrt r ≤ ∑ i, (m i : ℝ)) : ¬ UniversalSupport r d m := by
  intro hu
  have hr0 : 0 < r := by omega
  let D := r.factorial*d
  let M := (r-1).factorial * ∑ i, m i
  have har := factorial_symmetrization hr0 hd (s := ∑ i, m i) (by simpa using hbad)
  have hm : 0 < M := har.2.1
  have hs : (D : ℝ)/M ≤ Real.sqrt r := har.2.2
  have u : UniversalSupport r D (fun _ => M) := universalSupport_symmetrize hr0 hu
  obtain ⟨k, hk⟩ := sq
  have hl := (square_ratio_le_iff hk hm).mp hs
  exact (Nat.not_lt_of_ge hl) (Workers.W24.square_universalSupport_degree_gt k D M (square_root_ge_four hr hk) hm (hk ▸ u))
end OAI.Nagata.W13
namespace OMA.S_wp_nagata_s_conjecture_on_curves
open OAI.Nagata OAI.Nagata.ProjectiveGeometry MvPolynomial
theorem affine_order_bridge (p : Fin 2 → ℂ) (m : ℕ) (F : PlanePoly)
    (h : F ∈ pointIdeal p ^ m) : OAI.Nagata.AffineMultiplicity.orderAtLeast p m F := by
  have hle : pointIdeal p ≤ OAI.Nagata.AffineMultiplicity.pointIdeal p := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact OAI.Nagata.AffineMultiplicity.coordinate_difference_mem p i
  exact (Ideal.pow_right_mono hle m) h

/-- Lift each affine monomial to degree `F.totalDegree` by padding with X₀. -/
theorem affine_homogeneous_lift (F : PlanePoly) : ∃ G : MvPolynomial (Fin 3) ℂ,
    G.IsHomogeneous F.totalDegree ∧ W27.directChartHom 0 G = F := by
  classical
  let term (a : Fin 2 →₀ ℕ) : MvPolynomial (Fin 3) ℂ :=
    C (coeff a F) * X 0 ^ (F.totalDegree - (a 0 + a 1)) * X 1 ^ a 0 * X 2 ^ a 1
  refine ⟨∑ a ∈ F.support, term a, IsHomogeneous.sum _ _ _ ?_, ?_⟩
  · intro a ha
    have le := le_totalDegree ha
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at le
    have hh := (((isHomogeneous_C (Fin 3) (coeff a F)).mul
      ((isHomogeneous_X ℂ (0 : Fin 3)).pow (F.totalDegree - (a 0 + a 1)))).mul
      ((isHomogeneous_X ℂ (1 : Fin 3)).pow (a 0))).mul ((isHomogeneous_X ℂ (2 : Fin 3)).pow (a 1))
    convert hh using 1; omega
  · rw [map_sum]
    conv_rhs => rw [F.as_sum]
    apply Finset.sum_congr rfl
    intro a _
    simp [term, W27.directChartHom, monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two, mul_assoc]
    exact Or.inl rfl

end OMA.S_wp_nagata_s_conjecture_on_curves

namespace OMA.S_wp_nagata_s_conjecture_on_curves
open OAI.Nagata OAI.Nagata.ProjectiveGeometry MvPolynomial

theorem affine_bad_equation {r : ℕ} (hr : 10 ≤ r) (sq : IsSquare r) (d : ℕ) (m : Fin r → ℕ)
    (hd : 0 < d) (hb : (d : ℝ)*Real.sqrt r ≤ ∑ i, (m i : ℝ)) :
    ∃ q : MvPolynomial (Fin r × Fin 2) ℂ, q ≠ 0 ∧
      ∀ p : Fin r → Fin 2 → ℂ, Function.Injective p → ∀ F : PlanePoly, F ≠ 0 →
      F.totalDegree = d → (∀ i, F ∈ pointIdeal (p i) ^ m i) →
      MvPolynomial.eval (fun ij => p ij.1 ij.2) q = 0 := by
  let t : Workers.W25.IncidenceIndex r := (⟨d, hd⟩, m)
  have prop : W13.supportLocus r t ≠ Set.univ := by
    intro h
    apply W13.square_exclusion hr sq hd m hb
    intro P
    exact Set.eq_univ_iff_forall.mp h P
  obtain ⟨Q, hn, hv⟩ := Workers.W25.exists_nonzero_equation_of_proper_closed _
    (supportLocus_isConfigurationZariskiClosed r t) prop
  refine ⟨W16.blockDehomogenize Q, W16.blockDehomogenize_ne_zero Q hn, ?_⟩
  intro p hp F hF hdeg hm
  let P : OrderedDistinctPoints r := ⟨affinePlanePoint ∘ p, affinePlanePoint_injective.comp hp⟩
  obtain ⟨G, hg, he⟩ := affine_homogeneous_lift F
  have hP : P ∈ W13.supportLocus r t := by
    refine ⟨G, fun hz => hF (by simpa [hz] using he.symm), by change G.IsHomogeneous d; rwa [← hdeg], ?_⟩
    intro i
    have hc : (affinePlanePoint (p i)).rep 0 ≠ 0 :=
      (mk_rep_coordinate_ne_zero_iff _ _ _).mpr (by simp [affinePlaneVector])
    apply (multiplicityAtLeast_iff_directChart hg _ 0 hc _).mpr
    have hz : chartCoordinates₂ 0 (affinePlanePoint (p i)) = p i := by
      funext j
      change chartCoordinates 0 (Projectivization.mk ℂ _ _) _ = _
      rw [chartCoordinates_mk]
      fin_cases j <;> simp [affinePlaneVector]
    rw [he, hz]
    exact affine_order_bridge _ _ _ (hm i)
  rw [W16.eval_blockDehomogenize]
  exact hv P hP (fun i => affinePlaneVector (p i)) (fun i => affinePlaneVector_ne_zero _) (fun _ => rfl)

end OMA.S_wp_nagata_s_conjecture_on_curves
theorem OMA.solution : OMA.R_wp_nagata_s_conjecture_on_curves_R1.H2 := fun _ hr sq => OMA.S_wp_nagata_s_conjecture_on_curves.affine_bad_equation hr sq
