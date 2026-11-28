import FormalConjectures.OpenQuantumProblems.«23»
import Mathlib

-- Adapted from @marcusbuffett, open-math-agents PRs 3870 and 4880.
-- Finite Weyl and Galois conversion ported from Yaoling Yang,
-- Hertaspace/sic-povm-lean at e74571352233162adee70895903d82f8465fd054, Apache-2.0.
-- Mathematics by Radchenko–Wheeler and Appleby–Flammia–Kopp.
-- For d = 70, the analytic input is the restriction in SICLean.L2a.Inputs
-- supplied by the convolution identity and the common embedding of Stark reciprocity.
-- The attracting unit has discriminant (d-1)^2-4 = 4757.
-- Credit: @marcusbuffett

namespace OMA.R_OpenQuantumProblem23_hasSICPOVM_70_R1

open Matrix OpenQuantumProblem23
open scoped BigOperators

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem rank_eq_trace_of_idem (A : Matrix (ι) (ι) ℂ) (hA : A * A = A) :
    ((A.rank : ℕ) : ℂ) = A.trace := by
  have he : IsIdempotentElem A.mulVecLin := by
    apply LinearMap.ext
    intro v
    simp only [Module.End.mul_apply, Matrix.mulVecLin_apply]
    rw [Matrix.mulVec_mulVec, hA]
  have htrL : A.trace = LinearMap.trace ℂ (ι → ℂ) A.mulVecLin := by
    rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (ι))]
    congr 1
    ext i j
    simp [Matrix.mulVecLin, LinearMap.toMatrix]
  have hr : A.rank = Module.finrank ℂ (LinearMap.range A.mulVecLin) := by
    rw [Matrix.rank_eq_finrank_range_toLin A (Pi.basisFun ℂ (ι)) (Pi.basisFun ℂ (ι))]
    rfl
  have hp : LinearMap.IsProj (LinearMap.range A.mulVecLin) A.mulVecLin :=
    LinearMap.IsIdempotentElem.isProj_range A.mulVecLin he
  rw [htrL, LinearMap.IsProj.trace hp, ← hr]


theorem exists_unit_of_rank_one (A : Matrix (ι) (ι) ℂ) (hH : A.IsHermitian)
    (hA : A * A = A) (h1 : A.rank = 1) :
    ∃ ψ : ι → ℂ, ∑ i, Complex.normSq (ψ i) = 1 ∧ ∀ i j, A i j = ψ i * star (ψ j) := by
  have hcj : ∀ k l, A l k = star (A k l) := fun k l => by
    have h1' : Matrix.conjTranspose A l k = A l k := by rw [show Matrix.conjTranspose A = A from hH]
    rw [Matrix.conjTranspose_apply] at h1'
    exact h1'.symm
  have htr : (1 : ℂ) = A.trace := by
    have h2 := rank_eq_trace_of_idem A hA
    rw [h1] at h2
    exact_mod_cast h2
  obtain ⟨k, hk⟩ : ∃ k, A k k ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hz : A.trace = (0:ℂ) := by
      show ∑ i, Matrix.diag A i = 0
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [Matrix.diag_apply]
      exact hcon i
    rw [hz] at htr
    exact absurd htr (by norm_num)
  set u : ι → ℂ := fun i => A i k with hu
  have hAu : A *ᵥ u = u := by
    funext i
    have h2 : (A * A) i k = A i k := congrFun (congrFun hA i) k
    rw [Matrix.mul_apply] at h2
    show ∑ l, A i l * u l = u i
    simpa [hu] using h2
  have hrk : Module.finrank ℂ (LinearMap.range A.mulVecLin) = 1 := by
    have h5 : A.rank = Module.finrank ℂ (LinearMap.range A.mulVecLin) := by
      rw [Matrix.rank_eq_finrank_range_toLin A (Pi.basisFun ℂ (ι)) (Pi.basisFun ℂ (ι))]
      rfl
    rw [← h5]
    exact h1
  have huMem : u ∈ LinearMap.range A.mulVecLin := by
    refine ⟨u, ?_⟩
    show A *ᵥ u = u
    exact hAu
  have hspan : LinearMap.range A.mulVecLin = Submodule.span ℂ {u} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hrk huMem (fun h => hk (congrFun h k))
  have hcol : ∀ j, (fun i => A i j) ∈ LinearMap.range A.mulVecLin := by
    intro j
    refine ⟨Pi.single j (1:ℂ), ?_⟩
    funext i
    show (A *ᵥ Pi.single j (1:ℂ)) i = A i j
    simp [Matrix.mulVec, Matrix.mulVec_single]
  have hdec : ∀ j, ∃ c : ℂ, ∀ i, A i j = c * u i := by
    intro j
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hspan ▸ hcol j)
    exact ⟨c, fun i => by simpa using (congrFun hc i).symm⟩
  have hform : ∀ i j, A i j = A i k * A k j / A k k := by
    intro i j
    obtain ⟨c, hc⟩ := hdec j
    have hik : A i j = c * A i k := hc i
    have hkj : A k j = c * A k k := hc k
    rw [hik, hkj]
    field_simp [hk]
  -- A k k = ofReal (∑ normSq (A k l)), positive
  have hkksum : A k k = ∑ l, ((Complex.normSq (A k l) : ℝ) : ℂ) := by
    have h2 : (A * A) k k = A k k := congrFun (congrFun hA k) k
    rw [Matrix.mul_apply] at h2
    rw [← h2]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hcj k l]
    simp only [Complex.star_def, Complex.mul_conj]
  have hsumnn : 0 ≤ ∑ l, Complex.normSq (A k l) :=
    Finset.sum_nonneg (fun l _ => Complex.normSq_nonneg _)
  have hrne : (∑ l, Complex.normSq (A k l)) ≠ 0 := by
    intro hz
    apply hk
    rw [hkksum, ← Complex.ofReal_sum, hz]
    simp
  obtain ⟨r, hr0, hrc⟩ : ∃ r : ℝ, 0 < r ∧ ((r : ℂ) = A k k) := by
    refine ⟨∑ l, Complex.normSq (A k l), lt_of_le_of_ne hsumnn (Ne.symm hrne), ?_⟩
    rw [hkksum]
    exact Complex.ofReal_sum _ _
  -- the column sum equals the row sum
  have hcolsum : ∑ i, Complex.normSq (A i k) = r := by
    have h7 : ((∑ i, Complex.normSq (A i k) : ℝ) : ℂ) = A k k := by
      rw [Complex.ofReal_sum, hkksum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hcj k i]
      simp only [Complex.star_def, Complex.normSq_conj]
    exact Complex.ofReal_inj.mp (h7.trans hrc.symm)
  refine ⟨fun i => A i k / ((Real.sqrt r : ℂ)), ?_, ?_⟩
  · have hdiv : ∀ i, Complex.normSq (A i k / ((Real.sqrt r : ℂ)))
        = Complex.normSq (A i k) / r := by
      intro i
      rw [Complex.normSq_div, Complex.normSq_ofReal, Real.mul_self_sqrt hr0.le]
    show ∑ i, Complex.normSq (A i k / ((Real.sqrt r : ℂ))) = 1
    rw [Finset.sum_congr rfl (fun i _ => hdiv i), ← Finset.sum_div, hcolsum, div_self hr0.ne']
  · intro i j
    rw [hform i j, hcj j k, ← hrc]
    show A i k * star (A j k) / ((r : ℝ) : ℂ)
      = A i k / ((Real.sqrt r : ℂ)) * star (A j k / ((Real.sqrt r : ℂ)))
    have hsd : star (A j k / ((Real.sqrt r : ℂ)))
        = star (A j k) / star ((Real.sqrt r : ℂ)) := star_div₀ _ _
    have hs : star ((Real.sqrt r : ℂ)) = ((Real.sqrt r : ℂ)) := by simp
    rw [hsd, hs, div_mul_div_comm]
    congr 1
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hr0.le]


end

-- Existence of the finite array with the restricted convolution and common Galois flip.
def H1 : Prop :=
  let e := fun (t : ZMod 70) => ZMod.stdAddChar t
  let q := fun (i j : ZMod 70) => e (i^2 - i*j + j^2)
  let u : ℝ := (69 + Real.sqrt 4757) / 2
  ∃ (F : ZMod 70 → ZMod 70 → ℂ) (τ : ℂ →+* ℂ),
  F 0 0 = ((Real.sqrt u : ℂ) ^ 3) ∧
  (∀ i j, (i, j) ≠ (0, 0) → F i j * F (-i) (-j) = (q i j)⁻¹) ∧
  (∀ r s, (70 : ℂ)⁻¹ * ∑ i, ∑ j, F i j * F (r-i) (s-j) * q i j * e (-i*r+j*(r-s)) =
      (Real.sqrt 67 : ℂ) * F r s + if (r,s) = (0,0) then 70 else 0) ∧
  (∀ i j, (i,j) ≠ (0,0) → ‖τ (F i j)‖ = 1)

-- The finite algebraic conversion from these values to a rank-one Weyl fiducial.
def H2 : Prop :=
  let e := fun (t : ZMod 70) => ZMod.stdAddChar t
  let q := fun (i j : ZMod 70) => e (i^2 - i*j + j^2)
  let u : ℝ := (69 + Real.sqrt 4757) / 2
  ∀ (F : ZMod 70 → ZMod 70 → ℂ) (τ : ℂ →+* ℂ),
  F 0 0 = ((Real.sqrt u : ℂ) ^ 3) →
  (∀ i j, (i, j) ≠ (0, 0) → F i j * F (-i) (-j) = (q i j)⁻¹) →
  (∀ r s, (70 : ℂ)⁻¹ * ∑ i, ∑ j, F i j * F (r-i) (s-j) * q i j * e (-i*r+j*(r-s)) =
      (Real.sqrt 67 : ℂ) * F r s + if (r,s) = (0,0) then 70 else 0) →
  (∀ i j, (i,j) ≠ (0,0) → ‖τ (F i j)‖ = 1) →
  ∃ A : Matrix (ZMod 70) (ZMod 70) ℂ, A.IsHermitian ∧ A * A = A ∧ A.trace = 1 ∧
    ∀ a b : ZMod 70, (a,b) ≠ (0,0) →
      Complex.normSq (∑ t, A (t+a) t * e (b*t)) = (71 : ℝ)⁻¹

section

private theorem char_normSq {d : ℕ} [NeZero d] (x : ZMod d) :
    Complex.normSq (ZMod.stdAddChar x) = 1 := by
  exact Circle.normSq_coe (ZMod.toCircle x)

private theorem char_star {d : ℕ} [NeZero d] (x : ZMod d) :
    star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [AddChar.map_neg_eq_inv]
  exact (Circle.coe_inv_eq_conj (ZMod.toCircle x)).symm

private theorem orbit_of_matrix {d : ℕ} [NeZero d]
    (A : Matrix (ZMod d) (ZMod d) ℂ) (hH : A.IsHermitian)
    (hA : A * A = A) (htr : A.trace = 1)
    (hflat : ∀ a b : ZMod d, (a,b) ≠ (0,0) →
      Complex.normSq (∑ t, A (t+a) t * ZMod.stdAddChar (b*t)) = sicOverlapSq d) :
    HasSICPOVM d := by
  classical
  have hrank : A.rank = 1 := by
    have h := (rank_eq_trace_of_idem A hA).trans htr
    exact_mod_cast h
  obtain ⟨v, hv, hAv⟩ := exists_unit_of_rank_one A hH hA hrank
  let coord : Fin d ≃ ZMod d := Fintype.equivOfCardEq (by simp)
  let label : Fin (d^2) ≃ ZMod d × ZMod d := Fintype.equivOfCardEq (by simp [pow_two])
  let w (p : ZMod d × ZMod d) (t : ZMod d) := ZMod.stdAddChar (p.2*t) * v (t+p.1)
  refine ⟨fun j => mkStateVector (fun i => w (label j) (coord i)), ?_, ?_⟩
  · intro j
    have unit : ∑ i : Fin d, Complex.normSq (w (label j) (coord i)) = 1 := by
      rw [coord.sum_comp (fun t => Complex.normSq (w (label j) t))]
      simp only [w, Complex.normSq_mul, char_normSq, one_mul]
      exact (Equiv.sum_comp (Equiv.addRight (label j).1) (fun t => Complex.normSq (v t))).trans hv
    have hn : ‖mkStateVector (fun i => w (label j) (coord i))‖ ^ 2 = 1 := by
      simpa only [PiLp.norm_sq_eq_of_L2, Complex.sq_norm] using unit
    unfold IsNormalized
    nlinarith [norm_nonneg (mkStateVector (fun i => w (label j) (coord i)))]
  · intro j k hjk
    let p := label j
    let q := label k
    let a := q.1-p.1
    let b := q.2-p.2
    have hab : (a,b) ≠ (0,0) := by
      intro h
      apply hjk
      apply label.injective
      change p = q
      exact Prod.ext (sub_eq_zero.mp (congrArg Prod.fst h)).symm
        (sub_eq_zero.mp (congrArg Prod.snd h)).symm
    let f := fun t => A (t+a) t * ZMod.stdAddChar (b*t)
    have he (t) : star (w p t) * w q t =
        ZMod.stdAddChar (-(b*p.1)) * f (t+p.1) := by
      have heq : -(p.2*t) + q.2*t = -(b*p.1) + b*(t+p.1) := by dsimp [b]; ring
      have hx : t+p.1+a = t+q.1 := by dsimp [a]; abel
      simp only [w, f, star_mul, char_star, hAv, hx]
      calc
        _ = (ZMod.stdAddChar (-(p.2*t)) * ZMod.stdAddChar (q.2*t)) *
            (v (t+q.1) * star (v (t+p.1))) := by ring
        _ = _ := by
          rw [← AddChar.map_add_eq_mul, heq, AddChar.map_add_eq_mul]
          ring
    change Complex.normSq (∑ i, star (w p (coord i)) * w q (coord i)) = sicOverlapSq d
    rw [show (∑ i, star (w p (coord i)) * w q (coord i)) =
      ∑ t, star (w p t) * w q t from coord.sum_comp (fun t => star (w p t) * w q t)]
    simp_rw [he]
    have htranslate : (∑ t, f (t+p.1)) = ∑ t, f t := Equiv.sum_comp (Equiv.addRight p.1) f
    rw [← Finset.mul_sum, htranslate, Complex.normSq_mul, char_normSq, one_mul]
    exact hflat a b hab

end

theorem main : H1 → H2 → type_of% @OpenQuantumProblem23.hasSICPOVM_70 := by
  rintro ⟨F, τ, hzero, hreflect, hconv, hcircle⟩ h2
  obtain ⟨A, hH, hA, htr, hflat⟩ := h2 F τ hzero hreflect hconv hcircle
  apply orbit_of_matrix A hH hA htr
  intro a b hab
  convert hflat a b hab using 1 <;> norm_num [sicOverlapSq]

end OMA.R_OpenQuantumProblem23_hasSICPOVM_70_R1
