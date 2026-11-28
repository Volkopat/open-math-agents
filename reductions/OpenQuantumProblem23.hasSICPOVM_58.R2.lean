import FormalConjectures.OpenQuantumProblems.«23»
import Mathlib

/-! Restrict the full dimension-58 pentagon to its 58-torsion subgroup,
then apply the finite Weyl descent of the dimension-58 R1 reduction. -/

-- The rank-one projector factorization is from Yaoling Yang's SICLean.WHBasic
-- (Apache-2.0), as adapted in @marcusbuffett's merged dimension-68 reduction.
-- The orbit proof also follows that reduction, with a general additive character.
-- The finite descent follows the construction of Radchenko and Wheeler,
-- Real quadratic fields and finite quantum dilogarithms I, Section 4.4,
-- arXiv:2609.21892, and Stark units for real quadratic fields and
-- reciprocity laws, Proposition 7.

namespace OMA.R_OpenQuantumProblem23_hasSICPOVM_58_R2

open Matrix OpenQuantumProblem23
open scoped BigOperators

noncomputable section

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem rank_eq_trace_of_idem (A : Matrix (ι) (ι) ℂ) (hA : A * A = A) :
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


private theorem exists_unit_of_rank_one (A : Matrix (ι) (ι) ℂ) (hH : A.IsHermitian)
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
    push Not at hcon
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
    simp [Matrix.mulVec]
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

private theorem orbit_of_matrix {d : ℕ} [NeZero d]
    (e : AddChar (ZMod d) ℂ)
    (enorm : ∀ t, Complex.normSq (e t) = 1)
    (estar : ∀ t, star (e t) = e (-t))
    (A : Matrix (ZMod d) (ZMod d) ℂ) (hH : A.IsHermitian)
    (hA : A * A = A) (htr : A.trace = 1)
    (hflat : ∀ a b : ZMod d, (a,b) ≠ (0,0) →
      Complex.normSq (∑ t, A (t+a) t * e (b*t)) = sicOverlapSq d) :
    HasSICPOVM d := by
  classical
  have hrank : A.rank = 1 := by
    have h := (rank_eq_trace_of_idem A hA).trans htr
    exact_mod_cast h
  obtain ⟨v, hv, hAv⟩ := exists_unit_of_rank_one A hH hA hrank
  let coord : Fin d ≃ ZMod d := Fintype.equivOfCardEq (by simp)
  let label : Fin (d^2) ≃ ZMod d × ZMod d := Fintype.equivOfCardEq (by simp [pow_two])
  let w (p : ZMod d × ZMod d) (t : ZMod d) := e (p.2*t) * v (t+p.1)
  refine ⟨fun j => mkStateVector (fun i => w (label j) (coord i)), ?_, ?_⟩
  · intro j
    have unit : ∑ i : Fin d, Complex.normSq (w (label j) (coord i)) = 1 := by
      rw [coord.sum_comp (fun t => Complex.normSq (w (label j) t))]
      simp only [w, Complex.normSq_mul, enorm, one_mul]
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
    let f := fun t => A (t+a) t * e (b*t)
    have he (t) : star (w p t) * w q t =
        e (-(b*p.1)) * f (t+p.1) := by
      have heq : -(p.2*t) + q.2*t = -(b*p.1) + b*(t+p.1) := by dsimp [b]; ring
      have hx : t+p.1+a = t+q.1 := by dsimp [a]; abel
      simp only [w, f, star_mul, estar, hAv, hx]
      calc
        _ = (e (-(p.2*t)) * e (q.2*t)) *
            (v (t+q.1) * star (v (t+p.1))) := by ring
        _ = _ := by
          rw [← AddChar.map_add_eq_mul, heq, AddChar.map_add_eq_mul]
          ring
    change Complex.normSq (∑ i, star (w p (coord i)) * w q (coord i)) = sicOverlapSq d
    rw [show (∑ i, star (w p (coord i)) * w q (coord i)) =
      ∑ t, star (w p t) * w q t from coord.sum_comp (fun t => star (w p t) * w q t)]
    simp_rw [he]
    have htranslate : (∑ t, f (t+p.1)) = ∑ t, f t := Equiv.sum_comp (Equiv.addRight p.1) f
    rw [← Finset.mul_sum, htranslate, Complex.normSq_mul, enorm, one_mul]
    exact hflat a b hab


private abbrev R := ZMod 58
private abbrev M := Matrix R R ℂ

private def weyl (e : AddChar R ℂ) (f : R → R → ℂ) : M :=
  fun x y => (58 : ℂ)⁻¹ * ∑ b, f (x-y) b * e (b*y)

private def conv (e : AddChar R ℂ) (f : R → R → ℂ) (r s : R) : ℂ :=
  (58 : ℂ)⁻¹ * ∑ a, ∑ b, f a b * f (r-a) (s-b) * e (b*(r-a))

set_option maxHeartbeats 1000000 in
private theorem weyl_mul (e : AddChar R ℂ) (f : R → R → ℂ) :
    weyl e f * weyl e f = weyl e (conv e f) := by
  classical
  ext x y
  rw [Matrix.mul_apply]
  simp only [weyl, conv]
  let c : ℂ := (58 : ℂ)⁻¹
  let r : R := x-y
  let term (a b s : R) : ℂ := f a b * f (r-a) (s-b) * e (b*(r-a)) * e (s*y)
  have ht (z b j : R) :
      f (x-z) b * e (b*z) * (f (z-y) j * e (j*y)) = term (x-z) b (j+b) := by
    dsimp [term, r]
    rw [show x-y-(x-z) = z-y by abel, add_sub_cancel_right]
    rw [mul_assoc, mul_left_comm (e (b*z)), ← mul_assoc, ← AddChar.map_add_eq_mul]
    rw [mul_assoc (f (x - z) b * f (z - y) j), ← AddChar.map_add_eq_mul]
    congr 1
    ring
  calc
    ∑ z : R, (c * ∑ b, f (x-z) b * e (b*z)) * (c * ∑ j, f (z-y) j * e (j*y)) =
        c * c * ∑ z : R, ∑ b, ∑ j, term (x-z) b (j+b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      rw [mul_mul_mul_comm, Finset.sum_mul]
      simp_rw [Finset.mul_sum, ht]
    _ = c * c * ∑ a : R, ∑ b, ∑ s, term a b s := by
      congr 1
      calc
        ∑ z : R, ∑ b, ∑ j, term (x-z) b (j+b) =
            ∑ z : R, ∑ b, ∑ s, term (x-z) b s := by
          apply Finset.sum_congr rfl
          intro z _
          apply Finset.sum_congr rfl
          intro b _
          exact Equiv.sum_comp (Equiv.addRight b) (term (x-z) b)
        _ = _ := by
          simpa only [Equiv.trans_apply, Equiv.neg_apply, Equiv.coe_addLeft, ← sub_eq_add_neg]
            using Equiv.sum_comp ((Equiv.neg R).trans (Equiv.addLeft x))
              (fun a => ∑ b, ∑ s, term a b s)
    _ = c * ∑ s : R, (c * ∑ a : R, ∑ b, f a b * f (r-a) (s-b) *
          e (b*(r-a))) * e (s*y) := by
      have hswap : (∑ a, ∑ b, ∑ s, term a b s) = ∑ s, ∑ a, ∑ b, term a b s := by
        rw [show (∑ a, ∑ b, ∑ s, term a b s) = ∑ a, ∑ s, ∑ b, term a b s by
          exact Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
        exact Finset.sum_comm
      rw [hswap]
      rw [mul_assoc, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro s _
      simp only [term, ← Finset.sum_mul]
      ring

private theorem char_orth (e : AddChar R ℂ) (hinj : Function.Injective e) (b : R) :
    ∑ t : R, e (b*t) = if b = 0 then (58 : ℂ) else 0 := by
  classical
  by_cases hb : b = 0
  · subst b
    simp
  · rw [if_neg hb]
    let ψ : AddChar R ℂ := e.compAddMonoidHom (AddMonoidHom.mulLeft b)
    change ∑ t, ψ t = 0
    refine ψ.sum_eq_zero_iff_ne_zero.mpr ?_
    intro hψ
    apply hb
    apply hinj
    have h := congrArg (fun c : AddChar R ℂ => c 1) hψ
    simpa [ψ] using h

private theorem weyl_coeff (e : AddChar R ℂ) (hinj : Function.Injective e)
    (f : R → R → ℂ) (a b : R) :
    ∑ t, weyl e f (t+a) t * e (b*t) = f a (-b) := by
  classical
  simp only [weyl, add_sub_cancel_left, mul_assoc, Finset.sum_mul, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← AddChar.map_add_eq_mul, ← add_mul, ← Finset.mul_sum, char_orth e hinj,
    ← eq_neg_iff_add_eq_zero, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  field_simp


private def mass (a b : R) : ℂ := if (a,b) = (0,0) then 58 else 0

private theorem weyl_mass (e : AddChar R ℂ) : weyl e mass = 1 := by
  classical
  ext x y
  by_cases h : x = y
  · subst x
    simp [weyl, mass, ite_mul]
  · have hh : x-y ≠ 0 := sub_ne_zero.mpr h
    simp [weyl, mass, h, hh]

private theorem weyl_linear (e : AddChar R ℂ) (f g : R → R → ℂ) (c : ℂ) :
    weyl e (fun a b => c * f a b + g a b) = c • weyl e f + weyl e g := by
  ext x y
  simp only [weyl, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
    mul_assoc, ← Finset.mul_sum, mul_add]
  ring

private theorem trace_weyl (e : AddChar R ℂ) (hinj : Function.Injective e)
    (f : R → R → ℂ) : (weyl e f).trace = f 0 0 := by
  have h := weyl_coeff e hinj f 0 0
  simpa [Matrix.trace, Matrix.diag] using h

private theorem weyl_hermitian (e : AddChar R ℂ) (f : R → R → ℂ)
    (hchar : ∀ t, star (e t) = e (-t))
    (hf : ∀ a b, star (f (-a) (-b)) = f a b * e (-(a*b))) :
    (weyl e f).IsHermitian := by
  classical
  show (weyl e f).conjTranspose = weyl e f
  ext x y
  simp only [Matrix.conjTranspose_apply, weyl, star_mul', star_inv₀, star_ofNat,
    star_sum, hchar]
  congr 1
  calc
    ∑ b : R, star (f (y-x) b) * e (-(b*x)) =
        ∑ b : R, star (f (y-x) (-b)) * e (-((-b)*x)) := by
      symm
      exact Equiv.sum_comp (Equiv.neg R) (fun b => star (f (y-x) b) * e (-(b*x)))
    _ = ∑ b : R, f (x-y) b * e (b*y) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [show y-x = -(x-y) by abel, hf, mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      ring

private theorem char_power {n : ℕ} (e : AddChar (ZMod n) ℂ) (x : ZMod n) :
    e x ^ n = 1 := by
  rw [← AddChar.map_nsmul_eq_pow]
  rw [show n • x = 0 by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]]
  exact e.map_zero_eq_one

private theorem char_modulus {n : ℕ} [NeZero n] (e : AddChar (ZMod n) ℂ)
    (x : ZMod n) : ‖e x‖ = 1 := by
  have h := congrArg norm (char_power e x)
  rw [norm_pow, norm_one] at h
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one (NeZero.ne n)).mp (by simpa only [one_pow] using h)

private theorem char_square (e : AddChar R ℂ) (x : R) : Complex.normSq (e x) = 1 := by
  rw [← Complex.sq_norm, char_modulus e x]
  norm_num

private theorem char_conjugate (e : AddChar R ℂ) (x : R) : star (e x) = e (-x) := by
  rw [AddChar.map_neg_eq_inv]
  apply eq_inv_of_mul_eq_one_left
  rw [mul_comm, Complex.star_def, Complex.mul_conj, char_square e x, Complex.ofReal_one]

private theorem star_fixed_of_sq_pos (z : ℂ) (c : ℝ) (hc : 0 < c)
    (hz : z^2 = (c : ℂ)) : star z = z := by
  have hr := congrArg Complex.re hz
  have hi := congrArg Complex.im hz
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at hr hi
  have hnil : z.re * z.im = 0 := by nlinarith
  have hzero : z.im = 0 := by
    rcases mul_eq_zero.mp hnil with h | h
    · rw [h] at hr
      nlinarith [sq_nonneg z.im]
    · exact h
  apply Complex.ext <;> simp [hzero]

private theorem projection_idempotent (B : M) (t u : ℂ) (htu : t*u = 1) (hL : t+u ≠ 0)
    (hB : B*B = (t-u) • B + 1) :
    let A := (t+u)⁻¹ • (t • (1 : M) - B)
    A * A = A := by
  dsimp only
  have hprod : (t • (1 : M) - B) * (t • (1 : M) - B) =
      (t + u) • (t • (1 : M) - B) := by
    rw [sub_mul, mul_sub, mul_sub, smul_mul_smul_comm, one_mul, smul_mul_assoc, one_mul,
      mul_smul_comm, mul_one, hB, smul_sub, smul_smul]
    have ht : t*t + 1 = (t+u)*t := by rw [add_mul, mul_comm u t, htu]
    have hu : (t-u) - t - t = -(t+u) := by ring
    calc
      _ = (t*t+1) • (1 : M) + ((t-u) • B - t • B - t • B) := by
        rw [add_smul, one_smul]
        abel
      _ = _ := by rw [← sub_smul, ← sub_smul, hu, ht, neg_smul, sub_eq_add_neg]
  rw [smul_mul_smul_comm, hprod, smul_smul]
  congr 1
  field_simp

private theorem hermitian_scaled (B : M) (hB : B.IsHermitian) (t l : ℂ)
    (ht : star t = t) (hl : star l = l) :
    (l⁻¹ • (t • (1 : M) - B)).IsHermitian := by
  show Matrix.conjTranspose _ = _
  rw [Matrix.conjTranspose_smul, star_inv₀, hl, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul, ht, Matrix.conjTranspose_one, hB.eq]


private def rootPlus : ℂ := (((Real.sqrt 59 + Real.sqrt 55) / 2 : ℝ) : ℂ)
private def rootMinus : ℂ := (((Real.sqrt 59 - Real.sqrt 55) / 2 : ℝ) : ℂ)

private theorem roots_mul : rootPlus * rootMinus = 1 := by
  have h₁ : Real.sqrt 59 ^ 2 = 59 := Real.sq_sqrt (by norm_num)
  have h₂ : Real.sqrt 55 ^ 2 = 55 := Real.sq_sqrt (by norm_num)
  rw [rootPlus, rootMinus, ← Complex.ofReal_mul, ← Complex.ofReal_one]
  exact congrArg Complex.ofReal (by nlinarith)

private theorem roots_add : rootPlus + rootMinus = (Real.sqrt 59 : ℂ) := by
  rw [rootPlus, rootMinus, ← Complex.ofReal_add]
  congr 1
  ring

private theorem roots_sub : rootPlus - rootMinus = (Real.sqrt 55 : ℂ) := by
  rw [rootPlus, rootMinus, ← Complex.ofReal_sub]
  congr 1
  ring

private theorem roots_trace : (58 : ℂ) * rootPlus - rootPlus^3 = rootPlus+rootMinus := by
  have hs : (rootPlus+rootMinus)^2 = 59 := by
    rw [roots_add, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  linear_combination -rootPlus * hs + (2*rootPlus+rootMinus) * roots_mul


-- At the origin the convolution is the sum of reciprocal-phase products.
-- After replacing the origin term by 1, its mean equals 1 and every term
-- has modulus 1. Equality in the real-part estimate forces every product.
set_option maxRecDepth 2000 in
private theorem reflection_of_convolution (e : AddChar R ℂ) (g : R → R → ℂ)
    (t u : ℂ) (htu : t*u = 1) (hLsq : (t+u)^2 = 59)
    (htrace : (58 : ℂ)*t - t^3 = t+u) (ht3 : g 0 0 = t^3)
    (hcnv : conv e g 0 0 = (t-u) * g 0 0 + mass 0 0)
    (hunit : ∀ a b, (a,b) ≠ (0,0) → ‖g a b‖ = 1)
    (a b : R) (hab : (a,b) ≠ (0,0)) : g a b * g (-a) (-b) = e (a*b) := by
  classical
  let k (p : R × R) := g p.1 p.2 * g (-p.1) (-p.2) * e (-(p.2*p.1))
  let v (p : R × R) := if p = 0 then 1 else k p
  have ht6 : t^6 = (58 : ℂ) * (t-u)*t^3 + 1 := by
    have hu3 : u^3 = 57*u-t := by
      linear_combination u*hLsq - (t+2*u)*htu
    calc
      t^6 = (58 : ℂ) * (t-u)*t^3 + t^3*u^3 := by
        rw [hu3]
        linear_combination -t^3 * htrace
      _ = _ := by rw [← mul_pow, htu, one_pow]
  have hsum : (∑ p, k p) = t^6 + 3363 := by
    have h := hcnv
    rw [conv, mass, if_pos rfl, ht3] at h
    simp only [zero_sub, mul_neg] at h
    rw [Fintype.sum_prod_type]
    change (∑ x : R, ∑ y : R, g x y * g (-x) (-y) * e (-(y*x))) = _
    linear_combination 58*h - ht6
  have hvsum : (∑ p, v p) = (3364 : ℂ) := by
    have hv (p : R × R) : v p = k p + if p = 0 then 1-t^6 else 0 := by
      by_cases h : p = 0
      · subst p
        simp [v, k, ht3, ← pow_add]
      · simp [v, h]
    simp_rw [hv, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, hsum]
    ring
  have hvnorm (p : R × R) : ‖v p‖ = 1 := by
    by_cases hp : p = 0
    · simp [v,hp]
    · have hneg : (-p.1,-p.2) ≠ (0,0) := by
        simpa [Prod.ext_iff] using hp
      have hp' : (p.1,p.2) ≠ (0,0) := hp
      simp only [v, if_neg hp, k, norm_mul, hunit _ _ hp', hunit _ _ hneg, char_modulus,
        one_mul]
  have hsumreal : (∑ p, (1 - (v p).re)) = 0 := by
    have hh := congrArg Complex.reCLM hvsum
    rw [map_sum] at hh
    change (∑ p, (v p).re) = (3364 : ℂ).re at hh
    rw [Finset.sum_sub_distrib, hh]
    norm_num [Fintype.card_prod, ZMod.card]
  have hre (p : R × R) : (v p).re = 1 := by
    have hnonneg (i : R × R) : 0 ≤ 1 - (v i).re :=
      sub_nonneg.mpr ((Complex.re_le_norm _).trans_eq (hvnorm i))
    have h := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
      (f := fun i : R × R => 1 - (v i).re) (fun i _ => hnonneg i)).mp
        hsumreal p (Finset.mem_univ p)
    exact (sub_eq_zero.mp h).symm
  have hvone (p : R × R) : v p = 1 := by
    have h := congrArg (fun x : ℝ => x^2) (hvnorm p)
    change ‖v p‖ ^ 2 = (1 : ℝ)^2 at h
    rw [Complex.sq_norm, Complex.normSq_apply, hre] at h
    have hi : (v p).im = 0 := by
      have hs : (v p).im * (v p).im = 0 := by linarith
      exact (mul_eq_zero.mp hs).elim id id
    exact Complex.ext (by simpa using hre p) (by simpa using hi)
  have h : k (a,b) = 1 := by simpa only [v, if_neg (show (a,b) ≠ 0 from hab)] using hvone (a,b)
  change g a b * g (-a) (-b) * e (-(b*a)) = 1 at h
  rw [mul_comm b a] at h
  have he : e (-(a*b)) * e (a*b) = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  calc
    g a b * g (-a) (-b) = (g a b * g (-a) (-b)) * (e (-(a*b)) * e (a*b)) := by
      rw [he, mul_one]
    _ = e (a*b) := by rw [← mul_assoc, h, one_mul]

private theorem from_convolution (f : R → R → ℂ) (τ : ℂ →+* ℂ)
    (hzero : f 0 0 = rootPlus^3)
    (hconv : ∀ a b, conv ZMod.stdAddChar f a b =
      (rootPlus-rootMinus) * f a b + mass a b)
    (hunit : ∀ a b, (a,b) ≠ (0,0) → ‖τ (f a b)‖ = 1) :
    HasSICPOVM 58 := by
  classical
  let e : AddChar R ℂ := τ.toMonoidHom.compAddChar ZMod.stdAddChar
  let g : R → R → ℂ := fun a b => τ (f a b)
  let t : ℂ := τ rootPlus
  let u : ℂ := τ rootMinus
  let L : ℂ := t+u
  have he (a : R) : e a = τ (ZMod.stdAddChar a) := rfl
  have hinj : Function.Injective e := τ.injective.comp ZMod.injective_stdAddChar
  have htu : t*u = 1 := by
    simpa [t, u] using congrArg τ roots_mul
  have ht3 : g 0 0 = t^3 := by simp [g, hzero, t]
  have htrace : (58 : ℂ) * t - t^3 = L := by
    simpa only [L, t, u, map_mul, map_pow, map_sub, map_add, map_ofNat] using congrArg τ roots_trace
  have hLsq : L^2 = 59 := by
    have h : (rootPlus+rootMinus)^2 = (59 : ℂ) := by
      rw [roots_add, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    simpa only [L, t, u, map_pow, map_add, map_ofNat] using congrArg τ h
  have hLne : L ≠ 0 := by
    intro h
    rw [h] at hLsq
    norm_num at hLsq
  have hLstar : star L = L := star_fixed_of_sq_pos L 59 (by norm_num) (by simpa using hLsq)
  let D := t-u
  have hDsq : D^2 = 55 := by
    have h : (rootPlus-rootMinus)^2 = (55 : ℂ) := by
      rw [roots_sub, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    simpa only [D, t, u, map_pow, map_sub, map_ofNat] using congrArg τ h
  have hDstar : star D = D := star_fixed_of_sq_pos D 55 (by norm_num) (by simpa using hDsq)
  have htstar : star t = t := by
    have hsum : t = (L+D) / 2 := by dsimp [L, D]; ring
    rw [hsum, star_div₀, star_add, hLstar, hDstar, star_ofNat]
  have hcnv (a b : R) : conv e g a b = (t-u) * g a b + mass a b := by
    have hm : τ (mass a b) = mass a b := by
      unfold mass
      split <;> simp only [map_ofNat, map_zero]
    have h := congrArg τ (hconv a b)
    simpa only [conv, g, he, t, u, map_mul, map_inv₀, map_ofNat, map_sum, map_sub, map_add, hm]
      using h
  let B := weyl e g
  have hB : B*B = (t-u) • B + 1 := by
    change weyl e g * weyl e g = _
    rw [weyl_mul, show conv e g = fun a b => (t-u) * g a b + mass a b by
      funext a b; exact hcnv a b, weyl_linear, weyl_mass]
  have hg (a b : R) : star (g (-a) (-b)) = g a b * e (-(a*b)) := by
    by_cases h : (a,b) = (0,0)
    · have ha : a=0 := congrArg Prod.fst h
      have hb : b=0 := congrArg Prod.snd h
      simp [ha, hb, ht3, star_pow, htstar]
    · have hn : (-a,-b) ≠ (0,0) := by
        simpa [Prod.mk.injEq] using h
      have hprod : g a b * g (-a) (-b) = e (a*b) :=
        reflection_of_convolution e g t u htu hLsq htrace ht3 (hcnv 0 0) hunit a b h
      have hunit' : g (-a) (-b) * star (g (-a) (-b)) = 1 := by
        rw [Complex.star_def, Complex.mul_conj, ← Complex.sq_norm, hunit (-a) (-b) hn]
        norm_num
      calc
        star (g (-a) (-b)) =
            (g a b * g (-a) (-b) * e (-(a*b))) * star (g (-a) (-b)) := by
          rw [hprod, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, one_mul]
        _ = g a b * e (-(a*b)) := by
          rw [show g a b * g (-a) (-b) * e (-(a*b)) * star (g (-a) (-b)) =
            g a b * e (-(a*b)) * (g (-a) (-b) * star (g (-a) (-b))) by ring, hunit', mul_one]
  have hBH : B.IsHermitian := weyl_hermitian e g (char_conjugate e) hg
  let A := L⁻¹ • (t • (1 : M) - B)
  have hA : A*A = A := projection_idempotent B t u htu hLne hB
  have hAH : A.IsHermitian := hermitian_scaled B hBH t L htstar hLstar
  have hAtr : A.trace = 1 := by
    dsimp only [A]
    rw [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
      trace_weyl e hinj, ht3]
    simp only [ZMod.card, Nat.cast_ofNat, smul_eq_mul]
    rw [mul_comm t, htrace, inv_mul_cancel₀ hLne]
  apply orbit_of_matrix e (char_square e) (char_conjugate e) A hAH hA hAtr
  intro a b hab
  have hneg : (a,-b) ≠ (0,0) := by simpa [Prod.mk.injEq] using hab
  have hmass := weyl_coeff e hinj mass a b
  rw [weyl_mass, mass, if_neg hneg] at hmass
  have hsum : (∑ x : R, A (x+a) x * e (b*x)) = L⁻¹ * (-g a (-b)) := by
    simp only [A, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, mul_assoc,
      sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hmass, weyl_coeff e hinj, mul_zero, zero_sub]
  have hnorm : Complex.normSq L = 59 := by
    apply Complex.ofReal_injective
    rw [← Complex.mul_conj, ← Complex.star_def, hLstar, ← pow_two, hLsq]
    norm_num
  rw [hsum, Complex.normSq_mul, Complex.normSq_inv, Complex.normSq_neg, hnorm,
    ← Complex.sq_norm, hunit a (-b) hneg]
  norm_num [sicOverlapSq]


private def exp2pi (z : ℂ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z)

private def pochhammer (x q : ℂ) : ℂ := tprod (fun n : ℕ => 1 - x * q^n)

private abbrev A := ZMod 55
private abbrev G := (R × R) × A
private abbrev e : AddChar R ℂ := ZMod.stdAddChar
private abbrev c : AddChar A ℂ := ZMod.stdAddChar
-- The generator (epsilon-1)/55 has Gaussian exponent 29 modulo 55.
-- Polarization gives the coefficient 58 = 3 modulo 55 in the pairing.
private def gaussian (x : G) : ℂ :=
  e (x.1.1^2-x.1.1*x.1.2+x.1.2^2) * c (29*x.2^2)
private def pairing (x u : G) : ℂ :=
  e (x.1.1*(2*u.1.1-u.1.2)+x.1.2*(2*u.1.2-u.1.1)) * c (3*x.2*u.2)
private def rotate (x : G) : G := ((x.1.2-x.1.1, -x.1.1), x.2)
-- This solves (rotate - 1) u = ((r,s),0), with 39 the inverse of 3 modulo 58.
private def frequency (r s : R) (j : A) : G :=
  ((-39*(r+s),39*(r-2*s)),j)

private theorem rotate_freq (r s : R) (j : A) :
    rotate (frequency r s j) = frequency r s j + ((r,s),0) := by
  have h : (3*39 : R) = 1 := by decide
  apply Prod.ext
  · apply Prod.ext <;> dsimp [rotate,frequency]
    · linear_combination r * h
    · linear_combination s * h
  · simp [rotate, frequency]

private theorem pair_freq (a b r s : R) (k j : A) :
    pairing ((a,b),k) (frequency r s j) =
      e (-a*r+b*(r-s)) * c (3*k*j) := by
  unfold pairing frequency
  congr 2
  dsimp
  have h : (3*39 : R) = 1 := by decide
  linear_combination (-a*r+b*(r-s)) * h

private theorem orth55 (k : A) : ∑ j : A, c (3*k*j) = if k=0 then 55 else 0 := by
  split_ifs with hk
  · simp [hk, ZMod.card]
  · have hn : 3*k ≠ 0 := by
      intro hz
      apply hk
      have h : (37 * 3 : A) = 1 := by decide
      linear_combination 37 * hz - k * h
    exact AddChar.sum_eq_zero_of_ne_one ((ZMod.isPrimitive_stdAddChar 55) hn)

private def summand (F : G → ℂ) (v x : G) : ℂ :=
  F x * gaussian x * F (v-x)

private theorem average (F : G → ℂ) (r s : R) :
    (∑ j : A, ∑ x : G, summand F ((r,s),0) x * pairing x (frequency r s j)) =
    55 * ∑ a : R, ∑ b : R, summand F ((r,s),0) ((a,b),0) * e (-a*r+b*(r-s)) := by
  classical
  rw [Finset.sum_comm]
  simp only [Fintype.sum_prod_type, pair_freq, ← mul_assoc, ← Finset.mul_sum, orth55]
  simp [mul_comm (55 : ℂ), Finset.sum_mul]

-- Dropping the linear sign character from the published Weyl phase leaves
-- its multiplication law unchanged.
private def qphase (x : R) : ℂ := ZMod.stdAddChar (N := 116) ((x.val : ZMod 116)^2)

private theorem double_char (x : R) :
    ZMod.stdAddChar (N := 116) (2 * (x.val : ZMod 116)) = e x := by
  have h := ZMod.stdAddChar_coe (N := 116) (2 * (x.val : ℤ))
  push_cast at h
  rw [h]
  conv_rhs => rw [← ZMod.natCast_zmod_val x]
  change _ = ZMod.stdAddChar (N := 58) ((x.val : ℤ) : R)
  rw [ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

private theorem qphase_pair (x y : R) : qphase x * qphase y =
    qphase (x+y) * e (-(x*y)) := by
  unfold qphase
  rw [← double_char, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  apply congrArg
  have hs : (58 : ℤ) ∣ ((x+y).val : ℤ) - ((x.val : ℤ) + y.val) := by
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 58).mp
    simp
  have hp : (58 : ℤ) ∣ ((-(x*y)).val : ℤ) - (-(x.val : ℤ) * y.val) := by
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 58).mp
    simp
  obtain ⟨k,hk⟩ := hs
  obtain ⟨l,hl⟩ := hp
  have hs' : ((x+y).val : ℤ) = x.val+y.val+58*k := by linarith
  have hp' : ((-(x*y)).val : ℤ) = -(x.val : ℤ)*y.val+58*l := by linarith
  have heq : (((x.val : ℤ)^2+y.val^2 : ℤ) : ZMod 116) =
      ((((x+y).val : ℤ)^2+2*((-(x*y)).val : ℤ) : ℤ) : ZMod 116) := by
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 116).mpr
    use k*((x.val : ℤ)+y.val)+29*k^2+l
    rw [hs',hp']
    ring
  simpa only [Int.cast_add, Int.cast_pow, Int.cast_natCast, Int.cast_mul, Int.cast_ofNat]
    using heq

private theorem phase_ratio (a b r s : R) :
    (qphase a*qphase b) * (qphase (r-a)*qphase (s-b)) * e (b*(r-a)) =
      (qphase r*qphase s) * (e (a^2-a*b+b^2) * e (-a*r+b*(r-s))) := by
  calc
    _ = (qphase a*qphase (r-a)) * (qphase b*qphase (s-b)) * e (b*(r-a)) := by ring
    _ = _ := by
      rw [qphase_pair, qphase_pair]
      simp only [add_sub_cancel]
      have hz : e (-(a*(r-a))) * e (-(b*(s-b))) * e (b*(r-a)) =
          e (a^2-a*b+b^2) * e (-a*r+b*(r-s)) := by
        simp only [← AddChar.map_add_eq_mul]
        congr 1
        ring
      linear_combination (qphase r * qphase s) * hz
private def pentagon (F : G → ℂ) : Prop := ∀ v u : G,
  (∑ x : G, summand F v x * pairing x u) =
    58 * (rootPlus-rootMinus) * (gaussian (u+v) * F (-(u+v)) * F u * F v -
      if u = 0 ∧ v = 0 then 185020 * F 0 else 0)

private def reflects (F : G → ℂ) : Prop :=
  ∀ x : G, x ≠ 0 → gaussian x * F (-x) * F x = 1

private def twistedSum (F : G → ℂ) (r s : R) : ℂ :=
  ∑ a : R, ∑ b : R, summand F ((r,s),0) ((a,b),0) * e (-a*r+b*(r-s))

private theorem rotate_zero (x : G) (h : rotate x = 0) : x = 0 := by
  rcases x with ⟨⟨a,b⟩,k⟩
  simp only [rotate, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, neg_eq_zero] at h ⊢
  exact ⟨⟨h.1.2, by simpa [h.1.2] using h.1.1⟩, h.2⟩

private theorem restricted_off_origin (F : G → ℂ) (hp : pentagon F)
    (hr : reflects F) (ht : ∀ x, F (rotate x) = F x)
    (r s : R) (hv : (r,s) ≠ 0) :
    twistedSum F r s = 58 * (rootPlus-rootMinus) * F ((r,s),0) := by
  classical
  let v : G := ((r,s),0)
  have hne : v ≠ 0 := fun h => hv (congrArg Prod.fst h)
  have hrow (j : A) :
      (∑ x : G, summand F v x * pairing x (frequency r s j)) =
      58 * (rootPlus-rootMinus) * F v := by
    let u := frequency r s j
    have hrot : rotate u = u+v := rotate_freq r s j
    have hn : u+v ≠ 0 := by
      intro h
      have hu := rotate_zero u (hrot.trans h)
      exact hne (by simpa [hu] using h)
    have hflip : F u = F (u+v) := hrot ▸ (ht u).symm
    change (∑ x : G, summand F v x * pairing x u) = _
    rw [hp, if_neg (fun h => hne h.2), sub_zero, hflip, hr _ hn, one_mul]
  have h := average F r s
  change (∑ j : A, ∑ x : G, summand F v x * pairing x (frequency r s j)) =
    55 * twistedSum F r s at h
  simp only [hrow, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
    Nat.cast_ofNat] at h
  linear_combination -h / 55

private theorem restricted_origin (F : G → ℂ) (hr : reflects F) (h0 : F 0 = rootPlus^3) :
    twistedSum F 0 0 = 58 * ((rootPlus-rootMinus) * F 0 + 58) := by
  classical
  have hterm (p : R × R) : summand F 0 (p,0) =
      1 + if p=0 then (rootPlus^3)^2 - 1 else 0 := by
    by_cases h : p = 0
    · subst p
      simp [summand, gaussian, show ((0,0) : G) = 0 from rfl, h0, pow_two]
    · have hn : (p,(0 : A)) ≠ (0 : G) := fun hz => h (congrArg Prod.fst hz)
      have hh := hr _ hn
      simp only [summand, zero_sub, if_neg h, add_zero]
      linear_combination hh
  have hsum : twistedSum F 0 0 = 3363 + (rootPlus^3)^2 := by
    unfold twistedSum
    simp only [mul_zero, sub_zero, zero_add, AddChar.map_zero_eq_one, mul_one,
      show (((0,0),0) : G) = 0 from rfl]
    rw [← Fintype.sum_prod_type (fun p : R × R => summand F 0 (p,0))]
    simp [hterm, Finset.sum_add_distrib, Fintype.card_prod, ZMod.card]
    ring
  rw [hsum,h0]
  have h := roots_trace
  have hq : (rootPlus+rootMinus)^2 = 59 := by
    rw [roots_add, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have ht3 : rootPlus^3 = 57*rootPlus-rootMinus := by linear_combination -h
  rw [ht3]
  linear_combination -57 * hq + 3364 * roots_mul

private theorem restricted_conv (F : G → ℂ) (hp : pentagon F) (hr : reflects F)
    (ht : ∀ x, F (rotate x) = F x) (h0 : F 0 = rootPlus^3) (r s : R) :
    conv e (fun a b => (qphase a*qphase b) * F ((a,b),0)) r s =
      (rootPlus-rootMinus) * ((qphase r*qphase s) * F ((r,s),0)) + mass r s := by
  classical
  have hterm (a b : R) :
      ((qphase a*qphase b) * F ((a,b),0)) *
        ((qphase (r-a)*qphase (s-b)) * F ((r-a,s-b),0)) * e (b*(r-a)) =
      (qphase r*qphase s) * (summand F ((r,s),0) ((a,b),0) * e (-a*r+b*(r-s))) := by
    simp only [summand, gaussian, mul_zero, zero_pow (by decide : 2 ≠ 0),
      AddChar.map_zero_eq_one, mul_one, Prod.mk_sub_mk, sub_zero]
    linear_combination (F ((a,b),0) * F ((r-a,s-b),0)) * phase_ratio a b r s
  rw [conv]
  simp_rw [hterm]
  simp only [← Finset.mul_sum]
  change (58 : ℂ)⁻¹ * ((qphase r*qphase s) * twistedSum F r s) = _
  by_cases hv : (r,s) = 0
  · have hr0 : r = 0 := congrArg Prod.fst hv
    have hs0 : s = 0 := congrArg Prod.snd hv
    subst r s
    rw [restricted_origin F hr h0]
    simp [mass, qphase, show (((0,0),0) : G) = 0 from rfl]
  · rw [restricted_off_origin F hp hr ht _ _ hv]
    rw [mass, if_neg (show (r,s) ≠ (0,0) from hv)]
    ring
private theorem pair_orth (u : G) (hu : u ≠ 0) : ∑ x : G, pairing x u = 0 := by
  rcases u with ⟨⟨r,s⟩,k⟩
  simp only [Fintype.sum_prod_type, pairing, AddChar.map_add_eq_mul]
  simp_rw [show ∀ j : A, 3*j*k = 3*k*j from fun j => by ring, ← Finset.mul_sum, orth55]
  by_cases hk : k = 0
  · subst k
    simp only [ite_true, ← Finset.sum_mul, ← Finset.mul_sum]
    have hx (m : R) : ∑ a : R, e (a*m) = if m=0 then 58 else 0 := by
      simpa only [mul_comm] using char_orth e ZMod.injective_stdAddChar m
    simp only [hx]
    by_cases hs : 2*s-r=0
    · have hns : 2*r-s ≠ 0 := by
        intro h
        have hinv : (39*3 : R) = 1 := by decide
        have hr : r=0 := by linear_combination 39*(2*h+hs)-r*hinv
        have hs0 : s=0 := by linear_combination 39*(h+2*hs)-s*hinv
        exact hu (by simp [hr,hs0])
      simp [hs,hns]
    · simp [hs]
  · simp [hk]

private def excess : ℂ := 58 * (rootPlus-rootMinus) * rootPlus^3

private theorem excess_eq : excess = (rootPlus^3)^2 - 1 := by
  have ht : rootPlus^3 = 57*rootPlus-rootMinus := by linear_combination -roots_trace
  have hq : (rootPlus+rootMinus)^2 = 59 := by
    rw [roots_add, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [excess, ht]
  linear_combination 57 * hq - 3364 * roots_mul

private theorem excess_large : (185020 : ℝ) < ‖excess‖ := by
  rw [excess, roots_sub, rootPlus]
  norm_cast
  have h59 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 59)
  have h55 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 55)
  have hgt : Real.sqrt 55 < Real.sqrt 59 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hp : 0 < (Real.sqrt 59 - Real.sqrt 55)^3 := by positivity
  have hh : 0 < Real.sqrt 55 * (Real.sqrt 59 - Real.sqrt 55)^3 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    185020 < 185020 + (58/8 : ℝ) * (Real.sqrt 55 * (Real.sqrt 59 - Real.sqrt 55)^3) := by linarith
    _ = _ := by
      linear_combination -(58/4 : ℝ) * (3 * (Real.sqrt 55)^2 * h59 +
        (Real.sqrt 55)^2 * h55 + 232 * h55)

private theorem vanishing_defect {ι : Type*} [Fintype ι] [Zero ι] (g : ι → ℂ)
    (p : ι → ι → ℂ) (z : ℂ) (hsize : (Fintype.card ι : ℝ) < ‖z‖)
    (hzero : g 0 = 0) (hnorm : ∀ x u, ‖p x u‖ = 1)
    (heq : ∀ u ≠ 0, (∑ x, g x * p x u) = z * g u) : ∀ x, g x = 0 := by
  obtain ⟨u,hm⟩ := Finite.exists_max (fun x => ‖g x‖)
  have hz : ‖g u‖ = 0 := by
    by_cases h : u = 0
    · simp [h, hzero]
    · have hb : ‖z‖ * ‖g u‖ ≤ (Fintype.card ι : ℝ) * ‖g u‖ := calc
        _ = ‖∑ x, g x * p x u‖ := by rw [heq u h, norm_mul]
        _ ≤ ∑ x, ‖g x * p x u‖ := norm_sum_le _ _
        _ ≤ ∑ _x : ι, ‖g u‖ := Finset.sum_le_sum fun x _ => by
          simpa only [norm_mul, hnorm, mul_one] using hm x
        _ = _ := by simp
      exact le_antisymm (le_of_not_gt (fun hp =>
        (not_lt_of_ge hb) (mul_lt_mul_of_pos_right hsize hp))) (norm_nonneg _)
  intro x
  exact norm_eq_zero.mp (le_antisymm ((hm x).trans_eq hz) (norm_nonneg _))

/-- The zero-shift row of the pentagon makes the reflection defect an
eigenfunction of an unnormalized Fourier transform. The eigenvalue is
strictly larger than the group order, forcing the defect to vanish. -/
private theorem reflection_from_pentagon (F : G → ℂ) (hp : pentagon F)
    (h0 : F 0 = rootPlus^3) : reflects F := by
  classical
  let d (x : G) := gaussian x * F (-x) * F x
  let g (x : G) := d x - (1 + if x=0 then excess else 0)
  have hg0 : g 0 = 0 := by simp [g,d,gaussian,h0,excess_eq]; ring
  have heq (u : G) (hu : u ≠ 0) : (∑ x : G, g x * pairing x u) = excess * g u := by
    have ht (x : G) : g x * pairing x u = summand F 0 x * pairing x u -
        pairing x u - if x = 0 then excess else 0 := by
      by_cases h : x=0
      · subst x
        simp [g,d,summand,pairing]
        ring
      · simp [g,d,summand,h]
        ring
    simp only [ht, Finset.sum_sub_distrib, pair_orth u hu, sub_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [hp]
    simp [g,d,hu,excess,h0]
    ring
  have hn (x u : G) : ‖pairing x u‖ = 1 := by
    rw [pairing,norm_mul,char_modulus e,char_modulus c,one_mul]
  have hs : (Fintype.card G : ℝ) < ‖excess‖ := by
    simpa only [Fintype.card_prod, ZMod.card, Nat.cast_mul, Nat.cast_ofNat,
      show (58 : ℝ)*58*55 = 185020 by norm_num] using excess_large
  have hv := vanishing_defect g pairing excess hs hg0 hn heq
  intro x hx
  have hz := hv x
  simpa [g,d,hx, sub_eq_zero] using hz
/-- Coordinates represent (i epsilon + j)/58 + k (epsilon-1)/55 in the
group fixed by epsilon cubed. Multiplication by epsilon to the power -3
minus one gives first lattice coordinate -i-56j+58k. -/
private def boundary (x : G) : ℂ :=
  if x = 0 then rootPlus^3 else
  let i : ℂ := x.1.1.val
  let j : ℂ := x.1.2.val
  let k : ℂ := x.2.val
  let eps := rootPlus^2
  let z := (i*eps+j)/58+k*(eps-1)/55
  let m := -i-56*j+58*k
  let value (n : ℕ) :=
    let w := eps + Complex.I / ((n : ℂ) + 1)
    let l := 3248*w-57
    let w' := (185079*w-3248)/l
    (-Complex.I) * (pochhammer (exp2pi (z+m*w)) (exp2pi w) /
      pochhammer (exp2pi (z/l)) (exp2pi w'))
  Filter.lim (Filter.map value Filter.atTop)

/-- The full finite pentagon identity for the boundary values. -/
def H1 : Prop := pentagon boundary

/-- Invariance of the boundary values under multiplication by epsilon. -/
def H2 : Prop := ∀ x, boundary (rotate x) = boundary x

/-- A common embedding makes all nontrivial 58-torsion values unimodular. -/
def H3 : Prop := ∃ τ : ℂ →+* ℂ, ∀ a b : R, (a,b) ≠ 0 → ‖τ (boundary ((a,b),0))‖ = 1

theorem main : H1 → H2 → H3 → type_of% @OpenQuantumProblem23.hasSICPOVM_58 := by
  intro hp ht
  rintro ⟨τ, hunit⟩
  have h0 : boundary 0 = rootPlus^3 := by simp [boundary]
  have hr := reflection_from_pentagon boundary hp h0
  apply from_convolution (fun a b => (qphase a*qphase b) * boundary ((a,b),0)) τ
  · simp [qphase, show (((0,0),0) : G) = 0 from rfl, h0]
  · exact restricted_conv boundary hp hr ht h0
  · intro a b hn
    let z : AddChar (ZMod 116) ℂ := τ.toMonoidHom.compAddChar ZMod.stdAddChar
    have hu (x : R) : ‖τ (qphase x)‖ = 1 := char_modulus z _
    rw [map_mul, map_mul, norm_mul, norm_mul, hu, hu, hunit a b hn, one_mul, one_mul]

end

end OMA.R_OpenQuantumProblem23_hasSICPOVM_58_R2
