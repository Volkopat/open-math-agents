import FormalConjectures.Wikipedia.ErdosUlamProblem
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Inversion.ImageHyperplane
import Mathlib.Tactic.Abel

namespace OMA.R_ErdosUlamProblem_erdos_ulam_problem_variants_solymosi_de_zeeuw_R1
open Set Complex Module EuclideanGeometry
open scoped ComplexConjugate RealInnerProductSpace

/-- This is the genus-two arithmetic input. Each quadratic is strictly
positive on the real line, and distinct monic quadratics have no common
root in this family. -/
def H1 : Prop :=
  ∀ a b c : ℚ × ℚ, 0 < a.2 → 0 < b.2 → 0 < c.2 → a ≠ b → a ≠ c → b ≠ c →
    {t : ℚ | ∃ y : ℚ, y^2 = ((t-a.1)^2+a.2)*((t-b.1)^2+b.2)*((t-c.1)^2+c.2)}.Finite

/-- Inversion transfers the affine-line theorem to circles through a point of the set. -/
def H2 : Prop :=
  (∀ (S : Set (EuclideanSpace ℝ (Fin 2))),
      (∀ x ∈ S, ∀ y ∈ S, ∃ q : ℚ, dist x y = (q:ℝ)) →
      ∀ L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)), finrank ℝ L.direction ≤ 1 →
        (S ∩ (L : Set _)).Infinite → (S \ (L : Set _)).Finite) →
  ∀ (S : Set (EuclideanSpace ℝ (Fin 2)))
    (_hd : ∀ x ∈ S, ∀ y ∈ S, ∃ q : ℚ, dist x y = (q:ℝ))
    (c : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ) (_hr : 0 < ρ)
    (_many : {x ∈ S | dist x c = ρ}.Infinite), {x ∈ S | dist x c ≠ ρ}.Finite

theorem sqdist (z w : ℂ) : dist z w ^ 2 = (z.re-w.re)^2+(z.im-w.im)^2 := by
  rw [dist_eq_norm,Complex.sq_norm,Complex.normSq_apply]
  simp [pow_two]

theorem coefficients {S : Set ℂ} (hd : ∀ z ∈ S, ∀ w ∈ S, ∃ q : ℚ, dist z w = (q:ℝ))
    (zero : 0 ∈ S) (one : 1 ∈ S) {z : ℂ} (hz : z ∈ S) :
    ∃ a : ℚ × ℚ, (a.1:ℝ) = z.re ∧ (a.2:ℝ) = z.im^2 := by
  obtain ⟨d,hd₀⟩ := hd z hz 0 zero
  obtain ⟨e,hd₁⟩ := hd z hz 1 one
  have eq₀ := sqdist z 0
  have eq₁ := sqdist z 1
  rw [hd₀] at eq₀
  rw [hd₁] at eq₁
  simp only [zero_re,zero_im,one_re,one_im,sub_zero] at eq₀ eq₁
  let p : ℚ := (1+d^2-e^2)/2
  have hp : (p:ℝ) = z.re := by dsimp [p]; push_cast; nlinarith
  refine ⟨(p,d^2-p^2),hp,?_⟩
  push_cast
  nlinarith [hp]

theorem mirror {a z : ℂ} (h : a.re = z.re) (j : a.im^2 = z.im^2) : z ∈ ({a,conj a} : Set ℂ) := by
  have cases : z.im = a.im ∨ z.im = -a.im := by
    exact (mul_eq_zero.mp (show (z.im-a.im)*(z.im+a.im)=0 by nlinarith)).imp (by intro e; linarith) (by intro e; linarith)
  rcases cases with left | right
  · exact Or.inl (Complex.ext h.symm left)
  · exact Or.inr (Complex.ext h.symm (by simpa using right))

/-- On the normalized real axis the finite-exception assertion follows from
finiteness of rational points on sextics with three positive quadratic
factors. Repeated factors can only arise from reflection across the axis. -/
theorem normalized_line (arith : H1) (S : Set ℂ)
    (hd : ∀ z ∈ S, ∀ w ∈ S, ∃ q : ℚ, dist z w = (q:ℝ))
    (zero : 0 ∈ S) (one : 1 ∈ S) (hin : {z ∈ S | z.im = 0}.Infinite) :
    {z ∈ S | z.im ≠ 0}.Finite := by
  classical
  let T := {t : ℚ | ((t:ℝ):ℂ) ∈ S}
  have many : T.Infinite := by
    intro hf
    apply hin
    apply (hf.image (fun t : ℚ => ((t:ℝ):ℂ))).subset
    rintro z ⟨hz,horizontal⟩
    obtain ⟨p,hp,_⟩ := coefficients hd zero one hz
    have eqn : ((p.1:ℝ):ℂ) = z := Complex.ext hp (by simpa using horizontal.symm)
    exact ⟨p.1,show ((p.1:ℝ):ℂ) ∈ S from eqn ▸ hz,eqn⟩
  by_contra infiniteOff
  change Set.Infinite _ at infiniteOff
  obtain ⟨a,ha,ia⟩ := infiniteOff.nonempty
  obtain ⟨b,⟨hb,ib⟩,nb⟩ := (infiniteOff.sdiff ((finite_singleton (conj a)).insert a)).nonempty
  obtain ⟨c,⟨hc,ic⟩,nc⟩ := (infiniteOff.sdiff (((finite_singleton (conj a)).insert a).union ((finite_singleton (conj b)).insert b))).nonempty
  obtain ⟨A,ra,sa⟩ := coefficients hd zero one ha
  obtain ⟨B,rb,sb⟩ := coefficients hd zero one hb
  obtain ⟨C,rc,sc⟩ := coefficients hd zero one hc
  have positive {z : ℂ} {p : ℚ × ℚ} (nz : z.im ≠ 0) (eqn : (p.2:ℝ) = z.im^2) : 0 < p.2 := by
    exact_mod_cast (eqn.symm ▸ (sq_pos_of_ne_zero nz) : 0 < (p.2:ℝ))
  have separate {z w : ℂ} {p q : ℚ × ℚ} (hz : (p.1:ℝ) = z.re) (hw : (q.1:ℝ) = w.re)
      (iz : (p.2:ℝ) = z.im^2) (iw : (q.2:ℝ) = w.im^2)
      (ne : w ∉ ({z,conj z} : Set ℂ)) : p ≠ q := by
    rintro rfl
    exact ne (mirror (hz.symm.trans hw) (iz.symm.trans iw))
  have bound := arith A B C (positive ia sa) (positive ib sb) (positive ic sc)
    (separate ra rb sa sb nb) (separate ra rc sa sc (fun h => nc (Or.inl h)))
    (separate rb rc sb sc (fun h => nc (Or.inr h)))
  apply many (bound.subset ?_)
  intro t ht
  have factor (z : ℂ) (hz : z ∈ S) (p : ℚ × ℚ) (hr : (p.1:ℝ) = z.re) (hs : (p.2:ℝ) = z.im^2) :
      ∃ d : ℚ, d^2 = (t-p.1)^2+p.2 := by
    obtain ⟨d,eqn⟩ := hd _ ht z hz
    refine ⟨d,?_⟩
    have h := sqdist ((t:ℝ):ℂ) z
    rw [eqn] at h
    simp only [ofReal_re,ofReal_im,zero_sub,neg_sq] at h
    exact_mod_cast (by rw [hr,hs]; exact h : (d:ℝ)^2 = ((t:ℝ)-(p.1:ℝ))^2+(p.2:ℝ))
  obtain ⟨x,hx⟩ := factor a ha A ra sa
  obtain ⟨y,hy⟩ := factor b hb B rb sb
  obtain ⟨z,hz⟩ := factor c hc C rc sc
  exact ⟨x*y*z, by simp only [mul_pow,hx,hy,hz]⟩

/-- Normalize two members of the rational-distance set on the same line to
zero and one. Division in the complex plane scales all distances by the
same rational factor. -/
theorem normalize_line
    (normalized : ∀ S : Set ℂ, (∀ z ∈ S, ∀ w ∈ S, ∃ q : ℚ, dist z w = (q:ℝ)) →
      0 ∈ S → 1 ∈ S → {z ∈ S | z.im = 0}.Infinite → {z ∈ S | z.im ≠ 0}.Finite)
    (S : Set (EuclideanSpace ℝ (Fin 2)))
    (hd : ∀ x ∈ S, ∀ y ∈ S, ∃ q : ℚ, dist x y = (q:ℝ))
    (L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) (dim : finrank ℝ L.direction ≤ 1)
    (hin : (S ∩ (L : Set _)).Infinite) : (S \ (L : Set _)).Finite := by
  classical
  obtain ⟨a,ha⟩ := hin.nonempty
  obtain ⟨b,hb,hba⟩ := (hin.sdiff (finite_singleton a)).nonempty
  have ba : b ≠ a := hba
  have nonzero : b-a ≠ 0 := sub_ne_zero.mpr ba
  have span : (ℝ ∙ (b-a)) = L.direction := Submodule.eq_of_le_of_finrank_le
    ((Submodule.span_singleton_le_iff_mem _ _).mpr (L.vsub_mem_direction hb.2 ha.2))
    (by rwa [finrank_span_singleton nonzero])
  let e := Complex.orthonormalBasisOneI.repr.symm
  let d := e (b-a)
  have dn : d ≠ 0 := by
    intro h
    exact nonzero (e.injective (h.trans e.map_zero.symm))
  let F := fun x => e (x-a)/d
  have inj : Function.Injective F := by
    intro x y h
    exact sub_left_inj.mp (e.injective ((div_left_inj' dn).mp h))
  have scale (x y) : dist (F x) (F y) = dist x y / dist b a := by
    rw [dist_eq_norm (F x) (F y)]
    change ‖e (x-a)/d - e (y-a)/d‖ = _
    rw [← sub_div,norm_div,← e.map_sub,e.norm_map, show (x-a)-(y-a) = x-y by abel]
    change ‖x-y‖/‖e (b-a)‖ = _
    rw [e.norm_map,dist_eq_norm,dist_eq_norm]
  have axis (x) : (F x).im = 0 ↔ x ∈ L := by
    constructor
    · intro hh
      have hr : (((F x).re:ℂ)) = F x := Complex.ext rfl (by simpa using hh.symm)
      have eqn : x-a = (F x).re • (b-a) := by
        apply e.injective
        rw [e.map_smul]
        change e (x-a) = ((F x).re:ℂ)*d
        rw [hr]; exact (div_mul_cancel₀ _ dn).symm
      have mem : x-a ∈ L.direction := by
        rw [← span,eqn]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      exact (by simpa using L.vadd_mem_of_mem_direction mem ha.2)
    · intro hx
      have hm : x-a ∈ ℝ ∙ (b-a) := span ▸ L.vsub_mem_direction hx ha.2
      obtain ⟨t,ht⟩ := Submodule.mem_span_singleton.mp hm
      dsimp only [F]
      rw [← ht,e.map_smul]
      change ((t:ℂ)*d/d).im = 0
      rw [mul_div_cancel_right₀ _ dn,Complex.ofReal_im]
  let T := F '' S
  have rat : ∀ z ∈ T, ∀ w ∈ T, ∃ q : ℚ, dist z w = (q:ℝ) := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    obtain ⟨q,hq⟩ := hd x hx y hy
    obtain ⟨s,hs⟩ := hd b hb.1 a ha.1
    exact ⟨q/s,by rw [scale,hq,hs,Rat.cast_div]⟩
  have zero : 0 ∈ T := ⟨a,ha.1,by simp [F]⟩
  have one : 1 ∈ T := ⟨b,hb.1,by change d/d = 1; exact div_self dn⟩
  have many : {z ∈ T | z.im = 0}.Infinite := by
    apply (hin.image inj.injOn).mono
    rintro _ ⟨x,⟨hx,hL⟩,rfl⟩
    exact ⟨mem_image_of_mem _ hx,(axis x).mpr hL⟩
  apply (finite_image_iff inj.injOn).mp
  apply (normalized T rat zero one many).subset
  rintro _ ⟨x,⟨hx,hL⟩,rfl⟩
  exact ⟨mem_image_of_mem _ hx,fun h => hL ((axis x).mp h)⟩

/-- The parametrization of an affine line used in the problem statement. -/
theorem point_on_line {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a b x : E) :
    x ∈ AffineSubspace.mk' a (ℝ ∙ (b-a)) ↔ ∃ t : ℝ, x = a+t • (b-a) := by
  rw [AffineSubspace.mem_mk',Submodule.mem_span_singleton]
  change (∃ t : ℝ, t • (b-a) = x-a) ↔ _
  constructor
  · rintro ⟨t,ht⟩
    exact ⟨t,by rw [ht]; abel⟩
  · rintro ⟨t,rfl⟩
    exact ⟨t,by abel⟩

theorem main : H1 → H2 → type_of% @ErdosUlamProblem.erdos_ulam_problem.variants.solymosi_de_zeeuw := by
  intro arithmetic inversionStep S hd structureCase
  have lines := normalize_line (normalized_line arithmetic)
  rcases structureCase with ⟨a,b,ab,many⟩ | ⟨c,ρ,hr,many⟩
  · let L := AffineSubspace.mk' a (ℝ ∙ (b-a))
    have dim : finrank ℝ L.direction ≤ 1 := by
      change finrank ℝ (AffineSubspace.mk' a (ℝ ∙ (b-a))).direction ≤ 1
      rw [AffineSubspace.direction_mk',finrank_span_singleton (sub_ne_zero.mpr ab.symm)]
    have inf : (S ∩ (L : Set _)).Infinite := by
      apply many.mono
      rintro x ⟨hx,t⟩
      exact ⟨hx,(point_on_line a b x).mpr t⟩
    refine Or.inl ⟨a,b,ab,(lines S hd L dim inf).subset ?_⟩
    rintro x ⟨hx,no⟩
    exact ⟨hx,fun h => no ((point_on_line a b x).mp h)⟩
  · exact Or.inr ⟨c,ρ,hr,inversionStep lines S hd c ρ hr many⟩

end OMA.R_ErdosUlamProblem_erdos_ulam_problem_variants_solymosi_de_zeeuw_R1
