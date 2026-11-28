import FormalConjectures.OEIS.«179537»
import Mathlib

/-! # The split-prime alternating congruence for OEIS A179537 -/

section

/- # Short Weierstrass model of the CM elliptic curve of discriminant −7 -/

namespace SunCoster

def shortCurve (K : Type*) [Field K] : WeierstrassCurve.Affine K := ⟨0,0,0,-35,98⟩

theorem short_equation {K : Type*} [Field K] {x y : K} :
    (shortCurve K).Equation x y ↔ y^2=x^3-35*x+98 := by
  rw [WeierstrassCurve.Affine.equation_iff]; simp [shortCurve, sub_eq_add_neg]

end SunCoster

end

section

namespace SunCoster
open Polynomial WeierstrassCurve.Affine
noncomputable section
variable {F E L : Type*} [Field F] [Field E] [Field L]

/-- An embedding of the base field extends to the quadratic splitting field
whenever the image of the radicand has a square root in the target. -/
theorem lift_quadratic (g : F →+* E) (w : F) (z : E) (hz : z^2=g w) :
    ∃ φ : (X^2-C w).SplittingField →+* E, ∀ a,
      φ (algebraMap F (X^2-C w).SplittingField a)=g a := by
  let : Algebra F E := g.toAlgebra
  let f : F[X] := X^2-C w
  have h : f.map (algebraMap F E)=(X-C z)*(X-C (-z)) := by
    change (X^2-C w).map g=_
    simp only [Polynomial.map_sub,Polynomial.map_pow,map_X,map_C,←hz,Polynomial.C_pow,map_neg]
    ring
  have hs : (f.map (algebraMap F E)).Splits := by
    rw [h]
    exact (Splits.X_sub_C z).mul (Splits.X_sub_C (-z))
  let φ := Polynomial.SplittingField.lift f hs
  exact ⟨φ.toRingHom,φ.commutes⟩

private theorem map_equation (f : E →+* L) {x y : E} (h : (shortCurve E).Equation x y) :
    (shortCurve L).Equation (f x) (f y) := by
  apply short_equation.mpr
  simpa only [map_pow,map_mul,map_sub,map_add,map_ofNat] using congrArg f (short_equation.mp h)

private theorem map_smooth (f : E →+* L) {x y : E} (h : (shortCurve E).Nonsingular x y) :
    (shortCurve L).Nonsingular (f x) (f y) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff] at h ⊢
  refine ⟨map_equation f h.1,?_⟩
  rcases h.2 with h|h
  · left
    have H := f.injective.ne h
    simpa only [shortCurve,map_neg,map_sub,map_add,map_mul,map_pow,map_zero,map_ofNat] using H
  · right
    have H := f.injective.ne h
    simpa only [shortCurve,map_neg,map_sub,map_add,map_mul,map_pow,map_zero,map_ofNat] using H

private def mapPt (f : E →+* L) : (shortCurve E).Point → (shortCurve L).Point
  | .zero => 0
  | .some x y h => .some (f x) (f y) (map_smooth f h)

theorem short_negY_map (f : E →+* L) (x y : E) :
    f ((shortCurve E).negY x y)=(shortCurve L).negY (f x) (f y) := by simp [negY,shortCurve]

private theorem slope_map [DecidableEq E] [DecidableEq L] (f : E →+* L) (x u y v : E) :
    f ((shortCurve E).slope x u y v)=(shortCurve L).slope (f x) (f u) (f y) (f v) := by
  by_cases hx : x=u
  · by_cases hy : y=(shortCurve E).negY u v
    · have h' := congrArg f hy
      rw [short_negY_map] at h'
      rw [slope_of_Y_eq hx hy,slope_of_Y_eq (congrArg f hx) h',map_zero]
    · have h' := f.injective.ne hy
      rw [short_negY_map] at h'
      rw [slope_of_Y_ne hx hy,slope_of_Y_ne (congrArg f hx) h']
      simp [shortCurve,negY,map_ofNat]
  · rw [slope_of_X_ne hx,slope_of_X_ne (f.injective.ne hx),map_div₀,map_sub,map_sub]

private theorem addX_map (f : E →+* L) (x u m : E) :
    f ((shortCurve E).addX x u m)=(shortCurve L).addX (f x) (f u) (f m) := by
  simp [addX,shortCurve]

private theorem addY_map (f : E →+* L) (x u y m : E) :
    f ((shortCurve E).addY x u y m)=(shortCurve L).addY (f x) (f u) (f y) (f m) := by
  simp only [addY,short_negY_map,addX_map,negAddY,map_add,map_mul,map_sub]

/-- The group map of the fixed short curve induced by any field embedding. -/
def shortMap [DecidableEq E] [DecidableEq L] (f : E →+* L) :
    (shortCurve E).Point →+ (shortCurve L).Point where
  toFun := mapPt f
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x,y,p⟩) (_ | ⟨u,v,q⟩)
    any_goals rfl
    by_cases h : x=u ∧ y=(shortCurve E).negY u v
    · have ey := congrArg f h.2
      rw [short_negY_map] at ey
      rw [Point.add_of_Y_eq h.1 h.2]
      exact (Point.add_of_Y_eq (congrArg f h.1) ey).symm
    · have hh : ¬ (f x=f u ∧ f y=(shortCurve L).negY (f u) (f v)) := by
        rintro ⟨ha,hb⟩; exact h ⟨f.injective ha,f.injective (hb.trans (short_negY_map f u v).symm)⟩
      rw [Point.add_some h]
      change Point.some _ _ _=Point.some _ _ _ + Point.some _ _ _
      rw [Point.add_some hh,Point.some.injEq]
      exact ⟨by rw [addX_map,slope_map],by rw [addY_map,slope_map]⟩

@[simp] theorem shortMap_some [DecidableEq E] [DecidableEq L] (f : E →+* L) {x y : E}
    (h : (shortCurve E).Nonsingular x y) :
    shortMap f (Point.some x y h)=Point.some (f x) (f y) (map_smooth f h) := rfl

end
end SunCoster

end

section

open IntermediateField

namespace SunDescent

variable {K : Type*} [Field K]

noncomputable def deg (f : RatFunc K) := max f.num.natDegree f.denom.natDegree

noncomputable section

/-- Degree of a compositum of rational maps on the projective line. -/
theorem degree_substitution (φ : RatFunc K →ₐ[K] RatFunc K) (f : RatFunc K) :
    deg (φ f) = deg f * deg (φ RatFunc.X) := by
  let S := IntermediateField.adjoin K ({f} : Set (RatFunc K))
  let R : IntermediateField K (RatFunc K) := ⊤
  have sf : S.map φ = K⟮φ f⟯ := by simp [S,adjoin_map]
  have rf : R.map φ = K⟮φ RatFunc.X⟯ := by
    dsimp only [R]
    rw [← RatFunc.adjoin_X (K:=K),adjoin_map,Set.image_singleton]
  have le : S.map φ ≤ R.map φ := IntermediateField.map_mono φ (show S ≤ R from le_top)
  have h := relfinrank_mul_finrank_top le
  rw [relfinrank_map_map,sf,rf] at h
  dsimp only [R,S] at h
  simpa only [relfinrank_top_right,RatFunc.finrank_eq_max_natDegree,deg] using h.symm

def invariantField (σ : RatFunc K →ₐ[K] RatFunc K) : IntermediateField K (RatFunc K) where
  carrier := {x | σ x = x}
  zero_mem' := map_zero _
  one_mem' := map_one _
  add_mem' := by intro x y hx hy; change σ (x+y) = x+y; rw [map_add, hx, hy]
  mul_mem' := by intro x y hx hy; change σ (x*y) = x*y; rw [map_mul, hx, hy]
  inv_mem' := by intro x hx; change σ x⁻¹ = x⁻¹; rw [map_inv₀, hx]
  algebraMap_mem' := σ.commutes

/-- A nonidentity symmetry fixing a rational function of degree two fixes
exactly the rational functions generated by that function. -/
theorem quadratic_fixed (σ : RatFunc K →ₐ[K] RatFunc K) (g v : RatFunc K)
    (hg : deg g = 2) (hX : σ RatFunc.X ≠ RatFunc.X) (hs : σ g=g) (hv : σ v=v) :
    v ∈ K⟮g⟯ := by
  let E := invariantField σ
  have hle : K⟮g⟯ ≤ E := adjoin_simple_le_iff.mpr hs
  have mul := relfinrank_mul_finrank_top hle
  rw [g.finrank_eq_max_natDegree] at mul
  change _ = deg g at mul
  rw [hg] at mul
  have dn : Module.finrank E (RatFunc K) ∣ 2 :=
    ⟨relfinrank K⟮g⟯ E,by rw [mul_comm, mul]⟩
  have hne : Module.finrank E (RatFunc K) ≠ 1 := by
    intro hone
    rw [←relfinrank_top_right] at hone
    have htop := relfinrank_eq_one_iff.mp hone
    exact hX (htop (show (RatFunc.X : RatFunc K) ∈ (⊤ : IntermediateField K _) from trivial))
  have ht := ((Nat.dvd_prime Nat.prime_two).mp dn).resolve_left hne
  rw [ht] at mul
  exact (relfinrank_eq_one_iff.mp (show relfinrank K⟮g⟯ E = 1 by omega)) hv

def subst (g : RatFunc K) (hg : Transcendental K g) : RatFunc K →ₐ[K] RatFunc K :=
  K⟮g⟯.val.comp (RatFunc.algEquivOfTranscendental g hg).toAlgHom

@[simp] theorem subst_X (g : RatFunc K) (hg : Transcendental K g) :
    subst g hg RatFunc.X = g := RatFunc.algEquivOfTranscendental_X g hg

theorem factors {g v : RatFunc K} (hg : Transcendental K g) (hv : v ∈ K⟮g⟯) :
    ∃ q : RatFunc K, subst g hg q = v := by
  exact ⟨(RatFunc.algEquivOfTranscendental g hg).symm ⟨v,hv⟩, by simp [subst]⟩

end
end SunDescent

end

section

open Polynomial

namespace SunDescent
variable {K : Type*} [Field K]
noncomputable section

abbrev fraction (a b : K[X]) : RatFunc K := algebraMap K[X] (RatFunc K) a / algebraMap K[X] (RatFunc K) b

theorem deg_fraction (a b : K[X]) (ha : a ≠ 0) (hb : b ≠ 0) (cop : IsCoprime a b) :
    deg (fraction a b) = max a.natDegree b.natDegree := by
  let f := fraction a b
  have eq : f.num*b=a*f.denom := (RatFunc.num_mul_eq_mul_denom_iff hb).mpr rfl
  have u : a ∣ f.num := cop.dvd_of_dvd_mul_right (eq.symm ▸ dvd_mul_right a f.denom)
  have v : b ∣ f.denom := cop.symm.dvd_of_dvd_mul_left (eq ▸ dvd_mul_left b f.num)
  have fn : f≠0 := div_ne_zero (RatFunc.algebraMap_ne_zero ha) (RatFunc.algebraMap_ne_zero hb)
  apply congrArg₂ max
  · exact le_antisymm (natDegree_le_of_dvd (RatFunc.num_div_dvd a hb) ha)
      (natDegree_le_of_dvd u (RatFunc.num_ne_zero fn))
  · exact le_antisymm (natDegree_le_of_dvd (RatFunc.denom_div_dvd a b) hb)
      (natDegree_le_of_dvd v (RatFunc.denom_ne_zero f))

theorem transcendental_of_deg {f : RatFunc K} (hg : 0 < deg f) : Transcendental K f := by
  apply f.transcendental_of_ne_C
  rintro ⟨k,h⟩
  have hh := (f.eq_C_iff).mp ⟨k,h⟩
  simp [deg,hh.1,hh.2] at hg

def chart (A B : K) (x : RatFunc K) := x/(x^2+RatFunc.C A*x+RatFunc.C B)

theorem chart_degree (A B : K) (hB : B ≠ 0) : deg (chart A B RatFunc.X) = 2 := by
  let q : K[X] := X^2+C A*X+C B
  have hq : q.natDegree = 2 := by dsimp [q]; compute_degree <;> norm_num
  have hn : q≠0 := by intro e; simp [e] at hq
  have cop : IsCoprime X q := by
    refine ⟨-C B⁻¹*(X+C A),C B⁻¹,?_⟩
    dsimp [q]
    calc
      _ = C B⁻¹ * C B := by ring
      _ = 1 := by rw [←map_mul,inv_mul_cancel₀ hB,map_one]
  have eq : chart A B RatFunc.X = fraction X q := by
    simp [chart,fraction,q,RatFunc.algebraMap_X,RatFunc.algebraMap_C]
  rw [eq,deg_fraction X q X_ne_zero hn cop,hq,natDegree_X]; decide

theorem reciprocal_degree (B : K) (hB : B ≠ 0) : deg (RatFunc.C B/RatFunc.X) = 1 := by
  have eq : RatFunc.C B/RatFunc.X = fraction (C B) X := by
    simp [fraction,RatFunc.algebraMap_X,RatFunc.algebraMap_C]
  rw [eq, deg_fraction (C B) X (C_ne_zero.mpr hB) X_ne_zero _,natDegree_C,natDegree_X]; rfl
  exact ⟨C B⁻¹,0,by simp [←map_mul,hB]⟩

theorem square_degree : deg ((RatFunc.X : RatFunc K)^2) = 2 := by
  have e : (RatFunc.X : RatFunc K)^2 = algebraMap K[X] (RatFunc K) (X^2) := by rw [map_pow,RatFunc.algebraMap_X]
  rw [e,deg,RatFunc.num_algebraMap,RatFunc.denom_algebraMap,natDegree_pow,natDegree_X,natDegree_one]; decide

def flip (B : K) (hB : B≠0) : RatFunc K →ₐ[K] RatFunc K :=
  subst (RatFunc.C B/RatFunc.X) (transcendental_of_deg ((reciprocal_degree B hB).symm ▸ Nat.zero_lt_one))

@[simp] theorem flip_X (B : K) (hB : B≠0) : flip B hB RatFunc.X=RatFunc.C B/RatFunc.X := subst_X ..

theorem flip_nontrivial (B : K) (hB : B≠0) : flip B hB RatFunc.X ≠ RatFunc.X := by
  intro hx
  rw [flip_X,div_eq_iff RatFunc.X_ne_zero] at hx
  have e : (RatFunc.X : RatFunc K)^2 = RatFunc.C B := by simpa [pow_two] using hx.symm
  exact (transcendental_of_deg (f:=(RatFunc.X : RatFunc K)^2) (by rw [square_degree]; decide))
    (e ▸ isAlgebraic_algebraMap B)

theorem flip_chart (A B : K) (hB : B≠0) : flip B hB (chart A B RatFunc.X)=chart A B RatFunc.X := by
  have hn : RatFunc.C B ≠ 0 := (_root_.map_ne_zero _).mpr hB
  have formula (x : RatFunc K) (hx : x≠0) : chart A B x = (x+RatFunc.C A+RatFunc.C B/x)⁻¹ := by
    rw [chart, ←inv_div (x^2+RatFunc.C A*x+RatFunc.C B) x]
    apply congrArg Inv.inv
    field_simp [hx]
  have flip_const (c : K) : flip B hB (RatFunc.C c) = RatFunc.C c := (flip B hB).commutes c
  rw [formula _ RatFunc.X_ne_zero, map_inv₀, map_add, map_add, map_div₀,
    flip_X, flip_const, flip_const, div_div_cancel₀ hn]
  congr 1
  ring
theorem through_chart (A B : K) (hB : B≠0) (v : RatFunc K) (hv : flip B hB v = v) :
    ∃ q : RatFunc K, subst (chart A B RatFunc.X) (transcendental_of_deg (by rw [chart_degree A B hB]; decide)) q = v :=
  factors _ (quadratic_fixed _ _ _ (chart_degree A B hB) (flip_nontrivial B hB) (flip_chart A B hB) hv)

end
end SunDescent

end

section

/- # The conjugate degree-two maps on the discriminant minus seven CM model -/

namespace SunSevenIsogeny

variable {K : Type*} [Field K]

/-- Abscissa of the normalized Vélu isogeny with differential multiplier v. -/
def phiX (v X : K) := (X+(3*(4-v)^2-35)/(X-(4-v)))/v^2

/-- Ordinate of the normalized Vélu isogeny with differential multiplier v. -/
def phiY (v X Y : K) := Y*(1-(3*(4-v)^2-35)/(X-(4-v))^2)/v^3

/-- The two candidates for the traces of the CM endomorphisms satisfy
φ(P)+φ̄(P)=P on the generic point: φ(P), φ̄(P), and −P are collinear. -/
theorem trace_chord (v X Y : K) (hv : v^2=v-2) (hv0 : v≠0) (hc0 : 1-v≠0)
    (h₁ : X-(4-v)≠0) (h₂ : X-(4-(1-v))≠0) :
    (phiY v X Y + Y)*(phiX (1-v) X-X) = (phiY (1-v) X Y +Y)*(phiX v X-X) := by
  unfold phiX phiY
  field_simp [hv0,hc0,h₁,h₂]
  grobner

/-- Composition of the conjugate CM maps agrees with doubling in the
x-coordinate. -/
theorem norm_x (v X Y : K) (hv : v^2=v-2) (hv0 : v≠0) (hc0 : 1-v≠0)
    (hy : Y^2=X^3-35*X+98) (h₂Y : 2*Y≠0)
    (h₁ : X-(4-v)≠0) (h₂ : phiX v X - (4-(1-v))≠0) :
    phiX (1-v) (phiX v X) = ((3*X^2-35)/(2*Y))^2-2*X := by
  have h2 : (2:K) ≠ 0 := left_ne_zero_of_mul h₂Y
  have hY : Y ≠ 0 := right_ne_zero_of_mul h₂Y
  generalize hU : phiX v X = U at h₂ ⊢
  unfold phiX
  field_simp [hc0,h₂,h2,hY]
  rw [← hU]
  unfold phiX
  field_simp [hv0,h₁]
  rw [hy]
  clear hv0 hc0 h₂ h2 hY h₁ h₂Y hU hy
  grobner

/-- After translating the chosen two-torsion point to the origin, Vélu's
map sends a chord with nonzero intercept to the chord displayed here. -/
theorem velu_chord (A B m n x y : K) (he : y^2=x^3+A*x^2+B*x)
    (hl : y=m*x+n) (hx : x≠0) (hn : n≠0) :
    y*(1-B/x^2) = (m-B/n)*(x+A+B/x) + (n-A*m+(B/n)*m^2) := by
  field_simp [hx,hn]
  rw [hl] at he ⊢
  linear_combination -B * he

/-- The coordinate multiplier of Vélu's map is the logarithmic derivative
needed for its pullback of the invariant differential. -/
theorem phi_differential {L : Type*} [NontriviallyNormedField L] (v X : L)
    (h : X-(4-v) ≠ 0) :
    HasDerivAt (phiX v) ((1-(3*(4-v)^2-35)/(X-(4-v))^2)/v^2) X := by
  unfold phiX
  have e := (hasDerivAt_const X (3*(4-v)^2-35)).div ((hasDerivAt_id X).sub_const (4-v)) h
  simpa only [Pi.add_apply,Pi.div_apply,id_eq,zero_mul,zero_sub,zero_add,mul_one,neg_div,sub_eq_add_neg] using ((hasDerivAt_id X).add e).div_const (v^2)

/-- The ordinate of the composite fixes the sign of the norm-two map. -/
theorem norm_y (v X Y : K) (hv : v^2=v-2) (hv0 : v≠0) (hc0 : 1-v≠0)
    (hy : Y^2=X^3-35*X+98) (h₂Y : 2*Y≠0)
    (h₁ : X-(4-v)≠0) (h₂ : phiX v X - (4-(1-v))≠0) :
    let m := (3*X^2-35)/(2*Y)
    phiY (1-v) (phiX v X) (phiY v X Y) = m*(3*X-m^2)-Y := by
  dsimp only
  have h2 : (2:K) ≠ 0 := left_ne_zero_of_mul h₂Y
  have hY : Y ≠ 0 := right_ne_zero_of_mul h₂Y
  generalize hU : phiX v X = U at h₂ ⊢
  unfold phiY
  field_simp [hc0,h₂,h2,hY,hv0,h₁]
  rw [← hU]
  unfold phiX
  field_simp [hv0,h₁]
  rw [show Y^4=(Y^2)^2 by ring,hy]
  clear hv0 hc0 h₂ h2 hY h₁ h₂Y hU hy
  grobner

/-- The quotient by the point at x=0 has the same coordinates on the two
members of each kernel orbit. Coordinates are translated so that the other
two roots are e and f. -/
theorem kernel_translation (e f x y : K) (he : e≠0) (hf : f≠0) (hx : x≠0) :
    let u := e*f/x
    let w := -(e*f)*y/x^2
    (u-e)*(u-f)/u=(x-e)*(x-f)/x ∧
      (1-e*f/u^2)*w=(1-e*f/x^2)*y := by
  dsimp only
  constructor <;> field_simp [he,hf,hx] <;> ring

/-- Translation by the point at x=e becomes translation by the point
at zero on the quotient, separately for its abscissa and ordinate. -/
theorem other_translation (e f x y : K) (he : e≠0) (hx : x≠0)
    (hxe : x-e≠0) (hxf : x-f≠0) :
    let u := e*(x-f)/(x-e)
    let w := -e*(e-f)*y/(x-e)^2
    let X' := (x-e)*(x-f)/x
    let Y' := (1-e*f/x^2)*y
    (u-e)*(u-f)/u=(e-f)^2/X' ∧
      (1-e*f/u^2)*w=-(e-f)^2*Y'/X'^2 := by
  dsimp only
  constructor <;> field_simp [he,hx,hxe,hxf] <;> ring

end SunSevenIsogeny

end

section

/- Explicit degree-two complex multiplication formulas on the discriminant
−7 curve, in short Weierstrass coordinates. -/

namespace SunCoster

variable {K : Type*} [Field K]

/-- On the short model Y² = X³ − 35X + 98, the point at u=4−v
is the nontrivial kernel point for the 2-isogeny with multiplier v.
Here v is a root of X²−X+2. -/
theorem kernel_root {v : K} (hv : v^2=v-2) :
    (4-v)^3 - 35*(4-v)+98 = 0 := by
  linear_combination (11-v)*hv

/-- The rational map to the same short Weierstrass curve underlying the
degree-two CM generator. -/
theorem cm_generator {v X Y : K} (hv : v^2=v-2) (hv0 : v≠0)
    (hXY : Y^2=X^3-35*X+98) (hd : X≠4-v) :
    let u := 4-v
    let c := 3*u^2-35
    let X' := (X+c/(X-u))/v^2
    let Y' := (Y*(1-c/(X-u)^2))/v^3
    Y'^2 = X'^3-35*X'+98 := by
  let u := 4-v
  let c := 3*u^2-35
  let d := X-u
  let w := c/d
  have hd0 : d≠0 := sub_ne_zero.mpr hd
  have dw : d*w=c := by dsimp only [w]; field_simp
  have hu := kernel_root hv
  have hy : Y^2=d^2*(d+3*u+w) := by
    dsimp only [d] at dw ⊢
    dsimp only [u,c] at dw ⊢
    linear_combination hXY + hu - (X-(4-v))*dw
  have hdy : 1-c/d^2=(d-w)/d := by field_simp; linear_combination dw
  have v4 : v^4=2-3*v := by linear_combination (v^2+v-1)*hv
  have v6 : v^6=2+5*v := by linear_combination (v^4+v^3-v^2-3*v-1)*hv
  have ha : -3*u^2-4*c= -35*v^4 := by
    dsimp only [u,c]; linear_combination -15*hv + 35*v4
  have hb : 2*u^3-8*u*c=98*v^6 := by
    dsimp only [u,c]; linear_combination (22*v-242)*hv - 98*v6
  change (Y*(1-c/d^2)/v^3)^2=( (X+w)/v^2)^3-35*((X+w)/v^2)+98
  rw [hdy]
  have he : (Y*((d-w)/d))^2 = (X+w)^3-35*v^4*(X+w)+98*v^6 := by
    rw [mul_pow,hy,div_pow]
    field_simp [hd0]
    have h : X = d+u := by dsimp [d]; ring
    rw [h]
    linear_combination (d+u+w)*ha + hb - 4*(d+w+3*u)*dw
  have scale (A B : K) (h : A^2=B^3-35*v^4*B+98*v^6) :
      (A/v^3)^2=(B/v^2)^3-35*(B/v^2)+98 := by
    rw [div_pow,div_pow,h]
    field_simp [hv0]
  exact scale _ _ he

/-- Translation by the other nonzero two-torsion point acts by reciprocal
substitution on the Coster–van Hamme parameter t=X/Y. -/
theorem translate_parameter {x y e f : K} (he : e≠0) (hef : e≠f)
    (_hx : x≠e) (hy : y≠0) (hxy : y^2=x*(x-e)*(x-f)) :
    let X' := e*(x-f)/(x-e)
    let Y' := -e*(e-f)*y/(x-e)^2
    (x/y)*(X'/Y') = -1/(e-f) := by
  dsimp only
  field_simp [he,sub_ne_zero.mpr hef,sub_ne_zero.mpr _hx,hy]
  linear_combination hxy

end SunCoster

end

section

namespace SunCoster
open Polynomial SunDescent SunSevenIsogeny
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

theorem short_smooth {x y : K} (h : y^2=x^3-35*x+98) :
    (shortCurve K).Nonsingular x y := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  refine ⟨short_equation.mpr h,?_⟩
  change 0*y ≠ 3*x^2+2*0*x+(-35) ∨ y≠ -y-0*x-0
  by_contra! bad
  obtain ⟨ha,hb⟩ := bad
  grobner

theorem phi_abscissa_degree (v : K) (hv : v^2=v-2) :
    deg (phiX (RatFunc.C v) RatFunc.X) = 2 := by
  let e := 4-v
  let c := 3*e^2-35
  have hv0 : v≠0 := by intro z; simp [z] at hv
  have hc : c≠0 := by dsimp only [c,e]; intro h; grobner
  let F : K[X] := X*(X-C e)+C c
  let H : K[X] := C (v^2)*(X-C e)
  have fdeg : F.natDegree=2 := by dsimp only [F]; compute_degree; norm_num
  have hdeg : H.natDegree=1 := by dsimp only [H]; compute_degree; norm_num [hv0]
  have hF : F≠0 := by rintro z; simp [z] at fdeg
  have hH : H≠0 := by rintro z; simp [z] at hdeg
  have cop : IsCoprime F H := by
    refine ⟨C c⁻¹,-C c⁻¹*C ((v^2)⁻¹)*X,?_⟩
    have hh : C ((v^2)⁻¹)*C (v^2)= (1:K[X]) := by rw [←map_mul,inv_mul_cancel₀ (pow_ne_zero 2 hv0),map_one]
    have hcc : C c⁻¹*C c= (1:K[X]) := by rw [←map_mul,inv_mul_cancel₀ hc,map_one]
    dsimp only [F,H]
    linear_combination hcc - C c⁻¹*X*(X-C e)*hh
  have hden : (RatFunc.X : RatFunc K)-RatFunc.C e≠0 := by
    intro z
    exact RatFunc.transcendental_X (K:=K) ((sub_eq_zero.mp z) ▸ isAlgebraic_algebraMap e)
  have eq : phiX (RatFunc.C v) RatFunc.X = fraction F H := by
    have hce : RatFunc.C e = 4-RatFunc.C v := by simp [e,map_ofNat]
    have hcc : RatFunc.C c = 3*(RatFunc.C e)^2-35 := by simp [c,map_ofNat]
    simp only [fraction,F,H,map_add,map_mul,map_sub,map_pow,RatFunc.algebraMap_C,RatFunc.algebraMap_X]
    rw [phiX,←hce,←hcc]
    have hz : RatFunc.C v≠0 := (_root_.map_ne_zero _).2 hv0
    field_simp [hden,hz]
  rw [eq,deg_fraction F H hF hH cop,fdeg,hdeg]; decide

/-- For the identity point P and the Vélu generator V, the x-coordinate
of P−V is the x-coordinate of its conjugate Vélu generator. -/
theorem conjugate_chord_square {v x y : K} (hv : v^2=v-2) (hv0 : v≠0) (hc0 : 1-v≠0)
    (hxy : y^2=x^3-35*x+98) (h₁ : x-(4-v)≠0) (h₂ : x-(4-(1-v))≠0) :
    (y+phiY v x y)^2=(x-phiX v x)^2*(x+phiX v x+phiX (1-v) x) := by
  unfold phiY phiX
  rw [show y+y*(1-(3*(4-v)^2-35)/(x-(4-v))^2)/v^3 =
      y*(1+(1-(3*(4-v)^2-35)/(x-(4-v))^2)/v^3) by ring, mul_pow, hxy]
  field_simp [hv0,hc0,h₁,h₂]
  clear hv0 hc0 h₁ h₂ hxy
  grobner

end
end SunCoster

end

section

namespace SunCoster.Torsion
open WeierstrassCurve.Affine SunSevenIsogeny
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

def tx (r x : K) := r+(3*r^2-35)/(x-r)
def ty (r x y : K) := -(3*r^2-35)*y/(x-r)^2

/-- Translation by the point (r,0) on the short Weierstrass curve. -/
theorem translation [DecidableEq K] {r x y : K} (hr : (shortCurve K).Nonsingular r 0)
    (h : (shortCurve K).Nonsingular x y) (hx : x≠r) :
    ∃ j : (shortCurve K).Nonsingular (tx r x) (ty r x y),
      Point.some x y h + Point.some r 0 hr = Point.some _ _ j := by
  have e := short_equation.mp h.1
  have f := short_equation.mp hr.1
  have h₁ : (y/(x-r))^2-x-r=tx r x := by
    unfold tx; field_simp [sub_ne_zero.mpr hx]
    linear_combination e - f
  have h₂ : -(y/(x-r)*(tx r x-x)+y)=ty r x y := by
    unfold tx ty; field_simp [sub_ne_zero.mpr hx]; ring
  rw [Point.add_of_X_ne hx]
  generalize_proofs k
  have Xeq : (shortCurve K).addX x r ((shortCurve K).slope x r y 0)=tx r x := by
    simpa [slope_of_X_ne hx,addX,shortCurve] using h₁
  have Yeq : (shortCurve K).addY x r y ((shortCurve K).slope x r y 0)=ty r x y := by
    rw [addY,negAddY,Xeq]
    simpa [slope_of_X_ne hx,negY,shortCurve] using h₂
  exact ⟨Xeq ▸ Yeq ▸ k,by congr⟩

/-- Translation by the kernel point fixes both degree-two image coordinates. -/
theorem kernel_image (v x y : K) (hv : v^2=v-2) (hx : x≠4-v) :
    phiX v (tx (4-v) x)=phiX v x ∧
    phiY v (tx (4-v) x) (ty (4-v) x y)=phiY v x y := by
  let r := 4-v
  let c := 3*r^2-35
  have hc : c≠0 := by dsimp [c,r]; intro h; grobner
  have h : x-r≠0 := sub_ne_zero.mpr hx
  have d : tx r x-r=c/(x-r) := by simp [tx,c]
  change (tx r x+c/(tx r x-r))/v^2 = (x+c/(x-r))/v^2 ∧
    ty r x y*(1-c/(tx r x-r)^2)/v^3 = y*(1-c/(x-r)^2)/v^3
  rw [d]
  dsimp only [tx,ty]
  change (r+c/(x-r)+c/(c/(x-r)))/v^2 = _ ∧ -c*y/(x-r)^2*(1-c/(c/(x-r))^2)/v^3=_
  constructor <;> congr 1 <;> field_simp [hc,h] <;> ring

/-- Translation by (-7,0) changes the norm-two image by the point (3+v,0). -/
theorem minus_seven_image (v x y : K) (hv : v^2=v-2) (hx : x≠ -7)
    (ha : x≠4-v) (hb : x≠3+v) :
    phiX v (tx (-7) x)=tx (3+v) (phiX v x) ∧
    phiY v (tx (-7) x) (ty (-7) x y)=ty (3+v) (phiX v x) (phiY v x y) := by
  have hv0 : v≠0 := by intro e; rw [e] at hv; norm_num at hv
  have he : -7-(4-v)≠0 := by intro e; grobner
  have hu : x-(-7)≠0 := sub_ne_zero.mpr hx
  have hA := sub_ne_zero.mpr ha
  have hB := sub_ne_zero.mpr hb
  have h₁ : tx (-7) x-(4-v)=(-7-(4-v))*(x-(3+v))/(x-(-7)) := by
    unfold tx; field_simp [hu]; linear_combination hv
  have h₂ : phiX v x-(3+v)=(x-(-7))*(x-(3+v))/(v^2*(x-(4-v))) := by
    unfold phiX; field_simp [hv0,hA]; grobner
  change (tx (-7) x+(3*(4-v)^2-35)/(tx (-7) x-(4-v)))/v^2 =
      3+v+(3*(3+v)^2-35)/(phiX v x-(3+v)) ∧
    ty (-7) x y*(1-(3*(4-v)^2-35)/(tx (-7) x-(4-v))^2)/v^3 =
      -(3*(3+v)^2-35)*phiY v x y/(phiX v x-(3+v))^2
  rw [h₁,h₂]
  unfold tx ty phiY
  constructor <;> field_simp [hv0,hu,hA,hB,he] <;> clear * - hv <;> grobner

/-- After adding (4−v,0), the Coster parameter is transformed by a reciprocal. -/
theorem parameter_kernel (v x y : K) (hv : v^2=v-2) (he : y^2=x^3-35*x+98)
    (hx : x≠4-v) (hy : y≠0) :
    ((x+7)/y)*((tx (4-v) x+7)/ty (4-v) x y)=1/(2*v-1) := by
  have hc : 3*(4-v)^2-35≠0 := by intro h; grobner
  have hs : 2*v-1≠0 := by intro h; grobner
  let r := 4-v
  let k := 3*r^2-35
  let d := x-r
  have hd : d≠0 := sub_ne_zero.mpr hx
  have hk : k≠0 := hc
  change ((x+7)/y)*((r+k/d+7)/(-k*y/d^2))=1/(2*v-1)
  field_simp [hd,hk,hy,hs]
  dsimp only [r,k,d]
  clear * - hv he
  grobner

end
end SunCoster.Torsion

end

section

/- Degree estimates on the symmetric square of the Kummer line. -/

namespace SunCoster

open Polynomial

private theorem symmetric_bezout {R : Type*} [CommRing R] {a b c d : R}
    (ab : IsCoprime a b) (cd : IsCoprime c d) :
    ∃ i j k : R, i*(a*c)+j*(a*d+b*c)+k*(b*d)=1 := by
  obtain ⟨u,v,hu⟩:=ab
  obtain ⟨w,z,hw⟩:=cd
  let g := u*z-v*w
  let h := 1+g*(a*d)
  refine ⟨h*u*w-g^2*(b*d), h*v*w+g^2*(a*d), h*v*z,?_⟩
  have hh : (u*a+v*b)*(w*c+z*d)=1 := by rw [hu,hw,one_mul]
  dsimp only [h,g]
  linear_combination (1+(u*z-v*w)*(a*d))*hh

/-- A polynomial triple representing a pair of rational functions has the
canonical symmetric coordinates as a common-factor-free representative. -/
theorem symmetric_factor {R : Type*} [CommRing R] {a b c d F G H : R}
    (ab : IsCoprime a b) (cd : IsCoprime c d)
    (h₁ : F*(a*d+b*c)=G*(a*c)) (h₂ : F*(b*d)=H*(a*c))
    (h₃ : G*(b*d)=H*(a*d+b*c)) :
    ∃ e : R, F=e*(a*c) ∧ G=e*(a*d+b*c) ∧ H=e*(b*d) := by
  obtain ⟨i,j,k,hu⟩ := symmetric_bezout ab cd
  refine ⟨i*F+j*G+k*H,?_,?_,?_⟩
  · linear_combination -F*hu+j*h₁+k*h₂
  · linear_combination -G*hu-i*h₁+k*h₃
  · linear_combination -H*hu-i*h₂-j*h₃

variable {K : Type*} [Field K]

/-- The symmetric coordinate height bounds the sum of the two rational
function degrees; this includes numerator and denominator cancellations. -/
theorem symmetric_degree {a b c d F G H : K[X]} (hb : b≠0)
    (hd : d≠0) (ab : IsCoprime a b) (cd : IsCoprime c d)
    (h₁ : F*(a*d+b*c)=G*(a*c)) (h₂ : F*(b*d)=H*(a*c))
    (h₃ : G*(b*d)=H*(a*d+b*c)) (hH : H≠0)
    {n : ℕ} (hF' : F.natDegree≤n) (hG' : G.natDegree≤n) (hH' : H.natDegree≤n) :
    max a.natDegree b.natDegree + max c.natDegree d.natDegree ≤ n := by
  obtain ⟨e,hF,hG,hD⟩:=symmetric_factor ab cd h₁ h₂ h₃
  have he : e≠0 := by rintro rfl; simp [hD] at hH
  have edge (u v : K[X]) (hu : u≠0) (hv : v≠0) (h : (e*(u*v)).natDegree≤n) :
      u.natDegree+v.natDegree≤n := by
    rw [natDegree_mul he (mul_ne_zero hu hv),natDegree_mul hu hv] at h
    omega
  have hbd:=edge b d hb hd (hD ▸ hH')
  by_cases ha : a=0
  · subst a
    simp only [zero_mul,zero_add] at hG
    by_cases hc : c=0
    · simpa [hc] using hbd
    have hbc:=edge b c hb hc (hG ▸ hG')
    simp only [natDegree_zero, Nat.zero_max]
    omega
  by_cases hc : c=0
  · subst c
    simp only [mul_zero,add_zero] at hG
    have had:=edge a d ha hd (hG ▸ hG')
    simp only [natDegree_zero,Nat.zero_max]
    omega
  have hac:=edge a c ha hc (hF ▸ hF')
  by_cases had : (a*d).natDegree=(b*c).natDegree
  · rw [natDegree_mul ha hd,natDegree_mul hb hc] at had
    omega
  have ne : a*d+b*c≠0 := by
    intro h
    have h' : a*d=-(b*c) := eq_neg_of_add_eq_zero_left h
    exact had (by rw [h',natDegree_neg])
  rw [hG,natDegree_mul he ne] at hG'
  rcases lt_or_gt_of_ne had with h|h
  · rw [natDegree_add_eq_right_of_natDegree_lt h,natDegree_mul hb hc] at hG'
    rw [natDegree_mul ha hd,natDegree_mul hb hc] at h
    omega
  · rw [natDegree_add_eq_left_of_natDegree_lt h,natDegree_mul ha hd] at hG'
    rw [natDegree_mul ha hd,natDegree_mul hb hc] at h
    omega

/-- An exact parallelogram upper bound gives the quadratic upper bound for
the degrees of integer multiplications by a discrete second-difference argument. -/
theorem degree_mul_bound (h : ℕ → ℕ) (h0 : h 0=0) (h1 : h 1≤1)
    (hd : ∀ n, h (n+2)+h n ≤ 2*h (n+1)+2) (n : ℕ) : h n ≤ n^2 := by
  have deriv (j : ℕ) : h (j+1) ≤ h j+2*j+1 := by
    induction j with
    | zero => simpa [h0] using h1
    | succ j ih =>
      change h (j+2) ≤ h (j+1)+2*(j+1)+1
      have hh:=hd j; omega
  induction n with
  | zero => simp [h0]
  | succ n ih => have h':=deriv n; nlinarith

end SunCoster

end

section

/- The exact quadratic degree bound for the addition pair on a Jacobi quartic. -/

namespace SunCoster

open Polynomial

variable {K : Type*} [Field K]

noncomputable def height (f : RatFunc K) := max f.num.natDegree f.denom.natDegree

private theorem parts (f : RatFunc K) :
    f * algebraMap K[X] (RatFunc K) f.denom = algebraMap K[X] (RatFunc K) f.num :=
  ((div_eq_iff (RatFunc.algebraMap_ne_zero f.denom_ne_zero)).mp f.num_div_denom).symm

/-- The rational function degree of the two conjugate addition results is
bounded by twice the sum of the two input degrees. The equations are precisely
the product and sum formulas for the squared parameters of P+Q and P−Q. -/
theorem kummer_degree (A Δ : K) (u v r s : RatFunc K)
    (hn : 1-RatFunc.C Δ*u*v ≠ 0)
    (hp : r*s*(1-RatFunc.C Δ*u*v)^2 = (u-v)^2)
    (ht : (r+s)*(1-RatFunc.C Δ*u*v)^2 =
      2*(u+v - 4*RatFunc.C A*u*v + RatFunc.C Δ*u*v*(u+v))) :
    height r + height s ≤ 2*(height u+height v) := by
  let S := u.num*v.num
  let T := u.num*v.denom+u.denom*v.num
  let U := u.denom*v.denom
  let V := u.num*v.denom-u.denom*v.num
  let F := V^2
  let G := 2*(T*U-C (4*A)*S*U+C Δ*S*T)
  let H := (U-C Δ*S)^2
  let ι := algebraMap K[X] (RatFunc K)
  have hnum (z : RatFunc K) : ι z.num = z*ι z.denom := (parts z).symm
  let B := ι u.denom * ι v.denom
  have hB : B≠0 := mul_ne_zero (RatFunc.algebraMap_ne_zero u.denom_ne_zero)
    (RatFunc.algebraMap_ne_zero v.denom_ne_zero)
  have es : ι S = u*v*B := by dsimp [S,B]; rw [map_mul,hnum u,hnum v]; ring
  have et : ι T = (u+v)*B := by dsimp [T,B]; rw [map_add,map_mul,map_mul,hnum u,hnum v]; ring
  have eu : ι U = B := map_mul ..
  have ev : ι V = (u-v)*B := by dsimp [V,B]; rw [map_sub,map_mul,map_mul,hnum u,hnum v]; ring
  have hC (a : K) : ι (C a)=RatFunc.C a := RatFunc.algebraMap_C ..
  have eF : ι F= ((u-v)*B)^2 := by dsimp only [F]; rw [map_pow,ev]
  have eH : ι H= ((1-RatFunc.C Δ*u*v)*B)^2 := by
    calc
      _ = (ι U-ι (C Δ)*ι S)^2 := by simp only [H,map_pow,map_sub,map_mul]
      _ = _ := by rw [eu,es,hC]; ring
  have eG : ι G= 2*(u+v-4*RatFunc.C A*u*v+RatFunc.C Δ*u*v*(u+v))*B^2 := by
    calc
      _ = 2*(ι T*ι U-ι (C (4*A))*ι S*ι U+ι (C Δ)*ι S*ι T) := by
        simp only [G,map_mul,map_ofNat,map_add,map_sub]
      _ = _ := by rw [eu,es,et,hC,hC, map_mul RatFunc.C 4 A,map_ofNat]; ring
  have eP : ι F = r*s*ι H := by rw [eF,eH]; linear_combination -B^2*hp
  have eT : ι G = (r+s)*ι H := by rw [eG,eH]; linear_combination -B^2*ht
  have inj := RatFunc.algebraMap_injective (K:=K)
  let n := height u+height v
  have partdeg (f : RatFunc K) : f.num.natDegree≤height f ∧ f.denom.natDegree≤height f :=
    ⟨le_max_left .., le_max_right ..⟩
  have bS : S.natDegree≤n := natDegree_mul_le_of_le (partdeg u).1 (partdeg v).1
  have bU : U.natDegree≤n := natDegree_mul_le_of_le (partdeg u).2 (partdeg v).2
  have bV : V.natDegree≤n := (natDegree_sub_le _ _).trans (max_le
    (natDegree_mul_le_of_le (partdeg u).1 (partdeg v).2)
    (natDegree_mul_le_of_le (partdeg u).2 (partdeg v).1))
  have bT : T.natDegree≤n := (natDegree_add_le _ _).trans (max_le
    (natDegree_mul_le_of_le (partdeg u).1 (partdeg v).2)
    (natDegree_mul_le_of_le (partdeg u).2 (partdeg v).1))
  apply symmetric_degree r.denom_ne_zero s.denom_ne_zero r.isCoprime_num_denom s.isCoprime_num_denom
    (F:=F) (G:=G) (H:=H)
  · apply inj
    simp only [map_mul,map_add]
    change (ι F)*((ι r.num)*(ι s.denom)+(ι r.denom)*(ι s.num))=
      (ι G)*((ι r.num)*(ι s.num))
    rw [eP,eT,hnum r,hnum s]; ring
  · apply inj
    simp only [map_mul]
    change (ι F)*((ι r.denom)*(ι s.denom))=(ι H)*((ι r.num)*(ι s.num))
    rw [eP,hnum r,hnum s]; ring
  · apply inj
    simp only [map_mul,map_add]
    change (ι G)*((ι r.denom)*(ι s.denom))=
      (ι H)*((ι r.num)*(ι s.denom)+(ι r.denom)*(ι s.num))
    rw [eT,hnum r,hnum s]; ring
  · intro z; rw [z,map_zero] at eH; exact (pow_ne_zero 2 (mul_ne_zero hn hB)) eH.symm
  · exact natDegree_pow_le.trans (Nat.mul_le_mul_left 2 bV)
  · have mid : (C (4*A)*S).natDegree≤n :=
      (natDegree_C_mul_le ..).trans bS
    have delt : (C Δ*S).natDegree≤n := (natDegree_C_mul_le ..).trans bS
    have k := (natDegree_add_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le
      (natDegree_mul_le_of_le bT bU) (natDegree_mul_le_of_le mid bU)))
      (natDegree_mul_le_of_le delt bT))
    change (2*(T*U-C (4*A)*S*U+C Δ*S*T)).natDegree≤2*n
    rw [show (2:K[X])=C 2 from (map_ofNat C 2).symm]
    exact (natDegree_C_mul_le ..).trans (by simpa [two_mul] using k)
  · have bu := (natDegree_sub_le U (C Δ*S)).trans (max_le bU ((natDegree_C_mul_le ..).trans bS))
    exact natDegree_pow_le.trans (Nat.mul_le_mul_left 2 bu)

/-- The two identities in the theorem follow by squaring the Jacobi addition
formula at Q and at −Q and eliminating the two radical coordinates. -/
theorem jacobi_pair {A Δ u v U V r s : K} (hu : U^2=1-2*A*u^2+Δ*u^4)
    (hv : V^2=1-2*A*v^2+Δ*v^4) (hd : 1-Δ*u^2*v^2 ≠ 0)
    (hr : r*(1-Δ*u^2*v^2)=u*V+v*U) (hs : s*(1-Δ*u^2*v^2)=u*V-v*U) :
    r^2*s^2*(1-Δ*u^2*v^2)^2 = (u^2-v^2)^2 ∧
    (r^2+s^2)*(1-Δ*u^2*v^2)^2 =
      2*(u^2+v^2-4*A*u^2*v^2+Δ*u^2*v^2*(u^2+v^2)) := by
  let d := 1-Δ*u^2*v^2
  have product : r*s*d = u^2-v^2 := by
    apply mul_right_cancel₀ hd
    calc
      _ = (r*d)*(s*d) := by ring
      _ = (u*V+v*U)*(u*V-v*U) := by rw [hr,hs]
      _ = _ := by linear_combination u^2*hv-v^2*hu
  constructor
  · change r^2*s^2*d^2=(u^2-v^2)^2
    rw [←mul_pow,←mul_pow,product]
  · change (r^2+s^2)*d^2=_
    calc
      _ = (r*d)^2+(s*d)^2 := by ring
      _ = (u*V+v*U)^2+(u*V-v*U)^2 := by rw [hr,hs]
      _ = _ := by linear_combination 2*u^2*hv+2*v^2*hu

/-- Quadratic growth along an integer multiplication sequence. -/
theorem jacobi_integer_degree (A Δ : K) (f : ℕ → RatFunc K) (f0 : f 0=0)
    (regular : ∀ n, 1-RatFunc.C Δ*f (n+1)*f 1≠0)
    (product : ∀ n, f (n+2)*f n*(1-RatFunc.C Δ*f (n+1)*f 1)^2=(f (n+1)-f 1)^2)
    (sum : ∀ n, (f (n+2)+f n)*(1-RatFunc.C Δ*f (n+1)*f 1)^2=
      2*(f (n+1)+f 1-4*RatFunc.C A*f (n+1)*f 1+
        RatFunc.C Δ*f (n+1)*f 1*(f (n+1)+f 1))) (n : ℕ) :
    height (f n) ≤ n^2*height (f 1) := by
  let d i := height (f i)
  have h0 : d 0=0 := by simp [d,f0,height]
  have step j : d (j+1) ≤ d j+(2*j+1)*d 1 := by
    induction j with
    | zero => simp [h0]
    | succ j ih =>
      change d (j+2)≤d (j+1)+(2*(j+1)+1)*d 1
      have h : d (j+2)+d j≤2*(d (j+1)+d 1) :=
        kummer_degree A Δ _ _ _ _ (regular j) (product j) (sum j)
      nlinarith
  change d n≤n^2*d 1
  induction n with
  | zero => simp [h0]
  | succ n ih => have h:=step n; nlinarith

/-- Conjugate addition maps with degree d and inputs of degrees x² and
7y² have d at most x²+7y². -/
theorem jacobi_norm_bound (A Δ : K) (u v r s : RatFunc K) (x y : ℕ)
    (du : height u ≤ x^2) (dv : height v ≤ 7*y^2) (eqd : height r=height s)
    (hn : 1-RatFunc.C Δ*u*v≠0)
    (hp : r*s*(1-RatFunc.C Δ*u*v)^2=(u-v)^2)
    (ht : (r+s)*(1-RatFunc.C Δ*u*v)^2=
      2*(u+v-4*RatFunc.C A*u*v+RatFunc.C Δ*u*v*(u+v))) :
    height r ≤ x^2+7*y^2 := by
  have h := kummer_degree A Δ u v r s hn hp ht
  omega

end SunCoster

end

section

/- The exact quadratic degree bound for the addition pair on a Jacobi quartic. -/

namespace SunCoster

open Polynomial

variable {K : Type*} [Field K]



private theorem short_parts (f : RatFunc K) :
    f * algebraMap K[X] (RatFunc K) f.denom = algebraMap K[X] (RatFunc K) f.num :=
  ((div_eq_iff (RatFunc.algebraMap_ne_zero f.denom_ne_zero)).mp f.num_div_denom).symm

/-- The Kummer parallelogram on the short Weierstrass curve. -/
theorem short_degree (a b : K) (u v r s : RatFunc K) (hn : u≠v)
    (hp : r*s*(u-v)^2=(u*v-RatFunc.C a)^2-4*RatFunc.C b*(u+v))
    (ht : (r+s)*(u-v)^2=2*(u+v)*(u*v+RatFunc.C a)+4*RatFunc.C b) :
    height r+height s ≤ 2*(height u+height v) := by
  let S := u.num*v.num
  let T := u.num*v.denom+u.denom*v.num
  let U := u.denom*v.denom
  let V := u.num*v.denom-u.denom*v.num
  let F := (S-C a*U)^2-C (4*b)*T*U
  let G := C (2:K)*T*(S+C a*U)+C (4*b)*U^2
  let H := V^2
  let ι := algebraMap K[X] (RatFunc K)
  have hnum (z : RatFunc K) : ι z.num = z*ι z.denom := (short_parts z).symm
  let B := ι u.denom * ι v.denom
  have hB : B≠0 := mul_ne_zero (RatFunc.algebraMap_ne_zero u.denom_ne_zero)
    (RatFunc.algebraMap_ne_zero v.denom_ne_zero)
  have es : ι S = u*v*B := by dsimp [S,B]; rw [map_mul,hnum u,hnum v]; ring
  have et : ι T = (u+v)*B := by dsimp [T,B]; rw [map_add,map_mul,map_mul,hnum u,hnum v]; ring
  have eu : ι U = B := map_mul ..
  have ev : ι V = (u-v)*B := by dsimp [V,B]; rw [map_sub,map_mul,map_mul,hnum u,hnum v]; ring
  have hC (a : K) : ι (C a)=RatFunc.C a := RatFunc.algebraMap_C ..
  have eF : ι F=((u*v-RatFunc.C a)^2 - 4*RatFunc.C b*(u+v))*B^2 := by
    calc
      _ = (ι S-ι (C a)*ι U)^2-ι (C (4*b))*ι T*ι U := by simp only [F,map_sub,map_pow,map_mul]
      _ = _ := by rw [eu,es,et,hC,hC,map_mul RatFunc.C 4 b,map_ofNat]; ring
  have eG : ι G=(2*(u+v)*(u*v+RatFunc.C a)+4*RatFunc.C b)*B^2 := by
    calc
      _ = ι (C (2:K))*ι T*(ι S+ι (C a)*ι U)+ι (C (4*b))*(ι U)^2 := by
        simp only [G,map_add,map_mul,map_pow]
      _ = _ := by rw [eu,es,et,hC,hC,hC,map_mul RatFunc.C 4 b]; simp only [map_ofNat]; ring
  have eH : ι H=((u-v)*B)^2 := by dsimp only [H]; rw [map_pow,ev]
  have eP : ι F=r*s*ι H := by rw [eF,eH]; linear_combination -B^2*hp
  have eT : ι G=(r+s)*ι H := by rw [eG,eH]; linear_combination -B^2*ht
  have inj := RatFunc.algebraMap_injective (K:=K)
  let n := height u+height v
  have partdeg (f : RatFunc K) : f.num.natDegree≤height f ∧ f.denom.natDegree≤height f :=
    ⟨le_max_left .., le_max_right ..⟩
  have bS : S.natDegree≤n := natDegree_mul_le_of_le (partdeg u).1 (partdeg v).1
  have bU : U.natDegree≤n := natDegree_mul_le_of_le (partdeg u).2 (partdeg v).2
  have bV : V.natDegree≤n := (natDegree_sub_le _ _).trans (max_le
    (natDegree_mul_le_of_le (partdeg u).1 (partdeg v).2)
    (natDegree_mul_le_of_le (partdeg u).2 (partdeg v).1))
  have bT : T.natDegree≤n := (natDegree_add_le _ _).trans (max_le
    (natDegree_mul_le_of_le (partdeg u).1 (partdeg v).2)
    (natDegree_mul_le_of_le (partdeg u).2 (partdeg v).1))
  apply symmetric_degree r.denom_ne_zero s.denom_ne_zero r.isCoprime_num_denom s.isCoprime_num_denom
    (F:=F) (G:=G) (H:=H)
  · apply inj
    simp only [map_mul,map_add]
    change (ι F)*((ι r.num)*(ι s.denom)+(ι r.denom)*(ι s.num))=
      (ι G)*((ι r.num)*(ι s.num))
    rw [eP,eT,hnum r,hnum s]; ring
  · apply inj
    simp only [map_mul]
    change (ι F)*((ι r.denom)*(ι s.denom))=(ι H)*((ι r.num)*(ι s.num))
    rw [eP,hnum r,hnum s]; ring
  · apply inj
    simp only [map_mul,map_add]
    change (ι G)*((ι r.denom)*(ι s.denom))=
      (ι H)*((ι r.num)*(ι s.denom)+(ι r.denom)*(ι s.num))
    rw [eT,hnum r,hnum s]; ring
  · intro z; rw [z,map_zero] at eH
    exact (pow_ne_zero 2 (mul_ne_zero (sub_ne_zero.mpr hn) hB)) eH.symm
  · have aU : (C a*U).natDegree≤n := (natDegree_C_mul_le ..).trans bU
    have bT' : (C (4*b)*T).natDegree≤n := (natDegree_C_mul_le ..).trans bT
    have bdiff := (natDegree_sub_le S (C a*U)).trans (max_le bS aU)
    exact (natDegree_sub_le _ _).trans (max_le (natDegree_pow_le.trans (Nat.mul_le_mul_left 2 bdiff))
      (by simpa [two_mul] using natDegree_mul_le_of_le bT' bU))
  · have aU : (C a*U).natDegree≤n := (natDegree_C_mul_le ..).trans bU
    have dT : (C (2:K)*T).natDegree≤n := (natDegree_C_mul_le ..).trans bT
    have bsum := (natDegree_add_le S (C a*U)).trans (max_le bS aU)
    apply (natDegree_add_le _ _).trans
    apply max_le
    · simpa [two_mul] using natDegree_mul_le_of_le dT bsum
    · exact (natDegree_C_mul_le ..).trans (natDegree_pow_le.trans (Nat.mul_le_mul_left 2 bU))
  · exact natDegree_pow_le.trans (Nat.mul_le_mul_left 2 bV)

/-- The unordered x-coordinates of two chord sums in short Weierstrass form. -/
theorem short_chord {a b u v y z r s : K} (hu : y^2=u^3+a*u+b) (hv : z^2=v^3+a*v+b)
    (hd : u≠v) (hr : r*((u-v)^2)=(y-z)^2-(u+v)*(u-v)^2)
    (hs : s*((u-v)^2)=(y+z)^2-(u+v)*(u-v)^2) :
    r*s*(u-v)^2=(u*v-a)^2-4*b*(u+v) ∧
    (r+s)*(u-v)^2=2*(u+v)*(u*v+a)+4*b := by
  constructor
  · apply mul_right_cancel₀ (pow_ne_zero 2 (sub_ne_zero.mpr hd))
    calc
      _ = (r*(u-v)^2)*(s*(u-v)^2) := by ring
      _ = (y^2+z^2-(u+v)*(u-v)^2)^2-4*y^2*z^2 := by rw [hr,hs]; ring
      _ = _ := by rw [hu,hv]; ring
  · linear_combination hr+hs+2*hu+2*hv

/-- The same pair of chord identities for actual affine group points of E7b. -/
theorem short_xRep_chord [DecidableEq K] {u v y z : K} (P : (shortCurve K).Nonsingular u y)
    (Q : (shortCurve K).Nonsingular v z) (hd : u≠v) :
    let p := WeierstrassCurve.Affine.Point.some u y P
    let q := WeierstrassCurve.Affine.Point.some v z Q
    let r := (p+q).xRep 0
    let s := (p-q).xRep 0
    r*s*(u-v)^2 = (u*v+35)^2-392*(u+v) ∧
      (r+s)*(u-v)^2 = 2*(u+v)*(u*v-35)+392 := by
  let p := WeierstrassCurve.Affine.Point.some u y P
  let q := WeierstrassCurve.Affine.Point.some v z Q
  have hu := short_equation.mp P.1
  have hv := short_equation.mp Q.1
  have h := short_chord (a:=(-35:K)) (b:=98) (u:=u) (v:=v) (y:=y) (z:=z)
    (r:=(p+q).xRep 0) (s:=(p-q).xRep 0)
    (by linear_combination hu) (by linear_combination hv) hd
  have h1 : (p+q).xRep 0*(u-v)^2=(y-z)^2-(u+v)*(u-v)^2 := by
    dsimp only [p,q]
    rw [WeierstrassCurve.Affine.Point.add_of_X_ne hd,WeierstrassCurve.Affine.Point.xRep_some]
    simp [WeierstrassCurve.Affine.slope_of_X_ne hd,shortCurve]
    field_simp [sub_ne_zero.mpr hd]
    <;> ring
  have h2 : (p-q).xRep 0*(u-v)^2=(y+z)^2-(u+v)*(u-v)^2 := by
    dsimp only [p,q]
    rw [sub_eq_add_neg,WeierstrassCurve.Affine.Point.neg_some,
      WeierstrassCurve.Affine.Point.add_of_X_ne hd,WeierstrassCurve.Affine.Point.xRep_some]
    simp [WeierstrassCurve.Affine.slope_of_X_ne hd,shortCurve,WeierstrassCurve.Affine.negY]
    field_simp [sub_ne_zero.mpr hd]
    <;> ring
  obtain ⟨hp,ht⟩:=h h1 h2
  exact ⟨by linear_combination hp,by linear_combination ht⟩

end SunCoster

end

section

/- Pointwise degree bounds on the discriminant −7 Weierstrass model. -/

namespace SunCoster

open Polynomial WeierstrassCurve.Affine

variable {K L : Type*} [Field K] [Field L]

private theorem ratio_height {r : RatFunc K} {F H : K[X]} (hH : H≠0)
    (eqr : r=algebraMap _ _ F/algebraMap _ _ H) {n : ℕ}
    (hF' : F.natDegree≤n) (hH' : H.natDegree≤n) : height r ≤ n := by
  by_cases hF : F=0
  · simp [hF] at eqr
    simp [eqr,height]
  exact max_le ((natDegree_le_of_dvd ((RatFunc.num_dvd hF).mpr ⟨H,hH,eqr⟩) hF).trans hF')
    ((natDegree_le_of_dvd ((RatFunc.denom_dvd hH).mpr ⟨F,eqr⟩) hH).trans hH')

theorem short_double_degree {u r : RatFunc K} (hn : 4*(u^3-35*u+98)≠0)
    (hr : r*(4*(u^3-35*u+98))=u^4+70*u^2-784*u+1225) :
    height r ≤ 4*height u := by
  let N := u.num
  let D := u.denom
  let F := N^4+70*N^2*D^2-784*N*D^3+1225*D^4
  let H := 4*D*(N^3-35*N*D^2+98*D^3)
  let ι := algebraMap K[X] (RatFunc K)
  have hN : ι N = u*ι D := (div_eq_iff (RatFunc.algebraMap_ne_zero u.denom_ne_zero)).mp u.num_div_denom
  have hD : ι D≠0 := RatFunc.algebraMap_ne_zero u.denom_ne_zero
  have hH : ι H=4*(u^3-35*u+98)*(ι D)^4 := by
    simp only [H,map_mul,map_add,map_sub,map_pow,map_ofNat,hN]; ring
  have hF : ι F=(u^4+70*u^2-784*u+1225)*(ι D)^4 := by
    simp only [F,map_mul,map_add,map_sub,map_pow,map_ofNat,hN]; ring
  have nz : ι H≠0 := by rw [hH]; exact mul_ne_zero hn (pow_ne_zero 4 hD)
  have hdegN : N.natDegree≤height u := le_max_left ..
  have hdegD : D.natDegree≤height u := le_max_right ..
  apply ratio_height (F:=F) (H:=H)
  · exact fun h => nz (by rw [h,map_zero])
  · apply (eq_div_iff nz).mpr
    rw [hH,hF]; linear_combination (ι D)^4*hr
  · dsimp only [F]; compute_degree <;> omega
  · dsimp only [H]; compute_degree <;> omega

theorem short_xRep_double [DecidableEq L] {x y : L}
    (P : (shortCurve L).Nonsingular x y) (hn : 2*y≠0) :
    let p := Point.some x y P
    (p+p).xRep 0*(4*(x^3-35*x+98))=x^4+70*x^2-784*x+1225 := by
  dsimp only
  have hxy := short_equation.mp P.1
  have hny : y≠(shortCurve L).negY x y := by
    change y≠ -y-0*x-0
    intro h; apply hn; linear_combination h
  rw [Point.add_self_of_Y_ne hny,Point.xRep_some]
  simp only [Matrix.cons_val_zero,addX,slope_of_Y_ne rfl hny]
  change (((3*x^2+2*0*x+(-35)-0*y)/(y-(-y-0*x-0)))^2+
    0*((3*x^2+2*0*x+(-35)-0*y)/(y-(-y-0*x-0)))-0-x-x)*_=_
  rw [←hxy]
  have ey : y-(-y-0*x-0)=2*y := by ring
  rw [ey]
  simp only [zero_mul,mul_zero,add_zero,sub_zero]
  rw [show 4*y^2=(2*y)^2 by ring,sub_mul,sub_mul,div_pow,div_mul_cancel₀ _ (pow_ne_zero 2 hn)]
  linear_combination -8*x*hxy

private theorem height_of_one {ι : RatFunc K →+* L} {v : RatFunc K} (hv : ι v=1) :
    height v=0 := by
  have h : v=1 := ι.injective (by rw [hv,map_one])
  simp [h,height]

theorem short_double [DecidableEq L] (ι : RatFunc K →+* L) (P : (shortCurve L).Point)
    (u r : RatFunc K) (hu : ι u=P.xRep 0) (hr : ι r=(P+P).xRep 0) :
    height r ≤ 4*height u := by
  cases P with
  | zero =>
    rw [←Point.zero_def] at hr
    rw [height_of_one (ι:=ι) (by simpa using hr)]
    omega
  | some x y hp =>
    have hxu : ι u=x := by simpa only [Point.xRep_some,Matrix.cons_val_zero] using hu
    have hxy:=short_equation.mp hp.1
    by_cases hz : 2*y=0
    · have hny : y=(shortCurve L).negY x y := by
        change y= -y-0*x-0
        linear_combination hz
      rw [Point.add_self_of_Y_eq hny,Point.xRep_zero] at hr
      rw [height_of_one (ι:=ι) hr]
      omega
    · apply short_double_degree
      · intro h
        have he:=congrArg ι h
        simp only [map_mul,map_add,map_sub,map_pow,map_ofNat,map_zero,hxu] at he
        rw [←hxy] at he
        apply pow_ne_zero 2 hz
        linear_combination he
      · apply ι.injective
        simp only [map_mul,map_add,map_sub,map_pow,map_ofNat,hxu,hr]
        exact short_xRep_double hp hz

/-- Upper parallelogram identity for actual elliptic-curve points over an
extension of the rational function field. Each coordinate is supplied by its
unique rational-function representative. The formula xRep(O)₀=1 gives
height zero also in the exceptional addition cases. -/
theorem short_parallelogram [DecidableEq L] (ι : RatFunc K →+* L)
    (P Q : (shortCurve L).Point) (u v r s : RatFunc K)
    (hu : ι u=P.xRep 0) (hv : ι v=Q.xRep 0)
    (hr : ι r=(P+Q).xRep 0) (hs : ι s=(P-Q).xRep 0) :
    height r+height s≤2*(height u+height v) := by
  by_cases hPQ : P.xRep=Q.xRep
  · have uv : u=v := ι.injective (by rw [hu,hv,hPQ])
    rw [←uv]
    rcases Point.eq_or_eq_neg_of_xRep_eq_xRep hPQ with h|h
    · subst Q
      have hd:=short_double ι P u r hu hr
      have hzero : height s=0 := height_of_one (ι:=ι) (by simpa using hs)
      omega
    · have e : Q= -P := by rw [h,neg_neg]
      subst Q
      have hd:=short_double ι P u s hu (by simpa only [sub_neg_eq_add] using hs)
      have hzero : height r=0 := height_of_one (ι:=ι) (by simpa using hr)
      omega
  cases P with
  | zero =>
    rw [←Point.zero_def] at hr hs
    have rv : r=v := ι.injective (by simpa only [hr,hv,zero_add])
    have sv : s=v := ι.injective (by simpa only [hs,hv,zero_sub,Point.xRep_neg])
    rw [rv,sv]
    omega
  | some X Y p =>
    cases Q with
    | zero =>
      rw [←Point.zero_def] at hr hs
      have rU : r=u := ι.injective (by simpa only [hr,hu,add_zero])
      have sU : s=u := ι.injective (by simpa only [hs,hu,sub_zero])
      rw [rU,sU]
      omega
    | some W Z q =>
      have hxu : ι u=X := by simpa only [Point.xRep_some,Matrix.cons_val_zero] using hu
      have hxv : ι v=W := by simpa only [Point.xRep_some,Matrix.cons_val_zero] using hv
      have hdeg : X≠W := by rintro rfl; exact hPQ rfl
      obtain ⟨prod,sm⟩:=short_xRep_chord p q hdeg
      apply short_degree (-35) 98 u v r s
      · intro huv; exact hdeg (hxu.symm.trans ((congrArg ι huv).trans hxv))
      · apply ι.injective
        simp only [map_mul,map_add,map_sub,map_pow,map_neg,map_ofNat,hxu,hxv,hr,hs]
        linear_combination prod
      · apply ι.injective
        simp only [map_mul,map_add,map_sub,map_pow,map_neg,map_ofNat,hxu,hxv,hr,hs]
        linear_combination sm

end SunCoster

end

section

namespace SunCoster
open WeierstrassCurve.Affine
noncomputable section

variable {K L : Type*} [Field K] [Field L] [DecidableEq L]
variable (ι : RatFunc K →+* L) (Y : L) (w : RatFunc K) (hw : ι w=Y^2)

def rationalCoordinates : (shortCurve L).Point → Prop
  | .zero => True
  | .some x y _ => ∃ a b : RatFunc K, ι a=x ∧ ι b*Y=y

omit [DecidableEq L] in
private theorem rational_neg (P : (shortCurve L).Point) (h : rationalCoordinates ι Y P) :
    rationalCoordinates ι Y (-P) := by
  cases P with
  | zero => change True; trivial
  | some x y p =>
    obtain ⟨a,b,ha,hb⟩ := h
    rw [Point.neg_some]
    exact ⟨a,-b,ha,by simp only [map_neg,neg_mul,hb,negY,shortCurve,zero_mul,sub_zero]⟩

include w hw in
private theorem rational_add (P Q : (shortCurve L).Point) (hP : rationalCoordinates ι Y P)
    (hQ : rationalCoordinates ι Y Q) : rationalCoordinates ι Y (P+Q) := by
  cases P with
  | zero => simpa only [←Point.zero_def,zero_add] using hQ
  | some x y p =>
    cases Q with
    | zero => simpa only [←Point.zero_def,add_zero] using hP
    | some u v q =>
      obtain ⟨a,b,ha,hb⟩ := hP
      obtain ⟨c,d,hc,hd⟩ := hQ
      let m := (shortCurve L).slope x u y v
      have coords {s : RatFunc K} (hs : ι s*Y=m) :
          ∃ a' b' : RatFunc K, ι a'=(shortCurve L).addX x u m ∧
            ι b'*Y=(shortCurve L).addY x u y m := by
        let a' := w*s^2-a-c
        have ea' : ι a'=(shortCurve L).addX x u m := by
          simp only [a',map_sub,map_mul,map_pow,hw,ha,hc,←hs,addX,shortCurve,
            zero_mul,add_zero,sub_zero,mul_pow]
          ring
        refine ⟨a',s*(a-a')-b,ea',?_⟩
        simp only [map_sub,map_mul,ha,ea',addY,negY,negAddY,shortCurve,
          zero_mul,sub_zero]
        change (ι s*(x-(shortCurve L).addX x u m)-ι b)*Y = -(m*((shortCurve L).addX x u m-x)+y)
        linear_combination ((x-(shortCurve L).addX x u m))*hs - hb
      by_cases hx : x=u
      · by_cases hy : y=(shortCurve L).negY u v
        · rw [Point.add_of_Y_eq hx hy]
          trivial
        rw [Point.add_of_Y_ne hy]
        apply coords (s:=(3*a^2-35)/(2*b*w))
        dsimp only [m]
        rw [slope_of_Y_ne hx hy]


        simp only [map_div₀,map_sub,map_mul,map_pow,map_ofNat,ha,hw,negY,shortCurve,
          zero_mul,mul_zero,add_zero,sub_zero]
        rw [← hb]
        by_cases hY : Y=0
        · simp [hY]
        by_cases hb' : ι b=0
        · simp [hb']
        field_simp
        ring
      · rw [Point.add_of_X_ne hx]
        apply coords (s:=(b-d)/(a-c))
        dsimp only [m]
        rw [slope_of_X_ne hx]
        simp only [map_div₀,map_sub,ha,hc,←hb,←hd]
        ring

def rationalSubgroup : AddSubgroup (shortCurve L).Point where
  carrier := rationalCoordinates ι Y
  zero_mem' := trivial
  neg_mem' := rational_neg ι Y _
  add_mem' := rational_add ι Y w hw _ _

theorem exists_abscissa (P : rationalSubgroup ι Y w hw) :
    ∃ u : RatFunc K, ι u=P.val.xRep 0 := by
  obtain ⟨P,hP⟩ := P
  cases P with
  | zero => exact ⟨1,map_one _⟩
  | some x y pt =>
    obtain ⟨u,_,hu,_⟩ := hP
    exact ⟨u,hu⟩

def abscissa (P : rationalSubgroup ι Y w hw) : RatFunc K :=
  (exists_abscissa ι Y w hw P).choose

theorem abscissa_apply (P : rationalSubgroup ι Y w hw) :
    ι (abscissa ι Y w hw P)=P.val.xRep 0 := (exists_abscissa ι Y w hw P).choose_spec

end
end SunCoster

end

section

namespace SunCoster.ChartAction
open SunSevenIsogeny WeierstrassCurve.Affine SunCoster.Torsion
noncomputable section
variable {K L : Type*} [Field K] [Field L] [CharZero L] [DecidableEq L]

def param : (shortCurve L).Point → L
  | .zero => 0
  | .some x y _ => (x+7)/y

omit [CharZero L] in
@[simp] theorem param_neg (P : (shortCurve L).Point) : param (-P) = -param P := by
  cases P with
  | zero => simp [←Point.zero_def,param]
  | some x y p => rw [Point.neg_some]; simp [param,shortCurve,negY,div_neg]

theorem param_map (f : L →+* L) (P : (shortCurve L).Point) :
    param (shortMap f P)=f (param P) := by
  cases P with
  | zero => exact (map_zero f).symm
  | some x y p => simp [param,map_ofNat]

omit [CharZero L] in
theorem two_torsion (e : L) (h : (shortCurve L).Nonsingular e 0) :
    Point.some e 0 h+Point.some e 0 h=0 := by
  apply Point.add_self_of_Y_eq
  simp [shortCurve,negY]

def T₀ : (shortCurve L).Point := Point.some (-7) 0 (short_smooth (by norm_num))

theorem param_translate (P : (shortCurve L).Point) : param (P+T₀) = -param P := by
  cases P with
  | zero => simp [←Point.zero_def,T₀,param]
  | some x y p =>
    have hy := short_equation.mp p.1
    by_cases hx : x= -7
    · subst x
      have sy : y=0 := by rw [show (-7:L)^3-35*(-7)+98=0 by norm_num] at hy; exact (pow_eq_zero_iff (by decide : 2≠0)).mp hy
      subst y
      rw [T₀,two_torsion]
      simp [param]
    · obtain ⟨j,e⟩ := translation (short_smooth (by norm_num : (0:L)^2=(-7)^3-35*(-7)+98)) p hx
      rw [T₀,e]
      change (tx (-7) x+7)/ty (-7) x y= -((x+7)/y)
      by_cases hy0 : y=0
      · simp [ty,hy0]
      unfold tx ty
      have hd : x-(-7)≠0 := sub_ne_zero.mpr hx
      field_simp [hd,hy0]
      ring

omit [CharZero L] in
theorem rational_param_ratio (ι : RatFunc K →+* L) (Y : L)
    (p : (shortCurve L).Nonsingular (ι RatFunc.X) Y)
    (U : (shortCurve L).Point) (hU : rationalCoordinates ι Y U) :
    ∃ a : RatFunc K, ι a=param U/param (Point.some _ _ p) := by
  cases U with
  | zero => exact ⟨0,by simp [param]⟩
  | some x y u =>
    obtain ⟨a,b,ha,hb⟩ := hU
    by_cases hY : Y=0
    · exact ⟨0,by simp [param,hY]⟩
    refine ⟨(a+7)/(b*(RatFunc.X+7)),?_⟩
    simp only [param,map_div₀,map_add,map_ofNat,map_mul,ha,←hb]
    by_cases hz : ι b=0
    · simp [hz]
    by_cases hw : ι RatFunc.X+7=0
    · simp [hw]
    field_simp [hY,hz,hw]

private theorem odd_smul {G : Type*} [AddCommGroup G] {T : G} (ht : T+T=0) {n : ℤ}
    (hn : Odd n) : n•T=T := by
  obtain ⟨k,hk⟩ := hn
  rw [hk,add_zsmul,one_zsmul,mul_comm,mul_zsmul,two_zsmul,ht,zsmul_zero,zero_add]

/-- Both possible extensions of the translated coefficient embedding fix the
ratio of the Coster parameters. The sign choice for the quadratic ordinate
therefore disappears on descent. -/
theorem ratio_fixed (f : L →+* L) (P V T : (shortCurve L).Point)
    (hT : T+T=0) (m n : ℤ) (hm : Odd m)
    (action :
      (shortMap f P=P+T₀ ∧ shortMap f V=V+T) ∨
      (shortMap f P= -(P+T₀) ∧ shortMap f V= -(V+T))) :
    f (param (m•P+(2*n)•V)/param P)=param (m•P+(2*n)•V)/param P := by
  have ht₀ : T₀ + T₀ = (0:(shortCurve L).Point) := two_torsion ..
  have hr : m•(P+T₀)+(2*n)•(V+T)=(m•P+(2*n)•V)+T₀ := by
    rw [zsmul_add,zsmul_add,odd_smul ht₀ hm,show (2*n)•T=0 by rw [mul_comm,mul_zsmul,two_zsmul,hT,zsmul_zero]]
    abel
  rw [map_div₀,←param_map,←param_map,map_add,map_zsmul,map_zsmul]
  rcases action with ⟨hP,hV⟩|⟨hP,hV⟩
  · rw [hP,hV,hr,param_translate,param_translate,neg_div_neg_eq]
  · rw [hP,hV,zsmul_neg,zsmul_neg,←neg_add,hr,param_neg,param_neg,param_translate,param_translate,neg_neg,neg_neg]

end
end SunCoster.ChartAction

end

section

namespace SunCoster.ChartAction
open SunSevenIsogeny WeierstrassCurve.Affine SunCoster.Torsion
noncomputable section
variable {L : Type*} [Field L] [CharZero L] [DecidableEq L]

/-- The two possible actions of a lift on the generic point act with the
same sign on its CM image. -/
theorem generator_action (f : L →+* L) (t Y v : L) (hv : v^2=v-2)
    (hP : (shortCurve L).Nonsingular t Y)
    (hV : (shortCurve L).Nonsingular (phiX v t) (phiY v t Y))
    (hc : f v=v) (hfx : f t=tx (-7) t)
    (hfy : f Y=ty (-7) t Y ∨ f Y= -(ty (-7) t Y))
    (hx : t≠ -7) (ha : t≠4-v) (hb : t≠3+v) (hVx : phiX v t≠3+v) :
    ∃ T : (shortCurve L).Point, T+T=0 ∧
    let P := Point.some _ _ hP
    let V := Point.some _ _ hV
    (shortMap f P=P+T₀ ∧ shortMap f V=V+T) ∨
    (shortMap f P= -(P+T₀) ∧ shortMap f V= -(V+T)) := by
  have hroot : (0:L)^2=(3+v)^3-35*(3+v)+98 := by grobner
  let hT := short_smooth hroot
  let T := Point.some _ _ hT
  refine ⟨T,two_torsion ..,?_⟩
  dsimp only
  obtain ⟨hp,ep⟩ := translation (short_smooth (by norm_num : (0:L)^2=(-7)^3-35*(-7)+98)) hP hx
  obtain ⟨hq,eq⟩ := translation hT hV hVx
  obtain ⟨ex,ey⟩ := minus_seven_image v t Y hv hx ha hb
  have efX : f (phiX v t)=tx (3+v) (phiX v t) := by
    calc
      _ = phiX v (f t) := by simp [phiX,hc,map_ofNat]
      _ = _ := hfx ▸ ex
  have efY : f (phiY v t Y)=phiY v (tx (-7) t) (f Y) := by
    simp only [phiY,map_div₀,map_mul,map_sub,map_one,map_ofNat,map_pow,hfx,hc]
  change (shortMap f (Point.some t Y hP)=Point.some t Y hP+Point.some _ _ _ ∧
    shortMap f (Point.some _ _ hV)=Point.some _ _ hV+T) ∨
    (shortMap f (Point.some t Y hP)= -(Point.some t Y hP+Point.some _ _ _) ∧
    shortMap f (Point.some _ _ hV)= -(Point.some _ _ hV+T))
  simp only [T,ep,eq,shortMap_some,Point.neg_some,Point.some.injEq,efX,hfx,true_and]
  rcases hfy with h|h
  · exact Or.inl ⟨h,efY.trans (h ▸ ey)⟩
  · right
    simp only [shortCurve,negY,zero_mul,sub_zero]
    refine ⟨h,?_⟩
    rw [efY,h,←ey]
    simp [phiY,neg_div]

end
end SunCoster.ChartAction

end

section

namespace SunDescent
open Polynomial
noncomputable section
variable {K : Type*} [Field K]

def shiftX (c : K) : RatFunc K := RatFunc.X+RatFunc.C c

theorem shiftX_degree (c : K) : deg (shiftX c)=1 := by
  have he : shiftX c=algebraMap K[X] (RatFunc K) (X+C c) := by
    simp [shiftX,RatFunc.algebraMap_X,RatFunc.algebraMap_C]
  rw [he,deg,RatFunc.num_algebraMap,RatFunc.denom_algebraMap,natDegree_one,max_zero]
  compute_degree; norm_num

def shift (c : K) := subst (shiftX c) (transcendental_of_deg (by rw [shiftX_degree]; decide))

@[simp] theorem shift_X (c : K) : shift c RatFunc.X=shiftX c := subst_X ..

/-- The involution on the short-model coordinate associated to translation
by a two-torsion point with abscissa r. Its centered action is u ↦ B/u. -/
def translatedFlip (r B : K) (hB : B≠0) : RatFunc K →ₐ[K] RatFunc K :=
  (shift (-r)).comp ((flip B hB).comp (shift r))

theorem translatedFlip_X (r B : K) (hB : B≠0) :
    translatedFlip r B hB RatFunc.X = RatFunc.C B/shiftX (-r)+RatFunc.C r := by
  have comm (f : RatFunc K →ₐ[K] RatFunc K) (k : K) : f (RatFunc.C k)=RatFunc.C k :=
    f.commutes k
  simp only [translatedFlip,AlgHom.comp_apply,shift_X]
  change shift (-r) (flip B hB (RatFunc.X+RatFunc.C r))=_
  simp only [map_add,map_div₀,comm,flip_X,shift_X]

theorem translatedFlip_center (r B : K) (hB : B≠0) :
    translatedFlip r B hB (shiftX (-r))=RatFunc.C B/shiftX (-r) := by
  change translatedFlip r B hB (RatFunc.X+RatFunc.C (-r))=_
  rw [map_add,translatedFlip_X,show translatedFlip r B hB (RatFunc.C (-r))=RatFunc.C (-r)
    from (translatedFlip r B hB).commutes (-r),map_neg,add_neg_cancel_right]

theorem translatedFlip_nontrivial (r B : K) (hB : B≠0) :
    translatedFlip r B hB RatFunc.X ≠ RatFunc.X := by
  intro h
  have fix : translatedFlip r B hB (shiftX (-r)) = shiftX (-r) := by
    change translatedFlip r B hB (RatFunc.X+RatFunc.C (-r)) = RatFunc.X+RatFunc.C (-r)
    rw [map_add,h,show translatedFlip r B hB (RatFunc.C (-r)) = RatFunc.C (-r)
      from (translatedFlip r B hB).commutes (-r)]
  have tr : Transcendental K (shiftX (-r)) :=
    transcendental_of_deg (by rw [shiftX_degree]; decide)
  have nz : shiftX (-r)≠0 := by rintro e; exact tr (e ▸ isAlgebraic_zero)
  rw [translatedFlip_center,div_eq_iff nz] at fix
  apply tr
  refine ⟨X^2-C B,?_,?_⟩
  · intro z
    have hd : (X^2-C B).natDegree=2 := by compute_degree; norm_num
    simp [z] at hd
  · simp only [map_sub,map_pow,aeval_X,aeval_C,sub_eq_zero]
    change shiftX (-r)^2=RatFunc.C B
    simpa only [pow_two] using fix.symm

def translatedChart (r A B : K) := chart A B (shiftX (-r))

theorem translatedChart_degree (r A B : K) (hB : B≠0) : deg (translatedChart r A B)=2 := by
  have h : shift (-r) (chart A B RatFunc.X)=translatedChart r A B := by
    simp only [chart,translatedChart,map_div₀,map_add,map_mul,map_pow,
      show ∀ k : K, shift (-r) (RatFunc.C k)=RatFunc.C k from (shift (-r)).commutes,shift_X]
  rw [←h,degree_substitution,chart_degree _ _ hB,shift_X,shiftX_degree,mul_one]

theorem translatedFlip_chart (r A B : K) (hB : B≠0) :
    translatedFlip r B hB (translatedChart r A B)=translatedChart r A B := by
  let f := translatedFlip r B hB
  let s := shift (-r)
  have mapchart (φ : RatFunc K →ₐ[K] RatFunc K) (v : RatFunc K) :
      φ (chart A B v)=chart A B (φ v) := by
    simp only [chart,map_div₀,map_add,map_mul,map_pow,
      show ∀ k : K, φ (RatFunc.C k)=RatFunc.C k from φ.commutes]
  have h := congrArg s (flip_chart A B hB)
  simp only [mapchart,flip_X,map_div₀,show s (RatFunc.C B)=RatFunc.C B from s.commutes B,
    show s RatFunc.X=shiftX (-r) from shift_X _] at h
  simpa only [translatedChart,mapchart,translatedFlip_center] using h

theorem through_translated_chart (r A B : K) (hB : B≠0) (v : RatFunc K)
    (hv : translatedFlip r B hB v=v) :
    ∃ q : RatFunc K, subst (translatedChart r A B)
      (transcendental_of_deg (by rw [translatedChart_degree _ _ _ hB]; decide)) q=v :=
  factors _ (quadratic_fixed _ _ _ (translatedChart_degree _ _ _ hB)
    (translatedFlip_nontrivial _ _ hB) (translatedFlip_chart _ _ _ hB) hv)

end
end SunDescent

end

section

namespace SunCoster.ChartAction
open SunDescent SunSevenIsogeny WeierstrassCurve.Affine SunCoster.Torsion Polynomial
noncomputable section
variable (K : Type*) [Field K] [CharZero K]

def radicand : RatFunc K := RatFunc.X^3-35*RatFunc.X+98

abbrev DeckField := (X^2-C (radicand K)).SplittingField

abbrev incl : RatFunc K →+* DeckField K := algebraMap _ _

abbrev tau : RatFunc K →ₐ[K] RatFunc K :=
  translatedFlip (-7:K) 112 (by norm_num)

abbrev tauChart := translatedChart (-7:K) (-21) 112

theorem tau_X :
    tau K RatFunc.X=tx (-7) RatFunc.X := by
  rw [tau,translatedFlip_X]
  simp only [shiftX,map_neg,map_ofNat,neg_neg,tx]
  norm_num
  ring

theorem tau_const (c : K) : tau K (RatFunc.C c)=RatFunc.C c := (tau K).commutes c

theorem tauChart_degree : deg (tauChart K)=2 := translatedChart_degree _ _ _ (by norm_num)

theorem chart_ratio_descends [DecidableEq (DeckField K)] (v : K) (hv : v^2=v-2) (Y : DeckField K)
    (hP : (shortCurve _).Nonsingular (incl K RatFunc.X) Y)
    (hV : (shortCurve _).Nonsingular (phiX (incl K (RatFunc.C v)) (incl K RatFunc.X))
      (phiY (incl K (RatFunc.C v)) (incl K RatFunc.X) Y))
    (m n : ℤ) (hm : Odd m)
    (hU : rationalCoordinates (incl K) Y (m•(Point.some _ _ hP)+(2*n)•(Point.some _ _ hV))) :
    ∃ q : RatFunc K, incl K (subst (tauChart K)
      (transcendental_of_deg (by rw [tauChart_degree]; decide)) q) =
      param (m•(Point.some _ _ hP)+(2*n)•(Point.some _ _ hV))/param (Point.some _ _ hP) := by
  let ι := incl K
  let x := ι RatFunc.X
  let z := ι (RatFunc.C v)
  let P := Point.some _ _ hP
  let V := Point.some _ _ hV
  let U := m•P+(2*n)•V
  let g : RatFunc K →+* DeckField K := ι.comp (tau K).toRingHom
  have gX : g RatFunc.X=tx (-7) x := by
    change ι (tau K RatFunc.X)=_
    simp only [tau_X,tx,map_add,map_sub,map_mul,map_pow,map_div₀,map_neg,map_ofNat,x]
  have hc (k : K) : g (RatFunc.C k)=ι (RatFunc.C k) := congrArg ι (tau_const K k)
  have generic (c : K) : x≠ι (RatFunc.C c) := by
    intro h
    exact RatFunc.transcendental_X (K:=K) ((ι.injective h) ▸ isAlgebraic_algebraMap c)
  have hx : x≠ -7 := by simpa only [map_neg,map_ofNat] using generic (-7)
  have ha : x≠4-z := by simpa only [map_sub,map_ofNat,z] using generic (4-v)
  have hb : x≠3+z := by simpa only [map_add,map_ofNat,z] using generic (3+v)
  have hv' : z^2=z-2 := by simpa only [z,map_pow,map_sub,map_ofNat] using congrArg (fun k => ι (RatFunc.C k)) hv
  have hVx : phiX z x≠3+z := by
    intro h
    have bada : phiX (RatFunc.C v) RatFunc.X = RatFunc.C (3+v) := by
      apply ι.injective
      simpa only [phiX,map_sub,map_ofNat,map_pow,map_add,map_mul,map_div₀,x,z] using h
    have hd := phi_abscissa_degree v hv
    rw [bada] at hd
    simp only [deg,RatFunc.num_C,RatFunc.denom_C,natDegree_C,natDegree_one,max_self] at hd
    omega
  let Y' := ty (-7) x Y
  obtain ⟨ht,_⟩ := translation (short_smooth (by norm_num : (0:DeckField K)^2=(-7)^3-35*(-7)+98)) hP hx
  have hY' : Y'^2=g (radicand K) := by
    simp only [radicand,map_add,map_sub,map_pow,map_mul,map_ofNat,gX]
    exact short_equation.mp ht.1
  obtain ⟨f,hf⟩ := lift_quadratic g (radicand K) Y' hY'
  have ex (a : RatFunc K) : f (ι a)=g a := hf a
  have hY : Y^2=ι (radicand K) := by
    simp only [radicand,map_add,map_sub,map_pow,map_mul,map_ofNat]
    exact short_equation.mp hP.1
  have esq : (f Y)^2=Y'^2 := by rw [←map_pow,hY,ex,hY']
  have ey := sq_eq_sq_iff_eq_or_eq_neg.mp esq
  obtain ⟨T,hT,act⟩ := generator_action f x Y z hv' hP hV (by rw [ex,hc]) (by rw [ex,gX])
    ey hx ha hb hVx
  obtain ⟨a,ea⟩ := rational_param_ratio ι Y hP U hU
  have hfix := ratio_fixed f P V T hT m n hm act
  have hτ : tau K a=a := ι.injective (by
    change g a=ι a
    rw [←ex,ea]
    exact hfix)
  obtain ⟨q,hq⟩ := through_translated_chart (-7:K) (-21) 112 (by norm_num) a hτ
  exact ⟨q,(congrArg ι hq).trans ea⟩

end
end SunCoster.ChartAction

end

section

namespace SunDescent

variable {K : Type*} [Field K]
noncomputable section

theorem deg_square (f : RatFunc K) : deg (f^2) = 2 * deg f := by
  by_cases h : deg f = 0
  · have z : f.num.natDegree=0 ∧ f.denom.natDegree=0 := Nat.max_eq_zero_iff.mp h
    obtain ⟨c,rfl⟩ := f.eq_C_iff.mpr z
    rw [←map_pow RatFunc.C c 2]
    simp only [deg,RatFunc.num_C,RatFunc.denom_C,Polynomial.natDegree_C,Polynomial.natDegree_one,max_self,mul_zero]
  · let φ := subst f (transcendental_of_deg (Nat.pos_of_ne_zero h))
    have ht := degree_substitution φ ((RatFunc.X : RatFunc K)^2)
    rw [map_pow,square_degree] at ht
    simpa [φ] using ht

/-- The degree of the map in the local parameter `T=x/y` equals its degree on
the x-coordinate. Both squares are related by the same degree-two chart. -/
theorem chart_height_transfer (A B : K) (hB : B≠0) (R q : RatFunc K) (hR : Transcendental K R)
    (hX : subst R hR (chart A B RatFunc.X) =
      subst (chart A B RatFunc.X) (transcendental_of_deg (by rw [chart_degree A B hB]; decide))
        (RatFunc.X*q^2)) :
    deg (RatFunc.X * subst ((RatFunc.X : RatFunc K)^2)
        (transcendental_of_deg (by rw [square_degree]; decide)) q) = deg R := by
  let ξ := (RatFunc.X : RatFunc K)
  let hξ : Transcendental K (ξ^2) := transcendental_of_deg (by rw [square_degree]; decide)
  let ψ := subst (ξ^2) hξ
  let t := ξ * ψ q
  have ht : ψ (ξ * q^2) = t^2 := by simp [t,ψ,ξ,mul_pow]
  have hd := congrArg deg hX
  rw [degree_substitution (subst R hR) (chart A B RatFunc.X),
    degree_substitution (subst (chart A B RatFunc.X) _) (RatFunc.X*q^2)] at hd
  simp only [subst_X,chart_degree A B hB] at hd
  have de := degree_substitution ψ (ξ*q^2)
  rw [ht,deg_square] at de
  have sq : deg (ψ ξ)=2 := by simp [ψ,ξ,square_degree]
  rw [sq] at de
  change 2 * deg t = deg (RatFunc.X*q^2)*2 at de
  change deg t=deg R
  omega

end
end SunDescent

end

section

/- # The invariant differential under addition on a short Weierstrass model -/

namespace SunCoster

variable {K : Type*} [Field K]

/-- On a chord the symmetric expressions for the two intersection abscissas
give a division-free description of the derivative of the slope. -/
theorem chord_derivative (D : Derivation ℤ K K) (A B x₁ x₂ y₁ y₂ g₁ g₂ : K)
    (e₁ : y₁^2=x₁^3+A*x₁+B) (e₂ : y₂^2=x₂^3+A*x₂+B) (hd : x₁≠x₂)
    (hx₁ : D x₁=2*g₁*y₁) (hx₂ : D x₂=2*g₂*y₂)
    (hy₁ : D y₁=g₁*(3*x₁^2+A)) (hy₂ : D y₂=g₂*(3*x₂^2+A)) :
    let m := (y₁-y₂)/(x₁-x₂)
    let x₃ := m^2-x₁-x₂
    let y₃ := m*(x₁-x₃)-y₁
    D x₃=2*(g₁+g₂)*y₃ ∧ D y₃=(g₁+g₂)*(3*x₃^2+A) := by
  let m := (y₁-y₂)/(x₁-x₂)
  let x₃ := m^2-x₁-x₂
  let y₃ := m*(x₁-x₃)-y₁
  change D x₃=2*(g₁+g₂)*y₃ ∧ D y₃=(g₁+g₂)*(3*x₃^2+A)
  have hd' := sub_ne_zero.mpr hd
  have hline : m*(x₁-x₂)=y₁-y₂ := div_mul_cancel₀ _ hd'
  have hsum : m*(y₁+y₂)=x₁^2+x₁*x₂+x₂^2+A := by
    apply mul_left_cancel₀ hd'
    linear_combination (y₁+y₂)*hline + e₁ - e₂
  have hdiff := congrArg D hline
  rw [D.leibniz, D.map_sub,D.map_sub,smul_eq_mul,smul_eq_mul,hx₁,hx₂,hy₁,hy₂] at hdiff
  have hm : D m=g₁*(x₁-x₃)+g₂*(x₂-x₃) := by
    apply mul_left_cancel₀ hd'
    dsimp only [x₃]
    linear_combination hdiff + (g₁-g₂)*(-(hsum)) +
      (g₁+g₂)*m*hline
  have hx₃ : D x₃=2*(g₁+g₂)*y₃ := by
    dsimp only [x₃,y₃]
    rw [D.map_sub,D.map_sub,D.leibniz_pow,hm,hx₁,hx₂]
    dsimp only [x₃]; simp only [Nat.reduceSub, pow_one,smul_eq_mul,nsmul_eq_mul,Nat.cast_ofNat]
    linear_combination -2*g₂*hline
  refine ⟨hx₃,?_⟩
  change D (m*(x₁-x₃)-y₁) = _
  rw [D.map_sub,D.leibniz,D.map_sub,hx₁,hx₃,hm,hy₁,smul_eq_mul,smul_eq_mul]
  dsimp only [x₃,y₃]
  clear_value m
  grobner

theorem tangent_derivative (D : Derivation ℤ K K) (A x y g : K)
    (hd : 2*y≠0) (hA : D A=0) (hx : D x=2*g*y) (hy : D y=g*(3*x^2+A)) :
    let m := (3*x^2+A)/(2*y)
    let x₃ := m^2-x-x
    let y₃ := m*(x-x₃)-y
    D x₃=2*(g+g)*y₃ ∧ D y₃=(g+g)*(3*x₃^2+A) := by
  let m := (3*x^2+A)/(2*y)
  let x₃ := m^2-x-x
  let y₃ := m*(x-x₃)-y
  change D x₃=2*(g+g)*y₃ ∧ D y₃=(g+g)*(3*x₃^2+A)
  have ht : m*(2*y)=3*x^2+A := div_mul_cancel₀ _ hd
  have ht' := congrArg D ht
  have h2 : D (2:K)=0 := D.map_natCast 2
  have h3 : D (3:K)=0 := D.map_natCast 3
  simp only [D.leibniz,D.map_add,D.leibniz_pow,h2,h3,hA,hx,hy,smul_eq_mul,nsmul_eq_mul,
    Nat.reduceSub,pow_one,Nat.cast_ofNat,mul_zero,add_zero] at ht'
  have hm : D m=2*g*(x-x₃) := by
    apply mul_left_cancel₀ hd
    dsimp only [x₃]
    linear_combination ht' + 2*g*m*ht
  have hx₃ : D x₃=2*(g+g)*y₃ := by
    dsimp only [x₃,y₃]
    rw [D.map_sub,D.map_sub,D.leibniz_pow,hm,hx]
    dsimp only [x₃]; simp only [Nat.reduceSub,pow_one,smul_eq_mul,nsmul_eq_mul,Nat.cast_ofNat]
    ring
  refine ⟨hx₃,?_⟩
  change D (m*(x-x₃)-y) = _
  rw [D.map_sub,D.leibniz,D.map_sub,hx,hx₃,hm,hy,smul_eq_mul,smul_eq_mul]
  dsimp only [x₃,y₃]
  linear_combination 3*g*ht

end SunCoster

end

section

/- # Differential of the CM lattice of points -/

namespace SunCoster
open WeierstrassCurve.Affine
noncomputable section

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

def Velocity (D : Derivation ℤ K K) (a : K) : (shortCurve K).Point → Prop
  | .zero => a=0
  | .some x y _ => D x=2*a*y ∧ D y=a*(3*x^2-35)

theorem Velocity.unique {D : Derivation ℤ K K} {a b : K} {P : (shortCurve K).Point}
    (ha : Velocity D a P) (hb : Velocity D b P) : a=b := by
  cases P with
  | zero => exact ha.trans hb.symm
  | some x y h =>
    have hns := ((shortCurve K).nonsingular_iff' x y).mp h |>.2
    simp [shortCurve] at hns
    obtain ⟨ha₁,ha₂⟩ := ha
    obtain ⟨hb₁,hb₂⟩ := hb
    rcases hns with hg|hg
    · apply mul_right_cancel₀ (b:=3*x^2-35) (by intro hz; apply hg; linear_combination -hz)
      exact ha₂.symm.trans hb₂
    · apply mul_right_cancel₀ (b:=2*y) (by simpa using hg)
      linear_combination -ha₁+hb₁

theorem Velocity.neg {D : Derivation ℤ K K} {a : K} {P : (shortCurve K).Point}
    (ha : Velocity D a P) : Velocity D (-a) (-P) := by
  cases P with
  | zero =>
    rw [← Point.zero_def, neg_zero]
    exact neg_eq_zero.mpr ha
  | some x y h =>
    obtain ⟨hx,hy⟩ := ha
    rw [Point.neg_some]
    simp only [Velocity,negY,shortCurve,zero_mul,sub_zero,map_neg]
    constructor <;> first | linear_combination hx | linear_combination -hy

theorem Velocity.add {D : Derivation ℤ K K} {a b : K} {P Q : (shortCurve K).Point}
    (ha : Velocity D a P) (hb : Velocity D b Q) : Velocity D (a+b) (P+Q) := by
  cases P with
  | zero =>
    have h : a=0 := ha
    simpa [← Point.zero_def,h] using hb
  | some x y h =>
    cases Q with
    | zero =>
      have h : b=0 := hb
      simpa [← Point.zero_def,h] using ha
    | some u v j =>
      have e := short_equation.mp h.1
      have f := short_equation.mp j.1
      by_cases hx : x=u
      · subst u
        by_cases hv : y=(shortCurve K).negY x v
        · have he : Point.some x y h = -(Point.some x v j) := by
            rw [Point.neg_some]; subst y; rfl
          have hcoeff := ha.unique (he ▸ hb.neg)
          rw [Point.add_of_Y_eq rfl hv]
          change a+b=0; rw [hcoeff]; ring
        · have hyv := Y_eq_of_Y_ne h.1 j.1 rfl hv
          subst v
          have hcoeff := ha.unique hb
          subst b
          obtain ⟨hx',hy'⟩ := ha
          rw [Point.add_self_of_Y_ne hv]
          have hh : 2*y≠0 := by
            simp [shortCurve,negY] at hv
            intro hz
            apply hv; linear_combination hz
          have HD : D (-35:K)=0 := by simpa using D.map_intCast (-35)
          have E := tangent_derivative D (-35) x y a hh HD hx' (by simpa [sub_eq_add_neg] using hy')
          simp only [Velocity,addY,negAddY,addX,slope_of_Y_ne (W:=shortCurve K) rfl hv]
          simp only [negY,shortCurve,zero_mul,mul_zero,add_zero,sub_zero,sub_neg_eq_add,← two_mul y]
          dsimp only at E
          convert E using 1 <;> ring_nf
      · rw [Point.add_of_X_ne hx]
        obtain ⟨h₁,h₂⟩ := ha; obtain ⟨h₃,h₄⟩ := hb
        have E := chord_derivative D (-35) 98 x u y v a b
          (by simpa [sub_eq_add_neg] using e) (by simpa [sub_eq_add_neg] using f)
          hx h₁ h₃ (by simpa [sub_eq_add_neg] using h₂) (by simpa [sub_eq_add_neg] using h₄)
        simp only [Velocity,addY,negAddY,addX,slope_of_X_ne hx,negY,shortCurve,
          zero_mul,add_zero,sub_zero]
        dsimp only at E
        convert E using 1 <;> ring_nf

end
end SunCoster

end

section

namespace SunCoster
open WeierstrassCurve.Affine SunSevenIsogeny
noncomputable section

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

theorem Velocity.nsmul {D : Derivation ℤ K K} {a : K} {P : (shortCurve K).Point}
    (h : Velocity D a P) (n : ℕ) : Velocity D ((n : K)*a) (n • P) := by
  induction n with
  | zero => simp [Velocity, Point.zero_def]
  | succ n ih => simpa [succ_nsmul, Nat.cast_succ, add_mul] using ih.add h

theorem Velocity.zsmul {D : Derivation ℤ K K} {a : K} {P : (shortCurve K).Point}
    (h : Velocity D a P) (n : ℤ) : Velocity D ((n : K)*a) (n • P) := by
  cases n with
  | ofNat n => simpa using h.nsmul n
  | negSucc n =>
    rw [negSucc_zsmul]
    convert (h.nsmul (n+1)).neg using 1 <;> push_cast <;> ring

theorem deriv_numeral (D : Derivation ℤ K K) (n : ℕ) [n.AtLeastTwo] :
    D (OfNat.ofNat n : K)=0 := D.map_natCast n

/-- A point on the short model is smooth in characteristic zero. -/
theorem velocity_smooth {x y : K} (h : y^2=x^3-35*x+98) : (shortCurve K).Nonsingular x y := by
  apply ((shortCurve K).nonsingular_iff' x y).mpr
  refine ⟨short_equation.mpr h, ?_⟩
  simp only [shortCurve,zero_mul,mul_zero,add_zero,sub_zero,zero_add]
  by_contra! both
  obtain ⟨hx,hy⟩ := both
  have hy0 : y=0 := by linear_combination hy/2
  rw [hy0] at h
  grobner

/-- The two coordinate identities for the differential of the norm-two CM generator. -/
theorem generator_velocity (D : Derivation ℤ K K) (v x y a : K)
    (hv : v^2=v-2) (hv0 : v≠0) (hd : x≠4-v)
    (he : y^2=x^3-35*x+98) (hx : D x=2*a*y)
    (hy' : phiY v x y ≠ 0) :
    Velocity D (v*a) (.some (phiX v x) (phiY v x y) (velocity_smooth (cm_generator hv hv0 he hd))) := by
  have h2v : 2*v-1 ≠ 0 := by intro eq; grobner
  have vconst : D v=0 := by
    have e := congrArg D hv
    simp only [D.leibniz_pow,D.map_sub,show D (2:K)=0 from D.map_natCast 2,sub_zero,Nat.reduceSub,pow_one,
      smul_eq_mul,nsmul_eq_mul,Nat.cast_ofNat] at e
    apply (mul_eq_zero.mp (show (2*v-1)*D v=0 by linear_combination e)).resolve_left h2v
  let u := 4-v
  let c := 3*u^2-35
  have du : D u=0 := by simp [u,vconst,show D (4:K)=0 from D.map_natCast 4]
  have dc : D c=0 := by simp [c,D.leibniz,D.leibniz_pow,du,show D (3:K)=0 from D.map_natCast 3,
    show D (35:K)=0 from D.map_natCast 35]
  have dv2 : D (v^2)=0 := by simp [D.leibniz_pow,vconst]
  have hf : D (phiX v x)=2*(v*a)*phiY v x y := by
    change D ((x+c/(x-u))/v^2)=2*(v*a)*(y*(1-c/(x-u)^2)/v^3)
    rw [D.leibniz_div_const _ _ dv2,D.map_add,D.leibniz_div,dc,D.map_sub x u,du,hx]
    simp only [smul_eq_mul,sub_zero,mul_zero,zero_sub]
    field_simp [hv0,sub_ne_zero.mpr (show x≠u from hd)]
    <;> ring
  refine ⟨hf,?_⟩
  have ec : (phiY v x y)^2=(phiX v x)^3-35*(phiX v x)+98 := cm_generator hv hv0 he hd
  have diff := congrArg D ec
  simp only [D.leibniz_pow,D.map_add,D.map_sub,D.leibniz,show D (35:K)=0 from D.map_natCast 35,
    show D (98:K)=0 from D.map_natCast 98,add_zero,
    Nat.reduceSub,pow_one,smul_eq_mul,nsmul_eq_mul,Nat.cast_ofNat,hf,mul_zero] at diff
  apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (2:K)≠0) hy')
  linear_combination diff

/-- The multiplier of [m+n]P−[2n]φ(P) is m−n√−7 for the branch 2v−1=√−7. -/
theorem cm_lattice_multiplier {D : Derivation ℤ K K} (m n : ℤ) {v : K}
    {P G : (shortCurve K).Point} (hP : Velocity D 1 P) (hG : Velocity D v G) :
    Velocity D ((m:K)-(n:K)*(2*v-1)) ((m+n) • P - (2*n) • G) := by
  have h := (hP.zsmul (m+n)).add ((hG.zsmul (2*n)).neg)
  rw [sub_eq_add_neg (b := (2*n) • G)]
  convert h using 1 <;> push_cast <;> ring

/-- The normalized square root of the quartic in the parameter t=(x+7)/y. -/
def quarticRoot (x y : K) : K := ((x+7)^3-112*(x+7))/y^2

theorem short_quartic (x y : K) (he : y^2=x^3-35*x+98) (hy : y≠0) :
    (quarticRoot x y)^2=1+42*((x+7)/y)^2-7*((x+7)/y)^4 := by
  unfold quarticRoot
  field_simp
  ring_nf
  linear_combination (norm := ring) -(y^2 + x^3 + 42*x^2 + 553*x + 2156)*he

theorem short_parameter_derivative (D : Derivation ℤ K K) {x y a : K}
    (he : y^2=x^3-35*x+98) (hy : y≠0) (hx : D x=2*a*y) (hyd : D y=a*(3*x^2-35)) :
    D ((x+7)/y) = -a*quarticRoot x y := by
  rw [D.leibniz_div,D.map_add,deriv_numeral,add_zero,hx,hyd]
  simp only [quarticRoot,smul_eq_mul]
  field_simp
  linear_combination 2*a*he

end
end SunCoster

end

section

namespace SunCoster
open Polynomial
noncomputable section

variable {K L : Type*} [Field K] [Field L] [CharZero L]

theorem deriv_eval_of_constants (D : Derivation ℤ L L) (ι : K →+* L)
    (hc : ∀ k, D (ι k)=0) (t : L) (P : K[X]) :
    D (P.eval₂ ι t)=P.derivative.eval₂ ι t*D t := by
  induction P using Polynomial.induction_on' with
  | add a b ha hb =>
    simp only [derivative_add,eval₂_add,D.map_add,ha,hb,add_mul]
  | monomial n a =>
    simp only [derivative_monomial,eval₂_monomial,D.leibniz,D.leibniz_pow,hc,
      smul_eq_mul,nsmul_eq_mul,map_mul,map_natCast,mul_zero,add_zero]
    ring

/-- Descending the same generic point to a rational function of the local
parameter gives the homogeneous differential equation on its reduced fraction. -/
theorem wronskian_from_coordinates (D : Derivation ℤ L L) (ι : K →+* L)
    (hc : ∀ k, D (ι k)=0) (π : K) {x y u v : L} (hy : y≠0) (hv : v≠0)
    (hxy : y^2=x^3-35*x+98) (huv : v^2=u^3-35*u+98)
    (hx : D x=2*y) (hY : D y=3*x^2-35)
    (hu : D u=2*(ι π)*v) (hV : D v=ι π*(3*u^2-35)) (N B : K[X])
    (H : let t := (x+7)/y
      N.eval₂ ι t = ((u+7)/v)*B.eval₂ ι t)
    (hi : Function.Injective (eval₂RingHom ι ((x+7)/y))) :
    (1+42*X^2-7*X^4)*(N.derivative*B-N*B.derivative)^2 =
      C π^2*(B^4+42*N^2*B^2-7*N^4) := by
  classical
  let t := (x+7)/y
  let q := (u+7)/v
  let a := quarticRoot x y
  let b := quarticRoot u v
  let e := eval₂RingHom ι t
  have dt : D t= -a := by
    simpa [a,t] using short_parameter_derivative D (a:=1) hxy hy (by simpa using hx) (by simpa using hY)
  have dq : D q= -(ι π)*b := short_parameter_derivative D huv hv hu hV
  have Ha : a^2=1+42*t^2-7*t^4 := short_quartic x y hxy hy
  have Hb : b^2=1+42*q^2-7*q^4 := short_quartic u v huv hv
  change e N=q*e B at H
  have de (P : K[X]) : D (e P)=e P.derivative*D t := deriv_eval_of_constants D ι hc t P
  have Hd := congrArg D H
  rw [de,D.leibniz,de,dt,dq] at Hd
  simp only [smul_eq_mul] at Hd
  let W := e N.derivative*e B-e N*e B.derivative
  have diff : a*W=ι π*b*(e B)^2 := by
    dsimp only [W]
    linear_combination -(e B)*Hd - a*(e B.derivative)*H
  apply hi
  change e _=e _
  simp only [map_mul,map_add,map_sub,map_pow,map_one,map_ofNat,show e (C π)=ι π from eval₂_C ..]
  change (1+42*e X^2-7*e X^4)*W^2=ι π^2*((e B)^4+42*(e N)^2*(e B)^2-7*(e N)^4)
  have ex : e X=t := eval₂_X _ _
  rw [ex,←Ha,←mul_pow,diff,H,mul_pow,mul_pow,Hb]
  ring

end
end SunCoster

end

section

namespace SunCoster.Reciprocity
open Polynomial
noncomputable section
variable {K : Type*} [Field K]

/-- Homogenized numerator or denominator after substituting c/T. -/
def reciprocal (c : K) (d : ℕ) (P : K[X]) : K[X] := reflect d (P.comp (C c*X))

theorem coeff (c : K) (d i : ℕ) (hi : i≤d) (P : K[X]) :
    (reciprocal c d P).coeff i=P.coeff (d-i)*c^(d-i) := by
  simp [reciprocal,coeff_reflect,revAt_le hi]

private theorem scaled_degree (c : K) (P : K[X]) : (P.comp (C c*X)).natDegree≤P.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [comp_C_mul_X_coeff,coeff_eq_zero_of_natDegree_lt hn,zero_mul]

theorem degree_le (c : K) {d : ℕ} (P : K[X]) (h : P.natDegree≤d) :
    (reciprocal c d P).natDegree≤d :=
  natDegree_reflect_le.trans (max_le le_rfl ((scaled_degree c P).trans h))

theorem eval_reciprocal (c : K) {d : ℕ} (P : K[X]) (h : P.natDegree≤d) :
    aeval (RatFunc.X : RatFunc K) (reciprocal c d P) =
      RatFunc.X^d * aeval (RatFunc.C c/RatFunc.X) P := by
  let t := (RatFunc.X : RatFunc K)
  have ht : t≠0 := RatFunc.X_ne_zero
  letI := invertibleOfNonzero (inv_ne_zero ht)
  have e := eval₂_reflect_mul_pow (algebraMap K (RatFunc K)) t⁻¹ d (P.comp (C c*X)) ((scaled_degree c P).trans h)
  rw [invOf_eq_inv,inv_inv,eval₂_comp',eval₂_mul,eval₂_C,eval₂_X] at e
  change _ * _ = P.eval₂ _ (RatFunc.C c*t⁻¹) at e
  change (reciprocal c d P).eval₂ (algebraMap K (RatFunc K)) t =
    t^d * P.eval₂ (algebraMap K (RatFunc K)) (RatFunc.C c/t)
  rw [div_eq_mul_inv,← e,inv_pow]
  field_simp
  rfl

/-- Commutation with the reciprocal translation, written without fractions. -/
theorem polynomial_identity (c : K) {d : ℕ} (N D : K[X]) (hn : N.natDegree≤d) (hd : D.natDegree≤d)
    (h : let t := (RatFunc.X : RatFunc K)
      aeval t N * aeval (RatFunc.C c/t) N = RatFunc.C c * aeval t D * aeval (RatFunc.C c/t) D) :
    N*reciprocal c d N = C c*D*reciprocal c d D := by
  apply (transcendental_iff_injective.mp (RatFunc.transcendental_X (K:=K)))
  simp only [map_mul,aeval_C,eval_reciprocal _ _ hn,eval_reciprocal _ _ hd]
  change _ = RatFunc.C c * _ * _
  linear_combination RatFunc.X^d * h

/-- Coprimality makes the numerator and reversed denominator proportional. The
endpoint coefficients give the exact square of their ratio over the field. -/
theorem endpoints (c : K) (hc : c≠0) (d : ℕ) (N D : K[X])
    (hn : N.natDegree=d) (hd : D.natDegree≤d) (hN : N≠0) (hD : D.coeff 0≠0)
    (cop : IsCoprime N D)
    (h : N*reciprocal c d N = C c*D*reciprocal c d D) :
    ∃ k : K, k≠0 ∧ reciprocal c d D=C k*N ∧ reciprocal c d N=C (c*k)*D ∧
      (N.coeff d/D.coeff 0)^2 * c^d = c := by
  let S := reciprocal c d D
  have edge : S.coeff d=D.coeff 0 := by simp [S,coeff c d d le_rfl]
  have hs : S ≠ 0 := by intro e; rw [e,coeff_zero] at edge; exact hD edge.symm
  have divN : N ∣ D*S := by
    refine ⟨C c⁻¹*reciprocal c d N,?_⟩
    have w : C c⁻¹*C c=(1:K[X]) := by rw [← map_mul,inv_mul_cancel₀ hc,map_one]
    dsimp only [S]
    linear_combination -(C c⁻¹)*h - D*(reciprocal c d D)*w
  obtain ⟨T,hT⟩ := cop.dvd_of_dvd_mul_left divN
  have ht : T≠0 := by intro e; simp [e] at hT; exact hs hT
  have degS := degree_le c D hd
  change S.natDegree≤d at degS
  rw [hT,natDegree_mul hN ht,hn] at degS
  have tz := eq_C_of_natDegree_eq_zero (show T.natDegree=0 by omega)
  let k := T.coeff 0
  have hk : k≠0 := by intro e; exact ht (tz.trans (by change C k=0; simp [e]))
  have rD : S=C k*N := hT.trans (by rw [tz]; exact mul_comm ..)
  have rN : reciprocal c d N=C (c*k)*D := by
    apply mul_left_cancel₀ hN
    change N*reciprocal c d N=C c*D*S at h
    rw [h,rD,map_mul]; ring
  have e1 := congrArg (fun H : K[X] => H.coeff d) rD
  change S.coeff d=(C k*N).coeff d at e1
  rw [edge,coeff_C_mul] at e1
  have e2 := congrArg (fun H : K[X] => H.coeff 0) rN
  change (reciprocal c d N).coeff 0=(C (c*k)*D).coeff 0 at e2
  rw [coeff c d 0 (Nat.zero_le d),Nat.sub_zero,coeff_C_mul] at e2
  refine ⟨k,hk,rD,rN,?_⟩
  field_simp [hD]
  linear_combination N.coeff d*e2 - c*D.coeff 0*e1

end
end SunCoster.Reciprocity

end

section

namespace SunCoster.Reciprocity
open Polynomial
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

def oddFraction (N D : K[X]) : Prop := N.comp (-X)*D= -(N*D.comp (-X))

def reciprocalFraction (c : K) (N D : K[X]) : Prop :=
  let t := (RatFunc.X : RatFunc K)
  aeval t N * aeval (RatFunc.C c/t) N = RatFunc.C c * aeval t D * aeval (RatFunc.C c/t) D

def quarticEquation (π : K) (N D : K[X]) : Prop :=
  (1+42*X^2-7*X^4)*(N.derivative*D-N*D.derivative)^2 =
    C π^2*(D^4+42*N^2*D^2-7*N^4)

private theorem swap_coprime (c : K) (hc : c≠0) {N D : K[X]} (h : IsCoprime N D) :
    IsCoprime (C c*D) N := by
  obtain ⟨a,b,e⟩ := h
  refine ⟨b*C c⁻¹,a,?_⟩
  have inv : C c⁻¹*C c=(1:K[X]) := by rw [←map_mul,inv_mul_cancel₀ hc,map_one]
  linear_combination e + b*D*inv

private theorem swap_odd (c : K) {N D : K[X]} (h : oddFraction N D) :
    oddFraction (C c*D) N := by
  unfold oddFraction at *
  rw [mul_comp,C_comp]
  linear_combination C c*h

private theorem swap_reciprocal (c : K) {N D : K[X]} (h : reciprocalFraction c N D) :
    reciprocalFraction c (C c*D) N := by
  unfold reciprocalFraction at *
  dsimp only at *
  simp only [map_mul,aeval_C]
  change RatFunc.C c*_*(RatFunc.C c*_)=RatFunc.C c*_*_
  linear_combination -(RatFunc.C c)*h

private theorem swap_quartic (c π : K) (hc : -7*c^2=1) {N D : K[X]} (h : quarticEquation π N D) :
    quarticEquation π (C c*D) N := by
  unfold quarticEquation at *
  rw [derivative_C_mul]
  have e : -(7:K[X])*C c^2=1 := by simpa only [map_mul,map_neg,map_ofNat,map_pow,map_one] using congrArg C hc
  linear_combination (C c)^2*h + (C π)^2*(N^4-C c^2*D^4)*e

theorem ordered_presentation (c π : K) (hc : c≠0) (hcq : -7*c^2=1) (d : ℕ) (hd : 0<d)
    (N D : K[X]) (cop : IsCoprime N D) (deg : max N.natDegree D.natDegree=d)
    (odd : oddFraction N D) (recip : reciprocalFraction c N D) (eq : quarticEquation π N D) :
    ∃ A B : K[X], IsCoprime A B ∧ A.natDegree=d ∧ B.natDegree<d ∧
      A.coeff 0=0 ∧ B.coeff 0≠0 ∧ oddFraction A B ∧ reciprocalFraction c A B ∧ quarticEquation π A B := by
  have order (a b : K[X]) (h : max a.natDegree b.natDegree=d)
      (o : oddFraction a b) (r : reciprocalFraction c a b) (hb : b.coeff 0≠0) :
      a.natDegree=d ∧ b.natDegree<d ∧ a.coeff 0=0 := by
    have e := congrArg (fun f : K[X] => f.eval 0) o
    change ((a.comp (-X))*b).eval 0 = (-(a*(b.comp (-X)))).eval 0 at e
    simp only [eval_mul,eval_comp,eval_neg,eval_X,neg_zero,← coeff_zero_eq_eval_zero] at e
    have ha : a.coeff 0=0 := by
      apply (mul_eq_zero.mp (show a.coeff 0*b.coeff 0=0 by linear_combination e/2)).resolve_right hb
    have H := polynomial_identity c (d:=d) a b (by omega) (by omega) r
    have E := congrArg (fun f : K[X] => f.eval 0) H
    simp only [eval_mul,eval_C,←coeff_zero_eq_eval_zero,coeff c d 0 (Nat.zero_le d),
      Nat.sub_zero,ha,zero_mul] at E
    have vanish : b.coeff d=0 := by
      by_contra hn
      exact (mul_ne_zero (mul_ne_zero hc hb) (mul_ne_zero hn (pow_ne_zero _ hc))) E.symm
    have blt : b.natDegree<d := by
      by_contra! hh
      have eqd : b.natDegree=d := by omega
      rw [←eqd,coeff_natDegree] at vanish
      exact hb (by simp [leadingCoeff_eq_zero.mp vanish])
    exact ⟨by omega,blt,ha⟩
  by_cases hD : D.coeff 0=0
  · obtain ⟨i,j,bez⟩ := cop
    have hN : N.coeff 0≠0 := by
      intro z
      have e := congrArg (fun f : K[X] => f.eval 0) bez
      simp [←coeff_zero_eq_eval_zero,z,hD] at e
    have q := swap_quartic c π hcq eq
    have o := swap_odd c odd
    have r := swap_reciprocal c recip
    have e : max (C c*D).natDegree N.natDegree=d := by rw [natDegree_C_mul hc,max_comm]; exact deg
    obtain ⟨hn,hb,h₀⟩ := order (C c*D) N e o r hN
    exact ⟨_,_,swap_coprime c hc ⟨i,j,bez⟩,hn,hb,h₀,hN,o,r,q⟩
  · obtain ⟨hn,hb,h₀⟩ := order N D deg odd recip hD
    exact ⟨_,_,cop,hn,hb,h₀,hD,odd,recip,eq⟩

end
end SunCoster.Reciprocity

end

section

namespace SunCoster
open Polynomial SunDescent
noncomputable section
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

def ratEval (t : L) (ht : Transcendental K t) : RatFunc K →ₐ[K] L :=
  (IntermediateField.adjoin K {t}).val.comp (RatFunc.algEquivOfTranscendental t ht).toAlgHom

@[simp] theorem ratEval_X (t : L) (ht : Transcendental K t) : ratEval t ht RatFunc.X=t :=
  RatFunc.algEquivOfTranscendental_X t ht

theorem ratEval_poly (t : L) (ht : Transcendental K t) (P : K[X]) :
    ratEval t ht (algebraMap K[X] (RatFunc K) P)=aeval t P := by
  rw [←RatFunc.aeval_X_left_eq_algebraMap,←aeval_algHom_apply,ratEval_X]

theorem ratEval_num (t : L) (ht : Transcendental K t) (F : RatFunc K) :
    aeval t F.num=ratEval t ht F*aeval t F.denom := by
  rw [←ratEval_poly t ht,←ratEval_poly t ht,←map_mul]
  apply congrArg
  exact ((div_eq_iff (RatFunc.algebraMap_ne_zero F.denom_ne_zero)).mp (RatFunc.num_div_denom F))

theorem ratHom_ext (f g : RatFunc K →ₐ[K] L) (h : f RatFunc.X=g RatFunc.X) : f=g := by
  ext1 u
  induction u using RatFunc.induction_on with
  | f a b hb =>
    simp only [map_div₀,←RatFunc.aeval_X_left_eq_algebraMap,←aeval_algHom_apply,h]

theorem ratEval_comp (g : RatFunc K →ₐ[K] L) (t : RatFunc K) (ht : Transcendental K t)
    (w : L) (hw : Transcendental K w) (eq : g t=w) :
    g.comp (subst t ht)=ratEval w hw := by
  apply ratHom_ext
  simpa [eq]

def oddMap (q : RatFunc K) : RatFunc K :=
  RatFunc.X * subst ((RatFunc.X : RatFunc K)^2)
    (transcendental_of_deg (by rw [square_degree]; decide)) q

/-- A degree calculation in a translated chart is valid for any nonconstant
rational coordinate H of degree two. -/
theorem oddMap_degree (q R H : RatFunc K) (rh : Transcendental K R) (hh : deg H=2)
    (intertwine : subst R rh H = subst H (transcendental_of_deg (by omega)) (RatFunc.X*q^2)) :
    deg (oddMap q)=deg R := by
  let j := subst ((RatFunc.X : RatFunc K)^2) (transcendental_of_deg (by rw [square_degree]; decide))
  have e : j (RatFunc.X*q^2)=(oddMap q)^2 := by simp [oddMap,j,mul_pow]
  have E := congrArg deg intertwine
  rw [degree_substitution (subst R rh) H,degree_substitution (subst H _) (RatFunc.X*q^2)] at E
  simp only [subst_X,hh] at E
  have S := degree_substitution j (RatFunc.X*q^2)
  rw [e,deg_square,show deg (j RatFunc.X)=2 by simp [j,square_degree]] at S
  omega

theorem transcendental_square_chart (ι : RatFunc K →ₐ[K] L) (H : RatFunc K) (t : L)
    (hH : deg H=2) (h : t^2=ι H) : Transcendental K t := by
  have ht : Transcendental K H := transcendental_of_deg (by omega)
  intro a
  exact ht ((isAlgebraic_algHom_iff ι ι.injective).mp (h ▸ a.pow 2))

end
end SunCoster

end

section

namespace SunCoster.ChartAction
open SunSevenIsogeny WeierstrassCurve.Affine SunDescent Polynomial
noncomputable section
variable (K : Type*) [Field K] [CharZero K]

local instance deckAlgebra : Algebra K (DeckField K) := ((incl K).comp RatFunc.C).toAlgebra

def deckIncl : RatFunc K →ₐ[K] DeckField K where
  toRingHom := incl K
  commutes' _ := rfl

private theorem chart_image {L : Type*} [Field L] [Algebra K L] (j : RatFunc K →ₐ[K] L) :
    j (tauChart K) = (j RatFunc.X+7)/((j RatFunc.X+7)^2-21*(j RatFunc.X+7)+112) := by
  simp only [tauChart,translatedChart,chart,shiftX,map_div₀,map_add,map_mul,map_pow,map_neg,map_ofNat,neg_neg]
  ring

private theorem parameter_square {L : Type*} [Field L] {a b : L} (E : b^2=a^3-35*a+98) (hb : b≠0) :
    ((a+7)/b)^2=(a+7)/((a+7)^2-21*(a+7)+112) := by
  have h : b^2=(a+7)*((a+7)^2-21*(a+7)+112) := by linear_combination E
  have hd : (a+7)^2-21*(a+7)+112≠0 := by intro z; exact pow_ne_zero 2 hb (by rw [h,z,mul_zero])
  rw [div_pow,div_eq_div_iff (pow_ne_zero 2 hb) hd]
  linear_combination -(a+7)*h

private theorem generic_ordinate (j : RatFunc K →+* DeckField K) (R : RatFunc K) (hR : Transcendental K R)
    {y : DeckField K} (hy : y^2=(j R)^3-35*j R+98) : y≠0 := by
  intro z
  have h0 : R^3-35*R+98=0 := j.injective (by
    simp only [map_add,map_sub,map_mul,map_pow,map_ofNat,map_zero]
    rw [←hy,z,zero_pow (by decide : 2≠0)])
  apply hR
  refine ⟨X^3-35*X+98,?_,?_⟩
  · have hd : (X^3-35*X+98 : K[X]).natDegree=3 := by compute_degree <;> norm_num
    intro h; simp [h] at hd
  · simpa only [map_add,map_sub,map_mul,map_pow,map_ofNat,aeval_X] using h0

private theorem affine_coordinates_of_degree [DecidableEq (DeckField K)] (U : (shortCurve (DeckField K)).Point)
    (R : RatFunc K) (er : incl K R=U.xRep 0) (tr : Transcendental K R) :
    ∃ (b : DeckField K) (e : (shortCurve _).Nonsingular (incl K R) b), U=Point.some _ b e ∧ b≠0 := by
  cases U with
  | zero =>
    have e : R=1 := (incl K).injective (by rw [map_one]; exact er)
    exact (tr (e ▸ isAlgebraic_one)).elim
  | some a b h =>
    have ea : incl K R=a := er
    subst a
    exact ⟨b,h,rfl,generic_ordinate K (incl K) R tr (short_equation.mp h.1)⟩

/-- The Coster parameters of the generic point and the CM lattice point are
related by an odd rational map of the exact norm degree. The ordinate of
the image point and both nonvanishing assertions are supplied as well. -/
theorem geometric_chart_map [DecidableEq (DeckField K)] (v : K) (hv : v^2=v-2) (Y : DeckField K)
    (hP : (shortCurve _).Nonsingular (incl K RatFunc.X) Y)
    (hV : (shortCurve _).Nonsingular (phiX (incl K (RatFunc.C v)) (incl K RatFunc.X))
      (phiY (incl K (RatFunc.C v)) (incl K RatFunc.X) Y))
    (m n : ℤ) (hm : Odd m)
    (U : (shortCurve (DeckField K)).Point) (eU : U=m•Point.some _ _ hP+(2*n)•Point.some _ _ hV)
    (hU : rationalCoordinates (incl K) Y U) (R : RatFunc K) (er : incl K R=U.xRep 0)
    (p : ℕ) (hp : 0<p) (hdeg : deg R=p) :
    let t := param (Point.some _ _ hP)
    ∃ (ht : Transcendental K t) (q : RatFunc K) (b : DeckField K)
      (e : (shortCurve _).Nonsingular (incl K R) b),
      U=Point.some _ b e ∧ Y≠0 ∧ b≠0 ∧ t≠0 ∧ param U≠0 ∧
      deg (oddMap q)=p ∧ ratEval t ht (oddMap q)=param U := by
  let j := deckIncl K
  let t := param (Point.some _ _ hP)
  let w := param U
  let H := tauChart K
  have hH : deg H=2 := tauChart_degree K
  have hHt : Transcendental K H := transcendental_of_deg (by omega)
  have tr : Transcendental K R := transcendental_of_deg (by omega)
  have hY := generic_ordinate K (incl K) RatFunc.X RatFunc.transcendental_X (short_equation.mp hP.1)
  obtain ⟨b,e,eb,hb⟩ := affine_coordinates_of_degree K U R er tr
  have t2 : t^2=j H := (parameter_square (short_equation.mp hP.1) hY).trans (chart_image K j).symm
  have ht := transcendental_square_chart j H t hH t2
  have t0 : t≠0 := fun h => ht (h ▸ isAlgebraic_zero)
  let s := subst R tr
  have w2 : w^2=j (s H) := by
    rw [show w=(incl K R+7)/b by dsimp only [w]; rw [eb]; rfl,parameter_square (short_equation.mp e.1) hb]
    symm
    change (j.comp s) H=_
    change j (s (tauChart K))=(j R+7)/((j R+7)^2-21*(j R+7)+112)
    simpa only [AlgHom.comp_apply,show s RatFunc.X=R from subst_X ..] using chart_image K (j.comp s)
  have w0 : w≠0 := by
    intro z
    have e0 : j (s H)=0 := by rw [←w2,z,zero_pow (by decide : 2≠0)]
    have es : s H=0 := j.injective (show j (s H)=j 0 from e0.trans (map_zero j).symm)
    have ez : H=0 := s.injective (show s H=s 0 from es.trans (map_zero s).symm)
    exact hHt (ez ▸ isAlgebraic_zero)
  have qdesc := chart_ratio_descends K v hv Y hP hV m n hm (eU ▸ hU)
  rw [←eU] at qdesc
  obtain ⟨q,hq⟩ := qdesc
  let i := subst H hHt
  have ratio : j (i q)=w/t := hq
  have intertwine : s H=i (RatFunc.X*q^2) := j.injective (by
    change j (s H)=j (i (RatFunc.X*q^2))
    rw [map_mul i,map_pow i,map_mul j,map_pow j,show i RatFunc.X=H from subst_X ..,←w2,←t2,ratio]
    field_simp [t0])
  have degq := oddMap_degree q R H tr hH intertwine
  let k := subst ((RatFunc.X : RatFunc K)^2) (transcendental_of_deg (by rw [square_degree]; decide))
  have eqm : (ratEval t ht).comp k=j.comp i := by
    apply ratHom_ext
    simp only [AlgHom.comp_apply,show k RatFunc.X=(RatFunc.X:RatFunc K)^2 from subst_X ..,
      show i RatFunc.X=H from subst_X ..,map_pow,ratEval_X,t2]
  have ev : ratEval t ht (oddMap q)=w := by
    change ratEval t ht (RatFunc.X*k q)=_
    have eq := DFunLike.congr_fun eqm q
    change ratEval t ht (k q)=j (i q) at eq
    rw [map_mul,ratEval_X,eq,ratio,mul_div_cancel₀ _ t0]
  exact ⟨ht,q,b,e,eb,hY,hb,t0,w0,degq.trans hdeg,ev⟩

end
end SunCoster.ChartAction

end

section

namespace SunCoster
open Polynomial WeierstrassCurve.Affine SunDescent
noncomputable section
variable {K L : Type*} [Field K] [CharZero K] [Field L]

def doubleX (u : RatFunc K) : RatFunc K :=
  (u^4+70*u^2-784*u+1225)/(4*(u^3-35*u+98))

theorem doubleX_degree : deg (doubleX (RatFunc.X : RatFunc K)) = 4 := by
  let F : K[X] := X^4+70*X^2-784*X+1225
  let H : K[X] := 4*(X^3-35*X+98)
  have fdeg : F.natDegree=4 := by dsimp only [F]; compute_degree <;> norm_num
  have hdeg : H.natDegree=3 := by dsimp only [H]; compute_degree <;> norm_num
  have hF : F≠0 := by rintro h; simp [h] at fdeg
  have hH : H≠0 := by rintro h; simp [h] at hdeg
  have bezout : ((12:K[X])*X^2-560)*F + (-3*X^3-175*X+2646)*H = 351232 := by
    dsimp only [F,H]; ring
  have cop : IsCoprime F H := by
    let u := C ((351232:K)⁻¹)
    refine ⟨u*(12*X^2-560),u*(-3*X^3-175*X+2646),?_⟩
    rw [mul_assoc,mul_assoc,←mul_add,bezout]
    change C ((351232:K)⁻¹) * 351232 = 1
    rw [←map_ofNat C 351232, ←map_mul, inv_mul_cancel₀ (by norm_num), map_one]
  have eq : doubleX (RatFunc.X : RatFunc K) = fraction F H := by
    simp [doubleX,fraction,F,H,RatFunc.algebraMap_X,map_ofNat]
  rw [eq,deg_fraction _ _ hF hH cop,fdeg,hdeg]; decide

theorem short_double_exact [DecidableEq L] (ι : RatFunc K →+* L) (P : (shortCurve L).Point)
    (u r : RatFunc K) (hu : ι u=P.xRep 0) (hr : ι r=(P+P).xRep 0) :
    height r = 4*height u := by
  by_cases h : height u=0
  · have H := short_double ι P u r hu hr
    omega
  have tu := SunDescent.transcendental_of_deg (f:=u) (Nat.pos_of_ne_zero h)
  let φ := SunDescent.subst u tu
  have ex : φ (doubleX RatFunc.X) = doubleX u := by simp [φ,doubleX,map_ofNat]
  have d := SunDescent.degree_substitution φ (doubleX RatFunc.X)
  rw [ex, doubleX_degree, show φ RatFunc.X=u from subst_X ..] at d
  have gu : 4*(u^3-35*u+98)≠0 := by
    have q : (4*(Polynomial.X^3-35*Polynomial.X+98) : K[X]).natDegree=3 := by
      compute_degree <;> norm_num
    intro bad
    apply tu
    refine ⟨4*(Polynomial.X^3-35*Polynomial.X+98),?_,?_⟩
    · intro z; simp [z] at q
    · simpa only [map_mul,map_sub,map_add,map_pow,map_ofNat,aeval_X] using bad
  have eq : r=doubleX u := by
    cases P with
    | zero =>
      have z : u=1 := ι.injective (by simpa only [map_one,←Point.zero_def,Point.xRep_zero,Matrix.cons_val_zero] using hu)
      simp [z,height] at h
    | some x y hp =>
      have exu : ι u=x := by simpa only [Point.xRep_some,Matrix.cons_val_zero] using hu
      have hv : 4*(x^3-35*x+98)≠0 := by
        have hι := (map_ne_zero ι).2 gu
        simpa only [map_mul,map_add,map_sub,map_pow,map_ofNat,exu] using hι
      have hy : 2*y≠0 := by
        rw [←short_equation.mp hp.1] at hv
        intro z
        apply hv; linear_combination 2*y*z
      apply (eq_div_iff gu).2
      apply ι.injective
      simp only [map_mul,map_add,map_sub,map_pow,map_ofNat,exu,hr]
      exact short_xRep_double hp hy
  exact eq ▸ d

/-- Degree is an exact quadratic function on every subgroup with rational
abscissas. Equality follows by applying the upper parallelogram inequality
again at the sum and difference and using exact duplication. -/
theorem short_parallelogram_exact {G : Type*} [AddCommGroup G] [DecidableEq L]
    (ι : RatFunc K →+* L) (j : G →+ (shortCurve L).Point)
    (u : G → RatFunc K) (hu : ∀ P, ι (u P) = (j P).xRep 0) (P Q : G) :
    height (u (P+Q))+height (u (P-Q))=2*(height (u P)+height (u Q)) := by
  have upper (A B : G) := short_parallelogram ι (j A) (j B) (u A) (u B) (u (A+B)) (u (A-B))
    (hu A) (hu B) (by rw [hu,map_add]) (by rw [hu,map_sub])
  have dbl (A : G) := short_double_exact ι (j A) (u A) (u (A+A)) (hu A) (by rw [hu,map_add])
  have low := upper (P+Q) (P-Q)
  rw [show P+Q+(P-Q)=P+P by abel, show P+Q-(P-Q)=Q+Q by abel, dbl P,dbl Q] at low
  have up := upper P Q
  omega

end
end SunCoster

end

section

namespace SunCoster
section
variable {G : Type*} [AddCommGroup G]

/-- A function of an integer with zero second differences is affine. -/
private theorem zero_of_second_difference (f : ℤ → ℤ) (h0 : f 0=0) (h1 : f 1=0)
    (hrec : ∀ k, f (k+1)+f (k-1)=2*f k) (n : ℤ) : f n=0 := by
  suffices h : f n=0 ∧ f (n+1)=0 from h.1
  induction n using Int.inductionOn' (b:=0) with
  | zero => exact ⟨h0,h1⟩
  | succ i _ ih =>
    refine ⟨ih.2,?_⟩
    have h := hrec (i+1)
    rw [show i+1-1=i by omega,ih.1,ih.2] at h
    omega
  | pred i _ ih =>
    have h := hrec i
    rw [ih.1,ih.2] at h
    exact ⟨by omega,by simpa using ih.1⟩

theorem degree_on_line (q : G → ℤ)
    (para : ∀ a b, q (a+b)+q (a-b)=2*(q a+q b)) (A B : G) (n : ℤ) :
    q (A+n•B) = q A + n*(q (A+B)-q A-q B) + n^2*q B := by
  let f (i : ℤ) := q (A+i•B) - (q A + i*(q (A+B)-q A-q B) + i^2*q B)
  have hrec (i : ℤ) : f (i+1)+f (i-1)=2*f i := by
    dsimp only [f]
    have H := para (A+i•B) B
    rw [show A+(i+1)•B=A+i•B+B by rw [add_zsmul,one_zsmul,add_assoc],
      show A+(i-1)•B=A+i•B-B by rw [sub_zsmul,one_zsmul,add_sub_assoc,sub_eq_add_neg]]
    linear_combination H
  have H := zero_of_second_difference f (by simp [f]) (by simp [f]; ring) hrec n
  exact sub_eq_zero.mp H

/-- The degree form of the discriminant −7 lattice in the basis formed by the
identity and the degree-two CM generator, using the trace-one relation. -/
theorem cm_lattice_norm (q : G → ℤ) (q0 : q 0=0)
    (para : ∀ a b, q (a+b)+q (a-b)=2*(q a+q b))
    (P V : G) (id_deg : q P=1) (cm_deg : q V=2) (conj_deg : q (P-V)=2)
    (x y : ℤ) :
    q ((x-y)•P + (2*y)•V)=x^2+7*y^2 := by
  have hsum : q (P+V)=4 := by have h := para P V; omega
  have e₀ := degree_on_line q para 0 P (x-y)
  simp only [zero_add,q0,id_deg] at e₀
  have e₁ := degree_on_line q para V P (x-y)
  rw [add_comm V P,hsum,cm_deg,id_deg,add_comm V] at e₁
  have e₂ := degree_on_line q para ((x-y)•P) V (2*y)
  rw [e₀,e₁,cm_deg] at e₂
  linear_combination e₂

end
end SunCoster

end

section

namespace SunCoster
open Polynomial SunDescent SunSevenIsogeny WeierstrassCurve.Affine
noncomputable section

variable {K L : Type*} [Field K] [CharZero K] [Field L] [CharZero L] [DecidableEq L]

/-- For the generic point P and the explicit degree-two generator V over
the discriminant −7 curve, the abscissa of (x−y)P+2yV is rational of
exact degree x²+7y². -/
theorem generic_cm_norm (ι : RatFunc K →+* L) (v : K) (hv : v^2=v-2)
    (Y : L) (hY : Y^2=(ι RatFunc.X)^3-35*(ι RatFunc.X)+98) (x y : ℤ) :
    let t := ι RatFunc.X
    let z := ι (RatFunc.C v)
    ∃ (P V : (shortCurve L).Point) (R : RatFunc K),
      (∃ h, P=Point.some t Y h) ∧
      (∃ h, V=Point.some (phiX z t) (phiY z t Y) h) ∧
      ι R=((x-y)•P+(2*y)•V).xRep 0 ∧ (height R : ℤ)=x^2+7*y^2 ∧
      rationalCoordinates ι Y ((x-y)•P+(2*y)•V) := by
  let t := ι RatFunc.X
  let z := ι (RatFunc.C v)
  let w : RatFunc K := RatFunc.X^3-35*RatFunc.X+98
  have hw : ι w=Y^2 := by simp only [w,map_add,map_sub,map_pow,map_mul,map_ofNat,hY]
  let G := rationalSubgroup ι Y w hw
  have hv' : z^2=z-2 := by simpa [z,map_ofNat] using congrArg (fun k : K => ι (RatFunc.C k)) hv
  have hv0 : z≠0 := by rintro h; simp [h] at hv'
  have hc0 : 1-z≠0 := by intro h; grobner
  have generic (c : K) : t ≠ ι (RatFunc.C c) := by
    intro h
    exact RatFunc.transcendental_X (K:=K) ((ι.injective h) ▸ isAlgebraic_algebraMap c)
  have hn₁ : t ≠ 4-z := by simpa [z,map_ofNat] using generic (4-v)
  have hn₂ : t ≠ 4-(1-z) := by simpa [z,map_ofNat] using generic (4-(1-v))
  let P : G := ⟨Point.some t Y (short_smooth hY), RatFunc.X,1,rfl,by simp⟩
  have hcurve := cm_generator hv' hv0 hY hn₁
  let vX := phiX (RatFunc.C v) RatFunc.X
  let vY : RatFunc K := (1-(3*(4-RatFunc.C v)^2-35)/(RatFunc.X-(4-RatFunc.C v))^2)/(RatFunc.C v)^3
  have mapped (k : K) : ι (phiX (RatFunc.C k) RatFunc.X)=phiX (ι (RatFunc.C k)) t := by simp [phiX,t,map_ofNat]
  have mapVX : ι vX=phiX z t := mapped _
  have mapVY : ι vY*Y=phiY z t Y := by simp only [vY,phiY,z,t,map_div₀,map_one,map_ofNat,map_pow,map_sub,map_mul]; ring
  let V : G := ⟨Point.some (phiX z t) (phiY z t Y) (short_smooth hcurve),vX,vY,mapVX,mapVY⟩
  let A := abscissa ι Y w hw
  let Q (Z : G) := (height (A Z) : ℤ)
  have ha (Z : G) : ι (A Z) = Z.val.xRep 0 := abscissa_apply ι Y w hw Z
  have para (Z T : G) : Q (Z+T)+Q (Z-T)=2*(Q Z+Q T) := by
    dsimp only [Q]
    exact_mod_cast short_parallelogram_exact ι G.subtype A ha Z T
  have h0 : A 0=1 := ι.injective (by rw [ha,map_one]; rfl)
  have q0 : Q 0=0 := by simp [Q,h0,height]
  have hp : A P=RatFunc.X := ι.injective (by rw [ha]; rfl)
  have qP : Q P=1 := by simp [Q,hp,height]
  have hV : A V=vX := ι.injective ((ha V).trans mapVX.symm)
  have qV : Q V=2 := by
    dsimp only [Q]; rw [hV]
    exact_mod_cast phi_abscissa_degree v hv
  have hx : t≠phiX z t := by
    intro eq
    have bad : A P=A V := ι.injective (by rw [ha,ha]; exact eq)
    have h : Q P=Q V := congrArg (fun r => (height r:ℤ)) bad
    omega
  have chord := conjugate_chord_square hv' hv0 hc0 hY (sub_ne_zero.mpr hn₁) (sub_ne_zero.mpr hn₂)
  have hcX : ι (phiX (RatFunc.C (1-v)) RatFunc.X)=phiX (1-z) t := by
    rw [mapped]; simp [z]
  have eqConj : A (P-V)=phiX (RatFunc.C (1-v)) RatFunc.X := by
    apply ι.injective
    rw [ha,hcX]
    change ((Point.some t Y _)-(Point.some (phiX z t) (phiY z t Y) _)).xRep 0=_
    rw [sub_eq_add_neg,Point.neg_some,Point.add_of_X_ne hx,Point.xRep_some]
    simp only [Matrix.cons_val_zero,addX,slope_of_X_ne hx,negY,shortCurve,zero_mul,add_zero,sub_zero,sub_neg_eq_add]
    rw [div_pow]
    field_simp [sub_ne_zero.mpr hx]
    linear_combination chord
  have hvc : (1-v)^2=(1-v)-2 := by linear_combination hv
  have qC : Q (P-V)=2 := by
    dsimp only [Q]; rw [eqConj]
    exact_mod_cast phi_abscissa_degree (1-v) hvc
  let U := (x-y)•P+(2*y)•V
  exact ⟨P.val,V.val,A U,⟨_,rfl⟩,⟨_,rfl⟩,ha U,cm_lattice_norm Q q0 para P V qP qV qC x y,U.property⟩

end
end SunCoster

end

section

/- Translation by the kernel of the norm-two map in the generic curve field. -/

namespace SunCoster.KernelLift
open Polynomial SunDescent WeierstrassCurve.Affine SunCoster.Torsion
noncomputable section

variable (K : Type*) [Field K] [CharZero K]

abbrev FieldOfCurve :=
  (X^2-C ((RatFunc.X : RatFunc K)^3-35*RatFunc.X+98)).SplittingField

abbrev baseMap := algebraMap (RatFunc K) (FieldOfCurve K)
abbrev constMap := (baseMap K).comp RatFunc.C

theorem kernel_field_embedding (v : K) (hv : v^2=v-2) (Y : FieldOfCurve K)
    (hP : (shortCurve _).Nonsingular (baseMap K RatFunc.X) Y) :
    ∃ f : FieldOfCurve K →+* FieldOfCurve K, (∀ a : K, f (constMap K a)=constMap K a) ∧
      f (baseMap K RatFunc.X)=tx (4-constMap K v) (baseMap K RatFunc.X) ∧
      (f Y=ty (4-constMap K v) (baseMap K RatFunc.X) Y ∨
        f Y= -(ty (4-constMap K v) (baseMap K RatFunc.X) Y)) := by
  classical
  let L := FieldOfCurve K
  let ι := baseMap K
  let x := ι RatFunc.X
  let w := constMap K v
  let e := 4-v
  let b := 3*e^2-35
  have eb : b≠0 := by dsimp only [b,e]; intro h; grobner
  let τ := translatedFlip e b eb
  let g := ι.comp τ.toRingHom
  have wv : w^2=w-2 := by simpa only [w,map_pow,map_sub,map_ofNat] using congrArg (constMap K) hv
  have er : constMap K e=4-w := by simp only [e,w,map_sub,map_ofNat]
  have br : constMap K b=3*(4-w)^2-35 := by simp only [b,map_sub,map_pow,map_mul,map_ofNat,er]
  have xne : x≠4-w := by
    intro h
    have diff : ι RatFunc.X=ι (RatFunc.C e) := h.trans er.symm
    exact (RatFunc.transcendental_X (K:=K)) ((ι.injective diff) ▸ isAlgebraic_algebraMap e)
  have hx : g RatFunc.X=tx (4-w) x := by
    change ι (translatedFlip e b eb RatFunc.X)=_
    simp only [translatedFlip_X,shiftX,map_add,map_div₀,map_neg]
    change constMap K b/(x+ -constMap K e)+constMap K e=_
    rw [er,br,←sub_eq_add_neg]
    exact add_comm ..
  have heq : (0:L)^2=(4-w)^3-35*(4-w)+98 := by linear_combination (w-11)*wv
  obtain ⟨k,_⟩ := translation (short_smooth heq) hP xne
  let t := ty (4-w) x Y
  have tk : t^2=g (((RatFunc.X : RatFunc K)^3-35*RatFunc.X+98)) := by
    simp only [map_add,map_sub,map_pow,map_mul,map_ofNat,hx]
    exact short_equation.mp k.1
  obtain ⟨f,ext⟩ := lift_quadratic g ((RatFunc.X : RatFunc K)^3-35*RatFunc.X+98) t tk
  have fx : f x=tx (4-w) x := (ext RatFunc.X).trans hx
  have fy := congrArg f (short_equation.mp hP.1)
  change f (Y^2)=f (x^3-35*x+98) at fy
  simp only [map_pow,map_add,map_sub,map_mul,map_ofNat,fx] at fy
  have sq : (f Y)^2=t^2 := fy.trans (short_equation.mp k.1).symm
  refine ⟨f,?_,fx,sq_eq_sq_iff_eq_or_eq_neg.mp sq⟩
  intro a
  change f (ι (RatFunc.C a))=ι (RatFunc.C a)
  exact (ext (RatFunc.C a)).trans (congrArg ι (τ.commutes a))

end
end SunCoster.KernelLift

end

section

/- Simultaneous reciprocal transformation of the Coster parameters of a
generic point and its odd-norm CM image. -/

namespace SunCoster.KernelLift
open SunSevenIsogeny WeierstrassCurve.Affine SunCoster.Torsion ChartAction
noncomputable section

variable {L : Type*} [Field L] [CharZero L] [DecidableEq L]

def kernelPoint (v : L) (hv : v^2=v-2) : (shortCurve L).Point :=
  Point.some (4-v) 0 (short_smooth (by grobner))

theorem reciprocal_translation (v : L) (hv : v^2=v-2) (P : (shortCurve L).Point)
    (hp : param P≠0) : param P * param (P+kernelPoint v hv)=1/(2*v-1) := by
  cases P with
  | zero => exact (hp rfl).elim
  | some x y h =>
    have eq := short_equation.mp h.1
    have y0 : y≠0 := by intro z; simp [param,z] at hp
    have x0 : x≠4-v := by
      intro z
      have he : y^2=0 := by rw [eq,z]; grobner
      exact (pow_ne_zero 2 y0) he
    obtain ⟨_,e⟩ := translation (short_smooth (by grobner : (0:L)^2=(4-v)^3-35*(4-v)+98)) h x0
    rw [kernelPoint,e]
    exact parameter_kernel v x y hv eq x0 y0

theorem kernel_generators (f : L →+* L) (x y v : L) (hv : v^2=v-2)
    (hP : (shortCurve L).Nonsingular x y)
    (hV : (shortCurve L).Nonsingular (phiX v x) (phiY v x y))
    (fv : f v=v) (fx : f x=tx (4-v) x)
    (fy : f y=ty (4-v) x y ∨ f y= -(ty (4-v) x y)) (hx : x≠4-v) :
    let P := Point.some _ _ hP
    let V := Point.some _ _ hV
    (shortMap f P=P+kernelPoint v hv ∧ shortMap f V=V) ∨
    (shortMap f P= -(P+kernelPoint v hv) ∧ shortMap f V= -V) := by
  dsimp only
  obtain ⟨_,ep⟩ := translation (short_smooth (by grobner : (0:L)^2=(4-v)^3-35*(4-v)+98)) hP hx
  obtain ⟨ex,ey⟩ := kernel_image v x y hv hx
  have fX : f (phiX v x)=phiX v x := by
    calc
      _=phiX v (f x) := by simp [phiX,fv,map_ofNat]
      _=_ := by rw [fx,ex]
  have fY : f (phiY v x y)=phiY v (tx (4-v) x) (f y) := by
    simp only [phiY,map_div₀,map_mul,map_sub,map_one,map_ofNat,map_pow,fx,fv]
  simp only [kernelPoint,ep,shortMap_some,Point.neg_some,Point.some.injEq,fX,fx,true_and]
  rcases fy with e | e
  · exact .inl ⟨e,fY.trans (e ▸ ey)⟩
  · right
    simp only [shortCurve,negY,zero_mul,sub_zero]
    refine ⟨e,?_⟩
    rw [fY,e,←ey]
    simp [phiY,neg_div]

private theorem odd_smul_torsion {G : Type*} [AddCommGroup G] (T : G) (hT : T+T=0)
    (m : ℤ) (hm : Odd m) : m•T=T := by
  obtain ⟨a,e⟩ := hm
  rw [e,add_zsmul,one_zsmul,mul_comm,mul_zsmul,two_zsmul,hT,zsmul_zero,zero_add]

/-- The same sign occurs in the two reciprocal translations. The field
embedding fixes every constant. -/
theorem simultaneous_reciprocals (K : Type*) [Field K] [CharZero K] [DecidableEq (FieldOfCurve K)]
    (v : K) (hv : v^2=v-2) (Y : FieldOfCurve K)
    (hP : (shortCurve _).Nonsingular (baseMap K RatFunc.X) Y)
    (hV : (shortCurve _).Nonsingular (phiX (constMap K v) (baseMap K RatFunc.X))
      (phiY (constMap K v) (baseMap K RatFunc.X) Y))
    (m n : ℤ) (hm : Odd m) :
    let P := Point.some _ _ hP
    let V := Point.some _ _ hV
    let U := m•P+n•V
    param P≠0 → param U≠0 →
    ∃ f : FieldOfCurve K →+* FieldOfCurve K, (∀ a : K, f (constMap K a)=constMap K a) ∧
      let c := constMap K (1/(2*v-1))
      (f (param P)*param P=c ∧ f (param U)*param U=c) ∨
      (f (param P)*param P= -c ∧ f (param U)*param U= -c) := by
  intro P V U hp hu
  let ι := baseMap K
  let x := ι RatFunc.X
  let w := constMap K v
  have hw : w^2=w-2 := by simpa only [w,map_pow,map_sub,map_ofNat] using congrArg (constMap K) hv
  let T := kernelPoint w hw
  have hT : T+T=0 := two_torsion ..
  have hx : x≠4-w := by
    intro he
    have e : ι RatFunc.X=ι (RatFunc.C (4-v)) := by
      change x=constMap K (4-v)
      rw [map_sub,map_ofNat]; exact he
    exact (RatFunc.transcendental_X (K:=K)) (ι.injective e ▸ isAlgebraic_algebraMap (4-v))
  obtain ⟨f,hf,fx,fy⟩ := kernel_field_embedding K v hv Y hP
  have act := kernel_generators f x Y w hw hP hV (hf v) fx fy hx
  have p := reciprocal_translation w hw P hp
  have u := reciprocal_translation w hw U hu
  have c : constMap K (1/(2*v-1))=1/(2*w-1) := by simp only [w,map_div₀,map_one,map_sub,map_mul,map_ofNat]
  have addt : m•(P+T)+n•V=U+T := by
    rw [zsmul_add,odd_smul_torsion T hT m hm]
    dsimp only [U]; abel
  refine ⟨f,hf,?_⟩
  dsimp only
  rw [←param_map,←param_map,c]
  rcases act with ⟨p',v'⟩ | ⟨p',v'⟩
  · change shortMap f P=P+T at p'
    change shortMap f V=V at v'
    have su : shortMap f U=U+T := by
      change shortMap f (m•P+n•V)=_
      simp only [map_add,map_zsmul,p',v',addt]
    left
    rw [p',su]; exact ⟨(mul_comm ..).trans p,(mul_comm ..).trans u⟩
  · change shortMap f P= -(P+T) at p'
    change shortMap f V= -V at v'
    have su : shortMap f U= -(U+T) := by
      change shortMap f (m•P+n•V)=_
      simp only [map_add,map_zsmul,p',v',zsmul_neg,←neg_add,addt]
    right
    rw [p',su,param_neg,param_neg,neg_mul,neg_mul]
    exact ⟨congrArg Neg.neg ((mul_comm ..).trans p),congrArg Neg.neg ((mul_comm ..).trans u)⟩

end
end SunCoster.KernelLift

end

section

namespace SunCoster
open Polynomial SunDescent
noncomputable section

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

private theorem negX_trans : Transcendental K (-(RatFunc.X : RatFunc K)) := by
  intro h; exact RatFunc.transcendental_X (by simpa using h.neg)

private def reflectT : RatFunc K →ₐ[K] RatFunc K := subst (-RatFunc.X) negX_trans

private theorem reflect_oddMap (q : RatFunc K) : reflectT (oddMap q)= -oddMap q := by
  let j := subst ((RatFunc.X : RatFunc K)^2) (transcendental_of_deg (by rw [square_degree]; decide))
  have w : (reflectT (K:=K)).comp j=j := by
    apply ratHom_ext
    simp [j,reflectT]
  have e : reflectT (j q)=j q := DFunLike.congr_fun w q
  change reflectT (RatFunc.X*j q)= -(RatFunc.X*j q)
  rw [map_mul,e,show reflectT RatFunc.X= -(RatFunc.X : RatFunc K) from subst_X ..,neg_mul]

theorem hom_num (f : RatFunc K →ₐ[K] L) (F : RatFunc K) :
    aeval (f RatFunc.X) F.num=f F*aeval (f RatFunc.X) F.denom := by
  have h := (div_eq_iff (RatFunc.algebraMap_ne_zero F.denom_ne_zero)).mp (RatFunc.num_div_denom F)
  have E := congrArg f h
  simpa only [map_mul,←RatFunc.aeval_X_left_eq_algebraMap,←aeval_algHom_apply] using E

theorem oddMap_num (q : RatFunc K) :
    Reciprocity.oddFraction (oddMap q).num (oddMap q).denom := by
  let F := oddMap q
  have e := hom_num (reflectT (K:=K)) F
  have h := hom_num (AlgHom.id K (RatFunc K)) F
  rw [show reflectT RatFunc.X= -(RatFunc.X : RatFunc K) from subst_X ..] at e
  change aeval (-RatFunc.X : RatFunc K) F.num = reflectT F * aeval (-RatFunc.X : RatFunc K) F.denom at e
  change aeval (RatFunc.X : RatFunc K) F.num=F*aeval RatFunc.X F.denom at h
  rw [show reflectT F= -F from reflect_oddMap q] at e
  apply (transcendental_iff_injective.mp (RatFunc.transcendental_X (K:=K)))
  simp only [map_mul,map_neg,aeval_comp,aeval_X]
  rw [e,h]
  ring

theorem signed_reciprocity (q : RatFunc K) (c : K) (hc : c≠0)
    (t w : L) (ht : Transcendental K t) (hF : ratEval t ht (oddMap q)=w)
    (σ : L →ₐ[K] L)
    (H : (σ t*t=algebraMap K L c ∧ σ w*w=algebraMap K L c) ∨
      (σ t*t= -(algebraMap K L c) ∧ σ w*w= -(algebraMap K L c))) :
    Reciprocity.reciprocalFraction c (oddMap q).num (oddMap q).denom := by
  let F := oddMap q
  let E := ratEval t ht
  let j := flip c hc
  have nz : t≠0 := by rintro rfl; exact ht isAlgebraic_zero
  have ec (k : K) : E (RatFunc.C k)=algebraMap K L k := E.commutes _
  have ej : E (j RatFunc.X)=algebraMap K L c/t := by
    simp only [j,flip_X,map_div₀,ec,show E RatFunc.X=t from ratEval_X ..]
  have ed : E F=w := hF
  have prod : F*j F=RatFunc.C c := by
    apply E.injective
    change E (F*j F)=E (RatFunc.C c)
    rw [map_mul,ec,ed]
    rcases H with ⟨Ht,Hw⟩|⟨Ht,Hw⟩
    · have same : σ.comp E=E.comp j := by
        apply ratHom_ext
        change σ (E RatFunc.X)=E (j RatFunc.X)
        rw [show E RatFunc.X=t from ratEval_X ..,ej]; exact (eq_div_iff nz).mpr Ht
      have v := DFunLike.congr_fun same F
      change σ (E F)=E (j F) at v
      rw [ed] at v
      rw [←v,mul_comm,Hw]
    · have same : σ.comp E=(E.comp j).comp reflectT := by
        apply ratHom_ext
        change σ (E RatFunc.X)=E (j (reflectT RatFunc.X))
        rw [show E RatFunc.X=t from ratEval_X ..,show reflectT RatFunc.X= -(RatFunc.X : RatFunc K) from subst_X ..,
          map_neg,map_neg,ej,←neg_div]
        exact (eq_div_iff nz).mpr Ht
      have v := DFunLike.congr_fun same F
      change σ (E F)=E (j (reflectT F)) at v
      rw [ed,show reflectT F= -F from reflect_oddMap q,map_neg,map_neg] at v
      linear_combination -Hw+w*v
  have hj := hom_num j F
  have hi := hom_num (AlgHom.id K (RatFunc K)) F
  rw [show j RatFunc.X=RatFunc.C c/RatFunc.X from flip_X ..] at hj
  change aeval (RatFunc.C c/RatFunc.X) F.num=j F*aeval (RatFunc.C c/RatFunc.X) F.denom at hj
  change aeval (RatFunc.X : RatFunc K) F.num=F*aeval RatFunc.X F.denom at hi
  unfold Reciprocity.reciprocalFraction
  dsimp only
  change _=RatFunc.C c*aeval RatFunc.X F.denom*aeval _ F.denom
  rw [hi,hj]
  linear_combination (aeval RatFunc.X F.denom)*(aeval (RatFunc.C c/RatFunc.X) F.denom)*prod

end
end SunCoster

end

section

namespace SunCoster.RationalDerivative
open Polynomial
noncomputable section

variable {K : Type*} [Field K]
local instance : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _
private abbrev emb := algebraMap K[X] (RatFunc K)

private def quotient (a b : K[X]) : RatFunc K :=
  (emb a.derivative * emb b - emb a * emb b.derivative) / (emb b)^2

def deriv (f : RatFunc K) : RatFunc K :=
  f.liftOn' quotient (by
    intro a b c hb hc
    simp only [quotient,derivative_mul,map_add,map_mul]
    field_simp [RatFunc.algebraMap_ne_zero hb,RatFunc.algebraMap_ne_zero hc]
    <;> ring)

theorem deriv_div (a b : K[X]) : deriv (emb a / emb b) = quotient a b := by
  unfold deriv
  apply RatFunc.liftOn'_div
  simp [quotient]

theorem deriv_poly (a : K[X]) : deriv (emb a) = emb a.derivative := by
  simpa [quotient] using deriv_div a 1

private theorem add (f g : RatFunc K) : deriv (f+g)=deriv f+deriv g := by
  induction f using RatFunc.induction_on with
  | f a b hb =>
    induction g using RatFunc.induction_on with
    | f c d hd =>
      have h₁ := RatFunc.algebraMap_ne_zero hb
      have h₂ := RatFunc.algebraMap_ne_zero hd
      have e : emb a/emb b + emb c/emb d=emb (a*d+c*b)/emb (b*d) := by
        simp only [map_add,map_mul]; field_simp
      rw [e,deriv_div,deriv_div,deriv_div]
      simp only [quotient,derivative_mul,derivative_add,map_add,map_mul]
      field_simp
      <;> ring

private theorem mul (f g : RatFunc K) : deriv (f*g)=f*deriv g+g*deriv f := by
  induction f using RatFunc.induction_on with
  | f a b hb =>
    induction g using RatFunc.induction_on with
    | f c d hd =>
      have h₁ := RatFunc.algebraMap_ne_zero hb
      have h₂ := RatFunc.algebraMap_ne_zero hd
      have e : emb a/emb b * (emb c/emb d)=emb (a*c)/emb (b*d) := by
        simp only [map_mul,div_mul_div_comm]
      rw [e,deriv_div,deriv_div,deriv_div]
      simp only [quotient,derivative_mul,map_add,map_mul]
      field_simp
      <;> ring

def operator : Derivation ℤ (RatFunc K) (RatFunc K) := by
  let a : RatFunc K →+ RatFunc K :=
    { toFun := deriv, map_zero' := by simpa using deriv_poly (0 : K[X]), map_add' := add }
  refine { toFun := deriv, map_add' := add, map_smul' := ?_,
           map_one_eq_zero' := ?_, leibniz' := mul }
  · intro n x
    simpa [a,Algebra.smul_def,zsmul_eq_mul] using (map_zsmul a n x)
  · simpa using deriv_poly (1 : K[X])

@[simp] theorem operator_X : operator (RatFunc.X : RatFunc K) = 1 := by
  change deriv (RatFunc.X : RatFunc K) = _
  simpa [RatFunc.algebraMap_X] using deriv_poly (X : K[X])

@[simp] theorem operator_C (k : K) : operator (RatFunc.C k) = 0 := by
  change deriv (RatFunc.C k) = _
  simpa [RatFunc.algebraMap_C] using deriv_poly (C k)

end
end SunCoster.RationalDerivative

end

section

namespace SunCoster.GenericCM
open Polynomial SunSevenIsogeny WeierstrassCurve.Affine
noncomputable section

variable (K : Type*) [Field K] [CharZero K]

abbrev Base := RatFunc K

abbrev cover : (Base K)[X] := X^2-C (ChartAction.radicand K)

abbrev CurveField := ChartAction.DeckField K
local instance : Algebra ℤ (CurveField K) := Ring.toIntAlgebra _
local instance : Algebra ℤ (Base K) := Ring.toIntAlgebra _

abbrev abscissa : CurveField K := ChartAction.incl K RatFunc.X

abbrev constant (v : K) : CurveField K := ChartAction.incl K (RatFunc.C v)

theorem ordinate_exists : ∃ y : CurveField K, y^2=(abscissa K)^3-35*abscissa K+98 := by
  have hs := Polynomial.SplittingField.splits (cover K)
  have hh : ((cover K).map (algebraMap _ (CurveField K))).natDegree=2 := by
    rw [natDegree_map]
    unfold cover
    compute_degree <;> norm_num
  obtain ⟨y,hy⟩ := hs.exists_eval_eq_zero (degree_ne_of_natDegree_ne (hh.trans_ne (by decide : (2:ℕ)≠0)))
  refine ⟨y,?_⟩
  let w := (RatFunc.X : Base K)^3-35*RatFunc.X+98
  change ((X^2-C w).map (algebraMap (Base K) (CurveField K))).eval y=0 at hy
  rw [Polynomial.map_sub,Polynomial.map_pow,map_X,map_C,eval_sub,eval_pow,eval_X,
    eval_C,sub_eq_zero] at hy
  simpa only [w,abscissa,map_add,map_sub,map_mul,map_pow,map_ofNat] using hy

/-- A generic point and its norm-two image, with the normalized invariant
derivation. Both points have coordinates in the same finite function field. -/
theorem generic_generators (v : K) (hv : v^2=v-2) :
    ∃ (D : Derivation ℤ (CurveField K) (CurveField K)) (y : CurveField K),
      ∃ (hP : (shortCurve _).Nonsingular (abscissa K) y)
        (hG : (shortCurve _).Nonsingular (phiX (constant K v) (abscissa K))
          (phiY (constant K v) (abscissa K) y)),
      Velocity D 1 (.some _ _ hP) ∧ Velocity D (constant K v) (.some _ _ hG) ∧
      ∀ k : K, D (constant K k)=0 := by
  classical
  let F := Base K
  let L := CurveField K
  letI : Differential F := ⟨RationalDerivative.operator⟩
  letI : Differential L := Differential.differentialFiniteDimensional F L
  letI : DifferentialAlgebra F L := Differential.differentialAlgebraFiniteDimensional
  let d := Differential.deriv (R:=L)
  let x := abscissa K
  let w := constant K v
  have dx : d x=1 := by
    change Differential.deriv (algebraMap F L RatFunc.X)=_
    rw [deriv_algebraMap]
    have h : Differential.deriv (RatFunc.X : F)=1 := RationalDerivative.operator_X
    rw [h,map_one]
  have dc (k : K) : d (constant K k)=0 := by
    change Differential.deriv (algebraMap F L (RatFunc.C k))=_
    rw [deriv_algebraMap]
    have h : Differential.deriv (RatFunc.C k : F)=0 := RationalDerivative.operator_C _
    rw [h,map_zero]
  obtain ⟨y,hy⟩ := ordinate_exists K
  change y^2=x^3-35*x+98 at hy
  have dpoly := congrArg d hy
  simp only [d.leibniz_pow,d.map_add,d.map_sub,d.leibniz,show d (35:L)=0 from d.map_natCast 35,
    show d (98:L)=0 from d.map_natCast 98,add_zero,
    Nat.reduceSub,pow_one,smul_eq_mul,nsmul_eq_mul,Nat.cast_ofNat,dx,mul_one,mul_zero] at dpoly
  have hy0 : y≠0 := by
    intro e
    rw [e] at hy dpoly
    have cubic : x^3-35*x+98=0 := by simpa using hy.symm
    have quad : 3*x^2-35=0 := by simpa using dpoly.symm
    clear * - cubic quad
    grobner
  let D := (2*y) • d
  have hDx : D x=2*y := by change (2*y)*d x=_; rw [dx,mul_one]
  have hDy : D y=3*x^2-35 := by change (2*y)*d y=_; linear_combination dpoly
  have hw : w^2=w-2 := by
    have e := congrArg ((algebraMap F L).comp RatFunc.C) hv
    simpa only [w,constant,map_pow,map_sub,map_ofNat,RingHom.comp_apply] using e
  have hw0 : w≠0 := by intro e; rw [e] at hw; norm_num at hw
  have dw : d w=0 := dc v
  have hu : d (4-w)=0 := by simp [dw,show d (4:L)=0 from d.map_natCast 4]
  have hd : x≠4-w := by intro e; rw [e,hu] at dx; exact zero_ne_one dx
  have hi : 1-(3*(4-w)^2-35)/(x-(4-w))^2≠0 := by
    intro e
    have ee : (x-(4-w))^2 = 3*(4-w)^2-35 := by
      field_simp [sub_ne_zero.mpr hd] at e
      linear_combination e
    have de := congrArg d ee
    simp only [d.leibniz_pow,d.map_sub,d.leibniz,show d (3:L)=0 from d.map_natCast 3,
      show d (35:L)=0 from d.map_natCast 35,show d (4:L)=0 from d.map_natCast 4,
      dw,dx,hu,sub_zero,mul_zero,
      zero_mul,add_zero,Nat.reduceSub,pow_one,smul_eq_mul,nsmul_eq_mul,Nat.cast_ofNat,mul_one] at de
    apply hd
    linear_combination de/2
  have hy' : phiY w x y ≠ 0 := div_ne_zero (mul_ne_zero hy0 hi) (pow_ne_zero _ hw0)
  refine ⟨D,y,velocity_smooth hy,velocity_smooth (cm_generator hw hw0 hy hd),?_,?_,?_⟩
  · exact ⟨by simpa using hDx,by simpa using hDy⟩
  · simpa using generator_velocity D w x y 1 hw hw0 hd hy (by simpa using hDx) hy'
  · intro k; change (2*y)*d (constant K k)=0; rw [dc,mul_zero]

end
end SunCoster.GenericCM

end

section

open Polynomial

namespace SunFrobenius

/-- A primitive reciprocal pair after reduction to the residue field. Vanishing
of the first `p` coefficients of the quotient forces degree `p` and leaves
only the leading coefficient of the numerator and the constant denominator. -/
theorem reciprocal_reduction {K : Type*} [Field K] {d p : ℕ}
    (N D : K[X]) (hdp : d ≤ p) (ndeg : N.natDegree ≤ d) (ddeg : D.natDegree ≤ d)
    (primitive : N ≠ 0 ∨ D ≠ 0)
    (recip : ∀ j ≤ d, N.coeff j = 0 ↔ D.coeff (d-j) = 0)
    (low : ∀ i < p, N.coeff i = 0) :
    d = p ∧ D.coeff 0 ≠ 0 ∧ N = C (N.coeff p) * X^p ∧ D = C (D.coeff 0) := by
  have Dzero {j : ℕ} (hj : 0 < j) : D.coeff j = 0 := by
    by_cases h : j ≤ d
    · have h' : d-j < p := by omega
      simpa only [Nat.sub_sub_self h] using (recip (d-j) (Nat.sub_le ..)).mp (low _ h')
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  have hD : D = C (D.coeff 0) := by
    ext i
    by_cases hi : i = 0
    · simp [hi]
    · simpa [coeff_C, hi] using Dzero (Nat.pos_of_ne_zero hi)
  have nonzero : N.coeff d ≠ 0 := by
    intro hn
    have dc : D.coeff 0 = 0 := by simpa using (recip d le_rfl).mp hn
    have nz : N = 0 := by
      ext j
      simp only [coeff_zero]
      rcases lt_trichotomy j d with h | rfl | h
      · exact low j (h.trans_le hdp)
      · exact hn
      · exact coeff_eq_zero_of_natDegree_lt (ndeg.trans_lt h)
    have dz : D = 0 := hD.trans (by simp [dc])
    exact primitive.elim (· nz) (· dz)
  have hdp' : d = p := le_antisymm hdp (le_of_not_gt (fun h => nonzero (low d h)))
  subst d
  refine ⟨rfl, fun h => nonzero ((recip p le_rfl).mpr (by simpa using h)), ?_, hD⟩
  ext j
  rw [coeff_C_mul, coeff_X_pow]
  rcases lt_trichotomy j p with h | rfl | h
  · simp [h.ne, low j h]
  · simp
  · simp [h.ne', coeff_eq_zero_of_natDegree_lt (ndeg.trans_lt h)]

end SunFrobenius

end

section

/- Primitive reciprocal presentations at the inseparable prime. -/

namespace SunFrobenius
open Polynomial

private theorem euler_factor {K : Type*} [Field K] (m : ℕ) (T : K[X]) :
    X * (X^m*T).derivative = X^m*(C (m:K)*T + X*T.derivative) := by
  cases m with
  | zero => simp
  | succ m =>
    rw [derivative_mul,derivative_X_pow]
    simp only [Nat.succ_sub_one, Nat.cast_succ, pow_succ X m,map_add,map_one,C_eq_natCast]
    ring

/-- Vanishing of the Wronskian implies congruence of the orders at zero.
The input polynomials may have a common factor. -/
theorem congruent_orders {p : ℕ} [Fact p.Prime] (N D : (ZMod p)[X])
    (hN : N ≠ 0) (hD : D ≠ 0) (hw : N.derivative*D = N*D.derivative) :
    N.natTrailingDegree ≡ D.natTrailingDegree [MOD p] := by
  let n := N.natTrailingDegree
  let m := D.natTrailingDegree
  obtain ⟨U,hU⟩ : X^n ∣ N := X_pow_dvd_iff.mpr fun _ h => coeff_eq_zero_of_lt_natTrailingDegree h
  obtain ⟨V,hV⟩ : X^m ∣ D := X_pow_dvd_iff.mpr fun _ h => coeff_eq_zero_of_lt_natTrailingDegree h
  have U0 : U.eval 0 ≠ 0 := by
    have h : N.coeff n ≠ 0 := coeff_natTrailingDegree_ne_zero.mpr hN
    rw [hU,coeff_X_pow_mul',if_pos le_rfl,Nat.sub_self,coeff_zero_eq_eval_zero] at h
    exact h
  have V0 : V.eval 0 ≠ 0 := by
    have h : D.coeff m ≠ 0 := coeff_natTrailingDegree_ne_zero.mpr hD
    rw [hV,coeff_X_pow_mul',if_pos le_rfl,Nat.sub_self,coeff_zero_eq_eval_zero] at h
    exact h
  have ha : (X*N.derivative)*D=N*(X*D.derivative) := by linear_combination X*hw
  rw [hU,hV,euler_factor,euler_factor] at ha
  have hc : (C (n:ZMod p)*U+X*U.derivative)*V = U*(C (m:ZMod p)*V+X*V.derivative) := by
    apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero n (X_ne_zero (R:=ZMod p)))
      (pow_ne_zero m X_ne_zero))
    linear_combination ha
  have he := congrArg (Polynomial.eval 0) hc
  simp only [eval_mul,eval_add,eval_C,eval_X,zero_mul,add_zero] at he
  apply (ZMod.natCast_eq_natCast_iff ..).mp
  change (n:ZMod p) = (m:ZMod p)
  apply mul_right_cancel₀ (mul_ne_zero U0 V0)
  linear_combination he

/-- In an odd-over-even reciprocal presentation the orders at zero are
different. Under a degree bound of p, vanishing of the Wronskian forces
orders p and zero. In particular reduction cannot lose degree. -/
theorem primitive_reciprocal_frobenius {p d : ℕ} [Fact p.Prime]
    (N D : (ZMod p)[X]) (hdp : d ≤ p) (hNdeg : N.natDegree ≤ d)
    (hDdeg : D.natDegree < d) (hprim : N ≠ 0 ∨ D ≠ 0)
    (recip : ∀ j ≤ d, N.coeff j = 0 ↔ D.coeff (d-j) = 0)
    (oddN : ∀ i, i % 2 = 0 → N.coeff i = 0)
    (evenD : ∀ i, i % 2 = 1 → D.coeff i = 0)
    (hw : N.derivative*D = N*D.derivative) :
    d = p ∧ D.coeff 0 ≠ 0 ∧ N = C (N.coeff p)*X^p ∧ D = C (D.coeff 0) := by
  have nz : N ≠ 0 := by
    intro z
    apply hprim.resolve_left (by simpa using z)
    ext i
    rw [coeff_zero]
    by_cases h : i ≤ d
    · simpa only [Nat.sub_sub_self h] using
        (recip (d-i) (Nat.sub_le ..)).mp (by simp [z])
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  have dz : D ≠ 0 := by
    intro z
    apply nz
    ext i
    rw [coeff_zero]
    by_cases h : i ≤ d
    · exact (recip i h).mpr (by simp [z])
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  have hn := coeff_natTrailingDegree_ne_zero.mpr nz
  have hm := coeff_natTrailingDegree_ne_zero.mpr dz
  have parityN := mt (oddN _) hn
  have parityD := mt (evenD _) hm
  have nle := le_natDegree_of_ne_zero hn
  have mle := le_natDegree_of_ne_zero hm
  have hmod := congruent_orders N D nz dz hw
  have hn' : N.natTrailingDegree = p := by
    by_contra ne
    have ltN : N.natTrailingDegree < p := by omega
    have ltD : D.natTrailingDegree < p := by omega
    have eq := hmod.eq_of_lt_of_lt ltN ltD
    omega
  apply reciprocal_reduction N D hdp hNdeg hDdeg.le hprim recip
  intro i hi
  exact coeff_eq_zero_of_lt_natTrailingDegree (by simpa only [hn'] using hi)

end SunFrobenius

end

section

/- # A p-adic lift of the split CM parameter with prescribed residue -/

namespace SunCoster
open Polynomial

variable {p : ℕ} [Fact p.Prime]

theorem padic_unit_iff_residue {x : ℤ_[p]} : IsUnit x ↔ PadicInt.toZMod x ≠ 0 := by
  rw [← IsLocalRing.notMem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker]

theorem padic_unit_of_pow_residue {k : ℕ} (hk : 0<k) (x : ℤ_[p])
    (hu : IsUnit (PadicInt.toZModPow k x)) : IsUnit x := by
  by_contra hn
  obtain ⟨b,hb⟩ := (PadicInt.norm_lt_one_iff_dvd x).mp (PadicInt.not_isUnit_iff.mp hn)
  let red := ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p)
  have he : red (PadicInt.toZModPow k x)=0 := by
    simp only [hb,map_mul,map_natCast,ZMod.natCast_self,zero_mul]
  exact (hu.map red).ne_zero he

/-- Hensel lifting preserves the original class at every positive precision. -/
theorem lift_sqrt_neg_seven {k : ℕ} (hk : 0<k) (hp2 : p≠2)
    (s : ZMod (p^k)) (hs : s^2 = -7) (hunit : IsUnit s) :
    ∃ z : ℤ_[p], z^2 = -7 ∧ PadicInt.toZModPow k z=s ∧ IsUnit z := by
  let a : ℤ_[p] := s.val
  let res := @PadicInt.toZModPow p _ k
  have ha : res a=s := by simp [res,a]
  have ua := padic_unit_of_pow_residue hk a (ha ▸ hunit)
  have hn2 : (2:ZMod p)≠0 := by simpa using (ZMod.prime_ne_zero p 2 hp2)
  have u2 : IsUnit (2:ℤ_[p]) := padic_unit_iff_residue.mpr (by simpa only [map_ofNat] using hn2)
  let F : Polynomial ℤ_[p] := X^2+7
  have fv (t : ℤ_[p]) : F.aeval t=t^2+7 := by simp [F]
  have dv (t : ℤ_[p]) : F.derivative.aeval t=2*t := by
    simp only [F,derivative_add,derivative_X_pow,derivative_ofNat,add_zero,Nat.reduceSub,
      pow_one,map_mul,aeval_X,Nat.cast_ofNat,map_ofNat]
  have hv : res (a^2+7)=0 := by simp only [map_add,map_pow,map_ofNat,ha,hs,neg_add_cancel]
  have hmem : a^2+7 ∈ RingHom.ker res := hv
  rw [show RingHom.ker res=Ideal.span {(p:ℤ_[p])^k} from PadicInt.ker_toZModPow k,
    Ideal.mem_span_singleton] at hmem
  have small : ‖a^2+7‖<1 := (PadicInt.norm_lt_one_iff_dvd _).mpr
    (dvd_trans (dvd_pow_self _ hk.ne') hmem)
  have nd : ‖F.derivative.aeval a‖=1 := by rw [dv]; exact PadicInt.isUnit_iff.mp (u2.mul ua)
  obtain ⟨z,hz,hclose,_,_⟩ := hensels_lemma (F:=F) (a:=a) (by simpa only [fv,nd,one_pow] using small)
  rw [fv] at hz
  rw [nd] at hclose
  have hza : z^2 = -7 := by linear_combination hz
  have resid : PadicInt.toZMod z=PadicInt.toZMod a := by
    obtain ⟨t,ht⟩ := (PadicInt.norm_lt_one_iff_dvd _).mp hclose
    have he := congrArg (PadicInt.toZMod (p:=p)) ht
    simpa only [map_sub,map_mul,map_natCast,ZMod.natCast_self,zero_mul,sub_eq_zero] using he
  have uz : IsUnit z := padic_unit_iff_residue.mpr (resid ▸ padic_unit_iff_residue.mp ua)
  have usum : IsUnit (z+a) := by
    apply padic_unit_iff_residue.mpr
    rw [map_add,resid,←two_mul]
    exact mul_ne_zero hn2 (padic_unit_iff_residue.mp ua)
  have urs : IsUnit (res z+s) := by simpa only [map_add,ha] using usum.map res
  have hva : (res z)^2 = -7 := by simpa only [map_pow,map_neg,map_ofNat] using congrArg res hza
  refine ⟨z,hza,?_,uz⟩
  apply urs.mul_left_cancel
  linear_combination hva-hs

/-- Reduction from precision four to precision three uses the same p-adic root. -/
theorem lift_cube_four (hp2 : p≠2) (s : ZMod (p^3)) (hs : s^2 = -7) (hu : IsUnit s) :
    ∃ z : ℤ_[p], z^2 = -7 ∧ PadicInt.toZModPow 3 z=s ∧ IsUnit z ∧
      (PadicInt.toZModPow 4 z)^2 = -7 ∧
      ZMod.castHom (pow_dvd_pow p (by decide : 3≤4)) (ZMod (p^3)) (PadicInt.toZModPow 4 z)=s := by
  obtain ⟨z,hz,he,uu⟩ := lift_sqrt_neg_seven (by decide) hp2 s hs hu
  refine ⟨z,hz,he,uu,?_,?_⟩
  · simpa only [map_pow,map_neg,map_ofNat] using congrArg (PadicInt.toZModPow 4) hz
  · exact (DFunLike.congr_fun (PadicInt.zmod_cast_comp_toZModPow 3 4 (by decide)) z).trans he

/-- The factor inherited from the unit residue is a unit. The conjugate factor
is p times its inverse, with both identities already in the integral ring. -/
theorem oriented_padic_factors {k : ℕ} (hk : 0<k) (z : ℤ_[p]) (hz : z^2 = -7)
    (x y : ℤ) (hxy : (p:ℤ)=x^2+7*y^2)
    (hu : IsUnit ((x:ZMod (p^k))+(y:ZMod (p^k))*PadicInt.toZModPow k z)) :
    ∃ u : ℤ_[p]ˣ, (u:ℤ_[p])=x+y*z ∧ x-y*z=(p:ℤ_[p])*↑u⁻¹ ∧
      (x-y*z)*(x+y*z)=(p:ℤ_[p]) := by
  have uplus : IsUnit ((x:ℤ_[p])+y*z) := by
    apply padic_unit_of_pow_residue hk
    simpa only [map_add,map_mul,map_intCast] using hu
  obtain ⟨u,uh⟩ := uplus
  have hxy' : (p:ℤ_[p])=(x:ℤ_[p])^2+7*(y:ℤ_[p])^2 := by exact_mod_cast hxy
  have norm : ((x:ℤ_[p])-y*z)*(x+y*z)=p := by
    linear_combination -(y:ℤ_[p])^2*hz-hxy'
  refine ⟨u,uh,?_,norm⟩
  rw [←norm,←uh,mul_assoc,u.mul_inv, mul_one]

/-- The chosen characteristic-zero embedding simultaneously realizes the
prescribed cubic residue and the oriented factorization in the p-adic field. -/
theorem lift_oriented_cube (hp2 : p≠2) (s : ZMod (p^3)) (hs : s^2 = -7)
    (hsu : IsUnit s) (x y : ℤ) (hxy : (p:ℤ)=x^2+7*y^2)
    (hunit : IsUnit ((x:ZMod (p^3))+(y:ZMod (p^3))*s)) :
    ∃ (z : ℤ_[p]) (u : ℤ_[p]ˣ), z^2 = -7 ∧ PadicInt.toZModPow 3 z=s ∧
      (PadicInt.toZModPow 4 z)^2 = -7 ∧
      ZMod.castHom (pow_dvd_pow p (by decide : 3≤4)) (ZMod (p^3)) (PadicInt.toZModPow 4 z)=s ∧
      (u:ℤ_[p])=x+y*z ∧
      ((z:ℚ_[p])^2 = -7) ∧
      ((x:ℚ_[p])-y*(z:ℚ_[p])) = (p:ℚ_[p])*((u:ℤ_[p]):ℚ_[p])⁻¹ ∧
      ((x:ℚ_[p])-y*(z:ℚ_[p]))*(x+y*(z:ℚ_[p]))=p := by
  obtain ⟨z,hz,he,_,h4,h34⟩ := lift_cube_four hp2 s hs hsu
  obtain ⟨u,hu,hπ,hn⟩ := oriented_padic_factors (k:=3) (by decide) z hz x y hxy (he ▸ hunit)
  refine ⟨z,u,hz,he,h4,h34,hu,?_,?_,?_⟩
  · exact congrArg (fun w : ℤ_[p] => (w:ℚ_[p])) hz
  · have hu0 : ((u:ℤ_[p]):ℚ_[p]) ≠ 0 := PadicInt.coe_ne_zero.mpr u.ne_zero
    apply mul_right_cancel₀ hu0
    rw [mul_assoc,inv_mul_cancel₀ hu0,mul_one,hu]
    exact congrArg (fun w : ℤ_[p] => (w:ℚ_[p])) hn
  · exact congrArg (fun w : ℤ_[p] => (w:ℚ_[p])) hn

end SunCoster

end

section

/- The first Coster–van Hamme coefficient congruence, obtained by pulling back
an even differential. All calculations use polynomials modulo the prime cube. -/

namespace SunCoster
open Polynomial

noncomputable section

abbrev reduceSquare (p : ℕ) : ZMod (p^3) →+* ZMod (p^2) :=
  ZMod.castHom (pow_dvd_pow p (by decide : 2 ≤ 3)) _

def frobeniusPolynomial (p : ℕ) (u : ZMod (p^3)) (A D : (ZMod (p^3))[X]) :
    (ZMod (p^3))[X] :=
  C u * (X^p + C (p : ZMod (p^3))*A) *
    (1-C (p : ZMod (p^3))*D+(C (p : ZMod (p^3))*D)^2)

private theorem nil_cube (p : ℕ) : (C (p : ZMod (p^3)))^3 = 0 := by
  rw [← map_pow,← Nat.cast_pow,ZMod.natCast_self,map_zero]

theorem frobenius_denominator (p : ℕ) (u : ZMod (p^3)) (A D : (ZMod (p^3))[X]) :
    (1+C (p : ZMod (p^3))*D)*frobeniusPolynomial p u A D =
      C u*(X^p+C (p : ZMod (p^3))*A) := by
  unfold frobeniusPolynomial
  linear_combination C u * (X^p+C (p : ZMod (p^3))*A) * D^3 * nil_cube p

private theorem cancel_prime {p : ℕ} (hp : 0<p) {x y : ZMod (p^3)}
    (h : (p:ZMod (p^3))*x=(p:ZMod (p^3))*y) : reduceSquare p x = reduceSquare p y := by
  let : NeZero (p^3) := ⟨pow_ne_zero _ hp.ne'⟩
  let a := x-y
  have h₀ : (p:ZMod (p^3))*a = 0 := by dsimp only [a]; linear_combination h
  have h₁ : ((p*a.val : ℕ) : ZMod (p^3)) = 0 := by simpa using h₀
  have hd := (ZMod.natCast_eq_zero_iff _ _).1 h₁
  have hd₂ : p*p^2 ∣ p*a.val := by convert hd using 1; ring
  have hd' := Nat.dvd_of_mul_dvd_mul_left hp hd₂
  have hr : reduceSquare p a = 0 := by
    calc
      _ = reduceSquare p (a.val : ZMod (p^3)) := by rw [ZMod.natCast_zmod_val]
      _ = _ := by rw [map_natCast,ZMod.natCast_eq_zero_iff]; exact hd'
  exact sub_eq_zero.mp ((map_sub (reduceSquare p) x y).symm.trans hr)

/-- In an even differential, the positive-degree part is divisible by X².
After pullback the factor F² F' vanishes through degree p−1. -/
theorem differential_coefficient (p : ℕ) (hp : 0<p) (u : ZMod (p^3))
    (A D B : (ZMod (p^3))[X]) (haf : A.natDegree<p) (hd : D.coeff 0=0)
    (hB : X^2 ∣ B-1) :
    let F := frobeniusPolynomial p u A D
    ((B.comp F)*F.derivative).coeff (p-1) = (p:ZMod (p^3))*u := by
  let R := ZMod (p^3)
  let v : Polynomial R := C (p:R)
  let F := frobeniusPolynomial p u A D
  change ((B.comp F)*F.derivative).coeff (p-1) = (p:R)*u
  have hv : v^3=0 := nil_cube p
  let G := C u * (A*(1-v*D+(v*D)^2) + X^p*(-D+v*D^2))
  have hf : F=C u*X^p+v*G := by dsimp only [F,frobeniusPolynomial,G,v]; ring
  let H := C u*X^(p-1)+G.derivative
  have hder : F.derivative=v*H := by
    rw [hf]
    simp only [v, H,derivative_add,derivative_C_mul,derivative_X_pow]
    ring
  obtain ⟨T,hT⟩ := hB
  have hcomp : B.comp F=1+F^2*(T.comp F) := by
    have e : B=1+X^2*T := by linear_combination hT
    rw [e,add_comp,one_comp,mul_comp,pow_comp,X_comp]
  have hx : X^p ∣ F^2*F.derivative := by
    refine ⟨(v*(C u)^2*X^p+2*v^2*C u*G)*H, ?_⟩
    rw [hder,hf]
    linear_combination G^2*H*hv
  have hx' : X^p ∣ (B.comp F)*F.derivative - F.derivative := by
    obtain ⟨W,hW⟩ := hx
    refine ⟨W*(T.comp F), ?_⟩
    rw [hcomp]
    linear_combination (T.comp F)*hW
  have hvan := X_pow_dvd_iff.1 hx' (p-1) (by omega)
  rw [coeff_sub,sub_eq_zero] at hvan
  rw [hvan,coeff_derivative,show p-1+1=p by omega]
  have hc : v*F=C ((p:R)*u)*X^p+v^2*C u*(A-X^p*D) := by
    dsimp only [F,frobeniusPolynomial,v]
    rw [map_mul]
    linear_combination (C u*(X^p*D^2-A*D+C (p:R)*A*D^2))*nil_cube p
  have e := congrArg (fun P : Polynomial R => P.coeff p) hc
  simp only [v,coeff_C_mul,coeff_add,coeff_X_pow,if_true,mul_one,←map_pow,
    ←map_mul,coeff_sub,coeff_X_pow_mul',le_refl,if_true,Nat.sub_self,
    hd,coeff_eq_zero_of_natDegree_lt haf,sub_self,mul_zero,add_zero] at e
  rw [← Nat.cast_one (R:=R),← Nat.cast_add,show p-1+1=p by omega,mul_comm]
  exact e

theorem extract (p : ℕ) (hp : 0<p) (u π πbar : ZMod (p^3))
    (A D B : (ZMod (p^3))[X]) (haf : A.natDegree<p) (hd : D.coeff 0=0)
    (hB : X^2 ∣ B-1) (hnorm : π*πbar=(p:ZMod (p^3)))
    (hpull : let F := frobeniusPolynomial p u A D
      ((B.comp F)*F.derivative).coeff (p-1) = π*B.coeff (p-1)) :
    reduceSquare p (B.coeff (p-1)) = reduceSquare p (u*πbar) := by
  have hh := (differential_coefficient p hp u A D B haf hd hB).symm.trans hpull
  apply cancel_prime hp
  linear_combination -πbar*hh - B.coeff (p-1)*hnorm

end
end SunCoster

end

section

namespace SunCoster
open Polynomial
noncomputable section

variable {p : ℕ} [Fact p.Prime]

theorem padic_polynomial_divisible (P : ℤ_[p][X]) (h : P.map PadicInt.toZMod = 0) :
    C (p:ℤ_[p]) ∣ P := by
  apply (C_dvd_iff_dvd_coeff ..).mpr
  intro j
  have e := congrArg (fun f : (ZMod p)[X] => f.coeff j) h
  simp only [coeff_map, coeff_zero] at e
  change P.coeff j ∈ RingHom.ker PadicInt.toZMod at e
  simpa only [PadicInt.ker_toZMod,PadicInt.maximalIdeal_eq_span_p,Ideal.mem_span_singleton] using e

/-- A numerator and denominator with the indicated special fiber have
exact integral correction terms. The degree of the numerator correction
is strictly below p, and both correction terms vanish at zero. -/
theorem integral_normalized_shape (N D : ℤ_[p][X]) (hNdeg : N.natDegree ≤ p)
    (hN0 : N.coeff 0 = 0) (hNp : N.coeff p = 1) (hD0 : D.coeff 0=1)
    (hN : N.map PadicInt.toZMod = X^p) (hD : D.map PadicInt.toZMod = 1) :
    ∃ A E : ℤ_[p][X], A.natDegree < p ∧ A.coeff 0 = 0 ∧ E.coeff 0 = 0 ∧
      N = X^p + C (p:ℤ_[p])*A ∧ D=1 + C (p:ℤ_[p])*E := by
  have hp := (Fact.out : p.Prime).pos
  have hpz : (p:ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  obtain ⟨A,hA⟩ := padic_polynomial_divisible (N-X^p)
    (by simp only [Polynomial.map_sub,Polynomial.map_pow,map_X,hN,sub_self])
  obtain ⟨E,hE⟩ := padic_polynomial_divisible (D-1)
    (by simp only [Polynomial.map_sub,Polynomial.map_one,hD,sub_self])
  have aCoeff (i : ℕ) : N.coeff i - (X^p : ℤ_[p][X]).coeff i = (p:ℤ_[p])*A.coeff i := by
    simpa only [coeff_sub,coeff_C_mul] using congrArg (fun f : ℤ_[p][X] => f.coeff i) hA
  have hdeg : A.natDegree ≤ p-1 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    have e := aCoeff i
    have hzero : (p:ℤ_[p])*A.coeff i=0 := by
      rcases eq_or_lt_of_le (show p ≤ i by omega) with rfl | hh
      · simpa only [hNp,coeff_X_pow_self,sub_self] using e.symm
      · simpa only [coeff_eq_zero_of_natDegree_lt (hNdeg.trans_lt hh),coeff_X_pow,
          if_neg hh.ne',sub_self] using e.symm
    exact (mul_eq_zero.mp hzero).resolve_left hpz
  have a0 : A.coeff 0=0 := by
    apply (mul_eq_zero.mp _).resolve_left hpz
    simpa only [hN0,coeff_X_pow,if_neg hp.ne,sub_self] using (aCoeff 0).symm
  have e0 : E.coeff 0=0 := by
    apply (mul_eq_zero.mp _).resolve_left hpz
    simpa only [coeff_sub,hD0,coeff_one_zero,sub_self,coeff_C_mul] using
      (congrArg (fun f : ℤ_[p][X] => f.coeff 0) hE).symm
  exact ⟨A,E,by omega,a0,e0,by linear_combination hA,by linear_combination hE⟩

/-- The quartic differential identity over the integers forces vanishing of
the Wronskian after reduction, even if the reduced pair has a common factor. -/
theorem wronskian_residue (Q N D H : ℤ_[p][X]) (π : ℤ_[p])
    (hπ : PadicInt.toZMod π=0) (hQ : Q.coeff 0=1)
    (hw : Q*(N.derivative*D-N*D.derivative)^2=C π^2*H) :
    (N.map PadicInt.toZMod).derivative * (D.map PadicInt.toZMod) =
      (N.map PadicInt.toZMod) * (D.map PadicInt.toZMod).derivative := by
  let r := @PadicInt.toZMod p _
  have q : Q.map r ≠ 0 := by
    intro e
    have he := congrArg (fun f : (ZMod p)[X] => f.coeff 0) e
    simp only [coeff_map,hQ,map_one,coeff_zero,one_ne_zero] at he
  have e := congrArg (Polynomial.map r) hw
  simp only [Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_sub,Polynomial.map_C,
    ←Polynomial.derivative_map,show r π=0 from hπ,map_zero,zero_pow (by decide : 2≠0),
    zero_mul] at e
  exact sub_eq_zero.mp (pow_eq_zero_iff (by decide : 2≠0) |>.mp ((mul_eq_zero.mp e).resolve_left q))

/-- A primitive reciprocal polynomial model gives the integral numerator
and denominator with the normalizations used in the coefficient extraction.
Its end coefficients are automatically units. -/
theorem integral_frobenius_shape (d : ℕ) (N D : ℤ_[p][X]) (hdp : d ≤ p)
    (hdN : N.natDegree ≤ d) (hdD : D.natDegree < d) (h0 : N.coeff 0=0)
    (hprim : N.map PadicInt.toZMod ≠ 0 ∨ D.map PadicInt.toZMod ≠ 0)
    (hrec : ∀ j ≤ d, PadicInt.toZMod (N.coeff j) = 0 ↔ PadicInt.toZMod (D.coeff (d-j))=0)
    (hodd : ∀ i, i%2=0 → PadicInt.toZMod (N.coeff i)=0)
    (heven : ∀ i, i%2=1 → PadicInt.toZMod (D.coeff i)=0)
    (hw : (N.map PadicInt.toZMod).derivative * (D.map PadicInt.toZMod) =
      (N.map PadicInt.toZMod) * (D.map PadicInt.toZMod).derivative) :
    d=p ∧ ∃ (a b : ℤ_[p]ˣ) (A E : ℤ_[p][X]),
      (a:ℤ_[p]) = N.coeff p ∧ (b:ℤ_[p]) = D.coeff 0 ∧
      A.natDegree < p ∧ A.coeff 0=0 ∧ E.coeff 0=0 ∧
      N=C (a:ℤ_[p])*(X^p + C (p:ℤ_[p])*A) ∧ D=C (b:ℤ_[p])*(1+C (p:ℤ_[p])*E) := by
  let r := @PadicInt.toZMod p _
  obtain ⟨eD,hh,hN,hD⟩ := SunFrobenius.primitive_reciprocal_frobenius (N.map r) (D.map r) hdp
    (natDegree_map_le.trans hdN) (natDegree_map_le.trans_lt hdD) hprim
    (by simpa only [coeff_map] using hrec) (by simpa only [coeff_map] using hodd)
    (by simpa only [coeff_map] using heven) hw
  subst d
  have hb0 : r (D.coeff 0) ≠ 0 := by simpa only [coeff_map] using hh
  have ha0 : r (N.coeff p) ≠ 0 := mt (hrec p le_rfl).mp (by simpa only [Nat.sub_self] using hb0)
  obtain ⟨a,ha⟩ := padic_unit_iff_residue.mpr ha0
  obtain ⟨b,hb⟩ := padic_unit_iff_residue.mpr hb0
  let M := C (↑a⁻¹:ℤ_[p])*N
  let L := C (↑b⁻¹:ℤ_[p])*D
  have m0 : M.coeff 0=0 := by simp only [M,coeff_C_mul,h0,mul_zero]
  have mp : M.coeff p=1 := by simp only [M,coeff_C_mul,←ha,Units.inv_mul]
  have l0 : L.coeff 0=1 := by simp only [L,coeff_C_mul,←hb,Units.inv_mul]
  have mred : M.map r = X^p := by
    rw [show M.map r=C (r (↑a⁻¹:ℤ_[p]))*(N.map r) by simp [M],hN,coeff_map,←ha,
      ←mul_assoc,←map_mul,←map_mul,Units.inv_mul,map_one,map_one,one_mul]
  have lred : L.map r=1 := by
    rw [show L.map r=C (r (↑b⁻¹:ℤ_[p]))*(D.map r) by simp [L],hD,coeff_map,←hb,
      ←map_mul,←map_mul,Units.inv_mul,map_one,map_one]
  obtain ⟨A,E,hA,hA0,hE,hM,hL⟩ := integral_normalized_shape M L
    ((natDegree_C_mul_le ..).trans hdN) m0 mp l0 mred lred
  refine ⟨rfl,a,b,A,E,ha,hb,hA,hA0,hE,?_,?_⟩
  · rw [←hM]; simp only [M,←mul_assoc,←map_mul,Units.mul_inv,map_one,one_mul]
  · rw [←hL]; simp only [L,←mul_assoc,←map_mul,Units.mul_inv,map_one,one_mul]

/-- The normalized derivative is integral and has constant coefficient one.
This division takes place over p-adic integers before passing to finite precision. -/
theorem integral_derivative_quotient (Q N D J : ℤ_[p][X]) (π : ℤ_[p]) (unit : ℤ_[p]ˣ)
    (hπ : π*(unit:ℤ_[p])=p) (hQ : Q.coeff 0=1)
    (hW0 : (N.derivative*D-N*D.derivative).coeff 0=π)
    (hW : Q*(N.derivative*D-N*D.derivative)^2=C π^2*J) :
    ∃ H : ℤ_[p][X], H.coeff 0=1 ∧ N.derivative*D-N*D.derivative=C π*H ∧ Q*H^2=J := by
  let W := N.derivative*D-N*D.derivative
  have hπ0 : π ≠ 0 := by
    rintro rfl
    have z : (p:ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    exact z (by simpa using hπ.symm)
  have hπr : PadicInt.toZMod π = 0 := by
    have h := congrArg (PadicInt.toZMod (p:=p)) hπ
    rw [map_mul,map_natCast,ZMod.natCast_self] at h
    exact (mul_eq_zero.mp h).resolve_right ((unit.isUnit.map PadicInt.toZMod).ne_zero)
  have he := wronskian_residue Q N D J π hπr hQ hW
  have red : W.map PadicInt.toZMod=0 := by
    simp only [W,Polynomial.map_sub,Polynomial.map_mul,←derivative_map,he,sub_self]
  obtain ⟨G,hG⟩ := padic_polynomial_divisible W red
  let H := C (unit:ℤ_[p])*G
  have hw : W=C π*H := by rw [hG,show H=C (unit:ℤ_[p])*G from rfl,←mul_assoc,←map_mul,hπ]
  have h0 : H.coeff 0=1 := by
    have h := congrArg (fun f : ℤ_[p][X] => f.coeff 0) hw
    change W.coeff 0=π at hW0
    rw [hW0,coeff_C_mul] at h
    apply mul_left_cancel₀ hπ0
    simpa only [mul_one] using h.symm
  refine ⟨H,h0,hw,?_⟩
  apply mul_left_cancel₀ (pow_ne_zero 2 (C_ne_zero.mpr hπ0))
  change Q*W^2=C π^2*J at hW
  rw [hw] at hW
  linear_combination hW

end
end SunCoster

end

section

namespace SunCoster
open Polynomial

/-- The Wronskian identity of a rational map transfers to its polynomial
representative whenever the denominator is a polynomial unit. -/
theorem quotient_quartic_pullback {R : Type*} [CommRing R] (a b π : R)
    (N D F I H : R[X]) (hF : D*F=N) (hI : D*I=1)
    (hW : N.derivative*D - N*D.derivative=C π*H)
    (hQ : (1+C a*X^2+C b*X^4)*H^2 = D^4 + C a*N^2*D^2+C b*N^4) :
    F.derivative = C π*(I^2*H) ∧
    (1+C a*X^2+C b*X^4)*(I^2*H)^2 = (1+C a*X^2+C b*X^4).comp F := by
  have hd : F.derivative*D^2=C π*H := by
    rw [←hF,derivative_mul] at hW
    linear_combination hW
  constructor
  · calc
      F.derivative = (D*I)^2*F.derivative := by rw [hI,one_pow,one_mul]
      _ = C π*(I^2*H) := by linear_combination I^2*hd
  · simp only [add_comp,one_comp,mul_comp,C_comp,pow_comp,X_comp]
    rw [←hF] at hQ
    calc
      _ = I^4 * ((1+C a*X^2+C b*X^4)*H^2) := by ring
      _ = I^4 * (D^4+C a*(D*F)^2*D^2+C b*(D*F)^4) := by rw [hQ]
      _ = (D*I)^4*(1+C a*F^2+C b*F^4) := by ring
      _ = _ := by rw [hI,one_pow,one_mul]

end SunCoster

end

section

namespace SunCoster
open Polynomial
noncomputable section

/-- Direct transport of the characteristic-zero quartic equation to the finite
Frobenius polynomial. Only the squared Wronskian identity and the tangent at
the origin are required. -/
theorem finite_quartic_of_integral_model {p : ℕ} [Fact p.Prime]
    (a b π u : ℤ_[p]) (unit : ℤ_[p]ˣ) (hπ : π*(unit:ℤ_[p])=p)
    (A E : ℤ_[p][X]) (hE0 : E.coeff 0=0)
    (N D : ℤ_[p][X]) (hN : N=C u*(X^p + C (p:ℤ_[p])*A))
    (hD : D=1+C (p:ℤ_[p])*E)
    (hT : (N.derivative*D-N*D.derivative).coeff 0=π)
    (hq : (1+C a*X^2+C b*X^4)*(N.derivative*D-N*D.derivative)^2 =
      C π^2 * (D^4+C a*N^2*D^2+C b*N^4)) :
    let r := @PadicInt.toZModPow p _ 3
    let F := frobeniusPolynomial p (r u) (A.map r) (E.map r)
    let Q := 1+C (r a)*X^2+C (r b)*X^4
    ∃ V : (ZMod (p^3))[X], V.coeff 0=1 ∧ F.derivative=C (r π)*V ∧ Q*V^2=Q.comp F := by
  let r := @PadicInt.toZModPow p _ 3
  let F := frobeniusPolynomial p (r u) (A.map r) (E.map r)
  let T := C (p:ZMod (p^3))*(E.map r)
  let I := 1-T+T^2
  obtain ⟨H,hH0,hWH,hH⟩ := integral_derivative_quotient (1+C a*X^2+C b*X^4) N D
    (D^4+C a*N^2*D^2+C b*N^4) π unit hπ (by simp [coeff_zero_eq_eval_zero]) hT hq
  have mappedPrime : (C (p:ℤ_[p])).map r=C (p:ZMod (p^3)) := by rw [Polynomial.map_C,map_natCast]
  have dmap : D.map r=1+T := by rw [hD,Polynomial.map_add,Polynomial.map_one,
    Polynomial.map_mul,mappedPrime]
  have hf : D.map r*F=N.map r := by
    rw [dmap,hN,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_add,
      Polynomial.map_pow,map_X,Polynomial.map_mul,mappedPrime]
    exact frobenius_denominator p (r u) _ _
  have ht : T^3=0 := by
    simp only [T,mul_pow,←map_pow,←Nat.cast_pow,ZMod.natCast_self,map_zero,zero_mul]
  have hI : D.map r*I=1 := by rw [dmap]; dsimp only [I]; linear_combination ht
  have hw : (N.map r).derivative * D.map r - N.map r*(D.map r).derivative =
      C (r π)*(H.map r) := by
    simpa only [Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,derivative_map] using
      congrArg (Polynomial.map r) hWH
  have hq' : (1+C (r a)*X^2+C (r b)*X^4)*(H.map r)^2 =
      (D.map r)^4+C (r a)*(N.map r)^2*(D.map r)^2+C (r b)*(N.map r)^4 := by
    simpa only [Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_add,Polynomial.map_one,
      Polynomial.map_C,map_X] using congrArg (Polynomial.map r) hH
  obtain ⟨h1,h2⟩ := quotient_quartic_pullback (r a) (r b) (r π) (N.map r) (D.map r)
    F I (H.map r) hf hI hw hq'
  refine ⟨I^2*(H.map r),?_,h1,h2⟩
  have et : T.eval 0=0 := by
    rw [show T=C (p:ZMod (p^3))*(E.map r) from rfl,eval_mul,←coeff_zero_eq_eval_zero (E.map r),
      coeff_map,hE0,map_zero,mul_zero]
  have eh : (H.map r).eval 0=1 := by rw [←coeff_zero_eq_eval_zero,coeff_map,hH0,map_one]
  rw [coeff_zero_eq_eval_zero,eval_mul,eval_pow,show I=1-T+T^2 from rfl,eval_add,eval_sub,
    eval_one,eval_pow,et,eh]
  norm_num

end
end SunCoster

end

section

/- The squared Legendre evaluation from finite Frobenius pullback data. -/

namespace SunCoster
open Polynomial Finset

noncomputable section

/-- Through degree 2h, the Legendre coefficients of the invariant differential
in the parameter t=x/y for the model y²=x(x²+ax+b). Here s²=a²−4b and
1−2z=a/s. -/
def legendreDifferential {R : Type*} [CommRing R] (h : ℕ) (s z : R) : R[X] :=
  ∑ k ∈ range (h+1), monomial (2*k) (s^k * aeval z (shiftedLegendre k))

theorem legendreDifferential_coeff {R : Type*} [CommRing R] (h k : ℕ) (hk : k≤h) (s z : R) :
    (legendreDifferential h s z).coeff (2*k) = s^k * aeval z (shiftedLegendre k) := by
  rw [legendreDifferential,finsetSum_coeff,sum_eq_single k]
  · simp
  · intro j _ hj
    simp [coeff_monomial,show 2*j ≠ 2*k by omega]
  · intro hnk
    simp only [mem_range] at hnk
    omega

theorem legendreDifferential_even {R : Type*} [CommRing R] (h : ℕ) (s z : R) :
    X^2 ∣ legendreDifferential h s z-1 := by
  apply X_pow_dvd_iff.2
  intro n hn
  interval_cases n
  · have e := legendreDifferential_coeff h 0 (Nat.zero_le _) s z
    simpa [shiftedLegendre] using sub_eq_zero.mpr (show (legendreDifferential h s z).coeff 0=1 by
      simpa [shiftedLegendre] using e)
  · rw [coeff_sub,legendreDifferential,finsetSum_coeff,sum_eq_zero]
    · simp [coeff_one]
    · intro j _
      simp [coeff_monomial,show 2*j ≠ 1 by omega]

/-- Coster–van Hamme's r=m=1 conclusion. The leading coefficient of the
rational Frobenius map is normalized by its reciprocity at the two-torsion
point. Only the coefficient of t^(p−1) of the differential pullback is needed. -/
theorem legendre_square_of_pullback (p : ℕ) (hp : p.Prime) (hp2 : p≠2)
    (s z u π πbar : ZMod (p^3)) (hs : IsUnit s)
    (hu : u^2=(s^(p/2))^2) (hn : π*πbar=(p:ZMod (p^3)))
    (A D : (ZMod (p^3))[X]) (hA : A.natDegree<p) (hD : D.coeff 0=0)
    (hPull : let B := legendreDifferential (p/2) s z
      let F := frobeniusPolynomial p u A D
      ((B.comp F)*F.derivative).coeff (p-1)=π*B.coeff (p-1)) :
    (aeval (reduceSquare p z) (shiftedLegendre (p/2)))^2 = (reduceSquare p πbar)^2 := by
  let B := legendreDifferential (p/2) s z
  have hcoeff := extract p hp.pos u π πbar A D B hA hD (legendreDifferential_even _ _ _) hn hPull
  have ho := hp.eq_two_or_odd.resolve_left hp2
  rw [show p-1=2*(p/2) by omega,legendreDifferential_coeff _ _ le_rfl] at hcoeff
  have hz : reduceSquare p (aeval z (shiftedLegendre (p/2))) =
      aeval (reduceSquare p z) (shiftedLegendre (p/2)) := by
    exact (aeval_algHom_apply ((reduceSquare p).toIntAlgHom) z _).symm
  have he := congrArg (fun a : ZMod (p^2) => a^2) hcoeff
  simp only [map_mul,mul_pow,←map_pow,hu] at he
  apply ((hs.pow (p/2)).pow 2 |>.map (reduceSquare p)).mul_left_cancel
  simpa only [map_pow,hz] using he

end
end SunCoster

end

section

namespace SunAlternating

variable {R : Type*} [CommRing R]

theorem chooseAcross (n m : ℕ) :
    ((m:R)+1) * (n.choose (m+1) : R) = ((n:R)-m)*(n.choose m : R) := by
  by_cases h : m ≤ n
  · have e := congrArg (fun t : ℕ => (t:R)) (Nat.choose_succ_right_eq n m)
    push_cast [h] at e
    linear_combination e
  · have a : n < m := by omega
    simp [Nat.choose_eq_zero_of_lt a, Nat.choose_eq_zero_of_lt (show n < m+1 by omega)]

theorem chooseUp (n m : ℕ) :
    ((n:R)+1-m)*( (n+1).choose m : R) = ((n:R)+1)*(n.choose m : R) := by
  by_cases h : m ≤ n+1
  · have e := congrArg (fun t : ℕ => (t:R)) (Nat.choose_mul_succ_eq n m)
    push_cast [h] at e
    linear_combination -e
  · simp [Nat.choose_eq_zero_of_lt (show n < m by omega),
      Nat.choose_eq_zero_of_lt (show n+1 < m by omega)]

private def cert (n m : R) := 2*n^2-(6*m+8)*n+(5*m+8)*(m+1)

private def boundary (R : Type*) [CommRing R] (n m : ℕ) : R :=
  -(-1:R)^n * (((n:R)-m)*(n.choose m : R))^2 * cert (n:R) (m:R)

/-- The alternating sum of squared binomial coefficients in a fixed column. -/
def altColumn (R : Type*) [CommRing R] (N m : ℕ) : R :=
  ∑ n ∈ Finset.range N, (-1:R)^n * (n.choose m : R)^2

private theorem step (n m : ℕ) :
    ((m:R)+1)^2*((m:R)+2) *
        (4*((m:R)+2)*((-1:R)^n*(n.choose (m+2) : R)^2)
        + ((m:R)+1)*((-1:R)^n*(n.choose m : R)^2)) =
      boundary R (n+1) m - boundary R n m := by
  have c₁ := chooseAcross (R:=R) n m
  have c₂ := chooseAcross (R:=R) n (m+1)
  push_cast at c₂
  have c : ((m:R)+1)*((m:R)+2)*(n.choose (m+2):R) =
      ((n:R)-m-1)*((n:R)-m)*(n.choose m:R) := by
    linear_combination ((m:R)+1)*c₂ + ((n:R)-m-1)*c₁
  unfold boundary
  push_cast
  rw [chooseUp, pow_succ]
  unfold cert
  linear_combination 4*(-1:R)^n * congrArg (fun t : R => t^2) c

private theorem telescope (N m : ℕ) :
    ((m:R)+1)^2*((m:R)+2) *
      (4*((m:R)+2)*altColumn R N (m+2) + ((m:R)+1)*altColumn R N m) =
      boundary R N m := by
  induction N with
  | zero => cases m <;> simp [altColumn,boundary,Nat.choose]
  | succ N IH =>
    simp only [altColumn,Finset.sum_range_succ] at *
    linear_combination IH + step (R:=R) N m

theorem unitBelow {p : ℕ} (hp : p.Prime) (i : ℕ) (hi : 0 < i) (h : i < p) :
    IsUnit (i : ZMod (p^2)) :=
  (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide : 0<2)).2 fun hd =>
    (Nat.not_le_of_gt h) (Nat.le_of_dvd hi hd)

theorem columnRecurrence {p : ℕ} (hp : p.Prime) (m : ℕ) (hm : m+2 < p) :
    4*((m:ZMod (p^2))+2)*altColumn (ZMod (p^2)) p (m+2) +
      ((m:ZMod (p^2))+1)*altColumn (ZMod (p^2)) p m = 0 := by
  have u₁ := unitBelow hp (m+1) (by omega) (by omega)
  have u₂ := unitBelow hp (m+2) (by omega) hm
  push_cast at u₁ u₂
  apply ((u₁.pow 2).mul u₂).mul_left_cancel
  rw [mul_zero, telescope]
  have hN : p-1+1=p := by have := hp.pos; omega
  have he := chooseUp (R:=ZMod (p^2)) (p-1) m
  rw [← Nat.cast_add_one, hN] at he
  unfold boundary
  rw [he, mul_pow]
  have hz : (p : ZMod (p^2))^2 = 0 :=
    (Nat.cast_pow (α := ZMod (p^2)) p 2).symm.trans (ZMod.natCast_self (p^2))
  rw [hz]
  ring

theorem alternating_transform {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (j : ℕ) (hj : 2*j < p) :
    (-16 : ZMod (p^2))^j * altColumn (ZMod (p^2)) p (2*j) =
      ((2*j).choose j : ZMod (p^2)) := by
  induction j with
  | zero =>
    have ho := hp.odd_of_ne_two hp2
    simp [altColumn,neg_one_geom_sum,Nat.not_even_iff_odd.mpr ho]
  | succ j IH =>
    have h := columnRecurrence hp (2*j) (by omega)
    have ih := IH (by omega)
    have hc := congrArg (fun t : ℕ => (t : ZMod (p^2))) (Nat.succ_mul_centralBinom_succ j)
    simp only [Nat.centralBinom] at hc
    have hu := unitBelow hp (j+1) (by omega) (by omega)
    push_cast at hu hc h
    apply hu.mul_left_cancel
    rw [show 2*(j+1) = 2*j+2 by omega] at hc ⊢
    rw [pow_succ (-16:ZMod (p^2)) j]
    linear_combination -2*(-16 : ZMod (p^2))^j*h + 2*(2*(j:ZMod (p^2))+1)*ih - hc

end SunAlternating

end

section

/- The inverse square root of the elliptic quartic through the midpoint,
evaluated by raising the quartic to half the odd modulus. -/

namespace SunCoster
open Polynomial Finset
noncomputable section

private theorem unit_index {p i : ℕ} (hp : p.Prime) (hi : 0 < i) (hip : i < p) :
    IsUnit (i : ZMod (p^3)) :=
  (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide : 0<3)).2
    (fun d => hip.not_ge (Nat.le_of_dvd hi d))

private theorem center_choose {p n : ℕ} (hp : p.Prime)
    (hn : 2*(n : ZMod (p^3))+1=0) (k : ℕ) (hk : k<p) :
    (4:ZMod (p^3))^k*(n.choose k : ZMod (p^3))=(-1)^k*(Nat.centralBinom k : ZMod (p^3)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := SunAlternating.chooseAcross (R:=ZMod (p^3)) n k
    have hb := congrArg (fun r : ℕ => (r:ZMod (p^3))) (Nat.succ_mul_centralBinom_succ k)
    push_cast at hb
    have hu : IsUnit ((k:ZMod (p^3))+1) := by exact_mod_cast unit_index hp (i:=k+1) (by omega) hk
    apply hu.mul_left_cancel
    rw [pow_succ (4:ZMod (p^3)) k,pow_succ (-1:ZMod (p^3)) k]
    linear_combination (4*4^k)*h + (-1:ZMod (p^3))^k*hb +
      (-2*(2*(k:ZMod (p^3))+1))*ih (by omega) + (2*4^k*(n.choose k : ZMod (p^3)))*hn

private theorem mirror_choose {p n b : ℕ} (hp : p.Prime)
    (hn : (n:ZMod (p^3)) = -1-(b:ZMod (p^3))) (k : ℕ) (hk : k<p) :
    (n.choose k : ZMod (p^3)) = (-1)^k*((b+k).choose k : ZMod (p^3)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := SunAlternating.chooseAcross (R:=ZMod (p^3)) n k
    have hb := congrArg (fun r : ℕ => (r:ZMod (p^3))) (Nat.add_one_mul_choose_eq (b+k) k)
    push_cast at hb
    have hu : IsUnit ((k:ZMod (p^3))+1) := by exact_mod_cast unit_index hp (i:=k+1) (by omega) hk
    apply hu.mul_left_cancel
    rw [pow_succ (-1:ZMod (p^3)) k,show b+(k+1)=b+k+1 by omega]
    linear_combination h - (-1:ZMod (p^3))^k*hb +
      (-1-(b:ZMod (p^3))-(k:ZMod (p^3)))*ih (by omega) + (n.choose k : ZMod (p^3))*hn

def radicalBase {R : Type*} [CommRing R] (z : R) : R[X] := (1+X)^2 + C (-4*z)*X

private theorem radical_coeff {p m : ℕ} (hp : p.Prime)
    (hm : 2*(m:ZMod (p^3))+1=0) (k : ℕ) (hk : k < p) (hkm : k ≤ m) (z : ZMod (p^3)) :
    ((radicalBase z)^m).coeff k = (-1)^k * aeval z (shiftedLegendre k) := by
  let R := ZMod (p^3)
  let T := fun j : ℕ => C ((m.choose j : R)*(-4*z)^j) * (X^j*(1+X)^(2*(m-j)))
  have ex : (radicalBase z)^m = ∑ j ∈ range (m+1), T j := by
    rw [radicalBase,add_comm,add_pow]
    apply sum_congr rfl
    intro j _
    simp only [T,map_mul,map_pow,C_eq_natCast,mul_pow,pow_mul]
    ring
  rw [ex,finsetSum_coeff]
  trans ∑ j ∈ range (k+1), (T j).coeff k
  · symm
    apply sum_subset (range_mono (by omega))
    intro j _ hj
    simp only [mem_range] at hj
    dsimp only [T]
    rw [coeff_C_mul,coeff_X_pow_mul',if_neg (by omega),mul_zero]
  · simp only [shiftedLegendre,map_sum,map_mul,map_pow,aeval_X,aeval_C,mul_sum]
    apply sum_congr rfl
    intro j hj
    have hjk := mem_range_succ_iff.mp hj
    have hjm : j ≤ m := by omega
    have hcent := center_choose hp hm j (by omega)
    have hm' : ((2*(m-j):ℕ):R) = -1-((2*j:ℕ):R) := by
      dsimp only [R]
      push_cast [hjm]
      linear_combination hm
    have hmir := mirror_choose (p:=p) hp hm' (k-j) (by omega)
    rw [show 2*j+(k-j)=k+j by omega, ← Nat.choose_symm (show k-j≤k+j by omega),
      show k+j-(k-j)=2*j by omega] at hmir
    have hfac := Nat.choose_mul (n:=k+j) (k:=2*j) (s:=j) (by omega)
    rw [show 2*j-j=j by omega, show k+j-j=k by omega] at hfac
    have hf := congrArg (fun i : ℕ => (i:ZMod (p^3))) hfac
    push_cast at hf
    have hsg : (-1:R)^k = (-1)^j*(-1)^(k-j) := by rw [←pow_add,show j+(k-j)=k by omega]
    simp only [T,coeff_C_mul,coeff_X_pow_mul',if_pos hjk,coeff_one_add_X_pow]
    rw [hmir,← Nat.choose_symm (show k≤k+j by omega),show k+j-k=j by omega]
    rw [show -4*z=(-1:R)*4*z by ring,mul_pow,mul_pow]
    calc
      _ = ((4:R)^j*(m.choose j:R)) * ((-1:R)^j*(-1)^(k-j)) *
        z^j * ((k+j).choose (2*j):R) := by ring
      _ = _ := by
        rw [hcent,←hsg]
        simp only [map_neg,map_one,map_natCast,Nat.centralBinom_eq_two_mul_choose]
        linear_combination (-1:R)^j*(-1)^k*z^j*hf

private theorem low_frobenius (p : ℕ) (hp : p.Prime) (G : (ZMod (p^3))[X]) :
    X^p ∣ (1+X*G)^(p^3)-1 := by
  let R := ZMod (p^3)
  let f := fun k : ℕ => (X*G)^k*((p^3).choose k : Polynomial R)
  have e : (1+X*G)^(p^3)-1 = ∑ k ∈ range (p^3), f (k+1) := by
    rw [add_comm,add_pow]
    simp only [one_pow,mul_one]
    change (∑ k ∈ range (p^3+1), f k)-1=_
    rw [sum_range_succ']
    simp [f]
  rw [e]
  apply Finset.dvd_sum
  intro k _
  by_cases hkp : k+1<p
  · have h := Nat.add_one_mul_choose_eq (p^3-1) k
    rw [show (p^3-1)+1=p^3 by have := pow_pos hp.pos 3; omega] at h
    have eh := congrArg (fun n : ℕ => (n:ZMod (p^3))) h
    simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,ZMod.natCast_self,zero_mul] at eh
    have hu : IsUnit ((k:R)+1) := by exact_mod_cast unit_index hp (i:=k+1) (by omega) hkp
    have hc : ((p^3).choose (k+1):R)=0 := hu.mul_right_cancel (by simpa only [zero_mul] using eh.symm)
    have hc' := congrArg (C : R →+* Polynomial R) hc
    simp only [C_eq_natCast,map_zero] at hc'
    simp only [f,hc',mul_zero,dvd_zero]
  · refine ⟨X^(k+1-p)*G^(k+1)*((p^3).choose (k+1) : Polynomial R),?_⟩
    dsimp only [f]
    rw [mul_pow,show (X:Polynomial R)^(k+1)=X^p*X^(k+1-p) by rw [←pow_add]; congr 1; omega]
    ring

private def plainLegendre {R : Type*} [CommRing R] (h : ℕ) (z : R) : R[X] :=
  ∑ k ∈ range (h+1), monomial k ((-1:R)^k*aeval z (shiftedLegendre k))

private theorem plain_square (p : ℕ) (hp : p.Prime) (hp2 : p≠2) (z : ZMod (p^3)) :
    X^(p/2+1) ∣ radicalBase z*(plainLegendre (p/2) z)^2-1 := by
  let h := p/2
  let m := p^3/2
  let S := plainLegendre h z
  let Q := radicalBase z
  have hodd := hp.eq_two_or_odd.resolve_left hp2
  have oddpow : p^3%2=1 := by rw [Nat.pow_mod,hodd]
  have hm : 2*m+1=p^3 := by dsimp only [m]; omega
  have hmr := congrArg (fun n : ℕ => (n:ZMod (p^3))) hm
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,ZMod.natCast_self] at hmr
  have hpP : p≤p^3 := Nat.le_self_pow (by decide) _
  have he : X^(h+1) ∣ Q^m-S := by
    apply X_pow_dvd_iff.2
    intro k hk
    rw [coeff_sub,sub_eq_zero]
    have hp' := hp.two_le
    have src := radical_coeff hp hmr k (by dsimp [h] at hk; omega) (by dsimp [h,m] at hk ⊢; omega) z
    rw [src]
    simp only [S,plainLegendre,finsetSum_coeff,coeff_monomial]
    simp [show k∈range (h+1) from mem_range.mpr hk]
  let G := (2:Polynomial (ZMod (p^3))) + X + C (-4*z)
  have exQ : Q=1+X*G := by dsimp only [Q,radicalBase,G]; ring
  have hh : X^(h+1) ∣ Q^(p^3)-1 :=
    (pow_dvd_pow X (by dsimp [h]; have := hp.two_le; omega)).trans (exQ ▸ low_frobenius p hp G)
  obtain ⟨V,hV⟩ := he
  obtain ⟨U,hU⟩ := hh
  refine ⟨U-Q*V*(Q^m+S),?_⟩
  have heq : Q^(p^3)=(Q^m)^2*Q := calc
    _ = Q^(2*m+1) := congrArg (fun n : ℕ => Q^n) hm.symm
    _ = _ := by rw [pow_succ Q (2*m),show 2*m=m*2 by omega,pow_mul Q m 2]
  rw [heq] at hU
  change Q*S^2-1 = X^(h+1)*(U-Q*V*(Q^m+S))
  linear_combination hU - Q*(Q^m+S)*hV

theorem legendre_radical (p : ℕ) (hp : p.Prime) (hp2 : p≠2) (s z : ZMod (p^3)) :
    X^p ∣ (1-2*C (s*(1-2*z))*X^2+C (s^2)*X^4)*(legendreDifferential (p/2) s z)^2-1 := by
  let W := C (-s)*X^2
  have hQ : (radicalBase z).comp W = 1-2*C (s*(1-2*z))*X^2+C (s^2)*X^4 := by
    simp only [radicalBase,W,add_comp,pow_comp,one_comp,X_comp,mul_comp,C_comp,
      map_mul,map_neg,map_pow,map_sub,map_one,map_ofNat,neg_comp,ofNat_comp]
    ring
  have hS : (plainLegendre (p/2) z).comp W = legendreDifferential (p/2) s z := by
    simp only [plainLegendre,legendreDifferential,←C_mul_X_pow_eq_monomial,
      Polynomial.sum_comp,mul_comp,C_comp,pow_comp,X_comp]
    apply sum_congr rfl
    intro j _
    dsimp only [W]
    rw [mul_pow,← pow_mul,← map_pow]
    rw [show ∀ a b c d : (ZMod (p^3))[X], a*(b*c)=d*c ↔ a*b*c=d*c by intros; rw [mul_assoc]]
    rw [←map_mul]
    congr 2
    rw [show -s=(-1:ZMod (p^3))*s by ring,mul_pow]
    have e : (-1:ZMod (p^3))^j*(-1)^j=1 := by rw [←mul_pow,neg_one_mul,neg_neg,one_pow]
    linear_combination s^j*aeval z (shiftedLegendre j)*e
  obtain ⟨U,hU⟩ := plain_square p hp hp2 z
  have e := congrArg (fun f : (ZMod (p^3))[X] => f.comp W) hU
  simp only [sub_comp,mul_comp,one_comp,pow_comp,X_comp,hQ,hS] at e
  have hodd := hp.eq_two_or_odd.resolve_left hp2
  refine ⟨(C (-s))^(p/2+1)*X*(U.comp W),?_⟩
  rw [e]
  dsimp only [W]
  rw [mul_pow,←pow_mul,show 2*(p/2+1)=p+1 by omega,pow_succ (X : (ZMod (p^3))[X]) p]
  ring

end
end SunCoster

end

section

/- Recovering the normalized invariant differential from its quartic equation. -/

namespace SunCoster
open Polynomial

private theorem cancel_X_power {R : Type*} [CommRing R] {P : R[X]} (hu : IsUnit (P.coeff 0))
    (n : ℕ) (G : R[X]) (hd : X^n ∣ P*G) : X^n ∣ G := by
  induction n generalizing G with
  | zero => simp
  | succ n ih =>
    obtain ⟨T,rfl⟩ := ih G ((pow_dvd_pow X (by omega : n≤n+1)).trans hd)
    have e := X_pow_dvd_iff.1 hd n (by omega)
    rw [show P*(X^n*T)=X^n*(P*T) by ring,coeff_X_pow_mul',if_pos le_rfl,Nat.sub_self,
      coeff_zero_eq_eval_zero,eval_mul,←coeff_zero_eq_eval_zero,←coeff_zero_eq_eval_zero] at e
    have eT : T.coeff 0 = 0 := hu.mul_left_cancel (by simpa only [mul_zero] using e)
    obtain ⟨W,hW⟩ := X_dvd_iff.2 eT
    exact ⟨W,by rw [pow_succ X n,hW,mul_assoc]⟩

/-- A normalized differential pullback follows from the square of the
differential, provided the derivative multiplier has first been removed.
The source differential and its chosen square root both have constant one. -/
theorem pullback_of_quartic {R : Type*} [CommRing R] (n : ℕ) (Q B F V : R[X])
    (π : R) (h2 : IsUnit (2:R)) (hQ : Q.coeff 0=1) (hB : B.coeff 0=1)
    (hF : F.coeff 0=0) (hV : V.coeff 0=1)
    (hr : X^n ∣ Q*B^2-1) (hd : F.derivative=C π*V)
    (hv : X^n ∣ Q*V^2-Q.comp F) : X^n ∣ (B.comp F)*F.derivative-C π*B := by
  obtain ⟨T,hT⟩ := hr
  obtain ⟨S,hS⟩ := hv
  obtain ⟨G,hG⟩ := X_dvd_iff.2 hF
  have hf := congrArg (fun P : R[X] => P.comp F) hT
  simp only [sub_comp,mul_comp,one_comp,pow_comp,X_comp] at hf
  have hpow : F^n=X^n*G^n := by rw [hG,mul_pow]
  rw [hpow] at hf
  let Y := (B.comp F)*V
  have hac : X^n ∣ (Q*(Y+B))*(Y-B) := by
    refine ⟨S*(B.comp F)^2+G^n*(T.comp F)-T,?_⟩
    dsimp only [Y]
    linear_combination (B.comp F)^2*hS+hf-hT
  have h0 : (Q*(Y+B)).coeff 0=2 := by
    rw [coeff_zero_eq_eval_zero,eval_mul,eval_add,←coeff_zero_eq_eval_zero,hQ,one_mul,
      ←coeff_zero_eq_eval_zero B,hB]
    simp only [Y,eval_mul,eval_comp,←coeff_zero_eq_eval_zero F,hF,
      ←coeff_zero_eq_eval_zero B,hB,←coeff_zero_eq_eval_zero V,hV,one_mul,one_add_one_eq_two]
  obtain ⟨W,hW⟩ := cancel_X_power (h0 ▸ h2) n _ hac
  refine ⟨C π*W,?_⟩
  rw [hd]
  dsimp only [Y] at hW
  linear_combination C π*hW

end SunCoster

end

section

namespace SunSplit

theorem represented_ne_two {p : ℕ} {x y : ℤ}
    (h : (p : ℤ) = x^2 + 7*y^2) : p ≠ 2 := by
  rintro rfl
  have hc := congrArg (fun z : ℤ => (z : ZMod 4)) h
  push_cast at hc
  have hn : ∀ a b : ZMod 4, (2 : ZMod 4) ≠ a^2 + 7*b^2 := by decide
  exact hn x y hc

theorem not_dvd_representative {p : ℕ} (hp : p.Prime) (hp7 : p ≠ 7) {x y : ℤ}
    (h : (p : ℤ) = x^2 + 7*y^2) : ¬ (p : ℤ) ∣ x := by
  rintro ⟨z, rfl⟩
  have hp1 : 1 < (p : ℤ) := by exact_mod_cast hp.one_lt
  have hz : z = 0 := by
    by_contra hz
    have z1 : 1 ≤ z^2 := by have := sq_pos_of_ne_zero hz; omega
    nlinarith [mul_nonneg (sq_nonneg (p:ℤ)) (sub_nonneg.mpr z1),
      mul_pos (show (0:ℤ) < p by omega) (show (0:ℤ) < p-1 by omega), sq_nonneg y]
  simp [hz] at h
  have d : (7 : ℤ) ∣ (p : ℤ) := ⟨y^2,h⟩
  have d' : 7 ∣ p := by exact_mod_cast d
  rcases (Nat.dvd_prime hp).mp d' with e | e <;> omega

/-- Central binomial terms above the midpoint vanish to the full power of the prime. -/
theorem truncate_central (p : ℕ) (hp : p.Prime) (r : ℕ) (w : ℕ → ℤ) :
    (∑ k ∈ Finset.range p, w k * ((2*k).choose k : ℤ)^r) ≡
    (∑ k ∈ Finset.range ((p-1)/2+1), w k * ((2*k).choose k : ℤ)^r)
      [ZMOD (p : ℤ)^r] := by
  let a := (p-1)/2+1
  let f := fun k : ℕ => w k * ((2*k).choose k : ℤ)^r
  change (∑ k ∈ Finset.range p, f k) ≡ (∑ k ∈ Finset.range a, f k) [ZMOD (p : ℤ)^r]
  have hp1 := hp.pos
  have hsplit := Finset.sum_range_add f a (p-a)
  rw [show a+(p-a)=p by dsimp [a]; omega] at hsplit
  have hd : (p : ℤ)^r ∣ ∑ k ∈ Finset.range (p-a), f (a+k) := by
    apply Finset.dvd_sum
    intro k hk
    have hk := Finset.mem_range.mp hk
    have hk1 : a+k < p := by dsimp [a] at *; omega
    have hk2 : p ≤ 2*(a+k) := by dsimp [a]; omega
    have hd : p ∣ (2*(a+k)).choose (a+k) := hp.dvd_choose hk1 (by omega) hk2
    have hdZ : (p : ℤ) ∣ ((2*(a+k)).choose (a+k) : ℤ) := by exact_mod_cast hd
    exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hdZ r) _
  rw [hsplit]
  simpa only [add_zero] using hd.modEq_zero_int.add_left (∑ k ∈ Finset.range a, f k)

/-- Specialize the denominator-cleared Sun--Ye lift modulo p³ to the modulus p². -/
theorem reduce_cubic_lift {p : ℕ} (hp : p.Prime) (hp7 : p ≠ 7) {x y S : ℤ}
    (h : (p : ℤ) = x^2 + 7*y^2)
    (lift : (4*x^2)*S ≡ (4*x^2)*(4*x^2-2*(p:ℤ)) - (p:ℤ)^2 [ZMOD (p:ℤ)^3]) :
    S ≡ 4*x^2-2*(p:ℤ) [ZMOD (p:ℤ)^2] := by
  have hodd := represented_ne_two h
  have pi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have htwo : ¬ (p : ℤ) ∣ 2 := by
    intro hd
    have d : p ∣ 2 := by exact_mod_cast hd
    rcases (Nat.dvd_prime Nat.prime_two).mp d with e | e <;> grind [hp.ne_one]
  have cop : IsCoprime ((p:ℤ)^2) (4*x^2) := by
    have a : IsCoprime (p : ℤ) 2 := pi.coprime_iff_not_dvd.mpr htwo
    have b : IsCoprime (p : ℤ) x := pi.coprime_iff_not_dvd.mpr (not_dvd_representative hp hp7 h)
    rw [show (4 : ℤ) = 2^2 by norm_num]
    exact (a.pow_right.mul_right b.pow_right).pow_left
  have d : (p : ℤ)^2 ∣ (p : ℤ)^3 := pow_dvd_pow _ (by decide : 2 ≤ 3)
  have dl := (lift.of_dvd d).dvd
  rw [Int.modEq_iff_dvd]
  apply cop.dvd_of_dvd_mul_left
  obtain ⟨t, ht⟩ := dl
  use t+1
  linear_combination ht

end SunSplit

end

section

namespace SunCMPoint

/-- For either choice of split square root, the unit conjugate has the required
square modulo p². This is the arithmetic conclusion of the CM evaluation. -/
theorem unit_square {p : ℕ} {a b x : ZMod (p^2)} (hu : IsUnit a)
    (hs : a+b=2*x) (hn : a*b=(p:ZMod (p^2))) : a^2 = 4*x^2-2*(p:ZMod (p^2)) := by
  have hz : (p : ZMod (p^2))^2 = 0 :=
    (Nat.cast_pow (α:=ZMod (p^2)) p 2).symm.trans (ZMod.natCast_self (p^2))
  have hb : b^2 = 0 := by
    apply (hu.pow 2).mul_left_cancel
    rw [← mul_pow,hn,hz,mul_zero]
  linear_combination congrArg (fun t : ZMod (p^2) => t^2) hs - 2*hn - hb

/-- An odd prime represented by x²+7y² canonically determines the split root
at which x−yr is a unit. The construction uses only arithmetic modulo p². -/
theorem exists_oriented_root {p : ℕ} (hp : p.Prime) (hp7 : p ≠ 7) {x y : ℤ}
    (hsq : (p : ℤ) = x^2 + 7*y^2) :
    ∃ r : ZMod (p^2), r^2 = -7 ∧ IsUnit ((x:ZMod (p^2))-(y:ZMod (p^2))*r) ∧
        ((x:ZMod (p^2))-(y:ZMod (p^2))*r)^2 = 4*(x:ZMod (p^2))^2-2*(p:ZMod (p^2)) := by
  have hp2 := SunSplit.represented_ne_two hsq
  have pi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hx := SunSplit.not_dvd_representative hp hp7 hsq
  have hy : ¬ (p:ℤ) ∣ y := by
    rintro ⟨t,ht⟩
    apply hx
    apply pi.dvd_of_dvd_pow
    show (p:ℤ) ∣ x^2
    refine ⟨1-7*y*t,?_⟩
    linear_combination -hsq - 7*y*ht
  have unit {v : ℤ} (h : ¬ (p:ℤ) ∣ v) : IsUnit (v : ZMod (p^2)) := by
    apply (ZMod.coe_int_isUnit_iff_isCoprime ..).mpr
    rw [Nat.cast_pow]
    exact (pi.coprime_iff_not_dvd.mpr h).pow_left
  have uy := unit hy
  have htwo : ¬ (p:ℤ) ∣ 2 := by
    intro h
    have d : p ∣ 2 := by exact_mod_cast h
    have := Nat.le_of_dvd (by decide : 0 < 2) d
    have := hp.two_le
    omega
  let A := 2*(x:ZMod (p^2))
  have uA : IsUnit A := by
    exact (show IsUnit (2:ZMod (p^2)) by simpa using unit htwo).mul (unit hx)
  have hAI := ZMod.mul_inv_of_unit A uA
  let e := (p:ZMod (p^2)) * A⁻¹^2
  have hz : (p : ZMod (p^2))^2 = 0 :=
    (Nat.cast_pow (α:=ZMod (p^2)) p 2).symm.trans (ZMod.natCast_self (p^2))
  have he : e^2 = 0 := by dsimp [e]; rw [mul_pow,hz,zero_mul]
  have ue : IsUnit (1-e) :=
    .of_mul_eq_one (1+e) (by linear_combination -he)
  let u := A*(1-e)
  have uu : IsUnit u := uA.mul ue
  have hsum : u + (p:ZMod (p^2))*A⁻¹ = A := by
    dsimp only [u,e]
    linear_combination -(p:ZMod (p^2))*A⁻¹*hAI
  have hprod : u * ((p:ZMod (p^2))*A⁻¹) = p := by
    linear_combination ((p:ZMod (p^2))*A⁻¹)*hsum + (p:ZMod (p^2))*hAI - A⁻¹^2*hz
  have usq := unit_square uu hsum hprod
  let r := ((x:ZMod (p^2))-u)*(y:ZMod (p^2))⁻¹
  have hr : (y:ZMod (p^2))*r = (x:ZMod (p^2))-u := by
    dsimp only [r]
    linear_combination ((x:ZMod (p^2))-u)*ZMod.mul_inv_of_unit (y:ZMod (p^2)) uy
  have hxR := congrArg (fun z : ℤ => (z : ZMod (p^2))) hsq
  push_cast at hxR
  have hr2 : r^2 = -7 := by
    apply (uy.pow 2).mul_left_cancel
    rw [← mul_pow,hr]
    dsimp only [A] at hsum
    linear_combination u*hsum - hprod - hxR
  refine ⟨r,hr2,?_,?_⟩ <;> rw [hr,sub_sub_cancel]
  · exact uu
  · exact usq

end SunCMPoint

end

section

namespace SunClausen

/-- The midpoint product of the two binomial parameters gives a square of
central binomial coefficients modulo the square of an odd prime. -/
theorem midpoint {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {j : ℕ} (hj : j ≤ p/2) :
    (Nat.centralBinom j : ZMod (p^2))^2 =
      (-16 : ZMod (p^2))^j *
        ((p/2).choose j : ZMod (p^2)) * ((p/2+j).choose j : ZMod (p^2)) := by
  let h := p/2
  change _ = (-16 : ZMod (p^2))^j * (h.choose j : ZMod (p^2)) *
    ((h+j).choose j : ZMod (p^2))
  have hodd := hp.odd_of_ne_two hp2
  obtain ⟨d,hd⟩ := hodd
  have hnat : 2*h+1=p := by dsimp [h]; omega
  have hcast : 2*(h : ZMod (p^2))+1=p := by
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
      using congrArg (fun n : ℕ => (n : ZMod (p^2))) hnat
  have hz : (2*(h : ZMod (p^2))+1)^2 = 0 := by
    rw [hcast,← Nat.cast_pow,ZMod.natCast_self]
  induction j with
  | zero => simp
  | succ j ih =>
    have hi := ih (by omega)
    have hu := SunAlternating.unitBelow hp (j+1) (by omega) (by omega)
    push_cast at hu
    apply (hu.pow 2).mul_left_cancel
    have hc := congrArg (fun n : ℕ => (n : ZMod (p^2))) (Nat.succ_mul_centralBinom_succ j)
    have ha := SunAlternating.chooseAcross (R:=ZMod (p^2)) h j
    have hb := congrArg (fun n : ℕ => (n : ZMod (p^2))) (Nat.add_one_mul_choose_eq (h+j) j)
    push_cast at hc hb
    rw [pow_succ (-16 : ZMod (p^2)) j]
    have hr : (-16 : ZMod (p^2))*((h:ZMod (p^2))-j)*((h:ZMod (p^2))+j+1)
        = 4*(2*(j:ZMod (p^2))+1)^2 := by
      linear_combination -4*hz
    calc
      _ = (2*(2*(j:ZMod (p^2))+1)*(Nat.centralBinom j : ZMod (p^2)))^2 := by
        rw [← hc,mul_pow]
      _ = (-16:ZMod (p^2))^j *
          (((h:ZMod (p^2))-j)*(h.choose j : ZMod (p^2))) *
          (((h:ZMod (p^2))+j+1)*((h+j).choose j : ZMod (p^2)))*(-16) := by
        linear_combination 4*(2*(j:ZMod (p^2))+1)^2*hi -
          (-16:ZMod (p^2))^j*(h.choose j : ZMod (p^2))*((h+j).choose j : ZMod (p^2))*hr
      _ = _ := by
        rw [← ha, hb]
        ring

/-- The central cubic sum at the split-prime argument equals the finite
Clausen polynomial evaluated at -16. -/
theorem central_to_clausen {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∑ j ∈ Finset.range (p/2+1), (Nat.centralBinom j : ZMod (p^2))^3 =
    ∑ j ∈ Finset.range (p/2+1), (-16 : ZMod (p^2))^j *
       ((p/2).choose j : ZMod (p^2)) * ((p/2+j).choose j : ZMod (p^2)) *
       (Nat.centralBinom j : ZMod (p^2)) := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [show (Nat.centralBinom j : ZMod (p^2))^3 =
    (Nat.centralBinom j : ZMod (p^2))^2 * Nat.centralBinom j by ring,
    midpoint (j:=j) hp hp2 (by simpa using Finset.mem_range.mp hj)]

end SunClausen

end

section

open Polynomial Finset

namespace SunClausenSquare

noncomputable section

private abbrev P := Polynomial ℤ
private abbrev x : P := X
private abbrev d (f : P) : P := f.derivative
private def theta (f : P) : P := X * d f

private theorem theta_coeff (f : P) (k : ℕ) : (theta f).coeff k = (k:ℤ)*f.coeff k := by
  cases k <;> simp [theta, coeff_derivative, mul_comm]

private def a (n k : ℕ) : ℤ := n.choose k * ((n+k).choose k : ℤ)
private def b (n k : ℕ) : ℤ := a n k * Nat.centralBinom k
private def series (n : ℕ) (f : ℕ → ℤ) : P := ∑ i ∈ range (n+1), monomial i (f i)

private theorem coeff_series {n : ℕ} (f : ℕ → ℤ) (hz : ∀ i, n < i → f i = 0) (k : ℕ) :
    (series n f).coeff k = f k := by
  by_cases hk : k ≤ n
  · simp [series, finsetSum_coeff, coeff_monomial, hk]
  · simp [series, finsetSum_coeff, coeff_monomial, hk, hz k (by omega)]

private theorem a_step (n k : ℕ) :
    ((k:ℤ)+1)^2*a n (k+1) =
    ((n:ℤ)*((n:ℤ)+1) - (k:ℤ)*((k:ℤ)+1))*a n k := by
  by_cases hk : k ≤ n
  · have h₁ := congrArg (fun r : ℕ => (r:ℤ)) (Nat.choose_succ_right_eq n k)
    have h₂ := congrArg (fun r : ℕ => (r:ℤ)) (Nat.add_one_mul_choose_eq (n+k) k)
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_sub hk, Nat.cast_one] at h₁ h₂
    unfold a
    rw [show n+(k+1)=n+k+1 by omega]
    linear_combination ((k:ℤ)+1)*((n+k+1).choose (k+1) : ℤ)*h₁ -
      (((n:ℤ)-(k:ℤ))*(n.choose k : ℤ))*h₂
  · simp [a,Nat.choose_eq_zero_of_lt (show n<k by omega),Nat.choose_eq_zero_of_lt (show n<k+1 by omega)]

private theorem b_step (n k : ℕ) :
    ((k:ℤ)+1)^3*b n (k+1) = 2*(2*(k:ℤ)+1)*
      ((n:ℤ)*((n:ℤ)+1)-(k:ℤ)*((k:ℤ)+1))*b n k := by
  have h := congrArg (fun r : ℕ => (r:ℤ)) (Nat.succ_mul_centralBinom_succ k)
  simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at h
  unfold b
  linear_combination ((k:ℤ)+1) * (Nat.centralBinom (k+1):ℤ) * a_step n k +
    (a n k * ((n:ℤ)*((n:ℤ)+1) - (k:ℤ)*((k:ℤ)+1))) * h

private def leg (n : ℕ) : P := series n (a n)
private def cub (n : ℕ) : P := series n (b n)

private theorem leg_coeff (n k : ℕ) : (leg n).coeff k = a n k :=
  coeff_series _ (by intro i hi; simp [a,Nat.choose_eq_zero_of_lt hi]) k

private theorem cub_coeff (n k : ℕ) : (cub n).coeff k = b n k :=
  coeff_series _ (by intro i hi; simp [a,b,Nat.choose_eq_zero_of_lt hi]) k

private def eigen (n : ℕ) : ℤ := (n:ℤ)*((n:ℤ)+1)

private theorem leg_theta (n : ℕ) :
    theta (theta (leg n)) = x * (C (eigen n)*leg n - theta (leg n) - theta (theta (leg n))) := by
  ext k
  cases k with
  | zero => simp [theta_coeff]
  | succ k =>
    simp only [theta_coeff,coeff_X_mul,coeff_sub,coeff_C_mul,leg_coeff,Nat.cast_succ,eigen]
    linear_combination a_step n k

private theorem cub_theta (n : ℕ) :
    theta (theta (theta (cub n))) = x * (C (2*eigen n)*cub n +
      C (4*eigen n-2)*theta (cub n) - C 6*theta (theta (cub n)) -
      C 4*theta (theta (theta (cub n)))) := by
  ext k
  cases k with
  | zero => simp [theta_coeff]
  | succ k =>
    simp only [theta_coeff,coeff_X_mul,coeff_sub,coeff_add,coeff_C_mul,cub_coeff,Nat.cast_succ,eigen]
    linear_combination b_step n k

private def q : P := x*(1+x)
private def u : P := 1+2*x

private theorem leg_de (n : ℕ) :
    q*d (d (leg n)) + u*d (leg n) - C (eigen n)*leg n = 0 := by
  have h := leg_theta n
  simp [theta,derivative_mul] at h
  rw [eq_intCast (C : ℤ →+* P) (eigen n)]
  unfold q u
  linear_combination h

private theorem cub_de (n : ℕ) :
    x^2*(1+4*x)*d (d (d (cub n))) + 3*x*(1+6*x)*d (d (cub n)) +
      (1+(12-4*C (eigen n))*x)*d (cub n) - 2*C (eigen n)*cub n = 0 := by
  have h := cub_theta n
  simp [theta,derivative_mul,derivative_add] at h
  rw [eq_intCast (C : ℤ →+* P) (eigen n)]
  linear_combination h

private def spec (N : ℤ) (f : P) : P :=
  q^2*d (d (d f)) + 3*q*u*d (d f) + (u^2+(2-4*C N)*q)*d f - 2*C N*u*f

private theorem square_de (n : ℕ) : spec (eigen n) (leg n ^ 2) = 0 := by
  have h := leg_de n
  have hd := congrArg (derivative (R:=ℤ)) h
  simp only [q,u,x,d,derivative_sub,derivative_add,derivative_mul,derivative_X,
    derivative_C,derivative_one,derivative_ofNat,map_zero,zero_add,one_mul,zero_mul,
    mul_one] at hd
  unfold spec q u at *
  simp only [pow_two,derivative_mul,derivative_add]
  linear_combination 2*(leg n)*(X*(1+X))*hd +
    (6*(X*(1+X))*d (leg n) + 2*(1+2*X)*leg n)*h

private theorem composition_de (n : ℕ) : spec (eigen n) ((cub n).comp q) = 0 := by
  have h := congrArg (fun f : P => f.comp q) (cub_de n)
  simp only [add_comp,mul_comp,sub_comp,pow_comp,C_comp,X_comp,one_comp,
    ofNat_comp,zero_comp] at h
  simp only [spec,d,derivative_comp,derivative_mul,derivative_add,
    q,u,derivative_X,derivative_one,zero_add,zero_mul,
    one_mul,add_zero,mul_one] at h ⊢
  linear_combination (1+2*X)*h

private def kOp (N : ℤ) (f : P) := C 2 * theta (theta (theta f)) +
  C 3 * theta (theta f) + C (1-4*N)*theta f - C (2*N)*f
private def jOp (N : ℤ) (f : P) := theta (theta (theta f)) +
  C 3 * theta (theta f) + C (2-4*N)*theta f - C (4*N)*f

private theorem spec_theta (N : ℤ) (f : P) (h : spec N f = 0) :
    theta (theta (theta f)) + x*(kOp N f + x*jOp N f) = 0 := by
  simp only [theta,kOp,jOp,d,derivative_add,derivative_mul,derivative_X,one_mul,
    C_ofNat,map_sub,map_mul,map_one]
  unfold spec q u at h
  linear_combination x*h

private theorem coeff_kOp {N : ℤ} {f g : P} {k : ℕ} (he : f.coeff k = g.coeff k) :
    (kOp N f).coeff k = (kOp N g).coeff k := by
  simp only [kOp,coeff_add,coeff_sub,coeff_C_mul,theta_coeff,he]

private theorem coeff_jOp {N : ℤ} {f g : P} {k : ℕ} (he : f.coeff k = g.coeff k) :
    (jOp N f).coeff k = (jOp N g).coeff k := by
  simp only [jOp,coeff_add,coeff_sub,coeff_C_mul,theta_coeff,he]

private theorem unique_spec (N : ℤ) {f g : P} (hf : spec N f = 0) (hg : spec N g = 0)
    (h0 : f.coeff 0 = g.coeff 0) : f = g := by
  ext k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => exact h0
    | succ j =>
      have h := congrArg (fun a : P => a.coeff (j+1)) ((spec_theta N f hf).trans (spec_theta N g hg).symm)
      simp only [coeff_add,theta_coeff,coeff_X_mul,Nat.cast_succ] at h
      have hk := coeff_kOp (N:=N) (ih j (by omega))
      have hj : (x*jOp N f).coeff j = (x*jOp N g).coeff j := by
        cases j with
        | zero => simp
        | succ t => rw [coeff_X_mul, coeff_X_mul]; exact coeff_jOp (ih t (by omega))
      rw [hk,hj] at h
      have hn : (j:ℤ)+1 ≠ 0 := by positivity
      exact mul_left_cancel₀ hn (mul_left_cancel₀ hn (mul_left_cancel₀ hn (add_right_cancel h)))

theorem square_identity (n : ℕ) : (leg n)^2 = (cub n).comp q := by
  apply unique_spec (eigen n) (square_de n) (composition_de n)
  simp only [coeff_zero_eq_eval_zero, eval_pow, eval_comp, q, eval_mul, eval_X, zero_mul]
  rw [← coeff_zero_eq_eval_zero, ← coeff_zero_eq_eval_zero,leg_coeff,cub_coeff]
  simp [a,b]

/-- The terminating Clausen square identity evaluated in any commutative ring. -/
theorem terminating {R : Type*} [CommRing R] (n : ℕ) (t : R) :
    (∑ k ∈ range (n+1), (n.choose k : R)*((n+k).choose k : R)*t^k)^2 =
    ∑ k ∈ range (n+1), (n.choose k : R)*((n+k).choose k : R)*
      (Nat.centralBinom k:R)*(t*(1+t))^k := by
  have h := congrArg (fun f : P => f.eval₂ (Int.castRingHom R) t) (square_identity n)
  simpa only [leg,cub,series,q,eval₂_pow,eval₂_comp,eval₂_mul,eval₂_add,eval₂_one,
    eval₂_X,eval₂_finsetSum,eval₂_monomial,a,b,Int.coe_castRingHom,Int.cast_mul,
    Int.cast_natCast] using h

end
end SunClausenSquare

end

section

open Finset Polynomial

namespace SunClausenSquare

/-- Reduction modulo the square of an odd prime to the square of a Legendre value. -/
theorem central_square {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (t : ZMod (p^2)) (ht : t*(1+t) = -16) :
    ∑ j ∈ range (p/2+1), (Nat.centralBinom j : ZMod (p^2))^3 =
      ((shiftedLegendre (p/2)).eval₂ (Int.castRingHom (ZMod (p^2))) (-t))^2 := by
  let n := p/2
  have hs := terminating n t
  rw [ht] at hs
  rw [SunClausen.central_to_clausen hp hp2]
  have he : (shiftedLegendre n).eval₂ (Int.castRingHom (ZMod (p^2))) (-t) =
      ∑ k ∈ range (n+1), (n.choose k : ZMod (p^2))*((n+k).choose k : ZMod (p^2))*t^k := by
    simp only [shiftedLegendre,eval₂_finsetSum,eval₂_mul,eval₂_C,eval₂_pow,eval₂_X,
      Int.coe_castRingHom,Int.cast_mul,Int.cast_pow,Int.cast_neg,Int.cast_one,Int.cast_natCast]
    apply sum_congr rfl
    intro k _
    rw [Nat.choose_symm_add]
    rw [show (-t)^k = (-1)^k*t^k by rw [←mul_pow]; simp]
    have h : (-1 : ZMod (p^2))^k * (-1)^k = 1 := by rw [←mul_pow]; simp
    linear_combination ((n+k).choose k : ZMod (p^2))*(n.choose k : ZMod (p^2))*t^k*h
  change _ = ((shiftedLegendre n).eval₂ (Int.castRingHom (ZMod (p^2))) (-t))^2
  rw [he, hs]
  apply sum_congr rfl
  intro j _
  ring

/-- At any split square root of minus seven the transformed series is the
square of the Legendre polynomial evaluated at three times that root. -/
theorem central_square_at_root {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (r : ZMod (p^2)) (hr : r^2 = -7) :
    ∑ j ∈ range (p/2+1), (Nat.centralBinom j : ZMod (p^2))^3 =
    ((shiftedLegendre (p/2)).eval₂ (Int.castRingHom (ZMod (p^2)))
      (-((3*r-1)*(2 : ZMod (p^2))⁻¹)))^2 := by
  let t := (3*r-1)*(2 : ZMod (p^2))⁻¹
  have u : IsUnit (2 : ZMod (p^2)) := by
    simpa using SunAlternating.unitBelow hp 2 (by decide) (by have := hp.two_le; omega)
  have ht : 2*t=3*r-1 := by
    dsimp only [t]
    rw [mul_left_comm, ZMod.mul_inv_of_unit _ u, mul_one]
  apply central_square hp hp2 t
  apply (u.pow 2).mul_left_cancel
  linear_combination (2*t+3*r+1)*ht + 9*hr

end SunClausenSquare

end

section

namespace SunAlternating

theorem reorder (R : Type*) [CommRing R] (p : ℕ) (hp : 0 < p) (w : ℕ → R) :
    ∑ n ∈ Finset.range p, w n * (OeisA179537.a n : R) =
      ∑ j ∈ Finset.range ((p-1)/2+1), ((-16:R)^j * ((2*j).choose j : R)^2) *
        ∑ n ∈ Finset.range p, w n * (n.choose (2*j) : R)^2 := by
  let f (j : ℕ) : R := (-16:R)^j * ((2*j).choose j : R)^2
  have row (n : ℕ) (hn : n < p) : (OeisA179537.a n : R) =
      ∑ j ∈ Finset.range p, f j * (n.choose (2*j) : R)^2 := by
    unfold OeisA179537.a
    push_cast
    calc
      _ = ∑ j ∈ Finset.range (n+1), f j * (n.choose (2*j) : R)^2 := by
        apply Finset.sum_congr rfl
        intro j _
        have h := Nat.choose_mul (n:=n) (k:=2*j) (s:=j) (by omega)
        rw [show 2*j-j=j by omega] at h
        have e := congrArg (fun t : ℕ => (t:R)) h
        push_cast at e
        dsimp only [f]
        linear_combination -(-16:R)^j * congrArg (fun t : R => t^2) e
      _ = _ := by
        apply Finset.sum_subset (Finset.range_mono (by omega))
        intro j _ hj
        simp only [Finset.mem_range] at hj
        simp [Nat.choose_eq_zero_of_lt (show n < 2*j by omega)]
  calc
    _ = ∑ n ∈ Finset.range p, ∑ j ∈ Finset.range p,
        w n * (f j * (n.choose (2*j) : R)^2) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [row n (Finset.mem_range.mp hn), Finset.mul_sum]
    _ = ∑ j ∈ Finset.range p, ∑ n ∈ Finset.range p,
        w n * (f j * (n.choose (2*j) : R)^2) := Finset.sum_comm
    _ = ∑ j ∈ Finset.range ((p-1)/2+1), ∑ n ∈ Finset.range p,
        w n * (f j * (n.choose (2*j) : R)^2) := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro j _ hj
      simp only [Finset.mem_range] at hj
      apply Finset.sum_eq_zero
      intro n hn
      simp only [Finset.mem_range] at hn
      simp [Nat.choose_eq_zero_of_lt (show n < 2*j by omega)]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      dsimp only [f]
      ring

end SunAlternating

end

section

namespace SunWeightedColumn

open SunAlternating

def column (R : Type*) [CommRing R] (N m : ℕ) : R :=
  ∑ n ∈ Finset.range N, (-1:R)^n * (2*(n:R)-m+1) * (n.choose m : R)^2

private def cert {R : Type*} [CommRing R] (n m : R) : R :=
  4*n^3 - (14*m+20)*n^2 + (16*m^2+44*m+28)*n - (5*m^3+18*m^2+18*m+4)

private def boundary (R : Type*) [CommRing R] (n m : ℕ) : R :=
  -(-1:R)^n * (((n:R)-m)*(n.choose m : R))^2 * cert (n:R) (m:R)

variable {R : Type*} [CommRing R]

private theorem step (n m : ℕ) :
    ((m:R)+1)*((m:R)+2)^2 *
      (4*((m:R)+1)*((-1:R)^n*(2*(n:R)-((m:R)+2)+1)*(n.choose (m+2):R)^2)
        + ((m:R)+2)*((-1:R)^n*(2*(n:R)-m+1)*(n.choose m:R)^2)) =
      boundary R (n+1) m - boundary R n m := by
  have c₁ := chooseAcross (R:=R) n m
  have c₂ := chooseAcross (R:=R) n (m+1)
  push_cast at c₂
  have c : ((m:R)+1)*((m:R)+2)*(n.choose (m+2):R) =
      ((n:R)-m-1)*((n:R)-m)*(n.choose m:R) := by
    linear_combination ((m:R)+1)*c₂ + ((n:R)-m-1)*c₁
  unfold boundary
  push_cast
  rw [chooseUp, pow_succ (a := (-1:R))]
  unfold cert
  linear_combination 4*(-1:R)^n*(2*(n:R)-m-1)*congrArg (fun t : R => t^2) c

private theorem telescope (N m : ℕ) :
    ((m:R)+1)*((m:R)+2)^2 *
      (4*((m:R)+1)*column R N (m+2) + ((m:R)+2)*column R N m) =
      boundary R N m := by
  induction N with
  | zero => cases m <;> simp [column,boundary,Nat.choose]
  | succ N ih =>
    simp only [column,Finset.sum_range_succ] at *
    have h := step (R:=R) N m
    push_cast at ih ⊢
    linear_combination ih + h

theorem recurrence {p : ℕ} (hp : p.Prime) (m : ℕ) (hm : m+2 < p) :
    4*((m:ZMod (p^2))+1)*column (ZMod (p^2)) p (m+2) +
      ((m:ZMod (p^2))+2)*column (ZMod (p^2)) p m = 0 := by
  have u₁ := unitBelow hp (m+1) (by omega) (by omega)
  have u₂ := unitBelow hp (m+2) (by omega) hm
  push_cast at u₁ u₂
  apply (u₁.mul (u₂.pow 2)).mul_left_cancel
  rw [mul_zero, telescope]
  have hN : p-1+1=p := by have := hp.pos; omega
  have he := chooseUp (R:=ZMod (p^2)) (p-1) m
  rw [← Nat.cast_add_one, hN] at he
  unfold boundary
  rw [he, mul_pow]
  have hz : (p : ZMod (p^2))^2 = 0 :=
    (Nat.cast_pow (α := ZMod (p^2)) p 2).symm.trans (ZMod.natCast_self (p^2))
  rw [hz]
  ring

private theorem column_zero (N : ℕ) :
    column R N 0 = -(-1:R)^N * N := by
  induction N with
  | zero => simp [column]
  | succ k ih =>
    unfold column at *
    rw [Finset.sum_range_succ,ih]
    simp only [Nat.cast_succ, pow_succ, Nat.cast_zero, sub_zero, Nat.choose_zero_right,
      Nat.cast_one, one_pow, mul_one]
    ring

theorem transform {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (j : ℕ) (hj : 2*j < p) :
    ((2*j).choose j : ZMod (p^2))*column (ZMod (p^2)) p (2*j) =
      (p:ZMod (p^2))*(-1)^j := by
  induction j with
  | zero => simp [column_zero,(hp.odd_of_ne_two hp2).neg_one_pow]
  | succ j ih =>
    have h := recurrence hp (2*j) (by omega)
    have prev := ih (by omega)
    have hc := congrArg (fun t : ℕ => (t : ZMod (p^2))) (Nat.succ_mul_centralBinom_succ j)
    simp only [Nat.centralBinom] at hc
    have hu := unitBelow hp (j+1) (by omega) (by omega)
    have htwo := unitBelow hp 2 (by omega) (by have := hp.two_le; omega)
    push_cast at hu htwo hc h
    apply (htwo.mul hu).mul_left_cancel
    rw [show 2*(j+1)=2*j+2 by omega] at *
    rw [pow_succ (-1 : ZMod (p^2))]
    linear_combination ((2*j).choose j : ZMod (p^2))*h +
      2*column (ZMod (p^2)) p (2*j+2)*hc - 2*((j:ZMod (p^2))+1)*prev

end SunWeightedColumn

end

section

namespace SunCombination
open Finset SunAlternating
theorem alternating_reduction {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (∑ n ∈ range p, (-1:ℤ)^n*OeisA179537.a n) ≡
      (∑ j ∈ range ((p-1)/2+1), ((2*j).choose j : ℤ)^3) [ZMOD (p:ℤ)^2] := by
  rw [← Nat.cast_pow, ← ZMod.intCast_eq_intCast_iff]
  push_cast
  rw [reorder (ZMod (p^2)) p hp.pos (fun n => (-1:ZMod (p^2))^n)]
  apply sum_congr rfl
  intro j hj
  rw [mem_range] at hj
  have h := alternating_transform hp hp2 j (by have := hp.pos; omega)
  unfold altColumn at h
  linear_combination ((2*j).choose j : ZMod (p^2))^2*h

end SunCombination

end

section

namespace SplitSeven

theorem legendre_neg_seven (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    letI : Fact p.Prime := ⟨hp⟩
    letI : Fact (Nat.Prime 7) := ⟨by decide⟩
    legendreSym p (-7) = legendreSym 7 p := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have qr := legendreSym.quadratic_reciprocity' (p := p) (q := 7) hp2 (by decide)
  rw [legendreSym.at_neg hp2, ZMod.χ₄_eq_neg_one_pow (hp.mod_two_eq_one_iff_ne_two.mpr hp2)]
  rw [qr]
  rw [mul_comm (p/2) (7/2), pow_mul]
  norm_num

theorem exists_sqrt_neg_seven (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (h7 : p % 7 ∈ ({1, 2, 4} : Finset ℕ)) :
    ∃ r : ZMod p, r^2 = -7 := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hp7 : p ≠ 7 := by intro h; subst p; norm_num at h7
  have he : legendreSym 7 (p : ℤ) = 1 := by
    rw [legendreSym.mod]
    rw [← Int.natCast_mod]
    simp only [Finset.mem_insert, Finset.mem_singleton] at h7
    rcases h7 with h|h|h <;> rw [h] <;> decide
  have hs := (legendre_neg_seven p hp hp2).trans he
  have hn : ((-7 : ℤ) : ZMod p) ≠ 0 := by
    have hh := ZMod.prime_ne_zero p 7 hp7
    push_cast
    simpa using hh
  obtain ⟨r, hr⟩ := (legendreSym.eq_one_iff p hn).mp hs
  exact ⟨r, by simpa [pow_two] using hr.symm⟩

/-- An explicit lift of a square root of −7 modulo p to a unit square root modulo p³. -/
theorem exists_unit_sqrt_neg_seven (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (h7 : p % 7 ∈ ({1, 2, 4} : Finset ℕ)) :
    ∃ s : ZMod (p^3), s^2 = -7 ∧ IsUnit s := by
  let : Fact p.Prime := ⟨hp⟩
  have hp7 : p ≠ 7 := by intro h; subst p; norm_num at h7
  have nd7 : ¬ p ∣ 7 := fun h => hp7 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h)
  have nd2 : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h)
  have u7 : IsUnit (7 : ZMod (p^3)) := (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide : 0 < 3)).mpr nd7
  have u2 : IsUnit (2 : ZMod (p^3)) := (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide : 0 < 3)).mpr nd2
  have ud : IsUnit (392 : ZMod (p^3)) := by
    convert (u2.pow 3).mul (u7.pow 2) using 1
    ring
  obtain ⟨r,hr⟩ := exists_sqrt_neg_seven p hp hp2 h7
  let b : ℤ := r.val
  have hb : (b : ZMod p) = r := by simp [b]
  have hdiv : (p : ℤ) ∣ b^2+7 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    push_cast
    rw [hb,hr]; ring
  obtain ⟨k, hk⟩ := hdiv
  let a : ZMod (p^3) := b
  let e := a^2+7
  have heq : e = (p : ZMod (p^3)) * (k : ZMod (p^3)) := by
    have h := congrArg (fun z : ℤ => (z : ZMod (p^3))) hk
    simpa only [e, a, Int.cast_add, Int.cast_pow, Int.cast_ofNat, Int.cast_mul, Int.cast_natCast] using h
  have hc : (p : ZMod (p ^ 3))^3 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have hn : e^3 = 0 := by rw [heq,mul_pow,hc,zero_mul]
  let t := 392 + 28*e + 3*e^2
  let s := a*t*(392 : ZMod (p^3))⁻¹
  have hs : s*392 = a*t := by
    dsimp only [s]; rw [mul_assoc,ZMod.inv_mul_of_unit _ ud,mul_one]
  have hab : a^2 = e-7 := by dsimp only [e]; ring
  have halg : (a*t)^2 + 7 * 392^2 = 0 := by
    calc
      (a*t)^2 + 7*392^2 = e^3 * (1960+105*e+9*e^2) := by rw [mul_pow,hab]; dsimp only [t]; ring
      _ = 0 := by rw [hn,zero_mul]
  have hsq : s^2 = -7 := by
    apply (ud.pow 2).mul_left_cancel
    linear_combination halg + (s*392+a*t)*hs
  refine ⟨s,hsq,?_⟩
  apply isUnit_of_mul_isUnit_left (y := s)
  rw [← pow_two,hsq]
  exact u7.neg



/-- A positive integral form of discriminant −7 is integrally equivalent to the norm
form of the integers of ℚ(√−7). Only preservation of the represented value is needed. -/
private theorem reduce_form (a b c x y : ℤ) (ha : 0 < a)
    (hd : 4*a*c = b^2+7) :
    ∃ u v : ℤ, a*x^2+b*x*y+c*y^2 = u^2+u*v+2*v^2 := by
  let t := (b+a) / (2*a)
  let B := b-2*a*t
  let C := a*t^2-b*t+c
  let X := x+t*y
  have dd : 4*a*C = B^2+7 := by
    dsimp [C,B]; linear_combination hd
  have pos : 0 < 2*a := by omega
  have rem := Int.emod_add_mul_ediv (b+a) (2*a)
  have reml := Int.emod_nonneg (b+a) (by omega : 2*a ≠ 0)
  have remu := Int.emod_lt_of_pos (b+a) pos
  have hB : -a ≤ B ∧ B < a := by
    change -a ≤ b - 2*a*((b+a)/(2*a)) ∧ b - 2*a*((b+a)/(2*a)) < a
    constructor <;> linarith
  have hpos : 0 < C := by
    by_contra! hh
    nlinarith [mul_nonpos_of_nonneg_of_nonpos ha.le hh, sq_nonneg B]
  have eqv : a*x^2+b*x*y+c*y^2 = a*X^2+B*X*y+C*y^2 := by
    dsimp [X,B,C]; ring
  by_cases h : C < a
  · obtain ⟨u,v,huv⟩ := reduce_form C B a y X hpos (by linear_combination dd)
    refine ⟨u,v,?_⟩
    rw [eqv,← huv]; ring
  · have hbnd : B^2 ≤ a^2 := by
      nlinarith [mul_nonneg (show 0 ≤ a+B by omega) (show 0 ≤ a-B by omega)]
    have hA : a = 1 := by
      by_contra hne
      have : 2 ≤ a := by omega
      nlinarith [mul_nonneg (show 0 ≤ C-a by omega) ha.le,
        mul_nonneg (show 0 ≤ a-2 by omega) (show 0 ≤ a+2 by omega)]
    have hbc : B = -1 ∧ C = 2 := by
      rw [hA] at dd hB
      rcases (show B = -1 ∨ B = 0 by omega) with hx|hx <;> rw [hx] at dd <;> norm_num at dd <;> omega
    refine ⟨X,-y,?_⟩
    rw [eqv,hA,hbc.1,hbc.2]; ring
termination_by a.toNat
decreasing_by exact (Int.toNat_lt_toNat ha).mpr h

theorem represented_of_sqrt_neg_seven (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hs : ∃ r : ZMod p, r^2 = -7) : ∃ x y : ℤ, (p : ℤ) = x^2+7*y^2 := by
  let : Fact p.Prime := ⟨hp⟩
  have htwo : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
  obtain ⟨r,hr⟩ := hs
  let z : ZMod p := (r-1)/2
  have hz : z^2+z+2=0 := by
    dsimp [z]
    field_simp
    linear_combination hr
  let b : ℤ := z.val
  have hb : (b : ZMod p) = z := by simp [b]
  obtain ⟨c,hc⟩ : (p : ℤ) ∣ b^2+b+2 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    push_cast; rwa [hb]
  obtain ⟨u,v,huv⟩ := reduce_form (p : ℤ) (2*b+1) c 1 0 (by exact_mod_cast hp.pos)
    (by linear_combination -4*hc)
  norm_num at huv
  have hpodd := hp.mod_two_eq_one_iff_ne_two.mpr hp2
  have heven : Even v := by
    by_contra hh
    obtain ⟨k,hk⟩ := Int.not_even_iff_odd.mp hh
    rcases Int.even_or_odd u with ⟨m,hm⟩|⟨m,hm⟩ <;> rw [hk,hm] at huv <;> ring_nf at huv <;> omega
  obtain ⟨y,hy⟩ := heven
  refine ⟨u+y,y,?_⟩
  rw [huv, hy]; ring



theorem x_nonzero_mod (p : ℕ) (hp : p.Prime) (hp7 : p ≠ 7) (x y : ℤ)
    (hxy : (p : ℤ) = x^2+7*y^2) : (x : ZMod p) ≠ 0 := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  intro hx
  have hr := congrArg (fun v : ℤ => (v : ZMod p)) hxy
  have hy : (y : ZMod p) = 0 := by
    norm_cast at hr
    push_cast at hr
    have hn : (7 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 7 hp7
    simpa [hx, hn] using hr.symm
  obtain ⟨a,ha⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hx
  obtain ⟨b,hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hy
  have h : (p : ℤ)*1 = (p : ℤ)*((p : ℤ)*(a^2+7*b^2)) := by
    calc
      (p : ℤ)*1 = x^2+7*y^2 := by simpa using hxy
      _ = _ := by rw [ha,hb]; ring
  have hdiv : (p : ℤ) ∣ 1 := ⟨_,mul_left_cancel₀ (by exact_mod_cast hp.ne_zero) h⟩
  exact hp.not_dvd_one (by exact_mod_cast hdiv)

theorem exists_unit_branch (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hp7 : p ≠ 7)
    (s : ZMod (p^3)) (x y : ℤ) (hxy : (p : ℤ) = x^2+7*y^2) :
    ∃ v : ℤ, (p : ℤ) = x^2+7*v^2 ∧ IsUnit ((x : ZMod (p^3)) + (v : ZMod (p^3))*s) := by
  let : Fact p.Prime := ⟨hp⟩
  let π := ZMod.castHom (show p ∣ p^3 from dvd_pow_self _ (by decide)) (ZMod p)
  have hunit (z : ZMod (p^3)) (hz : π z ≠ 0) : IsUnit z := by
    rw [← ZMod.natCast_zmod_val z] at hz ⊢
    rw [map_natCast] at hz
    apply (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide : 0 < 3)).mpr
    exact fun h => hz ((ZMod.natCast_eq_zero_iff _ _).mpr h)
  by_cases h : π ((x : ZMod (p^3)) + (y : ZMod (p^3))*s) = 0
  · refine ⟨-y, by rw [neg_sq]; exact hxy, hunit _ ?_⟩
    intro h'
    have hx := x_nonzero_mod p hp hp7 x y hxy
    have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
    apply mul_ne_zero h2 hx
    push_cast at h h'
    simp only [map_add,map_mul,map_neg,map_intCast] at h h'
    linear_combination h + h'
  · exact ⟨y,hxy,hunit _ h⟩

/-- The split residue hypothesis supplies all algebraic parameters required by the
two CM evaluations, with a consistent choice of the unit prime above p. -/
theorem exists_cm_data (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (h7 : p % 7 ∈ ({1, 2, 4} : Finset ℕ)) :
    ∃ (s : ZMod (p^3)) (x y : ℤ), s^2 = -7 ∧ IsUnit s ∧
      (p : ℤ) = x^2 + 7*y^2 ∧ IsUnit ((x : ZMod (p^3)) + (y : ZMod (p^3))*s) := by
  obtain ⟨s,hs,hsu⟩ := exists_unit_sqrt_neg_seven p hp hp2 h7
  obtain ⟨x,y,hxy⟩ := represented_of_sqrt_neg_seven p hp hp2 (exists_sqrt_neg_seven p hp hp2 h7)
  have hp7 : p ≠ 7 := by intro h; subst p; norm_num at h7
  obtain ⟨v,hv,hvu⟩ := exists_unit_branch p hp hp2 hp7 s x y hxy
  exact ⟨s,x,v,hs,hsu,hv,hvu⟩

/-- The two nontrivial roots of the singular-modulus equation. The identity is stated
with denominators cleared so that it applies in any integral domain. -/
theorem cm_argument_pair {K : Type*} [CommRing K] [IsDomain K] (t s : K)
    (hs : s^2 = -7) (ht : (16*t-1)^3 = 3375*t^2) (ht1 : t ≠ 1) :
    8192*t = 47+45*s ∨ 8192*t = 47-45*s := by
  have hf : (t-1)*(4096*t^2-47*t+1) = 0 := by linear_combination ht
  have hq := (mul_eq_zero.mp hf).resolve_left (sub_ne_zero.mpr ht1)
  have hc : (8192*t-47-45*s)*(8192*t-47+45*s) = 0 := by
    linear_combination 16384*hq - 2025*hs
  rcases mul_eq_zero.mp hc with h|h
  · left; linear_combination h
  · right; linear_combination h

end SplitSeven

end

section

/- Reduction of the split-prime target to the finite rational Frobenius
lift at its discriminant −7 Legendre chart. -/

namespace SunCoster
open Polynomial

noncomputable section

def chart {p : ℕ} (s : ZMod (p^3)) : ZMod (p^3) :=
  -((3*s-1)*(2:ZMod (p^3))⁻¹)

/-- The hypotheses asserted by the algebraic construction of the degree-p
isogeny, in the chart t=x/y and to the finite precision used in the proof. -/
def FrobeniusLiftsAtSeven : Prop :=
  ∀ (p : ℕ), p.Prime → p≠2 → p≠7 → ∀ (x y : ℤ), (p:ℤ)=x^2+7*y^2 →
    ∀ s : ZMod (p^3), s^2= -7 → IsUnit s → IsUnit ((x:ZMod (p^3))+(y:ZMod (p^3))*s) →
    ∃ (u : ZMod (p^3)) (A D : (ZMod (p^3))[X]),
      A.natDegree<p ∧ D.coeff 0=0 ∧ u^2=(s^(p/2))^2 ∧
      let B := legendreDifferential (p/2) s (chart s)
      let F := frobeniusPolynomial p u A D
      X^p ∣ (B.comp F)*F.derivative - C ((x:ZMod (p^3))-(y:ZMod (p^3))*s)*B

theorem from_frobenius_lifts (lifts : FrobeniusLiftsAtSeven) :
    type_of% @OeisA179537.conjecture1 := by
  intro p hpF hp7 hleg x y hxy
  have hp : p.Prime := hpF.out
  have hp2 := SunSplit.represented_ne_two hxy
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have h7 : p%7 ∈ ({1,2,4} : Finset ℕ) := by
    have he := (legendreSym.mod 7 (p:ℤ)).symm.trans hleg
    rw [← Int.natCast_mod] at he
    have tbl : ∀ a : Fin 7, legendreSym 7 (a.val : ℤ)=1 →
        a.val ∈ ({1,2,4} : Finset ℕ) := by decide
    exact tbl ⟨p%7,Nat.mod_lt _ (by decide)⟩ he
  obtain ⟨s,hs,hsu⟩ := SplitSeven.exists_unit_sqrt_neg_seven p hp hp2 h7
  obtain ⟨v,hv,hvu⟩ := SplitSeven.exists_unit_branch p hp hp2 hp7 s x y hxy
  obtain ⟨u,A,D,hA,hD,hu,hF⟩ := lifts p hp hp2 hp7 x v hv s hs hsu hvu
  let red := reduceSquare p
  let ξ := (x:ZMod (p^3))+(v:ZMod (p^3))*s
  let π := (x:ZMod (p^3))-(v:ZMod (p^3))*s
  let B := legendreDifferential (p/2) s (chart s)
  let F := frobeniusPolynomial p u A D
  have hn : π*ξ = (p:ZMod (p^3)) := by
    have hh := congrArg (fun j : ℤ => (j:ZMod (p^3))) hv
    push_cast at hh
    dsimp only [π,ξ]
    linear_combination -hh - (v:ZMod (p^3))^2*hs
  have hq : ((B.comp F)*F.derivative).coeff (p-1)=π*B.coeff (p-1) := by
    have H := X_pow_dvd_iff.mp hF (p-1) (by have := hp.pos; omega)
    simpa only [coeff_sub,coeff_C_mul,sub_eq_zero] using H
  have ht := legendre_square_of_pullback p hp hp2 s (chart s) u π ξ hsu hu hn A D hA hD hq
  have h₂ : IsUnit (2:ZMod (p^3)) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide : 0<3)).2
      (fun d => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 d))
  have h₂' : IsUnit (2:ZMod (p^2)) := by simpa only [map_ofNat] using h₂.map red
  have hInv : red (2:ZMod (p^3))⁻¹ = (2:ZMod (p^2))⁻¹ := by
    apply h₂'.mul_left_cancel
    have e := congrArg red (ZMod.mul_inv_of_unit _ h₂)
    simpa only [map_mul,map_ofNat,map_one,ZMod.mul_inv_of_unit _ h₂'] using e
  have hchart : red (chart s) = -((3*(red s)-1)*(2:ZMod (p^2))⁻¹) := by
    simp only [chart,map_neg,map_mul,map_sub,map_ofNat,map_one,hInv]
  have hsr : (red s)^2 = -7 := by simpa only [map_pow,map_neg,map_ofNat] using congrArg red hs
  have hsq : (red ξ)^2=4*(x:ZMod (p^2))^2-2*(p:ZMod (p^2)) := by
    apply SunCMPoint.unit_square (hvu.map red) (b:=red π)
    · dsimp only [ξ,π]; simp only [map_add,map_sub,map_mul,map_intCast]; ring
    · change red ξ * red π = _
      rw [mul_comm,← map_mul,hn,map_natCast]
  apply (SunCombination.alternating_reduction hp hp2).trans
  rw [← Nat.cast_pow, ← ZMod.intCast_eq_intCast_iff]
  push_cast
  have hcl := SunClausenSquare.central_square_at_root hp hp2 (red s) hsr
  change (aeval (red (chart s)) (shiftedLegendre (p/2)))^2=(red ξ)^2 at ht
  rw [hchart] at ht
  have ho := hp.mod_two_eq_one_iff_ne_two.mpr hp2
  simpa only [Nat.centralBinom,show (p-1)/2=p/2 by omega] using hcl.trans (ht.trans hsq)

end
end SunCoster

end

section

/- An algebraic Frobenius lift on the discriminant −7 Jacobi quartic
suffices for the split-prime supercongruence. -/

namespace SunCoster
open Polynomial
noncomputable section

def quartic (R : Type*) [CommRing R] : R[X] := 1+42*X^2-7*X^4

/-- The rational map F and its normalized derivative V give a self-map
of the Jacobi quartic. Its coordinate equations are checked in a finite
polynomial ring through degree p−1. -/
def QuarticLiftsAtSeven : Prop :=
  ∀ (p : ℕ), p.Prime → p≠2 → p≠7 → ∀ (x y : ℤ), (p:ℤ)=x^2+7*y^2 →
    ∀ s : ZMod (p^3), s^2= -7 → IsUnit s → IsUnit ((x:ZMod (p^3))+(y:ZMod (p^3))*s) →
    ∃ (u : ZMod (p^3)) (A D V : (ZMod (p^3))[X]),
      A.natDegree<p ∧ A.coeff 0=0 ∧ D.coeff 0=0 ∧ u^2=(s^(p/2))^2 ∧ V.coeff 0=1 ∧
      let F := frobeniusPolynomial p u A D
      let Q := quartic (ZMod (p^3))
      F.derivative=C ((x:ZMod (p^3))-(y:ZMod (p^3))*s)*V ∧ X^p ∣ Q*V^2-Q.comp F

theorem from_quartic_lifts (lifts : QuarticLiftsAtSeven) : type_of% @OeisA179537.conjecture1 := by
  apply from_frobenius_lifts
  intro p hp hp2 hp7 x y hxy s hs hsu hunit
  obtain ⟨u,A,D,V,hA,hA0,hD,hu,hV,hd,hEq⟩ := lifts p hp hp2 hp7 x y hxy s hs hsu hunit
  refine ⟨u,A,D,hA,hD,hu,?_⟩
  let R := ZMod (p^3)
  let F := frobeniusPolynomial p u A D
  let B := legendreDifferential (p/2) s (chart s)
  let Q := quartic R
  have h₂ : IsUnit (2:R) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide : 0<3)).2
      (fun d => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 d))
  have ht : s*(1-2*chart s) = -21 := by
    unfold chart
    linear_combination s*(3*s-1)*ZMod.mul_inv_of_unit (2:R) h₂ + 3*hs
  have radical := legendre_radical p hp hp2 s (chart s)
  rw [ht,hs] at radical
  have hQ : 1-2*C (-21 : R)*X^2+C (-7 : R)*X^4=Q := by
    simp only [Q,quartic,map_neg,map_ofNat]
    ring
  rw [hQ] at radical
  apply pullback_of_quartic p Q B F V _ h₂ _ _ _ hV radical hd hEq
  · simp [Q,quartic,coeff_zero_eq_eval_zero]
  · have hh := legendreDifferential_coeff (p/2) 0 (by omega) s (chart s)
    simpa [B,shiftedLegendre] using hh
  · have h0 := hp.ne_zero
    simp [F,frobeniusPolynomial,coeff_zero_eq_eval_zero,h0,← coeff_zero_eq_eval_zero A,hA0]

end
end SunCoster

end

section

/- Reduction from a primitive integral quartic map to the split-prime congruence. -/

namespace SunCoster
open Polynomial
noncomputable section

/-- Characteristic-zero polynomial data of the oriented endomorphism in the
Jacobi chart. The presentation is scaled by any joint primitive factor. -/
structure IntegralQuarticPresentation (p : ℕ) [Fact p.Prime] (z π : ℤ_[p]) where
  degree : ℕ
  numerator : ℤ_[p][X]
  denominator : ℤ_[p][X]
  degree_le : degree ≤ p
  numerator_degree : numerator.natDegree ≤ degree
  denominator_degree : denominator.natDegree < degree
  numerator_zero : numerator.coeff 0=0
  primitive : numerator.map PadicInt.toZMod ≠ 0 ∨ denominator.map PadicInt.toZMod ≠ 0
  reciprocal : ∀ j ≤ degree, PadicInt.toZMod (numerator.coeff j)=0 ↔
    PadicInt.toZMod (denominator.coeff (degree-j))=0
  numerator_odd : ∀ i, i%2=0 → PadicInt.toZMod (numerator.coeff i)=0
  denominator_even : ∀ i, i%2=1 → PadicInt.toZMod (denominator.coeff i)=0
  ends : (numerator.coeff degree)^2=(z^(degree/2))^2*(denominator.coeff 0)^2
  tangent : (numerator.derivative*denominator-numerator*denominator.derivative).coeff 0 =
    π*(denominator.coeff 0)^2
  equation : (quartic ℤ_[p])*(numerator.derivative*denominator-numerator*denominator.derivative)^2 =
    C π^2*(denominator^4+42*numerator^2*denominator^2-7*numerator^4)

theorem IntegralQuarticPresentation.finite {p : ℕ} [Fact p.Prime] {z π : ℤ_[p]}
    (model : IntegralQuarticPresentation p z π) (unit : ℤ_[p]ˣ) (hπ : π*(unit:ℤ_[p])=p) :
    let r := @PadicInt.toZModPow p _ 3
    ∃ (u : ZMod (p^3)) (A E V : (ZMod (p^3))[X]),
      A.natDegree<p ∧ A.coeff 0=0 ∧ E.coeff 0=0 ∧ u^2=((r z)^(p/2))^2 ∧ V.coeff 0=1 ∧
      let F := frobeniusPolynomial p u A E
      F.derivative=C (r π)*V ∧ X^p ∣ quartic (ZMod (p^3))*V^2-(quartic (ZMod (p^3))).comp F := by
  let r := @PadicInt.toZModPow p _ 3
  let N := model.numerator
  let D := model.denominator
  let W := N.derivative*D-N*D.derivative
  have hπr : PadicInt.toZMod π=0 := by
    have h := congrArg (PadicInt.toZMod (p:=p)) hπ
    rw [map_mul,map_natCast,ZMod.natCast_self] at h
    exact (mul_eq_zero.mp h).resolve_right ((unit.isUnit.map PadicInt.toZMod).ne_zero)
  have hw := wronskian_residue (quartic ℤ_[p]) N D (D^4+42*N^2*D^2-7*N^4) π hπr
    (by simp [quartic,coeff_zero_eq_eval_zero]) model.equation
  obtain ⟨d,a,b,A,E,ha,hb,hA,hA0,hE,hN,hD⟩ := integral_frobenius_shape model.degree N D
    model.degree_le model.numerator_degree model.denominator_degree model.numerator_zero
    model.primitive model.reciprocal model.numerator_odd model.denominator_even hw
  let k : ℤ_[p] := ↑b⁻¹
  let K := C k
  let u := k*(a:ℤ_[p])
  have zk : k*(b:ℤ_[p])=1 := b.inv_mul
  have uk : u^2=(z^(p/2))^2 := by
    have e := model.ends
    rw [d,←ha,←hb] at e
    calc
      u^2=k^2*(a:ℤ_[p])^2 := mul_pow ..
      _=(z^(p/2))^2*(k*(b:ℤ_[p]))^2 := by rw [e]; ring
      _=_ := by rw [zk,one_pow,mul_one]
  have wr : (K*N).derivative*(K*D)-(K*N)*(K*D).derivative=K^2*W := by
    simp only [K,derivative_C_mul,W]; ring
  have tn : ((K*N).derivative*(K*D)-(K*N)*(K*D).derivative).coeff 0=π := by
    rw [wr,show K^2=C (k^2) from (map_pow ..).symm,coeff_C_mul,
      show W.coeff 0=π*(D.coeff 0)^2 from model.tangent,←hb]
    calc
      _=π*(k*(b:ℤ_[p]))^2 := by ring
      _=_ := by rw [zk,one_pow,mul_one]
  have q : (1+C (42:ℤ_[p])*X^2+C (-7:ℤ_[p])*X^4)*
      ((K*N).derivative*(K*D)-(K*N)*(K*D).derivative)^2 =
      C π^2 * ((K*D)^4 + C (42:ℤ_[p])*(K*N)^2*(K*D)^2+C (-7:ℤ_[p])*(K*N)^4) := by
    rw [wr]; simp only [map_neg,map_ofNat]
    have eq : (1+42*X^2-7*X^4)*W^2=C π^2*(D^4+42*N^2*D^2-7*N^4) := model.equation
    linear_combination K^4*eq
  have n' : K*N=C u*(X^p+C (p:ℤ_[p])*A) := by rw [hN,←mul_assoc]; simp [K,u]
  have d' : K*D=1+C (p:ℤ_[p])*E := by rw [hD,←mul_assoc]; simp [K,←map_mul,zk]
  obtain ⟨V,hV,der,pull⟩ := finite_quartic_of_integral_model 42 (-7) π u unit hπ A E hE
    (K*N) (K*D) n' d' tn q
  refine ⟨r u,A.map r,E.map r,V,natDegree_map_le.trans_lt hA,by simp [hA0],by simp [hE],
    by simpa only [map_pow] using congrArg r uk,hV,der,?_⟩
  have shape : 1+C (r 42)*X^2+C (r (-7))*X^4=quartic (ZMod (p^3)) := by
    simp only [quartic,map_ofNat,map_neg]; ring
  change (_ : (ZMod (p^3))[X]) = _ at pull
  rw [shape] at pull
  rw [pull,sub_self]; exact dvd_zero _

/-- Producing the characteristic-zero presentations for the oriented
split parameters suffices for the exact pinned statement. -/
theorem from_integral_quartic_presentations
    (models : ∀ (p : ℕ) [Fact p.Prime], p≠2 → p≠7 → ∀ (x y : ℤ),
      (p:ℤ)=x^2+7*y^2 → ∀ (z : ℤ_[p]), z^2= -7 → IsUnit z →
      IsUnit ((x:ℤ_[p])+y*z) → Nonempty (IntegralQuarticPresentation p z ((x:ℤ_[p])-y*z))) :
    type_of% @OeisA179537.conjecture1 := by
  apply from_quartic_lifts
  intro p hp hp2 hp7 x y hxy s hs hsu hunit
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨z,hz,he,hzu⟩ := lift_sqrt_neg_seven (by decide : 0<3) hp2 s hs hsu
  obtain ⟨unit,hu,_,hn⟩ := oriented_padic_factors (k:=3) (by decide) z hz x y hxy (he ▸ hunit)
  obtain ⟨model⟩ := models p hp2 hp7 x y hxy z hz hzu (hu ▸ unit.isUnit)
  have hπ : ((x:ℤ_[p])-y*z)*(unit:ℤ_[p])=p := by rw [hu]; exact hn
  simpa only [map_sub,map_mul,map_intCast,he] using model.finite unit hπ

end
end SunCoster

end

section

namespace SunCoster
open Polynomial

/-- A single scalar puts both polynomials of a p-adic fraction in the
valuation ring, with at least one coefficient becoming one. -/
theorem primitive_padic_model {p : ℕ} [Fact p.Prime] (N D : ℚ_[p][X]) (hn : N≠0 ∨ D≠0) :
    ∃ (c : ℚ_[p]) (M L : ℤ_[p][X]), c≠0 ∧
      M.map (algebraMap ℤ_[p] ℚ_[p])=C c*N ∧
      L.map (algebraMap ℤ_[p] ℚ_[p])=C c*D ∧
      (M.map PadicInt.toZMod≠0 ∨ L.map PadicInt.toZMod≠0) := by
  classical
  let s := (N.support.image N.coeff) ∪ (D.support.image D.coeff)
  have nonempty : s.Nonempty := by
    rcases hn with hn | hd
    · obtain ⟨j,hj⟩ := support_nonempty.mpr hn
      exact ⟨_,Finset.mem_union_left _ (Finset.mem_image_of_mem _ hj)⟩
    · obtain ⟨j,hj⟩ := support_nonempty.mpr hd
      exact ⟨_,Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj)⟩
  obtain ⟨t,ht,hmax⟩ := Finset.exists_max_image s (fun x : ℚ_[p] => ‖x‖) nonempty
  have cap (P : ℚ_[p][X]) (hP : P=N ∨ P=D) (i : ℕ) : ‖P.coeff i‖ ≤ ‖t‖ := by
    by_cases hi : P.coeff i=0
    · simp [hi]
    · apply hmax
      rcases hP with rfl | rfl
      · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (mem_support_iff.mpr hi))
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (mem_support_iff.mpr hi))
  have occ : (∃ i, i∈N.support ∧ N.coeff i=t) ∨ (∃ i, i∈D.support ∧ D.coeff i=t) := by
    simpa only [s,Finset.mem_union,Finset.mem_image] using ht
  have ht0 : t≠0 := by
    rcases occ with ⟨i,hi,he⟩ | ⟨i,hi,he⟩ <;> simpa only [←he] using mem_support_iff.mp hi
  let incl := algebraMap ℤ_[p] ℚ_[p]
  have liftP (P : ℚ_[p][X]) (hP : P=N ∨ P=D) : ∃ M : ℤ_[p][X], M.map incl=C t⁻¹*P := by
    apply (mem_lifts _).mp
    apply (lifts_iff_coeff_lifts _).mpr
    intro j
    have norm : ‖t⁻¹ * P.coeff j‖ ≤ 1 := by
      rw [norm_mul,norm_inv,inv_mul_eq_div,div_le_one (norm_pos_iff.mpr ht0)]
      exact cap P hP j
    exact ⟨⟨_,norm⟩,(coeff_C_mul ..).symm⟩
  obtain ⟨M,hM⟩ := liftP N (.inl rfl)
  obtain ⟨L,hL⟩ := liftP D (.inr rfl)
  have nz (P : ℚ_[p][X]) (Q : ℤ_[p][X]) {i : ℕ} (eq : Q.map incl=C t⁻¹*P)
      (h : P.coeff i=t) : Q.map PadicInt.toZMod ≠ 0 := by
    have he := congrArg (fun f : ℚ_[p][X] => f.coeff i) eq
    simp only [coeff_map,coeff_C_mul,h,inv_mul_cancel₀ ht0] at he
    have h1 : Q.coeff i=1 := Subtype.ext he
    intro z
    have hh := congrArg (fun f : (ZMod p)[X] => f.coeff i) z
    simp only [coeff_map,h1,map_one,coeff_zero,one_ne_zero] at hh
  refine ⟨t⁻¹,M,L,inv_ne_zero ht0,hM,hL,?_⟩
  rcases occ with ⟨i,hi,he⟩ | ⟨i,hi,he⟩
  · exact .inl (nz N M hM he)
  · exact .inr (nz D L hL he)

end SunCoster

end

section

/- Reduction of the split-prime congruence to a characteristic-zero quartic map. -/

namespace SunCoster
open Polynomial
noncomputable section

/-- Characteristic-zero data of the CM map, permitting arbitrary common
scaling of its numerator and denominator. -/
structure FieldQuarticPresentation (p : ℕ) [Fact p.Prime] (z π : ℚ_[p]) where
  degree : ℕ
  numerator : ℚ_[p][X]
  denominator : ℚ_[p][X]
  nonzero : denominator ≠ 0
  degree_le : degree ≤ p
  numerator_degree : numerator.natDegree ≤ degree
  denominator_degree : denominator.natDegree < degree
  reciprocal : ∀ j ≤ degree, ‖numerator.coeff j‖ = ‖denominator.coeff (degree-j)‖
  numerator_odd : ∀ i, i%2=0 → numerator.coeff i=0
  denominator_even : ∀ i, i%2=1 → denominator.coeff i=0
  ends : (numerator.coeff degree)^2=(z^(degree/2))^2*(denominator.coeff 0)^2
  tangent : (numerator.derivative*denominator-numerator*denominator.derivative).coeff 0 =
    π*(denominator.coeff 0)^2
  equation : (quartic ℚ_[p])*(numerator.derivative*denominator-numerator*denominator.derivative)^2 =
    C π^2*(denominator^4+42*numerator^2*denominator^2-7*numerator^4)

theorem FieldQuarticPresentation.integral {p : ℕ} [Fact p.Prime] {z π : ℤ_[p]}
    (model : FieldQuarticPresentation p (z:ℚ_[p]) (π:ℚ_[p])) :
    Nonempty (IntegralQuarticPresentation p z π) := by
  let N := model.numerator
  let D := model.denominator
  let r := algebraMap ℤ_[p] ℚ_[p]
  have inj : Function.Injective r := Subtype.coe_injective
  obtain ⟨k,M,L,hk,hM,hL,hprim⟩ := primitive_padic_model N D (.inr model.nonzero)
  change M.map r = C k*N at hM
  change L.map r = C k*D at hL
  have mcoeff (i : ℕ) : r (M.coeff i)=k*N.coeff i := by
    simpa only [coeff_map,coeff_C_mul] using congrArg (fun f : ℚ_[p][X] => f.coeff i) hM
  have lcoeff (i : ℕ) : r (L.coeff i)=k*D.coeff i := by
    simpa only [coeff_map,coeff_C_mul] using congrArg (fun f : ℚ_[p][X] => f.coeff i) hL
  have mpar (i : ℕ) (hh : i%2=0) : M.coeff i=0 := inj (by
    rw [mcoeff,show N.coeff i=0 from model.numerator_odd i hh,mul_zero,map_zero])
  have lpar (i : ℕ) (hh : i%2=1) : L.coeff i=0 := inj (by
    rw [lcoeff,show D.coeff i=0 from model.denominator_even i hh,mul_zero,map_zero])
  let W := N.derivative*D-N*D.derivative
  let V := M.derivative*L-M*L.derivative
  have wr : V.map r=C k^2*W := by
    simp only [V,W,Polynomial.map_sub,Polynomial.map_mul,←derivative_map,hM,hL,derivative_C_mul]
    ring
  refine ⟨⟨model.degree,M,L,model.degree_le,?_,?_,mpar 0 rfl,hprim,?_,
    fun i h => by rw [mpar i h,map_zero],fun i h => by rw [lpar i h,map_zero],?_,?_,?_⟩⟩
  · rw [←natDegree_map_eq_of_injective inj M,hM,natDegree_C_mul hk]
    exact model.numerator_degree
  · rw [←natDegree_map_eq_of_injective inj L,hL,natDegree_C_mul hk]
    exact model.denominator_degree
  · intro i hi
    have eq : ‖r (M.coeff i)‖=‖r (L.coeff (model.degree-i))‖ := by
      rw [mcoeff,lcoeff,norm_mul,norm_mul,show ‖N.coeff i‖=‖D.coeff (model.degree-i)‖
        from model.reciprocal i hi]
    have iff : IsUnit (M.coeff i) ↔ IsUnit (L.coeff (model.degree-i)) := by
      rw [PadicInt.isUnit_iff,PadicInt.isUnit_iff]
      change ‖r (M.coeff i)‖=1 ↔ ‖r (L.coeff (model.degree-i))‖=1
      rw [eq]
    simpa only [padic_unit_iff_residue,not_ne_iff] using iff.not
  · apply inj
    simp only [map_pow,map_mul,mcoeff,lcoeff]
    have e : (N.coeff model.degree)^2=((z:ℚ_[p])^(model.degree/2))^2*(D.coeff 0)^2 := model.ends
    change _=((z:ℚ_[p])^(model.degree/2))^2*_
    linear_combination k^2*e
  · apply inj
    change r (V.coeff 0)=_
    rw [←coeff_map,wr,←map_pow,coeff_C_mul,map_mul,map_pow,lcoeff]
    have e : W.coeff 0=(π:ℚ_[p])*(D.coeff 0)^2 := model.tangent
    rw [e]
    change _=(π:ℚ_[p])*_
    ring
  · apply Polynomial.map_injective r inj
    change ((quartic ℤ_[p])*V^2).map r=_
    simp only [Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_sub,Polynomial.map_add,
      Polynomial.map_C,Polynomial.map_ofNat,hM,hL,wr,quartic,Polynomial.map_one,map_X]
    have eq : (1+42*X^2-7*X^4)*W^2=C (π:ℚ_[p])^2*(D^4+42*N^2*D^2-7*N^4) := model.equation
    change _=C (π:ℚ_[p])^2*_
    linear_combination (C k)^4*eq

theorem from_field_quartic_presentations
    (models : ∀ (p : ℕ) [Fact p.Prime], p≠2 → p≠7 → ∀ (x y : ℤ),
      (p:ℤ)=x^2+7*y^2 → ∀ (z : ℤ_[p]), z^2= -7 → IsUnit z →
      IsUnit ((x:ℤ_[p])+y*z) →
      Nonempty (FieldQuarticPresentation p (z:ℚ_[p]) (((x:ℤ_[p])-y*z:ℤ_[p]):ℚ_[p]))) :
    type_of% @OeisA179537.conjecture1 := by
  apply from_integral_quartic_presentations
  intro p hp hp2 hp7 x y hxy z hz hzu hu
  obtain ⟨model⟩ := models p hp2 hp7 x y hxy z hz hzu hu
  exact model.integral

end
end SunCoster

end

section

namespace SunCoster
open Polynomial

/-- An odd rational function fixing zero has an odd numerator and an even
denominator in any reduced presentation regular at zero. -/
theorem odd_fraction_coefficients {K : Type*} [Field K] [CharZero K] (N D : K[X])
    (h0 : D.coeff 0 ≠ 0) (hcop : IsCoprime N D)
    (h : N.comp (-X)*D = -N*D.comp (-X)) :
    (∀ i, i%2=0 → N.coeff i=0) ∧ (∀ i, i%2=1 → D.coeff i=0) := by
  have hd : D≠0 := by intro z; exact h0 (by simp [z])
  obtain ⟨P,hP⟩ : D ∣ D.comp (-X) := by
    apply hcop.symm.dvd_of_dvd_mul_left
    exact ⟨-(N.comp (-X)),by linear_combination h⟩
  have hp : P≠0 := by
    intro z
    exact hd (comp_neg_X_eq_zero_iff.mp (hP.trans (by simp [z])))
  have e : D.natDegree = (D*P).natDegree := by
    rw [←hP]; exact (natDegree_eq_of_degree_eq degree_comp_neg_X).symm
  rw [natDegree_mul hd hp] at e
  have pc := eq_C_of_natDegree_eq_zero (show P.natDegree=0 by omega)
  have p0 : P.coeff 0=1 := by
    have hh := congrArg (Polynomial.eval 0) hP
    simp only [eval_comp,eval_neg,eval_X,neg_zero,eval_mul,←coeff_zero_eq_eval_zero] at hh
    apply mul_left_cancel₀ h0
    simpa only [mul_one] using hh.symm
  have d : D.comp (-X)=D := by rw [hP,pc,p0,map_one,mul_one]
  have n : N.comp (-X)= -N := mul_right_cancel₀ hd (by simpa only [d] using h)
  have negcoef (P : K[X]) (i : ℕ) : (P.comp (-X)).coeff i=P.coeff i*(-1)^i := by
    have e : (P.comp (C (-1:K)*X)).coeff i=P.coeff i*(-1)^i := comp_C_mul_X_coeff
    simpa only [map_neg,map_one,neg_one_mul] using e
  constructor
  · intro i hi
    have e := congrArg (fun f : K[X] => f.coeff i) n
    rw [negcoef,coeff_neg,Even.neg_one_pow (Nat.even_iff.mpr hi),mul_one] at e
    apply (mul_eq_zero.mp _).resolve_left (by norm_num : (2:K)≠0)
    linear_combination e
  · intro i hi
    have e := congrArg (fun f : K[X] => f.coeff i) d
    rw [negcoef,Odd.neg_one_pow (Nat.odd_iff.mpr hi),mul_neg_one] at e
    apply (mul_eq_zero.mp _).resolve_left (by norm_num : (2:K)≠0)
    linear_combination -e

end SunCoster

end

section

/- Characteristic-zero odd reciprocal maps on the Jacobi quartic suffice for A179537.1. -/

namespace SunCoster
open Polynomial
noncomputable section

/-- A reciprocal map whose numerator has odd degree has the prescribed
endpoint square. Its numerator coefficients and mirrored denominator
coefficients have equal p-adic norms. -/
theorem oriented_reciprocal_coefficients {p : ℕ} [Fact p.Prime]
    {z c : ℚ_[p]} (hz : ‖z‖=1) (hc : c=1/z) {d : ℕ} (hdodd : Odd d)
    (N D : ℚ_[p][X]) (hn : N.natDegree=d) (hd : D.natDegree≤d) (hN : N≠0)
    (h0 : D.coeff 0≠0) (cop : IsCoprime N D)
    (rec : N*Reciprocity.reciprocal c d N=C c*D*Reciprocity.reciprocal c d D) :
    (N.coeff d)^2=(z^(d/2))^2*(D.coeff 0)^2 ∧
    ∀ j ≤ d, ‖N.coeff j‖=‖D.coeff (d-j)‖ := by
  have z0 : z≠0 := by intro h; simp [h] at hz
  have cn : ‖c‖=1 := by simp [hc,norm_div,hz]
  have c0 : c≠0 := by intro h; simp [h] at cn
  obtain ⟨k,hk,rD,rN,eq⟩ := Reciprocity.endpoints c c0 d N D hn hd hN h0 cop rec
  have e0 := congrArg (fun f : ℚ_[p][X] => f.coeff d) rD
  rw [Reciprocity.coeff c d d le_rfl,Nat.sub_self,pow_zero,mul_one,coeff_C_mul] at e0
  have kn : ‖k‖=1 := by
    have hratio := congrArg norm eq
    simp only [norm_mul,norm_pow,cn,one_pow,mul_one,norm_div] at hratio
    have hnpos := norm_nonneg (N.coeff d)
    have hdpos := norm_pos_iff.mpr h0
    have ratio_nonneg : 0 ≤ ‖N.coeff d‖/‖D.coeff 0‖ := div_nonneg hnpos hdpos.le
    have eqnorm := (div_eq_one_iff_eq hdpos.ne').mp
      (show ‖N.coeff d‖/‖D.coeff 0‖=1 by nlinarith [hratio])
    have e := congrArg norm e0
    rw [norm_mul,eqnorm] at e
    apply mul_right_cancel₀ hdpos.ne'
    simpa only [one_mul] using e.symm
  constructor
  · obtain ⟨h,dh⟩ := hdodd
    have dh' : d=2*h+1 := by omega
    have ed : (N.coeff d)^2 * c^d=c*(D.coeff 0)^2 := by
      field_simp [h0] at eq
      linear_combination eq
    have cinv : c*z=1 := by rw [hc,div_mul_cancel₀ _ z0]
    have ec : c^(2*h)*z^(2*h)=1 := by
      rw [←mul_pow,cinv,one_pow]
    have half : d/2=h := by omega
    rw [half]
    have ed' : (N.coeff d)^2*c^(2*h)=(D.coeff 0)^2 := by
      apply mul_right_cancel₀ c0
      have ex : (N.coeff d)^2*(c^(2*h)*c)=c*(D.coeff 0)^2 := by
        simpa only [dh',pow_succ] using ed
      linear_combination ex
    calc
      _ = (N.coeff d)^2*(c^(2*h)*z^(2*h)) := by rw [ec,mul_one]
      _ = (z^h)^2*((N.coeff d)^2*c^(2*h)) := by ring
      _ = _ := by rw [ed']
  · intro j hj
    have e := congrArg (fun f : ℚ_[p][X] => f.coeff j) rD
    rw [Reciprocity.coeff c d j hj,coeff_C_mul] at e
    have nh := congrArg norm e
    simpa only [norm_mul,norm_pow,cn,kn,one_pow,mul_one,one_mul] using nh.symm

/-- Passing to the negative map when needed chooses the prescribed sign
of the tangent at zero. The squared quartic identity determines the
two possible tangent values before this sign choice. -/
theorem field_presentation_of_symmetries {p : ℕ} [Fact p.Prime]
    {z π : ℚ_[p]} (hz : ‖z‖=1) (N D : ℚ_[p][X]) (hN : N≠0) (h0 : D.coeff 0≠0)
    (hdeg : N.natDegree≤p) (hD : D.natDegree<N.natDegree) (cop : IsCoprime N D)
    (odd : N.comp (-X)*D = -N*D.comp (-X))
    (rec : let c := 1/z; let d := N.natDegree
      N*Reciprocity.reciprocal c d N=C c*D*Reciprocity.reciprocal c d D)
    (eq : quartic ℚ_[p]*(N.derivative*D-N*D.derivative)^2=
      C π^2*(D^4+42*N^2*D^2-7*N^4)) : Nonempty (FieldQuarticPresentation p z π) := by
  obtain ⟨oddN,evenD⟩ := odd_fraction_coefficients N D h0 cop odd
  have nzero : N.coeff 0=0 := oddN 0 rfl
  have dodd : Odd N.natDegree := by
    have nlead : N.coeff N.natDegree≠0 := leadingCoeff_ne_zero.mpr hN
    have e := mt (oddN _) nlead
    exact Nat.odd_iff.mpr (by omega)
  obtain ⟨ends,symm⟩ := oriented_reciprocal_coefficients hz rfl dodd N D rfl hD.le hN h0 cop rec
  let W := N.derivative*D-N*D.derivative
  have t : (W.coeff 0)^2=(π*(D.coeff 0)^2)^2 := by
    have e := congrArg (Polynomial.eval 0) eq
    change ((quartic ℚ_[p])*W^2).eval 0=_ at e
    simp only [quartic,eval_add,eval_mul,eval_sub,eval_X,eval_pow,zero_pow (by decide : 2≠0),
      zero_pow (by decide : 4≠0),mul_zero,add_zero,sub_zero,eval_one,one_mul,
      eval_C,←coeff_zero_eq_eval_zero N,nzero,←coeff_zero_eq_eval_zero D,
      ←coeff_zero_eq_eval_zero W] at e
    linear_combination e
  have hzD : D≠0 := by intro h; simp [h] at h0
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp t with tan | tan
  · exact ⟨⟨N.natDegree,N,D,hzD,hdeg,le_rfl,hD,symm,oddN,evenD,ends,tan,eq⟩⟩
  · have wn : (-N).derivative*D-(-N)*D.derivative= -W := by
      simp only [derivative_neg,W]; ring
    refine ⟨⟨N.natDegree,-N,D,hzD,hdeg,by simp,hD,?_,?_,evenD,?_,?_,?_⟩⟩
    · simpa only [coeff_neg,norm_neg] using symm
    · intro i hi; simp [oddN i hi]
    · simpa only [coeff_neg,neg_sq] using ends
    · rw [wn,coeff_neg,tan,neg_neg]
    · rw [wn]
      simpa only [neg_sq,Even.neg_pow (show Even 4 by decide)] using eq

/-- Geometric obligations on the rational CM map over the p-adic field. -/
def SymmetricQuarticMapsAtSeven : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p≠2 → p≠7 → ∀ (x y : ℤ), (p:ℤ)=x^2+7*y^2 →
    ∀ (z : ℤ_[p]), z^2= -7 → IsUnit z → IsUnit ((x:ℤ_[p])+y*z) →
    ∃ N D : ℚ_[p][X], N≠0 ∧ D.coeff 0≠0 ∧ N.natDegree≤p ∧ D.natDegree<N.natDegree ∧
      IsCoprime N D ∧ N.comp (-X)*D = -N*D.comp (-X) ∧
      (let c := 1/(z:ℚ_[p]); let d := N.natDegree
       N*Reciprocity.reciprocal c d N=C c*D*Reciprocity.reciprocal c d D) ∧
      quartic ℚ_[p]*(N.derivative*D-N*D.derivative)^2 =
        C ((x:ℚ_[p])-y*(z:ℚ_[p]))^2*(D^4+42*N^2*D^2-7*N^4)

theorem from_symmetric_quartic_maps (maps : SymmetricQuarticMapsAtSeven) :
    type_of% @OeisA179537.conjecture1 := by
  apply from_field_quartic_presentations
  intro p hp hp2 hp7 x y hxy z hz hzu hunit
  obtain ⟨N,D,hN,h0,hdeg,hD,cop,hodd,rec,eq⟩ := maps p hp2 hp7 x y hxy z hz hzu hunit
  exact field_presentation_of_symmetries (PadicInt.isUnit_iff.mp hzu) N D hN h0 hdeg hD
    cop hodd rec eq

end
end SunCoster

end

section

namespace SunCoster
open Polynomial SunDescent SunSevenIsogeny WeierstrassCurve.Affine ChartAction
noncomputable section

/-- The characteristic-zero CM construction, specialized to the branch
s = 2v−1. All three identities refer to the same rational map. -/
theorem cm_chart_presentation (K : Type*) [Field K] [CharZero K] (s : K) (hs : s^2= -7)
    (m n : ℤ) (p : ℕ) (hp : 0<p) (hpodd : Odd (m+n)) (hnorm : (p:ℤ)=m^2+7*n^2) :
    ∃ A B : K[X], IsCoprime A B ∧ A.natDegree=p ∧ B.natDegree<p ∧
      A.coeff 0=0 ∧ B.coeff 0≠0 ∧ Reciprocity.oddFraction A B ∧
      Reciprocity.reciprocalFraction (1/s) A B ∧ Reciprocity.quarticEquation ((m:K)-n*s) A B := by
  classical
  let L := DeckField K
  letI := deckAlgebra K
  let v := (1+s)/2
  have hv : v^2=v-2 := by dsimp [v]; linear_combination hs/4
  have ev : 2*v-1=s := by dsimp [v]; ring
  have s0 : s≠0 := by intro z; rw [z] at hs; norm_num at hs
  let c := 1/s
  have hc : c≠0 := one_div_ne_zero s0
  have hcq : -7*c^2=1 := by dsimp [c]; field_simp; linear_combination -hs
  obtain ⟨D,Y,hP,hV,dP,dV,dc⟩ := GenericCM.generic_generators K v hv
  let P : (shortCurve L).Point := Point.some (incl K RatFunc.X) Y hP
  let V : (shortCurve L).Point := Point.some (phiX (incl K (RatFunc.C v)) (incl K RatFunc.X))
    (phiY (incl K (RatFunc.C v)) (incl K RatFunc.X) Y) hV
  let U := (m+n) • P+(2*(-n)) • V
  let j := incl K
  let π : K := (m:K)-n*s
  obtain ⟨P₁,V₁,R,⟨_,rfl⟩,⟨_,rfl⟩,eR,dR,rU⟩ :=
    generic_cm_norm j v hv Y (short_equation.mp hP.1) m (-n)
  have eR' : j R=U.xRep 0 := by simpa only [U,P,V,sub_neg_eq_add] using eR
  have rat : rationalCoordinates j Y U := by simpa only [U,P,V,sub_neg_eq_add] using rU
  have degR : deg R=p := by
    change height R=p
    exact_mod_cast (show (height R : ℤ)=(p:ℤ) by simpa only [neg_sq,←hnorm] using dR)
  obtain ⟨ht,q,b,e,ub,y0,b0,t0,w0,dq,eq⟩ :=
    geometric_chart_map K v hv Y hP hV (m+n) (-n) hpodd U rfl rat R eR' p hp degR
  obtain ⟨f,fix,action⟩ := KernelLift.simultaneous_reciprocals K v hv Y hP hV
    (m+n) (2*(-n)) hpodd t0 w0
  let σ : L →ₐ[K] L := { toRingHom := f, commutes' := fix }
  have scale : algebraMap K L c=KernelLift.constMap K (1/(2*v-1)) := by rw [ev]; rfl
  have recip := signed_reciprocity (L:=L) q c hc (param P) (param U) ht eq σ
    (by
      rw [scale]
      first | exact action | convert! action using 3 <;> rfl)
  let F := oddMap q
  have ep : algebraMap K L π=(m:L)-(n:L)*(2*(incl K (RatFunc.C v))-1) := by
    change GenericCM.constant K π=_
    dsimp only [GenericCM.constant,π]
    rw [←ev]
    simp only [map_sub,map_mul,map_intCast,map_ofNat,map_one]
  have vel : Velocity D (algebraMap K L π) U := by
    rw [ep]
    have d := cm_lattice_multiplier m n dP dV
    simpa only [U,P,V,mul_neg,neg_zsmul,sub_eq_add_neg] using d
  rw [ub] at vel
  obtain ⟨dX,dY⟩ := vel
  have hnum := ratEval_num (L:=L) (param P) ht F
  change _=ratEval (param P) ht (oddMap q)*_ at hnum
  rw [eq,ub] at hnum
  have diff : Reciprocity.quarticEquation π F.num F.denom := by
    apply wronskian_from_coordinates (L:=L) D (algebraMap K L) dc π y0 b0
      (short_equation.mp hP.1) (short_equation.mp e.1)
      (by simpa using dP.1) (by simpa using dP.2) dX dY
    · exact hnum
    · exact transcendental_iff_injective.mp ht
  exact Reciprocity.ordered_presentation c π hc hcq p hp F.num F.denom F.isCoprime_num_denom
    dq (oddMap_num q) recip diff

theorem split_maps : SymmetricQuarticMapsAtSeven := by
  intro p hpF hp2 _ x y rep z hz _ _
  have hp : Nat.Prime p := hpF.out
  have primeOdd := hp.eq_two_or_odd.resolve_left hp2
  have op : Odd p := Nat.odd_iff.mpr (by omega)
  have oi : Odd (p:ℤ) := by exact_mod_cast op
  rw [rep] at oi
  have xyodd : Odd (x+y) := by simpa [parity_simps,show ¬Even (7:ℤ) by decide] using oi
  have hs : (z:ℚ_[p])^2= -7 := congrArg (fun w : ℤ_[p] => (w:ℚ_[p])) hz
  obtain ⟨N,D,cop,nd,dd,_,h0,odd,recip,eq⟩ := cm_chart_presentation ℚ_[p] z hs x y p hp.pos xyodd rep
  have hn : N≠0 := by intro h; simp [h] at nd; omega
  refine ⟨N,D,hn,h0,nd.le,by omega,cop,?_,?_,eq⟩
  · simpa only [Reciprocity.oddFraction,neg_mul] using odd
  · exact Reciprocity.polynomial_identity _ _ _ le_rfl (by omega) recip

end
end SunCoster

theorem OMA.solution : type_of% @OeisA179537.conjecture1 :=
  SunCoster.from_symmetric_quartic_maps SunCoster.split_maps

end
