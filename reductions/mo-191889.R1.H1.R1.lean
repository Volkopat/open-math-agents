import OMAReductions.R_mo_191889_R1
import Mathlib

/-!
# The small squarefree parameters in the fourth-power census

For coprime positive x and y with x⁴ + y⁴ = bz² and b odd, write
x² + iy² = B W² in the Gaussian integers, with norms b and z. Both
coordinates of B must be squares modulo each prime factor of b. Ten
composite parameters fail this condition at every height. If b divides z,
a second factorization gives x² + iy² = B³ W² with norms b and z/b.

For the small-parameter step of ZedingZhang's reduction, the remaining
analytic hypothesis H1 is the bounded necessary direction of Tunnell's
theorem. Its ternary representation counts use the full signed boxes.
Multiplication of three finite theta sums in base 2²¹ computes all their
counts exactly, because each box contains fewer than 2²¹ triples. Among
the 324 arithmetically admissible parameters, 67 give equal counts after
the factor of two. Four of these are among the ten Gaussian obstructions.
H2 and H3 give the remaining 55 prime and eight composite Gaussian searches.

Noam D. Elkies and Gaurav Goel proved the minimum in *On powerful integers
expressible as sums of two coprime fourth powers*, sections 2–4.
https://antsmath.org/ANTSXV/papers/ANTS-XV_elkies-goel.pdf
-/

namespace OMA.R_mo_191889_R1_H1_R1

/-- Tunnell's necessary condition for the relevant squarefree 2b.
After division by two, the ternary forms are 4x²+y²+32z² and 4x²+y²+8z².
The list for an axis of radius L visits the integers from -L to L. -/
def H1 : Prop :=
  let row := fun c L : ℕ => (List.range (2*L+1)).map fun i => c*(i.dist L)^2
  let reps := fun c L : ℕ => (row 4 50).flatMap fun x =>
    (row 1 100).flatMap fun y => (row c L).map fun z => x+y+z
  ∀ b : ℕ, 1<b → b ≤ 10000 → Squarefree b → (∀ p ∈ b.primeFactors, p%8=1) →
    b ∉ ({4721,4777,6497,6577,9881}:Finset ℕ) →
    b ∉ ({1513,2329,2993,4369,4633,7081,7361,7769,8633,9809}:Finset ℕ) →
    (∃ a d c : ℚ, 0<a ∧ 0<d ∧ 0<c ∧ a^2+d^2=c^2 ∧ a*d=4*(b:ℚ)) →
    2*(reps 32 17).count b=(reps 8 35).count b

/-- Gaussian square-coordinate search for the 55 surviving prime norms. -/
def H2 : Prop :=
  ∀ b ∈ ([17,97,113,193,257,337,433,577,593,641,673,881,929,1153,
      1217,1297,1409,1777,1873,1889,2129,2417,2657,2753,2801,2833,2897,3121,
      3137,3329,3457,3697,4001,4129,4177,4289,4481,4561,4817,4993,5281,6353,
      6449,6481,6673,7057,7489,7537,8017,8081,8737,8753,9281,9649,9857]:List ℕ), ∀ B W : GaussianInt, B.norm=b →
    (∀ p ∈ b.primeFactors, ∃ t u : ZMod p, t^2=(B.re:ZMod p) ∧ u^2=(B.im:ZMod p)) →
    let a := B^3*W^2
    0<a.re → a.re ≤ a.im → IsSquare a.re → IsSquare a.im → a.re.natAbs.Coprime a.im.natAbs →
    a.norm < 3088257489493360278725196965477359217 → False

/-- Gaussian square-coordinate search for the eight surviving composite norms. -/
def H3 : Prop :=
  ∀ b ∈ ([1921,3649,4097,5617,5729,6817,7633,9553]:List ℕ), ∀ B W : GaussianInt, B.norm=b →
    (∀ p ∈ b.primeFactors, ∃ t u : ZMod p, t^2=(B.re:ZMod p) ∧ u^2=(B.im:ZMod p)) →
    let a := B^3*W^2
    0<a.re → a.re ≤ a.im → IsSquare a.re → IsSquare a.im → a.re.natAbs.Coprime a.im.natAbs →
    a.norm < 3088257489493360278725196965477359217 → False

section Arithmetic

private theorem not_four {x y : ℕ} (hc : x.Coprime y) : ¬ 4 ∣ x^4+y^4 := by
  intro h
  have tab : ∀ i j : Fin 4, (i.val^4+j.val^4)%4 = 0 →
      i.val%2 = 0 ∧ j.val%2 = 0 := by decide
  have congr := ((Nat.mod_modEq x 4).pow 4).add ((Nat.mod_modEq y 4).pow 4)
  have h0 : ((x%4)^4+(y%4)^4)%4 = 0 := congr.trans h.modEq_zero_nat
  obtain ⟨hx,hy⟩ := tab ⟨x%4, Nat.mod_lt _ (by decide)⟩ ⟨y%4, Nat.mod_lt _ (by decide)⟩ h0
  change (x%4)%2 = 0 at hx
  change (y%4)%2 = 0 at hy
  rw [Nat.mod_mod_of_dvd x (by decide : 2 ∣ 4)] at hx
  rw [Nat.mod_mod_of_dvd y (by decide : 2 ∣ 4)] at hy
  have hd := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hx) (Nat.dvd_of_mod_eq_zero hy)
  rw [show x.gcd y = 1 from hc] at hd
  norm_num at hd

private theorem gunit_fourth (u : GaussianIntˣ) : (u:GaussianInt)^4=1 := by
  have h := (Zsqrtd.norm_eq_one_iff' (show (-1:ℤ)≤0 by decide) (u:GaussianInt)).mpr u.isUnit
  generalize eq : (u:GaussianInt)=v at h ⊢
  obtain ⟨a,b⟩ := v
  change a*a-(-1)*b*b=1 at h
  have al : -1≤a := by by_contra! e; nlinarith [sq_nonneg b, mul_nonneg (show 0≤ -a-2 by omega) (show 0≤ -a+2 by omega)]
  have ah : a≤1 := by by_contra! e; nlinarith [sq_nonneg b, mul_nonneg (show 0≤ a-2 by omega) (show 0≤ a+2 by omega)]
  have bl : -1≤b := by by_contra! e; nlinarith [sq_nonneg a, mul_nonneg (show 0≤ -b-2 by omega) (show 0≤ -b+2 by omega)]
  have bh : b≤1 := by by_contra! e; nlinarith [sq_nonneg a, mul_nonneg (show 0≤ b-2 by omega) (show 0≤ b+2 by omega)]
  interval_cases a <;> interval_cases b <;> norm_num at h <;> decide

private theorem quartic_coprime {x y b z : ℕ} (hc : x.Coprime y) (hb : Odd b)
    (he : x^4+y^4=b*z^2) :
    let a : GaussianInt := ⟨(x:ℤ)^2,(y:ℤ)^2⟩
    IsCoprime a (star a) := by
  let a : GaussianInt := ⟨(x:ℤ)^2,(y:ℤ)^2⟩
  let i : GaussianInt := ⟨0,1⟩
  change IsCoprime a (star a)
  have hz : Odd z := by
    rcases Nat.even_or_odd z with ev|od
    · have h4 : 2^2 ∣ z^2 := pow_dvd_pow_of_dvd (even_iff_two_dvd.mp ev) 2
      exact (not_four hc (he ▸ dvd_mul_of_dvd_right h4 b)).elim
    · exact od
  have plus : a+star a=2*(x:GaussianInt)^2 := by
    ext <;> simp [a,star,pow_two]
    ring
  have minus : (-i)*(a-star a)=2*(y:GaussianInt)^2 := by
    ext <;> simp [a,i,star,pow_two]
    ring
  have prod : a*star a=((b*z^2:ℕ):GaussianInt) := by
    rw [← he,Zsqrtd.natCast_val]
    ext <;> simp [a,star] <;> ring
  have cps := ((hc.pow_left 2).pow_right 2).isCoprime.map (Int.castRingHom GaussianInt)
  have oddN := Nat.coprime_two_left.mpr (hb.mul (hz.pow (n:=2)))
  have cp2 := oddN.isCoprime.map (Int.castRingHom GaussianInt)
  simp only [Int.coe_castRingHom, Nat.cast_pow, Int.cast_pow, Int.cast_natCast] at cps
  change IsCoprime (2:GaussianInt) ((b*z^2:ℕ):GaussianInt) at cp2
  apply IsRelPrime.isCoprime
  intro d da dc
  have dx := plus ▸ dvd_add da dc
  have dy := minus ▸ dvd_mul_of_dvd_right (dvd_sub da dc) (-i)
  have d2 : d ∣ 2 := by
    obtain ⟨j,k,eq⟩ := cps
    have ds := dvd_add (dvd_mul_of_dvd_left dx j) (dvd_mul_of_dvd_left dy k)
    convert ds using 1
    linear_combination -2*eq
  exact cp2.isRelPrime d2 (prod ▸ dvd_mul_of_dvd_left da _)

private theorem quartic_norm (x y : ℕ) :
    (⟨(x:ℤ)^2,(y:ℤ)^2⟩ : GaussianInt).norm = ((x^4+y^4 : ℕ):ℤ) := by
  simp [Zsqrtd.norm]
  ring

/-- A scalar square in a primitive Gaussian norm can be removed as a Gaussian square. -/
theorem strip_norm_square {a : GaussianInt} {b z : ℕ}
    (cp : IsCoprime a (star a)) (hz : 0<z) (he : a.norm=(b:ℤ)*(z:ℤ)^2) :
    ∃ B W : GaussianInt, a=B*W^2 ∧ B.norm=b ∧ W.norm=z := by
  have prod : a*star a=(b:GaussianInt)*(z:GaussianInt)^2 := by
    rw [← Zsqrtd.norm_eq_mul_conj, he]
    push_cast
    rfl
  have scalar : (z:GaussianInt)^2 ∣ a*star a := prod ▸ dvd_mul_left _ _
  obtain ⟨d,e,da,ec,hde⟩ := exists_dvd_and_dvd_of_dvd_mul
    ((dvd_pow_self (z:GaussianInt) (by decide : 2≠0)).trans scalar)
  have sd : star d ∣ star a := map_dvd (starRingEnd GaussianInt) da
  have se : star e ∣ a := by
    have h := map_dvd (starRingEnd GaussianInt) ec
    simpa only [starRingEnd_apply,star_star] using h
  have rev : (z:GaussianInt)=star e*star d := by
    simpa only [star_natCast,star_mul] using congrArg star hde
  have cpd := cp.of_isCoprime_of_dvd_left da
  have cpe := cp.of_isCoprime_of_dvd_left se
  have dse : d ∣ star e :=
    (cpd.of_isCoprime_of_dvd_right sd).dvd_of_dvd_mul_right
      (rev ▸ hde.symm ▸ dvd_mul_right d e)
  have sed : star e ∣ d :=
    (cpe.of_isCoprime_of_dvd_right ec).dvd_of_dvd_mul_right
      (hde ▸ rev.symm ▸ dvd_mul_right (star e) (star d))
  have en : d.norm=e.norm := by
    simpa using Zsqrtd.norm_eq_of_associated (by decide : (-1:ℤ)≤0)
      (associated_of_dvd_dvd dse sed)
  have normZ := congrArg Zsqrtd.norm hde
  rw [Zsqrtd.norm_natCast,Zsqrtd.norm_mul,←en] at normZ
  have dn : d.norm=(z:ℤ) := (sq_eq_sq₀ (GaussianInt.norm_nonneg d) (by positivity)).mp
    (by simpa [pow_two] using normZ.symm)
  have d2 : d^2 ∣ a := cpd.pow_left.dvd_of_dvd_mul_right
    ((pow_dvd_pow_of_dvd (hde ▸ dvd_mul_right d e) 2).trans scalar)
  obtain ⟨B,hab⟩ := d2
  have n := congrArg Zsqrtd.norm hab
  simp only [Zsqrtd.norm_mul,pow_two,dn,he] at n
  have bn : B.norm=(b:ℤ) := by
    have zz : (z:ℤ)*(z:ℤ)≠0 := by positivity
    exact mul_right_cancel₀ zz (by linear_combination -n)
  exact ⟨B,d,hab.trans (mul_comm _ _),bn,dn⟩

private theorem cube_of_norm {a : GaussianInt} {b : ℕ} (hc : IsCoprime a (star a))
    (hn : a.norm=(b:ℤ)^3) : ∃ B : GaussianInt, a=B^3 ∧ B.norm=b := by
  have prod : a*star a=(b:GaussianInt)^3 := by
    rw [← Zsqrtd.norm_eq_mul_conj,hn]
    push_cast
    rfl
  obtain ⟨d,⟨u,hu⟩⟩ := exists_associated_pow_of_mul_eq_pow' hc prod
  let B := d*(u:GaussianInt)^3
  have cube : a=B^3 := by
    rw [←hu]
    dsimp [B]
    rw [mul_pow]
    have e := gunit_fourth u
    calc d^3*(u:GaussianInt) = d^3*(((u:GaussianInt)^4)^2*(u:GaussianInt)) := by rw [e]; ring
         _ = d^3*((u:GaussianInt)^3)^3 := by ring
  refine ⟨B,cube,(Odd.strictMono_pow (by decide : Odd 3)).injective ?_⟩
  rw [← hn,cube]
  simp [pow_succ]

/-- The condition b ∣ z gives the stronger factorization with Gaussian exponents 3 and 2. -/
theorem powerful_descent {b k x y : ℕ} (hb : Odd b) (hk : 0<k) (hc : x.Coprime y)
    (he : x^4+y^4=b^3*k^2) :
    ∃ B W : GaussianInt, (⟨(x:ℤ)^2,(y:ℤ)^2⟩ : GaussianInt)=B^3*W^2 ∧
      B.norm=b ∧ W.norm=k := by
  let a : GaussianInt := ⟨(x:ℤ)^2,(y:ℤ)^2⟩
  have cp : IsCoprime a (star a) :=
    quartic_coprime hc hb (he.trans (by ring : b^3*k^2=b*(b*k)^2))
  have hn : a.norm=((b^3:ℕ):ℤ)*(k:ℤ)^2 := by
    rw [quartic_norm,he]
    push_cast
    rfl
  obtain ⟨D,W,eq,dn,wn⟩ := strip_norm_square cp hk hn
  have da : D ∣ a := eq ▸ dvd_mul_right _ _
  have dc : star D ∣ star a := map_dvd (starRingEnd GaussianInt) da
  obtain ⟨B,cube,bn⟩ := cube_of_norm
    ((cp.of_isCoprime_of_dvd_left da).of_isCoprime_of_dvd_right dc) (by simpa using dn)
  exact ⟨B,W,eq.trans (by rw [cube]),bn,wn⟩

/-- Both coordinates of the Gaussian square class must be squares at every prime of b. -/
theorem local_square_coordinates {b p x y : ℕ} {B W : GaussianInt}
    (hp : p.Prime) (hpb : p∣b) (hc : x.Coprime y) (hd : p∣x^4+y^4)
    (hb : B.norm=b) (he : (⟨(x:ℤ)^2,(y:ℤ)^2⟩ : GaussianInt)=B*W^2) :
    ∃ t u : ZMod p, t^2=(B.re:ZMod p) ∧ u^2=(B.im:ZMod p) := by
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨m,n⟩ := B
  obtain ⟨r,s⟩ := W
  have hsum := (ZMod.natCast_eq_zero_iff _ p).mpr hd
  push_cast at hsum
  have nonzero (a c : ℕ) (cop : a.Coprime c)
      (h : (a:ZMod p)^4+(c:ZMod p)^4=0) : (a:ZMod p)≠0 := by
    intro ha
    have hz : (c:ZMod p)=0 := by simpa [ha] using h
    have d := Nat.dvd_gcd ((ZMod.natCast_eq_zero_iff a p).mp ha)
      ((ZMod.natCast_eq_zero_iff c p).mp hz)
    rw [show a.gcd c=1 from cop] at d
    exact hp.not_dvd_one d
  have hx := nonzero x y hc hsum
  have hy := nonzero y x hc.symm (by rwa [add_comm])
  have E := congrArg Zsqrtd.re he
  have F := congrArg Zsqrtd.im he
  simp [pow_two] at E F
  change m*m-(-1)*n*n=(b:ℤ) at hb
  have row : m*(x:ℤ)^2=(m*r-n*s)^2-(b:ℤ)*s^2 := by
    linear_combination m*E-s^2*hb
  have col : n*(y:ℤ)^2=(n*r+m*s)^2-(b:ℤ)*s^2 := by
    linear_combination n*F-s^2*hb
  have R := congrArg (fun v : ℤ => (v:ZMod p)) row
  have C := congrArg (fun v : ℤ => (v:ZMod p)) col
  have bz := (ZMod.natCast_eq_zero_iff b p).mpr hpb
  push_cast at R C
  simp only [bz,zero_mul,sub_zero] at R C
  refine ⟨((m:ZMod p)*r-n*s)/x,((n:ZMod p)*r+m*s)/y,?_,?_⟩
  · rw [div_pow,div_eq_iff (pow_ne_zero _ hx)]
    exact R.symm
  · rw [div_pow,div_eq_iff (pow_ne_zero _ hy)]
    exact C.symm

set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
private theorem obstructed_norm {b : ℕ} (bad :
    b ∈ ({1513,2329,2993,4369,4633,7081,7361,7769,8633,9809}:Finset ℕ)) {B : GaussianInt}
    (hn : B.norm=b) (hr : ∃ t : ZMod b.minFac, t^2=(B.re:ZMod b.minFac)) : False := by
  have tab : ∀ b ∈ ({1513,2329,2993,4369,4633,7081,7361,7769,8633,9809}:Finset ℕ),
      ∀ m : Fin 100, (b-m.val^2).sqrt^2=b-m.val^2 → m.val^2 ≤ b →
      ∀ w : Fin b.minFac, w.val^4%b.minFac ≠ m.val^2%b.minFac := by decide +kernel
  have hi : b<10000 := by
    have : ∀ v ∈ ({1513,2329,2993,4369,4633,7081,7361,7769,8633,9809}:Finset ℕ),
        v<10000 := by decide
    exact this b bad
  have sum : B.re.natAbs^2+B.im.natAbs^2=b := by
    change B.re*B.re-(-1)*B.im*B.im=(b:ℤ) at hn
    exact_mod_cast (show (B.re.natAbs:ℤ)^2+(B.im.natAbs:ℤ)^2=(b:ℤ) by
      simp only [Int.natCast_natAbs,sq_abs]; linear_combination hn)
  have mx : B.re.natAbs<100 := by
    by_contra! h
    have := Nat.pow_le_pow_left h 2
    omega
  have rem : b-B.re.natAbs^2=B.im.natAbs^2 := by omega
  have issq : (b-B.re.natAbs^2).sqrt^2=b-B.re.natAbs^2 := by rw [rem,Nat.sqrt_eq']
  have h := tab b bad ⟨_,mx⟩ issq (by dsimp; omega)
  let _ : NeZero b.minFac := ⟨(Nat.minFac_pos b).ne'⟩
  obtain ⟨t,ht⟩ := hr
  apply h ⟨t.val,ZMod.val_lt t⟩
  apply (ZMod.natCast_eq_natCast_iff' _ _ _).mp
  have ab := congrArg (fun v : ℤ => (v:ZMod b.minFac))
    (show (B.re.natAbs:ℤ)^2=B.re^2 by rw [Int.natCast_natAbs,sq_abs])
  push_cast
  rw [ZMod.natCast_zmod_val,show t^4=(t^2)^2 by ring,ht]
  simpa only [Int.cast_pow,Int.cast_natCast] using ab.symm

/-- These ten curves have no positive primitive point, with no size or b ∣ z assumption. -/
theorem ten_obstructions {b x y z : ℕ}
    (bad : b ∈ ({1513,2329,2993,4369,4633,7081,7361,7769,8633,9809}:Finset ℕ))
    (hx : 0<x) (hc : x.Coprime y) (he : x^4+y^4=b*z^2) : False := by
  have props : ∀ b ∈ ({1513,2329,2993,4369,4633,7081,7361,7769,8633,9809}:Finset ℕ),
      Odd b ∧ 1<b := by decide
  obtain ⟨odd,lo⟩ := props b bad
  have hz : 0<z := by
    by_contra! h
    rw [show z=0 by omega] at he
    simp at he
    omega
  have hn : (⟨(x:ℤ)^2,(y:ℤ)^2⟩ : GaussianInt).norm=(b:ℤ)*(z:ℤ)^2 := by
    rw [quartic_norm,he]
    push_cast
    rfl
  obtain ⟨B,W,fac,bn,_⟩ := strip_norm_square (quartic_coprime hc odd he) hz hn
  have pd := Nat.minFac_dvd b
  have div : b.minFac∣x^4+y^4 := he ▸ dvd_mul_of_dvd_left pd _
  obtain ⟨t,u,ht,_⟩ := local_square_coordinates (Nat.minFac_prime (by omega)) pd hc div bn fac
  exact obstructed_norm bad bn ⟨t,ht⟩

/-- The Pythagorean triple for U = x⁴+y⁴ and V = 2x²y² supplies a triangle
of area 2b after division by xyz(y⁴−x⁴). -/
theorem triangle_of_quartic {x y z b : ℚ} (hx : 0<x) (hxy : x<y) (hz : 0<z)
    (he : x^4+y^4=b*z^2) :
    ∃ a d c : ℚ, 0<a ∧ 0<d ∧ 0<c ∧ a^2+d^2=c^2 ∧ a*d=4*b := by
  let u := x^4+y^4
  let v := 2*x^2*y^2
  let w := y^4-x^4
  let t := x*y*z
  have hy := hx.trans hxy
  have hu : 0<u := by dsimp [u]; positivity
  have hv : 0<v := by dsimp [v]; positivity
  have hw : 0<w := sub_pos.mpr (pow_lt_pow_left₀ hxy hx.le (by decide : 4≠0))
  have ht : 0<t := by dsimp [t]; positivity
  have rel : w^2=u^2-v^2 := by dsimp [u,v,w]; ring
  have size : 2*u*v=4*b*t^2 := by dsimp [u,v,t]; rw [he]; ring
  refine ⟨w^2/(t*w), (2*u*v)/(t*w), (u^2+v^2)/(t*w), by positivity,
    by positivity, by positivity, ?_, ?_⟩
  · rw [div_pow,div_pow,div_pow,←add_div]
    apply congrArg (fun q : ℚ => q/(t*w)^2)
    rw [rel]; ring
  · rw [size]
    field_simp [ht.ne',hw.ne']

/-- An exact histogram of a list of exponents, stored in base q with no carries. -/
private theorem count_digit (q : ℕ) (xs : List ℕ) (b : ℕ) (hq : xs.length<q) :
    (xs.map (fun e => q^e)).sum / q^b % q = xs.count b := by
  let enc (s : List ℕ) := (s.map (fun e => q^e)).sum
  let down (s : List ℕ) := s.filterMap fun e => match e with
    | 0 => none
    | k+1 => some k
  have len (s : List ℕ) : (down s).length ≤ s.length := List.length_filterMap_le ..
  have split (s : List ℕ) : enc s=s.count 0+q*enc (down s) := by
    induction s with
    | nil => simp [enc,down]
    | cons a s ih =>
      change q^a+enc s=_
      cases a with
      | zero =>
        simp only [down,List.filterMap_cons,List.count_cons_self] at *
        rw [ih]
        simp [enc]
        omega
      | succ a =>
        simp only [down,List.filterMap_cons,List.count_cons, Nat.succ_ne_zero, beq_iff_eq,
          if_false, Nat.add_zero] at *
        rw [ih]
        simp [enc,pow_succ]
        ring
  have shift (s : List ℕ) (i : ℕ) : (down s).count i=s.count (i+1) := by
    induction s with
    | nil => rfl
    | cons a s ih =>
      cases a <;> simp [down,List.count_cons,down] at * <;> omega
  change enc xs/q^b%q=xs.count b
  induction b generalizing xs with
  | zero =>
    have c := (List.count_le_length (a:=0) (l:=xs)).trans_lt hq
    rw [pow_zero,Nat.div_one,split,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt c]
  | succ i ih =>
    have c := (List.count_le_length (a:=0) (l:=xs)).trans_lt hq
    have pos := (Nat.zero_le _).trans_lt hq
    have div : enc xs/q=enc (down xs) := by
      rw [split,Nat.add_mul_div_left _ _ pos,Nat.div_eq_of_lt c,zero_add]
    rw [pow_succ',←Nat.div_div_eq_div_mul,div,ih (down xs) ((len xs).trans_lt hq),shift]

private theorem grid_digit (q b : ℕ) (xs ys zs : List ℕ)
    (h : xs.length*ys.length*zs.length<q) :
    ((xs.flatMap fun x => ys.flatMap fun y => zs.map fun z => x+y+z).count b) =
    ((xs.map (fun i => q^i)).sum*(ys.map (fun i => q^i)).sum*(zs.map (fun i => q^i)).sum)
      /q^b%q := by
  let enc (s : List ℕ) := (s.map (fun n => q^n)).sum
  have add (k : ℕ) (s : List ℕ) : enc (s.map (fun n => k+n))=q^k*enc s := by
    induction s with
    | nil => simp [enc]
    | cons a s ih =>
      change q^(k+a)+enc (s.map (fun n => k+n))=q^k*(q^a+enc s)
      rw [pow_add,ih,mul_add]
  have pair (s t : List ℕ) : enc (s.flatMap fun i => t.map fun j => i+j)=enc s*enc t := by
    induction s with
    | nil => simp [enc]
    | cons a s ih =>
      simp only [List.flatMap_cons,enc,List.map_append,List.sum_append] at *
      rw [show ((t.map (fun j => a+j)).map (fun n => q^n)).sum=q^a*enc t from add a t,ih]
      simp [enc,add_mul]
  let grid := xs.flatMap fun x => ys.flatMap fun y => zs.map fun z => x+y+z
  have sizes (s t : List ℕ) (f : ℕ → ℕ → ℕ) :
      (s.flatMap fun x => t.map (f x)).length=s.length*t.length := by
    induction s with
    | nil => simp
    | cons a s ih => simp [ih,Nat.add_mul,Nat.add_comm]
  have glen : grid.length=xs.length*ys.length*zs.length := by
    dsimp only [grid]
    induction xs with
    | nil => simp
    | cons x xs ih => simp [sizes,Nat.add_mul]; ring
  have combined : grid=(xs.flatMap fun x => ys.map fun y => x+y).flatMap
      (fun s => zs.map fun z => s+z) := by
    simp [grid,List.flatMap_assoc,List.flatMap_map]
  rw [← count_digit q grid b (glen ▸ h)]
  change enc grid /q^b%q=_
  rw [combined,pair,pair]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem balance_bit {b : ℕ} (hi : b ≤ 10000) (eight : b%8=1)
    : (0x59000000404400400c01c009800090a300047c00880081a224525000460400844000020c11434141120000800404110830810c0240154806000002c0201001000211104811204009101308048100411e2640002401046081080c11401810804821c1010401400f100183500844068641429102000cc012018a16020411340cc300008a204112044183002080516100001905410060062509087004:ℕ).testBit (b/8)=decide (
      let row := fun c L : ℕ => (List.range (2*L+1)).map fun i => c*(i.dist L)^2
      let enc := fun s : List ℕ => (s.map (fun d => 2097152^d)).sum
      let A := enc (row 4 50)*enc (row 1 100)
      2*(A*enc (row 32 17)/2097152^b%2097152) =
        A*enc (row 8 35)/2097152^b%2097152) := by
  let q : ℕ := 2097152
  let stride := q^8
  let scan : ℕ → ℕ → ℕ → ℕ := Nat.rec (fun _ _ => 0) (fun _ f c d =>
    Nat.bit (decide (2*(c%q)=d%q)) (f (c/stride) (d/stride)))
  have spec (k c d j : ℕ) (lt : j < k) : (scan k c d).testBit j =
      decide (2*(c/stride^j%q)=d/stride^j%q) := by
    induction k generalizing c d j with
    | zero => omega
    | succ k ih =>
      cases j with
      | zero =>
        change (Nat.bit _ _).testBit 0=_
        rw [Nat.testBit_bit_zero]
        simp
      | succ j =>
        change (Nat.bit _ _).testBit (j+1)=_
        rw [Nat.testBit_bit_succ,ih _ _ j (by omega)]
        simp only [Nat.div_div_eq_div_mul,pow_succ']
  let row := fun c L : ℕ => (List.range (2*L+1)).map fun i => c*(i.dist L)^2
  let enc := fun s : List ℕ => (s.map (fun d => q^d)).sum
  let A := enc (row 4 50)*enc (row 1 100)
  let C := A*enc (row 32 17)
  let D := A*enc (row 8 35)
  have scanEq : scan 1250 (C/q) (D/q)=0x59000000404400400c01c009800090a300047c00880081a224525000460400844000020c11434141120000800404110830810c0240154806000002c0201001000211104811204009101308048100411e2640002401046081080c11401810804821c1010401400f100183500844068641429102000cc012018a16020411340cc300008a204112044183002080516100001905410060062509087004 := by decide +kernel
  have pw : q*stride^(b/8)=q^b := by
    dsimp only [stride]
    rw [←pow_mul,←pow_succ']
    exact congrArg (fun j : ℕ => q^j) (show 8*(b/8)+1=b by omega)
  rw [←scanEq,spec 1250 (C/q) (D/q) (b/8) (by omega)]
  simp only [Nat.div_div_eq_div_mul,pw]
  rfl

private theorem mod_eight {b : ℕ} (hb : Squarefree b)
    (hp : ∀ p ∈ b.primeFactors, p%8=1) : b%8=1 := by
  nth_rw 1 [← Nat.prod_primeFactors_of_squarefree hb]
  apply Finset.prod_induction _ (fun a : ℕ => a%8=1)
  · intro a c ha hc
    rw [Nat.mul_mod,ha,hc]
  · decide
  · exact hp

/-- Translate the finite signed-box count to its bit in the exact theta-series table. -/
private theorem signed_balance {b : ℕ} (hi : b ≤ 10000) (eight : b%8=1) :
    let row := fun c L : ℕ => (List.range (2*L+1)).map fun i => c*(i.dist L)^2
    let reps := fun c L : ℕ => (row 4 50).flatMap fun a =>
      (row 1 100).flatMap fun d => (row c L).map fun s => a+d+s
    (0x59000000404400400c01c009800090a300047c00880081a224525000460400844000020c11434141120000800404110830810c0240154806000002c0201001000211104811204009101308048100411e2640002401046081080c11401810804821c1010401400f100183500844068641429102000cc012018a16020411340cc300008a204112044183002080516100001905410060062509087004:ℕ).testBit (b/8)=decide (2*(reps 32 17).count b=(reps 8 35).count b) := by
  let row := fun c L : ℕ => (List.range (2*L+1)).map fun i => c*(i.dist L)^2
  let reps := fun c L : ℕ => (row 4 50).flatMap fun a =>
    (row 1 100).flatMap fun d => (row c L).map fun s => a+d+s
  let enc := fun s : List ℕ => (s.map (fun d => 2097152^d)).sum
  have count (c L : ℕ) (bound : 101*201*(2*L+1)<2097152) :
      (reps c L).count b =
        enc (row 4 50)*enc (row 1 100)*enc (row c L)/2097152^b%2097152 :=
    grid_digit _ _ _ _ _ (by simpa [row] using bound)
  change _ = decide (2*(reps 32 17).count b=(reps 8 35).count b)
  rw [count 32 17 (by decide),count 8 35 (by decide)]
  exact balance_bit hi eight

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
/-- The full arithmetic census and the exact list of 67 balanced parameters. -/
theorem small_census :
    let row := fun c L : ℕ => (List.range (2*L+1)).map fun i => c*(i.dist L)^2
    let reps := fun c L : ℕ => (row 4 50).flatMap fun a =>
      (row 1 100).flatMap fun d => (row c L).map fun s => a+d+s
    let good := fun b : ℕ => decide (1<b ∧ b ∉ ({4721,4777,6497,6577,9881}:Finset ℕ) ∧
      (∀ p ∈ b.primeFactors, p%8=1) ∧ Squarefree b)
    let params := ((List.range 1250).map fun j => 8*j+1).filter good
    params.length=324 ∧ params.filter (fun b => decide (2*(reps 32 17).count b=(reps 8 35).count b))
      =([17,97,113,193,257,337,433,577,593,641,673,881,929,1153,
      1217,1297,1409,1513,1777,1873,1889,1921,2129,2417,2657,2753,2801,2833,
      2897,2993,3121,3137,3329,3457,3649,3697,4001,4097,4129,4177,4289,4481,
      4561,4817,4993,5281,5617,5729,6353,6449,6481,6673,6817,7057,7361,7489,
      7537,7633,8017,8081,8633,8737,8753,9281,9553,9649,9857]:List ℕ) := by
  let row := fun c L : ℕ => (List.range (2*L+1)).map fun i => c*(i.dist L)^2
  let reps := fun c L : ℕ => (row 4 50).flatMap fun a =>
    (row 1 100).flatMap fun d => (row c L).map fun s => a+d+s
  let good := fun b : ℕ => decide (1<b ∧ b ∉ ({4721,4777,6497,6577,9881}:Finset ℕ) ∧
    (∀ p ∈ b.primeFactors, p%8=1) ∧ Squarefree b)
  let params := ((List.range 1250).map fun j => 8*j+1).filter good
  let bit := fun b : ℕ => (0x59000000404400400c01c009800090a300047c00880081a224525000460400844000020c11434141120000800404110830810c0240154806000002c0201001000211104811204009101308048100411e2640002401046081080c11401810804821c1010401400f100183500844068641429102000cc012018a16020411340cc300008a204112044183002080516100001905410060062509087004:ℕ).testBit (b/8)
  have counted : params.length=324 ∧ params.filter bit=([17,97,113,193,257,337,433,577,593,641,673,881,929,1153,
      1217,1297,1409,1513,1777,1873,1889,1921,2129,2417,2657,2753,2801,2833,
      2897,2993,3121,3137,3329,3457,3649,3697,4001,4097,4129,4177,4289,4481,
      4561,4817,4993,5281,5617,5729,6353,6449,6481,6673,6817,7057,7361,7489,
      7537,7633,8017,8081,8633,8737,8753,9281,9553,9649,9857]:List ℕ) := by decide +kernel
  refine ⟨counted.1,Eq.trans ?_ counted.2⟩
  apply List.filter_congr
  intro b hm
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp (List.mem_filter.mp hm).1
  have bound := List.mem_range.mp hj
  exact (signed_balance (b:=8*j+1) (by omega) (by omega)).symm

private theorem remaining_parameters {b : ℕ} (lo : 1<b) (hi : b≤10000) (sf : Squarefree b)
    (res : ∀ p ∈ b.primeFactors, p%8=1) (ne : b ∉ ({4721,4777,6497,6577,9881}:Finset ℕ))
    (balance :
      let row := fun c L : ℕ => (List.range (2*L+1)).map fun i => c*(i.dist L)^2
      let reps := fun c L : ℕ => (row 4 50).flatMap fun a =>
        (row 1 100).flatMap fun d => (row c L).map fun s => a+d+s
      2*(reps 32 17).count b=(reps 8 35).count b) :
    b ∈ ({1513,2993,7361,8633}:Finset ℕ) ∨
    b ∈ ([17,97,113,193,257,337,433,577,593,641,673,881,929,1153,
      1217,1297,1409,1777,1873,1889,2129,2417,2657,2753,2801,2833,2897,3121,
      3137,3329,3457,3697,4001,4129,4177,4289,4481,4561,4817,4993,5281,6353,
      6449,6481,6673,7057,7489,7537,8017,8081,8737,8753,9281,9649,9857]:List ℕ) ∨ b ∈ ([1921,3649,4097,5617,5729,6817,7633,9553]:List ℕ) := by
  have parts : ∀ k ∈ ([17,97,113,193,257,337,433,577,593,641,673,881,929,1153,
      1217,1297,1409,1513,1777,1873,1889,1921,2129,2417,2657,2753,2801,2833,
      2897,2993,3121,3137,3329,3457,3649,3697,4001,4097,4129,4177,4289,4481,
      4561,4817,4993,5281,5617,5729,6353,6449,6481,6673,6817,7057,7361,7489,
      7537,7633,8017,8081,8633,8737,8753,9281,9553,9649,9857]:List ℕ),
      k ∈ ({1513,2993,7361,8633}:Finset ℕ) ∨
      k ∈ ([17,97,113,193,257,337,433,577,593,641,673,881,929,1153,
      1217,1297,1409,1777,1873,1889,2129,2417,2657,2753,2801,2833,2897,3121,
      3137,3329,3457,3697,4001,4129,4177,4289,4481,4561,4817,4993,5281,6353,
      6449,6481,6673,7057,7489,7537,8017,8081,8737,8753,9281,9649,9857]:List ℕ) ∨ k ∈ ([1921,3649,4097,5617,5729,6817,7633,9553]:List ℕ) := by decide +kernel
  apply parts b
  have census := small_census.2
  rw [←census]
  apply List.mem_filter.mpr
  refine ⟨List.mem_filter.mpr ⟨?_,decide_eq_true ⟨lo,ne,res,sf⟩⟩,decide_eq_true balance⟩
  have eight := mod_eight sf res
  exact List.mem_map.mpr ⟨b/8,List.mem_range.mpr (by omega),by omega⟩

end Arithmetic

theorem main : H1 → H2 → H3 → OMA.R_mo_191889_R1.H1 := by
  intro tunnell primes composites b z x y lo hi ne sf res div hx le _ hc he size
  by_cases bad : b ∈ ({1513,2329,2993,4369,4633,7081,7361,7769,8633,9809}:Finset ℕ)
  · exact ten_obstructions bad hx hc he
  have eight := mod_eight sf res
  have hb : Odd b := Nat.odd_iff.mpr (by omega)
  have hz : 0<z := by
    by_contra! h
    rw [show z=0 by omega] at he
    simp at he
    omega
  have xy : x<y := by
    rcases lt_or_eq_of_le le with h|h
    · exact h
    subst y
    have one : x=1 := by simpa [Nat.Coprime] using hc
    rw [one] at he
    norm_num at he
    have bd : b∣2 := (show b∣b*z^2 from dvd_mul_right _ _).trans (dvd_of_eq he.symm)
    have ble := Nat.le_of_dvd (by decide : 0<2) bd
    omega
  have tri := triangle_of_quartic (x:=(x:ℚ)) (y:=(y:ℚ)) (z:=(z:ℚ)) (b:=(b:ℚ))
    (by exact_mod_cast hx) (by exact_mod_cast xy)
    (by exact_mod_cast hz) (by exact_mod_cast he)
  have cnt := tunnell b lo hi sf res ne bad tri
  obtain ⟨k,hk⟩ := div
  have kp : 0<k := by by_contra! h; rw [show k=0 by omega,mul_zero] at hk; omega
  have power : x^4+y^4=b^3*k^2 := by rw [he,hk]; ring
  obtain ⟨B,W,fac,bn,wn⟩ := powerful_descent hb kp hc power
  let a : GaussianInt := ⟨(x:ℤ)^2,(y:ℤ)^2⟩
  have sqfac : a=B*(B*W)^2 := fac.trans (by ring)
  have localSq (p : ℕ) (hp : p ∈ b.primeFactors) :
      ∃ t u : ZMod p, t^2=(B.re:ZMod p) ∧ u^2=(B.im:ZMod p) := by
    obtain ⟨pr,pd,_⟩ := Nat.mem_primeFactors.mp hp
    exact local_square_coordinates pr pd hc (he ▸ dvd_mul_of_dvd_left pd _) bn sqfac
  have common :
      (0<a.re → a.re ≤ a.im → IsSquare a.re → IsSquare a.im → a.re.natAbs.Coprime a.im.natAbs →
        a.norm < 3088257489493360278725196965477359217 → False) → False := by
    intro applyCase
    apply applyCase
    · change 0<(x:ℤ)^2
      positivity
    · change (x:ℤ)^2 ≤ (y:ℤ)^2
      exact_mod_cast Nat.pow_le_pow_left le 2
    · exact ⟨(x:ℤ),pow_two _⟩
    · exact ⟨(y:ℤ),pow_two _⟩
    · simpa [a] using (hc.pow_left 2).pow_right 2
    · rw [quartic_norm,he]
      exact_mod_cast size
  change a = B^3*W^2 at fac
  rw [fac] at common
  rcases remaining_parameters lo hi sf res ne cnt with h|h|h
  · have sub : ({1513,2993,7361,8633}:Finset ℕ) ⊆
        {1513,2329,2993,4369,4633,7081,7361,7769,8633,9809} := by decide
    exact bad (sub h)
  · exact common (primes b h B W bn localSq)
  · exact common (composites b h B W bn localSq)

end OMA.R_mo_191889_R1_H1_R1
