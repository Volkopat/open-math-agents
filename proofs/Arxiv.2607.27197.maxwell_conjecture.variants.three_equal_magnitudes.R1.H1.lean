import OMAReductions.R_Arxiv_2607_27197_maxwell_conjecture_variants_three_equal_magnitudes_R1
import Mathlib

/-!
# Three equal planar charges

At an equilibrium, let `a` and `b` be the distance to the third charge divided by the
respective distances to the first two. Force balance gives the squared side lengths as
ratios of homogeneous expressions in `a`, `b` and `1`. The sum `u = a + b` exceeds one.
For fixed triangle shape and fixed `u`, a strict inequality determines `(a-b)^2` uniquely.

Eliminating `(a-b)^2` gives a degree-34 polynomial. On choosing the longest side as base,
two shape parameters lie in the unit square. Integer Bernstein coefficients on a dyadic
subdivision of this square bound the sign variations of the polynomial shifted by one.
Descartes' rule bounds the positive roots with multiplicity. For a symmetric triangle the
eliminant factors as one diagonal factor times a square, accounting for reflected pairs.
-/

namespace OMA.MaxwellH1Astra

abbrev Plane := ℝ × ℝ

def ds (p q : Plane) : ℝ := (p.1-q.1)^2 + (p.2-q.2)^2

noncomputable def rad (p q : Plane) : ℝ := Real.sqrt (ds p q)

lemma rad_sq (p q : Plane) : rad p q ^ 2 = ds p q :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

structure Balance (p A B C : Plane) (a b : ℝ) : Prop where
  posa : 0 < a
  posb : 0 < b
  posc : 0 < ds p C
  ra : a^2 * ds p A = ds p C
  rb : b^2 * ds p B = ds p C
  ex : a^3*(p.1 - A.1) + b^3*(p.1 - B.1) + (p.1 - C.1) = 0
  ey : a^3*(p.2 - A.2) + b^3*(p.2 - B.2) + (p.2 - C.2) = 0

def sideWeight (a b c : ℝ) : ℝ := c^3 * ((a+b)*(a^3+b^3)-c^4)

private lemma pair_identity (p A B : Plane) (i j k l : ℝ)
    (hx : i*(p.1-A.1)+j*(p.1-B.1) = k) (hy : i*(p.2-A.2)+j*(p.2-B.2) = l) :
    i*j*ds A B = (i+j)*(i*ds p A+j*ds p B) - (k^2+l^2) := by
  rw [← hx, ← hy]; unfold ds; ring

lemma Balance.sides {p A B C : Plane} {a b : ℝ} (e : Balance p A B C a b) :
    (a*b)^3*ds A B = ds p C * sideWeight a b 1 ∧
    (a*b)^3*ds B C = ds p C * sideWeight b 1 a ∧
    (a*b)^3*ds A C = ds p C * sideWeight a 1 b := by
  have hAB := pair_identity p A B (a^3) (b^3) (-(p.1-C.1)) (-(p.2-C.2))
    (by linarith [e.ex]) (by linarith [e.ey])
  have hBC := pair_identity p B C (b^3) 1 (-(a^3*(p.1-A.1))) (-(a^3*(p.2-A.2)))
    (by linarith [e.ex]) (by linarith [e.ey])
  have hAC := pair_identity p A C (a^3) 1 (-(b^3*(p.1-B.1))) (-(b^3*(p.2-B.2)))
    (by linarith [e.ex]) (by linarith [e.ey])
  have hneg (r x y : ℝ) : (-(r*x))^2+(-(r*y))^2 = r^2*(x^2+y^2) := by ring
  simp only [neg_sq] at hAB
  rw [hneg] at hBC hAC
  change _ = _ - ds p C at hAB
  change _ = _ - (a^3)^2 * ds p A at hBC
  change _ = _ - (b^3)^2 * ds p B at hAC
  unfold sideWeight
  refine ⟨?_, ?_, ?_⟩
  · linear_combination hAB + (a^3+b^3)*(a*e.ra + b*e.rb)
  · linear_combination a^3*hBC + a^3 * (b*(b^3+1)*e.rb - a^4*e.ra)
  · linear_combination b^3*hAC + b^3 * (a*(a^3+1)*e.ra - b^4*e.rb)

lemma Balance.sum_gt_one {p A B C : Plane} {a b : ℝ} (e : Balance p A B C a b)
    (hAB : 0 < ds A B) : 1 < a+b := by
  have ha := e.posa
  have hb := e.posb
  have hprod : 0 < (a*b)^3 * ds A B := by positivity
  rw [e.sides.1] at hprod
  have h := (mul_pos_iff_of_pos_left e.posc).mp hprod
  simp only [sideWeight, one_pow, one_mul] at h
  by_contra! hle
  have hlt : a^3+b^3 < (a+b)^3 := by nlinarith [mul_pos (mul_pos ha hb) (add_pos ha hb)]
  have hc : (a+b)^3 ≤ 1^3 := pow_le_pow_left₀ (by positivity) hle 3
  nlinarith [mul_le_mul hle (hlt.le.trans hc) (by positivity : 0 ≤ a^3+b^3) (by norm_num : (0:ℝ) ≤ 1)]

lemma Balance.unique_point {p p' A B C : Plane} {a b : ℝ}
    (e : Balance p A B C a b) (e' : Balance p' A B C a b) : p = p' := by
  have ha := e.posa
  have hb := e.posb
  have h : a^3+b^3+1 ≠ 0 := by positivity
  apply Prod.ext
  · exact mul_left_cancel₀ h (by linear_combination e.ex-e'.ex)
  · exact mul_left_cancel₀ h (by linear_combination e.ey-e'.ey)

lemma Balance.diff_sq_bound {p A B C : Plane} {a b : ℝ} (e : Balance p A B C a b) :
    (a+b)^2 * (a-b)^2 ≤ 1 := by
  let X := a^3 * (p.1-A.1)
  let Y := a^3 * (p.2-A.2)
  let U := b^3 * (p.1-B.1)
  let V := b^3 * (p.2-B.2)
  let d := ds p C
  have ha : X^2+Y^2 = a^4*d := by
    have h := e.ra
    dsimp [X,Y,d]; unfold ds at h ⊢; linear_combination a^4*h
  have hb : U^2+V^2 = b^4*d := by
    have h := e.rb
    dsimp [U,V,d]; unfold ds at h ⊢; linear_combination b^4*h
  have hc : (X+U)^2 + (Y+V)^2 = d := by
    have h1 : X+U = -(p.1-C.1) := by dsimp [X,U]; linarith [e.ex]
    have h2 : Y+V = -(p.2-C.2) := by dsimp [Y,V]; linarith [e.ey]
    rw [h1,h2]; simp only [neg_sq]; rfl
  have hh : 0 ≤ ((a^2+b^2)^2-1)*(1-(a^2-b^2)^2) := by
    apply nonneg_of_mul_nonneg_left (b := d^2) _ (sq_pos_of_pos e.posc)
    have h : ((a^2+b^2)^2-1)*(1-(a^2-b^2)^2)*d^2 = 4*(X*V-Y*U)^2 := by
      calc _ = 4 * (a^4*d) * (b^4*d) - (d-(a^4*d)-(b^4*d))^2 := by ring
           _ = _ := by rw [← ha, ← hb, ← hc]; ring
    rw [h]; positivity
  have hd : (a+b)^2 * (a-b)^2 = (a^2-b^2)^2 := by ring
  rw [hd]
  by_contra! h
  have h' : 0 < (a^2+b^2)^2-1 := by nlinarith [sq_nonneg (a*b)]
  exact (not_lt_of_ge hh) (mul_neg_of_pos_of_neg h' (by linarith))

def num {R : Type*} [CommRing R] (u q : R) : R := q^3*(-4*u-1) + q^2*(-16*u^3+3*u^2-4) +
  q*(-12*u^5-3*u^4+24*u) + u^6+4*u^4+8*u^3

def den {R : Type*} [CommRing R] (u q : R) : R := 24*q*u^2+8*u^4-32

def dif {R : Type*} [CommRing R] (u q : R) : R := -12*q^2*u^2 + q*(-16*u^4-8*u+8) - 4*u^6+8*u^3+24*u^2

lemma weight_num (a b : ℝ) : num (a+b) ((a-b)^2) =
    32*(sideWeight b 1 a + sideWeight a 1 b) := by unfold num sideWeight; ring

lemma weight_den (a b : ℝ) : den (a+b) ((a-b)^2) = 32*sideWeight a b 1 := by
  unfold den sideWeight; ring

lemma weight_dif (a b : ℝ) : (a-b)*dif (a+b) ((a-b)^2) =
    32*(sideWeight b 1 a - sideWeight a 1 b) := by unfold dif sideWeight; ring

set_option maxHeartbeats 4000000 in
lemma num_den_separate (u q r : ℝ) (hu : 1 < u) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hq' : u^2*q ≤ 1) (hr' : u^2*r ≤ 1) (hqr : q < r) :
    num u r * den u q < num u q * den u r := by
  let t := u-1
  let x := u^2*q
  let y := u^2*r
  have ht : 0 < t := sub_pos.mpr hu
  have hx : 0 ≤ x := mul_nonneg (sq_nonneg _) hq
  have hy : 0 ≤ y := mul_nonneg (sq_nonneg _) hr
  have hx' : 0 ≤ 1-x := sub_nonneg.mpr hq'
  have hy' : 0 ≤ 1-y := sub_nonneg.mpr hr'
  let c00 : ℝ := (((((((((((((((((96 * t + 1680) * t + 13824) * t + 71136) * t + 256320) * t + 685056) * t + 1401600) * t + 2231328) * t + 2780160) * t + 2704992) * t + 2038272) * t + 1177632) * t + 522432) * t + 186624) * t + 60672) * t + 18912) * t + 4511) * t + 528)
  have hc00 : 0 ≤ c00 := by dsimp [c00]; positivity
  let c01 : ℝ := (((((((((((((((((96 * t + 1680) * t + 13824) * t + 71136) * t + 256384) * t + 685876) * t + 1406448) * t + 2248856) * t + 2823184) * t + 2779884) * t + 2131680) * t + 1259504) * t + 569376) * t + 199948) * t + 58160) * t + 15000) * t + 3055) * t + 324)
  have hc01 : 0 ≤ c01 := by dsimp [c01]; positivity
  let c02 : ℝ := ((((((((((((((((96 * t + 1680) * t + 13824) * t + 71136) * t + 256448) * t + 686696) * t + 1411296) * t + 2266384) * t + 2866240) * t + 2855072) * t + 2226304) * t + 1344288) * t + 620672) * t + 217192) * t + 57376) * t + 10992) * t + 1183) * t^1
  have hc02 : 0 ≤ c02 := by dsimp [c02]; positivity
  let c10 : ℝ := (((((((((((((((((96 * t + 1680) * t + 13824) * t + 71136) * t + 256384) * t + 685876) * t + 1406448) * t + 2248856) * t + 2823184) * t + 2779884) * t + 2131680) * t + 1259504) * t + 569376) * t + 199948) * t + 58160) * t + 15000) * t + 3055) * t + 324)
  have hc10 : 0 ≤ c10 := by dsimp [c10]; positivity
  let c11 : ℝ := (((((((((((((((((96 * t + 1680) * t + 13824) * t + 71136) * t + 256448) * t + 686696) * t + 1411296) * t + 2266384) * t + 2866312) * t + 2855696) * t + 2228704) * t + 1349688) * t + 628640) * t + 225448) * t + 63616) * t + 14376) * t + 2359) * t + 192)
  have hc11 : 0 ≤ c11 := by dsimp [c11]; positivity
  let c12 : ℝ := ((((((((((((((((96 * t + 1680) * t + 13824) * t + 71136) * t + 256512) * t + 687516) * t + 1416144) * t + 2283912) * t + 2909472) * t + 2931804) * t + 2326944) * t + 1442784) * t + 692304) * t + 255120) * t + 71328) * t + 14208) * t + 1535) * t^1
  have hc12 : 0 ≤ c12 := by dsimp [c12]; positivity
  let c20 : ℝ := ((((((((((((((((96 * t + 1680) * t + 13824) * t + 71136) * t + 256448) * t + 686696) * t + 1411296) * t + 2266384) * t + 2866240) * t + 2855072) * t + 2226304) * t + 1344288) * t + 620672) * t + 217192) * t + 57376) * t + 10992) * t + 1183) * t^1
  have hc20 : 0 ≤ c20 := by dsimp [c20]; positivity
  let c21 : ℝ := ((((((((((((((((96 * t + 1680) * t + 13824) * t + 71136) * t + 256512) * t + 687516) * t + 1416144) * t + 2283912) * t + 2909472) * t + 2931804) * t + 2326944) * t + 1442784) * t + 692304) * t + 255120) * t + 71328) * t + 14208) * t + 1535) * t^1
  have hc21 : 0 ≤ c21 := by dsimp [c21]; positivity
  let c22 : ℝ := ((((((((((((((((96 * t + 1680) * t + 13824) * t + 71136) * t + 256576) * t + 688336) * t + 1420992) * t + 2301440) * t + 2952736) * t + 3008832) * t + 2428800) * t + 1544192) * t + 768384) * t + 297472) * t + 88064) * t + 18432) * t + 2047) * t^1
  have hc22 : 0 ≤ c22 := by dsimp [c22]; positivity
  let s0 := 1*c00*x^0*(1-x)^2*y^0*(1-y)^2 +
    2*c01*x^0*(1-x)^2*y^1*(1-y)^1 +
    1*c02*x^0*(1-x)^2*y^2*(1-y)^0 +
    2*c10*x^1*(1-x)^1*y^0*(1-y)^2 +
    4*c11*x^1*(1-x)^1*y^1*(1-y)^1 +
    2*c12*x^1*(1-x)^1*y^2*(1-y)^0 +
    1*c20*x^2*(1-x)^0*y^0*(1-y)^2 +
    2*c21*x^2*(1-x)^0*y^1*(1-y)^1 +
    1*c22*x^2*(1-x)^0*y^2*(1-y)^0
  have hs0 : 0 ≤ s0 := by dsimp only [s0]; positivity
  have hi : (num u q*den u r-num u r*den u q)*u^8 = (r-q)*(t+s0) := by
    dsimp only [num,den,t,s0,x,y,c00,c01,c02,c10,c11,c12,c20,c21,c22]; ring
  have hp : 0 < (num u q * den u r - num u r * den u q)*u^8 := by
    rw [hi]; exact mul_pos (sub_pos.mpr hqr) (add_pos_of_pos_of_nonneg ht hs0)
  exact sub_pos.mp (pos_of_mul_pos_left hp (by positivity))

def b50 {R : Type*} [CommRing R] (u : R) : R := -23328*u^16 + 93312*u^12
def b40 {R : Type*} [CommRing R] (u : R) : R := 3456*u^22 + 10368*u^19 - 34236*u^18 + 27216*u^16 - 7776*u^15 + 98496*u^14 + 1728*u^13 - 64800*u^12 - 41472*u^11 - 19872*u^10 - 6912*u^9 + 10368*u^8 - 3456*u^6
def b31 {R : Type*} [CommRing R] (u : R) : R := -3456*u^22 - 10368*u^19 + 13824*u^18 + 10368*u^16 - 4536*u^15 - 23004*u^14 + 864*u^13 - 101736*u^12 + 50544*u^11 + 23112*u^10 - 3456*u^9 - 38880*u^8 - 25920*u^7 - 4320*u^6
def b30 {R : Type*} [CommRing R] (u : R) : R := -128*u^28 - 768*u^25 + 3536*u^24 - 7488*u^22 + 1008*u^21 - 20580*u^20 - 8768*u^19 + 34968*u^18 + 18768*u^17 + 31544*u^16 - 8632*u^15 - 70572*u^14 - 39648*u^13 - 5036*u^12 + 11040*u^11 + 30064*u^10 + 13632*u^9 - 2664*u^8 - 1568*u^7 + 176*u^6 + 384*u^5 + 664*u^4 + 128*u^3 - 192*u^2 + 32
def b22 {R : Type*} [CommRing R] (u : R) : R := -1728*u^13 - 1296*u^12 - 324*u^11 - 27*u^10 + 6912*u^9 + 5184*u^8 + 1296*u^7 + 108*u^6
def b21 {R : Type*} [CommRing R] (u : R) : R := -3024*u^24 - 1728*u^22 - 6480*u^21 + 13392*u^20 - 10176*u^19 + 22608*u^18 - 11628*u^17 - 40686*u^16 + 38184*u^15 - 90864*u^14 + 58248*u^13 + 72780*u^12 + 20448*u^11 - 35994*u^10 - 26532*u^9 - 1674*u^8 + 24264*u^7 + 21432*u^6 + 6552*u^5 + 1092*u^4 - 288*u^3 - 576*u^2 - 288*u - 48
def b20 {R : Type*} [CommRing R] (u : R) : R := -112*u^30 + 320*u^28 - 32*u^27 + 1200*u^26 + 1152*u^25 - 3696*u^24 - 3504*u^23 - 1287*u^22 + 1536*u^21 + 15264*u^20 + 16032*u^19 - 496*u^18 - 16932*u^17 - 30598*u^16 - 11912*u^15 + 11898*u^14 + 18432*u^13 + 18412*u^12 + 6876*u^11 - 5627*u^10 - 5900*u^9 - 2706*u^8 - 808*u^7 + 649*u^6 + 336*u^5 - 252*u^4 - 120*u^3
def b12 {R : Type*} [CommRing R] (u : R) : R := 2688*u^22 - 672*u^21 - 336*u^20 + 8448*u^19 - 12288*u^18 + 1920*u^17 + 8580*u^16 - 1608*u^15 + 14172*u^14 - 3060*u^13 + 22296*u^12 - 29136*u^11 - 5616*u^10 + 5064*u^9 + 25644*u^8 + 9216*u^7 - 6480*u^6 - 948*u^5 + 4056*u^4 + 3360*u^3 + 1368*u^2 + 288*u + 24
def b11 {R : Type*} [CommRing R] (u : R) : R := -128*u^28 - 480*u^27 - 672*u^26 + 1152*u^25 - 2032*u^24 + 1440*u^23 + 10728*u^22 - 6288*u^21 + 7812*u^20 + 5880*u^19 - 26040*u^18 + 8256*u^17 - 1940*u^16 + 9744*u^15 + 40488*u^14 - 3900*u^13 - 22084*u^12 - 8148*u^11 - 6088*u^10 + 11736*u^9 + 13212*u^8 - 320*u^7 - 5756*u^6 - 4476*u^5 - 2208*u^4 - 316*u^3 + 384*u^2 + 144*u
def b10 {R : Type*} [CommRing R] (u : R) : R := -16*u^32 + 160*u^30 + 224*u^29 - 140*u^28 - 352*u^27 - 1056*u^26 - 1924*u^25 + 880*u^24 + 3856*u^23 + 3636*u^22 + 2112*u^21 - 3992*u^20 - 8820*u^19 - 5792*u^18 + 600*u^17 + 6560*u^16 + 7912*u^15 + 4196*u^14 - 960*u^13 - 3868*u^12 - 3028*u^11 - 1240*u^10 - 52*u^9 + 576*u^8 + 432*u^7 + 96*u^6
def b03 {R : Type*} [CommRing R] (u : R) : R := -256*u^19 - 192*u^18 - 48*u^17 - 772*u^16 + 448*u^15 + 624*u^14 - 396*u^13 - 416*u^12 - 1644*u^11 - 1161*u^10 - 2592*u^9 + 552*u^8 + 2320*u^7 + 1164*u^6 - 2076*u^5 - 3248*u^4 - 1840*u^3 - 516*u^2 - 72*u - 4
def b02 {R : Type*} [CommRing R] (u : R) : R := -768*u^25 + 2160*u^24 - 736*u^23 - 2868*u^22 + 8560*u^21 - 11152*u^20 - 800*u^19 + 3308*u^18 - 3684*u^17 + 12074*u^16 - 14120*u^15 + 24952*u^14 - 27372*u^13 - 8628*u^12 - 8348*u^11 + 19062*u^10 + 9268*u^9 - 7914*u^8 - 8272*u^7 - 3140*u^6 - 556*u^5 - 1140*u^4 - 1276*u^3 - 580*u^2 - 136*u - 16
def b01 {R : Type*} [CommRing R] (u : R) : R := 16*u^30 - 240*u^29 + 52*u^28 + 704*u^27 - 480*u^26 + 276*u^25 + 2016*u^24 - 1728*u^23 - 3141*u^22 + 1440*u^21 - 1656*u^20 - 2124*u^19 + 4720*u^18 + 1692*u^17 + 2458*u^16 - 4792*u^15 - 9642*u^14 - 816*u^13 + 2336*u^12 + 2472*u^11 + 3131*u^10 - 1216*u^9 - 2634*u^8 - 1280*u^7 - 829*u^6 + 240*u^5 + 684*u^4 + 216*u^3
def b00 {R : Type*} [CommRing R] (u : R) : R := 4*u^34 + 24*u^31 - 64*u^30 - 144*u^29 + 4*u^28 + 96*u^27 + 360*u^26 + 608*u^25 - 16*u^24 - 624*u^23 - 880*u^22 - 992*u^21 + 24*u^20 + 1056*u^19 + 1060*u^18 + 768*u^17 - 16*u^16 - 744*u^15 - 624*u^14 - 272*u^13 + 4*u^12 + 192*u^11 + 144*u^10 + 32*u^9

def elim (u L M : ℝ) : ℝ :=
  b50 u * L^5 * M^0 +
  b40 u * L^4 * M^0 +
  b31 u * L^3 * M^1 +
  b30 u * L^3 * M^0 +
  b22 u * L^2 * M^2 +
  b21 u * L^2 * M^1 +
  b20 u * L^2 * M^0 +
  b12 u * L^1 * M^2 +
  b11 u * L^1 * M^1 +
  b10 u * L^1 * M^0 +
  b03 u * L^0 * M^3 +
  b02 u * L^0 * M^2 +
  b01 u * L^0 * M^1 +
  b00 u * L^0 * M^0

def clearElim {R : Type*} [CommRing R] (u n m d : R) : R :=
  b50 u * n^5 * m^0 * d^1 +
  b40 u * n^4 * m^0 * d^2 +
  b31 u * n^3 * m^1 * d^1 +
  b30 u * n^3 * m^0 * d^3 +
  b22 u * n^2 * m^2 * d^0 +
  b21 u * n^2 * m^1 * d^2 +
  b20 u * n^2 * m^0 * d^4 +
  b12 u * n^1 * m^2 * d^1 +
  b11 u * n^1 * m^1 * d^3 +
  b10 u * n^1 * m^0 * d^5 +
  b03 u * n^0 * m^3 * d^0 +
  b02 u * n^0 * m^2 * d^2 +
  b01 u * n^0 * m^1 * d^4 +
  b00 u * n^0 * m^0 * d^6

lemma clear_elim (u L M n m d : ℝ) (hn : L*d=n) (hm : M*d^2=m) :
    elim u L M * d^6 = clearElim u n m d := by
  rw [← hn, ← hm]; unfold elim clearElim; ring

/- The identity has degree at most 58 in the sum and 16 in the squared difference.
Integer evaluations on a 59 by 17 grid certify it by univariate interpolation in each variable. -/
namespace Grid

def expanded {R : Type*} [CommRing R] (u q : R) : R :=
  clearElim u (num u q) (q*dif u q^2) (den u q)

set_option maxHeartbeats 1500000 in
lemma map_expanded {R S : Type*} [CommRing R] [CommRing S] (h : R →+* S) (u q : R) : h (expanded u q) = expanded (h u) (h q) := by
  simp [map_ofNat, expanded, num, den, dif, b50, b40, b31, b30, b22, b21, b20, b12, b11, b10, b03, b02, b01, b00, clearElim]

open Polynomial

set_option maxHeartbeats 4000000 in
lemma deg_u (q : ℝ) : (expanded X (C q)).natDegree ≤ 58 := by
  unfold expanded clearElim b00 b01 b02 b03 b10 b11 b12 b20 b21 b22 b30 b31 b40 b50 dif den num
  compute_degree

set_option maxHeartbeats 4000000 in
lemma deg_q (u : ℝ) : (expanded (C u) X).natDegree ≤ 16 := by
  unfold expanded clearElim b00 b01 b02 b03 b10 b11 b12 b20 b21 b22 b30 b31 b40 b50 dif den num
  compute_degree

set_option maxRecDepth 10000 in
lemma line0 : ∀ i : Fin 59, expanded (i:ℤ) 0 = 0 := by decide +kernel

set_option maxRecDepth 10000 in
lemma line1 : ∀ i : Fin 59, expanded (i:ℤ) 1 = 0 := by decide +kernel

set_option maxRecDepth 10000 in
lemma line2 : ∀ i : Fin 59, expanded (i:ℤ) 2 = 0 := by decide +kernel

set_option maxRecDepth 10000 in
lemma line3 : ∀ i : Fin 59, expanded (i:ℤ) 3 = 0 := by decide +kernel

set_option maxRecDepth 10000 in
lemma line4 : ∀ i : Fin 59, expanded (i:ℤ) 4 = 0 := by decide +kernel

set_option maxRecDepth 10000 in
lemma line5 : ∀ i : Fin 59, expanded (i:ℤ) 5 = 0 := by decide +kernel

set_option maxRecDepth 10000 in
lemma line6 : ∀ i : Fin 59, expanded (i:ℤ) 6 = 0 := by decide +kernel

set_option maxRecDepth 10000 in
lemma line7 : ∀ i : Fin 59, expanded (i:ℤ) 7 = 0 := by decide +kernel

set_option maxRecDepth 10000 in
lemma line8 : ∀ i : Fin 59, expanded (i:ℤ) 8 = 0 := by decide +kernel

set_option maxRecDepth 10000 in
lemma line9 : ∀ i : Fin 59, expanded (i:ℤ) 9 = 0 := by decide +kernel

set_option maxRecDepth 10000 in
lemma line10 : ∀ i : Fin 59, expanded (i:ℤ) 10 = 0 := by decide +kernel

set_option maxRecDepth 10000 in
lemma line11 : ∀ i : Fin 59, expanded (i:ℤ) 11 = 0 := by decide +kernel

set_option maxRecDepth 10000 in
lemma line12 : ∀ i : Fin 59, expanded (i:ℤ) 12 = 0 := by decide +kernel

set_option maxRecDepth 10000 in
lemma line13 : ∀ i : Fin 59, expanded (i:ℤ) 13 = 0 := by decide +kernel

set_option maxRecDepth 10000 in
lemma line14 : ∀ i : Fin 59, expanded (i:ℤ) 14 = 0 := by decide +kernel

set_option maxRecDepth 10000 in
lemma line15 : ∀ i : Fin 59, expanded (i:ℤ) 15 = 0 := by decide +kernel

set_option maxRecDepth 10000 in
lemma line16 : ∀ i : Fin 59, expanded (i:ℤ) 16 = 0 := by decide +kernel

lemma grid (i : Fin 59) (j : Fin 17) : expanded (i:ℤ) (j:ℤ) = 0 := by
  fin_cases j
  · exact line0 i
  · exact line1 i
  · exact line2 i
  · exact line3 i
  · exact line4 i
  · exact line5 i
  · exact line6 i
  · exact line7 i
  · exact line8 i
  · exact line9 i
  · exact line10 i
  · exact line11 i
  · exact line12 i
  · exact line13 i
  · exact line14 i
  · exact line15 i
  · exact line16 i

private lemma fin_real_inj {n : ℕ} : Function.Injective (fun i : Fin n => (i:ℝ)) := by
  intro i j h; apply Fin.ext; change ((i:ℕ):ℝ) = ((j:ℕ):ℝ) at h; exact_mod_cast h

lemma expanded_zero (u q : ℝ) : expanded u q = 0 := by
  have he (i : Fin 59) (j : Fin 17) : expanded (i:ℝ) (j:ℝ) = 0 := by
    have h := congrArg (Int.castRingHom ℝ) (grid i j)
    rw [map_expanded] at h; simpa using h
  have h1 (j : Fin 17) : expanded X (C (j:ℝ)) = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (@fin_real_inj 59) (fun i => ?_) ?_
    · change (evalRingHom (i:ℝ)) _ = _
      rw [map_expanded]; simpa using he i j
    · simpa using (Nat.lt_succ_of_le (deg_u j))
  have h2 : expanded (C u) X = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (@fin_real_inj 17) (fun j => ?_) ?_
    · have H := congrArg (evalRingHom u) (h1 j)
      rw [map_expanded] at H
      change (evalRingHom (j:ℝ)) _ = _
      rw [map_expanded]; simpa using H
    · simpa using (Nat.lt_succ_of_le (deg_q u))
  have H := congrArg (evalRingHom q) h2
  rw [map_expanded] at H; simpa using H

end Grid

lemma clearElim_eq_zero (u q : ℝ) :
    clearElim u (num u q) (q * dif u q ^ 2) (den u q) = 0 := Grid.expanded_zero u q

lemma elim_eq_zero (u q L M : ℝ) (hd : den u q ≠ 0)
    (hl : L*den u q=num u q) (hm : M*den u q^2=q*dif u q^2) : elim u L M = 0 := by
  apply (mul_eq_zero.mp _).resolve_right (pow_ne_zero 6 hd)
  rw [clear_elim _ _ _ _ _ _ hl hm,clearElim_eq_zero]

noncomputable def ratioA (p A C : Plane) : ℝ := rad p C / rad p A

def Equil (p A B C : Plane) : Prop :=
  ds p A ≠ 0 ∧ ds p B ≠ 0 ∧ ds p C ≠ 0 ∧
  (p.1-A.1)/rad p A^3 + (p.1-B.1)/rad p B^3 + (p.1-C.1)/rad p C^3 = 0 ∧
  (p.2-A.2)/rad p A^3 + (p.2-B.2)/rad p B^3 + (p.2-C.2)/rad p C^3 = 0

lemma equil_balance {p A B C : Plane} (e : Equil p A B C) :
    Balance p A B C (ratioA p A C) (ratioA p B C) := by
  obtain ⟨eA,eB,eC,ex,ey⟩ := e
  have rp (X : Plane) (hX : ds p X ≠ 0) : 0 < rad p X := by
    apply Real.sqrt_pos.mpr
    exact (add_nonneg (sq_nonneg _) (sq_nonneg _)).lt_of_ne hX.symm
  have ha := rp A eA
  have hb := rp B eB
  have hc := rp C eC
  unfold ratioA
  refine ⟨div_pos hc ha,div_pos hc hb,by rw [← rad_sq]; positivity,?_,?_,?_,?_⟩
  · rw [← rad_sq, ← rad_sq]; field_simp
  · rw [← rad_sq, ← rad_sq]; field_simp
  · calc _ = rad p C^3 * ((p.1-A.1)/rad p A^3 + (p.1-B.1)/rad p B^3 + (p.1-C.1)/rad p C^3) := by field_simp
         _ = 0 := by rw [ex,mul_zero]
  · calc _ = rad p C^3 * ((p.2-A.2)/rad p A^3 + (p.2-B.2)/rad p B^3 + (p.2-C.2)/rad p C^3) := by field_simp
         _ = 0 := by rw [ey,mul_zero]

noncomputable def shapeL (A B C : Plane) := (ds B C + ds A C) / ds A B
noncomputable def shapeJ (A B C : Plane) := (ds B C - ds A C) / ds A B

lemma Balance.shape {p A B C : Plane} {a b : ℝ} (e : Balance p A B C a b)
    (hAB : 0 < ds A B) :
    0 < den (a+b) ((a-b)^2) ∧
    shapeL A B C * den (a+b) ((a-b)^2) = num (a+b) ((a-b)^2) ∧
    shapeJ A B C * den (a+b) ((a-b)^2) = (a-b)*dif (a+b) ((a-b)^2) := by
  obtain ⟨h0,h1,h2⟩ := e.sides
  have hp := e.posc
  have ha := e.posa
  have hb := e.posb
  rw [weight_num,weight_den,weight_dif]
  have hw : 0 < sideWeight a b 1 := (mul_pos_iff_of_pos_left hp).mp (h0 ▸ (by positivity))
  refine ⟨by positivity,?_,?_⟩
  · unfold shapeL; field_simp
    apply mul_left_cancel₀ hp.ne'
    linear_combination (ds B C + ds A C)*(-h0)+ds A B*(h1+h2)
  · unfold shapeJ; field_simp
    apply mul_left_cancel₀ hp.ne'
    linear_combination (ds B C - ds A C)*(-h0)+ds A B*(h1-h2)

lemma Balance.eliminant {p A B C : Plane} {a b : ℝ} (e : Balance p A B C a b)
    (hAB : 0 < ds A B) : elim (a+b) (shapeL A B C) ((shapeJ A B C)^2) = 0 := by
  obtain ⟨hd, hL, hJ⟩ := e.shape hAB
  apply elim_eq_zero _ _ _ _ hd.ne' hL
  rw [← mul_pow, hJ, mul_pow]

lemma same_diff_sq {u q r L : ℝ} (hu : 1 < u) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hq' : u^2*q ≤ 1) (hr' : u^2*r ≤ 1)
    (h : L * den u q = num u q) (h' : L * den u r = num u r) : q = r := by
  rcases lt_trichotomy q r with hqr | hqr | hrq
  · have hlt := num_den_separate _ _ _ hu hq hr hq' hr' hqr
    rw [← h, ← h'] at hlt; linarith only [show L*den u r*den u q = L*den u q*den u r by ring,hlt]
  · exact hqr
  · have hlt := num_den_separate _ _ _ hu hr hq hr' hq' hrq
    rw [← h, ← h'] at hlt; linarith only [show L*den u r*den u q = L*den u q*den u r by ring,hlt]

lemma unique_sum {p p' A B C : Plane} {a b a' b' : ℝ}
    (hAB : 0 < ds A B) (e : Balance p A B C a b) (e' : Balance p' A B C a' b')
    (hs : a+b = a'+b') (hJ : shapeJ A B C ≠ 0) : p=p' := by
  obtain ⟨hd,hL,h⟩ := e.shape hAB
  obtain ⟨_,hL',h'⟩ := e'.shape hAB
  have he' := e'.diff_sq_bound
  rw [← hs] at hL' h' he'
  have hq := same_diff_sq (e.sum_gt_one hAB) (sq_nonneg _) (sq_nonneg _) e.diff_sq_bound he' hL hL'
  rw [← hq] at h'
  have hn : dif (a+b) ((a-b)^2) ≠ 0 := by
    intro hz; rw [hz,mul_zero] at h; exact mul_ne_zero hJ hd.ne' h
  have hh := mul_right_cancel₀ hn (h.symm.trans h')
  have aa : a = a' := by linarith
  have bb : b = b' := by linarith
  subst a'; subst b'; exact e.unique_point e'

lemma choose_chart {A B C : Plane} (hc : 0 < ds A B) (ha : 0 < ds B C) (hb : 0 < ds A C)
    (h₁ : ds B C ≤ ds A B) (h₂ : ds A C ≤ ds A B) :
    ∃ x v : ℝ, 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ v ∧ v ≤ 1 ∧
      shapeL A B C = (1+x^2+v*(3-2*x-x^2))/2 ∧ (shapeJ A B C)^2=x^2 := by
  let aa := ds B C / ds A B
  let bb := ds A C / ds A B
  let x := |aa-bb|
  have hap : 0 < aa := div_pos ha hc
  have hbp : 0 < bb := div_pos hb hc
  have ha1 : aa ≤ 1 := (div_le_one hc).mpr h₁
  have hb1 : bb ≤ 1 := (div_le_one hc).mpr h₂
  have hx : 0 ≤ x := abs_nonneg _
  have hx1 : x < 1 := abs_lt.mpr ⟨by linarith,by linarith⟩
  have hh : aa+bb+x ≤ 2 := by
    dsimp only [x]; rcases le_total aa bb with h|h
    · rw [abs_of_nonpos (sub_nonpos.mpr h)]; linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]; linarith
  have hs : x^2=(aa-bb)^2 := sq_abs _
  have hl : shapeL A B C = aa + bb := by unfold shapeL aa bb; ring
  have hj : shapeJ A B C = aa - bb := by unfold shapeJ aa bb; ring
  have harea : 0 ≤ 2*(aa+bb)-1-x^2 := by
    rw [hs]; dsimp only [aa,bb]
    have he : (2*(ds B C / ds A B + ds A C / ds A B) - 1 - (ds B C/ds A B-ds A C/ds A B)^2)*ds A B^2 =
        4*((A.1-C.1)*(B.2-C.2)-(A.2-C.2)*(B.1-C.1))^2 := by
      field_simp; unfold ds; ring
    apply nonneg_of_mul_nonneg_left (b := ds A B^2) _ (by positivity)
    rw [he]; positivity
  have hd : 0 < 3-2*x-x^2 := by nlinarith [mul_pos (sub_pos.mpr hx1) (show 0 < 3+x by linarith)]
  let v := (2*(aa+bb)-1-x^2)/(3-2*x-x^2)
  refine ⟨x,v,hx,hx1.le,div_nonneg harea hd.le,(div_le_one hd).mpr (by linarith),?_,?_⟩
  · rw [hl]; dsimp only [v]; rw [div_mul_cancel₀ _ hd.ne']; ring
  · rw [hj,hs]

/- Homogeneous Bernstein representations and the sign-variation bound. -/

abbrev Table := Array (Array ℤ)

def entry (p : Table) (i j : ℕ) : ℤ := (p[i]?.getD #[])[j]?.getD 0

def mon (d i : ℕ) (x y : ℝ) : ℝ := x^i*y^(d-i)

def value (p : Table) (x y v w : ℝ) : ℝ :=
  ∑ i : Fin 11, ∑ j : Fin 6, (entry p i j : ℝ) * mon 10 i x y * mon 5 j v w

def tx (m p : Table) : Table := Array.ofFn fun i : Fin 11 => Array.ofFn fun j : Fin 6 =>
  (List.ofFn (fun k : Fin 11 => entry m i k * entry p k j)).sum

def ty (m p : Table) : Table := Array.ofFn fun i : Fin 11 => Array.ofFn fun j : Fin 6 =>
  (List.ofFn (fun k : Fin 6 => entry m j k * entry p i k)).sum

private lemma entry_tx (m p : Table) (i : Fin 11) (j : Fin 6) :
    entry (tx m p) i j = ∑ k : Fin 11, entry m i k * entry p k j := by
  simp [tx,entry, i.isLt,j.isLt,Fin.sum_univ_succ]

private lemma entry_ty (m p : Table) (i : Fin 11) (j : Fin 6) :
    entry (ty m p) i j = ∑ k : Fin 6, entry m j k * entry p i k := by
  simp [ty,entry, i.isLt,j.isLt,Fin.sum_univ_succ]

lemma tx_spec (m p : Table) (x y v w X Y : ℝ)
    (h : ∀ k : Fin 11, mon 10 k X Y = ∑ i : Fin 11,(entry m i k : ℝ)*mon 10 i x y) :
    value p X Y v w = value (tx m p) x y v w := by
  unfold value
  simp_rw [h,entry_tx,Int.cast_sum,Int.cast_mul,Finset.mul_sum,Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]; enter [2,j]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro i _; ring

lemma ty_spec (m p : Table) (x y v w V W : ℝ)
    (h : ∀ k : Fin 6, mon 5 k V W = ∑ i : Fin 6,(entry m i k : ℝ)*mon 5 i v w) :
    value p x y V W = value (ty m p) x y v w := by
  unfold value
  simp_rw [h,entry_ty,Int.cast_sum,Int.cast_mul,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _; ring

inductive Mark where
  | up | down | both
  deriving DecidableEq

def Mark.fits : Mark → ℝ → Prop
  | .up, c => 0 ≤ c
  | .down, c => c ≤ 0
  | .both, _ => True

def bounds : List Mark → ℕ × ℕ
  | [] => (0,0)
  | m::ms =>
    let (p,n) := bounds ms
    match m with
    | .up => (p,max n (p+1))
    | .down => (max p (n+1), n)
    | .both => (max p (n+1),max n (p+1))

private noncomputable def signs (cs : List ℝ) := (cs.map SignType.sign).filter (· ≠ 0)

private lemma signs_bound {ms : List Mark} {cs : List ℝ}
    (h : List.Forall₂ Mark.fits ms cs) :
    ((signs cs).destutter' (· ≠ ·) 1).length ≤ (bounds ms).1 + 1 ∧
    ((signs cs).destutter' (· ≠ ·) (-1)).length ≤ (bounds ms).2 + 1 := by
  induction h with
  | nil => simp [signs,bounds]
  | @cons m c ms cs hm h ih =>
    obtain ⟨hp,hn⟩ := ih
    rcases lt_trichotomy c 0 with hc | rfl | hc
    · have hs := sign_eq_neg_one_iff.mpr hc
      cases m <;> simp_all [signs, bounds, Mark.fits] <;> first | (exfalso; linarith) | omega
    · cases m <;> simp_all [signs, bounds] <;> omega
    · have hs := sign_eq_one_iff.mpr hc
      cases m <;> simp_all [signs, bounds, Mark.fits] <;> first | (exfalso; linarith) | omega

private lemma destutter_le (p : SignType) (cs : List SignType) :
    (cs.destutter (· ≠ ·)).length ≤ (cs.destutter' (· ≠ ·) p).length := by
  cases cs with
  | nil => simp [List.destutter,List.destutter']
  | cons h t =>
    by_cases e : p=h
    · subst h; simp [List.destutter,List.destutter']
    · simp [List.destutter,List.destutter',e]

lemma changes_bound (P : Polynomial ℝ) (ms : List Mark)
    (h : List.Forall₂ Mark.fits ms P.coeffList) : P.signVariations ≤ (bounds ms).1 := by
  have H := (signs_bound h).1
  have D := destutter_le 1 (signs P.coeffList)
  change ((signs P.coeffList).destutter (· ≠ ·)).length - 1 ≤ _
  omega
def tableMark (p : Table) : Mark :=
  if ∀ i : Fin 11, ∀ j : Fin 6, 0 ≤ entry p i j then .up
  else if ∀ i : Fin 11, ∀ j : Fin 6, entry p i j ≤ 0 then .down else .both

lemma mark_fits (p : Table) (x y v w : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hv : 0 ≤ v) (hw : 0 ≤ w) : (tableMark p).fits (value p x y v w) := by
  unfold tableMark
  split_ifs with h k
  · apply Finset.sum_nonneg; intro i _; apply Finset.sum_nonneg; intro j _
    have hc : (0:ℝ) ≤ entry p i j := by exact_mod_cast h i j
    unfold mon; positivity
  · apply Finset.sum_nonpos; intro i _; apply Finset.sum_nonpos; intro j _
    apply mul_nonpos_of_nonpos_of_nonneg _ (by unfold mon; positivity)
    apply mul_nonpos_of_nonpos_of_nonneg _ (by unfold mon; positivity)
    exact_mod_cast k i j
  · trivial

def Good (ts : List Table) : Prop := ∀ x y v w : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ v → 0 ≤ w →
  ∃ ms : List Mark, (bounds ms).1 ≤ 4 ∧ List.Forall₂ Mark.fits ms (ts.map (fun p => value p x y v w))

lemma good_leaf (ts : List Table) (h : (bounds (ts.map tableMark)).1 ≤ 4) : Good ts := by
  intro x y v w hx hy hv hw
  refine ⟨ts.map tableMark,h,?_⟩
  clear h; induction ts with
  | nil => constructor
  | cons p ts ih => exact .cons (mark_fits p x y v w hx hy hv hw) ih


def all6 (f : ℕ → Bool) : Bool := f 0 && f 1 && f 2 && f 3 && f 4 && f 5

lemma all6_at (f : ℕ → Bool) (h : all6 f = true) (i : Fin 6) : f i = true := by
  simp only [all6,Bool.and_eq_true] at h; fin_cases i <;> tauto

def all11 (f : ℕ → Bool) : Bool := f 0 && f 1 && f 2 && f 3 && f 4 && f 5 && f 6 && f 7 && f 8 && f 9 && f 10

lemma all11_at (f : ℕ → Bool) (h : all11 f = true) (i : Fin 11) : f i = true := by
  simp only [all11,Bool.and_eq_true] at h; fin_cases i <;> tauto


def table0 : Table := #[
  #[800,74752,2099432,16773992,51531712,53789312],
  #[8000,700352,18394416,138390800,400264544,392949888],
  #[45440,3275328,73736136,519737768,1395194784,1248294144],
  #[171520,9751936,177175200,1155241024,2835358240,2250819840],
  #[460288,20032768,284858400,1673631424,3659385376,2519778432],
  #[898048,29210112,323580672,1641517696,3072436224,1797850752],
  #[1230848,29788160,265763328,1088307200,1657713152,806611968],
  #[1114112,20062208,153182208,466847744,548827136,216213504],
  #[524288,8650752,54263808,116129792,101449728,31457280],
  #[0,2097152,8388608,12582912,8388608,2097152],
  #[0,0,0,0,0,0]]

def table1 : Table := #[
  #[24960,1746144,34945296,242945328,681252480,652929792],
  #[249600,16380544,307515616,2013453216,5319778624,4807033600],
  #[1331584,75190240,1247617616,7618877872,18642550720,15422294528],
  #[4662272,217466048,3053443392,17127597888,38157472960,28170331648],
  #[11389952,426235776,4994725312,25133999616,49775266496,32087691008],
  #[19841024,577091840,5694700288,24911659520,42450388736,23440590592],
  #[23926784,536970240,4559414272,16580573184,23393758208,10859555840],
  #[18513920,332619776,2476511232,7062994944,7934365696,3033776128],
  #[7340032,132775936,812908544,1715470336,1486618624,458620928],
  #[0,29360128,117440512,176160768,117440512,29360128],
  #[0,0,0,0,0,0]]

def table2 : Table := #[
  #[341248,17697920,264351112,1585859656,4037980352,3515408512],
  #[3412480,166318080,2338237424,13215579472,31726335456,26128043648],
  #[17226496,740055808,9423479784,49907342344,111293937952,84599128320],
  #[55912448,2033027072,22687131936,111281725376,227094373280,155871841536],
  #[123982848,3715487360,36018870944,160721170752,294283449248,178889095808],
  #[190441472,4570406912,39067979520,155029639808,248213755904,131311983744],
  #[192569344,3689787904,28812011520,98691268096,134068532224,60692057088],
  #[107569152,1796454400,13652021248,38905350144,43502608384,16560394240],
  #[6651904,408420352,3446857728,7956570112,7172988928,2261508096],
  #[-28311552,-36700160,136314880,346030080,277872640,76546048],
  #[-8388608,-41943040,-83886080,-83886080,-41943040,-8388608]]

def table3 : Table := #[
  #[2669376,101502624,1166685120,6008905056,13866265344,10739197440],
  #[26693760,956255744,10381944704,50404610688,109697819264,80838826496],
  #[127706944,4074642336,40753494848,187683651424,382470744192,263842279424],
  #[381005312,10333967552,92658576384,404218554816,765161228416,486646457344],
  #[747627520,16629009792,133238420864,549003583616,955821267584,552840168960],
  #[945511424,16359787776,121884497152,477169706240,756377580288,393322213888],
  #[632818688,7673198592,64237622272,250869642240,361773191168,168100791296],
  #[-76836864,-1914191872,9658880000,61521301504,86793379840,36768313344],
  #[-551518208,-4848599040,-9991241728,-6397313024,542294016,1245446144],
  #[-441974784,-2693267456,-6353321984,-7320109056,-4143448064,-925368320],
  #[-117440512,-587202560,-1174405120,-1174405120,-587202560,-117440512]]

def table4 : Table := #[
  #[12921952,350051120,3093174496,13575408016,28708684928,18796314880],
  #[129219520,3310216960,27740981952,114789613120,228630900160,144447889152],
  #[578163296,13064707376,101407854880,408471225104,775805367488,472379766784],
  #[1524037888,27931432864,193275644160,784846630688,1445506417344,849027120640],
  #[2367027712,29973316032,180030640448,831082834496,1557821305280,893495546112],
  #[1549187584,-1769270912,-7868656768,349101731200,871470998656,521641128704],
  #[-1764261376,-53908644352,-231932881920,-235788518400,52216285696,108216305152],
  #[-5476354048,-79839492096,-291458766848,-419686803456,-256973504512,-54382329856],
  #[-6122168320,-59565801472,-183205216256,-253442523136,-164921761792,-41240821760],
  #[-3492806656,-23892590592,-60642295808,-73499410432,-43178262528,-9921363968],
  #[-834666496,-4173332480,-8346664960,-8346664960,-4173332480,-834666496]]

def table5 : Table := #[
  #[37306592,626601952,3657459488,12930977312,28126955008,11461697024],
  #[373065920,5972640192,33368920768,110762737472,223505639808,95162616832],
  #[1454033504,17892958496,79855449504,290019959648,637262085248,289726298112],
  #[2678685952,7582995328,-69638817408,31758651520,623553682816,356008768512],
  #[98530176,-97161231296,-755564154752,-1418263570368,-721918300544,-69454547456],
  #[-11840392448,-325338009344,-1842175580160,-3559913413376,-2770422065408,-767852061696],
  #[-31331894272,-543912080128,-2487553022208,-4502134514944,-3561925916416,-1034764237824],
  #[-44141927424,-552545244160,-2084348710912,-3391147057152,-2518719321088,-703517658112],
  #[-37552144384,-346693070848,-1079510667264,-1533895020544,-1028269600768,-264744321024],
  #[-18316001280,-124821176320,-316124692480,-382607032320,-224544686080,-51557171200],
  #[-3980394496,-19901972480,-39803944960,-39803944960,-19901972480,-3980394496]]

def table6 : Table := #[
  #[39602144,-327535856,-6941302432,-27633453136,-28433121920,-31817284864],
  #[396021440,-2924994176,-61031383360,-234950229952,-245354164928,-231070647040],
  #[295575008,-45471057296,-448057042720,-1347608097904,-1407243561152,-896476125184],
  #[-7139914496,-280021105376,-2029440915456,-5125064741216,-5191703805248,-2402599123968],
  #[-39070176512,-928524061408,-5544449940992,-12425618708576,-11924666037568,-4540310275328],
  #[-107849615360,-1921266965632,-9675301752320,-19534617203072,-17456612369152,-5886884072192],
  #[-187755094016,-2620793588352,-11163803424640,-20212538209664,-16583059967616,-5101286688256],
  #[-215992088576,-2372286863872,-8529460665344,-13668374134784,-10157553286144,-2862345041408],
  #[-160993392640,-1379081529344,-4154801391616,-5799848925184,-3846652829696,-983517159424],
  #[-71028047872,-468851589120,-1165125877760,-1392548577280,-809985638400,-184739397632],
  #[-14230749184,-71153745920,-142307491840,-142307491840,-71153745920,-14230749184]]

def table7 : Table := #[
  #[-169209056,-5806986880,-45824140832,-145965505664,-164750195200,-105862572032],
  #[-1692090560,-54762574400,-412627852224,-1259372326976,-1402788772352,-815583943680],
  #[-13658745184,-339741426880,-2242358591776,-6025257812416,-6422247755776,-3146892866560],
  #[-68659788032,-1390234078400,-8083139591808,-19118526067904,-19185042434048,-7939584351744],
  #[-222424896640,-3769590841792,-19360693241856,-41062074797248,-38445493471744,-13937947760640],
  #[-487020833024,-6939147574784,-31263748948736,-59935133597696,-51950451745280,-17024540831744],
  #[-737005067776,-8765134706176,-34336978644480,-59307599142400,-47188565128192,-14189814991872],
  #[-766276502528,-7508745004544,-25367681839104,-39082047128576,-28264646245376,-7807812453888],
  #[-526112806912,-4183942721536,-12071367995392,-16371575726080,-10634254317568,-2676216672256],
  #[-215976312832,-1373566304256,-3334502088704,-3921871568896,-2254620524544,-509661052928],
  #[-40447770624,-202238853120,-404477706240,-404477706240,-202238853120,-40447770624]]

def table8 : Table := #[
  #[-995183064,-19429212456,-120829324248,-335215601928,-329827597632,-158739477120],
  #[-9951830640,-184656593136,-1098998710032,-2923383463920,-2865689851872,-1278148245888],
  #[-62821735512,-1059484274136,-5777023000920,-13842672279288,-13245194267424,-5280343544832],
  #[-263729948736,-4035399152256,-20107329747360,-43277811576768,-39766940570208,-14288070996480],
  #[-757639829952,-10381261309872,-46988956947840,-91987719553392,-80175282304608,-26528419191936],
  #[-1522382716416,-18363194457600,-74651672848704,-133628620979712,-109314949288512,-33757328342400],
  #[-2152567154688,-22463352596928,-81081308569920,-132249781886016,-100510654464960,-29031395706624],
  #[-2110175230464,-18733197400320,-59440429115904,-87543688427520,-61148002956288,-16421721474816],
  #[-1371704916480,-10197207058944,-28155109459968,-36999135191040,-23463245655552,-5793717782016],
  #[-533927755776,-3277750370304,-7771723923456,-8987947106304,-5102085144576,-1142039347200],
  #[-94692704256,-473463521280,-946927042560,-946927042560,-473463521280,-94692704256]]

def table9 : Table := #[
  #[-2697212752,-37745129072,-197608143376,-490906848688,-388693131968,-120208024576],
  #[-26972127520,-361278580512,-1813257586784,-4322471076256,-3504958766016,-1060515585152],
  #[-163750718640,-2115577194704,-9907262430000,-21362479335504,-17669172629312,-5326333945344],
  #[-662674688640,-8208799874880,-35876331515712,-70224838107072,-57893735490624,-17418043309824],
  #[-1842645593696,-21320732824416,-86328083465248,-155681369527712,-124994226301056,-37108812739072],
  #[-3590954890560,-37772274309952,-139913671118784,-233644278957888,-179450395566592,-51790724236416],
  #[-4923833508224,-46026175422208,-154050985149440,-237331120854272,-171874654016128,-47492176397312],
  #[-4673129961216,-38109149676544,-114052497634816,-160692622983168,-108298701961984,-28222556898304],
  #[-2933229883392,-20556101153792,-54469346746368,-69403732150272,-42957679259648,-10400422585344],
  #[-1099008933888,-6538979426304,-15165828366336,-17253697880064,-9670783696896,-2142943690752],
  #[-186830028800,-934150144000,-1868300288000,-1868300288000,-934150144000,-186830028800]]

def table10 : Table := #[
  #[-4230843576,-39425251224,-178634227416,-427963638840,-208422220224,32203155072],
  #[-42308435760,-382071823344,-1653297307536,-3780977565552,-2099047800096,75739553664],
  #[-271984921848,-2651909663064,-10848929885880,-21658387896504,-14548866295008,-2139900321408],
  #[-1160476916544,-11801385079104,-45991311207456,-82898011586176,-60645320993888,-14138268156928],
  #[-3330718347456,-33240546257088,-122155378038048,-204626636797312,-151739307884768,-40051925018752],
  #[-6580760136192,-61597160394240,-210331321150464,-329877358763136,-239017929296640,-64640479106688],
  #[-9027902155264,-76873794522752,-240720697725184,-352175235905024,-243991006654720,-64690576107392],
  #[-8486630377984,-64393317136640,-182960964487168,-247577289219584,-161411801634304,-40888790143232],
  #[-5233587343872,-34876697465856,-89086338247680,-110334703386624,-66749245174272,-15857769913344],
  #[-1913475051520,-11085478516736,-25207163551744,-28243370070016,-15639788294144,-3431578310656],
  #[-315407958016,-1577039790080,-3154079580160,-3154079580160,-1577039790080,-315407958016]]

def table11 : Table := #[
  #[-1755851200,17888838496,66250314368,3625041440,216652382656,235144164608],
  #[-17558512000,161109655296,621872960512,161500960256,1593617528064,1712062685824],
  #[-211495111744,-857770224352,-3091830439680,-8023690415392,-1865026717888,3277751903232],
  #[-1270556605952,-9961141441856,-35596585659648,-62520631984064,-40110931452800,-5076775582080],
  #[-4317859172096,-37423807910400,-127696606867264,-203855383341440,-142413024885312,-33535283199232],
  #[-9299294555648,-78806576542976,-252288921505920,-377524281835136,-262118272244096,-67478825534592],
  #[-13316169242752,-104985107007040,-311344766066112,-437061917572288,-292542044503744,-75155955233280],
  #[-12738947041792,-91098876392064,-247859454961664,-324274012388608,-205670430251520,-50895943474304],
  #[-7864764640768,-50285572595200,-124515807553536,-150481633497088,-89234311510528,-20847677612544],
  #[-2845643937792,-16129171234816,-36060245561344,-39862148653056,-21832025872384,-4746595483648],
  #[-460057411584,-2300287057920,-4600574115840,-4600574115840,-2300287057920,-460057411584]]

def table12 : Table := #[
  #[11509865952,180843787680,614467195776,781972925568,721820402880,374686384896],
  #[115098659520,1726241571520,5807632463872,7484717796096,6335980188544,2979122834560],
  #[332539566896,5380618741920,17338653364560,20736392227040,16791167987328,8162338990464],
  #[-102051293312,3301151081440,7586970561984,-1722878957088,-457406492032,5205226039808],
  #[-3093196613424,-22361401424896,-77546267426992,-132200252766880,-94924879500096,-21165365757056],
  #[-9395831654432,-73715517740832,-229382387892576,-340430157728096,-235457797579392,-60133722033024],
  #[-15429557178432,-114992752214336,-329476076289728,-452382267162688,-298153565231104,-75684179322240],
  #[-15716936911232,-107546002336512,-283598937406720,-362510307391488,-225823127352704,-55082691942656],
  #[-9968215014400,-61758458200704,-149314028557824,-177073486613248,-103397645283840,-23847944042112],
  #[-3629983105024,-20231158359552,-44624802387968,-48787288056832,-26474886862848,-5711225939456],
  #[-582827294720,-2914136473600,-5828272947200,-5828272947200,-2914136473600,-582827294720]]

def table13 : Table := #[
  #[42381559296,466422862464,1408032736128,1683076474368,1069650793728,367391278080],
  #[423815592960,4494551913984,13446744679680,16280677267200,10088207786496,3162375716352],
  #[1679475382080,17042420186496,49261690522880,57942140947968,33981366972480,9881536645376],
  #[3264228825600,31303706712192,83488063988736,87660151178752,43619386763264,11332574889856],
  #[2150941649792,19510726558720,34781218784000,1387070147328,-25359410769024,-9375211572480],
  #[-4313145812736,-34345536822528,-124322668146176,-213852070553088,-166275807425280,-46727391216896],
  #[-12723083133888,-93599822129664,-271232225586816,-380175323555072,-256589182309312,-66769345345280],
  #[-15454151604992,-103537207574656,-270003422778368,-343346205722368,-213560215383296,-52134376469632],
  #[-10549980423936,-64135871805696,-152926563900928,-179464265107968,-103942423616256,-23818831027456],
  #[-3962783072256,-21840559398912,-47734406873088,-51787694948352,-27920491511808,-5989427109888],
  #[-641784168448,-3208920842240,-6417841684480,-6417841684480,-3208920842240,-641784168448]]

def table14 : Table := #[
  #[92328005296,834116165792,2248733456464,2401762540960,1113131122496,217633633024],
  #[923280052960,8092844231712,21713333064800,23711567240608,11365311619584,2192978301824],
  #[3905748426544,32688908411200,85428996537744,92135414070208,43251522568384,7749851816064],
  #[9087266141312,71090977804064,176011305145920,179443325397152,76316425201280,10864568973696],
  #[12029471735840,85002322766208,187875535385824,160153451232320,42464550146880,-2796966272384],
  #[6999523995584,38486704485440,46681382276928,-29351912418496,-76949564359936,-32406316699008],
  #[-3913104341216,-38294584051424,-140912314262496,-234856419522848,-180020302161344,-51694717190784],
  #[-10866789476480,-75298754650752,-203357000559616,-267302276063744,-171394621669248,-43017380990848],
  #[-9016118347136,-54875558514560,-131208675215616,-154533858030848,-89863332737408,-20678709754752],
  #[-3656191193088,-20072760885248,-43729131610112,-47312741449728,-25448175644672,-5447996112896],
  #[-611238758400,-3056193792000,-6112387584000,-6112387584000,-3056193792000,-611238758400]]

def table15 : Table := #[
  #[153296194720,1190705879360,2888965119712,2729434154944,885700889984,7731470848],
  #[1532961947200,11624242189760,28212913382464,27613403478976,10134385399808,642010398976],
  #[6653043205088,48491814349888,115552113475616,113383172022080,42986834323072,3315392200448],
  #[16433258907904,113131011289792,259362215093376,247146570767808,90083742359552,5599484394752],
  #[24969015493312,158806612580480,340037440311616,298791004545792,91042727718528,-1549866875136],
  #[22763511101056,128262794252672,238332649508224,161228173501312,8229516416000,-20165672934656],
  #[9646540393600,38847199051776,28146250509824,-56376440468736,-89728230044288,-34406197723904],
  #[-2635542060032,-28697107513600,-99940672781312,-154618677917184,-111026057244672,-30286486655232],
  #[-5585731560448,-35778121950464,-89128327478272,-108573566336512,-64945980237824,-15308350989568],
  #[-2754300204032,-15244102344704,-33433407338496,-36378609987584,-19661906318336,-4226901528576],
  #[-496274407424,-2481372037120,-4962744074240,-4962744074240,-2481372037120,-496274407424]]

def table16 : Table := #[
  #[208907710224,1430971618320,3155607596856,2648476229784,552025256256,-162912953472],
  #[2089077102240,14052094138400,31164523488272,27499025031984,7579486852256,-718069518976],
  #[9181509932768,59837839154960,131304073320136,117938075222840,36357959180576,-932472721280],
  #[23314229008384,145218444527200,310367797935264,276475571758368,87688351690592,-323772020608],
  #[37440070406552,219599571485624,448789469204424,384766085672008,115756740054816,-2379467071360],
  #[38627197592464,209125816099408,396914405035856,310016914653424,73330159219552,-10270992792832],
  #[24148891149896,115609471909304,188295747496440,108237265875304,-6584837077920,-17986936216192],
  #[6877986386272,22787453723968,10844998694400,-36105743094720,-47986599308128,-16945324856704],
  #[-1266545989984,-12421978023424,-38808333275072,-54558591584512,-36047365487584,-9141675144704],
  #[-1527192476672,-8785610444672,-19870517011968,-22169813134592,-12234554628608,-2676840537984],
  #[-331535620096,-1657678100480,-3315356200960,-3315356200960,-1657678100480,-331535620096]]

def table17 : Table := #[
  #[241605213792,1488286962048,3020738576496,2290787314512,279411730176,-237318756096],
  #[2416052137920,14696029025088,30148499561760,24367775669088,5103402440640,-1395850553856],
  #[10693468931616,63521054141568,129876312496368,108401809639248,28125013845696,-3228068507136],
  #[27562500142848,158227853707968,318476006824128,268418302153536,77047227810624,-3560421083904],
  #[45522872885424,250005785271888,489318543595728,408217638386544,121378013665344,-2003993511936],
  #[49620938980896,257872774448544,483730308785952,390136788914400,112705001839680,-1953313756416],
  #[35073243168048,169891546058448,298509919284048,223194142510320,55105685057856,-4396841058816],
  #[14732041812288,64287040827264,99538355114496,59625755415936,4124399736000,-5517999580416],
  #[2623792411584,8431799111424,5952255114624,-6496105208832,-10240741373760,-3600387750144],
  #[-341192183808,-2568435065088,-6861818422272,-8586766714368,-5155857503232,-1203666329856],
  #[-164641720320,-823208601600,-1646417203200,-1646417203200,-823208601600,-164641720320]]

def table18 : Table := #[
  #[241456905056,1361929738192,2584127427272,1824776822936,141727621696,-219394607104],
  #[2414569050560,13516200573312,26027583671536,19766469438032,3472371656352,-1368145632896],
  #[10732723215696,59102736426496,114161743440632,90535830074280,21425813660896,-3318286183552],
  #[27912128512128,150030569056608,287909994824928,233863880161824,64708406041632,-3363919839744],
  #[46852849798408,244126644630072,461558069826104,378505482951016,114714241271520,493033314944],
  #[52606339818288,264088337363312,488138693062192,399248208748752,127467123766496,4875610534912],
  #[39392845576312,189433536336008,339642106655560,273753868582744,89364361680032,5211908993152],
  #[18824010604704,86137911676736,148329784357376,116004121448640,37450483508576,2462245345280],
  #[5082932402400,21857781040000,35440847447744,26005180127232,7704280059232,365098742144],
  #[510948731136,1935553595520,2632727070720,1394346950400,77983415040,-108241329024],
  #[-34811181056,-174055905280,-348111810560,-348111810560,-174055905280,-34811181056]]

def table19 : Table := #[
  #[210736514208,1107881381472,2000917262496,1368773941152,113502932160,-151498613760],
  #[2107365142080,11042681274432,20295633292224,14952026054208,2657386757376,-934322136960],
  #[9393405879648,48732871325088,90298079346720,69860816352480,16811143942656,-2091058508544],
  #[24570483627264,125492107437696,232726706514816,186072790401664,53112700625792,-1155007071488],
  #[41666342085408,208548133509792,384899917868640,314582170106464,100353737032832,3789693370624],
  #[47626219278528,232828869113280,425867227563456,353180086900032,121956522646656,9441013475328],
  #[36833278533152,175557718826848,317456990603360,265969843101216,97635927329280,10398634537728],
  #[18731275131776,87082469641216,155688805145600,131662769581824,50932626632832,6607467687168],
  #[5807998553280,26463475255296,47014094901888,40341418706688,16454460962496,2471660455680],
  #[917182473344,4167773268352,7499268339968,6662990143232,2913355973248,499043374976],
  #[40764087296,203820436480,407640872960,407640872960,203820436480,40764087296]]

def table20 : Table := #[
  #[161607185576,805782861640,1411931659352,973840041080,127109953216,-78974104576],
  #[1616071855760,8059330660560,14385495345424,10614583647344,2230593045024,-441754061696],
  #[7217502699368,35823867625592,64678816538904,50084014051304,13342423871072,-669138567552],
  #[18954297056704,93266665494688,169429537625760,135991805814112,41994850501792,1120213875456],
  #[32364750106648,157421639810232,286657757898632,236558191186120,81010158144864,6052835153792],
  #[37428370553104,179658761082832,327196777872336,276209014283632,102322930256224,11080303315200],
  #[29531488133240,139889036245256,254698547763912,219435255402968,86673980577056,11579724825984],
  #[15559829700128,72914799372864,133011695235328,117042083589824,48909130464480,7523772437248],
  #[5159438700512,24080546410112,44299540989120,40009731511808,17645832194144,3014533961856],
  #[943356059904,4457008343168,8394472773632,7874928860928,3677692474112,683584103552],
  #[67138400256,335692001280,671384002560,671384002560,335692001280,67138400256]]

def table21 : Table := #[
  #[109227603312,525101119248,908828186448,651508148016,130810514304,-27742963200],
  #[1092276033120,5265035790688,9276780600544,7029721557024,1827954635584,-97746078464],
  #[4885167657488,23530226743152,41997290801008,33207213472208,10117898310336,262916553472],
  #[12866716465024,61767449689024,111271430410560,91016161178432,30954692799552,2309228807680],
  #[22079171588688,105456421455344,191285085584816,160935094716880,59445164439232,6417905440512],
  #[25741948447456,122249653414752,223017100473824,192314574249760,75866913141696,10061734398464],
  #[20583826330224,97268706036880,178518598166032,157535300909872,65670538746432,9968956295936],
  #[11089690778944,52287806107776,96763134470144,87420037474688,38253442075328,6398423741952],
  #[3821071246784,18083226723072,33915264499072,31457145626624,14396048414400,2592011810560],
  #[749780512256,3603476126976,6916099385344,6625246516736,3167196824064,604354077952],
  #[61947810304,309739051520,619478103040,619478103040,309739051520,61947810304]]

def table22 : Table := #[
  #[65110937352,306259589784,531334335768,402261356040,110003937024,-2071735680],
  #[651109373520,3075459295824,5421589816080,4280759519856,1343044012896,59524386816],
  #[2915298189336,13797422589672,24635196421416,20129347373304,6966317398176,590042045952],
  #[7695760550208,36435991024416,65740642828512,55289897244768,20623047588960,2333562698496],
  #[13255562691224,62725852033000,114202536514472,98498558699384,39015120889504,5248809362816],
  #[15547278344976,73525714232016,135011088178704,119142382170096,49617973854624,7508243976192],
  #[12549978835560,59373840485400,110016032830296,99226425678216,43150222398816,7115967901056],
  #[6863590169056,32563809401024,60999056276992,56237667477568,25415452882976,4476622450432],
  #[2422808087136,11580579206400,22008993773760,20771586954240,9724468977120,1804104677376],
  #[494932106880,2402538971136,4660834815744,4516591689216,2186174281344,422810543616],
  #[43911804032,219559020160,439118040320,439118040320,219559020160,43911804032]]

def table23 : Table := #[
  #[34184079232,159247987328,279826945408,224459363968,75509444864,5813118208],
  #[341840792320,1600261479168,2849828159744,2355328802560,853015080960,89093751296],
  #[1531950224512,7197120623488,12965307080832,10995134436736,4223079002368,528081247488],
  #[4051422780416,19084841788928,34733031292416,30133212448256,12149584272896,1715984108544],
  #[6999254259584,33047361998976,60715659969664,53774977036160,22596150861312,3488726055424],
  #[8247307875584,39039103504640,72396159104256,65372572234496,28476541796864,4708333037568],
  #[6704238794368,31846871998336,59645132501376,54876192856192,24683282229760,4309588670976],
  #[3705839824384,17700779458560,33526907678720,31431186832384,14555569340928,2656350553088],
  #[1329608629504,6407265377536,12303279610368,11762332860928,5595845253376,1059135254784],
  #[278555137536,1361533869568,2660584102912,2598100466688,1267808415232,247313319424],
  #[25730423040,128652115200,257304230400,257304230400,128652115200,25730423040]]

def table24 : Table := #[
  #[15753310144,73362670208,131339531968,111090937984,42847410176,5486644096],
  #[157533101440,737229289088,1333909730944,1151406567808,462335591936,65142567424],
  #[706517408384,3320382429952,6066012459008,5333134039424,2217173379712,336186777728],
  #[1871344832512,8828495167744,16275117288960,14553107170560,6238118982656,1002978765824],
  #[3240935055040,15347963830016,28542334412224,25931918900352,11424014608896,1927401345792],
  #[3833007091840,18227366374016,34198303907200,31549521421696,14248561158656,2502984361984],
  #[3132825265792,14972643711360,28356050102912,26556322356096,12270942919936,2230852221184],
  #[1745453673472,8396533053440,16067768611840,15277969314816,7211496640512,1350216557568],
  #[633501261824,3074567913856,5954613698048,5751446229248,2769816710656,531917527424],
  #[134978065408,663218988544,1303095300096,1279752623104,628204973056,123306726912],
  #[12784463488,63922317440,127844634880,127844634880,63922317440,12784463488]]

def table25 : Table := #[
  #[6337428672,29692724736,54279073152,48009787392,20266110912,3180100608],
  #[63374286720,298256859776,549599233280,492636445440,212631196544,34711411328],
  #[284413341440,1344175162880,2495891419392,2265516571904,997992829952,168605856000],
  #[754323850240,3579797335552,6696675609600,6152135501824,2761814265856,480880888320],
  #[1309139593088,6239354391296,11759018591232,10929672030464,4994007886976,893139649536],
  #[1553055722752,7436403806464,14122686437376,13278399050752,6169075401472,1130014704384],
  #[1274884000256,6137237282048,11750296647936,11175634100480,5274907384064,987216649728],
  #[714634353664,3462452013568,6688120375296,6435885036544,3084045233152,588462912000],
  #[261579717056,1277568368384,2492408908416,2427613685504,1180375534016,229182105600],
  #[56396804992,278272603264,549122363136,541699519744,267138338176,52685383296],
  #[5430937856,27154689280,54309378560,54309378560,27154689280,5430937856]]

def table26 : Table := #[
  #[2208139392,10448203776,19493935104,17868751104,8007815040,1392934656],
  #[22081393920,104877033216,196809314304,181937879040,82548978432,14624774400],
  #[99154973184,472717161984,892184980224,831658871040,381856583424,68820503808],
  #[263286331392,1260047198208,2391921626112,2248074826752,1044141911040,191227843584],
  #[457767730176,2199719642880,4200443711232,3980384984832,1869478756608,347585570304],
  #[544467412992,2627930093568,5049167377920,4824389005824,2290659187200,431974878720],
  #[448540756224,2175689428224,4207736556288,4054403247360,1945650757632,371835394560],
  #[252640035840,1232472431616,2400538460160,2333168762880,1131411692544,218948994048],
  #[93071366016,457101670656,897297090816,879994908672,431148397440,84420274944],
  #[20239279872,100206796032,198434385408,196455178752,97237986048,19249676544],
  #[1971489024,9857445120,19714890240,19714890240,9857445120,1971489024]]

def table27 : Table := #[
  #[659224320,3155278848,5996388096,5649347328,2634524160,485510400],
  #[6592243200,31646683648,60382773760,57187554816,26852306944,4993085440],
  #[29617111552,142617786880,273234888448,260158479616,122997883648,23073617152],
  #[78723055616,380309712896,731710172160,700482782208,333458621440,63099354112],
  #[137089913088,664571608832,1284294176000,1236329369344,592613080576,113096191488],
  #[163415442944,795169963520,1543865672192,1494716354048,721438330880,138833128448],
  #[135023177984,659744107776,1287317534464,1253714002176,609335942144,118218544640],
  #[76346334208,374777121792,735208239104,720424411136,352600921088,68953961472],
  #[28266373120,139491222784,275242722304,271444561408,133793981440,26367292672],
  #[6186276864,30714287104,60994379776,60560185344,30062995456,5969179648],
  #[607552768,3037763840,6075527680,6075527680,3037763840,607552768]]

def table28 : Table := #[
  #[166197312,804687360,1553277696,1493668224,715266240,136385664],
  #[1661973120,8064406400,15607572992,15055901184,7236843392,1386081920],
  #[7470112256,36331320320,70509467776,68241226112,32928768896,6335802496],
  #[19873543168,96895974400,188601137664,183162283520,88737335808,17153758720],
  #[34655574784,169419464832,330789487232,322406612096,156844747904,30463732992],
  #[41388438016,202921275904,397515016448,388901227264,190000318720,37081270016],
  #[34281898368,168611948416,331475728000,325574272384,159759662592,31331068160],
  #[19444919808,95971510784,189390061568,186790285312,92071830016,18145015296],
  #[7227544256,35809821056,70957597312,70289308160,34807387328,6893399680],
  #[1589492096,7909270656,15742161664,15665782016,7794701184,1551302272],
  #[157039232,785196160,1570392320,1570392320,785196160,157039232]]

def table29 : Table := #[
  #[34691584,169728512,331756288,323813632,157814528,30720256],
  #[346915840,1699771392,3327830528,3254021632,1589058048,310011392],
  #[1559885824,7655064064,15013468416,14708879104,7198180096,1407591168],
  #[4153106432,20416271360,40116925440,39384212480,19317201920,3786749952],
  #[7250612992,35709834496,70310225664,69177799936,34011195904,6684400128],
  #[8672932352,42801285632,84456089088,83289876992,41051967488,8089826304],
  #[7198347520,35602131712,70414487808,69614148352,34401622528,6798177792],
  #[4093266944,20293074944,40236404736,39883433984,19763618816,3916781568],
  #[1526125312,7585665280,15080977920,14990195200,7449491200,1480733952],
  #[336870912,1679166976,3347958784,3337583616,1663604224,331683328],
  #[33429248,167146240,334292480,334292480,167146240,33429248]]

def table30 : Table := #[
  #[5832576,28784256,56803200,56029824,27624192,5445888],
  #[58325760,288094976,569052416,561844992,277283840,54722048],
  #[262340224,1297055616,2564555904,2534736256,1252326144,247430400],
  #[698903552,3459140096,6846955008,6775059968,3351297536,662956032],
  #[1221320576,6051704960,11992848000,11881520000,5884712960,1165656576],
  #[1462764800,7257067776,14399965440,14285137664,7084826112,1405350912],
  #[1216028800,6041047936,12003551616,11924655232,5922703360,1176580608],
  #[692852224,3446957056,6859198464,6824375296,3394722304,675440640],
  #[258932992,1290199296,2571452928,2562492928,1276759296,254452992],
  #[57314816,286062080,571100160,570076160,284526080,56802816],
  #[5705984,28529920,57059840,57059840,28529920,5705984]]

def table31 : Table := #[
  #[758528,3768064,7486976,7437824,3694336,733952],
  #[7585280,37697024,74935296,74476544,37008896,7355904],
  #[34125568,169677568,337454592,335554048,166826752,33175296],
  #[90957824,452495360,900403200,895815680,445614080,88664064],
  #[159061504,791752192,1576393728,1569283072,781086208,155506176],
  #[190690304,949781504,1892222976,1884882944,938771456,187020288],
  #[158717440,791064064,1577081856,1572035584,783494656,156194304],
  #[90564608,451708928,901189632,898961408,448366592,89450496],
  #[33904384,169235200,337896960,337323520,168375040,33617664],
  #[7519744,37565952,75066368,75000832,37467648,7486976],
  #[750336,3751680,7503360,7503360,3751680,750336]]

def table32 : Table := #[
  #[71552,356992,712448,710912,354688,70784],
  #[715520,3570432,7126528,7112192,3548928,708352],
  #[3219584,16068224,32077056,32017664,15979136,3189888],
  #[8584192,42849280,85555200,85411840,42634240,8512512],
  #[15018752,74982656,149743104,149520896,74649344,14907648],
  #[18016768,89969152,179708928,179479552,89625088,17902080],
  #[15008000,74961152,149764608,149606912,74724608,14929152],
  #[8571904,42824704,85579776,85510144,42720256,8537088],
  #[3212672,16054400,32090880,32072960,16027520,3203712],
  #[713472,3566336,7130624,7128576,3563264,712448],
  #[71296,356480,712960,712960,356480,71296]]

def table33 : Table := #[
  #[4352,21760,43520,43520,21760,4352],
  #[43520,217600,435200,435200,217600,43520],
  #[195840,979200,1958400,1958400,979200,195840],
  #[522240,2611200,5222400,5222400,2611200,522240],
  #[913920,4569600,9139200,9139200,4569600,913920],
  #[1096704,5483520,10967040,10967040,5483520,1096704],
  #[913920,4569600,9139200,9139200,4569600,913920],
  #[522240,2611200,5222400,5222400,2611200,522240],
  #[195840,979200,1958400,1958400,979200,195840],
  #[43520,217600,435200,435200,217600,43520],
  #[4352,21760,43520,43520,21760,4352]]

def table34 : Table := #[
  #[128,640,1280,1280,640,128],
  #[1280,6400,12800,12800,6400,1280],
  #[5760,28800,57600,57600,28800,5760],
  #[15360,76800,153600,153600,76800,15360],
  #[26880,134400,268800,268800,134400,26880],
  #[32256,161280,322560,322560,161280,32256],
  #[26880,134400,268800,268800,134400,26880],
  #[15360,76800,153600,153600,76800,15360],
  #[5760,28800,57600,57600,28800,5760],
  #[1280,6400,12800,12800,6400,1280],
  #[128,640,1280,1280,640,128]]

def tables : List Table := [table34,table33,table32,table31,table30,table29,table28,table27,table26,table25,table24,table23,table22,table21,table20,table19,table18,table17,table16,table15,table14,table13,table12,table11,table10,table9,table8,table7,table6,table5,table4,table3,table2,table1,table0]

def cf0 (L M : ℝ) : ℝ := 32*((L^2 - M)*(69984*L^3 - 26892*L^2 - 46980*L*M - 20100*L + 10125*M^2 + 22122*M + 8125))
def cf1 (L M : ℝ) : ℝ := 32*(2*(L^2 - M)*(373248*L^3 - 27756*L^2 - 236952*L*M - 190864*L + 35775*M^2 + 103962*M + 57275))
def cf2 (L M : ℝ) : ℝ := 32*(3359232*L^5 + 1418148*L^4 - 6431076*L^3*M - 2941956*L^3 + 183465*L^2*M^2 - 302850*L^2*M + 822393*L^2 + 2792676*L*M^2 + 3131652*L*M - 41600*L - 327465*M^3 - 1130402*M^2 - 794361*M)
def cf3 (L M : ℝ) : ℝ := 32*(4*(1866240*L^5 + 2982312*L^4 - 5800626*L^3*M - 3474734*L^3 + 20601*L^2*M^2 - 2296848*L^2*M + 1139751*L^2 + 3043074*L*M^2 + 4056206*L*M - 148912*L - 293001*M^3 - 1112440*M^2 - 899127*M))
def cf4 (L M : ℝ) : ℝ := 32*(3732480*L^5 + 49321872*L^4 - 65852028*L^3*M - 49947428*L^3 - 708858*L^2*M^2 - 54883584*L^2*M + 21580922*L^2 + 42044700*L*M^2 + 60981604*L*M - 4000992*L - 3341222*M^3 - 13448400*M^2 - 11615642*M + 53248)
def cf5 (L M : ℝ) : ℝ := 32*(-4*(6998400*L^5 - 34344000*L^4 + 40245984*L^3*M + 38818980*L^3 + 554445*L^2*M^2 + 52403184*L^2*M - 20752545*L^2 - 29706396*L*M^2 - 43997628*L*M + 4331284*L + 1957407*M^3 + 8012008*M^2 + 6769245*M - 193536))
def cf6 (L M : ℝ) : ℝ := 32*(-100590336*L^5 + 297883440*L^4 - 357176412*L^3*M - 429205692*L^3 - 3583170*L^2*M^2 - 609375732*L^2*M + 250011054*L^2 + 281060508*L*M^2 + 395222492*L*M - 56562912*L - 15422318*M^3 - 60564924*M^2 - 41599614*M + 5192704)
def cf7 (L M : ℝ) : ℝ := 32*(-8*(24121152*L^5 - 69631812*L^4 + 90189693*L^3*M + 127158561*L^3 + 476280*L^2*M^2 + 181072146*L^2*M - 74274404*L^2 - 70645179*L*M^2 - 83525779*L*M + 19102648*L + 3190962*M^3 + 11010928*M^2 + 2372276*M - 2618368))
def cf8 (L M : ℝ) : ℝ := 32*(-3*(84680640*L^5 - 316344744*L^4 + 429540084*L^3*M + 665898608*L^3 + 950913*L^2*M^2 + 969681480*L^2*M - 384513517*L^2 - 324236396*L*M^2 - 242263136*L*M + 117169352*L + 11719383*M^3 + 29566880*M^2 - 37265355*M - 18201856))
def cf9 (L M : ℝ) : ℝ := 32*(-2*(123171840*L^5 - 733209192*L^4 + 986819544*L^3*M + 1610252976*L^3 + 765909*L^2*M^2 + 2495071872*L^2*M - 958421069*L^2 - 716147286*L*M^2 - 8729172*L*M + 331543330*L + 19985081*M^3 + 18420844*M^2 - 206977861*M - 43327616))
def cf10 (L M : ℝ) : ℝ := 32*(-180652032*L^5 + 1983415032*L^4 - 2547183132*L^3*M - 4314311356*L^3 - 583335*L^2*M^2 - 7316939226*L^2*M + 2843803161*L^2 + 1797468732*L*M^2 - 2092339932*L*M - 923969928*L - 37355973*M^3 + 58137234*M^2 + 834220899*M + 39791168)
def cf11 (L M : ℝ) : ℝ := 32*(-4*(25194240*L^5 - 568878552*L^4 + 688013190*L^3*M + 1237351038*L^3 + 37665*L^2*M^2 + 2287597878*L^2*M - 954814197*L^2 - 478601928*L*M^2 + 1447530867*L*M + 164470669*L + 7156053*M^3 - 33938641*M^2 - 277204266*M + 50284512))
def cf12 (L M : ℝ) : ℝ := 32*(-4*(10590912*L^5 - 544147524*L^4 + 621495153*L^3*M + 1273541368*L^3 + 5940*L^2*M^2 + 2435392263*L^2*M - 1128824908*L^2 - 430984512*L*M^2 + 2585944368*L*M - 199725651*L + 4477655*M^3 - 31104688*M^2 - 209955944*M + 166633808))
def cf13 (L M : ℝ) : ℝ := 32*(-4*(3265920*L^5 - 430714800*L^4 + 469233864*L^3*M + 1238218856*L^3 + 432*L^2*M^2 + 2204600448*L^2*M - 1097827648*L^2 - 326900355*L*M^2 + 3556202599*L*M - 942098996*L + 2270507*M^3 - 2512271*M^2 + 53759524*M + 286440736))
def cf14 (L M : ℝ) : ℝ := 32*(-4*(699840*L^5 - 281042460*L^4 + 295557417*L^3*M + 1169179965*L^3 + 1694818674*L^2*M - 762070107*L^2 - 207833889*L*M^2 + 3982525446*L*M - 1914492229*L + 920556*M^3 + 35710042*M^2 + 463482657*M + 297846888))
def cf15 (L M : ℝ) : ℝ := 32*(-8*(46656*L^5 - 75259692*L^4 + 77268087*L^3*M + 527935007*L^3 + 551972691*L^2*M - 87237177*L^2 - 54982719*L*M^2 + 1862733530*L*M - 1375851171*L + 145920*M^3 + 30664317*M^2 + 431504439*M + 49632016))
def cf16 (L M : ℝ) : ℝ := 32*(-23328*L^5 + 262698228*L^4 - 265783680*L^3*M - 3503059924*L^3 - 2426612730*L^2*M - 1795008493*L^2 + 191604564*L*M^2 - 11797409048*L*M + 12341650512*L - 279028*M^3 - 254976706*M^2 - 4341045887*M + 1227757392)
def cf17 (L M : ℝ) : ℝ := 32*(6*(15361164*L^4 - 15422400*L^3*M - 428498224*L^3 - 186164058*L^2*M - 575565553*L^2 + 11267696*L*M^2 - 1325904420*L*M + 1862386740*L - 7880*M^3 - 32408414*M^2 - 706214323*M + 523660712))
def cf18 (L M : ℝ) : ℝ := 32*(25443396*L^4 - 25463808*L^3*M - 1630480128*L^3 - 425903280*L^2*M - 3828868165*L^2 + 18853344*L*M^2 - 4578878752*L*M + 8260781832*L - 5056*M^3 - 114941296*M^2 - 3362961707*M + 4574574212)
def cf19 (L M : ℝ) : ℝ := 32*(4*(1333152*L^4 - 1333152*L^3*M - 220385516*L^3 - 33074088*L^2*M - 793793403*L^2 + 1000032*L*M^2 - 561498942*L*M + 1240701435*L - 64*M^3 - 13391100*M^2 - 553030440*M + 1251941518))
def cf20 (L M : ℝ) : ℝ := 32*(798336*L^4 - 798336*L^3*M - 402796884*L^3 - 32654880*L^2*M - 2107112337*L^2 + 606480*L*M^2 - 934288500*L*M + 2361871952*L - 19649036*M^2 - 1214268159*M + 4446366372)
def cf21 (L M : ℝ) : ℝ := 32*(76032*L^4 - 76032*L^3*M - 154279184*L^3 - 6165072*L^2*M - 1147865514*L^2 + 58464*L*M^2 - 326792000*L*M + 825268192*L - 5584104*M^2 - 555746742*M + 3306975032)
def cf22 (L M : ℝ) : ℝ := 32*(3456*L^4 - 3456*L^3*M - 49020672*L^3 - 836352*L^2*M - 518066535*L^2 + 2688*L*M^2 - 94886904*L*M + 152849124*L - 1190036*M^2 - 210543669*M + 2093936232)
def cf23 (L M : ℝ) : ℝ := 32*(-8*(1590672*L^3 + 9072*L^2*M + 24218526*L^2 + 2806596*L*M + 4985368*L + 22412*M^2 + 8135598*M - 142277709))
def cf24 (L M : ℝ) : ℝ := 32*(-2636464*L^3 - 3024*L^2*M - 59629296*L^2 - 4216432*L*M - 50974200*L - 17040*M^2 - 16023984*M + 533014924)
def cf25 (L M : ℝ) : ℝ := 32*(-420096*L^3 - 14891232*L^2 - 604128*L*M - 26344084*L - 768*M^2 - 3014892*M + 214992008)
def cf26 (L M : ℝ) : ℝ := 32*(-24*(2016*L^3 + 122836*L^2 + 2584*L*M + 389969*L + 16679*M - 3101127))
def cf27 (L M : ℝ) : ℝ := 32*(-8*(448*L^3 + 55724*L^2 + 508*L*M + 310718*L + 3790*M - 2744441))
def cf28 (L M : ℝ) : ℝ := 32*(-128*L^3 - 48400*L^2 - 128*L*M - 499404*L + 52*M + 5455484)
def cf29 (L M : ℝ) : ℝ := 32*(-3360*L^2 - 74336*L + 240*M + 1122120)
def cf30 (L M : ℝ) : ℝ := 32*(-112*L^2 - 7776*L + 16*M + 186184)
def cf31 (L _M : ℝ) : ℝ := 32*(23960 - 512*L)
def cf32 (L _M : ℝ) : ℝ := 32*(2244 - 16*L)
def cf33 (_L _M : ℝ) : ℝ := 32*(136)
def cf34 (_L _M : ℝ) : ℝ := 32*(4)
def coeffs (L M : ℝ) : Fin 35 → ℝ := ![cf0 L M, cf1 L M, cf2 L M, cf3 L M, cf4 L M, cf5 L M, cf6 L M, cf7 L M, cf8 L M, cf9 L M, cf10 L M, cf11 L M, cf12 L M, cf13 L M, cf14 L M, cf15 L M, cf16 L M, cf17 L M, cf18 L M, cf19 L M, cf20 L M, cf21 L M, cf22 L M, cf23 L M, cf24 L M, cf25 L M, cf26 L M, cf27 L M, cf28 L M, cf29 L M, cf30 L M, cf31 L M, cf32 L M, cf33 L M, cf34 L M]

def cfSpec0 : Array ℤ := #[69984,-53784,-467856,-80400,81000,392112,65000,751680,321600,0,-324000,-707904,-260000,0]
def cfSpec1 : Array ℤ := #[746496,-111024,-4881600,-1526912,572400,2107488,916400,7582464,6107648,0,-2289600,-6653568,-3665600,0]
def cfSpec2 : Array ℤ := #[3359232,2836296,-25724304,-11767824,1467720,-2422800,6579144,44682816,50106432,-665600,-10478880,-36172864,-25419552,0]
def cfSpec3 : Array ℤ := #[7464960,23858496,-92810016,-55595744,659232,-73499136,36472032,194756736,259597184,-9530368,-37504128,-142392320,-115088256,0]
def cfSpec4 : Array ℤ := #[3732480,98643744,-263408112,-199789712,-5670864,-439068672,172647376,672715200,975705664,-64015872,-106919104,-430348800,-371700544,1703936]
def cfSpec5 : Array ℤ := #[-27993600,274752000,-643935744,-621103680,-17742240,-1676901888,664081440,1901209344,2815848192,-277202176,-250548096,-1025537024,-866463360,24772608]
def cfSpec6 : Array ℤ := #[-100590336,595766880,-1428705648,-1716822768,-28665360,-4875005856,2000088432,4496968128,6323559872,-905006592,-493514176,-1938077568,-1331187648,166166528]
def cfSpec7 : Array ℤ := #[-192969216,1114108992,-2886070176,-4069073952,-30481920,-11588617344,4753561856,9042582912,10691299712,-2445138944,-816886272,-2818797568,-607302656,670302208]
def cfSpec8 : Array ℤ := #[-254041920,1898068464,-5154481008,-7990783296,-22821912,-23272355520,9228324408,15563347008,11628630528,-5624128896,-1125060768,-2838420480,3577474080,1747378176]
def cfSpec9 : Array ℤ := #[-246343680,2932836768,-7894556352,-12882023808,-12254544,-39921149952,15334737104,22916713152,279333504,-10609386560,-1279045184,-1178934016,13246583104,2772967424]
def cfSpec10 : Array ℤ := #[-180652032,3966830064,-10188732528,-17257245424,-4666680,-58535513808,22750425288,28759499712,-33477438912,-14783518848,-1195391136,1860391488,26695068768,1273317376]
def cfSpec11 : Array ℤ := #[-100776960,4551028416,-11008211040,-19797616608,-1205280,-73203132096,30554054304,30630523392,-92641975488,-10526122816,-915974784,4344146048,35482146048,-6436417536]
def cfSpec12 : Array ℤ := #[-42363648,4353180192,-9943922448,-20376661888,-190080,-77932552416,36122397056,27583008768,-165500439552,12782441664,-573139840,3981400064,26874360832,-21329127424]
def cfSpec13 : Array ℤ := #[-13063680,3445718400,-7507741824,-19811501696,-13824,-70547214336,35130484736,20921622720,-227596966336,60294335744,-290624896,321570688,-6881219072,-36664414208]
def cfSpec14 : Array ℤ := #[-2799360,2248339680,-4728918672,-18706879440,0,-54234197568,24386243424,13301368896,-254881628544,122527502656,-117831168,-4570885376,-59325780096,-38124401664]
def cfSpec15 : Array ℤ := #[-373248,1204155072,-2472578784,-16893920224,0,-35326252224,5583179328,7037788032,-238429891840,176108949888,-37355520,-7850065152,-110465136384,-12705796096]
def cfSpec16 : Array ℤ := #[-23328,525396456,-1063134720,-14012239696,0,-19412901840,-14360067944,3065673024,-188758544768,197466408192,-8928896,-8159254592,-138913468384,39288236544]
def cfSpec17 : Array ℤ := #[0,184333968,-370137600,-10283957376,0,-8935874784,-27627146544,1081698816,-127286824320,178789127040,-1512960,-6222415488,-135593150016,100542856704]
def cfSpec18 : Array ℤ := #[0,50886792,-101855232,-6521920512,0,-3407226240,-30630945320,301653504,-73262060032,132172509312,-161792,-3678121472,-107614774624,146386374784]
def cfSpec19 : Array ℤ := #[0,10665216,-21330432,-3526168256,0,-1058370816,-25401388896,64002048,-35935932288,79404891840,-8192,-1714060800,-70787896320,160248514304]
def cfSpec20 : Array ℤ := #[0,1596672,-3193344,-1611187536,0,-261239040,-16856898696,9703680,-14948616000,37789951232,0,-628769152,-38856581088,142283723904]
def cfSpec21 : Array ℤ := #[0,152064,-304128,-617116736,0,-49320576,-9182924112,935424,-5228672000,13204291072,0,-178691328,-17783895744,105823201024]
def cfSpec22 : Array ℤ := #[0,6912,-13824,-196082688,0,-6690816,-4144532280,43008,-1518190464,2445585984,0,-38081152,-6737397408,67005959424]
def cfSpec23 : Array ℤ := #[0,0,0,-50901504,0,-580608,-1549985664,0,-359244288,-638127104,0,-5737472,-2082713088,36423093504]
def cfSpec24 : Array ℤ := #[0,0,0,-10545856,0,-24192,-477034368,0,-67462912,-815587200,0,-545280,-512767488,17056477568]
def cfSpec25 : Array ℤ := #[0,0,0,-1680384,0,0,-119129856,0,-9666048,-421505344,0,-24576,-96476544,6879744256]
def cfSpec26 : Array ℤ := #[0,0,0,-193536,0,0,-23584512,0,-992256,-149748096,0,0,-12809472,2381665536]
def cfSpec27 : Array ℤ := #[0,0,0,-14336,0,0,-3566336,0,-65024,-39771904,0,0,-970240,702576896]
def cfSpec28 : Array ℤ := #[0,0,0,-512,0,0,-387200,0,-2048,-7990464,0,0,1664,174575488]
def cfSpec29 : Array ℤ := #[0,0,0,0,0,0,-26880,0,0,-1189376,0,0,7680,35907840]
def cfSpec30 : Array ℤ := #[0,0,0,0,0,0,-896,0,0,-124416,0,0,512,5957888]
def cfSpec31 : Array ℤ := #[0,0,0,0,0,0,0,0,0,-8192,0,0,0,766720]
def cfSpec32 : Array ℤ := #[0,0,0,0,0,0,0,0,0,-256,0,0,0,71808]
def cfSpec33 : Array ℤ := #[0,0,0,0,0,0,0,0,0,0,0,0,0,4352]
def cfSpec34 : Array ℤ := #[0,0,0,0,0,0,0,0,0,0,0,0,0,128]

def cfAt (c : Array ℤ) (i : ℕ) : ℤ := c.getD i 0

def polyAM {R : Type*} [CommRing R] (c : Array ℤ) (A M : R) : R :=
  (cfAt c 0 : R) * A^5 + (cfAt c 1 : R) * A^4 +
  (cfAt c 2 : R) * A^3 * M + (cfAt c 3 : R) * A^3 +
  (cfAt c 4 : R) * A^2 * M^2 + (cfAt c 5 : R) * A^2 * M + (cfAt c 6 : R) * A^2 +
  (cfAt c 7 : R) * A * M^2 + (cfAt c 8 : R) * A * M + (cfAt c 9 : R) * A +
  (cfAt c 10 : R) * M^3 + (cfAt c 11 : R) * M^2 + (cfAt c 12 : R) * M +
  (cfAt c 13 : R)

def valPoly {R : Type*} [CommRing R] (p : Table) (x v : R) : R :=
  ∑ i : Fin 11, ∑ j : Fin 6, (entry p i j : R) * (x^(i:ℕ) * (1 - x)^(10 - (i:ℕ))) *
    (v^(j:ℕ) * (1 - v)^(5 - (j:ℕ)))

private lemma map_valPoly {R S : Type*} [CommRing R] [CommRing S] (h : R →+* S)
    (p : Table) (x v : R) : h (valPoly p x v) = valPoly p (h x) (h v) := by
  simp [valPoly]

private lemma map_polyAM {R S : Type*} [CommRing R] [CommRing S] (h : R →+* S)
    (c : Array ℤ) (A M : R) : h (polyAM c A M) = polyAM c (h A) (h M) := by
  simp [polyAM]

def ctrlDiff {R : Type*} [CommRing R] (p : Table) (c : Array ℤ) (x v : R) : R :=
  valPoly p x v - polyAM c (1 + x^2 + v * (3 - 2*x - x^2)) (x^2)

private lemma map_ctrlDiff {R S : Type*} [CommRing R] [CommRing S] (h : R →+* S)
    (p : Table) (c : Array ℤ) (x v : R) : h (ctrlDiff p c x v) = ctrlDiff p c (h x) (h v) := by
  simp [ctrlDiff, map_valPoly, map_polyAM, map_ofNat]

private lemma nd_add {p q : Polynomial ℝ} {n : ℕ} (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) :
    (p + q).natDegree ≤ n :=
  le_trans (Polynomial.natDegree_add_le p q) (max_le hp hq)

private lemma nd_int (z : ℤ) : ((z : Polynomial ℝ)).natDegree ≤ 0 := by
  have h : (z : Polynomial ℝ) = Polynomial.C (z : ℝ) := by simp
  rw [h, Polynomial.natDegree_C]

private lemma natDegree_bern_le (d : ℕ) (i : Fin (d + 1)) :
    ((Polynomial.X : Polynomial ℝ) ^ (i : ℕ) * (1 - (Polynomial.X : Polynomial ℝ)) ^ (d - (i : ℕ))).natDegree ≤ d := by
  have h1 : ((Polynomial.X : Polynomial ℝ) ^ (i : ℕ)).natDegree ≤ (i : ℕ) := by simp
  have h1x : (1 - (Polynomial.X : Polynomial ℝ)).natDegree ≤ 1 := by compute_degree
  have h2 : ((1 - (Polynomial.X : Polynomial ℝ)) ^ (d - (i : ℕ))).natDegree ≤ d - (i : ℕ) :=
    Polynomial.natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left (d - (i : ℕ)) h1x)
  exact Polynomial.natDegree_mul_le.trans (by omega)

private lemma deg_x_valPoly (p : Table) (v : ℝ) :
    (valPoly p Polynomial.X (Polynomial.C v)).natDegree ≤ 10 := by
  unfold valPoly
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  have hc1 : ((entry p i j : Polynomial ℝ)).natDegree ≤ 0 := nd_int _
  have hc2 : (Polynomial.C v ^ (j : ℕ) * (1 - Polynomial.C v) ^ (5 - (j : ℕ))).natDegree ≤ 0 := by
    have h : Polynomial.C v ^ (j : ℕ) * (1 - Polynomial.C v) ^ (5 - (j : ℕ)) =
        Polynomial.C (v ^ (j : ℕ) * (1 - v) ^ (5 - (j : ℕ))) := by simp
    rw [h, Polynomial.natDegree_C]
  have hb := natDegree_bern_le 10 i
  have hm1 : ((entry p i j : Polynomial ℝ) *
      ((Polynomial.X : Polynomial ℝ) ^ (i : ℕ) * (1 - (Polynomial.X : Polynomial ℝ)) ^ (10 - (i : ℕ)))).natDegree ≤ 10 :=
    Polynomial.natDegree_mul_le.trans (by omega)
  exact Polynomial.natDegree_mul_le.trans (by omega)

private lemma deg_v_valPoly (p : Table) (x : ℝ) :
    (valPoly p (Polynomial.C x) Polynomial.X).natDegree ≤ 5 := by
  unfold valPoly
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  have hc1 : ((entry p i j : Polynomial ℝ) * (Polynomial.C x ^ (i : ℕ) * (1 - Polynomial.C x) ^ (10 - (i : ℕ)))).natDegree ≤ 0 := by
    have h : (entry p i j : Polynomial ℝ) * (Polynomial.C x ^ (i : ℕ) * (1 - Polynomial.C x) ^ (10 - (i : ℕ))) =
        Polynomial.C ((entry p i j : ℝ) * (x ^ (i : ℕ) * (1 - x) ^ (10 - (i : ℕ)))) := by simp
    rw [h, Polynomial.natDegree_C]
  have hb := natDegree_bern_le 5 j
  exact Polynomial.natDegree_mul_le.trans (by omega)

private lemma natDegree_term_le {A M : Polynomial ℝ} {dA dM : ℕ}
    (hA : A.natDegree ≤ dA) (hM : M.natDegree ≤ dM) (c : Polynomial ℝ) (hc : c.natDegree ≤ 0)
    (k l : ℕ) : (c * A ^ k * M ^ l).natDegree ≤ k * dA + l * dM := by
  have hpA : (A ^ k).natDegree ≤ k * dA := Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left k hA)
  have hpM : (M ^ l).natDegree ≤ l * dM := Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left l hM)
  have h1 : (c * A ^ k).natDegree ≤ k * dA := Polynomial.natDegree_mul_le.trans (by omega)
  exact Polynomial.natDegree_mul_le.trans (by omega)

private lemma natDegree_polyAM_le {A M : Polynomial ℝ} {dA dM : ℕ}
    (hA : A.natDegree ≤ dA) (hM : M.natDegree ≤ dM) (c : Array ℤ) (D : ℕ)
    (hD1 : 5 * dA ≤ D) (hD2 : 3 * dA + dM ≤ D) (hD3 : 2 * dA + 2 * dM ≤ D) (hD4 : 3 * dM ≤ D) :
    (polyAM c A M).natDegree ≤ D := by
  unfold polyAM
  have hA' (z : ℤ) (k : ℕ) (hk : k * dA ≤ D) : ((z : Polynomial ℝ) * A ^ k).natDegree ≤ D := by
    have := natDegree_term_le hA hM (z : Polynomial ℝ) (nd_int z) k 0
    simp only [pow_zero, mul_one, zero_mul, add_zero] at this; omega
  have hM' (z : ℤ) (l : ℕ) (hl : l * dM ≤ D) : ((z : Polynomial ℝ) * M ^ l).natDegree ≤ D := by
    have := natDegree_term_le hA hM (z : Polynomial ℝ) (nd_int z) 0 l
    simp only [pow_zero, mul_one, zero_mul, zero_add] at this; omega
  have hAM' (z : ℤ) (k l : ℕ) (hkl : k * dA + l * dM ≤ D) :
      ((z : Polynomial ℝ) * A ^ k * M ^ l).natDegree ≤ D :=
    (natDegree_term_le hA hM (z : Polynomial ℝ) (nd_int z) k l).trans hkl
  refine nd_add ?_ ((nd_int _).trans (Nat.zero_le D))
  refine nd_add ?_ (by simpa only [pow_one] using hM' _ 1 (by omega))
  refine nd_add ?_ (hM' _ 2 (by omega))
  refine nd_add ?_ (hM' _ 3 (by omega))
  refine nd_add ?_ (by simpa only [pow_one] using hA' _ 1 (by omega))
  refine nd_add ?_ (by simpa only [pow_one] using hAM' _ 1 1 (by omega))
  refine nd_add ?_ (by simpa only [pow_one] using hAM' _ 1 2 (by omega))
  refine nd_add ?_ (hA' _ 2 (by omega))
  refine nd_add ?_ (by simpa only [pow_one] using hAM' _ 2 1 (by omega))
  refine nd_add ?_ (hAM' _ 2 2 (by omega))
  refine nd_add ?_ (hA' _ 3 (by omega))
  refine nd_add ?_ (by simpa only [pow_one] using hAM' _ 3 1 (by omega))
  refine nd_add (hA' _ 5 (by omega)) (hA' _ 4 (by omega))

private lemma deg_x_ctrlDiff (p : Table) (c : Array ℤ) (v : ℝ) :
    (ctrlDiff p c Polynomial.X (Polynomial.C v)).natDegree ≤ 10 := by
  unfold ctrlDiff
  refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le (deg_x_valPoly p v) ?_)
  have hA : (1 + Polynomial.X ^ 2 + Polynomial.C v * (3 - 2 * Polynomial.X - Polynomial.X ^ 2)).natDegree ≤ 2 := by
    compute_degree!
  have hM : (Polynomial.X ^ 2 : Polynomial ℝ).natDegree ≤ 2 := by simp
  exact natDegree_polyAM_le hA hM c 10 (by omega) (by omega) (by omega) (by omega)

private lemma deg_v_ctrlDiff (p : Table) (c : Array ℤ) (x : ℝ) :
    (ctrlDiff p c (Polynomial.C x) Polynomial.X).natDegree ≤ 5 := by
  unfold ctrlDiff
  refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le (deg_v_valPoly p x) ?_)
  have hA : (1 + Polynomial.C x ^ 2 + Polynomial.X * (3 - 2 * Polynomial.C x - Polynomial.C x ^ 2)).natDegree ≤ 1 := by
    compute_degree!
  have hM : (Polynomial.C x ^ 2 : Polynomial ℝ).natDegree ≤ 0 := by rw [← map_pow, Polynomial.natDegree_C]
  exact natDegree_polyAM_le hA hM c 5 (by omega) (by omega) (by omega) (by omega)

private lemma fin_real_inj' {n : ℕ} : Function.Injective (fun i : Fin n => (i : ℝ)) := by
  intro i j h; apply Fin.ext; change ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) at h; exact_mod_cast h

private lemma array_getD_eq {α : Type*} (a : Array α) (i : ℕ) (d : α) :
    a.getD i d = a[i]?.getD d := by
  by_cases h : i < a.size
  · simp [Array.getD, h]
  · simp [Array.getD, h]

private lemma getD_eq_entry (p : Table) (i j : ℕ) : (p.getD i #[]).getD j 0 = entry p i j := by
  rw [array_getD_eq, array_getD_eq]; rfl

private def evalRow6 (r : Array ℤ) (mv0 mv1 mv2 mv3 mv4 mv5 : ℤ) : ℤ :=
  r.getD 0 0 * mv0 + r.getD 1 0 * mv1 + r.getD 2 0 * mv2 +
  r.getD 3 0 * mv3 + r.getD 4 0 * mv4 + r.getD 5 0 * mv5

private def evalValZ (p : Table) (x v : ℤ) : ℤ :=
  let y := 1 - x
  let w := 1 - v
  let x1 := x; let x2 := x1*x; let x3 := x2*x; let x4 := x3*x; let x5 := x4*x
  let x6 := x5*x; let x7 := x6*x; let x8 := x7*x; let x9 := x8*x; let x10 := x9*x
  let y1 := y; let y2 := y1*y; let y3 := y2*y; let y4 := y3*y; let y5 := y4*y
  let y6 := y5*y; let y7 := y6*y; let y8 := y7*y; let y9 := y8*y; let y10 := y9*y
  let w1 := w; let w2 := w1*w; let w3 := w2*w; let w4 := w3*w; let w5 := w4*w
  let v1 := v; let v2 := v1*v; let v3 := v2*v; let v4 := v3*v; let v5 := v4*v
  let mv0 := w5; let mv1 := v1*w4; let mv2 := v2*w3; let mv3 := v3*w2; let mv4 := v4*w1; let mv5 := v5
  evalRow6 (p.getD 0 #[]) mv0 mv1 mv2 mv3 mv4 mv5 * y10 +
  evalRow6 (p.getD 1 #[]) mv0 mv1 mv2 mv3 mv4 mv5 * (x1*y9) +
  evalRow6 (p.getD 2 #[]) mv0 mv1 mv2 mv3 mv4 mv5 * (x2*y8) +
  evalRow6 (p.getD 3 #[]) mv0 mv1 mv2 mv3 mv4 mv5 * (x3*y7) +
  evalRow6 (p.getD 4 #[]) mv0 mv1 mv2 mv3 mv4 mv5 * (x4*y6) +
  evalRow6 (p.getD 5 #[]) mv0 mv1 mv2 mv3 mv4 mv5 * (x5*y5) +
  evalRow6 (p.getD 6 #[]) mv0 mv1 mv2 mv3 mv4 mv5 * (x6*y4) +
  evalRow6 (p.getD 7 #[]) mv0 mv1 mv2 mv3 mv4 mv5 * (x7*y3) +
  evalRow6 (p.getD 8 #[]) mv0 mv1 mv2 mv3 mv4 mv5 * (x8*y2) +
  evalRow6 (p.getD 9 #[]) mv0 mv1 mv2 mv3 mv4 mv5 * (x9*y1) +
  evalRow6 (p.getD 10 #[]) mv0 mv1 mv2 mv3 mv4 mv5 * x10

private lemma evalRow6_eq (p : Table) (i : Fin 11) (v : ℤ) :
    evalRow6 (p.getD i #[]) ((1-v)^5) (v*(1-v)^4) (v^2*(1-v)^3) (v^3*(1-v)^2) (v^4*(1-v)) (v^5) =
    ∑ j : Fin 6, entry p i j * (v^(j:ℕ) * (1 - v)^(5 - (j:ℕ))) := by
  simp only [evalRow6, getD_eq_entry, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, add_zero]
  ring

private lemma evalValZ_eq (p : Table) (x v : ℤ) : evalValZ p x v = valPoly p x v := by
  have hx : ∀ i : Fin 11,
      (∑ j : Fin 6, entry p i j * (x^(i:ℕ) * (1 - x)^(10 - (i:ℕ))) * (v^(j:ℕ) * (1 - v)^(5 - (j:ℕ)))) =
      (∑ j : Fin 6, entry p i j * (v^(j:ℕ) * (1 - v)^(5 - (j:ℕ)))) * (x^(i:ℕ) * (1 - x)^(10 - (i:ℕ))) := by
    intro i; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => by ring
  unfold valPoly
  simp only [Int.cast_id]
  simp_rw [hx, ← evalRow6_eq]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, add_zero]
  unfold evalValZ
  dsimp only
  have hm0 : (1 - v) * (1 - v) * (1 - v) * (1 - v) * (1 - v) = (1 - v)^5 := by ring
  have hm1 : v * ((1 - v) * (1 - v) * (1 - v) * (1 - v)) = v * (1 - v)^4 := by ring
  have hm2 : v * v * ((1 - v) * (1 - v) * (1 - v)) = v^2 * (1 - v)^3 := by ring
  have hm3 : v * v * v * ((1 - v) * (1 - v)) = v^3 * (1 - v)^2 := by ring
  have hm4 : v * v * v * v * (1 - v) = v^4 * (1 - v) := by ring
  have hm5 : v * v * v * v * v = v^5 := by ring
  rw [hm0, hm1, hm2, hm3, hm4, hm5]
  ring

private def checkCtrlOne (p : Table) (c : Array ℤ) : Bool :=
  all11 fun i => all6 fun j =>
    let x : ℤ := i
    let v : ℤ := j
    decide (evalValZ p x v = polyAM c (1 + x^2 + v * (3 - 2*x - x^2)) (x^2))

private lemma ctrl_of_check (p : Table) (c : Array ℤ) (h : checkCtrlOne p c = true) (x v : ℝ) :
    value p x (1 - x) v (1 - v) = polyAM c (1 + x^2 + v * (3 - 2*x - x^2)) (x^2) := by
  have hgrid (i : Fin 11) (j : Fin 6) : ctrlDiff p c (i : ℤ) (j : ℤ) = 0 := by
    have hij := of_decide_eq_true (all6_at _ (all11_at _ h i) j)
    rw [evalValZ_eq] at hij
    exact sub_eq_zero.mpr hij
  have he (i : Fin 11) (j : Fin 6) : ctrlDiff p c (i : ℝ) (j : ℝ) = 0 := by
    have hc := congrArg (Int.castRingHom ℝ) (hgrid i j)
    rw [map_ctrlDiff] at hc; simpa using hc
  have h1 (j : Fin 6) : ctrlDiff p c Polynomial.X (Polynomial.C (j : ℝ)) = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (@fin_real_inj' 11) (fun i => ?_) ?_
    · change (Polynomial.evalRingHom (i : ℝ)) _ = _
      rw [map_ctrlDiff]; simpa using he i j
    · simpa using Nat.lt_succ_of_le (deg_x_ctrlDiff p c j)
  have h2 : ctrlDiff p c (Polynomial.C x) Polynomial.X = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (@fin_real_inj' 6) (fun j => ?_) ?_
    · have H := congrArg (Polynomial.evalRingHom x) (h1 j)
      rw [map_ctrlDiff] at H
      change (Polynomial.evalRingHom (j : ℝ)) _ = _
      rw [map_ctrlDiff]; simpa using H
    · simpa using Nat.lt_succ_of_le (deg_v_ctrlDiff p c x)
  have H := congrArg (Polynomial.evalRingHom v) h2
  rw [map_ctrlDiff] at H
  have hz : ctrlDiff p c x v = 0 := by simpa using H
  have hv : valPoly p x v = value p x (1 - x) v (1 - v) := rfl
  rw [← hv]; exact sub_eq_zero.mp hz

private lemma bL {a b : Bool} (h : (a && b) = true) : a = true := (Bool.and_eq_true a b ▸ h).1
private lemma bR {a b : Bool} (h : (a && b) = true) : b = true := (Bool.and_eq_true a b ▸ h).2

private def checkAllCtrl : Bool :=
  (((((checkCtrlOne table0 cfSpec0 && checkCtrlOne table1 cfSpec1) && (checkCtrlOne table2 cfSpec2 && checkCtrlOne table3 cfSpec3)) && ((checkCtrlOne table4 cfSpec4 && checkCtrlOne table5 cfSpec5) && (checkCtrlOne table6 cfSpec6 && checkCtrlOne table7 cfSpec7))) && (((checkCtrlOne table8 cfSpec8 && checkCtrlOne table9 cfSpec9) && (checkCtrlOne table10 cfSpec10 && checkCtrlOne table11 cfSpec11)) && ((checkCtrlOne table12 cfSpec12 && checkCtrlOne table13 cfSpec13) && (checkCtrlOne table14 cfSpec14 && (checkCtrlOne table15 cfSpec15 && checkCtrlOne table16 cfSpec16))))) && ((((checkCtrlOne table17 cfSpec17 && checkCtrlOne table18 cfSpec18) && (checkCtrlOne table19 cfSpec19 && checkCtrlOne table20 cfSpec20)) && ((checkCtrlOne table21 cfSpec21 && checkCtrlOne table22 cfSpec22) && (checkCtrlOne table23 cfSpec23 && (checkCtrlOne table24 cfSpec24 && checkCtrlOne table25 cfSpec25)))) && (((checkCtrlOne table26 cfSpec26 && checkCtrlOne table27 cfSpec27) && (checkCtrlOne table28 cfSpec28 && checkCtrlOne table29 cfSpec29)) && ((checkCtrlOne table30 cfSpec30 && checkCtrlOne table31 cfSpec31) && (checkCtrlOne table32 cfSpec32 && (checkCtrlOne table33 cfSpec33 && checkCtrlOne table34 cfSpec34))))))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma allCtrl_ok : checkAllCtrl = true := by decide +kernel

lemma ctrl0 (x v : ℝ) : value table0 x (1-x) v (1-v) =
    cf0 ((1+x^2 + v*(3-2*x-x^2))/2) (x^2) := by
  rw [ctrl_of_check table0 cfSpec0 (bL (bL (bL (bL (bL (allCtrl_ok)))))) x v]
  generalize (1+x^2 + v*(3-2*x-x^2)) = A
  generalize x^2 = M
  norm_num [polyAM, cfAt, Array.getD, cfSpec0, cf0]; ring

lemma ctrl1 (x v : ℝ) : value table1 x (1-x) v (1-v) =
    cf1 ((1+x^2 + v*(3-2*x-x^2))/2) (x^2) := by
  rw [ctrl_of_check table1 cfSpec1 (bR (bL (bL (bL (bL (allCtrl_ok)))))) x v]
  generalize (1+x^2 + v*(3-2*x-x^2)) = A
  generalize x^2 = M
  norm_num [polyAM, cfAt, Array.getD, cfSpec1, cf1]; ring

lemma ctrl2 (x v : ℝ) : value table2 x (1-x) v (1-v) =
    cf2 ((1+x^2 + v*(3-2*x-x^2))/2) (x^2) := by
  rw [ctrl_of_check table2 cfSpec2 (bL (bR (bL (bL (bL (allCtrl_ok)))))) x v]
  generalize (1+x^2 + v*(3-2*x-x^2)) = A
  generalize x^2 = M
  norm_num [polyAM, cfAt, Array.getD, cfSpec2, cf2]; ring

lemma ctrl3 (x v : ℝ) : value table3 x (1-x) v (1-v) =
    cf3 ((1+x^2 + v*(3-2*x-x^2))/2) (x^2) := by
  rw [ctrl_of_check table3 cfSpec3 (bR (bR (bL (bL (bL (allCtrl_ok)))))) x v]
  generalize (1+x^2 + v*(3-2*x-x^2)) = A
  generalize x^2 = M
  norm_num [polyAM, cfAt, Array.getD, cfSpec3, cf3]; ring

lemma ctrl4 (x v : ℝ) : value table4 x (1-x) v (1-v) =
    cf4 ((1+x^2 + v*(3-2*x-x^2))/2) (x^2) := by
  rw [ctrl_of_check table4 cfSpec4 (bL (bL (bR (bL (bL (allCtrl_ok)))))) x v]
  generalize (1+x^2 + v*(3-2*x-x^2)) = A
  generalize x^2 = M
  norm_num [polyAM, cfAt, Array.getD, cfSpec4, cf4]; ring

lemma ctrl5 (x v : ℝ) : value table5 x (1-x) v (1-v) =
    cf5 ((1+x^2 + v*(3-2*x-x^2))/2) (x^2) := by
  rw [ctrl_of_check table5 cfSpec5 (bR (bL (bR (bL (bL (allCtrl_ok)))))) x v]
  generalize (1+x^2 + v*(3-2*x-x^2)) = A
  generalize x^2 = M
  norm_num [polyAM, cfAt, Array.getD, cfSpec5, cf5]; ring

lemma ctrl6 (x v : ℝ) : value table6 x (1-x) v (1-v) =
    cf6 ((1+x^2 + v*(3-2*x-x^2))/2) (x^2) := by
  rw [ctrl_of_check table6 cfSpec6 (bL (bR (bR (bL (bL (allCtrl_ok)))))) x v]
  generalize (1+x^2 + v*(3-2*x-x^2)) = A
  generalize x^2 = M
  norm_num [polyAM, cfAt, Array.getD, cfSpec6, cf6]; ring

lemma ctrl7 (x v : ℝ) : value table7 x (1-x) v (1-v) =
    cf7 ((1+x^2 + v*(3-2*x-x^2))/2) (x^2) := by
  rw [ctrl_of_check table7 cfSpec7 (bR (bR (bR (bL (bL (allCtrl_ok)))))) x v]
  generalize (1+x^2 + v*(3-2*x-x^2)) = A
  generalize x^2 = M
  norm_num [polyAM, cfAt, Array.getD, cfSpec7, cf7]; ring

lemma ctrl8 (x v : ℝ) : value table8 x (1-x) v (1-v) =
    cf8 ((1+x^2 + v*(3-2*x-x^2))/2) (x^2) := by
  rw [ctrl_of_check table8 cfSpec8 (bL (bL (bL (bR (bL (allCtrl_ok)))))) x v]
  generalize (1+x^2 + v*(3-2*x-x^2)) = A
  generalize x^2 = M
  norm_num [polyAM, cfAt, Array.getD, cfSpec8, cf8]; ring

lemma ctrl9 (x v : ℝ) : value table9 x (1-x) v (1-v) =
    cf9 ((1+x^2 + v*(3-2*x-x^2))/2) (x^2) := by
  rw [ctrl_of_check table9 cfSpec9 (bR (bL (bL (bR (bL (allCtrl_ok)))))) x v]
  generalize (1+x^2 + v*(3-2*x-x^2)) = A
  generalize x^2 = M
  norm_num [polyAM, cfAt, Array.getD, cfSpec9, cf9]; ring

lemma ctrl10 (x v : ℝ) : value table10 x (1-x) v (1-v) =
    cf10 ((1+x^2 + v*(3-2*x-x^2))/2) (x^2) := by
  rw [ctrl_of_check table10 cfSpec10 (bL (bR (bL (bR (bL (allCtrl_ok)))))) x v]
  generalize (1+x^2 + v*(3-2*x-x^2)) = A
  generalize x^2 = M
  norm_num [polyAM, cfAt, Array.getD, cfSpec10, cf10]; ring

lemma ctrl11 (x v : ℝ) : value table11 x (1-x) v (1-v) =
    cf11 ((1+x^2 + v*(3-2*x-x^2))/2) (x^2) := by
  rw [ctrl_of_check table11 cfSpec11 (bR (bR (bL (bR (bL (allCtrl_ok)))))) x v]
  generalize (1+x^2 + v*(3-2*x-x^2)) = A
  generalize x^2 = M
  norm_num [polyAM, cfAt, Array.getD, cfSpec11, cf11]; ring

lemma ctrl12 (x v : ℝ) : value table12 x (1-x) v (1-v) =
    cf12 ((1+x^2 + v*(3-2*x-x^2))/2) (x^2) := by
  rw [ctrl_of_check table12 cfSpec12 (bL (bL (bR (bR (bL (allCtrl_ok)))))) x v]
  generalize (1+x^2 + v*(3-2*x-x^2)) = A
  generalize x^2 = M
  norm_num [polyAM, cfAt, Array.getD, cfSpec12, cf12]; ring

lemma ctrl13 (x v : ℝ) : value table13 x (1-x) v (1-v) =
    cf13 ((1+x^2 + v*(3-2*x-x^2))/2) (x^2) := by
  rw [ctrl_of_check table13 cfSpec13 (bR (bL (bR (bR (bL (allCtrl_ok)))))) x v]
  generalize (1+x^2 + v*(3-2*x-x^2)) = A
  generalize x^2 = M
  norm_num [polyAM, cfAt, Array.getD, cfSpec13, cf13]; ring

lemma ctrl14 (x v : ℝ) : value table14 x (1-x) v (1-v) =
    cf14 ((1+x^2 + v*(3-2*x-x^2))/2) (x^2) := by
  rw [ctrl_of_check table14 cfSpec14 (bL (bR (bR (bR (bL (allCtrl_ok)))))) x v]
  generalize (1+x^2 + v*(3-2*x-x^2)) = A
  generalize x^2 = M
  norm_num [polyAM, cfAt, Array.getD, cfSpec14, cf14]; ring

lemma ctrl15 (x v : ℝ) : value table15 x (1-x) v (1-v) =
    cf15 ((1+x^2 + v*(3-2*x-x^2))/2) (x^2) := by
  rw [ctrl_of_check table15 cfSpec15 (bL (bR (bR (bR (bR (bL (allCtrl_ok))))))) x v]
  generalize (1+x^2 + v*(3-2*x-x^2)) = A
  generalize x^2 = M
  norm_num [polyAM, cfAt, Array.getD, cfSpec15, cf15]; ring

lemma ctrl16 (x v : ℝ) : value table16 x (1-x) v (1-v) =
    cf16 ((1+x^2 + v*(3-2*x-x^2))/2) (x^2) := by
  rw [ctrl_of_check table16 cfSpec16 (bR (bR (bR (bR (bR (bL (allCtrl_ok))))))) x v]
  generalize (1+x^2 + v*(3-2*x-x^2)) = A
  generalize x^2 = M
  norm_num [polyAM, cfAt, Array.getD, cfSpec16, cf16]; ring

lemma ctrl17 (x v : ℝ) : value table17 x (1-x) v (1-v) =
    cf17 ((1+x^2 + v*(3-2*x-x^2))/2) (x^2) := by
  rw [ctrl_of_check table17 cfSpec17 (bL (bL (bL (bL (bR (allCtrl_ok)))))) x v]
  generalize (1+x^2 + v*(3-2*x-x^2)) = A
  generalize x^2 = M
  norm_num [polyAM, cfAt, Array.getD, cfSpec17, cf17]; ring

lemma ctrl18 (x v : ℝ) : value table18 x (1-x) v (1-v) =
    cf18 ((1+x^2 + v*(3-2*x-x^2))/2) (x^2) := by
  rw [ctrl_of_check table18 cfSpec18 (bR (bL (bL (bL (bR (allCtrl_ok)))))) x v]
  generalize (1+x^2 + v*(3-2*x-x^2)) = A
  generalize x^2 = M
  norm_num [polyAM, cfAt, Array.getD, cfSpec18, cf18]; ring

lemma ctrl19 (x v : ℝ) : value table19 x (1-x) v (1-v) =
    cf19 ((1+x^2 + v*(3-2*x-x^2))/2) (x^2) := by
  rw [ctrl_of_check table19 cfSpec19 (bL (bR (bL (bL (bR (allCtrl_ok)))))) x v]
  generalize (1+x^2 + v*(3-2*x-x^2)) = A
  generalize x^2 = M
  norm_num [polyAM, cfAt, Array.getD, cfSpec19, cf19]; ring

lemma ctrl20 (x v : ℝ) : value table20 x (1-x) v (1-v) =
    cf20 ((1+x^2 + v*(3-2*x-x^2))/2) (x^2) := by
  rw [ctrl_of_check table20 cfSpec20 (bR (bR (bL (bL (bR (allCtrl_ok)))))) x v]
  generalize (1+x^2 + v*(3-2*x-x^2)) = A
  generalize x^2 = M
  norm_num [polyAM, cfAt, Array.getD, cfSpec20, cf20]; ring

lemma ctrl21 (x v : ℝ) : value table21 x (1-x) v (1-v) =
    cf21 ((1+x^2 + v*(3-2*x-x^2))/2) (x^2) := by
  rw [ctrl_of_check table21 cfSpec21 (bL (bL (bR (bL (bR (allCtrl_ok)))))) x v]
  generalize (1+x^2 + v*(3-2*x-x^2)) = A
  generalize x^2 = M
  norm_num [polyAM, cfAt, Array.getD, cfSpec21, cf21]; ring

lemma ctrl22 (x v : ℝ) : value table22 x (1-x) v (1-v) =
    cf22 ((1+x^2 + v*(3-2*x-x^2))/2) (x^2) := by
  rw [ctrl_of_check table22 cfSpec22 (bR (bL (bR (bL (bR (allCtrl_ok)))))) x v]
  generalize (1+x^2 + v*(3-2*x-x^2)) = A
  generalize x^2 = M
  norm_num [polyAM, cfAt, Array.getD, cfSpec22, cf22]; ring

lemma ctrl23 (x v : ℝ) : value table23 x (1-x) v (1-v) =
    cf23 ((1+x^2 + v*(3-2*x-x^2))/2) (x^2) := by
  rw [ctrl_of_check table23 cfSpec23 (bL (bR (bR (bL (bR (allCtrl_ok)))))) x v]
  generalize (1+x^2 + v*(3-2*x-x^2)) = A
  generalize x^2 = M
  norm_num [polyAM, cfAt, Array.getD, cfSpec23, cf23]; ring

lemma ctrl24 (x v : ℝ) : value table24 x (1-x) v (1-v) =
    cf24 ((1+x^2 + v*(3-2*x-x^2))/2) (x^2) := by
  rw [ctrl_of_check table24 cfSpec24 (bL (bR (bR (bR (bL (bR (allCtrl_ok))))))) x v]
  generalize (1+x^2 + v*(3-2*x-x^2)) = A
  generalize x^2 = M
  norm_num [polyAM, cfAt, Array.getD, cfSpec24, cf24]; ring

lemma ctrl25 (x v : ℝ) : value table25 x (1-x) v (1-v) =
    cf25 ((1+x^2 + v*(3-2*x-x^2))/2) (x^2) := by
  rw [ctrl_of_check table25 cfSpec25 (bR (bR (bR (bR (bL (bR (allCtrl_ok))))))) x v]
  generalize (1+x^2 + v*(3-2*x-x^2)) = A
  generalize x^2 = M
  norm_num [polyAM, cfAt, Array.getD, cfSpec25, cf25]; ring

lemma ctrl26 (x v : ℝ) : value table26 x (1-x) v (1-v) =
    cf26 ((1+x^2 + v*(3-2*x-x^2))/2) (x^2) := by
  rw [ctrl_of_check table26 cfSpec26 (bL (bL (bL (bR (bR (allCtrl_ok)))))) x v]
  generalize (1+x^2 + v*(3-2*x-x^2)) = A
  generalize x^2 = M
  norm_num [polyAM, cfAt, Array.getD, cfSpec26, cf26]; ring

lemma ctrl27 (x v : ℝ) : value table27 x (1-x) v (1-v) =
    cf27 ((1+x^2 + v*(3-2*x-x^2))/2) (x^2) := by
  rw [ctrl_of_check table27 cfSpec27 (bR (bL (bL (bR (bR (allCtrl_ok)))))) x v]
  generalize (1+x^2 + v*(3-2*x-x^2)) = A
  generalize x^2 = M
  norm_num [polyAM, cfAt, Array.getD, cfSpec27, cf27]; ring

lemma ctrl28 (x v : ℝ) : value table28 x (1-x) v (1-v) =
    cf28 ((1+x^2 + v*(3-2*x-x^2))/2) (x^2) := by
  rw [ctrl_of_check table28 cfSpec28 (bL (bR (bL (bR (bR (allCtrl_ok)))))) x v]
  generalize (1+x^2 + v*(3-2*x-x^2)) = A
  generalize x^2 = M
  norm_num [polyAM, cfAt, Array.getD, cfSpec28, cf28]; ring

lemma ctrl29 (x v : ℝ) : value table29 x (1-x) v (1-v) =
    cf29 ((1+x^2 + v*(3-2*x-x^2))/2) (x^2) := by
  rw [ctrl_of_check table29 cfSpec29 (bR (bR (bL (bR (bR (allCtrl_ok)))))) x v]
  generalize (1+x^2 + v*(3-2*x-x^2)) = A
  generalize x^2 = M
  norm_num [polyAM, cfAt, Array.getD, cfSpec29, cf29]; ring

lemma ctrl30 (x v : ℝ) : value table30 x (1-x) v (1-v) =
    cf30 ((1+x^2 + v*(3-2*x-x^2))/2) (x^2) := by
  rw [ctrl_of_check table30 cfSpec30 (bL (bL (bR (bR (bR (allCtrl_ok)))))) x v]
  generalize (1+x^2 + v*(3-2*x-x^2)) = A
  generalize x^2 = M
  norm_num [polyAM, cfAt, Array.getD, cfSpec30, cf30]; ring

lemma ctrl31 (x v : ℝ) : value table31 x (1-x) v (1-v) =
    cf31 ((1+x^2 + v*(3-2*x-x^2))/2) (x^2) := by
  rw [ctrl_of_check table31 cfSpec31 (bR (bL (bR (bR (bR (allCtrl_ok)))))) x v]
  generalize (1+x^2 + v*(3-2*x-x^2)) = A
  generalize x^2 = M
  norm_num [polyAM, cfAt, Array.getD, cfSpec31, cf31]; ring

lemma ctrl32 (x v : ℝ) : value table32 x (1-x) v (1-v) =
    cf32 ((1+x^2 + v*(3-2*x-x^2))/2) (x^2) := by
  rw [ctrl_of_check table32 cfSpec32 (bL (bR (bR (bR (bR (allCtrl_ok)))))) x v]
  generalize (1+x^2 + v*(3-2*x-x^2)) = A
  generalize x^2 = M
  norm_num [polyAM, cfAt, Array.getD, cfSpec32, cf32]; ring

lemma ctrl33 (x v : ℝ) : value table33 x (1-x) v (1-v) =
    cf33 ((1+x^2 + v*(3-2*x-x^2))/2) (x^2) := by
  rw [ctrl_of_check table33 cfSpec33 (bL (bR (bR (bR (bR (bR (allCtrl_ok))))))) x v]
  generalize (1+x^2 + v*(3-2*x-x^2)) = A
  generalize x^2 = M
  norm_num [polyAM, cfAt, Array.getD, cfSpec33, cf33]

lemma ctrl34 (x v : ℝ) : value table34 x (1-x) v (1-v) =
    cf34 ((1+x^2 + v*(3-2*x-x^2))/2) (x^2) := by
  rw [ctrl_of_check table34 cfSpec34 (bR (bR (bR (bR (bR (bR (allCtrl_ok))))))) x v]
  generalize (1+x^2 + v*(3-2*x-x^2)) = A
  generalize x^2 = M
  norm_num [polyAM, cfAt, Array.getD, cfSpec34, cf34]

lemma table_values (x v : ℝ) : tables.map (fun p => value p x (1-x) v (1-v)) =
    (List.ofFn (coeffs ((1+x^2 + v*(3-2*x-x^2))/2) (x^2))).reverse := by
  simp only [tables,List.map_cons,List.map_nil,ctrl0,ctrl1,ctrl2,ctrl3,ctrl4,ctrl5,ctrl6,ctrl7,ctrl8,ctrl9,ctrl10,ctrl11,ctrl12,ctrl13,ctrl14,ctrl15,ctrl16,ctrl17,ctrl18,ctrl19,ctrl20,ctrl21,ctrl22,ctrl23,ctrl24,ctrl25,ctrl26,ctrl27,ctrl28,ctrl29,ctrl30,ctrl31,ctrl32,ctrl33,ctrl34]; rfl

def transform5 (a b c d : ℤ) : Table := #[
  #[d^5,b*d^4,b^2*d^3,b^3*d^2,b^4*d,b^5],
  #[5*c*d^4,4*b*c*d^3+a*d^4,3*b^2*c*d^2+2*a*b*d^3,2*b^3*c*d+3*a*b^2*d^2,b^4*c+4*a*b^3*d,5*a*b^4],
  #[10*c^2*d^3,6*b*c^2*d^2+4*a*c*d^3,3*b^2*c^2*d+6*a*b*c*d^2+a^2*d^3,b^3*c^2+6*a*b^2*c*d+3*a^2*b*d^2,4*a*b^3*c+6*a^2*b^2*d,10*a^2*b^3],
  #[10*c^3*d^2,4*b*c^3*d+6*a*c^2*d^2,b^2*c^3+6*a*b*c^2*d+3*a^2*c*d^2,3*a*b^2*c^2+6*a^2*b*c*d+a^3*d^2,6*a^2*b^2*c+4*a^3*b*d,10*a^3*b^2],
  #[5*c^4*d,b*c^4+4*a*c^3*d,2*a*b*c^3+3*a^2*c^2*d,3*a^2*b*c^2+2*a^3*c*d,4*a^3*b*c+a^4*d,5*a^4*b],
  #[c^5,a*c^4,a^2*c^3,a^3*c^2,a^4*c,a^5]]

set_option maxHeartbeats 5000000 in
lemma basisMatrix5 (a b c d : ℤ) (j : Fin 6) (x y : ℝ) :
    mon 5 j ((a:ℝ)*x+b*y) ((c:ℝ)*x+d*y) = ∑ i : Fin 6, (entry (transform5 a b c d) i j : ℝ)*mon 5 i x y := by
  fin_cases j <;> norm_num [Fin.sum_univ_succ,transform5,entry,mon] <;> ring

def row10_0 (_a b _c d : ℤ) : Array ℤ := #[d^10,b*d^9,b^2*d^8,b^3*d^7,b^4*d^6,b^5*d^5,b^6*d^4,b^7*d^3,b^8*d^2,b^9*d,b^10]

def row10_1 (a b c d : ℤ) : Array ℤ := #[10*c*d^9,9*b*c*d^8+a*d^9,8*b^2*c*d^7+2*a*b*d^8,7*b^3*c*d^6+3*a*b^2*d^7,6*b^4*c*d^5+4*a*b^3*d^6,5*b^5*c*d^4+5*a*b^4*d^5,4*b^6*c*d^3+6*a*b^5*d^4,3*b^7*c*d^2+7*a*b^6*d^3,2*b^8*c*d+8*a*b^7*d^2,b^9*c+9*a*b^8*d,10*a*b^9]

def row10_2 (a b c d : ℤ) : Array ℤ := #[45*c^2*d^8,36*b*c^2*d^7+9*a*c*d^8,28*b^2*c^2*d^6+16*a*b*c*d^7+a^2*d^8,21*b^3*c^2*d^5+21*a*b^2*c*d^6+3*a^2*b*d^7,15*b^4*c^2*d^4+24*a*b^3*c*d^5+6*a^2*b^2*d^6,10*b^5*c^2*d^3+25*a*b^4*c*d^4+10*a^2*b^3*d^5,6*b^6*c^2*d^2+24*a*b^5*c*d^3+15*a^2*b^4*d^4,3*b^7*c^2*d+21*a*b^6*c*d^2+21*a^2*b^5*d^3,b^8*c^2+16*a*b^7*c*d+28*a^2*b^6*d^2,9*a*b^8*c+36*a^2*b^7*d,45*a^2*b^8]

def row10_3 (a b c d : ℤ) : Array ℤ := #[120*c^3*d^7,84*b*c^3*d^6+36*a*c^2*d^7,56*b^2*c^3*d^5+56*a*b*c^2*d^6+8*a^2*c*d^7,35*b^3*c^3*d^4+63*a*b^2*c^2*d^5+21*a^2*b*c*d^6+a^3*d^7,20*b^4*c^3*d^3+60*a*b^3*c^2*d^4+36*a^2*b^2*c*d^5+4*a^3*b*d^6,10*b^5*c^3*d^2+50*a*b^4*c^2*d^3+50*a^2*b^3*c*d^4+10*a^3*b^2*d^5,4*b^6*c^3*d+36*a*b^5*c^2*d^2+60*a^2*b^4*c*d^3+20*a^3*b^3*d^4,b^7*c^3+21*a*b^6*c^2*d+63*a^2*b^5*c*d^2+35*a^3*b^4*d^3,8*a*b^7*c^2+56*a^2*b^6*c*d+56*a^3*b^5*d^2,36*a^2*b^7*c+84*a^3*b^6*d,120*a^3*b^7]

def row10_4 (a b c d : ℤ) : Array ℤ := #[210*c^4*d^6,126*b*c^4*d^5+84*a*c^3*d^6,70*b^2*c^4*d^4+112*a*b*c^3*d^5+28*a^2*c^2*d^6,35*b^3*c^4*d^3+105*a*b^2*c^3*d^4+63*a^2*b*c^2*d^5+7*a^3*c*d^6,15*b^4*c^4*d^2+80*a*b^3*c^3*d^3+90*a^2*b^2*c^2*d^4+24*a^3*b*c*d^5+a^4*d^6,5*b^5*c^4*d+50*a*b^4*c^3*d^2+100*a^2*b^3*c^2*d^3+50*a^3*b^2*c*d^4+5*a^4*b*d^5,b^6*c^4+24*a*b^5*c^3*d+90*a^2*b^4*c^2*d^2+80*a^3*b^3*c*d^3+15*a^4*b^2*d^4,7*a*b^6*c^3+63*a^2*b^5*c^2*d+105*a^3*b^4*c*d^2+35*a^4*b^3*d^3,28*a^2*b^6*c^2+112*a^3*b^5*c*d+70*a^4*b^4*d^2,84*a^3*b^6*c+126*a^4*b^5*d,210*a^4*b^6]

def row10_5 (a b c d : ℤ) : Array ℤ := #[252*c^5*d^5,126*b*c^5*d^4+126*a*c^4*d^5,56*b^2*c^5*d^3+140*a*b*c^4*d^4+56*a^2*c^3*d^5,21*b^3*c^5*d^2+105*a*b^2*c^4*d^3+105*a^2*b*c^3*d^4+21*a^3*c^2*d^5,6*b^4*c^5*d+60*a*b^3*c^4*d^2+120*a^2*b^2*c^3*d^3+60*a^3*b*c^2*d^4+6*a^4*c*d^5,b^5*c^5+25*a*b^4*c^4*d+100*a^2*b^3*c^3*d^2+100*a^3*b^2*c^2*d^3+25*a^4*b*c*d^4+a^5*d^5,6*a*b^5*c^4+60*a^2*b^4*c^3*d+120*a^3*b^3*c^2*d^2+60*a^4*b^2*c*d^3+6*a^5*b*d^4,21*a^2*b^5*c^3+105*a^3*b^4*c^2*d+105*a^4*b^3*c*d^2+21*a^5*b^2*d^3,56*a^3*b^5*c^2+140*a^4*b^4*c*d+56*a^5*b^3*d^2,126*a^4*b^5*c+126*a^5*b^4*d,252*a^5*b^5]

def row10_6 (a b c d : ℤ) : Array ℤ := #[210*c^6*d^4,84*b*c^6*d^3+126*a*c^5*d^4,28*b^2*c^6*d^2+112*a*b*c^5*d^3+70*a^2*c^4*d^4,7*b^3*c^6*d+63*a*b^2*c^5*d^2+105*a^2*b*c^4*d^3+35*a^3*c^3*d^4,b^4*c^6+24*a*b^3*c^5*d+90*a^2*b^2*c^4*d^2+80*a^3*b*c^3*d^3+15*a^4*c^2*d^4,5*a*b^4*c^5+50*a^2*b^3*c^4*d+100*a^3*b^2*c^3*d^2+50*a^4*b*c^2*d^3+5*a^5*c*d^4,15*a^2*b^4*c^4+80*a^3*b^3*c^3*d+90*a^4*b^2*c^2*d^2+24*a^5*b*c*d^3+a^6*d^4,35*a^3*b^4*c^3+105*a^4*b^3*c^2*d+63*a^5*b^2*c*d^2+7*a^6*b*d^3,70*a^4*b^4*c^2+112*a^5*b^3*c*d+28*a^6*b^2*d^2,126*a^5*b^4*c+84*a^6*b^3*d,210*a^6*b^4]

def row10_7 (a b c d : ℤ) : Array ℤ := #[120*c^7*d^3,36*b*c^7*d^2+84*a*c^6*d^3,8*b^2*c^7*d+56*a*b*c^6*d^2+56*a^2*c^5*d^3,b^3*c^7+21*a*b^2*c^6*d+63*a^2*b*c^5*d^2+35*a^3*c^4*d^3,4*a*b^3*c^6+36*a^2*b^2*c^5*d+60*a^3*b*c^4*d^2+20*a^4*c^3*d^3,10*a^2*b^3*c^5+50*a^3*b^2*c^4*d+50*a^4*b*c^3*d^2+10*a^5*c^2*d^3,20*a^3*b^3*c^4+60*a^4*b^2*c^3*d+36*a^5*b*c^2*d^2+4*a^6*c*d^3,35*a^4*b^3*c^3+63*a^5*b^2*c^2*d+21*a^6*b*c*d^2+a^7*d^3,56*a^5*b^3*c^2+56*a^6*b^2*c*d+8*a^7*b*d^2,84*a^6*b^3*c+36*a^7*b^2*d,120*a^7*b^3]

def row10_8 (a b c d : ℤ) : Array ℤ := #[45*c^8*d^2,9*b*c^8*d+36*a*c^7*d^2,b^2*c^8+16*a*b*c^7*d+28*a^2*c^6*d^2,3*a*b^2*c^7+21*a^2*b*c^6*d+21*a^3*c^5*d^2,6*a^2*b^2*c^6+24*a^3*b*c^5*d+15*a^4*c^4*d^2,10*a^3*b^2*c^5+25*a^4*b*c^4*d+10*a^5*c^3*d^2,15*a^4*b^2*c^4+24*a^5*b*c^3*d+6*a^6*c^2*d^2,21*a^5*b^2*c^3+21*a^6*b*c^2*d+3*a^7*c*d^2,28*a^6*b^2*c^2+16*a^7*b*c*d+a^8*d^2,36*a^7*b^2*c+9*a^8*b*d,45*a^8*b^2]

def row10_9 (a b c d : ℤ) : Array ℤ := #[10*c^9*d,b*c^9+9*a*c^8*d,2*a*b*c^8+8*a^2*c^7*d,3*a^2*b*c^7+7*a^3*c^6*d,4*a^3*b*c^6+6*a^4*c^5*d,5*a^4*b*c^5+5*a^5*c^4*d,6*a^5*b*c^4+4*a^6*c^3*d,7*a^6*b*c^3+3*a^7*c^2*d,8*a^7*b*c^2+2*a^8*c*d,9*a^8*b*c+a^9*d,10*a^9*b]

def row10_10 (a _b c _d : ℤ) : Array ℤ := #[c^10,a*c^9,a^2*c^8,a^3*c^7,a^4*c^6,a^5*c^5,a^6*c^4,a^7*c^3,a^8*c^2,a^9*c,a^10]

def transform10 (a b c d : ℤ) : Table := #[row10_0 a b c d,row10_1 a b c d,row10_2 a b c d,row10_3 a b c d,row10_4 a b c d,row10_5 a b c d,row10_6 a b c d,row10_7 a b c d,row10_8 a b c d,row10_9 a b c d,row10_10 a b c d]

set_option maxHeartbeats 5000000 in
lemma basisMatrix10 (a b c d : ℤ) (j : Fin 11) (x y : ℝ) :
    mon 10 j ((a:ℝ)*x+b*y) ((c:ℝ)*x+d*y) = ∑ i : Fin 11, (entry (transform10 a b c d) i j : ℝ)*mon 10 i x y := by
  fin_cases j <;> norm_num [Fin.sum_univ_succ,transform10,row10_0,row10_1,row10_2,row10_3,row10_4,row10_5,row10_6,row10_7,row10_8,row10_9,row10_10,entry,mon] <;> ring

def rectX (k : ℤ) (x y : ℝ) : ℝ := ((k+1 : ℤ) : ℝ)*x + k*y

def rectY (n k : ℤ) (x y : ℝ) : ℝ := ((n-k-1 : ℤ) : ℝ)*x + ((n-k : ℤ) : ℝ)*y

def BoxGood (n k m l : ℤ) : Prop := ∀ x y v w : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ v → 0 ≤ w →
  ∃ ms : List Mark, (bounds ms).1 ≤ 4 ∧ List.Forall₂ Mark.fits ms
    (tables.map (fun p => value p (rectX k x y) (rectY n k x y) (rectX l v w) (rectY m l v w)))

private lemma subboxL (n k : ℤ) (x y : ℝ) :
    rectX (2*k) x ((y-x)/2) = rectX k x y ∧ rectY (2*n) (2*k) x ((y-x)/2) = rectY n k x y := by
  unfold rectX rectY; push_cast; constructor <;> ring

private lemma subboxR (n k : ℤ) (x y : ℝ) :
    rectX (2*k+1) ((x-y)/2) y = rectX k x y ∧ rectY (2*n) (2*k+1) ((x-y)/2) y = rectY n k x y := by
  unfold rectX rectY; push_cast; constructor <;> ring

lemma box_x (n k m l : ℤ) (hL : BoxGood (2*n) (2*k) m l) (hR : BoxGood (2*n) (2*k+1) m l) : BoxGood n k m l := by
  intro x y v w hx hy hv hw; rcases le_total x y with h|h
  · obtain ⟨ms,hm,hs⟩ := hL x ((y-x)/2) v w hx (by linarith) hv hw
    exact ⟨ms,hm,by simpa only [(subboxL n k x y).1,(subboxL n k x y).2] using hs⟩
  · obtain ⟨ms,hm,hs⟩ := hR ((x-y)/2) y v w (by linarith) hy hv hw
    exact ⟨ms,hm,by simpa only [(subboxR n k x y).1,(subboxR n k x y).2] using hs⟩

lemma box_y (n k m l : ℤ) (hL : BoxGood n k (2*m) (2*l)) (hR : BoxGood n k (2*m) (2*l+1)) : BoxGood n k m l := by
  intro x y v w hx hy hv hw; rcases le_total v w with h|h
  · obtain ⟨ms,hm,hs⟩ := hL x y v ((w-v)/2) hx hy hv (by linarith)
    exact ⟨ms,hm,by simpa only [(subboxL m l v w).1,(subboxL m l v w).2] using hs⟩
  · obtain ⟨ms,hm,hs⟩ := hR x y ((v-w)/2) w hx hy (by linarith) hw
    exact ⟨ms,hm,by simpa only [(subboxR m l v w).1,(subboxR m l v w).2] using hs⟩

lemma box_root (h : BoxGood 1 0 1 0) : Good tables := by
  intro x y v w hx hy hv hw
  simpa [rectX,rectY] using h x y v w hx hy hv hw

def Pol (n k m l : ℤ) (p : Table) (s : Mark) : Prop :=
  ∀ x y v w : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ v → 0 ≤ w →
  s.fits (value p (rectX k x y) (rectY n k x y) (rectX l v w) (rectY m l v w))

lemma unmarked {n k m l : ℤ} {p : Table} : Pol n k m l p .both := fun _ _ _ _ _ _ _ _ => trivial

private lemma composeRect (n k r a : ℤ) (x y : ℝ) :
    rectX k (rectX a x y) (rectY r a x y) = rectX (k*r+a) x y ∧
    rectY n k (rectX a x y) (rectY r a x y) = rectY (n*r) (k*r+a) x y := by
  unfold rectX rectY; push_cast; constructor <;> ring

private lemma rect_pos {r a : ℤ} (ha : 0 ≤ a) (hr : a < r) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ rectX a x y ∧ 0 ≤ rectY r a x y := by
  have h₁ : 0 ≤ a+1 := by omega
  have h₂ : 0 ≤ r-a-1 := by omega
  have h₃ : 0 ≤ r-a := by omega
  unfold rectX rectY; constructor <;> positivity

lemma carry {n k m l : ℤ} {p : Table} {s : Mark} (h : Pol n k m l p s) (r a t b : ℤ)
    (h₀ : 0 ≤ a ∧ a < r ∧ 0 ≤ b ∧ b < t := by decide) : Pol (n*r) (k*r+a) (m*t) (l*t+b) p s := by
  intro x y v w hx hy hv hw
  have hp := rect_pos h₀.1 h₀.2.1 hx hy
  have hq := rect_pos h₀.2.2.1 h₀.2.2.2 hv hw
  have hh := h _ _ _ _ hp.1 hp.2 hq.1 hq.2
  simpa only [(composeRect n k r a x y).1,(composeRect n k r a x y).2,
    (composeRect m l t b v w).1,(composeRect m l t b v w).2] using hh

lemma from_marks {n k m l : ℤ} {ms : List Mark}
    (hs : List.Forall₂ (fun s p => Pol n k m l p s) ms tables) (h : (bounds ms).1 ≤ 4) : BoxGood n k m l := by
  intro x y v w hx hy hv hw
  refine ⟨ms,h,?_⟩
  generalize ht : tables = ts at hs ⊢
  clear ht h
  induction hs with
  | nil => constructor
  | cons z _ ih => exact .cons (z _ _ _ _ hx hy hv hw) ih

def dot11 (U p : Table) (i j : ℕ) : ℤ :=
  entry U i 0 * entry p 0 j +
  entry U i 1 * entry p 1 j +
  entry U i 2 * entry p 2 j +
  entry U i 3 * entry p 3 j +
  entry U i 4 * entry p 4 j +
  entry U i 5 * entry p 5 j +
  entry U i 6 * entry p 6 j +
  entry U i 7 * entry p 7 j +
  entry U i 8 * entry p 8 j +
  entry U i 9 * entry p 9 j +
  entry U i 10 * entry p 10 j

def projected (U V p : Table) (i j : ℕ) : ℤ :=
  entry V j 0 * dot11 U p i 0 +
  entry V j 1 * dot11 U p i 1 +
  entry V j 2 * dot11 U p i 2 +
  entry V j 3 * dot11 U p i 3 +
  entry V j 4 * dot11 U p i 4 +
  entry V j 5 * dot11 U p i 5

lemma projected_eq (U V p : Table) (i : Fin 11) (j : Fin 6) :
    entry (ty V (tx U p)) i j = projected U V p i j := by
  rw [entry_ty]; simp_rw [entry_tx]
  simp [Fin.sum_univ_succ,projected,dot11,add_assoc]

def rowDot11F (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 : ℤ)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 : Array ℤ) (j : ℕ) : ℤ :=
  u0 * p0.getD j 0 + u1 * p1.getD j 0 + u2 * p2.getD j 0 +
  u3 * p3.getD j 0 + u4 * p4.getD j 0 + u5 * p5.getD j 0 +
  u6 * p6.getD j 0 + u7 * p7.getD j 0 + u8 * p8.getD j 0 +
  u9 * p9.getD j 0 + u10 * p10.getD j 0

private lemma rowDot11F_eq (U p : Table) (i j : ℕ) :
    rowDot11F ((U.getD i #[]).getD 0 0) ((U.getD i #[]).getD 1 0)
      ((U.getD i #[]).getD 2 0) ((U.getD i #[]).getD 3 0)
      ((U.getD i #[]).getD 4 0) ((U.getD i #[]).getD 5 0)
      ((U.getD i #[]).getD 6 0) ((U.getD i #[]).getD 7 0)
      ((U.getD i #[]).getD 8 0) ((U.getD i #[]).getD 9 0)
      ((U.getD i #[]).getD 10 0)
      (p.getD 0 #[]) (p.getD 1 #[]) (p.getD 2 #[]) (p.getD 3 #[])
      (p.getD 4 #[]) (p.getD 5 #[]) (p.getD 6 #[]) (p.getD 7 #[])
      (p.getD 8 #[]) (p.getD 9 #[]) (p.getD 10 #[]) j = dot11 U p i j := by
  simp only [rowDot11F, dot11, getD_eq_entry]

def checkRow6Val (vj : Array ℤ) (d0 d1 d2 d3 d4 d5 : ℤ) (sg : Mark) : Bool :=
  let val := vj.getD 0 0 * d0 + vj.getD 1 0 * d1 + vj.getD 2 0 * d2 +
             vj.getD 3 0 * d3 + vj.getD 4 0 * d4 + vj.getD 5 0 * d5
  match sg with
  | .up => decide (0 ≤ val)
  | .down => decide (val ≤ 0)
  | .both => true

def checkRow6 (v0 v1 v2 v3 v4 v5 : Array ℤ) (d0 d1 d2 d3 d4 d5 : ℤ) (sg : Mark) : Bool :=
  checkRow6Val v0 d0 d1 d2 d3 d4 d5 sg &&
  checkRow6Val v1 d0 d1 d2 d3 d4 d5 sg &&
  checkRow6Val v2 d0 d1 d2 d3 d4 d5 sg &&
  checkRow6Val v3 d0 d1 d2 d3 d4 d5 sg &&
  checkRow6Val v4 d0 d1 d2 d3 d4 d5 sg &&
  checkRow6Val v5 d0 d1 d2 d3 d4 d5 sg

def hasMarkRow (v0 v1 v2 v3 v4 v5 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 ui : Array ℤ) (sg : Mark) : Bool :=
  let u0 := ui.getD 0 0; let u1 := ui.getD 1 0; let u2 := ui.getD 2 0
  let u3 := ui.getD 3 0; let u4 := ui.getD 4 0; let u5 := ui.getD 5 0
  let u6 := ui.getD 6 0; let u7 := ui.getD 7 0; let u8 := ui.getD 8 0
  let u9 := ui.getD 9 0; let u10 := ui.getD 10 0
  let d0 := rowDot11F u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 0
  let d1 := rowDot11F u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 1
  let d2 := rowDot11F u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 2
  let d3 := rowDot11F u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 3
  let d4 := rowDot11F u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 4
  let d5 := rowDot11F u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 5
  checkRow6 v0 v1 v2 v3 v4 v5 d0 d1 d2 d3 d4 d5 sg

def hasMark (U V p : Table) (sg : Mark) : Bool :=
  let v0 := V.getD 0 #[]; let v1 := V.getD 1 #[]; let v2 := V.getD 2 #[]
  let v3 := V.getD 3 #[]; let v4 := V.getD 4 #[]; let v5 := V.getD 5 #[]
  let p0 := p.getD 0 #[]; let p1 := p.getD 1 #[]; let p2 := p.getD 2 #[]
  let p3 := p.getD 3 #[]; let p4 := p.getD 4 #[]; let p5 := p.getD 5 #[]
  let p6 := p.getD 6 #[]; let p7 := p.getD 7 #[]; let p8 := p.getD 8 #[]
  let p9 := p.getD 9 #[]; let p10 := p.getD 10 #[]
  all11 fun i => hasMarkRow v0 v1 v2 v3 v4 v5 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 (U.getD i #[]) sg

private lemma checkRow6_spec (V : Table) (d0 d1 d2 d3 d4 d5 : ℤ) (sg : Mark)
    (h : checkRow6 (V.getD 0 #[]) (V.getD 1 #[]) (V.getD 2 #[]) (V.getD 3 #[]) (V.getD 4 #[]) (V.getD 5 #[])
           d0 d1 d2 d3 d4 d5 sg = true) (j : Fin 6) :
    checkRow6Val (V.getD j #[]) d0 d1 d2 d3 d4 d5 sg = true := by
  unfold checkRow6 at h
  simp only [Bool.and_eq_true] at h
  fin_cases j
  · exact h.1.1.1.1.1
  · exact h.1.1.1.1.2
  · exact h.1.1.1.2
  · exact h.1.1.2
  · exact h.1.2
  · exact h.2

private def markCond (U V p : Table) (i j : ℕ) : Mark → Bool
  | .up => decide (0 ≤ projected U V p i j)
  | .down => decide (projected U V p i j ≤ 0)
  | .both => true

private lemma hasMarkRow_spec (U V p : Table) (i : Fin 11) (j : Fin 6) (sg : Mark)
    (h : hasMarkRow (V.getD 0 #[]) (V.getD 1 #[]) (V.getD 2 #[]) (V.getD 3 #[]) (V.getD 4 #[]) (V.getD 5 #[])
           (p.getD 0 #[]) (p.getD 1 #[]) (p.getD 2 #[]) (p.getD 3 #[]) (p.getD 4 #[]) (p.getD 5 #[])
           (p.getD 6 #[]) (p.getD 7 #[]) (p.getD 8 #[]) (p.getD 9 #[]) (p.getD 10 #[])
           (U.getD i #[]) sg = true) :
    markCond U V p i j sg = true := by
  unfold hasMarkRow at h
  dsimp only at h
  have H := checkRow6_spec V _ _ _ _ _ _ sg h j
  rw [rowDot11F_eq, rowDot11F_eq, rowDot11F_eq, rowDot11F_eq, rowDot11F_eq, rowDot11F_eq] at H
  unfold checkRow6Val at H
  dsimp only at H
  cases sg
  · simp only [getD_eq_entry, decide_eq_true_eq] at H
    simp only [markCond, projected]
    exact decide_eq_true H
  · simp only [getD_eq_entry, decide_eq_true_eq] at H
    simp only [markCond, projected]
    exact decide_eq_true H
  · rfl

private lemma hasMark_spec (U V p : Table) (sg : Mark) (h : hasMark U V p sg = true)
    (i : Fin 11) (j : Fin 6) :
    markCond U V p i j sg = true := by
  unfold hasMark at h
  dsimp only at h
  exact hasMarkRow_spec U V p i j sg (all11_at _ h i)

lemma signedValue (U V p : Table) (sg : Mark) (h : hasMark U V p sg = true)
    (x y v w : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    sg.fits (value (ty V (tx U p)) x y v w) := by
  cases sg with
  | up =>
    apply Finset.sum_nonneg; intro i _; apply Finset.sum_nonneg; intro j _
    have H := hasMark_spec U V p .up h i j
    have Hp : 0 ≤ projected U V p i j := of_decide_eq_true H
    rw [projected_eq]; have T : (0:ℝ) ≤ projected U V p i j := by exact_mod_cast Hp
    unfold mon; positivity
  | down =>
    apply Finset.sum_nonpos; intro i _; apply Finset.sum_nonpos; intro j _
    have H := hasMark_spec U V p .down h i j
    have Hp : projected U V p i j ≤ 0 := of_decide_eq_true H
    rw [projected_eq]; apply mul_nonpos_of_nonpos_of_nonneg _ (by unfold mon; positivity)
    apply mul_nonpos_of_nonpos_of_nonneg _ (by unfold mon; positivity); exact_mod_cast Hp
  | both => trivial

lemma signFast (n k m l : ℤ) (U V p : Table) (s : Mark)
    (hU : U = transform10 (k+1) k (n-k-1) (n-k))
    (hV : V = transform5 (l+1) l (m-l-1) (m-l))
    (h : hasMark U V p s = true) : Pol n k m l p s := by
  intro x y v w hx hy hv hw
  have e1 : value p (rectX k x y) (rectY n k x y) (rectX l v w) (rectY m l v w) =
      value (tx U p) x y (rectX l v w) (rectY m l v w) :=
    tx_spec _ _ _ _ _ _ _ _ (fun j => hU ▸ basisMatrix10 _ _ _ _ j x y)
  have e2 : value (tx U p) x y (rectX l v w) (rectY m l v w) = value (ty V (tx U p)) x y v w :=
    ty_spec _ _ _ _ _ _ _ _ (fun j => hV ▸ basisMatrix5 _ _ _ _ j v w)
  rw [e1,e2]; exact signedValue U V p s h x y v w hx hy hv hw

/- Integer matrices for the parameter rectangles in the subdivision. -/
def mx5_1_0 : Table := #[
  #[1,0,0,0,0,0],
  #[0,1,0,0,0,0],
  #[0,0,1,0,0,0],
  #[0,0,0,1,0,0],
  #[0,0,0,0,1,0],
  #[0,0,0,0,0,1]]
def mx5_2_0 : Table := #[
  #[32,0,0,0,0,0],
  #[80,16,0,0,0,0],
  #[80,32,8,0,0,0],
  #[40,24,12,4,0,0],
  #[10,8,6,4,2,0],
  #[1,1,1,1,1,1]]
def mx5_2_1 : Table := #[
  #[1,1,1,1,1,1],
  #[0,2,4,6,8,10],
  #[0,0,4,12,24,40],
  #[0,0,0,8,32,80],
  #[0,0,0,0,16,80],
  #[0,0,0,0,0,32]]
def mx5_4_2 : Table := #[
  #[32,32,32,32,32,32],
  #[80,112,144,176,208,240],
  #[80,144,240,368,528,720],
  #[40,88,184,360,648,1080],
  #[10,26,66,162,378,810],
  #[1,3,9,27,81,243]]
def mx5_4_3 : Table := #[
  #[1,3,9,27,81,243],
  #[0,4,24,108,432,1620],
  #[0,0,16,144,864,4320],
  #[0,0,0,64,768,5760],
  #[0,0,0,0,256,3840],
  #[0,0,0,0,0,1024]]
def mx5_8_6 : Table := #[
  #[32,96,288,864,2592,7776],
  #[80,304,1104,3888,13392,45360],
  #[80,368,1616,6768,27216,105840],
  #[40,216,1128,5656,27048,123480],
  #[10,62,378,2254,13034,72030],
  #[1,7,49,343,2401,16807]]
def mx5_8_7 : Table := #[
  #[1,7,49,343,2401,16807],
  #[0,8,112,1176,10976,96040],
  #[0,0,64,1344,18816,219520],
  #[0,0,0,512,14336,250880],
  #[0,0,0,0,4096,143360],
  #[0,0,0,0,0,32768]]
def mx5_16_12 : Table := #[
  #[1024,3072,9216,27648,82944,248832],
  #[3840,12544,40704,131328,421632,1347840],
  #[5760,20352,71296,247680,853632,2920320],
  #[4320,16416,61920,231712,859872,3163680],
  #[1620,6588,26676,107484,430612,1713660],
  #[243,1053,4563,19773,85683,371293]]
def mx5_16_14 : Table := #[
  #[32,224,1568,10976,76832,537824],
  #[80,688,5712,46256,367696,2881200],
  #[80,816,8016,75824,693840,6174000],
  #[40,472,5416,60120,642600,6615000],
  #[10,134,1770,22950,290250,3543750],
  #[1,15,225,3375,50625,759375]]
def mx5_16_15 : Table := #[
  #[1,15,225,3375,50625,759375],
  #[0,16,480,10800,216000,4050000],
  #[0,0,256,11520,345600,8640000],
  #[0,0,0,4096,245760,9216000],
  #[0,0,0,0,65536,4915200],
  #[0,0,0,0,0,1048576]]
def mx5_32_24 : Table := #[
  #[32768,98304,294912,884736,2654208,7962624],
  #[143360,446464,1388544,4313088,13381632,41472000],
  #[250880,809984,2610176,8395776,26956800,86400000],
  #[219520,733824,2448768,8156800,27120000,90000000],
  #[96040,332024,1146600,3955000,13625000,46875000],
  #[16807,60025,214375,765625,2734375,9765625]]
def mx5_32_25 : Table := #[
  #[16807,60025,214375,765625,2734375,9765625],
  #[72030,268226,997150,3701250,13718750,50781250],
  #[123480,478632,1850968,7141800,27495000,105625000],
  #[105840,426384,1714032,6875024,27513200,109850000],
  #[45360,189648,791856,3301584,13744432,57122000],
  #[7776,33696,146016,632736,2741856,11881376]]
def mx5_32_26 : Table := #[
  #[7776,33696,146016,632736,2741856,11881376],
  #[32400,147312,668304,3025776,13674128,61691760],
  #[54000,257040,1219824,5771792,27231984,128129040],
  #[45000,223800,1109960,5489208,27066312,133057080],
  #[18750,97250,503550,2602530,13423806,69087330],
  #[3125,16875,91125,492075,2657205,14348907]]
def mx5_32_27 : Table := #[
  #[3125,16875,91125,492075,2657205,14348907],
  #[12500,71500,407700,2318220,13148244,74401740],
  #[20000,120800,726560,4351968,25964064,154314720],
  #[16000,101760,644736,4068736,25570944,160030080],
  #[6400,42752,284928,1894144,12556544,82978560],
  #[1024,7168,50176,351232,2458624,17210368]]
def mx5_32_28 : Table := #[
  #[1024,7168,50176,351232,2458624,17210368],
  #[3840,28928,216832,1618176,12029696,89125120],
  #[5760,46464,372352,2964864,23463552,184616320],
  #[4320,37152,317664,2699552,22794464,191209760],
  #[1620,14796,134676,1221132,11023828,99019340],
  #[243,2349,22707,219501,2121843,20511149]]
def mx5_32_29 : Table := #[
  #[243,2349,22707,219501,2121843,20511149],
  #[810,8694,92394,973878,10194602,106092150],
  #[1080,12744,148536,1710536,19477560,219501000],
  #[720,9264,117968,1485360,18478800,227070000],
  #[240,3344,46320,637200,8694000,117450000],
  #[32,480,7200,108000,1620000,24300000]]
def mx5_32_30 : Table := #[
  #[32,480,7200,108000,1620000,24300000],
  #[80,1456,25680,442800,7506000,125550000],
  #[80,1712,35408,707760,13726800,259470000],
  #[40,984,23592,548824,12339240,268119000],
  #[10,278,7626,205654,5421962,138528150],
  #[1,31,961,29791,923521,28629151]]
def mx5_32_31 : Table := #[
  #[1,31,961,29791,923521,28629151],
  #[0,32,1984,92256,3813248,147763360],
  #[0,0,1024,95232,5904384,305059840],
  #[0,0,0,32768,4063232,314900480],
  #[0,0,0,0,1048576,162529280],
  #[0,0,0,0,0,33554432]]
def mx5_64_50 : Table := #[
  #[537824,1920800,6860000,24500000,87500000,312500000],
  #[2497040,9093616,33104400,120470000,438250000,1593750000],
  #[4637360,17214288,63866544,236824400,877710000,3251250000],
  #[4306120,16287544,61574344,232656696,878617800,3316275000],
  #[1999270,7702682,29666598,114220314,439605414,1691300250],
  #[371293,1456611,5714397,22418019,87947613,345025251]]
def mx5_64_51 : Table := #[
  #[371293,1456611,5714397,22418019,87947613,345025251],
  #[1713660,6863428,27477372,109959876,439870716,1758952260],
  #[3163680,12930528,52817440,215614944,879679008,3586883040],
  #[2920320,12175488,50732928,211269760,879275904,3657214080],
  #[1347840,5730048,24350976,103444224,439259392,1864462080],
  #[248832,1078272,4672512,20247552,87739392,380204032]]
def mx5_64_52 : Table := #[
  #[248832,1078272,4672512,20247552,87739392,380204032],
  #[1140480,5052672,22374144,99031296,438134528,1937578240],
  #[2090880,9465984,42825600,193618048,874776448,3949678720],
  #[1916640,8863008,40957664,189146400,872902368,4025634080],
  #[878460,4147396,19572476,92326212,435316348,2051525060],
  #[161051,775973,3738779,18014117,86795291,418195493]]
def mx5_64_53 : Table := #[
  #[161051,775973,3738779,18014117,86795291,418195493],
  #[732050,3612334,17815314,87814958,432636562,2130429870],
  #[1331000,6722760,33929016,171101384,862183224,4341253320],
  #[1210000,6252400,32283280,166560624,858668688,4423163760],
  #[550000,2906000,15346800,81006480,427357296,2253309840],
  #[100000,540000,2916000,15746400,85030560,459165024]]
def mx5_64_54 : Table := #[
  #[100000,540000,2916000,15746400,85030560,459165024],
  #[450000,2494000,13813200,76457520,422948304,2338340400],
  #[810000,4604400,26148880,148364784,841032720,4763286000],
  #[729000,4247640,24727464,143818840,835698600,4851495000],
  #[328050,1958094,11681010,69641550,414939250,2470668750],
  #[59049,360855,2205225,13476375,82355625,503284375]]
def mx5_64_55 : Table := #[
  #[59049,360855,2205225,13476375,82355625,503284375],
  #[262440,1650456,10371240,65122200,408617000,2562175000],
  #[466560,3017088,19488384,125741440,810409600,5217520000],
  #[414720,2755584,18289664,121261056,803066880,5312384000],
  #[184320,1257472,8572928,58404864,397594624,2704486400],
  #[32768,229376,1605632,11239424,78675968,550731776]]
def mx5_64_56 : Table := #[
  #[32768,229376,1605632,11239424,78675968,550731776],
  #[143360,1036288,7483392,53989376,389165056,2802831360],
  #[250880,1870848,13931520,103599104,769348608,5705763840],
  #[219520,1687168,12949888,99262080,759798144,5807652480],
  #[96040,760088,6010536,47487384,374830632,2955680280],
  #[16807,136857,1114407,9074457,73892007,601692057]]
def mx5_64_57 : Table := #[
  #[16807,136857,1114407,9074457,73892007,601692057],
  #[72030,608482,5133534,43257186,364089438,3061240290],
  #[123480,1080744,9441880,82341288,716833368,6229892520],
  #[105840,958608,8667504,78232720,704865648,6339188880],
  #[45360,424656,3971376,37098192,346128688,3225201360],
  #[7776,75168,726624,7024032,67898976,656356768]]
def mx5_64_58 : Table := #[
  #[7776,75168,726624,7024032,67898976,656356768],
  #[32400,327024,3294864,33142128,332861072,3338366320],
  #[54000,568080,5961456,62408464,651795184,6791848720],
  #[45000,492600,5380040,58620984,637190088,6908949560],
  #[18750,213250,2421950,27465090,310943806,3514034690],
  #[3125,36875,435125,5134475,60586805,714924299]]
def mx5_64_59 : Table := #[
  #[3125,36875,435125,5134475,60586805,714924299],
  #[12500,155500,1929300,23879660,294924244,3635208300],
  #[20000,261600,3409440,44279264,573111840,7393644000],
  #[16000,219520,3001984,40913280,555638400,7518960000],
  #[6400,91904,1317120,18835200,268704000,3823200000],
  #[1024,15360,230400,3456000,51840000,777600000]]
def mx5_64_60 : Table := #[
  #[1024,15360,230400,3456000,51840000,777600000],
  #[3840,61696,986880,15724800,249696000,3952800000],
  #[5760,98688,1681024,28471680,479606400,8037360000],
  #[4320,78624,1423584,25635616,459022560,8171316000],
  #[1620,31212,599508,11475564,218809684,4153752300],
  #[243,4941,100467,2042829,41537523,844596301]]
def mx5_64_61 : Table := #[
  #[243,4941,100467,2042829,41537523,844596301],
  #[810,18198,405162,8952726,196565546,4292210710],
  #[1080,26568,646200,15544264,370046008,8725149640],
  #[720,19248,509648,13354800,346098384,8868184880],
  #[240,6928,198896,5673744,160633072,4506782480],
  #[32,992,30752,953312,29552672,916132832]]
def mx5_128_102 : Table := #[
  #[11881376,46611552,182860704,717376608,2814323616,11040808032],
  #[57122000,226343728,896789712,3552799536,14073740496,55745256240],
  #[109850000,439602800,1758967184,7037077104,28149104016,112583556720],
  #[105625000,426855000,1724773800,6968216152,28148053416,113687317080],
  #[50781250,207218750,845501250,3449516350,14072138306,57400949310],
  #[9765625,40234375,165765625,682954375,2813772025,11592740743]]
def mx5_128_103 : Table := #[
  #[9765625,40234375,165765625,682954375,2813772025,11592740743],
  #[46875000,195125000,812155000,3380027400,14065581944,58526458120],
  #[90000000,378480000,1591388800,6690260352,28121827968,118189352320],
  #[86400000,367027200,1558895616,6620177408,28109659136,119336821760],
  #[41472000,177942528,763416576,3274911744,14047301632,60247715840],
  #[7962624,34504704,149520384,647921664,2807660544,12166529024]]
def mx5_128_104 : Table := #[
  #[7962624,34504704,149520384,647921664,2807660544,12166529024],
  #[38154240,167104512,731787264,3204304896,14029303808,61417574400],
  #[73128960,323675136,1432378368,6337750016,28037667840,124016256000],
  #[70081920,313438848,1401617792,6266655360,28013731200,125208720000],
  #[33580920,151746824,685647480,3097672200,13993371000,63206325000],
  #[6436343,29383305,134141175,612383625,2795664375,12762815625]]
def mx5_128_105 : Table := #[
  #[6436343,29383305,134141175,612383625,2795664375,12762815625],
  #[30782510,142086226,655764270,3026164050,13963272750,64421831250],
  #[58888280,274796456,1282084952,5980622760,27893338200,130070745000],
  #[56327920,265698576,1253082864,5908739344,27856965360,131309514000],
  #[26939440,128436176,612261936,2918348752,13908684848,66280040400],
  #[5153632,24831136,119640928,576451744,2777449312,13382255776]]
def mx5_128_106 : Table := #[
  #[5153632,24831136,119640928,576451744,2777449312,13382255776],
  #[24596880,119875184,584147344,2846168688,13865808272,67542517360],
  #[46957680,231454608,1140624496,5620019088,27685459056,136359421840],
  #[44823240,223417656,1113400008,5547582776,27635962568,137645831480],
  #[21392910,107816562,543311118,2737524594,13791534094,69472188530],
  #[4084101,20809467,106029189,540243963,2752671621,14025517307]]
def mx5_128_107 : Table := #[
  #[4084101,20809467,106029189,540243963,2752671621,14025517307],
  #[19448100,100278108,516980772,2664915036,13735182116,70782984540],
  #[37044000,193263840,1008078624,5257144544,27410554656,142889015520],
  #[35280000,186211200,982643840,5184404352,27347227776,144224426880],
  #[16800000,89696000,478828800,2555815680,13640161536,72786159360],
  #[3200000,17280000,93312000,503884800,2720977920,14693280768]]
def mx5_128_108 : Table := #[
  #[3200000,17280000,93312000,503884800,2720977920,14693280768],
  #[15200000,83104000,454291200,2483032320,13569617664,74146648320],
  #[28880000,159843200,884493440,4893270912,27065052288,149666382720],
  #[27436000,153699360,860853216,4820489248,26987168736,151052182560],
  #[13032100,73885148,418830756,2373871324,13452761252,76225406940],
  #[2476099,14204989,81491779,467505469,2682005059,15386239549]]
def mx5_128_109 : Table := #[
  #[2476099,14204989,81491779,467505469,2682005059,15386239549],
  #[11728890,68164742,396087034,2301183366,13367289338,77636988550],
  #[22223160,130817736,769878328,4529737416,26645281080,156698509000],
  #[21053520,125508528,748030032,4457190320,26552094800,158136110000],
  #[9972720,60197904,363314160,2192374800,13227478000,79793450000],
  #[1889568,11547360,70567200,431244000,2635380000,16105100000]]
def mx5_128_110 : Table := #[
  #[1889568,11547360,70567200,431244000,2635380000,16105100000],
  #[8922960,55275696,342357840,2120065200,13126322000,81257550000],
  #[16854480,105819696,664204752,4167951920,26147470800,163992510000],
  #[15918120,101272536,644138024,4095929304,26038215720,165483351000],
  #[7516890,48452006,312256986,2012043942,12962406618,83493872550],
  #[1419857,9270831,60533073,395245359,2580719697,16850581551]]
def mx5_128_111 : Table := #[
  #[1419857,9270831,60533073,395245359,2580719697,16850581551],
  #[6681680,44256304,293073744,1940409648,12844790352,85011942960],
  #[12577280,84489728,567405056,3809392128,25567750656,171555632640],
  #[11837440,80633856,549101568,3738198016,25441640448,173101178880],
  #[5570560,38469632,265617408,1833631744,12655591424,87330324480],
  #[1048576,7340032,51380224,359661568,2517630976,17623416832]]
def mx5_128_112 : Table := #[
  #[1048576,7340032,51380224,359661568,2517630976,17623416832],
  #[4915200,34930688,248184832,1762983936,12520718336,88903843840],
  #[9216000,66478080,479371264,3455606784,24902148096,179395256320],
  #[8640000,63244800,462804480,3385559552,24758375936,180996999680],
  #[4050000,30078000,223333200,1657926960,12305025616,91306522160],
  #[759375,5720625,43095375,324651825,2445710415,18424351793]]
def mx5_128_113 : Table := #[
  #[759375,5720625,43095375,324651825,2445710415,18424351793],
  #[3543750,27128250,207620550,1588591290,12152078534,92936995770],
  #[6615000,51445800,399953880,3108216872,24146587608,187518894120],
  #[6174000,48768720,385088816,3039649488,23984325936,189178353360],
  #[2881200,23109968,185321136,1485754704,11908650672,95426249040],
  #[537824,4379424,35661024,290382624,2364544224,19254145824]]
def mx5_128_114 : Table := #[
  #[537824,4379424,35661024,290382624,2364544224,19254145824],
  #[2497040,20684272,171289104,1418071536,11736791568,97115209200],
  #[4637360,39065936,328960688,2768916816,23296889520,195934194000],
  #[4306120,36881208,315753672,2702177080,23115289800,197652915000],
  #[1999270,17404634,151476390,1317977050,11464355750,99693356250],
  #[371293,3284515,29055325,257027875,2273708125,20113571875]]
def mx5_128_115 : Table := #[
  #[371293,3284515,29055325,257027875,2273708125,20113571875],
  #[1713660,15440516,139076860,1252301700,11272725500,101442362500],
  #[3163680,29024736,266155552,2439475680,22348768800,204648940000],
  #[2920320,27271296,254553984,2374926464,22146961280,206428496000],
  #[1347840,12807936,121671936,1155493632,10969977088,104111763200],
  #[248832,2405376,23251968,224769024,2172767232,21003416576]]
def mx5_128_118 : Table := #[
  #[100000,1180000,13924000,164303200,1938777760,22877577568],
  #[450000,5438000,65678800,792832560,9565732304,115357276720],
  #[810000,10018800,123823120,1529141232,18869414928,232669761520],
  #[729000,9224280,116629416,1473495128,18601549736,234641539160],
  #[328050,4244238,54884466,709381134,9163894642,118315013390],
  #[59049,780759,10323369,136497879,1804805289,23863536599]]
def mx5_128_119 : Table := #[
  #[59049,780759,10323369,136497879,1804805289,23863536599],
  #[262440,3563352,48349224,655597656,8884158248,120320352600],
  #[466560,6500736,90488448,1258361216,17482604160,242662896000],
  #[414720,5925888,84595712,1206512640,17190835200,244702080000],
  #[184320,2699264,39505920,577843200,8446464000,123379200000],
  #[32768,491520,7372800,110592000,1658880000,24883200000]]
def mx5_128_120 : Table := #[
  #[32768,491520,7372800,110592000,1658880000,24883200000],
  #[143360,2215936,34222080,528076800,8142336000,125452800000],
  #[250880,3992576,63460352,1007447040,15974323200,252996480000],
  #[219520,3593856,58767744,959837824,15657671040,255104784000],
  #[96040,1616216,27178536,456682072,7667316008,128615328600],
  #[16807,290521,5021863,86806489,1500512167,25937424601]]
def mx5_128_121 : Table := #[
  #[16807,290521,5021863,86806489,1500512167,25937424601],
  #[72030,1288994,23040094,411382818,7337805662,130758917410],
  #[123480,2284968,42213976,778640808,14339629656,263679139240],
  #[105840,2023056,38610288,735729296,13997092208,265858305680],
  #[45360,894672,17629488,347035344,6823956784,134027740880],
  #[7776,158112,3214944,65370528,1329200736,27027081632]]
def mx5_256_226 : Table := #[
  #[24300000,183060000,1379052000,10388858400,78262733280,589579257376],
  #[117450000,891702000,6769558800,51389606640,390090089744,2960940075760],
  #[227070000,1737320400,13291118640,101672802256,777696047152,5948083161040],
  #[219501000,1692327480,13046510024,100569464376,775174656456,5974402113080],
  #[106092150,824201866,6402638966,49734657162,386307863158,3000418760330],
  #[20511149,160552787,1256740781,9837246803,77001897389,602738989907]]
def mx5_256_227 : Table := #[
  #[20511149,160552787,1256740781,9837246803,77001897389,602738989907],
  #[99019340,781326004,6164768844,48637810868,383711110732,3026971138740],
  #[191209760,1520824032,12095029536,96182079200,764787646752,6080611626720],
  #[184616320,1480022656,11863868800,95091956352,762114966912,6107398462080],
  #[89125120,720113408,5818020096,47002685184,379701948672,3067151650560],
  #[17210368,140141568,1141152768,9292243968,75665415168,616132666368]]
def mx5_256_242 : Table := #[
  #[537824,9296672,160699616,2777807648,48016389344,829997587232],
  #[2497040,43865584,770390544,13526644208,237445863952,4167136646640],
  #[4637360,82769232,1476743856,26337895760,469567791792,8368712439120],
  #[4306120,78068536,1414845640,25632054072,464191747272,8403293895480],
  #[1999270,36808538,677523366,12467960154,229381627302,4219009125210],
  #[371293,6940323,129730653,2424965283,45328197213,847288609443]]
def mx5_256_243 : Table := #[
  #[371293,6940323,129730653,2424965283,45328197213,847288609443],
  #[1713660,32594692,619783164,11781692676,223900344828,4253876969220],
  #[3163680,61213152,1183884832,22886984160,442266617376,8542765271520],
  #[2920320,57462912,1130221440,22220607616,436679413632,8577920684160],
  #[1347840,26963712,539267328,10782207744,215519367424,4306610384640],
  #[248832,5059584,102878208,2091856896,42534423552,864866612224]]
def mx10_1_0 : Table := #[
  #[1,0,0,0,0,0,0,0,0,0,0],
  #[0,1,0,0,0,0,0,0,0,0,0],
  #[0,0,1,0,0,0,0,0,0,0,0],
  #[0,0,0,1,0,0,0,0,0,0,0],
  #[0,0,0,0,1,0,0,0,0,0,0],
  #[0,0,0,0,0,1,0,0,0,0,0],
  #[0,0,0,0,0,0,1,0,0,0,0],
  #[0,0,0,0,0,0,0,1,0,0,0],
  #[0,0,0,0,0,0,0,0,1,0,0],
  #[0,0,0,0,0,0,0,0,0,1,0],
  #[0,0,0,0,0,0,0,0,0,0,1]]
def mx10_2_0 : Table := #[
  #[1024,0,0,0,0,0,0,0,0,0,0],
  #[5120,512,0,0,0,0,0,0,0,0,0],
  #[11520,2304,256,0,0,0,0,0,0,0,0],
  #[15360,4608,1024,128,0,0,0,0,0,0,0],
  #[13440,5376,1792,448,64,0,0,0,0,0,0],
  #[8064,4032,1792,672,192,32,0,0,0,0,0],
  #[3360,2016,1120,560,240,80,16,0,0,0,0],
  #[960,672,448,280,160,80,32,8,0,0,0],
  #[180,144,112,84,60,40,24,12,4,0,0],
  #[20,18,16,14,12,10,8,6,4,2,0],
  #[1,1,1,1,1,1,1,1,1,1,1]]
def mx10_2_1 : Table := #[
  #[1,1,1,1,1,1,1,1,1,1,1],
  #[0,2,4,6,8,10,12,14,16,18,20],
  #[0,0,4,12,24,40,60,84,112,144,180],
  #[0,0,0,8,32,80,160,280,448,672,960],
  #[0,0,0,0,16,80,240,560,1120,2016,3360],
  #[0,0,0,0,0,32,192,672,1792,4032,8064],
  #[0,0,0,0,0,0,64,448,1792,5376,13440],
  #[0,0,0,0,0,0,0,128,1024,4608,15360],
  #[0,0,0,0,0,0,0,0,256,2304,11520],
  #[0,0,0,0,0,0,0,0,0,512,5120],
  #[0,0,0,0,0,0,0,0,0,0,1024]]
def mx10_4_0 : Table := #[
  #[1048576,0,0,0,0,0,0,0,0,0,0],
  #[7864320,262144,0,0,0,0,0,0,0,0,0],
  #[26542080,1769472,65536,0,0,0,0,0,0,0,0],
  #[53084160,5308416,393216,16384,0,0,0,0,0,0,0],
  #[69672960,9289728,1032192,86016,4096,0,0,0,0,0,0],
  #[62705664,10450944,1548288,193536,18432,1024,0,0,0,0,0],
  #[39191040,7838208,1451520,241920,34560,3840,256,0,0,0,0],
  #[16796160,3919104,870912,181440,34560,5760,768,64,0,0,0],
  #[4723920,1259712,326592,81648,19440,4320,864,144,16,0,0],
  #[787320,236196,69984,20412,5832,1620,432,108,24,4,0],
  #[59049,19683,6561,2187,729,243,81,27,9,3,1]]
def mx10_4_1 : Table := #[
  #[59049,19683,6561,2187,729,243,81,27,9,3,1],
  #[393660,157464,61236,23328,8748,3240,1188,432,156,56,20],
  #[1180980,551124,247860,107892,45684,18900,7668,3060,1204,468,180],
  #[2099520,1119744,575424,285120,136512,63360,28608,12608,5440,2304,960],
  #[2449440,1469664,852768,477792,258336,134880,68128,33376,15904,7392,3360],
  #[1959552,1306368,846720,532224,323712,190208,107904,59136,31360,16128,8064],
  #[1088640,798336,572544,400512,272512,179840,114816,70784,42112,24192,13440],
  #[414720,331776,261120,201728,152576,112640,80896,56320,37888,24576,15360],
  #[103680,89856,77056,65280,54528,44800,36096,28416,21760,16128,11520],
  #[15360,14336,13312,12288,11264,10240,9216,8192,7168,6144,5120],
  #[1024,1024,1024,1024,1024,1024,1024,1024,1024,1024,1024]]
def mx10_4_2 : Table := #[
  #[1024,1024,1024,1024,1024,1024,1024,1024,1024,1024,1024],
  #[5120,6144,7168,8192,9216,10240,11264,12288,13312,14336,15360],
  #[11520,16128,21760,28416,36096,44800,54528,65280,77056,89856,103680],
  #[15360,24576,37888,56320,80896,112640,152576,201728,261120,331776,414720],
  #[13440,24192,42112,70784,114816,179840,272512,400512,572544,798336,1088640],
  #[8064,16128,31360,59136,107904,190208,323712,532224,846720,1306368,1959552],
  #[3360,7392,15904,33376,68128,134880,258336,477792,852768,1469664,2449440],
  #[960,2304,5440,12608,28608,63360,136512,285120,575424,1119744,2099520],
  #[180,468,1204,3060,7668,18900,45684,107892,247860,551124,1180980],
  #[20,56,156,432,1188,3240,8748,23328,61236,157464,393660],
  #[1,3,9,27,81,243,729,2187,6561,19683,59049]]
def mx10_4_3 : Table := #[
  #[1,3,9,27,81,243,729,2187,6561,19683,59049],
  #[0,4,24,108,432,1620,5832,20412,69984,236196,787320],
  #[0,0,16,144,864,4320,19440,81648,326592,1259712,4723920],
  #[0,0,0,64,768,5760,34560,181440,870912,3919104,16796160],
  #[0,0,0,0,256,3840,34560,241920,1451520,7838208,39191040],
  #[0,0,0,0,0,1024,18432,193536,1548288,10450944,62705664],
  #[0,0,0,0,0,0,4096,86016,1032192,9289728,69672960],
  #[0,0,0,0,0,0,0,16384,393216,5308416,53084160],
  #[0,0,0,0,0,0,0,0,65536,1769472,26542080],
  #[0,0,0,0,0,0,0,0,0,262144,7864320],
  #[0,0,0,0,0,0,0,0,0,0,1048576]]
def mx10_8_0 : Table := #[
  #[1073741824,0,0,0,0,0,0,0,0,0,0],
  #[9395240960,134217728,0,0,0,0,0,0,0,0,0],
  #[36993761280,1056964608,16777216,0,0,0,0,0,0,0,0],
  #[86318776320,3699376128,117440512,2097152,0,0,0,0,0,0,0],
  #[132175626240,7552892928,359661568,12845056,262144,0,0,0,0,0,0],
  #[138784407552,9913171968,629407744,33718272,1376256,32768,0,0,0,0,0],
  #[101196963840,8674025472,688414720,49172480,3010560,143360,4096,0,0,0,0],
  #[50598481920,5059848192,481890304,43025920,3512320,250880,14336,512,0,0,0],
  #[16602626880,1897443072,210827008,22588608,2304960,219520,18816,1344,64,0,0],
  #[3228288560,415065672,52706752,6588344,806736,96040,10976,1176,112,8,0],
  #[282475249,40353607,5764801,823543,117649,16807,2401,343,49,7,1]]
def mx10_8_1 : Table := #[
  #[282475249,40353607,5764801,823543,117649,16807,2401,343,49,7,1],
  #[2421216420,392006468,62589268,9882516,1546244,240100,37044,5684,868,132,20],
  #[9338977620,1689910236,299769652,52236156,8960532,1516060,253428,41916,6868,1116,180],
  #[21346234560,4269246912,835778496,160271552,30140096,5566400,1011136,180928,31936,5568,960],
  #[32019351840,7013762784,1505369376,316471008,65167648,13149920,2602272,505568,96544,18144,3360],
  #[32934190464,7841473920,1833826176,420819840,94679424,20873600,4508544,954240,198016,40320,8064],
  #[23524421760,6049137024,1532732544,382209408,93681792,22542720,5319808,1230208,278656,61824,13440],
  #[11522165760,3182312448,869170176,234482688,62401536,16358400,4217856,1068032,265216,64512,15360],
  #[3703553280,1093430016,320433408,93125376,26811648,7637760,2149632,596736,163072,43776,11520],
  #[705438720,221709312,69424128,21648384,6718464,2073600,635904,193536,58368,17408,5120],
  #[60466176,20155392,6718464,2239488,746496,248832,82944,27648,9216,3072,1024]]
def mx10_8_2 : Table := #[
  #[60466176,20155392,6718464,2239488,746496,248832,82944,27648,9216,3072,1024],
  #[503884800,181398528,64945152,23141376,8211456,2903040,1022976,359424,125952,44032,15360],
  #[1889568000,730632960,280122624,106562304,40248576,15102720,5633280,2089728,771328,283392,103680],
  #[4199040000,1735603200,710415360,288064512,115762176,46126080,18232320,7152640,2786304,1078272,414720],
  #[6123600000,2694384000,1173916800,506459520,216383616,91570560,38392960,15953280,6572160,2685312,1088640],
  #[6123600000,2857680000,1321488000,605404800,274711680,123453568,54942336,24216192,10571904,4572288,1959552],
  #[4252500000,2097900000,1026900000,498540000,239956000,114463200,54095904,25322976,11739168,5388768,2449440],
  #[2025000000,1053000000,544200000,279400000,142440000,72072000,36175680,18004032,8880192,4339008,2099520],
  #[632812500,345937500,188312500,102037500,55012500,29497500,15722100,8325180,4376916,2283228,1180980],
  #[117187500,67187500,38437500,21937500,12487500,7087500,4009500,2259900,1268460,708588,393660],
  #[9765625,5859375,3515625,2109375,1265625,759375,455625,273375,164025,98415,59049]]
def mx10_8_3 : Table := #[
  #[9765625,5859375,3515625,2109375,1265625,759375,455625,273375,164025,98415,59049],
  #[78125000,50000000,31875000,20250000,12825000,8100000,5103000,3207600,2012040,1259712,787320],
  #[281250000,191250000,129250000,86850000,58050000,38610000,25563600,16854480,11069136,7243344,4723920],
  #[600000000,432000000,308800000,219200000,154560000,108288000,75409920,52213248,35956224,24634368,16796160],
  #[840000000,638400000,481600000,360640000,268096000,197875200,145027584,105573888,76349952,54867456,39191040],
  #[806400000,645120000,512512000,404275200,316600320,246136832,189960192,145539072,110702592,83607552,62705664],
  #[537600000,451584000,377036800,312811520,257826816,211066880,171581440,138485760,110960640,88252416,69672960],
  #[245760000,216268800,189399040,165019648,142999552,123207680,105512960,89784320,75890688,63700992,53084160],
  #[73728000,67829760,62193664,56819712,51707904,46858240,42270720,37945344,33882112,30081024,26542080],
  #[13107200,12582912,12058624,11534336,11010048,10485760,9961472,9437184,8912896,8388608,7864320],
  #[1048576,1048576,1048576,1048576,1048576,1048576,1048576,1048576,1048576,1048576,1048576]]
def mx10_8_4 : Table := #[
  #[1048576,1048576,1048576,1048576,1048576,1048576,1048576,1048576,1048576,1048576,1048576],
  #[7864320,8388608,8912896,9437184,9961472,10485760,11010048,11534336,12058624,12582912,13107200],
  #[26542080,30081024,33882112,37945344,42270720,46858240,51707904,56819712,62193664,67829760,73728000],
  #[53084160,63700992,75890688,89784320,105512960,123207680,142999552,165019648,189399040,216268800,245760000],
  #[69672960,88252416,110960640,138485760,171581440,211066880,257826816,312811520,377036800,451584000,537600000],
  #[62705664,83607552,110702592,145539072,189960192,246136832,316600320,404275200,512512000,645120000,806400000],
  #[39191040,54867456,76349952,105573888,145027584,197875200,268096000,360640000,481600000,638400000,840000000],
  #[16796160,24634368,35956224,52213248,75409920,108288000,154560000,219200000,308800000,432000000,600000000],
  #[4723920,7243344,11069136,16854480,25563600,38610000,58050000,86850000,129250000,191250000,281250000],
  #[787320,1259712,2012040,3207600,5103000,8100000,12825000,20250000,31875000,50000000,78125000],
  #[59049,98415,164025,273375,455625,759375,1265625,2109375,3515625,5859375,9765625]]
def mx10_8_5 : Table := #[
  #[59049,98415,164025,273375,455625,759375,1265625,2109375,3515625,5859375,9765625],
  #[393660,708588,1268460,2259900,4009500,7087500,12487500,21937500,38437500,67187500,117187500],
  #[1180980,2283228,4376916,8325180,15722100,29497500,55012500,102037500,188312500,345937500,632812500],
  #[2099520,4339008,8880192,18004032,36175680,72072000,142440000,279400000,544200000,1053000000,2025000000],
  #[2449440,5388768,11739168,25322976,54095904,114463200,239956000,498540000,1026900000,2097900000,4252500000],
  #[1959552,4572288,10571904,24216192,54942336,123453568,274711680,605404800,1321488000,2857680000,6123600000],
  #[1088640,2685312,6572160,15953280,38392960,91570560,216383616,506459520,1173916800,2694384000,6123600000],
  #[414720,1078272,2786304,7152640,18232320,46126080,115762176,288064512,710415360,1735603200,4199040000],
  #[103680,283392,771328,2089728,5633280,15102720,40248576,106562304,280122624,730632960,1889568000],
  #[15360,44032,125952,359424,1022976,2903040,8211456,23141376,64945152,181398528,503884800],
  #[1024,3072,9216,27648,82944,248832,746496,2239488,6718464,20155392,60466176]]
def mx10_8_6 : Table := #[
  #[1024,3072,9216,27648,82944,248832,746496,2239488,6718464,20155392,60466176],
  #[5120,17408,58368,193536,635904,2073600,6718464,21648384,69424128,221709312,705438720],
  #[11520,43776,163072,596736,2149632,7637760,26811648,93125376,320433408,1093430016,3703553280],
  #[15360,64512,265216,1068032,4217856,16358400,62401536,234482688,869170176,3182312448,11522165760],
  #[13440,61824,278656,1230208,5319808,22542720,93681792,382209408,1532732544,6049137024,23524421760],
  #[8064,40320,198016,954240,4508544,20873600,94679424,420819840,1833826176,7841473920,32934190464],
  #[3360,18144,96544,505568,2602272,13149920,65167648,316471008,1505369376,7013762784,32019351840],
  #[960,5568,31936,180928,1011136,5566400,30140096,160271552,835778496,4269246912,21346234560],
  #[180,1116,6868,41916,253428,1516060,8960532,52236156,299769652,1689910236,9338977620],
  #[20,132,868,5684,37044,240100,1546244,9882516,62589268,392006468,2421216420],
  #[1,7,49,343,2401,16807,117649,823543,5764801,40353607,282475249]]
def mx10_8_7 : Table := #[
  #[1,7,49,343,2401,16807,117649,823543,5764801,40353607,282475249],
  #[0,8,112,1176,10976,96040,806736,6588344,52706752,415065672,3228288560],
  #[0,0,64,1344,18816,219520,2304960,22588608,210827008,1897443072,16602626880],
  #[0,0,0,512,14336,250880,3512320,43025920,481890304,5059848192,50598481920],
  #[0,0,0,0,4096,143360,3010560,49172480,688414720,8674025472,101196963840],
  #[0,0,0,0,0,32768,1376256,33718272,629407744,9913171968,138784407552],
  #[0,0,0,0,0,0,262144,12845056,359661568,7552892928,132175626240],
  #[0,0,0,0,0,0,0,2097152,117440512,3699376128,86318776320],
  #[0,0,0,0,0,0,0,0,16777216,1056964608,36993761280],
  #[0,0,0,0,0,0,0,0,0,134217728,9395240960],
  #[0,0,0,0,0,0,0,0,0,0,1073741824]]
def mx10_16_0 : Table := #[
  #[1099511627776,0,0,0,0,0,0,0,0,0,0],
  #[10307921510400,68719476736,0,0,0,0,0,0,0,0,0],
  #[43486543872000,579820584960,4294967296,0,0,0,0,0,0,0,0],
  #[108716359680000,2174327193600,32212254720,268435456,0,0,0,0,0,0,0],
  #[178362777600000,4756340736000,105696460800,1761607680,16777216,0,0,0,0,0,0],
  #[200658124800000,6688604160000,198180864000,4954521600,94371840,1048576,0,0,0,0,0],
  #[156764160000000,6270566400000,232243200000,7741440000,221184000,4915200,65536,0,0,0,0],
  #[83980800000000,3919104000000,174182400000,7257600000,276480000,9216000,245760,4096,0,0,0],
  #[29524500000000,1574640000000,81648000000,4082400000,194400000,8640000,345600,11520,256,0,0],
  #[6150937500000,369056250000,21870000000,1275750000,72900000,4050000,216000,10800,480,16,0],
  #[576650390625,38443359375,2562890625,170859375,11390625,759375,50625,3375,225,15,1]]
def mx10_16_1 : Table := #[
  #[576650390625,38443359375,2562890625,170859375,11390625,759375,50625,3375,225,15,1],
  #[5382070312500,399810937500,29387812500,2141437500,154912500,11137500,796500,56700,4020,284,20],
  #[22604695312500,1851432187500,149308312500,11873587500,932512500,72427500,5570100,424620,32116,2412,180],
  #[56260575000000,5036661000000,443280600000,38377800000,3271320000,274824000,22779840,1865024,150976,12096,960],
  #[91892272500000,8926677900000,852938100000,80147340000,7406964000,673471200,60280096,5315296,462112,39648,3360],
  #[102919345200000,10782026640000,1112949936000,113117558400,11314316160,1113309824,107755392,10260096,961408,88704,8064],
  #[80048379600000,8995913136000,998577820800,109388791680,11814898816,1257146240,131679360,13569920,1375360,137088,13440],
  #[42692469120000,5123096294400,608988871680,71646761984,8334384128,957608960,108559360,12129280,1334272,144384,15360],
  #[14942364192000,1906930287360,241818578176,30449443584,3804105984,471089920,57765120,7004928,838912,99072,11520],
  #[3099157017600,419124091904,56501638144,7589772288,1015411712,135224320,17912832,2358272,308224,39936,5120],
  #[289254654976,41322093568,5903156224,843308032,120472576,17210368,2458624,351232,50176,7168,1024]]
def mx10_16_2 : Table := #[
  #[289254654976,41322093568,5903156224,843308032,120472576,17210368,2458624,351232,50176,7168,1024],
  #[2685936081920,407317779456,61561486336,9276388352,1394039808,208983040,31259648,4666368,695296,103424,15360],
  #[11223375770880,1800673475328,287357211904,45628988160,7211758848,1134918400,177886464,27777792,4322560,670464,103680],
  #[27791216194560,4703128894464,790902461440,132192836608,21965698048,3629480960,596513792,97541120,15873024,2571264,414720],
  #[45160726316160,8039601827712,1421918452864,249859815296,43624576128,7568785280,1305095296,223692672,38118528,6459264,1088640],
  #[50321952180864,9400804253568,1745391007360,322025698176,59036525184,10753755008,1946259072,349985664,62536320,11104128,1959552],
  #[38939605854240,7616758068192,1481846128672,286680800224,55140276256,10542236640,2003169312,378235872,70961184,13226976,2449440],
  #[20661831677760,4223187573696,859474977088,174116995520,35103771456,7041378240,1404876096,278728128,54976320,10777536,2099520],
  #[7194744959220,1533824749548,326002679860,69064953516,14580847476,3066792300,642452148,134004780,27821556,5747436,1180980],
  #[1484629912220,329555211284,73039273788,16160156532,3568868316,786569940,172974204,37945908,8301852,1810836,393660],
  #[137858491849,31813498119,7341576489,1694209959,390971529,90224199,20820969,4804839,1108809,255879,59049]]
def mx10_16_3 : Table := #[
  #[137858491849,31813498119,7341576489,1694209959,390971529,90224199,20820969,4804839,1108809,255879,59049],
  #[1272539924760,306714751096,73792255992,17724042648,4250562264,1017914040,243445176,58150872,13874328,3306744,787320],
  #[5285935072080,1328260607856,332779519696,83139928560,20716093008,5148889200,1276690896,315849456,77973840,19210608,4723920],
  #[13011532485120,3403016188416,886825904640,230301280768,59605418496,15376458240,3954203136,1013783040,259158528,66064896,16796160],
  #[21018629399040,5712755682816,1546801611264,417237929472,112127222272,30021987840,8009335296,2129186304,564060672,148925952,39191040],
  #[23282174103552,6566767054848,1845361889280,516648996864,144105541632,40043204608,11085041664,3057094656,839946240,229920768,62705664],
  #[17909364695040,5235045064704,1525220057088,442870751232,128149364736,36950138880,10615595008,3038601216,866525184,246177792,69672960],
  #[9446697861120,2858231660544,862479581184,259528458240,77867384832,23292149760,6945374208,2064252928,611450880,180486144,53084160],
  #[3270010798080,1022926454784,319380848640,99516874752,30942756864,9599385600,2970943488,917176320,282394624,86704128,26542080],
  #[670771445760,216710774784,69943689216,22550151168,7261913088,2335703040,750256128,240648192,77070336,24641536,7864320],
  #[61917364224,20639121408,6879707136,2293235712,764411904,254803968,84934656,28311552,9437184,3145728,1048576]]
def mx10_16_4 : Table := #[
  #[61917364224,20639121408,6879707136,2293235712,764411904,254803968,84934656,28311552,9437184,3145728,1048576],
  #[567575838720,196071653376,67650453504,23314563072,8026324992,2760376320,948436992,325582848,111673344,38273024,13107200],
  #[2341250334720,837174362112,298741727232,106396581888,37822464000,13421445120,4754571264,1681588224,593821696,209387520,73728000],
  #[5723056373760,2115796598784,780241600512,287026053120,105336668160,38568591360,14090108928,5136318464,1868431360,678297600,245760000],
  #[9180736266240,3505372028928,1334817792000,506932715520,192013148160,72540119040,27334352896,10274037760,3852083200,1440768000,537600000],
  #[10098809892864,3978319048704,1563095052288,612517441536,239382392832,93304500224,36270059520,14061465600,5436928000,2096640000,806400000],
  #[7714368668160,3132501216768,1268962877952,512802909696,206716043776,83118886400,33335616000,13334720000,5320000000,2116800000,840000000],
  #[4040859778560,1689814089216,705264231936,293753275904,122095930880,50638016000,20954560000,8651200000,3563200000,1464000000,600000000],
  #[1389045548880,597710508912,256833827536,110197536240,47208440400,20191270000,8621250000,3674550000,1563250000,663750000,281250000],
  #[282953722920,125185586504,55343565640,24447541800,10790417000,4758325000,2096325000,922625000,405625000,178125000,78125000],
  #[25937424601,11789738455,5358972025,2435896375,1107225625,503284375,228765625,103984375,47265625,21484375,9765625]]
def mx10_16_5 : Table := #[
  #[25937424601,11789738455,5358972025,2435896375,1107225625,503284375,228765625,103984375,47265625,21484375,9765625],
  #[235794769100,110609182596,51835874860,24270385700,11354095500,5307362500,2478987500,1157062500,539687500,251562500,117187500],
  #[964614964500,466522873740,225264610516,108603131340,52281546900,25132607500,12065212500,5784487500,2769812500,1324687500,632812500],
  #[2338460520000,1164978513600,579216700480,287421804736,142355667520,70376504000,34729640000,17108600000,8413800000,4131000000,2025000000],
  #[3720278100000,1907488044000,975922208800,498244836320,253836212256,129050002400,65473876000,33151020000,16751700000,8448300000,4252500000],
  #[4058485200000,2139928560000,1125940816000,591162633600,309720005760,161919752576,84469092480,43970774400,22840272000,11838960000,6123600000],
  #[3074610000000,1665879600000,900869200000,486214960000,261895504000,140781820800,75521517696,40428581760,21596803200,11512368000,6123600000],
  #[1597200000000,888624000000,493609600000,273737600000,151547520000,83753856000,46204093440,25442159616,13983114240,7670246400,4199040000],
  #[544500000000,310860000000,177268000000,100965600000,57434400000,32628960000,18511545600,10487335680,5932590336,3350833920,1889568000],
  #[110000000000,64400000000,37680000000,22032000000,12873600000,7516800000,4385664000,2556748800,1489259520,866681856,503884800],
  #[10000000000,6000000000,3600000000,2160000000,1296000000,777600000,466560000,279936000,167961600,100776960,60466176]]
def mx10_16_6 : Table := #[
  #[10000000000,6000000000,3600000000,2160000000,1296000000,777600000,466560000,279936000,167961600,100776960,60466176],
  #[90000000000,55600000000,34320000000,21168000000,13046400000,8035200000,4945536000,3041971200,1869972480,1148857344,705438720],
  #[364500000000,231660000000,147028000000,93189600000,58989600000,37294560000,23550393600,14854337280,9359006976,5890413312,3703553280],
  #[874800000000,571536000000,372758400000,242704000000,157764480000,102386304000,66342620160,42921944064,27728096256,17886790656,11522165760],
  #[1377810000000,924663600000,619390800000,414131760000,276383824000,184117756800,122432708736,81269709696,53851900032,35622695808,23524421760],
  #[1488034800000,1025090640000,704867184000,483775286400,331411962240,226609873024,154658915712,105355506816,71635390848,48617138304,32934190464],
  #[1116026100000,788658444000,556378048800,391836100320,275473594656,193323644640,135428073760,94698129120,66095880480,46046877408,32019351840],
  #[573956280000,415799438400,300800329920,217292341824,156734440128,112880900160,81169824960,58273230400,41766336192,29884728384,21346234560],
  #[193710244500,143776048140,106604938836,78960086604,58419695124,43173115020,31867656660,23493564108,17297697172,12718798092,9338977620],
  #[38742048900,29443957164,22365163044,16978477068,12881421252,9766835820,7400391012,5603386572,4239599364,3205229356,2421216420],
  #[3486784401,2711943423,2109289329,1640558367,1275989841,992436543,771895089,600362847,466948881,363182463,282475249]]
def mx10_16_7 : Table := #[
  #[3486784401,2711943423,2109289329,1640558367,1275989841,992436543,771895089,600362847,466948881,363182463,282475249],
  #[30993639120,24794911296,19820623536,15832690272,12638375568,10081895040,8037510768,6403870368,5099378256,4058419904,3228288560],
  #[123974556480,101934635328,83704083264,68648005440,56232283968,46008648000,37601734464,30697918272,25035707200,20397513024,16602626880],
  #[293865615360,248153186304,209212968960,176104378368,148006268928,124203663360,104075661312,87084462080,72765435904,60718178304,50598481920],
  #[457124290560,396174385152,342749159424,296012537856,255208071168,219653038080,188732809216,161895473152,138646724608,118545014784,101196963840],
  #[487599243264,433421549568,384594739200,340672905216,301238452224,265901047808,234296573952,206086078464,180954726400,158610751488,138784407552],
  #[361184624640,329079324672,299352195072,271871115264,246508158976,223139594240,201645883392,181911683072,163825844224,147281412096,132175626240],
  #[183458856960,171228266496,159601655808,148562247680,138093264896,128177930240,118799466496,109941096448,101586042880,93717528576,86318776320],
  #[61152952320,58435043328,55784243200,53200551936,50683969536,48234496000,45852131328,43536875520,41288728576,39107690496,36993761280],
  #[12079595520,11811160064,11542724608,11274289152,11005853696,10737418240,10468982784,10200547328,9932111872,9663676416,9395240960],
  #[1073741824,1073741824,1073741824,1073741824,1073741824,1073741824,1073741824,1073741824,1073741824,1073741824,1073741824]]
def mx10_16_9 : Table := #[
  #[282475249,363182463,466948881,600362847,771895089,992436543,1275989841,1640558367,2109289329,2711943423,3486784401],
  #[2421216420,3205229356,4239599364,5603386572,7400391012,9766835820,12881421252,16978477068,22365163044,29443957164,38742048900],
  #[9338977620,12718798092,17297697172,23493564108,31867656660,43173115020,58419695124,78960086604,106604938836,143776048140,193710244500],
  #[21346234560,29884728384,41766336192,58273230400,81169824960,112880900160,156734440128,217292341824,300800329920,415799438400,573956280000],
  #[32019351840,46046877408,66095880480,94698129120,135428073760,193323644640,275473594656,391836100320,556378048800,788658444000,1116026100000],
  #[32934190464,48617138304,71635390848,105355506816,154658915712,226609873024,331411962240,483775286400,704867184000,1025090640000,1488034800000],
  #[23524421760,35622695808,53851900032,81269709696,122432708736,184117756800,276383824000,414131760000,619390800000,924663600000,1377810000000],
  #[11522165760,17886790656,27728096256,42921944064,66342620160,102386304000,157764480000,242704000000,372758400000,571536000000,874800000000],
  #[3703553280,5890413312,9359006976,14854337280,23550393600,37294560000,58989600000,93189600000,147028000000,231660000000,364500000000],
  #[705438720,1148857344,1869972480,3041971200,4945536000,8035200000,13046400000,21168000000,34320000000,55600000000,90000000000],
  #[60466176,100776960,167961600,279936000,466560000,777600000,1296000000,2160000000,3600000000,6000000000,10000000000]]
def mx10_16_10 : Table := #[
  #[60466176,100776960,167961600,279936000,466560000,777600000,1296000000,2160000000,3600000000,6000000000,10000000000],
  #[503884800,866681856,1489259520,2556748800,4385664000,7516800000,12873600000,22032000000,37680000000,64400000000,110000000000],
  #[1889568000,3350833920,5932590336,10487335680,18511545600,32628960000,57434400000,100965600000,177268000000,310860000000,544500000000],
  #[4199040000,7670246400,13983114240,25442159616,46204093440,83753856000,151547520000,273737600000,493609600000,888624000000,1597200000000],
  #[6123600000,11512368000,21596803200,40428581760,75521517696,140781820800,261895504000,486214960000,900869200000,1665879600000,3074610000000],
  #[6123600000,11838960000,22840272000,43970774400,84469092480,161919752576,309720005760,591162633600,1125940816000,2139928560000,4058485200000],
  #[4252500000,8448300000,16751700000,33151020000,65473876000,129050002400,253836212256,498244836320,975922208800,1907488044000,3720278100000],
  #[2025000000,4131000000,8413800000,17108600000,34729640000,70376504000,142355667520,287421804736,579216700480,1164978513600,2338460520000],
  #[632812500,1324687500,2769812500,5784487500,12065212500,25132607500,52281546900,108603131340,225264610516,466522873740,964614964500],
  #[117187500,251562500,539687500,1157062500,2478987500,5307362500,11354095500,24270385700,51835874860,110609182596,235794769100],
  #[9765625,21484375,47265625,103984375,228765625,503284375,1107225625,2435896375,5358972025,11789738455,25937424601]]
def mx10_16_11 : Table := #[
  #[9765625,21484375,47265625,103984375,228765625,503284375,1107225625,2435896375,5358972025,11789738455,25937424601],
  #[78125000,178125000,405625000,922625000,2096325000,4758325000,10790417000,24447541800,55343565640,125185586504,282953722920],
  #[281250000,663750000,1563250000,3674550000,8621250000,20191270000,47208440400,110197536240,256833827536,597710508912,1389045548880],
  #[600000000,1464000000,3563200000,8651200000,20954560000,50638016000,122095930880,293753275904,705264231936,1689814089216,4040859778560],
  #[840000000,2116800000,5320000000,13334720000,33335616000,83118886400,206716043776,512802909696,1268962877952,3132501216768,7714368668160],
  #[806400000,2096640000,5436928000,14061465600,36270059520,93304500224,239382392832,612517441536,1563095052288,3978319048704,10098809892864],
  #[537600000,1440768000,3852083200,10274037760,27334352896,72540119040,192013148160,506932715520,1334817792000,3505372028928,9180736266240],
  #[245760000,678297600,1868431360,5136318464,14090108928,38568591360,105336668160,287026053120,780241600512,2115796598784,5723056373760],
  #[73728000,209387520,593821696,1681588224,4754571264,13421445120,37822464000,106396581888,298741727232,837174362112,2341250334720],
  #[13107200,38273024,111673344,325582848,948436992,2760376320,8026324992,23314563072,67650453504,196071653376,567575838720],
  #[1048576,3145728,9437184,28311552,84934656,254803968,764411904,2293235712,6879707136,20639121408,61917364224]]
def mx10_32_0 : Table := #[
  #[1125899906842624,0,0,0,0,0,0,0,0,0,0],
  #[10907155347537920,35184372088832,0,0,0,0,0,0,0,0,0],
  #[47548380343173120,306763744149504,1099511627776,0,0,0,0,0,0,0,0],
  #[122833315886530560,1188709508579328,8521215115264,34359738368,0,0,0,0,0,0,0],
  #[208240855838883840,2686978785017856,28892245000192,233001975808,1073741824,0,0,0,0,0,0],
  #[242079994912702464,3904516046979072,55978724687872,677161992192,6241124352,33554432,0,0,0,0,0],
  #[195429162559733760,3782499920510976,67786736926720,1093334466560,15115223040,162529280,1048576,0,0,0,0],
  #[108184000702709760,2442864531996672,52534721118208,1059167764480,19523829760,314900480,4063232,32768,0,0,0],
  #[39301219005281280,1014225006587904,25446505541632,615641263104,14185282560,305059840,5904384,95232,1024,0,0],
  #[8460679091414720,245632618783008,7043229212416,198800824544,5496796992,147763360,3813248,92256,1984,32,0],
  #[819628286980801,26439622160671,852891037441,27512614111,887503681,28629151,923521,29791,961,31,1]]
def mx10_32_1 : Table := #[
  #[819628286980801,26439622160671,852891037441,27512614111,887503681,28629151,923521,29791,961,31,1],
  #[7931886648201300,283159824430412,10014591536404,351451457676,12253276628,424819660,14657172,503564,17236,588,20],
  #[34542087016360500,1351969857414540,52188766457524,1989496961292,74993599284,2798566540,103499700,3797004,138292,5004,180],
  #[89140869719640000,3795675742900800,159159756903360,6575883257408,267905458112,10772118080,427879360,16805440,653248,25152,960],
  #[150964376138100000,6947607848076000,314973116992800,14065036550880,618698042656,26817594080,1145982240,48308960,2010400,82656,3360],
  #[175313469063600000,8671418899920000,423143260848000,20359303171200,965433386880,45106504832,2076200832,94157952,4208512,185472,8064],
  #[141381829890000000,7479554871600000,391228866000000,20217299760000,1031384016000,51905020800,2575225984,125899648,6063232,287616,13440],
  #[78183500400000000,4405177872000000,246045859200000,13612406400000,745338240000,40353408000,2158279680,113927168,5929984,304128,15360],
  #[28373044500000000,1696280940000000,100814868000000,5952722400000,348948000000,20291040000,1169337600,66712320,3763456,209664,11520],
  #[6101730000000000,385786800000000,24319440000000,1527984000000,95644800000,5961600000,369792000,22809600,1397760,84992,5120],
  #[590490000000000,39366000000000,2624400000000,174960000000,11664000000,777600000,51840000,3456000,230400,15360,1024]]
def mx10_32_2 : Table := #[
  #[590490000000000,39366000000000,2624400000000,174960000000,11664000000,777600000,51840000,3456000,230400,15360,1024],
  #[5708070000000000,401533200000000,28168560000000,1971216000000,137635200000,9590400000,667008000,46310400,3210240,222208,15360],
  #[24830104500000000,1837998540000000,135456948000000,9941810400000,726861600000,52950240000,3844281600,278219520,20075776,1444608,103680],
  #[64006491600000000,4973377968000000,384416668800000,29563056000000,2262418560000,172328832000,13067473920,986647552,74191872,5557248,414720],
  #[108277648290000000,8811560343600000,713172373200000,57408870960000,4596559056000,366094588800,29007297664,2286807936,179399808,14007168,1088640],
  #[125602072016400000,10683394631280000,903982382352000,76087487548800,6370045845120,530434192768,43931350656,3618905472,296521344,24167808,1959552],
  #[101179446902100000,8978222184876000,793037972512800,69716198438880,6098784333856,530837153760,45965590560,3959232480,339202080,28903392,2449440],
  #[55889599241160000,5164969860907200,475550169119040,43614816701632,3983782767936,362321369280,32805069120,2956305600,265114944,23654592,2099520],
  #[20259979724920500,1946821040233740,186586558624564,17833131341964,1699367083956,161425425420,15282265140,1441562508,135456948,12675852,1180980],
  #[4352143792760700,434213886450148,43262689782972,4304141550756,427534389756,42394423140,4195981116,414448164,40844412,4015332,393660],
  #[420707233300201,43521437927607,4502217716649,465746660343,48180689001,4984209207,515607849,53338743,5517801,570807,59049]]
def mx10_32_3 : Table := #[
  #[420707233300201,43521437927607,4502217716649,465746660343,48180689001,4984209207,515607849,53338743,5517801,570807,59049],
  #[4062000873243320,436214872101992,46781664550008,5010791656104,536079390264,57289761000,6116175864,652326696,69511608,7400808,787320],
  #[17648693449264080,1964829911100336,218257331527888,24192982290096,2676272088528,295483466160,32564017872,3582469296,393461712,43145136,4723920],
  #[45440314168220160,5237947544514048,602136448109056,69035695390208,7894599891456,900529344000,102473427456,11633352192,1317689856,148925952,16796160],
  #[76778461870440960,9152900380614144,1087954164580864,128945131560448,15238944113152,1795876216320,211051381248,24734965248,2891137536,337042944,39191040],
  #[88957114442993664,10955309660467200,1345338410192896,164736834662400,20113813622784,2448713216000,297248477184,35978342400,4342173696,522547200,62705664],
  #[71574689781719040,9096684711174144,1153166113447936,145800710709248,18384920322048,2311932600320,289920458752,36253851648,4520484864,562028544,69672960],
  #[39489484017500160,5174484112637952,676604827795456,88277897838592,11491681632256,1492434944000,193353875456,24987435008,3220832256,414056448,53084160],
  #[14297916627025920,1929866579214336,260089689997312,34996801437696,4701203791872,630419292160,84382384128,11272912896,1502937088,199950336,26542080],
  #[3067752226488320,426160654123008,59152998596608,8203700535296,1136710385664,157351936000,21759524864,3005743104,414711808,57147392,7864320],
  #[296196766695424,42313823813632,6044831973376,863547424768,123363917824,17623416832,2517630976,359661568,51380224,7340032,1048576]]
def mx10_32_4 : Table := #[
  #[296196766695424,42313823813632,6044831973376,863547424768,123363917824,17623416832,2517630976,359661568,51380224,7340032,1048576],
  #[2856183107420160,420115822149632,61743640870912,9067247960064,1330567970816,195116400640,28593094656,4187488256,612892672,89653248,13107200],
  #[12393794555412480,1875463091453952,283405470466048,42768728260608,6445922058240,970299473920,145884512256,21908619264,3286564864,492503040,73728000],
  #[31869757428203520,4957517822164992,769837108690944,119343575859200,18470644613120,2854075105280,440318427136,67827269632,10432675840,1602355200,245760000],
  #[53780215660093440,8593452449390592,1370564177633280,218184489492480,34669586882560,5498983669760,870632595456,137599508480,21709004800,3419136000,537600000],
  #[62231392406679552,10207265421201408,1671110397702144,273081473667072,44541767725056,7251515936768,1178353643520,191121100800,30940672000,4999680000,806400000],
  #[50007368898224640,8413938259066368,1413289264439808,236982473473536,39668197630464,6628239244800,1105535296000,184058560000,30587200000,5073600000,840000000],
  #[27555080821470720,4752886956507648,818658177910272,140805437501952,24181885048320,4146645312000,709940160000,121352000000,20708800000,3528000000,600000000],
  #[9964114047049680,1760854016780208,310860001645776,54820860127920,9657133275600,1699233390000,298634850000,52419150000,9189250000,1608750000,281250000],
  #[2135167295796360,386363605906008,69875159396040,12629907941400,2281476213000,411866775000,74303325000,13395375000,2413125000,434375000,78125000],
  #[205891132094649,38127987424935,7060738412025,1307544150375,242137805625,44840334375,8303765625,1537734375,284765625,52734375,9765625]]
def mx10_32_5 : Table := #[
  #[205891132094649,38127987424935,7060738412025,1307544150375,242137805625,44840334375,8303765625,1537734375,284765625,52734375,9765625],
  #[1982655346096620,376196142592692,71339608844460,13520975066100,2561279899500,484939912500,91771987500,17359312500,3282187500,620312500,117187500],
  #[8591506499752020,1669346846960364,324040046681556,62840464250220,12175366454100,2356891627500,455852812500,88094587500,17010812500,3282187500,632812500],
  #[22062140147511360,4387285989448128,871387770936384,172863965343168,34251966089280,6778994328000,1340153640000,264645400000,52204200000,10287000000,2025000000],
  #[37178791730065440,7562865326286816,1536368908288032,311692891412448,63151745585184,12778395256800,2582294356000,521170860000,105052500000,21149100000,4252500000],
  #[42962159332520064,8935149946649472,1855827780573312,384938413921152,79737186402432,16494745512832,3407572068480,703006819200,144840528000,29801520000,6123600000],
  #[34475806871775360,7327336731152256,1555409668176000,329763565272960,69825239386240,14766145630080,3118604720256,657788100480,138560284800,29148336000,6123600000],
  #[18970814363304960,4118450297674752,893171129730048,193498554096640,41874738447360,9052049710080,1954570355712,421555166208,90812482560,19539532800,4199040000],
  #[6850571853415680,1518445841013504,336314134004992,74430927477504,16459361568000,3636738743040,802857878784,177084340992,39023265024,8591235840,1889568000],
  #[1465965993323520,331617378546688,74984979803136,16948355134464,3829034806272,864671708160,195166153728,44029080576,9927650304,2237248512,503884800],
  #[141167095653376,32577022073856,7517774324736,1734870998016,400354845696,92389579776,21320672256,4920155136,1135420416,262020096,60466176]]
def mx10_32_6 : Table := #[
  #[141167095653376,32577022073856,7517774324736,1734870998016,400354845696,92389579776,21320672256,4920155136,1135420416,262020096,60466176],
  #[1357375919744000,319923062930432,75370506691584,17749064825856,4178062107648,983119887360,231247291392,54374022144,12780758016,3003153408,705438720],
  #[5873261191200000,1413197000467200,339783876001024,81637314700032,19600607280384,4702772355840,1127588117760,270188815104,64701234432,15484379904,3703553280],
  #[15059644080000000,3697721838720000,907081274444800,222309304275968,54434686405632,13317040788480,3255074933760,794955617280,193981713408,47295747072,11522165760],
  #[25340747250000000,6346882542000000,1588012163920000,396919588374400,99108288462976,24721789073280,6160505639040,1533641074560,381422805120,94769813376,23524421760],
  #[29239323750000000,7467273450000000,1905058246000000,485517112080000,123608945366400,31437190946432,7987039546752,2027105764992,513944307072,130168467072,32934190464],
  #[23428945312500000,6098734687500000,1586033312500000,412064607500000,106953222900000,27732776204000,7183884814624,1859036215008,480590383392,124113106656,32019351840],
  #[12873046875000000,3414328125000000,904856875000000,239606125000000,63394555000000,16758480200000,4426276702400,1168036482368,307950492864,81115691328,21346234560],
  #[4641723632812500,1253979492187500,338567382812500,91355742187500,24635132812500,6638872187500,1787910652500,481172645100,129404958676,34776573804,9338977620],
  #[991821289062500,272827148437500,75024414062500,20624023437500,5667539062500,1556898437500,427528062500,117354877500,32200531300,8831675132,2421216420],
  #[95367431640625,26702880859375,7476806640625,2093505859375,586181640625,164130859375,45956640625,12867859375,3603000625,1008840175,282475249]]
def mx10_32_7 : Table := #[
  #[95367431640625,26702880859375,7476806640625,2093505859375,586181640625,164130859375,45956640625,12867859375,3603000625,1008840175,282475249],
  #[915527343750000,261230468750000,74511718750000,21246093750000,6056093750000,1725718750000,491604750000,140002310000,39859481200,11345128368,3228288560],
  #[3955078125000000,1149609375000000,333953125000000,96954375000000,28132125000000,8158255000000,2364600840000,684999537600,198335507776,57397652928,16602626880],
  #[10125000000000000,2997000000000000,886440000000000,261992000000000,77376320000000,22835724800000,6734627737600,1984768479232,584532938752,172034838528,50598481920],
  #[17010000000000000,5125680000000000,1543248000000000,464257920000000,139548390400000,41911675904000,12577458561024,3771391533056,1129963921408,338286993408,101196963840],
  #[19595520000000000,6009292800000000,1841301504000000,563716177920000,172436609433600,52702526701568,16094083547136,4910594260992,1497046319104,456005910528,138784407552],
  #[15676416000000000,4891041792000000,1524815953920000,474997417574400,147849308798976,45983095848960,14289755176960,4437067694080,1376604651520,426738450432,132175626240],
  #[8599633920000000,2728950497280000,865416196915200,274260119519232,86856670642176,27487874580480,8693030584320,2747185233920,867533062144,273753833472,86318776320],
  #[3095868211200000,998933476147200,322165983412224,103849943629824,33458818646016,10774244229120,3467598888960,1115399651328,358579437568,115209142272,36993761280],
  #[660451885056000,216628218298368,71035269414912,23287044243456,7631888449536,2500476272640,818996576256,268167020544,87778394112,28722593792,9395240960],
  #[63403380965376,21134460321792,7044820107264,2348273369088,782757789696,260919263232,86973087744,28991029248,9663676416,3221225472,1073741824]]
def mx10_32_8 : Table := #[
  #[63403380965376,21134460321792,7044820107264,2348273369088,782757789696,260919263232,86973087744,28991029248,9663676416,3221225472,1073741824],
  #[607615734251520,206060988137472,69861132730368,23678423138304,8023267344384,2717908992000,920465178624,311653564416,105495134208,35701915648,12079595520],
  #[2620342853959680,903828404699136,311598753251328,107372353683456,36981228699648,12731138703360,4380816310272,1506778546176,518030098432,178023038976,61152952320],
  #[6696431737896960,2348603595030528,823188044906496,288347041824768,100939969069056,35313942528000,12347208892416,4314546307072,1506778546176,525915389952,183458856960],
  #[11230474060431360,4003908143284224,1426473852862464,507854219378688,180680743452672,64236874629120,22822278135808,8102855835648,2874910703616,1019343273984,361184624640],
  #[12915045169496064,4679364191846400,1694216175353856,612972793036800,221617217470464,80067346432000,28906593583104,10428648652800,3759664398336,1354442342400,487599243264],
  #[10314098572861440,3796784112328704,1396732441337856,513476286210048,188640392716288,69255380459520,25408229548032,9315260817408,3412818468864,1249473060864,457124290560],
  #[5648196837519360,2111934469681152,789236942401536,294772205350912,110030632759296,41047285248000,15303642771456,5702175387648,2123330236416,790171987968,293865615360],
  #[2029820738483520,770743526786496,292537865257792,110986445025216,42089035620672,15954184128960,6044802355008,2289215411136,866529430848,327843827136,123974556480],
  #[432276638751120,166645776677968,64228627232208,24749232066576,9534335103504,3672073602000,1413907992144,544272111504,209455778448,80583461712,30993639120],
  #[41426511213649,16210373953167,6343189807761,2482117750863,971263467729,380059617807,148718980881,58194383823,22771715409,8910671247,3486784401]]
def mx10_32_9 : Table := #[
  #[41426511213649,16210373953167,6343189807761,2482117750863,971263467729,380059617807,148718980881,58194383823,22771715409,8910671247,3486784401],
  #[396253585521860,157561702385372,62635168923012,24893122950684,9890934251076,3929118754140,1560471625476,619615564956,245978529732,97629963228,38742048900],
  #[1705613259420180,688986858153132,278196740475028,112281462982188,45298427948820,18267590498220,7363875054996,2967306492204,1195234192404,481262340780,193710244500],
  #[4350549763158720,1784929112315712,731908795735744,299954538294080,122862611286720,50298295222080,20580665685696,8416695604032,3440355353280,1405555156800,573956280000],
  #[7282441994852640,3033871091926752,1263136410622240,525578948282080,218555585616160,90828864718560,37724699547936,15659202152160,6496172071200,2693342988000,1116026100000],
  #[8358976898439552,3535219478786688,1494203704115584,631150460045952,266431336507776,112400124387968,47388972896640,19967187139200,8407866096000,3538216080000,1488034800000],
  #[6662952600205440,2860065819692928,1226969811937408,526063270764416,225416723224704,96533092937600,41314855504000,17671535280000,7554027600000,3227137200000,1377810000000],
  #[3641862290795520,1586297329824768,690608621857792,300512337359872,130698949258240,56814336128000,24684049280000,10718748800000,4651977600000,2017872000000,874800000000],
  #[1306320169524480,577259268588288,254996392811776,112599231824640,49701720710400,21929981920000,9672352800000,4264312800000,1879252000000,827820000000,364500000000],
  #[277671920092160,124458481179648,55773842375680,24988930841600,11193688704000,5013078400000,2244598400000,1004784000000,449680000000,201200000000,90000000000],
  #[26559922791424,12072692177920,5487587353600,2494357888000,1133799040000,515363200000,234256000000,106480000000,48400000000,22000000000,10000000000]]
def mx10_32_10 : Table := #[
  #[26559922791424,12072692177920,5487587353600,2494357888000,1133799040000,515363200000,234256000000,106480000000,48400000000,22000000000,10000000000],
  #[253526535736320,116995362378752,53977904696320,24898226918400,11482292096000,5294185600000,2440521600000,1124816000000,518320000000,238800000000,110000000000],
  #[1089011710321920,510091199380224,238832953697536,111782896515840,52299151238400,24459946720000,11435661600000,5344600800000,2497012000000,1166220000000,544500000000],
  #[2772029808092160,1317614168521728,625984220488704,297252903123968,141084487132160,66930756992000,31737185920000,15042160000000,7126134400000,3374448000000,1597200000000],
  #[4630549793063040,2233087649122176,1076316532486272,518485490210688,249630118486144,120122029385600,57771714384000,27770037680000,13341605200000,6406369200000,3074610000000],
  #[5304084308417664,2594638644377472,1268531972813952,619845740502912,302707514051712,147747446671232,72073217631360,35138647420800,17121962704000,8338342320000,4058485200000],
  #[4219157972604960,2093140708487136,1037875488360480,514356637908960,254773260433440,126128130854880,62407529621536,30862231560160,15253919111200,7535254188000,3720278100000],
  #[2301358894148160,1157653261904832,582077052583488,292541431896000,146959039402560,73791159583680,37034677872192,18578306445248,9315241376320,4668417547200,2338460520000],
  #[823781876882580,420093095657004,214159033330452,109139447359404,55600472590740,28315445821740,14414953560084,7335752583852,3731764901524,1897660711980,964614964500],
  #[174741610247820,90320988154068,46677010628556,24117776289684,12459170883852,6435115685460,3323047096908,1715643448596,885574998924,457013134292,235794769100],
  #[16679880978201,8737080512391,4576565982681,2397248848071,1255701777561,657748550151,344534954841,180470690631,94532266521,49516901511,25937424601]]
def mx10_32_11 : Table := #[
  #[16679880978201,8737080512391,4576565982681,2397248848071,1255701777561,657748550151,344534954841,180470690631,94532266521,49516901511,25937424601],
  #[158856009316200,84420622093752,44854309025064,23827200671736,12654864667368,6719855317560,3567651999912,1893770364024,1005070331496,533324895928,282953722920],
  #[680811468498000,366989801114160,197754718899024,106524266797872,57361716642384,30878102510640,16616397687120,8938894822704,4807222894672,2584466566704,1389045548880],
  #[1729044999360000,945211266316800,516481293565440,282088834288128,154001621233152,84037923002880,45839353781760,24992941304320,13621173063168,7420487956992,4040859778560],
  #[2881741665600000,1597308237504000,884919044620800,490005158469120,271194777616896,150019216596480,82946637283840,45839353781760,25320225047040,13979371101696,7714368668160],
  #[3293419046400000,1850587845120000,1039323059712000,583403762995200,327314654392320,183543533228032,102870319951872,57626004344832,32264466296832,18055447990272,10098809892864],
  #[2613824640000000,1488635366400000,847408665600000,482156989440000,274203759616000,155864121139200,88553396772864,50286243667968,28541495549952,16191480324096,9180736266240],
  #[1422489600000000,820979712000000,473629900800000,273128243200000,157439016960000,90713899008000,52245447966720,30076943597568,17307209170944,9954649571328,5723056373760],
  #[508032000000000,297077760000000,173667328000000,101492121600000,59293900800000,34629672960000,20218296729600,11800369889280,6884914692096,4015599058944,2341250334720],
  #[107520000000000,63692800000000,37724160000000,22339584000000,13226803200000,7829913600000,4634247168000,2742327705600,1622464266240,959719145472,567575838720],
  #[10240000000000,6144000000000,3686400000000,2211840000000,1327104000000,796262400000,477757440000,286654464000,171992678400,103195607040,61917364224]]
def mx10_32_13 : Table := #[
  #[6131066257801,4194940071127,2870222153929,1963836210583,1343677407241,919358226007,629034575689,430392078103,294478790281,201485488087,137858491849],
  #[58083785600220,40285011533252,27935279587228,19368036473604,13425894093404,9305245202500,6448241075484,4467713717636,3095007852508,2143740334788,1484629912220],
  #[247620349137780,174058280505036,122311198708468,85921833731916,60340539761268,42362901082060,29732779344372,20862245242956,14634054676852,10262394458316,7194744959220],
  #[625567197821760,445579442659008,317249847625536,225790094414528,160634062312256,114235691960000,81208135917376,57707592809152,40992481880896,29108206825152,20661831677760],
  #[1037124564809760,748427902324704,539851456325664,389228689448928,280506377000992,202064069373920,145494007515168,104715754209248,75334022641696,54173121990624,38939605854240],
  #[1179046873678464,861876369648000,629739853900416,459916951536000,335737222959744,244974733040000,178667177130624,130247675376000,94906733224576,69123560688000,50321952180864],
  #[930826479219840,689138200404864,509986758427776,377246351922048,278935257011328,206154435150720,152297091114112,112460237239168,83006807438464,61239929971584,45160726316160],
  #[503906063938560,377782206999552,283123254998016,212104347282432,158840569230336,118907429760000,88979528365056,66558361791488,49767341618176,37197473983488,27791216194560],
  #[179019259557120,135887133862656,103119213065472,78231425723136,59333639484672,44987976149760,34100852421888,25840735070976,19575498519808,14824722721536,11223375770880],
  #[37688265169920,28960456393728,22250524843008,17092639097856,13128355666944,10081895040000,7741103053824,5942791701504,4561453145088,3500571640832,2685936081920],
  #[3570467226624,2777030065152,2159912272896,1679931767808,1306613597184,1016255020032,790420571136,614771555328,478155654144,371898842112,289254654976]]
def mx10_32_16 : Table := #[
  #[1099511627776,1099511627776,1099511627776,1099511627776,1099511627776,1099511627776,1099511627776,1099511627776,1099511627776,1099511627776,1099511627776],
  #[10307921510400,10445360463872,10582799417344,10720238370816,10857677324288,10995116277760,11132555231232,11269994184704,11407433138176,11544872091648,11682311045120],
  #[43486543872000,44646185041920,45823006081024,47017006989312,48228187766784,49456548413440,50702088929280,51964809314304,53244709568512,54541789691904,55856049684480],
  #[108716359680000,113065014067200,117542517473280,122151017381888,126892661276672,131769596641280,136783970959360,141937931714560,147233626390528,152673202470912,158258807439360],
  #[178362777600000,187875459072000,197810926387200,208183272407040,219006858428416,230296314183680,242066537840640,254332696002560,267110223708160,280414824431616,294262470082560],
  #[200658124800000,214035333120000,228205264896000,243207556300800,259083353456640,275875345989632,293627800584192,312386594537472,332199249313792,353114964099072,375184649355264],
  #[156764160000000,169305292800000,182775398400000,197236408320000,212753793024000,229396719206400,247238211272704,266355317014528,286829277478912,308745701031936,332194741616640],
  #[83980800000000,91819008000000,100353945600000,109643673600000,119750676480000,130742157312000,142690348400640,155672838176768,169772914868224,185079927472128,201689664552960],
  #[29524500000000,32673780000000,36149652000000,39984775200000,44214919200000,48879240480000,54020580998400,59685790383360,65926073257216,72797363299584,80360725720320],
  #[6150937500000,6889050000000,7714642500000,8637921000000,9670257900000,10824321600000,12114219924000,13555658750400,15166117354080,16965042096512,18974060239520],
  #[576650390625,653537109375,740675390625,839432109375,951356390625,1078203909375,1221964430625,1384893021375,1569545424225,1778818147455,2015993900449]]
def mx10_32_17 : Table := #[
  #[576650390625,653537109375,740675390625,839432109375,951356390625,1078203909375,1221964430625,1384893021375,1569545424225,1778818147455,2015993900449],
  #[5382070312500,6181692187500,7098865312500,8150721187500,9356869912500,10739756587500,12325068688500,14142201677100,16224791130420,18611320852588,21345817769460],
  #[22604695312500,26307559687500,30607657312500,35599976887500,41394427312500,48118155367500,55918219878900,64964676723660,75454137244276,87613872104268,101706543489780],
  #[56260575000000,66333897000000,78180341400000,92106930600000,108473028120000,127699132968000,150277131917760,176782248419392,207886965515712,244377244980288,287171416912320],
  #[91892272500000,109745628300000,131010736500000,156328775820000,186459436404000,222302470898400,264923103456544,315581977027296,375770437586208,447252092568288,532111743102240],
  #[102919345200000,124483398480000,150499251504000,181871844739200,219687147711360,265247784919168,320115558093696,386162178095232,465629765860224,561202973347968,676094920647552],
  #[80048379600000,98040205872000,120026343427200,146881902599040,179671032102016,219687147711360,268501588421760,328022437034880,400565594217600,488940617354112,596554341747840],
  #[42692469120000,52938661708800,65620809784320,81312087442432,100719018925056,124712122106880,154363499781120,190992931292160,236224358636544,292055076652032,360940442065920],
  #[14942364192000,18756224766720,23537359654144,29529364402944,37036700257536,46439769035520,58213684972800,72951640167168,91393975012608,114464330502912,143314587290880],
  #[3099157017600,3937405201408,5001659937792,6352639405056,8067308368896,10243205360640,13003916276736,16505996258304,20947720614912,26580144909312,33721079362560],
  #[289254654976,371898842112,478155654144,614771555328,790420571136,1016255020032,1306613597184,1679931767808,2159912272896,2777030065152,3570467226624]]
def mx10_64_0 : Table := #[
  #[1152921504606846976,0,0,0,0,0,0,0,0,0,0],
  #[11349071060973649920,18014398509481984,0,0,0,0,0,0,0,0,0],
  #[50272838215406714880,159596311794941952,281474976710656,0,0,0,0,0,0,0,0],
  #[131966200315442626560,628410477692583936,2216615441596416,4398046511104,0,0,0,0,0,0,0],
  #[227332399762149212160,1443380315950153728,7636932888625152,30305289240576,68719476736,0,0,0,0,0,0],
  #[268536397219038756864,2131241247770148864,15035211624480768,89495307288576,405874409472,1073741824,0,0,0,0,0],
  #[220283763343742730240,2097940603273740288,18500358053560320,146828238520320,998831554560,5284823040,16777216,0,0,0,0],
  #[123909616880855285760,1376773520898392064,14569031967178752,144534047293440,1310966415360,10404495360,66060288,262144,0,0,0],
  #[45740073418909470720,580826329129009152,7170695421345792,85365421682688,967861923840,10241925120,97542144,774144,4096,0,0],
  #[10005641060386446720,142937729434092096,2016758087253504,28010528989632,381095632512,5040947520,64012032,762048,8064,64,0],
  #[984930291881790849,15633814156853823,248155780267521,3938980639167,62523502209,992436543,15752961,250047,3969,63,1]]
def mx10_64_1 : Table := #[
  #[984930291881790849,15633814156853823,248155780267521,3938980639167,62523502209,992436543,15752961,250047,3969,63,1],
  #[9692964777249370260,169738553702984364,2946357518096916,50769083793708,869374411668,14807783340,251047188,4238892,71316,1196,20],
  #[42925986870675782580,822033747549039564,15537090298936500,290192414919372,5362370936244,98143447500,1780858548,32065740,573364,10188,180],
  #[112652325332567133120,2341876297236162624,47978479266669504,969217938722880,19319615404992,380308944960,7399723968,142434368,2714560,51264,960],
  #[194012338072754507040,4351121560464233184,96193784768302368,2096178271441632,45028539583776,953787552480,19930516768,411095776,8375584,168672,3360],
  #[229119332581157703552,5513880507585464448,130985856712368000,3070005927295104,70961793904512,1617207060608,36334763904,804886656,17584000,379008,8064],
  #[187902098148568487040,4829843997469604736,122801299944027264,3086232474229632,76612906456192,1877296135040,45380236416,1081695104,25416832,588672,13440],
  #[105668300092619013120,2889240770581595136,78337272523668480,2104658079515648,55986076630016,1473325859840,38322912256,984417280,24951808,623616,15360],
  #[38996634557990350080,1130163602653483776,32567210275384576,932586577662720,26520095010048,748349920000,20936207616,580129536,15904000,430848,11520],
  #[8528364524146037760,261134766279535616,7972935468454912,242650606414848,7358378906624,222236093440,6680810496,199764992,5936128,175104,5120],
  #[839299365868340224,27074173092527104,873360422339584,28172916849664,908803769344,29316250624,945685504,30505984,984064,31744,1024]]
def mx10_64_2 : Table := #[
  #[839299365868340224,27074173092527104,873360422339584,28172916849664,908803769344,29316250624,945685504,30505984,984064,31744,1024],
  #[8257622793220766720,280348695571006464,9494272978336768,320807730578432,10817696480256,364088919040,12232899584,410354688,13745152,459776,15360],
  #[36559958979662910720,1303088966276721408,46259247864321280,1636000695134976,57653953172736,2025025350400,70905009408,2475436800,86185216,2992896,103680],
  #[95920752591803765760,3581176696447036416,133061389870978048,4921040015027200,181180499547136,6641876003840,242477782016,8817241088,319411200,11529216,414720],
  #[165153876438307290240,6445455357560591232,250285419715042432,9670509163328384,371808514505856,14225872442240,541713357952,20532392832,774716544,29102976,1088640],
  #[194988125085227316864,7939759720551297408,321749595341399680,12975070820401536,520666931385984,20790019150208,826018399872,32656466304,1284716160,50295168,1959552],
  #[159869296104823472160,6780284266317737952,286340683523612704,12039529564950496,503928851234848,20994634330080,870519414816,35920154592,1474871328,60256224,2449440],
  #[89880433754785546560,3964055089978378944,174228730386606400,7630132385194688,332890218385728,14466037037760,626036980032,26975851200,1157177664,49408704,2099520],
  #[33161531002269667380,1518661335164755788,69379603010994484,3161408414273100,143659849396788,6509066042700,293999797044,13235219532,593712180,26532684,1180980],
  #[7250370577557167420,344306334143116676,16329691775965116,773423859907332,36577776603708,1727130206340,81410821308,3830203908,179832636,8424324,393660],
  #[713342911662882601,35082438278502423,1725365816975529,84854056572567,4173150323241,205236901143,10093618089,496407447,24413481,1200663,59049]]
def mx10_64_3 : Table := #[
  #[713342911662882601,35082438278502423,1725365816975529,84854056572567,4173150323241,205236901143,10093618089,496407447,24413481,1200663,59049],
  #[7016487655700484600,357342431426931784,18177624563545464,923657271544008,46885229861112,2377607816520,120461540472,6097945032,308436984,15588936,787320],
  #[31056584705559522000,1635986210719091760,86010998099217616,4513509119003184,236426928713424,12363364534320,645456269520,33644889648,1751151312,91014192,4723920],
  #[81459894309664320000,4433554903411238400,240720486346836480,13039260726183424,704691851340288,37999695029760,2044674869760,109789447680,5883259392,314648064,16796160],
  #[140217850860897600000,7876718616666816000,441330266931724800,24664214796910080,1374888134672896,76450001763840,4240463823360,234634821120,12951912960,713276928,39191040],
  #[165503037081715200000,9586514716208640000,553878731137536000,31919743824998400,1834800042332160,105195943604224,6015737843712,343130812416,19521589248,1107800064,62705664],
  #[135658227116160000000,8095015519718400000,481940681241600000,28625448176640000,1696185529344000,100262297395200,5911908130816,347718475776,20399726592,1193730048,69672960],
  #[76248183859200000000,4683221784576000000,287103058329600000,17566311628800000,1072616325120000,65358249984000,3973925437440,241086889984,14592638976,881197056,53084160],
  #[28124330112000000000,1776597027840000000,112073683968000000,7059911270400000,444065587200000,27887984640000,1748547993600,109444792320,6838091776,426442752,26542080],
  #[6147394560000000000,399076761600000000,25888481280000000,1678123008000000,108689817600000,7033651200000,454754304000,29373235200,1895301120,122159104,7864320],
  #[604661760000000000,40310784000000000,2687385600000000,179159040000000,11943936000000,796262400000,53084160000,3538944000,235929600,15728640,1048576]]
def mx10_64_4 : Table := #[
  #[604661760000000000,40310784000000000,2687385600000000,179159040000000,11943936000000,796262400000,53084160000,3538944000,235929600,15728640,1048576],
  #[5945840640000000000,407138918400000000,27859230720000000,1905057792000000,130188902400000,8891596800000,606928896000,41405644800,2823290880,192413696,13107200],
  #[26310344832000000000,1849156439040000000,129810428928000000,9102324326400000,637557350400000,44609495040000,3118119321600,217736478720,15189999616,1058734080,73728000],
  #[68991570892800000000,4973629630464000000,358024756838400000,25735233945600000,1847277895680000,132415635456000,9479016284160,677670158336,48385884160,3450470400,245760000],
  #[118722994911360000000,8773428098534400000,647306664883200000,47682860682240000,3506970276864000,257529134899200,18882212601856,1382356541440,101050163200,7375872000,537600000],
  #[140093133995404800000,10605920878748160000,801662179659264000,60498221046681600,4558265687715840,342894919602176,25752913489920,1931061350400,144567808000,10805760000,806400000],
  #[114798540357345600000,8898508326004416000,688759484964364800,53232563273326080,4108061379191296,316546228313600,24353960256000,1870796480000,143483200000,10987200000,840000000],
  #[64505846486508480000,5116734941641689600,405377863061521920,32076460732361216,2534883965396480,200060254784000,15768141760000,1241089600000,97547200000,7656000000,600000000],
  #[23786530891900002000,1929799907388045360,156426340285513936,12668058220672560,1024939709768400,82843727230000,6689263650000,539557950000,43473250000,3498750000,281250000],
  #[5197797491192963400,431094164806286456,35737035322000840,2961073461598200,245219034557000,20296579675000,1678973325000,138804875000,11468125000,946875000,78125000],
  #[511116753300641401,43314979093274695,3670760940108025,311081435602375,26362833525625,2234138434375,189333765625,16045234375,1359765625,115234375,9765625]]
def mx10_64_5 : Table := #[
  #[511116753300641401,43314979093274695,3670760940108025,311081435602375,26362833525625,2234138434375,189333765625,16045234375,1359765625,115234375,9765625],
  #[5024537574819864620,435205417059207444,37678183480159660,3260555250449300,282037635955500,24386189012500,2107701987500,182099812500,15727187500,1357812500,117187500],
  #[22227191644542112980,1966801177664334252,173896673708943316,15363394320332460,1356307122354900,119650211267500,10547821612500,929212387500,81804812500,7197187500,632812500],
  #[58267892220720567360,5264883774005493696,475240997642284096,42856070506538944,3860930599289920,347504804696000,31248332840000,2807360600000,251989800000,22599000000,2025000000],
  #[100240526447510806560,9244859774060318688,851688536459018272,78376891165585376,7204862781497376,661603708997600,60688882516000,5561143980000,509058900000,46550700000,4252500000],
  #[118249841368589019264,11126957603940872064,1045864602532935808,98196517691776896,9209523629246592,862775927345024,80738079742080,7547073609600,704691792000,65726640000,6123600000],
  #[96871338974267840640,9296478000920385408,891254045446387840,85356946039093120,8166296031352960,780468104173440,74511651862656,7106041837440,676958083200,64420272000,6123600000],
  #[54416829641719464960,5324007762725796864,520443596326454272,50831176000732160,4960209939317760,483587726146560,47102905893888,4583627357184,445607101440,43278105600,4199040000],
  #[20060441435718616320,2000181945607011072,199308944363652352,19847425283635968,1975118744782080,196419749886720,19519602787584,1938390891264,192347571456,19072039680,1889568000],
  #[4382318656390507520,445147272051823616,45201851878124544,4588343374943232,465582735240192,47225095787520,4788254518272,485291824128,49163480064,4978381824,503884800],
  #[430804206899405824,44565952437869568,4610270941848576,476924580191232,49337025537024,5103830227968,527982437376,54618872832,5650228224,584506368,60466176]]
def mx10_64_6 : Table := #[
  #[430804206899405824,44565952437869568,4610270941848576,476924580191232,49337025537024,5103830227968,527982437376,54618872832,5650228224,584506368,60466176],
  #[4233765481597608960,446171776705567744,47003566958846976,4950148228881408,521157775500288,54851508771840,5771394229248,607085632512,63841084416,6711745536,705438720],
  #[18723462862582529280,2009402487490708224,215524380090154240,23103668969079552,2475294107122944,265057466745600,28367860186368,3034535166720,324446010624,34672313088,3703553280],
  #[49068385432974904320,5361010531878564864,585292947216681984,63853779529200640,6961320618150912,758391497487360,82565227957248,8982722147328,976632007680,106113659904,11522165760],
  #[84389162878262874240,9383380603160747904,1042511368116613248,115731955276758912,12837464019488896,1422857122193280,157580434862208,17438345559936,1928294895744,213064048512,23524421760],
  #[99521012773675527552,11258577972581563008,1272620415085649280,143734148561291904,16220571193003392,1829014126369408,206068962524544,23198122797696,2609385287040,293271124608,32934190464],
  #[81504277702579095840,9378169158518175456,1078270639643068704,123881384059729632,14221634246314272,1631379286652640,186990409320736,21416072312544,2450833312032,280245565152,32019351840],
  #[45770875163024713920,5355164704494240576,626150790981685440,73164833310120768,8543543728257216,996966944043840,116258678268096,13547738155840,1577610971328,183577617216,21346234560],
  #[16868145803614711380,2006217462184302636,238497631355334996,28338721143567660,3365589095199828,399503876870700,47397365659476,5620239085356,666065107540,78892125228,9338977620],
  #[3683847934122753060,445270911819555996,53806598602644132,6500274239997468,785070948596004,94790144419740,11441692448676,1380656662812,166550042148,20084566684,2421216420],
  #[362033331456891249,44460233687688399,5460028698488049,670529840165199,82345769844849,10112638401999,1241902961649,152514398799,18729838449,2300155599,282475249]]
def mx10_64_7 : Table := #[
  #[362033331456891249,44460233687688399,5460028698488049,670529840165199,82345769844849,10112638401999,1241902961649,152514398799,18729838449,2300155599,282475249],
  #[3556818695015071920,443933761934211984,55393975367116848,6910322563306512,861844448300976,107462623620240,13396366784304,1669631313168,208046726832,25918545296,3228288560],
  #[15724882651645581120,1994183113216206528,252784022235589440,32029156053349056,4056550592544576,513556189675200,64989434680128,8221010938560,1039535269696,131397932736,16602626880],
  #[41197353379749826560,5307127728619401216,683288662471446528,87923860985917440,11307604248170496,1453447155363840,186722302857216,23975350611968,3076869591040,394668158976,50598481920],
  #[70830537389745315840,9266551508132093952,1211556443639980032,158306459474386944,20672109935271936,2697764260208640,351850493059072,45861618245632,5974200623104,777770950656,101196963840],
  #[83505475659489214464,11092206039982276608,1472468307036733440,195343297680900096,25898536898002944,3431435775377408,454360296456192,60124129787904,7950993326080,1050796228608,138784407552],
  #[68367056095488245760,9218415082549542912,1242251380765753344,167303183360065536,22518431555780608,3029068643041280,407206843908096,54708403699712,7345548034048,985652527104,132175626240],
  #[38381505176414453760,5252205971509346304,718362897159290880,98203036106620928,13417799166722048,1832354431631360,250095559770112,34116720394240,4651466358784,633826443264,86318776320],
  #[14140554538679009280,1963375241711321088,272507933739188224,37808573534699520,5243641232621568,726947961241600,100738944466944,13954399076352,1932148080640,267412045824,36993761280],
  #[3087216585442590720,434841032836775936,61235874985148416,8621657488883712,1213618976718848,170796085411840,24031147327488,3380407697408,475399192576,66840428544,9395240960],
  #[303305489096114176,43329355585159168,6189907940737024,884272562962432,126324651851776,18046378835968,2578054119424,368293445632,52613349376,7516192768,1073741824]]
def mx10_64_8 : Table := #[
  #[303305489096114176,43329355585159168,6189907940737024,884272562962432,126324651851776,18046378835968,2578054119424,368293445632,52613349376,7516192768,1073741824],
  #[2978893196479692800,431746078866407424,62562283829592064,9063793770364928,1312874060316672,190131491307520,27529935060992,3985461215232,576867794944,83483426816,12079595520],
  #[13165644038012928000,1935520655978004480,284445613339181056,41787800068030464,6136936985001984,900966614302720,132228034068480,19399880736768,2845365501952,417199030272,61152952320],
  #[34481448670986240000,5140870529128857600,766109667913891840,114117122493251584,16990993685413888,2528700331458560,376174291189760,55936664207360,8314234601472,1235289636864,183458856960],
  #[59264989903257600000,8959019252908032000,1353642090181427200,204422892777635840,30855939142189056,4655141751357440,701961624616960,105799019397120,15938200535040,2399871172608,361184624640],
  #[69848023814553600000,10703982870282240000,1639512879972352000,250993263368601600,38404919448698880,5873393063297024,897777337761792,137159415300096,20944026206208,3196483928064,487599243264],
  #[57167281395840000000,8879489422003200000,1378545585894400000,213916984314880000,33178654913536000,5143515997593600,796980570955776,123429870821376,19106290409472,2956070412288,457124290560],
  #[32083678334400000000,5050054304064000000,794568428684800000,124964706521600000,19645437335040000,3087107375616000,484903063941120,76132263481344,11947874512896,1874209591296,293865615360],
  #[11816533315125000000,1884506871555000000,300451430917000000,47886936550200000,7629978529800000,1215318903480000,193515162350400,30803113978560,4901467588416,779662210752,123974556480],
  #[2579005287031250000,416660074943750000,67303816841250000,10869855405750000,1755222376050000,283375822950000,45741835458000,7382140642800,1191150599760,192160562544,30993639120],
  #[253295162119140625,41448299255859375,6782448969140625,1109855285859375,181612683140625,29718439059375,4863017300625,795766467375,130216331025,21308126895,3486784401]]
def mx10_64_9 : Table := #[
  #[253295162119140625,41448299255859375,6782448969140625,1109855285859375,181612683140625,29718439059375,4863017300625,795766467375,130216331025,21308126895,3486784401],
  #[2486897955351562500,412305910173437500,68345162541562500,11327250311437500,1877031286762500,310992958237500,51518510554500,8533188704700,1413176020740,234001975356,38742048900],
  #[10987567330007812500,1845319388622187500,309823542219812500,52003490701387500,8726258726212500,1463873121067500,245505238218900,41162546535660,6899696377236,1156234926060,193710244500],
  #[28767449009475000000,4893372134541000000,832055851222200000,141428174278600000,24030372805560000,4081578072264000,693011836313280,117625116292416,19957598320320,3385066593600,573956280000],
  #[49427707843552500000,8514213916754700000,1466011466003700000,252318914458380000,43409306207476000,7465132145829600,1283260561348896,220503766099680,37874086336800,6502712076000,1116026100000],
  #[58234826695676400000,10156781221670160000,1770700927243248000,308567302263158400,53748951449973120,9358481622722176,1628756104544640,283349221545600,49272363504000,8564466960000,1488034800000],
  #[47646676387371600000,8412766699507632000,1484815680747907200,261958474126419840,46197380208560256,8143780522723200,1435018387024000,252761246640000,44502469200000,7832084400000,1377810000000],
  #[26731641817330560000,4777493426477798400,853546564963445760,152442150714971136,27216464844303360,4857415226496000,866609988480000,154555753600000,27554198400000,4910544000000,874800000000],
  #[9842104487289888000,1780194791438426880,321912234176322816,58196356702053120,10518174834105600,1900505449440000,343304762400000,61996946400000,11192788000000,2020140000000,364500000000],
  #[2147368251772339200,393033461839543296,71927062280340480,13161138915916800,2407861385856000,440458300800000,80558582400000,14731632000000,2693520000000,492400000000,90000000000],
  #[210832519264920576,39043059123133440,7230196133913600,1338925209984000,247949112960000,45916502400000,8503056000000,1574640000000,291600000000,54000000000,10000000000]]
def mx10_64_10 : Table := #[
  #[210832519264920576,39043059123133440,7230196133913600,1338925209984000,247949112960000,45916502400000,8503056000000,1574640000000,291600000000,54000000000,10000000000],
  #[2069282133526072320,387827720623125504,72676860397931520,13617365283763200,2551120873344000,477871747200000,89502537600000,16761168000000,3138480000000,587600000000,110000000000],
  #[9139329423073486080,1733343120490666752,328660417234642176,62302394012670720,11807510221497600,2237226467040000,423800359200000,80262770400000,15197428000000,2876940000000,544500000000],
  #[23920220218414556160,4590141489850899456,880540502045746176,168863754210499584,32373441379722240,6204518953344000,1188764104320000,227694780800000,43599529600000,8346096000000,1597200000000],
  #[41085193060332408960,7975867667477528448,1547807156568715392,300263668796923776,58228622058508416,11288047615459200,2187512724304000,423772389040000,82066507600000,15887348400000,3074610000000],
  #[48389227382169281664,9502007613130376064,1865200762507678848,365998368538809216,71791982834320512,14077187914212224,2759300528223360,540661270934400,105899705296000,20735169840000,4058485200000],
  #[39577608815663147040,7860207145640437728,1560528051628361760,309714358727985120,61447232425699360,12186910666319840,2416208254142496,478876685043680,94876971296800,18790786476000,3720278100000],
  #[22196965790795204160,4458006965950064064,895080768985968192,179662134170156480,36051406836061760,7231988143117760,1450312246132288,290758313881024,58273096214080,11675295614400,2338460520000],
  #[8169716575778790420,1659063338170032492,336841282423976212,68374225408650348,13875947549017620,2815362575955820,571091597941524,115817778725484,23482317418516,4759936388460,964614964500],
  #[1781872339573151820,365837940857157236,75101632592059084,15415490480108532,3163817855524172,649247871644020,133215043723212,27329921150708,5606147301964,1149821037684,235794769100],
  #[174887470365513049,36297399509823463,7533422539774681,1563540527123047,324508411289689,67350802343143,13978468410841,2901191556967,602134096729,124971227623,25937424601]]
def mx10_64_11 : Table := #[
  #[174887470365513049,36297399509823463,7533422539774681,1563540527123047,324508411289689,67350802343143,13978468410841,2901191556967,602134096729,124971227623,25937424601],
  #[1715877067737109160,360110049339312024,75566818203434536,15855320062352408,3326350370269608,697768175218840,146354324493608,30693909988632,6436534632616,1349603514776,282953722920],
  #[7575759129254406480,1607512314509425584,341027952926355280,72332691648845232,15338740181726544,3252045308129200,689345124875088,146093678266800,30955803394384,6557978682288,1389045548880],
  #[19820854074024107520,4251846490770338304,911830294724836864,195493749270745600,41902057590840832,8978889804853760,1923516699196928,411961394713088,88207503859200,18881835692544,4040859778560],
  #[34032032466720637440,7379369594380353024,1599623549089366528,346644294615137792,75096325231919616,16263811297902080,3521240256168448,762148126096896,164912753263104,35673110871552,7714368668160],
  #[40067902375912599552,8781209374111469568,1923873843304591360,421369651800674304,92260165908099072,20194330948702208,4418846843203584,966613128155136,211378467041280,46209705873408,10098809892864],
  #[32759920181563760640,7255680434987851776,1606519951365382144,355603465868664832,78689534319665152,17407578473226240,3849722617798656,851117514153984,188112639762432,41563696914432,9180736266240],
  #[18366747702871326720,4110526118697762816,919715378387353600,205730723650469888,46007995584086016,10286194012323840,2299122635636736,513753012633600,114770491342848,25632355516416,5723056373760],
  #[6757576985018695680,1528055869761847296,345466571992662016,78089041561190400,17647780577476608,3987536692838400,900808579547136,203456780107776,45943305338880,10372448452608,2341250334720],
  #[1473350118326927360,336582450834046976,76883314201853952,17560097338687488,4010282630774784,915746563031040,209086912659456,47734083551232,10896309485568,2487014129664,567575838720],
  #[144555105949057024,33358870603628544,7698200908529664,1776507901968384,409963361992704,94606929690624,21832368390144,5038238859264,1162670505984,268308578304,61917364224]]
def mx10_64_14 : Table := #[
  #[97656250000000000,27343750000000000,7656250000000000,2143750000000000,600250000000000,168070000000000,47059600000000,13176688000000,3689472640000,1033052339200,289254654976],
  #[957031250000000000,270468750000000000,76431250000000000,21596750000000000,6101970000000000,1723918000000000,486999632000000,137564622720000,38855417574400,10973967420416,3099157017600],
  #[4220507812500000000,1203792187500000000,343299812500000000,97888507500000000,27907876500000000,7955356780000000,2267415659040000,646162943865600,184116701875456,52454813725440,14942364192000],
  #[11029593750000000000,3174722250000000000,913626070000000000,262874506000000000,75621694960000000,21750187894400000,6254592298572800,1798270856324096,516930355092480,148569792537600,42692469120000],
  #[18915753281250000000,5494061238750000000,1595400273250000000,463182881630000000,134444297595600000,39015727678256000,11319959665630336,3283660956750720,952314576796800,276128791344000,80048379600000],
  #[22244925858750000000,6519125210850000000,1910081162878000000,559523583583440000,163866056248675200,47980371903618176,14045661964172160,4110785512041600,1202849945136000,351886142160000,102919345200000],
  #[18166689451312500000,5371408097359500000,1587852290895220000,469289878402290400,138669505903971616,40966514062168800,12099986783604000,3573125086860000,1054917731700000,311383529100000,91892272500000],
  #[10173346092735000000,3034563805947240000,905005049795761600,269853020377134656,80449693440392640,23979582153576000,7146250173720000,2129283498600000,634317528600000,188928369000000,56260575000000],
  #[3738704689080112500,1124968610934636300,338455404046023796,101813068102023180,30622865610122100,9209319892447500,2769159045712500,832541756287500,250265563312500,75219814687500,22604695312500],
  #[814206798955224500,247120071715553036,74997907395642420,22759228544604300,6906096125176500,2095433103487500,635741371912500,192864376687500,58504300312500,17745454687500,5382070312500],
  #[79792266297612001,24426203968656735,7477409378160225,2289002870865375,700715164550625,214504642209375,65664686390625,20101434609375,6153500390625,1883724609375,576650390625]]
def mx10_64_15 : Table := #[
  #[79792266297612001,24426203968656735,7477409378160225,2289002870865375,700715164550625,214504642209375,65664686390625,20101434609375,6153500390625,1883724609375,576650390625],
  #[781638526997015520,241404007657581664,74550280167562080,23020828872703200,7108207165836000,2194659740700000,677552355900000,209164315500000,64565707500000,19929037500000,6150937500000],
  #[3445590241456231680,1073524034412893952,334426758993300736,104167471054913280,32441864976057600,10102359627360000,3145457901600000,979241205600000,304818228000000,94872060000000,29524500000000],
  #[9000725528701992960,2828799451877769216,888895753001926656,279269914862977024,87724872264744960,27551625744384000,8651635937280000,2716291584000000,852672614400000,267618816000000,83980800000000],
  #[15429815192060559360,4891356380612395008,1550288587655872512,491259284682571776,155641102843641856,49300744146124800,15613441818624000,4943791964160000,1565086924800000,495374745600000,156764160000000],
  #[18137905205360984064,5799194181305892864,1853791073508261888,592470160007233536,189314857521119232,60480505904103424,19317842604195840,6168993752678400,1969620516864000,628728791040000,200658124800000],
  #[14806453228866109440,4774325735022133248,1539184110159790080,496119411187384320,159881644222709760,51514246944522240,16594803135348736,5344812827934720,1721108319436800,554113695744000,178362777600000],
  #[8288160407995023360,2695061683688177664,876210198530752512,284823816398438400,92570385760911360,30081188584488960,9773372028223488,3174824792817664,1031146485841920,334846387814400,108716359680000],
  #[3044630353957355520,998307367760166912,327296080121167872,107291044718051328,35166698298408960,11525093767249920,3776603398078464,1237375783010304,405363308363776,132778913955840,43486543872000],
  #[662776675691397120,219122084616339456,72439536889626624,23946126302380032,7915246769405952,2616150479339520,864628456292352,285735584268288,94420561035264,31198642438144,10307921510400],
  #[64925062108545024,21641687369515008,7213895789838336,2404631929946112,801543976648704,267181325549568,89060441849856,29686813949952,9895604649984,3298534883328,1099511627776]]
def mx10_64_22 : Table := #[
  #[17080198121677824,8946770444688384,4686403566265344,2454782820424704,1285838620222464,673534515354624,352803793757184,184801987206144,96801040917504,50705307147264,26559922791424],
  #[166735267378283520,87957210735442944,46397424052159488,24473440846052352,12908483810804736,6808238499363840,3590656792740864,1893620362411008,998601214313472,526588882451456,277671920092160],
  #[732444210268888320,389105669891973888,206691576152382720,109784389377712896,58307092131568896,30964604192121600,16442710695468288,8730626349392640,4635342815124736,2460838706701056,1306320169524480],
  #[1906680166414248960,1019996381707785216,545595147210451968,291805702991631360,156051801050213376,83444142148899840,44614425837628416,23851048430916608,12749486097525760,6814456950445056,3641862290795520],
  #[3257245284291008640,1754599724569302912,945040706766076032,508941669334218624,274050572645275776,147549861767763840,79431446880303232,42755491427727232,23011095126726784,12383084239591296,6662952600205440],
  #[3815630190169467264,2069569452740001408,1122372682094401920,608607781404610176,329975145407908224,178882667555643008,96961337733101952,52549941900914304,28476669630048640,15429415856012928,8358976898439552],
  #[3103984876923574560,1695114621520864992,925603312395442464,505355369601951456,275876574805350688,150583895721862880,82184100300085536,44847937060136672,24470472005048608,13350184178706144,7282441994852640],
  #[1731474557195463360,952009355837784384,523383483695190720,287708158874032448,158138414977481408,86911110129316160,47760140765340352,26242666292234560,14417901395364544,7920407987790144,4350549763158720],
  #[633843364687624980,350859172601767788,194199860714407444,107480536830262380,59480582149804308,32914305630376300,18212011558657044,10076146997896812,5574347653932820,3083586975726444,1705613259420180],
  #[137500412445463620,76623342498645116,42697147988574916,23791239098553852,13256089026720068,7385733742569340,4114826141196228,2292390810515708,1277041070755396,711376990292604,396253585521860],
  #[13422659310152401,7529784491061103,4224025446205009,2369575250310127,1329273920905681,745690248312943,418314041736529,234663974632687,131640766257361,73847259119983,41426511213649]]
def mx10_64_23 : Table := #[
  #[13422659310152401,7529784491061103,4224025446205009,2369575250310127,1329273920905681,745690248312943,418314041736529,234663974632687,131640766257361,73847259119983,41426511213649],
  #[130952773757584400,73972347322576944,41783360935525264,23600265907648688,13329389391393552,7528071223689520,4251454693534352,2400888682138032,1355774254391824,765568192107056,432276638751120],
  #[574914616496712000,327000216017154240,185975777236960576,105761778112115904,60140285431865664,34195342960457920,19441668529700160,11052627842497728,6282946306660672,3571307792056512,2029820738483520],
  #[1495712823406080000,856569197404262400,490489405737349120,280834240516132864,160777043641151488,92034759407144960,52678559907983360,30148824607232000,17252882485850112,9872065776881664,5648196837519360],
  #[2553656039961600000,1472400702065664000,848860991602892800,489321437168721920,282032514185895936,162536743838474240,93659437505781760,53963402832568320,31088164787527680,17907666797518848,10314098572861440],
  #[2989646095564800000,1735453099376640000,1007282889539584000,584568604173926400,339207117575946240,196806690028519424,114172151769464832,66225606769115136,38409366638297088,22273773553188864,12915045169496064],
  #[2430606581760000000,1420422773145600000,829982502092800000,484918115368960000,283279962210304000,165466886622412800,96639338590765056,56434442909515776,32952002045018112,19238290346999808,11230474060431360],
  #[1355041996800000000,797161291776000000,468916004454400000,275803013120000000,162202575175680000,95382996516864000,56083918419394560,32973086181556224,19383598297645056,11393638927958016,6696431737896960],
  #[495747072000000000,293578997760000000,173842628608000000,102932781465600000,60942031257600000,36078260060160000,21356955146649600,12641477150638080,7482051485761536,4427999663357952,2620342853959680],
  #[107479040000000000,64067993600000000,38189137920000000,22762487808000000,13566895718400000,8085779251200000,4818852642816000,2871742640947200,1711304217722880,1019737710526464,607615734251520],
  #[10485760000000000,6291456000000000,3774873600000000,2264924160000000,1358954496000000,815372697600000,489223618560000,293534171136000,176120502681600,105672301608960,63403380965376]]
def mx10_64_24 : Table := #[
  #[10485760000000000,6291456000000000,3774873600000000,2264924160000000,1358954496000000,815372697600000,489223618560000,293534171136000,176120502681600,105672301608960,63403380965376],
  #[102236160000000000,61761126400000000,37308334080000000,22535995392000000,13612194201600000,8221674700800000,4965619728384000,2998940781772800,1811105835909120,1093708321652736,660451885056000],
  #[448561152000000000,272817192960000000,165915394048000000,100894349721600000,61349717606400000,37301319106560000,22677858916761600,13786260418068480,8380266049437696,5093735163494400,3095868211200000],
  #[1166258995200000000,714109353984000000,437208848793600000,267650439577600000,163833257656320000,100274741968896000,61367257179095040,37552412222816256,22977100696780800,14057534914560000,8599633920000000],
  #[1989929410560000000,1226612898201600000,756007457587200000,465900826460160000,287084594397184000,176878669253836800,108965839533244416,67120437539635200,41339846983680000,25458499584000000,15676416000000000],
  #[2328217410355200000,1444688752066560000,896339041468416000,556054780074393600,344913405044981760,213919212002738176,132659001940377600,82256624271360000,50997897216000000,31614105600000000,19595520000000000],
  #[1891676645913600000,1181570335755264000,737942106063052800,460823753983057920,287737920017473536,179642398460928000,112142419686400000,69997119360000000,43685712000000000,27261360000000000,17010000000000000],
  #[1053934131294720000,662627305111449600,416564289502433280,261849229857386496,164579912136806400,103432808793600000,64997325120000000,40840216000000000,25658760000000000,16119000000000000,10125000000000000],
  #[385344666754632000,243854009628315840,154304289206773056,97632255352132800,61769707538760000,39077281035000000,24719482125000000,15635806875000000,9889328125000000,6254296875000000,3955078125000000],
  #[83491344463503600,53177564012139216,33868612448377200,21569899254930000,13736634297750000,8747698781250000,5570424843750000,3547019531250000,2258496093750000,1437988281250000,915527343750000],
  #[8140406085191601,5218209028968975,3345005787800625,2144234479359375,1374509281640625,881095693359375,564804931640625,362054443359375,232086181640625,148773193359375,95367431640625]]
def mx10_64_25 : Table := #[
  #[8140406085191601,5218209028968975,3345005787800625,2144234479359375,1374509281640625,881095693359375,564804931640625,362054443359375,232086181640625,148773193359375,95367431640625],
  #[79316777240328420,51186616567240284,33031503307635300,21314790332257500,13753551335062500,8874215085937500,5725673789062500,3694069335937500,2383227539062500,1537475585937500,991821289062500],
  #[347773561746055380,225935482624225452,146770306940095956,95336275048080300,61921960874572500,40215927777187500,26116722632812500,16959255117187500,11011911132812500,7149682617187500,4641723632812500],
  #[903616775818810560,590948299003772736,386429701528218816,252666463251818304,165188979982353600,107986928891400000,70585945755000000,46134147125000000,30149786875000000,19701703125000000,12873046875000000],
  #[1540782451075664160,1014296463744546528,667634325888190752,439402686753060576,289159332667803936,190266499958028000,125180941318900000,82350270047500000,54168017312500000,35626414687500000,23428945312500000],
  #[1801530250488468864,1193726522253492864,790891454613955968,523935301072450176,347046095923443072,229850462795997824,152213199966422400,100787800298640000,66728650534000000,44173870650000000,29239323750000000],
  #[1462780972618842240,975582127757397888,650578653774241920,433797505732456320,289218046823186560,192803386624135040,128515258963468416,85653545176035200,57080326073680000,38034512334000000,25340747250000000],
  #[814442153252981760,546698417041880064,366938638572260352,246261685759063040,165256192659983360,110885778004751360,74396222095756288,49909424839865344,33478856532659200,22455087757440000,15059644080000000],
  #[297584632919358720,201040306665898752,135807647281806592,91734659643065088,61959871788023040,41846108709733120,28259654005849344,19082948223615744,12885184697072896,8699655192134400,5873261191200000],
  #[64434279492510720,43808353587485696,29783749135688704,20248089520069632,13764827199398912,9357056807787520,6360471651935232,4323352896232448,2938550198232064,1997222045604864,1357375919744000],
  #[6278211847988224,4295618632834048,2939107485623296,2010968279636992,1375925665014784,941422823431168,644131405505536,440721487977472,301546281247744,206321139801088,141167095653376]]
def mx10_128_46 : Table := #[
  #[13744803133596058624,7710499318846569472,4325402056913929216,2426445056317570048,1361176495007417344,763586814272453632,428353578738205696,240295910023871488,134800144647537664,75619593338862592,42420747482776576],
  #[135771835831863505920,76426338423392242688,43020091083558581248,24215561426303978496,13630529843430585344,7672306537891302400,4318512696780616704,2430734555374029824,1368157141486302208,770068881053125632,433429376454456320],
  #[603522367813588389120,340887460868632670976,192539435708393819392,108747534731496911616,61420061797161798912,34689035557822984960,19591396518311202048,11064449239093998336,6248639763908693248,3528844334443328256,1992832893915598080],
  #[1589766237167501122560,901011144714444628992,510640597869637671936,289393544720080397312,164002587608950578176,92939634808471577600,52667131151514213376,29844674158093493248,16911515910159932416,9582675727818974208,5429747595016412160],
  #[2748162977054796147840,1562836675238087324544,888733200427930037376,505377538990624879488,287373826818140564608,163404966241084699520,92911629997748890752,52827701673317610368,30035867971707923584,17076761469789565824,9708624775871736960],
  #[3257578553289343726464,1858811008275611671680,1060624888807389123456,605166154231853612160,345281798231161582464,196996711140953398400,112390732878014354304,64119225448099167360,36579037116465214336,20867119792374602880,11903618203460129664],
  #[2681543321305252457760,1535286501394100277984,878983908044924906784,503221598185776730848,288087525716082453792,164921184114477585120,94409396704531901728,54043163809501336288,30935208839805365536,17707288389299622624,10135327093525835040],
  #[1513623756276832397760,869524661916573576768,499498822707880245696,286929756946659106368,164818223796038371776,94672391341475073600,54378835634405071296,31233802630805175872,17939411024870320576,10303382476605091392,5917520166406388160],
  #[560686848742790049780,323175780145573234956,186272443383378378228,107361789636907186956,61878838686726835188,35663651211509230860,20554203199901735412,11845861084357304076,6826902933094918132,3934339908369010956,2267310715932882420],
  #[123077600943539279220,71178211494176916492,41163310750249165428,23805026499277600524,13766456076543094644,7961056703230437900,4603777513384066164,2662275221684231436,1539524311970482548,890256385709920268,514800017627272820],
  #[12157665459056928801,7054447858958958687,4093321597173716769,2375137223051415903,1378166043005142561,799676592854835807,464009874866386209,269240297761977183,156225851787813921,90649568321324127,52599132235830049]]
def mx10_128_47 : Table := #[
  #[12157665459056928801,7054447858958958687,4093321597173716769,2375137223051415903,1378166043005142561,799676592854835807,464009874866386209,269240297761977183,156225851787813921,90649568321324127,52599132235830049],
  #[120075708237599296800,69910745685002257248,40703121193225169952,23697717961750717536,13796864783559756576,8032475153866278240,4676419983943658016,2722530733555312224,1584992723785795872,922734980716562272,537182627089328160],
  #[533669814389330208000,311768587863001301760,182130737370162418944,106396012799165240064,62152517049876792576,36306417267231793920,21207985434938062080,12388160691197031168,7236118639432738048,4226647263428788992,2468754201091380480],
  #[1405550128432803840000,823895309851722547200,482932256677062082560,283066795477240676352,165912921454322221056,97243391918131937280,56993933508447928320,33403028647880458240,19576352697200246784,11472722103541727232,6723415696589291520],
  #[2429345900994969600000,1428815292881485824000,840329791409229004800,494208702204364062720,290641746545270194176,170919888444254453760,100511146768820469760,59104819934686740480,34755107361142210560,20436261816740216832,12016317415180861440],
  #[2879224771549593600000,1699098075062599680000,1002646423129817088000,591648341955497164800,349112963630817607680,205994099373840007168,121543031782580944896,71711999307527749632,42309712783054209024,24961737145668599808,14726380491796119552],
  #[2369732322263040000000,1403115582416486400000,830758347236966400000,491861768813936640000,291204771082141696000,172401463521391411200,102063493985719025664,60420861707289624576,35767647461229723648,21172921884085321728,12533089780252016640],
  #[1337415067238400000000,794523617722368000000,471993706296115200000,280384732816998400000,166556366159216640000,98936557280428032000,58768011387029422080,34907102591626248192,20733622059974787072,12314735360876740608,7314143579964702720],
  #[495338913792000000000,295246453800960000000,175978030563328000000,104887490288025600000,62514443531059200000,37258763446517760000,22205873092401561600,13234226846792417280,7887158288880500736,4700388513407827968,2801161371050311680],
  #[108716359680000000000,65015067443200000000,38880191447040000000,23250805456896000000,13904097627340800000,8314627188326400000,4972077480148992000,2973227188381286400,1777924733203906560,1063147892027424768,635724566479503360],
  #[10737418240000000000,6442450944000000000,3865470566400000000,2319282339840000000,1391569403904000000,834941642342400000,500964985405440000,300578991243264000,180347394745958400,108208436847575040,64925062108545024]]
def mx10_128_48 : Table := #[
  #[10737418240000000000,6442450944000000000,3865470566400000000,2319282339840000000,1391569403904000000,834941642342400000,500964985405440000,300578991243264000,180347394745958400,108208436847575040,64925062108545024],
  #[106032005120000000000,63833951436800000000,38429219880960000000,23134841339904000000,13927290450739200000,8384205658521600000,5047222227959808000,3038352636483993600,1829023161715261440,1101020844924076032,662776675691397120],
  #[471179722752000000000,284616409743360000000,171919286468608000000,103843813235097600000,62723178941644800000,37884969678274560000,22882175822698905600,13820355879716782080,8347044145482694656,5041245089477689344,3044630353957355520],
  #[1240773269913600000000,752002837512192000000,455758958087372800000,276210172244787200000,167391299748495360000,101441319393558528000,61473186939163115520,37251643423680626688,22573247936870744064,13678283775371378688,8288160407995023360],
  #[2144211307069440000000,1303897610020454400000,792878332877209600000,482121816463114240000,293152911876161536000,178245615320511283200,108375405218437791744,65891572250415464448,40060492609593802752,24355104698910375936,14806453228866109440],
  #[2540890398877286400000,1550264775011205120000,945828797428006912000,577039963586769715200,352035090258009784320,214759667549949919232,131010527260575793152,79918324455353352192,48749846224617603072,29736293567972769792,18137905205360984064],
  #[2090941057409433600000,1279973538434433024000,783515360294866124800,479602390559638814720,293563760402895077376,179684577319192494080,109978147096041226240,67311490805065973760,41196395065133629440,25212527953285349376,15429815192060559360],
  #[1179888168109608960000,724660429325040844800,445058631594934435840,273330976459922833408,167860836695873585152,103085785161594798080,63304854447621570560,38874430594895544320,23871506348220776448,14658324432457531392,9000725528701992960],
  #[436927337253089568000,269235731360511394560,165900553077896598784,102224404444461503232,62987289511204472064,38809923335870391040,23912453645972747520,14733195324292510464,9077393415081010432,5592638310282019584,3445590241456231680],
  #[95881276786094655200,59276475420669151392,36645974546291828704,22655074099081029536,14005543789366872288,8658241805060851360,5352475150859037152,3308832565934876064,2045455678297590496,1264446542312178848,781638526997015520],
  #[9468276082626847201,5872728203148297631,3642578252585652961,2259320688312620191,1401350806674916321,869192272494568351,539119257623213281,334390425614398111,207406719684879841,128644674234925471,79792266297612001]]
def mx10_128_49 : Table := #[
  #[9468276082626847201,5872728203148297631,3642578252585652961,2259320688312620191,1401350806674916321,869192272494568351,539119257623213281,334390425614398111,207406719684879841,128644674234925471,79792266297612001],
  #[93484244866442288820,58178088642296801228,36205590505421230516,22531339667171374284,14021472344131454132,8725603644830515660,5429910001605228468,3378975946353086156,2102678715400006324,1308446942386330572,814206798955224500],
  #[415354049976218270580,259350250355160243084,161937096710061215092,101110794557274605964,63130646504085708660,39416179893797369740,24609367302688469364,15364485748056401292,9592400749002752884,5988641910949385100,3738704689080112500],
  #[1093590410063967092160,685117886889149393472,429205005467614653888,268876685163908348480,168434264222488026560,105510749878354479680,66092469482525789632,41399613688984656448,25931621515707006400,16242473704629480000,10173346092735000000],
  #[1889558113591538076960,1187704720149747692256,746524496269888146720,469209736048359502560,294901755888746417440,185342541255206662880,116482397415010618656,73203684553430463200,46003731004331380000,28909505646031500000,18166689451312500000],
  #[2238767587748961569664,1411855054526527857792,890344594559949040512,561452538419745178752,354042078805864156032,223245967569854997632,140766487029270883200,88756839747053520000,55961751353662000000,35283176280450000000,22244925858750000000],
  #[1842023964603575975040,1165479232910811751296,737396921054179032192,466536466619140514688,295159894157819493504,186731054222502192000,118130810722939600000,74730387045790000000,47273599329250000000,29903875758750000000,18915753281250000000],
  #[1039261260318834908160,659716706566561932288,418773676266786806784,265821668272006898688,168729282683233459200,107097561139420800000,67976328741360000000,43144436138000000000,27382987030000000000,17379038250000000000,11029593750000000000],
  #[384789770434505329920,245061501962540200704,156069647793458171136,99392486455724716800,63296597476438560000,40308704324460000000,25668999076500000000,16345966747500000000,10408875812500000000,6628092187500000000,4220507812500000000],
  #[84426447521494840320,53944143002536430592,34467159207108326400,22022268952844160000,14070644282448000000,8990031726000000000,5743858770000000000,3669792750000000000,2344631250000000000,1497968750000000000,957031250000000000],
  #[8335775831236199424,5343446045664230400,3425285926707840000,2195696106864000000,1407497504400000000,902241990000000000,578360250000000000,370743750000000000,237656250000000000,152343750000000000,97656250000000000]]
def mx10_256_98 : Table := #[
  #[9695514708609891533824,6013673680023856774144,3730000130647708632064,2313544384832123075584,1434983226035114312704,890052887034437991424,552058119806170399744,342415795829143665664,212384480957316957184,131732146416563682304,81707280688754689024],
  #[96341506914667909544960,59855549784975246099456,37187262992014213184512,23103767833752359011328,14353909970370876079104,8917773501325413975040,5540404519852728974336,3442114663678498440192,2138493907071388023808,1328585566584619664384,825410284508848389120],
  #[430792877438056190465280,268089809223041240967936,166836078752052908283136,103823944329186530077440,64610479078819847755008,40207427829639062137600,25021164521006111544576,15570646634977815472896,9689551762796135077120,6029740731647489649408,3752247772945836299520],
  #[1141510240637549736760320,711559483549556722953216,443547190739654019650560,276481248286437003947008,172341060792946688398336,107425919096573466045440,66961725296205742478336,41738942056431966940160,26016776655912299271168,16216711657769410292736,10108096041405110031360],
  #[1984999611488397406170240,1239396435643670659748736,773850193787089614826624,483170474008796965688192,301675971447637569301632,188355322292456770720640,117601244960235665190016,73424803212453448635264,45842734452082099416192,28621678069427632624512,17869669787484033805440],
  #[2366923587369709312167552,1480305270275484571029888,925795463235112745242240,578995950396087324610944,362103497141825057181312,226457457552526974439808,141624128407239647858304,88569580573529271570816,55389652564948546965120,34639324083676880523648,21662416028092889960064],
  #[1959952548613103175159840,1227802895445786426699744,769145682171185704718368,481820655068776271376352,301827685029659403505696,189073028570889665933280,118439600871586917830688,74192692706887009169376,46475296894667107029024,29112536825759572127712,18236217574670034915360],
  #[1112884448941255690777920,698309643822479766108864,438170630651010871399744,274938617043978326317760,172514447926975952500032,108246147019938270509760,67919841136916970493248,42616532675466503379648,26739716251359464781120,16777710782031761521344,10527029387127308784960],
  #[414690328679850815155380,260636699846078291095884,163811786779319383306420,102956232043789737979212,64708009513354582815924,40668798702209240148300,25560099805660949035188,16064293819375392744780,10096215681686938942644,6345319322221015638348,3987918020378585088180],
  #[91570156965874230632060,57647190165358313925764,36291186054517230405756,22846675276077966230148,14382807948064273724028,9054472939781973547140,5700087026130247998588,3588381516957351882372,2258991232627436406396,1422097213264533341316,895246902533968081020],
  #[9099059901039401398249,5737623759254144830743,3617992052013760116201,2281409000951351920407,1438595484676330191849,907139827916921585943,572018108049523802601,360699316540782525207,227447339729538025449,143422207854931621143,90438207500880449001]]
def mx10_256_99 : Table := #[
  #[9099059901039401398249,5737623759254144830743,3617992052013760116201,2281409000951351920407,1438595484676330191849,907139827916921585943,572018108049523802601,360699316540782525207,227447339729538025449,143422207854931621143,90438207500880449001],
  #[90411041054913797332920,57105285019724582689096,36068654985757971918264,22781504742949072177992,14389101745462330112952,9088323618556458171720,5740275134860228053432,3625604813858298621768,2289955561963324102584,1446346943834099081544,913517247483640899000],
  #[404258285481206915463120,255759553535374709965872,161809007160486056918992,102369697245629691509808,64764653689937090316240,40973454811179601769520,25921792784230769528784,16399303491483913399344,10374894645709928208336,6563566897347107300400,4152351124925640450000],
  #[1071155711848293483010560,678800978787154723628544,430159535900827794627072,272592496814728187799040,172741025054718940469760,109464763687050103580160,69366607718445352770048,43956573871832333673984,27854443297637220211200,17650719204146043840000,11184784174883880000000],
  #[1862582862003720515043840,1182282304664977977097728,750453238471459593208320,476346463029679502507520,302356366960986845954560,191916431206559080496640,121815364675648944554496,77319467202088769011200,49076378890182262080000,31149641044872504000000,19771083137421000000000],
  #[2220863132274499875262464,1412023546291789647949824,897757046801511314116608,570784861451373102084096,362896524463311715848192,230722479934670878388224,146687718119662991462400,93259768648953392640000,59291393054693184000000,37695170690654400000000,23964949257480000000000],
  #[1838931256023471234293760,1171113594600346844848128,745812109513232722501632,474959650544885140217856,302469004667543384825856,192620235914708978688000,122664760015005414400000,78115026396274560000000,49744631602512000000000,31677778384560000000000,20172516210000000000000],
  #[1044124753192580573429760,666036658667251543965696,424855411363237468962816,271007587205615922315264,172869754520431352217600,110269104213900902400000,70337339785390080000000,44865786767104000000000,28618171971840000000000,18254323296000000000000,11643588000000000000000],
  #[389052853896598493921280,248579548426306161672192,158825458523977192636416,101478203351091752140800,64837064631416463360000,41425889128565760000000,26467824449664000000000,16910737983360000000000,10804502608000000000000,6903111600000000000000,4410450000000000000000],
  #[85905513386934699294720,54977844971099512111104,35184649458783603916800,22517365770999889920000,14410557095141376000000,9222375232512000000000,5902060170240000000000,3777141888000000000000,2417251200000000000000,1546960000000000000000,990000000000000000000],
  #[8535834451185868210176,5471688750760171929600,3507492788948828160000,2248392813428736000000,1441277444505600000000,923895797760000000000,592240896000000000000,379641600000000000000,243360000000000000000,156000000000000000000,100000000000000000000]]


private def mx5Chk0 : Bool := ((((decide (mx5_1_0 = transform5 1 0 0 1) && decide (mx5_2_0 = transform5 1 0 1 2)) && (decide (mx5_2_1 = transform5 2 1 0 1) && decide (mx5_4_2 = transform5 3 2 1 2))) && ((decide (mx5_4_3 = transform5 4 3 0 1) && decide (mx5_8_6 = transform5 7 6 1 2)) && (decide (mx5_8_7 = transform5 8 7 0 1) && decide (mx5_16_12 = transform5 13 12 3 4)))) && (((decide (mx5_16_14 = transform5 15 14 1 2) && decide (mx5_16_15 = transform5 16 15 0 1)) && (decide (mx5_32_24 = transform5 25 24 7 8) && decide (mx5_32_25 = transform5 26 25 6 7))) && ((decide (mx5_32_26 = transform5 27 26 5 6) && decide (mx5_32_27 = transform5 28 27 4 5)) && (decide (mx5_32_28 = transform5 29 28 3 4) && decide (mx5_32_29 = transform5 30 29 2 3)))))
set_option maxRecDepth 10000 in set_option maxHeartbeats 2000000 in
private lemma mx5Ok0 : mx5Chk0 = true := by decide +kernel
private def mx5Chk1 : Bool := ((((decide (mx5_32_30 = transform5 31 30 1 2) && decide (mx5_32_31 = transform5 32 31 0 1)) && (decide (mx5_64_50 = transform5 51 50 13 14) && decide (mx5_64_51 = transform5 52 51 12 13))) && ((decide (mx5_64_52 = transform5 53 52 11 12) && decide (mx5_64_53 = transform5 54 53 10 11)) && (decide (mx5_64_54 = transform5 55 54 9 10) && decide (mx5_64_55 = transform5 56 55 8 9)))) && (((decide (mx5_64_56 = transform5 57 56 7 8) && decide (mx5_64_57 = transform5 58 57 6 7)) && (decide (mx5_64_58 = transform5 59 58 5 6) && decide (mx5_64_59 = transform5 60 59 4 5))) && ((decide (mx5_64_60 = transform5 61 60 3 4) && decide (mx5_64_61 = transform5 62 61 2 3)) && (decide (mx5_128_102 = transform5 103 102 25 26) && decide (mx5_128_103 = transform5 104 103 24 25)))))
set_option maxRecDepth 10000 in set_option maxHeartbeats 2000000 in
private lemma mx5Ok1 : mx5Chk1 = true := by decide +kernel
private def mx5Chk2 : Bool := ((((decide (mx5_128_104 = transform5 105 104 23 24) && decide (mx5_128_105 = transform5 106 105 22 23)) && (decide (mx5_128_106 = transform5 107 106 21 22) && decide (mx5_128_107 = transform5 108 107 20 21))) && ((decide (mx5_128_108 = transform5 109 108 19 20) && decide (mx5_128_109 = transform5 110 109 18 19)) && (decide (mx5_128_110 = transform5 111 110 17 18) && decide (mx5_128_111 = transform5 112 111 16 17)))) && (((decide (mx5_128_112 = transform5 113 112 15 16) && decide (mx5_128_113 = transform5 114 113 14 15)) && (decide (mx5_128_114 = transform5 115 114 13 14) && decide (mx5_128_115 = transform5 116 115 12 13))) && ((decide (mx5_128_118 = transform5 119 118 9 10) && decide (mx5_128_119 = transform5 120 119 8 9)) && (decide (mx5_128_120 = transform5 121 120 7 8) && decide (mx5_128_121 = transform5 122 121 6 7)))))
set_option maxRecDepth 10000 in set_option maxHeartbeats 2000000 in
private lemma mx5Ok2 : mx5Chk2 = true := by decide +kernel
private def mx5Chk3 : Bool := ((decide (mx5_256_226 = transform5 227 226 29 30) && decide (mx5_256_227 = transform5 228 227 28 29)) && (decide (mx5_256_242 = transform5 243 242 13 14) && decide (mx5_256_243 = transform5 244 243 12 13)))
set_option maxRecDepth 10000 in set_option maxHeartbeats 2000000 in
private lemma mx5Ok3 : mx5Chk3 = true := by decide +kernel
private def mx10Chk0 : Bool := ((((decide (mx10_1_0 = transform10 1 0 0 1) && decide (mx10_2_0 = transform10 1 0 1 2)) && (decide (mx10_2_1 = transform10 2 1 0 1) && decide (mx10_4_0 = transform10 1 0 3 4))) && ((decide (mx10_4_1 = transform10 2 1 2 3) && decide (mx10_4_2 = transform10 3 2 1 2)) && (decide (mx10_4_3 = transform10 4 3 0 1) && decide (mx10_8_0 = transform10 1 0 7 8)))) && (((decide (mx10_8_1 = transform10 2 1 6 7) && decide (mx10_8_2 = transform10 3 2 5 6)) && (decide (mx10_8_3 = transform10 4 3 4 5) && decide (mx10_8_4 = transform10 5 4 3 4))) && ((decide (mx10_8_5 = transform10 6 5 2 3) && decide (mx10_8_6 = transform10 7 6 1 2)) && (decide (mx10_8_7 = transform10 8 7 0 1) && decide (mx10_16_0 = transform10 1 0 15 16)))))
set_option maxRecDepth 10000 in set_option maxHeartbeats 3000000 in
private lemma mx10Ok0 : mx10Chk0 = true := by decide +kernel
private def mx10Chk1 : Bool := ((((decide (mx10_16_1 = transform10 2 1 14 15) && decide (mx10_16_2 = transform10 3 2 13 14)) && (decide (mx10_16_3 = transform10 4 3 12 13) && decide (mx10_16_4 = transform10 5 4 11 12))) && ((decide (mx10_16_5 = transform10 6 5 10 11) && decide (mx10_16_6 = transform10 7 6 9 10)) && (decide (mx10_16_7 = transform10 8 7 8 9) && decide (mx10_16_9 = transform10 10 9 6 7)))) && (((decide (mx10_16_10 = transform10 11 10 5 6) && decide (mx10_16_11 = transform10 12 11 4 5)) && (decide (mx10_32_0 = transform10 1 0 31 32) && decide (mx10_32_1 = transform10 2 1 30 31))) && ((decide (mx10_32_2 = transform10 3 2 29 30) && decide (mx10_32_3 = transform10 4 3 28 29)) && (decide (mx10_32_4 = transform10 5 4 27 28) && decide (mx10_32_5 = transform10 6 5 26 27)))))
set_option maxRecDepth 10000 in set_option maxHeartbeats 3000000 in
private lemma mx10Ok1 : mx10Chk1 = true := by decide +kernel
private def mx10Chk2 : Bool := ((((decide (mx10_32_6 = transform10 7 6 25 26) && decide (mx10_32_7 = transform10 8 7 24 25)) && (decide (mx10_32_8 = transform10 9 8 23 24) && decide (mx10_32_9 = transform10 10 9 22 23))) && ((decide (mx10_32_10 = transform10 11 10 21 22) && decide (mx10_32_11 = transform10 12 11 20 21)) && (decide (mx10_32_13 = transform10 14 13 18 19) && decide (mx10_32_16 = transform10 17 16 15 16)))) && (((decide (mx10_32_17 = transform10 18 17 14 15) && decide (mx10_64_0 = transform10 1 0 63 64)) && (decide (mx10_64_1 = transform10 2 1 62 63) && decide (mx10_64_2 = transform10 3 2 61 62))) && ((decide (mx10_64_3 = transform10 4 3 60 61) && decide (mx10_64_4 = transform10 5 4 59 60)) && (decide (mx10_64_5 = transform10 6 5 58 59) && decide (mx10_64_6 = transform10 7 6 57 58)))))
set_option maxRecDepth 10000 in set_option maxHeartbeats 3000000 in
private lemma mx10Ok2 : mx10Chk2 = true := by decide +kernel
private def mx10Chk3 : Bool := ((((decide (mx10_64_7 = transform10 8 7 56 57) && decide (mx10_64_8 = transform10 9 8 55 56)) && (decide (mx10_64_9 = transform10 10 9 54 55) && decide (mx10_64_10 = transform10 11 10 53 54))) && ((decide (mx10_64_11 = transform10 12 11 52 53) && decide (mx10_64_14 = transform10 15 14 49 50)) && (decide (mx10_64_15 = transform10 16 15 48 49) && decide (mx10_64_22 = transform10 23 22 41 42)))) && (((decide (mx10_64_23 = transform10 24 23 40 41) && decide (mx10_64_24 = transform10 25 24 39 40)) && (decide (mx10_64_25 = transform10 26 25 38 39) && decide (mx10_128_46 = transform10 47 46 81 82))) && ((decide (mx10_128_47 = transform10 48 47 80 81) && decide (mx10_128_48 = transform10 49 48 79 80)) && (decide (mx10_128_49 = transform10 50 49 78 79) && decide (mx10_256_98 = transform10 99 98 157 158)))))
set_option maxRecDepth 10000 in set_option maxHeartbeats 3000000 in
private lemma mx10Ok3 : mx10Chk3 = true := by decide +kernel
private def mx10Chk4 : Bool := decide (mx10_256_99 = transform10 100 99 156 157)
set_option maxRecDepth 10000 in set_option maxHeartbeats 3000000 in
private lemma mx10Ok4 : mx10Chk4 = true := by decide +kernel
lemma mx5_1_0_eq : mx5_1_0 = transform5 1 0 0 1 := of_decide_eq_true (bL (bL (bL (bL (mx5Ok0)))))
lemma mx5_2_0_eq : mx5_2_0 = transform5 1 0 1 2 := of_decide_eq_true (bR (bL (bL (bL (mx5Ok0)))))
lemma mx5_2_1_eq : mx5_2_1 = transform5 2 1 0 1 := of_decide_eq_true (bL (bR (bL (bL (mx5Ok0)))))
lemma mx5_4_2_eq : mx5_4_2 = transform5 3 2 1 2 := of_decide_eq_true (bR (bR (bL (bL (mx5Ok0)))))
lemma mx5_4_3_eq : mx5_4_3 = transform5 4 3 0 1 := of_decide_eq_true (bL (bL (bR (bL (mx5Ok0)))))
lemma mx5_8_6_eq : mx5_8_6 = transform5 7 6 1 2 := of_decide_eq_true (bR (bL (bR (bL (mx5Ok0)))))
lemma mx5_8_7_eq : mx5_8_7 = transform5 8 7 0 1 := of_decide_eq_true (bL (bR (bR (bL (mx5Ok0)))))
lemma mx5_16_12_eq : mx5_16_12 = transform5 13 12 3 4 := of_decide_eq_true (bR (bR (bR (bL (mx5Ok0)))))
lemma mx5_16_14_eq : mx5_16_14 = transform5 15 14 1 2 := of_decide_eq_true (bL (bL (bL (bR (mx5Ok0)))))
lemma mx5_16_15_eq : mx5_16_15 = transform5 16 15 0 1 := of_decide_eq_true (bR (bL (bL (bR (mx5Ok0)))))
lemma mx5_32_24_eq : mx5_32_24 = transform5 25 24 7 8 := of_decide_eq_true (bL (bR (bL (bR (mx5Ok0)))))
lemma mx5_32_25_eq : mx5_32_25 = transform5 26 25 6 7 := of_decide_eq_true (bR (bR (bL (bR (mx5Ok0)))))
lemma mx5_32_26_eq : mx5_32_26 = transform5 27 26 5 6 := of_decide_eq_true (bL (bL (bR (bR (mx5Ok0)))))
lemma mx5_32_27_eq : mx5_32_27 = transform5 28 27 4 5 := of_decide_eq_true (bR (bL (bR (bR (mx5Ok0)))))
lemma mx5_32_28_eq : mx5_32_28 = transform5 29 28 3 4 := of_decide_eq_true (bL (bR (bR (bR (mx5Ok0)))))
lemma mx5_32_29_eq : mx5_32_29 = transform5 30 29 2 3 := of_decide_eq_true (bR (bR (bR (bR (mx5Ok0)))))
lemma mx5_32_30_eq : mx5_32_30 = transform5 31 30 1 2 := of_decide_eq_true (bL (bL (bL (bL (mx5Ok1)))))
lemma mx5_32_31_eq : mx5_32_31 = transform5 32 31 0 1 := of_decide_eq_true (bR (bL (bL (bL (mx5Ok1)))))
lemma mx5_64_50_eq : mx5_64_50 = transform5 51 50 13 14 := of_decide_eq_true (bL (bR (bL (bL (mx5Ok1)))))
lemma mx5_64_51_eq : mx5_64_51 = transform5 52 51 12 13 := of_decide_eq_true (bR (bR (bL (bL (mx5Ok1)))))
lemma mx5_64_52_eq : mx5_64_52 = transform5 53 52 11 12 := of_decide_eq_true (bL (bL (bR (bL (mx5Ok1)))))
lemma mx5_64_53_eq : mx5_64_53 = transform5 54 53 10 11 := of_decide_eq_true (bR (bL (bR (bL (mx5Ok1)))))
lemma mx5_64_54_eq : mx5_64_54 = transform5 55 54 9 10 := of_decide_eq_true (bL (bR (bR (bL (mx5Ok1)))))
lemma mx5_64_55_eq : mx5_64_55 = transform5 56 55 8 9 := of_decide_eq_true (bR (bR (bR (bL (mx5Ok1)))))
lemma mx5_64_56_eq : mx5_64_56 = transform5 57 56 7 8 := of_decide_eq_true (bL (bL (bL (bR (mx5Ok1)))))
lemma mx5_64_57_eq : mx5_64_57 = transform5 58 57 6 7 := of_decide_eq_true (bR (bL (bL (bR (mx5Ok1)))))
lemma mx5_64_58_eq : mx5_64_58 = transform5 59 58 5 6 := of_decide_eq_true (bL (bR (bL (bR (mx5Ok1)))))
lemma mx5_64_59_eq : mx5_64_59 = transform5 60 59 4 5 := of_decide_eq_true (bR (bR (bL (bR (mx5Ok1)))))
lemma mx5_64_60_eq : mx5_64_60 = transform5 61 60 3 4 := of_decide_eq_true (bL (bL (bR (bR (mx5Ok1)))))
lemma mx5_64_61_eq : mx5_64_61 = transform5 62 61 2 3 := of_decide_eq_true (bR (bL (bR (bR (mx5Ok1)))))
lemma mx5_128_102_eq : mx5_128_102 = transform5 103 102 25 26 := of_decide_eq_true (bL (bR (bR (bR (mx5Ok1)))))
lemma mx5_128_103_eq : mx5_128_103 = transform5 104 103 24 25 := of_decide_eq_true (bR (bR (bR (bR (mx5Ok1)))))
lemma mx5_128_104_eq : mx5_128_104 = transform5 105 104 23 24 := of_decide_eq_true (bL (bL (bL (bL (mx5Ok2)))))
lemma mx5_128_105_eq : mx5_128_105 = transform5 106 105 22 23 := of_decide_eq_true (bR (bL (bL (bL (mx5Ok2)))))
lemma mx5_128_106_eq : mx5_128_106 = transform5 107 106 21 22 := of_decide_eq_true (bL (bR (bL (bL (mx5Ok2)))))
lemma mx5_128_107_eq : mx5_128_107 = transform5 108 107 20 21 := of_decide_eq_true (bR (bR (bL (bL (mx5Ok2)))))
lemma mx5_128_108_eq : mx5_128_108 = transform5 109 108 19 20 := of_decide_eq_true (bL (bL (bR (bL (mx5Ok2)))))
lemma mx5_128_109_eq : mx5_128_109 = transform5 110 109 18 19 := of_decide_eq_true (bR (bL (bR (bL (mx5Ok2)))))
lemma mx5_128_110_eq : mx5_128_110 = transform5 111 110 17 18 := of_decide_eq_true (bL (bR (bR (bL (mx5Ok2)))))
lemma mx5_128_111_eq : mx5_128_111 = transform5 112 111 16 17 := of_decide_eq_true (bR (bR (bR (bL (mx5Ok2)))))
lemma mx5_128_112_eq : mx5_128_112 = transform5 113 112 15 16 := of_decide_eq_true (bL (bL (bL (bR (mx5Ok2)))))
lemma mx5_128_113_eq : mx5_128_113 = transform5 114 113 14 15 := of_decide_eq_true (bR (bL (bL (bR (mx5Ok2)))))
lemma mx5_128_114_eq : mx5_128_114 = transform5 115 114 13 14 := of_decide_eq_true (bL (bR (bL (bR (mx5Ok2)))))
lemma mx5_128_115_eq : mx5_128_115 = transform5 116 115 12 13 := of_decide_eq_true (bR (bR (bL (bR (mx5Ok2)))))
lemma mx5_128_118_eq : mx5_128_118 = transform5 119 118 9 10 := of_decide_eq_true (bL (bL (bR (bR (mx5Ok2)))))
lemma mx5_128_119_eq : mx5_128_119 = transform5 120 119 8 9 := of_decide_eq_true (bR (bL (bR (bR (mx5Ok2)))))
lemma mx5_128_120_eq : mx5_128_120 = transform5 121 120 7 8 := of_decide_eq_true (bL (bR (bR (bR (mx5Ok2)))))
lemma mx5_128_121_eq : mx5_128_121 = transform5 122 121 6 7 := of_decide_eq_true (bR (bR (bR (bR (mx5Ok2)))))
lemma mx5_256_226_eq : mx5_256_226 = transform5 227 226 29 30 := of_decide_eq_true (bL (bL (mx5Ok3)))
lemma mx5_256_227_eq : mx5_256_227 = transform5 228 227 28 29 := of_decide_eq_true (bR (bL (mx5Ok3)))
lemma mx5_256_242_eq : mx5_256_242 = transform5 243 242 13 14 := of_decide_eq_true (bL (bR (mx5Ok3)))
lemma mx5_256_243_eq : mx5_256_243 = transform5 244 243 12 13 := of_decide_eq_true (bR (bR (mx5Ok3)))
lemma mx10_1_0_eq : mx10_1_0 = transform10 1 0 0 1 := of_decide_eq_true (bL (bL (bL (bL (mx10Ok0)))))
lemma mx10_2_0_eq : mx10_2_0 = transform10 1 0 1 2 := of_decide_eq_true (bR (bL (bL (bL (mx10Ok0)))))
lemma mx10_2_1_eq : mx10_2_1 = transform10 2 1 0 1 := of_decide_eq_true (bL (bR (bL (bL (mx10Ok0)))))
lemma mx10_4_0_eq : mx10_4_0 = transform10 1 0 3 4 := of_decide_eq_true (bR (bR (bL (bL (mx10Ok0)))))
lemma mx10_4_1_eq : mx10_4_1 = transform10 2 1 2 3 := of_decide_eq_true (bL (bL (bR (bL (mx10Ok0)))))
lemma mx10_4_2_eq : mx10_4_2 = transform10 3 2 1 2 := of_decide_eq_true (bR (bL (bR (bL (mx10Ok0)))))
lemma mx10_4_3_eq : mx10_4_3 = transform10 4 3 0 1 := of_decide_eq_true (bL (bR (bR (bL (mx10Ok0)))))
lemma mx10_8_0_eq : mx10_8_0 = transform10 1 0 7 8 := of_decide_eq_true (bR (bR (bR (bL (mx10Ok0)))))
lemma mx10_8_1_eq : mx10_8_1 = transform10 2 1 6 7 := of_decide_eq_true (bL (bL (bL (bR (mx10Ok0)))))
lemma mx10_8_2_eq : mx10_8_2 = transform10 3 2 5 6 := of_decide_eq_true (bR (bL (bL (bR (mx10Ok0)))))
lemma mx10_8_3_eq : mx10_8_3 = transform10 4 3 4 5 := of_decide_eq_true (bL (bR (bL (bR (mx10Ok0)))))
lemma mx10_8_4_eq : mx10_8_4 = transform10 5 4 3 4 := of_decide_eq_true (bR (bR (bL (bR (mx10Ok0)))))
lemma mx10_8_5_eq : mx10_8_5 = transform10 6 5 2 3 := of_decide_eq_true (bL (bL (bR (bR (mx10Ok0)))))
lemma mx10_8_6_eq : mx10_8_6 = transform10 7 6 1 2 := of_decide_eq_true (bR (bL (bR (bR (mx10Ok0)))))
lemma mx10_8_7_eq : mx10_8_7 = transform10 8 7 0 1 := of_decide_eq_true (bL (bR (bR (bR (mx10Ok0)))))
lemma mx10_16_0_eq : mx10_16_0 = transform10 1 0 15 16 := of_decide_eq_true (bR (bR (bR (bR (mx10Ok0)))))
lemma mx10_16_1_eq : mx10_16_1 = transform10 2 1 14 15 := of_decide_eq_true (bL (bL (bL (bL (mx10Ok1)))))
lemma mx10_16_2_eq : mx10_16_2 = transform10 3 2 13 14 := of_decide_eq_true (bR (bL (bL (bL (mx10Ok1)))))
lemma mx10_16_3_eq : mx10_16_3 = transform10 4 3 12 13 := of_decide_eq_true (bL (bR (bL (bL (mx10Ok1)))))
lemma mx10_16_4_eq : mx10_16_4 = transform10 5 4 11 12 := of_decide_eq_true (bR (bR (bL (bL (mx10Ok1)))))
lemma mx10_16_5_eq : mx10_16_5 = transform10 6 5 10 11 := of_decide_eq_true (bL (bL (bR (bL (mx10Ok1)))))
lemma mx10_16_6_eq : mx10_16_6 = transform10 7 6 9 10 := of_decide_eq_true (bR (bL (bR (bL (mx10Ok1)))))
lemma mx10_16_7_eq : mx10_16_7 = transform10 8 7 8 9 := of_decide_eq_true (bL (bR (bR (bL (mx10Ok1)))))
lemma mx10_16_9_eq : mx10_16_9 = transform10 10 9 6 7 := of_decide_eq_true (bR (bR (bR (bL (mx10Ok1)))))
lemma mx10_16_10_eq : mx10_16_10 = transform10 11 10 5 6 := of_decide_eq_true (bL (bL (bL (bR (mx10Ok1)))))
lemma mx10_16_11_eq : mx10_16_11 = transform10 12 11 4 5 := of_decide_eq_true (bR (bL (bL (bR (mx10Ok1)))))
lemma mx10_32_0_eq : mx10_32_0 = transform10 1 0 31 32 := of_decide_eq_true (bL (bR (bL (bR (mx10Ok1)))))
lemma mx10_32_1_eq : mx10_32_1 = transform10 2 1 30 31 := of_decide_eq_true (bR (bR (bL (bR (mx10Ok1)))))
lemma mx10_32_2_eq : mx10_32_2 = transform10 3 2 29 30 := of_decide_eq_true (bL (bL (bR (bR (mx10Ok1)))))
lemma mx10_32_3_eq : mx10_32_3 = transform10 4 3 28 29 := of_decide_eq_true (bR (bL (bR (bR (mx10Ok1)))))
lemma mx10_32_4_eq : mx10_32_4 = transform10 5 4 27 28 := of_decide_eq_true (bL (bR (bR (bR (mx10Ok1)))))
lemma mx10_32_5_eq : mx10_32_5 = transform10 6 5 26 27 := of_decide_eq_true (bR (bR (bR (bR (mx10Ok1)))))
lemma mx10_32_6_eq : mx10_32_6 = transform10 7 6 25 26 := of_decide_eq_true (bL (bL (bL (bL (mx10Ok2)))))
lemma mx10_32_7_eq : mx10_32_7 = transform10 8 7 24 25 := of_decide_eq_true (bR (bL (bL (bL (mx10Ok2)))))
lemma mx10_32_8_eq : mx10_32_8 = transform10 9 8 23 24 := of_decide_eq_true (bL (bR (bL (bL (mx10Ok2)))))
lemma mx10_32_9_eq : mx10_32_9 = transform10 10 9 22 23 := of_decide_eq_true (bR (bR (bL (bL (mx10Ok2)))))
lemma mx10_32_10_eq : mx10_32_10 = transform10 11 10 21 22 := of_decide_eq_true (bL (bL (bR (bL (mx10Ok2)))))
lemma mx10_32_11_eq : mx10_32_11 = transform10 12 11 20 21 := of_decide_eq_true (bR (bL (bR (bL (mx10Ok2)))))
lemma mx10_32_13_eq : mx10_32_13 = transform10 14 13 18 19 := of_decide_eq_true (bL (bR (bR (bL (mx10Ok2)))))
lemma mx10_32_16_eq : mx10_32_16 = transform10 17 16 15 16 := of_decide_eq_true (bR (bR (bR (bL (mx10Ok2)))))
lemma mx10_32_17_eq : mx10_32_17 = transform10 18 17 14 15 := of_decide_eq_true (bL (bL (bL (bR (mx10Ok2)))))
lemma mx10_64_0_eq : mx10_64_0 = transform10 1 0 63 64 := of_decide_eq_true (bR (bL (bL (bR (mx10Ok2)))))
lemma mx10_64_1_eq : mx10_64_1 = transform10 2 1 62 63 := of_decide_eq_true (bL (bR (bL (bR (mx10Ok2)))))
lemma mx10_64_2_eq : mx10_64_2 = transform10 3 2 61 62 := of_decide_eq_true (bR (bR (bL (bR (mx10Ok2)))))
lemma mx10_64_3_eq : mx10_64_3 = transform10 4 3 60 61 := of_decide_eq_true (bL (bL (bR (bR (mx10Ok2)))))
lemma mx10_64_4_eq : mx10_64_4 = transform10 5 4 59 60 := of_decide_eq_true (bR (bL (bR (bR (mx10Ok2)))))
lemma mx10_64_5_eq : mx10_64_5 = transform10 6 5 58 59 := of_decide_eq_true (bL (bR (bR (bR (mx10Ok2)))))
lemma mx10_64_6_eq : mx10_64_6 = transform10 7 6 57 58 := of_decide_eq_true (bR (bR (bR (bR (mx10Ok2)))))
lemma mx10_64_7_eq : mx10_64_7 = transform10 8 7 56 57 := of_decide_eq_true (bL (bL (bL (bL (mx10Ok3)))))
lemma mx10_64_8_eq : mx10_64_8 = transform10 9 8 55 56 := of_decide_eq_true (bR (bL (bL (bL (mx10Ok3)))))
lemma mx10_64_9_eq : mx10_64_9 = transform10 10 9 54 55 := of_decide_eq_true (bL (bR (bL (bL (mx10Ok3)))))
lemma mx10_64_10_eq : mx10_64_10 = transform10 11 10 53 54 := of_decide_eq_true (bR (bR (bL (bL (mx10Ok3)))))
lemma mx10_64_11_eq : mx10_64_11 = transform10 12 11 52 53 := of_decide_eq_true (bL (bL (bR (bL (mx10Ok3)))))
lemma mx10_64_14_eq : mx10_64_14 = transform10 15 14 49 50 := of_decide_eq_true (bR (bL (bR (bL (mx10Ok3)))))
lemma mx10_64_15_eq : mx10_64_15 = transform10 16 15 48 49 := of_decide_eq_true (bL (bR (bR (bL (mx10Ok3)))))
lemma mx10_64_22_eq : mx10_64_22 = transform10 23 22 41 42 := of_decide_eq_true (bR (bR (bR (bL (mx10Ok3)))))
lemma mx10_64_23_eq : mx10_64_23 = transform10 24 23 40 41 := of_decide_eq_true (bL (bL (bL (bR (mx10Ok3)))))
lemma mx10_64_24_eq : mx10_64_24 = transform10 25 24 39 40 := of_decide_eq_true (bR (bL (bL (bR (mx10Ok3)))))
lemma mx10_64_25_eq : mx10_64_25 = transform10 26 25 38 39 := of_decide_eq_true (bL (bR (bL (bR (mx10Ok3)))))
lemma mx10_128_46_eq : mx10_128_46 = transform10 47 46 81 82 := of_decide_eq_true (bR (bR (bL (bR (mx10Ok3)))))
lemma mx10_128_47_eq : mx10_128_47 = transform10 48 47 80 81 := of_decide_eq_true (bL (bL (bR (bR (mx10Ok3)))))
lemma mx10_128_48_eq : mx10_128_48 = transform10 49 48 79 80 := of_decide_eq_true (bR (bL (bR (bR (mx10Ok3)))))
lemma mx10_128_49_eq : mx10_128_49 = transform10 50 49 78 79 := of_decide_eq_true (bL (bR (bR (bR (mx10Ok3)))))
lemma mx10_256_98_eq : mx10_256_98 = transform10 99 98 157 158 := of_decide_eq_true (bR (bR (bR (bR (mx10Ok3)))))
lemma mx10_256_99_eq : mx10_256_99 = transform10 100 99 156 157 := of_decide_eq_true (mx10Ok4)

/- Signs certified in bounded chunks and inherited by descendants. -/
private def sgChk0 : Bool := ((((hasMark mx10_1_0 mx5_1_0 table0 .up && hasMark mx10_1_0 mx5_1_0 table1 .up) && (hasMark mx10_1_0 mx5_1_0 table7 .down && (hasMark mx10_1_0 mx5_1_0 table8 .down && hasMark mx10_1_0 mx5_1_0 table9 .down))) && ((hasMark mx10_1_0 mx5_1_0 table23 .up && (hasMark mx10_1_0 mx5_1_0 table24 .up && hasMark mx10_1_0 mx5_1_0 table25 .up)) && (hasMark mx10_1_0 mx5_1_0 table26 .up && (hasMark mx10_1_0 mx5_1_0 table27 .up && hasMark mx10_1_0 mx5_1_0 table28 .up)))) && (((hasMark mx10_1_0 mx5_1_0 table29 .up && hasMark mx10_1_0 mx5_1_0 table30 .up) && (hasMark mx10_1_0 mx5_1_0 table31 .up && (hasMark mx10_1_0 mx5_1_0 table32 .up && hasMark mx10_1_0 mx5_1_0 table33 .up))) && ((hasMark mx10_1_0 mx5_1_0 table34 .up && (hasMark mx10_2_0 mx5_1_0 table2 .up && hasMark mx10_2_0 mx5_1_0 table3 .up)) && (hasMark mx10_2_0 mx5_2_0 table10 .down && (hasMark mx10_2_0 mx5_2_0 table15 .up && hasMark mx10_2_0 mx5_2_0 table16 .up)))))
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
private lemma sgOk0 : sgChk0 = true := by decide +kernel
private def sgChk1 : Bool := ((((hasMark mx10_2_0 mx5_2_0 table17 .up && hasMark mx10_2_0 mx5_2_0 table18 .up) && (hasMark mx10_2_0 mx5_2_0 table19 .up && (hasMark mx10_2_0 mx5_2_0 table20 .up && hasMark mx10_2_0 mx5_2_0 table21 .up))) && ((hasMark mx10_2_0 mx5_2_0 table22 .up && (hasMark mx10_4_0 mx5_2_0 table4 .up && hasMark mx10_4_0 mx5_2_0 table5 .up)) && (hasMark mx10_4_0 mx5_2_0 table13 .up && (hasMark mx10_4_0 mx5_2_0 table14 .up && hasMark mx10_4_1 mx5_2_0 table6 .down)))) && (((hasMark mx10_4_1 mx5_2_0 table11 .down && hasMark mx10_8_2 mx5_2_0 table4 .up) && (hasMark mx10_8_2 mx5_2_0 table13 .up && (hasMark mx10_8_2 mx5_2_0 table14 .up && hasMark mx10_8_3 mx5_2_0 table5 .down))) && ((hasMark mx10_8_3 mx5_2_0 table12 .down && (hasMark mx10_2_0 mx5_2_1 table4 .up && hasMark mx10_2_0 mx5_2_1 table6 .down)) && (hasMark mx10_2_0 mx5_4_2 table10 .down && (hasMark mx10_2_0 mx5_4_2 table16 .up && hasMark mx10_2_0 mx5_4_2 table17 .up)))))
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
private lemma sgOk1 : sgChk1 = true := by decide +kernel
private def sgChk2 : Bool := ((((hasMark mx10_2_0 mx5_4_2 table18 .up && hasMark mx10_2_0 mx5_4_2 table19 .up) && (hasMark mx10_2_0 mx5_4_2 table20 .up && (hasMark mx10_2_0 mx5_4_2 table21 .up && hasMark mx10_2_0 mx5_4_2 table22 .up))) && ((hasMark mx10_4_0 mx5_4_2 table5 .up && (hasMark mx10_4_0 mx5_4_2 table12 .up && hasMark mx10_4_0 mx5_4_2 table13 .up)) && (hasMark mx10_4_0 mx5_4_2 table14 .up && (hasMark mx10_4_0 mx5_4_2 table15 .up && hasMark mx10_4_1 mx5_4_2 table11 .down)))) && (((hasMark mx10_8_2 mx5_4_2 table14 .up && hasMark mx10_8_2 mx5_4_2 table15 .up) && (hasMark mx10_8_3 mx5_4_2 table12 .down && (hasMark mx10_4_0 mx5_4_3 table5 .up && hasMark mx10_4_0 mx5_4_3 table12 .up))) && ((hasMark mx10_4_0 mx5_4_3 table13 .up && (hasMark mx10_4_0 mx5_4_3 table14 .up && hasMark mx10_4_0 mx5_4_3 table15 .up)) && (hasMark mx10_8_0 mx5_4_3 table11 .up && (hasMark mx10_8_0 mx5_8_6 table10 .down && hasMark mx10_8_0 mx5_8_6 table21 .up)))))
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
private lemma sgOk2 : sgChk2 = true := by decide +kernel
private def sgChk3 : Bool := ((((hasMark mx10_8_0 mx5_8_6 table22 .up && hasMark mx10_8_0 mx5_16_12 table16 .up) && (hasMark mx10_8_0 mx5_16_12 table20 .up && (hasMark mx10_8_0 mx5_32_24 table17 .up && hasMark mx10_8_0 mx5_32_24 table18 .up))) && ((hasMark mx10_8_0 mx5_32_24 table19 .up && (hasMark mx10_16_0 mx5_64_50 table17 .up && hasMark mx10_16_0 mx5_64_50 table19 .up)) && (hasMark mx10_32_0 mx5_128_102 table17 .up && (hasMark mx10_64_0 mx5_128_103 table18 .down && hasMark mx10_64_1 mx5_128_103 table17 .up)))) && (((hasMark mx10_32_1 mx5_64_51 table17 .up && hasMark mx10_32_1 mx5_64_51 table19 .up) && (hasMark mx10_16_1 mx5_32_25 table17 .up && (hasMark mx10_16_1 mx5_32_25 table18 .up && hasMark mx10_16_1 mx5_32_25 table19 .up))) && ((hasMark mx10_8_0 mx5_32_26 table16 .up && (hasMark mx10_16_0 mx5_64_52 table20 .up && hasMark mx10_32_0 mx5_64_52 table18 .down)) && (hasMark mx10_32_1 mx5_128_104 table17 .up && (hasMark mx10_64_2 mx5_128_105 table18 .down && hasMark mx10_64_3 mx5_128_105 table17 .up)))))
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
private lemma sgOk3 : sgChk3 = true := by decide +kernel
private def sgChk4 : Bool := ((((hasMark mx10_16_0 mx5_64_53 table18 .down && hasMark mx10_32_0 mx5_64_53 table17 .down) && (hasMark mx10_32_0 mx5_64_53 table19 .down && (hasMark mx10_32_1 mx5_64_53 table20 .up && hasMark mx10_16_1 mx5_32_26 table20 .up))) && ((hasMark mx10_16_1 mx5_64_52 table17 .up && (hasMark mx10_16_1 mx5_64_52 table19 .up && hasMark mx10_32_2 mx5_128_106 table17 .up)) && (hasMark mx10_64_4 mx5_128_107 table18 .down && (hasMark mx10_64_5 mx5_128_107 table17 .up && hasMark mx10_32_3 mx5_64_53 table17 .up)))) && (((hasMark mx10_32_3 mx5_64_53 table19 .up && hasMark mx10_16_0 mx5_32_27 table17 .down) && (hasMark mx10_16_0 mx5_32_27 table18 .down && (hasMark mx10_16_0 mx5_32_27 table19 .down && hasMark mx10_16_1 mx5_32_27 table16 .up))) && ((hasMark mx10_16_1 mx5_64_54 table20 .up && (hasMark mx10_32_2 mx5_64_54 table18 .down && hasMark mx10_32_3 mx5_128_108 table17 .up)) && (hasMark mx10_64_6 mx5_128_109 table18 .down && (hasMark mx10_64_7 mx5_128_109 table17 .up && hasMark mx10_16_1 mx5_64_55 table18 .down)))))
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
private lemma sgOk4 : sgChk4 = true := by decide +kernel
private def sgChk5 : Bool := ((((hasMark mx10_32_2 mx5_64_55 table17 .down && hasMark mx10_32_2 mx5_64_55 table19 .down) && (hasMark mx10_32_3 mx5_64_55 table20 .up && (hasMark mx10_8_0 mx5_8_7 table17 .down && hasMark mx10_8_0 mx5_8_7 table18 .down))) && ((hasMark mx10_8_0 mx5_8_7 table19 .down && (hasMark mx10_8_0 mx5_16_14 table22 .up && hasMark mx10_16_0 mx5_16_14 table20 .down)) && (hasMark mx10_16_1 mx5_16_14 table10 .down && (hasMark mx10_16_1 mx5_32_28 table21 .up && hasMark mx10_16_1 mx5_32_29 table20 .down)))) && (((hasMark mx10_8_0 mx5_16_15 table16 .down && hasMark mx10_8_0 mx5_16_15 table20 .down) && (hasMark mx10_8_0 mx5_32_30 table22 .up && (hasMark mx10_8_0 mx5_32_31 table21 .down && hasMark mx10_8_1 mx5_4_3 table10 .down))) && ((hasMark mx10_8_1 mx5_4_3 table22 .up && (hasMark mx10_8_1 mx5_8_6 table16 .up && hasMark mx10_8_1 mx5_8_6 table20 .up)) && (hasMark mx10_8_1 mx5_8_6 table21 .up && (hasMark mx10_16_2 mx5_8_6 table11 .up && hasMark mx10_16_2 mx5_16_12 table17 .up)))))
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
private lemma sgOk5 : sgChk5 = true := by decide +kernel
private def sgChk6 : Bool := ((((hasMark mx10_16_2 mx5_16_12 table18 .up && hasMark mx10_16_2 mx5_16_12 table19 .up) && (hasMark mx10_16_2 mx5_32_26 table17 .up && (hasMark mx10_16_2 mx5_32_26 table18 .up && hasMark mx10_16_2 mx5_32_26 table19 .up))) && ((hasMark mx10_16_2 mx5_64_54 table17 .up && (hasMark mx10_16_2 mx5_64_54 table19 .up && hasMark mx10_32_4 mx5_128_110 table17 .up)) && (hasMark mx10_64_8 mx5_128_111 table18 .down && (hasMark mx10_64_9 mx5_128_111 table17 .up && hasMark mx10_32_5 mx5_64_55 table17 .up)))) && (((hasMark mx10_32_5 mx5_64_55 table19 .up && hasMark mx10_16_3 mx5_8_6 table17 .up) && (hasMark mx10_16_3 mx5_8_6 table18 .up && (hasMark mx10_16_3 mx5_8_6 table19 .up && hasMark mx10_8_1 mx5_16_14 table21 .up))) && ((hasMark mx10_16_2 mx5_16_14 table11 .up && (hasMark mx10_16_2 mx5_32_28 table16 .up && hasMark mx10_16_2 mx5_64_56 table20 .up)) && (hasMark mx10_32_4 mx5_64_56 table18 .down && (hasMark mx10_32_5 mx5_128_112 table17 .up && hasMark mx10_64_10 mx5_128_113 table18 .down)))))
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
private lemma sgOk6 : sgChk6 = true := by decide +kernel
private def sgChk7 : Bool := ((((hasMark mx10_64_11 mx5_256_226 table17 .up && hasMark mx10_64_11 mx5_256_226 table19 .up) && (hasMark mx10_64_11 mx5_256_227 table18 .down && (hasMark mx10_16_2 mx5_64_57 table18 .down && hasMark mx10_32_4 mx5_64_57 table17 .down))) && ((hasMark mx10_32_4 mx5_64_57 table19 .down && (hasMark mx10_32_5 mx5_64_57 table20 .up && hasMark mx10_16_2 mx5_32_29 table17 .down)) && (hasMark mx10_16_2 mx5_32_29 table18 .down && (hasMark mx10_16_2 mx5_32_29 table19 .down && hasMark mx10_16_3 mx5_16_14 table16 .up)))) && (((hasMark mx10_16_3 mx5_16_14 table20 .up && hasMark mx10_32_6 mx5_16_14 table11 .up) && (hasMark mx10_32_6 mx5_64_56 table17 .up && (hasMark mx10_32_6 mx5_64_56 table19 .up && hasMark mx10_32_6 mx5_128_114 table19 .up))) && ((hasMark mx10_32_6 mx5_128_115 table18 .down && (hasMark mx10_32_6 mx5_32_29 table18 .down && hasMark mx10_32_7 mx5_32_28 table17 .up)) && (hasMark mx10_32_7 mx5_32_28 table19 .up && (hasMark mx10_64_14 mx5_32_29 table11 .up && hasMark mx10_64_14 mx5_32_29 table18 .down)))))
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
private lemma sgOk7 : sgChk7 = true := by decide +kernel
private def sgChk8 : Bool := ((((hasMark mx10_64_15 mx5_64_58 table19 .up && hasMark mx10_64_15 mx5_64_59 table17 .down) && (hasMark mx10_64_15 mx5_64_59 table18 .down && (hasMark mx10_8_1 mx5_16_15 table17 .down && hasMark mx10_8_1 mx5_16_15 table18 .down))) && ((hasMark mx10_8_1 mx5_16_15 table19 .down && (hasMark mx10_16_2 mx5_16_15 table11 .up && hasMark mx10_32_4 mx5_16_15 table16 .down)) && (hasMark mx10_32_4 mx5_16_15 table20 .down && (hasMark mx10_32_5 mx5_32_30 table21 .up && hasMark mx10_32_5 mx5_32_31 table16 .down)))) && (((hasMark mx10_32_5 mx5_32_31 table20 .down && hasMark mx10_16_3 mx5_16_15 table21 .up) && (hasMark mx10_4_1 mx5_4_3 table10 .down && (hasMark mx10_4_1 mx5_4_3 table21 .up && hasMark mx10_4_1 mx5_4_3 table22 .up))) && ((hasMark mx10_8_2 mx5_4_3 table5 .up && (hasMark mx10_8_2 mx5_8_6 table11 .down && hasMark mx10_8_2 mx5_8_6 table14 .up)) && (hasMark mx10_8_2 mx5_8_6 table15 .up && (hasMark mx10_8_2 mx5_8_6 table16 .up && hasMark mx10_8_2 mx5_8_6 table17 .up)))))
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
private lemma sgOk8 : sgChk8 = true := by decide +kernel
private def sgChk9 : Bool := ((((hasMark mx10_8_2 mx5_8_6 table18 .up && hasMark mx10_8_2 mx5_8_6 table19 .up) && (hasMark mx10_8_2 mx5_8_6 table20 .up && (hasMark mx10_16_4 mx5_8_7 table13 .up && hasMark mx10_16_4 mx5_8_7 table14 .up))) && ((hasMark mx10_16_4 mx5_8_7 table15 .up && (hasMark mx10_16_4 mx5_16_14 table11 .down && hasMark mx10_16_4 mx5_16_14 table16 .up)) && (hasMark mx10_16_4 mx5_16_14 table20 .up && (hasMark mx10_16_4 mx5_32_28 table17 .up && hasMark mx10_16_4 mx5_32_28 table18 .up)))) && (((hasMark mx10_16_4 mx5_32_28 table19 .up && hasMark mx10_16_4 mx5_32_29 table12 .up) && (hasMark mx10_16_4 mx5_64_58 table19 .up && (hasMark mx10_32_8 mx5_128_118 table19 .up && hasMark mx10_32_8 mx5_128_119 table17 .down))) && ((hasMark mx10_32_8 mx5_128_119 table18 .down && (hasMark mx10_32_9 mx5_64_59 table19 .up && hasMark mx10_16_4 mx5_16_15 table12 .up)) && (hasMark mx10_16_4 mx5_16_15 table17 .down && (hasMark mx10_16_4 mx5_32_30 table20 .up && hasMark mx10_16_4 mx5_64_60 table11 .down)))))
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
private lemma sgOk9 : sgChk9 = true := by decide +kernel
private def sgChk10 : Bool := ((((hasMark mx10_16_4 mx5_64_60 table16 .up && hasMark mx10_32_8 mx5_64_60 table18 .down) && (hasMark mx10_32_9 mx5_128_120 table19 .up && (hasMark mx10_32_9 mx5_128_121 table18 .down && hasMark mx10_16_4 mx5_64_61 table18 .down))) && ((hasMark mx10_16_4 mx5_32_31 table16 .down && (hasMark mx10_16_4 mx5_32_31 table18 .down && hasMark mx10_16_4 mx5_32_31 table19 .down)) && (hasMark mx10_16_5 mx5_8_7 table11 .down && (hasMark mx10_16_5 mx5_8_7 table20 .up && hasMark mx10_32_10 mx5_8_7 table13 .up)))) && (((hasMark mx10_32_10 mx5_8_7 table14 .up && hasMark mx10_32_10 mx5_8_7 table15 .up) && (hasMark mx10_32_10 mx5_16_14 table16 .up && (hasMark mx10_32_10 mx5_16_14 table18 .up && hasMark mx10_32_10 mx5_16_14 table19 .up))) && ((hasMark mx10_32_10 mx5_64_60 table16 .up && (hasMark mx10_32_10 mx5_64_60 table19 .up && hasMark mx10_32_10 mx5_64_61 table17 .down)) && (hasMark mx10_32_10 mx5_64_61 table18 .down && (hasMark mx10_32_10 mx5_32_31 table16 .down && hasMark mx10_32_10 mx5_32_31 table17 .down)))))
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
private lemma sgOk10 : sgChk10 = true := by decide +kernel
private def sgChk11 : Bool := ((((hasMark mx10_32_10 mx5_32_31 table18 .down && hasMark mx10_32_11 mx5_8_7 table12 .down) && (hasMark mx10_32_11 mx5_16_14 table14 .up && (hasMark mx10_32_11 mx5_16_14 table15 .up && hasMark mx10_32_11 mx5_16_14 table16 .up))) && ((hasMark mx10_32_11 mx5_16_14 table17 .up && (hasMark mx10_32_11 mx5_16_14 table18 .up && hasMark mx10_32_11 mx5_16_14 table19 .up)) && (hasMark mx10_32_11 mx5_32_30 table14 .up && (hasMark mx10_32_11 mx5_32_30 table19 .up && hasMark mx10_64_22 mx5_32_30 table13 .up)))) && (((hasMark mx10_64_22 mx5_32_30 table15 .up && hasMark mx10_64_22 mx5_128_120 table16 .up) && (hasMark mx10_64_22 mx5_128_120 table18 .up && (hasMark mx10_64_22 mx5_128_121 table17 .down && hasMark mx10_64_22 mx5_64_61 table17 .down))) && ((hasMark mx10_64_23 mx5_64_60 table15 .up && (hasMark mx10_64_23 mx5_64_60 table18 .up && hasMark mx10_64_23 mx5_64_61 table16 .down)) && (hasMark mx10_64_23 mx5_64_61 table17 .down && (hasMark mx10_32_11 mx5_32_31 table16 .down && hasMark mx10_32_11 mx5_32_31 table17 .down)))))
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
private lemma sgOk11 : sgChk11 = true := by decide +kernel
private def sgChk12 : Bool := ((((hasMark mx10_32_11 mx5_32_31 table18 .down && hasMark mx10_64_22 mx5_32_31 table13 .up) && (hasMark mx10_64_22 mx5_32_31 table14 .up && (hasMark mx10_128_46 mx5_32_31 table14 .up && hasMark mx10_128_47 mx5_32_31 table13 .down))) && ((hasMark mx10_128_47 mx5_32_31 table19 .up && (hasMark mx10_8_3 mx5_4_3 table11 .down && hasMark mx10_8_3 mx5_4_3 table12 .down)) && (hasMark mx10_8_3 mx5_4_3 table13 .down && (hasMark mx10_8_3 mx5_4_3 table19 .up && hasMark mx10_8_3 mx5_4_3 table20 .up)))) && (((hasMark mx10_8_3 mx5_8_6 table17 .up && hasMark mx10_8_3 mx5_8_6 table18 .up) && (hasMark mx10_16_6 mx5_16_14 table17 .up && (hasMark mx10_16_6 mx5_16_14 table18 .up && hasMark mx10_16_6 mx5_64_60 table18 .up))) && ((hasMark mx10_64_24 mx5_64_60 table5 .up && (hasMark mx10_128_48 mx5_64_60 table14 .up && hasMark mx10_128_48 mx5_64_60 table15 .up)) && (hasMark mx10_128_49 mx5_128_120 table15 .up && (hasMark mx10_128_49 mx5_128_120 table17 .up && hasMark mx10_256_98 mx5_256_242 table15 .up)))))
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
private lemma sgOk12 : sgChk12 = true := by decide +kernel
private def sgChk13 : Bool := ((((hasMark mx10_256_98 mx5_256_243 table16 .down && hasMark mx10_256_98 mx5_256_243 table17 .down) && (hasMark mx10_256_99 mx5_128_121 table14 .down && (hasMark mx10_256_99 mx5_128_121 table16 .down && hasMark mx10_64_25 mx5_64_60 table14 .down))) && ((hasMark mx10_32_13 mx5_64_60 table5 .down && (hasMark mx10_32_13 mx5_64_60 table14 .down && hasMark mx10_32_13 mx5_64_60 table15 .down)) && (hasMark mx10_16_6 mx5_64_61 table16 .down && (hasMark mx10_16_6 mx5_64_61 table17 .down && hasMark mx10_16_6 mx5_32_31 table15 .down)))) && (((hasMark mx10_16_6 mx5_32_31 table16 .down && hasMark mx10_16_6 mx5_32_31 table17 .down) && (hasMark mx10_16_7 mx5_8_7 table5 .down && (hasMark mx10_16_7 mx5_8_7 table14 .down && hasMark mx10_16_7 mx5_8_7 table15 .down))) && ((hasMark mx10_2_1 mx5_1_0 table5 .down && (hasMark mx10_2_1 mx5_1_0 table6 .down && hasMark mx10_2_1 mx5_1_0 table10 .down)) && (hasMark mx10_2_1 mx5_1_0 table11 .down && (hasMark mx10_2_1 mx5_1_0 table12 .down && hasMark mx10_2_1 mx5_1_0 table13 .down)))))
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
private lemma sgOk13 : sgChk13 = true := by decide +kernel
private def sgChk14 : Bool := ((((hasMark mx10_2_1 mx5_1_0 table19 .up && hasMark mx10_2_1 mx5_1_0 table20 .up) && (hasMark mx10_2_1 mx5_1_0 table21 .up && (hasMark mx10_2_1 mx5_1_0 table22 .up && hasMark mx10_4_2 mx5_1_0 table18 .up))) && ((hasMark mx10_4_2 mx5_2_0 table17 .up && (hasMark mx10_8_4 mx5_2_0 table2 .up && hasMark mx10_8_4 mx5_2_0 table16 .up)) && (hasMark mx10_32_16 mx5_2_0 table3 .up && (hasMark mx10_32_16 mx5_2_0 table15 .up && hasMark mx10_32_17 mx5_2_0 table14 .down)))) && (((hasMark mx10_16_9 mx5_2_0 table14 .down && hasMark mx10_8_5 mx5_2_0 table4 .down) && (hasMark mx10_8_5 mx5_2_0 table14 .down && (hasMark mx10_16_10 mx5_2_0 table2 .up && hasMark mx10_16_11 mx5_2_0 table15 .down))) && ((hasMark mx10_4_2 mx5_2_1 table2 .up && (hasMark mx10_4_2 mx5_2_1 table3 .up && hasMark mx10_4_2 mx5_2_1 table14 .down)) && (hasMark mx10_4_3 mx5_1_0 table4 .down && (hasMark mx10_4_3 mx5_1_0 table14 .down && hasMark mx10_4_3 mx5_1_0 table15 .down)))))
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
private lemma sgOk14 : sgChk14 = true := by decide +kernel
private def sgChk15 : Bool := ((hasMark mx10_4_3 mx5_1_0 table16 .down && hasMark mx10_8_6 mx5_2_0 table18 .up) && (hasMark mx10_8_6 mx5_2_1 table2 .up && (hasMark mx10_8_7 mx5_1_0 table3 .down && hasMark mx10_8_7 mx5_1_0 table17 .down)))
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
private lemma sgOk15 : sgChk15 = true := by decide +kernel
lemma s0 : Pol 1 0 1 0 table0 .up := signFast _ _ _ _ _ _ _ _ mx10_1_0_eq mx5_1_0_eq (bL (bL (bL (bL (sgOk0)))))
lemma s1 : Pol 1 0 1 0 table1 .up := signFast _ _ _ _ _ _ _ _ mx10_1_0_eq mx5_1_0_eq (bR (bL (bL (bL (sgOk0)))))
lemma s2 : Pol 1 0 1 0 table7 .down := signFast _ _ _ _ _ _ _ _ mx10_1_0_eq mx5_1_0_eq (bL (bR (bL (bL (sgOk0)))))
lemma s3 : Pol 1 0 1 0 table8 .down := signFast _ _ _ _ _ _ _ _ mx10_1_0_eq mx5_1_0_eq (bL (bR (bR (bL (bL (sgOk0))))))
lemma s4 : Pol 1 0 1 0 table9 .down := signFast _ _ _ _ _ _ _ _ mx10_1_0_eq mx5_1_0_eq (bR (bR (bR (bL (bL (sgOk0))))))
lemma s5 : Pol 1 0 1 0 table23 .up := signFast _ _ _ _ _ _ _ _ mx10_1_0_eq mx5_1_0_eq (bL (bL (bR (bL (sgOk0)))))
lemma s6 : Pol 1 0 1 0 table24 .up := signFast _ _ _ _ _ _ _ _ mx10_1_0_eq mx5_1_0_eq (bL (bR (bL (bR (bL (sgOk0))))))
lemma s7 : Pol 1 0 1 0 table25 .up := signFast _ _ _ _ _ _ _ _ mx10_1_0_eq mx5_1_0_eq (bR (bR (bL (bR (bL (sgOk0))))))
lemma s8 : Pol 1 0 1 0 table26 .up := signFast _ _ _ _ _ _ _ _ mx10_1_0_eq mx5_1_0_eq (bL (bR (bR (bL (sgOk0)))))
lemma s9 : Pol 1 0 1 0 table27 .up := signFast _ _ _ _ _ _ _ _ mx10_1_0_eq mx5_1_0_eq (bL (bR (bR (bR (bL (sgOk0))))))
lemma s10 : Pol 1 0 1 0 table28 .up := signFast _ _ _ _ _ _ _ _ mx10_1_0_eq mx5_1_0_eq (bR (bR (bR (bR (bL (sgOk0))))))
lemma s11 : Pol 1 0 1 0 table29 .up := signFast _ _ _ _ _ _ _ _ mx10_1_0_eq mx5_1_0_eq (bL (bL (bL (bR (sgOk0)))))
lemma s12 : Pol 1 0 1 0 table30 .up := signFast _ _ _ _ _ _ _ _ mx10_1_0_eq mx5_1_0_eq (bR (bL (bL (bR (sgOk0)))))
lemma s13 : Pol 1 0 1 0 table31 .up := signFast _ _ _ _ _ _ _ _ mx10_1_0_eq mx5_1_0_eq (bL (bR (bL (bR (sgOk0)))))
lemma s14 : Pol 1 0 1 0 table32 .up := signFast _ _ _ _ _ _ _ _ mx10_1_0_eq mx5_1_0_eq (bL (bR (bR (bL (bR (sgOk0))))))
lemma s15 : Pol 1 0 1 0 table33 .up := signFast _ _ _ _ _ _ _ _ mx10_1_0_eq mx5_1_0_eq (bR (bR (bR (bL (bR (sgOk0))))))
lemma s16 : Pol 1 0 1 0 table34 .up := signFast _ _ _ _ _ _ _ _ mx10_1_0_eq mx5_1_0_eq (bL (bL (bR (bR (sgOk0)))))
lemma s17 : Pol 2 0 1 0 table2 .up := signFast _ _ _ _ _ _ _ _ mx10_2_0_eq mx5_1_0_eq (bL (bR (bL (bR (bR (sgOk0))))))
lemma s18 : Pol 2 0 1 0 table3 .up := signFast _ _ _ _ _ _ _ _ mx10_2_0_eq mx5_1_0_eq (bR (bR (bL (bR (bR (sgOk0))))))
lemma s19 : Pol 2 0 2 0 table10 .down := signFast _ _ _ _ _ _ _ _ mx10_2_0_eq mx5_2_0_eq (bL (bR (bR (bR (sgOk0)))))
lemma s20 : Pol 2 0 2 0 table15 .up := signFast _ _ _ _ _ _ _ _ mx10_2_0_eq mx5_2_0_eq (bL (bR (bR (bR (bR (sgOk0))))))
lemma s21 : Pol 2 0 2 0 table16 .up := signFast _ _ _ _ _ _ _ _ mx10_2_0_eq mx5_2_0_eq (bR (bR (bR (bR (bR (sgOk0))))))
lemma s22 : Pol 2 0 2 0 table17 .up := signFast _ _ _ _ _ _ _ _ mx10_2_0_eq mx5_2_0_eq (bL (bL (bL (bL (sgOk1)))))
lemma s23 : Pol 2 0 2 0 table18 .up := signFast _ _ _ _ _ _ _ _ mx10_2_0_eq mx5_2_0_eq (bR (bL (bL (bL (sgOk1)))))
lemma s24 : Pol 2 0 2 0 table19 .up := signFast _ _ _ _ _ _ _ _ mx10_2_0_eq mx5_2_0_eq (bL (bR (bL (bL (sgOk1)))))
lemma s25 : Pol 2 0 2 0 table20 .up := signFast _ _ _ _ _ _ _ _ mx10_2_0_eq mx5_2_0_eq (bL (bR (bR (bL (bL (sgOk1))))))
lemma s26 : Pol 2 0 2 0 table21 .up := signFast _ _ _ _ _ _ _ _ mx10_2_0_eq mx5_2_0_eq (bR (bR (bR (bL (bL (sgOk1))))))
lemma s27 : Pol 2 0 2 0 table22 .up := signFast _ _ _ _ _ _ _ _ mx10_2_0_eq mx5_2_0_eq (bL (bL (bR (bL (sgOk1)))))
lemma s28 : Pol 4 0 2 0 table4 .up := signFast _ _ _ _ _ _ _ _ mx10_4_0_eq mx5_2_0_eq (bL (bR (bL (bR (bL (sgOk1))))))
lemma s29 : Pol 4 0 2 0 table5 .up := signFast _ _ _ _ _ _ _ _ mx10_4_0_eq mx5_2_0_eq (bR (bR (bL (bR (bL (sgOk1))))))
lemma s30 : Pol 4 0 2 0 table13 .up := signFast _ _ _ _ _ _ _ _ mx10_4_0_eq mx5_2_0_eq (bL (bR (bR (bL (sgOk1)))))
lemma s31 : Pol 4 0 2 0 table14 .up := signFast _ _ _ _ _ _ _ _ mx10_4_0_eq mx5_2_0_eq (bL (bR (bR (bR (bL (sgOk1))))))
lemma s32 : Pol 4 1 2 0 table6 .down := signFast _ _ _ _ _ _ _ _ mx10_4_1_eq mx5_2_0_eq (bR (bR (bR (bR (bL (sgOk1))))))
lemma s33 : Pol 4 1 2 0 table11 .down := signFast _ _ _ _ _ _ _ _ mx10_4_1_eq mx5_2_0_eq (bL (bL (bL (bR (sgOk1)))))
lemma s34 : Pol 8 2 2 0 table4 .up := signFast _ _ _ _ _ _ _ _ mx10_8_2_eq mx5_2_0_eq (bR (bL (bL (bR (sgOk1)))))
lemma s35 : Pol 8 2 2 0 table13 .up := signFast _ _ _ _ _ _ _ _ mx10_8_2_eq mx5_2_0_eq (bL (bR (bL (bR (sgOk1)))))
lemma s36 : Pol 8 2 2 0 table14 .up := signFast _ _ _ _ _ _ _ _ mx10_8_2_eq mx5_2_0_eq (bL (bR (bR (bL (bR (sgOk1))))))
lemma s37 : Pol 8 3 2 0 table5 .down := signFast _ _ _ _ _ _ _ _ mx10_8_3_eq mx5_2_0_eq (bR (bR (bR (bL (bR (sgOk1))))))
lemma s38 : Pol 8 3 2 0 table12 .down := signFast _ _ _ _ _ _ _ _ mx10_8_3_eq mx5_2_0_eq (bL (bL (bR (bR (sgOk1)))))
lemma s39 : Pol 2 0 2 1 table4 .up := signFast _ _ _ _ _ _ _ _ mx10_2_0_eq mx5_2_1_eq (bL (bR (bL (bR (bR (sgOk1))))))
lemma s40 : Pol 2 0 2 1 table6 .down := signFast _ _ _ _ _ _ _ _ mx10_2_0_eq mx5_2_1_eq (bR (bR (bL (bR (bR (sgOk1))))))
lemma s41 : Pol 2 0 4 2 table10 .down := signFast _ _ _ _ _ _ _ _ mx10_2_0_eq mx5_4_2_eq (bL (bR (bR (bR (sgOk1)))))
lemma s42 : Pol 2 0 4 2 table16 .up := signFast _ _ _ _ _ _ _ _ mx10_2_0_eq mx5_4_2_eq (bL (bR (bR (bR (bR (sgOk1))))))
lemma s43 : Pol 2 0 4 2 table17 .up := signFast _ _ _ _ _ _ _ _ mx10_2_0_eq mx5_4_2_eq (bR (bR (bR (bR (bR (sgOk1))))))
lemma s44 : Pol 2 0 4 2 table18 .up := signFast _ _ _ _ _ _ _ _ mx10_2_0_eq mx5_4_2_eq (bL (bL (bL (bL (sgOk2)))))
lemma s45 : Pol 2 0 4 2 table19 .up := signFast _ _ _ _ _ _ _ _ mx10_2_0_eq mx5_4_2_eq (bR (bL (bL (bL (sgOk2)))))
lemma s46 : Pol 2 0 4 2 table20 .up := signFast _ _ _ _ _ _ _ _ mx10_2_0_eq mx5_4_2_eq (bL (bR (bL (bL (sgOk2)))))
lemma s47 : Pol 2 0 4 2 table21 .up := signFast _ _ _ _ _ _ _ _ mx10_2_0_eq mx5_4_2_eq (bL (bR (bR (bL (bL (sgOk2))))))
lemma s48 : Pol 2 0 4 2 table22 .up := signFast _ _ _ _ _ _ _ _ mx10_2_0_eq mx5_4_2_eq (bR (bR (bR (bL (bL (sgOk2))))))
lemma s49 : Pol 4 0 4 2 table5 .up := signFast _ _ _ _ _ _ _ _ mx10_4_0_eq mx5_4_2_eq (bL (bL (bR (bL (sgOk2)))))
lemma s50 : Pol 4 0 4 2 table12 .up := signFast _ _ _ _ _ _ _ _ mx10_4_0_eq mx5_4_2_eq (bL (bR (bL (bR (bL (sgOk2))))))
lemma s51 : Pol 4 0 4 2 table13 .up := signFast _ _ _ _ _ _ _ _ mx10_4_0_eq mx5_4_2_eq (bR (bR (bL (bR (bL (sgOk2))))))
lemma s52 : Pol 4 0 4 2 table14 .up := signFast _ _ _ _ _ _ _ _ mx10_4_0_eq mx5_4_2_eq (bL (bR (bR (bL (sgOk2)))))
lemma s53 : Pol 4 0 4 2 table15 .up := signFast _ _ _ _ _ _ _ _ mx10_4_0_eq mx5_4_2_eq (bL (bR (bR (bR (bL (sgOk2))))))
lemma s54 : Pol 4 1 4 2 table11 .down := signFast _ _ _ _ _ _ _ _ mx10_4_1_eq mx5_4_2_eq (bR (bR (bR (bR (bL (sgOk2))))))
lemma s55 : Pol 8 2 4 2 table14 .up := signFast _ _ _ _ _ _ _ _ mx10_8_2_eq mx5_4_2_eq (bL (bL (bL (bR (sgOk2)))))
lemma s56 : Pol 8 2 4 2 table15 .up := signFast _ _ _ _ _ _ _ _ mx10_8_2_eq mx5_4_2_eq (bR (bL (bL (bR (sgOk2)))))
lemma s57 : Pol 8 3 4 2 table12 .down := signFast _ _ _ _ _ _ _ _ mx10_8_3_eq mx5_4_2_eq (bL (bR (bL (bR (sgOk2)))))
lemma s58 : Pol 4 0 4 3 table5 .up := signFast _ _ _ _ _ _ _ _ mx10_4_0_eq mx5_4_3_eq (bL (bR (bR (bL (bR (sgOk2))))))
lemma s59 : Pol 4 0 4 3 table12 .up := signFast _ _ _ _ _ _ _ _ mx10_4_0_eq mx5_4_3_eq (bR (bR (bR (bL (bR (sgOk2))))))
lemma s60 : Pol 4 0 4 3 table13 .up := signFast _ _ _ _ _ _ _ _ mx10_4_0_eq mx5_4_3_eq (bL (bL (bR (bR (sgOk2)))))
lemma s61 : Pol 4 0 4 3 table14 .up := signFast _ _ _ _ _ _ _ _ mx10_4_0_eq mx5_4_3_eq (bL (bR (bL (bR (bR (sgOk2))))))
lemma s62 : Pol 4 0 4 3 table15 .up := signFast _ _ _ _ _ _ _ _ mx10_4_0_eq mx5_4_3_eq (bR (bR (bL (bR (bR (sgOk2))))))
lemma s63 : Pol 8 0 4 3 table11 .up := signFast _ _ _ _ _ _ _ _ mx10_8_0_eq mx5_4_3_eq (bL (bR (bR (bR (sgOk2)))))
lemma s64 : Pol 8 0 8 6 table10 .down := signFast _ _ _ _ _ _ _ _ mx10_8_0_eq mx5_8_6_eq (bL (bR (bR (bR (bR (sgOk2))))))
lemma s65 : Pol 8 0 8 6 table21 .up := signFast _ _ _ _ _ _ _ _ mx10_8_0_eq mx5_8_6_eq (bR (bR (bR (bR (bR (sgOk2))))))
lemma s66 : Pol 8 0 8 6 table22 .up := signFast _ _ _ _ _ _ _ _ mx10_8_0_eq mx5_8_6_eq (bL (bL (bL (bL (sgOk3)))))
lemma s67 : Pol 8 0 16 12 table16 .up := signFast _ _ _ _ _ _ _ _ mx10_8_0_eq mx5_16_12_eq (bR (bL (bL (bL (sgOk3)))))
lemma s68 : Pol 8 0 16 12 table20 .up := signFast _ _ _ _ _ _ _ _ mx10_8_0_eq mx5_16_12_eq (bL (bR (bL (bL (sgOk3)))))
lemma s69 : Pol 8 0 32 24 table17 .up := signFast _ _ _ _ _ _ _ _ mx10_8_0_eq mx5_32_24_eq (bL (bR (bR (bL (bL (sgOk3))))))
lemma s70 : Pol 8 0 32 24 table18 .up := signFast _ _ _ _ _ _ _ _ mx10_8_0_eq mx5_32_24_eq (bR (bR (bR (bL (bL (sgOk3))))))
lemma s71 : Pol 8 0 32 24 table19 .up := signFast _ _ _ _ _ _ _ _ mx10_8_0_eq mx5_32_24_eq (bL (bL (bR (bL (sgOk3)))))
lemma s72 : Pol 16 0 64 50 table17 .up := signFast _ _ _ _ _ _ _ _ mx10_16_0_eq mx5_64_50_eq (bL (bR (bL (bR (bL (sgOk3))))))
lemma s73 : Pol 16 0 64 50 table19 .up := signFast _ _ _ _ _ _ _ _ mx10_16_0_eq mx5_64_50_eq (bR (bR (bL (bR (bL (sgOk3))))))
lemma s74 : Pol 32 0 128 102 table17 .up := signFast _ _ _ _ _ _ _ _ mx10_32_0_eq mx5_128_102_eq (bL (bR (bR (bL (sgOk3)))))
lemma s75 : Pol 64 0 128 103 table18 .down := signFast _ _ _ _ _ _ _ _ mx10_64_0_eq mx5_128_103_eq (bL (bR (bR (bR (bL (sgOk3))))))
lemma s76 : Pol 64 1 128 103 table17 .up := signFast _ _ _ _ _ _ _ _ mx10_64_1_eq mx5_128_103_eq (bR (bR (bR (bR (bL (sgOk3))))))
lemma s77 : Pol 32 1 64 51 table17 .up := signFast _ _ _ _ _ _ _ _ mx10_32_1_eq mx5_64_51_eq (bL (bL (bL (bR (sgOk3)))))
lemma s78 : Pol 32 1 64 51 table19 .up := signFast _ _ _ _ _ _ _ _ mx10_32_1_eq mx5_64_51_eq (bR (bL (bL (bR (sgOk3)))))
lemma s79 : Pol 16 1 32 25 table17 .up := signFast _ _ _ _ _ _ _ _ mx10_16_1_eq mx5_32_25_eq (bL (bR (bL (bR (sgOk3)))))
lemma s80 : Pol 16 1 32 25 table18 .up := signFast _ _ _ _ _ _ _ _ mx10_16_1_eq mx5_32_25_eq (bL (bR (bR (bL (bR (sgOk3))))))
lemma s81 : Pol 16 1 32 25 table19 .up := signFast _ _ _ _ _ _ _ _ mx10_16_1_eq mx5_32_25_eq (bR (bR (bR (bL (bR (sgOk3))))))
lemma s82 : Pol 8 0 32 26 table16 .up := signFast _ _ _ _ _ _ _ _ mx10_8_0_eq mx5_32_26_eq (bL (bL (bR (bR (sgOk3)))))
lemma s83 : Pol 16 0 64 52 table20 .up := signFast _ _ _ _ _ _ _ _ mx10_16_0_eq mx5_64_52_eq (bL (bR (bL (bR (bR (sgOk3))))))
lemma s84 : Pol 32 0 64 52 table18 .down := signFast _ _ _ _ _ _ _ _ mx10_32_0_eq mx5_64_52_eq (bR (bR (bL (bR (bR (sgOk3))))))
lemma s85 : Pol 32 1 128 104 table17 .up := signFast _ _ _ _ _ _ _ _ mx10_32_1_eq mx5_128_104_eq (bL (bR (bR (bR (sgOk3)))))
lemma s86 : Pol 64 2 128 105 table18 .down := signFast _ _ _ _ _ _ _ _ mx10_64_2_eq mx5_128_105_eq (bL (bR (bR (bR (bR (sgOk3))))))
lemma s87 : Pol 64 3 128 105 table17 .up := signFast _ _ _ _ _ _ _ _ mx10_64_3_eq mx5_128_105_eq (bR (bR (bR (bR (bR (sgOk3))))))
lemma s88 : Pol 16 0 64 53 table18 .down := signFast _ _ _ _ _ _ _ _ mx10_16_0_eq mx5_64_53_eq (bL (bL (bL (bL (sgOk4)))))
lemma s89 : Pol 32 0 64 53 table17 .down := signFast _ _ _ _ _ _ _ _ mx10_32_0_eq mx5_64_53_eq (bR (bL (bL (bL (sgOk4)))))
lemma s90 : Pol 32 0 64 53 table19 .down := signFast _ _ _ _ _ _ _ _ mx10_32_0_eq mx5_64_53_eq (bL (bR (bL (bL (sgOk4)))))
lemma s91 : Pol 32 1 64 53 table20 .up := signFast _ _ _ _ _ _ _ _ mx10_32_1_eq mx5_64_53_eq (bL (bR (bR (bL (bL (sgOk4))))))
lemma s92 : Pol 16 1 32 26 table20 .up := signFast _ _ _ _ _ _ _ _ mx10_16_1_eq mx5_32_26_eq (bR (bR (bR (bL (bL (sgOk4))))))
lemma s93 : Pol 16 1 64 52 table17 .up := signFast _ _ _ _ _ _ _ _ mx10_16_1_eq mx5_64_52_eq (bL (bL (bR (bL (sgOk4)))))
lemma s94 : Pol 16 1 64 52 table19 .up := signFast _ _ _ _ _ _ _ _ mx10_16_1_eq mx5_64_52_eq (bL (bR (bL (bR (bL (sgOk4))))))
lemma s95 : Pol 32 2 128 106 table17 .up := signFast _ _ _ _ _ _ _ _ mx10_32_2_eq mx5_128_106_eq (bR (bR (bL (bR (bL (sgOk4))))))
lemma s96 : Pol 64 4 128 107 table18 .down := signFast _ _ _ _ _ _ _ _ mx10_64_4_eq mx5_128_107_eq (bL (bR (bR (bL (sgOk4)))))
lemma s97 : Pol 64 5 128 107 table17 .up := signFast _ _ _ _ _ _ _ _ mx10_64_5_eq mx5_128_107_eq (bL (bR (bR (bR (bL (sgOk4))))))
lemma s98 : Pol 32 3 64 53 table17 .up := signFast _ _ _ _ _ _ _ _ mx10_32_3_eq mx5_64_53_eq (bR (bR (bR (bR (bL (sgOk4))))))
lemma s99 : Pol 32 3 64 53 table19 .up := signFast _ _ _ _ _ _ _ _ mx10_32_3_eq mx5_64_53_eq (bL (bL (bL (bR (sgOk4)))))
lemma s100 : Pol 16 0 32 27 table17 .down := signFast _ _ _ _ _ _ _ _ mx10_16_0_eq mx5_32_27_eq (bR (bL (bL (bR (sgOk4)))))
lemma s101 : Pol 16 0 32 27 table18 .down := signFast _ _ _ _ _ _ _ _ mx10_16_0_eq mx5_32_27_eq (bL (bR (bL (bR (sgOk4)))))
lemma s102 : Pol 16 0 32 27 table19 .down := signFast _ _ _ _ _ _ _ _ mx10_16_0_eq mx5_32_27_eq (bL (bR (bR (bL (bR (sgOk4))))))
lemma s103 : Pol 16 1 32 27 table16 .up := signFast _ _ _ _ _ _ _ _ mx10_16_1_eq mx5_32_27_eq (bR (bR (bR (bL (bR (sgOk4))))))
lemma s104 : Pol 16 1 64 54 table20 .up := signFast _ _ _ _ _ _ _ _ mx10_16_1_eq mx5_64_54_eq (bL (bL (bR (bR (sgOk4)))))
lemma s105 : Pol 32 2 64 54 table18 .down := signFast _ _ _ _ _ _ _ _ mx10_32_2_eq mx5_64_54_eq (bL (bR (bL (bR (bR (sgOk4))))))
lemma s106 : Pol 32 3 128 108 table17 .up := signFast _ _ _ _ _ _ _ _ mx10_32_3_eq mx5_128_108_eq (bR (bR (bL (bR (bR (sgOk4))))))
lemma s107 : Pol 64 6 128 109 table18 .down := signFast _ _ _ _ _ _ _ _ mx10_64_6_eq mx5_128_109_eq (bL (bR (bR (bR (sgOk4)))))
lemma s108 : Pol 64 7 128 109 table17 .up := signFast _ _ _ _ _ _ _ _ mx10_64_7_eq mx5_128_109_eq (bL (bR (bR (bR (bR (sgOk4))))))
lemma s109 : Pol 16 1 64 55 table18 .down := signFast _ _ _ _ _ _ _ _ mx10_16_1_eq mx5_64_55_eq (bR (bR (bR (bR (bR (sgOk4))))))
lemma s110 : Pol 32 2 64 55 table17 .down := signFast _ _ _ _ _ _ _ _ mx10_32_2_eq mx5_64_55_eq (bL (bL (bL (bL (sgOk5)))))
lemma s111 : Pol 32 2 64 55 table19 .down := signFast _ _ _ _ _ _ _ _ mx10_32_2_eq mx5_64_55_eq (bR (bL (bL (bL (sgOk5)))))
lemma s112 : Pol 32 3 64 55 table20 .up := signFast _ _ _ _ _ _ _ _ mx10_32_3_eq mx5_64_55_eq (bL (bR (bL (bL (sgOk5)))))
lemma s113 : Pol 8 0 8 7 table17 .down := signFast _ _ _ _ _ _ _ _ mx10_8_0_eq mx5_8_7_eq (bL (bR (bR (bL (bL (sgOk5))))))
lemma s114 : Pol 8 0 8 7 table18 .down := signFast _ _ _ _ _ _ _ _ mx10_8_0_eq mx5_8_7_eq (bR (bR (bR (bL (bL (sgOk5))))))
lemma s115 : Pol 8 0 8 7 table19 .down := signFast _ _ _ _ _ _ _ _ mx10_8_0_eq mx5_8_7_eq (bL (bL (bR (bL (sgOk5)))))
lemma s116 : Pol 8 0 16 14 table22 .up := signFast _ _ _ _ _ _ _ _ mx10_8_0_eq mx5_16_14_eq (bL (bR (bL (bR (bL (sgOk5))))))
lemma s117 : Pol 16 0 16 14 table20 .down := signFast _ _ _ _ _ _ _ _ mx10_16_0_eq mx5_16_14_eq (bR (bR (bL (bR (bL (sgOk5))))))
lemma s118 : Pol 16 1 16 14 table10 .down := signFast _ _ _ _ _ _ _ _ mx10_16_1_eq mx5_16_14_eq (bL (bR (bR (bL (sgOk5)))))
lemma s119 : Pol 16 1 32 28 table21 .up := signFast _ _ _ _ _ _ _ _ mx10_16_1_eq mx5_32_28_eq (bL (bR (bR (bR (bL (sgOk5))))))
lemma s120 : Pol 16 1 32 29 table20 .down := signFast _ _ _ _ _ _ _ _ mx10_16_1_eq mx5_32_29_eq (bR (bR (bR (bR (bL (sgOk5))))))
lemma s121 : Pol 8 0 16 15 table16 .down := signFast _ _ _ _ _ _ _ _ mx10_8_0_eq mx5_16_15_eq (bL (bL (bL (bR (sgOk5)))))
lemma s122 : Pol 8 0 16 15 table20 .down := signFast _ _ _ _ _ _ _ _ mx10_8_0_eq mx5_16_15_eq (bR (bL (bL (bR (sgOk5)))))
lemma s123 : Pol 8 0 32 30 table22 .up := signFast _ _ _ _ _ _ _ _ mx10_8_0_eq mx5_32_30_eq (bL (bR (bL (bR (sgOk5)))))
lemma s124 : Pol 8 0 32 31 table21 .down := signFast _ _ _ _ _ _ _ _ mx10_8_0_eq mx5_32_31_eq (bL (bR (bR (bL (bR (sgOk5))))))
lemma s125 : Pol 8 1 4 3 table10 .down := signFast _ _ _ _ _ _ _ _ mx10_8_1_eq mx5_4_3_eq (bR (bR (bR (bL (bR (sgOk5))))))
lemma s126 : Pol 8 1 4 3 table22 .up := signFast _ _ _ _ _ _ _ _ mx10_8_1_eq mx5_4_3_eq (bL (bL (bR (bR (sgOk5)))))
lemma s127 : Pol 8 1 8 6 table16 .up := signFast _ _ _ _ _ _ _ _ mx10_8_1_eq mx5_8_6_eq (bL (bR (bL (bR (bR (sgOk5))))))
lemma s128 : Pol 8 1 8 6 table20 .up := signFast _ _ _ _ _ _ _ _ mx10_8_1_eq mx5_8_6_eq (bR (bR (bL (bR (bR (sgOk5))))))
lemma s129 : Pol 8 1 8 6 table21 .up := signFast _ _ _ _ _ _ _ _ mx10_8_1_eq mx5_8_6_eq (bL (bR (bR (bR (sgOk5)))))
lemma s130 : Pol 16 2 8 6 table11 .up := signFast _ _ _ _ _ _ _ _ mx10_16_2_eq mx5_8_6_eq (bL (bR (bR (bR (bR (sgOk5))))))
lemma s131 : Pol 16 2 16 12 table17 .up := signFast _ _ _ _ _ _ _ _ mx10_16_2_eq mx5_16_12_eq (bR (bR (bR (bR (bR (sgOk5))))))
lemma s132 : Pol 16 2 16 12 table18 .up := signFast _ _ _ _ _ _ _ _ mx10_16_2_eq mx5_16_12_eq (bL (bL (bL (bL (sgOk6)))))
lemma s133 : Pol 16 2 16 12 table19 .up := signFast _ _ _ _ _ _ _ _ mx10_16_2_eq mx5_16_12_eq (bR (bL (bL (bL (sgOk6)))))
lemma s134 : Pol 16 2 32 26 table17 .up := signFast _ _ _ _ _ _ _ _ mx10_16_2_eq mx5_32_26_eq (bL (bR (bL (bL (sgOk6)))))
lemma s135 : Pol 16 2 32 26 table18 .up := signFast _ _ _ _ _ _ _ _ mx10_16_2_eq mx5_32_26_eq (bL (bR (bR (bL (bL (sgOk6))))))
lemma s136 : Pol 16 2 32 26 table19 .up := signFast _ _ _ _ _ _ _ _ mx10_16_2_eq mx5_32_26_eq (bR (bR (bR (bL (bL (sgOk6))))))
lemma s137 : Pol 16 2 64 54 table17 .up := signFast _ _ _ _ _ _ _ _ mx10_16_2_eq mx5_64_54_eq (bL (bL (bR (bL (sgOk6)))))
lemma s138 : Pol 16 2 64 54 table19 .up := signFast _ _ _ _ _ _ _ _ mx10_16_2_eq mx5_64_54_eq (bL (bR (bL (bR (bL (sgOk6))))))
lemma s139 : Pol 32 4 128 110 table17 .up := signFast _ _ _ _ _ _ _ _ mx10_32_4_eq mx5_128_110_eq (bR (bR (bL (bR (bL (sgOk6))))))
lemma s140 : Pol 64 8 128 111 table18 .down := signFast _ _ _ _ _ _ _ _ mx10_64_8_eq mx5_128_111_eq (bL (bR (bR (bL (sgOk6)))))
lemma s141 : Pol 64 9 128 111 table17 .up := signFast _ _ _ _ _ _ _ _ mx10_64_9_eq mx5_128_111_eq (bL (bR (bR (bR (bL (sgOk6))))))
lemma s142 : Pol 32 5 64 55 table17 .up := signFast _ _ _ _ _ _ _ _ mx10_32_5_eq mx5_64_55_eq (bR (bR (bR (bR (bL (sgOk6))))))
lemma s143 : Pol 32 5 64 55 table19 .up := signFast _ _ _ _ _ _ _ _ mx10_32_5_eq mx5_64_55_eq (bL (bL (bL (bR (sgOk6)))))
lemma s144 : Pol 16 3 8 6 table17 .up := signFast _ _ _ _ _ _ _ _ mx10_16_3_eq mx5_8_6_eq (bR (bL (bL (bR (sgOk6)))))
lemma s145 : Pol 16 3 8 6 table18 .up := signFast _ _ _ _ _ _ _ _ mx10_16_3_eq mx5_8_6_eq (bL (bR (bL (bR (sgOk6)))))
lemma s146 : Pol 16 3 8 6 table19 .up := signFast _ _ _ _ _ _ _ _ mx10_16_3_eq mx5_8_6_eq (bL (bR (bR (bL (bR (sgOk6))))))
lemma s147 : Pol 8 1 16 14 table21 .up := signFast _ _ _ _ _ _ _ _ mx10_8_1_eq mx5_16_14_eq (bR (bR (bR (bL (bR (sgOk6))))))
lemma s148 : Pol 16 2 16 14 table11 .up := signFast _ _ _ _ _ _ _ _ mx10_16_2_eq mx5_16_14_eq (bL (bL (bR (bR (sgOk6)))))
lemma s149 : Pol 16 2 32 28 table16 .up := signFast _ _ _ _ _ _ _ _ mx10_16_2_eq mx5_32_28_eq (bL (bR (bL (bR (bR (sgOk6))))))
lemma s150 : Pol 16 2 64 56 table20 .up := signFast _ _ _ _ _ _ _ _ mx10_16_2_eq mx5_64_56_eq (bR (bR (bL (bR (bR (sgOk6))))))
lemma s151 : Pol 32 4 64 56 table18 .down := signFast _ _ _ _ _ _ _ _ mx10_32_4_eq mx5_64_56_eq (bL (bR (bR (bR (sgOk6)))))
lemma s152 : Pol 32 5 128 112 table17 .up := signFast _ _ _ _ _ _ _ _ mx10_32_5_eq mx5_128_112_eq (bL (bR (bR (bR (bR (sgOk6))))))
lemma s153 : Pol 64 10 128 113 table18 .down := signFast _ _ _ _ _ _ _ _ mx10_64_10_eq mx5_128_113_eq (bR (bR (bR (bR (bR (sgOk6))))))
lemma s154 : Pol 64 11 256 226 table17 .up := signFast _ _ _ _ _ _ _ _ mx10_64_11_eq mx5_256_226_eq (bL (bL (bL (bL (sgOk7)))))
lemma s155 : Pol 64 11 256 226 table19 .up := signFast _ _ _ _ _ _ _ _ mx10_64_11_eq mx5_256_226_eq (bR (bL (bL (bL (sgOk7)))))
lemma s156 : Pol 64 11 256 227 table18 .down := signFast _ _ _ _ _ _ _ _ mx10_64_11_eq mx5_256_227_eq (bL (bR (bL (bL (sgOk7)))))
lemma s157 : Pol 16 2 64 57 table18 .down := signFast _ _ _ _ _ _ _ _ mx10_16_2_eq mx5_64_57_eq (bL (bR (bR (bL (bL (sgOk7))))))
lemma s158 : Pol 32 4 64 57 table17 .down := signFast _ _ _ _ _ _ _ _ mx10_32_4_eq mx5_64_57_eq (bR (bR (bR (bL (bL (sgOk7))))))
lemma s159 : Pol 32 4 64 57 table19 .down := signFast _ _ _ _ _ _ _ _ mx10_32_4_eq mx5_64_57_eq (bL (bL (bR (bL (sgOk7)))))
lemma s160 : Pol 32 5 64 57 table20 .up := signFast _ _ _ _ _ _ _ _ mx10_32_5_eq mx5_64_57_eq (bL (bR (bL (bR (bL (sgOk7))))))
lemma s161 : Pol 16 2 32 29 table17 .down := signFast _ _ _ _ _ _ _ _ mx10_16_2_eq mx5_32_29_eq (bR (bR (bL (bR (bL (sgOk7))))))
lemma s162 : Pol 16 2 32 29 table18 .down := signFast _ _ _ _ _ _ _ _ mx10_16_2_eq mx5_32_29_eq (bL (bR (bR (bL (sgOk7)))))
lemma s163 : Pol 16 2 32 29 table19 .down := signFast _ _ _ _ _ _ _ _ mx10_16_2_eq mx5_32_29_eq (bL (bR (bR (bR (bL (sgOk7))))))
lemma s164 : Pol 16 3 16 14 table16 .up := signFast _ _ _ _ _ _ _ _ mx10_16_3_eq mx5_16_14_eq (bR (bR (bR (bR (bL (sgOk7))))))
lemma s165 : Pol 16 3 16 14 table20 .up := signFast _ _ _ _ _ _ _ _ mx10_16_3_eq mx5_16_14_eq (bL (bL (bL (bR (sgOk7)))))
lemma s166 : Pol 32 6 16 14 table11 .up := signFast _ _ _ _ _ _ _ _ mx10_32_6_eq mx5_16_14_eq (bR (bL (bL (bR (sgOk7)))))
lemma s167 : Pol 32 6 64 56 table17 .up := signFast _ _ _ _ _ _ _ _ mx10_32_6_eq mx5_64_56_eq (bL (bR (bL (bR (sgOk7)))))
lemma s168 : Pol 32 6 64 56 table19 .up := signFast _ _ _ _ _ _ _ _ mx10_32_6_eq mx5_64_56_eq (bL (bR (bR (bL (bR (sgOk7))))))
lemma s169 : Pol 32 6 128 114 table19 .up := signFast _ _ _ _ _ _ _ _ mx10_32_6_eq mx5_128_114_eq (bR (bR (bR (bL (bR (sgOk7))))))
lemma s170 : Pol 32 6 128 115 table18 .down := signFast _ _ _ _ _ _ _ _ mx10_32_6_eq mx5_128_115_eq (bL (bL (bR (bR (sgOk7)))))
lemma s171 : Pol 32 6 32 29 table18 .down := signFast _ _ _ _ _ _ _ _ mx10_32_6_eq mx5_32_29_eq (bL (bR (bL (bR (bR (sgOk7))))))
lemma s172 : Pol 32 7 32 28 table17 .up := signFast _ _ _ _ _ _ _ _ mx10_32_7_eq mx5_32_28_eq (bR (bR (bL (bR (bR (sgOk7))))))
lemma s173 : Pol 32 7 32 28 table19 .up := signFast _ _ _ _ _ _ _ _ mx10_32_7_eq mx5_32_28_eq (bL (bR (bR (bR (sgOk7)))))
lemma s174 : Pol 64 14 32 29 table11 .up := signFast _ _ _ _ _ _ _ _ mx10_64_14_eq mx5_32_29_eq (bL (bR (bR (bR (bR (sgOk7))))))
lemma s175 : Pol 64 14 32 29 table18 .down := signFast _ _ _ _ _ _ _ _ mx10_64_14_eq mx5_32_29_eq (bR (bR (bR (bR (bR (sgOk7))))))
lemma s176 : Pol 64 15 64 58 table19 .up := signFast _ _ _ _ _ _ _ _ mx10_64_15_eq mx5_64_58_eq (bL (bL (bL (bL (sgOk8)))))
lemma s177 : Pol 64 15 64 59 table17 .down := signFast _ _ _ _ _ _ _ _ mx10_64_15_eq mx5_64_59_eq (bR (bL (bL (bL (sgOk8)))))
lemma s178 : Pol 64 15 64 59 table18 .down := signFast _ _ _ _ _ _ _ _ mx10_64_15_eq mx5_64_59_eq (bL (bR (bL (bL (sgOk8)))))
lemma s179 : Pol 8 1 16 15 table17 .down := signFast _ _ _ _ _ _ _ _ mx10_8_1_eq mx5_16_15_eq (bL (bR (bR (bL (bL (sgOk8))))))
lemma s180 : Pol 8 1 16 15 table18 .down := signFast _ _ _ _ _ _ _ _ mx10_8_1_eq mx5_16_15_eq (bR (bR (bR (bL (bL (sgOk8))))))
lemma s181 : Pol 8 1 16 15 table19 .down := signFast _ _ _ _ _ _ _ _ mx10_8_1_eq mx5_16_15_eq (bL (bL (bR (bL (sgOk8)))))
lemma s182 : Pol 16 2 16 15 table11 .up := signFast _ _ _ _ _ _ _ _ mx10_16_2_eq mx5_16_15_eq (bL (bR (bL (bR (bL (sgOk8))))))
lemma s183 : Pol 32 4 16 15 table16 .down := signFast _ _ _ _ _ _ _ _ mx10_32_4_eq mx5_16_15_eq (bR (bR (bL (bR (bL (sgOk8))))))
lemma s184 : Pol 32 4 16 15 table20 .down := signFast _ _ _ _ _ _ _ _ mx10_32_4_eq mx5_16_15_eq (bL (bR (bR (bL (sgOk8)))))
lemma s185 : Pol 32 5 32 30 table21 .up := signFast _ _ _ _ _ _ _ _ mx10_32_5_eq mx5_32_30_eq (bL (bR (bR (bR (bL (sgOk8))))))
lemma s186 : Pol 32 5 32 31 table16 .down := signFast _ _ _ _ _ _ _ _ mx10_32_5_eq mx5_32_31_eq (bR (bR (bR (bR (bL (sgOk8))))))
lemma s187 : Pol 32 5 32 31 table20 .down := signFast _ _ _ _ _ _ _ _ mx10_32_5_eq mx5_32_31_eq (bL (bL (bL (bR (sgOk8)))))
lemma s188 : Pol 16 3 16 15 table21 .up := signFast _ _ _ _ _ _ _ _ mx10_16_3_eq mx5_16_15_eq (bR (bL (bL (bR (sgOk8)))))
lemma s189 : Pol 4 1 4 3 table10 .down := signFast _ _ _ _ _ _ _ _ mx10_4_1_eq mx5_4_3_eq (bL (bR (bL (bR (sgOk8)))))
lemma s190 : Pol 4 1 4 3 table21 .up := signFast _ _ _ _ _ _ _ _ mx10_4_1_eq mx5_4_3_eq (bL (bR (bR (bL (bR (sgOk8))))))
lemma s191 : Pol 4 1 4 3 table22 .up := signFast _ _ _ _ _ _ _ _ mx10_4_1_eq mx5_4_3_eq (bR (bR (bR (bL (bR (sgOk8))))))
lemma s192 : Pol 8 2 4 3 table5 .up := signFast _ _ _ _ _ _ _ _ mx10_8_2_eq mx5_4_3_eq (bL (bL (bR (bR (sgOk8)))))
lemma s193 : Pol 8 2 8 6 table11 .down := signFast _ _ _ _ _ _ _ _ mx10_8_2_eq mx5_8_6_eq (bL (bR (bL (bR (bR (sgOk8))))))
lemma s194 : Pol 8 2 8 6 table14 .up := signFast _ _ _ _ _ _ _ _ mx10_8_2_eq mx5_8_6_eq (bR (bR (bL (bR (bR (sgOk8))))))
lemma s195 : Pol 8 2 8 6 table15 .up := signFast _ _ _ _ _ _ _ _ mx10_8_2_eq mx5_8_6_eq (bL (bR (bR (bR (sgOk8)))))
lemma s196 : Pol 8 2 8 6 table16 .up := signFast _ _ _ _ _ _ _ _ mx10_8_2_eq mx5_8_6_eq (bL (bR (bR (bR (bR (sgOk8))))))
lemma s197 : Pol 8 2 8 6 table17 .up := signFast _ _ _ _ _ _ _ _ mx10_8_2_eq mx5_8_6_eq (bR (bR (bR (bR (bR (sgOk8))))))
lemma s198 : Pol 8 2 8 6 table18 .up := signFast _ _ _ _ _ _ _ _ mx10_8_2_eq mx5_8_6_eq (bL (bL (bL (bL (sgOk9)))))
lemma s199 : Pol 8 2 8 6 table19 .up := signFast _ _ _ _ _ _ _ _ mx10_8_2_eq mx5_8_6_eq (bR (bL (bL (bL (sgOk9)))))
lemma s200 : Pol 8 2 8 6 table20 .up := signFast _ _ _ _ _ _ _ _ mx10_8_2_eq mx5_8_6_eq (bL (bR (bL (bL (sgOk9)))))
lemma s201 : Pol 16 4 8 7 table13 .up := signFast _ _ _ _ _ _ _ _ mx10_16_4_eq mx5_8_7_eq (bL (bR (bR (bL (bL (sgOk9))))))
lemma s202 : Pol 16 4 8 7 table14 .up := signFast _ _ _ _ _ _ _ _ mx10_16_4_eq mx5_8_7_eq (bR (bR (bR (bL (bL (sgOk9))))))
lemma s203 : Pol 16 4 8 7 table15 .up := signFast _ _ _ _ _ _ _ _ mx10_16_4_eq mx5_8_7_eq (bL (bL (bR (bL (sgOk9)))))
lemma s204 : Pol 16 4 16 14 table11 .down := signFast _ _ _ _ _ _ _ _ mx10_16_4_eq mx5_16_14_eq (bL (bR (bL (bR (bL (sgOk9))))))
lemma s205 : Pol 16 4 16 14 table16 .up := signFast _ _ _ _ _ _ _ _ mx10_16_4_eq mx5_16_14_eq (bR (bR (bL (bR (bL (sgOk9))))))
lemma s206 : Pol 16 4 16 14 table20 .up := signFast _ _ _ _ _ _ _ _ mx10_16_4_eq mx5_16_14_eq (bL (bR (bR (bL (sgOk9)))))
lemma s207 : Pol 16 4 32 28 table17 .up := signFast _ _ _ _ _ _ _ _ mx10_16_4_eq mx5_32_28_eq (bL (bR (bR (bR (bL (sgOk9))))))
lemma s208 : Pol 16 4 32 28 table18 .up := signFast _ _ _ _ _ _ _ _ mx10_16_4_eq mx5_32_28_eq (bR (bR (bR (bR (bL (sgOk9))))))
lemma s209 : Pol 16 4 32 28 table19 .up := signFast _ _ _ _ _ _ _ _ mx10_16_4_eq mx5_32_28_eq (bL (bL (bL (bR (sgOk9)))))
lemma s210 : Pol 16 4 32 29 table12 .up := signFast _ _ _ _ _ _ _ _ mx10_16_4_eq mx5_32_29_eq (bR (bL (bL (bR (sgOk9)))))
lemma s211 : Pol 16 4 64 58 table19 .up := signFast _ _ _ _ _ _ _ _ mx10_16_4_eq mx5_64_58_eq (bL (bR (bL (bR (sgOk9)))))
lemma s212 : Pol 32 8 128 118 table19 .up := signFast _ _ _ _ _ _ _ _ mx10_32_8_eq mx5_128_118_eq (bL (bR (bR (bL (bR (sgOk9))))))
lemma s213 : Pol 32 8 128 119 table17 .down := signFast _ _ _ _ _ _ _ _ mx10_32_8_eq mx5_128_119_eq (bR (bR (bR (bL (bR (sgOk9))))))
lemma s214 : Pol 32 8 128 119 table18 .down := signFast _ _ _ _ _ _ _ _ mx10_32_8_eq mx5_128_119_eq (bL (bL (bR (bR (sgOk9)))))
lemma s215 : Pol 32 9 64 59 table19 .up := signFast _ _ _ _ _ _ _ _ mx10_32_9_eq mx5_64_59_eq (bL (bR (bL (bR (bR (sgOk9))))))
lemma s216 : Pol 16 4 16 15 table12 .up := signFast _ _ _ _ _ _ _ _ mx10_16_4_eq mx5_16_15_eq (bR (bR (bL (bR (bR (sgOk9))))))
lemma s217 : Pol 16 4 16 15 table17 .down := signFast _ _ _ _ _ _ _ _ mx10_16_4_eq mx5_16_15_eq (bL (bR (bR (bR (sgOk9)))))
lemma s218 : Pol 16 4 32 30 table20 .up := signFast _ _ _ _ _ _ _ _ mx10_16_4_eq mx5_32_30_eq (bL (bR (bR (bR (bR (sgOk9))))))
lemma s219 : Pol 16 4 64 60 table11 .down := signFast _ _ _ _ _ _ _ _ mx10_16_4_eq mx5_64_60_eq (bR (bR (bR (bR (bR (sgOk9))))))
lemma s220 : Pol 16 4 64 60 table16 .up := signFast _ _ _ _ _ _ _ _ mx10_16_4_eq mx5_64_60_eq (bL (bL (bL (bL (sgOk10)))))
lemma s221 : Pol 32 8 64 60 table18 .down := signFast _ _ _ _ _ _ _ _ mx10_32_8_eq mx5_64_60_eq (bR (bL (bL (bL (sgOk10)))))
lemma s222 : Pol 32 9 128 120 table19 .up := signFast _ _ _ _ _ _ _ _ mx10_32_9_eq mx5_128_120_eq (bL (bR (bL (bL (sgOk10)))))
lemma s223 : Pol 32 9 128 121 table18 .down := signFast _ _ _ _ _ _ _ _ mx10_32_9_eq mx5_128_121_eq (bL (bR (bR (bL (bL (sgOk10))))))
lemma s224 : Pol 16 4 64 61 table18 .down := signFast _ _ _ _ _ _ _ _ mx10_16_4_eq mx5_64_61_eq (bR (bR (bR (bL (bL (sgOk10))))))
lemma s225 : Pol 16 4 32 31 table16 .down := signFast _ _ _ _ _ _ _ _ mx10_16_4_eq mx5_32_31_eq (bL (bL (bR (bL (sgOk10)))))
lemma s226 : Pol 16 4 32 31 table18 .down := signFast _ _ _ _ _ _ _ _ mx10_16_4_eq mx5_32_31_eq (bL (bR (bL (bR (bL (sgOk10))))))
lemma s227 : Pol 16 4 32 31 table19 .down := signFast _ _ _ _ _ _ _ _ mx10_16_4_eq mx5_32_31_eq (bR (bR (bL (bR (bL (sgOk10))))))
lemma s228 : Pol 16 5 8 7 table11 .down := signFast _ _ _ _ _ _ _ _ mx10_16_5_eq mx5_8_7_eq (bL (bR (bR (bL (sgOk10)))))
lemma s229 : Pol 16 5 8 7 table20 .up := signFast _ _ _ _ _ _ _ _ mx10_16_5_eq mx5_8_7_eq (bL (bR (bR (bR (bL (sgOk10))))))
lemma s230 : Pol 32 10 8 7 table13 .up := signFast _ _ _ _ _ _ _ _ mx10_32_10_eq mx5_8_7_eq (bR (bR (bR (bR (bL (sgOk10))))))
lemma s231 : Pol 32 10 8 7 table14 .up := signFast _ _ _ _ _ _ _ _ mx10_32_10_eq mx5_8_7_eq (bL (bL (bL (bR (sgOk10)))))
lemma s232 : Pol 32 10 8 7 table15 .up := signFast _ _ _ _ _ _ _ _ mx10_32_10_eq mx5_8_7_eq (bR (bL (bL (bR (sgOk10)))))
lemma s233 : Pol 32 10 16 14 table16 .up := signFast _ _ _ _ _ _ _ _ mx10_32_10_eq mx5_16_14_eq (bL (bR (bL (bR (sgOk10)))))
lemma s234 : Pol 32 10 16 14 table18 .up := signFast _ _ _ _ _ _ _ _ mx10_32_10_eq mx5_16_14_eq (bL (bR (bR (bL (bR (sgOk10))))))
lemma s235 : Pol 32 10 16 14 table19 .up := signFast _ _ _ _ _ _ _ _ mx10_32_10_eq mx5_16_14_eq (bR (bR (bR (bL (bR (sgOk10))))))
lemma s236 : Pol 32 10 64 60 table16 .up := signFast _ _ _ _ _ _ _ _ mx10_32_10_eq mx5_64_60_eq (bL (bL (bR (bR (sgOk10)))))
lemma s237 : Pol 32 10 64 60 table19 .up := signFast _ _ _ _ _ _ _ _ mx10_32_10_eq mx5_64_60_eq (bL (bR (bL (bR (bR (sgOk10))))))
lemma s238 : Pol 32 10 64 61 table17 .down := signFast _ _ _ _ _ _ _ _ mx10_32_10_eq mx5_64_61_eq (bR (bR (bL (bR (bR (sgOk10))))))
lemma s239 : Pol 32 10 64 61 table18 .down := signFast _ _ _ _ _ _ _ _ mx10_32_10_eq mx5_64_61_eq (bL (bR (bR (bR (sgOk10)))))
lemma s240 : Pol 32 10 32 31 table16 .down := signFast _ _ _ _ _ _ _ _ mx10_32_10_eq mx5_32_31_eq (bL (bR (bR (bR (bR (sgOk10))))))
lemma s241 : Pol 32 10 32 31 table17 .down := signFast _ _ _ _ _ _ _ _ mx10_32_10_eq mx5_32_31_eq (bR (bR (bR (bR (bR (sgOk10))))))
lemma s242 : Pol 32 10 32 31 table18 .down := signFast _ _ _ _ _ _ _ _ mx10_32_10_eq mx5_32_31_eq (bL (bL (bL (bL (sgOk11)))))
lemma s243 : Pol 32 11 8 7 table12 .down := signFast _ _ _ _ _ _ _ _ mx10_32_11_eq mx5_8_7_eq (bR (bL (bL (bL (sgOk11)))))
lemma s244 : Pol 32 11 16 14 table14 .up := signFast _ _ _ _ _ _ _ _ mx10_32_11_eq mx5_16_14_eq (bL (bR (bL (bL (sgOk11)))))
lemma s245 : Pol 32 11 16 14 table15 .up := signFast _ _ _ _ _ _ _ _ mx10_32_11_eq mx5_16_14_eq (bL (bR (bR (bL (bL (sgOk11))))))
lemma s246 : Pol 32 11 16 14 table16 .up := signFast _ _ _ _ _ _ _ _ mx10_32_11_eq mx5_16_14_eq (bR (bR (bR (bL (bL (sgOk11))))))
lemma s247 : Pol 32 11 16 14 table17 .up := signFast _ _ _ _ _ _ _ _ mx10_32_11_eq mx5_16_14_eq (bL (bL (bR (bL (sgOk11)))))
lemma s248 : Pol 32 11 16 14 table18 .up := signFast _ _ _ _ _ _ _ _ mx10_32_11_eq mx5_16_14_eq (bL (bR (bL (bR (bL (sgOk11))))))
lemma s249 : Pol 32 11 16 14 table19 .up := signFast _ _ _ _ _ _ _ _ mx10_32_11_eq mx5_16_14_eq (bR (bR (bL (bR (bL (sgOk11))))))
lemma s250 : Pol 32 11 32 30 table14 .up := signFast _ _ _ _ _ _ _ _ mx10_32_11_eq mx5_32_30_eq (bL (bR (bR (bL (sgOk11)))))
lemma s251 : Pol 32 11 32 30 table19 .up := signFast _ _ _ _ _ _ _ _ mx10_32_11_eq mx5_32_30_eq (bL (bR (bR (bR (bL (sgOk11))))))
lemma s252 : Pol 64 22 32 30 table13 .up := signFast _ _ _ _ _ _ _ _ mx10_64_22_eq mx5_32_30_eq (bR (bR (bR (bR (bL (sgOk11))))))
lemma s253 : Pol 64 22 32 30 table15 .up := signFast _ _ _ _ _ _ _ _ mx10_64_22_eq mx5_32_30_eq (bL (bL (bL (bR (sgOk11)))))
lemma s254 : Pol 64 22 128 120 table16 .up := signFast _ _ _ _ _ _ _ _ mx10_64_22_eq mx5_128_120_eq (bR (bL (bL (bR (sgOk11)))))
lemma s255 : Pol 64 22 128 120 table18 .up := signFast _ _ _ _ _ _ _ _ mx10_64_22_eq mx5_128_120_eq (bL (bR (bL (bR (sgOk11)))))
lemma s256 : Pol 64 22 128 121 table17 .down := signFast _ _ _ _ _ _ _ _ mx10_64_22_eq mx5_128_121_eq (bL (bR (bR (bL (bR (sgOk11))))))
lemma s257 : Pol 64 22 64 61 table17 .down := signFast _ _ _ _ _ _ _ _ mx10_64_22_eq mx5_64_61_eq (bR (bR (bR (bL (bR (sgOk11))))))
lemma s258 : Pol 64 23 64 60 table15 .up := signFast _ _ _ _ _ _ _ _ mx10_64_23_eq mx5_64_60_eq (bL (bL (bR (bR (sgOk11)))))
lemma s259 : Pol 64 23 64 60 table18 .up := signFast _ _ _ _ _ _ _ _ mx10_64_23_eq mx5_64_60_eq (bL (bR (bL (bR (bR (sgOk11))))))
lemma s260 : Pol 64 23 64 61 table16 .down := signFast _ _ _ _ _ _ _ _ mx10_64_23_eq mx5_64_61_eq (bR (bR (bL (bR (bR (sgOk11))))))
lemma s261 : Pol 64 23 64 61 table17 .down := signFast _ _ _ _ _ _ _ _ mx10_64_23_eq mx5_64_61_eq (bL (bR (bR (bR (sgOk11)))))
lemma s262 : Pol 32 11 32 31 table16 .down := signFast _ _ _ _ _ _ _ _ mx10_32_11_eq mx5_32_31_eq (bL (bR (bR (bR (bR (sgOk11))))))
lemma s263 : Pol 32 11 32 31 table17 .down := signFast _ _ _ _ _ _ _ _ mx10_32_11_eq mx5_32_31_eq (bR (bR (bR (bR (bR (sgOk11))))))
lemma s264 : Pol 32 11 32 31 table18 .down := signFast _ _ _ _ _ _ _ _ mx10_32_11_eq mx5_32_31_eq (bL (bL (bL (bL (sgOk12)))))
lemma s265 : Pol 64 22 32 31 table13 .up := signFast _ _ _ _ _ _ _ _ mx10_64_22_eq mx5_32_31_eq (bR (bL (bL (bL (sgOk12)))))
lemma s266 : Pol 64 22 32 31 table14 .up := signFast _ _ _ _ _ _ _ _ mx10_64_22_eq mx5_32_31_eq (bL (bR (bL (bL (sgOk12)))))
lemma s267 : Pol 128 46 32 31 table14 .up := signFast _ _ _ _ _ _ _ _ mx10_128_46_eq mx5_32_31_eq (bL (bR (bR (bL (bL (sgOk12))))))
lemma s268 : Pol 128 47 32 31 table13 .down := signFast _ _ _ _ _ _ _ _ mx10_128_47_eq mx5_32_31_eq (bR (bR (bR (bL (bL (sgOk12))))))
lemma s269 : Pol 128 47 32 31 table19 .up := signFast _ _ _ _ _ _ _ _ mx10_128_47_eq mx5_32_31_eq (bL (bL (bR (bL (sgOk12)))))
lemma s270 : Pol 8 3 4 3 table11 .down := signFast _ _ _ _ _ _ _ _ mx10_8_3_eq mx5_4_3_eq (bL (bR (bL (bR (bL (sgOk12))))))
lemma s271 : Pol 8 3 4 3 table12 .down := signFast _ _ _ _ _ _ _ _ mx10_8_3_eq mx5_4_3_eq (bR (bR (bL (bR (bL (sgOk12))))))
lemma s272 : Pol 8 3 4 3 table13 .down := signFast _ _ _ _ _ _ _ _ mx10_8_3_eq mx5_4_3_eq (bL (bR (bR (bL (sgOk12)))))
lemma s273 : Pol 8 3 4 3 table19 .up := signFast _ _ _ _ _ _ _ _ mx10_8_3_eq mx5_4_3_eq (bL (bR (bR (bR (bL (sgOk12))))))
lemma s274 : Pol 8 3 4 3 table20 .up := signFast _ _ _ _ _ _ _ _ mx10_8_3_eq mx5_4_3_eq (bR (bR (bR (bR (bL (sgOk12))))))
lemma s275 : Pol 8 3 8 6 table17 .up := signFast _ _ _ _ _ _ _ _ mx10_8_3_eq mx5_8_6_eq (bL (bL (bL (bR (sgOk12)))))
lemma s276 : Pol 8 3 8 6 table18 .up := signFast _ _ _ _ _ _ _ _ mx10_8_3_eq mx5_8_6_eq (bR (bL (bL (bR (sgOk12)))))
lemma s277 : Pol 16 6 16 14 table17 .up := signFast _ _ _ _ _ _ _ _ mx10_16_6_eq mx5_16_14_eq (bL (bR (bL (bR (sgOk12)))))
lemma s278 : Pol 16 6 16 14 table18 .up := signFast _ _ _ _ _ _ _ _ mx10_16_6_eq mx5_16_14_eq (bL (bR (bR (bL (bR (sgOk12))))))
lemma s279 : Pol 16 6 64 60 table18 .up := signFast _ _ _ _ _ _ _ _ mx10_16_6_eq mx5_64_60_eq (bR (bR (bR (bL (bR (sgOk12))))))
lemma s280 : Pol 64 24 64 60 table5 .up := signFast _ _ _ _ _ _ _ _ mx10_64_24_eq mx5_64_60_eq (bL (bL (bR (bR (sgOk12)))))
lemma s281 : Pol 128 48 64 60 table14 .up := signFast _ _ _ _ _ _ _ _ mx10_128_48_eq mx5_64_60_eq (bL (bR (bL (bR (bR (sgOk12))))))
lemma s282 : Pol 128 48 64 60 table15 .up := signFast _ _ _ _ _ _ _ _ mx10_128_48_eq mx5_64_60_eq (bR (bR (bL (bR (bR (sgOk12))))))
lemma s283 : Pol 128 49 128 120 table15 .up := signFast _ _ _ _ _ _ _ _ mx10_128_49_eq mx5_128_120_eq (bL (bR (bR (bR (sgOk12)))))
lemma s284 : Pol 128 49 128 120 table17 .up := signFast _ _ _ _ _ _ _ _ mx10_128_49_eq mx5_128_120_eq (bL (bR (bR (bR (bR (sgOk12))))))
lemma s285 : Pol 256 98 256 242 table15 .up := signFast _ _ _ _ _ _ _ _ mx10_256_98_eq mx5_256_242_eq (bR (bR (bR (bR (bR (sgOk12))))))
lemma s286 : Pol 256 98 256 243 table16 .down := signFast _ _ _ _ _ _ _ _ mx10_256_98_eq mx5_256_243_eq (bL (bL (bL (bL (sgOk13)))))
lemma s287 : Pol 256 98 256 243 table17 .down := signFast _ _ _ _ _ _ _ _ mx10_256_98_eq mx5_256_243_eq (bR (bL (bL (bL (sgOk13)))))
lemma s288 : Pol 256 99 128 121 table14 .down := signFast _ _ _ _ _ _ _ _ mx10_256_99_eq mx5_128_121_eq (bL (bR (bL (bL (sgOk13)))))
lemma s289 : Pol 256 99 128 121 table16 .down := signFast _ _ _ _ _ _ _ _ mx10_256_99_eq mx5_128_121_eq (bL (bR (bR (bL (bL (sgOk13))))))
lemma s290 : Pol 64 25 64 60 table14 .down := signFast _ _ _ _ _ _ _ _ mx10_64_25_eq mx5_64_60_eq (bR (bR (bR (bL (bL (sgOk13))))))
lemma s291 : Pol 32 13 64 60 table5 .down := signFast _ _ _ _ _ _ _ _ mx10_32_13_eq mx5_64_60_eq (bL (bL (bR (bL (sgOk13)))))
lemma s292 : Pol 32 13 64 60 table14 .down := signFast _ _ _ _ _ _ _ _ mx10_32_13_eq mx5_64_60_eq (bL (bR (bL (bR (bL (sgOk13))))))
lemma s293 : Pol 32 13 64 60 table15 .down := signFast _ _ _ _ _ _ _ _ mx10_32_13_eq mx5_64_60_eq (bR (bR (bL (bR (bL (sgOk13))))))
lemma s294 : Pol 16 6 64 61 table16 .down := signFast _ _ _ _ _ _ _ _ mx10_16_6_eq mx5_64_61_eq (bL (bR (bR (bL (sgOk13)))))
lemma s295 : Pol 16 6 64 61 table17 .down := signFast _ _ _ _ _ _ _ _ mx10_16_6_eq mx5_64_61_eq (bL (bR (bR (bR (bL (sgOk13))))))
lemma s296 : Pol 16 6 32 31 table15 .down := signFast _ _ _ _ _ _ _ _ mx10_16_6_eq mx5_32_31_eq (bR (bR (bR (bR (bL (sgOk13))))))
lemma s297 : Pol 16 6 32 31 table16 .down := signFast _ _ _ _ _ _ _ _ mx10_16_6_eq mx5_32_31_eq (bL (bL (bL (bR (sgOk13)))))
lemma s298 : Pol 16 6 32 31 table17 .down := signFast _ _ _ _ _ _ _ _ mx10_16_6_eq mx5_32_31_eq (bR (bL (bL (bR (sgOk13)))))
lemma s299 : Pol 16 7 8 7 table5 .down := signFast _ _ _ _ _ _ _ _ mx10_16_7_eq mx5_8_7_eq (bL (bR (bL (bR (sgOk13)))))
lemma s300 : Pol 16 7 8 7 table14 .down := signFast _ _ _ _ _ _ _ _ mx10_16_7_eq mx5_8_7_eq (bL (bR (bR (bL (bR (sgOk13))))))
lemma s301 : Pol 16 7 8 7 table15 .down := signFast _ _ _ _ _ _ _ _ mx10_16_7_eq mx5_8_7_eq (bR (bR (bR (bL (bR (sgOk13))))))
lemma s302 : Pol 2 1 1 0 table5 .down := signFast _ _ _ _ _ _ _ _ mx10_2_1_eq mx5_1_0_eq (bL (bL (bR (bR (sgOk13)))))
lemma s303 : Pol 2 1 1 0 table6 .down := signFast _ _ _ _ _ _ _ _ mx10_2_1_eq mx5_1_0_eq (bL (bR (bL (bR (bR (sgOk13))))))
lemma s304 : Pol 2 1 1 0 table10 .down := signFast _ _ _ _ _ _ _ _ mx10_2_1_eq mx5_1_0_eq (bR (bR (bL (bR (bR (sgOk13))))))
lemma s305 : Pol 2 1 1 0 table11 .down := signFast _ _ _ _ _ _ _ _ mx10_2_1_eq mx5_1_0_eq (bL (bR (bR (bR (sgOk13)))))
lemma s306 : Pol 2 1 1 0 table12 .down := signFast _ _ _ _ _ _ _ _ mx10_2_1_eq mx5_1_0_eq (bL (bR (bR (bR (bR (sgOk13))))))
lemma s307 : Pol 2 1 1 0 table13 .down := signFast _ _ _ _ _ _ _ _ mx10_2_1_eq mx5_1_0_eq (bR (bR (bR (bR (bR (sgOk13))))))
lemma s308 : Pol 2 1 1 0 table19 .up := signFast _ _ _ _ _ _ _ _ mx10_2_1_eq mx5_1_0_eq (bL (bL (bL (bL (sgOk14)))))
lemma s309 : Pol 2 1 1 0 table20 .up := signFast _ _ _ _ _ _ _ _ mx10_2_1_eq mx5_1_0_eq (bR (bL (bL (bL (sgOk14)))))
lemma s310 : Pol 2 1 1 0 table21 .up := signFast _ _ _ _ _ _ _ _ mx10_2_1_eq mx5_1_0_eq (bL (bR (bL (bL (sgOk14)))))
lemma s311 : Pol 2 1 1 0 table22 .up := signFast _ _ _ _ _ _ _ _ mx10_2_1_eq mx5_1_0_eq (bL (bR (bR (bL (bL (sgOk14))))))
lemma s312 : Pol 4 2 1 0 table18 .up := signFast _ _ _ _ _ _ _ _ mx10_4_2_eq mx5_1_0_eq (bR (bR (bR (bL (bL (sgOk14))))))
lemma s313 : Pol 4 2 2 0 table17 .up := signFast _ _ _ _ _ _ _ _ mx10_4_2_eq mx5_2_0_eq (bL (bL (bR (bL (sgOk14)))))
lemma s314 : Pol 8 4 2 0 table2 .up := signFast _ _ _ _ _ _ _ _ mx10_8_4_eq mx5_2_0_eq (bL (bR (bL (bR (bL (sgOk14))))))
lemma s315 : Pol 8 4 2 0 table16 .up := signFast _ _ _ _ _ _ _ _ mx10_8_4_eq mx5_2_0_eq (bR (bR (bL (bR (bL (sgOk14))))))
lemma s316 : Pol 32 16 2 0 table3 .up := signFast _ _ _ _ _ _ _ _ mx10_32_16_eq mx5_2_0_eq (bL (bR (bR (bL (sgOk14)))))
lemma s317 : Pol 32 16 2 0 table15 .up := signFast _ _ _ _ _ _ _ _ mx10_32_16_eq mx5_2_0_eq (bL (bR (bR (bR (bL (sgOk14))))))
lemma s318 : Pol 32 17 2 0 table14 .down := signFast _ _ _ _ _ _ _ _ mx10_32_17_eq mx5_2_0_eq (bR (bR (bR (bR (bL (sgOk14))))))
lemma s319 : Pol 16 9 2 0 table14 .down := signFast _ _ _ _ _ _ _ _ mx10_16_9_eq mx5_2_0_eq (bL (bL (bL (bR (sgOk14)))))
lemma s320 : Pol 8 5 2 0 table4 .down := signFast _ _ _ _ _ _ _ _ mx10_8_5_eq mx5_2_0_eq (bR (bL (bL (bR (sgOk14)))))
lemma s321 : Pol 8 5 2 0 table14 .down := signFast _ _ _ _ _ _ _ _ mx10_8_5_eq mx5_2_0_eq (bL (bR (bL (bR (sgOk14)))))
lemma s322 : Pol 16 10 2 0 table2 .up := signFast _ _ _ _ _ _ _ _ mx10_16_10_eq mx5_2_0_eq (bL (bR (bR (bL (bR (sgOk14))))))
lemma s323 : Pol 16 11 2 0 table15 .down := signFast _ _ _ _ _ _ _ _ mx10_16_11_eq mx5_2_0_eq (bR (bR (bR (bL (bR (sgOk14))))))
lemma s324 : Pol 4 2 2 1 table2 .up := signFast _ _ _ _ _ _ _ _ mx10_4_2_eq mx5_2_1_eq (bL (bL (bR (bR (sgOk14)))))
lemma s325 : Pol 4 2 2 1 table3 .up := signFast _ _ _ _ _ _ _ _ mx10_4_2_eq mx5_2_1_eq (bL (bR (bL (bR (bR (sgOk14))))))
lemma s326 : Pol 4 2 2 1 table14 .down := signFast _ _ _ _ _ _ _ _ mx10_4_2_eq mx5_2_1_eq (bR (bR (bL (bR (bR (sgOk14))))))
lemma s327 : Pol 4 3 1 0 table4 .down := signFast _ _ _ _ _ _ _ _ mx10_4_3_eq mx5_1_0_eq (bL (bR (bR (bR (sgOk14)))))
lemma s328 : Pol 4 3 1 0 table14 .down := signFast _ _ _ _ _ _ _ _ mx10_4_3_eq mx5_1_0_eq (bL (bR (bR (bR (bR (sgOk14))))))
lemma s329 : Pol 4 3 1 0 table15 .down := signFast _ _ _ _ _ _ _ _ mx10_4_3_eq mx5_1_0_eq (bR (bR (bR (bR (bR (sgOk14))))))
lemma s330 : Pol 4 3 1 0 table16 .down := signFast _ _ _ _ _ _ _ _ mx10_4_3_eq mx5_1_0_eq (bL (bL (sgOk15)))
lemma s331 : Pol 8 6 2 0 table18 .up := signFast _ _ _ _ _ _ _ _ mx10_8_6_eq mx5_2_0_eq (bR (bL (sgOk15)))
lemma s332 : Pol 8 6 2 1 table2 .up := signFast _ _ _ _ _ _ _ _ mx10_8_6_eq mx5_2_1_eq (bL (bR (sgOk15)))
lemma s333 : Pol 8 7 1 0 table3 .down := signFast _ _ _ _ _ _ _ _ mx10_8_7_eq mx5_1_0_eq (bL (bR (bR (sgOk15))))
lemma s334 : Pol 8 7 1 0 table17 .down := signFast _ _ _ _ _ _ _ _ mx10_8_7_eq mx5_1_0_eq (bR (bR (bR (sgOk15))))
lemma gLeaf0 : BoxGood 4 0 2 0 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.both,.down,.down,.down,.down,.both,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 4 0 2 0) <| .cons (carry s15 4 0 2 0) <| .cons (carry s14 4 0 2 0) <| .cons (carry s13 4 0 2 0) <|
    .cons (carry s12 4 0 2 0) <| .cons (carry s11 4 0 2 0) <| .cons (carry s10 4 0 2 0) <| .cons (carry s9 4 0 2 0) <|
    .cons (carry s8 4 0 2 0) <| .cons (carry s7 4 0 2 0) <| .cons (carry s6 4 0 2 0) <| .cons (carry s5 4 0 2 0) <|
    .cons (carry s27 2 0 1 0) <| .cons (carry s26 2 0 1 0) <| .cons (carry s25 2 0 1 0) <| .cons (carry s24 2 0 1 0) <|
    .cons (carry s23 2 0 1 0) <| .cons (carry s22 2 0 1 0) <| .cons (carry s21 2 0 1 0) <| .cons (carry s20 2 0 1 0) <|
    .cons s31 <| .cons s30 <| .cons unmarked <| .cons unmarked <|
    .cons (carry s19 2 0 1 0) <| .cons (carry s4 4 0 2 0) <| .cons (carry s3 4 0 2 0) <| .cons (carry s2 4 0 2 0) <|
    .cons unmarked <| .cons s29 <| .cons s28 <| .cons (carry s18 2 0 2 0) <|
    .cons (carry s17 2 0 2 0) <| .cons (carry s1 4 0 2 0) <| .cons (carry s0 4 0 2 0) <| .nil
  · decide

lemma gLeaf1 : BoxGood 8 2 2 0 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.down,.down,.down,.down,.down,.both,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 8 2 2 0) <| .cons (carry s15 8 2 2 0) <| .cons (carry s14 8 2 2 0) <| .cons (carry s13 8 2 2 0) <|
    .cons (carry s12 8 2 2 0) <| .cons (carry s11 8 2 2 0) <| .cons (carry s10 8 2 2 0) <| .cons (carry s9 8 2 2 0) <|
    .cons (carry s8 8 2 2 0) <| .cons (carry s7 8 2 2 0) <| .cons (carry s6 8 2 2 0) <| .cons (carry s5 8 2 2 0) <|
    .cons (carry s27 4 2 1 0) <| .cons (carry s26 4 2 1 0) <| .cons (carry s25 4 2 1 0) <| .cons (carry s24 4 2 1 0) <|
    .cons (carry s23 4 2 1 0) <| .cons (carry s22 4 2 1 0) <| .cons (carry s21 4 2 1 0) <| .cons (carry s20 4 2 1 0) <|
    .cons s36 <| .cons s35 <| .cons unmarked <| .cons (carry s33 2 0 1 0) <|
    .cons (carry s19 4 2 1 0) <| .cons (carry s4 8 2 2 0) <| .cons (carry s3 8 2 2 0) <| .cons (carry s2 8 2 2 0) <|
    .cons (carry s32 2 0 1 0) <| .cons unmarked <| .cons s34 <| .cons (carry s18 4 2 2 0) <|
    .cons (carry s17 4 2 2 0) <| .cons (carry s1 8 2 2 0) <| .cons (carry s0 8 2 2 0) <| .nil
  · decide

lemma gLeaf2 : BoxGood 8 3 2 0 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.both,.down,.down,.down,.down,.down,.down,.down,.down,.both,.up,.up,.up,.up])
  · exact .cons (carry s16 8 3 2 0) <| .cons (carry s15 8 3 2 0) <| .cons (carry s14 8 3 2 0) <| .cons (carry s13 8 3 2 0) <|
    .cons (carry s12 8 3 2 0) <| .cons (carry s11 8 3 2 0) <| .cons (carry s10 8 3 2 0) <| .cons (carry s9 8 3 2 0) <|
    .cons (carry s8 8 3 2 0) <| .cons (carry s7 8 3 2 0) <| .cons (carry s6 8 3 2 0) <| .cons (carry s5 8 3 2 0) <|
    .cons (carry s27 4 3 1 0) <| .cons (carry s26 4 3 1 0) <| .cons (carry s25 4 3 1 0) <| .cons (carry s24 4 3 1 0) <|
    .cons (carry s23 4 3 1 0) <| .cons (carry s22 4 3 1 0) <| .cons (carry s21 4 3 1 0) <| .cons (carry s20 4 3 1 0) <|
    .cons unmarked <| .cons unmarked <| .cons s38 <| .cons (carry s33 2 1 1 0) <|
    .cons (carry s19 4 3 1 0) <| .cons (carry s4 8 3 2 0) <| .cons (carry s3 8 3 2 0) <| .cons (carry s2 8 3 2 0) <|
    .cons (carry s32 2 1 1 0) <| .cons s37 <| .cons unmarked <| .cons (carry s18 4 3 2 0) <|
    .cons (carry s17 4 3 2 0) <| .cons (carry s1 8 3 2 0) <| .cons (carry s0 8 3 2 0) <| .nil
  · decide

lemma gLeaf3 : BoxGood 4 0 4 2 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 4 0 4 2) <| .cons (carry s15 4 0 4 2) <| .cons (carry s14 4 0 4 2) <| .cons (carry s13 4 0 4 2) <|
    .cons (carry s12 4 0 4 2) <| .cons (carry s11 4 0 4 2) <| .cons (carry s10 4 0 4 2) <| .cons (carry s9 4 0 4 2) <|
    .cons (carry s8 4 0 4 2) <| .cons (carry s7 4 0 4 2) <| .cons (carry s6 4 0 4 2) <| .cons (carry s5 4 0 4 2) <|
    .cons (carry s48 2 0 1 0) <| .cons (carry s47 2 0 1 0) <| .cons (carry s46 2 0 1 0) <| .cons (carry s45 2 0 1 0) <|
    .cons (carry s44 2 0 1 0) <| .cons (carry s43 2 0 1 0) <| .cons (carry s42 2 0 1 0) <| .cons s53 <|
    .cons s52 <| .cons s51 <| .cons s50 <| .cons unmarked <|
    .cons (carry s41 2 0 1 0) <| .cons (carry s4 4 0 4 2) <| .cons (carry s3 4 0 4 2) <| .cons (carry s2 4 0 4 2) <|
    .cons (carry s40 2 0 2 0) <| .cons s49 <| .cons (carry s39 2 0 2 0) <| .cons (carry s18 2 0 4 2) <|
    .cons (carry s17 2 0 4 2) <| .cons (carry s1 4 0 4 2) <| .cons (carry s0 4 0 4 2) <| .nil
  · decide

lemma gLeaf4 : BoxGood 8 2 4 2 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.both,.down,.down,.down,.down,.down,.down,.both,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 8 2 4 2) <| .cons (carry s15 8 2 4 2) <| .cons (carry s14 8 2 4 2) <| .cons (carry s13 8 2 4 2) <|
    .cons (carry s12 8 2 4 2) <| .cons (carry s11 8 2 4 2) <| .cons (carry s10 8 2 4 2) <| .cons (carry s9 8 2 4 2) <|
    .cons (carry s8 8 2 4 2) <| .cons (carry s7 8 2 4 2) <| .cons (carry s6 8 2 4 2) <| .cons (carry s5 8 2 4 2) <|
    .cons (carry s48 4 2 1 0) <| .cons (carry s47 4 2 1 0) <| .cons (carry s46 4 2 1 0) <| .cons (carry s45 4 2 1 0) <|
    .cons (carry s44 4 2 1 0) <| .cons (carry s43 4 2 1 0) <| .cons (carry s42 4 2 1 0) <| .cons s56 <|
    .cons s55 <| .cons unmarked <| .cons unmarked <| .cons (carry s54 2 0 1 0) <|
    .cons (carry s41 4 2 1 0) <| .cons (carry s4 8 2 4 2) <| .cons (carry s3 8 2 4 2) <| .cons (carry s2 8 2 4 2) <|
    .cons (carry s40 4 2 2 0) <| .cons unmarked <| .cons (carry s39 4 2 2 0) <| .cons (carry s18 4 2 4 2) <|
    .cons (carry s17 4 2 4 2) <| .cons (carry s1 8 2 4 2) <| .cons (carry s0 8 2 4 2) <| .nil
  · decide

lemma gLeaf5 : BoxGood 8 3 4 2 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.both,.both,.down,.down,.down,.down,.down,.down,.down,.both,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 8 3 4 2) <| .cons (carry s15 8 3 4 2) <| .cons (carry s14 8 3 4 2) <| .cons (carry s13 8 3 4 2) <|
    .cons (carry s12 8 3 4 2) <| .cons (carry s11 8 3 4 2) <| .cons (carry s10 8 3 4 2) <| .cons (carry s9 8 3 4 2) <|
    .cons (carry s8 8 3 4 2) <| .cons (carry s7 8 3 4 2) <| .cons (carry s6 8 3 4 2) <| .cons (carry s5 8 3 4 2) <|
    .cons (carry s48 4 3 1 0) <| .cons (carry s47 4 3 1 0) <| .cons (carry s46 4 3 1 0) <| .cons (carry s45 4 3 1 0) <|
    .cons (carry s44 4 3 1 0) <| .cons (carry s43 4 3 1 0) <| .cons (carry s42 4 3 1 0) <| .cons unmarked <|
    .cons unmarked <| .cons unmarked <| .cons s57 <| .cons (carry s54 2 1 1 0) <|
    .cons (carry s41 4 3 1 0) <| .cons (carry s4 8 3 4 2) <| .cons (carry s3 8 3 4 2) <| .cons (carry s2 8 3 4 2) <|
    .cons (carry s40 4 3 2 0) <| .cons unmarked <| .cons (carry s39 4 3 2 0) <| .cons (carry s18 4 3 4 2) <|
    .cons (carry s17 4 3 4 2) <| .cons (carry s1 8 3 4 2) <| .cons (carry s0 8 3 4 2) <| .nil
  · decide

lemma gLeaf6 : BoxGood 8 0 32 24 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 8 0 32 24) <| .cons (carry s15 8 0 32 24) <| .cons (carry s14 8 0 32 24) <| .cons (carry s13 8 0 32 24) <|
    .cons (carry s12 8 0 32 24) <| .cons (carry s11 8 0 32 24) <| .cons (carry s10 8 0 32 24) <| .cons (carry s9 8 0 32 24) <|
    .cons (carry s8 8 0 32 24) <| .cons (carry s7 8 0 32 24) <| .cons (carry s6 8 0 32 24) <| .cons (carry s5 8 0 32 24) <|
    .cons (carry s66 1 0 4 0) <| .cons (carry s65 1 0 4 0) <| .cons (carry s68 1 0 2 0) <| .cons s71 <|
    .cons s70 <| .cons s69 <| .cons (carry s67 1 0 2 0) <| .cons (carry s62 2 0 8 0) <|
    .cons (carry s61 2 0 8 0) <| .cons (carry s60 2 0 8 0) <| .cons (carry s59 2 0 8 0) <| .cons (carry s63 1 0 8 0) <|
    .cons (carry s64 1 0 4 0) <| .cons (carry s4 8 0 32 24) <| .cons (carry s3 8 0 32 24) <| .cons (carry s2 8 0 32 24) <|
    .cons (carry s40 4 0 16 8) <| .cons (carry s58 2 0 8 0) <| .cons (carry s39 4 0 16 8) <| .cons (carry s18 4 0 32 24) <|
    .cons (carry s17 4 0 32 24) <| .cons (carry s1 8 0 32 24) <| .cons (carry s0 8 0 32 24) <| .nil
  · decide

lemma gLeaf7 : BoxGood 16 0 64 50 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.up,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 16 0 64 50) <| .cons (carry s15 16 0 64 50) <| .cons (carry s14 16 0 64 50) <| .cons (carry s13 16 0 64 50) <|
    .cons (carry s12 16 0 64 50) <| .cons (carry s11 16 0 64 50) <| .cons (carry s10 16 0 64 50) <| .cons (carry s9 16 0 64 50) <|
    .cons (carry s8 16 0 64 50) <| .cons (carry s7 16 0 64 50) <| .cons (carry s6 16 0 64 50) <| .cons (carry s5 16 0 64 50) <|
    .cons (carry s66 2 0 8 2) <| .cons (carry s65 2 0 8 2) <| .cons (carry s68 2 0 4 2) <| .cons s73 <|
    .cons unmarked <| .cons s72 <| .cons (carry s67 2 0 4 2) <| .cons (carry s62 4 0 16 2) <|
    .cons (carry s61 4 0 16 2) <| .cons (carry s60 4 0 16 2) <| .cons (carry s59 4 0 16 2) <| .cons (carry s63 2 0 16 2) <|
    .cons (carry s64 2 0 8 2) <| .cons (carry s4 16 0 64 50) <| .cons (carry s3 16 0 64 50) <| .cons (carry s2 16 0 64 50) <|
    .cons (carry s40 8 0 32 18) <| .cons (carry s58 4 0 16 2) <| .cons (carry s39 8 0 32 18) <| .cons (carry s18 8 0 64 50) <|
    .cons (carry s17 8 0 64 50) <| .cons (carry s1 16 0 64 50) <| .cons (carry s0 16 0 64 50) <| .nil
  · decide

lemma gLeaf8 : BoxGood 32 0 128 102 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.both,.up,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 32 0 128 102) <| .cons (carry s15 32 0 128 102) <| .cons (carry s14 32 0 128 102) <| .cons (carry s13 32 0 128 102) <|
    .cons (carry s12 32 0 128 102) <| .cons (carry s11 32 0 128 102) <| .cons (carry s10 32 0 128 102) <| .cons (carry s9 32 0 128 102) <|
    .cons (carry s8 32 0 128 102) <| .cons (carry s7 32 0 128 102) <| .cons (carry s6 32 0 128 102) <| .cons (carry s5 32 0 128 102) <|
    .cons (carry s66 4 0 16 6) <| .cons (carry s65 4 0 16 6) <| .cons (carry s68 4 0 8 6) <| .cons unmarked <|
    .cons unmarked <| .cons s74 <| .cons (carry s67 4 0 8 6) <| .cons (carry s62 8 0 32 6) <|
    .cons (carry s61 8 0 32 6) <| .cons (carry s60 8 0 32 6) <| .cons (carry s59 8 0 32 6) <| .cons (carry s63 4 0 32 6) <|
    .cons (carry s64 4 0 16 6) <| .cons (carry s4 32 0 128 102) <| .cons (carry s3 32 0 128 102) <| .cons (carry s2 32 0 128 102) <|
    .cons (carry s40 16 0 64 38) <| .cons (carry s58 8 0 32 6) <| .cons (carry s39 16 0 64 38) <| .cons (carry s18 16 0 128 102) <|
    .cons (carry s17 16 0 128 102) <| .cons (carry s1 32 0 128 102) <| .cons (carry s0 32 0 128 102) <| .nil
  · decide

lemma gLeaf9 : BoxGood 64 0 128 103 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.both,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 64 0 128 103) <| .cons (carry s15 64 0 128 103) <| .cons (carry s14 64 0 128 103) <| .cons (carry s13 64 0 128 103) <|
    .cons (carry s12 64 0 128 103) <| .cons (carry s11 64 0 128 103) <| .cons (carry s10 64 0 128 103) <| .cons (carry s9 64 0 128 103) <|
    .cons (carry s8 64 0 128 103) <| .cons (carry s7 64 0 128 103) <| .cons (carry s6 64 0 128 103) <| .cons (carry s5 64 0 128 103) <|
    .cons (carry s66 8 0 16 7) <| .cons (carry s65 8 0 16 7) <| .cons (carry s68 8 0 8 7) <| .cons unmarked <|
    .cons s75 <| .cons unmarked <| .cons (carry s67 8 0 8 7) <| .cons (carry s62 16 0 32 7) <|
    .cons (carry s61 16 0 32 7) <| .cons (carry s60 16 0 32 7) <| .cons (carry s59 16 0 32 7) <| .cons (carry s63 8 0 32 7) <|
    .cons (carry s64 8 0 16 7) <| .cons (carry s4 64 0 128 103) <| .cons (carry s3 64 0 128 103) <| .cons (carry s2 64 0 128 103) <|
    .cons (carry s40 32 0 64 39) <| .cons (carry s58 16 0 32 7) <| .cons (carry s39 32 0 64 39) <| .cons (carry s18 32 0 128 103) <|
    .cons (carry s17 32 0 128 103) <| .cons (carry s1 64 0 128 103) <| .cons (carry s0 64 0 128 103) <| .nil
  · decide

lemma gLeaf10 : BoxGood 64 1 128 103 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.both,.up,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 64 1 128 103) <| .cons (carry s15 64 1 128 103) <| .cons (carry s14 64 1 128 103) <| .cons (carry s13 64 1 128 103) <|
    .cons (carry s12 64 1 128 103) <| .cons (carry s11 64 1 128 103) <| .cons (carry s10 64 1 128 103) <| .cons (carry s9 64 1 128 103) <|
    .cons (carry s8 64 1 128 103) <| .cons (carry s7 64 1 128 103) <| .cons (carry s6 64 1 128 103) <| .cons (carry s5 64 1 128 103) <|
    .cons (carry s66 8 1 16 7) <| .cons (carry s65 8 1 16 7) <| .cons (carry s68 8 1 8 7) <| .cons unmarked <|
    .cons unmarked <| .cons s76 <| .cons (carry s67 8 1 8 7) <| .cons (carry s62 16 1 32 7) <|
    .cons (carry s61 16 1 32 7) <| .cons (carry s60 16 1 32 7) <| .cons (carry s59 16 1 32 7) <| .cons (carry s63 8 1 32 7) <|
    .cons (carry s64 8 1 16 7) <| .cons (carry s4 64 1 128 103) <| .cons (carry s3 64 1 128 103) <| .cons (carry s2 64 1 128 103) <|
    .cons (carry s40 32 1 64 39) <| .cons (carry s58 16 1 32 7) <| .cons (carry s39 32 1 64 39) <| .cons (carry s18 32 1 128 103) <|
    .cons (carry s17 32 1 128 103) <| .cons (carry s1 64 1 128 103) <| .cons (carry s0 64 1 128 103) <| .nil
  · decide

lemma gLeaf11 : BoxGood 32 1 64 51 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.up,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 32 1 64 51) <| .cons (carry s15 32 1 64 51) <| .cons (carry s14 32 1 64 51) <| .cons (carry s13 32 1 64 51) <|
    .cons (carry s12 32 1 64 51) <| .cons (carry s11 32 1 64 51) <| .cons (carry s10 32 1 64 51) <| .cons (carry s9 32 1 64 51) <|
    .cons (carry s8 32 1 64 51) <| .cons (carry s7 32 1 64 51) <| .cons (carry s6 32 1 64 51) <| .cons (carry s5 32 1 64 51) <|
    .cons (carry s66 4 1 8 3) <| .cons (carry s65 4 1 8 3) <| .cons (carry s68 4 1 4 3) <| .cons s78 <|
    .cons unmarked <| .cons s77 <| .cons (carry s67 4 1 4 3) <| .cons (carry s62 8 1 16 3) <|
    .cons (carry s61 8 1 16 3) <| .cons (carry s60 8 1 16 3) <| .cons (carry s59 8 1 16 3) <| .cons (carry s63 4 1 16 3) <|
    .cons (carry s64 4 1 8 3) <| .cons (carry s4 32 1 64 51) <| .cons (carry s3 32 1 64 51) <| .cons (carry s2 32 1 64 51) <|
    .cons (carry s40 16 1 32 19) <| .cons (carry s58 8 1 16 3) <| .cons (carry s39 16 1 32 19) <| .cons (carry s18 16 1 64 51) <|
    .cons (carry s17 16 1 64 51) <| .cons (carry s1 32 1 64 51) <| .cons (carry s0 32 1 64 51) <| .nil
  · decide

lemma gLeaf12 : BoxGood 16 1 32 25 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 16 1 32 25) <| .cons (carry s15 16 1 32 25) <| .cons (carry s14 16 1 32 25) <| .cons (carry s13 16 1 32 25) <|
    .cons (carry s12 16 1 32 25) <| .cons (carry s11 16 1 32 25) <| .cons (carry s10 16 1 32 25) <| .cons (carry s9 16 1 32 25) <|
    .cons (carry s8 16 1 32 25) <| .cons (carry s7 16 1 32 25) <| .cons (carry s6 16 1 32 25) <| .cons (carry s5 16 1 32 25) <|
    .cons (carry s66 2 1 4 1) <| .cons (carry s65 2 1 4 1) <| .cons (carry s68 2 1 2 1) <| .cons s81 <|
    .cons s80 <| .cons s79 <| .cons (carry s67 2 1 2 1) <| .cons (carry s62 4 1 8 1) <|
    .cons (carry s61 4 1 8 1) <| .cons (carry s60 4 1 8 1) <| .cons (carry s59 4 1 8 1) <| .cons (carry s63 2 1 8 1) <|
    .cons (carry s64 2 1 4 1) <| .cons (carry s4 16 1 32 25) <| .cons (carry s3 16 1 32 25) <| .cons (carry s2 16 1 32 25) <|
    .cons (carry s40 8 1 16 9) <| .cons (carry s58 4 1 8 1) <| .cons (carry s39 8 1 16 9) <| .cons (carry s18 8 1 32 25) <|
    .cons (carry s17 8 1 32 25) <| .cons (carry s1 16 1 32 25) <| .cons (carry s0 16 1 32 25) <| .nil
  · decide

lemma gLeaf13 : BoxGood 32 0 64 52 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.both,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 32 0 64 52) <| .cons (carry s15 32 0 64 52) <| .cons (carry s14 32 0 64 52) <| .cons (carry s13 32 0 64 52) <|
    .cons (carry s12 32 0 64 52) <| .cons (carry s11 32 0 64 52) <| .cons (carry s10 32 0 64 52) <| .cons (carry s9 32 0 64 52) <|
    .cons (carry s8 32 0 64 52) <| .cons (carry s7 32 0 64 52) <| .cons (carry s6 32 0 64 52) <| .cons (carry s5 32 0 64 52) <|
    .cons (carry s66 4 0 8 4) <| .cons (carry s65 4 0 8 4) <| .cons (carry s83 2 0 1 0) <| .cons unmarked <|
    .cons s84 <| .cons unmarked <| .cons (carry s82 4 0 2 0) <| .cons (carry s62 8 0 16 4) <|
    .cons (carry s61 8 0 16 4) <| .cons (carry s60 8 0 16 4) <| .cons (carry s59 8 0 16 4) <| .cons (carry s63 4 0 16 4) <|
    .cons (carry s64 4 0 8 4) <| .cons (carry s4 32 0 64 52) <| .cons (carry s3 32 0 64 52) <| .cons (carry s2 32 0 64 52) <|
    .cons (carry s40 16 0 32 20) <| .cons (carry s58 8 0 16 4) <| .cons (carry s39 16 0 32 20) <| .cons (carry s18 16 0 64 52) <|
    .cons (carry s17 16 0 64 52) <| .cons (carry s1 32 0 64 52) <| .cons (carry s0 32 0 64 52) <| .nil
  · decide

lemma gLeaf14 : BoxGood 32 1 128 104 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.both,.up,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 32 1 128 104) <| .cons (carry s15 32 1 128 104) <| .cons (carry s14 32 1 128 104) <| .cons (carry s13 32 1 128 104) <|
    .cons (carry s12 32 1 128 104) <| .cons (carry s11 32 1 128 104) <| .cons (carry s10 32 1 128 104) <| .cons (carry s9 32 1 128 104) <|
    .cons (carry s8 32 1 128 104) <| .cons (carry s7 32 1 128 104) <| .cons (carry s6 32 1 128 104) <| .cons (carry s5 32 1 128 104) <|
    .cons (carry s66 4 1 16 8) <| .cons (carry s65 4 1 16 8) <| .cons (carry s83 2 1 2 0) <| .cons unmarked <|
    .cons unmarked <| .cons s85 <| .cons (carry s82 4 1 4 0) <| .cons (carry s62 8 1 32 8) <|
    .cons (carry s61 8 1 32 8) <| .cons (carry s60 8 1 32 8) <| .cons (carry s59 8 1 32 8) <| .cons (carry s63 4 1 32 8) <|
    .cons (carry s64 4 1 16 8) <| .cons (carry s4 32 1 128 104) <| .cons (carry s3 32 1 128 104) <| .cons (carry s2 32 1 128 104) <|
    .cons (carry s40 16 1 64 40) <| .cons (carry s58 8 1 32 8) <| .cons (carry s39 16 1 64 40) <| .cons (carry s18 16 1 128 104) <|
    .cons (carry s17 16 1 128 104) <| .cons (carry s1 32 1 128 104) <| .cons (carry s0 32 1 128 104) <| .nil
  · decide

lemma gLeaf15 : BoxGood 64 2 128 105 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.both,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 64 2 128 105) <| .cons (carry s15 64 2 128 105) <| .cons (carry s14 64 2 128 105) <| .cons (carry s13 64 2 128 105) <|
    .cons (carry s12 64 2 128 105) <| .cons (carry s11 64 2 128 105) <| .cons (carry s10 64 2 128 105) <| .cons (carry s9 64 2 128 105) <|
    .cons (carry s8 64 2 128 105) <| .cons (carry s7 64 2 128 105) <| .cons (carry s6 64 2 128 105) <| .cons (carry s5 64 2 128 105) <|
    .cons (carry s66 8 2 16 9) <| .cons (carry s65 8 2 16 9) <| .cons (carry s83 4 2 2 1) <| .cons unmarked <|
    .cons s86 <| .cons unmarked <| .cons (carry s82 8 2 4 1) <| .cons (carry s62 16 2 32 9) <|
    .cons (carry s61 16 2 32 9) <| .cons (carry s60 16 2 32 9) <| .cons (carry s59 16 2 32 9) <| .cons (carry s63 8 2 32 9) <|
    .cons (carry s64 8 2 16 9) <| .cons (carry s4 64 2 128 105) <| .cons (carry s3 64 2 128 105) <| .cons (carry s2 64 2 128 105) <|
    .cons (carry s40 32 2 64 41) <| .cons (carry s58 16 2 32 9) <| .cons (carry s39 32 2 64 41) <| .cons (carry s18 32 2 128 105) <|
    .cons (carry s17 32 2 128 105) <| .cons (carry s1 64 2 128 105) <| .cons (carry s0 64 2 128 105) <| .nil
  · decide

lemma gLeaf16 : BoxGood 64 3 128 105 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.both,.up,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 64 3 128 105) <| .cons (carry s15 64 3 128 105) <| .cons (carry s14 64 3 128 105) <| .cons (carry s13 64 3 128 105) <|
    .cons (carry s12 64 3 128 105) <| .cons (carry s11 64 3 128 105) <| .cons (carry s10 64 3 128 105) <| .cons (carry s9 64 3 128 105) <|
    .cons (carry s8 64 3 128 105) <| .cons (carry s7 64 3 128 105) <| .cons (carry s6 64 3 128 105) <| .cons (carry s5 64 3 128 105) <|
    .cons (carry s66 8 3 16 9) <| .cons (carry s65 8 3 16 9) <| .cons (carry s83 4 3 2 1) <| .cons unmarked <|
    .cons unmarked <| .cons s87 <| .cons (carry s82 8 3 4 1) <| .cons (carry s62 16 3 32 9) <|
    .cons (carry s61 16 3 32 9) <| .cons (carry s60 16 3 32 9) <| .cons (carry s59 16 3 32 9) <| .cons (carry s63 8 3 32 9) <|
    .cons (carry s64 8 3 16 9) <| .cons (carry s4 64 3 128 105) <| .cons (carry s3 64 3 128 105) <| .cons (carry s2 64 3 128 105) <|
    .cons (carry s40 32 3 64 41) <| .cons (carry s58 16 3 32 9) <| .cons (carry s39 32 3 64 41) <| .cons (carry s18 32 3 128 105) <|
    .cons (carry s17 32 3 128 105) <| .cons (carry s1 64 3 128 105) <| .cons (carry s0 64 3 128 105) <| .nil
  · decide

lemma gLeaf17 : BoxGood 32 0 64 53 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.down,.down,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 32 0 64 53) <| .cons (carry s15 32 0 64 53) <| .cons (carry s14 32 0 64 53) <| .cons (carry s13 32 0 64 53) <|
    .cons (carry s12 32 0 64 53) <| .cons (carry s11 32 0 64 53) <| .cons (carry s10 32 0 64 53) <| .cons (carry s9 32 0 64 53) <|
    .cons (carry s8 32 0 64 53) <| .cons (carry s7 32 0 64 53) <| .cons (carry s6 32 0 64 53) <| .cons (carry s5 32 0 64 53) <|
    .cons (carry s66 4 0 8 5) <| .cons (carry s65 4 0 8 5) <| .cons unmarked <| .cons s90 <|
    .cons (carry s88 2 0 1 0) <| .cons s89 <| .cons (carry s82 4 0 2 1) <| .cons (carry s62 8 0 16 5) <|
    .cons (carry s61 8 0 16 5) <| .cons (carry s60 8 0 16 5) <| .cons (carry s59 8 0 16 5) <| .cons (carry s63 4 0 16 5) <|
    .cons (carry s64 4 0 8 5) <| .cons (carry s4 32 0 64 53) <| .cons (carry s3 32 0 64 53) <| .cons (carry s2 32 0 64 53) <|
    .cons (carry s40 16 0 32 21) <| .cons (carry s58 8 0 16 5) <| .cons (carry s39 16 0 32 21) <| .cons (carry s18 16 0 64 53) <|
    .cons (carry s17 16 0 64 53) <| .cons (carry s1 32 0 64 53) <| .cons (carry s0 32 0 64 53) <| .nil
  · decide

lemma gLeaf18 : BoxGood 32 1 64 53 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.both,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 32 1 64 53) <| .cons (carry s15 32 1 64 53) <| .cons (carry s14 32 1 64 53) <| .cons (carry s13 32 1 64 53) <|
    .cons (carry s12 32 1 64 53) <| .cons (carry s11 32 1 64 53) <| .cons (carry s10 32 1 64 53) <| .cons (carry s9 32 1 64 53) <|
    .cons (carry s8 32 1 64 53) <| .cons (carry s7 32 1 64 53) <| .cons (carry s6 32 1 64 53) <| .cons (carry s5 32 1 64 53) <|
    .cons (carry s66 4 1 8 5) <| .cons (carry s65 4 1 8 5) <| .cons s91 <| .cons unmarked <|
    .cons (carry s88 2 1 1 0) <| .cons unmarked <| .cons (carry s82 4 1 2 1) <| .cons (carry s62 8 1 16 5) <|
    .cons (carry s61 8 1 16 5) <| .cons (carry s60 8 1 16 5) <| .cons (carry s59 8 1 16 5) <| .cons (carry s63 4 1 16 5) <|
    .cons (carry s64 4 1 8 5) <| .cons (carry s4 32 1 64 53) <| .cons (carry s3 32 1 64 53) <| .cons (carry s2 32 1 64 53) <|
    .cons (carry s40 16 1 32 21) <| .cons (carry s58 8 1 16 5) <| .cons (carry s39 16 1 32 21) <| .cons (carry s18 16 1 64 53) <|
    .cons (carry s17 16 1 64 53) <| .cons (carry s1 32 1 64 53) <| .cons (carry s0 32 1 64 53) <| .nil
  · decide

lemma gLeaf19 : BoxGood 16 1 64 52 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.up,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 16 1 64 52) <| .cons (carry s15 16 1 64 52) <| .cons (carry s14 16 1 64 52) <| .cons (carry s13 16 1 64 52) <|
    .cons (carry s12 16 1 64 52) <| .cons (carry s11 16 1 64 52) <| .cons (carry s10 16 1 64 52) <| .cons (carry s9 16 1 64 52) <|
    .cons (carry s8 16 1 64 52) <| .cons (carry s7 16 1 64 52) <| .cons (carry s6 16 1 64 52) <| .cons (carry s5 16 1 64 52) <|
    .cons (carry s66 2 1 8 4) <| .cons (carry s65 2 1 8 4) <| .cons (carry s92 1 0 2 0) <| .cons s94 <|
    .cons unmarked <| .cons s93 <| .cons (carry s82 2 1 2 0) <| .cons (carry s62 4 1 16 4) <|
    .cons (carry s61 4 1 16 4) <| .cons (carry s60 4 1 16 4) <| .cons (carry s59 4 1 16 4) <| .cons (carry s63 2 1 16 4) <|
    .cons (carry s64 2 1 8 4) <| .cons (carry s4 16 1 64 52) <| .cons (carry s3 16 1 64 52) <| .cons (carry s2 16 1 64 52) <|
    .cons (carry s40 8 1 32 20) <| .cons (carry s58 4 1 16 4) <| .cons (carry s39 8 1 32 20) <| .cons (carry s18 8 1 64 52) <|
    .cons (carry s17 8 1 64 52) <| .cons (carry s1 16 1 64 52) <| .cons (carry s0 16 1 64 52) <| .nil
  · decide

lemma gLeaf20 : BoxGood 32 2 128 106 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.both,.up,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 32 2 128 106) <| .cons (carry s15 32 2 128 106) <| .cons (carry s14 32 2 128 106) <| .cons (carry s13 32 2 128 106) <|
    .cons (carry s12 32 2 128 106) <| .cons (carry s11 32 2 128 106) <| .cons (carry s10 32 2 128 106) <| .cons (carry s9 32 2 128 106) <|
    .cons (carry s8 32 2 128 106) <| .cons (carry s7 32 2 128 106) <| .cons (carry s6 32 2 128 106) <| .cons (carry s5 32 2 128 106) <|
    .cons (carry s66 4 2 16 10) <| .cons (carry s65 4 2 16 10) <| .cons (carry s92 2 0 4 2) <| .cons unmarked <|
    .cons unmarked <| .cons s95 <| .cons (carry s82 4 2 4 2) <| .cons (carry s62 8 2 32 10) <|
    .cons (carry s61 8 2 32 10) <| .cons (carry s60 8 2 32 10) <| .cons (carry s59 8 2 32 10) <| .cons (carry s63 4 2 32 10) <|
    .cons (carry s64 4 2 16 10) <| .cons (carry s4 32 2 128 106) <| .cons (carry s3 32 2 128 106) <| .cons (carry s2 32 2 128 106) <|
    .cons (carry s40 16 2 64 42) <| .cons (carry s58 8 2 32 10) <| .cons (carry s39 16 2 64 42) <| .cons (carry s18 16 2 128 106) <|
    .cons (carry s17 16 2 128 106) <| .cons (carry s1 32 2 128 106) <| .cons (carry s0 32 2 128 106) <| .nil
  · decide

lemma gLeaf21 : BoxGood 64 4 128 107 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.both,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 64 4 128 107) <| .cons (carry s15 64 4 128 107) <| .cons (carry s14 64 4 128 107) <| .cons (carry s13 64 4 128 107) <|
    .cons (carry s12 64 4 128 107) <| .cons (carry s11 64 4 128 107) <| .cons (carry s10 64 4 128 107) <| .cons (carry s9 64 4 128 107) <|
    .cons (carry s8 64 4 128 107) <| .cons (carry s7 64 4 128 107) <| .cons (carry s6 64 4 128 107) <| .cons (carry s5 64 4 128 107) <|
    .cons (carry s66 8 4 16 11) <| .cons (carry s65 8 4 16 11) <| .cons (carry s92 4 0 4 3) <| .cons unmarked <|
    .cons s96 <| .cons unmarked <| .cons (carry s82 8 4 4 3) <| .cons (carry s62 16 4 32 11) <|
    .cons (carry s61 16 4 32 11) <| .cons (carry s60 16 4 32 11) <| .cons (carry s59 16 4 32 11) <| .cons (carry s63 8 4 32 11) <|
    .cons (carry s64 8 4 16 11) <| .cons (carry s4 64 4 128 107) <| .cons (carry s3 64 4 128 107) <| .cons (carry s2 64 4 128 107) <|
    .cons (carry s40 32 4 64 43) <| .cons (carry s58 16 4 32 11) <| .cons (carry s39 32 4 64 43) <| .cons (carry s18 32 4 128 107) <|
    .cons (carry s17 32 4 128 107) <| .cons (carry s1 64 4 128 107) <| .cons (carry s0 64 4 128 107) <| .nil
  · decide

lemma gLeaf22 : BoxGood 64 5 128 107 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.both,.up,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 64 5 128 107) <| .cons (carry s15 64 5 128 107) <| .cons (carry s14 64 5 128 107) <| .cons (carry s13 64 5 128 107) <|
    .cons (carry s12 64 5 128 107) <| .cons (carry s11 64 5 128 107) <| .cons (carry s10 64 5 128 107) <| .cons (carry s9 64 5 128 107) <|
    .cons (carry s8 64 5 128 107) <| .cons (carry s7 64 5 128 107) <| .cons (carry s6 64 5 128 107) <| .cons (carry s5 64 5 128 107) <|
    .cons (carry s66 8 5 16 11) <| .cons (carry s65 8 5 16 11) <| .cons (carry s92 4 1 4 3) <| .cons unmarked <|
    .cons unmarked <| .cons s97 <| .cons (carry s82 8 5 4 3) <| .cons (carry s62 16 5 32 11) <|
    .cons (carry s61 16 5 32 11) <| .cons (carry s60 16 5 32 11) <| .cons (carry s59 16 5 32 11) <| .cons (carry s63 8 5 32 11) <|
    .cons (carry s64 8 5 16 11) <| .cons (carry s4 64 5 128 107) <| .cons (carry s3 64 5 128 107) <| .cons (carry s2 64 5 128 107) <|
    .cons (carry s40 32 5 64 43) <| .cons (carry s58 16 5 32 11) <| .cons (carry s39 32 5 64 43) <| .cons (carry s18 32 5 128 107) <|
    .cons (carry s17 32 5 128 107) <| .cons (carry s1 64 5 128 107) <| .cons (carry s0 64 5 128 107) <| .nil
  · decide

lemma gLeaf23 : BoxGood 32 3 64 53 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.up,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 32 3 64 53) <| .cons (carry s15 32 3 64 53) <| .cons (carry s14 32 3 64 53) <| .cons (carry s13 32 3 64 53) <|
    .cons (carry s12 32 3 64 53) <| .cons (carry s11 32 3 64 53) <| .cons (carry s10 32 3 64 53) <| .cons (carry s9 32 3 64 53) <|
    .cons (carry s8 32 3 64 53) <| .cons (carry s7 32 3 64 53) <| .cons (carry s6 32 3 64 53) <| .cons (carry s5 32 3 64 53) <|
    .cons (carry s66 4 3 8 5) <| .cons (carry s65 4 3 8 5) <| .cons (carry s92 2 1 2 1) <| .cons s99 <|
    .cons unmarked <| .cons s98 <| .cons (carry s82 4 3 2 1) <| .cons (carry s62 8 3 16 5) <|
    .cons (carry s61 8 3 16 5) <| .cons (carry s60 8 3 16 5) <| .cons (carry s59 8 3 16 5) <| .cons (carry s63 4 3 16 5) <|
    .cons (carry s64 4 3 8 5) <| .cons (carry s4 32 3 64 53) <| .cons (carry s3 32 3 64 53) <| .cons (carry s2 32 3 64 53) <|
    .cons (carry s40 16 3 32 21) <| .cons (carry s58 8 3 16 5) <| .cons (carry s39 16 3 32 21) <| .cons (carry s18 16 3 64 53) <|
    .cons (carry s17 16 3 64 53) <| .cons (carry s1 32 3 64 53) <| .cons (carry s0 32 3 64 53) <| .nil
  · decide

lemma gLeaf24 : BoxGood 16 0 32 27 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.down,.down,.both,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 16 0 32 27) <| .cons (carry s15 16 0 32 27) <| .cons (carry s14 16 0 32 27) <| .cons (carry s13 16 0 32 27) <|
    .cons (carry s12 16 0 32 27) <| .cons (carry s11 16 0 32 27) <| .cons (carry s10 16 0 32 27) <| .cons (carry s9 16 0 32 27) <|
    .cons (carry s8 16 0 32 27) <| .cons (carry s7 16 0 32 27) <| .cons (carry s6 16 0 32 27) <| .cons (carry s5 16 0 32 27) <|
    .cons (carry s66 2 0 4 3) <| .cons (carry s65 2 0 4 3) <| .cons unmarked <| .cons s102 <|
    .cons s101 <| .cons s100 <| .cons unmarked <| .cons (carry s62 4 0 8 3) <|
    .cons (carry s61 4 0 8 3) <| .cons (carry s60 4 0 8 3) <| .cons (carry s59 4 0 8 3) <| .cons (carry s63 2 0 8 3) <|
    .cons (carry s64 2 0 4 3) <| .cons (carry s4 16 0 32 27) <| .cons (carry s3 16 0 32 27) <| .cons (carry s2 16 0 32 27) <|
    .cons (carry s40 8 0 16 11) <| .cons (carry s58 4 0 8 3) <| .cons (carry s39 8 0 16 11) <| .cons (carry s18 8 0 32 27) <|
    .cons (carry s17 8 0 32 27) <| .cons (carry s1 16 0 32 27) <| .cons (carry s0 16 0 32 27) <| .nil
  · decide

lemma gLeaf25 : BoxGood 32 2 64 54 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.both,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 32 2 64 54) <| .cons (carry s15 32 2 64 54) <| .cons (carry s14 32 2 64 54) <| .cons (carry s13 32 2 64 54) <|
    .cons (carry s12 32 2 64 54) <| .cons (carry s11 32 2 64 54) <| .cons (carry s10 32 2 64 54) <| .cons (carry s9 32 2 64 54) <|
    .cons (carry s8 32 2 64 54) <| .cons (carry s7 32 2 64 54) <| .cons (carry s6 32 2 64 54) <| .cons (carry s5 32 2 64 54) <|
    .cons (carry s66 4 2 8 6) <| .cons (carry s65 4 2 8 6) <| .cons (carry s104 2 0 1 0) <| .cons unmarked <|
    .cons s105 <| .cons unmarked <| .cons (carry s103 2 0 2 0) <| .cons (carry s62 8 2 16 6) <|
    .cons (carry s61 8 2 16 6) <| .cons (carry s60 8 2 16 6) <| .cons (carry s59 8 2 16 6) <| .cons (carry s63 4 2 16 6) <|
    .cons (carry s64 4 2 8 6) <| .cons (carry s4 32 2 64 54) <| .cons (carry s3 32 2 64 54) <| .cons (carry s2 32 2 64 54) <|
    .cons (carry s40 16 2 32 22) <| .cons (carry s58 8 2 16 6) <| .cons (carry s39 16 2 32 22) <| .cons (carry s18 16 2 64 54) <|
    .cons (carry s17 16 2 64 54) <| .cons (carry s1 32 2 64 54) <| .cons (carry s0 32 2 64 54) <| .nil
  · decide

lemma gLeaf26 : BoxGood 32 3 128 108 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.both,.up,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 32 3 128 108) <| .cons (carry s15 32 3 128 108) <| .cons (carry s14 32 3 128 108) <| .cons (carry s13 32 3 128 108) <|
    .cons (carry s12 32 3 128 108) <| .cons (carry s11 32 3 128 108) <| .cons (carry s10 32 3 128 108) <| .cons (carry s9 32 3 128 108) <|
    .cons (carry s8 32 3 128 108) <| .cons (carry s7 32 3 128 108) <| .cons (carry s6 32 3 128 108) <| .cons (carry s5 32 3 128 108) <|
    .cons (carry s66 4 3 16 12) <| .cons (carry s65 4 3 16 12) <| .cons (carry s104 2 1 2 0) <| .cons unmarked <|
    .cons unmarked <| .cons s106 <| .cons (carry s103 2 1 4 0) <| .cons (carry s62 8 3 32 12) <|
    .cons (carry s61 8 3 32 12) <| .cons (carry s60 8 3 32 12) <| .cons (carry s59 8 3 32 12) <| .cons (carry s63 4 3 32 12) <|
    .cons (carry s64 4 3 16 12) <| .cons (carry s4 32 3 128 108) <| .cons (carry s3 32 3 128 108) <| .cons (carry s2 32 3 128 108) <|
    .cons (carry s40 16 3 64 44) <| .cons (carry s58 8 3 32 12) <| .cons (carry s39 16 3 64 44) <| .cons (carry s18 16 3 128 108) <|
    .cons (carry s17 16 3 128 108) <| .cons (carry s1 32 3 128 108) <| .cons (carry s0 32 3 128 108) <| .nil
  · decide

lemma gLeaf27 : BoxGood 64 6 128 109 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.both,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 64 6 128 109) <| .cons (carry s15 64 6 128 109) <| .cons (carry s14 64 6 128 109) <| .cons (carry s13 64 6 128 109) <|
    .cons (carry s12 64 6 128 109) <| .cons (carry s11 64 6 128 109) <| .cons (carry s10 64 6 128 109) <| .cons (carry s9 64 6 128 109) <|
    .cons (carry s8 64 6 128 109) <| .cons (carry s7 64 6 128 109) <| .cons (carry s6 64 6 128 109) <| .cons (carry s5 64 6 128 109) <|
    .cons (carry s66 8 6 16 13) <| .cons (carry s65 8 6 16 13) <| .cons (carry s104 4 2 2 1) <| .cons unmarked <|
    .cons s107 <| .cons unmarked <| .cons (carry s103 4 2 4 1) <| .cons (carry s62 16 6 32 13) <|
    .cons (carry s61 16 6 32 13) <| .cons (carry s60 16 6 32 13) <| .cons (carry s59 16 6 32 13) <| .cons (carry s63 8 6 32 13) <|
    .cons (carry s64 8 6 16 13) <| .cons (carry s4 64 6 128 109) <| .cons (carry s3 64 6 128 109) <| .cons (carry s2 64 6 128 109) <|
    .cons (carry s40 32 6 64 45) <| .cons (carry s58 16 6 32 13) <| .cons (carry s39 32 6 64 45) <| .cons (carry s18 32 6 128 109) <|
    .cons (carry s17 32 6 128 109) <| .cons (carry s1 64 6 128 109) <| .cons (carry s0 64 6 128 109) <| .nil
  · decide

lemma gLeaf28 : BoxGood 64 7 128 109 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.both,.up,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 64 7 128 109) <| .cons (carry s15 64 7 128 109) <| .cons (carry s14 64 7 128 109) <| .cons (carry s13 64 7 128 109) <|
    .cons (carry s12 64 7 128 109) <| .cons (carry s11 64 7 128 109) <| .cons (carry s10 64 7 128 109) <| .cons (carry s9 64 7 128 109) <|
    .cons (carry s8 64 7 128 109) <| .cons (carry s7 64 7 128 109) <| .cons (carry s6 64 7 128 109) <| .cons (carry s5 64 7 128 109) <|
    .cons (carry s66 8 7 16 13) <| .cons (carry s65 8 7 16 13) <| .cons (carry s104 4 3 2 1) <| .cons unmarked <|
    .cons unmarked <| .cons s108 <| .cons (carry s103 4 3 4 1) <| .cons (carry s62 16 7 32 13) <|
    .cons (carry s61 16 7 32 13) <| .cons (carry s60 16 7 32 13) <| .cons (carry s59 16 7 32 13) <| .cons (carry s63 8 7 32 13) <|
    .cons (carry s64 8 7 16 13) <| .cons (carry s4 64 7 128 109) <| .cons (carry s3 64 7 128 109) <| .cons (carry s2 64 7 128 109) <|
    .cons (carry s40 32 7 64 45) <| .cons (carry s58 16 7 32 13) <| .cons (carry s39 32 7 64 45) <| .cons (carry s18 32 7 128 109) <|
    .cons (carry s17 32 7 128 109) <| .cons (carry s1 64 7 128 109) <| .cons (carry s0 64 7 128 109) <| .nil
  · decide

lemma gLeaf29 : BoxGood 32 2 64 55 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.down,.down,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 32 2 64 55) <| .cons (carry s15 32 2 64 55) <| .cons (carry s14 32 2 64 55) <| .cons (carry s13 32 2 64 55) <|
    .cons (carry s12 32 2 64 55) <| .cons (carry s11 32 2 64 55) <| .cons (carry s10 32 2 64 55) <| .cons (carry s9 32 2 64 55) <|
    .cons (carry s8 32 2 64 55) <| .cons (carry s7 32 2 64 55) <| .cons (carry s6 32 2 64 55) <| .cons (carry s5 32 2 64 55) <|
    .cons (carry s66 4 2 8 7) <| .cons (carry s65 4 2 8 7) <| .cons unmarked <| .cons s111 <|
    .cons (carry s109 2 0 1 0) <| .cons s110 <| .cons (carry s103 2 0 2 1) <| .cons (carry s62 8 2 16 7) <|
    .cons (carry s61 8 2 16 7) <| .cons (carry s60 8 2 16 7) <| .cons (carry s59 8 2 16 7) <| .cons (carry s63 4 2 16 7) <|
    .cons (carry s64 4 2 8 7) <| .cons (carry s4 32 2 64 55) <| .cons (carry s3 32 2 64 55) <| .cons (carry s2 32 2 64 55) <|
    .cons (carry s40 16 2 32 23) <| .cons (carry s58 8 2 16 7) <| .cons (carry s39 16 2 32 23) <| .cons (carry s18 16 2 64 55) <|
    .cons (carry s17 16 2 64 55) <| .cons (carry s1 32 2 64 55) <| .cons (carry s0 32 2 64 55) <| .nil
  · decide

lemma gLeaf30 : BoxGood 32 3 64 55 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.both,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 32 3 64 55) <| .cons (carry s15 32 3 64 55) <| .cons (carry s14 32 3 64 55) <| .cons (carry s13 32 3 64 55) <|
    .cons (carry s12 32 3 64 55) <| .cons (carry s11 32 3 64 55) <| .cons (carry s10 32 3 64 55) <| .cons (carry s9 32 3 64 55) <|
    .cons (carry s8 32 3 64 55) <| .cons (carry s7 32 3 64 55) <| .cons (carry s6 32 3 64 55) <| .cons (carry s5 32 3 64 55) <|
    .cons (carry s66 4 3 8 7) <| .cons (carry s65 4 3 8 7) <| .cons s112 <| .cons unmarked <|
    .cons (carry s109 2 1 1 0) <| .cons unmarked <| .cons (carry s103 2 1 2 1) <| .cons (carry s62 8 3 16 7) <|
    .cons (carry s61 8 3 16 7) <| .cons (carry s60 8 3 16 7) <| .cons (carry s59 8 3 16 7) <| .cons (carry s63 4 3 16 7) <|
    .cons (carry s64 4 3 8 7) <| .cons (carry s4 32 3 64 55) <| .cons (carry s3 32 3 64 55) <| .cons (carry s2 32 3 64 55) <|
    .cons (carry s40 16 3 32 23) <| .cons (carry s58 8 3 16 7) <| .cons (carry s39 16 3 32 23) <| .cons (carry s18 16 3 64 55) <|
    .cons (carry s17 16 3 64 55) <| .cons (carry s1 32 3 64 55) <| .cons (carry s0 32 3 64 55) <| .nil
  · decide

lemma gLeaf31 : BoxGood 16 0 16 14 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.down,.down,.down,.both,.up,.up,.up,.up,.up,.both,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 16 0 16 14) <| .cons (carry s15 16 0 16 14) <| .cons (carry s14 16 0 16 14) <| .cons (carry s13 16 0 16 14) <|
    .cons (carry s12 16 0 16 14) <| .cons (carry s11 16 0 16 14) <| .cons (carry s10 16 0 16 14) <| .cons (carry s9 16 0 16 14) <|
    .cons (carry s8 16 0 16 14) <| .cons (carry s7 16 0 16 14) <| .cons (carry s6 16 0 16 14) <| .cons (carry s5 16 0 16 14) <|
    .cons (carry s116 2 0 1 0) <| .cons unmarked <| .cons s117 <| .cons (carry s115 2 0 2 0) <|
    .cons (carry s114 2 0 2 0) <| .cons (carry s113 2 0 2 0) <| .cons unmarked <| .cons (carry s62 4 0 4 2) <|
    .cons (carry s61 4 0 4 2) <| .cons (carry s60 4 0 4 2) <| .cons (carry s59 4 0 4 2) <| .cons (carry s63 2 0 4 2) <|
    .cons unmarked <| .cons (carry s4 16 0 16 14) <| .cons (carry s3 16 0 16 14) <| .cons (carry s2 16 0 16 14) <|
    .cons (carry s40 8 0 8 6) <| .cons (carry s58 4 0 4 2) <| .cons (carry s39 8 0 8 6) <| .cons (carry s18 8 0 16 14) <|
    .cons (carry s17 8 0 16 14) <| .cons (carry s1 16 0 16 14) <| .cons (carry s0 16 0 16 14) <| .nil
  · decide

lemma gLeaf32 : BoxGood 16 1 32 28 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.down,.down,.both,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 16 1 32 28) <| .cons (carry s15 16 1 32 28) <| .cons (carry s14 16 1 32 28) <| .cons (carry s13 16 1 32 28) <|
    .cons (carry s12 16 1 32 28) <| .cons (carry s11 16 1 32 28) <| .cons (carry s10 16 1 32 28) <| .cons (carry s9 16 1 32 28) <|
    .cons (carry s8 16 1 32 28) <| .cons (carry s7 16 1 32 28) <| .cons (carry s6 16 1 32 28) <| .cons (carry s5 16 1 32 28) <|
    .cons (carry s116 2 1 2 0) <| .cons s119 <| .cons unmarked <| .cons (carry s115 2 1 4 0) <|
    .cons (carry s114 2 1 4 0) <| .cons (carry s113 2 1 4 0) <| .cons unmarked <| .cons (carry s62 4 1 8 4) <|
    .cons (carry s61 4 1 8 4) <| .cons (carry s60 4 1 8 4) <| .cons (carry s59 4 1 8 4) <| .cons (carry s63 2 1 8 4) <|
    .cons (carry s118 1 0 2 0) <| .cons (carry s4 16 1 32 28) <| .cons (carry s3 16 1 32 28) <| .cons (carry s2 16 1 32 28) <|
    .cons (carry s40 8 1 16 12) <| .cons (carry s58 4 1 8 4) <| .cons (carry s39 8 1 16 12) <| .cons (carry s18 8 1 32 28) <|
    .cons (carry s17 8 1 32 28) <| .cons (carry s1 16 1 32 28) <| .cons (carry s0 16 1 32 28) <| .nil
  · decide

lemma gLeaf33 : BoxGood 16 1 32 29 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.down,.down,.down,.both,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 16 1 32 29) <| .cons (carry s15 16 1 32 29) <| .cons (carry s14 16 1 32 29) <| .cons (carry s13 16 1 32 29) <|
    .cons (carry s12 16 1 32 29) <| .cons (carry s11 16 1 32 29) <| .cons (carry s10 16 1 32 29) <| .cons (carry s9 16 1 32 29) <|
    .cons (carry s8 16 1 32 29) <| .cons (carry s7 16 1 32 29) <| .cons (carry s6 16 1 32 29) <| .cons (carry s5 16 1 32 29) <|
    .cons (carry s116 2 1 2 1) <| .cons unmarked <| .cons s120 <| .cons (carry s115 2 1 4 1) <|
    .cons (carry s114 2 1 4 1) <| .cons (carry s113 2 1 4 1) <| .cons unmarked <| .cons (carry s62 4 1 8 5) <|
    .cons (carry s61 4 1 8 5) <| .cons (carry s60 4 1 8 5) <| .cons (carry s59 4 1 8 5) <| .cons (carry s63 2 1 8 5) <|
    .cons (carry s118 1 0 2 1) <| .cons (carry s4 16 1 32 29) <| .cons (carry s3 16 1 32 29) <| .cons (carry s2 16 1 32 29) <|
    .cons (carry s40 8 1 16 13) <| .cons (carry s58 4 1 8 5) <| .cons (carry s39 8 1 16 13) <| .cons (carry s18 8 1 32 29) <|
    .cons (carry s17 8 1 32 29) <| .cons (carry s1 16 1 32 29) <| .cons (carry s0 16 1 32 29) <| .nil
  · decide

lemma gLeaf34 : BoxGood 8 0 32 30 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.both,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 8 0 32 30) <| .cons (carry s15 8 0 32 30) <| .cons (carry s14 8 0 32 30) <| .cons (carry s13 8 0 32 30) <|
    .cons (carry s12 8 0 32 30) <| .cons (carry s11 8 0 32 30) <| .cons (carry s10 8 0 32 30) <| .cons (carry s9 8 0 32 30) <|
    .cons (carry s8 8 0 32 30) <| .cons (carry s7 8 0 32 30) <| .cons (carry s6 8 0 32 30) <| .cons (carry s5 8 0 32 30) <|
    .cons s123 <| .cons unmarked <| .cons (carry s122 1 0 2 0) <| .cons (carry s115 1 0 4 2) <|
    .cons (carry s114 1 0 4 2) <| .cons (carry s113 1 0 4 2) <| .cons (carry s121 1 0 2 0) <| .cons (carry s62 2 0 8 6) <|
    .cons (carry s61 2 0 8 6) <| .cons (carry s60 2 0 8 6) <| .cons (carry s59 2 0 8 6) <| .cons (carry s63 1 0 8 6) <|
    .cons unmarked <| .cons (carry s4 8 0 32 30) <| .cons (carry s3 8 0 32 30) <| .cons (carry s2 8 0 32 30) <|
    .cons (carry s40 4 0 16 14) <| .cons (carry s58 2 0 8 6) <| .cons (carry s39 4 0 16 14) <| .cons (carry s18 4 0 32 30) <|
    .cons (carry s17 4 0 32 30) <| .cons (carry s1 8 0 32 30) <| .cons (carry s0 8 0 32 30) <| .nil
  · decide

lemma gLeaf35 : BoxGood 8 0 32 31 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.both,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 8 0 32 31) <| .cons (carry s15 8 0 32 31) <| .cons (carry s14 8 0 32 31) <| .cons (carry s13 8 0 32 31) <|
    .cons (carry s12 8 0 32 31) <| .cons (carry s11 8 0 32 31) <| .cons (carry s10 8 0 32 31) <| .cons (carry s9 8 0 32 31) <|
    .cons (carry s8 8 0 32 31) <| .cons (carry s7 8 0 32 31) <| .cons (carry s6 8 0 32 31) <| .cons (carry s5 8 0 32 31) <|
    .cons unmarked <| .cons s124 <| .cons (carry s122 1 0 2 1) <| .cons (carry s115 1 0 4 3) <|
    .cons (carry s114 1 0 4 3) <| .cons (carry s113 1 0 4 3) <| .cons (carry s121 1 0 2 1) <| .cons (carry s62 2 0 8 7) <|
    .cons (carry s61 2 0 8 7) <| .cons (carry s60 2 0 8 7) <| .cons (carry s59 2 0 8 7) <| .cons (carry s63 1 0 8 7) <|
    .cons unmarked <| .cons (carry s4 8 0 32 31) <| .cons (carry s3 8 0 32 31) <| .cons (carry s2 8 0 32 31) <|
    .cons (carry s40 4 0 16 15) <| .cons (carry s58 2 0 8 7) <| .cons (carry s39 4 0 16 15) <| .cons (carry s18 4 0 32 31) <|
    .cons (carry s17 4 0 32 31) <| .cons (carry s1 8 0 32 31) <| .cons (carry s0 8 0 32 31) <| .nil
  · decide

lemma gLeaf36 : BoxGood 16 2 16 12 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 16 2 16 12) <| .cons (carry s15 16 2 16 12) <| .cons (carry s14 16 2 16 12) <| .cons (carry s13 16 2 16 12) <|
    .cons (carry s12 16 2 16 12) <| .cons (carry s11 16 2 16 12) <| .cons (carry s10 16 2 16 12) <| .cons (carry s9 16 2 16 12) <|
    .cons (carry s8 16 2 16 12) <| .cons (carry s7 16 2 16 12) <| .cons (carry s6 16 2 16 12) <| .cons (carry s5 16 2 16 12) <|
    .cons (carry s126 2 0 4 0) <| .cons (carry s129 2 0 2 0) <| .cons (carry s128 2 0 2 0) <| .cons s133 <|
    .cons s132 <| .cons s131 <| .cons (carry s127 2 0 2 0) <| .cons (carry s62 4 2 4 0) <|
    .cons (carry s61 4 2 4 0) <| .cons (carry s60 4 2 4 0) <| .cons (carry s59 4 2 4 0) <| .cons (carry s130 1 0 2 0) <|
    .cons (carry s125 2 0 4 0) <| .cons (carry s4 16 2 16 12) <| .cons (carry s3 16 2 16 12) <| .cons (carry s2 16 2 16 12) <|
    .cons (carry s40 8 2 8 4) <| .cons (carry s58 4 2 4 0) <| .cons (carry s39 8 2 8 4) <| .cons (carry s18 8 2 16 12) <|
    .cons (carry s17 8 2 16 12) <| .cons (carry s1 16 2 16 12) <| .cons (carry s0 16 2 16 12) <| .nil
  · decide

lemma gLeaf37 : BoxGood 16 2 32 26 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 16 2 32 26) <| .cons (carry s15 16 2 32 26) <| .cons (carry s14 16 2 32 26) <| .cons (carry s13 16 2 32 26) <|
    .cons (carry s12 16 2 32 26) <| .cons (carry s11 16 2 32 26) <| .cons (carry s10 16 2 32 26) <| .cons (carry s9 16 2 32 26) <|
    .cons (carry s8 16 2 32 26) <| .cons (carry s7 16 2 32 26) <| .cons (carry s6 16 2 32 26) <| .cons (carry s5 16 2 32 26) <|
    .cons (carry s126 2 0 8 2) <| .cons (carry s129 2 0 4 2) <| .cons (carry s128 2 0 4 2) <| .cons s136 <|
    .cons s135 <| .cons s134 <| .cons (carry s127 2 0 4 2) <| .cons (carry s62 4 2 8 2) <|
    .cons (carry s61 4 2 8 2) <| .cons (carry s60 4 2 8 2) <| .cons (carry s59 4 2 8 2) <| .cons (carry s130 1 0 4 2) <|
    .cons (carry s125 2 0 8 2) <| .cons (carry s4 16 2 32 26) <| .cons (carry s3 16 2 32 26) <| .cons (carry s2 16 2 32 26) <|
    .cons (carry s40 8 2 16 10) <| .cons (carry s58 4 2 8 2) <| .cons (carry s39 8 2 16 10) <| .cons (carry s18 8 2 32 26) <|
    .cons (carry s17 8 2 32 26) <| .cons (carry s1 16 2 32 26) <| .cons (carry s0 16 2 32 26) <| .nil
  · decide

lemma gLeaf38 : BoxGood 16 2 64 54 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.up,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 16 2 64 54) <| .cons (carry s15 16 2 64 54) <| .cons (carry s14 16 2 64 54) <| .cons (carry s13 16 2 64 54) <|
    .cons (carry s12 16 2 64 54) <| .cons (carry s11 16 2 64 54) <| .cons (carry s10 16 2 64 54) <| .cons (carry s9 16 2 64 54) <|
    .cons (carry s8 16 2 64 54) <| .cons (carry s7 16 2 64 54) <| .cons (carry s6 16 2 64 54) <| .cons (carry s5 16 2 64 54) <|
    .cons (carry s126 2 0 16 6) <| .cons (carry s129 2 0 8 6) <| .cons (carry s128 2 0 8 6) <| .cons s138 <|
    .cons unmarked <| .cons s137 <| .cons (carry s127 2 0 8 6) <| .cons (carry s62 4 2 16 6) <|
    .cons (carry s61 4 2 16 6) <| .cons (carry s60 4 2 16 6) <| .cons (carry s59 4 2 16 6) <| .cons (carry s130 1 0 8 6) <|
    .cons (carry s125 2 0 16 6) <| .cons (carry s4 16 2 64 54) <| .cons (carry s3 16 2 64 54) <| .cons (carry s2 16 2 64 54) <|
    .cons (carry s40 8 2 32 22) <| .cons (carry s58 4 2 16 6) <| .cons (carry s39 8 2 32 22) <| .cons (carry s18 8 2 64 54) <|
    .cons (carry s17 8 2 64 54) <| .cons (carry s1 16 2 64 54) <| .cons (carry s0 16 2 64 54) <| .nil
  · decide

lemma gLeaf39 : BoxGood 32 4 128 110 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.both,.up,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 32 4 128 110) <| .cons (carry s15 32 4 128 110) <| .cons (carry s14 32 4 128 110) <| .cons (carry s13 32 4 128 110) <|
    .cons (carry s12 32 4 128 110) <| .cons (carry s11 32 4 128 110) <| .cons (carry s10 32 4 128 110) <| .cons (carry s9 32 4 128 110) <|
    .cons (carry s8 32 4 128 110) <| .cons (carry s7 32 4 128 110) <| .cons (carry s6 32 4 128 110) <| .cons (carry s5 32 4 128 110) <|
    .cons (carry s126 4 0 32 14) <| .cons (carry s129 4 0 16 14) <| .cons (carry s128 4 0 16 14) <| .cons unmarked <|
    .cons unmarked <| .cons s139 <| .cons (carry s127 4 0 16 14) <| .cons (carry s62 8 4 32 14) <|
    .cons (carry s61 8 4 32 14) <| .cons (carry s60 8 4 32 14) <| .cons (carry s59 8 4 32 14) <| .cons (carry s130 2 0 16 14) <|
    .cons (carry s125 4 0 32 14) <| .cons (carry s4 32 4 128 110) <| .cons (carry s3 32 4 128 110) <| .cons (carry s2 32 4 128 110) <|
    .cons (carry s40 16 4 64 46) <| .cons (carry s58 8 4 32 14) <| .cons (carry s39 16 4 64 46) <| .cons (carry s18 16 4 128 110) <|
    .cons (carry s17 16 4 128 110) <| .cons (carry s1 32 4 128 110) <| .cons (carry s0 32 4 128 110) <| .nil
  · decide

lemma gLeaf40 : BoxGood 64 8 128 111 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.both,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 64 8 128 111) <| .cons (carry s15 64 8 128 111) <| .cons (carry s14 64 8 128 111) <| .cons (carry s13 64 8 128 111) <|
    .cons (carry s12 64 8 128 111) <| .cons (carry s11 64 8 128 111) <| .cons (carry s10 64 8 128 111) <| .cons (carry s9 64 8 128 111) <|
    .cons (carry s8 64 8 128 111) <| .cons (carry s7 64 8 128 111) <| .cons (carry s6 64 8 128 111) <| .cons (carry s5 64 8 128 111) <|
    .cons (carry s126 8 0 32 15) <| .cons (carry s129 8 0 16 15) <| .cons (carry s128 8 0 16 15) <| .cons unmarked <|
    .cons s140 <| .cons unmarked <| .cons (carry s127 8 0 16 15) <| .cons (carry s62 16 8 32 15) <|
    .cons (carry s61 16 8 32 15) <| .cons (carry s60 16 8 32 15) <| .cons (carry s59 16 8 32 15) <| .cons (carry s130 4 0 16 15) <|
    .cons (carry s125 8 0 32 15) <| .cons (carry s4 64 8 128 111) <| .cons (carry s3 64 8 128 111) <| .cons (carry s2 64 8 128 111) <|
    .cons (carry s40 32 8 64 47) <| .cons (carry s58 16 8 32 15) <| .cons (carry s39 32 8 64 47) <| .cons (carry s18 32 8 128 111) <|
    .cons (carry s17 32 8 128 111) <| .cons (carry s1 64 8 128 111) <| .cons (carry s0 64 8 128 111) <| .nil
  · decide

lemma gLeaf41 : BoxGood 64 9 128 111 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.both,.up,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 64 9 128 111) <| .cons (carry s15 64 9 128 111) <| .cons (carry s14 64 9 128 111) <| .cons (carry s13 64 9 128 111) <|
    .cons (carry s12 64 9 128 111) <| .cons (carry s11 64 9 128 111) <| .cons (carry s10 64 9 128 111) <| .cons (carry s9 64 9 128 111) <|
    .cons (carry s8 64 9 128 111) <| .cons (carry s7 64 9 128 111) <| .cons (carry s6 64 9 128 111) <| .cons (carry s5 64 9 128 111) <|
    .cons (carry s126 8 1 32 15) <| .cons (carry s129 8 1 16 15) <| .cons (carry s128 8 1 16 15) <| .cons unmarked <|
    .cons unmarked <| .cons s141 <| .cons (carry s127 8 1 16 15) <| .cons (carry s62 16 9 32 15) <|
    .cons (carry s61 16 9 32 15) <| .cons (carry s60 16 9 32 15) <| .cons (carry s59 16 9 32 15) <| .cons (carry s130 4 1 16 15) <|
    .cons (carry s125 8 1 32 15) <| .cons (carry s4 64 9 128 111) <| .cons (carry s3 64 9 128 111) <| .cons (carry s2 64 9 128 111) <|
    .cons (carry s40 32 9 64 47) <| .cons (carry s58 16 9 32 15) <| .cons (carry s39 32 9 64 47) <| .cons (carry s18 32 9 128 111) <|
    .cons (carry s17 32 9 128 111) <| .cons (carry s1 64 9 128 111) <| .cons (carry s0 64 9 128 111) <| .nil
  · decide

lemma gLeaf42 : BoxGood 32 5 64 55 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.up,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 32 5 64 55) <| .cons (carry s15 32 5 64 55) <| .cons (carry s14 32 5 64 55) <| .cons (carry s13 32 5 64 55) <|
    .cons (carry s12 32 5 64 55) <| .cons (carry s11 32 5 64 55) <| .cons (carry s10 32 5 64 55) <| .cons (carry s9 32 5 64 55) <|
    .cons (carry s8 32 5 64 55) <| .cons (carry s7 32 5 64 55) <| .cons (carry s6 32 5 64 55) <| .cons (carry s5 32 5 64 55) <|
    .cons (carry s126 4 1 16 7) <| .cons (carry s129 4 1 8 7) <| .cons (carry s128 4 1 8 7) <| .cons s143 <|
    .cons unmarked <| .cons s142 <| .cons (carry s127 4 1 8 7) <| .cons (carry s62 8 5 16 7) <|
    .cons (carry s61 8 5 16 7) <| .cons (carry s60 8 5 16 7) <| .cons (carry s59 8 5 16 7) <| .cons (carry s130 2 1 8 7) <|
    .cons (carry s125 4 1 16 7) <| .cons (carry s4 32 5 64 55) <| .cons (carry s3 32 5 64 55) <| .cons (carry s2 32 5 64 55) <|
    .cons (carry s40 16 5 32 23) <| .cons (carry s58 8 5 16 7) <| .cons (carry s39 16 5 32 23) <| .cons (carry s18 16 5 64 55) <|
    .cons (carry s17 16 5 64 55) <| .cons (carry s1 32 5 64 55) <| .cons (carry s0 32 5 64 55) <| .nil
  · decide

lemma gLeaf43 : BoxGood 16 3 8 6 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 16 3 8 6) <| .cons (carry s15 16 3 8 6) <| .cons (carry s14 16 3 8 6) <| .cons (carry s13 16 3 8 6) <|
    .cons (carry s12 16 3 8 6) <| .cons (carry s11 16 3 8 6) <| .cons (carry s10 16 3 8 6) <| .cons (carry s9 16 3 8 6) <|
    .cons (carry s8 16 3 8 6) <| .cons (carry s7 16 3 8 6) <| .cons (carry s6 16 3 8 6) <| .cons (carry s5 16 3 8 6) <|
    .cons (carry s126 2 1 2 0) <| .cons (carry s129 2 1 1 0) <| .cons (carry s128 2 1 1 0) <| .cons s146 <|
    .cons s145 <| .cons s144 <| .cons (carry s127 2 1 1 0) <| .cons (carry s62 4 3 2 0) <|
    .cons (carry s61 4 3 2 0) <| .cons (carry s60 4 3 2 0) <| .cons (carry s59 4 3 2 0) <| .cons unmarked <|
    .cons (carry s125 2 1 2 0) <| .cons (carry s4 16 3 8 6) <| .cons (carry s3 16 3 8 6) <| .cons (carry s2 16 3 8 6) <|
    .cons (carry s40 8 3 4 2) <| .cons (carry s58 4 3 2 0) <| .cons (carry s39 8 3 4 2) <| .cons (carry s18 8 3 8 6) <|
    .cons (carry s17 8 3 8 6) <| .cons (carry s1 16 3 8 6) <| .cons (carry s0 16 3 8 6) <| .nil
  · decide

lemma gLeaf44 : BoxGood 32 4 64 56 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.both,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 32 4 64 56) <| .cons (carry s15 32 4 64 56) <| .cons (carry s14 32 4 64 56) <| .cons (carry s13 32 4 64 56) <|
    .cons (carry s12 32 4 64 56) <| .cons (carry s11 32 4 64 56) <| .cons (carry s10 32 4 64 56) <| .cons (carry s9 32 4 64 56) <|
    .cons (carry s8 32 4 64 56) <| .cons (carry s7 32 4 64 56) <| .cons (carry s6 32 4 64 56) <| .cons (carry s5 32 4 64 56) <|
    .cons (carry s126 4 0 16 8) <| .cons (carry s147 4 0 4 0) <| .cons (carry s150 2 0 1 0) <| .cons unmarked <|
    .cons s151 <| .cons unmarked <| .cons (carry s149 2 0 2 0) <| .cons (carry s62 8 4 16 8) <|
    .cons (carry s61 8 4 16 8) <| .cons (carry s60 8 4 16 8) <| .cons (carry s59 8 4 16 8) <| .cons (carry s148 2 0 4 0) <|
    .cons (carry s125 4 0 16 8) <| .cons (carry s4 32 4 64 56) <| .cons (carry s3 32 4 64 56) <| .cons (carry s2 32 4 64 56) <|
    .cons (carry s40 16 4 32 24) <| .cons (carry s58 8 4 16 8) <| .cons (carry s39 16 4 32 24) <| .cons (carry s18 16 4 64 56) <|
    .cons (carry s17 16 4 64 56) <| .cons (carry s1 32 4 64 56) <| .cons (carry s0 32 4 64 56) <| .nil
  · decide

lemma gLeaf45 : BoxGood 32 5 128 112 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.both,.up,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 32 5 128 112) <| .cons (carry s15 32 5 128 112) <| .cons (carry s14 32 5 128 112) <| .cons (carry s13 32 5 128 112) <|
    .cons (carry s12 32 5 128 112) <| .cons (carry s11 32 5 128 112) <| .cons (carry s10 32 5 128 112) <| .cons (carry s9 32 5 128 112) <|
    .cons (carry s8 32 5 128 112) <| .cons (carry s7 32 5 128 112) <| .cons (carry s6 32 5 128 112) <| .cons (carry s5 32 5 128 112) <|
    .cons (carry s126 4 1 32 16) <| .cons (carry s147 4 1 8 0) <| .cons (carry s150 2 1 2 0) <| .cons unmarked <|
    .cons unmarked <| .cons s152 <| .cons (carry s149 2 1 4 0) <| .cons (carry s62 8 5 32 16) <|
    .cons (carry s61 8 5 32 16) <| .cons (carry s60 8 5 32 16) <| .cons (carry s59 8 5 32 16) <| .cons (carry s148 2 1 8 0) <|
    .cons (carry s125 4 1 32 16) <| .cons (carry s4 32 5 128 112) <| .cons (carry s3 32 5 128 112) <| .cons (carry s2 32 5 128 112) <|
    .cons (carry s40 16 5 64 48) <| .cons (carry s58 8 5 32 16) <| .cons (carry s39 16 5 64 48) <| .cons (carry s18 16 5 128 112) <|
    .cons (carry s17 16 5 128 112) <| .cons (carry s1 32 5 128 112) <| .cons (carry s0 32 5 128 112) <| .nil
  · decide

lemma gLeaf46 : BoxGood 64 10 128 113 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.both,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 64 10 128 113) <| .cons (carry s15 64 10 128 113) <| .cons (carry s14 64 10 128 113) <| .cons (carry s13 64 10 128 113) <|
    .cons (carry s12 64 10 128 113) <| .cons (carry s11 64 10 128 113) <| .cons (carry s10 64 10 128 113) <| .cons (carry s9 64 10 128 113) <|
    .cons (carry s8 64 10 128 113) <| .cons (carry s7 64 10 128 113) <| .cons (carry s6 64 10 128 113) <| .cons (carry s5 64 10 128 113) <|
    .cons (carry s126 8 2 32 17) <| .cons (carry s147 8 2 8 1) <| .cons (carry s150 4 2 2 1) <| .cons unmarked <|
    .cons s153 <| .cons unmarked <| .cons (carry s149 4 2 4 1) <| .cons (carry s62 16 10 32 17) <|
    .cons (carry s61 16 10 32 17) <| .cons (carry s60 16 10 32 17) <| .cons (carry s59 16 10 32 17) <| .cons (carry s148 4 2 8 1) <|
    .cons (carry s125 8 2 32 17) <| .cons (carry s4 64 10 128 113) <| .cons (carry s3 64 10 128 113) <| .cons (carry s2 64 10 128 113) <|
    .cons (carry s40 32 10 64 49) <| .cons (carry s58 16 10 32 17) <| .cons (carry s39 32 10 64 49) <| .cons (carry s18 32 10 128 113) <|
    .cons (carry s17 32 10 128 113) <| .cons (carry s1 64 10 128 113) <| .cons (carry s0 64 10 128 113) <| .nil
  · decide

lemma gLeaf47 : BoxGood 64 11 256 226 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.up,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 64 11 256 226) <| .cons (carry s15 64 11 256 226) <| .cons (carry s14 64 11 256 226) <| .cons (carry s13 64 11 256 226) <|
    .cons (carry s12 64 11 256 226) <| .cons (carry s11 64 11 256 226) <| .cons (carry s10 64 11 256 226) <| .cons (carry s9 64 11 256 226) <|
    .cons (carry s8 64 11 256 226) <| .cons (carry s7 64 11 256 226) <| .cons (carry s6 64 11 256 226) <| .cons (carry s5 64 11 256 226) <|
    .cons (carry s126 8 3 64 34) <| .cons (carry s147 8 3 16 2) <| .cons (carry s150 4 3 4 2) <| .cons s155 <|
    .cons unmarked <| .cons s154 <| .cons (carry s149 4 3 8 2) <| .cons (carry s62 16 11 64 34) <|
    .cons (carry s61 16 11 64 34) <| .cons (carry s60 16 11 64 34) <| .cons (carry s59 16 11 64 34) <| .cons (carry s148 4 3 16 2) <|
    .cons (carry s125 8 3 64 34) <| .cons (carry s4 64 11 256 226) <| .cons (carry s3 64 11 256 226) <| .cons (carry s2 64 11 256 226) <|
    .cons (carry s40 32 11 128 98) <| .cons (carry s58 16 11 64 34) <| .cons (carry s39 32 11 128 98) <| .cons (carry s18 32 11 256 226) <|
    .cons (carry s17 32 11 256 226) <| .cons (carry s1 64 11 256 226) <| .cons (carry s0 64 11 256 226) <| .nil
  · decide

lemma gLeaf48 : BoxGood 64 11 256 227 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.both,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 64 11 256 227) <| .cons (carry s15 64 11 256 227) <| .cons (carry s14 64 11 256 227) <| .cons (carry s13 64 11 256 227) <|
    .cons (carry s12 64 11 256 227) <| .cons (carry s11 64 11 256 227) <| .cons (carry s10 64 11 256 227) <| .cons (carry s9 64 11 256 227) <|
    .cons (carry s8 64 11 256 227) <| .cons (carry s7 64 11 256 227) <| .cons (carry s6 64 11 256 227) <| .cons (carry s5 64 11 256 227) <|
    .cons (carry s126 8 3 64 35) <| .cons (carry s147 8 3 16 3) <| .cons (carry s150 4 3 4 3) <| .cons unmarked <|
    .cons s156 <| .cons unmarked <| .cons (carry s149 4 3 8 3) <| .cons (carry s62 16 11 64 35) <|
    .cons (carry s61 16 11 64 35) <| .cons (carry s60 16 11 64 35) <| .cons (carry s59 16 11 64 35) <| .cons (carry s148 4 3 16 3) <|
    .cons (carry s125 8 3 64 35) <| .cons (carry s4 64 11 256 227) <| .cons (carry s3 64 11 256 227) <| .cons (carry s2 64 11 256 227) <|
    .cons (carry s40 32 11 128 99) <| .cons (carry s58 16 11 64 35) <| .cons (carry s39 32 11 128 99) <| .cons (carry s18 32 11 256 227) <|
    .cons (carry s17 32 11 256 227) <| .cons (carry s1 64 11 256 227) <| .cons (carry s0 64 11 256 227) <| .nil
  · decide

lemma gLeaf49 : BoxGood 32 4 64 57 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.down,.down,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 32 4 64 57) <| .cons (carry s15 32 4 64 57) <| .cons (carry s14 32 4 64 57) <| .cons (carry s13 32 4 64 57) <|
    .cons (carry s12 32 4 64 57) <| .cons (carry s11 32 4 64 57) <| .cons (carry s10 32 4 64 57) <| .cons (carry s9 32 4 64 57) <|
    .cons (carry s8 32 4 64 57) <| .cons (carry s7 32 4 64 57) <| .cons (carry s6 32 4 64 57) <| .cons (carry s5 32 4 64 57) <|
    .cons (carry s126 4 0 16 9) <| .cons (carry s147 4 0 4 1) <| .cons unmarked <| .cons s159 <|
    .cons (carry s157 2 0 1 0) <| .cons s158 <| .cons (carry s149 2 0 2 1) <| .cons (carry s62 8 4 16 9) <|
    .cons (carry s61 8 4 16 9) <| .cons (carry s60 8 4 16 9) <| .cons (carry s59 8 4 16 9) <| .cons (carry s148 2 0 4 1) <|
    .cons (carry s125 4 0 16 9) <| .cons (carry s4 32 4 64 57) <| .cons (carry s3 32 4 64 57) <| .cons (carry s2 32 4 64 57) <|
    .cons (carry s40 16 4 32 25) <| .cons (carry s58 8 4 16 9) <| .cons (carry s39 16 4 32 25) <| .cons (carry s18 16 4 64 57) <|
    .cons (carry s17 16 4 64 57) <| .cons (carry s1 32 4 64 57) <| .cons (carry s0 32 4 64 57) <| .nil
  · decide

lemma gLeaf50 : BoxGood 32 5 64 57 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.both,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 32 5 64 57) <| .cons (carry s15 32 5 64 57) <| .cons (carry s14 32 5 64 57) <| .cons (carry s13 32 5 64 57) <|
    .cons (carry s12 32 5 64 57) <| .cons (carry s11 32 5 64 57) <| .cons (carry s10 32 5 64 57) <| .cons (carry s9 32 5 64 57) <|
    .cons (carry s8 32 5 64 57) <| .cons (carry s7 32 5 64 57) <| .cons (carry s6 32 5 64 57) <| .cons (carry s5 32 5 64 57) <|
    .cons (carry s126 4 1 16 9) <| .cons (carry s147 4 1 4 1) <| .cons s160 <| .cons unmarked <|
    .cons (carry s157 2 1 1 0) <| .cons unmarked <| .cons (carry s149 2 1 2 1) <| .cons (carry s62 8 5 16 9) <|
    .cons (carry s61 8 5 16 9) <| .cons (carry s60 8 5 16 9) <| .cons (carry s59 8 5 16 9) <| .cons (carry s148 2 1 4 1) <|
    .cons (carry s125 4 1 16 9) <| .cons (carry s4 32 5 64 57) <| .cons (carry s3 32 5 64 57) <| .cons (carry s2 32 5 64 57) <|
    .cons (carry s40 16 5 32 25) <| .cons (carry s58 8 5 16 9) <| .cons (carry s39 16 5 32 25) <| .cons (carry s18 16 5 64 57) <|
    .cons (carry s17 16 5 64 57) <| .cons (carry s1 32 5 64 57) <| .cons (carry s0 32 5 64 57) <| .nil
  · decide

lemma gLeaf51 : BoxGood 16 2 32 29 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.down,.down,.both,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 16 2 32 29) <| .cons (carry s15 16 2 32 29) <| .cons (carry s14 16 2 32 29) <| .cons (carry s13 16 2 32 29) <|
    .cons (carry s12 16 2 32 29) <| .cons (carry s11 16 2 32 29) <| .cons (carry s10 16 2 32 29) <| .cons (carry s9 16 2 32 29) <|
    .cons (carry s8 16 2 32 29) <| .cons (carry s7 16 2 32 29) <| .cons (carry s6 16 2 32 29) <| .cons (carry s5 16 2 32 29) <|
    .cons (carry s126 2 0 8 5) <| .cons (carry s147 2 0 2 1) <| .cons unmarked <| .cons s163 <|
    .cons s162 <| .cons s161 <| .cons unmarked <| .cons (carry s62 4 2 8 5) <|
    .cons (carry s61 4 2 8 5) <| .cons (carry s60 4 2 8 5) <| .cons (carry s59 4 2 8 5) <| .cons (carry s148 1 0 2 1) <|
    .cons (carry s125 2 0 8 5) <| .cons (carry s4 16 2 32 29) <| .cons (carry s3 16 2 32 29) <| .cons (carry s2 16 2 32 29) <|
    .cons (carry s40 8 2 16 13) <| .cons (carry s58 4 2 8 5) <| .cons (carry s39 8 2 16 13) <| .cons (carry s18 8 2 32 29) <|
    .cons (carry s17 8 2 32 29) <| .cons (carry s1 16 2 32 29) <| .cons (carry s0 16 2 32 29) <| .nil
  · decide

lemma gLeaf52 : BoxGood 32 6 64 56 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.up,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 32 6 64 56) <| .cons (carry s15 32 6 64 56) <| .cons (carry s14 32 6 64 56) <| .cons (carry s13 32 6 64 56) <|
    .cons (carry s12 32 6 64 56) <| .cons (carry s11 32 6 64 56) <| .cons (carry s10 32 6 64 56) <| .cons (carry s9 32 6 64 56) <|
    .cons (carry s8 32 6 64 56) <| .cons (carry s7 32 6 64 56) <| .cons (carry s6 32 6 64 56) <| .cons (carry s5 32 6 64 56) <|
    .cons (carry s126 4 2 16 8) <| .cons (carry s147 4 2 4 0) <| .cons (carry s165 2 0 4 0) <| .cons s168 <|
    .cons unmarked <| .cons s167 <| .cons (carry s164 2 0 4 0) <| .cons (carry s62 8 6 16 8) <|
    .cons (carry s61 8 6 16 8) <| .cons (carry s60 8 6 16 8) <| .cons (carry s59 8 6 16 8) <| .cons (carry s166 1 0 4 0) <|
    .cons (carry s125 4 2 16 8) <| .cons (carry s4 32 6 64 56) <| .cons (carry s3 32 6 64 56) <| .cons (carry s2 32 6 64 56) <|
    .cons (carry s40 16 6 32 24) <| .cons (carry s58 8 6 16 8) <| .cons (carry s39 16 6 32 24) <| .cons (carry s18 16 6 64 56) <|
    .cons (carry s17 16 6 64 56) <| .cons (carry s1 32 6 64 56) <| .cons (carry s0 32 6 64 56) <| .nil
  · decide

lemma gLeaf53 : BoxGood 32 6 128 114 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.both,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 32 6 128 114) <| .cons (carry s15 32 6 128 114) <| .cons (carry s14 32 6 128 114) <| .cons (carry s13 32 6 128 114) <|
    .cons (carry s12 32 6 128 114) <| .cons (carry s11 32 6 128 114) <| .cons (carry s10 32 6 128 114) <| .cons (carry s9 32 6 128 114) <|
    .cons (carry s8 32 6 128 114) <| .cons (carry s7 32 6 128 114) <| .cons (carry s6 32 6 128 114) <| .cons (carry s5 32 6 128 114) <|
    .cons (carry s126 4 2 32 18) <| .cons (carry s147 4 2 8 2) <| .cons (carry s165 2 0 8 2) <| .cons s169 <|
    .cons unmarked <| .cons unmarked <| .cons (carry s164 2 0 8 2) <| .cons (carry s62 8 6 32 18) <|
    .cons (carry s61 8 6 32 18) <| .cons (carry s60 8 6 32 18) <| .cons (carry s59 8 6 32 18) <| .cons (carry s166 1 0 8 2) <|
    .cons (carry s125 4 2 32 18) <| .cons (carry s4 32 6 128 114) <| .cons (carry s3 32 6 128 114) <| .cons (carry s2 32 6 128 114) <|
    .cons (carry s40 16 6 64 50) <| .cons (carry s58 8 6 32 18) <| .cons (carry s39 16 6 64 50) <| .cons (carry s18 16 6 128 114) <|
    .cons (carry s17 16 6 128 114) <| .cons (carry s1 32 6 128 114) <| .cons (carry s0 32 6 128 114) <| .nil
  · decide

lemma gLeaf54 : BoxGood 32 6 128 115 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.both,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 32 6 128 115) <| .cons (carry s15 32 6 128 115) <| .cons (carry s14 32 6 128 115) <| .cons (carry s13 32 6 128 115) <|
    .cons (carry s12 32 6 128 115) <| .cons (carry s11 32 6 128 115) <| .cons (carry s10 32 6 128 115) <| .cons (carry s9 32 6 128 115) <|
    .cons (carry s8 32 6 128 115) <| .cons (carry s7 32 6 128 115) <| .cons (carry s6 32 6 128 115) <| .cons (carry s5 32 6 128 115) <|
    .cons (carry s126 4 2 32 19) <| .cons (carry s147 4 2 8 3) <| .cons (carry s165 2 0 8 3) <| .cons unmarked <|
    .cons s170 <| .cons unmarked <| .cons (carry s164 2 0 8 3) <| .cons (carry s62 8 6 32 19) <|
    .cons (carry s61 8 6 32 19) <| .cons (carry s60 8 6 32 19) <| .cons (carry s59 8 6 32 19) <| .cons (carry s166 1 0 8 3) <|
    .cons (carry s125 4 2 32 19) <| .cons (carry s4 32 6 128 115) <| .cons (carry s3 32 6 128 115) <| .cons (carry s2 32 6 128 115) <|
    .cons (carry s40 16 6 64 51) <| .cons (carry s58 8 6 32 19) <| .cons (carry s39 16 6 64 51) <| .cons (carry s18 16 6 128 115) <|
    .cons (carry s17 16 6 128 115) <| .cons (carry s1 32 6 128 115) <| .cons (carry s0 32 6 128 115) <| .nil
  · decide

lemma gLeaf55 : BoxGood 32 6 32 29 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.both,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 32 6 32 29) <| .cons (carry s15 32 6 32 29) <| .cons (carry s14 32 6 32 29) <| .cons (carry s13 32 6 32 29) <|
    .cons (carry s12 32 6 32 29) <| .cons (carry s11 32 6 32 29) <| .cons (carry s10 32 6 32 29) <| .cons (carry s9 32 6 32 29) <|
    .cons (carry s8 32 6 32 29) <| .cons (carry s7 32 6 32 29) <| .cons (carry s6 32 6 32 29) <| .cons (carry s5 32 6 32 29) <|
    .cons (carry s126 4 2 8 5) <| .cons (carry s147 4 2 2 1) <| .cons (carry s165 2 0 2 1) <| .cons unmarked <|
    .cons s171 <| .cons unmarked <| .cons (carry s164 2 0 2 1) <| .cons (carry s62 8 6 8 5) <|
    .cons (carry s61 8 6 8 5) <| .cons (carry s60 8 6 8 5) <| .cons (carry s59 8 6 8 5) <| .cons (carry s166 1 0 2 1) <|
    .cons (carry s125 4 2 8 5) <| .cons (carry s4 32 6 32 29) <| .cons (carry s3 32 6 32 29) <| .cons (carry s2 32 6 32 29) <|
    .cons (carry s40 16 6 16 13) <| .cons (carry s58 8 6 8 5) <| .cons (carry s39 16 6 16 13) <| .cons (carry s18 16 6 32 29) <|
    .cons (carry s17 16 6 32 29) <| .cons (carry s1 32 6 32 29) <| .cons (carry s0 32 6 32 29) <| .nil
  · decide

lemma gLeaf56 : BoxGood 32 7 32 28 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.up,.up,.up,.up,.up,.up,.both,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 32 7 32 28) <| .cons (carry s15 32 7 32 28) <| .cons (carry s14 32 7 32 28) <| .cons (carry s13 32 7 32 28) <|
    .cons (carry s12 32 7 32 28) <| .cons (carry s11 32 7 32 28) <| .cons (carry s10 32 7 32 28) <| .cons (carry s9 32 7 32 28) <|
    .cons (carry s8 32 7 32 28) <| .cons (carry s7 32 7 32 28) <| .cons (carry s6 32 7 32 28) <| .cons (carry s5 32 7 32 28) <|
    .cons (carry s126 4 3 8 4) <| .cons (carry s147 4 3 2 0) <| .cons (carry s165 2 1 2 0) <| .cons s173 <|
    .cons unmarked <| .cons s172 <| .cons (carry s164 2 1 2 0) <| .cons (carry s62 8 7 8 4) <|
    .cons (carry s61 8 7 8 4) <| .cons (carry s60 8 7 8 4) <| .cons (carry s59 8 7 8 4) <| .cons unmarked <|
    .cons (carry s125 4 3 8 4) <| .cons (carry s4 32 7 32 28) <| .cons (carry s3 32 7 32 28) <| .cons (carry s2 32 7 32 28) <|
    .cons (carry s40 16 7 16 12) <| .cons (carry s58 8 7 8 4) <| .cons (carry s39 16 7 16 12) <| .cons (carry s18 16 7 32 28) <|
    .cons (carry s17 16 7 32 28) <| .cons (carry s1 32 7 32 28) <| .cons (carry s0 32 7 32 28) <| .nil
  · decide

lemma gLeaf57 : BoxGood 64 14 32 29 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.both,.up,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 64 14 32 29) <| .cons (carry s15 64 14 32 29) <| .cons (carry s14 64 14 32 29) <| .cons (carry s13 64 14 32 29) <|
    .cons (carry s12 64 14 32 29) <| .cons (carry s11 64 14 32 29) <| .cons (carry s10 64 14 32 29) <| .cons (carry s9 64 14 32 29) <|
    .cons (carry s8 64 14 32 29) <| .cons (carry s7 64 14 32 29) <| .cons (carry s6 64 14 32 29) <| .cons (carry s5 64 14 32 29) <|
    .cons (carry s126 8 6 8 5) <| .cons (carry s147 8 6 2 1) <| .cons (carry s165 4 2 2 1) <| .cons unmarked <|
    .cons s175 <| .cons unmarked <| .cons (carry s164 4 2 2 1) <| .cons (carry s62 16 14 8 5) <|
    .cons (carry s61 16 14 8 5) <| .cons (carry s60 16 14 8 5) <| .cons (carry s59 16 14 8 5) <| .cons s174 <|
    .cons (carry s125 8 6 8 5) <| .cons (carry s4 64 14 32 29) <| .cons (carry s3 64 14 32 29) <| .cons (carry s2 64 14 32 29) <|
    .cons (carry s40 32 14 16 13) <| .cons (carry s58 16 14 8 5) <| .cons (carry s39 32 14 16 13) <| .cons (carry s18 32 14 32 29) <|
    .cons (carry s17 32 14 32 29) <| .cons (carry s1 64 14 32 29) <| .cons (carry s0 64 14 32 29) <| .nil
  · decide

lemma gLeaf58 : BoxGood 64 15 64 58 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.both,.up,.up,.up,.up,.up,.both,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 64 15 64 58) <| .cons (carry s15 64 15 64 58) <| .cons (carry s14 64 15 64 58) <| .cons (carry s13 64 15 64 58) <|
    .cons (carry s12 64 15 64 58) <| .cons (carry s11 64 15 64 58) <| .cons (carry s10 64 15 64 58) <| .cons (carry s9 64 15 64 58) <|
    .cons (carry s8 64 15 64 58) <| .cons (carry s7 64 15 64 58) <| .cons (carry s6 64 15 64 58) <| .cons (carry s5 64 15 64 58) <|
    .cons (carry s126 8 7 16 10) <| .cons (carry s147 8 7 4 2) <| .cons (carry s165 4 3 4 2) <| .cons s176 <|
    .cons unmarked <| .cons unmarked <| .cons (carry s164 4 3 4 2) <| .cons (carry s62 16 15 16 10) <|
    .cons (carry s61 16 15 16 10) <| .cons (carry s60 16 15 16 10) <| .cons (carry s59 16 15 16 10) <| .cons unmarked <|
    .cons (carry s125 8 7 16 10) <| .cons (carry s4 64 15 64 58) <| .cons (carry s3 64 15 64 58) <| .cons (carry s2 64 15 64 58) <|
    .cons (carry s40 32 15 32 26) <| .cons (carry s58 16 15 16 10) <| .cons (carry s39 32 15 32 26) <| .cons (carry s18 32 15 64 58) <|
    .cons (carry s17 32 15 64 58) <| .cons (carry s1 64 15 64 58) <| .cons (carry s0 64 15 64 58) <| .nil
  · decide

lemma gLeaf59 : BoxGood 64 15 64 59 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.down,.up,.up,.up,.up,.up,.both,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 64 15 64 59) <| .cons (carry s15 64 15 64 59) <| .cons (carry s14 64 15 64 59) <| .cons (carry s13 64 15 64 59) <|
    .cons (carry s12 64 15 64 59) <| .cons (carry s11 64 15 64 59) <| .cons (carry s10 64 15 64 59) <| .cons (carry s9 64 15 64 59) <|
    .cons (carry s8 64 15 64 59) <| .cons (carry s7 64 15 64 59) <| .cons (carry s6 64 15 64 59) <| .cons (carry s5 64 15 64 59) <|
    .cons (carry s126 8 7 16 11) <| .cons (carry s147 8 7 4 3) <| .cons (carry s165 4 3 4 3) <| .cons unmarked <|
    .cons s178 <| .cons s177 <| .cons (carry s164 4 3 4 3) <| .cons (carry s62 16 15 16 11) <|
    .cons (carry s61 16 15 16 11) <| .cons (carry s60 16 15 16 11) <| .cons (carry s59 16 15 16 11) <| .cons unmarked <|
    .cons (carry s125 8 7 16 11) <| .cons (carry s4 64 15 64 59) <| .cons (carry s3 64 15 64 59) <| .cons (carry s2 64 15 64 59) <|
    .cons (carry s40 32 15 32 27) <| .cons (carry s58 16 15 16 11) <| .cons (carry s39 32 15 32 27) <| .cons (carry s18 32 15 64 59) <|
    .cons (carry s17 32 15 64 59) <| .cons (carry s1 64 15 64 59) <| .cons (carry s0 64 15 64 59) <| .nil
  · decide

lemma gLeaf60 : BoxGood 32 4 16 15 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 32 4 16 15) <| .cons (carry s15 32 4 16 15) <| .cons (carry s14 32 4 16 15) <| .cons (carry s13 32 4 16 15) <|
    .cons (carry s12 32 4 16 15) <| .cons (carry s11 32 4 16 15) <| .cons (carry s10 32 4 16 15) <| .cons (carry s9 32 4 16 15) <|
    .cons (carry s8 32 4 16 15) <| .cons (carry s7 32 4 16 15) <| .cons (carry s6 32 4 16 15) <| .cons (carry s5 32 4 16 15) <|
    .cons (carry s126 4 0 4 3) <| .cons unmarked <| .cons s184 <| .cons (carry s181 4 0 1 0) <|
    .cons (carry s180 4 0 1 0) <| .cons (carry s179 4 0 1 0) <| .cons s183 <| .cons (carry s62 8 4 4 3) <|
    .cons (carry s61 8 4 4 3) <| .cons (carry s60 8 4 4 3) <| .cons (carry s59 8 4 4 3) <| .cons (carry s182 2 0 1 0) <|
    .cons (carry s125 4 0 4 3) <| .cons (carry s4 32 4 16 15) <| .cons (carry s3 32 4 16 15) <| .cons (carry s2 32 4 16 15) <|
    .cons (carry s40 16 4 8 7) <| .cons (carry s58 8 4 4 3) <| .cons (carry s39 16 4 8 7) <| .cons (carry s18 16 4 16 15) <|
    .cons (carry s17 16 4 16 15) <| .cons (carry s1 32 4 16 15) <| .cons (carry s0 32 4 16 15) <| .nil
  · decide

lemma gLeaf61 : BoxGood 32 5 32 30 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.down,.down,.both,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 32 5 32 30) <| .cons (carry s15 32 5 32 30) <| .cons (carry s14 32 5 32 30) <| .cons (carry s13 32 5 32 30) <|
    .cons (carry s12 32 5 32 30) <| .cons (carry s11 32 5 32 30) <| .cons (carry s10 32 5 32 30) <| .cons (carry s9 32 5 32 30) <|
    .cons (carry s8 32 5 32 30) <| .cons (carry s7 32 5 32 30) <| .cons (carry s6 32 5 32 30) <| .cons (carry s5 32 5 32 30) <|
    .cons (carry s126 4 1 8 6) <| .cons s185 <| .cons unmarked <| .cons (carry s181 4 1 2 0) <|
    .cons (carry s180 4 1 2 0) <| .cons (carry s179 4 1 2 0) <| .cons unmarked <| .cons (carry s62 8 5 8 6) <|
    .cons (carry s61 8 5 8 6) <| .cons (carry s60 8 5 8 6) <| .cons (carry s59 8 5 8 6) <| .cons (carry s182 2 1 2 0) <|
    .cons (carry s125 4 1 8 6) <| .cons (carry s4 32 5 32 30) <| .cons (carry s3 32 5 32 30) <| .cons (carry s2 32 5 32 30) <|
    .cons (carry s40 16 5 16 14) <| .cons (carry s58 8 5 8 6) <| .cons (carry s39 16 5 16 14) <| .cons (carry s18 16 5 32 30) <|
    .cons (carry s17 16 5 32 30) <| .cons (carry s1 32 5 32 30) <| .cons (carry s0 32 5 32 30) <| .nil
  · decide

lemma gLeaf62 : BoxGood 32 5 32 31 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 32 5 32 31) <| .cons (carry s15 32 5 32 31) <| .cons (carry s14 32 5 32 31) <| .cons (carry s13 32 5 32 31) <|
    .cons (carry s12 32 5 32 31) <| .cons (carry s11 32 5 32 31) <| .cons (carry s10 32 5 32 31) <| .cons (carry s9 32 5 32 31) <|
    .cons (carry s8 32 5 32 31) <| .cons (carry s7 32 5 32 31) <| .cons (carry s6 32 5 32 31) <| .cons (carry s5 32 5 32 31) <|
    .cons (carry s126 4 1 8 7) <| .cons unmarked <| .cons s187 <| .cons (carry s181 4 1 2 1) <|
    .cons (carry s180 4 1 2 1) <| .cons (carry s179 4 1 2 1) <| .cons s186 <| .cons (carry s62 8 5 8 7) <|
    .cons (carry s61 8 5 8 7) <| .cons (carry s60 8 5 8 7) <| .cons (carry s59 8 5 8 7) <| .cons (carry s182 2 1 2 1) <|
    .cons (carry s125 4 1 8 7) <| .cons (carry s4 32 5 32 31) <| .cons (carry s3 32 5 32 31) <| .cons (carry s2 32 5 32 31) <|
    .cons (carry s40 16 5 16 15) <| .cons (carry s58 8 5 8 7) <| .cons (carry s39 16 5 16 15) <| .cons (carry s18 16 5 32 31) <|
    .cons (carry s17 16 5 32 31) <| .cons (carry s1 32 5 32 31) <| .cons (carry s0 32 5 32 31) <| .nil
  · decide

lemma gLeaf63 : BoxGood 16 3 16 15 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.down,.down,.both,.up,.up,.up,.up,.both,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 16 3 16 15) <| .cons (carry s15 16 3 16 15) <| .cons (carry s14 16 3 16 15) <| .cons (carry s13 16 3 16 15) <|
    .cons (carry s12 16 3 16 15) <| .cons (carry s11 16 3 16 15) <| .cons (carry s10 16 3 16 15) <| .cons (carry s9 16 3 16 15) <|
    .cons (carry s8 16 3 16 15) <| .cons (carry s7 16 3 16 15) <| .cons (carry s6 16 3 16 15) <| .cons (carry s5 16 3 16 15) <|
    .cons (carry s126 2 1 4 3) <| .cons s188 <| .cons unmarked <| .cons (carry s181 2 1 1 0) <|
    .cons (carry s180 2 1 1 0) <| .cons (carry s179 2 1 1 0) <| .cons unmarked <| .cons (carry s62 4 3 4 3) <|
    .cons (carry s61 4 3 4 3) <| .cons (carry s60 4 3 4 3) <| .cons (carry s59 4 3 4 3) <| .cons unmarked <|
    .cons (carry s125 2 1 4 3) <| .cons (carry s4 16 3 16 15) <| .cons (carry s3 16 3 16 15) <| .cons (carry s2 16 3 16 15) <|
    .cons (carry s40 8 3 8 7) <| .cons (carry s58 4 3 4 3) <| .cons (carry s39 8 3 8 7) <| .cons (carry s18 8 3 16 15) <|
    .cons (carry s17 8 3 16 15) <| .cons (carry s1 16 3 16 15) <| .cons (carry s0 16 3 16 15) <| .nil
  · decide

lemma gLeaf64 : BoxGood 8 2 8 6 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.both,.down,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 8 2 8 6) <| .cons (carry s15 8 2 8 6) <| .cons (carry s14 8 2 8 6) <| .cons (carry s13 8 2 8 6) <|
    .cons (carry s12 8 2 8 6) <| .cons (carry s11 8 2 8 6) <| .cons (carry s10 8 2 8 6) <| .cons (carry s9 8 2 8 6) <|
    .cons (carry s8 8 2 8 6) <| .cons (carry s7 8 2 8 6) <| .cons (carry s6 8 2 8 6) <| .cons (carry s5 8 2 8 6) <|
    .cons (carry s191 2 0 2 0) <| .cons (carry s190 2 0 2 0) <| .cons s200 <| .cons s199 <|
    .cons s198 <| .cons s197 <| .cons s196 <| .cons s195 <|
    .cons s194 <| .cons unmarked <| .cons unmarked <| .cons s193 <|
    .cons (carry s189 2 0 2 0) <| .cons (carry s4 8 2 8 6) <| .cons (carry s3 8 2 8 6) <| .cons (carry s2 8 2 8 6) <|
    .cons (carry s40 4 2 4 2) <| .cons (carry s192 1 0 2 0) <| .cons (carry s39 4 2 4 2) <| .cons (carry s18 4 2 8 6) <|
    .cons (carry s17 4 2 8 6) <| .cons (carry s1 8 2 8 6) <| .cons (carry s0 8 2 8 6) <| .nil
  · decide

lemma gLeaf65 : BoxGood 16 4 32 28 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 16 4 32 28) <| .cons (carry s15 16 4 32 28) <| .cons (carry s14 16 4 32 28) <| .cons (carry s13 16 4 32 28) <|
    .cons (carry s12 16 4 32 28) <| .cons (carry s11 16 4 32 28) <| .cons (carry s10 16 4 32 28) <| .cons (carry s9 16 4 32 28) <|
    .cons (carry s8 16 4 32 28) <| .cons (carry s7 16 4 32 28) <| .cons (carry s6 16 4 32 28) <| .cons (carry s5 16 4 32 28) <|
    .cons (carry s191 4 0 8 4) <| .cons (carry s190 4 0 8 4) <| .cons (carry s206 1 0 2 0) <| .cons s209 <|
    .cons s208 <| .cons s207 <| .cons (carry s205 1 0 2 0) <| .cons (carry s203 1 0 4 0) <|
    .cons (carry s202 1 0 4 0) <| .cons (carry s201 1 0 4 0) <| .cons unmarked <| .cons (carry s204 1 0 2 0) <|
    .cons (carry s189 4 0 8 4) <| .cons (carry s4 16 4 32 28) <| .cons (carry s3 16 4 32 28) <| .cons (carry s2 16 4 32 28) <|
    .cons (carry s40 8 4 16 12) <| .cons (carry s192 2 0 8 4) <| .cons (carry s39 8 4 16 12) <| .cons (carry s18 8 4 32 28) <|
    .cons (carry s17 8 4 32 28) <| .cons (carry s1 16 4 32 28) <| .cons (carry s0 16 4 32 28) <| .nil
  · decide

lemma gLeaf66 : BoxGood 16 4 64 58 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.both,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 16 4 64 58) <| .cons (carry s15 16 4 64 58) <| .cons (carry s14 16 4 64 58) <| .cons (carry s13 16 4 64 58) <|
    .cons (carry s12 16 4 64 58) <| .cons (carry s11 16 4 64 58) <| .cons (carry s10 16 4 64 58) <| .cons (carry s9 16 4 64 58) <|
    .cons (carry s8 16 4 64 58) <| .cons (carry s7 16 4 64 58) <| .cons (carry s6 16 4 64 58) <| .cons (carry s5 16 4 64 58) <|
    .cons (carry s191 4 0 16 10) <| .cons (carry s190 4 0 16 10) <| .cons (carry s206 1 0 4 2) <| .cons s211 <|
    .cons unmarked <| .cons unmarked <| .cons (carry s205 1 0 4 2) <| .cons (carry s203 1 0 8 2) <|
    .cons (carry s202 1 0 8 2) <| .cons (carry s201 1 0 8 2) <| .cons (carry s210 1 0 2 0) <| .cons (carry s204 1 0 4 2) <|
    .cons (carry s189 4 0 16 10) <| .cons (carry s4 16 4 64 58) <| .cons (carry s3 16 4 64 58) <| .cons (carry s2 16 4 64 58) <|
    .cons (carry s40 8 4 32 26) <| .cons (carry s192 2 0 16 10) <| .cons (carry s39 8 4 32 26) <| .cons (carry s18 8 4 64 58) <|
    .cons (carry s17 8 4 64 58) <| .cons (carry s1 16 4 64 58) <| .cons (carry s0 16 4 64 58) <| .nil
  · decide

lemma gLeaf67 : BoxGood 32 8 128 118 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.both,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 32 8 128 118) <| .cons (carry s15 32 8 128 118) <| .cons (carry s14 32 8 128 118) <| .cons (carry s13 32 8 128 118) <|
    .cons (carry s12 32 8 128 118) <| .cons (carry s11 32 8 128 118) <| .cons (carry s10 32 8 128 118) <| .cons (carry s9 32 8 128 118) <|
    .cons (carry s8 32 8 128 118) <| .cons (carry s7 32 8 128 118) <| .cons (carry s6 32 8 128 118) <| .cons (carry s5 32 8 128 118) <|
    .cons (carry s191 8 0 32 22) <| .cons (carry s190 8 0 32 22) <| .cons (carry s206 2 0 8 6) <| .cons s212 <|
    .cons unmarked <| .cons unmarked <| .cons (carry s205 2 0 8 6) <| .cons (carry s203 2 0 16 6) <|
    .cons (carry s202 2 0 16 6) <| .cons (carry s201 2 0 16 6) <| .cons (carry s210 2 0 4 2) <| .cons (carry s204 2 0 8 6) <|
    .cons (carry s189 8 0 32 22) <| .cons (carry s4 32 8 128 118) <| .cons (carry s3 32 8 128 118) <| .cons (carry s2 32 8 128 118) <|
    .cons (carry s40 16 8 64 54) <| .cons (carry s192 4 0 32 22) <| .cons (carry s39 16 8 64 54) <| .cons (carry s18 16 8 128 118) <|
    .cons (carry s17 16 8 128 118) <| .cons (carry s1 32 8 128 118) <| .cons (carry s0 32 8 128 118) <| .nil
  · decide

lemma gLeaf68 : BoxGood 32 8 128 119 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.down,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 32 8 128 119) <| .cons (carry s15 32 8 128 119) <| .cons (carry s14 32 8 128 119) <| .cons (carry s13 32 8 128 119) <|
    .cons (carry s12 32 8 128 119) <| .cons (carry s11 32 8 128 119) <| .cons (carry s10 32 8 128 119) <| .cons (carry s9 32 8 128 119) <|
    .cons (carry s8 32 8 128 119) <| .cons (carry s7 32 8 128 119) <| .cons (carry s6 32 8 128 119) <| .cons (carry s5 32 8 128 119) <|
    .cons (carry s191 8 0 32 23) <| .cons (carry s190 8 0 32 23) <| .cons (carry s206 2 0 8 7) <| .cons unmarked <|
    .cons s214 <| .cons s213 <| .cons (carry s205 2 0 8 7) <| .cons (carry s203 2 0 16 7) <|
    .cons (carry s202 2 0 16 7) <| .cons (carry s201 2 0 16 7) <| .cons (carry s210 2 0 4 3) <| .cons (carry s204 2 0 8 7) <|
    .cons (carry s189 8 0 32 23) <| .cons (carry s4 32 8 128 119) <| .cons (carry s3 32 8 128 119) <| .cons (carry s2 32 8 128 119) <|
    .cons (carry s40 16 8 64 55) <| .cons (carry s192 4 0 32 23) <| .cons (carry s39 16 8 64 55) <| .cons (carry s18 16 8 128 119) <|
    .cons (carry s17 16 8 128 119) <| .cons (carry s1 32 8 128 119) <| .cons (carry s0 32 8 128 119) <| .nil
  · decide

lemma gLeaf69 : BoxGood 32 9 64 59 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.both,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 32 9 64 59) <| .cons (carry s15 32 9 64 59) <| .cons (carry s14 32 9 64 59) <| .cons (carry s13 32 9 64 59) <|
    .cons (carry s12 32 9 64 59) <| .cons (carry s11 32 9 64 59) <| .cons (carry s10 32 9 64 59) <| .cons (carry s9 32 9 64 59) <|
    .cons (carry s8 32 9 64 59) <| .cons (carry s7 32 9 64 59) <| .cons (carry s6 32 9 64 59) <| .cons (carry s5 32 9 64 59) <|
    .cons (carry s191 8 1 16 11) <| .cons (carry s190 8 1 16 11) <| .cons (carry s206 2 1 4 3) <| .cons s215 <|
    .cons unmarked <| .cons unmarked <| .cons (carry s205 2 1 4 3) <| .cons (carry s203 2 1 8 3) <|
    .cons (carry s202 2 1 8 3) <| .cons (carry s201 2 1 8 3) <| .cons (carry s210 2 1 2 1) <| .cons (carry s204 2 1 4 3) <|
    .cons (carry s189 8 1 16 11) <| .cons (carry s4 32 9 64 59) <| .cons (carry s3 32 9 64 59) <| .cons (carry s2 32 9 64 59) <|
    .cons (carry s40 16 9 32 27) <| .cons (carry s192 4 1 16 11) <| .cons (carry s39 16 9 32 27) <| .cons (carry s18 16 9 64 59) <|
    .cons (carry s17 16 9 64 59) <| .cons (carry s1 32 9 64 59) <| .cons (carry s0 32 9 64 59) <| .nil
  · decide

lemma gLeaf70 : BoxGood 32 8 64 60 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.down,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 32 8 64 60) <| .cons (carry s15 32 8 64 60) <| .cons (carry s14 32 8 64 60) <| .cons (carry s13 32 8 64 60) <|
    .cons (carry s12 32 8 64 60) <| .cons (carry s11 32 8 64 60) <| .cons (carry s10 32 8 64 60) <| .cons (carry s9 32 8 64 60) <|
    .cons (carry s8 32 8 64 60) <| .cons (carry s7 32 8 64 60) <| .cons (carry s6 32 8 64 60) <| .cons (carry s5 32 8 64 60) <|
    .cons (carry s191 8 0 16 12) <| .cons (carry s190 8 0 16 12) <| .cons (carry s218 2 0 2 0) <| .cons unmarked <|
    .cons s221 <| .cons (carry s217 2 0 4 0) <| .cons (carry s220 2 0 1 0) <| .cons (carry s203 2 0 8 4) <|
    .cons (carry s202 2 0 8 4) <| .cons (carry s201 2 0 8 4) <| .cons (carry s216 2 0 4 0) <| .cons (carry s219 2 0 1 0) <|
    .cons (carry s189 8 0 16 12) <| .cons (carry s4 32 8 64 60) <| .cons (carry s3 32 8 64 60) <| .cons (carry s2 32 8 64 60) <|
    .cons (carry s40 16 8 32 28) <| .cons (carry s192 4 0 16 12) <| .cons (carry s39 16 8 32 28) <| .cons (carry s18 16 8 64 60) <|
    .cons (carry s17 16 8 64 60) <| .cons (carry s1 32 8 64 60) <| .cons (carry s0 32 8 64 60) <| .nil
  · decide

lemma gLeaf71 : BoxGood 32 9 128 120 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 32 9 128 120) <| .cons (carry s15 32 9 128 120) <| .cons (carry s14 32 9 128 120) <| .cons (carry s13 32 9 128 120) <|
    .cons (carry s12 32 9 128 120) <| .cons (carry s11 32 9 128 120) <| .cons (carry s10 32 9 128 120) <| .cons (carry s9 32 9 128 120) <|
    .cons (carry s8 32 9 128 120) <| .cons (carry s7 32 9 128 120) <| .cons (carry s6 32 9 128 120) <| .cons (carry s5 32 9 128 120) <|
    .cons (carry s191 8 1 32 24) <| .cons (carry s190 8 1 32 24) <| .cons (carry s218 2 1 4 0) <| .cons s222 <|
    .cons unmarked <| .cons (carry s217 2 1 8 0) <| .cons (carry s220 2 1 2 0) <| .cons (carry s203 2 1 16 8) <|
    .cons (carry s202 2 1 16 8) <| .cons (carry s201 2 1 16 8) <| .cons (carry s216 2 1 8 0) <| .cons (carry s219 2 1 2 0) <|
    .cons (carry s189 8 1 32 24) <| .cons (carry s4 32 9 128 120) <| .cons (carry s3 32 9 128 120) <| .cons (carry s2 32 9 128 120) <|
    .cons (carry s40 16 9 64 56) <| .cons (carry s192 4 1 32 24) <| .cons (carry s39 16 9 64 56) <| .cons (carry s18 16 9 128 120) <|
    .cons (carry s17 16 9 128 120) <| .cons (carry s1 32 9 128 120) <| .cons (carry s0 32 9 128 120) <| .nil
  · decide

lemma gLeaf72 : BoxGood 32 9 128 121 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.down,.up,.up,.up,.up,.up,.down,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 32 9 128 121) <| .cons (carry s15 32 9 128 121) <| .cons (carry s14 32 9 128 121) <| .cons (carry s13 32 9 128 121) <|
    .cons (carry s12 32 9 128 121) <| .cons (carry s11 32 9 128 121) <| .cons (carry s10 32 9 128 121) <| .cons (carry s9 32 9 128 121) <|
    .cons (carry s8 32 9 128 121) <| .cons (carry s7 32 9 128 121) <| .cons (carry s6 32 9 128 121) <| .cons (carry s5 32 9 128 121) <|
    .cons (carry s191 8 1 32 25) <| .cons (carry s190 8 1 32 25) <| .cons (carry s218 2 1 4 1) <| .cons unmarked <|
    .cons s223 <| .cons (carry s217 2 1 8 1) <| .cons (carry s220 2 1 2 1) <| .cons (carry s203 2 1 16 9) <|
    .cons (carry s202 2 1 16 9) <| .cons (carry s201 2 1 16 9) <| .cons (carry s216 2 1 8 1) <| .cons (carry s219 2 1 2 1) <|
    .cons (carry s189 8 1 32 25) <| .cons (carry s4 32 9 128 121) <| .cons (carry s3 32 9 128 121) <| .cons (carry s2 32 9 128 121) <|
    .cons (carry s40 16 9 64 57) <| .cons (carry s192 4 1 32 25) <| .cons (carry s39 16 9 64 57) <| .cons (carry s18 16 9 128 121) <|
    .cons (carry s17 16 9 128 121) <| .cons (carry s1 32 9 128 121) <| .cons (carry s0 32 9 128 121) <| .nil
  · decide

lemma gLeaf73 : BoxGood 16 4 64 61 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.down,.both,.up,.up,.up,.up,.both,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 16 4 64 61) <| .cons (carry s15 16 4 64 61) <| .cons (carry s14 16 4 64 61) <| .cons (carry s13 16 4 64 61) <|
    .cons (carry s12 16 4 64 61) <| .cons (carry s11 16 4 64 61) <| .cons (carry s10 16 4 64 61) <| .cons (carry s9 16 4 64 61) <|
    .cons (carry s8 16 4 64 61) <| .cons (carry s7 16 4 64 61) <| .cons (carry s6 16 4 64 61) <| .cons (carry s5 16 4 64 61) <|
    .cons (carry s191 4 0 16 13) <| .cons (carry s190 4 0 16 13) <| .cons (carry s218 1 0 2 1) <| .cons unmarked <|
    .cons s224 <| .cons (carry s217 1 0 4 1) <| .cons unmarked <| .cons (carry s203 1 0 8 5) <|
    .cons (carry s202 1 0 8 5) <| .cons (carry s201 1 0 8 5) <| .cons (carry s216 1 0 4 1) <| .cons unmarked <|
    .cons (carry s189 4 0 16 13) <| .cons (carry s4 16 4 64 61) <| .cons (carry s3 16 4 64 61) <| .cons (carry s2 16 4 64 61) <|
    .cons (carry s40 8 4 32 29) <| .cons (carry s192 2 0 16 13) <| .cons (carry s39 8 4 32 29) <| .cons (carry s18 8 4 64 61) <|
    .cons (carry s17 8 4 64 61) <| .cons (carry s1 16 4 64 61) <| .cons (carry s0 16 4 64 61) <| .nil
  · decide

lemma gLeaf74 : BoxGood 16 4 32 31 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.down,.down,.down,.up,.up,.up,.up,.both,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 16 4 32 31) <| .cons (carry s15 16 4 32 31) <| .cons (carry s14 16 4 32 31) <| .cons (carry s13 16 4 32 31) <|
    .cons (carry s12 16 4 32 31) <| .cons (carry s11 16 4 32 31) <| .cons (carry s10 16 4 32 31) <| .cons (carry s9 16 4 32 31) <|
    .cons (carry s8 16 4 32 31) <| .cons (carry s7 16 4 32 31) <| .cons (carry s6 16 4 32 31) <| .cons (carry s5 16 4 32 31) <|
    .cons (carry s191 4 0 8 7) <| .cons (carry s190 4 0 8 7) <| .cons unmarked <| .cons s227 <|
    .cons s226 <| .cons (carry s217 1 0 2 1) <| .cons s225 <| .cons (carry s203 1 0 4 3) <|
    .cons (carry s202 1 0 4 3) <| .cons (carry s201 1 0 4 3) <| .cons (carry s216 1 0 2 1) <| .cons unmarked <|
    .cons (carry s189 4 0 8 7) <| .cons (carry s4 16 4 32 31) <| .cons (carry s3 16 4 32 31) <| .cons (carry s2 16 4 32 31) <|
    .cons (carry s40 8 4 16 15) <| .cons (carry s192 2 0 8 7) <| .cons (carry s39 8 4 16 15) <| .cons (carry s18 8 4 32 31) <|
    .cons (carry s17 8 4 32 31) <| .cons (carry s1 16 4 32 31) <| .cons (carry s0 16 4 32 31) <| .nil
  · decide

lemma gLeaf75 : BoxGood 32 10 16 14 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.up,.up,.up,.up,.both,.down,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 32 10 16 14) <| .cons (carry s15 32 10 16 14) <| .cons (carry s14 32 10 16 14) <| .cons (carry s13 32 10 16 14) <|
    .cons (carry s12 32 10 16 14) <| .cons (carry s11 32 10 16 14) <| .cons (carry s10 32 10 16 14) <| .cons (carry s9 32 10 16 14) <|
    .cons (carry s8 32 10 16 14) <| .cons (carry s7 32 10 16 14) <| .cons (carry s6 32 10 16 14) <| .cons (carry s5 32 10 16 14) <|
    .cons (carry s191 8 2 4 2) <| .cons (carry s190 8 2 4 2) <| .cons (carry s229 2 0 2 0) <| .cons s235 <|
    .cons s234 <| .cons unmarked <| .cons s233 <| .cons (carry s232 1 0 2 0) <|
    .cons (carry s231 1 0 2 0) <| .cons (carry s230 1 0 2 0) <| .cons unmarked <| .cons (carry s228 2 0 2 0) <|
    .cons (carry s189 8 2 4 2) <| .cons (carry s4 32 10 16 14) <| .cons (carry s3 32 10 16 14) <| .cons (carry s2 32 10 16 14) <|
    .cons (carry s40 16 10 8 6) <| .cons (carry s192 4 2 4 2) <| .cons (carry s39 16 10 8 6) <| .cons (carry s18 16 10 16 14) <|
    .cons (carry s17 16 10 16 14) <| .cons (carry s1 32 10 16 14) <| .cons (carry s0 32 10 16 14) <| .nil
  · decide

lemma gLeaf76 : BoxGood 32 10 64 60 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.both,.up,.up,.up,.up,.both,.down,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 32 10 64 60) <| .cons (carry s15 32 10 64 60) <| .cons (carry s14 32 10 64 60) <| .cons (carry s13 32 10 64 60) <|
    .cons (carry s12 32 10 64 60) <| .cons (carry s11 32 10 64 60) <| .cons (carry s10 32 10 64 60) <| .cons (carry s9 32 10 64 60) <|
    .cons (carry s8 32 10 64 60) <| .cons (carry s7 32 10 64 60) <| .cons (carry s6 32 10 64 60) <| .cons (carry s5 32 10 64 60) <|
    .cons (carry s191 8 2 16 12) <| .cons (carry s190 8 2 16 12) <| .cons (carry s229 2 0 8 4) <| .cons s237 <|
    .cons unmarked <| .cons unmarked <| .cons s236 <| .cons (carry s232 1 0 8 4) <|
    .cons (carry s231 1 0 8 4) <| .cons (carry s230 1 0 8 4) <| .cons unmarked <| .cons (carry s228 2 0 8 4) <|
    .cons (carry s189 8 2 16 12) <| .cons (carry s4 32 10 64 60) <| .cons (carry s3 32 10 64 60) <| .cons (carry s2 32 10 64 60) <|
    .cons (carry s40 16 10 32 28) <| .cons (carry s192 4 2 16 12) <| .cons (carry s39 16 10 32 28) <| .cons (carry s18 16 10 64 60) <|
    .cons (carry s17 16 10 64 60) <| .cons (carry s1 32 10 64 60) <| .cons (carry s0 32 10 64 60) <| .nil
  · decide

lemma gLeaf77 : BoxGood 32 10 64 61 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.down,.both,.up,.up,.up,.both,.down,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 32 10 64 61) <| .cons (carry s15 32 10 64 61) <| .cons (carry s14 32 10 64 61) <| .cons (carry s13 32 10 64 61) <|
    .cons (carry s12 32 10 64 61) <| .cons (carry s11 32 10 64 61) <| .cons (carry s10 32 10 64 61) <| .cons (carry s9 32 10 64 61) <|
    .cons (carry s8 32 10 64 61) <| .cons (carry s7 32 10 64 61) <| .cons (carry s6 32 10 64 61) <| .cons (carry s5 32 10 64 61) <|
    .cons (carry s191 8 2 16 13) <| .cons (carry s190 8 2 16 13) <| .cons (carry s229 2 0 8 5) <| .cons unmarked <|
    .cons s239 <| .cons s238 <| .cons unmarked <| .cons (carry s232 1 0 8 5) <|
    .cons (carry s231 1 0 8 5) <| .cons (carry s230 1 0 8 5) <| .cons unmarked <| .cons (carry s228 2 0 8 5) <|
    .cons (carry s189 8 2 16 13) <| .cons (carry s4 32 10 64 61) <| .cons (carry s3 32 10 64 61) <| .cons (carry s2 32 10 64 61) <|
    .cons (carry s40 16 10 32 29) <| .cons (carry s192 4 2 16 13) <| .cons (carry s39 16 10 32 29) <| .cons (carry s18 16 10 64 61) <|
    .cons (carry s17 16 10 64 61) <| .cons (carry s1 32 10 64 61) <| .cons (carry s0 32 10 64 61) <| .nil
  · decide

lemma gLeaf78 : BoxGood 32 10 32 31 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.down,.down,.up,.up,.up,.both,.down,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 32 10 32 31) <| .cons (carry s15 32 10 32 31) <| .cons (carry s14 32 10 32 31) <| .cons (carry s13 32 10 32 31) <|
    .cons (carry s12 32 10 32 31) <| .cons (carry s11 32 10 32 31) <| .cons (carry s10 32 10 32 31) <| .cons (carry s9 32 10 32 31) <|
    .cons (carry s8 32 10 32 31) <| .cons (carry s7 32 10 32 31) <| .cons (carry s6 32 10 32 31) <| .cons (carry s5 32 10 32 31) <|
    .cons (carry s191 8 2 8 7) <| .cons (carry s190 8 2 8 7) <| .cons (carry s229 2 0 4 3) <| .cons unmarked <|
    .cons s242 <| .cons s241 <| .cons s240 <| .cons (carry s232 1 0 4 3) <|
    .cons (carry s231 1 0 4 3) <| .cons (carry s230 1 0 4 3) <| .cons unmarked <| .cons (carry s228 2 0 4 3) <|
    .cons (carry s189 8 2 8 7) <| .cons (carry s4 32 10 32 31) <| .cons (carry s3 32 10 32 31) <| .cons (carry s2 32 10 32 31) <|
    .cons (carry s40 16 10 16 15) <| .cons (carry s192 4 2 8 7) <| .cons (carry s39 16 10 16 15) <| .cons (carry s18 16 10 32 31) <|
    .cons (carry s17 16 10 32 31) <| .cons (carry s1 32 10 32 31) <| .cons (carry s0 32 10 32 31) <| .nil
  · decide

lemma gLeaf79 : BoxGood 32 11 16 14 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.down,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 32 11 16 14) <| .cons (carry s15 32 11 16 14) <| .cons (carry s14 32 11 16 14) <| .cons (carry s13 32 11 16 14) <|
    .cons (carry s12 32 11 16 14) <| .cons (carry s11 32 11 16 14) <| .cons (carry s10 32 11 16 14) <| .cons (carry s9 32 11 16 14) <|
    .cons (carry s8 32 11 16 14) <| .cons (carry s7 32 11 16 14) <| .cons (carry s6 32 11 16 14) <| .cons (carry s5 32 11 16 14) <|
    .cons (carry s191 8 3 4 2) <| .cons (carry s190 8 3 4 2) <| .cons (carry s229 2 1 2 0) <| .cons s249 <|
    .cons s248 <| .cons s247 <| .cons s246 <| .cons s245 <|
    .cons s244 <| .cons unmarked <| .cons (carry s243 1 0 2 0) <| .cons (carry s228 2 1 2 0) <|
    .cons (carry s189 8 3 4 2) <| .cons (carry s4 32 11 16 14) <| .cons (carry s3 32 11 16 14) <| .cons (carry s2 32 11 16 14) <|
    .cons (carry s40 16 11 8 6) <| .cons (carry s192 4 3 4 2) <| .cons (carry s39 16 11 8 6) <| .cons (carry s18 16 11 16 14) <|
    .cons (carry s17 16 11 16 14) <| .cons (carry s1 32 11 16 14) <| .cons (carry s0 32 11 16 14) <| .nil
  · decide

lemma gLeaf80 : BoxGood 64 22 128 120 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.up,.up,.up,.up,.down,.down,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 64 22 128 120) <| .cons (carry s15 64 22 128 120) <| .cons (carry s14 64 22 128 120) <| .cons (carry s13 64 22 128 120) <|
    .cons (carry s12 64 22 128 120) <| .cons (carry s11 64 22 128 120) <| .cons (carry s10 64 22 128 120) <| .cons (carry s9 64 22 128 120) <|
    .cons (carry s8 64 22 128 120) <| .cons (carry s7 64 22 128 120) <| .cons (carry s6 64 22 128 120) <| .cons (carry s5 64 22 128 120) <|
    .cons (carry s191 16 6 32 24) <| .cons (carry s190 16 6 32 24) <| .cons (carry s229 4 2 16 8) <| .cons (carry s251 2 0 4 0) <|
    .cons s255 <| .cons unmarked <| .cons s254 <| .cons (carry s253 1 0 4 0) <|
    .cons (carry s250 2 0 4 0) <| .cons (carry s252 1 0 4 0) <| .cons (carry s243 2 0 16 8) <| .cons (carry s228 4 2 16 8) <|
    .cons (carry s189 16 6 32 24) <| .cons (carry s4 64 22 128 120) <| .cons (carry s3 64 22 128 120) <| .cons (carry s2 64 22 128 120) <|
    .cons (carry s40 32 22 64 56) <| .cons (carry s192 8 6 32 24) <| .cons (carry s39 32 22 64 56) <| .cons (carry s18 32 22 128 120) <|
    .cons (carry s17 32 22 128 120) <| .cons (carry s1 64 22 128 120) <| .cons (carry s0 64 22 128 120) <| .nil
  · decide

lemma gLeaf81 : BoxGood 64 22 128 121 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.both,.up,.up,.up,.down,.down,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 64 22 128 121) <| .cons (carry s15 64 22 128 121) <| .cons (carry s14 64 22 128 121) <| .cons (carry s13 64 22 128 121) <|
    .cons (carry s12 64 22 128 121) <| .cons (carry s11 64 22 128 121) <| .cons (carry s10 64 22 128 121) <| .cons (carry s9 64 22 128 121) <|
    .cons (carry s8 64 22 128 121) <| .cons (carry s7 64 22 128 121) <| .cons (carry s6 64 22 128 121) <| .cons (carry s5 64 22 128 121) <|
    .cons (carry s191 16 6 32 25) <| .cons (carry s190 16 6 32 25) <| .cons (carry s229 4 2 16 9) <| .cons (carry s251 2 0 4 1) <|
    .cons unmarked <| .cons s256 <| .cons unmarked <| .cons (carry s253 1 0 4 1) <|
    .cons (carry s250 2 0 4 1) <| .cons (carry s252 1 0 4 1) <| .cons (carry s243 2 0 16 9) <| .cons (carry s228 4 2 16 9) <|
    .cons (carry s189 16 6 32 25) <| .cons (carry s4 64 22 128 121) <| .cons (carry s3 64 22 128 121) <| .cons (carry s2 64 22 128 121) <|
    .cons (carry s40 32 22 64 57) <| .cons (carry s192 8 6 32 25) <| .cons (carry s39 32 22 64 57) <| .cons (carry s18 32 22 128 121) <|
    .cons (carry s17 32 22 128 121) <| .cons (carry s1 64 22 128 121) <| .cons (carry s0 64 22 128 121) <| .nil
  · decide

lemma gLeaf82 : BoxGood 64 22 64 61 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.both,.up,.up,.up,.down,.down,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 64 22 64 61) <| .cons (carry s15 64 22 64 61) <| .cons (carry s14 64 22 64 61) <| .cons (carry s13 64 22 64 61) <|
    .cons (carry s12 64 22 64 61) <| .cons (carry s11 64 22 64 61) <| .cons (carry s10 64 22 64 61) <| .cons (carry s9 64 22 64 61) <|
    .cons (carry s8 64 22 64 61) <| .cons (carry s7 64 22 64 61) <| .cons (carry s6 64 22 64 61) <| .cons (carry s5 64 22 64 61) <|
    .cons (carry s191 16 6 16 13) <| .cons (carry s190 16 6 16 13) <| .cons (carry s229 4 2 8 5) <| .cons (carry s251 2 0 2 1) <|
    .cons unmarked <| .cons s257 <| .cons unmarked <| .cons (carry s253 1 0 2 1) <|
    .cons (carry s250 2 0 2 1) <| .cons (carry s252 1 0 2 1) <| .cons (carry s243 2 0 8 5) <| .cons (carry s228 4 2 8 5) <|
    .cons (carry s189 16 6 16 13) <| .cons (carry s4 64 22 64 61) <| .cons (carry s3 64 22 64 61) <| .cons (carry s2 64 22 64 61) <|
    .cons (carry s40 32 22 32 29) <| .cons (carry s192 8 6 16 13) <| .cons (carry s39 32 22 32 29) <| .cons (carry s18 32 22 64 61) <|
    .cons (carry s17 32 22 64 61) <| .cons (carry s1 64 22 64 61) <| .cons (carry s0 64 22 64 61) <| .nil
  · decide

lemma gLeaf83 : BoxGood 64 23 64 60 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.both,.up,.up,.both,.down,.down,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 64 23 64 60) <| .cons (carry s15 64 23 64 60) <| .cons (carry s14 64 23 64 60) <| .cons (carry s13 64 23 64 60) <|
    .cons (carry s12 64 23 64 60) <| .cons (carry s11 64 23 64 60) <| .cons (carry s10 64 23 64 60) <| .cons (carry s9 64 23 64 60) <|
    .cons (carry s8 64 23 64 60) <| .cons (carry s7 64 23 64 60) <| .cons (carry s6 64 23 64 60) <| .cons (carry s5 64 23 64 60) <|
    .cons (carry s191 16 7 16 12) <| .cons (carry s190 16 7 16 12) <| .cons (carry s229 4 3 8 4) <| .cons (carry s251 2 1 2 0) <|
    .cons s259 <| .cons unmarked <| .cons unmarked <| .cons s258 <|
    .cons (carry s250 2 1 2 0) <| .cons unmarked <| .cons (carry s243 2 1 8 4) <| .cons (carry s228 4 3 8 4) <|
    .cons (carry s189 16 7 16 12) <| .cons (carry s4 64 23 64 60) <| .cons (carry s3 64 23 64 60) <| .cons (carry s2 64 23 64 60) <|
    .cons (carry s40 32 23 32 28) <| .cons (carry s192 8 7 16 12) <| .cons (carry s39 32 23 32 28) <| .cons (carry s18 32 23 64 60) <|
    .cons (carry s17 32 23 64 60) <| .cons (carry s1 64 23 64 60) <| .cons (carry s0 64 23 64 60) <| .nil
  · decide

lemma gLeaf84 : BoxGood 64 23 64 61 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.down,.both,.up,.both,.down,.down,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 64 23 64 61) <| .cons (carry s15 64 23 64 61) <| .cons (carry s14 64 23 64 61) <| .cons (carry s13 64 23 64 61) <|
    .cons (carry s12 64 23 64 61) <| .cons (carry s11 64 23 64 61) <| .cons (carry s10 64 23 64 61) <| .cons (carry s9 64 23 64 61) <|
    .cons (carry s8 64 23 64 61) <| .cons (carry s7 64 23 64 61) <| .cons (carry s6 64 23 64 61) <| .cons (carry s5 64 23 64 61) <|
    .cons (carry s191 16 7 16 13) <| .cons (carry s190 16 7 16 13) <| .cons (carry s229 4 3 8 5) <| .cons (carry s251 2 1 2 1) <|
    .cons unmarked <| .cons s261 <| .cons s260 <| .cons unmarked <|
    .cons (carry s250 2 1 2 1) <| .cons unmarked <| .cons (carry s243 2 1 8 5) <| .cons (carry s228 4 3 8 5) <|
    .cons (carry s189 16 7 16 13) <| .cons (carry s4 64 23 64 61) <| .cons (carry s3 64 23 64 61) <| .cons (carry s2 64 23 64 61) <|
    .cons (carry s40 32 23 32 29) <| .cons (carry s192 8 7 16 13) <| .cons (carry s39 32 23 32 29) <| .cons (carry s18 32 23 64 61) <|
    .cons (carry s17 32 23 64 61) <| .cons (carry s1 64 23 64 61) <| .cons (carry s0 64 23 64 61) <| .nil
  · decide

lemma gLeaf85 : BoxGood 64 22 32 31 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.down,.down,.both,.up,.up,.down,.down,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 64 22 32 31) <| .cons (carry s15 64 22 32 31) <| .cons (carry s14 64 22 32 31) <| .cons (carry s13 64 22 32 31) <|
    .cons (carry s12 64 22 32 31) <| .cons (carry s11 64 22 32 31) <| .cons (carry s10 64 22 32 31) <| .cons (carry s9 64 22 32 31) <|
    .cons (carry s8 64 22 32 31) <| .cons (carry s7 64 22 32 31) <| .cons (carry s6 64 22 32 31) <| .cons (carry s5 64 22 32 31) <|
    .cons (carry s191 16 6 8 7) <| .cons (carry s190 16 6 8 7) <| .cons (carry s229 4 2 4 3) <| .cons unmarked <|
    .cons (carry s264 2 0 1 0) <| .cons (carry s263 2 0 1 0) <| .cons (carry s262 2 0 1 0) <| .cons unmarked <|
    .cons s266 <| .cons s265 <| .cons (carry s243 2 0 4 3) <| .cons (carry s228 4 2 4 3) <|
    .cons (carry s189 16 6 8 7) <| .cons (carry s4 64 22 32 31) <| .cons (carry s3 64 22 32 31) <| .cons (carry s2 64 22 32 31) <|
    .cons (carry s40 32 22 16 15) <| .cons (carry s192 8 6 8 7) <| .cons (carry s39 32 22 16 15) <| .cons (carry s18 32 22 32 31) <|
    .cons (carry s17 32 22 32 31) <| .cons (carry s1 64 22 32 31) <| .cons (carry s0 64 22 32 31) <| .nil
  · decide

lemma gLeaf86 : BoxGood 128 46 32 31 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.down,.down,.both,.up,.both,.down,.down,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 128 46 32 31) <| .cons (carry s15 128 46 32 31) <| .cons (carry s14 128 46 32 31) <| .cons (carry s13 128 46 32 31) <|
    .cons (carry s12 128 46 32 31) <| .cons (carry s11 128 46 32 31) <| .cons (carry s10 128 46 32 31) <| .cons (carry s9 128 46 32 31) <|
    .cons (carry s8 128 46 32 31) <| .cons (carry s7 128 46 32 31) <| .cons (carry s6 128 46 32 31) <| .cons (carry s5 128 46 32 31) <|
    .cons (carry s191 32 14 8 7) <| .cons (carry s190 32 14 8 7) <| .cons (carry s229 8 6 4 3) <| .cons unmarked <|
    .cons (carry s264 4 2 1 0) <| .cons (carry s263 4 2 1 0) <| .cons (carry s262 4 2 1 0) <| .cons unmarked <|
    .cons s267 <| .cons unmarked <| .cons (carry s243 4 2 4 3) <| .cons (carry s228 8 6 4 3) <|
    .cons (carry s189 32 14 8 7) <| .cons (carry s4 128 46 32 31) <| .cons (carry s3 128 46 32 31) <| .cons (carry s2 128 46 32 31) <|
    .cons (carry s40 64 46 16 15) <| .cons (carry s192 16 14 8 7) <| .cons (carry s39 64 46 16 15) <| .cons (carry s18 64 46 32 31) <|
    .cons (carry s17 64 46 32 31) <| .cons (carry s1 128 46 32 31) <| .cons (carry s0 128 46 32 31) <| .nil
  · decide

lemma gLeaf87 : BoxGood 128 47 32 31 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.down,.down,.down,.both,.both,.down,.down,.down,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 128 47 32 31) <| .cons (carry s15 128 47 32 31) <| .cons (carry s14 128 47 32 31) <| .cons (carry s13 128 47 32 31) <|
    .cons (carry s12 128 47 32 31) <| .cons (carry s11 128 47 32 31) <| .cons (carry s10 128 47 32 31) <| .cons (carry s9 128 47 32 31) <|
    .cons (carry s8 128 47 32 31) <| .cons (carry s7 128 47 32 31) <| .cons (carry s6 128 47 32 31) <| .cons (carry s5 128 47 32 31) <|
    .cons (carry s191 32 15 8 7) <| .cons (carry s190 32 15 8 7) <| .cons (carry s229 8 7 4 3) <| .cons s269 <|
    .cons (carry s264 4 3 1 0) <| .cons (carry s263 4 3 1 0) <| .cons (carry s262 4 3 1 0) <| .cons unmarked <|
    .cons unmarked <| .cons s268 <| .cons (carry s243 4 3 4 3) <| .cons (carry s228 8 7 4 3) <|
    .cons (carry s189 32 15 8 7) <| .cons (carry s4 128 47 32 31) <| .cons (carry s3 128 47 32 31) <| .cons (carry s2 128 47 32 31) <|
    .cons (carry s40 64 47 16 15) <| .cons (carry s192 16 15 8 7) <| .cons (carry s39 64 47 16 15) <| .cons (carry s18 64 47 32 31) <|
    .cons (carry s17 64 47 32 31) <| .cons (carry s1 128 47 32 31) <| .cons (carry s0 128 47 32 31) <| .nil
  · decide

lemma gLeaf88 : BoxGood 8 3 8 6 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.both,.both,.down,.down,.down,.down,.down,.down,.down,.down,.both,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 8 3 8 6) <| .cons (carry s15 8 3 8 6) <| .cons (carry s14 8 3 8 6) <| .cons (carry s13 8 3 8 6) <|
    .cons (carry s12 8 3 8 6) <| .cons (carry s11 8 3 8 6) <| .cons (carry s10 8 3 8 6) <| .cons (carry s9 8 3 8 6) <|
    .cons (carry s8 8 3 8 6) <| .cons (carry s7 8 3 8 6) <| .cons (carry s6 8 3 8 6) <| .cons (carry s5 8 3 8 6) <|
    .cons (carry s191 2 1 2 0) <| .cons (carry s190 2 1 2 0) <| .cons (carry s274 1 0 2 0) <| .cons (carry s273 1 0 2 0) <|
    .cons s276 <| .cons s275 <| .cons unmarked <| .cons unmarked <|
    .cons unmarked <| .cons (carry s272 1 0 2 0) <| .cons (carry s271 1 0 2 0) <| .cons (carry s270 1 0 2 0) <|
    .cons (carry s189 2 1 2 0) <| .cons (carry s4 8 3 8 6) <| .cons (carry s3 8 3 8 6) <| .cons (carry s2 8 3 8 6) <|
    .cons (carry s40 4 3 4 2) <| .cons unmarked <| .cons (carry s39 4 3 4 2) <| .cons (carry s18 4 3 8 6) <|
    .cons (carry s17 4 3 8 6) <| .cons (carry s1 8 3 8 6) <| .cons (carry s0 8 3 8 6) <| .nil
  · decide

lemma gLeaf89 : BoxGood 16 6 16 14 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.both,.both,.down,.down,.down,.down,.down,.down,.down,.down,.both,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 16 6 16 14) <| .cons (carry s15 16 6 16 14) <| .cons (carry s14 16 6 16 14) <| .cons (carry s13 16 6 16 14) <|
    .cons (carry s12 16 6 16 14) <| .cons (carry s11 16 6 16 14) <| .cons (carry s10 16 6 16 14) <| .cons (carry s9 16 6 16 14) <|
    .cons (carry s8 16 6 16 14) <| .cons (carry s7 16 6 16 14) <| .cons (carry s6 16 6 16 14) <| .cons (carry s5 16 6 16 14) <|
    .cons (carry s191 4 2 4 2) <| .cons (carry s190 4 2 4 2) <| .cons (carry s274 2 0 4 2) <| .cons (carry s273 2 0 4 2) <|
    .cons s278 <| .cons s277 <| .cons unmarked <| .cons unmarked <|
    .cons unmarked <| .cons (carry s272 2 0 4 2) <| .cons (carry s271 2 0 4 2) <| .cons (carry s270 2 0 4 2) <|
    .cons (carry s189 4 2 4 2) <| .cons (carry s4 16 6 16 14) <| .cons (carry s3 16 6 16 14) <| .cons (carry s2 16 6 16 14) <|
    .cons (carry s40 8 6 8 6) <| .cons unmarked <| .cons (carry s39 8 6 8 6) <| .cons (carry s18 8 6 16 14) <|
    .cons (carry s17 8 6 16 14) <| .cons (carry s1 16 6 16 14) <| .cons (carry s0 16 6 16 14) <| .nil
  · decide

lemma gLeaf90 : BoxGood 128 48 64 60 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.both,.up,.up,.down,.down,.down,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 128 48 64 60) <| .cons (carry s15 128 48 64 60) <| .cons (carry s14 128 48 64 60) <| .cons (carry s13 128 48 64 60) <|
    .cons (carry s12 128 48 64 60) <| .cons (carry s11 128 48 64 60) <| .cons (carry s10 128 48 64 60) <| .cons (carry s9 128 48 64 60) <|
    .cons (carry s8 128 48 64 60) <| .cons (carry s7 128 48 64 60) <| .cons (carry s6 128 48 64 60) <| .cons (carry s5 128 48 64 60) <|
    .cons (carry s191 32 16 16 12) <| .cons (carry s190 32 16 16 12) <| .cons (carry s274 16 0 16 12) <| .cons (carry s273 16 0 16 12) <|
    .cons (carry s279 8 0 1 0) <| .cons unmarked <| .cons unmarked <| .cons s282 <|
    .cons s281 <| .cons (carry s272 16 0 16 12) <| .cons (carry s271 16 0 16 12) <| .cons (carry s270 16 0 16 12) <|
    .cons (carry s189 32 16 16 12) <| .cons (carry s4 128 48 64 60) <| .cons (carry s3 128 48 64 60) <| .cons (carry s2 128 48 64 60) <|
    .cons (carry s40 64 48 32 28) <| .cons (carry s280 2 0 1 0) <| .cons (carry s39 64 48 32 28) <| .cons (carry s18 64 48 64 60) <|
    .cons (carry s17 64 48 64 60) <| .cons (carry s1 128 48 64 60) <| .cons (carry s0 128 48 64 60) <| .nil
  · decide

lemma gLeaf91 : BoxGood 128 49 128 120 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.up,.both,.down,.down,.down,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 128 49 128 120) <| .cons (carry s15 128 49 128 120) <| .cons (carry s14 128 49 128 120) <| .cons (carry s13 128 49 128 120) <|
    .cons (carry s12 128 49 128 120) <| .cons (carry s11 128 49 128 120) <| .cons (carry s10 128 49 128 120) <| .cons (carry s9 128 49 128 120) <|
    .cons (carry s8 128 49 128 120) <| .cons (carry s7 128 49 128 120) <| .cons (carry s6 128 49 128 120) <| .cons (carry s5 128 49 128 120) <|
    .cons (carry s191 32 17 32 24) <| .cons (carry s190 32 17 32 24) <| .cons (carry s274 16 1 32 24) <| .cons (carry s273 16 1 32 24) <|
    .cons (carry s279 8 1 2 0) <| .cons s284 <| .cons unmarked <| .cons s283 <|
    .cons unmarked <| .cons (carry s272 16 1 32 24) <| .cons (carry s271 16 1 32 24) <| .cons (carry s270 16 1 32 24) <|
    .cons (carry s189 32 17 32 24) <| .cons (carry s4 128 49 128 120) <| .cons (carry s3 128 49 128 120) <| .cons (carry s2 128 49 128 120) <|
    .cons (carry s40 64 49 64 56) <| .cons (carry s280 2 1 2 0) <| .cons (carry s39 64 49 64 56) <| .cons (carry s18 64 49 128 120) <|
    .cons (carry s17 64 49 128 120) <| .cons (carry s1 128 49 128 120) <| .cons (carry s0 128 49 128 120) <| .nil
  · decide

lemma gLeaf92 : BoxGood 256 98 256 242 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.both,.up,.both,.down,.down,.down,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 256 98 256 242) <| .cons (carry s15 256 98 256 242) <| .cons (carry s14 256 98 256 242) <| .cons (carry s13 256 98 256 242) <|
    .cons (carry s12 256 98 256 242) <| .cons (carry s11 256 98 256 242) <| .cons (carry s10 256 98 256 242) <| .cons (carry s9 256 98 256 242) <|
    .cons (carry s8 256 98 256 242) <| .cons (carry s7 256 98 256 242) <| .cons (carry s6 256 98 256 242) <| .cons (carry s5 256 98 256 242) <|
    .cons (carry s191 64 34 64 50) <| .cons (carry s190 64 34 64 50) <| .cons (carry s274 32 2 64 50) <| .cons (carry s273 32 2 64 50) <|
    .cons (carry s279 16 2 4 2) <| .cons unmarked <| .cons unmarked <| .cons s285 <|
    .cons unmarked <| .cons (carry s272 32 2 64 50) <| .cons (carry s271 32 2 64 50) <| .cons (carry s270 32 2 64 50) <|
    .cons (carry s189 64 34 64 50) <| .cons (carry s4 256 98 256 242) <| .cons (carry s3 256 98 256 242) <| .cons (carry s2 256 98 256 242) <|
    .cons (carry s40 128 98 128 114) <| .cons (carry s280 4 2 4 2) <| .cons (carry s39 128 98 128 114) <| .cons (carry s18 128 98 256 242) <|
    .cons (carry s17 128 98 256 242) <| .cons (carry s1 256 98 256 242) <| .cons (carry s0 256 98 256 242) <| .nil
  · decide

lemma gLeaf93 : BoxGood 256 98 256 243 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.down,.down,.both,.both,.down,.down,.down,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 256 98 256 243) <| .cons (carry s15 256 98 256 243) <| .cons (carry s14 256 98 256 243) <| .cons (carry s13 256 98 256 243) <|
    .cons (carry s12 256 98 256 243) <| .cons (carry s11 256 98 256 243) <| .cons (carry s10 256 98 256 243) <| .cons (carry s9 256 98 256 243) <|
    .cons (carry s8 256 98 256 243) <| .cons (carry s7 256 98 256 243) <| .cons (carry s6 256 98 256 243) <| .cons (carry s5 256 98 256 243) <|
    .cons (carry s191 64 34 64 51) <| .cons (carry s190 64 34 64 51) <| .cons (carry s274 32 2 64 51) <| .cons (carry s273 32 2 64 51) <|
    .cons (carry s279 16 2 4 3) <| .cons s287 <| .cons s286 <| .cons unmarked <|
    .cons unmarked <| .cons (carry s272 32 2 64 51) <| .cons (carry s271 32 2 64 51) <| .cons (carry s270 32 2 64 51) <|
    .cons (carry s189 64 34 64 51) <| .cons (carry s4 256 98 256 243) <| .cons (carry s3 256 98 256 243) <| .cons (carry s2 256 98 256 243) <|
    .cons (carry s40 128 98 128 115) <| .cons (carry s280 4 2 4 3) <| .cons (carry s39 128 98 128 115) <| .cons (carry s18 128 98 256 243) <|
    .cons (carry s17 128 98 256 243) <| .cons (carry s1 256 98 256 243) <| .cons (carry s0 256 98 256 243) <| .nil
  · decide

lemma gLeaf94 : BoxGood 256 99 128 121 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.both,.down,.down,.down,.down,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 256 99 128 121) <| .cons (carry s15 256 99 128 121) <| .cons (carry s14 256 99 128 121) <| .cons (carry s13 256 99 128 121) <|
    .cons (carry s12 256 99 128 121) <| .cons (carry s11 256 99 128 121) <| .cons (carry s10 256 99 128 121) <| .cons (carry s9 256 99 128 121) <|
    .cons (carry s8 256 99 128 121) <| .cons (carry s7 256 99 128 121) <| .cons (carry s6 256 99 128 121) <| .cons (carry s5 256 99 128 121) <|
    .cons (carry s191 64 35 32 25) <| .cons (carry s190 64 35 32 25) <| .cons (carry s274 32 3 32 25) <| .cons (carry s273 32 3 32 25) <|
    .cons (carry s279 16 3 2 1) <| .cons unmarked <| .cons s289 <| .cons unmarked <|
    .cons s288 <| .cons (carry s272 32 3 32 25) <| .cons (carry s271 32 3 32 25) <| .cons (carry s270 32 3 32 25) <|
    .cons (carry s189 64 35 32 25) <| .cons (carry s4 256 99 128 121) <| .cons (carry s3 256 99 128 121) <| .cons (carry s2 256 99 128 121) <|
    .cons (carry s40 128 99 64 57) <| .cons (carry s280 4 3 2 1) <| .cons (carry s39 128 99 64 57) <| .cons (carry s18 128 99 128 121) <|
    .cons (carry s17 128 99 128 121) <| .cons (carry s1 256 99 128 121) <| .cons (carry s0 256 99 128 121) <| .nil
  · decide

lemma gLeaf95 : BoxGood 64 25 64 60 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.both,.both,.down,.down,.down,.down,.down,.down,.down,.down,.down,.both,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 64 25 64 60) <| .cons (carry s15 64 25 64 60) <| .cons (carry s14 64 25 64 60) <| .cons (carry s13 64 25 64 60) <|
    .cons (carry s12 64 25 64 60) <| .cons (carry s11 64 25 64 60) <| .cons (carry s10 64 25 64 60) <| .cons (carry s9 64 25 64 60) <|
    .cons (carry s8 64 25 64 60) <| .cons (carry s7 64 25 64 60) <| .cons (carry s6 64 25 64 60) <| .cons (carry s5 64 25 64 60) <|
    .cons (carry s191 16 9 16 12) <| .cons (carry s190 16 9 16 12) <| .cons (carry s274 8 1 16 12) <| .cons (carry s273 8 1 16 12) <|
    .cons (carry s279 4 1 1 0) <| .cons unmarked <| .cons unmarked <| .cons unmarked <|
    .cons s290 <| .cons (carry s272 8 1 16 12) <| .cons (carry s271 8 1 16 12) <| .cons (carry s270 8 1 16 12) <|
    .cons (carry s189 16 9 16 12) <| .cons (carry s4 64 25 64 60) <| .cons (carry s3 64 25 64 60) <| .cons (carry s2 64 25 64 60) <|
    .cons (carry s40 32 25 32 28) <| .cons unmarked <| .cons (carry s39 32 25 32 28) <| .cons (carry s18 32 25 64 60) <|
    .cons (carry s17 32 25 64 60) <| .cons (carry s1 64 25 64 60) <| .cons (carry s0 64 25 64 60) <| .nil
  · decide

lemma gLeaf96 : BoxGood 32 13 64 60 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.both,.down,.down,.down,.down,.down,.down,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 32 13 64 60) <| .cons (carry s15 32 13 64 60) <| .cons (carry s14 32 13 64 60) <| .cons (carry s13 32 13 64 60) <|
    .cons (carry s12 32 13 64 60) <| .cons (carry s11 32 13 64 60) <| .cons (carry s10 32 13 64 60) <| .cons (carry s9 32 13 64 60) <|
    .cons (carry s8 32 13 64 60) <| .cons (carry s7 32 13 64 60) <| .cons (carry s6 32 13 64 60) <| .cons (carry s5 32 13 64 60) <|
    .cons (carry s191 8 5 16 12) <| .cons (carry s190 8 5 16 12) <| .cons (carry s274 4 1 16 12) <| .cons (carry s273 4 1 16 12) <|
    .cons (carry s279 2 1 1 0) <| .cons unmarked <| .cons unmarked <| .cons s293 <|
    .cons s292 <| .cons (carry s272 4 1 16 12) <| .cons (carry s271 4 1 16 12) <| .cons (carry s270 4 1 16 12) <|
    .cons (carry s189 8 5 16 12) <| .cons (carry s4 32 13 64 60) <| .cons (carry s3 32 13 64 60) <| .cons (carry s2 32 13 64 60) <|
    .cons (carry s40 16 13 32 28) <| .cons s291 <| .cons (carry s39 16 13 32 28) <| .cons (carry s18 16 13 64 60) <|
    .cons (carry s17 16 13 64 60) <| .cons (carry s1 32 13 64 60) <| .cons (carry s0 32 13 64 60) <| .nil
  · decide

lemma gLeaf97 : BoxGood 16 6 64 61 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.down,.both,.both,.down,.down,.down,.down,.down,.down,.down,.down,.both,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 16 6 64 61) <| .cons (carry s15 16 6 64 61) <| .cons (carry s14 16 6 64 61) <| .cons (carry s13 16 6 64 61) <|
    .cons (carry s12 16 6 64 61) <| .cons (carry s11 16 6 64 61) <| .cons (carry s10 16 6 64 61) <| .cons (carry s9 16 6 64 61) <|
    .cons (carry s8 16 6 64 61) <| .cons (carry s7 16 6 64 61) <| .cons (carry s6 16 6 64 61) <| .cons (carry s5 16 6 64 61) <|
    .cons (carry s191 4 2 16 13) <| .cons (carry s190 4 2 16 13) <| .cons (carry s274 2 0 16 13) <| .cons (carry s273 2 0 16 13) <|
    .cons unmarked <| .cons s295 <| .cons s294 <| .cons unmarked <|
    .cons unmarked <| .cons (carry s272 2 0 16 13) <| .cons (carry s271 2 0 16 13) <| .cons (carry s270 2 0 16 13) <|
    .cons (carry s189 4 2 16 13) <| .cons (carry s4 16 6 64 61) <| .cons (carry s3 16 6 64 61) <| .cons (carry s2 16 6 64 61) <|
    .cons (carry s40 8 6 32 29) <| .cons unmarked <| .cons (carry s39 8 6 32 29) <| .cons (carry s18 8 6 64 61) <|
    .cons (carry s17 8 6 64 61) <| .cons (carry s1 16 6 64 61) <| .cons (carry s0 16 6 64 61) <| .nil
  · decide

lemma gLeaf98 : BoxGood 16 6 32 31 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.down,.down,.both,.down,.down,.down,.down,.down,.down,.down,.down,.both,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 16 6 32 31) <| .cons (carry s15 16 6 32 31) <| .cons (carry s14 16 6 32 31) <| .cons (carry s13 16 6 32 31) <|
    .cons (carry s12 16 6 32 31) <| .cons (carry s11 16 6 32 31) <| .cons (carry s10 16 6 32 31) <| .cons (carry s9 16 6 32 31) <|
    .cons (carry s8 16 6 32 31) <| .cons (carry s7 16 6 32 31) <| .cons (carry s6 16 6 32 31) <| .cons (carry s5 16 6 32 31) <|
    .cons (carry s191 4 2 8 7) <| .cons (carry s190 4 2 8 7) <| .cons (carry s274 2 0 8 7) <| .cons (carry s273 2 0 8 7) <|
    .cons unmarked <| .cons s298 <| .cons s297 <| .cons s296 <|
    .cons unmarked <| .cons (carry s272 2 0 8 7) <| .cons (carry s271 2 0 8 7) <| .cons (carry s270 2 0 8 7) <|
    .cons (carry s189 4 2 8 7) <| .cons (carry s4 16 6 32 31) <| .cons (carry s3 16 6 32 31) <| .cons (carry s2 16 6 32 31) <|
    .cons (carry s40 8 6 16 15) <| .cons unmarked <| .cons (carry s39 8 6 16 15) <| .cons (carry s18 8 6 32 31) <|
    .cons (carry s17 8 6 32 31) <| .cons (carry s1 16 6 32 31) <| .cons (carry s0 16 6 32 31) <| .nil
  · decide

lemma gLeaf99 : BoxGood 16 7 8 7 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.both,.both,.down,.down,.down,.down,.down,.down,.down,.down,.down,.down,.down,.up,.up,.up,.up,.up])
  · exact .cons (carry s16 16 7 8 7) <| .cons (carry s15 16 7 8 7) <| .cons (carry s14 16 7 8 7) <| .cons (carry s13 16 7 8 7) <|
    .cons (carry s12 16 7 8 7) <| .cons (carry s11 16 7 8 7) <| .cons (carry s10 16 7 8 7) <| .cons (carry s9 16 7 8 7) <|
    .cons (carry s8 16 7 8 7) <| .cons (carry s7 16 7 8 7) <| .cons (carry s6 16 7 8 7) <| .cons (carry s5 16 7 8 7) <|
    .cons (carry s191 4 3 2 1) <| .cons (carry s190 4 3 2 1) <| .cons (carry s274 2 1 2 1) <| .cons (carry s273 2 1 2 1) <|
    .cons unmarked <| .cons unmarked <| .cons unmarked <| .cons s301 <|
    .cons s300 <| .cons (carry s272 2 1 2 1) <| .cons (carry s271 2 1 2 1) <| .cons (carry s270 2 1 2 1) <|
    .cons (carry s189 4 3 2 1) <| .cons (carry s4 16 7 8 7) <| .cons (carry s3 16 7 8 7) <| .cons (carry s2 16 7 8 7) <|
    .cons (carry s40 8 7 4 3) <| .cons s299 <| .cons (carry s39 8 7 4 3) <| .cons (carry s18 8 7 8 7) <|
    .cons (carry s17 8 7 8 7) <| .cons (carry s1 16 7 8 7) <| .cons (carry s0 16 7 8 7) <| .nil
  · decide

lemma gLeaf100 : BoxGood 32 16 2 0 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.down,.down,.down,.down,.down,.down,.down,.down,.both,.up,.up,.up,.up])
  · exact .cons (carry s16 32 16 2 0) <| .cons (carry s15 32 16 2 0) <| .cons (carry s14 32 16 2 0) <| .cons (carry s13 32 16 2 0) <|
    .cons (carry s12 32 16 2 0) <| .cons (carry s11 32 16 2 0) <| .cons (carry s10 32 16 2 0) <| .cons (carry s9 32 16 2 0) <|
    .cons (carry s8 32 16 2 0) <| .cons (carry s7 32 16 2 0) <| .cons (carry s6 32 16 2 0) <| .cons (carry s5 32 16 2 0) <|
    .cons (carry s311 16 0 2 0) <| .cons (carry s310 16 0 2 0) <| .cons (carry s309 16 0 2 0) <| .cons (carry s308 16 0 2 0) <|
    .cons (carry s312 8 0 2 0) <| .cons (carry s313 8 0 1 0) <| .cons (carry s315 4 0 1 0) <| .cons s317 <|
    .cons unmarked <| .cons (carry s307 16 0 2 0) <| .cons (carry s306 16 0 2 0) <| .cons (carry s305 16 0 2 0) <|
    .cons (carry s304 16 0 2 0) <| .cons (carry s4 32 16 2 0) <| .cons (carry s3 32 16 2 0) <| .cons (carry s2 32 16 2 0) <|
    .cons (carry s303 16 0 2 0) <| .cons (carry s302 16 0 2 0) <| .cons unmarked <| .cons s316 <|
    .cons (carry s314 4 0 1 0) <| .cons (carry s1 32 16 2 0) <| .cons (carry s0 32 16 2 0) <| .nil
  · decide

lemma gLeaf101 : BoxGood 32 17 2 0 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.down,.down,.down,.down,.down,.down,.down,.down,.down,.both,.both,.up,.up,.up])
  · exact .cons (carry s16 32 17 2 0) <| .cons (carry s15 32 17 2 0) <| .cons (carry s14 32 17 2 0) <| .cons (carry s13 32 17 2 0) <|
    .cons (carry s12 32 17 2 0) <| .cons (carry s11 32 17 2 0) <| .cons (carry s10 32 17 2 0) <| .cons (carry s9 32 17 2 0) <|
    .cons (carry s8 32 17 2 0) <| .cons (carry s7 32 17 2 0) <| .cons (carry s6 32 17 2 0) <| .cons (carry s5 32 17 2 0) <|
    .cons (carry s311 16 1 2 0) <| .cons (carry s310 16 1 2 0) <| .cons (carry s309 16 1 2 0) <| .cons (carry s308 16 1 2 0) <|
    .cons (carry s312 8 1 2 0) <| .cons (carry s313 8 1 1 0) <| .cons (carry s315 4 1 1 0) <| .cons unmarked <|
    .cons s318 <| .cons (carry s307 16 1 2 0) <| .cons (carry s306 16 1 2 0) <| .cons (carry s305 16 1 2 0) <|
    .cons (carry s304 16 1 2 0) <| .cons (carry s4 32 17 2 0) <| .cons (carry s3 32 17 2 0) <| .cons (carry s2 32 17 2 0) <|
    .cons (carry s303 16 1 2 0) <| .cons (carry s302 16 1 2 0) <| .cons unmarked <| .cons unmarked <|
    .cons (carry s314 4 1 1 0) <| .cons (carry s1 32 17 2 0) <| .cons (carry s0 32 17 2 0) <| .nil
  · decide

lemma gLeaf102 : BoxGood 16 9 2 0 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.down,.down,.down,.down,.down,.down,.down,.down,.down,.both,.both,.up,.up,.up])
  · exact .cons (carry s16 16 9 2 0) <| .cons (carry s15 16 9 2 0) <| .cons (carry s14 16 9 2 0) <| .cons (carry s13 16 9 2 0) <|
    .cons (carry s12 16 9 2 0) <| .cons (carry s11 16 9 2 0) <| .cons (carry s10 16 9 2 0) <| .cons (carry s9 16 9 2 0) <|
    .cons (carry s8 16 9 2 0) <| .cons (carry s7 16 9 2 0) <| .cons (carry s6 16 9 2 0) <| .cons (carry s5 16 9 2 0) <|
    .cons (carry s311 8 1 2 0) <| .cons (carry s310 8 1 2 0) <| .cons (carry s309 8 1 2 0) <| .cons (carry s308 8 1 2 0) <|
    .cons (carry s312 4 1 2 0) <| .cons (carry s313 4 1 1 0) <| .cons (carry s315 2 1 1 0) <| .cons unmarked <|
    .cons s319 <| .cons (carry s307 8 1 2 0) <| .cons (carry s306 8 1 2 0) <| .cons (carry s305 8 1 2 0) <|
    .cons (carry s304 8 1 2 0) <| .cons (carry s4 16 9 2 0) <| .cons (carry s3 16 9 2 0) <| .cons (carry s2 16 9 2 0) <|
    .cons (carry s303 8 1 2 0) <| .cons (carry s302 8 1 2 0) <| .cons unmarked <| .cons unmarked <|
    .cons (carry s314 2 1 1 0) <| .cons (carry s1 16 9 2 0) <| .cons (carry s0 16 9 2 0) <| .nil
  · decide

lemma gLeaf103 : BoxGood 16 10 2 0 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.both,.down,.down,.down,.down,.down,.down,.down,.down,.down,.down,.down,.both,.up,.up,.up])
  · exact .cons (carry s16 16 10 2 0) <| .cons (carry s15 16 10 2 0) <| .cons (carry s14 16 10 2 0) <| .cons (carry s13 16 10 2 0) <|
    .cons (carry s12 16 10 2 0) <| .cons (carry s11 16 10 2 0) <| .cons (carry s10 16 10 2 0) <| .cons (carry s9 16 10 2 0) <|
    .cons (carry s8 16 10 2 0) <| .cons (carry s7 16 10 2 0) <| .cons (carry s6 16 10 2 0) <| .cons (carry s5 16 10 2 0) <|
    .cons (carry s311 8 2 2 0) <| .cons (carry s310 8 2 2 0) <| .cons (carry s309 8 2 2 0) <| .cons (carry s308 8 2 2 0) <|
    .cons (carry s312 4 2 2 0) <| .cons (carry s313 4 2 1 0) <| .cons unmarked <| .cons unmarked <|
    .cons (carry s321 2 0 1 0) <| .cons (carry s307 8 2 2 0) <| .cons (carry s306 8 2 2 0) <| .cons (carry s305 8 2 2 0) <|
    .cons (carry s304 8 2 2 0) <| .cons (carry s4 16 10 2 0) <| .cons (carry s3 16 10 2 0) <| .cons (carry s2 16 10 2 0) <|
    .cons (carry s303 8 2 2 0) <| .cons (carry s302 8 2 2 0) <| .cons (carry s320 2 0 1 0) <| .cons unmarked <|
    .cons s322 <| .cons (carry s1 16 10 2 0) <| .cons (carry s0 16 10 2 0) <| .nil
  · decide

lemma gLeaf104 : BoxGood 16 11 2 0 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.down,.down,.down,.down,.down,.down,.down,.down,.down,.down,.down,.both,.both,.up,.up])
  · exact .cons (carry s16 16 11 2 0) <| .cons (carry s15 16 11 2 0) <| .cons (carry s14 16 11 2 0) <| .cons (carry s13 16 11 2 0) <|
    .cons (carry s12 16 11 2 0) <| .cons (carry s11 16 11 2 0) <| .cons (carry s10 16 11 2 0) <| .cons (carry s9 16 11 2 0) <|
    .cons (carry s8 16 11 2 0) <| .cons (carry s7 16 11 2 0) <| .cons (carry s6 16 11 2 0) <| .cons (carry s5 16 11 2 0) <|
    .cons (carry s311 8 3 2 0) <| .cons (carry s310 8 3 2 0) <| .cons (carry s309 8 3 2 0) <| .cons (carry s308 8 3 2 0) <|
    .cons (carry s312 4 3 2 0) <| .cons (carry s313 4 3 1 0) <| .cons unmarked <| .cons s323 <|
    .cons (carry s321 2 1 1 0) <| .cons (carry s307 8 3 2 0) <| .cons (carry s306 8 3 2 0) <| .cons (carry s305 8 3 2 0) <|
    .cons (carry s304 8 3 2 0) <| .cons (carry s4 16 11 2 0) <| .cons (carry s3 16 11 2 0) <| .cons (carry s2 16 11 2 0) <|
    .cons (carry s303 8 3 2 0) <| .cons (carry s302 8 3 2 0) <| .cons (carry s320 2 1 1 0) <| .cons unmarked <|
    .cons unmarked <| .cons (carry s1 16 11 2 0) <| .cons (carry s0 16 11 2 0) <| .nil
  · decide

lemma gLeaf105 : BoxGood 4 2 2 1 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.both,.both,.down,.down,.down,.down,.down,.down,.down,.down,.down,.down,.both,.up,.up,.up,.up])
  · exact .cons (carry s16 4 2 2 1) <| .cons (carry s15 4 2 2 1) <| .cons (carry s14 4 2 2 1) <| .cons (carry s13 4 2 2 1) <|
    .cons (carry s12 4 2 2 1) <| .cons (carry s11 4 2 2 1) <| .cons (carry s10 4 2 2 1) <| .cons (carry s9 4 2 2 1) <|
    .cons (carry s8 4 2 2 1) <| .cons (carry s7 4 2 2 1) <| .cons (carry s6 4 2 2 1) <| .cons (carry s5 4 2 2 1) <|
    .cons (carry s311 2 0 2 1) <| .cons (carry s310 2 0 2 1) <| .cons (carry s309 2 0 2 1) <| .cons (carry s308 2 0 2 1) <|
    .cons (carry s312 1 0 2 1) <| .cons unmarked <| .cons unmarked <| .cons unmarked <|
    .cons s326 <| .cons (carry s307 2 0 2 1) <| .cons (carry s306 2 0 2 1) <| .cons (carry s305 2 0 2 1) <|
    .cons (carry s304 2 0 2 1) <| .cons (carry s4 4 2 2 1) <| .cons (carry s3 4 2 2 1) <| .cons (carry s2 4 2 2 1) <|
    .cons (carry s303 2 0 2 1) <| .cons (carry s302 2 0 2 1) <| .cons unmarked <| .cons s325 <|
    .cons s324 <| .cons (carry s1 4 2 2 1) <| .cons (carry s0 4 2 2 1) <| .nil
  · decide

lemma gLeaf106 : BoxGood 8 6 2 0 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.down,.down,.down,.down,.down,.down,.down,.down,.down,.down,.down,.down,.both,.both,.up,.up])
  · exact .cons (carry s16 8 6 2 0) <| .cons (carry s15 8 6 2 0) <| .cons (carry s14 8 6 2 0) <| .cons (carry s13 8 6 2 0) <|
    .cons (carry s12 8 6 2 0) <| .cons (carry s11 8 6 2 0) <| .cons (carry s10 8 6 2 0) <| .cons (carry s9 8 6 2 0) <|
    .cons (carry s8 8 6 2 0) <| .cons (carry s7 8 6 2 0) <| .cons (carry s6 8 6 2 0) <| .cons (carry s5 8 6 2 0) <|
    .cons (carry s311 4 2 2 0) <| .cons (carry s310 4 2 2 0) <| .cons (carry s309 4 2 2 0) <| .cons (carry s308 4 2 2 0) <|
    .cons s331 <| .cons unmarked <| .cons (carry s330 2 0 2 0) <| .cons (carry s329 2 0 2 0) <|
    .cons (carry s328 2 0 2 0) <| .cons (carry s307 4 2 2 0) <| .cons (carry s306 4 2 2 0) <| .cons (carry s305 4 2 2 0) <|
    .cons (carry s304 4 2 2 0) <| .cons (carry s4 8 6 2 0) <| .cons (carry s3 8 6 2 0) <| .cons (carry s2 8 6 2 0) <|
    .cons (carry s303 4 2 2 0) <| .cons (carry s302 4 2 2 0) <| .cons (carry s327 2 0 2 0) <| .cons unmarked <|
    .cons unmarked <| .cons (carry s1 8 6 2 0) <| .cons (carry s0 8 6 2 0) <| .nil
  · decide

lemma gLeaf107 : BoxGood 8 6 2 1 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.both,.down,.down,.down,.down,.down,.down,.down,.down,.down,.down,.down,.down,.down,.both,.up,.up,.up])
  · exact .cons (carry s16 8 6 2 1) <| .cons (carry s15 8 6 2 1) <| .cons (carry s14 8 6 2 1) <| .cons (carry s13 8 6 2 1) <|
    .cons (carry s12 8 6 2 1) <| .cons (carry s11 8 6 2 1) <| .cons (carry s10 8 6 2 1) <| .cons (carry s9 8 6 2 1) <|
    .cons (carry s8 8 6 2 1) <| .cons (carry s7 8 6 2 1) <| .cons (carry s6 8 6 2 1) <| .cons (carry s5 8 6 2 1) <|
    .cons (carry s311 4 2 2 1) <| .cons (carry s310 4 2 2 1) <| .cons (carry s309 4 2 2 1) <| .cons (carry s308 4 2 2 1) <|
    .cons unmarked <| .cons unmarked <| .cons (carry s330 2 0 2 1) <| .cons (carry s329 2 0 2 1) <|
    .cons (carry s328 2 0 2 1) <| .cons (carry s307 4 2 2 1) <| .cons (carry s306 4 2 2 1) <| .cons (carry s305 4 2 2 1) <|
    .cons (carry s304 4 2 2 1) <| .cons (carry s4 8 6 2 1) <| .cons (carry s3 8 6 2 1) <| .cons (carry s2 8 6 2 1) <|
    .cons (carry s303 4 2 2 1) <| .cons (carry s302 4 2 2 1) <| .cons (carry s327 2 0 2 1) <| .cons unmarked <|
    .cons s332 <| .cons (carry s1 8 6 2 1) <| .cons (carry s0 8 6 2 1) <| .nil
  · decide

lemma gLeaf108 : BoxGood 8 7 1 0 := by
  apply from_marks (ms := [.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.up,.both,.down,.down,.down,.down,.down,.down,.down,.down,.down,.down,.down,.down,.down,.down,.down,.both,.up,.up])
  · exact .cons (carry s16 8 7 1 0) <| .cons (carry s15 8 7 1 0) <| .cons (carry s14 8 7 1 0) <| .cons (carry s13 8 7 1 0) <|
    .cons (carry s12 8 7 1 0) <| .cons (carry s11 8 7 1 0) <| .cons (carry s10 8 7 1 0) <| .cons (carry s9 8 7 1 0) <|
    .cons (carry s8 8 7 1 0) <| .cons (carry s7 8 7 1 0) <| .cons (carry s6 8 7 1 0) <| .cons (carry s5 8 7 1 0) <|
    .cons (carry s311 4 3 1 0) <| .cons (carry s310 4 3 1 0) <| .cons (carry s309 4 3 1 0) <| .cons (carry s308 4 3 1 0) <|
    .cons unmarked <| .cons s334 <| .cons (carry s330 2 1 1 0) <| .cons (carry s329 2 1 1 0) <|
    .cons (carry s328 2 1 1 0) <| .cons (carry s307 4 3 1 0) <| .cons (carry s306 4 3 1 0) <| .cons (carry s305 4 3 1 0) <|
    .cons (carry s304 4 3 1 0) <| .cons (carry s4 8 7 1 0) <| .cons (carry s3 8 7 1 0) <| .cons (carry s2 8 7 1 0) <|
    .cons (carry s303 4 3 1 0) <| .cons (carry s302 4 3 1 0) <| .cons (carry s327 2 1 1 0) <| .cons s333 <|
    .cons unmarked <| .cons (carry s1 8 7 1 0) <| .cons (carry s0 8 7 1 0) <| .nil
  · decide

lemma gd0 : BoxGood 4 1 2 0 := box_x _ _ _ _ gLeaf1 gLeaf2

lemma gd1 : BoxGood 2 0 2 0 := box_x _ _ _ _ gLeaf0 gd0

lemma gd2 : BoxGood 4 1 4 2 := box_x _ _ _ _ gLeaf4 gLeaf5

lemma gd3 : BoxGood 2 0 4 2 := box_x _ _ _ _ gLeaf3 gd2

lemma gd4 : BoxGood 32 0 128 103 := box_x _ _ _ _ gLeaf9 gLeaf10

lemma gd5 : BoxGood 32 0 64 51 := box_y _ _ _ _ gLeaf8 gd4

lemma gd6 : BoxGood 16 0 64 51 := box_x _ _ _ _ gd5 gLeaf11

lemma gd7 : BoxGood 16 0 32 25 := box_y _ _ _ _ gLeaf7 gd6

lemma gd8 : BoxGood 8 0 32 25 := box_x _ _ _ _ gd7 gLeaf12

lemma gd9 : BoxGood 8 0 16 12 := box_y _ _ _ _ gLeaf6 gd8

lemma gd10 : BoxGood 32 1 128 105 := box_x _ _ _ _ gLeaf15 gLeaf16

lemma gd11 : BoxGood 32 1 64 52 := box_y _ _ _ _ gLeaf14 gd10

lemma gd12 : BoxGood 16 0 64 52 := box_x _ _ _ _ gLeaf13 gd11

lemma gd13 : BoxGood 16 0 64 53 := box_x _ _ _ _ gLeaf17 gLeaf18

lemma gd14 : BoxGood 16 0 32 26 := box_y _ _ _ _ gd12 gd13

lemma gd15 : BoxGood 32 2 128 107 := box_x _ _ _ _ gLeaf21 gLeaf22

lemma gd16 : BoxGood 32 2 64 53 := box_y _ _ _ _ gLeaf20 gd15

lemma gd17 : BoxGood 16 1 64 53 := box_x _ _ _ _ gd16 gLeaf23

lemma gd18 : BoxGood 16 1 32 26 := box_y _ _ _ _ gLeaf19 gd17

lemma gd19 : BoxGood 8 0 32 26 := box_x _ _ _ _ gd14 gd18

lemma gd20 : BoxGood 32 3 128 109 := box_x _ _ _ _ gLeaf27 gLeaf28

lemma gd21 : BoxGood 32 3 64 54 := box_y _ _ _ _ gLeaf26 gd20

lemma gd22 : BoxGood 16 1 64 54 := box_x _ _ _ _ gLeaf25 gd21

lemma gd23 : BoxGood 16 1 64 55 := box_x _ _ _ _ gLeaf29 gLeaf30

lemma gd24 : BoxGood 16 1 32 27 := box_y _ _ _ _ gd22 gd23

lemma gd25 : BoxGood 8 0 32 27 := box_x _ _ _ _ gLeaf24 gd24

lemma gd26 : BoxGood 8 0 16 13 := box_y _ _ _ _ gd19 gd25

lemma gd27 : BoxGood 8 0 8 6 := box_y _ _ _ _ gd9 gd26

lemma gd28 : BoxGood 16 1 16 14 := box_y _ _ _ _ gLeaf32 gLeaf33

lemma gd29 : BoxGood 8 0 16 14 := box_x _ _ _ _ gLeaf31 gd28

lemma gd30 : BoxGood 8 0 16 15 := box_y _ _ _ _ gLeaf34 gLeaf35

lemma gd31 : BoxGood 8 0 8 7 := box_y _ _ _ _ gd29 gd30

lemma gd32 : BoxGood 8 0 4 3 := box_y _ _ _ _ gd27 gd31

lemma gd33 : BoxGood 32 4 128 111 := box_x _ _ _ _ gLeaf40 gLeaf41

lemma gd34 : BoxGood 32 4 64 55 := box_y _ _ _ _ gLeaf39 gd33

lemma gd35 : BoxGood 16 2 64 55 := box_x _ _ _ _ gd34 gLeaf42

lemma gd36 : BoxGood 16 2 32 27 := box_y _ _ _ _ gLeaf38 gd35

lemma gd37 : BoxGood 16 2 16 13 := box_y _ _ _ _ gLeaf37 gd36

lemma gd38 : BoxGood 16 2 8 6 := box_y _ _ _ _ gLeaf36 gd37

lemma gd39 : BoxGood 8 1 8 6 := box_x _ _ _ _ gd38 gLeaf43

lemma gd40 : BoxGood 64 11 128 113 := box_y _ _ _ _ gLeaf47 gLeaf48

lemma gd41 : BoxGood 32 5 128 113 := box_x _ _ _ _ gLeaf46 gd40

lemma gd42 : BoxGood 32 5 64 56 := box_y _ _ _ _ gLeaf45 gd41

lemma gd43 : BoxGood 16 2 64 56 := box_x _ _ _ _ gLeaf44 gd42

lemma gd44 : BoxGood 16 2 64 57 := box_x _ _ _ _ gLeaf49 gLeaf50

lemma gd45 : BoxGood 16 2 32 28 := box_y _ _ _ _ gd43 gd44

lemma gd46 : BoxGood 16 2 16 14 := box_y _ _ _ _ gd45 gLeaf51

lemma gd47 : BoxGood 32 6 64 57 := box_y _ _ _ _ gLeaf53 gLeaf54

lemma gd48 : BoxGood 32 6 32 28 := box_y _ _ _ _ gLeaf52 gd47

lemma gd49 : BoxGood 32 6 16 14 := box_y _ _ _ _ gd48 gLeaf55

lemma gd50 : BoxGood 64 15 32 29 := box_y _ _ _ _ gLeaf58 gLeaf59

lemma gd51 : BoxGood 32 7 32 29 := box_x _ _ _ _ gLeaf57 gd50

lemma gd52 : BoxGood 32 7 16 14 := box_y _ _ _ _ gLeaf56 gd51

lemma gd53 : BoxGood 16 3 16 14 := box_x _ _ _ _ gd49 gd52

lemma gd54 : BoxGood 8 1 16 14 := box_x _ _ _ _ gd46 gd53

lemma gd55 : BoxGood 32 5 16 15 := box_y _ _ _ _ gLeaf61 gLeaf62

lemma gd56 : BoxGood 16 2 16 15 := box_x _ _ _ _ gLeaf60 gd55

lemma gd57 : BoxGood 8 1 16 15 := box_x _ _ _ _ gd56 gLeaf63

lemma gd58 : BoxGood 8 1 8 7 := box_y _ _ _ _ gd54 gd57

lemma gd59 : BoxGood 8 1 4 3 := box_y _ _ _ _ gd39 gd58

lemma gd60 : BoxGood 4 0 4 3 := box_x _ _ _ _ gd32 gd59

lemma gd61 : BoxGood 32 8 64 59 := box_y _ _ _ _ gLeaf67 gLeaf68

lemma gd62 : BoxGood 16 4 64 59 := box_x _ _ _ _ gd61 gLeaf69

lemma gd63 : BoxGood 16 4 32 29 := box_y _ _ _ _ gLeaf66 gd62

lemma gd64 : BoxGood 16 4 16 14 := box_y _ _ _ _ gLeaf65 gd63

lemma gd65 : BoxGood 32 9 64 60 := box_y _ _ _ _ gLeaf71 gLeaf72

lemma gd66 : BoxGood 16 4 64 60 := box_x _ _ _ _ gLeaf70 gd65

lemma gd67 : BoxGood 16 4 32 30 := box_y _ _ _ _ gd66 gLeaf73

lemma gd68 : BoxGood 16 4 16 15 := box_y _ _ _ _ gd67 gLeaf74

lemma gd69 : BoxGood 16 4 8 7 := box_y _ _ _ _ gd64 gd68

lemma gd70 : BoxGood 32 10 32 30 := box_y _ _ _ _ gLeaf76 gLeaf77

lemma gd71 : BoxGood 32 10 16 15 := box_y _ _ _ _ gd70 gLeaf78

lemma gd72 : BoxGood 32 10 8 7 := box_y _ _ _ _ gLeaf75 gd71

lemma gd73 : BoxGood 64 22 64 60 := box_y _ _ _ _ gLeaf80 gLeaf81

lemma gd74 : BoxGood 64 22 32 30 := box_y _ _ _ _ gd73 gLeaf82

lemma gd75 : BoxGood 64 23 32 30 := box_y _ _ _ _ gLeaf83 gLeaf84

lemma gd76 : BoxGood 32 11 32 30 := box_x _ _ _ _ gd74 gd75

lemma gd77 : BoxGood 64 23 32 31 := box_x _ _ _ _ gLeaf86 gLeaf87

lemma gd78 : BoxGood 32 11 32 31 := box_x _ _ _ _ gLeaf85 gd77

lemma gd79 : BoxGood 32 11 16 15 := box_y _ _ _ _ gd76 gd78

lemma gd80 : BoxGood 32 11 8 7 := box_y _ _ _ _ gLeaf79 gd79

lemma gd81 : BoxGood 16 5 8 7 := box_x _ _ _ _ gd72 gd80

lemma gd82 : BoxGood 8 2 8 7 := box_x _ _ _ _ gd69 gd81

lemma gd83 : BoxGood 8 2 4 3 := box_y _ _ _ _ gLeaf64 gd82

lemma gd84 : BoxGood 256 98 128 121 := box_y _ _ _ _ gLeaf92 gLeaf93

lemma gd85 : BoxGood 128 49 128 121 := box_x _ _ _ _ gd84 gLeaf94

lemma gd86 : BoxGood 128 49 64 60 := box_y _ _ _ _ gLeaf91 gd85

lemma gd87 : BoxGood 64 24 64 60 := box_x _ _ _ _ gLeaf90 gd86

lemma gd88 : BoxGood 32 12 64 60 := box_x _ _ _ _ gd87 gLeaf95

lemma gd89 : BoxGood 16 6 64 60 := box_x _ _ _ _ gd88 gLeaf96

lemma gd90 : BoxGood 16 6 32 30 := box_y _ _ _ _ gd89 gLeaf97

lemma gd91 : BoxGood 16 6 16 15 := box_y _ _ _ _ gd90 gLeaf98

lemma gd92 : BoxGood 16 6 8 7 := box_y _ _ _ _ gLeaf89 gd91

lemma gd93 : BoxGood 8 3 8 7 := box_x _ _ _ _ gd92 gLeaf99

lemma gd94 : BoxGood 8 3 4 3 := box_y _ _ _ _ gLeaf88 gd93

lemma gd95 : BoxGood 4 1 4 3 := box_x _ _ _ _ gd83 gd94

lemma gd96 : BoxGood 2 0 4 3 := box_x _ _ _ _ gd60 gd95

lemma gd97 : BoxGood 2 0 2 1 := box_y _ _ _ _ gd3 gd96

lemma gd98 : BoxGood 2 0 1 0 := box_y _ _ _ _ gd1 gd97

lemma gd99 : BoxGood 16 8 2 0 := box_x _ _ _ _ gLeaf100 gLeaf101

lemma gd100 : BoxGood 8 4 2 0 := box_x _ _ _ _ gd99 gLeaf102

lemma gd101 : BoxGood 8 5 2 0 := box_x _ _ _ _ gLeaf103 gLeaf104

lemma gd102 : BoxGood 4 2 2 0 := box_x _ _ _ _ gd100 gd101

lemma gd103 : BoxGood 4 2 1 0 := box_y _ _ _ _ gd102 gLeaf105

lemma gd104 : BoxGood 8 6 1 0 := box_y _ _ _ _ gLeaf106 gLeaf107

lemma gd105 : BoxGood 4 3 1 0 := box_x _ _ _ _ gd104 gLeaf108

lemma gd106 : BoxGood 2 1 1 0 := box_x _ _ _ _ gd103 gd105

lemma gd107 : BoxGood 1 0 1 0 := box_x _ _ _ _ gd98 gd106

lemma good_tables : Good tables := box_root gd107

open Polynomial

noncomputable def pack (f : Fin 35 → ℝ) : Polynomial ℝ :=
  ∑ i : Fin 35, Polynomial.monomial (i:ℕ) (f i)

lemma pack_coeff (f : Fin 35 → ℝ) (i : Fin 35) : (pack f).coeff i = f i := by
  classical
  simp only [pack, finsetSum_coeff, coeff_monomial]
  simp [← Fin.ext_iff]

lemma pack_degree (f : Fin 35 → ℝ) (hf : f 34 ≠ 0) : (pack f).degree = 34 := by
  apply le_antisymm
  · apply (degree_le_iff_coeff_zero _ _).mpr; intro n hn
    have hn' : 34 < n := by exact_mod_cast hn
    simp only [pack,finsetSum_coeff,coeff_monomial]
    apply Finset.sum_eq_zero; intro i _; rw [if_neg (by omega)]
  · apply le_degree_of_ne_zero
    change (pack f).coeff ((34:Fin 35):ℕ) ≠ 0
    simpa only [pack_coeff] using hf

lemma pack_eval (f : Fin 35 → ℝ) (x : ℝ) : (pack f).eval x = ∑ i, f i*x^(i:ℕ) := by
  simp [pack,eval_finsetSum,eval_monomial]

lemma pack_coeffList (f : Fin 35 → ℝ) (hf : f 34 ≠ 0) :
    (pack f).coeffList = (List.ofFn f).reverse := by
  rw [coeffList, pack_degree f hf,List.map_reverse]; congr 1
  apply List.ext_getElem
  · simp
  · intro n hn₁ hn₂; simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    apply pack_coeff f ⟨n,by simpa using hn₂⟩

lemma count_root_image {α : Type*} (s : Set α) (P : Polynomial ℝ) (f : α → ℝ)
    (hP : P ≠ 0) (hm : ∀ x ∈ s, 0 < f x ∧ P.eval (f x) = 0) (hi : Set.InjOn f s) :
    s.encard ≤ (P.roots.countP (0 < ·) : ℕ) := by
  classical
  let m := P.roots.filter (0 < ·)
  have maps : Set.MapsTo f s (m.toFinset : Set ℝ) := by
    intro x hx; obtain ⟨hp,he⟩ := hm x hx
    simp [m,Polynomial.mem_roots hP, Polynomial.IsRoot,he,hp]
  calc s.encard ≤ (m.toFinset : Set ℝ).encard := Set.encard_le_encard_of_injOn maps hi
    _ = ↑m.toFinset.card := Set.encard_coe_eq_coe_finsetCard _
    _ ≤ (m.card:ℕ) := by exact_mod_cast m.toFinset_card_le
    _ = _ := by rw [Multiset.countP_eq_card_filter]

noncomputable def eliminant (L M : ℝ) : Polynomial ℝ := pack (coeffs L M)

lemma leading_cf (L M : ℝ) : coeffs L M 34 ≠ 0 := by change 32*(4:ℝ) ≠ 0; norm_num

lemma elim_ne_zero (L M : ℝ) : eliminant L M ≠ 0 := by
  have hd := pack_degree _ (leading_cf L M)
  intro hz; change pack _ = 0 at hz; rw [hz] at hd; simp at hd

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 10000 in
lemma eliminant_eval (L M t : ℝ) : (eliminant L M).eval t = 32*elim (t+1) L M := by
  rw [eliminant,pack_eval]
  norm_num [Fin.sum_univ_succ,coeffs,cf0,cf1,cf2,cf3,cf4,cf5,cf6,cf7,cf8,cf9,cf10,cf11,cf12,cf13,cf14,cf15,cf16,cf17,cf18,cf19,cf20,cf21,cf22,cf23,cf24,cf25,cf26,cf27,cf28,cf29,cf30,cf31,cf32,cf33,cf34,elim,b50,b40,b31,b30,b22,b21,b20,b12,b11,b10,b03,b02,b01,b00]; grobner

def diagonal {R : Type*} [CommRing R] (L u : R) : R := -8*L*u^4 + 32*L + u^6 + 4*u^4 + 8*u^3

def reflected {R : Type*} [CommRing R] (L u : R) : R := -54*L^2*u^6 + 4*L*u^12 + 12*L*u^9 - 27*L*u^8 + 18*L*u^6 + 12*L*u^5 + 6*L*u^4 + 2*L*u^3 - 3*L*u^2 + L + 2*u^14 - 4*u^12 - 2*u^11 - 4*u^10 + 8*u^8 + 4*u^7 + 2*u^6 - 4*u^4 - 2*u^3

lemma diagonal_zero (u L : ℝ) (h : L * den u 0 = num u 0) : diagonal L u = 0 := by
  unfold den num at h; unfold diagonal; linear_combination -h

set_option maxHeartbeats 1000000 in
lemma reflected_zero (u q L : ℝ) (hd : den u q ≠ 0) (h : L * den u q = num u q)
    (hz : dif u q = 0) : reflected L u = 0 := by
  let d := den u q
  have hd' : d ≠ 0 := hd
  suffices H : 2*(reflected L u*d^2) = 0 by
    exact (mul_eq_zero.mp ((mul_eq_zero.mp H).resolve_left (by norm_num))).resolve_right (pow_ne_zero 2 hd')
  calc 2*(reflected L u*d^2) = 2*((-54*u^6)*(L*d)^2+(4*u^12 + 12*u^9 - 27*u^8 + 18*u^6 + 12*u^5 + 6*u^4 + 2*u^3 - 3*u^2 + 1)*(L*d)*d+(2*u^14 - 4*u^12 - 2*u^11 - 4*u^10 + 8*u^8 + 4*u^7 + 2*u^6 - 4*u^4 - 2*u^3)*d^2) := by unfold reflected; ring
       _ = dif u q*(144*q^4*u^6 + 72*q^4*u^5 + 9*q^4*u^4 + 960*q^3*u^8 - 24*q^3*u^7 - 66*q^3*u^6 + 192*q^3*u^5 + 120*q^3*u^4 + 42*q^3*u^3 + 6*q^3*u^2 + 64*q^2*u^13 + 16*q^2*u^12 + 2032*q^2*u^10 - 808*q^2*u^9 + 112*q^2*u^8 + 640*q^2*u^7 - 848*q^2*u^6 - 166*q^2*u^5 + 38*q^2*u^4 + 8*q^2*u^3 + 40*q^2*u^2 + 40*q^2*u + 8*q^2 + 192*q*u^15 - 64*q*u^14 + 1280*q*u^12 - 824*q*u^11 - 30*q*u^10 + 384*q*u^9 - 2504*q*u^8 + 1454*q*u^7 + 98*q*u^6 - 704*q*u^5 - 464*q*u^4 - 192*q*u^3 - 112*q*u^2 + 32*q*u + 32*q - 80*u^16 + 64*u^14 - 272*u^13 + 359*u^12 - 64*u^11 - 992*u^10 + 398*u^9 - 398*u^8 - 648*u^7 + 424*u^6 + 216*u^5 + 104*u^4 + 160*u^3 - 288*u^2 - 192*u) := by change L*d=num u q at h; rw [h]; dsimp [d, den, num, dif]; grobner
       _ = 0 := by rw [hz,zero_mul]

noncomputable def diagPoly (L : ℝ) : Polynomial ℝ := diagonal (Polynomial.C L) (Polynomial.X+1)
noncomputable def reflPoly (L : ℝ) : Polynomial ℝ := reflected (Polynomial.C L) (Polynomial.X+1)

lemma diagPoly_eval (L t : ℝ) : (diagPoly L).eval t = diagonal L (t+1) := by simp [diagPoly,diagonal]
lemma reflPoly_eval (L t : ℝ) : (reflPoly L).eval t = reflected L (t+1) := by simp [reflPoly,reflected]

set_option maxHeartbeats 1000000 in
lemma symmetric_factor (L : ℝ) : eliminant L 0 = Polynomial.C 32 * diagPoly L * (reflPoly L)^2 := by
  apply Polynomial.funext
  intro t
  rw [eliminant_eval]; simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,diagPoly_eval,reflPoly_eval]
  unfold elim diagonal reflected b50 b40 b31 b30 b22 b21 b20 b12 b11 b10 b03 b02 b01 b00; grobner

lemma class_count {α : Type*} (s : Set α) (f z : α → ℝ) (D R : Polynomial ℝ)
    (hD : D ≠ 0) (hR : R ≠ 0)
    (hp : ∀ x ∈ s, 0 < f x)
    (h0 : ∀ x ∈ s, z x = 0 → D.eval (f x) = 0)
    (h1 : ∀ x ∈ s, z x ≠ 0 → R.eval (f x) = 0)
    (hi : ∀ x ∈ s, ∀ y ∈ s, f x=f y → z x=z y → x=y)
    (hs : ∀ x ∈ s, ∀ y ∈ s, f x=f y → (z x)^2=(z y)^2) :
    s.encard ≤ ((D.roots.countP (0 < ·) + R.roots.countP (0 < ·) + R.roots.countP (0 < ·) : ℕ) : ℕ∞) := by
  let s₀ := {x ∈ s | z x=0}
  let spos := {x ∈ s | 0 < z x}
  let sneg := {x ∈ s | z x < 0}
  have e0 : s₀.encard ≤ (D.roots.countP (0 < ·) : ℕ) := by
    refine count_root_image _ _ _ hD (fun x hx => ⟨hp x hx.1,h0 x hx.1 hx.2⟩) ?_
    intro x hx y hy h; exact hi x hx.1 y hy.1 h (hx.2.trans hy.2.symm)
  have ep : spos.encard ≤ (R.roots.countP (0 < ·) : ℕ) := by
    refine count_root_image _ _ _ hR (fun x hx => ⟨hp x hx.1,h1 x hx.1 hx.2.ne'⟩) ?_
    intro x hx y hy h; apply hi x hx.1 y hy.1 h
    have hz := hs x hx.1 y hy.1 h
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp hz).resolve_right (by linarith [hx.2,hy.2])
  have em : sneg.encard ≤ (R.roots.countP (0 < ·) : ℕ) := by
    refine count_root_image _ _ _ hR (fun x hx => ⟨hp x hx.1,h1 x hx.1 hx.2.ne⟩) ?_
    intro x hx y hy h; apply hi x hx.1 y hy.1 h
    have hz := hs x hx.1 y hy.1 h
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp hz).resolve_right (by linarith [hx.2,hy.2])
  have sub : s ⊆ s₀ ∪ spos ∪ sneg := by
    intro x hx; rcases lt_trichotomy (z x) 0 with h|h|h
    · exact Or.inr ⟨hx,h⟩
    · exact Or.inl (Or.inl ⟨hx,h⟩)
    · exact Or.inl (Or.inr ⟨hx,h⟩)
  calc s.encard ≤ (s₀ ∪ spos ∪ sneg).encard := Set.encard_le_encard sub
    _ ≤ (s₀ ∪ spos).encard + sneg.encard := Set.encard_union_le _ _
    _ ≤ s₀.encard + spos.encard + sneg.encard := add_le_add_left (Set.encard_union_le _ _) _
    _ ≤ _ := by push_cast; exact add_le_add (add_le_add e0 ep) em

lemma count_for_shape (A B C : Plane) (hc : 0 < ds A B) (ha : 0 < ds B C) (hb : 0 < ds A C)
    (h₁ : ds B C ≤ ds A B) (h₂ : ds A C ≤ ds A B) :
    (eliminant (shapeL A B C) ((shapeJ A B C)^2)).roots.countP (0 < ·) ≤ 4 := by
  obtain ⟨x,v,hx0,hx1,hv0,hv1,hL,hM⟩ := choose_chart hc ha hb h₁ h₂
  obtain ⟨ms,hm,hs⟩ := good_tables x (1-x) v (1-v) hx0 (by linarith) hv0 (by linarith)
  apply (Polynomial.roots_countP_pos_le_signVariations _).trans
  refine (changes_bound _ ms ?_).trans hm
  rw [eliminant,pack_coeffList _ (leading_cf _ _),hL,hM,← table_values]
  exact hs

lemma longest_bound (A B C : Plane) (hc : 0 < ds A B) (ha : 0 < ds B C) (hb : 0 < ds A C)
    (h₁ : ds B C ≤ ds A B) (h₂ : ds A C ≤ ds A B) : {p | Equil p A B C}.encard ≤ 4 := by
  classical
  let s := {p | Equil p A B C}
  let a (p : Plane) := ratioA p A C
  let b (p : Plane) := ratioA p B C
  let f (p : Plane) := a p + b p - 1
  let z (p : Plane) := a p - b p
  let L := shapeL A B C
  let J := shapeJ A B C
  let P := eliminant L (J^2)
  have he (p : Plane) (hp : p ∈ s) : Balance p A B C (a p) (b p) := equil_balance hp
  have hf (p : Plane) (hp : p ∈ s) : 0 < f p := sub_pos.mpr ((he p hp).sum_gt_one hc)
  have hsum (p : Plane) : f p + 1 = a p + b p := by simp [f]
  have hbound : P.roots.countP (0 < ·) ≤ 4 := count_for_shape A B C hc ha hb h₁ h₂
  change s.encard ≤ 4
  suffices HS : s.encard ≤ (P.roots.countP (0 < ·) : ℕ) by exact HS.trans (by exact_mod_cast hbound)
  by_cases hJ : J=0
  · have hsP : P = Polynomial.C 32 * diagPoly L * reflPoly L ^ 2 := by
      dsimp only [P]; rw [hJ,zero_pow (by decide),symmetric_factor]
    have hPn : P ≠ 0 := elim_ne_zero _ _
    have hd : diagPoly L ≠ 0 := by intro e; simp [hsP,e] at hPn
    have hr : reflPoly L ≠ 0 := by intro e; simp [hsP,e] at hPn
    have hconst : (Polynomial.C 32 : Polynomial ℝ) ≠ 0 := by simp
    have hnr : P.roots.countP (0 < ·) = (diagPoly L).roots.countP (0 < ·) +
        (reflPoly L).roots.countP (0 < ·) + (reflPoly L).roots.countP (0 < ·) := by
      rw [hsP,pow_two,Polynomial.roots_mul (mul_ne_zero (mul_ne_zero hconst hd) (mul_ne_zero hr hr)),
        Polynomial.roots_mul (mul_ne_zero hconst hd),Polynomial.roots_mul (mul_ne_zero hr hr)]
      simp [Multiset.countP_add,add_assoc]
    rw [hnr]
    apply class_count s f z (diagPoly L) (reflPoly L) hd hr hf
    · intro p hp hz
      obtain ⟨_,hx,_⟩ := (he p hp).shape hc
      change L * den (a p+b p) (z p ^ 2) = _ at hx
      change L * den (a p+b p) (z p ^ 2) = num (a p+b p) (z p ^ 2) at hx
      rw [hz] at hx; norm_num only [zero_pow] at hx
      rw [diagPoly_eval,hsum]; exact diagonal_zero _ _ hx
    · intro p hp hz
      obtain ⟨hd',hl,hz'⟩ := (he p hp).shape hc
      change J * den (a p+b p) (z p^2) = z p * dif (a p+b p) (z p^2) at hz'
      rw [hJ,zero_mul] at hz'
      rw [reflPoly_eval,hsum]
      exact reflected_zero _ _ _ hd'.ne' hl ((mul_eq_zero.mp hz'.symm).resolve_left hz)
    · intro p hp p' hp' H K
      have Hs : a p+b p = a p'+b p' := sub_left_inj.mp H
      change a p-b p=a p'-b p' at K
      have aa : a p = a p' := by linarith
      have bb : b p = b p' := by linarith
      exact (he p hp).unique_point (aa ▸ bb ▸ he p' hp')
    · intro p hp p' hp' H
      obtain ⟨_,hL,_⟩ := (he p hp).shape hc
      obtain ⟨_,hL',_⟩ := (he p' hp').shape hc
      have Hs : a p+b p = a p'+b p' := sub_left_inj.mp H
      have hp'b := (he p' hp').diff_sq_bound
      rw [← Hs] at hL' hp'b
      exact same_diff_sq ((he p hp).sum_gt_one hc) (sq_nonneg _) (sq_nonneg _) (he p hp).diff_sq_bound hp'b hL hL'
  · apply count_root_image s P f (elim_ne_zero _ _)
    · intro p hp; refine ⟨hf p hp,?_⟩
      change (eliminant L (J^2)).eval (f p) = 0
      rw [eliminant_eval,hsum,(he p hp).eliminant hc,mul_zero]
    · intro p hp p' hp' h
      exact unique_sum hc (he p hp) (he p' hp') (sub_left_inj.mp h) hJ

lemma ds_comm (A B : Plane) : ds A B = ds B A := by unfold ds; ring

lemma cycle_equil {p A B C : Plane} (h : Equil p A B C) : Equil p B C A := by
  obtain ⟨ha,hb,hc,hx,hy⟩ := h; exact ⟨hb,hc,ha,by linarith,by linarith⟩

lemma triangle_bound (A B C : Plane) (hab : 0 < ds A B) (hbc : 0 < ds B C)
    (hac : 0 < ds A C) : {p | Equil p A B C}.encard ≤ 4 := by
  have hca : 0 < ds C A := ds_comm A C ▸ hac
  have hba : 0 < ds B A := ds_comm A B ▸ hab
  have hcb : 0 < ds C B := ds_comm B C ▸ hbc
  by_cases h : ds B C ≤ ds A B
  · by_cases k : ds A C ≤ ds A B
    · exact longest_bound A B C hab hbc hac h k
    · refine (Set.encard_le_encard (t := {p | Equil p C A B}) (fun p hp => cycle_equil (cycle_equil hp))).trans ?_
      exact longest_bound C A B hca hab hcb (by rw [ds_comm C A]; linarith) (by rw [ds_comm C B, ds_comm C A]; linarith)
  · by_cases k : ds A C ≤ ds B C
    · refine (Set.encard_le_encard (t := {p | Equil p B C A}) (fun p hp => cycle_equil hp)).trans ?_
      exact longest_bound B C A hbc hca hba (by rwa [ds_comm C A]) (by rw [ds_comm B A]; linarith)
    · refine (Set.encard_le_encard (t := {p | Equil p C A B}) (fun p hp => cycle_equil (cycle_equil hp))).trans ?_
      exact longest_bound C A B hca hab hcb (by rw [ds_comm C A]; linarith) (by rw [ds_comm C B,ds_comm C A]; linarith)

end OMA.MaxwellH1Astra

theorem OMA.solution :
    OMA.R_Arxiv_2607_27197_maxwell_conjecture_variants_three_equal_magnitudes_R1.H1 := by
  intro q u w hw hq heq _
  let A : OMA.MaxwellH1Astra.Plane := (0,0)
  let B : OMA.MaxwellH1Astra.Plane := (1,0)
  let C : OMA.MaxwellH1Astra.Plane := (u,w)
  have hab : 0 < OMA.MaxwellH1Astra.ds A B := by norm_num [OMA.MaxwellH1Astra.ds,A,B]
  have hbc : 0 < OMA.MaxwellH1Astra.ds B C := by
    dsimp [OMA.MaxwellH1Astra.ds,B,C]; nlinarith [sq_pos_of_ne_zero hw, sq_nonneg (1-u)]
  have hac : 0 < OMA.MaxwellH1Astra.ds A C := by
    dsimp [OMA.MaxwellH1Astra.ds,A,C]; nlinarith [sq_pos_of_ne_zero hw, sq_nonneg u]
  refine (Set.encard_le_encard (t := {p | OMA.MaxwellH1Astra.Equil p A B C}) ?_).trans
    (OMA.MaxwellH1Astra.triangle_bound A B C hab hbc hac)
  rintro p ⟨hn,hx,hy⟩
  have ef (i : Fin 3) := heq i 0
  have key {x y z r s t : ℝ} (h : q 0*x/r+q 0*y/s+q 0*z/t=0) : x/r+y/s+z/t=0 := by
    apply (mul_eq_zero.mp _).resolve_left (hq 0)
    linear_combination h
  refine ⟨hn 0,hn 1,hn 2,?_,?_⟩
  · apply key; simpa [Fin.sum_univ_three,ef 1,ef 2,OMA.MaxwellH1Astra.rad,OMA.MaxwellH1Astra.ds,A,B,C] using hx
  · apply key; simpa [Fin.sum_univ_three,ef 1,ef 2,OMA.MaxwellH1Astra.rad,OMA.MaxwellH1Astra.ds,A,B,C] using hy
