import FormalConjectures.ErdosProblems.«91»

/-!
# Two nonsimilar optimal configurations on eight points

Eight planar points determine at least four distinct distances, and two
explicit non-similar eight-point configurations in the triangular lattice
each determine four distances.

The underlying proof and infeasibility certificates are due to @drobison00
(PR #3838). The longer coefficient polynomials below are evaluated in
Horner form, retaining the original certificate identities.
-/

namespace OMA.EightDistances

open EuclideanGeometry Erdos91

private def palette (b c : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 1 else if k = 1 then b else c

private def profile (b c : ℝ) (i : Fin 27) : ℝ × ℝ × ℝ :=
  (palette b c (i.val / 9), palette b c (i.val / 3 % 3), palette b c (i.val % 3))

private def delta (t : ℝ) := t * (4 - t)
private def quad (t x y : ℝ) := x^2 + y^2 - (2-t)*x*y
private def u (p : ℝ × ℝ × ℝ) := 1 + p.1 - p.2.1
private def v (p : ℝ × ℝ × ℝ) := 1 + p.1 - p.2.2
private def locus (t : ℝ) (p : ℝ × ℝ × ℝ) := quad t (u p) (v p) - delta t * p.1
private def sep (t : ℝ) (p q : ℝ × ℝ × ℝ) := quad t (u p - u q) (v p - v q)
private def edge (t b c : ℝ) (p q : ℝ × ℝ × ℝ) :=
  let s := sep t p q
  (s - delta t) * (s - b * delta t) * (s - c * delta t)
private def invCondition (t b c z : ℝ) :=
  z*b*c*(b-1)*(c-1)*(b-c)*delta t-1

private def colorsE : Fin 27 → Fin 4 := ![1, 2, 2, 3, 2, 0, 3, 1, 3, 0, 0, 1, 3, 3, 1, 2, 0, 1, 0, 3, 2, 1, 2, 2, 0, 0, 3]

private lemma rejectE_0_7 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, 1, 1) = 0) (h2 : locus 1 (1, c, b) = 0)
    (h3 : edge 1 b c (1, 1, 1) (1, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1/2) * h1

private lemma rejectE_0_11 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, 1, 1) = 0) (h2 : locus 1 (b, 1, c) = 0)
    (h3 : edge 1 b c (1, 1, 1) (b, 1, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1/2) * h1

private lemma rejectE_0_14 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, 1, 1) = 0) (h2 : locus 1 (b, b, c) = 0)
    (h3 : edge 1 b c (1, 1, 1) (b, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1/2) * h1

private lemma rejectE_0_17 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, 1, 1) = 0) (h2 : locus 1 (b, c, c) = 0)
    (h3 : edge 1 b c (1, 1, 1) (b, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1/2) * h1

private lemma rejectE_0_21 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, 1, 1) = 0) (h2 : locus 1 (c, b, 1) = 0)
    (h3 : edge 1 b c (1, 1, 1) (c, b, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1/2) * h1

private lemma rejectE_1_2 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, 1, b) = 0) (h2 : locus 1 (1, 1, c) = 0)
    (h3 : edge 1 b c (1, 1, b) (1, 1, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (3*c*z*(c - 1)*(b - c + 2)) * h1 + (-6*b*z*(c - 1)) * h2

private lemma rejectE_1_4 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, 1, b) = 0) (h2 : locus 1 (1, b, b) = 0)
    (h3 : edge 1 b c (1, 1, b) (1, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((b - 3)/2) * h1 + (-(b - 2)/2) * h2

private lemma rejectE_1_15 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, 1, b) = 0) (h2 : locus 1 (b, c, 1) = 0)
    (h3 : edge 1 b c (1, 1, b) (b, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (z*(b*(b*(b*(108 - 27*b) - 189) + 164) + c*(b*(b*(b*(27*b - 108) + 270) - 251) + c*(b*(270 - 108*b) + c*(b*(27*b - 47) + c*(-b + 9*c - 54) + 81) - 117) + 135) - 54)/27) * h1
    + (z*(-38*b + c*(-100*b + c*(c*(2*b + c*(b + c - 8) + 25) - 46) + 44) - 16)/27) * h2
    + (-z*(c - 1)/27) * h3

private lemma rejectE_1_20 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, 1, b) = 0) (h2 : locus 1 (c, 1, c) = 0)
    (h3 : edge 1 b c (1, 1, b) (c, 1, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (z*(b*(b^2*(12 - 4*b) + 4) + c*(b*(b*(b*(8*b - 12) + 12) - 71) + c*(b*(b*(-24*b - 48) + 51) + c*(b*(48*b + 124) + c*(-56*b + 48*c - 240) + 297) + 21) - 150) + 36)/9) * h1
    + (-2*z*(-36*b + c*(3*b + c*(72*b + c*(-54*b + c*(12*b - 4*c + 10) - 4) - 4) + 10) - 4)/9) * h2
    + (-4*z*(2*c - 1)/9) * h3

private lemma rejectE_1_22 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, 1, b) = 0) (h2 : locus 1 (c, b, b) = 0)
    (h3 : edge 1 b c (1, 1, b) (c, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (z*(b*(b^2*(21 - 7*b) - 21) + c*(b*(b*(b*(5*b + 6) + 21) - 108) + c*(b*(b*(-15*b - 57) + 60) + c*(b*(30*b + 72) + c*(-30*b + 15*c - 66) + 66) + 6) - 39) + 21)/9) * h1
    + (z*(28*b + c*(13*b + c*(-72*b + c*(37*b + c*(-5*b + 5*c - 32) + 50) + 14) - 59) + 14)/9) * h2
    + (-z*(5*c - 7)/9) * h3

private lemma rejectE_1_23 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, 1, b) = 0) (h2 : locus 1 (c, b, c) = 0)
    (h3 : edge 1 b c (1, 1, b) (c, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (z*(b*(b*(b*(b*(1512 - 1512*c) + c*(4536*c - 3024) - 1512) + c*(c*(7560 - 6048*c) - 4536) + 3024) + c*(c*(c*(4144*c - 9856) + 10665) - 4063) - 1592) + c*(c*(c*(c*(5376 - 1176*c) - 11841) + 14703) - 9534) + 2472)/27) * h1
    + (2*z*(4072*b + c*(-7081*b + c*(4536*b + c*(-1372*b + c*(196*b - 28*c - 28) + 56) + 28) + 28) - 56)/27) * h2
    + (56*z*(c - 1)/27) * h3

private lemma rejectE_2_4 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, 1, c) = 0) (h2 : locus 1 (1, b, b) = 0)
    (h3 : edge 1 b c (1, 1, c) (1, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (z*(2043*b + c*(-3393*b + c*(2124*b + c*(-612*b + c*(64*b - 24*c + 148) - 108) - 648) + 1215) - 603)/9) * h1
    + (z*(b*(b*(b*(b*(92 - 8*b) + c*(24*c - 132) - 152) + c*(c*(456 - 88*c) - 432) - 8) + c*(c*(c*(120*c - 692) + 1011) - 63) + 92) + c*(c*(c*(c*(1032 - 120*c) - 3091) + 3576) - 1077) - 152)/9) * h2
    + (4*z*(2*b + 6*c - 19)/9) * h3

private lemma rejectE_2_15 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, 1, c) = 0) (h2 : locus 1 (b, c, 1) = 0)
    (h3 : edge 1 b c (1, 1, c) (b, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (-z*(-54*b + c*(c*(c*(57*b + c*(b - 19*c + 80) - 180) + 252) - 189) + 54)/27) * h1
    + (z*(b*(b*(b*(b*(5 - b) - 4) - 8) + 40) + c*(b*(b*(15*b - 18) - 180) + c*(b*(b*(9 - 8*b) + 90) + c*(b*(b + 52) + c*(-18*b + 8*c - 90) + 283) - 271) + 102) - 32)/27) * h2
    + (z*(b - c + 2)/27) * h3

private lemma rejectE_2_20 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, 1, c) = 0) (h2 : locus 1 (c, 1, c) = 0)
    (h3 : edge 1 b c (1, 1, c) (c, 1, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((c - 3)/2) * h1 + (-(c - 2)/2) * h2

private lemma rejectE_2_22 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, 1, c) = 0) (h2 : locus 1 (c, b, b) = 0)
    (h3 : edge 1 b c (1, 1, c) (c, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (-z*(10557*b + c*(-9720*b + c*(11007*b + c*(-6552*b + c*(1288*b - 1736*c + 4256) + 12345) - 45198) + 39798) - 10557)/27) * h1
    + (z*(b*(b*(b*(b*(56*b - 1120) + c*(8232 - 1568*c) - 2464) + c*(c*(6440*c - 30576) + 24696) - 56) + c*(c*(c*(59864 - 11256*c) - 81903) + 24615) + 1120) + c*(c*(c*(c*(8848*c - 57288) + 119417) - 89488) + 14871) + 2464)/27) * h2
    + (-56*z*(b + 7*c - 22)/27) * h3

private lemma rejectE_2_23 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, 1, c) = 0) (h2 : locus 1 (c, b, c) = 0)
    (h3 : edge 1 b c (1, 1, c) (c, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (-z*(-27*b + c*(99*b + c*(-174*b + c*(54*b + c*(35*b - 25*c + 59) + 21) - 210) + 270) - 81)/9) * h1
    + (-z*(b*(b*(b*(b*(5*b - 47) + 125) - 31) - 164) + c*(b*(b*(141 - 18*b) - 132) + c*(b*(b*(10*b - 111) + 150) + c*(b*(15*b - 75) + c*(15*b + 30*c - 126) + 51) + 298) - 363) + 44)/9) * h2
    + (z*(5*b + 5*c - 22)/9) * h3

private lemma rejectE_3_6 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, b, 1) = 0) (h2 : locus 1 (1, c, 1) = 0)
    (h3 : edge 1 b c (1, b, 1) (1, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (3*c*z*(c - 1)*(b - c + 2)) * h1 + (-6*b*z*(c - 1)) * h2

private lemma rejectE_3_8 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, b, 1) = 0) (h2 : locus 1 (1, c, c) = 0)
    (h3 : edge 1 b c (1, b, 1) (1, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (z*(b*(b^2*(12 - 4*b) + 4) + c*(b*(b*(b*(8*b - 12) + 12) - 71) + c*(b*(b*(-24*b - 48) + 51) + c*(b*(48*b + 124) + c*(-56*b + 48*c - 240) + 297) + 21) - 150) + 36)/9) * h1
    + (-2*z*(-36*b + c*(3*b + c*(72*b + c*(-54*b + c*(12*b - 4*c + 10) - 4) - 4) + 10) - 4)/9) * h2
    + (-4*z*(2*c - 1)/9) * h3

private lemma rejectE_3_12 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, b, 1) = 0) (h2 : locus 1 (b, b, 1) = 0)
    (h3 : edge 1 b c (1, b, 1) (b, b, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((b - 3)/2) * h1 + (-(b - 2)/2) * h2

private lemma rejectE_3_13 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, b, 1) = 0) (h2 : locus 1 (b, b, b) = 0)
    (h3 : edge 1 b c (1, b, 1) (b, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-9/8) * h1 + (-(3*b - 8)/8) * h2

private lemma rejectE_3_19 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, b, 1) = 0) (h2 : locus 1 (c, 1, b) = 0)
    (h3 : edge 1 b c (1, b, 1) (c, 1, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (z*(b*(b*(b*(108 - 27*b) - 189) + 164) + c*(b*(b*(b*(27*b - 108) + 270) - 251) + c*(b*(270 - 108*b) + c*(b*(27*b - 47) + c*(-b + 9*c - 54) + 81) - 117) + 135) - 54)/27) * h1
    + (z*(-38*b + c*(-100*b + c*(c*(2*b + c*(b + c - 8) + 25) - 46) + 44) - 16)/27) * h2
    + (-z*(c - 1)/27) * h3

private lemma rejectE_3_26 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, b, 1) = 0) (h2 : locus 1 (c, c, c) = 0)
    (h3 : edge 1 b c (1, b, 1) (c, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (z*(b*(b*(b*(192 - 32*b) + 96*c - 192) + c*(135*c - 519) - 32) + c*(c*(405 - 135*c) - 558) + 192)/45) * h1
    + (2*z*(45*b*c^2 - 165*b*c + 96*b + 32)/45) * h2
    + (32*z/45) * h3

private lemma rejectE_4_15 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, b, b) = 0) (h2 : locus 1 (b, c, 1) = 0)
    (h3 : edge 1 b c (1, b, b) (b, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (b*(b*(b*(b*(32637520 - 6504256*b) - 59903152) + 50931064) - 20119056)/280908 + c*(b*(b*(b*(b*(2946944*b - 5105216) + 229232) - 10169108) + 15469858) + c*(b*(b*(b*(2551440 - 4389504*b) + 12718932) - 10293437) + c*(b*(b*(4374048*b - 2833744) - 608284) + c*(b*(-2532208*b - 506334) + c*(1034425*b - 221536*c + 257686) + 2047228) - 6380492) + 8392912) - 5234712)/280908 + 1127417/140454) * h1
    + ((43631*b*c^5 - 169238*b*c^4 - 89848*b*c^3 + 1354751*b*c^2 - 3567062*b*c + 4512590*b + 483*c^6 - 175138*c^5 + 780565*c^4 - 722470*c^3 - 398941*c^2 + 1286860*c - 1973926)/280908) * h2
    + (-(46046*b*c - 101629*b + 483*c^2 - 174655*c + 382925)/280908) * h3

private lemma rejectE_4_20 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, b, b) = 0) (h2 : locus 1 (c, 1, c) = 0)
    (h3 : edge 1 b c (1, b, b) (c, 1, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (b*(b*(b*(b*(911 - 83*b) - 3470) + 6023) - 4361)/243 + c*(b*(b*(b*(b*(22*b - 244) + 1681) - 7819) + 12793) + c*(b*(b*(45*b + 192) - 2646) + c*(b*(b*(1297 - 66*b) - 4639) + c*(b*(2441 - 242*b) + c*(-330*b - 330*c + 2685) - 6614) + 2122) + 10833) - 8419)/243 + 1004/243) * h1
    + (1708*b/243 + c*(-46*b + c*(-158*b + c*(-515*b + c*(548*b + c*(-176*b - 66*c + 709) - 2059) + 1171) + 2095) - 1294)/243 - 761/243) * h2
    + (-(22*b*c - 83*b - 66*c^2 + 181*c + 247)/243) * h3

private lemma rejectE_4_22 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, b, b) = 0) (h2 : locus 1 (c, b, b) = 0)
    (h3 : edge 1 b c (1, b, b) (c, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (z*(b + c*(35*b + c*(60*b + c*(5*b + c*(-2*b + 3*c - 5) - 49) + 57) - 43) + 1)/27) * h1
    + (z*(-b + c*(-116*b + c*(21*b + c*(-5*b + c*(2*b + c - 9) + 20) - 7) + 30) + 1)/27) * h2
    + (-z*(c - 1)/27) * h3

private lemma rejectE_4_23 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, b, b) = 0) (h2 : locus 1 (c, b, c) = 0)
    (h3 : edge 1 b c (1, b, b) (c, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (b*(b*(b*(b*(28266 - 4953*b) - 36720) - 4953) + 30696)/7290 + c*(b*(b*(b*(b*(2852*b - 1223) - 4606) - 92449) + 82963) + c*(b*(b*(b*(-8587*b - 15634) + 74718) - 11323) + c*(b*(b*(17205*b + 23925) - 6336) + c*(b*(-20150*b - 36928) + c*(14446*b - 2945*c + 5470) + 30418) - 92076) + 13445) + 123932)/7290 - 145/27) * h1
    + (-b/3 + c*(-20394*b + c*(13581*b + c*(22071*b + c*(-17670*b + c*(2883*b - 31*c - 10254) + 62817) - 73113) - 63657) + 81504)/7290 + 4/3) * h2
    + (-(2852*b*c - 4953*b - 31*c^2 - 10378*c + 18360)/7290) * h3

private lemma rejectE_5_9 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, b, c) = 0) (h2 : locus 1 (b, 1, 1) = 0)
    (h3 : edge 1 b c (1, b, c) (b, 1, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (z*(b*(b*(b*(135 - 27*b) - 216) + 124) + c*(b*(b*(b*(27*b - 162) + 324) - 343) + c*(b*(b*(27*b - 135) + 162) + c*(b*(27*b - 79) + c*(b + c - 8) + 25) - 46) + 44) - 16)/27) * h1
    + (z*(2*b + c*(46*b + c*(c*(88*b + c*(-b - 18*c + 54) - 135) + 153) - 54))/27) * h2
    + (-z*(c - 1)/27) * h3

private lemma rejectE_5_10 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, b, c) = 0) (h2 : locus 1 (b, 1, b) = 0)
    (h3 : edge 1 b c (1, b, c) (b, 1, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (b*(b*(b*(b*(45646032 - 6504256*b) - 99161168) + 79212824) - 21709474)/280908 + c*(b*(b*(b*(b*(2946944*b - 17503360) + 18280896) + 30004796) - 33522822) + c*(b*(b*(b*(12119120 - 1442560*b) - 38567388) + 54620863) + c*(b*(b*(6376512 - 15456*b) - 25364056) + c*(b*(4251178 - 1105104*b) + c*(43631*b + 483*c - 175138) - 324539) + 5592218) - 12128249) + 6893704)/280908 + 174395/46818) * h1
    + (15604*b/70227 + c*(8950466*b + c*(-35409977*b + c*(20533384*b + c*(-2781646*b + c*(-55223*b + 883568*c - 8267210) + 27511016) - 41760640) + 28315612) - 4800964)/280908 - 127577/46818) * h2
    + (-(46046*b*c - 101629*b + 483*c^2 - 174655*c + 382925)/280908) * h3

private lemma rejectE_5_16 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, b, c) = 0) (h2 : locus 1 (b, c, b) = 0)
    (h3 : edge 1 b c (1, b, c) (b, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (3*z*(c - 1)*(b*c + 2*b - c^2 + c - 1)) * h1 + (-3*z*(c - 1)*(2*b - c^2 + 2*c - 1)) * h2

private lemma rejectE_5_18 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, b, c) = 0) (h2 : locus 1 (c, 1, 1) = 0)
    (h3 : edge 1 b c (1, b, c) (c, 1, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (z*(b*(b*(b*(b*(5 - b) - 4) - 8) + 40) + c*(b*(b*(15*b - 18) - 180) + c*(b*(b*(9 - 8*b) + 90) + c*(b*(b + 52) + c*(-18*b + 8*c - 90) + 283) - 271) + 102) - 32)/27) * h1
    + (-z*(-54*b + c*(c*(c*(57*b + c*(b - 19*c + 80) - 180) + 252) - 189) + 54)/27) * h2
    + (z*(b - c + 2)/27) * h3

private lemma rejectE_5_24 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, b, c) = 0) (h2 : locus 1 (c, c, 1) = 0)
    (h3 : edge 1 b c (1, b, c) (c, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (b*(b*(b*(b*(b*(161*c - 601) - 731*c + 2731) + c*(c*(3354 - 1127*c) + 4226) - 3933) + c*(c*(c*(9177*c - 49830) + 69399) - 43978) + 7592) + c*(c*(c*(c*(111216 - 19320*c) - 157737) + 37902) + 23761) - 5462)/972 + c*(c*(c*(c*(c*(33327*c - 262596) + 715737) - 863843) + 462900) - 86779)/972 + 109/162) * h1
    + (3385*b/486 + c*(-71375*b + c*(163853*b + c*(-166345*b + c*(79366*b + c*(-14329*b + 18193*c - 97258) + 196999) - 196553) + 104756) - 25661)/972 + 53/162) * h2
    + (-(161*b*c - 601*b + 805*c^2 - 3575*c + 2130)/972) * h3

private lemma rejectE_5_25 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, b, c) = 0) (h2 : locus 1 (c, c, b) = 0)
    (h3 : edge 1 b c (1, b, c) (c, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (3*c*z*(b*c - c^2 + 3*c - 1)) * h1 + (-3*c*z*(b - c^2 + 3*c - 1)) * h2

private lemma rejectE_6_8 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, c, 1) = 0) (h2 : locus 1 (1, c, c) = 0)
    (h3 : edge 1 b c (1, c, 1) (1, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((c - 3)/2) * h1 + (-(c - 2)/2) * h2

private lemma rejectE_6_12 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, c, 1) = 0) (h2 : locus 1 (b, b, 1) = 0)
    (h3 : edge 1 b c (1, c, 1) (b, b, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (z*(2043*b + c*(-3393*b + c*(2124*b + c*(-612*b + c*(64*b - 24*c + 148) - 108) - 648) + 1215) - 603)/9) * h1
    + (z*(b*(b*(b*(b*(92 - 8*b) + c*(24*c - 132) - 152) + c*(c*(456 - 88*c) - 432) - 8) + c*(c*(c*(120*c - 692) + 1011) - 63) + 92) + c*(c*(c*(c*(1032 - 120*c) - 3091) + 3576) - 1077) - 152)/9) * h2
    + (4*z*(2*b + 6*c - 19)/9) * h3

private lemma rejectE_6_13 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, c, 1) = 0) (h2 : locus 1 (b, b, b) = 0)
    (h3 : edge 1 b c (1, c, 1) (b, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (z*(b*(b*(135*b - 135*c - 405) + c*(519 - 96*c) + 558) + c*(c*(c*(32*c - 192) + 192) + 32) - 192)/45) * h1
    + (-2*z*(45*b^2*c - 165*b*c + 96*c + 32)/45) * h2
    + (-32*z/45) * h3

private lemma rejectE_6_19 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, c, 1) = 0) (h2 : locus 1 (c, 1, b) = 0)
    (h3 : edge 1 b c (1, c, 1) (c, 1, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (-z*(-54*b + c*(c*(c*(57*b + c*(b - 19*c + 80) - 180) + 252) - 189) + 54)/27) * h1
    + (z*(b*(b*(b*(b*(5 - b) - 4) - 8) + 40) + c*(b*(b*(15*b - 18) - 180) + c*(b*(b*(9 - 8*b) + 90) + c*(b*(b + 52) + c*(-18*b + 8*c - 90) + 283) - 271) + 102) - 32)/27) * h2
    + (z*(b - c + 2)/27) * h3

private lemma rejectE_6_26 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, c, 1) = 0) (h2 : locus 1 (c, c, c) = 0)
    (h3 : edge 1 b c (1, c, 1) (c, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-9/8) * h1 + (-(3*c - 8)/8) * h2

private lemma rejectE_7_11 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, c, b) = 0) (h2 : locus 1 (b, 1, c) = 0)
    (h3 : edge 1 b c (1, c, b) (b, 1, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (-z*(b*(b^2*(b*(3 - 2*b) - 2) + 1) + c*(b*(b*(b*(b*(b + 8) - 8) + 7) - 5) + c*(b*(b*(b*(-4*b - 14) - 5) + 7) + c*(b*(b*(7*b + 22) + 4) + c*(b*(-8*b - 16) + c*(5*b - 2*c + 10) - 17) + 16) - 8) + 1))) * h1
    + (z*(b*c - 2*b - 2*c^2 + 6*c - 1)/27) * h3

private lemma rejectE_7_14 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, c, b) = 0) (h2 : locus 1 (b, b, c) = 0)
    (h3 : edge 1 b c (1, c, b) (b, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (3*z*(c - 1)*(b*c + 2*b - c^2 + c - 1)) * h1 + (-3*z*(c - 1)*(2*b - c^2 + 2*c - 1)) * h2

private lemma rejectE_7_17 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, c, b) = 0) (h2 : locus 1 (b, c, c) = 0)
    (h3 : edge 1 b c (1, c, b) (b, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (3*c*z*(b*c - c^2 + 3*c - 1)) * h1 + (-3*c*z*(b - c^2 + 3*c - 1)) * h2

private lemma rejectE_7_21 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, c, b) = 0) (h2 : locus 1 (c, b, 1) = 0)
    (h3 : edge 1 b c (1, c, b) (c, b, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (-z*(b*(b^2*(b*(3 - 2*b) - 2) + 1) + c*(b*(b*(b*(b*(b + 8) - 8) + 7) - 5) + c*(b*(b*(b*(-4*b - 14) - 5) + 7) + c*(b*(b*(7*b + 22) + 4) + c*(b*(-8*b - 16) + c*(5*b - 2*c + 10) - 17) + 16) - 8) + 1))) * h1
    + (z*(b*c - 2*b - 2*c^2 + 6*c - 1)/27) * h3

private lemma rejectE_8_12 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, c, c) = 0) (h2 : locus 1 (b, b, 1) = 0)
    (h3 : edge 1 b c (1, c, c) (b, b, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (1708*b/243 + c*(-46*b + c*(-158*b + c*(-515*b + c*(548*b + c*(-176*b - 66*c + 709) - 2059) + 1171) + 2095) - 1294)/243 - 761/243) * h1
    + (b*(b*(b*(b*(911 - 83*b) - 3470) + 6023) - 4361)/243 + c*(b*(b*(b*(b*(22*b - 244) + 1681) - 7819) + 12793) + c*(b*(b*(45*b + 192) - 2646) + c*(b*(b*(1297 - 66*b) - 4639) + c*(b*(2441 - 242*b) + c*(-330*b - 330*c + 2685) - 6614) + 2122) + 10833) - 8419)/243 + 1004/243) * h2
    + (-(22*b*c - 83*b - 66*c^2 + 181*c + 247)/243) * h3

private lemma rejectE_8_13 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, c, c) = 0) (h2 : locus 1 (b, b, b) = 0)
    (h3 : edge 1 b c (1, c, c) (b, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (309*b/11 + c*(672*b + c*(-627*b + c*(93*b + c*(271 - 31*c) - 673) + 348) + 372)/33 - 92/11) * h1
    + (-(2*c - 7)/3) * h2
    + ((31*c - 116)/33) * h3

private lemma rejectE_8_19 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, c, c) = 0) (h2 : locus 1 (c, 1, b) = 0)
    (h3 : edge 1 b c (1, c, c) (c, 1, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (3385*b/486 + c*(-71375*b + c*(163853*b + c*(-166345*b + c*(79366*b + c*(-14329*b + 18193*c - 97258) + 196999) - 196553) + 104756) - 25661)/972 + 53/162) * h1
    + (b*(b*(b*(b*(b*(161*c - 601) - 731*c + 2731) + c*(c*(3354 - 1127*c) + 4226) - 3933) + c*(c*(c*(9177*c - 49830) + 69399) - 43978) + 7592) + c*(c*(c*(c*(111216 - 19320*c) - 157737) + 37902) + 23761) - 5462)/972 + c*(c*(c*(c*(c*(33327*c - 262596) + 715737) - 863843) + 462900) - 86779)/972 + 109/162) * h2
    + (-(161*b*c - 601*b + 805*c^2 - 3575*c + 2130)/972) * h3

private lemma rejectE_8_26 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, c, c) = 0) (h2 : locus 1 (c, c, c) = 0)
    (h3 : edge 1 b c (1, c, c) (c, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-9/2) * h1 + (-(3*c - 11)/2) * h2

private lemma rejectE_9_10 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, 1, 1) = 0) (h2 : locus 1 (b, 1, b) = 0)
    (h3 : edge 1 b c (b, 1, 1) (b, 1, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((b - 3)/2) * h1 + (-(b - 2)/2) * h2

private lemma rejectE_9_16 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, 1, 1) = 0) (h2 : locus 1 (b, c, b) = 0)
    (h3 : edge 1 b c (b, 1, 1) (b, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (z*(b*(b^2*(21 - 7*b) - 21) + c*(b*(b*(b*(5*b + 6) + 21) - 108) + c*(b*(b*(-15*b - 57) + 60) + c*(b*(30*b + 72) + c*(-30*b + 15*c - 66) + 66) + 6) - 39) + 21)/9) * h1
    + (z*(28*b + c*(13*b + c*(-72*b + c*(37*b + c*(-5*b + 5*c - 32) + 50) + 14) - 59) + 14)/9) * h2
    + (-z*(5*c - 7)/9) * h3

private lemma rejectE_9_18 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, 1, 1) = 0) (h2 : locus 1 (c, 1, 1) = 0)
    (h3 : edge 1 b c (b, 1, 1) (c, 1, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (3*c*z*(c - 1)*(b - c + 2)) * h1 + (-6*b*z*(c - 1)) * h2

private lemma rejectE_9_24 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, 1, 1) = 0) (h2 : locus 1 (c, c, 1) = 0)
    (h3 : edge 1 b c (b, 1, 1) (c, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (z*(b*(b^2*(12 - 4*b) + 4) + c*(b*(b*(b*(8*b - 12) + 12) - 71) + c*(b*(b*(-24*b - 48) + 51) + c*(b*(48*b + 124) + c*(-56*b + 48*c - 240) + 297) + 21) - 150) + 36)/9) * h1
    + (-2*z*(-36*b + c*(3*b + c*(72*b + c*(-54*b + c*(12*b - 4*c + 10) - 4) - 4) + 10) - 4)/9) * h2
    + (-4*z*(2*c - 1)/9) * h3

private lemma rejectE_9_25 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, 1, 1) = 0) (h2 : locus 1 (c, c, b) = 0)
    (h3 : edge 1 b c (b, 1, 1) (c, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (z*(b*(b*(b*(b*(1512 - 1512*c) + c*(4536*c - 3024) - 1512) + c*(c*(7560 - 6048*c) - 4536) + 3024) + c*(c*(c*(4144*c - 9856) + 10665) - 4063) - 1592) + c*(c*(c*(c*(5376 - 1176*c) - 11841) + 14703) - 9534) + 2472)/27) * h1
    + (2*z*(4072*b + c*(-7081*b + c*(4536*b + c*(-1372*b + c*(196*b - 28*c - 28) + 56) + 28) + 28) - 56)/27) * h2
    + (56*z*(c - 1)/27) * h3

private lemma rejectE_10_16 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, 1, b) = 0) (h2 : locus 1 (b, c, b) = 0)
    (h3 : edge 1 b c (b, 1, b) (b, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (z*(b + c*(35*b + c*(60*b + c*(5*b + c*(-2*b + 3*c - 5) - 49) + 57) - 43) + 1)/27) * h1
    + (z*(-b + c*(-116*b + c*(21*b + c*(-5*b + c*(2*b + c - 9) + 20) - 7) + 30) + 1)/27) * h2
    + (-z*(c - 1)/27) * h3

private lemma rejectE_10_18 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, 1, b) = 0) (h2 : locus 1 (c, 1, 1) = 0)
    (h3 : edge 1 b c (b, 1, b) (c, 1, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (z*(b*(b*(b*(b*(92 - 8*b) + c*(24*c - 132) - 152) + c*(c*(456 - 88*c) - 432) - 8) + c*(c*(c*(120*c - 692) + 1011) - 63) + 92) + c*(c*(c*(c*(1032 - 120*c) - 3091) + 3576) - 1077) - 152)/9) * h1
    + (z*(2043*b + c*(-3393*b + c*(2124*b + c*(-612*b + c*(64*b - 24*c + 148) - 108) - 648) + 1215) - 603)/9) * h2
    + (4*z*(2*b + 6*c - 19)/9) * h3

private lemma rejectE_10_24 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, 1, b) = 0) (h2 : locus 1 (c, c, 1) = 0)
    (h3 : edge 1 b c (b, 1, b) (c, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (b*(b*(b*(b*(911 - 83*b) - 3470) + 6023) - 4361)/243 + c*(b*(b*(b*(b*(22*b - 244) + 1681) - 7819) + 12793) + c*(b*(b*(45*b + 192) - 2646) + c*(b*(b*(1297 - 66*b) - 4639) + c*(b*(2441 - 242*b) + c*(-330*b - 330*c + 2685) - 6614) + 2122) + 10833) - 8419)/243 + 1004/243) * h1
    + (1708*b/243 + c*(-46*b + c*(-158*b + c*(-515*b + c*(548*b + c*(-176*b - 66*c + 709) - 2059) + 1171) + 2095) - 1294)/243 - 761/243) * h2
    + (-(22*b*c - 83*b - 66*c^2 + 181*c + 247)/243) * h3

private lemma rejectE_10_25 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, 1, b) = 0) (h2 : locus 1 (c, c, b) = 0)
    (h3 : edge 1 b c (b, 1, b) (c, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (b*(b*(b*(b*(28266 - 4953*b) - 36720) - 4953) + 30696)/7290 + c*(b*(b*(b*(b*(2852*b - 1223) - 4606) - 92449) + 82963) + c*(b*(b*(b*(-8587*b - 15634) + 74718) - 11323) + c*(b*(b*(17205*b + 23925) - 6336) + c*(b*(-20150*b - 36928) + c*(14446*b - 2945*c + 5470) + 30418) - 92076) + 13445) + 123932)/7290 - 145/27) * h1
    + (-b/3 + c*(-20394*b + c*(13581*b + c*(22071*b + c*(-17670*b + c*(2883*b - 31*c - 10254) + 62817) - 73113) - 63657) + 81504)/7290 + 4/3) * h2
    + (-(2852*b*c - 4953*b - 31*c^2 - 10378*c + 18360)/7290) * h3

private lemma rejectE_11_14 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, 1, c) = 0) (h2 : locus 1 (b, b, c) = 0)
    (h3 : edge 1 b c (b, 1, c) (b, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (3*z*(c - 1)*(b*c + 2*b - c^2 + c - 1)) * h1 + (-3*z*(c - 1)*(2*b - c^2 + 2*c - 1)) * h2

private lemma rejectE_11_17 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, 1, c) = 0) (h2 : locus 1 (b, c, c) = 0)
    (h3 : edge 1 b c (b, 1, c) (b, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (3*c*z*(b*c - c^2 + 3*c - 1)) * h1 + (-3*c*z*(b - c^2 + 3*c - 1)) * h2

private lemma rejectE_11_21 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, 1, c) = 0) (h2 : locus 1 (c, b, 1) = 0)
    (h3 : edge 1 b c (b, 1, c) (c, b, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (-z*(b*(b^2*(b*(3 - 2*b) - 2) + 1) + c*(b*(b*(b*(b*(b + 8) - 8) + 7) - 5) + c*(b*(b*(b*(-4*b - 14) - 5) + 7) + c*(b*(b*(7*b + 22) + 4) + c*(b*(-8*b - 16) + c*(5*b - 2*c + 10) - 17) + 16) - 8) + 1))) * h1
    + (z*(b*c - 2*b - 2*c^2 + 6*c - 1)/27) * h3

private lemma rejectE_12_13 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, b, 1) = 0) (h2 : locus 1 (b, b, b) = 0)
    (h3 : edge 1 b c (b, b, 1) (b, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-9/2) * h1 + (-(3*b - 11)/2) * h2

private lemma rejectE_12_19 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, b, 1) = 0) (h2 : locus 1 (c, 1, b) = 0)
    (h3 : edge 1 b c (b, b, 1) (c, 1, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (b*(b*(b*(b*(32637520 - 6504256*b) - 59903152) + 50931064) - 20119056)/280908 + c*(b*(b*(b*(b*(2946944*b - 5105216) + 229232) - 10169108) + 15469858) + c*(b*(b*(b*(2551440 - 4389504*b) + 12718932) - 10293437) + c*(b*(b*(4374048*b - 2833744) - 608284) + c*(b*(-2532208*b - 506334) + c*(1034425*b - 221536*c + 257686) + 2047228) - 6380492) + 8392912) - 5234712)/280908 + 1127417/140454) * h1
    + ((43631*b*c^5 - 169238*b*c^4 - 89848*b*c^3 + 1354751*b*c^2 - 3567062*b*c + 4512590*b + 483*c^6 - 175138*c^5 + 780565*c^4 - 722470*c^3 - 398941*c^2 + 1286860*c - 1973926)/280908) * h2
    + (-(46046*b*c - 101629*b + 483*c^2 - 174655*c + 382925)/280908) * h3

private lemma rejectE_12_26 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, b, 1) = 0) (h2 : locus 1 (c, c, c) = 0)
    (h3 : edge 1 b c (b, b, 1) (c, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (b*(b*(b*(b*(271 - 31*b) + 93*c - 673) - 627*c + 348) + 672*c + 372)/33 + 309*c/11 - 92/11) * h1
    + (-(2*b - 7)/3) * h2
    + ((31*b - 116)/33) * h3

private lemma rejectE_13_19 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, b, b) = 0) (h2 : locus 1 (c, 1, b) = 0)
    (h3 : edge 1 b c (b, b, b) (c, 1, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((45*b*c^2 - 108*b*c + 6*b + 45*c^3 - 378*c^2 + 729*c - 196)/8) * h1
    + (3*b*(b^2*(31*b - 124) + 93)/8 + 3*c*(b*(b^2*(-15*b - 2) + 327) + c*(b*(b*(30*b + 93) - 180) + c*(b*(-45*b - 62) + c*(30*b - 15*c + 91) - 124) - 45) + 78)/8 + 9/4) * h2
    + (3*(15*c - 31)/8) * h3

private lemma rejectE_13_26 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, b, b) = 0) (h2 : locus 1 (c, c, c) = 0)
    (h3 : edge 1 b c (b, b, b) (c, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (3*c) * h1 + (1) * h2 + (-1/3) * h3

private lemma rejectE_14_17 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, b, c) = 0) (h2 : locus 1 (b, c, c) = 0)
    (h3 : edge 1 b c (b, b, c) (b, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-3*c*z*(c - 1)*(2*b*c - c^2 + 2*c - 1)) * h1 + (3*c*z*(c - 1)*(2*b*c + b - c^2 + c - 1)) * h2

private lemma rejectE_14_21 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, b, c) = 0) (h2 : locus 1 (c, b, 1) = 0)
    (h3 : edge 1 b c (b, b, c) (c, b, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-3*z*(c - 1)*(2*b - c^2 + 2*c - 1)) * h1 + (3*z*(c - 1)*(b*c + 2*b - c^2 + c - 1)) * h2

private lemma rejectE_15_20 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, c, 1) = 0) (h2 : locus 1 (c, 1, c) = 0)
    (h3 : edge 1 b c (b, c, 1) (c, 1, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (b*(b*(b*(b*(b*(161*c - 601) - 731*c + 2731) + c*(c*(3354 - 1127*c) + 4226) - 3933) + c*(c*(c*(9177*c - 49830) + 69399) - 43978) + 7592) + c*(c*(c*(c*(111216 - 19320*c) - 157737) + 37902) + 23761) - 5462)/972 + c*(c*(c*(c*(c*(33327*c - 262596) + 715737) - 863843) + 462900) - 86779)/972 + 109/162) * h1
    + (3385*b/486 + c*(-71375*b + c*(163853*b + c*(-166345*b + c*(79366*b + c*(-14329*b + 18193*c - 97258) + 196999) - 196553) + 104756) - 25661)/972 + 53/162) * h2
    + (-(161*b*c - 601*b + 805*c^2 - 3575*c + 2130)/972) * h3

private lemma rejectE_15_22 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, c, 1) = 0) (h2 : locus 1 (c, b, b) = 0)
    (h3 : edge 1 b c (b, c, 1) (c, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (3*z*(c - 1)*(b*c + 2*b - c^2 + c - 1)) * h1 + (-3*z*(c - 1)*(2*b - c^2 + 2*c - 1)) * h2

private lemma rejectE_15_23 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, c, 1) = 0) (h2 : locus 1 (c, b, c) = 0)
    (h3 : edge 1 b c (b, c, 1) (c, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (3*c*z*(b*c - c^2 + 3*c - 1)) * h1 + (-3*c*z*(b - c^2 + 3*c - 1)) * h2

private lemma rejectE_16_18 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, c, b) = 0) (h2 : locus 1 (c, 1, 1) = 0)
    (h3 : edge 1 b c (b, c, b) (c, 1, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (z*(b*(b*(b*(b*(56*b - 1120) + c*(8232 - 1568*c) - 2464) + c*(c*(6440*c - 30576) + 24696) - 56) + c*(c*(c*(59864 - 11256*c) - 81903) + 24615) + 1120) + c*(c*(c*(c*(8848*c - 57288) + 119417) - 89488) + 14871) + 2464)/27) * h1
    + (-z*(10557*b + c*(-9720*b + c*(11007*b + c*(-6552*b + c*(1288*b - 1736*c + 4256) + 12345) - 45198) + 39798) - 10557)/27) * h2
    + (-56*z*(b + 7*c - 22)/27) * h3

private lemma rejectE_16_24 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, c, b) = 0) (h2 : locus 1 (c, c, 1) = 0)
    (h3 : edge 1 b c (b, c, b) (c, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (b*(b*(b*(b*(699 - 116*b) - 940) - 348) + 705)/81 + c*(b*(b*(b*(b*(31*b - 186) + 825) - 1656) + 885) + c*(b*(b*(1866 - 387*b) - 1680) + c*(b*(b*(62*b - 720) + 1416) + c*(b*(93*b - 627) + c*(93*b + 186*c - 975) + 960) + 516) - 1542) + 3336)/81 - 232/27) * h1
    + (250*b/81 + c*(-1543*b + c*(-917*b + c*(-911*b + c*(428*b + c*(217*b - 155*c + 177) + 324) - 505) + 861) - 333)/81 + 307/81) * h2
    + (-(31*b*c - 116*b + 31*c^2 - 178*c + 235)/81) * h3

private lemma rejectE_16_25 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, c, b) = 0) (h2 : locus 1 (c, c, b) = 0)
    (h3 : edge 1 b c (b, c, b) (c, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-3*c*z*(c - 1)*(2*b*c - c^2 + 2*c - 1)) * h1 + (3*c*z*(c - 1)*(2*b*c + b - c^2 + c - 1)) * h2

private lemma rejectE_17_21 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, c, c) = 0) (h2 : locus 1 (c, b, 1) = 0)
    (h3 : edge 1 b c (b, c, c) (c, b, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-3*c*z*(b - c^2 + 3*c - 1)) * h1 + (3*c*z*(b*c - c^2 + 3*c - 1)) * h2

private lemma rejectE_18_24 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (c, 1, 1) = 0) (h2 : locus 1 (c, c, 1) = 0)
    (h3 : edge 1 b c (c, 1, 1) (c, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((c - 3)/2) * h1 + (-(c - 2)/2) * h2

private lemma rejectE_18_25 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (c, 1, 1) = 0) (h2 : locus 1 (c, c, b) = 0)
    (h3 : edge 1 b c (c, 1, 1) (c, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (-z*(-27*b + c*(99*b + c*(-174*b + c*(54*b + c*(35*b - 25*c + 59) + 21) - 210) + 270) - 81)/9) * h1
    + (-z*(b*(b*(b*(b*(5*b - 47) + 125) - 31) - 164) + c*(b*(b*(141 - 18*b) - 132) + c*(b*(b*(10*b - 111) + 150) + c*(b*(15*b - 75) + c*(15*b + 30*c - 126) + 51) + 298) - 363) + 44)/9) * h2
    + (z*(5*b + 5*c - 22)/9) * h3

private lemma rejectE_19_26 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (c, 1, b) = 0) (h2 : locus 1 (c, c, c) = 0)
    (h3 : edge 1 b c (c, 1, b) (c, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (3*b*(b*(b*(b*(101 - 15*b) - 164) - 45) + 123)/8 + 3*c*(b*(b*(38*b - 180) + 312) + c*(b*(b*(15*b + 123) - 360) + c*(b*(-60*b - 22) + c*(45*b - 30*c + 161) - 164) - 270) + 471)/8 - 135/4) * h1
    + (36*b + c*(-576*b + c*(225*b - 180*c + 648) - 570)/8 + 4) * h2
    + (3*(15*b + 30*c - 41)/8) * h3

private lemma rejectE_20_22 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (c, 1, c) = 0) (h2 : locus 1 (c, b, b) = 0)
    (h3 : edge 1 b c (c, 1, c) (c, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (250*b/81 + c*(-1543*b + c*(-917*b + c*(-911*b + c*(428*b + c*(217*b - 155*c + 177) + 324) - 505) + 861) - 333)/81 + 307/81) * h1
    + (b*(b*(b*(b*(699 - 116*b) - 940) - 348) + 705)/81 + c*(b*(b*(b*(b*(31*b - 186) + 825) - 1656) + 885) + c*(b*(b*(1866 - 387*b) - 1680) + c*(b*(b*(62*b - 720) + 1416) + c*(b*(93*b - 627) + c*(93*b + 186*c - 975) + 960) + 516) - 1542) + 3336)/81 - 232/27) * h2
    + (-(31*b*c - 116*b + 31*c^2 - 178*c + 235)/81) * h3

private lemma rejectE_20_23 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (c, 1, c) = 0) (h2 : locus 1 (c, b, c) = 0)
    (h3 : edge 1 b c (c, 1, c) (c, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-2054*b/243 + c*(26066*b + c*(-22991*b + c*(3970*b + c*(2828*b + c*(-905*b + 724*c - 5713) + 17833) - 25715) + 18641) - 9104)/972 + 16/81) * h1
    + (b*(b*(b*(b*(5875 - 677*b) - 13827) + 2823) + 14940)/972 + c*(b*(b*(b*(b*(181*b - 1571) + 3940) + 480) - 20106) + c*(b*(b*(612*b - 9105) + 40068) + c*(b*(b*(3700 - 181*b) - 24647) + c*(b*(6064 - 362*b) + c*(-543*b - 724*c + 7161) - 26363) + 42873) - 27225) + 9888)/972 - 23/162) * h2
    + (-(181*b*c - 677*b - 362*c^2 + 1231*c + 459)/972) * h3

private lemma rejectE_22_23 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (c, b, b) = 0) (h2 : locus 1 (c, b, c) = 0)
    (h3 : edge 1 b c (c, b, b) (c, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-3*c*z*(c - 1)*(2*b*c - c^2 + 2*c - 1)) * h1 + (3*c*z*(c - 1)*(2*b*c + b - c^2 + c - 1)) * h2

private lemma rejectE_24_25 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (c, c, 1) = 0) (h2 : locus 1 (c, c, b) = 0)
    (h3 : edge 1 b c (c, c, 1) (c, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-2054*b/243 + c*(26066*b + c*(-22991*b + c*(3970*b + c*(2828*b + c*(-905*b + 724*c - 5713) + 17833) - 25715) + 18641) - 9104)/972 + 16/81) * h1
    + (b*(b*(b*(b*(5875 - 677*b) - 13827) + 2823) + 14940)/972 + c*(b*(b*(b*(b*(181*b - 1571) + 3940) + 480) - 20106) + c*(b*(b*(612*b - 9105) + 40068) + c*(b*(b*(3700 - 181*b) - 24647) + c*(b*(6064 - 362*b) + c*(-543*b - 724*c + 7161) - 26363) + 42873) - 27225) + 9888)/972 - 23/162) * h2
    + (-(181*b*c - 677*b - 362*c^2 + 1231*c + 459)/972) * h3

private lemma conflictE (b c z : ℝ) (i j : Fin 27)
    (h0 : invCondition 1 b c z = 0)
    (hi : locus 1 (profile b c i) = 0) (hj : locus 1 (profile b c j) = 0)
    (he : edge 1 b c (profile b c i) (profile b c j) = 0)
    (hlt : i < j) (hcol : colorsE i = colorsE j) : False := by
  fin_cases i
  · have possible : ∀ k : Fin 27, 0 < k → colorsE 0 = colorsE k → k = 7 ∨ k = 11 ∨ k = 14 ∨ k = 17 ∨ k = 21 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl | rfl | rfl
    · exact rejectE_0_7 b c z h0 hi hj he
    · exact rejectE_0_11 b c z h0 hi hj he
    · exact rejectE_0_14 b c z h0 hi hj he
    · exact rejectE_0_17 b c z h0 hi hj he
    · exact rejectE_0_21 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 1 < k → colorsE 1 = colorsE k → k = 2 ∨ k = 4 ∨ k = 15 ∨ k = 20 ∨ k = 22 ∨ k = 23 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl | rfl | rfl | rfl
    · exact rejectE_1_2 b c z h0 hi hj he
    · exact rejectE_1_4 b c z h0 hi hj he
    · exact rejectE_1_15 b c z h0 hi hj he
    · exact rejectE_1_20 b c z h0 hi hj he
    · exact rejectE_1_22 b c z h0 hi hj he
    · exact rejectE_1_23 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 2 < k → colorsE 2 = colorsE k → k = 4 ∨ k = 15 ∨ k = 20 ∨ k = 22 ∨ k = 23 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl | rfl | rfl
    · exact rejectE_2_4 b c z h0 hi hj he
    · exact rejectE_2_15 b c z h0 hi hj he
    · exact rejectE_2_20 b c z h0 hi hj he
    · exact rejectE_2_22 b c z h0 hi hj he
    · exact rejectE_2_23 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 3 < k → colorsE 3 = colorsE k → k = 6 ∨ k = 8 ∨ k = 12 ∨ k = 13 ∨ k = 19 ∨ k = 26 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl | rfl | rfl | rfl
    · exact rejectE_3_6 b c z h0 hi hj he
    · exact rejectE_3_8 b c z h0 hi hj he
    · exact rejectE_3_12 b c z h0 hi hj he
    · exact rejectE_3_13 b c z h0 hi hj he
    · exact rejectE_3_19 b c z h0 hi hj he
    · exact rejectE_3_26 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 4 < k → colorsE 4 = colorsE k → k = 15 ∨ k = 20 ∨ k = 22 ∨ k = 23 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl | rfl
    · exact rejectE_4_15 b c z h0 hi hj he
    · exact rejectE_4_20 b c z h0 hi hj he
    · exact rejectE_4_22 b c z h0 hi hj he
    · exact rejectE_4_23 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 5 < k → colorsE 5 = colorsE k → k = 9 ∨ k = 10 ∨ k = 16 ∨ k = 18 ∨ k = 24 ∨ k = 25 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl | rfl | rfl | rfl
    · exact rejectE_5_9 b c z h0 hi hj he
    · exact rejectE_5_10 b c z h0 hi hj he
    · exact rejectE_5_16 b c z h0 hi hj he
    · exact rejectE_5_18 b c z h0 hi hj he
    · exact rejectE_5_24 b c z h0 hi hj he
    · exact rejectE_5_25 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 6 < k → colorsE 6 = colorsE k → k = 8 ∨ k = 12 ∨ k = 13 ∨ k = 19 ∨ k = 26 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl | rfl | rfl
    · exact rejectE_6_8 b c z h0 hi hj he
    · exact rejectE_6_12 b c z h0 hi hj he
    · exact rejectE_6_13 b c z h0 hi hj he
    · exact rejectE_6_19 b c z h0 hi hj he
    · exact rejectE_6_26 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 7 < k → colorsE 7 = colorsE k → k = 11 ∨ k = 14 ∨ k = 17 ∨ k = 21 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl | rfl
    · exact rejectE_7_11 b c z h0 hi hj he
    · exact rejectE_7_14 b c z h0 hi hj he
    · exact rejectE_7_17 b c z h0 hi hj he
    · exact rejectE_7_21 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 8 < k → colorsE 8 = colorsE k → k = 12 ∨ k = 13 ∨ k = 19 ∨ k = 26 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl | rfl
    · exact rejectE_8_12 b c z h0 hi hj he
    · exact rejectE_8_13 b c z h0 hi hj he
    · exact rejectE_8_19 b c z h0 hi hj he
    · exact rejectE_8_26 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 9 < k → colorsE 9 = colorsE k → k = 10 ∨ k = 16 ∨ k = 18 ∨ k = 24 ∨ k = 25 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl | rfl | rfl
    · exact rejectE_9_10 b c z h0 hi hj he
    · exact rejectE_9_16 b c z h0 hi hj he
    · exact rejectE_9_18 b c z h0 hi hj he
    · exact rejectE_9_24 b c z h0 hi hj he
    · exact rejectE_9_25 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 10 < k → colorsE 10 = colorsE k → k = 16 ∨ k = 18 ∨ k = 24 ∨ k = 25 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl | rfl
    · exact rejectE_10_16 b c z h0 hi hj he
    · exact rejectE_10_18 b c z h0 hi hj he
    · exact rejectE_10_24 b c z h0 hi hj he
    · exact rejectE_10_25 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 11 < k → colorsE 11 = colorsE k → k = 14 ∨ k = 17 ∨ k = 21 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl
    · exact rejectE_11_14 b c z h0 hi hj he
    · exact rejectE_11_17 b c z h0 hi hj he
    · exact rejectE_11_21 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 12 < k → colorsE 12 = colorsE k → k = 13 ∨ k = 19 ∨ k = 26 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl
    · exact rejectE_12_13 b c z h0 hi hj he
    · exact rejectE_12_19 b c z h0 hi hj he
    · exact rejectE_12_26 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 13 < k → colorsE 13 = colorsE k → k = 19 ∨ k = 26 := by decide
    rcases possible j hlt hcol with rfl | rfl
    · exact rejectE_13_19 b c z h0 hi hj he
    · exact rejectE_13_26 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 14 < k → colorsE 14 = colorsE k → k = 17 ∨ k = 21 := by decide
    rcases possible j hlt hcol with rfl | rfl
    · exact rejectE_14_17 b c z h0 hi hj he
    · exact rejectE_14_21 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 15 < k → colorsE 15 = colorsE k → k = 20 ∨ k = 22 ∨ k = 23 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl
    · exact rejectE_15_20 b c z h0 hi hj he
    · exact rejectE_15_22 b c z h0 hi hj he
    · exact rejectE_15_23 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 16 < k → colorsE 16 = colorsE k → k = 18 ∨ k = 24 ∨ k = 25 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl
    · exact rejectE_16_18 b c z h0 hi hj he
    · exact rejectE_16_24 b c z h0 hi hj he
    · exact rejectE_16_25 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 17 < k → colorsE 17 = colorsE k → k = 21 := by decide
    rcases possible j hlt hcol with rfl
    exact rejectE_17_21 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 18 < k → colorsE 18 = colorsE k → k = 24 ∨ k = 25 := by decide
    rcases possible j hlt hcol with rfl | rfl
    · exact rejectE_18_24 b c z h0 hi hj he
    · exact rejectE_18_25 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 19 < k → colorsE 19 = colorsE k → k = 26 := by decide
    rcases possible j hlt hcol with rfl
    exact rejectE_19_26 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 20 < k → colorsE 20 = colorsE k → k = 22 ∨ k = 23 := by decide
    rcases possible j hlt hcol with rfl | rfl
    · exact rejectE_20_22 b c z h0 hi hj he
    · exact rejectE_20_23 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 21 < k → colorsE 21 = colorsE k → False := by decide
    exact possible j hlt hcol
  · have possible : ∀ k : Fin 27, 22 < k → colorsE 22 = colorsE k → k = 23 := by decide
    rcases possible j hlt hcol with rfl
    exact rejectE_22_23 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 23 < k → colorsE 23 = colorsE k → False := by decide
    exact possible j hlt hcol
  · have possible : ∀ k : Fin 27, 24 < k → colorsE 24 = colorsE k → k = 25 := by decide
    rcases possible j hlt hcol with rfl
    exact rejectE_24_25 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 25 < k → colorsE 25 = colorsE k → False := by decide
    exact possible j hlt hcol
  · have possible : ∀ k : Fin 27, 26 < k → colorsE 26 = colorsE k → False := by decide
    exact possible j hlt hcol

private def colorsI : Fin 27 → Fin 4 := ![3, 2, 0, 1, 2, 0, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 0, 1, 2, 0, 1, 2, 0, 3, 3, 0, 0]

private lemma rejectI_0_8 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, 1) = 0) (h2 : locus b (1, c, c) = 0)
    (h3 : edge b b c (1, 1, 1) (1, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (b*z*(b - 4)*(b - 1)*(b - 4*c)) * h1 + (-b*z*(b - 4)*(b - 1)*(b - c - 3)) * h2

private lemma rejectI_0_13 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, 1) = 0) (h2 : locus b (b, b, b) = 0)
    (h3 : edge b b c (1, 1, 1) (b, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-c*z*(c - 1)*(b*c - 4*b + 1)) * h1 + (-c*z*(c - 1)*(b^2 - b*c - b + 3)) * h2

private lemma rejectI_0_14 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, 1) = 0) (h2 : locus b (b, b, c) = 0)
    (h3 : edge b b c (1, 1, 1) (b, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (z*(b*(14 - 28*b) + c*(b*(92*b - 44) + c*(b*(-84*b - 53) + c*(b*(208 - 5*b) + c*(b*(12*b - 71) + c*(21 - 3*b) - 50) - 2) + 14)))/2) * h1
    + (z*(b*(b*(b*(b*(c*(8 - 6*c) + 14) + c*(c*(6*c + 46) - 122) - 42) + c*(c*(c*(-3*c - 50) + 17) + 274) - 14) + c*(c*(c*(21*c + 29) - 185) - 6) + 42) + c^4*(7 - 3*c))/2) * h2
    + (z*(3*c - 7)/2) * h3

private lemma rejectI_0_23 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, 1) = 0) (h2 : locus b (c, b, c) = 0)
    (h3 : edge b b c (1, 1, 1) (c, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (z*(b*(b*(b*(b*(24 - 16*b) - 112) - 485) - 2684) + c*(15002*b + c*(-8808*b + c*(2484*b + c*(-320*b + c*(12*b + 48) - 433) + 1582) - 2684)))/5) * h1
    + (z*(b*(b*(b*(b*(b*(24*c + 8) + c*(-24*c - 152) + 88) + c*(c*(12*c + 52) + 3) + 149) + c*(c*(24*c + 313) - 785) + 1229) + c*(c*(c*(124 - 60*c) - 1259) + 4746) - 8052) + c^4*(12*c - 8))/5) * h2
    + (-4*z*(3*c - 2)/5) * h3

private lemma rejectI_0_24 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, 1) = 0) (h2 : locus b (c, c, 1) = 0)
    (h3 : edge b b c (1, 1, 1) (c, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (z*(b*(-4*b - 1) + c*(12*b + c*(53*b + c*(22*b + c*(-24*b + c*(4*b + 4) - 17) + 10) + 10) - 2) - 5)/9) * h1
    + (z*(b*(b*(b*(b*(b*(4*c - 4) - 36*c + 36) + c*(c*(4*c - 12) + 87) - 79) + c*(c*(61 - 16*c) - 55) + 14) + c*(c*(c*(8 - 4*c) + 9) - 80) + 1) + c*(c*(c*(c*(4*c - 20) + 40) - 40) + 20) - 4)/9) * h2
    + (-4*z*(c - 1)/9) * h3

private lemma rejectI_1_4 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, b) = 0) (h2 : locus b (1, b, b) = 0)
    (h3 : edge b b c (1, 1, b) (1, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(3*b^2 - 8*b - 2)/2) * h1 + ((3*b - 11)/2) * h2

private lemma rejectI_1_9 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, b) = 0) (h2 : locus b (b, 1, 1) = 0)
    (h3 : edge b b c (1, 1, b) (b, 1, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(7*b^2 - 12*b - 3)/3) * h1 + ((7*b - 26)/6) * h2

private lemma rejectI_1_12 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, b) = 0) (h2 : locus b (b, b, 1) = 0)
    (h3 : edge b b c (1, 1, b) (b, b, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((5*b^2 - 9*b - 13)/6) * h1 + (-(5*b - 19)/6) * h2

private lemma rejectI_1_15 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, b) = 0) (h2 : locus b (b, c, 1) = 0)
    (h3 : edge b b c (1, 1, b) (b, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((851392543110912*b*c*z + 214484812474944*b*c - 1303748682122088*b*z + 422738309272314*b - 743103431316*c^2*z - 187204364667*c^2 - 3167122170548556*c*z - 820411429172469*c + 4831117383232944*z - 1399508996973212)/2601785587623728) * h0
    + (b*(143982106399838076 - 64231142702723820*b)/5203571175247456 + c*(b*(107089787421383430*b - 241406180635061628) + c*(b*(145413112022753400 - 66774388591496448*b) + c*(b*(18365408384415768*b - 37822086168003720) + c*(b*(4341806171499816 - 2170903085749908*b) + c*(b*(90939116597682*b - 181878233195364) - 90939116597682*c + 2261842202347590) - 20172555003774948) + 81912531628773504) - 172091936531304078) + 182093621155966236)/5203571175247456 + z*(b*(452023738240592352 - 201109499640549224*b) + c*(b*(333854458284845877*b - 749095427440149716) + c*(b*(441883436249931970 - 205002142550872082*b) + c*(b*(53951082036954024*b - 110555951060912142) + c*(b*(11042138953288022 - 5086430149110550*b) + c*(b*(128453807803251*b - 685877240556390) - 128079399073917*c + 6854209180341403) - 60572091894485346) + 245776576598029182) - 525418342908036473) + 565213703035832927) + z*(b*(5716351594187712 - 2578595019349536*b) + c*(b*(-2073819626711604*b - 7496873805337776) + c*(b*(13728146123532456*b - 1448862955832520) + c*(b*(5248696156081272 - 13941083973181536*b) + c*(b*(5066641041638904*b - 719102994734232) + c*(b*(-424953168124140*b - 852878749973544) + 426439374986772*c + 836705303883540) - 10880159443643160) + 24201046955095272) - 23371899444687708) + 11590126895910276) - 2914091952642720) - 236452158670649600)/5203571175247456 - 37824480417770559/2601785587623728) * h1
    + (b*(b*(b*(b*(b*(b*(c*(5652216232225344*z + 2182538798344368) + z*(-670993866586368*z - 53968345891513152) - 17181053284487904) + c*(c*(-9420360387042240*z - 3637564663907280) + z*(1118323110977280*z + 86179098997705024) + 27180062941916928) + z*(447329244390912*z + 35978897261008768) + 11454035522991936) + c*(c*(c*(3768144154816896*z + 1455025865562912) + z*(-447329244390912*z - 14312068370811616) - 3087636796005192) + z*(-2572143155247744*z - 249270280992490496) - 82229745244786392) + z*(5032453999397760*z + 404762594186348640) + 128857899633659280) + c*(c*(c*(z*(851392543110912*z - 9676893593919408) - 3819442897102644) + z*(105015255232691850 - 980901958706856*z) + 34068164378151840) + z*(73593260047080*z - 64038354325638026) - 17857730198575524) + z*(-4193711666164800*z - 337302161821957200) - 107381583028049400) + c*(c*(c*(c*(z*(-426439374986772*z - 3640064755742979) - 1364086748965230) + z*(59609722497425481 - 4649311188772452*z) + 21378034944733734) + z*(11618264401427412*z - 348740036346786101) - 116404777620446370) + z*(642712150360836*z + 889522136634141415) + 287646404340550398) + z*(-9421872209983584*z - 757805523559997176) - 241250623203017652) + c*(c*(c*(c*(z*(1705757499947088*z + 7023970713338124) + 2546295264735096) + z*(6716556476620056*z - 105170022229757206) - 37686750785186196) + z*(550334955901445098 - 22127594438727144*z) + 182530956683164584) + z*(4797406758952512*z - 1181712654165728528) - 380906103494807700) + z*(11256352236259776*z + 902209554417126224) + 287325800348025984)/5203571175247456 + c*(c*(c*(c*(c*(942036038704224*z + 363756466390728) + z*(-538271686084500*z - 18287005303220515) - 6410134428057582) + z*(120088598279793087 - 571260942879804*z) + 40741627027566006) + z*(3565970578104372*z - 371372931350515325) - 121945623980430978) + z*(1395324919629756*z + 556633502150511561) + 178917566236250694)/5203571175247456 + z*(-4243175957611872*z - 329547962739024800)/5203571175247456 - 52605527175514413/2601785587623728) * h2
    + ((-8089201404*c*z - 3123552813*c + 960296688*z^2 + 77237105132*z + 24588762114)/44682722876) * h3

private lemma rejectI_1_18 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, b) = 0) (h2 : locus b (c, 1, 1) = 0)
    (h3 : edge b b c (1, 1, b) (c, 1, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-c^2 + 4*c - 1) * h0
    + (b*(b*(b - 4) + c^2*z*(c*(c*(c*(60 - 6*c) - 210) + 300) - 144) + c*(c*(c - 5) + 3))/3 + c*(12 - 3*c)/3 + 1/3) * h1
    + (b*(b*(b*(b*(b*(2*c + 2) + c*(3*c - 12) - 15) + c*(c*(c*(3 - 3*z) + 15*z - 14) - 15*z + 11) + 3*z + 31) + c*(c*(c*(c*(6*z + 1) - 27*z - 9) + 15*z + 11) + 9*z + 25) - 3*z - 7) + c*(c*(c*(-24*c*z + 150*z) - 264*z + 3) + 138*z - 10) - 13)/3 + c*(c*(c*(6*c*z - 36*z) + 66*z) - 36*z - 1)/3 - 8/3) * h2
    + (-1/3) * h3

private lemma rejectI_1_21 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, b) = 0) (h2 : locus b (c, b, 1) = 0)
    (h3 : edge b b c (1, 1, b) (c, b, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(c - 2)*(55*b^2 + 55*b*c - 284*b + 55*c^2 - 339*c + 360)/12) * h0
    + (b*(b*(b*(b*(b*(b*(5*b + 55*c*z - 79) - 559*c*z + 503) + c*(1826*z - 10) - 52*z - 1650) + c*(73 - 1562*z) + 309*z + 2989) + c*(-1785*z - 153) - 395*z - 3057) + c*(2061*z + 41) + 71*z + 2042)/12 + c*(c*(-55*c + 220*z + 449) - 696*z - 818)/12 + 67*z/12 - 431/6) * h1
    + (b*(b*(b*(b*(b*(b*(5*b + c*(-55*z - 5) - 99) + c*(-10*c + 559*z + 89) + 779) + c*(c*(5*c + 103) - 1826*z - 586) + 52*z - 3110) + c*(c*(c*(c*(55*z + 5) - 339*z - 54) + 580*z - 342) + 1370*z + 1736) - 413*z + 6649) + c*(c*(c*(c*(-275*z - 19) + 1695*z + 133) - 2955*z + 416) + 2910*z - 2176) + 805*z - 7377) + c*(c*(c*(220*c*z - 1356*z) + 2595*z - 209) - 3654*z + 815) + 63*z + 3530)/12 + c*(-220*c*z + 696*z - 220)/12 - 67*z/12 + 63/2) * h2
    + (-(5*b - 19)/12) * h3

private lemma rejectI_2_5 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, c) = 0) (h2 : locus b (1, b, c) = 0)
    (h3 : edge b b c (1, 1, c) (1, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (-z*(b*(b*(b*(b*(b*(6*b - 36) + 45) + 33) - 24) + 3) + c*(142*b + c*(-54*b + c*(2*b + 11) - 34) - 1))/3) * h1
    + (-z*(b*(b*(b*(b*(b*(6*b - 2*c - 32) + 53) + c*(2*c + 8) - 6) + c*(5*c - 29) - 11) + c*(c*(25 - 2*c) - 40) - 42) + c*(c*(56 - 11*c) - 78) + 32)/3) * h2
    + (z*(3*b - c)/3) * h3

private lemma rejectI_2_16 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, c) = 0) (h2 : locus b (b, c, b) = 0)
    (h3 : edge b b c (1, 1, c) (b, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (z*(c - 1)*(b*(b*(3*c - 5) + c*(-c - 6) + 2) + 2*c^2)) * h1
    + (-z*(c - 1)*(b^2*c - b*c^2 - 5*b + 2*c^2 - 4*c + 2)) * h2

private lemma rejectI_2_19 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, c) = 0) (h2 : locus b (c, 1, b) = 0)
    (h3 : edge b b c (1, 1, c) (c, 1, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((c - 2)*(b^2 + b*c - 2*b - 3*c + 3)/4) * h0
    + (b*(b*(b*(b*(b*(b*(z*(3 - 3*c) - 3) + 2*c + z*(15*c - 27) + 22) - 12*c + z*(18*c + 96) - 39) + c + z*(-177*c - 171) - 15) + 62*c + z*(237*c + 117) + 67) - 41*c + z*(-36*c - 36) - 37)/12 + c*(c*(c*(-c - 2) + 2) + 3)/12 - 7/12) * h1
    + (b*(b*(b*(b*(b*(b*(c*(3*z - 2) - 3*z + 9) + c*(6*c - 15*z - 20) + 27*z - 31) + c*(c*(c*(-3*z - 8) - 3*z + 35) + 10) - 96*z + 39) + c*(c*(c*(8*c + 24*z - 52) + 6*z + 50) + 69*z + 2) + 171*z + 18) + c*(c*(c*(4*c - 57*z + 18) + 33*z - 93) - 75*z + 8) - 117*z - 67) + c*(c*(c*(-6*c + 36*z + 41) - 36*z - 2) - 36*z - 23) + 36*z + 37)/12 + c*(c*(c*(3 - 5*c) + 2) + 10)/12 + 1/12) * h2
    + (-(b - 1)/12) * h3

private lemma rejectI_2_22 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, c) = 0) (h2 : locus b (c, b, b) = 0)
    (h3 : edge b b c (1, 1, c) (c, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (b*(b*(b*(-8110448640*b - 63228361728) + 439511374080) - 656895868416)/46166400 + c*(b*(b*(b*(10234613760*b + 81135196672) - 433688799744) + 668880426240) + c*(b*(b*(b*(-4634542080*b - 36927343616) + 106414985472) - 272192507904) + c*(b*(b*(b*(772423680*b + 6153046016) + 22430123520) + 62643622656) + c*(b*(b*(19496960*b - 10785357312) - 13697935872) + c*(b*(130206720*b + 1138877952) + c*(642216960*b + 149703680*c - 258182656) - 27613855232) + 216602994944) - 702685830656) + 1155134093312) - 930052228096)/46166400 + z*(b*(b*(b*(b*(-5170636800*b - 147964158720) - 43958857152) + 1553824901952) - 2358063413568) + c*(b*(b*(b*(b*(6524851200*b + 187705956480) + 97306231168) - 1225517716320) + 2955915726336) + c*(b*(b*(b*(b*(-2954649600*b - 85223658240) - 65230639104) + 583918363776) - 2524134749088) + c*(b*(b*(b*(b*(492441600*b + 14250109440) + 21989226944) - 477339651216) + 748069255008) + c*(b*(b*(251821281024 - 4016476800*b) + 400693157904) + c*(b*(b*(492441600*b - 47568495360) - 323515238784) + c*(b*(59465462400 - 1285636800*b) + c*(1778078400*b - 1285636800*c - 42073349760) + 423616022528) - 1689485424528) + 3778685015008) - 5431939027760) + 5430456316416) - 3469306079392) + z*(b*(b*(b*(b*(-23267865600*b - 571405726080) - 72427515552) + 1742244058224) - 865243337472) + c*(b*(b*(b*(b*(14819414400*b + 505932451920) + 2247319802268) - 215239270194) + 1483856701632) + c*(b*(b*(b*(b*(5055220800*b + 36293813640) - 1669762792584) - 4819191730551) - 4450877240400) + c*(b*(b*(b*(b*(-6093964800*b - 180717899040) - 311893620246) + 3244557394368) + 4939659515097) + c*(b*(b*(b*(b*(1384992000*b + 70482333600) + 662588337600) + 510252680286) - 714771999864) + c*(b*(b*(b*(-8187480000*b - 222435460800) - 1084000787100) - 1798890000606) + c*(b*(b*(21140028000*b + 344207659950) + 1208380541760) + c*(b*(-30955176000*b - 297470530350) + c*(24030216000*b - 10100160000*c + 139655832750) - 708420195000) + 1615681889550) - 955148051088) - 3212137216035) + 7553824301304) - 6585222190671) + 2371765402710) - 209899613520) + 1001332164288)/46166400 + 751763381/120225) * h0
    + (c*(c*(c*(c*(149703680*c + 41224704) - 27681109504) + 161199551232) - 352605618688)/46166400 + z*(c*(c*(c*(c*(c*(-1285636800*c - 44644623360) + 335612412608) - 973615975952) + 1495840650496) - 1466641750816) + z*(c*z*(c*(c*(c*(c*(c*(c*(c*(c*(c*(285012000*c - 5636131200) + 40376599200) - 147079497600) + 312594206400) - 409655836800) + 331086571200) - 153745603200) + 30562509600) + 2898201600) - 1686031200) + c*(c*(c*(c*(c*(c*(c*(c*(15388800*c - 153888000) - 9530774400) + 118316741550) - 458039406300) + 576693097800) + 658414678812) - 2469926374611) + 1950980015670) - 209660767920) + 1001332164288)/46166400 + 751883606/120225) * h1
    + (-201152*b/1145 + c*(10234613760*b + c*(-4634542080*b + c*(772423680*b + 791920640*c + 3063351296) - 35961814016) + 93493975552)/46166400 + z*(b*(-5170636800*b - 158305432320) + c*(b*(b*(b*(b*(b*(8110448640*b + 38897015808) - 653527805184) + 1761413559552) - 1148322201216) + 195446522880) + c*(b*(b*(b*(b*(b*(-18345062400*b - 89328371200) + 1393767830784) - 3244889750016) + 800901318016) + 1070423611776) + c*(b*(b*(b*(b*(b*(14869155840*b + 73455072768) - 1020389571840) + 1654184161280) + 1843689317120) - 2553035350528) + c*(b*(b*(b*(b*(b*(-5406965760*b - 26859492352) + 307268613888) + 1103529472) - 2331326364928) + 2055713121280) + c*(b*(b*(b*(b*(b*(772423680*b + 3816278016) - 23999456256) - 214681230592) + 989614628096) - 755522642944) + c*(b*(b*(b*(b*(19496960*b - 2477394432) + 39699870208) - 148131309568) + 110889336832) + c*(b*c*(b*(748518400 - 149703680*b) - 598814720) + b*(b*(b*(3319563776 - 642216960*b) - 3111262720) + 433915904))) + 492441600) + 13234448640) - 51215617216) - 17363675904) + 313166219008) + z*(b*(b*(b*(b*(b*(b*(646329600*b + 2739844800) + 1348754400) - 2177834400) - 140414400) - 23928307200) - 619782014880) + c*z*(b*(b*(b*(b*(b*(b*(26639928000*b + 510032285280) - 1725081509088) - 3751977535920) + 4107532502448) + 824424173280) + 5058093600) + c*(b*(b*(b*(b*(b*(b*(2398032000*b - 847615935600) + 1037029744980) + 14345023780998) - 836907575490) - 12856418351208) - 870970337280) + c*(b*(b*(b*(b*(b*(b*(130293825480 - 29656670400*b) + 1935037485612) - 13169521522719) - 20524451381667) + 22693352906934) + 8504539995960) + c*(b*(b*(b*(b*(b*(b*(278618757480 - 2934187200*b) - 1373492811978) - 1396645482825) + 25959996136782) - 4450686262335) - 17074990389924) + c*(b*(b*(b*(b*(b*(b*(3552897600*b - 71328932640) + 126507090474) + 7025466709980) - 4781812499631) - 14563513523475) + 12106822307292) + c*(b*(b*(b*(-3955097770254*b - 8961255192942) + 8807703572844) - 1252286167248) + c*(b*(b*(b*(983114214390*b + 6697398948750) + 1675428927660) - 2347070929200) + c*(b*(b*(b*(-80362393650*b - 1834695027900) - 2985177821850) + 1036768156200) + c*(b*(b*(176474185650*b + 956506083750) - 85033179000) + c*(b*(b*(-2280096000*b - 103899801600) - 26257694400) + c*(b*(2280096000*b + 3420144000) + 1710072000) - 32799211200) + 217868767200) - 695452262400) + 1187644248000) - 1056426537600) + 331069939200) + 177203980800) - 160439529600) + 24562440000) + 5058093600) + c*(b*(b*(b*(b*(b*(b*(5416857600*b + 129697653120) - 428752658208) - 2157981111168) + 6435931703808) - 3973586737152) + 527694415920) + c*(b*(b*(b*(b*(b*(b*(-11633932800*b - 301907088000) + 924992137280) + 4834883001312) - 12849154865952) + 3439438314208) + 4065170593992) + c*(b*(b*(b*(b*(b*(b*(9694944000*b + 245122053120) - 733011308288) - 4550495700192) + 11723903883104) + 3150510328672) - 10072906598656) + c*(b*(b*(b*(b*(b*(b*(-3508646400*b - 90717540480) + 266647283392) + 2939836341456) - 8720624542000) - 6254863246016) + 11921602974848) + c*(b*(b*(b*(b*(b*(b*(492441600*b + 13142115840) - 36796230976) - 1434468055632) + 4383623788608) + 6982656212752) - 9879103776192) + c*(b*(b*(b*(433027002624*b - 920631917360) - 4777547087504) + 5228911378240) + c*(b*(b*(b*(-54962222400*b - 95058483968) + 1683375279040) - 1515518953472) + c*(b*(b*(b*(51633826560 - 1778078400*b) - 225507681600) + 171681623040) + c*(b*(b*(1285636800*b - 6305073600) + 5327212800) + 92332800) - 861772800) + 2785372800) + 9344193600) - 166231027200) + 633274743360) - 708852160686) - 935495255784) + 2606218625628) - 1285197090912) - 355399084992)/46166400 - 29557016/17175) * h2
    + (z^2*(-19236*b + c*z*(-100359*b + c*(-1204920*b + c*(1173240*b + c*(419148*b + c*(-328329*b + c*(41220*b - 16965*c + 267624) - 1231083) + 2156796) - 1505655) + 228924) + 100359) + c*(-7328*b + c*(-1832*b + c*(-6412*b + c*(1832*b - 916*c + 5496) - 6412) + 5496) + 1832) - 14217)/2748) * h3

private lemma rejectI_2_25 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, c) = 0) (h2 : locus b (c, c, b) = 0)
    (h3 : edge b b c (1, 1, c) (c, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (b*(b*(b*(b*(b*(31774682*b + 100787276) + 638155407) + 4068418949) + 24838551842) + 150050375553)/27354 + c*(-898862466723*b + c*(854527172885*b + c*(-488313017096*b + c*(170421953221*b + c*(-33603557662*b + c*(2889063444*b - 1093904016*c + 9956589064) - 40783028878) + 100110095133) - 157658745776) + 153197179543) - 544804285)/27354 + 4064/3) * h1
    + (b*(b*(b*(b*(b*(-26730880*b - 664130352) - 2860993936) - 16990728228) - 104468211984) + 275108805602)/27354 + c*(b*(b*(b*(b*(b*(391308786 - 40681420*b) + 5001480398) + 20936585267) + 134198199601) - 71853865426) + c*(b*(b*(b*(b*(b*(17824142*b + 152828346) - 2407636999) - 14116136088) - 93729400679) - 61834807271) + c*(b*(b*(b*(b*(5640776 - 81227618*b) + 4149971209) + 35516866953) + 69846902366) + c*(b*(b*(b*(126806952*b - 124689858) - 5603005202) - 22242504357) + c*(b*(b*(95234584 - 91158668*b) + 428363318) + c*(598386476*b - 364634672*c - 30738344) + 21933534046) - 123080143985) + 328941581044) - 524277785604) + 446725104016)/27354 - 24981053452/4559) * h2
    + (-(8912071*b*c^2 - 29252781*b*c + 15887341*b - 22789667*c^3 + 120906917*c^2 - 174577013*c + 37028198)/27354) * h3

private lemma rejectI_2_26 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, c) = 0) (h2 : locus b (c, c, c) = 0)
    (h3 : edge b b c (1, 1, c) (c, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (z*(b*(b*(b*(b*(6*b - 36) + 30) - 3) + 6) + c*(-11*b + c*(-106*b + c*(54*b + c*(-22*b + c*(7*b - 6*c + 2) + 59) - 136) + 124) - 50) + 7)/27) * h1
    + (z*(b*(b*(b*(b*(b*(b*(13*c - 6) + c*(-6*c - 126) + 42) + c*(c*(13*c + 29) + 383) - 53) + c*(c*(c*(-6*c - 55) - 30) - 328) - 59) + c*(c*(c*(31*c - 50) + 165) - 238) + 95) + c*(c*(c*(c*(7*c - 26) + 158) - 321) + 243) + 11) + c*(c^2*(c*(c*(9 - 6*c) + 16) - 40) + 47) - 26)/27) * h2
    + (-z*(13*b*c - 6*b - 6*c^2 - 22*c + 7)/27) * h3

private lemma rejectI_3_6 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, b, 1) = 0) (h2 : locus b (1, c, 1) = 0)
    (h3 : edge b b c (1, b, 1) (1, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (b*(b*(b*(b*(b*(146*b - 8) + 8) + 868) + 3464) - 11254)/4 + c*(b*(b*(b*(b*(b*(74*b - 1208) - 342) - 1226) - 8978) + 11590) + c*(b*(b*(b*(b*(b*(270 - 72*b) + 2141) + 2258) + 11212) + 4555) + c*(b*(b*(b*(b*(162*b - 721) - 1741) - 8405) - 12493) + c*(b*(b*(b*(316 - 126*b) + 2165) + 7407) + c*(b*(b*(45*b + 63) - 1172) + c*(-171*b + 45*c + 505) - 4948) + 17682) - 35242) + 40831) - 25370)/4 + 3245/2) * h1
    + (12121*b/2 + c*(-46276*b + c*(35275*b + c*(-13706*b + c*(2822*b + c*(-261*b + 45*c - 80) - 641) + 3746) - 9549) + 12398)/4 - 3243/2) * h2
    + ((36*b*c - 73*b - 45*c^2 + 125*c - 69)/4) * h3

private lemma rejectI_3_7 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, b, 1) = 0) (h2 : locus b (1, c, b) = 0)
    (h3 : edge b b c (1, b, 1) (1, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (c^2*z*(4*b - c)*(c - 3)) * h1
    + (z*(b*(b*(b*(1 - c) + c^2 - 1) + c*(12 - 4*c)) + c*(c - 3))) * h2

private lemma rejectI_3_10 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, b, 1) = 0) (h2 : locus b (b, 1, b) = 0)
    (h3 : edge b b c (1, b, 1) (b, 1, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((5*b^2 - 9*b - 13)/6) * h1 + (-(5*b - 19)/6) * h2

private lemma rejectI_3_11 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, b, 1) = 0) (h2 : locus b (b, 1, c) = 0)
    (h3 : edge b b c (1, b, 1) (b, 1, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((851392543110912*b*c*z + 214484812474944*b*c - 1303748682122088*b*z + 422738309272314*b - 743103431316*c^2*z - 187204364667*c^2 - 3167122170548556*c*z - 820411429172469*c + 4831117383232944*z - 1399508996973212)/2601785587623728) * h0
    + (b*(143982106399838076 - 64231142702723820*b)/5203571175247456 + c*(b*(107089787421383430*b - 241406180635061628) + c*(b*(145413112022753400 - 66774388591496448*b) + c*(b*(18365408384415768*b - 37822086168003720) + c*(b*(4341806171499816 - 2170903085749908*b) + c*(b*(90939116597682*b - 181878233195364) - 90939116597682*c + 2261842202347590) - 20172555003774948) + 81912531628773504) - 172091936531304078) + 182093621155966236)/5203571175247456 + z*(b*(452023738240592352 - 201109499640549224*b) + c*(b*(333854458284845877*b - 749095427440149716) + c*(b*(441883436249931970 - 205002142550872082*b) + c*(b*(53951082036954024*b - 110555951060912142) + c*(b*(11042138953288022 - 5086430149110550*b) + c*(b*(128453807803251*b - 685877240556390) - 128079399073917*c + 6854209180341403) - 60572091894485346) + 245776576598029182) - 525418342908036473) + 565213703035832927) + z*(b*(5716351594187712 - 2578595019349536*b) + c*(b*(-2073819626711604*b - 7496873805337776) + c*(b*(13728146123532456*b - 1448862955832520) + c*(b*(5248696156081272 - 13941083973181536*b) + c*(b*(5066641041638904*b - 719102994734232) + c*(b*(-424953168124140*b - 852878749973544) + 426439374986772*c + 836705303883540) - 10880159443643160) + 24201046955095272) - 23371899444687708) + 11590126895910276) - 2914091952642720) - 236452158670649600)/5203571175247456 - 37824480417770559/2601785587623728) * h1
    + (b*(b*(b*(b*(b*(b*(c*(5652216232225344*z + 2182538798344368) + z*(-670993866586368*z - 53968345891513152) - 17181053284487904) + c*(c*(-9420360387042240*z - 3637564663907280) + z*(1118323110977280*z + 86179098997705024) + 27180062941916928) + z*(447329244390912*z + 35978897261008768) + 11454035522991936) + c*(c*(c*(3768144154816896*z + 1455025865562912) + z*(-447329244390912*z - 14312068370811616) - 3087636796005192) + z*(-2572143155247744*z - 249270280992490496) - 82229745244786392) + z*(5032453999397760*z + 404762594186348640) + 128857899633659280) + c*(c*(c*(z*(851392543110912*z - 9676893593919408) - 3819442897102644) + z*(105015255232691850 - 980901958706856*z) + 34068164378151840) + z*(73593260047080*z - 64038354325638026) - 17857730198575524) + z*(-4193711666164800*z - 337302161821957200) - 107381583028049400) + c*(c*(c*(c*(z*(-426439374986772*z - 3640064755742979) - 1364086748965230) + z*(59609722497425481 - 4649311188772452*z) + 21378034944733734) + z*(11618264401427412*z - 348740036346786101) - 116404777620446370) + z*(642712150360836*z + 889522136634141415) + 287646404340550398) + z*(-9421872209983584*z - 757805523559997176) - 241250623203017652) + c*(c*(c*(c*(z*(1705757499947088*z + 7023970713338124) + 2546295264735096) + z*(6716556476620056*z - 105170022229757206) - 37686750785186196) + z*(550334955901445098 - 22127594438727144*z) + 182530956683164584) + z*(4797406758952512*z - 1181712654165728528) - 380906103494807700) + z*(11256352236259776*z + 902209554417126224) + 287325800348025984)/5203571175247456 + c*(c*(c*(c*(c*(942036038704224*z + 363756466390728) + z*(-538271686084500*z - 18287005303220515) - 6410134428057582) + z*(120088598279793087 - 571260942879804*z) + 40741627027566006) + z*(3565970578104372*z - 371372931350515325) - 121945623980430978) + z*(1395324919629756*z + 556633502150511561) + 178917566236250694)/5203571175247456 + z*(-4243175957611872*z - 329547962739024800)/5203571175247456 - 52605527175514413/2601785587623728) * h2
    + ((-8089201404*c*z - 3123552813*c + 960296688*z^2 + 77237105132*z + 24588762114)/44682722876) * h3

private lemma rejectI_3_17 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, b, 1) = 0) (h2 : locus b (b, c, c) = 0)
    (h3 : edge b b c (1, b, 1) (b, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(46*c - 11)*(b - c + 2)/3) * h0
    + (b*(b*(c*(c*(c*(c*(c*(46*z - 2) - 241*z + 31) + 193*z - 166) + 13*z + 372) - 11*z - 394) + 391) + c*(c*(c*(c*(c*(c*(2 - 46*z) + 333*z - 33) - 767*z + 199) + 763*z - 551) - 327*z + 739) + 44*z - 542) - 212)/6 + c*(92*c - 210)/6 + 12) * h1
    + (b*(b*(b*(b*(b*(b*(132 - 24*c) + c*(60*c - 334) + 22) + c*(c*(300 - 56*c) + 180) - 748) + c*(c*(c*(24*c - 46*z - 122) + 57*z - 239) - 11*z + 1010) + 11) + c*(c*(c*(c*(-4*c + 46*z + 16) + 35*z + 115) - 103*z - 403) + 22*z - 464) + 1100) + c*(c*(c*(c*(8 - 184*z) + 642*z - 130) - 557*z + 625) + 99*z - 822) - 157)/6 + c*(c*(c*(c*(46*z - 2) - 241*z + 29) + 239*z - 139) - 44*z + 232)/6 + 151/3) * h2
    + ((2*c - 11)/3) * h3

private lemma rejectI_3_20 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, b, 1) = 0) (h2 : locus b (c, 1, c) = 0)
    (h3 : edge b b c (1, b, 1) (c, 1, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (b*(b*(b*(b*(b*(914 - 92*b) - 3204) + 4370) + 408) - 9086)/66 + c*(14703*b + c*(-21572*b + c*(13849*b + c*(-4050*b + c*(351*b + c*(35*b - 70) - 1906) + 17657) - 55712) + 82501) - 57109)/66 + 7192/33) * h1
    + (b*(b*(b*(b*(b*(118*b - 1792) + 9376) - 19172) + 3840) + 29118)/66 + c*(b*(b*(b*(b*(b*(210*b - 2054) + 4968) + 4923) - 19671) - 5169) + c*(b*(b*(b*(b*(140*b - 853) - 1446) + 14049) - 20957) + c*(b*(b*(b*(35*b + 104) - 3373) + 12287) + c*(b*(b*(280 - 35*b) - 1696) + c*(-70*b - 35*c - 71) + 3050) - 13203) + 19947) - 7111)/66 - 2839/33) * h2
    + (-(105*b*c - 46*b - 35*c^2 - 421*c + 135)/66) * h3

private lemma rejectI_4_9 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, b, b) = 0) (h2 : locus b (b, 1, 1) = 0)
    (h3 : edge b b c (1, b, b) (b, 1, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-c*z*(c - 1)*(b^2 - b*c - 2*b + 4)) * h1 + (-c*z*(c - 3)*(c - 1)) * h2

private lemma rejectI_4_12 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, b, b) = 0) (h2 : locus b (b, b, 1) = 0)
    (h3 : edge b b c (1, b, b) (b, b, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((3*b^2 - 5*b - 9)/4) * h1 + (-(3*b^2 - 8*b - 4)/4) * h2

private lemma rejectI_4_15 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, b, b) = 0) (h2 : locus b (b, c, 1) = 0)
    (h3 : edge b b c (1, b, b) (b, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((b - 3)*(b + 3)/9) * h0
    + (b*(b*(b*(b*(b*(b*(240*c - 1040) + c*(776 - 276*c) + 1820) + c*(c*(102*c + 216*z - 295) - 216*z - 31) - 2626) + c*(c*(c*(-12*c - 216*z + 322) - 216*z - 2151) + 432*z + 5103) - 3692) + c*(c*(c*(-141*c + 432*z + 866) - 2808*z - 835) + 2376*z - 3351) + 9937) + c*(c*(c*(c*(12*c - 133) + 2376*z + 732) + 216*z - 2245) - 2592*z + 2766) - 1156)/1944 + c*(c*(c*(c*(63*c - 732) - 2592*z + 3450) + 2592*z - 8209) + 8681)/1944 - 3325/1944) * h1
    + (b*(-9473*b - 26)/1944 + c*(b*(5939*b + 32) + c*(b*(20 - 1516*b) + c*(b*(199*b - 32) + c*(b*(6 - 12*b) + 3*c - 25) + 70) - 90) + 55)/1944 - 13/1944) * h2
    + (-(3*c - 13)/1944) * h3

private lemma rejectI_4_18 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, b, b) = 0) (h2 : locus b (c, 1, 1) = 0)
    (h3 : edge b b c (1, b, b) (c, 1, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-c*z*(b^2*c - b^2 - b*c^2 - b*c + 2*b + 2*c^2 - 6*c + 8)) * h1 + (-2*b*z*(c - 3)) * h2

private lemma rejectI_4_21 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, b, b) = 0) (h2 : locus b (c, b, 1) = 0)
    (h3 : edge b b c (1, b, b) (c, b, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (b*(654 - 91*b)/144 + c*(b*(b*(b*(1547 - 182*b) - 3603) + 1187) + c*(b*(b*(b*(463 - 108*b) + 752) - 3973) + c*(b*(b*(b*(74*b - 899) + 2389) + 658) + c*(b*(b*(185*b - 1397) + 1897) + c*(148*b*c + b*(222*b - 1030)) + 100) - 298) + 211) - 55)/144 - 151/48) * h1
    + (b*(b*(c*(c*(c*(c*(37*c - 17) - 145) + 290) - 371) - 199) + c*(c*(74*c - 696) + 1268) + 470)/144 + 37*c/144 + 53/144) * h2
    + (-(37*c - 91)/144) * h3

private lemma rejectI_5_16 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, b, c) = 0) (h2 : locus b (b, c, b) = 0)
    (h3 : edge b b c (1, b, c) (b, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (c*(1254834*b + c*(b*(596241*z + 6613075) + c*(-2268973*b + 2268973*c - 596241*z - 4344102) - 596241*z - 7867909))/93528 - 1) * h0
    + (b*(b*(c*(c*(c*(c*(c*(c*(3203256 - 183786813*z) + z*(48295521*z + 351030510) + 49248934) + z*(48295521*z + 1024164405) - 126315448) + z*(-96591042*z - 446106852) - 68684049) + 480956049*z + 108736824) - 409407129*z - 8649081) + 11363652*z - 608423508) + c*(c*(c*(c*(c*(c*(-533876*c + 1286647983*z - 46469269) + z*(-338068647*z - 5213068794) - 68884655) + z*(386364168*z + 3292009533) + 538628720) + z*(-48295521*z - 1590584769) - 186536049) - 974643597*z - 78985956) + 536301243*z - 219025044) + 36931869*z + 1211843619)/7575768 + c*(c*(c*(c*(c*(c*(c*(10677520 - 183786813*z) + z*(48295521*z + 716640048) + 19660676) + z*(-48295521*z - 331744653) - 96018468) + 442971990*z - 84941346) + 357323724*z + 183055068) - 11363652*z - 180100557) + 144886563*z + 2095688700)/7575768 - 51*z/8 - 7867909/93528) * h1
    + (b^2*(b*(b*(34722270*z + 4193406) - 17361135*z - 2096703) - 17361135*z - 2096703)/7575768 + c*(b*(b*(b*(b*(74389833*z - 391713) - 271570239*z - 28109634) + 100589364*z + 15921129) - 190341171*z + 589553181) + c*(b*(b*(b*(b*(32898474*z - 13137761) - 251298045*z + 53767882) + 185150367*z - 40153883) + 1311975711*z + 121187598) + c*(b*(b*(b*(b*(-841752*z - 2537038) + z*(-48295521*z - 389720322) + 22448552) + z*(193182084*z + 1551761469) - 20852720) + 231551946*z - 46976741) + c*(b*(b*(b*(3203256*b + z*(48295521*z + 718463844) - 25471649) + z*(-96591042*z - 2084629365) + 113636376) + z*(-386364168*z - 3148977546) - 286873664) + c*(b*(b*(b*(3737132 - 183786813*z) + z*(-96591042*z - 701640144) - 21685895) + z*(386364168*z + 5752656045) + 38370003) + c*(b*(b*(367573626*z - 8008140) - 1470434796*z + 31520741) + c*(533876*b + 183786813*z - 10677520) + z*(-48295521*z - 716640048) + 14507388) + z*(48295521*z + 322765965) - 5074076) - 72601110*z + 129671010) - 357323724*z - 183055068) + 11363652*z + 363887370) - 193182084*z - 2447560962)/7575768) * h2
    + ((-533876*c^2 + 140292*c*z + 1579571*c - 5787045*z - 698901)/7575768) * h3

private lemma rejectI_5_19 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, b, c) = 0) (h2 : locus b (c, 1, b) = 0)
    (h3 : edge b b c (1, b, c) (c, 1, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (b*(b*(c*(-100555*c + 803439*z + 431145) - 803439*z - 507170) + c*(c*(200005*c - 1598049*z - 656260) - 88290*z + 145010) + 1606878*z + 1014340)/2224908 + c*(c*(c*(-99450*c + 794610*z + 226220) + 882900*z + 256685) - 715149*z - 46415)/2224908 - 13*z/36 - 1366039/1112454) * h0
    + (b*(b*(b*(b*(b*(b*(c*(-1105*c + 8829*z + 3815) - 79461*z - 2120) + c*(c*(c*(1105 - 100555*z) + z*(803439*z + 522871) + 16075) + z*(-1606878*z - 929486) - 69455) + z*(803439*z + 1840349) + 68360) + c*(c*(c*(c*(300560*z + 8840) + z*(-2401488*z - 1358042) - 81350) + z*(2313198*z + 2249707) + 125045) + z*(2498607*z - 1727872) + 182015) + z*(-2410317*z - 8982015) - 489480) + c*(c*(c*(c*(c*(-299455*z - 2210) + z*(2392659*z + 999588) - 53145) + z*(176580*z + 412133) + 563605) + z*(-4802976*z - 9469521) - 1518535) + z*(20653130 - 176580*z) + 1069975) + z*(2410317*z + 18305439) + 1030200) + c*(c*(c*(c*(c*(c*(99450*z - 17680) + z*(-794610*z - 185511) + 188115) + z*(-79461*z - 1809481) - 717955) + z*(7424633 - 2507436*z) + 811235) + z*(7310412*z + 421935) + 948300) + z*(-3125466*z - 34323515) - 2049225) + z*(-803439*z - 14253923) - 813320) + c*(c*(c*(c*(c*(c*(-8840*c + 270637*z + 90190) + z*(-1598049*z - 2871504) - 400875) + z*(8723052*z + 10483323) + 1038130) + z*(-11795544*z - 17391540) - 1417995) + z*(88290*z + 13538939) + 524085) + z*(4820634*z + 18326019) + 778265) + 1986525*z + 52530)/2224908 + c*(c*(c*(c*(c*(-1105*c + 8829*z - 10550) + 235321*z + 76205) + z*(-1598049*z - 2509872) - 231030) + z*(3928905*z + 3995903) + 313685) + z*(-2410317*z - 6245025) - 293595)/2224908 + 25*z/28 + 121105/556227) * h1
    + (b*(b*(b*(b*(b*(b*(-88290*z - 7040) + 971190*z + 77440) - 3355020*z - 267520) + 3884760*z + 309760) - 2030670*z - 161920) + c*(c*(c*(c*(c*(c*(-99450*z - 30940) + z*(794610*z + 1473457) + 237210) + z*(-7107345*z - 8403000) - 785780) + z*(15715620*z + 18844208) + 1362600) + z*(-9641268*z - 21042366) - 1315155) + 8890803*z + 823230) + 706320*z + 56320)/2224908 + c*(c*(c*(c*(c*(c*(8840*c - 270637*z - 70300) + z*(1598049*z + 2112567) + 240490) + z*(-3928905*z - 5143673) - 436910) + z*(2410317*z + 5406270) + 446185) - 2375001*z - 304920) - 1236060*z - 83735)/2224908 - 101*z/252 - 257105/1112454) * h2
    + (-(-1105*c^2 + 8829*c*z + 4920*c - 88290*z - 7040)/2224908) * h3

private lemma rejectI_5_22 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, b, c) = 0) (h2 : locus b (c, b, b) = 0)
    (h3 : edge b b c (1, b, c) (c, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (c*(b*(147243794 - 32405345*b) + c*(-9876015*b + c*(9625092 - 1877085*b) - 40132448))/4824 - 1) * h0
    + (b*(b*(c*(c*(c*(c*(c*(c*(1877085*z - 370670) + 34773020*z + 4955096) - 242173119*z - 27361005) + 426310415*z + 76218359) - 105950560*z - 108656006) - 114841665*z + 63428513) + 4824*z - 20424867) + c*(c*(c*(c*(c*(c*(-370670*c - 42030437*z + 5014073) + 267433631*z - 29255072) - 664959936*z + 98867884) + 810587216*z - 205580178) - 485881787*z + 248694148) + 114856137*z - 106503617) - 4824*z + 22277832)/4824 + c*(c^3*(658502*c - 2572679) + 9625092)/4824 - 5016556/603) * h1
    + (b^2*(b*(b*(4360170*b - 17616159) + 5537952) + 7718037)/4824 + c*(b*(b*(b*(b*(-2565400*b - 17962035) + 99249081) + 4824*z - 31886987) - 19296*z + 70266435) + c*(b*(b*(b*(b*(370670*b + 32405345*z + 19532931) - 244459829*z - 32497007) + 344510523*z - 53647234) + 459371484*z - 315555376) + c*(b*(b*(b*(b*(-32405345*z - 4974755) + 254335844*z - 15620079) - 204389564*z + 20671045) - 1139592077*z + 315067845) + c*(b*(b*(b*(370670*b - 7998930*z + 7335161) - 187787475*z + 8005992) + 846735475*z - 114616793) + c*(b*(b*(b*(-1877085*z - 741340) + 47661692*z - 3823427) - 164618501*z + 16877137) + c*(b*(370670*b - 1877085*z - 741340) + 370670*c + 42030437*z - 4272733) - 183372757*z + 24104613) + 256183985*z - 70972834) - 114846489*z + 77461580) + 4824*z - 20225475) - 13285998)/4824) * h2
    + ((185335*b*c - 726695*b - 658502*c + 2572679)/4824) * h3

private lemma rejectI_5_25 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, b, c) = 0) (h2 : locus b (c, c, b) = 0)
    (h3 : edge b b c (1, b, c) (c, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-b*z*(b^2*c - b^2 - b*c^2 + b + c^3 - 3*c^2)) * h1 + (b*c^2*z*(c - 3)) * h2

private lemma rejectI_5_26 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, b, c) = 0) (h2 : locus b (c, c, c) = 0)
    (h3 : edge b b c (1, b, c) (c, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(5170329025*b^2 + 10789872225*b*c - 5490351581*b + 2413768106*c^2 + 9863307350)/9863307350) * h0
    + (b*(b*(b*(b*(b*(c*(390030450*c - 64470481025*z + 1010974450) - 24479746975*z + 310472000) + c*(c*(390030450*c - 64919695200*z - 1524223475) + 342431059806*z - 5755374700) + 137589699394*z - 1357344775) + c*(c*(c*(8376104119*z - 1950152250) + 293424176525*z - 764537300) - 406104167575*z + 8131455725) - 221846949069*z + 1898730325) + c*(c*(c*(c*(2413768106*z + 585045675) - 94120557025*z + 3271598700) - 327670056656*z + 5870831475) - 252711595075*z + 1118669425) + 79086920650*z - 736400775) + c*(c*(c*(c*(-9655072424*z - 1755137025) + 155928102302*z - 2989263225) + 358876041679*z - 1090532900) + 280577942443*z - 728638975) - 88950228000*z + 6296760250)/9863307350 + c^4*(195015225*c - 29650076000*z + 310472000)/9863307350 - 1206884053/4931653675) * h1
    + (b*(b*(b*(b*(b*(310472000 - 29650076000*z) + 207550532000*z - 2173304000) - 385450988000*z + 4036136000) + 88950228000*z - 931416000) - 5170329025)/9863307350 + c*(b*(1429141425 - 355800912000*z) + c*(b*(469588900 - 271181648278*z) + c*(138891106079*b*z + c*(-1134799801*b*z - 2413768106*c*z - 28334087451*z) + 75222969557*z - 195015225) + 88950228000*z - 230913550) + 1516461675)/9863307350 + 422334737/758715950) * h2
    + ((-201*c + 30560*z - 320)/10166) * h3

private lemma rejectI_6_7 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, c, 1) = 0) (h2 : locus b (1, c, b) = 0)
    (h3 : edge b b c (1, c, 1) (1, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (-z*(b*(b*(b*(b*(b*(6*b - 36) + 45) + 33) - 24) + 3) + c*(142*b + c*(-54*b + c*(2*b + 11) - 34) - 1))/3) * h1
    + (-z*(b*(b*(b*(b*(b*(6*b - 2*c - 32) + 53) + c*(2*c + 8) - 6) + c*(5*c - 29) - 11) + c*(c*(25 - 2*c) - 40) - 42) + c*(c*(56 - 11*c) - 78) + 32)/3) * h2
    + (z*(3*b - c)/3) * h3

private lemma rejectI_6_10 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, c, 1) = 0) (h2 : locus b (b, 1, b) = 0)
    (h3 : edge b b c (1, c, 1) (b, 1, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (b*(29518486573513718*b - 66040333051871900)/216446596502295000 + c*(b*(2233647427131424570*b - 3058702239229548982) + c*(b*(4496627026175110561 - 991148448739675172*b) + c*(b*(-3085335399876391092*b - 171650486477371549) + c*(b*(2243522543236344590*b - 444272964578650155) + c*(b*(163518431552269901 - 496594768973895118*b) + c*(b*(24244706767312457*b - 22697111103312797) + 24244706767312457*c - 367702669721250691) + 2550929689591423977) - 9651114594943107330) + 20170667843559669478) - 23029520420599342093) + 12585966317819963174)/216446596502295000 - 1404071989259165951/108223298251147500) * h1
    + (b*(b*(b*(b*(b*(169114580325815128 - 49493712974899284*b) + 929372044864245006) - 3708423262776439006) - 197251053508134060) + 8984471292375837772)/216446596502295000 + c*(b*(b*(b*(b*(b*(479984377509982954 - 31817386912435254*b) - 3061881195706016462) + 8212724924350075218) - 113328271786616224) - 38023584465889134168) + c*(b*(b*(b*(b*(b*(17676326062464030*b + 272023738510858148) - 1586701322859335282) - 4355323536549709934) + 17313269229893474299) + 35520473836775008905) + c*(b*(b*(b*(b*(1510329511391270949 - 173186136748036306*b) - 181405543597015587) - 14709182175828741969) - 4212683168777758920) + c*(b*(b*(b*(98255759403429827 - 133534886244643407*b) + 5248224626870970407) - 8206597530161278600) + c*(b*(b*(-46941817870625254*b - 630955064220154257) + 3245987408886649334) + c*(b*(24244706767312457*b - 371339166925768997) + 50037009198624574*c - 1243593407325012352) + 9632331766771228777) - 34275624164275099145) + 65133244941664616922) - 66847360956719498297) + 33573331844690298526)/216446596502295000 - 2819719845655757941/108223298251147500) * h2
    + (-(8838163031232015*b^2*c - 24746856487449642*b^2 - 95431231405250168*b*c^2 + 309218935335520974*b*c - 138164418224139214*b + 24244706767312457*c^3 - 125255602048126121*c^2 + 402867114383601518*c - 135375472911439731)/216446596502295000) * h3

private lemma rejectI_6_11 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, c, 1) = 0) (h2 : locus b (b, 1, c) = 0)
    (h3 : edge b b c (1, c, 1) (b, 1, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((c - 4)*(5*b*c + 2*c^2 + 4*c + 18)/72) * h0
    + (b*(b*(c*(c*(c*(c*(c*(-324*c*z + 1188*z + 1) + 5508*z - 61) - 10692*z + 20) + 9504*z + 404) - 36288*z - 517) + 31104*z - 39) + c*(c*(c*(c*(c*(648*c*z - 3672*z + 14) + 10584*z + 410) - 28296*z - 1784) - 20736*z + 2600) + 57024*z - 1894) - 15552*z + 3102)/31104 + c*(c*(c*(c*(c*(c*(324*c*z - 2376*z - 1) + 3024*z - 98) - 648*z + 223) + 18252*z + 16) - 52272*z - 487) + 49248*z + 1250)/31104 - z/2 + 419/10368) * h1
    + (b*(b*(b*(b*(b*(72 - 16*b) - 4) - 382) + 447) - 15552*z + 436)/31104 + c*(b*(b*(b*(b*(48 - 24*b) + 470) + 15552*z - 1226) - 36288*z - 521) + c*(b*(b*(b*(28*b + 4320*z - 302) - 31104*z + 826) + 38016*z + 428) + c*(b*(b*(b*(38 - 5400*z) + 18036*z - 202) + 26352*z - 440) + c*(b*(b*(1080*b*z - 2376*z - 13) - 14796*z + 256) + c*(b*(-108*b*z + 2592*z - 15) + c*(-324*b*z - 324*c*z + 2376*z + 1) - 3024*z + 98) + 648*z - 1247) - 18252*z + 4080) + 52272*z - 5657) - 49248*z + 3710)/31104 + z/2 - 2281/31104) * h2
    + (1/1944) * h3

private lemma rejectI_6_17 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, c, 1) = 0) (h2 : locus b (b, c, c) = 0)
    (h3 : edge b b c (1, c, 1) (b, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (b*c*z*(c - 1)*(2*b*c - 8*b - c^2 + 2*c + 7)/2) * h1 + (-c*z*(c - 1)*(b^2 + b*c - 8*b - c^2 + 2*c + 7)/2) * h2

private lemma rejectI_6_20 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, c, 1) = 0) (h2 : locus b (c, 1, c) = 0)
    (h3 : edge b b c (1, c, 1) (c, 1, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (z*(b*(b*(b*(81 - 9*b) - 242) + 218) + c*(119*b + c*(-523*b + c*(517*b + c*(-164*b - 48*c + 708) - 1891) + 1860) - 639) + 10)/16) * h1
    + (-z*(b*(b*(b*(b*(b*(3*b + c - 37) + c*(12*c - 24) + 147) + c*(c*(4*c - 93) + 139) - 161) + c*(c*(20*c - 39) + 157) - 380) + c*(c*(c*(60*c - 531) + 1623) - 2015) + 1030) + c*(c*(c*(c*(16*c - 188) + 1053) - 2236) + 1985) - 630)/16) * h2
    + (z*(3*b + c - 10)/16) * h3

private lemma rejectI_7_10 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, c, b) = 0) (h2 : locus b (b, 1, b) = 0)
    (h3 : edge b b c (1, c, b) (b, 1, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(1391093*b*c - 583253*c^2 - 996107*c + 2387200)/2387200) * h0
    + (b*(b*(c*(c*(c*(323866587*c + 61950000*z - 462980819) - 591390125*z - 1528103065) + 220715125*z + 1807092478) + 319050000*z - 709094970) + c*(c*(c*(-581044116*c + 448396375*z + 1094870109) - 422245250*z + 4092954130) - 612626125*z - 3968087434) + 638100000*z - 256815670)/298400000 + c*(c*(c*(c*(107955529*c + 20650000*z - 364956703) - 342619875*z - 61482007) + 520726125*z + 220635420) + 89318750*z - 372994587)/298400000 - 5555*z/5968 + 5119593/2984000) * h1
    + (b*(b*(b*(b*(b*(b*(-514355058*b - 1584331645*c + 41300000*z + 3908860819) + c*(-1044554000*c + 144550000*z + 10605937051) - 268450000*z - 10619887406) + c*(c*(241333645*c + 144550000*z + 4198607891) - 805350000*z - 22515424710) + 557550000*z + 12006982710) + c*(c*(c*(215911058*c - 132586625*z - 3676400457) - 342363375*z - 1023902151) + 1156400000*z + 12714350738) - 351050000*z - 3264134833) + c*(c*(c*(c*(246793250*z - 638154471) + 523280000*z + 10697872341) - 944573250*z - 11547566218) + 401650000*z + 6424054819) - 123900000*z - 2725368942) + c*(c*(c*(c*(c*(215911058 - 72906625*z) - 750686500*z - 1387225283) + 658393125*z - 7152826492) + 1720175000*z + 10908622724) - 1668550000*z - 3537100102) + 82600000*z + 873928355)/298400000 + c*(c*(c*(c*(c*(218719875*z - 15843884) - 210976125*z + 1861901065) - 502318750*z - 3663201898) + 587500000*z + 3154861216) - 123900000*z - 1464189922)/298400000 + 413*z/5968 + 282776471/298400000) * h2
    + (-(-257177529*b + 107955529*c + 20650000*z + 282776471)/298400000) * h3

private lemma rejectI_7_11 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, c, b) = 0) (h2 : locus b (b, 1, c) = 0)
    (h3 : edge b b c (1, c, b) (b, 1, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (c*(-6995431630608088*b + c*(8967393548330938*b - 50278482092963866*c + 198049166375551855) - 110811698607234953)/22354737632615556 - 1) * h0
    + (b*(b*(c*(c*(c*(c*(c*(-108340376504192*c + 239014541924150805*z + 29701119635640192) - 5785227864820597068*z + 777146655472913344) + 24204660917475773142*z - 4254284652190203120) - 31181935813082872344*z + 5593738735448497216) + 16131343150600770357*z - 3540643360762095408) - 2915300828317085820*z - 332812318763198640) + c*(c*(c*(c*(c*(c*(54170188252096*c + 86569262972517384*z - 13740070958652128) + 2494813185766999206*z - 721828344151883712) - 9277790574565711818*z + 2881217799164514368) - 2544836200012954134*z - 421553541463549952) + 15412265502046034490*z - 2594963619864028464) - 9114376117272476184*z + 2660022408654739144) + 1558246733505312912*z + 1209975921889936332)/402385277387080008 + c*(c*(c*(c*(c*(c*(-595872070773056*c - 911908621730202003*z + 178794661647868416) + 121996352221788447*z - 395445957831001024) + 15585200225944836210*z - 1790746572158389072) - 32107451527093462398*z + 4928065256634229936) + 25831269111993636357*z - 4187025569543421872) - 9529882584258299985*z + 2026876007098796318)/402385277387080008 + 4188438564233867*z/1241929868478642 - 28386803616613241/67064212897846668) * h1
    + (b*(b*(b*(b*(b*(b*(c*(-650042259025152*c - 1038831155670208608*z + 195757858807520256) + 3116493467010625824*z - 649071477020841792) + c*(c*(-1516765271058688*c - 2423939363230486752*z + 459801867759664640) + 12119696816152433760*z - 2428036787483725376) - 14543636179382920512*z + 3029000226097261696) + c*(c*(c*(-541701882520960*c - 865692629725173840*z + 171257077244081280) + 15582467335053129120*z - 2993499832189589344) - 47959371686774630736*z + 9809961572425697952) + 27009610047425423808*z - 5625286134180628864) + c*(c*(c*(c*(650042259025152*c + 1119537697605187050*z - 193699391653940608) + 29473099334583534*z + 17687510887583296) - 28158620844365194392*z + 5518440485688537120) + 62503007866157551248*z - 12869860748822100160) - 22334869846909485072*z + 4651678918649366176) + c*(c*(c*(c*(c*(216680753008384*c - 146582557914094479*z - 71157170121985216) - 8450572166925160905*z + 1996712020893592192) + 29549090539840158963*z - 6562838487840940080) - 7302046378091662143*z + 1695206561495138672) - 8802010710448267932*z + 1861362511260591616) + 2077662311340417216*z - 432714318013894528) + c*(c*(c*(c*(c*(c*(-54170188252096*c - 86569262972517384*z + 16448580371256928) + 1995063046728826878*z - 83970426617569216) + 8302038509641924170*z - 3160102603378536224) - 60401277887240772108*z + 14596888768089411136) + 66404844957724792812*z - 14179641001878812400) - 27641242076254549056*z + 6052702771972255192) + 4155324622680834432*z - 865428636027789056)/402385277387080008 + c*(c*(c*(c*(c*(c*(595872070773056*c + 911908621730202003*z - 184536701602590592) - 9379044769243609593*z + 2134661862124067712) + 31229995576731093513*z - 6969075262414851632) - 37334549721349111671*z + 7617058433620417392) + 20631538700207642628*z - 4799351372425355072) - 5367294304296077808*z - 880198470094239458)/402385277387080008 + 2404701749236594*z/1862894802717963 - 13522322437934204/50298159673385001) * h2
    + (2*(6771273531512*c^2 + 10821157871564673*c*z - 2039144362578336*c - 32463473614694019*z + 6761161218967102)/50298159673385001) * h3

private lemma rejectI_7_17 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, c, b) = 0) (h2 : locus b (b, c, c) = 0)
    (h3 : edge b b c (1, c, b) (b, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (c*(b*(651413042907210*b - 3788629520914765) + c*(20917593137113*b + c*(7833259232400*b + 21298991002686) + 943583839393431))/14714106028125 - 1) * h0
    + (b*(b*(c*(c*(c*(c*(c*(c*(-23499777697200*z - 246188147304) - 656935123165842*z + 5747698707204) + 8264211859023732*z - 49605172456742) - 35573986316710420*z + 162453820111006) + 38806547628998592*z - 128050784139946) - 14596577020065754*z + 90215632507702) + 2657807993631004*z + 65861029992020) + c*(c*(c*(c*(c*(c*(c*(-3916629616200*z - 123094073652) + 118050530857370*z + 2763931981143) + 488075888002900*z - 14946237541526) - 750230052515886*z + 6787554418349) + 8399915723254556*z + 60619707614090) - 10860066800745542*z - 75551766523033) + 6618232556024056*z + 133758758343660) - 1386446376809366*z + 301207071499717)/58856424112500 + c*(c^3*(c*(1093769209092 - 636369046675096*z) + 75153668682152*z - 4015405195772) + 85195964010744)/58856424112500 + 314527946464477/4904702009375) * h1
    + (b*(b*(b*(b*(b*(b*(b*(c*(-93999110788800*z - 2954257767648) + 2366519069669472*z + 28266875458632) + c*(c*(-15666518464800*z - 492376294608) - 3188796658133664*z + 18659405583444) - 5465375662080768*z - 94759619821212) + c*(c*(c*(15666518464800*z + 492376294608) - 780124596183208*z + 4260644013048) + 3325638368154800*z - 95307901593896) - 1521724875177192*z + 55519932026808) + c*(c*(c*(c*(23499777697200*z + 738564441912) + 1143900625029748*z - 14561379903654) + 13782551051173220*z + 43082419878560) + 2914568060835728*z + 99538203057758) + 6629983695381352*z + 84104885661896) + c*(c*(c*(c*(c*(31333036929600*z + 492376294608) + 406137430531958*z - 12014127111402) - 16405934391160424*z + 83036870629872) + 347712294061814*z - 139025802317912) + 1775280962745572*z + 123259233371714) + 94352832761848*z - 82395326057440) + c*(c*(c*(c*(c*(c*(3916629616200*z + 123094073652) - 180716604716570*z - 3748684570359) - 1001679931256384*z + 37374268806854) + 32141367025945528*z - 124733392188242) - 53434130731840852*z + 63407209186664) + 3897330528837414*z - 127276822932765) - 225461006046456*z + 12046215587316) + c*(c*(c*(c*(c*(15666518464800*c*z + 947868999507382*z + 518729696994) - 4430469615143876*z + 4578079463104) + 5723615949272662*z - 94826331847192) + 14885249929748264*z + 151073046000486) - 5545785507237464*z - 78208206674344))/58856424112500 + c*(c*(c*(c*(c*(c*(c*(3916629616200*z + 123094073652) - 110217271624970*z - 2517743833839) - 728093579333840*z + 9295279505588) + 1707787150443376*z + 15750586709162) - 3845339802405324*z - 27461367323130) + 1386446376809366*z + 8893850363383) - 57176653364164)/58856424112500) * h2
    + ((3916629616200*b*c*z + 123094073652*b*c - 98604961236228*b*z - 1177786477443*b + 159092261668774*c*z - 273442302273*c - 18788417170538*z + 1003851298943)/14714106028125) * h3

private lemma rejectI_7_20 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, c, b) = 0) (h2 : locus b (c, 1, c) = 0)
    (h3 : edge b b c (1, c, b) (c, 1, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(147219014*b*c - 71983311*b + 79147842*c^2 - 582430483*c + 289586939)/440062) * h0
    + (b*(b*(b*(b*(b*(c*(885972*c + 5684256*z - 3738334) - 947376*z + 573835) + c*(c*(1771944*c - 135850502*z - 13973796) + 173728277*z + 29906672) - 64404303*z - 4590680) + c*(c*(c*(68071172*z - 7383100) + 542226214*z + 43457950) - 924498836*z - 61665698) + 349254362*z + 7312193) + c*(c*(c*(c*(79147842*z + 7678424) - 533166931*z - 36927196) + 164965049*z + 32269264) + 611799139*z - 20889787) - 306639707*z + 11067340) + c*(c*(c*(c*(c*(79147842*z + 590648) - 475728645*z - 20310104) + 758217864*z + 113420498) - 493744218*z - 152481483) + 78580413*z + 90708328) + 22737024*z - 86198337)/440062 + c*(c*(c*(c*(c*(11076670*z + 6201804) + 23363067*z - 47136342) - 118075389*z + 99411614) + 147334049*z - 97642594) - 79803789*z + 46335897)/440062 + 11664*z/301 + 103269606/220031) * h1
    + (b*(b*(b*(b*(b*(573835 - 947376*z) + 8526384*z - 5164515) - 21789648*z + 13198205) + 9473760*z - 5738350) + c*(c*(c*(c*(c*(-79147842*z - 590648) + 328509631*z + 1704692) - 216727873*z - 7450352) - 19844340*z + 531437) + 4736880*z - 4907934) + 7579008*z + 67392631)/440062 + c*(c*(c*(c*(c*(3248564 - 11076670*z) + 15115657*z - 11443074) - 22512819*z + 20068874) + 19894896*z - 12122904) - 9473760*z + 10022741)/440062 + 648*z/301 - 144860356/220031) * h2
    + (-(202*c + 1296*z - 785)/602) * h3

private lemma rejectI_8_13 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, c, c) = 0) (h2 : locus b (b, b, b) = 0)
    (h3 : edge b b c (1, c, c) (b, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (b*(b*(630*c + 10141) + c*(11016*c - 44379) + 245)/14 - 1) * h0
    + (-35*b/2 + c*(b*(87348*z - 35) + c*(b*(-11955*z - 280) + c*(b*(315 - 224866*z) + c*(b*(227824*z - 140) + c*(-94064*b*z + c*(15104*b*z - 3776*z) + 22572*z) - 54250*z + 35) + 56536*z - 70) - 2155*z + 70) - 22514*z)/14 + 11121/14) * h1
    + (b^2*(b*(4196*b*z - 12714*z - 35) + 378*z + 105)/14 + c*(b*(b*(b*(b*(4196*b*z - 48031*z - 35) + 63146*z + 315) + 45052*z - 560) + 22514*z + 70) + c*(b*(b*(b*(-9705*b*z + 217904*z + 35) - 270545*z - 280) - 8733*z - 385) + c*(b*(b*(b*(8602*b*z - 113998*z - 35) - 51798*z + 245) - 136072*z + 105) + c*(b*(b*(-4214*b*z + 167643*z - 35) + 79937*z + 105) + c*(b*(b*(3776*b*z - 48272*z) + 19446*z - 35) + c*(b*(3776*b*z - 22152*z) + c*(3776*b*z + 3776*c*z - 37676*z) + 144538*z - 35) - 273536*z + 210) + 228299*z - 350) + 13894*z + 280) - 90056*z - 105) + 105)/14 + 35/2) * h2
    + (-(4196*b*z + 3776*c^2*z - 15020*c*z - 126*z - 35)/14) * h3

private lemma rejectI_8_14 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, c, c) = 0) (h2 : locus b (b, b, c) = 0)
    (h3 : edge b b c (1, c, c) (b, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (b*(b*(-2821661*b - 16356200*c + 13121178) + c*(46341671 - 11297208*c) - 9392197)/47678464 + c^2*(4045048*c - 9392197)/47678464 - 1) * h0
    + (b*(b*(c*(c*(c*(c*(7270239*z + 38262) - 22250531*z + 296639) + 27931487*z - 510398) - 6534900*z - 377629) - 2891794*z + 448287) + c*(c*(c*(c*(-3434675*c*z - 11345384*z - 707847) + 1928260*z + 1217594) - 14888860*z + 720902) + 13809204*z - 342461) - 1790658*z + 469651)/5959808 + c*(c*(c*(c*(c*(505631*c*z + 5077674*z + 172179) - 983484*z - 281694) + 2477422*z - 228053) - 1790658*z + 11347) - 203161)/5959808 - 441251/5959808) * h1
    + (b*(b*(b*(b*(b*c*(-5023933*c*z + 619389*z) + c*(c*(c*(-20795803*z - 306096) + 30051212*z + 1146992) - 20495521*z + 1453088) - 1101136*z) + c*(c*(c*(-306096*c + 88321855*z + 3748808) + 23542229*z - 8449392) + 131441780*z - 11777752) - 2758088*z + 726544) + c*(c*(c*(c*(15342256*c*z - 118768304*z + 918288) + 97517108*z - 9256800) - 381715764*z + 17892728) - 225082840*z + 26194280) + 39116568*z - 3632720) + c*(c*(c*(c*(c*(-4045048*c*z - 24441200*z - 1377432) + 194547264*z + 9293760) + 36405808*z - 14149128) + 110130304*z - 8841560) - 57301056*z + 1988392) - 2133208)/47678464 + c*(c^3*(c*(-2529496*z - 153048) - 8263768*z + 726544) + 4045048)/47678464 - 9392197/47678464) * h2
    + ((137642*b*z + 316187*c*z + 19131*c + 1032971*z - 90818)/5959808) * h3

private lemma rejectI_8_23 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, c, c) = 0) (h2 : locus b (c, b, c) = 0)
    (h3 : edge b b c (1, c, c) (c, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-z*(b^2 + b*c^2 - 6*b*c + b + c^2)) * h1 + (-b*z*(b^2*c - b^2 - b*c^2 + b*c - b - c^2 + 4*c)) * h2

private lemma rejectI_8_24 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, c, c) = 0) (h2 : locus b (c, c, 1) = 0)
    (h3 : edge b b c (1, c, c) (c, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (b*(b*(9315891*z - 4001480) + 3914001*z - 3512120)/322218 + c*(b*(b*(6230840 - 8358714*z) - 28724787*z + 15546000) + c*(b*(-1252440*b + 24810786*z - 18784080) + c*(3717560*b - 2465120*c - 16452072*z + 13765920) + 27502254*z - 16614480) - 5648292*z + 1791680)/322218 - 285*z/17 + 533297/53703) * h0
    + (b*(b*(b*(b*(2179710*z - 234800) + z*(83843019*z - 49091580) + 1408800) + z*(70109001 - 132460029*z) - 3376440) + c*(c*(c*(c*(c*(c*(-22186080*z - 636160) + z*(153463464 - 148068648*z) + 5015920) + z*(473205564*z - 205276932) - 14610440) + z*(139454055*z - 379534572) + 20166040) + z*(647000739 - 960569766*z) - 13261160) + z*(253831968*z - 55229076) + 29406640) + z*(40002417*z - 32476545) + 4024520)/2899962 + c*(c*(c*(c*(c*(c*(159040*c - 10210536*z - 1661520) + z*(53416044 - 75228426*z) + 6849160) + z*(161459649*z - 12825288) - 14922040) + z*(71219655*z - 202752801) + 18322800) + z*(306568278 - 362751129*z) - 13537360) + z*(242146827*z - 8453826) - 31878960)/2899962 + z*(70943787 - 36846576*z)/2899962 - 2403680/161109) * h1
    + (b*(b*(b*(b*(b*(c*(c*(-11271960*c*z + z*(67349520 - 75228426*z) - 19880) + z*(159071445*z - 92223558) + 103320) + z*(37103175 - 83843019*z) - 117400) + c*(c*(c*(c*(44730000*z - 39760) + z*(298525500*z - 247585716) + 246400) + z*(268807626 - 490434750*z) - 222760) + z*(59449221*z - 24074892) - 941480) + z*(132460029*z - 52671321) + 1498040) + c*(c*(c*(c*(c*(-55644120*z - 79520) + z*(269875368 - 371365722*z) + 870520) + z*(355586517*z - 102604266) - 3402600) + z*(530607753*z - 390363489) + 5235320) + z*(318721824 - 558669150*z) - 1073360) + z*(29206980 - 40002417*z) - 3672320) + c*(c*(c*(c*(c*(c*(22186080*z - 79520) + z*(148068648*z - 80051832) + 691600) + z*(48617010*z - 136411488) - 1955840) + z*(515556594 - 740343240*z) + 1233960) + z*(647715042*z - 377597826) + 3663920) + z*(-8444007*z - 20017953) - 8218440) + z*(36846576*z + 5270247) + 8074720) + c*(c*(c*(c*(c*(c*(-159040*c + 10210536*z + 1860320) + z*(75228426*z - 74633184) - 8260080) + z*(78460776 - 311916501*z) + 17621760) + z*(330740730 - 124442487*z) - 18677960) + z*(710661276*z - 421877268) + 8528080) + z*(-147386304*z - 68939838) + 927320) + 37405719*z - 31843880)/2899962 + c*(c*(c*(c*(c*(-19880*c - 132678*z + 182840) + 1620567*z - 649960) - 5155488*z + 1169040) + 7069842*z - 23323640) - 152560746*z + 80094040)/2899962 - 295*z/18 + 15790300/1449981) * h2
    + ((19880*c^2 + 132678*c*z - 103320*c - 1089855*z + 117400)/2899962) * h3

private lemma rejectI_9_12 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, 1, 1) = 0) (h2 : locus b (b, b, 1) = 0)
    (h3 : edge b b c (b, 1, 1) (b, b, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((4*b^2 - 6*b - 11)/6) * h1 + (-(4*b^2 - 6*b - 3)/3) * h2

private lemma rejectI_9_15 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, 1, 1) = 0) (h2 : locus b (b, c, 1) = 0)
    (h3 : edge b b c (b, 1, 1) (b, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((c - 5)*(c + 3)/16) * h0
    + (b*(43*b + 20)/3072 + c*(b*(b*(b*(10 - b) + 3744*z - 34) - 3168*z - 15) + c*(b*(b*(b*(b - 10) - 1632*z + 12) + 960*z - 9) + c*(b*(b*(14 - 672*z) + 2112*z + 9) + c*(b*(b*(96*z - 3) + 192*z - 7) + c*(b*(2 - 96*z) + 288*z - 1) - 672*z - 5) - 3168*z + 24) + 4128*z - 40) - 576*z - 15)/3072 - 155/3072) * h1
    + (b*(b*(c*(c*(c*(2*c + 192*z - 8) + 192*z + 8) - 1152*z + 4) - 22) + c*(c^2*(8 - 4*c) - 8) + 4)/1536 + c*(c*(c*(c*(c - 5) + 10) - 10) + 5)/1536 + 95/1536) * h2
    + (-(c - 1)/1536) * h3

private lemma rejectI_9_18 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, 1, 1) = 0) (h2 : locus b (c, 1, 1) = 0)
    (h3 : edge b b c (b, 1, 1) (c, 1, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-c*z*(c - 1)*(b^2 - b*c - 3*b + 3*c - 4)/2) * h1 + (-2*b*z*(c - 1)) * h2

private lemma rejectI_9_21 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, 1, 1) = 0) (h2 : locus b (c, b, 1) = 0)
    (h3 : edge b b c (b, 1, 1) (c, b, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (b*(b*(b*(b*(b*(b*(24*c - 36) + c*(154 - 84*c) - 42) + c*(c*(128*c - 320) + 120) + 108) + c*(c*(c*(409 - 110*c) - 344) - 37) + 6) + c*(c*(c*(c*(56*c - 316) + 532) - 326) + 197) - 183) + c*(c*(c*(c*(c*(144 - 16*c) - 468) + 726) - 883) + 1063) + 1044)/1344 + c*(c*(c*(2112 - 352*c) - 1724) - 4310)/1344 - 519/448) * h1
    + (b*(b*(c*(c*(c*(c*(2*c - 31) + 172) - 99) - 492) - 1122) + c*(c*(4*c - 674) + 1994) + 1368)/672 + c/336 + 223/224) * h2
    + (-(2*c - 3)/672) * h3

private lemma rejectI_10_11 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, 1, b) = 0) (h2 : locus b (b, 1, c) = 0)
    (h3 : edge b b c (b, 1, b) (b, 1, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (b*(b*(b*(b*(b*(1049762 - 227060*b) - 966298) - 362360) + 22138) - 261846)/135000 + c*(b*(b*(b*(b*(b*(2638924 - 227060*b) - 7405704) + 4473020) + 1872008) + 354008) + c*(b*(b*(b*(b*(226802*b - 1841892) + 549085) + 4391619) + 2103989) + c*(b*(b*(b*(522430 - 113186*b) + 2577351) - 1953686) + c*(b*(b*(565543 - 215*b) - 3125532) + c*(b*(-129*b - 224265) + c*(86*b - 731) + 1046408) - 736392) - 743795) + 806826) + 116394)/135000 - 28463/67500) * h1
    + (b*(147994 - 83904*b)/135000 + c*(b*(174768 - 104712*b) + c*(b*(180441*b - 288795) + c*(b*(172528*b - 286262) + c*(b*(181883 - 112025*b) + c*(b*(86*b - 559) + 43*c + 43) + 297558) - 451335) - 463836) + 267458)/135000 + 95963/67500) * h2
    + ((113530*b^2 + 129*b*c - 184291*b - 43*c^2 + 43*c - 296784)/135000) * h3

private lemma rejectI_10_17 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, 1, b) = 0) (h2 : locus b (b, c, c) = 0)
    (h3 : edge b b c (b, 1, b) (b, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(71609509241975214520467979078656*b^3 + 569264033717861707280545385160954*b^2*c - 3832278837578933058596744684495574*b^2 - 603838703917999472652142197769378*b*c^2 + 2031833027191309691721592677815788*b*c + 5362313685929694452678542921261054*b + 589302182707112536183840105809805*c^3 - 3569532604149912798702965666843133*c^2 + 5452676932694040578141623523441859*c - 2547310475642130280151596056421491)/91751816414522207209393116990000) * h0
    + (b*(b*(b*(b*(b*(c*(c*(1850288312427569415019716087744 - 358047546209876072602339895393280*z) + 1727121859621175436863532396203520*z - 14881378649524297602850878962112) - 4107222940233898092783577502430720*z + 27991541136724768073375192096640) + c*(c*(c*(925144156213784707509858043872*c - 1803735465673782781669790780006370*z - 15492214968616486535651013970224) + 12509737059287695689020346704534160*z + 78914152580104822642453219733136) + 683019135019885879340287672448850*z - 135039923023868762913835273601136) + 10688480390859192982217859806557440*z + 38245523349991460113705718847600) + c*(c*(c*(c*(-1712902431392707098338142134904*c + 3496626120193889485400431199004620*z + 26498157107858857061832918222288) - 3129629197660706498792648432851120*z - 149627153991850545167532560869632) - 103131356503296604795591513076181660*z + 375637197363168102878521323976320) + 50794620057571975632727799696689280*z - 259928776965095046307537950874248) - 6737566374468540707821518154682880*z - 287351073726443783460264174472080) + c*(c*(c*(c*(c*(1850288312427569415019716087744*c - 4596630119714260679918719017085675*z - 22108589007169461436987009734240) + 15788493619329449250854135196758490*z + 109143860056312451664130147479168) + 23665224722935807595688439495661820*z - 295710579521986663870742031230664) + 84995927009090958862456624571915430*z + 253225654631788630099317490126152) - 68533753490257063940579219755731665*z - 5669983990341402791006446111959178) + 848930035758110451334964017825920*z + 22786746323380544592342111599401510) + c*(c*(c*(c*(c*(c*(-925144156213784707509858043872*c + 2261973756829912998788604278643905*z + 10179564782373251414693853986664) - 8785673237163455502482624227177655*z - 57832909760388623881133268599184) - 25246917903347559625458026704471950*z + 264578686115205374227381027374504) + 104940306887881408346123728414397290*z - 641693825025627539362824246047688) - 112123443370711248497954151765091795*z + 6103199163423688580615166248592514) + 28044787098183205211715947892815085*z - 16030761941522128035321866325956676) + 1493047416417685379379900683907840*z - 22145213232191567146006548461335870)/458759082072611036046965584950000 + c*(c*(17847525634868529131198146760262825 - 2946510913535562680919200529049025*c) + 999813254574117050001814214836800*z - 27265548342626390381477160247377087)/458759082072611036046965584950000 - 127125033660242008*z/214254874764376875 + 35241817292648773504517113998881/1223357552193629429458574893200) * h1
    + (b*(b*(c*(c*(c*(c*(c*(-137385881034862316681573952840*c + 999813254574117050001814214836800*z - 3327038063440748600654476491336) - 15479871398528989539716677278930435*z + 49220831991205068400349048688120) + 56909071265197053372544163362843920*z - 182896343131103048514684942980928) - 35082353579058468580317265640218405*z + 151634723752122277845529741927680) - 3474010114732512837837740662197320*z + 3096381994821364332554849455363865) - 11238888981204520642080378259653695) + c*(c*(c*(c*(-1850288312427569415019716087744*c + 16309991167802076721254010673483910*z + 16246395296786777049303553939320) - 65055937506086478427846389456137985*z - 78590051369144857269567118371456) - 43074480714731990877683406961353110*z + 403064941023718905335042745798120) + 80523208335901593788726998956384785*z - 6543158779329922652544338278702810) + 22232348127888254102867212892904670)/458759082072611036046965584950000 + c*(c*(c*(c*(925144156213784707509858043872*c - 2261973756829912998788604278643905*z - 8329276469945681999674137898920) + 4261725723503629504905415669889845*z + 40249212664283475174275134757472) + 36032343107184731634057462322895545*z - 176163141959797328829201341819160) - 34137906633293223432908776793985645*z - 5649432834930694391398611503279650)/458759082072611036046965584950000 + 165892098340657842552237279956243/3528916015943161815745889115000) * h2
    + ((30244992884532036*b*c + 22379022009382798560*b*z - 152517485486101720*b + 4491445972420295*c^2 - 32686089586526233400*c*z + 70735420251823746*c + 8898752356216940560*z - 665940805779581835)/14997841233506381250) * h3

private lemma rejectI_10_20 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, 1, b) = 0) (h2 : locus b (c, 1, c) = 0)
    (h3 : edge b b c (b, 1, b) (c, 1, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (b*(b*(b*(b*(b*(11398 - 2458*b) - 11492) - 1066) - 3538) + 2284)/1250 + c*(b*(b*(b*(b*(b*(29904 - 2458*b) - 85958) + 62802) - 5304) + 19860) + c*(b*(b*(b*(b*(3758*b - 34559) + 40799) + 12546) + 38565) + c*(b*(b*(b*(24221 - 3475*b) + 16322) + 2067) + c*(b*(b*(1596*b - 4718) - 70329) + c*(b*(10168 - 473*b) - 1892*c + 21032) - 31506) - 4132) + 34015) - 12856)/1250 - 721/625) * h1
    + (b*(5222*b - 5168)/1250 + c*(b*(11560*b - 47832) + c*(b*(-11224*b - 6311) + c*(b*(14770*b + 24198) + c*(b*(7346 - 11928*b) + c*(3961*b - 473*c - 1252) + 2609) - 14562) - 227) + 18240)/1250 + 1346/625) * h2
    + ((1229*b^2 - 650*b*c - 2012*b + 473*c^2 + 306*c - 2748)/1250) * h3

private lemma rejectI_11_17 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, 1, c) = 0) (h2 : locus b (b, c, c) = 0)
    (h3 : edge b b c (b, 1, c) (b, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (z*(b*(b*(688*b - 7936) + 4772) + c*(b*(b*(b*(b*(688*b - 7540) + 24818) + 4420) - 4847) + c*(b*(b*(b*(8826 - 872*b) - 31452) + 5111) + c*(b*(b*(b*(156*b - 1386) + 1260) - 19094) + c*(b*(b*(78*b - 468) + 16786) + c*(-2923*b + c*(195*b + 312) - 3680) + 10968) - 13312) + 6248) + 96) - 632)/1792) * h1
    + (z*(b*(3148*b + 696) + c*(b*(-20205*b - 2414) + c*(b*(4340*b - 1600) + c*(b*(4146*b + 6548) + c*(b*(-1480*b - 3464) + c*(b*(195*b + 234) - 195*c + 1675) - 4434) + 7638) - 10359) + 6543) - 868)/1792) * h2
    + (-z*(172*b + 39*c^2 - 304*c - 79)/224) * h3

private lemma rejectI_11_20 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, 1, c) = 0) (h2 : locus b (c, 1, c) = 0)
    (h3 : edge b b c (b, 1, c) (c, 1, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((3 - 2*b)*(-720171229953*b + c*(2463016007219*b + c*(100625211190*b - 407354373609*c + 401259674151) + 419543772525) - 715952999442)/907511779125) * h0
    + (b*(b*(b*(b*(b*(-552982365184*b - 276491182592) + 2903157417216) + 207368386944) + 449298171712) - 777631451040)/3630047116500 + c*(b*(b*(b*(b*(b*(1916814366720 - 37247822848*b) - 2880684919812*z + 2960462895872) + 11539612601292*z - 2681821096704) + 2796320309592*z - 14001663660480) - 10014905531166*z - 2410323528604) + c*(b*(b*(b*(b*(b*(45785477120*b + 153260118528) + 12732748948688*z - 3233783240448) - 57681415195666*z - 6903663868160) + 20290740364907*z + 2957635147008) + 19748766789677*z + 7774737455360) + c*(b*(b*(b*(b*(-160249169920*b - 9449563184116*z - 443102366976) + 40808305052740*z + 2882100153088) + 2398041000271*z + 7026143667200) - 43589137612001*z - 1809392057728) + c*(b*(b*(b*(b*(263266493440 - 402500844760*z) + 3502829624818*z + 764667913600) - 19295421812641*z - 1711718607168) + 30497551837641*z - 1370423002048) + c*(b*(b*(b*(1830667916816*z - 257543308800) - 5475596326101*z - 582305391168) + 1014223485385*z + 466206345792) + c*(b*(b*(145941208320 - 714083536028*z) + 2343501030464*z + 61547796224) + c*(-22892738560*b - 714083536028*z + 20031146240) + 4703409485275*z - 122174838336) - 26947922975093*z + 22339927488) + 63373439984696*z + 1233473591360) - 64755623915860*z - 2894367490240) + 27950073567797*z + 476850854208) - 3609292610787*z + 864893910024)/3630047116500 - 15120611548/43214846625) * h1
    + (b*(b*(c*(c*(c*(c*(c*(c*(-714083536028*z - 37200700160) + 9280079277315*z + 250606464704) - 24419904949130*z - 41870538624) - 886004722674*z - 2099140266816) + 30364112072470*z + 3064041119744) - 13624198141953*z - 3195103009984) + 1501677557816) + c*(c*(c*(c*(c*(c*(22892738560*c - 201250422380*z - 121641234944) - 10839950725042*z - 219868708224) + 28552512000240*z + 1856171933440) - 18605327426668*z - 1165868491136) - 8920888957316*z - 5527905013760) + 10014905531166*z + 11707531386916) - 2136799312860)/3630047116500 + c*(c*(c*(c*(c*(c*(c*(714083536028*z - 20031146240) - 4703409485275*z + 122174838336) + 26947922975093*z - 22339927488) - 63373439984696*z - 1233473591360) + 64755623915860*z + 2894367490240) - 27950073567797*z - 476850854208) + 3609292610787*z - 5753146393332)/3630047116500 - 307604792231/302503926375) * h2
    + (-256*(44712380*c^2 - 36374827*c - 540021841)/907511779125) * h3

private lemma rejectI_12_15 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, b, 1) = 0) (h2 : locus b (b, c, 1) = 0)
    (h3 : edge b b c (b, b, 1) (b, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (b*(b*(b*(b*(b*(1049762 - 227060*b) - 966298) - 362360) + 22138) - 261846)/135000 + c*(b*(b*(b*(b*(b*(2638924 - 227060*b) - 7405704) + 4473020) + 1872008) + 354008) + c*(b*(b*(b*(b*(226802*b - 1841892) + 549085) + 4391619) + 2103989) + c*(b*(b*(b*(522430 - 113186*b) + 2577351) - 1953686) + c*(b*(b*(565543 - 215*b) - 3125532) + c*(b*(-129*b - 224265) + c*(86*b - 731) + 1046408) - 736392) - 743795) + 806826) + 116394)/135000 - 28463/67500) * h1
    + (b*(147994 - 83904*b)/135000 + c*(b*(174768 - 104712*b) + c*(b*(180441*b - 288795) + c*(b*(172528*b - 286262) + c*(b*(181883 - 112025*b) + c*(b*(86*b - 559) + 43*c + 43) + 297558) - 451335) - 463836) + 267458)/135000 + 95963/67500) * h2
    + ((113530*b^2 + 129*b*c - 184291*b - 43*c^2 + 43*c - 296784)/135000) * h3

private lemma rejectI_12_18 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, b, 1) = 0) (h2 : locus b (c, 1, 1) = 0)
    (h3 : edge b b c (b, b, 1) (c, 1, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(16046*c + 4915)*(3*c^2 - 55*c + 175)/860125) * h0
    + (b*(b*(b*(b*(c*(c*(5964*c - 2567360*z - 135026) + 6915680*z + 803912) + 2359200*z - 1357530) + c*(c*(c*(c*(2982*c - 1283680*z - 94351) + 15010960*z + 991681) - 22238880*z - 3891291) - 31363440*z + 3697149) - 7077600*z + 4072590) + c*(c*(c*(c*(c*(-5964*c + 2326670*z + 170810) - 17740225*z - 1578284) + 6703170*z + 5385756) + 57618880*z - 3665237) + 38312385*z - 6018266) + 6684400*z - 3846335) + c*(c*(c*(c*(c*(c*(8946*c - 3610350*z - 259197) + 31627965*z + 2548255) - 95395620*z - 11077395) + 123595340*z + 22046519) - 53340575*z - 19201147) - 41233940*z + 10495659) - 3145600*z + 1810040)/4300625 + c*(c*(4335943 - 240690*c) + 1283680*z - 12630058)/4300625 + 16*z/175 - 45251/860125) * h1
    + (b*(b*(c*(c*(c*(c*(c*(-2982*c + 1283680*z + 85405) - 11881990*z - 845800) + 47105845*z + 4006936) - 65612210*z - 10065353) + 12276590*z + 12346734) + 11378225*z - 7117860) + c*(c*(c*(c*(17892*c - 6257940*z - 440862) + 17819730*z + 3156288) - 33267250*z - 7768616) + 30159230*z + 5192768) + 12926450*z + 4109280)/4300625 + c*(c*(c*(c*(-8946*c + 3610350*z + 223413) - 17186565*z - 1654603) + 26649360*z + 4450037) - 13146860*z - 4531176)/4300625 - 41*z/25 + 248269/122875) * h2
    + (-(-2982*c^2 + 1283680*c*z + 58567*c + 393200*z - 226255)/4300625) * h3

private lemma rejectI_12_21 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, b, 1) = 0) (h2 : locus b (c, b, 1) = 0)
    (h3 : edge b b c (b, b, 1) (c, b, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(b + c - 3)*(113071*c^3 - 241867*c^2 - 334067*c + 155246)/3000) * h0
    + (b*(b*(b*(b*(b*(b*(c*(34194 - 7798*c) - 11998) + c*(c*(31192*c - 144574) + 82186) - 11998) + c*(c*(c*(318839 - 58485*c) - 347941) + 27596) + 23996) + c*(c*(c*(c*(c*(66283 - 565355*z) + 1774690*z - 458306) + 461000*z + 915134) - 2446565*z - 638887) + 776230*z + 290950) - 59990) + c*(c*(c*(c*(c*(-46788*c + 3392130*z + 411811) - 10648140*z - 1243261) - 2766000*z + 1605311) + 14679390*z - 994026) - 4657380*z + 362938) - 59990) + c*(c*(c*(c*(c*(c*(c*(565355*z + 19495) - 3470755*z - 225849) + 1470940*z + 1054882) + 14477705*z - 2518019) - 5349925*z + 3027960) - 12350700*z - 1880650) + 4657380*z + 882360) + 1923650)/15000 + c*(c*(c*(c*(c*(565355*z + 19495) - 1774690*z - 732719) - 461000*z + 3497180) + 2446565*z - 1853680) - 776230*z - 6770441)/15000 - 1287701/7500) * h1
    + (b*(b*(c*(c*(c*(c*(c*(-3899*c - 1696065*z + 59986) + 5324070*z - 431905) + 1383000*z + 1526099) - 7339695*z - 2035459) + 2328690*z + 781756) - 2187606) + c*(c*(c*(c*(c*(3392130*z + 38990) - 10648140*z - 284041) - 2766000*z + 922309) + 14679390*z - 2794829) - 4657380*z + 3970781) + 1987500)/15000 + c*(c*(c*(c*(c*(-565355*z - 19495) + 1774690*z + 167364) + 461000*z - 591780) - 2446565*z - 103990) + 776230*z + 983206)/15000 + 1229773/3750) * h2
    + ((3899*c^2 - 17097*c + 5999)/15000) * h3

private lemma rejectI_13_14 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, b, b) = 0) (h2 : locus b (b, b, c) = 0)
    (h3 : edge b b c (b, b, b) (b, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (z*(b*(b*(b*(b*(472 - 280*b) - 472) + 972) - 604) + c*(b*(b*(b*(b*(1778 - 114*b) - 2002) + 176) + 2584) + c*(b*(b*(b*(b*(166*b - 1510) + 3090) - 4739) - 3127) + c*(b*(b*(b*(887 - 140*b) - 122) + 1284) + c*(b*(b*(57*b + 218) - 1969) + c*(-280*b + 70*c + 415) + 409) + 772) - 604)))/366) * h1
    + (z*(b*(b*(c*(c*(c*(c*(13*c - 428) + 507) - 1797) + 3540) - 2180) + c*(c*(c*(c*(1433 - 8*c) + 133) - 889) - 772) + 604) + c^4*(c*(13*c - 244) + 96))/366) * h2
    + (-z*(83*b*c - 140*b + 13*c^2 - 244*c + 96)/366) * h3

private lemma rejectI_13_23 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, b, b) = 0) (h2 : locus b (c, b, c) = 0)
    (h3 : edge b b c (b, b, b) (c, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-c*z*(b - 1)*(b*c - b - c^2)) * h1 + (-b*c*z*(b - 1)) * h2

private lemma rejectI_13_24 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, b, b) = 0) (h2 : locus b (c, c, 1) = 0)
    (h3 : edge b b c (b, b, b) (c, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (z*(b*(2*b - 8) + c*(b*(b*(b*(2*b - 16) + 29) + 15) + c*(b*(11 - 3*b) + c*(b*(2*b - 9) + 4*c - 15) + 18) - 7))) * h1
    + (z*(b*(2*b - 8) + c*(b*(21 - 7*b) + c*(b*(4*b - 8) + c*(-2*b + 2*c - 8) + 12) - 8) + 2)) * h2
    + (-2*z) * h3

private lemma rejectI_14_23 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, b, c) = 0) (h2 : locus b (c, b, c) = 0)
    (h3 : edge b b c (b, b, c) (c, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((b - 2)*(301*b*c^2 + 246639*b*c + 63661*b - 66220*c^3 - 39251*c^2 + 205824)/411648) * h0
    + (b*(b*(b*(b*(b*(55216*b + 55216) - 276080) - 165648) - 55216) + 55216)/411648 + c*(b*(b*(b*(b*(b*(3728*b - 217136) - 63661*z - 294720) + 112481*z + 596192) + 838137*z + 1542320) - 808455*z - 57660) + c*(b*(b*(b*(b*(b*(-2408*b - 17320) - 182978*z + 407520) + 1184375*z + 517568) - 1881518*z - 1577296) - 5667*z - 1585316) + c*(b*(b*(b*(b*(9632*b + 246338*z + 40000) - 1009461*z - 464136) - 1126889*z - 181128) + 4694218*z + 2343096) + c*(b*(b*(b*(b*(301*z - 18060) - 220874*z - 52156) + 1797511*z + 404740) - 3234027*z - 677744) + c*(b*(b*(b*(20468 - 66521*z) + 306539*z + 22368) - 314668*z - 196276) + c*(b*(b*(66220*z - 14448) - 331401*z + 37868) + c*(1204*b + 66220*z - 7224) - 26066*z + 28040) + 699763*z + 132328) - 754758*z - 371716) + 14841*z + 186544) + 24260) + 395947)/411648 - 9717/34304) * h1
    + (b*(b*(c*(c*(c*(c*(c*(4816*c - 199563*z - 12272) - 657204*z - 118628) + 1405701*z + 162356) + 259521*z + 316032) - 808455*z - 583212) + 282252) + c*(c*(c*(c*(c*(c*(-1204*c + 198961*z - 23420) + 366800*z + 140196) + 1834501*z + 413088) - 3184702*z - 1599664) - 24015*z + 1212228) + 808455*z - 57080) - 224763)/411648 + c*(c*(c*(c*(c*(c*(c*(7224 - 66220*z) + 26066*z - 28040) - 699763*z - 132328) + 754758*z + 371716) - 14841*z - 186544) - 24260) - 263507)/411648 + 97553/205824) * h2
    + ((301*c^2 - 466*c - 6902)/102912) * h3

private lemma rejectI_14_24 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, b, c) = 0) (h2 : locus b (c, c, 1) = 0)
    (h3 : edge b b c (b, b, c) (c, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (b*(b*(b*(b*(b*(37285799168276795963156 - 37120940089661622047612*b) + 143569201323860118879490) - 74654027875861178884084) - 219801907512726801477952) - 43614177437453495072948)/463967372565043937268 + c*(b*(b*(b*(b*(b*(77812566083895274362382*b + 328414369606608823677894) - 998952005394463924328685) + 128704594386659025701310) + 1539553141897858208096378) + 560087500650511248307262) + c*(b*(b*(b*(b*(b*(114933506173556896409994*b - 1585356096218435371406856) + 1890103768588911123100235) - 532785478425782752573659) - 3180540291949775536229462) - 3733939562555361871370348) + c*(b*(b*(b*(b*(4255190373250546279883526 - 355940204024582214545534*b) - 2797525874791849875052267) + 5034689006946652267564118) + 13214160160981097946161089) + c*(b*(b*(b*(509428562858502558398822*b - 5832547552471943305735196) + 517835453236706179666309) - 24155045145836742293377619) + c*(b*(b*(3357035005960100906561788 - 306976717667840687706576*b) + 14221443731451693411089832) + c*(b*(54830334312903844255484*b - 3442393986552890497630648) + 712794346067749975321292*c - 4237939923377837206159110) + 13216033611814827017390003) - 18601574000057909664221110) + 11531763429776755074965700) - 2587040103736344246073659) - 25576181320358137244023)/463967372565043937268 + 23132219880728814619181/231983686282521968634) * h1
    + ((3556276513308741511408030*b^2*c^5 - 5499446810620191371480822*b^2*c^4 - 894152554396408828344522*b^2*c^3 + 2880167980508475849137868*b^2*c^2 - 964047265408487263982225*b^2*c + 53334683884402610968102*b^2 - 1469233496132560505674568*b*c^6 - 12300173593186374419248236*b*c^5 + 33928743001345826565686177*b*c^4 - 23804886896997889771106562*b*c^3 + 7094876435255540729994650*b*c^2 - 861491917075496627104842*b*c + 23145310922386832503676*b + 164491002938711532766452*c^7 + 4075537409400254717712622*c^6 - 9530594730463744335028027*c^5 + 6431592454646454579455202*c^4 - 2926139343028557081812529*c^3 + 1161268178254919318059087*c^2 - 271180545937647246002363*c + 25847392922418075817498)/463967372565043937268) * h2
    + (-(57466753086778448204997*b^2*c - 18560470044830811023806*b^2 - 63036595838734210862773*b*c^2 - 77161355318803718428303*b*c + 18642899584138397981578*b + 13707583578225961063871*c^3 + 33444867611943421410685*c^2 - 18274225184247015074599*c + 25383425549853031880230)/463967372565043937268) * h3

private lemma rejectI_15_18 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, c, 1) = 0) (h2 : locus b (c, 1, 1) = 0)
    (h3 : edge b b c (b, c, 1) (c, 1, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((2832*b^3 - 25802*b^2*c - 4248*b^2 - 31070*b*c^2 + 118160*b*c - 2436*c^3 + 6288*c^2 - 5268*c - 6603)/8019) * h0
    + (b*(b*(b*(b*(b*(b*(c*(47412*z - 2672) - 142236*z + 14136) + c*(c*(16032 - 208008*z) + 919188*z - 92832) - 426708*z + 42408) + c*(c*(-41416*c - 2705508*z + 267204) + 2847744*z - 249104) + 284472*z - 28272) + c*(c*(c*(c*(59452 - 1564596*z) + 11886588*z - 446122) - 13240152*z + 733606) + 1590624*z - 192560) + 284472*z - 28272) + c*(c*(c*(c*(c*(1365768*z - 47762) - 6351642*z + 428365) + 1341468*z - 1072060) + 3001185*z + 749165) + 74277*z + 20256) - 426708*z + 42408) + c*(c*(c*(c*(c*(c*(19706 - 133056*z) + 400734*z - 223157) - 223452*z + 908610) + 4743333*z - 1547115) - 5438691*z + 1031140) + 508896*z - 98584) + 568944*z - 56544)/433026 + c*(c*(c*(c*(c*(47412*z - 2672) - 331884*z + 24824) + 853416*z - 72576) - 1043064*z + 95504) + 616356*z - 190760)/433026 - 878*z/2673 + 15100/72171) * h1
    + (b*(b*(c*(c*(c*(c*(c*(246240*z - 1670) - 1159326*z + 7833) + 2474550*z - 89221) - 426519*z + 324711) - 782514*z - 370917) - 636903*z - 7632) + c*(c*(c*(c*(c*(35404 - 929880*z) + 1235844*z - 222706) + 1062936*z + 536666) - 2264544*z - 562382) + 468936*z + 315258) + 426708*z - 10440)/433026 + c*(c*(c*(c*(c*(c*(133056*z - 19706) + 149850*z + 167713) - 565812*z - 536130) - 600183*z + 844436) + 1843317*z - 674476) - 1170423*z + 276555)/433026 + 865*z/1782 - 90334/24057) * h2
    + (-2*(11853*c*z - 668*c - 35559*z + 3534)/216513) * h3

private lemma rejectI_15_21 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, c, 1) = 0) (h2 : locus b (c, b, 1) = 0)
    (h3 : edge b b c (b, c, 1) (c, b, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (b*(b*(54166528000*b + c*(c*(118337709750*z + 435634700166) - 290127122500*z - 1085211378980) - 109499894750*z - 524547338606) + c*(c*(c*(92066719875*z + 338923729323) - 349076498000*z - 1323505043408) + 188619040375*z + 781682090751) + 218999789500*z + 886595093212)/70830720000 + c*(c*(c*(c*(16448932500*z + 60553189620) - 75735478500*z - 286967890116) + 62296159625*z + 284011948289) + 101508082125*z + 321258568229)/70830720000 - 437999579*z/283322880 - 81174167101/11805120000) * h0
    + (b*(b^4*(b*(-100414464000*z - 367560105984) - 200828928000*z - 735120211968) - 272769902000*z - 457775053872)/283322880000 + c*(b*(b*(b*(b*(b*(b*(24999936000*z + 92031860736) + 376796160000*z + 1776824180736) + z*(218999789500*z + 2549555221212) + 4104421183488) + z*(-1204498842250*z - 4430978676666) + 3216150927360) + z*(1478248579125*z + 6138730127181) + 45945013248) + z*(-875999158000*z - 3309103188848) + 1238837452800) + c*(b*(b*(b*(b*(-398804729856*b + z*(361254455500*z - 302888495252) - 4029429977088) + z*(-1313128990750*z - 7224107920302) - 9442941272064) + z*(-319750003750*z - 2705482633590) - 8021251292160) + z*(-1811496307625*z - 7131151419937) - 3131036083200) + c*(b*(b*(b*(b*(z*(-816929664500*z - 2891692542292) + 751593529344) + z*(3754017674750*z + 16026202253966) + 5256379619328) + z*(-1846277400750*z - 5583776483262) + 10505355082752) + z*(2370819759875*z + 10566380999723) + 7369770381312) + c*(b*(b*(b*(b*z*(236675419500*z + 871269400332) + z*(-1302185571750*z - 5090953759478) - 774601494528) + z*(397888213500*z + 695015153436) - 3889462287360) + z*(2336101178000*z + 7694137262608) - 5284809271296) + c*(b*(b*(b*z*(65795730000*z + 242212758480) + z*(408228321625*z + 1639766776401) + 440985999360) + z*(-2822208694500*z - 10241923199172) + 1373046263808) + c*(b*c*z*(-92066719875*z - 338923729323) + b*(b*z*(-118337709750*z - 435634700166) + z*(894849942125*z + 3287339626949) - 116957156352)) + z*(-92066719875*z - 334757073323) + 15338643456) + z*(618649782500*z + 2262166006980) - 147539887104) + z*(-1150392786750*z - 4154036796878) + 853638829056) + z*(240560092500*z + 396049284100) - 2271624683568) + z*(383249631625*z + 1642006639121) + 1181657082000)/283322880000 - 193703167*z/566645760 - 201460273579/70830720000) * h1
    + (b*(915550107744*b + 2286123354504)/283322880000 + c*(b*(-2523619918848*b - 4621317301296) + c*(b*(2016004921344*b + 10260222382080) + c*(b*(-594491271168*b - 7729030557696) + c*(b*(35506071552*b + 2381657911296) + c*(b*(5751991296*b - 256922277888) + 116957156352*c - 1164057246720) + 4368654987264) - 7726416838656) + 6576827735040) - 1508304997716)/283322880000 + z*(b*(545539804000*b + 466473069000) + c*z*(b*(273749736875*b + 109499894750) + c*(b*(2354994145125*b - 38372561750) + c*(b*(-2899281529750*b - 660219393000) + c*(b*(1115894602000 - 243028175250*b) + c*(b*(605632542875*b - 645140251750) + c*(b*(118337709750 - 92066719875*b) + 92066719875*c - 802783222250) + 2479759071625) - 3159995448500) + 1248263340125) + 525939170750) - 383249631625) + c*(b*(-370492389485*b - 364759395394) + c*(b*(9518026599677*b + 1909524947162) + c*(b*(-10577043309926*b - 4017262021288) + c*(b*(4605293042832 - 1038297887874*b) + c*(b*(2255981532931*b - 2461906967478) + c*(b*(435634700166 - 338923729323*b) + 338923729323*c - 2948415897626) + 9013125884161) - 10900493154836) + 3001186811957) + 3234000216142) - 1429677477621) - 341147995500)/283322880000 - 214754009027/70830720000) * h2
    + (-(1017250*c*z + 3744786*c - 4085875*z - 14956059)/69170625) * h3

private lemma rejectI_16_19 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, c, b) = 0) (h2 : locus b (c, 1, b) = 0)
    (h3 : edge b b c (b, c, b) (c, 1, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((36764931894775812879*b^3 + 35731099183964082015*b^2*c^2 + 348917005266172992*b^2*c*z - 114998753685105181552*b^2*c - 2750051959307984808*b^2*z + 9761343561812843471*b^2 - 22211223817058753685*b*c^3 - 2130258166393153248*b*c^2*z + 130536579622195766393*b*c^2 + 5445022971481181136*b*c*z - 223345329114849732205*b*c + 5500103918615969616*b*z - 129817482807953125579*b - 312885651325376334*c^4 + 105598442871370152*c^3*z + 5298514483166125343*c^3 - 991670068663730496*c^2*z + 7336892095134238767*c^2 + 2456215901176600296*c*z - 21824334938465932567*c - 2750051959307984808*z + 80889062433124193429)/2402144918240275800) * h0
    + (b*(b*(b*(b*(b*(b*(c*(-5794232300102283570*c*z + z*(9585099888799195572 - 247917517165932624*z) - 82653718485108) + z*(743752551497797872*z + 23405031244997362854) + 1507340811559094) + c*(c*(37662509950664843205*c*z + z*(1611463861578562056*z + 27711833356774674924) + 537249170153202) + z*(-5702102894816450352*z - 228879649166013112686) - 10087003289831989) + z*(2603133930242292552*z + 81917609357490769989) + 5275692840456829) + c*(c*(c*(z*(-3539723051771234568*z - 266378244196653298071) - 1529093791974498) + z*(9544824410888406024*z + 393086346834218043153) + 29580206242787953) + z*(-6872812669197935640*z - 182995334099301750795) - 30859159777718873) + z*(-371876275748898936*z - 11702515622498681427) - 753670405779547) + c*(c*(c*(2479611554553240*c + z*(442422244144459836456 - 6321790177612512984*z) - 49518217707998436) + z*(61208033011358579424*z - 676618243911702254823) + 79290913104409076) + z*(521978284171788705777 - 48688304904597750840*z) - 16332787771694710) + z*(-2231257654493393616*z - 70215093734992088562) - 4522022434677282) + c*(c*(c*(c*(c*(-102337722205766091477*c*z + z*(1015684959931702322880 - 482038170018475896*z) - 2396957836068132) + z*(35383220633161418472*z - 3744072054739396013700) + 48506799207349990) + z*(5554878219291583767279 - 163653261568261079472*z) - 88624245988461518) + z*(84843084838121283744*z - 2080931332674789054156) + 20616635990330243) + z*(43661076749830920528*z - 622042385009093969394) + 22444804736416194) + z*(1487505102995595744*z + 46810062489994725708) + 3014681623118188) + c*(c*(c*(c*(c*(c*(93646373755612666122*c*z + z*(3649884946040811528*z - 1019131975877368931967) + 1322459495761728) + z*(4200268347131075888136 - 53081942402136360240*z) - 24448067858885936) + z*(170677839744906297984*z - 7781134081472562942219) + 7351822741998104) + z*(5317743050178418412592 - 81083037997810895256*z) - 12297971241575060) + z*(528639267394381294992 - 47063150688824568360*z) - 163312585970362186) + z*(4297272467582421792*z - 1423622764150274979864) - 734929498415572936) + z*(2231257654493393616*z + 60536626286384343546) - 3970335697646653596)/7206434754720827400 + c*(c*(c*(c*(c*(-2897116150051141785*c*z + z*(115821620600319114618 - 123958758582966312*z) - 41326859242554) + z*(4765513773287508336*z - 781319684004890114955) + 2324091056996599) + z*(2174871548075824128939 - 45479174045754016080*z) - 25374653539461020) + z*(56167221012515897616*z - 2590425799497445871370) - 982905978112968235) + z*(1121520750672303381528 - 14337931912802693064*z) + 15682643066711059823)/7206434754720827400 + z*(-1115628827246696808*z - 34742813069519553969)/7206434754720827400 + 7030991215517393963/2402144918240275800) * h1
    + (b*(3966567345617755861*b + 89200314696963697654)/7206434754720827400 + c*(b*(753977892856274381*b - 3764770286400598004) + c*(b*(81636681070886807*b - 830494401584261000) + c*(b*(93594326570042132*b - 200432745905594422) + c*(b*(491564107734140*b - 92722104322771990) + c*(b*(5868414012442668 - 330614873940432*b) - 1322459495761728*c + 20232728216145428) + 56380617408383518) + 197207071783086956) + 929255656092682941) - 65477568164691717537)/7206434754720827400 + z*(b*(11337781824522191115 - 119049204398877750681*b) + c*(b*(1670603600726581544409*b - 1229012393081929957095) + c*(b*(6233499415816936888251 - 632601751915679268558*b) + c*(b*(-1501117421738199632178*b - 11032753892663267040921) + c*(b*(596576036782987053171*b + 8490555838293098704089) + c*(b*(18222877081084299351*b - 2792454342396069756972) + c*(b*(348511449671990388423 - 23176929200409134280*b) - 93646373755612666122*c + 720810157710224082891) - 2115256069643799415011) + 2626655792696167010280) - 1265983321727362082112) + 175653121384559855385) - 58053896087062689888) + z*(b*(371876275748898936 - 4090639033237888296*b) + c*(b*(5619428219054883168*b + 11238962948228535264) + c*(b*(-28827203292577593288*b - 91371614960197099152) + c*(b*(13538885393932568856*b + 224600006238615412632) + c*(b*(14875157540074726368*b - 154163624614626230856) + c*(b*(9944187905145314736 - 991670068663730496*b) - 3649884946040811528*c + 41388535012516127784) - 48109901704623087336) + 5041025019080219664) + 7437525514977978720) - 2355216413076359928) + 371876275748898936) + 3452359744574727003)/7206434754720827400 + 124937187862249593617/3603217377360413700) * h2
    + ((2897116150051141785*c^2*z + 123958758582966312*c*z^2 - 4792549944399597786*c*z + 41326859242554*c - 371876275748898936*z^2 - 11702515622498681427*z - 753670405779547)/7206434754720827400) * h3

private lemma rejectI_16_22 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, c, b) = 0) (h2 : locus b (c, b, b) = 0)
    (h3 : edge b b c (b, c, b) (c, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-b*z*(c - 1)*(b*c - 2*b - c^2 + 2*c - 1)) * h1 + (-z*(c - 1)*(2*b^2 - 3*b*c + b + c^2)) * h2

private lemma rejectI_16_25 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, c, b) = 0) (h2 : locus b (c, c, b) = 0)
    (h3 : edge b b c (b, c, b) (c, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((b - 2)*(301*b*c^2 + 246639*b*c + 63661*b - 66220*c^3 - 39251*c^2 + 205824)/411648) * h0
    + (b*(b*(b*(b*(b*(55216*b + 55216) - 276080) - 165648) - 55216) + 55216)/411648 + c*(b*(b*(b*(b*(b*(3728*b - 217136) - 63661*z - 294720) + 112481*z + 596192) + 838137*z + 1542320) - 808455*z - 57660) + c*(b*(b*(b*(b*(b*(-2408*b - 17320) - 182978*z + 407520) + 1184375*z + 517568) - 1881518*z - 1577296) - 5667*z - 1585316) + c*(b*(b*(b*(b*(9632*b + 246338*z + 40000) - 1009461*z - 464136) - 1126889*z - 181128) + 4694218*z + 2343096) + c*(b*(b*(b*(b*(301*z - 18060) - 220874*z - 52156) + 1797511*z + 404740) - 3234027*z - 677744) + c*(b*(b*(b*(20468 - 66521*z) + 306539*z + 22368) - 314668*z - 196276) + c*(b*(b*(66220*z - 14448) - 331401*z + 37868) + c*(1204*b + 66220*z - 7224) - 26066*z + 28040) + 699763*z + 132328) - 754758*z - 371716) + 14841*z + 186544) + 24260) + 395947)/411648 - 9717/34304) * h1
    + (b*(b*(c*(c*(c*(c*(c*(4816*c - 199563*z - 12272) - 657204*z - 118628) + 1405701*z + 162356) + 259521*z + 316032) - 808455*z - 583212) + 282252) + c*(c*(c*(c*(c*(c*(-1204*c + 198961*z - 23420) + 366800*z + 140196) + 1834501*z + 413088) - 3184702*z - 1599664) - 24015*z + 1212228) + 808455*z - 57080) - 224763)/411648 + c*(c*(c*(c*(c*(c*(c*(7224 - 66220*z) + 26066*z - 28040) - 699763*z - 132328) + 754758*z + 371716) - 14841*z - 186544) - 24260) - 263507)/411648 + 97553/205824) * h2
    + ((301*c^2 - 466*c - 6902)/102912) * h3

private lemma rejectI_16_26 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, c, b) = 0) (h2 : locus b (c, c, c) = 0)
    (h3 : edge b b c (b, c, b) (c, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (z*(b*(b*(b*(b*(b*(b*(22*c + 22) - 222*c - 90) + c*(c*(-c - 169) + 454) + 104) + c*(c*(c*(c + 168) + 1663) - 288) - 116) + c*(c*(c*(c*(5*c - 100) - 1508) - 2664) + 910) - 12) + c*(c*(c*(c*(647 - 24*c) + 1980) - 1094) - 234) + 92) + c^4*(c*(5*c - 96) + 27))/14) * h1
    + (z*(b*(196*b - 92) + c*(b*(142 - 482*b) + c*(b*(186*b + 916) + c*(b*(330*b - 1496) + c*(b*(-9*b - 107) + c*(5*b + 3) + 423) - 134) - 92)))/14) * h2
    + (-z*(11*b^2 + 11*b*c - 12*b + 5*c^2 - 96*c + 27)/14) * h3

private lemma rejectI_17_20 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, c, c) = 0) (h2 : locus b (c, 1, c) = 0)
    (h3 : edge b b c (b, c, c) (c, 1, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((c - 2)*(b*(b*(289523816*b - 7345786621) + 877899095) + c*(81503994416*b + c*(-35886371632*b + 12259803776*c - 52272871754) + 67771379047) - 27753264202)/5046867) * h0
    + (b*(b*(b*(b*(b*(b*(18735616*b + 108672256*c - 429069632) + c*(c*(1737142896*c*z - 5211428688*z - 930254592) + 3474285792*z + 2912597856) - 1274081952) + c*(c*(c*(2370126464 - 51023291310*z) + 153069873930*z - 8056686240) - 102046582620*z + 5019546272) + 2061962656) + c*(c*(c*(c*(-216186801240*c*z + 1141058656008*z - 2972957696) - 1729170657318*z + 12596004016) + 442903398498*z - 13277209520) + 361395404052*z - 1180866384) + 2125657744) + c*(c*(c*(c*(c*(72690251208*c*z + 357682295019*z + 1682035392) - 3230787103491*z - 9386890688) + 5935285387935*z + 14111426512) - 2808978652101*z + 262682016) - 325892178570*z - 6846833648) - 2652626976) + c*(c*(c*(c*(c*(-287139909552*c*z + 1817054980647*z + 2840394688) - 4738489227825*z - 8829549840) + 6410700776085*z + 19709140016) - 4402871747439*z + 8616907568) + 1200745128084*z - 83157004416) + 918090232)/60562404 + c*(c*(c*(c*(c*(c*(72690251208*c*z - 446975087469*z - 11709760) + 1080530229165*z - 35129280) - 1318419460050*z - 9045795520) + 850989612498*z + 3009980112) - 270350081025*z - 42766608576) + 31534535673*z + 181826550976)/60562404 - 1021333526/15140601) * h1
    + (b*(b*(c*(c*(c*(c*(c*(214449658344*c*z - 1958550474426*z - 288067200) + 6828217675308*z - 756455984) - 10567529358288*z - 1720841200) + 6621088555800*z - 11338834560) - 1137676056738*z - 31697999232) + 167135178000) + c*(c*(c*(c*(c*(c*(-72690251208*c*z + 446975087469*z + 11709760) - 1080530229165*z + 1305438144) + 1318419460050*z + 2821588800) - 850989612498*z + 6646797616) + 270350081025*z + 38966808128) - 31534535673*z - 173935524352) - 15061873872)/60562404 + c*(c*(c*(c*(211718144*c - 1322781248) + 3173943552) + 143415320704) - 625159108216)/60562404 + 55471916215/5046867) * h2
    + (-16*(292744*b + 3308096*c - 7436073)/15140601) * h3

private lemma rejectI_18_21 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (c, 1, 1) = 0) (h2 : locus b (c, b, 1) = 0)
    (h3 : edge b b c (c, 1, 1) (c, b, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((2*c^2 - 6*c - 9)/9) * h0
    + (b*(b*(b*(b*(b*(c*(-16*c + 324*z + 52) - 648*z + 8) + c*(c*(16*c - 324*z + 44) - 324*z - 292) + 1620*z - 92) + c*(c*(c*(-16*c + 486*z + 20) - 1620*z - 36) + 1215*z + 378) + 729*z + 216) + c*(c*(c*(c*(16*c - 648*z - 84) + 3402*z + 116) - 4212*z - 130) + 3969*z + 328) - 3807*z - 70) + c*(c*(c*(c*(c*(-16*c + 648*z + 132) - 4536*z - 304) + 10044*z + 174) - 10044*z - 22) + 486*z - 180) + 4374*z - 198)/729 + c*(c*(c*(-16*c + 648*z + 84) - 2592*z - 238) + 4050*z + 404)/729 - 28*z/9 + 298/729) * h1
    + (2*b*(b*(b*(b*(b*(-486*z - 30) + 2916*z + 180) - 3645*z - 225) - 2673*z - 165) + c*(c*(c*(c*(c*(8*c - 324*z - 74) + 2592*z + 210) - 7290*z - 205) + 9396*z + 122) - 4941*z - 11) + 1944*z + 120)/729 + 2*c*(77*c + 81*z - 226)/729 - 2*z/3 - 10/243) * h2
    + (-2*(c - 3)*(-4*c + 81*z + 5)/729) * h3

private lemma rejectI_19_22 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (c, 1, b) = 0) (h2 : locus b (c, b, b) = 0)
    (h3 : edge b b c (c, 1, b) (c, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (z*(b*(b*(c*(c*(c*(38 - 6*c) - 62) + 36) - 30) + c*(c*(c*(c*(8*c - 62) + 173) - 271) + 222) + 1) + 3*c - 10)) * h1
    + (z*(b*(b*(b*(b*(b*(2*c + 2) + c*(8*c - 28) - 32) + c*(c*(6*c - 70) + 129) + 135) + c*(c*(c*(-2*c - 14) + 145) - 198) - 139) + c*(c*(c*(c*(70 - 8*c) - 195) + 204) - 90) - 88) + c*(c*(46 - 8*c) - 76) + 80)) * h2
    + (-z*(b + 3*c - 10)) * h3

private lemma rejectI_19_25 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (c, 1, b) = 0) (h2 : locus b (c, c, b) = 0)
    (h3 : edge b b c (c, 1, b) (c, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (b*(b*(b*(b*(b*(2338616 - 283415*b) - 5470008) + 1690629) - 242068) - 6180389)/5013 + c*(32314306*b + c*(-15849351*b + c*(3316393*b + c*(-232403*b + c*(-16808*b + 4456*c + 70280) - 735534) + 3069498) - 5977832) - 1640)/5013 + 33322/5013) * h1
    + (b*(b*(b*(b*(b*(b*(283415*b - 2622031) + 7536977) - 5112033) - 2631469) + 5232291) - 9448112)/5013 + c*(b*(b*(b*(b*(b*(b*(11768*b - 620499) + 3814140) - 6820873) + 353208) - 8560062) - 13395121) + c*(b*(b*(b*(b*(b*(522983 - 21264*b) - 1152822) - 263788) + 2875366) + 12813902) + c*(b*(b*(b*(b*(16224*b - 550323) + 979820) + 676781) - 4404586) + c*(b*(b*(b*(147872 - 21264*b) + 90031) + 1561344) + c*(b*(b*(4456*b + 2856) - 437859) + c*(-21264*b + 4456*c + 87520) - 450482) + 639289) + 64796) - 517007) - 1793548)/5013 + 1835813/1671) * h2
    + (-(11768*b^2*c + 283415*b^2 - 21264*b*c^2 - 538123*b*c - 626358*b + 4456*c^3 + 114256*c^2 + 168214*c + 28309)/5013) * h3

private lemma rejectI_19_26 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (c, 1, b) = 0) (h2 : locus b (c, c, c) = 0)
    (h3 : edge b b c (c, 1, b) (c, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(4821092010900*b*c*z - 316770859140780*b*c - 9305620296225*b*z + 626995985258579*b - 9082997801100*c^2*z + 596800270669620*c^2 + 17181196657875*c*z - 1252135065480957*c + 1659852580125*z + 97365866635229)/24254248244664) * h0
    + (b*(b*(b*(b*(b*(z*(8548703812800*z - 672478150063656) - 16117278258306) + z*(1793564837492330 - 22796543500800*z) + 23568673964468) + z*(23553459984225*z - 1747406541156787) - 52743110062974) + z*(80188622744025*z - 6261367660470085) - 246009877835527) + c*(c*(c*(c*(c*(12940489816232 - 193180437276*z) + z*(5699135875200*z - 445952306352473) - 169265852421046) + z*(5480217475731326 - 69814414471200*z) + 914524072991535) + z*(372046713852900*z - 28885579323598276) - 2535755512353419) + z*(82191230723775025 - 1069166795087325*z) + 4487260585980791) + z*(232462409409525*z - 17837909226251272) - 963565388504579)/24254248244664 + c*(c*(9082997801100*z - 596800270669620) - 17229491767194*z + 1255370187935015)/24254248244664 + z*(1424783968800*z - 113739544257401)/24254248244664 - 9474728929202/3031781030583) * h1
    + (b*(b*(b*(b*(b*(c*(96590218638*z - 6470244908116) + z*(223869612698638 - 2849567937600*z) + 24783160810450) + c*(c*(c*(48295109319*z - 3235122454058) + z*(428271009506228 - 6245875979700*z) + 41507682491747) + z*(22675416119925*z - 1615037616730040) - 96995339609756) + z*(1411747007436787 - 19279108077825*z) + 5863001485125) + c*(c*(c*(c*(6470244908116 - 96590218638*z) + z*(16753657749600*z - 1136764610978572) - 70074875167262) + z*(4715158694598045 - 64065494131200*z) + 212245261109862) + z*(73937486798550*z - 5943367732714251) - 203953285932773) + z*(972989740664181 - 10285159274775*z) + 116954983745111) + c*(c*(c*(c*(c*(96590218638*z - 6470244908116) + z*(819848866509835 - 11932565738700*z) + 79780242529436) + z*(45130135929375*z - 3508850555078815) - 352943920855393) + z*(9549331963747260 - 117265084315650*z) + 791729991064450) + z*(201434093554875*z - 15573622415238965) - 977919270505896) + z*(10985369655172549 - 145506062813700*z) + 618306199403284) + c*(c*(c*(c*(c*(c*(3235122454058 - 48295109319*z) + z*(1424783968800*z - 111355265037491) - 51213049853921) + z*(1080000249541491 - 12288761730900*z) + 334689338965043) + z*(112474144502925*z - 8933063000339330) - 1185866021048519) + z*(35829645073395199 - 467067254738025*z) + 2502773141086697) + z*(584072378209950*z - 44560777905577172) - 2171785596671584) + z*(427479715139025*z - 32775181689770614) - 1688595672074596)/24254248244664 + c*(c*(c*(c*(3235122454058 - 48295109319*z) + z*(1424783968800*z - 109229400915173) - 190707750159152) + z*(1331663618743404 - 17097407625600*z) + 939970488853521) + z*(88024934572425*z - 6824557940036574) - 1053347095272940)/24254248244664 + z*(18740532674805455 - 243860681159925*z)/24254248244664 + 35305978468213/4042374707444) * h2
    + (-(-80357919*c*z + 5382899258*c + 2370688800*z^2 - 186488671676*z - 4469572451)/40356486264) * h3

private lemma rejectI_22_25 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (c, b, b) = 0) (h2 : locus b (c, c, b) = 0)
    (h3 : edge b b c (c, b, b) (c, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (z*(b*(b^2*(b*(2*b - 4) - 8) + 8) + c*(b*(b*(b*(48 - 20*b) + 51) - 47) + c*(b*(b*(b*(b*(12 - 2*b) + 45) - 187) + 54) + c*(b*(b*(b*(4*b - 38) + 79) - 65) + c*(b*(b*(b - 6) + 19) + c*(b*(6 - b) - c - 7) + 18) - 7) + 8)))) * h1
    + (z*(b*(b*(c*(c*(c*(c*(19 - 2*c) - 50) + 55) - 45) + 16) + c*(c*(c*(c*(c*(c - 6) - 15) + 70) - 45) + 23) - 8) + c^4*(c*(2*c - 5) + 1))) * h2
    + (z*(b*c - b - 2*c^2 + 5*c - 1)) * h3

private lemma rejectI_22_26 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (c, b, b) = 0) (h2 : locus b (c, c, c) = 0)
    (h3 : edge b b c (c, b, b) (c, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-6*b^2*c*z + 6*b^2*z + 6*b*c^2*z - 6*b*c*z - 1) * h0
    + (-c*z*(b*(3 - b) + c*(b*(b - 3) - 4) + z*(b*(b*(b*(6*b - 18) - 18) - 18) + c*(b*(b*(b*(30 - 12*b) + 78) + 24) + c*(b*(b*(b*(6*b - 6) - 108) + 12) + c*(b*(b*(54 - 6*b) - 24) + c*(b*(6 - 6*b) + 72) - 426) + 654) - 66) - 18) + 9)) * h1
    + (z*(6*b + c*z*(18*b + c*(300*b + c*(6*b + c*(-162*b + c*(60*b + c*(-6*b - 18) + 138) - 360) + 360) - 102) - 18) + c*(3*b + c*(-5*b + c*(b + 1) - 4) + 3))) * h2

private lemma rejectI_23_24 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (c, b, c) = 0) (h2 : locus b (c, c, 1) = 0)
    (h3 : edge b b c (c, b, c) (c, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(2*c - 1)*(1023286*c - 292541)/81) * h0
    + (b*(b*(b*(b*(b*(1334016 - 160256*b) - 3611136) + 3088128) - 7898607*z + 66048) - 43425936*z - 1069824)/2187 + c*(b*(b*(b*(b*(b*(1253888 - 160256*b) - 2823936) - 51324543*z - 258816) - 106581987*z + 2961408) + 1022459544*z + 18494052) + c*(b*(b*(b*(b*(80128*b - 626944) + 98683380*z + 2974464) + 106581987*z - 5605632) - 1432891863*z - 3342392) + c*(b*(b*(b*(320512*b - 55257444*z - 2668032) - 98683380*z + 5299200) + 935476452*z + 3892624) + c*(b*(b*(-320512*b + 55257444*z + 2587904) - 284185827*z - 4873952) + c*(b*(80128*b + 27628722*z - 1073600) + c*(40064*b - 193280) + 55257444*z + 3113856) - 347341878*z - 1978432) + 923644944*z - 5781536) - 1314478368*z - 1568912) + 971102196*z - 11383496)/2187 - 10673494*z/81 - 1709824/2187) * h1
    + (b*(b*(b*(b*(773120 - 160256*b) + 7898607*z - 184064) + 43425936*z - 674560) + c*(c*(c*(c*(c*(-40064*c - 27628722*z + 606912) + 339443271*z - 2282272) - 1310447052*z + 410480) + 2253920526*z + 5435448) - 1835655210*z - 21612644) + 288184338*z + 2082304)/2187 + c*(c*(c*(c*(c*(193280*c - 55257444*z - 2727296) + 236826990*z + 10814016) - 394733520*z - 13313504) + 288184338*z + 18440848) + 25370056)/2187 - 7670116/2187) * h2
    + (256*(313*b - 884)/2187) * h3

private lemma rejectI_25_26 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (c, c, b) = 0) (h2 : locus b (c, c, c) = 0)
    (h3 : edge b b c (c, c, b) (c, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0
    + (-b*z*(b*(b*(b + c - 4) - c^2 + 4) + c*(4*c - 17) + 4)) * h1
    + (z*(b^4 - 4*b^3 + 4*b^2 + 5*b*c^2 - 21*b*c + 4*b - c^3 + 4*c^2)) * h2

private lemma conflictI (b c z : ℝ) (i j : Fin 27)
    (h0 : invCondition b b c z = 0)
    (hi : locus b (profile b c i) = 0) (hj : locus b (profile b c j) = 0)
    (he : edge b b c (profile b c i) (profile b c j) = 0)
    (hlt : i < j) (hcol : colorsI i = colorsI j) : False := by
  fin_cases i
  · have possible : ∀ k : Fin 27, 0 < k → colorsI 0 = colorsI k → k = 8 ∨ k = 13 ∨ k = 14 ∨ k = 23 ∨ k = 24 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl | rfl | rfl
    · exact rejectI_0_8 b c z h0 hi hj he
    · exact rejectI_0_13 b c z h0 hi hj he
    · exact rejectI_0_14 b c z h0 hi hj he
    · exact rejectI_0_23 b c z h0 hi hj he
    · exact rejectI_0_24 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 1 < k → colorsI 1 = colorsI k → k = 4 ∨ k = 9 ∨ k = 12 ∨ k = 15 ∨ k = 18 ∨ k = 21 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl | rfl | rfl | rfl
    · exact rejectI_1_4 b c z h0 hi hj he
    · exact rejectI_1_9 b c z h0 hi hj he
    · exact rejectI_1_12 b c z h0 hi hj he
    · exact rejectI_1_15 b c z h0 hi hj he
    · exact rejectI_1_18 b c z h0 hi hj he
    · exact rejectI_1_21 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 2 < k → colorsI 2 = colorsI k → k = 5 ∨ k = 16 ∨ k = 19 ∨ k = 22 ∨ k = 25 ∨ k = 26 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl | rfl | rfl | rfl
    · exact rejectI_2_5 b c z h0 hi hj he
    · exact rejectI_2_16 b c z h0 hi hj he
    · exact rejectI_2_19 b c z h0 hi hj he
    · exact rejectI_2_22 b c z h0 hi hj he
    · exact rejectI_2_25 b c z h0 hi hj he
    · exact rejectI_2_26 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 3 < k → colorsI 3 = colorsI k → k = 6 ∨ k = 7 ∨ k = 10 ∨ k = 11 ∨ k = 17 ∨ k = 20 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl | rfl | rfl | rfl
    · exact rejectI_3_6 b c z h0 hi hj he
    · exact rejectI_3_7 b c z h0 hi hj he
    · exact rejectI_3_10 b c z h0 hi hj he
    · exact rejectI_3_11 b c z h0 hi hj he
    · exact rejectI_3_17 b c z h0 hi hj he
    · exact rejectI_3_20 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 4 < k → colorsI 4 = colorsI k → k = 9 ∨ k = 12 ∨ k = 15 ∨ k = 18 ∨ k = 21 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl | rfl | rfl
    · exact rejectI_4_9 b c z h0 hi hj he
    · exact rejectI_4_12 b c z h0 hi hj he
    · exact rejectI_4_15 b c z h0 hi hj he
    · exact rejectI_4_18 b c z h0 hi hj he
    · exact rejectI_4_21 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 5 < k → colorsI 5 = colorsI k → k = 16 ∨ k = 19 ∨ k = 22 ∨ k = 25 ∨ k = 26 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl | rfl | rfl
    · exact rejectI_5_16 b c z h0 hi hj he
    · exact rejectI_5_19 b c z h0 hi hj he
    · exact rejectI_5_22 b c z h0 hi hj he
    · exact rejectI_5_25 b c z h0 hi hj he
    · exact rejectI_5_26 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 6 < k → colorsI 6 = colorsI k → k = 7 ∨ k = 10 ∨ k = 11 ∨ k = 17 ∨ k = 20 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl | rfl | rfl
    · exact rejectI_6_7 b c z h0 hi hj he
    · exact rejectI_6_10 b c z h0 hi hj he
    · exact rejectI_6_11 b c z h0 hi hj he
    · exact rejectI_6_17 b c z h0 hi hj he
    · exact rejectI_6_20 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 7 < k → colorsI 7 = colorsI k → k = 10 ∨ k = 11 ∨ k = 17 ∨ k = 20 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl | rfl
    · exact rejectI_7_10 b c z h0 hi hj he
    · exact rejectI_7_11 b c z h0 hi hj he
    · exact rejectI_7_17 b c z h0 hi hj he
    · exact rejectI_7_20 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 8 < k → colorsI 8 = colorsI k → k = 13 ∨ k = 14 ∨ k = 23 ∨ k = 24 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl | rfl
    · exact rejectI_8_13 b c z h0 hi hj he
    · exact rejectI_8_14 b c z h0 hi hj he
    · exact rejectI_8_23 b c z h0 hi hj he
    · exact rejectI_8_24 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 9 < k → colorsI 9 = colorsI k → k = 12 ∨ k = 15 ∨ k = 18 ∨ k = 21 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl | rfl
    · exact rejectI_9_12 b c z h0 hi hj he
    · exact rejectI_9_15 b c z h0 hi hj he
    · exact rejectI_9_18 b c z h0 hi hj he
    · exact rejectI_9_21 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 10 < k → colorsI 10 = colorsI k → k = 11 ∨ k = 17 ∨ k = 20 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl
    · exact rejectI_10_11 b c z h0 hi hj he
    · exact rejectI_10_17 b c z h0 hi hj he
    · exact rejectI_10_20 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 11 < k → colorsI 11 = colorsI k → k = 17 ∨ k = 20 := by decide
    rcases possible j hlt hcol with rfl | rfl
    · exact rejectI_11_17 b c z h0 hi hj he
    · exact rejectI_11_20 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 12 < k → colorsI 12 = colorsI k → k = 15 ∨ k = 18 ∨ k = 21 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl
    · exact rejectI_12_15 b c z h0 hi hj he
    · exact rejectI_12_18 b c z h0 hi hj he
    · exact rejectI_12_21 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 13 < k → colorsI 13 = colorsI k → k = 14 ∨ k = 23 ∨ k = 24 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl
    · exact rejectI_13_14 b c z h0 hi hj he
    · exact rejectI_13_23 b c z h0 hi hj he
    · exact rejectI_13_24 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 14 < k → colorsI 14 = colorsI k → k = 23 ∨ k = 24 := by decide
    rcases possible j hlt hcol with rfl | rfl
    · exact rejectI_14_23 b c z h0 hi hj he
    · exact rejectI_14_24 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 15 < k → colorsI 15 = colorsI k → k = 18 ∨ k = 21 := by decide
    rcases possible j hlt hcol with rfl | rfl
    · exact rejectI_15_18 b c z h0 hi hj he
    · exact rejectI_15_21 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 16 < k → colorsI 16 = colorsI k → k = 19 ∨ k = 22 ∨ k = 25 ∨ k = 26 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl | rfl
    · exact rejectI_16_19 b c z h0 hi hj he
    · exact rejectI_16_22 b c z h0 hi hj he
    · exact rejectI_16_25 b c z h0 hi hj he
    · exact rejectI_16_26 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 17 < k → colorsI 17 = colorsI k → k = 20 := by decide
    rcases possible j hlt hcol with rfl
    exact rejectI_17_20 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 18 < k → colorsI 18 = colorsI k → k = 21 := by decide
    rcases possible j hlt hcol with rfl
    exact rejectI_18_21 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 19 < k → colorsI 19 = colorsI k → k = 22 ∨ k = 25 ∨ k = 26 := by decide
    rcases possible j hlt hcol with rfl | rfl | rfl
    · exact rejectI_19_22 b c z h0 hi hj he
    · exact rejectI_19_25 b c z h0 hi hj he
    · exact rejectI_19_26 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 20 < k → colorsI 20 = colorsI k → False := by decide
    exact possible j hlt hcol
  · have possible : ∀ k : Fin 27, 21 < k → colorsI 21 = colorsI k → False := by decide
    exact possible j hlt hcol
  · have possible : ∀ k : Fin 27, 22 < k → colorsI 22 = colorsI k → k = 25 ∨ k = 26 := by decide
    rcases possible j hlt hcol with rfl | rfl
    · exact rejectI_22_25 b c z h0 hi hj he
    · exact rejectI_22_26 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 23 < k → colorsI 23 = colorsI k → k = 24 := by decide
    rcases possible j hlt hcol with rfl
    exact rejectI_23_24 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 24 < k → colorsI 24 = colorsI k → False := by decide
    exact possible j hlt hcol
  · have possible : ∀ k : Fin 27, 25 < k → colorsI 25 = colorsI k → k = 26 := by decide
    rcases possible j hlt hcol with rfl
    exact rejectI_25_26 b c z h0 hi hj he
  · have possible : ∀ k : Fin 27, 26 < k → colorsI 26 = colorsI k → False := by decide
    exact possible j hlt hcol

private def squared (x y : ℝ × ℝ) := (x.1-y.1)^2 + (x.2-y.2)^2
private def len (x : ℝ × ℝ) := x.1^2 + x.2^2
private def dot (x y : ℝ × ℝ) := x.1*y.1 + x.2*y.2
private noncomputable def coords (o : ℝ²) (r : ℝ) (x : ℝ²) : ℝ × ℝ :=
  ((x 0-o 0)/r, (x 1-o 1)/r)

private lemma coords_sq (o x y : ℝ²) (r : ℝ) :
    squared (coords o r x) (coords o r y) = dist x y ^ 2 / r^2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  simp only [Real.dist_eq, sq_abs, squared, coords, div_eq_mul_inv]
  ring

private lemma coords_len (o x : ℝ²) (r : ℝ) :
    len (coords o r x) = dist x o ^ 2 / r^2 := by
  simpa [squared, coords, len] using coords_sq o x o r

private lemma squared_pos (o x y : ℝ²) {r : ℝ} (hr : 0 < r) (hne : x ≠ y) :
    0 < squared (coords o r x) (coords o r y) := by
  rw [coords_sq]
  exact div_pos (sq_pos_of_pos (dist_pos.mpr hne)) (sq_pos_of_pos hr)

private lemma squared_symm (x y : ℝ × ℝ) : squared x y = squared y x := by
  simp only [squared]
  ring

private lemma antipodal (e f : ℝ × ℝ) (he : len e = 1) (hf : len f = 1)
    (h : squared e f = 4) : f = (-e.1, -e.2) := by
  have hz : (e.1+f.1)^2 + (e.2+f.2)^2 = 0 := by
    unfold squared at h
    unfold len at he hf
    linear_combination 2*he + 2*hf - h
  exact Prod.ext (by dsimp; nlinarith [sq_nonneg (e.2+f.2), sq_nonneg (e.1+f.1)])
    (by dsimp; nlinarith [sq_nonneg (e.1+f.1), sq_nonneg (e.2+f.2)])

private def geometric (e f x : ℝ × ℝ) := (len x, squared x e, squared x f)

private lemma geom_u (e f x : ℝ × ℝ) (he : len e = 1) :
    u (geometric e f x) = 2 * dot e x := by
  simp only [u, geometric, squared, len, dot]
  unfold len at he
  linear_combination -he

private lemma geom_v (e f x : ℝ × ℝ) (hf : len f = 1) :
    v (geometric e f x) = 2 * dot f x := by
  simp only [v, geometric, squared, len, dot]
  unfold len at hf
  linear_combination -hf

private lemma basis_t (e f : ℝ × ℝ) (he : len e = 1) (hf : len f = 1) :
    squared e f = 2 - 2*dot e f := by
  simp only [squared, dot]
  unfold len at he hf
  linear_combination he + hf

private lemma gram (e f w : ℝ × ℝ) (he : len e = 1) (hf : len f = 1) :
    quad (squared e f) (2*dot e w) (2*dot f w) = delta (squared e f) * len w := by
  have h : len f * (dot e w)^2 + len e * (dot f w)^2 - 2*dot e f*dot e w*dot f w =
      (len e * len f - (dot e f)^2) * len w := by
    unfold len dot
    ring
  rw [he, hf] at h
  rw [basis_t e f he hf]
  unfold quad delta
  linear_combination 4*h

private lemma geom_locus (e f x : ℝ × ℝ) (he : len e = 1) (hf : len f = 1) :
    locus (squared e f) (geometric e f x) = 0 := by
  unfold locus
  rw [geom_u _ _ _ he, geom_v _ _ _ hf, gram _ _ _ he hf]
  exact sub_self _

private lemma geom_sep (e f x y : ℝ × ℝ) (he : len e = 1) (hf : len f = 1) :
    sep (squared e f) (geometric e f x) (geometric e f y) =
    delta (squared e f) * squared x y := by
  let w : ℝ × ℝ := (x.1-y.1,x.2-y.2)
  have hd (a : ℝ × ℝ) : 2*dot a x - 2*dot a y = 2*dot a w := by
    simp only [dot,w]
    ring
  unfold sep
  rw [geom_u _ _ _ he, geom_u _ _ _ he, geom_v _ _ _ hf, geom_v _ _ _ hf,
    hd, hd, gram _ _ _ he hf]
  rfl

private lemma pad_distances (D : Finset ℝ) (hcard : D.card ≤ 3) (h1 : 1 ∈ D)
    (h0 : 0 ∉ D) : ∃ b c : ℝ, b ≠ 0 ∧ c ≠ 0 ∧ b ≠ 1 ∧ c ≠ 1 ∧ b ≠ c ∧
      ∀ d ∈ D, d = 1 ∨ d = b ∨ d = c := by
  classical
  obtain ⟨T, hT, hfour⟩ := Infinite.exists_superset_card_eq (insert 0 D) 4
    (by rw [Finset.card_insert_of_notMem h0]; omega)
  have z : (0:ℝ) ∈ T := hT (by simp)
  have one : (1:ℝ) ∈ T.erase 0 := Finset.mem_erase.mpr ⟨one_ne_zero, hT (by simp [h1])⟩
  have two : ((T.erase 0).erase 1).card = 2 := by
    rw [Finset.card_erase_of_mem one, Finset.card_erase_of_mem z, hfour]
  obtain ⟨b,c,hbc,hs⟩ := Finset.card_eq_two.mp two
  have hb : b ∈ (T.erase 0).erase 1 := by simp [hs]
  have hc : c ∈ (T.erase 0).erase 1 := by simp [hs]
  simp only [Finset.mem_erase] at hb hc
  refine ⟨b,c,hb.2.1,hc.2.1,hb.1,hc.1,hbc,?_⟩
  intro d hd
  by_cases h : d = 1
  · exact Or.inl h
  right
  have hmem : d ∈ (T.erase 0).erase 1 :=
    Finset.mem_erase.mpr ⟨h, Finset.mem_erase.mpr ⟨fun e => h0 (e ▸ hd), hT (Finset.mem_insert_of_mem hd)⟩⟩
  simpa [hs] using hmem

private def inPalette (b c x : ℝ) : Prop := x = 1 ∨ x = b ∨ x = c

private lemma profile_exists (b c x y z : ℝ)
    (hx : inPalette b c x) (hy : inPalette b c y) (hz : inPalette b c z) :
    ∃ i : Fin 27, profile b c i = (x,y,z) := by
  have index (w : ℝ) (hw : inPalette b c w) : ∃ i : Fin 3, palette b c i.val = w := by
    rcases hw with rfl | rfl | rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
  obtain ⟨i, rfl⟩ := index x hx
  obtain ⟨j, rfl⟩ := index y hy
  obtain ⟨k, rfl⟩ := index z hz
  have pack : ∀ i j k : Fin 3, ∃ n : Fin 27,
      n.val / 9 = i.val ∧ n.val / 3 % 3 = j.val ∧ n.val % 3 = k.val := by decide
  obtain ⟨n,h1,h2,h3⟩ := pack i j k
  exact ⟨n, by simp only [profile,h1,h2,h3]⟩

private lemma color_bound (R : Finset ℝ²) (X : ℝ² → ℝ × ℝ) (e f : ℝ × ℝ)
    (he : len e = 1) (hf : len f = 1) (b c : ℝ) (hd : delta (squared e f) ≠ 0)
    (col : Fin 27 → Fin 4)
    (conflict : ∀ i j : Fin 27, locus (squared e f) (profile b c i) = 0 →
      locus (squared e f) (profile b c j) = 0 →
      edge (squared e f) b c (profile b c i) (profile b c j) = 0 →
      i < j → col i = col j → False)
    (mem : ∀ x ∈ R, inPalette b c (len (X x)) ∧
      inPalette b c (squared (X x) e) ∧ inPalette b c (squared (X x) f))
    (pairs : ∀ x ∈ R, ∀ y ∈ R, x ≠ y →
      squared (X x) (X y) ≠ 0 ∧ inPalette b c (squared (X x) (X y))) : R.card ≤ 4 := by
  classical
  have codes (x : R) : ∃ i : Fin 27, profile b c i = geometric e f (X x) := by
    obtain ⟨h1,h2,h3⟩ := mem x x.property
    exact profile_exists b c _ _ _ h1 h2 h3
  choose idx eqn using codes
  have loc (x : R) : locus (squared e f) (profile b c (idx x)) = 0 := by
    rw [eqn]; exact geom_locus _ _ _ he hf
  have no_lt (x y : R) (ne : x ≠ y) (lt : idx x < idx y) (co : col (idx x) = col (idx y)) : False := by
    apply conflict _ _ (loc x) (loc y) _ lt co
    obtain ⟨_,ds⟩ := pairs x x.property y y.property (fun h => ne (Subtype.ext h))
    rw [eqn,eqn]
    unfold edge
    rw [geom_sep _ _ _ _ he hf]
    rcases ds with d | d | d <;> rw [d] <;> ring
  have inj : Function.Injective (fun x : R => col (idx x)) := by
    intro x y hcol
    by_contra hne
    rcases lt_trichotomy (idx x) (idx y) with h | h | h
    · exact no_lt x y hne h hcol
    · have hp := (eqn x).symm.trans ((congrArg (profile b c) h).trans (eqn y))
      have hs := geom_sep e f (X x) (X y) he hf
      rw [hp] at hs
      simp [sep,quad] at hs
      exact hs.elim hd (pairs x x.property y y.property (fun h => hne (Subtype.ext h))).1
    · exact no_lt y x (Ne.symm hne) h hcol.symm
  simpa using Fintype.card_le_of_injective _ inj

private lemma radius_anchors (S : Finset ℝ²) (hS : S.card = 8)
    (hD : (distanceSet S).card ≤ 3) (o : ℝ²) (ho : o ∈ S) :
    ∃ (r : ℝ) (a b : ℝ²), 0 < r ∧ a ∈ S ∧ b ∈ S ∧
      a ≠ o ∧ b ≠ o ∧ a ≠ b ∧
      len (coords o r a) = 1 ∧ len (coords o r b) = 1 ∧
      squared (coords o r a) (coords o r b) ≠ 4 := by
  classical
  have maps (x : ℝ²) (hx : x ∈ S.erase o) : dist x o ∈ distanceSet S := by
    obtain ⟨hne,hx⟩ := Finset.mem_erase.mp hx
    exact Finset.mem_image.mpr ⟨(x,o),Finset.mem_offDiag.mpr ⟨hx,ho,hne⟩,rfl⟩
  have hlt : (distanceSet S).card * 2 < (S.erase o).card := by
    rw [Finset.card_erase_of_mem ho,hS]; omega
  obtain ⟨r,_,hr⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to maps hlt
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := Finset.two_lt_card_iff.mp hr
  simp only [Finset.mem_filter,Finset.mem_erase] at ha hb hc
  have rp : 0 < r := ha.2 ▸ dist_pos.mpr ha.1.1
  have normalized (x : ℝ²) (hx : dist x o = r) : len (coords o r x) = 1 := by
    rw [coords_len,hx,div_self (pow_ne_zero _ rp.ne')]
  refine ⟨r,a,?_⟩
  by_cases h : squared (coords o r a) (coords o r b) = 4
  · refine ⟨c,rp,ha.1.2,hc.1.2,ha.1.1,hc.1.1,hac,normalized a ha.2,normalized c hc.2,?_⟩
    intro hc4
    have eq := (antipodal _ _ (normalized a ha.2) (normalized b hb.2) h).trans
      (antipodal _ _ (normalized a ha.2) (normalized c hc.2) hc4).symm
    have pos := squared_pos o b c rp hbc
    rw [eq] at pos
    simpa [squared] using pos
  · exact ⟨b,rp,ha.1.2,hb.1.2,ha.1.1,hb.1.1,hab,normalized a ha.2,normalized b hb.2,h⟩

private def validColoring (t b c : ℝ) (col : Fin 27 → Fin 4) : Prop :=
  ∀ i j : Fin 27, locus t (profile b c i) = 0 → locus t (profile b c j) = 0 →
    edge t b c (profile b c i) (profile b c j) = 0 → i < j → col i = col j → False

private lemma lower_from_colors
    (colorings : ∀ t b c z : ℝ, (t = 1 ∨ t = b) → invCondition t b c z = 0 →
      ∃ col, validColoring t b c col)
    (S : Finset ℝ²) (hS : S.card = 8) : 4 ≤ distinctDistances S := by
  classical
  by_contra! h
  have hD : (distanceSet S).card ≤ 3 := by change distinctDistances S ≤ 3; omega
  obtain ⟨o,ho⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  obtain ⟨r,a,f,hr,ha,hf,hao,hfo,haf,unitA,unitF,notFour⟩ :=
    radius_anchors S hS hD o ho
  let X := coords o r
  let t := squared (X a) (X f)
  have ht : t ≠ 0 := (squared_pos o a f hr haf).ne'
  have hd : delta t ≠ 0 := mul_ne_zero ht (sub_ne_zero.mpr (Ne.symm notFour))
  let D := (distanceSet S).image (fun d : ℝ => d^2 / r^2)
  have inD (x : ℝ²) (hx : x ∈ S) (y : ℝ²) (hy : y ∈ S) (hne : x ≠ y) :
      squared (X x) (X y) ∈ D := by
    refine Finset.mem_image.mpr ⟨dist x y,Finset.mem_image.mpr
      ⟨(x,y),Finset.mem_offDiag.mpr ⟨hx,hy,hne⟩,rfl⟩,(coords_sq _ _ _ _).symm⟩
  have origin (x : ℝ²) : squared (X x) (X o) = len (X x) := by
    simp only [X,coords_sq,coords_len]
  have one : 1 ∈ D := by
    have hh := inD a ha o ho hao
    rwa [origin,unitA] at hh
  have zero : 0 ∉ D := by
    intro hz
    obtain ⟨d,hm,eq⟩ := Finset.mem_image.mp hz
    obtain ⟨⟨x,y⟩,hp,rfl⟩ := Finset.mem_image.mp hm
    have ne := (Finset.mem_offDiag.mp hp).2.2
    exact (div_pos (sq_pos_of_pos (dist_pos.mpr ne)) (sq_pos_of_pos hr)).ne' eq
  obtain ⟨b,c,b0,c0,b1,c1,bc,cover⟩ := pad_distances D (Finset.card_image_le.trans hD) one zero
  have tmem := cover t (inD a ha f hf haf)
  have oriented : ∃ b c : ℝ, b ≠ 0 ∧ c ≠ 0 ∧ b ≠ 1 ∧ c ≠ 1 ∧ b ≠ c ∧
      (t = 1 ∨ t = b) ∧ ∀ d ∈ D, inPalette b c d := by
    rcases tmem with e | e | e
    · exact ⟨b,c,b0,c0,b1,c1,bc,Or.inl e,cover⟩
    · exact ⟨b,c,b0,c0,b1,c1,bc,Or.inr e,cover⟩
    · refine ⟨c,b,c0,b0,c1,b1,bc.symm,Or.inr e,?_⟩
      intro d hmem
      rcases cover d hmem with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
  obtain ⟨B,C,B0,C0,B1,C1,BC,shape,pal⟩ := oriented
  let factor := B*C*(B-1)*(C-1)*(B-C)*delta t
  have nonzero : factor ≠ 0 := by
    dsimp [factor]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero B0 C0)
      (sub_ne_zero.mpr B1)) (sub_ne_zero.mpr C1)) (sub_ne_zero.mpr BC)) hd
  have inv : invCondition t B C factor⁻¹ = 0 := by
    unfold invCondition
    rw [show factor⁻¹*B*C*(B-1)*(C-1)*(B-C)*delta t = factor⁻¹*factor by dsimp [factor]; ring]
    rw [inv_mul_cancel₀ nonzero, sub_self]
  obtain ⟨col,hcol⟩ := colorings t B C factor⁻¹ shape inv
  let R := ((S.erase o).erase a).erase f
  have rem (x : ℝ²) (hx : x ∈ R) : x ≠ f ∧ x ≠ a ∧ x ≠ o ∧ x ∈ S := by
    simpa only [R,Finset.mem_erase] using hx
  have amem : a ∈ S.erase o := Finset.mem_erase.mpr ⟨hao,ha⟩
  have fmem : f ∈ (S.erase o).erase a :=
    Finset.mem_erase.mpr ⟨haf.symm, Finset.mem_erase.mpr ⟨hfo,hf⟩⟩
  have size : R.card = 5 := by
    simp only [R,Finset.card_erase_of_mem fmem,Finset.card_erase_of_mem amem,
      Finset.card_erase_of_mem ho,hS]
  have bound := color_bound R X (X a) (X f) unitA unitF B C hd col hcol (by
    intro x hx
    obtain ⟨xf,xa,xo,xS⟩ := rem x hx
    refine ⟨?_,pal _ (inD x xS a ha xa),pal _ (inD x xS f hf xf)⟩
    rw [← origin]
    exact pal _ (inD x xS o ho xo)) (by
    intro x hx y hy ne
    exact ⟨(squared_pos o x y hr ne).ne',pal _ (inD x (rem x hx).2.2.2 y (rem y hy).2.2.2 ne)⟩)
  omega
lemma eight_lower (S : Finset ℝ²) (hs : S.card = 8) : 4 ≤ distinctDistances S := by
  apply lower_from_colors _ S hs
  intro t b c z shape inv
  rcases shape with eq | eq
  · subst t
    exact ⟨colorsE, fun i j => conflictE b c z i j inv⟩
  · subst t
    exact ⟨colorsI, fun i j => conflictI b c z i j inv⟩

end OMA.EightDistances

namespace OMA.Erdos91Eight

open EuclideanGeometry Finset Erdos91

private def firstPoints : Finset (ℤ × ℤ) :=
  {(-1, 0), (-1, 1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 1), (2, -1)}

private def secondPoints : Finset (ℤ × ℤ) :=
  {(-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0)}

private noncomputable def point (p : ℤ × ℤ) : ℝ² :=
  !₂[(p.1 : ℝ) + (p.2 : ℝ) / 2, (p.2 : ℝ) * Real.sqrt 3 / 2]

private noncomputable def lattice : (ℤ × ℤ) ↪ ℝ² where
  toFun := point
  inj' := by
    intro p q h
    have hx := congrArg (fun x : ℝ² => x 0) h
    have hy := congrArg (fun x : ℝ² => x 1) h
    simp only [point, Matrix.cons_val_zero, Matrix.cons_val_one] at hx hy
    have hp : (p.2 : ℝ) = q.2 := by
      apply mul_right_cancel₀ (by positivity : Real.sqrt (3 : ℝ) ≠ 0)
      linarith
    exact Prod.ext (by exact_mod_cast (show (p.1 : ℝ) = q.1 by linarith)) (by exact_mod_cast hp)

private def squareDistance (p q : ℤ × ℤ) : ℤ :=
  let x := p.1 - q.1
  let y := p.2 - q.2
  x ^ 2 + x * y + y ^ 2

private theorem lattice_square (p q : ℤ × ℤ) :
    dist (lattice p) (lattice q) ^ 2 = (squareDistance p q : ℝ) := by
  change dist (point p) (point q) ^ 2 = _
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  simp only [point, Matrix.cons_val_zero, Matrix.cons_val_one, Real.dist_eq, sq_abs,
    squareDistance, Int.cast_add, Int.cast_sub, Int.cast_pow, Int.cast_mul]
  calc
    _ = ((p.1 : ℝ) - q.1 + ((p.2 : ℝ) - q.2) / 2) ^ 2 +
        ((p.2 : ℝ) - q.2) ^ 2 * (Real.sqrt 3) ^ 2 / 4 := by ring
    _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; ring

private def squaredValues : Finset ℤ := {1, 3, 4, 7}

private theorem first_values :
    firstPoints.offDiag.image (fun p => squareDistance p.1 p.2) = squaredValues := by decide

private theorem second_values :
    secondPoints.offDiag.image (fun p => squareDistance p.1 p.2) = squaredValues := by decide

private theorem offDiag_map {α β : Type} (e : α ↪ β) (S : Finset α) :
    (S.map e).offDiag = S.offDiag.map (e.prodMap e) := by
  ext p
  rcases p with ⟨p, q⟩
  simp only [mem_offDiag, mem_map]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩, hxy⟩
    exact ⟨(x, y), ⟨hx, hy, fun h => hxy (congrArg e h)⟩, rfl⟩
  · rintro ⟨⟨x, y⟩, ⟨hx, hy, hxy⟩, h⟩
    have h' : (e x, e y) = (p, q) := h
    cases h'
    exact ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩, fun he => hxy (e.injective he)⟩

private theorem distances_le_four (S : Finset (ℤ × ℤ))
    (hc : S.offDiag.image (fun p => squareDistance p.1 p.2) = squaredValues) :
    distinctDistances (S.map lattice) ≤ 4 := by
  classical
  unfold distinctDistances distanceSet
  apply le_trans (card_le_card (t := squaredValues.image (fun z : ℤ => Real.sqrt (z : ℝ))) ?_)
    ((card_image_le).trans (by decide))
  intro d hd
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hd
  rw [offDiag_map] at hp
  obtain ⟨q, hq, rfl⟩ := mem_map.mp hp
  refine mem_image.mpr ⟨squareDistance q.1 q.2, ?_, ?_⟩
  · rw [← hc]
    exact mem_image.mpr ⟨q, hq, rfl⟩
  · change Real.sqrt (squareDistance q.1 q.2 : ℝ) = dist (lattice q.1) (lattice q.2)
    rw [← lattice_square, Real.sqrt_sq dist_nonneg]

private theorem unit_minimum (S : Finset (ℤ × ℤ))
    (hc : S.offDiag.image (fun p => squareDistance p.1 p.2) = squaredValues) :
    (∀ z ∈ (S.map lattice).offDiag, (1 : ℝ) ≤ dist z.1 z.2 ^ 2) ∧
      ∃ z ∈ (S.map lattice).offDiag, dist z.1 z.2 ^ 2 = (1 : ℝ) := by
  rw [offDiag_map]
  constructor
  · intro z hz
    obtain ⟨q, hq, rfl⟩ := mem_map.mp hz
    change (1 : ℝ) ≤ dist (lattice q.1) (lattice q.2) ^ 2
    rw [lattice_square]
    have h : squareDistance q.1 q.2 ∈ squaredValues := by
      rw [← hc]
      exact mem_image.mpr ⟨q, hq, rfl⟩
    simp only [squaredValues, mem_insert, mem_singleton] at h
    rcases h with h | h | h | h <;> rw [h] <;> norm_num
  · have h : (1 : ℤ) ∈ S.offDiag.image (fun p => squareDistance p.1 p.2) := by
      rw [hc]
      decide
    obtain ⟨q, hq, h1⟩ := mem_image.mp h
    refine ⟨(lattice.prodMap lattice) q, mem_map.mpr ⟨q, hq, rfl⟩, ?_⟩
    change dist (lattice q.1) (lattice q.2) ^ 2 = 1
    rw [lattice_square, h1, Int.cast_one]

private noncomputable def unitCount (S : Finset ℝ²) : ℕ :=
  S.offDiag.filter (fun z => dist z.1 z.2 ^ 2 = (1 : ℝ)) |>.card

private theorem unitCount_lattice (S : Finset (ℤ × ℤ)) :
    unitCount (S.map lattice) = (S.offDiag.filter fun z => squareDistance z.1 z.2 = 1).card := by
  classical
  rw [unitCount, offDiag_map, filter_map, card_map]
  congr 1
  ext z
  simp only [mem_filter, Function.comp_apply]
  change (z ∈ S.offDiag ∧ dist (lattice z.1) (lattice z.2) ^ 2 = 1) ↔
    z ∈ S.offDiag ∧ squareDistance z.1 z.2 = 1
  rw [lattice_square, ← Int.cast_one (R := ℝ), Int.cast_inj]

private theorem first_units : (firstPoints.offDiag.filter
    fun z => squareDistance z.1 z.2 = 1).card = 20 := by decide

private theorem second_units : (secondPoints.offDiag.filter
    fun z => squareDistance z.1 z.2 = 1).card = 28 := by decide

private theorem unitCount_invariant (A B : Finset ℝ²)
    (hA : (∀ z ∈ A.offDiag, (1 : ℝ) ≤ dist z.1 z.2 ^ 2) ∧
      ∃ z ∈ A.offDiag, dist z.1 z.2 ^ 2 = (1 : ℝ))
    (hB : (∀ z ∈ B.offDiag, (1 : ℝ) ≤ dist z.1 z.2 ^ 2) ∧
      ∃ z ∈ B.offDiag, dist z.1 z.2 ^ 2 = (1 : ℝ))
    (hs : DilationEquivSimilar A B) : unitCount A = unitCount B := by
  classical
  obtain ⟨f, hf⟩ := hs
  let e : ℝ² ↪ ℝ² := ⟨f, f.injective⟩
  have hmap : A.map e = B := by
    ext p
    rw [mem_map]
    change (∃ q ∈ (A : Set ℝ²), f q = p) ↔ p ∈ (B : Set ℝ²)
    rw [← hf]
    rfl
  have hpair : A.offDiag.map (e.prodMap e) = B.offDiag :=
    (offDiag_map e A).symm.trans (congrArg Finset.offDiag hmap)
  have hsquare (z : ℝ² × ℝ²) :
      dist ((e.prodMap e) z).1 ((e.prodMap e) z).2 ^ 2 =
        (Dilation.ratio f : ℝ) ^ 2 * dist z.1 z.2 ^ 2 := by
    change dist (f z.1) (f z.2) ^ 2 = _
    rw [Dilation.dist_eq, mul_pow]
  have hratio : (Dilation.ratio f : ℝ) ^ 2 = 1 := by
    apply le_antisymm
    · obtain ⟨z, hz, hd⟩ := hB.2
      rw [← hpair] at hz
      obtain ⟨u, hu, rfl⟩ := mem_map.mp hz
      rw [hsquare] at hd
      calc
        (Dilation.ratio f : ℝ) ^ 2 = (Dilation.ratio f : ℝ) ^ 2 * 1 := by ring
        _ ≤ (Dilation.ratio f : ℝ) ^ 2 * dist u.1 u.2 ^ 2 :=
          mul_le_mul_of_nonneg_left (hA.1 u hu) (sq_nonneg _)
        _ = 1 := hd
    · obtain ⟨z, hz, hd⟩ := hA.2
      have hzB : (e.prodMap e) z ∈ B.offDiag := by
        rw [← hpair]
        exact mem_map.mpr ⟨z, hz, rfl⟩
      have hh := hB.1 _ hzB
      rwa [hsquare, hd, mul_one] at hh
  unfold unitCount
  rw [← hpair, filter_map, card_map]
  congr 1
  ext z
  simp only [mem_filter, Function.comp_apply, hsquare, hratio, one_mul]

theorem witnesses :
    ∃ A B : Finset ℝ², A.card = 8 ∧ B.card = 8 ∧
      distinctDistances A ≤ 4 ∧ distinctDistances B ≤ 4 ∧ ¬DilationEquivSimilar A B := by
  refine ⟨firstPoints.map lattice, secondPoints.map lattice, ?_, ?_,
    distances_le_four _ first_values, distances_le_four _ second_values, ?_⟩
  · rw [card_map]
    decide
  · rw [card_map]
    decide
  · intro h
    have hc := unitCount_invariant _ _ (unit_minimum _ first_values) (unit_minimum _ second_values) h
    rw [unitCount_lattice, unitCount_lattice, first_units, second_units] at hc
    omega

end OMA.Erdos91Eight

section
open EuclideanGeometry Erdos91

theorem OMA.solution : type_of% @Erdos91.erdos_91.variants.eight := by
  intro h
  have hbound := OMA.EightDistances.eight_lower
  obtain ⟨A, B, hA, hB, hdistA, hdistB, hnonsim⟩ := OMA.Erdos91Eight.witnesses
  have heA := le_antisymm hdistA (hbound A hA)
  have heB := le_antisymm hdistB (hbound B hB)
  have hmin : minimalDistinctDistances ℝ² 8 = 4 := by
    unfold minimalDistinctDistances
    apply le_antisymm
    · exact Nat.sInf_le ⟨A, hA, heA⟩
    · apply le_csInf
      · exact ⟨4, A, hA, heA⟩
      rintro d ⟨S, hS, hd⟩
      exact hd ▸ hbound S hS
  exact hnonsim (h A B ⟨hA, heA.trans hmin.symm⟩ ⟨hB, heB.trans hmin.symm⟩)

end

