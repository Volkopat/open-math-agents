import OMAReductions.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H4_R1

/-!
# The small-distance cases of Erdős problem 1082(i)

The eight-point argument and its checked polynomial certificates are from the merged proof
of Erdős 91, eight-point variant, reduction 1, hypothesis 1 (upstream pull request 1829).
An isosceles triangle also gives eight squared-distance profiles in the two-distance case.
The univariate identities below color those profiles with two colors, ruling out six points.
For four points a single equilateral-triangle identity rules out one distance.
-/

namespace OMA.EightDistances

open EuclideanGeometry

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
  linear_combination (-1) * h0 + (z*(27*b^4*c - 27*b^4 - 108*b^3*c + 108*b^3 + 27*b^2*c^3 - 108*b^2*c^2 + 270*b^2*c - 189*b^2 - b*c^4 - 47*b*c^3 + 270*b*c^2 - 251*b*c + 164*b + 9*c^5 - 54*c^4 + 81*c^3 - 117*c^2 + 135*c - 54)/27) * h1 + (z*(b*c^4 + 2*b*c^3 - 100*b*c - 38*b + c^5 - 8*c^4 + 25*c^3 - 46*c^2 + 44*c - 16)/27) * h2 + (-z*(c - 1)/27) * h3

private lemma rejectE_1_20 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, 1, b) = 0) (h2 : locus 1 (c, 1, c) = 0)
    (h3 : edge 1 b c (1, 1, b) (c, 1, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (z*(8*b^4*c - 4*b^4 - 24*b^3*c^2 - 12*b^3*c + 12*b^3 + 48*b^2*c^3 - 48*b^2*c^2 + 12*b^2*c - 56*b*c^4 + 124*b*c^3 + 51*b*c^2 - 71*b*c + 4*b + 48*c^5 - 240*c^4 + 297*c^3 + 21*c^2 - 150*c + 36)/9) * h1 + (-2*z*(12*b*c^4 - 54*b*c^3 + 72*b*c^2 + 3*b*c - 36*b - 4*c^5 + 10*c^4 - 4*c^3 - 4*c^2 + 10*c - 4)/9) * h2 + (-4*z*(2*c - 1)/9) * h3

private lemma rejectE_1_22 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, 1, b) = 0) (h2 : locus 1 (c, b, b) = 0)
    (h3 : edge 1 b c (1, 1, b) (c, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (z*(5*b^4*c - 7*b^4 - 15*b^3*c^2 + 6*b^3*c + 21*b^3 + 30*b^2*c^3 - 57*b^2*c^2 + 21*b^2*c - 30*b*c^4 + 72*b*c^3 + 60*b*c^2 - 108*b*c - 21*b + 15*c^5 - 66*c^4 + 66*c^3 + 6*c^2 - 39*c + 21)/9) * h1 + (-z*(5*b*c^4 - 37*b*c^3 + 72*b*c^2 - 13*b*c - 28*b - 5*c^5 + 32*c^4 - 50*c^3 - 14*c^2 + 59*c - 14)/9) * h2 + (-z*(5*c - 7)/9) * h3

private lemma rejectE_1_23 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, 1, b) = 0) (h2 : locus 1 (c, b, c) = 0)
    (h3 : edge 1 b c (1, 1, b) (c, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-z*(1512*b^4*c - 1512*b^4 - 4536*b^3*c^2 + 3024*b^3*c + 1512*b^3 + 6048*b^2*c^3 - 7560*b^2*c^2 + 4536*b^2*c - 3024*b^2 - 4144*b*c^4 + 9856*b*c^3 - 10665*b*c^2 + 4063*b*c + 1592*b + 1176*c^5 - 5376*c^4 + 11841*c^3 - 14703*c^2 + 9534*c - 2472)/27) * h1 + (2*z*(196*b*c^4 - 1372*b*c^3 + 4536*b*c^2 - 7081*b*c + 4072*b - 28*c^5 - 28*c^4 + 56*c^3 + 28*c^2 + 28*c - 56)/27) * h2 + (56*z*(c - 1)/27) * h3

private lemma rejectE_2_4 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, 1, c) = 0) (h2 : locus 1 (1, b, b) = 0)
    (h3 : edge 1 b c (1, 1, c) (1, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (z*(64*b*c^4 - 612*b*c^3 + 2124*b*c^2 - 3393*b*c + 2043*b - 24*c^5 + 148*c^4 - 108*c^3 - 648*c^2 + 1215*c - 603)/9) * h1 + (-z*(8*b^5 - 92*b^4 - 24*b^3*c^2 + 132*b^3*c + 152*b^3 + 88*b^2*c^3 - 456*b^2*c^2 + 432*b^2*c + 8*b^2 - 120*b*c^4 + 692*b*c^3 - 1011*b*c^2 + 63*b*c - 92*b + 120*c^5 - 1032*c^4 + 3091*c^3 - 3576*c^2 + 1077*c + 152)/9) * h2 + (4*z*(2*b + 6*c - 19)/9) * h3

private lemma rejectE_2_15 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, 1, c) = 0) (h2 : locus 1 (b, c, 1) = 0)
    (h3 : edge 1 b c (1, 1, c) (b, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-z*(b*c^4 + 57*b*c^3 - 54*b - 19*c^5 + 80*c^4 - 180*c^3 + 252*c^2 - 189*c + 54)/27) * h1 + (-z*(b^5 - 5*b^4 + 8*b^3*c^2 - 15*b^3*c + 4*b^3 - b^2*c^3 - 9*b^2*c^2 + 18*b^2*c + 8*b^2 + 18*b*c^4 - 52*b*c^3 - 90*b*c^2 + 180*b*c - 40*b - 8*c^5 + 90*c^4 - 283*c^3 + 271*c^2 - 102*c + 32)/27) * h2 + (z*(b - c + 2)/27) * h3

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
  linear_combination (-1) * h0 + (-z*(1288*b*c^4 - 6552*b*c^3 + 11007*b*c^2 - 9720*b*c + 10557*b - 1736*c^5 + 4256*c^4 + 12345*c^3 - 45198*c^2 + 39798*c - 10557)/27) * h1 + (z*(56*b^5 - 1120*b^4 - 1568*b^3*c^2 + 8232*b^3*c - 2464*b^3 + 6440*b^2*c^3 - 30576*b^2*c^2 + 24696*b^2*c - 56*b^2 - 11256*b*c^4 + 59864*b*c^3 - 81903*b*c^2 + 24615*b*c + 1120*b + 8848*c^5 - 57288*c^4 + 119417*c^3 - 89488*c^2 + 14871*c + 2464)/27) * h2 + (-56*z*(b + 7*c - 22)/27) * h3

private lemma rejectE_2_23 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, 1, c) = 0) (h2 : locus 1 (c, b, c) = 0)
    (h3 : edge 1 b c (1, 1, c) (c, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-z*(35*b*c^4 + 54*b*c^3 - 174*b*c^2 + 99*b*c - 27*b - 25*c^5 + 59*c^4 + 21*c^3 - 210*c^2 + 270*c - 81)/9) * h1 + (-z*(5*b^5 - 47*b^4 + 10*b^3*c^2 - 18*b^3*c + 125*b^3 + 15*b^2*c^3 - 111*b^2*c^2 + 141*b^2*c - 31*b^2 + 15*b*c^4 - 75*b*c^3 + 150*b*c^2 - 132*b*c - 164*b + 30*c^5 - 126*c^4 + 51*c^3 + 298*c^2 - 363*c + 44)/9) * h2 + (z*(5*b + 5*c - 22)/9) * h3

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
  linear_combination (-1) * h0 + (z*(8*b^4*c - 4*b^4 - 24*b^3*c^2 - 12*b^3*c + 12*b^3 + 48*b^2*c^3 - 48*b^2*c^2 + 12*b^2*c - 56*b*c^4 + 124*b*c^3 + 51*b*c^2 - 71*b*c + 4*b + 48*c^5 - 240*c^4 + 297*c^3 + 21*c^2 - 150*c + 36)/9) * h1 + (-2*z*(12*b*c^4 - 54*b*c^3 + 72*b*c^2 + 3*b*c - 36*b - 4*c^5 + 10*c^4 - 4*c^3 - 4*c^2 + 10*c - 4)/9) * h2 + (-4*z*(2*c - 1)/9) * h3

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
  linear_combination (-1) * h0 + (z*(27*b^4*c - 27*b^4 - 108*b^3*c + 108*b^3 + 27*b^2*c^3 - 108*b^2*c^2 + 270*b^2*c - 189*b^2 - b*c^4 - 47*b*c^3 + 270*b*c^2 - 251*b*c + 164*b + 9*c^5 - 54*c^4 + 81*c^3 - 117*c^2 + 135*c - 54)/27) * h1 + (z*(b*c^4 + 2*b*c^3 - 100*b*c - 38*b + c^5 - 8*c^4 + 25*c^3 - 46*c^2 + 44*c - 16)/27) * h2 + (-z*(c - 1)/27) * h3

private lemma rejectE_3_26 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, b, 1) = 0) (h2 : locus 1 (c, c, c) = 0)
    (h3 : edge 1 b c (1, b, 1) (c, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-z*(32*b^4 - 192*b^3 - 96*b^2*c + 192*b^2 - 135*b*c^2 + 519*b*c + 32*b + 135*c^3 - 405*c^2 + 558*c - 192)/45) * h1 + (2*z*(45*b*c^2 - 165*b*c + 96*b + 32)/45) * h2 + (32*z/45) * h3

private lemma rejectE_4_15 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, b, b) = 0) (h2 : locus 1 (b, c, 1) = 0)
    (h3 : edge 1 b c (1, b, b) (b, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((2946944*b^5*c - 6504256*b^5 - 4389504*b^4*c^2 - 5105216*b^4*c + 32637520*b^4 + 4374048*b^3*c^3 + 2551440*b^3*c^2 + 229232*b^3*c - 59903152*b^3 - 2532208*b^2*c^4 - 2833744*b^2*c^3 + 12718932*b^2*c^2 - 10169108*b^2*c + 50931064*b^2 + 1034425*b*c^5 - 506334*b*c^4 - 608284*b*c^3 - 10293437*b*c^2 + 15469858*b*c - 20119056*b - 221536*c^6 + 257686*c^5 + 2047228*c^4 - 6380492*c^3 + 8392912*c^2 - 5234712*c + 2254834)/280908) * h1 + ((43631*b*c^5 - 169238*b*c^4 - 89848*b*c^3 + 1354751*b*c^2 - 3567062*b*c + 4512590*b + 483*c^6 - 175138*c^5 + 780565*c^4 - 722470*c^3 - 398941*c^2 + 1286860*c - 1973926)/280908) * h2 + (-(46046*b*c - 101629*b + 483*c^2 - 174655*c + 382925)/280908) * h3

private lemma rejectE_4_20 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, b, b) = 0) (h2 : locus 1 (c, 1, c) = 0)
    (h3 : edge 1 b c (1, b, b) (c, 1, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((22*b^5*c - 83*b^5 - 244*b^4*c + 911*b^4 - 66*b^3*c^3 + 45*b^3*c^2 + 1681*b^3*c - 3470*b^3 - 242*b^2*c^4 + 1297*b^2*c^3 + 192*b^2*c^2 - 7819*b^2*c + 6023*b^2 - 330*b*c^5 + 2441*b*c^4 - 4639*b*c^3 - 2646*b*c^2 + 12793*b*c - 4361*b - 330*c^6 + 2685*c^5 - 6614*c^4 + 2122*c^3 + 10833*c^2 - 8419*c + 1004)/243) * h1 + (-(176*b*c^5 - 548*b*c^4 + 515*b*c^3 + 158*b*c^2 + 46*b*c - 1708*b + 66*c^6 - 709*c^5 + 2059*c^4 - 1171*c^3 - 2095*c^2 + 1294*c + 761)/243) * h2 + (-(22*b*c - 83*b - 66*c^2 + 181*c + 247)/243) * h3

private lemma rejectE_4_22 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, b, b) = 0) (h2 : locus 1 (c, b, b) = 0)
    (h3 : edge 1 b c (1, b, b) (c, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-z*(2*b*c^4 - 5*b*c^3 - 60*b*c^2 - 35*b*c - b - 3*c^5 + 5*c^4 + 49*c^3 - 57*c^2 + 43*c - 1)/27) * h1 + (z*(2*b*c^4 - 5*b*c^3 + 21*b*c^2 - 116*b*c - b + c^5 - 9*c^4 + 20*c^3 - 7*c^2 + 30*c + 1)/27) * h2 + (-z*(c - 1)/27) * h3

private lemma rejectE_4_23 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, b, b) = 0) (h2 : locus 1 (c, b, c) = 0)
    (h3 : edge 1 b c (1, b, b) (c, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((2852*b^5*c - 4953*b^5 - 8587*b^4*c^2 - 1223*b^4*c + 28266*b^4 + 17205*b^3*c^3 - 15634*b^3*c^2 - 4606*b^3*c - 36720*b^3 - 20150*b^2*c^4 + 23925*b^2*c^3 + 74718*b^2*c^2 - 92449*b^2*c - 4953*b^2 + 14446*b*c^5 - 36928*b*c^4 - 6336*b*c^3 - 11323*b*c^2 + 82963*b*c + 30696*b - 2945*c^6 + 5470*c^5 + 30418*c^4 - 92076*c^3 + 13445*c^2 + 123932*c - 39150)/7290) * h1 + ((2883*b*c^5 - 17670*b*c^4 + 22071*b*c^3 + 13581*b*c^2 - 20394*b*c - 2430*b - 31*c^6 - 10254*c^5 + 62817*c^4 - 73113*c^3 - 63657*c^2 + 81504*c + 9720)/7290) * h2 + (-(2852*b*c - 4953*b - 31*c^2 - 10378*c + 18360)/7290) * h3

private lemma rejectE_5_9 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, b, c) = 0) (h2 : locus 1 (b, 1, 1) = 0)
    (h3 : edge 1 b c (1, b, c) (b, 1, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (z*(27*b^4*c - 27*b^4 + 27*b^3*c^2 - 162*b^3*c + 135*b^3 + 27*b^2*c^3 - 135*b^2*c^2 + 324*b^2*c - 216*b^2 + b*c^4 - 79*b*c^3 + 162*b*c^2 - 343*b*c + 124*b + c^5 - 8*c^4 + 25*c^3 - 46*c^2 + 44*c - 16)/27) * h1 + (-z*(b*c^4 - 88*b*c^3 - 46*b*c - 2*b + 18*c^5 - 54*c^4 + 135*c^3 - 153*c^2 + 54*c)/27) * h2 + (-z*(c - 1)/27) * h3

private lemma rejectE_5_10 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, b, c) = 0) (h2 : locus 1 (b, 1, b) = 0)
    (h3 : edge 1 b c (1, b, c) (b, 1, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((2946944*b^5*c - 6504256*b^5 - 1442560*b^4*c^2 - 17503360*b^4*c + 45646032*b^4 - 15456*b^3*c^3 + 12119120*b^3*c^2 + 18280896*b^3*c - 99161168*b^3 - 1105104*b^2*c^4 + 6376512*b^2*c^3 - 38567388*b^2*c^2 + 30004796*b^2*c + 79212824*b^2 + 43631*b*c^5 + 4251178*b*c^4 - 25364056*b*c^3 + 54620863*b*c^2 - 33522822*b*c - 21709474*b + 483*c^6 - 175138*c^5 - 324539*c^4 + 5592218*c^3 - 12128249*c^2 + 6893704*c + 1046370)/280908) * h1 + (-(55223*b*c^5 + 2781646*b*c^4 - 20533384*b*c^3 + 35409977*b*c^2 - 8950466*b*c - 62416*b - 883568*c^6 + 8267210*c^5 - 27511016*c^4 + 41760640*c^3 - 28315612*c^2 + 4800964*c + 765462)/280908) * h2 + (-(46046*b*c - 101629*b + 483*c^2 - 174655*c + 382925)/280908) * h3

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
  linear_combination (-1) * h0 + (-z*(b^5 - 5*b^4 + 8*b^3*c^2 - 15*b^3*c + 4*b^3 - b^2*c^3 - 9*b^2*c^2 + 18*b^2*c + 8*b^2 + 18*b*c^4 - 52*b*c^3 - 90*b*c^2 + 180*b*c - 40*b - 8*c^5 + 90*c^4 - 283*c^3 + 271*c^2 - 102*c + 32)/27) * h1 + (-z*(b*c^4 + 57*b*c^3 - 54*b - 19*c^5 + 80*c^4 - 180*c^3 + 252*c^2 - 189*c + 54)/27) * h2 + (z*(b - c + 2)/27) * h3

private lemma rejectE_5_24 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, b, c) = 0) (h2 : locus 1 (c, c, 1) = 0)
    (h3 : edge 1 b c (1, b, c) (c, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((161*b^5*c - 601*b^5 - 731*b^4*c + 2731*b^4 - 1127*b^3*c^3 + 3354*b^3*c^2 + 4226*b^3*c - 3933*b^3 + 9177*b^2*c^4 - 49830*b^2*c^3 + 69399*b^2*c^2 - 43978*b^2*c + 7592*b^2 - 19320*b*c^5 + 111216*b*c^4 - 157737*b*c^3 + 37902*b*c^2 + 23761*b*c - 5462*b + 33327*c^6 - 262596*c^5 + 715737*c^4 - 863843*c^3 + 462900*c^2 - 86779*c + 654)/972) * h1 + (-(14329*b*c^5 - 79366*b*c^4 + 166345*b*c^3 - 163853*b*c^2 + 71375*b*c - 6770*b - 18193*c^6 + 97258*c^5 - 196999*c^4 + 196553*c^3 - 104756*c^2 + 25661*c - 318)/972) * h2 + (-(161*b*c - 601*b + 805*c^2 - 3575*c + 2130)/972) * h3

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
  linear_combination (-1) * h0 + (z*(64*b*c^4 - 612*b*c^3 + 2124*b*c^2 - 3393*b*c + 2043*b - 24*c^5 + 148*c^4 - 108*c^3 - 648*c^2 + 1215*c - 603)/9) * h1 + (-z*(8*b^5 - 92*b^4 - 24*b^3*c^2 + 132*b^3*c + 152*b^3 + 88*b^2*c^3 - 456*b^2*c^2 + 432*b^2*c + 8*b^2 - 120*b*c^4 + 692*b*c^3 - 1011*b*c^2 + 63*b*c - 92*b + 120*c^5 - 1032*c^4 + 3091*c^3 - 3576*c^2 + 1077*c + 152)/9) * h2 + (4*z*(2*b + 6*c - 19)/9) * h3

private lemma rejectE_6_13 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, c, 1) = 0) (h2 : locus 1 (b, b, b) = 0)
    (h3 : edge 1 b c (1, c, 1) (b, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (z*(135*b^3 - 135*b^2*c - 405*b^2 - 96*b*c^2 + 519*b*c + 558*b + 32*c^4 - 192*c^3 + 192*c^2 + 32*c - 192)/45) * h1 + (-2*z*(45*b^2*c - 165*b*c + 96*c + 32)/45) * h2 + (-32*z/45) * h3

private lemma rejectE_6_19 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, c, 1) = 0) (h2 : locus 1 (c, 1, b) = 0)
    (h3 : edge 1 b c (1, c, 1) (c, 1, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-z*(b*c^4 + 57*b*c^3 - 54*b - 19*c^5 + 80*c^4 - 180*c^3 + 252*c^2 - 189*c + 54)/27) * h1 + (-z*(b^5 - 5*b^4 + 8*b^3*c^2 - 15*b^3*c + 4*b^3 - b^2*c^3 - 9*b^2*c^2 + 18*b^2*c + 8*b^2 + 18*b*c^4 - 52*b*c^3 - 90*b*c^2 + 180*b*c - 40*b - 8*c^5 + 90*c^4 - 283*c^3 + 271*c^2 - 102*c + 32)/27) * h2 + (z*(b - c + 2)/27) * h3

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
  linear_combination (-1) * h0 + (-z*(b^5*c - 2*b^5 - 4*b^4*c^2 + 8*b^4*c + 3*b^4 + 7*b^3*c^3 - 14*b^3*c^2 - 8*b^3*c - 2*b^3 - 8*b^2*c^4 + 22*b^2*c^3 - 5*b^2*c^2 + 7*b^2*c + 5*b*c^5 - 16*b*c^4 + 4*b*c^3 + 7*b*c^2 - 5*b*c + b - 2*c^6 + 10*c^5 - 17*c^4 + 16*c^3 - 8*c^2 + c)) * h1 + (z*(b*c - 2*b - 2*c^2 + 6*c - 1)/27) * h3

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
  linear_combination (-1) * h0 + (-z*(b^5*c - 2*b^5 - 4*b^4*c^2 + 8*b^4*c + 3*b^4 + 7*b^3*c^3 - 14*b^3*c^2 - 8*b^3*c - 2*b^3 - 8*b^2*c^4 + 22*b^2*c^3 - 5*b^2*c^2 + 7*b^2*c + 5*b*c^5 - 16*b*c^4 + 4*b*c^3 + 7*b*c^2 - 5*b*c + b - 2*c^6 + 10*c^5 - 17*c^4 + 16*c^3 - 8*c^2 + c)) * h1 + (z*(b*c - 2*b - 2*c^2 + 6*c - 1)/27) * h3

private lemma rejectE_8_12 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, c, c) = 0) (h2 : locus 1 (b, b, 1) = 0)
    (h3 : edge 1 b c (1, c, c) (b, b, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(176*b*c^5 - 548*b*c^4 + 515*b*c^3 + 158*b*c^2 + 46*b*c - 1708*b + 66*c^6 - 709*c^5 + 2059*c^4 - 1171*c^3 - 2095*c^2 + 1294*c + 761)/243) * h1 + ((22*b^5*c - 83*b^5 - 244*b^4*c + 911*b^4 - 66*b^3*c^3 + 45*b^3*c^2 + 1681*b^3*c - 3470*b^3 - 242*b^2*c^4 + 1297*b^2*c^3 + 192*b^2*c^2 - 7819*b^2*c + 6023*b^2 - 330*b*c^5 + 2441*b*c^4 - 4639*b*c^3 - 2646*b*c^2 + 12793*b*c - 4361*b - 330*c^6 + 2685*c^5 - 6614*c^4 + 2122*c^3 + 10833*c^2 - 8419*c + 1004)/243) * h2 + (-(22*b*c - 83*b - 66*c^2 + 181*c + 247)/243) * h3

private lemma rejectE_8_13 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, c, c) = 0) (h2 : locus 1 (b, b, b) = 0)
    (h3 : edge 1 b c (1, c, c) (b, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((93*b*c^3 - 627*b*c^2 + 672*b*c + 927*b - 31*c^5 + 271*c^4 - 673*c^3 + 348*c^2 + 372*c - 276)/33) * h1 + (-(2*c - 7)/3) * h2 + ((31*c - 116)/33) * h3

private lemma rejectE_8_19 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (1, c, c) = 0) (h2 : locus 1 (c, 1, b) = 0)
    (h3 : edge 1 b c (1, c, c) (c, 1, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(14329*b*c^5 - 79366*b*c^4 + 166345*b*c^3 - 163853*b*c^2 + 71375*b*c - 6770*b - 18193*c^6 + 97258*c^5 - 196999*c^4 + 196553*c^3 - 104756*c^2 + 25661*c - 318)/972) * h1 + ((161*b^5*c - 601*b^5 - 731*b^4*c + 2731*b^4 - 1127*b^3*c^3 + 3354*b^3*c^2 + 4226*b^3*c - 3933*b^3 + 9177*b^2*c^4 - 49830*b^2*c^3 + 69399*b^2*c^2 - 43978*b^2*c + 7592*b^2 - 19320*b*c^5 + 111216*b*c^4 - 157737*b*c^3 + 37902*b*c^2 + 23761*b*c - 5462*b + 33327*c^6 - 262596*c^5 + 715737*c^4 - 863843*c^3 + 462900*c^2 - 86779*c + 654)/972) * h2 + (-(161*b*c - 601*b + 805*c^2 - 3575*c + 2130)/972) * h3

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
  linear_combination (-1) * h0 + (z*(5*b^4*c - 7*b^4 - 15*b^3*c^2 + 6*b^3*c + 21*b^3 + 30*b^2*c^3 - 57*b^2*c^2 + 21*b^2*c - 30*b*c^4 + 72*b*c^3 + 60*b*c^2 - 108*b*c - 21*b + 15*c^5 - 66*c^4 + 66*c^3 + 6*c^2 - 39*c + 21)/9) * h1 + (-z*(5*b*c^4 - 37*b*c^3 + 72*b*c^2 - 13*b*c - 28*b - 5*c^5 + 32*c^4 - 50*c^3 - 14*c^2 + 59*c - 14)/9) * h2 + (-z*(5*c - 7)/9) * h3

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
  linear_combination (-1) * h0 + (z*(8*b^4*c - 4*b^4 - 24*b^3*c^2 - 12*b^3*c + 12*b^3 + 48*b^2*c^3 - 48*b^2*c^2 + 12*b^2*c - 56*b*c^4 + 124*b*c^3 + 51*b*c^2 - 71*b*c + 4*b + 48*c^5 - 240*c^4 + 297*c^3 + 21*c^2 - 150*c + 36)/9) * h1 + (-2*z*(12*b*c^4 - 54*b*c^3 + 72*b*c^2 + 3*b*c - 36*b - 4*c^5 + 10*c^4 - 4*c^3 - 4*c^2 + 10*c - 4)/9) * h2 + (-4*z*(2*c - 1)/9) * h3

private lemma rejectE_9_25 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, 1, 1) = 0) (h2 : locus 1 (c, c, b) = 0)
    (h3 : edge 1 b c (b, 1, 1) (c, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-z*(1512*b^4*c - 1512*b^4 - 4536*b^3*c^2 + 3024*b^3*c + 1512*b^3 + 6048*b^2*c^3 - 7560*b^2*c^2 + 4536*b^2*c - 3024*b^2 - 4144*b*c^4 + 9856*b*c^3 - 10665*b*c^2 + 4063*b*c + 1592*b + 1176*c^5 - 5376*c^4 + 11841*c^3 - 14703*c^2 + 9534*c - 2472)/27) * h1 + (2*z*(196*b*c^4 - 1372*b*c^3 + 4536*b*c^2 - 7081*b*c + 4072*b - 28*c^5 - 28*c^4 + 56*c^3 + 28*c^2 + 28*c - 56)/27) * h2 + (56*z*(c - 1)/27) * h3

private lemma rejectE_10_16 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, 1, b) = 0) (h2 : locus 1 (b, c, b) = 0)
    (h3 : edge 1 b c (b, 1, b) (b, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-z*(2*b*c^4 - 5*b*c^3 - 60*b*c^2 - 35*b*c - b - 3*c^5 + 5*c^4 + 49*c^3 - 57*c^2 + 43*c - 1)/27) * h1 + (z*(2*b*c^4 - 5*b*c^3 + 21*b*c^2 - 116*b*c - b + c^5 - 9*c^4 + 20*c^3 - 7*c^2 + 30*c + 1)/27) * h2 + (-z*(c - 1)/27) * h3

private lemma rejectE_10_18 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, 1, b) = 0) (h2 : locus 1 (c, 1, 1) = 0)
    (h3 : edge 1 b c (b, 1, b) (c, 1, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-z*(8*b^5 - 92*b^4 - 24*b^3*c^2 + 132*b^3*c + 152*b^3 + 88*b^2*c^3 - 456*b^2*c^2 + 432*b^2*c + 8*b^2 - 120*b*c^4 + 692*b*c^3 - 1011*b*c^2 + 63*b*c - 92*b + 120*c^5 - 1032*c^4 + 3091*c^3 - 3576*c^2 + 1077*c + 152)/9) * h1 + (z*(64*b*c^4 - 612*b*c^3 + 2124*b*c^2 - 3393*b*c + 2043*b - 24*c^5 + 148*c^4 - 108*c^3 - 648*c^2 + 1215*c - 603)/9) * h2 + (4*z*(2*b + 6*c - 19)/9) * h3

private lemma rejectE_10_24 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, 1, b) = 0) (h2 : locus 1 (c, c, 1) = 0)
    (h3 : edge 1 b c (b, 1, b) (c, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((22*b^5*c - 83*b^5 - 244*b^4*c + 911*b^4 - 66*b^3*c^3 + 45*b^3*c^2 + 1681*b^3*c - 3470*b^3 - 242*b^2*c^4 + 1297*b^2*c^3 + 192*b^2*c^2 - 7819*b^2*c + 6023*b^2 - 330*b*c^5 + 2441*b*c^4 - 4639*b*c^3 - 2646*b*c^2 + 12793*b*c - 4361*b - 330*c^6 + 2685*c^5 - 6614*c^4 + 2122*c^3 + 10833*c^2 - 8419*c + 1004)/243) * h1 + (-(176*b*c^5 - 548*b*c^4 + 515*b*c^3 + 158*b*c^2 + 46*b*c - 1708*b + 66*c^6 - 709*c^5 + 2059*c^4 - 1171*c^3 - 2095*c^2 + 1294*c + 761)/243) * h2 + (-(22*b*c - 83*b - 66*c^2 + 181*c + 247)/243) * h3

private lemma rejectE_10_25 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, 1, b) = 0) (h2 : locus 1 (c, c, b) = 0)
    (h3 : edge 1 b c (b, 1, b) (c, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((2852*b^5*c - 4953*b^5 - 8587*b^4*c^2 - 1223*b^4*c + 28266*b^4 + 17205*b^3*c^3 - 15634*b^3*c^2 - 4606*b^3*c - 36720*b^3 - 20150*b^2*c^4 + 23925*b^2*c^3 + 74718*b^2*c^2 - 92449*b^2*c - 4953*b^2 + 14446*b*c^5 - 36928*b*c^4 - 6336*b*c^3 - 11323*b*c^2 + 82963*b*c + 30696*b - 2945*c^6 + 5470*c^5 + 30418*c^4 - 92076*c^3 + 13445*c^2 + 123932*c - 39150)/7290) * h1 + ((2883*b*c^5 - 17670*b*c^4 + 22071*b*c^3 + 13581*b*c^2 - 20394*b*c - 2430*b - 31*c^6 - 10254*c^5 + 62817*c^4 - 73113*c^3 - 63657*c^2 + 81504*c + 9720)/7290) * h2 + (-(2852*b*c - 4953*b - 31*c^2 - 10378*c + 18360)/7290) * h3

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
  linear_combination (-1) * h0 + (-z*(b^5*c - 2*b^5 - 4*b^4*c^2 + 8*b^4*c + 3*b^4 + 7*b^3*c^3 - 14*b^3*c^2 - 8*b^3*c - 2*b^3 - 8*b^2*c^4 + 22*b^2*c^3 - 5*b^2*c^2 + 7*b^2*c + 5*b*c^5 - 16*b*c^4 + 4*b*c^3 + 7*b*c^2 - 5*b*c + b - 2*c^6 + 10*c^5 - 17*c^4 + 16*c^3 - 8*c^2 + c)) * h1 + (z*(b*c - 2*b - 2*c^2 + 6*c - 1)/27) * h3

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
  linear_combination ((2946944*b^5*c - 6504256*b^5 - 4389504*b^4*c^2 - 5105216*b^4*c + 32637520*b^4 + 4374048*b^3*c^3 + 2551440*b^3*c^2 + 229232*b^3*c - 59903152*b^3 - 2532208*b^2*c^4 - 2833744*b^2*c^3 + 12718932*b^2*c^2 - 10169108*b^2*c + 50931064*b^2 + 1034425*b*c^5 - 506334*b*c^4 - 608284*b*c^3 - 10293437*b*c^2 + 15469858*b*c - 20119056*b - 221536*c^6 + 257686*c^5 + 2047228*c^4 - 6380492*c^3 + 8392912*c^2 - 5234712*c + 2254834)/280908) * h1 + ((43631*b*c^5 - 169238*b*c^4 - 89848*b*c^3 + 1354751*b*c^2 - 3567062*b*c + 4512590*b + 483*c^6 - 175138*c^5 + 780565*c^4 - 722470*c^3 - 398941*c^2 + 1286860*c - 1973926)/280908) * h2 + (-(46046*b*c - 101629*b + 483*c^2 - 174655*c + 382925)/280908) * h3

private lemma rejectE_12_26 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, b, 1) = 0) (h2 : locus 1 (c, c, c) = 0)
    (h3 : edge 1 b c (b, b, 1) (c, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(31*b^5 - 271*b^4 - 93*b^3*c + 673*b^3 + 627*b^2*c - 348*b^2 - 672*b*c - 372*b - 927*c + 276)/33) * h1 + (-(2*b - 7)/3) * h2 + ((31*b - 116)/33) * h3

private lemma rejectE_13_19 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, b, b) = 0) (h2 : locus 1 (c, 1, b) = 0)
    (h3 : edge 1 b c (b, b, b) (c, 1, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((45*b*c^2 - 108*b*c + 6*b + 45*c^3 - 378*c^2 + 729*c - 196)/8) * h1 + (-3*(15*b^4*c - 31*b^4 - 30*b^3*c^2 + 2*b^3*c + 124*b^3 + 45*b^2*c^3 - 93*b^2*c^2 - 30*b*c^4 + 62*b*c^3 + 180*b*c^2 - 327*b*c - 93*b + 15*c^5 - 91*c^4 + 124*c^3 + 45*c^2 - 78*c - 6)/8) * h2 + (3*(15*c - 31)/8) * h3

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
  linear_combination ((161*b^5*c - 601*b^5 - 731*b^4*c + 2731*b^4 - 1127*b^3*c^3 + 3354*b^3*c^2 + 4226*b^3*c - 3933*b^3 + 9177*b^2*c^4 - 49830*b^2*c^3 + 69399*b^2*c^2 - 43978*b^2*c + 7592*b^2 - 19320*b*c^5 + 111216*b*c^4 - 157737*b*c^3 + 37902*b*c^2 + 23761*b*c - 5462*b + 33327*c^6 - 262596*c^5 + 715737*c^4 - 863843*c^3 + 462900*c^2 - 86779*c + 654)/972) * h1 + (-(14329*b*c^5 - 79366*b*c^4 + 166345*b*c^3 - 163853*b*c^2 + 71375*b*c - 6770*b - 18193*c^6 + 97258*c^5 - 196999*c^4 + 196553*c^3 - 104756*c^2 + 25661*c - 318)/972) * h2 + (-(161*b*c - 601*b + 805*c^2 - 3575*c + 2130)/972) * h3

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
  linear_combination (-1) * h0 + (z*(56*b^5 - 1120*b^4 - 1568*b^3*c^2 + 8232*b^3*c - 2464*b^3 + 6440*b^2*c^3 - 30576*b^2*c^2 + 24696*b^2*c - 56*b^2 - 11256*b*c^4 + 59864*b*c^3 - 81903*b*c^2 + 24615*b*c + 1120*b + 8848*c^5 - 57288*c^4 + 119417*c^3 - 89488*c^2 + 14871*c + 2464)/27) * h1 + (-z*(1288*b*c^4 - 6552*b*c^3 + 11007*b*c^2 - 9720*b*c + 10557*b - 1736*c^5 + 4256*c^4 + 12345*c^3 - 45198*c^2 + 39798*c - 10557)/27) * h2 + (-56*z*(b + 7*c - 22)/27) * h3

private lemma rejectE_16_24 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (b, c, b) = 0) (h2 : locus 1 (c, c, 1) = 0)
    (h3 : edge 1 b c (b, c, b) (c, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((31*b^5*c - 116*b^5 - 186*b^4*c + 699*b^4 + 62*b^3*c^3 - 387*b^3*c^2 + 825*b^3*c - 940*b^3 + 93*b^2*c^4 - 720*b^2*c^3 + 1866*b^2*c^2 - 1656*b^2*c - 348*b^2 + 93*b*c^5 - 627*b*c^4 + 1416*b*c^3 - 1680*b*c^2 + 885*b*c + 705*b + 186*c^6 - 975*c^5 + 960*c^4 + 516*c^3 - 1542*c^2 + 3336*c - 696)/81) * h1 + ((217*b*c^5 + 428*b*c^4 - 911*b*c^3 - 917*b*c^2 - 1543*b*c + 250*b - 155*c^6 + 177*c^5 + 324*c^4 - 505*c^3 + 861*c^2 - 333*c + 307)/81) * h2 + (-(31*b*c - 116*b + 31*c^2 - 178*c + 235)/81) * h3

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
  linear_combination (-1) * h0 + (-z*(35*b*c^4 + 54*b*c^3 - 174*b*c^2 + 99*b*c - 27*b - 25*c^5 + 59*c^4 + 21*c^3 - 210*c^2 + 270*c - 81)/9) * h1 + (-z*(5*b^5 - 47*b^4 + 10*b^3*c^2 - 18*b^3*c + 125*b^3 + 15*b^2*c^3 - 111*b^2*c^2 + 141*b^2*c - 31*b^2 + 15*b*c^4 - 75*b*c^3 + 150*b*c^2 - 132*b*c - 164*b + 30*c^5 - 126*c^4 + 51*c^3 + 298*c^2 - 363*c + 44)/9) * h2 + (z*(5*b + 5*c - 22)/9) * h3

private lemma rejectE_19_26 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (c, 1, b) = 0) (h2 : locus 1 (c, c, c) = 0)
    (h3 : edge 1 b c (c, 1, b) (c, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-3*(15*b^5 - 101*b^4 - 15*b^3*c^2 - 38*b^3*c + 164*b^3 + 60*b^2*c^3 - 123*b^2*c^2 + 180*b^2*c + 45*b^2 - 45*b*c^4 + 22*b*c^3 + 360*b*c^2 - 312*b*c - 123*b + 30*c^5 - 161*c^4 + 164*c^3 + 270*c^2 - 471*c + 90)/8) * h1 + ((225*b*c^2 - 576*b*c + 288*b - 180*c^3 + 648*c^2 - 570*c + 32)/8) * h2 + (3*(15*b + 30*c - 41)/8) * h3

private lemma rejectE_20_22 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (c, 1, c) = 0) (h2 : locus 1 (c, b, b) = 0)
    (h3 : edge 1 b c (c, 1, c) (c, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((217*b*c^5 + 428*b*c^4 - 911*b*c^3 - 917*b*c^2 - 1543*b*c + 250*b - 155*c^6 + 177*c^5 + 324*c^4 - 505*c^3 + 861*c^2 - 333*c + 307)/81) * h1 + ((31*b^5*c - 116*b^5 - 186*b^4*c + 699*b^4 + 62*b^3*c^3 - 387*b^3*c^2 + 825*b^3*c - 940*b^3 + 93*b^2*c^4 - 720*b^2*c^3 + 1866*b^2*c^2 - 1656*b^2*c - 348*b^2 + 93*b*c^5 - 627*b*c^4 + 1416*b*c^3 - 1680*b*c^2 + 885*b*c + 705*b + 186*c^6 - 975*c^5 + 960*c^4 + 516*c^3 - 1542*c^2 + 3336*c - 696)/81) * h2 + (-(31*b*c - 116*b + 31*c^2 - 178*c + 235)/81) * h3

private lemma rejectE_20_23 (b c z : ℝ)
    (h0 : invCondition 1 b c z = 0)
    (h1 : locus 1 (c, 1, c) = 0) (h2 : locus 1 (c, b, c) = 0)
    (h3 : edge 1 b c (c, 1, c) (c, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(905*b*c^5 - 2828*b*c^4 - 3970*b*c^3 + 22991*b*c^2 - 26066*b*c + 8216*b - 724*c^6 + 5713*c^5 - 17833*c^4 + 25715*c^3 - 18641*c^2 + 9104*c - 192)/972) * h1 + ((181*b^5*c - 677*b^5 - 1571*b^4*c + 5875*b^4 - 181*b^3*c^3 + 612*b^3*c^2 + 3940*b^3*c - 13827*b^3 - 362*b^2*c^4 + 3700*b^2*c^3 - 9105*b^2*c^2 + 480*b^2*c + 2823*b^2 - 543*b*c^5 + 6064*b*c^4 - 24647*b*c^3 + 40068*b*c^2 - 20106*b*c + 14940*b - 724*c^6 + 7161*c^5 - 26363*c^4 + 42873*c^3 - 27225*c^2 + 9888*c - 138)/972) * h2 + (-(181*b*c - 677*b - 362*c^2 + 1231*c + 459)/972) * h3

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
  linear_combination (-(905*b*c^5 - 2828*b*c^4 - 3970*b*c^3 + 22991*b*c^2 - 26066*b*c + 8216*b - 724*c^6 + 5713*c^5 - 17833*c^4 + 25715*c^3 - 18641*c^2 + 9104*c - 192)/972) * h1 + ((181*b^5*c - 677*b^5 - 1571*b^4*c + 5875*b^4 - 181*b^3*c^3 + 612*b^3*c^2 + 3940*b^3*c - 13827*b^3 - 362*b^2*c^4 + 3700*b^2*c^3 - 9105*b^2*c^2 + 480*b^2*c + 2823*b^2 - 543*b*c^5 + 6064*b*c^4 - 24647*b*c^3 + 40068*b*c^2 - 20106*b*c + 14940*b - 724*c^6 + 7161*c^5 - 26363*c^4 + 42873*c^3 - 27225*c^2 + 9888*c - 138)/972) * h2 + (-(181*b*c - 677*b - 362*c^2 + 1231*c + 459)/972) * h3

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
  linear_combination (-1) * h0 + (z*(12*b^2*c^4 - 5*b^2*c^3 - 84*b^2*c^2 + 92*b^2*c - 28*b^2 - 3*b*c^5 - 71*b*c^4 + 208*b*c^3 - 53*b*c^2 - 44*b*c + 14*b + 21*c^5 - 50*c^4 - 2*c^3 + 14*c^2)/2) * h1 + (-z*(6*b^4*c^2 - 8*b^4*c - 14*b^4 - 6*b^3*c^3 - 46*b^3*c^2 + 122*b^3*c + 42*b^3 + 3*b^2*c^4 + 50*b^2*c^3 - 17*b^2*c^2 - 274*b^2*c + 14*b^2 - 21*b*c^4 - 29*b*c^3 + 185*b*c^2 + 6*b*c - 42*b + 3*c^5 - 7*c^4)/2) * h2 + (z*(3*c - 7)/2) * h3

private lemma rejectI_0_23 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, 1) = 0) (h2 : locus b (c, b, c) = 0)
    (h3 : edge b b c (1, 1, 1) (c, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-z*(16*b^5 - 24*b^4 + 112*b^3 + 485*b^2 - 12*b*c^5 + 320*b*c^4 - 2484*b*c^3 + 8808*b*c^2 - 15002*b*c + 2684*b - 48*c^5 + 433*c^4 - 1582*c^3 + 2684*c^2)/5) * h1 + (z*(24*b^5*c + 8*b^5 - 24*b^4*c^2 - 152*b^4*c + 88*b^4 + 12*b^3*c^3 + 52*b^3*c^2 + 3*b^3*c + 149*b^3 + 24*b^2*c^3 + 313*b^2*c^2 - 785*b^2*c + 1229*b^2 - 60*b*c^4 + 124*b*c^3 - 1259*b*c^2 + 4746*b*c - 8052*b + 12*c^5 - 8*c^4)/5) * h2 + (-4*z*(3*c - 2)/5) * h3

private lemma rejectI_0_24 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, 1) = 0) (h2 : locus b (c, c, 1) = 0)
    (h3 : edge b b c (1, 1, 1) (c, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-z*(4*b^2 - 4*b*c^5 + 24*b*c^4 - 22*b*c^3 - 53*b*c^2 - 12*b*c + b - 4*c^5 + 17*c^4 - 10*c^3 - 10*c^2 + 2*c + 5)/9) * h1 + (z*(4*b^5*c - 4*b^5 - 36*b^4*c + 36*b^4 + 4*b^3*c^3 - 12*b^3*c^2 + 87*b^3*c - 79*b^3 - 16*b^2*c^3 + 61*b^2*c^2 - 55*b^2*c + 14*b^2 - 4*b*c^4 + 8*b*c^3 + 9*b*c^2 - 80*b*c + b + 4*c^5 - 20*c^4 + 40*c^3 - 40*c^2 + 20*c - 4)/9) * h2 + (-4*z*(c - 1)/9) * h3

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
  linear_combination ((851392543110912*b*c*z + 214484812474944*b*c - 1303748682122088*b*z + 422738309272314*b - 743103431316*c^2*z - 187204364667*c^2 - 3167122170548556*c*z - 820411429172469*c + 4831117383232944*z - 1399508996973212)/2601785587623728) * h0 + (-(424953168124140*b^2*c^5*z^2 - 128453807803251*b^2*c^5*z - 90939116597682*b^2*c^5 - 5066641041638904*b^2*c^4*z^2 + 5086430149110550*b^2*c^4*z + 2170903085749908*b^2*c^4 + 13941083973181536*b^2*c^3*z^2 - 53951082036954024*b^2*c^3*z - 18365408384415768*b^2*c^3 - 13728146123532456*b^2*c^2*z^2 + 205002142550872082*b^2*c^2*z + 66774388591496448*b^2*c^2 + 2073819626711604*b^2*c*z^2 - 333854458284845877*b^2*c*z - 107089787421383430*b^2*c + 2578595019349536*b^2*z^2 + 201109499640549224*b^2*z + 64231142702723820*b^2 + 852878749973544*b*c^5*z^2 + 685877240556390*b*c^5*z + 181878233195364*b*c^5 + 719102994734232*b*c^4*z^2 - 11042138953288022*b*c^4*z - 4341806171499816*b*c^4 - 5248696156081272*b*c^3*z^2 + 110555951060912142*b*c^3*z + 37822086168003720*b*c^3 + 1448862955832520*b*c^2*z^2 - 441883436249931970*b*c^2*z - 145413112022753400*b*c^2 + 7496873805337776*b*c*z^2 + 749095427440149716*b*c*z + 241406180635061628*b*c - 5716351594187712*b*z^2 - 452023738240592352*b*z - 143982106399838076*b - 426439374986772*c^6*z^2 + 128079399073917*c^6*z + 90939116597682*c^6 - 836705303883540*c^5*z^2 - 6854209180341403*c^5*z - 2261842202347590*c^5 + 10880159443643160*c^4*z^2 + 60572091894485346*c^4*z + 20172555003774948*c^4 - 24201046955095272*c^3*z^2 - 245776576598029182*c^3*z - 81912531628773504*c^3 + 23371899444687708*c^2*z^2 + 525418342908036473*c^2*z + 172091936531304078*c^2 - 11590126895910276*c*z^2 - 565213703035832927*c*z - 182093621155966236*c + 2914091952642720*z^2 + 236452158670649600*z + 75648960835541118)/5203571175247456) * h1 + (-(-5652216232225344*b^6*c*z - 2182538798344368*b^6*c + 670993866586368*b^6*z^2 + 53968345891513152*b^6*z + 17181053284487904*b^6 + 9420360387042240*b^5*c^2*z + 3637564663907280*b^5*c^2 - 1118323110977280*b^5*c*z^2 - 86179098997705024*b^5*c*z - 27180062941916928*b^5*c - 447329244390912*b^5*z^2 - 35978897261008768*b^5*z - 11454035522991936*b^5 - 3768144154816896*b^4*c^3*z - 1455025865562912*b^4*c^3 + 447329244390912*b^4*c^2*z^2 + 14312068370811616*b^4*c^2*z + 3087636796005192*b^4*c^2 + 2572143155247744*b^4*c*z^2 + 249270280992490496*b^4*c*z + 82229745244786392*b^4*c - 5032453999397760*b^4*z^2 - 404762594186348640*b^4*z - 128857899633659280*b^4 - 851392543110912*b^3*c^3*z^2 + 9676893593919408*b^3*c^3*z + 3819442897102644*b^3*c^3 + 980901958706856*b^3*c^2*z^2 - 105015255232691850*b^3*c^2*z - 34068164378151840*b^3*c^2 - 73593260047080*b^3*c*z^2 + 64038354325638026*b^3*c*z + 17857730198575524*b^3*c + 4193711666164800*b^3*z^2 + 337302161821957200*b^3*z + 107381583028049400*b^3 + 426439374986772*b^2*c^4*z^2 + 3640064755742979*b^2*c^4*z + 1364086748965230*b^2*c^4 + 4649311188772452*b^2*c^3*z^2 - 59609722497425481*b^2*c^3*z - 21378034944733734*b^2*c^3 - 11618264401427412*b^2*c^2*z^2 + 348740036346786101*b^2*c^2*z + 116404777620446370*b^2*c^2 - 642712150360836*b^2*c*z^2 - 889522136634141415*b^2*c*z - 287646404340550398*b^2*c + 9421872209983584*b^2*z^2 + 757805523559997176*b^2*z + 241250623203017652*b^2 - 1705757499947088*b*c^4*z^2 - 7023970713338124*b*c^4*z - 2546295264735096*b*c^4 - 6716556476620056*b*c^3*z^2 + 105170022229757206*b*c^3*z + 37686750785186196*b*c^3 + 22127594438727144*b*c^2*z^2 - 550334955901445098*b*c^2*z - 182530956683164584*b*c^2 - 4797406758952512*b*c*z^2 + 1181712654165728528*b*c*z + 380906103494807700*b*c - 11256352236259776*b*z^2 - 902209554417126224*b*z - 287325800348025984*b - 942036038704224*c^5*z - 363756466390728*c^5 + 538271686084500*c^4*z^2 + 18287005303220515*c^4*z + 6410134428057582*c^4 + 571260942879804*c^3*z^2 - 120088598279793087*c^3*z - 40741627027566006*c^3 - 3565970578104372*c^2*z^2 + 371372931350515325*c^2*z + 121945623980430978*c^2 - 1395324919629756*c*z^2 - 556633502150511561*c*z - 178917566236250694*c + 4243175957611872*z^2 + 329547962739024800*z + 105211054351028826)/5203571175247456) * h2 + ((-8089201404*c*z - 3123552813*c + 960296688*z^2 + 77237105132*z + 24588762114)/44682722876) * h3

private lemma rejectI_1_18 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, b) = 0) (h2 : locus b (c, 1, 1) = 0)
    (h3 : edge b b c (1, 1, b) (c, 1, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-c^2 + 4*c - 1) * h0 + (-(-b^3 + 4*b^2 + 6*b*c^6*z - 60*b*c^5*z + 210*b*c^4*z - 300*b*c^3*z - b*c^3 + 144*b*c^2*z + 5*b*c^2 - 3*b*c + 3*c^2 - 12*c - 1)/3) * h1 + (-(-2*b^5*c - 2*b^5 - 3*b^4*c^2 + 12*b^4*c + 15*b^4 + 3*b^3*c^3*z - 3*b^3*c^3 - 15*b^3*c^2*z + 14*b^3*c^2 + 15*b^3*c*z - 11*b^3*c - 3*b^3*z - 31*b^3 - 6*b^2*c^4*z - b^2*c^4 + 27*b^2*c^3*z + 9*b^2*c^3 - 15*b^2*c^2*z - 11*b^2*c^2 - 9*b^2*c*z - 25*b^2*c + 3*b^2*z + 7*b^2 + 24*b*c^4*z - 150*b*c^3*z + 264*b*c^2*z - 3*b*c^2 - 138*b*c*z + 10*b*c + 13*b - 6*c^4*z + 36*c^3*z - 66*c^2*z + 36*c*z + c + 8)/3) * h2 + (-1/3) * h3

private lemma rejectI_1_21 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, b) = 0) (h2 : locus b (c, b, 1) = 0)
    (h3 : edge b b c (1, 1, b) (c, b, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(c - 2)*(55*b^2 + 55*b*c - 284*b + 55*c^2 - 339*c + 360)/12) * h0 + ((5*b^7 + 55*b^6*c*z - 79*b^6 - 559*b^5*c*z + 503*b^5 + 1826*b^4*c*z - 10*b^4*c - 52*b^4*z - 1650*b^4 - 1562*b^3*c*z + 73*b^3*c + 309*b^3*z + 2989*b^3 - 1785*b^2*c*z - 153*b^2*c - 395*b^2*z - 3057*b^2 + 2061*b*c*z + 41*b*c + 71*b*z + 2042*b - 55*c^3 + 220*c^2*z + 449*c^2 - 696*c*z - 818*c + 67*z - 862)/12) * h1 + (-(-5*b^7 + 55*b^6*c*z + 5*b^6*c + 99*b^6 + 10*b^5*c^2 - 559*b^5*c*z - 89*b^5*c - 779*b^5 - 5*b^4*c^3 - 103*b^4*c^2 + 1826*b^4*c*z + 586*b^4*c - 52*b^4*z + 3110*b^4 - 55*b^3*c^4*z - 5*b^3*c^4 + 339*b^3*c^3*z + 54*b^3*c^3 - 580*b^3*c^2*z + 342*b^3*c^2 - 1370*b^3*c*z - 1736*b^3*c + 413*b^3*z - 6649*b^3 + 275*b^2*c^4*z + 19*b^2*c^4 - 1695*b^2*c^3*z - 133*b^2*c^3 + 2955*b^2*c^2*z - 416*b^2*c^2 - 2910*b^2*c*z + 2176*b^2*c - 805*b^2*z + 7377*b^2 - 220*b*c^4*z + 1356*b*c^3*z - 2595*b*c^2*z + 209*b*c^2 + 3654*b*c*z - 815*b*c - 63*b*z - 3530*b + 220*c^2*z - 696*c*z + 220*c + 67*z - 378)/12) * h2 + (-(5*b - 19)/12) * h3

private lemma rejectI_2_5 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, c) = 0) (h2 : locus b (1, b, c) = 0)
    (h3 : edge b b c (1, 1, c) (1, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-z*(6*b^6 - 36*b^5 + 45*b^4 + 33*b^3 - 24*b^2 + 2*b*c^3 - 54*b*c^2 + 142*b*c + 3*b + 11*c^3 - 34*c^2 - c)/3) * h1 + (-z*(6*b^6 - 2*b^5*c - 32*b^5 + 53*b^4 + 2*b^3*c^2 + 8*b^3*c - 6*b^3 + 5*b^2*c^2 - 29*b^2*c - 11*b^2 - 2*b*c^3 + 25*b*c^2 - 40*b*c - 42*b - 11*c^3 + 56*c^2 - 78*c + 32)/3) * h2 + (z*(3*b - c)/3) * h3

private lemma rejectI_2_16 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, c) = 0) (h2 : locus b (b, c, b) = 0)
    (h3 : edge b b c (1, 1, c) (b, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (z*(c - 1)*(3*b^2*c - 5*b^2 - b*c^2 - 6*b*c + 2*b + 2*c^2)) * h1 + (-z*(c - 1)*(b^2*c - b*c^2 - 5*b + 2*c^2 - 4*c + 2)) * h2

private lemma rejectI_2_19 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, c) = 0) (h2 : locus b (c, 1, b) = 0)
    (h3 : edge b b c (1, 1, c) (c, 1, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((c - 2)*(b^2 + b*c - 2*b - 3*c + 3)/4) * h0 + (-(3*b^6*c*z - 3*b^6*z + 3*b^6 - 15*b^5*c*z - 2*b^5*c + 27*b^5*z - 22*b^5 - 18*b^4*c*z + 12*b^4*c - 96*b^4*z + 39*b^4 + 177*b^3*c*z - b^3*c + 171*b^3*z + 15*b^3 - 237*b^2*c*z - 62*b^2*c - 117*b^2*z - 67*b^2 + 36*b*c*z + 41*b*c + 36*b*z + 37*b + c^4 + 2*c^3 - 2*c^2 - 3*c + 7)/12) * h1 + ((3*b^6*c*z - 2*b^6*c - 3*b^6*z + 9*b^6 + 6*b^5*c^2 - 15*b^5*c*z - 20*b^5*c + 27*b^5*z - 31*b^5 - 3*b^4*c^3*z - 8*b^4*c^3 - 3*b^4*c^2*z + 35*b^4*c^2 + 10*b^4*c - 96*b^4*z + 39*b^4 + 8*b^3*c^4 + 24*b^3*c^3*z - 52*b^3*c^3 + 6*b^3*c^2*z + 50*b^3*c^2 + 69*b^3*c*z + 2*b^3*c + 171*b^3*z + 18*b^3 + 4*b^2*c^4 - 57*b^2*c^3*z + 18*b^2*c^3 + 33*b^2*c^2*z - 93*b^2*c^2 - 75*b^2*c*z + 8*b^2*c - 117*b^2*z - 67*b^2 - 6*b*c^4 + 36*b*c^3*z + 41*b*c^3 - 36*b*c^2*z - 2*b*c^2 - 36*b*c*z - 23*b*c + 36*b*z + 37*b - 5*c^4 + 3*c^3 + 2*c^2 + 10*c + 1)/12) * h2 + (-(b - 1)/12) * h3

private lemma rejectI_2_22 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, c) = 0) (h2 : locus b (c, b, b) = 0)
    (h3 : edge b b c (1, 1, c) (c, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((1384992000*b^5*c^4*z^2 - 6093964800*b^5*c^3*z^2 + 492441600*b^5*c^3*z + 5055220800*b^5*c^2*z^2 - 2954649600*b^5*c^2*z + 14819414400*b^5*c*z^2 + 6524851200*b^5*c*z - 23267865600*b^5*z^2 - 5170636800*b^5*z - 8187480000*b^4*c^5*z^2 + 70482333600*b^4*c^4*z^2 - 180717899040*b^4*c^3*z^2 + 14250109440*b^4*c^3*z + 772423680*b^4*c^3 + 36293813640*b^4*c^2*z^2 - 85223658240*b^4*c^2*z - 4634542080*b^4*c^2 + 505932451920*b^4*c*z^2 + 187705956480*b^4*c*z + 10234613760*b^4*c - 571405726080*b^4*z^2 - 147964158720*b^4*z - 8110448640*b^4 + 21140028000*b^3*c^6*z^2 - 222435460800*b^3*c^5*z^2 + 492441600*b^3*c^5*z + 662588337600*b^3*c^4*z^2 - 4016476800*b^3*c^4*z + 19496960*b^3*c^4 - 311893620246*b^3*c^3*z^2 + 21989226944*b^3*c^3*z + 6153046016*b^3*c^3 - 1669762792584*b^3*c^2*z^2 - 65230639104*b^3*c^2*z - 36927343616*b^3*c^2 + 2247319802268*b^3*c*z^2 + 97306231168*b^3*c*z + 81135196672*b^3*c - 72427515552*b^3*z^2 - 43958857152*b^3*z - 63228361728*b^3 - 30955176000*b^2*c^7*z^2 + 344207659950*b^2*c^6*z^2 - 1285636800*b^2*c^6*z - 1084000787100*b^2*c^5*z^2 - 47568495360*b^2*c^5*z + 130206720*b^2*c^5 + 510252680286*b^2*c^4*z^2 + 251821281024*b^2*c^4*z - 10785357312*b^2*c^4 + 3244557394368*b^2*c^3*z^2 - 477339651216*b^2*c^3*z + 22430123520*b^2*c^3 - 4819191730551*b^2*c^2*z^2 + 583918363776*b^2*c^2*z + 106414985472*b^2*c^2 - 215239270194*b^2*c*z^2 - 1225517716320*b^2*c*z - 433688799744*b^2*c + 1742244058224*b^2*z^2 + 1553824901952*b^2*z + 439511374080*b^2 + 24030216000*b*c^8*z^2 - 297470530350*b*c^7*z^2 + 1778078400*b*c^7*z + 1208380541760*b*c^6*z^2 + 59465462400*b*c^6*z + 642216960*b*c^6 - 1798890000606*b*c^5*z^2 - 323515238784*b*c^5*z + 1138877952*b*c^5 - 714771999864*b*c^4*z^2 + 400693157904*b*c^4*z - 13697935872*b*c^4 + 4939659515097*b*c^3*z^2 + 748069255008*b*c^3*z + 62643622656*b*c^3 - 4450877240400*b*c^2*z^2 - 2524134749088*b*c^2*z - 272192507904*b*c^2 + 1483856701632*b*c*z^2 + 2955915726336*b*c*z + 668880426240*b*c - 865243337472*b*z^2 - 2358063413568*b*z - 656895868416*b - 10100160000*c^9*z^2 + 139655832750*c^8*z^2 - 1285636800*c^8*z - 708420195000*c^7*z^2 - 42073349760*c^7*z + 149703680*c^7 + 1615681889550*c^6*z^2 + 423616022528*c^6*z - 258182656*c^6 - 955148051088*c^5*z^2 - 1689485424528*c^5*z - 27613855232*c^5 - 3212137216035*c^4*z^2 + 3778685015008*c^4*z + 216602994944*c^4 + 7553824301304*c^3*z^2 - 5431939027760*c^3*z - 702685830656*c^3 - 6585222190671*c^2*z^2 + 5430456316416*c^2*z + 1155134093312*c^2 + 2371765402710*c*z^2 - 3469306079392*c*z - 930052228096*c - 209899613520*z^2 + 1001332164288*z + 288677138304)/46166400) * h0 + ((285012000*c^11*z^3 - 5636131200*c^10*z^3 + 40376599200*c^9*z^3 + 15388800*c^9*z^2 - 147079497600*c^8*z^3 - 153888000*c^8*z^2 + 312594206400*c^7*z^3 - 9530774400*c^7*z^2 - 409655836800*c^6*z^3 + 118316741550*c^6*z^2 - 1285636800*c^6*z + 331086571200*c^5*z^3 - 458039406300*c^5*z^2 - 44644623360*c^5*z + 149703680*c^5 - 153745603200*c^4*z^3 + 576693097800*c^4*z^2 + 335612412608*c^4*z + 41224704*c^4 + 30562509600*c^3*z^3 + 658414678812*c^3*z^2 - 973615975952*c^3*z - 27681109504*c^3 + 2898201600*c^2*z^3 - 2469926374611*c^2*z^2 + 1495840650496*c^2*z + 161199551232*c^2 - 1686031200*c*z^3 + 1950980015670*c*z^2 - 1466641750816*c*z - 352605618688*c - 209660767920*z^2 + 1001332164288*z + 288723304704)/46166400) * h1 + ((3552897600*b^7*c^5*z^3 + 492441600*b^7*c^5*z^2 - 2934187200*b^7*c^4*z^3 - 3508646400*b^7*c^4*z^2 - 29656670400*b^7*c^3*z^3 + 9694944000*b^7*c^3*z^2 + 2398032000*b^7*c^2*z^3 - 11633932800*b^7*c^2*z^2 + 26639928000*b^7*c*z^3 + 5416857600*b^7*c*z^2 + 646329600*b^7*z^2 - 71328932640*b^6*c^5*z^3 + 13142115840*b^6*c^5*z^2 + 772423680*b^6*c^5*z + 278618757480*b^6*c^4*z^3 - 90717540480*b^6*c^4*z^2 - 5406965760*b^6*c^4*z + 130293825480*b^6*c^3*z^3 + 245122053120*b^6*c^3*z^2 + 14869155840*b^6*c^3*z - 847615935600*b^6*c^2*z^3 - 301907088000*b^6*c^2*z^2 - 18345062400*b^6*c^2*z + 510032285280*b^6*c*z^3 + 129697653120*b^6*c*z^2 + 8110448640*b^6*c*z + 2739844800*b^6*z^2 + 19496960*b^5*c^6*z + 126507090474*b^5*c^5*z^3 - 36796230976*b^5*c^5*z^2 + 3816278016*b^5*c^5*z - 1373492811978*b^5*c^4*z^3 + 266647283392*b^5*c^4*z^2 - 26859492352*b^5*c^4*z + 1935037485612*b^5*c^3*z^3 - 733011308288*b^5*c^3*z^2 + 73455072768*b^5*c^3*z + 1037029744980*b^5*c^2*z^3 + 924992137280*b^5*c^2*z^2 - 89328371200*b^5*c^2*z - 1725081509088*b^5*c*z^3 - 428752658208*b^5*c*z^2 + 38897015808*b^5*c*z + 1348754400*b^5*z^2 - 80362393650*b^4*c^8*z^3 - 1778078400*b^4*c^8*z^2 + 983114214390*b^4*c^7*z^3 - 54962222400*b^4*c^7*z^2 - 642216960*b^4*c^7*z - 3955097770254*b^4*c^6*z^3 + 433027002624*b^4*c^6*z^2 - 2477394432*b^4*c^6*z + 7025466709980*b^4*c^5*z^3 - 1434468055632*b^4*c^5*z^2 - 23999456256*b^4*c^5*z - 1396645482825*b^4*c^4*z^3 + 2939836341456*b^4*c^4*z^2 + 307268613888*b^4*c^4*z - 13169521522719*b^4*c^3*z^3 - 4550495700192*b^4*c^3*z^2 - 1020389571840*b^4*c^3*z + 14345023780998*b^4*c^2*z^3 + 4834883001312*b^4*c^2*z^2 + 1393767830784*b^4*c^2*z - 3751977535920*b^4*c*z^3 - 2157981111168*b^4*c*z^2 - 653527805184*b^4*c*z - 2177834400*b^4*z^2 - 2280096000*b^3*c^10*z^3 + 176474185650*b^3*c^9*z^3 + 1285636800*b^3*c^9*z^2 - 1834695027900*b^3*c^8*z^3 + 51633826560*b^3*c^8*z^2 - 149703680*b^3*c^8*z + 6697398948750*b^3*c^7*z^3 - 95058483968*b^3*c^7*z^2 + 3319563776*b^3*c^7*z - 8961255192942*b^3*c^6*z^3 - 920631917360*b^3*c^6*z^2 + 39699870208*b^3*c^6*z - 4781812499631*b^3*c^5*z^3 + 4383623788608*b^3*c^5*z^2 - 214681230592*b^3*c^5*z + 25959996136782*b^3*c^4*z^3 - 8720624542000*b^3*c^4*z^2 + 1103529472*b^3*c^4*z - 20524451381667*b^3*c^3*z^3 + 11723903883104*b^3*c^3*z^2 + 1654184161280*b^3*c^3*z - 836907575490*b^3*c^2*z^3 - 12849154865952*b^3*c^2*z^2 - 3244889750016*b^3*c^2*z + 4107532502448*b^3*c*z^3 + 6435931703808*b^3*c*z^2 + 1761413559552*b^3*c*z - 140414400*b^3*z^2 + 2280096000*b^2*c^11*z^3 - 103899801600*b^2*c^10*z^3 + 956506083750*b^2*c^9*z^3 - 6305073600*b^2*c^9*z^2 - 2985177821850*b^2*c^8*z^3 - 225507681600*b^2*c^8*z^2 + 748518400*b^2*c^8*z + 1675428927660*b^2*c^7*z^3 + 1683375279040*b^2*c^7*z^2 - 3111262720*b^2*c^7*z + 8807703572844*b^2*c^6*z^3 - 4777547087504*b^2*c^6*z^2 - 148131309568*b^2*c^6*z - 14563513523475*b^2*c^5*z^3 + 6982656212752*b^2*c^5*z^2 + 989614628096*b^2*c^5*z - 4450686262335*b^2*c^4*z^3 - 6254863246016*b^2*c^4*z^2 - 2331326364928*b^2*c^4*z + 22693352906934*b^2*c^3*z^3 + 3150510328672*b^2*c^3*z^2 + 1843689317120*b^2*c^3*z - 12856418351208*b^2*c^2*z^3 + 3439438314208*b^2*c^2*z^2 + 800901318016*b^2*c^2*z + 824424173280*b^2*c*z^3 - 3973586737152*b^2*c*z^2 - 1148322201216*b^2*c*z - 23928307200*b^2*z^2 - 5170636800*b^2*z + 3420144000*b*c^11*z^3 - 26257694400*b*c^10*z^3 - 85033179000*b*c^9*z^3 + 5327212800*b*c^9*z^2 + 1036768156200*b*c^8*z^3 + 171681623040*b*c^8*z^2 - 598814720*b*c^8*z - 2347070929200*b*c^7*z^3 - 1515518953472*b*c^7*z^2 + 433915904*b*c^7*z - 1252286167248*b*c^6*z^3 + 5228911378240*b*c^6*z^2 + 110889336832*b*c^6*z + 12106822307292*b*c^5*z^3 - 9879103776192*b*c^5*z^2 - 755522642944*b*c^5*z - 17074990389924*b*c^4*z^3 + 11921602974848*b*c^4*z^2 + 2055713121280*b*c^4*z + 8504539995960*b*c^3*z^3 - 10072906598656*b*c^3*z^2 - 2553035350528*b*c^3*z + 772423680*b*c^3 - 870970337280*b*c^2*z^3 + 4065170593992*b*c^2*z^2 + 1070423611776*b*c^2*z - 4634542080*b*c^2 + 5058093600*b*c*z^3 + 527694415920*b*c*z^2 + 195446522880*b*c*z + 10234613760*b*c - 619782014880*b*z^2 - 158305432320*b*z - 8110448640*b + 1710072000*c^11*z^3 - 32799211200*c^10*z^3 + 217868767200*c^9*z^3 + 92332800*c^9*z^2 - 695452262400*c^8*z^3 - 861772800*c^8*z^2 + 1187644248000*c^7*z^3 + 2785372800*c^7*z^2 - 1056426537600*c^6*z^3 + 9344193600*c^6*z^2 + 331069939200*c^5*z^3 - 166231027200*c^5*z^2 + 492441600*c^5*z + 177203980800*c^4*z^3 + 633274743360*c^4*z^2 + 13234448640*c^4*z + 791920640*c^4 - 160439529600*c^3*z^3 - 708852160686*c^3*z^2 - 51215617216*c^3*z + 3063351296*c^3 + 24562440000*c^2*z^3 - 935495255784*c^2*z^2 - 17363675904*c^2*z - 35961814016*c^2 + 5058093600*c*z^3 + 2606218625628*c*z^2 + 313166219008*c*z + 93493975552*c - 1285197090912*z^2 - 355399084992*z - 79449259008)/46166400) * h2 + (z^2*(41220*b*c^6*z - 328329*b*c^5*z + 419148*b*c^4*z + 1832*b*c^4 + 1173240*b*c^3*z - 6412*b*c^3 - 1204920*b*c^2*z - 1832*b*c^2 - 100359*b*c*z - 7328*b*c - 19236*b - 16965*c^7*z + 267624*c^6*z - 1231083*c^5*z - 916*c^5 + 2156796*c^4*z + 5496*c^4 - 1505655*c^3*z - 6412*c^3 + 228924*c^2*z + 5496*c^2 + 100359*c*z + 1832*c - 14217)/2748) * h3

private lemma rejectI_2_25 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, c) = 0) (h2 : locus b (c, c, b) = 0)
    (h3 : edge b b c (1, 1, c) (c, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((31774682*b^6 + 100787276*b^5 + 638155407*b^4 + 4068418949*b^3 + 24838551842*b^2 + 2889063444*b*c^6 - 33603557662*b*c^5 + 170421953221*b*c^4 - 488313017096*b*c^3 + 854527172885*b*c^2 - 898862466723*b*c + 150050375553*b - 1093904016*c^7 + 9956589064*c^6 - 40783028878*c^5 + 100110095133*c^4 - 157658745776*c^3 + 153197179543*c^2 - 544804285*c + 37055552)/27354) * h1 + ((17824142*b^6*c^2 - 40681420*b^6*c - 26730880*b^6 - 81227618*b^5*c^3 + 152828346*b^5*c^2 + 391308786*b^5*c - 664130352*b^5 + 126806952*b^4*c^4 + 5640776*b^4*c^3 - 2407636999*b^4*c^2 + 5001480398*b^4*c - 2860993936*b^4 - 91158668*b^3*c^5 - 124689858*b^3*c^4 + 4149971209*b^3*c^3 - 14116136088*b^3*c^2 + 20936585267*b^3*c - 16990728228*b^3 + 95234584*b^2*c^5 - 5603005202*b^2*c^4 + 35516866953*b^2*c^3 - 93729400679*b^2*c^2 + 134198199601*b^2*c - 104468211984*b^2 + 598386476*b*c^6 + 428363318*b*c^5 - 22242504357*b*c^4 + 69846902366*b*c^3 - 61834807271*b*c^2 - 71853865426*b*c + 275108805602*b - 364634672*c^7 - 30738344*c^6 + 21933534046*c^5 - 123080143985*c^4 + 328941581044*c^3 - 524277785604*c^2 + 446725104016*c - 149886320712)/27354) * h2 + (-(8912071*b*c^2 - 29252781*b*c + 15887341*b - 22789667*c^3 + 120906917*c^2 - 174577013*c + 37028198)/27354) * h3

private lemma rejectI_2_26 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, 1, c) = 0) (h2 : locus b (c, c, c) = 0)
    (h3 : edge b b c (1, 1, c) (c, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (z*(6*b^5 - 36*b^4 + 30*b^3 - 3*b^2 + 7*b*c^5 - 22*b*c^4 + 54*b*c^3 - 106*b*c^2 - 11*b*c + 6*b - 6*c^6 + 2*c^5 + 59*c^4 - 136*c^3 + 124*c^2 - 50*c + 7)/27) * h1 + (z*(13*b^6*c - 6*b^6 - 6*b^5*c^2 - 126*b^5*c + 42*b^5 + 13*b^4*c^3 + 29*b^4*c^2 + 383*b^4*c - 53*b^4 - 6*b^3*c^4 - 55*b^3*c^3 - 30*b^3*c^2 - 328*b^3*c - 59*b^3 + 31*b^2*c^4 - 50*b^2*c^3 + 165*b^2*c^2 - 238*b^2*c + 95*b^2 + 7*b*c^5 - 26*b*c^4 + 158*b*c^3 - 321*b*c^2 + 243*b*c + 11*b - 6*c^6 + 9*c^5 + 16*c^4 - 40*c^3 + 47*c - 26)/27) * h2 + (-z*(13*b*c - 6*b - 6*c^2 - 22*c + 7)/27) * h3

private lemma rejectI_3_6 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, b, 1) = 0) (h2 : locus b (1, c, 1) = 0)
    (h3 : edge b b c (1, b, 1) (1, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(72*b^6*c^2 - 74*b^6*c - 146*b^6 - 162*b^5*c^3 - 270*b^5*c^2 + 1208*b^5*c + 8*b^5 + 126*b^4*c^4 + 721*b^4*c^3 - 2141*b^4*c^2 + 342*b^4*c - 8*b^4 - 45*b^3*c^5 - 316*b^3*c^4 + 1741*b^3*c^3 - 2258*b^3*c^2 + 1226*b^3*c - 868*b^3 - 63*b^2*c^5 - 2165*b^2*c^4 + 8405*b^2*c^3 - 11212*b^2*c^2 + 8978*b^2*c - 3464*b^2 + 171*b*c^6 + 1172*b*c^5 - 7407*b*c^4 + 12493*b*c^3 - 4555*b*c^2 - 11590*b*c + 11254*b - 45*c^7 - 505*c^6 + 4948*c^5 - 17682*c^4 + 35242*c^3 - 40831*c^2 + 25370*c - 6490)/4) * h1 + (-(261*b*c^5 - 2822*b*c^4 + 13706*b*c^3 - 35275*b*c^2 + 46276*b*c - 24242*b - 45*c^6 + 80*c^5 + 641*c^4 - 3746*c^3 + 9549*c^2 - 12398*c + 6486)/4) * h2 + ((36*b*c - 73*b - 45*c^2 + 125*c - 69)/4) * h3

private lemma rejectI_3_7 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, b, 1) = 0) (h2 : locus b (1, c, b) = 0)
    (h3 : edge b b c (1, b, 1) (1, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (c^2*z*(4*b - c)*(c - 3)) * h1 + (-z*(b^3*c - b^3 - b^2*c^2 + b^2 + 4*b*c^2 - 12*b*c - c^2 + 3*c)) * h2

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
  linear_combination ((851392543110912*b*c*z + 214484812474944*b*c - 1303748682122088*b*z + 422738309272314*b - 743103431316*c^2*z - 187204364667*c^2 - 3167122170548556*c*z - 820411429172469*c + 4831117383232944*z - 1399508996973212)/2601785587623728) * h0 + (-(424953168124140*b^2*c^5*z^2 - 128453807803251*b^2*c^5*z - 90939116597682*b^2*c^5 - 5066641041638904*b^2*c^4*z^2 + 5086430149110550*b^2*c^4*z + 2170903085749908*b^2*c^4 + 13941083973181536*b^2*c^3*z^2 - 53951082036954024*b^2*c^3*z - 18365408384415768*b^2*c^3 - 13728146123532456*b^2*c^2*z^2 + 205002142550872082*b^2*c^2*z + 66774388591496448*b^2*c^2 + 2073819626711604*b^2*c*z^2 - 333854458284845877*b^2*c*z - 107089787421383430*b^2*c + 2578595019349536*b^2*z^2 + 201109499640549224*b^2*z + 64231142702723820*b^2 + 852878749973544*b*c^5*z^2 + 685877240556390*b*c^5*z + 181878233195364*b*c^5 + 719102994734232*b*c^4*z^2 - 11042138953288022*b*c^4*z - 4341806171499816*b*c^4 - 5248696156081272*b*c^3*z^2 + 110555951060912142*b*c^3*z + 37822086168003720*b*c^3 + 1448862955832520*b*c^2*z^2 - 441883436249931970*b*c^2*z - 145413112022753400*b*c^2 + 7496873805337776*b*c*z^2 + 749095427440149716*b*c*z + 241406180635061628*b*c - 5716351594187712*b*z^2 - 452023738240592352*b*z - 143982106399838076*b - 426439374986772*c^6*z^2 + 128079399073917*c^6*z + 90939116597682*c^6 - 836705303883540*c^5*z^2 - 6854209180341403*c^5*z - 2261842202347590*c^5 + 10880159443643160*c^4*z^2 + 60572091894485346*c^4*z + 20172555003774948*c^4 - 24201046955095272*c^3*z^2 - 245776576598029182*c^3*z - 81912531628773504*c^3 + 23371899444687708*c^2*z^2 + 525418342908036473*c^2*z + 172091936531304078*c^2 - 11590126895910276*c*z^2 - 565213703035832927*c*z - 182093621155966236*c + 2914091952642720*z^2 + 236452158670649600*z + 75648960835541118)/5203571175247456) * h1 + (-(-5652216232225344*b^6*c*z - 2182538798344368*b^6*c + 670993866586368*b^6*z^2 + 53968345891513152*b^6*z + 17181053284487904*b^6 + 9420360387042240*b^5*c^2*z + 3637564663907280*b^5*c^2 - 1118323110977280*b^5*c*z^2 - 86179098997705024*b^5*c*z - 27180062941916928*b^5*c - 447329244390912*b^5*z^2 - 35978897261008768*b^5*z - 11454035522991936*b^5 - 3768144154816896*b^4*c^3*z - 1455025865562912*b^4*c^3 + 447329244390912*b^4*c^2*z^2 + 14312068370811616*b^4*c^2*z + 3087636796005192*b^4*c^2 + 2572143155247744*b^4*c*z^2 + 249270280992490496*b^4*c*z + 82229745244786392*b^4*c - 5032453999397760*b^4*z^2 - 404762594186348640*b^4*z - 128857899633659280*b^4 - 851392543110912*b^3*c^3*z^2 + 9676893593919408*b^3*c^3*z + 3819442897102644*b^3*c^3 + 980901958706856*b^3*c^2*z^2 - 105015255232691850*b^3*c^2*z - 34068164378151840*b^3*c^2 - 73593260047080*b^3*c*z^2 + 64038354325638026*b^3*c*z + 17857730198575524*b^3*c + 4193711666164800*b^3*z^2 + 337302161821957200*b^3*z + 107381583028049400*b^3 + 426439374986772*b^2*c^4*z^2 + 3640064755742979*b^2*c^4*z + 1364086748965230*b^2*c^4 + 4649311188772452*b^2*c^3*z^2 - 59609722497425481*b^2*c^3*z - 21378034944733734*b^2*c^3 - 11618264401427412*b^2*c^2*z^2 + 348740036346786101*b^2*c^2*z + 116404777620446370*b^2*c^2 - 642712150360836*b^2*c*z^2 - 889522136634141415*b^2*c*z - 287646404340550398*b^2*c + 9421872209983584*b^2*z^2 + 757805523559997176*b^2*z + 241250623203017652*b^2 - 1705757499947088*b*c^4*z^2 - 7023970713338124*b*c^4*z - 2546295264735096*b*c^4 - 6716556476620056*b*c^3*z^2 + 105170022229757206*b*c^3*z + 37686750785186196*b*c^3 + 22127594438727144*b*c^2*z^2 - 550334955901445098*b*c^2*z - 182530956683164584*b*c^2 - 4797406758952512*b*c*z^2 + 1181712654165728528*b*c*z + 380906103494807700*b*c - 11256352236259776*b*z^2 - 902209554417126224*b*z - 287325800348025984*b - 942036038704224*c^5*z - 363756466390728*c^5 + 538271686084500*c^4*z^2 + 18287005303220515*c^4*z + 6410134428057582*c^4 + 571260942879804*c^3*z^2 - 120088598279793087*c^3*z - 40741627027566006*c^3 - 3565970578104372*c^2*z^2 + 371372931350515325*c^2*z + 121945623980430978*c^2 - 1395324919629756*c*z^2 - 556633502150511561*c*z - 178917566236250694*c + 4243175957611872*z^2 + 329547962739024800*z + 105211054351028826)/5203571175247456) * h2 + ((-8089201404*c*z - 3123552813*c + 960296688*z^2 + 77237105132*z + 24588762114)/44682722876) * h3

private lemma rejectI_3_17 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, b, 1) = 0) (h2 : locus b (b, c, c) = 0)
    (h3 : edge b b c (1, b, 1) (b, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(46*c - 11)*(b - c + 2)/3) * h0 + ((46*b^2*c^5*z - 2*b^2*c^5 - 241*b^2*c^4*z + 31*b^2*c^4 + 193*b^2*c^3*z - 166*b^2*c^3 + 13*b^2*c^2*z + 372*b^2*c^2 - 11*b^2*c*z - 394*b^2*c + 391*b^2 - 46*b*c^6*z + 2*b*c^6 + 333*b*c^5*z - 33*b*c^5 - 767*b*c^4*z + 199*b*c^4 + 763*b*c^3*z - 551*b*c^3 - 327*b*c^2*z + 739*b*c^2 + 44*b*c*z - 542*b*c - 212*b + 92*c^2 - 210*c + 72)/6) * h1 + (-(24*b^6*c - 132*b^6 - 60*b^5*c^2 + 334*b^5*c - 22*b^5 + 56*b^4*c^3 - 300*b^4*c^2 - 180*b^4*c + 748*b^4 - 24*b^3*c^4 + 46*b^3*c^3*z + 122*b^3*c^3 - 57*b^3*c^2*z + 239*b^3*c^2 + 11*b^3*c*z - 1010*b^3*c - 11*b^3 + 4*b^2*c^5 - 46*b^2*c^4*z - 16*b^2*c^4 - 35*b^2*c^3*z - 115*b^2*c^3 + 103*b^2*c^2*z + 403*b^2*c^2 - 22*b^2*c*z + 464*b^2*c - 1100*b^2 + 184*b*c^4*z - 8*b*c^4 - 642*b*c^3*z + 130*b*c^3 + 557*b*c^2*z - 625*b*c^2 - 99*b*c*z + 822*b*c + 157*b - 46*c^4*z + 2*c^4 + 241*c^3*z - 29*c^3 - 239*c^2*z + 139*c^2 + 44*c*z - 232*c - 302)/6) * h2 + ((2*c - 11)/3) * h3

private lemma rejectI_3_20 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, b, 1) = 0) (h2 : locus b (c, 1, c) = 0)
    (h3 : edge b b c (1, b, 1) (c, 1, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(92*b^6 - 914*b^5 + 3204*b^4 - 4370*b^3 - 408*b^2 - 35*b*c^6 - 351*b*c^5 + 4050*b*c^4 - 13849*b*c^3 + 21572*b*c^2 - 14703*b*c + 9086*b + 70*c^6 + 1906*c^5 - 17657*c^4 + 55712*c^3 - 82501*c^2 + 57109*c - 14384)/66) * h1 + ((210*b^6*c + 118*b^6 + 140*b^5*c^2 - 2054*b^5*c - 1792*b^5 + 35*b^4*c^3 - 853*b^4*c^2 + 4968*b^4*c + 9376*b^4 - 35*b^3*c^4 + 104*b^3*c^3 - 1446*b^3*c^2 + 4923*b^3*c - 19172*b^3 + 280*b^2*c^4 - 3373*b^2*c^3 + 14049*b^2*c^2 - 19671*b^2*c + 3840*b^2 - 70*b*c^5 - 1696*b*c^4 + 12287*b*c^3 - 20957*b*c^2 - 5169*b*c + 29118*b - 35*c^6 - 71*c^5 + 3050*c^4 - 13203*c^3 + 19947*c^2 - 7111*c - 5678)/66) * h2 + (-(105*b*c - 46*b - 35*c^2 - 421*c + 135)/66) * h3

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
  linear_combination ((b - 3)*(b + 3)/9) * h0 + ((240*b^6*c - 1040*b^6 - 276*b^5*c^2 + 776*b^5*c + 1820*b^5 + 102*b^4*c^3 + 216*b^4*c^2*z - 295*b^4*c^2 - 216*b^4*c*z - 31*b^4*c - 2626*b^4 - 12*b^3*c^4 - 216*b^3*c^3*z + 322*b^3*c^3 - 216*b^3*c^2*z - 2151*b^3*c^2 + 432*b^3*c*z + 5103*b^3*c - 3692*b^3 - 141*b^2*c^4 + 432*b^2*c^3*z + 866*b^2*c^3 - 2808*b^2*c^2*z - 835*b^2*c^2 + 2376*b^2*c*z - 3351*b^2*c + 9937*b^2 + 12*b*c^5 - 133*b*c^4 + 2376*b*c^3*z + 732*b*c^3 + 216*b*c^2*z - 2245*b*c^2 - 2592*b*c*z + 2766*b*c - 1156*b + 63*c^5 - 732*c^4 - 2592*c^3*z + 3450*c^3 + 2592*c^2*z - 8209*c^2 + 8681*c - 3325)/1944) * h1 + (-(12*b^2*c^4 - 199*b^2*c^3 + 1516*b^2*c^2 - 5939*b^2*c + 9473*b^2 - 6*b*c^4 + 32*b*c^3 - 20*b*c^2 - 32*b*c + 26*b - 3*c^5 + 25*c^4 - 70*c^3 + 90*c^2 - 55*c + 13)/1944) * h2 + (-(3*c - 13)/1944) * h3

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
  linear_combination ((74*b^4*c^3 - 108*b^4*c^2 - 182*b^4*c + 185*b^3*c^4 - 899*b^3*c^3 + 463*b^3*c^2 + 1547*b^3*c + 222*b^2*c^5 - 1397*b^2*c^4 + 2389*b^2*c^3 + 752*b^2*c^2 - 3603*b^2*c - 91*b^2 + 148*b*c^6 - 1030*b*c^5 + 1897*b*c^4 + 658*b*c^3 - 3973*b*c^2 + 1187*b*c + 654*b + 100*c^4 - 298*c^3 + 211*c^2 - 55*c - 453)/144) * h1 + ((37*b^2*c^5 - 17*b^2*c^4 - 145*b^2*c^3 + 290*b^2*c^2 - 371*b^2*c - 199*b^2 + 74*b*c^3 - 696*b*c^2 + 1268*b*c + 470*b + 37*c + 53)/144) * h2 + (-(37*c - 91)/144) * h3

private lemma rejectI_5_16 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, b, c) = 0) (h2 : locus b (b, c, b) = 0)
    (h3 : edge b b c (1, b, c) (b, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((-2268973*b*c^3 + 596241*b*c^2*z + 6613075*b*c^2 + 1254834*b*c + 2268973*c^4 - 596241*c^3*z - 4344102*c^3 - 596241*c^2*z - 7867909*c^2 - 93528)/93528) * h0 + ((-183786813*b^2*c^6*z + 3203256*b^2*c^6 + 48295521*b^2*c^5*z^2 + 351030510*b^2*c^5*z + 49248934*b^2*c^5 + 48295521*b^2*c^4*z^2 + 1024164405*b^2*c^4*z - 126315448*b^2*c^4 - 96591042*b^2*c^3*z^2 - 446106852*b^2*c^3*z - 68684049*b^2*c^3 + 480956049*b^2*c^2*z + 108736824*b^2*c^2 - 409407129*b^2*c*z - 8649081*b^2*c + 11363652*b^2*z - 608423508*b^2 - 533876*b*c^7 + 1286647983*b*c^6*z - 46469269*b*c^6 - 338068647*b*c^5*z^2 - 5213068794*b*c^5*z - 68884655*b*c^5 + 386364168*b*c^4*z^2 + 3292009533*b*c^4*z + 538628720*b*c^4 - 48295521*b*c^3*z^2 - 1590584769*b*c^3*z - 186536049*b*c^3 - 974643597*b*c^2*z - 78985956*b*c^2 + 536301243*b*c*z - 219025044*b*c + 36931869*b*z + 1211843619*b - 183786813*c^7*z + 10677520*c^7 + 48295521*c^6*z^2 + 716640048*c^6*z + 19660676*c^6 - 48295521*c^5*z^2 - 331744653*c^5*z - 96018468*c^5 + 442971990*c^4*z - 84941346*c^4 + 357323724*c^3*z + 183055068*c^3 - 11363652*c^2*z - 180100557*c^2 + 144886563*c*z + 2095688700*c - 48295521*z - 637300629)/7575768) * h1 + ((3203256*b^4*c^4 - 841752*b^4*c^3*z - 2537038*b^4*c^3 + 32898474*b^4*c^2*z - 13137761*b^4*c^2 + 74389833*b^4*c*z - 391713*b^4*c + 34722270*b^4*z + 4193406*b^4 - 183786813*b^3*c^5*z + 3737132*b^3*c^5 + 48295521*b^3*c^4*z^2 + 718463844*b^3*c^4*z - 25471649*b^3*c^4 - 48295521*b^3*c^3*z^2 - 389720322*b^3*c^3*z + 22448552*b^3*c^3 - 251298045*b^3*c^2*z + 53767882*b^3*c^2 - 271570239*b^3*c*z - 28109634*b^3*c - 17361135*b^3*z - 2096703*b^3 + 367573626*b^2*c^6*z - 8008140*b^2*c^6 - 96591042*b^2*c^5*z^2 - 701640144*b^2*c^5*z - 21685895*b^2*c^5 - 96591042*b^2*c^4*z^2 - 2084629365*b^2*c^4*z + 113636376*b^2*c^4 + 193182084*b^2*c^3*z^2 + 1551761469*b^2*c^3*z - 20852720*b^2*c^3 + 185150367*b^2*c^2*z - 40153883*b^2*c^2 + 100589364*b^2*c*z + 15921129*b^2*c - 17361135*b^2*z - 2096703*b^2 + 533876*b*c^7 - 1470434796*b*c^6*z + 31520741*b*c^6 + 386364168*b*c^5*z^2 + 5752656045*b*c^5*z + 38370003*b*c^5 - 386364168*b*c^4*z^2 - 3148977546*b*c^4*z - 286873664*b*c^4 + 231551946*b*c^3*z - 46976741*b*c^3 + 1311975711*b*c^2*z + 121187598*b*c^2 - 190341171*b*c*z + 589553181*b*c + 183786813*c^7*z - 10677520*c^7 - 48295521*c^6*z^2 - 716640048*c^6*z + 14507388*c^6 + 48295521*c^5*z^2 + 322765965*c^5*z - 5074076*c^5 - 72601110*c^4*z + 129671010*c^4 - 357323724*c^3*z - 183055068*c^3 + 11363652*c^2*z + 363887370*c^2 - 193182084*c*z - 2447560962*c)/7575768) * h2 + ((-533876*c^2 + 140292*c*z + 1579571*c - 5787045*z - 698901)/7575768) * h3

private lemma rejectI_5_19 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, b, c) = 0) (h2 : locus b (c, 1, b) = 0)
    (h3 : edge b b c (1, b, c) (c, 1, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((-100555*b^2*c^2 + 803439*b^2*c*z + 431145*b^2*c - 803439*b^2*z - 507170*b^2 + 200005*b*c^3 - 1598049*b*c^2*z - 656260*b*c^2 - 88290*b*c*z + 145010*b*c + 1606878*b*z + 1014340*b - 99450*c^4 + 794610*c^3*z + 226220*c^3 + 882900*c^2*z + 256685*c^2 - 715149*c*z - 46415*c - 803439*z - 2732078)/2224908) * h0 + ((-1105*b^6*c^2 + 8829*b^6*c*z + 3815*b^6*c - 79461*b^6*z - 2120*b^6 - 100555*b^5*c^3*z + 1105*b^5*c^3 + 803439*b^5*c^2*z^2 + 522871*b^5*c^2*z + 16075*b^5*c^2 - 1606878*b^5*c*z^2 - 929486*b^5*c*z - 69455*b^5*c + 803439*b^5*z^2 + 1840349*b^5*z + 68360*b^5 + 300560*b^4*c^4*z + 8840*b^4*c^4 - 2401488*b^4*c^3*z^2 - 1358042*b^4*c^3*z - 81350*b^4*c^3 + 2313198*b^4*c^2*z^2 + 2249707*b^4*c^2*z + 125045*b^4*c^2 + 2498607*b^4*c*z^2 - 1727872*b^4*c*z + 182015*b^4*c - 2410317*b^4*z^2 - 8982015*b^4*z - 489480*b^4 - 299455*b^3*c^5*z - 2210*b^3*c^5 + 2392659*b^3*c^4*z^2 + 999588*b^3*c^4*z - 53145*b^3*c^4 + 176580*b^3*c^3*z^2 + 412133*b^3*c^3*z + 563605*b^3*c^3 - 4802976*b^3*c^2*z^2 - 9469521*b^3*c^2*z - 1518535*b^3*c^2 - 176580*b^3*c*z^2 + 20653130*b^3*c*z + 1069975*b^3*c + 2410317*b^3*z^2 + 18305439*b^3*z + 1030200*b^3 + 99450*b^2*c^6*z - 17680*b^2*c^6 - 794610*b^2*c^5*z^2 - 185511*b^2*c^5*z + 188115*b^2*c^5 - 79461*b^2*c^4*z^2 - 1809481*b^2*c^4*z - 717955*b^2*c^4 - 2507436*b^2*c^3*z^2 + 7424633*b^2*c^3*z + 811235*b^2*c^3 + 7310412*b^2*c^2*z^2 + 421935*b^2*c^2*z + 948300*b^2*c^2 - 3125466*b^2*c*z^2 - 34323515*b^2*c*z - 2049225*b^2*c - 803439*b^2*z^2 - 14253923*b^2*z - 813320*b^2 - 8840*b*c^7 + 270637*b*c^6*z + 90190*b*c^6 - 1598049*b*c^5*z^2 - 2871504*b*c^5*z - 400875*b*c^5 + 8723052*b*c^4*z^2 + 10483323*b*c^4*z + 1038130*b*c^4 - 11795544*b*c^3*z^2 - 17391540*b*c^3*z - 1417995*b*c^3 + 88290*b*c^2*z^2 + 13538939*b*c^2*z + 524085*b*c^2 + 4820634*b*c*z^2 + 18326019*b*c*z + 778265*b*c + 1986525*b*z + 52530*b - 1105*c^6 + 8829*c^5*z - 10550*c^5 + 235321*c^4*z + 76205*c^4 - 1598049*c^3*z^2 - 2509872*c^3*z - 231030*c^3 + 3928905*c^2*z^2 + 3995903*c^2*z + 313685*c^2 - 2410317*c*z^2 - 6245025*c*z - 293595*c + 1986525*z + 484420)/2224908) * h1 + ((-88290*b^6*z - 7040*b^6 + 971190*b^5*z + 77440*b^5 - 3355020*b^4*z - 267520*b^4 + 3884760*b^3*z + 309760*b^3 - 2030670*b^2*z - 161920*b^2 - 99450*b*c^6*z - 30940*b*c^6 + 794610*b*c^5*z^2 + 1473457*b*c^5*z + 237210*b*c^5 - 7107345*b*c^4*z^2 - 8403000*b*c^4*z - 785780*b*c^4 + 15715620*b*c^3*z^2 + 18844208*b*c^3*z + 1362600*b*c^3 - 9641268*b*c^2*z^2 - 21042366*b*c^2*z - 1315155*b*c^2 + 8890803*b*c*z + 823230*b*c + 706320*b*z + 56320*b + 8840*c^7 - 270637*c^6*z - 70300*c^6 + 1598049*c^5*z^2 + 2112567*c^5*z + 240490*c^5 - 3928905*c^4*z^2 - 5143673*c^4*z - 436910*c^4 + 2410317*c^3*z^2 + 5406270*c^3*z + 446185*c^3 - 2375001*c^2*z - 304920*c^2 - 1236060*c*z - 83735*c - 891729*z - 514210)/2224908) * h2 + (-(-1105*c^2 + 8829*c*z + 4920*c - 88290*z - 7040)/2224908) * h3

private lemma rejectI_5_22 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, b, c) = 0) (h2 : locus b (c, b, b) = 0)
    (h3 : edge b b c (1, b, c) (c, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(32405345*b^2*c + 1877085*b*c^3 + 9876015*b*c^2 - 147243794*b*c - 9625092*c^3 + 40132448*c^2 + 4824)/4824) * h0 + ((1877085*b^2*c^6*z - 370670*b^2*c^6 + 34773020*b^2*c^5*z + 4955096*b^2*c^5 - 242173119*b^2*c^4*z - 27361005*b^2*c^4 + 426310415*b^2*c^3*z + 76218359*b^2*c^3 - 105950560*b^2*c^2*z - 108656006*b^2*c^2 - 114841665*b^2*c*z + 63428513*b^2*c + 4824*b^2*z - 20424867*b^2 - 370670*b*c^7 - 42030437*b*c^6*z + 5014073*b*c^6 + 267433631*b*c^5*z - 29255072*b*c^5 - 664959936*b*c^4*z + 98867884*b*c^4 + 810587216*b*c^3*z - 205580178*b*c^3 - 485881787*b*c^2*z + 248694148*b*c^2 + 114856137*b*c*z - 106503617*b*c - 4824*b*z + 22277832*b + 658502*c^5 - 2572679*c^4 + 9625092*c - 40132448)/4824) * h1 + (-(-370670*b^5*c^2 + 2565400*b^5*c - 4360170*b^5 - 370670*b^4*c^4 + 32405345*b^4*c^3*z + 4974755*b^4*c^3 - 32405345*b^4*c^2*z - 19532931*b^4*c^2 + 17962035*b^4*c + 17616159*b^4 + 1877085*b^3*c^5*z + 741340*b^3*c^5 + 7998930*b^3*c^4*z - 7335161*b^3*c^4 - 254335844*b^3*c^3*z + 15620079*b^3*c^3 + 244459829*b^3*c^2*z + 32497007*b^3*c^2 - 99249081*b^3*c - 5537952*b^3 - 370670*b^2*c^6 - 47661692*b^2*c^5*z + 3823427*b^2*c^5 + 187787475*b^2*c^4*z - 8005992*b^2*c^4 + 204389564*b^2*c^3*z - 20671045*b^2*c^3 - 344510523*b^2*c^2*z + 53647234*b^2*c^2 - 4824*b^2*c*z + 31886987*b^2*c - 7718037*b^2 + 1877085*b*c^6*z + 741340*b*c^6 + 164618501*b*c^5*z - 16877137*b*c^5 - 846735475*b*c^4*z + 114616793*b*c^4 + 1139592077*b*c^3*z - 315067845*b*c^3 - 459371484*b*c^2*z + 315555376*b*c^2 + 19296*b*c*z - 70266435*b*c - 370670*c^7 - 42030437*c^6*z + 4272733*c^6 + 183372757*c^5*z - 24104613*c^5 - 256183985*c^4*z + 70972834*c^4 + 114846489*c^3*z - 77461580*c^3 - 4824*c^2*z + 20225475*c^2 + 13285998*c)/4824) * h2 + ((185335*b*c - 726695*b - 658502*c + 2572679)/4824) * h3

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
  linear_combination (-(5170329025*b^2 + 10789872225*b*c - 5490351581*b + 2413768106*c^2 + 9863307350)/9863307350) * h0 + (-(-390030450*b^5*c^2 + 64470481025*b^5*c*z - 1010974450*b^5*c + 24479746975*b^5*z - 310472000*b^5 - 390030450*b^4*c^3 + 64919695200*b^4*c^2*z + 1524223475*b^4*c^2 - 342431059806*b^4*c*z + 5755374700*b^4*c - 137589699394*b^4*z + 1357344775*b^4 - 8376104119*b^3*c^3*z + 1950152250*b^3*c^3 - 293424176525*b^3*c^2*z + 764537300*b^3*c^2 + 406104167575*b^3*c*z - 8131455725*b^3*c + 221846949069*b^3*z - 1898730325*b^3 - 2413768106*b^2*c^4*z - 585045675*b^2*c^4 + 94120557025*b^2*c^3*z - 3271598700*b^2*c^3 + 327670056656*b^2*c^2*z - 5870831475*b^2*c^2 + 252711595075*b^2*c*z - 1118669425*b^2*c - 79086920650*b^2*z + 736400775*b^2 + 9655072424*b*c^4*z + 1755137025*b*c^4 - 155928102302*b*c^3*z + 2989263225*b*c^3 - 358876041679*b*c^2*z + 1090532900*b*c^2 - 280577942443*b*c*z + 728638975*b*c + 88950228000*b*z - 6296760250*b - 195015225*c^5 + 29650076000*c^4*z - 310472000*c^4 + 2413768106)/9863307350) * h1 + (-(29650076000*b^5*z - 310472000*b^5 - 207550532000*b^4*z + 2173304000*b^4 + 385450988000*b^3*z - 4036136000*b^3 - 88950228000*b^2*z + 931416000*b^2 + 1134799801*b*c^4*z - 138891106079*b*c^3*z + 271181648278*b*c^2*z - 469588900*b*c^2 + 355800912000*b*c*z - 1429141425*b*c + 5170329025*b + 2413768106*c^5*z + 28334087451*c^4*z - 75222969557*c^3*z + 195015225*c^3 - 88950228000*c^2*z + 230913550*c^2 - 1516461675*c - 5490351581)/9863307350) * h2 + ((-201*c + 30560*z - 320)/10166) * h3

private lemma rejectI_6_7 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, c, 1) = 0) (h2 : locus b (1, c, b) = 0)
    (h3 : edge b b c (1, c, 1) (1, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-z*(6*b^6 - 36*b^5 + 45*b^4 + 33*b^3 - 24*b^2 + 2*b*c^3 - 54*b*c^2 + 142*b*c + 3*b + 11*c^3 - 34*c^2 - c)/3) * h1 + (-z*(6*b^6 - 2*b^5*c - 32*b^5 + 53*b^4 + 2*b^3*c^2 + 8*b^3*c - 6*b^3 + 5*b^2*c^2 - 29*b^2*c - 11*b^2 - 2*b*c^3 + 25*b*c^2 - 40*b*c - 42*b - 11*c^3 + 56*c^2 - 78*c + 32)/3) * h2 + (z*(3*b - c)/3) * h3

private lemma rejectI_6_10 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, c, 1) = 0) (h2 : locus b (b, 1, b) = 0)
    (h3 : edge b b c (1, c, 1) (b, 1, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((24244706767312457*b^2*c^6 - 496594768973895118*b^2*c^5 + 2243522543236344590*b^2*c^4 - 3085335399876391092*b^2*c^3 - 991148448739675172*b^2*c^2 + 2233647427131424570*b^2*c + 29518486573513718*b^2 - 22697111103312797*b*c^6 + 163518431552269901*b*c^5 - 444272964578650155*b*c^4 - 171650486477371549*b*c^3 + 4496627026175110561*b*c^2 - 3058702239229548982*b*c - 66040333051871900*b + 24244706767312457*c^7 - 367702669721250691*c^6 + 2550929689591423977*c^5 - 9651114594943107330*c^4 + 20170667843559669478*c^3 - 23029520420599342093*c^2 + 12585966317819963174*c - 2808143978518331902)/216446596502295000) * h1 + ((17676326062464030*b^6*c^2 - 31817386912435254*b^6*c - 49493712974899284*b^6 - 173186136748036306*b^5*c^3 + 272023738510858148*b^5*c^2 + 479984377509982954*b^5*c + 169114580325815128*b^5 - 133534886244643407*b^4*c^4 + 1510329511391270949*b^4*c^3 - 1586701322859335282*b^4*c^2 - 3061881195706016462*b^4*c + 929372044864245006*b^4 - 46941817870625254*b^3*c^5 + 98255759403429827*b^3*c^4 - 181405543597015587*b^3*c^3 - 4355323536549709934*b^3*c^2 + 8212724924350075218*b^3*c - 3708423262776439006*b^3 + 24244706767312457*b^2*c^6 - 630955064220154257*b^2*c^5 + 5248224626870970407*b^2*c^4 - 14709182175828741969*b^2*c^3 + 17313269229893474299*b^2*c^2 - 113328271786616224*b^2*c - 197251053508134060*b^2 - 371339166925768997*b*c^6 + 3245987408886649334*b*c^5 - 8206597530161278600*b*c^4 - 4212683168777758920*b*c^3 + 35520473836775008905*b*c^2 - 38023584465889134168*b*c + 8984471292375837772*b + 50037009198624574*c^7 - 1243593407325012352*c^6 + 9632331766771228777*c^5 - 34275624164275099145*c^4 + 65133244941664616922*c^3 - 66847360956719498297*c^2 + 33573331844690298526*c - 5639439691311515882)/216446596502295000) * h2 + (-(8838163031232015*b^2*c - 24746856487449642*b^2 - 95431231405250168*b*c^2 + 309218935335520974*b*c - 138164418224139214*b + 24244706767312457*c^3 - 125255602048126121*c^2 + 402867114383601518*c - 135375472911439731)/216446596502295000) * h3

private lemma rejectI_6_11 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, c, 1) = 0) (h2 : locus b (b, 1, c) = 0)
    (h3 : edge b b c (1, c, 1) (b, 1, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((c - 4)*(5*b*c + 2*c^2 + 4*c + 18)/72) * h0 + (-(324*b^2*c^6*z - 1188*b^2*c^5*z - b^2*c^5 - 5508*b^2*c^4*z + 61*b^2*c^4 + 10692*b^2*c^3*z - 20*b^2*c^3 - 9504*b^2*c^2*z - 404*b^2*c^2 + 36288*b^2*c*z + 517*b^2*c - 31104*b^2*z + 39*b^2 - 648*b*c^6*z + 3672*b*c^5*z - 14*b*c^5 - 10584*b*c^4*z - 410*b*c^4 + 28296*b*c^3*z + 1784*b*c^3 + 20736*b*c^2*z - 2600*b*c^2 - 57024*b*c*z + 1894*b*c + 15552*b*z - 3102*b - 324*c^7*z + 2376*c^6*z + c^6 - 3024*c^5*z + 98*c^5 + 648*c^4*z - 223*c^4 - 18252*c^3*z - 16*c^3 + 52272*c^2*z + 487*c^2 - 49248*c*z - 1250*c + 15552*z - 1257)/31104) * h1 + ((-16*b^6 - 24*b^5*c + 72*b^5 + 28*b^4*c^2 + 48*b^4*c - 4*b^4 + 1080*b^3*c^4*z - 5400*b^3*c^3*z + 38*b^3*c^3 + 4320*b^3*c^2*z - 302*b^3*c^2 + 470*b^3*c - 382*b^3 - 108*b^2*c^5*z - 2376*b^2*c^4*z - 13*b^2*c^4 + 18036*b^2*c^3*z - 202*b^2*c^3 - 31104*b^2*c^2*z + 826*b^2*c^2 + 15552*b^2*c*z - 1226*b^2*c + 447*b^2 - 324*b*c^6*z + 2592*b*c^5*z - 15*b*c^5 - 14796*b*c^4*z + 256*b*c^4 + 26352*b*c^3*z - 440*b*c^3 + 38016*b*c^2*z + 428*b*c^2 - 36288*b*c*z - 521*b*c - 15552*b*z + 436*b - 324*c^7*z + 2376*c^6*z + c^6 - 3024*c^5*z + 98*c^5 + 648*c^4*z - 1247*c^4 - 18252*c^3*z + 4080*c^3 + 52272*c^2*z - 5657*c^2 - 49248*c*z + 3710*c + 15552*z - 2281)/31104) * h2 + (1/1944) * h3

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
  linear_combination (-1) * h0 + (-z*(9*b^4 - 81*b^3 + 242*b^2 + 164*b*c^4 - 517*b*c^3 + 523*b*c^2 - 119*b*c - 218*b + 48*c^5 - 708*c^4 + 1891*c^3 - 1860*c^2 + 639*c - 10)/16) * h1 + (-z*(3*b^6 + b^5*c - 37*b^5 + 12*b^4*c^2 - 24*b^4*c + 147*b^4 + 4*b^3*c^3 - 93*b^3*c^2 + 139*b^3*c - 161*b^3 + 20*b^2*c^3 - 39*b^2*c^2 + 157*b^2*c - 380*b^2 + 60*b*c^4 - 531*b*c^3 + 1623*b*c^2 - 2015*b*c + 1030*b + 16*c^5 - 188*c^4 + 1053*c^3 - 2236*c^2 + 1985*c - 630)/16) * h2 + (z*(3*b + c - 10)/16) * h3

private lemma rejectI_7_10 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, c, b) = 0) (h2 : locus b (b, 1, b) = 0)
    (h3 : edge b b c (1, c, b) (b, 1, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(1391093*b*c - 583253*c^2 - 996107*c + 2387200)/2387200) * h0 + ((323866587*b^2*c^4 + 61950000*b^2*c^3*z - 462980819*b^2*c^3 - 591390125*b^2*c^2*z - 1528103065*b^2*c^2 + 220715125*b^2*c*z + 1807092478*b^2*c + 319050000*b^2*z - 709094970*b^2 - 581044116*b*c^4 + 448396375*b*c^3*z + 1094870109*b*c^3 - 422245250*b*c^2*z + 4092954130*b*c^2 - 612626125*b*c*z - 3968087434*b*c + 638100000*b*z - 256815670*b + 107955529*c^5 + 20650000*c^4*z - 364956703*c^4 - 342619875*c^3*z - 61482007*c^3 + 520726125*c^2*z + 220635420*c^2 + 89318750*c*z - 372994587*c - 277750000*z + 511959300)/298400000) * h1 + ((-514355058*b^7 - 1584331645*b^6*c + 41300000*b^6*z + 3908860819*b^6 - 1044554000*b^5*c^2 + 144550000*b^5*c*z + 10605937051*b^5*c - 268450000*b^5*z - 10619887406*b^5 + 241333645*b^4*c^3 + 144550000*b^4*c^2*z + 4198607891*b^4*c^2 - 805350000*b^4*c*z - 22515424710*b^4*c + 557550000*b^4*z + 12006982710*b^4 + 215911058*b^3*c^4 - 132586625*b^3*c^3*z - 3676400457*b^3*c^3 - 342363375*b^3*c^2*z - 1023902151*b^3*c^2 + 1156400000*b^3*c*z + 12714350738*b^3*c - 351050000*b^3*z - 3264134833*b^3 + 246793250*b^2*c^4*z - 638154471*b^2*c^4 + 523280000*b^2*c^3*z + 10697872341*b^2*c^3 - 944573250*b^2*c^2*z - 11547566218*b^2*c^2 + 401650000*b^2*c*z + 6424054819*b^2*c - 123900000*b^2*z - 2725368942*b^2 - 72906625*b*c^5*z + 215911058*b*c^5 - 750686500*b*c^4*z - 1387225283*b*c^4 + 658393125*b*c^3*z - 7152826492*b*c^3 + 1720175000*b*c^2*z + 10908622724*b*c^2 - 1668550000*b*c*z - 3537100102*b*c + 82600000*b*z + 873928355*b + 218719875*c^5*z - 15843884*c^5 - 210976125*c^4*z + 1861901065*c^4 - 502318750*c^3*z - 3663201898*c^3 + 587500000*c^2*z + 3154861216*c^2 - 123900000*c*z - 1464189922*c + 20650000*z + 282776471)/298400000) * h2 + (-(-257177529*b + 107955529*c + 20650000*z + 282776471)/298400000) * h3

private lemma rejectI_7_11 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, c, b) = 0) (h2 : locus b (b, 1, c) = 0)
    (h3 : edge b b c (1, c, b) (b, 1, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((8967393548330938*b*c^2 - 6995431630608088*b*c - 50278482092963866*c^3 + 198049166375551855*c^2 - 110811698607234953*c - 22354737632615556)/22354737632615556) * h0 + ((-108340376504192*b^2*c^6 + 239014541924150805*b^2*c^5*z + 29701119635640192*b^2*c^5 - 5785227864820597068*b^2*c^4*z + 777146655472913344*b^2*c^4 + 24204660917475773142*b^2*c^3*z - 4254284652190203120*b^2*c^3 - 31181935813082872344*b^2*c^2*z + 5593738735448497216*b^2*c^2 + 16131343150600770357*b^2*c*z - 3540643360762095408*b^2*c - 2915300828317085820*b^2*z - 332812318763198640*b^2 + 54170188252096*b*c^7 + 86569262972517384*b*c^6*z - 13740070958652128*b*c^6 + 2494813185766999206*b*c^5*z - 721828344151883712*b*c^5 - 9277790574565711818*b*c^4*z + 2881217799164514368*b*c^4 - 2544836200012954134*b*c^3*z - 421553541463549952*b*c^3 + 15412265502046034490*b*c^2*z - 2594963619864028464*b*c^2 - 9114376117272476184*b*c*z + 2660022408654739144*b*c + 1558246733505312912*b*z + 1209975921889936332*b - 595872070773056*c^7 - 911908621730202003*c^6*z + 178794661647868416*c^6 + 121996352221788447*c^5*z - 395445957831001024*c^5 + 15585200225944836210*c^4*z - 1790746572158389072*c^4 - 32107451527093462398*c^3*z + 4928065256634229936*c^3 + 25831269111993636357*c^2*z - 4187025569543421872*c^2 - 9529882584258299985*c*z + 2026876007098796318*c + 1357054094811772908*z - 170320821699679446)/402385277387080008) * h1 + (-(650042259025152*b^6*c^2 + 1038831155670208608*b^6*c*z - 195757858807520256*b^6*c - 3116493467010625824*b^6*z + 649071477020841792*b^6 + 1516765271058688*b^5*c^3 + 2423939363230486752*b^5*c^2*z - 459801867759664640*b^5*c^2 - 12119696816152433760*b^5*c*z + 2428036787483725376*b^5*c + 14543636179382920512*b^5*z - 3029000226097261696*b^5 + 541701882520960*b^4*c^4 + 865692629725173840*b^4*c^3*z - 171257077244081280*b^4*c^3 - 15582467335053129120*b^4*c^2*z + 2993499832189589344*b^4*c^2 + 47959371686774630736*b^4*c*z - 9809961572425697952*b^4*c - 27009610047425423808*b^4*z + 5625286134180628864*b^4 - 650042259025152*b^3*c^5 - 1119537697605187050*b^3*c^4*z + 193699391653940608*b^3*c^4 - 29473099334583534*b^3*c^3*z - 17687510887583296*b^3*c^3 + 28158620844365194392*b^3*c^2*z - 5518440485688537120*b^3*c^2 - 62503007866157551248*b^3*c*z + 12869860748822100160*b^3*c + 22334869846909485072*b^3*z - 4651678918649366176*b^3 - 216680753008384*b^2*c^6 + 146582557914094479*b^2*c^5*z + 71157170121985216*b^2*c^5 + 8450572166925160905*b^2*c^4*z - 1996712020893592192*b^2*c^4 - 29549090539840158963*b^2*c^3*z + 6562838487840940080*b^2*c^3 + 7302046378091662143*b^2*c^2*z - 1695206561495138672*b^2*c^2 + 8802010710448267932*b^2*c*z - 1861362511260591616*b^2*c - 2077662311340417216*b^2*z + 432714318013894528*b^2 + 54170188252096*b*c^7 + 86569262972517384*b*c^6*z - 16448580371256928*b*c^6 - 1995063046728826878*b*c^5*z + 83970426617569216*b*c^5 - 8302038509641924170*b*c^4*z + 3160102603378536224*b*c^4 + 60401277887240772108*b*c^3*z - 14596888768089411136*b*c^3 - 66404844957724792812*b*c^2*z + 14179641001878812400*b*c^2 + 27641242076254549056*b*c*z - 6052702771972255192*b*c - 4155324622680834432*b*z + 865428636027789056*b - 595872070773056*c^7 - 911908621730202003*c^6*z + 184536701602590592*c^6 + 9379044769243609593*c^5*z - 2134661862124067712*c^5 - 31229995576731093513*c^4*z + 6969075262414851632*c^4 + 37334549721349111671*c^3*z - 7617058433620417392*c^3 - 20631538700207642628*c^2*z + 4799351372425355072*c^2 + 5367294304296077808*c*z + 880198470094239458*c - 519415577835104304*z + 108178579503473632)/402385277387080008) * h2 + (2*(6771273531512*c^2 + 10821157871564673*c*z - 2039144362578336*c - 32463473614694019*z + 6761161218967102)/50298159673385001) * h3

private lemma rejectI_7_17 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, c, b) = 0) (h2 : locus b (b, c, c) = 0)
    (h3 : edge b b c (1, c, b) (b, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((651413042907210*b^2*c + 7833259232400*b*c^3 + 20917593137113*b*c^2 - 3788629520914765*b*c + 21298991002686*c^3 + 943583839393431*c^2 - 14714106028125)/14714106028125) * h0 + (-(23499777697200*b^2*c^6*z + 246188147304*b^2*c^6 + 656935123165842*b^2*c^5*z - 5747698707204*b^2*c^5 - 8264211859023732*b^2*c^4*z + 49605172456742*b^2*c^4 + 35573986316710420*b^2*c^3*z - 162453820111006*b^2*c^3 - 38806547628998592*b^2*c^2*z + 128050784139946*b^2*c^2 + 14596577020065754*b^2*c*z - 90215632507702*b^2*c - 2657807993631004*b^2*z - 65861029992020*b^2 + 3916629616200*b*c^7*z + 123094073652*b*c^7 - 118050530857370*b*c^6*z - 2763931981143*b*c^6 - 488075888002900*b*c^5*z + 14946237541526*b*c^5 + 750230052515886*b*c^4*z - 6787554418349*b*c^4 - 8399915723254556*b*c^3*z - 60619707614090*b*c^3 + 10860066800745542*b*c^2*z + 75551766523033*b*c^2 - 6618232556024056*b*c*z - 133758758343660*b*c + 1386446376809366*b*z - 301207071499717*b + 636369046675096*c^5*z - 1093769209092*c^5 - 75153668682152*c^4*z + 4015405195772*c^4 - 85195964010744*c - 3774335357573724)/58856424112500) * h1 + (-(93999110788800*b^7*c*z + 2954257767648*b^7*c - 2366519069669472*b^7*z - 28266875458632*b^7 + 15666518464800*b^6*c^2*z + 492376294608*b^6*c^2 + 3188796658133664*b^6*c*z - 18659405583444*b^6*c + 5465375662080768*b^6*z + 94759619821212*b^6 - 15666518464800*b^5*c^3*z - 492376294608*b^5*c^3 + 780124596183208*b^5*c^2*z - 4260644013048*b^5*c^2 - 3325638368154800*b^5*c*z + 95307901593896*b^5*c + 1521724875177192*b^5*z - 55519932026808*b^5 - 23499777697200*b^4*c^4*z - 738564441912*b^4*c^4 - 1143900625029748*b^4*c^3*z + 14561379903654*b^4*c^3 - 13782551051173220*b^4*c^2*z - 43082419878560*b^4*c^2 - 2914568060835728*b^4*c*z - 99538203057758*b^4*c - 6629983695381352*b^4*z - 84104885661896*b^4 - 31333036929600*b^3*c^5*z - 492376294608*b^3*c^5 - 406137430531958*b^3*c^4*z + 12014127111402*b^3*c^4 + 16405934391160424*b^3*c^3*z - 83036870629872*b^3*c^3 - 347712294061814*b^3*c^2*z + 139025802317912*b^3*c^2 - 1775280962745572*b^3*c*z - 123259233371714*b^3*c - 94352832761848*b^3*z + 82395326057440*b^3 - 3916629616200*b^2*c^6*z - 123094073652*b^2*c^6 + 180716604716570*b^2*c^5*z + 3748684570359*b^2*c^5 + 1001679931256384*b^2*c^4*z - 37374268806854*b^2*c^4 - 32141367025945528*b^2*c^3*z + 124733392188242*b^2*c^3 + 53434130731840852*b^2*c^2*z - 63407209186664*b^2*c^2 - 3897330528837414*b^2*c*z + 127276822932765*b^2*c + 225461006046456*b^2*z - 12046215587316*b^2 - 15666518464800*b*c^6*z - 947868999507382*b*c^5*z - 518729696994*b*c^5 + 4430469615143876*b*c^4*z - 4578079463104*b*c^4 - 5723615949272662*b*c^3*z + 94826331847192*b*c^3 - 14885249929748264*b*c^2*z - 151073046000486*b*c^2 + 5545785507237464*b*c*z + 78208206674344*b*c - 3916629616200*c^7*z - 123094073652*c^7 + 110217271624970*c^6*z + 2517743833839*c^6 + 728093579333840*c^5*z - 9295279505588*c^5 - 1707787150443376*c^4*z - 15750586709162*c^4 + 3845339802405324*c^3*z + 27461367323130*c^3 - 1386446376809366*c^2*z - 8893850363383*c^2 + 57176653364164*c)/58856424112500) * h2 + ((3916629616200*b*c*z + 123094073652*b*c - 98604961236228*b*z - 1177786477443*b + 159092261668774*c*z - 273442302273*c - 18788417170538*z + 1003851298943)/14714106028125) * h3

private lemma rejectI_7_20 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, c, b) = 0) (h2 : locus b (c, 1, c) = 0)
    (h3 : edge b b c (1, c, b) (c, 1, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(147219014*b*c - 71983311*b + 79147842*c^2 - 582430483*c + 289586939)/440062) * h0 + ((885972*b^5*c^2 + 5684256*b^5*c*z - 3738334*b^5*c - 947376*b^5*z + 573835*b^5 + 1771944*b^4*c^3 - 135850502*b^4*c^2*z - 13973796*b^4*c^2 + 173728277*b^4*c*z + 29906672*b^4*c - 64404303*b^4*z - 4590680*b^4 + 68071172*b^3*c^3*z - 7383100*b^3*c^3 + 542226214*b^3*c^2*z + 43457950*b^3*c^2 - 924498836*b^3*c*z - 61665698*b^3*c + 349254362*b^3*z + 7312193*b^3 + 79147842*b^2*c^4*z + 7678424*b^2*c^4 - 533166931*b^2*c^3*z - 36927196*b^2*c^3 + 164965049*b^2*c^2*z + 32269264*b^2*c^2 + 611799139*b^2*c*z - 20889787*b^2*c - 306639707*b^2*z + 11067340*b^2 + 79147842*b*c^5*z + 590648*b*c^5 - 475728645*b*c^4*z - 20310104*b*c^4 + 758217864*b*c^3*z + 113420498*b*c^3 - 493744218*b*c^2*z - 152481483*b*c^2 + 78580413*b*c*z + 90708328*b*c + 22737024*b*z - 86198337*b + 11076670*c^5*z + 6201804*c^5 + 23363067*c^4*z - 47136342*c^4 - 118075389*c^3*z + 99411614*c^3 + 147334049*c^2*z - 97642594*c^2 - 79803789*c*z + 46335897*c + 17052768*z + 206539212)/440062) * h1 + (-(947376*b^5*z - 573835*b^5 - 8526384*b^4*z + 5164515*b^4 + 21789648*b^3*z - 13198205*b^3 - 9473760*b^2*z + 5738350*b^2 + 79147842*b*c^5*z + 590648*b*c^5 - 328509631*b*c^4*z - 1704692*b*c^4 + 216727873*b*c^3*z + 7450352*b*c^3 + 19844340*b*c^2*z - 531437*b*c^2 - 4736880*b*c*z + 4907934*b*c - 7579008*b*z - 67392631*b + 11076670*c^5*z - 3248564*c^5 - 15115657*c^4*z + 11443074*c^4 + 22512819*c^3*z - 20068874*c^3 - 19894896*c^2*z + 12122904*c^2 + 9473760*c*z - 10022741*c - 947376*z + 289720712)/440062) * h2 + (-(202*c + 1296*z - 785)/602) * h3

private lemma rejectI_8_13 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, c, c) = 0) (h2 : locus b (b, b, b) = 0)
    (h3 : edge b b c (1, c, c) (b, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((630*b^2*c + 10141*b^2 + 11016*b*c^2 - 44379*b*c + 245*b - 14)/14) * h0 + ((15104*b*c^6*z - 94064*b*c^5*z + 227824*b*c^4*z - 140*b*c^4 - 224866*b*c^3*z + 315*b*c^3 - 11955*b*c^2*z - 280*b*c^2 + 87348*b*c*z - 35*b*c - 245*b - 3776*c^6*z + 22572*c^5*z - 54250*c^4*z + 35*c^4 + 56536*c^3*z - 70*c^3 - 2155*c^2*z + 70*c^2 - 22514*c*z + 11121)/14) * h1 + ((4196*b^5*c*z + 8602*b^4*c^3*z - 9705*b^4*c^2*z - 48031*b^4*c*z - 35*b^4*c + 4196*b^4*z + 3776*b^3*c^5*z - 4214*b^3*c^4*z - 113998*b^3*c^3*z - 35*b^3*c^3 + 217904*b^3*c^2*z + 35*b^3*c^2 + 63146*b^3*c*z + 315*b^3*c - 12714*b^3*z - 35*b^3 + 3776*b^2*c^6*z - 48272*b^2*c^5*z + 167643*b^2*c^4*z - 35*b^2*c^4 - 51798*b^2*c^3*z + 245*b^2*c^3 - 270545*b^2*c^2*z - 280*b^2*c^2 + 45052*b^2*c*z - 560*b^2*c + 378*b^2*z + 105*b^2 + 3776*b*c^7*z - 22152*b*c^6*z + 19446*b*c^5*z - 35*b*c^5 + 79937*b*c^4*z + 105*b*c^4 - 136072*b*c^3*z + 105*b*c^3 - 8733*b*c^2*z - 385*b*c^2 + 22514*b*c*z + 70*b*c + 3776*c^8*z - 37676*c^7*z + 144538*c^6*z - 35*c^6 - 273536*c^5*z + 210*c^5 + 228299*c^4*z - 350*c^4 + 13894*c^3*z + 280*c^3 - 90056*c^2*z - 105*c^2 + 105*c + 245)/14) * h2 + (-(4196*b*z + 3776*c^2*z - 15020*c*z - 126*z - 35)/14) * h3

private lemma rejectI_8_14 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (1, c, c) = 0) (h2 : locus b (b, b, c) = 0)
    (h3 : edge b b c (1, c, c) (b, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(2821661*b^3 + 16356200*b^2*c - 13121178*b^2 + 11297208*b*c^2 - 46341671*b*c + 9392197*b - 4045048*c^3 + 9392197*c^2 + 47678464)/47678464) * h0 + ((7270239*b^2*c^4*z + 38262*b^2*c^4 - 22250531*b^2*c^3*z + 296639*b^2*c^3 + 27931487*b^2*c^2*z - 510398*b^2*c^2 - 6534900*b^2*c*z - 377629*b^2*c - 2891794*b^2*z + 448287*b^2 - 3434675*b*c^5*z - 11345384*b*c^4*z - 707847*b*c^4 + 1928260*b*c^3*z + 1217594*b*c^3 - 14888860*b*c^2*z + 720902*b*c^2 + 13809204*b*c*z - 342461*b*c - 1790658*b*z + 469651*b + 505631*c^6*z + 5077674*c^5*z + 172179*c^5 - 983484*c^4*z - 281694*c^4 + 2477422*c^3*z - 228053*c^3 - 1790658*c^2*z + 11347*c^2 - 203161*c - 441251)/5959808) * h1 + (-(5023933*b^5*c^2*z - 619389*b^5*c*z + 20795803*b^4*c^3*z + 306096*b^4*c^3 - 30051212*b^4*c^2*z - 1146992*b^4*c^2 + 20495521*b^4*c*z - 1453088*b^4*c + 1101136*b^4*z + 306096*b^3*c^4 - 88321855*b^3*c^3*z - 3748808*b^3*c^3 - 23542229*b^3*c^2*z + 8449392*b^3*c^2 - 131441780*b^3*c*z + 11777752*b^3*c + 2758088*b^3*z - 726544*b^3 - 15342256*b^2*c^5*z + 118768304*b^2*c^4*z - 918288*b^2*c^4 - 97517108*b^2*c^3*z + 9256800*b^2*c^3 + 381715764*b^2*c^2*z - 17892728*b^2*c^2 + 225082840*b^2*c*z - 26194280*b^2*c - 39116568*b^2*z + 3632720*b^2 + 4045048*b*c^6*z + 24441200*b*c^5*z + 1377432*b*c^5 - 194547264*b*c^4*z - 9293760*b*c^4 - 36405808*b*c^3*z + 14149128*b*c^3 - 110130304*b*c^2*z + 8841560*b*c^2 + 57301056*b*c*z - 1988392*b*c + 2133208*b + 2529496*c^5*z + 153048*c^5 + 8263768*c^4*z - 726544*c^4 - 4045048*c + 9392197)/47678464) * h2 + ((137642*b*z + 316187*c*z + 19131*c + 1032971*z - 90818)/5959808) * h3

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
  linear_combination (-(1252440*b^2*c^2 + 8358714*b^2*c*z - 6230840*b^2*c - 9315891*b^2*z + 4001480*b^2 - 3717560*b*c^3 - 24810786*b*c^2*z + 18784080*b*c^2 + 28724787*b*c*z - 15546000*b*c - 3914001*b*z + 3512120*b + 2465120*c^4 + 16452072*c^3*z - 13765920*c^3 - 27502254*c^2*z + 16614480*c^2 + 5648292*c*z - 1791680*c + 5401890*z - 3199782)/322218) * h0 + ((2179710*b^4*z - 234800*b^4 + 83843019*b^3*z^2 - 49091580*b^3*z + 1408800*b^3 - 132460029*b^2*z^2 + 70109001*b^2*z - 3376440*b^2 - 22186080*b*c^6*z - 636160*b*c^6 - 148068648*b*c^5*z^2 + 153463464*b*c^5*z + 5015920*b*c^5 + 473205564*b*c^4*z^2 - 205276932*b*c^4*z - 14610440*b*c^4 + 139454055*b*c^3*z^2 - 379534572*b*c^3*z + 20166040*b*c^3 - 960569766*b*c^2*z^2 + 647000739*b*c^2*z - 13261160*b*c^2 + 253831968*b*c*z^2 - 55229076*b*c*z + 29406640*b*c + 40002417*b*z^2 - 32476545*b*z + 4024520*b + 159040*c^7 - 10210536*c^6*z - 1661520*c^6 - 75228426*c^5*z^2 + 53416044*c^5*z + 6849160*c^5 + 161459649*c^4*z^2 - 12825288*c^4*z - 14922040*c^4 + 71219655*c^3*z^2 - 202752801*c^3*z + 18322800*c^3 - 362751129*c^2*z^2 + 306568278*c^2*z - 13537360*c^2 + 242146827*c*z^2 - 8453826*c*z - 31878960*c - 36846576*z^2 + 70943787*z - 43266240)/2899962) * h1 + (-(11271960*b^5*c^3*z + 75228426*b^5*c^2*z^2 - 67349520*b^5*c^2*z + 19880*b^5*c^2 - 159071445*b^5*c*z^2 + 92223558*b^5*c*z - 103320*b^5*c + 83843019*b^5*z^2 - 37103175*b^5*z + 117400*b^5 - 44730000*b^4*c^4*z + 39760*b^4*c^4 - 298525500*b^4*c^3*z^2 + 247585716*b^4*c^3*z - 246400*b^4*c^3 + 490434750*b^4*c^2*z^2 - 268807626*b^4*c^2*z + 222760*b^4*c^2 - 59449221*b^4*c*z^2 + 24074892*b^4*c*z + 941480*b^4*c - 132460029*b^4*z^2 + 52671321*b^4*z - 1498040*b^4 + 55644120*b^3*c^5*z + 79520*b^3*c^5 + 371365722*b^3*c^4*z^2 - 269875368*b^3*c^4*z - 870520*b^3*c^4 - 355586517*b^3*c^3*z^2 + 102604266*b^3*c^3*z + 3402600*b^3*c^3 - 530607753*b^3*c^2*z^2 + 390363489*b^3*c^2*z - 5235320*b^3*c^2 + 558669150*b^3*c*z^2 - 318721824*b^3*c*z + 1073360*b^3*c + 40002417*b^3*z^2 - 29206980*b^3*z + 3672320*b^3 - 22186080*b^2*c^6*z + 79520*b^2*c^6 - 148068648*b^2*c^5*z^2 + 80051832*b^2*c^5*z - 691600*b^2*c^5 - 48617010*b^2*c^4*z^2 + 136411488*b^2*c^4*z + 1955840*b^2*c^4 + 740343240*b^2*c^3*z^2 - 515556594*b^2*c^3*z - 1233960*b^2*c^3 - 647715042*b^2*c^2*z^2 + 377597826*b^2*c^2*z - 3663920*b^2*c^2 + 8444007*b^2*c*z^2 + 20017953*b^2*c*z + 8218440*b^2*c - 36846576*b^2*z^2 - 5270247*b^2*z - 8074720*b^2 + 159040*b*c^7 - 10210536*b*c^6*z - 1860320*b*c^6 - 75228426*b*c^5*z^2 + 74633184*b*c^5*z + 8260080*b*c^5 + 311916501*b*c^4*z^2 - 78460776*b*c^4*z - 17621760*b*c^4 + 124442487*b*c^3*z^2 - 330740730*b*c^3*z + 18677960*b*c^3 - 710661276*b*c^2*z^2 + 421877268*b*c^2*z - 8528080*b*c^2 + 147386304*b*c*z^2 + 68939838*b*c*z - 927320*b*c - 37405719*b*z + 31843880*b + 19880*c^6 + 132678*c^5*z - 182840*c^5 - 1620567*c^4*z + 649960*c^4 + 5155488*c^3*z - 1169040*c^3 - 7069842*c^2*z + 23323640*c^2 + 152560746*c*z - 80094040*c + 47527155*z - 31580600)/2899962) * h2 + ((19880*c^2 + 132678*c*z - 103320*c - 1089855*z + 117400)/2899962) * h3

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
  linear_combination ((c - 5)*(c + 3)/16) * h0 + ((b^4*c^2 - b^4*c - 10*b^3*c^2 + 10*b^3*c + 96*b^2*c^4*z - 3*b^2*c^4 - 672*b^2*c^3*z + 14*b^2*c^3 - 1632*b^2*c^2*z + 12*b^2*c^2 + 3744*b^2*c*z - 34*b^2*c + 43*b^2 - 96*b*c^5*z + 2*b*c^5 + 192*b*c^4*z - 7*b*c^4 + 2112*b*c^3*z + 9*b*c^3 + 960*b*c^2*z - 9*b*c^2 - 3168*b*c*z - 15*b*c + 20*b + 288*c^5*z - c^5 - 672*c^4*z - 5*c^4 - 3168*c^3*z + 24*c^3 + 4128*c^2*z - 40*c^2 - 576*c*z - 15*c - 155)/3072) * h1 + ((2*b^2*c^4 + 192*b^2*c^3*z - 8*b^2*c^3 + 192*b^2*c^2*z + 8*b^2*c^2 - 1152*b^2*c*z + 4*b^2*c - 22*b^2 - 4*b*c^4 + 8*b*c^3 - 8*b*c + 4*b + c^5 - 5*c^4 + 10*c^3 - 10*c^2 + 5*c + 95)/1536) * h2 + (-(c - 1)/1536) * h3

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
  linear_combination ((24*b^6*c - 36*b^6 - 84*b^5*c^2 + 154*b^5*c - 42*b^5 + 128*b^4*c^3 - 320*b^4*c^2 + 120*b^4*c + 108*b^4 - 110*b^3*c^4 + 409*b^3*c^3 - 344*b^3*c^2 - 37*b^3*c + 6*b^3 + 56*b^2*c^5 - 316*b^2*c^4 + 532*b^2*c^3 - 326*b^2*c^2 + 197*b^2*c - 183*b^2 - 16*b*c^6 + 144*b*c^5 - 468*b*c^4 + 726*b*c^3 - 883*b*c^2 + 1063*b*c + 1044*b - 352*c^4 + 2112*c^3 - 1724*c^2 - 4310*c - 1557)/1344) * h1 + ((2*b^2*c^5 - 31*b^2*c^4 + 172*b^2*c^3 - 99*b^2*c^2 - 492*b^2*c - 1122*b^2 + 4*b*c^3 - 674*b*c^2 + 1994*b*c + 1368*b + 2*c + 669)/672) * h2 + (-(2*c - 3)/672) * h3

private lemma rejectI_10_11 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, 1, b) = 0) (h2 : locus b (b, 1, c) = 0)
    (h3 : edge b b c (b, 1, b) (b, 1, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(227060*b^6*c + 227060*b^6 - 226802*b^5*c^2 - 2638924*b^5*c - 1049762*b^5 + 113186*b^4*c^3 + 1841892*b^4*c^2 + 7405704*b^4*c + 966298*b^4 + 215*b^3*c^4 - 522430*b^3*c^3 - 549085*b^3*c^2 - 4473020*b^3*c + 362360*b^3 + 129*b^2*c^5 - 565543*b^2*c^4 - 2577351*b^2*c^3 - 4391619*b^2*c^2 - 1872008*b^2*c - 22138*b^2 - 86*b*c^6 + 224265*b*c^5 + 3125532*b*c^4 + 1953686*b*c^3 - 2103989*b*c^2 - 354008*b*c + 261846*b + 731*c^6 - 1046408*c^5 + 736392*c^4 + 743795*c^3 - 806826*c^2 - 116394*c + 56926)/135000) * h1 + ((86*b^2*c^5 - 112025*b^2*c^4 + 172528*b^2*c^3 + 180441*b^2*c^2 - 104712*b^2*c - 83904*b^2 - 559*b*c^5 + 181883*b*c^4 - 286262*b*c^3 - 288795*b*c^2 + 174768*b*c + 147994*b + 43*c^6 + 43*c^5 + 297558*c^4 - 451335*c^3 - 463836*c^2 + 267458*c + 191926)/135000) * h2 + ((113530*b^2 + 129*b*c - 184291*b - 43*c^2 + 43*c - 296784)/135000) * h3

private lemma rejectI_10_17 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, 1, b) = 0) (h2 : locus b (b, c, c) = 0)
    (h3 : edge b b c (b, 1, b) (b, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(71609509241975214520467979078656*b^3 + 569264033717861707280545385160954*b^2*c - 3832278837578933058596744684495574*b^2 - 603838703917999472652142197769378*b*c^2 + 2031833027191309691721592677815788*b*c + 5362313685929694452678542921261054*b + 589302182707112536183840105809805*c^3 - 3569532604149912798702965666843133*c^2 + 5452676932694040578141623523441859*c - 2547310475642130280151596056421491)/91751816414522207209393116990000) * h0 + (-(358047546209876072602339895393280*b^5*c^2*z - 1850288312427569415019716087744*b^5*c^2 - 1727121859621175436863532396203520*b^5*c*z + 14881378649524297602850878962112*b^5*c + 4107222940233898092783577502430720*b^5*z - 27991541136724768073375192096640*b^5 - 925144156213784707509858043872*b^4*c^4 + 1803735465673782781669790780006370*b^4*c^3*z + 15492214968616486535651013970224*b^4*c^3 - 12509737059287695689020346704534160*b^4*c^2*z - 78914152580104822642453219733136*b^4*c^2 - 683019135019885879340287672448850*b^4*c*z + 135039923023868762913835273601136*b^4*c - 10688480390859192982217859806557440*b^4*z - 38245523349991460113705718847600*b^4 + 1712902431392707098338142134904*b^3*c^5 - 3496626120193889485400431199004620*b^3*c^4*z - 26498157107858857061832918222288*b^3*c^4 + 3129629197660706498792648432851120*b^3*c^3*z + 149627153991850545167532560869632*b^3*c^3 + 103131356503296604795591513076181660*b^3*c^2*z - 375637197363168102878521323976320*b^3*c^2 - 50794620057571975632727799696689280*b^3*c*z + 259928776965095046307537950874248*b^3*c + 6737566374468540707821518154682880*b^3*z + 287351073726443783460264174472080*b^3 - 1850288312427569415019716087744*b^2*c^6 + 4596630119714260679918719017085675*b^2*c^5*z + 22108589007169461436987009734240*b^2*c^5 - 15788493619329449250854135196758490*b^2*c^4*z - 109143860056312451664130147479168*b^2*c^4 - 23665224722935807595688439495661820*b^2*c^3*z + 295710579521986663870742031230664*b^2*c^3 - 84995927009090958862456624571915430*b^2*c^2*z - 253225654631788630099317490126152*b^2*c^2 + 68533753490257063940579219755731665*b^2*c*z + 5669983990341402791006446111959178*b^2*c - 848930035758110451334964017825920*b^2*z - 22786746323380544592342111599401510*b^2 + 925144156213784707509858043872*b*c^7 - 2261973756829912998788604278643905*b*c^6*z - 10179564782373251414693853986664*b*c^6 + 8785673237163455502482624227177655*b*c^5*z + 57832909760388623881133268599184*b*c^5 + 25246917903347559625458026704471950*b*c^4*z - 264578686115205374227381027374504*b*c^4 - 104940306887881408346123728414397290*b*c^3*z + 641693825025627539362824246047688*b*c^3 + 112123443370711248497954151765091795*b*c^2*z - 6103199163423688580615166248592514*b*c^2 - 28044787098183205211715947892815085*b*c*z + 16030761941522128035321866325956676*b*c - 1493047416417685379379900683907840*b*z + 22145213232191567146006548461335870*b + 2946510913535562680919200529049025*c^3 - 17847525634868529131198146760262825*c^2 - 999813254574117050001814214836800*c*z + 27265548342626390381477160247377087*c + 272198071640416882688812116789120*z - 13215681484743290064193917749580375)/458759082072611036046965584950000) * h1 + ((-137385881034862316681573952840*b^2*c^6 + 999813254574117050001814214836800*b^2*c^5*z - 3327038063440748600654476491336*b^2*c^5 - 15479871398528989539716677278930435*b^2*c^4*z + 49220831991205068400349048688120*b^2*c^4 + 56909071265197053372544163362843920*b^2*c^3*z - 182896343131103048514684942980928*b^2*c^3 - 35082353579058468580317265640218405*b^2*c^2*z + 151634723752122277845529741927680*b^2*c^2 - 3474010114732512837837740662197320*b^2*c*z + 3096381994821364332554849455363865*b^2*c - 11238888981204520642080378259653695*b^2 - 1850288312427569415019716087744*b*c^5 + 16309991167802076721254010673483910*b*c^4*z + 16246395296786777049303553939320*b*c^4 - 65055937506086478427846389456137985*b*c^3*z - 78590051369144857269567118371456*b*c^3 - 43074480714731990877683406961353110*b*c^2*z + 403064941023718905335042745798120*b*c^2 + 80523208335901593788726998956384785*b*c*z - 6543158779329922652544338278702810*b*c + 22232348127888254102867212892904670*b + 925144156213784707509858043872*c^5 - 2261973756829912998788604278643905*c^4*z - 8329276469945681999674137898920*c^4 + 4261725723503629504905415669889845*c^3*z + 40249212664283475174275134757472*c^3 + 36032343107184731634057462322895545*c^2*z - 176163141959797328829201341819160*c^2 - 34137906633293223432908776793985645*c*z - 5649432834930694391398611503279650*c + 21565972784285519531790846394311590)/458759082072611036046965584950000) * h2 + ((30244992884532036*b*c + 22379022009382798560*b*z - 152517485486101720*b + 4491445972420295*c^2 - 32686089586526233400*c*z + 70735420251823746*c + 8898752356216940560*z - 665940805779581835)/14997841233506381250) * h3

private lemma rejectI_10_20 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, 1, b) = 0) (h2 : locus b (c, 1, c) = 0)
    (h3 : edge b b c (b, 1, b) (c, 1, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(2458*b^6*c + 2458*b^6 - 3758*b^5*c^2 - 29904*b^5*c - 11398*b^5 + 3475*b^4*c^3 + 34559*b^4*c^2 + 85958*b^4*c + 11492*b^4 - 1596*b^3*c^4 - 24221*b^3*c^3 - 40799*b^3*c^2 - 62802*b^3*c + 1066*b^3 + 473*b^2*c^5 + 4718*b^2*c^4 - 16322*b^2*c^3 - 12546*b^2*c^2 + 5304*b^2*c + 3538*b^2 - 10168*b*c^5 + 70329*b*c^4 - 2067*b*c^3 - 38565*b*c^2 - 19860*b*c - 2284*b + 1892*c^6 - 21032*c^5 + 31506*c^4 + 4132*c^3 - 34015*c^2 + 12856*c + 1442)/1250) * h1 + (-(11928*b^2*c^4 - 14770*b^2*c^3 + 11224*b^2*c^2 - 11560*b^2*c - 5222*b^2 - 3961*b*c^5 - 7346*b*c^4 - 24198*b*c^3 + 6311*b*c^2 + 47832*b*c + 5168*b + 473*c^6 + 1252*c^5 - 2609*c^4 + 14562*c^3 + 227*c^2 - 18240*c - 2692)/1250) * h2 + ((1229*b^2 - 650*b*c - 2012*b + 473*c^2 + 306*c - 2748)/1250) * h3

private lemma rejectI_11_17 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, 1, c) = 0) (h2 : locus b (b, c, c) = 0)
    (h3 : edge b b c (b, 1, c) (b, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (z*(688*b^5*c + 156*b^4*c^3 - 872*b^4*c^2 - 7540*b^4*c + 78*b^3*c^4 - 1386*b^3*c^3 + 8826*b^3*c^2 + 24818*b^3*c + 688*b^3 - 468*b^2*c^4 + 1260*b^2*c^3 - 31452*b^2*c^2 + 4420*b^2*c - 7936*b^2 + 195*b*c^6 - 2923*b*c^5 + 16786*b*c^4 - 19094*b*c^3 + 5111*b*c^2 - 4847*b*c + 4772*b + 312*c^6 - 3680*c^5 + 10968*c^4 - 13312*c^3 + 6248*c^2 + 96*c - 632)/1792) * h1 + (z*(195*b^2*c^5 - 1480*b^2*c^4 + 4146*b^2*c^3 + 4340*b^2*c^2 - 20205*b^2*c + 3148*b^2 + 234*b*c^5 - 3464*b*c^4 + 6548*b*c^3 - 1600*b*c^2 - 2414*b*c + 696*b - 195*c^6 + 1675*c^5 - 4434*c^4 + 7638*c^3 - 10359*c^2 + 6543*c - 868)/1792) * h2 + (-z*(172*b + 39*c^2 - 304*c - 79)/224) * h3

private lemma rejectI_11_20 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, 1, c) = 0) (h2 : locus b (c, 1, c) = 0)
    (h3 : edge b b c (b, 1, c) (c, 1, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(2*b - 3)*(100625211190*b*c^2 + 2463016007219*b*c - 720171229953*b - 407354373609*c^3 + 401259674151*c^2 + 419543772525*c - 715952999442)/907511779125) * h0 + (-(-45785477120*b^6*c^2 + 37247822848*b^6*c + 552982365184*b^6 + 160249169920*b^5*c^3 - 153260118528*b^5*c^2 - 1916814366720*b^5*c + 276491182592*b^5 + 402500844760*b^4*c^4*z - 263266493440*b^4*c^4 + 9449563184116*b^4*c^3*z + 443102366976*b^4*c^3 - 12732748948688*b^4*c^2*z + 3233783240448*b^4*c^2 + 2880684919812*b^4*c*z - 2960462895872*b^4*c - 2903157417216*b^4 - 1830667916816*b^3*c^5*z + 257543308800*b^3*c^5 - 3502829624818*b^3*c^4*z - 764667913600*b^3*c^4 - 40808305052740*b^3*c^3*z - 2882100153088*b^3*c^3 + 57681415195666*b^3*c^2*z + 6903663868160*b^3*c^2 - 11539612601292*b^3*c*z + 2681821096704*b^3*c - 207368386944*b^3 + 714083536028*b^2*c^6*z - 145941208320*b^2*c^6 + 5475596326101*b^2*c^5*z + 582305391168*b^2*c^5 + 19295421812641*b^2*c^4*z + 1711718607168*b^2*c^4 - 2398041000271*b^2*c^3*z - 7026143667200*b^2*c^3 - 20290740364907*b^2*c^2*z - 2957635147008*b^2*c^2 - 2796320309592*b^2*c*z + 14001663660480*b^2*c - 449298171712*b^2 + 22892738560*b*c^7 - 2343501030464*b*c^6*z - 61547796224*b*c^6 - 1014223485385*b*c^5*z - 466206345792*b*c^5 - 30497551837641*b*c^4*z + 1370423002048*b*c^4 + 43589137612001*b*c^3*z + 1809392057728*b*c^3 - 19748766789677*b*c^2*z - 7774737455360*b*c^2 + 10014905531166*b*c*z + 2410323528604*b*c + 777631451040*b + 714083536028*c^7*z - 20031146240*c^7 - 4703409485275*c^6*z + 122174838336*c^6 + 26947922975093*c^5*z - 22339927488*c^5 - 63373439984696*c^4*z - 1233473591360*c^4 + 64755623915860*c^3*z + 2894367490240*c^3 - 27950073567797*c^2*z - 476850854208*c^2 + 3609292610787*c*z - 864893910024*c + 1270131370032)/3630047116500) * h1 + (-(714083536028*b^2*c^6*z + 37200700160*b^2*c^6 - 9280079277315*b^2*c^5*z - 250606464704*b^2*c^5 + 24419904949130*b^2*c^4*z + 41870538624*b^2*c^4 + 886004722674*b^2*c^3*z + 2099140266816*b^2*c^3 - 30364112072470*b^2*c^2*z - 3064041119744*b^2*c^2 + 13624198141953*b^2*c*z + 3195103009984*b^2*c - 1501677557816*b^2 - 22892738560*b*c^7 + 201250422380*b*c^6*z + 121641234944*b*c^6 + 10839950725042*b*c^5*z + 219868708224*b*c^5 - 28552512000240*b*c^4*z - 1856171933440*b*c^4 + 18605327426668*b*c^3*z + 1165868491136*b*c^3 + 8920888957316*b*c^2*z + 5527905013760*b*c^2 - 10014905531166*b*c*z - 11707531386916*b*c + 2136799312860*b - 714083536028*c^7*z + 20031146240*c^7 + 4703409485275*c^6*z - 122174838336*c^6 - 26947922975093*c^5*z + 22339927488*c^5 + 63373439984696*c^4*z + 1233473591360*c^4 - 64755623915860*c^3*z - 2894367490240*c^3 + 27950073567797*c^2*z + 476850854208*c^2 - 3609292610787*c*z + 5753146393332*c + 3691257506772)/3630047116500) * h2 + (-256*(44712380*c^2 - 36374827*c - 540021841)/907511779125) * h3

private lemma rejectI_12_15 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, b, 1) = 0) (h2 : locus b (b, c, 1) = 0)
    (h3 : edge b b c (b, b, 1) (b, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(227060*b^6*c + 227060*b^6 - 226802*b^5*c^2 - 2638924*b^5*c - 1049762*b^5 + 113186*b^4*c^3 + 1841892*b^4*c^2 + 7405704*b^4*c + 966298*b^4 + 215*b^3*c^4 - 522430*b^3*c^3 - 549085*b^3*c^2 - 4473020*b^3*c + 362360*b^3 + 129*b^2*c^5 - 565543*b^2*c^4 - 2577351*b^2*c^3 - 4391619*b^2*c^2 - 1872008*b^2*c - 22138*b^2 - 86*b*c^6 + 224265*b*c^5 + 3125532*b*c^4 + 1953686*b*c^3 - 2103989*b*c^2 - 354008*b*c + 261846*b + 731*c^6 - 1046408*c^5 + 736392*c^4 + 743795*c^3 - 806826*c^2 - 116394*c + 56926)/135000) * h1 + ((86*b^2*c^5 - 112025*b^2*c^4 + 172528*b^2*c^3 + 180441*b^2*c^2 - 104712*b^2*c - 83904*b^2 - 559*b*c^5 + 181883*b*c^4 - 286262*b*c^3 - 288795*b*c^2 + 174768*b*c + 147994*b + 43*c^6 + 43*c^5 + 297558*c^4 - 451335*c^3 - 463836*c^2 + 267458*c + 191926)/135000) * h2 + ((113530*b^2 + 129*b*c - 184291*b - 43*c^2 + 43*c - 296784)/135000) * h3

private lemma rejectI_12_18 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, b, 1) = 0) (h2 : locus b (c, 1, 1) = 0)
    (h3 : edge b b c (b, b, 1) (c, 1, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(16046*c + 4915)*(3*c^2 - 55*c + 175)/860125) * h0 + (-(-5964*b^4*c^3 + 2567360*b^4*c^2*z + 135026*b^4*c^2 - 6915680*b^4*c*z - 803912*b^4*c - 2359200*b^4*z + 1357530*b^4 - 2982*b^3*c^5 + 1283680*b^3*c^4*z + 94351*b^3*c^4 - 15010960*b^3*c^3*z - 991681*b^3*c^3 + 22238880*b^3*c^2*z + 3891291*b^3*c^2 + 31363440*b^3*c*z - 3697149*b^3*c + 7077600*b^3*z - 4072590*b^3 + 5964*b^2*c^6 - 2326670*b^2*c^5*z - 170810*b^2*c^5 + 17740225*b^2*c^4*z + 1578284*b^2*c^4 - 6703170*b^2*c^3*z - 5385756*b^2*c^3 - 57618880*b^2*c^2*z + 3665237*b^2*c^2 - 38312385*b^2*c*z + 6018266*b^2*c - 6684400*b^2*z + 3846335*b^2 - 8946*b*c^7 + 3610350*b*c^6*z + 259197*b*c^6 - 31627965*b*c^5*z - 2548255*b*c^5 + 95395620*b*c^4*z + 11077395*b*c^4 - 123595340*b*c^3*z - 22046519*b*c^3 + 53340575*b*c^2*z + 19201147*b*c^2 + 41233940*b*c*z - 10495659*b*c + 3145600*b*z - 1810040*b + 240690*c^3 - 4335943*c^2 - 1283680*c*z + 12630058*c - 393200*z + 226255)/4300625) * h1 + ((-2982*b^2*c^6 + 1283680*b^2*c^5*z + 85405*b^2*c^5 - 11881990*b^2*c^4*z - 845800*b^2*c^4 + 47105845*b^2*c^3*z + 4006936*b^2*c^3 - 65612210*b^2*c^2*z - 10065353*b^2*c^2 + 12276590*b^2*c*z + 12346734*b^2*c + 11378225*b^2*z - 7117860*b^2 + 17892*b*c^5 - 6257940*b*c^4*z - 440862*b*c^4 + 17819730*b*c^3*z + 3156288*b*c^3 - 33267250*b*c^2*z - 7768616*b*c^2 + 30159230*b*c*z + 5192768*b*c + 12926450*b*z + 4109280*b - 8946*c^5 + 3610350*c^4*z + 223413*c^4 - 17186565*c^3*z - 1654603*c^3 + 26649360*c^2*z + 4450037*c^2 - 13146860*c*z - 4531176*c - 7053025*z + 8689415)/4300625) * h2 + (-(-2982*c^2 + 1283680*c*z + 58567*c + 393200*z - 226255)/4300625) * h3

private lemma rejectI_12_21 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, b, 1) = 0) (h2 : locus b (c, b, 1) = 0)
    (h3 : edge b b c (b, b, 1) (c, b, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(b + c - 3)*(113071*c^3 - 241867*c^2 - 334067*c + 155246)/3000) * h0 + (-(7798*b^6*c^2 - 34194*b^6*c + 11998*b^6 - 31192*b^5*c^3 + 144574*b^5*c^2 - 82186*b^5*c + 11998*b^5 + 58485*b^4*c^4 - 318839*b^4*c^3 + 347941*b^4*c^2 - 27596*b^4*c - 23996*b^4 + 565355*b^3*c^5*z - 66283*b^3*c^5 - 1774690*b^3*c^4*z + 458306*b^3*c^4 - 461000*b^3*c^3*z - 915134*b^3*c^3 + 2446565*b^3*c^2*z + 638887*b^3*c^2 - 776230*b^3*c*z - 290950*b^3*c + 59990*b^3 + 46788*b^2*c^6 - 3392130*b^2*c^5*z - 411811*b^2*c^5 + 10648140*b^2*c^4*z + 1243261*b^2*c^4 + 2766000*b^2*c^3*z - 1605311*b^2*c^3 - 14679390*b^2*c^2*z + 994026*b^2*c^2 + 4657380*b^2*c*z - 362938*b^2*c + 59990*b^2 - 565355*b*c^7*z - 19495*b*c^7 + 3470755*b*c^6*z + 225849*b*c^6 - 1470940*b*c^5*z - 1054882*b*c^5 - 14477705*b*c^4*z + 2518019*b*c^4 + 5349925*b*c^3*z - 3027960*b*c^3 + 12350700*b*c^2*z + 1880650*b*c^2 - 4657380*b*c*z - 882360*b*c - 1923650*b - 565355*c^5*z - 19495*c^5 + 1774690*c^4*z + 732719*c^4 + 461000*c^3*z - 3497180*c^3 - 2446565*c^2*z + 1853680*c^2 + 776230*c*z + 6770441*c + 2575402)/15000) * h1 + (-(3899*b^2*c^6 + 1696065*b^2*c^5*z - 59986*b^2*c^5 - 5324070*b^2*c^4*z + 431905*b^2*c^4 - 1383000*b^2*c^3*z - 1526099*b^2*c^3 + 7339695*b^2*c^2*z + 2035459*b^2*c^2 - 2328690*b^2*c*z - 781756*b^2*c + 2187606*b^2 - 3392130*b*c^5*z - 38990*b*c^5 + 10648140*b*c^4*z + 284041*b*c^4 + 2766000*b*c^3*z - 922309*b*c^3 - 14679390*b*c^2*z + 2794829*b*c^2 + 4657380*b*c*z - 3970781*b*c - 1987500*b + 565355*c^5*z + 19495*c^5 - 1774690*c^4*z - 167364*c^4 - 461000*c^3*z + 591780*c^3 + 2446565*c^2*z + 103990*c^2 - 776230*c*z - 983206*c - 4919092)/15000) * h2 + ((3899*c^2 - 17097*c + 5999)/15000) * h3

private lemma rejectI_13_14 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, b, b) = 0) (h2 : locus b (b, b, c) = 0)
    (h3 : edge b b c (b, b, b) (b, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (z*(166*b^5*c^2 - 114*b^5*c - 280*b^5 - 140*b^4*c^3 - 1510*b^4*c^2 + 1778*b^4*c + 472*b^4 + 57*b^3*c^4 + 887*b^3*c^3 + 3090*b^3*c^2 - 2002*b^3*c - 472*b^3 + 218*b^2*c^4 - 122*b^2*c^3 - 4739*b^2*c^2 + 176*b^2*c + 972*b^2 - 280*b*c^5 - 1969*b*c^4 + 1284*b*c^3 - 3127*b*c^2 + 2584*b*c - 604*b + 70*c^6 + 415*c^5 + 409*c^4 + 772*c^3 - 604*c^2)/366) * h1 + (z*(13*b^2*c^5 - 428*b^2*c^4 + 507*b^2*c^3 - 1797*b^2*c^2 + 3540*b^2*c - 2180*b^2 - 8*b*c^5 + 1433*b*c^4 + 133*b*c^3 - 889*b*c^2 - 772*b*c + 604*b + 13*c^6 - 244*c^5 + 96*c^4)/366) * h2 + (-z*(83*b*c - 140*b + 13*c^2 - 244*c + 96)/366) * h3

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
  linear_combination (-1) * h0 + (z*(2*b^4*c - 16*b^3*c + 2*b^2*c^3 - 3*b^2*c^2 + 29*b^2*c + 2*b^2 - 9*b*c^3 + 11*b*c^2 + 15*b*c - 8*b + 4*c^4 - 15*c^3 + 18*c^2 - 7*c)) * h1 + (z*(4*b^2*c^2 - 7*b^2*c + 2*b^2 - 2*b*c^3 - 8*b*c^2 + 21*b*c - 8*b + 2*c^4 - 8*c^3 + 12*c^2 - 8*c + 2)) * h2 + (-2*z) * h3

private lemma rejectI_14_23 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, b, c) = 0) (h2 : locus b (c, b, c) = 0)
    (h3 : edge b b c (b, b, c) (c, b, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((b - 2)*(301*b*c^2 + 246639*b*c + 63661*b - 66220*c^3 - 39251*c^2 + 205824)/411648) * h0 + ((-2408*b^6*c^2 + 3728*b^6*c + 55216*b^6 + 9632*b^5*c^3 - 17320*b^5*c^2 - 217136*b^5*c + 55216*b^5 + 301*b^4*c^4*z - 18060*b^4*c^4 + 246338*b^4*c^3*z + 40000*b^4*c^3 - 182978*b^4*c^2*z + 407520*b^4*c^2 - 63661*b^4*c*z - 294720*b^4*c - 276080*b^4 - 66521*b^3*c^5*z + 20468*b^3*c^5 - 220874*b^3*c^4*z - 52156*b^3*c^4 - 1009461*b^3*c^3*z - 464136*b^3*c^3 + 1184375*b^3*c^2*z + 517568*b^3*c^2 + 112481*b^3*c*z + 596192*b^3*c - 165648*b^3 + 66220*b^2*c^6*z - 14448*b^2*c^6 + 306539*b^2*c^5*z + 22368*b^2*c^5 + 1797511*b^2*c^4*z + 404740*b^2*c^4 - 1126889*b^2*c^3*z - 181128*b^2*c^3 - 1881518*b^2*c^2*z - 1577296*b^2*c^2 + 838137*b^2*c*z + 1542320*b^2*c - 55216*b^2 + 1204*b*c^7 - 331401*b*c^6*z + 37868*b*c^6 - 314668*b*c^5*z - 196276*b*c^5 - 3234027*b*c^4*z - 677744*b*c^4 + 4694218*b*c^3*z + 2343096*b*c^3 - 5667*b*c^2*z - 1585316*b*c^2 - 808455*b*c*z - 57660*b*c + 55216*b + 66220*c^7*z - 7224*c^7 - 26066*c^6*z + 28040*c^6 + 699763*c^5*z + 132328*c^5 - 754758*c^4*z - 371716*c^4 + 14841*c^3*z + 186544*c^3 + 24260*c^2 + 395947*c - 116604)/411648) * h1 + (-(-4816*b^2*c^6 + 199563*b^2*c^5*z + 12272*b^2*c^5 + 657204*b^2*c^4*z + 118628*b^2*c^4 - 1405701*b^2*c^3*z - 162356*b^2*c^3 - 259521*b^2*c^2*z - 316032*b^2*c^2 + 808455*b^2*c*z + 583212*b^2*c - 282252*b^2 + 1204*b*c^7 - 198961*b*c^6*z + 23420*b*c^6 - 366800*b*c^5*z - 140196*b*c^5 - 1834501*b*c^4*z - 413088*b*c^4 + 3184702*b*c^3*z + 1599664*b*c^3 + 24015*b*c^2*z - 1212228*b*c^2 - 808455*b*c*z + 57080*b*c + 224763*b + 66220*c^7*z - 7224*c^7 - 26066*c^6*z + 28040*c^6 + 699763*c^5*z + 132328*c^5 - 754758*c^4*z - 371716*c^4 + 14841*c^3*z + 186544*c^3 + 24260*c^2 + 263507*c - 195106)/411648) * h2 + ((301*c^2 - 466*c - 6902)/102912) * h3

private lemma rejectI_14_24 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, b, c) = 0) (h2 : locus b (c, c, 1) = 0)
    (h3 : edge b b c (b, b, c) (c, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((114933506173556896409994*b^6*c^2 + 77812566083895274362382*b^6*c - 37120940089661622047612*b^6 - 355940204024582214545534*b^5*c^3 - 1585356096218435371406856*b^5*c^2 + 328414369606608823677894*b^5*c + 37285799168276795963156*b^5 + 509428562858502558398822*b^4*c^4 + 4255190373250546279883526*b^4*c^3 + 1890103768588911123100235*b^4*c^2 - 998952005394463924328685*b^4*c + 143569201323860118879490*b^4 - 306976717667840687706576*b^3*c^5 - 5832547552471943305735196*b^3*c^4 - 2797525874791849875052267*b^3*c^3 - 532785478425782752573659*b^3*c^2 + 128704594386659025701310*b^3*c - 74654027875861178884084*b^3 + 54830334312903844255484*b^2*c^6 + 3357035005960100906561788*b^2*c^5 + 517835453236706179666309*b^2*c^4 + 5034689006946652267564118*b^2*c^3 - 3180540291949775536229462*b^2*c^2 + 1539553141897858208096378*b^2*c - 219801907512726801477952*b^2 - 3442393986552890497630648*b*c^6 + 14221443731451693411089832*b*c^5 - 24155045145836742293377619*b*c^4 + 13214160160981097946161089*b*c^3 - 3733939562555361871370348*b*c^2 + 560087500650511248307262*b*c - 43614177437453495072948*b + 712794346067749975321292*c^7 - 4237939923377837206159110*c^6 + 13216033611814827017390003*c^5 - 18601574000057909664221110*c^4 + 11531763429776755074965700*c^3 - 2587040103736344246073659*c^2 - 25576181320358137244023*c + 46264439761457629238362)/463967372565043937268) * h1 + ((3556276513308741511408030*b^2*c^5 - 5499446810620191371480822*b^2*c^4 - 894152554396408828344522*b^2*c^3 + 2880167980508475849137868*b^2*c^2 - 964047265408487263982225*b^2*c + 53334683884402610968102*b^2 - 1469233496132560505674568*b*c^6 - 12300173593186374419248236*b*c^5 + 33928743001345826565686177*b*c^4 - 23804886896997889771106562*b*c^3 + 7094876435255540729994650*b*c^2 - 861491917075496627104842*b*c + 23145310922386832503676*b + 164491002938711532766452*c^7 + 4075537409400254717712622*c^6 - 9530594730463744335028027*c^5 + 6431592454646454579455202*c^4 - 2926139343028557081812529*c^3 + 1161268178254919318059087*c^2 - 271180545937647246002363*c + 25847392922418075817498)/463967372565043937268) * h2 + (-(57466753086778448204997*b^2*c - 18560470044830811023806*b^2 - 63036595838734210862773*b*c^2 - 77161355318803718428303*b*c + 18642899584138397981578*b + 13707583578225961063871*c^3 + 33444867611943421410685*c^2 - 18274225184247015074599*c + 25383425549853031880230)/463967372565043937268) * h3

private lemma rejectI_15_18 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, c, 1) = 0) (h2 : locus b (c, 1, 1) = 0)
    (h3 : edge b b c (b, c, 1) (c, 1, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((2832*b^3 - 25802*b^2*c - 4248*b^2 - 31070*b*c^2 + 118160*b*c - 2436*c^3 + 6288*c^2 - 5268*c - 6603)/8019) * h0 + ((47412*b^6*c*z - 2672*b^6*c - 142236*b^6*z + 14136*b^6 - 208008*b^5*c^2*z + 16032*b^5*c^2 + 919188*b^5*c*z - 92832*b^5*c - 426708*b^5*z + 42408*b^5 - 41416*b^4*c^3 - 2705508*b^4*c^2*z + 267204*b^4*c^2 + 2847744*b^4*c*z - 249104*b^4*c + 284472*b^4*z - 28272*b^4 - 1564596*b^3*c^4*z + 59452*b^3*c^4 + 11886588*b^3*c^3*z - 446122*b^3*c^3 - 13240152*b^3*c^2*z + 733606*b^3*c^2 + 1590624*b^3*c*z - 192560*b^3*c + 284472*b^3*z - 28272*b^3 + 1365768*b^2*c^5*z - 47762*b^2*c^5 - 6351642*b^2*c^4*z + 428365*b^2*c^4 + 1341468*b^2*c^3*z - 1072060*b^2*c^3 + 3001185*b^2*c^2*z + 749165*b^2*c^2 + 74277*b^2*c*z + 20256*b^2*c - 426708*b^2*z + 42408*b^2 - 133056*b*c^6*z + 19706*b*c^6 + 400734*b*c^5*z - 223157*b*c^5 - 223452*b*c^4*z + 908610*b*c^4 + 4743333*b*c^3*z - 1547115*b*c^3 - 5438691*b*c^2*z + 1031140*b*c^2 + 508896*b*c*z - 98584*b*c + 568944*b*z - 56544*b + 47412*c^5*z - 2672*c^5 - 331884*c^4*z + 24824*c^4 + 853416*c^3*z - 72576*c^3 - 1043064*c^2*z + 95504*c^2 + 616356*c*z - 190760*c - 142236*z + 90600)/433026) * h1 + ((246240*b^2*c^5*z - 1670*b^2*c^5 - 1159326*b^2*c^4*z + 7833*b^2*c^4 + 2474550*b^2*c^3*z - 89221*b^2*c^3 - 426519*b^2*c^2*z + 324711*b^2*c^2 - 782514*b^2*c*z - 370917*b^2*c - 636903*b^2*z - 7632*b^2 - 929880*b*c^5*z + 35404*b*c^5 + 1235844*b*c^4*z - 222706*b*c^4 + 1062936*b*c^3*z + 536666*b*c^3 - 2264544*b*c^2*z - 562382*b*c^2 + 468936*b*c*z + 315258*b*c + 426708*b*z - 10440*b + 133056*c^6*z - 19706*c^6 + 149850*c^5*z + 167713*c^5 - 565812*c^4*z - 536130*c^4 - 600183*c^3*z + 844436*c^3 + 1843317*c^2*z - 674476*c^2 - 1170423*c*z + 276555*c + 210195*z - 1626012)/433026) * h2 + (-2*(11853*c*z - 668*c - 35559*z + 3534)/216513) * h3

private lemma rejectI_15_21 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, c, 1) = 0) (h2 : locus b (c, b, 1) = 0)
    (h3 : edge b b c (b, c, 1) (c, b, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((54166528000*b^3 + 118337709750*b^2*c^2*z + 435634700166*b^2*c^2 - 290127122500*b^2*c*z - 1085211378980*b^2*c - 109499894750*b^2*z - 524547338606*b^2 + 92066719875*b*c^3*z + 338923729323*b*c^3 - 349076498000*b*c^2*z - 1323505043408*b*c^2 + 188619040375*b*c*z + 781682090751*b*c + 218999789500*b*z + 886595093212*b + 16448932500*c^4*z + 60553189620*c^4 - 75735478500*c^3*z - 286967890116*c^3 + 62296159625*c^2*z + 284011948289*c^2 + 101508082125*c*z + 321258568229*c - 109499894750*z - 487045002606)/70830720000) * h0 + ((24999936000*b^6*c*z + 92031860736*b^6*c - 100414464000*b^6*z - 367560105984*b^6 - 398804729856*b^5*c^2 + 376796160000*b^5*c*z + 1776824180736*b^5*c - 200828928000*b^5*z - 735120211968*b^5 + 236675419500*b^4*c^4*z^2 + 871269400332*b^4*c^4*z - 816929664500*b^4*c^3*z^2 - 2891692542292*b^4*c^3*z + 751593529344*b^4*c^3 + 361254455500*b^4*c^2*z^2 - 302888495252*b^4*c^2*z - 4029429977088*b^4*c^2 + 218999789500*b^4*c*z^2 + 2549555221212*b^4*c*z + 4104421183488*b^4*c + 65795730000*b^3*c^5*z^2 + 242212758480*b^3*c^5*z - 1302185571750*b^3*c^4*z^2 - 5090953759478*b^3*c^4*z - 774601494528*b^3*c^4 + 3754017674750*b^3*c^3*z^2 + 16026202253966*b^3*c^3*z + 5256379619328*b^3*c^3 - 1313128990750*b^3*c^2*z^2 - 7224107920302*b^3*c^2*z - 9442941272064*b^3*c^2 - 1204498842250*b^3*c*z^2 - 4430978676666*b^3*c*z + 3216150927360*b^3*c - 118337709750*b^2*c^6*z^2 - 435634700166*b^2*c^6*z + 408228321625*b^2*c^5*z^2 + 1639766776401*b^2*c^5*z + 440985999360*b^2*c^5 + 397888213500*b^2*c^4*z^2 + 695015153436*b^2*c^4*z - 3889462287360*b^2*c^4 - 1846277400750*b^2*c^3*z^2 - 5583776483262*b^2*c^3*z + 10505355082752*b^2*c^3 - 319750003750*b^2*c^2*z^2 - 2705482633590*b^2*c^2*z - 8021251292160*b^2*c^2 + 1478248579125*b^2*c*z^2 + 6138730127181*b^2*c*z + 45945013248*b^2*c - 92066719875*b*c^7*z^2 - 338923729323*b*c^7*z + 894849942125*b*c^6*z^2 + 3287339626949*b*c^6*z - 116957156352*b*c^6 - 2822208694500*b*c^5*z^2 - 10241923199172*b*c^5*z + 1373046263808*b*c^5 + 2336101178000*b*c^4*z^2 + 7694137262608*b*c^4*z - 5284809271296*b*c^4 + 2370819759875*b*c^3*z^2 + 10566380999723*b*c^3*z + 7369770381312*b*c^3 - 1811496307625*b*c^2*z^2 - 7131151419937*b*c^2*z - 3131036083200*b*c^2 - 875999158000*b*c*z^2 - 3309103188848*b*c*z + 1238837452800*b*c - 272769902000*b*z - 457775053872*b - 92066719875*c^5*z^2 - 334757073323*c^5*z + 15338643456*c^5 + 618649782500*c^4*z^2 + 2262166006980*c^4*z - 147539887104*c^4 - 1150392786750*c^3*z^2 - 4154036796878*c^3*z + 853638829056*c^3 + 240560092500*c^2*z^2 + 396049284100*c^2*z - 2271624683568*c^2 + 383249631625*c*z^2 + 1642006639121*c*z + 1181657082000*c - 96851583500*z - 805841094316)/283322880000) * h1 + (-(92066719875*b^2*c^6*z^2 + 338923729323*b^2*c^6*z - 605632542875*b^2*c^5*z^2 - 2255981532931*b^2*c^5*z - 5751991296*b^2*c^5 + 243028175250*b^2*c^4*z^2 + 1038297887874*b^2*c^4*z - 35506071552*b^2*c^4 + 2899281529750*b^2*c^3*z^2 + 10577043309926*b^2*c^3*z + 594491271168*b^2*c^3 - 2354994145125*b^2*c^2*z^2 - 9518026599677*b^2*c^2*z - 2016004921344*b^2*c^2 - 273749736875*b^2*c*z^2 + 370492389485*b^2*c*z + 2523619918848*b^2*c - 545539804000*b^2*z - 915550107744*b^2 - 118337709750*b*c^6*z^2 - 435634700166*b*c^6*z + 645140251750*b*c^5*z^2 + 2461906967478*b*c^5*z + 256922277888*b*c^5 - 1115894602000*b*c^4*z^2 - 4605293042832*b*c^4*z - 2381657911296*b*c^4 + 660219393000*b*c^3*z^2 + 4017262021288*b*c^3*z + 7729030557696*b*c^3 + 38372561750*b*c^2*z^2 - 1909524947162*b*c^2*z - 10260222382080*b*c^2 - 109499894750*b*c*z^2 + 364759395394*b*c*z + 4621317301296*b*c - 466473069000*b*z - 2286123354504*b - 92066719875*c^7*z^2 - 338923729323*c^7*z + 802783222250*c^6*z^2 + 2948415897626*c^6*z - 116957156352*c^6 - 2479759071625*c^5*z^2 - 9013125884161*c^5*z + 1164057246720*c^5 + 3159995448500*c^4*z^2 + 10900493154836*c^4*z - 4368654987264*c^4 - 1248263340125*c^3*z^2 - 3001186811957*c^3*z + 7726416838656*c^3 - 525939170750*c^2*z^2 - 3234000216142*c^2*z - 6576827735040*c^2 + 383249631625*c*z^2 + 1429677477621*c*z + 1508304997716*c + 341147995500*z + 859016036108)/283322880000) * h2 + (-(1017250*c*z + 3744786*c - 4085875*z - 14956059)/69170625) * h3

private lemma rejectI_16_19 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, c, b) = 0) (h2 : locus b (c, 1, b) = 0)
    (h3 : edge b b c (b, c, b) (c, 1, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((36764931894775812879*b^3 + 35731099183964082015*b^2*c^2 + 348917005266172992*b^2*c*z - 114998753685105181552*b^2*c - 2750051959307984808*b^2*z + 9761343561812843471*b^2 - 22211223817058753685*b*c^3 - 2130258166393153248*b*c^2*z + 130536579622195766393*b*c^2 + 5445022971481181136*b*c*z - 223345329114849732205*b*c + 5500103918615969616*b*z - 129817482807953125579*b - 312885651325376334*c^4 + 105598442871370152*c^3*z + 5298514483166125343*c^3 - 991670068663730496*c^2*z + 7336892095134238767*c^2 + 2456215901176600296*c*z - 21824334938465932567*c - 2750051959307984808*z + 80889062433124193429)/2402144918240275800) * h0 + (-(5794232300102283570*b^6*c^2*z + 247917517165932624*b^6*c*z^2 - 9585099888799195572*b^6*c*z + 82653718485108*b^6*c - 743752551497797872*b^6*z^2 - 23405031244997362854*b^6*z - 1507340811559094*b^6 - 37662509950664843205*b^5*c^3*z - 1611463861578562056*b^5*c^2*z^2 - 27711833356774674924*b^5*c^2*z - 537249170153202*b^5*c^2 + 5702102894816450352*b^5*c*z^2 + 228879649166013112686*b^5*c*z + 10087003289831989*b^5*c - 2603133930242292552*b^5*z^2 - 81917609357490769989*b^5*z - 5275692840456829*b^5 + 3539723051771234568*b^4*c^3*z^2 + 266378244196653298071*b^4*c^3*z + 1529093791974498*b^4*c^3 - 9544824410888406024*b^4*c^2*z^2 - 393086346834218043153*b^4*c^2*z - 29580206242787953*b^4*c^2 + 6872812669197935640*b^4*c*z^2 + 182995334099301750795*b^4*c*z + 30859159777718873*b^4*c + 371876275748898936*b^4*z^2 + 11702515622498681427*b^4*z + 753670405779547*b^4 - 2479611554553240*b^3*c^4 + 6321790177612512984*b^3*c^3*z^2 - 442422244144459836456*b^3*c^3*z + 49518217707998436*b^3*c^3 - 61208033011358579424*b^3*c^2*z^2 + 676618243911702254823*b^3*c^2*z - 79290913104409076*b^3*c^2 + 48688304904597750840*b^3*c*z^2 - 521978284171788705777*b^3*c*z + 16332787771694710*b^3*c + 2231257654493393616*b^3*z^2 + 70215093734992088562*b^3*z + 4522022434677282*b^3 + 102337722205766091477*b^2*c^6*z + 482038170018475896*b^2*c^5*z^2 - 1015684959931702322880*b^2*c^5*z + 2396957836068132*b^2*c^5 - 35383220633161418472*b^2*c^4*z^2 + 3744072054739396013700*b^2*c^4*z - 48506799207349990*b^2*c^4 + 163653261568261079472*b^2*c^3*z^2 - 5554878219291583767279*b^2*c^3*z + 88624245988461518*b^2*c^3 - 84843084838121283744*b^2*c^2*z^2 + 2080931332674789054156*b^2*c^2*z - 20616635990330243*b^2*c^2 - 43661076749830920528*b^2*c*z^2 + 622042385009093969394*b^2*c*z - 22444804736416194*b^2*c - 1487505102995595744*b^2*z^2 - 46810062489994725708*b^2*z - 3014681623118188*b^2 - 93646373755612666122*b*c^7*z - 3649884946040811528*b*c^6*z^2 + 1019131975877368931967*b*c^6*z - 1322459495761728*b*c^6 + 53081942402136360240*b*c^5*z^2 - 4200268347131075888136*b*c^5*z + 24448067858885936*b*c^5 - 170677839744906297984*b*c^4*z^2 + 7781134081472562942219*b*c^4*z - 7351822741998104*b*c^4 + 81083037997810895256*b*c^3*z^2 - 5317743050178418412592*b*c^3*z + 12297971241575060*b*c^3 + 47063150688824568360*b*c^2*z^2 - 528639267394381294992*b*c^2*z + 163312585970362186*b*c^2 - 4297272467582421792*b*c*z^2 + 1423622764150274979864*b*c*z + 734929498415572936*b*c - 2231257654493393616*b*z^2 - 60536626286384343546*b*z + 3970335697646653596*b + 2897116150051141785*c^6*z + 123958758582966312*c^5*z^2 - 115821620600319114618*c^5*z + 41326859242554*c^5 - 4765513773287508336*c^4*z^2 + 781319684004890114955*c^4*z - 2324091056996599*c^4 + 45479174045754016080*c^3*z^2 - 2174871548075824128939*c^3*z + 25374653539461020*c^3 - 56167221012515897616*c^2*z^2 + 2590425799497445871370*c^2*z + 982905978112968235*c^2 + 14337931912802693064*c*z^2 - 1121520750672303381528*c*z - 15682643066711059823*c + 1115628827246696808*z^2 + 34742813069519553969*z - 21092973646552181889)/7206434754720827400) * h1 + (-(23176929200409134280*b^2*c^6*z + 991670068663730496*b^2*c^5*z^2 - 18222877081084299351*b^2*c^5*z + 330614873940432*b^2*c^5 - 14875157540074726368*b^2*c^4*z^2 - 596576036782987053171*b^2*c^4*z - 491564107734140*b^2*c^4 - 13538885393932568856*b^2*c^3*z^2 + 1501117421738199632178*b^2*c^3*z - 93594326570042132*b^2*c^3 + 28827203292577593288*b^2*c^2*z^2 + 632601751915679268558*b^2*c^2*z - 81636681070886807*b^2*c^2 - 5619428219054883168*b^2*c*z^2 - 1670603600726581544409*b^2*c*z - 753977892856274381*b^2*c + 4090639033237888296*b^2*z^2 + 119049204398877750681*b^2*z - 3966567345617755861*b^2 - 348511449671990388423*b*c^6*z - 9944187905145314736*b*c^5*z^2 + 2792454342396069756972*b*c^5*z - 5868414012442668*b*c^5 + 154163624614626230856*b*c^4*z^2 - 8490555838293098704089*b*c^4*z + 92722104322771990*b*c^4 - 224600006238615412632*b*c^3*z^2 + 11032753892663267040921*b*c^3*z + 200432745905594422*b*c^3 + 91371614960197099152*b*c^2*z^2 - 6233499415816936888251*b*c^2*z + 830494401584261000*b*c^2 - 11238962948228535264*b*c*z^2 + 1229012393081929957095*b*c*z + 3764770286400598004*b*c - 371876275748898936*b*z^2 - 11337781824522191115*b*z - 89200314696963697654*b + 93646373755612666122*c^7*z + 3649884946040811528*c^6*z^2 - 720810157710224082891*c^6*z + 1322459495761728*c^6 - 41388535012516127784*c^5*z^2 + 2115256069643799415011*c^5*z - 20232728216145428*c^5 + 48109901704623087336*c^4*z^2 - 2626655792696167010280*c^4*z - 56380617408383518*c^4 - 5041025019080219664*c^3*z^2 + 1265983321727362082112*c^3*z - 197207071783086956*c^3 - 7437525514977978720*c^2*z^2 - 175653121384559855385*c^2*z - 929255656092682941*c^2 + 2355216413076359928*c*z^2 + 58053896087062689888*c*z + 65477568164691717537*c - 371876275748898936*z^2 - 3452359744574727003*z - 249874375724499187234)/7206434754720827400) * h2 + ((2897116150051141785*c^2*z + 123958758582966312*c*z^2 - 4792549944399597786*c*z + 41326859242554*c - 371876275748898936*z^2 - 11702515622498681427*z - 753670405779547)/7206434754720827400) * h3

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
  linear_combination ((b - 2)*(301*b*c^2 + 246639*b*c + 63661*b - 66220*c^3 - 39251*c^2 + 205824)/411648) * h0 + ((-2408*b^6*c^2 + 3728*b^6*c + 55216*b^6 + 9632*b^5*c^3 - 17320*b^5*c^2 - 217136*b^5*c + 55216*b^5 + 301*b^4*c^4*z - 18060*b^4*c^4 + 246338*b^4*c^3*z + 40000*b^4*c^3 - 182978*b^4*c^2*z + 407520*b^4*c^2 - 63661*b^4*c*z - 294720*b^4*c - 276080*b^4 - 66521*b^3*c^5*z + 20468*b^3*c^5 - 220874*b^3*c^4*z - 52156*b^3*c^4 - 1009461*b^3*c^3*z - 464136*b^3*c^3 + 1184375*b^3*c^2*z + 517568*b^3*c^2 + 112481*b^3*c*z + 596192*b^3*c - 165648*b^3 + 66220*b^2*c^6*z - 14448*b^2*c^6 + 306539*b^2*c^5*z + 22368*b^2*c^5 + 1797511*b^2*c^4*z + 404740*b^2*c^4 - 1126889*b^2*c^3*z - 181128*b^2*c^3 - 1881518*b^2*c^2*z - 1577296*b^2*c^2 + 838137*b^2*c*z + 1542320*b^2*c - 55216*b^2 + 1204*b*c^7 - 331401*b*c^6*z + 37868*b*c^6 - 314668*b*c^5*z - 196276*b*c^5 - 3234027*b*c^4*z - 677744*b*c^4 + 4694218*b*c^3*z + 2343096*b*c^3 - 5667*b*c^2*z - 1585316*b*c^2 - 808455*b*c*z - 57660*b*c + 55216*b + 66220*c^7*z - 7224*c^7 - 26066*c^6*z + 28040*c^6 + 699763*c^5*z + 132328*c^5 - 754758*c^4*z - 371716*c^4 + 14841*c^3*z + 186544*c^3 + 24260*c^2 + 395947*c - 116604)/411648) * h1 + (-(-4816*b^2*c^6 + 199563*b^2*c^5*z + 12272*b^2*c^5 + 657204*b^2*c^4*z + 118628*b^2*c^4 - 1405701*b^2*c^3*z - 162356*b^2*c^3 - 259521*b^2*c^2*z - 316032*b^2*c^2 + 808455*b^2*c*z + 583212*b^2*c - 282252*b^2 + 1204*b*c^7 - 198961*b*c^6*z + 23420*b*c^6 - 366800*b*c^5*z - 140196*b*c^5 - 1834501*b*c^4*z - 413088*b*c^4 + 3184702*b*c^3*z + 1599664*b*c^3 + 24015*b*c^2*z - 1212228*b*c^2 - 808455*b*c*z + 57080*b*c + 224763*b + 66220*c^7*z - 7224*c^7 - 26066*c^6*z + 28040*c^6 + 699763*c^5*z + 132328*c^5 - 754758*c^4*z - 371716*c^4 + 14841*c^3*z + 186544*c^3 + 24260*c^2 + 263507*c - 195106)/411648) * h2 + ((301*c^2 - 466*c - 6902)/102912) * h3

private lemma rejectI_16_26 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, c, b) = 0) (h2 : locus b (c, c, c) = 0)
    (h3 : edge b b c (b, c, b) (c, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (z*(22*b^6*c + 22*b^6 - 222*b^5*c - 90*b^5 - b^4*c^3 - 169*b^4*c^2 + 454*b^4*c + 104*b^4 + b^3*c^4 + 168*b^3*c^3 + 1663*b^3*c^2 - 288*b^3*c - 116*b^3 + 5*b^2*c^5 - 100*b^2*c^4 - 1508*b^2*c^3 - 2664*b^2*c^2 + 910*b^2*c - 12*b^2 - 24*b*c^5 + 647*b*c^4 + 1980*b*c^3 - 1094*b*c^2 - 234*b*c + 92*b + 5*c^6 - 96*c^5 + 27*c^4)/14) * h1 + (-z*(9*b^2*c^4 - 330*b^2*c^3 - 186*b^2*c^2 + 482*b^2*c - 196*b^2 - 5*b*c^5 + 107*b*c^4 + 1496*b*c^3 - 916*b*c^2 - 142*b*c + 92*b - 3*c^5 - 423*c^4 + 134*c^3 + 92*c^2)/14) * h2 + (-z*(11*b^2 + 11*b*c - 12*b + 5*c^2 - 96*c + 27)/14) * h3

private lemma rejectI_17_20 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (b, c, c) = 0) (h2 : locus b (c, 1, c) = 0)
    (h3 : edge b b c (b, c, c) (c, 1, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((c - 2)*(289523816*b^3 - 7345786621*b^2 - 35886371632*b*c^2 + 81503994416*b*c + 877899095*b + 12259803776*c^3 - 52272871754*c^2 + 67771379047*c - 27753264202)/5046867) * h0 + ((18735616*b^7 + 108672256*b^6*c - 429069632*b^6 + 1737142896*b^5*c^3*z - 5211428688*b^5*c^2*z - 930254592*b^5*c^2 + 3474285792*b^5*c*z + 2912597856*b^5*c - 1274081952*b^5 - 51023291310*b^4*c^3*z + 2370126464*b^4*c^3 + 153069873930*b^4*c^2*z - 8056686240*b^4*c^2 - 102046582620*b^4*c*z + 5019546272*b^4*c + 2061962656*b^4 - 216186801240*b^3*c^5*z + 1141058656008*b^3*c^4*z - 2972957696*b^3*c^4 - 1729170657318*b^3*c^3*z + 12596004016*b^3*c^3 + 442903398498*b^3*c^2*z - 13277209520*b^3*c^2 + 361395404052*b^3*c*z - 1180866384*b^3*c + 2125657744*b^3 + 72690251208*b^2*c^6*z + 357682295019*b^2*c^5*z + 1682035392*b^2*c^5 - 3230787103491*b^2*c^4*z - 9386890688*b^2*c^4 + 5935285387935*b^2*c^3*z + 14111426512*b^2*c^3 - 2808978652101*b^2*c^2*z + 262682016*b^2*c^2 - 325892178570*b^2*c*z - 6846833648*b^2*c - 2652626976*b^2 - 287139909552*b*c^6*z + 1817054980647*b*c^5*z + 2840394688*b*c^5 - 4738489227825*b*c^4*z - 8829549840*b*c^4 + 6410700776085*b*c^3*z + 19709140016*b*c^3 - 4402871747439*b*c^2*z + 8616907568*b*c^2 + 1200745128084*b*c*z - 83157004416*b*c + 918090232*b + 72690251208*c^7*z - 446975087469*c^6*z - 11709760*c^6 + 1080530229165*c^5*z - 35129280*c^5 - 1318419460050*c^4*z - 9045795520*c^4 + 850989612498*c^3*z + 3009980112*c^3 - 270350081025*c^2*z - 42766608576*c^2 + 31534535673*c*z + 181826550976*c - 4085334104)/60562404) * h1 + ((214449658344*b^2*c^6*z - 1958550474426*b^2*c^5*z - 288067200*b^2*c^5 + 6828217675308*b^2*c^4*z - 756455984*b^2*c^4 - 10567529358288*b^2*c^3*z - 1720841200*b^2*c^3 + 6621088555800*b^2*c^2*z - 11338834560*b^2*c^2 - 1137676056738*b^2*c*z - 31697999232*b^2*c + 167135178000*b^2 - 72690251208*b*c^7*z + 446975087469*b*c^6*z + 11709760*b*c^6 - 1080530229165*b*c^5*z + 1305438144*b*c^5 + 1318419460050*b*c^4*z + 2821588800*b*c^4 - 850989612498*b*c^3*z + 6646797616*b*c^3 + 270350081025*b*c^2*z + 38966808128*b*c^2 - 31534535673*b*c*z - 173935524352*b*c - 15061873872*b + 211718144*c^5 - 1322781248*c^4 + 3173943552*c^3 + 143415320704*c^2 - 625159108216*c + 665662994580)/60562404) * h2 + (-16*(292744*b + 3308096*c - 7436073)/15140601) * h3

private lemma rejectI_18_21 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (c, 1, 1) = 0) (h2 : locus b (c, b, 1) = 0)
    (h3 : edge b b c (c, 1, 1) (c, b, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination ((2*c^2 - 6*c - 9)/9) * h0 + ((-16*b^5*c^2 + 324*b^5*c*z + 52*b^5*c - 648*b^5*z + 8*b^5 + 16*b^4*c^3 - 324*b^4*c^2*z + 44*b^4*c^2 - 324*b^4*c*z - 292*b^4*c + 1620*b^4*z - 92*b^4 - 16*b^3*c^4 + 486*b^3*c^3*z + 20*b^3*c^3 - 1620*b^3*c^2*z - 36*b^3*c^2 + 1215*b^3*c*z + 378*b^3*c + 729*b^3*z + 216*b^3 + 16*b^2*c^5 - 648*b^2*c^4*z - 84*b^2*c^4 + 3402*b^2*c^3*z + 116*b^2*c^3 - 4212*b^2*c^2*z - 130*b^2*c^2 + 3969*b^2*c*z + 328*b^2*c - 3807*b^2*z - 70*b^2 - 16*b*c^6 + 648*b*c^5*z + 132*b*c^5 - 4536*b*c^4*z - 304*b*c^4 + 10044*b*c^3*z + 174*b*c^3 - 10044*b*c^2*z - 22*b*c^2 + 486*b*c*z - 180*b*c + 4374*b*z - 198*b - 16*c^4 + 648*c^3*z + 84*c^3 - 2592*c^2*z - 238*c^2 + 4050*c*z + 404*c - 2268*z + 298)/729) * h1 + (-2*(486*b^5*z + 30*b^5 - 2916*b^4*z - 180*b^4 + 3645*b^3*z + 225*b^3 + 2673*b^2*z + 165*b^2 - 8*b*c^6 + 324*b*c^5*z + 74*b*c^5 - 2592*b*c^4*z - 210*b*c^4 + 7290*b*c^3*z + 205*b*c^3 - 9396*b*c^2*z - 122*b*c^2 + 4941*b*c*z + 11*b*c - 1944*b*z - 120*b - 77*c^2 - 81*c*z + 226*c + 243*z + 15)/729) * h2 + (-2*(c - 3)*(-4*c + 81*z + 5)/729) * h3

private lemma rejectI_19_22 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (c, 1, b) = 0) (h2 : locus b (c, b, b) = 0)
    (h3 : edge b b c (c, 1, b) (c, b, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-z*(6*b^2*c^4 - 38*b^2*c^3 + 62*b^2*c^2 - 36*b^2*c + 30*b^2 - 8*b*c^5 + 62*b*c^4 - 173*b*c^3 + 271*b*c^2 - 222*b*c - b - 3*c + 10)) * h1 + (z*(2*b^5*c + 2*b^5 + 8*b^4*c^2 - 28*b^4*c - 32*b^4 + 6*b^3*c^3 - 70*b^3*c^2 + 129*b^3*c + 135*b^3 - 2*b^2*c^4 - 14*b^2*c^3 + 145*b^2*c^2 - 198*b^2*c - 139*b^2 - 8*b*c^5 + 70*b*c^4 - 195*b*c^3 + 204*b*c^2 - 90*b*c - 88*b - 8*c^3 + 46*c^2 - 76*c + 80)) * h2 + (-z*(b + 3*c - 10)) * h3

private lemma rejectI_19_25 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (c, 1, b) = 0) (h2 : locus b (c, c, b) = 0)
    (h3 : edge b b c (c, 1, b) (c, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(283415*b^6 - 2338616*b^5 + 5470008*b^4 - 1690629*b^3 + 242068*b^2 + 16808*b*c^5 + 232403*b*c^4 - 3316393*b*c^3 + 15849351*b*c^2 - 32314306*b*c + 6180389*b - 4456*c^6 - 70280*c^5 + 735534*c^4 - 3069498*c^3 + 5977832*c^2 + 1640*c - 33322)/5013) * h1 + ((11768*b^7*c + 283415*b^7 - 21264*b^6*c^2 - 620499*b^6*c - 2622031*b^6 + 16224*b^5*c^3 + 522983*b^5*c^2 + 3814140*b^5*c + 7536977*b^5 - 21264*b^4*c^4 - 550323*b^4*c^3 - 1152822*b^4*c^2 - 6820873*b^4*c - 5112033*b^4 + 4456*b^3*c^5 + 147872*b^3*c^4 + 979820*b^3*c^3 - 263788*b^3*c^2 + 353208*b^3*c - 2631469*b^3 + 2856*b^2*c^5 + 90031*b^2*c^4 + 676781*b^2*c^3 + 2875366*b^2*c^2 - 8560062*b^2*c + 5232291*b^2 - 21264*b*c^6 - 437859*b*c^5 + 1561344*b*c^4 - 4404586*b*c^3 + 12813902*b*c^2 - 13395121*b*c - 9448112*b + 4456*c^7 + 87520*c^6 - 450482*c^5 + 639289*c^4 + 64796*c^3 - 517007*c^2 - 1793548*c + 5507439)/5013) * h2 + (-(11768*b^2*c + 283415*b^2 - 21264*b*c^2 - 538123*b*c - 626358*b + 4456*c^3 + 114256*c^2 + 168214*c + 28309)/5013) * h3

private lemma rejectI_19_26 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (c, 1, b) = 0) (h2 : locus b (c, c, c) = 0)
    (h3 : edge b b c (c, 1, b) (c, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(4821092010900*b*c*z - 316770859140780*b*c - 9305620296225*b*z + 626995985258579*b - 9082997801100*c^2*z + 596800270669620*c^2 + 17181196657875*c*z - 1252135065480957*c + 1659852580125*z + 97365866635229)/24254248244664) * h0 + ((8548703812800*b^5*z^2 - 672478150063656*b^5*z - 16117278258306*b^5 - 22796543500800*b^4*z^2 + 1793564837492330*b^4*z + 23568673964468*b^4 + 23553459984225*b^3*z^2 - 1747406541156787*b^3*z - 52743110062974*b^3 + 80188622744025*b^2*z^2 - 6261367660470085*b^2*z - 246009877835527*b^2 - 193180437276*b*c^5*z + 12940489816232*b*c^5 + 5699135875200*b*c^4*z^2 - 445952306352473*b*c^4*z - 169265852421046*b*c^4 - 69814414471200*b*c^3*z^2 + 5480217475731326*b*c^3*z + 914524072991535*b*c^3 + 372046713852900*b*c^2*z^2 - 28885579323598276*b*c^2*z - 2535755512353419*b*c^2 - 1069166795087325*b*c*z^2 + 82191230723775025*b*c*z + 4487260585980791*b*c + 232462409409525*b*z^2 - 17837909226251272*b*z - 963565388504579*b + 9082997801100*c^2*z - 596800270669620*c^2 - 17229491767194*c*z + 1255370187935015*c + 1424783968800*z^2 - 113739544257401*z - 75797831433616)/24254248244664) * h1 + (-(-96590218638*b^5*c*z + 6470244908116*b^5*c + 2849567937600*b^5*z^2 - 223869612698638*b^5*z - 24783160810450*b^5 - 48295109319*b^4*c^3*z + 3235122454058*b^4*c^3 + 6245875979700*b^4*c^2*z^2 - 428271009506228*b^4*c^2*z - 41507682491747*b^4*c^2 - 22675416119925*b^4*c*z^2 + 1615037616730040*b^4*c*z + 96995339609756*b^4*c + 19279108077825*b^4*z^2 - 1411747007436787*b^4*z - 5863001485125*b^4 + 96590218638*b^3*c^4*z - 6470244908116*b^3*c^4 - 16753657749600*b^3*c^3*z^2 + 1136764610978572*b^3*c^3*z + 70074875167262*b^3*c^3 + 64065494131200*b^3*c^2*z^2 - 4715158694598045*b^3*c^2*z - 212245261109862*b^3*c^2 - 73937486798550*b^3*c*z^2 + 5943367732714251*b^3*c*z + 203953285932773*b^3*c + 10285159274775*b^3*z^2 - 972989740664181*b^3*z - 116954983745111*b^3 - 96590218638*b^2*c^5*z + 6470244908116*b^2*c^5 + 11932565738700*b^2*c^4*z^2 - 819848866509835*b^2*c^4*z - 79780242529436*b^2*c^4 - 45130135929375*b^2*c^3*z^2 + 3508850555078815*b^2*c^3*z + 352943920855393*b^2*c^3 + 117265084315650*b^2*c^2*z^2 - 9549331963747260*b^2*c^2*z - 791729991064450*b^2*c^2 - 201434093554875*b^2*c*z^2 + 15573622415238965*b^2*c*z + 977919270505896*b^2*c + 145506062813700*b^2*z^2 - 10985369655172549*b^2*z - 618306199403284*b^2 + 48295109319*b*c^6*z - 3235122454058*b*c^6 - 1424783968800*b*c^5*z^2 + 111355265037491*b*c^5*z + 51213049853921*b*c^5 + 12288761730900*b*c^4*z^2 - 1080000249541491*b*c^4*z - 334689338965043*b*c^4 - 112474144502925*b*c^3*z^2 + 8933063000339330*b*c^3*z + 1185866021048519*b*c^3 + 467067254738025*b*c^2*z^2 - 35829645073395199*b*c^2*z - 2502773141086697*b*c^2 - 584072378209950*b*c*z^2 + 44560777905577172*b*c*z + 2171785596671584*b*c - 427479715139025*b*z^2 + 32775181689770614*b*z + 1688595672074596*b + 48295109319*c^4*z - 3235122454058*c^4 - 1424783968800*c^3*z^2 + 109229400915173*c^3*z + 190707750159152*c^3 + 17097407625600*c^2*z^2 - 1331663618743404*c^2*z - 939970488853521*c^2 - 88024934572425*c*z^2 + 6824557940036574*c*z + 1053347095272940*c + 243860681159925*z^2 - 18740532674805455*z - 211835870809278)/24254248244664) * h2 + (-(-80357919*c*z + 5382899258*c + 2370688800*z^2 - 186488671676*z - 4469572451)/40356486264) * h3

private lemma rejectI_22_25 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (c, b, b) = 0) (h2 : locus b (c, c, b) = 0)
    (h3 : edge b b c (c, b, b) (c, c, b) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-z*(2*b^5*c^2 - 2*b^5 - 4*b^4*c^3 - 12*b^4*c^2 + 20*b^4*c + 4*b^4 - b^3*c^4 + 38*b^3*c^3 - 45*b^3*c^2 - 48*b^3*c + 8*b^3 + b^2*c^5 + 6*b^2*c^4 - 79*b^2*c^3 + 187*b^2*c^2 - 51*b^2*c - 6*b*c^5 - 19*b*c^4 + 65*b*c^3 - 54*b*c^2 + 47*b*c - 8*b + c^6 + 7*c^5 - 18*c^4 + 7*c^3 - 8*c^2)) * h1 + (-z*(2*b^2*c^5 - 19*b^2*c^4 + 50*b^2*c^3 - 55*b^2*c^2 + 45*b^2*c - 16*b^2 - b*c^6 + 6*b*c^5 + 15*b*c^4 - 70*b*c^3 + 45*b*c^2 - 23*b*c + 8*b - 2*c^6 + 5*c^5 - c^4)) * h2 + (z*(b*c - b - 2*c^2 + 5*c - 1)) * h3

private lemma rejectI_22_26 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (c, b, b) = 0) (h2 : locus b (c, c, c) = 0)
    (h3 : edge b b c (c, b, b) (c, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-6*b^2*c*z + 6*b^2*z + 6*b*c^2*z - 6*b*c*z - 1) * h0 + (-c*z*(6*b^4*c^2*z - 12*b^4*c*z + 6*b^4*z - 6*b^3*c^3*z - 6*b^3*c^2*z + 30*b^3*c*z - 18*b^3*z - 6*b^2*c^4*z + 54*b^2*c^3*z - 108*b^2*c^2*z + 78*b^2*c*z + b^2*c - 18*b^2*z - b^2 + 6*b*c^4*z - 24*b*c^3*z + 12*b*c^2*z + 24*b*c*z - 3*b*c - 18*b*z + 3*b + 72*c^4*z - 426*c^3*z + 654*c^2*z - 66*c*z - 4*c - 18*z + 9)) * h1 + (-z*(6*b*c^6*z - 60*b*c^5*z + 162*b*c^4*z - 6*b*c^3*z - b*c^3 - 300*b*c^2*z + 5*b*c^2 - 18*b*c*z - 3*b*c - 6*b + 18*c^6*z - 138*c^5*z + 360*c^4*z - 360*c^3*z - c^3 + 102*c^2*z + 4*c^2 + 18*c*z - 3*c)) * h2

private lemma rejectI_23_24 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (c, b, c) = 0) (h2 : locus b (c, c, 1) = 0)
    (h3 : edge b b c (c, b, c) (c, c, 1) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-(2*c - 1)*(1023286*c - 292541)/81) * h0 + (-(160256*b^6*c + 160256*b^6 - 80128*b^5*c^2 - 1253888*b^5*c - 1334016*b^5 - 320512*b^4*c^3 + 626944*b^4*c^2 + 2823936*b^4*c + 3611136*b^4 + 320512*b^3*c^4 + 55257444*b^3*c^3*z + 2668032*b^3*c^3 - 98683380*b^3*c^2*z - 2974464*b^3*c^2 + 51324543*b^3*c*z + 258816*b^3*c - 3088128*b^3 - 80128*b^2*c^5 - 55257444*b^2*c^4*z - 2587904*b^2*c^4 + 98683380*b^2*c^3*z - 5299200*b^2*c^3 - 106581987*b^2*c^2*z + 5605632*b^2*c^2 + 106581987*b^2*c*z - 2961408*b^2*c + 7898607*b^2*z - 66048*b^2 - 40064*b*c^6 - 27628722*b*c^5*z + 1073600*b*c^5 + 284185827*b*c^4*z + 4873952*b*c^4 - 935476452*b*c^3*z - 3892624*b*c^3 + 1432891863*b*c^2*z + 3342392*b*c^2 - 1022459544*b*c*z - 18494052*b*c + 43425936*b*z + 1069824*b + 193280*c^6 - 55257444*c^5*z - 3113856*c^5 + 347341878*c^4*z + 1978432*c^4 - 923644944*c^3*z + 5781536*c^3 + 1314478368*c^2*z + 1568912*c^2 - 971102196*c*z + 11383496*c + 288184338*z + 1709824)/2187) * h1 + ((-160256*b^5 + 773120*b^4 + 7898607*b^3*z - 184064*b^3 + 43425936*b^2*z - 674560*b^2 - 40064*b*c^6 - 27628722*b*c^5*z + 606912*b*c^5 + 339443271*b*c^4*z - 2282272*b*c^4 - 1310447052*b*c^3*z + 410480*b*c^3 + 2253920526*b*c^2*z + 5435448*b*c^2 - 1835655210*b*c*z - 21612644*b*c + 288184338*b*z + 2082304*b + 193280*c^6 - 55257444*c^5*z - 2727296*c^5 + 236826990*c^4*z + 10814016*c^4 - 394733520*c^3*z - 13313504*c^3 + 288184338*c^2*z + 18440848*c^2 + 25370056*c - 7670116)/2187) * h2 + (256*(313*b - 884)/2187) * h3

private lemma rejectI_25_26 (b c z : ℝ)
    (h0 : invCondition b b c z = 0)
    (h1 : locus b (c, c, b) = 0) (h2 : locus b (c, c, c) = 0)
    (h3 : edge b b c (c, c, b) (c, c, c) = 0) : False := by
  simp only [invCondition, locus, edge, sep, quad, delta, u, v] at h0 h1 h2 h3
  apply one_ne_zero (α := ℝ)
  linear_combination (-1) * h0 + (-b*z*(b^3 + b^2*c - 4*b^2 - b*c^2 + 4*b + 4*c^2 - 17*c + 4)) * h1 + (z*(b^4 - 4*b^3 + 4*b^2 + 5*b*c^2 - 21*b*c + 4*b - c^3 + 4*c^2)) * h2

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

private lemma small_anchors (S : Finset ℝ²) (hsize : (distanceSet S).card*2 < S.card-1) (o : ℝ²) (ho : o ∈ S) :
    ∃ (r : ℝ) (a b : ℝ²), 0 < r ∧ a ∈ S ∧ b ∈ S ∧
      a ≠ o ∧ b ≠ o ∧ a ≠ b ∧
      len (coords o r a) = 1 ∧ len (coords o r b) = 1 ∧
      squared (coords o r a) (coords o r b) ≠ 4 := by
  classical
  have maps (x : ℝ²) (hx : x ∈ S.erase o) : dist x o ∈ distanceSet S := by
    obtain ⟨hne,hx⟩ := Finset.mem_erase.mp hx
    exact Finset.mem_image.mpr ⟨(x,o),Finset.mem_offDiag.mpr ⟨hx,ho,hne⟩,rfl⟩
  have hlt : (distanceSet S).card * 2 < (S.erase o).card := by
    rw [Finset.card_erase_of_mem ho]; exact hsize
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
    small_anchors S (by omega) o ho
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
private lemma eight_lower (S : Finset ℝ²) (hs : S.card = 8) : 4 ≤ distinctDistances S := by
  apply lower_from_colors _ S hs
  intro t b c z shape inv
  rcases shape with eq | eq
  · subst t
    exact ⟨colorsE, fun i j => conflictE b c z i j inv⟩
  · subst t
    exact ⟨colorsI, fun i j => conflictI b c z i j inv⟩

private def pTwo (b : ℝ) (i : Fin 8) : ℝ × ℝ × ℝ :=
  (if i.val/4=0 then 1 else b,if i.val/2%2=0 then 1 else b,if i.val%2=0 then 1 else b)
private def cTwo (i : Fin 8) : Fin 2 := if i=6 then 1 else 0
private def edgeTwo (t b : ℝ) (p q : ℝ × ℝ × ℝ) :=
  (sep t p q-delta t)*(sep t p q-b*delta t)

private lemma unit_0_1 (b : ℝ) (hnz : b*(b-1)*delta 1≠0)
    (h0 : locus 1 (1,1,1)=0) (h1 : locus 1 (1,1,b)=0)
    (h2 : edgeTwo 1 b (1,1,1) (1,1,b)=0) : False := by
  apply pow_ne_zero 0 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((-1)/(2))*h0

private lemma unit_0_2 (b : ℝ) (hnz : b*(b-1)*delta 1≠0)
    (h0 : locus 1 (1,1,1)=0) (h1 : locus 1 (1,b,1)=0)
    (h2 : edgeTwo 1 b (1,1,1) (1,b,1)=0) : False := by
  apply pow_ne_zero 0 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((-1)/(2))*h0

private lemma unit_0_3 (b : ℝ) (hnz : b*(b-1)*delta 1≠0)
    (h0 : locus 1 (1,1,1)=0) (h1 : locus 1 (1,b,b)=0)
    (h2 : edgeTwo 1 b (1,1,1) (1,b,b)=0) : False := by
  apply pow_ne_zero 0 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((-1)/(2))*h0

private lemma unit_0_4 (b : ℝ) (hnz : b*(b-1)*delta 1≠0)
    (h0 : locus 1 (1,1,1)=0) (h1 : locus 1 (b,1,1)=0)
    (h2 : edgeTwo 1 b (1,1,1) (b,1,1)=0) : False := by
  apply pow_ne_zero 0 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((-1)/(2))*h0

private lemma unit_0_5 (b : ℝ) (hnz : b*(b-1)*delta 1≠0)
    (h0 : locus 1 (1,1,1)=0) (h1 : locus 1 (b,1,b)=0)
    (h2 : edgeTwo 1 b (1,1,1) (b,1,b)=0) : False := by
  apply pow_ne_zero 0 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((-1)/(2))*h0

private lemma unit_0_7 (b : ℝ) (hnz : b*(b-1)*delta 1≠0)
    (h0 : locus 1 (1,1,1)=0) (h1 : locus 1 (b,b,b)=0)
    (h2 : edgeTwo 1 b (1,1,1) (b,b,b)=0) : False := by
  apply pow_ne_zero 0 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((-1)/(2))*h0

private lemma unit_1_2 (b : ℝ) (hnz : b*(b-1)*delta 1≠0)
    (h0 : locus 1 (1,1,b)=0) (h1 : locus 1 (1,b,1)=0)
    (h2 : edgeTwo 1 b (1,1,b) (1,b,1)=0) : False := by
  apply pow_ne_zero 1 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination (-3*(b - 1)^3)*h1 + ((b - 1)/(3))*h2

private lemma unit_1_3 (b : ℝ) (hnz : b*(b-1)*delta 1≠0)
    (h0 : locus 1 (1,1,b)=0) (h1 : locus 1 (1,b,b)=0)
    (h2 : edgeTwo 1 b (1,1,b) (1,b,b)=0) : False := by
  apply pow_ne_zero 0 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((b - 3)/(2))*h0 + ((2 - b)/(2))*h1

private lemma unit_1_4 (b : ℝ) (hnz : b*(b-1)*delta 1≠0)
    (h0 : locus 1 (1,1,b)=0) (h1 : locus 1 (b,1,1)=0)
    (h2 : edgeTwo 1 b (1,1,b) (b,1,1)=0) : False := by
  apply pow_ne_zero 1 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination (-3*(b - 1)^3)*h1 + ((b - 1)/(3))*h2

private lemma unit_1_5 (b : ℝ) (hnz : b*(b-1)*delta 1≠0)
    (h0 : locus 1 (1,1,b)=0) (h1 : locus 1 (b,1,b)=0)
    (h2 : edgeTwo 1 b (1,1,b) (b,1,b)=0) : False := by
  apply pow_ne_zero 0 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((b - 3)/(2))*h0 + ((2 - b)/(2))*h1

private lemma unit_1_7 (b : ℝ) (hnz : b*(b-1)*delta 1≠0)
    (h0 : locus 1 (1,1,b)=0) (h1 : locus 1 (b,b,b)=0)
    (h2 : edgeTwo 1 b (1,1,b) (b,b,b)=0) : False := by
  apply pow_ne_zero 0 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((-9)/(8))*h0 + ((8 - 3*b)/(8))*h1

private lemma unit_2_3 (b : ℝ) (hnz : b*(b-1)*delta 1≠0)
    (h0 : locus 1 (1,b,1)=0) (h1 : locus 1 (1,b,b)=0)
    (h2 : edgeTwo 1 b (1,b,1) (1,b,b)=0) : False := by
  apply pow_ne_zero 0 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((b - 3)/(2))*h0 + ((2 - b)/(2))*h1

private lemma unit_2_4 (b : ℝ) (hnz : b*(b-1)*delta 1≠0)
    (h0 : locus 1 (1,b,1)=0) (h1 : locus 1 (b,1,1)=0)
    (h2 : edgeTwo 1 b (1,b,1) (b,1,1)=0) : False := by
  apply pow_ne_zero 1 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination (-3*(b - 1)^3)*h1 + ((b - 1)/(3))*h2

private lemma unit_2_5 (b : ℝ) (hnz : b*(b-1)*delta 1≠0)
    (h0 : locus 1 (1,b,1)=0) (h1 : locus 1 (b,1,b)=0)
    (h2 : edgeTwo 1 b (1,b,1) (b,1,b)=0) : False := by
  apply pow_ne_zero 0 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((b - 3)/(2))*h0 + ((2 - b)/(2))*h1

private lemma unit_2_7 (b : ℝ) (hnz : b*(b-1)*delta 1≠0)
    (h0 : locus 1 (1,b,1)=0) (h1 : locus 1 (b,b,b)=0)
    (h2 : edgeTwo 1 b (1,b,1) (b,b,b)=0) : False := by
  apply pow_ne_zero 0 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((-9)/(8))*h0 + ((8 - 3*b)/(8))*h1

private lemma unit_3_4 (b : ℝ) (hnz : b*(b-1)*delta 1≠0)
    (h0 : locus 1 (1,b,b)=0) (h1 : locus 1 (b,1,1)=0)
    (h2 : edgeTwo 1 b (1,b,b) (b,1,1)=0) : False := by
  apply pow_ne_zero 0 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((2 - b)/(2))*h0 + ((b - 3)/(2))*h1

private lemma unit_3_5 (b : ℝ) (hnz : b*(b-1)*delta 1≠0)
    (h0 : locus 1 (1,b,b)=0) (h1 : locus 1 (b,1,b)=0)
    (h2 : edgeTwo 1 b (1,b,b) (b,1,b)=0) : False := by
  apply pow_ne_zero 0 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((-7*b^3 + 33*b^2 - 40*b + 3)/(3))*h1 + ((7*b - 26)/(27))*h2

private lemma unit_3_7 (b : ℝ) (hnz : b*(b-1)*delta 1≠0)
    (h0 : locus 1 (1,b,b)=0) (h1 : locus 1 (b,b,b)=0)
    (h2 : edgeTwo 1 b (1,b,b) (b,b,b)=0) : False := by
  apply pow_ne_zero 0 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((-9)/(2))*h0 + ((11 - 3*b)/(2))*h1

private lemma unit_4_5 (b : ℝ) (hnz : b*(b-1)*delta 1≠0)
    (h0 : locus 1 (b,1,1)=0) (h1 : locus 1 (b,1,b)=0)
    (h2 : edgeTwo 1 b (b,1,1) (b,1,b)=0) : False := by
  apply pow_ne_zero 0 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((b - 3)/(2))*h0 + ((2 - b)/(2))*h1

private lemma unit_4_7 (b : ℝ) (hnz : b*(b-1)*delta 1≠0)
    (h0 : locus 1 (b,1,1)=0) (h1 : locus 1 (b,b,b)=0)
    (h2 : edgeTwo 1 b (b,1,1) (b,b,b)=0) : False := by
  apply pow_ne_zero 0 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((-9)/(8))*h0 + ((8 - 3*b)/(8))*h1

private lemma unit_5_7 (b : ℝ) (hnz : b*(b-1)*delta 1≠0)
    (h0 : locus 1 (b,1,b)=0) (h1 : locus 1 (b,b,b)=0)
    (h2 : edgeTwo 1 b (b,1,b) (b,b,b)=0) : False := by
  apply pow_ne_zero 0 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((-9)/(2))*h0 + ((11 - 3*b)/(2))*h1

private lemma unit_conflict (b : ℝ) (hnz : b*(b-1)*delta 1≠0) (i j : Fin 8)
    (hi : locus 1 (pTwo b i)=0) (hj : locus 1 (pTwo b j)=0)
    (he : edgeTwo 1 b (pTwo b i) (pTwo b j)=0) (hlt : i<j) (hcol : cTwo i=cTwo j) : False := by
  fin_cases i <;> fin_cases j
  · exact (by decide : ¬ ((0:Fin 8)<0)) hlt
  · exact unit_0_1 b hnz hi hj he
  · exact unit_0_2 b hnz hi hj he
  · exact unit_0_3 b hnz hi hj he
  · exact unit_0_4 b hnz hi hj he
  · exact unit_0_5 b hnz hi hj he
  · exact (by decide : cTwo 0≠cTwo 6) hcol
  · exact unit_0_7 b hnz hi hj he
  · exact (by decide : ¬ ((1:Fin 8)<0)) hlt
  · exact (by decide : ¬ ((1:Fin 8)<1)) hlt
  · exact unit_1_2 b hnz hi hj he
  · exact unit_1_3 b hnz hi hj he
  · exact unit_1_4 b hnz hi hj he
  · exact unit_1_5 b hnz hi hj he
  · exact (by decide : cTwo 1≠cTwo 6) hcol
  · exact unit_1_7 b hnz hi hj he
  · exact (by decide : ¬ ((2:Fin 8)<0)) hlt
  · exact (by decide : ¬ ((2:Fin 8)<1)) hlt
  · exact (by decide : ¬ ((2:Fin 8)<2)) hlt
  · exact unit_2_3 b hnz hi hj he
  · exact unit_2_4 b hnz hi hj he
  · exact unit_2_5 b hnz hi hj he
  · exact (by decide : cTwo 2≠cTwo 6) hcol
  · exact unit_2_7 b hnz hi hj he
  · exact (by decide : ¬ ((3:Fin 8)<0)) hlt
  · exact (by decide : ¬ ((3:Fin 8)<1)) hlt
  · exact (by decide : ¬ ((3:Fin 8)<2)) hlt
  · exact (by decide : ¬ ((3:Fin 8)<3)) hlt
  · exact unit_3_4 b hnz hi hj he
  · exact unit_3_5 b hnz hi hj he
  · exact (by decide : cTwo 3≠cTwo 6) hcol
  · exact unit_3_7 b hnz hi hj he
  · exact (by decide : ¬ ((4:Fin 8)<0)) hlt
  · exact (by decide : ¬ ((4:Fin 8)<1)) hlt
  · exact (by decide : ¬ ((4:Fin 8)<2)) hlt
  · exact (by decide : ¬ ((4:Fin 8)<3)) hlt
  · exact (by decide : ¬ ((4:Fin 8)<4)) hlt
  · exact unit_4_5 b hnz hi hj he
  · exact (by decide : cTwo 4≠cTwo 6) hcol
  · exact unit_4_7 b hnz hi hj he
  · exact (by decide : ¬ ((5:Fin 8)<0)) hlt
  · exact (by decide : ¬ ((5:Fin 8)<1)) hlt
  · exact (by decide : ¬ ((5:Fin 8)<2)) hlt
  · exact (by decide : ¬ ((5:Fin 8)<3)) hlt
  · exact (by decide : ¬ ((5:Fin 8)<4)) hlt
  · exact (by decide : ¬ ((5:Fin 8)<5)) hlt
  · exact (by decide : cTwo 5≠cTwo 6) hcol
  · exact unit_5_7 b hnz hi hj he
  · exact (by decide : ¬ ((6:Fin 8)<0)) hlt
  · exact (by decide : ¬ ((6:Fin 8)<1)) hlt
  · exact (by decide : ¬ ((6:Fin 8)<2)) hlt
  · exact (by decide : ¬ ((6:Fin 8)<3)) hlt
  · exact (by decide : ¬ ((6:Fin 8)<4)) hlt
  · exact (by decide : ¬ ((6:Fin 8)<5)) hlt
  · exact (by decide : ¬ ((6:Fin 8)<6)) hlt
  · exact (by decide : cTwo 6≠cTwo 7) hcol
  · exact (by decide : ¬ ((7:Fin 8)<0)) hlt
  · exact (by decide : ¬ ((7:Fin 8)<1)) hlt
  · exact (by decide : ¬ ((7:Fin 8)<2)) hlt
  · exact (by decide : ¬ ((7:Fin 8)<3)) hlt
  · exact (by decide : ¬ ((7:Fin 8)<4)) hlt
  · exact (by decide : ¬ ((7:Fin 8)<5)) hlt
  · exact (by decide : ¬ ((7:Fin 8)<6)) hlt
  · exact (by decide : ¬ ((7:Fin 8)<7)) hlt
private lemma other_0_1 (b : ℝ) (hnz : b*(b-1)*delta b≠0)
    (h0 : locus b (1,1,1)=0) (h1 : locus b (1,1,b)=0)
    (h2 : edgeTwo b b (1,1,1) (1,1,b)=0) : False := by
  apply pow_ne_zero 0 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((b - 3)/(2))*h0 + ((2 - b)/(2))*h1

private lemma other_0_2 (b : ℝ) (hnz : b*(b-1)*delta b≠0)
    (h0 : locus b (1,1,1)=0) (h1 : locus b (1,b,1)=0)
    (h2 : edgeTwo b b (1,1,1) (1,b,1)=0) : False := by
  apply pow_ne_zero 0 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((b - 3)/(2))*h0 + ((2 - b)/(2))*h1

private lemma other_0_3 (b : ℝ) (hnz : b*(b-1)*delta b≠0)
    (h0 : locus b (1,1,1)=0) (h1 : locus b (1,b,b)=0)
    (h2 : edgeTwo b b (1,1,1) (1,b,b)=0) : False := by
  apply pow_ne_zero 1 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((b*(b - 4)*(b - 1)^2*(b + 1)*(2*b^2 - 2*b - 3))/(9))*h0 + ((-b*(b - 4)*(b - 1))/(9))*h2

private lemma other_0_4 (b : ℝ) (hnz : b*(b-1)*delta b≠0)
    (h0 : locus b (1,1,1)=0) (h1 : locus b (b,1,1)=0)
    (h2 : edgeTwo b b (1,1,1) (b,1,1)=0) : False := by
  apply pow_ne_zero 1 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((b*(b - 4)*(b - 1)*(b + 1))/(3))*h0 + ((-b*(b - 4)*(b - 1))/(6))*h1

private lemma other_0_5 (b : ℝ) (hnz : b*(b-1)*delta b≠0)
    (h0 : locus b (1,1,1)=0) (h1 : locus b (b,1,b)=0)
    (h2 : edgeTwo b b (1,1,1) (b,1,b)=0) : False := by
  apply pow_ne_zero 0 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((b^2 - 3*b - 3)/(4))*h0 + ((4 - b)/(4))*h1

private lemma other_0_7 (b : ℝ) (hnz : b*(b-1)*delta b≠0)
    (h0 : locus b (1,1,1)=0) (h1 : locus b (b,b,b)=0)
    (h2 : edgeTwo b b (1,1,1) (b,b,b)=0) : False := by
  apply pow_ne_zero 1 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((-b*(b - 4)*(b - 1)^2)/(2))*h0 + ((b*(b - 4)*(b - 1))/(2))*h1

private lemma other_1_2 (b : ℝ) (hnz : b*(b-1)*delta b≠0)
    (h0 : locus b (1,1,b)=0) (h1 : locus b (1,b,1)=0)
    (h2 : edgeTwo b b (1,1,b) (1,b,1)=0) : False := by
  apply pow_ne_zero 0 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((-2*b^4 + 19*b^3 - 61*b^2 + 76*b - 29)/(3))*h1 + ((2 - b)/(3))*h2

private lemma other_1_3 (b : ℝ) (hnz : b*(b-1)*delta b≠0)
    (h0 : locus b (1,1,b)=0) (h1 : locus b (1,b,b)=0)
    (h2 : edgeTwo b b (1,1,b) (1,b,b)=0) : False := by
  apply pow_ne_zero 0 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((-3*b^2 + 8*b + 2)/(2))*h0 + ((3*b - 11)/(2))*h1

private lemma other_1_4 (b : ℝ) (hnz : b*(b-1)*delta b≠0)
    (h0 : locus b (1,1,b)=0) (h1 : locus b (b,1,1)=0)
    (h2 : edgeTwo b b (1,1,b) (b,1,1)=0) : False := by
  apply pow_ne_zero 0 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((-7*b^2 + 12*b + 3)/(3))*h0 + ((7*b - 26)/(6))*h1

private lemma other_1_5 (b : ℝ) (hnz : b*(b-1)*delta b≠0)
    (h0 : locus b (1,1,b)=0) (h1 : locus b (b,1,b)=0)
    (h2 : edgeTwo b b (1,1,b) (b,1,b)=0) : False := by
  apply pow_ne_zero 0 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((5*b^2 - 9*b - 13)/(6))*h0 + ((19 - 5*b)/(6))*h1

private lemma other_1_7 (b : ℝ) (hnz : b*(b-1)*delta b≠0)
    (h0 : locus b (1,1,b)=0) (h1 : locus b (b,b,b)=0)
    (h2 : edgeTwo b b (1,1,b) (b,b,b)=0) : False := by
  apply pow_ne_zero 0 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((-14*b^4 + 80*b^3 - 83*b^2 - 99*b + 29)/(3))*h0 + ((7*b - 26)/(3))*h2

private lemma other_2_3 (b : ℝ) (hnz : b*(b-1)*delta b≠0)
    (h0 : locus b (1,b,1)=0) (h1 : locus b (1,b,b)=0)
    (h2 : edgeTwo b b (1,b,1) (1,b,b)=0) : False := by
  apply pow_ne_zero 0 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((-3*b^2 + 8*b + 2)/(2))*h0 + ((3*b - 11)/(2))*h1

private lemma other_2_4 (b : ℝ) (hnz : b*(b-1)*delta b≠0)
    (h0 : locus b (1,b,1)=0) (h1 : locus b (b,1,1)=0)
    (h2 : edgeTwo b b (1,b,1) (b,1,1)=0) : False := by
  apply pow_ne_zero 0 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((-7*b^2 + 12*b + 3)/(3))*h0 + ((7*b - 26)/(6))*h1

private lemma other_2_5 (b : ℝ) (hnz : b*(b-1)*delta b≠0)
    (h0 : locus b (1,b,1)=0) (h1 : locus b (b,1,b)=0)
    (h2 : edgeTwo b b (1,b,1) (b,1,b)=0) : False := by
  apply pow_ne_zero 0 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((5*b^2 - 9*b - 13)/(6))*h0 + ((19 - 5*b)/(6))*h1

private lemma other_2_7 (b : ℝ) (hnz : b*(b-1)*delta b≠0)
    (h0 : locus b (1,b,1)=0) (h1 : locus b (b,b,b)=0)
    (h2 : edgeTwo b b (1,b,1) (b,b,b)=0) : False := by
  apply pow_ne_zero 0 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((-14*b^4 + 80*b^3 - 83*b^2 - 99*b + 29)/(3))*h0 + ((7*b - 26)/(3))*h2

private lemma other_3_4 (b : ℝ) (hnz : b*(b-1)*delta b≠0)
    (h0 : locus b (1,b,b)=0) (h1 : locus b (b,1,1)=0)
    (h2 : edgeTwo b b (1,b,b) (b,1,1)=0) : False := by
  apply pow_ne_zero 1 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((b - 4)*(b - 1))*h0 + ((-(b - 4)*(b - 1))/(2))*h1

private lemma other_3_5 (b : ℝ) (hnz : b*(b-1)*delta b≠0)
    (h0 : locus b (1,b,b)=0) (h1 : locus b (b,1,b)=0)
    (h2 : edgeTwo b b (1,b,b) (b,1,b)=0) : False := by
  apply pow_ne_zero 0 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((3*b^2 - 5*b - 9)/(4))*h0 + ((-3*b^2 + 8*b + 4)/(4))*h1

private lemma other_3_7 (b : ℝ) (hnz : b*(b-1)*delta b≠0)
    (h0 : locus b (1,b,b)=0) (h1 : locus b (b,b,b)=0)
    (h2 : edgeTwo b b (1,b,b) (b,b,b)=0) : False := by
  apply pow_ne_zero 1 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((-b*(b - 4)*(b - 3)*(b - 1))/(2))*h0 + ((b*(b - 4)*(b - 2)*(b - 1))/(2))*h1

private lemma other_4_5 (b : ℝ) (hnz : b*(b-1)*delta b≠0)
    (h0 : locus b (b,1,1)=0) (h1 : locus b (b,1,b)=0)
    (h2 : edgeTwo b b (b,1,1) (b,1,b)=0) : False := by
  apply pow_ne_zero 0 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((4*b^2 - 6*b - 11)/(6))*h0 + ((-4*b^2 + 6*b + 3)/(3))*h1

private lemma other_4_7 (b : ℝ) (hnz : b*(b-1)*delta b≠0)
    (h0 : locus b (b,1,1)=0) (h1 : locus b (b,b,b)=0)
    (h2 : edgeTwo b b (b,1,1) (b,b,b)=0) : False := by
  apply pow_ne_zero 1 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((-b*(b - 4)*(b - 1)*(2*b - 7))/(6))*h0 + ((b*(b - 4)*(b - 1)*(2*b - 3))/(3))*h1

private lemma other_5_7 (b : ℝ) (hnz : b*(b-1)*delta b≠0)
    (h0 : locus b (b,1,b)=0) (h1 : locus b (b,b,b)=0)
    (h2 : edgeTwo b b (b,1,b) (b,b,b)=0) : False := by
  apply pow_ne_zero 0 hnz
  simp only [edgeTwo,locus,sep,quad,u,v,delta] at h0 h1 h2 ⊢
  linear_combination ((-13*b^2 + 47*b + 6)/(6))*h0 + ((13*b^2 - 21*b - 35)/(6))*h1

private lemma other_conflict (b : ℝ) (hnz : b*(b-1)*delta b≠0) (i j : Fin 8)
    (hi : locus b (pTwo b i)=0) (hj : locus b (pTwo b j)=0)
    (he : edgeTwo b b (pTwo b i) (pTwo b j)=0) (hlt : i<j) (hcol : cTwo i=cTwo j) : False := by
  fin_cases i <;> fin_cases j
  · exact (by decide : ¬ ((0:Fin 8)<0)) hlt
  · exact other_0_1 b hnz hi hj he
  · exact other_0_2 b hnz hi hj he
  · exact other_0_3 b hnz hi hj he
  · exact other_0_4 b hnz hi hj he
  · exact other_0_5 b hnz hi hj he
  · exact (by decide : cTwo 0≠cTwo 6) hcol
  · exact other_0_7 b hnz hi hj he
  · exact (by decide : ¬ ((1:Fin 8)<0)) hlt
  · exact (by decide : ¬ ((1:Fin 8)<1)) hlt
  · exact other_1_2 b hnz hi hj he
  · exact other_1_3 b hnz hi hj he
  · exact other_1_4 b hnz hi hj he
  · exact other_1_5 b hnz hi hj he
  · exact (by decide : cTwo 1≠cTwo 6) hcol
  · exact other_1_7 b hnz hi hj he
  · exact (by decide : ¬ ((2:Fin 8)<0)) hlt
  · exact (by decide : ¬ ((2:Fin 8)<1)) hlt
  · exact (by decide : ¬ ((2:Fin 8)<2)) hlt
  · exact other_2_3 b hnz hi hj he
  · exact other_2_4 b hnz hi hj he
  · exact other_2_5 b hnz hi hj he
  · exact (by decide : cTwo 2≠cTwo 6) hcol
  · exact other_2_7 b hnz hi hj he
  · exact (by decide : ¬ ((3:Fin 8)<0)) hlt
  · exact (by decide : ¬ ((3:Fin 8)<1)) hlt
  · exact (by decide : ¬ ((3:Fin 8)<2)) hlt
  · exact (by decide : ¬ ((3:Fin 8)<3)) hlt
  · exact other_3_4 b hnz hi hj he
  · exact other_3_5 b hnz hi hj he
  · exact (by decide : cTwo 3≠cTwo 6) hcol
  · exact other_3_7 b hnz hi hj he
  · exact (by decide : ¬ ((4:Fin 8)<0)) hlt
  · exact (by decide : ¬ ((4:Fin 8)<1)) hlt
  · exact (by decide : ¬ ((4:Fin 8)<2)) hlt
  · exact (by decide : ¬ ((4:Fin 8)<3)) hlt
  · exact (by decide : ¬ ((4:Fin 8)<4)) hlt
  · exact other_4_5 b hnz hi hj he
  · exact (by decide : cTwo 4≠cTwo 6) hcol
  · exact other_4_7 b hnz hi hj he
  · exact (by decide : ¬ ((5:Fin 8)<0)) hlt
  · exact (by decide : ¬ ((5:Fin 8)<1)) hlt
  · exact (by decide : ¬ ((5:Fin 8)<2)) hlt
  · exact (by decide : ¬ ((5:Fin 8)<3)) hlt
  · exact (by decide : ¬ ((5:Fin 8)<4)) hlt
  · exact (by decide : ¬ ((5:Fin 8)<5)) hlt
  · exact (by decide : cTwo 5≠cTwo 6) hcol
  · exact other_5_7 b hnz hi hj he
  · exact (by decide : ¬ ((6:Fin 8)<0)) hlt
  · exact (by decide : ¬ ((6:Fin 8)<1)) hlt
  · exact (by decide : ¬ ((6:Fin 8)<2)) hlt
  · exact (by decide : ¬ ((6:Fin 8)<3)) hlt
  · exact (by decide : ¬ ((6:Fin 8)<4)) hlt
  · exact (by decide : ¬ ((6:Fin 8)<5)) hlt
  · exact (by decide : ¬ ((6:Fin 8)<6)) hlt
  · exact (by decide : cTwo 6≠cTwo 7) hcol
  · exact (by decide : ¬ ((7:Fin 8)<0)) hlt
  · exact (by decide : ¬ ((7:Fin 8)<1)) hlt
  · exact (by decide : ¬ ((7:Fin 8)<2)) hlt
  · exact (by decide : ¬ ((7:Fin 8)<3)) hlt
  · exact (by decide : ¬ ((7:Fin 8)<4)) hlt
  · exact (by decide : ¬ ((7:Fin 8)<5)) hlt
  · exact (by decide : ¬ ((7:Fin 8)<6)) hlt
  · exact (by decide : ¬ ((7:Fin 8)<7)) hlt

private def inTwo (b x : ℝ) : Prop := x=1 ∨ x=b

private lemma pTwo_exists (b x y z : ℝ) (hx : inTwo b x) (hy : inTwo b y) (hz : inTwo b z) :
    ∃ i : Fin 8, pTwo b i=(x,y,z) := by
  rcases hx with rfl|rfl <;> rcases hy with rfl|rfl <;> rcases hz with rfl|rfl
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩
  · exact ⟨3,rfl⟩
  · exact ⟨4,rfl⟩
  · exact ⟨5,rfl⟩
  · exact ⟨6,rfl⟩
  · exact ⟨7,rfl⟩
private lemma two_color_bound (R : Finset ℝ²) (X : ℝ² → ℝ × ℝ) (e f : ℝ × ℝ)
    (he : len e = 1) (hf : len f = 1) (b : ℝ) (hd : delta (squared e f) ≠ 0)
    (col : Fin 8 → Fin 2)
    (conflict : ∀ i j : Fin 8, locus (squared e f) (pTwo b i) = 0 →
      locus (squared e f) (pTwo b j) = 0 →
      edgeTwo (squared e f) b (pTwo b i) (pTwo b j) = 0 →
      i < j → col i = col j → False)
    (mem : ∀ x ∈ R, inTwo b (len (X x)) ∧
      inTwo b (squared (X x) e) ∧ inTwo b (squared (X x) f))
    (pairs : ∀ x ∈ R, ∀ y ∈ R, x ≠ y →
      squared (X x) (X y) ≠ 0 ∧ inTwo b (squared (X x) (X y))) : R.card ≤ 2 := by
  classical
  have codes (x : R) : ∃ i : Fin 8, pTwo b i = geometric e f (X x) := by
    obtain ⟨h1,h2,h3⟩ := mem x x.property
    exact pTwo_exists b _ _ _ h1 h2 h3
  choose idx eqn using codes
  have loc (x : R) : locus (squared e f) (pTwo b (idx x)) = 0 := by
    rw [eqn]; exact geom_locus _ _ _ he hf
  have no_lt (x y : R) (ne : x ≠ y) (lt : idx x < idx y) (co : col (idx x) = col (idx y)) : False := by
    apply conflict _ _ (loc x) (loc y) _ lt co
    obtain ⟨_,ds⟩ := pairs x x.property y y.property (fun h => ne (Subtype.ext h))
    rw [eqn,eqn]
    unfold edgeTwo
    rw [geom_sep _ _ _ _ he hf]
    rcases ds with d | d <;> rw [d] <;> ring
  have inj : Function.Injective (fun x : R => col (idx x)) := by
    intro x y hcol
    by_contra hne
    rcases lt_trichotomy (idx x) (idx y) with h | h | h
    · exact no_lt x y hne h hcol
    · have hp := (eqn x).symm.trans ((congrArg (pTwo b) h).trans (eqn y))
      have hs := geom_sep e f (X x) (X y) he hf
      rw [hp] at hs
      simp [sep,quad] at hs
      exact hs.elim hd (pairs x x.property y y.property (fun h => hne (Subtype.ext h))).1
    · exact no_lt y x (Ne.symm hne) h hcol.symm
  simpa using Fintype.card_le_of_injective _ inj

private lemma pad_two (D : Finset ℝ) (hcard : D.card≤2) (one : 1∈D) (zero : 0∉D) :
    ∃ b : ℝ, b≠0 ∧ b≠1 ∧ ∀ x∈D, inTwo b x := by
  classical
  by_cases h : ∃ b ∈ D, b≠1
  · obtain ⟨b,hb,hb1⟩ := h
    have hc : (D.erase 1).card≤1 := by rw [Finset.card_erase_of_mem one]; omega
    refine ⟨b,fun h => zero (h ▸ hb),hb1,?_⟩
    intro x hx
    by_cases hx1 : x=1
    · exact Or.inl hx1
    · exact Or.inr (Finset.card_le_one.mp hc _ (Finset.mem_erase.mpr ⟨hx1,hx⟩) _ (Finset.mem_erase.mpr ⟨hb1,hb⟩))
  · exact ⟨2,by norm_num,by norm_num,fun x hx => Or.inl (by by_contra hn; exact h ⟨x,hx,hn⟩)⟩

private lemma six_lower (S : Finset ℝ²) (hS : S.card=6) : 3≤distinctDistances S := by
  classical
  by_contra! h
  have hD : (distanceSet S).card≤2 := by change distinctDistances S≤2; omega
  obtain ⟨o,ho⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  obtain ⟨r,a,f,hr,ha,hf,hao,hfo,haf,unitA,unitF,notFour⟩ :=
    small_anchors S (by omega) o ho
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
  obtain ⟨B,hB0,hB1,pal⟩ := pad_two D (Finset.card_image_le.trans hD) one zero
  have hshape := pal t (inD a ha f hf haf)
  have hnz : B*(B-1)*delta t≠0 := mul_ne_zero (mul_ne_zero hB0 (sub_ne_zero.mpr hB1)) hd
  have hcol : ∀ i j : Fin 8, locus t (pTwo B i)=0 → locus t (pTwo B j)=0 →
      edgeTwo t B (pTwo B i) (pTwo B j)=0 → i<j → cTwo i=cTwo j → False := by
    rcases hshape with h|h
    · rw [h] at hnz ⊢
      exact unit_conflict B hnz
    · rw [h] at hnz ⊢
      exact other_conflict B hnz
  let R := ((S.erase o).erase a).erase f
  have rem (x : ℝ²) (hx : x ∈ R) : x ≠ f ∧ x ≠ a ∧ x ≠ o ∧ x ∈ S := by
    simpa only [R,Finset.mem_erase] using hx
  have amem : a ∈ S.erase o := Finset.mem_erase.mpr ⟨hao,ha⟩
  have fmem : f ∈ (S.erase o).erase a :=
    Finset.mem_erase.mpr ⟨haf.symm, Finset.mem_erase.mpr ⟨hfo,hf⟩⟩
  have size : R.card = 3 := by
    simp only [R,Finset.card_erase_of_mem fmem,Finset.card_erase_of_mem amem,
      Finset.card_erase_of_mem ho,hS]
  have bound := two_color_bound R X (X a) (X f) unitA unitF B hd cTwo hcol (by
    intro x hx
    obtain ⟨xf,xa,xo,xS⟩ := rem x hx
    refine ⟨?_,pal _ (inD x xS a ha xa),pal _ (inD x xS f hf xf)⟩
    rw [← origin]
    exact pal _ (inD x xS o ho xo)) (by
    intro x hx y hy ne
    exact ⟨(squared_pos o x y hr ne).ne',pal _ (inD x (rem x hx).2.2.2 y (rem y hy).2.2.2 ne)⟩)
  omega
private lemma four_lower (S : Finset ℝ²) (hS : S.card=4) : 2≤distinctDistances S := by
  classical
  by_contra! h
  have hD : (distanceSet S).card≤1 := by change distinctDistances S≤1; omega
  obtain ⟨o,ho⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  obtain ⟨r,a,f,hr,ha,hf,hao,hfo,haf,unitA,unitF,notFour⟩ :=
    small_anchors S (by omega) o ho
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
  let R := ((S.erase o).erase a).erase f
  have rem (x : ℝ²) (hx : x ∈ R) : x ≠ f ∧ x ≠ a ∧ x ≠ o ∧ x ∈ S := by
    simpa only [R,Finset.mem_erase] using hx
  have amem : a ∈ S.erase o := Finset.mem_erase.mpr ⟨hao,ha⟩
  have fmem : f ∈ (S.erase o).erase a :=
    Finset.mem_erase.mpr ⟨haf.symm, Finset.mem_erase.mpr ⟨hfo,hf⟩⟩
  have size : R.card = 1 := by
    simp only [R,Finset.card_erase_of_mem fmem,Finset.card_erase_of_mem amem,
      Finset.card_erase_of_mem ho,hS]
  have hle : D.card≤1 := Finset.card_image_le.trans hD
  have all (z : ℝ) (hz : z∈D) : z=1 := Finset.card_le_one.mp hle _ hz _ one
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0<R.card by omega)
  obtain ⟨xf,xa,xo,xS⟩ := rem x hx
  have hxf := all _ (inD x xS f hf xf)
  have hxa := all _ (inD x xS a ha xa)
  have hxo := all _ (inD x xS o ho xo)
  rw [origin] at hxo
  have hbase := all _ (inD a ha f hf haf)
  have hh := geom_locus (X a) (X f) (X x) unitA unitF
  simp [geometric,hbase,hxf,hxa,hxo,locus,quad,u,v,delta] at hh
  norm_num at hh

private lemma all_small (A : Finset ℝ²) (hsmall : distinctDistances A ≤ 3) :
    A.card/2 ≤ distinctDistances A := by
  classical
  have restrict (n k : ℕ) (hn : n≤A.card) (h : ∀ B : Finset ℝ², B.card=n → k≤distinctDistances B) :
      k≤distinctDistances A := by
    obtain ⟨B,hBA,hB⟩ := Finset.exists_subset_card_eq hn
    exact (h B hB).trans (Finset.card_le_card (OMA.R_Erdos1082_erdos_1082_parts_i_R1.distanceSet_mono hBA))
  by_cases h8 : 8≤A.card
  · have := restrict 8 4 h8 eight_lower
    omega
  by_cases h6 : 6≤A.card
  · have := restrict 6 3 h6 six_lower
    omega
  by_cases h4 : 4≤A.card
  · have := restrict 4 2 h4 four_lower
    omega
  by_cases h2 : 1<A.card
  · obtain ⟨x,y,hx,hy,hxy⟩ := Finset.one_lt_card_iff.mp h2
    have hd : 0<distinctDistances A := Finset.card_pos.mpr ⟨dist x y,
      OMA.R_Erdos1082_erdos_1082_parts_i_R1.dist_mem hx hy hxy⟩
    omega
  · omega

end OMA.EightDistances

theorem OMA.solution : OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H4_R1.H1 :=
  fun A _ h => OMA.EightDistances.all_small A h
