import OMAStatements.S_oeis_a168452
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

-- Problem: A168452, the self-convolution of consecutive Catalan products.
-- Source: https://oeis.org/A168452
-- Statement credit: @JeremyDevs; recurrence conjectured by R. J. Mathar, Nov 22 2024.
-- The proof derives a second-order Euler differential equation from the Catalan ratio,
-- differentiates it three times, and verifies an explicit polynomial certificate
-- for the required operator on the squared generating series.
-- Symbolic computation suggested the certificate; all identities are checked in Lean.
-- The alternative 2013 Maple recurrence in OEIS is not assumed.

-- Component: A168452Defs

namespace A168452Proof
open PowerSeries OMA.S_oeis_a168452

noncomputable def F : PowerSeries ℚ := mk (fun n => (c n : ℚ))

noncomputable def theta (f : PowerSeries ℚ) : PowerSeries ℚ :=
  X * derivative ℚ f

noncomputable def thetaN : ℕ → PowerSeries ℚ → PowerSeries ℚ
  | 0, f => f
  | k + 1, f => theta (thetaN k f)

/-- The Euler differential operator whose coefficients are the conjectured recurrence. -/
noncomputable def targetOp (f : PowerSeries ℚ) : PowerSeries ℚ :=
  (3 * thetaN 5 f + 33 * thetaN 4 f + 135 * thetaN 3 f +
    255 * thetaN 2 f + 222 * thetaN 1 f + 72 * f) +
  X * (-128 * thetaN 5 f - 1424 * thetaN 4 f - 6004 * thetaN 3 f -
    11980 * thetaN 2 f - 11304 * thetaN 1 f - 4032 * f) +
  X ^ 2 * (1536 * thetaN 5 f + 17664 * thetaN 4 f + 78528 * thetaN 3 f +
    167424 * thetaN 2 f + 168192 * thetaN 1 f + 61728 * f) +
  X ^ 3 * (-12288 * thetaN 4 f - 113664 * thetaN 3 f -
    359424 * thetaN 2 f - 463872 * thetaN 1 f - 207360 * f) +
  X ^ 4 * (-65536 * thetaN 5 f - 655360 * thetaN 4 f - 2539520 * thetaN 3 f -
    4751360 * thetaN 2 f - 4276224 * thetaN 1 f - 1474560 * f)

end A168452Proof

-- Component: A168452Base

namespace A168452Proof
open PowerSeries OMA.S_oeis_a168452

theorem catalan_step (n : ℕ) :
    (n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
  apply Nat.eq_of_mul_eq_mul_left (show 0 < n + 1 by omega)
  calc
    (n + 1) * ((n + 2) * catalan (n + 1)) =
        (n + 1) * (n + 1).centralBinom := by
      rw [← succ_mul_catalan_eq_centralBinom (n + 1)]
    _ = 2 * (2 * n + 1) * n.centralBinom := Nat.succ_mul_centralBinom_succ n
    _ = (n + 1) * (2 * (2 * n + 1) * catalan n) := by
      rw [← succ_mul_catalan_eq_centralBinom n]
      ring

theorem c_step (n : ℕ) :
    ((n : ℚ) + 2) * (n + 3) * (c (n + 1) : ℚ) =
      4 * (2 * n + 1) * (2 * n + 3) * (c n : ℚ) := by
  have h1 : ((n : ℚ) + 2) * (catalan (n + 1) : ℚ) =
      2 * (2 * n + 1) * (catalan n : ℚ) := by exact_mod_cast catalan_step n
  have h2 : ((n : ℚ) + 3) * (catalan (n + 2) : ℚ) =
      2 * (2 * n + 3) * (catalan (n + 1) : ℚ) := by
    have h := catalan_step (n + 1)
    exact_mod_cast (by simpa [Nat.add_assoc, Nat.mul_add] using h)
  simp only [c, Int.cast_mul, Int.cast_natCast, Nat.add_assoc]
  calc
    _ = (((n : ℚ) + 2) * catalan (n + 1)) * ((n + 3) * catalan (n + 2)) := by ring
    _ = (2 * (2 * n + 1) * catalan n) * (2 * (2 * n + 3) * catalan (n + 1)) := by rw [h1, h2]
    _ = _ := by ring

private theorem coeff_theta_base (f : PowerSeries ℚ) (n : ℕ) :
    coeff n (theta f) = (n : ℚ) * coeff n f := by
  cases n with
  | zero => simp [theta, coeff_zero_eq_constantCoeff_apply]
  | succ n =>
    rw [theta, ← pow_one (X : PowerSeries ℚ), coeff_X_pow_mul, coeff_derivative]
    push_cast
    ring

theorem base_theta :
    thetaN 2 F + 3 * thetaN 1 F + 2 * F -
      4 * X * (4 * thetaN 2 F + 8 * thetaN 1 F + 3 * F) = 2 := by
  rw [show (4 : PowerSeries ℚ) * X *
      (4 * thetaN 2 F + 8 * thetaN 1 F + 3 * F) =
      X ^ 1 * (4 * (4 * thetaN 2 F + 8 * thetaN 1 F + 3 * F)) by ring]
  ext n
  cases n with
  | zero =>
    simp [thetaN, theta, F, c, catalan_zero, catalan_one,
      coeff_zero_eq_constantCoeff_apply]
  | succ n =>
    simp only [show (2 : PowerSeries ℚ) = C (2 : ℚ) from (map_ofNat C 2).symm,
      show (3 : PowerSeries ℚ) = C (3 : ℚ) from (map_ofNat C 3).symm,
      show (4 : PowerSeries ℚ) = C (4 : ℚ) from (map_ofNat C 4).symm,
      show (8 : PowerSeries ℚ) = C (8 : ℚ) from (map_ofNat C 8).symm,
      map_sub, map_add, coeff_C_mul, thetaN, coeff_theta_base,
      coeff_X_pow_mul, F, coeff_mk, coeff_C, Nat.add_eq_zero_iff]
    have h := c_step n
    push_cast
    simp only [and_false, if_false]
    nlinarith [h]

end A168452Proof

-- Component: A168452Theta

namespace A168452Proof
open PowerSeries

@[simp] theorem theta_zero : theta 0 = 0 := by simp [theta]
@[simp] theorem theta_one : theta 1 = 0 := by simp [theta]
@[simp] theorem theta_C (q : ℚ) : theta (C q) = 0 := by simp [theta]
@[simp] theorem theta_X : theta X = X := by simp [theta]
@[simp] theorem theta_natCast (n : ℕ) : theta (n : PowerSeries ℚ) = 0 := by
  simp [theta, Derivation.map_natCast]
@[simp] theorem theta_ofNat (n : ℕ) [n.AtLeastTwo] : theta (ofNat(n) : PowerSeries ℚ) = 0 := by
  simpa only [map_ofNat] using theta_C (OfNat.ofNat n : ℚ)
@[simp] theorem theta_add (f g : PowerSeries ℚ) : theta (f+g) = theta f+theta g := by
  simp [theta, mul_add]
@[simp] theorem theta_sub (f g : PowerSeries ℚ) : theta (f-g) = theta f-theta g := by
  simp [theta, mul_sub]
@[simp] theorem theta_neg (f : PowerSeries ℚ) : theta (-f) = -theta f := by
  simp [theta]
@[simp] theorem theta_mul (f g : PowerSeries ℚ) :
    theta (f*g) = theta f*g + f*theta g := by
  simp only [theta, Derivation.leibniz, smul_eq_mul]
  ring
@[simp] theorem theta_pow (f : PowerSeries ℚ) (n : ℕ) :
    theta (f^n) = n*f^(n-1)*theta f := by
  simp only [theta, PowerSeries.derivative_pow]
  ring

theorem theta_jet (n : ℕ) (f : PowerSeries ℚ) : theta (thetaN n f) = thetaN (n+1) f := rfl

theorem square_jet1 (f : PowerSeries ℚ) : thetaN 1 (f^2) = 2*f*thetaN 1 f := by
  simp [thetaN, theta_pow]

theorem square_jet2 (f : PowerSeries ℚ) :
    thetaN 2 (f^2) = 2*f*thetaN 2 f+2*(thetaN 1 f)^2 := by
  change theta (thetaN 1 (f^2)) = _
  rw [square_jet1]
  simp only [theta_mul, theta_ofNat, theta_jet, zero_mul, zero_add]
  change 2*thetaN 1 f*thetaN 1 f+2*f*thetaN 2 f = _
  ring

theorem square_jet3 (f : PowerSeries ℚ) :
    thetaN 3 (f^2) = 2*f*thetaN 3 f+6*thetaN 1 f*thetaN 2 f := by
  change theta (thetaN 2 (f^2)) = _
  rw [square_jet2]
  simp only [theta_add, theta_mul, theta_ofNat, theta_jet, theta_pow,
    zero_mul, zero_add]
  change (2*thetaN 1 f*thetaN 2 f+2*f*thetaN 3 f)+
    2*(2*(thetaN 1 f)^(2-1)*thetaN 2 f) = _
  ring

theorem square_jet4 (f : PowerSeries ℚ) :
    thetaN 4 (f^2) = 2*f*thetaN 4 f+8*thetaN 1 f*thetaN 3 f+6*(thetaN 2 f)^2 := by
  change theta (thetaN 3 (f^2)) = _
  rw [square_jet3]
  simp only [theta_add, theta_mul, theta_ofNat, theta_jet, zero_mul, zero_add]
  change (2*thetaN 1 f*thetaN 3 f+2*f*thetaN 4 f)+
    (6*thetaN 2 f*thetaN 2 f+6*thetaN 1 f*thetaN 3 f) = _
  ring

theorem square_jet5 (f : PowerSeries ℚ) :
    thetaN 5 (f^2) = 2*f*thetaN 5 f+10*thetaN 1 f*thetaN 4 f+20*thetaN 2 f*thetaN 3 f := by
  change theta (thetaN 4 (f^2)) = _
  rw [square_jet4]
  simp only [theta_add, theta_mul, theta_ofNat, theta_jet, theta_pow, zero_mul, zero_add]
  change ((2*thetaN 1 f*thetaN 4 f+2*f*thetaN 5 f)+
    (8*thetaN 2 f*thetaN 3 f+8*thetaN 1 f*thetaN 4 f))+
    6*(2*(thetaN 2 f)^(2-1)*thetaN 3 f) = _
  ring

end A168452Proof

-- Component: A168452Ring

namespace A168452Proof

/-- The target operator evaluated on six abstract Euler jets. -/
def jetOp {R : Type*} [CommRing R] (x g0 g1 g2 g3 g4 g5 : R) : R :=
  (3*g5 + 33*g4 + 135*g3 + 255*g2 + 222*g1 + 72*g0) +
  x * (-128*g5 -1424*g4 -6004*g3 -11980*g2 -11304*g1 -4032*g0) +
  x^2 * (1536*g5 +17664*g4 +78528*g3 +167424*g2 +168192*g1 +61728*g0) +
  x^3 * (-12288*g4 -113664*g3 -359424*g2 -463872*g1 -207360*g0) +
  x^4 * (-65536*g5 -655360*g4 -2539520*g3 -4751360*g2 -4276224*g1 -1474560*g0)

/- A polynomial ideal certificate for the square of a solution of the second-order equation. -/
set_option maxHeartbeats 1200000 in
theorem jet_certificate {R : Type*} [CommRing R] (x f0 f1 f2 f3 f4 f5 : R)
    (h0 : (1-16*x)*f2 + (3-32*x)*f1 + (2-12*x)*f0 = 2)
    (h1 : (1-16*x)*f3 + (3-48*x)*f2 + (2-44*x)*f1 -12*x*f0 = 0)
    (h2 : (1-16*x)*f4 + (3-64*x)*f3 + (2-92*x)*f2 -56*x*f1 -12*x*f0 = 0)
    (h3 : (1-16*x)*f5 + (3-80*x)*f4 + (2-156*x)*f3 -148*x*f2 -68*x*f1 -12*x*f0 = 0) :
    (1-16*x) * (jetOp x (f0^2) (2*f0*f1) (2*f0*f2+2*f1^2)
      (2*f0*f3+6*f1*f2) (2*f0*f4+8*f1*f3+6*f2^2)
      (2*f0*f5+10*f1*f4+20*f2*f3) - (72-1152*x)) = 0 := by
  unfold jetOp
  linear_combination
    (-18*(16*x-1)^2*(12*f0*x-2*f0+32*f1*x-3*f1+16*f2*x-f2-2))*h0 +
    (-2*(16*x-1)*(36864*f0*x^3+5120*f0*x^2-1248*f0*x+57*f0+
      81920*f1*x^3+6912*f1*x^2-2144*f1*x+87*f1+
      40960*f2*x^3+2560*f2*x^2-800*f2*x+30*f2))*h1 +
    (-2*(16*x-1)^2*(1280*f0*x^2+176*f0*x-24*f0+
      1280*f1*x^2+160*f1*x-15*f1))*h2 +
    (-2*f0*(16*x-1)^3*(16*x+3))*h3

end A168452Proof

-- Component: A168452Certificate

namespace A168452Proof
open PowerSeries

theorem base_jet0 : (1-16*X)*thetaN 2 F + (3-32*X)*thetaN 1 F + (2-12*X)*F = 2 := by
  linear_combination base_theta

theorem base_jet1 : (1-16*X)*thetaN 3 F + (3-48*X)*thetaN 2 F +
    (2-44*X)*thetaN 1 F -12*X*F = 0 := by
  have h := congrArg theta base_jet0
  simp only [theta_add, theta_sub, theta_mul, theta_ofNat, theta_one,
    theta_zero, theta_X, theta_jet, Nat.reduceAdd,
    zero_mul, mul_zero, zero_add, add_zero, one_mul,
    show theta F = thetaN 1 F from rfl] at h
  linear_combination h

theorem base_jet2 : (1-16*X)*thetaN 4 F + (3-64*X)*thetaN 3 F +
    (2-92*X)*thetaN 2 F -56*X*thetaN 1 F -12*X*F = 0 := by
  have h := congrArg theta base_jet1
  simp only [theta_add, theta_sub, theta_mul, theta_ofNat, theta_one,
    theta_zero, theta_X, theta_jet, Nat.reduceAdd,
    zero_mul, mul_zero, zero_add, add_zero, one_mul,
    show theta F = thetaN 1 F from rfl] at h
  linear_combination h

theorem base_jet3 : (1-16*X)*thetaN 5 F + (3-80*X)*thetaN 4 F +
    (2-156*X)*thetaN 3 F -148*X*thetaN 2 F -68*X*thetaN 1 F -12*X*F = 0 := by
  have h := congrArg theta base_jet2
  simp only [theta_add, theta_sub, theta_mul, theta_ofNat, theta_one,
    theta_zero, theta_X, theta_jet, Nat.reduceAdd,
    zero_mul, mul_zero, zero_add, add_zero, one_mul,
    show theta F = thetaN 1 F from rfl] at h
  linear_combination h

theorem target_identity : targetOp (F^2) = 72-1152*X := by
  have h := jet_certificate (X : PowerSeries ℚ) F (thetaN 1 F) (thetaN 2 F)
    (thetaN 3 F) (thetaN 4 F) (thetaN 5 F) base_jet0 base_jet1 base_jet2 base_jet3
  have he : targetOp (F^2) = jetOp X (F^2) (2*F*thetaN 1 F)
      (2*F*thetaN 2 F+2*(thetaN 1 F)^2)
      (2*F*thetaN 3 F+6*thetaN 1 F*thetaN 2 F)
      (2*F*thetaN 4 F+8*thetaN 1 F*thetaN 3 F+6*(thetaN 2 F)^2)
      (2*F*thetaN 5 F+10*thetaN 1 F*thetaN 4 F+20*thetaN 2 F*thetaN 3 F) := by
    simp only [targetOp, square_jet1, square_jet2, square_jet3, square_jet4, square_jet5, jetOp]
  rw [← he] at h
  have hp : (1-16*(X : PowerSeries ℚ)) ≠ 0 := by
    intro hp
    have hc := congrArg constantCoeff hp
    norm_num at hc
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hp)

end A168452Proof

-- Component: A168452Coeffs

namespace A168452Proof
open PowerSeries OMA.S_oeis_a168452

lemma coeff_theta (f : PowerSeries ℚ) (n : ℕ) :
    coeff n (theta f) = (n : ℚ) * coeff n f := by
  cases n with
  | zero => simp [theta]
  | succ n =>
    rw [theta, coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring

lemma coeff_thetaN (k : ℕ) (f : PowerSeries ℚ) (n : ℕ) :
    coeff n (thetaN k f) = (n : ℚ) ^ k * coeff n f := by
  induction k with
  | zero => simp [thetaN]
  | succ k ih =>
    rw [thetaN, coeff_theta, ih, pow_succ]
    ring

lemma coeff_F_sq (n : ℕ) : coeff n (F ^ 2) = (a n : ℚ) := by
  rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i F * coeff j F) n]
  simp [F, a]

lemma coeff_nat_mul (n m : ℕ) (f : PowerSeries ℚ) :
    coeff n ((m : PowerSeries ℚ) * f) = (m : ℚ) * coeff n f := by
  simpa only [map_natCast] using coeff_C_mul n f (m : ℚ)

lemma coeff_nat (n m : ℕ) :
    coeff n (m : PowerSeries ℚ) = if n = 0 then (m : ℚ) else 0 := by
  simpa only [map_natCast] using coeff_C n (m : ℚ)

lemma coeff_num_mul (n m : ℕ) [m.AtLeastTwo] (f : PowerSeries ℚ) :
    coeff n ((ofNat(m) : PowerSeries ℚ) * f) =
      (ofNat(m) : ℚ) * coeff n f := by
  simpa only [map_ofNat] using coeff_C_mul n f (ofNat(m) : ℚ)

lemma coeff_num (n m : ℕ) [m.AtLeastTwo] :
    coeff n (ofNat(m) : PowerSeries ℚ) =
      if n = 0 then (ofNat(m) : ℚ) else 0 := by
  simpa only [map_ofNat] using coeff_C n (ofNat(m) : ℚ)

lemma coeff_shift (g : PowerSeries ℚ) (n k : ℕ) (hk : k ≤ n) :
    coeff n (X ^ k * g) = coeff (n - k) g := by
  rw [coeff_X_pow_mul', if_pos hk]

lemma coeff_shift_one (g : PowerSeries ℚ) (n : ℕ) (hn : 1 ≤ n) :
    coeff n (X * g) = coeff (n - 1) g := by
  simpa only [pow_one] using coeff_shift g n 1 hn

lemma coeff_targetOp (g : PowerSeries ℚ) (n : ℕ) (hn : 4 ≤ n) :
    coeff n (targetOp g) =
    3 * ((n : ℚ) + 4) * ((n : ℚ) + 3) * ((n : ℚ) + 2) * ((n : ℚ) + 1) ^ 2 * coeff n g
      - 4 * (n : ℚ) * ((n : ℚ) + 1)
        * (32 * (n : ℚ) ^ 3 + 164 * (n : ℚ) ^ 2 + 233 * (n : ℚ) + 75) * coeff (n - 1) g
      + 96 * (16 * (n : ℚ) ^ 5 + 24 * (n : ℚ) ^ 4 - 14 * (n : ℚ) ^ 3 - 28 * (n : ℚ) ^ 2
          - 16 * (n : ℚ) + 3) * coeff (n - 2) g
      + 1536 * (-8 * (n : ℚ) ^ 4 + 22 * (n : ℚ) ^ 3 - 32 * (n : ℚ) + 15) * coeff (n - 3) g
      - 16384 * (2 * (n : ℚ) - 5) * ((n : ℚ) - 1) * ((n : ℚ) - 2) * ((n : ℚ) - 3)
        * (2 * (n : ℚ) - 3) * coeff (n - 4) g := by
  simp only [targetOp, map_add, map_sub, neg_mul, map_neg, coeff_num_mul,
    coeff_shift_one _ n (by omega), coeff_shift _ n 2 (by omega),
    coeff_shift _ n 3 (by omega), coeff_shift _ n 4 hn, coeff_thetaN]
  rw [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 2 ≤ n by omega),
    Nat.cast_sub (show 3 ≤ n by omega), Nat.cast_sub hn]
  norm_num only [Nat.cast_ofNat]
  ring

theorem solution_of_operator (hOp : targetOp (F ^ 2) = 72 - 1152 * X) :
    type_of% @OMA.S_oeis_a168452.main := by
  intro n hn
  have h := congrArg (coeff n) hOp
  rw [coeff_targetOp (F ^ 2) n hn] at h
  simp only [coeff_F_sq, map_sub, coeff_num, coeff_num_mul, coeff_X,
    if_neg (show n ≠ 0 by omega), if_neg (show n ≠ 1 by omega), mul_zero, sub_zero] at h
  exact_mod_cast h

end A168452Proof

-- Component: A168452Finish

theorem OMA.solution : type_of% @OMA.S_oeis_a168452.main :=
  A168452Proof.solution_of_operator A168452Proof.target_identity
