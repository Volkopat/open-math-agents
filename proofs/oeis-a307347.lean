import OMAStatements.S_oeis_a307347

-- Closed antelope walks of length 2n. The count is a Fourier integral of
-- phi(x, y) = (cos(3x) cos(4y) + cos(4x) cos(3y)) / 2. Two torus peaks,
-- at (0, 0) and (pi, pi), each contribute the Gaussian integral 2 pi / 25.

open OMA.S_oeis_a307347

noncomputable section

open Finset MeasureTheory Filter Set Function intervalIntegral
open scoped Topology ENNReal BigOperators

namespace OMA_A307347_Proof

def phi (x y : ℝ) : ℝ :=
  (Real.cos (3 * x) * Real.cos (4 * y) + Real.cos (4 * x) * Real.cos (3 * y)) / 2

def step (v : ℤ × ℤ) (x y : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((v.1 : ℂ) * x + (v.2 : ℂ) * y))

def phase (c k : ℤ) (x y : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((c : ℂ) * x + (k : ℂ) * y))

def box (n : ℕ) : ℝ :=
  ∫ x in (-Real.pi)..Real.pi, ∫ y in (-Real.pi)..Real.pi, (phi x y) ^ (2 * n)

def lo : ℝ := -Real.pi / 2
def hi : ℝ := 3 * Real.pi / 2
def rad2 : ℝ := 1 / 16
def sqSet : Set (ℝ × ℝ) := Icc lo hi ×ˢ Icc lo hi

def disk (c : ℝ × ℝ) (r : ℝ) : Set (ℝ × ℝ) :=
  {p | (p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2 ≤ r}

def openDisk (c : ℝ × ℝ) (r : ℝ) : Set (ℝ × ℝ) :=
  {p | (p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2 < r}

def origin : ℝ × ℝ := (0, 0)
def peak : ℝ × ℝ := (Real.pi, Real.pi)

lemma cos_as_sin_sq (θ : ℝ) : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
  conv_lhs => rw [← show 2 * (θ / 2) = θ by ring]
  exact Real.cos_two_mul_eq_one_sub (x := θ / 2)

lemma phi_zero : phi 0 0 = 1 := by
  unfold phi
  simp [Real.cos_zero]

lemma cos_int_three : Real.cos (3 * Real.pi) = -1 := by
  have h : (3 : ℝ) * Real.pi = (3 : ℤ) * Real.pi := by push_cast; ring
  rw [h, Real.cos_int_mul_pi]
  norm_num

lemma cos_int_four : Real.cos (4 * Real.pi) = 1 := by
  have h : (4 : ℝ) * Real.pi = (4 : ℤ) * Real.pi := by push_cast; ring
  rw [h, Real.cos_int_mul_pi]
  norm_num

lemma phi_peak : phi Real.pi Real.pi = -1 := by
  unfold phi
  rw [cos_int_three, cos_int_four]
  norm_num

lemma phi_axis_y : phi 0 Real.pi = 0 := by
  unfold phi
  rw [show (3 : ℝ) * 0 = 0 by ring, show (4 : ℝ) * 0 = 0 by ring, Real.cos_zero,
    cos_int_three, cos_int_four]
  norm_num

lemma phi_axis_x : phi Real.pi 0 = 0 := by
  unfold phi
  rw [show (3 : ℝ) * 0 = 0 by ring, show (4 : ℝ) * 0 = 0 by ring, Real.cos_zero,
    cos_int_three, cos_int_four]
  norm_num

lemma phi_add_pi (x y : ℝ) : phi (x + Real.pi) (y + Real.pi) = -phi x y := by
  unfold phi
  have h3 (t : ℝ) : Real.cos (3 * (t + Real.pi)) = -Real.cos (3 * t) := by
    have h : 3 * (t + Real.pi) = 3 * t + Real.pi + (1 : ℤ) * (2 * Real.pi) := by
      push_cast; ring
    rw [h, Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  have h4 (t : ℝ) : Real.cos (4 * (t + Real.pi)) = Real.cos (4 * t) := by
    have h : 4 * (t + Real.pi) = 4 * t + (2 : ℤ) * (2 * Real.pi) := by
      push_cast; ring
    rw [h, Real.cos_add_int_mul_two_pi]
  rw [h3 x, h4 y, h4 x, h3 y]
  ring

lemma phi_add_two_pi_x (x y : ℝ) : phi (x + 2 * Real.pi) y = phi x y := by
  unfold phi
  have h3 : Real.cos (3 * (x + 2 * Real.pi)) = Real.cos (3 * x) := by
    have h : 3 * (x + 2 * Real.pi) = 3 * x + (3 : ℤ) * (2 * Real.pi) := by
      push_cast; ring
    rw [h, Real.cos_add_int_mul_two_pi]
  have h4 : Real.cos (4 * (x + 2 * Real.pi)) = Real.cos (4 * x) := by
    have h : 4 * (x + 2 * Real.pi) = 4 * x + (4 : ℤ) * (2 * Real.pi) := by
      push_cast; ring
    rw [h, Real.cos_add_int_mul_two_pi]
  rw [h3, h4]

lemma phi_add_two_pi_y (x y : ℝ) : phi x (y + 2 * Real.pi) = phi x y := by
  unfold phi
  have h3 : Real.cos (3 * (y + 2 * Real.pi)) = Real.cos (3 * y) := by
    have h : 3 * (y + 2 * Real.pi) = 3 * y + (3 : ℤ) * (2 * Real.pi) := by
      push_cast; ring
    rw [h, Real.cos_add_int_mul_two_pi]
  have h4 : Real.cos (4 * (y + 2 * Real.pi)) = Real.cos (4 * y) := by
    have h : 4 * (y + 2 * Real.pi) = 4 * y + (4 : ℤ) * (2 * Real.pi) := by
      push_cast; ring
    rw [h, Real.cos_add_int_mul_two_pi]
  rw [h3, h4]

lemma neg_pow_two_mul (z : ℝ) (n : ℕ) : (-z) ^ (2 * n) = z ^ (2 * n) := by
  rw [pow_mul, neg_sq, ← pow_mul]

lemma abs_cos_le_one (θ : ℝ) : |Real.cos θ| ≤ 1 :=
  abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩

lemma abs_cos_prod_le (a b : ℝ) : |Real.cos a * Real.cos b| ≤ 1 := by
  rw [abs_mul]
  nlinarith [abs_cos_le_one a, abs_cos_le_one b, abs_nonneg (Real.cos a), abs_nonneg (Real.cos b)]

lemma abs_phi_le_one (x y : ℝ) : |phi x y| ≤ 1 := by
  unfold phi
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h := abs_add_le (Real.cos (3 * x) * Real.cos (4 * y)) (Real.cos (4 * x) * Real.cos (3 * y))
  have h1 := abs_cos_prod_le (3 * x) (4 * y)
  have h2 := abs_cos_prod_le (4 * x) (3 * y)
  linarith

lemma exp_I (θ : ℝ) :
    Complex.exp (Complex.I * θ) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
  rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

lemma exp_add_I (u v : ℝ) :
    Complex.exp (Complex.I * (u + v)) =
      Complex.exp (Complex.I * u) * Complex.exp (Complex.I * v) := by
  rw [← Complex.exp_add]
  congr 1
  ring

lemma exp_cos_pair (v : ℝ) :
    Complex.exp (Complex.I * v) + Complex.exp (Complex.I * (-v)) = 2 * (Real.cos v : ℂ) := by
  have hneg : Complex.exp (Complex.I * (-v)) =
      (Real.cos (-v) : ℂ) + (Real.sin (-v) : ℂ) * Complex.I := by
    simpa [Complex.ofReal_neg] using exp_I (-v)
  rw [exp_I v, hneg, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg, neg_mul,
    add_add_add_comm, add_neg_cancel, add_zero, ← two_mul]

lemma four_cos (a b : ℝ) :
    Complex.exp (Complex.I * (a + b)) + Complex.exp (Complex.I * (a - b)) +
        Complex.exp (Complex.I * (-a + b)) + Complex.exp (Complex.I * (-a - b)) =
      4 * (Real.cos a * Real.cos b : ℂ) := by
  have align (u v : ℝ) :
      Complex.exp (Complex.I * (u + v)) =
        Complex.exp (Complex.I * u) * Complex.exp (Complex.I * v) :=
    exp_add_I u v
  have e1 : Complex.exp (Complex.I * (a + b)) =
      Complex.exp (Complex.I * a) * Complex.exp (Complex.I * b) :=
    align a b
  have e2 : Complex.exp (Complex.I * (a - b)) =
      Complex.exp (Complex.I * a) * Complex.exp (Complex.I * (-b)) := by
    simpa [sub_eq_add_neg, Complex.ofReal_neg, mul_neg] using align a (-b)
  have e3 : Complex.exp (Complex.I * (-a + b)) =
      Complex.exp (Complex.I * (-a)) * Complex.exp (Complex.I * b) := by
    simpa [Complex.ofReal_neg] using align (-a) b
  have e4 : Complex.exp (Complex.I * (-a - b)) =
      Complex.exp (Complex.I * (-a)) * Complex.exp (Complex.I * (-b)) := by
    simpa [sub_eq_add_neg, Complex.ofReal_neg, mul_neg] using align (-a) (-b)
  rw [e1, e2, e3, e4, add_assoc]
  have hfac :
      Complex.exp (Complex.I * a) * Complex.exp (Complex.I * b) +
          Complex.exp (Complex.I * a) * Complex.exp (Complex.I * (-b)) +
          (Complex.exp (Complex.I * (-a)) * Complex.exp (Complex.I * b) +
            Complex.exp (Complex.I * (-a)) * Complex.exp (Complex.I * (-b))) =
        (Complex.exp (Complex.I * a) + Complex.exp (Complex.I * (-a))) *
          (Complex.exp (Complex.I * b) + Complex.exp (Complex.I * (-b))) := by
    ring
  rw [hfac, exp_cos_pair a, exp_cos_pair b]
  ring

lemma step_real (a b : ℤ) (x y : ℝ) :
    step (a, b) x y = Complex.exp (Complex.I * ((a : ℝ) * x + (b : ℝ) * y)) :=
  rfl

lemma sum_four_a (f : ℤ × ℤ → ℂ) :
    ∑ v ∈ ({(3, 4), (3, -4), (-3, 4), (-3, -4)} : Finset (ℤ × ℤ)), f v =
      f (3, 4) + f (3, -4) + f (-3, 4) + f (-3, -4) := by
  classical
  rw [Finset.sum_insert (by decide : (3, 4) ∉ ({(3, -4), (-3, 4), (-3, -4)} : Finset _))]
  rw [Finset.sum_insert (by decide : (3, -4) ∉ ({(-3, 4), (-3, -4)} : Finset _))]
  rw [Finset.sum_insert (by decide : (-3, 4) ∉ ({(-3, -4)} : Finset _))]
  rw [Finset.sum_singleton]
  abel

lemma sum_four_b (f : ℤ × ℤ → ℂ) :
    ∑ v ∈ ({(4, 3), (4, -3), (-4, 3), (-4, -3)} : Finset (ℤ × ℤ)), f v =
      f (4, 3) + f (4, -3) + f (-4, 3) + f (-4, -3) := by
  classical
  rw [Finset.sum_insert (by decide : (4, 3) ∉ ({(4, -3), (-4, 3), (-4, -3)} : Finset _))]
  rw [Finset.sum_insert (by decide : (4, -3) ∉ ({(-4, 3), (-4, -3)} : Finset _))]
  rw [Finset.sum_insert (by decide : (-4, 3) ∉ ({(-4, -3)} : Finset _))]
  rw [Finset.sum_singleton]
  abel

lemma moves_union :
    moves =
      ({(3, 4), (3, -4), (-3, 4), (-3, -4)} : Finset (ℤ × ℤ)) ∪
        {(4, 3), (4, -3), (-4, 3), (-4, -3)} := by
  decide

lemma moves_disj :
    Disjoint ({(3, 4), (3, -4), (-3, 4), (-3, -4)} : Finset (ℤ × ℤ))
      {(4, 3), (4, -3), (-4, 3), (-4, -3)} := by
  decide

lemma group34 (x y : ℝ) :
    step (3, 4) x y + step (3, -4) x y + step (-3, 4) x y + step (-3, -4) x y =
      4 * (Real.cos (3 * x) * Real.cos (4 * y) : ℂ) := by
  have h1 : step (3, 4) x y = Complex.exp (Complex.I * (3 * x + 4 * y)) := by
    rw [step_real]; congr 1
  have h2 : step (3, -4) x y = Complex.exp (Complex.I * (3 * x - 4 * y)) := by
    rw [step_real]; congr 1; push_cast; ring
  have h3 : step (-3, 4) x y = Complex.exp (Complex.I * (-(3 * x) + 4 * y)) := by
    rw [step_real]; congr 1; push_cast; ring
  have h4 : step (-3, -4) x y = Complex.exp (Complex.I * (-(3 * x) - 4 * y)) := by
    rw [step_real]; congr 1; push_cast; ring
  rw [h1, h2, h3, h4]
  simpa [sub_eq_add_neg] using four_cos (3 * x) (4 * y)

lemma group43 (x y : ℝ) :
    step (4, 3) x y + step (4, -3) x y + step (-4, 3) x y + step (-4, -3) x y =
      4 * (Real.cos (4 * x) * Real.cos (3 * y) : ℂ) := by
  have h1 : step (4, 3) x y = Complex.exp (Complex.I * (4 * x + 3 * y)) := by
    rw [step_real]; congr 1
  have h2 : step (4, -3) x y = Complex.exp (Complex.I * (4 * x - 3 * y)) := by
    rw [step_real]; congr 1; push_cast; ring
  have h3 : step (-4, 3) x y = Complex.exp (Complex.I * (-(4 * x) + 3 * y)) := by
    rw [step_real]; congr 1; push_cast; ring
  have h4 : step (-4, -3) x y = Complex.exp (Complex.I * (-(4 * x) - 3 * y)) := by
    rw [step_real]; congr 1; push_cast; ring
  rw [h1, h2, h3, h4]
  simpa [sub_eq_add_neg] using four_cos (4 * x) (3 * y)

lemma symbol_eq (x y : ℝ) :
    ∑ v ∈ moves, step v x y = 8 * (phi x y : ℂ) := by
  classical
  rw [moves_union, Finset.sum_union moves_disj, sum_four_a, sum_four_b, group34, group43]
  unfold phi
  push_cast
  ring

lemma step_phase (p : Fin n → ℤ × ℤ) (i : Fin n) (x y : ℝ) :
    step (p i) x y = phase (p i).1 (p i).2 x y := by
  rfl

lemma int_exp (k : ℤ) :
    ∫ t in (-Real.pi)..Real.pi, Complex.exp (Complex.I * (k : ℂ) * t) =
      if k = 0 then (2 * Real.pi : ℂ) else 0 := by
  by_cases hk : k = 0
  · subst hk
    simp only [Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero, if_true]
    rw [intervalIntegral.integral_const]
    have hlen : Real.pi - (-Real.pi) = 2 * Real.pi := by ring
    rw [hlen]
    simp
  · simp only [hk, if_false]
    have hc : Complex.I * (k : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hk)
    have hfun : (fun t : ℝ => Complex.exp (Complex.I * (k : ℂ) * t)) =
        fun t : ℝ => Complex.exp ((Complex.I * (k : ℂ)) * t) := by
      ext t; rw [mul_assoc]
    rw [hfun, integral_exp_mul_complex hc]
    have hexp (t : ℝ) : Complex.exp ((Complex.I * (k : ℂ)) * t) =
        (Real.cos ((k : ℝ) * t) : ℂ) + (Real.sin ((k : ℝ) * t) : ℂ) * Complex.I := by
      have harg : (Complex.I * (k : ℂ)) * t =
          Complex.ofReal ((k : ℝ) * t) * Complex.I := by
        push_cast
        ring
      rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    rw [hexp Real.pi, hexp (-Real.pi)]
    have hsinπ : Real.sin ((k : ℝ) * Real.pi) = 0 := Real.sin_int_mul_pi k
    have hsinN : Real.sin ((k : ℝ) * -Real.pi) = 0 := by
      rw [mul_neg, Real.sin_neg, hsinπ, neg_zero]
    have hcosN : Real.cos ((k : ℝ) * -Real.pi) = Real.cos ((k : ℝ) * Real.pi) := by
      rw [mul_neg, Real.cos_neg]
    rw [hsinπ, hsinN, hcosN]
    simp [sub_self, zero_div, zero_mul]

lemma inner_char (c k : ℤ) (x : ℝ) :
    ∫ y in (-Real.pi)..Real.pi, phase c k x y =
      Complex.exp (Complex.I * (c : ℂ) * x) * (if k = 0 then (2 * Real.pi : ℂ) else 0) := by
  unfold phase
  have hsplit : ∀ y : ℝ, Complex.exp (Complex.I * ((c : ℂ) * x + (k : ℂ) * y)) =
      Complex.exp (Complex.I * (c : ℂ) * x) * Complex.exp (Complex.I * (k : ℂ) * y) := by
    intro y
    rw [← Complex.exp_add]
    congr 1
    ring
  simp_rw [hsplit, intervalIntegral.integral_const_mul, int_exp]

lemma outer_char (c k : ℤ) :
    ∫ x in (-Real.pi)..Real.pi,
        Complex.exp (Complex.I * (c : ℂ) * x) * (if k = 0 then (2 * Real.pi : ℂ) else 0) =
      if c = 0 ∧ k = 0 then (2 * Real.pi : ℂ) ^ 2 else 0 := by
  rw [intervalIntegral.integral_mul_const, int_exp]
  by_cases hc : c = 0 <;> by_cases hk : k = 0 <;> simp [hc, hk, pow_two, mul_comm, mul_left_comm]

lemma symbol_pow (n : ℕ) (x y : ℝ) :
    (∑ v ∈ moves, step v x y) ^ (2 * n) =
      ∑ p ∈ Fintype.piFinset (fun _ : Fin (2 * n) => moves),
        phase (∑ i, p i).1 (∑ i, p i).2 x y := by
  rw [Finset.sum_pow']
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold phase step
  rw [← Complex.exp_sum]
  apply congrArg Complex.exp
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  congr 1
  · rw [← Int.cast_sum]
    have hsum : ∑ i, (p i).1 = (∑ i, p i).1 := by
      simpa only [AddMonoidHom.coe_fst] using
        (map_sum (AddMonoidHom.fst ℤ ℤ) (fun i => p i) Finset.univ).symm
    rw [hsum]
  · rw [← Int.cast_sum]
    have hsum : ∑ i, (p i).2 = (∑ i, p i).2 := by
      simpa only [AddMonoidHom.coe_snd] using
        (map_sum (AddMonoidHom.snd ℤ ℤ) (fun i => p i) Finset.univ).symm
    rw [hsum]

set_option maxHeartbeats 8000000 in
lemma path_integral (n : ℕ) :
    ∫ x in (-Real.pi)..Real.pi, ∫ y in (-Real.pi)..Real.pi,
        (∑ v ∈ moves, step v x y) ^ (2 * n) =
      (a n : ℂ) * (2 * Real.pi : ℂ) ^ 2 := by
  let S := Fintype.piFinset (fun _ : Fin (2 * n) => moves)
  simp_rw [symbol_pow]
  have hinner : ∀ x : ℝ, ∫ y in (-Real.pi)..Real.pi,
      ∑ p ∈ S, phase (∑ i, p i).1 (∑ i, p i).2 x y =
      ∑ p ∈ S, ∫ y in (-Real.pi)..Real.pi, phase (∑ i, p i).1 (∑ i, p i).2 x y := by
    intro x
    refine intervalIntegral.integral_finsetSum ?_
    intro p _
    apply Continuous.intervalIntegrable
    unfold phase
    fun_prop
  have hint : ∫ x in (-Real.pi)..Real.pi, ∫ y in (-Real.pi)..Real.pi,
      ∑ p ∈ S, phase (∑ i, p i).1 (∑ i, p i).2 x y =
      ∫ x in (-Real.pi)..Real.pi, ∑ p ∈ S, ∫ y in (-Real.pi)..Real.pi,
        phase (∑ i, p i).1 (∑ i, p i).2 x y := by
    refine intervalIntegral.integral_congr fun x _ => hinner x
  rw [hint]
  simp_rw [inner_char]
  have houter : ∫ x in (-Real.pi)..Real.pi, ∑ p ∈ S,
      Complex.exp (Complex.I * ((∑ i, p i).1 : ℂ) * x) *
        (if (∑ i, p i).2 = 0 then (2 * Real.pi : ℂ) else 0) =
      ∑ p ∈ S, ∫ x in (-Real.pi)..Real.pi,
        Complex.exp (Complex.I * ((∑ i, p i).1 : ℂ) * x) *
          (if (∑ i, p i).2 = 0 then (2 * Real.pi : ℂ) else 0) := by
    refine intervalIntegral.integral_finsetSum ?_
    intro p _
    apply Continuous.intervalIntegrable
    fun_prop
  rw [houter]
  simp_rw [outer_char]
  have hiff : ∀ p : Fin (2 * n) → ℤ × ℤ,
      ((∑ i, p i).1 = 0 ∧ (∑ i, p i).2 = 0) ↔ ∑ i, p i = 0 := by
    intro p
    simpa using (Prod.ext_iff (x := ∑ i, p i) (y := (0 : ℤ × ℤ))).symm
  simp_rw [hiff]
  have hsplit : ∀ p : Fin (2 * n) → ℤ × ℤ,
      (if ∑ i, p i = 0 then (2 * Real.pi : ℂ) ^ 2 else 0) =
        (2 * Real.pi : ℂ) ^ 2 * (if ∑ i, p i = 0 then 1 else 0) := by
    intro p
    split_ifs <;> simp
  simp_rw [hsplit, ← Finset.mul_sum, Finset.sum_boole]
  have hcard : (#{p ∈ S | ∑ i, p i = 0} : ℂ) = (a n : ℂ) := by
    simp [S, a]
  rw [hcard]
  ring

lemma eight_pow (n : ℕ) : (8 : ℂ) ^ (2 * n) = (64 : ℂ) ^ n := by
  rw [pow_mul]
  norm_num

lemma phi_pow_mul (n : ℕ) (x y : ℝ) :
    ((8 : ℂ) * (phi x y : ℂ)) ^ (2 * n) =
      (64 : ℂ) ^ n * Complex.ofReal ((phi x y) ^ (2 * n)) := by
  rw [mul_pow, eight_pow, Complex.ofReal_pow]

lemma integral_eight (n : ℕ) :
    ∫ x in (-Real.pi)..Real.pi, ∫ y in (-Real.pi)..Real.pi,
        ((8 : ℂ) * (phi x y : ℂ)) ^ (2 * n) =
      (64 : ℂ) ^ n * (box n : ℂ) := by
  have hinner (x : ℝ) :
      ∫ y in (-Real.pi)..Real.pi, ((8 : ℂ) * (phi x y : ℂ)) ^ (2 * n) =
        (64 : ℂ) ^ n *
          Complex.ofReal (∫ y in (-Real.pi)..Real.pi, (phi x y) ^ (2 * n)) := by
    simp_rw [phi_pow_mul]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
  simp_rw [hinner]
  rw [intervalIntegral.integral_const_mul]
  unfold box
  rw [intervalIntegral.integral_ofReal]

lemma a_mul_box (n : ℕ) :
    (a n : ℝ) * (2 * Real.pi) ^ 2 = (64 : ℝ) ^ n * box n := by
  have hsym : ∫ x in (-Real.pi)..Real.pi, ∫ y in (-Real.pi)..Real.pi,
      ((8 : ℂ) * (phi x y : ℂ)) ^ (2 * n) = (a n : ℂ) * (2 * Real.pi : ℂ) ^ 2 := by
    simp_rw [← symbol_eq]
    exact path_integral n
  rw [integral_eight] at hsym
  have hcast : ((64 : ℝ) ^ n * box n : ℂ) = ((a n : ℝ) * (2 * Real.pi) ^ 2 : ℂ) := by
    push_cast
    simpa using hsym
  exact_mod_cast hcast.symm

lemma a_eq_box (n : ℕ) :
    (a n : ℝ) = (64 : ℝ) ^ n * box n / (4 * Real.pi ^ 2) := by
  have hmul := a_mul_box n
  have hsq : (2 * Real.pi) ^ 2 = 4 * Real.pi ^ 2 := by ring
  rw [hsq] at hmul
  have hne : 4 * Real.pi ^ 2 ≠ 0 := by positivity
  exact (eq_div_iff hne).mpr hmul

lemma lo_le_hi : lo ≤ hi := by
  unfold lo hi
  nlinarith [Real.pi_pos]

lemma neg_pi_shift : -Real.pi + 2 * Real.pi = Real.pi := by ring

lemma lo_shift : lo + 2 * Real.pi = hi := by
  unfold lo hi
  ring

lemma periodic_inner (n : ℕ) (x : ℝ) :
    Function.Periodic (fun y => (phi x y) ^ (2 * n)) (2 * Real.pi) := by
  intro y
  dsimp
  rw [phi_add_two_pi_y]

lemma periodic_outer (n : ℕ) :
    Function.Periodic (fun x => ∫ y in lo..hi, (phi x y) ^ (2 * n)) (2 * Real.pi) := by
  intro x
  dsimp
  refine intervalIntegral.integral_congr ?_
  intro y _
  dsimp
  rw [phi_add_two_pi_x]

lemma box_shift (n : ℕ) :
    box n = ∫ x in lo..hi, ∫ y in lo..hi, (phi x y) ^ (2 * n) := by
  have hinner : ∀ x, ∫ y in (-Real.pi)..Real.pi, (phi x y) ^ (2 * n) =
      ∫ y in lo..hi, (phi x y) ^ (2 * n) := by
    intro x
    have h := (periodic_inner n x).intervalIntegral_add_eq (-Real.pi) lo
    rw [neg_pi_shift, lo_shift] at h
    exact h
  unfold box
  simp_rw [hinner]
  have h := (periodic_outer n).intervalIntegral_add_eq (-Real.pi) lo
  rw [neg_pi_shift, lo_shift] at h
  exact h

lemma cont_pow (n : ℕ) : Continuous fun p : ℝ × ℝ => (phi p.1 p.2) ^ (2 * n) := by
  unfold phi
  fun_prop

lemma integrable_sq (n : ℕ) :
    IntegrableOn (fun p : ℝ × ℝ => (phi p.1 p.2) ^ (2 * n)) sqSet :=
  (cont_pow n).continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

lemma box_set (n : ℕ) :
    ∫ x in lo..hi, ∫ y in lo..hi, (phi x y) ^ (2 * n) =
      ∫ p in sqSet, (phi p.1 p.2) ^ (2 * n) := by
  simp_rw [intervalIntegral.integral_of_le lo_le_hi]
  have hinner : ∀ x, ∫ y in Ioc lo hi, (phi x y) ^ (2 * n) =
      ∫ y in Icc lo hi, (phi x y) ^ (2 * n) := by
    intro x
    exact (integral_Icc_eq_integral_Ioc).symm
  simp_rw [hinner]
  rw [← integral_Icc_eq_integral_Ioc]
  rw [sqSet, Measure.volume_eq_prod ℝ ℝ]
  exact (setIntegral_prod _ (integrable_sq n)).symm

lemma abs_sin_sq_sub (θ : ℝ) : |Real.sin θ ^ 2 - θ ^ 2| ≤ |θ| ^ 4 / 3 := by
  have hdiff : |Real.sin θ - θ| ≤ |θ| ^ 3 / 6 := by
    simpa [abs_sub_comm] using Real.abs_sub_sin_le θ
  have hsum : |Real.sin θ + θ| ≤ 2 * |θ| := by
    calc |Real.sin θ + θ| ≤ |Real.sin θ| + |θ| := abs_add_le _ _
      _ ≤ |θ| + |θ| := add_le_add Real.abs_sin_le_abs le_rfl
      _ = 2 * |θ| := by ring
  have hfac : Real.sin θ ^ 2 - θ ^ 2 = (Real.sin θ - θ) * (Real.sin θ + θ) := by
    rw [sq_sub_sq, mul_comm]
  rw [hfac, abs_mul]
  have hmul : |Real.sin θ - θ| * |Real.sin θ + θ| ≤ (|θ| ^ 3 / 6) * (2 * |θ|) :=
    mul_le_mul hdiff hsum (abs_nonneg _) (div_nonneg (pow_nonneg (abs_nonneg _) _) (by norm_num))
  have hmul' : (|θ| ^ 3 / 6) * (2 * |θ|) = |θ| ^ 4 / 3 := by ring
  linarith

lemma lead_eq (x y : ℝ) :
    (3 * x / 2) ^ 2 + (2 * y) ^ 2 + (2 * x) ^ 2 + (3 * y / 2) ^ 2 =
      (25 / 4) * (x ^ 2 + y ^ 2) := by
  ring

lemma phi_expand (x y : ℝ) :
    phi x y = 1 - (Real.sin (3 * x / 2) ^ 2 + Real.sin (2 * y) ^ 2 +
      Real.sin (2 * x) ^ 2 + Real.sin (3 * y / 2) ^ 2) +
      2 * Real.sin (3 * x / 2) ^ 2 * Real.sin (2 * y) ^ 2 +
      2 * Real.sin (2 * x) ^ 2 * Real.sin (3 * y / 2) ^ 2 := by
  unfold phi
  rw [cos_as_sin_sq (3 * x), cos_as_sin_sq (4 * y), cos_as_sin_sq (4 * x), cos_as_sin_sq (3 * y)]
  ring

lemma abs_pow_four (t : ℝ) : |t| ^ 4 = t ^ 4 := by
  calc |t| ^ 4 = (|t| ^ 2) ^ 2 := by ring
    _ = (t ^ 2) ^ 2 := by rw [sq_abs]
    _ = t ^ 4 := by ring

lemma abs_add4 (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  calc |a + b + c + d| ≤ |a + b + c| + |d| := abs_add_le _ _
    _ ≤ |a + b| + |c| + |d| := by
        linarith [abs_add_le (a + b) c]
    _ ≤ |a| + |b| + |c| + |d| := by
        linarith [abs_add_le a b]

lemma phi_taylor (x y : ℝ) :
    |phi x y - (1 - (25 / 4) * (x ^ 2 + y ^ 2))| ≤ 32 * (x ^ 2 + y ^ 2) ^ 2 := by
  set s1 : ℝ := Real.sin (3 * x / 2)
  set s2 : ℝ := Real.sin (2 * y)
  set s3 : ℝ := Real.sin (2 * x)
  set s4 : ℝ := Real.sin (3 * y / 2)
  set t1 : ℝ := 3 * x / 2
  set t2 : ℝ := 2 * y
  set t3 : ℝ := 2 * x
  set t4 : ℝ := 3 * y / 2
  have hform : phi x y - (1 - (25 / 4) * (x ^ 2 + y ^ 2)) =
      -((s1 ^ 2 - t1 ^ 2) + (s2 ^ 2 - t2 ^ 2) + (s3 ^ 2 - t3 ^ 2) + (s4 ^ 2 - t4 ^ 2)) +
        (2 * s1 ^ 2 * s2 ^ 2 + 2 * s3 ^ 2 * s4 ^ 2) := by
    unfold s1 s2 s3 s4 t1 t2 t3 t4
    rw [phi_expand, ← lead_eq]
    ring_nf
  have htri : |phi x y - (1 - (25 / 4) * (x ^ 2 + y ^ 2))| ≤
      |s1 ^ 2 - t1 ^ 2| + |s2 ^ 2 - t2 ^ 2| + |s3 ^ 2 - t3 ^ 2| + |s4 ^ 2 - t4 ^ 2| +
        |2 * s1 ^ 2 * s2 ^ 2 + 2 * s3 ^ 2 * s4 ^ 2| := by
    rw [hform]
    calc |-((s1 ^ 2 - t1 ^ 2) + (s2 ^ 2 - t2 ^ 2) + (s3 ^ 2 - t3 ^ 2) + (s4 ^ 2 - t4 ^ 2)) +
          (2 * s1 ^ 2 * s2 ^ 2 + 2 * s3 ^ 2 * s4 ^ 2)|
        ≤ |-((s1 ^ 2 - t1 ^ 2) + (s2 ^ 2 - t2 ^ 2) + (s3 ^ 2 - t3 ^ 2) + (s4 ^ 2 - t4 ^ 2))| +
            |2 * s1 ^ 2 * s2 ^ 2 + 2 * s3 ^ 2 * s4 ^ 2| := abs_add_le _ _
      _ = |(s1 ^ 2 - t1 ^ 2) + (s2 ^ 2 - t2 ^ 2) + (s3 ^ 2 - t3 ^ 2) + (s4 ^ 2 - t4 ^ 2)| +
            |2 * s1 ^ 2 * s2 ^ 2 + 2 * s3 ^ 2 * s4 ^ 2| := by rw [abs_neg]
      _ ≤ |s1 ^ 2 - t1 ^ 2| + |s2 ^ 2 - t2 ^ 2| + |s3 ^ 2 - t3 ^ 2| + |s4 ^ 2 - t4 ^ 2| +
            |2 * s1 ^ 2 * s2 ^ 2 + 2 * s3 ^ 2 * s4 ^ 2| := by
          gcongr
          exact abs_add4 _ _ _ _
  have h1 := abs_sin_sq_sub t1
  have h2 := abs_sin_sq_sub t2
  have h3 := abs_sin_sq_sub t3
  have h4 := abs_sin_sq_sub t4
  have hsin : |s1 ^ 2 - t1 ^ 2| + |s2 ^ 2 - t2 ^ 2| + |s3 ^ 2 - t3 ^ 2| + |s4 ^ 2 - t4 ^ 2| ≤
      8 * (x ^ 4 + y ^ 4) := by
    have hb1 : |t1| ^ 4 = (81 / 16) * x ^ 4 := by
      rw [abs_pow_four]; unfold t1; ring
    have hb2 : |t2| ^ 4 = 16 * y ^ 4 := by
      rw [abs_pow_four]; unfold t2; ring
    have hb3 : |t3| ^ 4 = 16 * x ^ 4 := by
      rw [abs_pow_four]; unfold t3; ring
    have hb4 : |t4| ^ 4 = (81 / 16) * y ^ 4 := by
      rw [abs_pow_four]; unfold t4; ring
    have hsum : |t1| ^ 4 / 3 + |t2| ^ 4 / 3 + |t3| ^ 4 / 3 + |t4| ^ 4 / 3 =
        (337 / 48) * (x ^ 4 + y ^ 4) := by
      rw [hb1, hb2, hb3, hb4]
      ring
    have hle8 : (337 / 48) * (x ^ 4 + y ^ 4) ≤ 8 * (x ^ 4 + y ^ 4) := by
      have hnum : (337 : ℝ) / 48 ≤ 8 := by norm_num
      have hnn : 0 ≤ x ^ 4 + y ^ 4 := by positivity
      nlinarith
    calc |s1 ^ 2 - t1 ^ 2| + |s2 ^ 2 - t2 ^ 2| + |s3 ^ 2 - t3 ^ 2| + |s4 ^ 2 - t4 ^ 2|
        ≤ |t1| ^ 4 / 3 + |t2| ^ 4 / 3 + |t3| ^ 4 / 3 + |t4| ^ 4 / 3 := by
          gcongr
      _ = (337 / 48) * (x ^ 4 + y ^ 4) := hsum
      _ ≤ 8 * (x ^ 4 + y ^ 4) := hle8
  have hcross : |2 * s1 ^ 2 * s2 ^ 2 + 2 * s3 ^ 2 * s4 ^ 2| ≤ 36 * x ^ 2 * y ^ 2 := by
    have hs1 : |s1| ≤ |t1| := Real.abs_sin_le_abs
    have hs2 : |s2| ≤ |t2| := Real.abs_sin_le_abs
    have hs3 : |s3| ≤ |t3| := Real.abs_sin_le_abs
    have hs4 : |s4| ≤ |t4| := Real.abs_sin_le_abs
    have hprod (u v a b : ℝ) (hu : |u| ≤ |a|) (hv : |v| ≤ |b|) :
        |u ^ 2 * v ^ 2| ≤ |a| ^ 2 * |b| ^ 2 := by
      rw [abs_mul, abs_pow, abs_pow]
      exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hu 2)
        (pow_le_pow_left₀ (abs_nonneg _) hv 2) (pow_nonneg (abs_nonneg _) _)
        (pow_nonneg (abs_nonneg _) _)
    have ht12 : |t1| ^ 2 * |t2| ^ 2 = 9 * x ^ 2 * y ^ 2 := by
      rw [sq_abs, sq_abs]; unfold t1 t2; ring
    have ht34 : |t3| ^ 2 * |t4| ^ 2 = 9 * x ^ 2 * y ^ 2 := by
      rw [sq_abs, sq_abs]; unfold t3 t4; ring
    have h12 : |2 * s1 ^ 2 * s2 ^ 2| ≤ 18 * x ^ 2 * y ^ 2 := by
      have habs : |2 * s1 ^ 2 * s2 ^ 2| = 2 * |s1 ^ 2 * s2 ^ 2| := by
        rw [mul_assoc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      calc |2 * s1 ^ 2 * s2 ^ 2| = 2 * |s1 ^ 2 * s2 ^ 2| := habs
        _ ≤ 2 * (|t1| ^ 2 * |t2| ^ 2) :=
            mul_le_mul_of_nonneg_left (hprod s1 s2 t1 t2 hs1 hs2) (by norm_num)
        _ = 18 * x ^ 2 * y ^ 2 := by rw [ht12]; ring
    have h34 : |2 * s3 ^ 2 * s4 ^ 2| ≤ 18 * x ^ 2 * y ^ 2 := by
      have habs : |2 * s3 ^ 2 * s4 ^ 2| = 2 * |s3 ^ 2 * s4 ^ 2| := by
        rw [mul_assoc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      calc |2 * s3 ^ 2 * s4 ^ 2| = 2 * |s3 ^ 2 * s4 ^ 2| := habs
        _ ≤ 2 * (|t3| ^ 2 * |t4| ^ 2) :=
            mul_le_mul_of_nonneg_left (hprod s3 s4 t3 t4 hs3 hs4) (by norm_num)
        _ = 18 * x ^ 2 * y ^ 2 := by rw [ht34]; ring
    calc |2 * s1 ^ 2 * s2 ^ 2 + 2 * s3 ^ 2 * s4 ^ 2|
        ≤ |2 * s1 ^ 2 * s2 ^ 2| + |2 * s3 ^ 2 * s4 ^ 2| := abs_add_le _ _
      _ ≤ 18 * x ^ 2 * y ^ 2 + 18 * x ^ 2 * y ^ 2 := add_le_add h12 h34
      _ = 36 * x ^ 2 * y ^ 2 := by ring
  have hρ : 8 * (x ^ 4 + y ^ 4) + 36 * x ^ 2 * y ^ 2 ≤ 32 * (x ^ 2 + y ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x * y), sq_nonneg x, sq_nonneg y]
  calc |phi x y - (1 - (25 / 4) * (x ^ 2 + y ^ 2))|
      ≤ |s1 ^ 2 - t1 ^ 2| + |s2 ^ 2 - t2 ^ 2| + |s3 ^ 2 - t3 ^ 2| + |s4 ^ 2 - t4 ^ 2| +
          |2 * s1 ^ 2 * s2 ^ 2 + 2 * s3 ^ 2 * s4 ^ 2| := htri
    _ ≤ 8 * (x ^ 4 + y ^ 4) + 36 * x ^ 2 * y ^ 2 := by gcongr
    _ ≤ 32 * (x ^ 2 + y ^ 2) ^ 2 := hρ

lemma phi_bounds_small {x y : ℝ} (h : x ^ 2 + y ^ 2 ≤ rad2) :
    31 / 64 ≤ phi x y ∧ phi x y ≤ Real.exp (-(17 / 4) * (x ^ 2 + y ^ 2)) := by
  have herr := phi_taylor x y
  have habs := (abs_le.mp herr)
  have h32 : 32 * (x ^ 2 + y ^ 2) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
    have hrad : x ^ 2 + y ^ 2 ≤ 1 / 16 := by simpa [rad2] using h
    nlinarith [sq_nonneg (x ^ 2 + y ^ 2)]
  have hlo : 1 - (33 / 4) * (x ^ 2 + y ^ 2) ≤ phi x y := by linarith [habs.1, h32]
  have hhi : phi x y ≤ 1 - (17 / 4) * (x ^ 2 + y ^ 2) := by linarith [habs.2, h32]
  refine ⟨?_, ?_⟩
  · have h33 : (33 / 4) * (x ^ 2 + y ^ 2) ≤ 33 / 64 := by
      have hrad : x ^ 2 + y ^ 2 ≤ 1 / 16 := by simpa [rad2] using h
      nlinarith
    linarith
  · have hexp := Real.add_one_le_exp (-(17 / 4) * (x ^ 2 + y ^ 2))
    linarith

lemma fourth_le_pi : (1 : ℝ) / 4 ≤ Real.pi / 2 := by
  nlinarith [Real.pi_gt_three]

lemma disk_subset_sq (c : ℝ × ℝ) (hc1 : |c.1| = 0 ∨ c.1 = Real.pi) (hc2 : |c.2| = 0 ∨ c.2 = Real.pi) :
    disk c rad2 ⊆ sqSet := by
  intro p hp
  have hrad : (p.1 - c.1) ^ 2 ≤ rad2 ∧ (p.2 - c.2) ^ 2 ≤ rad2 := by
    have hle : (p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2 ≤ rad2 := by
      simpa [disk] using hp
    constructor <;> nlinarith [hle, sq_nonneg (p.1 - c.1), sq_nonneg (p.2 - c.2)]
  have habs1 : |p.1 - c.1| ≤ 1 / 4 := by
    have hsq : (p.1 - c.1) ^ 2 ≤ (1 / 4) ^ 2 := by
      have h := hrad.1
      simp only [rad2] at h
      have h16 : (16 : ℝ)⁻¹ = (1 / 4) ^ 2 := by norm_num
      linarith
    exact abs_le_of_sq_le_sq hsq (by norm_num)
  have habs2 : |p.2 - c.2| ≤ 1 / 4 := by
    have hsq : (p.2 - c.2) ^ 2 ≤ (1 / 4) ^ 2 := by
      have h := hrad.2
      simp only [rad2] at h
      have h16 : (16 : ℝ)⁻¹ = (1 / 4) ^ 2 := by norm_num
      linarith
    exact abs_le_of_sq_le_sq hsq (by norm_num)
  have hcoord (z w : ℝ) (hw : |w| = 0 ∨ w = Real.pi) (hz : |z - w| ≤ 1 / 4) :
      lo ≤ z ∧ z ≤ hi := by
    rcases hw with hw | hw
    · have hw0 : w = 0 := by
        have : |w| ≤ 0 := by simpa using hw.le
        have := abs_nonneg w
        have : |w| = 0 := le_antisymm (by simpa using hw.le) this
        exact abs_eq_zero.mp this
      rw [hw0] at hz
      simp only [sub_zero] at hz
      constructor
      · unfold lo
        linarith [abs_le.mp hz, fourth_le_pi]
      · unfold hi
        linarith [abs_le.mp hz, Real.pi_gt_three]
    · rw [hw] at hz
      constructor
      · unfold lo
        have hneg : -Real.pi / 2 ≤ Real.pi - 1 / 4 := by nlinarith [Real.pi_gt_three]
        linarith [abs_le.mp hz, hneg]
      · unfold hi
        have hpos : Real.pi + 1 / 4 ≤ 3 * Real.pi / 2 := by nlinarith [Real.pi_gt_three]
        linarith [abs_le.mp hz, hpos]
  have h1 := hcoord p.1 c.1 hc1 habs1
  have h2 := hcoord p.2 c.2 hc2 habs2
  exact ⟨⟨h1.1, h1.2⟩, ⟨h2.1, h2.2⟩⟩

lemma origin_disk_subset : disk origin rad2 ⊆ sqSet :=
  disk_subset_sq origin (Or.inl (by simp [origin])) (Or.inl (by simp [origin]))

lemma peak_disk_subset : disk peak rad2 ⊆ sqSet :=
  disk_subset_sq peak (Or.inr (by simp [peak])) (Or.inr (by simp [peak]))

lemma disks_disjoint : Disjoint (disk origin rad2) (disk peak rad2) := by
  rw [Set.disjoint_left]
  intro p hp0 hp1
  have h0 : p.1 ^ 2 + p.2 ^ 2 ≤ rad2 := by simpa [disk, origin] using hp0
  have h1 : (p.1 - Real.pi) ^ 2 + (p.2 - Real.pi) ^ 2 ≤ rad2 := by simpa [disk, peak] using hp1
  have hcomp1 : Real.pi ^ 2 ≤ 2 * p.1 ^ 2 + 2 * (p.1 - Real.pi) ^ 2 := by
    nlinarith [sq_nonneg (p.1 + (p.1 - Real.pi))]
  have hcomp2 : Real.pi ^ 2 ≤ 2 * p.2 ^ 2 + 2 * (p.2 - Real.pi) ^ 2 := by
    nlinarith [sq_nonneg (p.2 + (p.2 - Real.pi))]
  have hsum : 2 * Real.pi ^ 2 ≤ 4 * rad2 := by
    nlinarith
  simp only [rad2] at hsum
  nlinarith [Real.pi_gt_three, hsum]

lemma int_of_pi_interval {k : ℤ} {x : ℝ} (hx0 : lo ≤ x) (hx1 : x ≤ hi)
    (hk : (k : ℝ) * Real.pi = x) : k = 0 ∨ k = 1 := by
  have hlt : (k : ℝ) < 2 := by
    unfold hi at hx1
    nlinarith [Real.pi_gt_three, Real.pi_pos, hk, hx1]
  have hgt : (-1 : ℝ) < k := by
    unfold lo at hx0
    nlinarith [Real.pi_gt_three, Real.pi_pos, hk, hx0]
  have hlt' : k < 2 := by exact_mod_cast hlt
  have hgt' : -1 < k := by exact_mod_cast hgt
  omega

lemma abs_mul_eq_one_of_le {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hab : |a * b| = 1) :
    |a| = 1 ∧ |b| = 1 := by
  rw [abs_mul] at hab
  constructor <;> nlinarith [abs_nonneg a, abs_nonneg b]

lemma abs_add_two {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hab : |a + b| = 2) :
    |a| = 1 ∧ |b| = 1 := by
  have hle : |a + b| ≤ |a| + |b| := abs_add_le a b
  have hsum : |a| + |b| = 2 := by
    have hupper : |a| + |b| ≤ 2 := by linarith
    have hlower : 2 ≤ |a| + |b| := by linarith
    linarith
  constructor <;> nlinarith

lemma pi_int_of_abs_cos {θ : ℝ} (h : |Real.cos θ| = 1) : ∃ k : ℤ, (k : ℝ) * Real.pi = θ :=
  (Real.abs_cos_eq_one_iff).mp h

lemma coord_pi (x : ℝ) (hx : x ∈ Icc lo hi) (h3 : |Real.cos (3 * x)| = 1)
    (h4 : |Real.cos (4 * x)| = 1) : x = 0 ∨ x = Real.pi := by
  obtain ⟨k, hk⟩ := pi_int_of_abs_cos h3
  obtain ⟨m, hm⟩ := pi_int_of_abs_cos h4
  have hxeq : x = ((m - k : ℤ) : ℝ) * Real.pi := by
    have hk' : (k : ℝ) * Real.pi = 3 * x := hk
    have hm' : (m : ℝ) * Real.pi = 4 * x := hm
    have hdiff : x = 4 * x - 3 * x := by ring
    rw [hdiff, ← hm', ← hk']
    push_cast
    ring
  have hk0 := int_of_pi_interval hx.1 hx.2 hxeq.symm
  rcases hk0 with hk0 | hk0
  · left
    rw [hk0] at hxeq
    simp only [Int.cast_zero, zero_mul] at hxeq
    exact hxeq
  · right
    rw [hk0] at hxeq
    simp only [Int.cast_one, one_mul] at hxeq
    exact hxeq

lemma abs_phi_one_mem {p : ℝ × ℝ} (hp : p ∈ sqSet) (habs : |phi p.1 p.2| = 1) :
    p = origin ∨ p = peak := by
  have hA : |Real.cos (3 * p.1) * Real.cos (4 * p.2)| = 1 := by
    unfold phi at habs
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at habs
    have hsum := abs_add_two (abs_cos_prod_le (3 * p.1) (4 * p.2))
      (abs_cos_prod_le (4 * p.1) (3 * p.2)) (by
        have : |Real.cos (3 * p.1) * Real.cos (4 * p.2) + Real.cos (4 * p.1) * Real.cos (3 * p.2)| =
            2 := by linarith
        exact this)
    exact hsum.1
  have hB : |Real.cos (4 * p.1) * Real.cos (3 * p.2)| = 1 := by
    unfold phi at habs
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at habs
    have hsum := abs_add_two (abs_cos_prod_le (3 * p.1) (4 * p.2))
      (abs_cos_prod_le (4 * p.1) (3 * p.2)) (by
        have : |Real.cos (3 * p.1) * Real.cos (4 * p.2) + Real.cos (4 * p.1) * Real.cos (3 * p.2)| =
            2 := by linarith
        exact this)
    exact hsum.2
  have h3x : |Real.cos (3 * p.1)| = 1 :=
    (abs_mul_eq_one_of_le (abs_cos_le_one _) (abs_cos_le_one _) hA).1
  have h4y : |Real.cos (4 * p.2)| = 1 :=
    (abs_mul_eq_one_of_le (abs_cos_le_one _) (abs_cos_le_one _) hA).2
  have h4x : |Real.cos (4 * p.1)| = 1 :=
    (abs_mul_eq_one_of_le (abs_cos_le_one _) (abs_cos_le_one _) hB).1
  have h3y : |Real.cos (3 * p.2)| = 1 :=
    (abs_mul_eq_one_of_le (abs_cos_le_one _) (abs_cos_le_one _) hB).2
  have hx := coord_pi p.1 hp.1 h3x h4x
  have hy := coord_pi p.2 hp.2 h3y h4y
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · left
    simp [origin, Prod.ext_iff, hx, hy]
  · exfalso
    have : |phi p.1 p.2| = 0 := by simp [hx, hy, phi_axis_y]
    linarith
  · exfalso
    have : |phi p.1 p.2| = 0 := by simp [hx, hy, phi_axis_x]
    linarith
  · right
    simp [peak, Prod.ext_iff, hx, hy]

def gap : Set (ℝ × ℝ) := sqSet \ (openDisk origin rad2 ∪ openDisk peak rad2)

lemma gap_closed : IsClosed gap := by
  have hop : IsOpen (openDisk origin rad2 ∪ openDisk peak rad2) := by
    refine IsOpen.union ?_ ?_
    · exact isOpen_lt (by fun_prop) continuous_const
    · exact isOpen_lt (by fun_prop) continuous_const
  exact (isClosed_Icc.prod isClosed_Icc).inter hop.isClosed_compl

lemma gap_compact : IsCompact gap :=
  IsCompact.of_isClosed_subset (isCompact_Icc.prod isCompact_Icc) gap_closed
    (fun _ hp => hp.1)

lemma gap_nonempty : gap.Nonempty := by
  refine ⟨(0, Real.pi), ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · unfold lo hi
      constructor <;> nlinarith [Real.pi_gt_three, Real.pi_pos]
    · unfold lo hi
      constructor <;> nlinarith [Real.pi_gt_three, Real.pi_pos]
  · intro h
    rcases h with h | h
    · have : Real.pi ^ 2 < rad2 := by simpa [openDisk, origin] using h
      simp only [rad2] at this
      nlinarith [Real.pi_gt_three, this]
    · have : Real.pi ^ 2 < rad2 := by simpa [openDisk, peak] using h
      simp only [rad2] at this
      nlinarith [Real.pi_gt_three, this]

lemma abs_phi_cont : Continuous fun p : ℝ × ℝ => |phi p.1 p.2| := by
  unfold phi
  fun_prop

lemma origin_in_open : origin ∈ openDisk origin rad2 := by
  simp [openDisk, origin, rad2]

lemma peak_in_open : peak ∈ openDisk peak rad2 := by
  simp [openDisk, peak, rad2]

lemma gap_max : ∃ M : ℝ, 0 ≤ M ∧ M < 1 ∧ ∀ p ∈ gap, |phi p.1 p.2| ≤ M := by
  obtain ⟨q, hq, hmax⟩ :=
    gap_compact.exists_isMaxOn gap_nonempty abs_phi_cont.continuousOn
  refine ⟨|phi q.1 q.2|, abs_nonneg _, ?_, fun p hp => (isMaxOn_iff.mp hmax) p hp⟩
  have hle : |phi q.1 q.2| ≤ 1 := abs_phi_le_one _ _
  by_contra hge
  push Not at hge
  have heq : |phi q.1 q.2| = 1 := le_antisymm hle hge
  rcases abs_phi_one_mem hq.1 heq with h | h
  · exact hq.2 (Or.inl (by simpa [← h] using origin_in_open))
  · exact hq.2 (Or.inr (by simpa [← h] using peak_in_open))

lemma disk_closed (c : ℝ × ℝ) (r : ℝ) : IsClosed (disk c r) := by
  unfold disk
  exact isClosed_le (by fun_prop) continuous_const

lemma disk_measurable (c : ℝ × ℝ) (r : ℝ) : MeasurableSet (disk c r) :=
  (disk_closed c r).measurableSet

lemma disk0_compact : IsCompact (disk origin rad2) :=
  IsCompact.of_isClosed_subset (isCompact_Icc.prod isCompact_Icc) (disk_closed origin rad2)
    (fun _ hp => origin_disk_subset hp)

lemma diskπ_compact : IsCompact (disk peak rad2) :=
  IsCompact.of_isClosed_subset (isCompact_Icc.prod isCompact_Icc) (disk_closed peak rad2)
    (fun _ hp => peak_disk_subset hp)

lemma disk_translate (n : ℕ) :
    ∫ p in disk peak rad2, (phi p.1 p.2) ^ (2 * n) =
      ∫ p in disk origin rad2, (phi p.1 p.2) ^ (2 * n) := by
  let f : ℝ × ℝ → ℝ × ℝ := fun p => p + peak
  have hembed : MeasurableEmbedding f :=
    (Homeomorph.addRight peak).isClosedEmbedding.measurableEmbedding
  have hmap : Measure.map f volume = volume := map_add_right_eq_self volume peak
  have hpre : f ⁻¹' disk peak rad2 = disk origin rad2 := by
    ext p
    simp only [f, Set.mem_preimage, disk]
    rw [Set.mem_ofPred, Set.mem_ofPred]
    simp [origin, peak, Prod.fst_add, Prod.snd_add, add_sub_cancel_right, sub_zero]
  rw [← hmap, hembed.setIntegral_map (fun p => (phi p.1 p.2) ^ (2 * n)) (disk peak rad2),
    hpre, hmap]
  refine setIntegral_congr_fun (disk_measurable origin rad2) ?_
  intro p _
  simp only [f]
  rw [Prod.fst_add, Prod.snd_add, peak, phi_add_pi, neg_pow_two_mul]

def rem : Set (ℝ × ℝ) := sqSet \ (disk origin rad2 ∪ disk peak rad2)

lemma rem_subset_gap : rem ⊆ gap := by
  intro p hp
  refine ⟨hp.1, ?_⟩
  intro hopen
  apply hp.2
  rcases hopen with h | h
  · have hlt : (p.1 - origin.1) ^ 2 + (p.2 - origin.2) ^ 2 < rad2 := by
      simpa [openDisk, origin] using h
    exact Or.inl (by simpa [disk, origin] using hlt.le)
  · have hlt : (p.1 - peak.1) ^ 2 + (p.2 - peak.2) ^ 2 < rad2 := by
      simpa [openDisk, peak] using h
    exact Or.inr (by simpa [disk, peak] using hlt.le)

lemma rem_measurable : MeasurableSet rem :=
  (measurableSet_Icc.prod measurableSet_Icc).diff
    ((disk_measurable origin rad2).union (disk_measurable peak rad2))

lemma rem_finite : volume rem < ⊤ := by
  have hsq : volume sqSet < ⊤ := by
    simpa [sqSet] using (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  exact lt_of_le_of_lt (measure_mono (fun _ hp => hp.1)) hsq

lemma cover : disk origin rad2 ∪ disk peak rad2 ∪ rem = sqSet := by
  ext p
  constructor
  · intro h
    rcases h with h | h
    · rcases h with h | h
      · exact origin_disk_subset h
      · exact peak_disk_subset h
    · exact h.1
  · intro hp
    by_cases h : p ∈ disk origin rad2 ∪ disk peak rad2
    · exact Or.inl h
    · exact Or.inr ⟨hp, h⟩

lemma box_decompose (n : ℕ) :
    box n =
      (2 * (∫ p in disk origin rad2, (phi p.1 p.2) ^ (2 * n))) +
        (∫ p in rem, (phi p.1 p.2) ^ (2 * n)) := by
  rw [box_shift, box_set]
  have hsq := integrable_sq n
  have h0 := hsq.mono_set origin_disk_subset
  have hπ := hsq.mono_set peak_disk_subset
  have hunion : disk origin rad2 ∪ disk peak rad2 ⊆ sqSet :=
    union_subset origin_disk_subset peak_disk_subset
  have hu := hsq.mono_set hunion
  have hremi : IntegrableOn (fun p => (phi p.1 p.2) ^ (2 * n)) rem :=
    hsq.mono_set (fun _ hp => hp.1)
  have hdisj : Disjoint (disk origin rad2 ∪ disk peak rad2) rem := by
    simpa [rem] using
      (disjoint_sdiff_right : Disjoint (disk origin rad2 ∪ disk peak rad2)
        (sqSet \ (disk origin rad2 ∪ disk peak rad2)))
  have heq := setIntegral_union hdisj rem_measurable hu hremi
  rw [cover] at heq
  have heq2 := setIntegral_union disks_disjoint (disk_measurable peak rad2) h0 hπ
  rw [heq2, disk_translate n] at heq
  rw [heq, ← two_mul]

lemma sq_div (u v : ℝ) (n : ℕ) :
    (u / Real.sqrt (n : ℝ)) ^ 2 + (v / Real.sqrt (n : ℝ)) ^ 2 =
      (u ^ 2 + v ^ 2) / (n : ℝ) := by
  rw [div_pow, div_pow, ← add_div, Real.sq_sqrt (Nat.cast_nonneg n)]

def scaled (n : ℕ) (p : ℝ × ℝ) : ℝ :=
  if p.1 ^ 2 + p.2 ^ 2 ≤ (n : ℝ) * rad2 then
    (phi (p.1 / Real.sqrt (n : ℝ)) (p.2 / Real.sqrt (n : ℝ))) ^ (2 * n)
  else
    0

lemma scaled_of_le {n : ℕ} {p : ℝ × ℝ} (h : p.1 ^ 2 + p.2 ^ 2 ≤ (n : ℝ) * rad2) :
    scaled n p =
      (phi (p.1 / Real.sqrt (n : ℝ)) (p.2 / Real.sqrt (n : ℝ))) ^ (2 * n) := by
  simp [scaled, h]

lemma scaled_of_gt {n : ℕ} {p : ℝ × ℝ} (h : ¬ p.1 ^ 2 + p.2 ^ 2 ≤ (n : ℝ) * rad2) :
    scaled n p = 0 := by
  simp [scaled, h]

lemma scaled_pull (n : ℕ) (hn : 1 ≤ n) (p : ℝ × ℝ) :
    scaled n p =
      (disk origin rad2).indicator (fun q => (phi q.1 q.2) ^ (2 * n))
        ((Real.sqrt (n : ℝ))⁻¹ • p) := by
  set R : ℝ := Real.sqrt (n : ℝ)
  have hn0 : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hR2 : R ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have h1 : (R⁻¹ • p).1 = R⁻¹ * p.1 := by simp [smul_eq_mul]
  have h2 : (R⁻¹ • p).2 = R⁻¹ * p.2 := by simp [smul_eq_mul]
  have hsq : (R⁻¹ • p).1 ^ 2 + (R⁻¹ • p).2 ^ 2 =
      (p.1 ^ 2 + p.2 ^ 2) / (n : ℝ) := by
    rw [h1, h2]
    calc (R⁻¹ * p.1) ^ 2 + (R⁻¹ * p.2) ^ 2
        = (p.1 ^ 2 + p.2 ^ 2) * (R ^ 2)⁻¹ := by ring_nf
      _ = (p.1 ^ 2 + p.2 ^ 2) / (n : ℝ) := by rw [hR2, div_eq_mul_inv]
  have hiff : R⁻¹ • p ∈ disk origin rad2 ↔ p.1 ^ 2 + p.2 ^ 2 ≤ (n : ℝ) * rad2 := by
    simp only [disk, origin, Set.mem_ofPred_eq, sub_zero, hsq]
    exact div_le_iff₀' hn0
  have hphi : phi (R⁻¹ • p).1 (R⁻¹ • p).2 = phi (p.1 / R) (p.2 / R) := by
    rw [h1, h2, inv_mul_eq_div, inv_mul_eq_div]
  by_cases hs : p.1 ^ 2 + p.2 ^ 2 ≤ (n : ℝ) * rad2
  · rw [scaled_of_le hs, Set.indicator_of_mem (hiff.mpr hs), hphi]
  · rw [scaled_of_gt hs, Set.indicator_of_notMem ((hiff.not).mpr hs)]

lemma integral_scaled (n : ℕ) (hn : 1 ≤ n) :
    ∫ p, scaled n p =
      (n : ℝ) * ∫ p in disk origin rad2, (phi p.1 p.2) ^ (2 * n) := by
  set R : ℝ := Real.sqrt (n : ℝ)
  let f : ℝ × ℝ → ℝ :=
    (disk origin rad2).indicator (fun q => (phi q.1 q.2) ^ (2 * n))
  have hrank : Module.finrank ℝ (ℝ × ℝ) = 2 := by
    simp [Module.finrank_prod, Module.finrank_self]
  have hR2 : R ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have hscale :=
    Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (ℝ × ℝ)) f
      (Real.sqrt_nonneg (n : ℝ))
  rw [hrank, hR2, smul_eq_mul] at hscale
  have hind : ∫ p, f p = ∫ p in disk origin rad2, (phi p.1 p.2) ^ (2 * n) := by
    simpa [f] using
      integral_indicator (disk_measurable origin rad2)
        (f := fun q => (phi q.1 q.2) ^ (2 * n))
  have hpull : (fun p => f (R⁻¹ • p)) = scaled n := by
    ext p
    simpa [f, R] using (scaled_pull n hn p).symm
  calc ∫ p, scaled n p = ∫ p, f (R⁻¹ • p) := by
        refine integral_congr_ae ?_
        filter_upwards with p
        exact (congr_fun hpull p).symm
    _ = (n : ℝ) * ∫ p, f p := hscale
    _ = (n : ℝ) * ∫ p in disk origin rad2, (phi p.1 p.2) ^ (2 * n) := by rw [hind]

lemma tendsto_phase (u v : ℝ) :
    Tendsto (fun n : ℕ =>
        (n : ℝ) * (phi (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ)) - 1))
      atTop (nhds (-(25 / 4) * (u ^ 2 + v ^ 2))) := by
  set s : ℝ := u ^ 2 + v ^ 2
  have herr (n : ℕ) :
      |phi (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ)) -
          (1 - (25 / 4) * (s / (n : ℝ)))| ≤
        32 * (s / (n : ℝ)) ^ 2 := by
    simpa [sq_div u v n, s] using
      phi_taylor (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ))
  have hclose (n : ℕ) (hn : n ≠ 0) :
      |(n : ℝ) * (phi (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ)) - 1) +
          (25 / 4) * s| ≤
        32 * s ^ 2 / (n : ℝ) := by
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have halg (z : ℝ) :
        (n : ℝ) * (z - 1) + (25 / 4) * s =
          (n : ℝ) * (z - (1 - (25 / 4) * (s / (n : ℝ)))) := by
      field_simp [hn0]
      ring
    set z : ℝ := phi (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ))
    calc |(n : ℝ) * (z - 1) + (25 / 4) * s|
        = |(n : ℝ) * (z - (1 - (25 / 4) * (s / (n : ℝ))))| := by rw [halg z]
      _ = (n : ℝ) * |z - (1 - (25 / 4) * (s / (n : ℝ)))| := by
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
      _ ≤ (n : ℝ) * (32 * (s / (n : ℝ)) ^ 2) := by
          gcongr
          simpa [z] using herr n
      _ = 32 * s ^ 2 / (n : ℝ) := by field_simp [hn0]
  have hzero : Tendsto (fun n : ℕ => 32 * s ^ 2 / (n : ℝ)) atTop (nhds 0) := by
    have h := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (32 * s ^ 2)
    simpa [div_eq_mul_inv, mul_zero] using h
  have hdiff : Tendsto (fun n : ℕ =>
      (n : ℝ) * (phi (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ)) - 1) +
        (25 / 4) * s) atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ hzero
    filter_upwards [eventually_ne_atTop 0] with n hn
    rw [Real.norm_eq_abs]
    exact hclose n hn
  have hsub := hdiff.sub_const ((25 / 4) * s)
  simpa [add_sub_cancel_right] using hsub

lemma tendsto_scaled_at (p : ℝ × ℝ) :
    Tendsto (fun n => scaled n p) atTop
      (nhds (Real.exp (-(25 / 2) * (p.1 ^ 2 + p.2 ^ 2)))) := by
  set s : ℝ := p.1 ^ 2 + p.2 ^ 2
  let g : ℕ → ℝ := fun n =>
    if n = 0 then 0 else
      phi (p.1 / Real.sqrt (n : ℝ)) (p.2 / Real.sqrt (n : ℝ)) - 1
  have hg : Tendsto (fun n : ℕ => (n : ℝ) * g n) atTop (nhds (-(25 / 4) * s)) := by
    refine Tendsto.congr' ?_ (tendsto_phase p.1 p.2)
    filter_upwards [eventually_ne_atTop 0] with n hn
    unfold g
    rw [if_neg hn]
  have hpow := Real.tendsto_one_add_pow_exp_of_tendsto hg
  have hexp : Real.exp (-(25 / 4) * s) * Real.exp (-(25 / 4) * s) =
      Real.exp (-(25 / 2) * s) := by
    rw [← Real.exp_add]
    ring_nf
  have hsq : Tendsto (fun n => ((1 + g n) ^ n) ^ 2) atTop
      (nhds (Real.exp (-(25 / 2) * s))) := by
    have hmul := hpow.mul hpow
    rw [hexp] at hmul
    simpa [← pow_two] using hmul
  refine Tendsto.congr' ?_ hsq
  have hrad : (0 : ℝ) < rad2 := by
    unfold rad2
    norm_num
  filter_upwards [eventually_ne_atTop 0, eventually_gt_atTop (Nat.ceil (s / rad2))] with n hn hgt
  have hsle : s ≤ (n : ℝ) * rad2 := by
    simpa [mul_comm] using ((div_lt_iff₀' hrad).mp (Nat.lt_of_ceil_lt hgt)).le
  have hg1 : 1 + g n = phi (p.1 / Real.sqrt (n : ℝ)) (p.2 / Real.sqrt (n : ℝ)) := by
    simp [g, show n ≠ 0 from hn]
  rw [scaled_of_le (by simpa [s] using hsle), ← hg1]
  rw [show 2 * n = n * 2 by omega, pow_mul]

lemma scaled_nonneg (n : ℕ) (p : ℝ × ℝ) : 0 ≤ scaled n p := by
  by_cases h : p.1 ^ 2 + p.2 ^ 2 ≤ (n : ℝ) * rad2
  · rw [scaled_of_le h, Nat.mul_comm, pow_mul]
    exact sq_nonneg _
  · rw [scaled_of_gt h]

lemma scaled_le (n : ℕ) (p : ℝ × ℝ) :
    ‖scaled n p‖ ≤ Real.exp (-(17 / 2) * (p.1 ^ 2 + p.2 ^ 2)) := by
  rw [Real.norm_eq_abs, abs_of_nonneg (scaled_nonneg n p)]
  by_cases h : p.1 ^ 2 + p.2 ^ 2 ≤ (n : ℝ) * rad2
  · rw [scaled_of_le h]
    by_cases hn : n = 0
    · subst hn
      have hs0 : p.1 ^ 2 + p.2 ^ 2 = 0 := by
        simp only [Nat.cast_zero, zero_mul] at h
        nlinarith [sq_nonneg p.1, sq_nonneg p.2, h]
      have hp1 : p.1 = 0 := by nlinarith [sq_nonneg p.1, hs0]
      have hp2 : p.2 = 0 := by nlinarith [sq_nonneg p.2, hs0]
      simp [hp1, hp2, phi_zero, Real.exp_zero]
    · have hn0 : (0 : ℝ) < n := by
        have : 0 < n := Nat.pos_of_ne_zero hn
        exact_mod_cast this
      have hρ : (p.1 / Real.sqrt (n : ℝ)) ^ 2 + (p.2 / Real.sqrt (n : ℝ)) ^ 2 ≤ rad2 := by
        rw [sq_div]
        exact (div_le_iff₀' hn0).mpr h
      have hb := phi_bounds_small hρ
      have hnn : 0 ≤ phi (p.1 / Real.sqrt (n : ℝ)) (p.2 / Real.sqrt (n : ℝ)) := by
        linarith [hb.1]
      have hpow := pow_le_pow_left₀ hnn hb.2 (2 * n)
      rw [← Real.exp_nat_mul] at hpow
      refine hpow.trans ?_
      apply Real.exp_le_exp.mpr
      apply le_of_eq
      rw [sq_div]
      push_cast
      field_simp [hn0.ne']
      ring
  · rw [scaled_of_gt h]
    exact (Real.exp_pos _).le

lemma measurable_scaled (n : ℕ) : Measurable (scaled n) := by
  have hs : MeasurableSet {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ (n : ℝ) * rad2} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  have hf : Measurable (fun p : ℝ × ℝ =>
      (phi (p.1 / Real.sqrt (n : ℝ)) (p.2 / Real.sqrt (n : ℝ))) ^ (2 * n)) := by
    unfold phi
    fun_prop
  unfold scaled
  exact Measurable.ite hs hf measurable_const

lemma integrable_gauss (c : ℝ) (hc : 0 < c) :
    Integrable (fun p : ℝ × ℝ => Real.exp (-c * (p.1 ^ 2 + p.2 ^ 2))) := by
  have hg : Integrable (fun x : ℝ => Real.exp (-c * x ^ 2)) := integrable_exp_neg_mul_sq hc
  have heq : (fun p : ℝ × ℝ => Real.exp (-c * (p.1 ^ 2 + p.2 ^ 2))) =
      fun p => Real.exp (-c * p.1 ^ 2) * Real.exp (-c * p.2 ^ 2) := by
    ext p
    rw [← Real.exp_add]
    ring_nf
  rw [heq, Measure.volume_eq_prod]
  exact hg.mul_prod hg

lemma gauss_integral :
    ∫ p : ℝ × ℝ, Real.exp (-(25 / 2) * (p.1 ^ 2 + p.2 ^ 2)) = 2 * Real.pi / 25 := by
  have heq : (fun p : ℝ × ℝ => Real.exp (-(25 / 2) * (p.1 ^ 2 + p.2 ^ 2))) =
      fun p => Real.exp (-(25 / 2) * p.1 ^ 2) * Real.exp (-(25 / 2) * p.2 ^ 2) := by
    ext p
    rw [← Real.exp_add]
    ring_nf
  rw [heq, Measure.volume_eq_prod]
  rw [integral_prod_mul (fun x : ℝ => Real.exp (-(25 / 2) * x ^ 2))
    (fun x : ℝ => Real.exp (-(25 / 2) * x ^ 2))]
  have hgauss := integral_gaussian (25 / 2)
  simp_rw [hgauss]
  have hnn : 0 ≤ Real.pi / (25 / 2) := by positivity
  rw [← pow_two, Real.sq_sqrt hnn]
  field_simp

lemma tendsto_integral_scaled :
    Tendsto (fun n => ∫ p, scaled n p) atTop (nhds (2 * Real.pi / 25)) := by
  have h := tendsto_integral_of_dominated_convergence
    (fun p : ℝ × ℝ => Real.exp (-(17 / 2) * (p.1 ^ 2 + p.2 ^ 2)))
    (fun n => (measurable_scaled n).aestronglyMeasurable)
    (integrable_gauss (17 / 2) (by norm_num))
    (fun n => ae_of_all _ (fun p => scaled_le n p))
    (ae_of_all _ tendsto_scaled_at)
  have hassoc : (fun p : ℝ × ℝ => Real.exp (-(25 / 2 * (p.1 ^ 2 + p.2 ^ 2)))) =
      fun p => Real.exp (-(25 / 2) * (p.1 ^ 2 + p.2 ^ 2)) := by
    ext p
    ring_nf
  simpa [hassoc, gauss_integral] using h

lemma rem_tendsto_zero (M : ℝ) (hM0 : 0 ≤ M) (hM1 : M < 1)
    (hbound : ∀ p ∈ gap, |phi p.1 p.2| ≤ M) :
    Tendsto (fun n : ℕ => (n : ℝ) * ∫ p in rem, (phi p.1 p.2) ^ (2 * n)) atTop (nhds 0) := by
  have hμ : volume rem < ⊤ := rem_finite
  have hnorm (n : ℕ) :
      ‖∫ p in rem, (phi p.1 p.2) ^ (2 * n)‖ ≤ (M ^ 2) ^ n * volume.real rem := by
    refine norm_setIntegral_le_of_norm_le_const (μ := volume) hμ ?_
    intro p hp
    have habs : |phi p.1 p.2| ≤ M := hbound p (rem_subset_gap hp)
    rw [Real.norm_eq_abs, abs_pow]
    calc |phi p.1 p.2| ^ (2 * n) ≤ M ^ (2 * n) :=
          pow_le_pow_left₀ (abs_nonneg _) habs _
      _ = (M ^ 2) ^ n := by rw [pow_mul]
  refine squeeze_zero_norm'
      (a := fun n : ℕ => volume.real rem * ((n : ℝ) * (M ^ 2) ^ n)) ?_ ?_
  · filter_upwards with n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
    calc (n : ℝ) * ‖∫ p in rem, (phi p.1 p.2) ^ (2 * n)‖
        ≤ (n : ℝ) * ((M ^ 2) ^ n * volume.real rem) := by
          gcongr
          exact hnorm n
      _ = volume.real rem * ((n : ℝ) * (M ^ 2) ^ n) := by ring
  · have hr0 : 0 ≤ M ^ 2 := by positivity
    have hr1 : M ^ 2 < 1 := by nlinarith
    have h := (tendsto_self_mul_const_pow_of_lt_one hr0 hr1).const_mul (volume.real rem)
    simpa [mul_zero, mul_left_comm, mul_comm] using h

lemma n_box_eq (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * box n =
      (2 * (∫ p, scaled n p)) +
        ((n : ℝ) * (∫ p in rem, (phi p.1 p.2) ^ (2 * n))) := by
  rw [box_decompose]
  have hsc := integral_scaled n hn
  rw [mul_add, mul_left_comm, ← hsc]

lemma tendsto_n_box :
    Tendsto (fun n : ℕ => (n : ℝ) * box n) atTop (nhds (4 * Real.pi / 25)) := by
  obtain ⟨M, hM0, hM1, hM⟩ := gap_max
  have hrem := rem_tendsto_zero M hM0 hM1 hM
  have htwo := tendsto_integral_scaled.const_mul 2
  have hsum := htwo.add hrem
  have hpt : 2 * (2 * Real.pi / 25) + 0 = 4 * Real.pi / 25 := by ring
  rw [hpt] at hsum
  refine Tendsto.congr' ?_ hsum
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (n_box_eq n hn).symm

lemma ratio_eq (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℝ) / ((64 : ℝ) ^ n / (25 * Real.pi * (n : ℝ))) =
      (n : ℝ) * box n * 25 / (4 * Real.pi) := by
  rw [a_eq_box]
  have h64 : (64 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hn0 : (n : ℝ) ≠ 0 := by
    have : n ≠ 0 := by omega
    exact_mod_cast this
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [h64, hn0, hpi]

lemma tendsto_ratio :
    Tendsto (fun n : ℕ => (n : ℝ) * box n * 25 / (4 * Real.pi)) atTop (nhds 1) := by
  have h := tendsto_n_box.mul (tendsto_const_nhds (x := 25 / (4 * Real.pi)))
  have hpt : (4 * Real.pi / 25) * (25 / (4 * Real.pi)) = 1 := by
    field_simp
  have hfun : ∀ n : ℕ, (n : ℝ) * box n * (25 / (4 * Real.pi)) =
      (n : ℝ) * box n * 25 / (4 * Real.pi) := by
    intro n
    ring_nf
  have h' := Tendsto.congr hfun h
  rw [hpt] at h'
  exact h'

lemma tendsto_main :
    Filter.Tendsto
      (fun n : ℕ => (a n : ℝ) / ((64 : ℝ) ^ n / (25 * Real.pi * (n : ℝ))))
      Filter.atTop (nhds 1) := by
  refine Tendsto.congr' ?_ tendsto_ratio
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (ratio_eq n hn).symm

end OMA_A307347_Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a307347.main := by
  exact OMA_A307347_Proof.tendsto_main

end
