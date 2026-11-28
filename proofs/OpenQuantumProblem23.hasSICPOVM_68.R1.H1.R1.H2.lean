import OMAReductions.R_OpenQuantumProblem23_hasSICPOVM_68_R1_H1_R1
import Mathlib

/-!
# Dimension-68 reflection and twisted convolution

The pentagon equation gives a Fourier identity for its convolution kernel.
Reflection follows by Fourier inversion. Averaging over the subgroup annihilator
and using the order-three symmetry yields the twisted convolution on the subgroup.

Adapted from Yaoling Yang's SICLean, WHBasic, L2a and L2b, under Apache-2.0,
commit e74571352233162adee70895903d82f8465fd054.
-/
noncomputable section
open scoped BigOperators

namespace SICLean

def omega (d : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / d)
variable {d : ℕ}
theorem omega_pow_d_of_ne_zero (d : ℕ) (hd : d ≠ 0) : omega d ^ (d : ℕ) = 1 := by
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  simp only [omega]
  rw [← Complex.exp_nat_mul, mul_comm, div_mul_cancel₀ _ hd']
  exact Complex.exp_two_pi_mul_I

theorem omega_zpow_dvd (d : ℕ) {z : ℤ} (h : (d : ℤ) ∣ z) : omega d ^ z = 1 := by
  by_cases hd : d = 0
  · subst hd
    have h1 : omega 0 = 1 := by
      rw [omega]
      simp
    rw [h1, _root_.one_zpow]
  · obtain ⟨c, hc⟩ := h
    rw [hc, _root_.zpow_mul, zpow_natCast, omega_pow_d_of_ne_zero d hd, _root_.one_zpow]


theorem omega_exp (d : ℕ) (z : ℤ) :
    omega d ^ z = Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (d : ℂ)) := by
  cases z with
  | ofNat n =>
      show omega d ^ ((n : ℕ) : ℤ) = Complex.exp (2 * ↑Real.pi * Complex.I * ((n : ℕ) : ℂ) / ↑d)
      rw [zpow_natCast]
      simp only [omega]
      rw [← Complex.exp_nat_mul]
      congr 1
      ring
  | negSucc n =>
      rw [zpow_negSucc]
      simp only [omega]
      rw [← Complex.exp_nat_mul, ← Complex.exp_neg]
      congr 1
      push_cast
      ring


theorem omega_ne_one_of_not_dvd [NeZero d] {a : ℤ} (ha : ¬ (d : ℤ) ∣ a) : omega d ^ a ≠ 1 := by
  intro h
  apply ha
  have h1 : Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (d : ℂ)) = 1 := by
    rw [← omega_exp d a, h]
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h1
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  have h2c : (2 : ℂ) ≠ 0 := by norm_num
  have hπ : ((Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero h2c hπ) Complex.I_ne_zero
  have h2 : (2 * Real.pi * Complex.I : ℂ) * (a : ℂ)
      = (2 * Real.pi * Complex.I : ℂ) * ((k : ℂ) * (d : ℂ)) := by
    have h3 := (div_eq_iff hd0).mp hk
    linear_combination h3
  have h4 : (a : ℂ) = ((k * (d : ℕ) : ℤ) : ℂ) := by
    have := mul_left_cancel₀ hpi h2
    push_cast

    linear_combination this
  exact ⟨k, (Int.cast_injective h4).trans (mul_comm _ _)⟩

theorem omega_ne_zero (d : ℕ) : omega d ≠ 0 := by
  show Complex.exp _ ≠ 0
  exact Complex.exp_ne_zero _

end SICLean

namespace SICLean.L2a

abbrev Index (M : ℕ) := ZMod M × ZMod M

/- The M² values F(i,j) = F_γ((i ε + j)/M). -/
abbrev Values (M : ℕ) := Index M → ℂ

/- Evaluate a residue-indexed value at an integer lift. -/
def valueAt {M : ℕ} (F : Values M) (i j : ℤ) : ℂ := F (i, j)

/- The attracting unit of α, not the unit ε³ of γ = α³. -/
def epsilon (M : ℕ) : ℝ :=
  ((M : ℝ) - 1 + Real.sqrt (((M : ℝ) - 1) ^ 2 - 4)) / 2

/- Positive √ε, embedded in ℂ. -/
def sqrtEpsilon (M : ℕ) : ℂ := (Real.sqrt (epsilon M) : ℂ)

/- The projector denominator √ε + ε^(-1/2). -/
def denominator (M : ℕ) : ℂ := sqrtEpsilon M + (sqrtEpsilon M)⁻¹

/- The coefficient √(M-3) in the identity of [RW26]. -/
def convolutionScalar (M : ℕ) : ℂ := (Real.sqrt ((M : ℝ) - 3) : ℂ)

/- e_M(n) = exp(2πin/M), with integer exponent. -/
def e (M : ℕ) (n : ℤ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) / (M : ℂ))

/- The quadratic form in the H-Gaussian. -/
def quadraticForm (i j : ℤ) : ℤ := i ^ 2 - i * j + j ^ 2

/- Explicit Gaussian on integer lifts of H. -/
def gaussianLift (M : ℕ) (i j : ℤ) : ℂ := e M (quadraticForm i j)

/- The same Gaussian as a function on H, using least nonnegative representatives. -/
def gaussian (M : ℕ) (h : Index M) : ℂ :=
  gaussianLift M h.1.val h.2.val

/- The restricted pairing ⟨h;k⟩. It is allowed to be degenerate on H. -/
def pairing (M : ℕ) (h k : Index M) : ℂ :=
  gaussian M (h + k) / (gaussian M h * gaussian M k)


def convolution (M : ℕ) (F : Values M) (r s : ℤ) : ℂ :=
  (M : ℂ)⁻¹ * ∑ i : Fin M, ∑ j : Fin M,
    valueAt F i j * valueAt F (r - i) (s - j) * gaussianLift M i j *
      e M (-(i : ℤ) * r + (j : ℤ) * (r - s))
theorem e_eq_omega_zpow (M : ℕ) (n : ℤ) : e M n = omega M ^ n := by
  rw [e, omega_exp]

/- Phases agree when the exponents are congruent modulo `M`. -/
theorem e_eq_of_dvd {M : ℕ} {n n' : ℤ} (h : ((M : ℕ) : ℤ) ∣ n - n') : e M n = e M n' := by
  by_cases hM : M = 0
  · subst hM
    have hn : n = n' := sub_eq_zero.mp (Int.zero_dvd.mp h)
    rw [hn]
  · rw [e_eq_omega_zpow, e_eq_omega_zpow]
    obtain ⟨q, hq⟩ := h
    have hn : n = n' + ((M : ℕ) : ℤ) * q := by linear_combination hq
    rw [hn, zpow_add₀ (omega_ne_zero M), _root_.zpow_mul, zpow_natCast,
      omega_pow_d_of_ne_zero M hM, _root_.one_zpow, mul_one]


theorem e_mul (M : ℕ) (n n' : ℤ) : e M n * e M n' = e M (n + n') := by
  rw [e_eq_omega_zpow, e_eq_omega_zpow, e_eq_omega_zpow, ← zpow_add₀ (omega_ne_zero M)]

theorem e_inv (M : ℕ) (n : ℤ) : (e M n)⁻¹ = e M (-n) := by
  rw [e_eq_omega_zpow, e_eq_omega_zpow, ← _root_.zpow_neg]


end SICLean.L2a

namespace SICLean.L2b


variable {A : Type*} [AddCommGroup A]

local instance MetricDecEq : DecidableEq A := Classical.decEq A

/- Polarization of a Gaussian, not a separately chosen bicharacter. -/
def metricPairing (q : A → ℂ) (x y : A) : ℂ :=
  q (x + y) / (q x * q y)

/- [RW26, Def. 1]. These hypotheses belong to the general abstract theorem.
For the concrete group below every field is a theorem, never an input on E. -/
structure IsMetricGaussian (q : A → ℂ) : Prop where
  nonzero : ∀ x, q x ≠ 0
  even : ∀ x, q (-x) = q x
  add_left : ∀ x y z,
    metricPairing q (x + y) z = metricPairing q x z * metricPairing q y z
  add_right : ∀ x y z,
    metricPairing q x (y + z) = metricPairing q x y * metricPairing q x z
  nondegenerate : ∀ x, (∀ y, metricPairing q x y = 1) → x = 0

/- The ℂˣ-valued version of the same Gaussian, with no extra data. -/
def gaussianUnits {q : A → ℂ} (hq : IsMetricGaussian q) (x : A) : ℂˣ :=
  Units.mk0 (q x) (hq.nonzero x)

theorem metric_zero {q : A → ℂ} (hq : IsMetricGaussian q) : q 0 = 1 := by
  have hp := hq.add_right 0 0 0
  simp only [add_zero] at hp
  have hv : metricPairing q 0 0 = (q 0)⁻¹ := by
    simp only [metricPairing, add_zero]
    field_simp
  rw [hv] at hp
  have key : (q 0)⁻¹ * (1 - (q 0)⁻¹) = 0 := by
    have h : (q 0)⁻¹ * (1 - (q 0)⁻¹) = (q 0)⁻¹ - (q 0)⁻¹ * (q 0)⁻¹ := by ring
    rw [h, ← hp, sub_self]
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h (inv_ne_zero (hq.nonzero 0))
  · exact inv_eq_one.mp (sub_eq_zero.mp h).symm

theorem metric_pairing_symmetric (q : A → ℂ) (x y : A) :
    metricPairing q x y = metricPairing q y x := by
  simp only [metricPairing]
  rw [add_comm y x, mul_comm (q y) (q x)]

variable [Fintype A]

/- The positive real square root, embedded in ℂ. -/
def sqrtCard (A : Type*) [Fintype A] : ℂ :=
  (Real.sqrt (Fintype.card A) : ℂ)

/- The normalized counting integral of [RW26], with total mass √|A|. -/
def normalizedSum (f : A → ℂ) : ℂ :=
  (∑ x : A, f x) / sqrtCard A

/- The hat in [RW26] is F⁻¹: the character has the minus sign. -/
def fourier (q : A → ℂ) (f : A → ℂ) (y : A) : ℂ :=
  normalizedSum (fun x => f x * metricPairing q x (-y))

theorem sqrtCard_ne_zero : sqrtCard A ≠ 0 := by
  have h : (0 : ℝ) < Real.sqrt (Fintype.card A) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
  simp only [sqrtCard]
  exact Complex.ofReal_ne_zero.mpr h.ne'

theorem metric_norm {q : A → ℂ} (hq : IsMetricGaussian q) (x : A) :
    ‖q x‖ = 1 := by
  have h1 : q 0 = 1 := metric_zero hq
  have hchar : ∀ y : A, ∃ k : ℕ, 0 < k ∧ (metricPairing q x y) ^ k = 1 := by
    intro y
    have hz : metricPairing q x 0 = 1 := by
      simp only [metricPairing, add_zero, h1, mul_one]
      exact div_self (hq.nonzero x)
    have hpow : ∀ k : ℕ, metricPairing q x (k • y) = (metricPairing q x y) ^ k := by
      intro k
      induction k with
      | zero => simp only [zero_nsmul, pow_zero, hz]
      | succ k ih =>
        rw [succ_nsmul, hq.add_right x (k • y) y, ih, pow_succ]
    refine ⟨addOrderOf y, addOrderOf_pos y, ?_⟩
    rw [← hpow, addOrderOf_nsmul_eq_zero y, hz]
  have hnorm : ∀ y : A, ‖metricPairing q x y‖ = 1 := by
    intro y
    obtain ⟨k, hk, hval⟩ := hchar y
    have h2 : ‖metricPairing q x y‖ ^ k = 1 := by
      rw [← norm_pow, hval, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hk.ne').mp h2
  have key : metricPairing q x (-x) = 1 / (q x * q x) := by
    simp only [metricPairing, add_neg_cancel, hq.even x, h1]
  have hn := hnorm (-x)
  rw [key, norm_div, norm_one, one_div, inv_eq_one] at hn
  have h5 : ‖q x‖ ^ 2 = 1 := by
    have h7 : ‖q x‖ ^ 2 = ‖q x * q x‖ := by rw [← norm_pow, pow_two]
    rw [h7, hn]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp h5

theorem character_sum {q : A → ℂ} (hq : IsMetricGaussian q) (y : A) :
    (∑ x : A, metricPairing q x y) =
      if y = 0 then (Fintype.card A : ℂ) else 0 := by
  rcases eq_or_ne y 0 with rfl | hy
  · have hone : ∀ x : A, metricPairing q x 0 = 1 := by
      intro x
      simp only [metricPairing, add_zero, metric_zero hq, mul_one]
      exact div_self (hq.nonzero x)
    simp only [hone]
    rw [Finset.sum_const, Nat.smul_one_eq_cast, Finset.card_univ]
    simp
  · have hex : ∃ x₀ : A, metricPairing q x₀ y ≠ 1 := by
      by_contra hc
      push Not at hc
      exact hy (hq.nondegenerate y (fun z => by
        rw [metric_pairing_symmetric q y z, hc z]))
    obtain ⟨x₀, hx₀⟩ := hex
    have htr : ∑ x : A, metricPairing q (x + x₀) y = ∑ x : A, metricPairing q x y :=
      Fintype.sum_equiv (Equiv.addRight x₀) _ _ (fun _ => rfl)
    have hsplit : ∀ x : A,
        metricPairing q (x + x₀) y = metricPairing q x y * metricPairing q x₀ y :=
      fun x => hq.add_left x x₀ y
    have hcalc : (∑ x : A, metricPairing q x y) * metricPairing q x₀ y
        = ∑ x : A, metricPairing q x y := by
      calc (∑ x : A, metricPairing q x y) * metricPairing q x₀ y
          = ∑ x : A, metricPairing q x y * metricPairing q x₀ y :=
            Finset.sum_mul _ _ _
        _ = ∑ x : A, metricPairing q (x + x₀) y :=
            Finset.sum_congr rfl (fun x _ => (hsplit x).symm)
        _ = ∑ x : A, metricPairing q x y := htr
    rw [if_neg hy]
    have hS : (∑ x : A, metricPairing q x y) * (1 - metricPairing q x₀ y) = 0 := by
      have h : (∑ x : A, metricPairing q x y) * (1 - metricPairing q x₀ y)
          = (∑ x : A, metricPairing q x y) - (∑ x : A, metricPairing q x y) * metricPairing q x₀ y := by
        ring
      rw [h, hcalc, sub_self]
    have hne : (1 - metricPairing q x₀ y) ≠ 0 := sub_ne_zero.mpr hx₀.symm
    exact (mul_eq_zero.mp hS).resolve_right hne

theorem fourier_twice {q : A → ℂ} (hq : IsMetricGaussian q) (f : A → ℂ) (x : A) :
    fourier q (fourier q f) x = f (-x) := by
  have hN : sqrtCard A * sqrtCard A = (Fintype.card A : ℂ) := by
    rw [sqrtCard, ← Complex.ofReal_mul]
    exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg (Fintype.card A))
  have hN0 : (Fintype.card A : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.pos_iff_ne_zero.mp Fintype.card_pos)
  -- the polarization factor appearing after one round trip
  have key : ∀ y z : A,
      metricPairing q z (-y) * metricPairing q y (-x) = metricPairing q (z + x) (-y) := by
    intro y z
    have hnn : metricPairing q y (-x) = metricPairing q (-y) x := by
      simp only [metricPairing]
      rw [show -y + x = -(y + -x) from by rw [neg_add, neg_neg], hq.even (y + -x), hq.even y,
        hq.even x]
    rw [hnn, ← metric_pairing_symmetric q x (-y), hq.add_left z x (-y)]
  have hpull : ∀ (S : A → ℂ),
      (∑ y : A, (S y / sqrtCard A) * metricPairing q y (-x))
        = (∑ y : A, S y * metricPairing q y (-x)) / sqrtCard A := by
    intro S
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun y _ =>
      div_mul_eq_mul_div (S y) (sqrtCard A) (metricPairing q y (-x))
  have hswap : (∑ w : A, (∑ v : A, f v * metricPairing q v (-w)) * metricPairing q w (-x))
      = (∑ v : A, f v * (∑ w : A, metricPairing q v (-w) * metricPairing q w (-x))) := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, mul_assoc]
  have hin : ∀ v : A, (∑ w : A, metricPairing q v (-w) * metricPairing q w (-x))
      = if v + x = 0 then (Fintype.card A : ℂ) else 0 := by
    intro v
    have h1 : (∑ w : A, metricPairing q v (-w) * metricPairing q w (-x))
        = ∑ w : A, metricPairing q (-w) (v + x) :=
      Finset.sum_congr rfl fun w _ => (key w v).trans (metric_pairing_symmetric q (v + x) (-w))
    rw [h1, Fintype.sum_equiv (Equiv.neg A)
      (fun w => metricPairing q (-w) (v + x)) (fun w => metricPairing q w (v + x))
      (fun w => rfl)]
    exact character_sum hq (v + x)
  have hlast : (∑ v : A, f v * (if v + x = 0 then (Fintype.card A : ℂ) else 0))
      = f (-x) * (Fintype.card A : ℂ) := by
    rw [Finset.sum_eq_single_of_mem (-x) (Finset.mem_univ _)
      (fun b _ hb => by
        have hbn : ¬(b + x = 0) := fun h => hb (eq_neg_iff_add_eq_zero.mpr h)
        simp [hbn]),
      if_pos (neg_add_cancel x)]
  simp only [fourier, normalizedSum]
  rw [hpull (fun w => ∑ v : A, f v * metricPairing q v (-w)), div_div, hN, hswap]
  simp only [hin]
  rw [hlast, mul_div_cancel_right₀ _ hN0]

/- Groups of order at most four are excluded.
This is the assertion in [RW26, footnote 5]. -/
theorem gaussian_not_constant_off_zero {q : A → ℂ} (hq : IsMetricGaussian q)
    (hcard : 4 < Fintype.card A) :
    ¬ ∃ c : ℂ, ∀ x : A, x ≠ 0 → q x = c := by
  rintro ⟨c, hc⟩
  have hex : ∃ x : A, x ≠ 0 := by
    by_contra hall
    push Not at hall
    have h1 : Fintype.card A ≤ 1 :=
      Fintype.card_le_one_iff_subsingleton.mpr ⟨fun a b => by rw [hall a, hall b]⟩
    omega
  obtain ⟨x, hx⟩ := hex
  have hqx : q x = c := hc x hx
  have hc0 : c ≠ 0 := by rw [← hqx]; exact hq.nonzero x
  have hnorm : ‖c‖ = 1 := by
    rw [← hqx]
    exact metric_norm hq x
  have hsum : (∑ y : A, metricPairing q x y) = 0 := by
    rw [show (∑ y : A, metricPairing q x y) = (∑ y : A, metricPairing q y x) from
      Finset.sum_congr rfl fun y _ => metric_pairing_symmetric q x y,
      character_sum hq x, if_neg hx]
  have hb0 : metricPairing q x 0 = 1 := by
    simp only [metricPairing, add_zero, metric_zero hq, mul_one]
    exact div_self (hq.nonzero x)
  have hbx : metricPairing q x (-x) = 1 / (c * c) := by
    simp only [metricPairing, add_neg_cancel, hq.even x, metric_zero hq, hqx]
  have hrest : ∀ y : A, y ≠ 0 → y ≠ -x → metricPairing q x y = 1 / c := by
    intro y hy0 hyx
    have hxy : x + y ≠ 0 := by
      intro h
      exact hyx (eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact h))
    rw [metricPairing, hc x hx, hc y hy0, hc (x + y) hxy]
    field_simp
  have h0x : (0 : A) ∉ ({-(x : A)} : Finset A) := by
    simp only [Finset.mem_singleton]
    intro h
    exact hx (neg_eq_zero.mp h.symm)
  have hcardins : (insert (0 : A) {-(x : A)} : Finset A).card = 2 := by
    rw [Finset.card_insert_of_notMem h0x, Finset.card_singleton]
  have hcard2 : (Finset.univ \ (insert (0 : A) {-(x : A)} : Finset A)).card
      = Fintype.card A - 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), hcardins, Finset.card_univ]
  have hmem : ∀ y ∈ Finset.univ \ (insert (0 : A) {-(x : A)}), metricPairing q x y = 1 / c := by
    intro y hy
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or
      ] at hy
    exact hrest y hy.2.1 hy.2.2
  have hsumrest : (∑ y ∈ Finset.univ \ (insert (0 : A) {-(x : A)}), metricPairing q x y)
      = ((Fintype.card A - 2 : ℕ) : ℂ) * (1 / c) := by
    rw [Finset.sum_congr rfl (fun y hy => hmem y hy), Finset.sum_const, hcard2]

    ring
  rw [← Finset.sum_sdiff (Finset.subset_univ _), Finset.sum_insert h0x, Finset.sum_singleton,
    hb0, hbx, hsumrest] at hsum
  -- hsum : 1 + 1/(c*c) + ((card A - 2 : ℕ) : ℂ) * (1/c) = 0
  have hN2 : ((Fintype.card A - 2 : ℕ) : ℂ) = (Fintype.card A : ℂ) - 2 := by
    have h2 : 2 ≤ Fintype.card A := by omega
    rw [Nat.cast_sub h2, Nat.cast_ofNat]
  rw [hN2] at hsum
  have hkey : c + c⁻¹ = -((Fintype.card A : ℂ) - 2) := by
    rw [inv_eq_one_div]
    field_simp at hsum ⊢
    linear_combination hsum
  have habs : ‖c + c⁻¹‖ ≤ 2 := by
    have h1 : ‖c + c⁻¹‖ ≤ ‖c‖ + ‖c⁻¹‖ := norm_add_le _ _
    rw [norm_inv, hnorm, inv_one] at h1
    linarith
  have hval : ‖c + c⁻¹‖ = (Fintype.card A : ℝ) - 2 := by
    have h2 : ((Fintype.card A : ℕ) : ℂ) - 2 = (((Fintype.card A : ℝ) - 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hkey, norm_neg, h2, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by
        have : (2 : ℝ) ≤ Fintype.card A := by exact_mod_cast (by omega : 2 ≤ Fintype.card A)
        linarith)]
  rw [hval] at habs
  have h4 : (Fintype.card A : ℝ) ≤ 4 := by linarith
  have h5 : Fintype.card A ≤ 4 := by exact_mod_cast h4
  omega


end SICLean.L2b

namespace SICLean.L2b


variable {A : Type*} [AddCommGroup A] [Fintype A]

local instance FiniteQDDefsDecEq : DecidableEq A := Classical.decEq A

/- The function relation [RW26, (31)], including every term of the sum. -/
def Pentagon (q E : A → ℂ) (C : ℂ) : Prop :=
  ∀ x y : A,
    metricPairing q x y * E x * E y =
      C + normalizedSum (fun z => E (y - z) * E z * q z * E (x - z))

/- The E-dependent content of [RW26, Def. 4]. The ambient metric property and |A|>1
are supplied by the abstract theorem's context and proved for concrete G. -/
def IsFiniteQuantumDilogarithm (q E : A → ℂ) : Prop :=
  ∃ C : ℂ, C ≠ 0 ∧ Pentagon q E C

/- The convolution kernel used in the proof, immediately before (33). -/
def pentagonKernel (q E : A → ℂ) (x z : A) : ℂ :=
  E (x - z) * E z * q z

/- The scalar in [RW26, Thm. 5(iii)]. No root of unity or Gauss sum is assumed. -/
def fourierScalar (q E : A → ℂ) : ℂ := fourier q E 0 / E 0


end SICLean.L2b

namespace SICLean.L2b

variable {A : Type*} [AddCommGroup A] [Fintype A]
local instance finiteQDAuxDecidableEq : DecidableEq A := Classical.decEq A

omit [Fintype A] in
theorem aux_pairing_zero_left {q : A → ℂ} (hq : IsMetricGaussian q) (x : A) :
    metricPairing q 0 x = 1 := by
  simp [metricPairing, metric_zero hq, hq.nonzero x]

omit [Fintype A] in
theorem aux_pairing_zero_right {q : A → ℂ} (hq : IsMetricGaussian q) (x : A) :
    metricPairing q x 0 = 1 := by
  rw [metric_pairing_symmetric]
  exact aux_pairing_zero_left hq x

omit [AddCommGroup A] in
theorem aux_normalizedSum_add (f g : A → ℂ) :
    normalizedSum (fun x => f x + g x) = normalizedSum f + normalizedSum g := by
  simp [normalizedSum, Finset.sum_add_distrib, add_div]

omit [AddCommGroup A] in
theorem aux_normalizedSum_mul_left (c : ℂ) (f : A → ℂ) :
    normalizedSum (fun x => c * f x) = c * normalizedSum f := by
  simp only [normalizedSum, ← Finset.mul_sum, mul_div_assoc]

omit [AddCommGroup A] in
theorem aux_normalizedSum_mul_right (f : A → ℂ) (c : ℂ) :
    normalizedSum (fun x => f x * c) = normalizedSum f * c := by
  simp [normalizedSum, Finset.sum_mul, div_mul_eq_mul_div]

omit [AddCommGroup A] in
theorem aux_normalizedSum_swap (f : A → A → ℂ) :
    normalizedSum (fun x => normalizedSum (f x)) =
      normalizedSum (fun y => normalizedSum (fun x => f x y)) := by
  simp only [normalizedSum, Finset.sum_div]
  rw [Finset.sum_comm]

theorem aux_normalizedSum_translate (f : A → ℂ) (z : A) :
    normalizedSum (fun x => f (x + z)) = normalizedSum f := by
  unfold normalizedSum
  congr 1
  exact Equiv.sum_comp (Equiv.addRight z) f

theorem aux_fourier_add (q f g : A → ℂ) :
    fourier q (fun x => f x + g x) = fun y => fourier q f y + fourier q g y := by
  funext y
  simp only [fourier, add_mul, aux_normalizedSum_add]

theorem aux_fourier_mul_left (q : A → ℂ) (c : ℂ) (f : A → ℂ) :
    fourier q (fun x => c * f x) = fun y => c * fourier q f y := by
  funext y
  simp only [fourier, mul_assoc, aux_normalizedSum_mul_left]

theorem aux_fourier_delta {q : A → ℂ} (hq : IsMetricGaussian q) (c : ℂ) (y : A) :
    fourier q (fun x => if x = 0 then c else 0) y = c / sqrtCard A := by
  simp [fourier, normalizedSum, ite_mul, aux_pairing_zero_left hq]

theorem aux_fourier_constant {q : A → ℂ} (hq : IsMetricGaussian q) (c : ℂ) (y : A) :
    fourier q (fun _ => c) y =
      c * (Fintype.card A : ℂ) / sqrtCard A * (if y = 0 then 1 else 0) := by
  unfold fourier normalizedSum
  rw [← Finset.mul_sum, character_sum hq]
  by_cases hy : y = 0 <;> simp [hy]

theorem aux_fourier_convolution {q : A → ℂ} (hq : IsMetricGaussian q)
    (f g : A → ℂ) (y : A) :
    fourier q (fun x => normalizedSum (fun z => f (x - z) * g z)) y =
      fourier q f y * fourier q g y := by
  unfold fourier
  simp_rw [← aux_normalizedSum_mul_right]
  rw [aux_normalizedSum_swap]
  have h (z : A) :
      normalizedSum (fun x => f (x - z) * g z * metricPairing q x (-y)) =
        normalizedSum (fun x => f x * g z * metricPairing q (x + z) (-y)) := by
    rw [← aux_normalizedSum_translate
      (fun x => f (x - z) * g z * metricPairing q x (-y)) z]
    simp
  simp_rw [h, hq.add_left]
  have hh (z : A) :
      normalizedSum (fun x => f x * g z *
        (metricPairing q x (-y) * metricPairing q z (-y))) =
      normalizedSum (fun x => f x * metricPairing q x (-y)) *
        (g z * metricPairing q z (-y)) := by
    rw [← aux_normalizedSum_mul_right]
    congr 1
    funext x
    ring
  simp_rw [hh]
  conv_rhs => rw [aux_normalizedSum_mul_right]
  exact aux_normalizedSum_mul_left (normalizedSum (fun x => f x * metricPairing q x (-y)))
    (fun z => g z * metricPairing q z (-y))

/- If two functions agree away from zero, their Fourier transforms differ by a constant. -/
theorem aux_fourier_affine_of_off_zero {q f g : A → ℂ}
    (hq : IsMetricGaussian q) (c : ℂ)
    (h : ∀ x : A, x ≠ 0 → f x = c * g x) :
    ∃ b : ℂ, ∀ y : A, fourier q f y = c * fourier q g y + b := by
  refine ⟨(f 0 - c * g 0) / sqrtCard A, ?_⟩
  have hf : f = fun x => c * g x + if x = 0 then f 0 - c * g 0 else 0 := by
    funext x
    by_cases hx : x = 0
    · simp [hx]
    · simp [hx, h x hx]
  intro y
  conv_lhs => rw [hf]
  simp only [aux_fourier_add, aux_fourier_mul_left, aux_fourier_delta hq]
omit [Fintype A] in
theorem aux_pairing_neg_neg {q : A → ℂ} (hq : IsMetricGaussian q) (x y : A) :
    metricPairing q (-x) (-y) = metricPairing q x y := by
  simp only [metricPairing, ← neg_add, hq.even]

theorem aux_fourier_reflection {q : A → ℂ} (hq : IsMetricGaussian q)
    (f : A → ℂ) (y : A) :
    fourier q (fun x => f (-x)) y = fourier q f (-y) := by
  unfold fourier normalizedSum
  simp only [neg_neg]
  congr 1
  calc
    (∑ x : A, f (-x) * metricPairing q x (-y)) =
        ∑ x : A, f (-(-x)) * metricPairing q (-x) (-y) :=
      (Equiv.sum_comp (Equiv.neg A) (fun x => f (-x) * metricPairing q x (-y))).symm
    _ = ∑ x : A, f x * metricPairing q x y := by
      simp only [neg_neg, aux_pairing_neg_neg hq]

omit [AddCommGroup A] in
theorem aux_sqrtCard_sq : sqrtCard A ^ 2 = (Fintype.card A : ℂ) := by
  unfold sqrtCard
  rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  rfl


end SICLean.L2b

namespace SICLean.L2b


variable {A : Type*} [AddCommGroup A] [Fintype A]

local instance finiteQDCoreDecidableEq : DecidableEq A := Classical.decEq A

omit [Fintype A] in
theorem core_pairing_ne_zero {q : A → ℂ} (hq : IsMetricGaussian q) (x y : A) :
    metricPairing q x y ≠ 0 :=
  div_ne_zero (hq.nonzero _) (mul_ne_zero (hq.nonzero _) (hq.nonzero _))

omit [Fintype A] in
@[simp] theorem core_pairing_zero_left {q : A → ℂ} (hq : IsMetricGaussian q) (y : A) :
    metricPairing q 0 y = 1 := by
  simp [metricPairing, metric_zero hq, hq.nonzero y]

omit [Fintype A] in
@[simp] theorem core_pairing_zero_right {q : A → ℂ} (hq : IsMetricGaussian q) (x : A) :
    metricPairing q x 0 = 1 := by
  simp [metricPairing, metric_zero hq, hq.nonzero x]

omit [Fintype A] in
theorem core_pairing_neg_left {q : A → ℂ} (hq : IsMetricGaussian q) (x y : A) :
    metricPairing q (-x) y = (metricPairing q x y)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← hq.add_left, neg_add_cancel, core_pairing_zero_left hq]

omit [Fintype A] in
theorem core_pairing_neg_right {q : A → ℂ} (hq : IsMetricGaussian q) (x y : A) :
    metricPairing q x (-y) = (metricPairing q x y)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← hq.add_right, neg_add_cancel, core_pairing_zero_right hq]

omit [Fintype A] in
theorem core_pairing_neg_neg {q : A → ℂ} (hq : IsMetricGaussian q) (x y : A) :
    metricPairing q (-x) (-y) = metricPairing q x y := by
  rw [core_pairing_neg_left hq, core_pairing_neg_right hq, inv_inv]

omit [Fintype A] in
theorem core_pairing_sub_left {q : A → ℂ} (hq : IsMetricGaussian q) (x y z : A) :
    metricPairing q (x - y) z = metricPairing q x z / metricPairing q y z := by
  rw [sub_eq_add_neg, hq.add_left, core_pairing_neg_left hq, div_eq_mul_inv]

omit [Fintype A] in
theorem core_pairing_sub_right {q : A → ℂ} (hq : IsMetricGaussian q) (x y z : A) :
    metricPairing q x (y - z) = metricPairing q x y / metricPairing q x z := by
  rw [sub_eq_add_neg, hq.add_right, core_pairing_neg_right hq, div_eq_mul_inv]

omit [Fintype A] in
theorem core_gaussian_add {q : A → ℂ} (hq : IsMetricGaussian q) (x y : A) :
    q (x + y) = metricPairing q x y * q x * q y := by
  dsimp [metricPairing]
  field_simp [hq.nonzero x, hq.nonzero y]

omit [AddCommGroup A] in
theorem core_sqrtCard_sq : sqrtCard A ^ 2 = (Fintype.card A : ℂ) := by
  unfold sqrtCard
  rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  rfl

omit [AddCommGroup A] in
theorem core_normalizedSum_congr {f g : A → ℂ} (h : ∀ x, f x = g x) :
    normalizedSum f = normalizedSum g := by
  unfold normalizedSum
  congr 1
  exact Finset.sum_congr rfl fun x _ => h x

omit [AddCommGroup A] in
@[simp] theorem core_normalizedSum_zero : normalizedSum (fun _ : A => (0 : ℂ)) = 0 := by
  simp [normalizedSum]

omit [AddCommGroup A] in
theorem core_normalizedSum_add (f g : A → ℂ) :
    normalizedSum (fun x => f x + g x) = normalizedSum f + normalizedSum g := by
  simp [normalizedSum, Finset.sum_add_distrib, add_div]

omit [AddCommGroup A] in
theorem core_normalizedSum_mul_left (c : ℂ) (f : A → ℂ) :
    normalizedSum (fun x => c * f x) = c * normalizedSum f := by
  unfold normalizedSum
  rw [← Finset.mul_sum]
  ring

omit [AddCommGroup A] in
theorem core_normalizedSum_mul_right (f : A → ℂ) (c : ℂ) :
    normalizedSum (fun x => f x * c) = normalizedSum f * c := by
  simp only [mul_comm _ c, core_normalizedSum_mul_left]

omit [AddCommGroup A] in
theorem core_normalizedSum_swap (f : A → A → ℂ) :
    normalizedSum (fun x => normalizedSum (fun y => f x y)) =
      normalizedSum (fun y => normalizedSum (fun x => f x y)) := by
  unfold normalizedSum
  simp only [Finset.sum_div]
  rw [Finset.sum_comm]

theorem core_normalizedSum_translate (f : A → ℂ) (a : A) :
    normalizedSum (fun x => f (x + a)) = normalizedSum f := by
  unfold normalizedSum
  congr 1
  exact Fintype.sum_equiv (Equiv.addRight a) _ _ (fun _ => rfl)

theorem core_normalizedSum_neg (f : A → ℂ) :
    normalizedSum (fun x => f (-x)) = normalizedSum f := by
  unfold normalizedSum
  congr 1
  exact Fintype.sum_equiv (Equiv.neg A) _ _ (fun _ => rfl)

theorem core_normalizedSum_sub (f : A → ℂ) (a : A) :
    normalizedSum (fun x => f (a - x)) = normalizedSum f := by
  unfold normalizedSum
  congr 1
  exact Fintype.sum_equiv (Equiv.subLeft a) _ _ (fun _ => rfl)

theorem core_fourier_zero {q : A → ℂ} (hq : IsMetricGaussian q) (f : A → ℂ) :
    fourier q f 0 = normalizedSum f := by
  simp [fourier, core_pairing_zero_right hq]

theorem core_character_normalizedSum {q : A → ℂ} (hq : IsMetricGaussian q) (w : A) :
    normalizedSum (fun y => metricPairing q y (-w)) =
      sqrtCard A * (if w = 0 then 1 else 0) := by
  rw [normalizedSum, character_sum hq]
  by_cases hw : w = 0
  · subst w
    simp only [neg_zero, ↓reduceIte, mul_one]
    apply (div_eq_iff sqrtCard_ne_zero).2
    simpa [pow_two] using (core_sqrtCard_sq (A := A)).symm
  · simp [hw]

theorem core_fourier_convolution {q : A → ℂ} (hq : IsMetricGaussian q)
    (f g : A → ℂ) (w : A) :
    fourier q (fun y => normalizedSum (fun z => f (y - z) * g z)) w =
      fourier q f w * fourier q g w := by
  unfold fourier
  calc
    _ = normalizedSum (fun y => normalizedSum (fun z =>
        f (y - z) * g z * metricPairing q y (-w))) := by
      apply core_normalizedSum_congr
      intro y
      rw [core_normalizedSum_mul_right]
    _ = normalizedSum (fun z => normalizedSum (fun y =>
        f (y - z) * g z * metricPairing q y (-w))) := core_normalizedSum_swap _
    _ = normalizedSum (fun z => normalizedSum (fun y =>
        f y * g z * metricPairing q (y + z) (-w))) := by
      apply core_normalizedSum_congr
      intro z
      symm
      simpa only [add_sub_cancel_right] using
        core_normalizedSum_translate (fun y =>
          f (y - z) * g z * metricPairing q y (-w)) z
    _ = normalizedSum (fun z =>
        normalizedSum (fun y => f y * metricPairing q y (-w)) *
          (g z * metricPairing q z (-w))) := by
      apply core_normalizedSum_congr
      intro z
      rw [← core_normalizedSum_mul_right]
      apply core_normalizedSum_congr
      intro y
      rw [hq.add_left]
      ring
    _ = _ := core_normalizedSum_mul_left _ _

theorem transformed_pentagon_core {q E : A → ℂ} (hq : IsMetricGaussian q)
    {C : ℂ} (_hC : C ≠ 0) (hE : Pentagon q E C) (x w : A) :
    E x * fourier q E (w - x) =
      C * sqrtCard A * (if w = 0 then 1 else 0) +
        fourier q E w * fourier q (pentagonKernel q E x) w := by
  have hp := congrArg (fun f : A → ℂ => fourier q f w) (funext (hE x))
  calc
    E x * fourier q E (w - x) =
        fourier q (fun y => metricPairing q x y * E x * E y) w := by
      unfold fourier
      rw [← core_normalizedSum_mul_left]
      apply core_normalizedSum_congr
      intro y
      dsimp only
      rw [metric_pairing_symmetric q x y]
      have hz : -(w - x) = x + -w := by abel
      rw [hz, hq.add_right]
      ring
    _ = fourier q (fun y => C + normalizedSum (fun z =>
        E (y - z) * E z * q z * E (x - z))) w := hp
    _ = _ := by
      unfold fourier
      simp_rw [add_mul]
      rw [core_normalizedSum_add]
      congr 1
      · rw [core_normalizedSum_mul_left, core_character_normalizedSum hq]
        ring
      · change fourier q (fun y => normalizedSum (fun z =>
            E (y - z) * E z * q z * E (x - z))) w =
          fourier q E w * fourier q (pentagonKernel q E x) w
        rw [← core_fourier_convolution hq E (pentagonKernel q E x) w]
        congr 1
        funext y
        apply core_normalizedSum_congr
        intro z
        unfold pentagonKernel
        ring

/- The support argument in [RW26, Thm. 5], including finite-set reversibility of translations. -/
theorem fourier_everywhere_ne_zero_core {q E : A → ℂ} (hq : IsMetricGaussian q)
    (hE : IsFiniteQuantumDilogarithm q E) (w : A) :
    fourier q E w ≠ 0 := by
  obtain ⟨C, hC, hP⟩ := hE
  have hzero : fourier q E 0 ≠ 0 := by
    intro hz
    have hp := transformed_pentagon_core hq hC hP 0 0
    simp only [sub_self, hz, mul_zero, zero_mul, ite_true, mul_one, add_zero] at hp
    exact (mul_ne_zero hC sqrtCard_ne_zero) hp.symm
  have hforward : ∀ x, E x ≠ 0 → ∀ v,
      fourier q E v = 0 → fourier q E (v - x) = 0 := by
    intro x hx v hv
    have hv0 : v ≠ 0 := by
      intro h
      subst v
      exact hzero hv
    have hp := transformed_pentagon_core hq hC hP x v
    simp only [hv, if_neg hv0, mul_zero, zero_mul, add_zero] at hp
    exact (mul_eq_zero.mp hp).resolve_left hx
  let H : AddSubgroup A :=
    { carrier := {x | ∀ v, fourier q E v = 0 ↔ fourier q E (v - x) = 0}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy v
        have hs : v - (x + y) = (v - x) - y := by abel
        rw [hs]
        exact (hx v).trans (hy (v - x))
      neg_mem' := by
        intro x hx v
        have hs : (v - -x) - x = v := by abel
        simpa only [hs] using (hx (v - -x)).symm }
  have hsupport : ∀ x, E x ≠ 0 → x ∈ H := by
    intro x hx v
    constructor
    · exact hforward x hx v
    · intro hv
      let f : {v : A // fourier q E v = 0} → {v : A // fourier q E v = 0} :=
        fun z => ⟨z.val - x, hforward x hx z.val z.property⟩
      have hf : Function.Injective f := by
        intro a b hab
        apply Subtype.ext
        have ht := congrArg Subtype.val hab
        exact sub_left_inj.mp ht
      obtain ⟨z, hz⟩ := Finite.surjective_of_injective hf ⟨v - x, hv⟩
      have hzv : z.val = v := by
        have ht := congrArg Subtype.val hz
        exact sub_left_inj.mp ht
      simpa only [hzv] using z.property
  have hall : ∀ x : A, x ∈ H := by
    intro x
    by_contra hx
    have hex : E x = 0 := by
      by_contra he
      exact hx (hsupport x he)
    have hsum : normalizedSum (fun z => E (x - z) * E z * q z * E (x - z)) = 0 := by
      calc
        _ = normalizedSum (fun _ : A => (0 : ℂ)) := by
          apply core_normalizedSum_congr
          intro z
          by_cases hz : E z = 0
          · simp only [hz, mul_zero, zero_mul]
          · have hxz : E (x - z) = 0 := by
              by_contra he
              have ht := H.add_mem (hsupport (x - z) he) (hsupport z hz)
              exact hx (by simpa only [sub_add_cancel] using ht)
            simp only [hxz, zero_mul]
        _ = 0 := core_normalizedSum_zero
    have hp := hP x x
    simp only [hex, mul_zero, hsum, add_zero] at hp
    exact hC hp.symm
  intro hw
  have hz := (hall w w).mp hw
  exact hzero (by simpa only [sub_self] using hz)

theorem core_fourier_const {q : A → ℂ} (hq : IsMetricGaussian q) (c : ℂ) (w : A) :
    fourier q (fun _ => c) w = c * sqrtCard A * (if w = 0 then 1 else 0) := by
  unfold fourier
  rw [core_normalizedSum_mul_left, core_character_normalizedSum hq]
  ring

theorem core_fourier_delta {q : A → ℂ} (hq : IsMetricGaussian q) (c : ℂ) (w : A) :
    fourier q (fun x => if x = 0 then c else 0) w = c / sqrtCard A := by
  unfold fourier normalizedSum
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp [core_pairing_zero_left hq]

theorem core_fourier_sub_distrib (q f g : A → ℂ) (w : A) :
    fourier q (fun x => f x - g x) w = fourier q f w - fourier q g w := by
  unfold fourier normalizedSum
  simp only [sub_mul, Finset.sum_sub_distrib, sub_div]

/- [RW26, (34)], obtained by Fourier inversion before determining the constant. -/
theorem reflection_with_constant_core {q E : A → ℂ} (hq : IsMetricGaussian q)
    {C : ℂ} (hC : C ≠ 0) (hE : Pentagon q E C) (u : A) :
    E u * E (-u) * q u =
      sqrtCard A * E 0 * (if u = 0 then 1 else 0) - C / fourier q E 0 := by
  have hhat := fourier_everywhere_ne_zero_core hq ⟨C, hC, hE⟩
  have hker : ∀ w, fourier q (pentagonKernel q E 0) w =
      E 0 - if w = 0 then C * sqrtCard A / fourier q E 0 else 0 := by
    intro w
    have hp := transformed_pentagon_core hq hC hE 0 w
    simp only [sub_zero] at hp
    by_cases hw : w = 0
    · subst w
      simp only [ite_true]
      simp only [ite_true, mul_one] at hp
      field_simp [hhat 0]
      linear_combination -hp
    · simp only [if_neg hw, mul_zero, zero_add] at hp ⊢
      exact (mul_left_cancel₀ (hhat w)) (by linear_combination -hp)
  have hi : fourier q (fourier q (pentagonKernel q E 0)) (-u) =
      pentagonKernel q E 0 u := by
    simpa only [neg_neg] using fourier_twice hq (pentagonKernel q E 0) (-u)
  rw [funext hker, core_fourier_sub_distrib, core_fourier_const hq,
    core_fourier_delta hq] at hi
  have hs : C * sqrtCard A / fourier q E 0 / sqrtCard A = C / fourier q E 0 := by
    field_simp [sqrtCard_ne_zero]
  rw [hs] at hi
  simpa only [pentagonKernel, zero_sub, hq.even u, neg_eq_zero, mul_comm] using hi.symm

theorem fqd_everywhere_ne_zero_core {q E : A → ℂ} (hq : IsMetricGaussian q)
    (hE : IsFiniteQuantumDilogarithm q E) (u : A) : E u ≠ 0 := by
  obtain ⟨C, hC, hP⟩ := hE
  have hhat := fourier_everywhere_ne_zero_core hq ⟨C, hC, hP⟩ 0
  intro hu
  have hp := reflection_with_constant_core hq hC hP u
  by_cases h0 : u = 0
  · subst u
    simp only [hu, zero_mul, mul_zero, zero_sub] at hp
    exact (div_ne_zero hC hhat) (neg_eq_zero.mp hp.symm)
  · simp only [hu, zero_mul, if_neg h0, mul_zero, zero_sub] at hp
    exact (div_ne_zero hC hhat) (neg_eq_zero.mp hp.symm)

omit [Fintype A] in
theorem core_gaussian_sub {q : A → ℂ} (hq : IsMetricGaussian q) (x y : A) :
    q (x - y) = metricPairing q x (-y) * q x * q y := by
  rw [sub_eq_add_neg, core_gaussian_add hq, hq.even]

omit [Fintype A] in
theorem core_kernel_phase {q : A → ℂ} (hq : IsMetricGaussian q) (x w z : A) :
    q (x - z) * metricPairing q (x - z) (-w) =
      q (x - w) / q w * q z * metricPairing q z (-(x - w)) := by
  have hb : metricPairing q (x - z) (-w) =
      metricPairing q x (-w) * metricPairing q z w := by
    rw [sub_eq_add_neg, hq.add_left, core_pairing_neg_neg hq]
  have hs : metricPairing q x (-z) = metricPairing q z (-x) := by
    rw [core_pairing_neg_right hq, core_pairing_neg_right hq,
      metric_pairing_symmetric q x z]
  have hn : -(x - w) = -x + w := by abel
  rw [core_gaussian_sub hq, hb, core_gaussian_sub hq, hs, hn, hq.add_right]
  field_simp [hq.nonzero w]

theorem kernel_fourier_symmetry_core {q E : A → ℂ} (hq : IsMetricGaussian q)
    (x w : A) :
    fourier q (pentagonKernel q E x) w =
      q (x - w) / q w * fourier q (pentagonKernel q E x) (x - w) := by
  unfold fourier
  calc
    _ = normalizedSum (fun z => pentagonKernel q E x (x - z) *
        metricPairing q (x - z) (-w)) :=
      (core_normalizedSum_sub (fun z => pentagonKernel q E x z *
        metricPairing q z (-w)) x).symm
    _ = q (x - w) / q w * normalizedSum (fun z =>
        pentagonKernel q E x z * metricPairing q z (-(x - w))) := by
      rw [← core_normalizedSum_mul_left]
      apply core_normalizedSum_congr
      intro z
      dsimp only [pentagonKernel]
      rw [sub_sub_cancel]
      linear_combination E (x - z) * E z * core_kernel_phase hq x w z

theorem core_fourier_product_relation {q E : A → ℂ} (hq : IsMetricGaussian q)
    (hE : IsFiniteQuantumDilogarithm q E) (u v : A) (hu : u ≠ 0) (hv : v ≠ 0) :
    fourier q E u * fourier q E (-u) * q v =
      fourier q E v * fourier q E (-v) * q u := by
  obtain ⟨C, hC, hP⟩ := hE
  have hp1 := transformed_pentagon_core hq hC hP (u + v) v
  have hp2 := transformed_pentagon_core hq hC hP (u + v) u
  have he := fqd_everywhere_ne_zero_core hq ⟨C, hC, hP⟩ (u + v)
  have h1 : v - (u + v) = -u := by abel
  have h2 : u - (u + v) = -v := by abel
  have h3 : u + v - v = u := by abel
  simp only [h1, if_neg hv, mul_zero, zero_add] at hp1
  simp only [h2, if_neg hu, mul_zero, zero_add] at hp2
  rw [kernel_fourier_symmetry_core hq (u + v) v, h3] at hp1
  field_simp [hq.nonzero v] at hp1
  apply mul_left_cancel₀ he
  linear_combination fourier q E u * hp1 - (fourier q E v * q u) * hp2

theorem fourier_product_off_zero_core {q E : A → ℂ} (hq : IsMetricGaussian q)
    (hE : IsFiniteQuantumDilogarithm q E) :
    ∃ d : ℂ, d ≠ 0 ∧ ∀ u : A, u ≠ 0 →
      fourier q E u * fourier q E (-u) = d * q u := by
  by_cases hnontrivial : ∃ v : A, v ≠ 0
  · obtain ⟨v, hv⟩ := hnontrivial
    refine ⟨fourier q E v * fourier q E (-v) / q v,
      div_ne_zero (mul_ne_zero (fourier_everywhere_ne_zero_core hq hE v)
        (fourier_everywhere_ne_zero_core hq hE (-v))) (hq.nonzero v), ?_⟩
    intro u hu
    have hp := core_fourier_product_relation hq hE u v hu hv
    apply (mul_right_cancel₀ (hq.nonzero v))
    field_simp [hq.nonzero v]
    exact hp
  · refine ⟨1, one_ne_zero, ?_⟩
    intro u hu
    exact (hnontrivial ⟨u, hu⟩).elim


end SICLean.L2b

namespace SICLean.L2b


variable {A : Type*} [AddCommGroup A] [Fintype A]

local instance finiteQDDecidableEq : DecidableEq A := Classical.decEq A

theorem transformed_pentagon {q E : A → ℂ} (hq : IsMetricGaussian q)
    {C : ℂ} (hC : C ≠ 0) (hE : Pentagon q E C) (x w : A) :
    E x * fourier q E (w - x) =
      C * sqrtCard A * (if w = 0 then 1 else 0) +
        fourier q E w * fourier q (pentagonKernel q E x) w := by
  exact transformed_pentagon_core hq hC hE x w

theorem fourier_everywhere_ne_zero {q E : A → ℂ} (hq : IsMetricGaussian q)
    (hE : IsFiniteQuantumDilogarithm q E) (w : A) :
    fourier q E w ≠ 0 := by
  exact fourier_everywhere_ne_zero_core hq hE w

/- [RW26, (34)]. This statement precedes the determination of C. -/
theorem reflection_with_constant {q E : A → ℂ} (hq : IsMetricGaussian q)
    {C : ℂ} (hC : C ≠ 0) (hE : Pentagon q E C) (u : A) :
    E u * E (-u) * q u =
      sqrtCard A * E 0 * (if u = 0 then 1 else 0) - C / fourier q E 0 := by
  exact reflection_with_constant_core hq hC hE u

theorem fqd_everywhere_ne_zero {q E : A → ℂ} (hq : IsMetricGaussian q)
    (hE : IsFiniteQuantumDilogarithm q E) (u : A) : E u ≠ 0 := by
  exact fqd_everywhere_ne_zero_core hq hE u

theorem kernel_fourier_symmetry {q E : A → ℂ} (hq : IsMetricGaussian q)
    (x w : A) :
    fourier q (pentagonKernel q E x) w =
      q (x - w) / q w * fourier q (pentagonKernel q E x) (x - w) := by
  exact kernel_fourier_symmetry_core hq x w

theorem fourier_product_off_zero {q E : A → ℂ} (hq : IsMetricGaussian q)
    (hE : IsFiniteQuantumDilogarithm q E) :
    ∃ d : ℂ, d ≠ 0 ∧ ∀ u : A, u ≠ 0 →
      fourier q E u * fourier q E (-u) = d * q u := by
  exact fourier_product_off_zero_core hq hE

/- A form of [RW26, (35)], before choosing the nonzero-point product. -/
theorem aux_fqd_relation35 {q E : A → ℂ} (hq : IsMetricGaussian q)
    {C : ℂ} (hC : C ≠ 0) (hP : Pentagon q E C) (x : A) (hx : x ≠ 0) :
    E x * fourier q E x * fourier q E (-x) =
      C * sqrtCard A * fourier q E x + q x * E x * fourier q E 0 ^ 2 := by
  have h0 := transformed_pentagon hq hC hP x 0
  have h1 := transformed_pentagon hq hC hP x x
  have hk := kernel_fourier_symmetry (E := E) hq x x
  simp only [zero_sub, ite_true, mul_one] at h0
  simp only [sub_self, if_neg hx, mul_zero, zero_add] at h1
  simp only [sub_self, metric_zero hq, one_div] at hk
  have hk' : q x * fourier q (pentagonKernel q E x) x =
      fourier q (pentagonKernel q E x) 0 := by
    rw [hk]
    field_simp [hq.nonzero x]
  linear_combination fourier q E x * h0 - (q x * fourier q E 0) * h1 -
    (fourier q E x * fourier q E 0) * hk'

/- Proportionality away from zero, from [RW26, (35)]. -/
theorem fourier_proportional_off_zero {q E : A → ℂ} (hq : IsMetricGaussian q)
    (hE : IsFiniteQuantumDilogarithm q E) :
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ x : A, x ≠ 0 → fourier q E x = lam * q x * E x := by
  obtain ⟨C, hC, hP⟩ := hE
  obtain ⟨d, hd, hprod⟩ := fourier_product_off_zero hq ⟨C, hC, hP⟩
  have hF (x : A) := fourier_everywhere_ne_zero hq ⟨C, hC, hP⟩ x
  have hs := sqrtCard_ne_zero (A := A)
  have hrel (x : A) (hx : x ≠ 0) :
      E x * (d - fourier q E 0 ^ 2) * q x =
        C * sqrtCard A * fourier q E x := by
    have h0 := transformed_pentagon hq hC hP x 0
    have h1 := transformed_pentagon hq hC hP x x
    have hk := kernel_fourier_symmetry (E := E) hq x x
    have hp := hprod x hx
    simp only [zero_sub, ite_true, mul_one] at h0
    simp only [sub_self, if_neg hx, mul_zero, zero_add] at h1
    simp only [sub_self, metric_zero hq, one_div] at hk
    have hk' : q x * fourier q (pentagonKernel q E x) x =
        fourier q (pentagonKernel q E x) 0 := by
      rw [hk]
      field_simp [hq.nonzero x]
    linear_combination -E x * hp + fourier q E x * h0 -
      (q x * fourier q E 0) * h1 -
      (fourier q E x * fourier q E 0) * hk'
  by_cases hex : ∃ x : A, x ≠ 0
  · obtain ⟨v, hv⟩ := hex
    have hn : d - fourier q E 0 ^ 2 ≠ 0 := by
      intro h
      have hr := hrel v hv
      rw [h, mul_zero, zero_mul] at hr
      exact mul_ne_zero (mul_ne_zero hC hs) (hF v) hr.symm
    refine ⟨(d - fourier q E 0 ^ 2) / (C * sqrtCard A),
      div_ne_zero hn (mul_ne_zero hC hs), ?_⟩
    intro x hx
    have hr := hrel x hx
    field_simp
    linear_combination -hr
  · refine ⟨1, one_ne_zero, ?_⟩
    intro x hx
    exact (hex ⟨x, hx⟩).elim

/- Affine form of the Fourier step in [RW26, Thm. 5]. -/
theorem gaussian_times_E_affine_fourier {q E : A → ℂ}
    (hq : IsMetricGaussian q) (hE : IsFiniteQuantumDilogarithm q E) :
    ∃ a b : ℂ, ∀ x : A, q x * E x = a * fourier q E x + b := by
  obtain ⟨C, hC, hP⟩ := hE
  obtain ⟨lam, hlam, hprop⟩ := fourier_proportional_off_zero hq ⟨C, hC, hP⟩
  have hF (x : A) := fourier_everywhere_ne_zero hq ⟨C, hC, hP⟩ x
  have hEn (x : A) := fqd_everywhere_ne_zero hq ⟨C, hC, hP⟩ x
  let K : A → ℂ := fun x => fourier q (pentagonKernel q E x) 0
  have hK (x : A) (hx : x ≠ 0) : K x = fourier q E 0 / lam := by
    apply (eq_div_iff hlam).2
    apply mul_left_cancel₀ (hEn x)
    have ht := transformed_pentagon hq hC hP x x
    have hk := kernel_fourier_symmetry (E := E) hq x x
    simp only [sub_self, if_neg hx, mul_zero, zero_add] at ht
    simp only [sub_self, metric_zero hq, one_div] at hk
    rw [hprop x hx, hk] at ht
    dsimp [K]
    field_simp [hq.nonzero x] at ht
    linear_combination -ht
  have hKconv : K = fun x => normalizedSum (fun z => E (x - z) * (q z * E z)) := by
    funext x
    simp only [K, fourier, neg_zero, aux_pairing_zero_right hq, mul_one,
      pentagonKernel]
    congr 1
    funext z
    ring
  obtain ⟨b, hb⟩ := aux_fourier_affine_of_off_zero (g := fun _ => 1) hq
    (fourier q E 0 / lam) (by simpa using hK)
  have hprod (y : A) (hy : y ≠ 0) :
      fourier q E y * fourier q (fun x => q x * E x) y = b := by
    have ht := hb y
    rw [hKconv, aux_fourier_convolution hq] at ht
    simpa only [aux_fourier_constant hq, if_neg hy, mul_zero, zero_add] using ht
  let r : ℂ := -lam * C / fourier q E 0
  have hr : r ≠ 0 := div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hlam) hC) (hF 0)
  have hreflect (y : A) (hy : y ≠ 0) : fourier q E y * E (-y) = r := by
    have ht := reflection_with_constant hq hC hP y
    simp only [if_neg hy, mul_zero, zero_sub] at ht
    rw [hprop y hy]
    dsimp [r]
    linear_combination lam * ht
  have hdual (y : A) (hy : y ≠ 0) :
      fourier q (fun x => q x * E x) y = (b / r) * E (-y) := by
    apply mul_left_cancel₀ (hF y)
    rw [hprod y hy]
    calc
      b = (b / r) * r := by field_simp
      _ = fourier q E y * ((b / r) * E (-y)) := by
        rw [← hreflect y hy]
        ring
  obtain ⟨d, hd⟩ := aux_fourier_affine_of_off_zero hq (b / r) hdual
  refine ⟨b / r, d, ?_⟩
  intro x
  have ht := hd (-x)
  simpa only [fourier_twice hq, aux_fourier_reflection hq, neg_neg] using ht

theorem gaussian_times_E_not_constant_off_zero {q E : A → ℂ}
    (hq : IsMetricGaussian q) (hE : IsFiniteQuantumDilogarithm q E)
    (hcard : 4 < Fintype.card A) :
    ¬ ∃ c : ℂ, ∀ x : A, x ≠ 0 → q x * E x = c := by
  rintro ⟨c, hc⟩
  obtain ⟨C, hC, hP⟩ := hE
  have hF := fourier_everywhere_ne_zero hq ⟨C, hC, hP⟩ 0
  have hE0 := fqd_everywhere_ne_zero hq ⟨C, hC, hP⟩
  apply gaussian_not_constant_off_zero hq hcard
  refine ⟨-(c ^ 2 * fourier q E 0) / C, ?_⟩
  intro x hx
  have hr := reflection_with_constant hq hC hP x
  have hc1 := hc x hx
  have hc2 := hc (-x) (neg_ne_zero.mpr hx)
  rw [hq.even] at hc2
  simp only [if_neg hx, mul_zero, zero_sub] at hr
  have hqx := hq.nonzero x
  field_simp at hr ⊢
  linear_combination -(fourier q E 0) * (q x * E (-x) * hc1 + c * hc2) +
    q x * hr

/- Exactly the first half of Thm. 5(iii), also at zero. It is proved before
C and the origin quadratic are determined, following the affine argument. -/
theorem fqd_fourier {q E : A → ℂ} (hq : IsMetricGaussian q)
    (hcard : 4 < Fintype.card A) (hE : IsFiniteQuantumDilogarithm q E) (u : A) :
    fourier q E u = fourierScalar q E * q u * E u := by
  obtain ⟨lam, hlam, hprop⟩ := fourier_proportional_off_zero hq hE
  obtain ⟨a, b, haff⟩ := gaussian_times_E_affine_fourier hq hE
  have hnot := gaussian_times_E_not_constant_off_zero hq hE hcard
  have hal : a * lam = 1 := by
    by_contra hn
    have hn' : 1 - a * lam ≠ 0 := sub_ne_zero.mpr (Ne.symm hn)
    apply hnot
    refine ⟨b / (1 - a * lam), ?_⟩
    intro x hx
    apply (eq_div_iff hn').2
    have ht := haff x
    rw [hprop x hx] at ht
    linear_combination ht
  have hex : ∃ x : A, x ≠ 0 := by
    by_contra hn
    apply hnot
    refine ⟨0, ?_⟩
    intro x hx
    exact (hn ⟨x, hx⟩).elim
  obtain ⟨v, hv⟩ := hex
  have hb : b = 0 := by
    have ht := haff v
    rw [hprop v hv] at ht
    linear_combination -(q v * E v) * hal - ht
  have hfull (x : A) : fourier q E x = lam * q x * E x := by
    have ht := haff x
    rw [hb, add_zero] at ht
    linear_combination -lam * ht - fourier q E x * hal
  have hscalar : fourierScalar q E = lam := by
    unfold fourierScalar
    apply (div_eq_iff (fqd_everywhere_ne_zero hq hE 0)).2
    simpa [metric_zero hq] using hfull 0
  rw [hscalar]
  exact hfull u

/- The origin quadratic and the nonzero pentagon constant are forced together. -/
theorem aux_fqd_origin_and_constant {q E : A → ℂ} (hq : IsMetricGaussian q)
    (hcard : 4 < Fintype.card A) {C : ℂ} (hC : C ≠ 0) (hP : Pentagon q E C) :
    E 0 ^ 2 = sqrtCard A * E 0 + 1 ∧ C = -fourier q E 0 := by
  have hE : IsFiniteQuantumDilogarithm q E := ⟨C, hC, hP⟩
  have he := fqd_everywhere_ne_zero hq hE 0
  have hf := fourier_everywhere_ne_zero hq hE 0
  have hs := sqrtCard_ne_zero (A := A)
  have : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨v, hv⟩ := exists_ne (0 : A)
  have hev := fqd_everywhere_ne_zero hq hE v
  have hqv := hq.nonzero v
  have hrel := aux_fqd_relation35 hq hC hP v hv
  rw [fqd_fourier hq hcard hE v, fqd_fourier hq hcard hE (-v),
    hq.even, fourierScalar] at hrel
  field_simp [he, hf, hev, hqv] at hrel
  have hrv := reflection_with_constant hq hC hP v
  simp only [if_neg hv, mul_zero, zero_sub] at hrv
  field_simp at hrv
  have hr0 := reflection_with_constant hq hC hP (0 : A)
  simp only [neg_zero, metric_zero hq, mul_one, ite_true] at hr0
  field_simp at hr0
  have hc : fourier q E 0 * E 0 ^ 2 + C * (sqrtCard A * E 0 + 1) = 0 := by
    linear_combination -hrel + hrv
  have hcf : C + fourier q E 0 = 0 := by
    apply mul_left_cancel₀ (mul_ne_zero hs he)
    rw [mul_zero]
    linear_combination hc - hr0
  have hCeq : C = -fourier q E 0 := eq_neg_of_add_eq_zero_left hcf
  refine ⟨?_, hCeq⟩
  rw [hCeq] at hr0
  apply mul_left_cancel₀ hf
  linear_combination hr0

theorem fqd_origin_quadratic {q E : A → ℂ} (hq : IsMetricGaussian q)
    (hcard : 4 < Fintype.card A) (hE : IsFiniteQuantumDilogarithm q E) :
    E 0 ^ 2 = sqrtCard A * E 0 + 1 := by
  obtain ⟨C, hC, hP⟩ := hE
  exact (aux_fqd_origin_and_constant hq hcard hC hP).1

theorem pentagon_constant_eq {q E : A → ℂ} (hq : IsMetricGaussian q)
    (hcard : 4 < Fintype.card A) {C : ℂ} (hC : C ≠ 0) (hE : Pentagon q E C) :
    C = -fourier q E 0 := by
  exact (aux_fqd_origin_and_constant hq hcard hC hE).2

theorem fqd_reflection {q E : A → ℂ} (hq : IsMetricGaussian q)
    (hcard : 4 < Fintype.card A) (hE : IsFiniteQuantumDilogarithm q E)
    (u : A) (hu : u ≠ 0) : E u * E (-u) = (q u)⁻¹ := by
  obtain ⟨C, hC, hP⟩ := hE
  have hr := reflection_with_constant hq hC hP u
  rw [pentagon_constant_eq hq hcard hC hP] at hr
  have hF := fourier_everywhere_ne_zero hq ⟨C, hC, hP⟩ 0
  simp only [if_neg hu, mul_zero, neg_div, div_self hF, sub_neg_eq_add,
    zero_add] at hr
  exact eq_inv_of_mul_eq_one_left hr

theorem fqd_reflection_all {q E : A → ℂ} (hq : IsMetricGaussian q)
    (hcard : 4 < Fintype.card A) (hE : IsFiniteQuantumDilogarithm q E) (u : A) :
    E u * E (-u) * q u =
      1 + sqrtCard A * E 0 * (if u = 0 then 1 else 0) := by
  obtain ⟨C, hC, hP⟩ := hE
  have hr := reflection_with_constant hq hC hP u
  rw [pentagon_constant_eq hq hcard hC hP] at hr
  have hF := fourier_everywhere_ne_zero hq ⟨C, hC, hP⟩ 0
  simpa only [neg_div, div_self hF, sub_neg_eq_add, add_comm] using hr

/- A zero-inclusive inverse formula used to derive (36) from (33). -/
theorem fqd_inverse_reflection {q E : A → ℂ} (hq : IsMetricGaussian q)
    (hcard : 4 < Fintype.card A) (hE : IsFiniteQuantumDilogarithm q E) (u : A) :
    (q u * E (-u))⁻¹ = E u - sqrtCard A * (if u = 0 then 1 else 0) := by
  by_cases hu : u = 0
  · subst u
    have he := fqd_everywhere_ne_zero hq hE 0
    have hr := fqd_origin_quadratic hq hcard hE
    simp only [neg_zero, metric_zero hq, one_mul, ite_true, mul_one]
    apply inv_eq_of_mul_eq_one_right
    linear_combination hr
  · have hr := fqd_reflection hq hcard hE u hu
    simp only [if_neg hu, mul_zero, sub_zero]
    apply inv_eq_of_mul_eq_one_right
    calc
      (q u * E (-u)) * E u = q u * (E u * E (-u)) := by ring
      _ = 1 := by rw [hr, mul_inv_cancel₀ (hq.nonzero u)]

/- [RW26, (36)], including the value at (0,0). -/
theorem fqd_pentagon36 {q E : A → ℂ} (hq : IsMetricGaussian q)
    (hcard : 4 < Fintype.card A) (hE : IsFiniteQuantumDilogarithm q E) (x y : A) :
    normalizedSum (fun t => E t * q t * E (x - t) * metricPairing q t y) =
      q (x + y) * E (-x - y) * E x * E y -
        (Fintype.card A : ℂ) * E 0 * (if x = 0 ∧ y = 0 then 1 else 0) := by
  obtain ⟨C, hC, hP⟩ := hE
  have hE : IsFiniteQuantumDilogarithm q E := ⟨C, hC, hP⟩
  have hFn (z : A) := fourier_everywhere_ne_zero hq hE z
  have hEn (z : A) := fqd_everywhere_ne_zero hq hE z
  have hCeq := pentagon_constant_eq hq hcard hC hP
  have hk0 (z : A) (hz : z ≠ 0) :
      fourier q (pentagonKernel q E z) 0 = E 0 := by
    have ht := transformed_pentagon hq hC hP z z
    have hk := kernel_fourier_symmetry (E := E) hq z z
    simp only [sub_self, if_neg hz, mul_zero, zero_add] at ht
    simp only [sub_self, metric_zero hq, one_div] at hk
    rw [fqd_fourier hq hcard hE z, hk, fourierScalar] at ht
    field_simp [hFn 0, hEn 0, hEn z, hq.nonzero z] at ht
    linear_combination -ht
  have hk00 : fourier q (pentagonKernel q E 0) 0 = E 0 + sqrtCard A := by
    have ht := transformed_pentagon hq hC hP 0 0
    simp only [sub_self, ite_true, mul_one, hCeq] at ht
    apply mul_left_cancel₀ (hFn 0)
    linear_combination -ht
  have hleft :
      normalizedSum (fun t => E t * q t * E (x - t) * metricPairing q t y) =
        fourier q (pentagonKernel q E x) (-y) := by
    unfold fourier pentagonKernel
    simp only [neg_neg]
    congr 1
    funext t
    ring
  rw [hleft]
  by_cases hy : y = 0
  · subst y
    simp only [neg_zero, add_zero, sub_zero, and_true]
    by_cases hx : x = 0
    · subst x
      rw [hk00]
      simp only [neg_zero, metric_zero hq, one_mul, ite_true, mul_one]
      have he := fqd_origin_quadratic hq hcard hE
      have hs := aux_sqrtCard_sq (A := A)
      linear_combination -(E 0 + sqrtCard A) * he - E 0 * hs
    · rw [hk0 x hx]
      simp only [if_neg hx, mul_zero, sub_zero]
      have hr := fqd_reflection_all hq hcard hE x
      simp only [if_neg hx, mul_zero, add_zero] at hr
      linear_combination -E 0 * hr
  · simp only [hy, and_false, if_false, mul_zero, sub_zero]
    have ht := transformed_pentagon hq hC hP x (-y)
    have hxy : -y - x = -x - y := by abel
    have hqxy : q (-x - y) = q (x + y) := by
      rw [show -x - y = -(x + y) by abel, hq.even]
    simp only [if_neg (neg_ne_zero.mpr hy), mul_zero, zero_add, hxy] at ht
    rw [fqd_fourier hq hcard hE (-x - y), hqxy] at ht
    have hr := fqd_reflection_all hq hcard hE y
    simp only [if_neg hy, mul_zero, add_zero] at hr
    apply mul_left_cancel₀ (hFn (-y))
    rw [← ht, fqd_fourier hq hcard hE (-y), hq.even]
    linear_combination -(fourierScalar q E * q (x + y) * E (-x - y) * E x) * hr


end SICLean.L2b

namespace SICLean.L2b

abbrev cofactor (M : ℕ) : ℕ := M - 3
abbrev longModulus (M : ℕ) : ℕ := M * cofactor M
abbrev groupOrder (M : ℕ) : ℕ := M ^ 2 * cofactor M

/- Smith coordinates. A representative (x,y) has numerator
`(a,b)=(x,y-(M-2)x)` relative to ε⁻³−1, as in [RW26]. -/
abbrev G (M : ℕ) := ZMod M × ZMod (longModulus M)

instance validMNeZero (M : ℕ) [Fact (4 ≤ M)] : NeZero M :=
  ⟨by have := (Fact.out : 4 ≤ M); omega⟩

instance cofactorNeZero (M : ℕ) [Fact (4 ≤ M)] : NeZero (cofactor M) :=
  ⟨by have := (Fact.out : 4 ≤ M); simp only [cofactor]; omega⟩

instance longModulusNeZero (M : ℕ) [Fact (4 ≤ M)] : NeZero (longModulus M) :=
  ⟨by
    have h4 := (Fact.out : 4 ≤ M)
    exact Nat.mul_ne_zero (by omega) (by simp only [cofactor]; omega)⟩

def coordinate (M : ℕ) (x y : ℤ) : G M := (x, y)


variable (M : ℕ) [Fact (4 ≤ M)]

theorem card_G : Fintype.card (G M) = groupOrder M := by
  simp only [G, Fintype.card_prod, ZMod.card, groupOrder, cofactor, longModulus]
  ring

theorem card_G_gt_four : 4 < Fintype.card (G M) := by
  have h4 : (4 : ℕ) ≤ M := Fact.out
  rw [card_G]
  simp only [groupOrder, cofactor, pow_two]
  have h3 : (1 : ℕ) ≤ M - 3 := by omega
  have h16 : (16 : ℕ) ≤ M * M := Nat.mul_le_mul h4 h4
  have h2 : M * M * 1 ≤ M * M * (M - 3) := Nat.mul_le_mul_left _ h3
  omega

theorem sqrtCard_G : sqrtCard (G M) = (M : ℂ) * L2a.convolutionScalar M := by
  have h4 : (4 : ℕ) ≤ M := Fact.out
  have hc : ((groupOrder M : ℕ) : ℝ) = ((M : ℝ)) ^ 2 * ((M : ℝ) - 3) := by
    have h3 : (3 : ℕ) ≤ M := by omega
    simp only [groupOrder, cofactor, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub h3]
    push_cast
    ring
  have hsq : Real.sqrt (((M : ℝ)) ^ 2 * ((M : ℝ) - 3)) = (M : ℝ) * Real.sqrt ((M : ℝ) - 3) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [sqrtCard, card_G, hc, hsq, Complex.ofReal_mul]
  rfl


omit [Fact (4 ≤ M)] in
private theorem coordinate_eq_of_dvd {a a' b b' : ℤ} (ha : ((M : ℤ)) ∣ a - a')
    (hb : ((longModulus M : ℤ)) ∣ b - b') :
    coordinate M a b = coordinate M a' b' := by
  have ha' : ((M : ℤ)) ∣ a' - a := by rw [← neg_sub]; exact Int.dvd_neg.mpr ha
  have hb' : ((longModulus M : ℤ)) ∣ b' - b := by rw [← neg_sub]; exact Int.dvd_neg.mpr hb
  simp only [coordinate, Prod.ext_iff]
  exact ⟨(ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr ha',
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr hb'⟩

private theorem coordinate_val (g : G M) :
    coordinate M (g.1.val : ℤ) (g.2.val : ℤ) = g := by
  refine Prod.ext ?_ ?_
  · simp only [coordinate]
    push_cast
    exact ZMod.natCast_zmod_val g.1
  · simp only [coordinate]
    push_cast
    exact ZMod.natCast_zmod_val g.2

omit [Fact (4 ≤ M)] in
private theorem coordinate_add (a b c d : ℤ) :
    coordinate M a b + coordinate M c d = coordinate M (a + c) (b + d) := by
  simp only [coordinate, Prod.ext_iff, Prod.fst_add, Prod.snd_add]
  constructor <;> push_cast <;> ring

omit [Fact (4 ≤ M)] in
private theorem coordinate_sub (a b c d : ℤ) :
    coordinate M a b - coordinate M c d = coordinate M (a - c) (b - d) := by
  simp only [coordinate, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]
  constructor <;> push_cast <;> ring

private theorem hcoℤ : ((cofactor M : ℤ)) = ((M : ℤ)) - 3 :=
  Nat.cast_sub (by have := (Fact.out : 4 ≤ M); omega)

omit [Fact (4 ≤ M)] in
private theorem hnmℤ : ((longModulus M : ℤ)) = ((M : ℤ)) * ((cofactor M : ℤ)) := by
  simp only [longModulus, cofactor, Nat.cast_mul]

private theorem coordinate_fst_val (a b : ℤ) :
    ((coordinate M a b).1.val : ℤ) = ((a : ℤ)) % ((M : ℤ)) := by
  simp only [coordinate]
  exact_mod_cast ZMod.val_intCast a

private theorem coordinate_snd_val (a b : ℤ) :
    ((coordinate M a b).2.val : ℤ) = ((b : ℤ)) % ((longModulus M : ℤ)) := by
  simp only [coordinate]
  exact_mod_cast ZMod.val_intCast b

/- The head symbol of epsilonAut on any integer pair: only mods get reduced. -/
private theorem epsAut_on_coordinate (x y : ℤ) :
    coordinate M (((coordinate M x y).1.val : ℤ) + ((coordinate M x y).2.val : ℤ))
        (((cofactor M : ℤ)) * ((coordinate M x y).1.val : ℤ)
          + ((M : ℤ) - 2) * ((coordinate M x y).2.val : ℤ))
      = coordinate M (x + y) (((cofactor M : ℤ)) * x + ((M : ℤ) - 2) * y) := by
  rw [coordinate_fst_val, coordinate_snd_val]
  have hA := Int.mul_ediv_add_emod (x : ℤ) ((M : ℤ))
  have hB := Int.mul_ediv_add_emod (y : ℤ) ((longModulus M : ℤ))
  have h1 : (x : ℤ) % ((M : ℤ)) - x = -(((M : ℤ)) * (x / ((M : ℤ)))) := by
    linear_combination hA
  have h2 : (y : ℤ) % ((longModulus M : ℤ)) - y
      = -(((longModulus M : ℤ)) * (y / ((longModulus M : ℤ)))) := by
    linear_combination hB
  have h3 : ((M : ℤ)) * ((cofactor M : ℤ)) = ((longModulus M : ℤ)) := hnmℤ M
  refine coordinate_eq_of_dvd (M := M) ?_ ?_
  · refine ⟨-(x / ((M : ℤ))) - ((cofactor M : ℤ)) * (y / ((longModulus M : ℤ))), ?_⟩
    linear_combination h1 + h2 + (y / ((longModulus M : ℤ))) * h3
  · refine ⟨-(x / ((M : ℤ))) - ((M : ℤ) - 2) * (y / ((longModulus M : ℤ))), ?_⟩
    linear_combination ((cofactor M : ℤ)) * h1 + ((M : ℤ) - 2) * h2
      - (x / ((M : ℤ))) * h3

private theorem epsAutInv_on_coordinate (x y : ℤ) :
    coordinate M (((M : ℤ) - 2) * ((coordinate M x y).1.val : ℤ)
        - ((coordinate M x y).2.val : ℤ))
        (-((cofactor M : ℤ)) * ((coordinate M x y).1.val : ℤ)
          + ((coordinate M x y).2.val : ℤ))
      = coordinate M (((M : ℤ) - 2) * x - y) (-((cofactor M : ℤ)) * x + y) := by
  have h1 := Int.mul_ediv_add_emod (x : ℤ) ((M : ℤ))
  have h2 := Int.mul_ediv_add_emod (y : ℤ) ((longModulus M : ℤ))
  have hnm : ((M : ℤ)) * ((cofactor M : ℤ)) = ((longModulus M : ℤ)) := hnmℤ M
  have hf := coordinate_fst_val M x y
  have hs := coordinate_snd_val M x y
  refine coordinate_eq_of_dvd (M := M) ⟨-((M : ℤ) - 2) * (x / ((M : ℤ)))
      + ((cofactor M : ℤ)) * (y / ((longModulus M : ℤ))), ?_⟩
    ⟨(x / ((M : ℤ))) - (y / ((longModulus M : ℤ))), ?_⟩
  · rw [hf, hs]
    linear_combination ((M : ℤ) - 2) * h1 - h2
      - (y / ((longModulus M : ℤ))) * hnm
  · rw [hf, hs]
    linear_combination (x / ((M : ℤ))) * hnm - ((cofactor M : ℤ)) * h1 + h2

/- Explicit multiplication by ε; its inverse is (u x−y, −m x+y). -/
def epsilonAut (M : ℕ) [Fact (4 ≤ M)] : G M ≃+ G M where
  toFun g := coordinate M ((g.1.val : ℤ) + g.2.val)
    ((cofactor M : ℤ) * g.1.val + ((M : ℤ) - 2) * g.2.val)
  invFun g := coordinate M (((M : ℤ) - 2) * g.1.val - g.2.val)
    (-(cofactor M : ℤ) * g.1.val + g.2.val)
  left_inv := by
    intro g
    rw [← coordinate_val M g]
    have hA : (fun g' : G M => coordinate M ((g'.1.val : ℤ) + g'.2.val)
        (((cofactor M : ℤ)) * g'.1.val + ((M : ℤ) - 2) * g'.2.val))
        (coordinate M ((g.1.val : ℤ)) ((g.2.val : ℤ)))
      = coordinate M (((g.1.val : ℤ)) + ((g.2.val : ℤ)))
          (((cofactor M : ℤ)) * ((g.1.val : ℤ)) + ((M : ℤ) - 2) * ((g.2.val : ℤ))) :=
      epsAut_on_coordinate M ((g.1.val : ℤ)) ((g.2.val : ℤ))
    rw [hA]
    have hB : (fun g' : G M => coordinate M (((M : ℤ) - 2) * g'.1.val - g'.2.val)
        (-((cofactor M : ℤ)) * g'.1.val + g'.2.val))
        (coordinate M (((g.1.val : ℤ)) + ((g.2.val : ℤ)))
          (((cofactor M : ℤ)) * ((g.1.val : ℤ)) + ((M : ℤ) - 2) * ((g.2.val : ℤ))))
      = coordinate M (((M : ℤ) - 2) * (((g.1.val : ℤ)) + ((g.2.val : ℤ)))
          - (((cofactor M : ℤ)) * ((g.1.val : ℤ)) + ((M : ℤ) - 2) * ((g.2.val : ℤ))))
        (-((cofactor M : ℤ)) * (((g.1.val : ℤ)) + ((g.2.val : ℤ)))
          + (((cofactor M : ℤ)) * ((g.1.val : ℤ)) + ((M : ℤ) - 2) * ((g.2.val : ℤ)))) :=
      epsAutInv_on_coordinate M (((g.1.val : ℤ)) + ((g.2.val : ℤ)))
        (((cofactor M : ℤ)) * ((g.1.val : ℤ)) + ((M : ℤ) - 2) * ((g.2.val : ℤ)))
    rw [hB]
    have hco : ((cofactor M : ℤ)) = ((M : ℤ)) - 3 := hcoℤ M
    rw [hco]
    exact coordinate_eq_of_dvd (M := M) ⟨0, by ring⟩ ⟨0, by ring⟩
  right_inv := by
    intro g
    rw [← coordinate_val M g]
    have hA : (fun g' : G M => coordinate M (((M : ℤ) - 2) * g'.1.val - g'.2.val)
        (-((cofactor M : ℤ)) * g'.1.val + g'.2.val))
        (coordinate M ((g.1.val : ℤ)) ((g.2.val : ℤ)))
      = coordinate M (((M : ℤ) - 2) * ((g.1.val : ℤ)) - ((g.2.val : ℤ)))
        (-((cofactor M : ℤ)) * ((g.1.val : ℤ)) + ((g.2.val : ℤ))) :=
      epsAutInv_on_coordinate M ((g.1.val : ℤ)) ((g.2.val : ℤ))
    rw [hA]
    have hB : (fun g' : G M => coordinate M ((g'.1.val : ℤ) + g'.2.val)
        (((cofactor M : ℤ)) * g'.1.val + ((M : ℤ) - 2) * g'.2.val))
        (coordinate M (((M : ℤ) - 2) * ((g.1.val : ℤ)) - ((g.2.val : ℤ)))
          (-((cofactor M : ℤ)) * ((g.1.val : ℤ)) + ((g.2.val : ℤ))))
      = coordinate M ((((M : ℤ) - 2) * ((g.1.val : ℤ)) - ((g.2.val : ℤ)))
          + (-((cofactor M : ℤ)) * ((g.1.val : ℤ)) + ((g.2.val : ℤ))))
        (((cofactor M : ℤ)) * (((M : ℤ) - 2) * ((g.1.val : ℤ)) - ((g.2.val : ℤ)))
          + ((M : ℤ) - 2) * (-((cofactor M : ℤ)) * ((g.1.val : ℤ)) + ((g.2.val : ℤ)))) :=
      epsAut_on_coordinate M (((M : ℤ) - 2) * ((g.1.val : ℤ)) - ((g.2.val : ℤ)))
        (-((cofactor M : ℤ)) * ((g.1.val : ℤ)) + ((g.2.val : ℤ)))
    rw [hB]
    have hco : ((cofactor M : ℤ)) = ((M : ℤ)) - 3 := hcoℤ M
    rw [hco]
    exact coordinate_eq_of_dvd (M := M) ⟨0, by ring⟩ ⟨0, by ring⟩
  map_add' := by
    intro g₁ g₂
    rw [show g₁ = coordinate M ((g₁.1.val : ℤ)) ((g₁.2.val : ℤ)) from (coordinate_val M g₁).symm,
      show g₂ = coordinate M ((g₂.1.val : ℤ)) ((g₂.2.val : ℤ)) from (coordinate_val M g₂).symm,
      show coordinate M ((g₁.1.val : ℤ)) ((g₁.2.val : ℤ))
          + coordinate M ((g₂.1.val : ℤ)) ((g₂.2.val : ℤ))
        = coordinate M (((g₁.1.val : ℤ)) + (g₂.1.val : ℤ))
          (((g₁.2.val : ℤ)) + (g₂.2.val : ℤ))
        from coordinate_add M ((g₁.1.val : ℤ)) ((g₁.2.val : ℤ))
          ((g₂.1.val : ℤ)) ((g₂.2.val : ℤ))]
    rw [epsAut_on_coordinate M (((g₁.1.val : ℤ)) + (g₂.1.val : ℤ))
        (((g₁.2.val : ℤ)) + (g₂.2.val : ℤ)),
      epsAut_on_coordinate M ((g₁.1.val : ℤ)) ((g₁.2.val : ℤ)),
      epsAut_on_coordinate M ((g₂.1.val : ℤ)) ((g₂.2.val : ℤ)), coordinate_add]
    exact coordinate_eq_of_dvd (M := M) ⟨0, by ring⟩ ⟨0, by ring⟩

private theorem epsilonAut_coordinate (x y : ℤ) :
    epsilonAut M (coordinate M x y)
      = coordinate M (x + y) (((cofactor M : ℤ)) * x + ((M : ℤ) - 2) * y) :=
  epsAut_on_coordinate M x y

def iota (M : ℕ) [Fact (4 ≤ M)] : L2a.Index M →+ G M where
  toFun h := coordinate M (2 * (h.2.val : ℤ) - h.1.val)
    ((cofactor M : ℤ) * h.2.val)
  map_zero' := by
    simp [coordinate]
  map_add' := by
    intro a b
    have h4 : (4 : ℕ) ≤ M := Fact.out
    have : NeZero M := NeZero.of_pos (by omega)
    have hm1 : ((M : ℤ)) * (((a.1.val : ℤ) + b.1.val) / ((M : ℤ)))
        + (((a.1.val : ℤ) + b.1.val) % ((M : ℤ))) = (a.1.val : ℤ) + b.1.val :=
      Int.mul_ediv_add_emod _ _
    have hm2 : ((M : ℤ)) * (((a.2.val : ℤ) + b.2.val) / ((M : ℤ)))
        + (((a.2.val : ℤ) + b.2.val) % ((M : ℤ))) = (a.2.val : ℤ) + b.2.val :=
      Int.mul_ediv_add_emod _ _
    have hL : coordinate M (2 * ((a + b).2.val : ℤ) - (a + b).1.val)
        (((cofactor M : ℤ)) * (a + b).2.val) = coordinate M
        (2 * (((a.2.val : ℤ) + b.2.val) % ((M : ℤ)))
          - (((a.1.val : ℤ) + b.1.val) % ((M : ℤ))))
        (((cofactor M : ℤ)) * (((a.2.val : ℤ) + b.2.val) % ((M : ℤ)))) := by
      simp only [Prod.fst_add, Prod.snd_add, ZMod.val_add]
      push_cast
      rfl
    have hR : coordinate M (2 * (a.2.val : ℤ) - a.1.val) (((cofactor M : ℤ)) * (a.2.val : ℤ))
        + coordinate M (2 * (b.2.val : ℤ) - b.1.val) (((cofactor M : ℤ)) * (b.2.val : ℤ))
        = coordinate M
        ((2 * (a.2.val : ℤ) - a.1.val) + (2 * (b.2.val : ℤ) - b.1.val))
        (((cofactor M : ℤ)) * (a.2.val : ℤ) + ((cofactor M : ℤ)) * (b.2.val : ℤ)) :=
      coordinate_add M (2 * (a.2.val : ℤ) - a.1.val) (((cofactor M : ℤ)) * (a.2.val : ℤ))
        (2 * (b.2.val : ℤ) - b.1.val) (((cofactor M : ℤ)) * (b.2.val : ℤ))
    rw [hL, hR]
    have hnm := hnmℤ M
    refine coordinate_eq_of_dvd
      (a := 2 * (((a.2.val : ℤ) + b.2.val) % ((M : ℤ)))
        - (((a.1.val : ℤ) + b.1.val) % ((M : ℤ))))
      (a' := (2 * (a.2.val : ℤ) - a.1.val) + (2 * (b.2.val : ℤ) - b.1.val))
      (b := ((cofactor M : ℤ)) * (((a.2.val : ℤ) + b.2.val) % ((M : ℤ))))
      (b' := ((cofactor M : ℤ)) * (a.2.val : ℤ) + ((cofactor M : ℤ)) * (b.2.val : ℤ))
      (ha := ⟨(((a.1.val : ℤ) + b.1.val) / ((M : ℤ))) - 2 * (((a.2.val : ℤ) + b.2.val) / ((M : ℤ))),
        by linear_combination 2 * hm2 - hm1⟩)
      (hb := ⟨-(((a.2.val : ℤ) + b.2.val) / ((M : ℤ))),
        by linear_combination ((cofactor M : ℤ)) * hm2
          + (((a.2.val : ℤ) + b.2.val) / ((M : ℤ))) * hnm⟩)

private theorem nat_eq_of_modEq_lt (n a b : ℕ) (h : a ≡ b [MOD n]) (ha : a < n) (hb : b < n) :
    a = b := by
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · rw [Nat.modEq_iff_dvd' (Nat.le_of_lt hab)] at h
    obtain ⟨k, hk⟩ := h
    match k with
    | 0 => omega
    | k + 1 =>
      have hge : n ≤ n * (k + 1) := Nat.le_mul_of_pos_right n (by omega)
      omega
  · exact hab
  · have h2 := h.symm
    rw [Nat.modEq_iff_dvd' (Nat.le_of_lt hab)] at h2
    obtain ⟨k, hk⟩ := h2
    match k with
    | 0 => omega
    | k + 1 =>
      have hge : n ≤ n * (k + 1) := Nat.le_mul_of_pos_right n (by omega)
      omega

theorem iota_injective : Function.Injective (iota M) := by
  intro a b hab
  have h4 : (4 : ℕ) ≤ M := Fact.out
  have : NeZero M := NeZero.of_pos (by omega)
  have hcℤ : ((cofactor M : ℤ)) = ((M : ℤ)) - 3 := hcoℤ M
  have hco0 : ((cofactor M : ℤ)) ≠ 0 := by omega
  have hab1 : ((iota M a).1 : ZMod M) = ((iota M b).1 : ZMod M) := congrArg Prod.fst hab
  have hab2 : ((iota M a).2 : ZMod (longModulus M)) = ((iota M b).2 : ZMod (longModulus M)) :=
    congrArg Prod.snd hab
  have e1 : ((iota M a).1 : ZMod M) = (((2 * (a.2.val : ℤ) - a.1.val : ℤ)) : ZMod M) := rfl
  have e1' : ((iota M b).1 : ZMod M) = (((2 * (b.2.val : ℤ) - b.1.val : ℤ)) : ZMod M) := rfl
  have e2 : ((iota M a).2 : ZMod (longModulus M))
      = (((((cofactor M : ℤ)) * a.2.val : ℤ)) : ZMod (longModulus M)) := rfl
  have e2' : ((iota M b).2 : ZMod (longModulus M))
      = (((((cofactor M : ℤ)) * b.2.val : ℤ)) : ZMod (longModulus M)) := rfl
  rw [e1, e1'] at hab1
  rw [e2, e2'] at hab2
  have h1 : ((M : ℤ)) ∣ ((2 * (b.2.val : ℤ) - b.1.val) - (2 * (a.2.val : ℤ) - a.1.val)) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (2 * (a.2.val : ℤ) - a.1.val)
      (2 * (b.2.val : ℤ) - b.1.val) M).mp hab1
  have h2 : ((longModulus M : ℤ)) ∣ (((cofactor M : ℤ)) * b.2.val - ((cofactor M : ℤ)) * a.2.val) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (((cofactor M : ℤ)) * a.2.val)
      (((cofactor M : ℤ)) * b.2.val) (longModulus M)).mp hab2
  rw [← mul_sub, hnmℤ M, mul_comm ((M : ℤ)) ((cofactor M : ℤ))] at h2
  have hs : ((M : ℤ)) ∣ ((b.2.val : ℤ) - a.2.val) :=
    (Int.mul_dvd_mul_iff_left hco0).mp h2
  have hr : ((M : ℤ)) ∣ ((b.1.val : ℤ) - a.1.val) := by
    obtain ⟨k1, hk1⟩ := hs
    obtain ⟨k2, hk2⟩ := h1
    refine ⟨2 * k1 - k2, ?_⟩
    linear_combination 2 * hk1 - hk2
  refine Prod.ext ?_ ?_
  · exact ZMod.val_injective M
      (nat_eq_of_modEq_lt M _ _ ((Nat.modEq_iff_dvd).mpr hr) (ZMod.val_lt _) (ZMod.val_lt _))
  · exact ZMod.val_injective M
      (nat_eq_of_modEq_lt M _ _ ((Nat.modEq_iff_dvd).mpr hs) (ZMod.val_lt _) (ZMod.val_lt _))

private theorem zmod_nsmul_eq_zero_iff (M N : ℕ) (x : ℤ) :
    M • ((x : ZMod N)) = 0 ↔ ((N : ℤ)) ∣ ((M : ℤ)) * x := by
  constructor
  · intro h
    have eM : ((M : ZMod N)) = ((((M : ℤ)) : ZMod N)) := by push_cast; rfl
    rw [nsmul_eq_mul, eM, ← Int.cast_mul] at h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
  · intro h
    have key : ((((M : ℤ) * x : ℤ)) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
    have eM : ((M : ZMod N)) = ((((M : ℤ)) : ZMod N)) := by push_cast; rfl
    rw [nsmul_eq_mul, eM, ← Int.cast_mul]
    exact key

theorem iota_range_eq_torsion :
    ((iota M).range : Set (G M)) = {g : G M | M • g = 0} := by
  have h4 : (4 : ℕ) ≤ M := Fact.out
  have : NeZero M := NeZero.of_pos (by omega)
  have hco := hcoℤ M
  have hnm := hnmℤ M
  have : NeZero (longModulus M) := by
    refine ⟨fun hc => ?_⟩
    have e0 : ((longModulus M : ℤ)) = 0 := by rw [hc]; simp
    rw [hnm, hco] at e0
    rcases Int.mul_eq_zero.mp e0 with h1 | h2 <;> omega
  ext g
  constructor
  · intro hg
    rw [SetLike.mem_coe] at hg
    obtain ⟨h, rfl⟩ := AddMonoidHom.mem_range.mp hg
    show (M • ((((2 * (h.2.val : ℤ) - h.1.val : ℤ)) : ZMod M),
      (((((cofactor M : ℤ)) * h.2.val : ℤ)) : ZMod (longModulus M)))) = (0, 0)
    rw [Prod.smul_def, Prod.mk_zero_zero]
    refine Prod.ext ?_ ?_
    · exact (zmod_nsmul_eq_zero_iff _ _ _).mpr (dvd_mul_right _ _)
    · exact (zmod_nsmul_eq_zero_iff _ _ _).mpr (by
        refine ⟨(h.2.val : ℤ), ?_⟩
        rw [hnm]
        ring)
  · intro hg
    rw [SetLike.mem_coe, AddMonoidHom.mem_range]
    have hsn : M • (g.2 : ZMod (longModulus M)) = 0 := by
      have := congrArg Prod.snd hg
      simpa using this
    have hgc : (g.2 : ZMod (longModulus M)) = ((((g.2.val : ℤ)) : ZMod (longModulus M))) := by
      simp [ZMod.natCast_val]
    rw [hgc] at hsn
    have hdvd := (zmod_nsmul_eq_zero_iff M (longModulus M) ((g.2.val : ℤ))).mp hsn
    rw [hnm] at hdvd
    have hc0 : ((M : ℤ)) ≠ 0 := by omega
    have hcov : ((cofactor M : ℤ)) ∣ ((g.2.val : ℤ)) := (Int.mul_dvd_mul_iff_left hc0).mp hdvd
    have hvt : ((cofactor M : ℤ)) * (((((g.2.val : ℤ))) / (((cofactor M : ℤ))))) = ((g.2.val : ℤ)) := by
      have e := Int.mul_ediv_add_emod ((g.2.val : ℤ)) ((cofactor M : ℤ))
      rw [Int.emod_eq_zero_of_dvd hcov, add_zero] at e
      exact e
    refine ⟨((((2 * ((g.2.val : ℤ)) / ((cofactor M : ℤ)) - (g.1.val : ℤ) : ℤ)) : ZMod M), (((((g.2.val : ℤ)) / ((cofactor M : ℤ)) : ℤ)) : ZMod M)), ?_⟩
    show coordinate M (2 * (((((((g.2.val : ℤ)) / ((cofactor M : ℤ)) : ℤ)) : ZMod M).val : ℤ)) - (((((2 * ((g.2.val : ℤ)) / ((cofactor M : ℤ)) - (g.1.val : ℤ) : ℤ)) : ZMod M).val : ℤ))) ((((cofactor M : ℤ)) * (((((((g.2.val : ℤ)) / ((cofactor M : ℤ)) : ℤ)) : ZMod M).val : ℤ)))) = g
    rw [ZMod.val_intCast, ZMod.val_intCast]
    have et : ((M : ℤ)) * ((((g.2.val : ℤ)) / ((cofactor M : ℤ))) / ((M : ℤ))) + ((((g.2.val : ℤ)) / ((cofactor M : ℤ))) % ((M : ℤ))) = (((g.2.val : ℤ)) / ((cofactor M : ℤ))) := Int.mul_ediv_add_emod _ _
    have eu : ((M : ℤ)) * ((2 * ((g.2.val : ℤ)) / ((cofactor M : ℤ)) - ((g.1.val : ℤ))) / ((M : ℤ))) + ((2 * ((g.2.val : ℤ)) / ((cofactor M : ℤ)) - ((g.1.val : ℤ))) % ((M : ℤ))) = (2 * ((g.2.val : ℤ)) / ((cofactor M : ℤ)) - ((g.1.val : ℤ))) := Int.mul_ediv_add_emod _ _
    have hco0' : ((cofactor M : ℤ)) ≠ 0 := by have := hcoℤ M; omega
    have hnum : ((2 : ℤ)) * ((g.2.val : ℤ))
        = ((2 : ℤ)) * (((cofactor M : ℤ)) * (((g.2.val : ℤ)) / ((cofactor M : ℤ)))) := by
      rw [hvt]
    have h2T : (((2 : ℤ)) * ((g.2.val : ℤ))) / ((cofactor M : ℤ))
        = ((2 : ℤ)) * (((g.2.val : ℤ)) / ((cofactor M : ℤ))) := by
      rw [hnum, ← mul_assoc, mul_comm ((2 : ℤ)) ((cofactor M : ℤ)), mul_assoc,
        Int.mul_ediv_cancel_left (((2 : ℤ)) * (((g.2.val : ℤ)) / ((cofactor M : ℤ)))) hco0']
    have hcoord : coordinate M (2 * ((((g.2.val : ℤ)) / ((cofactor M : ℤ))) % ((M : ℤ))) - ((2 * ((g.2.val : ℤ)) / ((cofactor M : ℤ)) - ((g.1.val : ℤ))) % ((M : ℤ)))) (((cofactor M : ℤ)) * ((((g.2.val : ℤ)) / ((cofactor M : ℤ))) % ((M : ℤ))))
        = coordinate M ((g.1.val : ℤ)) ((g.2.val : ℤ)) :=
      coordinate_eq_of_dvd
        (a := (2 * ((((g.2.val : ℤ)) / ((cofactor M : ℤ))) % ((M : ℤ))) - ((2 * ((g.2.val : ℤ)) / ((cofactor M : ℤ)) - ((g.1.val : ℤ))) % ((M : ℤ)))))
        (a' := (g.1.val : ℤ))
        (b := (((cofactor M : ℤ)) * ((((g.2.val : ℤ)) / ((cofactor M : ℤ))) % ((M : ℤ)))))
        (b' := (g.2.val : ℤ))
        (ha := ⟨((2 * ((g.2.val : ℤ)) / ((cofactor M : ℤ)) - ((g.1.val : ℤ))) / ((M : ℤ))) - 2 * ((((g.2.val : ℤ)) / ((cofactor M : ℤ))) / ((M : ℤ))), by linear_combination 2 * et - eu - h2T⟩)
        (hb := ⟨-((((g.2.val : ℤ)) / ((cofactor M : ℤ))) / ((M : ℤ))), by
          linear_combination ((cofactor M : ℤ)) * et + hvt + ((((g.2.val : ℤ)) / ((cofactor M : ℤ))) / ((M : ℤ))) * hnm⟩)
    exact hcoord.trans (coordinate_val M g)

def annihilatorGenerator : G M := coordinate M 0 (-(M : ℤ))

theorem epsilonAut_fixes_annihilatorGenerator :
    epsilonAut M (annihilatorGenerator M) = annihilatorGenerator M := by
  unfold annihilatorGenerator
  rw [epsilonAut_coordinate]
  apply coordinate_eq_of_dvd (M := M)
  · exact ⟨-1, by ring⟩
  · refine ⟨-1, ?_⟩
    rw [hnmℤ M, hcoℤ M]
    ring

/- The witness w, using canonical lifts of h=(r,s). -/
def witnessW (h : L2a.Index M) : G M :=
  coordinate M ((h.1.val : ℤ) - h.2.val)
    (((M : ℤ) - 1) * h.1.val - ((M : ℤ) - 2) * h.2.val)

theorem witnessW_epsilon (h : L2a.Index M) :
    epsilonAut M (witnessW M h) = witnessW M h + iota M h := by
  change epsilonAut M (coordinate M _ _) = coordinate M _ _ + coordinate M _ _
  rw [epsilonAut_coordinate, coordinate_add, hcoℤ M]
  apply coordinate_eq_of_dvd (M := M)
  · exact ⟨(h.1.val : ℤ) - h.2.val, by ring⟩
  · refine ⟨(h.1.val : ℤ) - h.2.val, ?_⟩
    rw [hnmℤ M, hcoℤ M]
    ring

end SICLean.L2b

namespace SICLean.L2b

def gaussianLift (M : ℕ) (x y : ℤ) : ℂ :=
  L2a.e M (x ^ 2 + x * y) *
    L2a.e (2 * longModulus M) (((longModulus M : ℤ) + (M : ℤ) - 2) * y ^ 2)

def gaussian (M : ℕ) (g : G M) : ℂ := gaussianLift M g.1.val g.2.val

/- The displayed bicharacter formula, on integer Smith lifts. -/
def pairingLift (M : ℕ) (x y z w : ℤ) : ℂ :=
  L2a.e (longModulus M)
    ((cofactor M : ℤ) * (2 * x * z + x * w + y * z) + ((M : ℤ) - 2) * y * w)

/- ### Generic helper lemmas about `L2a.e` and parity -/

private theorem e_ne_zero (N : ℕ) (t : ℤ) : L2a.e N t ≠ 0 := by
  rw [L2a.e_eq_omega_zpow]
  exact zpow_ne_zero _ (omega_ne_zero N)

/- `e N t = 1` exactly on the multiples of the modulus. -/
private theorem e_eq_one_iff_dvd {N : ℕ} (hN : N ≠ 0) (t : ℤ) :
    L2a.e N t = 1 ↔ ((N : ℕ) : ℤ) ∣ t := by
  rw [L2a.e_eq_omega_zpow]
  constructor
  · intro h
    by_contra hc
    have : NeZero N := ⟨hN⟩
    exact omega_ne_one_of_not_dvd hc h
  · exact omega_zpow_dvd N

/- Rescaling the modulus: `e M z = e N (c * z)` when `N = c * M` with `c, M ≠ 0`. -/
private theorem e_mod_cast (c M N : ℕ) (hc : c ≠ 0) (hM : M ≠ 0) (hN : N = c * M) (z : ℤ) :
    L2a.e M z = L2a.e N ((c : ℤ) * z) := by
  have hc' : ((c : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hc
  have hM' : ((M : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hM
  rw [L2a.e_eq_omega_zpow, L2a.e_eq_omega_zpow, omega_exp, omega_exp, hN]
  push_cast
  apply congrArg Complex.exp
  field_simp

private theorem e_two_eq_neg_one (t : ℤ) : L2a.e 2 t = (-1 : ℂ) ^ t := by
  have h2 : omega 2 = -1 := by
    rw [omega]
    have h : (2 * Real.pi * Complex.I / (2 : ℕ) : ℂ) = Real.pi * Complex.I := by
      push_cast
      field_simp
    rw [h, Complex.exp_mul_I]
    norm_num
  rw [L2a.e_eq_omega_zpow, h2]

private theorem e_pow (N : ℕ) (t : ℤ) : ∀ k : ℕ, L2a.e N (k * t) = (L2a.e N t) ^ k
  | 0 => by simp [L2a.e]
  | k + 1 => by
    push_cast
    rw [add_mul, one_mul, ← L2a.e_mul, e_pow N t k, pow_succ]

private theorem two_dvd_sq_sub_self (t : ℤ) : (2 : ℤ) ∣ t ^ 2 - t := by
  rcases Int.even_or_odd t with ⟨k, hk⟩ | ⟨k, hk⟩
  · refine ⟨2 * k ^ 2 - k, ?_⟩
    subst hk
    ring
  · refine ⟨2 * k ^ 2 + k, ?_⟩
    subst hk
    ring

private theorem two_dvd_mul_consec (t : ℤ) : (2 : ℤ) ∣ t * (t + 1) := by
  have h := two_dvd_sq_sub_self (t + 1)
  have hid : (t + 1) ^ 2 - (t + 1) = t * (t + 1) := by ring
  rwa [hid] at h

/- The quadratic coefficient in the §4.4 formula is always odd. -/
private theorem exists_half_odd (t : ℤ) : ∃ p : ℤ, t ^ 2 - 3 * t + 3 = 2 * p + 1 := by
  rcases Int.even_or_odd t with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨2 * k ^ 2 - 3 * k + 1, by subst hk; ring⟩
  · exact ⟨2 * k ^ 2 - k, by subst hk; ring⟩

/- The quadratic coefficient in the ι formula is always even. -/
private theorem exists_half_even (t : ℤ) : ∃ p : ℤ, t ^ 2 - 5 * t + 8 = 2 * p := by
  rcases Int.even_or_odd t with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨2 * k ^ 2 - 5 * k + 4, by subst hk; ring⟩
  · exact ⟨2 * k ^ 2 - 3 * k + 2, by subst hk; ring⟩

/- Powers of a single `e`-phase divide. -/
private theorem e_div (N : ℕ) (u v p q : ℤ) :
    L2a.e N u * L2a.e N v / (L2a.e N p * L2a.e N q) = L2a.e N (u + v - p - q) := by
  rw [div_eq_mul_inv, mul_inv, L2a.e_inv, L2a.e_inv]
  simp only [L2a.e_mul]
  congr 1
  ring

variable (M : ℕ) [Fact (4 ≤ M)]

/- ### Cast bookkeeping for the Smith coordinates -/

private theorem cofactor_cast : ((cofactor M : ℕ) : ℤ) = (M : ℤ) - 3 := by
  have h4 : 4 ≤ M := Fact.out
  rw [Nat.cast_sub (by omega : (3 : ℕ) ≤ M)]
  push_cast
  ring

private theorem longModulus_cast :
    ((longModulus M : ℕ) : ℤ) = (M : ℤ) * ((M : ℤ) - 3) := by
  rw [Nat.cast_mul, cofactor_cast]

private theorem longModulus_ne : longModulus M ≠ 0 := NeZero.ne _

private theorem cofactor_ne : cofactor M ≠ 0 := NeZero.ne _

private theorem M_ne : M ≠ 0 := NeZero.ne M

/- Converting from modulus `M` up to modulus `2n`. -/
private theorem e_to_2n (s : ℤ) :
    L2a.e M s = L2a.e (2 * longModulus M) (2 * (cofactor M : ℤ) * s) :=
  e_mod_cast (2 * cofactor M) M (2 * longModulus M)
    (by intro h; have := cofactor_ne M; omega) (M_ne M)
    (by rw [show longModulus M = cofactor M * M from Nat.mul_comm M (cofactor M)]; ring) s

/- The sign hidden in a half-period: `(-1) ^ t = e_{2n} (n * t)`. -/
private theorem neg_one_eq (t : ℤ) :
    (-1 : ℂ) ^ t = L2a.e (2 * longModulus M) ((longModulus M : ℤ) * t) := by
  rw [← e_two_eq_neg_one, e_mod_cast (longModulus M) 2 (2 * longModulus M) (longModulus_ne M)
    two_ne_zero (by ring)]

theorem longModulus_even : Even (longModulus M) := by
  have h4 : 4 ≤ M := Fact.out
  rcases Nat.even_or_odd M with ⟨k, hk⟩ | ⟨k, hk⟩
  · refine ⟨k * (M - 3), ?_⟩
    rw [show longModulus M = M * (M - 3) from rfl, hk]
    ring
  · refine ⟨M * (k - 1), ?_⟩
    have hsub : 2 * k + 1 - 3 = 2 * (k - 1) := by omega
    rw [show longModulus M = M * (M - 3) from rfl, hk, hsub]
    ring

/- The Gaussian is computed on any integer lift of the Smith coordinates. -/
private theorem gaussian_cast_eq (x y : ℤ) :
    gaussian M ((x : ZMod M), (y : ZMod (longModulus M))) = gaussianLift M x y := by
  have hvx : ((M : ℕ) : ℤ) ∣ (((x : ZMod M).val : ℕ) : ℤ) - x := by
    have hv : (((x : ZMod M).val : ℕ) : ℤ) = x % ((M : ℕ) : ℤ) := ZMod.val_intCast x
    refine ⟨-(x / ((M : ℕ) : ℤ)), ?_⟩
    rw [hv]
    linarith [Int.emod_add_mul_ediv x ((M : ℕ) : ℤ)]
  have hvy : ((longModulus M : ℕ) : ℤ) ∣ (((y : ZMod (longModulus M)).val : ℕ) : ℤ) - y := by
    have hv : (((y : ZMod (longModulus M)).val : ℕ) : ℤ) = y % ((longModulus M : ℕ) : ℤ) :=
      ZMod.val_intCast y
    refine ⟨-(y / ((longModulus M : ℕ) : ℤ)), ?_⟩
    rw [hv]
    linarith [Int.emod_add_mul_ediv y ((longModulus M : ℕ) : ℤ)]
  set v : ℤ := (((x : ZMod M).val : ℕ) : ℤ) with hvdef
  set w : ℤ := (((y : ZMod (longModulus M)).val : ℕ) : ℤ) with hwdef
  have hMn : ((M : ℕ) : ℤ) ∣ ((longModulus M : ℕ) : ℤ) := by
    refine ⟨(cofactor M : ℤ), ?_⟩
    push_cast
    ring
  have hd1 : ((M : ℕ) : ℤ) ∣ (v ^ 2 + v * w) - (x ^ 2 + x * y) := by
    have hid : (v ^ 2 + v * w) - (x ^ 2 + x * y)
        = (v - x) * (v + x) + v * (w - y) + (v - x) * y := by ring
    rw [hid]
    exact dvd_add
      (dvd_add (dvd_mul_of_dvd_left hvx _)
        (dvd_trans hMn (dvd_mul_of_dvd_right hvy v)))
      (dvd_mul_of_dvd_left hvx _)
  obtain ⟨k, hk⟩ := hvy
  obtain ⟨k', hk'⟩ := longModulus_even M
  have hk'2 : ((longModulus M : ℕ) : ℤ) = 2 * k' := by
    have := hk'
    push_cast
    linarith
  have hd2 : ((2 * longModulus M : ℕ) : ℤ) ∣
      ((((longModulus M : ℕ) : ℤ) + (M : ℤ) - 2) * w ^ 2) -
        (((longModulus M : ℕ) : ℤ) + (M : ℤ) - 2) * y ^ 2 := by
    have hw2 : w = y + ((longModulus M : ℕ) : ℤ) * k := by linear_combination hk
    have hdiv : ((2 * longModulus M : ℕ) : ℤ) = 2 * (2 * k') := by
      have h2 := hk'2
      push_cast at h2
      push_cast
      linarith
    refine ⟨(((longModulus M : ℕ) : ℤ) + (M : ℤ) - 2) * (y * k + k' * k ^ 2), ?_⟩
    rw [hw2, hk'2, hdiv]
    ring
  show L2a.e M (v ^ 2 + v * w) *
      L2a.e (2 * longModulus M) ((((longModulus M : ℕ) : ℤ) + (M : ℤ) - 2) * w ^ 2) =
    gaussianLift M x y
  rw [L2a.e_eq_of_dvd hd1, L2a.e_eq_of_dvd hd2]
  rfl

theorem gaussianLift_periodic (x y a b : ℤ) :
    gaussianLift M (x + (M : ℤ) * a) (y + (longModulus M : ℤ) * b) =
      gaussianLift M x y := by
  have h1 : (((x + (M : ℤ) * a : ℤ)) : ZMod M) = ((x : ZMod M)) := by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    exact ⟨-a, by ring⟩
  have h2 : (((y + (longModulus M : ℤ) * b : ℤ)) : ZMod (longModulus M)) =
      ((y : ZMod (longModulus M))) := by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    exact ⟨-b, by ring⟩
  rw [← gaussian_cast_eq, ← gaussian_cast_eq, h1, h2, gaussian_cast_eq]

/- Any group element is its own canonical lift of the Smith coordinates. -/
private theorem G_eq_val_cast (g : G M) :
    g = (((g.1.val : ℤ) : ZMod M), ((g.2.val : ℤ) : ZMod (longModulus M))) := by
  refine Prod.ext ?_ ?_
  · exact ((ZMod.intCast_eq_iff M ((g.1.val : ℕ) : ℤ) g.1).2 ⟨0, by simp⟩).symm
  · exact ((ZMod.intCast_eq_iff (longModulus M) ((g.2.val : ℕ) : ℤ) g.2).2 ⟨0, by simp⟩).symm


omit [Fact (4 ≤ M)] in
theorem gaussian_ne_zero (g : G M) : gaussian M g ≠ 0 := by
  show L2a.e M _ * L2a.e (2 * longModulus M) _ ≠ 0
  exact mul_ne_zero (e_ne_zero M _) (e_ne_zero (2 * longModulus M) _)

omit [Fact (4 ≤ M)] in
theorem gaussian_zero : gaussian M 0 = 1 := by
  simp [gaussian, gaussianLift, ZMod.val_zero, L2a.e]

theorem gaussian_even (g : G M) : gaussian M (-g) = gaussian M g := by
  rw [G_eq_val_cast M g]
  have hneg : (-(((g.1.val : ℤ) : ZMod M), ((g.2.val : ℤ) : ZMod (longModulus M))) :
      G M) = (((Int.cast (-(g.1.val : ℤ))) : ZMod M),
        ((Int.cast (-(g.2.val : ℤ))) : ZMod (longModulus M))) := by
    refine Prod.ext ?_ ?_
    · simp [Int.cast_neg]
    · simp [Int.cast_neg]
  rw [hneg, gaussian_cast_eq, gaussian_cast_eq]
  show L2a.e M _ * L2a.e (2 * longModulus M) _ = L2a.e M _ * L2a.e (2 * longModulus M) _
  congr 1
  · congr 1
    ring
  · congr 1
    ring

/- ### The bicharacter on integer Smith lifts -/

omit [Fact (4 ≤ M)] in
private theorem cast_pair_add (x y z w : ℤ) :
    ((x : ZMod M), (y : ZMod (longModulus M))) + ((z : ZMod M), (w : ZMod (longModulus M))) =
      (((x + z : ℤ) : ZMod M), ((y + w : ℤ) : ZMod (longModulus M))) := by
  refine Prod.ext ?_ ?_
  · simp
  · simp

/- Down to the long modulus: `e_M s = e_n (m s)`. -/
private theorem e_to_n (s : ℤ) :
    L2a.e M s = L2a.e (longModulus M) ((cofactor M : ℤ) * s) :=
  e_mod_cast (cofactor M) M (longModulus M) (cofactor_ne M) (M_ne M)
    (Nat.mul_comm M (cofactor M)) s

private theorem e_n_to_2n (s : ℤ) :
    L2a.e (longModulus M) s = L2a.e (2 * longModulus M) (2 * s) :=
  e_mod_cast 2 (longModulus M) (2 * longModulus M) two_ne_zero (longModulus_ne M) rfl s

omit [Fact (4 ≤ M)] in
private theorem two_longModulus_cast :
    ((2 * longModulus M : ℕ) : ℤ) = 2 * ((longModulus M : ℕ) : ℤ) := by
  rw [Nat.cast_mul, Nat.cast_two]

/- The displayed bicharacter formula, on integer lifts. -/
private theorem metricPairing_lift (x y z w : ℤ) :
    metricPairing (gaussian M) ((x : ZMod M), (y : ZMod (longModulus M)))
        ((z : ZMod M), (w : ZMod (longModulus M))) =
      L2a.e (longModulus M)
        ((cofactor M : ℤ) * (2 * x * z + x * w + y * z) + ((M : ℤ) - 2) * y * w) := by
  show gaussian M (((x : ZMod M), (y : ZMod (longModulus M))) +
      ((z : ZMod M), (w : ZMod (longModulus M)))) /
    (gaussian M ((x : ZMod M), (y : ZMod (longModulus M))) *
      gaussian M ((z : ZMod M), (w : ZMod (longModulus M)))) = _
  rw [cast_pair_add M x y z w, gaussian_cast_eq, gaussian_cast_eq, gaussian_cast_eq]
  show L2a.e M ((x + z) ^ 2 + (x + z) * (y + w)) *
      L2a.e (2 * longModulus M)
        ((((longModulus M : ℕ) : ℤ) + (M : ℤ) - 2) * (y + w) ^ 2) /
    (L2a.e M (x ^ 2 + x * y) *
      L2a.e (2 * longModulus M) ((((longModulus M : ℕ) : ℤ) + (M : ℤ) - 2) * y ^ 2) *
    (L2a.e M (z ^ 2 + z * w) *
      L2a.e (2 * longModulus M) ((((longModulus M : ℕ) : ℤ) + (M : ℤ) - 2) * w ^ 2))) =
    L2a.e (longModulus M)
      ((cofactor M : ℤ) * (2 * x * z + x * w + y * z) + ((M : ℤ) - 2) * y * w)
  rw [e_to_2n M, e_to_2n M, e_to_2n M, e_n_to_2n M]
  rw [div_eq_mul_inv, mul_inv, mul_inv, mul_inv]
  rw [L2a.e_inv, L2a.e_inv, L2a.e_inv, L2a.e_inv]
  simp only [L2a.e_mul]
  refine L2a.e_eq_of_dvd ⟨y * w, ?_⟩
  rw [cofactor_cast M, two_longModulus_cast, longModulus_cast]
  ring

theorem concrete_pairing_formula (g h : G M) :
    metricPairing (gaussian M) g h =
      pairingLift M g.1.val g.2.val h.1.val h.2.val := by
  have key := metricPairing_lift M g.1.val g.2.val h.1.val h.2.val
  rw [← G_eq_val_cast M g, ← G_eq_val_cast M h] at key
  exact key


theorem concrete_isMetricGaussian : IsMetricGaussian (gaussian M) := by
  refine ⟨gaussian_ne_zero M, gaussian_even M, ?_, ?_, ?_⟩
  · intro x y z
    rw [G_eq_val_cast M x, G_eq_val_cast M y, G_eq_val_cast M z, cast_pair_add M,
      metricPairing_lift M, metricPairing_lift M, metricPairing_lift M, L2a.e_mul]
    exact L2a.e_eq_of_dvd ⟨0, by rw [cofactor_cast M]; ring⟩
  · intro x y z
    rw [G_eq_val_cast M x, G_eq_val_cast M y, G_eq_val_cast M z, cast_pair_add M,
      metricPairing_lift M, metricPairing_lift M, metricPairing_lift M, L2a.e_mul]
    exact L2a.e_eq_of_dvd ⟨0, by rw [cofactor_cast M]; ring⟩
  · intro x hx
    have e10 := hx (((1 : ℤ) : ZMod M), ((0 : ℤ) : ZMod (longModulus M)))
    rw [G_eq_val_cast M x, metricPairing_lift M] at e10
    have e01 := hx (((0 : ℤ) : ZMod M), ((1 : ℤ) : ZMod (longModulus M)))
    rw [G_eq_val_cast M x, metricPairing_lift M] at e01
    obtain ⟨k1, hk1⟩ := (e_eq_one_iff_dvd (longModulus_ne M) _).1 e10
    rw [cofactor_cast M, longModulus_cast M] at hk1
    have h4 : 4 ≤ M := Fact.out
    have hm3 : ((M : ℤ) - 3) ≠ 0 := by
      rw [← cofactor_cast M]
      exact_mod_cast (cofactor_ne M)
    have hM : ((M : ℕ) : ℤ) ∣ 2 * ((x.1.val : ℕ) : ℤ) + ((x.2.val : ℕ) : ℤ) := by
      refine ⟨k1, ?_⟩
      have hc : ((M : ℤ) - 3) * (2 * ((x.1.val : ℕ) : ℤ) + ((x.2.val : ℕ) : ℤ)) =
          ((M : ℤ) - 3) * ((M : ℤ) * k1) := by
        linear_combination hk1
      exact mul_left_cancel₀ hm3 hc
    obtain ⟨k2, hk2⟩ := (e_eq_one_iff_dvd (longModulus_ne M) _).1 e01
    have hn : ((longModulus M : ℕ) : ℤ) ∣
        ((cofactor M : ℤ) * ((x.1.val : ℕ) : ℤ) + ((M : ℤ) - 2) * ((x.2.val : ℕ) : ℤ)) :=
      ⟨k2, by linear_combination hk2⟩
    obtain ⟨c1, hc1⟩ := hM
    obtain ⟨c2, hc2⟩ := hn
    rw [longModulus_cast M, cofactor_cast M] at hc2
    have hdivX : ((M : ℕ) : ℤ) ∣ ((x.1.val : ℕ) : ℤ) := by
      refine ⟨-((M : ℤ) - 2) * c1 + ((M : ℤ) - 3) * c2 + (x.1.val : ℕ), ?_⟩
      linear_combination -((M : ℤ) - 2) * hc1 + hc2
    have hX0 : ((x.1.val : ℕ) : ℤ) = 0 :=
      (Int.emod_eq_of_lt (by exact_mod_cast Nat.zero_le _)
        (by exact_mod_cast ZMod.val_lt x.1)).symm.trans (Int.emod_eq_zero_of_dvd hdivX)
    rw [hX0] at hc1
    have hdivY : ((M : ℕ) : ℤ) ∣ ((x.2.val : ℕ) : ℤ) :=
      ⟨c1, by linear_combination hc1⟩
    obtain ⟨y', hy'⟩ := hdivY
    rw [hX0, hy'] at hc2
    have hMne : ((M : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (M_ne M)
    have hmy : ((M : ℤ) - 3) * c2 = ((M : ℤ) - 2) * y' :=
      mul_left_cancel₀ hMne (by linear_combination -hc2)
    have hdivY2 : ((longModulus M : ℕ) : ℤ) ∣ ((x.2.val : ℕ) : ℤ) := by
      refine ⟨c2 - y', ?_⟩
      rw [longModulus_cast M]
      linear_combination -(M : ℤ) * hmy + hy'
    have hY0 : ((x.2.val : ℕ) : ℤ) = 0 :=
      (Int.emod_eq_of_lt (by exact_mod_cast Nat.zero_le _)
        (by exact_mod_cast ZMod.val_lt x.2)).symm.trans (Int.emod_eq_zero_of_dvd hdivY2)
    exact Prod.ext ((ZMod.val_eq_zero _).1 (by exact_mod_cast hX0))
      ((ZMod.val_eq_zero _).1 (by exact_mod_cast hY0))

theorem epsilonAut_preserves_gaussian (g : G M) :
    gaussian M (epsilonAut M g) = gaussian M g := by
  show gaussian M (coordinate M (((g.1.val : ℕ) : ℤ) + ((g.2.val : ℕ) : ℤ))
      ((cofactor M : ℤ) * ((g.1.val : ℕ) : ℤ) + ((M : ℤ) - 2) * ((g.2.val : ℕ) : ℤ))) =
    gaussian M g
  simp only [coordinate]
  rw [gaussian_cast_eq]
  show L2a.e M ((((g.1.val : ℕ) : ℤ) + ((g.2.val : ℕ) : ℤ)) ^ 2 +
      (((g.1.val : ℕ) : ℤ) + ((g.2.val : ℕ) : ℤ)) *
        ((cofactor M : ℤ) * ((g.1.val : ℕ) : ℤ) + ((M : ℤ) - 2) * ((g.2.val : ℕ) : ℤ))) *
      L2a.e (2 * longModulus M)
        ((((longModulus M : ℕ) : ℤ) + (M : ℤ) - 2) *
          ((cofactor M : ℤ) * ((g.1.val : ℕ) : ℤ) +
            ((M : ℤ) - 2) * ((g.2.val : ℕ) : ℤ)) ^ 2) =
    L2a.e M (((g.1.val : ℕ) : ℤ) ^ 2 + ((g.1.val : ℕ) : ℤ) * ((g.2.val : ℕ) : ℤ)) *
      L2a.e (2 * longModulus M)
        ((((longModulus M : ℕ) : ℤ) + (M : ℤ) - 2) * ((g.2.val : ℕ) : ℤ) ^ 2)
  rw [e_to_2n M, e_to_2n M, L2a.e_mul, L2a.e_mul]
  obtain ⟨p1, hp1⟩ := two_dvd_mul_consec (((M : ℤ) - 3))
  obtain ⟨p2, hp2⟩ := two_dvd_mul_consec (((M : ℤ) - 2))
  refine L2a.e_eq_of_dvd ⟨p1 * ((g.1.val : ℕ) : ℤ) ^ 2 +
      ((M : ℤ) - 2) * ((M : ℤ) - 2) * ((g.1.val : ℕ) : ℤ) * ((g.2.val : ℕ) : ℤ) +
      p2 * ((g.2.val : ℕ) : ℤ) ^ 2, ?_⟩
  rw [two_longModulus_cast, longModulus_cast, cofactor_cast]
  linear_combination ((M : ℤ) * ((M : ℤ) - 3)) *
    (hp1 * ((g.1.val : ℕ) : ℤ) ^ 2 + hp2 * ((g.2.val : ℕ) : ℤ) ^ 2)

/- Exact agreement with L2a's e_M(i²−ij+j²), with its positive sign. -/
theorem gaussian_iota (h : L2a.Index M) :
    gaussian M (iota M h) = L2a.gaussian M h := by
  show gaussian M (coordinate M (2 * ((h.2.val : ℕ) : ℤ) - ((h.1.val : ℕ) : ℤ))
      ((cofactor M : ℤ) * ((h.2.val : ℕ) : ℤ))) = L2a.gaussian M h
  simp only [coordinate]
  rw [gaussian_cast_eq]
  show L2a.e M ((2 * ((h.2.val : ℕ) : ℤ) - ((h.1.val : ℕ) : ℤ)) ^ 2 +
      (2 * ((h.2.val : ℕ) : ℤ) - ((h.1.val : ℕ) : ℤ)) *
        ((cofactor M : ℤ) * ((h.2.val : ℕ) : ℤ))) *
      L2a.e (2 * longModulus M)
        ((((longModulus M : ℕ) : ℤ) + (M : ℤ) - 2) *
          ((cofactor M : ℤ) * ((h.2.val : ℕ) : ℤ)) ^ 2) =
    L2a.e M (((h.1.val : ℕ) : ℤ) ^ 2 - ((h.1.val : ℕ) : ℤ) * ((h.2.val : ℕ) : ℤ) +
      ((h.2.val : ℕ) : ℤ) ^ 2)
  rw [e_to_2n M, e_to_2n M, L2a.e_mul]
  obtain ⟨p, hp⟩ := exists_half_even ((M : ℕ) : ℤ)
  refine L2a.e_eq_of_dvd ⟨-((h.1.val : ℕ) : ℤ) * ((h.2.val : ℕ) : ℤ) +
      p * ((h.2.val : ℕ) : ℤ) ^ 2, ?_⟩
  rw [two_longModulus_cast, longModulus_cast, cofactor_cast]
  linear_combination ((M : ℤ) * ((M : ℤ) - 3)) * (((h.2.val : ℕ) : ℤ) ^ 2) * hp


theorem pairing_mixed (g : G M) (h : L2a.Index M) :
    metricPairing (gaussian M) g (iota M h) =
      L2a.e M ((g.1.val : ℤ) * ((h.2.val : ℤ) - 2 * h.1.val) -
        (g.2.val : ℤ) * h.1.val) := by
  have hiota : iota M h = coordinate M (2 * ((h.2.val : ℕ) : ℤ) - ((h.1.val : ℕ) : ℤ))
      ((cofactor M : ℤ) * ((h.2.val : ℕ) : ℤ)) := rfl
  rw [hiota]
  simp only [coordinate]
  nth_rw 1 [G_eq_val_cast M g]
  rw [metricPairing_lift M ((g.1.val : ℕ) : ℤ) ((g.2.val : ℕ) : ℤ)
      (2 * ((h.2.val : ℕ) : ℤ) - ((h.1.val : ℕ) : ℤ))
      ((cofactor M : ℤ) * ((h.2.val : ℕ) : ℤ)), e_n_to_2n M, e_to_2n M]
  refine L2a.e_eq_of_dvd ⟨((h.2.val : ℕ) : ℤ) *
      (((g.1.val : ℕ) : ℤ) + ((g.2.val : ℕ) : ℤ)), ?_⟩
  rw [two_longModulus_cast, longModulus_cast, cofactor_cast]
  ring

theorem pairing_witnessW (h k : L2a.Index M) :
    metricPairing (gaussian M) (witnessW M h) (iota M k) =
      L2a.e M (-(k.1.val : ℤ) * h.1.val +
        (k.2.val : ℤ) * ((h.1.val : ℤ) - h.2.val)) := by
  have hw : witnessW M h = coordinate M (((h.1.val : ℕ) : ℤ) - ((h.2.val : ℕ) : ℤ))
      (((M : ℤ) - 1) * ((h.1.val : ℕ) : ℤ) - ((M : ℤ) - 2) * ((h.2.val : ℕ) : ℤ)) := rfl
  have hiota : iota M k = coordinate M (2 * ((k.2.val : ℕ) : ℤ) - ((k.1.val : ℕ) : ℤ))
      ((cofactor M : ℤ) * ((k.2.val : ℕ) : ℤ)) := rfl
  rw [hw, hiota]
  simp only [coordinate]
  rw [metricPairing_lift M (((h.1.val : ℕ) : ℤ) - ((h.2.val : ℕ) : ℤ))
      (((M : ℤ) - 1) * ((h.1.val : ℕ) : ℤ) - ((M : ℤ) - 2) * ((h.2.val : ℕ) : ℤ))
      (2 * ((k.2.val : ℕ) : ℤ) - ((k.1.val : ℕ) : ℤ))
      ((cofactor M : ℤ) * ((k.2.val : ℕ) : ℤ)), e_n_to_2n M, e_to_2n M]
  refine L2a.e_eq_of_dvd ⟨((M : ℤ) * ((h.1.val : ℕ) : ℤ) * ((k.2.val : ℕ) : ℤ) -
      ((M : ℤ) - 1) * ((h.2.val : ℕ) : ℤ) * ((k.2.val : ℕ) : ℤ) -
      ((h.1.val : ℕ) : ℤ) * ((k.1.val : ℕ) : ℤ) +
      ((h.2.val : ℕ) : ℤ) * ((k.1.val : ℕ) : ℤ)), ?_⟩
  rw [two_longModulus_cast, longModulus_cast, cofactor_cast]
  ring

omit [Fact (4 ≤ M)] in
private theorem smul_cast_pair (t x y : ℤ) :
    t • (((x : ZMod M), (y : ZMod (longModulus M)))) =
      ((((t * x : ℤ) : ZMod M), ((t * y : ℤ) : ZMod (longModulus M)))) := by
  simp [Prod.smul_def, zsmul_eq_mul, Int.cast_mul]

/- Converting from modulus `cofactor M` up to modulus `n`. -/
private theorem e_m_to_n (z : ℤ) :
    L2a.e (cofactor M) z = L2a.e (longModulus M) ((M : ℤ) * z) :=
  e_mod_cast M (cofactor M) (longModulus M) (M_ne M) (cofactor_ne M) rfl z

theorem pairing_annihilatorGenerator (j : ℤ) (g : G M) :
    metricPairing (gaussian M) (j • annihilatorGenerator M) g =
      L2a.e (cofactor M) (-j * (g.2.val : ℤ)) := by
  have hgen : annihilatorGenerator M = coordinate M 0 (-(M : ℤ)) := rfl
  rw [hgen]
  simp only [coordinate]
  rw [smul_cast_pair M j 0 (-(M : ℤ))]
  nth_rw 1 [G_eq_val_cast M g]
  rw [metricPairing_lift M (j * 0) (j * (-(M : ℤ))) ((g.1.val : ℕ) : ℤ)
      ((g.2.val : ℕ) : ℤ), e_m_to_n M]
  refine L2a.e_eq_of_dvd ⟨-j * (((g.1.val : ℕ) : ℤ) + ((g.2.val : ℕ) : ℤ)), ?_⟩
  rw [longModulus_cast, cofactor_cast]
  ring

/- If `c` divides both the modulus and `x`, it divides the reduced value of `x`. -/
private theorem dvd_val_cast {N : ℕ} [NeZero N] (x c : ℤ) (hcN : c ∣ ((N : ℕ) : ℤ))
    (hcx : c ∣ x) : c ∣ ((((x : ZMod N).val : ℕ) : ℤ)) := by
  have hv : ((((x : ZMod N).val : ℕ) : ℤ)) = x % ((N : ℕ) : ℤ) := ZMod.val_intCast x
  obtain ⟨k, hk⟩ := hcx
  obtain ⟨l, hl⟩ := hcN
  rw [hv]
  refine ⟨k - (x / ((N : ℕ) : ℤ)) * l, ?_⟩
  linear_combination Int.mul_ediv_add_emod x ((N : ℕ) : ℤ) + hk - (x / ((N : ℕ) : ℤ)) * hl

/- The annihilator of H is cyclic even when the pairing on H is degenerate. -/
theorem orthogonal_iota :
    {g : G M | ∀ h : L2a.Index M, metricPairing (gaussian M) g (iota M h) = 1} =
      (AddSubgroup.zmultiples (annihilatorGenerator M) : Set (G M)) := by
  have hgen : annihilatorGenerator M = coordinate M 0 (-(M : ℤ)) := rfl
  ext g
  simp only [SetLike.mem_coe]
  refine ⟨fun hg => ?_, fun hmem h => ?_⟩
  · have h4 : 4 ≤ M := Fact.out
    have : Fact (1 < M) := ⟨by have := Fact.out (p := 4 ≤ M); omega⟩
    have hv2 : (((((0 : ZMod M), (1 : ZMod M)) : L2a.Index M).2.val : ℕ) : ℤ) = 1 := by
      show (((1 : ZMod M).val : ℕ) : ℤ) = 1
      exact_mod_cast ZMod.val_one M
    have hv1 : (((((0 : ZMod M), (1 : ZMod M)) : L2a.Index M).1.val : ℕ) : ℤ) = 0 := by
      show (((0 : ZMod M).val : ℕ) : ℤ) = 0
      simp
    have hA := hg (((0 : ZMod M), (1 : ZMod M)) : L2a.Index M)
    rw [pairing_mixed M g, hv2, hv1] at hA
    obtain ⟨k1, hk1⟩ := (e_eq_one_iff_dvd (M_ne M) _).1 hA
    ring_nf at hk1
    have hX0 : ((g.1.val : ℕ) : ℤ) = 0 := by
      have hlt : ((g.1.val : ℕ) : ℤ) < ((M : ℕ) : ℤ) := by
        exact_mod_cast ZMod.val_lt g.1
      have hge : (0 : ℤ) ≤ ((g.1.val : ℕ) : ℤ) := by exact_mod_cast Nat.zero_le _
      have hMpos : (0 : ℤ) < ((M : ℕ) : ℤ) := by omega
      have hk10 : k1 = 0 := by
        rcases lt_trichotomy k1 0 with hk | hk | hk
        · have hneg : ((M : ℕ) : ℤ) * k1 < 0 := mul_neg_of_pos_of_neg hMpos hk
          omega
        · exact hk
        · have hle : ((M : ℕ) : ℤ) ≤ ((M : ℕ) : ℤ) * k1 := by
            nlinarith
          omega
      rw [hk10, mul_zero] at hk1
      omega
    have hv2' : (((((1 : ZMod M), (0 : ZMod M)) : L2a.Index M).2.val : ℕ) : ℤ) = 0 := by
      show (((0 : ZMod M).val : ℕ) : ℤ) = 0
      simp
    have hv1' : (((((1 : ZMod M), (0 : ZMod M)) : L2a.Index M).1.val : ℕ) : ℤ) = 1 := by
      show (((1 : ZMod M).val : ℕ) : ℤ) = 1
      exact_mod_cast ZMod.val_one M
    have hB := hg (((1 : ZMod M), (0 : ZMod M)) : L2a.Index M)
    rw [pairing_mixed M g, hv2', hv1'] at hB
    obtain ⟨k2, hk2⟩ := (e_eq_one_iff_dvd (M_ne M) _).1 hB
    ring_nf at hk2
    rw [hX0] at hk2
    ring_nf at hk2
    obtain ⟨t, ht⟩ : ((M : ℕ) : ℤ) ∣ ((g.2.val : ℕ) : ℤ) := ⟨-k2, by linear_combination -hk2⟩
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨-t, ?_⟩
    have hgt : g = coordinate M 0 ((M : ℤ) * t) := by
      rw [G_eq_val_cast M g]
      simp only [coordinate]
      refine Prod.ext ?_ ?_
      · rw [hX0]
      · rw [ht]
    rw [hgt, hgen]
    simp only [coordinate]
    rw [smul_cast_pair M (-t) 0 (-(M : ℤ))]
    refine Prod.ext ?_ ?_
    · simp
    · rw [Int.neg_mul_neg, Int.mul_comm t ((M : ℕ) : ℤ)]
  · obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
    have hiota : iota M h = coordinate M (2 * ((h.2.val : ℕ) : ℤ) - ((h.1.val : ℕ) : ℤ))
        ((cofactor M : ℤ) * ((h.2.val : ℕ) : ℤ)) := rfl
    rw [← hz, pairing_annihilatorGenerator M z (iota M h), hiota,
      e_eq_one_iff_dvd (cofactor_ne M)]
    simp only [coordinate]
    refine dvd_mul_of_dvd_right ?_ (-z)
    exact dvd_val_cast ((cofactor M : ℤ) * ((h.2.val : ℕ) : ℤ)) ((cofactor M : ℕ) : ℤ)
      (by refine ⟨((M : ℕ) : ℤ), ?_⟩; rw [longModulus_cast M, cofactor_cast M]; ring)
      ⟨((h.2.val : ℕ) : ℤ), rfl⟩
private theorem e_pow_nat {N : ℕ} (k : ℤ) (n : ℕ) :
    L2a.e N (((n : ℕ) : ℤ) * k) = (L2a.e N k) ^ n := by
  induction n with
  | zero => simp [L2a.e]
  | succ n ih =>
    have hcast : (((n + 1 : ℕ) : ℤ) * k) = (((n : ℕ) : ℤ) * k) + k := by
      push_cast
      ring
    rw [hcast, ← L2a.e_mul, ih, pow_succ]

private theorem nsmul_val' {n : ℕ} [NeZero n] (k : ℕ) (a : ZMod n) :
    ((k • a : ZMod n)).val = k * a.val % n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [add_smul, one_smul, ZMod.val_add, ih, Nat.add_comm (k * a.val % n) a.val,
      Nat.add_mod_mod, Nat.add_mul, one_mul, Nat.add_comm a.val (k * a.val)]

omit [Fact (4 ≤ M)] in
private theorem zsmul_cast_nat (n : ℕ) (a : G M) :
    ((n : ℕ) : ℤ) • a = n • a := by
  simp

private theorem mem_range_iff (g : G M) :
    g ∈ (iota M).range ↔ ((cofactor M : ℕ) : ℤ) ∣ ((g.2.val : ℕ) : ℤ) := by
  have hset := iota_range_eq_torsion M
  constructor
  · intro h
    have h0 : ((M : ℕ) • g : G M) = 0 := by
      have h' : g ∈ ((iota M).range : Set (G M)) := h
      rw [hset] at h'
      exact h'
    have hs : ((M : ℕ) • g.2 : ZMod (longModulus M)) = 0 := by
      have h1 := congrArg Prod.snd h0
      simpa using h1
    have hv0 : M * g.2.val % (longModulus M) = 0 := by
      have h2 := congrArg ZMod.val hs
      rwa [nsmul_val', ZMod.val_zero] at h2
    have hdd : (longModulus M) ∣ (M * g.2.val) := Nat.dvd_of_mod_eq_zero hv0
    exact (Int.natCast_dvd_natCast).mpr
      (Nat.dvd_of_mul_dvd_mul_left (by have := Fact.out (p := 4 ≤ M); omega) hdd)
  · intro hdvd
    have h' : g ∈ {g : G M | (M : ℕ) • g = 0} := by
      show ((M : ℕ) • g : G M) = 0
      have hd : (cofactor M : ℕ) ∣ g.2.val := Int.natCast_dvd_natCast.mp hdvd
      refine Prod.ext ?_ ?_
      · show ((M : ℕ) • g.1 : ZMod M) = 0
        apply ZMod.val_injective
        rw [nsmul_val', Nat.mul_mod_right, ZMod.val_zero]
      · show ((M : ℕ) • g.2 : ZMod (longModulus M)) = 0
        apply ZMod.val_injective
        rw [nsmul_val', ZMod.val_zero]
        exact Nat.mod_eq_zero_of_dvd (mul_dvd_mul_left M hd)
    rw [← hset] at h'
    exact h'

/- The averaging step in (40). The sum has one term when M=4. -/
theorem character_filter (g : G M) :
    (∑ j : Fin (cofactor M),
      metricPairing (gaussian M) (j.val • annihilatorGenerator M) g) /
        (cofactor M : ℂ) = if g ∈ (iota M).range then 1 else 0 := by
  have hmne : ((cofactor M : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (cofactor_ne M)
  have hterm : ∀ j : Fin (cofactor M),
      metricPairing (gaussian M) (j.val • annihilatorGenerator M) g =
        L2a.e (cofactor M) (-((j.val : ℕ) : ℤ) * ((g.2.val : ℕ) : ℤ)) := by
    intro j
    rw [← zsmul_cast_nat]
    exact pairing_annihilatorGenerator M ((j.val : ℕ) : ℤ) g
  rw [Finset.sum_congr rfl (fun j _ => hterm j),
    Fin.sum_univ_eq_sum_range
      (fun i => L2a.e (cofactor M) (-((i : ℕ) : ℤ) * ((g.2.val : ℕ) : ℤ)))]
  set c : ℂ := L2a.e (cofactor M) (-((g.2.val : ℕ) : ℤ)) with hc
  have hpow : ∀ i : ℕ,
      L2a.e (cofactor M) (-((i : ℕ) : ℤ) * ((g.2.val : ℕ) : ℤ)) = c ^ i := by
    intro i
    have hneg : (-((i : ℕ) : ℤ) * ((g.2.val : ℕ) : ℤ)) =
        ((i : ℕ) : ℤ) * (-((g.2.val : ℕ) : ℤ)) := by ring
    rw [hneg, e_pow_nat, ← hc]
  rw [Finset.sum_congr rfl (fun i _ => hpow i)]
  have hcm : c ^ (cofactor M) = 1 := by
    rw [hc, ← e_pow_nat]
    exact (e_eq_one_iff_dvd (cofactor_ne M) _).2 ⟨-((g.2.val : ℕ) : ℤ), rfl⟩
  by_cases hc1 : c = 1
  · have hdvd : ((cofactor M : ℕ) : ℤ) ∣ ((g.2.val : ℕ) : ℤ) := by
      have h1 := (e_eq_one_iff_dvd (cofactor_ne M) _).1 hc1
      obtain ⟨k, hk⟩ := h1
      exact ⟨-k, by linear_combination -hk⟩
    have hsum : (∑ i ∈ Finset.range (cofactor M), c ^ i) = ((cofactor M : ℕ) : ℂ) := by
      rw [hc1]
      simp
    rw [if_pos ((mem_range_iff M g).mpr hdvd), hsum, div_self hmne]
  · have hnd : ¬ (((cofactor M : ℕ) : ℤ) ∣ ((g.2.val : ℕ) : ℤ)) := by
      intro hdvd
      apply hc1
      rw [hc]
      refine (e_eq_one_iff_dvd (cofactor_ne M) _).2 ?_
      obtain ⟨k, hk⟩ := hdvd
      exact ⟨-k, by linear_combination -hk⟩
    rw [if_neg (fun hin => hnd ((mem_range_iff M g).mp hin)), geom_sum_eq hc1, hcm, sub_self,
      zero_div, zero_div]

theorem sum_character_filter (f : G M → ℂ) :
    (∑ j : Fin (cofactor M), ∑ g : G M,
      f g * metricPairing (gaussian M) (j.val • annihilatorGenerator M) g) =
      (cofactor M : ℂ) * ∑ h : L2a.Index M, f (iota M h) := by
  have hmne : ((cofactor M : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (cofactor_ne M)
  have ht2 : ∀ (j : Fin (cofactor M)) (g : G M),
      metricPairing (gaussian M) (j.val • annihilatorGenerator M) g =
        L2a.e (cofactor M) (-((j.val : ℕ) : ℤ) * ((g.2.val : ℕ) : ℤ)) := by
    intro j g
    rw [← zsmul_cast_nat]
    exact pairing_annihilatorGenerator M ((j.val : ℕ) : ℤ) g
  have hcf : ∀ g : G M,
      (∑ j : Fin (cofactor M),
        L2a.e (cofactor M) (-((j.val : ℕ) : ℤ) * ((g.2.val : ℕ) : ℤ))) =
        ((cofactor M : ℕ) : ℂ) * (if g ∈ (iota M).range then 1 else 0) := by
    intro g
    have h0 := character_filter M g
    rw [Finset.sum_congr rfl (fun j _ => ht2 j g)] at h0
    rw [← h0, mul_div_cancel₀ _ hmne]
  have hint : ∀ g : G M,
      f g * (((cofactor M : ℕ) : ℂ) * (if g ∈ (iota M).range then 1 else 0)) =
        ((cofactor M : ℕ) : ℂ) * (if g ∈ (iota M).range then f g else 0) := by
    intro g
    by_cases hg : g ∈ (iota M).range
    · rw [if_pos hg, if_pos hg, mul_one, mul_comm]
    · rw [if_neg hg, if_neg hg, mul_zero, mul_zero]
  have hterm2 : ∀ (j : Fin (cofactor M)) (g : G M),
      f g * metricPairing (gaussian M) (j.val • annihilatorGenerator M) g =
        f g * L2a.e (cofactor M) (-((j.val : ℕ) : ℤ) * ((g.2.val : ℕ) : ℤ)) := fun j g => by
    rw [ht2 j g]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun g _ => Finset.sum_congr rfl (fun j _ => hterm2 j g))]
  simp only [← Finset.mul_sum, hcf, hint]
  congr 1
  rw [← Finset.sum_filter]
  have himg : (Finset.univ.filter (fun x : G M => x ∈ (iota M).range)) =
      Finset.univ.image (iota M) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      AddMonoidHom.mem_range]
  rw [himg, Finset.sum_image]
  exact fun _ _ _ _ hab => iota_injective M hab


end SICLean.L2b

namespace SICLean.L2b

variable (M : ℕ) [Fact (4 ≤ M)]

private theorem cast_dimension_ne_zero : (M : ℂ) ≠ 0 := by
  exact_mod_cast (NeZero.ne M)

private theorem cast_cofactor_ne_zero : (cofactor M : ℂ) ≠ 0 := by
  exact_mod_cast (NeZero.ne (cofactor M))

private theorem convolutionScalar_sq :
    L2a.convolutionScalar M ^ 2 = (cofactor M : ℂ) := by
  have hM : 4 ≤ M := Fact.out
  have hM' : (4 : ℝ) ≤ M := by exact_mod_cast hM
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ (M : ℝ) - 3 by linarith)
  unfold L2a.convolutionScalar
  rw [← Complex.ofReal_pow, hs]
  simp only [cofactor, Nat.cast_sub (show 3 ≤ M by omega), Nat.cast_ofNat,
    Complex.ofReal_sub, Complex.ofReal_natCast, Complex.ofReal_ofNat]

private theorem convolutionScalar_ne_zero : L2a.convolutionScalar M ≠ 0 := by
  intro hc
  have hs := convolutionScalar_sq M
  rw [hc, zero_pow (by decide : 2 ≠ 0)] at hs
  exact cast_cofactor_ne_zero M hs.symm

/- E restricted along the explicit homomorphism ι; no relabeling of H. -/
def restrict (E : G M → ℂ) : L2a.Values M := E ∘ iota M

/- Input A, with no group-structure hypotheses.
Sources: [RW26, (31)], [RW26, (38)], and the zero convention in [RW26, (37)] for γ=α³. -/
structure FQDInput (E : G M → ℂ) : Prop where
  pentagon : IsFiniteQuantumDilogarithm (gaussian M) E
  epsilon_invariant : ∀ g : G M, E g = E (epsilonAut M g)
  origin : E 0 = L2a.sqrtEpsilon M ^ 3

def convolutionKernel (E : G M → ℂ) (h : L2a.Index M) (g : G M) : ℂ :=
  E g * gaussian M g * E (iota M h - g)

def subgroupConvolution (E : G M → ℂ) (h : L2a.Index M) : ℂ :=
  (∑ k : L2a.Index M, convolutionKernel M E h (iota M k) *
    metricPairing (gaussian M) (witnessW M h) (iota M k)) / (M : ℂ)

def shiftedW (h : L2a.Index M) (j : Fin (cofactor M)) : G M :=
  witnessW M h + j.val • annihilatorGenerator M

def averagedFullConvolution (E : G M → ℂ) (h : L2a.Index M) : ℂ :=
  (∑ j : Fin (cofactor M), ∑ g : G M,
    convolutionKernel M E h g * metricPairing (gaussian M) (shiftedW M h j) g) /
      ((M : ℂ) * (cofactor M : ℂ))

private theorem pairing_shiftedW_iota (h k : L2a.Index M) (j : Fin (cofactor M)) :
    metricPairing (gaussian M) (shiftedW M h j) (iota M k) =
      metricPairing (gaussian M) (witnessW M h) (iota M k) := by
  have hm : j.val • annihilatorGenerator M ∈
      AddSubgroup.zmultiples (annihilatorGenerator M) := by
    exact AddSubgroup.nsmul_mem _
      (AddSubgroup.mem_zmultiples_iff.mpr ⟨1, by simp⟩) j.val
  change j.val • annihilatorGenerator M ∈
    (AddSubgroup.zmultiples (annihilatorGenerator M) : Set (G M)) at hm
  rw [← orthogonal_iota M] at hm
  have hp := hm k
  rw [shiftedW, (concrete_isMetricGaussian M).add_left, hp, mul_one]

private theorem sum_index_eq_fin (f : L2a.Index M → ℂ) :
    (∑ k : L2a.Index M, f k) =
      ∑ i : Fin M, ∑ j : Fin M, f ((i.val : ZMod M), (j.val : ZMod M)) := by
  let e : Fin M ≃ ZMod M :=
    { toFun := fun i => (i.val : ZMod M)
      invFun := fun k => ⟨k.val, ZMod.val_lt k⟩
      left_inv := by
        intro i
        apply Fin.ext
        exact ZMod.val_cast_of_lt i.isLt
      right_inv := ZMod.natCast_zmod_val }
  calc
    _ = ∑ p : Fin M × Fin M, f (e p.1, e p.2) :=
      (Fintype.sum_equiv (e.prodCongr e) _ f (fun _ => rfl)).symm
    _ = _ := Fintype.sum_prod_type _

theorem subgroupConvolution_eq_L2a (E : G M → ℂ) (h : L2a.Index M) :
    subgroupConvolution M E h =
      L2a.convolution M (restrict M E) h.1.val h.2.val := by
  unfold subgroupConvolution L2a.convolution
  rw [sum_index_eq_fin, div_eq_inv_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hi : ((i.val : ZMod M).val : ℤ) = (i.val : ℤ) := by
    rw [ZMod.val_cast_of_lt i.isLt]
  have hj : ((j.val : ZMod M).val : ℤ) = (j.val : ℤ) := by
    rw [ZMod.val_cast_of_lt j.isLt]
  have hsub : iota M
      (((h.1.val : ℤ) - i.val : ℤ), ((h.2.val : ℤ) - j.val : ℤ)) =
      iota M h - iota M ((i.val : ZMod M), (j.val : ZMod M)) := by
    have hp : ((((h.1.val : ℤ) - i.val : ℤ) : ZMod M),
        (((h.2.val : ℤ) - j.val : ℤ) : ZMod M)) =
        h - ((i.val : ZMod M), (j.val : ZMod M)) := by
      simp only [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val]
      rfl
    rw [hp, map_sub]
  simp only [convolutionKernel, gaussian_iota, pairing_witnessW,
    L2a.gaussian, L2a.valueAt, restrict, Function.comp_apply, hi, hj,
    Int.cast_natCast]
  rw [hsub]
  ring

/- First equality in (40), valid also at h=0. -/
theorem average_over_annihilator (E : G M → ℂ) (h : L2a.Index M) :
    subgroupConvolution M E h =
      (∑ j : Fin (cofactor M), ∑ k : L2a.Index M,
        convolutionKernel M E h (iota M k) *
          metricPairing (gaussian M) (shiftedW M h j) (iota M k)) /
            ((M : ℂ) * (cofactor M : ℂ)) := by
  simp_rw [pairing_shiftedW_iota]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold subgroupConvolution
  field_simp [cast_dimension_ne_zero M, cast_cofactor_ne_zero M]

/- Second equality in (40), by the character filter for H. -/
theorem average_extend_to_G (E : G M → ℂ) (h : L2a.Index M) :
    subgroupConvolution M E h = averagedFullConvolution M E h := by
  have hs : (∑ j : Fin (cofactor M), ∑ g : G M,
      convolutionKernel M E h g * metricPairing (gaussian M) (shiftedW M h j) g) =
      (cofactor M : ℂ) * ∑ k : L2a.Index M,
        convolutionKernel M E h (iota M k) *
          metricPairing (gaussian M) (witnessW M h) (iota M k) := by
    calc
      _ = ∑ j : Fin (cofactor M), ∑ g : G M,
          (convolutionKernel M E h g * metricPairing (gaussian M) (witnessW M h) g) *
            metricPairing (gaussian M) (j.val • annihilatorGenerator M) g := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro g _
        rw [shiftedW, (concrete_isMetricGaussian M).add_left]
        ring
      _ = _ := sum_character_filter M _
  unfold subgroupConvolution averagedFullConvolution
  rw [hs]
  field_simp [cast_dimension_ne_zero M, cast_cofactor_ne_zero M]

/- Apply [RW26, (36)], including the value at (0,0). -/
theorem average_pentagon36 {E : G M → ℂ}
    (hE : IsFiniteQuantumDilogarithm (gaussian M) E) (h : L2a.Index M) :
    averagedFullConvolution M E h =
      (∑ j : Fin (cofactor M),
        (E (iota M h) * E (shiftedW M h j) *
            gaussian M (iota M h + shiftedW M h j) *
            E (-(iota M h + shiftedW M h j)) -
          (groupOrder M : ℂ) * E 0 *
            (if iota M h = 0 ∧ shiftedW M h j = 0 then 1 else 0))) /
        L2a.convolutionScalar M := by
  let R : Fin (cofactor M) → ℂ := fun j =>
    E (iota M h) * E (shiftedW M h j) *
        gaussian M (iota M h + shiftedW M h j) *
        E (-(iota M h + shiftedW M h j)) -
      (groupOrder M : ℂ) * E 0 *
        (if iota M h = 0 ∧ shiftedW M h j = 0 then 1 else 0)
  have hp (j : Fin (cofactor M)) :
      (∑ g : G M, convolutionKernel M E h g *
        metricPairing (gaussian M) (shiftedW M h j) g) = R j * sqrtCard (G M) := by
    apply (div_eq_iff (sqrtCard_ne_zero (A := G M))).mp
    calc
      _ = normalizedSum (fun g : G M => E g * gaussian M g * E (iota M h - g) *
          metricPairing (gaussian M) g (shiftedW M h j)) := by
        unfold normalizedSum convolutionKernel
        congr 1
        apply Finset.sum_congr rfl
        intro g _
        rw [metric_pairing_symmetric (gaussian M) (shiftedW M h j) g]
      _ = R j := by
        rw [fqd_pentagon36 (concrete_isMetricGaussian M) (card_G_gt_four M) hE]
        dsimp only [R]
        rw [card_G M, show -iota M h - shiftedW M h j =
          -(iota M h + shiftedW M h j) by abel]
        ac_rfl
  change (∑ j : Fin (cofactor M), ∑ g : G M,
      convolutionKernel M E h g * metricPairing (gaussian M) (shiftedW M h j) g) /
      ((M : ℂ) * (cofactor M : ℂ)) = (∑ j : Fin (cofactor M), R j) /
        L2a.convolutionScalar M
  simp_rw [hp]
  rw [← Finset.sum_mul, sqrtCard_G M, ← convolutionScalar_sq M]
  field_simp [cast_dimension_ne_zero M, convolutionScalar_ne_zero M]

/- The last equality of [RW26, (40)] is the case h≠0. -/
theorem equation40_nonzero {E : G M → ℂ}
    (hE : IsFiniteQuantumDilogarithm (gaussian M) E)
    (h : L2a.Index M) (hh : h ≠ 0) :
    subgroupConvolution M E h =
      (∑ j : Fin (cofactor M), E (iota M h) * E (shiftedW M h j) *
        gaussian M (iota M h + shiftedW M h j) *
        E (-(iota M h + shiftedW M h j))) / L2a.convolutionScalar M := by
  have hv : iota M h ≠ 0 := by
    intro hv
    apply hh
    apply iota_injective M
    simpa only [map_zero] using hv
  rw [average_extend_to_G, average_pentagon36 M hE]
  simp only [hv, false_and, if_false, mul_zero, sub_zero]

theorem epsilonAut_shiftedW (h : L2a.Index M) (j : Fin (cofactor M)) :
    epsilonAut M (shiftedW M h j) = iota M h + shiftedW M h j := by
  simp only [shiftedW, map_add, map_nsmul, witnessW_epsilon,
    epsilonAut_fixes_annihilatorGenerator]
  abel

/- Both factors are nonzero in the application of [RW26, Thm. 5(ii)]. -/
theorem shiftedW_ne_zero (h : L2a.Index M) (hh : h ≠ 0) (j : Fin (cofactor M)) :
    shiftedW M h j ≠ 0 ∧ iota M h + shiftedW M h j ≠ 0 := by
  have hv : iota M h ≠ 0 := by
    intro hv
    apply hh
    apply iota_injective M
    simpa only [map_zero] using hv
  have hy : shiftedW M h j ≠ 0 := by
    intro hy
    have he := epsilonAut_shiftedW M h j
    rw [hy, map_zero, add_zero] at he
    exact hv he.symm
  refine ⟨hy, ?_⟩
  intro hz
  apply hy
  apply (epsilonAut M).injective
  rw [epsilonAut_shiftedW, hz, map_zero]

theorem equation40_term {E : G M → ℂ} (hE : FQDInput M E)
    (h : L2a.Index M) (hh : h ≠ 0) (j : Fin (cofactor M)) :
    E (iota M h) * E (shiftedW M h j) * gaussian M (iota M h + shiftedW M h j) *
      E (-(iota M h + shiftedW M h j)) = E (iota M h) := by
  have hz := (shiftedW_ne_zero M h hh j).2
  have hi := hE.epsilon_invariant (shiftedW M h j)
  rw [epsilonAut_shiftedW] at hi
  have hr := fqd_reflection (concrete_isMetricGaussian M) (card_G_gt_four M)
    hE.pentagon (iota M h + shiftedW M h j) hz
  rw [hi]
  calc
    _ = E (iota M h) *
        ((E (iota M h + shiftedW M h j) * E (-(iota M h + shiftedW M h j))) *
          gaussian M (iota M h + shiftedW M h j)) := by ring
    _ = E (iota M h) := by
      rw [hr, inv_mul_cancel₀ (gaussian_ne_zero M _), mul_one]

theorem subgroupConvolution_nonzero {E : G M → ℂ} (hE : FQDInput M E)
    (h : L2a.Index M) (hh : h ≠ 0) :
    subgroupConvolution M E h = L2a.convolutionScalar M * E (iota M h) := by
  rw [equation40_nonzero M hE.pentagon h hh]
  simp_rw [equation40_term M hE h hh]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← convolutionScalar_sq M]
  field_simp [convolutionScalar_ne_zero M]

/- The value at zero. It follows from the origin quadratic; reflection is used only off zero. -/
theorem subgroupConvolution_zero {E : G M → ℂ}
    (hE : IsFiniteQuantumDilogarithm (gaussian M) E) :
    subgroupConvolution M E 0 = (E 0 ^ 2 + (M : ℂ) ^ 2 - 1) / (M : ℂ) ∧
    subgroupConvolution M E 0 = L2a.convolutionScalar M * E 0 + (M : ℂ) := by
  have hW : witnessW M (0 : L2a.Index M) = 0 := by
    simp [witnessW, coordinate]
  have hp (k : L2a.Index M) :
      metricPairing (gaussian M) (witnessW M 0) (iota M k) = 1 := by
    rw [hW]
    simp [metricPairing, gaussian_zero, gaussian_ne_zero]
  have ht (k : L2a.Index M) :
      convolutionKernel M E 0 (iota M k) *
          metricPairing (gaussian M) (witnessW M 0) (iota M k) =
        (if k = 0 then E 0 ^ 2 - 1 else 0) + 1 := by
    rw [hp, mul_one]
    by_cases hk : k = 0
    · subst k
      simp [convolutionKernel, gaussian_zero, pow_two]
    · have hv : iota M k ≠ 0 := by
        intro hv
        apply hk
        apply iota_injective M
        simpa only [map_zero] using hv
      have hr := fqd_reflection_all (concrete_isMetricGaussian M) (card_G_gt_four M)
        hE (iota M k)
      simp only [hv, if_false, mul_zero, add_zero] at hr
      simp only [convolutionKernel, map_zero, zero_sub, if_neg hk, zero_add]
      calc
        _ = E (iota M k) * E (-iota M k) * gaussian M (iota M k) := by ring
        _ = 1 := hr
  have hc : (Fintype.card (L2a.Index M) : ℂ) = (M : ℂ) ^ 2 := by
    simp [L2a.Index, Fintype.card_prod, pow_two]
  have hz : subgroupConvolution M E 0 =
      (E 0 ^ 2 + (M : ℂ) ^ 2 - 1) / (M : ℂ) := by
    unfold subgroupConvolution
    simp_rw [ht]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [hc]
    ring
  refine ⟨hz, ?_⟩
  rw [hz, fqd_origin_quadratic (concrete_isMetricGaussian M) (card_G_gt_four M) hE,
    sqrtCard_G M]
  field_simp [cast_dimension_ne_zero M]
  ring

theorem restrict_origin {E : G M → ℂ} (hE : FQDInput M E) :
    restrict M E 0 = L2a.sqrtEpsilon M ^ 3 := by
  simpa only [restrict, Function.comp_apply, map_zero] using hE.origin

theorem restrict_reflection {E : G M → ℂ} (hE : FQDInput M E)
    (h : L2a.Index M) (hh : h ≠ 0) :
    restrict M E h * restrict M E (-h) = (L2a.gaussian M h)⁻¹ := by
  have hv : iota M h ≠ 0 := by
    intro hv
    apply hh
    apply iota_injective M
    simpa only [map_zero] using hv
  have hr := fqd_reflection (concrete_isMetricGaussian M) (card_G_gt_four M)
    hE.pentagon (iota M h) hv
  simpa only [restrict, Function.comp_apply, map_neg, gaussian_iota] using hr

theorem restrict_convolution {E : G M → ℂ} (hE : FQDInput M E) (h : L2a.Index M) :
    L2a.convolution M (restrict M E) h.1.val h.2.val =
      L2a.convolutionScalar M * restrict M E h + if h = 0 then (M : ℂ) else 0 := by
  rw [← subgroupConvolution_eq_L2a]
  by_cases hh : h = 0
  · subst h
    simpa [restrict] using
      (subgroupConvolution_zero M hE.pentagon).2
  · simpa only [restrict, Function.comp_apply, if_neg hh, add_zero] using
      subgroupConvolution_nonzero M hE h hh


end SICLean.L2b

open SICLean SICLean.L2b

private theorem specialized_char (z : ℤ) :
    L2a.e 68 z = ZMod.stdAddChar (z : ZMod 68) := (ZMod.stdAddChar_coe z).symm

private theorem specialized_gaussian (i j : ZMod 68) :
    L2a.gaussian 68 (i,j) = ZMod.stdAddChar (i^2-i*j+j^2) := by
  unfold L2a.gaussian L2a.gaussianLift L2a.quadraticForm
  rw [specialized_char]
  simp

theorem OMA.solution : OMA.R_OpenQuantumProblem23_hasSICPOVM_68_R1_H1_R1.H2 := by
  have : Fact (4 ≤ 68) := ⟨by decide⟩
  intro E hp hi ho
  have hE : FQDInput 68 E := by
    constructor
    · obtain ⟨C, hC, h⟩ := hp
      refine ⟨C, hC, ?_⟩
      intro x y
      have hn : sqrtCard (G 68) = (Real.sqrt 300560 : ℂ) := by
        rw [sqrtCard, card_G]
        norm_num [groupOrder, cofactor]
      unfold normalizedSum
      rw [hn]
      convert h x y using 1 <;> congr 3
    · exact hi
    · have hu : L2a.epsilon 68 = (67 + Real.sqrt 4485) / 2 := by
        norm_num [L2a.epsilon]
      simpa only [L2a.sqrtEpsilon, hu] using ho
  constructor
  · intro i j hij
    have hr := restrict_reflection 68 hE (i,j) hij
    rw [specialized_gaussian] at hr
    exact hr
  · intro r s
    have hc := restrict_convolution 68 hE (r,s)
    have hscalar : L2a.convolutionScalar 68 = (Real.sqrt 65 : ℂ) := by
      norm_num [L2a.convolutionScalar]
    rw [hscalar] at hc
    change (68 : ℂ)⁻¹ * ∑ i : ZMod 68, ∑ j : ZMod 68,
      restrict 68 E (i,j) * restrict 68 E (r-i,s-j) *
      ZMod.stdAddChar (i^2-i*j+j^2) * ZMod.stdAddChar (-i*r+j*(r-s)) = _
    rw [← subgroupConvolution_eq_L2a] at hc
    calc
      _ = subgroupConvolution 68 E (r,s) := by
        unfold subgroupConvolution
        rw [Fintype.sum_prod_type, div_eq_inv_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        simp only [convolutionKernel, gaussian_iota, specialized_gaussian, pairing_witnessW,
          specialized_char, Int.cast_add, Int.cast_sub, Int.cast_neg, Int.cast_mul,
          Int.cast_natCast, ZMod.natCast_zmod_val, restrict, Function.comp_apply]
        rw [← map_sub, show (r,s) - (i,j) = (r-i,s-j) from rfl]
        ring
      _ = _ := by
        rw [hc]
        by_cases h : (r,s) = (0,0)
        · have h' : (r,s) = (0 : L2a.Index 68) := h
          simp only [if_pos h, if_pos h', Nat.cast_ofNat]
          rfl
        · have h' : (r,s) ≠ (0 : L2a.Index 68) := h
          simp only [if_neg h, if_neg h']
          rfl
