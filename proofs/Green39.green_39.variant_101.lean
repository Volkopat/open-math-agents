import FormalConjectures.GreensOpenProblems.«39»
import Mathlib

/-!
Green's Open Problem 39, one-percent variant.

Problem by Ben Green, `100 open problems` (2024), Problem 39.
https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.39
The statement and `Green39.proportionCoverable` are imported from Formal Conjectures
at revision `9097e2f90e66d2f6244209cb1c07f7120d17ec53`. The covering problem is also discussed by Béla Bollobás,
Svante Janson and Oliver Riordan, `On covering by translates of a set` (2011).
https://arxiv.org/abs/0910.3815
The proof and its Lean formalization were developed in the Burntgogi workspace
with OpenAI Codex. Each section names its original Lean source.
-/

/- Source: one-percent-formal/transcripts/Retention.lean -/
section Retention

/- The geometric loss and the retained targets from §6. -/

namespace Green39.Transcripts

open Finset

noncomputable section

def level (x₀ : ℝ) : ℕ → ℝ
  | 0 => x₀
  | i + 1 => level x₀ i / 2

theorem level_eq_div_pow (x₀ : ℝ) (i : ℕ) : level x₀ i = x₀ / 2 ^ i := by
  induction i with
  | zero => simp [level]
  | succ i ih => rw [level, ih, pow_succ, div_div]

theorem level_pos {x₀ : ℝ} (hx : 0 < x₀) (i : ℕ) : 0 < level x₀ i := by
  rw [level_eq_div_pow]
  positivity

theorem level_antitone {x₀ : ℝ} (hx : 0 ≤ x₀) : Antitone (level x₀) := by
  apply antitone_nat_of_succ_le
  intro i
  rw [level]
  have h : 0 ≤ level x₀ i := by rw [level_eq_div_pow]; positivity
  linarith

theorem last_level_bounds {x₀ : ℝ} {n : ℕ}
    (hactive : 5000 < level x₀ n) (hstop : level x₀ (n + 1) ≤ 5000) :
    5000 < level x₀ n ∧ level x₀ n ≤ 10000 := by
  rw [level] at hstop
  exact ⟨hactive, by linarith⟩

/-- There is a first inactive level whenever the initial level is active. -/
theorem exists_last_active {x₀ : ℝ} (hx : 5000 < x₀) :
    ∃ n, (∀ i ≤ n, 5000 < level x₀ i) ∧ level x₀ (n + 1) ≤ 5000 := by
  have hstop : ∃ n, level x₀ n ≤ 5000 := by
    obtain ⟨n, hn⟩ := exists_nat_gt (x₀ / 5000)
    have hpow : n < 2 ^ n := Nat.lt_two_pow_self
    have hn' : (n : ℝ) < 2 ^ n := by exact_mod_cast hpow
    refine ⟨n, ?_⟩
    rw [level_eq_div_pow, div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)]
    linarith
  obtain ⟨n, heq⟩ := Nat.exists_eq_succ_of_ne_zero
    (show Nat.find hstop ≠ 0 by
      intro h
      have hspec := Nat.find_spec hstop
      rw [h, level] at hspec
      linarith)
  refine ⟨n, ?_, ?_⟩
  · intro i hi
    exact lt_of_not_ge (Nat.find_min hstop (by omega))
  · simpa only [heq] using Nat.find_spec hstop

def lossRate (x : ℝ) : ℝ := 1 / x ^ 2

theorem lossRate_halve (x : ℝ) : lossRate (x / 2) = 4 * lossRate x := by
  unfold lossRate
  rw [div_pow, div_div_eq_mul_div]
  ring

/-- Exact sum of the active-stage loss rates through stage `n`. -/
theorem sum_lossRate (x₀ : ℝ) (n : ℕ) :
    3 * (∑ i ∈ range (n + 1), lossRate (level x₀ i)) =
      4 * lossRate (level x₀ n) - lossRate x₀ := by
  induction n with
  | zero => simp [level]; ring
  | succ n ih =>
    have hs : lossRate (level x₀ (n + 1)) = 4 * lossRate (level x₀ n) := by
      rw [level, lossRate_halve]
    rw [sum_range_succ, hs]
    linarith

theorem sum_lossRate_lt {x₀ : ℝ} {n : ℕ} (hactive : 5000 < level x₀ n) :
    (∑ i ∈ range (n + 1), lossRate (level x₀ i)) < 4 / (3 * 5000 ^ 2) := by
  have hlast : lossRate (level x₀ n) < 1 / (5000 : ℝ) ^ 2 := by
    unfold lossRate
    apply one_div_lt_one_div_of_lt (by positivity)
    nlinarith [sq_nonneg (level x₀ n - 5000)]
  have hfirst : 0 ≤ lossRate x₀ := by unfold lossRate; positivity
  linarith [sum_lossRate x₀ n]

variable {Point : Type*} [DecidableEq Point]

/-- Exact telescoping of the number of target points lost. -/
theorem card_telescope (targets : ℕ → Finset Point) (m : ℕ)
    (hsub : ∀ i < m, targets (i + 1) ⊆ targets i) :
    (targets m).card + ∑ i ∈ range m, ((targets i) \ (targets (i + 1))).card =
      (targets 0).card := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    have hstep := card_sdiff_add_card_eq_card (hsub m (Nat.lt_succ_self m))
    have hp := ih (fun i hi => hsub i (Nat.lt_succ_of_lt hi))
    omega

/-- The exact real-valued lower bound obtained by summing the per-stage loss budgets. -/
theorem card_retained_lower (targets : ℕ → Finset Point) (x₀ k : ℝ) (m : ℕ)
    (hsub : ∀ i < m, targets (i + 1) ⊆ targets i)
    (hloss : ∀ i < m, (((targets i) \ (targets (i + 1))).card : ℝ) ≤
      k * lossRate (level x₀ i)) :
    ((targets 0).card : ℝ) - k * (∑ i ∈ range m, lossRate (level x₀ i)) ≤
      (targets m).card := by
  have hcast := congrArg (fun a : ℕ => (a : ℝ)) (card_telescope targets m hsub)
  push_cast at hcast
  have hsum : (∑ i ∈ range m, (((targets i) \ (targets (i + 1))).card : ℝ)) ≤
      k * (∑ i ∈ range m, lossRate (level x₀ i)) := by
    rw [mul_sum]
    exact sum_le_sum fun i hi => hloss i (mem_range.mp hi)
  linarith

/-- The aggregate loss is strictly below the manuscript's geometric bound. -/
theorem card_loss_lt (targets : ℕ → Finset Point) {x₀ k : ℝ} {n : ℕ}
    (hk : 0 < k) (hactive : 5000 < level x₀ n)
    (hsub : ∀ i ≤ n, targets (i + 1) ⊆ targets i)
    (hloss : ∀ i ≤ n, (((targets i) \ (targets (i + 1))).card : ℝ) ≤
      k * lossRate (level x₀ i)) :
    ((targets 0).card : ℝ) - (targets (n + 1)).card < 4 * k / (3 * 5000 ^ 2) := by
  have h := card_retained_lower targets x₀ k (n + 1)
    (fun i hi => hsub i (Nat.lt_succ_iff.mp hi)) (fun i hi => hloss i (Nat.lt_succ_iff.mp hi))
  have hb := mul_lt_mul_of_pos_left (sum_lossRate_lt hactive) hk
  linarith

/-- Retaining the intersection with each output container preserves more than
`0.11 k` good centers at every prefix, including the terminal prefix. -/
theorem retention_each_prefix (targets containers : ℕ → Finset Point) {x₀ k : ℝ} {n : ℕ}
    (hk : 0 < k) (hactive : 5000 < level x₀ n)
    (hstart : k / 9 ≤ (targets 0).card)
    (hnext : ∀ i ≤ n, targets (i + 1) = targets i ∩ containers i)
    (hloss : ∀ i ≤ n, (((targets i) \ containers i).card : ℝ) ≤
      k * lossRate (level x₀ i)) :
    ∀ m ≤ n + 1, (11 / 100 : ℝ) * k < (targets m).card := by
  have hx : 0 ≤ x₀ := by
    have he := level_eq_div_pow x₀ n
    have hp : (0 : ℝ) < 2 ^ n := by positivity
    rw [he, lt_div_iff₀ hp] at hactive
    linarith
  intro m hm
  cases m with
  | zero => linarith
  | succ j =>
    have hj : j ≤ n := by omega
    have hprefix := hactive.trans_le (level_antitone hx hj)
    have hsub (i : ℕ) (hi : i ≤ j) : targets (i + 1) ⊆ targets i := by
      rw [hnext i (hi.trans hj)]
      exact inter_subset_left
    have hstep (i : ℕ) (hi : i ≤ j) :
        (((targets i) \ targets (i + 1)).card : ℝ) ≤ k * lossRate (level x₀ i) := by
      rw [hnext i (hi.trans hj)]
      have heq : targets i \ (targets i ∩ containers i) = targets i \ containers i := by
        ext a
        simp only [mem_sdiff, mem_inter]
        tauto
      rw [heq]
      exact hloss i (hi.trans hj)
    have hb := card_loss_lt targets hk hprefix hsub hstep
    linarith

end

end Green39.Transcripts

end Retention

/- Source: one-percent-formal/fourier/FourierDiscrepancy.lean -/
section FourierDiscrepancy

/-
# Deterministic Fourier discrepancy for the fitted piece

The counting-measure transform is `ZMod.dft`. The normalized transform divides by the
ambient cardinality. The transform of the uniform probability on a nonempty set instead
divides its indicator transform by the set cardinality.
-/

open Finset
open scoped Pointwise ComplexConjugate

namespace OnePercent.Fourier

variable {p : ℕ} [NeZero p]

/-- Indicator of a finite set, with values in the coefficient ring. -/
def indicator {R : Type*} [Zero R] [One R] (U : Finset (ZMod p)) (z : ZMod p) : R :=
  if z ∈ U then 1 else 0

/-- Counting-measure convolution on `ZMod p`. -/
noncomputable def convolution {R : Type*} [Semiring R] (f g : ZMod p → R) (z : ZMod p) : R :=
  ∑ u, f u * g (z - u)

lemma convolution_indicator {R : Type*} [Semiring R] (U : Finset (ZMod p)) (g : ZMod p → R)
    (z : ZMod p) : convolution (indicator U) g z = ∑ u ∈ U, g (z - u) := by
  simp only [convolution, indicator, ite_mul, one_mul, zero_mul, ← Finset.sum_filter,
    Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- Fourier coefficients with the ambient averaging convention. -/
noncomputable def normalizedDFT (f : ZMod p → ℂ) (a : ZMod p) : ℂ :=
  ZMod.dft f a / (p : ℂ)

/-- The uniform law on `S`, whose mass is one when `S` is nonempty. -/
noncomputable def uniformLaw (S : Finset (ZMod p)) (z : ZMod p) : ℂ :=
  indicator S z / (S.card : ℂ)

/-- The actual number of points of `U` hit at center `z` by a shift in `S`. -/
def observed (U S : Finset (ZMod p)) (z : ZMod p) : ℝ :=
  ((z +ᵥ S) ∩ U).card

/-- The smooth prediction at `z`, using a measure given by its masses `μ`. -/
noncomputable def predicted (U S : Finset (ZMod p)) (μ : ZMod p → ℝ) (z : ZMod p) : ℝ :=
  (S.card : ℝ) * ∑ u ∈ U, μ (u - z)

/-- The real, pointwise discrepancy from Section 5. -/
noncomputable def discrepancy (U S : Finset (ZMod p)) (μ : ZMod p → ℝ) (z : ZMod p) : ℝ :=
  observed U S z - predicted U S μ z

/-- The difference between the indicator of `S` and the fitted mass rescaled by `|S|`. -/
noncomputable def centeredKernel (S : Finset (ZMod p)) (μ : ZMod p → ℝ) (z : ZMod p) : ℝ :=
  indicator S z - (S.card : ℝ) * μ z

omit [NeZero p] in
lemma observed_eq_sum (U S : Finset (ZMod p)) (z : ZMod p) :
    observed U S z = ∑ u ∈ U, (indicator S (u - z) : ℝ) := by
  simp only [observed, indicator, ← Finset.sum_filter]
  have h : U.filter (fun u ↦ u - z ∈ S) = (z +ᵥ S) ∩ U := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_vadd_finset, vadd_eq_add]
    constructor
    · rintro ⟨huU, huS⟩
      exact ⟨⟨u - z, huS, by abel⟩, huU⟩
    · rintro ⟨⟨v, hvS, rfl⟩, huU⟩
      exact ⟨huU, by simpa using hvS⟩
  rw [h]
  simp

lemma discrepancy_eq_convolution (U S : Finset (ZMod p)) (μ : ZMod p → ℝ) (z : ZMod p) :
    discrepancy U S μ z = convolution (indicator U) (fun t ↦ centeredKernel S μ (-t)) z := by
  rw [discrepancy, observed_eq_sum, predicted, Finset.mul_sum, ← Finset.sum_sub_distrib,
    convolution_indicator]
  simp only [centeredKernel, neg_sub]

lemma dft_convolution (f g : ZMod p → ℂ) (a : ZMod p) :
    ZMod.dft (convolution f g) a = ZMod.dft f a * ZMod.dft g a := by
  simp only [ZMod.dft_apply, smul_eq_mul, convolution]
  conv_lhs => enter [2, z]; rw [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.subRight u) _ _ fun z ↦ ?_
  change ZMod.stdAddChar (-(z * a)) * (f u * g (z - u)) =
    (ZMod.stdAddChar (-(u * a)) * f u) * (ZMod.stdAddChar (-((z - u) * a)) * g (z - u))
  rw [show -(z * a) = -(u * a) + -((z - u) * a) by ring, AddChar.map_add_eq_mul]
  ring

lemma normalizedDFT_convolution (f g : ZMod p → ℂ) (a : ZMod p) :
    normalizedDFT (convolution f g) a =
      (p : ℂ) * normalizedDFT f a * normalizedDFT g a := by
  simp only [normalizedDFT, dft_convolution]
  field_simp

lemma dft_uniformLaw (S : Finset (ZMod p)) (a : ZMod p) :
    ZMod.dft (uniformLaw S) a = ZMod.dft (indicator S) a / (S.card : ℂ) := by
  simp [uniformLaw, ZMod.dft_apply, smul_eq_mul, Finset.sum_div, mul_div_assoc]

lemma dft_indicator_eq_card_mul_uniformLaw (S : Finset (ZMod p)) (hS : S.Nonempty)
    (a : ZMod p) :
    ZMod.dft (indicator S) a = (S.card : ℂ) * ZMod.dft (uniformLaw S) a := by
  have hcard : (S.card : ℂ) ≠ 0 := by exact_mod_cast hS.card_ne_zero
  rw [dft_uniformLaw, mul_comm (S.card : ℂ), div_mul_cancel₀ _ hcard]

private lemma sum_indicator {R : Type*} [Semiring R] (S : Finset (ZMod p)) :
    (∑ z : ZMod p, (indicator S z : R)) = (S.card : R) := by
  simp [indicator]

lemma dft_centeredKernel (S : Finset (ZMod p)) (μ : ZMod p → ℝ) (a : ZMod p) :
    ZMod.dft (fun z ↦ (centeredKernel S μ z : ℂ)) a =
      ZMod.dft (indicator S) a - (S.card : ℂ) * ZMod.dft (fun z ↦ (μ z : ℂ)) a := by
  have h : (fun z ↦ (centeredKernel S μ z : ℂ)) =
      indicator S - fun z ↦ (S.card : ℂ) * (μ z : ℂ) := by
    funext z
    simp only [Pi.sub_apply, centeredKernel, Complex.ofReal_sub, Complex.ofReal_mul,
      Complex.ofReal_natCast]
    by_cases hz : z ∈ S <;> simp [indicator, hz]
  rw [h, map_sub, ZMod.dft_const_mul, Pi.sub_apply]

/-- The frequency reverses because the kernel in the observed count uses `u - z`. -/
lemma dft_discrepancy (U S : Finset (ZMod p)) (μ : ZMod p → ℝ) (a : ZMod p) :
    ZMod.dft (fun z ↦ (discrepancy U S μ z : ℂ)) a =
      ZMod.dft (indicator U) a *
        (ZMod.dft (indicator S) (-a) -
          (S.card : ℂ) * ZMod.dft (fun z ↦ (μ z : ℂ)) (-a)) := by
  have h : (fun z ↦ (discrepancy U S μ z : ℂ)) =
      convolution (indicator U) (fun t ↦ (centeredKernel S μ (-t) : ℂ)) := by
    funext z
    rw [discrepancy_eq_convolution]
    simp only [convolution, Complex.ofReal_sum, Complex.ofReal_mul]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    by_cases hu : u ∈ U <;> simp [indicator, hu]
  rw [h, dft_convolution, ZMod.dft_comp_neg (fun t ↦ (centeredKernel S μ t : ℂ))]
  exact congrArg (ZMod.dft (indicator U) a * ·) (dft_centeredKernel S μ (-a))

/-- Centering cancels the zero Fourier mode when the fitted masses sum to one. -/
lemma sum_discrepancy_eq_zero (U S : Finset (ZMod p)) (μ : ZMod p → ℝ)
    (hμ : ∑ z : ZMod p, μ z = 1) : ∑ z : ZMod p, discrepancy U S μ z = 0 := by
  have hfitMass : ∑ z : ZMod p, (μ z : ℂ) = 1 := by exact_mod_cast hμ
  have hzero := dft_discrepancy U S μ (0 : ZMod p)
  simp only [neg_zero, ZMod.dft_apply_zero, sum_indicator, hfitMass, mul_one, sub_self,
    mul_zero] at hzero
  exact_mod_cast hzero

private lemma inverse_sum (f : ZMod p → ℂ) (x : ZMod p) :
    (∑ a : ZMod p, ZMod.stdAddChar (a * x) * ZMod.dft f a) = (p : ℂ) * f x := by
  have h := congrFun (ZMod.dft.symm_apply_apply f) x
  rw [ZMod.invDFT_apply] at h
  exact (inv_mul_eq_iff_eq_mul₀ (NeZero.ne (p : ℂ))).mp h

/-- Parseval for the unnormalized transform, with counting measure on both sides. -/
lemma parseval_unnormalized (f : ZMod p → ℂ) :
    (∑ a : ZMod p, ‖ZMod.dft f a‖ ^ 2) = (p : ℝ) * ∑ x : ZMod p, ‖f x‖ ^ 2 := by
  have h : (∑ a : ZMod p, conj (ZMod.dft f a) * ZMod.dft f a) =
      (p : ℂ) * ∑ x : ZMod p, conj (f x) * f x := by
    calc
      _ = ∑ x : ZMod p, conj (f x) *
          (∑ a : ZMod p, ZMod.stdAddChar (a * x) * ZMod.dft f a) := by
        conv_lhs => enter [2, a, 1]; rw [ZMod.dft_apply, map_sum]
        simp only [Finset.sum_mul, Finset.mul_sum, smul_eq_mul, map_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_
        rw [← AddChar.inv_apply_eq_conj, ← AddChar.map_neg_eq_inv, neg_neg, mul_comm x a]
        ring
      _ = _ := by
        simp only [inverse_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun _ _ ↦ ?_
        ring
  simp only [Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_sum, ← Complex.ofReal_natCast p,
    ← Complex.ofReal_mul, Complex.ofReal_inj] at h
  exact h

/-- Parseval for coefficients divided by `p`, with the spatial mean square on the right. -/
lemma parseval_normalized (f : ZMod p → ℂ) :
    (∑ a : ZMod p, ‖normalizedDFT f a‖ ^ 2) = (∑ x : ZMod p, ‖f x‖ ^ 2) / (p : ℝ) := by
  simp only [normalizedDFT, norm_div, Complex.norm_natCast, div_pow, ← Finset.sum_div,
    parseval_unnormalized]
  have hp : (p : ℝ) ≠ 0 := NeZero.ne _
  field_simp

/-- The counting-measure form of (5), allowing an arbitrary sup norm bound `B`. -/
def FourierFit (S : Finset (ZMod p)) (μ : ZMod p → ℝ) (B : ℝ) : Prop :=
  ∀ a : ZMod p, ‖ZMod.dft (indicator S) a -
    (S.card : ℂ) * ZMod.dft (fun z ↦ (μ z : ℂ)) a‖ ≤ B

lemma fourierFit_iff_normalizedDFT (S : Finset (ZMod p)) (μ : ZMod p → ℝ) (B : ℝ) :
    FourierFit S μ B ↔ ∀ a : ZMod p, ‖normalizedDFT (indicator S) a -
      (S.card : ℂ) * normalizedDFT (fun z ↦ (μ z : ℂ)) a‖ ≤ B / (p : ℝ) := by
  have hp : 0 < (p : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne p))
  simp only [FourierFit, normalizedDFT, ← mul_div_assoc, ← sub_div, norm_div,
    Complex.norm_natCast, div_le_div_iff_of_pos_right hp]

/-- Passing from the normalized empirical law of `S` to (5) costs a factor of `|S|`. -/
lemma fourierFit_iff_uniformLaw (S : Finset (ZMod p)) (μ : ZMod p → ℝ) (hS : S.Nonempty)
    (B : ℝ) : FourierFit S μ (B * S.card) ↔ ∀ a : ZMod p,
      ‖ZMod.dft (uniformLaw S) a - ZMod.dft (fun z ↦ (μ z : ℂ)) a‖ ≤ B := by
  have hs : 0 < (S.card : ℝ) := by exact_mod_cast hS.card_pos
  simp only [FourierFit, dft_indicator_eq_card_mul_uniformLaw S hS, ← mul_sub, norm_mul,
    Complex.norm_natCast, mul_comm (S.card : ℝ), mul_le_mul_iff_of_pos_right hs]

lemma mean_sq_discrepancy_le (U S : Finset (ZMod p)) (μ : ZMod p → ℝ) {B : ℝ}
    (hfit : FourierFit S μ B) :
    (∑ z : ZMod p, |discrepancy U S μ z| ^ 2) / (p : ℝ) ≤
      B ^ 2 * ((U.card : ℝ) / (p : ℝ)) := by
  have hU : (∑ z : ZMod p, ‖(indicator U z : ℂ)‖ ^ 2) = (U.card : ℝ) := by
    simp [indicator, apply_ite (fun w : ℂ ↦ ‖w‖ ^ 2)]
  have hD := parseval_normalized (fun z ↦ (discrepancy U S μ z : ℂ))
  simp only [Complex.norm_real, Real.norm_eq_abs] at hD
  rw [← hD, ← hU, ← parseval_normalized, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ ↦ ?_
  rw [normalizedDFT, dft_discrepancy, mul_div_right_comm, norm_mul, mul_pow]
  change ‖normalizedDFT (indicator U) a‖ ^ 2 * _ ≤ B ^ 2 * ‖normalizedDFT (indicator U) a‖ ^ 2
  rw [mul_comm (B ^ 2)]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hfit (-a)) _) (sq_nonneg _)

/-- Positions where the absolute discrepancy strictly exceeds the threshold. -/
noncomputable def exceptional (f : ZMod p → ℝ) (δ : ℝ) : Finset (ZMod p) := by
  classical
  exact Finset.univ.filter fun z ↦ δ < |f z|

@[simp] lemma mem_exceptional (f : ZMod p → ℝ) (δ : ℝ) (z : ZMod p) :
    z ∈ exceptional f δ ↔ δ < |f z| := by
  classical
  simp [exceptional]

lemma exceptional_card_mul_sq_le (f : ZMod p → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ((exceptional f δ).card : ℝ) * δ ^ 2 ≤ ∑ z : ZMod p, |f z| ^ 2 := by
  calc
    _ = ∑ z ∈ exceptional f δ, δ ^ 2 := by simp
    _ ≤ ∑ z ∈ exceptional f δ, |f z| ^ 2 := by
      exact Finset.sum_le_sum fun z hz ↦
        pow_le_pow_left₀ hδ ((mem_exceptional f δ z).mp hz).le _
    _ ≤ _ := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun z _ _ ↦ sq_nonneg _)

/-- The exceptional fraction, retaining the factor `|U| / p`. -/
lemma exceptional_fraction_le (U S : Finset (ZMod p)) (μ : ZMod p → ℝ) {B δ : ℝ}
    (hfit : FourierFit S μ B) (hδ : 0 < δ) :
    ((exceptional (discrepancy U S μ) δ).card : ℝ) / (p : ℝ) ≤
      (B / δ) ^ 2 * ((U.card : ℝ) / (p : ℝ)) := by
  have hp : 0 < (p : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne p))
  have h := (div_le_div_iff_of_pos_right hp).2
    (exceptional_card_mul_sq_le (discrepancy U S μ) hδ.le)
  have hbound := h.trans (mean_sq_discrepancy_le U S μ hfit)
  have hscaled : (((exceptional (discrepancy U S μ) δ).card : ℝ) / (p : ℝ)) * δ ^ 2 ≤
      B ^ 2 * ((U.card : ℝ) / p) := by
    rwa [div_mul_eq_mul_div]
  calc
    _ ≤ (B ^ 2 * ((U.card : ℝ) / p)) / δ ^ 2 := (le_div_iff₀ (sq_pos_of_pos hδ)).2 hscaled
    _ = _ := by ring

/-- An upper bound on the number of exceptional positions for any positive threshold. -/
lemma exceptional_card_le (U S : Finset (ZMod p)) (μ : ZMod p → ℝ) {B δ : ℝ}
    (hfit : FourierFit S μ B) (hδ : 0 < δ) :
    ((exceptional (discrepancy U S μ) δ).card : ℝ) ≤ (B / δ) ^ 2 * U.card := by
  have hp : 0 < (p : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne p))
  have h := exceptional_fraction_le U S μ hfit hδ
  rw [← mul_div_assoc, div_le_div_iff_of_pos_right hp] at h
  exact h

/-- The threshold `0.001 r |S| / k` used for exceptional positions. -/
noncomputable def cutoff (r s k : ℕ) : ℝ := (0.001 : ℝ) * r * s / k

lemma exceptional_fraction_section5 (U S : Finset (ZMod p)) (μ : ZMod p → ℝ)
    {r k : ℕ} {η : ℝ} (hk : 0 < k) (hη : 0 ≤ η)
    (hr : (0.099 : ℝ) ≤ (r : ℝ) / k) (hfit : FourierFit S μ (7 * η * S.card)) :
    ((exceptional (discrepancy U S μ) (cutoff r S.card k)).card : ℝ) / (p : ℝ) ≤
      (71000 * η) ^ 2 := by
  classical
  by_cases hS : S.Nonempty
  · have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
    have hr' : 0 < (r : ℝ) := (div_pos_iff_of_pos_right hk').mp (by linarith)
    have hs' : 0 < (S.card : ℝ) := by exact_mod_cast hS.card_pos
    have hδ : 0 < cutoff r S.card k := by unfold cutoff; positivity
    have hcoeff : (7 : ℝ) ≤ 71000 * (0.001 * ((r : ℝ) / k)) := by linarith
    have hratio : 7 * η * (S.card : ℝ) / cutoff r S.card k ≤ 71000 * η := by
      apply (div_le_iff₀ hδ).2
      calc
        _ = 7 * (η * (S.card : ℝ)) := by ring
        _ ≤ 71000 * (0.001 * ((r : ℝ) / k)) * (η * (S.card : ℝ)) :=
          mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hη hs'.le)
        _ = _ := by unfold cutoff; ring
    have hU : (U.card : ℝ) / (p : ℝ) ≤ 1 := by
      have hp : 0 < (p : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne p))
      have hcard : U.card ≤ p := by simpa [ZMod.card] using Finset.card_le_univ U
      apply (div_le_iff₀ hp).2
      simpa using (Nat.cast_le (α := ℝ)).2 hcard
    calc
      _ ≤ (7 * η * (S.card : ℝ) / cutoff r S.card k) ^ 2 * ((U.card : ℝ) / p) :=
        exceptional_fraction_le U S μ hfit hδ
      _ ≤ (7 * η * (S.card : ℝ) / cutoff r S.card k) ^ 2 :=
        mul_le_of_le_one_right (sq_nonneg _) hU
      _ ≤ _ := pow_le_pow_left₀ (div_nonneg (by positivity) hδ.le) hratio _
  · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [hEmpty, exceptional, discrepancy, observed, predicted, cutoff, sq_nonneg]

lemma exceptional_card_section5 (U S : Finset (ZMod p)) (μ : ZMod p → ℝ)
    {r k : ℕ} {η : ℝ} (hk : 0 < k) (hη : 0 ≤ η)
    (hr : (0.099 : ℝ) ≤ (r : ℝ) / k) (hfit : FourierFit S μ (7 * η * S.card)) :
    ((exceptional (discrepancy U S μ) (cutoff r S.card k)).card : ℝ) ≤
      (71000 * η) ^ 2 * (p : ℝ) := by
  have hp : 0 < (p : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne p))
  exact (div_le_iff₀ hp).mp (exceptional_fraction_section5 U S μ hk hη hr hfit)

/-- The deterministic lower bound on the aggregate prediction from the first inequality in (4). -/
lemma sum_predicted_ge_of_l1 (A₂ U S : Finset (ZMod p)) (μ : ZMod p → ℝ) {ε : ℝ}
    (hL1 : (∑ u : ZMod p, |convolution (indicator A₂) μ u - (A₂.card : ℝ) / p|) ≤ ε) :
    (S.card : ℝ) * ((A₂.card : ℝ) * U.card / p - ε) ≤ ∑ z ∈ A₂, predicted U S μ z := by
  have hdiff : (∑ u ∈ U, ((A₂.card : ℝ) / p - convolution (indicator A₂) μ u)) ≤ ε := by
    calc
      _ ≤ ∑ u ∈ U, |convolution (indicator A₂) μ u - (A₂.card : ℝ) / p| := by
        apply Finset.sum_le_sum
        intro u _
        rw [← neg_sub]
        apply neg_le_abs
      _ ≤ ∑ u : ZMod p, |convolution (indicator A₂) μ u - (A₂.card : ℝ) / p| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ ↦ abs_nonneg _)
      _ ≤ ε := hL1
  have hmean : (∑ _ ∈ U, (A₂.card : ℝ) / p) = (A₂.card : ℝ) * U.card / p := by
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [Finset.sum_sub_distrib, hmean] at hdiff
  calc
    _ ≤ (S.card : ℝ) * ∑ u ∈ U, convolution (indicator A₂) μ u :=
      mul_le_mul_of_nonneg_left (by linarith only [hdiff]) (Nat.cast_nonneg _)
    _ = _ := by
      simp only [predicted, convolution_indicator, ← Finset.mul_sum]
      rw [Finset.sum_comm]

/-- Exceptional positions that occur in the second half of the sample. -/
noncomputable def exceptionalHits (A₂ U S : Finset (ZMod p)) (μ : ZMod p → ℝ) (r k : ℕ) :
    Finset (ZMod p) :=
  A₂ ∩ exceptional (discrepancy U S μ) (cutoff r S.card k)

/-- The deterministic hit-count implication of the three estimates preceding Parseval in §5. -/
lemma exceptionalHits_lower_of_prediction_cap (A₂ U S : Finset (ZMod p))
    (μ : ZMod p → ℝ) {r k : ℕ} (hr : 0 < r) (hk : 0 < k) (hS : S.Nonempty)
    (hA₂ : A₂.card ≤ k)
    (hpred : (0.244 : ℝ) * r * S.card ≤ ∑ z ∈ A₂, predicted U S μ z)
    (hobs : (∑ z ∈ A₂, observed U S z) ≤ (0.115 : ℝ) * r * S.card)
    (hcap : (∑ z ∈ exceptionalHits A₂ U S μ r k, predicted U S μ z) ≤
      (r : ℝ) * S.card *
        (0.51 * ((exceptionalHits A₂ U S μ r k).card : ℝ) / k + 0.001)) :
    (0.244 - 0.115 - 0.001 - 0.001 : ℝ) / 0.51 ≤
      ((exceptionalHits A₂ U S μ r k).card : ℝ) / k ∧
    (0.24 : ℝ) * k < (exceptionalHits A₂ U S μ r k).card := by
  classical
  let E := exceptionalHits A₂ U S μ r k
  let δ := cutoff r S.card k
  let rs : ℝ := (r : ℝ) * S.card
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hs' : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hrs : 0 < rs := by dsimp [rs]; positivity
  have hδ : 0 ≤ δ := by dsimp [δ, cutoff]; positivity
  have hE : E ⊆ A₂ := Finset.inter_subset_left
  have hcard : ((A₂ \ E).card : ℝ) ≤ k := by
    exact_mod_cast (Finset.card_le_card (Finset.sdiff_subset : A₂ \ E ⊆ A₂)).trans hA₂
  have hgood : (∑ z ∈ A₂ \ E, (predicted U S μ z - observed U S z)) ≤ (k : ℝ) * δ := by
    calc
      _ ≤ ∑ _ ∈ A₂ \ E, δ := by
        refine Finset.sum_le_sum fun z hz ↦ ?_
        obtain ⟨hzA, hzE⟩ := Finset.mem_sdiff.mp hz
        have hzδ : |discrepancy U S μ z| ≤ δ := by
          apply le_of_not_gt
          intro hzbad
          exact hzE (Finset.mem_inter.mpr ⟨hzA, (mem_exceptional _ _ _).mpr hzbad⟩)
        have hzLower := (abs_le.mp hzδ).1
        dsimp [discrepancy] at hzLower
        linarith only [hzLower]
      _ = ((A₂ \ E).card : ℝ) * δ := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard hδ
  have hbad : (∑ z ∈ E, (predicted U S μ z - observed U S z)) ≤
      rs * (0.51 * (E.card : ℝ) / k + 0.001) := by
    refine (Finset.sum_le_sum fun z _ ↦ sub_le_self _ ?_).trans hcap
    exact Nat.cast_nonneg _
  have htotal : (0.244 - 0.115 : ℝ) * rs ≤
      (∑ z ∈ A₂, (predicted U S μ z - observed U S z)) := by
    rw [Finset.sum_sub_distrib]
    dsimp [rs]
    linarith only [hpred, hobs]
  rw [← Finset.sum_sdiff hE] at htotal
  have hcutoff : (k : ℝ) * δ = 0.001 * rs := by
    dsimp [δ, cutoff, rs]
    field_simp
  have hgap := htotal.trans (add_le_add hgood hbad)
  rw [hcutoff] at hgap
  have hcancel : (0.244 - 0.115 : ℝ) ≤ 0.001 + (0.51 * (E.card : ℝ) / k + 0.001) := by
    apply (mul_le_mul_iff_right₀ hrs).mp
    convert hgap using 1 <;> ring
  have hratio : (0.244 - 0.115 - 0.001 - 0.001 : ℝ) / 0.51 ≤ (E.card : ℝ) / k := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 0.51)]
    rw [mul_div_assoc] at hcancel
    linarith only [hcancel]
  refine ⟨hratio, (lt_div_iff₀ hk').mp ?_⟩
  exact (by norm_num : (0.24 : ℝ) < (0.244 - 0.115 - 0.001 - 0.001) / 0.51).trans_le hratio

/-- The reflected convolution `1_{A₁} * μ̌` appearing in the smoothness assumption (4). -/
noncomputable def smoothed (A₁ : Finset (ZMod p)) (μ : ZMod p → ℝ) (z : ZMod p) : ℝ :=
  ∑ a ∈ A₁, μ (a - z)

lemma smoothed_eq_convolution (A₁ : Finset (ZMod p)) (μ : ZMod p → ℝ) (z : ZMod p) :
    smoothed A₁ μ z = convolution (indicator A₁) (fun t ↦ μ (-t)) z := by
  simp [smoothed, convolution_indicator, neg_sub]

omit [NeZero p] in
private lemma predicted_le_sum_smoothed (A₁ R S : Finset (ZMod p)) (μ : ZMod p → ℝ)
    (hμ : ∀ z, 0 ≤ μ z) (z : ZMod p) :
    predicted (A₁ + R) S μ z ≤ (S.card : ℝ) * ∑ v ∈ R, smoothed A₁ μ (z - v) := by
  unfold predicted
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  calc
    (∑ u ∈ A₁ + R, μ (u - z)) ≤ ∑ b ∈ R ×ˢ A₁, μ (b.1 + b.2 - z) := by
      rw [add_comm A₁ R, Finset.add_def]
      exact Finset.sum_image_le_of_nonneg (fun u _ ↦ hμ (u - z))
    _ = _ := by
      rw [Finset.sum_product]
      refine Finset.sum_congr rfl fun v _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_
      congr 1
      abel

omit [NeZero p] in
/-- Counting all representations in `A₁ + R` and applying the smooth excess bound from (4). -/
lemma sum_predicted_le_of_smooth_cap (A₁ A₂ R S E : Finset (ZMod p)) (μ : ZMod p → ℝ) (k : ℕ)
    (hμ : ∀ z, 0 ≤ μ z) (hE : E ⊆ A₂)
    (hcap : ∀ v ∈ R, (∑ z ∈ A₂, max (smoothed A₁ μ (z - v) - (0.51 : ℝ) / k) 0) ≤ 0.001) :
    (∑ z ∈ E, predicted (A₁ + R) S μ z) ≤
      (R.card : ℝ) * S.card * (0.51 * (E.card : ℝ) / k + 0.001) := by
  have hshift (v : ZMod p) (hv : v ∈ R) :
      (∑ z ∈ E, smoothed A₁ μ (z - v)) ≤ 0.51 * (E.card : ℝ) / k + 0.001 := by
    have hexcess : (∑ z ∈ E, max (smoothed A₁ μ (z - v) - (0.51 : ℝ) / k) 0) ≤ 0.001 :=
      (Finset.sum_le_sum_of_subset_of_nonneg hE (fun _ _ _ ↦ le_max_right _ _)).trans (hcap v hv)
    calc
      _ ≤ ∑ z ∈ E, ((0.51 : ℝ) / k + max (smoothed A₁ μ (z - v) - (0.51 : ℝ) / k) 0) := by
        refine Finset.sum_le_sum fun z _ ↦ ?_
        have hz := le_max_left (smoothed A₁ μ (z - v) - (0.51 : ℝ) / k) 0
        linarith only [hz]
      _ ≤ _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        have hconst : (E.card : ℝ) * ((0.51 : ℝ) / k) = 0.51 * E.card / k := by ring
        rw [hconst]
        exact add_le_add le_rfl hexcess
  calc
    _ ≤ ∑ z ∈ E, (S.card : ℝ) * ∑ v ∈ R, smoothed A₁ μ (z - v) :=
      Finset.sum_le_sum fun z _ ↦ predicted_le_sum_smoothed A₁ R S μ hμ z
    _ = (S.card : ℝ) * ∑ v ∈ R, ∑ z ∈ E, smoothed A₁ μ (z - v) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (S.card : ℝ) * ∑ _ ∈ R, (0.51 * (E.card : ℝ) / k + 0.001) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hshift) (Nat.cast_nonneg _)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- The required hit count using the smooth excess bound and the two aggregate estimates in §5. -/
lemma exceptionalHits_section5 (A₁ A₂ R S : Finset (ZMod p)) (μ : ZMod p → ℝ) {k : ℕ}
    (hk : 0 < k) (hR : R.Nonempty) (hS : S.Nonempty) (hA₂ : A₂.card ≤ k)
    (hμ : ∀ z, 0 ≤ μ z)
    (hpred : (0.244 : ℝ) * R.card * S.card ≤ ∑ z ∈ A₂, predicted (A₁ + R) S μ z)
    (hobs : (∑ z ∈ A₂, observed (A₁ + R) S z) ≤ (0.115 : ℝ) * R.card * S.card)
    (hcap : ∀ v ∈ R, (∑ z ∈ A₂, max (smoothed A₁ μ (z - v) - (0.51 : ℝ) / k) 0) ≤ 0.001) :
    (0.244 - 0.115 - 0.001 - 0.001 : ℝ) / 0.51 ≤
      ((exceptionalHits A₂ (A₁ + R) S μ R.card k).card : ℝ) / k ∧
    (0.24 : ℝ) * k < (exceptionalHits A₂ (A₁ + R) S μ R.card k).card := by
  apply exceptionalHits_lower_of_prediction_cap _ _ _ _ hR.card_pos hk hS hA₂ hpred hobs
  exact sum_predicted_le_of_smooth_cap A₁ A₂ R S _ μ k hμ Finset.inter_subset_left hcap

end OnePercent.Fourier

end FourierDiscrepancy

/- Source: one-percent-formal/assembly/AssemblyModel.lean -/
section AssemblyModel

open Finset
open scoped Pointwise Classical
namespace Green39.Assembly
noncomputable section

abbrev Points (p : ℕ) := Finset (ZMod p)
abbrev Law (p : ℕ) := ZMod p → ℝ
abbrev Sample (p : ℕ) := Points p × Points p
abbrev W (p : ℕ) := Points p × Points p × Law p
abbrev half (k : ℕ) := k / 2
abbrev rest (k : ℕ) := k - k / 2
abbrev rSize (k : ℕ) := k / 10
abbrev sMax (k : ℕ) := k / 1000
def x (p i : ℕ) := Transcripts.level (Real.log ((p : ℝ) / p.sqrt)) i
def eta (x : ℝ) := Real.exp (-1000 - 0.22 * x)

structure Catalog (p : ℕ) where
  stages : ℕ
  containers : ℕ → Finset (Points p)
  laws : ℕ → Finset (Law p)

variable {p : ℕ} [NeZero p]
open OnePercent.Fourier

/-- The input at index zero is the entire group. At the last index the
containers are the outputs of the last active stage alone. -/
structure StageSpec (C : Catalog p) : Prop where
  initial : univ ∈ C.containers 0
  active : ∀ i < C.stages, 5000 < x p i
  stop : x p C.stages ≤ 5000
  containerSize : ∀ i ≤ C.stages, ∀ P ∈ C.containers i,
    (P.card : ℝ) ≤ p.sqrt * Real.exp (x p i)
  capped : ∀ i < C.stages, ∀ μ ∈ C.laws i, (∀ z, 0 ≤ μ z) ∧
    (∑ z, μ z) = 1 ∧ ∀ z, μ z ≤ 2 / (10 ^ 24 * (p.sqrt : ℝ))
  alternative : ∀ i < C.stages, ∀ P ∈ C.containers i, ∀ V ⊆ P,
    (0.11 : ℝ) * p.sqrt ≤ (V.card : ℝ) → (V.card : ℝ) ≤ 2 * p.sqrt →
    (∃ F ⊆ V, (p.sqrt : ℝ) * Transcripts.lossRate (x p i) ≤ (F.card : ℝ) ∧
      ∃ μ ∈ C.laws i, FourierFit F μ (5 * eta (x p i) * F.card)) ∨
    ∃ Q ∈ C.containers (i+1), ((V \ Q).card : ℝ) ≤
      p.sqrt * Transcripts.lossRate (x p i)

def witnesses (C : Catalog p) (i : ℕ) : Finset (W p) :=
  (C.containers i).biUnion fun P =>
    ((P.powersetCard (rSize p.sqrt)) ×ˢ
      ((P.powerset.filter fun S => S.Nonempty ∧ S.card ≤ sMax p.sqrt) ×ˢ C.laws i)).filter
      fun w => FourierFit w.2.1 w.2.2 (7 * eta (x p i) * w.2.1.card)

def hits (w : W p) (q : Sample p) : Prop :=
  (0.24 : ℝ) * p.sqrt ≤
    (exceptionalHits q.2 (q.1 + w.1) w.2.1 w.2.2 w.1.card p.sqrt).card

def typical (μ : Law p) (q : Sample p) : Prop :=
  (∑ u, |convolution (indicator q.2) μ u - (q.2.card : ℝ) / p|) ≤
    (0.00000001 : ℝ) * p.sqrt ∧
  ∀ v, (∑ z ∈ q.2, max (smoothed q.1 μ (z-v) - 0.51 / p.sqrt) 0) ≤ 0.001

theorem numerical {k : ℕ} (hk : 100000 ≤ k) (hp : p < (k+1)^2) :
    (p : ℝ) ≤ 1.0001 * k^2 ∧
    (0.0999 : ℝ) * k ≤ (rSize k : ℝ) ∧
    (0.244 : ℝ) * rSize k ≤
      (rest k : ℝ) * ((half k : ℝ) - 0.0114*k) * rSize k / p - 0.00000001*k := by
  have hk' : (100000 : ℝ) ≤ k := by exact_mod_cast hk
  have hp' : (p : ℝ) < ((k : ℝ)+1)^2 := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne p))
  have hk2 : (100000 : ℝ) * k ≤ (k : ℝ)^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hk') (Nat.cast_nonneg k)]
  have hpc : (p : ℝ) ≤ 1.0001 * k^2 := by nlinarith
  have hr : (k : ℝ) ≤ 10*(rSize k : ℝ)+9 := by exact_mod_cast (show k ≤ 10*rSize k+9 by dsimp [rSize]; omega)
  have hr' : (0.0999 : ℝ)*k ≤ (rSize k : ℝ) := by linarith
  refine ⟨hpc, hr', ?_⟩
  have h1 : (k : ℝ) ≤ 2*(half k : ℝ)+1 := by exact_mod_cast (show k ≤ 2*half k+1 by dsimp [half]; omega)
  have h2 : (k : ℝ) ≤ 2*(rest k : ℝ) := by exact_mod_cast (show k ≤ 2*rest k by dsimp [rest]; omega)
  have hmul := mul_le_mul (show (0.5:ℝ)*k ≤ rest k by linarith)
    (show (0.48859:ℝ)*k ≤ (half k : ℝ) - 0.0114*k by linarith)
    (by positivity) (Nat.cast_nonneg _)
  have hmul' : (0.2441:ℝ)*p ≤ (rest k : ℝ)*((half k : ℝ)-0.0114*k) := by nlinarith
  have htimes := mul_le_mul_of_nonneg_right hmul' (Nat.cast_nonneg (rSize k))
  have hdiv : (0.2441:ℝ)*rSize k ≤ (rest k : ℝ)*((half k : ℝ)-0.0114*k)*rSize k/p := by
    apply (le_div_iff₀ hp0).mpr
    linarith only [htimes]
  linarith

/-- Retention with early exit: only an actually fitted target produces a witness. -/
theorem iterate {C : Catalog p} (spec : StageSpec C) (G : Points p)
    (_hk : 0 < p.sqrt) (hstart : (p.sqrt : ℝ)/9 ≤ G.card)
    (hsize : (G.card : ℝ) ≤ 2*p.sqrt) :
    (∃ i < C.stages, ∃ P ∈ C.containers i, ∃ V ⊆ P, V ⊆ G ∧
      (0.11 : ℝ)*p.sqrt ≤ V.card ∧ ∃ F ⊆ V,
      (p.sqrt : ℝ)*Transcripts.lossRate (x p i) ≤ F.card ∧
      ∃ μ ∈ C.laws i, FourierFit F μ (5*eta (x p i)*F.card)) ∨
    ∃ P ∈ C.containers C.stages, (0.11 : ℝ)*p.sqrt ≤ (G ∩ P).card := by
  classical
  by_cases hf : ∃ i < C.stages, ∃ P ∈ C.containers i, ∃ V ⊆ P, V ⊆ G ∧
      (0.11 : ℝ)*p.sqrt ≤ V.card ∧ ∃ F ⊆ V,
      (p.sqrt : ℝ)*Transcripts.lossRate (x p i) ≤ F.card ∧
      ∃ μ ∈ C.laws i, FourierFit F μ (5*eta (x p i)*F.card)
  · exact Or.inl hf
  right
  let loss (j : ℕ) := ∑ i ∈ range j, Transcripts.lossRate (x p i)
  have margin (j : ℕ) (hj : j ≤ C.stages) :
      (0.11:ℝ)*p.sqrt ≤ (G.card : ℝ) - p.sqrt * loss j := by
    have h : loss j ≤ 4/(3*(5000:ℝ)^2) := by
      cases j with
      | zero => norm_num [loss]
      | succ i => exact (Transcripts.sum_lossRate_lt (spec.active i (by omega))).le
    have hm := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg p.sqrt)
    linarith
  have path (j : ℕ) (hj : j ≤ C.stages) : ∃ P ∈ C.containers j,
      (G.card : ℝ) - p.sqrt * loss j ≤ (G ∩ P).card := by
    induction j with
    | zero => exact ⟨univ, spec.initial, by simp [loss]⟩
    | succ i ih =>
      obtain ⟨P,hP,hV⟩ := ih (by omega)
      let V := G ∩ P
      have hG : V ⊆ G := inter_subset_left
      have hVP : V ⊆ P := inter_subset_right
      have hbig := (margin i (by omega)).trans hV
      rcases spec.alternative i (by omega) P hP V hVP hbig
          ((Nat.cast_le.mpr (card_le_card hG)).trans hsize) with hfit | ⟨Q,hQ,hcut⟩
      · exact (hf ⟨i,by omega,P,hP,V,hVP,hG,hbig,hfit⟩).elim
      · refine ⟨Q,hQ,?_⟩
        have he := card_sdiff_add_card_inter V Q
        have he' : ((V \ Q).card : ℝ) + (V ∩ Q).card = V.card := by exact_mod_cast he
        have hle : ((V ∩ Q).card : ℝ) ≤ (G ∩ Q).card :=
          Nat.cast_le.mpr (card_le_card (inter_subset_inter_right hG))
        have hl : loss (i+1) = loss i + Transcripts.lossRate (x p i) := sum_range_succ _ _
        change _ ≤ (V.card : ℝ) at hV
        rw [hl]
        linarith
  obtain ⟨P,hP,h⟩ := path _ le_rfl
  exact ⟨P,hP,(margin _ le_rfl).trans h⟩

end
end Green39.Assembly

end AssemblyModel

/- Source: one-percent-formal/concentration/SliceConcentration.lean -/
section SliceConcentration

/-
# Exchange bounded differences on a finite slice

The sample is a uniformly chosen `k`-subset of a finite population. The proof
exposes one element at a time and couples two choices by a transposition.
This is the concentration argument in §1 of `overnight-astra/review/one-percent.md`.
-/

open MeasureTheory
open scoped BigOperators Classical


namespace Green39.Concentration

noncomputable section

variable {α : Type*} [DecidableEq α]

/-- The arithmetic mean over a finite sample space. -/
def mean (s : Finset α) (f : α → ℝ) : ℝ :=
  (∑ a ∈ s, f a) / s.card

/-- Expectation under the uniform law on the `k`-element subsets of `s`. -/
def sliceMean (s : Finset α) (k : ℕ) (f : Finset α → ℝ) : ℝ :=
  mean (s.powersetCard k) f

/-- Two elements of the slice at exchange distance at most one have observable
values within `L` of each other. -/
def ExchangeLipschitz (s : Finset α) (k : ℕ) (f : Finset α → ℝ) (L : ℝ) : Prop :=
  ∀ A ∈ s.powersetCard k, ∀ B ∈ s.powersetCard k,
    (A \ B).card ≤ 1 → |f A - f B| ≤ L

private theorem mem_slice_insert {s A : Finset α} {k : ℕ} {x : α} (hx : x ∈ s)
    (hA : A ∈ (s.erase x).powersetCard k) :
    insert x A ∈ s.powersetCard (k + 1) := by
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hA
  have hnot : x ∉ A := fun h ↦ Finset.notMem_erase x s (hsub h)
  exact Finset.mem_powersetCard.mpr
    ⟨Finset.insert_subset_iff.mpr ⟨hx, hsub.trans (Finset.erase_subset _ _)⟩,
      by rw [Finset.card_insert_of_notMem hnot, hcard]⟩

/-- Exposing an element preserves the exchange bound on the remaining slice. -/
theorem ExchangeLipschitz.insert {s : Finset α} {k : ℕ} {f : Finset α → ℝ} {L : ℝ}
    (hf : ExchangeLipschitz s (k + 1) f L) {x : α} (hx : x ∈ s) :
    ExchangeLipschitz (s.erase x) k (fun A ↦ f (insert x A)) L := by
  intro A hA B hB hd
  apply hf _ (mem_slice_insert hx hA) _ (mem_slice_insert hx hB)
  refine (Finset.card_le_card ?_).trans hd
  intro z hz
  simp only [Finset.mem_sdiff, Finset.mem_insert] at hz ⊢
  tauto

private theorem sum_slice_insert (s : Finset α) (k : ℕ) (f : Finset α → ℝ)
    {x : α} (hx : x ∈ s) :
    ∑ A ∈ (s.erase x).powersetCard k, f (insert x A) =
      ∑ B ∈ (s.powersetCard (k + 1)).filter (fun B ↦ x ∈ B), f B := by
  refine Finset.sum_bij (fun A _ ↦ insert x A) (fun A hA ↦ ?_) (fun A hA B hB h ↦ ?_)
    (fun B hB ↦ ?_) (fun _ _ ↦ rfl)
  · simp [mem_slice_insert hx hA]
  · have erase_insert (C : Finset α) (hC : C ∈ (s.erase x).powersetCard k) :
        (insert x C).erase x = C :=
      Finset.erase_insert <| fun hxC ↦ Finset.notMem_erase x s ((Finset.mem_powersetCard.mp hC).1 hxC)
    simpa only [erase_insert A hA, erase_insert B hB] using congrArg (fun C ↦ C.erase x) h
  · obtain ⟨hB, hxB⟩ := Finset.mem_filter.mp hB
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hB
    refine ⟨B.erase x, Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, Finset.insert_erase hxB⟩
    · exact Finset.erase_subset_erase _ hsub
    · rw [Finset.card_erase_of_mem hxB, hcard, Nat.add_sub_cancel]

private theorem sum_slice_first (s : Finset α) (k : ℕ) (f : Finset α → ℝ) :
    (∑ x ∈ s, ∑ A ∈ (s.erase x).powersetCard k, f (insert x A)) =
      (k + 1 : ℝ) * ∑ B ∈ s.powersetCard (k + 1), f B := by
  calc
    _ = ∑ x ∈ s, ∑ B ∈ s.powersetCard (k + 1), if x ∈ B then f B else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [sum_slice_insert s k f hx, Finset.sum_filter]
    _ = ∑ B ∈ s.powersetCard (k + 1), ∑ x ∈ s, if x ∈ B then f B else 0 :=
      Finset.sum_comm
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B hB
      obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hB
      have hfilter : s.filter (fun x ↦ x ∈ B) = B := by
        ext x
        exact Finset.mem_filter.trans ⟨And.right, fun hx ↦ ⟨hsub hx, hx⟩⟩
      rw [← Finset.sum_filter, hfilter, Finset.sum_const, nsmul_eq_mul, hcard, Nat.cast_add,
        Nat.cast_one]

/-- A uniformly chosen first element, followed by a uniform completion, gives
the uniform law on the full slice. -/
theorem sliceMean_succ (s : Finset α) (k : ℕ) (f : Finset α → ℝ) :
    sliceMean s (k + 1) f =
      mean s (fun x ↦ sliceMean (s.erase x) k (fun A ↦ f (insert x A))) := by
  let d := (s.card - 1).choose k
  have hcard (x : α) (hx : x ∈ s) : ((s.erase x).powersetCard k).card = d := by
    rw [Finset.card_powersetCard, Finset.card_erase_of_mem hx]
  have hcounts : (s.card : ℝ) * d = (k + 1 : ℝ) * (s.powersetCard (k + 1)).card := by
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, hcard] using
      calc
        (s.card : ℝ) * d = ∑ x ∈ s, (∑ _A ∈ (s.erase x).powersetCard k, (1 : ℝ)) := by
          simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
          calc
            _ = ∑ _x ∈ s, (d : ℝ) := by simp [nsmul_eq_mul]
            _ = _ := Finset.sum_congr rfl (fun x hx ↦ by rw [hcard x hx])
        _ = _ := sum_slice_first s k (fun _ ↦ 1)
  unfold sliceMean mean
  have hsum :
      (∑ x ∈ s, (∑ A ∈ (s.erase x).powersetCard k, f (insert x A)) /
        ((s.erase x).powersetCard k).card) =
      (∑ x ∈ s, ∑ A ∈ (s.erase x).powersetCard k, f (insert x A)) / d := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun x hx ↦ by rw [hcard x hx])
  rw [hsum, sum_slice_first, div_div, mul_comm (d : ℝ), hcounts, mul_div_mul_left _ _ (by positivity)]

private theorem sliceMean_insert_eq_mean_filter (s : Finset α) (k : ℕ)
    (f : Finset α → ℝ) {x : α} (hx : x ∈ s) :
    sliceMean (s.erase x) k (fun A ↦ f (insert x A)) =
      mean ((s.powersetCard (k + 1)).filter (fun B ↦ x ∈ B)) f := by
  have hcard :
      (((s.erase x).powersetCard k).card : ℝ) =
        (((s.powersetCard (k + 1)).filter (fun B ↦ x ∈ B)).card : ℝ) := by
    simpa using sum_slice_insert s k (fun _ ↦ 1) hx
  unfold sliceMean mean
  rw [sum_slice_insert s k f hx, hcard]

private def swapSet (x y : α) (A : Finset α) : Finset α :=
  A.map (Equiv.swap x y).toEmbedding

private theorem mem_swapSet {x y z : α} {A : Finset α} :
    z ∈ swapSet x y A ↔ Equiv.swap x y z ∈ A := by
  rw [swapSet, Finset.mem_map]
  exact ⟨fun ⟨a, ha, haz⟩ ↦ by
    change Equiv.swap x y a = z at haz
    simpa [← haz] using ha,
    fun hz ↦ ⟨Equiv.swap x y z, hz, Equiv.swap_apply_self _ _ _⟩⟩

private theorem swapSet_swapSet (x y : α) (A : Finset α) :
    swapSet x y (swapSet x y A) = A := by
  ext z
  simp only [mem_swapSet, Equiv.swap_apply_self]

private theorem swap_mem {s : Finset α} {x y z : α}
    (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s) : Equiv.swap x y z ∈ s := by
  by_cases hzx : z = x
  · simpa [hzx] using hy
  by_cases hzy : z = y
  · simpa [hzy] using hx
  simpa [Equiv.swap_apply_of_ne_of_ne hzx hzy] using hz

private theorem swapSet_mem_filter {s A : Finset α} {k : ℕ} {x y : α}
    (hx : x ∈ s) (hy : y ∈ s)
    (hA : A ∈ (s.powersetCard k).filter (fun B ↦ x ∈ B)) :
    swapSet x y A ∈ (s.powersetCard k).filter (fun B ↦ y ∈ B) := by
  obtain ⟨hA, hxA⟩ := Finset.mem_filter.mp hA
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hA
  refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
  · intro z hz
    have hm := swap_mem hx hy (hsub (mem_swapSet.mp hz))
    simpa only [Equiv.swap_apply_self] using hm
  · simpa [swapSet] using hcard
  · simpa only [mem_swapSet, Equiv.swap_apply_right] using hxA

private theorem card_sdiff_swapSet_le_one {x y : α} {A : Finset α} (hx : x ∈ A) :
    (A \ swapSet x y A).card ≤ 1 := by
  have hsub : A \ swapSet x y A ⊆ {x} := by
    intro z hz
    obtain ⟨hzA, hzswap⟩ := Finset.mem_sdiff.mp hz
    by_contra hzx
    have hne : z ≠ x := by simpa using hzx
    apply hzswap
    rw [mem_swapSet]
    by_cases hzy : z = y
    · simpa [hzy] using hx
    simpa [Equiv.swap_apply_of_ne_of_ne hne hzy] using hzA
  simpa using Finset.card_le_card hsub

private theorem abs_mean_le {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {f : ι → ℝ} {L : ℝ} (hf : ∀ x ∈ s, |f x| ≤ L) : |mean s f| ≤ L := by
  have hpos : 0 < (s.card : ℝ) := by exact_mod_cast hs.card_pos
  rw [mean, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  calc
    |∑ x ∈ s, f x| ≤ ∑ x ∈ s, |f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ s, L := Finset.sum_le_sum hf
    _ = _ := by simp [nsmul_eq_mul, mul_comm]

/-- Any two first choices give conditional means within one exchange bound.
The coupling applies the same transposition to the entire completion. -/
theorem abs_sliceMean_insert_sub_le {s : Finset α} {k : ℕ} {f : Finset α → ℝ} {L : ℝ}
    (hk : k + 1 ≤ s.card) (hf : ExchangeLipschitz s (k + 1) f L)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s) :
    |sliceMean (s.erase x) k (fun A ↦ f (insert x A)) -
      sliceMean (s.erase y) k (fun A ↦ f (insert y A))| ≤ L := by
  rw [sliceMean_insert_eq_mean_filter s k f hx, sliceMean_insert_eq_mean_filter s k f hy]
  let S := (s.powersetCard (k + 1)).filter (fun B ↦ x ∈ B)
  let T := (s.powersetCard (k + 1)).filter (fun B ↦ y ∈ B)
  change |mean S f - mean T f| ≤ L
  have hS : S.Nonempty := by
    have hle : k ≤ (s.erase x).card := by rw [Finset.card_erase_of_mem hx]; omega
    obtain ⟨A, hA⟩ := Finset.powersetCard_nonempty.mpr hle
    exact ⟨insert x A, Finset.mem_filter.mpr ⟨mem_slice_insert hx hA, Finset.mem_insert_self _ _⟩⟩
  have sum_swap (g : Finset α → ℝ) : ∑ A ∈ S, g (swapSet x y A) = ∑ B ∈ T, g B := by
    refine Finset.sum_bij (fun A _ ↦ swapSet x y A) (fun A hA ↦ swapSet_mem_filter hx hy hA)
      (fun A _ B _ h ↦ ?_) (fun B hB ↦ ?_) (fun _ _ ↦ rfl)
    · simpa only [swapSet_swapSet] using congrArg (swapSet x y) h
    · have hs : swapSet x y B = swapSet y x B := by simp [swapSet, Equiv.swap_comm x y]
      exact ⟨swapSet x y B, hs.symm ▸ swapSet_mem_filter hy hx hB, swapSet_swapSet x y B⟩
  have hcard : (S.card : ℝ) = (T.card : ℝ) := by
    simpa using sum_swap (fun _ ↦ 1)
  have hdiff : mean S f - mean T f = mean S (fun A ↦ f A - f (swapSet x y A)) := by
    rw [mean, mean, mean, Finset.sum_sub_distrib, sum_swap, hcard, sub_div]
  rw [hdiff]
  apply abs_mean_le hS
  intro A hA
  obtain ⟨hAA, hxA⟩ := Finset.mem_filter.mp hA
  exact hf A hAA _ (Finset.mem_filter.mp (swapSet_mem_filter hx hy hA)).1
    (card_sdiff_swapSet_le_one (y := y) hxA)

private theorem mean_congr {ι : Type*} (s : Finset ι) {f g : ι → ℝ}
    (h : ∀ x ∈ s, f x = g x) : mean s f = mean s g := by
  unfold mean
  rw [Finset.sum_congr rfl h]

private theorem mean_mono {ι : Type*} (s : Finset ι) {f g : ι → ℝ}
    (h : ∀ x ∈ s, f x ≤ g x) : mean s f ≤ mean s g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum h) (Nat.cast_nonneg _)

private theorem mean_const {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (c : ℝ) :
    mean s (fun _ ↦ c) = c := by
  have hpos : 0 < (s.card : ℝ) := by exact_mod_cast hs.card_pos
  rw [mean, Finset.sum_const, nsmul_eq_mul, mul_comm, mul_div_cancel_right₀ _ hpos.ne']

private theorem mean_const_mul {ι : Type*} (s : Finset ι) (a : ℝ) (f : ι → ℝ) :
    mean s (fun x ↦ a * f x) = a * mean s f := by
  rw [mean, ← Finset.mul_sum, mul_div_assoc, mean]

private theorem mean_sub {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    mean s (fun x ↦ f x - g x) = mean s f - mean s g := by
  unfold mean
  rw [Finset.sum_sub_distrib, sub_div]

private theorem abs_sub_mean_le {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {f : ι → ℝ} {L : ℝ} {x : ι} (hx : x ∈ s)
    (h : ∀ a ∈ s, ∀ b ∈ s, |f a - f b| ≤ L) : |f x - mean s f| ≤ L := by
  rw [← mean_const hs (f x), ← mean_sub]
  exact abs_mean_le hs (h x hx)

private theorem mean_exp_centered_le {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {f : ι → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x ∈ s, |f x - mean s f| ≤ L) (t : ℝ) :
    mean s (fun x ↦ Real.exp (t * (f x - mean s f))) ≤ Real.exp (L ^ 2 * t ^ 2 / 2) := by
  let : MeasurableSpace ↥s := ⊤
  let : Nonempty ↥s := by
    obtain ⟨x, hx⟩ := hs
    exact ⟨⟨x, hx⟩⟩
  let p := PMF.uniformOfFintype ↥s
  have integral_mean (g : ι → ℝ) :
      (∫ x : ↥s, g x ∂p.toMeasure) = mean s g := by
    rw [PMF.integral_eq_sum]
    simp only [p, PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      Fintype.card_coe, smul_eq_mul]
    rw [← Finset.mul_sum, ← Finset.sum_subtype s (fun _ ↦ Iff.rfl), mean, div_eq_mul_inv, mul_comm]
  let X : ↥s → ℝ := fun x ↦ f x - mean s f
  have hmeas : AEMeasurable X p.toMeasure := Measurable.of_discrete.aemeasurable
  have hbound : ∀ᵐ x ∂p.toMeasure, X x ∈ Set.Icc (-L) L :=
    Filter.Eventually.of_forall (fun x ↦ abs_le.mp (hf x x.2))
  have hzero : (∫ x, X x ∂p.toMeasure) = 0 := by
    change (∫ x : ↥s, (f x - mean s f) ∂p.toMeasure) = 0
    rw [integral_mean (fun x ↦ f x - mean s f), mean_sub, mean_const hs, sub_self]
  have h := (ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    hmeas hbound hzero).mgf_le t
  change (∫ x : ↥s, Real.exp (t * (f x - mean s f)) ∂p.toMeasure) ≤ _ at h
  rw [integral_mean (fun x ↦ Real.exp (t * (f x - mean s f)))] at h
  have hwidth : (↑‖L - -L‖₊ : ℝ) / 2 = L := by
    change ‖L - -L‖ / 2 = L
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    ring
  simpa only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, hwidth] using h

/-- The centered moment generating function on the uniform slice is bounded
by that of a centered Gaussian with variance parameter `k * L²`. -/
theorem sliceMean_exp_centered_le {s : Finset α} {k : ℕ} {f : Finset α → ℝ} {L : ℝ}
    (hk : k ≤ s.card) (hf : ExchangeLipschitz s k f L) (hL : 0 ≤ L) (t : ℝ) :
    sliceMean s k (fun A ↦ Real.exp (t * (f A - sliceMean s k f))) ≤
      Real.exp ((k : ℝ) * L ^ 2 * t ^ 2 / 2) := by
  induction k generalizing s f with
  | zero => simp [sliceMean, mean, Finset.powersetCard_zero]
  | succ k ih =>
      let g : α → ℝ := fun x ↦ sliceMean (s.erase x) k (fun A ↦ f (insert x A))
      let m := sliceMean s (k + 1) f
      have hs : s.Nonempty := Finset.card_pos.mp (by omega)
      have hm : m = mean s g := sliceMean_succ s k f
      have hg (x : α) (hx : x ∈ s) : |g x - mean s g| ≤ L :=
        abs_sub_mean_le hs hx (fun _ ha _ hb ↦ abs_sliceMean_insert_sub_le hk hf ha hb)
      let C := Real.exp ((k : ℝ) * L ^ 2 * t ^ 2 / 2)
      rw [sliceMean_succ]
      change mean s (fun x ↦ sliceMean (s.erase x) k
        (fun A ↦ Real.exp (t * (f (insert x A) - m)))) ≤ _
      calc
        _ = mean s (fun x ↦
            Real.exp (t * (g x - m)) * sliceMean (s.erase x) k
              (fun A ↦ Real.exp (t * (f (insert x A) - g x)))) := by
          apply mean_congr
          intro x _
          unfold sliceMean
          rw [← mean_const_mul]
          apply mean_congr
          intro A _
          rw [← Real.exp_add]
          congr 1
          ring
        _ ≤ mean s (fun x ↦ C * Real.exp (t * (g x - m))) := by
          apply mean_mono
          intro x hx
          have hcard : k ≤ (s.erase x).card := by rw [Finset.card_erase_of_mem hx]; omega
          rw [mul_comm C]
          exact mul_le_mul_of_nonneg_left (ih hcard (hf.insert hx)) (Real.exp_nonneg _)
        _ = C * mean s (fun x ↦ Real.exp (t * (g x - mean s g))) := by
          rw [hm, mean_const_mul]
        _ ≤ C * Real.exp (L ^ 2 * t ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left (mean_exp_centered_le hs hL hg t) (Real.exp_nonneg _)
        _ = _ := by
          dsimp only [C]
          rw [← Real.exp_add, Nat.cast_succ]
          congr 1
          ring

/-- The probability of an event for a uniformly chosen `k`-subset of `s`. -/
def sliceProbability (s : Finset α) (k : ℕ) (E : Finset α → Prop) : ℝ :=
  (((s.powersetCard k).filter E).card : ℝ) / (s.powersetCard k).card

omit [DecidableEq α] in
private theorem sliceProbability_le_one (s : Finset α) {k : ℕ} (hk : k ≤ s.card)
    (E : Finset α → Prop) : sliceProbability s k E ≤ 1 := by
  have hpos : 0 < ((s.powersetCard k).card : ℝ) := by
    exact_mod_cast (Finset.powersetCard_nonempty.mpr hk).card_pos
  rw [sliceProbability, div_le_one₀ hpos]
  exact_mod_cast Finset.card_filter_le _ _

private theorem sliceProbability_or_le (s : Finset α) (k : ℕ) (E F : Finset α → Prop) :
    sliceProbability s k (fun A ↦ E A ∨ F A) ≤
      sliceProbability s k E + sliceProbability s k F := by
  let S := s.powersetCard k
  let events (P : Finset α → Prop) := S.filter P
  change ((events (fun A ↦ E A ∨ F A)).card : ℝ) / S.card ≤
    (events E).card / (S.card : ℝ) + (events F).card / (S.card : ℝ)
  rw [← add_div, ← Nat.cast_add]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have mem_events (P : Finset α → Prop) (A : Finset α) :
      A ∈ events P ↔ A ∈ S ∧ P A := Finset.mem_filter
  have hsub : events (fun A ↦ E A ∨ F A) ⊆ events E ∪ events F := by
    intro A hA
    obtain ⟨hA, hE | hF⟩ := (mem_events (fun B ↦ E B ∨ F B) A).mp hA
    · exact Finset.mem_union_left _ ((mem_events E A).mpr ⟨hA, hE⟩)
    · exact Finset.mem_union_right _ ((mem_events F A).mpr ⟨hA, hF⟩)
  exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

omit [DecidableEq α] in
private theorem sliceProbability_mul_exp_le (s : Finset α) (k : ℕ)
    (X : Finset α → ℝ) (u t : ℝ) (ht : 0 ≤ t) :
    sliceProbability s k (fun A ↦ u ≤ X A) * Real.exp (t * u) ≤
      sliceMean s k (fun A ↦ Real.exp (t * X A)) := by
  rw [sliceProbability, sliceMean, mean, div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    _ = ∑ _A ∈ (s.powersetCard k).filter (fun A ↦ u ≤ X A), Real.exp (t * u) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ A ∈ (s.powersetCard k).filter (fun A ↦ u ≤ X A), Real.exp (t * X A) := by
      apply Finset.sum_le_sum
      intro A hA
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hA).2 ht)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ ↦ Real.exp_nonneg _)

/-- One-sided bounded differences for a uniform slice. -/
theorem sliceProbability_ge_le {s : Finset α} {k : ℕ} {f : Finset α → ℝ} {L u : ℝ}
    (hk : k ≤ s.card) (hf : ExchangeLipschitz s k f L) (hL : 0 ≤ L) (hu : 0 ≤ u) :
    sliceProbability s k (fun A ↦ u ≤ f A - sliceMean s k f) ≤
      Real.exp (-u ^ 2 / (2 * (k : ℝ) * L ^ 2)) := by
  let v := (k : ℝ) * L ^ 2
  have hden : 2 * (k : ℝ) * L ^ 2 = 2 * v := by dsimp [v]; ring
  rw [hden]
  by_cases hv : v = 0
  · simpa [hv] using sliceProbability_le_one s hk (fun A ↦ u ≤ f A - sliceMean s k f)
  have hvpos : 0 < v := lt_of_le_of_ne (by dsimp [v]; positivity) (Ne.symm hv)
  let t := u / v
  have ht : 0 ≤ t := div_nonneg hu hvpos.le
  have hmarkov := sliceProbability_mul_exp_le s k (fun A ↦ f A - sliceMean s k f) u t ht
  have hmgf := sliceMean_exp_centered_le hk hf hL t
  calc
    _ ≤ Real.exp (v * t ^ 2 / 2) / Real.exp (t * u) :=
      (le_div_iff₀ (Real.exp_pos _)).mpr (hmarkov.trans hmgf)
    _ = _ := by
      rw [← Real.exp_sub]
      congr 1
      dsimp [t]
      field_simp [hv]
      ring

omit [DecidableEq α] in
private theorem sliceMean_neg (s : Finset α) (k : ℕ) (f : Finset α → ℝ) :
    sliceMean s k (fun A ↦ -f A) = -sliceMean s k f := by
  simp [sliceMean, mean, Finset.sum_neg_distrib, neg_div]

/-- The lower tail has the same one-sided bound. -/
theorem sliceProbability_le_le {s : Finset α} {k : ℕ} {f : Finset α → ℝ} {L u : ℝ}
    (hk : k ≤ s.card) (hf : ExchangeLipschitz s k f L) (hL : 0 ≤ L) (hu : 0 ≤ u) :
    sliceProbability s k (fun A ↦ u ≤ sliceMean s k f - f A) ≤
      Real.exp (-u ^ 2 / (2 * (k : ℝ) * L ^ 2)) := by
  have hneg : ExchangeLipschitz s k (fun A ↦ -f A) L := by
    intro A hA B hB hAB
    change |-f A - -f B| ≤ L
    rw [show -f A - -f B = -(f A - f B) by ring, abs_neg]
    exact hf A hA B hB hAB
  simpa only [sliceMean_neg, neg_sub_neg] using sliceProbability_ge_le hk hneg hL hu

/-- The Green 39 exchange bounded-differences tail on the uniform slice. -/
theorem sliceProbability_abs_ge_le {s : Finset α} {k : ℕ} {f : Finset α → ℝ} {L u : ℝ}
    (hk : k ≤ s.card) (hf : ExchangeLipschitz s k f L) (hL : 0 ≤ L) (hu : 0 ≤ u) :
    sliceProbability s k (fun A ↦ u ≤ |f A - sliceMean s k f|) ≤
      2 * Real.exp (-u ^ 2 / (2 * (k : ℝ) * L ^ 2)) := by
  let m := sliceMean s k f
  have hE : (fun A : Finset α ↦ u ≤ |f A - m|) =
      (fun A ↦ u ≤ f A - m ∨ u ≤ m - f A) := by
    funext A
    exact propext (by rw [abs_eq_max_neg, le_max_iff, neg_sub])
  change sliceProbability s k (fun A ↦ u ≤ |f A - m|) ≤ _
  rw [hE]
  calc
    _ ≤ sliceProbability s k (fun A ↦ u ≤ f A - m) +
        sliceProbability s k (fun A ↦ u ≤ m - f A) := sliceProbability_or_le s k _ _
    _ ≤ _ := by
      rw [two_mul]
      exact add_le_add (sliceProbability_ge_le hk hf hL hu) (sliceProbability_le_le hk hf hL hu)

/-- If the variance parameter vanishes, the observable is constant on the slice. -/
theorem eq_sliceMean_of_variance_zero {s : Finset α} {k : ℕ} {f : Finset α → ℝ} {L : ℝ}
    (hk : k ≤ s.card) (hf : ExchangeLipschitz s k f L) (hL : 0 ≤ L)
    (hv : (k : ℝ) * L ^ 2 = 0) {A : Finset α} (hA : A ∈ s.powersetCard k) :
    f A = sliceMean s k f := by
  let m := sliceMean s k f
  let S := s.powersetCard k
  let d : ℝ := S.card
  by_contra hne
  have hd : 0 < d := by
    change 0 < (S.card : ℝ)
    exact_mod_cast (Finset.card_pos.mpr ⟨A, hA⟩ : 0 < S.card)
  have hne' : f A - m ≠ 0 := sub_ne_zero.mpr hne
  let t := d / (f A - m)
  have ht : t * (f A - m) = d := div_mul_cancel₀ _ hne'
  have hmgf := sliceMean_exp_centered_le hk hf hL t
  rw [hv, zero_mul, zero_div, Real.exp_zero] at hmgf
  change (∑ B ∈ S, Real.exp (t * (f B - m))) / d ≤ 1 at hmgf
  have hsum : (∑ B ∈ S, Real.exp (t * (f B - m))) ≤ d := by
    simpa only [one_mul] using (div_le_iff₀ hd).mp hmgf
  have hpoint : Real.exp (t * (f A - m)) ≤ ∑ B ∈ S, Real.exp (t * (f B - m)) :=
    Finset.single_le_sum (fun B _ ↦ Real.exp_nonneg (t * (f B - m))) hA
  rw [ht] at hpoint
  linarith [Real.add_one_le_exp d, hpoint.trans hsum]

end

end Green39.Concentration

end SliceConcentration

/- Source: one-percent-formal/split/SplitLaws.lean -/
section SplitLaws

/-
# Uniform ordered splits of a finite population

The two descriptions condition on the first half or on the union. Their
fibers are uniform slices, with constant cardinality on each marginal.
-/

open Finset
open scoped BigOperators Classical


namespace Green39.Split

open Concentration

noncomputable section

variable {α : Type*} [DecidableEq α]

/-- The uniform sample space of ordered disjoint pairs with the indicated sizes. -/
def orderedPairs (s : Finset α) (k₁ k₂ : ℕ) : Finset (Finset α × Finset α) :=
  (s.powersetCard k₁ ×ˢ s.powersetCard k₂).filter fun q ↦ Disjoint q.1 q.2

@[simp] theorem mem_orderedPairs {s : Finset α} {k₁ k₂ : ℕ} {q : Finset α × Finset α} :
    q ∈ orderedPairs s k₁ k₂ ↔
      q.1 ⊆ s ∧ q.1.card = k₁ ∧ q.2 ⊆ s ∧ q.2.card = k₂ ∧ Disjoint q.1 q.2 := by
  simp only [orderedPairs, mem_filter, mem_product, mem_powersetCard]
  tauto

/-- Uniform probability on a finite sample space, with value zero for an empty space. -/
def probability {β : Type*} (S : Finset β) (E : β → Prop) : ℝ :=
  ((S.filter E).card : ℝ) / S.card

omit [DecidableEq α] in
theorem probability_mono {S : Finset α} {E F : α → Prop}
    (h : ∀ x ∈ S, E x → F x) :
    probability S E ≤ probability S F := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast card_le_card (show S.filter E ⊆ S.filter F from fun x hx ↦
    mem_filter.mpr ⟨(mem_filter.mp hx).1, h x (mem_filter.mp hx).1 (mem_filter.mp hx).2⟩)

omit [DecidableEq α] in
theorem sliceProbability_eq_probability (s : Finset α) (k : ℕ) (E : Finset α → Prop) :
    sliceProbability s k E = probability (s.powersetCard k) E := rfl

theorem orderedPairs_union_mem {s : Finset α} {k₁ k₂ : ℕ} {q : Finset α × Finset α}
    (hq : q ∈ orderedPairs s k₁ k₂) : q.1 ∪ q.2 ∈ s.powersetCard (k₁ + k₂) := by
  obtain ⟨h₁, hc₁, h₂, hc₂, hd⟩ := mem_orderedPairs.mp hq
  exact mem_powersetCard.mpr ⟨union_subset h₁ h₂, by rw [card_union_of_disjoint hd, hc₁, hc₂]⟩

/-- Counting a restricted first-half fiber leaves precisely the indicated second-half slice. -/
theorem card_firstFiber {s A₁ : Finset α} {k₁ k₂ : ℕ} (hA₁ : A₁ ∈ s.powersetCard k₁)
    (E : Finset α × Finset α → Prop) :
    (((orderedPairs s k₁ k₂).filter E).filter fun q ↦ q.1 = A₁).card =
      (((s \ A₁).powersetCard k₂).filter fun A₂ ↦ E (A₁, A₂)).card := by
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hA₁
  refine card_bij' (fun q _ ↦ q.2) (fun A₂ _ ↦ (A₁, A₂)) ?_ ?_ ?_ ?_
  · rintro ⟨B, C⟩ hq
    simp only [mem_filter, mem_orderedPairs, mem_powersetCard] at hq ⊢
    obtain ⟨⟨⟨_, _, hC, hsize, hd⟩, he⟩, rfl⟩ := hq
    refine ⟨⟨?_, hsize⟩, he⟩
    exact fun x hx ↦ mem_sdiff.mpr ⟨hC hx, fun hx' ↦ disjoint_left.mp hd hx' hx⟩
  · intro C hC
    simp only [mem_filter, mem_powersetCard] at hC
    obtain ⟨⟨hC, hc⟩, he⟩ := hC
    simp only [mem_filter, mem_orderedPairs]
    exact ⟨⟨⟨hsub, hcard, hC.trans sdiff_subset, hc, disjoint_left.mpr
      (fun _ hx hx' ↦ (mem_sdiff.mp (hC hx')).2 hx)⟩, he⟩, trivial⟩
  · rintro ⟨B, C⟩ hq
    have heq : B = A₁ := (mem_filter.mp hq).2
    simp [heq]
  · intro C _
    rfl

/-- Counting a restricted union fiber leaves precisely the indicated first-half slice. -/
theorem card_unionFiber {s A : Finset α} {k₁ k₂ : ℕ} (hA : A ∈ s.powersetCard (k₁ + k₂))
    (E : Finset α × Finset α → Prop) :
    (((orderedPairs s k₁ k₂).filter E).filter fun q ↦ q.1 ∪ q.2 = A).card =
      ((A.powersetCard k₁).filter fun A₁ ↦ E (A₁, A \ A₁)).card := by
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hA
  refine card_bij' (fun q _ ↦ q.1) (fun B _ ↦ (B, A \ B)) ?_ ?_ ?_ ?_
  · rintro ⟨B, C⟩ hq
    simp only [mem_filter, mem_orderedPairs, mem_powersetCard] at hq ⊢
    obtain ⟨⟨⟨_, hc, _, _, hd⟩, he⟩, rfl⟩ := hq
    exact ⟨⟨subset_union_left, hc⟩, by rwa [union_sdiff_cancel_left hd]⟩
  · intro B hB
    obtain ⟨⟨hB, hc⟩, he⟩ := (show (B ⊆ A ∧ B.card = k₁) ∧ E (B, A \ B) from
      ⟨mem_powersetCard.mp (mem_filter.mp hB).1, (mem_filter.mp hB).2⟩)
    simp only [mem_filter, mem_orderedPairs]
    refine ⟨⟨⟨hB.trans hsub, hc, sdiff_subset.trans hsub, ?_,
        disjoint_left.mpr (fun _ hx hx' ↦ (mem_sdiff.mp hx').2 hx)⟩, he⟩, ?_⟩
    · rw [card_sdiff_of_subset hB, hcard, hc]
      omega
    · exact sup_sdiff_cancel_right hB
  · rintro ⟨B, C⟩ hq
    simp only [mem_filter, mem_orderedPairs] at hq
    obtain ⟨⟨⟨_, _, _, _, hd⟩, _⟩, hUnion⟩ := hq
    rw [← hUnion, union_sdiff_cancel_left hd]
  · intro B _
    rfl

/-- Conditional on a first half of positive mass, the second half is uniform in its complement. -/
theorem conditional_first {s A₁ : Finset α} {k₁ k₂ : ℕ} (hA₁ : A₁ ∈ s.powersetCard k₁)
    (E : Finset α × Finset α → Prop) :
    probability ((orderedPairs s k₁ k₂).filter fun q ↦ q.1 = A₁) E =
      sliceProbability (s \ A₁) k₂ (fun A₂ ↦ E (A₁, A₂)) := by
  unfold probability sliceProbability
  rw [filter_comm, card_firstFiber hA₁, ← filter_true (orderedPairs s k₁ k₂),
    card_firstFiber hA₁, filter_true]

/-- Conditional on a union of positive mass, the first half is uniform in that union. -/
theorem conditional_union {s A : Finset α} {k₁ k₂ : ℕ} (hA : A ∈ s.powersetCard (k₁ + k₂))
    (E : Finset α × Finset α → Prop) :
    probability ((orderedPairs s k₁ k₂).filter fun q ↦ q.1 ∪ q.2 = A) E =
      sliceProbability A k₁ (fun A₁ ↦ E (A₁, A \ A₁)) := by
  unfold probability sliceProbability
  rw [filter_comm, card_unionFiber hA, ← filter_true (orderedPairs s k₁ k₂),
    card_unionFiber hA, filter_true]

private theorem probability_eq_mean_fibers {β γ : Type*} [DecidableEq γ]
    {S : Finset β} {T : Finset γ} {f : β → γ} {d : ℕ}
    (hmaps : ∀ x ∈ S, f x ∈ T) (hsize : ∀ y ∈ T, (S.filter fun x ↦ f x = y).card = d)
    (E : β → Prop) :
    probability S E = mean T (fun y ↦ probability (S.filter fun x ↦ f x = y) E) := by
  have htotal : S.card = T.card * d := calc
    S.card = ∑ y ∈ T, (S.filter fun x ↦ f x = y).card := card_eq_sum_card_fiberwise hmaps
    _ = ∑ _y ∈ T, d := sum_congr rfl hsize
    _ = T.card * d := by simp
  have hevent : (S.filter E).card =
      ∑ y ∈ T, ((S.filter fun x ↦ f x = y).filter E).card := by
    rw [card_eq_sum_card_fiberwise (fun x hx ↦ hmaps x (mem_filter.mp hx).1)]
    exact sum_congr rfl (fun y _ ↦ by rw [filter_comm])
  unfold probability mean
  rw [htotal, hevent, Nat.cast_mul, Nat.cast_sum]
  have hs : (∑ y ∈ T, (((S.filter fun x ↦ f x = y).filter E).card : ℝ) /
        ((S.filter fun x ↦ f x = y).card : ℝ)) =
      ∑ y ∈ T, (((S.filter fun x ↦ f x = y).filter E).card : ℝ) / (d : ℝ) :=
    sum_congr rfl (fun y hy ↦ by rw [hsize y hy])
  rw [hs, ← sum_div, div_div, mul_comm (d : ℝ)]

/-- Expose the first half uniformly, then sample the second half from its complement. -/
theorem probability_eq_mean_first (s : Finset α) (k₁ k₂ : ℕ)
    (E : Finset α × Finset α → Prop) :
    probability (orderedPairs s k₁ k₂) E =
      mean (s.powersetCard k₁)
        (fun A₁ ↦ sliceProbability (s \ A₁) k₂ (fun A₂ ↦ E (A₁, A₂))) := by
  have hmaps : ∀ q ∈ orderedPairs s k₁ k₂, q.1 ∈ s.powersetCard k₁ := fun _ hq ↦
    mem_powersetCard.mpr ⟨(mem_orderedPairs.mp hq).1, (mem_orderedPairs.mp hq).2.1⟩
  have hsize : ∀ A₁ ∈ s.powersetCard k₁,
      ((orderedPairs s k₁ k₂).filter fun q ↦ q.1 = A₁).card = (s.card - k₁).choose k₂ := by
    intro A₁ hA₁
    have h := card_firstFiber (k₂ := k₂) hA₁ (fun _ ↦ True)
    simp only [filter_true, card_powersetCard] at h
    rw [h, card_sdiff_of_subset (mem_powersetCard.mp hA₁).1, (mem_powersetCard.mp hA₁).2]
  rw [probability_eq_mean_fibers hmaps hsize]
  unfold mean
  congr 1
  exact sum_congr rfl (fun _ hA₁ ↦ conditional_first hA₁ E)

/-- Expose the union uniformly, then sample the first half from that union. -/
theorem probability_eq_mean_union (s : Finset α) (k₁ k₂ : ℕ)
    (E : Finset α × Finset α → Prop) :
    probability (orderedPairs s k₁ k₂) E =
      mean (s.powersetCard (k₁ + k₂))
        (fun A ↦ sliceProbability A k₁ (fun A₁ ↦ E (A₁, A \ A₁))) := by
  have hmaps : ∀ q ∈ orderedPairs s k₁ k₂, q.1 ∪ q.2 ∈ s.powersetCard (k₁ + k₂) :=
    fun _ ↦ orderedPairs_union_mem
  have hsize : ∀ A ∈ s.powersetCard (k₁ + k₂),
      ((orderedPairs s k₁ k₂).filter fun q ↦ q.1 ∪ q.2 = A).card = (k₁ + k₂).choose k₁ := by
    intro A hA
    have h := card_unionFiber hA (k₁ := k₁) (k₂ := k₂) (fun _ ↦ True)
    simpa only [filter_true, card_powersetCard, (mem_powersetCard.mp hA).2] using h
  rw [probability_eq_mean_fibers hmaps hsize]
  unfold mean
  congr 1
  exact sum_congr rfl (fun _ hA ↦ conditional_union hA E)

/-- The union itself has the uniform law on the slice of size k₁ + k₂. -/
theorem probability_union (s : Finset α) (k₁ k₂ : ℕ) (E : Finset α → Prop) :
    probability (orderedPairs s k₁ k₂) (fun q ↦ E (q.1 ∪ q.2)) =
      sliceProbability s (k₁ + k₂) E := by
  rw [probability_eq_mean_union]
  let U := s.powersetCard (k₁ + k₂)
  have hs (A : Finset α) (hA : A ∈ U) :
      sliceProbability A k₁ (fun B ↦ E (B ∪ (A \ B))) = if E A then 1 else 0 := by
    have hcard := (mem_powersetCard.mp hA).2
    have hpos : A.card.choose k₁ ≠ 0 := (Nat.choose_pos (by omega)).ne'
    have hfilter : ((A.powersetCard k₁).filter fun B ↦ E (B ∪ (A \ B))) =
        ((A.powersetCard k₁).filter fun _ ↦ E A) := by
      apply filter_congr
      intro B hB
      rw [show B ∪ (A \ B) = A from sup_sdiff_cancel_right (mem_powersetCard.mp hB).1]
    unfold sliceProbability
    rw [hfilter]
    by_cases he : E A
    · simp [he, hpos]
    · simp [he]
  change (∑ A ∈ U, sliceProbability A k₁ (fun B ↦ E (B ∪ (A \ B)))) / U.card = _
  rw [sum_congr rfl hs, ← sum_filter]
  simp only [sum_const, nsmul_eq_mul, mul_one, sliceProbability, U]

omit [DecidableEq α] in
theorem mean_le_of_forall_le {S : Finset α} {f : α → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ x ∈ S, f x ≤ b) : mean S f ≤ b := by
  by_cases hS : S.Nonempty
  · unfold mean
    rw [div_le_iff₀ (by exact_mod_cast hS.card_pos : (0 : ℝ) < S.card), mul_comm]
    simpa only [sum_const, nsmul_eq_mul] using sum_le_sum h
  · simp [mean, not_nonempty_iff_eq_empty.mp hS, hb]

omit [DecidableEq α] in
theorem probability_exists_le_sum {β : Type*} (S : Finset α) (T : Finset β) (E : β → α → Prop) :
    probability S (fun x ↦ ∃ y ∈ T, E y x) ≤ ∑ y ∈ T, probability S (E y) := by
  classical
  unfold probability
  rw [← sum_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  simp only [← Nat.cast_sum, Nat.cast_le]
  apply (card_le_card (t := T.biUnion (fun y ↦ S.filter (E y))) ?_).trans card_biUnion_le
  intro x hx
  simp only [mem_filter] at hx
  obtain ⟨hx, y, hy, he⟩ := hx
  exact mem_biUnion.mpr ⟨y, hy, mem_filter.mpr ⟨hx, he⟩⟩

/-- Complementation interchanges the two uniform slices inside the same union. -/
theorem sliceProbability_complement (A : Finset α) (k₁ k₂ : ℕ)
    (hA : A.card = k₁ + k₂) (E : Finset α → Prop) :
    sliceProbability A k₁ (fun B ↦ E (A \ B)) = sliceProbability A k₂ E := by
  have hmem {i j : ℕ} (hij : A.card = i + j) {B : Finset α}
      (hB : B ∈ A.powersetCard i) : A \ B ∈ A.powersetCard j := by
    obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hB
    refine mem_powersetCard.mpr ⟨sdiff_subset, ?_⟩
    rw [card_sdiff_of_subset hsub, hij, hcard]
    omega
  have hrev : A.card = k₂ + k₁ := hA.trans (Nat.add_comm _ _)
  have hinv {i : ℕ} {B : Finset α} (hB : B ∈ A.powersetCard i) :
      A \ (A \ B) = B := Finset.sdiff_sdiff_eq_self (mem_powersetCard.mp hB).1
  unfold sliceProbability
  congr 1
  · congr 1
    refine card_bij' (fun B _ ↦ A \ B) (fun B _ ↦ A \ B) ?_ ?_ ?_ ?_
    · intro B hB
      obtain ⟨hb, he⟩ := mem_filter.mp hB
      exact mem_filter.mpr ⟨hmem hA hb, he⟩
    · intro B hB
      obtain ⟨hb, he⟩ := mem_filter.mp hB
      exact mem_filter.mpr ⟨hmem hrev hb, by rwa [hinv hb]⟩
    · intro B hB
      exact hinv (mem_filter.mp hB).1
    · intro B hB
      exact hinv (mem_filter.mp hB).1
  · congr 1
    exact card_bij' (fun B _ ↦ A \ B) (fun B _ ↦ A \ B)
      (fun _ ↦ hmem hA) (fun _ ↦ hmem hrev) (fun _ ↦ hinv) (fun _ ↦ hinv)

/-- Exact probability that all the points in a fixed subset appear in a uniform slice. -/
theorem sliceProbability_contains (s C : Finset α) (j : ℕ) (hC : C ⊆ s) (hj : C.card ≤ j) :
    sliceProbability s j (fun B ↦ C ⊆ B) =
      ((s.card - C.card).choose (j - C.card) : ℝ) / (s.card.choose j : ℝ) := by
  unfold sliceProbability
  rw [filter_congr_decidable _ (fun B ↦ C ⊆ B) _,
    card_filter_powersetCard_subset C s j hC hj, card_powersetCard]

end

end Green39.Split

end SplitLaws

/- Source: one-percent-formal/private/PrivateIncidence.lean -/
section PrivateIncidence

/-
# Private incidences in a Green 39 translate cover

The deterministic estimates in section 2 of `overnight-astra/review/one-percent.md`.
The cover equation is `A + T = Finset.univ`, as in `Green39.proportionCoverable`.
-/

open scoped BigOperators Pointwise

namespace Green39

variable {p : ℕ}

/-- The incidence of label `a` at center `t` is also covered at another center of `T`. -/
def NonprivateAt (A T : Finset (ZMod p)) (a t : ZMod p) : Prop :=
  ∃ b ∈ A, ∃ u ∈ T, u ≠ t ∧ b + u = a + t

/-- Labels in `L` that are nonprivate at `t` relative to the full sets `A` and `T`. -/
noncomputable def nonprivateLabels (A T L : Finset (ZMod p)) (t : ZMod p) :
    Finset (ZMod p) := by
  classical
  exact L.filter (fun a => NonprivateAt A T a t)

@[simp] theorem mem_nonprivateLabels {A T L : Finset (ZMod p)} {a t : ZMod p} :
    a ∈ nonprivateLabels A T L t ↔ a ∈ L ∧ NonprivateAt A T a t := by
  classical
  simp [nonprivateLabels]

private theorem card_filter_product {α β : Type*} (L : Finset α) (C : Finset β)
    (P : α → β → Prop) [DecidableRel P] :
    ((L ×ˢ C).filter fun i => P i.1 i.2).card =
      ∑ a ∈ L, (C.filter fun t => P a t).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]

theorem card_group_le_card_mul [NeZero p] {A T : Finset (ZMod p)}
    (hcover : A + T = Finset.univ) : p ≤ A.card * T.card := by
  calc
    p = (A + T).card := by simp [hcover, ZMod.card]
    _ ≤ A.card * T.card := Finset.card_add_le

/-- A point with multiplicity `m` contributes either zero or at most `2 * (m - 1)`
nonprivate incidences. Sum this estimate over the covered group. -/
theorem total_nonprivate_incidence_le [NeZero p] {A T : Finset (ZMod p)}
    (hcover : A + T = Finset.univ) :
    (∑ t ∈ T, (nonprivateLabels A T A t).card) ≤ 2 * (A.card * T.card - p) := by
  classical
  let point : ZMod p × ZMod p → ZMod p := fun i => i.2 + i.1
  let I := T ×ˢ A
  let J := I.filter (fun i => NonprivateAt A T i.2 i.1)
  let m := fun x => (I.filter (fun i => point i = x)).card
  let n := fun x => (J.filter (fun i => point i = x)).card
  have hJ : J.card = ∑ t ∈ T, (nonprivateLabels A T A t).card :=
    card_filter_product T A (fun t a => NonprivateAt A T a t)
  have hm : I.card = ∑ x, m x :=
    Finset.card_eq_sum_card_fiberwise (f := point) (fun _ _ => Finset.mem_univ _)
  have hn : J.card = ∑ x, n x :=
    Finset.card_eq_sum_card_fiberwise (f := point) (fun _ _ => Finset.mem_univ _)
  have hpoint : ∀ x, n x + 2 ≤ 2 * m x := by
    intro x
    have hpos : 0 < m x := by
      have hx : x ∈ A + T := by
        rw [hcover]
        exact Finset.mem_univ x
      obtain ⟨a, ha, t, ht, hat⟩ := Finset.mem_add.mp hx
      exact Finset.card_pos.mpr
        ⟨(t, a), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ht, ha⟩, hat⟩⟩
    have hle : n x ≤ m x := by
      apply Finset.card_le_card
      intro i hi
      obtain ⟨hj, hix⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1, hix⟩
    by_cases hmultiple : 1 < m x
    · omega
    · have hzero : n x = 0 := by
        by_contra hne
        obtain ⟨⟨t, a⟩, hi⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
        obtain ⟨hj, hax⟩ := Finset.mem_filter.mp hi
        obtain ⟨hat, hb⟩ := Finset.mem_filter.mp hj
        obtain ⟨b, hbA, u, huT, hut, hbu⟩ := hb
        have htwo : 1 < m x :=
          Finset.one_lt_card.mpr ⟨(u, b),
            Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨huT, hbA⟩, hbu.trans hax⟩,
            (t, a), Finset.mem_filter.mpr ⟨hat, hax⟩,
            fun h => hut (congrArg Prod.fst h)⟩
        exact hmultiple htwo
      omega
  have hsum : (∑ x, (n x + 2)) ≤ ∑ x, 2 * m x :=
    Finset.sum_le_sum (fun x _ => hpoint x)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hn, ← hm] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ZMod.card,
    I, Finset.card_product] at hsum
  change J.card + p * 2 ≤ 2 * (T.card * A.card) at hsum
  rw [← hJ]
  rw [Nat.mul_comm T.card A.card] at hsum
  have hcovered := card_group_le_card_mul hcover
  omega

private theorem total_nonprivate_incidence_le_real [NeZero p] {A T : Finset (ZMod p)}
    (hcover : A + T = Finset.univ) :
    ((∑ t ∈ T, (nonprivateLabels A T A t).card : ℕ) : ℝ) ≤
      2 * ((A.card : ℝ) * T.card - p) := by
  have htotal : ((∑ t ∈ T, (nonprivateLabels A T A t).card : ℕ) : ℝ) ≤
      ((2 * (A.card * T.card - p) : ℕ) : ℝ) := by
    exact_mod_cast total_nonprivate_incidence_le hcover
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (card_group_le_card_mul hcover)]
    using htotal

/-- Centers of `T` with at most `threshold` nonprivate labels in the full set `A`. -/
noncomputable def nearPrivateCenters (A T : Finset (ZMod p)) (threshold : ℝ) :
    Finset (ZMod p) := by
  classical
  exact T.filter (fun t => ((nonprivateLabels A T A t).card : ℝ) ≤ threshold)

@[simp] theorem mem_nearPrivateCenters {A T : Finset (ZMod p)} {t : ZMod p} {threshold : ℝ} :
    t ∈ nearPrivateCenters A T threshold ↔
      t ∈ T ∧ ((nonprivateLabels A T A t).card : ℝ) ≤ threshold := by
  classical
  simp [nearPrivateCenters]

/-- Averaging bounds the number of centers above the nonprivate-label threshold. -/
theorem card_nearPrivateCenters_ge [NeZero p] {A T : Finset (ZMod p)}
    (hcover : A + T = Finset.univ) {threshold : ℝ} (hthreshold : 0 < threshold) :
    (T.card : ℝ) - 2 * ((A.card : ℝ) * T.card - p) / threshold ≤
      (nearPrivateCenters A T threshold).card := by
  classical
  let good := nearPrivateCenters A T threshold
  let bad := T \ good
  have hgood : good ⊆ T := Finset.filter_subset _ _
  have hcount : (bad.card : ℝ) + good.card = T.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hgood
  have hsum : (bad.card : ℝ) * threshold ≤
      ((∑ t ∈ T, (nonprivateLabels A T A t).card : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
    calc
      (bad.card : ℝ) * threshold = ∑ _t ∈ bad, threshold := by simp
      _ ≤ ∑ t ∈ bad, ((nonprivateLabels A T A t).card : ℝ) := by
        apply Finset.sum_le_sum
        intro t ht
        obtain ⟨htT, hn⟩ := Finset.mem_sdiff.mp ht
        apply le_of_lt
        apply lt_of_not_ge
        intro h
        exact hn (mem_nearPrivateCenters.mpr ⟨htT, h⟩)
      _ ≤ ∑ t ∈ T, ((nonprivateLabels A T A t).card : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun _ _ _ => Nat.cast_nonneg _)
  have hbad := (le_div_iff₀ hthreshold).mpr (hsum.trans (total_nonprivate_incidence_le_real hcover))
  linarith

/-- For a one-percent cover, at most `0.02 * p` incidences are nonprivate. -/
theorem total_nonprivate_incidence_onePercent [NeZero p] {A T : Finset (ZMod p)}
    (hcover : A + T = Finset.univ) (hk : 0 < A.card)
    (hsmall : (T.card : ℝ) ≤ 1.01 * p / A.card) :
    ((∑ t ∈ T, (nonprivateLabels A T A t).card : ℕ) : ℝ) ≤ 0.02 * p := by
  have hk' : (0 : ℝ) < A.card := by exact_mod_cast hk
  have hsmall' := (le_div_iff₀ hk').mp hsmall
  nlinarith only [hsmall', total_nonprivate_incidence_le_real hcover]

/-- The section 2 bounds for the number of centers with at most `0.0225 * |A|`
nonprivate labels. The square bound applies in particular to `|A| = Nat.sqrt p`. -/
theorem card_nearPrivateCenters_onePercent [NeZero p] {A T : Finset (ZMod p)}
    (hcover : A + T = Finset.univ) (hk : 0 < A.card) (hsquare : A.card ^ 2 ≤ p)
    (hsmall : (T.card : ℝ) ≤ 1.01 * p / A.card) :
    let good := nearPrivateCenters A T (0.0225 * A.card)
    (T.card : ℝ) - 0.02 * p / (0.0225 * A.card) ≤ good.card ∧
      (p : ℝ) / (9 * A.card) ≤ (T.card : ℝ) - 0.02 * p / (0.0225 * A.card) ∧
      (A.card : ℝ) / 9 ≤ (p : ℝ) / (9 * A.card) := by
  have hk' : (0 : ℝ) < A.card := by exact_mod_cast hk
  have hthreshold : (0 : ℝ) < 0.0225 * A.card := by positivity
  have hsmall' := (le_div_iff₀ hk').mp hsmall
  have hcover' : (p : ℝ) ≤ (T.card : ℝ) * A.card := by
    rw [mul_comm]
    exact_mod_cast card_group_le_card_mul hcover
  have hsquare' : (A.card : ℝ) ^ 2 ≤ p := by exact_mod_cast hsquare
  refine ⟨?_, ?_, ?_⟩
  · calc
      (T.card : ℝ) - 0.02 * p / (0.0225 * A.card) ≤
          (T.card : ℝ) - 2 * ((A.card : ℝ) * T.card - p) / (0.0225 * A.card) := by
        apply sub_le_sub_left
        apply (div_le_div_iff_of_pos_right hthreshold).mpr
        nlinarith only [hsmall']
      _ ≤ _ := card_nearPrivateCenters_ge hcover hthreshold
  · have hlow : (p : ℝ) / A.card ≤ T.card := (div_le_iff₀ hk').mpr hcover'
    have heq : (p : ℝ) / (9 * A.card) + 0.02 * p / (0.0225 * A.card) = p / A.card := by
      field_simp
      ring
    linarith only [hlow, heq]
  · rw [le_div_iff₀ (by positivity : (0 : ℝ) < 9 * A.card)]
    nlinarith only [hsquare']

/-- Private incidences in `A₁ × R` give distinct points of `A₁ + R`. -/
theorem card_add_ge_of_nonprivate_bound {A T A₁ R : Finset (ZMod p)}
    (hA₁ : A₁ ⊆ A) (hR : R ⊆ T) {bound : ℝ}
    (hbound : ∀ t ∈ R, ((nonprivateLabels A T A₁ t).card : ℝ) ≤ bound) :
    ((A₁.card : ℝ) - bound) * R.card ≤ (A₁ + R).card := by
  classical
  let I := (R ×ˢ A₁).filter (fun i => i.2 ∉ nonprivateLabels A T A₁ i.1)
  have hinj : I.card ≤ (A₁ + R).card := by
    apply Finset.card_le_card_of_injOn (fun i => i.2 + i.1)
    · intro i hi
      obtain ⟨hr, ha⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hi).1
      exact Finset.add_mem_add ha hr
    · rintro ⟨t, a⟩ ht ⟨u, b⟩ hu heq
      obtain ⟨ht', hpriv⟩ := Finset.mem_filter.mp ht
      obtain ⟨_, ha⟩ := Finset.mem_product.mp ht'
      obtain ⟨hu', hb⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hu).1
      have hut : u = t := by
        by_contra hne
        exact hpriv (mem_nonprivateLabels.mpr ⟨ha, b, hA₁ hb, u, hR hu', hne, heq.symm⟩)
      subst u
      have hab : a = b := add_right_cancel heq
      subst b
      rfl
  have hcard : I.card = ∑ t ∈ R, (A₁ \ nonprivateLabels A T A₁ t).card := by
    calc
      I.card = ∑ t ∈ R, (A₁.filter (fun a => a ∉ nonprivateLabels A T A₁ t)).card :=
        card_filter_product R A₁ (fun t a => a ∉ nonprivateLabels A T A₁ t)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro t _
        congr 1
        ext a
        simp only [Finset.mem_filter, Finset.mem_sdiff]
  have hinj' : (I.card : ℝ) ≤ (A₁ + R).card := by exact_mod_cast hinj
  rw [hcard, Nat.cast_sum] at hinj'
  refine le_trans ?_ hinj'
  rw [mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_le_sum
  intro t ht
  rw [Finset.cast_card_sdiff (s := nonprivateLabels A T A₁ t) (t := A₁)
    (fun _ ha => (mem_nonprivateLabels.mp ha).1)]
  exact sub_le_sub_left (hbound t ht) _

/-- For disjoint label sets, every hit of `A₁ + R` by an `A₂` label at an `S` center
is a nonprivate incidence. The two sets of centers can overlap. -/
theorem sum_translate_inter_card_le_of_nonprivate_bound {A T A₁ A₂ R S : Finset (ZMod p)}
    (hA₁ : A₁ ⊆ A) (hdisjoint : Disjoint A₁ A₂) (hR : R ⊆ T) {bound : ℝ}
    (hbound : ∀ t ∈ S, ((nonprivateLabels A T A₂ t).card : ℝ) ≤ bound) :
    ((∑ z ∈ A₂, ((({z} : Finset (ZMod p)) + S) ∩ (A₁ + R)).card : ℕ) : ℝ) ≤
      bound * S.card := by
  classical
  let U := A₁ + R
  have hslice (z : ZMod p) : ((({z} : Finset (ZMod p)) + S) ∩ U).card =
      (S.filter (fun t => z + t ∈ U)).card := by
    have himage : (S.filter (fun t => z + t ∈ U)).image (fun t => z + t) =
        (({z} : Finset (ZMod p)) + S) ∩ U := by
      ext x
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_inter, Finset.mem_add,
        Finset.mem_singleton]
      constructor
      · rintro ⟨t, ⟨ht, hU⟩, rfl⟩
        exact ⟨⟨z, rfl, t, ht, rfl⟩, hU⟩
      · rintro ⟨⟨a, rfl, t, ht, rfl⟩, hU⟩
        exact ⟨t, ⟨ht, hU⟩, rfl⟩
    rw [← himage, Finset.card_image_of_injective _ (add_right_injective z)]
  have hswap : (∑ z ∈ A₂, (S.filter (fun t => z + t ∈ U)).card) =
      ∑ t ∈ S, (A₂.filter (fun z => z + t ∈ U)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
  change ((∑ z ∈ A₂, ((({z} : Finset (ZMod p)) + S) ∩ U).card : ℕ) : ℝ) ≤
    bound * S.card
  simp_rw [hslice]
  rw [hswap, Nat.cast_sum, mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_le_sum
  intro t ht
  refine le_trans ?_ (hbound t ht)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro z hz
  obtain ⟨hzA₂, hzU⟩ := Finset.mem_filter.mp hz
  obtain ⟨a, ha, u, hu, hau⟩ := Finset.mem_add.mp hzU
  have hut : u ≠ t := by
    intro heq
    subst u
    have haz : a = z := add_right_cancel hau
    exact Finset.disjoint_left.mp hdisjoint (haz ▸ ha) hzA₂
  exact mem_nonprivateLabels.mpr ⟨hzA₂, a, hA₁ ha, u, hR hu, hut, hau⟩

/-- Both inequalities (3) for a given balanced split. The per-half bound is `0.0114 * |A|`.
The hypotheses on `R` and `S` are independent. -/
theorem balanced_halves_bounds {A T A₁ A₂ R S : Finset (ZMod p)}
    (hsplit : A₁ ∪ A₂ = A) (hdisjoint : Disjoint A₁ A₂)
    (hbalance : A₁.card = A.card / 2) (hR : R ⊆ T) (_hS : S ⊆ T)
    (hR₁ : ∀ t ∈ R, ((nonprivateLabels A T A₁ t).card : ℝ) ≤ 0.0114 * A.card)
    (hS₂ : ∀ t ∈ S, ((nonprivateLabels A T A₂ t).card : ℝ) ≤ 0.0114 * A.card) :
    let U := A₁ + R
    (((A.card / 2 : ℕ) : ℝ) - 0.0114 * A.card) * R.card ≤ U.card ∧
      ((∑ z ∈ A₂, ((({z} : Finset (ZMod p)) + S) ∩ U).card : ℕ) : ℝ) ≤
        0.0114 * A.card * S.card := by
  have hA₁ : A₁ ⊆ A := by
    rw [← hsplit]
    exact Finset.subset_union_left
  refine ⟨?_, sum_translate_inter_card_le_of_nonprivate_bound hA₁ hdisjoint hR hS₂⟩
  rw [← hbalance]
  exact card_add_ge_of_nonprivate_bound hA₁ hR hR₁

end Green39

end PrivateIncidence

/- Source: one-percent-formal/split/PrivateBalance.lean -/
section PrivateBalance

/-
# The balanced split for the canonical cover (§2)

The cover is selected on the union fiber. On this fiber the nonprivate labels
at any one center form a fixed subset of the population.
-/

open Finset
open scoped BigOperators Classical Pointwise


namespace Green39.Split

open Concentration

noncomputable section

variable {α : Type*} [DecidableEq α]

/-- Mean of the number of marked points in a uniform slice. -/
theorem sliceMean_card_inter (s D : Finset α) {j : ℕ} (hj : j ≤ s.card) (hD : D ⊆ s) :
    sliceMean s j (fun B ↦ ((B ∩ D).card : ℝ)) = (j : ℝ) / s.card * D.card := by
  classical
  by_cases hj0 : j = 0
  · simp [hj0, sliceMean, mean, powersetCard_zero]
  let S := s.powersetCard j
  have hpoint (x : α) (hx : x ∈ D) :
      sliceProbability s j (fun B ↦ x ∈ B) = (j : ℝ) / s.card := by
    have hE : (fun B : Finset α ↦ x ∈ B) = (fun B ↦ {x} ⊆ B) :=
      funext fun B ↦ propext (by rw [singleton_subset_iff])
    rw [hE, sliceProbability_contains s {x} j (singleton_subset_iff.mpr (hD hx))
      (by simpa only [card_singleton] using (show 1 ≤ j by omega)), card_singleton]
    have hs : (0 : ℝ) < s.card := by exact_mod_cast card_pos.mpr ⟨x, hD hx⟩
    have hc : (0 : ℝ) < s.card.choose j := by exact_mod_cast Nat.choose_pos hj
    have h := Nat.choose_mul (n := s.card) (k := j) (s := 1) (Nat.pos_of_ne_zero hj0)
    simp only [Nat.choose_one_right] at h
    have h' : (s.card.choose j : ℝ) * j = (s.card : ℝ) * (s.card - 1).choose (j - 1) := by
      exact_mod_cast h
    apply (div_eq_div_iff hc.ne' hs.ne').mpr
    linarith only [h']
  have hcount (B : Finset α) : ((B ∩ D).card : ℝ) = ∑ x ∈ D, if x ∈ B then 1 else 0 := by
    rw [← sum_filter]
    have h : (D.filter fun x ↦ x ∈ B) = B ∩ D := by
      ext x
      simp [and_comm]
    rw [h]
    simp
  have hin (x : α) :
      (∑ B ∈ S, if x ∈ B then (1 : ℝ) else 0) / S.card =
        sliceProbability s j (fun B ↦ x ∈ B) := by
    rw [← sum_filter]
    unfold sliceProbability
    simp only [sum_const, nsmul_eq_mul, mul_one]
    congr 2
    apply congrArg Finset.card
    ext B
    simp only [mem_filter, S]
  change (∑ B ∈ S, ((B ∩ D).card : ℝ)) / S.card = _
  rw [sum_congr rfl (fun B _ ↦ hcount B), sum_comm, sum_div]
  calc
    _ = ∑ x ∈ D, sliceProbability s j (fun B ↦ x ∈ B) :=
      sum_congr rfl (fun x _ ↦ hin x)
    _ = ∑ _x ∈ D, (j : ℝ) / s.card := sum_congr rfl hpoint
    _ = _ := by simp [mul_comm]

/-- Exchanging one point changes the number of marked points by at most one. -/
theorem exchangeLipschitz_card_inter (s D : Finset α) (j : ℕ) :
    ExchangeLipschitz s j (fun B ↦ ((B ∩ D).card : ℝ)) 1 := by
  intro B hB C hC hd
  have hswap : (C \ B).card ≤ 1 :=
    (card_sdiff_comm ((mem_powersetCard.mp hC).2.trans (mem_powersetCard.mp hB).2.symm)).le.trans hd
  have hstep (U V : Finset α) (hUV : (U \ V).card ≤ 1) :
      ((U ∩ D).card : ℝ) ≤ (V ∩ D).card + 1 := by
    have hsub : (U ∩ D) \ (V ∩ D) ⊆ U \ V := by
      intro x hx
      simp only [mem_sdiff, mem_inter] at hx ⊢
      tauto
    have hdiff := (card_le_card hsub).trans hUV
    have hinter : ((U ∩ D) ∩ (V ∩ D)).card ≤ (V ∩ D).card := card_le_card inter_subset_right
    have hadd := card_sdiff_add_card_inter (U ∩ D) (V ∩ D)
    exact_mod_cast (show (U ∩ D).card ≤ (V ∩ D).card + 1 by omega)
  exact abs_le.mpr ⟨by linarith only [hstep C B hswap], by linarith only [hstep B C hd]⟩

variable {p : ℕ}

/-- All covers eligible for the one-percent cover budget. -/
def smallCovers [NeZero p] (A : Finset (ZMod p)) : Finset (Finset (ZMod p)) :=
  (univ : Finset (ZMod p)).powerset.filter fun T ↦
    A + T = univ ∧ (T.card : ℝ) ≤ 1.01 * p / A.card

/-- Compare covers lexicographically by their sorted lists of representatives. -/
def coverKey (T : Finset (ZMod p)) : List ℕ :=
  (T.image ZMod.val).sort

theorem coverKey_injective [NeZero p] : Function.Injective (coverKey (p := p)) := by
  intro T U h
  have hi : T.image ZMod.val = U.image ZMod.val := by
    simpa only [coverKey, sort_toFinset] using congrArg List.toFinset h
  ext t
  exact ⟨fun ht ↦ by
    obtain ⟨u, hu, hval⟩ := mem_image.mp (hi ▸ mem_image_of_mem ZMod.val ht)
    rwa [ZMod.val_injective p hval] at hu, fun hu ↦ by
    obtain ⟨v, hv, hval⟩ := mem_image.mp (hi.symm ▸ mem_image_of_mem ZMod.val hu)
    rwa [ZMod.val_injective p hval] at hv⟩

/-- The first eligible cover in lexicographic order, and the empty set when none exists. -/
def canonicalCover [NeZero p] (A : Finset (ZMod p)) : Finset (ZMod p) :=
  if h : (smallCovers A).Nonempty then (exists_min_image (smallCovers A) coverKey h).choose
  else ∅

theorem canonicalCover_spec [NeZero p] {A : Finset (ZMod p)} (h : (smallCovers A).Nonempty) :
    canonicalCover A ∈ smallCovers A ∧
      ∀ T ∈ smallCovers A, coverKey (canonicalCover A) ≤ coverKey T := by
  unfold canonicalCover
  rw [dif_pos h]
  exact (exists_min_image (smallCovers A) coverKey h).choose_spec

theorem canonicalCover_nearPrivate_card [NeZero p] {A : Finset (ZMod p)}
    (hcover : (smallCovers A).Nonempty) (hk : 0 < A.card) (hsquare : A.card ^ 2 ≤ p) :
    (A.card : ℝ) / 9 ≤ (nearPrivateCenters A (canonicalCover A) (0.0225 * A.card)).card := by
  obtain ⟨hcov, hbudget⟩ := (mem_filter.mp (canonicalCover_spec hcover).1).2
  obtain ⟨h₁, h₂, h₃⟩ := card_nearPrivateCenters_onePercent hcov hk hsquare hbudget
  exact h₃.trans (h₂.trans h₁)

/-- Failure is a strict exceedance at a near-private center in either half. -/
def BalanceFailure (A T A₁ A₂ : Finset (ZMod p)) : Prop :=
  ∃ t ∈ nearPrivateCenters A T (0.0225 * A.card),
    (0.0114 : ℝ) * A.card < (nonprivateLabels A T A₁ t).card ∨
    (0.0114 : ℝ) * A.card < (nonprivateLabels A T A₂ t).card

/-- On a balanced split, any two sets of near-private centers satisfy both bounds in (3). -/
theorem balanced_halves_bounds_of_nearPrivate {A T A₁ A₂ R S : Finset (ZMod p)}
    (hsplit : A₁ ∪ A₂ = A) (hdisjoint : Disjoint A₁ A₂) (hhalf : A₁.card = A.card / 2)
    (hR : R ⊆ nearPrivateCenters A T (0.0225 * A.card))
    (hS : S ⊆ nearPrivateCenters A T (0.0225 * A.card))
    (hbalanced : ¬ BalanceFailure A T A₁ A₂) :
    let U := A₁ + R
    (((A.card / 2 : ℕ) : ℝ) - 0.0114 * A.card) * R.card ≤ U.card ∧
      ((∑ z ∈ A₂, ((({z} : Finset (ZMod p)) + S) ∩ U).card : ℕ) : ℝ) ≤
        0.0114 * (A.card : ℝ) * S.card := by
  apply Green39.balanced_halves_bounds hsplit hdisjoint hhalf
    (fun _ ht ↦ (mem_nearPrivateCenters.mp (hR ht)).1)
    (fun _ ht ↦ (mem_nearPrivateCenters.mp (hS ht)).1)
  · exact fun t ht ↦ le_of_not_gt (fun h ↦ hbalanced ⟨t, hR ht, Or.inl h⟩)
  · exact fun t ht ↦ le_of_not_gt (fun h ↦ hbalanced ⟨t, hS ht, Or.inr h⟩)

private theorem nonprivateLabels_eq_inter {A T B : Finset (ZMod p)} (hB : B ⊆ A) (t : ZMod p) :
    nonprivateLabels A T B t = B ∩ nonprivateLabels A T A t := by
  ext a
  simp only [mem_nonprivateLabels, mem_inter]
  exact ⟨fun ⟨ha, h⟩ ↦ ⟨ha, hB ha, h⟩, fun ⟨ha, _, h⟩ ↦ ⟨ha, h⟩⟩

private theorem sliceProbability_center_failure (A T : Finset (ZMod p)) (t : ZMod p)
    {j : ℕ} (hj0 : 0 < j) (hj : j ≤ A.card) (hjhalf : 2 * j ≤ A.card + 1) (hk : 225 ≤ A.card)
    (ht : t ∈ nearPrivateCenters A T (0.0225 * A.card)) :
    sliceProbability A j
        (fun B ↦ (0.0114 : ℝ) * A.card < (nonprivateLabels A T B t).card) ≤
      Real.exp (-(A.card : ℝ) / 200000000) := by
  let D := nonprivateLabels A T A t
  have hD : D ⊆ A := fun _ hx ↦ (mem_nonprivateLabels.mp hx).1
  have hsmall : (D.card : ℝ) ≤ 0.0225 * A.card := (mem_nearPrivateCenters.mp ht).2
  have hpos : (0 : ℝ) < A.card := by exact_mod_cast (show 0 < A.card by omega)
  let f : Finset (ZMod p) → ℝ := fun B ↦ (B ∩ D).card
  have hjhalf' : 2 * (j : ℝ) ≤ (A.card : ℝ) + 1 := by exact_mod_cast hjhalf
  have hμ : sliceMean A j f ≤ 0.01125 * ((A.card : ℝ) + 1) := by
    rw [sliceMean_card_inter A D hj hD]
    calc
      _ ≤ ((j : ℝ) / A.card) * (0.0225 * A.card) :=
        mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = 0.0225 * j := by field_simp
      _ ≤ _ := by linarith only [hjhalf']
  have hk' : (225 : ℝ) ≤ A.card := by exact_mod_cast hk
  let u : ℝ := (A.card : ℝ) / 10000
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hevent : sliceProbability A j
        (fun B ↦ (0.0114 : ℝ) * A.card < (nonprivateLabels A T B t).card) ≤
      sliceProbability A j (fun B ↦ u ≤ f B - sliceMean A j f) := by
    simp only [sliceProbability_eq_probability]
    apply probability_mono
    intro B hB h
    rw [nonprivateLabels_eq_inter (mem_powersetCard.mp hB).1] at h
    change (0.0114 : ℝ) * A.card < f B at h
    dsimp [u]
    linarith only [h, hμ, hk']
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj0
  have hj' : (j : ℝ) ≤ A.card := by exact_mod_cast hj
  refine hevent.trans ((sliceProbability_ge_le hj (exchangeLipschitz_card_inter A D j)
    zero_le_one hu).trans (Real.exp_le_exp.mpr ?_))
  rw [one_pow, mul_one]
  apply (div_le_iff₀ (by positivity : 0 < 2 * (j : ℝ))).mpr
  dsimp [u]
  have hm := mul_le_mul_of_nonneg_left hj' hpos.le
  nlinarith only [hm]

/-- Simultaneous balance at all near-private centers, given the full set and cover. -/
theorem sliceProbability_balance_failure [NeZero p] (A T : Finset (ZMod p)) {k₁ k₂ : ℕ}
    (hA : A.card = k₁ + k₂) (hhalf : k₁ = A.card / 2) (hk : 225 ≤ A.card) :
    sliceProbability A k₁ (fun B ↦ BalanceFailure A T B (A \ B)) ≤
      2 * p * Real.exp (-(A.card : ℝ) / 200000000) := by
  let good := nearPrivateCenters A T (0.0225 * A.card)
  let index := good ×ˢ (univ : Finset Bool)
  let E (w : ZMod p × Bool) (B : Finset (ZMod p)) : Prop :=
    (0.0114 : ℝ) * A.card <
      (nonprivateLabels A T (if w.2 then A \ B else B) w.1).card
  have hE : (fun B ↦ BalanceFailure A T B (A \ B)) = (fun B ↦ ∃ w ∈ index, E w B) := by
    funext B
    apply propext
    constructor
    · rintro ⟨t, ht, h₁ | h₂⟩
      · exact ⟨(t, false), mem_product.mpr ⟨ht, mem_univ _⟩, h₁⟩
      · exact ⟨(t, true), mem_product.mpr ⟨ht, mem_univ _⟩, h₂⟩
    · rintro ⟨⟨t, b⟩, hw, h⟩
      refine ⟨t, (mem_product.mp hw).1, ?_⟩
      cases b
      · exact Or.inl h
      · exact Or.inr h
  have htail (w : ZMod p × Bool) (hw : w ∈ index) :
      sliceProbability A k₁ (E w) ≤ Real.exp (-(A.card : ℝ) / 200000000) := by
    have ht := (mem_product.mp hw).1
    obtain ⟨t, b⟩ := w
    cases b
    · exact sliceProbability_center_failure A T t (by omega) (by omega) (by omega) hk ht
    · change sliceProbability A k₁
          (fun B ↦ (0.0114 : ℝ) * A.card < (nonprivateLabels A T (A \ B) t).card) ≤ _
      rw [sliceProbability_complement A k₁ k₂ hA
        (fun B ↦ (0.0114 : ℝ) * A.card < (nonprivateLabels A T B t).card)]
      exact sliceProbability_center_failure A T t (by omega) (by omega) (by omega) hk ht
  rw [hE]
  calc
    _ ≤ ∑ w ∈ index, sliceProbability A k₁ (E w) := by
      simp only [sliceProbability_eq_probability]
      exact probability_exists_le_sum _ _ _
    _ ≤ ∑ _w ∈ index, Real.exp (-(A.card : ℝ) / 200000000) := sum_le_sum htail
    _ = ((good.card : ℝ) * 2) * Real.exp (-(A.card : ℝ) / 200000000) := by
      simp [index, card_product]
    _ ≤ _ := by
      have hcard : (good.card : ℝ) ≤ p := by
        exact_mod_cast (show good.card ≤ p from by simpa [ZMod.card] using card_le_univ good)
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      linarith only [hcard]

/-- The joint event of cover existence and a failed balance for the canonical cover. -/
def CanonicalBalanceFailure [NeZero p] (q : Finset (ZMod p) × Finset (ZMod p)) : Prop :=
  let A := q.1 ∪ q.2
  (smallCovers A).Nonempty ∧ BalanceFailure A (canonicalCover A) q.1 q.2

/-- Averaging over the full set preserves the simultaneous bound. -/
theorem canonical_balance_failure_bound [NeZero p] {k : ℕ} (hk : 225 ≤ k) :
    probability (orderedPairs (univ : Finset (ZMod p)) (k / 2) (k - k / 2))
        CanonicalBalanceFailure ≤ 2 * p * Real.exp (-(k : ℝ) / 200000000) := by
  rw [probability_eq_mean_union]
  apply mean_le_of_forall_le (by positivity)
  intro A hA
  have hsize : A.card = k / 2 + (k - k / 2) := (mem_powersetCard.mp hA).2
  have hcard : A.card = k := by omega
  have htail := sliceProbability_balance_failure A (canonicalCover A) hsize (by omega) (by omega)
  rw [hcard] at htail
  refine le_trans ?_ htail
  simp only [sliceProbability_eq_probability]
  apply probability_mono
  intro B hB
  unfold CanonicalBalanceFailure
  rw [show B ∪ (A \ B) = A from sup_sdiff_cancel_right (mem_powersetCard.mp hB).1]
  exact And.right

open Filter
open scoped Topology

/-- Joint failure probability in the actual square-root-sized split model. -/
def canonicalBalanceFailureProbability (p : ℕ) : ℝ :=
  if hp : p = 0 then 0
  else
    letI : NeZero p := ⟨hp⟩
    let k := p.sqrt
    probability (orderedPairs (univ : Finset (ZMod p)) (k / 2) (k - k / 2))
      CanonicalBalanceFailure

/-- The joint failure probability tends to zero even along all positive moduli. -/
theorem tendsto_canonical_balance_failure :
    Tendsto canonicalBalanceFailureProbability atTop (𝓝 0) := by
  let C : ℝ := 200000000
  let y (p : ℕ) : ℝ := (p.sqrt : ℝ) / C
  have hroot : Tendsto Nat.sqrt atTop atTop := by
    refine tendsto_atTop.mpr fun k ↦ (eventually_ge_atTop (k ^ 2)).mono ?_
    exact fun _ hp ↦ Nat.le_sqrt'.mpr hp
  have hy : Tendsto y atTop atTop :=
    Tendsto.atTop_div_const (by positivity) (tendsto_natCast_atTop_atTop.comp hroot)
  have hf : Tendsto (fun p : ℕ ↦ y p ^ (2 : ℕ) * Real.exp (-y p)) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hy
  have hc : Tendsto (fun _ : ℕ ↦ 8 * C ^ (2 : ℕ)) atTop (𝓝 (8 * C ^ (2 : ℕ))) :=
    tendsto_const_nhds
  have ht : Tendsto (fun p ↦ (8 * C ^ (2 : ℕ)) * (y p ^ (2 : ℕ) * Real.exp (-y p)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using hc.mul hf
  refine squeeze_zero' (Eventually.of_forall ?_) ?_ ht
  · intro p
    unfold canonicalBalanceFailureProbability
    split
    · rfl
    · unfold probability
      positivity
  · filter_upwards [eventually_ge_atTop (225 ^ 2 : ℕ)] with p hp
    have hk : 225 ≤ p.sqrt := Nat.le_sqrt'.mpr hp
    have hp0 : p ≠ 0 := by omega
    let _ : NeZero p := ⟨hp0⟩
    rw [canonicalBalanceFailureProbability, dif_neg hp0]
    refine (canonical_balance_failure_bound hk).trans ?_
    have hp' : (p : ℝ) ≤ ((p.sqrt : ℝ) + 1) ^ 2 := by
      exact_mod_cast (Nat.lt_succ_sqrt' p).le
    have hroot' : (1 : ℝ) ≤ p.sqrt := by exact_mod_cast (show 1 ≤ p.sqrt by omega)
    have hcoeff : (2 : ℝ) * p ≤ 8 * (p.sqrt : ℝ) ^ 2 := by
      have hsq := pow_le_pow_left₀ (show (0 : ℝ) ≤ (p.sqrt : ℝ) + 1 by positivity)
        (show (p.sqrt : ℝ) + 1 ≤ 2 * p.sqrt by linarith only [hroot']) 2
      nlinarith only [hp', hsq]
    calc
      _ ≤ (8 * (p.sqrt : ℝ) ^ 2) * Real.exp (-(p.sqrt : ℝ) / 200000000) :=
        mul_le_mul_of_nonneg_right hcoeff (Real.exp_nonneg _)
      _ = _ := by
        unfold y C
        rw [neg_div]
        ring

end

end Green39.Split

end PrivateBalance

/- Source: one-percent-formal/sparsify/FourierSparsification.lean -/
section FourierSparsification

/-
# Fourier sparsification for Green 39, Section 5

The empirical character sums are centered at their exact uniform-slice means.
Using exchange constant two and threshold `η * s` in each coordinate gives
total failure probability at most `4 * p * exp (-s * η^2 / 8)`.
-/

open Finset Green39.Concentration
open scoped BigOperators


namespace OnePercent.Fourier

noncomputable section

private theorem sliceMean_sum {α : Type*} [DecidableEq α]
    (F : Finset α) {s : ℕ} (hs : 0 < s) (hsF : s ≤ F.card) (w : α → ℝ) :
    sliceMean F s (fun S ↦ ∑ x ∈ S, w x) = (s : ℝ) / F.card * ∑ x ∈ F, w x := by
  classical
  have hcount (x : α) (hx : x ∈ F) :
      ((F.powersetCard s).filter (fun S ↦ x ∈ S)).card =
        (F.card - 1).choose (s - 1) := by
    simpa only [singleton_subset_iff, card_singleton] using
      card_filter_powersetCard_subset ({x} : Finset α) F s (by simpa using hx) hs
  have hsum :
      (∑ S ∈ F.powersetCard s, ∑ x ∈ S, w x) =
        ((F.card - 1).choose (s - 1) : ℝ) * ∑ x ∈ F, w x := by
    calc
      _ = ∑ S ∈ F.powersetCard s, ∑ x ∈ F, if x ∈ S then w x else 0 := by
        apply sum_congr rfl
        intro S hS
        rw [← sum_filter, filter_mem_eq_inter,
          inter_eq_right.mpr (mem_powersetCard.mp hS).1]
      _ = ∑ x ∈ F, ∑ S ∈ F.powersetCard s, if x ∈ S then w x else 0 := sum_comm
      _ = _ := by
        rw [mul_sum]
        apply sum_congr rfl
        intro x hx
        rw [← sum_filter, sum_const, nsmul_eq_mul, hcount x hx]
  have hchoose : (F.card : ℝ) * ((F.card - 1).choose (s - 1) : ℝ) =
      (s : ℝ) * (F.card.choose s : ℝ) := by
    exact_mod_cast (by simpa [Nat.mul_comm s] using
      (Nat.choose_mul (n := F.card) (k := s) (s := 1) hs).symm)
  have hF : (F.card : ℝ) ≠ 0 := by exact_mod_cast (hs.trans_le hsF).ne'
  have hslice : (F.card.choose s : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hsF).ne'
  rw [sliceMean, mean, hsum, card_powersetCard]
  field_simp
  linear_combination (∑ x ∈ F, w x) * hchoose

private theorem exchangeLipschitz_sum {α : Type*} [DecidableEq α]
    (F : Finset α) (s : ℕ) {w : α → ℝ} (hw : ∀ x, |w x| ≤ 1) :
    ExchangeLipschitz F s (fun S ↦ ∑ x ∈ S, w x) 2 := by
  intro A hA B hB hAB
  have hBA : (B \ A).card ≤ 1 := by
    have h₁ := card_sdiff_add_card_inter A B
    have h₂ := card_sdiff_add_card_inter B A
    rw [inter_comm B A] at h₂
    have hcard := (mem_powersetCard.mp hA).2.trans (mem_powersetCard.mp hB).2.symm
    omega
  have habs (T : Finset α) (hT : T.card ≤ 1) : |∑ x ∈ T, w x| ≤ 1 :=
    (abs_sum_le_sum_abs _ _).trans <| calc
      _ ≤ ∑ _x ∈ T, (1 : ℝ) := sum_le_sum (fun x _ ↦ hw x)
      _ ≤ 1 := by simpa using (show (T.card : ℝ) ≤ 1 by exact_mod_cast hT)
  have hsum (U V : Finset α) :
      (∑ x ∈ U \ V, w x) + (∑ x ∈ U ∩ V, w x) = ∑ x ∈ U, w x := by
    rw [← sum_union (disjoint_sdiff_inter U V), sdiff_union_inter]
  calc
    |(∑ x ∈ A, w x) - ∑ x ∈ B, w x| =
        |(∑ x ∈ A \ B, w x) - ∑ x ∈ B \ A, w x| := by
      rw [← hsum A B, ← hsum B A, inter_comm B A]
      congr 1
      ring
    _ ≤ |∑ x ∈ A \ B, w x| + |∑ x ∈ B \ A, w x| := abs_sub _ _
    _ ≤ 2 := by linarith [habs _ hAB, habs _ hBA]

/-- The finite union bound on a uniform slice, stated for its good event. -/
private theorem one_sub_sum_le_sliceProbability_forall
    {α ι : Type*} [Fintype ι] (F : Finset α) {s : ℕ} (hs : s ≤ F.card)
    (bad : ι → Finset α → Prop) :
    1 - ∑ i, sliceProbability F s (bad i) ≤
      sliceProbability F s (fun S ↦ ∀ i, ¬ bad i S) := by
  classical
  let T := F.powersetCard s
  have ht : 0 < (T.card : ℝ) := by
    exact_mod_cast (by simpa [T, card_powersetCard] using Nat.choose_pos hs : 0 < T.card)
  have hcount : (T.filter (fun S ↦ ¬ ∀ i, ¬ bad i S)).card ≤
      ∑ i, (T.filter (bad i)).card := by
    apply (card_le_card (t := univ.biUnion (fun i : ι ↦ T.filter (bad i))) ?_).trans
      card_biUnion_le
    intro S hS
    obtain ⟨hST, hSbad⟩ := mem_filter.mp hS
    obtain ⟨i, hi⟩ : ∃ i, bad i S := by simpa only [not_forall, not_not] using hSbad
    exact mem_biUnion.mpr ⟨i, mem_univ i, mem_filter.mpr ⟨hST, hi⟩⟩
  have hpartition := T.card_filter_add_card_filter_not (fun S ↦ ∀ i, ¬ bad i S)
  simp only [sliceProbability]
  rw [← sum_div, sub_le_iff_le_add, ← add_div, le_div_iff₀ ht, one_mul, ← Nat.cast_sum,
    ← Nat.cast_add]
  have hgoodFilter :
      @filter _ (fun S ↦ ∀ i, ¬ bad i S) (fun _ ↦ Classical.propDecidable _) T =
        T.filter (fun S ↦ ∀ i, ¬ bad i S) :=
    filter_congr_decidable _ _ _
  rw [hgoodFilter]
  exact Nat.cast_le.mpr (hpartition.ge.trans (Nat.add_le_add_left hcount _))

variable {p : ℕ} [NeZero p]

private def character (a z : ZMod p) : ℂ := ZMod.stdAddChar (-(z * a))

private def coordinate (b : Bool) (z : ℂ) : ℝ := if b then z.re else z.im

private theorem abs_character_coordinate_le_one (a z : ZMod p) (b : Bool) :
    |coordinate b (character a z)| ≤ 1 := by
  have hn : ‖character a z‖ = 1 := by
    simp [character, AddChar.norm_apply]
  cases b
  · exact (Complex.abs_im_le_norm _).trans_eq hn
  · exact (Complex.abs_re_le_norm _).trans_eq hn

private theorem dft_indicator_eq_sum (F : Finset (ZMod p)) (a : ZMod p) :
    ZMod.dft (indicator F) a = ∑ z ∈ F, character a z := by
  simp [ZMod.dft_apply, smul_eq_mul, indicator, character, mul_ite]

private theorem coordinate_dft_indicator (F : Finset (ZMod p)) (a : ZMod p) (b : Bool) :
    coordinate b (ZMod.dft (indicator F) a) = ∑ z ∈ F, coordinate b (character a z) := by
  rw [dft_indicator_eq_sum]
  cases b <;> simp [coordinate, Complex.re_sum, Complex.im_sum]

private theorem coordinate_sub_real_mul (b : Bool) (z w : ℂ) (r : ℝ) :
    coordinate b (z - (r : ℂ) * w) = coordinate b z - r * coordinate b w := by
  cases b <;> simp [coordinate, Complex.mul_re, Complex.mul_im]

private def observable (i : ZMod p × Bool) (S : Finset (ZMod p)) : ℝ :=
  ∑ z ∈ S, coordinate i.2 (character i.1 z)

private def frequencyBad (F : Finset (ZMod p)) (s : ℕ) (η : ℝ)
    (i : ZMod p × Bool) (S : Finset (ZMod p)) : Prop :=
  η * s ≤ |observable i S - sliceMean F s (observable i)|

/-- Uniform sampling without replacement gives the Fourier residual with at least
`1 - 4 * p * exp (-s * η^2 / 8)` probability. -/
theorem sliceProbability_fourierFit_ge (F : Finset (ZMod p)) (μ : ZMod p → ℝ)
    {s : ℕ} {η : ℝ} (hs : 0 < s) (hsF : s ≤ F.card) (hη : 0 ≤ η)
    (hfit : FourierFit F μ (5 * η * F.card)) :
    1 - 4 * (p : ℝ) * Real.exp (-(s : ℝ) * η ^ 2 / 8) ≤
      sliceProbability F s (fun S ↦ FourierFit S μ (7 * η * s)) := by
  classical
  let bad := frequencyBad F s η
  have htail (i : ZMod p × Bool) : sliceProbability F s (bad i) ≤
      2 * Real.exp (-(s : ℝ) * η ^ 2 / 8) := by
    have h := sliceProbability_abs_ge_le hsF
      (exchangeLipschitz_sum F s (abs_character_coordinate_le_one i.1 · i.2))
      (by norm_num : (0 : ℝ) ≤ 2) (mul_nonneg hη (Nat.cast_nonneg s))
    change sliceProbability F s (bad i) ≤ _ at h
    have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
    convert h using 3
    field_simp
    ring
  have hsum : (∑ i, sliceProbability F s (bad i)) ≤
      4 * (p : ℝ) * Real.exp (-(s : ℝ) * η ^ 2 / 8) := by
    calc
      _ ≤ ∑ _i : ZMod p × Bool, 2 * Real.exp (-(s : ℝ) * η ^ 2 / 8) :=
        sum_le_sum (fun i _ ↦ htail i)
      _ = _ := by simp [Fintype.card_prod, ZMod.card, nsmul_eq_mul]; ring
  refine (sub_le_sub_left hsum 1).trans
    ((one_sub_sum_le_sliceProbability_forall F hsF bad).trans ?_)
  unfold sliceProbability
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr (card_le_card ?_)
  intro S hS
  simp only [mem_filter] at hS ⊢
  obtain ⟨hS, hgood⟩ := hS
  obtain ⟨_, hcard⟩ := mem_powersetCard.mp hS
  refine ⟨hS, fun a ↦ ?_⟩
  let r := (s : ℝ) / F.card
  let d := ZMod.dft (indicator S) a - (r : ℂ) * ZMod.dft (indicator F) a
  have hd (b : Bool) : |coordinate b d| ≤ η * s := by
    have h := lt_of_not_ge (hgood (a, b))
    change |observable (a, b) S - sliceMean F s (observable (a, b))| < η * s at h
    rw [show sliceMean F s (observable (a, b)) =
        r * observable (a, b) F from sliceMean_sum F hs hsF _] at h
    simpa only [d, coordinate_sub_real_mul, coordinate_dft_indicator, observable] using h.le
  have hdNorm : ‖d‖ ≤ 2 * η * s := by
    have hre : |d.re| ≤ η * s := hd true
    have him : |d.im| ≤ η * s := hd false
    exact (Complex.norm_le_abs_re_add_abs_im _).trans (by linarith)
  have hFpos : (0 : ℝ) < F.card := by exact_mod_cast hs.trans_le hsF
  have hr : 0 ≤ r := div_nonneg (Nat.cast_nonneg _) hFpos.le
  have hrCard : r * F.card = s := div_mul_cancel₀ _ hFpos.ne'
  have hrCardC : (r : ℂ) * (F.card : ℂ) = s := by exact_mod_cast hrCard
  let m := ZMod.dft (fun z ↦ (μ z : ℂ)) a
  have heq : ZMod.dft (indicator S) a - (S.card : ℂ) * m =
      d + (r : ℂ) * (ZMod.dft (indicator F) a - (F.card : ℂ) * m) := by
    rw [hcard, mul_sub, ← mul_assoc, hrCardC]
    dsimp [d]
    ring
  change ‖ZMod.dft (indicator S) a - (S.card : ℂ) * m‖ ≤ 7 * η * s
  rw [heq]
  calc
    _ ≤ ‖d‖ + ‖(r : ℂ) * (ZMod.dft (indicator F) a - (F.card : ℂ) * m)‖ :=
      norm_add_le _ _
    _ ≤ 2 * η * s + r * (5 * η * F.card) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
      exact add_le_add hdNorm (mul_le_mul_of_nonneg_left (hfit a) hr)
    _ = _ := by rw [show r * (5 * η * F.card) = 5 * η * (r * F.card) by ring, hrCard]; ring

/-- Exact finite sufficient criterion for positive success probability. -/
theorem sparsification_tail_lt_one_iff (p s : ℕ) [NeZero p] (η : ℝ) :
    4 * (p : ℝ) * Real.exp (-(s : ℝ) * η ^ 2 / 8) < 1 ↔
      8 * Real.log (4 * (p : ℝ)) < (s : ℝ) * η ^ 2 := by
  have hp := mul_pos (by norm_num : (0 : ℝ) < 4)
    (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne p)) : (0 : ℝ) < p)
  have heq : 4 * (p : ℝ) * Real.exp (-(s : ℝ) * η ^ 2 / 8) =
      Real.exp (Real.log (4 * (p : ℝ)) + -(s : ℝ) * η ^ 2 / 8) := by
    rw [Real.exp_add, Real.exp_log hp]
  rw [heq, ← Real.exp_zero, Real.exp_lt_exp]
  constructor <;> intro h <;> linarith

/-- Section 5, equation (5). The logarithmic criterion is needed only when
the entire fitted piece cannot be used. -/
theorem exists_fourierFit_sparsify (F : Finset (ZMod p)) (μ : ZMod p → ℝ)
    (sStar : ℕ) {η : ℝ} (hη : 0 ≤ η)
    (hfit : FourierFit F μ (5 * η * F.card))
    (hsize : sStar < F.card → 0 < sStar →
      8 * Real.log (4 * (p : ℝ)) < (sStar : ℝ) * η ^ 2) :
    ∃ S ⊆ F, S.card = min F.card sStar ∧ FourierFit S μ (7 * η * S.card) := by
  classical
  by_cases hF : F.card ≤ sStar
  · refine ⟨F, Subset.rfl, (min_eq_left hF).symm, fun a ↦ (hfit a).trans ?_⟩
    gcongr
    norm_num
  have hlt := lt_of_not_ge hF
  rw [min_eq_right hlt.le]
  by_cases hs : sStar = 0
  · subst sStar
    exact ⟨∅, empty_subset _, card_empty, by simp [FourierFit, dft_indicator_eq_sum]⟩
  have hspos := Nat.pos_of_ne_zero hs
  have ht := (sparsification_tail_lt_one_iff p sStar η).mpr (hsize hlt hspos)
  have hpos := (sub_pos.mpr ht).trans_le
    (sliceProbability_fourierFit_ge F μ hspos hlt.le hη hfit)
  rw [sliceProbability] at hpos
  have hcard := (div_pos_iff_of_pos_right (show (0 : ℝ) < (F.powersetCard sStar).card by
    exact_mod_cast (by simpa [card_powersetCard] using Nat.choose_pos hlt.le :
      0 < (F.powersetCard sStar).card))).mp hpos
  obtain ⟨S, hS⟩ := card_pos.mp (show 0 < ((F.powersetCard sStar).filter
    (fun S ↦ FourierFit S μ (7 * η * sStar))).card by exact_mod_cast hcard)
  obtain ⟨⟨hsub, hsize⟩, hfitS⟩ := (mem_filter.mp hS).imp_left mem_powersetCard.mp
  exact ⟨S, hsub, hsize, hsize.symm ▸ hfitS⟩

/-- The version with the (5η) fit expressed for the uniform probability law on `F`. -/
theorem exists_fourierFit_sparsify_of_uniformLaw (F : Finset (ZMod p)) (μ : ZMod p → ℝ)
    (sStar : ℕ) {η : ℝ} (hF : F.Nonempty) (hη : 0 ≤ η)
    (hfit : ∀ a : ZMod p,
      ‖ZMod.dft (uniformLaw F) a - ZMod.dft (fun z ↦ (μ z : ℂ)) a‖ ≤ 5 * η)
    (hsize : sStar < F.card → 0 < sStar →
      8 * Real.log (4 * (p : ℝ)) < (sStar : ℝ) * η ^ 2) :
    ∃ S ⊆ F, S.card = min F.card sStar ∧ FourierFit S μ (7 * η * S.card) :=
  exists_fourierFit_sparsify F μ sStar hη ((fourierFit_iff_uniformLaw F μ hF _).mpr hfit) hsize

end

end OnePercent.Fourier

end FourierSparsification

/- Source: one-percent-formal/outside/OutsideRestriction.lean -/
section OutsideRestriction

/-
# Finite outside restriction for Green's problem 39

The sample space is `Finset.univ.powersetCard k`, as in
`Green39.proportionCoverable`. The counts below are the numerators of
the two uniform expectations in §1 of `overnight-astra/review/one-percent.md`.
The counting identities apply to every nonzero modulus. When `k > p`,
the sums and the binomial counts vanish.
-/

open scoped Pointwise
open Finset

namespace Green39

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

/-- The points left uncovered by the centers in `P`. -/
def uncovered (A P : Finset G) : Finset G := univ \ (A + P)

/-- The points of the translate by `t` that the centers in `P` leave uncovered. -/
def outsideHits (A P : Finset G) (t : G) : Finset G := (A + {t}) ∩ uncovered A P

private def allowed (P : Finset G) (x : G) : Finset G :=
  univ \ P.image (fun v ↦ x - v)

private theorem mem_uncovered_iff_subset_allowed {A P : Finset G} {x : G} :
    x ∈ uncovered A P ↔ A ⊆ allowed P x := by
  simp only [uncovered, mem_sdiff, mem_univ, true_and, allowed]
  constructor
  · intro hx a ha
    refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
    rintro himage
    obtain ⟨v, hv, rfl⟩ := mem_image.mp himage
    exact hx (mem_add.mpr ⟨x - v, ha, v, hv, sub_add_cancel _ _⟩)
  · intro h hx
    obtain ⟨a, ha, v, hv, rfl⟩ := mem_add.mp hx
    exact (mem_sdiff.mp (h ha)).2 (mem_image.mpr ⟨v, hv, add_sub_cancel_right _ _⟩)

private theorem card_allowed (P : Finset G) (x : G) :
    (allowed P x).card = Fintype.card G - P.card := by
  rw [allowed, card_sdiff_of_subset (subset_univ _), card_univ]
  congr 1
  exact card_image_of_injOn fun _ _ _ _ h ↦ sub_right_inj.mp h

omit [Fintype G] in
private theorem mem_add_singleton_iff_sub_mem {A : Finset G} {t x : G} :
    x ∈ A + {t} ↔ x - t ∈ A := by
  constructor
  · intro hx
    obtain ⟨a, ha, v, hv, rfl⟩ := mem_add.mp hx
    simpa only [mem_singleton.mp hv, add_sub_cancel_right] using ha
  · intro hx
    exact mem_add.mpr ⟨x - t, hx, t, mem_singleton_self _, sub_add_cancel _ _⟩

omit [AddCommGroup G] in
private theorem sum_card_eq_sum_card_filter {ι : Type*} (S : Finset ι)
    (F : ι → Finset G) :
    ∑ a ∈ S, (F a).card = ∑ x ∈ (univ : Finset G), (S.filter (fun a ↦ x ∈ F a)).card := by
  classical
  calc
    _ = ∑ a ∈ S, ∑ x ∈ (univ : Finset G), (if x ∈ F a then (1 : ℕ) else 0) := by
      refine sum_congr rfl fun a _ ↦ ?_
      rw [← sum_filter]
      simp
    _ = ∑ x ∈ (univ : Finset G), ∑ a ∈ S, (if x ∈ F a then (1 : ℕ) else 0) := sum_comm
    _ = _ := by
      refine sum_congr rfl fun x _ ↦ ?_
      rw [← sum_filter]
      simp

private theorem filter_powersetCard_mem {α : Type*} [DecidableEq α]
    (S : Finset α) {x : α} (hx : x ∈ S) (n : ℕ) :
    ((S.powersetCard (n + 1)).filter (fun A ↦ x ∈ A)).card =
      (S.card - 1).choose n := by
  have hfilter : (S.powersetCard (n + 1)).filter (fun A ↦ x ∈ A) =
      ((S.erase x).powersetCard n).image (insert x) := by
    ext A
    simp only [mem_filter, mem_powersetCard, mem_image]
    constructor
    · rintro ⟨⟨hAS, hcard⟩, hAx⟩
      refine ⟨A.erase x, ⟨?_, ?_⟩, insert_erase hAx⟩
      · intro a ha
        exact mem_erase.mpr ⟨(mem_erase.mp ha).1, hAS (mem_erase.mp ha).2⟩
      · rw [card_erase_of_mem hAx, hcard, Nat.add_sub_cancel]
    · rintro ⟨B, ⟨hBS, hcard⟩, rfl⟩
      refine ⟨⟨insert_subset hx (hBS.trans (erase_subset _ _)), ?_⟩, mem_insert_self _ _⟩
      rw [card_insert_of_notMem (fun h ↦ notMem_erase x S (hBS h)), hcard]
  rw [hfilter, card_image_of_injOn, card_powersetCard, card_erase_of_mem hx]
  intro A hA B hB h
  have hAx : x ∉ A := fun ha ↦ notMem_erase x S ((mem_powersetCard.mp hA).1 ha)
  have hBx : x ∉ B := fun hb ↦ notMem_erase x S ((mem_powersetCard.mp hB).1 hb)
  simpa only [erase_insert hAx, erase_insert hBx] using congrArg (fun U ↦ U.erase x) h

/-- Exact sum of uncovered cardinalities over the uniform `k`-subset sample space. -/
theorem sum_card_uncovered {p : ℕ} [NeZero p] (k : ℕ) (P : Finset (ZMod p)) :
    ∑ A ∈ (univ : Finset (ZMod p)).powersetCard k, (uncovered A P).card =
      p * (p - P.card).choose k := by
  rw [sum_card_eq_sum_card_filter]
  have hf (x : ZMod p) :
      (((univ : Finset (ZMod p)).powersetCard k).filter
        (fun A ↦ x ∈ uncovered A P)) = (allowed P x).powersetCard k := by
    ext A
    simp [mem_uncovered_iff_subset_allowed, and_comm]
  simp only [hf, card_powersetCard, card_allowed, ZMod.card, sum_const, card_univ, nsmul_eq_mul,
    Nat.cast_id]

/-- Exact sum of uncovered hits at a fixed outside center over the uniform
`k`-subset sample space. -/
theorem sum_card_outsideHits {p k : ℕ} [NeZero p] (P : Finset (ZMod p)) {t : ZMod p}
    (ht : t ∉ P) (hk : 1 ≤ k) :
    ∑ A ∈ (univ : Finset (ZMod p)).powersetCard k, (outsideHits A P t).card =
      p * (p - 1 - P.card).choose (k - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rw [sum_card_eq_sum_card_filter]
  have hf (x : ZMod p) :
      (((univ : Finset (ZMod p)).powersetCard (n + 1)).filter
        (fun A ↦ x ∈ outsideHits A P t)) =
        ((allowed P x).powersetCard (n + 1)).filter (fun A ↦ x - t ∈ A) := by
    ext A
    simp only [mem_filter, mem_powersetCard, subset_univ, true_and, outsideHits, mem_inter,
      mem_add_singleton_iff_sub_mem, mem_uncovered_iff_subset_allowed]
    exact ⟨fun ⟨hc, ha, hs⟩ ↦ ⟨⟨hs, hc⟩, ha⟩, fun ⟨⟨hs, hc⟩, ha⟩ ↦ ⟨hc, ha, hs⟩⟩
  have hx (x : ZMod p) : x - t ∈ allowed P x := by
    refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
    rintro hm
    obtain ⟨v, hv, he⟩ := mem_image.mp hm
    exact ht (sub_right_inj.mp he ▸ hv)
  simp only [hf, filter_powersetCard_mem _ (hx _), card_allowed, ZMod.card,
    Nat.sub_right_comm p P.card 1, Nat.succ_sub_one, sum_const, card_univ, nsmul_eq_mul, Nat.cast_id]

/-- Regularity bounds the intersection with every left translate of `P`. -/
def OutsideRegular (B P : Finset G) (L : ℕ) : Prop :=
  ∀ v : G, (B ∩ ({v} + P)).card ≤ L

omit [Fintype G] in
private theorem card_translate_inter (B P : Finset G) (t v : G) :
    ((B + {t}) ∩ ({v} + P)).card = (B ∩ ({v - t} + P)).card := by
  have hshift : ({v - t} : Finset G) + P + {t} = {v} + P := by
    calc
      _ = ({v - t} : Finset G) + {t} + P := add_right_comm _ _ _
      _ = _ := by rw [singleton_add_singleton, sub_add_cancel]
  rw [← hshift, ← inter_add_singleton, card_add_singleton]

private theorem card_lost_outsideHits_le {B B' P : Finset G} {L : ℕ}
    (hB : OutsideRegular B P L) (t : G) :
    (outsideHits B P t \ outsideHits B' P t).card ≤
      (B \ B').card + L * (B' \ B).card := by
  let hits (v : G) := (B + {t}) ∩ ({v} + P)
  have hsub : outsideHits B P t \ outsideHits B' P t ⊆
      ((B \ B') + {t}) ∪ (B' \ B).biUnion hits := by
    intro x hx
    obtain ⟨hx, hx'⟩ := mem_sdiff.mp hx
    obtain ⟨hxB, hxH⟩ := mem_inter.mp hx
    by_cases hxB' : x ∈ B' + {t}
    · have hxP : x ∈ B' + P := by
        by_contra hxP
        exact hx' (mem_inter.mpr ⟨hxB', mem_sdiff.mpr ⟨mem_univ _, hxP⟩⟩)
      obtain ⟨v, hvB', a, ha, he⟩ := mem_add.mp hxP
      have hvB : v ∉ B := fun hvB ↦ (mem_sdiff.mp hxH).2 (mem_add.mpr ⟨v, hvB, a, ha, he⟩)
      apply mem_union_right
      exact mem_biUnion.mpr ⟨v, mem_sdiff.mpr ⟨hvB', hvB⟩,
        mem_inter.mpr ⟨hxB, mem_add.mpr ⟨v, mem_singleton_self _, a, ha, he⟩⟩⟩
    · apply mem_union_left
      rw [mem_add_singleton_iff_sub_mem] at hxB hxB' ⊢
      exact mem_sdiff.mpr ⟨hxB, hxB'⟩
  calc
    _ ≤ (((B \ B') + {t}) ∪ (B' \ B).biUnion hits).card := card_le_card hsub
    _ ≤ ((B \ B') + {t}).card + ((B' \ B).biUnion hits).card := card_union_le _ _
    _ ≤ (B \ B').card + ∑ v ∈ B' \ B, (hits v).card := by
      rw [card_add_singleton]
      exact Nat.add_le_add_left card_biUnion_le _
    _ ≤ (B \ B').card + ∑ _v ∈ B' \ B, L :=
      Nat.add_le_add_left (sum_le_sum fun v _ ↦ (card_translate_inter B P t v).le.trans
        (hB (v - t))) _
    _ = _ := by rw [sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm]

/-- On samples of equal size, the absolute difference of the two hit counts is
at most `(1 + L) * (B \ B').card` when both samples are regular. -/
theorem dist_card_outsideHits_le {B B' P : Finset G} {L : ℕ}
    (hsize : B.card = B'.card) (hB : OutsideRegular B P L) (hB' : OutsideRegular B' P L)
    (t : G) :
    Nat.dist (outsideHits B P t).card (outsideHits B' P t).card ≤
      (1 + L) * (B \ B').card := by
  have hd : (B \ B').card = (B' \ B).card := card_sdiff_comm hsize
  have h : (outsideHits B P t \ outsideHits B' P t).card ≤ (1 + L) * (B \ B').card := by
    simpa only [Nat.add_mul, Nat.one_mul, ← hd] using
      (card_lost_outsideHits_le (B' := B') hB t)
  have h' : (outsideHits B' P t \ outsideHits B P t).card ≤ (1 + L) * (B \ B').card := by
    simpa only [Nat.add_mul, Nat.one_mul, ← hd] using
      (card_lost_outsideHits_le (B' := B) hB' t)
  rcases le_total (outsideHits B P t).card (outsideHits B' P t).card with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab]
    exact (le_card_sdiff _ _).trans h'
  · rw [Nat.dist_eq_sub_of_le_right hba]
    exact (le_card_sdiff _ _).trans h

/-- Every uncovered point of a cover is hit by some center in `T \ P`. -/
theorem card_uncovered_le_sum_card_outsideHits (A P T : Finset G)
    (hcover : A + T = univ) :
    (uncovered A P).card ≤ ∑ t ∈ T \ P, (outsideHits A P t).card := by
  have hsub : uncovered A P ⊆ (T \ P).biUnion (outsideHits A P) := by
    intro x hx
    have hxT : x ∈ A + T := hcover ▸ mem_univ x
    obtain ⟨a, ha, t, ht, he⟩ := mem_add.mp hxT
    have htP : t ∉ P := fun htP ↦ (mem_sdiff.mp hx).2 (mem_add.mpr ⟨a, ha, t, htP, he⟩)
    exact mem_biUnion.mpr ⟨t, mem_sdiff.mpr ⟨ht, htP⟩,
      mem_inter.mpr ⟨mem_add.mpr ⟨a, ha, t, mem_singleton_self _, he⟩, hx⟩⟩
  exact (card_le_card hsub).trans card_biUnion_le

/-- A pointwise cap on outside hits bounds how many holes the outside part of
any cover can account for. -/
theorem card_uncovered_le_card_outside_mul (A P T : Finset G)
    (hcover : A + T = univ) (C : ℕ)
    (hcap : ∀ t ∈ T \ P, (outsideHits A P t).card ≤ C) :
    (uncovered A P).card ≤ (T \ P).card * C := by
  calc
    _ ≤ ∑ t ∈ T \ P, (outsideHits A P t).card :=
      card_uncovered_le_sum_card_outsideHits A P T hcover
    _ ≤ ∑ _t ∈ T \ P, C := sum_le_sum hcap
    _ = _ := by rw [sum_const, nsmul_eq_mul, Nat.cast_id]

/-- The two cardinality estimates in §1 force the stated lower bound for the
outside portion of every cover. -/
theorem le_card_outside_of_bounds (A P T : Finset G) (hcover : A + T = univ)
    {k : ℕ} {δ ρ : ℝ} (hk : 0 < k) (hδ : 0 ≤ δ) (hρ : 0 < ρ)
    (hholes : (1 - δ) * (Fintype.card G : ℝ) * ρ ≤ (uncovered A P).card)
    (hhits : ∀ t ∈ T \ P, ((outsideHits A P t).card : ℝ) ≤ (1 + δ) * k * ρ) :
    (1 - δ) / (1 + δ) * (Fintype.card G : ℝ) / k ≤ ((T \ P).card : ℝ) := by
  have hsum : ((uncovered A P).card : ℝ) ≤ ∑ t ∈ T \ P, ((outsideHits A P t).card : ℝ) := by
    rw [← Nat.cast_sum]
    exact Nat.cast_le.mpr (card_uncovered_le_sum_card_outsideHits A P T hcover)
  have hcap : (1 - δ) * (Fintype.card G : ℝ) * ρ ≤
      ((T \ P).card : ℝ) * ((1 + δ) * k * ρ) := by
    calc
      _ ≤ ((uncovered A P).card : ℝ) := hholes
      _ ≤ ∑ t ∈ T \ P, ((outsideHits A P t).card : ℝ) := hsum
      _ ≤ ∑ _t ∈ T \ P, (1 + δ) * k * ρ := sum_le_sum hhits
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  have hden : 0 < (1 + δ) * (k : ℝ) * ρ :=
    mul_pos (mul_pos (add_pos_of_pos_of_nonneg zero_lt_one hδ) (Nat.cast_pos.mpr hk)) hρ
  calc
    _ = ((1 - δ) * (Fintype.card G : ℝ)) / ((1 + δ) * k) := by
      rw [div_mul_eq_mul_div, div_div]
    _ = ((1 - δ) * (Fintype.card G : ℝ) * ρ) / ((1 + δ) * k * ρ) :=
      (mul_div_mul_right _ _ hρ.ne').symm
    _ ≤ _ := (div_le_iff₀ hden).mpr hcap

end Green39

end OutsideRestriction

/- Source: one-percent-formal/terminal/SliceRegularity.lean -/
section SliceRegularity

/-
# Regular samples on a uniform slice

The extension uses the directional difference cardinality, which is symmetric
on the fixed-size slice. The regularity estimate counts actual samples
containing a prescribed set of points.
-/

open Finset
open scoped BigOperators Classical Pointwise

namespace Green39.Terminal

open Concentration

noncomputable section

variable {α ι : Type*}

theorem sliceProbability_nonneg (s : Finset α) (k : ℕ) (E : Finset α → Prop) :
    0 ≤ sliceProbability s k E := by
  unfold sliceProbability
  positivity

theorem sliceProbability_mono {s : Finset α} {k : ℕ} {E F : Finset α → Prop}
    (h : ∀ A ∈ s.powersetCard k, E A → F A) :
    sliceProbability s k E ≤ sliceProbability s k F := by
  unfold sliceProbability
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast (card_le_card (fun A hA ↦
    mem_filter.mpr ⟨(mem_filter.mp hA).1, h A (mem_filter.mp hA).1 (mem_filter.mp hA).2⟩) :
    ((s.powersetCard k).filter E).card ≤ ((s.powersetCard k).filter F).card)

theorem sliceProbability_exists_le (s : Finset α) (k : ℕ)
    (J : Finset ι) (E : ι → Finset α → Prop) :
    sliceProbability s k (fun A ↦ ∃ j ∈ J, E j A) ≤
      ∑ j ∈ J, sliceProbability s k (E j) := by
  let S := s.powersetCard k
  have heq : (S.filter fun A ↦ ∃ j ∈ J, E j A) = J.biUnion (fun j ↦ S.filter (E j)) := by
    ext A
    simp only [mem_filter, mem_biUnion]
    exact ⟨fun ⟨hA, j, hj, he⟩ ↦ ⟨j, hj, hA, he⟩,
      fun ⟨j, hj, hA, he⟩ ↦ ⟨hA, j, hj, he⟩⟩
  simp only [sliceProbability, ← sum_div, ← Nat.cast_sum]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have h := (card_le_card heq.le).trans card_biUnion_le
  dsimp only [S] at h
  exact Nat.cast_le.mpr (by convert h using 2 <;> first | rfl | ext A; simp only [mem_filter])

theorem sliceProbability_or_le (s : Finset α) (k : ℕ) (E F : Finset α → Prop) :
    sliceProbability s k (fun A ↦ E A ∨ F A) ≤
      sliceProbability s k E + sliceProbability s k F := by
  let S := s.powersetCard k
  have heq : (S.filter fun A ↦ E A ∨ F A) = S.filter E ∪ S.filter F := by
    ext A
    simp only [mem_filter, mem_union, and_or_left]
  simp only [sliceProbability, ← add_div, ← Nat.cast_add]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have h := (card_le_card heq.le).trans (card_union_le _ _)
  dsimp only [S] at h
  exact Nat.cast_le.mpr (by convert h using 2 <;> first | rfl | ext A; simp only [mem_filter])

theorem sliceProbability_add_compl (s : Finset α) {k : ℕ} (hk : k ≤ s.card)
    (E : Finset α → Prop) :
    sliceProbability s k E + sliceProbability s k (fun A ↦ ¬ E A) = 1 := by
  have hpos : 0 < ((s.powersetCard k).card : ℝ) := by
    exact_mod_cast (powersetCard_nonempty.mpr hk).card_pos
  rw [sliceProbability, sliceProbability, ← add_div, ← Nat.cast_add,
    card_filter_add_card_filter_not, div_self hpos.ne']

section Extension

variable [DecidableEq α]

private theorem card_sdiff_triangle (A B C : Finset α) :
    (A \ C).card ≤ (A \ B).card + (B \ C).card := by
  refine (card_le_card (t := (A \ B) ∪ (B \ C)) ?_).trans (card_union_le _ _)
  intro a ha
  obtain ⟨haA, haC⟩ := mem_sdiff.mp ha
  by_cases haB : a ∈ B
  · exact mem_union_right _ (mem_sdiff.mpr ⟨haB, haC⟩)
  · exact mem_union_left _ (mem_sdiff.mpr ⟨haA, haB⟩)

/-- A clipped finite McShane extension. The input function is nonnegative on the domain. -/
def regularExtension (D : Finset (Finset α)) (hD : D.Nonempty)
    (f : Finset α → ℝ) (L K : ℝ) (A : Finset α) : ℝ :=
  min K (D.inf' hD fun B ↦ f B + L * ((A \ B).card : ℝ))

theorem regularExtension_nonneg {D : Finset (Finset α)} (hD : D.Nonempty)
    {f : Finset α → ℝ} {L K : ℝ}
    (hf : ∀ B ∈ D, 0 ≤ f B) (hL : 0 ≤ L) (hK : 0 ≤ K) (A : Finset α) :
    0 ≤ regularExtension D hD f L K A := by
  refine le_min hK (le_inf' _ _ fun B hB ↦ ?_)
  exact add_nonneg (hf B hB) (by positivity)

theorem regularExtension_le {D : Finset (Finset α)} (hD : D.Nonempty)
    (f : Finset α → ℝ) (L K : ℝ) (A : Finset α) :
    regularExtension D hD f L K A ≤ K := min_le_left _ _

theorem regularExtension_eq {D : Finset (Finset α)} (hD : D.Nonempty)
    {f : Finset α → ℝ} {L K : ℝ}
    (hf : ∀ A ∈ D, ∀ B ∈ D, |f A - f B| ≤ L * ((A \ B).card : ℝ))
    {A : Finset α} (hA : A ∈ D) (hK : f A ≤ K) :
    regularExtension D hD f L K A = f A := by
  apply le_antisymm
  · refine (min_le_right _ _).trans ?_
    have h := inf'_le (s := D) (fun B ↦ f B + L * ((A \ B).card : ℝ)) hA
    simpa only [Finset.sdiff_self, card_empty, Nat.cast_zero, mul_zero, add_zero] using h
  · refine le_min hK (le_inf' _ _ fun B hB ↦ ?_)
    linarith [(le_abs_self (f A - f B)).trans (hf A hA B hB)]

private theorem regularExtension_sub_le {D : Finset (Finset α)} (hD : D.Nonempty)
    (f : Finset α → ℝ) {L : ℝ} (hL : 0 ≤ L) (K : ℝ) (A B : Finset α) :
    regularExtension D hD f L K A - regularExtension D hD f L K B ≤
      L * ((A \ B).card : ℝ) := by
  let g (U : Finset α) := D.inf' hD fun C ↦ f C + L * ((U \ C).card : ℝ)
  have hg : g A ≤ g B + L * ((A \ B).card : ℝ) := by
    obtain ⟨C, hC, heq⟩ := exists_mem_eq_inf' hD (fun C ↦ f C + L * ((B \ C).card : ℝ))
    change g B = f C + L * ((B \ C).card : ℝ) at heq
    rw [heq]
    refine (inf'_le (s := D) (fun C ↦ f C + L * ((A \ C).card : ℝ)) hC).trans ?_
    have h : ((A \ C).card : ℝ) ≤ (A \ B).card + (B \ C).card := by
      exact_mod_cast card_sdiff_triangle A B C
    linarith [mul_le_mul_of_nonneg_left h hL]
  change min K (g A) - min K (g B) ≤ _
  by_cases hB : g B ≤ K
  · rw [min_eq_right hB]
    linarith [min_le_right K (g A)]
  · rw [min_eq_left (le_of_not_ge hB)]
    have h : 0 ≤ L * ((A \ B).card : ℝ) := by positivity
    linarith [min_le_left K (g A)]

theorem regularExtension_exchangeLipschitz {D : Finset (Finset α)} (hD : D.Nonempty)
    (f : Finset α → ℝ) {L : ℝ} (hL : 0 ≤ L) (K : ℝ) (s : Finset α) (k : ℕ) :
    ExchangeLipschitz s k (regularExtension D hD f L K) L := by
  intro A hA B hB hAB
  have hsize : A.card = B.card := (mem_powersetCard.mp hA).2.trans (mem_powersetCard.mp hB).2.symm
  have hBA : (B \ A).card ≤ 1 := card_sdiff_comm hsize ▸ hAB
  have bound {U V : Finset α} (h : (U \ V).card ≤ 1) :
      regularExtension D hD f L K U - regularExtension D hD f L K V ≤ L :=
    (regularExtension_sub_le hD f hL K U V).trans
      (mul_le_of_le_one_right hL (by exact_mod_cast h))
  exact abs_sub_le_iff.mpr ⟨bound hAB, bound hBA⟩

end Extension

/-- Clipping bounds the mean shift by the probability of leaving the regular domain. -/
theorem sliceMean_sub_abs_le {s : Finset α} {k : ℕ} {f g : Finset α → ℝ}
    {E : Finset α → Prop} {K : ℝ}
    (hK : ∀ A ∈ s.powersetCard k, |f A - g A| ≤ K)
    (heq : ∀ A ∈ s.powersetCard k, E A → f A = g A) :
    |sliceMean s k f - sliceMean s k g| ≤
      K * sliceProbability s k (fun A ↦ ¬ E A) := by
  rw [sliceMean, sliceMean, mean, mean, ← sub_div, ← sum_sub_distrib, abs_div,
    abs_of_nonneg (show 0 ≤ ((s.powersetCard k).card : ℝ) from Nat.cast_nonneg _), sliceProbability, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ A ∈ s.powersetCard k, if ¬ E A then K else 0 := by
      refine sum_le_sum fun A hA ↦ ?_
      by_cases h : E A
      · simp [h, heq A hA h]
      · simpa [h] using hK A hA
    _ = _ := by
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
      congr 3
      ext A
      simp only [mem_filter]

variable {p k : ℕ} [NeZero p]

/-- Probability on the uniform slice of the cyclic group. -/
abbrev probability (p k : ℕ) [NeZero p] (E : Finset (ZMod p) → Prop) : ℝ :=
  sliceProbability univ k E

/-- The regularity union bound, with the exact containment probability of
each possible witness of size «L + 1». -/
def irregularBound (p k m L : ℕ) : ℝ :=
  (p : ℝ) * (m.choose (L + 1) : ℝ) * ((p - (L + 1)).choose (k - (L + 1)) : ℝ) /
    (p.choose k : ℝ)

/-- To fail regularity, some translate must contain «L + 1» specified sample points. -/
theorem probability_irregular_le (P : Finset (ZMod p)) (L : ℕ) :
    probability p k (fun A ↦ ¬ OutsideRegular A P L) ≤ irregularBound p k P.card L := by
  by_cases hk : L + 1 ≤ k
  · let witnesses (v : ZMod p) := (({v} : Finset (ZMod p)) + P).powersetCard (L + 1)
    have hsub : probability p k (fun A ↦ ¬ OutsideRegular A P L) ≤
        probability p k (fun A ↦ ∃ v ∈ (univ : Finset (ZMod p)),
          ∃ B ∈ witnesses v, B ⊆ A) := by
      apply sliceProbability_mono
      intro A _ hA
      obtain ⟨v, hv⟩ : ∃ v : ZMod p, L < (A ∩ ({v} + P)).card := by
        simpa only [OutsideRegular, not_forall, not_le] using hA
      obtain ⟨B, hB, hc⟩ := exists_subset_card_eq (show L + 1 ≤ _ from hv)
      refine ⟨v, mem_univ _, B, mem_powersetCard.mpr ⟨?_, hc⟩, hB.trans inter_subset_left⟩
      exact hB.trans inter_subset_right
    have hcard (v : ZMod p) : (witnesses v).card = P.card.choose (L + 1) := by
      simp [witnesses, card_powersetCard, card_singleton_add]
    have hprob (v : ZMod p) (B : Finset (ZMod p)) (hB : B ∈ witnesses v) :
        probability p k (fun A ↦ B ⊆ A) =
          ((p - (L + 1)).choose (k - (L + 1)) : ℝ) / (p.choose k : ℝ) := by
      have hc := (mem_powersetCard.mp hB).2
      unfold probability sliceProbability
      have hc' := card_filter_powersetCard_subset B univ k (subset_univ B) (by omega)
      have hnum : (((univ : Finset (ZMod p)).powersetCard k).filter
          (fun A ↦ B ⊆ A)).card = (p - (L + 1)).choose (k - (L + 1)) := by
        simpa only [hc, card_univ, ZMod.card] using hc'
      rw [card_powersetCard, card_univ, ZMod.card]
      congr 2
      convert hnum using 2
      ext A
      simp only [mem_filter]
    refine hsub.trans ((sliceProbability_exists_le _ _ _ _).trans ?_)
    calc
      _ ≤ ∑ v ∈ (univ : Finset (ZMod p)), ∑ B ∈ witnesses v,
          probability p k (fun A ↦ B ⊆ A) :=
        sum_le_sum fun v _ ↦ sliceProbability_exists_le _ _ _ _
      _ = _ := by
        simp only [sum_congr rfl (hprob _), sum_const, hcard, card_univ, ZMod.card,
          nsmul_eq_mul, irregularBound]
        ring
  · have hzero : probability p k (fun A ↦ ¬ OutsideRegular A P L) =
        probability p k (fun _ ↦ False) := by
      apply le_antisymm
      · apply sliceProbability_mono
        intro A hA hv
        exact hv (fun v ↦ (card_le_card inter_subset_left).trans
          (by rw [(mem_powersetCard.mp hA).2]; omega))
      · exact sliceProbability_mono (fun _ _ h ↦ h.elim)
    rw [hzero]
    simp only [probability, sliceProbability, filter_false, card_empty, Nat.cast_zero, zero_div]
    unfold irregularBound
    positivity

end

end Green39.Terminal

end SliceRegularity

/- Source: one-percent-formal/terminal/TerminalConcentration.lean -/
section TerminalConcentration

/-
# Finite probability estimate for terminal containers

On the uniform slice, the complement of the joint event is bounded by the
irregularity probability plus one lower tail for the uncovered set and a
union of upper tails for the scores. The cover conclusion is deterministic
on that joint event.
-/

open Finset
open scoped BigOperators Classical Pointwise

namespace Green39.Terminal

open Concentration

noncomputable section

variable {p k : ℕ} [NeZero p]

/-- Avoidance probability of a fixed set of size «m» on the uniform slice. -/
def rho (p k m : ℕ) : ℝ := ((p - m).choose k : ℝ) / (p.choose k : ℝ)

/-- The exact mean of an outside score, when «0 < k». -/
def scoreMean (p k m : ℕ) : ℝ :=
  (p : ℝ) * ((p - 1 - m).choose (k - 1) : ℝ) / (p.choose k : ℝ)

theorem rho_nonneg (p k m : ℕ) : 0 ≤ rho p k m := by
  unfold rho
  positivity

theorem rho_pos {p k m : ℕ} (hk : k ≤ p - m) : 0 < rho p k m := by
  unfold rho
  have := Nat.choose_pos hk
  have := Nat.choose_pos (hk.trans (Nat.sub_le p m))
  positivity

theorem mean_holes (P : Finset (ZMod p)) :
    sliceMean univ k (fun A ↦ ((uncovered A P).card : ℝ)) = (p : ℝ) * rho p k P.card := by
  simp only [sliceMean, mean, card_powersetCard, card_univ, ZMod.card, ← Nat.cast_sum,
    sum_card_uncovered, Nat.cast_mul, rho, mul_div_assoc]

theorem mean_score (P : Finset (ZMod p)) {t : ZMod p} (ht : t ∉ P) (hk : 0 < k) :
    sliceMean univ k (fun A ↦ ((outsideHits A P t).card : ℝ)) = scoreMean p k P.card := by
  simp only [sliceMean, mean, card_powersetCard, card_univ, ZMod.card, ← Nat.cast_sum,
    sum_card_outsideHits P ht hk, Nat.cast_mul, scoreMean]

theorem scoreMean_eq {p k m : ℕ} (hk : 0 < k) (hm : m < p) :
    scoreMean p k m = (k : ℝ) * rho p k m * ((p : ℝ) / ((p : ℝ) - m)) := by
  have hnat : (p - m) * (p - 1 - m).choose (k - 1) = (p - m).choose k * k := by
    have h := Nat.add_one_mul_choose_eq (p - 1 - m) (k - 1)
    rwa [show p - 1 - m + 1 = p - m by omega, show k - 1 + 1 = k by omega] at h
  have hreal : ((p : ℝ) - m) * ((p - 1 - m).choose (k - 1) : ℝ) =
      ((p - m).choose k : ℝ) * k := by
    rw [← Nat.cast_sub hm.le]
    exact_mod_cast hnat
  have hpm : (p : ℝ) - m ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hm.ne')
  have hfactor : ((p - 1 - m).choose (k - 1) : ℝ) =
      ((p - m).choose k : ℝ) * k / ((p : ℝ) - m) := by
    apply (eq_div_iff hpm).mpr
    rwa [mul_comm]
  rw [scoreMean, rho, hfactor]
  ring

private theorem card_lost_holes_le (A B P : Finset (ZMod p)) :
    (uncovered A P \ uncovered B P).card ≤ P.card * (B \ A).card := by
  let additions := (B \ A).biUnion (fun v ↦ ({v} : Finset (ZMod p)) + P)
  have hsub : uncovered A P \ uncovered B P ⊆ additions := by
    intro x hx
    obtain ⟨hxA, hxB⟩ := mem_sdiff.mp hx
    have hxBP : x ∈ B + P := by
      by_contra h
      exact hxB (mem_sdiff.mpr ⟨mem_univ _, h⟩)
    obtain ⟨v, hvB, a, ha, he⟩ := mem_add.mp hxBP
    have hvA : v ∉ A := fun hvA ↦ (mem_sdiff.mp hxA).2 (mem_add.mpr ⟨v, hvA, a, ha, he⟩)
    exact mem_biUnion.mpr ⟨v, mem_sdiff.mpr ⟨hvB, hvA⟩,
      mem_add.mpr ⟨v, mem_singleton_self _, a, ha, he⟩⟩
  calc
    _ ≤ additions.card := card_le_card hsub
    _ ≤ ∑ v ∈ B \ A, (({v} : Finset (ZMod p)) + P).card := card_biUnion_le
    _ = _ := by simp [card_singleton_add, mul_comm]

theorem holes_exchangeLipschitz (P : Finset (ZMod p)) :
    ExchangeLipschitz univ k (fun A ↦ ((uncovered A P).card : ℝ))
      (max 1 (P.card : ℝ)) := by
  intro A hA B hB hAB
  have hsize : A.card = B.card := (mem_powersetCard.mp hA).2.trans (mem_powersetCard.mp hB).2.symm
  have hBA : (B \ A).card ≤ 1 := card_sdiff_comm hsize ▸ hAB
  have hd (U V : Finset (ZMod p)) (h : (V \ U).card ≤ 1) :
      ((uncovered U P).card : ℝ) - (uncovered V P).card ≤ (P.card : ℝ) := by
    have hle := (le_card_sdiff (uncovered V P) (uncovered U P)).trans (card_lost_holes_le U V P)
    have hcard : (uncovered U P).card ≤ (uncovered V P).card + P.card := by
      have hh := Nat.mul_le_mul_left P.card h
      omega
    have hr : ((uncovered U P).card : ℝ) ≤ (uncovered V P).card + (P.card : ℝ) := by
      exact_mod_cast hcard
    linarith
  exact abs_sub_le_iff.mpr ⟨(hd A B hBA).trans (le_max_right _ _),
    (hd B A hAB).trans (le_max_right _ _)⟩

private theorem score_le_of_mem {A : Finset (ZMod p)} (hA : A ∈ (univ : Finset (ZMod p)).powersetCard k)
    (P : Finset (ZMod p)) (t : ZMod p) : ((outsideHits A P t).card : ℝ) ≤ (k : ℝ) := by
  have h := card_le_card (inter_subset_left :
    outsideHits A P t ⊆ A + {t})
  rw [card_add_singleton, (mem_powersetCard.mp hA).2] at h
  exact_mod_cast h

private theorem score_zero_of_mem (A P : Finset (ZMod p)) {t : ZMod p} (ht : t ∈ P) :
    (outsideHits A P t).card = 0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hadd, hxH⟩ := mem_inter.mp hx
  obtain ⟨a, ha, v, hv, he⟩ := mem_add.mp hadd
  exact (mem_sdiff.mp hxH).2 (mem_add.mpr ⟨a, ha, v, (mem_singleton.mp hv).symm ▸ ht, he⟩)

private theorem score_regular_lipschitz (P : Finset (ZMod p)) (L : ℕ) (t : ZMod p)
    {A B : Finset (ZMod p)} (hsize : A.card = B.card)
    (hA : OutsideRegular A P L) (hB : OutsideRegular B P L) :
    |((outsideHits A P t).card : ℝ) - (outsideHits B P t).card| ≤
      (1 + (L : ℝ)) * ((A \ B).card : ℝ) := by
  have hh := dist_card_outsideHits_le hsize hA hB t
  have he : ((Nat.dist (outsideHits A P t).card (outsideHits B P t).card : ℕ) : ℝ) =
      |((outsideHits A P t).card : ℝ) - (outsideHits B P t).card| := by
    rcases le_total (outsideHits A P t).card (outsideHits B P t).card with hab | hba
    · rw [Nat.dist_eq_sub_of_le hab, Nat.cast_sub hab, abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hab))]
      ring
    · rw [Nat.dist_eq_sub_of_le_right hba, Nat.cast_sub hba, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hba))]
  rw [← he]
  exact_mod_cast hh

/-- The tail bound consists of one regularity union bound, a lower tail for
the holes, and at most «p» upper tails with deviation «u». -/
def failureBound (p k m L : ℕ) (δ u : ℝ) : ℝ :=
  irregularBound p k m L +
    Real.exp (-(δ * (p : ℝ) * rho p k m) ^ 2 / (2 * (k : ℝ) * (max 1 (m : ℝ)) ^ 2)) +
    (p : ℝ) * Real.exp (-u ^ 2 / (2 * (k : ℝ) * (1 + (L : ℝ)) ^ 2))

/-- The good event includes regularity, the lower bound on holes and the cap on every score. -/
def JointGood (P : Finset (ZMod p)) (k L : ℕ) (δ : ℝ) (A : Finset (ZMod p)) : Prop :=
  OutsideRegular A P L ∧
  (1 - δ) * (p : ℝ) * rho p k P.card ≤ (uncovered A P).card ∧
  ∀ t : ZMod p, ((outsideHits A P t).card : ℝ) ≤ (1 + δ) * k * rho p k P.card

/-- Finite simultaneous estimate on the true uniform slice. The margin condition
pays for the shift between the genuine score and the clipped extension. -/
theorem probability_not_jointGood_le (P : Finset (ZMod p)) (L : ℕ) {δ u : ℝ}
    (hk : 0 < k) (hkp : k ≤ p) (hδ : 0 ≤ δ) (hu : 0 ≤ u)
    (hmargin : scoreMean p k P.card + (k : ℝ) * irregularBound p k P.card L + u ≤
      (1 + δ) * k * rho p k P.card) :
    probability p k (fun A ↦ ¬ JointGood P k L δ A) ≤ failureBound p k P.card L δ u := by
  let s : Finset (ZMod p) := univ
  let m := P.card
  let r := rho p k m
  let Q := irregularBound p k m L
  let reg (A : Finset (ZMod p)) := OutsideRegular A P L
  let D := (s.powersetCard k).filter reg
  have hs : k ≤ s.card := by simpa [s, ZMod.card] using hkp
  have hQ : probability p k (fun A ↦ ¬ reg A) ≤ Q := probability_irregular_le P L
  by_cases hQ1 : Q < 1
  swap
  · have hprob : probability p k (fun A ↦ ¬ JointGood P k L δ A) ≤ 1 := by
      linarith [sliceProbability_add_compl s hs (fun A ↦ ¬ JointGood P k L δ A),
        sliceProbability_nonneg s k (fun A ↦ ¬ ¬ JointGood P k L δ A)]
    refine hprob.trans ?_
    unfold failureBound
    have hQ' : 1 ≤ irregularBound p k P.card L := le_of_not_gt hQ1
    have hp0 : 0 ≤ (p : ℝ) := Nat.cast_nonneg _
    linarith [Real.exp_nonneg (-(δ * (p : ℝ) * rho p k P.card) ^ 2 /
      (2 * (k : ℝ) * (max 1 (P.card : ℝ)) ^ 2)),
      mul_nonneg hp0 (Real.exp_nonneg (-u ^ 2 / (2 * (k : ℝ) * (1 + (L : ℝ)) ^ 2)))]
  have hD : D.Nonempty := by
    by_contra h
    have hD0 : D = ∅ := not_nonempty_iff_eq_empty.mp h
    have hreg0 : probability p k reg = 0 := by
      change (D.card : ℝ) / (s.powersetCard k).card = 0
      rw [hD0, card_empty, Nat.cast_zero, zero_div]
    have hc := sliceProbability_add_compl s hs reg
    change probability p k reg + probability p k (fun A ↦ ¬ reg A) = 1 at hc
    linarith
  let X (t : ZMod p) (A : Finset (ZMod p)) : ℝ := (outsideHits A P t).card
  let F (t : ZMod p) := regularExtension D hD (X t) (1 + (L : ℝ)) k
  have hF_eq (t : ZMod p) {A : Finset (ZMod p)} (hA : A ∈ s.powersetCard k)
      (hreg : reg A) : F t A = X t A := by
    apply regularExtension_eq hD ?_ (mem_filter.mpr ⟨hA, hreg⟩) (score_le_of_mem hA P t)
    intro B hB C hC
    have hb := mem_filter.mp hB
    have hc := mem_filter.mp hC
    exact score_regular_lipschitz P L t
      ((mem_powersetCard.mp hb.1).2.trans (mem_powersetCard.mp hc.1).2.symm) hb.2 hc.2
  have hFmean (t : ZMod p) (ht : t ∉ P) :
      sliceMean s k (F t) ≤ scoreMean p k m + (k : ℝ) * Q := by
    have hdev := sliceMean_sub_abs_le (s := s) (k := k) (E := reg) (K := (k : ℝ))
      (f := F t) (g := X t) (fun A hA ↦ ?_) (fun A hA hr ↦ hF_eq t hA hr)
    · have hm : sliceMean s k (X t) = scoreMean p k m := mean_score P ht hk
      have h := (le_abs_self _).trans hdev
      rw [hm] at h
      have hmul := mul_le_mul_of_nonneg_left hQ (Nat.cast_nonneg k : 0 ≤ (k : ℝ))
      change _ ≤ (k : ℝ) * probability p k (fun A ↦ ¬ reg A) at h
      linarith
    · apply abs_sub_le_iff.mpr
      have hF0 : 0 ≤ F t A := regularExtension_nonneg hD (fun _ _ ↦ by dsimp [X]; positivity)
        (by positivity) (Nat.cast_nonneg _) _
      have hF1 : F t A ≤ (k : ℝ) := regularExtension_le hD _ _ _ _
      have hX0 : 0 ≤ X t A := Nat.cast_nonneg _
      have hX1 : X t A ≤ (k : ℝ) := score_le_of_mem hA P t
      constructor <;> linarith
  let H (A : Finset (ZMod p)) : ℝ := (uncovered A P).card
  let lower (A : Finset (ZMod p)) := δ * (p : ℝ) * r ≤ sliceMean s k H - H A
  let upper (t : ZMod p) (A : Finset (ZMod p)) := u ≤ F t A - sliceMean s k (F t)
  have hsub : probability p k (fun A ↦ ¬ JointGood P k L δ A) ≤
      probability p k (fun A ↦ ¬ reg A ∨ lower A ∨ ∃ t ∈ (univ \ P), upper t A) := by
    apply sliceProbability_mono
    intro A hA hbad
    by_cases hreg : reg A
    swap
    · exact Or.inl hreg
    right
    by_cases hH : (1 - δ) * (p : ℝ) * r ≤ H A
    swap
    · left
      dsimp only [lower]
      have hmean : sliceMean s k H = (p : ℝ) * r := mean_holes P
      rw [hmean]
      linarith
    right
    have hnot : ¬ ∀ t : ZMod p, X t A ≤ (1 + δ) * (k : ℝ) * r :=
      fun h ↦ hbad ⟨hreg, hH, h⟩
    obtain ⟨t, ht⟩ := not_forall.mp hnot
    have htP : t ∉ P := by
      intro hm
      apply ht
      dsimp only [X]
      rw [score_zero_of_mem A P hm, Nat.cast_zero]
      exact mul_nonneg (by positivity) (rho_nonneg _ _ _)
    refine ⟨t, mem_sdiff.mpr ⟨mem_univ _, htP⟩, ?_⟩
    dsimp only [upper]
    rw [hF_eq t hA hreg]
    have hF := hFmean t htP
    change scoreMean p k m + (k : ℝ) * Q + u ≤ (1 + δ) * (k : ℝ) * r at hmargin
    linarith [lt_of_not_ge ht]
  have hlower : probability p k lower ≤
      Real.exp (-(δ * (p : ℝ) * r) ^ 2 / (2 * (k : ℝ) * (max 1 (m : ℝ)) ^ 2)) :=
    sliceProbability_le_le hs (holes_exchangeLipschitz (k := k) P)
      (le_trans zero_le_one (le_max_left _ _))
      (mul_nonneg (mul_nonneg hδ (Nat.cast_nonneg _)) (rho_nonneg p k m))
  have hUpper (t : ZMod p) :
      probability p k (upper t) ≤
        Real.exp (-u ^ 2 / (2 * (k : ℝ) * (1 + (L : ℝ)) ^ 2)) :=
    sliceProbability_ge_le hs
      (regularExtension_exchangeLipschitz hD (X t) (show 0 ≤ 1 + (L : ℝ) by positivity) k s k)
      (by positivity) hu
  refine hsub.trans ((sliceProbability_or_le s k _ _).trans ?_)
  refine (add_le_add hQ (sliceProbability_or_le s k _ _)).trans ?_
  refine (add_le_add (le_refl Q) (add_le_add hlower (sliceProbability_exists_le s k _ _))).trans ?_
  have hsum : ∑ t ∈ (univ \ P), probability p k (upper t) ≤
      (p : ℝ) * Real.exp (-u ^ 2 / (2 * (k : ℝ) * (1 + (L : ℝ)) ^ 2)) := by
    calc
      _ ≤ ∑ _t ∈ (univ \ P), Real.exp (-u ^ 2 / (2 * (k : ℝ) * (1 + (L : ℝ)) ^ 2)) :=
        sum_le_sum fun t _ ↦ hUpper t
      _ ≤ _ := by
        rw [sum_const, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        exact_mod_cast ((card_le_card (sdiff_subset (s := (univ : Finset (ZMod p))) (t := P))).trans_eq
          (by rw [card_univ, ZMod.card]))
  refine (add_le_add (le_refl Q) (add_le_add (le_refl _) hsum)).trans_eq ?_
  dsimp [failureBound, Q, r, m]
  ring

/-- Every cover has the stated number of centers outside each listed container. -/
def CoversOutside (P : Finset (ZMod p)) (k : ℕ) (ζ : ℝ) (A : Finset (ZMod p)) : Prop :=
  ∀ T : Finset (ZMod p), A + T = univ →
    (1 - ζ) * (p : ℝ) / k ≤ ((T \ P).card : ℝ)

theorem coversOutside_of_jointGood {P : Finset (ZMod p)} {L : ℕ} {δ ζ : ℝ}
    {A : Finset (ZMod p)} (hk : 0 < k) (hδ : 0 ≤ δ) (hρ : 0 < rho p k P.card)
    (hζ : 1 - ζ ≤ (1 - δ) / (1 + δ)) (hA : JointGood P k L δ A) :
    CoversOutside P k ζ A := by
  intro T hT
  calc
    _ ≤ (1 - δ) / (1 + δ) * (p : ℝ) / k := by
      gcongr
    _ ≤ _ := by
      have hh : (1 - δ) * (Fintype.card (ZMod p) : ℝ) * rho p k P.card ≤
          (uncovered A P).card := by simpa only [ZMod.card] using hA.2.1
      simpa only [ZMod.card] using le_card_outside_of_bounds A P T hT hk hδ hρ hh
        (fun t _ ↦ hA.2.2 t)

/-- Finite version of (1) for a deterministic list, with a separate bound for
each container. -/
theorem probability_not_coversOutside_list_le (Ps : Finset (Finset (ZMod p)))
    (L : ℕ) {δ ζ u : ℝ}
    (hk : 0 < k) (hkp : k ≤ p) (hδ : 0 ≤ δ) (hu : 0 ≤ u)
    (hζ : 1 - ζ ≤ (1 - δ) / (1 + δ))
    (hρ : ∀ P ∈ Ps, 0 < rho p k P.card)
    (hmargin : ∀ P ∈ Ps, scoreMean p k P.card + (k : ℝ) * irregularBound p k P.card L + u ≤
      (1 + δ) * k * rho p k P.card) :
    probability p k (fun A ↦ ¬ ∀ P ∈ Ps, CoversOutside P k ζ A) ≤
      ∑ P ∈ Ps, failureBound p k P.card L δ u := by
  refine (sliceProbability_mono (F := fun A ↦ ∃ P ∈ Ps, ¬ JointGood P k L δ A) ?_).trans
    ((sliceProbability_exists_le _ _ _ _).trans ?_)
  · intro A _ hA
    by_contra h
    apply hA
    exact fun P hP ↦ coversOutside_of_jointGood hk hδ (hρ P hP) hζ
      (by_contra fun hj ↦ h ⟨P, hP, hj⟩)
  · exact sum_le_sum fun P hP ↦ probability_not_jointGood_le P L hk hkp hδ hu (hmargin P hP)

end

end Green39.Terminal

end TerminalConcentration

/- Source: one-percent-formal/assembly/AssemblyFinite.lean -/
section AssemblyFinite

/- Canonical covers, balanced splits, retained terminals and fitted witnesses. -/

open Finset Filter Topology
open scoped Pointwise Classical
namespace Green39.Assembly
noncomputable section

variable {p : ℕ} [NeZero p]
open Split OnePercent.Fourier

abbrev space (p : ℕ) [NeZero p] :=
  orderedPairs (univ : Points p) (half p.sqrt) (rest p.sqrt)

def terminalOK (C : Catalog p) (A : Points p) : Prop :=
  ∀ P ∈ C.containers C.stages, Terminal.CoversOutside P p.sqrt 0.02 A

def smoothBad (C : Catalog p) (q : Sample p) : Prop :=
  ∃ i < C.stages, ∃ μ ∈ C.laws i, ¬ typical μ q

def hitBad (C : Catalog p) (q : Sample p) : Prop :=
  ∃ i < C.stages, ∃ w ∈ witnesses C i, hits w q

def cover (p : ℕ) [NeZero p] (A : Points p) :=
  ∃ T : Points p, T.card ≤ ⌊1.01*(p.sqrt : ℝ)⌋₊ ∧ A + T = univ

theorem card_union_sample {q : Sample p} (hq : q ∈ space p) :
    (q.1 ∪ q.2).card = p.sqrt := by
  have h := (mem_powersetCard.mp (orderedPairs_union_mem hq)).2
  dsimp [half,rest] at h
  omega

/-- The upstream floor budget implies eligibility for the canonical cover. -/
theorem small_of_cover {A : Points p} (ha : A.card = p.sqrt) (hk : 0 < p.sqrt)
    (hc : cover p A) : (smallCovers A).Nonempty := by
  obtain ⟨T,ht,hcover⟩ := hc
  refine ⟨T, mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _),hcover,?_⟩⟩
  have h₁ : (T.card : ℝ) ≤ 1.01*p.sqrt :=
    (Nat.cast_le.mpr ht).trans (Nat.floor_le (by positivity))
  have h₂ : (p.sqrt : ℝ)^2 ≤ p := by exact_mod_cast Nat.sqrt_le' p
  rw [ha,le_div_iff₀ (Nat.cast_pos.mpr hk)]
  nlinarith [mul_le_mul_of_nonneg_right h₁ (Nat.cast_nonneg p.sqrt)]

/-- Starting from a true upstream cover yields a concrete failed event on every split. -/
theorem witness_inclusion {C : Catalog p} (spec : StageSpec C) (hk : 100000 ≤ p.sqrt)
    (hsparse : ∀ i < C.stages, 8*Real.log (4*(p:ℝ)) <
      (sMax p.sqrt : ℝ) * eta (x p i)^2)
    {q : Sample p} (hq : q ∈ space p) (hc : cover p (q.1 ∪ q.2)) :
    CanonicalBalanceFailure q ∨ ¬ terminalOK C (q.1 ∪ q.2) ∨ smoothBad C q ∨ hitBad C q := by
  classical
  let k := p.sqrt
  let A := q.1 ∪ q.2
  let T := canonicalCover A
  let G := nearPrivateCenters A T (0.0225*A.card)
  have ha : A.card = k := card_union_sample hq
  have hk0 : 0 < k := lt_of_lt_of_le (by decide : 0 < 100000) hk
  have hk0' : (0:ℝ) < k := Nat.cast_pos.mpr hk0
  have hsmall := small_of_cover ha hk0 hc
  have hT := (mem_filter.mp (canonicalCover_spec hsmall).1).2
  change A + T = univ ∧ (T.card : ℝ) ≤ 1.01*p/A.card at hT
  have hg := card_nearPrivateCenters_onePercent hT.1 (ha ▸ hk0)
    (ha ▸ Nat.sqrt_le' p) hT.2
  have hstart : (k : ℝ)/9 ≤ G.card := ha ▸ hg.2.2.trans (hg.2.1.trans hg.1)
  have hGT : G ⊆ T := fun _ ht => (mem_nearPrivateCenters.mp ht).1
  have hm := numerical (p := p) hk (Nat.lt_succ_sqrt' p)
  have hTk : (T.card : ℝ) * k ≤ 1.01*p := (le_div_iff₀ hk0').mp (ha ▸ hT.2)
  have hTk' : (T.card : ℝ) ≤ 2*k := by
    apply (le_of_mul_le_mul_right _ hk0')
    nlinarith only [hm.1,hTk,sq_nonneg (k:ℝ)]
  have hGk := (Nat.cast_le.mpr (card_le_card hGT)).trans hTk'
  by_cases hb : BalanceFailure A T q.1 q.2
  · exact Or.inl ⟨hsmall,hb⟩
  right
  by_cases hnt : ¬ terminalOK C A
  · exact Or.inl hnt
  right
  have ht := Classical.not_not.mp hnt
  by_cases hs : smoothBad C q
  · exact Or.inl hs
  right
  rcases iterate spec G hk0 hstart hGk with
    ⟨i,hi,P,hP,V,hVP,hVG,hV,F,hFV,hF,μ,hμ,hfit⟩ | ⟨P,hP,hret⟩
  · have hFp : F.Nonempty := by
      apply card_pos.mp
      have hx : 0 < x p i := lt_trans (by norm_num) (spec.active i hi)
      have hpos : 0 < (p.sqrt:ℝ)*Transcripts.lossRate (x p i) := by unfold Transcripts.lossRate; positivity
      exact_mod_cast hpos.trans_le hF
    obtain ⟨S,hSF,hsz,hfitS⟩ := exists_fourierFit_sparsify F μ (sMax k) (Real.exp_nonneg _)
      hfit (fun _ _ => hsparse i hi)
    have hSp : S.Nonempty := card_pos.mp (hsz ▸ lt_min hFp.card_pos (by dsimp [sMax,k]; omega))
    have hrV : rSize k ≤ V.card := by
      have hr : 10*rSize k ≤ k := by simpa [Nat.mul_comm] using Nat.div_mul_le_self k 10
      have hr' : 10*(rSize k:ℝ) ≤ k := by exact_mod_cast hr
      change (0.11:ℝ)*k ≤ V.card at hV
      exact_mod_cast (show (rSize k:ℝ) ≤ V.card by linarith)
    obtain ⟨R,hR₀⟩ := powersetCard_nonempty.mpr hrV
    obtain ⟨hRV,hr⟩ := mem_powersetCard.mp hR₀
    have hRp : R.Nonempty := card_pos.mp (hr ▸ (by dsimp [rSize,k]; omega))
    have hRG := hRV.trans hVG
    have hSG := (hSF.trans hFV).trans hVG
    have hbal (t) (h : t ∈ G) :
        ((nonprivateLabels A T q.1 t).card : ℝ) ≤ 0.0114*A.card ∧
        ((nonprivateLabels A T q.2 t).card : ℝ) ≤ 0.0114*A.card :=
      ⟨le_of_not_gt fun hh => hb ⟨t,h,Or.inl hh⟩,le_of_not_gt fun hh => hb ⟨t,h,Or.inr hh⟩⟩
    obtain ⟨_,h1,_,h2,hd⟩ := mem_orderedPairs.mp hq
    have hpriv := balanced_halves_bounds (show q.1 ∪ q.2 = A from rfl) hd (by rw [ha]; exact h1)
      (hRG.trans hGT) (hSG.trans hGT) (fun t ht => (hbal t (hRG ht)).1)
      (fun t ht => (hbal t (hSG ht)).2)
    obtain ⟨hl,hu⟩ := hpriv
    rw [ha] at hl hu
    have htyp : typical μ q := by_contra fun hn => hs ⟨i,hi,μ,hμ,hn⟩
    let U := q.1 + R
    have hpred := sum_predicted_ge_of_l1 q.2 U S μ htyp.1
    have hbase : (0.244 : ℝ)*R.card ≤ (q.2.card:ℝ)*U.card/p - 0.00000001*k := by
      rw [h2]
      have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (rest k))) (Nat.cast_nonneg p)
      rw [hr] at h ⊢
      rw [←mul_assoc] at h
      exact hm.2.2.trans (sub_le_sub_right h _)
    have hpred' : (0.244:ℝ)*R.card*S.card ≤ ∑ z ∈ q.2, predicted U S μ z := by
      linarith only [hpred,mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg S.card)]
    have hobs : (∑ z ∈ q.2, observed U S z) ≤ (0.115:ℝ)*R.card*S.card := by
      have hcoef : (0.0114:ℝ)*k ≤ 0.115*R.card := by rw [hr]; linarith only [hm.2.1]
      simp only [Nat.cast_sum, singleton_add] at hu
      exact hu.trans (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg S.card))
    have hh := (exceptionalHits_section5 q.1 q.2 R S μ hk0 hRp hSp
      (by rw [h2]; exact Nat.sub_le _ _) (spec.capped i hi μ hμ).1 hpred' hobs
      (fun v _ => htyp.2 v)).2
    refine ⟨i,hi,(R,S,μ),mem_biUnion.mpr ⟨P,hP,mem_filter.mpr ⟨?_,hfitS⟩⟩,hh.le⟩
    exact mem_product.mpr ⟨mem_powersetCard.mpr ⟨hRV.trans hVP,hr⟩,mem_product.mpr
      ⟨mem_filter.mpr ⟨mem_powerset.mpr ((hSF.trans hFV).trans hVP),hSp,hsz ▸ min_le_right ..⟩,hμ⟩⟩
  · have hout := ht P hP T hT.1
    have hinter : ((G ∩ P).card:ℝ) ≤ (T ∩ P).card :=
      Nat.cast_le.mpr (card_le_card (inter_subset_inter_right hGT))
    have he : ((T \ P).card:ℝ) + (T ∩ P).card = T.card := by exact_mod_cast card_sdiff_add_card_inter T P
    have hl := (div_le_iff₀ hk0').mp hout
    change (0.11:ℝ)*k ≤ _ at hret
    have hn : (0.11:ℝ)*k ≤ (T.card:ℝ) - (T \ P).card := by linarith
    exfalso
    nlinarith only [mul_le_mul_of_nonneg_right hn hk0'.le,hl,hTk,hm.1,sq_pos_of_pos hk0']

end
end Green39.Assembly

end AssemblyFinite

/- Source: one-percent-formal/split/WitnessProbability.lean -/
section WitnessProbability

/-
# The §5 hit-count bound

For a particular set of r distinct hits, the probability that the sample
contains all of them is the ratio of two binomial coefficients. Union over
the r-subsets of the bad set before using the bound on its cardinality.
-/

open Finset
open scoped BigOperators Classical


namespace Green39.Split

open Concentration

noncomputable section

variable {α : Type*} [DecidableEq α]

private theorem choose_le_choose_mul_ratio_pow {m n r : ℕ} (hmn : m ≤ n) (hr : r ≤ n) :
    (m.choose r : ℝ) ≤ (n.choose r : ℝ) * ((m : ℝ) / n) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    obtain h | h := lt_or_ge m (r + 1)
    · rw [Nat.choose_eq_zero_of_lt h]
      simp only [Nat.cast_zero]
      positivity
    have hnr : r ≤ n := by omega
    have hmr : r ≤ m := by omega
    have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hstep : ((m - r : ℕ) : ℝ) ≤ (n - r : ℕ) * ((m : ℝ) / n) := by
      rw [← mul_div_assoc, le_div_iff₀ hn, Nat.cast_sub hmr, Nat.cast_sub hnr]
      have hmul : 0 ≤ (r : ℝ) * ((n : ℝ) - m) :=
        mul_nonneg (by positivity) (sub_nonneg.mpr (by exact_mod_cast hmn))
      nlinarith only [hmul]
    have hrec (a : ℕ) :
        (a.choose (r + 1) : ℝ) * (r + 1 : ℝ) = a.choose r * (a - r : ℕ) := by
      exact_mod_cast Nat.choose_succ_right_eq a r
    apply (mul_le_mul_iff_left₀ (by positivity : (0 : ℝ) < r + 1)).mp
    rw [hrec m]
    calc
      (m.choose r : ℝ) * (m - r : ℕ)
          ≤ ((n.choose r : ℝ) * ((m : ℝ) / n) ^ r) *
              ((n - r : ℕ) * ((m : ℝ) / n)) :=
        mul_le_mul (ih hnr) hstep (by positivity) (by positivity)
      _ = ((n.choose r : ℝ) * (n - r : ℕ)) * ((m : ℝ) / n) ^ (r + 1) := by
        rw [pow_succ]
        ring
      _ = ((n.choose (r + 1) : ℝ) * ((m : ℝ) / n) ^ (r + 1)) * (r + 1 : ℝ) := by
        rw [← hrec n]
        ring

/-- Binomial upper bound for at least r hits in a sample of size j. -/
theorem sliceProbability_hits_binomial (s D : Finset α) {j r : ℕ}
    (hj : j ≤ s.card) (hr : r ≤ j) :
    sliceProbability s j (fun B ↦ r ≤ (B ∩ D).card) ≤
      (j.choose r : ℝ) * (((s ∩ D).card : ℝ) / s.card) ^ r := by
  classical
  let W := (s ∩ D).powersetCard r
  have hsubset (B : Finset α) (hB : B ∈ s.powersetCard j) (h : r ≤ (B ∩ D).card) :
      ∃ C ∈ W, C ⊆ B := by
    obtain ⟨C, hC⟩ := powersetCard_nonempty.mpr h
    obtain ⟨hCsub, hCsize⟩ := mem_powersetCard.mp hC
    have hCB : C ⊆ B := hCsub.trans inter_subset_left
    have hCD : C ⊆ D := hCsub.trans inter_subset_right
    exact ⟨C, mem_powersetCard.mpr
      ⟨subset_inter (hCB.trans (mem_powersetCard.mp hB).1) hCD, hCsize⟩, hCB⟩
  have hfixed (C : Finset α) (hC : C ∈ W) :
      sliceProbability s j (fun B ↦ C ⊆ B) =
        ((s.card - r).choose (j - r) : ℝ) / (s.card.choose j : ℝ) := by
    obtain ⟨hCsub, hCsize⟩ := mem_powersetCard.mp hC
    simpa only [hCsize] using sliceProbability_contains s C j (hCsub.trans inter_subset_left)
      (hCsize ▸ hr)
  let n := s.card
  let m := (s ∩ D).card
  have hmn : m ≤ n := card_le_card inter_subset_left
  have hdenj : (0 : ℝ) < n.choose j := by exact_mod_cast Nat.choose_pos hj
  have hdenr : (0 : ℝ) < n.choose r := by exact_mod_cast Nat.choose_pos (hr.trans hj)
  have hchoose : (n.choose j : ℝ) * j.choose r = n.choose r * (n - r).choose (j - r) := by
    exact_mod_cast Nat.choose_mul (n := n) hr
  have hratio : ((n - r).choose (j - r) : ℝ) / (n.choose j : ℝ) =
      (j.choose r : ℝ) / (n.choose r : ℝ) := by
    rw [div_eq_div_iff hdenj.ne' hdenr.ne']
    linarith only [hchoose]
  calc
    sliceProbability s j (fun B ↦ r ≤ (B ∩ D).card)
        ≤ sliceProbability s j (fun B ↦ ∃ C ∈ W, C ⊆ B) := by
      rw [sliceProbability_eq_probability, sliceProbability_eq_probability]
      exact probability_mono hsubset
    _ ≤ ∑ C ∈ W, sliceProbability s j (fun B ↦ C ⊆ B) := by
      simp only [sliceProbability_eq_probability]
      exact probability_exists_le_sum _ _ _
    _ = (m.choose r : ℝ) * ((j.choose r : ℝ) / (n.choose r : ℝ)) := by
      rw [sum_congr rfl hfixed, sum_const, nsmul_eq_mul, show W.card = m.choose r from
        card_powersetCard _ _, hratio]
    _ = (j.choose r : ℝ) * ((m.choose r : ℝ) / (n.choose r : ℝ)) := by ring
    _ ≤ (j.choose r : ℝ) * ((m : ℝ) / n) ^ r := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (div_le_iff₀ hdenr).mpr
        (by simpa only [mul_comm] using choose_le_choose_mul_ratio_pow hmn (hr.trans hj))

/-- A real threshold rounds up to the corresponding integer binomial count. -/
theorem sliceProbability_hits_real_binomial (s D : Finset α) {j : ℕ} {q t : ℝ}
    (hj : j ≤ s.card) (hq : ((s ∩ D).card : ℝ) / s.card ≤ q) :
    sliceProbability s j (fun B ↦ t ≤ (B ∩ D).card) ≤
      (j.choose ⌈t⌉₊ : ℝ) * q ^ ⌈t⌉₊ := by
  let r := ⌈t⌉₊
  have hnonneg : 0 ≤ q := (by positivity : 0 ≤ ((s ∩ D).card : ℝ) / s.card).trans hq
  have hE : (fun B : Finset α ↦ t ≤ (B ∩ D).card) =
      (fun B : Finset α ↦ r ≤ (B ∩ D).card) :=
    funext fun _ ↦ propext Nat.ceil_le.symm
  rw [hE]
  by_cases hr : r ≤ j
  · exact (sliceProbability_hits_binomial s D hj hr).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hq _) (by positivity))
  · have hfalse : (s.powersetCard j).filter (fun B ↦ r ≤ (B ∩ D).card) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro B hB
      obtain ⟨hB, hhit⟩ := mem_filter.mp hB
      have hcard := (mem_powersetCard.mp hB).2
      have hle : (B ∩ D).card ≤ B.card := card_le_card inter_subset_left
      omega
    unfold sliceProbability
    rw [filter_congr_decidable _ (fun B ↦ r ≤ (B ∩ D).card) _, hfalse]
    simp only [card_empty, Nat.cast_zero, zero_div]
    positivity

/-- Replace the binomial coefficient and the ceiling by the manuscript's simpler bound. -/
theorem sliceProbability_hits_section5 (s D : Finset α) {j k : ℕ} {q : ℝ}
    (hj : j ≤ s.card) (hjk : j ≤ k) (hq : ((s ∩ D).card : ℝ) / s.card ≤ q)
    (hq₁ : q ≤ 1) :
    sliceProbability s j (fun B ↦ (0.24 : ℝ) * k ≤ (B ∩ D).card) ≤
      (2 : ℝ) ^ k * q ^ ((0.24 : ℝ) * k) := by
  let r := ⌈(0.24 : ℝ) * k⌉₊
  have hnonneg : 0 ≤ q := (by positivity : 0 ≤ ((s ∩ D).card : ℝ) / s.card).trans hq
  have hbin : (j.choose r : ℝ) ≤ (2 : ℝ) ^ k := by
    exact_mod_cast (Nat.choose_le_two_pow j r).trans (Nat.pow_le_pow_right (by decide) hjk)
  have hceil : (0.24 : ℝ) * k ≤ (r : ℝ) := Nat.le_ceil _
  have hpow : q ^ r ≤ q ^ ((0.24 : ℝ) * k) := by
    rw [← Real.rpow_natCast q r]
    exact Real.rpow_le_rpow_of_exponent_ge' hnonneg hq₁ (by positivity) hceil
  exact (sliceProbability_hits_real_binomial s D hj hq).trans
    (mul_le_mul hbin hpow (by positivity) (by positivity))

private theorem complement_density_le {s A₁ D : Finset α} {k₁ : ℕ} {η : ℝ}
    (hA₁ : A₁ ∈ s.powersetCard k₁) (hhalf : 2 * k₁ ≤ s.card) (hs : 0 < s.card)
    (hD : (D.card : ℝ) ≤ (71000 * η) ^ 2 * s.card) :
    (((s \ A₁) ∩ D).card : ℝ) / (s \ A₁).card ≤ 2 * (71000 * η) ^ 2 := by
  have hcomp : (s \ A₁).card = s.card - k₁ := by
    rw [card_sdiff_of_subset (mem_powersetCard.mp hA₁).1, (mem_powersetCard.mp hA₁).2]
  have hpos : (0 : ℝ) < (s \ A₁).card := by
    exact_mod_cast (show 0 < (s \ A₁).card by omega)
  have hpop : (s.card : ℝ) ≤ 2 * (s \ A₁).card := by
    exact_mod_cast (show s.card ≤ 2 * (s \ A₁).card by omega)
  apply (div_le_iff₀ hpos).mpr
  have hle : (((s \ A₁) ∩ D).card : ℝ) ≤ D.card := by
    exact_mod_cast card_le_card inter_subset_right
  calc
    _ ≤ (71000 * η) ^ 2 * s.card := hle.trans hD
    _ ≤ (71000 * η) ^ 2 * (2 * (s \ A₁).card) :=
      mul_le_mul_of_nonneg_left hpop (sq_nonneg _)
    _ = _ := by ring

/-- The binomial bound conditional only on A₁. The bad set is fixed on this fiber. -/
theorem conditional_witness_hits_binomial {s A₁ : Finset α} {k₁ k₂ : ℕ} {η : ℝ}
    (hA₁ : A₁ ∈ s.powersetCard k₁) (hk : k₁ + k₂ ≤ s.card)
    (hhalf : 2 * k₁ ≤ s.card) (hs : 0 < s.card) (D : Finset α → Finset α)
    (hD : ((D A₁).card : ℝ) ≤ (71000 * η) ^ 2 * s.card) :
    let r := ⌈(0.24 : ℝ) * (k₁ + k₂ : ℕ)⌉₊
    probability ((orderedPairs s k₁ k₂).filter fun q ↦ q.1 = A₁)
        (fun q ↦ (0.24 : ℝ) * (k₁ + k₂ : ℕ) ≤ (q.2 ∩ D q.1).card) ≤
      (k₂.choose r : ℝ) * (2 * (71000 * η) ^ 2) ^ r := by
  dsimp only
  have hj : k₂ ≤ (s \ A₁).card := by
    rw [card_sdiff_of_subset (mem_powersetCard.mp hA₁).1, (mem_powersetCard.mp hA₁).2]
    omega
  rw [conditional_first hA₁ (fun q ↦ (0.24 : ℝ) * (k₁ + k₂ : ℕ) ≤ (q.2 ∩ D q.1).card)]
  exact sliceProbability_hits_real_binomial (s \ A₁) (D A₁) hj
    (complement_density_le hA₁ hhalf hs hD)

/-- The §5 bound conditional only on A₁. -/
theorem conditional_witness_hits {s A₁ : Finset α} {k₁ k₂ : ℕ} {η : ℝ}
    (hA₁ : A₁ ∈ s.powersetCard k₁) (hk : k₁ + k₂ ≤ s.card)
    (hhalf : 2 * k₁ ≤ s.card) (hs : 0 < s.card) (D : Finset α → Finset α)
    (hD : ((D A₁).card : ℝ) ≤ (71000 * η) ^ 2 * s.card)
    (hη : 2 * (71000 * η) ^ 2 ≤ 1) :
    probability ((orderedPairs s k₁ k₂).filter fun q ↦ q.1 = A₁)
        (fun q ↦ (0.24 : ℝ) * (k₁ + k₂ : ℕ) ≤ (q.2 ∩ D q.1).card) ≤
      (2 : ℝ) ^ (k₁ + k₂) * (2 * (71000 * η) ^ 2) ^ ((0.24 : ℝ) * (k₁ + k₂ : ℕ)) := by
  have hj : k₂ ≤ (s \ A₁).card := by
    rw [card_sdiff_of_subset (mem_powersetCard.mp hA₁).1, (mem_powersetCard.mp hA₁).2]
    omega
  rw [conditional_first hA₁ (fun q ↦ (0.24 : ℝ) * (k₁ + k₂ : ℕ) ≤ (q.2 ∩ D q.1).card)]
  exact sliceProbability_hits_section5 (s \ A₁) (D A₁) (j := k₂) (k := k₁ + k₂)
    hj (by omega) (complement_density_le hA₁ hhalf hs hD) hη

/-- The same bound after averaging over A₁, for one fixed witness description. -/
theorem witness_hits_probability {s : Finset α} {k₁ k₂ : ℕ} {η : ℝ}
    (hk : k₁ + k₂ ≤ s.card) (hhalf : 2 * k₁ ≤ s.card) (hs : 0 < s.card)
    (D : Finset α → Finset α)
    (hD : ∀ A₁ ∈ s.powersetCard k₁, ((D A₁).card : ℝ) ≤ (71000 * η) ^ 2 * s.card)
    (hη : 2 * (71000 * η) ^ 2 ≤ 1) :
    probability (orderedPairs s k₁ k₂)
        (fun q ↦ (0.24 : ℝ) * (k₁ + k₂ : ℕ) ≤ (q.2 ∩ D q.1).card) ≤
      (2 : ℝ) ^ (k₁ + k₂) * (2 * (71000 * η) ^ 2) ^ ((0.24 : ℝ) * (k₁ + k₂ : ℕ)) := by
  rw [probability_eq_mean_first]
  apply mean_le_of_forall_le (by positivity)
  intro A₁ hA₁
  rw [← conditional_first hA₁ (fun q ↦ (0.24 : ℝ) * (k₁ + k₂ : ℕ) ≤ (q.2 ∩ D q.1).card)]
  exact conditional_witness_hits hA₁ hk hhalf hs D (hD A₁ hA₁) hη

/-- The base of the §5 exponential bound is below one at every active level. -/
theorem section5_eta_small {x : ℝ} (hx : 0 ≤ x) :
    2 * (71000 * Real.exp (-1000 - 0.22 * x)) ^ 2 ≤ 1 := by
  have h₂ : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp 1]
  have hpow : (2 : ℝ) ^ 17 ≤ Real.exp 17 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h₂ 17
    norm_num only [Real.exp_one_pow, Nat.cast_ofNat] at h ⊢
    exact h
  have hη : Real.exp (-1000 - 0.22 * x) ≤ 1 / (2 : ℝ) ^ 17 := calc
    _ ≤ Real.exp (-17) := Real.exp_le_exp.mpr (by linarith only [hx])
    _ = 1 / Real.exp 17 := by rw [Real.exp_neg, one_div]
    _ ≤ _ := one_div_le_one_div_of_le (by positivity) hpow
  calc
    _ ≤ 2 * (71000 * (1 / (2 : ℝ) ^ 17)) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hη (by norm_num)) 2)
        (by norm_num)
    _ ≤ 1 := by norm_num

end

end Green39.Split

end WitnessProbability

/- Source: one-percent-formal/assembly/AssemblyBounds.lean -/
section AssemblyBounds

open Finset Real
open scoped Pointwise Classical
namespace Green39.Assembly
noncomputable section

variable {p : ℕ} [NeZero p]
open Split OnePercent.Fourier

/-- An exponential generating-function bound counts *all* permitted sizes,
including the empty set. This spends two extra units in the intercept. -/
theorem count_subsets {α : Type*} [DecidableEq α] (P : Finset α)
    (B : Finset (Finset α)) {x a k : ℝ} (hx : 0 ≤ x)
    (hp : (P.card : ℝ) ≤ k * exp x)
    (hb : ∀ s ∈ B, s ⊆ P ∧ (s.card : ℝ) ≤ a) :
    (B.card : ℝ) ≤ exp (k + a*x) := by
  classical
  have hweight : ∑ s ∈ P.powerset, exp (-x * s.card) = (1 + exp (-x))^P.card := by
    have h := Finset.prod_one_add (f := fun _ : α => exp (-x)) P
    simp only [prod_const] at h
    simpa only [← Real.exp_nat_mul, mul_comm (-x)] using h.symm
  have hsum : (B.card : ℝ) * exp (-x*a) ≤ (1 + exp (-x)) ^ P.card := by
    rw [← hweight, ← nsmul_eq_mul, ← sum_const]
    refine (sum_le_sum (s := B) (g := fun s => exp (-x * (s.card:ℝ))) ?_).trans ?_
    · intro s hs
      exact exp_le_exp.mpr (mul_le_mul_of_nonpos_left (hb s hs).2 (neg_nonpos.mpr hx))
    · exact sum_le_sum_of_subset_of_nonneg (fun s hs => mem_powerset.mpr (hb s hs).1)
        (fun _ _ _ => (exp_pos _).le)
  have hpow : (1 + exp (-x))^P.card ≤ exp k := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + exp (-x))
      (show 1 + exp (-x) ≤ exp (exp (-x)) by linarith only [Real.add_one_le_exp (exp (-x))]) P.card
    rw [← exp_nat_mul] at h
    apply h.trans (exp_le_exp.mpr ?_)
    calc
      (P.card : ℝ) * exp (-x) ≤ (k * exp x) * exp (-x) := mul_le_mul_of_nonneg_right hp (exp_pos _).le
      _ = k := by rw [exp_neg]; field_simp
  have h := mul_le_mul_of_nonneg_right (hsum.trans hpow) (exp_pos (a*x)).le
  rwa [mul_assoc, ← exp_add, show -x*a+a*x=0 by ring, exp_zero,mul_one,← exp_add] at h

theorem count_witnesses {C : Catalog p} (spec : StageSpec C) {i : ℕ} (hi : i < C.stages) :
    ((witnesses C i).card:ℝ) ≤
      ((C.containers i).card:ℝ) * (C.laws i).card *
        exp ((p.sqrt:ℝ)*(2+0.101*x p i)) := by
  classical
  let k := p.sqrt
  let y := x p i
  have hy : 0 ≤ y := le_trans (by norm_num) (spec.active i hi).le
  let f (P : Points p) := ((P.powersetCard (rSize k)) ×ˢ
    ((P.powerset.filter fun S => S.Nonempty ∧ S.card ≤ sMax k) ×ˢ C.laws i)).filter
    (fun w => FourierFit w.2.1 w.2.2 (7*eta y*w.2.1.card))
  have hsingle (P : Points p) (hP : P ∈ C.containers i) :
      ((f P).card:ℝ) ≤ (C.laws i).card * exp ((k:ℝ)*(2+0.101*y)) := by
    have hsize := spec.containerSize i hi.le P hP
    have hr := count_subsets P (P.powersetCard (rSize k)) (a := (0.1:ℝ)*k) hy hsize (by
      intro R hR
      obtain ⟨hsub,he⟩ := mem_powersetCard.mp hR
      have hh : (rSize k : ℝ)*10 ≤ k := by exact_mod_cast Nat.div_mul_le_self k 10
      exact ⟨hsub, by rw [he]; linarith⟩)
    have hs := count_subsets P (P.powerset.filter fun S => S.Nonempty ∧ S.card ≤ sMax k)
      (a := (0.001:ℝ)*k) hy hsize (by
        intro S hS
        obtain ⟨hsub,_,he⟩ := mem_filter.mp hS
        have hh : (sMax k : ℝ)*1000 ≤ k := by exact_mod_cast Nat.div_mul_le_self k 1000
        exact ⟨mem_powerset.mp hsub,(Nat.cast_le.mpr he).trans (by linarith)⟩)
    unfold f
    apply (Nat.cast_le.mpr (card_filter_le _ _)).trans
    rw [card_product,card_product,Nat.cast_mul,Nat.cast_mul,←mul_assoc]
    apply (mul_le_mul_of_nonneg_right (mul_le_mul hr hs (by positivity) (exp_pos _).le)
      (Nat.cast_nonneg _)).trans_eq
    rw [←exp_add,mul_comm]
    congr 2
    ring
  change (((C.containers i).biUnion f).card:ℝ) ≤ _
  refine (Nat.cast_le.mpr card_biUnion_le).trans ?_
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ _ ∈ C.containers i, (C.laws i).card * exp ((k:ℝ)*(2+0.101*y)) := sum_le_sum hsingle
    _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring

def hitBase (y : ℝ) := 2*(71000*eta y)^2
def hitBound (k : ℕ) (y : ℝ) := (2:ℝ)^k * hitBase y ^ ((0.24:ℝ)*k)

theorem base_bound {y : ℝ} : hitBase y ≤ exp (-1966 - 0.44*y) := by
  have he : (2:ℝ) ≤ exp 1 := by linarith only [Real.add_one_le_exp (1:ℝ)]
  have hc : (2:ℝ)*71000^2 ≤ exp 34 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) he 34
    rw [← exp_nat_mul] at h
    norm_num at h ⊢
    linarith
  unfold hitBase eta
  rw [mul_pow, ←exp_nat_mul, ←mul_assoc]
  apply (mul_le_mul_of_nonneg_right hc (exp_pos _).le).trans_eq
  rw [←exp_add]
  congr 1
  push_cast
  ring

theorem paid_witnesses (k : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    exp ((k:ℝ)*(2+0.101*y)) * hitBound k y ≤ exp (-468*(k:ℝ)) := by
  have he : (2:ℝ) ≤ exp 1 := by linarith only [Real.add_one_le_exp (1:ℝ)]
  have h2 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) he k
  rw [← exp_nat_mul, mul_one] at h2
  have hq := Real.rpow_le_rpow (show 0 ≤ hitBase y by unfold hitBase; positivity)
    (base_bound (y:=y)) (show 0 ≤ (0.24:ℝ)*k by positivity)
  rw [←exp_mul] at hq
  unfold hitBound
  apply (mul_le_mul_of_nonneg_left (mul_le_mul h2 hq (Real.rpow_nonneg
    (by unfold hitBase; positivity) _) (exp_pos _).le) (exp_pos _).le).trans
  rw [←exp_add,←exp_add]
  apply exp_le_exp.mpr
  nlinarith [mul_nonneg (Nat.cast_nonneg k : 0 ≤ (k:ℝ)) hy]

set_option maxHeartbeats 1200000 in
theorem witness_probability {C : Catalog p} (spec : StageSpec C) {i : ℕ} (hi : i < C.stages)
    (hk : 100000 ≤ p.sqrt) {w : W p} (hw : w ∈ witnesses C i) :
    probability (orderedPairs (univ : Points p) (half p.sqrt) (rest p.sqrt)) (hits w) ≤
      hitBound p.sqrt (x p i) := by
  obtain ⟨P,_,hw⟩ := mem_biUnion.mp hw
  obtain ⟨hpair,hfit⟩ := mem_filter.mp hw
  have hr := (mem_powersetCard.mp (mem_product.mp hpair).1).2
  have hk0 : 0 < p.sqrt := by omega
  have hs : half p.sqrt + rest p.sqrt = p.sqrt := by dsimp [half,rest]; omega
  let D := fun A : Points p => exceptional (discrepancy (A+w.1) w.2.1 w.2.2)
    (cutoff w.1.card w.2.1.card p.sqrt)
  have hc : (univ : Points p).card = p := by simp
  have hb := witness_hits_probability (s := (univ : Points p)) (k₁ := half p.sqrt) (k₂ := rest p.sqrt)
    (η := eta (x p i)) (by rw [hs,hc]; exact Nat.sqrt_le_self _)
    (by rw [hc]; have h := Nat.sqrt_le_self p; dsimp [half]; omega)
    (by rw [hc]; exact Nat.pos_of_ne_zero (NeZero.ne p)) D
    (fun A _ => by
      rw [hc]
      refine exceptional_card_section5 (A+w.1) w.2.1 w.2.2 hk0 (exp_pos _).le ?_ hfit
      rw [hr,le_div_iff₀ (Nat.cast_pos.mpr hk0)]
      exact (mul_le_mul_of_nonneg_right (by norm_num : (0.099:ℝ) ≤ 0.0999) (Nat.cast_nonneg _)).trans
        (numerical (p:=p) hk (Nat.lt_succ_sqrt' p)).2.1)
    (by apply base_bound.trans; apply Real.exp_le_one_iff.mpr; linarith only [spec.active i hi])
  have heq : hits w = fun q => (0.24:ℝ)*p.sqrt ≤ (q.2 ∩ D q.1).card := rfl
  rw [heq]
  simpa only [hs,hitBound,hitBase] using hb

end
end Green39.Assembly

end AssemblyBounds

/- Source: one-percent-formal/assembly/AssemblyProbability.lean -/
section AssemblyProbability

/- Pushforward and finite union estimates for the cover event. -/

open Finset Real Filter Topology
open scoped Pointwise Classical
namespace Green39.Assembly
noncomputable section

variable {p : ℕ} [NeZero p]
open Split Concentration

theorem prob_or {α} (S : Finset α) (E F : α → Prop) :
    probability S (fun a => E a ∨ F a) ≤ probability S E + probability S F := by
  classical
  unfold probability
  rw [← add_div, ← Nat.cast_add]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr
  apply (card_le_card ?_).trans (card_union_le _ _)
  intro a ha
  simp only [mem_filter] at ha
  obtain ⟨h,h₁|h₂⟩ := ha
  · exact mem_union_left _ (mem_filter.mpr ⟨h,h₁⟩)
  · exact mem_union_right _ (mem_filter.mpr ⟨h,h₂⟩)

/-- Exact pushforward of the disjoint-pair law to the uniform union slice. -/
theorem union_law (E : Points p → Prop) :
    probability (space p) (fun q => E (q.1 ∪ q.2)) =
      sliceProbability (univ : Points p) p.sqrt E := by
  classical
  rw [probability_eq_mean_union]
  have hsum : half p.sqrt + rest p.sqrt = p.sqrt := by dsimp [half,rest]; omega
  rw [hsum]
  let D := (univ : Points p).powersetCard p.sqrt
  have hfib (A : Points p) (hA : A ∈ D) :
      sliceProbability A (half p.sqrt) (fun B => E (B ∪ (A \ B))) = if E A then 1 else 0 := by
    have ha := (mem_powersetCard.mp hA).2
    have hn : (A.powersetCard (half p.sqrt)).Nonempty :=
      powersetCard_nonempty.mpr (ha ▸ Nat.div_le_self _ _)
    have hfilter : (A.powersetCard (half p.sqrt)).filter (fun B => E (B ∪ (A \ B))) =
        (A.powersetCard (half p.sqrt)).filter (fun _ => E A) := by
      ext B
      simp only [mem_filter]
      apply and_congr_right
      intro hB
      have hu : B ∪ (A \ B) = A := sup_sdiff_cancel_right (mem_powersetCard.mp hB).1
      rw [hu]
    unfold sliceProbability
    rw [hfilter]
    split_ifs with he
    · simp [he, Nat.choose_pos (show half p.sqrt ≤ A.card by rw [ha]; exact Nat.div_le_self _ _)|>.ne']
    · simp [he]
  unfold mean
  change (∑ A ∈ D, sliceProbability A (half p.sqrt) (fun B => E (B ∪ (A \ B)))) / D.card = ((D.filter E).card:ℝ)/D.card
  rw [sum_congr rfl hfib, ← sum_filter]
  simp [D]

theorem hit_union {C : Catalog p} (spec : StageSpec C) (hk : 100000 ≤ p.sqrt) :
    probability (space p) (hitBad C) ≤
      (∑ i ∈ range C.stages, ((C.containers i).card:ℝ) * (C.laws i).card) *
        exp (-468*(p.sqrt:ℝ)) := by
  classical
  have h0 := probability_exists_le_sum (space p) (range C.stages)
    (fun i q => ∃ w ∈ witnesses C i, hits w q)
  simp only [mem_range] at h0
  apply h0.trans
  rw [sum_mul]
  apply sum_le_sum
  intro i hi
  have hi' := mem_range.mp hi
  have h1 := probability_exists_le_sum (space p) (witnesses C i) hits
  apply h1.trans
  calc
    _ ≤ ∑ _ ∈ witnesses C i, hitBound p.sqrt (x p i) :=
      sum_le_sum fun w hw => witness_probability spec hi' hk hw
    _ = _ := by rw [sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (count_witnesses spec hi') (by unfold hitBound hitBase; positivity)
    _ ≤ _ := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left (paid_witnesses _ ((by norm_num : (0:ℝ) ≤ 5000).trans (spec.active _ hi').le)) (by positivity)

def allLaws (C : Catalog p) := (range C.stages).biUnion C.laws

theorem smooth_union (C : Catalog p) (b : ℝ)
    (hb : ∀ μ ∈ allLaws C, probability (space p) (fun q => ¬ typical μ q) ≤ b) :
    probability (space p) (smoothBad C) ≤ ((allLaws C).card:ℝ)*b := by
  have hu := probability_exists_le_sum (space p) (allLaws C) (fun μ q => ¬typical μ q)
  calc
    _ ≤ probability (space p) (fun q => ∃ μ ∈ allLaws C, ¬typical μ q) := by
      apply probability_mono
      rintro q _ ⟨i,hi,μ,hμ,h⟩
      exact ⟨μ,mem_biUnion.mpr ⟨i,mem_range.mpr hi,hμ⟩,h⟩
    _ ≤ _ := hu.trans (by rw [← nsmul_eq_mul, ← sum_const]; exact sum_le_sum hb)

theorem cover_upper {C : Catalog p} (spec : StageSpec C) (hk : 100000 ≤ p.sqrt)
    (hsparse : ∀ i < C.stages, 8*log (4*(p:ℝ)) < (sMax p.sqrt:ℝ)*eta (x p i)^2)
    (b : ℝ) (hb : ∀ μ ∈ allLaws C, probability (space p) (fun q => ¬typical μ q) ≤ b) :
    sliceProbability (univ : Points p) p.sqrt (cover p) ≤
      2*p*exp (-(p.sqrt:ℝ)/200000000) +
      sliceProbability (univ : Points p) p.sqrt (fun A => ¬terminalOK C A) +
      ((allLaws C).card:ℝ)*b +
      (∑ i ∈ range C.stages, ((C.containers i).card:ℝ)*(C.laws i).card)*exp (-468*(p.sqrt:ℝ)) := by
  rw [← union_law, ← union_law (fun A => ¬terminalOK C A)]
  have hm := probability_mono (fun q hq hc => witness_inclusion spec hk hsparse hq hc)
  have ho := prob_or (space p) CanonicalBalanceFailure (fun q => ¬terminalOK C (q.1 ∪ q.2) ∨ smoothBad C q ∨ hitBad C q)
  have ht := prob_or (space p) (fun q => ¬terminalOK C (q.1 ∪ q.2)) (fun q => smoothBad C q ∨ hitBad C q)
  have hs := prob_or (space p) (smoothBad C) (hitBad C)
  have hbal := canonical_balance_failure_bound (p:=p) (k:=p.sqrt) (by omega)
  linarith only [hm,ho,ht,hs,hbal,smooth_union C b hb,hit_union spec hk]

end
end Green39.Assembly

end AssemblyProbability

/- Source: one-percent-formal/sparsify/SparsificationRates.lean -/
section SparsificationRates

/-
# The sample cap and tolerance in Green 39, Section 5

The constants are those of the review: the cap is the floor of `0.001 k`,
and the tolerance is `exp (-1000 - 0.22 x)` as in `Constants.lean`.
Every level has `x ≤ log (p / k)`.
-/

open Filter


namespace OnePercent.Fourier

noncomputable section

/-- The maximum number of centers kept from the fitted piece. -/
def sparsificationCap (k : ℕ) : ℕ := k / 1000

/-- Natural division gives the floor used for the sample cap in the review. -/
theorem sparsificationCap_eq_floor (k : ℕ) :
    sparsificationCap k = ⌊(0.001 : ℝ) * k⌋₊ := by
  rw [show (0.001 : ℝ) * k = (k : ℝ) / 1000 by ring]
  exact (Nat.floor_div_eq_div k 1000).symm

/-- The fitting tolerance at level `x`. -/
def sparsificationEta (x : ℝ) : ℝ := Real.exp (-1000 - 0.22 * x)

/-- The rate `k^0.56` is uniform over levels up to `log (2k)`. -/
theorem sparsification_scale_lower {k : ℕ} (hk : 2000 ≤ k) {x : ℝ}
    (hx : x ≤ Real.log (2 * (k : ℝ))) :
    Real.exp (-2000) / 4000 * (k : ℝ) ^ (0.56 : ℝ) ≤
      (sparsificationCap k : ℝ) * sparsificationEta x ^ 2 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkcap : (k : ℝ) / 2000 ≤ (sparsificationCap k : ℝ) := by
    have h : k ≤ 2000 * (k / 1000) := by omega
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2000), mul_comm]
    exact_mod_cast h
  have htwo : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-0.44 : ℝ) := by
    calc
      (1 / 2 : ℝ) = (2 : ℝ) ^ (-(1 : ℝ)) := by
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_one, one_div]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have heta : Real.exp (-2000) * ((1 / 2 : ℝ) * (k : ℝ) ^ (-0.44 : ℝ)) ≤
      sparsificationEta x ^ 2 := by
    calc
      _ ≤ Real.exp (-2000) * ((2 : ℝ) ^ (-0.44 : ℝ) * (k : ℝ) ^ (-0.44 : ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right htwo (by positivity))
          (Real.exp_nonneg _)
      _ = Real.exp (-2000 - 0.44 * Real.log (2 * (k : ℝ))) := by
        rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hkpos.le,
          Real.rpow_def_of_pos (mul_pos (by norm_num) hkpos), ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp ((-1000 - 0.22 * x) + (-1000 - 0.22 * x)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [sparsificationEta, sq, Real.exp_add]
  calc
    _ = ((k : ℝ) / 2000) *
        (Real.exp (-2000) * ((1 / 2 : ℝ) * (k : ℝ) ^ (-0.44 : ℝ))) := by
      rw [show (0.56 : ℝ) = 1 + (-0.44) by norm_num, Real.rpow_add hkpos, Real.rpow_one]
      ring
    _ ≤ _ := mul_le_mul hkcap heta (by positivity) (Nat.cast_nonneg _)

/-- For every fixed multiple of `log (4p)`, the sample scale eventually exceeds
that multiple uniformly in the level, when `p ≤ 2 k²`. -/
theorem sparsification_scale_eventually (M : ℝ) (hM : 0 ≤ M) :
    ∀ᶠ k : ℕ in atTop, ∀ p : ℕ, 0 < p → (p : ℝ) ≤ 2 * (k : ℝ) ^ 2 →
      ∀ x : ℝ, x ≤ Real.log ((p : ℝ) / k) →
        M * Real.log (4 * (p : ℝ)) < (sparsificationCap k : ℝ) * sparsificationEta x ^ 2 := by
  let c := Real.exp (-2000) / 4000
  have hc : 0 < c := by dsimp [c]; positivity
  have hDen : 0 < 5 * (M + 1) := by linarith
  have hsmall := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 0.56)).bound
    (div_pos hc hDen)
  have hnat := tendsto_natCast_atTop_atTop.eventually hsmall
  filter_upwards [eventually_ge_atTop (2000 : ℕ), hnat] with k hk hlog p hp hpUpper x hx
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
  have hkpos : (0 : ℝ) < k := by linarith
  have hLogPos : 0 < Real.log (k : ℝ) := Real.log_pos (by linarith)
  have hLogp : Real.log (4 * (p : ℝ)) ≤ 5 * Real.log (k : ℝ) := by
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp
    calc
      _ ≤ Real.log (8 * (k : ℝ) ^ 2) := Real.log_le_log (by positivity) (by linarith)
      _ = 3 * Real.log (2 : ℝ) + 2 * Real.log (k : ℝ) := by
        rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_mul (by norm_num)
          (pow_ne_zero _ hkpos.ne'), Real.log_pow, Real.log_pow]
        norm_num
      _ ≤ _ := by linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hk2]
  have hxUpper : x ≤ Real.log (2 * (k : ℝ)) := by
    refine hx.trans (Real.log_le_log (div_pos (by exact_mod_cast hp) hkpos) ?_)
    rw [div_le_iff₀ hkpos]
    nlinarith only [hpUpper]
  change ‖Real.log (k : ℝ)‖ ≤ c / (5 * (M + 1)) * ‖(k : ℝ) ^ (0.56 : ℝ)‖ at hlog
  rw [Real.norm_of_nonneg hLogPos.le, Real.norm_of_nonneg (by positivity),
    div_mul_eq_mul_div, le_div_iff₀ hDen] at hlog
  calc
    _ ≤ M * (5 * Real.log (k : ℝ)) := mul_le_mul_of_nonneg_left hLogp hM
    _ < Real.log (k : ℝ) * (5 * (M + 1)) := by nlinarith only [hLogPos]
    _ ≤ c * (k : ℝ) ^ (0.56 : ℝ) := hlog
    _ ≤ _ := sparsification_scale_lower hk hxUpper

/-- In the paper, `k = ⌊√p⌋`. The scale dominates every fixed multiple of the
logarithm as `p → ∞`, uniformly over all levels. -/
theorem sparsification_scale_eventually_sqrt (M : ℝ) (hM : 0 ≤ M) :
    ∀ᶠ p : ℕ in atTop, ∀ x : ℝ, x ≤ Real.log ((p : ℝ) / p.sqrt) →
      M * Real.log (4 * (p : ℝ)) <
        (sparsificationCap p.sqrt : ℝ) * sparsificationEta x ^ 2 := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp (sparsification_scale_eventually M hM)
  have hthreshold : ∀ᶠ p : ℕ in atTop, (max K 3) ^ 2 ≤ p := eventually_ge_atTop _
  filter_upwards [hthreshold] with p hp x hx
  have hsqrt := Nat.le_sqrt'.mpr hp
  have h3 : 3 ≤ p.sqrt := (le_max_right K 3).trans hsqrt
  have hp2 : p ≤ 2 * p.sqrt ^ 2 := by
    have hnext := Nat.lt_succ_sqrt' p
    rw [Nat.succ_eq_add_one] at hnext
    nlinarith [Nat.mul_le_mul_left p.sqrt h3]
  have hpPos : 0 < p := Nat.sqrt_pos.mp (by omega)
  exact hK p.sqrt ((le_max_left K 3).trans hsqrt) p hpPos (by exact_mod_cast hp2) x hx

/-- Equation (5) holds uniformly over all active levels for sufficiently large
moduli, with the paper's cap and tolerance. -/
theorem exists_fourierFit_sparsify_eventually :
    ∀ᶠ p : ℕ in atTop, ∀ [NeZero p], ∀ x : ℝ, x ≤ Real.log ((p : ℝ) / p.sqrt) →
      ∀ (F : Finset (ZMod p)) (μ : ZMod p → ℝ),
        FourierFit F μ (5 * sparsificationEta x * F.card) →
        ∃ S ⊆ F, S.card = min F.card (sparsificationCap p.sqrt) ∧
          FourierFit S μ (7 * sparsificationEta x * S.card) := by
  filter_upwards [sparsification_scale_eventually_sqrt 8 (by norm_num)] with p hp
  intro _ x hx F μ hfit
  exact exists_fourierFit_sparsify F μ _ (Real.exp_nonneg _) hfit (fun _ _ ↦ hp x hx)

end

end OnePercent.Fourier

end SparsificationRates

/- Source: one-percent-formal/terminal/TerminalRates.lean -/
section TerminalRates

/-
# Uniform rates for terminal containers

A product of descending-factorial ratios gives both a uniform lower bound
for the hole density and the containment estimate for regularity.
-/

open Finset
open scoped BigOperators Classical

namespace Green39.Terminal

noncomputable section

private theorem choose_div_choose_eq_prod (a b r : ℕ) :
    (a.choose r : ℝ) / (b.choose r : ℝ) =
      ∏ i ∈ range r, (((a - i : ℕ) : ℝ) / ((b - i : ℕ) : ℝ)) := by
  rw [prod_div_distrib, ← Nat.cast_prod, ← Nat.cast_prod,
    ← Nat.descFactorial_eq_prod_range, ← Nat.descFactorial_eq_prod_range,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  exact (mul_div_mul_left _ _ (by exact_mod_cast (Nat.factorial_pos r).ne')).symm

private theorem contain_ratio_le_pow {p k r : ℕ} (hkp : k ≤ p) (hr : r ≤ k) :
    (((p - r).choose (k - r) : ℕ) : ℝ) / (p.choose k : ℝ) ≤ ((k : ℝ) / p) ^ r := by
  have hpos : 0 < (p.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hkp
  have hpos' : 0 < (p.choose r : ℝ) := by exact_mod_cast Nat.choose_pos (hr.trans hkp)
  have heq : (((p - r).choose (k - r) : ℕ) : ℝ) / (p.choose k : ℝ) =
      (k.choose r : ℝ) / (p.choose r : ℝ) := by
    apply (div_eq_div_iff hpos.ne' hpos'.ne').mpr
    have h := Nat.choose_mul (n := p) hr
    exact_mod_cast (by simpa only [mul_comm] using h.symm :
      (p - r).choose (k - r) * p.choose r = k.choose r * p.choose k)
  rw [heq, choose_div_choose_eq_prod k p r, ← show
    (∏ _i ∈ range r, (k : ℝ) / p) = ((k : ℝ) / p) ^ r by rw [prod_const, card_range]]
  refine prod_le_prod (fun i _ ↦ by positivity) fun i hi ↦ ?_
  have hi' : i < r := by simpa only [card_range, mem_range] using hi
  have hki : i ≤ k := hi'.le.trans hr
  have hpi : i < p := hi'.trans_le (hr.trans hkp)
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Nat.zero_le i).trans_lt hpi
  have hpi' : 0 < ((p - i : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hpi
  have hkpr : (k : ℝ) ≤ p := by exact_mod_cast hkp
  have h := mul_nonneg (Nat.cast_nonneg i : 0 ≤ (i : ℝ)) (sub_nonneg.mpr hkpr)
  apply (div_le_div_iff₀ hpi' hp).mpr
  rw [Nat.cast_sub hki, Nat.cast_sub hpi.le]
  nlinarith

/-- A usable exponential version of the exact regularity bound. -/
theorem irregularBound_le_exp {p k m L : ℕ} {M : ℝ}
    (hkp : k ≤ p) (hr : L + 1 ≤ k)
    (hm : (m : ℝ) * ((k : ℝ) / p) ≤ M) :
    irregularBound p k m L ≤
      (p : ℝ) * Real.exp (2 * M - ((L + 1 : ℕ) : ℝ) * Real.log 2) := by
  let r := L + 1
  let q : ℝ := (k : ℝ) / p
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hbin : (m.choose r : ℝ) * (2 * q) ^ r ≤ Real.exp (2 * M) := by
    by_cases hm' : r ≤ m
    swap
    · simp [Nat.choose_eq_zero_of_lt (lt_of_not_ge hm'), Real.exp_nonneg]
    calc
      _ ≤ (2 * q + 1) ^ m := by
        rw [add_pow]
        have hm'' : r ∈ range (m + 1) := mem_range.mpr (Nat.lt_succ_of_le hm')
        simpa only [one_pow, mul_one, one_mul, mul_comm] using
          (single_le_sum (f := fun i ↦ (2 * q) ^ i * 1 ^ (m - i) * (m.choose i : ℝ))
            (fun i _ ↦ by positivity) hm'')
      _ ≤ (Real.exp (2 * q)) ^ m :=
        pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp _) _
      _ = Real.exp (2 * ((m : ℝ) * q)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hr2 : 0 < (2 : ℝ) ^ r := by positivity
  have hb : (m.choose r : ℝ) * q ^ r ≤ Real.exp (2 * M - (r : ℝ) * Real.log 2) := by
    rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    apply (le_div_iff₀ hr2).mpr
    rw [mul_pow] at hbin
    simpa only [mul_left_comm, mul_assoc, mul_comm] using hbin
  calc
    _ = (p : ℝ) * ((m.choose r : ℝ) * (((p - r).choose (k - r) : ℝ) / p.choose k)) := by
      dsimp [irregularBound, r]
      ring
    _ ≤ (p : ℝ) * ((m.choose r : ℝ) * q ^ r) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (contain_ratio_le_pow hkp hr) (Nat.cast_nonneg _))
        (Nat.cast_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)

private theorem exp_neg_twice_le_one_sub {y : ℝ} (hy : 0 ≤ y) (hy' : y ≤ 1 / 2) :
    Real.exp (-2 * y) ≤ 1 - y := by
  have hpos : 0 < 1 - y := by linarith
  apply (Real.le_log_iff_exp_le hpos).mp
  refine le_trans ?_ (Real.one_sub_inv_le_log_of_pos hpos)
  rw [inv_eq_one_div]
  have h : 1 / (1 - y) ≤ 1 + 2 * y := by
    apply (div_le_iff₀ hpos).mpr
    nlinarith [mul_nonneg hy (show 0 ≤ 1 - 2 * y by linarith)]
  linarith

/-- If «k + m ≤ p/2», the hole density has a uniform positive lower bound
in terms of «m*k/p». -/
theorem choose_avoidance_ge_exp {p k m : ℕ} (hp : 0 < p) (hkm : 2 * (k + m) ≤ p) :
    Real.exp (-4 * ((m : ℝ) * k / p)) ≤ (p - m).choose k / (p.choose k : ℝ) := by
  have hpr : 0 < (p : ℝ) := by exact_mod_cast hp
  have hkp : k ≤ p := by omega
  rw [choose_div_choose_eq_prod (p - m) p k]
  calc
    _ = (Real.exp (-4 * ((m : ℝ) / p))) ^ k := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ = ∏ _i ∈ range k, Real.exp (-4 * ((m : ℝ) / p)) := by rw [prod_const, card_range]
    _ ≤ _ := by
      refine prod_le_prod (fun i _ ↦ Real.exp_nonneg _) fun i hi ↦ ?_
      have hi' := mem_range.mp hi
      have hip : i < p := hi'.trans_le hkp
      have hmip : m + i ≤ p := by omega
      have hpi : 0 < ((p : ℝ) - i) := sub_pos.mpr (by exact_mod_cast hip)
      have hhalf : (p : ℝ) / 2 ≤ (p : ℝ) - i := by
        have h : 2 * i ≤ p := by omega
        have hh : (2 : ℝ) * i ≤ p := by exact_mod_cast h
        linarith
      have hmhalf : (m : ℝ) / ((p : ℝ) - i) ≤ 1 / 2 := by
        apply (div_le_iff₀ hpi).mpr
        have h : 2 * m + i ≤ p := by omega
        have hh : (2 : ℝ) * m + i ≤ p := by exact_mod_cast h
        linarith
      have hmfrac : (m : ℝ) / ((p : ℝ) - i) ≤ 2 * ((m : ℝ) / p) := by
        apply (div_le_iff₀ hpi).mpr
        have h := mul_le_mul_of_nonneg_left hhalf
          (show 0 ≤ 2 * ((m : ℝ) / p) by positivity)
        have he : 2 * ((m : ℝ) / p) * ((p : ℝ) / 2) = m := by field_simp
        rwa [he] at h
      calc
        _ ≤ Real.exp (-2 * ((m : ℝ) / ((p : ℝ) - i))) := Real.exp_le_exp.mpr (by linarith)
        _ ≤ 1 - (m : ℝ) / ((p : ℝ) - i) :=
          exp_neg_twice_le_one_sub (div_nonneg (Nat.cast_nonneg _) hpi.le) hmhalf
        _ = _ := by
          rw [Nat.cast_sub (show i ≤ p - m by omega), Nat.cast_sub (show m ≤ p by omega),
            Nat.cast_sub hip.le]
          field_simp
          ring

end

end Green39.Terminal

end TerminalRates

/- Source: one-percent-formal/terminal/TerminalUniform.lean -/
section TerminalUniform

/-
# A uniform bound for bounded-size terminal containers

With «k = floor sqrt p», use «L = floor sqrt (floor sqrt k)». With
«x = L + 1», the resulting bound is a constant times «x^8 exp(-a*x)»,
uniformly over all prescribed containers of size at most «M*k».
-/

open Finset
open scoped BigOperators Classical

namespace Green39.Terminal

noncomputable section

/-- The size parameter for the uniform exponential bound. -/
def scale (p : ℕ) : ℕ := (Nat.sqrt p).sqrt.sqrt + 1

theorem modulus_le_scale_pow (p : ℕ) : p ≤ (scale p) ^ 8 := by
  let k := p.sqrt
  let L := k.sqrt.sqrt
  have h₁ : p < (k + 1) ^ 2 := Nat.lt_succ_sqrt' p
  have h₂ : k < (k.sqrt + 1) ^ 2 := Nat.lt_succ_sqrt' k
  have h₃ : k.sqrt + 1 ≤ (L + 1) ^ 2 := Nat.lt_succ_sqrt' k.sqrt
  have h₄ : k + 1 ≤ (L + 1) ^ 4 := by
    calc
      _ ≤ (k.sqrt + 1) ^ 2 := h₂
      _ ≤ ((L + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left h₃ _
      _ = _ := by ring
  calc
    _ ≤ (k + 1) ^ 2 := h₁.le
    _ ≤ ((L + 1) ^ 4) ^ 2 := Nat.pow_le_pow_left h₄ _
    _ = _ := by unfold scale; change _ = (L + 1) ^ 8; ring

private theorem scale_le_k_and_cube (p : ℕ) (hk : 1 < p.sqrt) :
    scale p ≤ p.sqrt ∧ scale p ^ 3 ≤ 8 * p.sqrt := by
  let k := p.sqrt
  let L := k.sqrt.sqrt
  have hL : L ≤ k.sqrt := Nat.sqrt_le_self _
  have hL0 : 1 ≤ L := by
    have hh : 1 ≤ k.sqrt := Nat.le_sqrt.mpr (by omega)
    exact Nat.le_sqrt.mpr (by simpa using hh)
  have hpow : L ^ 4 ≤ k := by
    calc
      _ = (L ^ 2) ^ 2 := by ring
      _ ≤ k.sqrt ^ 2 := Nat.pow_le_pow_left (Nat.sqrt_le' k.sqrt) _
      _ ≤ k := Nat.sqrt_le' k
  change L + 1 ≤ k ∧ (L + 1) ^ 3 ≤ 8 * k
  constructor
  · have hks : k.sqrt < k := Nat.sqrt_lt_self hk
    exact Nat.succ_le_of_lt (hL.trans_lt hks)
  · calc
      _ ≤ (2 * L) ^ 3 := Nat.pow_le_pow_left (by omega) _
      _ = 8 * L ^ 3 := by ring
      _ ≤ 8 * L ^ 4 := by
        apply Nat.mul_le_mul_left
        calc
          _ = L ^ 3 * 1 := (Nat.mul_one _).symm
          _ ≤ L ^ 3 * L := Nat.mul_le_mul_left _ hL0
          _ = L ^ 4 := (pow_succ L 3).symm
      _ ≤ _ := Nat.mul_le_mul_left _ hpow

/-- A uniform lower bound for the density of holes. -/
def densityLower (M : ℝ) : ℝ := Real.exp (-4 * M)

/-- Decay rate for the three failure terms. -/
def decay (M δ : ℝ) : ℝ :=
  min (Real.log 2) ((δ * densityLower M) ^ 2 / (256 * (max 1 M) ^ 2))

theorem decay_pos (M : ℝ) {δ : ℝ} (hδ : 0 < δ) : 0 < decay M δ := by
  unfold decay densityLower
  have hB : 0 < max 1 M := zero_lt_one.trans_le (le_max_left _ _)
  have hA := mul_pos hδ (Real.exp_pos (-4 * M))
  exact lt_min (Real.log_pos (by norm_num)) (by positivity)

/-- Uniform probability bound as a function of the scale. -/
def uniformBound (M δ x : ℝ) : ℝ :=
  (Real.exp (2 * M) + 2) * x ^ 8 * Real.exp (-decay M δ * x)

theorem uniformBound_nonneg (M δ x : ℝ) : 0 ≤ uniformBound M δ x := by
  unfold uniformBound
  positivity

private theorem uniform_parameters {p m : ℕ} {M δ : ℝ}
    (hM : 0 ≤ M) (hδ : 0 < δ)
    (hk : 1 < p.sqrt) (hsize : (m : ℝ) ≤ M * (p.sqrt : ℝ))
    (hlarge : 2 * (1 + M) ≤ (p.sqrt : ℝ))
    (hlarge' : 4 * M / δ ≤ (p.sqrt : ℝ))
    (hsmall : uniformBound M δ (scale p) ≤ δ * densityLower M / 4) :
    let k := p.sqrt
    let L := k.sqrt.sqrt
    let u := δ * densityLower M * (k : ℝ) / 4
    0 < rho p k m ∧
    scoreMean p k m + (k : ℝ) * irregularBound p k m L + u ≤ (1 + δ) * k * rho p k m ∧
    failureBound p k m L δ u ≤ uniformBound M δ (scale p) := by
  let k := p.sqrt
  let L := k.sqrt.sqrt
  let x : ℝ := scale p
  let B : ℝ := max 1 M
  let a := δ * densityLower M
  let c := decay M δ
  let u := a * (k : ℝ) / 4
  change 0 < rho p k m ∧
    scoreMean p k m + (k : ℝ) * irregularBound p k m L + u ≤ (1 + δ) * k * rho p k m ∧
    failureBound p k m L δ u ≤ uniformBound M δ x
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hk1 : 1 ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
  have hp : 0 < p := (show 0 < k by omega).trans_le (Nat.sqrt_le_self p)
  have hpr : 0 < (p : ℝ) := by exact_mod_cast hp
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  have ha : 0 < a := mul_pos hδ (Real.exp_pos _)
  have hc : 0 < c := decay_pos M hδ
  have hx : 0 < x := by dsimp [x, scale]; positivity
  have hxk : x ≤ k := Nat.cast_le.mpr (scale_le_k_and_cube p hk).1
  have hxcube : x ^ 3 ≤ 8 * (k : ℝ) := by
    dsimp only [x, k]
    exact_mod_cast (scale_le_k_and_cube p hk).2
  have hpx : (p : ℝ) ≤ x ^ 8 := by
    dsimp only [x]
    exact_mod_cast modulus_le_scale_pow p
  have hk2 : (k : ℝ) ^ 2 ≤ p := by exact_mod_cast Nat.sqrt_le' p
  have hkm : 2 * (k + m) ≤ p := by
    have h₁ : (2 : ℝ) * ((k : ℝ) + m) ≤ (2 * (1 + M)) * k := by linarith
    have h₂ := mul_le_mul_of_nonneg_right hlarge hkpos.le
    have hh : (2 : ℝ) * ((k : ℝ) + m) ≤ p := by nlinarith
    exact_mod_cast hh
  have hmp : (m : ℝ) * k / p ≤ M := by
    apply (div_le_iff₀ hpr).mpr
    have h₁ := mul_le_mul_of_nonneg_right hsize hkpos.le
    have h₂ := mul_le_mul_of_nonneg_left hk2 hM
    nlinarith
  have hrho : densityLower M ≤ rho p k m :=
    (Real.exp_le_exp.mpr (by linarith)).trans (choose_avoidance_ge_exp hp hkm)
  have hrhopos : 0 < rho p k m := (Real.exp_pos (-4 * M)).trans_le hrho
  have hQ : irregularBound p k m L ≤
      (p : ℝ) * Real.exp (2 * M) * Real.exp (-c * x) := by
    have h := irregularBound_le_exp (p := p) (k := k) (m := m) (L := L) (M := M)
      (Nat.sqrt_le_self p) (scale_le_k_and_cube p hk).1 (by rwa [← mul_div_assoc])
    refine h.trans ?_
    rw [sub_eq_add_neg, Real.exp_add, ← mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have hcLog : c ≤ Real.log 2 := min_le_left _ _
    have hh := mul_le_mul_of_nonneg_right hcLog hx.le
    change -(x * Real.log 2) ≤ -c * x
    linarith [mul_comm (Real.log 2) x]
  have hQsmall : irregularBound p k m L ≤ a / 4 := by
    refine hQ.trans (le_trans ?_ hsmall)
    unfold uniformBound
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    calc
      _ ≤ x ^ 8 * Real.exp (2 * M) := mul_le_mul_of_nonneg_right hpx (Real.exp_nonneg _)
      _ ≤ _ := by
        rw [mul_comm (Real.exp (2 * M) + 2)]
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hpm : m < p := by omega
  have hratio : (p : ℝ) / ((p : ℝ) - m) ≤ 1 + δ / 2 := by
    have h₁ : (4 : ℝ) * m ≤ δ * p := by
      have h₂ := (div_le_iff₀ hδ).mp hlarge'
      have h₃ := mul_le_mul_of_nonneg_right h₂ hkpos.le
      have h₄ := mul_le_mul_of_nonneg_left hk2 hδ.le
      nlinarith
    have h₂ : (2 : ℝ) * m ≤ p := by exact_mod_cast (show 2 * m ≤ p by omega)
    have h₃ := mul_le_mul_of_nonneg_left (show (p : ℝ) / 2 ≤ p - m by linarith)
      (show 0 ≤ δ / 2 by positivity)
    apply (div_le_iff₀ (sub_pos.mpr (by exact_mod_cast hpm))).mpr
    nlinarith
  have hmargin : scoreMean p k m + (k : ℝ) * irregularBound p k m L + u ≤
      (1 + δ) * (k : ℝ) * rho p k m := by
    rw [scoreMean_eq (show 0 < k by omega) hpm]
    have hmean := mul_le_mul_of_nonneg_left hratio (show 0 ≤ (k : ℝ) * rho p k m by positivity)
    have hQk := mul_le_mul_of_nonneg_left hQsmall hkpos.le
    have haρ : a ≤ δ * rho p k m := mul_le_mul_of_nonneg_left hrho hδ.le
    have haρk := mul_le_mul_of_nonneg_right haρ hkpos.le
    dsimp [u]
    nlinarith
  have hMax : max 1 (m : ℝ) ≤ B * (k : ℝ) := by
    apply max_le
    · exact le_trans hk1 (by simpa using (mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) M) hkpos.le))
    · exact hsize.trans (mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) M) hkpos.le)
  have hc₀ : c ≤ a ^ 2 / (256 * B ^ 2) := min_le_right _ _
  have hc₁ : c ≤ a ^ 2 / 256 := hc₀.trans (by
    have hB1 : 1 ≤ B := le_max_left _ _
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num)
    nlinarith [sq_nonneg (B - 1)])
  have hhole : c * x ≤ (δ * (p : ℝ) * rho p k m) ^ 2 /
      (2 * (k : ℝ) * (max 1 (m : ℝ)) ^ 2) := by
    have hc₂ : c ≤ a ^ 2 / (2 * B ^ 2) := hc₀.trans (by
      apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      nlinarith [sq_nonneg B])
    have ham : a * (k : ℝ) ^ 2 ≤ δ * (p : ℝ) * rho p k m := by
      calc
        _ ≤ a * (p : ℝ) := mul_le_mul_of_nonneg_left hk2 ha.le
        _ = δ * (p : ℝ) * densityLower M := by dsimp [a]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hrho (by positivity)
    have hmaxpos : 0 < max 1 (m : ℝ) := zero_lt_one.trans_le (le_max_left _ _)
    calc
      _ ≤ c * (k : ℝ) := mul_le_mul_of_nonneg_left hxk hc.le
      _ ≤ a ^ 2 / (2 * B ^ 2) * (k : ℝ) := mul_le_mul_of_nonneg_right hc₂ hkpos.le
      _ = (a * (k : ℝ) ^ 2) ^ 2 / (2 * (k : ℝ) * (B * (k : ℝ)) ^ 2) := by
        field_simp
      _ ≤ _ := by gcongr
  have hscore : c * x ≤ u ^ 2 / (2 * (k : ℝ) * (1 + (L : ℝ)) ^ 2) := by
    have hxL : x = 1 + (L : ℝ) := by dsimp [x, scale, L, k]; push_cast; ring
    have hx' : x ≤ 8 * (k : ℝ) / x ^ 2 := (le_div_iff₀ (by positivity)).mpr
      (by calc x * x ^ 2 = x ^ 3 := by ring
               _ ≤ _ := hxcube)
    calc
      _ ≤ a ^ 2 / 256 * x := mul_le_mul_of_nonneg_right hc₁ hx.le
      _ ≤ a ^ 2 / 256 * (8 * (k : ℝ) / x ^ 2) :=
        mul_le_mul_of_nonneg_left hx' (by positivity)
      _ = _ := by
        rw [← hxL]
        dsimp [u]
        field_simp
        ring
  refine ⟨hrhopos, hmargin, ?_⟩
  have hH : Real.exp (-(δ * (p : ℝ) * rho p k m) ^ 2 /
      (2 * (k : ℝ) * (max 1 (m : ℝ)) ^ 2)) ≤ Real.exp (-c * x) := by
    simpa only [neg_div, neg_mul] using Real.exp_le_exp.mpr (neg_le_neg hhole)
  have hX : (p : ℝ) * Real.exp (-u ^ 2 / (2 * (k : ℝ) * (1 + (L : ℝ)) ^ 2)) ≤
      (p : ℝ) * Real.exp (-c * x) := by
    simpa only [neg_div, neg_mul] using
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hscore)) hpr.le
  calc
    _ ≤ (p : ℝ) * Real.exp (2 * M) * Real.exp (-c * x) +
        Real.exp (-c * x) + (p : ℝ) * Real.exp (-c * x) := add_le_add (add_le_add hQ hH) hX
    _ ≤ uniformBound M δ x := by
      unfold uniformBound
      change _ ≤ (Real.exp (2 * M) + 2) * x ^ 8 * Real.exp (-c * x)
      have hp1 : 1 ≤ (p : ℝ) := by exact_mod_cast hp
      have h₁ : (p : ℝ) * Real.exp (2 * M) ≤ x ^ 8 * Real.exp (2 * M) :=
        mul_le_mul_of_nonneg_right hpx (Real.exp_nonneg _)
      have h := mul_le_mul_of_nonneg_right (show (p : ℝ) * Real.exp (2 * M) + 1 + p ≤
        (Real.exp (2 * M) + 2) * x ^ 8 by linarith) (Real.exp_nonneg (-c * x))
      linarith

/-- The bound for a finite list with «|P| ≤ M*k» is uniform in the prescribed sets. -/
theorem probability_not_coversOutside_list_le_uniform {p : ℕ} [NeZero p]
    (Ps : Finset (Finset (ZMod p))) {M δ ζ : ℝ} (hM : 0 ≤ M) (hδ : 0 < δ)
    (hk : 1 < p.sqrt) (hsize : ∀ P ∈ Ps, (P.card : ℝ) ≤ M * (p.sqrt : ℝ))
    (hlarge : 2 * (1 + M) ≤ (p.sqrt : ℝ)) (hlarge' : 4 * M / δ ≤ (p.sqrt : ℝ))
    (hsmall : uniformBound M δ (scale p) ≤ δ * densityLower M / 4)
    (hζ : 1 - ζ ≤ (1 - δ) / (1 + δ)) :
    probability p p.sqrt (fun A ↦ ¬ ∀ P ∈ Ps, CoversOutside P p.sqrt ζ A) ≤
      (Ps.card : ℝ) * uniformBound M δ (scale p) := by
  let q := fun P hP ↦ uniform_parameters hM hδ hk (hsize P hP) hlarge hlarge' hsmall
  have hk' : 0 < p.sqrt := (Nat.zero_lt_one).trans hk
  refine (probability_not_coversOutside_list_le Ps p.sqrt.sqrt.sqrt hk' (Nat.sqrt_le_self p)
    hδ.le (by unfold densityLower; positivity) hζ (fun P hP ↦ (q P hP).1)
    (fun P hP ↦ (q P hP).2.1)).trans ?_
  calc
    _ ≤ ∑ _P ∈ Ps, uniformBound M δ (scale p) := sum_le_sum fun P hP ↦ (q P hP).2.2
    _ = _ := by rw [sum_const, nsmul_eq_mul]

end

end Green39.Terminal

end TerminalUniform

/- Source: one-percent-formal/terminal/TerminalLimit.lean -/
section TerminalLimit

/-
# Terminal-container restriction for polylogarithmic transcript lists

For any fixed size bound and any prescribed family whose logarithmic size
grows at most polylogarithmically, the simultaneous event in Section 1,
equation (1), has uniform-slice probability tending to one.
-/

open Filter Topology Asymptotics
open scoped BigOperators Classical

namespace Green39.Terminal

noncomputable section

private theorem tendsto_nat_sqrt : Tendsto Nat.sqrt atTop atTop :=
  tendsto_atTop.mpr fun b ↦ (eventually_ge_atTop (b * b)).mono fun _ h ↦ Nat.le_sqrt.mpr h

private theorem tendsto_scale : Tendsto (fun p : ℕ ↦ (scale p : ℝ)) atTop atTop := by
  apply (tendsto_natCast_atTop_atTop (R := ℝ)).comp
  have h := tendsto_nat_sqrt.comp (tendsto_nat_sqrt.comp tendsto_nat_sqrt)
  exact tendsto_atTop.mpr fun b ↦ (h.eventually_ge_atTop b).mono fun p hp ↦
    (show b ≤ p.sqrt.sqrt.sqrt from hp).trans (Nat.le_succ _)

private theorem tendsto_polynomial_exp (C : ℝ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ ↦ C * x ^ 8 * Real.exp (-a * x)) atTop (𝓝 0) := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((8 : ℕ) : ℝ) a ha
  simp only [Real.rpow_natCast] at h
  simpa only [mul_zero, mul_assoc] using h.const_mul C

/-- The simultaneous good event for (1), evaluated on an arbitrary cofinal
family of moduli. The family of prescribed sets may depend on the modulus. -/
theorem coversOutside_tendsto_one {ι : Type*} {l : Filter ι} (p : ι → ℕ)
    [∀ i, NeZero (p i)] (hp : Tendsto p l atTop)
    (Ps : (i : ι) → Finset (Finset (ZMod (p i)))) {M ζ C D : ℝ}
    (hM : 0 ≤ M) (hζ : 0 < ζ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hsize : ∀ᶠ i in l, ∀ P ∈ Ps i, (P.card : ℝ) ≤ M * ((p i).sqrt : ℝ))
    (hlist : ∀ᶠ i in l, Real.log (1 + ((Ps i).card : ℝ)) ≤ C * Real.log (p i : ℝ) ^ D) :
    Tendsto (fun i ↦ probability (p i) (p i).sqrt
      (fun A ↦ ∀ P ∈ Ps i, CoversOutside P (p i).sqrt ζ A)) l (𝓝 1) := by
  let δ := min (ζ / 2) (1 / 2)
  let a := decay M δ
  let x (i : ι) : ℝ := scale (p i)
  let k (i : ι) : ℕ := (p i).sqrt
  let E (i : ι) (A : Finset (ZMod (p i))) := ∀ P ∈ Ps i, CoversOutside P (k i) ζ A
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hratio : 1 - ζ ≤ (1 - δ) / (1 + δ) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have h := min_le_left (ζ / 2) (1 / 2 : ℝ)
    change δ ≤ ζ / 2 at h
    nlinarith [mul_nonneg hδ.le hζ.le]
  have ha : 0 < a := decay_pos M hδ
  have hx : Tendsto x l atTop := tendsto_scale.comp hp
  have hk : Tendsto k l atTop := tendsto_nat_sqrt.comp hp
  have hkr : Tendsto (fun i ↦ (k i : ℝ)) l atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp hk
  have hSmall : ∀ᶠ i in l, uniformBound M δ (x i) ≤ δ * densityLower M / 4 := by
    have hlim := (tendsto_polynomial_exp (Real.exp (2 * M) + 2) ha).comp hx
    have hc : 0 < δ * densityLower M / 4 := by unfold densityLower; positivity
    exact (hlim.eventually (Iio_mem_nhds hc)).mono fun i hi ↦ hi.le
  have hfinite : ∀ᶠ i in l, probability (p i) (k i) (fun A ↦ ¬ E i A) ≤
      ((Ps i).card : ℝ) * uniformBound M δ (x i) := by
    filter_upwards [hk.eventually_ge_atTop 2, hsize, hkr.eventually_ge_atTop (2 * (1 + M)),
      hkr.eventually_ge_atTop (4 * M / δ), hSmall] with i hi hs h₁ h₂ h₃
    exact probability_not_coversOutside_list_le_uniform (Ps i) hM hδ hi hs h₁ h₂ h₃ hratio
  have hlogLittle : (fun y : ℝ ↦ C * (8 : ℝ) ^ D * Real.log y ^ D) =o[atTop]
      (fun y : ℝ ↦ y) := by
    have h := (isLittleO_log_rpow_rpow_atTop D (s := 1) zero_lt_one).const_mul_left
      (C * (8 : ℝ) ^ D)
    simpa only [Real.rpow_one] using h
  have hlogUpper : ∀ᶠ i in l, Real.log (1 + ((Ps i).card : ℝ)) ≤ a * x i / 2 := by
    have hlo := hx.eventually (hlogLittle.def (show 0 < a / 2 by positivity))
    filter_upwards [hx.eventually_ge_atTop 1, hlo, hlist] with i hxi hl hi
    have hp1 : 1 ≤ (p i : ℝ) := by
      exact_mod_cast (show 1 ≤ p i from Nat.pos_of_ne_zero (NeZero.ne (p i)))
    have hpX : (p i : ℝ) ≤ x i ^ 8 := by
      dsimp only [x]
      exact_mod_cast modulus_le_scale_pow (p i)
    have hlog : Real.log (p i : ℝ) ≤ 8 * Real.log (x i) := by
      calc
        _ ≤ Real.log (x i ^ 8) := Real.log_le_log (zero_lt_one.trans_le hp1) hpX
        _ = _ := by norm_num [Real.log_pow]
    calc
      _ ≤ C * Real.log (p i : ℝ) ^ D := hi
      _ ≤ C * (8 * Real.log (x i)) ^ D :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Real.log_nonneg hp1) hlog hD) hC
      _ = C * (8 : ℝ) ^ D * Real.log (x i) ^ D := by
        rw [Real.mul_rpow (by norm_num) (Real.log_nonneg hxi), mul_assoc]
      _ ≤ _ := by
        have hxl : 0 ≤ x i := zero_le_one.trans hxi
        change ‖C * (8 : ℝ) ^ D * Real.log (x i) ^ D‖ ≤ (a / 2) * ‖x i‖ at hl
        rw [Real.norm_of_nonneg hxl] at hl
        have hh := (le_abs_self (C * (8 : ℝ) ^ D * Real.log (x i) ^ D)).trans
          (by simpa only [Real.norm_eq_abs] using hl)
        linarith
  have hcounts : ∀ᶠ i in l, ((Ps i).card : ℝ) ≤ Real.exp (a * x i / 2) :=
    hlogUpper.mono fun i hi ↦ by
      have hpos : 0 < 1 + ((Ps i).card : ℝ) := by positivity
      have h := (Real.log_le_iff_le_exp hpos).mp hi
      linarith
  have hlim : Tendsto (fun i ↦ (Real.exp (2 * M) + 2) * x i ^ 8 *
      Real.exp (-(a / 2) * x i)) l (𝓝 0) :=
    (tendsto_polynomial_exp _ (by positivity : 0 < a / 2)).comp hx
  have hfail : Tendsto (fun i ↦ probability (p i) (k i) (fun A ↦ ¬ E i A)) l (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    · exact Eventually.of_forall fun _ ↦ sliceProbability_nonneg _ _ _
    · filter_upwards [hfinite, hcounts] with i hfin hcount
      refine hfin.trans ((mul_le_mul_of_nonneg_right hcount (uniformBound_nonneg _ _ _)).trans_eq ?_)
      unfold uniformBound
      change Real.exp (a * x i / 2) *
          ((Real.exp (2 * M) + 2) * x i ^ 8 * Real.exp (-a * x i)) = _
      rw [show ∀ z w v : ℝ, z * (w * v) = w * (z * v) by intros; ring, ← Real.exp_add]
      congr 2
      ring
  have hsuccess : Tendsto (fun i ↦ 1 - probability (p i) (k i) (fun A ↦ ¬ E i A))
      l (𝓝 1) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hfail
  convert hsuccess using 1
  funext i
  have hki : k i ≤ (Finset.univ : Finset (ZMod (p i))).card := by
    simpa only [Finset.card_univ, ZMod.card] using Nat.sqrt_le_self (p i)
  change probability (p i) (k i) (E i) = 1 - probability (p i) (k i) (fun A ↦ ¬ E i A)
  exact eq_sub_of_add_eq (sliceProbability_add_compl _ hki (E i))

/-- Section 1, equation (1), along the primes. The probability is with
respect to the uniformly chosen «floor sqrt p»-element subset of «ZMod p». -/
theorem coversOutside_tendsto_one_primes
    (Ps : (p : {n : ℕ // n.Prime}) → Finset (Finset (ZMod p.val))) {M ζ C D : ℝ}
    (hM : 0 ≤ M) (hζ : 0 < ζ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hsize : ∀ᶠ p in atTop, ∀ P ∈ Ps p, (P.card : ℝ) ≤ M * (p.val.sqrt : ℝ))
    (hlist : ∀ᶠ p in atTop, Real.log (1 + ((Ps p).card : ℝ)) ≤ C * Real.log (p.val : ℝ) ^ D) :
    Tendsto (fun p : {n : ℕ // n.Prime} ↦
      letI : NeZero p.val := ⟨p.property.ne_zero⟩
      probability p.val p.val.sqrt (fun A ↦ ∀ P ∈ Ps p, CoversOutside P p.val.sqrt ζ A))
      atTop (𝓝 1) := by
  have hp : Tendsto (fun p : {n : ℕ // n.Prime} ↦ p.val) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    obtain ⟨q, hq, hprime⟩ := Nat.exists_infinite_primes b
    exact (eventually_ge_atTop (⟨q, hprime⟩ : {n : ℕ // n.Prime})).mono
      fun _ h ↦ hq.trans h
  exact @coversOutside_tendsto_one _ _ (fun p : {n : ℕ // n.Prime} ↦ p.val)
    (fun p ↦ ⟨p.property.ne_zero⟩) hp Ps _ _ _ _ hM hζ hC hD hsize hlist

end

end Green39.Terminal

end TerminalLimit

/- Source: one-percent-formal/smooth-law/SliceWeights.lean -/
section SliceWeights

open scoped BigOperators Classical
open Green39.Concentration

namespace Green39.Smooth
noncomputable section
variable {α ι : Type*} [DecidableEq α]

def incProb (s : Finset α) (k : ℕ) (t : Finset α) : ℝ :=
  (((s.powersetCard k).filter (fun A ↦ t ⊆ A)).card : ℝ) / (s.powersetCard k).card

theorem inc_empty {s : Finset α} {k : ℕ} (hk : k ≤ s.card) :
    incProb s k ∅ = 1 := by
  simp [incProb, (Nat.choose_pos hk).ne']

private theorem count_insert (s t : Finset α) (k : ℕ) {x : α} (hx : x ∈ s) (ht : x ∉ t) :
    ((s.powersetCard (k+1)).filter (fun A ↦ insert x t ⊆ A)).card =
      (((s.erase x).powersetCard k).filter (fun A ↦ t ⊆ A)).card := by
  apply Finset.card_bij (fun A _ ↦ A.erase x)
  · intro A h
    obtain ⟨ha, hxt⟩ := Finset.mem_filter.mp h
    obtain ⟨hs, hc⟩ := Finset.mem_powersetCard.mp ha
    obtain ⟨hxA, htA⟩ := Finset.insert_subset_iff.mp hxt
    exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.erase_subset_erase x hs,
      by simp [Finset.card_erase_of_mem hxA, hc]⟩, fun y hy ↦
      Finset.mem_erase.mpr ⟨fun he ↦ ht (he ▸ hy), htA hy⟩⟩
  · intro A hA B hB he
    have hmem (C : Finset α) (hC : C ∈ (s.powersetCard (k+1)).filter (fun D ↦ insert x t ⊆ D)) :
        x ∈ C := (Finset.mem_filter.mp hC).2 (Finset.mem_insert_self _ _)
    simpa [Finset.insert_erase (hmem _ hA), Finset.insert_erase (hmem _ hB)] using
      congrArg (insert x) he
  · intro B hB
    obtain ⟨hb, htB⟩ := Finset.mem_filter.mp hB
    obtain ⟨hs, hc⟩ := Finset.mem_powersetCard.mp hb
    have hn : x ∉ B := fun h ↦ Finset.notMem_erase x s (hs h)
    exact ⟨insert x B, Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
      ⟨Finset.insert_subset_iff.mpr ⟨hx, hs.trans (Finset.erase_subset _ _)⟩,
       by simp [Finset.card_insert_of_notMem hn, hc]⟩, Finset.insert_subset_insert _ htB⟩,
      Finset.erase_insert hn⟩

theorem inc_insert {s t : Finset α} {k : ℕ} {x : α}
    (hk : k+1 ≤ s.card) (hx : x ∈ s) (ht : x ∉ t) :
    incProb s (k+1) (insert x t) =
      ((k+1 : ℕ) : ℝ) / s.card * incProb (s.erase x) k t := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero_of_mem hx)
  have hk' : k ≤ n := by omega
  have h : (n+1 : ℕ) * n.choose k = (n+1).choose (k+1) * (k+1) := Nat.add_one_mul_choose_eq n k
  unfold incProb
  rw [count_insert s t k hx ht, Finset.card_powersetCard, Finset.card_powersetCard,
    Finset.card_erase_of_mem hx, hn, Nat.succ_sub_one]
  have h' : ((n+1 : ℕ) : ℝ) * n.choose k = ((n+1).choose (k+1) : ℝ) * (k+1 : ℕ) := by exact_mod_cast h
  have h1 := Nat.choose_pos hk'
  have h2 := Nat.choose_pos (Nat.succ_le_succ hk')
  rw [div_mul_div_comm, div_eq_div_iff (by exact_mod_cast h2.ne') (by positivity)]
  push_cast at h' ⊢
  linear_combination (↑(((s.erase x).powersetCard k).filter (fun A ↦ t ⊆ A)).card : ℝ) * h'

theorem inc_singleton {s : Finset α} {k : ℕ} (hk : k ≤ s.card) {x : α} (hx : x ∈ s) :
    incProb s k {x} = (k : ℝ)/s.card := by
  cases k with
  | zero => simp [incProb, Finset.powersetCard_zero]
  | succ k =>
    rw [← Finset.insert_empty (a := x), inc_insert hk hx (Finset.notMem_empty _),
      inc_empty (by rw [Finset.card_erase_of_mem hx]; omega), mul_one]

/-- Joint inclusion probabilities are bounded by independent Bernoulli inclusion. -/
theorem inc_le_pow {s t : Finset α} {k : ℕ} (hk : k ≤ s.card) (ht : t ⊆ s) :
    incProb s k t ≤ ((k : ℝ)/s.card)^t.card := by
  induction t using Finset.induction_on generalizing s k with
  | empty => simp [inc_empty hk]
  | @insert x t hxt ih =>
    obtain ⟨hx, hts⟩ := Finset.insert_subset_iff.mp ht
    cases k with
    | zero => simp [incProb, Finset.powersetCard_zero]
    | succ k =>
      have hcard := Finset.card_erase_of_mem hx
      have hk' : k ≤ (s.erase x).card := by omega
      have hts' : t ⊆ s.erase x := fun y hy ↦ Finset.mem_erase.mpr
        ⟨fun he ↦ hxt (he ▸ hy), hts hy⟩
      have hratio : (k : ℝ)/(s.erase x).card ≤ ((k+1 : ℕ) : ℝ)/s.card := by
        by_cases he : (s.erase x).card = 0
        · simp [he]; positivity
        have hp : 0 < ((s.erase x).card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero he
        have hs : 0 < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨x,hx⟩
        have hsc : s.card = (s.erase x).card + 1 := by omega
        rw [div_le_div_iff₀ hp hs, hsc, Nat.cast_add, Nat.cast_one, Nat.cast_succ]
        have hk'' : (k : ℝ) ≤ (s.erase x).card := by exact_mod_cast hk'
        nlinarith
      rw [inc_insert hk hx hxt, Finset.card_insert_of_notMem hxt, pow_succ, mul_comm]
      exact mul_le_mul_of_nonneg_right ((ih hk' hts').trans (pow_le_pow_left₀
        (by positivity) hratio _)) (by positivity)

end
end Green39.Smooth

end SliceWeights

/- Source: one-percent-formal/smooth-law/SliceMoments.lean -/
section SliceMoments

open scoped BigOperators Classical
open Green39.Concentration

namespace Green39.Smooth
noncomputable section
variable {α ι : Type*} [DecidableEq α]

omit [DecidableEq α] in
theorem sm_congr {s : Finset α} {k : ℕ} {f g : Finset α → ℝ}
    (h : ∀ A ∈ s.powersetCard k, f A = g A) : sliceMean s k f = sliceMean s k g := by
  unfold sliceMean mean
  rw [Finset.sum_congr rfl h]

omit [DecidableEq α] in
theorem sm_mono {s : Finset α} {k : ℕ} {f g : Finset α → ℝ}
    (h : ∀ A ∈ s.powersetCard k, f A ≤ g A) : sliceMean s k f ≤ sliceMean s k g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum h) (by positivity)

omit [DecidableEq α] in
theorem sm_sum (s : Finset α) (k : ℕ) (d : Finset ι) (f : ι → Finset α → ℝ) :
    sliceMean s k (fun A ↦ ∑ i ∈ d, f i A) = ∑ i ∈ d, sliceMean s k (f i) := by
  unfold sliceMean mean
  rw [Finset.sum_comm, Finset.sum_div]

theorem sm_inc (s t : Finset α) (k : ℕ) (c : ℝ) :
    sliceMean s k (fun A ↦ if t ⊆ A then c else 0) = incProb s k t * c := by
  unfold sliceMean mean incProb
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  ring

theorem sm_const {s : Finset α} {k : ℕ} (hk : k ≤ s.card) (c : ℝ) :
    sliceMean s k (fun _ ↦ c) = c := by simpa [inc_empty hk] using sm_inc s ∅ k c

private theorem restrict_sum {A s : Finset α} (h : A ⊆ s) (f : α → ℝ) :
    ∑ x ∈ A, f x = ∑ x ∈ s, if x ∈ A then f x else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter]
  exact ⟨fun hx ↦ ⟨h hx, hx⟩, And.right⟩

theorem sm_weight {s : Finset α} {k : ℕ} (hk : k ≤ s.card) (w : α → ℝ) :
    sliceMean s k (fun A ↦ ∑ x ∈ A, w x) = ((k : ℝ)/s.card) * ∑ x ∈ s, w x := by
  calc
    _ = sliceMean s k (fun A ↦ ∑ x ∈ s, if {x} ⊆ A then w x else 0) := by
      apply sm_congr
      intro A hA
      simpa using restrict_sum (Finset.mem_powersetCard.mp hA).1 w
    _ = _ := by
      rw [sm_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x hx ↦ by rw [sm_inc, inc_singleton hk hx])

theorem sm_variance {s : Finset α} {k : ℕ} (hk : k ≤ s.card) (w : α → ℝ)
    (hw : ∀ x ∈ s, 0 ≤ w x) :
    sliceMean s k (fun A ↦ ((∑ x ∈ A, w x) - ((k : ℝ)/s.card) * ∑ x ∈ s, w x)^2)
      ≤ ((k : ℝ)/s.card) * ∑ x ∈ s, w x ^ 2 := by
  let q : ℝ := k / (s.card : ℝ)
  let m := q * ∑ x ∈ s, w x
  let X (A : Finset α) := ∑ x ∈ A, w x
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hsecond : sliceMean s k (fun A ↦ X A ^ 2) ≤
      q * (∑ x ∈ s, w x ^ 2) + m ^ 2 := by
    calc
      _ = sliceMean s k (fun A ↦ ∑ x ∈ s, ∑ y ∈ s,
          if {x,y} ⊆ A then w x * w y else 0) := by
        apply sm_congr
        intro A hA
        dsimp [X]
        rw [sq, restrict_sum (Finset.mem_powersetCard.mp hA).1 w, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;> simp [Finset.insert_subset_iff,hx,hy]
      _ = ∑ x ∈ s, ∑ y ∈ s, incProb s k {x,y} * (w x * w y) := by
        rw [sm_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [sm_sum]
        simp_rw [sm_inc]
      _ ≤ ∑ x ∈ s, ∑ y ∈ s, ((if x = y then q * w x ^ 2 else 0) +
          (q*w x)*(q*w y)) := by
        apply Finset.sum_le_sum
        intro x hx
        apply Finset.sum_le_sum
        intro y hy
        by_cases he : x = y
        · subst y
          rw [Finset.insert_eq_of_mem (Finset.mem_singleton_self x), inc_singleton hk hx, if_pos rfl]
          change q * _ ≤ _
          nlinarith [sq_nonneg (q * w x)]
        · have hxy : ({x,y} : Finset α) ⊆ s := by simp [Finset.insert_subset_iff,hx,hy]
          have hi := inc_le_pow hk hxy
          have hn : x ∉ ({y} : Finset α) := by simpa using he
          rw [Finset.card_insert_of_notMem hn, Finset.card_singleton] at hi
          rw [if_neg he, zero_add]
          calc
            _ ≤ q^2 * (w x*w y) := mul_le_mul_of_nonneg_right hi (mul_nonneg (hw _ hx) (hw _ hy))
            _ = _ := by ring
      _ = _ := by
        simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp [m, Finset.sum_ite_eq, ← Finset.sum_mul, ← Finset.mul_sum]
        ring
  have hmean : sliceMean s k X = m := sm_weight hk w
  have hconst := sm_const hk (m^2)
  change sliceMean s k (fun A ↦ (X A - m)^2) ≤ _
  have he : sliceMean s k (fun A ↦ (X A - m)^2) =
      sliceMean s k (fun A ↦ X A^2) - 2*m*sliceMean s k X + sliceMean s k (fun _ ↦ m^2) := by
    unfold sliceMean mean
    simp_rw [show ∀ z : ℝ, (z-m)^2 = z^2 - 2*m*z + m^2 by intro z; ring,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  rw [he,hmean,hconst]
  linarith

/-- Exponential moment for bounded nonnegative weights in a uniform sample without replacement. -/
theorem sm_weight_exp {s : Finset α} {k : ℕ} (hk : k ≤ s.card) (w : α → ℝ)
    {b : ℝ} (hb : 0 < b) (hw : ∀ x ∈ s, 0 ≤ w x ∧ w x ≤ b) :
    sliceMean s k (fun A ↦ Real.exp ((∑ x ∈ A, w x)/b)) ≤
      Real.exp ((Real.exp 1 - 1) * (((k : ℝ)/s.card) * ∑ x ∈ s, w x) / b) := by
  let d (x : α) := Real.exp (w x/b) - 1
  let q : ℝ := k / (s.card : ℝ)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hd (x) (hx : x ∈ s) : 0 ≤ d x := sub_nonneg.mpr
    (Real.one_le_exp (div_nonneg (hw x hx).1 hb.le))
  have hch (x) (hx : x ∈ s) : d x ≤ (Real.exp 1 - 1) * (w x/b) := by
    let u := w x/b
    have hu : 0 ≤ u := div_nonneg (hw x hx).1 hb.le
    have hv : u ≤ 1 := (div_le_one₀ hb).mpr (hw x hx).2
    have h := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (1:ℝ))
      (sub_nonneg.mpr hv) hu (show 1-u+u=1 by ring)
    simp only [smul_eq_mul, mul_zero, mul_one, zero_add, Real.exp_zero] at h
    change Real.exp u - 1 ≤ (Real.exp 1 - 1)*u
    linarith
  calc
    _ = sliceMean s k (fun A ↦ ∑ t ∈ s.powerset, if t ⊆ A then ∏ x ∈ t, d x else 0) := by
      apply sm_congr
      intro A hA
      have hsub := (Finset.mem_powersetCard.mp hA).1
      rw [Finset.sum_div, Real.exp_sum]
      simp_rw [show ∀ x, Real.exp (w x/b) = 1 + d x by intro x; dsimp [d]; ring]
      rw [Finset.prod_one_add, ← Finset.sum_filter]
      congr 1
      ext t
      simp only [Finset.mem_powerset, Finset.mem_filter]
      exact ⟨fun h ↦ ⟨h.trans hsub,h⟩, And.right⟩
    _ = ∑ t ∈ s.powerset, incProb s k t * ∏ x ∈ t, d x := by
      rw [sm_sum]; simp_rw [sm_inc]
    _ ≤ ∑ t ∈ s.powerset, ∏ x ∈ t, (q*d x) := by
      apply Finset.sum_le_sum
      intro t ht
      rw [Finset.prod_mul_distrib, Finset.prod_const]
      exact mul_le_mul_of_nonneg_right (inc_le_pow hk (Finset.mem_powerset.mp ht))
        (Finset.prod_nonneg (fun x hx ↦ hd x ((Finset.mem_powerset.mp ht) hx)))
    _ = ∏ x ∈ s, (1+q*d x) := (Finset.prod_one_add _).symm
    _ ≤ ∏ x ∈ s, Real.exp (q*d x) := by
      apply Finset.prod_le_prod
      · intro x hx; linarith [mul_nonneg hq (hd x hx)]
      · intro x _; linarith [Real.add_one_le_exp (q*d x)]
    _ ≤ _ := by
      rw [← Real.exp_sum, Real.exp_le_exp]
      calc
        _ ≤ ∑ x ∈ s, q*((Real.exp 1-1)*(w x/b)) :=
          Finset.sum_le_sum (fun x hx ↦ mul_le_mul_of_nonneg_left (hch x hx) hq)
        _ = _ := by simp_rw [← Finset.mul_sum, ← Finset.sum_div]; dsimp [q]; ring

end
end Green39.Smooth

end SliceMoments

/- Source: one-percent-formal/smooth-law/SmoothConvolution.lean -/
section SmoothConvolution

open scoped BigOperators Classical
open Green39.Concentration

namespace Green39.Smooth
noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def conv (μ : G → ℝ) (A : Finset G) (z : G) := ∑ a ∈ A, μ (z-a)

def l1 (μ : G → ℝ) (k : ℕ) (A : Finset G) :=
  ∑ z : G, |conv μ A z - k/(Fintype.card G : ℝ)|

theorem conv_variance (μ : G → ℝ) (hn : ∀ x, 0 ≤ μ x) (hm : ∑ x, μ x = 1)
    {k : ℕ} (hk : k ≤ Fintype.card G) (z : G) :
    sliceMean Finset.univ k (fun A ↦ (conv μ A z - k/(Fintype.card G : ℝ))^2) ≤
      (k/(Fintype.card G : ℝ)) * ∑ x, μ x ^ 2 := by
  have h := sm_variance (s := Finset.univ) (by simpa using hk) (fun a ↦ μ (z-a))
    (fun a _ ↦ hn _)
  have h1 : ∑ a, μ (z-a) = 1 := ((Equiv.subLeft z).sum_comp μ).trans hm
  have h2 : ∑ a, μ (z-a)^2 = ∑ x, μ x^2 := (Equiv.subLeft z).sum_comp (fun a ↦ μ a^2)
  simpa only [conv, Finset.card_univ, h1, h2, mul_one] using h

/-- Expected counting-measure ℓ¹ error of the actual convolution under the uniform slice. -/
theorem sm_l1 (μ : G → ℝ) (hn : ∀ x, 0 ≤ μ x) (hm : ∑ x, μ x = 1)
    {k : ℕ} (hk : k ≤ Fintype.card G) :
    sliceMean Finset.univ k (l1 μ k) ≤ Real.sqrt ((Fintype.card G : ℝ)*k*∑ x, μ x^2) := by
  let p : ℝ := Fintype.card G
  have hp : 0 < p := by dsimp [p]; exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
  let v : ℝ := k/p * ∑ x, μ x^2
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hz (z : G) : sliceMean Finset.univ k (fun A ↦ |conv μ A z - k/p|) ≤ Real.sqrt v := by
    apply Real.le_sqrt_of_sq_le
    calc
      _ ≤ sliceMean Finset.univ k (fun A ↦ |conv μ A z - k/p|^2) := sum_div_card_sq_le_sum_sq_div_card
      _ ≤ v := by simpa only [sq_abs] using conv_variance μ hn hm hk z
  change sliceMean Finset.univ k (fun A ↦ ∑ z : G, |conv μ A z - k/p|) ≤ _
  rw [sm_sum]
  calc
    _ ≤ ∑ _z : G, Real.sqrt v := Finset.sum_le_sum (fun z _ ↦ hz z)
    _ = p * Real.sqrt v := by simp [p,nsmul_eq_mul]
    _ ≤ _ := by
      apply Real.le_sqrt_of_sq_le
      rw [mul_pow, Real.sq_sqrt hv]
      change p^2 * ((k:ℝ)/p * _) ≤ p * k * _
      exact le_of_eq (by field_simp)

omit [DecidableEq G] in
theorem conv_mass (μ : G → ℝ) (hm : ∑ x, μ x = 1) (A : Finset G) :
    ∑ z, conv μ A z = A.card := by
  unfold conv
  rw [Finset.sum_comm]
  have h (a : G) : ∑ z, μ (z-a) = 1 := ((Equiv.subRight a).sum_comp μ).trans hm
  simp_rw [h]
  simp

theorem l1_exchange (μ : G → ℝ) (hn : ∀ x, 0 ≤ μ x) (hm : ∑ x, μ x = 1)
    (s : Finset G) (k : ℕ) : ExchangeLipschitz s k (l1 μ k) 2 := by
  intro A hA B hB hd
  let c := (k : ℝ)/Fintype.card G
  have hBA : (B \ A).card ≤ 1 := by
    rw [Finset.card_sdiff_comm ((Finset.mem_powersetCard.mp hB).2.trans (Finset.mem_powersetCard.mp hA).2.symm)]
    exact hd
  have hdiff (z : G) : conv μ A z - conv μ B z = conv μ (A \ B) z - conv μ (B \ A) z := by
    have h₁ := Finset.sum_inter_add_sum_sdiff A B (fun a ↦ μ (z-a))
    have h₂ := Finset.sum_inter_add_sum_sdiff B A (fun a ↦ μ (z-a))
    rw [Finset.inter_comm B A] at h₂
    unfold conv
    linarith
  change abs ((∑ z : G, |conv μ A z - c|) - ∑ z : G, |conv μ B z - c|) ≤ 2
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ z : G, abs (|conv μ A z - c| - |conv μ B z - c|) := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ z : G, (conv μ (A \ B) z + conv μ (B \ A) z) := by
      apply Finset.sum_le_sum
      intro z _
      apply (abs_abs_sub_abs_le_abs_sub _ _).trans
      rw [sub_sub_sub_cancel_right, hdiff]
      have hnon (D : Finset G) : 0 ≤ conv μ D z := Finset.sum_nonneg (fun _ _ ↦ hn _)
      exact abs_le.mpr ⟨by linarith [hnon (A \ B)], by linarith [hnon (B \ A)]⟩
    _ ≤ 2 := by
      rw [Finset.sum_add_distrib, conv_mass μ hm, conv_mass μ hm]
      exact_mod_cast (show (A \ B).card + (B \ A).card ≤ 2 by omega)

omit [AddCommGroup G] [DecidableEq G] in
theorem law_sum_sq_le_cap (μ : G → ℝ) (hn : ∀ x, 0 ≤ μ x) (hm : ∑ x, μ x = 1)
    {b : ℝ} (hb : ∀ x, μ x ≤ b) : ∑ x, μ x^2 ≤ b := by
  calc
    _ ≤ ∑ x, b * μ x := Finset.sum_le_sum (fun x _ ↦ by rw [sq]; exact mul_le_mul_of_nonneg_right (hb x) (hn x))
    _ = _ := by rw [← Finset.mul_sum, hm, mul_one]

end
end Green39.Smooth

end SmoothConvolution

/- Source: one-percent-formal/smooth-law/SplitSlice.lean -/
section SplitSlice

open scoped BigOperators Classical
open Green39.Concentration

namespace Green39.Smooth
noncomputable section
variable {α ι : Type*} [DecidableEq α]

/-- Expose a uniform first half, then sample the second from its complement. -/
def splitMean (s : Finset α) (a b : ℕ) (f : Finset α → Finset α → ℝ) :=
  sliceMean s a (fun A ↦ sliceMean (s \ A) b (f A))

private theorem disj_slice (s A : Finset α) (b : ℕ) :
    (s \ A).powersetCard b = (s.powersetCard b).filter (fun B ↦ Disjoint B A) := by
  ext B
  simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_sdiff]
  tauto

private theorem pair_sum (s : Finset α) (a b : ℕ) (f : Finset α → Finset α → ℝ) :
    (∑ A ∈ s.powersetCard a, ∑ B ∈ (s \ A).powersetCard b, f A B) =
      ∑ B ∈ s.powersetCard b, ∑ A ∈ (s \ B).powersetCard a, f A B := by
  simp_rw [disj_slice, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp_rw [disjoint_comm]

private theorem card_rest {s A : Finset α} {a : ℕ} (hA : A ∈ s.powersetCard a) :
    (s \ A).card = s.card - a := by
  rw [Finset.card_sdiff_of_subset (Finset.mem_powersetCard.mp hA).1,
    (Finset.mem_powersetCard.mp hA).2]

private theorem split_formula (s : Finset α) (a b : ℕ) (f : Finset α → Finset α → ℝ) :
    splitMean s a b f =
    (∑ A ∈ s.powersetCard a, ∑ B ∈ (s \ A).powersetCard b, f A B) /
      ((s.card-a).choose b * (s.card.choose a : ℝ)) := by
  unfold splitMean sliceMean mean
  rw [← div_div, Finset.card_powersetCard]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro A hA
  simp only [Finset.card_powersetCard, card_rest hA]

theorem split_swap (s : Finset α) (a b : ℕ) (f : Finset α → Finset α → ℝ) :
    splitMean s a b f = splitMean s b a (fun B A ↦ f A B) := by
  have count (i j : ℕ) :
      (∑ A ∈ s.powersetCard i, ∑ _B ∈ (s \ A).powersetCard j, (1:ℝ)) =
        (s.card-i).choose j * (s.card.choose i : ℝ) := by
    calc
      _ = ∑ _A ∈ s.powersetCard i, ((s.card-i).choose j : ℝ) := by
        apply Finset.sum_congr rfl
        intro A hA
        simp [card_rest hA]
      _ = _ := by simp [nsmul_eq_mul, mul_comm]
  rw [split_formula, split_formula, pair_sum s a b f]
  rw [← count a b, ← count b a, pair_sum s a b (fun _ _ ↦ 1)]

theorem split_fst {s : Finset α} {a b : ℕ} (hk : a+b ≤ s.card) (f : Finset α → ℝ) :
    splitMean s a b (fun A _ ↦ f A) = sliceMean s a f := by
  apply sm_congr
  intro A hA
  exact sm_const (by rw [card_rest hA]; omega) _

theorem split_snd {s : Finset α} {a b : ℕ} (hk : a+b ≤ s.card) (f : Finset α → ℝ) :
    splitMean s a b (fun _ B ↦ f B) = sliceMean s b f := by
  rw [split_swap, split_fst (by omega : b+a ≤ s.card)]

omit [DecidableEq α] in
theorem sm_event (s : Finset α) (k : ℕ) (E : Finset α → Prop) :
    sliceMean s k (fun A ↦ if E A then 1 else 0) = sliceProbability s k E := by
  unfold sliceProbability sliceMean mean
  rw [← Finset.sum_filter]
  simp

omit [DecidableEq α] in
theorem prob_mono {s : Finset α} {k : ℕ} {E F : Finset α → Prop}
    (h : ∀ A ∈ s.powersetCard k, E A → F A) :
    sliceProbability s k E ≤ sliceProbability s k F := by
  rw [← sm_event, ← sm_event]
  apply sm_mono
  intro A hA
  by_cases he : E A
  · simp [he,h A hA he]
  · simp [he]; split <;> norm_num

omit [DecidableEq α] in
theorem prob_union (s : Finset α) (k : ℕ) (d : Finset ι) (E : ι → Finset α → Prop) :
    sliceProbability s k (fun A ↦ ∃ i ∈ d, E i A) ≤ ∑ i ∈ d, sliceProbability s k (E i) := by
  simp_rw [← sm_event]
  rw [← sm_sum]
  apply sm_mono
  intro A _
  split
  · rename_i he
    obtain ⟨i,hi,hei⟩ := he
    simpa [hei] using (Finset.single_le_sum (f := fun j ↦ if E j A then (1:ℝ) else 0)
      (fun _ _ ↦ by split <;> norm_num) hi)
  · exact Finset.sum_nonneg (fun _ _ ↦ by split <;> norm_num)

theorem weight_tail {s : Finset α} {k : ℕ} (hk : k ≤ s.card) (w : α → ℝ)
    {b : ℝ} (hb : 0 < b) (hw : ∀ x ∈ s, 0 ≤ w x ∧ w x ≤ b) (t : ℝ) :
    sliceProbability s k (fun A ↦ t ≤ ∑ x ∈ A, w x) ≤
      Real.exp (((Real.exp 1-1) * (((k:ℝ)/s.card)*∑ x ∈ s, w x) - t)/b) := by
  let c := Real.exp (t/b)
  have hc : 0 < c := Real.exp_pos _
  have hm := sm_weight_exp hk w hb hw
  have h : c * sliceProbability s k (fun A ↦ t ≤ ∑ x ∈ A, w x) ≤
      sliceMean s k (fun A ↦ Real.exp ((∑ x ∈ A, w x)/b)) := by
    rw [← sm_event]
    calc
      _ = sliceMean s k (fun A ↦ c * (if t ≤ ∑ x ∈ A, w x then 1 else 0)) := by
        unfold sliceMean mean; rw [← Finset.mul_sum]; ring
      _ ≤ _ := by
        apply sm_mono
        intro A _
        split
        · rename_i h
          simpa [c] using Real.exp_le_exp.mpr (div_le_div_of_nonneg_right h hb.le)
        · simpa only [mul_zero] using Real.exp_nonneg ((∑ x ∈ A, w x)/b)
  apply le_of_le_of_eq ((le_div_iff₀ hc).mpr ((mul_comm _ c).le.trans (h.trans hm)))
  rw [← Real.exp_sub]
  congr 1
  ring

end
end Green39.Smooth

end SplitSlice

/- Source: one-percent-formal/smooth-law/SplitEvents.lean -/
section SplitEvents

open scoped BigOperators Classical
open Green39.Concentration

namespace Green39.Smooth
noncomputable section
variable {α ι : Type*} [DecidableEq α]

omit [DecidableEq α] in
theorem sm_add (s : Finset α) (k : ℕ) (f g : Finset α → ℝ) :
    sliceMean s k (fun A ↦ f A + g A) = sliceMean s k f + sliceMean s k g := by
  unfold sliceMean mean
  rw [Finset.sum_add_distrib, add_div]

omit [DecidableEq α] in
theorem prob_or (s : Finset α) (k : ℕ) (E F : Finset α → Prop) :
    sliceProbability s k (fun A ↦ E A ∨ F A) ≤ sliceProbability s k E + sliceProbability s k F := by
  simp_rw [← sm_event]
  rw [← sm_add]
  apply sm_mono
  intro A _
  by_cases he : E A <;> by_cases hf : F A <;> simp [he,hf]

omit [DecidableEq α] in
theorem prob_one {s : Finset α} {k : ℕ} (hk : k ≤ s.card) (E : Finset α → Prop) :
    sliceProbability s k E ≤ 1 := by
  rw [← sm_event]
  calc
    _ ≤ sliceMean s k (fun _ ↦ 1) := by
      apply sm_mono
      intro A _
      split <;> norm_num
    _ = _ := sm_const hk 1

/-- Joint probability for a uniformly sampled disjoint pair, in exposure order. -/
def splitProb (s : Finset α) (a b : ℕ) (E : Finset α → Finset α → Prop) :=
  splitMean s a b (fun A B ↦ if E A B then 1 else 0)

theorem split_union (s : Finset α) (a b : ℕ) (I : Finset ι) (E : ι → Finset α → Finset α → Prop) :
    splitProb s a b (fun A B ↦ ∃ i ∈ I, E i A B) ≤ ∑ i ∈ I, splitProb s a b (E i) := by
  unfold splitProb splitMean
  rw [← sm_sum]
  apply sm_mono
  intro A _
  simpa only [sm_event] using prob_union (s \ A) b I (fun i ↦ E i A)

theorem split_bad_le {s : Finset α} {a b : ℕ} (hk : a+b ≤ s.card)
    (EA EB : Finset α → Prop) (E : Finset α → Finset α → Prop) {q : ℝ} (hq : 0 ≤ q)
    (h : ∀ A ∈ s.powersetCard a, ¬EA A → sliceProbability (s \ A) b (E A) ≤ q) :
    splitProb s a b (fun A B ↦ EB B ∨ E A B) ≤
      sliceProbability s b EB + sliceProbability s a EA + q := by
  let u (A : Finset α) := sliceProbability (s \ A) b EB
  let v (A : Finset α) := sliceProbability (s \ A) b (E A)
  have hu : sliceMean s a u = sliceProbability s b EB := by
    simpa only [splitMean, sm_event, u] using split_snd hk (fun B ↦ if EB B then (1:ℝ) else 0)
  have hv : sliceMean s a v ≤ sliceProbability s a EA + q := by
    calc
      _ ≤ sliceMean s a (fun A ↦ (if EA A then 1 else 0) + q) := by
        apply sm_mono
        intro A hA
        by_cases he : EA A
        · rw [if_pos he]
          have hc : b ≤ (s \ A).card := by
            rw [Finset.card_sdiff_of_subset (Finset.mem_powersetCard.mp hA).1,
              (Finset.mem_powersetCard.mp hA).2]; omega
          exact (prob_one hc _).trans (by linarith)
        · simpa [he] using h A hA he
      _ = _ := by rw [sm_add, sm_event, sm_const (by omega : a ≤ s.card)]
  calc
    _ ≤ sliceMean s a (fun A ↦ u A + v A) := by
      apply sm_mono
      intro A _
      rw [sm_event]
      exact prob_or _ _ _ _
    _ ≤ _ := by rw [sm_add, hu]; linarith

end
end Green39.Smooth

end SplitEvents

/- Source: one-percent-formal/smooth-law/SmoothLaw.lean -/
section SmoothLaw

open scoped BigOperators Classical
open Green39.Concentration

namespace Green39.Smooth
noncomputable section
variable {G ι : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Pointwise excess of the first-half convolution, translated by v. -/
def excess (μ : G → ℝ) (A : Finset G) (c : ℝ) (v z : G) :=
  max (conv (fun x ↦ μ (-x)) A (z-v) - c) 0

def l1Tail (n : ℕ) (u : ℝ) := Real.exp (-u^2 / (2*(n:ℝ)*2^2))

theorem l1_tail (μ : G → ℝ) (hn : ∀ x, 0 ≤ μ x) (hm : ∑ x, μ x = 1)
    {a : ℕ} (ha : a ≤ Fintype.card G) {m D u : ℝ} (hb : ∀ x, μ x ≤ m)
    (hu : 0 ≤ u) (hD : Real.sqrt ((Fintype.card G : ℝ)*a*m) + u ≤ D) :
    sliceProbability Finset.univ a (fun A ↦ D < l1 μ a A) ≤ l1Tail a u := by
  have hE := sm_l1 μ hn hm ha
  have hcap := law_sum_sq_le_cap μ hn hm hb
  have hupper := hE.trans (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hcap
    (by positivity : 0 ≤ (Fintype.card G : ℝ)*a)))
  apply (prob_mono (s := Finset.univ) (F := fun A ↦ u ≤ l1 μ a A - sliceMean Finset.univ a (l1 μ a))
    (E := fun A ↦ D < l1 μ a A) (fun A _ h ↦ by linarith)).trans
  exact sliceProbability_ge_le (by simpa using ha) (l1_exchange μ hn hm _ a) (by norm_num) hu

theorem conv_max_tail (μ : G → ℝ) (hn : ∀ x, 0 ≤ μ x) (hm : ∑ x, μ x = 1)
    {a : ℕ} (ha : a ≤ Fintype.card G) {m : ℝ} (hm0 : 0 < m) (hb : ∀ x, μ x ≤ m) (t : ℝ) :
    sliceProbability Finset.univ a (fun A ↦ ∃ z, t < conv μ A z) ≤
      (Fintype.card G : ℝ)*Real.exp (((Real.exp 1-1)*(a/(Fintype.card G:ℝ))-t)/m) := by
  let E (z : G) (A : Finset G) := t < conv μ A z
  have hz (z : G) : sliceProbability Finset.univ a (E z) ≤
      Real.exp (((Real.exp 1-1)*(a/(Fintype.card G:ℝ))-t)/m) := by
    have h := weight_tail (s := Finset.univ) (by simpa using ha) (fun x ↦ μ (z-x)) hm0
      (fun x _ ↦ ⟨hn _, hb _⟩) t
    have he : ∑ x, μ (z-x) = 1 := ((Equiv.subLeft z).sum_comp μ).trans hm
    apply (prob_mono (F := fun A ↦ t ≤ conv μ A z) (fun _ _ ha ↦ le_of_lt ha)).trans
    simpa only [conv, he, Finset.card_univ, mul_one] using h
  calc
    _ ≤ ∑ z, sliceProbability Finset.univ a (E z) := by
      simpa only [Finset.mem_univ, true_and] using prob_union Finset.univ a Finset.univ E
    _ ≤ _ := (Finset.sum_le_sum (fun z _ ↦ hz z)).trans_eq (by simp [nsmul_eq_mul])

theorem excess_tail (μ : G → ℝ) {a b : ℕ} (hab : a+b ≤ Fintype.card G)
    {A : Finset G} (hA : A.card = a) {c t D T : ℝ} (ht : 0 < t)
    (hc : (a:ℝ)/Fintype.card G ≤ c)
    (hD : l1 (fun x ↦ μ (-x)) a A ≤ D)
    (hcap : ∀ z, conv (fun x ↦ μ (-x)) A z ≤ t) :
    sliceProbability (Finset.univ \ A) b (fun B ↦ ∃ v, T < ∑ z ∈ B, excess μ A c v z) ≤
      (Fintype.card G:ℝ)*Real.exp (((Real.exp 1-1)*
        ((b:ℝ)/(Fintype.card G-a : ℕ)*D)-T)/t) := by
  let S := Finset.univ \ A
  have hN : S.card = Fintype.card G-a := by
    simp [S, Finset.card_sdiff_of_subset (Finset.subset_univ A), hA]
  have hb : b ≤ S.card := by rw [hN]; omega
  have hc0 : 0 ≤ c := (by positivity : 0 ≤ (a:ℝ)/Fintype.card G).trans hc
  have he0 (v z : G) : 0 ≤ excess μ A c v z := le_max_right _ _
  have het (v z : G) : excess μ A c v z ≤ t := max_le (by linarith [hcap (z-v)]) ht.le
  have hmass (v : G) : ∑ z ∈ S, excess μ A c v z ≤ D := by
    calc
      _ ≤ ∑ z, excess μ A c v z := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun z _ _ ↦ he0 _ z)
      _ ≤ ∑ z, |conv (fun x ↦ μ (-x)) A (z-v) - (a:ℝ)/Fintype.card G| := by
        apply Finset.sum_le_sum
        intro z _
        apply max_le _ (abs_nonneg _)
        exact (sub_le_sub_left hc _).trans (le_abs_self _)
      _ = l1 (fun x ↦ μ (-x)) a A := (Equiv.subRight v).sum_comp
        (fun z ↦ |conv (fun x ↦ μ (-x)) A z - (a:ℝ)/Fintype.card G|)
      _ ≤ _ := hD
  let E (v : G) (B : Finset G) := T < ∑ z ∈ B, excess μ A c v z
  have he (v : G) : sliceProbability S b (E v) ≤ Real.exp (((Real.exp 1-1)*
        ((b:ℝ)/(Fintype.card G-a : ℕ)*D)-T)/t) := by
    apply (prob_mono (F := fun B ↦ T ≤ ∑ z ∈ B, excess μ A c v z)
      (fun _ _ h ↦ le_of_lt h)).trans
    apply (weight_tail hb _ ht (fun z _ ↦ ⟨he0 v z, het v z⟩) T).trans
    rw [hN, Real.exp_le_exp]
    gcongr
    · exact sub_nonneg.mpr (Real.one_le_exp (by norm_num))
    · exact hmass v
  calc
    _ ≤ ∑ v, sliceProbability S b (E v) := by
      simpa only [Finset.mem_univ, true_and] using prob_union S b Finset.univ E
    _ ≤ _ := (Finset.sum_le_sum (fun v _ ↦ he v)).trans_eq (by simp [nsmul_eq_mul])

/-- Finite failure bound for both inequalities of (4), simultaneously over a deterministic
family and all shifts. The two slices are sampled disjointly, and may have unequal sizes. -/
theorem equation_four (I : Finset ι) (μ : ι → G → ℝ) {m : ℝ} (hm : 0 < m)
    (hn : ∀ i ∈ I, ∀ x, 0 ≤ μ i x) (hmass : ∀ i ∈ I, ∑ x, μ i x = 1)
    (hcap : ∀ i ∈ I, ∀ x, μ i x ≤ m)
    {a b : ℕ} (hab : a+b ≤ Fintype.card G) {c t D T u v : ℝ}
    (hc : (a:ℝ)/Fintype.card G ≤ c) (ht : 0 < t) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (haD : Real.sqrt ((Fintype.card G:ℝ)*a*m) + u ≤ D)
    (hbD : Real.sqrt ((Fintype.card G:ℝ)*b*m) + v ≤ D) :
    splitProb Finset.univ a b (fun A B ↦ ∃ i ∈ I,
      D < l1 (μ i) b B ∨ ∃ shift, T < ∑ z ∈ B, excess (μ i) A c shift z) ≤
      (I.card:ℝ) * (l1Tail b v + l1Tail a u +
        (Fintype.card G:ℝ) * Real.exp (((Real.exp 1-1)*(a/(Fintype.card G:ℝ))-t)/m) +
        (Fintype.card G:ℝ) * Real.exp (((Real.exp 1-1)*((b:ℝ)/(Fintype.card G-a:ℕ)*D)-T)/t)) := by
  apply (split_union _ _ _ I _).trans
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_le_sum
  intro i hi
  let ν (x : G) := μ i (-x)
  have hν : ∑ x, ν x = 1 := (Equiv.sum_comp (Equiv.neg G) (μ i)).trans (hmass i hi)
  have hνn (x : G) : 0 ≤ ν x := hn i hi _
  have hνb (x : G) : ν x ≤ m := hcap i hi _
  let EA (A : Finset G) := D < l1 ν a A ∨ ∃ z, t < conv ν A z
  have hA := prob_or Finset.univ a (fun A ↦ D < l1 ν a A) (fun A ↦ ∃ z, t < conv ν A z)
  have hA' := hA.trans (add_le_add (l1_tail ν hνn hν (by omega) hνb hu haD)
    (conv_max_tail ν hνn hν (by omega) hm hνb t))
  have hB := l1_tail (μ i) (hn i hi) (hmass i hi) (by omega) (hcap i hi) hv hbD
  apply (split_bad_le (by simpa using hab) EA (fun B ↦ D < l1 (μ i) b B)
    (fun A B ↦ ∃ shift, T < ∑ z ∈ B, excess (μ i) A c shift z)
    (q := (Fintype.card G:ℝ)*Real.exp (((Real.exp 1-1)*((b:ℝ)/(Fintype.card G-a:ℕ)*D)-T)/t))
    (by positivity) ?_).trans
  · dsimp only [EA]
    linarith only [hA', hB]
  · intro A hA he
    change ¬(_ ∨ _) at he
    obtain ⟨h₁,h₂⟩ := not_or.mp he
    exact excess_tail _ hab (Finset.mem_powersetCard.mp hA).2 ht hc (le_of_not_gt h₁)
      (fun z ↦ le_of_not_gt (fun hz ↦ h₂ ⟨z,hz⟩))

end
end Green39.Smooth

end SmoothLaw

/- Source: one-percent-formal/smooth-law/PaperConstants.lean -/
section PaperConstants

open scoped BigOperators Classical
open Green39.Concentration

namespace Green39.Smooth
noncomputable section

private theorem numeric_l1 {p k n : ℝ} (hk : 0 < k) (hn : 0 ≤ n)
    (hp' : p ≤ 2*k^2) (hn' : n ≤ k) :
    Real.sqrt (p*n*(2/(10^24*k))) + k/200000000 ≤ k/100000000 := by
  have h : p*n ≤ (2*k^2)*k := mul_le_mul hp' hn' hn (by positivity)
  have hs : Real.sqrt (p*n*(2/(10^24*k))) ≤ k/200000000 := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg k, mul_pos (sq_pos_of_pos hk) hk]
  linarith

private theorem numeric_tail {k : ℝ} {n : ℕ} (hk : 0 < k) (hn : 0 < n) (hn' : (n:ℝ) ≤ k) :
    l1Tail n (k/200000000) ≤ Real.exp (-k/320000000000000000) := by
  unfold l1Tail
  rw [Real.exp_le_exp, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [mul_le_mul_of_nonneg_left hn' hk.le]

/-- The manuscript's constants with explicit finite failure rates. Here p can be the
cardinality of any finite additive abelian group. Its only size inputs are k² ≤ p ≤ 2k². -/
theorem paper_equation_four {G ι : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]
    (I : Finset ι) (μ : ι → G → ℝ) {k a b : ℕ}
    (hk : 2 ≤ k) (hab : a+b=k) (ha : 0 < a) (hb : 0 < b) (hhalf : 2*a ≤ k)
    (hlo : k^2 ≤ Fintype.card G) (hhi : Fintype.card G ≤ 2*k^2)
    (hn : ∀ i ∈ I, ∀ x, 0 ≤ μ i x) (hm : ∀ i ∈ I, ∑ x, μ i x = 1)
    (hc : ∀ i ∈ I, ∀ x, μ i x ≤ 2/(10^24*(k:ℝ))) :
    splitProb Finset.univ a b (fun A B ↦ ∃ i ∈ I,
      (k:ℝ)/100000000 < l1 (μ i) b B ∨ ∃ v, (1:ℝ)/1000 <
        ∑ z ∈ B, excess (μ i) A ((51:ℝ)/(100*k)) v z) ≤
      (I.card:ℝ)*(2*Real.exp (-(k:ℝ)/320000000000000000) +
        (Fintype.card G:ℝ)*Real.exp (10^24 - (10^24/2)*Real.sqrt k) +
        (Fintype.card G:ℝ)*Real.exp (-(9:ℝ)/10000*Real.sqrt k)) := by
  let p := Fintype.card G
  have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : 0 < (k:ℝ) := by linarith
  have ha' : (a:ℝ) ≤ k := by exact_mod_cast (show a ≤ k by omega)
  have hb' : (b:ℝ) ≤ k := by exact_mod_cast (show b ≤ k by omega)
  have hhalf' : 2*(a:ℝ) ≤ k := by exact_mod_cast hhalf
  have hlo' : (k:ℝ)^2 ≤ p := by exact_mod_cast hlo
  have hhi' : (p:ℝ) ≤ 2*(k:ℝ)^2 := by exact_mod_cast hhi
  have hp0 : 0 < (p:ℝ) := by nlinarith
  have hkp : a+b ≤ Fintype.card G := by rw [hab]; exact (Nat.le_self_pow (by decide) k).trans hlo
  have hs := Real.sq_sqrt hk0.le
  have hs0 := Real.sqrt_pos.mpr hk0
  have hc' : (a:ℝ)/p ≤ 51/(100*k) := by
    rw [div_le_div_iff₀ hp0 (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hhalf' hk0.le]
  have hE := equation_four I μ (m := 2/(10^24*(k:ℝ))) (by positivity) hn hm hc hkp
    (t := (Real.sqrt k)⁻¹) (T := 1/1000) hc' (inv_pos.mpr hs0)
    (by positivity : 0 ≤ (k:ℝ)/200000000) (by positivity : 0 ≤ (k:ℝ)/200000000)
    (numeric_l1 hk0 (Nat.cast_nonneg a) hhi' ha')
    (numeric_l1 hk0 (Nat.cast_nonneg b) hhi' hb')
  apply hE.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hden : a ≤ p := by change a ≤ Fintype.card G; omega
  have hden' : (0:ℝ) < p-a := by nlinarith
  have hexp : Real.exp 1 - 1 ≤ 2 := by linarith [Real.exp_one_lt_d9]
  have he0 : 0 ≤ Real.exp 1 - 1 := sub_nonneg.mpr (Real.one_le_exp (by norm_num))
  have hmean : ((a:ℝ)/p)*k ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one₀ hp0]
    nlinarith [mul_le_mul_of_nonneg_right ha' hk0.le]
  have hcoord : ((Real.exp 1-1)*((a:ℝ)/p) - (Real.sqrt k)⁻¹)/(2/(10^24*k)) ≤
      10^24 - (10^24/2)*Real.sqrt k := by
    have hprod := mul_le_mul hexp hmean (by positivity : 0 ≤ ((a:ℝ)/p)*k) (by norm_num : (0:ℝ) ≤ 2)
    have hroot : (Real.sqrt k)⁻¹ * k = Real.sqrt k := by
      field_simp
      nlinarith only [hs]
    rw [div_div_eq_mul_div, div_le_iff₀ (by norm_num)]
    nlinarith [hroot]
  have hmean' : (b:ℝ)/(p-a)*((k:ℝ)/100000000) ≤ 2/100000000 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hden']
    nlinarith [mul_le_mul_of_nonneg_right hb' hk0.le]
  have hexc : ((Real.exp 1-1)*((b:ℝ)/(p-a : ℕ)*((k:ℝ)/100000000))-1/1000)/(Real.sqrt k)⁻¹ ≤
      -(9:ℝ)/10000*Real.sqrt k := by
    rw [Nat.cast_sub hden, div_inv_eq_mul]
    apply mul_le_mul_of_nonneg_right _ hs0.le
    have hprod := mul_le_mul hexp hmean' (by positivity : 0 ≤ (b:ℝ)/(p-a)*((k:ℝ)/100000000))
      (by norm_num : (0:ℝ) ≤ 2)
    linarith
  have h1 := numeric_tail hk0 ha ha'
  have h2 := numeric_tail hk0 hb hb'
  have h3 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hcoord) (Nat.cast_nonneg p (α := ℝ))
  have h4 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexc) (Nat.cast_nonneg p (α := ℝ))
  change _ ≤ 2*_ + (p:ℝ)*_ + (p:ℝ)*_
  dsimp only [p] at *
  linarith only [h1,h2,h3,h4]

end
end Green39.Smooth

end PaperConstants

/- Source: one-percent-formal/assembly/AssemblySmooth.lean -/
section AssemblySmooth

/- Transfer of the capped-law estimate to the ordered-pair probability from §2. -/

open Finset Real Filter Topology
open scoped Pointwise Classical
namespace Green39.Assembly
noncomputable section
open Split OnePercent.Fourier
variable {p : ℕ} [NeZero p]

theorem probability_eq_splitProb {α : Type*} [DecidableEq α] (s : Finset α) (a b : ℕ)
    (E : Finset α → Finset α → Prop) :
    probability (orderedPairs s a b) (fun q => E q.1 q.2) = Smooth.splitProb s a b E := by
  rw [probability_eq_mean_first]
  unfold Smooth.splitProb Smooth.splitMean
  simp_rw [Smooth.sm_event]
  rfl

def smoothBound (p k : ℝ) := 2*exp (-k/320000000000000000) +
  p*exp (10^24 - (10^24/2)*sqrt k) + p*exp (-(9:ℝ)/10000*sqrt k)

theorem one_law (μ : Law p) (hn : ∀ z, 0 ≤ μ z) (hm : ∑ z, μ z = 1)
    (hc : ∀ z, μ z ≤ 2/(10^24*(p.sqrt:ℝ))) (hk : 100000 ≤ p.sqrt) :
    probability (orderedPairs (univ:Points p) (half p.sqrt) (rest p.sqrt)) (fun q => ¬typical μ q)
      ≤ smoothBound p p.sqrt := by
  let k := p.sqrt
  let a := half k
  let b := rest k
  let c := (51:ℝ)/(100*k)
  have hab : a+b=k := by dsimp [a,b,half,rest]; omega
  have hpc : Fintype.card (ZMod p) ≤ 2*k^2 := by
    rw [ZMod.card]
    have h := Nat.lt_succ_sqrt' p
    dsimp [k]
    nlinarith [Nat.mul_le_mul_left p.sqrt (show 3 ≤ p.sqrt by omega)]
  have h := Smooth.paper_equation_four (G:=ZMod p) ({μ} : Finset (Law p)) id (k:=k) (a:=a) (b:=b)
    (by dsimp [k]; omega) hab (by dsimp [a,k,half]; omega) (by dsimp [b,k,rest]; omega)
    (by dsimp [a,half]; omega) (by simpa [k] using Nat.sqrt_le' p) hpc
    (by simpa using hn) (by simpa using hm) (by simpa using hc)
  let E (A B : Points p) := (k:ℝ)/100000000 < Smooth.l1 μ b B ∨
    ∃ v, (1:ℝ)/1000 < ∑ z ∈ B, Smooth.excess μ A c v z
  have he : probability (orderedPairs (univ:Points p) a b) (fun q => E q.1 q.2) ≤ smoothBound p k := by
    rw [probability_eq_splitProb]
    simpa [E,c,smoothBound,ZMod.card] using h
  refine (probability_mono ?_).trans he
  intro q hq hbad
  have h2 := (mem_orderedPairs.mp hq).2.2.2.1
  by_contra hnot
  change ¬ (_ ∨ _) at hnot
  push Not at hnot
  apply hbad
  have hconv (u : ZMod p) : convolution (indicator q.2) μ u = Smooth.conv μ q.2 u := convolution_indicator _ _ _
  have hsm (z : ZMod p) : smoothed q.1 μ z = Smooth.conv (fun t => μ (-t)) q.1 z := by
    simp only [smoothed_eq_convolution,convolution_indicator,Smooth.conv]
  constructor
  · rw [show (0.00000001:ℝ)*(p.sqrt:ℝ) = k/100000000 by dsimp [k]; ring]
    simpa only [hconv,h2,Smooth.l1,ZMod.card] using hnot.1
  · intro v
    simpa only [Smooth.excess,← hsm,show c = 0.51/(p.sqrt:ℝ) by dsimp [c,k]; ring,
      show (1:ℝ)/1000 = 0.001 by norm_num] using hnot.2 v

theorem power_margin {a b : ℝ} (h : a < b) (M : ℝ) :
    ∀ᶠ y : ℝ in atTop, M*y^a ≤ y^b := by
  filter_upwards [(tendsto_rpow_atTop (sub_pos.mpr h)).eventually_ge_atTop M,
    eventually_gt_atTop (0:ℝ)] with y hM hy
  calc
    _ ≤ y^(b-a)*y^a := mul_le_mul_of_nonneg_right hM (rpow_nonneg hy.le _)
    _ = _ := by rw [←rpow_add hy]; congr 1; ring

theorem smoothBound_eventually :
    ∀ᶠ k : ℝ in atTop, ∀ p : ℝ, 0 ≤ p → p ≤ 2*k^2 → smoothBound p k ≤ exp (-(k^(0.48:ℝ))) := by
  filter_upwards [eventually_ge_atTop (2:ℝ),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<0.48)).eventually_ge_atTop 4,
    power_margin (a:=0.48) (b:=1) (by norm_num) (10^19),
    power_margin (a:=0.48) (b:=0.5) (by norm_num) 10000,
    (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<0.48)).def (by norm_num : (0:ℝ)<1/3)]
    with k hk hz hlinear hroot hlog p hp hpc
  let z := k^(0.48:ℝ)
  have hk0 : 0 < k := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) hk
  rw [rpow_one] at hlinear
  have hsqrt : (10000:ℝ)*z ≤ sqrt k := by simpa only [Real.sqrt_eq_rpow,show (1:ℝ)/2=0.5 by norm_num] using hroot
  have hl : log k ≤ (1/3:ℝ)*z := by
    change ‖log k‖ ≤ (1/3:ℝ)*‖k^(0.48:ℝ)‖ at hlog
    simpa [z,Real.norm_of_nonneg (log_nonneg ((by norm_num : (1:ℝ) ≤ 2).trans hk)),Real.norm_of_nonneg (rpow_nonneg hk0.le _)] using hlog
  have hpz : p ≤ exp z := by
    calc
      _ ≤ k^3 := hpc.trans (by nlinarith [mul_nonneg (sq_nonneg k) (sub_nonneg.mpr hk)])
      _ = exp (3*log k) := by rw [show (3:ℝ) = (↑(3:ℕ):ℝ) by norm_num,exp_nat_mul,exp_log hk0]
      _ ≤ _ := exp_le_exp.mpr (by linarith)
  change 4 ≤ z at hz
  change (10:ℝ)^19*z ≤ k at hlinear
  have h₁ : exp (-k/320000000000000000) ≤ exp (-2*z) := exp_le_exp.mpr (by linarith only [hlinear,hz])
  have prod (u : ℝ) (hu : u ≤ -3*z) : p*exp u ≤ exp (-2*z) := by
    apply (mul_le_mul_of_nonneg_right hpz (exp_pos _).le).trans
    rw [←exp_add]; exact exp_le_exp.mpr (by linarith)
  have h₂ := prod (10^24 - (10^24/2)*sqrt k) (by linarith only [hsqrt,hz])
  have h₃ := prod (-(9:ℝ)/10000*sqrt k) (by linarith only [hsqrt,hz])
  have h₄ : (4:ℝ) ≤ exp z := by linarith only [Real.add_one_le_exp z,hz]
  unfold smoothBound
  calc
    _ ≤ 4*exp (-2*z) := by linarith only [h₁,h₂,h₃]
    _ ≤ exp z * exp (-2*z) := mul_le_mul_of_nonneg_right h₄ (exp_pos _).le
    _ = _ := by rw [←exp_add]; congr 1; change z + -2*z = -z; ring

end
end Green39.Assembly

end AssemblySmooth

/- Source: one-percent-formal/assembly/AssemblyRates.lean -/
section AssemblyRates

/- Prime moduli, the square-root scale, and scalar limits used for the split estimate. -/

open Filter Topology Real
namespace Green39.Assembly
noncomputable section

abbrev Prime := {p : ℕ // p.Prime}

theorem prime_cofinal : Tendsto (fun p : Prime => p.val) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  obtain ⟨n,hn,hp⟩ := Nat.exists_infinite_primes b
  exact (eventually_ge_atTop (⟨n,hp⟩ : Prime)).mono fun _ h => hn.trans h

theorem prime_root : Tendsto (fun p : Prime => p.val.sqrt) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  exact (prime_cofinal.eventually_ge_atTop (b*b)).mono fun _ h => Nat.le_sqrt.mpr h

theorem prime_root_real : Tendsto (fun p : Prime => (p.val.sqrt:ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp prime_root

theorem exp_decay (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun p : Prime => exp (-c * (p.val.sqrt:ℝ) ^ a)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_atTop ha).comp prime_root_real
  have hn := tendsto_neg_atTop_atBot.comp (h.const_mul_atTop hc)
  simpa only [Function.comp_def,neg_mul] using tendsto_exp_atBot.comp hn

theorem balance_decay : Tendsto (fun p : Prime => 4*(p.val.sqrt:ℝ)^2 * exp (-(p.val.sqrt:ℝ)/200000000)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2:ℝ) (1/200000000) (by norm_num)).comp prime_root_real
  have h' := h.const_mul (4:ℝ)
  simp only [mul_zero,Function.comp_apply,rpow_two] at h'
  apply h'.congr
  intro p
  rw [mul_assoc]
  congr 2
  ring_nf

theorem eventually_active : ∀ᶠ p : Prime in atTop, 5000 < log ((p.val:ℝ)/p.val.sqrt) := by
  filter_upwards [(tendsto_log_atTop.comp prime_root_real).eventually_gt_atTop 5000,
    prime_root.eventually_ge_atTop 1] with p h hk
  have hk0 : (0:ℝ)<p.val.sqrt := Nat.cast_pos.mpr (show 0 < p.val.sqrt by omega)
  apply h.trans_le (log_le_log hk0 ((le_div_iff₀ hk0).mpr ?_))
  change (p.val.sqrt:ℝ) * (p.val.sqrt:ℝ) ≤ (p.val:ℝ)
  exact_mod_cast Nat.sqrt_le p.val
end
end Green39.Assembly

end AssemblyRates

/- Source: one-percent-formal/assembly/AssemblyEndpoint.lean -/
section AssemblyEndpoint

/- Limiting composition along the primes for the uniform coverable proportion. -/

open Filter Topology Finset Real
open scoped Classical Pointwise
namespace Green39.Assembly
noncomputable section

local instance (p : Prime) : NeZero p.val := ⟨p.property.ne_zero⟩

def sliceCover (p : Prime) : ℝ := Concentration.sliceProbability (univ : Points p.val) p.val.sqrt (cover p.val)

/-- Only deterministic catalog data, a last-list counting estimate, and a
one-law deviation rate enter the endpoint. The exponents 0.46 and 0.70
allow slack above the transcript exponents 0.44 and 0.66. -/
theorem tendsto_zero_of_catalog (C : (p : Prime) → Catalog p.val) {L : ℝ} (hL : 0 ≤ L)
    (hstage : ∀ᶠ p in atTop, StageSpec (C p))
    (hterm : ∀ᶠ p in atTop, log (1 + (((C p).containers (C p).stages).card:ℝ)) ≤
      L * log (p.val:ℝ)^ (2:ℝ))
    (hlaws : ∀ᶠ p in atTop, ((allLaws (C p)).card:ℝ) ≤ exp ((p.val.sqrt:ℝ)^(0.46:ℝ)))
    (hcost : ∀ᶠ p in atTop,
      (∑ i ∈ range (C p).stages, (((C p).containers i).card:ℝ)*((C p).laws i).card) ≤
        exp ((p.val.sqrt:ℝ)^(0.70:ℝ)))
    (hsmooth : ∀ᶠ p : Prime in atTop, ∀ μ ∈ allLaws (C p),
      Split.probability (space p.val) (fun q => ¬typical μ q) ≤ exp (-((p.val.sqrt:ℝ)^(0.48:ℝ)))) :
    Tendsto sliceCover atTop (𝓝 0) := by
  let Ps := fun p : Prime => (C p).containers (C p).stages
  have hsize : ∀ᶠ p in atTop, ∀ P ∈ Ps p, (P.card:ℝ) ≤ exp 5000 * p.val.sqrt := by
    filter_upwards [hstage] with p hs P hP
    exact (hs.containerSize _ le_rfl P hP).trans (by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right (exp_le_exp.mpr hs.stop) (Nat.cast_nonneg _))
  have ht := Terminal.coversOutside_tendsto_one_primes Ps (ζ:=0.02) (exp_pos _).le
    (by norm_num) hL (by norm_num) hsize hterm
  let bad (p : Prime) := Concentration.sliceProbability (univ : Points p.val) p.val.sqrt (fun A => ¬ terminalOK (C p) A)
  have hb : Tendsto bad atTop (𝓝 0) := by
    have ht' := (tendsto_const_nhds (x:=(1:ℝ)) (f:=atTop (α:=Prime))).sub ht
    convert ht' using 1
    · funext p
      have h := Terminal.sliceProbability_add_compl (univ : Points p.val)
        (k:=p.val.sqrt) (by simpa using Nat.sqrt_le_self p.val) (terminalOK (C p))
      change _ = 1 - Concentration.sliceProbability _ _ (terminalOK (C p))
      unfold bad
      linarith
    · norm_num
  let k := fun p : Prime => (p.val.sqrt:ℝ)
  have hsu := exp_decay 0.48 0.5 (by norm_num) (by norm_num)
  have hhi := exp_decay 1 467 (by norm_num) (by norm_num)
  simp only [Real.rpow_one] at hhi
  have hupper := ((balance_decay.add hb).add hsu).add hhi
  simp only [add_zero] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Eventually.of_forall fun p => by unfold sliceCover; unfold Concentration.sliceProbability; positivity
  · have hsp := prime_cofinal.eventually (OnePercent.Fourier.sparsification_scale_eventually_sqrt 8 (by norm_num))
    filter_upwards [hstage,hlaws,hcost,hsmooth,prime_root.eventually_ge_atTop 100000,hsp,
      prime_root_real.eventually (power_margin (a:=0.46) (b:=0.48) (by norm_num) 2),
      prime_root_real.eventually (power_margin (a:=0.70) (b:=1) (by norm_num) 1)]
      with p spec hl hc hs hk hsp hmargin hcost'
    have hk0 : 0 < p.val.sqrt := by omega
    have hx : 0 ≤ log ((p.val:ℝ) / p.val.sqrt) := log_nonneg
      ((one_le_div (Nat.cast_pos.mpr hk0)).mpr (Nat.cast_le.mpr (Nat.sqrt_le_self _)))
    have hpar (i : ℕ) (_ : i < (C p).stages) : 8*log (4*(p.val:ℝ)) <
        (sMax p.val.sqrt:ℝ)*eta (x p.val i)^2 :=
      hsp _ (Transcripts.level_antitone hx (Nat.zero_le i))
    unfold sliceCover
    apply (cover_upper spec hk hpar _ hs).trans
    have hp := (numerical (p:=p.val) hk (Nat.lt_succ_sqrt' p.val)).1
    have h₁ : 2*(p.val:ℝ)*exp (-(k p)/200000000) ≤ 4*(k p)^2* exp (-(k p)/200000000) := by
      apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
      dsimp [k]; nlinarith [sq_nonneg (p.val.sqrt:ℝ)]
    have h₂ : ((allLaws (C p)).card:ℝ)*exp (-(k p ^ (0.48:ℝ))) ≤ exp (-0.5*k p ^ (0.48:ℝ)) := by
      apply (mul_le_mul_of_nonneg_right hl (exp_pos _).le).trans
      rw [←exp_add]; apply exp_le_exp.mpr; dsimp [k]; linarith
    have h₃ := mul_le_mul_of_nonneg_right hc (exp_pos (-468*k p)).le
    rw [←exp_add] at h₃
    have h₄ : exp (k p ^ (0.70:ℝ) + -468*k p) ≤ exp (-467*k p) := by
      apply exp_le_exp.mpr; simp only [rpow_one,one_mul] at hcost'; dsimp [k]; linarith
    exact add_le_add (add_le_add (add_le_add h₁ (le_refl (bad p))) h₂) (h₃.trans h₄)

end
end Green39.Assembly

end AssemblyEndpoint

/- Source: one-percent-formal/assembly/AssemblyUpstream.lean -/
section AssemblyUpstream

/- The rational upstream proportion is exactly the probability on the uniform slice. -/

open Finset Filter Topology
open scoped Pointwise Classical
namespace Green39.Assembly
noncomputable section

theorem upstream_eq_slice (p k c : ℕ) [NeZero p] (hk : k ≤ p) :
    (proportionCoverable p k c : ℝ) = Concentration.sliceProbability
      (univ : Finset (ZMod p)) k (fun A => ∃ T : Finset (ZMod p), T.card ≤ c ∧ A+T=univ) := by
  rw [proportionCoverable, dif_neg (NeZero.ne p),if_neg (not_lt_of_ge hk)]
  unfold Concentration.sliceProbability
  push_cast
  congr 2
  apply congrArg Finset.card
  ext A
  simp only [mem_filter]

theorem exact_negation
    (h : Tendsto (fun p : {q : ℕ // q.Prime} =>
      letI : NeZero p.val := ⟨p.property.ne_zero⟩
      let k := p.val.sqrt
      Concentration.sliceProbability (univ : Finset (ZMod p.val)) k
        (fun A => ∃ T : Finset (ZMod p.val), T.card ≤ ⌊1.01*(k:ℝ)⌋₊ ∧ A+T=univ)) atTop (𝓝 0)) :
    ¬ type_of% @Green39.green_39.variant_101 := by
  intro hup
  let : Nonempty {q : ℕ // q.Prime} := ⟨⟨2,Nat.prime_two⟩⟩
  apply zero_ne_one (tendsto_nhds_unique h _)
  convert hup using 1
  funext p
  let : NeZero p.val := ⟨p.property.ne_zero⟩
  exact (upstream_eq_slice _ _ _ (Nat.sqrt_le_self p.val)).symm

end
end Green39.Assembly

end AssemblyUpstream

/- Source: one-percent-formal/fitting/Fitting.lean -/
section Fitting

/- # Finite multiplicative-weights fitting for cyclic translate covers

The potential is cross entropy. Omitting the entropy of the fixed target
does not change the decrement, and permits zero target weights.
-/

namespace Green39.Fitting
open Finset Real
noncomputable section
variable {ι : Type*} [Fintype ι]

def testMean (m f : ι → ℝ) : ℝ := ∑ x, m x * f x
def normalizer (m f : ι → ℝ) (t : ℝ) : ℝ := ∑ x, m x * exp (t * f x)
def tilt (m f : ι → ℝ) (t : ℝ) (x : ι) : ℝ :=
  m x * exp (t * f x) / normalizer m f t
def potential (ν m : ι → ℝ) : ℝ := -∑ x, ν x * log (m x)

variable [Nonempty ι]

theorem normalizer_pos {m : ι → ℝ} (hm : ∀ x, 0 < m x) (f : ι → ℝ) (t : ℝ) :
    0 < normalizer m f t := by
  exact sum_pos (fun i _ => mul_pos (hm i) (exp_pos _)) univ_nonempty

theorem tilt_pos {m : ι → ℝ} (hm : ∀ x, 0 < m x) (f : ι → ℝ) (t : ℝ) (x : ι) :
    0 < tilt m f t x :=
  div_pos (mul_pos (hm x) (exp_pos _)) (normalizer_pos hm f t)

theorem sum_tilt {m : ι → ℝ} (hm : ∀ x, 0 < m x) (f : ι → ℝ) (t : ℝ) :
    ∑ x, tilt m f t x = 1 := by
  simp only [tilt, ← sum_div]
  exact div_self (normalizer_pos hm f t).ne'

theorem log_normalizer_le {m f : ι → ℝ} (hm : ∀ x, 0 < m x)
    (hs : ∑ x, m x = 1) (hf : ∀ x, |f x| ≤ 1) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    log (normalizer m f t) ≤ t * testMean m f + t^2 := by
  have hb (x : ι) : exp (t*f x) ≤ 1 + t*f x + t^2 := by
    have hab : |t*f x| ≤ t := by
      rw [abs_mul,abs_of_nonneg ht]
      simpa using mul_le_mul_of_nonneg_left (hf x) ht
    have he := (abs_le.mp (abs_exp_sub_one_sub_id_le (hab.trans ht'))).2
    have hsq := sq_le_sq.mpr (show |t*f x| ≤ |t| by simpa [abs_of_nonneg ht] using hab)
    linarith
  have hbound : normalizer m f t ≤ 1 + t*testMean m f + t^2 := calc
    _ ≤ ∑ x, m x * (1+t*f x+t^2) := sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (hb i) (hm i).le)
    _ = ∑ x, (m x + t*(m x*f x) + m x*t^2) := by
      apply sum_congr rfl
      intro x _
      ring
    _ = _ := by simp only [sum_add_distrib,←mul_sum,←sum_mul,hs,one_mul,testMean]
  linarith [log_le_sub_one_of_pos (normalizer_pos hm f t)]

theorem potential_tilt {m ν : ι → ℝ} (hm : ∀ x, 0 < m x) (hν : ∑ x, ν x = 1)
    (f : ι → ℝ) (t : ℝ) :
    potential ν (tilt m f t) = potential ν m - t*testMean ν f + log (normalizer m f t) := by
  have he (x : ι) : ν x * log (tilt m f t x) =
      ν x * log (m x) + t*(ν x * f x) - ν x * log (normalizer m f t) := by
    rw [tilt,log_div (mul_pos (hm x) (exp_pos _)).ne' (normalizer_pos hm f t).ne',
      log_mul (hm x).ne' (exp_pos _).ne',log_exp]
    ring
  simp only [potential,he,sum_sub_distrib,sum_add_distrib,←mul_sum,←sum_mul,hν,one_mul,testMean]
  ring

/-- A separating test decreases the fitting potential by at least η²/16. -/
theorem update_decrement {m ν f : ι → ℝ} (hm : ∀ x, 0 < m x)
    (hs : ∑ x, m x = 1) (hν : ∑ x, ν x = 1) (hf : ∀ x, |f x| ≤ 1)
    {η : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1) (hgap : η/2 ≤ testMean ν f - testMean m f) :
    potential ν (tilt m f (η/4)) ≤ potential ν m - η^2/16 := by
  rw [potential_tilt hm hν]
  have h := log_normalizer_le hm hs hf (t := η/4) (by positivity) (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hgap hη]

omit [Nonempty ι] in
theorem potential_nonneg {ν m : ι → ℝ} (hν : ∀ x, 0 ≤ ν x) (hm : ∀ x, 0 < m x)
    (hs : ∑ x, m x = 1) : 0 ≤ potential ν m := by
  apply neg_nonneg.mpr
  apply sum_nonpos
  intro x _
  have hle : m x ≤ 1 := hs ▸ single_le_sum (f := m) (fun i _ => (hm i).le) (mem_univ x)
  exact mul_nonpos_of_nonneg_of_nonpos (hν x) (log_nonpos (hm x).le hle)

omit [Nonempty ι] in
theorem uniform_potential {ν : ι → ℝ} (hν : ∑ x, ν x = 1) :
    potential ν (fun _ => (Fintype.card ι : ℝ)⁻¹) = log (Fintype.card ι : ℝ) := by
  simp [potential, ←sum_mul, hν]

/-- The trajectory depends only on the ordered instructions and the learning rate. -/
def trajectory (f : ℕ → ι → ℝ) (η : ℝ) : ℕ → ι → ℝ
  | 0 => fun _ => (Fintype.card ι : ℝ)⁻¹
  | n+1 => tilt (trajectory f η n) (f n) (η/4)

theorem trajectory_law (f : ℕ → ι → ℝ) (η : ℝ) (n : ℕ) :
    (∀ i, 0 < trajectory f η n i) ∧ ∑ i, trajectory f η n i = 1 := by
  induction n with
  | zero =>
    have hpos : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
    constructor
    · intro i
      exact inv_pos.mpr hpos
    · simp [trajectory,hpos.ne']
  | succ n ih =>
    exact ⟨tilt_pos ih.1 _ _, sum_tilt ih.1 _ _⟩

/-- Any sequence of valid separating instructions must stop by the stated bound.
The target may be supported on an arbitrary subset, and the tests may be adaptive. -/
theorem iterations_le {ν : ι → ℝ} (hν : ∀ x, 0 ≤ ν x) (hνs : ∑ x, ν x = 1)
    {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1) (f : ℕ → ι → ℝ) (n : ℕ)
    (hf : ∀ j < n, ∀ x, |f j x| ≤ 1)
    (hg : ∀ j < n, η/2 ≤ testMean ν (f j) - testMean (trajectory f η j) (f j)) :
    (n : ℝ) ≤ 16 * log (Fintype.card ι : ℝ) / η^2 := by
  have htel (j : ℕ) (hj : j ≤ n) :
      potential ν (trajectory f η j) + j*(η^2/16) ≤ log (Fintype.card ι : ℝ) := by
    induction j with
    | zero => simp [trajectory,uniform_potential hνs]
    | succ j ih =>
      have hj' : j < n := by omega
      obtain ⟨hp,hs⟩ := trajectory_law f η j
      have hd := update_decrement hp hs hνs (hf j hj') hη.le hη' (hg j hj')
      have hprev := ih hj'.le
      simp only [trajectory,Nat.cast_succ]
      linarith
  obtain ⟨hp,hs⟩ := trajectory_law f η n
  have h := potential_nonneg hν hp hs
  apply (le_div_iff₀ (sq_pos_of_pos hη)).mpr
  linarith [htel n le_rfl]


end
end Green39.Fitting

end Fitting

/- Source: one-percent-formal/fitting/CappedFit.lean -/
section CappedFit

/- # Truncation and normalized fitting for an arbitrary finite test family -/

namespace Green39.Fitting
open Finset Real
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def keep (J : Finset ι) (m : ι → ℝ) (x : ι) : ℝ := if x ∈ J then 0 else m x
def dropMass (J : Finset ι) (m : ι → ℝ) (x : ι) : ℝ := if x ∈ J then m x else 0
def clipped (J : Finset ι) (m : ι → ℝ) (x : ι) : ℝ := keep J m x / ∑ y, keep J m y

omit [Fintype ι] in
private theorem split_mass (J : Finset ι) (m : ι → ℝ) (x : ι) :
    keep J m x + dropMass J m x = m x := by by_cases hx : x ∈ J <;> simp [keep,dropMass,hx]

omit [DecidableEq ι] in
theorem abs_testMean_le {m f : ι → ℝ} (hm : ∀ x, 0 ≤ m x) (hf : ∀ x, |f x| ≤ 1) :
    |testMean m f| ≤ ∑ x, m x := calc
  _ ≤ ∑ x, |m x * f x| := abs_sum_le_sum_abs _ _
  _ ≤ _ := by
    apply sum_le_sum
    intro x _
    rw [abs_mul,abs_of_nonneg (hm x)]
    simpa using mul_le_mul_of_nonneg_left (hf x) (hm x)

/-- Deleting mass h and renormalizing changes every bounded test by at most 2h. -/
theorem clipped_test {m f : ι → ℝ} (J : Finset ι) (hm : ∀ x, 0 ≤ m x)
    (hs : ∑ x, m x = 1) (hf : ∀ x, |f x| ≤ 1) (hl : (∑ x, dropMass J m x) < 1) :
    |testMean (clipped J m) f - testMean m f| ≤ 2*∑ x, dropMass J m x := by
  let r := ∑ x, keep J m x
  let h := ∑ x, dropMass J m x
  have hk (x : ι) : 0 ≤ keep J m x := by simp [keep]; split <;> simp_all
  have hd (x : ι) : 0 ≤ dropMass J m x := by simp [dropMass]; split <;> simp_all
  have hm1 : r + h = 1 := by
    simpa [r,h,←sum_add_distrib,split_mass] using hs
  have hr : 0 < r := by change h < 1 at hl; linarith
  have hh : 0 ≤ h := sum_nonneg fun x _ => hd x
  have hmean : testMean m f = testMean (keep J m) f + testMean (dropMass J m) f := by
    simp only [testMean,←sum_add_distrib,←add_mul,split_mass]
  have hcmean : testMean (clipped J m) f = testMean (keep J m) f / r := by
    simp only [testMean,clipped,←sum_div,r,div_mul_eq_mul_div]
  have heq : testMean (clipped J m) f - testMean m f =
      (h/r)*testMean (keep J m) f - testMean (dropMass J m) f := by
    rw [hcmean,hmean]
    field_simp [hr.ne']
    linear_combination (testMean (keep J m) f) * (-hm1)
  rw [heq]
  calc
    _ ≤ |h/r * testMean (keep J m) f| + |testMean (dropMass J m) f| := abs_sub _ _
    _ ≤ h/r*r + h := by
      rw [abs_mul,abs_of_nonneg (div_nonneg hh hr.le)]
      exact add_le_add (mul_le_mul_of_nonneg_left (abs_testMean_le hk hf) (div_nonneg hh hr.le))
        (abs_testMean_le hd hf)
    _ = _ := by change h/r*r + h = 2*h; field_simp; ring

theorem clipped_law {m : ι → ℝ} {cap : ℝ} (hm : ∀ x, 0 ≤ m x) (hs : ∑ x, m x = 1)
    (hc : 0 ≤ cap) (J : Finset ι) (hout : ∀ x ∉ J, m x ≤ cap)
    (hl : (∑ x, dropMass J m x) ≤ 1/2) :
    (∑ x, clipped J m x = 1) ∧ ∀ x, 0 ≤ clipped J m x ∧ clipped J m x ≤ 2*cap := by
  have hh : (∑ x, keep J m x) + (∑ x, dropMass J m x) = 1 := by
    rw [←sum_add_distrib]; simpa only [split_mass] using hs
  have hr : 1 / 2 ≤ ∑ x, keep J m x := by linarith
  have hp : 0 < ∑ x, keep J m x := by linarith
  constructor
  · simp [clipped,←sum_div,hp.ne']
  · intro x
    have ha : 0 ≤ keep J m x := by by_cases h : x ∈ J <;> simp [keep,h,hm]
    have hb : keep J m x ≤ cap := by by_cases h : x ∈ J <;> simp [keep,h,hout,hc]
    exact ⟨div_nonneg ha hp.le,(div_le_iff₀ hp).mpr (by nlinarith [mul_nonneg hc (sub_nonneg.mpr hr)])⟩

end
end Green39.Fitting

end CappedFit

/- Source: one-percent-formal/fitting/FitSearch.lean -/
section FitSearch

/- # Target-independent decoding and finite termination of a fitting run -/

namespace Green39.Fitting
open Finset Real
noncomputable section
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι]

def heavy (cap : ℝ) (m : ι → ℝ) : Finset ι := univ.filter (fun i => cap < m i)
abbrev Instruction (σ : Type*) := Option (Bool × σ)

def testAt (g : σ → ι → ℝ) (cap : ℝ) (m : ι → ℝ) : Instruction σ → ι → ℝ
  | none, i => if i ∈ heavy cap m then -1 else 0
  | some (true,j), i => g j i
  | some (false,j), i => -g j i

def decode (g : σ → ι → ℝ) (η cap : ℝ) : List (Instruction σ) → ι → ℝ
  | [] => fun _ => (Fintype.card ι : ℝ)⁻¹
  | c :: cs =>
    let m := decode g η cap cs
    tilt m (testAt g cap m c) (η/4)

def stop (ν : ι → ℝ) (g : σ → ι → ℝ) (η cap : ℝ) (m : ι → ℝ) : Prop :=
  let J := heavy cap m
  η/2 ≤ ∑ i, dropMass J ν i ∨
    ((∑ i, clipped J m i = 1) ∧ (∀ i, 0 ≤ clipped J m i ∧ clipped J m i ≤ 2*cap) ∧
    ∀ j, |testMean ν (g j) - testMean (clipped J m) (g j)| ≤ 3*η)

theorem testAt_bound {g : σ → ι → ℝ} (hg : ∀ j i, |g j i| ≤ 1)
    (cap : ℝ) (m : ι → ℝ) (c : Instruction σ) (i : ι) : |testAt g cap m c i| ≤ 1 := by
  cases c with
  | none => by_cases h : i ∈ heavy cap m <;> simp [testAt,h]
  | some c => rcases c with ⟨b,j⟩; cases b <;> simpa [testAt] using hg j i

private theorem heavy_mean (q m : ι → ℝ) (g : σ → ι → ℝ) (cap : ℝ) :
    testMean q (testAt g cap m none) = -(∑ i, dropMass (heavy cap m) q i) := by
  unfold testMean
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro i _
  by_cases h : i ∈ heavy cap m <;> simp [testAt,dropMass,h]

theorem stop_or_update {m ν : ι → ℝ} {g : σ → ι → ℝ} {η cap : ℝ}
    (hg : ∀ j i, |g j i| ≤ 1) (hm : ∀ i, 0 < m i) (hs : ∑ i, m i = 1)
    (hc : 0 ≤ cap) (he : 0 ≤ η) (he' : η ≤ 1/2) :
    stop ν g η cap m ∨ ∃ c : Instruction σ,
      η/2 ≤ testMean ν (testAt g cap m c) - testMean m (testAt g cap m c) := by
  classical
  by_cases ht : η/2 ≤ ∑ i, dropMass (heavy cap m) ν i
  · exact Or.inl (Or.inl ht)
  by_cases hw : η < ∑ i, dropMass (heavy cap m) m i
  · refine Or.inr ⟨none,?_⟩
    rw [heavy_mean,heavy_mean]
    linarith
  have hsmall := le_of_not_gt hw
  by_cases htests : ∀ j, |testMean ν (g j)-testMean m (g j)| ≤ η/2
  · have h := clipped_law (fun i => (hm i).le) hs hc (heavy cap m)
        (fun x hx => le_of_not_gt (fun h => hx (mem_filter.mpr ⟨mem_univ _,h⟩)))
        (hsmall.trans he')
    refine Or.inl (Or.inr ⟨h.1,h.2,fun j => ?_⟩)
    have hh := clipped_test (heavy cap m) (fun i => (hm i).le) hs (hg j) (by linarith)
    have hb := abs_sub_le (testMean ν (g j)) (testMean m (g j)) (testMean (clipped (heavy cap m) m) (g j))
    rw [abs_sub_comm (testMean m (g j))] at hb
    linarith [htests j]
  · push Not at htests
    obtain ⟨j,hj⟩ := htests
    rcases lt_abs.mp hj with h | h
    · refine Or.inr ⟨some (true,j),?_⟩
      change η/2 ≤ testMean ν (g j) - testMean m (g j)
      exact h.le
    · refine Or.inr ⟨some (false,j),?_⟩
      simp only [testAt,testMean,mul_neg,sum_neg_distrib] at *
      linarith

variable [Nonempty ι]

theorem decode_law (g : σ → ι → ℝ) (η cap : ℝ) (cs : List (Instruction σ)) :
    (∀ i, 0 < decode g η cap cs i) ∧ ∑ i, decode g η cap cs i = 1 := by
  induction cs with
  | nil => exact trajectory_law (fun _ _ => 0) η 0
  | cons c cs ih => exact ⟨tilt_pos ih.1 _ _,sum_tilt ih.1 _ _⟩

/-- The list of possible transcripts is independent of ν. Reading the successful word
from the right reconstructs the heavy set or capped law that witnesses termination. -/
theorem finite_search {ν : ι → ℝ} (hν : ∀ i, 0 ≤ ν i) (hνs : ∑ i, ν i = 1)
    {g : σ → ι → ℝ} (hg : ∀ j i, |g j i| ≤ 1) {η cap : ℝ} (he : 0 < η)
    (he' : η ≤ 1/2) (hc : 0 ≤ cap) (B : ℕ) (hB : 16*log (Fintype.card ι) < B*η^2) :
    ∃ cs : List (Instruction σ), cs.length ≤ B ∧ stop ν g η cap (decode g η cap cs) := by
  classical
  by_contra! hx
  have extend (j : ℕ) (hj : j ≤ B) : ∃ cs : List (Instruction σ), cs.length = j ∧
      potential ν (decode g η cap cs) + j*(η^2/16) ≤ log (Fintype.card ι) := by
    induction j with
    | zero => exact ⟨[],rfl,by simp [decode,uniform_potential hνs]⟩
    | succ j ih =>
      have hj' : j ≤ B := by omega
      obtain ⟨cs,hlen,hold⟩ := ih hj'
      obtain ⟨hm,hs⟩ := decode_law g η cap cs
      obtain ⟨c,hgap⟩ := (stop_or_update hg hm hs hc he.le he').resolve_left
        (hx cs (hlen ▸ hj'))
      have hd := update_decrement hm hs hνs (testAt_bound hg cap _ c) he.le (by linarith) hgap
      refine ⟨c::cs,by simp [hlen],?_⟩
      simp only [decode,Nat.cast_succ]
      linarith
  obtain ⟨cs,_,h⟩ := extend B le_rfl
  obtain ⟨hm,hs⟩ := decode_law g η cap cs
  linarith [potential_nonneg hν hm hs]

end
end Green39.Fitting

end FitSearch

/- Source: one-percent-formal/fitting/FitStage.lean -/
section FitStage

/- # Peeling a finite target using short, target-independent instructions -/

namespace Green39.Fitting
open Finset Real
noncomputable section
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι]

def uniformOn (F : Finset ι) (i : ι) : ℝ := if i ∈ F then (F.card : ℝ)⁻¹ else 0

omit [Fintype ι] in
theorem uniformOn_nonneg (F : Finset ι) (i : ι) : 0 ≤ uniformOn F i := by
  by_cases hi : i ∈ F <;> simp [uniformOn,hi]

theorem uniformOn_sum {F : Finset ι} (hF : F.Nonempty) : ∑ i, uniformOn F i = 1 := by
  classical
  simp [uniformOn,Finset.sum_ite_mem, (show (F.card : ℝ) ≠ 0 by exact_mod_cast hF.card_pos.ne')]

theorem uniformOn_drop (F J : Finset ι) :
    ∑ i, dropMass J (uniformOn F) i = ((J ∩ F).card : ℝ) / (F.card : ℝ) := by
  classical
  have h (i : ι) : dropMass J (uniformOn F) i =
      if i ∈ J ∩ F then (F.card : ℝ)⁻¹ else 0 := by
    by_cases hi : i ∈ J <;> by_cases hf : i ∈ F <;> simp [dropMass,uniformOn,hi,hf]
  simp only [h,Finset.sum_ite_mem,Finset.univ_inter,sum_const,nsmul_eq_mul,div_eq_mul_inv]

def Fitted (F : Finset ι) (g : σ → ι → ℝ) (η cap : ℝ) (μ : ι → ℝ) : Prop :=
  (∑ i, μ i = 1) ∧ (∀ i, 0 ≤ μ i ∧ μ i ≤ 2*cap) ∧
  ∀ j, |testMean (uniformOn F) (g j) - testMean μ (g j)| ≤ 3*η

def recordedUnion (g : σ → ι → ℝ) (η cap : ℝ) : List (List (Instruction σ)) → Finset ι
  | [] => ∅
  | w :: ws => heavy cap (decode g η cap w) ∪ recordedUnion g η cap ws

variable [Nonempty ι]

/-- One round of the fitting procedure. The pool of words and all laws and unions
decoded from them are determined by the tests, cap, accuracy and budgets. -/
theorem stage_alternative {g : σ → ι → ℝ} (hg : ∀ j i, |g j i| ≤ 1)
    {η cap θ : ℝ} (he : 0 < η) (he' : η ≤ 1/2) (hc : 0 ≤ cap) (ht : 0 < θ)
    (B : ℕ) (hB : 16*log (Fintype.card ι) < B*η^2)
    (n : ℕ) (V : Finset ι) (hN : (1-η/2)^n * V.card < θ) :
    (∃ F ⊆ V, θ ≤ F.card ∧ ∃ w : List (Instruction σ), w.length ≤ B ∧
      Fitted F g η cap (clipped (heavy cap (decode g η cap w)) (decode g η cap w))) ∨
    (∃ ws : List (List (Instruction σ)), ws.length ≤ n ∧ (∀ w ∈ ws, w.length ≤ B) ∧
      ((V \ recordedUnion g η cap ws).card : ℝ) < θ) := by
  classical
  induction n generalizing V with
  | zero => exact Or.inr ⟨[],by simp,by simp,by simpa [recordedUnion] using hN⟩
  | succ n ih =>
    by_cases hv : (V.card : ℝ) < θ
    · exact Or.inr ⟨[],by simp,by simp,by simpa [recordedUnion] using hv⟩
    have hp : V.Nonempty := by
      apply card_pos.mp
      exact_mod_cast ht.trans_le (le_of_not_gt hv)
    obtain ⟨w,hw,hstop⟩ := finite_search (uniformOn_nonneg V) (uniformOn_sum hp) hg he he' hc B hB
    let J := heavy cap (decode g η cap w)
    rcases hstop with hpeel | hfit
    · change η / 2 ≤ ∑ i, dropMass J (uniformOn V) i at hpeel
      rw [uniformOn_drop] at hpeel
      have hsize := (le_div_iff₀ (show 0 < (V.card : ℝ) by exact_mod_cast hp.card_pos)).mp hpeel
      have hcard : (V \ J).card + (J ∩ V).card = V.card := by
        rw [inter_comm J V]
        exact card_sdiff_add_card_inter V J
      have hleft : ((V \ J).card : ℝ) ≤ (1-η/2)*V.card := by
        have hh : ((V \ J).card : ℝ) + (J ∩ V).card = V.card := by exact_mod_cast hcard
        linarith
      have hnext : (1-η/2)^n * (V \ J).card < θ := by
        apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left hleft
          (pow_nonneg (by linarith : 0 ≤ 1-η/2) _))
        simpa [pow_succ,mul_assoc] using hN
      rcases ih (V \ J) hnext with ⟨F,hF,hF',w',hw',hf'⟩ | ⟨ws,hws,hs,hsmall⟩
      · exact Or.inl ⟨F,hF.trans sdiff_subset,hF',w',hw',hf'⟩
      · refine Or.inr ⟨w::ws,by simpa using hws,?_,?_⟩
        · intro u hu
          rcases List.mem_cons.mp hu with rfl | hu
          · exact hw
          · exact hs u hu
        · have heq : V \ recordedUnion g η cap (w::ws) = (V \ J) \ recordedUnion g η cap ws := by
            ext i
            simp [recordedUnion,J]
            tauto
          simpa only [heq] using hsmall
    · exact Or.inl ⟨V,Subset.rfl,le_of_not_gt hv,w,hw,hfit⟩

end
end Green39.Fitting

end FitStage

/- Source: one-percent-formal/fitting/FitFourier.lean -/
section FitFourier

/- # A finite, deterministically decodable Fourier fit or a small uncovered remainder -/

namespace Green39.Fitting
open Finset Real
noncomputable section
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι]

def realTests (χ : σ → ι → ℂ) (j : σ × Bool) (i : ι) : ℝ :=
  if j.2 then (χ j.1 i).re else (χ j.1 i).im

def transform (χ : σ → ι → ℂ) (m : ι → ℝ) (j : σ) : ℂ :=
  ∑ i, χ j i * (m i : ℂ)

omit [Fintype ι] [DecidableEq ι] in
theorem realTests_bound {χ : σ → ι → ℂ} (h : ∀ j i, ‖χ j i‖ ≤ 1) :
    ∀ j i, |realTests χ j i| ≤ 1 := by
  rintro ⟨j,b⟩ i
  cases b
  · exact (Complex.abs_im_le_norm _).trans (h j i)
  · exact (Complex.abs_re_le_norm _).trans (h j i)

omit [DecidableEq ι] in
private theorem transform_re (χ : σ → ι → ℂ) (m : ι → ℝ) (j : σ) :
    (transform χ m j).re = testMean m (realTests χ (j,true)) := by
  simp [transform,testMean,realTests,Complex.re_sum,Complex.mul_re,mul_comm]

omit [DecidableEq ι] in
private theorem transform_im (χ : σ → ι → ℂ) (m : ι → ℝ) (j : σ) :
    (transform χ m j).im = testMean m (realTests χ (j,false)) := by
  simp [transform,testMean,realTests,Complex.im_sum,Complex.mul_im,mul_comm]

theorem fourier_fit_of_fitted {F : Finset ι} {χ : σ → ι → ℂ} {η cap : ℝ} {μ : ι → ℝ}
    (he : 0 ≤ η) (hf : Fitted F (realTests χ) η cap μ) (j : σ) :
    ‖transform χ (uniformOn F) j - transform χ μ j‖ ≤ 5*η := by
  let z := transform χ (uniformOn F) j - transform χ μ j
  have hr : |z.re| ≤ 3*η := by simpa only [z,Complex.sub_re,transform_re] using hf.2.2 (j,true)
  have hi : |z.im| ≤ 3*η := by simpa only [z,Complex.sub_im,transform_im] using hf.2.2 (j,false)
  have hrs := sq_le_sq.mpr (show |z.re| ≤ |3*η| by simpa [abs_of_nonneg (by positivity : 0 ≤ 3*η)] using hr)
  have his := sq_le_sq.mpr (show |z.im| ≤ |3*η| by simpa [abs_of_nonneg (by positivity : 0 ≤ 3*η)] using hi)
  have hz := Complex.sq_norm z
  rw [Complex.normSq_apply] at hz
  change ‖z‖ ≤ 5*η
  nlinarith [norm_nonneg z,sq_nonneg η]

theorem cyclic_transform {p : ℕ} [NeZero p] (m : ZMod p → ℝ) (j : ZMod p) :
    transform (fun t i : ZMod p => ZMod.stdAddChar (-(i*t))) m j =
      ZMod.dft (fun i => (m i : ℂ)) j := by
  simp only [transform,ZMod.dft_apply,smul_eq_mul]

omit [DecidableEq ι] in
theorem heavy_card {m : ι → ℝ} (hm : ∀ x, 0 ≤ m x) (hs : ∑ x, m x = 1)
    {cap : ℝ} (hc : 0 < cap) : ((heavy cap m).card : ℝ) ≤ 1/cap := by
  apply (le_div_iff₀ hc).mpr
  calc
    _ = ∑ _ ∈ heavy cap m, cap := by simp
    _ ≤ ∑ i ∈ heavy cap m, m i := by
       apply sum_le_sum
       intro i hi
       exact (mem_filter.mp hi).2.le
    _ ≤ ∑ i, m i := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _ => hm i)
    _ = _ := hs

theorem recordedUnion_card [Nonempty ι] (g : σ → ι → ℝ) (η : ℝ) {cap : ℝ}
    (hc : 0 < cap) (ws : List (List (Instruction σ))) :
    ((recordedUnion g η cap ws).card : ℝ) ≤ ws.length / cap := by
  induction ws with
  | nil => simp [recordedUnion]
  | cons w ws ih =>
    let J := heavy cap (decode g η cap w)
    have hsub : (recordedUnion g η cap (w::ws)).card ≤ J.card + (recordedUnion g η cap ws).card :=
      card_union_le _ _
    obtain ⟨hm,hs⟩ := decode_law g η cap w
    have hJ := heavy_card (fun i => (hm i).le) hs hc
    calc
      ((recordedUnion g η cap (w::ws)).card : ℝ)
          ≤ (J.card : ℝ) + (recordedUnion g η cap ws).card := by exact_mod_cast hsub
      _ ≤ 1/cap + ws.length/cap := add_le_add hJ ih
      _ = _ := by simp [add_div,add_comm]

def cyclicTests (p : ℕ) [NeZero p] := realTests (fun t i : ZMod p => ZMod.stdAddChar (-(i*t)))

def fittedLaw {p : ℕ} [NeZero p] (η cap : ℝ) (w : List (Instruction (ZMod p × Bool))) :
    ZMod p → ℝ :=
  let m := decode (cyclicTests p) η cap w
  clipped (heavy cap m) m

/-- The §3 dichotomy with a uniform Fourier error 5η, explicit decoder, bounds on both
transcript lengths, and the size of each decoded container. -/
theorem cyclic_stage {p : ℕ} [NeZero p] {η cap θ : ℝ} (he : 0 < η)
    (he' : η ≤ 1/2) (hc : 0 < cap) (ht : 0 < θ)
    (B n : ℕ) (hB : 16*log p < B*η^2) (V : Finset (ZMod p))
    (hN : (1-η/2)^n * V.card < θ) :
    (∃ F ⊆ V, θ ≤ F.card ∧ ∃ w : List (Instruction (ZMod p × Bool)), w.length ≤ B ∧
      let μ := fittedLaw η cap w
      (∑ i, μ i = 1) ∧ (∀ i, 0 ≤ μ i ∧ μ i ≤ 2*cap) ∧ ∀ j : ZMod p,
      ‖ZMod.dft (fun i => (uniformOn F i : ℂ)) j - ZMod.dft (fun i => (μ i : ℂ)) j‖ ≤ 5*η) ∨
    (∃ ws : List (List (Instruction (ZMod p × Bool))), ws.length ≤ n ∧ (∀ w ∈ ws, w.length ≤ B) ∧
      let P := recordedUnion (cyclicTests p) η cap ws
      (P.card : ℝ) ≤ n/cap ∧ ((V \ P).card : ℝ) < θ) := by
  have hg : ∀ j i, |cyclicTests p j i| ≤ 1 := by
    apply realTests_bound
    intro j i
    simp
  have hh := stage_alternative hg he he' hc.le ht B (by simpa [ZMod.card] using hB) n V hN
  rcases hh with ⟨F,hFV,hs,w,hw,hf⟩ | ⟨ws,hn,hlen,hrem⟩
  · refine Or.inl ⟨F,hFV,hs,w,hw,hf.1,hf.2.1,?_⟩
    intro j
    simpa only [fittedLaw,cyclic_transform] using fourier_fit_of_fitted he.le hf j
  · refine Or.inr ⟨ws,hn,hlen,?_,hrem⟩
    exact (recordedUnion_card (cyclicTests p) η hc ws).trans
      (div_le_div_of_nonneg_right (by exact_mod_cast hn) hc.le)


end
end Green39.Fitting

end FitFourier

/- Source: one-percent-formal/fitting/FitParameters.lean -/
section FitParameters

/- # Explicit instruction and removal budgets for the fitting stage -/

namespace Green39.Fitting
open Real
noncomputable section

def wordBudget (p : ℕ) (η : ℝ) : ℕ := ⌊16*log p / η^2⌋₊ + 1
def peelBudget (η ξ : ℝ) : ℕ := ⌊(2/η)*log (2/ξ)⌋₊ + 1

theorem wordBudget_spec (p : ℕ) {η : ℝ} (he : 0 < η) :
    16*log p < (wordBudget p η : ℝ)*η^2 := by
  apply (div_lt_iff₀ (sq_pos_of_pos he)).mp
  simpa [wordBudget] using Nat.lt_floor_add_one (16*log p/η^2)

theorem peelBudget_spec {η ξ : ℝ} (he : 0 < η) (he' : η ≤ 1/2) (hξ : 0 < ξ) :
    (1-η/2)^(peelBudget η ξ) < ξ/2 := by
  let n := peelBudget η ξ
  have hn : (2/η)*log (2/ξ) < (n : ℝ) := by
    simpa [n,peelBudget] using Nat.lt_floor_add_one ((2/η)*log (2/ξ))
  have hlog : log (2/ξ) < (n : ℝ)*η/2 := by
    have hh := mul_lt_mul_of_pos_right hn he
    field_simp [ne_of_gt he] at hh
    linarith
  have hx : 1-η/2 ≤ exp (-(η/2)) := by linarith [add_one_le_exp (-(η/2))]
  calc
    _ ≤ exp (-(η/2))^n := pow_le_pow_left₀ (by linarith) hx _
    _ = exp ((n:ℝ)*(-(η/2))) := (exp_nat_mul _ _).symm
    _ < exp (-log (2/ξ)) := exp_lt_exp.mpr (by linarith)
    _ = _ := by rw [exp_neg,exp_log (by positivity)]; field_simp

theorem wordBudget_le (p : ℕ) (hp : 1 ≤ p) {η : ℝ} (he : 0 < η) :
    (wordBudget p η : ℝ) ≤ 16*log p/η^2 + 1 := by
  simp only [wordBudget,Nat.cast_add,Nat.cast_one,add_le_add_iff_right]
  exact Nat.floor_le (div_nonneg (mul_nonneg (by norm_num)
    (log_nonneg (by exact_mod_cast hp))) (sq_pos_of_pos he).le)

theorem peelBudget_le {η ξ : ℝ} (he : 0 < η) (hξ : 0 < ξ) (hξ' : ξ ≤ 1) :
    (peelBudget η ξ : ℝ) ≤ (2/η)*log (2/ξ) + 1 := by
  simp only [peelBudget,Nat.cast_add,Nat.cast_one,add_le_add_iff_right]
  exact Nat.floor_le (mul_nonneg (by positivity) (log_nonneg ((le_div_iff₀ hξ).mpr (by linarith))))

/-- In particular a successful transcript never uses an implicit search-depth parameter. -/
theorem cyclic_stage_explicit {p : ℕ} [NeZero p] (V : Finset (ZMod p)) {k η ξ K : ℝ}
    (hk : 0 < k) (hV : V.card ≤ 2*k) (he : 0 < η) (he' : η ≤ 1/2)
    (hξ : 0 < ξ) (hK : 0 < K) :
    (∃ F ⊆ V, ξ*k ≤ F.card ∧ ∃ w : List (Instruction (ZMod p × Bool)),
      w.length ≤ wordBudget p η ∧
      let μ := fittedLaw η (1/(K*k)) w
      (∑ i, μ i = 1) ∧ (∀ i, 0 ≤ μ i ∧ μ i ≤ 2*(1/(K*k))) ∧ ∀ j : ZMod p,
      ‖ZMod.dft (fun i => (uniformOn F i : ℂ)) j - ZMod.dft (fun i => (μ i : ℂ)) j‖ ≤ 5*η) ∨
    (∃ ws : List (List (Instruction (ZMod p × Bool))), ws.length ≤ peelBudget η ξ ∧
      (∀ w ∈ ws, w.length ≤ wordBudget p η) ∧
      let P := recordedUnion (cyclicTests p) η (1/(K*k)) ws
      (P.card : ℝ) ≤ (peelBudget η ξ : ℝ) / (1/(K*k)) ∧ ((V \ P).card : ℝ) < ξ*k) := by
  apply cyclic_stage he he' (by positivity) (by positivity) _ _ (wordBudget_spec p he) V
  calc
    _ ≤ (1-η/2)^peelBudget η ξ * (2*k) :=
      mul_le_mul_of_nonneg_left hV (pow_nonneg (by linarith) _)
    _ < (ξ/2)*(2*k) := mul_lt_mul_of_pos_right (peelBudget_spec he he' hξ) (by positivity)
    _ = _ := by ring

end
end Green39.Fitting

end FitParameters

/- Source: one-percent-formal/transcripts/TranscriptCount.lean -/
section TranscriptCount

/- Finite decoding and counting for the restarted runs in §3. -/

namespace Green39.Transcripts

open Finset

/-- The four signed tests for each frequency, plus the state-dependent heavy-set test. -/
abbrev Instruction (p : ℕ) := (Fin 4 × Fin p) ⊕ Unit

theorem card_instruction (p : ℕ) : Fintype.card (Instruction p) = 4 * p + 1 := by
  simp

variable {A : Type*} [DecidableEq A]

/-- All ordered words of length at most the budget in the given finite alphabet. -/
def words (alphabet : Finset A) : ℕ → Finset (List A)
  | 0 => {[]}
  | n + 1 => insert [] ((alphabet ×ˢ words alphabet n).image fun aw => aw.1 :: aw.2)

theorem mem_words {alphabet : Finset A} {n : ℕ} {w : List A} :
    w ∈ words alphabet n ↔ w.length ≤ n ∧ ∀ a ∈ w, a ∈ alphabet := by
  induction n generalizing w with
  | zero => cases w <;> simp [words]
  | succ n ih =>
    cases w with
    | nil => simp [words]
    | cons a w =>
      simp [words, ih, forall_eq_or_imp, and_assoc, and_left_comm, and_comm]

/-- The exact number of words, including the empty word. -/
def wordCount (a : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => 1 + a * wordCount a n

theorem wordCount_eq_sum (a n : ℕ) :
    wordCount a n = ∑ i ∈ range (n + 1), a ^ i := by
  induction n with
  | zero => simp [wordCount]
  | succ n ih =>
    rw [wordCount, ih, sum_range_succ' (fun i => a ^ i) (n + 1), mul_sum, pow_zero]
    simp only [pow_succ', Nat.add_comm 1]

theorem card_words (alphabet : Finset A) (n : ℕ) :
    (words alphabet n).card = wordCount alphabet.card n := by
  induction n with
  | zero => simp [words, wordCount]
  | succ n ih =>
    have hnil : [] ∉ (alphabet ×ˢ words alphabet n).image
        (fun aw : A × List A => aw.1 :: aw.2) := by simp
    have hinj : Function.Injective (fun aw : A × List A => aw.1 :: aw.2) := by
      rintro ⟨a, w⟩ ⟨b, v⟩ h
      simpa using h
    rw [words, card_insert_of_notMem hnil, card_image_of_injective _ hinj,
      card_product, ih, wordCount, Nat.add_comm]

theorem wordCount_le (a n : ℕ) : wordCount a n ≤ (a + 1) ^ n := by
  induction n with
  | zero => simp [wordCount]
  | succ n ih =>
    rw [wordCount]
    calc
      1 + a * wordCount a n ≤ (a + 1) ^ n + a * (a + 1) ^ n :=
        Nat.add_le_add (Nat.one_le_pow _ _ (by omega)) (Nat.mul_le_mul_left a ih)
      _ = (a + 1) ^ (n + 1) := by rw [pow_succ]; ring

/-- A fixed stage can replay a run from its reset state. The step reads the current
state, so the heavy-set instruction needs no additional symbol for the set. -/
structure Stage (State A Law Point : Type*) where
  reset : State
  step : State → A → State
  law : State → Law
  heavy : State → Finset Point

variable {State Law Point : Type*}

def Stage.replay (stage : Stage State A Law Point) (record : List A) : State :=
  record.foldl stage.step stage.reset

def Stage.outputLaw (stage : Stage State A Law Point) (record : List A) : Law :=
  stage.law (stage.replay record)

def Stage.outputHeavy (stage : Stage State A Law Point) (record : List A) : Finset Point :=
  stage.heavy (stage.replay record)

variable [DecidableEq Point]

/-- All records in the outer word are decoded from the same reset. -/
def Stage.outputContainer (stage : Stage State A Law Point) : List (List A) → Finset Point
  | [] => ∅
  | record :: rest => stage.outputHeavy record ∪ stage.outputContainer rest

omit [DecidableEq A] [DecidableEq Point] in
/-- A run starting in the prescribed reset state has the replayed state. -/
theorem Stage.replay_eq_of_reset (stage : Stage State A Law Point)
    {start : State} (h : start = stage.reset) (record : List A) :
    record.foldl stage.step start = stage.replay record := by
  subst start
  rfl

omit [DecidableEq A] [DecidableEq Point] in
/-- Any two input histories selecting the same current record have the same output,
provided both start in the prescribed reset state. -/
theorem Stage.history_independent (stage : Stage State A Law Point)
    {History : Type*} (start : History → State) (h : ∀ history, start history = stage.reset)
    (left right : History) (record : List A) :
    record.foldl stage.step (start left) = record.foldl stage.step (start right) := by
  rw [h left, h right]

omit [DecidableEq A] in
/-- The container formed by an implementation that resets each run belongs to the same
stage-only decoding, even if the implementation uses an arbitrary start function. -/
theorem Stage.container_eq_of_reset (stage : Stage State A Law Point)
    (start : List A → State) (h : ∀ record, start record = stage.reset)
    (records : List (List A)) :
    (records.map (fun record => stage.heavy (record.foldl stage.step (start record)))).foldr
        (· ∪ ·) ∅ = stage.outputContainer records := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
    simp only [List.map_cons, List.foldr_cons, Stage.outputContainer]
    rw [ih, stage.replay_eq_of_reset (h record)]
    rfl

def Stage.lawList [DecidableEq Law] (stage : Stage State A Law Point)
    (alphabet : Finset A) (runBudget : ℕ) : Finset Law :=
  (words alphabet runBudget).image stage.outputLaw

def Stage.containerList (stage : Stage State A Law Point)
    (alphabet : Finset A) (runBudget removalBudget : ℕ) : Finset (Finset Point) :=
  (words (words alphabet runBudget) removalBudget).image stage.outputContainer

omit [DecidableEq Point] in
theorem Stage.outputLaw_mem [DecidableEq Law] (stage : Stage State A Law Point)
    {alphabet : Finset A} {runBudget : ℕ} {record : List A}
    (hlen : record.length ≤ runBudget) (hsym : ∀ a ∈ record, a ∈ alphabet) :
    stage.outputLaw record ∈ stage.lawList alphabet runBudget :=
  mem_image_of_mem _ (mem_words.mpr ⟨hlen, hsym⟩)

theorem Stage.outputContainer_mem (stage : Stage State A Law Point)
    {alphabet : Finset A} {runBudget removalBudget : ℕ} {records : List (List A)}
    (hlen : records.length ≤ removalBudget)
    (hword : ∀ record ∈ records, record.length ≤ runBudget ∧ ∀ a ∈ record, a ∈ alphabet) :
    stage.outputContainer records ∈ stage.containerList alphabet runBudget removalBudget :=
  mem_image_of_mem _ (mem_words.mpr ⟨hlen, fun record hr => mem_words.mpr (hword record hr)⟩)

/-- In particular the empty union appears even if the removal budget is zero. -/
theorem Stage.empty_mem_containerList (stage : Stage State A Law Point)
    (alphabet : Finset A) (runBudget removalBudget : ℕ) :
    ∅ ∈ stage.containerList alphabet runBudget removalBudget := by
  simpa [Stage.outputContainer] using stage.outputContainer_mem
    (alphabet := alphabet) (runBudget := runBudget) (removalBudget := removalBudget)
    (records := []) (by simp) (by simp)

/-- One fixed list covers the implementation's output for every prior history.
The selected words may depend on the history, but their decoding never does. -/
theorem Stage.container_mem_of_history (stage : Stage State A Law Point)
    {History : Type*} (records : History → List (List A)) (start : History → List A → State)
    (hreset : ∀ history record, start history record = stage.reset)
    (alphabet : Finset A) (runBudget removalBudget : ℕ)
    (hlen : ∀ history, (records history).length ≤ removalBudget)
    (hword : ∀ history record, record ∈ records history →
      record.length ≤ runBudget ∧ ∀ a ∈ record, a ∈ alphabet)
    (history : History) :
    ((records history).map (fun record =>
      stage.heavy (record.foldl stage.step (start history record)))).foldr (· ∪ ·) ∅ ∈
      stage.containerList alphabet runBudget removalBudget := by
  rw [stage.container_eq_of_reset (start history) (hreset history)]
  exact stage.outputContainer_mem (hlen history) (hword history)

omit [DecidableEq Point] in
theorem Stage.card_lawList_le [DecidableEq Law] (stage : Stage State A Law Point)
    (alphabet : Finset A) (runBudget : ℕ) :
    (stage.lawList alphabet runBudget).card ≤ wordCount alphabet.card runBudget :=
  card_words alphabet runBudget ▸ card_image_le

theorem Stage.card_containerList_le (stage : Stage State A Law Point)
    (alphabet : Finset A) (runBudget removalBudget : ℕ) :
    (stage.containerList alphabet runBudget removalBudget).card ≤
      wordCount (wordCount alphabet.card runBudget) removalBudget := by
  unfold Stage.containerList
  exact card_image_le.trans (by rw [card_words, card_words])

omit [DecidableEq A] in
theorem Stage.card_outputContainer_le (stage : Stage State A Law Point)
    (records : List (List A)) (heavyBudget : ℕ)
    (h : ∀ record ∈ records, (stage.outputHeavy record).card ≤ heavyBudget) :
    (stage.outputContainer records).card ≤ records.length * heavyBudget := by
  induction records with
  | nil => simp [Stage.outputContainer]
  | cons record rest ih =>
    rw [Stage.outputContainer, List.length_cons, Nat.add_mul, Nat.one_mul]
    exact (card_union_le _ _).trans (by
      have hfirst := h record List.mem_cons_self
      have hrest := ih (fun w hw => h w (List.mem_cons_of_mem _ hw))
      omega)

theorem Stage.card_mem_containerList_le (stage : Stage State A Law Point)
    (alphabet : Finset A) (runBudget removalBudget heavyBudget : ℕ)
    (h : ∀ record ∈ words alphabet runBudget, (stage.outputHeavy record).card ≤ heavyBudget)
    {container : Finset Point} (hmem : container ∈ stage.containerList alphabet runBudget removalBudget) :
    container.card ≤ removalBudget * heavyBudget := by
  obtain ⟨records, hrecords, rfl⟩ := mem_image.mp hmem
  obtain ⟨hlen, hwords⟩ := mem_words.mp hrecords
  exact (stage.card_outputContainer_le records heavyBudget
    (fun record hr => h record (hwords record hr))).trans (Nat.mul_le_mul_right _ hlen)

end Green39.Transcripts

end TranscriptCount

/- Source: one-percent-formal/transcripts/TranscriptBounds.lean -/
section TranscriptBounds

/- Finite logarithmic bounds for the one-percent fitting schedule. -/

namespace Green39.Transcripts

open Finset Real

noncomputable section

def logCard {V : Type*} (s : Finset V) : ℝ := log (1 + (s.card : ℝ))

private theorem log_succ_le_of_le_pow {v a : ℝ} (hv : 0 ≤ v) (ha : 1 ≤ a)
    (n : ℕ) (h : v ≤ a ^ n) :
    log (1 + v) ≤ log 2 + (n : ℝ) * log a := by
  have hp : 1 ≤ a ^ n := one_le_pow₀ ha
  have ha' : 0 < a := zero_lt_one.trans_le ha
  calc
    log (1 + v) ≤ log (2 * a ^ n) := log_le_log (by positivity) (by linarith)
    _ = _ := by rw [log_mul (by norm_num) (pow_ne_zero _ ha'.ne'), log_pow]

variable {State A Law Point : Type*} [DecidableEq A]

theorem Stage.logCard_lawList_le [DecidableEq Law] (stage : Stage State A Law Point)
    (alphabet : Finset A) (L : ℕ) :
    logCard (stage.lawList alphabet L) ≤ log 2 + (L : ℝ) * log (1 + alphabet.card) := by
  apply log_succ_le_of_le_pow (Nat.cast_nonneg _)
    (le_add_of_nonneg_right (Nat.cast_nonneg _))
  exact_mod_cast (stage.card_lawList_le alphabet L).trans
    (by simpa only [Nat.add_comm] using wordCount_le alphabet.card L)

theorem Stage.logCard_containerList_le [DecidableEq Point] (stage : Stage State A Law Point)
    (alphabet : Finset A) (L R : ℕ) :
    logCard (stage.containerList alphabet L R) ≤
      log 2 + (R : ℝ) * (log 2 + (L : ℝ) * log (1 + alphabet.card)) := by
  let W := wordCount alphabet.card L
  have hcard : ((stage.containerList alphabet L R).card : ℝ) ≤ (1 + (W : ℝ)) ^ R := by
    exact_mod_cast (stage.card_containerList_le alphabet L R).trans (by
      simpa only [Nat.add_comm] using wordCount_le W R)
  have hword : (W : ℝ) ≤ (1 + (alphabet.card : ℝ)) ^ L := by
    exact_mod_cast (by simpa only [Nat.add_comm] using wordCount_le alphabet.card L :
      W ≤ (1 + alphabet.card) ^ L)
  calc
    logCard (stage.containerList alphabet L R) ≤ log 2 + (R : ℝ) * log (1 + W) :=
      log_succ_le_of_le_pow (Nat.cast_nonneg _) (le_add_of_nonneg_right (Nat.cast_nonneg _))
        R hcard
    _ ≤ _ := by
      have hlog := log_succ_le_of_le_pow (Nat.cast_nonneg _)
        (le_add_of_nonneg_right (Nat.cast_nonneg _)) L hword
      have hmul := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α := ℝ) R)
      exact add_le_add (le_refl _) hmul

theorem logCard_mono {V : Type*} {s t : Finset V} (h : s ⊆ t) : logCard s ≤ logCard t := by
  have hc : (s.card : ℝ) ≤ (t.card : ℝ) := by exact_mod_cast card_le_card h
  exact log_le_log (by positivity) (by linarith only [hc])

/-- Combining stages pays only the logarithm of the number of stages. -/
theorem logCard_biUnion_le {I V : Type*} [DecidableEq V]
    (indices : Finset I) (f : I → Finset V) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ i ∈ indices, logCard (f i) ≤ B) :
    logCard (indices.biUnion f) ≤ log (1 + (indices.card : ℝ)) + B := by
  have hcount i (hi : i ∈ indices) : ((f i).card : ℝ) ≤ exp B :=
    (by linarith : ((f i).card : ℝ) ≤ 1 + (f i).card).trans
      ((log_le_iff_le_exp (by positivity)).mp (h i hi))
  have hsum : ((indices.biUnion f).card : ℝ) ≤ (indices.card : ℝ) * exp B := calc
    _ ≤ ∑ i ∈ indices, ((f i).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := indices) (t := f))
    _ ≤ ∑ _i ∈ indices, exp B := sum_le_sum hcount
    _ = _ := by simp
  have hexp : 1 ≤ exp B := one_le_exp hB
  calc
    logCard (indices.biUnion f) ≤ log ((1 + (indices.card : ℝ)) * exp B) := by
      apply log_le_log (by positivity)
      linarith
    _ = _ := by rw [log_mul (by positivity) (exp_pos B).ne', log_exp]

def inverseEta (x : ℝ) : ℝ := exp (1000 + (11 / 50 : ℝ) * x)

theorem inv_inverseEta (x : ℝ) : (inverseEta x)⁻¹ = exp (-1000 - (11 / 50 : ℝ) * x) := by
  rw [inverseEta, ← exp_neg]
  congr 1
  ring

def runBudget (p : ℕ) (x : ℝ) : ℕ := ⌈16 * log (p : ℝ) * inverseEta x ^ 2⌉₊ + 1

def removalBudget (x : ℝ) : ℕ := 2 + ⌈2 * inverseEta x * log (2 * x ^ 2)⌉₊

theorem inverseEta_mono : Monotone inverseEta := by
  intro x y hxy
  unfold inverseEta
  exact exp_le_exp.mpr (by linarith)

theorem inverseEta_one_le {x : ℝ} (hx : 0 ≤ x) : 1 ≤ inverseEta x := by
  unfold inverseEta
  exact one_le_exp (by positivity)

theorem inv_inverseEta_le_half {x : ℝ} (hx : 0 ≤ x) :
    (inverseEta x)⁻¹ ≤ 1 / 2 := by
  have he : 2 ≤ inverseEta x := by
    unfold inverseEta
    linarith [add_one_le_exp (1000 + (11 / 50 : ℝ) * x)]
  rw [← one_div, div_le_iff₀ (by linarith : 0 < inverseEta x)]
  linarith

/-- This integer budget satisfies the strict inequality required by the potential argument. -/
theorem runBudget_suffices (p : ℕ) (x : ℝ) :
    16 * log (p : ℝ) < (runBudget p x : ℝ) * (inverseEta x)⁻¹ ^ 2 := by
  have he : 0 < inverseEta x := exp_pos _
  have hceil := Nat.le_ceil (16 * log (p : ℝ) * inverseEta x ^ 2)
  have hb : 16 * log (p : ℝ) * inverseEta x ^ 2 < (runBudget p x : ℝ) := by
    unfold runBudget
    push_cast
    linarith only [hceil]
  rw [inv_pow, ← div_eq_mul_inv]
  exact (lt_div_iff₀ (pow_pos he 2)).mpr hb

theorem runBudget_le {p : ℕ} {x : ℝ} (hp : 0 < p) (hx : 0 ≤ x) :
    (runBudget p x : ℝ) ≤ 18 * inverseEta x ^ 2 * (1 + log (p : ℝ)) := by
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hlog := log_nonneg hp'
  have hsq : 1 ≤ inverseEta x ^ 2 := one_le_pow₀ (inverseEta_one_le hx)
  have hceil := Nat.ceil_lt_add_one
    (show 0 ≤ 16 * log (p : ℝ) * inverseEta x ^ 2 by positivity)
  unfold runBudget
  push_cast
  nlinarith only [hceil, hsq, mul_nonneg hlog (sq_nonneg (inverseEta x))]

private theorem log_two_le_one : log 2 ≤ 1 := by
  linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]

private theorem removal_log_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ log (2 * x ^ 2) := by
  exact log_nonneg (by nlinarith [sq_nonneg (x - 1)])

theorem removalBudget_lt {x : ℝ} (hx : 1 ≤ x) :
    (removalBudget x : ℝ) < 3 + 2 * inverseEta x * log (2 * x ^ 2) := by
  have he : 0 ≤ inverseEta x := (zero_le_one.trans (inverseEta_one_le (by linarith)))
  have hc := Nat.ceil_lt_add_one (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) he)
    (removal_log_nonneg hx))
  unfold removalBudget
  push_cast
  linarith

/-- Applying the allotted number of removals, each losing at least the fraction
`η/2` of the current target, leaves fewer than `k/x²` points. -/
theorem removalBudget_suffices {x k size : ℝ}
    (hx : 1 ≤ x) (hk : 0 < k) (hsize : size ≤ 2 * k) :
    (1 - (inverseEta x)⁻¹ / 2) ^ removalBudget x * size < k * lossRate x := by
  have hx0 : 0 < x := by linarith
  let E := inverseEta x
  have hE : 1 ≤ E := inverseEta_one_le hx0.le
  have hE0 : 0 < E := zero_lt_one.trans_le hE
  let t := E⁻¹ / 2
  have ht : 0 < t := div_pos (inv_pos.mpr hE0) (by norm_num)
  have hbase : 0 ≤ 1 - t := by
    change 0 ≤ 1 - E⁻¹ / 2
    rw [← one_div]
    have hinv := (div_le_iff₀ hE0).mpr (show (1 : ℝ) ≤ 1 * E by simpa using hE)
    linarith
  have hceil := Nat.le_ceil (2 * E * log (2 * x ^ 2))
  have hcount : 2 * E * log (2 * x ^ 2) < (removalBudget x : ℝ) := by
    unfold removalBudget
    push_cast
    change 2 * E * log (2 * x ^ 2) < 2 + (⌈2 * E * log (2 * x ^ 2)⌉₊ : ℝ)
    linarith only [hceil]
  have hprod : log (2 * x ^ 2) < (removalBudget x : ℝ) * t := calc
    _ = (2 * E * log (2 * x ^ 2)) * t := by
      dsimp only [t]
      field_simp [hE0.ne']
    _ < _ := mul_lt_mul_of_pos_right hcount ht
  have hpow : (1 - t) ^ removalBudget x < (2 * x ^ 2)⁻¹ := calc
    _ ≤ exp (-t) ^ removalBudget x :=
      pow_le_pow_left₀ hbase (by linarith [add_one_le_exp (-t)]) _
    _ = exp ((removalBudget x : ℝ) * (-t)) := (exp_nat_mul _ _).symm
    _ < exp (-log (2 * x ^ 2)) := exp_lt_exp.mpr (by linarith only [hprod])
    _ = _ := by rw [exp_neg, exp_log (by positivity)]
  change (1 - t) ^ removalBudget x * size < k * lossRate x
  calc
    _ ≤ (1 - t) ^ removalBudget x * (2 * k) :=
      mul_le_mul_of_nonneg_left hsize (pow_nonneg hbase _)
    _ < (2 * x ^ 2)⁻¹ * (2 * k) := mul_lt_mul_of_pos_right hpow (by positivity)
    _ = _ := by
      unfold lossRate
      field_simp

private theorem log_alphabet_le {p : ℕ} (hp : 0 < p) :
    log (1 + ((univ : Finset (Instruction p)).card : ℝ)) ≤ 6 * (1 + log (p : ℝ)) := by
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by positivity
  rw [card_univ, card_instruction]
  push_cast
  calc
    log (1 + (4 * (p : ℝ) + 1)) ≤ log (6 * (p : ℝ)) := log_le_log (by positivity) (by linarith)
    _ = log 6 + log (p : ℝ) := log_mul (by norm_num) hp0.ne'
    _ ≤ _ := by linarith [log_le_self (by norm_num : (0 : ℝ) ≤ 6), log_nonneg hp']

private theorem log_word_budget_le {p L : ℕ} {C E x : ℝ}
    (hp : 0 < p) (hC : 1 ≤ C) (hx : 0 ≤ x) (hE : inverseEta x ≤ E)
    (hL : (L : ℝ) ≤ C * (inverseEta x) ^ 2 * (1 + log (p : ℝ))) :
    log 2 + (L : ℝ) * log (1 + ((univ : Finset (Instruction p)).card : ℝ)) ≤
      7 * C * E ^ 2 * (1 + log (p : ℝ)) ^ 2 := by
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hW : 1 ≤ 1 + log (p : ℝ) := by linarith [log_nonneg hp']
  have hE0 : 0 ≤ inverseEta x := zero_le_one.trans (inverseEta_one_le hx)
  have hE' : 1 ≤ E := (inverseEta_one_le hx).trans hE
  have hL' : (L : ℝ) ≤ C * E ^ 2 * (1 + log (p : ℝ)) := by
    refine hL.trans ?_
    gcongr
  have hbase : 1 ≤ C * E ^ 2 * (1 + log (p : ℝ)) ^ 2 := by
    calc
      1 = (1 : ℝ) * 1 ^ 2 * 1 ^ 2 := by norm_num
      _ ≤ _ := by gcongr
  have hprod := mul_le_mul hL' (log_alphabet_le hp)
    (log_nonneg (le_add_of_nonneg_right (Nat.cast_nonneg _))) (by positivity)
  nlinarith only [hprod, log_two_le_one, hbase]

variable {p : ℕ} {S V P : Type*}

/-- A per-run bound gives a finite log bound for the laws at this stage. -/
theorem Stage.logCard_laws_of_eta_le [DecidableEq V]
    (stage : Stage S (Instruction p) V P) {L : ℕ} {C E x : ℝ}
    (hp : 0 < p) (hC : 1 ≤ C) (hx : 0 ≤ x) (hE : inverseEta x ≤ E)
    (hL : (L : ℝ) ≤ C * (inverseEta x) ^ 2 * (1 + log (p : ℝ))) :
    logCard (stage.lawList univ L) ≤ 7 * C * E ^ 2 * (1 + log (p : ℝ)) ^ 2 :=
  (stage.logCard_lawList_le univ L).trans (log_word_budget_le hp hC hx hE hL)

/-- The outer list costs the removal count times the log cost of a single word.
The hypothesis on `R` can be used with any fitting implementation giving that bound. -/
theorem Stage.logCard_containers_of_eta_le [DecidableEq P]
    (stage : Stage S (Instruction p) V P) {L R : ℕ} {C D E B x : ℝ}
    (hp : 0 < p) (hC : 1 ≤ C) (hD : 1 ≤ D) (hx : 0 ≤ x) (hE : inverseEta x ≤ E)
    (hB : 0 ≤ B) (hL : (L : ℝ) ≤ C * (inverseEta x) ^ 2 * (1 + log (p : ℝ)))
    (hR : (R : ℝ) ≤ D * E * (1 + B)) :
    logCard (stage.containerList univ L R) ≤
      8 * C * D * E ^ 3 * (1 + log (p : ℝ)) ^ 2 * (1 + B) := by
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hW : 1 ≤ 1 + log (p : ℝ) := by linarith [log_nonneg hp']
  have hE' : 1 ≤ E := (inverseEta_one_le hx).trans hE
  have hlog : 0 ≤ log (1 + ((univ : Finset (Instruction p)).card : ℝ)) :=
    log_nonneg (le_add_of_nonneg_right (Nat.cast_nonneg _))
  have hrun := log_word_budget_le hp hC hx hE hL
  have hbase' : 1 ≤ C * D * E ^ 3 * (1 + log (p : ℝ)) ^ 2 * (1 + B) := by
    have hB1 : 1 ≤ 1 + B := by linarith
    calc
      1 = (1 : ℝ) * 1 * 1 ^ 3 * 1 ^ 2 * 1 := by norm_num
      _ ≤ _ := by gcongr
  refine (stage.logCard_containerList_le univ L R).trans ?_
  have hs := mul_le_mul hR hrun
    (add_nonneg (log_nonneg (by norm_num)) (mul_nonneg (Nat.cast_nonneg _) hlog))
    (by positivity)
  nlinarith only [hs, log_two_le_one, hbase']

theorem removals_le_envelope {x E B : ℝ} {R : ℕ} (hx : 1 ≤ x)
    (hE : inverseEta x ≤ E) (hB : log (2 * x ^ 2) ≤ B)
    (hR : R ≤ removalBudget x) :
    (R : ℝ) ≤ 3 * E * (1 + B) := by
  have hE' : 1 ≤ E := (inverseEta_one_le (by linarith)).trans hE
  have hB' : 0 ≤ B := (removal_log_nonneg hx).trans hB
  have hr : (R : ℝ) ≤ removalBudget x := by exact_mod_cast hR
  have hm := mul_le_mul hE hB (removal_log_nonneg hx) (by positivity)
  nlinarith only [hr, hm, hE', mul_nonneg (by positivity : 0 ≤ E) hB',
    removalBudget_lt hx]

/-- The elementary estimate for `k = floor √p` used in the exponents. -/
theorem log_initial_le_log_four_mul {p k : ℕ} (hp : 0 < p) (hk : 0 < k)
    (hsqrt : p < (k + 1) ^ 2) :
    log ((p : ℝ) / k) ≤ log (4 * (k : ℝ)) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hs : (p : ℝ) < ((k : ℝ) + 1) ^ 2 := by exact_mod_cast hsqrt
  apply log_le_log (by positivity)
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < k)).mpr
  calc
    (p : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := hs.le
    _ ≤ (2 * (k : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    _ = _ := by ring

private theorem inverseEta_log_sq {y : ℝ} (hy : 0 < y) :
    inverseEta (log y) ^ 2 = exp 2000 * y ^ (11 / 25 : ℝ) := by
  rw [inverseEta, ← exp_nat_mul, rpow_def_of_pos hy, ← exp_add]
  congr 1
  push_cast
  ring

private theorem inverseEta_log_cube {y : ℝ} (hy : 0 < y) :
    inverseEta (log y) ^ 3 = exp 3000 * y ^ (33 / 50 : ℝ) := by
  rw [inverseEta, ← exp_nat_mul, rpow_def_of_pos hy, ← exp_add]
  congr 1
  push_cast
  ring

private theorem removal_log_le_of_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    log (2 * x ^ 2) ≤ log (2 * y ^ 2) := by
  apply log_le_log (by positivity)
  gcongr

private theorem removal_log_le_log_log {p k : ℕ} (hp : 0 < p) (hk : 0 < k)
    {x : ℝ} (hx : 0 < x) (hupper : x ≤ log ((p : ℝ) / k)) :
    log (2 * x ^ 2) ≤ 1 + 2 * log (1 + log (p : ℝ)) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog : log ((p : ℝ) / k) ≤ log (p : ℝ) := by
    apply log_le_log (by positivity)
    exact div_le_self (by positivity) hk'
  rw [log_mul (by norm_num) (pow_ne_zero _ hx.ne'), log_pow]
  norm_num
  have hlx := log_le_log hx (show x ≤ 1 + log (p : ℝ) by linarith)
  linarith [log_two_le_one]

/-- At every active stage the log size of the law list has the power `0.44`. -/
theorem Stage.logCard_laws_power [DecidableEq V]
    (stage : Stage S (Instruction p) V P) {k L : ℕ} {C x : ℝ}
    (hp : 0 < p) (hk : 0 < k) (hsqrt : p < (k + 1) ^ 2) (hC : 1 ≤ C)
    (hx : 5000 < x) (hupper : x ≤ log ((p : ℝ) / k))
    (hL : (L : ℝ) ≤ C * inverseEta x ^ 2 * (1 + log (p : ℝ))) :
    logCard (stage.lawList univ L) ≤
      7 * C * exp 2000 * (4 * (k : ℝ)) ^ (11 / 25 : ℝ) * (1 + log (p : ℝ)) ^ 2 := by
  have hE := inverseEta_mono (hupper.trans (log_initial_le_log_four_mul hp hk hsqrt))
  have h := stage.logCard_laws_of_eta_le hp hC (by linarith) hE hL
  rw [inverseEta_log_sq (by positivity : 0 < 4 * (k : ℝ))] at h
  convert h using 1
  ring

/-- At every active stage the log size of the output-container list has the power
`0.66`. This bound uses the manuscript's explicit removal budget. -/
theorem Stage.logCard_containers_power [DecidableEq P]
    (stage : Stage S (Instruction p) V P) {k L R : ℕ} {C x : ℝ}
    (hp : 0 < p) (hk : 0 < k) (hsqrt : p < (k + 1) ^ 2) (hC : 1 ≤ C)
    (hx : 5000 < x) (hupper : x ≤ log ((p : ℝ) / k))
    (hL : (L : ℝ) ≤ C * inverseEta x ^ 2 * (1 + log (p : ℝ)))
    (hR : R ≤ removalBudget x) :
    logCard (stage.containerList univ L R) ≤
      48 * C * exp 3000 * (4 * (k : ℝ)) ^ (33 / 50 : ℝ) *
        (1 + log (p : ℝ)) ^ 2 * (1 + log (1 + log (p : ℝ))) := by
  have hE := inverseEta_mono (hupper.trans (log_initial_le_log_four_mul hp hk hsqrt))
  have hB := removal_log_le_log_log hp hk (by linarith : 0 < x) hupper
  have hR' := removals_le_envelope (by linarith : 1 ≤ x) hE hB hR
  have h := stage.logCard_containers_of_eta_le hp hC (by norm_num : (1 : ℝ) ≤ 3)
    (by linarith) hE ((removal_log_nonneg (by linarith)).trans hB) hL hR'
  rw [inverseEta_log_cube (by positivity : 0 < 4 * (k : ℝ))] at h
  convert h using 1
  ring

/-- The last-stage output list has a log size quadratic in `1 + log p`, with
an absolute constant apart from the per-run constant `C`. -/
theorem Stage.logCard_last_containers [DecidableEq P]
    (stage : Stage S (Instruction p) V P) {L R : ℕ} {C x : ℝ}
    (hp : 0 < p) (hC : 1 ≤ C) (hx : 5000 < x) (hstop : x ≤ 10000)
    (hL : (L : ℝ) ≤ C * inverseEta x ^ 2 * (1 + log (p : ℝ)))
    (hR : R ≤ removalBudget x) :
    logCard (stage.containerList univ L R) ≤
      24 * C * (inverseEta 10000) ^ 3 * (1 + log (2 * (10000 : ℝ) ^ 2)) *
        (1 + log (p : ℝ)) ^ 2 := by
  have hE := inverseEta_mono hstop
  have hB := removal_log_le_of_le (by linarith : 0 < x) hstop
  have hR' := removals_le_envelope (by linarith : 1 ≤ x) hE hB hR
  have h := stage.logCard_containers_of_eta_le hp hC (by norm_num : (1 : ℝ) ≤ 3)
    (by linarith) hE (removal_log_nonneg (by norm_num)) hL hR'
  convert h using 1
  ring

/-- Log overhead of the level count. In this application `x₀ = log (p/k)`. -/
theorem last_active_index_le {x₀ : ℝ} {n : ℕ} (hactive : 5000 < level x₀ n) :
    (n : ℝ) < log (x₀ / 5000) / log 2 := by
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  have hx : (2 : ℝ) ^ n < x₀ / 5000 := by
    rw [level_eq_div_pow, lt_div_iff₀ hpos] at hactive
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 5000)).mpr
    linarith
  have hlog := log_lt_log hpos hx
  rw [log_pow] at hlog
  exact (lt_div_iff₀ (log_pos (by norm_num : (1 : ℝ) < 2))).mpr hlog

/-- All levels through an active stage, with a common run-length constant. -/
theorem logCard_all_laws [DecidableEq V]
    (stage : ℕ → Stage S (Instruction p) V P) (L : ℕ → ℕ)
    {k n : ℕ} {C : ℝ}
    (hp : 0 < p) (hk : 0 < k) (hsqrt : p < (k + 1) ^ 2) (hC : 1 ≤ C)
    (hactive : 5000 < level (log ((p : ℝ) / k)) n)
    (hL : ∀ i ≤ n, (L i : ℝ) ≤
      C * inverseEta (level (log ((p : ℝ) / k)) i) ^ 2 * (1 + log (p : ℝ))) :
    logCard ((range (n + 1)).biUnion (fun i => (stage i).lawList univ (L i))) ≤
      log (1 + (n + 1 : ℕ)) +
        7 * C * exp 2000 * (4 * (k : ℝ)) ^ (11 / 25 : ℝ) * (1 + log (p : ℝ)) ^ 2 := by
  let x₀ := log ((p : ℝ) / k)
  have hx : 0 ≤ x₀ := by
    rw [level_eq_div_pow, lt_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)] at hactive
    linarith [show 0 < (5000 : ℝ) * 2 ^ n by positivity]
  refine le_trans (logCard_biUnion_le _ _ (by positivity : 0 ≤
    7 * C * exp 2000 * (4 * (k : ℝ)) ^ (11 / 25 : ℝ) * (1 + log (p : ℝ)) ^ 2) ?_) ?_
  · intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
    exact (stage i).logCard_laws_power hp hk hsqrt hC
      (hactive.trans_le (level_antitone hx hin))
      (show level x₀ i ≤ x₀ from level_antitone hx (Nat.zero_le i)) (hL i hin)
  · rw [card_range]

/-- All stage container lists together pay one additive level-count term. -/
theorem logCard_all_containers [DecidableEq P]
    (stage : ℕ → Stage S (Instruction p) V P) (L R : ℕ → ℕ)
    {k n : ℕ} {C : ℝ}
    (hp : 0 < p) (hk : 0 < k) (hsqrt : p < (k + 1) ^ 2) (hC : 1 ≤ C)
    (hactive : 5000 < level (log ((p : ℝ) / k)) n)
    (hL : ∀ i ≤ n, (L i : ℝ) ≤
      C * inverseEta (level (log ((p : ℝ) / k)) i) ^ 2 * (1 + log (p : ℝ)))
    (hR : ∀ i ≤ n, R i ≤ removalBudget (level (log ((p : ℝ) / k)) i)) :
    logCard ((range (n + 1)).biUnion (fun i => (stage i).containerList univ (L i) (R i))) ≤
      log (1 + (n + 1 : ℕ)) +
        48 * C * exp 3000 * (4 * (k : ℝ)) ^ (33 / 50 : ℝ) *
          (1 + log (p : ℝ)) ^ 2 * (1 + log (1 + log (p : ℝ))) := by
  let x₀ := log ((p : ℝ) / k)
  have hx : 0 ≤ x₀ := by
    rw [level_eq_div_pow, lt_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)] at hactive
    linarith [show 0 < (5000 : ℝ) * 2 ^ n by positivity]
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hlog : 0 ≤ log (1 + log (p : ℝ)) := log_nonneg (by linarith [log_nonneg hp'])
  refine le_trans (logCard_biUnion_le _ _ (by positivity : 0 ≤
    48 * C * exp 3000 * (4 * (k : ℝ)) ^ (33 / 50 : ℝ) *
      (1 + log (p : ℝ)) ^ 2 * (1 + log (1 + log (p : ℝ)))) ?_) ?_
  · intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
    exact (stage i).logCard_containers_power hp hk hsqrt hC
      (hactive.trans_le (level_antitone hx hin))
      (show level x₀ i ≤ x₀ from level_antitone hx (Nat.zero_le i)) (hL i hin) (hR i hin)
  · rw [card_range]

/-- The manuscript's explicit removal bound is small enough to halve the level. -/
theorem removalBudget_shrink {x : ℝ} (hx : 5000 ≤ x) :
    (10 : ℝ) ^ 24 * (removalBudget x : ℝ) < exp (x / 2) := by
  have hx0 : 0 < x := by linarith
  have hpow (n : ℕ) : log ((2 : ℝ) ^ n) ≤ n := by
    rw [log_pow]
    simpa using mul_le_mul_of_nonneg_left log_two_le_one (Nat.cast_nonneg n)
  have hlog10 : log 10 ≤ 4 :=
    (log_le_log (by norm_num : (0 : ℝ) < 10) (by norm_num : (10 : ℝ) ≤ 2 ^ (4 : ℕ))).trans
      (hpow 4)
  have hlog5000 : log 5000 ≤ 13 :=
    (log_le_log (by norm_num : (0 : ℝ) < 5000)
      (by norm_num : (5000 : ℝ) ≤ 2 ^ (13 : ℕ))).trans (hpow 13)
  have hlogK : log ((10 : ℝ) ^ 24) ≤ 96 := by
    rw [log_pow]
    norm_num
    linarith
  have hlogx : log x ≤ x / 100 := by
    have hquot := log_le_sub_one_of_pos
      (div_pos hx0 (by norm_num : (0 : ℝ) < 5000))
    rw [log_div hx0.ne' (by norm_num)] at hquot
    linarith
  have hn : 0 ≤ log (2 * x ^ 2) := removal_log_nonneg (by linarith)
  have hQ : 0 < 5 + 2 * log (2 * x ^ 2) := by linarith
  have hlogQ : log (5 + 2 * log (2 * x ^ 2)) ≤ 7 + x / 25 := by
    apply (log_le_self hQ.le).trans
    rw [log_mul (by norm_num) (pow_ne_zero _ hx0.ne'), log_pow]
    norm_num
    linarith only [log_two_le_one, hlogx]
  have hE : 1 ≤ inverseEta x := inverseEta_one_le hx0.le
  have hE0 : 0 < inverseEta x := zero_lt_one.trans_le hE
  have hK : 0 < (10 : ℝ) ^ 24 := by positivity
  have hbound : (10 : ℝ) ^ 24 * inverseEta x * (5 + 2 * log (2 * x ^ 2)) < exp (x / 2) := by
    apply (log_lt_iff_lt_exp (mul_pos (mul_pos hK hE0) hQ)).mp
    rw [log_mul (mul_pos hK hE0).ne' hQ.ne', log_mul hK.ne' hE0.ne', inverseEta, log_exp]
    calc
      log ((10 : ℝ) ^ 24) + (1000 + 11 / 50 * x) + log (5 + 2 * log (2 * x ^ 2)) ≤
          96 + (1000 + 11 / 50 * x) + (7 + x / 25) := by gcongr
      _ < x / 2 := by linarith only [hx]
  calc
    (10 : ℝ) ^ 24 * (removalBudget x : ℝ) <
        (10 : ℝ) ^ 24 * (3 + 2 * inverseEta x * log (2 * x ^ 2)) :=
      mul_lt_mul_of_pos_left (removalBudget_lt (by linarith)) hK
    _ ≤ (10 : ℝ) ^ 24 * (inverseEta x * (5 + 2 * log (2 * x ^ 2))) :=
      mul_le_mul_of_nonneg_left (by nlinarith only [hE]) hK.le
    _ = (10 : ℝ) ^ 24 * inverseEta x * (5 + 2 * log (2 * x ^ 2)) := by ring
    _ < exp (x / 2) := hbound

/-- Every candidate built from heavy sets of size at most `K*k` shrinks. -/
theorem Stage.container_card_le_shrink [DecidableEq P]
    (stage : Stage S (Instruction p) V P) {k L R : ℕ} {x : ℝ}
    (hx : 5000 ≤ x) (hR : R ≤ removalBudget x)
    (hheavy : ∀ record ∈ words univ L, (stage.outputHeavy record).card ≤ 10 ^ 24 * k)
    {container : Finset P} (hmem : container ∈ stage.containerList univ L R) :
    (container.card : ℝ) ≤ exp (x / 2) * (k : ℝ) := by
  have hc := stage.card_mem_containerList_le univ L R _ hheavy hmem
  have hc' : (container.card : ℝ) ≤ (R : ℝ) * ((10 : ℝ) ^ 24 * (k : ℝ)) := by
    exact_mod_cast hc
  have hr : (R : ℝ) ≤ (removalBudget x : ℝ) := by exact_mod_cast hR
  have hs := (mul_le_mul_of_nonneg_left hr (show 0 ≤ (10 : ℝ) ^ 24 by positivity)).trans
    (removalBudget_shrink hx).le
  calc
    (container.card : ℝ) ≤ (R : ℝ) * ((10 : ℝ) ^ 24 * (k : ℝ)) := hc'
    _ = ((10 : ℝ) ^ 24 * (R : ℝ)) * (k : ℝ) := by ring
    _ ≤ exp (x / 2) * (k : ℝ) := mul_le_mul_of_nonneg_right hs (by positivity)

/-- At the terminal stage every candidate is within the size cutoff for §1. -/
theorem Stage.terminal_card_le [DecidableEq P]
    (stage : Stage S (Instruction p) V P) {k L R : ℕ} {x : ℝ}
    (hx : 5000 < x) (hstop : x ≤ 10000) (hR : R ≤ removalBudget x)
    (hheavy : ∀ record ∈ words univ L, (stage.outputHeavy record).card ≤ 10 ^ 24 * k)
    {container : Finset P} (hmem : container ∈ stage.containerList univ L R) :
    (container.card : ℝ) ≤ exp 5000 * (k : ℝ) := by
  exact (stage.container_card_le_shrink hx.le hR hheavy hmem).trans
    (mul_le_mul_of_nonneg_right (exp_le_exp.mpr (by linarith)) (by positivity))

end

end Green39.Transcripts

end TranscriptBounds

/- Source: one-percent-formal/transcripts/FittingReplay.lean -/
section FittingReplay

/- The interface between the fitting procedure and its target-independent descriptions.
The caller supplies the public tests and the fitting procedure's tilt and trim functions. -/

namespace Green39.Transcripts

open Finset

noncomputable section

variable {P : Type*} [Fintype P]

def IsLaw (m : P → ℝ) : Prop := (∀ a, 0 ≤ m a) ∧ ∑ a, m a = 1

def IsCappedLaw (cap : ℝ) (m : P → ℝ) : Prop := IsLaw m ∧ ∀ a, m a ≤ cap

def uniformState : P → ℝ := fun _ => (Fintype.card P : ℝ)⁻¹

theorem uniformState_isLaw [Nonempty P] : IsLaw (uniformState : P → ℝ) := by
  have hcard : (Fintype.card P : ℝ) ≠ 0 := by positivity
  constructor
  · intro a
    unfold uniformState
    positivity
  · simp [uniformState, sum_const, nsmul_eq_mul, hcard]

def heavyAt (cap : ℝ) (m : P → ℝ) : Finset P := by
  classical
  exact univ.filter fun a => cap < m a

theorem mem_heavyAt {cap : ℝ} {m : P → ℝ} {a : P} :
    a ∈ heavyAt cap m ↔ cap < m a := by
  classical
  simp [heavyAt]

theorem heavyAt_card_le {B : ℕ} {m : P → ℝ} (hB : 0 < B) (hm : IsLaw m) :
    (heavyAt (B : ℝ)⁻¹ m).card ≤ B := by
  let J := heavyAt (B : ℝ)⁻¹ m
  have hB' : (0 : ℝ) < B := by positivity
  have hsum : (J.card : ℝ) * (B : ℝ)⁻¹ ≤ 1 := calc
    _ = ∑ _a ∈ J, (B : ℝ)⁻¹ := by simp [sum_const, nsmul_eq_mul]
    _ ≤ ∑ a ∈ J, m a := sum_le_sum fun _ ha => (mem_heavyAt.mp ha).le
    _ ≤ ∑ a, m a := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun a _ _ => hm.1 a)
    _ = 1 := hm.2
  rw [← div_eq_mul_inv, div_le_iff₀ hB', one_mul] at hsum
  exact_mod_cast hsum

/-- The heavy test is decoded from the current law. The initial law is uniform
and the signed tests, tilt, cap, and trim are fixed public stage data. -/
def uniformStage {p : ℕ} (cap : ℝ) (signedTests : Fin 4 × Fin p → P → ℝ)
    (tilt : (P → ℝ) → (P → ℝ) → P → ℝ) (trim : Finset P → (P → ℝ) → P → ℝ) :
    Stage (P → ℝ) (Instruction p) (P → ℝ) P := by
  classical
  exact {
    reset := uniformState
    step := fun m instruction => tilt m (match instruction with
      | .inl test => signedTests test
      | .inr _ => fun a => if a ∈ heavyAt cap m then -1 else 0)
    law := fun m => trim (heavyAt cap m) m
    heavy := heavyAt cap
  }

omit [Fintype P] in
private theorem foldl_preserves {Q : Type*} {A : Type*} (step : Q → A → Q)
    (invariant : Q → Prop) (hs : ∀ q a, invariant q → invariant (step q a))
    (record : List A) (start : Q) (hstart : invariant start) :
    invariant (record.foldl step start) := by
  induction record generalizing start with
  | nil => exact hstart
  | cons a record ih => exact ih (step start a) (hs start a hstart)

/-- A tilt preserving probability laws gives the heavy-set size bound for every
word in the encoding, including words the target-dependent algorithm would never select. -/
theorem uniformStage_heavy_le {p B : ℕ} [Nonempty P] (hB : 0 < B)
    (signedTests : Fin 4 × Fin p → P → ℝ)
    (tilt : (P → ℝ) → (P → ℝ) → P → ℝ) (trim : Finset P → (P → ℝ) → P → ℝ)
    (htilt : ∀ m f, IsLaw m → IsLaw (tilt m f)) (record : List (Instruction p)) :
    ((uniformStage (B : ℝ)⁻¹ signedTests tilt trim).outputHeavy record).card ≤ B := by
  classical
  let stage := uniformStage (B : ℝ)⁻¹ signedTests tilt trim
  apply heavyAt_card_le hB
  apply foldl_preserves stage.step IsLaw _ record stage.reset uniformState_isLaw
  intro m instruction hm
  cases instruction <;> exact htilt m _ hm

/-- Filtering the over-enumeration by the cap and the law axioms gives a list of
genuine capped probability laws. -/
def Stage.cappedLawList {S : Type*} {p : ℕ}
    (stage : Stage S (Instruction p) (P → ℝ) P) (cap : ℝ) (L : ℕ) : Finset (P → ℝ) := by
  classical
  exact (stage.lawList univ L).filter (IsCappedLaw cap)

theorem Stage.mem_cappedLawList {S : Type*} {p : ℕ}
    (stage : Stage S (Instruction p) (P → ℝ) P) {cap : ℝ} {L : ℕ} {m : P → ℝ} :
    m ∈ stage.cappedLawList cap L ↔
      IsCappedLaw cap m ∧ ∃ record : List (Instruction p), record.length ≤ L ∧
        stage.outputLaw record = m := by
  classical
  simp only [Stage.cappedLawList, Stage.lawList, mem_filter, mem_image, mem_words,
    mem_univ, implies_true, and_true]
  exact and_comm

theorem Stage.logCard_cappedLaws_power {S : Type*} {p k L : ℕ}
    (stage : Stage S (Instruction p) (P → ℝ) P) {C x cap : ℝ}
    (hp : 0 < p) (hk : 0 < k) (hsqrt : p < (k + 1) ^ 2) (hC : 1 ≤ C)
    (hx : 5000 < x) (hupper : x ≤ Real.log ((p : ℝ) / k))
    (hL : (L : ℝ) ≤ C * inverseEta x ^ 2 * (1 + Real.log (p : ℝ))) :
    logCard (stage.cappedLawList cap L) ≤
      7 * C * Real.exp 2000 * (4 * (k : ℝ)) ^ (11 / 25 : ℝ) * (1 + Real.log (p : ℝ)) ^ 2 := by
  classical
  exact (logCard_mono (filter_subset _ _)).trans
    (stage.logCard_laws_power hp hk hsqrt hC hx hupper hL)

/-- The joint law family used in §4 contains only capped probability laws. It
inherits the all-stage logarithmic budget from the unfiltered descriptions. -/
theorem logCard_all_cappedLaws {S : Type*} {p k n : ℕ}
    (stage : ℕ → Stage S (Instruction p) (P → ℝ) P) (cap : ℝ) (L : ℕ → ℕ) {C : ℝ}
    (hp : 0 < p) (hk : 0 < k) (hsqrt : p < (k + 1) ^ 2) (hC : 1 ≤ C)
    (hactive : 5000 < level (Real.log ((p : ℝ) / k)) n)
    (hL : ∀ i ≤ n, (L i : ℝ) ≤
      C * inverseEta (level (Real.log ((p : ℝ) / k)) i) ^ 2 * (1 + Real.log (p : ℝ))) :
    logCard ((range (n + 1)).biUnion (fun i => (stage i).cappedLawList cap (L i))) ≤
      Real.log (1 + (n + 1 : ℕ)) +
        7 * C * Real.exp 2000 * (4 * (k : ℝ)) ^ (11 / 25 : ℝ) * (1 + Real.log (p : ℝ)) ^ 2 := by
  classical
  refine (logCard_mono ?_).trans (logCard_all_laws stage L hp hk hsqrt hC hactive hL)
  intro law hlaw
  obtain ⟨i, hi, hmem⟩ := mem_biUnion.mp hlaw
  exact mem_biUnion.mpr ⟨i, hi, (mem_filter.mp hmem).1⟩

end

end Green39.Transcripts

end FittingReplay

/- Source: one-percent-formal/transcripts/FittingBridge.lean -/
section FittingBridge

/- An adapter for the fitting implementation's newest-first transcripts. -/

namespace Green39.Transcripts

open Finset

noncomputable section

variable {P σ : Type*} [Fintype P] [DecidableEq P] [Fintype σ]

def instructionEquiv {p : ℕ} (hσ : Fintype.card σ = 2 * p) :
    Fitting.Instruction σ ≃ Instruction p :=
  Fintype.equivOfCardEq (by
    rw [card_instruction]
    simp only [Fitting.Instruction, Fintype.card_option, Fintype.card_prod, Fintype.card_bool, hσ]
    omega)

/-- The fitting implementation stores the newest instruction first. -/
def encodeFittingWord {p : ℕ} (hσ : Fintype.card σ = 2 * p)
    (word : List (Fitting.Instruction σ)) : List (Instruction p) :=
  word.reverse.map (instructionEquiv hσ)

theorem encodeFittingWord_length {p : ℕ} (hσ : Fintype.card σ = 2 * p)
    (word : List (Fitting.Instruction σ)) :
    (encodeFittingWord hσ word).length = word.length := by
  simp [encodeFittingWord]

def fittingStage {p : ℕ} (hσ : Fintype.card σ = 2 * p) (tests : σ → P → ℝ) (η cap : ℝ) :
    Stage (P → ℝ) (Instruction p) (P → ℝ) P where
  reset := uniformState
  step := fun m instruction =>
    Fitting.tilt m (Fitting.testAt tests cap m ((instructionEquiv hσ).symm instruction)) (η / 4)
  law := fun m => Fitting.clipped (Fitting.heavy cap m) m
  heavy := Fitting.heavy cap

theorem fittingStage_replay_eq {p : ℕ} (hσ : Fintype.card σ = 2 * p)
    (tests : σ → P → ℝ) (η cap : ℝ) (word : List (Fitting.Instruction σ)) :
    (fittingStage hσ tests η cap).replay (encodeFittingWord hσ word) =
      Fitting.decode tests η cap word := by
  induction word with
  | nil => rfl
  | cons instruction word ih =>
    simp only [encodeFittingWord, List.reverse_cons, List.map_append, Stage.replay, List.foldl_append,
      List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    change (fittingStage hσ tests η cap).step
      ((fittingStage hσ tests η cap).replay (encodeFittingWord hσ word))
        (instructionEquiv hσ instruction) = _
    rw [ih]
    simp [fittingStage, Fitting.decode]

theorem fittingStage_outputContainer_eq {p : ℕ} (hσ : Fintype.card σ = 2 * p)
    (tests : σ → P → ℝ) (η cap : ℝ) (records : List (List (Fitting.Instruction σ))) :
    (fittingStage hσ tests η cap).outputContainer (records.map (encodeFittingWord hσ)) =
      Fitting.recordedUnion tests η cap records := by
  induction records with
  | nil => rfl
  | cons word records ih =>
    simp only [List.map_cons, Stage.outputContainer, Stage.outputHeavy, fittingStage_replay_eq,
      Fitting.recordedUnion, ih]
    rfl

theorem recordedUnion_mem {p L R : ℕ} (hσ : Fintype.card σ = 2 * p)
    (tests : σ → P → ℝ) (η cap : ℝ)
    (records : List (List (Fitting.Instruction σ))) (hR : records.length ≤ R)
    (hL : ∀ word ∈ records, word.length ≤ L) :
    Fitting.recordedUnion tests η cap records ∈
      (fittingStage hσ tests η cap).containerList univ L R := by
  rw [← fittingStage_outputContainer_eq hσ tests η cap records]
  apply Stage.outputContainer_mem
  · simpa using hR
  · intro word hw
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hw
    exact ⟨(encodeFittingWord_length hσ source).trans_le (hL source hsource),
      fun _ _ => mem_univ _⟩

theorem fittedLaw_mem {p L : ℕ} (hσ : Fintype.card σ = 2 * p)
    (tests : σ → P → ℝ) (η cap : ℝ) (F : Finset P)
    (word : List (Fitting.Instruction σ)) (hL : word.length ≤ L)
    (hfit : Fitting.Fitted F tests η cap
      (Fitting.clipped (Fitting.heavy cap (Fitting.decode tests η cap word))
        (Fitting.decode tests η cap word))) :
    Fitting.clipped (Fitting.heavy cap (Fitting.decode tests η cap word))
        (Fitting.decode tests η cap word) ∈
      (fittingStage hσ tests η cap).cappedLawList (2 * cap) L := by
  refine (Stage.mem_cappedLawList _).mpr ⟨⟨⟨fun a => (hfit.2.1 a).1, hfit.1⟩,
    fun a => (hfit.2.1 a).2⟩, encodeFittingWord hσ word, ?_, ?_⟩
  · simpa only [encodeFittingWord_length] using hL
  · rw [Stage.outputLaw, fittingStage_replay_eq]
    rfl

theorem fittingStage_heavy_le {p H : ℕ} [Nonempty P] (hH : 0 < H)
    (hσ : Fintype.card σ = 2 * p) (tests : σ → P → ℝ) (η : ℝ)
    (word : List (Instruction p)) :
    ((fittingStage hσ tests η (H : ℝ)⁻¹).outputHeavy word).card ≤ H := by
  let decodedWord := (word.map (instructionEquiv hσ).symm).reverse
  have hword : encodeFittingWord hσ decodedWord = word := by
    simp [encodeFittingWord, decodedWord, List.map_map, Function.comp_def]
  rw [← hword, Stage.outputHeavy, fittingStage_replay_eq]
  let m := Fitting.decode tests η (H : ℝ)⁻¹ decodedWord
  change (Fitting.heavy (H : ℝ)⁻¹ m).card ≤ H
  have hheavy : Fitting.heavy (H : ℝ)⁻¹ m = heavyAt (H : ℝ)⁻¹ m := by
    ext a
    simp [Fitting.heavy, mem_heavyAt]
  rw [hheavy]
  obtain ⟨hpos, hsum⟩ := Fitting.decode_law tests η (H : ℝ)⁻¹ decodedWord
  exact heavyAt_card_le hH ⟨fun a => (hpos a).le, hsum⟩

/-- The implementation's two alternatives land in the target-independent
families counted by the transcript bounds. -/
theorem fitting_stage_enumerated {p : ℕ} [Nonempty P]
    (hσ : Fintype.card σ = 2 * p) {tests : σ → P → ℝ} (htests : ∀ j a, |tests j a| ≤ 1)
    {η cap θ : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 2) (hcap : 0 ≤ cap) (hθ : 0 < θ)
    (L : ℕ) (hL : 16 * Real.log (Fintype.card P) < L * η ^ 2)
    (R : ℕ) (V : Finset P) (hR : (1 - η / 2) ^ R * V.card < θ) :
    (∃ F ⊆ V, θ ≤ F.card ∧ ∃ μ ∈ (fittingStage hσ tests η cap).cappedLawList (2 * cap) L,
      Fitting.Fitted F tests η cap μ) ∨
    (∃ container ∈ (fittingStage hσ tests η cap).containerList univ L R,
      ((V \ container).card : ℝ) < θ) := by
  rcases Fitting.stage_alternative htests hη hη' hcap hθ L hL R V hR with
    ⟨F, hsub, hsize, word, hword, hfit⟩ | ⟨records, hlen, hwords, hloss⟩
  · exact Or.inl ⟨F, hsub, hsize, _, fittedLaw_mem hσ tests η cap F word hword hfit, hfit⟩
  · exact Or.inr ⟨_, recordedUnion_mem hσ tests η cap records hlen hwords, hloss⟩

/-- The scalar budgets instantiate the fitting dichotomy at an active level. -/
theorem fitting_stage_at_level {p k : ℕ} [Nonempty P]
    (hσ : Fintype.card σ = 2 * p) (hP : Fintype.card P = p)
    {tests : σ → P → ℝ} (htests : ∀ j a, |tests j a| ≤ 1)
    {x : ℝ} (hx : 5000 < x) (hk : 0 < k) (V : Finset P)
    (hsize : (V.card : ℝ) ≤ 2 * (k : ℝ)) :
    let cap := ((10 ^ 24 * k : ℕ) : ℝ)⁻¹
    let η := (inverseEta x)⁻¹
    let stage := fittingStage hσ tests η cap
    (∃ F ⊆ V, (k : ℝ) * lossRate x ≤ F.card ∧
      ∃ μ ∈ stage.cappedLawList (2 * cap) (runBudget p x), Fitting.Fitted F tests η cap μ) ∨
    (∃ container ∈ stage.containerList univ (runBudget p x) (removalBudget x),
      (container.card : ℝ) ≤ Real.exp (x / 2) * (k : ℝ) ∧
        ((V \ container).card : ℝ) < (k : ℝ) * lossRate x) := by
  intro cap η stage
  have hx0 : 0 < x := by linarith
  have hη : 0 < η := inv_pos.mpr (Real.exp_pos _)
  have hcap : 0 < cap := by dsimp only [cap]; positivity
  have hθ : 0 < (k : ℝ) * lossRate x := by unfold lossRate; positivity
  have hrun : 16 * Real.log (Fintype.card P) < (runBudget p x : ℝ) * η ^ 2 := by
    rw [hP]
    exact runBudget_suffices p x
  have hout := fitting_stage_enumerated hσ htests hη (inv_inverseEta_le_half hx0.le)
    hcap.le hθ (runBudget p x) hrun (removalBudget x) V
    (removalBudget_suffices (by linarith) (by positivity) hsize)
  rcases hout with hfit | ⟨container, hmem, hloss⟩
  · exact Or.inl hfit
  · refine Or.inr ⟨container, hmem, ?_, hloss⟩
    exact stage.container_card_le_shrink hx.le le_rfl
      (fun word _ => fittingStage_heavy_le (by positivity : 0 < 10 ^ 24 * k) hσ tests η word) hmem

/-- A single last-stage family covers every admissible list of records and has
both the cardinality and member-size bounds required in §1. -/
theorem fitting_terminal_family {p k L R : ℕ} [Nonempty P]
    (hσ : Fintype.card σ = 2 * p) (tests : σ → P → ℝ) {C x : ℝ}
    (hp : 0 < p) (hk : 0 < k) (hC : 1 ≤ C) (hx : 5000 < x) (hstop : x ≤ 10000)
    (hL : (L : ℝ) ≤ C * inverseEta x ^ 2 * (1 + Real.log (p : ℝ)))
    (hR : R ≤ removalBudget x) :
    let cap := ((10 ^ 24 * k : ℕ) : ℝ)⁻¹
    let η := (inverseEta x)⁻¹
    ∃ family : Finset (Finset P),
      logCard family ≤
        24 * C * (inverseEta 10000) ^ 3 * (1 + Real.log (2 * (10000 : ℝ) ^ 2)) *
          (1 + Real.log (p : ℝ)) ^ 2 ∧
      (∀ container ∈ family, (container.card : ℝ) ≤ Real.exp 5000 * (k : ℝ)) ∧
      (∀ records : List (List (Fitting.Instruction σ)), records.length ≤ R →
        (∀ word ∈ records, word.length ≤ L) →
        Fitting.recordedUnion tests η cap records ∈ family) := by
  intro cap η
  let stage := fittingStage hσ tests η cap
  refine ⟨stage.containerList univ L R, stage.logCard_last_containers hp hC hx hstop hL hR,
    ?_, fun records hlen hwords => recordedUnion_mem hσ tests η cap records hlen hwords⟩
  intro container hmem
  exact stage.terminal_card_le hx hstop hR
    (fun word _ => fittingStage_heavy_le (by positivity : 0 < 10 ^ 24 * k) hσ tests η word) hmem

end

end Green39.Transcripts

end FittingBridge

/- Source: one-percent-formal/catalog/ConcreteCatalog.lean -/
section ConcreteCatalog

/- A finite catalog whose entries are decoded from the explicit cyclic fitting runs. -/

open Finset Real
open scoped Classical

namespace Green39.Assembly

noncomputable section

open OnePercent.Fourier

private theorem exists_stop (p : ℕ) : ∃ i, x p i ≤ 5000 := by
  by_cases h : x p 0 ≤ 5000
  · exact ⟨0, h⟩
  · obtain ⟨i, _, hi⟩ := Transcripts.exists_last_active (lt_of_not_ge h)
    exact ⟨i + 1, hi⟩

def stageCount (p : ℕ) : ℕ := Nat.find (exists_stop p)

theorem stageCount_active {p i : ℕ} (hi : i < stageCount p) : 5000 < x p i :=
  lt_of_not_ge (Nat.find_min (exists_stop p) hi)

theorem stageCount_stop (p : ℕ) : x p (stageCount p) ≤ 5000 :=
  Nat.find_spec (exists_stop p)

theorem stageCount_pos {p : ℕ} (h : 5000 < x p 0) : 0 < stageCount p := by
  by_contra! hz
  simpa [Nat.eq_zero_of_le_zero hz, h.not_ge] using stageCount_stop p

theorem stageCount_le (p : ℕ) : (stageCount p : ℝ) ≤ 1 + x p 0 / 5000 := by
  have hx : 0 ≤ x p 0 := by
    unfold x Transcripts.level
    by_cases hp : p = 0
    · simp [hp]
    · apply log_nonneg
      have hk : 0 < p.sqrt := Nat.sqrt_pos.mpr (Nat.pos_of_ne_zero hp)
      exact (one_le_div (Nat.cast_pos.mpr hk)).mpr (Nat.cast_le.mpr (Nat.sqrt_le_self p))
  cases h : stageCount p with
  | zero => simp only [Nat.cast_zero]; positivity
  | succ i =>
    have hi := stageCount_active (p := p) (i := i) (by omega)
    have hpow : (i : ℝ) < 2 ^ i := by exact_mod_cast (Nat.lt_two_pow_self : i < 2 ^ i)
    unfold x at hi
    rw [Transcripts.level_eq_div_pow, lt_div_iff₀ (by positivity)] at hi
    simp only [Nat.cast_succ]
    change (i : ℝ) + 1 ≤ 1 + Real.log ((p : ℝ) / ↑p.sqrt) / 5000
    linarith

variable {p : ℕ} [NeZero p]

private theorem p_pos (p : ℕ) [NeZero p] : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)

private theorem k_pos (p : ℕ) [NeZero p] : 0 < p.sqrt := Nat.sqrt_pos.mpr (p_pos p)

private theorem x_le_initial (p : ℕ) [NeZero p] (i : ℕ) : x p i ≤ x p 0 := by
  apply Transcripts.level_antitone _ (Nat.zero_le i)
  exact log_nonneg ((one_le_div (Nat.cast_pos.mpr (k_pos p))).mpr
    (Nat.cast_le.mpr (Nat.sqrt_le_self p)))

private theorem eta_eq (y : ℝ) : eta y = (Transcripts.inverseEta y)⁻¹ := by
  rw [Transcripts.inv_inverseEta]
  unfold eta
  congr 1
  ring

def fittingCap (p : ℕ) : ℝ := 1 / (10 ^ 24 * (p.sqrt : ℝ))

def fittingWords (p i : ℕ) : ℕ := Fitting.wordBudget p (eta (x p i))

def fittingPeels (p i : ℕ) : ℕ := Fitting.peelBudget (eta (x p i)) (Transcripts.lossRate (x p i))

theorem fittingWords_le (p i : ℕ) : fittingWords p i ≤ Transcripts.runBudget p (x p i) := by
  unfold fittingWords Fitting.wordBudget Transcripts.runBudget
  rw [eta_eq, inv_pow, div_inv_eq_mul]
  exact Nat.add_le_add_right (Nat.floor_le_ceil _) _

theorem fittingPeels_le (p i : ℕ) : fittingPeels p i ≤ Transcripts.removalBudget (x p i) := by
  unfold fittingPeels Fitting.peelBudget Transcripts.removalBudget Transcripts.lossRate
  rw [eta_eq, div_inv_eq_mul, div_div_eq_mul_div, div_one]
  have h := Nat.floor_le_ceil
    (2 * Transcripts.inverseEta (x p i) * Real.log (2 * x p i ^ 2))
  omega

private theorem cyclic_alphabet (p : ℕ) [NeZero p] : Fintype.card (ZMod p × Bool) = 2 * p := by
  simp [Nat.mul_comm]

def cyclicDecoder (p : ℕ) [NeZero p] (i : ℕ) :
    Transcripts.Stage (Law p) (Transcripts.Instruction p) (Law p) (ZMod p) :=
  Transcripts.fittingStage (cyclic_alphabet p) (Fitting.cyclicTests p) (eta (x p i)) (fittingCap p)

/-- Stage zero starts with the full group. Each later list is decoded from the
immediately preceding stage's records, with no dependence on prior containers. -/
def concreteCatalog (p : ℕ) [NeZero p] : Catalog p where
  stages := stageCount p
  containers
    | 0 => {univ}
    | i + 1 => (cyclicDecoder p i).containerList univ (fittingWords p i) (fittingPeels p i)
  laws i := (cyclicDecoder p i).cappedLawList (2 * fittingCap p) (fittingWords p i)

theorem concreteCatalog_container_mem (p : ℕ) [NeZero p] (i : ℕ)
    (ws : List (List (Fitting.Instruction (ZMod p × Bool))))
    (hlen : ws.length ≤ fittingPeels p i) (hword : ∀ w ∈ ws, w.length ≤ fittingWords p i) :
    Fitting.recordedUnion (Fitting.cyclicTests p) (eta (x p i)) (fittingCap p) ws ∈
      (concreteCatalog p).containers (i + 1) :=
  Transcripts.recordedUnion_mem (cyclic_alphabet p) _ _ _ ws hlen hword

/-- Every listed container, including a terminal one, is the union decoded
from a single stage's records. -/
theorem concreteCatalog_mem_containers_iff (p : ℕ) [NeZero p] (i : ℕ) (P : Points p) :
    P ∈ (concreteCatalog p).containers (i + 1) ↔
      ∃ ws : List (List (Fitting.Instruction (ZMod p × Bool))), ws.length ≤ fittingPeels p i ∧
        (∀ w ∈ ws, w.length ≤ fittingWords p i) ∧
        P = Fitting.recordedUnion (Fitting.cyclicTests p) (eta (x p i)) (fittingCap p) ws := by
  constructor
  · intro hP
    change P ∈ (cyclicDecoder p i).containerList univ (fittingWords p i) (fittingPeels p i) at hP
    obtain ⟨records, hrecords, rfl⟩ := mem_image.mp hP
    obtain ⟨hlen, hwords⟩ := Transcripts.mem_words.mp hrecords
    let decodeWord (w : List (Transcripts.Instruction p)) :=
      (w.map (Transcripts.instructionEquiv (cyclic_alphabet p)).symm).reverse
    let ws := records.map decodeWord
    refine ⟨ws, by simpa only [ws, List.length_map] using hlen, ?_, ?_⟩
    · intro w hw
      obtain ⟨record, hrecord, rfl⟩ := List.mem_map.mp hw
      simpa only [decodeWord, List.length_reverse, List.length_map] using
        (Transcripts.mem_words.mp (hwords record hrecord)).1
    · have hcomp : Transcripts.encodeFittingWord (cyclic_alphabet p) ∘ decodeWord = id := by
        funext word
        simp [Transcripts.encodeFittingWord, decodeWord, List.map_map, Function.comp_def]
      have hmap : ws.map (Transcripts.encodeFittingWord (cyclic_alphabet p)) = records := by
        simp only [ws, List.map_map, hcomp, List.map_id]
      calc
        (cyclicDecoder p i).outputContainer records =
            (cyclicDecoder p i).outputContainer (ws.map (Transcripts.encodeFittingWord (cyclic_alphabet p))) :=
          congrArg (cyclicDecoder p i).outputContainer hmap.symm
        _ = _ := Transcripts.fittingStage_outputContainer_eq (cyclic_alphabet p) _ _ _ ws
  · rintro ⟨ws, hlen, hword, rfl⟩
    exact concreteCatalog_container_mem p i ws hlen hword

private theorem concreteCatalog_law_mem (i : ℕ) (w : List (Fitting.Instruction (ZMod p × Bool)))
    (hlen : w.length ≤ fittingWords p i)
    (hcap : Transcripts.IsCappedLaw (2 * fittingCap p)
      (Fitting.fittedLaw (eta (x p i)) (fittingCap p) w)) :
    Fitting.fittedLaw (eta (x p i)) (fittingCap p) w ∈ (concreteCatalog p).laws i := by
  apply (Transcripts.Stage.mem_cappedLawList _).mpr
  refine ⟨hcap, Transcripts.encodeFittingWord (cyclic_alphabet p) w, ?_, ?_⟩
  · simpa only [Transcripts.encodeFittingWord_length] using hlen
  · unfold cyclicDecoder Transcripts.Stage.outputLaw
    rw [Transcripts.fittingStage_replay_eq]
    rfl

theorem concreteCatalog_spec (p : ℕ) [NeZero p] : StageSpec (concreteCatalog p) := by
  refine ⟨by simp [concreteCatalog], fun _ => stageCount_active, stageCount_stop p, ?_, ?_, ?_⟩
  · intro i hi P hP
    cases i with
    | zero =>
      have hP' : P = univ := by simpa [concreteCatalog] using hP
      subst P
      have hk : (0 : ℝ) < p.sqrt := Nat.cast_pos.mpr (k_pos p)
      rw [card_univ, ZMod.card, x, Transcripts.level,
        exp_log (div_pos (Nat.cast_pos.mpr (p_pos p)) hk)]
      exact le_of_eq (by field_simp)
    | succ i =>
      have hx := stageCount_active (p := p) (i := i) (by
        change i + 1 ≤ stageCount p at hi
        omega)
      have hcap : fittingCap p = ((10 ^ 24 * p.sqrt : ℕ) : ℝ)⁻¹ := by
        norm_num [fittingCap, one_div]
      change P ∈ (cyclicDecoder p i).containerList univ (fittingWords p i) (fittingPeels p i) at hP
      have h := (cyclicDecoder p i).container_card_le_shrink hx.le (fittingPeels_le p i)
        (k := p.sqrt) (fun word _ => by
          unfold cyclicDecoder
          rw [hcap]
          exact Transcripts.fittingStage_heavy_le (Nat.mul_pos (by decide) (k_pos p))
            (cyclic_alphabet p) _ _ word) hP
      simpa only [x, Transcripts.level, mul_comm] using h
  · intro i _ μ hμ
    have h := ((Transcripts.Stage.mem_cappedLawList _).mp hμ).1
    exact ⟨h.1.1, h.1.2, fun z => by simpa only [fittingCap, mul_one_div] using h.2 z⟩
  · intro i hi _ _ V _ _ hV
    have hx := stageCount_active hi
    have hk : (0 : ℝ) < p.sqrt := Nat.cast_pos.mpr (k_pos p)
    have hη : 0 < eta (x p i) := exp_pos _
    have hη' : eta (x p i) ≤ 1 / 2 := by
      rw [eta_eq]
      exact Transcripts.inv_inverseEta_le_half (by linarith)
    have hξ : 0 < Transcripts.lossRate (x p i) := by
      unfold Transcripts.lossRate
      exact one_div_pos.mpr (sq_pos_of_pos (by linarith))
    rcases Fitting.cyclic_stage_explicit V hk hV hη hη' hξ (by norm_num : (0 : ℝ) < 10 ^ 24) with
      ⟨F, hsub, hcard, w, hw, hsum, hcap, hfit⟩ | ⟨ws, hlen, hwords, _, hcut⟩
    · have hF : F.Nonempty := card_pos.mp (by exact_mod_cast (mul_pos hξ hk).trans_le hcard)
      refine Or.inl ⟨F, hsub, by simpa only [mul_comm] using hcard, _,
        concreteCatalog_law_mem i w hw ⟨⟨fun z => (hcap z).1, hsum⟩, fun z => (hcap z).2⟩,
        (fourierFit_iff_uniformLaw _ _ hF _).mpr ?_⟩
      have hu : uniformLaw F = fun z => (Fitting.uniformOn F z : ℂ) := by
        funext z
        by_cases hz : z ∈ F <;> simp [uniformLaw, indicator, Fitting.uniformOn, hz, one_div]
      rw [hu]
      exact hfit
    · exact Or.inr ⟨_, concreteCatalog_container_mem p i ws hlen hwords,
        by simpa only [fittingCap, mul_comm] using hcut.le⟩

theorem concreteCatalog_card_laws (p : ℕ) [NeZero p] (i : ℕ) :
    ((concreteCatalog p).laws i).card ≤ Transcripts.wordCount (4 * p + 1) (fittingWords p i) := by
  change ((cyclicDecoder p i).cappedLawList _ _).card ≤ _
  refine (card_filter_le _ _).trans ?_
  simpa only [card_univ, Transcripts.card_instruction] using
    (cyclicDecoder p i).card_lawList_le univ (fittingWords p i)

theorem concreteCatalog_card_containers (p : ℕ) [NeZero p] (i : ℕ) :
    ((concreteCatalog p).containers (i + 1)).card ≤
      Transcripts.wordCount (Transcripts.wordCount (4 * p + 1) (fittingWords p i))
        (fittingPeels p i) := by
  simpa only [concreteCatalog, card_univ, Transcripts.card_instruction] using
    (cyclicDecoder p i).card_containerList_le univ (fittingWords p i) (fittingPeels p i)

private theorem fittingWords_real_le (p : ℕ) [NeZero p] {i : ℕ} (hi : i < stageCount p) :
    (fittingWords p i : ℝ) ≤ 18 * Transcripts.inverseEta (x p i) ^ 2 * (1 + log (p : ℝ)) :=
  (Nat.cast_le.mpr (fittingWords_le p i)).trans
    (Transcripts.runBudget_le (p_pos p) (by linarith [stageCount_active hi]))

def lawExponent (p : ℕ) : ℝ :=
  7 * 18 * exp 2000 * (4 * (p.sqrt : ℝ)) ^ (11 / 25 : ℝ) * (1 + log (p : ℝ)) ^ 2

def containerExponent (p : ℕ) : ℝ :=
  48 * 18 * exp 3000 * (4 * (p.sqrt : ℝ)) ^ (33 / 50 : ℝ) * (1 + log (p : ℝ)) ^ 2 *
    (1 + log (1 + log (p : ℝ)))

def terminalCoefficient : ℝ :=
  24 * 18 * Transcripts.inverseEta 10000 ^ 3 * (1 + log (2 * (10000 : ℝ) ^ 2))

theorem concreteCatalog_log_laws (p : ℕ) [NeZero p] {i : ℕ} (hi : i < stageCount p) :
    Transcripts.logCard ((concreteCatalog p).laws i) ≤ lawExponent p := by
  exact (cyclicDecoder p i).logCard_cappedLaws_power (p_pos p) (k_pos p) (Nat.lt_succ_sqrt' p)
    (by norm_num : (1 : ℝ) ≤ 18) (stageCount_active hi) (x_le_initial p i)
    (fittingWords_real_le p hi)

theorem concreteCatalog_log_containers (p : ℕ) [NeZero p] {i : ℕ} (hi : i < stageCount p) :
    Transcripts.logCard ((concreteCatalog p).containers (i + 1)) ≤ containerExponent p := by
  exact (cyclicDecoder p i).logCard_containers_power (p_pos p) (k_pos p) (Nat.lt_succ_sqrt' p)
    (by norm_num : (1 : ℝ) ≤ 18) (stageCount_active hi) (x_le_initial p i)
    (fittingWords_real_le p hi) (fittingPeels_le p i)

theorem concreteCatalog_log_terminal (p : ℕ) [NeZero p] (h : 0 < stageCount p) :
    Transcripts.logCard ((concreteCatalog p).containers (concreteCatalog p).stages) ≤
      terminalCoefficient * (1 + log (p : ℝ)) ^ 2 := by
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'
  have hactive : i < stageCount p := by omega
  have hstop : x p (i + 1) ≤ 5000 := by
    simpa only [hi, Nat.succ_eq_add_one] using stageCount_stop p
  have hlast := (Transcripts.last_level_bounds (stageCount_active hactive) hstop).2
  change Transcripts.logCard ((concreteCatalog p).containers (stageCount p)) ≤ _
  rw [hi]
  exact (cyclicDecoder p i).logCard_last_containers (p_pos p) (by norm_num : (1 : ℝ) ≤ 18)
    (stageCount_active hactive) hlast (fittingWords_real_le p hactive) (fittingPeels_le p i)

theorem concreteCatalog_log_allLaws (p : ℕ) [NeZero p] :
    Transcripts.logCard ((range (concreteCatalog p).stages).biUnion (concreteCatalog p).laws) ≤
      log (1 + (stageCount p : ℝ)) + lawExponent p := by
  have hnonneg : 0 ≤ lawExponent p := by unfold lawExponent; positivity
  exact (Transcripts.logCard_biUnion_le _ _ hnonneg
    (fun _ hi => concreteCatalog_log_laws p (mem_range.mp hi))).trans_eq
    (by rw [card_range])

private theorem card_le_exp_of_logCard {α : Type*} {s : Finset α} {a : ℝ}
    (h : Transcripts.logCard s ≤ a) : (s.card : ℝ) ≤ exp a := by
  have h' := (log_le_iff_le_exp (by positivity : 0 < 1 + (s.card : ℝ))).mp h
  linarith

theorem concreteCatalog_sum_card_products (p : ℕ) [NeZero p] :
    (∑ i ∈ range (concreteCatalog p).stages,
      (((concreteCatalog p).containers i).card : ℝ) * ((concreteCatalog p).laws i).card) ≤
      (stageCount p : ℝ) * exp (containerExponent p + lawExponent p) := by
  have hp : 0 ≤ log (p : ℝ) := log_nonneg (by exact_mod_cast p_pos p)
  have he : 0 ≤ containerExponent p := by
    have hlog : 0 ≤ log (1 + log (p : ℝ)) := log_nonneg (by linarith)
    unfold containerExponent
    positivity
  calc
    _ ≤ ∑ _ ∈ range (concreteCatalog p).stages, exp (containerExponent p + lawExponent p) := by
      apply sum_le_sum
      intro i hi
      have hL := card_le_exp_of_logCard (concreteCatalog_log_laws p (mem_range.mp hi))
      have hC : (((concreteCatalog p).containers i).card : ℝ) ≤ exp (containerExponent p) := by
        cases i with
        | zero => simpa [concreteCatalog] using one_le_exp he
        | succ i =>
          apply card_le_exp_of_logCard
          apply concreteCatalog_log_containers p
          have h := mem_range.mp hi
          change i + 1 < stageCount p at h
          omega
      rw [exp_add]
      exact mul_le_mul hC hL (Nat.cast_nonneg _) (exp_pos _).le
    _ = _ := by simp [concreteCatalog, nsmul_eq_mul]

end

end Green39.Assembly

end ConcreteCatalog

/- Source: one-percent-formal/catalog/CatalogRates.lean -/
section CatalogRates

/- The concrete catalog counts in the form used by the probability endpoint. -/

open Filter Topology Finset Real
open scoped Classical

namespace Green39.Assembly

noncomputable section

private theorem half_le_log_two : (1 / 2 : ℝ) ≤ log 2 := by
  have h := one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at h
  linarith

private theorem initial_le_log (p : ℕ) [NeZero p] : x p 0 ≤ log (p : ℝ) := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hk : (1 : ℝ) ≤ p.sqrt := by exact_mod_cast Nat.sqrt_pos.mpr hp
  exact log_le_log (div_pos (Nat.cast_pos.mpr hp) (zero_lt_one.trans_le hk))
    (div_le_self (Nat.cast_nonneg _) hk)

private theorem log_stageCount_le (p : ℕ) [NeZero p] :
    log (1 + (stageCount p : ℝ)) ≤ 1 + log (p : ℝ) := by
  have h := stageCount_le p
  have hlog := initial_le_log p
  have hcount := log_le_sub_one_of_pos (show 0 < 1 + (stageCount p : ℝ) by positivity)
  linarith [log_natCast_nonneg p]

private theorem one_add_log_le_sqrt_log {p : ℕ} (hk : 2 ≤ p.sqrt) :
    1 + log (p : ℝ) ≤ 6 * log (p.sqrt : ℝ) := by
  let k : ℝ := p.sqrt
  have hk' : 2 ≤ k := by
    change (2 : ℝ) ≤ (p.sqrt : ℝ)
    exact_mod_cast hk
  have hp : (p : ℝ) ≤ (k + 1) ^ 2 := by
    change (p : ℝ) ≤ ((p.sqrt : ℝ) + 1) ^ 2
    exact_mod_cast (Nat.lt_succ_sqrt' p).le
  have hp2 : (p : ℝ) ≤ (2 * k) ^ 2 := hp.trans
    (pow_le_pow_left₀ (by positivity) (by linarith) 2)
  have hp0 : 0 < p := Nat.sqrt_pos.mp (by omega)
  have hlog := log_le_log (Nat.cast_pos.mpr hp0) hp2
  rw [log_pow, log_mul (by norm_num) (by positivity : k ≠ 0)] at hlog
  have hklog : log 2 ≤ log k := log_le_log (by norm_num) hk'
  norm_num at hlog
  change 1 + log (p : ℝ) ≤ 6 * log k
  linarith [half_le_log_two]

private theorem log_sqrt_le_initial (p : ℕ) (hk : 0 < p.sqrt) : log (p.sqrt : ℝ) ≤ x p 0 := by
  have hk' : (0 : ℝ) < p.sqrt := Nat.cast_pos.mpr hk
  have hsq : (p.sqrt : ℝ) ^ 2 ≤ p := by exact_mod_cast Nat.sqrt_le' p
  apply log_le_log hk'
  apply (le_div_iff₀ hk').mpr
  simpa only [pow_two] using hsq

private theorem small_log_eventually :
    ∀ᶠ t : ℝ in atTop, 6 * log t ≤ t ^ (0.005 : ℝ) := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 0.005)).bound
    (show (0 : ℝ) < 1 / 6 by norm_num)
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with t ht ht1
  change ‖log t‖ ≤ 1 / 6 * ‖t ^ (0.005 : ℝ)‖ at ht
  rw [Real.norm_of_nonneg (log_nonneg ht1), Real.norm_of_nonneg (by positivity)] at ht
  linarith

private theorem absorb_constant {a b : ℝ} (hab : a < b) (C : ℝ) :
    ∀ᶠ t : ℝ in atTop, C * t ^ a ≤ t ^ b := by
  filter_upwards [(tendsto_rpow_atTop (sub_pos.mpr hab)).eventually_ge_atTop C,
    eventually_gt_atTop (0 : ℝ)] with t hC ht
  rw [show b = (b - a) + a by ring, rpow_add ht]
  exact mul_le_mul_of_nonneg_right hC (rpow_nonneg ht.le _)

private def lawConstant : ℝ := 7 * 18 * exp 2000 * (4 : ℝ) ^ (11 / 25 : ℝ)

private def containerConstant : ℝ := 48 * 18 * exp 3000 * (4 : ℝ) ^ (33 / 50 : ℝ)

private theorem lawExponent_le {p : ℕ} (hlog : 1 + log (p : ℝ) ≤ (p.sqrt : ℝ) ^ (0.005 : ℝ)) :
    lawExponent p ≤ lawConstant * (p.sqrt : ℝ) ^ (0.45 : ℝ) := by
  let k : ℝ := p.sqrt
  have hsq := pow_le_pow_left₀ (by linarith [log_natCast_nonneg p] : 0 ≤ 1 + log (p : ℝ)) hlog 2
  have hnonneg : 0 ≤ lawConstant * k ^ (11 / 25 : ℝ) := by unfold lawConstant; positivity
  have hpow : (k ^ (0.005 : ℝ)) ^ (2 : ℕ) = k ^ (0.01 : ℝ) := by
    rw [← rpow_mul_natCast (by positivity), show (0.005 : ℝ) * (2 : ℕ) = 0.01 by norm_num]
  rw [hpow] at hsq
  unfold lawExponent
  rw [mul_rpow (by norm_num) (Nat.cast_nonneg _), ← mul_assoc]
  change lawConstant * k ^ (11 / 25 : ℝ) * (1 + log (p : ℝ)) ^ 2 ≤ _
  calc
    _ ≤ lawConstant * k ^ (11 / 25 : ℝ) * k ^ (0.01 : ℝ) :=
      mul_le_mul_of_nonneg_left hsq hnonneg
    _ = _ := by
      rw [mul_assoc, ← rpow_add' (by positivity : 0 ≤ k) (by norm_num : (11 / 25 : ℝ) + 0.01 ≠ 0)]
      rw [show (11 / 25 : ℝ) + (0.01 : ℝ) = 0.45 by norm_num]

private theorem containerExponent_le {p : ℕ}
    (hlog : 1 + log (p : ℝ) ≤ (p.sqrt : ℝ) ^ (0.005 : ℝ)) :
    containerExponent p ≤ containerConstant * (p.sqrt : ℝ) ^ (0.675 : ℝ) := by
  let k : ℝ := p.sqrt
  have hL : 0 ≤ 1 + log (p : ℝ) := by linarith [log_natCast_nonneg p]
  have ht := log_le_sub_one_of_pos (show 0 < 1 + log (p : ℝ) by linarith [log_natCast_nonneg p])
  have hcube := pow_le_pow_left₀ hL hlog 3
  have hpow : (k ^ (0.005 : ℝ)) ^ (3 : ℕ) = k ^ (0.015 : ℝ) := by
    rw [← rpow_mul_natCast (by positivity), show (0.005 : ℝ) * (3 : ℕ) = 0.015 by norm_num]
  rw [hpow] at hcube
  have hnonneg : 0 ≤ containerConstant * k ^ (33 / 50 : ℝ) := by unfold containerConstant; positivity
  unfold containerExponent
  rw [mul_rpow (by norm_num) (Nat.cast_nonneg _), ← mul_assoc]
  change containerConstant * k ^ (33 / 50 : ℝ) * (1 + log (p : ℝ)) ^ 2 *
    (1 + log (1 + log (p : ℝ))) ≤ _
  calc
    _ ≤ containerConstant * k ^ (33 / 50 : ℝ) * (1 + log (p : ℝ)) ^ 2 *
        (1 + log (p : ℝ)) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = containerConstant * k ^ (33 / 50 : ℝ) * (1 + log (p : ℝ)) ^ 3 := by ring
    _ ≤ containerConstant * k ^ (33 / 50 : ℝ) * k ^ (0.015 : ℝ) :=
      mul_le_mul_of_nonneg_left hcube hnonneg
    _ = _ := by
      rw [mul_assoc, ← rpow_add' (by positivity : 0 ≤ k) (by norm_num : (33 / 50 : ℝ) + 0.015 ≠ 0)]
      rw [show (33 / 50 : ℝ) + (0.015 : ℝ) = 0.675 by norm_num]

def terminalLogConstant : ℝ := 9 * terminalCoefficient

theorem terminalLogConstant_nonneg : 0 ≤ terminalLogConstant := by
  have hlog : 0 ≤ log (2 * (10000 : ℝ) ^ 2) := log_nonneg (by norm_num)
  unfold terminalLogConstant terminalCoefficient Transcripts.inverseEta
  positivity

variable {ι : Type*} {l : Filter ι}

/-- These bounds hold along any cofinal family, in particular along the primes. -/
theorem concreteCatalog_eventual_bounds (m : ι → ℕ) [∀ i, NeZero (m i)]
    (hm : Tendsto m l atTop) :
    ∀ᶠ i in l,
      let C := concreteCatalog (m i)
      let k := ((m i).sqrt : ℝ)
      Transcripts.logCard (C.containers C.stages) ≤ terminalLogConstant * log (m i : ℝ) ^ (2 : ℝ) ∧
      (((range C.stages).biUnion C.laws).card : ℝ) ≤ exp (k ^ (0.46 : ℝ)) ∧
      (∑ j ∈ range C.stages, ((C.containers j).card : ℝ) * (C.laws j).card) ≤ exp (k ^ (0.70 : ℝ)) := by
  have hkNat : Tendsto (fun i => (m i).sqrt) l atTop := by
    apply tendsto_atTop.mpr
    intro b
    exact (hm.eventually_ge_atTop (b * b)).mono fun _ h => Nat.le_sqrt.mpr h
  have hkReal : Tendsto (fun i => ((m i).sqrt : ℝ)) l atTop :=
    tendsto_natCast_atTop_atTop.comp hkNat
  have hlaw := hkReal.eventually (absorb_constant (a := 0.45) (b := 0.46) (by norm_num) (1 + lawConstant))
  have hcost := hkReal.eventually
    (absorb_constant (a := 0.675) (b := 0.70) (by norm_num) (1 + containerConstant + lawConstant))
  have hactive := (tendsto_log_atTop.comp hkReal).eventually_gt_atTop 5000
  filter_upwards [hkNat.eventually_ge_atTop 2, hkReal.eventually small_log_eventually, hlaw, hcost,
    hactive] with i hk hs hlaw hcost ha
  dsimp only
  let p := m i
  let k : ℝ := p.sqrt
  have hkP : 2 ≤ p.sqrt := hk
  have hk1 : 1 ≤ k := by
    change (1 : ℝ) ≤ (p.sqrt : ℝ)
    exact_mod_cast (show 1 ≤ p.sqrt from (by decide : 1 ≤ 2).trans hkP)
  have hL : 1 + log (p : ℝ) ≤ k ^ (0.005 : ℝ) := (one_add_log_le_sqrt_log hk).trans hs
  have hcount := (log_stageCount_le p).trans hL
  have hlaw' := lawExponent_le hL
  have hcost' := containerExponent_le hL
  have hsmallLaw : k ^ (0.005 : ℝ) ≤ k ^ (0.45 : ℝ) :=
    rpow_le_rpow_of_exponent_le hk1 (by norm_num)
  have hlawCost : k ^ (0.45 : ℝ) ≤ k ^ (0.675 : ℝ) :=
    rpow_le_rpow_of_exponent_le hk1 (by norm_num)
  have hpos := stageCount_pos (ha.trans_le (log_sqrt_le_initial p ((by decide : 0 < 2).trans_le hkP)))
  refine ⟨?_, ?_, ?_⟩
  · have hplog : (1 / 2 : ℝ) ≤ log (p : ℝ) := half_le_log_two.trans
      (log_le_log (by norm_num) (by exact_mod_cast hk.trans (Nat.sqrt_le_self p)))
    have hcoeff : 0 ≤ terminalCoefficient := by
      have h := terminalLogConstant_nonneg
      unfold terminalLogConstant at h
      linarith
    apply (concreteCatalog_log_terminal p hpos).trans
    rw [rpow_two, terminalLogConstant]
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + log (p : ℝ))
      (show 1 + log (p : ℝ) ≤ 3 * log (p : ℝ) by linarith) 2
    have hscaled := mul_le_mul_of_nonneg_left hsq hcoeff
    calc
      _ ≤ terminalCoefficient * (3 * log (p : ℝ)) ^ 2 := hscaled
      _ = _ := by ring
  · have hlogCount := concreteCatalog_log_allLaws p
    have hbound : log (1 + (stageCount p : ℝ)) + lawExponent p ≤ k ^ (0.46 : ℝ) := by
      apply (add_le_add (hcount.trans hsmallLaw) hlaw').trans
      rw [← one_add_mul]
      exact hlaw
    have hh := (log_le_iff_le_exp (by positivity)).mp (hlogCount.trans hbound)
    linarith
  · apply (concreteCatalog_sum_card_products p).trans
    have hlawBig : lawExponent p ≤ lawConstant * k ^ (0.675 : ℝ) :=
      hlaw'.trans (mul_le_mul_of_nonneg_left hlawCost (by unfold lawConstant; positivity))
    have hbound : log (1 + (stageCount p : ℝ)) + (containerExponent p + lawExponent p) ≤
        k ^ (0.70 : ℝ) := by
      apply (add_le_add ((hcount.trans hsmallLaw).trans hlawCost) (add_le_add hcost' hlawBig)).trans
      calc
        _ = (1 + containerConstant + lawConstant) * k ^ (0.675 : ℝ) := by
          change k ^ (0.675 : ℝ) + (containerConstant * k ^ (0.675 : ℝ) +
            lawConstant * k ^ (0.675 : ℝ)) = _
          ring
        _ ≤ _ := hcost
    calc
      _ ≤ (1 + (stageCount p : ℝ)) * exp (containerExponent p + lawExponent p) := by gcongr; linarith
      _ = exp (log (1 + (stageCount p : ℝ)) + (containerExponent p + lawExponent p)) := by
        rw [exp_add (log (1 + (stageCount p : ℝ))) (containerExponent p + lawExponent p),
          exp_log (by positivity)]
      _ ≤ _ := exp_le_exp.mpr hbound

end

end Green39.Assembly

end CatalogRates

/- Source: one-percent-formal/smooth-law/SmoothRate.lean -/
section SmoothRate

open Filter Asymptotics
open scoped Topology

namespace Green39.Smooth
noncomputable section

/-- Scalar upper bound for the joint failure event with the manuscript's constants. -/
def paperRate (N p k : ℝ) := N*(2*Real.exp (-k/320000000000000000) +
    p*Real.exp (10^24 - (10^24/2)*Real.sqrt k) +
    p*Real.exp (-(9:ℝ)/10000*Real.sqrt k))

theorem paperRate_le {N p k : ℝ} (hN : 0 ≤ N) (hp : 1 ≤ p)
    (hk : 10^16 ≤ Real.sqrt k) (hcost : N*p ≤ Real.exp (Real.sqrt k/10000)) :
    paperRate N p k ≤ 4*Real.exp (-(8:ℝ)/10000*Real.sqrt k) := by
  let r := Real.sqrt k
  have hr : (10:ℝ)^16 ≤ r := hk
  have hk0 : 0 ≤ k := by
    by_contra! h
    rw [Real.sqrt_eq_zero_of_nonpos h.le] at hk
    norm_num at hk
  have hr2 : r^2 = k := Real.sq_sqrt hk0
  have hr0 : 0 ≤ r := Real.sqrt_nonneg k
  have h₁ : -k/320000000000000000 ≤ -(9:ℝ)/10000*r := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) hr0]
  have h₂ : (10:ℝ)^24 - (10^24/2)*r ≤ -(9:ℝ)/10000*r := by linarith
  let e := Real.exp (-(9:ℝ)/10000*r)
  have he : 0 ≤ e := Real.exp_nonneg _
  calc
    paperRate N p k ≤ N*(2*e + p*e + p*e) := by
      unfold paperRate
      exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h₁) (by norm_num : (0:ℝ) ≤ 2))
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h₂) (zero_le_one.trans hp))) le_rfl) hN
    _ ≤ 4*(N*p)*e := by
      have hpe := mul_le_mul_of_nonneg_right hp he
      nlinarith [mul_nonneg hN (sub_nonneg.mpr hpe)]
    _ ≤ 4*Real.exp (r/10000)*e := by gcongr
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- If the logarithmic family-and-shift cost is o(√k), the explicit finite error tends to zero. -/
theorem paperRate_tendsto {N p k : ℕ → ℝ} (hN : ∀ n, 0 ≤ N n) (hp : ∀ n, 1 ≤ p n)
    (hk : Tendsto k atTop atTop)
    (hcost : (fun n ↦ Real.log (1+N n*p n)) =o[atTop] (fun n ↦ Real.sqrt (k n))) :
    Tendsto (fun n ↦ paperRate (N n) (p n) (k n)) atTop (𝓝 0) := by
  have hr := Real.tendsto_sqrt_atTop.comp hk
  have hu : Tendsto (fun n ↦ 4*Real.exp (-(8:ℝ)/10000*Real.sqrt (k n))) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using (Real.tendsto_exp_atBot.comp
      (hr.const_mul_atTop_of_neg (show -(8:ℝ)/10000 < 0 by norm_num))).const_mul 4
  apply squeeze_zero' _ _ hu
  · exact Filter.Eventually.of_forall fun n ↦ by
      dsimp [paperRate]
      have hp0 := (zero_le_one.trans (hp n))
      have hN0 := hN n
      positivity
  · filter_upwards [hr.eventually_ge_atTop (10^16), hcost.bound (show 0 < (1:ℝ)/10000 by norm_num)]
      with n hn hc
    apply paperRate_le (hN n) (hp n) hn
    have hpos : 0 < 1+N n*p n := by
      have hh := mul_nonneg (hN n) (zero_le_one.trans (hp n))
      linarith
    have hlog : Real.log (1+N n*p n) ≤ Real.sqrt (k n)/10000 := by
      simp only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at hc
      linarith [le_abs_self (Real.log (1+N n*p n))]
    have h := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log hpos] at h
    linarith

end
end Green39.Smooth

end SmoothRate

/- Source: one-percent-formal/smooth-law/EquationFour.lean -/
section EquationFour

open Filter Asymptotics
open scoped BigOperators Classical Topology
open Green39.Concentration

namespace Green39.Smooth
noncomputable section

/-- Probability that either assertion of (4) fails, for the manuscript's actual split sizes. -/
def eqFourFailure {p : ℕ} [NeZero p] {ι : Type*} (I : Finset ι) (μ : ι → ZMod p → ℝ) :=
  let k := p.sqrt
  let a := k/2
  splitProb Finset.univ a (k-a) (fun A B ↦ ∃ i ∈ I,
    (k:ℝ)/100000000 < l1 (μ i) (k-a) B ∨ ∃ v, (1:ℝ)/1000 <
      ∑ z ∈ B, excess (μ i) A ((51:ℝ)/(100*k)) v z)

theorem eqFourFailure_le {p : ℕ} [NeZero p] {ι : Type*} (I : Finset ι) (μ : ι → ZMod p → ℝ)
    (hp : 4 ≤ p) (hn : ∀ i ∈ I, ∀ x, 0 ≤ μ i x) (hm : ∀ i ∈ I, ∑ x, μ i x = 1)
    (hc : ∀ i ∈ I, ∀ x, μ i x ≤ 2/(10^24*(p.sqrt:ℝ))) :
    eqFourFailure I μ ≤ paperRate I.card p p.sqrt := by
  have hk : 2 ≤ p.sqrt := Nat.le_sqrt.mpr hp
  have hh : p ≤ 2*p.sqrt^2 := by
    have h := Nat.sqrt_le_add p
    nlinarith [Nat.mul_le_mul_right p.sqrt hk]
  have h := paper_equation_four I μ (k := p.sqrt) (a := p.sqrt/2) (b := p.sqrt-p.sqrt/2)
    hk (by omega) (by omega) (by omega) (by omega) (by rw [ZMod.card]; exact Nat.sqrt_le' p)
    (by rwa [ZMod.card]) hn hm hc
  simpa only [eqFourFailure, paperRate, ZMod.card] using h

private theorem eqFourFailure_nonneg {p : ℕ} [NeZero p] {ι : Type*}
    (I : Finset ι) (μ : ι → ZMod p → ℝ) : 0 ≤ eqFourFailure I μ := by
  unfold eqFourFailure splitProb splitMean sliceMean mean
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro A _
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact Finset.sum_nonneg (fun _ _ ↦ by dsimp only; split <;> norm_num)

/-- Equation (4) with probability tending to one. The family may vary with p.
The input from §3 is precisely that the logarithm of the law-and-shift count is o(√k). -/
theorem eqFourFailure_tendsto {p : ℕ → ℕ} [∀ n, NeZero (p n)] {ι : ℕ → Type*}
    (I : ∀ n, Finset (ι n)) (μ : ∀ n, ι n → ZMod (p n) → ℝ)
    (hp : Tendsto p atTop atTop)
    (hn : ∀ n i, i ∈ I n → ∀ x, 0 ≤ μ n i x)
    (hm : ∀ n i, i ∈ I n → ∑ x, μ n i x = 1)
    (hc : ∀ n i, i ∈ I n → ∀ x, μ n i x ≤ 2/(10^24*((p n).sqrt:ℝ)))
    (hcost : (fun n ↦ Real.log (1+((I n).card:ℝ)*(p n))) =o[atTop]
      (fun n ↦ Real.sqrt ((p n).sqrt:ℝ))) :
    Tendsto (fun n ↦ eqFourFailure (I n) (μ n)) atTop (𝓝 0) := by
  have hs : Tendsto (fun n ↦ (p n).sqrt) atTop atTop := by
    apply tendsto_atTop.mpr
    intro a
    filter_upwards [hp.eventually_ge_atTop (a^2)] with n h
    exact Nat.le_sqrt'.mpr h
  have hr : Tendsto (fun n ↦ ((p n).sqrt:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hs
  have hrate := paperRate_tendsto (N := fun n ↦ ((I n).card:ℝ)) (p := fun n ↦ (p n:ℝ))
    (fun _ ↦ Nat.cast_nonneg _) (fun n ↦ by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne (p n)))
    hr hcost
  apply squeeze_zero' (Eventually.of_forall (fun n ↦ eqFourFailure_nonneg (I n) (μ n))) _ hrate
  filter_upwards [hp.eventually_ge_atTop 4] with n h
  exact eqFourFailure_le _ _ h (hn n) (hm n) (hc n)

end
end Green39.Smooth

end EquationFour

/- Source: one-percent-formal/smooth-law/CatalogLaw.lean -/
section CatalogLaw

open scoped BigOperators Classical Pointwise
open Finset Filter Real
open Green39.Assembly Green39.Split OnePercent.Fourier

namespace Green39.Smooth
noncomputable section

theorem ordered_eq_split {α : Type*} [DecidableEq α] (s : Finset α) (a b : ℕ)
    (E : Finset α → Finset α → Prop) :
    probability (orderedPairs s a b) (fun q ↦ E q.1 q.2) = splitProb s a b E := by
  rw [probability_eq_mean_first]
  unfold splitProb splitMean
  simp_rw [sm_event]
  rfl

theorem typical_failure_le {p : ℕ} [NeZero p] (hp : 4 ≤ p) (μ : Law p)
    (hn : ∀ x, 0 ≤ μ x) (hm : ∑ x, μ x = 1) (hc : ∀ x, μ x ≤ 2/(10^24*(p.sqrt:ℝ))) :
    probability (orderedPairs (univ : Points p) (half p.sqrt) (rest p.sqrt))
      (fun q ↦ ¬typical μ q) ≤ paperRate 1 p p.sqrt := by
  let k := p.sqrt
  let c := (51:ℝ)/(100*k)
  let E (A B : Points p) := (k:ℝ)/100000000 < l1 μ (rest k) B ∨
    ∃ v, (1:ℝ)/1000 < ∑ z ∈ B, excess μ A c v z
  have h := eqFourFailure_le ({μ} : Finset (Law p)) id hp
    (by simpa using hn) (by simpa using hm) (by simpa using hc)
  have he : probability (orderedPairs (univ:Points p) (half k) (rest k))
      (fun q ↦ E q.1 q.2) ≤ paperRate 1 p k := by
    rw [ordered_eq_split]
    simpa [eqFourFailure,E,k,c,half,rest] using h
  refine (probability_mono ?_).trans he
  intro q hq hbad
  have h2 := (mem_orderedPairs.mp hq).2.2.2.1
  by_contra hnot
  change ¬ (_ ∨ _) at hnot
  push Not at hnot
  apply hbad
  have hconv (u : ZMod p) : convolution (indicator q.2) μ u = conv μ q.2 u :=
    convolution_indicator _ _ _
  have hsm (z : ZMod p) : smoothed q.1 μ z = conv (fun t ↦ μ (-t)) q.1 z := by
    simp only [smoothed_eq_convolution,convolution_indicator,conv]
  constructor
  · rw [show (0.00000001:ℝ)*(p.sqrt:ℝ) = k/100000000 by dsimp [k]; ring]
    simpa only [hconv,h2,l1,ZMod.card] using hnot.1
  · intro v
    simpa only [excess,← hsm,show c = 0.51/(p.sqrt:ℝ) by dsimp [c,k]; ring,
      show (1:ℝ)/1000 = 0.001 by norm_num] using hnot.2 v

private abbrev Primes := {p : ℕ // p.Prime}
local instance (p : Primes) : NeZero p.val := ⟨p.property.ne_zero⟩

/-- The expansions of `Assembly.allLaws` and `Assembly.space` avoid importing the
assembly endpoint back into its own input. The conclusion is definitionally its hsmooth. -/
theorem hsmooth_of_rate (C : (p : {n : ℕ // n.Prime}) → Catalog p.val)
    (hstage : ∀ᶠ p in atTop, StageSpec (C p))
    (hr : ∀ᶠ p : ℕ in atTop, paperRate 1 p p.sqrt ≤ exp (-((p.sqrt:ℝ)^(0.48:ℝ)))) :
    ∀ᶠ p in atTop, ∀ μ ∈ (range (C p).stages).biUnion (C p).laws,
      probability (orderedPairs (univ : Points p.val) (half p.val.sqrt) (rest p.val.sqrt))
        (fun q ↦ ¬typical μ q) ≤ exp (-((p.val.sqrt:ℝ)^(0.48:ℝ))) := by
  have hpr : Tendsto (fun p : {n : ℕ // n.Prime} ↦ p.val) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    obtain ⟨n,hn,hp⟩ := Nat.exists_infinite_primes b
    exact (eventually_ge_atTop (⟨n,hp⟩ : {n : ℕ // n.Prime})).mono fun _ h ↦ hn.trans h
  filter_upwards [hstage, hpr.eventually_ge_atTop 4, hpr.eventually hr] with p hs h4 hrate μ hμ
  obtain ⟨i,hi,hiμ⟩ := mem_biUnion.mp hμ
  obtain ⟨hn,hm,hc⟩ := hs.capped i (mem_range.mp hi) μ hiμ
  exact (typical_failure_le h4 μ hn hm hc).trans hrate

end
end Green39.Smooth

end CatalogLaw

/- Source: one-percent-formal/smooth-law/SingletonRate.lean -/
section SingletonRate

open Filter Real
namespace Green39.Smooth

theorem singleton_paperRate : ∀ᶠ p : ℕ in atTop,
    paperRate 1 p p.sqrt ≤ exp (-((p.sqrt : ℝ)^(0.48:ℝ))) := by
  have hs : Tendsto Nat.sqrt atTop atTop := by
    refine tendsto_atTop.mpr fun k => (eventually_ge_atTop (k^2)).mono ?_
    exact fun _ hp => Nat.le_sqrt'.mpr hp
  have hk : Tendsto (fun p : ℕ => (p.sqrt : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hs
  have hr := Real.tendsto_sqrt_atTop.comp hk
  have hl := hk.eventually ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/2)).bound
    (by norm_num : (0:ℝ) < 1/30000))
  have hm := hk.eventually ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/2-0.48)).eventually_ge_atTop 2500)
  filter_upwards [hs.eventually_ge_atTop 4, hr.eventually_ge_atTop ((10:ℝ)^16), hl, hm] with p h4 hbig hlog hmargin
  let k : ℝ := p.sqrt
  have hk4 : 4 ≤ k := by dsimp [k]; exact_mod_cast h4
  have hk0 : 0 < k := by linarith
  have hp1 : 1 ≤ p := by have := Nat.sqrt_le_self p; omega
  have hp3 : p ≤ p.sqrt^3 := by
    have h := Nat.lt_succ_sqrt' p
    have hm₁ := Nat.mul_le_mul_left p.sqrt h4
    have hm₂ := Nat.mul_le_mul_left (p.sqrt^2) h4
    rw [Nat.succ_eq_add_one] at h
    nlinarith
  have hcost : (p:ℝ) ≤ exp (sqrt k/10000) := by
    change ‖log k‖ ≤ (1/30000:ℝ)*‖k^(1/2:ℝ)‖ at hlog
    rw [← Real.sqrt_eq_rpow, Real.norm_of_nonneg (sqrt_nonneg _),
      Real.norm_of_nonneg (log_nonneg (by linarith))] at hlog
    rw [← Real.exp_log (show 0 < (p:ℝ) by exact_mod_cast (show 0 < p by omega))]
    apply Real.exp_le_exp.mpr
    have hl' := Real.log_le_log (by exact_mod_cast (show 0 < p by omega) : (0:ℝ)<p)
      (show (p:ℝ) ≤ k^(3:ℕ) by dsimp [k]; exact_mod_cast hp3)
    rw [log_pow] at hl'
    norm_num at hl'
    linarith only [hl', hlog]
  have h := paperRate_le (N:=1) (p:=(p:ℝ)) (k:=k) (by norm_num) (by exact_mod_cast hp1) hbig (by simpa using hcost)
  have hz : (2500:ℝ)*k^(0.48:ℝ) ≤ sqrt k := by
    rw [sqrt_eq_rpow, show (1/2:ℝ) = (1/2-0.48)+0.48 by norm_num, rpow_add hk0]
    exact mul_le_mul_of_nonneg_right hmargin (rpow_nonneg hk0.le _)
  have hlog4 : log (4:ℝ) ≤ 4 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : 0 < (4:ℝ))]
  change (10:ℝ)^16 ≤ sqrt k at hbig
  apply h.trans
  conv_lhs => lhs; rw [← Real.exp_log (by norm_num : 0 < (4:ℝ))]
  rw [← exp_add]
  apply exp_le_exp.mpr
  linarith

end Green39.Smooth

end SingletonRate

/- Source: one-percent-formal/smooth-law/CatalogEndpoint.lean -/
section CatalogEndpoint

open Finset Filter Real
open scoped Classical
open Green39.Assembly Green39.Split

namespace Green39.Smooth
noncomputable section

local instance (p : {n : ℕ // n.Prime}) : NeZero p.val := ⟨p.property.ne_zero⟩

/-- The hsmooth input of Assembly.tendsto_zero_of_catalog.
Only the deterministic stage specification is required of the catalog. -/
theorem hsmooth (C : (p : {n : ℕ // n.Prime}) → Catalog p.val)
    (hstage : ∀ᶠ p in atTop, StageSpec (C p)) :
    ∀ᶠ p in atTop, ∀ μ ∈ (range (C p).stages).biUnion (C p).laws,
      probability (orderedPairs (univ : Points p.val) (half p.val.sqrt) (rest p.val.sqrt))
        (fun q ↦ ¬typical μ q) ≤ exp (-((p.val.sqrt:ℝ)^(0.48:ℝ))) :=
  hsmooth_of_rate C hstage singleton_paperRate

end
end Green39.Smooth

end CatalogEndpoint

/- Source: one-percent-formal/final/Green39Result.lean -/
section Green39Result

open Filter Topology Finset Real
open scoped Classical

namespace Green39.OnePercentResult
open Green39.Assembly

local instance (p : Prime) : NeZero p.val := ⟨p.property.ne_zero⟩

/-- The proportion of uniformly chosen square-root-size sets covered at the
one-percent budget tends to zero along the primes. -/
theorem coverable_tendsto_zero : Tendsto sliceCover atTop (𝓝 0) := by
  let C : (p : Prime) → Catalog p.val := fun p => concreteCatalog p.val
  have hstage : ∀ᶠ p in atTop, StageSpec (C p) :=
    Eventually.of_forall fun p => concreteCatalog_spec p.val
  have h := concreteCatalog_eventual_bounds (fun p : Prime => p.val) prime_cofinal
  exact tendsto_zero_of_catalog C terminalLogConstant_nonneg hstage
    (h.mono fun _ hx => hx.1) (h.mono fun _ hx => hx.2.1)
    (h.mono fun _ hx => hx.2.2) (Green39.Smooth.hsmooth C hstage)

/-- Negation of the exact one-percent variant in the pinned statement. -/
theorem disproof : ¬ (type_of% @Green39.green_39.variant_101) :=
  exact_negation coverable_tendsto_zero

end Green39.OnePercentResult

end Green39Result

theorem OMA.disproof : ¬ (type_of% @Green39.green_39.variant_101) :=
  Green39.OnePercentResult.disproof
