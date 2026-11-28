import OMAStatements.S_oeis_a294413
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

-- Problem: A294413: Golden-ratio limit of complementary sequence a(n) = a(n-1) + a(n-2) - b(n-1) + 6.
-- Upstream: formal-conjectures statements/oeis-a294413.lean:0 (declaration OMA.S_oeis_a294413.main)
-- Credit: Daniel Whorlow (@draonbioetl)
-- Elementary proof via pigeonhole bound b(n) <= 2*n + 2, exponential growth a(n) >= (4/3)^n,
-- and contracting recurrence d(n+1) = psi * d(n) + (6 - b(n+1)) for d(n) = a(n+1) - phi * a(n).

namespace OMA_A294413

open OMA.S_oeis_a294413 Finset Filter

/-- Pigeonhole bound for complementary strictly increasing sequences:
if `a k > N` and `b k > N`, then `N ≤ 2 * k`. -/
private lemma pigeonhole_le {a b : ℕ → ℕ} (h : Solution a b) {N k : ℕ}
    (ha : N < a k) (hb : N < b k) : N ≤ 2 * k := by
  classical
  have hsub : Icc 1 N ⊆ (range k).image a ∪ (range k).image b := by
    intro m hm
    have hm1 : 1 ≤ m := (mem_Icc.mp hm).1
    have hmN : m ≤ N := (mem_Icc.mp hm).2
    rcases h.cover m (by omega) with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · apply mem_union_left
      refine mem_image.mpr ⟨i, mem_range.mpr ?_, rfl⟩
      by_contra hge
      have : a k ≤ a i := h.strict_a.monotone (by omega)
      omega
    · apply mem_union_right
      refine mem_image.mpr ⟨j, mem_range.mpr ?_, rfl⟩
      by_contra hge
      have : b k ≤ b j := h.strict_b.monotone (by omega)
      omega
  have hcard := card_le_card hsub
  have hcard_icc : (Icc 1 N).card = N := by simp
  have hcard_union : ((range k).image a ∪ (range k).image b).card ≤ 2 * k := by
    calc
      ((range k).image a ∪ (range k).image b).card
          ≤ ((range k).image a).card + ((range k).image b).card := card_union_le _ _
      _ ≤ (range k).card + (range k).card := add_le_add card_image_le card_image_le
      _ = 2 * k := by rw [card_range]; ring
  omega

private lemma a_two {a b : ℕ → ℕ} (h : Solution a b) : a 2 = 6 := by
  have hrec := h.recurrence 0
  simp only [Nat.zero_add] at hrec
  rw [h.a_zero, h.a_one, h.b_one] at hrec
  omega

private lemma a_pos {a b : ℕ → ℕ} (h : Solution a b) (n : ℕ) : 0 < a n := by
  have : a 0 ≤ a n := h.strict_a.monotone (Nat.zero_le n)
  rw [h.a_zero] at this
  omega

/-- Simultaneous linear lower bound `3 * n + 3 ≤ a (n + 1)` for all `n`. -/
private lemma a_ge_three_mul {a b : ℕ → ℕ} (h : Solution a b) :
    ∀ n : ℕ, 3 * n + 3 ≤ a (n + 1) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 =>
      rw [h.a_one]
    | 1 =>
      rw [a_two h]
    | n + 2 =>
      have h1 : 3 * n + 3 ≤ a (n + 1) := ih n (by omega)
      have h2 : 3 * (n + 1) + 3 ≤ a (n + 2) := ih (n + 1) (by omega)
      have hb : b (n + 2) ≤ 2 * n + 5 := by
        by_contra hgt
        have hpig := pigeonhole_le h (N := 2 * n + 5) (k := n + 2) (by omega) (by omega)
        omega
      have hrec := h.recurrence (n + 1)
      have h3 : n + 1 + 2 = n + 2 + 1 := by omega
      have h2' : n + 1 + 1 = n + 2 := by omega
      rw [h3, h2'] at hrec
      omega

/-- Linear upper bound `b k ≤ 2 * k + 2` for all `k`. -/
private lemma b_le_two_mul_add_two {a b : ℕ → ℕ} (h : Solution a b) (k : ℕ) :
    b k ≤ 2 * k + 2 := by
  match k with
  | 0 => rw [h.b_zero]
  | 1 => rw [h.b_one]
  | k + 2 =>
    have ha : 2 * (k + 2) + 1 < a (k + 2) := by
      have := a_ge_three_mul h (k + 1)
      have heq : k + 1 + 1 = k + 2 := by omega
      rw [heq] at this
      omega
    by_contra hgt
    have hpig := pigeonhole_le h (N := 2 * (k + 2) + 1) (k := k + 2) ha (by omega)
    omega

private lemma b_two {a b : ℕ → ℕ} (h : Solution a b) : b 2 = 5 := by
  have hb2_gt : 4 < b 2 := by
    have : b 1 < b 2 := h.strict_b (by omega)
    rw [h.b_one] at this; exact this
  have hb2_le : b 2 ≤ 5 := by
    rcases h.cover 5 (by omega) with ⟨i, hi⟩ | ⟨j, hj⟩
    · exfalso
      have hi0 : i ≠ 0 := by intro h0; subst h0; rw [h.a_zero] at hi; omega
      have hi1 : i ≠ 1 := by intro h1; subst h1; rw [h.a_one] at hi; omega
      have hi2 : 2 ≤ i := by omega
      have : a 2 ≤ a i := h.strict_a.monotone hi2
      rw [a_two h, hi] at this; omega
    · have hj0 : j ≠ 0 := by intro h0; subst h0; rw [h.b_zero] at hj; omega
      have hj1 : j ≠ 1 := by intro h1; subst h1; rw [h.b_one] at hj; omega
      have hj2 : 2 ≤ j := by omega
      have : b 2 ≤ b j := h.strict_b.monotone hj2
      omega
  omega

private lemma a_three {a b : ℕ → ℕ} (h : Solution a b) : a 3 = 10 := by
  have hrec := h.recurrence 1
  change (a 3 : ℤ) = a 2 + a 1 - b 2 + 6 at hrec
  rw [h.a_one, a_two h, b_two h] at hrec
  omega

private lemma a_four_ge {a b : ℕ → ℕ} (h : Solution a b) : 14 ≤ a 4 := by
  have hrec := h.recurrence 2
  change (a 4 : ℤ) = a 3 + a 2 - b 3 + 6 at hrec
  have hb3 : b 3 ≤ 8 := b_le_two_mul_add_two h 3
  rw [a_two h, a_three h] at hrec
  omega

/-- Stronger linear lower bound `4 * n ≤ a n + 4` for all `n`. -/
private lemma four_mul_le_a_add_four {a b : ℕ → ℕ} (h : Solution a b) :
    ∀ n : ℕ, 4 * n ≤ a n + 4 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 => rw [h.a_zero]; omega
    | 1 => rw [h.a_one]; omega
    | 2 => rw [a_two h]; omega
    | 3 => rw [a_three h]; omega
    | 4 => have := a_four_ge h; omega
    | n + 5 =>
      have h1 : 4 * (n + 3) ≤ a (n + 3) + 4 := ih (n + 3) (by omega)
      have h2 : 4 * (n + 4) ≤ a (n + 4) + 4 := ih (n + 4) (by omega)
      have hb : b (n + 4) ≤ 2 * (n + 4) + 2 := b_le_two_mul_add_two h (n + 4)
      have hrec := h.recurrence (n + 3)
      have h5 : n + 3 + 2 = n + 5 := by omega
      have h4 : n + 3 + 1 = n + 4 := by omega
      rw [h5, h4] at hrec
      omega

/-- Exponential lower bound `(4 / 3 : ℝ) ^ n ≤ a n` for all `n`. -/
private lemma exp_lower_bound {a b : ℕ → ℕ} (h : Solution a b) :
    ∀ n : ℕ, (4 / 3 : ℝ) ^ n ≤ (a n : ℝ) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 =>
      rw [h.a_zero]; norm_num
    | 1 =>
      rw [h.a_one]; norm_num
    | n + 2 =>
      have h1 : (4 / 3 : ℝ) ^ n ≤ (a n : ℝ) := ih n (by omega)
      have h2 : (4 / 3 : ℝ) ^ (n + 1) ≤ (a (n + 1) : ℝ) := ih (n + 1) (by omega)
      have hstep : 2 * a (n + 2) ≥ 2 * a (n + 1) + a n := by
        have hrec := h.recurrence n
        have hb : b (n + 1) ≤ 2 * (n + 1) + 2 := b_le_two_mul_add_two h (n + 1)
        have ha4 : 4 * n ≤ a n + 4 := four_mul_le_a_add_four h n
        omega
      have hstepR : 2 * (a (n + 2) : ℝ) ≥ 2 * (a (n + 1) : ℝ) + (a n : ℝ) := by
        exact_mod_cast hstep
      have hpow_pos : (0 : ℝ) ≤ (4 / 3 : ℝ) ^ n := by positivity
      have hpow2 : (4 / 3 : ℝ) ^ (n + 2) = (16 / 9 : ℝ) * (4 / 3 : ℝ) ^ n := by
        rw [pow_succ, pow_succ]; ring
      have hpow1 : (4 / 3 : ℝ) ^ (n + 1) = (4 / 3 : ℝ) * (4 / 3 : ℝ) ^ n := by
        rw [pow_succ]; ring
      rw [hpow1] at h2
      rw [hpow2]
      linarith

/-- Linear-vs-exponential domination `6 * n + 36 ≤ 36 * (7 / 6) ^ n`. -/
private lemma lin_le_exp_seven_six :
    ∀ n : ℕ, 6 * (n : ℝ) + 36 ≤ 36 * (7 / 6 : ℝ) ^ n := by
  intro n
  induction n with
  | zero => norm_num
  | succ n ih =>
    push_cast
    rw [pow_succ]
    linarith

private lemma main_proof : ∀ a b : ℕ → ℕ, Solution a b →
    Tendsto (fun n : ℕ => (a (n + 1) : ℝ) / (a n : ℝ))
      atTop (nhds ((1 + Real.sqrt 5) / 2)) := by
  intro a b h
  set φ : ℝ := (1 + Real.sqrt 5) / 2
  set ψ : ℝ := (1 - Real.sqrt 5) / 2
  have hsq5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hsqrt5_gt1 : 1 < Real.sqrt 5 := by
    have : Real.sqrt 1 < Real.sqrt 5 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    simpa using this
  have hsqrt5_lt : Real.sqrt 5 < 7 / 3 := by
    have hlt : (5 : ℝ) < (7 / 3 : ℝ) ^ 2 := by norm_num
    have := Real.sqrt_lt_sqrt (by norm_num) hlt
    rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 7 / 3)] at this
  have hψ_abs : |ψ| ≤ 2 / 3 := by
    rw [abs_le]
    dsimp [ψ]
    constructor <;> linarith
  have hφψ_add : φ + ψ = 1 := by dsimp [φ, ψ]; ring
  have hφψ_mul : φ * ψ = -1 := by
    dsimp [φ, ψ]
    nlinarith [hsq5]
  -- Define `d n = a (n + 1) - φ * a n` and bound `|d n| ≤ 6 * n + 30`
  let d : ℕ → ℝ := fun n => (a (n + 1) : ℝ) - φ * (a n : ℝ)
  have hd_rec : ∀ n : ℕ, d (n + 1) = ψ * d n + (6 - (b (n + 1) : ℝ)) := by
    intro n
    have hrecZ := h.recurrence n
    have hrecR : (a (n + 2) : ℝ) = (a (n + 1) : ℝ) + (a n : ℝ) - (b (n + 1) : ℝ) + 6 := by
      exact_mod_cast hrecZ
    dsimp [d]
    rw [hrecR]
    have h1 : 1 - φ = ψ := by linarith [hφψ_add]
    have h2 : -(ψ * φ) = 1 := by linarith [hφψ_mul]
    calc
      (a (n + 1) : ℝ) + (a n : ℝ) - (b (n + 1) : ℝ) + 6 - φ * (a (n + 1) : ℝ)
          = (1 - φ) * (a (n + 1) : ℝ) + (-(ψ * φ)) * (a n : ℝ) + (6 - (b (n + 1) : ℝ)) := by
            rw [h2]; ring
      _ = ψ * ((a (n + 1) : ℝ) - φ * (a n : ℝ)) + (6 - (b (n + 1) : ℝ)) := by
            rw [h1]; ring
  have hd_bound : ∀ n : ℕ, |d n| ≤ 6 * (n : ℝ) + 30 := by
    intro n
    induction n with
    | zero =>
      dsimp [d]
      rw [h.a_zero, h.a_one]
      rw [abs_le]
      dsimp [φ]
      constructor <;> linarith
    | succ n ih =>
      rw [hd_rec n]
      have hbR : (b (n + 1) : ℝ) ≤ 2 * (n : ℝ) + 4 := by
        have hbN := b_le_two_mul_add_two h (n + 1)
        exact_mod_cast hbN
      have hb_abs : |6 - (b (n + 1) : ℝ)| ≤ 2 * (n : ℝ) + 10 := by
        rw [abs_le]
        have hb0 : (0 : ℝ) ≤ (b (n + 1) : ℝ) := Nat.cast_nonneg _
        constructor <;> linarith
      have hmul : |ψ| * |d n| ≤ (2 / 3 : ℝ) * (6 * (n : ℝ) + 30) := by
        exact mul_le_mul hψ_abs ih (abs_nonneg _) (by norm_num)
      calc
        |ψ * d n + (6 - (b (n + 1) : ℝ))|
            ≤ |ψ * d n| + |6 - (b (n + 1) : ℝ)| := abs_add_le _ _
        _ = |ψ| * |d n| + |6 - (b (n + 1) : ℝ)| := by rw [abs_mul]
        _ ≤ (2 / 3 : ℝ) * (6 * (n : ℝ) + 30) + (2 * (n : ℝ) + 10) := add_le_add hmul hb_abs
        _ ≤ 6 * ((n + 1 : ℕ) : ℝ) + 30 := by push_cast; linarith
  -- Show `(a (n + 1) : ℝ) / a n - φ → 0`, hence `a (n + 1) / a n → φ`!
  have hdiff_zero : Tendsto (fun n : ℕ => (a (n + 1) : ℝ) / (a n : ℝ) - φ) atTop (nhds 0) := by
    have hupper : Tendsto (fun n : ℕ => (36 : ℝ) * (7 / 8 : ℝ) ^ n) atTop (nhds 0) := by
      have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (7 / 8 : ℝ)) (by norm_num) (by norm_num)
      simpa using hpow.const_mul (36 : ℝ)
    have hlower : Tendsto (fun n : ℕ => -((36 : ℝ) * (7 / 8 : ℝ) ^ n)) atTop (nhds 0) := by
      simpa using hupper.neg
    have hbound : ∀ n : ℕ, |(a (n + 1) : ℝ) / (a n : ℝ) - φ| ≤ (36 : ℝ) * (7 / 8 : ℝ) ^ n := by
      intro n
      have ha_pos : (0 : ℝ) < (a n : ℝ) := by exact_mod_cast a_pos h n
      have ha_ne : (a n : ℝ) ≠ 0 := ha_pos.ne'
      have hdiv_eq : (a (n + 1) : ℝ) / (a n : ℝ) - φ = d n / (a n : ℝ) := by
        dsimp [d]
        rw [sub_div, mul_div_cancel_right₀ _ ha_ne]
      rw [hdiv_eq, abs_div, abs_of_pos ha_pos]
      have hnum : |d n| ≤ 36 * (7 / 6 : ℝ) ^ n :=
        le_trans (hd_bound n) (le_trans (by linarith) (lin_le_exp_seven_six n))
      have hden : (4 / 3 : ℝ) ^ n ≤ (a n : ℝ) := exp_lower_bound h n
      have hden_pos : (0 : ℝ) < (4 / 3 : ℝ) ^ n := by positivity
      calc
        |d n| / (a n : ℝ) ≤ (36 * (7 / 6 : ℝ) ^ n) / (4 / 3 : ℝ) ^ n := by
          exact div_le_div₀ (by positivity) hnum hden_pos hden
        _ = 36 * ((7 / 6 : ℝ) / (4 / 3 : ℝ)) ^ n := by
          rw [mul_div_assoc, ← div_pow]
        _ = 36 * (7 / 8 : ℝ) ^ n := by
          congr 2; norm_num
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlower hupper
      (fun n => (abs_le.mp (hbound n)).1) (fun n => (abs_le.mp (hbound n)).2)
  have hres := hdiff_zero.add_const φ
  simpa using hres

end OMA_A294413

theorem OMA.solution : type_of% @OMA.S_oeis_a294413.main :=
  OMA_A294413.main_proof
