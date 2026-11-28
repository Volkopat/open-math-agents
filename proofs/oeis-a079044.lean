import OMAStatements.S_oeis_a079044
import Mathlib

/-!
# Negative partial sums of sin(j/π)

The integration-by-parts recurrence and integral bounds below are adapted
from Mathlib.Analysis.Real.Pi.Irrational, copyright (c) 2022 Bhavik Mehta,
released under the Apache License, Version 2.0. The integer recurrence here
uses rationality of the *square* of π/2.
-/

namespace SineIndex

open intervalIntegral MeasureTheory.MeasureSpace Set Real Filter
open scoped Nat

private noncomputable def I (n : ℕ) (θ : ℝ) : ℝ := ∫ x in (-1)..1, (1 - x ^ 2) ^ n * cos (x * θ)

variable {n : ℕ} {θ : ℝ}

private lemma I_zero : I 0 θ * θ = 2 * sin θ := by
  rw [mul_comm, I]
  simp [mul_integral_comp_mul_right, two_mul]

private lemma recursion' (n : ℕ) :
    I (n + 1) θ * θ ^ 2 = - (2 * 2 * ((n + 1) * (0 ^ n * cos θ))) +
      2 * (n + 1) * (2 * n + 1) * I n θ - 4 * (n + 1) * n * I (n - 1) θ := by
  rw [I]
  let f (x : ℝ) : ℝ := 1 - x ^ 2
  let u₁ (x : ℝ) : ℝ := f x ^ (n + 1)
  let u₁' (x : ℝ) : ℝ := - (2 * (n + 1) * x * f x ^ n)
  let v₁ (x : ℝ) : ℝ := sin (x * θ)
  let v₁' (x : ℝ) : ℝ := cos (x * θ) * θ
  let u₂ (x : ℝ) : ℝ := x * (f x) ^ n
  let u₂' (x : ℝ) : ℝ := (f x) ^ n - 2 * n * x ^ 2 * (f x) ^ (n - 1)
  let v₂ (x : ℝ) : ℝ := cos (x * θ)
  let v₂' (x : ℝ) : ℝ := -sin (x * θ) * θ
  have hfd : Continuous f := by fun_prop
  have hu₁d : Continuous u₁' := by fun_prop
  have hv₁d : Continuous v₁' := by fun_prop
  have hu₂d : Continuous u₂' := by fun_prop
  have hv₂d : Continuous v₂' := by fun_prop
  have hu₁_eval_one : u₁ 1 = 0 := by simp only [u₁, f]; simp
  have hu₁_eval_neg_one : u₁ (-1) = 0 := by simp only [u₁, f]; simp
  have t : u₂ 1 * v₂ 1 - u₂ (-1) * v₂ (-1) = 2 * (0 ^ n * cos θ) := by simp [u₂, v₂, f, ← two_mul]
  have hf (x) : HasDerivAt f (- 2 * x) x := by
    convert! (hasDerivAt_pow 2 x).const_sub 1 using 1
    simp
  have hu₁ (x) : HasDerivAt u₁ (u₁' x) x := by
    convert! (hf x).pow _ using 1
    simp only [Nat.add_succ_sub_one, u₁', Nat.cast_add_one]
    ring
  have hv₁ (x) : HasDerivAt v₁ (v₁' x) x := (hasDerivAt_mul_const θ).sin
  have hu₂ (x) : HasDerivAt u₂ (u₂' x) x := by
    convert! (hasDerivAt_id' x).fun_mul ((hf x).fun_pow _) using 1
    simp only [u₂']
    ring
  have hv₂ (x) : HasDerivAt v₂ (v₂' x) x := (hasDerivAt_mul_const θ).cos
  convert_to (∫ (x : ℝ) in (-1)..1, u₁ x * v₁' x) * θ = _ using 1
  · simp_rw [u₁, v₁', f, ← intervalIntegral.integral_mul_const, sq θ, mul_assoc]
  rw [integral_mul_deriv_eq_deriv_mul (fun x _ => hu₁ x) (fun x _ => hv₁ x)
    (hu₁d.intervalIntegrable _ _) (hv₁d.intervalIntegrable _ _), hu₁_eval_one, hu₁_eval_neg_one,
    zero_mul, zero_mul, sub_zero, zero_sub, ← integral_neg, ← integral_mul_const]
  convert_to ((-2 : ℝ) * (n + 1)) * ∫ (x : ℝ) in (-1)..1, (u₂ x * v₂' x) = _ using 1
  · rw [← integral_const_mul]
    congr 1 with x
    dsimp [u₁', v₁, u₂, v₂']
    ring
  rw [integral_mul_deriv_eq_deriv_mul (fun x _ => hu₂ x) (fun x _ => hv₂ x)
    (hu₂d.intervalIntegrable _ _) (hv₂d.intervalIntegrable _ _),
    mul_sub, t, neg_mul, neg_mul, neg_mul, sub_neg_eq_add]
  have (x : _) : u₂' x = (2 * n + 1) * f x ^ n - 2 * n * f x ^ (n - 1) := by
    cases n with
    | zero => simp [u₂']
    | succ n => ring!
  simp_rw [this, sub_mul, mul_assoc _ _ (v₂ _)]
  have : Continuous v₂ := by fun_prop
  rw [mul_mul_mul_comm, integral_sub, mul_sub, add_sub_assoc]
  · congr 1
    simp_rw [integral_const_mul]
    ring!
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

private lemma recursion (n : ℕ) :
    I (n + 2) θ * θ ^ 2 =
      2 * (n + 2) * (2 * n + 3) * I (n + 1) θ - 4 * (n + 2) * (n + 1) * I n θ := by
  rw [recursion' (n + 1)]
  push_cast
  ring

private lemma I_one : I 1 θ * θ ^ 3 = 4 * sin θ - 4 * θ * cos θ := by
  rw [_root_.pow_succ, ← mul_assoc, recursion' 0, sub_mul, add_mul, mul_assoc _ (I 0 θ), I_zero]
  ring

private lemma I_pos : 0 < I n (π / 2) := by
  refine integral_pos (by simp) (by fun_prop) ?_ ⟨0, by simp⟩
  refine fun x hx => mul_nonneg (pow_nonneg ?_ _) ?_
  · rw [sub_nonneg, sq_le_one_iff_abs_le_one, abs_le]
    exact ⟨hx.1.le, hx.2⟩
  refine cos_nonneg_of_neg_pi_div_two_le_of_le ?_ ?_ <;>
  nlinarith [hx.1, hx.2, pi_pos]

private lemma I_le (n : ℕ) : I n (π / 2) ≤ 2 := by
  rw [← norm_of_nonneg I_pos.le]
  refine (norm_integral_le_of_norm_le_const ?_).trans (show (1 : ℝ) * _ ≤ _ by norm_num)
  intro x hx
  simp only [uIoc_of_le, neg_le_self_iff, zero_le_one, mem_Ioc] at hx
  rw [norm_eq_abs, abs_mul, abs_pow]
  refine mul_le_one₀ (pow_le_one₀ (abs_nonneg _) ?_) (abs_nonneg _) (abs_cos_le_one _)
  rw [abs_le]
  constructor <;> nlinarith


private def ints (a b : ℕ) : ℕ → ℤ
  | 0 => 2
  | 1 => 4 * b
  | n+2 => 2 * (2 * n + 3 : ℤ) * b * ints a b (n+1) - 4 * a * b * ints a b n

private lemma integralInt (a b : ℕ) (hab : (π / 2)^2 * b = a) (n : ℕ) :
    (ints a b n : ℝ) * n.factorial = (π/2) * (a : ℝ)^n * I n (π/2) := by
  induction n using Nat.twoStepInduction with
  | zero =>
    have h := I_zero (θ := π/2)
    rw [sin_pi_div_two] at h
    simp [ints]; linarith
  | one =>
    have h := I_one (θ := π/2)
    rw [sin_pi_div_two, cos_pi_div_two] at h
    simp [ints]
    linear_combination -(b : ℝ) * h + (π/2) * I 1 (π/2) * hab
  | more n h₀ h₁ =>
    have hr := recursion (θ := π/2) n
    simp only [ints, Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_natCast,
      Int.cast_ofNat, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h₁ ⊢
    rw [pow_succ, pow_succ]
    linear_combination
      2 * (2*(n : ℝ)+3) * b * (n+2) * h₁ -
      4 * a * b * ((n : ℝ)+1) * (n+2) * h₀ -
      (π/2) * (a : ℝ)^n * a * b * hr +
      (π/2) * (a : ℝ)^n * a * I (n+2) (π/2) * hab

private lemma noInteger (m k : ℕ) (hm : 0 < m) : 2 * π^2 * m ≠ k := by
  intro heq
  have hk : 0 < (k : ℝ) := heq ▸ by positivity
  have hab : (π / 2)^2 * ((8*m : ℕ) : ℝ) = k := by push_cast; linarith only [heq]
  have hlim := (FloorSemiring.tendsto_pow_div_factorial_atTop (k : ℝ)).const_mul (π/2)
  have hz : Tendsto (fun n : ℕ => (π/2) * ((k : ℝ)^n / n.factorial)) atTop (nhds 0) := by
    simpa only [mul_zero] using hlim
  obtain ⟨n, hn⟩ := (hz.eventually_lt_const (by norm_num : (0 : ℝ)<1/2)).exists
  have hi := integralInt k (8*m) hab n
  have hf : 0 < (n.factorial : ℝ) := by positivity
  have hi' : (ints k (8*m) n : ℝ) =
      (π/2) * ((k : ℝ)^n / n.factorial) * I n (π/2) := by
    field_simp; linear_combination 2 * hi
  have hpos : 0 < (π/2) * ((k : ℝ)^n / n.factorial) := by positivity
  have hp : 0 < (ints k (8*m) n : ℝ) := hi' ▸ mul_pos hpos I_pos
  have hlt : (ints k (8*m) n : ℝ) < 1 := by
    rw [hi']
    nlinarith [mul_le_mul_of_nonneg_left (I_le n) hpos.le]
  norm_cast at hp hlt
  omega

private noncomputable def spacing : ℝ := 2 * π^2

private lemma spacingLarge : 1 < spacing := by
  unfold spacing
  nlinarith [Real.pi_gt_three, sq_nonneg (π-3)]

private lemma factored (k : ℕ) (a : ℝ) :
    sin a * (∑ j ∈ Finset.range (k+1), sin (2 * (j : ℝ) * a)) =
      sin (k*a) * sin ((k+1)*a) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    let u := ((k : ℝ)+1)*a
    have h₁ : (k : ℝ)*a = u-a := by dsimp [u]; ring
    have h₂ : ((k : ℝ)+1+1)*a = u+a := by dsimp [u]; ring
    have h₃ : 2*((k : ℝ)+1)*a = 2*u := by dsimp [u]; ring
    rw [h₁, h₂, h₃, sin_sub, sin_add, sin_two_mul]
    change _ = sin u * _
    ring

private lemma signed (x : ℝ) (m : ℕ) (hl : (m : ℝ) < x) (hu : x < (m : ℝ)+1) :
    ∃ b : ℝ, 0 < b ∧ sin (x*π) = (-1 : ℝ)^m * b := by
  refine ⟨sin ((x-m)*π), sin_pos_of_pos_of_lt_pi (mul_pos (sub_pos.2 hl) pi_pos) ?_, ?_⟩
  · nlinarith [mul_lt_mul_of_pos_right hu pi_pos]
  · rw [← sin_add_nat_mul_pi]; congr 1; ring

private noncomputable def slot (k : ℕ) : ℕ := ⌊(k : ℝ)/spacing⌋₊

private lemma slotUpper (k : ℕ) : (k : ℝ) / spacing < (slot k : ℝ)+1 :=
  Nat.lt_floor_add_one _

private lemma slotLower (k : ℕ) (hk : 0 < k) : (slot k : ℝ) < (k : ℝ)/spacing := by
  have hc : 0 < spacing := by linarith [spacingLarge]
  apply lt_of_le_of_ne (Nat.floor_le (div_nonneg (Nat.cast_nonneg _) hc.le))
  intro h
  change (slot k : ℝ) = (k : ℝ)/spacing at h
  by_cases hz : slot k = 0
  · rw [hz, Nat.cast_zero] at h
    exact (div_pos (show (0 : ℝ) < k by exact_mod_cast hk) hc).ne h
  · exact noInteger (slot k) k (Nat.pos_of_ne_zero hz)
      (by change spacing * _ = _; rw [h]; field_simp [hc.ne'])

private lemma slotStep (k : ℕ) : slot (k+1) = slot k ∨ slot (k+1) = slot k+1 := by
  have hc : 0 < spacing := by linarith [spacingLarge]
  have h₁ : slot k ≤ slot (k+1) := Nat.floor_mono (by push_cast; apply div_le_div_of_nonneg_right _ hc.le; linarith)
  have h₂ : slot (k+1) ≤ slot k+1 := by
    rw [slot, slot, ← Nat.floor_add_one (div_nonneg (Nat.cast_nonneg _) hc.le)]
    apply Nat.floor_mono
    push_cast
    rw [add_div]
    linarith [(div_le_one hc).2 spacingLarge.le]
  omega

open OMA.S_oeis_a079044

private lemma negIff (k : ℕ) (hk : 0 < k) : P k ↔ slot (k+1) ≠ slot k := by
  let a := 1/(2*π)
  have ha : 0 < sin a := by
    apply sin_pos_of_pos_of_lt_pi (by dsimp [a]; positivity)
    dsimp [a]; rw [div_lt_iff₀ (by positivity)]; nlinarith [Real.pi_gt_three, sq_nonneg (π-3)]
  have identity := factored k a
  have angle (j : ℕ) : 2 * (j : ℝ) * a = j / π := by dsimp [a]; ring
  simp_rw [angle] at identity
  have reangle (j : ℕ) : (j : ℝ) * a = ((j : ℝ)/spacing)*π := by
    dsimp [a, spacing]; field_simp
  obtain ⟨b,hb,eb⟩ := signed _ _ (slotLower k hk) (slotUpper k)
  obtain ⟨d,hd,ed⟩ := signed _ _ (slotLower (k+1) (by omega)) (slotUpper (k+1))
  have et : sin (((k : ℝ)+1)*a) = (-1 : ℝ)^slot (k+1)*d := by
    rw [← reangle (k+1)] at ed
    simpa only [Nat.cast_add_one] using ed
  rw [et, reangle, eb] at identity
  have ss : ((-1 : ℝ)^slot k) * ((-1 : ℝ)^slot k) = 1 := by rw [← mul_pow]; norm_num
  unfold P
  rcases slotStep k with he | he
  · rw [he] at identity ⊢
    simp only [ne_self_iff_false, iff_false, not_lt]
    have hp : 0 < sin a * ∑ j ∈ Finset.range (k+1), sin (j / π) := by
      rw [identity, mul_mul_mul_comm, ss, one_mul]; positivity
    exact (pos_of_mul_pos_right hp ha.le).le
  · rw [he, pow_succ] at identity
    have hp : sin a * ∑ j ∈ Finset.range (k+1), sin (j / π) < 0 := by
      rw [identity]
      calc _ = -(((-1 : ℝ)^slot k)*((-1 : ℝ)^slot k)) * (b*d) := by ring
        _ < 0 := by rw [ss]; nlinarith [mul_pos hb hd]
    exact iff_of_true (neg_of_mul_neg_right hp ha.le) (by omega)

private noncomputable def term (i : ℕ) : ℕ := ⌊spacing * (i+1)⌋₊

private lemma termIff (k : ℕ) : P k ↔ k ∈ Set.range term := by
  have hc : 0 < spacing := by linarith [spacingLarge]
  have bounds (i : ℕ) : term i = k ↔ (k : ℝ) ≤ spacing * (i+1) ∧ spacing * (i+1) < k+1 :=
    Nat.floor_eq_iff (by positivity)
  by_cases hk : k = 0
  · subst k
    have no : ¬ 0 ∈ Set.range term := by
      rintro ⟨i,hi⟩
      have ht := ((Nat.floor_eq_iff (by positivity : 0 ≤ spacing*((i : ℝ)+1))).1 hi).2
      push_cast at ht
      nlinarith [mul_nonneg hc.le (Nat.cast_nonneg i), spacingLarge]
    exact iff_of_false (by simp [P]) no
  rw [negIff k (Nat.pos_of_ne_zero hk)]
  constructor
  · intro hn
    have he := (slotStep k).resolve_left hn
    refine ⟨slot k, (bounds _).2 ⟨?_, ?_⟩⟩
    · simpa only [mul_comm spacing] using ((div_lt_iff₀ hc).1 (slotUpper k)).le
    · have h := (lt_div_iff₀ hc).1 (slotLower (k+1) (by omega))
      rw [he] at h
      simpa only [Nat.cast_add_one, mul_comm spacing] using h
  · rintro ⟨i,hi⟩ he
    obtain ⟨lo,up⟩ := (bounds i).1 hi
    have neq : spacing * ((i : ℝ)+1) ≠ k := by
      simpa only [spacing, Nat.cast_add_one] using noInteger (i+1) k (by omega)
    have h₁ : slot k < i+1 := by
      apply (Nat.floor_lt (div_nonneg (Nat.cast_nonneg _) hc.le)).2
      apply (div_lt_iff₀ hc).2
      simpa only [Nat.cast_add_one, mul_comm spacing] using lt_of_le_of_ne lo neq.symm
    have h₂ : i+1 ≤ slot (k+1) := by
      apply Nat.le_floor
      apply (le_div_iff₀ hc).2
      simpa only [Nat.cast_add_one, mul_comm spacing] using up.le
    omega

private lemma monoTerm : StrictMono term := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hc : 0 < spacing := by linarith [spacingLarge]
  change ⌊spacing * ((n : ℝ)+1)⌋₊ < ⌊spacing * ((n+1 : ℕ)+1)⌋₊
  rw [Nat.lt_iff_add_one_le, ← Nat.floor_add_one (by positivity)]
  apply Nat.floor_mono
  push_cast
  nlinarith [spacingLarge]

end SineIndex

open SineIndex OMA.S_oeis_a079044 in
theorem OMA.solution : type_of% @OMA.S_oeis_a079044.main := by
  intro n hn
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  have hr : Set.range term = Set.ofPred P := Set.ext fun k => (termIff k).symm
  have hinf : (Set.ofPred P).Infinite := hr ▸ Set.infinite_range_of_injective monoTerm.injective
  have ident := Nat.nth_comp_of_strictMono (p := P) (n := j) monoTerm
    (fun k h => (termIff k).mp h) (fun hf => (hinf hf).elim)
  rw [Nat.nth_of_forall (fun i _ => (termIff (term i)).mpr ⟨i,rfl⟩)] at ident
  simpa [term, spacing] using ident.symm
