import OMAStatements.S_mo_145807
import Mathlib

namespace DyadicDerivative

open Polynomial

noncomputable def a : ℝ[X] := C (1 / 2 : ℝ) * (X + 1)
noncomputable def b : ℝ[X] := C (1 / 2 : ℝ) * (X - 1)

noncomputable def advance (t : ℝ) (z : ℝ[X] × ℝ[X]) : ℝ[X] × ℝ[X] :=
  let r := z.1 ^ 2 - z.2 ^ 2
  let s := 2 * z.1 * z.2
  (a * (a * r - C t * b * s), a * (a * s + C t * b * r))

noncomputable def pair : ℕ → ℝ[X] × ℝ[X]
  | 0 => (1, 0)
  | n + 1 => advance ((2 : ℝ) ^ n) (pair n)

lemma at_one (n : ℕ) : (pair n).1.eval 1 = 1 ∧ (pair n).2.eval 1 = 0 := by
  induction n with
  | zero => simp [pair]
  | succ n ih => norm_num [pair, advance, a, b, ih.1, ih.2]

lemma slope (n : ℕ) : (pair n).2.derivative.eval 1 = n * (2 : ℝ) ^ n / 4 := by
  induction n with
  | zero => simp [pair]
  | succ n ih =>
    simp [pair, advance, derivative_mul, a, b, (at_one n).1, (at_one n).2, ih,
      pow_succ]
    ring

lemma kernel_bound (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    u^2 * (u^2 + v^2) * (u+2*v)^4 ≤ (u+v)^8 := by
  have h : 0 ≤ 3*u^6*v^2 + 16*u^5*v^3 + 30*u^4*v^4 + 24*u^3*v^5 +
      12*u^2*v^6 + 8*u*v^7 + v^8 := by positivity
  linarith only [h]

noncomputable def energy (x : ℝ) (z : ℝ[X] × ℝ[X]) : ℝ := (z.1.eval x)^2 + (z.2.eval x)^2

lemma energy_advance (x t : ℝ) (z : ℝ[X] × ℝ[X]) :
    energy x (advance t z) = (energy x z)^2 * |a.eval x|^2 *
      (|a.eval x|^2 + (t * |b.eval x|)^2) := by
  simp [energy, advance, mul_pow, sq_abs]
  ring

lemma bound (x : ℝ) (n : ℕ) :
    energy x (pair n) * (|a.eval x| + 2^n * |b.eval x|)^4 ≤
      (|a.eval x| + |b.eval x|)^(4 * 2^n) := by
  induction n with
  | zero => simp [energy, pair]
  | succ n ih =>
    let u := |a.eval x|
    let v := (2 : ℝ)^n * |b.eval x|
    have hu : 0 ≤ u := abs_nonneg _
    have hv : 0 ≤ v := by dsimp [v]; positivity
    have he : 0 ≤ energy x (pair n) := by unfold energy; positivity
    have hsq := pow_le_pow_left₀ (show 0 ≤ energy x (pair n) * (u+v)^4 by positivity) ih 2
    rw [pair, energy_advance]
    calc
      _ = (energy x (pair n))^2 * (u^2 * (u^2 + v^2) * (u+2*v)^4) := by
        dsimp [u,v]; rw [pow_succ]; ring
      _ ≤ (energy x (pair n))^2 * (u+v)^8 :=
        mul_le_mul_of_nonneg_left (kernel_bound u v hu hv) (sq_nonneg _)
      _ = (energy x (pair n) * (u+v)^4)^2 := by ring
      _ ≤ _ := by
        rw [show 4 * 2^(n+1) = (4 * 2^n) * 2 by ring, pow_mul]
        exact hsq

lemma abs_sum (x : ℝ) : |a.eval x| + |b.eval x| = max 1 |x| := by
  simp [a,b]
  rcases le_total x (-1) with h|h
  · rw [abs_of_nonpos (by linarith : x ≤ 0), max_eq_right (by linarith)]
    rw [abs_of_nonpos (by linarith : x+1 ≤ 0), abs_of_nonpos (by linarith : x-1 ≤ 0)]
    ring
  · rcases le_total x 1 with h'|h'
    · rw [max_eq_left (abs_le.mpr ⟨by linarith, h'⟩),
        abs_of_nonneg (by linarith : 0 ≤ x+1), abs_of_nonpos (by linarith : x-1 ≤ 0)]
      ring
    · rw [abs_of_nonneg (by linarith : 0 ≤ x), max_eq_right h',
        abs_of_nonneg (by linarith : 0 ≤ x+1), abs_of_nonneg (by linarith : 0 ≤ x-1)]
      ring

noncomputable def witness (n : ℕ) := a^2 * (pair n).2

lemma envelope (n : ℕ) (x : ℝ) :
    |(witness n).eval x| ≤ max 1 (|x|^(2*2^n)) := by
  have h := bound x n
  rw [abs_sum] at h
  have hu := abs_nonneg (a.eval x)
  have hz := sq_nonneg ((pair n).2.eval x)
  have h1 : |a.eval x|^4 ≤ (|a.eval x| + (2 : ℝ)^n * |b.eval x|)^4 := by
    apply pow_le_pow_left₀ hu
    exact le_add_of_nonneg_right (by positivity)
  have h2 : ((pair n).2.eval x)^2 ≤ energy x (pair n) :=
    le_add_of_nonneg_left (sq_nonneg _)
  have h3 := (mul_le_mul h2 h1 (by positivity) (by unfold energy; positivity)).trans h
  have h4 : |(witness n).eval x| ^ 2 ≤ ((max 1 |x|)^(2*2^n))^2 := by
    calc
      _ = ((pair n).2.eval x)^2 * |a.eval x|^4 := by
        rw [sq_abs, witness, eval_mul, eval_pow,
          show |a.eval x|^4 = (a.eval x)^4 by
            rw [show (4:ℕ) = 2*2 by decide, pow_mul, sq_abs, ← pow_mul]]
        ring
      _ ≤ _ := h3
      _ = _ := by rw [← pow_mul]; congr 1 <;> ring
  have h5 : |(witness n).eval x| ≤ (max 1 |x|)^(2*2^n) := by
    have hn : 0 ≤ (max 1 |x|)^(2*2^n) := by positivity
    nlinarith
  rcases le_total |x| 1 with hx|hx
  · rw [max_eq_left hx, one_pow] at h5
    exact h5.trans (le_max_left _ _)
  · rw [max_eq_right hx] at h5
    exact h5.trans (le_max_right _ _)

lemma witness_slope (n : ℕ) : (witness n).derivative.eval 1 = n * (2 : ℝ)^n / 4 := by
  norm_num [witness, derivative_mul, slope, (at_one n).2, a]

end DyadicDerivative

open DyadicDerivative in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_145807.main) := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (8 * C)
  have h := hC (2 * 2^n) (witness n) (envelope n)
  rw [witness_slope, abs_of_nonneg (by positivity)] at h
  push_cast at h
  have hp : (0 : ℝ) < 2^n := by positivity
  nlinarith only [h, mul_pos (sub_pos.mpr hn) hp]
