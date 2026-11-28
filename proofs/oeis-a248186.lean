import OMAStatements.S_oeis_a248186
import Mathlib.Tactic

open OMA.S_oeis_a248186

namespace CubicTailProof

lemma telescopes (k : ℕ) : tail k = 1/(3*((k : ℝ)+1)*(k+2)*(k+3)) := by
  induction k with
  | zero => norm_num [tail]
  | succ k ih =>
    have hs : tail (k+1) = tail k - 1/(((k : ℝ)+1)*(k+2)*(k+3)*(k+4)) := by
      simp only [tail, Finset.sum_range_succ]
      ring
    rw [hs, ih]
    push_cast
    field_simp
    ring

lemma r_pos : 0 < r := Real.rpow_pos_of_pos (by norm_num) _

lemma r_cube : 3*r^3 = 1 := by
  have h : r^3 = (3 : ℝ)⁻¹ := by
    unfold r
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [h]
  norm_num

lemma threshold_cube (n : ℕ) (hn : 2 < n) :
    3*((threshold n)^3-threshold n) = (n : ℝ)^3 + 1/(3*(n : ℝ)^3) := by
  let x := r*(n : ℝ)
  have hx : 0 < x := mul_pos r_pos (by positivity)
  have hcube : 3*x^3 = (n : ℝ)^3 := by
    dsimp [x]
    rw [mul_pow, ← mul_assoc, r_cube, one_mul]
  have hs : threshold n = x + 1/(3*x) := by
    unfold threshold
    congr 1
    apply (div_eq_div_iff (by positivity) (by positivity)).mpr
    dsimp [x]
    linear_combination (n : ℝ) * r_cube
  have identity (z : ℝ) (hz : 0 < z) :
      3*((z+1/(3*z))^3-(z+1/(3*z))) = 3*z^3 + 1/(9*z^3) := by
    field_simp
    ring
  rw [hs, identity x hx, hcube, show 9*x^3 = 3*(n : ℝ)^3 by linarith only [hcube]]

lemma cutoff (n k : ℕ) (hn : 2 < n) :
    ⌊threshold n - 1⌋₊ ≤ k ↔ n^3 < 3*(k+1)*(k+2)*(k+3) := by
  let s := threshold n
  let w : ℝ := k+2
  let b := 3*(k+1)*(k+2)*(k+3)
  have hs : 0 ≤ s := by
    dsimp [s, threshold]
    have := r_pos
    positivity
  have hw : 2 ≤ w := by dsimp [w]; linarith [Nat.cast_nonneg (α := ℝ) k]
  have factor_pos : 0 < w^2+w*s+s^2-1 := by
    nlinarith [mul_nonneg (show 0 ≤ w by linarith) hs, sq_nonneg (w-2), sq_nonneg s]
  have fac : (b : ℝ) - 3*(s^3-s) = 3*(w-s)*(w^2+w*s+s^2-1) := by
    dsimp [b, w]
    push_cast
    ring
  have mono : s < w ↔ 3*(s^3-s) < (b : ℝ) := by
    constructor
    · intro h
      linarith only [fac, mul_pos (show 0 < 3*(w-s) by linarith) factor_pos]
    · intro h
      by_contra! hnw
      linarith only [fac, h, mul_nonpos_of_nonpos_of_nonneg
        (show 3*(w-s) ≤ 0 by linarith) factor_pos.le]
  have err : 0 < 1/(3*(n : ℝ)^3) := by positivity
  have err_lt : 1/(3*(n : ℝ)^3) < 1 := by
    apply (div_lt_iff₀ (by positivity)).mpr
    have hp : (1 : ℝ) ≤ (n : ℝ)^3 := one_le_pow₀ (by exact_mod_cast (show 1 ≤ n by omega))
    linarith
  have hf : ⌊threshold n - 1⌋₊ ≤ k ↔ s < w := by
    rw [← Nat.lt_succ_iff, Nat.floor_lt' (Nat.succ_ne_zero k), Nat.cast_succ]
    dsimp [s, w]
    constructor <;> intro h <;> linarith
  rw [hf, mono]
  change 3*((threshold n)^3-threshold n) < (b : ℝ) ↔ n^3 < b
  rw [threshold_cube n hn]
  constructor
  · intro h
    exact_mod_cast (show (n : ℝ)^3 < (b : ℝ) by linarith)
  · intro h
    have hb : (n : ℝ)^3+1 ≤ (b : ℝ) := by exact_mod_cast (show n^3+1 ≤ b by omega)
    linarith

lemma good (n k : ℕ) (hn : 2<n) :
    tail k < 1/(n : ℝ)^3 ↔ n^3 < 3*(k+1)*(k+2)*(k+3) := by
  rw [telescopes, div_lt_div_iff₀ (by positivity) (by positivity)]
  simp only [one_mul]
  norm_cast

end CubicTailProof

open CubicTailProof

theorem OMA.solution : type_of% @OMA.S_oeis_a248186.main := by
  intro n hn
  have hp : 0 < ⌊threshold n - 1⌋₊ := by
    by_contra! hz
    have h := (cutoff n 0 hn).mp hz
    have h3 := Nat.pow_le_pow_left (show 3 ≤ n by omega) 3
    omega
  exact ⟨⟨hp, (good n _ hn).mpr ((cutoff n _ hn).mp le_rfl)⟩,
    fun k hk => (cutoff n k hn).mpr ((good n k hn).mp hk.2)⟩
