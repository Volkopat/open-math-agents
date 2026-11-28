import OMAStatements.S_oeis_a217976
import Mathlib

/-!
Proof. Write `f x = x * log x` and `D k = f (k + 1) - f k`. Each term `A217865 k = ⌊f (k + 1)⌋ - ⌊f k⌋` lies strictly
within `1` of `D k`. Since `f` is convex on `[0, ∞)`, `D` is monotone. If `A217865 i = n` and `A217865 j = n + 2`,
then `D i < n + 1 < D j`, so `j ≤ i` is impossible (it would give `D j ≤ D i`).
-/

namespace OMA.A217976Proof

/-- Midpoint convexity of `x * log x` at `x`, `x + 1`, `x + 2`, for `x ≥ 0`. -/
theorem mid (x : ℝ) (hx : 0 ≤ x) :
    2 * ((x + 1) * Real.log (x + 1)) ≤ x * Real.log x + (x + 2) * Real.log (x + 2) := by
  have hy : (0 : ℝ) ≤ x + 2 := by linarith
  have h := Real.convexOn_mul_log.2 (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr hy)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have e : (1 / 2 : ℝ) * x + 1 / 2 * (x + 2) = x + 1 := by ring
  have h2 : (1 / 2 * x + 1 / 2 * (x + 2)) * Real.log (1 / 2 * x + 1 / 2 * (x + 2)) ≤
      1 / 2 * (x * Real.log x) + 1 / 2 * ((x + 2) * Real.log (x + 2)) := by
    exact h
  rw [e] at h2
  linarith

/-- The real first difference `D k = (k + 1) * log (k + 1) - k * log k` is monotone in `k`. -/
theorem D_mono : Monotone (fun k : ℕ =>
    ((k + 1 : ℕ) : ℝ) * Real.log ((k + 1 : ℕ) : ℝ) - (k : ℝ) * Real.log (k : ℝ)) := by
  apply monotone_nat_of_le_succ
  intro k
  have h := mid (k : ℝ) (Nat.cast_nonneg k)
  have c1 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by
    push_cast; ring
  have c2 : ((k + 1 + 1 : ℕ) : ℝ) = (k : ℝ) + 2 := by
    push_cast; ring
  show ((k + 1 : ℕ) : ℝ) * Real.log ((k + 1 : ℕ) : ℝ) - (k : ℝ) * Real.log (k : ℝ) ≤
    ((k + 1 + 1 : ℕ) : ℝ) * Real.log ((k + 1 + 1 : ℕ) : ℝ) -
      ((k + 1 : ℕ) : ℝ) * Real.log ((k + 1 : ℕ) : ℝ)
  rw [c2, c1]
  linarith

/-- A difference of two floors lies strictly within `1` of the difference of the reals. -/
theorem floor_sub_bounds (a b : ℝ) :
    a - b - 1 < ((⌊a⌋ - ⌊b⌋ : ℤ) : ℝ) ∧ ((⌊a⌋ - ⌊b⌋ : ℤ) : ℝ) < a - b + 1 := by
  have h1 := Int.floor_le a
  have h2 := Int.lt_floor_add_one a
  have h3 := Int.floor_le b
  have h4 := Int.lt_floor_add_one b
  push_cast
  constructor <;> linarith

/-- The core statement: a difference equal to `m` occurs strictly before any difference equal to `m + 2`. -/
theorem key (m : ℤ) (i j : ℕ)
    (hi : ⌊((i + 1 : ℕ) : ℝ) * Real.log ((i + 1 : ℕ) : ℝ)⌋ - ⌊(i : ℝ) * Real.log (i : ℝ)⌋ = m)
    (hj : ⌊((j + 1 : ℕ) : ℝ) * Real.log ((j + 1 : ℕ) : ℝ)⌋ - ⌊(j : ℝ) * Real.log (j : ℝ)⌋ = m + 2) :
    i < j := by
  by_contra hji
  have hle : j ≤ i := by omega
  have hmono : ((j + 1 : ℕ) : ℝ) * Real.log ((j + 1 : ℕ) : ℝ) - (j : ℝ) * Real.log (j : ℝ) ≤
      ((i + 1 : ℕ) : ℝ) * Real.log ((i + 1 : ℕ) : ℝ) - (i : ℝ) * Real.log (i : ℝ) := D_mono hle
  obtain ⟨a1, a2⟩ := floor_sub_bounds (((i + 1 : ℕ) : ℝ) * Real.log ((i + 1 : ℕ) : ℝ))
    ((i : ℝ) * Real.log (i : ℝ))
  obtain ⟨b1, b2⟩ := floor_sub_bounds (((j + 1 : ℕ) : ℝ) * Real.log ((j + 1 : ℕ) : ℝ))
    ((j : ℝ) * Real.log (j : ℝ))
  rw [hi] at a1 a2
  rw [hj] at b1 b2
  have hm2 : ((m + 2 : ℤ) : ℝ) = (m : ℝ) + 2 := by
    push_cast; ring
  rw [hm2] at b1 b2
  linarith

end OMA.A217976Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a217976.main := by
  intro n i j _hi _hj hin hjn
  exact OMA.A217976Proof.key (n : ℤ) i j hin hjn
