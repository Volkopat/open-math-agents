import OMAStatements.S_oeis_a144837
import Mathlib

/-!
Credit: @ivillar
Proof: by Binet's formula, Lucas(5m) = f(Lucas(m)) for odd m, where f(x) = x^5 + 5x^3 + 5x
(Bala's recurrence in the OEIS entry), so a(n+1) = f(a(n)). All a(n) are 1 mod 5. If y is 1 mod 5
and x - y is divisible by 5^k (k ≥ 1), then f(x) - f(y) is divisible by 5^(k+2), because
f(y+d) - f(y) = 5d(y^4 + 3y^2 + 1) + O(d^2) and y^4 + 3y^2 + 1 is divisible by 5. Starting from
a(1) - a(0) = 10, induction gives 5^(2n+1) | a(n+1) - a(n), and n + r + 1 ≤ 2n + 1.
-/

namespace OMAA144837Helpers
open OMA.S_oeis_a144837 Real

theorem lucas_binet (n : ℕ) :
    (lucas n : ℝ) = goldenRatio ^ n + goldenConj ^ n ∧
      (lucas (n + 1) : ℝ) = goldenRatio ^ (n + 1) + goldenConj ^ (n + 1) := by
  induction n with
  | zero =>
    refine ⟨by norm_num [lucas], ?_⟩
    simp only [lucas, zero_add, pow_one]
    push_cast
    linarith [goldenRatio_add_goldenConj]
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have h : lucas (k + 1 + 1) = lucas (k + 1) + lucas k := rfl
    rw [h]
    push_cast
    rw [ih.1, ih.2]
    have e1 : goldenRatio ^ (k + 1 + 1) = goldenRatio ^ k * goldenRatio ^ 2 := by ring
    have e2 : goldenConj ^ (k + 1 + 1) = goldenConj ^ k * goldenConj ^ 2 := by ring
    rw [e1, e2, goldenRatio_sq, goldenConj_sq]
    ring

def f (x : ℤ) : ℤ := x ^ 5 + 5 * x ^ 3 + 5 * x

theorem lucas_five_mul (m : ℕ) (hm : Odd m) : lucas (5 * m) = f (lucas m) := by
  have h5 := (lucas_binet (5 * m)).1
  have h1 := (lucas_binet m).1
  have huv : goldenRatio ^ m * goldenConj ^ m = -1 := by
    rw [← mul_pow, goldenRatio_mul_goldenConj, hm.neg_one_pow]
  have key : (lucas (5 * m) : ℝ) = ((f (lucas m) : ℤ) : ℝ) := by
    rw [h5]
    unfold f
    push_cast
    rw [h1, pow_mul', pow_mul']
    set u := goldenRatio ^ m
    set v := goldenConj ^ m
    linear_combination (-(5 * (u ^ 3 + v ^ 3) + 5 * (u + v) * (2 * u * v + 1))) * huv
  exact_mod_cast key

theorem a_succ (n : ℕ) : a (n + 1) = f (a n) := by
  unfold a
  rw [pow_succ, mul_comm]
  exact lucas_five_mul (5 ^ n) (Odd.pow ⟨2, rfl⟩)

theorem a_one_mod (n : ℕ) : ∃ s : ℤ, a n = 5 * s + 1 := by
  induction n with
  | zero => exact ⟨0, by simp [a, lucas]⟩
  | succ k ih =>
    obtain ⟨s, hs⟩ := ih
    rw [a_succ, hs]
    exact ⟨625 * s ^ 5 + 625 * s ^ 4 + 375 * s ^ 3 + 125 * s ^ 2 + 25 * s + 2, by unfold f; ring⟩

theorem step (x y : ℤ) (j : ℕ) (hxy : (5 : ℤ) ^ (j + 1) ∣ x - y) (s : ℤ) (hy : y = 5 * s + 1) :
    (5 : ℤ) ^ (j + 3) ∣ f x - f y := by
  obtain ⟨t, ht⟩ := hxy
  have hx : x = y + 5 ^ (j + 1) * t := by linarith
  subst hx
  subst hy
  refine ⟨t * (125 * s ^ 4 + 100 * s ^ 3 + 45 * s ^ 2 + 10 * s + 1) +
    5 ^ j * t ^ 2 * (2 * (5 * s + 1) ^ 3 + 3 * (5 * s + 1)) +
    5 ^ (2 * j + 1) * t ^ 3 * (2 * (5 * s + 1) ^ 2 + 1) +
    5 ^ (3 * j + 2) * (5 * s + 1) * t ^ 4 + 5 ^ (4 * j + 2) * t ^ 5, ?_⟩
  unfold f
  ring

theorem gap (n : ℕ) : (5 : ℤ) ^ (2 * n + 1) ∣ a (n + 1) - a n := by
  induction n with
  | zero => exact ⟨2, by decide⟩
  | succ k ih =>
    obtain ⟨s', hs'⟩ := a_one_mod k
    have h := step (a (k + 1)) (a k) (2 * k) ih s' hs'
    have h2 : a (k + 1 + 1) - a (k + 1) = f (a (k + 1)) - f (a k) := by
      rw [a_succ (k + 1), a_succ k]
    rw [h2, show 2 * (k + 1) + 1 = 2 * k + 3 by ring]
    exact h

end OMAA144837Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a144837.main := by
  intro n r _ hr
  rw [Int.modEq_comm, Int.modEq_iff_dvd]
  exact (pow_dvd_pow (5 : ℤ) (by omega : n + r + 1 ≤ 2 * n + 1)).trans (OMAA144837Helpers.gap n)
