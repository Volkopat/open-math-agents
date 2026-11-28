import OMAStatements.S_oeis_a277929

open OMA.S_oeis_a277929
open PowerSeries

namespace RuleFive

private theorem coord (x : ℤ) : x = -1 ∨ x = 0 ∨ x = 1 ∨
    (x ≠ 0 ∧ x + 1 ≠ 0 ∧ x - 1 ≠ 0) := by omega

private theorem first (p : ℤ × ℤ) : state 1 p = if p = (0, 0) then false else true := by
  rcases p with ⟨x, y⟩
  rcases coord x with rfl | rfl | rfl | ⟨hx, hxp, hxm⟩ <;>
    rcases coord y with rfl | rfl | rfl | ⟨hy, hyp, hym⟩ <;>
    norm_num [state, nbrs, rule, List.countP_cons, Prod.mk.injEq, *] <;> rfl

private theorem uniform_succ (t : ℕ) (b : Bool) (h : ∀ p, state t p = b)
    (p : ℤ × ℤ) : state (t + 1) p = !b := by
  rw [state]
  simp only [h]
  cases b <;> norm_num [nbrs, List.countP_cons, rule] <;> decide

private theorem second (p : ℤ × ℤ) : state 2 p = false := by
  by_cases h : p = (0, 0)
  · subst p; decide
  · rw [state, first, if_neg h]
    have bound := List.countP_le_length (p := fun q => state 1 q) (l := nbrs p)
    change _ ≤ 4 at bound
    generalize (nbrs p).countP (fun q => state 1 q) = k at *
    interval_cases k <;> decide

private theorem ticks (k : ℕ) :
    (∀ p, state (2*k+2) p = false) ∧ ∀ p, state (2*k+3) p = true := by
  induction k with
  | zero => exact ⟨second, uniform_succ 2 false second⟩
  | succ k ih =>
    have off := uniform_succ (2*k+3) true ih.2
    have on' := uniform_succ (2*k+3+1) false off
    rw [show 2*(k+1)+2 = 2*k+3+1 by omega, show 2*(k+1)+3 = 2*k+3+1+1 by omega]
    exact ⟨by simpa using off, by simpa using on'⟩

private theorem geometric (n : ℕ) : (∑ k ∈ Finset.range (n+1), 2^(n-k)) + 1 = 2^(n+1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h : (∑ k ∈ Finset.range (n+1), 2^(n+1-k)) = 2 * ∑ k ∈ Finset.range (n+1), 2^(n-k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have := Finset.mem_range.mp hk
      rw [show n+1-k = (n-k)+1 by omega, pow_succ, Nat.mul_comm]
    rw [h, Nat.sub_self, pow_zero, pow_succ _ (n+1)]
    omega

private theorem even_value (n : ℕ) (hn : 1 < n) (he : Even n) : a n = 0 := by
  obtain ⟨k, h⟩ := he
  obtain ⟨d, rfl⟩ : ∃ d, n = 2*d+2 := ⟨k-1, by omega⟩
  simp [a, (ticks d).1]

private theorem odd_value (n : ℕ) (hn : 1 < n) (ho : Odd n) : a n + 1 = 2^(n+1) := by
  obtain ⟨k, h⟩ := ho
  obtain ⟨d, rfl⟩ : ∃ d, n = 2*d+3 := ⟨k-1, by omega⟩
  simpa [a, (ticks d).2] using geometric (2*d+3)


private theorem odd_formula (n : ℕ) (hn : 1 < n) (ho : Odd n) :
    (a n : ℚ) = 2^n - 1 - (-2)^n := by
  have h : (a n : ℚ) + 1 = 2^(n+1) := by exact_mod_cast odd_value n hn ho
  rw [ho.neg_pow]
  rw [pow_succ] at h
  linarith

private theorem rec' (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 5 * a (n-2) - 4 * a (n-4) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k+4 := ⟨n-4, by omega⟩
  rw [show k+4-2 = k+2 by omega, show k+4-4 = k by omega]
  rcases Nat.even_or_odd k with ⟨d, hd⟩ | ⟨d, hd⟩
  · rw [even_value k (by omega) ⟨d, hd⟩,
      even_value (k+2) (by omega) ⟨d+1, by omega⟩,
      even_value (k+4) (by omega) ⟨d+2, by omega⟩]
    norm_num
  · have h0 : (a k : ℤ) + 1 = 2^(k+1) := by exact_mod_cast odd_value k (by omega) ⟨d, hd⟩
    have h2 : (a (k+2) : ℤ) + 1 = 2^(k+2+1) := by exact_mod_cast odd_value (k+2) (by omega) ⟨d+1, by omega⟩
    have h4 : (a (k+4) : ℤ) + 1 = 2^(k+4+1) := by exact_mod_cast odd_value (k+4) (by omega) ⟨d+2, by omega⟩
    norm_num [pow_succ] at h0 h2 h4
    linarith

private theorem gen : A = (1 + X - 5 * X ^ 2 + 10 * X ^ 3 + 4 * X ^ 4 - 8 * X ^ 5) *
      ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X))⁻¹ := by
  let D : PowerSeries ℚ := (1-X)*(1+X)*(1-2*X)*(1+2*X)
  have hd : constantCoeff D ≠ 0 := by simp [D]
  have h : A * D = 1 + X - 5*X^2 + 10*X^3 + 4*X^4 - 8*X^5 := by
    rw [show A * D = A - C 5 * (A * X^2) + C 4 * (A * X^4) by simp only [D, map_ofNat]; ring]
    have reshape : 1 + X - 5*X^2 + 10*X^3 + 4*X^4 - 8*X^5 =
        (1 : PowerSeries ℚ) + X^1 - C 5 * X^2 + C 10 * X^3 + C 4 * X^4 - C 8 * X^5 := by
      simp only [map_ofNat]; ring
    rw [reshape]
    ext n
    simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_one, coeff_X_pow, A, coeff_mk]
    rcases Nat.lt_or_ge n 6 with small | large
    · have h0 : a 0 = 1 := by decide
      have h1 : a 1 = 1 := by decide
      have h2 : a 2 = 0 := even_value _ (by decide) (by decide)
      have h3 : a 3 = 15 := by have := odd_value 3 (by decide) (by decide); omega
      have h4 : a 4 = 0 := even_value _ (by decide) (by decide)
      have h5 : a 5 = 63 := by have := odd_value 5 (by decide) (by decide); omega
      interval_cases n <;> norm_num [h0,h1,h2,h3,h4,h5]
    · simp only [if_pos (show 2 ≤ n by omega), if_pos (show 4 ≤ n by omega),
        show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega,
        show n ≠ 4 by omega, show n ≠ 5 by omega, if_false]
      have hr : (a n : ℚ) = 5 * a (n-2) - 4 * a (n-4) := by exact_mod_cast rec' n (by omega)
      simp only [coeff_C, if_pos (show 3 ≤ n by omega), if_pos (show 5 ≤ n by omega),
        if_neg (show n-2 ≠ 0 by omega), if_neg (show n-3 ≠ 0 by omega),
        if_neg (show n-4 ≠ 0 by omega), if_neg (show n-5 ≠ 0 by omega)]
      linarith
  change A = _ * D⁻¹
  rw [← h, mul_assoc, PowerSeries.mul_inv_cancel _ hd, mul_one]

end RuleFive

theorem OMA.solution : type_of% @OMA.S_oeis_a277929.main :=
  ⟨fun n hn he => by simp [RuleFive.even_value n hn he],
    RuleFive.odd_formula, RuleFive.rec', RuleFive.gen⟩
