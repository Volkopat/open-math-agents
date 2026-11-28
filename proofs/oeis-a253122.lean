import OMAStatements.S_oeis_a253122
import Mathlib

namespace OMA.S_oeis_a253122

/-- At an even stage the two starting bits do not affect the count. The difference
between the even- and odd-parity counts doubles after every two further bits. -/
private theorem twice_even (k : ℕ) (x y odd : Bool) :
    2 * (completions (2*k) x y odd : ℤ) =
      4^k + (if odd then -1 else 1) * 2^k := by
  induction k generalizing x y odd with
  | zero => cases odd <;> simp [completions]
  | succ k ih =>
    cases x <;> cases y <;> cases odd <;>
      simp [completions, median, mul_add, ih, pow_succ] <;> ring

theorem closed_even (n : ℕ) (hn : 0 < n) (h : n % 2 = 0) :
    a n = 2 ^ (n / 2 + 1) + 2 ^ (n + 1) := by
  let k := n / 2
  have hk : n = 2*k := by dsimp [k]; omega
  rw [a, if_neg (Nat.ne_of_gt hn), countedWords]
  zify
  rw [show n/2 = k from rfl, hk]
  apply (mul_right_inj' (show (2 : ℤ) ≠ 0 by decide)).mp
  simp [mul_add, twice_even, pow_succ, pow_mul]
  ring

theorem closed_odd (n : ℕ) (hn : 0 < n) (h : n % 2 = 1) :
    a n = 2 ^ (n + 1) := by
  let k := n / 2
  have hk : n = 2*k+1 := by dsimp [k]; omega
  rw [a, if_neg (Nat.ne_of_gt hn), countedWords, hk]
  zify
  simp only [completions, median, Bool.false_and, Bool.true_and, Bool.false_or,
    Bool.true_or, Bool.false_xor, Nat.cast_add]
  apply (mul_right_inj' (show (2 : ℤ) ≠ 0 by decide)).mp
  simp [mul_add, twice_even, pow_succ, pow_mul]
  ring


open PowerSeries

private theorem twoStep (k : ℕ) (hk : 0 < k) : (a (k+2) : ℤ) - 2*a k = 2^(k+2) := by
  by_cases he : k%2=0
  · rw [closed_even (k+2) (by omega) (by omega), closed_even k hk he,
      show (k+2)/2+1 = k/2+1+1 by omega]
    push_cast
    simp only [pow_succ]
    ring
  · rw [closed_odd (k+2) (by omega) (by omega), closed_odd k hk (by omega)]
    push_cast
    simp only [pow_succ]
    ring

theorem wordSeries :
    (1-2*X)*(1-2*X^2)*mk (fun n => (a n:ℤ)) = 4*X*(1+X-4*X^2) := by
  let A : ℤ⟦X⟧ := mk fun n => (a n : ℤ)
  change _ * A = _
  have lhs : (1-2*X)*(1-2*X^2)*A = A - (A*X^1+A*X^1) -
      (A*X^2+A*X^2) + (A*X^3+A*X^3+A*X^3+A*X^3) := by ring
  have rhs : 4*(X : ℤ⟦X⟧)*(1+X-4*X^2) = C (4:ℤ)*X^1+C (4:ℤ)*X^2-C (16:ℤ)*X^3 := by
    simp only [map_ofNat]
    ring
  rw [lhs,rhs]
  ext n
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_mul_X_pow', A, coeff_mk]
  by_cases small : n ≤ 3
  · interval_cases n <;> decide
  · obtain ⟨k,rfl⟩ : ∃ k : ℕ, n = k+4 := ⟨n-4, by omega⟩
    have h := twoStep (k+2) (by omega)
    have h' := twoStep (k+1) (by omega)
    simp only [show k+4-1=k+3 by omega,
      show k+4-2=k+2 by omega, show k+4-3=k+1 by omega,
      show 1≤k+4 by omega, show 2≤k+4 by omega, show 3≤k+4 by omega,
      show k+4≠1 by omega, show k+4≠2 by omega, show k+4≠3 by omega, if_true,if_false]
    simp only [pow_succ] at h h'
    linarith

end OMA.S_oeis_a253122

open OMA.S_oeis_a253122 in
theorem OMA.solution : type_of% @OMA.S_oeis_a253122.main :=
  ⟨wordSeries, closed_even, closed_odd⟩
