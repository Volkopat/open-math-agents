import OMAStatements.S_oeis_a308733
import Mathlib

namespace OMA.S_oeis_a308733

section

open Finset

/-- Number of the same partitions when every partition has unit weight. -/
def unweighted (m : ℕ) : ℤ :=
  ∑ p ∈ range (m / 4 + 1), triples (m - 4 * p)

theorem pairs_eq (n : ℕ) : pairs n = 1 + (if 2 ≤ n then pairs (n-2) else 0) := by
  unfold pairs
  split_ifs <;> omega

private theorem triples_add (n : ℕ) : triples (n+3) = pairs (n+3) + triples n := by
  unfold triples
  rw [show (n+3)/3+1 = (n/3+1)+1 by omega, sum_range_succ']
  simp only [Nat.mul_zero, Nat.sub_zero, Nat.mul_succ, Nat.add_sub_add_right]
  rw [add_comm]

theorem triples_eq (n : ℕ) : triples n = pairs n + (if 3 ≤ n then triples (n-3) else 0) := by
  by_cases hn : 3 ≤ n
  · simpa [hn] using triples_add (n-3)
  · simp [triples, if_neg hn, Nat.div_eq_of_lt (by omega : n < 3)]

private theorem unweighted_add (n : ℕ) : unweighted (n+4) = triples (n+4) + unweighted n := by
  unfold unweighted
  rw [show (n+4)/4+1 = (n/4+1)+1 by omega, sum_range_succ']
  simp only [Nat.mul_zero, Nat.sub_zero, Nat.mul_succ, Nat.add_sub_add_right]
  rw [add_comm]

theorem unweighted_eq (n : ℕ) :
    unweighted n = triples n + (if 4 ≤ n then unweighted (n-4) else 0) := by
  by_cases hn : 4 ≤ n
  · simpa [hn] using unweighted_add (n-4)
  · simp [unweighted, if_neg hn, Nat.div_eq_of_lt (by omega : n < 4)]

private theorem weight_add (n : ℕ) : weight (n+4) = unweighted (n+4) + weight n := by
  rw [unweighted_add]
  unfold weight unweighted
  rw [show (n+4)/4+1 = (n/4+1)+1 by omega, sum_range_succ']
  simp only [Nat.mul_zero, Nat.sub_zero, Nat.mul_succ, Nat.add_sub_add_right,
    Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, one_mul]
  simp_rw [add_mul, one_mul]
  rw [sum_add_distrib]
  ring

theorem weight_eq (n : ℕ) : weight n = unweighted n + (if 4 ≤ n then weight (n-4) else 0) := by
  by_cases hn : 4 ≤ n
  · simpa [hn] using weight_add (n-4)
  · simp [weight, unweighted, if_neg hn, Nat.div_eq_of_lt (by omega : n < 4)]


end

open PowerSeries

private theorem removeLag (d : ℕ) (f g : ℕ → ℤ)
    (h : ∀ n, f n = g n + (if d ≤ n then f (n-d) else 0)) :
    mk f * (1-X^d) = mk g := by
  rw [mul_sub, mul_one]
  ext n
  simp only [map_sub, coeff_mk, coeff_mul_X_pow']
  rw [h n]
  abel

private theorem ones : mk (fun _ => (1:ℤ)) * (1-X) = 1 := by
  rw [mul_sub, mul_one, ← pow_one (X : ℤ⟦X⟧)]
  ext n
  cases n <;> simp

theorem partition_series :
    (let x := (PowerSeries.X : PowerSeries ℤ)
     ((1-x)^5*(1+x)^3*(1+x^2)^2*(1+x+x^2))*PowerSeries.mk a = x^4) := by
  dsimp only
  have shift : mk a = mk weight * X^4 := by
    ext n
    simp [a, coeff_mul_X_pow']
  have h₂ := removeLag 2 pairs (fun _ => 1) pairs_eq
  have h₃ := removeLag 3 triples pairs triples_eq
  have h₄ := removeLag 4 unweighted triples unweighted_eq
  have hw := removeLag 4 weight unweighted weight_eq
  calc
    _ = (((((mk weight * (1-X^4)) * (1-X^4)) * (1-X^3)) * (1-X^2)) * (1-X)) * X^4 := by
      rw [shift]
      ring
    _ = _ := by rw [hw,h₄,h₃,h₂,ones,one_mul]

open PowerSeries in
theorem recurrence_of_series
    (h : ((1-X)^5*(1+X)^3*(1+X^2)^2*(1+X+X^2)) * mk a = X^4) :
    ∀ n : ℕ, 13 < n →
      a n = a (n-1) + a (n-2) + a (n-4) - 3*a (n-5) - a (n-6) + a (n-8)
        + 3*a (n-9) - a (n-10) - a (n-12) - a (n-13) + a (n-14) := by
  intro n hn
  let A := mk a
  change _ * A = X^4 at h
  rw [show ((1-X)^5*(1+X)^3*(1+X^2)^2*(1+X+X^2)) * A =
      A - A*X^1 - A*X^2 - A*X^4 + C 3*(A*X^5) + A*X^6 - A*X^8
        - C 3*(A*X^9) + A*X^10 + A*X^12 + A*X^13 - A*X^14 by
        simp only [map_ofNat]; ring] at h
  have hc := congrArg (coeff (R := ℤ) n) h
  simp (disch := omega) only [map_add, map_sub, coeff_C_mul, coeff_X_pow, coeff_mul_X_pow',
    A, coeff_mk, if_pos, if_neg] at hc
  linarith

end OMA.S_oeis_a308733

open OMA.S_oeis_a308733 in
theorem OMA.solution : type_of% @OMA.S_oeis_a308733.main :=
  ⟨partition_series, recurrence_of_series partition_series⟩
