import OMAStatements.S_oeis_a128424
import Mathlib

namespace OMA.S_oeis_a128424

/-- Candidate values of a(n+4)-1. -/
def b : ℕ → ℕ
  | 0 => 4
  | 1 => 6
  | 2 => 9
  | n + 3 => b (n+2) + b n

private def error (n : ℕ) : ℤ :=
  (b n : ℤ)^2 + (b (n+1) : ℤ)^2 + (b n : ℤ) * b (n+1) - (b (n+2) : ℤ)^2

private def lowerMargin (n : ℕ) : ℤ :=
  3 * ((b n : ℤ) + b (n+1)) - 2 * b (n+2)

private def upperMargin (n : ℕ) : ℤ :=
  4 * (b (n+2) : ℤ) - 3 * ((b n : ℤ) + b (n+1))

private theorem error_rec (n : ℕ) : error (n+3) = error n - error (n+1) := by
  simp only [error, Nat.add_assoc, Nat.reduceAdd, b, Nat.cast_add]
  ring

private theorem lower_rec (n : ℕ) : lowerMargin (n+3) = lowerMargin (n+2) + lowerMargin n := by
  simp only [lowerMargin, Nat.add_assoc, b, Nat.cast_add]
  ring

private theorem upper_rec (n : ℕ) : upperMargin (n+3) = upperMargin (n+2) + upperMargin n := by
  simp only [upperMargin, Nat.add_assoc, b, Nat.cast_add]
  ring

private def Window (X : ℕ → ℤ) (n : ℕ) : Prop :=
  0 ≤ X n ∧ X n ≤ X (n+1) ∧ X (n+1) ≤ X (n+2) ∧
  -X n ≤ error n ∧ error n ≤ X n ∧
  -X (n+1) ≤ error (n+1) ∧ error (n+1) ≤ X (n+1) ∧
  -X (n+2) ≤ error (n+2) ∧ error (n+2) ≤ X (n+2)

/-- A positive increasing margin grows fast enough to absorb the two errors in error_rec. -/
private theorem bound_error (X : ℕ → ℤ) (hX : ∀ n, X (n+3) = X (n+2) + X n)
    (h0 : Window X 0) (n : ℕ) : -X n ≤ error n ∧ error n ≤ X n := by
  have h (j : ℕ) : Window X j := by
    induction j with
    | zero => exact h0
    | succ j hj =>
      rcases hj with ⟨h₀,h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈⟩
      have hx := hX j
      have he := error_rec j
      simp only [Window, Nat.add_assoc, Nat.reduceAdd]
      exact ⟨by omega, h₂, by omega, h₅, h₆, h₇, h₈, by omega, by omega⟩
  exact ⟨(h n).2.2.2.1, (h n).2.2.2.2.1⟩

/-- The two margins place the radicand between consecutive squares. -/
theorem sqrt_bounds (n : ℕ) :
    (b (n+2)+1)^2 ≤ (b n+1)^2 + (b (n+1)+1)^2 + (b (n+1)+1)*(b n+1) ∧
    (b n+1)^2 + (b (n+1)+1)^2 + (b (n+1)+1)*(b n+1) < (b (n+2)+2)^2 := by
  have hl := (bound_error lowerMargin lower_rec (by unfold Window; decide +kernel) n).1
  have hu := (bound_error upperMargin upper_rec (by unfold Window; decide +kernel) n).2
  unfold lowerMargin error at hl
  unfold upperMargin error at hu
  zify
  constructor <;> nlinarith

/-- The integer bounds identify every term of the original floor-square-root sequence. -/
theorem a_eq_b : ∀ n : ℕ, a (n+4) = b n + 1
  | 0 => by decide +kernel
  | 1 => by decide +kernel
  | n+2 => by
    change Nat.sqrt (a ((n+1)+4)^2 + a (n+4)^2 + a ((n+1)+4) * a (n+4)) = b (n+2) + 1
    rw [a_eq_b (n+1), a_eq_b n, add_comm ((b (n+1)+1)^2) ((b n+1)^2)]
    obtain ⟨hl, hu⟩ := sqrt_bounds n
    have hl' := Nat.le_sqrt'.mpr hl
    have hu' := Nat.sqrt_lt'.mpr hu
    omega


open PowerSeries

private theorem linear_recurrence (n : ℕ) (h : 7 < n) :
    (a n : ℤ) = 2*a (n-1)-a (n-2)+a (n-3)-a (n-4) := by
  obtain ⟨k,rfl⟩ : ∃ k : ℕ, n=k+8 := ⟨n-8, by omega⟩
  change (a ((k+4)+4) : ℤ) = 2*a ((k+3)+4) - a ((k+2)+4) + a ((k+1)+4) - a (k+4)
  simp only [a_eq_b, Nat.cast_add, Nat.cast_one]
  rw [show b (k+4)=b (k+3)+b (k+1) by rfl, show b (k+3)=b (k+2)+b k by rfl]
  push_cast
  ring

private theorem gf :
    (1-X)*(1-X-X^3)*mk (fun n => (a n : ℤ)) =
      X*(1+X-2*X^2+X^3-2*X^4+X^5-X^6) := by
  let A : ℤ⟦X⟧ := mk fun n => (a n : ℤ)
  change _ * A = _
  have den : (1-X)*(1-X-X^3)*A = A-(A*X^1+A*X^1)+A*X^2-A*X^3+A*X^4 := by ring
  have num : (X : ℤ⟦X⟧)*(1+X-2*X^2+X^3-2*X^4+X^5-X^6) =
      C (1:ℤ)*X^1+C (1:ℤ)*X^2-C (2:ℤ)*X^3+C (1:ℤ)*X^4-C (2:ℤ)*X^5+
      C (1:ℤ)*X^6-C (1:ℤ)*X^7 := by simp only [map_ofNat,map_one]; ring
  rw [den,num]
  ext n
  simp only [map_sub,map_add,coeff_C_mul_X_pow]
  simp only [coeff_mul_X_pow',A,coeff_mk]
  by_cases hn : n ≤ 7
  · interval_cases n <;> decide +kernel
  · simp (disch := omega) only [if_pos, if_neg]
    linarith [linear_recurrence n (by omega)]

end OMA.S_oeis_a128424

open OMA.S_oeis_a128424 in
theorem OMA.solution : type_of% @OMA.S_oeis_a128424.main :=
  ⟨linear_recurrence, gf⟩
