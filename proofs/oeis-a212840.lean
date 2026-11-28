import OMAStatements.S_oeis_a212840
import Mathlib

/-!
# Proof of the polynomial, recurrence, and generating series for OEIS A212840

Partition continuations by whether the last letter is an endpoint. This yields
a two-state recurrence, with m interior letters. After seven steps the count is
a polynomial of degree seven in m. Eight backward differences give the claimed
recurrence and generating function, including the initial coefficients.
-/

namespace A212840Proof
open OMA.S_oeis_a212840

/-- Counts after an endpoint and after an interior letter or the start. -/
private def counts (m : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | k+1 =>
    let (e, u) := counts m k
    (e + m*u, 2*e + m*u)

private def select (p : Option Letter) (c : ℕ × ℕ) : ℕ :=
  match p with
  | some .low | some .high => c.1
  | _ => c.2

private theorem length_flat {α β : Type} (l : List α) (f : α → List β) :
    (l.flatMap f).length = (l.map (fun x => (f x).length)).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [ih]

private theorem count_words (m k : ℕ) (p : Option Letter) :
    (words m k p).length = select p (counts m k) := by
  induction k generalizing p with
  | zero => cases p with
            | none => rfl
            | some l => cases l <;> rfl
  | succ k ih =>
    simp only [words, length_flat, List.length_map, ih]
    cases p with
    | none =>
      simp [choices, select, counts, List.map_map, Function.comp_def]
      omega
    | some l =>
      cases l <;> simp [choices, select, counts, List.map_map, Function.comp_def]
      omega

theorem polynomial (m : ℕ) :
    a (m+1) = m^7 + 14*m^6 + 72*m^5 + 170*m^4 + 192*m^3 + 102*m^2 + 24*m + 2 := by
  rw [a, count_words]
  simp only [select, counts]
  ring

/-- Hardin's empirical polynomial, expressed in the original alphabet parameter. -/
theorem original_polynomial (m : ℕ) :
    let n : ℤ := (m : ℤ) + 1
    (a (m+1) : ℤ) = n^7+7*n^6+9*n^5-15*n^4-13*n^3+15*n^2-n-1 := by
  rw [polynomial]
  push_cast
  ring

/-- Barker's order-eight recurrence, starting at height parameter 9. -/
theorem recurrence (m : ℕ) :
    (a (m+9) : ℤ) = 8*a (m+8) - 28*a (m+7) + 56*a (m+6) - 70*a (m+5)
      + 56*a (m+4) - 28*a (m+3) + 8*a (m+2) - a (m+1) := by
  repeat rw [show ∀ k, (a (k+1) : ℤ) = _ from original_polynomial]
  push_cast
  ring

open PowerSeries

/-- Coefficients after multiplying a formal series by (1-X) exactly k times. -/
private def differences (f : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0, n => f n
  | k+1, 0 => differences f k 0
  | k+1, n+1 => differences f k (n+1) - differences f k n

private theorem coeff_differences (f : ℕ → ℤ) (k n : ℕ) :
    coeff n ((1-X)^k * PowerSeries.mk f) = differences f k n := by
  induction k generalizing n with
  | zero => simp [differences]
  | succ k ih =>
    rw [pow_succ', mul_assoc, sub_mul, one_mul, map_sub, ih]
    cases n with
    | zero => simp [differences]
    | succ n => rw [coeff_succ_X_mul, ih, differences]

/-- The denominator has constant coefficient one, so this specifies the generating series. -/
theorem generating_function :
    (1-X)^8 * PowerSeries.mk (fun n => (a n : ℤ)) = PowerSeries.mk numerator := by
  ext n
  rw [coeff_differences, coeff_mk]
  have h0 : a 0 = 0 := rfl
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | m
  all_goals simp only [differences, numerator, polynomial, h0]
  all_goals push_cast
  all_goals ring

end A212840Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a212840.main := by
  exact ⟨A212840Proof.original_polynomial, A212840Proof.recurrence, A212840Proof.generating_function⟩
