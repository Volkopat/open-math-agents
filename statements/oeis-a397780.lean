import Mathlib

/-!
# The number and distribution of the decimal digit supports in OEIS A397780

Each qualifying support first appears at its least nonnegative integer witness.
Source: https://oeis.org/A397780
-/

namespace OMA.S_oeis_a397780

/-- Zero has one decimal digit. The digit order is immaterial for multiplicities. -/
def decimalDigits (n : ℕ) : List ℕ := if n=0 then [0] else Nat.digits 10 n

def combined (n : ℕ) : List ℕ := decimalDigits n ++ decimalDigits (n*n)

def support (n : ℕ) : Finset ℕ := (combined n).toFinset

def eligible (n : ℕ) : Prop := ∀ d ∈ support n, d ≤ (combined n).count d

/-- The first qualifying integer with its particular set of digits. -/
def isTerm (n : ℕ) : Prop :=
  eligible n ∧ ∀ m < n, eligible m → support m ≠ support n

theorem main : {n : ℕ | isTerm n}.ncard = 665 ∧
    (List.range 10).map (fun j => {n : ℕ | isTerm n ∧ (support n).card = j+1}.ncard) =
      [2,1,2,31,243,210,120,45,10,1] := by
  sorry

end OMA.S_oeis_a397780
