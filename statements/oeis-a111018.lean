import Mathlib

/-!
# A111018: Indices of Catalan numbers that are divisible by 3.

Source: https://oeis.org/A111018
Credit: @agchua

Comment of A111018 (L. Edson Jeffery, Dec 02 2015):
  Conjecture: The sequence contains all numbers n such that n and n+1 are both in the sequence
  A074940, or, equivalently, such that neither n nor n+1 is in the sequence A005836.
A074940 is the numbers with at least one digit 2 in base 3; A005836 is the numbers with no digit 2
in base 3 (0 included). A000108 is Mathlib's catalan (catalan 0 = 1), and A111018 is the set of
n with 3 dividing catalan n (the offset 1 changes nothing, since catalan 0 = 1). Both forms of the
conjecture are stated, for all n >= 0.
-/

namespace OMA.S_oeis_a111018

/-- A074940: the numbers with at least one digit 2 in base 3. -/
def A074940 : Set ℕ := {n | 2 ∈ Nat.digits 3 n}

/-- A005836: the numbers with no digit 2 in base 3. -/
def A005836 : Set ℕ := {n | 2 ∉ Nat.digits 3 n}

/-- A111018: the indices n of the Catalan numbers divisible by 3. -/
def A111018 : Set ℕ := {n | 3 ∣ catalan n}

/-- The comment's conjecture, in both of its forms. -/
theorem main :
    (∀ n : ℕ, n ∈ A074940 → n + 1 ∈ A074940 → n ∈ A111018) ∧
    (∀ n : ℕ, n ∉ A005836 → n + 1 ∉ A005836 → n ∈ A111018) := by
  sorry

end OMA.S_oeis_a111018
