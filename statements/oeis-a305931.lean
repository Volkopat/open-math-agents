import Mathlib

/-!
# A305931: Powers of 3 having at least one digit '0' in their decimal representation.

Source: https://oeis.org/A305931
Credit: @azmiozgen

Conjectures (from the entry):
1. The complement A238939 has only 23 elements, the largest being 3^68; thus all larger powers
   of 3 are in this sequence.
2. Each of the subsequences "powers of 3 with exactly n digits 0" is finite.

Formalization notes:
* Conjecture 1 is stated as: for every k > 68, the digit 0 occurs in the decimal digits of 3^k.
* Conjecture 2 is stated as: for every n, the set of exponents k such that 3^k has exactly n
  digits 0 in base 10 is finite.
* Controls (computed): 3^10 = 59049 is the first power of 3 with a digit 0 (the first term);
  exactly 23 exponents k ≤ 68 give zeroless powers, the largest being k = 68, as A238939 lists.
-/

namespace OMA.S_oeis_a305931

/-- Both conjectures of the entry. -/
theorem main :
    (∀ k : ℕ, 68 < k → 0 ∈ Nat.digits 10 (3 ^ k)) ∧
      ∀ n : ℕ, {k : ℕ | (Nat.digits 10 (3 ^ k)).count 0 = n}.Finite := by
  sorry

end OMA.S_oeis_a305931
