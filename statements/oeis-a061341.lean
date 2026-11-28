import Mathlib

/-!
# The last digits of roots of concatenated cubes (OEIS A061341)

François Marques conjectured on July 11, 2021 that the roots in A061341 have
last digit in {1,2,3,4,5,6,8}, and that those ending in 3 are of the form
3·10^k+3 for k ≥ 2. A061341 consists of roots not ending in zero whose cube
is the concatenation of at least two other cubes. The example for 2272
explicitly includes 0 as a one-digit cube. Digits appear in reading order.

Source: https://oeis.org/A061341
Credit: Robert Leshner (@rleshner).
-/
namespace OMA.S_oeis_a061341

/-- The usual, unpadded decimal representation, including the one digit of zero. -/
def decimal (n : ℕ) : List ℕ := if n = 0 then [0] else (Nat.digits 10 n).reverse

/-- Each listed root contributes the full decimal expansion of its cube. -/
def member (n : ℕ) : Prop :=
  n % 10 ≠ 0 ∧ ∃ roots : List ℕ, 2 ≤ roots.length ∧
    roots.flatMap (fun r => decimal (r^3)) = decimal (n^3)

theorem main : ∀ n : ℕ, member n →
    n % 10 ∈ ({1,2,3,4,5,6,8} : Finset ℕ) ∧
    (n % 10 = 3 → ∃ k : ℕ, 2 ≤ k ∧ n = 3*10^k+3) := by
  sorry

end OMA.S_oeis_a061341
