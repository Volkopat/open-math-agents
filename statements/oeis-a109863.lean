import Mathlib

/-!
# A109863: Primes arising as the 10's complement of A109862(n).

Source: https://oeis.org/A109863
Credit: @luciusacarr

The entry records one conjecture: the sequence is infinite. (Its other comments, that `a(n) - 1`
is a palindrome and that 7, 5 and 3 are the only palindromic terms, are presented as facts.) Its
terms begin 7, 5, 3, 89, 809, 647, 617, 71, 89399, ... (647 = 1000 - 353, with 353 in A109862).

Reading of the source:
* A109862 lists the palindromic primes `p` whose 10's complement `10^L - p` is prime, where `L` is
  the number of decimal digits of `p`. This sequence lists those complements `10^L - p`.
* The sequence is listed in the order of A109862 (it is not monotone); "infinite" is read as the
  set of values `10^L - p`, for `p` in A109862, being infinite. (Distinct `p` with the same number
  of digits give distinct complements, and complements are below `10^L`, so infinitely many `p`
  give infinitely many values.)
-/

namespace OMA.S_oeis_a109863

/-- The 10's complement of `p`: `10^L - p`, where `L` is the number of decimal digits of `p`. -/
def tensComplement (p : ℕ) : ℕ := 10 ^ (Nat.digits 10 p).length - p

/-- `p` is a term of A109862: a palindromic prime whose 10's complement is prime. -/
def IsA109862 (p : ℕ) : Prop :=
  p.Prime ∧ (Nat.digits 10 p).reverse = Nat.digits 10 p ∧ (tensComplement p).Prime

theorem main : {q : ℕ | ∃ p : ℕ, IsA109862 p ∧ q = tensComplement p}.Infinite := by
  sorry

end OMA.S_oeis_a109863
