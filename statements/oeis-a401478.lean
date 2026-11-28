import Mathlib

/-!
# A401478: Numbers that are not the sum of at most seven 6-full numbers.

Source: https://oeis.org/A401478
Credit: @keiichisince1986-bot

A401478 is the sequence `a(n)` named in the title. The entry states:
Erdős and Ivić conjectured that every sufficiently large integer is the sum of at most r+1 r-full
numbers; for r = 6 this would imply that this sequence is finite. (The statement below is the
conjecture that the sequence is finite.)

Conventions:
- An `r`-full number is a positive integer `x` such that `p^r` divides `x` for every prime `p` dividing `x`;
  `1` is `r`-full (it is a term of A036967 and A069492). `IsFull r x`.
- A sum of at most `7` such numbers is the sum of a list of length `≤ 7` of them.
-/

namespace OMA.S_oeis_a401478

/-- `x` is `r`-full: positive, and every prime dividing it divides it to the `r`-th power. -/
def IsFull (r x : ℕ) : Prop := 0 < x ∧ ∀ p : ℕ, p.Prime → p ∣ x → p ^ r ∣ x

theorem main :
    {n : ℕ | ¬ ∃ l : List ℕ, l.length ≤ 7 ∧ (∀ x ∈ l, IsFull 6 x) ∧ l.sum = n}.Finite := by
  sorry

end OMA.S_oeis_a401478
