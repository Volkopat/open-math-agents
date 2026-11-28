import Mathlib

/-!
# OEIS A345211: the terms are even, and their halves are the complement of A157932

Source: https://oeis.org/A345211 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-fable-5-2), submitted by @jleguina.

Entry A345211: Numbers with the same number of odd / even, refactorable divisors. A refactorable
number (A033950) is a positive integer divisible by its number of divisors. Comment (Amiram Eldar,
Oct 11 2023): All the terms are even. Conjecture: The sequence a(n)/2 is the complement of A157932
(verified for a(n) < 4*10^7).
Entry A157932: Numbers k such that (3^(35*k) + 5^(21*k) + 7^(15*k)) mod 105 is prime.

Formalization notes:
* The statement has both sentences of the comment: every term is even, and for every positive m,
  2*m is a term if and only if m is not in A157932.
* A157932 lists k = 0 as its first term; the terms of A345211 are positive, so the complement is
  taken in the positive integers.
* Controls: the terms of A345211 up to 30 are 2, 4, 6, 10, 14, 18, 20, 22, 26, 28, 30 and the
  terms of A157932 up to 20 are 0, 4, 6, 8, 12, 16, 18, 20, as in the entries.
-/

namespace OMA.S_oeis_a345211

/-- d is refactorable: its number of divisors divides it. -/
def Refac (d : ℕ) : Prop := (Nat.divisors d).card ∣ d

instance : DecidablePred Refac := fun d => inferInstanceAs (Decidable ((Nat.divisors d).card ∣ d))

/-- The odd refactorable divisors of n. -/
def oddRef (n : ℕ) : Finset ℕ := (Nat.divisors n).filter (fun d => Odd d ∧ Refac d)

/-- The even refactorable divisors of n. -/
def evenRef (n : ℕ) : Finset ℕ := (Nat.divisors n).filter (fun d => Even d ∧ Refac d)

/-- Membership in A345211. -/
def InA345211 (n : ℕ) : Prop := 0 < n ∧ (oddRef n).card = (evenRef n).card

/-- Membership in A157932. -/
def InA157932 (k : ℕ) : Prop := ((3 ^ (35 * k) + 5 ^ (21 * k) + 7 ^ (15 * k)) % 105).Prime

/-- All terms of A345211 are even, and the halves of the terms are exactly the positive integers
that are not in A157932. -/
theorem main : (∀ n : ℕ, InA345211 n → Even n) ∧
    (∀ m : ℕ, 0 < m → (InA345211 (2 * m) ↔ ¬ InA157932 m)) := by
  sorry

end OMA.S_oeis_a345211
