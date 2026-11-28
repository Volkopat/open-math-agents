import Mathlib

/-!
# Record changes in the number of prime-power quotients (OEIS A357604)

Source: https://oeis.org/A357604 (Randell Heyman; conjecture by Thomas
Scheuerle, October 2022). Credit: @Chihiro-g.

Every denominator contributes separately, even when two quotients coincide.
At zero the counting sum is empty in effect. A record strictly exceeds all
earlier values starting at index one. The second clause is read as record
indices, consistently with the first clause and the reported check to 20000:
the drop size 5 itself already sets a record at 60 and is outside A025487.
A135972 consists of nonprime Mersenne numbers. A025487 consists of products
of primorials, equivalently the least integers of each prime signature.
-/

namespace OMA.S_oeis_a357604

def indicator (q : ℕ) : ℤ := if IsPrimePow q then 1 else 0

/-- The extra denominator zero contributes zero by natural-number division. -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), indicator (n / k)

def recordAt (f : ℕ → ℤ) (n : ℕ) : Prop :=
  1 ≤ n ∧ ∀ j : ℕ, 1 ≤ j → j < n → f j < f n

def leastSignature (n : ℕ) : Prop :=
  ∃ l : List ℕ, (l.map primorial).prod = n

theorem main :
    (∀ n : ℕ, recordAt (fun j => a (j + 1) - a j) n →
      (∃ e : ℕ, n + 1 = 2 ^ e) ∧ ¬ n.Prime) ∧
    (∀ n : ℕ, recordAt (fun j => a (j - 1) - a j) n →
      leastSignature n) := by
  sorry

end OMA.S_oeis_a357604
