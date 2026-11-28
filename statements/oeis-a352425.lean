import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Find
import Mathlib.NumberTheory.Divisors

/-!
# Parts in partitions into an odd number of consecutive positive integers

Row n of A352425 is formed by listing the parts of all such partitions.
A partition is uniquely specified by its smallest part l and its length d;
the two bounds l,d≤n lose no positive-part partition. A003056(n) is the
largest t with t(t+1)/2≤n. A341309(n) sums the odd divisors up to this bound.

Sources: https://oeis.org/A352425, https://oeis.org/A003056, and
https://oeis.org/A341309 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Solitude1312
-/

namespace OMA.S_oeis_a352425

def runSum (l d : ℕ) : ℕ := ∑ i ∈ Finset.range d, (l + i)

def runs (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 n) ×ˢ (Finset.Icc 1 n)).filter fun z => Odd z.2 ∧ runSum z.1 z.2 = n

def triangularRoot (n : ℕ) : ℕ := Nat.findGreatest (fun d => d * (d+1) ≤ 2*n) n

def lengths (n : ℕ) : Finset ℕ := n.divisors.filter fun d => Odd d ∧ d ≤ triangularRoot n

theorem main : ∀ n : ℕ, 0 < n → (∑ z ∈ runs n, z.2) = ∑ d ∈ lengths n, d := by
  sorry

end OMA.S_oeis_a352425
