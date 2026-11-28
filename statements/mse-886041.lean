import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Order.Interval.Finset.Nat

/-!
# Counting distinct products by largest divisors

Source: Fred Daniel Kline, Math.SE 886041, August 2014, CC BY-SA 3.0.
https://math.stackexchange.com/questions/886041

The question asks for the multiplication table with k rows and k! columns;
the closing sentence proposes using lcm(1,...,k) columns as well. The sum
runs from 1 to the number of columns inclusive, using the zero-based index r.
-/

namespace OMA.S_mse_886041

open Finset

def beta (n k : ℕ) : ℕ := Nat.findGreatest (fun d => d ∣ n) k

def divisorSum (k m : ℕ) : ℕ := ∑ r ∈ range m, beta (r+1) k

def table (k m : ℕ) : Finset ℕ :=
  ((Icc 1 k) ×ˢ (Icc 1 m)).image (fun z => z.1*z.2)

def period (k : ℕ) : ℕ := (Icc 1 k).lcm id

theorem main : ∀ (k : ℕ), 0 < k →
    divisorSum k k.factorial = (table k k.factorial).card ∧
    divisorSum k (period k) = (table k (period k)).card := by
  sorry

end OMA.S_mse_886041
