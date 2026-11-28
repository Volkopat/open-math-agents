import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Prime.Defs

/-!
# Least modulus meeting the AKS order threshold

Source: Jianing Song, OEIS A394432, https://oeis.org/A394432 (CC BY-SA 4.0).
Credit: @jatin6

The entry starts at n = 2, where the PARI convention gives a(2) = 1.
The first assertion records this listed exception explicitly. Above it,
the proposed prime powers have positive exponent. The second assertion
asks for an occurrence other than the specific high-exponent occurrences
listed in the entry. The third is the separate strict-threshold conjecture.
-/

namespace OMA.S_oeis_a394432

noncomputable def threshold (n : ℕ) : ℝ := (Real.logb 2 (n : ℝ)) ^ 2

def IsTerm (n r : ℕ) : Prop :=
  IsLeast {s : ℕ | 0 < s ∧ n.Coprime s ∧
    threshold n ≤ (orderOf (n : ZMod s) : ℝ)} r

def OddPrimePowers : Prop :=
  IsTerm 2 1 ∧ ∀ n : ℕ, 3 ≤ n → ∃ r p k : ℕ,
    IsTerm n r ∧ p.Prime ∧ Odd p ∧ 0 < k ∧ r = p ^ k

def Listed (n r : ℕ) : Prop :=
  (r = 81 ∧ n ∈ ([110, 119] : List ℕ)) ∨
  (r = 625 ∧ n ∈ ([3961388, 4132533, 4466762, 4610283, 4629398, 4961877,
    4966163, 5006623, 5054222, 5063527, 5276203, 5314622, 5338663] : List ℕ))

def FurtherPower : Prop := ∃ n r p k : ℕ, 2 ≤ n ∧ IsTerm n r ∧ p.Prime ∧
  3 < k ∧ r = p ^ k ∧ ¬ Listed n r

def StrictAtPowersOfTwo : Prop := ∀ e : ℕ, 1 < e → ∃ r : ℕ,
  IsTerm (2 ^ e) r ∧
  orderOf ((2 ^ e : ℕ) : ZMod r) = orderOf (2 : ZMod r) / Nat.gcd (orderOf (2 : ZMod r)) e ∧
  e ^ 2 < orderOf ((2 ^ e : ℕ) : ZMod r)

theorem main : OddPrimePowers ∧ FurtherPower ∧ StrictAtPowersOfTwo := by
  sorry

end OMA.S_oeis_a394432
