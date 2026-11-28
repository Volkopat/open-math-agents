import Mathlib

/-!
# Eigenvalues of a double Möbius transform

Source: Mats Granvik, https://mathoverflow.net/questions/495907 (CC BY-SA 4.0).
Contribution by @connoranderson.

The row and column indexed by i : Fin n correspond to the integer i+1.
The symmetric variant uses Mathematica's entrywise multiplication.
Real eigenvalues are described as the real roots of the characteristic polynomial.
-/

namespace OMA.S_mo_495907
open Finset Polynomial
open scoped ArithmeticFunction.Moebius
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def first (d : ℕ) : ℤ := ∑ e ∈ d.divisors, μ e * (e : ℤ)
def entry (i j : ℕ) : ℤ := ∑ d ∈ i.divisors, μ d * first (d.gcd j)
def rad (i : ℕ) := ∏ p ∈ i.primeFactors, p
def count (n r : ℕ) := ((univ : Finset (Fin n)).filter (fun i => rad (i.val+1)=r)).card
noncomputable def raw (n : ℕ) : Mat n := fun i j => (entry (i.val+1) (j.val+1) : ℝ)
noncomputable def signs (n : ℕ) : Mat n := fun i j => ((entry (i.val+1) (j.val+1)).sign : ℝ)
noncomputable def symmSigns (n : ℕ) : Mat n := fun i j =>
  ((entry (i.val+1) (j.val+1) * entry (j.val+1) (i.val+1)).sign : ℝ)
def eigs {n : ℕ} (B : Mat n) : Set ℝ := {x | B.charpoly.IsRoot x}

theorem main :
    (∀ i j : ℕ, i ≠ 0 → j ≠ 0 → entry i j = if rad i ∣ j then (rad i : ℤ) else 0) ∧
    (∀ n : ℕ, (signs n).charpoly = ∏ i : Fin n, (X - C (count n (i.val+1) : ℝ))) ∧
    (∀ n : ℕ, (symmSigns n).charpoly = (signs n).charpoly) ∧
    (∀ n : ℕ, (raw n).charpoly =
       ∏ i : Fin n, (X - C ((i.val+1 : ℕ) * count n (i.val+1) : ℝ))) ∧
    IsGreatest (eigs (signs 48)) 6 ∧
    ¬ (∀ n : ℕ, 2 ≤ n → IsGreatest (eigs (signs n)) (Nat.log 2 n : ℝ)) := by
  sorry
end OMA.S_mo_495907
