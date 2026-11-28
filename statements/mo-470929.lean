import Mathlib

/-!
# Positivity of a signed Stirling–Delannoy sum

Source: https://mathoverflow.net/questions/470929
Credit: @Mapika

Zhi Wang asks for strict positivity for every n ≥ 1 and every coefficient
index between 0 and d = 2n+2. The first-kind Stirling numbers are signed.
-/

open Finset
open scoped BigOperators
namespace OMA.S_mo_470929

def delannoy : ℕ → ℕ → ℕ
  | 0, _ => 1
  | _ + 1, 0 => 1
  | a + 1, b + 1 => delannoy a (b+1) + delannoy (a+1) b + delannoy a b
termination_by a b => a+b

def signedFirst (d j : ℕ) : ℤ :=
  (-1 : ℤ) ^ (d-j) * (Nat.stirlingFirst d j : ℤ)

theorem main : ∀ n : ℕ, 1 ≤ n → ∀ m : ℕ, m ≤ 2*n+2 →
    let d := 2*n+2
    0 < ∑ i ∈ range (n+1), ((delannoy (n-i) i : ℚ) / (d : ℚ)) *
      (∑ j ∈ Icc m d, (signedFirst d j : ℚ) * (j.choose m : ℚ) *
        ((d : ℚ) - (i : ℚ)) ^ (j-m)) := by
  sorry
end OMA.S_mo_470929
