import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic

/-!
# The number of cyclotomic cosets of 3 modulo powers of 10

Source: https://oeis.org/A220018
Credit: @luciusacarr
-/

namespace OMA.S_oeis_a220018

/-- Traverse the orbit of `start`, stopping upon returning to it. -/
def orbitMin (modulus start : ℕ) : ℕ → ℕ → ℕ
  | 0, current => current
  | fuel + 1, current =>
    let next := (3 * current) % modulus
    if next = start then current else min current (orbitMin modulus start fuel next)

/-- Multiplication by 3 permutes the residues modulo `10^n`. Every orbit
returns to its start within `10^n` steps and has one least representative. -/
def a (n : ℕ) : ℕ :=
  let modulus := 10 ^ n
  ((Finset.range modulus).filter (fun r => orbitMin modulus r modulus r = r)).card

theorem main :
    (∀ n : ℕ, 2 < n → (a n : ℤ) = 8 * (n : ℤ) ^ 2 - 14 * (n : ℤ) - 1) ∧
    (∀ n : ℕ, 5 < n → (a n : ℤ) =
      3 * (a (n - 1) : ℤ) - 3 * (a (n - 2) : ℤ) + (a (n - 3) : ℤ)) := by
  sorry

end OMA.S_oeis_a220018
