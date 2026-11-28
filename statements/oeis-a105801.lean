import Mathlib.Data.Nat.Basic

/-!
# Eventual stabilization of A105801 modulo powers of three

Source: https://oeis.org/A105801
Credit: @blakestone-x

OEIS starts at index one. Consecutive terms are carried as an ordered pair.
The conjecture asks for one common residue for each positive exponent.
-/

namespace OMA.S_oeis_a105801

def next (x y : Nat) : Nat :=
  if (x+y)%2 = 0 then (x+y)/2 else 3*(x+y)+1

def step (s : Nat × Nat) : Nat × Nat := (s.2, next s.1 s.2)

def orbit (s : Nat × Nat) : Nat → Nat × Nat
  | 0 => s
  | n+1 => step (orbit s n)

def sequence (s : Nat × Nat) : Nat → Nat
  | 0 => 0
  | n+1 => (orbit s n).1

def a : ℕ → ℕ := sequence (1, 2)

theorem main : ∀ k : ℕ, 0 < k → ∃ m r : ℕ, ∀ n : ℕ, m < n → a n % 3^k = r := by
  sorry

end OMA.S_oeis_a105801
