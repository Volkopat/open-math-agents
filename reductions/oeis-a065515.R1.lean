import OMAStatements.S_oeis_a065515
import Mathlib

/-! Distinct prime squares and prime cubes supply a reserve in addition to
all the primes and 1. It suffices to control the prime count at the number
of perfect powers using just the square and cube cutoffs. -/
namespace OMA.R_oeis_a065515_R1
open OMA.S_oeis_a065515
def H1 : Prop := ∀ n s c : ℕ, 1≤n → s^2≤n → c^3≤n →
  Nat.primeCounting n + Nat.primeCounting s + Nat.primeCounting c + 1 ≤ a n

def H2 : Prop := ∀ n : ℕ, 1≤n → ∃ s c : ℕ, s^2≤n ∧ c^3≤n ∧
  Nat.primeCounting (A069623 n) ≤ Nat.primeCounting s + Nat.primeCounting c

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a065515.main := by
  intro counts interval n hn
  obtain ⟨s,c,hs,hc,pi⟩ := interval n hn
  have := counts n s c hn hs hc
  omega
end OMA.R_oeis_a065515_R1
