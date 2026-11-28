import OMAStatements.S_oeis_a003459
import Mathlib

/-! Every multidigit permutable prime consists of repetitions of one
admissible digit, with at most one exceptional position. For a digit
repeated at least five times, a seven-digit suffix would otherwise force
divisibility by seven. The remaining multiplicities form a finite set.
The open step asks whether any such near-repdigit beyond 991 can fail
to be a repunit. See A. Slinko, Absolute Primes (arXiv:1811.08613),
for the classical digit restriction. -/
namespace OMA.R_oeis_a003459_R1
open OMA.S_oeis_a003459

def H1 : Prop := ∀ p : ℕ, 10 ≤ p → IsPermutablePrime p →
  (∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9]) ∧
    (∃ a : ℕ, (Nat.digits 10 p).length ≤ (Nat.digits 10 p).count a + 1)

def H2 : Prop := ∀ p : ℕ, 991 < p → IsPermutablePrime p →
  ((∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9]) ∧
    (∃ a : ℕ, (Nat.digits 10 p).length ≤ (Nat.digits 10 p).count a + 1)) →
  ∃ k : ℕ, p = (10 ^ k - 1) / 9

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a003459.main := by
  intro digits rest p hp hlarge
  exact rest p hlarge hp (digits p (by omega) hp)
end OMA.R_oeis_a003459_R1
