import Mathlib

/-!
# A069517: a(n) = (-1)*Sum_{d|n} (moebius(d)*(-1)^d).

Source: https://oeis.org/A069517 (conjecture of Peter Bala, Sep 11 2026), together with
https://oeis.org/A393210.
Credit: @esracummings31-blip

Conjecture: Sum_{d | n} a(d)^2 * phi(d) = A393210(n), for n >= 1, where A069517(n) =
Sum_{d | n} (-1)^(d+1) * moebius(d) and A393210(n) is the halting time of Wolfram's 2-state
2-symbol Turing machine 3626 when started with n on the tape.

Conventions for A393210 (Wolfram, P vs. NP and the Difficulty of Computation, 2026, The Basic
Setup): the binary digits of n are written on an otherwise blank (all 0) tape, the head starts
on the least significant digit in state 1, and the machine stops as soon as the head moves
further to the right than where it started. The halting time is the number of steps taken.

Machine 3626 in Wolfram's numbering has the rules (state, read) -> (state, write, move):
  (1, 0) -> (1, 0, left),  (1, 1) -> (2, 1, right),
  (2, 0) -> (1, 1, left),  (2, 1) -> (2, 0, right).
This decoding was checked to reproduce the 1000 terms of the b-file of A393210, as well as
A037227 for machine 3589 and A010684 for machine 3197 (the machines cross-referenced there).

Below, Wolfram's states 1 and 2 are `0` and `1`, a cell holds a `Bool` (true = digit 1), and
cells are indexed by `p : ℤ`, the distance to the left of the starting cell, so cell `p ≥ 0`
initially holds bit `p` of `n`. Moving left is `p + 1`, moving right is `p - 1`, and the
machine has stopped once the head position is negative.
-/

namespace OMA.S_oeis_a069517

open ArithmeticFunction

/-- A069517(n) = Sum_{d | n} (-1)^(d+1) * moebius(d). -/
def a (n : ℕ) : ℤ := ∑ d ∈ n.divisors, (-1) ^ (d + 1) * moebius d

/-- A configuration of the Turing machine: state, head position, tape. -/
structure Cfg where
  state : Fin 2
  pos : ℤ
  tape : ℤ → Bool

/-- One step of Wolfram's 2-state 2-symbol Turing machine 3626. -/
def step (c : Cfg) : Cfg :=
  match c.state, c.tape c.pos with
  | 0, false => ⟨0, c.pos + 1, Function.update c.tape c.pos false⟩
  | 0, true => ⟨1, c.pos - 1, Function.update c.tape c.pos true⟩
  | 1, false => ⟨0, c.pos + 1, Function.update c.tape c.pos true⟩
  | 1, true => ⟨1, c.pos - 1, Function.update c.tape c.pos false⟩

/-- The start configuration for input `n`: binary digits of `n`, head on the last digit. -/
def init (n : ℕ) : Cfg :=
  ⟨0, 0, fun p => if 0 ≤ p then n.testBit p.toNat else false⟩

/-- The configuration after `t` steps. -/
def run (n t : ℕ) : Cfg := step^[t] (init n)

/-- `t` is the halting time on input `n`: the head is first to the right of its start
after exactly `t` steps. -/
def IsHaltTime (n t : ℕ) : Prop :=
  (run n t).pos < 0 ∧ ∀ s < t, 0 ≤ (run n s).pos

/-- Bala's conjecture: Sum_{d | n} A069517(d)^2 * phi(d) = A393210(n) for every n ≥ 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    ∃ t : ℕ, IsHaltTime n t ∧ (t : ℤ) = ∑ d ∈ n.divisors, a d ^ 2 * (d.totient : ℤ) := by
  sorry

end OMA.S_oeis_a069517
