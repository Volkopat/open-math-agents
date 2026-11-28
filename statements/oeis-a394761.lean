import Mathlib.Data.Nat.GCD.Basic

/-!
# OEIS A394761

Source: https://oeis.org/A394761 (Sam Chapman)

A381466 defines the states. A392200 gives the gcd at each positive step.
A maximal positive run of unit gcds gives one term of A394761. Consecutive
runs of the same length are separated by one step of non-unit gcd, since
a division updates the state to a divisor of the step index and the
next step is then coprime to the updated state.
-/

namespace OMA.S_oeis_a394761

def state : ℕ → ℕ
  | 0 => 4
  | n + 1 =>
    let s := state n
    let g := Nat.gcd s (n + 1)
    if g = 1 then s + (n + 1) else (n + 1) / g

def gcdAt (n : ℕ) : ℕ := Nat.gcd (state n) (n + 1)

def IsRun (start len : ℕ) : Prop :=
  0 < len ∧ (start = 0 ∨ gcdAt (start - 1) ≠ 1) ∧
    (∀ j < len, gcdAt (start + j) = 1) ∧ gcdAt (start + len) ≠ 1

def Repeated (start len count : ℕ) : Prop :=
  ∀ j < count, IsRun (start + j * (len + 1)) len

theorem main : ∀ start : ℕ,
    ¬ Repeated start 1 9 ∧ ¬ Repeated start 2 5 ∧ ¬ Repeated start 3 4 := by
  sorry

end OMA.S_oeis_a394761
