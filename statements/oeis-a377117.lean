import Mathlib.Data.Nat.Nth
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# OEIS A377117, the divisibility and index-gap conjecture

Source: https://oeis.org/A377117 (Clark Kimberling; OEIS Foundation, CC BY-SA 4.0).
Let t³ = 2 and b = t + t². Since b³ = 6b + 6, its constant coefficients
satisfy c(n+3) = 6(c(n)+c(n+1)), with c(1)=0, c(2)=4, c(3)=6.
The published list uses 1 at indices 0 and 1. The definition below preserves
those displayed terms and the stated algebraic coefficients from index 2 on.

The conjectural assertion is infinite divisibility for each prime and eventual
periodicity of the successive gaps. The entry also specifies exact repeating
gap lists for the first six primes. Both claims are recorded, separately named.
-/

namespace OMA.S_oeis_a377117

def advance {R : Type} [CommSemiring R] (u : R × R × R) : R × R × R :=
  (u.2.1, u.2.2, 6 * (u.1 + u.2.1))

def state (R : Type) [CommSemiring R] (n : ℕ) : R × R × R :=
  advance^[n] (0, 4, 6)

def a : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => (state ℕ (n + 1)).1

noncomputable def gap (p i : ℕ) : ℕ :=
  Nat.nth (fun n => p ∣ a n) (i + 1) - Nat.nth (fun n => p ∣ a n) i

def primeGaps : Prop := ∀ p : ℕ, p.Prime →
    {n : ℕ | p ∣ a n}.Infinite ∧
    ∃ K L : ℕ, 0 < L ∧ ∀ i ≥ K, gap p (i + L) = gap p i

def reportedPeriods : List (ℕ × List ℕ) :=
  [(2, [1]), (3, [1, 2, 8, 9, 4]), (5, [21, 9, 10]),
   (7, [8, 42, 7, 19, 1, 2, 10, 31, 4, 11, 6, 34, 60, 23, 5, 9, 16]),
   (11, [9, 21]),
   (13, [15, 51, 45, 1, 2, 17, 41, 28, 54, 119, 13, 9, 25])]

def tableCorrect : Prop :=
  ∀ (p : ℕ) (l : List ℕ), (p, l) ∈ reportedPeriods →
    ∀ i : ℕ, gap p i = l.getD (i % l.length) 0

theorem main : primeGaps ∧ tableCorrect := by
  sorry

end OMA.S_oeis_a377117
