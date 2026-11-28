import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Choose.Sum

/-!
# A220181 — Period of the toppleable permutation numbers modulo a prime

Source: Peter Bala's conjecture (June 1, 2022), https://oeis.org/A220181,
OEIS Foundation, CC BY-SA 4.0.

The defining e.g.f. is the sum over k of (1-exp(-k*x))^k. Expand its k-th
summand as (-1)^k (exp(-k*x)-1)^k. In degree n, the i-th exponential in
the binomial expansion contributes (-k*i)^n after multiplication by n!.
Only k ≤ n can contribute. This is the integer formula used below.
-/

namespace OMA.S_oeis_a220181

open Finset

def term (n k : ℕ) : ℤ :=
  (-1)^k * (-(k : ℤ))^n *
    ∑ i ∈ range (k+1), (-1 : ℤ)^(k-i) * (k.choose i : ℤ) * (i : ℤ)^n

def a (n : ℕ) : ℤ := ∑ k ∈ range (n+1), term n k

theorem main : ∀ p : ℕ, p.Prime → ∀ n : ℕ, 1 ≤ n →
    (a (n + (p - 1)) : ZMod p) = (a n : ZMod p) := by
  sorry

end OMA.S_oeis_a220181
