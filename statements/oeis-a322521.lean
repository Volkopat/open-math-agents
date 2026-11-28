import Mathlib

/-!
# A322521: inverse of the Collatz tree encoding A319303
Source: https://oeis.org/A322521 (Remy Sigrist, Dec 13 2018)

Claim: if the Collatz conjecture is true, then this sequence contains every nonnegative integer.

Conventions.
* A319303(n) (offset 0) is computed by the program of its entry: start at v = 1 with r = n;
  while r > 0: decrement r; if v > 4 and v + 2 is a multiple of 6 (a branching node of the
  Collatz tree other than 4), move to 2v when r is even and to (v-1)/3 when r is odd, and then
  replace r by floor(r/2); otherwise move to 2v. The result is the final value of v.
  Here `enc v r` is the value reached from node v with counter r, so A319303(n) = enc 1 n.
* A322521(n) (offset 1): if A319303(k) = n for some k then a(n) = k (we take the least such k),
  else a(n) = -1.
* The Collatz conjecture: every positive integer reaches 1 under iteration of the map
  n -> n/2 (n even), n -> 3n+1 (n odd).
* Contains every nonnegative integer: for every k there is n >= 1 with a(n) = k.
-/

namespace OMA.S_oeis_a322521

/-- The node reached from node v with counter r. -/
def enc (v : ℕ) : ℕ → ℕ
  | 0 => v
  | r + 1 =>
    if 4 < v ∧ (v + 2) % 6 = 0 then
      (if r % 2 = 0 then enc (2 * v) (r / 2) else enc ((v - 1) / 3) (r / 2))
    else enc (2 * v) r
termination_by r => r
decreasing_by all_goals omega

/-- A319303. -/
def A319303 (n : ℕ) : ℕ := enc 1 n

open Classical in
/-- A322521. -/
noncomputable def a (n : ℕ) : ℤ :=
  if h : ∃ k, A319303 k = n then (Nat.find h : ℤ) else -1

/-- The Collatz map. -/
def collatz (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

theorem main : (∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, collatz^[m] n = 1) →
    ∀ k : ℕ, ∃ n : ℕ, 1 ≤ n ∧ a n = k := by
  sorry

end OMA.S_oeis_a322521
