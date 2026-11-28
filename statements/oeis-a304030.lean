import Mathlib

/-!
# A304030: number of steps at which the Collatz trajectory of n crosses its initial value

Source: https://oeis.org/A304030 (claim in the comments of the entry)

Entry (offset 1): a(n) is the number of steps at which the Collatz ('3x+1') trajectory of n
crosses its initial value, or -1 if the number of crossings is infinite. The trajectory is
treated as terminating as soon as 1 is reached.
Claim: If the Collatz conjecture is true, then for n > 1, a(n) == n (mod 2).

Conventions:
* `collatz x` is the 3x+1 map: x/2 for even x and 3x+1 for odd x; `x n t` is the t-th iterate
  of n.
* A step t -> t+1 crosses the initial value n when x(t) and x(t+1) lie strictly on opposite
  sides of n, i.e. (x(t+1) - n) * (x(t) - n) < 0 (as in the programs of the entry).
* When the trajectory of n reaches 1, `stop n` is the first t with x(t) = 1 and the trajectory
  consists of the steps t -> t+1 for t < stop n; `crossings n` counts the crossing steps among
  them, which is a(n) in that case. Under the Collatz conjecture every trajectory reaches 1, so
  this is a(n) for every n >= 1.
* The Collatz conjecture is the hypothesis that every n >= 1 has an iterate equal to 1.
-/

namespace OMA.S_oeis_a304030

/-- The Collatz (3x+1) map. -/
def collatz (x : ℕ) : ℕ := if x % 2 = 0 then x / 2 else 3 * x + 1

/-- The t-th term of the Collatz trajectory of n. -/
def x (n t : ℕ) : ℕ := collatz^[t] n

/-- The first time the trajectory of n reaches 1 (meaningful when it does). -/
noncomputable def stop (n : ℕ) : ℕ := sInf {t : ℕ | x n t = 1}

/-- The number of steps t -> t+1, t < stop n, at which the trajectory crosses n. -/
noncomputable def crossings (n : ℕ) : ℕ :=
  ((Finset.range (stop n)).filter fun t =>
    ((x n (t + 1) : ℤ) - n) * ((x n t : ℤ) - n) < 0).card

theorem main : (∀ m : ℕ, 1 ≤ m → ∃ t, x m t = 1) →
    ∀ n : ℕ, 1 < n → crossings n % 2 = n % 2 := by
  sorry

end OMA.S_oeis_a304030
