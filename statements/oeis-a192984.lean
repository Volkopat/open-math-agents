import Mathlib

/-!
# A192984: In repeated iterations of function m->m/3 if m == 0 (mod 3), m->4m+a if 4m+a == 0 (mod 3) where a = 1 or 2, a(n) is maximum value achieved if starting from n.

Source: https://oeis.org/A192984
Credit: @agchua

Comment of A192984 (unsigned):
  If a(n) exists (which is the conjecture of A194428) then a(n) must be a multiple of 9, since if
  a(n) is not divisible by 3 then the next iteration 4*a(n) + 1 or 4*a(n) + 2 would be greater
  than a(n), while if a(n) was divisible by 3 only once, a(n) = 3x -> x -> 4x+1 or 4x+2 is
  greater than 3x.
Offset 1, data 9, 9, 9, 18, 189, ... (a(4) = 18: the trajectory is 4, 18, 6, 2, 9, 3, 1, 6, ...).
The map sends m to m/3 if 3 divides m, and otherwise to 4m + a with a in {1, 2} such that 3
divides 4m + a, that is a = 2 if m = 1 (mod 3) and a = 1 if m = 2 (mod 3). The trajectory starts
with n itself. a(n) exists when the set of values achieved has a greatest element. The claim is
stated for every n >= 1.
-/

namespace OMA.S_oeis_a192984

/-- The map m -> m/3 if m = 0 (mod 3), m -> 4m + a otherwise, where a in {1, 2} makes 4m + a
divisible by 3. -/
def step (m : ℕ) : ℕ :=
  if m % 3 = 0 then m / 3 else if m % 3 = 1 then 4 * m + 2 else 4 * m + 1

/-- The values achieved by the trajectory n, step(n), step(step(n)), ... -/
def orbit (n : ℕ) : Set ℕ := {m | ∃ k : ℕ, step^[k] n = m}

/-- The claim: if a(n) exists, that is, if the values achieved starting from n have a maximum M,
then M is a multiple of 9. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∀ M : ℕ, IsGreatest (orbit n) M → 9 ∣ M := by
  sorry

end OMA.S_oeis_a192984
