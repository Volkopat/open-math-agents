import Mathlib

/-!
# A078173: a(n) = max(min(r,s,t)) over positive integer solutions of r*s*t = n*(r+s+t)

Source: https://oeis.org/A078173
Credit: @xor2k

Formalizes the OEIS A078173 conjecture (offset 1):
Conjecture: max(t) = n*(n+2) and max(s) = 2*n, where the maxima are taken over all positive
integer solutions r<=s<=t of the above Diophantine equation (r*s*t = n*(r+s+t)).

Conventions:
* n ranges over the positive integers (offset 1).
* `Sol n r s t` means r, s, t are positive integers with r <= s <= t and r*s*t = n*(r+s+t);
  positivity of s and t follows from 0 < r and the ordering.
* A maximum is expressed with Mathlib's `IsGreatest`: the value is attained by some solution
  and bounds the corresponding coordinate of every solution.
-/

namespace OMA.S_oeis_a078173

/-- `(r, s, t)` is a positive integer solution of `r*s*t = n*(r+s+t)` with `r <= s <= t`. -/
def Sol (n r s t : ℕ) : Prop :=
  0 < r ∧ r ≤ s ∧ s ≤ t ∧ r * s * t = n * (r + s + t)

/-- For every `n >= 1`: the largest `t` over all solutions is `n*(n+2)` and the largest `s`
is `2*n`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      IsGreatest {t : ℕ | ∃ r s : ℕ, Sol n r s t} (n * (n + 2)) ∧
      IsGreatest {s : ℕ | ∃ r t : ℕ, Sol n r s t} (2 * n) := by
  sorry

end OMA.S_oeis_a078173
