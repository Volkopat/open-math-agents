import Mathlib

/-!
# A047618: Numbers that are congruent to {0, 2, 5} mod 8

Source: https://oeis.org/A047618
Credit: @jagong-cmu

Formalizes the conjecture of L. Edson Jeffery (Sep 02 2014) in OEIS A047618:
Conjecture: a(n)+a(n+1)+a(n+2) = 8*n-1; or a(n) = 8*(n-2)-a(n-1)-a(n-2)-1, n>3,
with a(1)=0, a(2)=2, a(3)=5.

Conventions: the offset is `1`, as in OEIS, so `a(1) = 0` is the least natural number
`k` with `k % 8 ∈ {0, 2, 5}`. We write `a n = Nat.nth P (n - 1)`, where `P` is that
property; `Nat.nth` counts from `0`, hence the shift `n - 1`. The value `a 0` is a junk
value and is never used. The first identity is stated for every `n ≥ 1`. The second form
is stated as written: the three initial values and the recurrence for every `n > 3`.
Both identities are taken in `ℤ`, so `8*n - 1` and `8*(n-2) - ...` are integer
subtractions; the indices `n - 1` and `n - 2` are natural-number subtractions, exact for
`n > 3`. The two forms are stated together, as a conjunction.
-/

namespace OMA.S_oeis_a047618

/-- `a(n)` is the `n`-th natural number (from `n = 1`) congruent to `0`, `2` or `5` mod `8`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.nth (fun k => k % 8 = 0 ∨ k % 8 = 2 ∨ k % 8 = 5) (n - 1)

/-- Jeffery's conjecture: both forms, as a conjunction. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → (a n : ℤ) + (a (n + 1) : ℤ) + (a (n + 2) : ℤ) = 8 * (n : ℤ) - 1) ∧
      (a 1 = 0 ∧ a 2 = 2 ∧ a 3 = 5 ∧
        ∀ n : ℕ, 3 < n →
          (a n : ℤ) = 8 * ((n : ℤ) - 2) - (a (n - 1) : ℤ) - (a (n - 2) : ℤ) - 1) := by
  sorry

end OMA.S_oeis_a047618
