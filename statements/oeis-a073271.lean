import Mathlib

/-!
# A073271: a(n) = floor( prime(n)*prime(n+2) / prime(n+1) ).

Source: https://oeis.org/A073271
Credit: @azmiozgen

Conjectures (from the entry):
1. a(n) is even except for a(1)=3, a(3)=7 and a(8)=23.
2. (Gionata Neri, May 31 2015) when a(n) = a(n+1) then A001223(n+1) = A001223(n) + A001223(n+2).

Formalization notes:
* prime(n) is the n-th prime with prime(1) = 2 (offset 1), i.e. `Nat.nth Nat.Prime (n - 1)`.
* A001223(n) = prime(n+1) - prime(n), the n-th prime gap.
* Conjecture 1 is stated as: for n >= 1, a(n) is odd exactly when n is 1, 3 or 8.
* The statement is the conjunction of both conjectures, each for all n >= 1.
* Controls: a(1..24) = 3, 4, 7, 8, 14, 14, 20, 23, 24, 34, 34, 38, 44, 48, 52, 54, 64, 64, 68,
  76, 76, 84, 90, 92, as in the entry; among n <= 40 the odd values occur at n = 1, 3, 8.
-/

namespace OMA.S_oeis_a073271

/-- The `n`-th prime, `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- A073271(n) = floor(prime(n) * prime(n+2) / prime(n+1)). -/
noncomputable def a (n : ℕ) : ℕ := prime n * prime (n + 2) / prime (n + 1)

/-- A001223(n) = prime(n+1) - prime(n). -/
noncomputable def gap (n : ℕ) : ℕ := prime (n + 1) - prime n

/-- Both conjectures of the entry. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → (Odd (a n) ↔ n = 1 ∨ n = 3 ∨ n = 8)) ∧
    (∀ n : ℕ, 1 ≤ n → a n = a (n + 1) → gap (n + 1) = gap n + gap (n + 2)) := by
  sorry

end OMA.S_oeis_a073271
