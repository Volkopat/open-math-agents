import Mathlib

/-!
# A091508: Least k such that b(k) = 1, where b(1) = n and b(k+1) = b(k)+k+1 if gcd(k+1, b(k)) = 1 or else b(k)/gcd(k+1, b(k)).

Source: https://oeis.org/A091508
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A091508 (Benoit Cloitre, Mar 03 2004): a(n) always
exists. That means sequence (b(k)) becomes ultimately regular for any n, i.e. there is always k0
such that b(k0) = 1.

Conventions:
* The sequence has offset 1 (data 1, 2, 111, 7, 5, 3, 25, 22, 25, 111, 111, 4, ...).
* The sequence b is defined by b(1) = n and b(k+1) = b(k) + k + 1 if gcd(k+1, b(k)) = 1, and
  b(k+1) = b(k)/gcd(k+1, b(k)) otherwise (an exact division). The helper `b n j` is b(j+1), so
  that the recursion starts at j = 0; b(k+1) is obtained from b(k) with k + 1 = j + 2.
* `a(n) always exists` is the statement that for every n >= 1 some term of the sequence b equals
  1.
-/

namespace OMA.S_oeis_a091508

/-- `b n j` is the term b(j+1) of the sequence b(1) = n, b(k+1) = b(k) + k + 1 if
gcd(k+1, b(k)) = 1 and b(k+1) = b(k)/gcd(k+1, b(k)) otherwise. -/
def b (n : ℕ) : ℕ → ℕ
  | 0 => n
  | j + 1 => if Nat.gcd (j + 2) (b n j) = 1 then b n j + (j + 2)
      else b n j / Nat.gcd (j + 2) (b n j)

/-- The conjecture recorded in A091508. -/
theorem main : ∀ n : ℕ, 0 < n → ∃ j : ℕ, b n j = 1 := by
  sorry

end OMA.S_oeis_a091508
