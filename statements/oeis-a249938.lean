import Mathlib

/-!
# OEIS A249938

Even-indexed Fubini (ordered Bell) numbers `a(n) = A000670(2 * n) = Sum_{k = 0..2*n} k! * S(2 * n, k)`,
with e.g.f. `Sum_{k >= 0} exp(k^2 * x) / 2^(k + 1)`.
(First terms: `1, 3, 75, 4683, 545835, 102247563, ...`)

Conjectures (Federico Provvedi, Nov 07 2020):
1. For `n > 1`, `a(n + 1) - a(n) ≡ 0 (mod m)` for all `n > 1` if and only if `m` divides `288`.
2. For every prime `p`, the sequence `a(n) (mod p)` for `n >= 1` is purely periodic, and its
   minimal period equals the number of nonzero quadratic residues modulo `p`
   (`1` for `p = 2`, `(p - 1) / 2` for odd primes `p`).
-/

namespace OMA.S_oeis_a249938

/-- Stirling numbers of the second kind `S(n, k)`. -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | _ + 1, 0 => 0
  | 0, _ + 1 => 0
  | n + 1, k + 1 => (k + 1) * stirling2 n (k + 1) + stirling2 n k

/-- Sequence A249938: `a(n) = Sum_{k = 0..2*n} k! * S(2 * n, k)`. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2 * n + 1), k.factorial * stirling2 (2 * n) k

/-- Number of nonzero quadratic residues modulo `p`. -/
def numNonzeroQR (p : ℕ) : ℕ :=
  ((Finset.range p).image (fun x => x ^ 2 % p) \ {0}).card

theorem main :
    (∀ m : ℕ, (∀ n : ℕ, 1 < n → a (n + 1) ≡ a n [MOD m]) ↔ m ∣ 288) ∧
    (∀ p : ℕ, p.Prime →
      (∀ n : ℕ, 1 ≤ n → a (n + numNonzeroQR p) ≡ a n [MOD p]) ∧
      (∀ d : ℕ, 1 ≤ d → (∀ n : ℕ, 1 ≤ n → a (n + d) ≡ a n [MOD p]) →
        numNonzeroQR p ∣ d)) := by
  sorry

end OMA.S_oeis_a249938
