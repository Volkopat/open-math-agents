import Mathlib

/-!
# A165886: a(n) = A165641(n+1)/A165641(n).

Source: https://oeis.org/A165886
Credit: @avivorly

A165886 (offset 0): `a(n) = A165641(n+1)/A165641(n)`: 1, 6, 1, 60, 1, 42, 1, 120, 1, 66, 1, 5460, ...
where `A165641(n) = A091137(n)/A001316(n)`, `A091137(n) = Product_{2 <= p <= n+1, p prime} p^floor(n/(p-1))`
(the Hirzebruch numbers) and `A001316(n) = 2^(number of 1's in the binary expansion of n)` (Gould's sequence).

Conjecture (in the entry, Paul Curtz's sequence; R. J. Mathar, Jul 04 2011: correct at least up to `n <= 2000`):
`a(n)/A141459(n+1) = A006519(n+1)`,
where `A141459(m) = Product_{p - 1 divides m} p` over the odd primes `p`, and `A006519(m)` is the highest power of 2
dividing `m`.

Conventions:
- The ratios are taken in `ℚ`, exactly as written (no integrality is assumed).
- `A091137 n` is the product over the primes `p ≤ n + 1`. `A141459 m` is the product over the odd primes `p ≤ m + 1`
  with `(p - 1) ∣ m`; for `m ≥ 1` every odd prime with `(p - 1) ∣ m` is `≤ m + 1`, so this is the full product
  (it is only used at `m = n + 1 ≥ 1`).
- `A006519 m = 2 ^ (2-adic valuation of m)`; the number of 1's in the binary expansion is the digit sum
  `(Nat.digits 2 n).sum`.
- The conjecture is stated for every `n ≥ 0` (the offset of A165886).
-/

namespace OMA.S_oeis_a165886

/-- A091137 (the Hirzebruch numbers): `Product_{2 <= p <= n+1, p prime} p^floor(n/(p-1))`. -/
def A091137 (n : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (n + 2)).filter Nat.Prime, p ^ (n / (p - 1))

/-- A001316 (Gould's sequence): `2^(number of 1's in the binary expansion of n)`. -/
def A001316 (n : ℕ) : ℕ := 2 ^ (Nat.digits 2 n).sum

/-- A165641: `A091137(n) / A001316(n)`, in `ℚ`. -/
noncomputable def A165641 (n : ℕ) : ℚ := (A091137 n : ℚ) / (A001316 n : ℚ)

/-- A165886: `a(n) = A165641(n+1) / A165641(n)`, in `ℚ`. -/
noncomputable def a (n : ℕ) : ℚ := A165641 (n + 1) / A165641 n

/-- A141459: the product of the odd primes `p` with `(p - 1) ∣ m` (over `p ≤ m + 1`). -/
def A141459 (m : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (m + 2)).filter (fun p => p.Prime ∧ p ≠ 2 ∧ (p - 1) ∣ m), p

/-- A006519: the highest power of 2 dividing `m`. -/
def A006519 (m : ℕ) : ℕ := 2 ^ padicValNat 2 m

theorem main : ∀ n : ℕ, a n / (A141459 (n + 1) : ℚ) = (A006519 (n + 1) : ℚ) := by
  sorry

end OMA.S_oeis_a165886
