import Mathlib

/-!
# A206824: Number of solutions (n,k) of s(k) = s(n) (mod n), where 1 <= k < n and s(k) = k(k+1)/2.

Source: https://oeis.org/A206824
Credit: @esracummings31-blip

Conjectures (Michael De Vlieger, Sep 22 2017):
* a(p^e) = 1, with e > 0;
* a(A002110(n)) = 2^(n-1) and a(A002110(n)/2) = 2^(n-1) - 1 for n > 0;
* a(n) = 2^(A001221(n) - 1) for n even, a(n) = 2^A001221(n) - 1 for n odd.

Conventions: the sequence has offset 2, so the general formulas are stated for n >= 2.
A001221(n) is the number of distinct primes dividing n; A002110(n) is the product of the
first n primes.
-/

namespace OMA.S_oeis_a206824

/-- The triangular number s(k) = k(k+1)/2. -/
def s (k : ℕ) : ℕ := k * (k + 1) / 2

/-- A206824(n): the number of 1 <= k < n with s(k) = s(n) (mod n). -/
def a (n : ℕ) : ℕ := ((Finset.Ico 1 n).filter (fun k => s k ≡ s n [MOD n])).card

/-- A001221(n): number of distinct primes dividing n. -/
def A001221 (n : ℕ) : ℕ := n.primeFactors.card

/-- A002110(n): product of the first n primes (primorial numbers). -/
noncomputable def A002110 (n : ℕ) : ℕ := ∏ i ∈ Finset.range n, Nat.nth Nat.Prime i

theorem main :
    (∀ p e : ℕ, p.Prime → 0 < e → a (p ^ e) = 1) ∧
    (∀ n : ℕ, 0 < n → a (A002110 n) = 2 ^ (n - 1) ∧ a (A002110 n / 2) = 2 ^ (n - 1) - 1) ∧
    (∀ n : ℕ, 2 ≤ n → Even n → a n = 2 ^ (A001221 n - 1)) ∧
    (∀ n : ℕ, 2 ≤ n → Odd n → a n = 2 ^ A001221 n - 1) := by
  sorry

end OMA.S_oeis_a206824
