import Mathlib

/-!
# A258170: T(n,k) = (1/k!) * Sum_{i=0..k} (-1)^(k-i) * C(k,i) * A185651(n,i); triangle T(n,k), n >= 0, 0 <= k <= n, read by rows.

Source: https://oeis.org/A258170
Credit: @agchua

Petros Hadjicostas (Sep 07 2018), in the formula section of A258170:
  Conjecture 1: T(n,k) = Stirling2(n,k) for k >= 1 and k <= n <= 2*k - 1.
  Conjecture 2: T(n,k) = Stirling2(n,k) for k >= 2 and n prime >= 2.
  Here, Stirling2(n,k) = A008277(n,k).
A185651 is defined by its name line: A(n,k) = Sum_{d|n} phi(d)*k^(n/d), n >= 0, k >= 0 (the
empty sum gives A(0,k) = 0). Stirling2 is Mathlib's `Nat.stirlingSecond`, the Stirling numbers
of the second kind (A008277). T is computed in ℚ. Both conjectures are stated on the triangle,
0 ≤ k ≤ n, with the bounds on k and n exactly as printed.
-/

namespace OMA.S_oeis_a258170

/-- A185651(n,k) = Sum_{d|n} phi(d)*k^(n/d). -/
def A185651 (n k : ℕ) : ℕ := ∑ d ∈ n.divisors, Nat.totient d * k ^ (n / d)

/-- T(n,k) = (1/k!) * Sum_{i=0..k} (-1)^(k-i) * C(k,i) * A185651(n,i). -/
def T (n k : ℕ) : ℚ :=
  (1 / (k.factorial : ℚ)) * ∑ i ∈ Finset.range (k + 1),
    (-1 : ℚ) ^ (k - i) * (k.choose i : ℚ) * (A185651 n i : ℚ)

/-- Conjectures 1 and 2: T(n,k) = Stirling2(n,k) for 1 ≤ k ≤ n ≤ 2k - 1, and for 2 ≤ k ≤ n
with n prime. -/
theorem main :
    (∀ n k : ℕ, 1 ≤ k → k ≤ n → n ≤ 2 * k - 1 → T n k = (Nat.stirlingSecond n k : ℚ)) ∧
    (∀ n k : ℕ, 2 ≤ k → k ≤ n → n.Prime → T n k = (Nat.stirlingSecond n k : ℚ)) := by
  sorry

end OMA.S_oeis_a258170
