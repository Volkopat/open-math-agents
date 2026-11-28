import Mathlib

/-!
# A081601: numbers m such that 3 does not divide Sum_{k=0..m} binomial(2k,k)

Source: https://oeis.org/A081601 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A081601 (Benoit Cloitre, Apr 22 2003), offset 1: numbers m such that 3 does not divide
Sum_{k=0..m} binomial(2k,k) = A006134(m). Data
0, 3, 9, 12, 27, 30, 36, 39, 81, 84, 90, 93, 108, 111, 117, 120, 243, 246, 252, 255, 270, ...

Formula section, from Ilya Gutkovskiy, Jul 23 2017:
G.f.: (x/(1 - x))*Sum_{k>=0} 3^(k+1)*x^(2^k)/(1 + x^(2^k)) (conjecture).
(The entry also says: Apparently a(n) = 3*A005836(n).)

Formalization notes.
* `a n` is the n-th term (offset 1) of the increasing sequence of all m >= 0 such that 3 does
  not divide Sum_{k=0..m} binomial(2k,k): `Nat.nth` of this predicate at the index n - 1.
* The coefficient of x^n in the conjectured generating function is
  Sum_{k>=0} 3^(k+1) * b_k(n-1), where b_k(j) = floor(j / 2^k) mod 2 is the binary digit k of j.
  Reason: x^(2^k)/(1 + x^(2^k)) = Sum_{i>=1} (-1)^(i-1) x^(i*2^k), the factor 1/(1 - x) gives the
  partial sums, and Sum_{i>=1, i*2^k <= j} (-1)^(i-1) = floor(j/2^k) mod 2; the factor x moves
  the index from j to n = j + 1. The digits b_k(n-1) are 0 for k >= n, so the sum over k is the
  finite sum over k < n.
* `main` says that a(n) is equal to this coefficient for each n >= 1.
-/

namespace OMA.S_oeis_a081601

/-- A081601(n): the n-th number m ≥ 0 such that 3 does not divide Sum_{k=0..m} C(2k, k). -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.nth (fun m => ¬ 3 ∣ ∑ k ∈ Finset.range (m + 1), (2 * k).choose k) (n - 1)

/-- a(n) is the coefficient of x^n in (x/(1 - x)) * Sum_{k>=0} 3^(k+1) x^(2^k)/(1 + x^(2^k)). -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    a n = ∑ k ∈ Finset.range n, 3 ^ (k + 1) * ((n - 1) / 2 ^ k % 2) := by
  sorry

end OMA.S_oeis_a081601
