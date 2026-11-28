import Mathlib

/-!
# A248137: Least positive integer m such that m + n divides M(m) + M(n), where M(.) is given by A001006.

Source: https://oeis.org/A248137
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A248137 (Zhi-Wei Sun, Oct 02 2014): a(n) exists for any
n > 0.

Conventions:
* The sequence has offset 1 (data 1, 1, 244, 1, 23, 4, 1, 1, 3494, 1, 68058, 4, ...).
* M(.) is the sequence A001006: the Motzkin numbers M(n) = Sum_{k=0..floor(n/2)}
  C(n,2k)*C(2k,k)/(k+1) (1, 1, 2, 4, 9, 21, 51, ...), where C(2k,k)/(k+1) is the Catalan number
  `catalan k` of Mathlib; this is the helper `M`.
* `a(n) exists` means that there is a positive integer m with the stated divisibility (then the
  least such m exists); it is stated directly as the existence of m, without defining a(n).
-/

namespace OMA.S_oeis_a248137

/-- A001006: the Motzkin numbers M(n) = Sum_{k=0..floor(n/2)} C(n,2k)*Catalan(k). -/
def M (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n / 2 + 1), n.choose (2 * k) * catalan k

/-- The conjecture recorded in A248137. -/
theorem main : ∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧ m + n ∣ M m + M n := by
  sorry

end OMA.S_oeis_a248137
