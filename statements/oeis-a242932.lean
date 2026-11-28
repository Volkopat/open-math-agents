import Mathlib

/-!
# A242932: Numbers n such that k*n/(k+n) is prime for some k.

Source: https://oeis.org/A242932
Credit: @ShoQo

Conjecture: "It is believed that numbers in A016742 (except 4) are not included in this
sequence." (Sela Fried, Mar 27 2026: "A number n belongs to this sequence iff n belongs to the
set {p+1, 2*p, p*(p+1)}, for some prime p. In particular, the conjecture regarding A016742 is
true.")

Formalization notes:
* n ≥ 1 is a term iff for some k ≥ 1, (k + n) ∣ k n and k n / (k + n) is prime
  (data: 3, 4, 6, 8, 10, ...).
* A016742 is the even squares 4 m^2 (m ≥ 0). The claim: 4 m^2 is not a term unless 4 m^2 = 4.
-/

namespace OMA.S_oeis_a242932

/-- n is a term of A242932. -/
def InSeq (n : ℕ) : Prop :=
  1 ≤ n ∧ ∃ k : ℕ, 1 ≤ k ∧ (k + n) ∣ k * n ∧ (k * n / (k + n)).Prime

theorem main : ∀ m : ℕ, 4 * m ^ 2 ≠ 4 → ¬ InSeq (4 * m ^ 2) := by
  sorry

end OMA.S_oeis_a242932
