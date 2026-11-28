import Mathlib

/-!
# Infinitude of the record positions of A380528

Source: https://oeis.org/A380530, with A380528, A380459, A276086 and A349394.

A prime power p^(e+1) dividing n contributes p^e copies of the primorial
digits of n/p^(e+1). The first radix whose column sum reaches that radix is
A380528(n), with value one when every column is below its radix. This is the
smallest prime r such that r^r divides A380459(n).

The entry asks whether its sequence of strict record positions is infinite.
It also asks separate questions about squarefreeness, decimal endings and the
number of prime factors of those positions.
-/
namespace OMA.S_oeis_a380530

noncomputable def radix (j : ℕ) := Nat.nth Nat.Prime j
noncomputable def place (j : ℕ) := ∏ i ∈ Finset.range j, radix i
noncomputable def digit (n j : ℕ) := (n / place j) % radix j

noncomputable def column (n j : ℕ) : ℕ :=
  ∑ p ∈ n.primeFactors, ∑ e ∈ Finset.range (n.factorization p),
    p^e * digit (n/p^(e+1)) j

noncomputable def value (n : ℕ) : ℕ := by
  classical
  exact if h : ∃ j, radix j ≤ column n j then radix (Nat.find h) else 1

def records : Set ℕ := {n | 0 < n ∧ ∀ i, 0 < i → i < n → value i < value n}

theorem main : records.Infinite := by
  sorry
end OMA.S_oeis_a380530
