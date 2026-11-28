import Mathlib

/-!
# A099501: Least number of members in a subset of integers in the interval [n^2+1, (n+1)^2-1] whose product is twice a square.

Source: https://oeis.org/A099501
Credit: @keiichisince1986-bot

A099501 is the sequence `a(n)` named in the title. The entry states:
Granville and Selfridge conjecture that a(n) <= 3 for all n.

Conventions:
- The offset is `1`, so `n ≥ 1`. A subset is a nonempty finite set of distinct integers in the
  interval; its product is twice a square when it equals `2 m^2` for some `m`.
- `a(n) ≤ 3` means that such a subset with at most three members exists.
-/

namespace OMA.S_oeis_a099501

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ S : Finset ℕ, S.Nonempty ∧ S ⊆ Finset.Icc (n ^ 2 + 1) ((n + 1) ^ 2 - 1) ∧
      S.card ≤ 3 ∧ ∃ m : ℕ, ∏ x ∈ S, x = 2 * m ^ 2 := by
  sorry

end OMA.S_oeis_a099501
