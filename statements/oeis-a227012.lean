import Mathlib

/-!
# OEIS A227012

Source: https://oeis.org/A227012 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Haruzame0

a(n) is the floor of the harmonic mean of the integers from (n - 1)^3 + 1
through n^3. For n = 1 that range is the singleton {1}.

Franck Maminirina Ramaharo conjectured
a(n) = (2*n^3 - 3*n^2 + n + 2)/2 + floor(max(0, n - 3)/4).
In Nat arithmetic the second term is (n - 3) / 4, which is 0 for n < 3.
-/

namespace OMA.S_oeis_a227012

def cube (n : ℕ) : ℕ := n ^ 3

noncomputable def raw (n : ℕ) : ℝ :=
  let lo := cube (n - 1) + 1
  let hi := cube n
  let count : ℝ := (hi - lo + 1 : ℕ)
  let denom : ℝ := ∑ k ∈ Finset.Icc lo hi, (1 / (k : ℝ))
  count / denom

def predicted (n : ℕ) : ℕ :=
  (2 * n ^ 3 - 3 * n ^ 2 + n + 2) / 2 + (n - 3) / 4

theorem main : ∀ n : ℕ, 0 < n → Nat.floor (raw n) = predicted n := by
  sorry

end OMA.S_oeis_a227012
