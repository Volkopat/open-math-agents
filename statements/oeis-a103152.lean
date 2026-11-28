import Mathlib

/-!
# OEIS A103152: divisibility by three

Source: https://oeis.org/A103152 (OEIS Foundation, CC BY-SA 4.0).
Credit: @kumagi

For positive `n`, the term is the least odd number with exactly `n`
representations as `2p + q` for odd primes `p` and `q`, or zero when no
such odd number exists. Each admissible `p` determines one `q`.

The original conjecture excludes indices 2, 3, and 4 from divisibility by
three. The source also reports McNeil's counterexample at index 23.
-/

namespace OMA.S_oeis_a103152

def representations (m : ℕ) : ℕ :=
  ((Finset.range (m / 2 + 1)).filter fun p =>
    p.Prime ∧ Odd p ∧ (m - 2 * p).Prime ∧ Odd (m - 2 * p)).card

noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | Odd m ∧ representations m = n}

theorem main : ∀ n : ℕ, 1 ≤ n → n ≠ 2 → n ≠ 3 → n ≠ 4 → 3 ∣ a n := by
  sorry

end OMA.S_oeis_a103152
