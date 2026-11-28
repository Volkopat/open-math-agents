import Mathlib

/-!
# A033627: 0-additive sequence: not the sum of any previous pair

Source: https://oeis.org/A033627
Credit: @avivorly

A033627 is the 0-additive sequence (the Stöhr sequence): each term is not the sum of any previous pair. Its data
begins 1, 2, 4, 7, 10, 13, 16, 19, ...

Conjecture (Ya-Ping Lu, Oct 19 2021, in the entry): a(n+1) is the number of distinct numbers of steps required for
the last n digits of integers to repeat themselves by iterating the map m -> m^2 + 1.

Conventions:
- The sequence (offset 1) is defined greedily from its name, not from the closed form in the entry: `a(1) = 1`, and
  `a(n+1)` is the least integer `k > a(n)` that is not `a(i) + a(j)` for indices `1 ≤ i < j ≤ n`. A pair is two
  distinct earlier terms: allowing a term twice would exclude `2 = 1 + 1`, against the data `1, 2, 4, ...`; the entry's
  Mathematica program also uses the two-element subsets. `A033627 0 = 0` is only a seed: it is not a term and never
  enters a pair, and it makes `a(1)` the least positive integer.
- The last `n` digits of an integer are its residue modulo `10^n`, an element `x` of `ZMod (10^n)`, and the map
  `f(m) = m^2 + 1` acts on these residues (`sq1`). The number of steps required for `x` to repeat itself is `rho x`:
  the least `t ≥ 1` such that `f^t(x)` is one of the earlier values `x, f(x), ..., f^(t-1)(x)` (the length of the
  tail plus the length of the cycle). For `n = 1` the orbit of `0` is `0, 1, 2, 5, 6, 7, 0`, so `rho 0 = 6`; the
  values of `rho` on `ZMod 10` are `6` and `7`, two of them, and `a(2) = 2`. This reading gives `a(n+1)` for
  `n = 1, ..., 10`.
- The conjecture is stated for every `n ≥ 1`.
-/

namespace OMA.S_oeis_a033627

/-- A033627 with offset 1: `A033627 (n + 1)` is the least `k > A033627 n` that is not `A033627 i + A033627 j` for
any indices `1 ≤ i < j ≤ n`. The seed `A033627 0 = 0` is not a term. -/
noncomputable def A033627 : ℕ → ℕ
  | 0 => 0
  | n + 1 => sInf {k : ℕ | A033627 n < k ∧
      ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ n → A033627 i + A033627 j ≠ k}
decreasing_by all_goals omega

/-- The map `m ↦ m ^ 2 + 1` on residues modulo `N`. -/
def sq1 (N : ℕ) (m : ZMod N) : ZMod N := m ^ 2 + 1

/-- The number of steps for `x` to repeat itself under `f = sq1 N`: the least `t ≥ 1` such that `f^[t] x` equals
`f^[s] x` for some `s < t`. -/
noncomputable def rho (N : ℕ) (x : ZMod N) : ℕ :=
  sInf {t : ℕ | 1 ≤ t ∧ ∃ s < t, (sq1 N)^[t] x = (sq1 N)^[s] x}

theorem main : ∀ n ≥ 1,
    A033627 (n + 1) = ((Finset.univ : Finset (ZMod (10 ^ n))).image (rho (10 ^ n))).card := by
  sorry

end OMA.S_oeis_a033627
