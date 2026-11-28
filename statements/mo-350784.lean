import Mathlib

/-!
# Is `|{k^{k+1} + (k+1)^k mod p : k = 0, …, p-1}| = (1 - e^{-1}) p + O(√p)`?

Source: https://mathoverflow.net/questions/350784 (Zhi-Wei Sun, CC BY-SA 4.0).

For each prime `p` let `w_p = |{k^{k+1} + (k+1)^k (mod p) : k = 0, …, p - 1}|`, the number of
residue classes modulo `p` hit by `k^{k+1} + (k+1)^k`. Conjecture: `w_p = (1 - e^{-1}) p + O(√p)`.
(For `p = 32452843` the asker found `w_p - (1 - e^{-1})p ≈ 5096.75` while `√p ≈ 5696.74`.)

Formalization notes:
* `w p` counts the image of `k ↦ k^{k+1} + (k+1)^k` in `ZMod p` over `k ∈ {0, …, p-1}`; the
  exponents are natural numbers (so `k = 0` gives `0^1 + 1^0 = 1`).
* `O(√p)` is stated as: some constant `C` bounds `|w_p - (1 - e^{-1})p|` by `C √p` for every
  prime `p` (finitely many small primes can always be absorbed into `C`, as `√p ≥ 1`).
* Checked numerically: `(w_p - (1 - e^{-1})p)/√p` is `-0.18, -0.21, -0.29, -0.30` for
  `p = 101, 1009, 10007, 100003`.
-/

namespace OMA.S_mo_350784

/-- `w_p`: the number of residues mod `p` of the form `k^{k+1} + (k+1)^k`, `0 ≤ k ≤ p - 1`. -/
def w (p : ℕ) : ℕ :=
  ((Finset.range p).image fun k : ℕ => ((k : ZMod p) ^ (k + 1) + ((k + 1 : ℕ) : ZMod p) ^ k)).card

/-- Sun's conjecture: `w_p = (1 - e^{-1}) p + O(√p)`. -/
theorem main : ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime →
    |(w p : ℝ) - (1 - Real.exp (-1)) * p| ≤ C * Real.sqrt p := by
  sorry

end OMA.S_mo_350784
