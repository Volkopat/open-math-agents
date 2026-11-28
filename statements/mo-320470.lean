import Mathlib

/-!
# `(p-1)²` divides a Legendre-symbol determinant

Source: https://mathoverflow.net/questions/320470 (CC BY-SA 4.0).

For an odd prime `p` and `c, d ∈ ℤ` let `[c, d]_p = det[((i² + cij + dj²)/p)]_{0 ≤ i, j ≤ p-1}` (Legendre
symbols). Conjecture 1 (Z.-W. Sun, verified for `p < 750`): if `(d/p) = -1` then `(p-1)² ∣ [c, d]_p`.

We state Conjecture 1. (The extension to Jacobi symbols and Conjecture 2 are not stated.)

Formalization notes:
* Indices are `Fin p`, cast to `ℤ`; `legendreSym p` needs the instance `Fact p.Prime`.
* Checked independently for all odd primes `p ≤ 23` and all residues `c, d` with `(d/p) = -1`
  (727 cases).
-/

namespace OMA.S_mo_320470

/-- For an odd prime `p` and `(d/p) = -1`, `(p-1)² ∣ det[((i² + cij + dj²)/p)]`. -/
theorem main : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ c d : ℤ, legendreSym p d = -1 →
    ((p : ℤ) - 1) ^ 2 ∣ (Matrix.of (fun i j : Fin p =>
      legendreSym p (((i : ℕ) : ℤ) ^ 2 + c * ((i : ℕ) : ℤ) * ((j : ℕ) : ℤ) + d * ((j : ℕ) : ℤ) ^ 2))).det := by
  sorry

end OMA.S_mo_320470
