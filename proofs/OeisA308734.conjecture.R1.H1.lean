import OMAReductions.R_OeisA308734_conjecture_R1
import Mathlib.NumberTheory.SumTwoSquares

/-!
# Proof of `OeisA308734.conjecture.R1.H1`

Proves that if `(2 ^ a * 3 ^ b) ^ 2 + (2 ^ c * 5 ^ d) ^ 2 ≤ n` and every prime factor `q ≡ 3 (mod 4)`
of `m = n - (2 ^ a * 3 ^ b) ^ 2 - (2 ^ c * 5 ^ d) ^ 2` has even `q`-adic valuation, then
`OeisA308734.A n` holds.

By the Fermat–Euler two-square theorem (`Nat.eq_sq_add_sq_iff`), `m = x ^ 2 + y ^ 2` for some
`x, y : ℕ`, giving `n = (2 ^ a * 3 ^ b) ^ 2 + (2 ^ c * 5 ^ d) ^ 2 + x ^ 2 + y ^ 2`.
-/

theorem OMA.solution : OMA.R_OeisA308734_conjecture_R1.H1 := by
  intro n a b c d hle hodd
  obtain ⟨x, y, hm⟩ := Nat.eq_sq_add_sq_iff.mpr hodd
  exact ⟨a, b, c, d, x, y, by omega⟩
