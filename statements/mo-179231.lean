import Mathlib

/-!
# Irreducibility of X^m − g(Y)

Question by r_l, https://mathoverflow.net/questions/179231 (CC BY-SA 3.0).
Vesselin Dimitrov gave the Vahlen–Capelli criterion in the source comments.
Credit: @connoranderson

The iterated polynomial ring is ℂ[Y][X]. The coefficient g is arbitrary,
including zero and constant polynomials.
-/

namespace OMA.S_mo_179231
open Polynomial
open scoped Polynomial

theorem main : ∀ (m : ℕ), 2 ≤ m → ∀ g : ℂ[X],
    Irreducible (X ^ m - C g) ↔
      ∀ p : ℕ, p.Prime → p ∣ m → ∀ b : ℂ[X], b ^ p ≠ g := by
  sorry

end OMA.S_mo_179231
