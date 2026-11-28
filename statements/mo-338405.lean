import Mathlib

/-!
# The size of a nonsingular interval box over a prime field

Source: fil, https://mathoverflow.net/questions/338405 (CC BY-SA 4.0).
Credit: @connoranderson.

An entry perturbation independently ranges over the initial interval
0,…,L−1 in every entry. In every positive dimension d, no translate
can consist entirely of nonsingular matrices when p ≤ L^d. A nonsingular
translate exists for L=1 and whenever d! L^d < p. These matching
exponents give Θ_d(p^(1/d)) for the largest possible side, in particular
Θ(√p) for the original 2×2 problem. The lower construction extends the
half-identity example in the source.
-/
namespace OMA.S_mo_338405
open Matrix
abbrev Mat (d : ℕ) (R : Type*) := Matrix (Fin d) (Fin d) R
def offset {d L p : ℕ} (e : Mat d (Fin L)) : Mat d (ZMod p) := .of fun i j => (e i j).val

theorem main : ∀ (p d L : ℕ) [Fact p.Prime], 0 < d → 0 < L →
    ((p ≤ L^d → ∀ M : Mat d (ZMod p), ∃ e : Mat d (Fin L), (M+offset e).det=0) ∧
     (L=1 ∨ d.factorial*L^d < p → ∃ M : Mat d (ZMod p),
       ∀ e : Mat d (Fin L), (M+offset e).det≠0)) := by
  sorry
end OMA.S_mo_338405
