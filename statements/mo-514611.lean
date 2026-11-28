import Mathlib

/-!
# Galois group of x(x-1)⋯(x-p+1)+1

Source: https://mathoverflow.net/questions/514611 (CC BY-SA 4.0).

For a prime `p` let `f_p(x) = x(x-1)⋯(x-p+1) + 1 ∈ ℚ[x]`. Reduction mod `p` shows `f_p` is
irreducible, and computation gives `Gal(f_p/ℚ) ≅ S_p` for every prime `p < 100`.
The question asks whether this holds for every prime `p`; `main` states the expected yes.
The Galois group is `Polynomial.Gal`, and `S_p` is the symmetric group on `p` letters.
-/

namespace OMA.S_mo_514611

open Polynomial

/-- `x(x-1)⋯(x-p+1) + 1` over `ℚ`. -/
noncomputable def f (p : ℕ) : ℚ[X] :=
  (∏ i ∈ Finset.range p, (X - C (i : ℚ))) + 1

theorem main : ∀ p : ℕ, p.Prime → Nonempty ((f p).Gal ≃* Equiv.Perm (Fin p)) := by
  sorry

end OMA.S_mo_514611
