import Mathlib

/-!
# Prime-order cyclic groups and homotopy groups of spheres

The explicit conjecture in the question excludes the cyclic group of every prime order
greater than three from the homotopy groups of spheres.

[MathOverflow question](https://mathoverflow.net/questions/377545/which-finite-abelian-groups-arent-homotopy-groups-of-spheres)
-/

namespace OMA.S_mo_377545

abbrev Sphere (n : ℕ) :=
  ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

theorem main :
    ∀ p : ℕ, Nat.Prime p → 3 < p →
      ∀ (n k : ℕ) (x : Sphere n),
        ¬ Nonempty (HomotopyGroup.Pi (k + 1) (Sphere n) x ≃* Multiplicative (ZMod p)) := by
  sorry

end OMA.S_mo_377545
