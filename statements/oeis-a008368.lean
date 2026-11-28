import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a008368

/-- A single step in the 3D face-centered cubic (f.c.c.) lattice: one coordinate changes by `0`
and the other two change by `±1`. -/
def IsFccStep (p q : ℤ × ℤ × ℤ) : Prop :=
  let dx := (q.1 - p.1).natAbs
  let dy := (q.2.1 - p.2.1).natAbs
  let dz := (q.2.2 - p.2.2).natAbs
  (dx = 1 ∧ dy = 1 ∧ dz = 0) ∨ (dx = 1 ∧ dy = 0 ∧ dz = 1) ∨ (dx = 0 ∧ dy = 1 ∧ dz = 1)

/-- `FccReachable k p` means `p` can be reached from the origin `(0, 0, 0)` in `k` f.c.c. steps. -/
inductive FccReachable : ℕ → (ℤ × ℤ × ℤ) → Prop
  | zero : FccReachable 0 (0, 0, 0)
  | step {k : ℕ} {p q : ℤ × ℤ × ℤ} : FccReachable k p → IsFccStep p q → FccReachable (k + 1) q

/-- Exact f.c.c. step distance `n` from the origin: reachable in `n` steps and not in fewer. -/
def AtFccDist (n : ℕ) (p : ℤ × ℤ × ℤ) : Prop :=
  FccReachable n p ∧ ∀ k < n, ¬ FccReachable k p

/-- OEIS A008368(n): Number of `O_h`-orbits (canonical representatives `0 ≤ x ≤ y ≤ z` up to
coordinate permutations and sign changes) of points at exact distance `n` from the origin in
the f.c.c. lattice. -/
noncomputable def A008368 (n : ℕ) : ℕ :=
  Set.ncard { t : ℕ × ℕ × ℕ |
    t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧ AtFccDist n ((t.1 : ℤ), (t.2.1 : ℤ), (t.2.2 : ℤ)) }

/-- Conjecture (Simon Plouffe, 1992; OEIS A008368): The ordinary generating function of
`A008368(n)` equals `(1 - x^5) / ((1 - x) * (1 - x^2)^2 * (1 - x^3))`, i.e.
`(1 - X) * (1 - X^2)^2 * (1 - X^3) * (∑_{n ≥ 0} A008368(n) * X^n) = 1 - X^5` in `ℤ⟦X⟧`. -/
theorem main :
    ((1 - PowerSeries.X) * (1 - PowerSeries.X ^ 2) ^ 2 * (1 - PowerSeries.X ^ 3)) *
      PowerSeries.mk (fun n => (A008368 n : ℤ)) =
      1 - PowerSeries.X ^ 5 := by
  sorry

end OMA.S_oeis_a008368
