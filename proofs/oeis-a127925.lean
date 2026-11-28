import OMAStatements.S_oeis_a127925
import Mathlib

/-!
# A127925: the claimed equivalence fails at `q = 2`

`2` is a term: it is prime and, since `π(2) = 1`, there is no `i` with `1 ≤ i < π(2)`, so the
defining condition holds vacuously.  But `m = 1` satisfies `0 < m < 2` and
`2 π(2) = 2 = π(1) + π(3) = 0 + 2`, so the right-hand side of the equivalence is false.
-/

open OMA.S_oeis_a127925 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a127925.main) := by
  intro h
  have p1 : Nat.primeCounting 1 = 0 := by decide
  have p2 : Nat.primeCounting 2 = 1 := by decide
  have p3 : Nat.primeCounting 3 = 2 := by decide
  have hterm : IsTerm 2 := by
    refine ⟨Nat.prime_two, fun i hi1 hi2 => ?_⟩
    rw [p2] at hi2
    omega
  exact (h 2 (by norm_num)).mp hterm ⟨1, by norm_num, by norm_num, by rw [p2, p1, p3]⟩
