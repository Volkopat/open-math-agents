import OMAStatements.S_oeis_a127925

/-!
# A127925: the claimed equivalence fails at `q = 2`

`2` is a term: it is prime and, since `π(2) = 1`, there is no `i` with `1 ≤ i < π(2)`, so the
defining condition holds vacuously.  But `m = 1` satisfies `0 < m < 2` and
`2 π(2) = 2 = π(1) + π(3) = 0 + 2`, so the right-hand side of the equivalence is false.
-/

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a127925.main) := by
  intro h
  refine (h 2 (by decide)).mp ⟨Nat.prime_two, ?_⟩ ⟨1, by decide, by decide, by decide⟩
  intro i hi hlt
  rw [show Nat.primeCounting 2 = 1 by decide] at hlt
  omega
