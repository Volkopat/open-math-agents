import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1
import Mathlib

-- Reduction Erdos64.erdos_64.R1.H1.R1.H1.R1.H2.R2.H1.R1.H1.R1
-- of step Erdos64.erdos_64.R1.H1.R1.H1.R1.H2.R2.H1.R1.H1
-- Credit: @arindale

/-!
# Splitting the non-free case by whether the two shifts commute

The step asks: when every point has a nonidentity stabilizer element in the group generated
by the two shifts `p` and `q`, find a cycle of length a power of two in the normalized
regular matching graph.

When `p` and `q` commute, `p (q x) = q (p x)` holds for every point `x`, so the set
`{x | p (q x) ≠ q (p x)}` is empty.  The hypothesis `Fintype.card X ≤ 3 * |·|` then forces
`Fintype.card X ≤ 0`, which contradicts `Nonempty X`.  Thus the commuting branch has no
models at all and is vacuously true, while every real instance lies in the noncommuting
branch.  This isolates the open content in `H2` and makes `H1` an elementary statement.
-/

namespace OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H1_R1

open SimpleGraph

/-- The commuting branch: the same conclusion, assuming `p` and `q` commute. -/
def H1 : Prop :=
  ∀ (X : Type) [Fintype X] [Nonempty X] (p q : Equiv.Perm X),
    Commute p q →
    (∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x) →
    Fintype.card X ≤ 3 * {x : X | p (q x) ≠ q (p x)}.ncard →
    Odd (Nat.card (Subgroup.closure ({p,q} : Set (Equiv.Perm X)))) →
    (∀ x : X, ∃ g ∈ Subgroup.closure ({p,q} : Set (Equiv.Perm X)), g ≠ 1 ∧ g x=x) →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ SimpleGraph.fromRel (fun u v : Bool × X =>
      u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=p u.2 ∨ v.2=q u.2))

/-- The noncommuting branch, which contains all the models: the open core. -/
def H2 : Prop :=
  ∀ (X : Type) [Fintype X] [Nonempty X] (p q : Equiv.Perm X),
    ¬ Commute p q →
    (∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x) →
    Fintype.card X ≤ 3 * {x : X | p (q x) ≠ q (p x)}.ncard →
    Odd (Nat.card (Subgroup.closure ({p,q} : Set (Equiv.Perm X)))) →
    (∀ x : X, ∃ g ∈ Subgroup.closure ({p,q} : Set (Equiv.Perm X)), g ≠ 1 ∧ g x=x) →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ SimpleGraph.fromRel (fun u v : Bool × X =>
      u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=p u.2 ∨ v.2=q u.2))

theorem main : H1 → H2 →
    OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1.H1 := by
  intro h1 h2 X _ _ p q separated density odd allFixed
  classical
  by_cases hcomm : Commute p q
  · exact h1 X p q hcomm separated density odd allFixed
  · exact h2 X p q hcomm separated density odd allFixed

end OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H1_R1
