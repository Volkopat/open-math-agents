import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Ring.Parity

namespace OMA.S_oeis_a242533

/-- A permutation `σ` of `Fin m` represents a cyclic arrangement of `{1, ..., m}` where
every pair of cyclically adjacent elements has coprime difference and sum. -/
def IsValidCycle (m : ℕ) (σ : Equiv.Perm (Fin m)) : Prop :=
  ∀ i : Fin m,
    let j : Fin m := ⟨(i.val + 1) % m, Nat.mod_lt _ (Nat.pos_of_ne_zero (Fin.pos i).ne')⟩
    let a : ℕ := (σ i).val + 1
    let b : ℕ := (σ j).val + 1
    Nat.Coprime (Int.natAbs ((a : ℤ) - (b : ℤ))) (a + b)

/-- Two permutations of `Fin m` represent the same undirected cyclic arrangement if one is
a cyclic shift or reversal of the other. -/
def CyclicEquiv (m : ℕ) (σ τ : Equiv.Perm (Fin m)) : Prop :=
  ∃ k : ℕ, (∀ i : Fin m, τ i = σ ⟨(i.val + k) % m, Nat.mod_lt _ (Fin.pos i)⟩) ∨
    (∀ i : Fin m, τ i = σ ⟨(k + m - 1 - i.val) % m, Nat.mod_lt _ (Fin.pos i)⟩)

/-- `NPC(m)` (OEIS A242533): the number of undirected cyclic arrangements of `{1, ..., m}`
such that the difference of any two neighbors is coprime to their sum. -/
noncomputable def NPC (m : ℕ) : ℕ :=
  letI := Classical.decPred (IsValidCycle m)
  letI := Classical.decRel (fun x y : {σ : Equiv.Perm (Fin m) // IsValidCycle m σ} =>
    CyclicEquiv m x.1 y.1)
  (Finset.univ.image (fun x : {σ : Equiv.Perm (Fin m) // IsValidCycle m σ} =>
    Finset.univ.filter (fun y : {σ : Equiv.Perm (Fin m) // IsValidCycle m σ} =>
      CyclicEquiv m x.1 y.1))).card

/-- Conjecture (OEIS A242533): `NPC(m) = 0` for all odd `m`. -/
theorem main : ∀ m : ℕ, Odd m → NPC m = 0 := by
  sorry

end OMA.S_oeis_a242533
