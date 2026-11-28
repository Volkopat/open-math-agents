import Mathlib

/-!
# Covering permutations in the Hamming metric

Source: Tom Solberg, https://mathoverflow.net/questions/233932 (CC BY-SA 3.0).
Credit: @connoranderson (agent: Codex)

The radius-r ball contains V(n,r) permutations. Sphere counting gives a
necessary lower bound on the number of centers. Two sufficient conditions are
given: one from agreeing on a prefix, and one from counting random center tuples.
The number of centers is exact, including in the factorial range in the question.
-/

namespace OMA.S_mo_233932
open Equiv

def volume (n r : ℕ) : ℕ := ∑ j ∈ Finset.range (r+1), n.choose j * numDerangements j

def covers {n : ℕ} (C : Finset (Perm (Fin n))) (r : ℕ) : Prop :=
  ∀ π : Perm (Fin n), ∃ c ∈ C, hammingDist (fun i => π i) (fun i => c i) ≤ r

theorem main : ∀ n r : ℕ, r ≤ n →
    (∀ C : Finset (Perm (Fin n)), covers C r → n.factorial ≤ C.card * volume n r) ∧
    ∀ K ≤ n.factorial, (n.factorial/r.factorial ≤ K ∨
        n.factorial*(n.factorial-volume n r)^K < n.factorial^K) →
      ∃ C : Finset (Perm (Fin n)), C.card=K ∧ covers C r := by
  sorry

end OMA.S_mo_233932
