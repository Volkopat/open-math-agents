import OMAReductions.R_CunninghamChain_infinitely_many_secondKind_chains_R1
import Mathlib

-- Step CunninghamChain.infinitely_many_secondKind_chains.R1.H1: hypothesis H1 of reduction CunninghamChain.infinitely_many_secondKind_chains.R1
-- Credit: @ivillar. Every prime p > 3 with p = 2 (mod 3) starts a second-kind chain of exact length one, since 3 divides 2p - 1 > 3; Dirichlet's theorem (Mathlib Nat.forall_exists_prime_gt_and_modEq) gives infinitely many such p.

/-! Step CunninghamChain.infinitely_many_secondKind_chains.R1.H1. -/

theorem P8Cunningham.cunn_h1 : Set.Infinite {p : ℕ | CunninghamChain.IsSecondKindChainOfLength p 1} := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨p, hpN, hpp, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq (N + 5) (q := 3) (a := 2)
    (by norm_num) (by norm_num)
  refine ⟨p, ⟨Nat.one_pos, ?_, ?_⟩, by omega⟩
  · intro i hi
    have : i = 0 := by omega
    subst this
    simpa [CunninghamChain.secondKindTerm] using hpp
  · simp only [CunninghamChain.secondKindTerm]
    intro hq
    have h3 : 3 ∣ 2 * p - 1 := by
      have := hmod
      unfold Nat.ModEq at this
      omega
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp h3
    omega

theorem OMA.solution : OMA.R_CunninghamChain_infinitely_many_secondKind_chains_R1.H1 :=
  P8Cunningham.cunn_h1
