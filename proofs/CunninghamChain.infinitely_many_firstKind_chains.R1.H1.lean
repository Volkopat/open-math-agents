import OMAReductions.R_CunninghamChain_infinitely_many_firstKind_chains_R1
import Mathlib

-- Step CunninghamChain.infinitely_many_firstKind_chains.R1.H1: hypothesis H1 of reduction CunninghamChain.infinitely_many_firstKind_chains.R1
-- Credit: @ivillar

/-!
Primes `p ≡ 1 (mod 3)` (infinitely many, Mathlib's `Nat.infinite_setOfPred_prime_modEq_one`) have
`3 ∣ 2 p + 1` with `2 p + 1 > 3`, so they start a first-kind chain of exact length one.
-/
namespace F2CC1

theorem inf_len_one : Set.Infinite {p : ℕ | CunninghamChain.IsFirstKindChainOfLength p 1} := by
  refine Set.Infinite.mono ?_ (Nat.infinite_setOfPred_prime_modEq_one (k := 3) (by norm_num))
  rintro p ⟨hp, hmod⟩
  have hm : p % 3 = 1 % 3 := hmod
  refine ⟨one_pos, ?_, ?_⟩
  · intro i hi
    interval_cases i
    simpa [CunninghamChain.firstKindTerm] using hp
  · simp only [CunninghamChain.firstKindTerm]
    intro hpr
    have h3 : 3 ∣ 2 * p + 1 := by omega
    have h := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hpr).mp h3
    have h2 := hp.two_le
    omega

end F2CC1

theorem OMA.solution : OMA.R_CunninghamChain_infinitely_many_firstKind_chains_R1.H1 :=
  F2CC1.inf_len_one
