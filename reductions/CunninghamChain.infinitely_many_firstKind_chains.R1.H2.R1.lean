import OMAReductions.R_CunninghamChain_infinitely_many_firstKind_chains_R1
import Mathlib.FieldTheory.Finite.Basic

-- Reduction CunninghamChain.infinitely_many_firstKind_chains.R1.H2.R1 of step CunninghamChain.infinitely_many_firstKind_chains.R1.H2
-- Credit: @hiattco

namespace OMA.R_CunninghamChain_infinitely_many_firstKind_chains_R1_H2_R1

open CunninghamChain

private theorem firstKind_suffix (p d i : ℕ) :
    firstKindTerm (firstKindTerm p d) i = firstKindTerm p (d + i) := by
  induction i with
  | zero => rfl
  | succ i ih => exact congrArg (fun q => 2 * q + 1) ih

private theorem index_le_firstKind (p i : ℕ) : i ≤ firstKindTerm p i := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    change i + 1 ≤ 2 * firstKindTerm p i + 1
    omega

private theorem firstFailure (P : Nat → Prop) {t : Nat} (ht : ¬ P t) :
    ∃ j, ¬ P j ∧ ∀ i < j, P i := by
  classical
  induction t using Nat.strongRecOn with
  | ind t ih =>
    by_cases all : ∀ i < t, P i
    · exact ⟨t, ht, all⟩
    · simp only [Classical.not_forall] at all
      obtain ⟨i, hi, hf⟩ := all
      exact ih i hi hf

private theorem suffix_unbounded (F : Nat → Nat → Nat) (P : Nat → Prop)
    (shift : ∀ p s i, F (F p s) i = F p (s+i))
    (grow : ∀ p s, s ≤ F p s)
    (prefixes : ∀ L, ∃ p, ∀ i < L, P (F p i))
    (ends : ∀ p, ∃ j, ¬ P (F p j)) (k B : Nat) :
    ∃ q, (∀ i < k, P (F q i)) ∧ ¬ P (F q k) ∧ B < q := by
  obtain ⟨p, hp⟩ := prefixes (B+k+1)
  obtain ⟨t, ht⟩ := ends p
  obtain ⟨j, hj, hbefore⟩ := firstFailure (fun i => P (F p i)) ht
  have hjbig : B+k+1 ≤ j := by
    exact Nat.le_of_not_gt (fun h => hj (hp j h))
  refine ⟨F p (j-k), ?_, ?_, ?_⟩
  · intro i hi
    rw [shift]
    exact hbefore _ (by omega)
  · rw [shift, Nat.sub_add_cancel (by omega)]
    exact hj
  · have := grow p (j-k)
    omega

-- The open prime-pattern input requires only one prefix of each length.
def H1 : Prop :=
  ∀ L : ℕ, ∃ p : ℕ, ∀ i < L, (firstKindTerm p i).Prime

-- Each prescribed start eventually encounters a nonprime.
def H2 : Prop :=
  ∀ p : ℕ, ∃ j : ℕ, ¬ (firstKindTerm p j).Prime

/-- Closed form of the first-kind Cunningham recurrence, with no subtraction. -/
lemma firstKindTerm_add_one (p j : ℕ) :
    CunninghamChain.firstKindTerm p j + 1 = 2^j * (p+1) := by
  induction j with
  | zero => simp [CunninghamChain.firstKindTerm]
  | succ j ih =>
    calc
      CunninghamChain.firstKindTerm p (j+1) + 1 = 2*(CunninghamChain.firstKindTerm p j+1) := by
        simp only [CunninghamChain.firstKindTerm]; omega
      _ = 2^(j+1) * (p+1) := by rw [ih, pow_succ]; ac_rfl

/-- For an odd prime start, the term indexed by `p - 1` is a proper multiple of `p`. -/
lemma firstKindTerm_odd_prime_witness {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p ∣ CunninghamChain.firstKindTerm p (p-1) ∧ p < CunninghamChain.firstKindTerm p (p-1) := by
  have hclosed := firstKindTerm_add_one p (p-1)
  have hpow := Nat.ModEq.pow_card_sub_one_eq_one hp ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have hsucc : p+1 ≡ 1 [MOD p] := by simp [Nat.ModEq]
  have hmod : CunninghamChain.firstKindTerm p (p-1) + 1 ≡ 0 + 1 [MOD p] := by
    rw [hclosed]
    simpa using hpow.mul hsucc
  have htwo := hp.two_le
  have hgt : 1 < (2:ℕ)^(p-1) := one_lt_pow₀ (by decide) (by omega)
  have hb := Nat.mul_le_mul_right (p+1) (show 2 ≤ (2:ℕ)^(p-1) by omega)
  exact ⟨Nat.modEq_zero_iff_dvd.mp (Nat.ModEq.add_right_cancel' 1 hmod), by omega⟩

/-- Every first-kind Cunningham recurrence has a nonprime term. -/
lemma firstKindTerm_has_nonprime (p : ℕ) : ∃ j, ¬ (CunninghamChain.firstKindTerm p j).Prime := by
  by_cases hp : p.Prime
  · by_cases hp2 : p = 2
    · subst p
      exact ⟨5, CunninghamChain.two_starts_firstKind_length_five.2.2⟩
    · obtain ⟨hd, hlt⟩ := firstKindTerm_odd_prime_witness hp hp2
      exact ⟨p-1, fun h => (h.eq_one_or_self_of_dvd p hd).elim hp.ne_one (Nat.ne_of_lt hlt)⟩
  · exact ⟨0, hp⟩

theorem termination : H2 := firstKindTerm_has_nonprime

theorem main : H1 → H2 → OMA.R_CunninghamChain_infinitely_many_firstKind_chains_R1.H2 := by
  intro prefixes ends k hk
  apply Set.infinite_iff_exists_gt.mpr
  intro B
  obtain ⟨q, hprime, hstop, hB⟩ :=
    suffix_unbounded firstKindTerm Nat.Prime firstKind_suffix index_le_firstKind prefixes ends k B
  exact ⟨q, ⟨by omega, hprime, hstop⟩, hB⟩

/-- Arbitrarily long prime prefixes suffice to produce unboundedly many starts
of any prescribed exact length at least two. -/
theorem of_prime_prefixes : H1 → OMA.R_CunninghamChain_infinitely_many_firstKind_chains_R1.H2 :=
  fun prefixes => main prefixes termination

end OMA.R_CunninghamChain_infinitely_many_firstKind_chains_R1_H2_R1
