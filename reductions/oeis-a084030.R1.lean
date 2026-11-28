import OMAStatements.S_oeis_a084030
import Mathlib

/-! # Reduction oeis-a084030.R1 - split of the A084030 proof

The merged proof `proofs/oeis-a084030.lean` exceeds the 30-minute
check budget. Split:

* `H1` : for every n ≥ 3 there exists a Finset of at least n eligible
  witnesses (n-digit multiples of n with digit sum n). Reduced further
  in `oeis-a084030.R1.H1.R1` (table range n ≤ 130 vs the two-block
  construction n ≥ 131).
* `H2` : the boundary values n = 1 and n = 2 each have exactly one
  witness.

`main` is the comparison `(witnesses n).card < n ↔ n = 2`. -/

namespace OMA.R_oeis_a084030_R1

/-- At least n eligible witnesses for every n ≥ 3. -/
def H1 : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∃ s : Finset ℕ, n ≤ s.card ∧ ∀ N ∈ s, n ∣ N ∧ (Nat.digits 10 N).length = n ∧ (Nat.digits 10 N).sum = n

/-- The single witness at n = 1 and at n = 2. -/
def H2 : Prop :=
  (OMA.S_oeis_a084030.witnesses 1).card = 1 ∧
    (OMA.S_oeis_a084030.witnesses 2).card = 1

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a084030.main := by
  intro h1 h2 n hn
  obtain ⟨h2a, h2b⟩ := h2
  have mem_wit : ∀ {m M : ℕ},
      m ∣ M ∧ (Nat.digits 10 M).length = m ∧
        (Nat.digits 10 M).sum = m →
      M ∈ OMA.S_oeis_a084030.witnesses m := by
    intro m M h
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, h⟩
    have hlt := Nat.lt_base_pow_length_digits (b := 10) (m := M)
      (by norm_num)
    rwa [h.2.1] at hlt
  constructor
  · intro hlt
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · interval_cases n
      · exact absurd hlt (by rw [h2a]; exact Nat.lt_irrefl 1)
      · rfl
    · obtain ⟨s, hs, hwit⟩ := h1 n h3
      have hsub : s ⊆ OMA.S_oeis_a084030.witnesses n :=
        fun N hN => mem_wit (hwit N hN)
      have : n ≤ (OMA.S_oeis_a084030.witnesses n).card :=
        hs.trans (Finset.card_le_card hsub)
      exact absurd hlt (Nat.not_lt.mpr this)
  · intro hn2
    subst hn2
    rw [h2b]
    norm_num

end OMA.R_oeis_a084030_R1
