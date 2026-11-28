import OMAReductions.R_Erdos1020_erdos_1020_R1

-- Reduction Erdos1020.erdos_1020.R1.H2.R1 of step Erdos1020.erdos_1020.R1.H2
-- Credit: @rickmanelius

/-!
# Erdős 1020, step H2 (the upper bound): `k = 2` outright by Erdős–Ko–Rado

The step is the upper half of the Erdős Matching Conjecture: for `r ≥ 3`, `k ≥ 2` and
`n ≥ r k`, an `r`-uniform family on `n` labelled vertices with no `k` pairwise disjoint edges
has at most `max (C(r k - 1, r), C(n, r) - C(n - k + 1, r))` edges.

Proved below, with no hypothesis (`case_two`): the case `k = 2`. A family with no two disjoint
edges is intersecting (its edges are nonempty since `r ≥ 3`), so the Erdős–Ko–Rado theorem of
Mathlib (`Finset.erdos_ko_rado`, valid since `2 r ≤ n`) bounds it by `C(n - 1, r - 1)`, which by
Pascal's rule equals `C(n, r) - C(n - 1, r)`, the second term of the maximum.

The remaining cases `k ≥ 3` are left as hypotheses, split at Frankl's threshold:
* `H1`: `n ≥ (2 k - 1) r - k + 1` (in Frankl's notation `n ≥ (2 s + 1) k - s` with `s = k - 1`
  and uniformity `r`; reported as settled by Frankl in 2013);
* `H2`: `r k ≤ n < (2 k - 1) r - k + 1` (the middle range, open in general).
-/

namespace OMA.R_Erdos1020_erdos_1020_R1_H2_R1

open Finset

/-- The step for `k ≥ 3` and `n` at or above Frankl's threshold `(2 k - 1) r - k + 1`. -/
def H1 : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∀ n k : ℕ, 3 ≤ k → (2 * k - 1) * r - k + 1 ≤ n →
    Erdos1020.f n r k ≤ max ((r * k - 1).choose r) (n.choose r - (n - k + 1).choose r)

/-- The step for `k ≥ 3` and `r k ≤ n` below Frankl's threshold. -/
def H2 : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∀ n k : ℕ, 3 ≤ k → r * k ≤ n → n < (2 * k - 1) * r - k + 1 →
    Erdos1020.f n r k ≤ max ((r * k - 1).choose r) (n.choose r - (n - k + 1).choose r)

/-- The case `k = 2`: an `r`-uniform family with no two disjoint edges is intersecting, so the
Erdős–Ko–Rado theorem bounds it by `C(n - 1, r - 1) = C(n, r) - C(n - 1, r)`. -/
lemma case_two (r n : ℕ) (hr : 3 ≤ r) (hn : r * 2 ≤ n) :
    Erdos1020.f n r 2 ≤ max ((r * 2 - 1).choose r) (n.choose r - (n - 2 + 1).choose r) := by
  classical
  have key : Erdos1020.f n r 2 ≤ (n - 1).choose (r - 1) := by
    unfold Erdos1020.f Hypergraph.extremalNumber
    apply Finset.sup_le
    intro H hH
    simp only [Finset.mem_filter, Finset.mem_powerset] at hH
    obtain ⟨hsub, hnot⟩ := hH
    have hsized : (H : Set (Finset (Fin n))).Sized r := by
      intro e he
      have h := hsub (Finset.mem_coe.mp he)
      rw [Finset.mem_powersetCard] at h
      exact h.2
    have hint : (H : Set (Finset (Fin n))).Intersecting := by
      intro a ha b hb hdisj
      by_cases hab : a = b
      · subst hab
        have hcard := hsized ha
        rw [Finset.disjoint_self_iff_empty] at hdisj
        rw [hdisj, Finset.card_empty] at hcard
        omega
      · apply hnot
        refine ⟨{a, b}, ?_, Finset.card_pair hab, ?_⟩
        · intro x hx
          rw [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact Finset.mem_coe.mp ha
          · exact Finset.mem_coe.mp hb
        · intro x hx y hy hxy
          rw [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
            Set.mem_singleton_iff] at hx hy
          rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
          · exact absurd rfl hxy
          · exact hdisj
          · exact hdisj.symm
          · exact absurd rfl hxy
    exact Finset.erdos_ko_rado hint hsized (by omega)
  have hn1 : n - 2 + 1 = n - 1 := by omega
  rw [hn1]
  have hpascal : n.choose r = (n - 1).choose (r - 1) + (n - 1).choose r := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    simp [Nat.choose_succ_succ]
  exact le_trans key (le_trans (by omega) (le_max_right _ _))

theorem main : H1 → H2 → OMA.R_Erdos1020_erdos_1020_R1.H2 := by
  intro h1 h2
  unfold OMA.R_Erdos1020_erdos_1020_R1.H2
  intro r hr n k hk hn
  rcases (show k = 2 ∨ 3 ≤ k by omega) with rfl | hk3
  · exact case_two r n hr hn
  · by_cases hF : (2 * k - 1) * r - k + 1 ≤ n
    · exact h1 r hr n k hk3 hF
    · exact h2 r hr n k hk3 hn (by omega)

end OMA.R_Erdos1020_erdos_1020_R1_H2_R1
