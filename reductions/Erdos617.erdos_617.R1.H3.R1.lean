import OMAReductions.R_Erdos617_erdos_617_R1

-- Reduction Erdos617.erdos_617.R1.H3.R1 of step Erdos617.erdos_617.R1.H3
-- Credit: @timlantin

/-!
Reduction Erdos617.erdos_617.R1.H3.R1 of step Erdos617.erdos_617.R1.H3 (Erdős–Gyárfás balanced
colourings, all r ≥ 6; the parent reduction is by capioryadi-collab).

Split r = 6 from r ≥ 7.

* H1: the r = 6 case in the single-graph form of Xia and Szeider (arXiv:2610.24484), exactly as
  the parent's H1 (Fin 17) and H2 (Fin 26): a graph on 37 vertices with at most 111 edges has
  7 vertices that are independent or miss fewer than 5 edges.
* H2: the colouring statement for r ≥ 7, unchanged.

The single-graph form is NOT available for r = 7: five disjoint K7 together with the complement
of the balanced blow-up C5[3] is a graph on 50 vertices with 165 ≤ 175 edges, independence
number 7, in which every 8 vertices miss at least 6 edges. So the split at 6 is the natural one.

Written with Claude Code (AI-assisted).
-/

namespace OMA.R_Erdos617_erdos_617_R1_H3_R1

def H1 : Prop :=
  ∀ adj : Sym2 (Fin 37) → Bool,
    ((Finset.univ : Finset (Fin 37 × Fin 37)).filter
      (fun p => p.1 ≠ p.2 ∧ adj s(p.1, p.2) = true)).card ≤ 222 →
    ∃ S : Finset (Fin 37), S.card = 7 ∧
      ((∀ u ∈ S, ∀ v ∈ S, u ≠ v → adj s(u, v) = false) ∨
       ((S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ adj s(p.1, p.2) = false)).card < 10)

def H2 : Prop :=
  ∀ (r : ℕ) (_ : r ≥ 7) (coloring : Sym2 (Fin (r ^ 2 + 1)) → Fin r),
    ((Finset.univ : Finset (Fin (r ^ 2 + 1) × Fin (r ^ 2 + 1))).filter
      (fun p => p.1 ≠ p.2 ∧ coloring s(p.1, p.2) = ⟨0, by omega⟩)).card ≤ r * (r ^ 2 + 1) →
    ∃ (S : Finset (Fin (r ^ 2 + 1))) (k : Fin r),
      S.card = r + 1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k

open OMA.R_Erdos617_erdos_617_R1 in
lemma six (h1 : H1) (c : Sym2 (Fin (6 ^ 2 + 1)) → Fin 6)
    (hc : ((Finset.univ : Finset (Fin (6 ^ 2 + 1) × Fin (6 ^ 2 + 1))).filter
      (fun p => p.1 ≠ p.2 ∧ c s(p.1, p.2) = (0 : Fin 6))).card ≤ 6 * (6 ^ 2 + 1)) :
    ∃ (S : Finset (Fin (6 ^ 2 + 1))) (k : Fin 6),
      S.card = 6 + 1 ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u, v) ≠ k := by
  let adj : Sym2 (Fin 37) → Bool := fun e => decide (c e = (0 : Fin 6))
  have hadj : ((Finset.univ : Finset (Fin 37 × Fin 37)).filter
      (fun p => p.1 ≠ p.2 ∧ adj s(p.1, p.2) = true)).card ≤ 222 := by
    simpa [adj] using hc
  obtain ⟨S, hScard, hS | hS⟩ := h1 adj hadj
  · refine ⟨S, 0, hScard, ?_⟩
    intro u hu v hv huv
    have := hS u hu v hv huv
    simpa [adj] using this
  · have hfew : ((S ×ˢ S).filter
        (fun p => p.1 ≠ p.2 ∧ c s(p.1, p.2) ≠ (0 : Fin 6))).card < 2 * (6 - 1) := by
      simpa [adj] using hS
    obtain ⟨j, hj⟩ := missing_color_of_few_nonedges (r := 6) c 0 S hfew
    exact ⟨S, j, hScard, hj⟩

theorem main : H1 → H2 → OMA.R_Erdos617_erdos_617_R1.H3 := by
  intro h1 h2 r hr coloring hc
  by_cases h6 : r = 6
  · subst h6
    exact six h1 coloring hc
  · exact h2 r (by omega) coloring hc

end OMA.R_Erdos617_erdos_617_R1_H3_R1
