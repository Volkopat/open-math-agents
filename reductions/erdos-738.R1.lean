import OMAStatements.S_erdos_738
import Mathlib

/-!
Classical slice of Erdős Problem 738 (Gyárfás): a triangle-free graph of infinite chromatic
number contains every finite tree as an induced subgraph.

H1 is the classical star case: trees with a vertex adjacent to all other vertices. If every vertex
of `G` had fewer than `s` neighbours, a greedy colouring of each finite vertex set plus Tychonoff
compactness (the de Bruijn-Erdős argument) would colour `G` with `s` colours; so some vertex has
`s` neighbours, which are pairwise non-adjacent because `G` is triangle-free, and they span an
induced star. This is a known case, not progress on the conjecture.

H2 is the open rest: trees in which no vertex is adjacent to all others (diameter at least 3).
-/

namespace OMA.R_erdos_738_R1

/-- Gyárfás' conjecture for stars. -/
def H1 : Prop :=
  ∀ {V : Type} (G : SimpleGraph V), G.chromaticNumber = ⊤ → G.CliqueFree 3 →
    ∀ {W : Type} [Fintype W] (T : SimpleGraph W), T.IsTree →
      (∃ c : W, ∀ w, w ≠ c → T.Adj c w) → T.IsIndContained G

/-- Open rest: trees without a vertex adjacent to all others. -/
def H2 : Prop :=
  ∀ {V : Type} (G : SimpleGraph V), G.chromaticNumber = ⊤ → G.CliqueFree 3 →
    ∀ {W : Type} [Fintype W] (T : SimpleGraph W), T.IsTree →
      (∀ c : W, ∃ w, w ≠ c ∧ ¬ T.Adj c w) → T.IsIndContained G

theorem main : H1 → H2 → type_of% @OMA.S_erdos_738.main := by
  intro h1 h2 V G hchi htri W _ T hT
  by_cases hs : ∃ c : W, ∀ w, w ≠ c → T.Adj c w
  · exact h1 G hchi htri T hT hs
  · refine h2 G hchi htri T hT (fun c => ?_)
    by_contra hc
    exact hs ⟨c, fun w hw => by
      by_contra hn
      exact hc ⟨w, hw, hn⟩⟩

end OMA.R_erdos_738_R1
