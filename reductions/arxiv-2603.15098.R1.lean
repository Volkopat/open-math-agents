import OMAStatements.S_arxiv_2603_15098
import Mathlib

/-!
Reduction of Koebe's circle-domain conjecture (arXiv 2603.15098) to its
normalized form, following the architecture of OpenAI's openai/math
(Apache-2.0, commit 3344da59991ed94f9ba711217b29c1d760badfa6,
OAI/Analysis/CircleDomains/Selection/ConditionalKoebe.lean).

H1 is Koebe uniformization for domains containing the point at infinity.
H2 is the Möbius normalization step: every domain can be moved by a map
carrying it to a domain through infinity, and conformal equivalences out of
the moved domain pull back to conformal equivalences out of the original.
-/

namespace OMA.R_arxiv_2603_15098_R1
open Set OMA.S_arxiv_2603_15098
open scoped OnePoint

/-- Koebe uniformization for domains of the sphere containing infinity. -/
def H1 : Prop :=
  ∀ U : Set OMA.S_arxiv_2603_15098.Sphere, IsOpen U → IsConnected U → ∞ ∈ U →
    ∃ (V : Set OMA.S_arxiv_2603_15098.Sphere) (f : OMA.S_arxiv_2603_15098.Sphere →
      OMA.S_arxiv_2603_15098.Sphere),
      OMA.S_arxiv_2603_15098.IsCircleDomain V ∧
        OMA.S_arxiv_2603_15098.IsConformalEquivalence f U V

/-- Normalization: move a domain through infinity, pulling back conformal models. -/
def H2 : Prop :=
  ∀ U : Set OMA.S_arxiv_2603_15098.Sphere, IsOpen U → IsConnected U →
    ∃ g : OMA.S_arxiv_2603_15098.Sphere → OMA.S_arxiv_2603_15098.Sphere,
      IsOpen (g '' U) ∧ IsConnected (g '' U) ∧ ∞ ∈ g '' U ∧
      ∀ (V : Set OMA.S_arxiv_2603_15098.Sphere)
        (f : OMA.S_arxiv_2603_15098.Sphere → OMA.S_arxiv_2603_15098.Sphere),
        OMA.S_arxiv_2603_15098.IsConformalEquivalence f (g '' U) V →
          OMA.S_arxiv_2603_15098.IsConformalEquivalence (f ∘ g) U V

theorem main : H1 → H2 → type_of% @OMA.S_arxiv_2603_15098.main := by
  intro h1 h2 U hU hconn
  obtain ⟨g, hgo, hgc, hinf, hpull⟩ := h2 U hU hconn
  obtain ⟨V, f, hV, hf⟩ := h1 (g '' U) hgo hgc hinf
  exact ⟨V, f ∘ g, hV, hpull V f hf⟩

end OMA.R_arxiv_2603_15098_R1
