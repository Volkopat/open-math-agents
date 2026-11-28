import OMAReductions.R_Erdos599_erdos_599_R1
import Mathlib

/-!
# Erdős 599 linkability: orthogonal Menger data and first-hit trimming

The deep input is the strong Aharoni--Berger orthogonal separator theorem.
The complementary finite-path input is the trimming/transport argument which,
from such orthogonal data, converts the maximality hypothesis on first-hit
wave families into a linkage covering the whole source set.
-/

namespace OMA.R_Erdos599_erdos_599_R1_H2_R1

/-- Strong Aharoni--Berger input: every pair of vertex sets has an orthogonal
path packing and separator. -/
def H1 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) (A B : Set V),
    ∃ (ι : Type) (a b : ι → V) (p : ∀ i, G.Walk (a i) (b i)) (S : Set V),
      (∀ i, a i ∈ A) ∧ (∀ i, b i ∈ B) ∧ (∀ i, (p i).IsPath) ∧
      (Pairwise fun i j => Disjoint {v | v ∈ (p i).support} {v | v ∈ (p j).support}) ∧
      S ⊆ {v | ∃ i, v ∈ (p i).support} ∧
      (∀ i, ∃! v, v ∈ S ∧ v ∈ (p i).support) ∧
      (∀ a' ∈ A, ∀ b' ∈ B, ∀ q : G.Walk a' b', q.IsPath → ∃ v ∈ q.support, v ∈ S)

/-- Finite-path transport input: orthogonal Menger data can be trimmed to
first-hit wave paths; the maximality hypothesis then forces the source cover. -/
def H2 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) (A B : Set V),
    (∀ (T : Set V) (b : T → V) (q : ∀ t : T, G.Walk (b t) t.1),
      (∀ t, b t ∈ A) → (∀ t, (q t).IsPath) →
      (∀ t, (∀ x ∈ (q t).support.tail, x ∉ A) ∧
        (∀ x ∈ (q t).support.dropLast, x ∉ B)) →
      (Pairwise fun t u => Disjoint {v | v ∈ (q t).support} {v | v ∈ (q u).support}) →
      (∀ u ∈ A, ∀ v ∈ B, ∀ w : G.Walk u v, w.IsPath → ∃ x ∈ w.support, x ∈ T) →
      ∀ x ∈ A, ∃ t, b t = x) →
    ∀ (ι : Type) (a b : ι → V) (p : ∀ i, G.Walk (a i) (b i)) (S : Set V),
      (∀ i, a i ∈ A) → (∀ i, b i ∈ B) → (∀ i, (p i).IsPath) →
      (Pairwise fun i j => Disjoint {v | v ∈ (p i).support} {v | v ∈ (p j).support}) →
      S ⊆ {v | ∃ i, v ∈ (p i).support} →
      (∀ i, ∃! v, v ∈ S ∧ v ∈ (p i).support) →
      (∀ a' ∈ A, ∀ b' ∈ B, ∀ q : G.Walk a' b', q.IsPath → ∃ v ∈ q.support, v ∈ S) →
      ∃ (b' : A → V) (p' : ∀ x : A, G.Walk x.1 (b' x)),
        (∀ x, b' x ∈ B) ∧
        (Pairwise fun x y => Disjoint {v | v ∈ (p' x).support} {v | v ∈ (p' y).support})

theorem main : H1 → H2 → OMA.R_Erdos599_erdos_599_R1.H2 := by
  intro hstrong htransport V G A B hmax
  obtain ⟨ι, a, b, p, S, ha, hb, hp, hdisjoint, hsub, hunique, hsep⟩ :=
    hstrong V G A B
  exact htransport V G A B hmax ι a b p S
    ha hb hp hdisjoint hsub hunique hsep

end OMA.R_Erdos599_erdos_599_R1_H2_R1
