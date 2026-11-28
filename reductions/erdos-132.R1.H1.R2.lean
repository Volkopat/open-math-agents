import OMAReductions.R_erdos_132_R1
import Mathlib

/-!
# Geometric cases of the two-rare-distances question

The first case covers every six-point set and every configuration with at most two distances.
The second covers sets on m arbitrary lines when the point count reaches 4m².
The third hypothesis isolates the configurations left by these two results.

Formalization by Koa Okano (@KoaOkano) with OpenAI Codex.
-/

open Finset
open scoped Classical
open OMA.S_erdos_132 (rareDistances)

namespace OMA.R_erdos_132_R1_H1_R2

/-- A two-distance set of size at least five has five points and two rare
distances. Every six-point set also has two rare distances. -/
def H1 : Prop :=
  (∀ A : Finset (EuclideanSpace ℝ (Fin 2)), 5 ≤ A.card →
    (A.offDiag.image (fun p => dist p.1 p.2)).card ≤ 2 →
    A.card = 5 ∧ (rareDistances A).card = 2) ∧
  (∀ A : Finset (EuclideanSpace ℝ (Fin 2)), A.card = 6 → 2 ≤ (rareDistances A).card)

/-- The line-cover case of the two-rare-distances question. -/
def H2 : Prop :=
  ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))) (C : Finset (Finset (EuclideanSpace ℝ (Fin 2)))), C.Nonempty →
    A ⊆ C.biUnion id → (∀ L ∈ C, Collinear ℝ (L : Set (EuclideanSpace ℝ (Fin 2)))) →
    4*C.card^2 ≤ A.card → 2 ≤ (rareDistances A).card

/-- The remaining configurations have at least seven points and between three
and half the point count in distinct distances. Every line cover costs 4m² > n. -/
def H3 : Prop :=
  ∀ A : Finset (EuclideanSpace ℝ (Fin 2)), 7 ≤ A.card →
    3 ≤ (A.offDiag.image (fun p => dist p.1 p.2)).card →
    (A.offDiag.image (fun p => dist p.1 p.2)).card ≤ A.card / 2 →
    (∀ C : Finset (Finset (EuclideanSpace ℝ (Fin 2))), C.Nonempty → A ⊆ C.biUnion id →
      (∀ L ∈ C, Collinear ℝ (L : Set (EuclideanSpace ℝ (Fin 2)))) → A.card < 4*C.card^2) →
    2 ≤ (rareDistances A).card

theorem main : H1 → H2 → H3 → OMA.R_erdos_132_R1.H1 := by
  classical
  intro smallSets lines rest A five few
  by_cases six : A.card = 6
  · exact smallSets.2 A six
  by_cases small : (A.offDiag.image (fun p => dist p.1 p.2)).card ≤ 2
  · exact (smallSets.1 A five small).2.ge
  have three : 3 ≤ (A.offDiag.image (fun p => dist p.1 p.2)).card := by omega
  have seven : 7 ≤ A.card := by
    have lim := three.trans few
    omega
  by_contra! bad
  apply (not_le_of_gt bad) (rest A seven three few ?_)
  intro C ne covered collinear
  by_contra! large
  exact (not_le_of_gt bad) (lines A C ne covered collinear large)

end OMA.R_erdos_132_R1_H1_R2
