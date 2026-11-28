import OMAReductions.R_arxiv_2009_03418_R1_H2_R2_H1_R1
import Mathlib
/- Adapted from OpenAI openai/math@3344da59991ed94f9ba711217b29c1d760badfa6, CompleteCrossing. Apache-2.0. -/
namespace OMA.R_arxiv_2009_03418_R1_H2_R2_H1_R1_H2_R1
open OMA.S_arxiv_2009_03418
open scoped Classical BigOperators
noncomputable section
def H1 : Prop := ∀ n : ℕ,
  let P := fun (A : AdmissibleDrawing (completeGraph n)) =>
    (∀ e f : CompleteEdge n, e ≠ f → (e.1.1 = f.1.1 ∨ e.1.1 = f.1.2 ∨ e.1.2 = f.1.1 ∨ e.1.2 = f.1.2) → Disjoint (edgeInterior A.toContinuousDrawing e) (edgeInterior A.toContinuousDrawing f)) ∧
    ∀ e, ∃ m : ℕ, 0 < m ∧ ∃ k : Fin (m+1) → unitInterval, StrictMono k ∧ k 0 = 0 ∧ k (Fin.last m) = 1 ∧ (∀ i, A.edge e (k i) ∉ crossingPoints A.toContinuousDrawing) ∧ ∀ i : Fin m, ∀ t : unitInterval, k i.castSucc ≤ t → t ≤ k i.succ → let a := k i.castSucc; let b := k i.succ; let u := ((t:ℝ)-a)/((b:ℝ)-a); A.edge e t = (1-u) • A.edge e a + u • A.edge e b
  ∀ D : AdmissibleDrawing (completeGraph n), ∃ A, P A ∧ crossingCount A ≤ crossingCount D

def H2 : Prop := ∀ s : ℕ, 2 ≤ s →
  let n := 2*s+1
  let P := fun (A : AdmissibleDrawing (completeGraph n)) =>
    (∀ e f : CompleteEdge n, e ≠ f → (e.1.1 = f.1.1 ∨ e.1.1 = f.1.2 ∨ e.1.2 = f.1.1 ∨ e.1.2 = f.1.2) → Disjoint (edgeInterior A.toContinuousDrawing e) (edgeInterior A.toContinuousDrawing f)) ∧
    ∀ e, ∃ m : ℕ, 0 < m ∧ ∃ k : Fin (m+1) → unitInterval, StrictMono k ∧ k 0 = 0 ∧ k (Fin.last m) = 1 ∧ (∀ i, A.edge e (k i) ∉ crossingPoints A.toContinuousDrawing) ∧ ∀ i : Fin m, ∀ t : unitInterval, k i.castSucc ≤ t → t ≤ k i.succ → let a := k i.castSucc; let b := k i.succ; let u := ((t:ℝ)-a)/((b:ℝ)-a); A.edge e t = (1-u) • A.edge e a + u • A.edge e b
  let T := Fin n → Fin n → Fin n → Fin n → ℝ
  let good := fun (J : T) =>
    ∃ orders : ∀ i : Fin n, LinearOrder {j : Fin n // j ≠ i},
      (∀ i k q, J i i k q = 0) ∧ (∀ i p k, J i p k k = 0) ∧
      (∀ i p k q, J p i k q = -J i p k q) ∧ (∀ i p k q, J i p q k = -J i p k q) ∧
      (∀ i p k q, J k q i p = -J i p k q) ∧
      (∀ i (p q : {j : Fin n // j ≠ i}), J i p.val i q.val = (if @LT.lt _ (orders i).toLT p q then 1/2 else if @LT.lt _ (orders i).toLT q p then -(1/2) else 0)) ∧
      (∀ z z' : Fin n → Fin n → ℝ, (∀ v, ((∑ i, z i v) - ∑ p, z v p) = 0) → (∀ v, ((∑ i, z' i v) - ∑ p, z' v p) = 0) → (∑ i, ∑ p, ∑ k, ∑ q, J i p k q * z i p * z' k q) = 0)
  let supp := fun (J : T) => (Finset.univ : Finset ((Fin n × Fin n) × (Fin n × Fin n))).filter fun a => let x := a.1; let y := a.2;
      x.1 < x.2 ∧ y.1 < y.2 ∧
      x.1 ≠ y.1 ∧ x.1 ≠ y.2 ∧
      x.2 ≠ y.1 ∧ x.2 ≠ y.2 ∧
      J x.1 x.2 y.1 y.2 ≠ 0
  ∀ A : AdmissibleDrawing (completeGraph n), P A → ∃ J : T, good J ∧ (supp J).card ≤ 2*crossingCount A

theorem main : H1 → H2 → OMA.R_arxiv_2009_03418_R1_H2_R2_H1_R1.H2 := by
  intro norm tensor s hs
  dsimp only
  intro D
  obtain ⟨A, hA, hle⟩ := norm _ D
  obtain ⟨J, good, hb⟩ := tensor s hs A hA
  exact ⟨J, good, hb.trans (Nat.mul_le_mul_left 2 hle)⟩
end
end OMA.R_arxiv_2009_03418_R1_H2_R2_H1_R1_H2_R1
