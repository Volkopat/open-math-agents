import OMAReductions.R_arxiv_2009_03418_R1_H2_R2
import Mathlib
/- Adapted from OpenAI openai/math@3344da59991ed94f9ba711217b29c1d760badfa6, CompleteCrossing. Apache-2.0. -/
namespace OMA.R_arxiv_2009_03418_R1_H2_R2_H1_R1
open OMA.S_arxiv_2009_03418
open scoped Classical BigOperators
noncomputable section
def H1 : Prop := ∀ s : ℕ, 2 ≤ s →
  let n := 2*s+1
  let T := Fin n → Fin n → Fin n → Fin n → ℝ
  let good := fun (J : T) =>
    ∃ orders : ∀ i : Fin n, LinearOrder {j : Fin n // j ≠ i},
      (∀ i k q, J i i k q = 0) ∧ (∀ i p k, J i p k k = 0) ∧
      (∀ i p k q, J p i k q = -J i p k q) ∧ (∀ i p k q, J i p q k = -J i p k q) ∧
      (∀ i p k q, J k q i p = -J i p k q) ∧
      (∀ i (p q : {j : Fin n // j ≠ i}), J i p.val i q.val = (if @LT.lt _ (orders i).toLT p q then 1/2 else if @LT.lt _ (orders i).toLT q p then -(1/2) else 0)) ∧
      (∀ z z' : Fin n → Fin n → ℝ, (∀ v, ((∑ i, z i v) - ∑ p, z v p) = 0) → (∀ v, ((∑ i, z' i v) - ∑ p, z' v p) = 0) → (∑ i, ∑ p, ∑ k, ∑ q, J i p k q * z i p * z' k q) = 0)
  let supp := fun (J : T) => (Finset.univ : Finset ((Fin n × Fin n) × (Fin n × Fin n))).filter fun a =>
      a.1.1 < a.1.2 ∧ a.2.1 < a.2.2 ∧
      a.1.1 ≠ a.2.1 ∧ a.1.1 ≠ a.2.2 ∧
      a.1.2 ≠ a.2.1 ∧ a.1.2 ≠ a.2.2 ∧
      J a.1.1 a.1.2 a.2.1 a.2.2 ≠ 0
  ∀ J : T, good J → 2*(s.choose 2)^2 ≤ (supp J).card

def H2 : Prop := ∀ s : ℕ, 2 ≤ s →
  let n := 2*s+1
  let T := Fin n → Fin n → Fin n → Fin n → ℝ
  let good := fun (J : T) =>
    ∃ orders : ∀ i : Fin n, LinearOrder {j : Fin n // j ≠ i},
      (∀ i k q, J i i k q = 0) ∧ (∀ i p k, J i p k k = 0) ∧
      (∀ i p k q, J p i k q = -J i p k q) ∧ (∀ i p k q, J i p q k = -J i p k q) ∧
      (∀ i p k q, J k q i p = -J i p k q) ∧
      (∀ i (p q : {j : Fin n // j ≠ i}), J i p.val i q.val = (if @LT.lt _ (orders i).toLT p q then 1/2 else if @LT.lt _ (orders i).toLT q p then -(1/2) else 0)) ∧
      (∀ z z' : Fin n → Fin n → ℝ, (∀ v, ((∑ i, z i v) - ∑ p, z v p) = 0) → (∀ v, ((∑ i, z' i v) - ∑ p, z' v p) = 0) → (∑ i, ∑ p, ∑ k, ∑ q, J i p k q * z i p * z' k q) = 0)
  let supp := fun (J : T) => (Finset.univ : Finset ((Fin n × Fin n) × (Fin n × Fin n))).filter fun a =>
      a.1.1 < a.1.2 ∧ a.2.1 < a.2.2 ∧
      a.1.1 ≠ a.2.1 ∧ a.1.1 ≠ a.2.2 ∧
      a.1.2 ≠ a.2.1 ∧ a.1.2 ≠ a.2.2 ∧
      J a.1.1 a.1.2 a.2.1 a.2.2 ≠ 0
  ∀ D : AdmissibleDrawing (completeGraph n), ∃ J : T, good J ∧ (supp J).card ≤ 2*crossingCount D

theorem main : H1 → H2 → OMA.R_arxiv_2009_03418_R1_H2_R2.H1 := by
  intro alg geo s hs D
  obtain ⟨J,hJ,hle⟩ := geo s hs D
  have := alg s hs J hJ
  omega
end
end OMA.R_arxiv_2009_03418_R1_H2_R2_H1_R1
