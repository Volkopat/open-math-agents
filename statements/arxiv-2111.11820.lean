import Mathlib

namespace OMA.S_arxiv_2111_11820

open SimpleGraph

noncomputable def quadForm {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, if G.Adj i j then x i * x j else 0

noncomputable def rayleighQuot {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℝ) : ℝ :=
  quadForm G x / (∑ i : Fin n, x i ^ 2)

noncomputable def maxEig {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℝ :=
  sSup { r : ℝ | ∃ x : Fin n → ℝ, (∑ i : Fin n, x i ^ 2) ≠ 0 ∧ r = rayleighQuot G x }

noncomputable def minEig {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℝ :=
  sInf { r : ℝ | ∃ x : Fin n → ℝ, (∑ i : Fin n, x i ^ 2) ≠ 0 ∧ r = rayleighQuot G x }

noncomputable def graphSpread {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℝ :=
  maxEig G - minEig G

def HasMinor {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ B : W → Set V,
    (∀ w, (B w).Nonempty) ∧
    (∀ w₁ w₂, w₁ ≠ w₂ → Disjoint (B w₁) (B w₂)) ∧
    (∀ w, (G.induce (B w)).Connected) ∧
    (∀ w₁ w₂, H.Adj w₁ w₂ → ∃ u ∈ B w₁, ∃ v ∈ B w₂, G.Adj u v)

def K4Graph : SimpleGraph (Fin 4) := ⊤

def K23Graph : SimpleGraph (Fin 2 ⊕ Fin 3) where
  Adj u v := (u.isLeft ∧ v.isRight) ∨ (u.isRight ∧ v.isLeft)
  symm := ⟨fun _ _ h => by rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> tauto⟩
  loopless := ⟨fun u h => by cases u <;> simp at h⟩

def IsOuterplanar {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬ HasMinor G K4Graph ∧ ¬ HasMinor G K23Graph

def fanGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj u v :=
    (u.val = 0 ∧ v.val ≠ 0) ∨
    (v.val = 0 ∧ u.val ≠ 0) ∨
    (u.val ≠ 0 ∧ v.val ≠ 0 ∧ (u.val + 1 = v.val ∨ v.val + 1 = u.val))
  symm := ⟨fun _ _ h => by rcases h with h | h | ⟨hu, hv, h⟩ <;> tauto⟩
  loopless := ⟨fun u h => by rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨_, _, h1 | h1⟩ <;> omega⟩

instance instDecidableRelFanGraph (n : ℕ) : DecidableRel (fanGraph n).Adj :=
  fun u v => by unfold fanGraph; dsimp; infer_instance

theorem main :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        IsOuterplanar G → graphSpread G ≤ graphSpread (fanGraph n) := by
  sorry

end OMA.S_arxiv_2111_11820
