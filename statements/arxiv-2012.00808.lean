import Mathlib

namespace OMA.S_arxiv_2012_00808

open SimpleGraph

abbrev TokenVert (V : Type*) (k : ℕ) := { S : Finset V // S.card = k }

def tokenGraph {V : Type*} [DecidableEq V] (G : SimpleGraph V) (k : ℕ) :
    SimpleGraph (TokenVert V k) where
  Adj S T := ∃ u v : V, G.Adj u v ∧ symmDiff S.val T.val = {u, v}
  symm := ⟨fun _ _ => by
    rintro ⟨u, v, huv, h⟩
    exact ⟨u, v, huv, by rwa [symmDiff_comm]⟩⟩
  loopless := ⟨by
    intro S ⟨u, v, _, h⟩
    rw [symmDiff_self] at h
    exact Finset.insert_ne_empty u {v} h.symm⟩

noncomputable def laplacianForm {W : Type*} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (f : W → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ u : W, ∑ v : W, if H.Adj u v then (f u - f v) ^ 2 else 0

noncomputable def algebraicConnectivity {W : Type*} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] : ℝ :=
  sInf { r : ℝ | ∃ f : W → ℝ, (∑ w : W, f w) = 0 ∧ (∑ w : W, f w ^ 2) = 1 ∧
    r = laplacianForm H f }

theorem main :
    ∀ (n k : ℕ), 1 ≤ k → k ≤ n - 1 →
    ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel (tokenGraph G k).Adj],
      algebraicConnectivity (tokenGraph G k) = algebraicConnectivity G := by
  sorry

end OMA.S_arxiv_2012_00808
