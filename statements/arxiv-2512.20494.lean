import Mathlib

namespace OMA.S_arxiv_2512_20494

/-- A tournament on `n` vertices `Fin n`: an irreflexive, asymmetric, total binary relation. -/
structure Tournament (n : ℕ) where
  adj : Fin n → Fin n → Prop
  irrefl : ∀ u, ¬ adj u u
  total_asym : ∀ u v, u ≠ v → (adj u v ↔ ¬ adj v u)

/-- Two vertices `u, v` of a tournament `T` have isomorphic directed links if the induced
subtournaments on their neighborhoods `V \ {u}` and `V \ {v}` are isomorphic as digraphs. -/
def HasIsoLink {n : ℕ} (T : Tournament n) (u v : Fin n) : Prop :=
  ∃ e : {x : Fin n // x ≠ u} ≃ {y : Fin n // y ≠ v},
    ∀ x y : {x : Fin n // x ≠ u}, T.adj x.1 y.1 ↔ T.adj (e x).1 (e y).1

/-- A tournament is link-irregular if no two distinct vertices have isomorphic directed links. -/
def IsLinkIrregular {n : ℕ} (T : Tournament n) : Prop :=
  ∀ u v : Fin n, u ≠ v → ¬ HasIsoLink T u v

/-- Conjecture from arXiv:2512.20494 ("On Link-irregular Digraphs"): for every `n ≥ 2`,
a link-irregular tournament on `n` vertices exists if and only if `n ≥ 6`. -/
theorem main :
    ∀ n : ℕ, 2 ≤ n → ((∃ T : Tournament n, IsLinkIrregular T) ↔ 6 ≤ n) := by
  sorry

end OMA.S_arxiv_2512_20494
