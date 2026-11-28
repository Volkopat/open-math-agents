import Mathlib

namespace OMA.S_arxiv_2601_03293

/-- The Generalized Petersen graph `GP(n, k)` on `2n` vertices `Fin n ⊕ Fin n`:
`Sum.inl i` forms the outer `n`-cycle `u_0, ..., u_{n-1}`, `Sum.inr i` forms the inner star
with step `k`, and spokes join `Sum.inl i` to `Sum.inr i`. -/
def genPetersen (n k : ℕ) : SimpleGraph (Fin n ⊕ Fin n) where
  Adj x y :=
    match x, y with
    | Sum.inl i, Sum.inl j => i ≠ j ∧ ((i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val)
    | Sum.inl i, Sum.inr j => i = j
    | Sum.inr i, Sum.inl j => i = j
    | Sum.inr i, Sum.inr j => i ≠ j ∧ ((i.val + k) % n = j.val ∨ (j.val + k) % n = i.val)
  symm := ⟨by
    rintro (i | i) (j | j) h
    · exact ⟨h.1.symm, h.2.symm⟩
    · exact h.symm
    · exact h.symm
    · exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by
    rintro (i | i) h <;> exact h.1 rfl⟩

/-- The independence polynomial `I(G, x) = ∑_{S independent} x^{|S|}` of a finite simple graph `G`. -/
noncomputable def indepPoly {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Polynomial ℝ := by
  classical
  exact ∑ S ∈ (Finset.univ : Finset (Finset V)).filter
      (fun S => ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v),
    Polynomial.X ^ S.card

/-- A real polynomial is real-rooted if all of its complex roots lie on the real axis. -/
def IsRealRooted (P : Polynomial ℝ) : Prop :=
  ∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).eval z = 0 → z.im = 0

/-- Conjecture from arXiv:2601.03293 ("Parity-Dependent Real-Rootedness in Independence
Polynomials of Generalized Petersen Graphs"): for all `n ≥ 3` and `1 ≤ k < n / 2`,
the independence polynomial `I(GP(n, k), x)` is real-rooted if and only if `k` is even. -/
theorem main :
    ∀ (n k : ℕ), 3 ≤ n → 1 ≤ k → 2 * k < n →
      (IsRealRooted (indepPoly (genPetersen n k)) ↔ Even k) := by
  sorry

end OMA.S_arxiv_2601_03293
