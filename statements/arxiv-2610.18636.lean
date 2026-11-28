import Mathlib

namespace OMA.S_arxiv_2610_18636

/-- The complete tripartite graph on `3 * n` vertices whose three independent parts are
`{0, ..., a - 1}`, `{a, ..., a + b - 1}`, and `{a + b, ..., 3 * n - 1}`.
In particular, `completeTripartite3 n n n` is `K_{n,n,n}` and for `n ≥ 4`,
`completeTripartite3 n (n - 1) n` is `K_{n-1,n,n+1}`. -/
def completeTripartite3 (n a b : ℕ) : SimpleGraph (Fin (3 * n)) where
  Adj u v :=
    (if u.val < a then (0 : Fin 3) else if u.val < a + b then 1 else 2) ≠
    (if v.val < a then (0 : Fin 3) else if v.val < a + b then 1 else 2)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h rfl⟩

/-- `lam : Fin N → ℝ` is the ordered (non-decreasing) adjacency spectrum of a simple graph `G`
on `Fin N`: it is monotone and the characteristic polynomial of the adjacency matrix of `G`
factors as `∏ i, (X - C (lam i))`. -/
def IsOrderedSpectrum {N : ℕ} (G : SimpleGraph (Fin N)) (lam : Fin N → ℝ) : Prop := by
  classical
  exact Monotone lam ∧
    (G.adjMatrix ℝ).charpoly = ∏ i : Fin N, (Polynomial.X - Polynomial.C (lam i))

/-- Conjectures of Abdollahi and Zakeri (Ars Math. Contemp. 22(1) (2022) P1.06; disproved in
arXiv:2610.18636): for every `n ≥ 4`, among all simple graphs on `3n` vertices not isomorphic to
`K_{n,n,n}`, both the `ℓ_1` and `ℓ_2` spectral distances from `K_{n,n,n}` are minimized at
`K_{n-1,n,n+1}`. -/
theorem main :
    ∀ (n : ℕ), 4 ≤ n →
      ∀ (H : SimpleGraph (Fin (3 * n))),
        ¬ Nonempty (H ≃g completeTripartite3 n n n) →
        ∀ (lam0 lam1 lam2 : Fin (3 * n) → ℝ),
          IsOrderedSpectrum (completeTripartite3 n n n) lam0 →
          IsOrderedSpectrum (completeTripartite3 n (n - 1) n) lam1 →
          IsOrderedSpectrum H lam2 →
          (∑ i : Fin (3 * n), |lam0 i - lam1 i| ≤ ∑ i : Fin (3 * n), |lam0 i - lam2 i|) ∧
          (∑ i : Fin (3 * n), (lam0 i - lam1 i) ^ 2 ≤
            ∑ i : Fin (3 * n), (lam0 i - lam2 i) ^ 2) := by
  sorry

end OMA.S_arxiv_2610_18636
