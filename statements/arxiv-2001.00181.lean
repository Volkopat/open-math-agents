import Mathlib

namespace OMA.S_arxiv_2001_00181

/-- The squid graph `Sq(2n - 1; 1^n)` on `3n - 1` vertices (`n ≥ 2`):
vertices `0, ..., 2n - 2` form an odd cycle `C_{2n - 1}` and vertices
`2n - 1, ..., 3n - 2` are `n` pendant leaves attached to the hub vertex `0`. -/
def squidGraph (n : ℕ) : SimpleGraph (Fin (3 * n - 1)) where
  Adj u v :=
    (u.val < 2 * n - 1 ∧ v.val < 2 * n - 1 ∧
      (v.val = u.val + 1 ∨ u.val = v.val + 1 ∨
        (u.val = 0 ∧ v.val = 2 * n - 2 ∧ 0 < 2 * n - 2) ∨
        (v.val = 0 ∧ u.val = 2 * n - 2 ∧ 0 < 2 * n - 2))) ∨
    (u.val = 0 ∧ 2 * n - 1 ≤ v.val) ∨
    (v.val = 0 ∧ 2 * n - 1 ≤ u.val)
  symm := ⟨by
    intro u v h
    rcases h with ⟨hu, hv, h1 | h2 | h3 | h4⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨hv, hu, Or.inr (Or.inl h1)⟩
    · exact Or.inl ⟨hv, hu, Or.inl h2⟩
    · exact Or.inl ⟨hv, hu, Or.inr (Or.inr (Or.inr h3))⟩
    · exact Or.inl ⟨hv, hu, Or.inr (Or.inr (Or.inl h4))⟩
    · exact Or.inr (Or.inr ⟨h1, h2⟩)
    · exact Or.inr (Or.inl ⟨h1, h2⟩)⟩
  loopless := ⟨by
    intro u h
    rcases h with ⟨hu, _, h1 | h2 | h3 | h4⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega⟩

/-- A partition of `N`: a weakly decreasing list of positive integers summing to `N`. -/
def IsPartitionOf (N : ℕ) (lam : List ℕ) : Prop :=
  lam.sum = N ∧ (∀ x ∈ lam, 0 < x) ∧ lam.Pairwise (· ≥ ·)

/-- Monomial coefficient `[x^w] X_G` of Stanley's chromatic symmetric function `X_G`:
the number of proper `k`-colorings of `G` in which each color `c : Fin k` is used
exactly `w c` times. -/
noncomputable def chromCoeff {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) (w : Fin k → ℕ) : ℕ :=
  (@Finset.filter (V → Fin k)
    (fun f => (∀ u v, G.Adj u v → f u ≠ f v) ∧
      ∀ c : Fin k, (Finset.univ.filter (fun v => f v = c)).card = w c)
    (Classical.decPred _) Finset.univ).card

/-- A semistandard Young tableau of shape `lam` with entries in `Fin k` and content `w`. -/
def IsSSYT (lam : List ℕ) (k : ℕ) (w : Fin k → ℕ)
    (T : (r : Fin lam.length) → Fin (lam.get r) → Fin k) : Prop :=
  (∀ (r : Fin lam.length) (c₁ c₂ : Fin (lam.get r)), c₁.val ≤ c₂.val → T r c₁ ≤ T r c₂) ∧
  (∀ (r₁ r₂ : Fin lam.length) (c₁ : Fin (lam.get r₁)) (c₂ : Fin (lam.get r₂)),
    r₁.val < r₂.val → c₁.val = c₂.val → T r₁ c₁ < T r₂ c₂) ∧
  (∀ col : Fin k,
    (Finset.univ.filter (fun p : Sigma (fun r : Fin lam.length => Fin (lam.get r)) =>
      T p.1 p.2 = col)).card = w col)

/-- The Kostka number `K_{lam, w}` = `[x^w] s_lam`, the number of semistandard Young tableaux
of shape `lam` with entries in `Fin k` and content `w`. -/
noncomputable def kostka (lam : List ℕ) (k : ℕ) (w : Fin k → ℕ) : ℕ :=
  (@Finset.filter ((r : Fin lam.length) → Fin (lam.get r) → Fin k)
    (fun T => IsSSYT lam k w T)
    (Classical.decPred _) Finset.univ).card

/-- A graph `G` is Schur-positive if its chromatic symmetric function `X_G` is a nonnegative
real linear combination of Schur functions `s_lam` over partitions `lam` of `|V(G)|`, i.e.,
for every number of variables `k` and every monomial exponent `w : Fin k → ℕ`,
`[x^w] X_G = ∑_{lam ∈ S} c(lam) * [x^w] s_lam`. -/
def IsSchurPositive {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∃ (S : Finset (List ℕ)) (c : List ℕ → ℝ),
    (∀ lam ∈ S, IsPartitionOf (Fintype.card V) lam ∧ 0 ≤ c lam) ∧
    ∀ (k : ℕ) (w : Fin k → ℕ),
      (chromCoeff G k w : ℝ) = ∑ lam ∈ S, c lam * (kostka lam k w : ℝ)

/-- Conjecture (Wang & Wang 2020, arXiv:2001.00181; proved by Li–Li–Yang–Zhang):
For every `n ≥ 3`, the squid graph `Sq(2n - 1; 1^n)` is not Schur-positive. -/
theorem main :
    ∀ n : ℕ, 3 ≤ n → ¬ IsSchurPositive (squidGraph n) := by
  sorry

end OMA.S_arxiv_2001_00181
