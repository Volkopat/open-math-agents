import Mathlib

/-!
# Illumination (Levi–Hadwiger–Gohberg–Markus) conjecture

Source: https://en.wikipedia.org/wiki/Levi%E2%80%93Hadwiger_conjecture
(the article "Hadwiger conjecture (combinatorial geometry)").
Credit: @jagraj28

The article states the conjecture formally: if `K` is a convex body in `ℝⁿ`, there are `2ⁿ`
scalars `sᵢ` with `0 < sᵢ < 1` and `2ⁿ` translation vectors `vᵢ` with
`K ⊆ ⋃ᵢ (sᵢ K + vᵢ)`; furthermore the bound `2ⁿ` is necessary if and only if `K` is a
parallelepiped. It is open for `n ≥ 3` (Levi proved the case `n = 2`). The illumination form is
equivalent (Boltyansky) and is not stated here.

Formalization notes:
* `ℝⁿ` is `EuclideanSpace ℝ (Fin n)`. A convex body is a compact convex set with nonempty
  interior, the meaning in the article's lead and in the catalogue entry. (The article's
  "Formal statement" section says "bounded convex set"; the standard sources, for example
  Brass–Moser–Pach, use convex bodies.)
* `CoveredBy K m`: `K` lies in the union of `m` images `{s • x + v | x ∈ K}` with `0 < s < 1`.
  Repetitions are allowed, so this is "at most `m` smaller homothetic copies".
* "The bound `2ⁿ` is necessary" means that `2ⁿ - 1` copies do not suffice.
* A parallelepiped is a translate of Mathlib's `parallelepiped w` for `n` linearly independent
  vectors `w`.
* `main` is the conjunction of the two parts of the conjecture, for every dimension `n`.
-/

namespace OMA.S_wpc_illumination_conjecture

/-- `K` is covered by `m` smaller homothetic copies `s • K + v` (with `0 < s < 1`) of itself. -/
def CoveredBy {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (m : ℕ) : Prop :=
  ∃ (s : Fin m → ℝ) (v : Fin m → EuclideanSpace ℝ (Fin n)),
    (∀ i, 0 < s i ∧ s i < 1) ∧ K ⊆ ⋃ i, (fun x => s i • x + v i) '' K

/-- `K` is a (non-degenerate) parallelepiped: a translate of the parallelepiped spanned by `n`
linearly independent vectors. -/
def IsParallelepiped {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ (w : Fin n → EuclideanSpace ℝ (Fin n)) (c : EuclideanSpace ℝ (Fin n)),
    LinearIndependent ℝ w ∧ K = (fun x => x + c) '' parallelepiped w

/-- The Levi–Hadwiger covering conjecture: every convex body in `ℝⁿ` is covered by `2ⁿ` smaller
homothetic copies of itself, and `2ⁿ` copies are needed exactly for parallelepipeds. -/
theorem main :
    ∀ (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))),
      Convex ℝ K → IsCompact K → (interior K).Nonempty →
        CoveredBy K (2 ^ n) ∧ (¬ CoveredBy K (2 ^ n - 1) ↔ IsParallelepiped K) := by
  sorry

end OMA.S_wpc_illumination_conjecture
