import Mathlib

namespace OMA.S_arxiv_2210_09447

/-- Total degree of a monomial `m : Fin r → ℕ`. -/
def monDeg {r : ℕ} (m : Fin r → ℕ) : ℕ :=
  ∑ i : Fin r, m i

/-- A finite set `M` of monomials in `r` variables is a non-degenerate pure order ideal of
socle degree `e` if:
1. `M` is nonempty,
2. `M` is downward-closed under divisibility (`v ≤ u → v ∈ M`),
3. every monomial in `M` has degree at most `e` and divides some monomial in `M` of degree `e`
   (equivalently, all maximal elements of `M` have the same degree `e`), and
4. every variable `x_i` belongs to `M` (so the codimension is `r`). -/
def IsPureOrderIdeal {r : ℕ} (M : Finset (Fin r → ℕ)) (e : ℕ) : Prop :=
  M.Nonempty ∧
  (∀ u ∈ M, ∀ v : Fin r → ℕ, v ≤ u → v ∈ M) ∧
  (∀ u ∈ M, monDeg u ≤ e) ∧
  (∀ u ∈ M, ∃ w ∈ M, u ≤ w ∧ monDeg w = e) ∧
  (∀ i : Fin r, (fun j => if j = i then 1 else 0) ∈ M)

/-- The pure `O`-sequence (degree-count vector, equivalently the Hilbert function of the
associated level monomial Artinian algebra) of `M`. -/
def oSeq {r : ℕ} (M : Finset (Fin r → ℕ)) (d : ℕ) : ℕ :=
  (M.filter (fun m => monDeg m = d)).card

/-- Question (Iarrobino; answered in the negative by Zanello, arXiv:2210.09447):
Are all pure `O`-sequences (and hence all level Hilbert functions) log-concave? -/
theorem main :
    ∀ (r e : ℕ) (M : Finset (Fin r → ℕ)),
      IsPureOrderIdeal M e →
      ∀ d : ℕ, 1 ≤ d → d + 1 ≤ e →
        oSeq M (d - 1) * oSeq M (d + 1) ≤ (oSeq M d) ^ 2 := by
  sorry

end OMA.S_arxiv_2210_09447
