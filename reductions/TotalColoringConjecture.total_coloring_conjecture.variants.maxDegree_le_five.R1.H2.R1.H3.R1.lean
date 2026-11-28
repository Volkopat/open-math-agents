import OMAReductions.R_TotalColoringConjecture_total_coloring_conjecture_variants_maxDegree_le_five_R1_H2_R1
import Mathlib

/-! Kostochka's matched multigraph theorem uses two reusable results. A loopless
multigraph of maximum degree two decomposes into paths and cycles, including
doubled edges. A pair of degree-two simple graphs on folded vertices admits a
three-color palette in the absence of the Section 5 square obstruction. -/
namespace OMA.R_TotalColoringConjecture_total_coloring_conjecture_variants_maxDegree_le_five_R1_H2_R1_H3_R1
open SimpleGraph
open scoped Classical

/-- Lists cover the components. A cyclic row of length two represents a doubled edge. -/
def H1 : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W] (k : W → W → ℕ),
  (∀ x y, k x y = k y x) → (∀ x, k x x = 0) → (∀ x, ∑ y, k x y ≤ 2) →
  let row (l : List W) (c : Bool) (x y : W) :=
    if ∃ i : Fin l.length, (c = true ∨ i.val + 1 < l.length) ∧
      s(x,y) = s(l[i.val],l[(i.val+1)%l.length]'(Nat.mod_lt _ (Fin.pos i)))
    then (if c = true ∧ l.length = 2 then 2 else 1) else 0
  ∃ P : List (List W × Bool), (P.map (fun p => p.1.toFinset)).Pairwise Disjoint ∧
    (∀ x, ∃ p ∈ P, x ∈ p.1) ∧ ∀ p ∈ P, p.1.Nodup ∧ p.1 ≠ [] ∧
      ∀ x ∈ p.1, ∀ y, k x y = row p.1 p.2 x y

/-- A common three-color palette for the vertices of S and edges of F,
with incident colors excluded at the marked vertices. -/
def H2 : Prop :=
  ∀ (U : Type) [Fintype U] (S F : SimpleGraph U) (t : U → Bool),
    (∀ v, S.degree v ≤ 2) →
    (∀ v, F.degree v ≤ 2) →
    (∀ x y, F.Adj x y → t x = true → t y = true → S.Adj x y) →
    (∀ x y z, x ≠ z → F.Adj x y → F.Adj y z → ¬ (t x = true ∧ t y = true ∧ t z = true)) →
    (∀ s : Fin 4 ↪ U, (∀ i, t (s i) = true) → (∀ i, S.Adj (s i) (s (i+1))) →
      (∀ i, F.Adj (s i) (s (i+1)) ∨ F.Adj (s i) (s (i+3))) →
      ∀ x y, t x = false → t y = false → F.Adj (s 0) x → F.Adj (s 2) x →
        F.Adj (s 1) y → F.Adj (s 3) y → False) →
    ∃ (c : U → Fin 3) (h : F.edgeSet → Fin 3),
      (∀ x y, S.Adj x y → c x ≠ c y) ∧
      (∀ e f, e ≠ f → (∃ v : U, v ∈ e.val ∧ v ∈ f.val) → h e ≠ h f) ∧
      (∀ v e, t v = true → v ∈ e.val → h e ≠ c v)

/-- A counterexample to seven-total-coloring yields a failed row on its
vertex set or a failed palette on the unordered pairs of its vertices. -/
def H3 : Prop :=
  ∀ (W : Type) [Fintype W] (A : SimpleGraph W) (mult : W → W → ℕ),
    (∀ x y, mult x y = mult y x) → (∀ x, mult x x = 0) →
    (∀ x, ∑ y, mult x y = 5) → (∀ x y, A.Adj x y ↔ 0 < mult x y) →
    (∃ M : A.Subgraph, M.IsPerfectMatching) →
    ¬ (∃ (vc : W → Fin 7) (ec : W → W → Finset (Fin 7)),
        (∀ x y, ec x y = ec y x) ∧ (∀ x y, (ec x y).card = mult x y) ∧
        (∀ x y, A.Adj x y → vc x ≠ vc y) ∧ (∀ x y, vc x ∉ ec x y) ∧
        (∀ x y z, y ≠ z → Disjoint (ec x y) (ec x z))) →
    (∃ k : W → W → ℕ, (∀ x y, k x y = k y x) ∧ (∀ x, k x x = 0) ∧
      (∀ x, ∑ y, k x y ≤ 2) ∧ ¬ (
        let row (l : List W) (c : Bool) (x y : W) :=
          if ∃ i : Fin l.length, (c = true ∨ i.val + 1 < l.length) ∧
            s(x,y) = s(l[i.val],l[(i.val+1)%l.length]'(Nat.mod_lt _ (Fin.pos i)))
          then (if c = true ∧ l.length = 2 then 2 else 1) else 0
        ∃ P : List (List W × Bool), (P.map (fun p => p.1.toFinset)).Pairwise Disjoint ∧
          (∀ x, ∃ p ∈ P, x ∈ p.1) ∧ ∀ p ∈ P, p.1.Nodup ∧ p.1 ≠ [] ∧
            ∀ x ∈ p.1, ∀ y, k x y = row p.1 p.2 x y)) ∨ (
      let U := Sym2 W
      ∃ (S F : SimpleGraph U) (t : U → Bool),
        (∀ v, S.degree v ≤ 2) ∧
        (∀ v, F.degree v ≤ 2) ∧
        (∀ x y, F.Adj x y → t x = true → t y = true → S.Adj x y) ∧
        (∀ x y z, x ≠ z → F.Adj x y → F.Adj y z → ¬ (t x = true ∧ t y = true ∧ t z = true)) ∧
        (∀ s : Fin 4 ↪ U, (∀ i, t (s i) = true) → (∀ i, S.Adj (s i) (s (i+1))) →
        (∀ i, F.Adj (s i) (s (i+1)) ∨ F.Adj (s i) (s (i+3))) →
        ∀ x y, t x = false → t y = false → F.Adj (s 0) x → F.Adj (s 2) x →
          F.Adj (s 1) y → F.Adj (s 3) y → False) ∧
        ¬ ∃ (c : U → Fin 3) (h : F.edgeSet → Fin 3),
        (∀ x y, S.Adj x y → c x ≠ c y) ∧
        (∀ e f, e ≠ f → (∃ v : U, v ∈ e.val ∧ v ∈ f.val) → h e ≠ h f) ∧
        (∀ v e, t v = true → v ∈ e.val → h e ≠ c v))

theorem main : H1 → H2 → H3 → OMA.R_TotalColoringConjecture_total_coloring_conjecture_variants_maxDegree_le_five_R1_H2_R1.H3 := by
  classical
  intro rows paint transfer W _ A m symm loops regular support matching
  by_contra no
  rcases transfer W A m symm loops regular support matching no with failed | failed
  · obtain ⟨k,ks,kl,kd,missing⟩ := failed
    exact missing (rows W k ks kl kd)
  · obtain ⟨S,F,t,sd,fd,inside,three,square,missing⟩ := failed
    exact missing (paint (Sym2 W) S F t sd fd inside three square)

end OMA.R_TotalColoringConjecture_total_coloring_conjecture_variants_maxDegree_le_five_R1_H2_R1_H3_R1
