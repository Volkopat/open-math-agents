import Mathlib

/-!
# The nearest Kronecker product of a permutation and an orthogonal matrix

Source: Nick, https://mathoverflow.net/questions/228115 (CC BY-SA 3.0).
Contribution by @connoranderson.

The squared Frobenius objective is the blockwise loss below. For a fixed
permutation it reduces to the classical orthogonal Procrustes problem
(P. H. Schönemann, Psychometrika 31 (1966), 1–10). The outer optimization
is finite. The last clause gives a MaxCut reduction with entries in
{-1,0,1}: a graph edge joins s i to t i, and a Boolean partition scores
one point for each edge crossing it.
-/
namespace OMA.S_mo_228115
open Matrix Finset
abbrev Sq (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
abbrev Blocks (ι : Type*) (n : ℕ) := Matrix (ι × Fin n) (ι × Fin n) ℝ
abbrev Orth (n : ℕ) := unitary (Sq n)
noncomputable def col {n : ℕ} (S : Sq n) (j : Fin n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (Sᵀ j)
noncomputable def nuclear {n : ℕ} (S : Sq n) : ℝ :=
  ∑ j,Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self S).eigenvalues j)
noncomputable def score {n : ℕ} (S Q : Sq n) : ℝ := (Qᵀ*S).trace
noncomputable def blockSum {ι : Type*} [Fintype ι] {n : ℕ} (A : Blocks ι n) (p : Equiv.Perm ι) : Sq n :=
  Matrix.of fun i j => ∑ a,A (a,i) (p a,j)
noncomputable def loss {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Blocks ι n) (p : Equiv.Perm ι) (Q : Orth n) : ℝ :=
  ∑ a,∑ b,∑ i,∑ j,(A (a,i) (b,j)-(if p a=b then (Q:Sq n) i j else 0))^2
noncomputable def sizeSq {ι : Type*} [Fintype ι] {n : ℕ} (A : Blocks ι n) : ℝ :=
  ∑ a,∑ b,∑ i,∑ j,(A (a,i) (b,j))^2

def cut {v e : ℕ} (s t : Fin e → Fin v) (b : Fin v → Bool) : ℕ :=
  ∑ a, if b (s a)≠b (t a) then 1 else 0
noncomputable def incidence {v e : ℕ} (s t : Fin e → Fin v) (i : Fin v) (l : Fin (e+1)) : ℝ :=
  Fin.cases 0 (fun a => (if s a=i then 1 else 0)-(if t a=i then 1 else 0)) l
noncomputable def cutInput {v e : ℕ} (s t : Fin e → Fin v) : Blocks (Fin v × Bool) (e+1) :=
  Matrix.of fun a b => if a.1.2=false ∧ a.1.1=b.1.1 ∧ b.2=0 then
    (if b.1.2 then -1 else 1)*incidence s t a.1.1 a.2 else 0

theorem main :
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (A : Blocks ι n),
      (∃ (p : Equiv.Perm ι) (Q : Orth n), ∀ r U,loss A p Q≤loss A r U) ∧
      (∀ p : Equiv.Perm ι, IsLeast (Set.range (fun Q : Orth n => loss A p Q))
        (sizeSq A+(Fintype.card ι:ℝ)*n-2*nuclear (blockSum A p))) ∧
      (∀ (p : Equiv.Perm ι) (Q : Orth n), (∀ r U,loss A p Q≤loss A r U) ↔
        (∀ r,nuclear (blockSum A r)≤nuclear (blockSum A p)) ∧ score (blockSum A p) Q=nuclear (blockSum A p))) ∧
    (∀ (v e : ℕ) (s t : Fin e → Fin v),
      (∀ i j,cutInput s t i j= -1 ∨ cutInput s t i j=0 ∨ cutInput s t i j=1) ∧
      ∀ k : ℕ, (∃ p : Equiv.Perm (Fin v × Bool),4*(k:ℝ)≤(nuclear (blockSum (cutInput s t) p))^2) ↔
        ∃ b : Fin v → Bool,k≤cut s t b) := by sorry

end OMA.S_mo_228115
