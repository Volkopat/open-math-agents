import Mathlib

namespace OMA.S_arxiv_2609_00462

/-- A `V × V` matrix `u` over a unital ring `R` is a magic unitary if its entries are idempotent,
entries in the same row or column are pairwise orthogonal, and every row and column sums to `1`. -/
def IsMagicUnitary {V : Type*} [Fintype V] [DecidableEq V] {R : Type*} [Ring R]
    (u : Matrix V V R) : Prop :=
  (∀ i j, u i j * u i j = u i j) ∧
  (∀ i j₁ j₂, j₁ ≠ j₂ → u i j₁ * u i j₂ = 0) ∧
  (∀ i₁ i₂ j, i₁ ≠ i₂ → u i₁ j * u i₂ j = 0) ∧
  (∀ i, ∑ j, u i j = 1) ∧
  (∀ j, ∑ i, u i j = 1)

/-- Adjacency matrix of the circulant graph `Cay(ZMod p, S)` over `ℂ`: entry `(x, y)` is `1` if
`x - y ∈ S` and `0` otherwise. -/
noncomputable def circulantAdj (p : ℕ) [NeZero p] (S : Finset (ZMod p)) :
    Matrix (ZMod p) (ZMod p) ℂ :=
  Matrix.of fun x y => if x - y ∈ S then 1 else 0

/-- A graph with adjacency matrix `A : Matrix V V ℂ` has no quantum symmetry (equivalently, its
quantum permutation algebra `A(X) = A_s(n) / ⟨A u = u A⟩` is commutative) if every magic unitary
`u` over any unital `ℂ`-algebra `R` commuting with `A` has pairwise commuting entries. -/
def HasNoQuantumSymmetry {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℂ) : Prop :=
  ∀ (R : Type) [Ring R] [Algebra ℂ R] (u : Matrix V V R),
    IsMagicUnitary u →
    u * A.map (algebraMap ℂ R) = A.map (algebraMap ℂ R) * u →
    ∀ i j k l : V, u i j * u k l = u k l * u i j

/-- The multiplier group `E(S) = {a ∈ (ZMod p)ˣ | a · S = S}` of a connection set `S ⊆ ZMod p`. -/
def multiplierGroup (p : ℕ) [NeZero p] (S : Finset (ZMod p)) : Finset (ZMod p) :=
  Finset.univ.filter fun a => a ≠ 0 ∧ S.image (fun x => a * x) = S

/-- Connection set `S = {±1, ±2, ±4, ±8, ±15} ⊆ ZMod 31` of Chassaniol's open graph
`C_31(2, 4, 8, 15)` (the cubic residues modulo `31`). -/
def connC31 : Finset (ZMod 31) :=
  {1, -1, 2, -2, 4, -4, 8, -8, 15, -15}

/-- Connection set `S = {±1, ±4, ±10, ±16, ±18} ⊆ ZMod 41` of Chassaniol's open graph
`C_41(4, 10, 16, 18)` (the quartic residues modulo `41`). -/
def connC41 : Finset (ZMod 41) :=
  {1, -1, 4, -4, 10, -10, 16, -16, 18, -18}

/-- Marashdeh (arXiv:2609.00462), Theorem D (Theorems 6.2 & 6.5), settling the two prime-order
circulants `C_31(2, 4, 8, 15)` and `C_41(4, 10, 16, 18)` left open by Chassaniol and completing
the classification for prime-order circulants of type at most `10`:
1. `C_31(2, 4, 8, 15)` has no quantum symmetry;
2. `C_41(4, 10, 16, 18)` has no quantum symmetry;
3. Every nontrivial symmetric circulant graph of prime order `p ≥ 5` and type `|E(S)| ≤ 10`
   has no quantum symmetry. -/
theorem main :
    HasNoQuantumSymmetry (circulantAdj 31 connC31) ∧
    HasNoQuantumSymmetry (circulantAdj 41 connC41) ∧
    ∀ (p : ℕ) [Fact (Nat.Prime p)] (hp : 5 ≤ p) (S : Finset (ZMod p)),
      S.Nonempty →
      (0 : ZMod p) ∉ S →
      S ≠ Finset.univ.erase 0 →
      (∀ x ∈ S, -x ∈ S) →
      (multiplierGroup p S).card ≤ 10 →
      HasNoQuantumSymmetry (circulantAdj p S) := by
  sorry

end OMA.S_arxiv_2609_00462
