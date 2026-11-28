import Mathlib

/-!
# Cyclic Hamilton cycle decompositions of carousel tournaments

Source: https://arxiv.org/abs/2610.07102, Problem 1.2 (Hongci Liao, Yongju Peng, Guang Li and
Yingbin Ma, Oct 2026)

For an odd integer n, the carousel tournament T_n is the Cayley tournament on Z_n with
connection set {1, 2, ..., (n-1)/2}: there is an arc from x to y exactly when y - x is one of
1, 2, ..., (n-1)/2. The paper asks whether T_n has a Hamilton decomposition invariant under
translation by 1 (a cyclic Hamilton cycle decomposition), and states the question as Problem 1.2:
for which odd integers n does T_n admit one? The answer is yes when n is prime, and the paper
proves it when n = pq for primes 7 <= p < q; all other odd composite orders are left open.

Formalized claim: the yes or no form of the question, namely that the answer is every odd n.
That is, for every odd n >= 3, the tournament T_n has a cyclic Hamilton cycle decomposition.

Formalization notes:
* Vertices are the elements of `ZMod n`. `IsArc n x y` says that (y - x), read as a residue in
  0, ..., n-1, lies between 1 and (n-1)/2.
* A Hamilton cycle is encoded by its successor permutation σ: σ is a single cycle that moves every
  vertex, and every step x to σ x is an arc of T_n.
* A Hamilton decomposition is a set F of Hamilton cycles such that every arc of T_n lies on
  exactly one cycle of F. Since every step of a cycle of F is an arc of T_n, the arc sets of the
  cycles of F partition the arcs of T_n.
* Invariance under translation by 1: for every σ in F, the translated cycle
  x ↦ σ (x - 1) + 1, which is t * σ * t⁻¹ for the translation t = `Equiv.addRight 1`, is again
  in F.
* n = 1 is excluded: T_1 has a single vertex and no arcs.
-/

namespace OMA.S_arxiv_2610_07102

/-- The arcs of the carousel tournament T_n: from x to y when y - x is one of 1, ..., (n-1)/2. -/
def IsArc (n : ℕ) (x y : ZMod n) : Prop :=
  (y - x).val ∈ Finset.Icc 1 ((n - 1) / 2)

/-- σ is (the successor map of) a Hamilton cycle of T_n. -/
def IsHamCycle (n : ℕ) (σ : Equiv.Perm (ZMod n)) : Prop :=
  σ.IsCycle ∧ (∀ x, σ x ≠ x) ∧ ∀ x, IsArc n x (σ x)

/-- F is a Hamilton decomposition of T_n invariant under translation by 1. -/
def IsCyclicHamDecomp (n : ℕ) (F : Set (Equiv.Perm (ZMod n))) : Prop :=
  (∀ σ ∈ F, IsHamCycle n σ) ∧
  (∀ x y, IsArc n x y → ∃! σ, σ ∈ F ∧ σ x = y) ∧
  (∀ σ ∈ F, Equiv.addRight (1 : ZMod n) * σ * (Equiv.addRight (1 : ZMod n))⁻¹ ∈ F)

/-- Problem 1.2 of arXiv 2610.07102, in yes or no form: every carousel tournament T_n with n odd
and n >= 3 has a cyclic Hamilton cycle decomposition. -/
theorem main :
    ∀ n : ℕ, Odd n → 3 ≤ n → ∃ F : Set (Equiv.Perm (ZMod n)), IsCyclicHamDecomp n F := by
  sorry

end OMA.S_arxiv_2610_07102
