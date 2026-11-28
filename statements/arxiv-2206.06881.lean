import Mathlib

/-!
# Combinatorial Derived Matroids: the weak-order (categorical genericity) conjecture

Source: https://arxiv.org/abs/2206.06881
Credit: @mjkang-estrella

O. Kuznetsova, R. Freij-Hollanti, R. Jurrius, *Combinatorial Derived Matroids*, arXiv:2206.06881
(v3, December 2022), Section 8.1, **Conjecture 8.4**; it is Conjecture 43 of the journal version
(Electron. J. Combin. 30(2) (2023), P2.8) and Conjecture 8.5 of arXiv v1.

> **Conjecture 8.4.** Let `M` be a representable matroid with set of circuits `C`. Then
> `δM ≥ δ_OW(R)` for every representation `R` of `M`, where the order relation is the weak
> order on the set of matroids on `C`.

The paper's abstract says "We formulate conjectures relating our construction to previous
definitions of derived matroids". Those conjectures are in Section 8: 8.4 (above, against the
Oxley–Wang derived matroid), 8.6 (an algebraic-geometric genericity statement: for every matroid
`N ≠ δM` on `C` with `V_N(M)` nonempty, `V_N(M)` has positive codimension in the variety `V(M)`
of representations) and 8.7 (an adjoint of `M`, when one exists, can be chosen equal to `δ(M*)`,
and every adjoint is below `δ(M*)` in the weak order). They are separate statements about
different objects, not one combined claim. This file states Conjecture 8.4, the one whose
objects (`δM`, `δ_OW(R)`, the weak order) are all defined in the paper itself.

## The definitions, against the source

* *Matroids, rank, nullity* (Definitions 2.1, 2.3). A matroid is a Mathlib `Matroid E` on a
  finite type `E` whose ground set is all of `E`. The paper's dependent sets are Mathlib's
  `M.Dep`, and its circuits ("inclusion-minimal dependent sets") are Mathlib's `M.IsCircuit`.
  Definition 2.3 sets `r(S) = max{|T| : T ⊆ S, T independent}` (the printed condition
  `S ∉ D` is a typo for `T ∉ D`) and `n(S) = |S| - r(S)`. `rank` is that maximum, written as the
  supremum of the cardinalities of the independent subsets of `S` (zero for `S = ∅`), and
  `nullity` subtracts it. For a finite matroid this is Mathlib's `Matroid.rk`.
* *Representations* (Section 2, after Definition 2.3). `M(R)` has the columns of `R` as its
  ground set, and a set of columns is independent when the submatrix they form has full column
  rank, i.e. when those columns are linearly independent. `M` is representable over `F` if
  `M(R) = M` for some `R ∈ F^{m×E}`. `IsRepresentation M R` says exactly that `M(R) = M`: the
  ground set of `M` is `E` (the column index set of `R`) and `I ⊆ E` is independent in `M` if
  and only if the columns `(R i e)_i`, `e ∈ I`, are linearly independent. The conjecture
  quantifies over every field `F`, every `m`, and every `R ∈ F^{m×E}` representing `M`.
* *The ground set `C(M)`*. `Circuits M` is the type of circuits of `M`, each stored as a
  `Finset E` (every subset of the finite type `E` is finite).
* *`ε` and `↑`* (Definition 4.1). For a collection `D` of sets of circuits,
  `ε(D) = D ∪ {(A₁ ∪ A₂) \ {C} : A₁, A₂ ∈ D, A₁ ∩ A₂ ∉ D, C ∈ A₁ ∩ A₂}` and
  `↑D = {A : ∃ A' ∈ D, A' ⊆ A}`. These are `epsilon` and `upClosure`, word for word.
* *The stages* (Definition 4.2). `A₀ = {A ⊆ C : |A| > n(⋃_{C ∈ A} C)}` is `initial M`, where
  `support A` is the union `⋃_{C ∈ A} C` (Notation 4.5). Then `A_{i+1} = ↑ε(A_i)`. The paper
  prints "for `i ≥ 1`", which would leave `A₁` undefined; the recursion is meant to start at
  `i = 0` (the paper applies Lemma 4.6 "for every `i ≥ 0`" in Proposition 4.7, and in
  Section 5.3 writes an `A ∈ A₁ - A₀` as `(A₁ ∪ A₂) \ {C}` with `A₁, A₂ ∈ A₀`), so
  `stage M (i + 1)` is `↑ε(stage M i)` for every `i`.
* *`δM`* (Definition 4.3). The combinatorial derived matroid has ground set `C(M)` and dependent
  sets `A = ⋃_{i ≥ 0} A_i`; `DerivedDependent M A` says `A` lies in some stage. (The paper proves
  this is a matroid, Proposition 4.7; the statement only uses its dependent sets.)
* *Circuit vectors and `δ_OW`* (Section 3.2, Definition 3.3). Let `Q` be the row space of `R`
  (the code representing `M`). Its dual `Q^⊥` is `{x : R x = 0}`. A circuit vector of `Q` on a
  circuit `C` is a `q_C ∈ Q^⊥` with `supp(q_C) = C`; this is `IsCircuitVector R C q`. The
  Oxley–Wang derived matroid `δ_OW(R)` is the matroid on `C(M)` represented by the matrix whose
  column indexed by `C` is `q_C`. So a set `A` of circuits is dependent in `δ_OW(R)` exactly when
  the vectors `q_C`, `C ∈ A`, are linearly dependent; this is `OWDependent q A`. Circuit vectors
  are unique up to nonzero scalars (Section 3.2), so this does not depend on the choice of `q`.
  `main` asks for the inequality for every admissible choice `q`. Since circuit vectors exist
  for every circuit, this is equivalent to asking it for one choice, and the quantifier over
  `q` is never vacuous.
* *The weak order* (Definition 8.3). `M₁ ≥ M₂` when every dependent set of `M₁` is dependent in
  `M₂`. `WeakGE D₁ D₂` says this for the dependent-set predicates `D₁` of `δM` and `D₂` of
  `δ_OW(R)`, both matroids on the ground set `C(M)`.

Universes: the field and the ground set range over `Type`.
-/

namespace OMA.S_arxiv_2206_06881

variable {E : Type} [DecidableEq E]

/-- `R ∈ F^{m×E}` represents `M`, i.e. `M(R) = M`: the ground set of `M` is `E`, and a set of
columns is independent in `M` exactly when those columns of `R` are linearly independent. -/
def IsRepresentation {F : Type} [Field F] {m : ℕ} (M : Matroid E) (R : Matrix (Fin m) E F) :
    Prop :=
  M.E = Set.univ ∧ ∀ I : Set E, M.Indep I ↔ LinearIndepOn F (fun e => fun i => R i e) I

/-- The circuits of `M`: the ground set `C(M)` of the derived matroids. -/
abbrev Circuits (M : Matroid E) : Type := {C : Finset E // M.IsCircuit (C : Set E)}

/-- Definition 2.3: `r(S) = max{|T| : T ⊆ S, T independent}`. -/
noncomputable def rank (M : Matroid E) (S : Finset E) : ℕ := by
  classical
  exact (S.powerset.filter (fun T : Finset E => M.Indep (T : Set E))).sup Finset.card

/-- Definition 2.3: `n(S) = |S| - r(S)`. -/
noncomputable def nullity (M : Matroid E) (S : Finset E) : ℕ :=
  S.card - rank M S

/-- Notation 4.5: `supp(A) = ⋃_{C ∈ A} C`. -/
def support {M : Matroid E} (A : Finset (Circuits M)) : Finset E :=
  A.biUnion (fun C => C.1)

/-- Definition 4.1: `ε(D) = D ∪ {(A₁ ∪ A₂) \ {C} : A₁, A₂ ∈ D, A₁ ∩ A₂ ∉ D, C ∈ A₁ ∩ A₂}`. -/
def epsilon {α : Type} [DecidableEq α] (D : Set (Finset α)) : Set (Finset α) :=
  D ∪ {W | ∃ A₁ ∈ D, ∃ A₂ ∈ D, A₁ ∩ A₂ ∉ D ∧ ∃ C ∈ A₁ ∩ A₂, W = (A₁ ∪ A₂).erase C}

/-- Definition 4.1: `↑D = {A : ∃ A' ∈ D, A' ⊆ A}`. -/
def upClosure {α : Type} (D : Set (Finset α)) : Set (Finset α) :=
  {A | ∃ A' ∈ D, A' ⊆ A}

/-- Definition 4.2: `A₀ = {A ⊆ C(M) : |A| > n(⋃_{C ∈ A} C)}`. -/
noncomputable def initial (M : Matroid E) : Set (Finset (Circuits M)) :=
  {A | nullity M (support A) < A.card}

/-- Definition 4.2: `A₀` as above and `A_{i+1} = ↑ε(A_i)`. -/
noncomputable def stage (M : Matroid E) : ℕ → Set (Finset (Circuits M))
  | 0 => initial M
  | i + 1 => upClosure (epsilon (stage M i))

/-- Definition 4.3: the dependent sets of the combinatorial derived matroid `δM` are
`A = ⋃_{i ≥ 0} A_i`. -/
def DerivedDependent (M : Matroid E) (A : Finset (Circuits M)) : Prop :=
  ∃ i, A ∈ stage M i

/-- Section 3.2: `q` is a circuit vector of `R` on `C`: `q ∈ Q^⊥ = {x : R x = 0}` (where `Q` is
the row space of `R`) and `supp(q) = C`. -/
def IsCircuitVector [Fintype E] {F : Type} [Field F] {m : ℕ} (R : Matrix (Fin m) E F)
    (C : Finset E) (q : E → F) : Prop :=
  R.mulVec q = 0 ∧ ∀ e, q e ≠ 0 ↔ e ∈ C

/-- Definition 3.3: with `q_C` the column indexed by the circuit `C`, a set `A` of circuits is
dependent in `δ_OW(R)` when the vectors `q_C`, `C ∈ A`, are linearly dependent. -/
def OWDependent {F : Type} [Field F] {M : Matroid E} (q : Circuits M → E → F)
    (A : Finset (Circuits M)) : Prop :=
  ¬ LinearIndependent F (fun C : A => q C.1)

/-- Definition 8.3: the weak order `M₁ ≥ M₂` on matroids with a common ground set, in terms of
their dependent-set predicates: every dependent set of `M₁` is dependent in `M₂`. -/
def WeakGE {α : Type} (D₁ D₂ : Finset α → Prop) : Prop :=
  ∀ A, D₁ A → D₂ A

/-- **Conjecture 8.4** (arXiv v3; Conjecture 43 of the journal version). For every matroid `M`
on a finite set `E`, every field `F` and every representation `R ∈ F^{m×E}` of `M`, and every
choice `q` of circuit vectors of `R`, `δM ≥ δ_OW(R)` in the weak order. -/
theorem main :
    ∀ (F : Type) [Field F] (E : Type) [Fintype E] [DecidableEq E] (M : Matroid E) (m : ℕ)
      (R : Matrix (Fin m) E F), IsRepresentation M R →
      ∀ q : Circuits M → E → F, (∀ C : Circuits M, IsCircuitVector R C.1 (q C)) →
        WeakGE (DerivedDependent M) (OWDependent q) := by
  sorry

end OMA.S_arxiv_2206_06881
