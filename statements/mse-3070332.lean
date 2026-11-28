import Mathlib

/-!
# Can Erdős-Turán $\frac{5}{8}$ theorem be generalised that way?

Source: https://math.stackexchange.com/questions/3070332/can-erd%c5%91s-tur%c3%a1n-frac58-theorem-be-generalised-that-way
Credit: @mgv27

For a group word $w$ over an alphabet of $n$ symbols, let $\mathfrak{U}_w$ be the variety of
all groups $G$ satisfying the identity $w(a_1, \dots, a_n) = e$ for all $a_1, \dots, a_n \in G$.
Is it true that for any group word $w$ there exists a real number $\epsilon(w) > 0$ such that
any finite group $G$ is in $\mathfrak{U}_w$ iff
$$\frac{|\{(a_1, \dots, a_n) \in G^n : w(a_1, \dots, a_n) = e\}|}{|G|^n} > 1 - \epsilon(w)?$$
(For $w = [a, b]$ this is the Erdős–Turán $5/8$ theorem with $\epsilon = 3/8$.)

Formalization notes:
* A group word in `n` letters is an element `w : FreeGroup (Fin n)`; its value at
  `a : Fin n → G` is `FreeGroup.lift a w`.
* `G` ranges over finite groups in `Type`; the proportion is computed in `ℝ` with
  `Nat.card` of the solution set over `(Fintype.card G)^n`.
* The direction "in the variety ⟹ proportion `= 1 > 1 - ε`" is automatic, so the content is a
  gap: groups outside `𝔘_w` have proportion at most `1 - ε(w)`. The iff is kept as asked.
* Comments point to partial results (commutator-like words, metabelian and 2-Engel words) and
  note the general question as open (Dixon, "Probabilistic Group Theory").
-/

namespace OMA.S_mse_3070332

/-- `G` lies in the variety `𝔘_w`: the law `w = e` holds identically in `G`. -/
def SatisfiesLaw {n : ℕ} (w : FreeGroup (Fin n)) (G : Type) [Group G] : Prop :=
  ∀ a : Fin n → G, FreeGroup.lift a w = 1

/-- The proportion of tuples `(a_1, …, a_n) ∈ G^n` with `w(a_1, …, a_n) = e`. -/
noncomputable def lawProb {n : ℕ} (w : FreeGroup (Fin n)) (G : Type) [Group G] [Fintype G] :
    ℝ :=
  (Nat.card {a : Fin n → G // FreeGroup.lift a w = 1} : ℝ) / ((Fintype.card G : ℝ) ^ n)

/-- Every group word `w` admits `ε(w) > 0` such that a finite group satisfies the law `w`
iff the proportion of solutions of `w = e` exceeds `1 - ε(w)`. -/
theorem main : ∀ (n : ℕ) (w : FreeGroup (Fin n)), ∃ ε : ℝ, 0 < ε ∧
    ∀ (G : Type) [Group G] [Fintype G], SatisfiesLaw w G ↔ 1 - ε < lawProb w G := by
  sorry

end OMA.S_mse_3070332
