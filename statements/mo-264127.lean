import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

/-!
# Infection of a neighbor in regular graphs

Source: https://mathoverflow.net/questions/264127/among-regular-graphs-do-cliques-have-the-highest-infection-rate

On a finite vertex set use independent rate-one clocks on ordered pairs,
ignoring contacts along nonedges. Exactly one oriented clock on each edge
crossing from infected to uninfected can transmit, so these are precisely
the transition rates of the original process at scaled time λt. Conditional
on k contacts their ordered labels are uniform. Disconnected dummy vertices
do not change the infection probability.

For an arbitrary locally finite graph, infection of a fixed target is witnessed
by a finite chronological path. Bounding every finite induced sample containing
the source, the target and all neighbors of the source is therefore equivalent
to bounding the unrestricted infection probability. The finite samples form a
directed family; the connected component of the source is countable.
-/
namespace OMA.S_mo_264127

/-- Whether an increasing subsequence of the contacts joins x to y. -/
def hit {V : Type} (R : V → V → Prop) (x y : V) :
    (k : ℕ) → (Fin k → V × V) → Prop
  | 0, _ => x=y
  | k+1, w => hit R x y k (Fin.tail w) ∨
      (x=(w 0).1 ∧ R (w 0).1 (w 0).2 ∧ hit R (w 0).2 y k (Fin.tail w))

noncomputable def successes {V : Type} [Fintype V] (R : V → V → Prop) (x y : V) (k : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter fun w => hit R x y k w).card

noncomputable def prob {V : Type} [Fintype V] (R : V → V → Prop) (x y : V) (t : ℝ) : ℝ :=
  Real.exp (-(Fintype.card V:ℝ)^2*t) *
    ∑' k : ℕ, (successes R x y k:ℝ)*t^k/(k.factorial:ℝ)

def clique {V : Type} (R : V → V → Prop) (i x y : V) : Prop :=
  x≠y ∧ (x=i ∨ R i x) ∧ (y=i ∨ R i y)

def comparison {V : Type} (G : SimpleGraph V) (S : Finset V) (i j : S) (t : ℝ) : Prop :=
  let R : S → S → Prop := fun x y => G.Adj x.val y.val
  prob R i j t ≤ prob (clique R i) i j t

theorem main : ∀ (V : Type) (G : SimpleGraph V) [G.LocallyFinite] (d : ℕ),
    G.IsRegularOfDegree d → ∀ (S : Finset V) (i j : S), G.Adj i.val j.val →
    (∀ v, G.Adj i.val v → v∈S) → ∀ t : ℝ, 0≤t → comparison G S i j t := by
  sorry

end OMA.S_mo_264127
