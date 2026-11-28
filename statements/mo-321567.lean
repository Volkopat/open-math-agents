import Mathlib

/-!
# Nonnegative functions with even directions on the finite affine plane

Source: https://mathoverflow.net/questions/321567 (Seva, CC BY-SA 4.0).
Credit: @connoranderson

A function decomposes uniquely as its mean plus zero-mean functions of the
line intercept in each direction. A direction is even precisely when its
component vanishes. Thus at least k even directions amount to using at most
p+1-k univariate components and imposing nonnegativity at the p² points.
Allowing the directions to vary gives a nonconvex set. Even when three
directions are prescribed, normalization need not give the convex hull of
transversal permutations: an explicit order-five array has two entries per
prescribed line in its support but contains no transversal in that support.
-/

namespace OMA.S_mo_321567
open Finset
noncomputable section

abbrev Pt (p : ℕ) := ZMod p × ZMod p
abbrev Dir (p : ℕ) := Option (ZMod p)

def label {p : ℕ} (s : Dir p) (x : Pt p) : ZMod p :=
  s.elim x.1 (fun m => x.2-m*x.1)

def point {p : ℕ} (s : Dir p) (a t : ZMod p) : Pt p :=
  s.elim (a,t) (fun m => (t,a+m*t))

def lineMean {p : ℕ} [NeZero p] (w : Pt p → ℝ) (s : Dir p) (a : ZMod p) : ℝ :=
  (∑ t, w (point s a t))/p

def mean {p : ℕ} [NeZero p] (w : Pt p → ℝ) : ℝ := (∑ x, w x)/(p:ℝ)^2

def assemble {p : ℕ} [NeZero p] (c : ℝ) (g : Dir p → ZMod p → ℝ) (x : Pt p) : ℝ :=
  c + ∑ s, g s (label s x)

def centered {p : ℕ} [NeZero p] (g : Dir p → ZMod p → ℝ) : Prop := ∀ s, ∑ t, g s t=0

def active {p : ℕ} [NeZero p] (g : Dir p → ZMod p → ℝ) : Finset (Dir p) := by
  classical
  exact univ.filter (fun s => g s ≠ 0)

def evens {p : ℕ} [NeZero p] (w : Pt p → ℝ) : Finset (Dir p) := by
  classical
  exact univ.filter (fun s => ∀ a, lineMean w s a=mean w)

def admissible {p : ℕ} [NeZero p] (k : ℕ) : Set (Pt p → ℝ) :=
  {w | (∀ x, 0 ≤ w x) ∧ k ≤ (evens w).card}

def permA : Fin 5 → Fin 5 := ![0,1,3,4,2]
def permB : Fin 5 → Fin 5 := ![2,0,4,1,3]

def support5 (i j : Fin 5) : Bool := decide (j=permA i ∨ j=permB i)

theorem main :
    (∀ (p : ℕ) [Fact p.Prime] (w : Pt p → ℝ),
      (∃! cg : ℝ × (Dir p → ZMod p → ℝ), centered cg.2 ∧ w = assemble cg.1 cg.2) ∧
      (∀ c g, centered g → w = assemble c g →
        c = mean w ∧ (∀ s a, g s a = lineMean w s a - mean w) ∧
        (∀ k : ℕ, w ∈ admissible k ↔
          (∀ x, 0 ≤ assemble c g x) ∧ (active g).card + k ≤ p+1))) ∧
    (∀ (p : ℕ) [Fact p.Prime] (k : ℕ), 3 ≤ k → k ≤ p → ¬Convex ℝ (@admissible p _ k)) ∧
    ((∀ i : Fin 5, (univ.filter (fun j => support5 i j)).card=2) ∧
     (∀ j : Fin 5, (univ.filter (fun i => support5 i j)).card=2) ∧
     (∀ a : Fin 5, (univ.filter (fun i => support5 i (a+i))).card=2) ∧
     ¬∃ f : Fin 5 → Fin 5, Function.Injective f ∧ Function.Injective (fun i => f i-i) ∧
        ∀ i, support5 i (f i)) := by
  sorry

end
end OMA.S_mo_321567
