import Mathlib

/-!
# First straight terraces in the symmetric divisor-sum pyramid

Source: https://oeis.org/A380573
Geometric construction: https://oeis.org/A237593 and https://oeis.org/A237270
Conjecture: Omar E. Pol (2025).

The boundary at level n is the symmetric Dyck path whose run lengths are h
followed by reverse(h). Here h_k=T(n,k)-T(n,k+1), through its positive terms,
where T(n,k)=ceil((n+1)/k-(k+1)/2). Equivalently, T(n,k) counts nonnegative m
with k(k+1)/2+k*m<=n, so its positive part is the integer quotient in count.

InShape is the region below that path, with cells indexed from (0,0).
For h=a::b::r, the first horizontal and last vertical runs bound an outer
L of width a and extent sum(h). The remaining symmetric region is InShape r,
translated by (a,a); for h=[a] the region is an a by a square.
This gives the recursive construction below directly from the boundary word.

A terrace is a maximal four-neighbor connected component of the new cells
between consecutive regions. HorizontalComponent identifies the entire
component, rather than merely finding a bar contained within a larger part.
The two orientations of a straight free polyomino are both included.
-/

namespace OMA.S_oeis_a380573

def tri : ℕ → ℕ
  | 0 => 0
  | n+1 => tri n+n+1

def count (n k : ℕ) : ℕ :=
  if k=0 then 0 else if tri k ≤ n then (n-tri k)/k+1 else 0

def dropWidth (n k : ℕ) : ℕ := count n k-count n (k+1)

def halfRuns (n : ℕ) : List ℕ :=
  if n=0 then [] else dropWidth n 1 ::
    (((List.range (n-1)).map fun i => dropWidth n (i+2)).filter (0<·))

def InShape : List ℕ → ℕ → ℕ → Prop
  | [], _, _ => False
  | [a], x, y => x<a ∧ y<a
  | a::b::r, x, y =>
      (x<a ∧ y<(a+b+r.sum)) ∨ (y<a ∧ x<(a+b+r.sum)) ∨
      (a ≤ x ∧ a ≤ y ∧ InShape r (x-a) (y-a))

def shapeDecidable : (r : List ℕ) → (x y : ℕ) → Decidable (InShape r x y)
  | [], x, y => by unfold InShape; infer_instance
  | [a], x, y => by unfold InShape; infer_instance
  | a::b::r, x, y => by
      unfold InShape
      haveI := shapeDecidable r (x-a) (y-a)
      infer_instance

instance (r : List ℕ) (x y : ℕ) : Decidable (InShape r x y) := shapeDecidable r x y

def Layer (n x y : ℕ) : Prop :=
  InShape (halfRuns n) x y ∧ ¬InShape (halfRuns (n-1)) x y

instance (n x y : ℕ) : Decidable (Layer n x y) := by unfold Layer; infer_instance

abbrev Cell := ℕ × ℕ

def Adjacent (x y u v : ℕ) : Prop :=
  (u=x+1 ∧ v=y) ∨ (x=u+1 ∧ v=y) ∨
  (u=x ∧ v=y+1) ∨ (u=x ∧ y=v+1)

def Edge (P : ℕ → ℕ → Prop) (p q : Cell) : Prop :=
  P p.1 p.2 ∧ P q.1 q.2 ∧ Adjacent p.1 p.2 q.1 q.2

def Reach (P : ℕ → ℕ → Prop) (p q : Cell) : Prop :=
  Relation.ReflTransGen (Edge P) p q

def HorizontalComponent (P : ℕ → ℕ → Prop) (x y k : ℕ) : Prop :=
  P x y ∧ ∀u v, Reach P (x,y) (u,v) ↔ x ≤ u ∧ u<x+k ∧ v=y

def HasStraightTerrace (n k : ℕ) : Prop :=
  (∃x y, HorizontalComponent (Layer n) x y k) ∨
  (∃x y, HorizontalComponent (fun u v => Layer n v u) x y k)

theorem main :
    ∀ k : ℕ, 0<k →
      HasStraightTerrace (2*k-1) k ∧
      ∀ n : ℕ, 0<n → n<2*k-1 → ¬HasStraightTerrace n k := by
  sorry

end OMA.S_oeis_a380573
