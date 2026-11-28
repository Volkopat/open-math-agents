import Mathlib

/-!
# Vertices of a simplex section of a cardinality-scaled cube hull

Source: https://mathoverflow.net/questions/207139 (tam, CC BY-SA 3.0).
Credit: @connoranderson

Write h(k)=k d(k). Keep the original layers with h(k)=e. For each pair
with h(k)<e<h(l), cut the segment between the two ordered prefix vectors,
then include all coordinate permutations of the cut. These are nested
supports irrespective of which cardinality is larger. There are at most
quadratically many shapes before permuting. The section is exactly their
convex hull. A candidate is an actual vertex exactly when a strict linear
system in n unknowns exposes it against every distinct candidate.
The result permits ties and arbitrary nonnegative layer scales.
-/

namespace OMA.S_mo_207139
open Finset
noncomputable section
abbrev V (n : ℕ) := Fin n → ℝ
abbrev Layer (n : ℕ) := Fin (n+1)
def pref {n : ℕ} (d : Layer n → ℝ) (k : Layer n) (i : Fin n) : ℝ :=
  if i.val<k.val then d k else 0
def ht {n : ℕ} (d : Layer n → ℝ) (k : Layer n) : ℝ := k.val*d k
def orbit {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : V n) : V n := v ∘ σ
def scaleHull {n : ℕ} (d : Layer n → ℝ) : Set (V n) :=
  convexHull ℝ (Set.range (fun p : Layer n × Equiv.Perm (Fin n) => orbit p.2 (pref d p.1)))
def simplex (n : ℕ) (e : ℝ) : Set (V n) := convexHull ℝ (Set.range (fun i : Fin n => Pi.single i e))
def cut {n : ℕ} (d : Layer n → ℝ) (e : ℝ) (k l : Layer n) : V n :=
  ((ht d l-e)/(ht d l-ht d k)) • pref d k + ((e-ht d k)/(ht d l-ht d k)) • pref d l
def candidates {n : ℕ} (d : Layer n → ℝ) (e : ℝ) : Set (V n) :=
  {x | (∃ k σ, ht d k=e ∧ x=orbit σ (pref d k)) ∨
    ∃ k l σ, ht d k < e ∧ e < ht d l ∧ x=orbit σ (cut d e k l)}
def score {n : ℕ} (c x : V n) : ℝ := ∑ i,c i*x i

theorem main : ∀ (n : ℕ) (d : Layer n → ℝ) (e : ℝ), (∀ k,0 ≤ d k) → 0<e →
    scaleHull d ∩ simplex n e = convexHull ℝ (candidates d e) ∧
    ∀ x, x∈(scaleHull d ∩ simplex n e).extremePoints ℝ ↔
      x∈candidates d e ∧ ∃ c : V n, ∀ y∈candidates d e, y≠x → score c y < score c x := by
  sorry
end
end OMA.S_mo_207139
