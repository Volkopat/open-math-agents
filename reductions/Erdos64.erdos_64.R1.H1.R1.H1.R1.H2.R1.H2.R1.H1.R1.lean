import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1_H2_R1
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.Semiconj.Basic
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Set.Card.Arithmetic

import Mathlib.GroupTheory.OrderOfElement

/-!
# Short cycles from commuting adjacent conjugates

Write r = q p q⁻¹. A conjugate square at y is the equality pr(y) = rp(y).
If these squares close at x, q(x) and r⁻¹(x), the graph of the three
pointwise distinct matchings 1, p, q contains a simple C4, C8 or C16.
The eighteen positions in the certificate are words of length at most
four applied to x. They need not be distinct. With edges labeled 0, 1, 2
for the three matchings, the first closed trace reads 0120121010210201.
A repeated same-shore vertex identifies two positions. Transport these
equalities by the permutations and their inverses to obtain the next
trace or contradict matching separation. A nonbacktracking eight-step
trace that folds at opposite positions contains a four-cycle.

If all three cycle lengths are absent, the three inverse images of the
square-failure set cover X. A union bound gives defect at least |X|/3.
Relabeling the matchings yields the same bound for all three relative
pairs. In particular an abelian normal subgroup cannot contain a
relative matching difference, which rules out index two.

The result extends the odd-order regular-action rectangle of @mejiasd3v
in PR 7828 to arbitrary separated permutation actions. The matching
formulation and the central-commutator case come from PRs 592, 5246
and 5820. The target is the residual step of PR 8157.
Formalization by @bmander.
-/
namespace Erdos64.MatchingConjugate
open SimpleGraph
universe u
variable {X : Type u}

private theorem reverse_move (f : Equiv.Perm X) {a b : X} (h : f a=b) : f.symm b=a :=
  f.symm_apply_eq.mpr h.symm

private theorem move_eq (f : X → X) {a b c d : X}
    (ha : f a=c) (hb : f b=d) (h : a=b) : c=d :=
  ha.symm.trans ((congrArg f h).trans hb)
set_option maxHeartbeats 6000000 in
set_option maxRecDepth 5000 in
private theorem collision4 {G : SimpleGraph (Bool × X)} (no : ¬ cycleGraph 4 ⊑ G)
    (x0 x1 x2 x3 : X)
    (e0 : G.Adj (false,x0) (true,x1))
    (e1 : G.Adj (false,x2) (true,x1))
    (e2 : G.Adj (false,x2) (true,x3))
    (e3 : G.Adj (false,x0) (true,x3))
    : x0=x2 ∨ x1=x3 := by
  classical
  by_contra! h
  apply no
  let l : List (Bool × X) := [(false,x0),(true,x1),(false,x2),(true,x3)]
  let f : Fin 4 → Bool × X := l.get
  have nd : l.Nodup := by
    obtain ⟨d0_2,d1_3⟩ := h
    simp [l, *]
  have step (i : Fin 4) : G.Adj (f i) (f (i+1)) := by
    fin_cases i
    · exact e0
    · exact e1.symm
    · exact e2
    · exact e3.symm
  refine ⟨⟨⟨f,?_⟩,List.nodup_iff_injective_get.mp nd⟩⟩
  intro i j adj
  rcases cycleGraph_adj.mp adj with h|h
  · exact (sub_eq_iff_eq_add'.mp h) ▸ (step j).symm
  · exact (sub_eq_iff_eq_add'.mp h) ▸ step i

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 5000 in
private theorem collision8 {G : SimpleGraph (Bool × X)} (no : ¬ cycleGraph 8 ⊑ G)
    (x0 x1 x2 x3 x4 x5 x6 x7 : X)
    (e0 : G.Adj (false,x0) (true,x1))
    (e1 : G.Adj (false,x2) (true,x1))
    (e2 : G.Adj (false,x2) (true,x3))
    (e3 : G.Adj (false,x4) (true,x3))
    (e4 : G.Adj (false,x4) (true,x5))
    (e5 : G.Adj (false,x6) (true,x5))
    (e6 : G.Adj (false,x6) (true,x7))
    (e7 : G.Adj (false,x0) (true,x7))
    : x0=x2 ∨ x0=x4 ∨ x0=x6 ∨ x1=x3 ∨ x1=x5 ∨ x1=x7 ∨ x2=x4 ∨ x2=x6 ∨ x3=x5 ∨ x3=x7 ∨ x4=x6 ∨ x5=x7 := by
  classical
  by_contra! h
  apply no
  let l : List (Bool × X) := [(false,x0),(true,x1),(false,x2),(true,x3),(false,x4),(true,x5),(false,x6),(true,x7)]
  let f : Fin 8 → Bool × X := l.get
  have nd : l.Nodup := by
    obtain ⟨d0_2,d0_4,d0_6,d1_3,d1_5,d1_7,d2_4,d2_6,d3_5,d3_7,d4_6,d5_7⟩ := h
    simp [l, *]
  have step (i : Fin 8) : G.Adj (f i) (f (i+1)) := by
    fin_cases i
    · exact e0
    · exact e1.symm
    · exact e2
    · exact e3.symm
    · exact e4
    · exact e5.symm
    · exact e6
    · exact e7.symm
  refine ⟨⟨⟨f,?_⟩,List.nodup_iff_injective_get.mp nd⟩⟩
  intro i j adj
  rcases cycleGraph_adj.mp adj with h|h
  · exact (sub_eq_iff_eq_add'.mp h) ▸ (step j).symm
  · exact (sub_eq_iff_eq_add'.mp h) ▸ step i

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 5000 in
private theorem collision16 {G : SimpleGraph (Bool × X)} (no : ¬ cycleGraph 16 ⊑ G)
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : X)
    (e0 : G.Adj (false,x0) (true,x1))
    (e1 : G.Adj (false,x2) (true,x1))
    (e2 : G.Adj (false,x2) (true,x3))
    (e3 : G.Adj (false,x4) (true,x3))
    (e4 : G.Adj (false,x4) (true,x5))
    (e5 : G.Adj (false,x6) (true,x5))
    (e6 : G.Adj (false,x6) (true,x7))
    (e7 : G.Adj (false,x8) (true,x7))
    (e8 : G.Adj (false,x8) (true,x9))
    (e9 : G.Adj (false,x10) (true,x9))
    (e10 : G.Adj (false,x10) (true,x11))
    (e11 : G.Adj (false,x12) (true,x11))
    (e12 : G.Adj (false,x12) (true,x13))
    (e13 : G.Adj (false,x14) (true,x13))
    (e14 : G.Adj (false,x14) (true,x15))
    (e15 : G.Adj (false,x0) (true,x15))
    : x0=x2 ∨ x0=x4 ∨ x0=x6 ∨ x0=x8 ∨ x0=x10 ∨ x0=x12 ∨ x0=x14 ∨ x1=x3 ∨ x1=x5 ∨ x1=x7 ∨ x1=x9 ∨ x1=x11 ∨ x1=x13 ∨ x1=x15 ∨ x2=x4 ∨ x2=x6 ∨ x2=x8 ∨ x2=x10 ∨ x2=x12 ∨ x2=x14 ∨ x3=x5 ∨ x3=x7 ∨ x3=x9 ∨ x3=x11 ∨ x3=x13 ∨ x3=x15 ∨ x4=x6 ∨ x4=x8 ∨ x4=x10 ∨ x4=x12 ∨ x4=x14 ∨ x5=x7 ∨ x5=x9 ∨ x5=x11 ∨ x5=x13 ∨ x5=x15 ∨ x6=x8 ∨ x6=x10 ∨ x6=x12 ∨ x6=x14 ∨ x7=x9 ∨ x7=x11 ∨ x7=x13 ∨ x7=x15 ∨ x8=x10 ∨ x8=x12 ∨ x8=x14 ∨ x9=x11 ∨ x9=x13 ∨ x9=x15 ∨ x10=x12 ∨ x10=x14 ∨ x11=x13 ∨ x11=x15 ∨ x12=x14 ∨ x13=x15 := by
  classical
  by_contra! h
  apply no
  let l : List (Bool × X) := [(false,x0),(true,x1),(false,x2),(true,x3),(false,x4),(true,x5),(false,x6),(true,x7),(false,x8),(true,x9),(false,x10),(true,x11),(false,x12),(true,x13),(false,x14),(true,x15)]
  let f : Fin 16 → Bool × X := l.get
  have nd : l.Nodup := by
    obtain ⟨d0_2,d0_4,d0_6,d0_8,d0_10,d0_12,d0_14,d1_3,d1_5,d1_7,d1_9,d1_11,d1_13,d1_15,d2_4,d2_6,d2_8,d2_10,d2_12,d2_14,d3_5,d3_7,d3_9,d3_11,d3_13,d3_15,d4_6,d4_8,d4_10,d4_12,d4_14,d5_7,d5_9,d5_11,d5_13,d5_15,d6_8,d6_10,d6_12,d6_14,d7_9,d7_11,d7_13,d7_15,d8_10,d8_12,d8_14,d9_11,d9_13,d9_15,d10_12,d10_14,d11_13,d11_15,d12_14,d13_15⟩ := h
    simp [l, *]
  have step (i : Fin 16) : G.Adj (f i) (f (i+1)) := by
    fin_cases i
    · exact e0
    · exact e1.symm
    · exact e2
    · exact e3.symm
    · exact e4
    · exact e5.symm
    · exact e6
    · exact e7.symm
    · exact e8
    · exact e9.symm
    · exact e10
    · exact e11.symm
    · exact e12
    · exact e13.symm
    · exact e14
    · exact e15.symm
  refine ⟨⟨⟨f,?_⟩,List.nodup_iff_injective_get.mp nd⟩⟩
  intro i j adj
  rcases cycleGraph_adj.mp adj with h|h
  · exact (sub_eq_iff_eq_add'.mp h) ▸ (step j).symm
  · exact (sub_eq_iff_eq_add'.mp h) ▸ step i

private theorem short4 (p q : Equiv.Perm X) (G : SimpleGraph (Bool × X))
    (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x)
    (e₀ : ∀ x, G.Adj (false,x) (true,x)) (e₁ : ∀ x, G.Adj (false,x) (true,p x))
    (e₂ : ∀ x, G.Adj (false,x) (true,q x))
    (no : ¬ (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G))
    (c : Fin 4 → Fin 3) (different : ∀ i, c i ≠ c (i+1))
    (x0 x1 x2 x3 : X)
    (w0 : ((![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X) (c 0)) x0 = x1)
    (w1 : ((![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X) (c 1)) x2 = x1)
    (w2 : ((![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X) (c 2)) x2 = x3)
    (w3 : ((![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X) (c 3)) x0 = x3)
    : False := by
  let F := (![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X)
  have apart (i j : Fin 3) (ij : i ≠ j) (x : X) : F i x ≠ F j x := by
    fin_cases i <;> fin_cases j <;> first | exact (ij rfl).elim | exact (sep x).1 | exact (sep x).1.symm | exact (sep x).2.1 | exact (sep x).2.1.symm | exact (sep x).2.2 | exact (sep x).2.2.symm
  have edge (i : Fin 3) (x : X) : G.Adj (false,x) (true,F i x) := by
    fin_cases i <;> first | exact e₀ x | exact e₁ x | exact e₂ x
  have a0 : G.Adj (false,x0) (true,x1) := (w0) ▸ edge (c 0) x0
  have a1 : G.Adj (false,x2) (true,x1) := (w1) ▸ edge (c 1) x2
  have a2 : G.Adj (false,x2) (true,x3) := (w2) ▸ edge (c 2) x2
  have a3 : G.Adj (false,x0) (true,x3) := (w3) ▸ edge (c 3) x0
  have d0 : x0 ≠ x2 := by
    intro hit
    exact apart _ _ (different 0) x0 ((w0).trans (w1.symm.trans (congrArg (F (c 1)) hit.symm)))
  have d1 : x1 ≠ x3 := by
    intro hit
    exact apart _ _ (different 1) x2 ((w1).trans (hit.trans w2.symm))
  have d2 : x2 ≠ x0 := by
    intro hit
    exact apart _ _ (different 2) x2 ((w2).trans (w3.symm.trans (congrArg (F (c 3)) hit.symm)))
  have d3 : x3 ≠ x1 := by
    intro hit
    exact apart _ _ (different 3) x0 ((w3).trans (hit.trans w0.symm))
  rcases collision4 (fun h => no (.inl h)) x0 x1 x2 x3 a0 a1 a2 a3 with h|h
  · exact d0 h
  · exact d1 h

private theorem short8 (p q : Equiv.Perm X) (G : SimpleGraph (Bool × X))
    (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x)
    (e₀ : ∀ x, G.Adj (false,x) (true,x)) (e₁ : ∀ x, G.Adj (false,x) (true,p x))
    (e₂ : ∀ x, G.Adj (false,x) (true,q x))
    (no : ¬ (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G))
    (c : Fin 8 → Fin 3) (different : ∀ i, c i ≠ c (i+1))
    (x0 x1 x2 x3 x4 x5 x6 x7 : X)
    (w0 : ((![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X) (c 0)) x0 = x1)
    (w1 : ((![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X) (c 1)) x2 = x1)
    (w2 : ((![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X) (c 2)) x2 = x3)
    (w3 : ((![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X) (c 3)) x4 = x3)
    (w4 : ((![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X) (c 4)) x4 = x5)
    (w5 : ((![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X) (c 5)) x6 = x5)
    (w6 : ((![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X) (c 6)) x6 = x7)
    (w7 : ((![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X) (c 7)) x0 = x7)
    : False := by
  let F := (![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X)
  have apart (i j : Fin 3) (ij : i ≠ j) (x : X) : F i x ≠ F j x := by
    fin_cases i <;> fin_cases j <;> first | exact (ij rfl).elim | exact (sep x).1 | exact (sep x).1.symm | exact (sep x).2.1 | exact (sep x).2.1.symm | exact (sep x).2.2 | exact (sep x).2.2.symm
  have edge (i : Fin 3) (x : X) : G.Adj (false,x) (true,F i x) := by
    fin_cases i <;> first | exact e₀ x | exact e₁ x | exact e₂ x
  have a0 : G.Adj (false,x0) (true,x1) := (w0) ▸ edge (c 0) x0
  have a1 : G.Adj (false,x2) (true,x1) := (w1) ▸ edge (c 1) x2
  have a2 : G.Adj (false,x2) (true,x3) := (w2) ▸ edge (c 2) x2
  have a3 : G.Adj (false,x4) (true,x3) := (w3) ▸ edge (c 3) x4
  have a4 : G.Adj (false,x4) (true,x5) := (w4) ▸ edge (c 4) x4
  have a5 : G.Adj (false,x6) (true,x5) := (w5) ▸ edge (c 5) x6
  have a6 : G.Adj (false,x6) (true,x7) := (w6) ▸ edge (c 6) x6
  have a7 : G.Adj (false,x0) (true,x7) := (w7) ▸ edge (c 7) x0
  have d0 : x0 ≠ x2 := by
    intro hit
    exact apart _ _ (different 0) x0 ((w0).trans (w1.symm.trans (congrArg (F (c 1)) hit.symm)))
  have d1 : x1 ≠ x3 := by
    intro hit
    exact apart _ _ (different 1) x2 ((w1).trans (hit.trans w2.symm))
  have d2 : x2 ≠ x4 := by
    intro hit
    exact apart _ _ (different 2) x2 ((w2).trans (w3.symm.trans (congrArg (F (c 3)) hit.symm)))
  have d3 : x3 ≠ x5 := by
    intro hit
    exact apart _ _ (different 3) x4 ((w3).trans (hit.trans w4.symm))
  have d4 : x4 ≠ x6 := by
    intro hit
    exact apart _ _ (different 4) x4 ((w4).trans (w5.symm.trans (congrArg (F (c 5)) hit.symm)))
  have d5 : x5 ≠ x7 := by
    intro hit
    exact apart _ _ (different 5) x6 ((w5).trans (hit.trans w6.symm))
  have d6 : x6 ≠ x0 := by
    intro hit
    exact apart _ _ (different 6) x6 ((w6).trans (w7.symm.trans (congrArg (F (c 7)) hit.symm)))
  have d7 : x7 ≠ x1 := by
    intro hit
    exact apart _ _ (different 7) x0 ((w7).trans (hit.trans w0.symm))
  have o0 : x0 ≠ x4 := by
    intro hit
    rcases collision4 (fun h => no (.inl h)) x0 x1 x2 x3 a0 a1 a2 (hit.symm ▸ a3) with h|h
    · exact d0 h
    · exact d1 h
  have o1 : x1 ≠ x5 := by
    intro hit
    rcases collision4 (fun h => no (.inl h)) x2 x3 x4 x1 a2 a3 (hit.symm ▸ a4) a1 with h|h
    · exact d2 h
    · exact d1 h.symm
  have o2 : x2 ≠ x6 := by
    intro hit
    rcases collision4 (fun h => no (.inl h)) x2 x3 x4 x5 a2 a3 a4 (hit.symm ▸ a5) with h|h
    · exact d2 h
    · exact d3 h
  have o3 : x3 ≠ x7 := by
    intro hit
    rcases collision4 (fun h => no (.inl h)) x4 x5 x6 x3 a4 a5 (hit.symm ▸ a6) a3 with h|h
    · exact d4 h
    · exact d3 h.symm
  rcases collision8 (fun h => no (.inr (.inl h))) x0 x1 x2 x3 x4 x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 with h|h|h|h|h|h|h|h|h|h|h|h
  · exact d0 h
  · exact o0 h
  · exact d6 h.symm
  · exact d1 h
  · exact o1 h
  · exact d7 h.symm
  · exact d2 h
  · exact o2 h
  · exact d3 h
  · exact o3 h
  · exact d4 h
  · exact d5 h

variable (p q : Equiv.Perm X) (v : ℕ → X)
variable (hp : ∀ i : Fin 10, let e := ([(0,1),(2,6),(3,7),(4,9),(5,10),(8,3),(11,5),(12,15),(13,16),(14,17)] : List (ℕ × ℕ)).get i; p (v e.1)=v e.2)
variable (hq : ∀ i : Fin 10, let e := ([(0,2),(1,4),(3,0),(5,1),(7,13),(8,14),(10,16),(11,17),(12,6),(15,9)] : List (ℕ × ℕ)).get i; q (v e.1)=v e.2)

variable (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x)
variable (G : SimpleGraph (Bool × X))
variable (e₀ : ∀ x, G.Adj (false,x) (true,x))
variable (e₁ : ∀ x, G.Adj (false,x) (true,p x))
variable (e₂ : ∀ x, G.Adj (false,x) (true,q x))
variable (no : ¬ (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G))
set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp sep in
private theorem branch1 (h0 : v 3 = v 8) : False := by
  have t0 := move_eq p (hp 5) (hp 2) (Eq.symm h0)
  exact (sep (v 3)).1 (Eq.trans (hp 2) (Eq.symm t0))

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep in
private theorem branch2 (h0 : v 3 = v 14) : False := by
  exact (sep (v 8)).2.2 (Eq.trans (hp 5) (Eq.symm (Eq.trans (hq 5) (Eq.symm h0))))

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hq sep in
private theorem branch4 (h1 : v 0 = v 3) : False := by
  have t0 := move_eq q (hq 2) (hq 0) (Eq.symm h1)
  exact (sep (v 0)).2.1 (Eq.trans (hq 0) (Eq.symm t0))

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch5 (h0 : v 3 = v 11) (h1 : v 0 = v 4) : False := by
  have t0 := move_eq p (hp 3) (hp 0) (Eq.symm h1)
  have t1 := move_eq q.symm (reverse_move q (hq 9)) (reverse_move q (hq 3)) t0
  have t2 := move_eq p.symm (reverse_move p (hp 7)) (reverse_move p (hp 6)) t1
  have t3 := move_eq q.symm (reverse_move q (hq 1)) (reverse_move q (hq 2)) (Eq.symm h1)
  have t4 := move_eq q (hq 8) (hq 1) (Eq.trans (Eq.trans t2 (Eq.symm h0)) (Eq.symm t3))
  exact short4 p q G sep e₀ e₁ e₂ no ![0,1,0,2] (by decide)
    (v 0) (v 0) (v 2) (v 2)
    (rfl) (Eq.trans (hp 1) (Eq.trans t4 (Eq.symm h1))) (rfl) (hq 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch7 (h0 : v 3 = v 11) (h1 : v 0 = v 15) (h2 : v 0 = v 16) : False := by
  have t0 := move_eq p (hp 6) (hp 2) (Eq.symm h0)
  have t1 := move_eq q (hq 4) (hq 3) (Eq.symm t0)
  have t2 := move_eq p.symm (reverse_move p (hp 8)) (reverse_move p (hp 7)) (Eq.trans (Eq.symm h2) h1)
  exact short4 p q G sep e₀ e₁ e₂ no ![0,1,0,1] (by decide)
    (v 0) (v 0) (v 1) (v 1)
    (rfl) (Eq.trans (congrArg p (Eq.trans (Eq.symm t1) t2)) (Eq.trans (hp 7) (Eq.symm h1))) (rfl) (hp 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch8 (h0 : v 3 = v 11) (h1 : v 0 = v 15) (h2 : v 12 = v 16) : False := by
  have t0 := move_eq p (hp 6) (hp 2) (Eq.symm h0)
  have t1 := move_eq q (hq 4) (hq 3) (Eq.symm t0)
  have t2 := move_eq q (hq 9) (hq 0) (Eq.symm h1)
  exact short8 p q G sep e₀ e₁ e₂ no ![0,1,0,1,2,0,1,2] (by decide)
    (v 0) (v 0) (v 12) (v 12) (v 1) (v 4) (v 4) (v 2)
    (rfl) (Eq.trans (hp 7) (Eq.symm h1)) (rfl) (Eq.trans (congrArg p (Eq.symm t1)) (Eq.trans (hp 8) (Eq.symm h2))) (hq 1) (rfl) (Eq.trans (hp 3) t2) (hq 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch9 (h1 : v 0 = v 15) (h2 : v 8 = v 4) : False := by
  have t0 := move_eq q (hq 9) (hq 0) (Eq.symm h1)
  have t1 := move_eq p (hp 5) (hp 3) h2
  exact short4 p q G sep e₀ e₁ e₂ no ![0,2,0,2] (by decide)
    (v 0) (v 0) (v 2) (v 2)
    (rfl) (Eq.trans (congrArg q (Eq.trans (Eq.symm t0) (Eq.symm t1))) (hq 2)) (rfl) (hq 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch10 (h1 : v 0 = v 15) (h2 : v 3 = v 4) : False := by
  have t0 := move_eq p (hp 3) (hp 2) (Eq.symm h2)
  have t1 := move_eq q (hq 9) (hq 0) (Eq.symm h1)
  exact short4 p q G sep e₀ e₁ e₂ no ![0,2,1,2] (by decide)
    (v 0) (v 0) (v 3) (v 2)
    (rfl) (hq 2) (Eq.trans (hp 2) (Eq.trans (Eq.symm t0) t1)) (hq 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch11 (h1 : v 0 = v 15) (h2 : v 5 = v 4) : False := by
  have t0 := move_eq q (hq 9) (hq 0) (Eq.symm h1)
  exact short4 p q G sep e₀ e₁ e₂ no ![1,2,1,2] (by decide)
    (v 0) (v 1) (v 4) (v 2)
    (hp 0) (Eq.trans (congrArg q (Eq.symm h2)) (hq 3)) (Eq.trans (hp 3) t0) (hq 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch12 (h2 : v 10 = v 4) : False := by
  exact short4 p q G sep e₀ e₁ e₂ no ![0,2,1,2] (by decide)
    (v 1) (v 1) (v 5) (v 4)
    (rfl) (hq 3) (Eq.trans (hp 4) h2) (hq 1)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch6 (h0 : v 3 = v 11) (h1 : v 0 = v 15) : False := by
  have t0 := move_eq q (hq 7) (hq 2) (Eq.symm h0)
  have t1 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 7)) (Eq.trans t0 h1)
  have t2 := move_eq p (hp 6) (hp 2) (Eq.symm h0)
  have t3 := move_eq q (hq 4) (hq 3) (Eq.symm t2)
  have t4 := move_eq q (hq 9) (hq 0) (Eq.symm h1)
  rcases collision16 (fun h => no (.inr (.inr h)))
    (v 0) (v 0) (v 12) (v 12) (v 8) (v 3) (v 3) (v 5) (v 5) (v 10) (v 10) (v 16) (v 1) (v 4) (v 4) (v 2)
    (e₀ (v 0))
    ((Eq.trans (hp 7) (Eq.symm h1)) ▸ e₁ (v 12))
    (e₀ (v 12))
    ((Eq.trans (hq 5) t1) ▸ e₂ (v 8))
    ((hp 5) ▸ e₁ (v 8))
    (e₀ (v 3))
    ((Eq.trans (hp 2) (Eq.symm t2)) ▸ e₁ (v 3))
    (e₀ (v 5))
    ((hp 4) ▸ e₁ (v 5))
    (e₀ (v 10))
    ((hq 6) ▸ e₂ (v 10))
    ((Eq.trans (congrArg p (Eq.symm t3)) (hp 8)) ▸ e₁ (v 1))
    ((hq 1) ▸ e₂ (v 1))
    (e₀ (v 4))
    ((Eq.trans (hp 3) t4) ▸ e₁ (v 4))
    ((hq 0) ▸ e₂ (v 0)) with hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit
  · have t0 := move_eq p (hp 7) (hp 0) (Eq.symm hit)
    have t1 := move_eq q.symm (reverse_move q (hq 3)) (reverse_move q (hq 2)) (Eq.trans (Eq.symm t0) (Eq.symm h1))
    have t2 := move_eq p.symm (reverse_move p (hp 6)) (reverse_move p (hp 5)) t1
    exact branch1 p q v hp sep (Eq.trans h0 t2)
  · have t0 := move_eq p (hp 5) (hp 0) (Eq.symm hit)
    have t1 := move_eq q (hq 2) (hq 1) t0
    exact branch5 p q v hp hq sep G e₀ e₁ e₂ no h0 t1
  · exact branch4 p q v hq sep hit
  · have t0 := move_eq q (hq 7) (hq 2) (Eq.symm h0)
    have t1 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 6)) (Eq.trans t0 hit)
    exact branch2 p q v hp hq sep (Eq.trans h0 (Eq.symm t1))
  · have t0 := move_eq q (hq 6) (hq 0) (Eq.symm hit)
    have t1 := move_eq q (hq 9) (hq 0) (Eq.symm h1)
    have t2 := move_eq p.symm (reverse_move p (hp 8)) (reverse_move p (hp 3)) (Eq.trans t0 (Eq.symm t1))
    have t3 := move_eq p (hp 6) (hp 2) (Eq.symm h0)
    have t4 := move_eq q (hq 4) (hq 3) (Eq.symm t3)
    have t5 := move_eq q.symm (reverse_move q (hq 1)) (reverse_move q (hq 3)) (Eq.trans (Eq.symm t2) t4)
    have t6 := move_eq p.symm (reverse_move p (hp 6)) (reverse_move p (hp 0)) (Eq.symm t5)
    exact branch4 p q v hq sep (Eq.trans (Eq.symm t6) (Eq.symm h0))
  · have t0 := move_eq q.symm (reverse_move q (hq 3)) (reverse_move q (hq 2)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 6)) (reverse_move p (hp 5)) t0
    exact branch1 p q v hp sep (Eq.trans h0 t1)
  · exact branch5 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · have t0 := move_eq p (hp 7) (hp 0) (Eq.symm hit)
    have t1 := move_eq q.symm (reverse_move q (hq 3)) (reverse_move q (hq 2)) (Eq.trans (Eq.symm t0) (Eq.symm h1))
    have t2 := move_eq p.symm (reverse_move p (hp 6)) (reverse_move p (hp 5)) t1
    exact branch1 p q v hp sep (Eq.trans h0 t2)
  · exact branch4 p q v hq sep hit
  · have t0 := move_eq q (hq 7) (hq 2) (Eq.symm h0)
    have t1 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 6)) (Eq.trans t0 hit)
    exact branch2 p q v hp hq sep (Eq.trans h0 (Eq.symm t1))
  · have t0 := move_eq q (hq 6) (hq 0) (Eq.symm hit)
    have t1 := move_eq q (hq 9) (hq 0) (Eq.symm h1)
    have t2 := move_eq p.symm (reverse_move p (hp 8)) (reverse_move p (hp 3)) (Eq.trans t0 (Eq.symm t1))
    have t3 := move_eq p (hp 6) (hp 2) (Eq.symm h0)
    have t4 := move_eq q (hq 4) (hq 3) (Eq.symm t3)
    have t5 := move_eq q.symm (reverse_move q (hq 1)) (reverse_move q (hq 3)) (Eq.trans (Eq.symm t2) t4)
    have t6 := move_eq p.symm (reverse_move p (hp 6)) (reverse_move p (hp 0)) (Eq.symm t5)
    exact branch4 p q v hq sep (Eq.trans (Eq.symm t6) (Eq.symm h0))
  · exact branch7 p q v hp hq sep G e₀ e₁ e₂ no h0 h1 hit
  · exact branch5 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · have t0 := move_eq q.symm (reverse_move q (hq 0)) (reverse_move q (hq 2)) (Eq.symm hit)
    exact branch4 p q v hq sep t0
  · have t0 := move_eq p (hp 7) (hp 5) hit
    exact branch4 p q v hq sep (Eq.trans h1 t0)
  · have t0 := move_eq q (hq 7) (hq 2) (Eq.symm h0)
    have t1 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 7)) (Eq.trans t0 h1)
    exact branch2 p q v hp hq sep (Eq.trans (Eq.symm hit) (Eq.symm t1))
  · have t0 := move_eq q (hq 8) (hq 3) hit
    have t1 := move_eq p.symm (reverse_move p (hp 1)) (reverse_move p (hp 0)) t0
    have t2 := move_eq p (hp 7) (hp 4) hit
    have t3 := move_eq q (hq 6) (hq 0) (Eq.trans (Eq.symm t2) (Eq.symm h1))
    exact branch7 p q v hp hq sep G e₀ e₁ e₂ no h0 h1 (Eq.trans (Eq.symm t1) (Eq.symm t3))
  · have t0 := move_eq q (hq 9) (hq 0) (Eq.symm h1)
    have t1 := move_eq q (hq 8) (hq 6) hit
    have t2 := move_eq p.symm (reverse_move p (hp 8)) (reverse_move p (hp 1)) (Eq.symm t1)
    have t3 := move_eq p (hp 6) (hp 2) (Eq.symm h0)
    have t4 := move_eq q (hq 4) (hq 3) (Eq.symm t3)
    have t5 := move_eq p.symm (reverse_move p (hp 3)) (reverse_move p (hp 0)) (Eq.trans (Eq.trans t0 (Eq.symm t2)) t4)
    exact branch5 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.symm t5)
  · have t0 := move_eq p (hp 6) (hp 2) (Eq.symm h0)
    have t1 := move_eq q (hq 4) (hq 3) (Eq.symm t0)
    have t2 := move_eq p (hp 8) (hp 7) (Eq.trans t1 (Eq.symm hit))
    exact branch7 p q v hp hq sep G e₀ e₁ e₂ no h0 h1 (Eq.trans h1 (Eq.symm t2))
  · have t0 := move_eq q (hq 9) (hq 0) (Eq.symm h1)
    have t1 := move_eq p (hp 7) (hp 3) hit
    have t2 := move_eq q.symm (reverse_move q (hq 0)) (reverse_move q (hq 2)) (Eq.trans (Eq.trans (Eq.symm t0) (Eq.symm t1)) (Eq.symm h1))
    exact branch4 p q v hq sep t2
  · have t0 := move_eq q (hq 7) (hq 2) (Eq.symm h0)
    have t1 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 7)) (Eq.trans t0 h1)
    exact branch2 p q v hp hq sep (Eq.trans (Eq.symm hit) (Eq.symm t1))
  · have t0 := move_eq q (hq 8) (hq 3) hit
    have t1 := move_eq p.symm (reverse_move p (hp 1)) (reverse_move p (hp 0)) t0
    have t2 := move_eq p (hp 7) (hp 4) hit
    have t3 := move_eq q (hq 6) (hq 0) (Eq.trans (Eq.symm t2) (Eq.symm h1))
    exact branch7 p q v hp hq sep G e₀ e₁ e₂ no h0 h1 (Eq.trans (Eq.symm t1) (Eq.symm t3))
  · have t0 := move_eq q (hq 9) (hq 0) (Eq.symm h1)
    have t1 := move_eq q (hq 8) (hq 6) hit
    have t2 := move_eq p.symm (reverse_move p (hp 8)) (reverse_move p (hp 1)) (Eq.symm t1)
    have t3 := move_eq p (hp 6) (hp 2) (Eq.symm h0)
    have t4 := move_eq q (hq 4) (hq 3) (Eq.symm t3)
    have t5 := move_eq p.symm (reverse_move p (hp 3)) (reverse_move p (hp 0)) (Eq.trans (Eq.trans t0 (Eq.symm t2)) t4)
    exact branch5 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.symm t5)
  · exact branch8 p q v hp hq sep G e₀ e₁ e₂ no h0 h1 hit
  · have t0 := move_eq q (hq 9) (hq 0) (Eq.symm h1)
    have t1 := move_eq p (hp 7) (hp 3) hit
    have t2 := move_eq q.symm (reverse_move q (hq 0)) (reverse_move q (hq 2)) (Eq.trans (Eq.trans (Eq.symm t0) (Eq.symm t1)) (Eq.symm h1))
    exact branch4 p q v hq sep t2
  · have t0 := move_eq p (hp 7) (hp 1) hit
    have t1 := move_eq q.symm (reverse_move q (hq 8)) (reverse_move q (hq 2)) (Eq.trans (Eq.symm t0) (Eq.symm h1))
    have t2 := move_eq q (hq 7) (hq 2) (Eq.symm h0)
    have t3 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 7)) (Eq.trans t2 h1)
    exact branch2 p q v hp hq sep (Eq.trans (Eq.symm t1) (Eq.symm t3))
  · exact branch1 p q v hp sep (Eq.symm hit)
  · have t0 := move_eq p (hp 5) (hp 4) hit
    have t1 := move_eq q (hq 6) (hq 2) (Eq.symm t0)
    exact branch7 p q v hp hq sep G e₀ e₁ e₂ no h0 h1 (Eq.symm t1)
  · have t0 := move_eq q (hq 7) (hq 2) (Eq.symm h0)
    have t1 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 7)) (Eq.trans t0 h1)
    have t2 := move_eq q (hq 6) (hq 5) (Eq.symm hit)
    exact branch8 p q v hp hq sep G e₀ e₁ e₂ no h0 h1 (Eq.trans (Eq.symm t1) (Eq.symm t2))
  · have t0 := move_eq q (hq 9) (hq 0) (Eq.symm h1)
    have t1 := move_eq q (hq 5) (hq 1) hit
    have t2 := move_eq p (hp 9) (hp 3) t1
    have t3 := move_eq q (hq 7) (hq 2) (Eq.symm h0)
    have t4 := move_eq q.symm (reverse_move q (hq 0)) (reverse_move q (hq 2)) (Eq.trans (Eq.trans (Eq.symm t0) (Eq.symm t2)) t3)
    exact branch4 p q v hq sep t4
  · exact branch9 p q v hp hq sep G e₀ e₁ e₂ no h1 hit
  · have t0 := move_eq p.symm (reverse_move p (hp 6)) (reverse_move p (hp 5)) (Eq.symm hit)
    exact branch1 p q v hp sep (Eq.trans h0 t0)
  · have t0 := move_eq q (hq 6) (hq 2) (Eq.symm hit)
    exact branch7 p q v hp hq sep G e₀ e₁ e₂ no h0 h1 (Eq.symm t0)
  · have t0 := move_eq q (hq 9) (hq 0) (Eq.symm h1)
    have t1 := move_eq q (hq 7) (hq 2) (Eq.symm h0)
    have t2 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 7)) (Eq.trans t1 h1)
    have t3 := move_eq p.symm (reverse_move p (hp 8)) (reverse_move p (hp 5)) (Eq.symm hit)
    have t4 := move_eq p (hp 6) (hp 2) (Eq.symm h0)
    have t5 := move_eq q (hq 4) (hq 3) (Eq.symm t4)
    have t6 := move_eq q (hq 5) (hq 1) (Eq.trans (Eq.symm t3) t5)
    have t7 := move_eq p (hp 7) (hp 3) (Eq.trans (Eq.symm t2) t6)
    have t8 := move_eq q.symm (reverse_move q (hq 0)) (reverse_move q (hq 2)) (Eq.trans (Eq.trans (Eq.symm t0) (Eq.symm t7)) (Eq.symm h1))
    exact branch4 p q v hq sep t8
  · exact branch10 p q v hp hq sep G e₀ e₁ e₂ no h1 hit
  · have t0 := move_eq q (hq 9) (hq 0) (Eq.symm h1)
    have t1 := move_eq p.symm (reverse_move p (hp 3)) (reverse_move p (hp 5)) (Eq.trans t0 (Eq.symm hit))
    exact branch9 p q v hp hq sep G e₀ e₁ e₂ no h1 (Eq.symm t1)
  · have t0 := move_eq p.symm (reverse_move p (hp 6)) (reverse_move p (hp 5)) (Eq.symm hit)
    exact branch1 p q v hp sep (Eq.trans h0 t0)
  · have t0 := move_eq q (hq 6) (hq 2) (Eq.symm hit)
    exact branch7 p q v hp hq sep G e₀ e₁ e₂ no h0 h1 (Eq.symm t0)
  · have t0 := move_eq q (hq 2) (hq 1) hit
    exact branch5 p q v hp hq sep G e₀ e₁ e₂ no h0 t0
  · exact branch10 p q v hp hq sep G e₀ e₁ e₂ no h1 hit
  · have t0 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 6)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 6)) (reverse_move p (hp 5)) (Eq.trans t0 (Eq.symm h0))
    exact branch1 p q v hp sep (Eq.trans h0 t1)
  · have t0 := move_eq q (hq 7) (hq 2) (Eq.symm h0)
    have t1 := move_eq p.symm (reverse_move p (hp 8)) (reverse_move p (hp 6)) (Eq.symm hit)
    have t2 := move_eq p (hp 6) (hp 2) (Eq.symm h0)
    have t3 := move_eq q (hq 4) (hq 3) (Eq.symm t2)
    have t4 := move_eq q (hq 7) (hq 1) (Eq.trans (Eq.symm t1) t3)
    exact branch5 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.trans (Eq.symm t0) t4)
  · exact branch11 p q v hp hq sep G e₀ e₁ e₂ no h1 hit
  · have t0 := move_eq q (hq 9) (hq 0) (Eq.symm h1)
    have t1 := move_eq p.symm (reverse_move p (hp 3)) (reverse_move p (hp 6)) (Eq.trans t0 (Eq.symm hit))
    exact branch10 p q v hp hq sep G e₀ e₁ e₂ no h1 (Eq.trans h0 (Eq.symm t1))
  · have t0 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 6)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 6)) (reverse_move p (hp 5)) (Eq.trans t0 (Eq.symm h0))
    exact branch1 p q v hp sep (Eq.trans h0 t1)
  · have t0 := move_eq q (hq 3) (hq 1) hit
    exact branch11 p q v hp hq sep G e₀ e₁ e₂ no h1 (Eq.trans hit t0)
  · exact branch11 p q v hp hq sep G e₀ e₁ e₂ no h1 hit
  · have t0 := move_eq p.symm (reverse_move p (hp 8)) (reverse_move p (hp 4)) (Eq.symm hit)
    have t1 := move_eq p (hp 6) (hp 2) (Eq.symm h0)
    have t2 := move_eq q (hq 4) (hq 3) (Eq.symm t1)
    have t3 := move_eq q (hq 3) (hq 1) (Eq.trans (Eq.symm t0) t2)
    exact branch11 p q v hp hq sep G e₀ e₁ e₂ no h1 (Eq.trans (Eq.trans (Eq.symm t0) t2) t3)
  · exact branch12 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq q (hq 9) (hq 0) (Eq.symm h1)
    have t1 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 3)) (Eq.trans hit (Eq.symm t0))
    exact branch11 p q v hp hq sep G e₀ e₁ e₂ no h1 t1
  · have t0 := move_eq q (hq 9) (hq 0) (Eq.symm h1)
    have t1 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 0)) hit
    have t2 := move_eq q (hq 3) (hq 0) t1
    have t3 := move_eq p.symm (reverse_move p (hp 3)) (reverse_move p (hp 0)) (Eq.trans t0 (Eq.symm t2))
    exact branch5 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.symm t3)
  · exact branch12 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq q (hq 9) (hq 0) (Eq.symm h1)
    have t1 := move_eq q.symm (reverse_move q (hq 6)) (reverse_move q (hq 1)) hit
    have t2 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 0)) t1
    have t3 := move_eq q (hq 3) (hq 0) t2
    have t4 := move_eq p.symm (reverse_move p (hp 3)) (reverse_move p (hp 0)) (Eq.trans t0 (Eq.symm t3))
    exact branch5 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.symm t4)
  · have t0 := move_eq q (hq 9) (hq 0) (Eq.symm h1)
    have t1 := move_eq p.symm (reverse_move p (hp 8)) (reverse_move p (hp 3)) (Eq.trans hit (Eq.symm t0))
    have t2 := move_eq p (hp 6) (hp 2) (Eq.symm h0)
    have t3 := move_eq q (hq 4) (hq 3) (Eq.symm t2)
    have t4 := move_eq q.symm (reverse_move q (hq 1)) (reverse_move q (hq 3)) (Eq.trans (Eq.symm t1) t3)
    exact branch11 p q v hp hq sep G e₀ e₁ e₂ no h1 (Eq.trans (Eq.trans (Eq.symm t4) (Eq.symm t3)) t1)
  · have t0 := move_eq q.symm (reverse_move q (hq 1)) (reverse_move q (hq 3)) (Eq.symm hit)
    exact branch11 p q v hp hq sep G e₀ e₁ e₂ no h1 (Eq.trans (Eq.symm t0) hit)
  · have t0 := move_eq q.symm (reverse_move q (hq 1)) (reverse_move q (hq 0)) hit
    have t1 := move_eq q.symm (reverse_move q (hq 3)) (reverse_move q (hq 2)) t0
    have t2 := move_eq p.symm (reverse_move p (hp 6)) (reverse_move p (hp 5)) t1
    exact branch1 p q v hp sep (Eq.trans h0 t2)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep in
private theorem branch13 (h1 : v 0 = v 12) : False := by
  have t0 := move_eq q (hq 8) (hq 0) (Eq.symm h1)
  exact (sep (v 2)).1 (Eq.trans (hp 1) t0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch14 (h0 : v 3 = v 11) (h1 : v 0 = v 9) : False := by
  have t0 := move_eq q (hq 7) (hq 2) (Eq.symm h0)
  have t1 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 3)) (Eq.trans t0 h1)
  have t2 := move_eq q.symm (reverse_move q (hq 5)) (reverse_move q (hq 1)) t1
  have t3 := move_eq q.symm (reverse_move q (hq 9)) (reverse_move q (hq 2)) (Eq.symm h1)
  have t4 := move_eq p.symm (reverse_move p (hp 7)) (reverse_move p (hp 5)) t3
  have t5 := move_eq q (hq 8) (hq 5) t4
  exact short8 p q G sep e₀ e₁ e₂ no ![0,2,0,1,2,1,0,2] (by decide)
    (v 0) (v 0) (v 3) (v 3) (v 1) (v 4) (v 2) (v 2)
    (rfl) (hq 2) (rfl) (Eq.trans (congrArg p (Eq.symm t2)) (hp 5)) (hq 1) (Eq.trans (hp 1) (Eq.trans t5 t1)) (rfl) (hq 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch15 (h0 : v 3 = v 11) (h1 : v 3 = v 4) : False := by
  have t0 := move_eq q (hq 7) (hq 2) (Eq.symm h0)
  exact short8 p q G sep e₀ e₁ e₂ no ![0,1,0,2,1,2,0,1] (by decide)
    (v 0) (v 0) (v 14) (v 14) (v 8) (v 3) (v 1) (v 1)
    (rfl) (Eq.trans (hp 9) t0) (rfl) (hq 5) (hp 5) (Eq.trans (hq 1) (Eq.symm h1)) (rfl) (hp 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hq sep G e₀ e₁ e₂ no in
private theorem branch16 (h1 : v 3 = v 2) : False := by
  exact short4 p q G sep e₀ e₁ e₂ no ![0,2,0,2] (by decide)
    (v 0) (v 0) (v 2) (v 2)
    (rfl) (Eq.trans (congrArg q (Eq.symm h1)) (hq 2)) (rfl) (hq 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hq sep G e₀ e₁ e₂ no in
private theorem branch17 (h1 : v 5 = v 4) : False := by
  exact short4 p q G sep e₀ e₁ e₂ no ![0,2,0,2] (by decide)
    (v 1) (v 1) (v 4) (v 4)
    (rfl) (Eq.trans (congrArg q (Eq.symm h1)) (hq 3)) (rfl) (hq 1)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch18 (h0 : v 3 = v 11) (h1 : v 5 = v 2) : False := by
  have t0 := move_eq p (hp 6) (hp 2) (Eq.symm h0)
  exact short4 p q G sep e₀ e₁ e₂ no ![0,2,1,2] (by decide)
    (v 0) (v 0) (v 3) (v 2)
    (rfl) (hq 2) (Eq.trans (hp 2) (Eq.trans (Eq.symm t0) h1)) (hq 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch20 (h2 : v 0 = v 10) : False := by
  exact short4 p q G sep e₀ e₁ e₂ no ![0,1,2,1] (by decide)
    (v 0) (v 0) (v 5) (v 1)
    (rfl) (Eq.trans (hp 4) (Eq.symm h2)) (hq 3) (hp 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch21 (h0 : v 3 = v 11) (h1 : v 1 = v 12) (h2 : v 14 = v 10) : False := by
  have t0 := move_eq q (hq 7) (hq 2) (Eq.symm h0)
  have t1 := move_eq p (hp 6) (hp 2) (Eq.symm h0)
  have t2 := move_eq q (hq 4) (hq 3) (Eq.symm t1)
  have t3 := move_eq p (hp 8) (hp 7) (Eq.trans t2 h1)
  have t4 := move_eq q (hq 8) (hq 1) (Eq.symm h1)
  exact short8 p q G sep e₀ e₁ e₂ no ![0,1,2,1,2,1,0,2] (by decide)
    (v 0) (v 0) (v 10) (v 15) (v 1) (v 4) (v 2) (v 2)
    (rfl) (Eq.trans (congrArg p (Eq.symm h2)) (Eq.trans (hp 9) t0)) (Eq.trans (hq 6) t3) (Eq.trans (congrArg p (h1)) (hp 7)) (hq 1) (Eq.trans (hp 1) t4) (rfl) (hq 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch22 (h0 : v 3 = v 11) (h1 : v 1 = v 12) (h2 : v 14 = v 15) : False := by
  have t0 := move_eq q (hq 7) (hq 2) (Eq.symm h0)
  have t1 := move_eq q (hq 8) (hq 1) (Eq.symm h1)
  exact short8 p q G sep e₀ e₁ e₂ no ![0,1,0,1,2,1,0,2] (by decide)
    (v 0) (v 0) (v 14) (v 14) (v 1) (v 4) (v 2) (v 2)
    (rfl) (Eq.trans (hp 9) t0) (rfl) (Eq.trans (congrArg p (h1)) (Eq.trans (hp 7) (Eq.symm h2))) (hq 1) (Eq.trans (hp 1) t1) (rfl) (hq 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch23 (h2 : v 10 = v 2) : False := by
  exact short4 p q G sep e₀ e₁ e₂ no ![1,2,1,2] (by decide)
    (v 0) (v 1) (v 5) (v 2)
    (hp 0) (hq 3) (Eq.trans (hp 4) h2) (hq 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch19 (h0 : v 3 = v 11) (h1 : v 1 = v 12) : False := by
  have t0 := move_eq q (hq 7) (hq 2) (Eq.symm h0)
  have t1 := move_eq p (hp 6) (hp 2) (Eq.symm h0)
  have t2 := move_eq q (hq 4) (hq 3) (Eq.symm t1)
  have t3 := move_eq p (hp 8) (hp 7) (Eq.trans t2 h1)
  have t4 := move_eq q (hq 8) (hq 1) (Eq.symm h1)
  rcases collision16 (fun h => no (.inr (.inr h)))
    (v 0) (v 0) (v 14) (v 14) (v 8) (v 3) (v 3) (v 5) (v 5) (v 10) (v 10) (v 15) (v 1) (v 4) (v 2) (v 2)
    (e₀ (v 0))
    ((Eq.trans (hp 9) t0) ▸ e₁ (v 14))
    (e₀ (v 14))
    ((hq 5) ▸ e₂ (v 8))
    ((hp 5) ▸ e₁ (v 8))
    (e₀ (v 3))
    ((Eq.trans (hp 2) (Eq.symm t1)) ▸ e₁ (v 3))
    (e₀ (v 5))
    ((hp 4) ▸ e₁ (v 5))
    (e₀ (v 10))
    ((Eq.trans (hq 6) t3) ▸ e₂ (v 10))
    ((Eq.trans (congrArg p (h1)) (hp 7)) ▸ e₁ (v 1))
    ((hq 1) ▸ e₂ (v 1))
    ((Eq.trans (hp 1) t4) ▸ e₁ (v 2))
    (e₀ (v 2))
    ((hq 0) ▸ e₂ (v 0)) with hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit
  · have t0 := move_eq q.symm (reverse_move q (hq 5)) (reverse_move q (hq 2)) (Eq.symm hit)
    exact branch1 p q v hp sep (Eq.symm t0)
  · have t0 := move_eq p (hp 5) (hp 0) (Eq.symm hit)
    have t1 := move_eq q (hq 2) (hq 1) t0
    exact branch5 p q v hp hq sep G e₀ e₁ e₂ no h0 t1
  · exact branch4 p q v hq sep hit
  · have t0 := move_eq q (hq 7) (hq 2) (Eq.symm h0)
    have t1 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 6)) (Eq.trans t0 hit)
    exact branch2 p q v hp hq sep (Eq.trans h0 (Eq.symm t1))
  · exact branch20 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch13 p q v hp hq sep (Eq.trans hit h1)
  · have t0 := move_eq q.symm (reverse_move q (hq 0)) (reverse_move q (hq 2)) (Eq.symm hit)
    exact branch4 p q v hq sep t0
  · have t0 := move_eq q.symm (reverse_move q (hq 5)) (reverse_move q (hq 2)) (Eq.symm hit)
    exact branch1 p q v hp sep (Eq.symm t0)
  · exact branch4 p q v hq sep hit
  · have t0 := move_eq q (hq 7) (hq 2) (Eq.symm h0)
    have t1 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 6)) (Eq.trans t0 hit)
    exact branch2 p q v hp hq sep (Eq.trans h0 (Eq.symm t1))
  · exact branch20 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch6 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · exact branch5 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · have t0 := move_eq q.symm (reverse_move q (hq 0)) (reverse_move q (hq 2)) (Eq.symm hit)
    exact branch4 p q v hq sep t0
  · have t0 := move_eq q (hq 7) (hq 2) (Eq.symm h0)
    have t1 := move_eq p (hp 9) (hp 5) hit
    exact branch4 p q v hq sep (Eq.trans (Eq.symm t0) t1)
  · exact branch2 p q v hp hq sep (Eq.symm hit)
  · have t0 := move_eq q (hq 7) (hq 2) (Eq.symm h0)
    have t1 := move_eq p (hp 9) (hp 4) hit
    exact branch20 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t0) t1)
  · exact branch21 p q v hp hq sep G e₀ e₁ e₂ no h0 h1 hit
  · have t0 := move_eq q (hq 7) (hq 2) (Eq.symm h0)
    have t1 := move_eq p (hp 9) (hp 7) (Eq.trans hit h1)
    exact branch6 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.trans (Eq.symm t0) t1)
  · have t0 := move_eq q (hq 7) (hq 2) (Eq.symm h0)
    have t1 := move_eq p (hp 9) (hp 1) hit
    have t2 := move_eq q (hq 8) (hq 1) (Eq.symm h1)
    exact branch5 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.trans (Eq.trans (Eq.symm t0) t1) t2)
  · exact branch2 p q v hp hq sep (Eq.symm hit)
  · have t0 := move_eq q (hq 7) (hq 2) (Eq.symm h0)
    have t1 := move_eq p (hp 9) (hp 4) hit
    exact branch20 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t0) t1)
  · exact branch21 p q v hp hq sep G e₀ e₁ e₂ no h0 h1 hit
  · exact branch22 p q v hp hq sep G e₀ e₁ e₂ no h0 h1 hit
  · have t0 := move_eq q (hq 7) (hq 2) (Eq.symm h0)
    have t1 := move_eq p (hp 9) (hp 3) hit
    exact branch14 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.trans (Eq.symm t0) t1)
  · have t0 := move_eq q (hq 7) (hq 2) (Eq.symm h0)
    have t1 := move_eq p (hp 9) (hp 1) hit
    have t2 := move_eq q (hq 8) (hq 1) (Eq.symm h1)
    exact branch5 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.trans (Eq.trans (Eq.symm t0) t1) t2)
  · exact branch1 p q v hp sep (Eq.symm hit)
  · have t0 := move_eq q (hq 7) (hq 2) (Eq.symm h0)
    have t1 := move_eq q (hq 5) (hq 3) hit
    have t2 := move_eq p (hp 9) (hp 7) (Eq.trans t1 h1)
    exact branch6 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.trans (Eq.symm t0) t2)
  · have t0 := move_eq q (hq 6) (hq 5) (Eq.symm hit)
    have t1 := move_eq p (hp 6) (hp 2) (Eq.symm h0)
    have t2 := move_eq q (hq 4) (hq 3) (Eq.symm t1)
    have t3 := move_eq p (hp 8) (hp 7) (Eq.trans t2 h1)
    exact branch22 p q v hp hq sep G e₀ e₁ e₂ no h0 h1 (Eq.trans (Eq.symm t0) t3)
  · have t0 := move_eq q (hq 7) (hq 2) (Eq.symm h0)
    have t1 := move_eq q (hq 5) (hq 1) hit
    have t2 := move_eq p (hp 9) (hp 3) t1
    exact branch14 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.trans (Eq.symm t0) t2)
  · have t0 := move_eq p (hp 5) (hp 1) hit
    have t1 := move_eq q (hq 8) (hq 1) (Eq.symm h1)
    exact branch15 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.trans t0 t1)
  · have t0 := move_eq q (hq 3) (hq 2) (Eq.symm hit)
    exact branch13 p q v hp hq sep (Eq.trans (Eq.symm t0) h1)
  · have t0 := move_eq q (hq 6) (hq 2) (Eq.symm hit)
    have t1 := move_eq p (hp 6) (hp 2) (Eq.symm h0)
    have t2 := move_eq q (hq 4) (hq 3) (Eq.symm t1)
    have t3 := move_eq p (hp 8) (hp 7) (Eq.trans t2 h1)
    exact branch6 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.trans (Eq.symm t0) t3)
  · have t0 := move_eq q (hq 9) (hq 2) (Eq.symm hit)
    exact branch14 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.symm t0)
  · exact branch15 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · exact branch16 p q v hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq q (hq 3) (hq 2) (Eq.symm hit)
    exact branch13 p q v hp hq sep (Eq.trans (Eq.symm t0) h1)
  · have t0 := move_eq q (hq 6) (hq 2) (Eq.symm hit)
    have t1 := move_eq p (hp 6) (hp 2) (Eq.symm h0)
    have t2 := move_eq q (hq 4) (hq 3) (Eq.symm t1)
    have t3 := move_eq p (hp 8) (hp 7) (Eq.trans t2 h1)
    exact branch6 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.trans (Eq.symm t0) t3)
  · have t0 := move_eq q (hq 2) (hq 1) hit
    exact branch5 p q v hp hq sep G e₀ e₁ e₂ no h0 t0
  · exact branch16 p q v hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 6)) (Eq.symm hit)
    have t1 := move_eq q (hq 3) (hq 2) (Eq.trans t0 (Eq.symm h0))
    exact branch13 p q v hp hq sep (Eq.trans (Eq.symm t1) h1)
  · have t0 := move_eq p.symm (reverse_move p (hp 7)) (reverse_move p (hp 6)) (Eq.symm hit)
    have t1 := move_eq q (hq 2) (hq 1) (Eq.trans (Eq.trans h0 (Eq.symm t0)) (Eq.symm h1))
    exact branch5 p q v hp hq sep G e₀ e₁ e₂ no h0 t1
  · exact branch17 p q v hq sep G e₀ e₁ e₂ no hit
  · exact branch18 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · have t0 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 6)) (Eq.symm hit)
    have t1 := move_eq q (hq 3) (hq 2) (Eq.trans t0 (Eq.symm h0))
    exact branch13 p q v hp hq sep (Eq.trans (Eq.symm t1) h1)
  · have t0 := move_eq q (hq 3) (hq 1) hit
    exact branch17 p q v hq sep G e₀ e₁ e₂ no (Eq.trans hit t0)
  · exact branch18 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · have t0 := move_eq p.symm (reverse_move p (hp 7)) (reverse_move p (hp 4)) (Eq.symm hit)
    have t1 := move_eq q (hq 3) (hq 1) (Eq.trans (Eq.symm t0) (Eq.symm h1))
    exact branch17 p q v hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.trans (Eq.symm t0) (Eq.symm h1)) t1)
  · exact branch12 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch23 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 0)) hit
    have t1 := move_eq q (hq 3) (hq 0) t0
    exact branch23 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans hit t1)
  · exact branch23 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq q (hq 7) (hq 2) (Eq.symm h0)
    have t1 := move_eq q (hq 8) (hq 1) (Eq.symm h1)
    have t2 := move_eq p.symm (reverse_move p (hp 7)) (reverse_move p (hp 1)) (Eq.trans hit (Eq.symm t1))
    have t3 := move_eq q.symm (reverse_move q (hq 0)) (reverse_move q (hq 3)) (Eq.trans (Eq.symm t2) (Eq.symm h1))
    have t4 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 6)) (Eq.trans t0 t3)
    exact branch2 p q v hp hq sep (Eq.trans h0 (Eq.symm t4))
  · have t0 := move_eq p (hp 6) (hp 2) (Eq.symm h0)
    have t1 := move_eq q (hq 4) (hq 3) (Eq.symm t0)
    have t2 := move_eq p (hp 8) (hp 7) (Eq.trans t1 h1)
    have t3 := move_eq q.symm (reverse_move q (hq 6)) (reverse_move q (hq 0)) (Eq.trans t2 hit)
    exact branch20 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t3)
  · have t0 := move_eq q.symm (reverse_move q (hq 0)) (reverse_move q (hq 3)) (Eq.symm hit)
    have t1 := move_eq p (hp 4) (hp 0) (Eq.symm t0)
    exact branch23 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans t1 hit)
  · have t0 := move_eq q.symm (reverse_move q (hq 1)) (reverse_move q (hq 0)) hit
    exact branch13 p q v hp hq sep (Eq.trans (Eq.symm t0) h1)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep in
private theorem branch24 (h1 : v 4 = v 15) : False := by
  exact (sep (v 4)).2.2 (Eq.trans (hp 3) (Eq.symm (Eq.trans (congrArg q (h1)) (hq 9))))

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep in
private theorem branch25 (h1 : v 4 = v 12) : False := by
  have t0 := move_eq p (hp 7) (hp 3) (Eq.symm h1)
  exact (sep (v 9)).2.1 (Eq.trans (congrArg q (Eq.symm t0)) (hq 9))

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch26 (h1 : v 15 = v 2) : False := by
  exact short4 p q G sep e₀ e₁ e₂ no ![0,1,2,1] (by decide)
    (v 2) (v 2) (v 12) (v 6)
    (rfl) (Eq.trans (hp 7) h1) (hq 8) (hp 1)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep in
private theorem branch27 (h1 : v 15 = v 6) : False := by
  have t0 := move_eq p.symm (reverse_move p (hp 7)) (reverse_move p (hp 1)) h1
  exact (sep (v 2)).2.2 (Eq.trans (hp 1) (Eq.symm (Eq.trans (congrArg q (Eq.symm t0)) (hq 8))))

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch3 (h0 : v 3 = v 11) : False := by
  have t0 := move_eq p (hp 6) (hp 2) (Eq.symm h0)
  rcases collision16 (fun h => no (.inr (.inr h)))
    (v 0) (v 0) (v 3) (v 5) (v 5) (v 1) (v 1) (v 4) (v 4) (v 9) (v 15) (v 15) (v 12) (v 6) (v 2) (v 2)
    (e₀ (v 0))
    ((hq 2) ▸ e₂ (v 3))
    ((Eq.trans (hp 2) (Eq.symm t0)) ▸ e₁ (v 3))
    (e₀ (v 5))
    ((hq 3) ▸ e₂ (v 5))
    (e₀ (v 1))
    ((hq 1) ▸ e₂ (v 1))
    (e₀ (v 4))
    ((hp 3) ▸ e₁ (v 4))
    ((hq 9) ▸ e₂ (v 15))
    (e₀ (v 15))
    ((hp 7) ▸ e₁ (v 12))
    ((hq 8) ▸ e₂ (v 12))
    ((hp 1) ▸ e₁ (v 2))
    (e₀ (v 2))
    ((hq 0) ▸ e₂ (v 0)) with hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit
  · exact branch4 p q v hq sep hit
  · have t0 := move_eq q (hq 7) (hq 2) (Eq.symm h0)
    have t1 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 6)) (Eq.trans t0 hit)
    exact branch2 p q v hp hq sep (Eq.trans h0 (Eq.symm t1))
  · have t0 := move_eq q.symm (reverse_move q (hq 3)) (reverse_move q (hq 2)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 6)) (reverse_move p (hp 5)) t0
    exact branch1 p q v hp sep (Eq.trans h0 t1)
  · exact branch5 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · exact branch6 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · exact branch13 p q v hp hq sep hit
  · have t0 := move_eq q.symm (reverse_move q (hq 0)) (reverse_move q (hq 2)) (Eq.symm hit)
    exact branch4 p q v hq sep t0
  · have t0 := move_eq q (hq 7) (hq 2) (Eq.symm h0)
    have t1 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 6)) (Eq.trans t0 hit)
    exact branch2 p q v hp hq sep (Eq.trans h0 (Eq.symm t1))
  · have t0 := move_eq q.symm (reverse_move q (hq 3)) (reverse_move q (hq 2)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 6)) (reverse_move p (hp 5)) t0
    exact branch1 p q v hp sep (Eq.trans h0 t1)
  · exact branch5 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · exact branch14 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · exact branch6 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · have t0 := move_eq q.symm (reverse_move q (hq 8)) (reverse_move q (hq 2)) (Eq.symm hit)
    have t1 := move_eq p (hp 7) (hp 2) t0
    have t2 := move_eq p (hp 6) (hp 2) (Eq.symm h0)
    have t3 := move_eq q (hq 9) (hq 3) (Eq.trans t1 (Eq.symm t2))
    have t4 := move_eq p.symm (reverse_move p (hp 3)) (reverse_move p (hp 0)) t3
    exact branch5 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.symm t4)
  · have t0 := move_eq q.symm (reverse_move q (hq 0)) (reverse_move q (hq 2)) (Eq.symm hit)
    exact branch4 p q v hq sep t0
  · have t0 := move_eq p.symm (reverse_move p (hp 6)) (reverse_move p (hp 5)) (Eq.symm hit)
    exact branch1 p q v hp sep (Eq.trans h0 t0)
  · have t0 := move_eq q (hq 2) (hq 1) hit
    exact branch5 p q v hp hq sep G e₀ e₁ e₂ no h0 t0
  · exact branch15 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · have t0 := move_eq q (hq 9) (hq 2) (Eq.symm hit)
    exact branch14 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.symm t0)
  · have t0 := move_eq p (hp 7) (hp 2) (Eq.symm hit)
    have t1 := move_eq p (hp 6) (hp 2) (Eq.symm h0)
    have t2 := move_eq q (hq 9) (hq 3) (Eq.trans t0 (Eq.symm t1))
    have t3 := move_eq p.symm (reverse_move p (hp 3)) (reverse_move p (hp 0)) t2
    exact branch5 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.symm t3)
  · exact branch16 p q v hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 6)) (reverse_move p (hp 0)) hit
    exact branch4 p q v hq sep (Eq.trans (Eq.symm t0) (Eq.symm h0))
  · exact branch17 p q v hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 3)) (reverse_move p (hp 6)) (Eq.symm hit)
    exact branch15 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.trans h0 (Eq.symm t0))
  · have t0 := move_eq q (hq 9) (hq 3) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 3)) (reverse_move p (hp 0)) t0
    exact branch5 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.symm t1)
  · have t0 := move_eq p.symm (reverse_move p (hp 1)) (reverse_move p (hp 6)) (Eq.symm hit)
    exact branch16 p q v hq sep G e₀ e₁ e₂ no (Eq.trans h0 (Eq.symm t0))
  · exact branch18 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · have t0 := move_eq q (hq 3) (hq 1) hit
    exact branch17 p q v hq sep G e₀ e₁ e₂ no (Eq.trans hit t0)
  · exact branch17 p q v hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq q (hq 9) (hq 3) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 3)) (reverse_move p (hp 0)) t0
    exact branch5 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.symm t1)
  · have t0 := move_eq q (hq 8) (hq 3) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 1)) (reverse_move p (hp 0)) t0
    have t2 := move_eq q.symm (reverse_move q (hq 0)) (reverse_move q (hq 2)) t1
    exact branch4 p q v hq sep t2
  · exact branch18 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · have t0 := move_eq q.symm (reverse_move q (hq 1)) (reverse_move q (hq 3)) (Eq.symm hit)
    exact branch17 p q v hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t0) hit)
  · have t0 := move_eq p.symm (reverse_move p (hp 3)) (reverse_move p (hp 0)) (Eq.symm hit)
    exact branch5 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 7)) (reverse_move p (hp 0)) (Eq.symm hit)
    exact branch13 p q v hp hq sep (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 1)) (reverse_move p (hp 0)) (Eq.symm hit)
    have t1 := move_eq q.symm (reverse_move q (hq 0)) (reverse_move q (hq 2)) t0
    exact branch4 p q v hq sep t1
  · have t0 := move_eq q (hq 7) (hq 2) (Eq.symm h0)
    have t1 := move_eq q.symm (reverse_move q (hq 0)) (reverse_move q (hq 3)) (Eq.symm hit)
    have t2 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 6)) (Eq.trans t0 t1)
    exact branch2 p q v hp hq sep (Eq.trans h0 (Eq.symm t2))
  · have t0 := move_eq q.symm (reverse_move q (hq 1)) (reverse_move q (hq 3)) (Eq.symm hit)
    exact branch17 p q v hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t0) hit)
  · have t0 := move_eq p.symm (reverse_move p (hp 7)) (reverse_move p (hp 0)) (Eq.symm hit)
    exact branch13 p q v hp hq sep (Eq.symm t0)
  · exact branch19 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · have t0 := move_eq q.symm (reverse_move q (hq 0)) (reverse_move q (hq 3)) (Eq.symm hit)
    have t1 := move_eq p (hp 4) (hp 0) (Eq.symm t0)
    exact branch23 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans t1 hit)
  · have t0 := move_eq q.symm (reverse_move q (hq 9)) (reverse_move q (hq 1)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 7)) (reverse_move p (hp 0)) t0
    exact branch13 p q v hp hq sep (Eq.symm t1)
  · exact branch24 p q v hp hq sep hit
  · have t0 := move_eq q.symm (reverse_move q (hq 8)) (reverse_move q (hq 1)) (Eq.symm hit)
    exact branch19 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.symm t0)
  · have t0 := move_eq q.symm (reverse_move q (hq 1)) (reverse_move q (hq 0)) hit
    have t1 := move_eq q.symm (reverse_move q (hq 3)) (reverse_move q (hq 2)) t0
    have t2 := move_eq p.symm (reverse_move p (hp 6)) (reverse_move p (hp 5)) t1
    exact branch1 p q v hp sep (Eq.trans h0 t2)
  · exact branch24 p q v hp hq sep hit
  · exact branch25 p q v hp hq sep hit
  · have t0 := move_eq q.symm (reverse_move q (hq 1)) (reverse_move q (hq 0)) hit
    have t1 := move_eq q.symm (reverse_move q (hq 3)) (reverse_move q (hq 2)) t0
    have t2 := move_eq p.symm (reverse_move p (hp 6)) (reverse_move p (hp 5)) t1
    exact branch1 p q v hp sep (Eq.trans h0 t2)
  · have t0 := move_eq p.symm (reverse_move p (hp 7)) (reverse_move p (hp 3)) (Eq.symm hit)
    exact branch25 p q v hp hq sep (Eq.symm t0)
  · have t0 := move_eq p (hp 6) (hp 2) (Eq.symm h0)
    have t1 := move_eq q (hq 4) (hq 3) (Eq.symm t0)
    have t2 := move_eq p.symm (reverse_move p (hp 3)) (reverse_move p (hp 1)) hit
    have t3 := move_eq q.symm (reverse_move q (hq 1)) (reverse_move q (hq 0)) t2
    have t4 := move_eq q.symm (reverse_move q (hq 4)) (reverse_move q (hq 2)) (Eq.trans t1 t3)
    have t5 := move_eq p.symm (reverse_move p (hp 6)) (reverse_move p (hp 5)) (Eq.trans t0 t4)
    exact branch1 p q v hp sep (Eq.trans h0 t5)
  · have t0 := move_eq q.symm (reverse_move q (hq 9)) (reverse_move q (hq 0)) hit
    exact branch6 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.symm t0)
  · have t0 := move_eq p (hp 6) (hp 2) (Eq.symm h0)
    have t1 := move_eq q (hq 4) (hq 3) (Eq.symm t0)
    have t2 := move_eq q (hq 9) (hq 8) hit
    have t3 := move_eq p.symm (reverse_move p (hp 3)) (reverse_move p (hp 1)) t2
    have t4 := move_eq q.symm (reverse_move q (hq 1)) (reverse_move q (hq 0)) t3
    have t5 := move_eq q.symm (reverse_move q (hq 4)) (reverse_move q (hq 2)) (Eq.trans t1 t4)
    have t6 := move_eq p.symm (reverse_move p (hp 6)) (reverse_move p (hp 5)) (Eq.trans t0 t5)
    exact branch1 p q v hp sep (Eq.trans h0 t6)
  · exact branch26 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch27 p q v hp hq sep hit
  · exact branch26 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p (hp 7) (hp 1) hit
    exact branch27 p q v hp hq sep t0
  · have t0 := move_eq q.symm (reverse_move q (hq 8)) (reverse_move q (hq 0)) hit
    exact branch13 p q v hp hq sep (Eq.symm t0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep in
private theorem branch28 (h0 : v 3 = v 5) : False := by
  have t0 := move_eq q (hq 3) (hq 2) (Eq.symm h0)
  exact (sep (v 0)).1 (Eq.trans (hp 0) t0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch31 (h0 : v 3 = v 10) (h1 : v 0 = v 15) (h2 : v 12 = v 17) : False := by
  have t0 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 5)) (Eq.symm h0)
  have t1 := move_eq q (hq 5) (hq 3) (Eq.symm t0)
  have t2 := move_eq q (hq 9) (hq 0) (Eq.symm h1)
  exact short8 p q G sep e₀ e₁ e₂ no ![0,1,0,1,2,0,1,2] (by decide)
    (v 0) (v 0) (v 12) (v 12) (v 1) (v 4) (v 4) (v 2)
    (rfl) (Eq.trans (hp 7) (Eq.symm h1)) (rfl) (Eq.trans (congrArg p (Eq.symm t1)) (Eq.trans (hp 9) (Eq.symm h2))) (hq 1) (rfl) (Eq.trans (hp 3) t2) (hq 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch32 (h0 : v 3 = v 10) (h1 : v 0 = v 15) (h2 : v 7 = v 4) : False := by
  have t0 := move_eq q (hq 6) (hq 2) (Eq.symm h0)
  have t1 := move_eq p.symm (reverse_move p (hp 8)) (reverse_move p (hp 7)) (Eq.trans t0 h1)
  exact short8 p q G sep e₀ e₁ e₂ no ![0,1,0,2,0,2,0,1] (by decide)
    (v 0) (v 0) (v 12) (v 12) (v 4) (v 4) (v 1) (v 1)
    (rfl) (Eq.trans (hp 7) (Eq.symm h1)) (rfl) (Eq.trans (congrArg q (Eq.symm h2)) (Eq.trans (hq 4) t1)) (rfl) (hq 1) (rfl) (hp 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch33 (h2 : v 5 = v 2) : False := by
  exact short4 p q G sep e₀ e₁ e₂ no ![1,2,0,2] (by decide)
    (v 0) (v 1) (v 2) (v 2)
    (hp 0) (Eq.trans (congrArg q (Eq.symm h2)) (hq 3)) (rfl) (hq 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch30 (h0 : v 3 = v 10) (h1 : v 0 = v 15) : False := by
  have t0 := move_eq q (hq 6) (hq 2) (Eq.symm h0)
  have t1 := move_eq p.symm (reverse_move p (hp 8)) (reverse_move p (hp 7)) (Eq.trans t0 h1)
  have t2 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 5)) (Eq.symm h0)
  have t3 := move_eq q (hq 5) (hq 3) (Eq.symm t2)
  have t4 := move_eq q (hq 9) (hq 0) (Eq.symm h1)
  rcases collision16 (fun h => no (.inr (.inr h)))
    (v 0) (v 0) (v 12) (v 12) (v 7) (v 7) (v 3) (v 3) (v 5) (v 5) (v 11) (v 17) (v 1) (v 4) (v 4) (v 2)
    (e₀ (v 0))
    ((Eq.trans (hp 7) (Eq.symm h1)) ▸ e₁ (v 12))
    (e₀ (v 12))
    ((Eq.trans (hq 4) t1) ▸ e₂ (v 7))
    (e₀ (v 7))
    ((hp 2) ▸ e₁ (v 3))
    (e₀ (v 3))
    ((Eq.trans (hp 4) (Eq.symm h0)) ▸ e₁ (v 5))
    (e₀ (v 5))
    ((hp 6) ▸ e₁ (v 11))
    ((hq 7) ▸ e₂ (v 11))
    ((Eq.trans (congrArg p (Eq.symm t3)) (hp 9)) ▸ e₁ (v 1))
    ((hq 1) ▸ e₂ (v 1))
    (e₀ (v 4))
    ((Eq.trans (hp 3) t4) ▸ e₁ (v 4))
    ((hq 0) ▸ e₂ (v 0)) with hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit
  · exact branch13 p q v hp hq sep hit
  · have t0 := move_eq q (hq 6) (hq 2) (Eq.symm h0)
    have t1 := move_eq q (hq 4) (hq 0) (Eq.symm hit)
    have t2 := move_eq p (hp 8) (hp 1) t1
    exact branch27 p q v hp hq sep (Eq.trans (Eq.trans (Eq.symm h1) (Eq.symm t0)) t2)
  · exact branch4 p q v hq sep hit
  · have t0 := move_eq p (hp 4) (hp 0) (Eq.symm hit)
    have t1 := move_eq q (hq 3) (hq 0) (Eq.symm hit)
    exact branch23 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans t0 t1)
  · have t0 := move_eq p (hp 6) (hp 0) (Eq.symm hit)
    have t1 := move_eq q (hq 3) (hq 1) t0
    exact branch17 p q v hq sep G e₀ e₁ e₂ no (Eq.trans t0 t1)
  · have t0 := move_eq q.symm (reverse_move q (hq 3)) (reverse_move q (hq 2)) (Eq.symm hit)
    exact branch28 p q v hp hq sep (Eq.symm t0)
  · exact branch24 p q v hp hq sep (Eq.trans (Eq.symm hit) h1)
  · exact branch13 p q v hp hq sep hit
  · have t0 := move_eq q (hq 6) (hq 2) (Eq.symm h0)
    have t1 := move_eq q (hq 4) (hq 0) (Eq.symm hit)
    have t2 := move_eq p (hp 8) (hp 1) t1
    exact branch27 p q v hp hq sep (Eq.trans (Eq.trans (Eq.symm h1) (Eq.symm t0)) t2)
  · exact branch4 p q v hq sep hit
  · have t0 := move_eq p (hp 4) (hp 0) (Eq.symm hit)
    have t1 := move_eq q (hq 3) (hq 0) (Eq.symm hit)
    exact branch23 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans t0 t1)
  · have t0 := move_eq q.symm (reverse_move q (hq 7)) (reverse_move q (hq 2)) (Eq.symm hit)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · exact branch24 p q v hp hq sep (Eq.trans (Eq.symm hit) h1)
  · exact branch26 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm h1) hit)
  · have t0 := move_eq q (hq 6) (hq 2) (Eq.symm h0)
    have t1 := move_eq p.symm (reverse_move p (hp 8)) (reverse_move p (hp 7)) (Eq.trans t0 h1)
    have t2 := move_eq q (hq 8) (hq 4) hit
    have t3 := move_eq p.symm (reverse_move p (hp 2)) (reverse_move p (hp 1)) (Eq.trans (Eq.trans (Eq.symm hit) (Eq.symm t1)) (Eq.symm t2))
    exact branch16 p q v hq sep G e₀ e₁ e₂ no t3
  · have t0 := move_eq q (hq 8) (hq 2) hit
    exact branch27 p q v hp hq sep (Eq.trans (Eq.symm h1) (Eq.symm t0))
  · have t0 := move_eq p (hp 7) (hp 4) hit
    exact branch20 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans h1 t0)
  · have t0 := move_eq p (hp 7) (hp 6) hit
    have t1 := move_eq p (hp 4) (hp 0) (Eq.trans (Eq.symm t0) (Eq.symm h1))
    have t2 := move_eq q (hq 3) (hq 0) (Eq.trans (Eq.symm t0) (Eq.symm h1))
    exact branch23 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans t1 t2)
  · have t0 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 5)) (Eq.symm h0)
    have t1 := move_eq q (hq 5) (hq 3) (Eq.symm t0)
    have t2 := move_eq p (hp 9) (hp 7) (Eq.trans t1 (Eq.symm hit))
    have t3 := move_eq q.symm (reverse_move q (hq 7)) (reverse_move q (hq 2)) (Eq.trans t2 (Eq.symm h1))
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t3)
  · exact branch25 p q v hp hq sep (Eq.symm hit)
  · have t0 := move_eq q (hq 6) (hq 2) (Eq.symm h0)
    have t1 := move_eq p.symm (reverse_move p (hp 8)) (reverse_move p (hp 7)) (Eq.trans t0 h1)
    have t2 := move_eq q (hq 8) (hq 4) hit
    have t3 := move_eq p.symm (reverse_move p (hp 2)) (reverse_move p (hp 1)) (Eq.trans (Eq.trans (Eq.symm hit) (Eq.symm t1)) (Eq.symm t2))
    exact branch16 p q v hq sep G e₀ e₁ e₂ no t3
  · have t0 := move_eq q (hq 8) (hq 2) hit
    exact branch27 p q v hp hq sep (Eq.trans (Eq.symm h1) (Eq.symm t0))
  · have t0 := move_eq p (hp 7) (hp 4) hit
    exact branch20 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans h1 t0)
  · exact branch31 p q v hp hq sep G e₀ e₁ e₂ no h0 h1 hit
  · exact branch25 p q v hp hq sep (Eq.symm hit)
  · have t0 := move_eq p (hp 7) (hp 1) hit
    exact branch27 p q v hp hq sep t0
  · have t0 := move_eq p.symm (reverse_move p (hp 2)) (reverse_move p (hp 5)) hit
    exact branch1 p q v hp sep t0
  · have t0 := move_eq p.symm (reverse_move p (hp 2)) (reverse_move p (hp 6)) hit
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq q (hq 6) (hq 2) (Eq.symm h0)
    have t1 := move_eq p.symm (reverse_move p (hp 8)) (reverse_move p (hp 7)) (Eq.trans t0 h1)
    have t2 := move_eq q (hq 7) (hq 4) (Eq.symm hit)
    exact branch31 p q v hp hq sep G e₀ e₁ e₂ no h0 h1 (Eq.trans (Eq.symm t1) (Eq.symm t2))
  · have t0 := move_eq p.symm (reverse_move p (hp 2)) (reverse_move p (hp 0)) hit
    exact branch4 p q v hq sep (Eq.symm t0)
  · exact branch32 p q v hp hq sep G e₀ e₁ e₂ no h0 h1 hit
  · have t0 := move_eq p.symm (reverse_move p (hp 2)) (reverse_move p (hp 5)) hit
    exact branch1 p q v hp sep t0
  · have t0 := move_eq p.symm (reverse_move p (hp 2)) (reverse_move p (hp 6)) hit
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 2)) (Eq.symm hit)
    exact branch2 p q v hp hq sep (Eq.symm t0)
  · exact branch32 p q v hp hq sep G e₀ e₁ e₂ no h0 h1 hit
  · have t0 := move_eq q (hq 9) (hq 0) (Eq.symm h1)
    have t1 := move_eq p.symm (reverse_move p (hp 3)) (reverse_move p (hp 2)) (Eq.trans t0 (Eq.symm hit))
    exact branch10 p q v hp hq sep G e₀ e₁ e₂ no h1 (Eq.symm t1)
  · exact branch28 p q v hp hq sep hit
  · exact branch3 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq q (hq 2) (hq 1) hit
    exact branch24 p q v hp hq sep (Eq.trans (Eq.symm t0) h1)
  · exact branch10 p q v hp hq sep G e₀ e₁ e₂ no h1 hit
  · exact branch28 p q v hp hq sep hit
  · have t0 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 5)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 5)) (Eq.symm h0)
    have t2 := move_eq q (hq 5) (hq 3) (Eq.symm t1)
    have t3 := move_eq q (hq 3) (hq 1) (Eq.trans (Eq.trans t1 (Eq.symm t0)) t2)
    exact branch9 p q v hp hq sep G e₀ e₁ e₂ no h1 (Eq.trans (Eq.trans (Eq.symm t0) t2) t3)
  · exact branch10 p q v hp hq sep G e₀ e₁ e₂ no h1 hit
  · exact branch16 p q v hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p (hp 6) (hp 4) (Eq.symm hit)
    exact branch28 p q v hp hq sep (Eq.trans h0 (Eq.symm t0))
  · have t0 := move_eq q (hq 3) (hq 1) hit
    exact branch17 p q v hq sep G e₀ e₁ e₂ no (Eq.trans hit t0)
  · exact branch17 p q v hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 6)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 5)) (Eq.symm h0)
    have t2 := move_eq q (hq 5) (hq 3) (Eq.symm t1)
    have t3 := move_eq q (hq 7) (hq 1) (Eq.trans (Eq.symm t0) t2)
    exact branch17 p q v hq sep G e₀ e₁ e₂ no (Eq.trans hit t3)
  · exact branch17 p q v hq sep G e₀ e₁ e₂ no hit
  · exact branch33 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 5)) (Eq.symm h0)
    have t1 := move_eq q (hq 5) (hq 3) (Eq.symm t0)
    have t2 := move_eq p (hp 9) (hp 6) (Eq.trans t1 (Eq.symm hit))
    have t3 := move_eq q (hq 7) (hq 1) hit
    exact branch17 p q v hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t2) t3)
  · have t0 := move_eq p (hp 6) (hp 3) hit
    have t1 := move_eq q (hq 9) (hq 0) (Eq.symm h1)
    exact branch33 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans t0 t1)
  · have t0 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 5)) (Eq.symm h0)
    have t1 := move_eq q (hq 5) (hq 3) (Eq.symm t0)
    have t2 := move_eq q.symm (reverse_move q (hq 7)) (reverse_move q (hq 1)) hit
    have t3 := move_eq p (hp 9) (hp 6) (Eq.trans t1 (Eq.symm t2))
    exact branch17 p q v hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t3) hit)
  · have t0 := move_eq q.symm (reverse_move q (hq 7)) (reverse_move q (hq 0)) hit
    have t1 := move_eq p (hp 6) (hp 0) t0
    have t2 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 5)) (Eq.symm h0)
    have t3 := move_eq q (hq 5) (hq 3) (Eq.symm t2)
    have t4 := move_eq q (hq 9) (hq 0) (Eq.symm h1)
    have t5 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 3)) (Eq.trans hit (Eq.symm t4))
    exact branch17 p q v hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.trans t1 (Eq.symm t3)) t5)
  · have t0 := move_eq q.symm (reverse_move q (hq 1)) (reverse_move q (hq 3)) (Eq.symm hit)
    exact branch17 p q v hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t0) hit)
  · have t0 := move_eq p (hp 3) (hp 1) hit
    have t1 := move_eq q.symm (reverse_move q (hq 9)) (reverse_move q (hq 8)) t0
    exact branch13 p q v hp hq sep (Eq.trans h1 t1)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hq sep in
private theorem branch35 (h2 : v 13 = v 7) : False := by
  exact (sep (v 7)).2.1 (Eq.trans (hq 4) h2)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch36 (h0 : v 3 = v 10) (h1 : v 1 = v 12) (h2 : v 13 = v 15) : False := by
  have t0 := move_eq q (hq 6) (hq 2) (Eq.symm h0)
  have t1 := move_eq q (hq 8) (hq 1) (Eq.symm h1)
  exact short8 p q G sep e₀ e₁ e₂ no ![0,1,0,1,2,1,0,2] (by decide)
    (v 0) (v 0) (v 13) (v 13) (v 1) (v 4) (v 2) (v 2)
    (rfl) (Eq.trans (hp 8) t0) (rfl) (Eq.trans (congrArg p (h1)) (Eq.trans (hp 7) (Eq.symm h2))) (hq 1) (Eq.trans (hp 1) t1) (rfl) (hq 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch37 (h2 : v 7 = v 2) : False := by
  exact short4 p q G sep e₀ e₁ e₂ no ![0,2,1,2] (by decide)
    (v 0) (v 0) (v 3) (v 2)
    (rfl) (hq 2) (Eq.trans (hp 2) h2) (hq 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch34 (h0 : v 3 = v 10) (h1 : v 1 = v 12) : False := by
  have t0 := move_eq q (hq 6) (hq 2) (Eq.symm h0)
  have t1 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 5)) (Eq.symm h0)
  have t2 := move_eq q (hq 5) (hq 3) (Eq.symm t1)
  have t3 := move_eq p (hp 9) (hp 7) (Eq.trans t2 h1)
  have t4 := move_eq q (hq 8) (hq 1) (Eq.symm h1)
  rcases collision16 (fun h => no (.inr (.inr h)))
    (v 0) (v 0) (v 13) (v 13) (v 7) (v 7) (v 3) (v 3) (v 5) (v 5) (v 11) (v 15) (v 1) (v 4) (v 2) (v 2)
    (e₀ (v 0))
    ((Eq.trans (hp 8) t0) ▸ e₁ (v 13))
    (e₀ (v 13))
    ((hq 4) ▸ e₂ (v 7))
    (e₀ (v 7))
    ((hp 2) ▸ e₁ (v 3))
    (e₀ (v 3))
    ((Eq.trans (hp 4) (Eq.symm h0)) ▸ e₁ (v 5))
    (e₀ (v 5))
    ((hp 6) ▸ e₁ (v 11))
    ((Eq.trans (hq 7) t3) ▸ e₂ (v 11))
    ((Eq.trans (congrArg p (h1)) (hp 7)) ▸ e₁ (v 1))
    ((hq 1) ▸ e₂ (v 1))
    ((Eq.trans (hp 1) t4) ▸ e₁ (v 2))
    (e₀ (v 2))
    ((hq 0) ▸ e₂ (v 0)) with hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit
  · have t0 := move_eq q (hq 6) (hq 2) (Eq.symm h0)
    have t1 := move_eq p (hp 8) (hp 0) (Eq.symm hit)
    exact branch13 p q v hp hq sep (Eq.trans (Eq.trans (Eq.symm t0) t1) h1)
  · have t0 := move_eq q (hq 6) (hq 2) (Eq.symm h0)
    have t1 := move_eq p.symm (reverse_move p (hp 8)) (reverse_move p (hp 2)) (Eq.trans t0 hit)
    have t2 := move_eq q (hq 4) (hq 0) (Eq.symm hit)
    exact branch16 p q v hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t1) t2)
  · exact branch4 p q v hq sep hit
  · have t0 := move_eq p (hp 4) (hp 0) (Eq.symm hit)
    have t1 := move_eq q (hq 3) (hq 0) (Eq.symm hit)
    exact branch23 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans t0 t1)
  · have t0 := move_eq p (hp 6) (hp 0) (Eq.symm hit)
    have t1 := move_eq q (hq 3) (hq 1) t0
    exact branch17 p q v hq sep G e₀ e₁ e₂ no (Eq.trans t0 t1)
  · exact branch13 p q v hp hq sep (Eq.trans hit h1)
  · have t0 := move_eq q.symm (reverse_move q (hq 0)) (reverse_move q (hq 2)) (Eq.symm hit)
    exact branch4 p q v hq sep t0
  · have t0 := move_eq q (hq 6) (hq 2) (Eq.symm h0)
    have t1 := move_eq p (hp 8) (hp 0) (Eq.symm hit)
    exact branch13 p q v hp hq sep (Eq.trans (Eq.trans (Eq.symm t0) t1) h1)
  · have t0 := move_eq q (hq 6) (hq 2) (Eq.symm h0)
    have t1 := move_eq p.symm (reverse_move p (hp 8)) (reverse_move p (hp 2)) (Eq.trans t0 hit)
    have t2 := move_eq q (hq 4) (hq 0) (Eq.symm hit)
    exact branch16 p q v hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t1) t2)
  · exact branch4 p q v hq sep hit
  · have t0 := move_eq p (hp 4) (hp 0) (Eq.symm hit)
    have t1 := move_eq q (hq 3) (hq 0) (Eq.symm hit)
    exact branch23 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans t0 t1)
  · exact branch30 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · have t0 := move_eq q.symm (reverse_move q (hq 1)) (reverse_move q (hq 2)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 0)) (Eq.trans (Eq.symm h0) (Eq.symm t0))
    exact branch17 p q v hq sep G e₀ e₁ e₂ no (Eq.trans t1 hit)
  · have t0 := move_eq q.symm (reverse_move q (hq 0)) (reverse_move q (hq 2)) (Eq.symm hit)
    exact branch4 p q v hq sep t0
  · exact branch35 p q v hq sep hit
  · have t0 := move_eq p (hp 8) (hp 2) hit
    have t1 := move_eq q (hq 6) (hq 2) (Eq.symm h0)
    have t2 := move_eq q (hq 4) (hq 0) (Eq.trans (Eq.symm t0) t1)
    exact branch16 p q v hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm hit) t2)
  · have t0 := move_eq q (hq 6) (hq 2) (Eq.symm h0)
    have t1 := move_eq p (hp 8) (hp 4) hit
    exact branch20 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t0) t1)
  · have t0 := move_eq p (hp 8) (hp 6) hit
    have t1 := move_eq q (hq 6) (hq 2) (Eq.symm h0)
    have t2 := move_eq p (hp 4) (hp 0) (Eq.trans (Eq.symm t0) t1)
    have t3 := move_eq q (hq 6) (hq 1) t2
    exact branch17 p q v hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t0) t3)
  · have t0 := move_eq q (hq 6) (hq 2) (Eq.symm h0)
    have t1 := move_eq p (hp 8) (hp 7) (Eq.trans hit h1)
    exact branch30 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.trans (Eq.symm t0) t1)
  · have t0 := move_eq q.symm (reverse_move q (hq 4)) (reverse_move q (hq 0)) hit
    have t1 := move_eq q (hq 6) (hq 2) (Eq.symm h0)
    have t2 := move_eq p (hp 8) (hp 1) hit
    have t3 := move_eq p.symm (reverse_move p (hp 2)) (reverse_move p (hp 1)) (Eq.trans (Eq.trans t0 (Eq.symm t1)) t2)
    exact branch16 p q v hq sep G e₀ e₁ e₂ no t3
  · exact branch35 p q v hq sep hit
  · have t0 := move_eq p (hp 8) (hp 2) hit
    have t1 := move_eq q (hq 6) (hq 2) (Eq.symm h0)
    have t2 := move_eq q (hq 4) (hq 0) (Eq.trans (Eq.symm t0) t1)
    exact branch16 p q v hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm hit) t2)
  · have t0 := move_eq q (hq 6) (hq 2) (Eq.symm h0)
    have t1 := move_eq p (hp 8) (hp 4) hit
    exact branch20 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t0) t1)
  · exact branch36 p q v hp hq sep G e₀ e₁ e₂ no h0 h1 hit
  · have t0 := move_eq q.symm (reverse_move q (hq 4)) (reverse_move q (hq 1)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 2)) (reverse_move p (hp 0)) t0
    exact branch4 p q v hq sep (Eq.symm t1)
  · have t0 := move_eq q.symm (reverse_move q (hq 4)) (reverse_move q (hq 0)) hit
    have t1 := move_eq q (hq 6) (hq 2) (Eq.symm h0)
    have t2 := move_eq p (hp 8) (hp 1) hit
    have t3 := move_eq p.symm (reverse_move p (hp 2)) (reverse_move p (hp 1)) (Eq.trans (Eq.trans t0 (Eq.symm t1)) t2)
    exact branch16 p q v hq sep G e₀ e₁ e₂ no t3
  · have t0 := move_eq p.symm (reverse_move p (hp 2)) (reverse_move p (hp 5)) hit
    exact branch1 p q v hp sep t0
  · have t0 := move_eq p.symm (reverse_move p (hp 2)) (reverse_move p (hp 6)) hit
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq q (hq 7) (hq 4) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 5)) (Eq.symm h0)
    have t2 := move_eq q (hq 5) (hq 3) (Eq.symm t1)
    have t3 := move_eq p (hp 9) (hp 7) (Eq.trans t2 h1)
    exact branch36 p q v hp hq sep G e₀ e₁ e₂ no h0 h1 (Eq.trans (Eq.symm t0) t3)
  · have t0 := move_eq p.symm (reverse_move p (hp 2)) (reverse_move p (hp 0)) hit
    exact branch4 p q v hq sep (Eq.symm t0)
  · exact branch37 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 2)) (reverse_move p (hp 5)) hit
    exact branch1 p q v hp sep t0
  · have t0 := move_eq p.symm (reverse_move p (hp 2)) (reverse_move p (hp 6)) hit
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq p.symm (reverse_move p (hp 7)) (reverse_move p (hp 2)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 5)) (Eq.symm h0)
    have t2 := move_eq p.symm (reverse_move p (hp 5)) (reverse_move p (hp 0)) (Eq.trans (Eq.symm t0) (Eq.symm h1))
    have t3 := move_eq q (hq 3) (hq 0) (Eq.trans t1 t2)
    exact branch16 p q v hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.trans (Eq.symm t0) (Eq.symm h1)) t3)
  · have t0 := move_eq q (hq 8) (hq 1) (Eq.symm h1)
    have t1 := move_eq p.symm (reverse_move p (hp 2)) (reverse_move p (hp 1)) (Eq.trans hit (Eq.symm t0))
    exact branch16 p q v hq sep G e₀ e₁ e₂ no t1
  · exact branch37 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch28 p q v hp hq sep hit
  · exact branch3 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 0)) (Eq.trans (Eq.symm h0) hit)
    have t1 := move_eq q (hq 2) (hq 1) hit
    exact branch17 p q v hq sep G e₀ e₁ e₂ no (Eq.trans t0 t1)
  · exact branch16 p q v hq sep G e₀ e₁ e₂ no hit
  · exact branch28 p q v hp hq sep hit
  · have t0 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 5)) (Eq.symm h0)
    have t1 := move_eq p.symm (reverse_move p (hp 7)) (reverse_move p (hp 5)) (Eq.symm hit)
    have t2 := move_eq q (hq 3) (hq 1) (Eq.trans (Eq.trans t0 (Eq.symm t1)) (Eq.symm h1))
    exact branch25 p q v hp hq sep (Eq.trans (Eq.symm t2) h1)
  · exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm h0) hit)
  · exact branch16 p q v hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p (hp 6) (hp 4) (Eq.symm hit)
    exact branch28 p q v hp hq sep (Eq.trans h0 (Eq.symm t0))
  · have t0 := move_eq q (hq 3) (hq 1) hit
    exact branch17 p q v hq sep G e₀ e₁ e₂ no (Eq.trans hit t0)
  · exact branch33 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 7)) (reverse_move p (hp 6)) (Eq.symm hit)
    have t1 := move_eq q (hq 7) (hq 1) (Eq.trans (Eq.symm t0) (Eq.symm h1))
    have t2 := move_eq q (hq 9) (hq 3) (Eq.symm hit)
    have t3 := move_eq p.symm (reverse_move p (hp 3)) (reverse_move p (hp 0)) t2
    have t4 := move_eq q.symm (reverse_move q (hq 7)) (reverse_move q (hq 2)) (Eq.trans t1 t3)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t4)
  · exact branch17 p q v hq sep G e₀ e₁ e₂ no hit
  · exact branch33 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 5)) (Eq.symm h0)
    have t1 := move_eq q (hq 5) (hq 3) (Eq.symm t0)
    have t2 := move_eq p (hp 9) (hp 6) (Eq.trans t1 (Eq.symm hit))
    have t3 := move_eq q (hq 7) (hq 1) hit
    exact branch17 p q v hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t2) t3)
  · have t0 := move_eq p (hp 6) (hp 1) hit
    have t1 := move_eq q (hq 8) (hq 1) (Eq.symm h1)
    exact branch17 p q v hq sep G e₀ e₁ e₂ no (Eq.trans t0 t1)
  · exact branch24 p q v hp hq sep (Eq.symm hit)
  · exact branch26 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p (hp 7) (hp 1) (Eq.trans (Eq.symm h1) hit)
    exact branch27 p q v hp hq sep t0
  · have t0 := move_eq q.symm (reverse_move q (hq 1)) (reverse_move q (hq 0)) hit
    exact branch13 p q v hp hq sep (Eq.trans (Eq.symm t0) h1)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch29 (h0 : v 3 = v 10) : False := by
  rcases collision16 (fun h => no (.inr (.inr h)))
    (v 0) (v 0) (v 3) (v 3) (v 5) (v 1) (v 1) (v 4) (v 4) (v 9) (v 15) (v 15) (v 12) (v 6) (v 2) (v 2)
    (e₀ (v 0))
    ((hq 2) ▸ e₂ (v 3))
    (e₀ (v 3))
    ((Eq.trans (hp 4) (Eq.symm h0)) ▸ e₁ (v 5))
    ((hq 3) ▸ e₂ (v 5))
    (e₀ (v 1))
    ((hq 1) ▸ e₂ (v 1))
    (e₀ (v 4))
    ((hp 3) ▸ e₁ (v 4))
    ((hq 9) ▸ e₂ (v 15))
    (e₀ (v 15))
    ((hp 7) ▸ e₁ (v 12))
    ((hq 8) ▸ e₂ (v 12))
    ((hp 1) ▸ e₁ (v 2))
    (e₀ (v 2))
    ((hq 0) ▸ e₂ (v 0)) with hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit
  · exact branch4 p q v hq sep hit
  · have t0 := move_eq p (hp 4) (hp 0) (Eq.symm hit)
    have t1 := move_eq q (hq 3) (hq 0) (Eq.symm hit)
    exact branch23 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans t0 t1)
  · have t0 := move_eq q.symm (reverse_move q (hq 3)) (reverse_move q (hq 2)) (Eq.symm hit)
    exact branch28 p q v hp hq sep (Eq.symm t0)
  · have t0 := move_eq q.symm (reverse_move q (hq 1)) (reverse_move q (hq 2)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 0)) (Eq.trans (Eq.symm h0) (Eq.symm t0))
    exact branch17 p q v hq sep G e₀ e₁ e₂ no (Eq.trans t1 hit)
  · exact branch30 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · exact branch13 p q v hp hq sep hit
  · have t0 := move_eq q.symm (reverse_move q (hq 0)) (reverse_move q (hq 2)) (Eq.symm hit)
    exact branch4 p q v hq sep t0
  · exact branch4 p q v hq sep hit
  · have t0 := move_eq q.symm (reverse_move q (hq 3)) (reverse_move q (hq 2)) (Eq.symm hit)
    exact branch28 p q v hp hq sep (Eq.symm t0)
  · have t0 := move_eq q.symm (reverse_move q (hq 1)) (reverse_move q (hq 2)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 0)) (Eq.trans (Eq.symm h0) (Eq.symm t0))
    exact branch17 p q v hq sep G e₀ e₁ e₂ no (Eq.trans t1 hit)
  · have t0 := move_eq q (hq 6) (hq 2) (Eq.symm h0)
    have t1 := move_eq p.symm (reverse_move p (hp 8)) (reverse_move p (hp 3)) (Eq.trans t0 hit)
    have t2 := move_eq q.symm (reverse_move q (hq 4)) (reverse_move q (hq 1)) t1
    have t3 := move_eq p.symm (reverse_move p (hp 2)) (reverse_move p (hp 0)) t2
    exact branch4 p q v hq sep (Eq.symm t3)
  · exact branch30 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · have t0 := move_eq q.symm (reverse_move q (hq 8)) (reverse_move q (hq 2)) (Eq.symm hit)
    have t1 := move_eq p (hp 7) (hp 2) t0
    have t2 := move_eq q (hq 9) (hq 4) t1
    have t3 := move_eq q (hq 6) (hq 2) (Eq.symm h0)
    have t4 := move_eq p.symm (reverse_move p (hp 8)) (reverse_move p (hp 1)) (Eq.trans t3 hit)
    have t5 := move_eq q.symm (reverse_move q (hq 9)) (reverse_move q (hq 0)) (Eq.trans t2 t4)
    exact branch30 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.symm t5)
  · have t0 := move_eq q.symm (reverse_move q (hq 0)) (reverse_move q (hq 2)) (Eq.symm hit)
    exact branch4 p q v hq sep t0
  · exact branch28 p q v hp hq sep hit
  · have t0 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 0)) (Eq.trans (Eq.symm h0) hit)
    have t1 := move_eq q (hq 2) (hq 1) hit
    exact branch17 p q v hq sep G e₀ e₁ e₂ no (Eq.trans t0 t1)
  · exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm h0) hit)
  · have t0 := move_eq p.symm (reverse_move p (hp 7)) (reverse_move p (hp 5)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 5)) (Eq.symm h0)
    have t2 := move_eq q (hq 8) (hq 3) (Eq.trans t0 (Eq.symm t1))
    have t3 := move_eq p.symm (reverse_move p (hp 1)) (reverse_move p (hp 0)) t2
    have t4 := move_eq q.symm (reverse_move q (hq 0)) (reverse_move q (hq 2)) t3
    exact branch4 p q v hq sep t4
  · have t0 := move_eq p (hp 7) (hp 2) (Eq.symm hit)
    have t1 := move_eq q (hq 9) (hq 4) t0
    have t2 := move_eq q (hq 6) (hq 2) (Eq.symm h0)
    have t3 := move_eq q (hq 8) (hq 2) (Eq.symm hit)
    have t4 := move_eq p.symm (reverse_move p (hp 8)) (reverse_move p (hp 1)) (Eq.trans t2 (Eq.symm t3))
    have t5 := move_eq q.symm (reverse_move q (hq 9)) (reverse_move q (hq 0)) (Eq.trans t1 t4)
    exact branch30 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.symm t5)
  · exact branch16 p q v hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 0)) (Eq.trans (Eq.symm h0) hit)
    have t1 := move_eq q (hq 2) (hq 1) hit
    exact branch17 p q v hq sep G e₀ e₁ e₂ no (Eq.trans t0 t1)
  · exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm h0) hit)
  · have t0 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 5)) (Eq.symm h0)
    have t1 := move_eq p.symm (reverse_move p (hp 3)) (reverse_move p (hp 5)) (Eq.symm hit)
    exact branch17 p q v hq sep G e₀ e₁ e₂ no (Eq.trans t0 (Eq.symm t1))
  · have t0 := move_eq p.symm (reverse_move p (hp 7)) (reverse_move p (hp 5)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 5)) (Eq.symm h0)
    have t2 := move_eq q (hq 8) (hq 3) (Eq.trans t0 (Eq.symm t1))
    have t3 := move_eq p.symm (reverse_move p (hp 1)) (reverse_move p (hp 0)) t2
    have t4 := move_eq q.symm (reverse_move q (hq 0)) (reverse_move q (hq 2)) t3
    exact branch4 p q v hq sep t4
  · have t0 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 5)) (Eq.symm h0)
    have t1 := move_eq p.symm (reverse_move p (hp 1)) (reverse_move p (hp 5)) (Eq.symm hit)
    exact branch33 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans t0 (Eq.symm t1))
  · exact branch16 p q v hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq q (hq 3) (hq 1) hit
    exact branch17 p q v hq sep G e₀ e₁ e₂ no (Eq.trans hit t0)
  · exact branch17 p q v hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq q (hq 9) (hq 3) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 3)) (reverse_move p (hp 0)) t0
    have t2 := move_eq q.symm (reverse_move q (hq 1)) (reverse_move q (hq 2)) t1
    have t3 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 5)) (Eq.symm h0)
    have t4 := move_eq q (hq 5) (hq 3) (Eq.symm t3)
    exact branch2 p q v hp hq sep (Eq.trans (Eq.symm t2) (Eq.symm t4))
  · have t0 := move_eq q (hq 8) (hq 3) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 1)) (reverse_move p (hp 0)) t0
    have t2 := move_eq q.symm (reverse_move q (hq 0)) (reverse_move q (hq 2)) t1
    exact branch4 p q v hq sep t2
  · exact branch33 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq q.symm (reverse_move q (hq 1)) (reverse_move q (hq 3)) (Eq.symm hit)
    exact branch17 p q v hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t0) hit)
  · have t0 := move_eq p.symm (reverse_move p (hp 3)) (reverse_move p (hp 0)) (Eq.symm hit)
    have t1 := move_eq q.symm (reverse_move q (hq 1)) (reverse_move q (hq 2)) t0
    have t2 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 0)) (Eq.trans (Eq.symm h0) (Eq.symm t1))
    exact branch17 p q v hq sep G e₀ e₁ e₂ no (Eq.trans t2 (Eq.symm t0))
  · have t0 := move_eq p.symm (reverse_move p (hp 7)) (reverse_move p (hp 0)) (Eq.symm hit)
    exact branch13 p q v hp hq sep (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 1)) (reverse_move p (hp 0)) (Eq.symm hit)
    have t1 := move_eq q.symm (reverse_move q (hq 0)) (reverse_move q (hq 2)) t0
    exact branch4 p q v hq sep t1
  · have t0 := move_eq q.symm (reverse_move q (hq 0)) (reverse_move q (hq 3)) (Eq.symm hit)
    have t1 := move_eq p (hp 4) (hp 0) (Eq.symm t0)
    exact branch23 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans t1 hit)
  · have t0 := move_eq q.symm (reverse_move q (hq 1)) (reverse_move q (hq 3)) (Eq.symm hit)
    exact branch17 p q v hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t0) hit)
  · have t0 := move_eq p.symm (reverse_move p (hp 7)) (reverse_move p (hp 0)) (Eq.symm hit)
    exact branch13 p q v hp hq sep (Eq.symm t0)
  · exact branch34 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · have t0 := move_eq q.symm (reverse_move q (hq 0)) (reverse_move q (hq 3)) (Eq.symm hit)
    have t1 := move_eq p (hp 4) (hp 0) (Eq.symm t0)
    exact branch23 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans t1 hit)
  · have t0 := move_eq q.symm (reverse_move q (hq 9)) (reverse_move q (hq 1)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 7)) (reverse_move p (hp 0)) t0
    exact branch13 p q v hp hq sep (Eq.symm t1)
  · exact branch24 p q v hp hq sep hit
  · have t0 := move_eq q.symm (reverse_move q (hq 8)) (reverse_move q (hq 1)) (Eq.symm hit)
    exact branch34 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.symm t0)
  · have t0 := move_eq q.symm (reverse_move q (hq 1)) (reverse_move q (hq 0)) hit
    have t1 := move_eq q.symm (reverse_move q (hq 3)) (reverse_move q (hq 2)) t0
    exact branch28 p q v hp hq sep (Eq.symm t1)
  · exact branch24 p q v hp hq sep hit
  · exact branch25 p q v hp hq sep hit
  · have t0 := move_eq q.symm (reverse_move q (hq 1)) (reverse_move q (hq 0)) hit
    have t1 := move_eq q.symm (reverse_move q (hq 3)) (reverse_move q (hq 2)) t0
    exact branch28 p q v hp hq sep (Eq.symm t1)
  · have t0 := move_eq p.symm (reverse_move p (hp 7)) (reverse_move p (hp 3)) (Eq.symm hit)
    exact branch25 p q v hp hq sep (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 5)) (Eq.symm h0)
    have t1 := move_eq q (hq 5) (hq 3) (Eq.symm t0)
    have t2 := move_eq p.symm (reverse_move p (hp 3)) (reverse_move p (hp 1)) hit
    have t3 := move_eq q.symm (reverse_move q (hq 1)) (reverse_move q (hq 0)) t2
    have t4 := move_eq q.symm (reverse_move q (hq 5)) (reverse_move q (hq 2)) (Eq.trans t1 t3)
    exact branch1 p q v hp sep (Eq.symm t4)
  · have t0 := move_eq q.symm (reverse_move q (hq 9)) (reverse_move q (hq 0)) hit
    exact branch30 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 5)) (Eq.symm h0)
    have t1 := move_eq q (hq 5) (hq 3) (Eq.symm t0)
    have t2 := move_eq q (hq 9) (hq 8) hit
    have t3 := move_eq p.symm (reverse_move p (hp 3)) (reverse_move p (hp 1)) t2
    have t4 := move_eq q.symm (reverse_move q (hq 1)) (reverse_move q (hq 0)) t3
    have t5 := move_eq q.symm (reverse_move q (hq 5)) (reverse_move q (hq 2)) (Eq.trans t1 t4)
    exact branch1 p q v hp sep (Eq.symm t5)
  · exact branch26 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch27 p q v hp hq sep hit
  · exact branch26 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p (hp 7) (hp 1) hit
    exact branch27 p q v hp hq sep t0
  · have t0 := move_eq q.symm (reverse_move q (hq 8)) (reverse_move q (hq 0)) hit
    exact branch13 p q v hp hq sep (Eq.symm t0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch38 (h0 : v 3 = v 13) : False := by
  exact short4 p q G sep e₀ e₁ e₂ no ![0,2,0,1] (by decide)
    (v 3) (v 3) (v 7) (v 7)
    (rfl) (Eq.trans (hq 4) (Eq.symm h0)) (rfl) (hp 2)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep in
private theorem branch39 (h0 : v 3 = v 17) : False := by
  have t0 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 5)) (Eq.symm h0)
  exact (sep (v 8)).2.1 (Eq.trans (hq 5) t0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch40 (h0 : v 3 = v 16) : False := by
  exact short8 p q G sep e₀ e₁ e₂ no ![0,2,0,2,0,1,2,1] (by decide)
    (v 0) (v 0) (v 3) (v 3) (v 10) (v 10) (v 5) (v 1)
    (rfl) (hq 2) (rfl) (Eq.trans (hq 6) (Eq.symm h0)) (rfl) (hp 4) (hq 3) (hp 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch41 (h0 : v 8 = v 10) : False := by
  exact short8 p q G sep e₀ e₁ e₂ no ![0,2,0,1,0,1,2,1] (by decide)
    (v 0) (v 0) (v 3) (v 3) (v 8) (v 8) (v 5) (v 1)
    (rfl) (hq 2) (rfl) (hp 5) (rfl) (Eq.trans (hp 4) (Eq.symm h0)) (hq 3) (hp 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp sep G e₀ e₁ e₂ no in
private theorem branch42 (h0 : v 8 = v 7) : False := by
  exact short4 p q G sep e₀ e₁ e₂ no ![0,1,0,1] (by decide)
    (v 3) (v 3) (v 7) (v 7)
    (rfl) (Eq.trans (congrArg p (Eq.symm h0)) (hp 5)) (rfl) (hp 2)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch43 (h0 : v 14 = v 5) : False := by
  have t0 := move_eq p (hp 9) (hp 4) h0
  exact short4 p q G sep e₀ e₁ e₂ no ![0,1,2,1] (by decide)
    (v 5) (v 5) (v 11) (v 10)
    (rfl) (hp 6) (Eq.trans (hq 7) t0) (hp 4)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch44 (h0 : v 14 = v 10) : False := by
  exact short8 p q G sep e₀ e₁ e₂ no ![0,2,0,1,2,1,2,1] (by decide)
    (v 0) (v 0) (v 3) (v 3) (v 8) (v 10) (v 5) (v 1)
    (rfl) (hq 2) (rfl) (hp 5) (Eq.trans (hq 5) h0) (hp 4) (hq 3) (hp 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch45 (h0 : v 14 = v 7) : False := by
  exact short4 p q G sep e₀ e₁ e₂ no ![0,1,2,1] (by decide)
    (v 3) (v 3) (v 8) (v 7)
    (rfl) (hp 5) (Eq.trans (hq 5) h0) (hp 2)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep in
private theorem branch46 (h0 : v 14 = v 11) : False := by
  have t0 := move_eq p (hp 9) (hp 6) h0
  exact (sep (v 11)).2.2 (Eq.trans (hp 6) (Eq.symm (Eq.trans (hq 7) t0)))

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch47 (h0 : v 17 = v 13) : False := by
  have t0 := move_eq q.symm (reverse_move q (hq 7)) (reverse_move q (hq 4)) h0
  exact short8 p q G sep e₀ e₁ e₂ no ![0,2,1,0,1,0,2,1] (by decide)
    (v 0) (v 0) (v 3) (v 7) (v 7) (v 5) (v 5) (v 1)
    (rfl) (hq 2) (hp 2) (rfl) (Eq.trans (congrArg p (Eq.symm t0)) (hp 6)) (rfl) (hq 3) (hp 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch48 (h0 : v 11 = v 13) : False := by
  have t0 := move_eq p (hp 8) (hp 6) (Eq.symm h0)
  exact short4 p q G sep e₀ e₁ e₂ no ![0,2,0,1] (by decide)
    (v 5) (v 5) (v 10) (v 10)
    (rfl) (Eq.trans (hq 6) t0) (rfl) (hp 4)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep in
private theorem branch49 (h0 : v 5 = v 13) : False := by
  have t0 := move_eq p (hp 8) (hp 4) (Eq.symm h0)
  exact (sep (v 10)).2.1 (Eq.trans (hq 6) t0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep in
private theorem branch50 (h0 : v 10 = v 13) : False := by
  exact (sep (v 10)).2.2 (Eq.trans (Eq.trans (congrArg p (h0)) (hp 8)) (Eq.symm (hq 6)))

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch0 : False := by
  rcases collision16 (fun h => no (.inr (.inr h)))
    (v 3) (v 3) (v 8) (v 14) (v 14) (v 17) (v 11) (v 5) (v 5) (v 10) (v 10) (v 16) (v 13) (v 13) (v 7) (v 7)
    (e₀ (v 3))
    ((hp 5) ▸ e₁ (v 8))
    ((hq 5) ▸ e₂ (v 8))
    (e₀ (v 14))
    ((hp 9) ▸ e₁ (v 14))
    ((hq 7) ▸ e₂ (v 11))
    ((hp 6) ▸ e₁ (v 11))
    (e₀ (v 5))
    ((hp 4) ▸ e₁ (v 5))
    (e₀ (v 10))
    ((hq 6) ▸ e₂ (v 10))
    ((hp 8) ▸ e₁ (v 13))
    (e₀ (v 13))
    ((hq 4) ▸ e₂ (v 7))
    (e₀ (v 7))
    ((hp 2) ▸ e₁ (v 3)) with hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit
  · exact branch1 p q v hp sep hit
  · exact branch2 p q v hp hq sep hit
  · exact branch3 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch28 p q v hp hq sep hit
  · exact branch29 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch38 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 2)) (reverse_move p (hp 5)) (Eq.symm hit)
    exact branch1 p q v hp sep t0
  · exact branch2 p q v hp hq sep hit
  · exact branch39 p q v hp hq sep hit
  · exact branch28 p q v hp hq sep hit
  · exact branch29 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch40 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch38 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 2)) (reverse_move p (hp 5)) (Eq.symm hit)
    exact branch1 p q v hp sep t0
  · have t0 := move_eq p (hp 9) (hp 5) (Eq.symm hit)
    exact branch39 p q v hp hq sep (Eq.symm t0)
  · have t0 := move_eq p (hp 6) (hp 5) (Eq.symm hit)
    exact branch28 p q v hp hq sep (Eq.symm t0)
  · have t0 := move_eq p (hp 5) (hp 4) hit
    exact branch29 p q v hp hq sep G e₀ e₁ e₂ no t0
  · exact branch41 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p (hp 8) (hp 5) (Eq.symm hit)
    exact branch40 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · exact branch42 p q v hp sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq q.symm (reverse_move q (hq 7)) (reverse_move q (hq 5)) (Eq.symm hit)
    have t1 := move_eq p (hp 6) (hp 5) t0
    exact branch28 p q v hp hq sep (Eq.symm t1)
  · exact branch43 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch44 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq q.symm (reverse_move q (hq 6)) (reverse_move q (hq 5)) (Eq.symm hit)
    exact branch41 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq q.symm (reverse_move q (hq 5)) (reverse_move q (hq 4)) hit
    exact branch42 p q v hp sep G e₀ e₁ e₂ no t0
  · exact branch45 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch46 p q v hp hq sep hit
  · exact branch43 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch44 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq q.symm (reverse_move q (hq 5)) (reverse_move q (hq 4)) hit
    exact branch42 p q v hp sep G e₀ e₁ e₂ no t0
  · exact branch45 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 6)) hit
    exact branch46 p q v hp hq sep t0
  · have t0 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 4)) hit
    exact branch43 p q v hp hq sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 8)) hit
    have t1 := move_eq q.symm (reverse_move q (hq 5)) (reverse_move q (hq 4)) t0
    exact branch42 p q v hp sep G e₀ e₁ e₂ no t1
  · exact branch47 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 2)) hit
    exact branch2 p q v hp hq sep (Eq.symm t0)
  · have t0 := move_eq q (hq 7) (hq 3) hit
    have t1 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 0)) t0
    have t2 := move_eq q.symm (reverse_move q (hq 5)) (reverse_move q (hq 2)) t1
    exact branch1 p q v hp sep (Eq.symm t2)
  · have t0 := move_eq q (hq 7) (hq 6) hit
    have t1 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 8)) t0
    have t2 := move_eq q.symm (reverse_move q (hq 5)) (reverse_move q (hq 4)) t1
    exact branch42 p q v hp sep G e₀ e₁ e₂ no t2
  · exact branch48 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq q (hq 7) (hq 4) hit
    exact branch47 p q v hp hq sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 6)) (Eq.symm hit)
    have t1 := move_eq q (hq 7) (hq 3) (Eq.symm t0)
    have t2 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 0)) t1
    have t3 := move_eq q.symm (reverse_move q (hq 5)) (reverse_move q (hq 2)) t2
    exact branch1 p q v hp sep (Eq.symm t3)
  · have t0 := move_eq p.symm (reverse_move p (hp 8)) (reverse_move p (hp 6)) (Eq.symm hit)
    exact branch48 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · exact branch49 p q v hp hq sep hit
  · have t0 := move_eq p.symm (reverse_move p (hp 2)) (reverse_move p (hp 6)) (Eq.symm hit)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 6)) (Eq.symm hit)
    have t1 := move_eq q (hq 7) (hq 3) (Eq.symm t0)
    have t2 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 0)) t1
    have t3 := move_eq q.symm (reverse_move q (hq 5)) (reverse_move q (hq 2)) t2
    exact branch1 p q v hp sep (Eq.symm t3)
  · exact branch49 p q v hp hq sep hit
  · have t0 := move_eq p.symm (reverse_move p (hp 2)) (reverse_move p (hp 6)) (Eq.symm hit)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq p.symm (reverse_move p (hp 8)) (reverse_move p (hp 4)) (Eq.symm hit)
    exact branch49 p q v hp hq sep (Eq.symm t0)
  · exact branch50 p q v hp hq sep hit
  · have t0 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 2)) hit
    exact branch28 p q v hp hq sep (Eq.symm t0)
  · exact branch50 p q v hp hq sep hit
  · have t0 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 2)) hit
    exact branch28 p q v hp hq sep (Eq.symm t0)
  · have t0 := move_eq q.symm (reverse_move q (hq 6)) (reverse_move q (hq 4)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 4)) (reverse_move p (hp 2)) t0
    exact branch28 p q v hp hq sep (Eq.symm t1)
  · have t0 := move_eq p.symm (reverse_move p (hp 8)) (reverse_move p (hp 2)) hit
    exact branch38 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · exact branch35 p q v hq sep hit
  · exact branch35 p q v hq sep hit

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 8000 in
/-- Checking the conjugate square at three specified translates of one point suffices. -/
theorem local_matching_cycle (p q : Equiv.Perm X)
    (x : X) (squares : ∀ i : Fin 3, let y := ((![q,(1 : Equiv.Perm X),q*p⁻¹*q⁻¹] : Fin 3 → Equiv.Perm X) i) x;
      (p*(q*p*q⁻¹)) y = ((q*p*q⁻¹)*p) y)
    (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x)
    (G : SimpleGraph (Bool × X))
    (e₀ : ∀ x, G.Adj (false,x) (true,x))
    (e₁ : ∀ x, G.Adj (false,x) (true,p x))
    (e₂ : ∀ x, G.Adj (false,x) (true,q x)) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G := by

  classical
  have t0_12 : (p*(q⁻¹*p*q)) x=(q⁻¹*p*q*p) x := by
    have h := congrArg (fun y : X => (q⁻¹ : Equiv.Perm X) y) ((squares 0).symm)
    calc
      _ = ((q⁻¹)*(q*p*q⁻¹*p)*(q)) x := congrArg (fun g : Equiv.Perm X => g x) (by group : _ = _)
      _ = ((q⁻¹)*(p*q*p*q⁻¹)*(q)) x := h
      _ = _ := congrArg (fun g : Equiv.Perm X => g x) (by group : _ = _)
  have t0_13 : (p*(q*p*q⁻¹)) x=(q*p*q⁻¹*p) x := by
    have h := congrArg (fun y : X => ((1 : Equiv.Perm X) : Equiv.Perm X) y) (squares 1)
    calc
      _ = (((1 : Equiv.Perm X))*(p*q*p*q⁻¹)*((1 : Equiv.Perm X))) x := congrArg (fun g : Equiv.Perm X => g x) (by group : _ = _)
      _ = (((1 : Equiv.Perm X))*(q*p*q⁻¹*p)*((1 : Equiv.Perm X))) x := h
      _ = _ := congrArg (fun g : Equiv.Perm X => g x) (by group : _ = _)
  have t0_14 : (p*(q*p⁻¹*q⁻¹)) x=(q*p⁻¹*q⁻¹*p) x := by
    have h := congrArg (fun y : X => (q*p⁻¹*q⁻¹ : Equiv.Perm X) y) ((squares 2).symm)
    calc
      _ = ((q*p⁻¹*q⁻¹)*(q*p*q⁻¹*p)*(q*p⁻¹*q⁻¹)) x := congrArg (fun g : Equiv.Perm X => g x) (by group : _ = _)
      _ = ((q*p⁻¹*q⁻¹)*(p*q*p*q⁻¹)*(q*p⁻¹*q⁻¹)) x := h
      _ = _ := congrArg (fun g : Equiv.Perm X => g x) (by group : _ = _)
  let W : List (Equiv.Perm X) := [
    (1 : Equiv.Perm X),p,q,q⁻¹,q*p,q⁻¹*p,
    p*q,p*q⁻¹,p⁻¹*q⁻¹,p*q*p,p*q⁻¹*p,p⁻¹*q⁻¹*p,
    q⁻¹*p*q,q*p*q⁻¹,q*p⁻¹*q⁻¹,q⁻¹*p*q*p,q*p*q⁻¹*p,q*p⁻¹*q⁻¹*p]
  let v (i : ℕ) := (W.getD i 1) x
  have hp (i : Fin 10) : let e := ([(0,1),(2,6),(3,7),(4,9),(5,10),(8,3),(11,5),(12,15),(13,16),(14,17)] : List (ℕ × ℕ)).get i; p (v e.1)=v e.2 := by
    fin_cases i
    · change (p*((1 : Equiv.Perm X))) x = (p) x
      exact congrArg (fun f : Equiv.Perm X => f x) (by group : _ = _)
    · change (p*(q)) x = (p*q) x
      exact congrArg (fun f : Equiv.Perm X => f x) (by group : _ = _)
    · change (p*(q⁻¹)) x = (p*q⁻¹) x
      exact congrArg (fun f : Equiv.Perm X => f x) (by group : _ = _)
    · change (p*(q*p)) x = (p*q*p) x
      exact congrArg (fun f : Equiv.Perm X => f x) (by group : _ = _)
    · change (p*(q⁻¹*p)) x = (p*q⁻¹*p) x
      exact congrArg (fun f : Equiv.Perm X => f x) (by group : _ = _)
    · change (p*(p⁻¹*q⁻¹)) x = (q⁻¹) x
      exact congrArg (fun f : Equiv.Perm X => f x) (by group : _ = _)
    · change (p*(p⁻¹*q⁻¹*p)) x = (q⁻¹*p) x
      exact congrArg (fun f : Equiv.Perm X => f x) (by group : _ = _)
    · change (p*(q⁻¹*p*q)) x = (q⁻¹*p*q*p) x
      exact t0_12
    · change (p*(q*p*q⁻¹)) x = (q*p*q⁻¹*p) x
      exact t0_13
    · change (p*(q*p⁻¹*q⁻¹)) x = (q*p⁻¹*q⁻¹*p) x
      exact t0_14
  have hq (i : Fin 10) : let e := ([(0,2),(1,4),(3,0),(5,1),(7,13),(8,14),(10,16),(11,17),(12,6),(15,9)] : List (ℕ × ℕ)).get i; q (v e.1)=v e.2 := by
    fin_cases i
    · change (q*((1 : Equiv.Perm X))) x = (q) x
      exact congrArg (fun f : Equiv.Perm X => f x) (by group : _ = _)
    · change (q*(p)) x = (q*p) x
      exact congrArg (fun f : Equiv.Perm X => f x) (by group : _ = _)
    · change (q*(q⁻¹)) x = ((1 : Equiv.Perm X)) x
      exact congrArg (fun f : Equiv.Perm X => f x) (by group : _ = _)
    · change (q*(q⁻¹*p)) x = (p) x
      exact congrArg (fun f : Equiv.Perm X => f x) (by group : _ = _)
    · change (q*(p*q⁻¹)) x = (q*p*q⁻¹) x
      exact congrArg (fun f : Equiv.Perm X => f x) (by group : _ = _)
    · change (q*(p⁻¹*q⁻¹)) x = (q*p⁻¹*q⁻¹) x
      exact congrArg (fun f : Equiv.Perm X => f x) (by group : _ = _)
    · change (q*(p*q⁻¹*p)) x = (q*p*q⁻¹*p) x
      exact congrArg (fun f : Equiv.Perm X => f x) (by group : _ = _)
    · change (q*(p⁻¹*q⁻¹*p)) x = (q*p⁻¹*q⁻¹*p) x
      exact congrArg (fun f : Equiv.Perm X => f x) (by group : _ = _)
    · change (q*(q⁻¹*p*q)) x = (p*q) x
      exact congrArg (fun f : Equiv.Perm X => f x) (by group : _ = _)
    · change (q*(q⁻¹*p*q*p)) x = (p*q*p) x
      exact congrArg (fun f : Equiv.Perm X => f x) (by group : _ = _)
  by_contra no
  exact branch0 p q v hp hq sep G e₀ e₁ e₂ no


/-- On any nonempty action, commutation with the first conjugate suffices
for a simple cycle of length four, eight, or sixteen. -/
theorem conjugate_matching_cycle [Nonempty X] (p q : Equiv.Perm X)
    (comm : Commute p (q*p*q⁻¹))
    (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x)
    (G : SimpleGraph (Bool × X))
    (e₀ : ∀ x, G.Adj (false,x) (true,x))
    (e₁ : ∀ x, G.Adj (false,x) (true,p x))
    (e₂ : ∀ x, G.Adj (false,x) (true,q x)) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G := by

  classical
  exact local_matching_cycle p q (Classical.choice inferInstance) (fun i =>
    congrArg (fun g : Equiv.Perm X => g _) comm.eq) sep G e₀ e₁ e₂

theorem conjugate_defect_bound [Fintype X] (p q : Equiv.Perm X)
    (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x)
    (G : SimpleGraph (Bool × X))
    (e₀ : ∀ x, G.Adj (false,x) (true,x))
    (e₁ : ∀ x, G.Adj (false,x) (true,p x))
    (e₂ : ∀ x, G.Adj (false,x) (true,q x)) :
    ¬ (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) →
    Fintype.card X ≤ 3 * {y : X | (p*(q*p*q⁻¹)) y ≠ ((q*p*q⁻¹)*p) y}.ncard := by

  classical
  intro no
  let move : Fin 3 → Equiv.Perm X := ![q,(1 : Equiv.Perm X),q*p⁻¹*q⁻¹]
  let bad := {y : X | (p*(q*p*q⁻¹)) y ≠ ((q*p*q⁻¹)*p) y}
  let test (i : Fin 3) := (move i) ⁻¹' bad
  have cover : Set.univ ⊆ ⋃ i, test i := by
    intro x _
    by_contra hx
    apply no
    apply local_matching_cycle p q x _ sep G e₀ e₁ e₂
    intro i
    by_contra fail
    exact hx (Set.mem_iUnion.mpr ⟨i,fail⟩)
  have count (i : Fin 3) : (test i).ncard = bad.ncard := by
    have h := Set.encard_preimage_of_bijective (move i).bijective bad
    exact congrArg ENat.toNat h
  calc
    Fintype.card X = (Set.univ : Set X).ncard := by simp [Nat.card_eq_fintype_card]
    _ ≤ (⋃ i, test i).ncard := Set.ncard_le_ncard cover
    _ ≤ ∑ i, (test i).ncard := Set.ncard_iUnion_le_of_fintype test
    _ = 3 * bad.ncard := by simp [count]

/-- Any repeated pair of matching cosets can serve as the first pair. -/
theorem matching_cycle_after_relabel [Nonempty X] (p q : Equiv.Perm X)
    (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x)
    (ok : Commute p (q*p*q⁻¹) ∨ Commute q (p*q*p⁻¹) ∨
      Commute (p⁻¹*q) (p⁻¹*(p⁻¹*q)*(p⁻¹)⁻¹))
    (G : SimpleGraph (Bool × X))
    (e₀ : ∀ x, G.Adj (false,x) (true,x))
    (e₁ : ∀ x, G.Adj (false,x) (true,p x))
    (e₂ : ∀ x, G.Adj (false,x) (true,q x)) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G := by

  classical
  rcases ok with h|h|h
  · exact conjugate_matching_cycle p q h sep G e₀ e₁ e₂
  · exact conjugate_matching_cycle q p h (fun x => ⟨(sep x).2.1,(sep x).1,(sep x).2.2.symm⟩) G e₀ e₂ e₁
  let f : Bool × X → Bool × X := fun u => (u.1,if u.1 then p u.2 else u.2)
  have inj : Function.Injective f := by
    rintro ⟨i,x⟩ ⟨j,y⟩ h
    have ij : i=j := congrArg Prod.fst h
    subst j
    cases i <;> simpa [f] using h
  have lift : G.comap f ⊑ G := ⟨⟨⟨f,fun edge => edge⟩,inj⟩⟩
  have separated (x : X) : (p⁻¹*q) x ≠ x ∧ p⁻¹ x ≠ x ∧ (p⁻¹*q) x ≠ p⁻¹ x := by
    change p.symm (q x) ≠ x ∧ p.symm x ≠ x ∧ p.symm (q x) ≠ p.symm x
    exact ⟨fun h => (sep x).2.2 (p.symm_apply_eq.mp h).symm,
      fun h => (sep x).1 (p.symm_apply_eq.mp h).symm,fun h => (sep x).2.1 (p.symm.injective h)⟩
  have short := conjugate_matching_cycle (p⁻¹*q) p⁻¹ h
    separated (G.comap f) (fun x => e₁ x)
    (fun x => by change G.Adj (false,x) (true,p (p.symm (q x))); simpa using e₂ x)
    (fun x => by change G.Adj (false,x) (true,p (p.symm x)); simpa using e₀ x)
  exact short.imp (fun h => h.trans lift) (Or.imp (fun h => h.trans lift) (fun h => h.trans lift))


/-- In the absence of short cycles the conjugate-square defect has density
at least one third for each of the three choices of matching pair. -/
theorem relabel_defect_bounds [Fintype X] (p q : Equiv.Perm X)
    (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x)
    (G : SimpleGraph (Bool × X))
    (e₀ : ∀ x, G.Adj (false,x) (true,x))
    (e₁ : ∀ x, G.Adj (false,x) (true,p x))
    (e₂ : ∀ x, G.Adj (false,x) (true,q x)) 
    (no : ¬ (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G)) :
     ∀ (a b : Equiv.Perm X), (a=p ∧ b=q) ∨ (a=q ∧ b=p) ∨ (a=p⁻¹*q ∧ b=p⁻¹) →
       Fintype.card X ≤ 3 * {y : X | (a*(b*a*b⁻¹)) y ≠ ((b*a*b⁻¹)*a) y}.ncard := by
  classical
  intro a b choices
  rcases choices with ⟨ha,hb⟩|⟨ha,hb⟩|⟨ha,hb⟩ <;> subst a <;> subst b
  · exact conjugate_defect_bound p q sep G e₀ e₁ e₂ no
  · exact conjugate_defect_bound q p (fun x => ⟨(sep x).2.1,(sep x).1,(sep x).2.2.symm⟩) G e₀ e₂ e₁ no
  let f : Bool × X → Bool × X := fun u => (u.1,if u.1 then p u.2 else u.2)
  have inj : Function.Injective f := by
    rintro ⟨i,x⟩ ⟨j,y⟩ h
    have ij : i=j := congrArg Prod.fst h
    subst j
    cases i <;> simpa [f] using h
  have lift : G.comap f ⊑ G := ⟨⟨⟨f,fun edge => edge⟩,inj⟩⟩
  have separated (x : X) : (p⁻¹*q) x ≠ x ∧ p⁻¹ x ≠ x ∧ (p⁻¹*q) x ≠ p⁻¹ x := by
    change p.symm (q x) ≠ x ∧ p.symm x ≠ x ∧ p.symm (q x) ≠ p.symm x
    exact ⟨fun h => (sep x).2.2 (p.symm_apply_eq.mp h).symm,
      fun h => (sep x).1 (p.symm_apply_eq.mp h).symm,fun h => (sep x).2.1 (p.symm.injective h)⟩
  apply conjugate_defect_bound (p⁻¹*q) p⁻¹ separated (G.comap f) (fun x => e₁ x)
    (fun x => by change G.Adj (false,x) (true,p (p.symm (q x))); simpa using e₂ x)
    (fun x => by change G.Adj (false,x) (true,p (p.symm x)); simpa using e₀ x)
  exact fun h => no (h.imp (fun c => c.trans lift) (Or.imp (fun c => c.trans lift) (fun c => c.trans lift)))

/-- A separated matching graph has a cycle of length four, eight, or sixteen
whenever the relative permutations generate a group with an abelian normal
subgroup of index two. No transitivity or freeness assumption is required. -/
theorem index_two_matching_cycle [Nonempty X] (p q : Equiv.Perm X)
    (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x)
    (idx : ∃ N : Subgroup (Subgroup.closure ({p,q} : Set (Equiv.Perm X))),
      N.Normal ∧ IsMulCommutative N ∧ N.index=2)
    (G : SimpleGraph (Bool × X))
    (e₀ : ∀ x, G.Adj (false,x) (true,x))
    (e₁ : ∀ x, G.Adj (false,x) (true,p x))
    (e₂ : ∀ x, G.Adj (false,x) (true,q x)) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G := by
  classical
  let K := Subgroup.closure ({p,q} : Set (Equiv.Perm X))
  let a : K := ⟨p,Subgroup.subset_closure (by simp)⟩
  let b : K := ⟨q,Subgroup.subset_closure (by simp)⟩
  obtain ⟨N,normal,abelian,two⟩ := idx
  have commute {g h : K} (hg : g∈N) (hh : h∈N) : Commute (g : Equiv.Perm X) (h : Equiv.Perm X) :=
    congrArg (fun z : N => ((z:K):Equiv.Perm X))
      (abelian.is_comm.comm (⟨g,hg⟩ : N) (⟨h,hh⟩ : N))

  have rels {g : K} (hg : g ∈ N) (h : K) :
      Commute (g : Equiv.Perm X) ((h:Equiv.Perm X)*g*(h:Equiv.Perm X)⁻¹) :=
    commute hg (normal.conj_mem _ hg h)
  apply matching_cycle_after_relabel p q sep _ G e₀ e₁ e₂
  by_cases ha : a∈N
  · exact .inl (rels ha b)
  by_cases hb : b∈N
  · exact .inr (.inl (rels hb a))
  have hab : a⁻¹*b∈N :=
    (N.mul_mem_iff_of_index_two two).mpr (by simp [ha,hb])
  exact .inr (.inr (rels hab a⁻¹))

end Erdos64.MatchingConjugate

/-!
# The 32-step trace for three distinct matching cosets

In cyclic quotient coordinates the matchings p and q send (a,b,c,z) to
(c,a,b,z+1) and (b+1,c,a,z-1). The chart uses the radius-five ball.
The root 32-step trace either embeds, or two same-shore positions agree.
The branch lemmas transport these equalities along labeled chart edges.
Shorter traces and pointwise separation exclude every resulting case.
The argument allows arbitrary identifications on the chart.
Formalization by @bmander.
-/
namespace Erdos64.IndexThreeCore
open SimpleGraph
universe u
variable {X : Type u}

open Erdos64.MatchingConjugate (reverse_move move_eq collision4 collision8 collision16)

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 5000 in
private theorem collision32 {G : SimpleGraph (Bool × X)} (no : ¬ cycleGraph 32 ⊑ G)
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : X)
    (e0 : G.Adj (false,x0) (true,x1))
    (e1 : G.Adj (false,x2) (true,x1))
    (e2 : G.Adj (false,x2) (true,x3))
    (e3 : G.Adj (false,x4) (true,x3))
    (e4 : G.Adj (false,x4) (true,x5))
    (e5 : G.Adj (false,x6) (true,x5))
    (e6 : G.Adj (false,x6) (true,x7))
    (e7 : G.Adj (false,x8) (true,x7))
    (e8 : G.Adj (false,x8) (true,x9))
    (e9 : G.Adj (false,x10) (true,x9))
    (e10 : G.Adj (false,x10) (true,x11))
    (e11 : G.Adj (false,x12) (true,x11))
    (e12 : G.Adj (false,x12) (true,x13))
    (e13 : G.Adj (false,x14) (true,x13))
    (e14 : G.Adj (false,x14) (true,x15))
    (e15 : G.Adj (false,x16) (true,x15))
    (e16 : G.Adj (false,x16) (true,x17))
    (e17 : G.Adj (false,x18) (true,x17))
    (e18 : G.Adj (false,x18) (true,x19))
    (e19 : G.Adj (false,x20) (true,x19))
    (e20 : G.Adj (false,x20) (true,x21))
    (e21 : G.Adj (false,x22) (true,x21))
    (e22 : G.Adj (false,x22) (true,x23))
    (e23 : G.Adj (false,x24) (true,x23))
    (e24 : G.Adj (false,x24) (true,x25))
    (e25 : G.Adj (false,x26) (true,x25))
    (e26 : G.Adj (false,x26) (true,x27))
    (e27 : G.Adj (false,x28) (true,x27))
    (e28 : G.Adj (false,x28) (true,x29))
    (e29 : G.Adj (false,x30) (true,x29))
    (e30 : G.Adj (false,x30) (true,x31))
    (e31 : G.Adj (false,x0) (true,x31))
    : x0=x2 ∨ x0=x4 ∨ x0=x6 ∨ x0=x8 ∨ x0=x10 ∨ x0=x12 ∨ x0=x14 ∨ x0=x16 ∨ x0=x18 ∨ x0=x20 ∨ x0=x22 ∨ x0=x24 ∨ x0=x26 ∨ x0=x28 ∨ x0=x30 ∨ x1=x3 ∨ x1=x5 ∨ x1=x7 ∨ x1=x9 ∨ x1=x11 ∨ x1=x13 ∨ x1=x15 ∨ x1=x17 ∨ x1=x19 ∨ x1=x21 ∨ x1=x23 ∨ x1=x25 ∨ x1=x27 ∨ x1=x29 ∨ x1=x31 ∨ x2=x4 ∨ x2=x6 ∨ x2=x8 ∨ x2=x10 ∨ x2=x12 ∨ x2=x14 ∨ x2=x16 ∨ x2=x18 ∨ x2=x20 ∨ x2=x22 ∨ x2=x24 ∨ x2=x26 ∨ x2=x28 ∨ x2=x30 ∨ x3=x5 ∨ x3=x7 ∨ x3=x9 ∨ x3=x11 ∨ x3=x13 ∨ x3=x15 ∨ x3=x17 ∨ x3=x19 ∨ x3=x21 ∨ x3=x23 ∨ x3=x25 ∨ x3=x27 ∨ x3=x29 ∨ x3=x31 ∨ x4=x6 ∨ x4=x8 ∨ x4=x10 ∨ x4=x12 ∨ x4=x14 ∨ x4=x16 ∨ x4=x18 ∨ x4=x20 ∨ x4=x22 ∨ x4=x24 ∨ x4=x26 ∨ x4=x28 ∨ x4=x30 ∨ x5=x7 ∨ x5=x9 ∨ x5=x11 ∨ x5=x13 ∨ x5=x15 ∨ x5=x17 ∨ x5=x19 ∨ x5=x21 ∨ x5=x23 ∨ x5=x25 ∨ x5=x27 ∨ x5=x29 ∨ x5=x31 ∨ x6=x8 ∨ x6=x10 ∨ x6=x12 ∨ x6=x14 ∨ x6=x16 ∨ x6=x18 ∨ x6=x20 ∨ x6=x22 ∨ x6=x24 ∨ x6=x26 ∨ x6=x28 ∨ x6=x30 ∨ x7=x9 ∨ x7=x11 ∨ x7=x13 ∨ x7=x15 ∨ x7=x17 ∨ x7=x19 ∨ x7=x21 ∨ x7=x23 ∨ x7=x25 ∨ x7=x27 ∨ x7=x29 ∨ x7=x31 ∨ x8=x10 ∨ x8=x12 ∨ x8=x14 ∨ x8=x16 ∨ x8=x18 ∨ x8=x20 ∨ x8=x22 ∨ x8=x24 ∨ x8=x26 ∨ x8=x28 ∨ x8=x30 ∨ x9=x11 ∨ x9=x13 ∨ x9=x15 ∨ x9=x17 ∨ x9=x19 ∨ x9=x21 ∨ x9=x23 ∨ x9=x25 ∨ x9=x27 ∨ x9=x29 ∨ x9=x31 ∨ x10=x12 ∨ x10=x14 ∨ x10=x16 ∨ x10=x18 ∨ x10=x20 ∨ x10=x22 ∨ x10=x24 ∨ x10=x26 ∨ x10=x28 ∨ x10=x30 ∨ x11=x13 ∨ x11=x15 ∨ x11=x17 ∨ x11=x19 ∨ x11=x21 ∨ x11=x23 ∨ x11=x25 ∨ x11=x27 ∨ x11=x29 ∨ x11=x31 ∨ x12=x14 ∨ x12=x16 ∨ x12=x18 ∨ x12=x20 ∨ x12=x22 ∨ x12=x24 ∨ x12=x26 ∨ x12=x28 ∨ x12=x30 ∨ x13=x15 ∨ x13=x17 ∨ x13=x19 ∨ x13=x21 ∨ x13=x23 ∨ x13=x25 ∨ x13=x27 ∨ x13=x29 ∨ x13=x31 ∨ x14=x16 ∨ x14=x18 ∨ x14=x20 ∨ x14=x22 ∨ x14=x24 ∨ x14=x26 ∨ x14=x28 ∨ x14=x30 ∨ x15=x17 ∨ x15=x19 ∨ x15=x21 ∨ x15=x23 ∨ x15=x25 ∨ x15=x27 ∨ x15=x29 ∨ x15=x31 ∨ x16=x18 ∨ x16=x20 ∨ x16=x22 ∨ x16=x24 ∨ x16=x26 ∨ x16=x28 ∨ x16=x30 ∨ x17=x19 ∨ x17=x21 ∨ x17=x23 ∨ x17=x25 ∨ x17=x27 ∨ x17=x29 ∨ x17=x31 ∨ x18=x20 ∨ x18=x22 ∨ x18=x24 ∨ x18=x26 ∨ x18=x28 ∨ x18=x30 ∨ x19=x21 ∨ x19=x23 ∨ x19=x25 ∨ x19=x27 ∨ x19=x29 ∨ x19=x31 ∨ x20=x22 ∨ x20=x24 ∨ x20=x26 ∨ x20=x28 ∨ x20=x30 ∨ x21=x23 ∨ x21=x25 ∨ x21=x27 ∨ x21=x29 ∨ x21=x31 ∨ x22=x24 ∨ x22=x26 ∨ x22=x28 ∨ x22=x30 ∨ x23=x25 ∨ x23=x27 ∨ x23=x29 ∨ x23=x31 ∨ x24=x26 ∨ x24=x28 ∨ x24=x30 ∨ x25=x27 ∨ x25=x29 ∨ x25=x31 ∨ x26=x28 ∨ x26=x30 ∨ x27=x29 ∨ x27=x31 ∨ x28=x30 ∨ x29=x31 := by
  classical
  by_contra! h
  apply no
  let l : List (Bool × X) := [(false,x0),(true,x1),(false,x2),(true,x3),(false,x4),(true,x5),(false,x6),(true,x7),(false,x8),(true,x9),(false,x10),(true,x11),(false,x12),(true,x13),(false,x14),(true,x15),(false,x16),(true,x17),(false,x18),(true,x19),(false,x20),(true,x21),(false,x22),(true,x23),(false,x24),(true,x25),(false,x26),(true,x27),(false,x28),(true,x29),(false,x30),(true,x31)]
  let f : Fin 32 → Bool × X := l.get
  have nd : l.Nodup := by
    obtain ⟨d0_2,d0_4,d0_6,d0_8,d0_10,d0_12,d0_14,d0_16,d0_18,d0_20,d0_22,d0_24,d0_26,d0_28,d0_30,d1_3,d1_5,d1_7,d1_9,d1_11,d1_13,d1_15,d1_17,d1_19,d1_21,d1_23,d1_25,d1_27,d1_29,d1_31,d2_4,d2_6,d2_8,d2_10,d2_12,d2_14,d2_16,d2_18,d2_20,d2_22,d2_24,d2_26,d2_28,d2_30,d3_5,d3_7,d3_9,d3_11,d3_13,d3_15,d3_17,d3_19,d3_21,d3_23,d3_25,d3_27,d3_29,d3_31,d4_6,d4_8,d4_10,d4_12,d4_14,d4_16,d4_18,d4_20,d4_22,d4_24,d4_26,d4_28,d4_30,d5_7,d5_9,d5_11,d5_13,d5_15,d5_17,d5_19,d5_21,d5_23,d5_25,d5_27,d5_29,d5_31,d6_8,d6_10,d6_12,d6_14,d6_16,d6_18,d6_20,d6_22,d6_24,d6_26,d6_28,d6_30,d7_9,d7_11,d7_13,d7_15,d7_17,d7_19,d7_21,d7_23,d7_25,d7_27,d7_29,d7_31,d8_10,d8_12,d8_14,d8_16,d8_18,d8_20,d8_22,d8_24,d8_26,d8_28,d8_30,d9_11,d9_13,d9_15,d9_17,d9_19,d9_21,d9_23,d9_25,d9_27,d9_29,d9_31,d10_12,d10_14,d10_16,d10_18,d10_20,d10_22,d10_24,d10_26,d10_28,d10_30,d11_13,d11_15,d11_17,d11_19,d11_21,d11_23,d11_25,d11_27,d11_29,d11_31,d12_14,d12_16,d12_18,d12_20,d12_22,d12_24,d12_26,d12_28,d12_30,d13_15,d13_17,d13_19,d13_21,d13_23,d13_25,d13_27,d13_29,d13_31,d14_16,d14_18,d14_20,d14_22,d14_24,d14_26,d14_28,d14_30,d15_17,d15_19,d15_21,d15_23,d15_25,d15_27,d15_29,d15_31,d16_18,d16_20,d16_22,d16_24,d16_26,d16_28,d16_30,d17_19,d17_21,d17_23,d17_25,d17_27,d17_29,d17_31,d18_20,d18_22,d18_24,d18_26,d18_28,d18_30,d19_21,d19_23,d19_25,d19_27,d19_29,d19_31,d20_22,d20_24,d20_26,d20_28,d20_30,d21_23,d21_25,d21_27,d21_29,d21_31,d22_24,d22_26,d22_28,d22_30,d23_25,d23_27,d23_29,d23_31,d24_26,d24_28,d24_30,d25_27,d25_29,d25_31,d26_28,d26_30,d27_29,d27_31,d28_30,d29_31⟩ := h
    simp [l, *]
  have step (i : Fin 32) : G.Adj (f i) (f (i+1)) := by
    fin_cases i
    · exact e0
    · exact e1.symm
    · exact e2
    · exact e3.symm
    · exact e4
    · exact e5.symm
    · exact e6
    · exact e7.symm
    · exact e8
    · exact e9.symm
    · exact e10
    · exact e11.symm
    · exact e12
    · exact e13.symm
    · exact e14
    · exact e15.symm
    · exact e16
    · exact e17.symm
    · exact e18
    · exact e19.symm
    · exact e20
    · exact e21.symm
    · exact e22
    · exact e23.symm
    · exact e24
    · exact e25.symm
    · exact e26
    · exact e27.symm
    · exact e28
    · exact e29.symm
    · exact e30
    · exact e31.symm
  refine ⟨⟨⟨f,?_⟩,List.nodup_iff_injective_get.mp nd⟩⟩
  intro i j adj
  rcases cycleGraph_adj.mp adj with h|h
  · exact (sub_eq_iff_eq_add'.mp h) ▸ (step j).symm
  · exact (sub_eq_iff_eq_add'.mp h) ▸ step i

private theorem short4 (p q : Equiv.Perm X) (G : SimpleGraph (Bool × X))
    (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x)
    (e₀ : ∀ x, G.Adj (false,x) (true,x)) (e₁ : ∀ x, G.Adj (false,x) (true,p x))
    (e₂ : ∀ x, G.Adj (false,x) (true,q x))
    (no : ¬ (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G))
    (c : Fin 4 → Fin 3) (different : ∀ i, c i ≠ c (i+1))
    (x0 x1 x2 x3 : X)
    (w0 : ((![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X) (c 0)) x0 = x1)
    (w1 : ((![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X) (c 1)) x2 = x1)
    (w2 : ((![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X) (c 2)) x2 = x3)
    (w3 : ((![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X) (c 3)) x0 = x3)
    : False := by
  let F := (![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X)
  have apart (i j : Fin 3) (ij : i ≠ j) (x : X) : F i x ≠ F j x := by
    fin_cases i <;> fin_cases j <;> first | exact (ij rfl).elim | exact (sep x).1 | exact (sep x).1.symm | exact (sep x).2.1 | exact (sep x).2.1.symm | exact (sep x).2.2 | exact (sep x).2.2.symm
  have edge (i : Fin 3) (x : X) : G.Adj (false,x) (true,F i x) := by
    fin_cases i <;> first | exact e₀ x | exact e₁ x | exact e₂ x
  have a0 : G.Adj (false,x0) (true,x1) := (w0) ▸ edge (c 0) x0
  have a1 : G.Adj (false,x2) (true,x1) := (w1) ▸ edge (c 1) x2
  have a2 : G.Adj (false,x2) (true,x3) := (w2) ▸ edge (c 2) x2
  have a3 : G.Adj (false,x0) (true,x3) := (w3) ▸ edge (c 3) x0
  have d0 : x0 ≠ x2 := by
    intro hit
    exact apart _ _ (different 0) x0 ((w0).trans (w1.symm.trans (congrArg (F (c 1)) hit.symm)))
  have d1 : x1 ≠ x3 := by
    intro hit
    exact apart _ _ (different 1) x2 ((w1).trans (hit.trans w2.symm))
  have d2 : x2 ≠ x0 := by
    intro hit
    exact apart _ _ (different 2) x2 ((w2).trans (w3.symm.trans (congrArg (F (c 3)) hit.symm)))
  have d3 : x3 ≠ x1 := by
    intro hit
    exact apart _ _ (different 3) x0 ((w3).trans (hit.trans w0.symm))
  rcases collision4 (fun h => no (.inl h)) x0 x1 x2 x3 a0 a1 a2 a3 with h|h
  · exact d0 h
  · exact d1 h

private theorem short8 (p q : Equiv.Perm X) (G : SimpleGraph (Bool × X))
    (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x)
    (e₀ : ∀ x, G.Adj (false,x) (true,x)) (e₁ : ∀ x, G.Adj (false,x) (true,p x))
    (e₂ : ∀ x, G.Adj (false,x) (true,q x))
    (no : ¬ (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G))
    (c : Fin 8 → Fin 3) (different : ∀ i, c i ≠ c (i+1))
    (x0 x1 x2 x3 x4 x5 x6 x7 : X)
    (w0 : ((![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X) (c 0)) x0 = x1)
    (w1 : ((![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X) (c 1)) x2 = x1)
    (w2 : ((![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X) (c 2)) x2 = x3)
    (w3 : ((![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X) (c 3)) x4 = x3)
    (w4 : ((![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X) (c 4)) x4 = x5)
    (w5 : ((![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X) (c 5)) x6 = x5)
    (w6 : ((![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X) (c 6)) x6 = x7)
    (w7 : ((![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X) (c 7)) x0 = x7)
    : False := by
  let F := (![(1 : Equiv.Perm X),p,q] : Fin 3 → Equiv.Perm X)
  have apart (i j : Fin 3) (ij : i ≠ j) (x : X) : F i x ≠ F j x := by
    fin_cases i <;> fin_cases j <;> first | exact (ij rfl).elim | exact (sep x).1 | exact (sep x).1.symm | exact (sep x).2.1 | exact (sep x).2.1.symm | exact (sep x).2.2 | exact (sep x).2.2.symm
  have edge (i : Fin 3) (x : X) : G.Adj (false,x) (true,F i x) := by
    fin_cases i <;> first | exact e₀ x | exact e₁ x | exact e₂ x
  have a0 : G.Adj (false,x0) (true,x1) := (w0) ▸ edge (c 0) x0
  have a1 : G.Adj (false,x2) (true,x1) := (w1) ▸ edge (c 1) x2
  have a2 : G.Adj (false,x2) (true,x3) := (w2) ▸ edge (c 2) x2
  have a3 : G.Adj (false,x4) (true,x3) := (w3) ▸ edge (c 3) x4
  have a4 : G.Adj (false,x4) (true,x5) := (w4) ▸ edge (c 4) x4
  have a5 : G.Adj (false,x6) (true,x5) := (w5) ▸ edge (c 5) x6
  have a6 : G.Adj (false,x6) (true,x7) := (w6) ▸ edge (c 6) x6
  have a7 : G.Adj (false,x0) (true,x7) := (w7) ▸ edge (c 7) x0
  have d0 : x0 ≠ x2 := by
    intro hit
    exact apart _ _ (different 0) x0 ((w0).trans (w1.symm.trans (congrArg (F (c 1)) hit.symm)))
  have d1 : x1 ≠ x3 := by
    intro hit
    exact apart _ _ (different 1) x2 ((w1).trans (hit.trans w2.symm))
  have d2 : x2 ≠ x4 := by
    intro hit
    exact apart _ _ (different 2) x2 ((w2).trans (w3.symm.trans (congrArg (F (c 3)) hit.symm)))
  have d3 : x3 ≠ x5 := by
    intro hit
    exact apart _ _ (different 3) x4 ((w3).trans (hit.trans w4.symm))
  have d4 : x4 ≠ x6 := by
    intro hit
    exact apart _ _ (different 4) x4 ((w4).trans (w5.symm.trans (congrArg (F (c 5)) hit.symm)))
  have d5 : x5 ≠ x7 := by
    intro hit
    exact apart _ _ (different 5) x6 ((w5).trans (hit.trans w6.symm))
  have d6 : x6 ≠ x0 := by
    intro hit
    exact apart _ _ (different 6) x6 ((w6).trans (w7.symm.trans (congrArg (F (c 7)) hit.symm)))
  have d7 : x7 ≠ x1 := by
    intro hit
    exact apart _ _ (different 7) x0 ((w7).trans (hit.trans w0.symm))
  have o0 : x0 ≠ x4 := by
    intro hit
    rcases collision4 (fun h => no (.inl h)) x0 x1 x2 x3 a0 a1 a2 (hit.symm ▸ a3) with h|h
    · exact d0 h
    · exact d1 h
  have o1 : x1 ≠ x5 := by
    intro hit
    rcases collision4 (fun h => no (.inl h)) x2 x3 x4 x1 a2 a3 (hit.symm ▸ a4) a1 with h|h
    · exact d2 h
    · exact d1 h.symm
  have o2 : x2 ≠ x6 := by
    intro hit
    rcases collision4 (fun h => no (.inl h)) x2 x3 x4 x5 a2 a3 a4 (hit.symm ▸ a5) with h|h
    · exact d2 h
    · exact d3 h
  have o3 : x3 ≠ x7 := by
    intro hit
    rcases collision4 (fun h => no (.inl h)) x4 x5 x6 x3 a4 a5 (hit.symm ▸ a6) a3 with h|h
    · exact d4 h
    · exact d3 h.symm
  rcases collision8 (fun h => no (.inr (.inl h))) x0 x1 x2 x3 x4 x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 with h|h|h|h|h|h|h|h|h|h|h|h
  · exact d0 h
  · exact o0 h
  · exact d6 h.symm
  · exact d1 h
  · exact o1 h
  · exact d7 h.symm
  · exact d2 h
  · exact o2 h
  · exact d3 h
  · exact o3 h
  · exact d4 h
  · exact d5 h

variable (p q : Equiv.Perm X) (v : ℕ → X)
variable (hp : ∀ i : Fin 174, let e := ([(0,1),(1,5),(2,8),(3,0),(4,14),(5,17),(6,20),(7,23),(8,26),(9,29),(10,2),(11,35),(12,3),(13,41),(14,44),(15,4),(16,50),(17,53),(18,56),(19,59),(20,62),(21,65),(22,6),(23,71),(24,7),(25,77),(26,54),(27,80),(28,83),(29,86),(30,66),(31,9),(32,67),(33,10),(34,98),(35,58),(36,68),(37,11),(38,69),(39,12),(40,75),(41,60),(42,13),(43,113),(44,55),(45,117),(46,61),(47,84),(48,15),(49,120),(50,73),(51,16),(52,79),(53,127),(54,130),(55,132),(56,134),(57,137),(58,18),(59,140),(60,19),(61,145),(62,128),(63,147),(64,150),(65,153),(66,138),(67,21),(68,139),(69,22),(70,161),(71,129),(72,164),(73,133),(74,151),(75,24),(76,167),(77,142),(78,25),(79,146),(80,174),(81,177),(82,27),(83,183),(84,28),(85,187),(86,131),(87,189),(88,178),(89,30),(90,179),(91,31),(92,200),(93,180),(94,32),(95,181),(96,33),(97,47),(98,165),(99,34),(100,211),(101,143),(102,36),(103,37),(104,222),(105,38),(106,39),(107,48),(108,40),(109,171),(110,214),(111,42),(112,235),(113,46),(114,43),(115,52),(116,242),(117,245),(118,45),(119,249),(120,243),(121,49),(122,255),(123,244),(124,51),(125,259),(126,251),(139,57),(149,63),(151,64),(160,74),(162,70),(165,72),(168,76),(171,78),(179,81),(181,82),(188,85),(191,87),(193,88),(195,89),(197,90),(199,91),(201,92),(202,93),(203,94),(204,95),(205,96),(206,97),(209,99),(213,100),(214,101),(217,102),(220,103),(221,110),(222,118),(223,104),(224,105),(226,106),(227,111),(228,107),(229,124),(231,108),(233,109),(234,115),(236,112),(239,114),(243,116),(250,119),(253,121),(255,123),(256,122),(257,126),(260,125)] : List (ℕ × ℕ)).get i; p (v e.1)=v e.2)
variable (hq : ∀ i : Fin 174, let e := ([(0,2),(1,6),(2,9),(3,11),(4,0),(5,18),(6,21),(7,1),(8,27),(9,30),(10,32),(11,36),(12,38),(13,3),(14,45),(15,47),(16,4),(17,54),(18,57),(19,5),(20,63),(21,66),(22,68),(23,72),(24,74),(25,7),(26,65),(27,81),(28,8),(29,87),(30,88),(31,90),(32,93),(33,95),(34,10),(35,100),(36,89),(37,91),(38,94),(39,96),(40,12),(41,70),(42,110),(43,13),(44,83),(45,58),(46,14),(47,92),(48,104),(49,15),(50,85),(51,75),(52,16),(53,128),(54,131),(55,17),(56,135),(57,138),(58,29),(59,141),(60,143),(61,19),(62,137),(63,148),(64,20),(65,154),(66,155),(67,156),(68,158),(69,159),(70,22),(71,150),(72,26),(73,23),(74,157),(75,34),(76,24),(77,152),(78,41),(79,25),(80,175),(81,178),(82,180),(83,184),(84,185),(85,28),(86,177),(87,190),(88,192),(89,194),(90,196),(91,198),(92,31),(93,193),(94,195),(95,197),(96,199),(97,33),(98,182),(99,208),(100,212),(101,35),(102,216),(103,219),(104,37),(105,217),(106,220),(107,39),(108,230),(109,40),(110,218),(111,225),(112,42),(113,215),(114,48),(115,43),(116,44),(117,246),(118,200),(119,46),(120,248),(121,252),(122,49),(123,50),(124,207),(125,51),(126,52),(129,53),(133,55),(136,56),(141,62),(142,59),(144,60),(146,61),(152,64),(157,67),(160,69),(163,71),(166,73),(169,76),(170,77),(172,78),(173,79),(176,80),(182,82),(184,86),(186,84),(188,98),(207,97),(210,99),(215,101),(218,102),(221,103),(225,105),(227,106),(229,107),(232,108),(233,111),(234,109),(237,112),(238,113),(240,114),(241,115),(244,116),(247,117),(248,118),(250,120),(251,119),(254,121),(256,124),(257,122),(258,123),(261,125),(262,126)] : List (ℕ × ℕ)).get i; q (v e.1)=v e.2)

variable (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x)
variable (G : SimpleGraph (Bool × X))
variable (e₀ : ∀ x, G.Adj (false,x) (true,x))
variable (e₁ : ∀ x, G.Adj (false,x) (true,p x))
variable (e₂ : ∀ x, G.Adj (false,x) (true,q x))
variable (no : ¬ (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G))
set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp sep in
private theorem branch1 (h0 : v 0 = v 3) : False := by
  have t0 := move_eq p (hp 3) (hp 0) (Eq.symm h0)
  exact (sep (v 0)).1 (Eq.trans (hp 0) (Eq.symm t0))

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp sep G e₀ e₁ e₂ no in
private theorem branch2 (h0 : v 0 = v 12) : False := by
  have t0 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 3)) (Eq.symm h0)
  have t1 := move_eq p (hp 12) (hp 0) (Eq.symm h0)
  have t2 := move_eq p (hp 39) (hp 1) (Eq.trans t0 t1)
  exact short4 p q G sep e₀ e₁ e₂ no ![0,1,0,1] (by decide)
    (v 0) (v 0) (v 1) (v 1)
    (rfl) (Eq.trans (hp 1) (Eq.trans (Eq.symm t2) (Eq.symm h0))) (rfl) (hp 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep in
private theorem branch4 (h1 : v 0 = v 7) : False := by
  have t0 := move_eq q (hq 7) (hq 0) (Eq.symm h1)
  exact (sep (v 0)).2.2 (Eq.trans (hp 0) (Eq.symm (Eq.trans (hq 0) (Eq.symm t0))))

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep in
private theorem branch5 (h1 : v 0 = v 24) : False := by
  have t0 := move_eq p (hp 24) (hp 0) (Eq.symm h1)
  have t1 := move_eq q (hq 7) (hq 1) t0
  exact (sep (v 1)).2.1 (Eq.trans (hq 1) (Eq.symm t1))

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch6 (h1 : v 0 = v 23) : False := by
  have t0 := move_eq p (hp 23) (hp 0) (Eq.symm h1)
  have t1 := move_eq q.symm (reverse_move q (hq 137)) (reverse_move q (hq 7)) t0
  have t2 := move_eq p.symm (reverse_move p (hp 7)) (reverse_move p (hp 3)) (Eq.symm h1)
  have t3 := move_eq q (hq 137) (hq 3) (Eq.trans t1 t2)
  exact short4 p q G sep e₀ e₁ e₂ no ![0,1,2,1] (by decide)
    (v 0) (v 0) (v 3) (v 1)
    (rfl) (hp 3) (Eq.trans (hq 3) (Eq.trans (Eq.symm t3) t0)) (hp 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep in
private theorem branch7 (h0 : v 0 = v 39) (h1 : v 0 = v 34) : False := by
  have t0 := move_eq q (hq 39) (hq 0) (Eq.symm h0)
  have t1 := move_eq p.symm (reverse_move p (hp 147)) (reverse_move p (hp 10)) t0
  have t2 := move_eq q (hq 34) (hq 0) (Eq.symm h1)
  have t3 := move_eq p (hp 147) (hp 2) (Eq.trans t1 t2)
  exact (sep (v 2)).1 (Eq.trans (hp 2) (Eq.trans (Eq.symm t3) t0))

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hq sep in
private theorem branch8 (h1 : v 0 = v 2) : False := by
  exact (sep (v 0)).2.1 (Eq.trans (hq 0) (Eq.symm h1))

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch9 (h0 : v 0 = v 39) (h1 : v 3 = v 34) : False := by
  have t0 := move_eq p (hp 39) (hp 0) (Eq.symm h0)
  have t1 := move_eq q.symm (reverse_move q (hq 40)) (reverse_move q (hq 7)) t0
  have t2 := move_eq p (hp 40) (hp 7) t1
  have t3 := move_eq q.symm (reverse_move q (hq 75)) (reverse_move q (hq 13)) (Eq.symm h1)
  exact short8 p q G sep e₀ e₁ e₂ no ![0,1,0,2,0,1,2,1] (by decide)
    (v 0) (v 0) (v 3) (v 3) (v 13) (v 13) (v 7) (v 1)
    (rfl) (hp 3) (rfl) (hq 13) (rfl) (Eq.trans (hp 7) (Eq.trans (Eq.symm t2) t3)) (hq 7) (hp 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch10 (h1 : v 3 = v 2) : False := by
  have t0 := move_eq p (hp 3) (hp 2) h1
  exact short4 p q G sep e₀ e₁ e₂ no ![0,1,0,2] (by decide)
    (v 0) (v 0) (v 2) (v 2)
    (rfl) (Eq.trans (hp 2) (Eq.symm t0)) (rfl) (hq 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep in
private theorem branch11 (h0 : v 0 = v 39) (h1 : v 1 = v 34) : False := by
  have t0 := move_eq q.symm (reverse_move q (hq 75)) (reverse_move q (hq 7)) (Eq.symm h1)
  have t1 := move_eq p (hp 75) (hp 7) t0
  have t2 := move_eq p.symm (reverse_move p (hp 40)) (reverse_move p (hp 24)) t0
  have t3 := move_eq p (hp 39) (hp 0) (Eq.symm h0)
  have t4 := move_eq q.symm (reverse_move q (hq 40)) (reverse_move q (hq 7)) t3
  exact (sep (v 7)).1 (Eq.trans (hp 7) (Eq.trans (Eq.trans (Eq.symm t1) (Eq.symm t2)) t4))

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch12 (h1 : v 7 = v 10) : False := by
  have t0 := move_eq p (hp 10) (hp 7) (Eq.symm h1)
  exact short4 p q G sep e₀ e₁ e₂ no ![1,2,1,2] (by decide)
    (v 0) (v 1) (v 7) (v 2)
    (hp 0) (hq 7) (Eq.trans (hp 7) (Eq.symm t0)) (hq 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch13 (h1 : v 7 = v 2) : False := by
  have t0 := move_eq q (hq 7) (hq 2) h1
  exact short4 p q G sep e₀ e₁ e₂ no ![1,2,0,2] (by decide)
    (v 0) (v 1) (v 2) (v 2)
    (hp 0) (Eq.trans (hq 2) (Eq.symm t0)) (rfl) (hq 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep in
private theorem branch14 (h0 : v 0 = v 39) (h1 : v 24 = v 34) : False := by
  have t0 := move_eq p (hp 34) (hp 24) (Eq.symm h1)
  have t1 := move_eq p (hp 98) (hp 7) t0
  have t2 := move_eq p (hp 132) (hp 23) t1
  have t3 := move_eq q (hq 34) (hq 24) (Eq.symm h1)
  have t4 := move_eq p.symm (reverse_move p (hp 130)) (reverse_move p (hp 33)) (Eq.symm t3)
  have t5 := move_eq q (hq 39) (hq 0) (Eq.symm h0)
  have t6 := move_eq p (hp 96) (hp 2) t5
  have t7 := move_eq p (hp 130) (hp 8) (Eq.trans t4 t6)
  have t8 := move_eq q.symm (reverse_move q (hq 72)) (reverse_move q (hq 34)) (Eq.trans (Eq.symm t7) (Eq.symm t3))
  exact (sep (v 23)).2.2 (Eq.trans (Eq.trans (hp 23) (Eq.trans (Eq.trans (Eq.symm t2) t8) (Eq.symm h1))) (Eq.symm (Eq.trans (hq 23) (Eq.trans t8 (Eq.symm h1)))))

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch15 (h1 : v 24 = v 2) : False := by
  have t0 := move_eq p.symm (reverse_move p (hp 75)) (reverse_move p (hp 10)) h1
  have t1 := move_eq q (hq 75) (hq 10) t0
  have t2 := move_eq q (hq 34) (hq 32) t1
  exact short4 p q G sep e₀ e₁ e₂ no ![0,2,0,2] (by decide)
    (v 10) (v 10) (v 32) (v 32)
    (rfl) (Eq.trans (hq 32) (Eq.symm t2)) (rfl) (hq 10)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch3 (h0 : v 0 = v 39) : False := by
  have t0 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 3)) (Eq.symm h0)
  have t1 := move_eq p.symm (reverse_move p (hp 158)) (reverse_move p (hp 12)) t0
  have t2 := move_eq p (hp 39) (hp 0) (Eq.symm h0)
  have t3 := move_eq p (hp 158) (hp 1) (Eq.trans t1 t2)
  have t4 := move_eq q.symm (reverse_move q (hq 40)) (reverse_move q (hq 7)) t2
  have t5 := move_eq p (hp 40) (hp 7) t4
  have t6 := move_eq p (hp 75) (hp 23) t5
  have t7 := move_eq q (hq 75) (hq 23) t5
  rcases collision16 (fun h => no (.inr (.inr (.inl h))))
    (v 0) (v 0) (v 3) (v 3) (v 1) (v 1) (v 7) (v 7) (v 24) (v 24) (v 23) (v 34) (v 34) (v 10) (v 10) (v 2)
    (e₀ (v 0))
    ((hp 3) ▸ e₁ (v 3))
    (e₀ (v 3))
    ((Eq.trans (hp 1) (Eq.trans (Eq.symm t3) t0)) ▸ e₁ (v 1))
    (e₀ (v 1))
    ((hq 7) ▸ e₂ (v 7))
    (e₀ (v 7))
    ((hp 24) ▸ e₁ (v 24))
    (e₀ (v 24))
    ((Eq.trans (hp 23) (Eq.symm t6)) ▸ e₁ (v 23))
    ((Eq.trans (hq 23) (Eq.symm t7)) ▸ e₂ (v 23))
    (e₀ (v 34))
    ((hq 34) ▸ e₂ (v 34))
    (e₀ (v 10))
    ((hp 10) ▸ e₁ (v 10))
    ((hq 0) ▸ e₂ (v 0)) with hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit
  · exact branch1 p q v hp sep hit
  · have t0 := move_eq p.symm (reverse_move p (hp 0)) (reverse_move p (hp 3)) (Eq.symm hit)
    exact branch1 p q v hp sep t0
  · exact branch4 p q v hp hq sep hit
  · exact branch5 p q v hp hq sep hit
  · exact branch6 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch7 p q v hp hq sep h0 hit
  · have t0 := move_eq q (hq 10) (hq 0) (Eq.symm hit)
    have t1 := move_eq p (hp 10) (hp 0) (Eq.symm hit)
    have t2 := move_eq q.symm (reverse_move q (hq 10)) (reverse_move q (hq 7)) (Eq.trans t0 t1)
    exact branch4 p q v hp hq sep (Eq.trans hit t2)
  · exact branch1 p q v hp sep hit
  · have t0 := move_eq p.symm (reverse_move p (hp 0)) (reverse_move p (hp 3)) (Eq.symm hit)
    exact branch1 p q v hp sep t0
  · exact branch4 p q v hp hq sep hit
  · exact branch5 p q v hp hq sep hit
  · exact branch7 p q v hp hq sep h0 hit
  · have t0 := move_eq q (hq 10) (hq 0) (Eq.symm hit)
    have t1 := move_eq p (hp 10) (hp 0) (Eq.symm hit)
    have t2 := move_eq q.symm (reverse_move q (hq 10)) (reverse_move q (hq 7)) (Eq.trans t0 t1)
    exact branch4 p q v hp hq sep (Eq.trans hit t2)
  · exact branch8 p q v hq sep hit
  · have t0 := move_eq p.symm (reverse_move p (hp 12)) (reverse_move p (hp 0)) hit
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 7) (hp 3) (Eq.symm hit)
    exact branch6 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 24) (hp 3) (Eq.symm hit)
    exact branch4 p q v hp hq sep (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 7)) (reverse_move p (hp 12)) (Eq.symm hit)
    have t1 := move_eq p (hp 39) (hp 0) (Eq.symm h0)
    have t2 := move_eq p.symm (reverse_move p (hp 24)) (reverse_move p (hp 0)) (Eq.trans t0 t1)
    exact branch5 p q v hp hq sep (Eq.symm t2)
  · exact branch9 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · have t0 := move_eq p (hp 10) (hp 3) (Eq.symm hit)
    exact branch8 p q v hq sep (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 12)) (reverse_move p (hp 0)) hit
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 7) (hp 3) (Eq.symm hit)
    exact branch6 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 24) (hp 3) (Eq.symm hit)
    exact branch4 p q v hp hq sep (Eq.symm t0)
  · exact branch9 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · have t0 := move_eq p (hp 10) (hp 3) (Eq.symm hit)
    exact branch8 p q v hq sep (Eq.symm t0)
  · exact branch10 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 24)) (reverse_move p (hp 0)) (Eq.symm hit)
    exact branch5 p q v hp hq sep (Eq.symm t0)
  · have t0 := move_eq p (hp 24) (hp 1) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 3)) (Eq.symm h0)
    have t2 := move_eq p.symm (reverse_move p (hp 158)) (reverse_move p (hp 12)) t1
    have t3 := move_eq p (hp 39) (hp 0) (Eq.symm h0)
    have t4 := move_eq p (hp 158) (hp 1) (Eq.trans t2 t3)
    have t5 := move_eq p (hp 7) (hp 3) (Eq.trans (Eq.trans t0 (Eq.symm t4)) t1)
    exact branch6 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t5)
  · have t0 := move_eq p.symm (reverse_move p (hp 7)) (reverse_move p (hp 0)) (Eq.symm hit)
    exact branch4 p q v hp hq sep (Eq.symm t0)
  · exact branch11 p q v hp hq sep h0 hit
  · have t0 := move_eq p.symm (reverse_move p (hp 33)) (reverse_move p (hp 0)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 96)) (reverse_move p (hp 3)) t0
    have t2 := move_eq q (hq 39) (hq 0) (Eq.symm h0)
    exact branch10 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t1) t2)
  · have t0 := move_eq p.symm (reverse_move p (hp 24)) (reverse_move p (hp 0)) (Eq.symm hit)
    exact branch5 p q v hp hq sep (Eq.symm t0)
  · have t0 := move_eq p (hp 24) (hp 1) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 3)) (Eq.symm h0)
    have t2 := move_eq p.symm (reverse_move p (hp 158)) (reverse_move p (hp 12)) t1
    have t3 := move_eq p (hp 39) (hp 0) (Eq.symm h0)
    have t4 := move_eq p (hp 158) (hp 1) (Eq.trans t2 t3)
    have t5 := move_eq p (hp 7) (hp 3) (Eq.trans (Eq.trans t0 (Eq.symm t4)) t1)
    exact branch6 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t5)
  · exact branch11 p q v hp hq sep h0 hit
  · have t0 := move_eq p.symm (reverse_move p (hp 33)) (reverse_move p (hp 0)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 96)) (reverse_move p (hp 3)) t0
    have t2 := move_eq q (hq 39) (hq 0) (Eq.symm h0)
    exact branch10 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t1) t2)
  · have t0 := move_eq q.symm (reverse_move q (hq 0)) (reverse_move q (hq 7)) (Eq.symm hit)
    exact branch4 p q v hp hq sep t0
  · have t0 := move_eq p.symm (reverse_move p (hp 75)) (reverse_move p (hp 24)) (Eq.symm hit)
    have t1 := move_eq q (hq 75) (hq 7) (Eq.trans t0 (Eq.symm hit))
    exact branch11 p q v hp hq sep h0 (Eq.symm t1)
  · have t0 := move_eq p.symm (reverse_move p (hp 7)) (reverse_move p (hp 24)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 75)) (reverse_move p (hp 24)) (Eq.symm t0)
    have t2 := move_eq q (hq 75) (hq 7) (Eq.trans t1 (Eq.symm t0))
    exact branch11 p q v hp hq sep h0 (Eq.symm t2)
  · have t0 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 3)) (Eq.symm h0)
    have t1 := move_eq p.symm (reverse_move p (hp 158)) (reverse_move p (hp 12)) t0
    have t2 := move_eq p (hp 39) (hp 0) (Eq.symm h0)
    have t3 := move_eq p (hp 158) (hp 1) (Eq.trans t1 t2)
    have t4 := move_eq q (hq 39) (hq 0) (Eq.symm h0)
    have t5 := move_eq p.symm (reverse_move p (hp 147)) (reverse_move p (hp 10)) t4
    have t6 := move_eq q (hq 34) (hq 7) (Eq.symm hit)
    have t7 := move_eq p (hp 147) (hp 1) (Eq.trans t5 t6)
    exact branch10 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.trans (Eq.trans (Eq.symm t0) t3) (Eq.symm t7)) t4)
  · exact branch12 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 75)) (reverse_move p (hp 24)) (Eq.symm hit)
    have t1 := move_eq q (hq 75) (hq 7) (Eq.trans t0 (Eq.symm hit))
    exact branch11 p q v hp hq sep h0 (Eq.symm t1)
  · have t0 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 3)) (Eq.symm h0)
    have t1 := move_eq p.symm (reverse_move p (hp 158)) (reverse_move p (hp 12)) t0
    have t2 := move_eq p (hp 39) (hp 0) (Eq.symm h0)
    have t3 := move_eq p (hp 158) (hp 1) (Eq.trans t1 t2)
    have t4 := move_eq q (hq 39) (hq 0) (Eq.symm h0)
    have t5 := move_eq p.symm (reverse_move p (hp 147)) (reverse_move p (hp 10)) t4
    have t6 := move_eq q (hq 34) (hq 7) (Eq.symm hit)
    have t7 := move_eq p (hp 147) (hp 1) (Eq.trans t5 t6)
    exact branch10 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.trans (Eq.trans (Eq.symm t0) t3) (Eq.symm t7)) t4)
  · exact branch12 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch13 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 75)) (reverse_move p (hp 7)) hit
    have t1 := move_eq q (hq 75) (hq 7) t0
    exact branch11 p q v hp hq sep h0 (Eq.symm t1)
  · exact branch14 p q v hp hq sep h0 hit
  · have t0 := move_eq p (hp 24) (hp 10) hit
    exact branch13 p q v hp hq sep G e₀ e₁ e₂ no t0
  · exact branch14 p q v hp hq sep h0 hit
  · have t0 := move_eq p (hp 24) (hp 10) hit
    exact branch13 p q v hp hq sep G e₀ e₁ e₂ no t0
  · exact branch15 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq q (hq 39) (hq 0) (Eq.symm h0)
    have t1 := move_eq p (hp 96) (hp 2) t0
    have t2 := move_eq p (hp 34) (hp 23) (Eq.symm hit)
    have t3 := move_eq p (hp 98) (hp 71) t2
    have t4 := move_eq q (hq 34) (hq 23) (Eq.symm hit)
    have t5 := move_eq p.symm (reverse_move p (hp 132)) (reverse_move p (hp 33)) (Eq.symm t4)
    have t6 := move_eq q (hq 127) (hq 8) (Eq.trans (Eq.trans (Eq.symm t3) t5) t1)
    have t7 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 3)) (Eq.symm h0)
    have t8 := move_eq p.symm (reverse_move p (hp 158)) (reverse_move p (hp 12)) t7
    have t9 := move_eq p (hp 39) (hp 0) (Eq.symm h0)
    have t10 := move_eq p (hp 158) (hp 1) (Eq.trans t8 t9)
    have t11 := move_eq p (hp 5) (hp 3) (Eq.trans (Eq.symm t10) t7)
    have t12 := move_eq p (hp 17) (hp 0) t11
    have t13 := move_eq q.symm (reverse_move q (hq 8)) (reverse_move q (hq 7)) (Eq.trans (Eq.symm t6) t12)
    have t14 := move_eq p.symm (reverse_move p (hp 96)) (reverse_move p (hp 24)) (Eq.trans t1 t13)
    exact branch15 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t14) t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 7)) (reverse_move p (hp 33)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 96)) (reverse_move p (hp 24)) (Eq.symm t0)
    have t2 := move_eq q (hq 39) (hq 0) (Eq.symm h0)
    exact branch15 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t1) t2)
  · have t0 := move_eq q.symm (reverse_move q (hq 75)) (reverse_move q (hq 34)) hit
    have t1 := move_eq p (hp 75) (hp 10) (Eq.trans t0 hit)
    exact branch15 p q v hp hq sep G e₀ e₁ e₂ no t1
  · have t0 := move_eq p (hp 34) (hp 2) hit
    have t1 := move_eq p (hp 98) (hp 8) t0
    have t2 := move_eq p (hp 132) (hp 26) t1
    have t3 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 3)) (Eq.symm h0)
    have t4 := move_eq p.symm (reverse_move p (hp 158)) (reverse_move p (hp 12)) t3
    have t5 := move_eq p (hp 39) (hp 0) (Eq.symm h0)
    have t6 := move_eq p (hp 158) (hp 1) (Eq.trans t4 t5)
    have t7 := move_eq p (hp 5) (hp 3) (Eq.trans (Eq.symm t6) t3)
    have t8 := move_eq q (hq 17) (hq 0) t7
    have t9 := move_eq q.symm (reverse_move q (hq 23)) (reverse_move q (hq 0)) (Eq.trans t2 t8)
    exact branch6 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t9)
  · have t0 := move_eq q.symm (reverse_move q (hq 75)) (reverse_move q (hq 34)) hit
    have t1 := move_eq p (hp 75) (hp 10) (Eq.trans t0 hit)
    exact branch15 p q v hp hq sep G e₀ e₁ e₂ no t1
  · have t0 := move_eq q.symm (reverse_move q (hq 34)) (reverse_move q (hq 0)) hit
    exact branch7 p q v hp hq sep h0 (Eq.symm t0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp sep G e₀ e₁ e₂ no in
private theorem branch16 (h0 : v 0 = v 106) : False := by
  have t0 := move_eq p (hp 106) (hp 0) (Eq.symm h0)
  have t1 := move_eq p (hp 39) (hp 1) t0
  have t2 := move_eq p (hp 12) (hp 5) t1
  exact short8 p q G sep e₀ e₁ e₂ no ![0,1,0,1,0,1,0,1] (by decide)
    (v 0) (v 0) (v 3) (v 3) (v 5) (v 5) (v 1) (v 1)
    (rfl) (hp 3) (rfl) (Eq.trans (hp 5) (Eq.symm t2)) (rfl) (hp 1) (rfl) (hp 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch18 (h0 : v 0 = v 227) (h1 : v 0 = v 93) : False := by
  have t0 := move_eq p (hp 159) (hp 0) (Eq.symm h0)
  have t1 := move_eq q.symm (reverse_move q (hq 157)) (reverse_move q (hq 7)) t0
  have t2 := move_eq p (hp 163) (hp 7) t1
  have t3 := move_eq p (hp 109) (hp 23) t2
  have t4 := move_eq q (hq 154) (hq 0) (Eq.symm h0)
  have t5 := move_eq p (hp 106) (hp 2) t4
  have t6 := move_eq q (hq 39) (hq 8) t5
  have t7 := move_eq p (hp 93) (hp 0) (Eq.symm h1)
  have t8 := move_eq q.symm (reverse_move q (hq 82)) (reverse_move q (hq 7)) t7
  have t9 := move_eq p (hp 82) (hp 7) t8
  have t10 := move_eq p (hp 96) (hp 23) (Eq.trans t6 t9)
  have t11 := move_eq p (hp 134) (hp 33) (Eq.trans t3 (Eq.symm t10))
  have t12 := move_eq q (hq 78) (hq 10) t11
  have t13 := move_eq q.symm (reverse_move q (hq 32)) (reverse_move q (hq 4)) (Eq.symm h1)
  exact short8 p q G sep e₀ e₁ e₂ no ![0,1,0,2,1,2,1,2] (by decide)
    (v 0) (v 0) (v 3) (v 3) (v 13) (v 4) (v 10) (v 2)
    (rfl) (hp 3) (rfl) (hq 13) (Eq.trans (hp 13) (Eq.trans t12 t13)) (Eq.trans (hq 10) t13) (hp 10) (hq 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch19 (h1 : v 0 = v 32) : False := by
  have t0 := move_eq q (hq 32) (hq 0) (Eq.symm h1)
  have t1 := move_eq p.symm (reverse_move p (hp 144)) (reverse_move p (hp 10)) t0
  have t2 := move_eq q.symm (reverse_move q (hq 10)) (reverse_move q (hq 4)) (Eq.symm h1)
  have t3 := move_eq p (hp 144) (hp 4) (Eq.trans t1 t2)
  exact short4 p q G sep e₀ e₁ e₂ no ![0,2,1,2] (by decide)
    (v 0) (v 0) (v 4) (v 2)
    (rfl) (hq 4) (Eq.trans (hp 4) (Eq.trans (Eq.symm t3) t0)) (hq 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch20 (h0 : v 0 = v 227) (h1 : v 0 = v 27) : False := by
  have t0 := move_eq q (hq 27) (hq 0) (Eq.symm h1)
  have t1 := move_eq p.symm (reverse_move p (hp 135)) (reverse_move p (hp 10)) t0
  have t2 := move_eq p.symm (reverse_move p (hp 90)) (reverse_move p (hp 33)) t1
  have t3 := move_eq q (hq 90) (hq 33) t2
  have t4 := move_eq p.symm (reverse_move p (hp 82)) (reverse_move p (hp 3)) (Eq.symm h1)
  have t5 := move_eq p.symm (reverse_move p (hp 136)) (reverse_move p (hp 12)) t4
  have t6 := move_eq p.symm (reverse_move p (hp 95)) (reverse_move p (hp 39)) t5
  have t7 := move_eq q (hq 154) (hq 0) (Eq.symm h0)
  have t8 := move_eq p (hp 106) (hp 2) t7
  have t9 := move_eq q.symm (reverse_move q (hq 8)) (reverse_move q (hq 4)) (Eq.symm h1)
  have t10 := move_eq q.symm (reverse_move q (hq 90)) (reverse_move q (hq 16)) (Eq.trans (Eq.trans (Eq.trans t3 t6) t8) t9)
  have t11 := move_eq p (hp 33) (hp 16) (Eq.trans (Eq.symm t2) t10)
  have t12 := move_eq p (hp 50) (hp 10) (Eq.symm t11)
  have t13 := move_eq q (hq 73) (hq 2) t12
  have t14 := move_eq q.symm (reverse_move q (hq 28)) (reverse_move q (hq 16)) t9
  have t15 := move_eq p.symm (reverse_move p (hp 84)) (reverse_move p (hp 51)) t14
  have t16 := move_eq p (hp 81) (hp 2) t0
  have t17 := move_eq p.symm (reverse_move p (hp 81)) (reverse_move p (hp 15)) (Eq.trans t16 t9)
  have t18 := move_eq q (hq 15) (hq 2) (Eq.trans (Eq.symm t17) t0)
  have t19 := move_eq p (hp 47) (hp 9) t18
  have t20 := move_eq p.symm (reverse_move p (hp 124)) (reverse_move p (hp 9)) (Eq.trans (Eq.symm t15) t19)
  have t21 := move_eq p.symm (reverse_move p (hp 96)) (reverse_move p (hp 51)) (Eq.trans (Eq.symm t2) t10)
  have t22 := move_eq q (hq 39) (hq 4) (Eq.trans t8 t9)
  have t23 := move_eq p.symm (reverse_move p (hp 124)) (reverse_move p (hp 3)) (Eq.trans (Eq.symm t21) t22)
  have t24 := move_eq q.symm (reverse_move q (hq 125)) (reverse_move q (hq 58)) (Eq.trans (Eq.symm t15) t19)
  have t25 := move_eq q.symm (reverse_move q (hq 125)) (reverse_move q (hq 4)) (Eq.trans (Eq.symm t21) t22)
  have t26 := move_eq p (hp 58) (hp 4) (Eq.trans (Eq.symm t24) t25)
  have t27 := move_eq p (hp 8) (hp 4) t9
  have t28 := move_eq q (hq 26) (hq 14) t27
  have t29 := move_eq q.symm (reverse_move q (hq 45)) (reverse_move q (hq 16)) (Eq.trans (Eq.symm t24) t25)
  have t30 := move_eq p (hp 51) (hp 0) (Eq.trans (Eq.symm t21) t22)
  have t31 := move_eq q.symm (reverse_move q (hq 26)) (reverse_move q (hq 7)) (Eq.trans (Eq.trans t28 t29) t30)
  have t32 := move_eq p (hp 26) (hp 14) t27
  have t33 := move_eq p (hp 28) (hp 16) t14
  have t34 := move_eq q.symm (reverse_move q (hq 44)) (reverse_move q (hq 123)) t33
  have t35 := move_eq q.symm (reverse_move q (hq 123)) (reverse_move q (hq 34)) (Eq.symm t11)
  have t36 := move_eq q.symm (reverse_move q (hq 17)) (reverse_move q (hq 75)) (Eq.trans (Eq.trans t32 t34) t35)
  have t37 := move_eq q (hq 51) (hq 0) (Eq.trans (Eq.symm t21) t22)
  exact short8 p q G sep e₀ e₁ e₂ no ![0,1,0,1,0,2,1,2] (by decide)
    (v 0) (v 0) (v 3) (v 3) (v 7) (v 7) (v 5) (v 2)
    (rfl) (hp 3) (rfl) (Eq.trans (hp 7) (Eq.trans (Eq.trans t13 (Eq.symm t20)) t23)) (rfl) (Eq.trans (hq 5) (Eq.trans (Eq.trans t26 (Eq.symm t27)) t31)) (Eq.trans (hp 5) (Eq.trans t36 t37)) (hq 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch21 (h1 : v 0 = v 180) : False := by
  have t0 := move_eq p.symm (reverse_move p (hp 93)) (reverse_move p (hp 3)) (Eq.symm h1)
  have t1 := move_eq q.symm (reverse_move q (hq 32)) (reverse_move q (hq 13)) t0
  exact short8 p q G sep e₀ e₁ e₂ no ![0,1,0,2,0,2,1,2] (by decide)
    (v 0) (v 0) (v 3) (v 3) (v 13) (v 13) (v 10) (v 2)
    (rfl) (hp 3) (rfl) (hq 13) (rfl) (Eq.trans (hq 10) t1) (hp 10) (hq 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch22 (h0 : v 0 = v 227) (h1 : v 3 = v 27) : False := by
  have t0 := move_eq p (hp 159) (hp 0) (Eq.symm h0)
  have t1 := move_eq p (hp 111) (hp 1) t0
  have t2 := move_eq q.symm (reverse_move q (hq 8)) (reverse_move q (hq 13)) (Eq.symm h1)
  have t3 := move_eq p.symm (reverse_move p (hp 42)) (reverse_move p (hp 2)) (Eq.symm t2)
  exact short4 p q G sep e₀ e₁ e₂ no ![1,0,1,2] (by decide)
    (v 0) (v 1) (v 1) (v 2)
    (hp 0) (rfl) (Eq.trans (hp 1) (Eq.trans (Eq.symm t1) t3)) (hq 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch23 (h0 : v 0 = v 227) (h1 : v 3 = v 180) : False := by
  have t0 := move_eq p.symm (reverse_move p (hp 93)) (reverse_move p (hp 12)) (Eq.symm h1)
  have t1 := move_eq p.symm (reverse_move p (hp 144)) (reverse_move p (hp 39)) t0
  have t2 := move_eq q (hq 154) (hq 0) (Eq.symm h0)
  have t3 := move_eq p (hp 106) (hp 2) t2
  have t4 := move_eq p (hp 144) (hp 8) (Eq.trans t1 t3)
  have t5 := move_eq q (hq 26) (hq 12) (Eq.trans (Eq.symm t4) t0)
  have t6 := move_eq q.symm (reverse_move q (hq 32)) (reverse_move q (hq 40)) t0
  have t7 := move_eq p (hp 40) (hp 32) (Eq.symm t6)
  have t8 := move_eq p (hp 75) (hp 67) t7
  have t9 := move_eq p (hp 24) (hp 21) t8
  exact short8 p q G sep e₀ e₁ e₂ no ![0,1,0,1,2,0,2,1] (by decide)
    (v 0) (v 0) (v 3) (v 3) (v 12) (v 7) (v 7) (v 1)
    (rfl) (hp 3) (rfl) (hp 12) (Eq.trans (hq 12) (Eq.trans (Eq.symm t5) (Eq.symm t9))) (rfl) (hq 7) (hp 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch24 (h1 : v 8 = v 32) : False := by
  have t0 := move_eq p (hp 32) (hp 8) (Eq.symm h1)
  have t1 := move_eq p (hp 67) (hp 26) t0
  have t2 := move_eq q.symm (reverse_move q (hq 17)) (reverse_move q (hq 6)) (Eq.symm t1)
  exact short4 p q G sep e₀ e₁ e₂ no ![1,0,1,2] (by decide)
    (v 1) (v 5) (v 5) (v 6)
    (hp 1) (rfl) (Eq.trans (hp 5) t2) (hq 1)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch17 (h0 : v 0 = v 227) : False := by
  have t0 := move_eq q (hq 154) (hq 0) (Eq.symm h0)
  have t1 := move_eq p (hp 106) (hp 2) t0
  have t2 := move_eq p (hp 39) (hp 8) t1
  rcases collision16 (fun h => no (.inr (.inr (.inl h))))
    (v 0) (v 0) (v 3) (v 3) (v 12) (v 12) (v 8) (v 27) (v 82) (v 180) (v 93) (v 93) (v 32) (v 32) (v 10) (v 2)
    (e₀ (v 0))
    ((hp 3) ▸ e₁ (v 3))
    (e₀ (v 3))
    ((hp 12) ▸ e₁ (v 12))
    (e₀ (v 12))
    ((Eq.trans (hp 8) (Eq.symm t2)) ▸ e₁ (v 8))
    ((hq 8) ▸ e₂ (v 8))
    ((hp 82) ▸ e₁ (v 82))
    ((hq 82) ▸ e₂ (v 82))
    ((hp 93) ▸ e₁ (v 93))
    (e₀ (v 93))
    ((hq 32) ▸ e₂ (v 32))
    (e₀ (v 32))
    ((hq 10) ▸ e₂ (v 10))
    ((hp 10) ▸ e₁ (v 10))
    ((hq 0) ▸ e₂ (v 0)) with hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit
  · exact branch1 p q v hp sep hit
  · exact branch2 p q v hp sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 2)) (reverse_move p (hp 3)) (Eq.symm hit)
    exact branch10 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 82) (hp 0) (Eq.symm hit)
    have t1 := move_eq q.symm (reverse_move q (hq 8)) (reverse_move q (hq 7)) t0
    have t2 := move_eq p.symm (reverse_move p (hp 2)) (reverse_move p (hp 24)) t1
    exact branch15 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · exact branch18 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · exact branch19 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq q (hq 10) (hq 0) (Eq.symm hit)
    have t1 := move_eq p (hp 10) (hp 0) (Eq.symm hit)
    have t2 := move_eq q.symm (reverse_move q (hq 10)) (reverse_move q (hq 7)) (Eq.trans t0 t1)
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · exact branch1 p q v hp sep hit
  · exact branch2 p q v hp sep G e₀ e₁ e₂ no hit
  · exact branch20 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · exact branch21 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch18 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · exact branch19 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch8 p q v hq sep hit
  · have t0 := move_eq p (hp 12) (hp 3) (Eq.symm hit)
    exact branch1 p q v hp sep (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 2)) (reverse_move p (hp 12)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 10)) (Eq.symm t0)
    have t2 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 33)) t1
    have t3 := move_eq q (hq 154) (hq 0) (Eq.symm h0)
    have t4 := move_eq p (hp 33) (hp 2) (Eq.trans (Eq.symm t2) t3)
    have t5 := move_eq p (hp 39) (hp 3) (Eq.trans (Eq.trans t1 t4) (Eq.symm hit))
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t5)
  · have t0 := move_eq p (hp 82) (hp 3) (Eq.symm hit)
    exact branch20 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.symm t0)
  · have t0 := move_eq p (hp 93) (hp 3) (Eq.symm hit)
    exact branch21 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 94)) (reverse_move p (hp 12)) (Eq.symm hit)
    have t1 := move_eq q.symm (reverse_move q (hq 38)) (reverse_move q (hq 40)) t0
    have t2 := move_eq p (hp 40) (hp 38) (Eq.symm t1)
    have t3 := move_eq p (hp 75) (hp 69) t2
    have t4 := move_eq q (hq 154) (hq 0) (Eq.symm h0)
    have t5 := move_eq p (hp 106) (hp 2) t4
    have t6 := move_eq q.symm (reverse_move q (hq 10)) (reverse_move q (hq 13)) (Eq.symm hit)
    have t7 := move_eq p.symm (reverse_move p (hp 42)) (reverse_move p (hp 33)) (Eq.symm t6)
    have t8 := move_eq p.symm (reverse_move p (hp 111)) (reverse_move p (hp 96)) t7
    have t9 := move_eq p (hp 159) (hp 0) (Eq.symm h0)
    have t10 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 7)) (Eq.trans (Eq.symm t8) t9)
    have t11 := move_eq p (hp 32) (hp 3) (Eq.symm hit)
    have t12 := move_eq p (hp 67) (hp 0) t11
    have t13 := move_eq q.symm (reverse_move q (hq 6)) (reverse_move q (hq 7)) t12
    have t14 := move_eq p.symm (reverse_move p (hp 2)) (reverse_move p (hp 22)) (Eq.trans (Eq.trans (Eq.symm t5) t10) (Eq.symm t13))
    exact branch15 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans t3 (Eq.symm t14))
  · have t0 := move_eq p (hp 10) (hp 3) (Eq.symm hit)
    exact branch8 p q v hq sep (Eq.symm t0)
  · have t0 := move_eq p (hp 12) (hp 3) (Eq.symm hit)
    exact branch1 p q v hp sep (Eq.symm t0)
  · exact branch22 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · exact branch23 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · have t0 := move_eq p (hp 93) (hp 3) (Eq.symm hit)
    exact branch21 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 94)) (reverse_move p (hp 12)) (Eq.symm hit)
    have t1 := move_eq q.symm (reverse_move q (hq 38)) (reverse_move q (hq 40)) t0
    have t2 := move_eq p (hp 40) (hp 38) (Eq.symm t1)
    have t3 := move_eq p (hp 75) (hp 69) t2
    have t4 := move_eq q (hq 154) (hq 0) (Eq.symm h0)
    have t5 := move_eq p (hp 106) (hp 2) t4
    have t6 := move_eq q.symm (reverse_move q (hq 10)) (reverse_move q (hq 13)) (Eq.symm hit)
    have t7 := move_eq p.symm (reverse_move p (hp 42)) (reverse_move p (hp 33)) (Eq.symm t6)
    have t8 := move_eq p.symm (reverse_move p (hp 111)) (reverse_move p (hp 96)) t7
    have t9 := move_eq p (hp 159) (hp 0) (Eq.symm h0)
    have t10 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 7)) (Eq.trans (Eq.symm t8) t9)
    have t11 := move_eq p (hp 32) (hp 3) (Eq.symm hit)
    have t12 := move_eq p (hp 67) (hp 0) t11
    have t13 := move_eq q.symm (reverse_move q (hq 6)) (reverse_move q (hq 7)) t12
    have t14 := move_eq p.symm (reverse_move p (hp 2)) (reverse_move p (hp 22)) (Eq.trans (Eq.trans (Eq.symm t5) t10) (Eq.symm t13))
    exact branch15 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans t3 (Eq.symm t14))
  · exact branch10 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p (hp 12) (hp 8) hit
    have t1 := move_eq p (hp 26) (hp 3) (Eq.symm t0)
    have t2 := move_eq q (hq 54) (hq 0) t1
    have t3 := move_eq p.symm (reverse_move p (hp 86)) (reverse_move p (hp 10)) t2
    have t4 := move_eq q.symm (reverse_move q (hq 40)) (reverse_move q (hq 28)) hit
    have t5 := move_eq p (hp 40) (hp 28) t4
    have t6 := move_eq q (hq 83) (hq 75) (Eq.symm t5)
    have t7 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 2)) hit
    have t8 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 10)) t7
    have t9 := move_eq q.symm (reverse_move q (hq 154)) (reverse_move q (hq 34)) t8
    have t10 := move_eq q (hq 145) (hq 0) (Eq.trans (Eq.trans t6 (Eq.symm t9)) (Eq.symm h0))
    have t11 := move_eq p (hp 10) (hp 2) (Eq.trans (Eq.symm t3) t10)
    have t12 := move_eq p (hp 12) (hp 2) (Eq.trans hit (Eq.symm t11))
    exact branch10 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans t12 (Eq.symm t11))
  · have t0 := move_eq p (hp 82) (hp 12) (Eq.symm hit)
    exact branch22 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.symm t0)
  · have t0 := move_eq p (hp 93) (hp 12) (Eq.symm hit)
    exact branch23 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.symm t0)
  · have t0 := move_eq q.symm (reverse_move q (hq 10)) (reverse_move q (hq 40)) (Eq.symm hit)
    have t1 := move_eq q.symm (reverse_move q (hq 109)) (reverse_move q (hq 34)) (Eq.symm t0)
    have t2 := move_eq p (hp 40) (hp 10) (Eq.symm t0)
    have t3 := move_eq q (hq 75) (hq 2) t2
    have t4 := move_eq q.symm (reverse_move q (hq 158)) (reverse_move q (hq 2)) (Eq.trans t1 t3)
    have t5 := move_eq p (hp 164) (hp 2) t4
    have t6 := move_eq q.symm (reverse_move q (hq 162)) (reverse_move q (hq 28)) t5
    have t7 := move_eq q (hq 32) (hq 12) (Eq.symm hit)
    have t8 := move_eq q (hq 93) (hq 38) t7
    have t9 := move_eq p.symm (reverse_move p (hp 94)) (reverse_move p (hp 39)) (Eq.symm hit)
    have t10 := move_eq q (hq 154) (hq 0) (Eq.symm h0)
    have t11 := move_eq p (hp 106) (hp 2) t10
    have t12 := move_eq q.symm (reverse_move q (hq 93)) (reverse_move q (hq 28)) (Eq.trans (Eq.trans t8 t9) t11)
    have t13 := move_eq q.symm (reverse_move q (hq 38)) (reverse_move q (hq 107)) t9
    have t14 := move_eq p.symm (reverse_move p (hp 160)) (reverse_move p (hp 105)) (Eq.symm t13)
    have t15 := move_eq p (hp 159) (hp 0) (Eq.symm h0)
    have t16 := move_eq q (hq 111) (hq 1) t15
    have t17 := move_eq p (hp 32) (hp 12) (Eq.symm hit)
    have t18 := move_eq p (hp 67) (hp 3) t17
    have t19 := move_eq q.symm (reverse_move q (hq 6)) (reverse_move q (hq 4)) t18
    have t20 := move_eq q (hq 153) (hq 4) (Eq.trans t16 t19)
    have t21 := move_eq p (hp 160) (hp 0) (Eq.trans t14 t20)
    have t22 := move_eq q (hq 162) (hq 1) (Eq.trans (Eq.trans (Eq.trans (Eq.trans t6 (Eq.symm t12)) t7) t13) t21)
    have t23 := move_eq q (hq 8) (hq 4) (Eq.trans (Eq.trans (Eq.symm t5) t22) t19)
    exact branch20 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.symm t23)
  · have t0 := move_eq p (hp 12) (hp 10) hit
    exact branch10 p q v hp hq sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq q (hq 154) (hq 0) (Eq.symm h0)
    have t1 := move_eq p.symm (reverse_move p (hp 158)) (reverse_move p (hp 10)) t0
    have t2 := move_eq q.symm (reverse_move q (hq 8)) (reverse_move q (hq 40)) (Eq.symm hit)
    have t3 := move_eq p (hp 40) (hp 8) (Eq.symm t2)
    have t4 := move_eq q.symm (reverse_move q (hq 51)) (reverse_move q (hq 72)) t3
    have t5 := move_eq q.symm (reverse_move q (hq 109)) (reverse_move q (hq 28)) (Eq.symm t2)
    have t6 := move_eq p (hp 159) (hp 0) (Eq.symm h0)
    have t7 := move_eq q.symm (reverse_move q (hq 157)) (reverse_move q (hq 7)) t6
    have t8 := move_eq p (hp 163) (hp 7) t7
    have t9 := move_eq q (hq 28) (hq 23) (Eq.trans (Eq.symm t5) t8)
    have t10 := move_eq p.symm (reverse_move p (hp 124)) (reverse_move p (hp 2)) (Eq.trans t4 (Eq.symm t9))
    have t11 := move_eq p.symm (reverse_move p (hp 161)) (reverse_move p (hp 10)) t10
    have t12 := move_eq p (hp 106) (hp 2) t0
    have t13 := move_eq q.symm (reverse_move q (hq 107)) (reverse_move q (hq 28)) t12
    have t14 := move_eq q.symm (reverse_move q (hq 155)) (reverse_move q (hq 73)) (Eq.trans (Eq.trans t13 (Eq.symm t5)) t8)
    have t15 := move_eq q.symm (reverse_move q (hq 85)) (reverse_move q (hq 73)) (Eq.trans (Eq.symm t5) t8)
    have t16 := move_eq q (hq 27) (hq 12) (Eq.symm hit)
    have t17 := move_eq p (hp 39) (hp 8) t12
    have t18 := move_eq q (hq 75) (hq 12) (Eq.trans t3 (Eq.symm t17))
    have t19 := move_eq p (hp 81) (hp 34) (Eq.trans t16 (Eq.symm t18))
    have t20 := move_eq p (hp 81) (hp 38) t16
    have t21 := move_eq q.symm (reverse_move q (hq 147)) (reverse_move q (hq 136)) (Eq.trans (Eq.symm t19) t20)
    have t22 := move_eq q.symm (reverse_move q (hq 86)) (reverse_move q (hq 136)) t20
    have t23 := move_eq p.symm (reverse_move p (hp 82)) (reverse_move p (hp 39)) (Eq.symm hit)
    have t24 := move_eq q.symm (reverse_move q (hq 144)) (reverse_move q (hq 107)) t23
    have t25 := move_eq q.symm (reverse_move q (hq 98)) (reverse_move q (hq 155)) t24
    have t26 := move_eq q.symm (reverse_move q (hq 86)) (reverse_move q (hq 34)) (Eq.trans (Eq.trans t19 t25) t11)
    have t27 := move_eq p.symm (reverse_move p (hp 136)) (reverse_move p (hp 106)) t23
    have t28 := move_eq p.symm (reverse_move p (hp 95)) (reverse_move p (hp 158)) t27
    have t29 := move_eq q.symm (reverse_move q (hq 33)) (reverse_move q (hq 34)) (Eq.trans t28 t1)
    have t30 := move_eq q (hq 39) (hq 8) t12
    have t31 := move_eq p (hp 96) (hp 12) (Eq.trans t30 (Eq.symm hit))
    have t32 := move_eq p (hp 137) (hp 3) (Eq.trans (Eq.trans (Eq.trans (Eq.trans t21 (Eq.symm t22)) t26) (Eq.symm t29)) t31)
    have t33 := move_eq p (hp 158) (hp 0) (Eq.trans (Eq.trans (Eq.trans (Eq.trans t1 (Eq.symm t11)) t14) (Eq.symm t15)) t32)
    have t34 := move_eq q.symm (reverse_move q (hq 0)) (reverse_move q (hq 7)) (Eq.trans (Eq.symm t0) t33)
    exact branch4 p q v hp hq sep t34
  · have t0 := move_eq q (hq 154) (hq 0) (Eq.symm h0)
    have t1 := move_eq p (hp 106) (hp 2) t0
    have t2 := move_eq q (hq 39) (hq 8) t1
    have t3 := move_eq p (hp 96) (hp 27) t2
    have t4 := move_eq q.symm (reverse_move q (hq 82)) (reverse_move q (hq 40)) (Eq.symm hit)
    have t5 := move_eq p (hp 82) (hp 40) t4
    have t6 := move_eq p (hp 75) (hp 27) (Eq.symm t5)
    have t7 := move_eq p (hp 33) (hp 24) (Eq.trans t3 (Eq.symm t6))
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t7)
  · have t0 := move_eq p (hp 93) (hp 12) (Eq.symm hit)
    exact branch23 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.symm t0)
  · have t0 := move_eq q.symm (reverse_move q (hq 10)) (reverse_move q (hq 40)) (Eq.symm hit)
    have t1 := move_eq q.symm (reverse_move q (hq 109)) (reverse_move q (hq 34)) (Eq.symm t0)
    have t2 := move_eq p (hp 40) (hp 10) (Eq.symm t0)
    have t3 := move_eq q (hq 75) (hq 2) t2
    have t4 := move_eq q.symm (reverse_move q (hq 158)) (reverse_move q (hq 2)) (Eq.trans t1 t3)
    have t5 := move_eq p (hp 164) (hp 2) t4
    have t6 := move_eq q.symm (reverse_move q (hq 162)) (reverse_move q (hq 28)) t5
    have t7 := move_eq q (hq 32) (hq 12) (Eq.symm hit)
    have t8 := move_eq q (hq 93) (hq 38) t7
    have t9 := move_eq p.symm (reverse_move p (hp 94)) (reverse_move p (hp 39)) (Eq.symm hit)
    have t10 := move_eq q (hq 154) (hq 0) (Eq.symm h0)
    have t11 := move_eq p (hp 106) (hp 2) t10
    have t12 := move_eq q.symm (reverse_move q (hq 93)) (reverse_move q (hq 28)) (Eq.trans (Eq.trans t8 t9) t11)
    have t13 := move_eq q.symm (reverse_move q (hq 38)) (reverse_move q (hq 107)) t9
    have t14 := move_eq p.symm (reverse_move p (hp 160)) (reverse_move p (hp 105)) (Eq.symm t13)
    have t15 := move_eq p (hp 159) (hp 0) (Eq.symm h0)
    have t16 := move_eq q (hq 111) (hq 1) t15
    have t17 := move_eq p (hp 32) (hp 12) (Eq.symm hit)
    have t18 := move_eq p (hp 67) (hp 3) t17
    have t19 := move_eq q.symm (reverse_move q (hq 6)) (reverse_move q (hq 4)) t18
    have t20 := move_eq q (hq 153) (hq 4) (Eq.trans t16 t19)
    have t21 := move_eq p (hp 160) (hp 0) (Eq.trans t14 t20)
    have t22 := move_eq q (hq 162) (hq 1) (Eq.trans (Eq.trans (Eq.trans (Eq.trans t6 (Eq.symm t12)) t7) t13) t21)
    have t23 := move_eq q (hq 8) (hq 4) (Eq.trans (Eq.trans (Eq.symm t5) t22) t19)
    exact branch20 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.symm t23)
  · have t0 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 10)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 33)) t0
    have t2 := move_eq q (hq 154) (hq 0) (Eq.symm h0)
    have t3 := move_eq p (hp 33) (hp 2) (Eq.trans (Eq.symm t1) t2)
    have t4 := move_eq p (hp 12) (hp 2) hit
    have t5 := move_eq p (hp 39) (hp 3) (Eq.trans (Eq.trans t0 t3) (Eq.symm t4))
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t5)
  · have t0 := move_eq q (hq 154) (hq 0) (Eq.symm h0)
    have t1 := move_eq p.symm (reverse_move p (hp 158)) (reverse_move p (hp 10)) t0
    have t2 := move_eq q (hq 82) (hq 8) (Eq.symm hit)
    have t3 := move_eq p (hp 82) (hp 8) (Eq.symm hit)
    have t4 := move_eq q.symm (reverse_move q (hq 82)) (reverse_move q (hq 72)) (Eq.trans t2 t3)
    have t5 := move_eq p.symm (reverse_move p (hp 132)) (reverse_move p (hp 2)) (Eq.trans (Eq.symm t4) (Eq.symm hit))
    have t6 := move_eq p.symm (reverse_move p (hp 98)) (reverse_move p (hp 10)) t5
    have t7 := move_eq q.symm (reverse_move q (hq 144)) (reverse_move q (hq 28)) (Eq.symm hit)
    have t8 := move_eq q.symm (reverse_move q (hq 98)) (reverse_move q (hq 85)) t7
    have t9 := move_eq p.symm (reverse_move p (hp 34)) (reverse_move p (hp 137)) t8
    have t10 := move_eq p.symm (reverse_move p (hp 136)) (reverse_move p (hp 2)) (Eq.symm hit)
    have t11 := move_eq p.symm (reverse_move p (hp 95)) (reverse_move p (hp 10)) t10
    have t12 := move_eq q.symm (reverse_move q (hq 33)) (reverse_move q (hq 34)) t11
    have t13 := move_eq p (hp 106) (hp 2) t0
    have t14 := move_eq q (hq 39) (hq 8) t13
    have t15 := move_eq p (hp 39) (hp 8) t13
    have t16 := move_eq p (hp 96) (hp 12) (Eq.trans (Eq.trans t14 t3) (Eq.symm t15))
    have t17 := move_eq p (hp 137) (hp 3) (Eq.trans (Eq.trans (Eq.symm t9) (Eq.symm t12)) t16)
    have t18 := move_eq p (hp 158) (hp 0) (Eq.trans (Eq.trans (Eq.trans t1 (Eq.symm t6)) t8) t17)
    have t19 := move_eq q.symm (reverse_move q (hq 0)) (reverse_move q (hq 7)) (Eq.trans (Eq.symm t0) t18)
    exact branch4 p q v hp hq sep t19
  · have t0 := move_eq q (hq 154) (hq 0) (Eq.symm h0)
    have t1 := move_eq p (hp 106) (hp 2) t0
    have t2 := move_eq q (hq 39) (hq 8) t1
    have t3 := move_eq p.symm (reverse_move p (hp 147)) (reverse_move p (hp 82)) t2
    have t4 := move_eq p (hp 93) (hp 8) (Eq.symm hit)
    have t5 := move_eq q.symm (reverse_move q (hq 82)) (reverse_move q (hq 72)) t4
    have t6 := move_eq p (hp 159) (hp 0) (Eq.symm h0)
    have t7 := move_eq q.symm (reverse_move q (hq 157)) (reverse_move q (hq 7)) t6
    have t8 := move_eq p (hp 163) (hp 7) t7
    have t9 := move_eq q (hq 109) (hq 23) t8
    have t10 := move_eq p (hp 147) (hp 40) (Eq.trans (Eq.trans t3 t5) (Eq.symm t9))
    have t11 := move_eq p (hp 75) (hp 27) (Eq.trans (Eq.symm t10) t2)
    have t12 := move_eq p (hp 80) (hp 24) (Eq.symm t11)
    have t13 := move_eq q (hq 93) (hq 8) (Eq.symm hit)
    have t14 := move_eq p (hp 139) (hp 27) t13
    have t15 := move_eq p (hp 88) (hp 80) t14
    have t16 := move_eq q (hq 75) (hq 27) (Eq.trans (Eq.symm t10) t2)
    have t17 := move_eq q (hq 81) (hq 34) (Eq.symm t16)
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.trans (Eq.symm t12) (Eq.symm t15)) t17)
  · exact branch24 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 33)) (reverse_move p (hp 2)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 96)) (reverse_move p (hp 10)) t0
    have t2 := move_eq q.symm (reverse_move q (hq 34)) (reverse_move q (hq 28)) (Eq.symm hit)
    have t3 := move_eq p.symm (reverse_move p (hp 99)) (reverse_move p (hp 84)) t2
    have t4 := move_eq p.symm (reverse_move p (hp 149)) (reverse_move p (hp 47)) t3
    have t5 := move_eq q.symm (reverse_move q (hq 97)) (reverse_move q (hq 0)) t0
    have t6 := move_eq p (hp 97) (hp 0) t5
    have t7 := move_eq p (hp 149) (hp 1) (Eq.trans t4 t6)
    have t8 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 28)) (Eq.trans t1 (Eq.symm hit))
    have t9 := move_eq p (hp 10) (hp 8) (Eq.symm hit)
    have t10 := move_eq p (hp 26) (hp 2) (Eq.symm t9)
    have t11 := move_eq q.symm (reverse_move q (hq 17)) (reverse_move q (hq 28)) t10
    have t12 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 5)) (Eq.trans t8 (Eq.symm t11))
    have t13 := move_eq q (hq 154) (hq 0) (Eq.symm h0)
    have t14 := move_eq p.symm (reverse_move p (hp 47)) (reverse_move p (hp 10)) (Eq.trans (Eq.trans (Eq.trans (Eq.symm t3) t7) (Eq.symm t12)) t13)
    have t15 := move_eq p.symm (reverse_move p (hp 147)) (reverse_move p (hp 0)) (Eq.trans (Eq.trans t1 (Eq.symm t14)) t6)
    have t16 := move_eq p.symm (reverse_move p (hp 147)) (reverse_move p (hp 2)) (Eq.trans t1 (Eq.symm hit))
    exact branch8 p q v hq sep (Eq.trans (Eq.symm t15) t16)
  · have t0 := move_eq q (hq 154) (hq 0) (Eq.symm h0)
    have t1 := move_eq p.symm (reverse_move p (hp 158)) (reverse_move p (hp 10)) t0
    have t2 := move_eq p.symm (reverse_move p (hp 93)) (reverse_move p (hp 82)) (Eq.symm hit)
    have t3 := move_eq q.symm (reverse_move q (hq 82)) (reverse_move q (hq 8)) (Eq.symm hit)
    have t4 := move_eq q.symm (reverse_move q (hq 32)) (reverse_move q (hq 28)) (Eq.trans t2 t3)
    have t5 := move_eq q.symm (reverse_move q (hq 10)) (reverse_move q (hq 85)) t4
    have t6 := move_eq p.symm (reverse_move p (hp 137)) (reverse_move p (hp 33)) (Eq.symm t5)
    have t7 := move_eq p (hp 106) (hp 2) t0
    have t8 := move_eq q (hq 39) (hq 8) t7
    have t9 := move_eq p (hp 82) (hp 8) t3
    have t10 := move_eq p (hp 39) (hp 8) t7
    have t11 := move_eq p (hp 96) (hp 12) (Eq.trans (Eq.trans t8 t9) (Eq.symm t10))
    have t12 := move_eq p (hp 137) (hp 3) (Eq.trans t6 t11)
    have t13 := move_eq p (hp 158) (hp 0) (Eq.trans (Eq.trans t1 t5) t12)
    have t14 := move_eq q.symm (reverse_move q (hq 0)) (reverse_move q (hq 7)) (Eq.trans (Eq.symm t0) t13)
    exact branch4 p q v hp hq sep t14
  · have t0 := move_eq q.symm (reverse_move q (hq 32)) (reverse_move q (hq 8)) (Eq.symm hit)
    exact branch24 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq q.symm (reverse_move q (hq 10)) (reverse_move q (hq 8)) (Eq.symm hit)
    have t1 := move_eq p (hp 10) (hp 8) t0
    have t2 := move_eq p (hp 26) (hp 2) (Eq.symm t1)
    have t3 := move_eq q.symm (reverse_move q (hq 17)) (reverse_move q (hq 28)) t2
    have t4 := move_eq q.symm (reverse_move q (hq 34)) (reverse_move q (hq 28)) t0
    have t5 := move_eq p (hp 34) (hp 28) t4
    have t6 := move_eq p.symm (reverse_move p (hp 94)) (reverse_move p (hp 82)) (Eq.symm hit)
    have t7 := move_eq q.symm (reverse_move q (hq 38)) (reverse_move q (hq 144)) t6
    have t8 := move_eq q.symm (reverse_move q (hq 98)) (reverse_move q (hq 12)) (Eq.symm t7)
    have t9 := move_eq p.symm (reverse_move p (hp 28)) (reverse_move p (hp 39)) (Eq.trans (Eq.symm t5) t8)
    have t10 := move_eq q (hq 154) (hq 0) (Eq.symm h0)
    have t11 := move_eq p (hp 106) (hp 2) t10
    have t12 := move_eq q (hq 17) (hq 8) (Eq.trans (Eq.trans t3 t9) t11)
    exact branch24 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.trans (Eq.symm t2) t12) hit)
  · have t0 := move_eq p (hp 27) (hp 2) hit
    have t1 := move_eq q.symm (reverse_move q (hq 8)) (reverse_move q (hq 0)) hit
    have t2 := move_eq p.symm (reverse_move p (hp 27)) (reverse_move p (hp 3)) (Eq.trans t0 t1)
    exact branch22 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.symm t2)
  · have t0 := move_eq q (hq 154) (hq 0) (Eq.symm h0)
    have t1 := move_eq p.symm (reverse_move p (hp 158)) (reverse_move p (hp 10)) t0
    have t2 := move_eq q.symm (reverse_move q (hq 32)) (reverse_move q (hq 144)) (Eq.symm hit)
    have t3 := move_eq q.symm (reverse_move q (hq 98)) (reverse_move q (hq 10)) (Eq.symm t2)
    have t4 := move_eq p (hp 93) (hp 82) (Eq.symm hit)
    have t5 := move_eq q.symm (reverse_move q (hq 82)) (reverse_move q (hq 8)) t4
    have t6 := move_eq q.symm (reverse_move q (hq 144)) (reverse_move q (hq 28)) t5
    have t7 := move_eq q.symm (reverse_move q (hq 98)) (reverse_move q (hq 85)) t6
    have t8 := move_eq q.symm (reverse_move q (hq 147)) (reverse_move q (hq 34)) t3
    have t9 := move_eq p.symm (reverse_move p (hp 34)) (reverse_move p (hp 33)) t3
    have t10 := move_eq p (hp 106) (hp 2) t0
    have t11 := move_eq q (hq 39) (hq 8) t10
    have t12 := move_eq p (hp 82) (hp 8) t5
    have t13 := move_eq p (hp 39) (hp 8) t10
    have t14 := move_eq p (hp 96) (hp 12) (Eq.trans (Eq.trans t11 t12) (Eq.symm t13))
    have t15 := move_eq p (hp 137) (hp 3) (Eq.trans (Eq.trans t8 t9) t14)
    have t16 := move_eq p (hp 158) (hp 0) (Eq.trans (Eq.trans (Eq.trans t1 (Eq.symm t3)) t7) t15)
    have t17 := move_eq q.symm (reverse_move q (hq 0)) (reverse_move q (hq 7)) (Eq.trans (Eq.symm t0) t16)
    exact branch4 p q v hp hq sep t17
  · have t0 := move_eq q.symm (reverse_move q (hq 144)) (reverse_move q (hq 10)) hit
    have t1 := move_eq q.symm (reverse_move q (hq 98)) (reverse_move q (hq 34)) t0
    have t2 := move_eq p.symm (reverse_move p (hp 34)) (reverse_move p (hp 99)) t1
    have t3 := move_eq p.symm (reverse_move p (hp 149)) (reverse_move p (hp 99)) (Eq.symm t2)
    have t4 := move_eq q.symm (reverse_move q (hq 147)) (reverse_move q (hq 75)) t1
    have t5 := move_eq p (hp 98) (hp 34) t1
    have t6 := move_eq p (hp 132) (hp 34) (Eq.trans t5 t1)
    have t7 := move_eq q.symm (reverse_move q (hq 23)) (reverse_move q (hq 75)) (Eq.trans t6 t1)
    have t8 := move_eq p (hp 159) (hp 0) (Eq.symm h0)
    have t9 := move_eq q.symm (reverse_move q (hq 157)) (reverse_move q (hq 7)) t8
    have t10 := move_eq p (hp 163) (hp 7) t9
    have t11 := move_eq q (hq 109) (hq 23) t10
    have t12 := move_eq p.symm (reverse_move p (hp 40)) (reverse_move p (hp 7)) (Eq.symm t7)
    have t13 := move_eq p (hp 132) (hp 7) (Eq.trans (Eq.trans (Eq.trans t5 (Eq.symm t6)) (Eq.symm t11)) t12)
    have t14 := move_eq q (hq 147) (hq 7) (Eq.trans (Eq.trans (Eq.trans (Eq.trans t4 (Eq.symm t7)) (Eq.symm t13)) (Eq.symm t11)) t12)
    have t15 := move_eq p (hp 149) (hp 1) (Eq.trans (Eq.trans (Eq.trans t3 (Eq.symm t2)) (Eq.symm t1)) t14)
    have t16 := move_eq p.symm (reverse_move p (hp 1)) (reverse_move p (hp 0)) (Eq.trans (Eq.trans (Eq.trans (Eq.symm t15) (Eq.symm t2)) (Eq.symm t1)) t14)
    exact branch6 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.trans (Eq.trans (Eq.symm t16) (Eq.symm t14)) (Eq.symm t6)) t13)
  · have t0 := move_eq p (hp 82) (hp 10) hit
    have t1 := move_eq q.symm (reverse_move q (hq 8)) (reverse_move q (hq 0)) t0
    have t2 := move_eq q (hq 154) (hq 0) (Eq.symm h0)
    have t3 := move_eq p (hp 106) (hp 2) t2
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t1) (Eq.symm t3))
  · have t0 := move_eq p (hp 159) (hp 0) (Eq.symm h0)
    have t1 := move_eq q.symm (reverse_move q (hq 157)) (reverse_move q (hq 7)) t0
    have t2 := move_eq p (hp 163) (hp 7) t1
    have t3 := move_eq q (hq 109) (hq 23) t2
    have t4 := move_eq q.symm (reverse_move q (hq 82)) (reverse_move q (hq 32)) hit
    have t5 := move_eq q.symm (reverse_move q (hq 144)) (reverse_move q (hq 10)) t4
    have t6 := move_eq q.symm (reverse_move q (hq 98)) (reverse_move q (hq 34)) t5
    have t7 := move_eq p (hp 98) (hp 34) t6
    have t8 := move_eq p (hp 132) (hp 34) (Eq.trans t7 t6)
    have t9 := move_eq q (hq 111) (hq 1) t0
    have t10 := move_eq q (hq 153) (hq 6) t9
    have t11 := move_eq p (hp 105) (hp 21) t10
    have t12 := move_eq q (hq 154) (hq 0) (Eq.symm h0)
    have t13 := move_eq p (hp 106) (hp 2) t12
    have t14 := move_eq q (hq 39) (hq 8) t13
    have t15 := move_eq p (hp 96) (hp 27) t14
    have t16 := move_eq p (hp 82) (hp 32) t4
    have t17 := move_eq p (hp 67) (hp 27) (Eq.symm t16)
    have t18 := move_eq p (hp 33) (hp 21) (Eq.trans t15 (Eq.symm t17))
    have t19 := move_eq q.symm (reverse_move q (hq 12)) (reverse_move q (hq 34)) (Eq.trans t11 (Eq.symm t18))
    have t20 := move_eq p (hp 40) (hp 12) (Eq.trans (Eq.trans (Eq.trans t3 t8) t6) (Eq.symm t19))
    have t21 := move_eq p (hp 75) (hp 3) t20
    exact branch5 p q v hp hq sep (Eq.symm t21)
  · have t0 := move_eq q.symm (reverse_move q (hq 82)) (reverse_move q (hq 10)) hit
    have t1 := move_eq p (hp 82) (hp 10) t0
    have t2 := move_eq q.symm (reverse_move q (hq 8)) (reverse_move q (hq 0)) t1
    have t3 := move_eq q (hq 154) (hq 0) (Eq.symm h0)
    have t4 := move_eq p (hp 106) (hp 2) t3
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t2) (Eq.symm t4))
  · have t0 := move_eq q (hq 154) (hq 0) (Eq.symm h0)
    have t1 := move_eq p (hp 106) (hp 2) t0
    have t2 := move_eq q.symm (reverse_move q (hq 82)) (reverse_move q (hq 0)) hit
    have t3 := move_eq p (hp 82) (hp 0) t2
    have t4 := move_eq q.symm (reverse_move q (hq 8)) (reverse_move q (hq 7)) t3
    have t5 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 24)) (Eq.trans t1 t4)
    exact branch15 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t5) t0)
  · have t0 := move_eq q (hq 93) (hq 32) hit
    have t1 := move_eq q.symm (reverse_move q (hq 32)) (reverse_move q (hq 10)) hit
    have t2 := move_eq q.symm (reverse_move q (hq 93)) (reverse_move q (hq 34)) (Eq.trans (Eq.trans t0 hit) t1)
    have t3 := move_eq q.symm (reverse_move q (hq 75)) (reverse_move q (hq 34)) (Eq.trans (Eq.trans (Eq.symm t2) hit) t1)
    have t4 := move_eq p (hp 75) (hp 10) (Eq.trans (Eq.trans (Eq.trans t3 (Eq.symm t2)) hit) t1)
    exact branch15 p q v hp hq sep G e₀ e₁ e₂ no t4
  · have t0 := move_eq q.symm (reverse_move q (hq 32)) (reverse_move q (hq 34)) hit
    have t1 := move_eq q.symm (reverse_move q (hq 75)) (reverse_move q (hq 10)) (Eq.symm t0)
    have t2 := move_eq p (hp 75) (hp 10) t1
    exact branch15 p q v hp hq sep G e₀ e₁ e₂ no t2
  · have t0 := move_eq q (hq 93) (hq 32) hit
    have t1 := move_eq q.symm (reverse_move q (hq 32)) (reverse_move q (hq 10)) hit
    have t2 := move_eq q.symm (reverse_move q (hq 93)) (reverse_move q (hq 34)) (Eq.trans (Eq.trans t0 hit) t1)
    have t3 := move_eq q.symm (reverse_move q (hq 75)) (reverse_move q (hq 34)) (Eq.trans (Eq.trans (Eq.symm t2) hit) t1)
    have t4 := move_eq p (hp 75) (hp 10) (Eq.trans (Eq.trans (Eq.trans t3 (Eq.symm t2)) hit) t1)
    exact branch15 p q v hp hq sep G e₀ e₁ e₂ no t4
  · have t0 := move_eq q.symm (reverse_move q (hq 32)) (reverse_move q (hq 0)) hit
    exact branch19 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq q.symm (reverse_move q (hq 10)) (reverse_move q (hq 34)) hit
    have t1 := move_eq q.symm (reverse_move q (hq 75)) (reverse_move q (hq 34)) (Eq.symm t0)
    have t2 := move_eq p (hp 75) (hp 10) (Eq.trans t1 (Eq.symm t0))
    exact branch15 p q v hp hq sep G e₀ e₁ e₂ no t2
  · have t0 := move_eq p.symm (reverse_move p (hp 94)) (reverse_move p (hp 10)) hit
    have t1 := move_eq q.symm (reverse_move q (hq 10)) (reverse_move q (hq 0)) hit
    have t2 := move_eq q (hq 94) (hq 0) (Eq.trans t0 t1)
    have t3 := move_eq p (hp 94) (hp 0) (Eq.trans t0 t1)
    have t4 := move_eq q.symm (reverse_move q (hq 94)) (reverse_move q (hq 7)) (Eq.trans (Eq.trans t2 (Eq.symm hit)) t3)
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t4) t0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch25 (h0 : v 0 = v 111) : False := by
  have t0 := move_eq p (hp 111) (hp 0) (Eq.symm h0)
  have t1 := move_eq p (hp 42) (hp 1) t0
  have t2 := move_eq q (hq 13) (hq 5) t1
  exact short8 p q G sep e₀ e₁ e₂ no ![0,1,0,2,0,1,0,1] (by decide)
    (v 0) (v 0) (v 3) (v 3) (v 5) (v 5) (v 1) (v 1)
    (rfl) (hp 3) (rfl) (Eq.trans (hq 5) (Eq.symm t2)) (rfl) (hp 1) (rfl) (hp 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch26 (h0 : v 0 = v 42) : False := by
  have t0 := move_eq p (hp 42) (hp 0) (Eq.symm h0)
  have t1 := move_eq p (hp 13) (hp 1) t0
  have t2 := move_eq q.symm (reverse_move q (hq 78)) (reverse_move q (hq 19)) t1
  have t3 := move_eq p (hp 78) (hp 19) t2
  exact short8 p q G sep e₀ e₁ e₂ no ![0,2,0,2,0,1,2,1] (by decide)
    (v 1) (v 1) (v 7) (v 7) (v 25) (v 25) (v 19) (v 5)
    (rfl) (hq 7) (rfl) (hq 25) (rfl) (Eq.trans (hp 19) (Eq.symm t3)) (hq 19) (hp 1)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep in
private theorem branch27 (h0 : v 0 = v 41) : False := by
  have t0 := move_eq p.symm (reverse_move p (hp 13)) (reverse_move p (hp 3)) (Eq.symm h0)
  have t1 := move_eq q (hq 13) (hq 3) t0
  exact (sep (v 3)).2.1 (Eq.trans (hq 3) (Eq.symm t1))

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep in
private theorem branch28 (h0 : v 0 = v 60) : False := by
  have t0 := move_eq p (hp 60) (hp 0) (Eq.symm h0)
  have t1 := move_eq q (hq 19) (hq 1) t0
  exact (sep (v 1)).2.2 (Eq.trans (hp 1) (Eq.symm (Eq.trans (hq 1) (Eq.symm t1))))

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch29 (h0 : v 0 = v 19) : False := by
  have t0 := move_eq q (hq 19) (hq 0) (Eq.symm h0)
  exact short4 p q G sep e₀ e₁ e₂ no ![1,0,1,2] (by decide)
    (v 0) (v 1) (v 1) (v 2)
    (hp 0) (rfl) (Eq.trans (hp 1) t0) (hq 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch30 (h0 : v 0 = v 142) : False := by
  have t0 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 3)) (Eq.symm h0)
  have t1 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 12)) t0
  have t2 := move_eq q (hq 25) (hq 12) t1
  exact short8 p q G sep e₀ e₁ e₂ no ![0,1,0,1,2,0,2,1] (by decide)
    (v 0) (v 0) (v 3) (v 3) (v 12) (v 7) (v 7) (v 1)
    (rfl) (hp 3) (rfl) (hp 12) (Eq.trans (hq 12) (Eq.symm t2)) (rfl) (hq 7) (hp 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch31 (h0 : v 0 = v 77) : False := by
  have t0 := move_eq p (hp 77) (hp 0) (Eq.symm h0)
  have t1 := move_eq q (hq 131) (hq 1) t0
  exact short4 p q G sep e₀ e₁ e₂ no ![1,2,1,2] (by decide)
    (v 1) (v 5) (v 19) (v 6)
    (hp 1) (hq 19) (Eq.trans (hp 19) t1) (hq 1)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch32 (h0 : v 0 = v 59) : False := by
  have t0 := move_eq p.symm (reverse_move p (hp 19)) (reverse_move p (hp 3)) (Eq.symm h0)
  have t1 := move_eq q (hq 19) (hq 3) t0
  have t2 := move_eq q (hq 11) (hq 5) (Eq.symm t1)
  have t3 := move_eq p (hp 36) (hp 18) t2
  exact short8 p q G sep e₀ e₁ e₂ no ![1,0,2,0,1,2,1,2] (by decide)
    (v 1) (v 5) (v 5) (v 18) (v 18) (v 56) (v 22) (v 6)
    (hp 1) (rfl) (hq 5) (rfl) (hp 18) (Eq.trans (hq 22) t3) (hp 22) (hq 1)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch33 (h0 : v 3 = v 142) : False := by
  have t0 := move_eq q (hq 131) (hq 3) (Eq.symm h0)
  exact short8 p q G sep e₀ e₁ e₂ no ![0,1,2,1,2,1,0,1] (by decide)
    (v 0) (v 0) (v 3) (v 11) (v 19) (v 5) (v 1) (v 1)
    (rfl) (hp 3) (hq 3) (Eq.trans (hp 19) t0) (hq 19) (hp 1) (rfl) (hp 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch34 (h0 : v 3 = v 59) : False := by
  have t0 := move_eq p.symm (reverse_move p (hp 19)) (reverse_move p (hp 12)) (Eq.symm h0)
  have t1 := move_eq q (hq 19) (hq 12) t0
  exact short8 p q G sep e₀ e₁ e₂ no ![0,1,0,1,2,1,0,1] (by decide)
    (v 0) (v 0) (v 3) (v 3) (v 12) (v 5) (v 1) (v 1)
    (rfl) (hp 3) (rfl) (hp 12) (Eq.trans (hq 12) (Eq.symm t1)) (hp 1) (rfl) (hp 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch36 (h0 : v 12 = v 142) (h1 : v 0 = v 64) : False := by
  have t0 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 39)) (Eq.symm h0)
  have t1 := move_eq q.symm (reverse_move q (hq 134)) (reverse_move q (hq 4)) (Eq.symm h1)
  have t2 := move_eq q.symm (reverse_move q (hq 77)) (reverse_move q (hq 16)) t1
  have t3 := move_eq p (hp 39) (hp 16) (Eq.trans (Eq.symm t0) t2)
  have t4 := move_eq p (hp 50) (hp 12) (Eq.symm t3)
  have t5 := move_eq q (hq 73) (hq 3) t4
  have t6 := move_eq p (hp 23) (hp 11) t5
  have t7 := move_eq p (hp 64) (hp 0) (Eq.symm h1)
  have t8 := move_eq q.symm (reverse_move q (hq 71)) (reverse_move q (hq 7)) t7
  exact short4 p q G sep e₀ e₁ e₂ no ![0,1,0,1] (by decide)
    (v 7) (v 7) (v 11) (v 11)
    (rfl) (Eq.trans (hp 11) (Eq.trans (Eq.symm t6) t8)) (rfl) (Eq.trans (hp 7) t5)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch37 (h0 : v 12 = v 142) (h1 : v 3 = v 64) : False := by
  have t0 := move_eq q.symm (reverse_move q (hq 134)) (reverse_move q (hq 13)) (Eq.symm h1)
  have t1 := move_eq q.symm (reverse_move q (hq 77)) (reverse_move q (hq 43)) t0
  have t2 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 39)) (Eq.symm h0)
  have t3 := move_eq q.symm (reverse_move q (hq 115)) (reverse_move q (hq 107)) (Eq.trans (Eq.symm t1) t2)
  have t4 := move_eq p.symm (reverse_move p (hp 129)) (reverse_move p (hp 12)) (Eq.symm h1)
  have t5 := move_eq p.symm (reverse_move p (hp 74)) (reverse_move p (hp 39)) t4
  have t6 := move_eq q.symm (reverse_move q (hq 24)) (reverse_move q (hq 107)) t5
  have t7 := move_eq p.symm (reverse_move p (hp 164)) (reverse_move p (hp 75)) (Eq.trans t3 (Eq.symm t6))
  have t8 := move_eq q (hq 158) (hq 75) t7
  have t9 := move_eq q (hq 131) (hq 12) (Eq.symm h0)
  have t10 := move_eq p (hp 59) (hp 38) t9
  have t11 := move_eq q (hq 64) (hq 3) (Eq.symm h1)
  have t12 := move_eq p.symm (reverse_move p (hp 6)) (reverse_move p (hp 37)) t11
  have t13 := move_eq p.symm (reverse_move p (hp 103)) (reverse_move p (hp 22)) (Eq.symm t12)
  have t14 := move_eq p.symm (reverse_move p (hp 153)) (reverse_move p (hp 69)) t13
  have t15 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 106)) t2
  have t16 := move_eq q (hq 106) (hq 25) (Eq.symm t15)
  have t17 := move_eq p.symm (reverse_move p (hp 59)) (reverse_move p (hp 24)) (Eq.trans (Eq.trans t10 (Eq.symm t14)) t16)
  have t18 := move_eq p.symm (reverse_move p (hp 19)) (reverse_move p (hp 105)) t9
  have t19 := move_eq p.symm (reverse_move p (hp 157)) (reverse_move p (hp 60)) (Eq.symm t18)
  have t20 := move_eq p (hp 20) (hp 11) t11
  have t21 := move_eq q.symm (reverse_move q (hq 130)) (reverse_move q (hq 101)) t20
  have t22 := move_eq q (hq 59) (hq 38) t9
  have t23 := move_eq p (hp 101) (hp 94) (Eq.trans (Eq.symm t21) t22)
  have t24 := move_eq q.symm (reverse_move q (hq 60)) (reverse_move q (hq 10)) t23
  have t25 := move_eq p (hp 157) (hp 10) (Eq.trans t19 t24)
  have t26 := move_eq p (hp 19) (hp 2) (Eq.trans t18 t25)
  have t27 := move_eq p.symm (reverse_move p (hp 75)) (reverse_move p (hp 2)) (Eq.trans (Eq.symm t17) t26)
  have t28 := move_eq q (hq 75) (hq 2) t27
  have t29 := move_eq q (hq 19) (hq 2) (Eq.trans t18 t25)
  have t30 := move_eq q (hq 109) (hq 5) (Eq.trans (Eq.trans t8 t28) (Eq.symm t29))
  have t31 := move_eq p.symm (reverse_move p (hp 40)) (reverse_move p (hp 10)) t27
  have t32 := move_eq q (hq 43) (hq 39) (Eq.trans (Eq.symm t1) t2)
  have t33 := move_eq p (hp 96) (hp 13) (Eq.symm t32)
  have t34 := move_eq q (hq 41) (hq 33) (Eq.symm t33)
  have t35 := move_eq p (hp 153) (hp 7) t16
  have t36 := move_eq p (hp 64) (hp 3) (Eq.symm h1)
  have t37 := move_eq q.symm (reverse_move q (hq 71)) (reverse_move q (hq 4)) t36
  have t38 := move_eq p.symm (reverse_move p (hp 23)) (reverse_move p (hp 15)) t37
  have t39 := move_eq q.symm (reverse_move q (hq 70)) (reverse_move q (hq 49)) (Eq.trans (Eq.trans (Eq.symm t13) t35) t38)
  have t40 := move_eq p (hp 24) (hp 8) (Eq.trans (Eq.symm t17) t26)
  have t41 := move_eq p (hp 26) (hp 7) (Eq.symm t40)
  have t42 := move_eq q.symm (reverse_move q (hq 17)) (reverse_move q (hq 49)) (Eq.trans t41 t38)
  exact short4 p q G sep e₀ e₁ e₂ no ![2,1,2,1] (by decide)
    (v 5) (v 10) (v 33) (v 17)
    (Eq.trans (hq 5) (Eq.trans (Eq.symm t30) t31)) (hp 33) (Eq.trans (hq 33) (Eq.trans (Eq.trans (Eq.symm t34) t39) (Eq.symm t42))) (hp 5)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch38 (h0 : v 12 = v 142) (h1 : v 39 = v 64) : False := by
  have t0 := move_eq q (hq 64) (hq 39) (Eq.symm h1)
  have t1 := move_eq p (hp 96) (hp 20) (Eq.symm t0)
  have t2 := move_eq q.symm (reverse_move q (hq 130)) (reverse_move q (hq 97)) (Eq.symm t1)
  have t3 := move_eq q (hq 131) (hq 12) (Eq.symm h0)
  have t4 := move_eq q (hq 59) (hq 38) t3
  have t5 := move_eq q (hq 97) (hq 94) (Eq.trans (Eq.symm t2) t4)
  have t6 := move_eq p (hp 140) (hp 33) (Eq.symm t5)
  have t7 := move_eq p (hp 89) (hp 10) t6
  have t8 := move_eq q (hq 30) (hq 2) t7
  have t9 := move_eq p (hp 97) (hp 94) (Eq.trans (Eq.symm t2) t4)
  have t10 := move_eq q (hq 47) (hq 32) t9
  have t11 := move_eq q (hq 93) (hq 92) (Eq.symm t10)
  have t12 := move_eq q (hq 96) (hq 20) (Eq.symm t0)
  have t13 := move_eq q.symm (reverse_move q (hq 134)) (reverse_move q (hq 107)) (Eq.symm h1)
  have t14 := move_eq q.symm (reverse_move q (hq 77)) (reverse_move q (hq 155)) t13
  have t15 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 39)) (Eq.symm h0)
  have t16 := move_eq q (hq 155) (hq 39) (Eq.trans (Eq.symm t14) t15)
  have t17 := move_eq q (hq 107) (hq 20) (Eq.trans t16 (Eq.symm t0))
  have t18 := move_eq p (hp 142) (hp 39) (Eq.trans t12 (Eq.symm t17))
  have t19 := move_eq p (hp 91) (hp 12) t18
  have t20 := move_eq p (hp 139) (hp 3) (Eq.trans t11 t19)
  exact short4 p q G sep e₀ e₁ e₂ no ![0,2,0,2] (by decide)
    (v 0) (v 0) (v 2) (v 2)
    (rfl) (Eq.trans (hq 2) (Eq.trans (Eq.symm t8) t20)) (rfl) (hq 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch35 (h0 : v 12 = v 142) : False := by
  have t0 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 39)) (Eq.symm h0)
  have t1 := move_eq q (hq 77) (hq 39) t0
  have t2 := move_eq q (hq 134) (hq 96) t1
  rcases collision16 (fun h => no (.inr (.inr (.inl h))))
    (v 0) (v 0) (v 3) (v 3) (v 12) (v 12) (v 39) (v 96) (v 96) (v 64) (v 64) (v 20) (v 6) (v 6) (v 1) (v 1)
    (e₀ (v 0))
    ((hp 3) ▸ e₁ (v 3))
    (e₀ (v 3))
    ((hp 12) ▸ e₁ (v 12))
    (e₀ (v 12))
    ((hp 39) ▸ e₁ (v 39))
    ((hq 39) ▸ e₂ (v 39))
    (e₀ (v 96))
    ((Eq.trans (hq 96) (Eq.symm t2)) ▸ e₂ (v 96))
    (e₀ (v 64))
    ((hq 64) ▸ e₂ (v 64))
    ((hp 6) ▸ e₁ (v 6))
    (e₀ (v 6))
    ((hq 1) ▸ e₂ (v 1))
    (e₀ (v 1))
    ((hp 0) ▸ e₁ (v 0)) with hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit
  · exact branch1 p q v hp sep hit
  · exact branch2 p q v hp sep G e₀ e₁ e₂ no hit
  · exact branch3 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq q (hq 96) (hq 0) (Eq.symm hit)
    have t1 := move_eq p (hp 142) (hp 2) t0
    have t2 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 39)) (Eq.symm h0)
    have t3 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 4)) (Eq.symm hit)
    have t4 := move_eq q (hq 77) (hq 4) (Eq.trans t2 t3)
    have t5 := move_eq q (hq 134) (hq 0) t4
    have t6 := move_eq p (hp 64) (hp 2) t5
    have t7 := move_eq p (hp 96) (hp 0) (Eq.symm hit)
    have t8 := move_eq q.symm (reverse_move q (hq 97)) (reverse_move q (hq 7)) t7
    have t9 := move_eq p (hp 97) (hp 7) t8
    have t10 := move_eq q.symm (reverse_move q (hq 148)) (reverse_move q (hq 25)) t8
    have t11 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 15)) (Eq.trans t2 t3)
    have t12 := move_eq q (hq 148) (hq 15) (Eq.trans t10 t11)
    have t13 := move_eq p (hp 23) (hp 7) (Eq.trans (Eq.trans (Eq.symm t9) (Eq.symm t12)) t8)
    have t14 := move_eq q (hq 71) (hq 7) (Eq.trans (Eq.trans (Eq.trans t13 (Eq.symm t9)) (Eq.symm t12)) t8)
    have t15 := move_eq p.symm (reverse_move p (hp 142)) (reverse_move p (hp 0)) (Eq.trans (Eq.trans t1 (Eq.symm t6)) t14)
    exact branch8 p q v hq sep (Eq.trans (Eq.symm t15) t0)
  · exact branch36 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · have t0 := move_eq p.symm (reverse_move p (hp 22)) (reverse_move p (hp 3)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 69)) (reverse_move p (hp 12)) t0
    have t2 := move_eq q (hq 69) (hq 12) t1
    have t3 := move_eq q (hq 131) (hq 12) (Eq.symm h0)
    have t4 := move_eq q (hq 59) (hq 38) t3
    have t5 := move_eq p (hp 6) (hp 0) (Eq.symm hit)
    have t6 := move_eq p (hp 20) (hp 1) t5
    have t7 := move_eq q.symm (reverse_move q (hq 130)) (reverse_move q (hq 19)) t6
    have t8 := move_eq p (hp 94) (hp 19) (Eq.trans (Eq.symm t4) t7)
    have t9 := move_eq q.symm (reverse_move q (hq 69)) (reverse_move q (hq 10)) (Eq.trans (Eq.trans t2 (Eq.symm t3)) (Eq.symm t8))
    have t10 := move_eq p (hp 12) (hp 10) (Eq.trans (Eq.symm t1) t9)
    exact branch10 p q v hp hq sep G e₀ e₁ e₂ no t10
  · have t0 := move_eq p.symm (reverse_move p (hp 0)) (reverse_move p (hp 3)) (Eq.symm hit)
    exact branch1 p q v hp sep t0
  · exact branch1 p q v hp sep hit
  · exact branch2 p q v hp sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq q (hq 96) (hq 0) (Eq.symm hit)
    have t1 := move_eq p (hp 142) (hp 2) t0
    have t2 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 39)) (Eq.symm h0)
    have t3 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 4)) (Eq.symm hit)
    have t4 := move_eq q (hq 77) (hq 4) (Eq.trans t2 t3)
    have t5 := move_eq q (hq 134) (hq 0) t4
    have t6 := move_eq p (hp 64) (hp 2) t5
    have t7 := move_eq p (hp 96) (hp 0) (Eq.symm hit)
    have t8 := move_eq q.symm (reverse_move q (hq 97)) (reverse_move q (hq 7)) t7
    have t9 := move_eq p (hp 97) (hp 7) t8
    have t10 := move_eq q.symm (reverse_move q (hq 148)) (reverse_move q (hq 25)) t8
    have t11 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 15)) (Eq.trans t2 t3)
    have t12 := move_eq q (hq 148) (hq 15) (Eq.trans t10 t11)
    have t13 := move_eq p (hp 23) (hp 7) (Eq.trans (Eq.trans (Eq.symm t9) (Eq.symm t12)) t8)
    have t14 := move_eq q (hq 71) (hq 7) (Eq.trans (Eq.trans (Eq.trans t13 (Eq.symm t9)) (Eq.symm t12)) t8)
    have t15 := move_eq p.symm (reverse_move p (hp 142)) (reverse_move p (hp 0)) (Eq.trans (Eq.trans t1 (Eq.symm t6)) t14)
    exact branch8 p q v hq sep (Eq.trans (Eq.symm t15) t0)
  · exact branch36 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · have t0 := move_eq p (hp 20) (hp 0) (Eq.symm hit)
    have t1 := move_eq q (hq 62) (hq 1) t0
    have t2 := move_eq p.symm (reverse_move p (hp 6)) (reverse_move p (hp 3)) (Eq.symm hit)
    have t3 := move_eq q.symm (reverse_move q (hq 62)) (reverse_move q (hq 13)) (Eq.trans t1 t2)
    have t4 := move_eq p.symm (reverse_move p (hp 42)) (reverse_move p (hp 0)) (Eq.trans (Eq.symm t3) t0)
    exact branch26 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t4)
  · have t0 := move_eq p.symm (reverse_move p (hp 22)) (reverse_move p (hp 3)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 69)) (reverse_move p (hp 12)) t0
    have t2 := move_eq q (hq 69) (hq 12) t1
    have t3 := move_eq q (hq 131) (hq 12) (Eq.symm h0)
    have t4 := move_eq q (hq 59) (hq 38) t3
    have t5 := move_eq p (hp 6) (hp 0) (Eq.symm hit)
    have t6 := move_eq p (hp 20) (hp 1) t5
    have t7 := move_eq q.symm (reverse_move q (hq 130)) (reverse_move q (hq 19)) t6
    have t8 := move_eq p (hp 94) (hp 19) (Eq.trans (Eq.symm t4) t7)
    have t9 := move_eq q.symm (reverse_move q (hq 69)) (reverse_move q (hq 10)) (Eq.trans (Eq.trans t2 (Eq.symm t3)) (Eq.symm t8))
    have t10 := move_eq p (hp 12) (hp 10) (Eq.trans (Eq.symm t1) t9)
    exact branch10 p q v hp hq sep G e₀ e₁ e₂ no t10
  · have t0 := move_eq p.symm (reverse_move p (hp 0)) (reverse_move p (hp 3)) (Eq.symm hit)
    exact branch1 p q v hp sep t0
  · exact branch33 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans hit h0)
  · have t0 := move_eq p (hp 39) (hp 3) (Eq.symm hit)
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 13)) (Eq.symm hit)
    have t1 := move_eq p (hp 39) (hp 13) t0
    have t2 := move_eq p (hp 41) (hp 12) (Eq.symm t1)
    have t3 := move_eq p (hp 60) (hp 3) t2
    exact branch29 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t3)
  · exact branch37 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · have t0 := move_eq q.symm (reverse_move q (hq 1)) (reverse_move q (hq 13)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 42)) (reverse_move p (hp 0)) (Eq.symm t0)
    exact branch26 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p.symm (reverse_move p (hp 12)) (reverse_move p (hp 0)) hit
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t0)
  · exact branch33 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans hit h0)
  · have t0 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 13)) (Eq.symm hit)
    have t1 := move_eq p (hp 39) (hp 13) t0
    have t2 := move_eq p (hp 41) (hp 12) (Eq.symm t1)
    have t3 := move_eq p (hp 60) (hp 3) t2
    exact branch29 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t3)
  · exact branch37 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · have t0 := move_eq p.symm (reverse_move p (hp 6)) (reverse_move p (hp 12)) (Eq.symm hit)
    have t1 := move_eq q (hq 131) (hq 6) (Eq.trans (Eq.symm h0) (Eq.symm t0))
    have t2 := move_eq p (hp 20) (hp 3) (Eq.symm hit)
    have t3 := move_eq q.symm (reverse_move q (hq 130)) (reverse_move q (hq 4)) t2
    have t4 := move_eq q.symm (reverse_move q (hq 59)) (reverse_move q (hq 16)) t3
    have t5 := move_eq p.symm (reverse_move p (hp 67)) (reverse_move p (hp 51)) (Eq.trans (Eq.symm t1) t4)
    have t6 := move_eq p.symm (reverse_move p (hp 19)) (reverse_move p (hp 51)) t4
    have t7 := move_eq q.symm (reverse_move q (hq 135)) (reverse_move q (hq 61)) (Eq.trans t5 (Eq.symm t6))
    have t8 := move_eq q.symm (reverse_move q (hq 6)) (reverse_move q (hq 52)) (Eq.trans (Eq.symm t1) t4)
    have t9 := move_eq p (hp 52) (hp 6) (Eq.symm t8)
    have t10 := move_eq p (hp 79) (hp 3) (Eq.trans t9 (Eq.symm hit))
    have t11 := move_eq q (hq 133) (hq 0) t10
    have t12 := move_eq q.symm (reverse_move q (hq 74)) (reverse_move q (hq 0)) (Eq.trans t7 t11)
    have t13 := move_eq q.symm (reverse_move q (hq 64)) (reverse_move q (hq 13)) (Eq.symm hit)
    have t14 := move_eq p.symm (reverse_move p (hp 129)) (reverse_move p (hp 42)) t13
    have t15 := move_eq p.symm (reverse_move p (hp 74)) (reverse_move p (hp 111)) t14
    exact branch25 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t12) t15)
  · have t0 := move_eq q.symm (reverse_move q (hq 1)) (reverse_move q (hq 13)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 42)) (reverse_move p (hp 0)) (Eq.symm t0)
    exact branch26 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p.symm (reverse_move p (hp 12)) (reverse_move p (hp 0)) hit
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 39) (hp 12) (Eq.symm hit)
    exact branch33 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t0) h0)
  · have t0 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 40)) (Eq.symm hit)
    have t1 := move_eq p (hp 40) (hp 39) (Eq.symm t0)
    have t2 := move_eq p (hp 75) (hp 12) t1
    have t3 := move_eq p (hp 24) (hp 3) t2
    exact branch4 p q v hp hq sep (Eq.symm t3)
  · have t0 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 39)) (Eq.symm h0)
    have t1 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 106)) t0
    have t2 := move_eq p.symm (reverse_move p (hp 158)) (reverse_move p (hp 78)) (Eq.symm t1)
    have t3 := move_eq q.symm (reverse_move q (hq 134)) (reverse_move q (hq 40)) (Eq.symm hit)
    have t4 := move_eq q.symm (reverse_move q (hq 77)) (reverse_move q (hq 109)) t3
    have t5 := move_eq p (hp 109) (hp 39) (Eq.trans (Eq.symm t4) t0)
    have t6 := move_eq p (hp 134) (hp 12) t5
    have t7 := move_eq p (hp 158) (hp 3) (Eq.trans t2 t6)
    exact branch16 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t7)
  · have t0 := move_eq q (hq 131) (hq 6) (Eq.trans (Eq.symm h0) hit)
    have t1 := move_eq p (hp 12) (hp 6) hit
    have t2 := move_eq p (hp 20) (hp 3) (Eq.symm t1)
    have t3 := move_eq q.symm (reverse_move q (hq 130)) (reverse_move q (hq 4)) t2
    have t4 := move_eq q.symm (reverse_move q (hq 59)) (reverse_move q (hq 16)) t3
    have t5 := move_eq q.symm (reverse_move q (hq 6)) (reverse_move q (hq 52)) (Eq.trans (Eq.symm t0) t4)
    have t6 := move_eq p (hp 52) (hp 6) (Eq.symm t5)
    have t7 := move_eq p (hp 79) (hp 3) (Eq.trans t6 (Eq.symm t1))
    have t8 := move_eq q (hq 12) (hq 6) hit
    have t9 := move_eq p (hp 38) (hp 21) t8
    have t10 := move_eq q.symm (reverse_move q (hq 136)) (reverse_move q (hq 26)) t9
    have t11 := move_eq p (hp 130) (hp 26) t10
    have t12 := move_eq q (hq 74) (hq 54) t11
    have t13 := move_eq p.symm (reverse_move p (hp 67)) (reverse_move p (hp 51)) (Eq.trans (Eq.symm t0) t4)
    have t14 := move_eq q.symm (reverse_move q (hq 40)) (reverse_move q (hq 1)) hit
    have t15 := move_eq p (hp 40) (hp 1) t14
    have t16 := move_eq q.symm (reverse_move q (hq 51)) (reverse_move q (hq 19)) t15
    have t17 := move_eq q.symm (reverse_move q (hq 135)) (reverse_move q (hq 61)) (Eq.trans t13 t16)
    have t18 := move_eq q.symm (reverse_move q (hq 54)) (reverse_move q (hq 133)) (Eq.trans (Eq.symm t12) t17)
    have t19 := move_eq q.symm (reverse_move q (hq 64)) (reverse_move q (hq 13)) (Eq.symm t1)
    have t20 := move_eq p.symm (reverse_move p (hp 129)) (reverse_move p (hp 42)) t19
    have t21 := move_eq p.symm (reverse_move p (hp 74)) (reverse_move p (hp 111)) t20
    exact branch25 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.trans (Eq.trans (Eq.symm t7) (Eq.symm t18)) (Eq.symm t11)) t21)
  · have t0 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 0)) hit
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 40)) (Eq.symm hit)
    have t1 := move_eq p (hp 40) (hp 39) (Eq.symm t0)
    have t2 := move_eq p (hp 75) (hp 12) t1
    have t3 := move_eq p (hp 24) (hp 3) t2
    exact branch4 p q v hp hq sep (Eq.symm t3)
  · have t0 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 39)) (Eq.symm h0)
    have t1 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 106)) t0
    have t2 := move_eq p.symm (reverse_move p (hp 158)) (reverse_move p (hp 78)) (Eq.symm t1)
    have t3 := move_eq q.symm (reverse_move q (hq 134)) (reverse_move q (hq 40)) (Eq.symm hit)
    have t4 := move_eq q.symm (reverse_move q (hq 77)) (reverse_move q (hq 109)) t3
    have t5 := move_eq p (hp 109) (hp 39) (Eq.trans (Eq.symm t4) t0)
    have t6 := move_eq p (hp 134) (hp 12) t5
    have t7 := move_eq p (hp 158) (hp 3) (Eq.trans t2 t6)
    exact branch16 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t7)
  · have t0 := move_eq q.symm (reverse_move q (hq 64)) (reverse_move q (hq 40)) (Eq.symm hit)
    have t1 := move_eq q.symm (reverse_move q (hq 134)) (reverse_move q (hq 109)) t0
    have t2 := move_eq q.symm (reverse_move q (hq 77)) (reverse_move q (hq 158)) t1
    have t3 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 39)) (Eq.symm h0)
    have t4 := move_eq p.symm (reverse_move p (hp 6)) (reverse_move p (hp 39)) (Eq.symm hit)
    have t5 := move_eq p (hp 164) (hp 6) (Eq.trans (Eq.trans (Eq.symm t2) t3) (Eq.symm t4))
    have t6 := move_eq p (hp 115) (hp 12) (Eq.trans t5 (Eq.symm hit))
    have t7 := move_eq p (hp 52) (hp 3) t6
    have t8 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 22)) (Eq.trans t3 (Eq.symm t4))
    have t9 := move_eq q.symm (reverse_move q (hq 79)) (reverse_move q (hq 70)) t8
    have t10 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 22)) (Eq.symm t4)
    have t11 := move_eq q.symm (reverse_move q (hq 154)) (reverse_move q (hq 70)) t10
    exact branch17 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.trans (Eq.symm t7) t9) (Eq.symm t11))
  · have t0 := move_eq q (hq 131) (hq 6) (Eq.trans (Eq.symm h0) hit)
    have t1 := move_eq p (hp 12) (hp 6) hit
    have t2 := move_eq p (hp 20) (hp 3) (Eq.symm t1)
    have t3 := move_eq q.symm (reverse_move q (hq 130)) (reverse_move q (hq 4)) t2
    have t4 := move_eq q.symm (reverse_move q (hq 59)) (reverse_move q (hq 16)) t3
    have t5 := move_eq q.symm (reverse_move q (hq 6)) (reverse_move q (hq 52)) (Eq.trans (Eq.symm t0) t4)
    have t6 := move_eq p (hp 52) (hp 6) (Eq.symm t5)
    have t7 := move_eq p (hp 79) (hp 3) (Eq.trans t6 (Eq.symm t1))
    have t8 := move_eq q (hq 12) (hq 6) hit
    have t9 := move_eq p (hp 38) (hp 21) t8
    have t10 := move_eq q.symm (reverse_move q (hq 136)) (reverse_move q (hq 26)) t9
    have t11 := move_eq p (hp 130) (hp 26) t10
    have t12 := move_eq q (hq 74) (hq 54) t11
    have t13 := move_eq p.symm (reverse_move p (hp 67)) (reverse_move p (hp 51)) (Eq.trans (Eq.symm t0) t4)
    have t14 := move_eq q.symm (reverse_move q (hq 40)) (reverse_move q (hq 1)) hit
    have t15 := move_eq p (hp 40) (hp 1) t14
    have t16 := move_eq q.symm (reverse_move q (hq 51)) (reverse_move q (hq 19)) t15
    have t17 := move_eq q.symm (reverse_move q (hq 135)) (reverse_move q (hq 61)) (Eq.trans t13 t16)
    have t18 := move_eq q.symm (reverse_move q (hq 54)) (reverse_move q (hq 133)) (Eq.trans (Eq.symm t12) t17)
    have t19 := move_eq q.symm (reverse_move q (hq 64)) (reverse_move q (hq 13)) (Eq.symm t1)
    have t20 := move_eq p.symm (reverse_move p (hp 129)) (reverse_move p (hp 42)) t19
    have t21 := move_eq p.symm (reverse_move p (hp 74)) (reverse_move p (hp 111)) t20
    exact branch25 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.trans (Eq.trans (Eq.symm t7) (Eq.symm t18)) (Eq.symm t11)) t21)
  · have t0 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 0)) hit
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 96) (hp 39) (Eq.symm hit)
    have t1 := move_eq p (hp 33) (hp 12) t0
    have t2 := move_eq p (hp 10) (hp 3) t1
    exact branch8 p q v hq sep (Eq.symm t2)
  · exact branch38 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · have t0 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 22)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 39)) (Eq.symm h0)
    have t2 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 22)) (Eq.trans t1 hit)
    have t3 := move_eq p.symm (reverse_move p (hp 78)) (reverse_move p (hp 69)) t2
    have t4 := move_eq p (hp 39) (hp 6) hit
    have t5 := move_eq q.symm (reverse_move q (hq 64)) (reverse_move q (hq 40)) (Eq.symm t4)
    have t6 := move_eq q.symm (reverse_move q (hq 134)) (reverse_move q (hq 109)) t5
    have t7 := move_eq q (hq 77) (hq 6) (Eq.trans t1 hit)
    have t8 := move_eq p (hp 109) (hp 21) (Eq.trans (Eq.symm t6) t7)
    have t9 := move_eq q (hq 39) (hq 6) hit
    have t10 := move_eq p (hp 96) (hp 21) t9
    have t11 := move_eq p (hp 134) (hp 33) (Eq.trans t8 (Eq.symm t10))
    have t12 := move_eq p (hp 69) (hp 10) (Eq.trans (Eq.symm t3) t11)
    have t13 := move_eq q.symm (reverse_move q (hq 154)) (reverse_move q (hq 0)) (Eq.trans t0 t12)
    exact branch17 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t13)
  · have t0 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 0)) hit
    exact branch16 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 134)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 39)) (Eq.symm h0)
    have t2 := move_eq q (hq 77) (hq 39) t1
    exact branch38 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.trans (Eq.trans t0 t2) hit)
  · have t0 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 64)) hit
    exact branch38 p q v hp hq sep G e₀ e₁ e₂ no h0 t0
  · have t0 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 1)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 0)) t0
    exact branch16 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq q (hq 96) (hq 1) hit
    have t1 := move_eq p (hp 142) (hp 6) t0
    have t2 := move_eq q.symm (reverse_move q (hq 37)) (reverse_move q (hq 64)) t1
    have t3 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 39)) (Eq.symm h0)
    have t4 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 7)) hit
    have t5 := move_eq q (hq 77) (hq 7) (Eq.trans t3 t4)
    have t6 := move_eq q (hq 134) (hq 1) t5
    have t7 := move_eq p (hp 37) (hp 6) (Eq.trans t2 t6)
    have t8 := move_eq q.symm (reverse_move q (hq 37)) (reverse_move q (hq 3)) (Eq.trans t1 (Eq.symm t7))
    exact branch37 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.trans (Eq.symm t8) t2)
  · have t0 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 134)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 39)) (Eq.symm h0)
    have t2 := move_eq q (hq 77) (hq 39) t1
    exact branch38 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.trans (Eq.trans t0 t2) hit)
  · have t0 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 1)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 0)) t0
    exact branch16 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq q (hq 96) (hq 1) hit
    have t1 := move_eq p (hp 142) (hp 6) t0
    have t2 := move_eq q.symm (reverse_move q (hq 37)) (reverse_move q (hq 64)) t1
    have t3 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 39)) (Eq.symm h0)
    have t4 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 7)) hit
    have t5 := move_eq q (hq 77) (hq 7) (Eq.trans t3 t4)
    have t6 := move_eq q (hq 134) (hq 1) t5
    have t7 := move_eq p (hp 37) (hp 6) (Eq.trans t2 t6)
    have t8 := move_eq q.symm (reverse_move q (hq 37)) (reverse_move q (hq 3)) (Eq.trans t1 (Eq.symm t7))
    exact branch37 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.trans (Eq.symm t8) t2)
  · have t0 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 39)) (Eq.symm h0)
    have t1 := move_eq q.symm (reverse_move q (hq 134)) (reverse_move q (hq 64)) hit
    have t2 := move_eq q.symm (reverse_move q (hq 77)) (reverse_move q (hq 64)) (Eq.trans t1 hit)
    exact branch38 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.trans (Eq.symm t0) t2)
  · have t0 := move_eq p.symm (reverse_move p (hp 129)) (reverse_move p (hp 22)) hit
    have t1 := move_eq p (hp 64) (hp 6) hit
    have t2 := move_eq q.symm (reverse_move q (hq 71)) (reverse_move q (hq 64)) t1
    have t3 := move_eq p.symm (reverse_move p (hp 23)) (reverse_move p (hp 22)) (Eq.trans t2 hit)
    have t4 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 39)) (Eq.symm h0)
    have t5 := move_eq q.symm (reverse_move q (hq 134)) (reverse_move q (hq 1)) hit
    have t6 := move_eq q.symm (reverse_move q (hq 77)) (reverse_move q (hq 7)) t5
    have t7 := move_eq p (hp 39) (hp 7) (Eq.trans (Eq.symm t4) t6)
    have t8 := move_eq p (hp 129) (hp 12) (Eq.trans (Eq.trans t0 (Eq.symm t3)) (Eq.symm t7))
    exact branch37 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.symm t8)
  · have t0 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 39)) (Eq.symm h0)
    have t1 := move_eq q.symm (reverse_move q (hq 134)) (reverse_move q (hq 7)) hit
    have t2 := move_eq q.symm (reverse_move q (hq 77)) (reverse_move q (hq 25)) t1
    have t3 := move_eq p (hp 39) (hp 25) (Eq.trans (Eq.symm t0) t2)
    have t4 := move_eq p.symm (reverse_move p (hp 129)) (reverse_move p (hp 0)) hit
    have t5 := move_eq p.symm (reverse_move p (hp 74)) (reverse_move p (hp 3)) t4
    have t6 := move_eq p.symm (reverse_move p (hp 130)) (reverse_move p (hp 12)) t5
    have t7 := move_eq q (hq 64) (hq 1) hit
    have t8 := move_eq p.symm (reverse_move p (hp 6)) (reverse_move p (hp 22)) t7
    have t9 := move_eq p.symm (reverse_move p (hp 69)) (reverse_move p (hp 22)) (Eq.symm t8)
    have t10 := move_eq q.symm (reverse_move q (hq 136)) (reverse_move q (hq 1)) (Eq.trans t9 (Eq.symm t8))
    exact branch38 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.trans (Eq.trans (Eq.trans (Eq.trans (Eq.symm t0) (Eq.symm t3)) (Eq.symm t6)) t10) (Eq.symm hit))
  · have t0 := move_eq p.symm (reverse_move p (hp 129)) (reverse_move p (hp 22)) hit
    have t1 := move_eq p (hp 64) (hp 6) hit
    have t2 := move_eq q.symm (reverse_move q (hq 71)) (reverse_move q (hq 64)) t1
    have t3 := move_eq p.symm (reverse_move p (hp 23)) (reverse_move p (hp 22)) (Eq.trans t2 hit)
    have t4 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 39)) (Eq.symm h0)
    have t5 := move_eq q.symm (reverse_move q (hq 134)) (reverse_move q (hq 1)) hit
    have t6 := move_eq q.symm (reverse_move q (hq 77)) (reverse_move q (hq 7)) t5
    have t7 := move_eq p (hp 39) (hp 7) (Eq.trans (Eq.symm t4) t6)
    have t8 := move_eq p (hp 129) (hp 12) (Eq.trans (Eq.trans t0 (Eq.symm t3)) (Eq.symm t7))
    exact branch37 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.symm t8)
  · have t0 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 39)) (Eq.symm h0)
    have t1 := move_eq q.symm (reverse_move q (hq 134)) (reverse_move q (hq 7)) hit
    have t2 := move_eq q.symm (reverse_move q (hq 77)) (reverse_move q (hq 25)) t1
    have t3 := move_eq p (hp 39) (hp 25) (Eq.trans (Eq.symm t0) t2)
    have t4 := move_eq p.symm (reverse_move p (hp 129)) (reverse_move p (hp 0)) hit
    have t5 := move_eq p.symm (reverse_move p (hp 74)) (reverse_move p (hp 3)) t4
    have t6 := move_eq p.symm (reverse_move p (hp 130)) (reverse_move p (hp 12)) t5
    have t7 := move_eq q (hq 64) (hq 1) hit
    have t8 := move_eq p.symm (reverse_move p (hp 6)) (reverse_move p (hp 22)) t7
    have t9 := move_eq p.symm (reverse_move p (hp 69)) (reverse_move p (hp 22)) (Eq.symm t8)
    have t10 := move_eq q.symm (reverse_move q (hq 136)) (reverse_move q (hq 1)) (Eq.trans t9 (Eq.symm t8))
    exact branch38 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.trans (Eq.trans (Eq.trans (Eq.trans (Eq.symm t0) (Eq.symm t3)) (Eq.symm t6)) t10) (Eq.symm hit))
  · have t0 := move_eq p.symm (reverse_move p (hp 6)) (reverse_move p (hp 22)) hit
    have t1 := move_eq q.symm (reverse_move q (hq 70)) (reverse_move q (hq 1)) (Eq.symm t0)
    have t2 := move_eq p (hp 70) (hp 1) t1
    have t3 := move_eq p.symm (reverse_move p (hp 69)) (reverse_move p (hp 22)) (Eq.symm t0)
    have t4 := move_eq q.symm (reverse_move q (hq 136)) (reverse_move q (hq 1)) (Eq.trans t3 (Eq.symm t0))
    have t5 := move_eq p (hp 130) (hp 1) t4
    have t6 := move_eq q.symm (reverse_move q (hq 64)) (reverse_move q (hq 1)) hit
    have t7 := move_eq p.symm (reverse_move p (hp 129)) (reverse_move p (hp 0)) t6
    have t8 := move_eq p.symm (reverse_move p (hp 74)) (reverse_move p (hp 3)) t7
    have t9 := move_eq p.symm (reverse_move p (hp 70)) (reverse_move p (hp 12)) (Eq.trans (Eq.trans t2 (Eq.symm t5)) t8)
    have t10 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 0)) (Eq.trans (Eq.symm t9) t1)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t10)
  · have t0 := move_eq p.symm (reverse_move p (hp 6)) (reverse_move p (hp 0)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 22)) (reverse_move p (hp 3)) t0
    have t2 := move_eq p.symm (reverse_move p (hp 69)) (reverse_move p (hp 12)) t1
    have t3 := move_eq q (hq 69) (hq 12) t2
    have t4 := move_eq q (hq 131) (hq 12) (Eq.symm h0)
    have t5 := move_eq q (hq 59) (hq 38) t4
    have t6 := move_eq p (hp 20) (hp 1) hit
    have t7 := move_eq q.symm (reverse_move q (hq 130)) (reverse_move q (hq 19)) t6
    have t8 := move_eq p (hp 94) (hp 19) (Eq.trans (Eq.symm t5) t7)
    have t9 := move_eq q.symm (reverse_move q (hq 69)) (reverse_move q (hq 10)) (Eq.trans (Eq.trans t3 (Eq.symm t4)) (Eq.symm t8))
    have t10 := move_eq p (hp 12) (hp 10) (Eq.trans (Eq.symm t2) t9)
    exact branch10 p q v hp hq sep G e₀ e₁ e₂ no t10
  · have t0 := move_eq q.symm (reverse_move q (hq 1)) (reverse_move q (hq 7)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 24)) (reverse_move p (hp 0)) (Eq.symm t0)
    exact branch5 p q v hp hq sep (Eq.symm t1)
  · have t0 := move_eq q.symm (reverse_move q (hq 1)) (reverse_move q (hq 7)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 24)) (reverse_move p (hp 0)) (Eq.symm t0)
    exact branch5 p q v hp hq sep (Eq.symm t1)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch39 (h0 : v 12 = v 7) : False := by
  have t0 := move_eq q (hq 12) (hq 7) h0
  have t1 := move_eq q (hq 38) (hq 1) t0
  have t2 := move_eq p (hp 94) (hp 6) t1
  exact short8 p q G sep e₀ e₁ e₂ no ![1,0,2,0,1,2,1,2] (by decide)
    (v 0) (v 1) (v 1) (v 6) (v 6) (v 20) (v 10) (v 2)
    (hp 0) (rfl) (hq 1) (rfl) (hp 6) (Eq.trans (hq 10) t2) (hp 10) (hq 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch41 (h0 : v 12 = v 59) (h1 : v 0 = v 29) : False := by
  have t0 := move_eq q (hq 29) (hq 0) (Eq.symm h1)
  have t1 := move_eq q (hq 87) (hq 2) t0
  have t2 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 3)) (Eq.symm h1)
  have t3 := move_eq q.symm (reverse_move q (hq 87)) (reverse_move q (hq 13)) (Eq.trans t1 t2)
  have t4 := move_eq p.symm (reverse_move p (hp 42)) (reverse_move p (hp 10)) (Eq.trans (Eq.symm t3) t0)
  have t5 := move_eq q (hq 42) (hq 10) t4
  have t6 := move_eq q (hq 110) (hq 32) t5
  have t7 := move_eq q (hq 9) (hq 3) t2
  have t8 := move_eq q (hq 30) (hq 11) t7
  have t9 := move_eq p.symm (reverse_move p (hp 139)) (reverse_move p (hp 102)) t8
  have t10 := move_eq q.symm (reverse_move q (hq 58)) (reverse_move q (hq 4)) (Eq.symm h1)
  have t11 := move_eq p (hp 58) (hp 4) t10
  have t12 := move_eq p (hp 18) (hp 14) t11
  have t13 := move_eq p (hp 56) (hp 44) t12
  have t14 := move_eq p.symm (reverse_move p (hp 89)) (reverse_move p (hp 37)) t7
  have t15 := move_eq p.symm (reverse_move p (hp 35)) (reverse_move p (hp 15)) t10
  have t16 := move_eq p.symm (reverse_move p (hp 11)) (reverse_move p (hp 48)) t15
  have t17 := move_eq p.symm (reverse_move p (hp 107)) (reverse_move p (hp 37)) (Eq.symm t16)
  have t18 := move_eq p.symm (reverse_move p (hp 19)) (reverse_move p (hp 39)) (Eq.symm h0)
  have t19 := move_eq q.symm (reverse_move q (hq 107)) (reverse_move q (hq 61)) (Eq.symm t18)
  have t20 := move_eq q.symm (reverse_move q (hq 5)) (reverse_move q (hq 46)) t11
  have t21 := move_eq p (hp 46) (hp 5) (Eq.symm t20)
  have t22 := move_eq q.symm (reverse_move q (hq 36)) (reverse_move q (hq 55)) (Eq.trans (Eq.trans (Eq.trans t14 (Eq.symm t17)) t19) t21)
  have t23 := move_eq p.symm (reverse_move p (hp 56)) (reverse_move p (hp 102)) (Eq.trans t13 (Eq.symm t22))
  have t24 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 60)) (Eq.symm t18)
  have t25 := move_eq p.symm (reverse_move p (hp 31)) (reverse_move p (hp 12)) t2
  have t26 := move_eq p.symm (reverse_move p (hp 91)) (reverse_move p (hp 39)) t25
  have t27 := move_eq p.symm (reverse_move p (hp 142)) (reverse_move p (hp 60)) (Eq.trans t26 (Eq.symm t18))
  have t28 := move_eq q (hq 39) (hq 19) (Eq.symm t18)
  have t29 := move_eq q (hq 96) (hq 5) t28
  have t30 := move_eq p (hp 106) (hp 14) (Eq.trans (Eq.trans (Eq.trans t24 (Eq.symm t27)) t29) t11)
  have t31 := move_eq q.symm (reverse_move q (hq 93)) (reverse_move q (hq 61)) (Eq.trans (Eq.trans (Eq.trans (Eq.trans t9 (Eq.symm t23)) t12) (Eq.symm t30)) (Eq.symm t18))
  have t32 := move_eq q.symm (reverse_move q (hq 110)) (reverse_move q (hq 55)) (Eq.trans (Eq.trans t6 t31) t21)
  have t33 := move_eq p (hp 139) (hp 19) (Eq.trans (Eq.trans (Eq.trans (Eq.trans t9 (Eq.symm t23)) t12) (Eq.symm t30)) (Eq.symm t18))
  exact short8 p q G sep e₀ e₁ e₂ no ![0,1,0,1,0,2,1,2] (by decide)
    (v 0) (v 0) (v 3) (v 3) (v 12) (v 12) (v 10) (v 2)
    (rfl) (hp 3) (rfl) (hp 12) (rfl) (Eq.trans (hq 10) (Eq.trans (Eq.trans (Eq.trans (Eq.trans (Eq.trans (Eq.symm t5) t32) (Eq.symm t22)) (Eq.symm t8)) t33) (Eq.symm h0))) (hp 10) (hq 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch42 (h1 : v 3 = v 29) : False := by
  exact short8 p q G sep e₀ e₁ e₂ no ![0,1,0,1,0,2,0,2] (by decide)
    (v 0) (v 0) (v 3) (v 3) (v 9) (v 9) (v 2) (v 2)
    (rfl) (hp 3) (rfl) (Eq.trans (hp 9) (Eq.symm h1)) (rfl) (hq 2) (rfl) (hq 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch43 (h0 : v 12 = v 59) (h1 : v 12 = v 29) : False := by
  have t0 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 39)) (Eq.symm h1)
  have t1 := move_eq q (hq 39) (hq 9) (Eq.symm t0)
  have t2 := move_eq p (hp 96) (hp 30) t1
  have t3 := move_eq p.symm (reverse_move p (hp 19)) (reverse_move p (hp 39)) (Eq.symm h0)
  have t4 := move_eq q (hq 19) (hq 9) (Eq.trans t3 (Eq.symm t0))
  have t5 := move_eq p (hp 30) (hp 5) (Eq.symm t4)
  have t6 := move_eq p (hp 33) (hp 17) (Eq.trans t2 t5)
  have t7 := move_eq q.symm (reverse_move q (hq 127)) (reverse_move q (hq 34)) (Eq.symm t6)
  have t8 := move_eq q.symm (reverse_move q (hq 58)) (reverse_move q (hq 40)) (Eq.symm h1)
  have t9 := move_eq p (hp 58) (hp 40) t8
  have t10 := move_eq q (hq 75) (hq 18) (Eq.symm t9)
  have t11 := move_eq p (hp 57) (hp 34) (Eq.symm t10)
  have t12 := move_eq q (hq 59) (hq 12) (Eq.symm h0)
  have t13 := move_eq q (hq 130) (hq 38) t12
  have t14 := move_eq q (hq 94) (hq 62) (Eq.symm t13)
  have t15 := move_eq p.symm (reverse_move p (hp 89)) (reverse_move p (hp 1)) (Eq.symm t4)
  have t16 := move_eq p.symm (reverse_move p (hp 140)) (reverse_move p (hp 0)) t15
  have t17 := move_eq p.symm (reverse_move p (hp 34)) (reverse_move p (hp 3)) (Eq.trans (Eq.trans (Eq.symm t11) (Eq.symm t14)) t16)
  have t18 := move_eq q (hq 127) (hq 3) (Eq.trans t7 t17)
  have t19 := move_eq p.symm (reverse_move p (hp 60)) (reverse_move p (hp 31)) (Eq.trans t3 (Eq.symm t0))
  have t20 := move_eq q.symm (reverse_move q (hq 132)) (reverse_move q (hq 92)) t19
  have t21 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 31)) (Eq.symm t0)
  have t22 := move_eq q.symm (reverse_move q (hq 154)) (reverse_move q (hq 92)) t21
  have t23 := move_eq q (hq 96) (hq 30) t1
  have t24 := move_eq p (hp 142) (hp 88) t23
  have t25 := move_eq q (hq 30) (hq 5) (Eq.symm t4)
  have t26 := move_eq p (hp 88) (hp 18) t25
  have t27 := move_eq p (hp 75) (hp 18) (Eq.symm t9)
  have t28 := move_eq p (hp 91) (hp 24) (Eq.trans (Eq.trans t24 t26) (Eq.symm t27))
  have t29 := move_eq q.symm (reverse_move q (hq 154)) (reverse_move q (hq 25)) (Eq.trans t21 t28)
  have t30 := move_eq q.symm (reverse_move q (hq 131)) (reverse_move q (hq 40)) (Eq.symm h0)
  have t31 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 108)) t30
  have t32 := move_eq p.symm (reverse_move p (hp 35)) (reverse_move p (hp 108)) t8
  have t33 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 11)) (Eq.trans t31 (Eq.symm t32))
  have t34 := move_eq q (hq 132) (hq 10) (Eq.trans (Eq.trans (Eq.trans (Eq.trans (Eq.trans t20 (Eq.symm t22)) t29) t33) (Eq.symm t18)) (Eq.symm t6))
  exact short8 p q G sep e₀ e₁ e₂ no ![0,1,2,0,2,0,2,1] (by decide)
    (v 0) (v 0) (v 3) (v 10) (v 10) (v 7) (v 7) (v 1)
    (rfl) (hp 3) (Eq.trans (hq 3) (Eq.trans (Eq.symm t18) (Eq.symm t6))) (rfl) (Eq.trans (hq 10) (Eq.trans (Eq.trans (Eq.symm t34) t19) t28)) (rfl) (hq 7) (hp 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch40 (h0 : v 12 = v 59) : False := by
  rcases collision16 (fun h => no (.inr (.inr (.inl h))))
    (v 0) (v 0) (v 3) (v 3) (v 12) (v 12) (v 19) (v 5) (v 5) (v 18) (v 58) (v 29) (v 9) (v 9) (v 2) (v 2)
    (e₀ (v 0))
    ((hp 3) ▸ e₁ (v 3))
    (e₀ (v 3))
    ((hp 12) ▸ e₁ (v 12))
    (e₀ (v 12))
    ((Eq.trans (hp 19) (Eq.symm h0)) ▸ e₁ (v 19))
    ((hq 19) ▸ e₂ (v 19))
    (e₀ (v 5))
    ((hq 5) ▸ e₂ (v 5))
    ((hp 58) ▸ e₁ (v 58))
    ((hq 58) ▸ e₂ (v 58))
    ((hp 9) ▸ e₁ (v 9))
    (e₀ (v 9))
    ((hq 2) ▸ e₂ (v 2))
    (e₀ (v 2))
    ((hq 0) ▸ e₂ (v 0)) with hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit
  · exact branch1 p q v hp sep hit
  · exact branch2 p q v hp sep G e₀ e₁ e₂ no hit
  · exact branch29 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p (hp 59) (hp 12) (Eq.symm h0)
    have t1 := move_eq p.symm (reverse_move p (hp 1)) (reverse_move p (hp 3)) (Eq.symm hit)
    have t2 := move_eq p.symm (reverse_move p (hp 59)) (reverse_move p (hp 0)) (Eq.trans t0 (Eq.symm t1))
    exact branch32 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq p.symm (reverse_move p (hp 35)) (reverse_move p (hp 3)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 11)) (reverse_move p (hp 12)) t0
    have t2 := move_eq q.symm (reverse_move q (hq 131)) (reverse_move q (hq 3)) (Eq.trans (Eq.symm h0) (Eq.symm t1))
    exact branch33 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq p (hp 9) (hp 0) (Eq.symm hit)
    have t1 := move_eq q.symm (reverse_move q (hq 58)) (reverse_move q (hq 7)) t0
    have t2 := move_eq q (hq 9) (hq 0) (Eq.symm hit)
    have t3 := move_eq p (hp 30) (hp 2) t2
    have t4 := move_eq p (hp 66) (hp 8) t3
    have t5 := move_eq q.symm (reverse_move q (hq 21)) (reverse_move q (hq 28)) t3
    have t6 := move_eq p (hp 28) (hp 21) (Eq.symm t5)
    have t7 := move_eq p (hp 29) (hp 1) t0
    have t8 := move_eq q.symm (reverse_move q (hq 145)) (reverse_move q (hq 19)) t7
    have t9 := move_eq q.symm (reverse_move q (hq 83)) (reverse_move q (hq 61)) t8
    have t10 := move_eq p.symm (reverse_move p (hp 31)) (reverse_move p (hp 3)) (Eq.symm hit)
    have t11 := move_eq p.symm (reverse_move p (hp 91)) (reverse_move p (hp 12)) t10
    have t12 := move_eq p.symm (reverse_move p (hp 142)) (reverse_move p (hp 39)) t11
    have t13 := move_eq p.symm (reverse_move p (hp 19)) (reverse_move p (hp 39)) (Eq.symm h0)
    have t14 := move_eq q.symm (reverse_move q (hq 96)) (reverse_move q (hq 61)) (Eq.trans t12 (Eq.symm t13))
    have t15 := move_eq q (hq 39) (hq 19) (Eq.symm t13)
    have t16 := move_eq q.symm (reverse_move q (hq 26)) (reverse_move q (hq 19)) (Eq.trans (Eq.trans (Eq.trans (Eq.symm t6) t9) (Eq.symm t14)) t15)
    have t17 := move_eq q (hq 61) (hq 5) (Eq.trans (Eq.symm t14) t15)
    have t18 := move_eq p.symm (reverse_move p (hp 66)) (reverse_move p (hp 58)) (Eq.trans (Eq.trans t4 t16) t17)
    have t19 := move_eq q.symm (reverse_move q (hq 2)) (reverse_move q (hq 4)) (Eq.symm hit)
    have t20 := move_eq p (hp 4) (hp 2) (Eq.symm t19)
    have t21 := move_eq q (hq 14) (hq 8) t20
    have t22 := move_eq q.symm (reverse_move q (hq 45)) (reverse_move q (hq 25)) t1
    have t23 := move_eq q.symm (reverse_move q (hq 8)) (reverse_move q (hq 79)) (Eq.trans (Eq.symm t21) t22)
    have t24 := move_eq q.symm (reverse_move q (hq 142)) (reverse_move q (hq 28)) (Eq.symm t23)
    have t25 := move_eq q.symm (reverse_move q (hq 46)) (reverse_move q (hq 28)) t20
    have t26 := move_eq p.symm (reverse_move p (hp 46)) (reverse_move p (hp 1)) (Eq.trans (Eq.symm t14) t15)
    have t27 := move_eq q (hq 142) (hq 1) (Eq.trans (Eq.trans t24 (Eq.symm t25)) t26)
    have t28 := move_eq p.symm (reverse_move p (hp 24)) (reverse_move p (hp 22)) (Eq.trans (Eq.trans (Eq.trans (Eq.trans (Eq.symm t1) (Eq.symm t18)) t3) t23) t27)
    have t29 := move_eq p.symm (reverse_move p (hp 2)) (reverse_move p (hp 22)) (Eq.trans t23 t27)
    exact branch15 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans t28 (Eq.symm t29))
  · exact branch8 p q v hq sep hit
  · exact branch1 p q v hp sep hit
  · exact branch2 p q v hp sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p (hp 59) (hp 12) (Eq.symm h0)
    have t1 := move_eq p.symm (reverse_move p (hp 1)) (reverse_move p (hp 3)) (Eq.symm hit)
    have t2 := move_eq p.symm (reverse_move p (hp 59)) (reverse_move p (hp 0)) (Eq.trans t0 (Eq.symm t1))
    exact branch32 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq p (hp 18) (hp 0) (Eq.symm hit)
    have t1 := move_eq p (hp 56) (hp 1) t0
    have t2 := move_eq q.symm (reverse_move q (hq 5)) (reverse_move q (hq 4)) (Eq.symm hit)
    have t3 := move_eq p.symm (reverse_move p (hp 56)) (reverse_move p (hp 15)) (Eq.trans t1 t2)
    have t4 := move_eq q.symm (reverse_move q (hq 49)) (reverse_move q (hq 7)) (Eq.trans (Eq.symm t3) t0)
    have t5 := move_eq p (hp 49) (hp 7) t4
    have t6 := move_eq q.symm (reverse_move q (hq 19)) (reverse_move q (hq 16)) t2
    have t7 := move_eq p (hp 19) (hp 16) t6
    have t8 := move_eq p (hp 50) (hp 12) (Eq.trans (Eq.symm t7) (Eq.symm h0))
    have t9 := move_eq q (hq 73) (hq 3) t8
    have t10 := move_eq q (hq 120) (hq 11) (Eq.trans t5 t9)
    have t11 := move_eq p.symm (reverse_move p (hp 48)) (reverse_move p (hp 0)) (Eq.trans (Eq.symm t3) t0)
    have t12 := move_eq q.symm (reverse_move q (hq 114)) (reverse_move q (hq 4)) t11
    have t13 := move_eq q.symm (reverse_move q (hq 161)) (reverse_move q (hq 16)) t12
    have t14 := move_eq p.symm (reverse_move p (hp 19)) (reverse_move p (hp 39)) (Eq.symm h0)
    have t15 := move_eq p.symm (reverse_move p (hp 58)) (reverse_move p (hp 3)) (Eq.symm hit)
    have t16 := move_eq p.symm (reverse_move p (hp 35)) (reverse_move p (hp 12)) t15
    have t17 := move_eq p.symm (reverse_move p (hp 11)) (reverse_move p (hp 39)) t16
    have t18 := move_eq q (hq 161) (hq 11) (Eq.trans (Eq.trans (Eq.trans t13 (Eq.symm t6)) t14) (Eq.symm t17))
    have t19 := move_eq q (hq 165) (hq 4) (Eq.trans (Eq.trans t10 (Eq.symm t18)) t12)
    have t20 := move_eq q.symm (reverse_move q (hq 45)) (reverse_move q (hq 13)) t15
    have t21 := move_eq p.symm (reverse_move p (hp 118)) (reverse_move p (hp 42)) t20
    exact branch26 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t19) t21)
  · exact branch41 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · have t0 := move_eq p (hp 9) (hp 0) (Eq.symm hit)
    have t1 := move_eq q.symm (reverse_move q (hq 58)) (reverse_move q (hq 7)) t0
    have t2 := move_eq q (hq 9) (hq 0) (Eq.symm hit)
    have t3 := move_eq p (hp 30) (hp 2) t2
    have t4 := move_eq p (hp 66) (hp 8) t3
    have t5 := move_eq q.symm (reverse_move q (hq 21)) (reverse_move q (hq 28)) t3
    have t6 := move_eq p (hp 28) (hp 21) (Eq.symm t5)
    have t7 := move_eq p (hp 29) (hp 1) t0
    have t8 := move_eq q.symm (reverse_move q (hq 145)) (reverse_move q (hq 19)) t7
    have t9 := move_eq q.symm (reverse_move q (hq 83)) (reverse_move q (hq 61)) t8
    have t10 := move_eq p.symm (reverse_move p (hp 31)) (reverse_move p (hp 3)) (Eq.symm hit)
    have t11 := move_eq p.symm (reverse_move p (hp 91)) (reverse_move p (hp 12)) t10
    have t12 := move_eq p.symm (reverse_move p (hp 142)) (reverse_move p (hp 39)) t11
    have t13 := move_eq p.symm (reverse_move p (hp 19)) (reverse_move p (hp 39)) (Eq.symm h0)
    have t14 := move_eq q.symm (reverse_move q (hq 96)) (reverse_move q (hq 61)) (Eq.trans t12 (Eq.symm t13))
    have t15 := move_eq q (hq 39) (hq 19) (Eq.symm t13)
    have t16 := move_eq q.symm (reverse_move q (hq 26)) (reverse_move q (hq 19)) (Eq.trans (Eq.trans (Eq.trans (Eq.symm t6) t9) (Eq.symm t14)) t15)
    have t17 := move_eq q (hq 61) (hq 5) (Eq.trans (Eq.symm t14) t15)
    have t18 := move_eq p.symm (reverse_move p (hp 66)) (reverse_move p (hp 58)) (Eq.trans (Eq.trans t4 t16) t17)
    have t19 := move_eq q.symm (reverse_move q (hq 2)) (reverse_move q (hq 4)) (Eq.symm hit)
    have t20 := move_eq p (hp 4) (hp 2) (Eq.symm t19)
    have t21 := move_eq q (hq 14) (hq 8) t20
    have t22 := move_eq q.symm (reverse_move q (hq 45)) (reverse_move q (hq 25)) t1
    have t23 := move_eq q.symm (reverse_move q (hq 8)) (reverse_move q (hq 79)) (Eq.trans (Eq.symm t21) t22)
    have t24 := move_eq q.symm (reverse_move q (hq 142)) (reverse_move q (hq 28)) (Eq.symm t23)
    have t25 := move_eq q.symm (reverse_move q (hq 46)) (reverse_move q (hq 28)) t20
    have t26 := move_eq p.symm (reverse_move p (hp 46)) (reverse_move p (hp 1)) (Eq.trans (Eq.symm t14) t15)
    have t27 := move_eq q (hq 142) (hq 1) (Eq.trans (Eq.trans t24 (Eq.symm t25)) t26)
    have t28 := move_eq p.symm (reverse_move p (hp 24)) (reverse_move p (hp 22)) (Eq.trans (Eq.trans (Eq.trans (Eq.trans (Eq.symm t1) (Eq.symm t18)) t3) t23) t27)
    have t29 := move_eq p.symm (reverse_move p (hp 2)) (reverse_move p (hp 22)) (Eq.trans t23 t27)
    exact branch15 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans t28 (Eq.symm t29))
  · exact branch8 p q v hq sep hit
  · exact branch34 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans hit h0)
  · have t0 := move_eq p (hp 19) (hp 3) (Eq.symm hit)
    exact branch32 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 1)) (reverse_move p (hp 12)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 0)) (Eq.symm t0)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p (hp 58) (hp 3) (Eq.symm hit)
    have t1 := move_eq q.symm (reverse_move q (hq 5)) (reverse_move q (hq 4)) t0
    have t2 := move_eq q.symm (reverse_move q (hq 19)) (reverse_move q (hq 16)) t1
    have t3 := move_eq p.symm (reverse_move p (hp 19)) (reverse_move p (hp 39)) (Eq.symm h0)
    have t4 := move_eq p.symm (reverse_move p (hp 35)) (reverse_move p (hp 12)) (Eq.symm hit)
    have t5 := move_eq p.symm (reverse_move p (hp 11)) (reverse_move p (hp 39)) t4
    have t6 := move_eq q (hq 16) (hq 11) (Eq.trans (Eq.trans (Eq.symm t2) t3) (Eq.symm t5))
    have t7 := move_eq q (hq 36) (hq 4) (Eq.symm t6)
    have t8 := move_eq q (hq 59) (hq 12) (Eq.symm h0)
    have t9 := move_eq q (hq 130) (hq 38) t8
    have t10 := move_eq q (hq 94) (hq 62) (Eq.symm t9)
    have t11 := move_eq q (hq 18) (hq 0) t0
    have t12 := move_eq p (hp 57) (hp 2) t11
    have t13 := move_eq p (hp 140) (hp 8) (Eq.trans t10 t12)
    have t14 := move_eq q (hq 58) (hq 3) (Eq.symm hit)
    have t15 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 37)) t14
    have t16 := move_eq q.symm (reverse_move q (hq 104)) (reverse_move q (hq 2)) (Eq.symm t15)
    have t17 := move_eq p (hp 104) (hp 2) t16
    have t18 := move_eq p (hp 155) (hp 8) t17
    have t19 := move_eq q.symm (reverse_move q (hq 45)) (reverse_move q (hq 13)) (Eq.symm hit)
    have t20 := move_eq p.symm (reverse_move p (hp 118)) (reverse_move p (hp 42)) t19
    exact branch26 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.trans (Eq.trans (Eq.symm t7) t13) (Eq.symm t18)) t20)
  · have t0 := move_eq p (hp 9) (hp 3) (Eq.symm hit)
    exact branch41 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.symm t0)
  · exact branch10 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch34 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans hit h0)
  · have t0 := move_eq p.symm (reverse_move p (hp 1)) (reverse_move p (hp 12)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 0)) (Eq.symm t0)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq q.symm (reverse_move q (hq 5)) (reverse_move q (hq 13)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 42)) (reverse_move p (hp 1)) (Eq.symm t0)
    have t2 := move_eq p.symm (reverse_move p (hp 111)) (reverse_move p (hp 0)) t1
    exact branch25 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · exact branch42 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p (hp 9) (hp 3) (Eq.symm hit)
    exact branch41 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.symm t0)
  · exact branch10 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p (hp 19) (hp 12) (Eq.symm hit)
    exact branch34 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 1)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 0)) t0
    exact branch16 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq q (hq 58) (hq 12) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 105)) (reverse_move p (hp 9)) (Eq.symm t0)
    have t2 := move_eq q.symm (reverse_move q (hq 153)) (reverse_move q (hq 2)) t1
    have t3 := move_eq q.symm (reverse_move q (hq 111)) (reverse_move q (hq 0)) t2
    exact branch25 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t3)
  · have t0 := move_eq p (hp 12) (hp 9) hit
    exact branch42 p q v hp hq sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq q.symm (reverse_move q (hq 131)) (reverse_move q (hq 0)) (Eq.trans (Eq.symm h0) hit)
    exact branch30 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 1)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 0)) t0
    exact branch16 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p.symm (reverse_move p (hp 58)) (reverse_move p (hp 39)) (Eq.symm hit)
    have t1 := move_eq q (hq 58) (hq 39) t0
    have t2 := move_eq p.symm (reverse_move p (hp 147)) (reverse_move p (hp 9)) (Eq.symm t1)
    have t3 := move_eq p.symm (reverse_move p (hp 19)) (reverse_move p (hp 39)) (Eq.symm h0)
    have t4 := move_eq q (hq 39) (hq 19) (Eq.symm t3)
    have t5 := move_eq p.symm (reverse_move p (hp 147)) (reverse_move p (hp 1)) t4
    have t6 := move_eq q.symm (reverse_move q (hq 2)) (reverse_move q (hq 7)) (Eq.trans (Eq.symm t2) t5)
    exact branch13 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t6)
  · exact branch43 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · have t0 := move_eq p (hp 12) (hp 9) hit
    exact branch42 p q v hp hq sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq q.symm (reverse_move q (hq 131)) (reverse_move q (hq 0)) (Eq.trans (Eq.symm h0) hit)
    exact branch30 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 60)) (reverse_move p (hp 1)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 41)) (reverse_move p (hp 0)) t0
    exact branch27 p q v hp hq sep (Eq.symm t1)
  · have t0 := move_eq q (hq 58) (hq 19) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 1)) t0
    have t2 := move_eq q.symm (reverse_move q (hq 2)) (reverse_move q (hq 7)) t1
    exact branch13 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq p (hp 19) (hp 9) hit
    exact branch43 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.trans h0 t0)
  · have t0 := move_eq q (hq 19) (hq 2) hit
    have t1 := move_eq p.symm (reverse_move p (hp 31)) (reverse_move p (hp 1)) (Eq.symm t0)
    have t2 := move_eq q.symm (reverse_move q (hq 92)) (reverse_move q (hq 7)) t1
    have t3 := move_eq p (hp 92) (hp 7) t2
    have t4 := move_eq p (hp 19) (hp 2) hit
    have t5 := move_eq p (hp 12) (hp 8) (Eq.trans h0 t4)
    have t6 := move_eq q.symm (reverse_move q (hq 72)) (reverse_move q (hq 13)) (Eq.symm t5)
    have t7 := move_eq p.symm (reverse_move p (hp 60)) (reverse_move p (hp 10)) hit
    have t8 := move_eq p.symm (reverse_move p (hp 41)) (reverse_move p (hp 33)) t7
    have t9 := move_eq p.symm (reverse_move p (hp 13)) (reverse_move p (hp 96)) t8
    have t10 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 2)) (Eq.trans h0 t4)
    have t11 := move_eq q (hq 39) (hq 2) t10
    have t12 := move_eq q.symm (reverse_move q (hq 23)) (reverse_move q (hq 19)) (Eq.trans (Eq.trans (Eq.trans t6 t9) t11) (Eq.symm t0))
    have t13 := move_eq p.symm (reverse_move p (hp 92)) (reverse_move p (hp 10)) (Eq.trans (Eq.trans t3 t12) hit)
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t2) t13)
  · have t0 := move_eq q.symm (reverse_move q (hq 5)) (reverse_move q (hq 19)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 60)) (reverse_move p (hp 1)) (Eq.symm t0)
    have t2 := move_eq p.symm (reverse_move p (hp 41)) (reverse_move p (hp 0)) t1
    exact branch27 p q v hp hq sep (Eq.symm t2)
  · have t0 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 1)) (Eq.symm hit)
    have t1 := move_eq q.symm (reverse_move q (hq 2)) (reverse_move q (hq 7)) t0
    exact branch13 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq q.symm (reverse_move q (hq 2)) (reverse_move q (hq 19)) (Eq.symm hit)
    have t1 := move_eq p (hp 19) (hp 2) (Eq.symm t0)
    have t2 := move_eq p (hp 12) (hp 8) (Eq.trans h0 t1)
    have t3 := move_eq q.symm (reverse_move q (hq 72)) (reverse_move q (hq 13)) (Eq.symm t2)
    have t4 := move_eq p.symm (reverse_move p (hp 31)) (reverse_move p (hp 1)) (Eq.symm hit)
    have t5 := move_eq p.symm (reverse_move p (hp 91)) (reverse_move p (hp 0)) t4
    have t6 := move_eq p.symm (reverse_move p (hp 142)) (reverse_move p (hp 3)) t5
    have t7 := move_eq q.symm (reverse_move q (hq 96)) (reverse_move q (hq 13)) t6
    have t8 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 2)) (Eq.trans h0 t1)
    have t9 := move_eq q (hq 39) (hq 2) t8
    have t10 := move_eq p.symm (reverse_move p (hp 132)) (reverse_move p (hp 1)) (Eq.trans (Eq.trans (Eq.trans t3 (Eq.symm t7)) t9) (Eq.symm hit))
    have t11 := move_eq p.symm (reverse_move p (hp 98)) (reverse_move p (hp 0)) t10
    have t12 := move_eq q (hq 12) (hq 8) (Eq.trans h0 t1)
    have t13 := move_eq p.symm (reverse_move p (hp 105)) (reverse_move p (hp 82)) t12
    have t14 := move_eq q.symm (reverse_move q (hq 153)) (reverse_move q (hq 144)) t13
    have t15 := move_eq q.symm (reverse_move q (hq 111)) (reverse_move q (hq 98)) t14
    exact branch25 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t11) (Eq.symm t15))
  · have t0 := move_eq q.symm (reverse_move q (hq 19)) (reverse_move q (hq 0)) hit
    exact branch29 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 19)) (reverse_move p (hp 39)) (Eq.symm h0)
    have t1 := move_eq q (hq 39) (hq 19) (Eq.symm t0)
    have t2 := move_eq q (hq 96) (hq 5) t1
    have t3 := move_eq p (hp 58) (hp 5) (Eq.symm hit)
    have t4 := move_eq p (hp 142) (hp 17) (Eq.trans t2 t3)
    have t5 := move_eq q (hq 58) (hq 5) (Eq.symm hit)
    have t6 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 5)) (Eq.trans t5 t3)
    have t7 := move_eq p.symm (reverse_move p (hp 31)) (reverse_move p (hp 1)) t6
    have t8 := move_eq p.symm (reverse_move p (hp 91)) (reverse_move p (hp 0)) t7
    have t9 := move_eq p.symm (reverse_move p (hp 17)) (reverse_move p (hp 3)) (Eq.trans (Eq.symm t4) t8)
    exact branch42 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.trans (Eq.symm t9) (Eq.symm t3)) (Eq.symm t5))
  · have t0 := move_eq q.symm (reverse_move q (hq 2)) (reverse_move q (hq 19)) (Eq.symm hit)
    have t1 := move_eq p (hp 19) (hp 2) (Eq.symm t0)
    have t2 := move_eq p (hp 12) (hp 8) (Eq.trans h0 t1)
    have t3 := move_eq q.symm (reverse_move q (hq 72)) (reverse_move q (hq 13)) (Eq.symm t2)
    have t4 := move_eq p.symm (reverse_move p (hp 31)) (reverse_move p (hp 1)) (Eq.symm hit)
    have t5 := move_eq p.symm (reverse_move p (hp 91)) (reverse_move p (hp 0)) t4
    have t6 := move_eq p.symm (reverse_move p (hp 142)) (reverse_move p (hp 3)) t5
    have t7 := move_eq q.symm (reverse_move q (hq 96)) (reverse_move q (hq 13)) t6
    have t8 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 2)) (Eq.trans h0 t1)
    have t9 := move_eq q (hq 39) (hq 2) t8
    have t10 := move_eq p.symm (reverse_move p (hp 132)) (reverse_move p (hp 1)) (Eq.trans (Eq.trans (Eq.trans t3 (Eq.symm t7)) t9) (Eq.symm hit))
    have t11 := move_eq p.symm (reverse_move p (hp 98)) (reverse_move p (hp 0)) t10
    have t12 := move_eq q (hq 12) (hq 8) (Eq.trans h0 t1)
    have t13 := move_eq p.symm (reverse_move p (hp 105)) (reverse_move p (hp 82)) t12
    have t14 := move_eq q.symm (reverse_move q (hq 153)) (reverse_move q (hq 144)) t13
    have t15 := move_eq q.symm (reverse_move q (hq 111)) (reverse_move q (hq 98)) t14
    exact branch25 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t11) (Eq.symm t15))
  · have t0 := move_eq q.symm (reverse_move q (hq 19)) (reverse_move q (hq 0)) hit
    exact branch29 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 58)) (Eq.symm hit)
    have t1 := move_eq q.symm (reverse_move q (hq 58)) (reverse_move q (hq 5)) (Eq.symm hit)
    have t2 := move_eq p.symm (reverse_move p (hp 31)) (reverse_move p (hp 1)) (Eq.trans t0 t1)
    have t3 := move_eq p.symm (reverse_move p (hp 91)) (reverse_move p (hp 0)) t2
    have t4 := move_eq p.symm (reverse_move p (hp 142)) (reverse_move p (hp 3)) t3
    have t5 := move_eq p.symm (reverse_move p (hp 19)) (reverse_move p (hp 39)) (Eq.symm h0)
    have t6 := move_eq q.symm (reverse_move q (hq 2)) (reverse_move q (hq 19)) (Eq.trans t0 t1)
    have t7 := move_eq q (hq 39) (hq 2) (Eq.trans (Eq.symm t5) (Eq.symm t6))
    have t8 := move_eq q (hq 96) (hq 5) (Eq.trans (Eq.trans t7 t0) t1)
    exact branch42 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.trans (Eq.symm t4) t8) hit)
  · have t0 := move_eq q.symm (reverse_move q (hq 5)) (reverse_move q (hq 2)) hit
    have t1 := move_eq q.symm (reverse_move q (hq 19)) (reverse_move q (hq 0)) t0
    exact branch29 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p (hp 59) (hp 12) (Eq.symm h0)
    have t1 := move_eq q.symm (reverse_move q (hq 5)) (reverse_move q (hq 0)) hit
    have t2 := move_eq p.symm (reverse_move p (hp 1)) (reverse_move p (hp 3)) t1
    have t3 := move_eq p.symm (reverse_move p (hp 59)) (reverse_move p (hp 0)) (Eq.trans t0 (Eq.symm t2))
    exact branch32 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t3)
  · have t0 := move_eq p.symm (reverse_move p (hp 35)) (reverse_move p (hp 31)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 11)) (reverse_move p (hp 91)) t0
    have t2 := move_eq q.symm (reverse_move q (hq 37)) (reverse_move q (hq 3)) (Eq.symm t1)
    have t3 := move_eq p.symm (reverse_move p (hp 142)) (reverse_move p (hp 37)) (Eq.symm t1)
    have t4 := move_eq p.symm (reverse_move p (hp 19)) (reverse_move p (hp 39)) (Eq.symm h0)
    have t5 := move_eq q (hq 39) (hq 19) (Eq.symm t4)
    have t6 := move_eq q (hq 96) (hq 5) t5
    have t7 := move_eq p (hp 58) (hp 9) hit
    exact branch42 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.trans (Eq.trans (Eq.symm t2) (Eq.symm t3)) t6) t7)
  · have t0 := move_eq q (hq 58) (hq 2) hit
    have t1 := move_eq p (hp 29) (hp 9) t0
    have t2 := move_eq p (hp 86) (hp 9) (Eq.trans t1 t0)
    have t3 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 31)) t0
    have t4 := move_eq p.symm (reverse_move p (hp 91)) (reverse_move p (hp 31)) (Eq.symm t3)
    have t5 := move_eq p.symm (reverse_move p (hp 142)) (reverse_move p (hp 31)) (Eq.trans t4 (Eq.symm t3))
    have t6 := move_eq p.symm (reverse_move p (hp 19)) (reverse_move p (hp 39)) (Eq.symm h0)
    have t7 := move_eq q (hq 39) (hq 19) (Eq.symm t6)
    have t8 := move_eq q (hq 96) (hq 5) t7
    have t9 := move_eq p (hp 58) (hp 2) hit
    have t10 := move_eq p.symm (reverse_move p (hp 86)) (reverse_move p (hp 2)) (Eq.trans (Eq.trans (Eq.trans (Eq.trans (Eq.trans t2 t0) t3) (Eq.symm t5)) t8) t9)
    have t11 := move_eq q.symm (reverse_move q (hq 54)) (reverse_move q (hq 0)) (Eq.trans (Eq.trans t2 (Eq.symm t1)) t10)
    have t12 := move_eq q.symm (reverse_move q (hq 5)) (reverse_move q (hq 28)) t9
    have t13 := move_eq p (hp 28) (hp 5) (Eq.symm t12)
    have t14 := move_eq q (hq 83) (hq 17) t13
    have t15 := move_eq q.symm (reverse_move q (hq 145)) (reverse_move q (hq 2)) (Eq.trans t1 t0)
    exact branch8 p q v hq sep (Eq.trans (Eq.trans (Eq.symm t11) (Eq.symm t14)) t15)
  · have t0 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 31)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 91)) (reverse_move p (hp 31)) (Eq.symm t0)
    have t2 := move_eq p.symm (reverse_move p (hp 142)) (reverse_move p (hp 31)) (Eq.trans t1 (Eq.symm t0))
    have t3 := move_eq q.symm (reverse_move q (hq 96)) (reverse_move q (hq 2)) (Eq.trans t2 (Eq.symm t0))
    have t4 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 0)) t3
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t4)
  · have t0 := move_eq q.symm (reverse_move q (hq 58)) (reverse_move q (hq 0)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 35)) (reverse_move p (hp 3)) t0
    have t2 := move_eq p.symm (reverse_move p (hp 11)) (reverse_move p (hp 12)) t1
    have t3 := move_eq q.symm (reverse_move q (hq 131)) (reverse_move q (hq 3)) (Eq.trans (Eq.symm h0) (Eq.symm t2))
    exact branch33 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t3)
  · have t0 := move_eq q.symm (reverse_move q (hq 2)) (reverse_move q (hq 0)) hit
    exact branch8 p q v hq sep (Eq.symm t0)
  · have t0 := move_eq q.symm (reverse_move q (hq 2)) (reverse_move q (hq 0)) hit
    exact branch8 p q v hq sep (Eq.symm t0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch45 (h0 : v 39 = v 142) (h1 : v 13 = v 111) : False := by
  have t0 := move_eq p (hp 111) (hp 13) (Eq.symm h1)
  have t1 := move_eq q (hq 42) (hq 41) t0
  have t2 := move_eq p.symm (reverse_move p (hp 154)) (reverse_move p (hp 131)) t1
  have t3 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 106)) (Eq.symm h0)
  have t4 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 42)) (Eq.symm h1)
  have t5 := move_eq q (hq 154) (hq 41) (Eq.trans t4 t0)
  have t6 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 131)) (Eq.trans t3 t5)
  have t7 := move_eq q (hq 152) (hq 25) (Eq.trans t2 (Eq.symm t6))
  have t8 := move_eq q (hq 106) (hq 70) t5
  have t9 := move_eq p (hp 153) (hp 22) t8
  have t10 := move_eq q (hq 7) (hq 6) (Eq.trans (Eq.symm t7) t9)
  exact short4 p q G sep e₀ e₁ e₂ no ![0,2,0,2] (by decide)
    (v 1) (v 1) (v 6) (v 6)
    (rfl) (Eq.trans (hq 6) (Eq.symm t10)) (rfl) (hq 1)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch44 (h0 : v 39 = v 142) : False := by
  have t0 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 106)) (Eq.symm h0)
  have t1 := move_eq q.symm (reverse_move q (hq 154)) (reverse_move q (hq 140)) (Eq.symm t0)
  rcases collision16 (fun h => no (.inr (.inr (.inl h))))
    (v 0) (v 0) (v 3) (v 3) (v 13) (v 13) (v 42) (v 42) (v 111) (v 111) (v 170) (v 77) (v 25) (v 7) (v 7) (v 1)
    (e₀ (v 0))
    ((hp 3) ▸ e₁ (v 3))
    (e₀ (v 3))
    ((hq 13) ▸ e₂ (v 13))
    (e₀ (v 13))
    ((hp 42) ▸ e₁ (v 42))
    (e₀ (v 42))
    ((hp 111) ▸ e₁ (v 111))
    (e₀ (v 111))
    ((Eq.trans (congrArg p (Eq.symm t1)) (hp 159)) ▸ e₁ (v 170))
    ((hq 140) ▸ e₂ (v 170))
    ((hp 25) ▸ e₁ (v 25))
    ((hq 25) ▸ e₂ (v 25))
    (e₀ (v 7))
    ((hq 7) ▸ e₂ (v 7))
    ((hp 0) ▸ e₁ (v 0)) with hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit
  · exact branch1 p q v hp sep hit
  · have t0 := move_eq q (hq 13) (hq 0) (Eq.symm hit)
    exact branch10 p q v hp hq sep G e₀ e₁ e₂ no t0
  · exact branch26 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch25 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 106)) (Eq.symm h0)
    have t1 := move_eq q (hq 140) (hq 0) (Eq.symm hit)
    have t2 := move_eq q.symm (reverse_move q (hq 154)) (reverse_move q (hq 0)) (Eq.trans (Eq.symm t0) t1)
    exact branch17 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq q (hq 25) (hq 0) (Eq.symm hit)
    exact branch13 p q v hp hq sep G e₀ e₁ e₂ no t0
  · exact branch4 p q v hp hq sep hit
  · exact branch1 p q v hp sep hit
  · have t0 := move_eq q (hq 13) (hq 0) (Eq.symm hit)
    exact branch10 p q v hp hq sep G e₀ e₁ e₂ no t0
  · exact branch26 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch25 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch31 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch4 p q v hp hq sep hit
  · have t0 := move_eq p.symm (reverse_move p (hp 0)) (reverse_move p (hp 3)) (Eq.symm hit)
    exact branch1 p q v hp sep t0
  · have t0 := move_eq p (hp 13) (hp 3) (Eq.symm hit)
    exact branch27 p q v hp hq sep (Eq.symm t0)
  · have t0 := move_eq q.symm (reverse_move q (hq 112)) (reverse_move q (hq 13)) (Eq.symm hit)
    have t1 := move_eq p (hp 42) (hp 3) (Eq.symm hit)
    have t2 := move_eq q (hq 112) (hq 0) (Eq.trans t0 t1)
    exact branch10 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans hit t2)
  · have t0 := move_eq p (hp 111) (hp 3) (Eq.symm hit)
    exact branch26 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 106)) (Eq.symm h0)
    have t1 := move_eq q (hq 140) (hq 3) (Eq.symm hit)
    have t2 := move_eq q.symm (reverse_move q (hq 154)) (reverse_move q (hq 3)) (Eq.trans (Eq.symm t0) t1)
    have t3 := move_eq p (hp 159) (hp 3) t2
    exact branch25 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t3)
  · have t0 := move_eq p (hp 25) (hp 3) (Eq.symm hit)
    exact branch31 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 7) (hp 3) (Eq.symm hit)
    exact branch6 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 13) (hp 3) (Eq.symm hit)
    exact branch27 p q v hp hq sep (Eq.symm t0)
  · have t0 := move_eq q.symm (reverse_move q (hq 112)) (reverse_move q (hq 13)) (Eq.symm hit)
    have t1 := move_eq p (hp 42) (hp 3) (Eq.symm hit)
    have t2 := move_eq q (hq 112) (hq 0) (Eq.trans t0 t1)
    exact branch10 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans hit t2)
  · have t0 := move_eq p (hp 111) (hp 3) (Eq.symm hit)
    exact branch26 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 77) (hp 3) (Eq.symm hit)
    exact branch30 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 7) (hp 3) (Eq.symm hit)
    exact branch6 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 12)) (reverse_move p (hp 0)) hit
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 106)) (Eq.symm h0)
    have t1 := move_eq p.symm (reverse_move p (hp 111)) (reverse_move p (hp 42)) (Eq.symm hit)
    have t2 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 42)) (Eq.trans t1 (Eq.symm hit))
    have t3 := move_eq q (hq 154) (hq 13) (Eq.trans t2 (Eq.symm hit))
    have t4 := move_eq p (hp 77) (hp 3) (Eq.trans t0 t3)
    exact branch30 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t4)
  · exact branch45 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · have t0 := move_eq q (hq 140) (hq 13) (Eq.symm hit)
    have t1 := move_eq p (hp 77) (hp 3) t0
    exact branch30 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq q (hq 25) (hq 13) (Eq.symm hit)
    have t1 := move_eq p (hp 7) (hp 3) t0
    exact branch6 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq q (hq 13) (hq 7) hit
    have t1 := move_eq p.symm (reverse_move p (hp 12)) (reverse_move p (hp 0)) t0
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p.symm (reverse_move p (hp 111)) (reverse_move p (hp 42)) (Eq.symm hit)
    exact branch45 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.trans hit (Eq.symm t0))
  · exact branch45 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · have t0 := move_eq p (hp 77) (hp 13) (Eq.symm hit)
    have t1 := move_eq q (hq 41) (hq 39) (Eq.trans (Eq.symm t0) (Eq.symm h0))
    have t2 := move_eq q (hq 131) (hq 39) (Eq.symm h0)
    have t3 := move_eq p.symm (reverse_move p (hp 131)) (reverse_move p (hp 19)) (Eq.trans t1 (Eq.symm t2))
    have t4 := move_eq p (hp 41) (hp 39) (Eq.trans (Eq.symm t0) (Eq.symm h0))
    have t5 := move_eq p (hp 60) (hp 12) t4
    have t6 := move_eq p (hp 131) (hp 3) (Eq.trans t3 t5)
    exact branch32 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.trans (Eq.symm t6) t1) (Eq.symm t2))
  · have t0 := move_eq q (hq 13) (hq 7) hit
    have t1 := move_eq p.symm (reverse_move p (hp 12)) (reverse_move p (hp 0)) t0
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p.symm (reverse_move p (hp 42)) (reverse_move p (hp 0)) hit
    exact branch26 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 111) (hp 42) (Eq.symm hit)
    exact branch45 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.trans (Eq.symm t0) hit)
  · have t0 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 106)) (Eq.symm h0)
    have t1 := move_eq q.symm (reverse_move q (hq 154)) (reverse_move q (hq 140)) (Eq.symm t0)
    have t2 := move_eq p (hp 159) (hp 42) (Eq.trans t1 (Eq.symm hit))
    exact branch45 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.symm t2)
  · have t0 := move_eq p (hp 42) (hp 25) hit
    have t1 := move_eq p (hp 77) (hp 13) (Eq.symm t0)
    have t2 := move_eq q (hq 41) (hq 39) (Eq.trans (Eq.symm t1) (Eq.symm h0))
    have t3 := move_eq q (hq 131) (hq 39) (Eq.symm h0)
    have t4 := move_eq p.symm (reverse_move p (hp 131)) (reverse_move p (hp 19)) (Eq.trans t2 (Eq.symm t3))
    have t5 := move_eq p (hp 41) (hp 39) (Eq.trans (Eq.symm t1) (Eq.symm h0))
    have t6 := move_eq p (hp 60) (hp 12) t5
    have t7 := move_eq p (hp 131) (hp 3) (Eq.trans t4 t6)
    exact branch32 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.trans (Eq.symm t7) t2) (Eq.symm t3))
  · have t0 := move_eq q.symm (reverse_move q (hq 112)) (reverse_move q (hq 25)) hit
    have t1 := move_eq p (hp 112) (hp 25) t0
    have t2 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 106)) (Eq.symm h0)
    have t3 := move_eq p.symm (reverse_move p (hp 111)) (reverse_move p (hp 24)) hit
    have t4 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 75)) t3
    have t5 := move_eq q (hq 154) (hq 75) t4
    have t6 := move_eq p.symm (reverse_move p (hp 112)) (reverse_move p (hp 99)) (Eq.trans (Eq.trans t1 t2) t5)
    have t7 := move_eq p.symm (reverse_move p (hp 149)) (reverse_move p (hp 78)) (Eq.trans (Eq.symm t6) t0)
    have t8 := move_eq q (hq 111) (hq 24) t3
    have t9 := move_eq q (hq 153) (hq 74) t8
    have t10 := move_eq p (hp 42) (hp 7) hit
    have t11 := move_eq p (hp 23) (hp 13) (Eq.symm t10)
    have t12 := move_eq q (hq 71) (hq 41) t11
    have t13 := move_eq p.symm (reverse_move p (hp 64)) (reverse_move p (hp 131)) t12
    have t14 := move_eq q (hq 77) (hq 34) (Eq.trans t2 t5)
    have t15 := move_eq q (hq 134) (hq 10) t14
    have t16 := move_eq p (hp 131) (hp 32) (Eq.trans (Eq.symm t13) t15)
    have t17 := move_eq q.symm (reverse_move q (hq 41)) (reverse_move q (hq 135)) t16
    have t18 := move_eq q.symm (reverse_move q (hq 153)) (reverse_move q (hq 78)) (Eq.trans t9 (Eq.symm t17))
    have t19 := move_eq p.symm (reverse_move p (hp 129)) (reverse_move p (hp 94)) t15
    have t20 := move_eq p (hp 71) (hp 41) t11
    have t21 := move_eq p (hp 105) (hp 41) (Eq.trans t9 (Eq.symm t17))
    have t22 := move_eq q (hq 127) (hq 38) (Eq.trans t20 (Eq.symm t21))
    have t23 := move_eq p.symm (reverse_move p (hp 74)) (reverse_move p (hp 17)) (Eq.trans t19 (Eq.symm t22))
    have t24 := move_eq p (hp 149) (hp 17) (Eq.trans (Eq.trans (Eq.trans t7 (Eq.symm t18)) t8) t23)
    have t25 := move_eq q (hq 53) (hq 25) (Eq.trans (Eq.trans (Eq.symm t24) (Eq.symm t6)) t0)
    have t26 := move_eq p.symm (reverse_move p (hp 62)) (reverse_move p (hp 24)) t25
    have t27 := move_eq q (hq 64) (hq 32) t15
    have t28 := move_eq p (hp 93) (hp 20) (Eq.symm t27)
    have t29 := move_eq p (hp 53) (hp 25) (Eq.trans (Eq.trans (Eq.symm t24) (Eq.symm t6)) t0)
    have t30 := move_eq p (hp 129) (hp 53) (Eq.trans t19 (Eq.symm t22))
    have t31 := move_eq q (hq 77) (hq 32) (Eq.trans (Eq.trans (Eq.symm t29) (Eq.symm t30)) t15)
    have t32 := move_eq p (hp 93) (hp 10) (Eq.trans (Eq.symm t31) t14)
    exact branch15 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.trans (Eq.symm t26) (Eq.symm t28)) t32)
  · have t0 := move_eq p (hp 111) (hp 42) (Eq.symm hit)
    exact branch45 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.trans (Eq.symm t0) hit)
  · have t0 := move_eq p (hp 77) (hp 42) (Eq.symm hit)
    have t1 := move_eq q (hq 131) (hq 13) t0
    exact branch34 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq q.symm (reverse_move q (hq 112)) (reverse_move q (hq 25)) hit
    have t1 := move_eq p (hp 112) (hp 25) t0
    have t2 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 106)) (Eq.symm h0)
    have t3 := move_eq p.symm (reverse_move p (hp 111)) (reverse_move p (hp 24)) hit
    have t4 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 75)) t3
    have t5 := move_eq q (hq 154) (hq 75) t4
    have t6 := move_eq p.symm (reverse_move p (hp 112)) (reverse_move p (hp 99)) (Eq.trans (Eq.trans t1 t2) t5)
    have t7 := move_eq p.symm (reverse_move p (hp 149)) (reverse_move p (hp 78)) (Eq.trans (Eq.symm t6) t0)
    have t8 := move_eq q (hq 111) (hq 24) t3
    have t9 := move_eq q (hq 153) (hq 74) t8
    have t10 := move_eq p (hp 42) (hp 7) hit
    have t11 := move_eq p (hp 23) (hp 13) (Eq.symm t10)
    have t12 := move_eq q (hq 71) (hq 41) t11
    have t13 := move_eq p.symm (reverse_move p (hp 64)) (reverse_move p (hp 131)) t12
    have t14 := move_eq q (hq 77) (hq 34) (Eq.trans t2 t5)
    have t15 := move_eq q (hq 134) (hq 10) t14
    have t16 := move_eq p (hp 131) (hp 32) (Eq.trans (Eq.symm t13) t15)
    have t17 := move_eq q.symm (reverse_move q (hq 41)) (reverse_move q (hq 135)) t16
    have t18 := move_eq q.symm (reverse_move q (hq 153)) (reverse_move q (hq 78)) (Eq.trans t9 (Eq.symm t17))
    have t19 := move_eq p.symm (reverse_move p (hp 129)) (reverse_move p (hp 94)) t15
    have t20 := move_eq p (hp 71) (hp 41) t11
    have t21 := move_eq p (hp 105) (hp 41) (Eq.trans t9 (Eq.symm t17))
    have t22 := move_eq q (hq 127) (hq 38) (Eq.trans t20 (Eq.symm t21))
    have t23 := move_eq p.symm (reverse_move p (hp 74)) (reverse_move p (hp 17)) (Eq.trans t19 (Eq.symm t22))
    have t24 := move_eq p (hp 149) (hp 17) (Eq.trans (Eq.trans (Eq.trans t7 (Eq.symm t18)) t8) t23)
    have t25 := move_eq q (hq 53) (hq 25) (Eq.trans (Eq.trans (Eq.symm t24) (Eq.symm t6)) t0)
    have t26 := move_eq p.symm (reverse_move p (hp 62)) (reverse_move p (hp 24)) t25
    have t27 := move_eq q (hq 64) (hq 32) t15
    have t28 := move_eq p (hp 93) (hp 20) (Eq.symm t27)
    have t29 := move_eq p (hp 53) (hp 25) (Eq.trans (Eq.trans (Eq.symm t24) (Eq.symm t6)) t0)
    have t30 := move_eq p (hp 129) (hp 53) (Eq.trans t19 (Eq.symm t22))
    have t31 := move_eq q (hq 77) (hq 32) (Eq.trans (Eq.trans (Eq.symm t29) (Eq.symm t30)) t15)
    have t32 := move_eq p (hp 93) (hp 10) (Eq.trans (Eq.symm t31) t14)
    exact branch15 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.trans (Eq.symm t26) (Eq.symm t28)) t32)
  · have t0 := move_eq p.symm (reverse_move p (hp 111)) (reverse_move p (hp 0)) hit
    exact branch25 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 106)) (Eq.symm h0)
    have t1 := move_eq q.symm (reverse_move q (hq 154)) (reverse_move q (hq 140)) (Eq.symm t0)
    have t2 := move_eq p (hp 159) (hp 111) (Eq.trans t1 (Eq.symm hit))
    have t3 := move_eq p (hp 111) (hp 42) t2
    exact branch45 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.trans (Eq.symm t3) (Eq.symm t2))
  · have t0 := move_eq p (hp 111) (hp 25) hit
    have t1 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 106)) (Eq.symm h0)
    have t2 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 78)) hit
    have t3 := move_eq q (hq 154) (hq 78) t2
    have t4 := move_eq p.symm (reverse_move p (hp 111)) (reverse_move p (hp 13)) (Eq.trans (Eq.trans t0 t1) t3)
    exact branch45 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.symm t4)
  · have t0 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 106)) (Eq.symm h0)
    have t1 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 24)) hit
    have t2 := move_eq q (hq 154) (hq 24) t1
    have t3 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 130)) (Eq.trans t0 t2)
    have t4 := move_eq q.symm (reverse_move q (hq 157)) (reverse_move q (hq 25)) hit
    have t5 := move_eq p (hp 163) (hp 25) t4
    have t6 := move_eq p (hp 109) (hp 74) (Eq.trans (Eq.trans t5 t0) t2)
    have t7 := move_eq p (hp 77) (hp 74) (Eq.trans t0 t2)
    have t8 := move_eq p (hp 134) (hp 39) (Eq.trans (Eq.trans t6 (Eq.symm t7)) (Eq.symm h0))
    have t9 := move_eq p (hp 78) (hp 12) t8
    have t10 := move_eq p (hp 130) (hp 3) (Eq.trans (Eq.symm t3) t9)
    exact branch16 p q v hp sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t10) (Eq.symm t2))
  · have t0 := move_eq p (hp 111) (hp 77) hit
    have t1 := move_eq p (hp 42) (hp 39) (Eq.trans t0 (Eq.symm h0))
    have t2 := move_eq p (hp 13) (hp 12) t1
    have t3 := move_eq p (hp 41) (hp 3) t2
    exact branch28 p q v hp hq sep (Eq.symm t3)
  · have t0 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 106)) (Eq.symm h0)
    have t1 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 24)) hit
    have t2 := move_eq q (hq 154) (hq 24) t1
    have t3 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 130)) (Eq.trans t0 t2)
    have t4 := move_eq q.symm (reverse_move q (hq 157)) (reverse_move q (hq 25)) hit
    have t5 := move_eq p (hp 163) (hp 25) t4
    have t6 := move_eq p (hp 109) (hp 74) (Eq.trans (Eq.trans t5 t0) t2)
    have t7 := move_eq p (hp 77) (hp 74) (Eq.trans t0 t2)
    have t8 := move_eq p (hp 134) (hp 39) (Eq.trans (Eq.trans t6 (Eq.symm t7)) (Eq.symm h0))
    have t9 := move_eq p (hp 78) (hp 12) t8
    have t10 := move_eq p (hp 130) (hp 3) (Eq.trans (Eq.symm t3) t9)
    exact branch16 p q v hp sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t10) (Eq.symm t2))
  · have t0 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 0)) hit
    exact branch17 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq q (hq 140) (hq 25) hit
    have t1 := move_eq p (hp 77) (hp 7) t0
    have t2 := move_eq p (hp 39) (hp 23) (Eq.trans h0 t1)
    have t3 := move_eq q (hq 71) (hq 12) (Eq.symm t2)
    have t4 := move_eq q (hq 77) (hq 7) t0
    have t5 := move_eq q (hq 134) (hq 1) t4
    have t6 := move_eq p (hp 64) (hp 6) t5
    have t7 := move_eq q.symm (reverse_move q (hq 71)) (reverse_move q (hq 64)) t6
    have t8 := move_eq p (hp 12) (hp 6) (Eq.trans (Eq.trans t2 t7) t5)
    have t9 := move_eq p (hp 38) (hp 3) (Eq.trans (Eq.trans (Eq.symm t3) t6) (Eq.symm t8))
    have t10 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 24)) t0
    have t11 := move_eq q (hq 140) (hq 24) (Eq.trans hit t10)
    have t12 := move_eq p (hp 74) (hp 7) (Eq.trans (Eq.symm t11) t0)
    have t13 := move_eq p.symm (reverse_move p (hp 129)) (reverse_move p (hp 22)) t5
    have t14 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 69)) (Eq.trans (Eq.trans t1 (Eq.symm t12)) t13)
    exact branch31 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t9) (Eq.symm t14))
  · have t0 := move_eq q (hq 140) (hq 7) hit
    have t1 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 0)) t0
    have t2 := move_eq q (hq 25) (hq 0) t1
    exact branch13 p q v hp hq sep G e₀ e₁ e₂ no t2
  · have t0 := move_eq p (hp 77) (hp 7) hit
    have t1 := move_eq p (hp 39) (hp 23) (Eq.trans h0 t0)
    have t2 := move_eq q (hq 71) (hq 12) (Eq.symm t1)
    have t3 := move_eq q (hq 77) (hq 7) hit
    have t4 := move_eq q (hq 134) (hq 1) t3
    have t5 := move_eq p (hp 64) (hp 6) t4
    have t6 := move_eq q.symm (reverse_move q (hq 71)) (reverse_move q (hq 64)) t5
    have t7 := move_eq p (hp 12) (hp 6) (Eq.trans (Eq.trans t1 t6) t4)
    have t8 := move_eq p (hp 38) (hp 3) (Eq.trans (Eq.trans (Eq.symm t2) t5) (Eq.symm t7))
    have t9 := move_eq q.symm (reverse_move q (hq 140)) (reverse_move q (hq 25)) hit
    have t10 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 24)) hit
    have t11 := move_eq q (hq 140) (hq 24) (Eq.trans t9 t10)
    have t12 := move_eq p (hp 74) (hp 7) (Eq.trans (Eq.symm t11) hit)
    have t13 := move_eq p.symm (reverse_move p (hp 129)) (reverse_move p (hp 22)) t4
    have t14 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 69)) (Eq.trans (Eq.trans t0 (Eq.symm t12)) t13)
    exact branch31 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t8) (Eq.symm t14))
  · have t0 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 0)) hit
    have t1 := move_eq q (hq 25) (hq 0) t0
    exact branch13 p q v hp hq sep G e₀ e₁ e₂ no t1
  · have t0 := move_eq q (hq 25) (hq 7) hit
    have t1 := move_eq p.symm (reverse_move p (hp 24)) (reverse_move p (hp 0)) t0
    exact branch5 p q v hp hq sep (Eq.symm t1)
  · have t0 := move_eq p.symm (reverse_move p (hp 24)) (reverse_move p (hp 0)) hit
    exact branch5 p q v hp hq sep (Eq.symm t0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch46 (h0 : v 39 = v 7) : False := by
  have t0 := move_eq p (hp 39) (hp 7) h0
  exact short8 p q G sep e₀ e₁ e₂ no ![0,1,0,1,0,1,2,1] (by decide)
    (v 0) (v 0) (v 3) (v 3) (v 12) (v 12) (v 7) (v 1)
    (rfl) (hp 3) (rfl) (hp 12) (rfl) (Eq.trans (hp 7) (Eq.symm t0)) (hq 7) (hp 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep in
private theorem branch48 (h0 : v 39 = v 59) (h1 : v 77 = v 7) : False := by
  have t0 := move_eq q (hq 77) (hq 7) h1
  have t1 := move_eq q (hq 134) (hq 1) t0
  have t2 := move_eq p (hp 64) (hp 6) t1
  have t3 := move_eq q.symm (reverse_move q (hq 131)) (reverse_move q (hq 107)) (Eq.symm h0)
  have t4 := move_eq p (hp 77) (hp 7) h1
  have t5 := move_eq p (hp 107) (hp 23) (Eq.trans (Eq.symm t3) t4)
  have t6 := move_eq q (hq 71) (hq 48) (Eq.symm t5)
  have t7 := move_eq p (hp 71) (hp 48) (Eq.symm t5)
  have t8 := move_eq q (hq 127) (hq 15) t7
  have t9 := move_eq p.symm (reverse_move p (hp 19)) (reverse_move p (hp 106)) (Eq.symm h0)
  have t10 := move_eq q (hq 106) (hq 19) (Eq.symm t9)
  have t11 := move_eq p (hp 153) (hp 5) t10
  have t12 := move_eq p (hp 103) (hp 17) t11
  have t13 := move_eq q.symm (reverse_move q (hq 15)) (reverse_move q (hq 104)) (Eq.trans (Eq.symm t8) (Eq.symm t12))
  have t14 := move_eq q (hq 64) (hq 6) t1
  exact (sep (v 6)).2.2 (Eq.trans (Eq.trans (hp 6) (Eq.trans (Eq.trans (Eq.symm t2) t6) (Eq.symm t13))) (Eq.symm (Eq.trans (hq 6) (Eq.trans (Eq.trans (Eq.trans (Eq.symm t14) (Eq.symm t2)) t6) (Eq.symm t13)))))

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch47 (h0 : v 39 = v 59) : False := by
  have t0 := move_eq q.symm (reverse_move q (hq 131)) (reverse_move q (hq 107)) (Eq.symm h0)
  rcases collision16 (fun h => no (.inr (.inr (.inl h))))
    (v 0) (v 0) (v 3) (v 3) (v 12) (v 12) (v 39) (v 39) (v 107) (v 107) (v 77) (v 77) (v 25) (v 7) (v 7) (v 1)
    (e₀ (v 0))
    ((hp 3) ▸ e₁ (v 3))
    (e₀ (v 3))
    ((hp 12) ▸ e₁ (v 12))
    (e₀ (v 12))
    ((hp 39) ▸ e₁ (v 39))
    (e₀ (v 39))
    ((hq 107) ▸ e₂ (v 107))
    (e₀ (v 107))
    ((Eq.trans (hp 77) t0) ▸ e₁ (v 77))
    (e₀ (v 77))
    ((hp 25) ▸ e₁ (v 25))
    ((hq 25) ▸ e₂ (v 25))
    (e₀ (v 7))
    ((hq 7) ▸ e₂ (v 7))
    ((hp 0) ▸ e₁ (v 0)) with hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit
  · exact branch1 p q v hp sep hit
  · exact branch2 p q v hp sep G e₀ e₁ e₂ no hit
  · exact branch3 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq q.symm (reverse_move q (hq 131)) (reverse_move q (hq 107)) (Eq.symm h0)
    exact branch30 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans hit (Eq.symm t0))
  · exact branch31 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq q (hq 25) (hq 0) (Eq.symm hit)
    exact branch13 p q v hp hq sep G e₀ e₁ e₂ no t0
  · exact branch4 p q v hp hq sep hit
  · exact branch1 p q v hp sep hit
  · exact branch2 p q v hp sep G e₀ e₁ e₂ no hit
  · exact branch3 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq q.symm (reverse_move q (hq 131)) (reverse_move q (hq 107)) (Eq.symm h0)
    exact branch30 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans hit (Eq.symm t0))
  · exact branch31 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch4 p q v hp hq sep hit
  · have t0 := move_eq p.symm (reverse_move p (hp 0)) (reverse_move p (hp 3)) (Eq.symm hit)
    exact branch1 p q v hp sep t0
  · have t0 := move_eq p (hp 12) (hp 3) (Eq.symm hit)
    exact branch1 p q v hp sep (Eq.symm t0)
  · exact branch34 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans hit h0)
  · have t0 := move_eq q.symm (reverse_move q (hq 131)) (reverse_move q (hq 107)) (Eq.symm h0)
    exact branch33 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans hit (Eq.symm t0))
  · have t0 := move_eq p (hp 77) (hp 3) (Eq.symm hit)
    exact branch30 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 25) (hp 3) (Eq.symm hit)
    exact branch31 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 7) (hp 3) (Eq.symm hit)
    exact branch6 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 12) (hp 3) (Eq.symm hit)
    exact branch1 p q v hp sep (Eq.symm t0)
  · exact branch34 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans hit h0)
  · have t0 := move_eq q.symm (reverse_move q (hq 131)) (reverse_move q (hq 107)) (Eq.symm h0)
    exact branch33 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans hit (Eq.symm t0))
  · have t0 := move_eq p (hp 77) (hp 3) (Eq.symm hit)
    exact branch30 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 7) (hp 3) (Eq.symm hit)
    exact branch6 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 12)) (reverse_move p (hp 0)) hit
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t0)
  · exact branch40 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans hit h0)
  · have t0 := move_eq q.symm (reverse_move q (hq 131)) (reverse_move q (hq 107)) (Eq.symm h0)
    exact branch35 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans hit (Eq.symm t0))
  · have t0 := move_eq p (hp 77) (hp 12) (Eq.symm hit)
    exact branch33 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 25) (hp 12) (Eq.symm hit)
    have t1 := move_eq p (hp 77) (hp 3) t0
    exact branch30 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · exact branch39 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch40 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans hit h0)
  · have t0 := move_eq q.symm (reverse_move q (hq 131)) (reverse_move q (hq 107)) (Eq.symm h0)
    exact branch35 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans hit (Eq.symm t0))
  · have t0 := move_eq p (hp 77) (hp 12) (Eq.symm hit)
    exact branch33 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · exact branch39 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 0)) hit
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq q.symm (reverse_move q (hq 131)) (reverse_move q (hq 107)) (Eq.symm h0)
    exact branch44 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans hit (Eq.symm t0))
  · have t0 := move_eq p (hp 77) (hp 39) (Eq.symm hit)
    exact branch35 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 39) (hp 25) hit
    have t1 := move_eq p (hp 77) (hp 12) (Eq.symm t0)
    exact branch33 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · exact branch46 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq q.symm (reverse_move q (hq 131)) (reverse_move q (hq 107)) (Eq.symm h0)
    exact branch44 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans hit (Eq.symm t0))
  · have t0 := move_eq p (hp 77) (hp 39) (Eq.symm hit)
    exact branch35 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · exact branch46 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 0)) hit
    exact branch16 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq q.symm (reverse_move q (hq 131)) (reverse_move q (hq 107)) (Eq.symm h0)
    have t1 := move_eq p (hp 107) (hp 77) hit
    have t2 := move_eq p.symm (reverse_move p (hp 160)) (reverse_move p (hp 107)) (Eq.trans (Eq.symm t0) (Eq.symm t1))
    have t3 := move_eq p (hp 160) (hp 48) (Eq.trans (Eq.trans t2 (Eq.symm t0)) (Eq.symm t1))
    have t4 := move_eq p (hp 48) (hp 15) (Eq.trans (Eq.trans t1 t0) t3)
    have t5 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 15)) (Eq.trans (Eq.trans (Eq.symm hit) t3) t4)
    have t6 := move_eq q (hq 25) (hq 4) (Eq.trans t5 t4)
    exact branch4 p q v hp hq sep (Eq.symm t6)
  · have t0 := move_eq q (hq 107) (hq 25) hit
    exact branch46 p q v hp hq sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq q (hq 107) (hq 7) hit
    have t1 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 0)) t0
    exact branch16 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq q.symm (reverse_move q (hq 131)) (reverse_move q (hq 107)) (Eq.symm h0)
    have t1 := move_eq p (hp 107) (hp 77) hit
    have t2 := move_eq p.symm (reverse_move p (hp 160)) (reverse_move p (hp 107)) (Eq.trans (Eq.symm t0) (Eq.symm t1))
    have t3 := move_eq p (hp 160) (hp 48) (Eq.trans (Eq.trans t2 (Eq.symm t0)) (Eq.symm t1))
    have t4 := move_eq p (hp 48) (hp 15) (Eq.trans (Eq.trans t1 t0) t3)
    have t5 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 15)) (Eq.trans (Eq.trans (Eq.symm hit) t3) t4)
    have t6 := move_eq q (hq 25) (hq 4) (Eq.trans t5 t4)
    exact branch4 p q v hp hq sep (Eq.symm t6)
  · have t0 := move_eq q (hq 107) (hq 7) hit
    have t1 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 0)) t0
    exact branch16 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq q.symm (reverse_move q (hq 131)) (reverse_move q (hq 107)) (Eq.symm h0)
    have t1 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 0)) (Eq.trans t0 hit)
    exact branch31 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq q.symm (reverse_move q (hq 131)) (reverse_move q (hq 107)) (Eq.symm h0)
    have t1 := move_eq p (hp 77) (hp 25) hit
    have t2 := move_eq q (hq 107) (hq 25) (Eq.trans (Eq.trans (Eq.symm t0) t1) hit)
    exact branch46 p q v hp hq sep G e₀ e₁ e₂ no t2
  · exact branch48 p q v hp hq sep h0 hit
  · exact branch48 p q v hp hq sep h0 hit
  · have t0 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 0)) hit
    have t1 := move_eq q (hq 25) (hq 0) t0
    exact branch13 p q v hp hq sep G e₀ e₁ e₂ no t1
  · have t0 := move_eq q (hq 25) (hq 7) hit
    have t1 := move_eq p.symm (reverse_move p (hp 24)) (reverse_move p (hp 0)) t0
    exact branch5 p q v hp hq sep (Eq.symm t1)
  · have t0 := move_eq p.symm (reverse_move p (hp 24)) (reverse_move p (hp 0)) hit
    exact branch5 p q v hp hq sep (Eq.symm t0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch49 (h0 : v 106 = v 142) : False := by
  rcases collision16 (fun h => no (.inr (.inr (.inl h))))
    (v 0) (v 0) (v 3) (v 3) (v 12) (v 12) (v 39) (v 39) (v 106) (v 106) (v 77) (v 77) (v 25) (v 7) (v 7) (v 1)
    (e₀ (v 0))
    ((hp 3) ▸ e₁ (v 3))
    (e₀ (v 3))
    ((hp 12) ▸ e₁ (v 12))
    (e₀ (v 12))
    ((hp 39) ▸ e₁ (v 39))
    (e₀ (v 39))
    ((hp 106) ▸ e₁ (v 106))
    (e₀ (v 106))
    ((Eq.trans (hp 77) (Eq.symm h0)) ▸ e₁ (v 77))
    (e₀ (v 77))
    ((hp 25) ▸ e₁ (v 25))
    ((hq 25) ▸ e₂ (v 25))
    (e₀ (v 7))
    ((hq 7) ▸ e₂ (v 7))
    ((hp 0) ▸ e₁ (v 0)) with hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit
  · exact branch1 p q v hp sep hit
  · exact branch2 p q v hp sep G e₀ e₁ e₂ no hit
  · exact branch3 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch16 p q v hp sep G e₀ e₁ e₂ no hit
  · exact branch31 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq q (hq 25) (hq 0) (Eq.symm hit)
    exact branch13 p q v hp hq sep G e₀ e₁ e₂ no t0
  · exact branch4 p q v hp hq sep hit
  · exact branch1 p q v hp sep hit
  · exact branch2 p q v hp sep G e₀ e₁ e₂ no hit
  · exact branch3 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch16 p q v hp sep G e₀ e₁ e₂ no hit
  · exact branch31 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch4 p q v hp hq sep hit
  · have t0 := move_eq p.symm (reverse_move p (hp 0)) (reverse_move p (hp 3)) (Eq.symm hit)
    exact branch1 p q v hp sep t0
  · have t0 := move_eq p (hp 12) (hp 3) (Eq.symm hit)
    exact branch1 p q v hp sep (Eq.symm t0)
  · have t0 := move_eq p (hp 39) (hp 3) (Eq.symm hit)
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t0)
  · exact branch33 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans hit h0)
  · have t0 := move_eq p (hp 77) (hp 3) (Eq.symm hit)
    exact branch30 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 25) (hp 3) (Eq.symm hit)
    exact branch31 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 7) (hp 3) (Eq.symm hit)
    exact branch6 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 12) (hp 3) (Eq.symm hit)
    exact branch1 p q v hp sep (Eq.symm t0)
  · have t0 := move_eq p (hp 39) (hp 3) (Eq.symm hit)
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t0)
  · exact branch33 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans hit h0)
  · have t0 := move_eq p (hp 77) (hp 3) (Eq.symm hit)
    exact branch30 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 7) (hp 3) (Eq.symm hit)
    exact branch6 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 12)) (reverse_move p (hp 0)) hit
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 39) (hp 12) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 12)) (Eq.trans (Eq.symm hit) t0)
    exact branch35 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t1) h0)
  · exact branch35 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans hit h0)
  · have t0 := move_eq p (hp 77) (hp 12) (Eq.symm hit)
    exact branch33 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 25) (hp 12) (Eq.symm hit)
    have t1 := move_eq p (hp 77) (hp 3) t0
    exact branch30 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · exact branch39 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p (hp 39) (hp 12) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 12)) (Eq.trans (Eq.symm hit) t0)
    exact branch35 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t1) h0)
  · exact branch35 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans hit h0)
  · have t0 := move_eq p (hp 77) (hp 12) (Eq.symm hit)
    exact branch33 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · exact branch39 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 0)) hit
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · exact branch44 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans hit h0)
  · have t0 := move_eq p (hp 77) (hp 39) (Eq.symm hit)
    exact branch35 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 39) (hp 25) hit
    have t1 := move_eq p (hp 77) (hp 12) (Eq.symm t0)
    exact branch33 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · exact branch46 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch44 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans hit h0)
  · have t0 := move_eq p (hp 77) (hp 39) (Eq.symm hit)
    exact branch35 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · exact branch46 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 0)) hit
    exact branch16 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 106) (hp 77) hit
    exact branch44 p q v hp hq sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq p.symm (reverse_move p (hp 158)) (reverse_move p (hp 78)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 78)) (Eq.trans (Eq.symm h0) hit)
    have t2 := move_eq p (hp 106) (hp 25) hit
    have t3 := move_eq p (hp 158) (hp 39) (Eq.trans (Eq.trans t0 (Eq.symm t1)) (Eq.symm t2))
    exact branch35 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t3) h0)
  · have t0 := move_eq q (hq 131) (hq 7) (Eq.trans (Eq.symm h0) hit)
    have t1 := move_eq p.symm (reverse_move p (hp 19)) (reverse_move p (hp 0)) t0
    exact branch29 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p (hp 106) (hp 77) hit
    exact branch44 p q v hp hq sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq q (hq 131) (hq 7) (Eq.trans (Eq.symm h0) hit)
    have t1 := move_eq p.symm (reverse_move p (hp 19)) (reverse_move p (hp 0)) t0
    exact branch29 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 0)) (Eq.trans (Eq.symm h0) hit)
    exact branch31 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 77) (hp 25) hit
    have t1 := move_eq p (hp 106) (hp 25) (Eq.trans (Eq.trans h0 t0) hit)
    exact branch44 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans t1 (Eq.symm t0))
  · have t0 := move_eq p (hp 77) (hp 7) hit
    have t1 := move_eq q.symm (reverse_move q (hq 140)) (reverse_move q (hq 25)) hit
    have t2 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 24)) hit
    have t3 := move_eq q (hq 140) (hq 24) (Eq.trans t1 t2)
    have t4 := move_eq p (hp 74) (hp 7) (Eq.trans (Eq.symm t3) hit)
    have t5 := move_eq q (hq 77) (hq 7) hit
    have t6 := move_eq q (hq 134) (hq 1) t5
    have t7 := move_eq p.symm (reverse_move p (hp 129)) (reverse_move p (hp 22)) t6
    have t8 := move_eq q (hq 74) (hq 7) (Eq.trans (Eq.symm t3) hit)
    have t9 := move_eq q (hq 135) (hq 1) t8
    have t10 := move_eq p.symm (reverse_move p (hp 32)) (reverse_move p (hp 22)) t9
    have t11 := move_eq p (hp 106) (hp 23) (Eq.trans h0 t0)
    have t12 := move_eq p (hp 71) (hp 39) (Eq.symm t11)
    have t13 := move_eq q (hq 127) (hq 12) t12
    have t14 := move_eq q (hq 53) (hq 38) t13
    have t15 := move_eq q (hq 71) (hq 39) (Eq.symm t11)
    have t16 := move_eq p (hp 64) (hp 6) t6
    have t17 := move_eq p (hp 96) (hp 20) (Eq.trans (Eq.symm t15) t16)
    have t18 := move_eq p (hp 62) (hp 33) (Eq.symm t17)
    have t19 := move_eq p (hp 94) (hp 10) (Eq.trans (Eq.symm t14) t18)
    have t20 := move_eq q.symm (reverse_move q (hq 154)) (reverse_move q (hq 0)) (Eq.trans (Eq.trans (Eq.trans (Eq.trans (Eq.trans h0 t0) (Eq.symm t4)) t7) (Eq.symm t10)) t19)
    exact branch17 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t20)
  · have t0 := move_eq p (hp 77) (hp 7) hit
    have t1 := move_eq q.symm (reverse_move q (hq 140)) (reverse_move q (hq 25)) hit
    have t2 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 24)) hit
    have t3 := move_eq q (hq 140) (hq 24) (Eq.trans t1 t2)
    have t4 := move_eq p (hp 74) (hp 7) (Eq.trans (Eq.symm t3) hit)
    have t5 := move_eq q (hq 77) (hq 7) hit
    have t6 := move_eq q (hq 134) (hq 1) t5
    have t7 := move_eq p.symm (reverse_move p (hp 129)) (reverse_move p (hp 22)) t6
    have t8 := move_eq q (hq 74) (hq 7) (Eq.trans (Eq.symm t3) hit)
    have t9 := move_eq q (hq 135) (hq 1) t8
    have t10 := move_eq p.symm (reverse_move p (hp 32)) (reverse_move p (hp 22)) t9
    have t11 := move_eq p (hp 106) (hp 23) (Eq.trans h0 t0)
    have t12 := move_eq p (hp 71) (hp 39) (Eq.symm t11)
    have t13 := move_eq q (hq 127) (hq 12) t12
    have t14 := move_eq q (hq 53) (hq 38) t13
    have t15 := move_eq q (hq 71) (hq 39) (Eq.symm t11)
    have t16 := move_eq p (hp 64) (hp 6) t6
    have t17 := move_eq p (hp 96) (hp 20) (Eq.trans (Eq.symm t15) t16)
    have t18 := move_eq p (hp 62) (hp 33) (Eq.symm t17)
    have t19 := move_eq p (hp 94) (hp 10) (Eq.trans (Eq.symm t14) t18)
    have t20 := move_eq q.symm (reverse_move q (hq 154)) (reverse_move q (hq 0)) (Eq.trans (Eq.trans (Eq.trans (Eq.trans (Eq.trans h0 t0) (Eq.symm t4)) t7) (Eq.symm t10)) t19)
    exact branch17 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t20)
  · have t0 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 0)) hit
    have t1 := move_eq q (hq 25) (hq 0) t0
    exact branch13 p q v hp hq sep G e₀ e₁ e₂ no t1
  · have t0 := move_eq q (hq 25) (hq 7) hit
    have t1 := move_eq p.symm (reverse_move p (hp 24)) (reverse_move p (hp 0)) t0
    exact branch5 p q v hp hq sep (Eq.symm t1)
  · have t0 := move_eq p.symm (reverse_move p (hp 24)) (reverse_move p (hp 0)) hit
    exact branch5 p q v hp hq sep (Eq.symm t0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch50 (h0 : v 106 = v 7) : False := by
  have t0 := move_eq p (hp 106) (hp 7) h0
  have t1 := move_eq p (hp 39) (hp 23) t0
  rcases collision16 (fun h => no (.inr (.inr (.inl h))))
    (v 0) (v 0) (v 3) (v 3) (v 12) (v 12) (v 23) (v 72) (v 165) (v 165) (v 98) (v 98) (v 34) (v 10) (v 10) (v 2)
    (e₀ (v 0))
    ((hp 3) ▸ e₁ (v 3))
    (e₀ (v 3))
    ((hp 12) ▸ e₁ (v 12))
    (e₀ (v 12))
    ((Eq.trans (hp 23) (Eq.symm t1)) ▸ e₁ (v 23))
    ((hq 23) ▸ e₂ (v 23))
    ((hp 132) ▸ e₁ (v 165))
    (e₀ (v 165))
    ((hp 98) ▸ e₁ (v 98))
    (e₀ (v 98))
    ((hp 34) ▸ e₁ (v 34))
    ((hq 34) ▸ e₂ (v 34))
    (e₀ (v 10))
    ((hp 10) ▸ e₁ (v 10))
    ((hq 0) ▸ e₂ (v 0)) with hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit
  · exact branch1 p q v hp sep hit
  · exact branch2 p q v hp sep G e₀ e₁ e₂ no hit
  · exact branch6 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p (hp 106) (hp 7) h0
    have t1 := move_eq p (hp 132) (hp 0) (Eq.symm hit)
    have t2 := move_eq q.symm (reverse_move q (hq 23)) (reverse_move q (hq 7)) t1
    exact branch46 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans t0 t2)
  · have t0 := move_eq q.symm (reverse_move q (hq 154)) (reverse_move q (hq 25)) h0
    have t1 := move_eq p (hp 159) (hp 25) t0
    have t2 := move_eq p (hp 111) (hp 77) t1
    have t3 := move_eq p.symm (reverse_move p (hp 34)) (reverse_move p (hp 3)) (Eq.symm hit)
    have t4 := move_eq q.symm (reverse_move q (hq 75)) (reverse_move q (hq 13)) t3
    have t5 := move_eq p.symm (reverse_move p (hp 40)) (reverse_move p (hp 42)) t4
    have t6 := move_eq q (hq 131) (hq 40) (Eq.trans (Eq.symm t2) (Eq.symm t5))
    exact branch40 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t6)
  · have t0 := move_eq q (hq 34) (hq 0) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 33)) (reverse_move p (hp 10)) t0
    have t2 := move_eq q.symm (reverse_move q (hq 97)) (reverse_move q (hq 0)) (Eq.trans t1 t0)
    have t3 := move_eq q.symm (reverse_move q (hq 75)) (reverse_move q (hq 4)) (Eq.symm hit)
    have t4 := move_eq p.symm (reverse_move p (hp 40)) (reverse_move p (hp 15)) t3
    have t5 := move_eq q (hq 40) (hq 15) t4
    have t6 := move_eq p.symm (reverse_move p (hp 97)) (reverse_move p (hp 39)) (Eq.symm t5)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t2) t6)
  · have t0 := move_eq q (hq 10) (hq 0) (Eq.symm hit)
    have t1 := move_eq p (hp 10) (hp 0) (Eq.symm hit)
    have t2 := move_eq q.symm (reverse_move q (hq 10)) (reverse_move q (hq 7)) (Eq.trans t0 t1)
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · exact branch1 p q v hp sep hit
  · exact branch2 p q v hp sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq q.symm (reverse_move q (hq 23)) (reverse_move q (hq 4)) (Eq.symm hit)
    have t1 := move_eq p (hp 106) (hp 7) h0
    have t2 := move_eq q.symm (reverse_move q (hq 107)) (reverse_move q (hq 16)) (Eq.trans t1 t0)
    have t3 := move_eq p.symm (reverse_move p (hp 160)) (reverse_move p (hp 51)) t2
    have t4 := move_eq q.symm (reverse_move q (hq 73)) (reverse_move q (hq 16)) t0
    have t5 := move_eq p.symm (reverse_move p (hp 50)) (reverse_move p (hp 51)) t4
    have t6 := move_eq p (hp 107) (hp 16) t2
    have t7 := move_eq p (hp 160) (hp 48) (Eq.trans (Eq.trans t3 (Eq.symm t5)) (Eq.symm t6))
    have t8 := move_eq p.symm (reverse_move p (hp 7)) (reverse_move p (hp 15)) t0
    have t9 := move_eq q (hq 16) (hq 7) (Eq.trans (Eq.trans (Eq.symm t2) t7) (Eq.symm t8))
    have t10 := move_eq p.symm (reverse_move p (hp 7)) (reverse_move p (hp 0)) (Eq.trans t0 t9)
    exact branch4 p q v hp hq sep (Eq.symm t10)
  · have t0 := move_eq p (hp 106) (hp 7) h0
    have t1 := move_eq p (hp 132) (hp 0) (Eq.symm hit)
    have t2 := move_eq q.symm (reverse_move q (hq 23)) (reverse_move q (hq 7)) t1
    exact branch46 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans t0 t2)
  · have t0 := move_eq q.symm (reverse_move q (hq 154)) (reverse_move q (hq 25)) h0
    have t1 := move_eq p (hp 159) (hp 25) t0
    have t2 := move_eq p (hp 111) (hp 77) t1
    have t3 := move_eq p.symm (reverse_move p (hp 34)) (reverse_move p (hp 3)) (Eq.symm hit)
    have t4 := move_eq q.symm (reverse_move q (hq 75)) (reverse_move q (hq 13)) t3
    have t5 := move_eq p.symm (reverse_move p (hp 40)) (reverse_move p (hp 42)) t4
    have t6 := move_eq q (hq 131) (hq 40) (Eq.trans (Eq.symm t2) (Eq.symm t5))
    exact branch40 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t6)
  · have t0 := move_eq q (hq 10) (hq 0) (Eq.symm hit)
    have t1 := move_eq p (hp 10) (hp 0) (Eq.symm hit)
    have t2 := move_eq q.symm (reverse_move q (hq 10)) (reverse_move q (hq 7)) (Eq.trans t0 t1)
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · exact branch8 p q v hq sep hit
  · have t0 := move_eq p (hp 12) (hp 3) (Eq.symm hit)
    exact branch1 p q v hp sep (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 7)) (reverse_move p (hp 12)) (Eq.symm hit)
    exact branch39 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 132) (hp 3) (Eq.symm hit)
    have t1 := move_eq q (hq 72) (hq 0) t0
    have t2 := move_eq p (hp 26) (hp 2) t1
    have t3 := move_eq p.symm (reverse_move p (hp 8)) (reverse_move p (hp 10)) t1
    have t4 := move_eq p.symm (reverse_move p (hp 98)) (reverse_move p (hp 12)) (Eq.symm hit)
    have t5 := move_eq p.symm (reverse_move p (hp 34)) (reverse_move p (hp 39)) t4
    have t6 := move_eq p (hp 106) (hp 7) h0
    have t7 := move_eq q.symm (reverse_move q (hq 23)) (reverse_move q (hq 4)) t0
    have t8 := move_eq q (hq 34) (hq 4) (Eq.trans (Eq.trans t5 t6) t7)
    have t9 := move_eq p.symm (reverse_move p (hp 26)) (reverse_move p (hp 3)) (Eq.trans (Eq.trans t2 t3) t8)
    exact branch10 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t9) t1)
  · have t0 := move_eq p (hp 106) (hp 7) h0
    have t1 := move_eq p (hp 98) (hp 3) (Eq.symm hit)
    have t2 := move_eq p (hp 132) (hp 0) t1
    have t3 := move_eq q.symm (reverse_move q (hq 23)) (reverse_move q (hq 7)) t2
    exact branch46 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans t0 t3)
  · have t0 := move_eq q.symm (reverse_move q (hq 75)) (reverse_move q (hq 13)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 40)) (reverse_move p (hp 42)) t0
    have t2 := move_eq p.symm (reverse_move p (hp 111)) (reverse_move p (hp 108)) (Eq.symm t1)
    have t3 := move_eq q.symm (reverse_move q (hq 154)) (reverse_move q (hq 25)) h0
    have t4 := move_eq p (hp 159) (hp 25) t3
    have t5 := move_eq p (hp 108) (hp 77) (Eq.trans (Eq.symm t2) t4)
    have t6 := move_eq q (hq 131) (hq 40) (Eq.symm t5)
    exact branch40 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t6)
  · have t0 := move_eq p (hp 10) (hp 3) (Eq.symm hit)
    exact branch8 p q v hq sep (Eq.symm t0)
  · have t0 := move_eq p (hp 12) (hp 3) (Eq.symm hit)
    exact branch1 p q v hp sep (Eq.symm t0)
  · have t0 := move_eq p (hp 106) (hp 7) h0
    have t1 := move_eq q.symm (reverse_move q (hq 23)) (reverse_move q (hq 13)) (Eq.symm hit)
    have t2 := move_eq p (hp 39) (hp 13) (Eq.trans t0 t1)
    have t3 := move_eq p (hp 41) (hp 12) (Eq.symm t2)
    have t4 := move_eq p (hp 60) (hp 3) t3
    exact branch29 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t4)
  · have t0 := move_eq p (hp 132) (hp 3) (Eq.symm hit)
    have t1 := move_eq q (hq 72) (hq 0) t0
    have t2 := move_eq p (hp 26) (hp 2) t1
    have t3 := move_eq p.symm (reverse_move p (hp 8)) (reverse_move p (hp 10)) t1
    have t4 := move_eq p.symm (reverse_move p (hp 98)) (reverse_move p (hp 12)) (Eq.symm hit)
    have t5 := move_eq p.symm (reverse_move p (hp 34)) (reverse_move p (hp 39)) t4
    have t6 := move_eq p (hp 106) (hp 7) h0
    have t7 := move_eq q.symm (reverse_move q (hq 23)) (reverse_move q (hq 4)) t0
    have t8 := move_eq q (hq 34) (hq 4) (Eq.trans (Eq.trans t5 t6) t7)
    have t9 := move_eq p.symm (reverse_move p (hp 26)) (reverse_move p (hp 3)) (Eq.trans (Eq.trans t2 t3) t8)
    exact branch10 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t9) t1)
  · have t0 := move_eq p (hp 106) (hp 7) h0
    have t1 := move_eq p (hp 98) (hp 3) (Eq.symm hit)
    have t2 := move_eq p (hp 132) (hp 0) t1
    have t3 := move_eq q.symm (reverse_move q (hq 23)) (reverse_move q (hq 7)) t2
    exact branch46 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans t0 t3)
  · have t0 := move_eq p (hp 10) (hp 3) (Eq.symm hit)
    exact branch8 p q v hq sep (Eq.symm t0)
  · exact branch10 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 7)) (reverse_move p (hp 39)) (Eq.symm hit)
    exact branch46 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 132) (hp 12) (Eq.symm hit)
    have t1 := move_eq q.symm (reverse_move q (hq 23)) (reverse_move q (hq 13)) t0
    have t2 := move_eq p.symm (reverse_move p (hp 7)) (reverse_move p (hp 42)) t1
    have t3 := move_eq q.symm (reverse_move q (hq 154)) (reverse_move q (hq 25)) h0
    have t4 := move_eq p (hp 159) (hp 25) t3
    have t5 := move_eq p (hp 111) (hp 77) t4
    exact branch49 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.trans h0 t2) t5)
  · have t0 := move_eq p (hp 98) (hp 12) (Eq.symm hit)
    have t1 := move_eq p (hp 132) (hp 3) t0
    have t2 := move_eq q (hq 72) (hq 0) t1
    have t3 := move_eq p.symm (reverse_move p (hp 34)) (reverse_move p (hp 39)) (Eq.symm hit)
    have t4 := move_eq p (hp 106) (hp 7) h0
    have t5 := move_eq q (hq 34) (hq 23) (Eq.trans t3 t4)
    have t6 := move_eq p (hp 10) (hp 0) (Eq.trans t5 t1)
    have t7 := move_eq q.symm (reverse_move q (hq 72)) (reverse_move q (hq 7)) (Eq.trans t2 t6)
    exact branch4 p q v hp hq sep (Eq.trans (Eq.symm t1) t7)
  · have t0 := move_eq q.symm (reverse_move q (hq 75)) (reverse_move q (hq 40)) (Eq.symm hit)
    have t1 := move_eq p (hp 75) (hp 40) t0
    have t2 := move_eq q (hq 75) (hq 24) (Eq.symm t1)
    have t3 := move_eq q (hq 34) (hq 12) (Eq.symm hit)
    have t4 := move_eq p (hp 38) (hp 10) (Eq.symm t3)
    have t5 := move_eq q.symm (reverse_move q (hq 136)) (reverse_move q (hq 0)) t4
    have t6 := move_eq p (hp 130) (hp 0) t5
    have t7 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 0)) (Eq.trans (Eq.trans hit t2) t6)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t7)
  · have t0 := move_eq p (hp 12) (hp 10) hit
    exact branch10 p q v hp hq sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq p.symm (reverse_move p (hp 158)) (reverse_move p (hp 24)) h0
    have t1 := move_eq q.symm (reverse_move q (hq 23)) (reverse_move q (hq 40)) (Eq.symm hit)
    have t2 := move_eq p (hp 40) (hp 23) (Eq.symm t1)
    have t3 := move_eq p.symm (reverse_move p (hp 132)) (reverse_move p (hp 39)) (Eq.symm hit)
    have t4 := move_eq p (hp 106) (hp 7) h0
    have t5 := move_eq p (hp 132) (hp 23) (Eq.trans t3 t4)
    have t6 := move_eq p (hp 75) (hp 12) (Eq.trans (Eq.trans t2 (Eq.symm t5)) (Eq.symm hit))
    have t7 := move_eq p (hp 158) (hp 3) (Eq.trans t0 t6)
    exact branch16 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t7)
  · have t0 := move_eq p (hp 132) (hp 12) (Eq.symm hit)
    have t1 := move_eq q.symm (reverse_move q (hq 23)) (reverse_move q (hq 13)) t0
    have t2 := move_eq p.symm (reverse_move p (hp 7)) (reverse_move p (hp 42)) t1
    have t3 := move_eq q.symm (reverse_move q (hq 154)) (reverse_move q (hq 25)) h0
    have t4 := move_eq p (hp 159) (hp 25) t3
    have t5 := move_eq p (hp 111) (hp 77) t4
    exact branch49 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.trans h0 t2) t5)
  · have t0 := move_eq p (hp 98) (hp 12) (Eq.symm hit)
    have t1 := move_eq p (hp 132) (hp 3) t0
    have t2 := move_eq q (hq 72) (hq 0) t1
    have t3 := move_eq p.symm (reverse_move p (hp 34)) (reverse_move p (hp 39)) (Eq.symm hit)
    have t4 := move_eq p (hp 106) (hp 7) h0
    have t5 := move_eq q (hq 34) (hq 23) (Eq.trans t3 t4)
    have t6 := move_eq p (hp 10) (hp 0) (Eq.trans t5 t1)
    have t7 := move_eq q.symm (reverse_move q (hq 72)) (reverse_move q (hq 7)) (Eq.trans t2 t6)
    exact branch4 p q v hp hq sep (Eq.trans (Eq.symm t1) t7)
  · have t0 := move_eq p (hp 12) (hp 10) hit
    exact branch10 p q v hp hq sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq q (hq 12) (hq 2) hit
    have t1 := move_eq p.symm (reverse_move p (hp 105)) (reverse_move p (hp 31)) t0
    have t2 := move_eq q.symm (reverse_move q (hq 153)) (reverse_move q (hq 92)) t1
    have t3 := move_eq q.symm (reverse_move q (hq 111)) (reverse_move q (hq 47)) t2
    have t4 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 10)) hit
    have t5 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 33)) t4
    have t6 := move_eq q.symm (reverse_move q (hq 97)) (reverse_move q (hq 25)) (Eq.trans (Eq.symm t5) h0)
    have t7 := move_eq p.symm (reverse_move p (hp 158)) (reverse_move p (hp 24)) h0
    have t8 := move_eq q.symm (reverse_move q (hq 40)) (reverse_move q (hq 0)) hit
    have t9 := move_eq p (hp 40) (hp 0) t8
    have t10 := move_eq p (hp 75) (hp 1) t9
    have t11 := move_eq p (hp 158) (hp 5) (Eq.trans t7 t10)
    have t12 := move_eq q.symm (reverse_move q (hq 55)) (reverse_move q (hq 25)) (Eq.trans (Eq.symm t11) h0)
    have t13 := move_eq q.symm (reverse_move q (hq 128)) (reverse_move q (hq 79)) t12
    have t14 := move_eq p (hp 106) (hp 7) h0
    have t15 := move_eq q.symm (reverse_move q (hq 73)) (reverse_move q (hq 34)) (Eq.trans (Eq.symm t14) t4)
    have t16 := move_eq p (hp 17) (hp 7) (Eq.trans (Eq.symm t11) h0)
    have t17 := move_eq q.symm (reverse_move q (hq 127)) (reverse_move q (hq 34)) (Eq.trans (Eq.trans t16 (Eq.symm t14)) t4)
    have t18 := move_eq p (hp 23) (hp 10) (Eq.trans (Eq.symm t14) t4)
    have t19 := move_eq p (hp 71) (hp 2) t18
    have t20 := move_eq p (hp 12) (hp 2) hit
    have t21 := move_eq p (hp 73) (hp 3) (Eq.trans (Eq.trans (Eq.trans t15 (Eq.symm t17)) t19) (Eq.symm t20))
    have t22 := move_eq q (hq 79) (hq 0) (Eq.trans (Eq.symm t13) t21)
    have t23 := move_eq p (hp 97) (hp 2) (Eq.trans t6 t22)
    have t24 := move_eq p (hp 111) (hp 3) (Eq.trans (Eq.trans t3 t23) (Eq.symm t20))
    exact branch26 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t24)
  · have t0 := move_eq p.symm (reverse_move p (hp 98)) (reverse_move p (hp 7)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 34)) (reverse_move p (hp 24)) t0
    have t2 := move_eq q (hq 34) (hq 24) t1
    have t3 := move_eq p (hp 106) (hp 7) h0
    have t4 := move_eq q (hq 39) (hq 23) t3
    have t5 := move_eq p (hp 132) (hp 23) (Eq.symm hit)
    have t6 := move_eq p (hp 39) (hp 23) t3
    have t7 := move_eq p (hp 96) (hp 12) (Eq.trans (Eq.trans t4 t5) (Eq.symm t6))
    have t8 := move_eq p (hp 33) (hp 3) t7
    have t9 := move_eq q (hq 74) (hq 0) (Eq.trans (Eq.symm t2) t8)
    have t10 := move_eq q (hq 71) (hq 12) (Eq.symm t6)
    have t11 := move_eq q (hq 72) (hq 12) (Eq.trans t5 (Eq.symm t6))
    have t12 := move_eq p.symm (reverse_move p (hp 64)) (reverse_move p (hp 8)) (Eq.trans t10 (Eq.symm t11))
    have t13 := move_eq p.symm (reverse_move p (hp 129)) (reverse_move p (hp 2)) t12
    have t14 := move_eq p (hp 74) (hp 0) (Eq.trans (Eq.symm t2) t8)
    have t15 := move_eq q.symm (reverse_move q (hq 74)) (reverse_move q (hq 7)) (Eq.trans (Eq.trans t9 (Eq.symm t13)) t14)
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t15) (Eq.symm t2))
  · have t0 := move_eq p.symm (reverse_move p (hp 34)) (reverse_move p (hp 7)) (Eq.symm hit)
    have t1 := move_eq q.symm (reverse_move q (hq 75)) (reverse_move q (hq 25)) t0
    have t2 := move_eq p (hp 75) (hp 25) t1
    have t3 := move_eq p (hp 77) (hp 24) (Eq.symm t2)
    exact branch49 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans h0 (Eq.symm t3))
  · have t0 := move_eq p (hp 34) (hp 23) (Eq.symm hit)
    have t1 := move_eq p (hp 98) (hp 71) t0
    have t2 := move_eq q (hq 34) (hq 23) (Eq.symm hit)
    have t3 := move_eq p.symm (reverse_move p (hp 132)) (reverse_move p (hp 33)) (Eq.symm t2)
    have t4 := move_eq p.symm (reverse_move p (hp 71)) (reverse_move p (hp 96)) (Eq.trans (Eq.symm t1) t3)
    have t5 := move_eq p (hp 106) (hp 7) h0
    have t6 := move_eq q (hq 39) (hq 23) t5
    have t7 := move_eq p.symm (reverse_move p (hp 23)) (reverse_move p (hp 33)) (Eq.trans (Eq.trans t4 t6) (Eq.symm t2))
    have t8 := move_eq p (hp 71) (hp 10) (Eq.trans (Eq.trans t4 t6) (Eq.symm t2))
    have t9 := move_eq p.symm (reverse_move p (hp 7)) (reverse_move p (hp 10)) (Eq.trans (Eq.trans (Eq.trans t7 (Eq.symm t3)) t1) t8)
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no t9
  · have t0 := move_eq p.symm (reverse_move p (hp 7)) (reverse_move p (hp 33)) hit
    have t1 := move_eq q.symm (reverse_move q (hq 97)) (reverse_move q (hq 25)) (Eq.symm t0)
    have t2 := move_eq p (hp 97) (hp 25) t1
    have t3 := move_eq q (hq 23) (hq 10) hit
    have t4 := move_eq p.symm (reverse_move p (hp 132)) (reverse_move p (hp 94)) t3
    have t5 := move_eq p.symm (reverse_move p (hp 98)) (reverse_move p (hp 145)) t4
    have t6 := move_eq p (hp 106) (hp 7) h0
    have t7 := move_eq q (hq 39) (hq 10) (Eq.trans t6 hit)
    have t8 := move_eq p.symm (reverse_move p (hp 96)) (reverse_move p (hp 24)) (Eq.symm t0)
    have t9 := move_eq p.symm (reverse_move p (hp 132)) (reverse_move p (hp 75)) (Eq.trans (Eq.trans t3 (Eq.symm t7)) t8)
    have t10 := move_eq p.symm (reverse_move p (hp 145)) (reverse_move p (hp 40)) (Eq.trans (Eq.symm t4) t9)
    have t11 := move_eq q (hq 98) (hq 40) (Eq.trans t5 t10)
    have t12 := move_eq p (hp 39) (hp 10) (Eq.trans t6 hit)
    have t13 := move_eq q (hq 144) (hq 2) (Eq.trans t11 t12)
    have t14 := move_eq q (hq 72) (hq 32) t3
    have t15 := move_eq p (hp 93) (hp 26) (Eq.symm t14)
    have t16 := move_eq q.symm (reverse_move q (hq 82)) (reverse_move q (hq 17)) t15
    have t17 := move_eq p.symm (reverse_move p (hp 158)) (reverse_move p (hp 24)) h0
    have t18 := move_eq p.symm (reverse_move p (hp 147)) (reverse_move p (hp 75)) t8
    have t19 := move_eq q.symm (reverse_move q (hq 98)) (reverse_move q (hq 0)) (Eq.trans t11 t12)
    have t20 := move_eq p (hp 145) (hp 0) (Eq.trans (Eq.symm t5) t19)
    have t21 := move_eq p (hp 147) (hp 1) (Eq.trans (Eq.trans (Eq.trans t18 (Eq.symm t9)) t4) t20)
    have t22 := move_eq p (hp 158) (hp 5) (Eq.trans (Eq.trans t17 (Eq.symm t8)) t21)
    have t23 := move_eq q.symm (reverse_move q (hq 2)) (reverse_move q (hq 25)) (Eq.trans (Eq.trans (Eq.trans (Eq.symm t13) t16) (Eq.symm t22)) h0)
    have t24 := move_eq p (hp 25) (hp 2) (Eq.symm t23)
    have t25 := move_eq p (hp 12) (hp 2) t12
    have t26 := move_eq p (hp 47) (hp 3) (Eq.trans (Eq.trans t2 t24) (Eq.symm t25))
    have t27 := move_eq p (hp 77) (hp 47) (Eq.symm t2)
    exact branch30 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t26) (Eq.symm t27))
  · have t0 := move_eq p.symm (reverse_move p (hp 98)) (reverse_move p (hp 132)) (Eq.symm hit)
    have t1 := move_eq p (hp 132) (hp 72) (Eq.symm hit)
    have t2 := move_eq p (hp 106) (hp 7) h0
    have t3 := move_eq q (hq 39) (hq 23) t2
    have t4 := move_eq p (hp 96) (hp 72) t3
    have t5 := move_eq p (hp 98) (hp 33) (Eq.trans (Eq.trans (Eq.trans t0 (Eq.symm hit)) t1) (Eq.symm t4))
    have t6 := move_eq q.symm (reverse_move q (hq 147)) (reverse_move q (hq 34)) (Eq.trans t0 t5)
    have t7 := move_eq p.symm (reverse_move p (hp 34)) (reverse_move p (hp 33)) (Eq.trans t0 t5)
    have t8 := move_eq p (hp 132) (hp 10) t5
    have t9 := move_eq q (hq 147) (hq 2) (Eq.trans (Eq.trans (Eq.trans (Eq.trans t6 t7) t4) (Eq.symm t1)) t8)
    have t10 := move_eq q.symm (reverse_move q (hq 2)) (reverse_move q (hq 0)) (Eq.trans (Eq.trans (Eq.trans (Eq.symm t9) t0) (Eq.symm hit)) t8)
    exact branch8 p q v hq sep (Eq.symm t10)
  · have t0 := move_eq p (hp 98) (hp 72) (Eq.symm hit)
    have t1 := move_eq p (hp 106) (hp 7) h0
    have t2 := move_eq q (hq 39) (hq 23) t1
    have t3 := move_eq p (hp 96) (hp 72) t2
    have t4 := move_eq p (hp 132) (hp 33) (Eq.trans t0 (Eq.symm t3))
    have t5 := move_eq p (hp 72) (hp 10) t4
    have t6 := move_eq p (hp 132) (hp 2) (Eq.trans t0 t5)
    have t7 := move_eq p.symm (reverse_move p (hp 34)) (reverse_move p (hp 132)) (Eq.symm hit)
    have t8 := move_eq q (hq 34) (hq 33) (Eq.trans (Eq.trans t7 t0) (Eq.symm t3))
    have t9 := move_eq q (hq 98) (hq 72) (Eq.symm hit)
    have t10 := move_eq q (hq 144) (hq 26) t9
    have t11 := move_eq p.symm (reverse_move p (hp 136)) (reverse_move p (hp 21)) t10
    have t12 := move_eq p.symm (reverse_move p (hp 95)) (reverse_move p (hp 67)) t11
    have t13 := move_eq q (hq 67) (hq 10) (Eq.trans (Eq.symm t12) (Eq.symm t8))
    have t14 := move_eq p.symm (reverse_move p (hp 32)) (reverse_move p (hp 33)) (Eq.trans (Eq.symm t12) (Eq.symm t8))
    have t15 := move_eq q.symm (reverse_move q (hq 67)) (reverse_move q (hq 0)) (Eq.trans (Eq.trans (Eq.trans t13 t14) t3) t5)
    have t16 := move_eq p.symm (reverse_move p (hp 2)) (reverse_move p (hp 3)) (Eq.trans (Eq.trans (Eq.trans (Eq.trans (Eq.symm t6) t4) t8) t12) t15)
    exact branch10 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t16)
  · have t0 := move_eq q.symm (reverse_move q (hq 23)) (reverse_move q (hq 34)) hit
    have t1 := move_eq p (hp 34) (hp 23) (Eq.symm t0)
    have t2 := move_eq p.symm (reverse_move p (hp 132)) (reverse_move p (hp 33)) hit
    have t3 := move_eq p.symm (reverse_move p (hp 98)) (reverse_move p (hp 96)) t2
    have t4 := move_eq p (hp 106) (hp 7) h0
    have t5 := move_eq q (hq 39) (hq 23) t4
    have t6 := move_eq p.symm (reverse_move p (hp 23)) (reverse_move p (hp 33)) (Eq.trans (Eq.trans (Eq.trans (Eq.symm t1) t3) t5) hit)
    have t7 := move_eq p (hp 96) (hp 10) (Eq.trans t5 hit)
    have t8 := move_eq p.symm (reverse_move p (hp 7)) (reverse_move p (hp 10)) (Eq.trans t6 t7)
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no t8
  · have t0 := move_eq q.symm (reverse_move q (hq 23)) (reverse_move q (hq 0)) hit
    exact branch6 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 132) (hp 98) hit
    have t1 := move_eq p (hp 98) (hp 72) (Eq.trans (Eq.symm hit) (Eq.symm t0))
    have t2 := move_eq p (hp 106) (hp 7) h0
    have t3 := move_eq q (hq 39) (hq 23) t2
    have t4 := move_eq p (hp 96) (hp 72) t3
    have t5 := move_eq p (hp 132) (hp 33) (Eq.trans t1 (Eq.symm t4))
    have t6 := move_eq p.symm (reverse_move p (hp 147)) (reverse_move p (hp 132)) t3
    have t7 := move_eq p (hp 147) (hp 10) (Eq.trans (Eq.trans t6 (Eq.symm t0)) t5)
    have t8 := move_eq q.symm (reverse_move q (hq 34)) (reverse_move q (hq 0)) (Eq.trans (Eq.trans (Eq.symm t5) (Eq.symm t3)) t7)
    have t9 := move_eq p.symm (reverse_move p (hp 34)) (reverse_move p (hp 96)) (Eq.trans (Eq.trans (Eq.symm hit) t1) (Eq.symm t4))
    exact branch8 p q v hq sep (Eq.trans (Eq.trans (Eq.symm t8) t9) t7)
  · have t0 := move_eq p (hp 132) (hp 34) hit
    have t1 := move_eq p (hp 98) (hp 72) (Eq.symm t0)
    have t2 := move_eq p (hp 106) (hp 7) h0
    have t3 := move_eq q (hq 39) (hq 23) t2
    have t4 := move_eq p (hp 96) (hp 72) t3
    have t5 := move_eq p (hp 132) (hp 33) (Eq.trans t1 (Eq.symm t4))
    have t6 := move_eq q.symm (reverse_move q (hq 23)) (reverse_move q (hq 34)) t5
    have t7 := move_eq p (hp 72) (hp 10) t5
    have t8 := move_eq p.symm (reverse_move p (hp 7)) (reverse_move p (hp 10)) (Eq.trans (Eq.trans (Eq.trans t6 (Eq.symm hit)) t1) t7)
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no t8
  · have t0 := move_eq p (hp 132) (hp 10) hit
    have t1 := move_eq q.symm (reverse_move q (hq 23)) (reverse_move q (hq 0)) t0
    exact branch6 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p (hp 132) (hp 98) hit
    have t1 := move_eq p (hp 98) (hp 72) (Eq.trans (Eq.symm hit) (Eq.symm t0))
    have t2 := move_eq p (hp 106) (hp 7) h0
    have t3 := move_eq q (hq 39) (hq 23) t2
    have t4 := move_eq p (hp 96) (hp 72) t3
    have t5 := move_eq p (hp 132) (hp 33) (Eq.trans t1 (Eq.symm t4))
    have t6 := move_eq p.symm (reverse_move p (hp 147)) (reverse_move p (hp 132)) t3
    have t7 := move_eq p (hp 147) (hp 10) (Eq.trans (Eq.trans t6 (Eq.symm t0)) t5)
    have t8 := move_eq q.symm (reverse_move q (hq 34)) (reverse_move q (hq 0)) (Eq.trans (Eq.trans (Eq.symm t5) (Eq.symm t3)) t7)
    have t9 := move_eq p.symm (reverse_move p (hp 34)) (reverse_move p (hp 96)) (Eq.trans (Eq.trans (Eq.symm hit) t1) (Eq.symm t4))
    exact branch8 p q v hq sep (Eq.trans (Eq.trans (Eq.symm t8) t9) t7)
  · have t0 := move_eq p (hp 132) (hp 10) hit
    have t1 := move_eq q.symm (reverse_move q (hq 23)) (reverse_move q (hq 0)) t0
    exact branch6 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p (hp 132) (hp 2) hit
    have t1 := move_eq q (hq 72) (hq 8) t0
    have t2 := move_eq q (hq 27) (hq 26) (Eq.symm t1)
    have t3 := move_eq p.symm (reverse_move p (hp 98)) (reverse_move p (hp 10)) hit
    have t4 := move_eq q.symm (reverse_move q (hq 147)) (reverse_move q (hq 34)) t3
    have t5 := move_eq p.symm (reverse_move p (hp 34)) (reverse_move p (hp 33)) t3
    have t6 := move_eq p (hp 106) (hp 7) h0
    have t7 := move_eq q (hq 39) (hq 23) t6
    have t8 := move_eq p (hp 96) (hp 8) (Eq.trans t7 t0)
    have t9 := move_eq q (hq 147) (hq 26) (Eq.trans (Eq.trans t4 t5) t8)
    have t10 := move_eq p (hp 81) (hp 10) (Eq.trans (Eq.trans t2 (Eq.symm t9)) t3)
    have t11 := move_eq q.symm (reverse_move q (hq 86)) (reverse_move q (hq 0)) t10
    have t12 := move_eq p (hp 33) (hp 26) t8
    have t13 := move_eq q (hq 54) (hq 10) (Eq.symm t12)
    have t14 := move_eq q.symm (reverse_move q (hq 23)) (reverse_move q (hq 28)) t0
    have t15 := move_eq q.symm (reverse_move q (hq 85)) (reverse_move q (hq 73)) (Eq.symm t14)
    have t16 := move_eq p (hp 137) (hp 26) (Eq.trans (Eq.trans t4 t5) t8)
    have t17 := move_eq q (hq 73) (hq 10) (Eq.trans (Eq.trans (Eq.symm t15) t16) (Eq.symm t12))
    have t18 := move_eq p.symm (reverse_move p (hp 86)) (reverse_move p (hp 7)) (Eq.trans t13 (Eq.symm t17))
    exact branch4 p q v hp hq sep (Eq.trans (Eq.symm t11) t18)
  · have t0 := move_eq p.symm (reverse_move p (hp 34)) (reverse_move p (hp 99)) hit
    have t1 := move_eq p (hp 98) (hp 34) hit
    have t2 := move_eq p (hp 106) (hp 7) h0
    have t3 := move_eq q (hq 39) (hq 23) t2
    have t4 := move_eq p (hp 132) (hp 34) (Eq.trans t1 hit)
    have t5 := move_eq p (hp 96) (hp 34) (Eq.trans (Eq.trans t3 t4) hit)
    have t6 := move_eq p (hp 98) (hp 33) (Eq.symm t5)
    have t7 := move_eq p (hp 99) (hp 10) (Eq.trans (Eq.trans (Eq.trans (Eq.symm t0) (Eq.symm hit)) (Eq.symm t1)) t6)
    have t8 := move_eq q.symm (reverse_move q (hq 149)) (reverse_move q (hq 0)) (Eq.trans (Eq.symm t0) t7)
    have t9 := move_eq q.symm (reverse_move q (hq 149)) (reverse_move q (hq 75)) (Eq.symm t0)
    have t10 := move_eq q.symm (reverse_move q (hq 23)) (reverse_move q (hq 75)) (Eq.trans t4 hit)
    exact branch6 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.trans (Eq.symm t8) t9) (Eq.symm t10))
  · have t0 := move_eq q (hq 98) (hq 10) hit
    have t1 := move_eq q (hq 144) (hq 32) t0
    have t2 := move_eq p (hp 93) (hp 82) (Eq.symm t1)
    have t3 := move_eq p (hp 98) (hp 10) hit
    have t4 := move_eq p (hp 132) (hp 2) t3
    have t5 := move_eq q (hq 72) (hq 8) t4
    have t6 := move_eq p (hp 106) (hp 7) h0
    have t7 := move_eq q (hq 39) (hq 23) t6
    have t8 := move_eq p (hp 96) (hp 8) (Eq.trans t7 t4)
    have t9 := move_eq q.symm (reverse_move q (hq 147)) (reverse_move q (hq 34)) hit
    have t10 := move_eq p.symm (reverse_move p (hp 34)) (reverse_move p (hp 33)) hit
    have t11 := move_eq q (hq 147) (hq 26) (Eq.trans (Eq.trans t9 t10) t8)
    have t12 := move_eq p.symm (reverse_move p (hp 21)) (reverse_move p (hp 33)) (Eq.trans (Eq.symm t11) hit)
    have t13 := move_eq p (hp 137) (hp 33) (Eq.trans t9 t10)
    have t14 := move_eq q (hq 85) (hq 10) t13
    have t15 := move_eq q.symm (reverse_move q (hq 23)) (reverse_move q (hq 28)) t4
    have t16 := move_eq p (hp 32) (hp 23) (Eq.trans (Eq.symm t14) (Eq.symm t15))
    have t17 := move_eq p (hp 39) (hp 23) t6
    have t18 := move_eq p (hp 67) (hp 12) (Eq.trans t16 (Eq.symm t17))
    have t19 := move_eq q.symm (reverse_move q (hq 82)) (reverse_move q (hq 13)) (Eq.trans (Eq.trans (Eq.trans (Eq.trans t2 (Eq.symm t5)) (Eq.symm t8)) (Eq.symm t12)) t18)
    have t20 := move_eq p.symm (reverse_move p (hp 93)) (reverse_move p (hp 8)) (Eq.trans t2 (Eq.symm t5))
    have t21 := move_eq p (hp 13) (hp 8) (Eq.trans (Eq.trans (Eq.symm t19) t1) t20)
    have t22 := move_eq p (hp 41) (hp 3) (Eq.trans (Eq.trans (Eq.trans t21 (Eq.symm t8)) (Eq.symm t12)) t18)
    exact branch28 p q v hp hq sep (Eq.symm t22)
  · have t0 := move_eq q (hq 98) (hq 10) hit
    have t1 := move_eq q (hq 144) (hq 32) t0
    have t2 := move_eq p (hp 93) (hp 82) (Eq.symm t1)
    have t3 := move_eq p (hp 98) (hp 10) hit
    have t4 := move_eq p (hp 132) (hp 2) t3
    have t5 := move_eq q (hq 72) (hq 8) t4
    have t6 := move_eq p (hp 106) (hp 7) h0
    have t7 := move_eq q (hq 39) (hq 23) t6
    have t8 := move_eq p (hp 96) (hp 8) (Eq.trans t7 t4)
    have t9 := move_eq q.symm (reverse_move q (hq 147)) (reverse_move q (hq 34)) hit
    have t10 := move_eq p.symm (reverse_move p (hp 34)) (reverse_move p (hp 33)) hit
    have t11 := move_eq q (hq 147) (hq 26) (Eq.trans (Eq.trans t9 t10) t8)
    have t12 := move_eq p.symm (reverse_move p (hp 21)) (reverse_move p (hp 33)) (Eq.trans (Eq.symm t11) hit)
    have t13 := move_eq p (hp 137) (hp 33) (Eq.trans t9 t10)
    have t14 := move_eq q (hq 85) (hq 10) t13
    have t15 := move_eq q.symm (reverse_move q (hq 23)) (reverse_move q (hq 28)) t4
    have t16 := move_eq p (hp 32) (hp 23) (Eq.trans (Eq.symm t14) (Eq.symm t15))
    have t17 := move_eq p (hp 39) (hp 23) t6
    have t18 := move_eq p (hp 67) (hp 12) (Eq.trans t16 (Eq.symm t17))
    have t19 := move_eq q.symm (reverse_move q (hq 82)) (reverse_move q (hq 13)) (Eq.trans (Eq.trans (Eq.trans (Eq.trans t2 (Eq.symm t5)) (Eq.symm t8)) (Eq.symm t12)) t18)
    have t20 := move_eq p.symm (reverse_move p (hp 93)) (reverse_move p (hp 8)) (Eq.trans t2 (Eq.symm t5))
    have t21 := move_eq p (hp 13) (hp 8) (Eq.trans (Eq.trans (Eq.symm t19) t1) t20)
    have t22 := move_eq p (hp 41) (hp 3) (Eq.trans (Eq.trans (Eq.trans t21 (Eq.symm t8)) (Eq.symm t12)) t18)
    exact branch28 p q v hp hq sep (Eq.symm t22)
  · have t0 := move_eq p.symm (reverse_move p (hp 34)) (reverse_move p (hp 10)) hit
    have t1 := move_eq q.symm (reverse_move q (hq 75)) (reverse_move q (hq 34)) t0
    have t2 := move_eq p (hp 75) (hp 10) (Eq.trans t1 t0)
    exact branch15 p q v hp hq sep G e₀ e₁ e₂ no t2
  · have t0 := move_eq q.symm (reverse_move q (hq 75)) (reverse_move q (hq 34)) hit
    have t1 := move_eq p (hp 75) (hp 10) (Eq.trans t0 hit)
    exact branch15 p q v hp hq sep G e₀ e₁ e₂ no t1
  · have t0 := move_eq p.symm (reverse_move p (hp 33)) (reverse_move p (hp 10)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 96)) (reverse_move p (hp 10)) (Eq.trans t0 hit)
    have t2 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 0)) (Eq.trans t1 hit)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch51 (h0 : v 106 = v 59) : False := by
  have t0 := move_eq q.symm (reverse_move q (hq 154)) (reverse_move q (hq 131)) h0
  rcases collision16 (fun h => no (.inr (.inr (.inl h))))
    (v 0) (v 0) (v 3) (v 3) (v 13) (v 13) (v 42) (v 42) (v 111) (v 111) (v 142) (v 59) (v 19) (v 5) (v 1) (v 1)
    (e₀ (v 0))
    ((hp 3) ▸ e₁ (v 3))
    (e₀ (v 3))
    ((hq 13) ▸ e₂ (v 13))
    (e₀ (v 13))
    ((hp 42) ▸ e₁ (v 42))
    (e₀ (v 42))
    ((hp 111) ▸ e₁ (v 111))
    (e₀ (v 111))
    ((Eq.trans (congrArg p (Eq.symm t0)) (hp 159)) ▸ e₁ (v 142))
    ((hq 131) ▸ e₂ (v 142))
    ((hp 19) ▸ e₁ (v 19))
    ((hq 19) ▸ e₂ (v 19))
    ((hp 1) ▸ e₁ (v 1))
    (e₀ (v 1))
    ((hp 0) ▸ e₁ (v 0)) with hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit
  · exact branch1 p q v hp sep hit
  · have t0 := move_eq q (hq 13) (hq 0) (Eq.symm hit)
    exact branch10 p q v hp hq sep G e₀ e₁ e₂ no t0
  · exact branch26 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch25 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch30 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch29 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 0)) (reverse_move p (hp 3)) (Eq.symm hit)
    exact branch1 p q v hp sep t0
  · exact branch1 p q v hp sep hit
  · have t0 := move_eq q (hq 13) (hq 0) (Eq.symm hit)
    exact branch10 p q v hp hq sep G e₀ e₁ e₂ no t0
  · exact branch26 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch25 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch32 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 1)) (reverse_move p (hp 3)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 12)) (reverse_move p (hp 0)) (Eq.symm t0)
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p.symm (reverse_move p (hp 0)) (reverse_move p (hp 3)) (Eq.symm hit)
    exact branch1 p q v hp sep t0
  · have t0 := move_eq p (hp 13) (hp 3) (Eq.symm hit)
    exact branch27 p q v hp hq sep (Eq.symm t0)
  · have t0 := move_eq q.symm (reverse_move q (hq 112)) (reverse_move q (hq 13)) (Eq.symm hit)
    have t1 := move_eq p (hp 42) (hp 3) (Eq.symm hit)
    have t2 := move_eq q (hq 112) (hq 0) (Eq.trans t0 t1)
    exact branch10 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans hit t2)
  · have t0 := move_eq p (hp 111) (hp 3) (Eq.symm hit)
    exact branch26 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · exact branch33 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p (hp 19) (hp 3) (Eq.symm hit)
    exact branch32 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 12)) (reverse_move p (hp 0)) hit
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 13) (hp 3) (Eq.symm hit)
    exact branch27 p q v hp hq sep (Eq.symm t0)
  · have t0 := move_eq q.symm (reverse_move q (hq 112)) (reverse_move q (hq 13)) (Eq.symm hit)
    have t1 := move_eq p (hp 42) (hp 3) (Eq.symm hit)
    have t2 := move_eq q (hq 112) (hq 0) (Eq.trans t0 t1)
    exact branch10 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans hit t2)
  · have t0 := move_eq p (hp 111) (hp 3) (Eq.symm hit)
    exact branch26 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · exact branch34 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 1)) (reverse_move p (hp 12)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 0)) (Eq.symm t0)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p.symm (reverse_move p (hp 12)) (reverse_move p (hp 0)) hit
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq q.symm (reverse_move q (hq 154)) (reverse_move q (hq 131)) h0
    have t1 := move_eq p.symm (reverse_move p (hp 111)) (reverse_move p (hp 42)) (Eq.symm hit)
    have t2 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 42)) (Eq.trans t1 (Eq.symm hit))
    have t3 := move_eq q (hq 131) (hq 13) (Eq.trans (Eq.trans (Eq.symm t0) t2) (Eq.symm hit))
    exact branch34 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t3)
  · have t0 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 42)) (Eq.symm hit)
    have t1 := move_eq p (hp 111) (hp 13) (Eq.symm hit)
    have t2 := move_eq p (hp 159) (hp 41) (Eq.trans t0 t1)
    have t3 := move_eq p (hp 60) (hp 13) (Eq.trans (Eq.symm t2) (Eq.symm hit))
    have t4 := move_eq p (hp 159) (hp 19) (Eq.trans (Eq.trans t0 t1) (Eq.symm t3))
    have t5 := move_eq q.symm (reverse_move q (hq 154)) (reverse_move q (hq 131)) h0
    have t6 := move_eq q (hq 131) (hq 19) (Eq.trans (Eq.trans (Eq.trans (Eq.symm t5) t0) t1) (Eq.symm t3))
    have t7 := move_eq p (hp 13) (hp 5) (Eq.trans (Eq.trans hit t4) t6)
    have t8 := move_eq q (hq 106) (hq 59) h0
    have t9 := move_eq q (hq 131) (hq 41) (Eq.trans (Eq.trans (Eq.symm t5) t0) t1)
    have t10 := move_eq q (hq 70) (hq 59) (Eq.symm t9)
    have t11 := move_eq p (hp 153) (hp 22) (Eq.trans t8 (Eq.symm t10))
    have t12 := move_eq q (hq 42) (hq 41) t1
    have t13 := move_eq p.symm (reverse_move p (hp 154)) (reverse_move p (hp 19)) (Eq.trans t12 (Eq.symm t9))
    have t14 := move_eq q (hq 152) (hq 19) t13
    have t15 := move_eq q.symm (reverse_move q (hq 1)) (reverse_move q (hq 19)) (Eq.trans (Eq.symm t11) t14)
    have t16 := move_eq p.symm (reverse_move p (hp 5)) (reverse_move p (hp 0)) (Eq.trans (Eq.trans (Eq.symm t7) (Eq.symm t3)) (Eq.symm t15))
    exact branch32 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t16) (Eq.symm t6))
  · have t0 := move_eq q (hq 131) (hq 13) (Eq.symm hit)
    exact branch34 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq q (hq 19) (hq 13) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 1)) (reverse_move p (hp 12)) t0
    have t2 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 0)) (Eq.symm t1)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq p.symm (reverse_move p (hp 42)) (reverse_move p (hp 0)) hit
    exact branch26 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq q.symm (reverse_move q (hq 154)) (reverse_move q (hq 131)) h0
    have t1 := move_eq p.symm (reverse_move p (hp 111)) (reverse_move p (hp 42)) (Eq.symm hit)
    have t2 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 42)) (Eq.trans t1 (Eq.symm hit))
    have t3 := move_eq q (hq 131) (hq 13) (Eq.trans (Eq.trans (Eq.symm t0) t2) (Eq.symm hit))
    exact branch34 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t3)
  · have t0 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 42)) (Eq.symm hit)
    have t1 := move_eq p (hp 111) (hp 13) (Eq.symm hit)
    have t2 := move_eq p (hp 159) (hp 41) (Eq.trans t0 t1)
    have t3 := move_eq p (hp 60) (hp 13) (Eq.trans (Eq.symm t2) (Eq.symm hit))
    have t4 := move_eq p (hp 159) (hp 19) (Eq.trans (Eq.trans t0 t1) (Eq.symm t3))
    have t5 := move_eq q.symm (reverse_move q (hq 154)) (reverse_move q (hq 131)) h0
    have t6 := move_eq q (hq 131) (hq 19) (Eq.trans (Eq.trans (Eq.trans (Eq.symm t5) t0) t1) (Eq.symm t3))
    have t7 := move_eq p (hp 13) (hp 5) (Eq.trans (Eq.trans hit t4) t6)
    have t8 := move_eq q (hq 106) (hq 59) h0
    have t9 := move_eq q (hq 131) (hq 41) (Eq.trans (Eq.trans (Eq.symm t5) t0) t1)
    have t10 := move_eq q (hq 70) (hq 59) (Eq.symm t9)
    have t11 := move_eq p (hp 153) (hp 22) (Eq.trans t8 (Eq.symm t10))
    have t12 := move_eq q (hq 42) (hq 41) t1
    have t13 := move_eq p.symm (reverse_move p (hp 154)) (reverse_move p (hp 19)) (Eq.trans t12 (Eq.symm t9))
    have t14 := move_eq q (hq 152) (hq 19) t13
    have t15 := move_eq q.symm (reverse_move q (hq 1)) (reverse_move q (hq 19)) (Eq.trans (Eq.symm t11) t14)
    have t16 := move_eq p.symm (reverse_move p (hp 5)) (reverse_move p (hp 0)) (Eq.trans (Eq.trans (Eq.symm t7) (Eq.symm t3)) (Eq.symm t15))
    exact branch32 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t16) (Eq.symm t6))
  · have t0 := move_eq p.symm (reverse_move p (hp 158)) (reverse_move p (hp 42)) (Eq.trans h0 (Eq.symm hit))
    have t1 := move_eq p.symm (reverse_move p (hp 19)) (reverse_move p (hp 42)) (Eq.symm hit)
    have t2 := move_eq p (hp 106) (hp 13) (Eq.trans h0 (Eq.symm hit))
    have t3 := move_eq p (hp 41) (hp 39) (Eq.symm t2)
    have t4 := move_eq p (hp 60) (hp 12) t3
    have t5 := move_eq p (hp 158) (hp 3) (Eq.trans (Eq.trans t0 (Eq.symm t1)) t4)
    exact branch16 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t5)
  · have t0 := move_eq p.symm (reverse_move p (hp 42)) (reverse_move p (hp 1)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 111)) (reverse_move p (hp 0)) t0
    exact branch25 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p.symm (reverse_move p (hp 42)) (reverse_move p (hp 0)) hit
    exact branch26 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq q.symm (reverse_move q (hq 154)) (reverse_move q (hq 131)) h0
    have t1 := move_eq p (hp 111) (hp 42) (Eq.symm hit)
    have t2 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 42)) (Eq.trans (Eq.symm hit) t1)
    have t3 := move_eq q (hq 131) (hq 13) (Eq.trans (Eq.trans (Eq.symm t0) t2) t1)
    exact branch34 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t3)
  · have t0 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 111)) (Eq.symm hit)
    have t1 := move_eq q.symm (reverse_move q (hq 154)) (reverse_move q (hq 131)) h0
    have t2 := move_eq p (hp 159) (hp 42) (Eq.trans t1 (Eq.symm hit))
    have t3 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 42)) (Eq.trans t0 t2)
    have t4 := move_eq q (hq 131) (hq 25) (Eq.trans (Eq.symm hit) (Eq.symm t3))
    exact branch50 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans h0 t4)
  · have t0 := move_eq p (hp 42) (hp 19) hit
    have t1 := move_eq p (hp 106) (hp 13) (Eq.trans h0 (Eq.symm t0))
    have t2 := move_eq p.symm (reverse_move p (hp 111)) (reverse_move p (hp 60)) hit
    have t3 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 41)) t2
    have t4 := move_eq q.symm (reverse_move q (hq 154)) (reverse_move q (hq 43)) (Eq.trans h0 (Eq.symm t0))
    have t5 := move_eq q.symm (reverse_move q (hq 131)) (reverse_move q (hq 43)) (Eq.symm t0)
    exact branch44 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.trans (Eq.trans t1 (Eq.symm t3)) t4) (Eq.symm t5))
  · have t0 := move_eq p.symm (reverse_move p (hp 111)) (reverse_move p (hp 0)) hit
    exact branch25 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq q.symm (reverse_move q (hq 154)) (reverse_move q (hq 131)) h0
    have t1 := move_eq p (hp 111) (hp 42) (Eq.symm hit)
    have t2 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 42)) (Eq.trans (Eq.symm hit) t1)
    have t3 := move_eq q (hq 131) (hq 13) (Eq.trans (Eq.trans (Eq.symm t0) t2) t1)
    exact branch34 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t3)
  · have t0 := move_eq p (hp 106) (hp 42) (Eq.trans h0 (Eq.symm hit))
    have t1 := move_eq p (hp 39) (hp 13) t0
    have t2 := move_eq p (hp 41) (hp 12) (Eq.symm t1)
    have t3 := move_eq p (hp 60) (hp 3) t2
    exact branch29 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t3)
  · have t0 := move_eq p.symm (reverse_move p (hp 111)) (reverse_move p (hp 1)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 0)) t0
    exact branch17 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p.symm (reverse_move p (hp 111)) (reverse_move p (hp 0)) hit
    exact branch25 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq q.symm (reverse_move q (hq 154)) (reverse_move q (hq 131)) h0
    have t1 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 159)) (Eq.symm hit)
    have t2 := move_eq p (hp 111) (hp 77) (Eq.trans (Eq.trans hit (Eq.symm t0)) (Eq.symm t1))
    have t3 := move_eq p (hp 159) (hp 42) (Eq.trans t0 (Eq.symm t2))
    have t4 := move_eq q (hq 154) (hq 13) (Eq.trans (Eq.trans t0 (Eq.symm hit)) t3)
    exact branch34 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t4) h0)
  · have t0 := move_eq p (hp 106) (hp 59) h0
    have t1 := move_eq p (hp 111) (hp 19) hit
    have t2 := move_eq p (hp 59) (hp 42) (Eq.symm t1)
    have t3 := move_eq p (hp 39) (hp 13) (Eq.trans t0 t2)
    have t4 := move_eq p (hp 41) (hp 12) (Eq.symm t3)
    have t5 := move_eq p (hp 60) (hp 3) t4
    exact branch29 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t5)
  · have t0 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 0)) hit
    exact branch17 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq q.symm (reverse_move q (hq 154)) (reverse_move q (hq 131)) h0
    have t1 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 19)) hit
    have t2 := move_eq q (hq 131) (hq 19) (Eq.trans (Eq.symm t0) t1)
    have t3 := move_eq p.symm (reverse_move p (hp 19)) (reverse_move p (hp 1)) t2
    have t4 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 0)) (Eq.trans (Eq.trans (Eq.symm t0) t1) t3)
    exact branch31 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t4)
  · have t0 := move_eq q.symm (reverse_move q (hq 154)) (reverse_move q (hq 131)) h0
    have t1 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 1)) hit
    have t2 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 0)) (Eq.trans (Eq.symm t0) t1)
    exact branch31 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 0)) hit
    exact branch17 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq q (hq 131) (hq 19) hit
    have t1 := move_eq p.symm (reverse_move p (hp 19)) (reverse_move p (hp 1)) t0
    have t2 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 0)) (Eq.trans hit t1)
    exact branch31 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 0)) hit
    exact branch31 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 19)) (reverse_move p (hp 1)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 60)) (reverse_move p (hp 0)) t0
    exact branch28 p q v hp hq sep (Eq.symm t1)
  · have t0 := move_eq p.symm (reverse_move p (hp 19)) (reverse_move p (hp 0)) hit
    exact branch29 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 60)) (reverse_move p (hp 0)) hit
    exact branch28 p q v hp hq sep (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 1)) (reverse_move p (hp 0)) hit
    have t1 := move_eq p (hp 5) (hp 1) hit
    have t2 := move_eq p.symm (reverse_move p (hp 5)) (reverse_move p (hp 3)) (Eq.trans (Eq.trans t1 hit) t0)
    exact branch1 p q v hp sep (Eq.trans (Eq.trans (Eq.symm t0) (Eq.symm hit)) t2)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep in
private theorem branch53 (h0 : v 106 = v 1) (h1 : v 38 = v 86) : False := by
  have t0 := move_eq p.symm (reverse_move p (hp 29)) (reverse_move p (hp 105)) (Eq.symm h1)
  have t1 := move_eq p.symm (reverse_move p (hp 157)) (reverse_move p (hp 9)) (Eq.symm t0)
  have t2 := move_eq q.symm (reverse_move q (hq 153)) (reverse_move q (hq 58)) (Eq.symm t0)
  have t3 := move_eq q.symm (reverse_move q (hq 111)) (reverse_move q (hq 45)) t2
  have t4 := move_eq q.symm (reverse_move q (hq 154)) (reverse_move q (hq 7)) h0
  have t5 := move_eq p (hp 159) (hp 7) t4
  have t6 := move_eq q (hq 45) (hq 23) (Eq.trans (Eq.symm t3) t5)
  have t7 := move_eq q (hq 72) (hq 58) (Eq.symm t6)
  have t8 := move_eq p.symm (reverse_move p (hp 157)) (reverse_move p (hp 8)) (Eq.trans (Eq.symm t0) (Eq.symm t7))
  exact (sep (v 2)).2.2 (Eq.trans (hp 2) (Eq.symm (Eq.trans (hq 2) (Eq.trans (Eq.symm t1) t8))))

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch54 (h0 : v 106 = v 1) (h1 : v 86 = v 2) : False := by
  have t0 := move_eq q (hq 86) (hq 2) h1
  have t1 := move_eq p.symm (reverse_move p (hp 81)) (reverse_move p (hp 31)) t0
  have t2 := move_eq p.symm (reverse_move p (hp 29)) (reverse_move p (hp 10)) h1
  have t3 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 33)) t2
  have t4 := move_eq p.symm (reverse_move p (hp 96)) (reverse_move p (hp 31)) (Eq.symm t3)
  have t5 := move_eq p (hp 106) (hp 1) h0
  have t6 := move_eq q (hq 39) (hq 5) t5
  have t7 := move_eq q (hq 81) (hq 18) (Eq.trans (Eq.trans t1 (Eq.symm t4)) t6)
  have t8 := move_eq p.symm (reverse_move p (hp 88)) (reverse_move p (hp 127)) t7
  have t9 := move_eq q (hq 33) (hq 9) (Eq.symm t3)
  have t10 := move_eq q (hq 95) (hq 30) t9
  have t11 := move_eq p (hp 141) (hp 88) t10
  have t12 := move_eq p.symm (reverse_move p (hp 135)) (reverse_move p (hp 58)) (Eq.trans (Eq.trans t1 (Eq.symm t4)) t6)
  have t13 := move_eq q.symm (reverse_move q (hq 58)) (reverse_move q (hq 34)) t2
  have t14 := move_eq p.symm (reverse_move p (hp 90)) (reverse_move p (hp 99)) (Eq.trans t12 t13)
  have t15 := move_eq q.symm (reverse_move q (hq 154)) (reverse_move q (hq 7)) h0
  have t16 := move_eq p (hp 159) (hp 7) t15
  have t17 := move_eq q (hq 111) (hq 23) t16
  have t18 := move_eq p (hp 58) (hp 34) t13
  have t19 := move_eq p (hp 98) (hp 18) (Eq.symm t18)
  have t20 := move_eq p (hp 81) (hp 18) (Eq.trans (Eq.trans t1 (Eq.symm t4)) t6)
  have t21 := move_eq p (hp 132) (hp 9) (Eq.trans (Eq.trans t19 (Eq.symm t20)) t0)
  have t22 := move_eq q.symm (reverse_move q (hq 111)) (reverse_move q (hq 34)) (Eq.trans (Eq.trans t17 t21) t2)
  have t23 := move_eq p.symm (reverse_move p (hp 99)) (reverse_move p (hp 7)) (Eq.trans (Eq.symm t22) t16)
  have t24 := move_eq p.symm (reverse_move p (hp 127)) (reverse_move p (hp 24)) (Eq.trans (Eq.trans (Eq.trans (Eq.symm t7) (Eq.symm t11)) t14) t23)
  have t25 := move_eq p.symm (reverse_move p (hp 35)) (reverse_move p (hp 99)) t13
  have t26 := move_eq p.symm (reverse_move p (hp 11)) (reverse_move p (hp 24)) (Eq.trans t25 t23)
  have t27 := move_eq q.symm (reverse_move q (hq 30)) (reverse_move q (hq 3)) (Eq.trans (Eq.trans t8 t24) (Eq.symm t26))
  exact short8 p q G sep e₀ e₁ e₂ no ![0,1,0,2,0,2,0,2] (by decide)
    (v 0) (v 0) (v 3) (v 3) (v 9) (v 9) (v 2) (v 2)
    (rfl) (hp 3) (rfl) (Eq.trans (hq 9) t27) (rfl) (hq 2) (rfl) (hq 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch52 (h0 : v 106 = v 1) : False := by
  have t0 := move_eq p (hp 106) (hp 1) h0
  have t1 := move_eq p (hp 39) (hp 5) t0
  have t2 := move_eq q (hq 17) (hq 12) (Eq.symm t1)
  have t3 := move_eq q (hq 54) (hq 38) t2
  rcases collision16 (fun h => no (.inr (.inr (.inl h))))
    (v 0) (v 0) (v 3) (v 3) (v 12) (v 38) (v 38) (v 94) (v 86) (v 86) (v 29) (v 29) (v 9) (v 9) (v 2) (v 2)
    (e₀ (v 0))
    ((hp 3) ▸ e₁ (v 3))
    (e₀ (v 3))
    ((hp 12) ▸ e₁ (v 12))
    ((hq 12) ▸ e₂ (v 12))
    (e₀ (v 38))
    ((hq 38) ▸ e₂ (v 38))
    ((Eq.trans (hp 86) t3) ▸ e₁ (v 86))
    (e₀ (v 86))
    ((hp 29) ▸ e₁ (v 29))
    (e₀ (v 29))
    ((hp 9) ▸ e₁ (v 9))
    (e₀ (v 9))
    ((hq 2) ▸ e₂ (v 2))
    (e₀ (v 2))
    ((hq 0) ▸ e₂ (v 0)) with hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit
  · exact branch1 p q v hp sep hit
  · exact branch2 p q v hp sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq q (hq 38) (hq 0) (Eq.symm hit)
    have t1 := move_eq p (hp 94) (hp 2) t0
    exact branch24 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p.symm (reverse_move p (hp 29)) (reverse_move p (hp 3)) (Eq.symm hit)
    exact branch42 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 3)) (Eq.symm hit)
    have t1 := move_eq q (hq 9) (hq 3) t0
    have t2 := move_eq q.symm (reverse_move q (hq 58)) (reverse_move q (hq 4)) (Eq.symm hit)
    have t3 := move_eq p.symm (reverse_move p (hp 35)) (reverse_move p (hp 15)) t2
    have t4 := move_eq p.symm (reverse_move p (hp 11)) (reverse_move p (hp 48)) t3
    have t5 := move_eq p.symm (reverse_move p (hp 31)) (reverse_move p (hp 12)) t0
    have t6 := move_eq q (hq 31) (hq 12) t5
    have t7 := move_eq p (hp 58) (hp 4) t2
    have t8 := move_eq q.symm (reverse_move q (hq 5)) (reverse_move q (hq 46)) t7
    have t9 := move_eq p (hp 46) (hp 5) (Eq.symm t8)
    have t10 := move_eq p (hp 106) (hp 1) h0
    have t11 := move_eq p (hp 39) (hp 5) t10
    have t12 := move_eq q (hq 61) (hq 12) (Eq.trans t9 (Eq.symm t11))
    have t13 := move_eq p (hp 90) (hp 19) (Eq.trans t6 (Eq.symm t12))
    have t14 := move_eq p.symm (reverse_move p (hp 89)) (reverse_move p (hp 37)) t1
    have t15 := move_eq p.symm (reverse_move p (hp 107)) (reverse_move p (hp 37)) (Eq.symm t4)
    have t16 := move_eq q.symm (reverse_move q (hq 107)) (reverse_move q (hq 19)) t10
    have t17 := move_eq p (hp 89) (hp 19) (Eq.trans (Eq.trans t14 (Eq.symm t15)) t16)
    have t18 := move_eq p (hp 135) (hp 11) (Eq.trans (Eq.trans t13 (Eq.symm t17)) t1)
    have t19 := move_eq p (hp 29) (hp 0) (Eq.symm hit)
    have t20 := move_eq q (hq 86) (hq 1) t19
    have t21 := move_eq p.symm (reverse_move p (hp 81)) (reverse_move p (hp 22)) t20
    have t22 := move_eq q (hq 81) (hq 22) t21
    have t23 := move_eq q (hq 18) (hq 14) t7
    have t24 := move_eq q.symm (reverse_move q (hq 45)) (reverse_move q (hq 16)) t2
    have t25 := move_eq p.symm (reverse_move p (hp 127)) (reverse_move p (hp 51)) (Eq.trans t23 t24)
    have t26 := move_eq p.symm (reverse_move p (hp 118)) (reverse_move p (hp 51)) t24
    have t27 := move_eq p.symm (reverse_move p (hp 155)) (reverse_move p (hp 124)) t26
    have t28 := move_eq q (hq 48) (hq 11) (Eq.symm t4)
    have t29 := move_eq q.symm (reverse_move q (hq 36)) (reverse_move q (hq 61)) (Eq.trans (Eq.trans t14 (Eq.symm t15)) t16)
    have t30 := move_eq p (hp 104) (hp 12) (Eq.trans (Eq.trans (Eq.trans t28 t29) t9) (Eq.symm t11))
    have t31 := move_eq p (hp 124) (hp 3) (Eq.trans (Eq.symm t27) t30)
    have t32 := move_eq p.symm (reverse_move p (hp 68)) (reverse_move p (hp 3)) (Eq.trans t25 t31)
    have t33 := move_eq q.symm (reverse_move q (hq 81)) (reverse_move q (hq 13)) (Eq.trans t22 t32)
    have t34 := move_eq q (hq 29) (hq 0) (Eq.symm hit)
    have t35 := move_eq q (hq 87) (hq 2) t34
    have t36 := move_eq q.symm (reverse_move q (hq 87)) (reverse_move q (hq 13)) (Eq.trans t35 t0)
    have t37 := move_eq p.symm (reverse_move p (hp 48)) (reverse_move p (hp 10)) (Eq.trans (Eq.trans (Eq.trans (Eq.trans (Eq.symm t3) (Eq.symm t18)) t33) (Eq.symm t36)) t34)
    have t38 := move_eq q.symm (reverse_move q (hq 9)) (reverse_move q (hq 34)) (Eq.trans (Eq.trans t1 t4) t37)
    have t39 := move_eq q.symm (reverse_move q (hq 131)) (reverse_move q (hq 34)) (Eq.trans (Eq.trans (Eq.trans (Eq.symm t17) t1) t4) t37)
    exact branch33 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.trans (Eq.symm t0) t38) (Eq.symm t39))
  · have t0 := move_eq p.symm (reverse_move p (hp 31)) (reverse_move p (hp 3)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 91)) (reverse_move p (hp 12)) t0
    have t2 := move_eq p.symm (reverse_move p (hp 142)) (reverse_move p (hp 39)) t1
    have t3 := move_eq p (hp 106) (hp 1) h0
    have t4 := move_eq p (hp 142) (hp 5) (Eq.trans t2 t3)
    have t5 := move_eq q (hq 17) (hq 12) (Eq.trans (Eq.symm t4) t1)
    have t6 := move_eq p (hp 9) (hp 0) (Eq.symm hit)
    have t7 := move_eq p (hp 29) (hp 1) t6
    have t8 := move_eq p (hp 86) (hp 5) t7
    have t9 := move_eq q.symm (reverse_move q (hq 54)) (reverse_move q (hq 55)) t8
    have t10 := move_eq q.symm (reverse_move q (hq 55)) (reverse_move q (hq 40)) (Eq.trans (Eq.symm t4) t1)
    have t11 := move_eq q.symm (reverse_move q (hq 37)) (reverse_move q (hq 40)) t1
    have t12 := move_eq q (hq 38) (hq 37) (Eq.trans (Eq.trans (Eq.trans (Eq.symm t5) t9) t10) (Eq.symm t11))
    have t13 := move_eq q (hq 9) (hq 0) (Eq.symm hit)
    have t14 := move_eq p.symm (reverse_move p (hp 89)) (reverse_move p (hp 10)) t13
    have t15 := move_eq p.symm (reverse_move p (hp 140)) (reverse_move p (hp 33)) t14
    have t16 := move_eq q.symm (reverse_move q (hq 94)) (reverse_move q (hq 97)) t15
    have t17 := move_eq q.symm (reverse_move q (hq 96)) (reverse_move q (hq 19)) (Eq.trans t2 t3)
    have t18 := move_eq q (hq 39) (hq 5) t3
    have t19 := move_eq p (hp 19) (hp 18) (Eq.trans (Eq.symm t17) t18)
    have t20 := move_eq p (hp 96) (hp 18) t18
    have t21 := move_eq q.symm (reverse_move q (hq 131)) (reverse_move q (hq 97)) (Eq.trans t19 (Eq.symm t20))
    exact branch35 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.trans (Eq.trans (Eq.symm t1) (Eq.symm t12)) t16) (Eq.symm t21))
  · exact branch8 p q v hq sep hit
  · exact branch1 p q v hp sep hit
  · have t0 := move_eq q (hq 38) (hq 0) (Eq.symm hit)
    have t1 := move_eq p (hp 94) (hp 2) t0
    exact branch24 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p (hp 94) (hp 0) (Eq.symm hit)
    have t1 := move_eq q.symm (reverse_move q (hq 10)) (reverse_move q (hq 7)) t0
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p.symm (reverse_move p (hp 29)) (reverse_move p (hp 3)) (Eq.symm hit)
    exact branch42 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 3)) (Eq.symm hit)
    have t1 := move_eq q (hq 9) (hq 3) t0
    have t2 := move_eq q.symm (reverse_move q (hq 58)) (reverse_move q (hq 4)) (Eq.symm hit)
    have t3 := move_eq p.symm (reverse_move p (hp 35)) (reverse_move p (hp 15)) t2
    have t4 := move_eq p.symm (reverse_move p (hp 11)) (reverse_move p (hp 48)) t3
    have t5 := move_eq p.symm (reverse_move p (hp 31)) (reverse_move p (hp 12)) t0
    have t6 := move_eq q (hq 31) (hq 12) t5
    have t7 := move_eq p (hp 58) (hp 4) t2
    have t8 := move_eq q.symm (reverse_move q (hq 5)) (reverse_move q (hq 46)) t7
    have t9 := move_eq p (hp 46) (hp 5) (Eq.symm t8)
    have t10 := move_eq p (hp 106) (hp 1) h0
    have t11 := move_eq p (hp 39) (hp 5) t10
    have t12 := move_eq q (hq 61) (hq 12) (Eq.trans t9 (Eq.symm t11))
    have t13 := move_eq p (hp 90) (hp 19) (Eq.trans t6 (Eq.symm t12))
    have t14 := move_eq p.symm (reverse_move p (hp 89)) (reverse_move p (hp 37)) t1
    have t15 := move_eq p.symm (reverse_move p (hp 107)) (reverse_move p (hp 37)) (Eq.symm t4)
    have t16 := move_eq q.symm (reverse_move q (hq 107)) (reverse_move q (hq 19)) t10
    have t17 := move_eq p (hp 89) (hp 19) (Eq.trans (Eq.trans t14 (Eq.symm t15)) t16)
    have t18 := move_eq p (hp 135) (hp 11) (Eq.trans (Eq.trans t13 (Eq.symm t17)) t1)
    have t19 := move_eq p (hp 29) (hp 0) (Eq.symm hit)
    have t20 := move_eq q (hq 86) (hq 1) t19
    have t21 := move_eq p.symm (reverse_move p (hp 81)) (reverse_move p (hp 22)) t20
    have t22 := move_eq q (hq 81) (hq 22) t21
    have t23 := move_eq q (hq 18) (hq 14) t7
    have t24 := move_eq q.symm (reverse_move q (hq 45)) (reverse_move q (hq 16)) t2
    have t25 := move_eq p.symm (reverse_move p (hp 127)) (reverse_move p (hp 51)) (Eq.trans t23 t24)
    have t26 := move_eq p.symm (reverse_move p (hp 118)) (reverse_move p (hp 51)) t24
    have t27 := move_eq p.symm (reverse_move p (hp 155)) (reverse_move p (hp 124)) t26
    have t28 := move_eq q (hq 48) (hq 11) (Eq.symm t4)
    have t29 := move_eq q.symm (reverse_move q (hq 36)) (reverse_move q (hq 61)) (Eq.trans (Eq.trans t14 (Eq.symm t15)) t16)
    have t30 := move_eq p (hp 104) (hp 12) (Eq.trans (Eq.trans (Eq.trans t28 t29) t9) (Eq.symm t11))
    have t31 := move_eq p (hp 124) (hp 3) (Eq.trans (Eq.symm t27) t30)
    have t32 := move_eq p.symm (reverse_move p (hp 68)) (reverse_move p (hp 3)) (Eq.trans t25 t31)
    have t33 := move_eq q.symm (reverse_move q (hq 81)) (reverse_move q (hq 13)) (Eq.trans t22 t32)
    have t34 := move_eq q (hq 29) (hq 0) (Eq.symm hit)
    have t35 := move_eq q (hq 87) (hq 2) t34
    have t36 := move_eq q.symm (reverse_move q (hq 87)) (reverse_move q (hq 13)) (Eq.trans t35 t0)
    have t37 := move_eq p.symm (reverse_move p (hp 48)) (reverse_move p (hp 10)) (Eq.trans (Eq.trans (Eq.trans (Eq.trans (Eq.symm t3) (Eq.symm t18)) t33) (Eq.symm t36)) t34)
    have t38 := move_eq q.symm (reverse_move q (hq 9)) (reverse_move q (hq 34)) (Eq.trans (Eq.trans t1 t4) t37)
    have t39 := move_eq q.symm (reverse_move q (hq 131)) (reverse_move q (hq 34)) (Eq.trans (Eq.trans (Eq.trans (Eq.symm t17) t1) t4) t37)
    exact branch33 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.trans (Eq.symm t0) t38) (Eq.symm t39))
  · have t0 := move_eq p.symm (reverse_move p (hp 31)) (reverse_move p (hp 3)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 91)) (reverse_move p (hp 12)) t0
    have t2 := move_eq p.symm (reverse_move p (hp 142)) (reverse_move p (hp 39)) t1
    have t3 := move_eq p (hp 106) (hp 1) h0
    have t4 := move_eq p (hp 142) (hp 5) (Eq.trans t2 t3)
    have t5 := move_eq q (hq 17) (hq 12) (Eq.trans (Eq.symm t4) t1)
    have t6 := move_eq p (hp 9) (hp 0) (Eq.symm hit)
    have t7 := move_eq p (hp 29) (hp 1) t6
    have t8 := move_eq p (hp 86) (hp 5) t7
    have t9 := move_eq q.symm (reverse_move q (hq 54)) (reverse_move q (hq 55)) t8
    have t10 := move_eq q.symm (reverse_move q (hq 55)) (reverse_move q (hq 40)) (Eq.trans (Eq.symm t4) t1)
    have t11 := move_eq q.symm (reverse_move q (hq 37)) (reverse_move q (hq 40)) t1
    have t12 := move_eq q (hq 38) (hq 37) (Eq.trans (Eq.trans (Eq.trans (Eq.symm t5) t9) t10) (Eq.symm t11))
    have t13 := move_eq q (hq 9) (hq 0) (Eq.symm hit)
    have t14 := move_eq p.symm (reverse_move p (hp 89)) (reverse_move p (hp 10)) t13
    have t15 := move_eq p.symm (reverse_move p (hp 140)) (reverse_move p (hp 33)) t14
    have t16 := move_eq q.symm (reverse_move q (hq 94)) (reverse_move q (hq 97)) t15
    have t17 := move_eq q.symm (reverse_move q (hq 96)) (reverse_move q (hq 19)) (Eq.trans t2 t3)
    have t18 := move_eq q (hq 39) (hq 5) t3
    have t19 := move_eq p (hp 19) (hp 18) (Eq.trans (Eq.symm t17) t18)
    have t20 := move_eq p (hp 96) (hp 18) t18
    have t21 := move_eq q.symm (reverse_move q (hq 131)) (reverse_move q (hq 97)) (Eq.trans t19 (Eq.symm t20))
    exact branch35 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.trans (Eq.trans (Eq.symm t1) (Eq.symm t12)) t16) (Eq.symm t21))
  · exact branch8 p q v hq sep hit
  · have t0 := move_eq p (hp 12) (hp 3) (Eq.symm hit)
    exact branch1 p q v hp sep (Eq.symm t0)
  · have t0 := move_eq q.symm (reverse_move q (hq 12)) (reverse_move q (hq 13)) (Eq.symm hit)
    have t1 := move_eq p (hp 13) (hp 12) (Eq.symm t0)
    have t2 := move_eq p (hp 41) (hp 3) t1
    exact branch28 p q v hp hq sep (Eq.symm t2)
  · have t0 := move_eq p (hp 106) (hp 1) h0
    have t1 := move_eq q (hq 39) (hq 5) t0
    have t2 := move_eq p (hp 96) (hp 18) t1
    have t3 := move_eq p.symm (reverse_move p (hp 29)) (reverse_move p (hp 12)) (Eq.symm hit)
    have t4 := move_eq q.symm (reverse_move q (hq 58)) (reverse_move q (hq 40)) t3
    have t5 := move_eq p (hp 58) (hp 40) t4
    have t6 := move_eq p (hp 75) (hp 18) (Eq.symm t5)
    have t7 := move_eq p (hp 33) (hp 24) (Eq.trans t2 (Eq.symm t6))
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t7)
  · exact branch42 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq q (hq 9) (hq 3) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 89)) (reverse_move p (hp 37)) t0
    have t2 := move_eq q (hq 89) (hq 37) t1
    have t3 := move_eq p.symm (reverse_move p (hp 31)) (reverse_move p (hp 12)) (Eq.symm hit)
    have t4 := move_eq p.symm (reverse_move p (hp 91)) (reverse_move p (hp 39)) t3
    have t5 := move_eq p (hp 106) (hp 1) h0
    have t6 := move_eq q.symm (reverse_move q (hq 89)) (reverse_move q (hq 19)) (Eq.trans (Eq.trans t2 t4) t5)
    have t7 := move_eq p (hp 37) (hp 19) (Eq.trans (Eq.symm t1) t6)
    have t8 := move_eq q.symm (reverse_move q (hq 131)) (reverse_move q (hq 3)) (Eq.symm t7)
    exact branch33 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t8)
  · exact branch10 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq q.symm (reverse_move q (hq 12)) (reverse_move q (hq 13)) (Eq.symm hit)
    have t1 := move_eq p (hp 13) (hp 12) (Eq.symm t0)
    have t2 := move_eq p (hp 41) (hp 3) t1
    exact branch28 p q v hp hq sep (Eq.symm t2)
  · have t0 := move_eq p (hp 94) (hp 3) (Eq.symm hit)
    exact branch19 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 106) (hp 1) h0
    have t1 := move_eq q (hq 39) (hq 5) t0
    have t2 := move_eq p (hp 96) (hp 18) t1
    have t3 := move_eq p.symm (reverse_move p (hp 29)) (reverse_move p (hp 12)) (Eq.symm hit)
    have t4 := move_eq q.symm (reverse_move q (hq 58)) (reverse_move q (hq 40)) t3
    have t5 := move_eq p (hp 58) (hp 40) t4
    have t6 := move_eq p (hp 75) (hp 18) (Eq.symm t5)
    have t7 := move_eq p (hp 33) (hp 24) (Eq.trans t2 (Eq.symm t6))
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t7)
  · exact branch42 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq q (hq 9) (hq 3) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 89)) (reverse_move p (hp 37)) t0
    have t2 := move_eq q (hq 89) (hq 37) t1
    have t3 := move_eq p.symm (reverse_move p (hp 31)) (reverse_move p (hp 12)) (Eq.symm hit)
    have t4 := move_eq p.symm (reverse_move p (hp 91)) (reverse_move p (hp 39)) t3
    have t5 := move_eq p (hp 106) (hp 1) h0
    have t6 := move_eq q.symm (reverse_move q (hq 89)) (reverse_move q (hq 19)) (Eq.trans (Eq.trans t2 t4) t5)
    have t7 := move_eq p (hp 37) (hp 19) (Eq.trans (Eq.symm t1) t6)
    have t8 := move_eq q.symm (reverse_move q (hq 131)) (reverse_move q (hq 3)) (Eq.symm t7)
    exact branch33 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t8)
  · exact branch10 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq q.symm (reverse_move q (hq 12)) (reverse_move q (hq 40)) (Eq.symm hit)
    have t1 := move_eq p (hp 40) (hp 12) (Eq.symm t0)
    have t2 := move_eq p (hp 75) (hp 3) t1
    exact branch5 p q v hp hq sep (Eq.symm t2)
  · have t0 := move_eq p.symm (reverse_move p (hp 29)) (reverse_move p (hp 39)) (Eq.symm hit)
    have t1 := move_eq p (hp 106) (hp 1) h0
    have t2 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 1)) (Eq.trans t0 t1)
    have t3 := move_eq q.symm (reverse_move q (hq 2)) (reverse_move q (hq 7)) t2
    exact branch13 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t3)
  · have t0 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 39)) (Eq.symm hit)
    have t1 := move_eq q (hq 39) (hq 9) (Eq.symm t0)
    have t2 := move_eq p (hp 96) (hp 30) t1
    have t3 := move_eq p (hp 106) (hp 1) h0
    have t4 := move_eq q (hq 9) (hq 5) (Eq.trans t0 t3)
    have t5 := move_eq p (hp 30) (hp 18) t4
    have t6 := move_eq q.symm (reverse_move q (hq 58)) (reverse_move q (hq 40)) (Eq.symm hit)
    have t7 := move_eq p (hp 58) (hp 40) t6
    have t8 := move_eq p (hp 75) (hp 18) (Eq.symm t7)
    have t9 := move_eq p (hp 33) (hp 24) (Eq.trans (Eq.trans t2 t5) (Eq.symm t8))
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t9)
  · have t0 := move_eq p (hp 12) (hp 9) hit
    exact branch42 p q v hp hq sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 10)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 33)) t0
    have t2 := move_eq p.symm (reverse_move p (hp 96)) (reverse_move p (hp 0)) (Eq.trans (Eq.symm t1) h0)
    have t3 := move_eq q (hq 39) (hq 10) t0
    exact branch19 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t2) t3)
  · have t0 := move_eq q (hq 94) (hq 38) (Eq.symm hit)
    have t1 := move_eq q.symm (reverse_move q (hq 38)) (reverse_move q (hq 12)) (Eq.symm hit)
    have t2 := move_eq q.symm (reverse_move q (hq 94)) (reverse_move q (hq 40)) (Eq.trans (Eq.trans t0 (Eq.symm hit)) t1)
    have t3 := move_eq p (hp 40) (hp 12) (Eq.trans (Eq.trans (Eq.symm t2) (Eq.symm hit)) t1)
    have t4 := move_eq p (hp 75) (hp 3) t3
    exact branch5 p q v hp hq sep (Eq.symm t4)
  · exact branch53 p q v hp hq sep h0 hit
  · have t0 := move_eq p.symm (reverse_move p (hp 105)) (reverse_move p (hp 9)) hit
    have t1 := move_eq q.symm (reverse_move q (hq 153)) (reverse_move q (hq 2)) t0
    have t2 := move_eq q.symm (reverse_move q (hq 111)) (reverse_move q (hq 0)) t1
    exact branch25 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq p (hp 106) (hp 1) h0
    have t1 := move_eq p (hp 39) (hp 5) t0
    have t2 := move_eq p (hp 38) (hp 9) hit
    have t3 := move_eq p (hp 69) (hp 29) t2
    have t4 := move_eq p (hp 86) (hp 22) (Eq.symm t3)
    have t5 := move_eq q.symm (reverse_move q (hq 54)) (reverse_move q (hq 1)) t4
    have t6 := move_eq q.symm (reverse_move q (hq 17)) (reverse_move q (hq 7)) t5
    exact branch39 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans t1 t6)
  · have t0 := move_eq q.symm (reverse_move q (hq 12)) (reverse_move q (hq 0)) hit
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t0)
  · exact branch53 p q v hp hq sep h0 hit
  · have t0 := move_eq p.symm (reverse_move p (hp 105)) (reverse_move p (hp 9)) hit
    have t1 := move_eq q.symm (reverse_move q (hq 153)) (reverse_move q (hq 2)) t0
    have t2 := move_eq q.symm (reverse_move q (hq 111)) (reverse_move q (hq 0)) t1
    exact branch25 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq p (hp 106) (hp 1) h0
    have t1 := move_eq p (hp 39) (hp 5) t0
    have t2 := move_eq p (hp 38) (hp 9) hit
    have t3 := move_eq p (hp 69) (hp 29) t2
    have t4 := move_eq p (hp 86) (hp 22) (Eq.symm t3)
    have t5 := move_eq q.symm (reverse_move q (hq 54)) (reverse_move q (hq 1)) t4
    have t6 := move_eq q.symm (reverse_move q (hq 17)) (reverse_move q (hq 7)) t5
    exact branch39 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans t1 t6)
  · have t0 := move_eq q.symm (reverse_move q (hq 12)) (reverse_move q (hq 0)) hit
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq q.symm (reverse_move q (hq 38)) (reverse_move q (hq 145)) hit
    have t1 := move_eq q.symm (reverse_move q (hq 83)) (reverse_move q (hq 12)) (Eq.symm t0)
    have t2 := move_eq p (hp 83) (hp 12) t1
    have t3 := move_eq p (hp 94) (hp 86) hit
    have t4 := move_eq q.symm (reverse_move q (hq 54)) (reverse_move q (hq 10)) (Eq.symm t3)
    have t5 := move_eq p.symm (reverse_move p (hp 26)) (reverse_move p (hp 33)) t4
    have t6 := move_eq q.symm (reverse_move q (hq 97)) (reverse_move q (hq 72)) (Eq.symm t5)
    have t7 := move_eq p (hp 97) (hp 72) t6
    have t8 := move_eq p.symm (reverse_move p (hp 28)) (reverse_move p (hp 39)) t1
    have t9 := move_eq p (hp 106) (hp 1) h0
    have t10 := move_eq p.symm (reverse_move p (hp 84)) (reverse_move p (hp 1)) (Eq.trans t8 t9)
    have t11 := move_eq p.symm (reverse_move p (hp 47)) (reverse_move p (hp 0)) t10
    have t12 := move_eq p.symm (reverse_move p (hp 72)) (reverse_move p (hp 3)) (Eq.trans (Eq.symm t7) t11)
    have t13 := move_eq q.symm (reverse_move q (hq 17)) (reverse_move q (hq 34)) t4
    have t14 := move_eq p (hp 39) (hp 5) t9
    have t15 := move_eq p (hp 34) (hp 12) (Eq.trans (Eq.symm t13) (Eq.symm t14))
    have t16 := move_eq p (hp 98) (hp 3) t15
    have t17 := move_eq p (hp 132) (hp 0) t16
    have t18 := move_eq p.symm (reverse_move p (hp 83)) (reverse_move p (hp 0)) (Eq.trans (Eq.trans t2 (Eq.symm t12)) t17)
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t18) t1)
  · have t0 := move_eq q (hq 106) (hq 1) h0
    have t1 := move_eq p (hp 106) (hp 1) h0
    have t2 := move_eq q (hq 39) (hq 5) t1
    have t3 := move_eq p (hp 96) (hp 18) t2
    have t4 := move_eq q.symm (reverse_move q (hq 38)) (reverse_move q (hq 58)) hit
    have t5 := move_eq p (hp 58) (hp 38) (Eq.symm t4)
    have t6 := move_eq p (hp 69) (hp 18) (Eq.symm t5)
    have t7 := move_eq p (hp 33) (hp 22) (Eq.trans t3 (Eq.symm t6))
    have t8 := move_eq p (hp 94) (hp 29) hit
    have t9 := move_eq q.symm (reverse_move q (hq 145)) (reverse_move q (hq 10)) (Eq.symm t8)
    have t10 := move_eq p (hp 86) (hp 32) (Eq.symm t8)
    have t11 := move_eq p (hp 39) (hp 5) t1
    have t12 := move_eq q (hq 17) (hq 12) (Eq.symm t11)
    have t13 := move_eq q (hq 54) (hq 38) t12
    have t14 := move_eq p.symm (reverse_move p (hp 32)) (reverse_move p (hp 9)) (Eq.trans (Eq.trans (Eq.symm t10) t13) hit)
    have t15 := move_eq q.symm (reverse_move q (hq 145)) (reverse_move q (hq 2)) (Eq.trans (Eq.symm t8) t14)
    have t16 := move_eq q.symm (reverse_move q (hq 106)) (reverse_move q (hq 0)) (Eq.trans (Eq.trans (Eq.trans t0 (Eq.symm t7)) (Eq.symm t9)) t15)
    exact branch16 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t16)
  · have t0 := move_eq q.symm (reverse_move q (hq 38)) (reverse_move q (hq 2)) hit
    have t1 := move_eq q.symm (reverse_move q (hq 12)) (reverse_move q (hq 0)) t0
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p (hp 94) (hp 2) hit
    exact branch24 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 86) (hp 29) hit
    have t1 := move_eq p.symm (reverse_move p (hp 29)) (reverse_move p (hp 9)) hit
    have t2 := move_eq q.symm (reverse_move q (hq 54)) (reverse_move q (hq 2)) (Eq.trans (Eq.trans t0 hit) t1)
    have t3 := move_eq q.symm (reverse_move q (hq 17)) (reverse_move q (hq 0)) t2
    have t4 := move_eq p (hp 106) (hp 1) h0
    have t5 := move_eq p (hp 39) (hp 5) t4
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t3) (Eq.symm t5))
  · have t0 := move_eq p (hp 106) (hp 1) h0
    have t1 := move_eq q (hq 39) (hq 5) t0
    have t2 := move_eq p.symm (reverse_move p (hp 147)) (reverse_move p (hp 58)) t1
    have t3 := move_eq p.symm (reverse_move p (hp 29)) (reverse_move p (hp 31)) hit
    have t4 := move_eq p.symm (reverse_move p (hp 91)) (reverse_move p (hp 9)) (Eq.symm t3)
    have t5 := move_eq p.symm (reverse_move p (hp 142)) (reverse_move p (hp 31)) t4
    have t6 := move_eq q.symm (reverse_move q (hq 96)) (reverse_move q (hq 58)) (Eq.trans t5 (Eq.symm t3))
    have t7 := move_eq p (hp 147) (hp 18) (Eq.trans (Eq.trans t2 (Eq.symm t6)) t1)
    have t8 := move_eq p (hp 96) (hp 18) t1
    have t9 := move_eq p (hp 39) (hp 5) t0
    have t10 := move_eq q (hq 17) (hq 12) (Eq.symm t9)
    have t11 := move_eq p (hp 86) (hp 9) hit
    have t12 := move_eq q.symm (reverse_move q (hq 54)) (reverse_move q (hq 58)) t11
    have t13 := move_eq p (hp 33) (hp 18) (Eq.trans (Eq.trans t8 (Eq.symm t7)) t1)
    have t14 := move_eq p.symm (reverse_move p (hp 105)) (reverse_move p (hp 33)) (Eq.trans (Eq.trans (Eq.trans (Eq.trans (Eq.symm t10) t12) (Eq.symm t6)) t7) (Eq.symm t13))
    have t15 := move_eq q.symm (reverse_move q (hq 154)) (reverse_move q (hq 7)) h0
    have t16 := move_eq p (hp 159) (hp 7) t15
    have t17 := move_eq q (hq 111) (hq 23) t16
    have t18 := move_eq q (hq 153) (hq 72) t17
    have t19 := move_eq q.symm (reverse_move q (hq 92)) (reverse_move q (hq 58)) (Eq.symm t3)
    have t20 := move_eq q.symm (reverse_move q (hq 47)) (reverse_move q (hq 17)) (Eq.trans t19 (Eq.symm t12))
    have t21 := move_eq q.symm (reverse_move q (hq 145)) (reverse_move q (hq 2)) hit
    have t22 := move_eq q.symm (reverse_move q (hq 83)) (reverse_move q (hq 0)) t21
    have t23 := move_eq p.symm (reverse_move p (hp 28)) (reverse_move p (hp 3)) t22
    have t24 := move_eq p.symm (reverse_move p (hp 84)) (reverse_move p (hp 12)) t23
    have t25 := move_eq p (hp 47) (hp 12) (Eq.trans t20 (Eq.symm t9))
    have t26 := move_eq q (hq 47) (hq 3) (Eq.trans (Eq.trans (Eq.trans t20 (Eq.symm t9)) (Eq.symm t24)) t25)
    have t27 := move_eq q (hq 28) (hq 3) t23
    have t28 := move_eq p.symm (reverse_move p (hp 26)) (reverse_move p (hp 2)) (Eq.trans (Eq.trans (Eq.trans t12 (Eq.symm t19)) t26) (Eq.symm t27))
    have t29 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 0)) (Eq.trans (Eq.trans (Eq.trans (Eq.trans t7 (Eq.symm t8)) (Eq.symm t14)) t18) t28)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t29)
  · exact branch54 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · have t0 := move_eq p (hp 86) (hp 29) hit
    have t1 := move_eq p.symm (reverse_move p (hp 29)) (reverse_move p (hp 9)) hit
    have t2 := move_eq q.symm (reverse_move q (hq 54)) (reverse_move q (hq 2)) (Eq.trans (Eq.trans t0 hit) t1)
    have t3 := move_eq q.symm (reverse_move q (hq 17)) (reverse_move q (hq 0)) t2
    have t4 := move_eq p (hp 106) (hp 1) h0
    have t5 := move_eq p (hp 39) (hp 5) t4
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t3) (Eq.symm t5))
  · have t0 := move_eq p (hp 106) (hp 1) h0
    have t1 := move_eq q (hq 39) (hq 5) t0
    have t2 := move_eq p.symm (reverse_move p (hp 147)) (reverse_move p (hp 58)) t1
    have t3 := move_eq p.symm (reverse_move p (hp 29)) (reverse_move p (hp 31)) hit
    have t4 := move_eq p.symm (reverse_move p (hp 91)) (reverse_move p (hp 9)) (Eq.symm t3)
    have t5 := move_eq p.symm (reverse_move p (hp 142)) (reverse_move p (hp 31)) t4
    have t6 := move_eq q.symm (reverse_move q (hq 96)) (reverse_move q (hq 58)) (Eq.trans t5 (Eq.symm t3))
    have t7 := move_eq p (hp 147) (hp 18) (Eq.trans (Eq.trans t2 (Eq.symm t6)) t1)
    have t8 := move_eq p (hp 96) (hp 18) t1
    have t9 := move_eq p (hp 39) (hp 5) t0
    have t10 := move_eq q (hq 17) (hq 12) (Eq.symm t9)
    have t11 := move_eq p (hp 86) (hp 9) hit
    have t12 := move_eq q.symm (reverse_move q (hq 54)) (reverse_move q (hq 58)) t11
    have t13 := move_eq p (hp 33) (hp 18) (Eq.trans (Eq.trans t8 (Eq.symm t7)) t1)
    have t14 := move_eq p.symm (reverse_move p (hp 105)) (reverse_move p (hp 33)) (Eq.trans (Eq.trans (Eq.trans (Eq.trans (Eq.symm t10) t12) (Eq.symm t6)) t7) (Eq.symm t13))
    have t15 := move_eq q.symm (reverse_move q (hq 154)) (reverse_move q (hq 7)) h0
    have t16 := move_eq p (hp 159) (hp 7) t15
    have t17 := move_eq q (hq 111) (hq 23) t16
    have t18 := move_eq q (hq 153) (hq 72) t17
    have t19 := move_eq q.symm (reverse_move q (hq 92)) (reverse_move q (hq 58)) (Eq.symm t3)
    have t20 := move_eq q.symm (reverse_move q (hq 47)) (reverse_move q (hq 17)) (Eq.trans t19 (Eq.symm t12))
    have t21 := move_eq q.symm (reverse_move q (hq 145)) (reverse_move q (hq 2)) hit
    have t22 := move_eq q.symm (reverse_move q (hq 83)) (reverse_move q (hq 0)) t21
    have t23 := move_eq p.symm (reverse_move p (hp 28)) (reverse_move p (hp 3)) t22
    have t24 := move_eq p.symm (reverse_move p (hp 84)) (reverse_move p (hp 12)) t23
    have t25 := move_eq p (hp 47) (hp 12) (Eq.trans t20 (Eq.symm t9))
    have t26 := move_eq q (hq 47) (hq 3) (Eq.trans (Eq.trans (Eq.trans t20 (Eq.symm t9)) (Eq.symm t24)) t25)
    have t27 := move_eq q (hq 28) (hq 3) t23
    have t28 := move_eq p.symm (reverse_move p (hp 26)) (reverse_move p (hp 2)) (Eq.trans (Eq.trans (Eq.trans t12 (Eq.symm t19)) t26) (Eq.symm t27))
    have t29 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 0)) (Eq.trans (Eq.trans (Eq.trans (Eq.trans t7 (Eq.symm t8)) (Eq.symm t14)) t18) t28)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t29)
  · exact branch54 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · have t0 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 31)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 91)) (reverse_move p (hp 31)) (Eq.symm t0)
    have t2 := move_eq p.symm (reverse_move p (hp 142)) (reverse_move p (hp 31)) (Eq.trans t1 (Eq.symm t0))
    have t3 := move_eq q.symm (reverse_move q (hq 96)) (reverse_move q (hq 2)) (Eq.trans t2 (Eq.symm t0))
    have t4 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 0)) t3
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t4)
  · have t0 := move_eq p (hp 106) (hp 1) h0
    have t1 := move_eq q.symm (reverse_move q (hq 58)) (reverse_move q (hq 0)) hit
    have t2 := move_eq p (hp 58) (hp 0) t1
    have t3 := move_eq q.symm (reverse_move q (hq 5)) (reverse_move q (hq 7)) t2
    exact branch46 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans t0 t3)
  · have t0 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 31)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 91)) (reverse_move p (hp 31)) (Eq.symm t0)
    have t2 := move_eq p.symm (reverse_move p (hp 142)) (reverse_move p (hp 31)) (Eq.trans t1 (Eq.symm t0))
    have t3 := move_eq q.symm (reverse_move q (hq 96)) (reverse_move q (hq 2)) (Eq.trans t2 (Eq.symm t0))
    have t4 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 0)) t3
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t4)
  · have t0 := move_eq p (hp 106) (hp 1) h0
    have t1 := move_eq q.symm (reverse_move q (hq 58)) (reverse_move q (hq 0)) hit
    have t2 := move_eq p (hp 58) (hp 0) t1
    have t3 := move_eq q.symm (reverse_move q (hq 5)) (reverse_move q (hq 7)) t2
    exact branch46 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans t0 t3)
  · have t0 := move_eq q.symm (reverse_move q (hq 2)) (reverse_move q (hq 0)) hit
    exact branch8 p q v hq sep (Eq.symm t0)
  · have t0 := move_eq q.symm (reverse_move q (hq 2)) (reverse_move q (hq 0)) hit
    exact branch8 p q v hq sep (Eq.symm t0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp sep G e₀ e₁ e₂ no in
private theorem branch55 (h0 : v 227 = v 42) : False := by
  have t0 := move_eq p (hp 159) (hp 42) h0
  have t1 := move_eq p (hp 111) (hp 13) t0
  have t2 := move_eq p (hp 159) (hp 41) (Eq.trans h0 t1)
  have t3 := move_eq p (hp 60) (hp 13) (Eq.trans (Eq.symm t2) t0)
  have t4 := move_eq p (hp 159) (hp 19) (Eq.trans (Eq.trans h0 t1) (Eq.symm t3))
  exact short4 p q G sep e₀ e₁ e₂ no ![0,1,0,1] (by decide)
    (v 13) (v 13) (v 19) (v 19)
    (rfl) (Eq.trans (hp 19) (Eq.trans (Eq.symm t4) t0)) (rfl) (Eq.trans (hp 13) (Eq.symm t3))

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp sep G e₀ e₁ e₂ no in
private theorem branch56 (h0 : v 227 = v 41) : False := by
  have t0 := move_eq p (hp 159) (hp 41) h0
  have t1 := move_eq p (hp 111) (hp 60) t0
  have t2 := move_eq p (hp 42) (hp 19) t1
  exact short8 p q G sep e₀ e₁ e₂ no ![0,1,0,1,0,1,0,1] (by decide)
    (v 13) (v 13) (v 19) (v 19) (v 60) (v 60) (v 41) (v 41)
    (rfl) (Eq.trans (hp 19) (Eq.symm t2)) (rfl) (hp 60) (rfl) (hp 41) (rfl) (hp 13)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch57 (h0 : v 227 = v 60) : False := by
  have t0 := move_eq q (hq 154) (hq 60) h0
  rcases collision16 (fun h => no (.inr (.inr (.inl h))))
    (v 0) (v 0) (v 3) (v 3) (v 12) (v 12) (v 39) (v 39) (v 106) (v 106) (v 60) (v 19) (v 19) (v 5) (v 1) (v 1)
    (e₀ (v 0))
    ((hp 3) ▸ e₁ (v 3))
    (e₀ (v 3))
    ((hp 12) ▸ e₁ (v 12))
    (e₀ (v 12))
    ((hp 39) ▸ e₁ (v 39))
    (e₀ (v 39))
    ((hp 106) ▸ e₁ (v 106))
    (e₀ (v 106))
    ((Eq.trans (hq 60) (Eq.symm t0)) ▸ e₂ (v 60))
    ((hp 60) ▸ e₁ (v 60))
    (e₀ (v 19))
    ((hq 19) ▸ e₂ (v 19))
    ((hp 1) ▸ e₁ (v 1))
    (e₀ (v 1))
    ((hp 0) ▸ e₁ (v 0)) with hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit
  · exact branch1 p q v hp sep hit
  · exact branch2 p q v hp sep G e₀ e₁ e₂ no hit
  · exact branch3 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch16 p q v hp sep G e₀ e₁ e₂ no hit
  · exact branch28 p q v hp hq sep hit
  · exact branch29 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 0)) (reverse_move p (hp 3)) (Eq.symm hit)
    exact branch1 p q v hp sep t0
  · exact branch1 p q v hp sep hit
  · exact branch2 p q v hp sep G e₀ e₁ e₂ no hit
  · exact branch3 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch16 p q v hp sep G e₀ e₁ e₂ no hit
  · exact branch29 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 1)) (reverse_move p (hp 3)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 12)) (reverse_move p (hp 0)) (Eq.symm t0)
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p.symm (reverse_move p (hp 0)) (reverse_move p (hp 3)) (Eq.symm hit)
    exact branch1 p q v hp sep t0
  · have t0 := move_eq p (hp 12) (hp 3) (Eq.symm hit)
    exact branch1 p q v hp sep (Eq.symm t0)
  · have t0 := move_eq p (hp 39) (hp 3) (Eq.symm hit)
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 106) (hp 3) (Eq.symm hit)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 60) (hp 3) (Eq.symm hit)
    exact branch29 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 19) (hp 3) (Eq.symm hit)
    exact branch32 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 12)) (reverse_move p (hp 0)) hit
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 12) (hp 3) (Eq.symm hit)
    exact branch1 p q v hp sep (Eq.symm t0)
  · have t0 := move_eq p (hp 39) (hp 3) (Eq.symm hit)
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 106) (hp 3) (Eq.symm hit)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 19) (hp 3) (Eq.symm hit)
    exact branch32 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq q.symm (reverse_move q (hq 19)) (reverse_move q (hq 13)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 60)) (reverse_move p (hp 42)) t0
    exact branch55 p q v hp sep G e₀ e₁ e₂ no (Eq.trans h0 t1)
  · have t0 := move_eq p.symm (reverse_move p (hp 12)) (reverse_move p (hp 0)) hit
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 39) (hp 12) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 12)) (Eq.trans (Eq.symm hit) t0)
    have t2 := move_eq p (hp 106) (hp 3) (Eq.trans t1 t0)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq p.symm (reverse_move p (hp 158)) (reverse_move p (hp 39)) (Eq.symm hit)
    have t1 := move_eq p (hp 106) (hp 12) (Eq.symm hit)
    have t2 := move_eq p (hp 158) (hp 3) (Eq.trans t0 t1)
    exact branch16 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq p (hp 60) (hp 12) (Eq.symm hit)
    have t1 := move_eq p (hp 19) (hp 3) t0
    exact branch32 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p (hp 19) (hp 12) (Eq.symm hit)
    exact branch34 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 0)) hit
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 39) (hp 12) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 12)) (Eq.trans (Eq.symm hit) t0)
    have t2 := move_eq p (hp 106) (hp 3) (Eq.trans t1 t0)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq p.symm (reverse_move p (hp 158)) (reverse_move p (hp 39)) (Eq.symm hit)
    have t1 := move_eq p (hp 106) (hp 12) (Eq.symm hit)
    have t2 := move_eq p (hp 158) (hp 3) (Eq.trans t0 t1)
    exact branch16 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq p (hp 19) (hp 12) (Eq.symm hit)
    exact branch34 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 1)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 0)) t0
    exact branch16 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 0)) hit
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 106) (hp 39) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 158)) (reverse_move p (hp 39)) (Eq.trans (Eq.symm hit) t0)
    have t2 := move_eq p (hp 158) (hp 12) (Eq.trans t1 t0)
    have t3 := move_eq p (hp 12) (hp 3) (Eq.trans (Eq.trans (Eq.symm t0) hit) t2)
    exact branch1 p q v hp sep (Eq.symm t3)
  · have t0 := move_eq p (hp 60) (hp 39) (Eq.symm hit)
    have t1 := move_eq p (hp 19) (hp 12) t0
    exact branch34 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p (hp 39) (hp 19) hit
    exact branch40 p q v hp hq sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 0)) hit
    exact branch16 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 106) (hp 39) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 158)) (reverse_move p (hp 39)) (Eq.trans (Eq.symm hit) t0)
    have t2 := move_eq p (hp 158) (hp 12) (Eq.trans t1 t0)
    have t3 := move_eq p (hp 12) (hp 3) (Eq.trans (Eq.trans (Eq.symm t0) hit) t2)
    exact branch1 p q v hp sep (Eq.symm t3)
  · have t0 := move_eq p (hp 39) (hp 19) hit
    exact branch40 p q v hp hq sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 1)) hit
    exact branch52 p q v hp hq sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 0)) hit
    exact branch16 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 106) (hp 60) hit
    have t1 := move_eq p (hp 39) (hp 19) t0
    exact branch40 p q v hp hq sep G e₀ e₁ e₂ no t1
  · have t0 := move_eq p (hp 106) (hp 19) hit
    exact branch47 p q v hp hq sep G e₀ e₁ e₂ no t0
  · exact branch52 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p (hp 106) (hp 19) hit
    exact branch47 p q v hp hq sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq q.symm (reverse_move q (hq 154)) (reverse_move q (hq 19)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 41)) (reverse_move p (hp 60)) (Eq.trans (Eq.symm h0) t0)
    exact branch56 p q v hp sep G e₀ e₁ e₂ no (Eq.trans h0 (Eq.symm t1))
  · exact branch52 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 41)) (reverse_move p (hp 60)) hit
    exact branch56 p q v hp sep G e₀ e₁ e₂ no (Eq.trans h0 (Eq.symm t0))
  · have t0 := move_eq p.symm (reverse_move p (hp 41)) (reverse_move p (hp 0)) hit
    exact branch27 p q v hp hq sep (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 60)) (reverse_move p (hp 1)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 41)) (reverse_move p (hp 0)) t0
    exact branch27 p q v hp hq sep (Eq.symm t1)
  · have t0 := move_eq p.symm (reverse_move p (hp 60)) (reverse_move p (hp 0)) hit
    exact branch28 p q v hp hq sep (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 60)) (reverse_move p (hp 0)) hit
    exact branch28 p q v hp hq sep (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 1)) (reverse_move p (hp 0)) hit
    have t1 := move_eq p (hp 5) (hp 1) hit
    have t2 := move_eq p.symm (reverse_move p (hp 5)) (reverse_move p (hp 3)) (Eq.trans (Eq.trans t1 hit) t0)
    exact branch1 p q v hp sep (Eq.trans (Eq.trans (Eq.symm t0) (Eq.symm hit)) t2)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hq sep G e₀ e₁ e₂ no in
private theorem branch59 (h1 : v 0 = v 9) : False := by
  exact short4 p q G sep e₀ e₁ e₂ no ![0,2,0,2] (by decide)
    (v 0) (v 0) (v 2) (v 2)
    (rfl) (Eq.trans (hq 2) (Eq.symm h1)) (rfl) (hq 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch60 (h0 : v 227 = v 19) (h1 : v 0 = v 18) : False := by
  have t0 := move_eq q (hq 154) (hq 19) h0
  have t1 := move_eq q.symm (reverse_move q (hq 5)) (reverse_move q (hq 4)) (Eq.symm h1)
  have t2 := move_eq p (hp 106) (hp 4) (Eq.trans t0 t1)
  have t3 := move_eq p.symm (reverse_move p (hp 58)) (reverse_move p (hp 3)) (Eq.symm h1)
  have t4 := move_eq p.symm (reverse_move p (hp 35)) (reverse_move p (hp 12)) t3
  have t5 := move_eq p.symm (reverse_move p (hp 11)) (reverse_move p (hp 39)) t4
  exact short8 p q G sep e₀ e₁ e₂ no ![0,1,2,1,0,1,0,1] (by decide)
    (v 0) (v 0) (v 3) (v 11) (v 4) (v 4) (v 1) (v 1)
    (rfl) (hp 3) (hq 3) (Eq.trans (hp 4) (Eq.trans (Eq.symm t2) (Eq.symm t5))) (rfl) (Eq.trans (hp 1) t1) (rfl) (hp 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch61 (h1 : v 0 = v 29) : False := by
  have t0 := move_eq q.symm (reverse_move q (hq 58)) (reverse_move q (hq 4)) (Eq.symm h1)
  have t1 := move_eq p (hp 58) (hp 4) t0
  exact short8 p q G sep e₀ e₁ e₂ no ![0,2,1,2,0,1,0,1] (by decide)
    (v 0) (v 0) (v 4) (v 14) (v 5) (v 5) (v 1) (v 1)
    (rfl) (hq 4) (hp 4) (Eq.trans (hq 5) t1) (rfl) (hp 1) (rfl) (hp 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch62 (h0 : v 227 = v 19) (h1 : v 12 = v 29) : False := by
  have t0 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 39)) (Eq.symm h1)
  have t1 := move_eq q (hq 39) (hq 9) (Eq.symm t0)
  have t2 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 31)) (Eq.symm t0)
  have t3 := move_eq q (hq 154) (hq 19) h0
  have t4 := move_eq p.symm (reverse_move p (hp 91)) (reverse_move p (hp 1)) (Eq.trans (Eq.symm t2) t3)
  have t5 := move_eq p.symm (reverse_move p (hp 142)) (reverse_move p (hp 0)) t4
  have t6 := move_eq q.symm (reverse_move q (hq 96)) (reverse_move q (hq 4)) t5
  exact short8 p q G sep e₀ e₁ e₂ no ![0,2,0,2,0,2,0,2] (by decide)
    (v 0) (v 0) (v 4) (v 4) (v 9) (v 9) (v 2) (v 2)
    (rfl) (hq 4) (rfl) (Eq.trans (hq 9) (Eq.trans (Eq.symm t1) t6)) (rfl) (hq 2) (rfl) (hq 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep in
private theorem branch63 (h1 : v 17 = v 18) : False := by
  have t0 := move_eq p.symm (reverse_move p (hp 58)) (reverse_move p (hp 5)) (Eq.symm h1)
  have t1 := move_eq p.symm (reverse_move p (hp 35)) (reverse_move p (hp 1)) t0
  have t2 := move_eq p.symm (reverse_move p (hp 11)) (reverse_move p (hp 0)) t1
  exact (sep (v 3)).2.2 (Eq.trans (hp 3) (Eq.symm (Eq.trans (hq 3) t2)))

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch64 (h1 : v 17 = v 29) : False := by
  have t0 := move_eq q.symm (reverse_move q (hq 58)) (reverse_move q (hq 55)) (Eq.symm h1)
  have t1 := move_eq p (hp 58) (hp 55) t0
  exact short4 p q G sep e₀ e₁ e₂ no ![1,2,1,2] (by decide)
    (v 5) (v 17) (v 55) (v 18)
    (hp 5) (hq 55) (Eq.trans (hp 55) (Eq.symm t1)) (hq 5)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch58 (h0 : v 227 = v 19) : False := by
  have t0 := move_eq q (hq 154) (hq 19) h0
  have t1 := move_eq p (hp 106) (hp 5) t0
  have t2 := move_eq p (hp 39) (hp 17) t1
  rcases collision16 (fun h => no (.inr (.inr (.inl h))))
    (v 0) (v 0) (v 3) (v 3) (v 12) (v 12) (v 17) (v 17) (v 5) (v 18) (v 58) (v 29) (v 9) (v 9) (v 2) (v 2)
    (e₀ (v 0))
    ((hp 3) ▸ e₁ (v 3))
    (e₀ (v 3))
    ((hp 12) ▸ e₁ (v 12))
    (e₀ (v 12))
    ((Eq.trans (hp 17) (Eq.symm t2)) ▸ e₁ (v 17))
    (e₀ (v 17))
    ((hp 5) ▸ e₁ (v 5))
    ((hq 5) ▸ e₂ (v 5))
    ((hp 58) ▸ e₁ (v 58))
    ((hq 58) ▸ e₂ (v 58))
    ((hp 9) ▸ e₁ (v 9))
    (e₀ (v 9))
    ((hq 2) ▸ e₂ (v 2))
    (e₀ (v 2))
    ((hq 0) ▸ e₂ (v 0)) with hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit
  · exact branch1 p q v hp sep hit
  · exact branch2 p q v hp sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p (hp 17) (hp 0) (Eq.symm hit)
    have t1 := move_eq p (hp 53) (hp 1) t0
    have t2 := move_eq p.symm (reverse_move p (hp 5)) (reverse_move p (hp 3)) (Eq.symm hit)
    have t3 := move_eq p.symm (reverse_move p (hp 53)) (reverse_move p (hp 12)) (Eq.trans t1 t2)
    have t4 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 0)) (Eq.trans (Eq.symm t3) t0)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t4)
  · have t0 := move_eq q.symm (reverse_move q (hq 19)) (reverse_move q (hq 4)) (Eq.symm hit)
    have t1 := move_eq q (hq 154) (hq 4) (Eq.trans h0 t0)
    exact branch16 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq q (hq 154) (hq 19) h0
    have t1 := move_eq p (hp 58) (hp 0) (Eq.symm hit)
    have t2 := move_eq q.symm (reverse_move q (hq 5)) (reverse_move q (hq 7)) t1
    exact branch50 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans t0 t2)
  · exact branch59 p q v hq sep G e₀ e₁ e₂ no hit
  · exact branch8 p q v hq sep hit
  · exact branch1 p q v hp sep hit
  · exact branch2 p q v hp sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p (hp 17) (hp 0) (Eq.symm hit)
    have t1 := move_eq p (hp 53) (hp 1) t0
    have t2 := move_eq p.symm (reverse_move p (hp 5)) (reverse_move p (hp 3)) (Eq.symm hit)
    have t3 := move_eq p.symm (reverse_move p (hp 53)) (reverse_move p (hp 12)) (Eq.trans t1 t2)
    have t4 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 0)) (Eq.trans (Eq.symm t3) t0)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t4)
  · exact branch60 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · exact branch61 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch59 p q v hq sep G e₀ e₁ e₂ no hit
  · exact branch8 p q v hq sep hit
  · have t0 := move_eq p (hp 12) (hp 3) (Eq.symm hit)
    exact branch1 p q v hp sep (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 5)) (reverse_move p (hp 12)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 1)) (Eq.symm t0)
    have t2 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 0)) t1
    exact branch16 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq p.symm (reverse_move p (hp 1)) (reverse_move p (hp 12)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 0)) (Eq.symm t0)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p (hp 58) (hp 3) (Eq.symm hit)
    exact branch60 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.symm t0)
  · have t0 := move_eq p (hp 9) (hp 3) (Eq.symm hit)
    exact branch61 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · exact branch10 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p (hp 12) (hp 3) (Eq.symm hit)
    exact branch1 p q v hp sep (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 5)) (reverse_move p (hp 12)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 1)) (Eq.symm t0)
    have t2 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 0)) t1
    exact branch16 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq q.symm (reverse_move q (hq 5)) (reverse_move q (hq 13)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 42)) (reverse_move p (hp 1)) (Eq.symm t0)
    have t2 := move_eq p.symm (reverse_move p (hp 111)) (reverse_move p (hp 0)) t1
    exact branch25 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · exact branch42 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p (hp 9) (hp 3) (Eq.symm hit)
    exact branch61 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · exact branch10 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 5)) (reverse_move p (hp 39)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 1)) (Eq.symm t0)
    exact branch52 p q v hp hq sep G e₀ e₁ e₂ no t1
  · have t0 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 1)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 0)) t0
    exact branch16 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p (hp 159) (hp 19) h0
    have t1 := move_eq q (hq 111) (hq 59) t0
    have t2 := move_eq q (hq 58) (hq 12) (Eq.symm hit)
    have t3 := move_eq p.symm (reverse_move p (hp 105)) (reverse_move p (hp 9)) (Eq.symm t2)
    have t4 := move_eq q.symm (reverse_move q (hq 153)) (reverse_move q (hq 2)) t3
    have t5 := move_eq q.symm (reverse_move q (hq 59)) (reverse_move q (hq 0)) (Eq.trans (Eq.symm t1) t4)
    exact branch32 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t5)
  · have t0 := move_eq p (hp 12) (hp 9) hit
    exact branch42 p q v hp hq sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq q.symm (reverse_move q (hq 40)) (reverse_move q (hq 0)) hit
    have t1 := move_eq p (hp 40) (hp 0) t0
    have t2 := move_eq p (hp 75) (hp 1) t1
    have t3 := move_eq p (hp 24) (hp 5) t2
    have t4 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 10)) hit
    have t5 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 33)) t4
    have t6 := move_eq q (hq 154) (hq 19) h0
    have t7 := move_eq p (hp 33) (hp 5) (Eq.trans (Eq.symm t5) t6)
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans t3 (Eq.symm t7))
  · have t0 := move_eq p.symm (reverse_move p (hp 5)) (reverse_move p (hp 39)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 1)) (Eq.symm t0)
    exact branch52 p q v hp hq sep G e₀ e₁ e₂ no t1
  · have t0 := move_eq p (hp 18) (hp 12) (Eq.symm hit)
    have t1 := move_eq q (hq 56) (hq 3) t0
    have t2 := move_eq p.symm (reverse_move p (hp 58)) (reverse_move p (hp 39)) (Eq.symm hit)
    have t3 := move_eq p.symm (reverse_move p (hp 35)) (reverse_move p (hp 106)) t2
    have t4 := move_eq q (hq 154) (hq 19) h0
    have t5 := move_eq p.symm (reverse_move p (hp 11)) (reverse_move p (hp 1)) (Eq.trans t3 t4)
    have t6 := move_eq q.symm (reverse_move q (hq 56)) (reverse_move q (hq 7)) (Eq.trans t1 t5)
    have t7 := move_eq p (hp 7) (hp 3) (Eq.trans (Eq.symm t6) t0)
    exact branch6 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t7)
  · exact branch62 p q v hp hq sep G e₀ e₁ e₂ no h0 hit
  · have t0 := move_eq p (hp 12) (hp 9) hit
    exact branch42 p q v hp hq sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq q.symm (reverse_move q (hq 40)) (reverse_move q (hq 0)) hit
    have t1 := move_eq p (hp 40) (hp 0) t0
    have t2 := move_eq p (hp 75) (hp 1) t1
    have t3 := move_eq p (hp 24) (hp 5) t2
    have t4 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 10)) hit
    have t5 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 33)) t4
    have t6 := move_eq q (hq 154) (hq 19) h0
    have t7 := move_eq p (hp 33) (hp 5) (Eq.trans (Eq.symm t5) t6)
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans t3 (Eq.symm t7))
  · have t0 := move_eq q (hq 154) (hq 19) h0
    have t1 := move_eq p.symm (reverse_move p (hp 5)) (reverse_move p (hp 1)) hit
    exact branch52 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans t0 t1)
  · have t0 := move_eq p (hp 58) (hp 17) (Eq.symm hit)
    have t1 := move_eq q.symm (reverse_move q (hq 127)) (reverse_move q (hq 5)) (Eq.symm t0)
    have t2 := move_eq p.symm (reverse_move p (hp 71)) (reverse_move p (hp 1)) t1
    have t3 := move_eq p.symm (reverse_move p (hp 23)) (reverse_move p (hp 0)) t2
    exact branch6 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t3)
  · have t0 := move_eq q.symm (reverse_move q (hq 55)) (reverse_move q (hq 2)) hit
    have t1 := move_eq q.symm (reverse_move q (hq 128)) (reverse_move q (hq 0)) t0
    have t2 := move_eq p.symm (reverse_move p (hp 73)) (reverse_move p (hp 3)) t1
    have t3 := move_eq p.symm (reverse_move p (hp 50)) (reverse_move p (hp 12)) t2
    have t4 := move_eq p.symm (reverse_move p (hp 5)) (reverse_move p (hp 31)) hit
    have t5 := move_eq p.symm (reverse_move p (hp 91)) (reverse_move p (hp 1)) (Eq.symm t4)
    have t6 := move_eq p.symm (reverse_move p (hp 142)) (reverse_move p (hp 0)) t5
    have t7 := move_eq q.symm (reverse_move q (hq 96)) (reverse_move q (hq 4)) t6
    have t8 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 16)) t7
    have t9 := move_eq q (hq 154) (hq 19) h0
    have t10 := move_eq p (hp 106) (hp 5) t9
    have t11 := move_eq p (hp 16) (hp 9) (Eq.trans (Eq.trans (Eq.symm t8) t10) hit)
    exact branch62 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.trans (Eq.symm t3) t11)
  · have t0 := move_eq q.symm (reverse_move q (hq 55)) (reverse_move q (hq 0)) hit
    have t1 := move_eq q.symm (reverse_move q (hq 128)) (reverse_move q (hq 4)) t0
    have t2 := move_eq p.symm (reverse_move p (hp 5)) (reverse_move p (hp 10)) hit
    have t3 := move_eq p.symm (reverse_move p (hp 33)) (reverse_move p (hp 1)) (Eq.symm t2)
    have t4 := move_eq p.symm (reverse_move p (hp 96)) (reverse_move p (hp 0)) t3
    have t5 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 4)) t4
    have t6 := move_eq q (hq 154) (hq 19) h0
    have t7 := move_eq p (hp 106) (hp 5) t6
    have t8 := move_eq q (hq 128) (hq 2) (Eq.trans (Eq.trans (Eq.trans t1 (Eq.symm t5)) t7) hit)
    exact branch59 p q v hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t0) t8)
  · exact branch63 p q v hp hq sep hit
  · exact branch64 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq q.symm (reverse_move q (hq 55)) (reverse_move q (hq 2)) hit
    have t1 := move_eq q.symm (reverse_move q (hq 128)) (reverse_move q (hq 0)) t0
    have t2 := move_eq p.symm (reverse_move p (hp 73)) (reverse_move p (hp 3)) t1
    have t3 := move_eq p.symm (reverse_move p (hp 50)) (reverse_move p (hp 12)) t2
    have t4 := move_eq p.symm (reverse_move p (hp 5)) (reverse_move p (hp 31)) hit
    have t5 := move_eq p.symm (reverse_move p (hp 91)) (reverse_move p (hp 1)) (Eq.symm t4)
    have t6 := move_eq p.symm (reverse_move p (hp 142)) (reverse_move p (hp 0)) t5
    have t7 := move_eq q.symm (reverse_move q (hq 96)) (reverse_move q (hq 4)) t6
    have t8 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 16)) t7
    have t9 := move_eq q (hq 154) (hq 19) h0
    have t10 := move_eq p (hp 106) (hp 5) t9
    have t11 := move_eq p (hp 16) (hp 9) (Eq.trans (Eq.trans (Eq.symm t8) t10) hit)
    exact branch62 p q v hp hq sep G e₀ e₁ e₂ no h0 (Eq.trans (Eq.symm t3) t11)
  · have t0 := move_eq q.symm (reverse_move q (hq 55)) (reverse_move q (hq 0)) hit
    have t1 := move_eq q.symm (reverse_move q (hq 128)) (reverse_move q (hq 4)) t0
    have t2 := move_eq p.symm (reverse_move p (hp 5)) (reverse_move p (hp 10)) hit
    have t3 := move_eq p.symm (reverse_move p (hp 33)) (reverse_move p (hp 1)) (Eq.symm t2)
    have t4 := move_eq p.symm (reverse_move p (hp 96)) (reverse_move p (hp 0)) t3
    have t5 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 4)) t4
    have t6 := move_eq q (hq 154) (hq 19) h0
    have t7 := move_eq p (hp 106) (hp 5) t6
    have t8 := move_eq q (hq 128) (hq 2) (Eq.trans (Eq.trans (Eq.trans t1 (Eq.symm t5)) t7) hit)
    exact branch59 p q v hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t0) t8)
  · have t0 := move_eq p (hp 58) (hp 5) (Eq.symm hit)
    exact branch63 p q v hp hq sep (Eq.symm t0)
  · have t0 := move_eq p (hp 9) (hp 5) (Eq.symm hit)
    exact branch64 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq q.symm (reverse_move q (hq 19)) (reverse_move q (hq 0)) hit
    exact branch29 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq q.symm (reverse_move q (hq 58)) (reverse_move q (hq 5)) (Eq.symm hit)
    have t1 := move_eq p (hp 58) (hp 5) t0
    exact branch63 p q v hp hq sep (Eq.symm t1)
  · have t0 := move_eq q.symm (reverse_move q (hq 5)) (reverse_move q (hq 2)) hit
    have t1 := move_eq q.symm (reverse_move q (hq 19)) (reverse_move q (hq 0)) t0
    exact branch29 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq q.symm (reverse_move q (hq 5)) (reverse_move q (hq 0)) hit
    have t1 := move_eq q (hq 154) (hq 19) h0
    exact branch16 p q v hp sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t0) (Eq.symm t1))
  · have t0 := move_eq p (hp 58) (hp 9) hit
    have t1 := move_eq q.symm (reverse_move q (hq 58)) (reverse_move q (hq 5)) (Eq.symm t0)
    have t2 := move_eq p (hp 58) (hp 5) t1
    exact branch63 p q v hp hq sep (Eq.symm t2)
  · have t0 := move_eq q (hq 58) (hq 2) hit
    have t1 := move_eq p (hp 29) (hp 9) t0
    have t2 := move_eq q.symm (reverse_move q (hq 145)) (reverse_move q (hq 2)) (Eq.trans t1 t0)
    have t3 := move_eq q.symm (reverse_move q (hq 83)) (reverse_move q (hq 0)) t2
    have t4 := move_eq p (hp 58) (hp 2) hit
    have t5 := move_eq q.symm (reverse_move q (hq 5)) (reverse_move q (hq 28)) t4
    have t6 := move_eq p (hp 28) (hp 5) (Eq.symm t5)
    have t7 := move_eq q (hq 154) (hq 19) h0
    have t8 := move_eq p (hp 106) (hp 5) t7
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.trans (Eq.symm t3) t6) (Eq.symm t8))
  · have t0 := move_eq p.symm (reverse_move p (hp 9)) (reverse_move p (hp 31)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 91)) (reverse_move p (hp 31)) (Eq.symm t0)
    have t2 := move_eq p.symm (reverse_move p (hp 142)) (reverse_move p (hp 31)) (Eq.trans t1 (Eq.symm t0))
    have t3 := move_eq q.symm (reverse_move q (hq 96)) (reverse_move q (hq 2)) (Eq.trans t2 (Eq.symm t0))
    have t4 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 0)) t3
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t4)
  · have t0 := move_eq q (hq 154) (hq 19) h0
    have t1 := move_eq q.symm (reverse_move q (hq 58)) (reverse_move q (hq 0)) hit
    have t2 := move_eq p (hp 58) (hp 0) t1
    have t3 := move_eq q.symm (reverse_move q (hq 5)) (reverse_move q (hq 7)) t2
    exact branch50 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans t0 t3)
  · have t0 := move_eq q.symm (reverse_move q (hq 2)) (reverse_move q (hq 0)) hit
    exact branch8 p q v hq sep (Eq.symm t0)
  · have t0 := move_eq q.symm (reverse_move q (hq 2)) (reverse_move q (hq 0)) hit
    exact branch8 p q v hq sep (Eq.symm t0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch65 (h0 : v 227 = v 77) : False := by
  have t0 := move_eq q (hq 154) (hq 77) h0
  rcases collision16 (fun h => no (.inr (.inr (.inl h))))
    (v 0) (v 0) (v 3) (v 3) (v 12) (v 12) (v 39) (v 39) (v 106) (v 106) (v 77) (v 77) (v 25) (v 7) (v 7) (v 1)
    (e₀ (v 0))
    ((hp 3) ▸ e₁ (v 3))
    (e₀ (v 3))
    ((hp 12) ▸ e₁ (v 12))
    (e₀ (v 12))
    ((hp 39) ▸ e₁ (v 39))
    (e₀ (v 39))
    ((hp 106) ▸ e₁ (v 106))
    (e₀ (v 106))
    ((Eq.trans (hq 77) (Eq.symm t0)) ▸ e₂ (v 77))
    (e₀ (v 77))
    ((hp 25) ▸ e₁ (v 25))
    ((hq 25) ▸ e₂ (v 25))
    (e₀ (v 7))
    ((hq 7) ▸ e₂ (v 7))
    ((hp 0) ▸ e₁ (v 0)) with hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit
  · exact branch1 p q v hp sep hit
  · exact branch2 p q v hp sep G e₀ e₁ e₂ no hit
  · exact branch3 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch16 p q v hp sep G e₀ e₁ e₂ no hit
  · exact branch31 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq q (hq 25) (hq 0) (Eq.symm hit)
    exact branch13 p q v hp hq sep G e₀ e₁ e₂ no t0
  · exact branch4 p q v hp hq sep hit
  · exact branch1 p q v hp sep hit
  · exact branch2 p q v hp sep G e₀ e₁ e₂ no hit
  · exact branch3 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch16 p q v hp sep G e₀ e₁ e₂ no hit
  · exact branch31 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch4 p q v hp hq sep hit
  · have t0 := move_eq p.symm (reverse_move p (hp 0)) (reverse_move p (hp 3)) (Eq.symm hit)
    exact branch1 p q v hp sep t0
  · have t0 := move_eq p (hp 12) (hp 3) (Eq.symm hit)
    exact branch1 p q v hp sep (Eq.symm t0)
  · have t0 := move_eq p (hp 39) (hp 3) (Eq.symm hit)
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 106) (hp 3) (Eq.symm hit)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 77) (hp 3) (Eq.symm hit)
    exact branch30 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 25) (hp 3) (Eq.symm hit)
    exact branch31 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 7) (hp 3) (Eq.symm hit)
    exact branch6 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 12) (hp 3) (Eq.symm hit)
    exact branch1 p q v hp sep (Eq.symm t0)
  · have t0 := move_eq p (hp 39) (hp 3) (Eq.symm hit)
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 106) (hp 3) (Eq.symm hit)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 77) (hp 3) (Eq.symm hit)
    exact branch30 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 7) (hp 3) (Eq.symm hit)
    exact branch6 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 12)) (reverse_move p (hp 0)) hit
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 39) (hp 12) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 12)) (Eq.trans (Eq.symm hit) t0)
    have t2 := move_eq p (hp 106) (hp 3) (Eq.trans t1 t0)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq p.symm (reverse_move p (hp 158)) (reverse_move p (hp 39)) (Eq.symm hit)
    have t1 := move_eq p (hp 106) (hp 12) (Eq.symm hit)
    have t2 := move_eq p (hp 158) (hp 3) (Eq.trans t0 t1)
    exact branch16 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq p (hp 77) (hp 12) (Eq.symm hit)
    exact branch33 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 25) (hp 12) (Eq.symm hit)
    have t1 := move_eq p (hp 77) (hp 3) t0
    exact branch30 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · exact branch39 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p (hp 39) (hp 12) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 12)) (Eq.trans (Eq.symm hit) t0)
    have t2 := move_eq p (hp 106) (hp 3) (Eq.trans t1 t0)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq p.symm (reverse_move p (hp 158)) (reverse_move p (hp 39)) (Eq.symm hit)
    have t1 := move_eq p (hp 106) (hp 12) (Eq.symm hit)
    have t2 := move_eq p (hp 158) (hp 3) (Eq.trans t0 t1)
    exact branch16 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq p (hp 77) (hp 12) (Eq.symm hit)
    exact branch33 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · exact branch39 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 0)) hit
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 106) (hp 39) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 158)) (reverse_move p (hp 39)) (Eq.trans (Eq.symm hit) t0)
    have t2 := move_eq p (hp 158) (hp 12) (Eq.trans t1 t0)
    have t3 := move_eq p (hp 12) (hp 3) (Eq.trans (Eq.trans (Eq.symm t0) hit) t2)
    exact branch1 p q v hp sep (Eq.symm t3)
  · have t0 := move_eq p (hp 77) (hp 39) (Eq.symm hit)
    exact branch35 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 39) (hp 25) hit
    have t1 := move_eq p (hp 77) (hp 12) (Eq.symm t0)
    exact branch33 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · exact branch46 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p (hp 106) (hp 39) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 158)) (reverse_move p (hp 39)) (Eq.trans (Eq.symm hit) t0)
    have t2 := move_eq p (hp 158) (hp 12) (Eq.trans t1 t0)
    have t3 := move_eq p (hp 12) (hp 3) (Eq.trans (Eq.trans (Eq.symm t0) hit) t2)
    exact branch1 p q v hp sep (Eq.symm t3)
  · have t0 := move_eq p (hp 77) (hp 39) (Eq.symm hit)
    exact branch35 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · exact branch46 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 0)) hit
    exact branch16 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 106) (hp 77) hit
    exact branch44 p q v hp hq sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq p (hp 106) (hp 25) hit
    have t1 := move_eq p (hp 77) (hp 39) (Eq.symm t0)
    exact branch35 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · exact branch50 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p (hp 106) (hp 77) hit
    exact branch44 p q v hp hq sep G e₀ e₁ e₂ no t0
  · exact branch50 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch52 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq q (hq 154) (hq 25) (Eq.trans h0 hit)
    exact branch50 p q v hp hq sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq q (hq 154) (hq 7) (Eq.trans h0 hit)
    exact branch52 p q v hp hq sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq q (hq 154) (hq 7) (Eq.trans h0 hit)
    exact branch52 p q v hp hq sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 0)) hit
    have t1 := move_eq q (hq 25) (hq 0) t0
    exact branch13 p q v hp hq sep G e₀ e₁ e₂ no t1
  · have t0 := move_eq q (hq 25) (hq 7) hit
    have t1 := move_eq p.symm (reverse_move p (hp 24)) (reverse_move p (hp 0)) t0
    exact branch5 p q v hp hq sep (Eq.symm t1)
  · have t0 := move_eq p.symm (reverse_move p (hp 24)) (reverse_move p (hp 0)) hit
    exact branch5 p q v hp hq sep (Eq.symm t0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch66 (h0 : v 111 = v 7) : False := by
  have t0 := move_eq q (hq 111) (hq 7) h0
  have t1 := move_eq q (hq 153) (hq 1) t0
  have t2 := move_eq p (hp 105) (hp 6) t1
  have t3 := move_eq p (hp 38) (hp 20) t2
  have t4 := move_eq p (hp 69) (hp 62) t3
  exact short8 p q G sep e₀ e₁ e₂ no ![0,1,0,1,0,1,0,1] (by decide)
    (v 6) (v 6) (v 22) (v 22) (v 62) (v 62) (v 20) (v 20)
    (rfl) (hp 22) (rfl) (Eq.trans (hp 62) (Eq.symm t4)) (rfl) (hp 20) (rfl) (hp 6)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch67 (h0 : v 42 = v 7) : False := by
  have t0 := move_eq p (hp 42) (hp 7) h0
  exact short8 p q G sep e₀ e₁ e₂ no ![0,1,0,2,0,1,2,1] (by decide)
    (v 0) (v 0) (v 3) (v 3) (v 13) (v 13) (v 7) (v 1)
    (rfl) (hp 3) (rfl) (hq 13) (rfl) (Eq.trans (hp 7) (Eq.symm t0)) (hq 7) (hp 0)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch68 (h0 : v 42 = v 25) : False := by
  have t0 := move_eq p (hp 42) (hp 25) h0
  have t1 := move_eq p (hp 77) (hp 13) (Eq.symm t0)
  have t2 := move_eq q (hq 131) (hq 41) t1
  have t3 := move_eq q (hq 70) (hq 59) (Eq.symm t2)
  exact short8 p q G sep e₀ e₁ e₂ no ![1,2,1,0,2,0,1,2] (by decide)
    (v 1) (v 5) (v 19) (v 59) (v 59) (v 22) (v 22) (v 6)
    (hp 1) (hq 19) (hp 19) (rfl) (Eq.trans (hq 59) (Eq.symm t3)) (rfl) (hp 22) (hq 1)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch69 (h0 : v 60 = v 7) : False := by
  have t0 := move_eq p.symm (reverse_move p (hp 41)) (reverse_move p (hp 24)) h0
  have t1 := move_eq p.symm (reverse_move p (hp 13)) (reverse_move p (hp 75)) t0
  have t2 := move_eq q (hq 75) (hq 13) (Eq.symm t1)
  have t3 := move_eq q (hq 34) (hq 3) t2
  have t4 := move_eq p.symm (reverse_move p (hp 37)) (reverse_move p (hp 33)) (Eq.symm t3)
  have t5 := move_eq q (hq 37) (hq 33) t4
  rcases collision16 (fun h => no (.inr (.inr (.inl h))))
    (v 0) (v 0) (v 3) (v 3) (v 12) (v 12) (v 39) (v 96) (v 96) (v 199) (v 199) (v 91) (v 33) (v 10) (v 10) (v 2)
    (e₀ (v 0))
    ((hp 3) ▸ e₁ (v 3))
    (e₀ (v 3))
    ((hp 12) ▸ e₁ (v 12))
    (e₀ (v 12))
    ((hp 39) ▸ e₁ (v 39))
    ((hq 39) ▸ e₂ (v 39))
    (e₀ (v 96))
    ((hq 96) ▸ e₂ (v 96))
    (e₀ (v 199))
    ((hp 142) ▸ e₁ (v 199))
    ((Eq.trans (hq 33) (Eq.symm t5)) ▸ e₂ (v 33))
    ((hp 33) ▸ e₁ (v 33))
    (e₀ (v 10))
    ((hp 10) ▸ e₁ (v 10))
    ((hq 0) ▸ e₂ (v 0)) with hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit
  · exact branch1 p q v hp sep hit
  · exact branch2 p q v hp sep G e₀ e₁ e₂ no hit
  · exact branch3 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p (hp 96) (hp 0) (Eq.symm hit)
    have t1 := move_eq p (hp 33) (hp 1) t0
    have t2 := move_eq q.symm (reverse_move q (hq 34)) (reverse_move q (hq 19)) t1
    have t3 := move_eq p.symm (reverse_move p (hp 41)) (reverse_move p (hp 24)) h0
    have t4 := move_eq p.symm (reverse_move p (hp 13)) (reverse_move p (hp 75)) t3
    have t5 := move_eq q (hq 75) (hq 13) (Eq.symm t4)
    have t6 := move_eq p (hp 19) (hp 3) (Eq.trans (Eq.symm t2) t5)
    exact branch32 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t6)
  · have t0 := move_eq p (hp 142) (hp 0) (Eq.symm hit)
    have t1 := move_eq p (hp 91) (hp 1) t0
    have t2 := move_eq q.symm (reverse_move q (hq 92)) (reverse_move q (hq 19)) t1
    have t3 := move_eq p (hp 60) (hp 7) h0
    have t4 := move_eq q.symm (reverse_move q (hq 37)) (reverse_move q (hq 7)) t0
    have t5 := move_eq p (hp 37) (hp 7) t4
    have t6 := move_eq p.symm (reverse_move p (hp 41)) (reverse_move p (hp 24)) h0
    have t7 := move_eq p.symm (reverse_move p (hp 13)) (reverse_move p (hp 75)) t6
    have t8 := move_eq q (hq 75) (hq 13) (Eq.symm t7)
    have t9 := move_eq q (hq 34) (hq 3) t8
    have t10 := move_eq p (hp 92) (hp 10) (Eq.trans (Eq.trans (Eq.trans t2 t3) (Eq.symm t5)) (Eq.symm t9))
    have t11 := move_eq q.symm (reverse_move q (hq 118)) (reverse_move q (hq 0)) t10
    have t12 := move_eq q.symm (reverse_move q (hq 104)) (reverse_move q (hq 25)) t4
    have t13 := move_eq p (hp 104) (hp 25) t12
    have t14 := move_eq p (hp 155) (hp 77) t13
    exact branch30 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t11) t14)
  · have t0 := move_eq q (hq 33) (hq 0) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 146)) (reverse_move p (hp 10)) t0
    have t2 := move_eq p (hp 33) (hp 0) (Eq.symm hit)
    have t3 := move_eq p (hp 146) (hp 1) (Eq.trans t1 t2)
    have t4 := move_eq q.symm (reverse_move q (hq 19)) (reverse_move q (hq 0)) (Eq.trans (Eq.symm t3) t0)
    exact branch29 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t4)
  · have t0 := move_eq q (hq 10) (hq 0) (Eq.symm hit)
    have t1 := move_eq p (hp 10) (hp 0) (Eq.symm hit)
    have t2 := move_eq q.symm (reverse_move q (hq 10)) (reverse_move q (hq 7)) (Eq.trans t0 t1)
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · exact branch1 p q v hp sep hit
  · exact branch2 p q v hp sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p (hp 96) (hp 0) (Eq.symm hit)
    have t1 := move_eq p (hp 33) (hp 1) t0
    have t2 := move_eq q.symm (reverse_move q (hq 34)) (reverse_move q (hq 19)) t1
    have t3 := move_eq p.symm (reverse_move p (hp 41)) (reverse_move p (hp 24)) h0
    have t4 := move_eq p.symm (reverse_move p (hp 13)) (reverse_move p (hp 75)) t3
    have t5 := move_eq q (hq 75) (hq 13) (Eq.symm t4)
    have t6 := move_eq p (hp 19) (hp 3) (Eq.trans (Eq.symm t2) t5)
    exact branch32 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t6)
  · have t0 := move_eq p (hp 142) (hp 0) (Eq.symm hit)
    have t1 := move_eq p (hp 91) (hp 1) t0
    have t2 := move_eq q.symm (reverse_move q (hq 92)) (reverse_move q (hq 19)) t1
    have t3 := move_eq p (hp 60) (hp 7) h0
    have t4 := move_eq q.symm (reverse_move q (hq 37)) (reverse_move q (hq 7)) t0
    have t5 := move_eq p (hp 37) (hp 7) t4
    have t6 := move_eq p.symm (reverse_move p (hp 41)) (reverse_move p (hp 24)) h0
    have t7 := move_eq p.symm (reverse_move p (hp 13)) (reverse_move p (hp 75)) t6
    have t8 := move_eq q (hq 75) (hq 13) (Eq.symm t7)
    have t9 := move_eq q (hq 34) (hq 3) t8
    have t10 := move_eq p (hp 92) (hp 10) (Eq.trans (Eq.trans (Eq.trans t2 t3) (Eq.symm t5)) (Eq.symm t9))
    have t11 := move_eq q.symm (reverse_move q (hq 118)) (reverse_move q (hq 0)) t10
    have t12 := move_eq q.symm (reverse_move q (hq 104)) (reverse_move q (hq 25)) t4
    have t13 := move_eq p (hp 104) (hp 25) t12
    have t14 := move_eq p (hp 155) (hp 77) t13
    exact branch30 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t11) t14)
  · have t0 := move_eq p (hp 91) (hp 0) (Eq.symm hit)
    have t1 := move_eq p (hp 31) (hp 1) t0
    have t2 := move_eq p (hp 9) (hp 5) t1
    exact branch64 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq q (hq 10) (hq 0) (Eq.symm hit)
    have t1 := move_eq p (hp 10) (hp 0) (Eq.symm hit)
    have t2 := move_eq q.symm (reverse_move q (hq 10)) (reverse_move q (hq 7)) (Eq.trans t0 t1)
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · exact branch8 p q v hq sep hit
  · have t0 := move_eq p (hp 12) (hp 3) (Eq.symm hit)
    exact branch1 p q v hp sep (Eq.symm t0)
  · have t0 := move_eq p (hp 39) (hp 3) (Eq.symm hit)
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 13)) (Eq.symm hit)
    have t1 := move_eq p (hp 39) (hp 13) t0
    have t2 := move_eq p (hp 41) (hp 12) (Eq.symm t1)
    have t3 := move_eq p (hp 60) (hp 3) t2
    exact branch29 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t3)
  · have t0 := move_eq p (hp 142) (hp 3) (Eq.symm hit)
    have t1 := move_eq p (hp 91) (hp 0) t0
    have t2 := move_eq p (hp 31) (hp 1) t1
    have t3 := move_eq p (hp 9) (hp 5) t2
    exact branch64 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t3)
  · have t0 := move_eq p (hp 33) (hp 3) (Eq.symm hit)
    have t1 := move_eq q (hq 10) (hq 0) t0
    have t2 := move_eq p (hp 10) (hp 0) t0
    have t3 := move_eq q.symm (reverse_move q (hq 10)) (reverse_move q (hq 7)) (Eq.trans t1 t2)
    exact branch12 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t3)
  · have t0 := move_eq p (hp 10) (hp 3) (Eq.symm hit)
    exact branch8 p q v hq sep (Eq.symm t0)
  · have t0 := move_eq p (hp 12) (hp 3) (Eq.symm hit)
    exact branch1 p q v hp sep (Eq.symm t0)
  · have t0 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 13)) (Eq.symm hit)
    have t1 := move_eq p (hp 39) (hp 13) t0
    have t2 := move_eq p (hp 41) (hp 12) (Eq.symm t1)
    have t3 := move_eq p (hp 60) (hp 3) t2
    exact branch29 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t3)
  · have t0 := move_eq p (hp 142) (hp 3) (Eq.symm hit)
    have t1 := move_eq p (hp 91) (hp 0) t0
    have t2 := move_eq p (hp 31) (hp 1) t1
    have t3 := move_eq p (hp 9) (hp 5) t2
    exact branch64 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t3)
  · have t0 := move_eq q.symm (reverse_move q (hq 37)) (reverse_move q (hq 13)) (Eq.symm hit)
    have t1 := move_eq p (hp 37) (hp 13) t0
    have t2 := move_eq p (hp 41) (hp 11) (Eq.symm t1)
    have t3 := move_eq q (hq 60) (hq 7) h0
    have t4 := move_eq p.symm (reverse_move p (hp 101)) (reverse_move p (hp 0)) t3
    have t5 := move_eq q (hq 101) (hq 0) t4
    exact branch13 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.trans (Eq.symm h0) t2) t5)
  · have t0 := move_eq p (hp 10) (hp 3) (Eq.symm hit)
    exact branch8 p q v hq sep (Eq.symm t0)
  · exact branch10 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p (hp 39) (hp 12) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 12)) (Eq.trans (Eq.symm hit) t0)
    have t2 := move_eq p (hp 106) (hp 3) (Eq.trans t1 t0)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 40)) (Eq.symm hit)
    have t1 := move_eq p (hp 40) (hp 39) (Eq.symm t0)
    have t2 := move_eq p (hp 75) (hp 12) t1
    have t3 := move_eq p (hp 24) (hp 3) t2
    exact branch4 p q v hp hq sep (Eq.symm t3)
  · have t0 := move_eq q.symm (reverse_move q (hq 96)) (reverse_move q (hq 40)) (Eq.symm hit)
    have t1 := move_eq p (hp 96) (hp 40) t0
    have t2 := move_eq p.symm (reverse_move p (hp 41)) (reverse_move p (hp 24)) h0
    have t3 := move_eq p.symm (reverse_move p (hp 13)) (reverse_move p (hp 75)) t2
    have t4 := move_eq p (hp 33) (hp 13) (Eq.trans t1 (Eq.symm t3))
    have t5 := move_eq p (hp 41) (hp 10) (Eq.symm t4)
    exact branch13 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm h0) t5)
  · have t0 := move_eq p (hp 33) (hp 12) (Eq.symm hit)
    have t1 := move_eq p (hp 10) (hp 3) t0
    exact branch8 p q v hq sep (Eq.symm t1)
  · have t0 := move_eq p (hp 12) (hp 10) hit
    exact branch10 p q v hp hq sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 40)) (Eq.symm hit)
    have t1 := move_eq p (hp 40) (hp 39) (Eq.symm t0)
    have t2 := move_eq p (hp 75) (hp 12) t1
    have t3 := move_eq p (hp 24) (hp 3) t2
    exact branch4 p q v hp hq sep (Eq.symm t3)
  · have t0 := move_eq q.symm (reverse_move q (hq 96)) (reverse_move q (hq 40)) (Eq.symm hit)
    have t1 := move_eq p (hp 96) (hp 40) t0
    have t2 := move_eq p.symm (reverse_move p (hp 41)) (reverse_move p (hp 24)) h0
    have t3 := move_eq p.symm (reverse_move p (hp 13)) (reverse_move p (hp 75)) t2
    have t4 := move_eq p (hp 33) (hp 13) (Eq.trans t1 (Eq.symm t3))
    have t5 := move_eq p (hp 41) (hp 10) (Eq.symm t4)
    exact branch13 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm h0) t5)
  · have t0 := move_eq p (hp 91) (hp 12) (Eq.symm hit)
    have t1 := move_eq p (hp 31) (hp 3) t0
    exact branch59 p q v hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p (hp 12) (hp 10) hit
    exact branch10 p q v hp hq sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 10)) hit
    have t1 := move_eq q.symm (reverse_move q (hq 107)) (reverse_move q (hq 34)) t0
    have t2 := move_eq q.symm (reverse_move q (hq 40)) (reverse_move q (hq 0)) hit
    have t3 := move_eq p (hp 40) (hp 0) t2
    have t4 := move_eq q (hq 75) (hq 1) t3
    have t5 := move_eq q (hq 12) (hq 2) hit
    have t6 := move_eq p (hp 38) (hp 9) t5
    have t7 := move_eq p (hp 69) (hp 29) t6
    have t8 := move_eq p (hp 86) (hp 22) (Eq.symm t7)
    have t9 := move_eq p.symm (reverse_move p (hp 41)) (reverse_move p (hp 24)) h0
    have t10 := move_eq p (hp 75) (hp 1) t3
    have t11 := move_eq p (hp 60) (hp 7) h0
    have t12 := move_eq q (hq 23) (hq 19) (Eq.symm t11)
    have t13 := move_eq p (hp 12) (hp 2) hit
    have t14 := move_eq p (hp 8) (hp 3) (Eq.symm t13)
    have t15 := move_eq q.symm (reverse_move q (hq 72)) (reverse_move q (hq 4)) t14
    have t16 := move_eq q (hq 41) (hq 4) (Eq.trans (Eq.trans (Eq.trans t9 t10) (Eq.symm t12)) t15)
    have t17 := move_eq q (hq 70) (hq 0) t16
    have t18 := move_eq p (hp 86) (hp 2) (Eq.trans (Eq.symm t7) t17)
    have t19 := move_eq p (hp 107) (hp 3) (Eq.trans (Eq.trans (Eq.trans (Eq.trans t1 t4) (Eq.symm t8)) t18) (Eq.symm t13))
    have t20 := move_eq p (hp 107) (hp 6) (Eq.trans t1 t4)
    have t21 := move_eq p (hp 48) (hp 20) t20
    have t22 := move_eq p.symm (reverse_move p (hp 13)) (reverse_move p (hp 15)) (Eq.trans (Eq.trans (Eq.trans t9 t10) (Eq.symm t12)) t15)
    have t23 := move_eq p.symm (reverse_move p (hp 20)) (reverse_move p (hp 42)) (Eq.trans (Eq.symm t21) (Eq.symm t22))
    exact branch26 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.trans (Eq.symm t19) t20) t23)
  · have t0 := move_eq p (hp 96) (hp 39) (Eq.symm hit)
    have t1 := move_eq p (hp 33) (hp 12) t0
    have t2 := move_eq p (hp 10) (hp 3) t1
    exact branch8 p q v hq sep (Eq.symm t2)
  · have t0 := move_eq p (hp 142) (hp 39) (Eq.symm hit)
    have t1 := move_eq p (hp 91) (hp 12) t0
    have t2 := move_eq p (hp 31) (hp 3) t1
    exact branch59 p q v hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq p (hp 39) (hp 33) hit
    have t1 := move_eq p (hp 12) (hp 10) t0
    exact branch10 p q v hp hq sep G e₀ e₁ e₂ no t1
  · have t0 := move_eq p (hp 60) (hp 7) h0
    have t1 := move_eq q (hq 23) (hq 19) (Eq.symm t0)
    have t2 := move_eq p.symm (reverse_move p (hp 132)) (reverse_move p (hp 1)) t1
    have t3 := move_eq p.symm (reverse_move p (hp 98)) (reverse_move p (hp 0)) t2
    have t4 := move_eq q.symm (reverse_move q (hq 107)) (reverse_move q (hq 34)) hit
    have t5 := move_eq p (hp 107) (hp 34) t4
    have t6 := move_eq p (hp 39) (hp 10) hit
    have t7 := move_eq q.symm (reverse_move q (hq 40)) (reverse_move q (hq 0)) t6
    have t8 := move_eq p (hp 40) (hp 0) t7
    have t9 := move_eq q (hq 75) (hq 1) t8
    have t10 := move_eq p (hp 107) (hp 6) (Eq.trans t4 t9)
    have t11 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 33)) hit
    have t12 := move_eq q.symm (reverse_move q (hq 154)) (reverse_move q (hq 97)) t11
    have t13 := move_eq p (hp 159) (hp 97) t12
    have t14 := move_eq q (hq 39) (hq 10) hit
    have t15 := move_eq p (hp 96) (hp 32) t14
    have t16 := move_eq q.symm (reverse_move q (hq 135)) (reverse_move q (hq 97)) (Eq.symm t15)
    have t17 := move_eq p.symm (reverse_move p (hp 41)) (reverse_move p (hp 24)) h0
    have t18 := move_eq q (hq 41) (hq 24) t17
    have t19 := move_eq q (hq 74) (hq 70) (Eq.symm t18)
    have t20 := move_eq p (hp 97) (hp 22) (Eq.trans (Eq.symm t16) t19)
    have t21 := move_eq p (hp 111) (hp 6) (Eq.trans t13 t20)
    exact branch26 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.trans (Eq.trans (Eq.symm t3) (Eq.symm t5)) t10) (Eq.symm t21))
  · have t0 := move_eq q (hq 60) (hq 7) h0
    have t1 := move_eq p.symm (reverse_move p (hp 101)) (reverse_move p (hp 0)) t0
    have t2 := move_eq q (hq 101) (hq 0) t1
    have t3 := move_eq q (hq 35) (hq 2) t2
    have t4 := move_eq p (hp 142) (hp 96) (Eq.symm hit)
    have t5 := move_eq p (hp 91) (hp 33) t4
    have t6 := move_eq p (hp 31) (hp 10) t5
    have t7 := move_eq q.symm (reverse_move q (hq 35)) (reverse_move q (hq 0)) (Eq.trans t3 t6)
    exact branch8 p q v hq sep (Eq.trans (Eq.symm t7) t2)
  · have t0 := move_eq p.symm (reverse_move p (hp 41)) (reverse_move p (hp 24)) h0
    have t1 := move_eq p.symm (reverse_move p (hp 13)) (reverse_move p (hp 75)) t0
    have t2 := move_eq q (hq 75) (hq 13) (Eq.symm t1)
    have t3 := move_eq p (hp 96) (hp 91) hit
    have t4 := move_eq p (hp 33) (hp 31) t3
    have t5 := move_eq q.symm (reverse_move q (hq 34)) (reverse_move q (hq 2)) t4
    exact branch10 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t2) t5)
  · have t0 := move_eq p.symm (reverse_move p (hp 147)) (reverse_move p (hp 33)) hit
    have t1 := move_eq p (hp 96) (hp 10) hit
    have t2 := move_eq p (hp 147) (hp 2) (Eq.trans t0 t1)
    have t3 := move_eq p (hp 10) (hp 8) (Eq.trans (Eq.symm hit) t2)
    have t4 := move_eq q.symm (reverse_move q (hq 72)) (reverse_move q (hq 0)) (Eq.symm t3)
    have t5 := move_eq p (hp 60) (hp 7) h0
    have t6 := move_eq q (hq 23) (hq 19) (Eq.symm t5)
    have t7 := move_eq p (hp 26) (hp 2) (Eq.symm t3)
    have t8 := move_eq q.symm (reverse_move q (hq 17)) (reverse_move q (hq 28)) t7
    have t9 := move_eq p (hp 5) (hp 0) (Eq.trans (Eq.symm t6) t4)
    have t10 := move_eq p (hp 28) (hp 1) (Eq.trans (Eq.symm t8) t9)
    have t11 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 34)) hit
    have t12 := move_eq q.symm (reverse_move q (hq 34)) (reverse_move q (hq 28)) (Eq.trans (Eq.symm hit) t2)
    have t13 := move_eq p (hp 39) (hp 28) (Eq.trans t11 t12)
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.trans (Eq.trans (Eq.trans (Eq.symm t4) t6) (Eq.symm t10)) (Eq.symm t13))
  · have t0 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 0)) hit
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq q (hq 60) (hq 7) h0
    have t1 := move_eq p.symm (reverse_move p (hp 101)) (reverse_move p (hp 0)) t0
    have t2 := move_eq q (hq 101) (hq 0) t1
    have t3 := move_eq q (hq 35) (hq 2) t2
    have t4 := move_eq p (hp 142) (hp 96) (Eq.symm hit)
    have t5 := move_eq p (hp 91) (hp 33) t4
    have t6 := move_eq p (hp 31) (hp 10) t5
    have t7 := move_eq q.symm (reverse_move q (hq 35)) (reverse_move q (hq 0)) (Eq.trans t3 t6)
    exact branch8 p q v hq sep (Eq.trans (Eq.symm t7) t2)
  · have t0 := move_eq p (hp 96) (hp 33) hit
    have t1 := move_eq p.symm (reverse_move p (hp 147)) (reverse_move p (hp 33)) (Eq.trans hit t0)
    have t2 := move_eq p (hp 147) (hp 10) (Eq.trans t1 t0)
    have t3 := move_eq q.symm (reverse_move q (hq 34)) (reverse_move q (hq 0)) (Eq.trans (Eq.trans (Eq.symm t0) (Eq.symm hit)) t2)
    have t4 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 34)) (Eq.trans hit t0)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t3) (Eq.symm t4))
  · have t0 := move_eq p.symm (reverse_move p (hp 147)) (reverse_move p (hp 33)) hit
    have t1 := move_eq p (hp 96) (hp 10) hit
    have t2 := move_eq p (hp 147) (hp 2) (Eq.trans t0 t1)
    have t3 := move_eq p (hp 10) (hp 8) (Eq.trans (Eq.symm hit) t2)
    have t4 := move_eq q.symm (reverse_move q (hq 72)) (reverse_move q (hq 0)) (Eq.symm t3)
    have t5 := move_eq p (hp 60) (hp 7) h0
    have t6 := move_eq q (hq 23) (hq 19) (Eq.symm t5)
    have t7 := move_eq p (hp 26) (hp 2) (Eq.symm t3)
    have t8 := move_eq q.symm (reverse_move q (hq 17)) (reverse_move q (hq 28)) t7
    have t9 := move_eq p (hp 5) (hp 0) (Eq.trans (Eq.symm t6) t4)
    have t10 := move_eq p (hp 28) (hp 1) (Eq.trans (Eq.symm t8) t9)
    have t11 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 34)) hit
    have t12 := move_eq q.symm (reverse_move q (hq 34)) (reverse_move q (hq 28)) (Eq.trans (Eq.symm hit) t2)
    have t13 := move_eq p (hp 39) (hp 28) (Eq.trans t11 t12)
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.trans (Eq.trans (Eq.trans (Eq.symm t4) t6) (Eq.symm t10)) (Eq.symm t13))
  · have t0 := move_eq p (hp 142) (hp 91) hit
    have t1 := move_eq q.symm (reverse_move q (hq 96)) (reverse_move q (hq 92)) (Eq.trans hit t0)
    have t2 := move_eq p (hp 91) (hp 31) t0
    have t3 := move_eq q.symm (reverse_move q (hq 96)) (reverse_move q (hq 2)) (Eq.trans (Eq.trans hit t0) t2)
    have t4 := move_eq q.symm (reverse_move q (hq 47)) (reverse_move q (hq 0)) (Eq.trans (Eq.symm t1) t3)
    have t5 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 47)) t1
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t4) (Eq.symm t5))
  · have t0 := move_eq q.symm (reverse_move q (hq 96)) (reverse_move q (hq 34)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 41)) (reverse_move p (hp 24)) h0
    have t2 := move_eq p.symm (reverse_move p (hp 13)) (reverse_move p (hp 75)) t1
    have t3 := move_eq q (hq 75) (hq 13) (Eq.symm t2)
    have t4 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 13)) (Eq.trans t0 t3)
    have t5 := move_eq p (hp 39) (hp 13) t4
    have t6 := move_eq p (hp 41) (hp 12) (Eq.symm t5)
    have t7 := move_eq p (hp 60) (hp 3) t6
    exact branch29 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t7)
  · have t0 := move_eq p.symm (reverse_move p (hp 41)) (reverse_move p (hp 24)) h0
    have t1 := move_eq p.symm (reverse_move p (hp 13)) (reverse_move p (hp 75)) t0
    have t2 := move_eq q (hq 75) (hq 13) (Eq.symm t1)
    have t3 := move_eq p.symm (reverse_move p (hp 99)) (reverse_move p (hp 12)) t2
    have t4 := move_eq q (hq 99) (hq 12) t3
    have t5 := move_eq p (hp 60) (hp 7) h0
    have t6 := move_eq q.symm (reverse_move q (hq 73)) (reverse_move q (hq 61)) (Eq.symm t5)
    have t7 := move_eq p.symm (reverse_move p (hp 50)) (reverse_move p (hp 46)) t6
    have t8 := move_eq q (hq 50) (hq 46) t7
    have t9 := move_eq q.symm (reverse_move q (hq 96)) (reverse_move q (hq 0)) hit
    have t10 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 4)) t9
    have t11 := move_eq p (hp 39) (hp 4) t10
    have t12 := move_eq q (hq 85) (hq 12) (Eq.trans t8 (Eq.symm t11))
    have t13 := move_eq p (hp 142) (hp 2) hit
    have t14 := move_eq q.symm (reverse_move q (hq 37)) (reverse_move q (hq 28)) t13
    have t15 := move_eq p (hp 37) (hp 28) t14
    have t16 := move_eq q (hq 34) (hq 3) t2
    have t17 := move_eq p (hp 96) (hp 0) t9
    have t18 := move_eq p (hp 33) (hp 1) t17
    have t19 := move_eq p.symm (reverse_move p (hp 28)) (reverse_move p (hp 1)) (Eq.trans (Eq.trans (Eq.symm t15) (Eq.symm t16)) t18)
    have t20 := move_eq q.symm (reverse_move q (hq 99)) (reverse_move q (hq 7)) (Eq.trans (Eq.trans t4 (Eq.symm t12)) t19)
    exact branch39 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t3) t20)
  · have t0 := move_eq p (hp 142) (hp 33) hit
    have t1 := move_eq p (hp 91) (hp 10) t0
    have t2 := move_eq p (hp 31) (hp 2) t1
    have t3 := move_eq q (hq 31) (hq 2) t1
    have t4 := move_eq p.symm (reverse_move p (hp 141)) (reverse_move p (hp 2)) (Eq.trans t3 t2)
    have t5 := move_eq q.symm (reverse_move q (hq 31)) (reverse_move q (hq 28)) (Eq.trans t3 t2)
    have t6 := move_eq q.symm (reverse_move q (hq 96)) (reverse_move q (hq 97)) hit
    have t7 := move_eq p (hp 97) (hp 96) (Eq.symm t6)
    have t8 := move_eq p (hp 47) (hp 33) t7
    have t9 := move_eq p.symm (reverse_move p (hp 41)) (reverse_move p (hp 24)) h0
    have t10 := move_eq p.symm (reverse_move p (hp 13)) (reverse_move p (hp 75)) t9
    have t11 := move_eq q (hq 75) (hq 13) (Eq.symm t10)
    have t12 := move_eq q (hq 34) (hq 3) t11
    have t13 := move_eq q.symm (reverse_move q (hq 37)) (reverse_move q (hq 34)) t0
    have t14 := move_eq p (hp 37) (hp 3) (Eq.trans t13 t11)
    have t15 := move_eq p (hp 84) (hp 0) (Eq.trans (Eq.trans t8 t12) t14)
    have t16 := move_eq p (hp 141) (hp 1) (Eq.trans (Eq.trans (Eq.trans t4 (Eq.symm t1)) t5) t15)
    have t17 := move_eq p (hp 8) (hp 5) (Eq.trans (Eq.trans (Eq.symm t2) (Eq.symm t3)) t16)
    have t18 := move_eq p (hp 60) (hp 7) h0
    have t19 := move_eq q (hq 23) (hq 19) (Eq.symm t18)
    have t20 := move_eq q (hq 72) (hq 5) t19
    exact branch63 p q v hp hq sep (Eq.trans (Eq.symm t17) t20)
  · have t0 := move_eq q.symm (reverse_move q (hq 96)) (reverse_move q (hq 34)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 41)) (reverse_move p (hp 24)) h0
    have t2 := move_eq p.symm (reverse_move p (hp 13)) (reverse_move p (hp 75)) t1
    have t3 := move_eq q (hq 75) (hq 13) (Eq.symm t2)
    have t4 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 13)) (Eq.trans t0 t3)
    have t5 := move_eq p (hp 39) (hp 13) t4
    have t6 := move_eq p (hp 41) (hp 12) (Eq.symm t5)
    have t7 := move_eq p (hp 60) (hp 3) t6
    exact branch29 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t7)
  · have t0 := move_eq q (hq 60) (hq 7) h0
    have t1 := move_eq p.symm (reverse_move p (hp 101)) (reverse_move p (hp 0)) t0
    have t2 := move_eq q (hq 101) (hq 0) t1
    have t3 := move_eq q.symm (reverse_move q (hq 37)) (reverse_move q (hq 34)) hit
    have t4 := move_eq p (hp 37) (hp 34) t3
    have t5 := move_eq p (hp 98) (hp 11) (Eq.symm t4)
    have t6 := move_eq p (hp 60) (hp 7) h0
    have t7 := move_eq q (hq 23) (hq 19) (Eq.symm t6)
    have t8 := move_eq p.symm (reverse_move p (hp 132)) (reverse_move p (hp 1)) t7
    have t9 := move_eq q.symm (reverse_move q (hq 0)) (reverse_move q (hq 7)) (Eq.trans (Eq.trans (Eq.symm t2) (Eq.symm t5)) t8)
    exact branch4 p q v hp hq sep t9
  · have t0 := move_eq p.symm (reverse_move p (hp 142)) (reverse_move p (hp 10)) hit
    have t1 := move_eq q.symm (reverse_move q (hq 96)) (reverse_move q (hq 34)) t0
    have t2 := move_eq p.symm (reverse_move p (hp 41)) (reverse_move p (hp 24)) h0
    have t3 := move_eq p.symm (reverse_move p (hp 13)) (reverse_move p (hp 75)) t2
    have t4 := move_eq q (hq 75) (hq 13) (Eq.symm t3)
    have t5 := move_eq q (hq 96) (hq 3) (Eq.trans t1 t4)
    have t6 := move_eq q.symm (reverse_move q (hq 37)) (reverse_move q (hq 0)) hit
    have t7 := move_eq p (hp 37) (hp 0) t6
    have t8 := move_eq p (hp 142) (hp 1) (Eq.trans t5 t7)
    have t9 := move_eq q.symm (reverse_move q (hq 19)) (reverse_move q (hq 0)) (Eq.trans (Eq.symm t8) hit)
    exact branch29 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t9)
  · have t0 := move_eq p (hp 33) (hp 10) hit
    have t1 := move_eq p.symm (reverse_move p (hp 96)) (reverse_move p (hp 10)) (Eq.trans hit t0)
    have t2 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 0)) (Eq.trans t1 t0)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq p.symm (reverse_move p (hp 33)) (reverse_move p (hp 10)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 96)) (reverse_move p (hp 10)) (Eq.trans t0 hit)
    have t2 := move_eq q.symm (reverse_move q (hq 39)) (reverse_move q (hq 0)) (Eq.trans t1 hit)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep in
private theorem branch70 (h0 : v 60 = v 25) : False := by
  have t0 := move_eq p.symm (reverse_move p (hp 41)) (reverse_move p (hp 78)) h0
  have t1 := move_eq q (hq 78) (hq 41) (Eq.symm t0)
  have t2 := move_eq q (hq 70) (hq 41) (Eq.symm t1)
  have t3 := move_eq q (hq 78) (hq 22) (Eq.trans (Eq.trans (Eq.symm t0) t1) (Eq.symm t2))
  exact (sep (v 22)).2.1 (Eq.trans (hq 22) (Eq.trans (Eq.trans (Eq.symm t3) t1) (Eq.symm t2)))

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
private theorem branch71 (h0 : v 19 = v 25) : False := by
  have t0 := move_eq q (hq 25) (hq 19) (Eq.symm h0)
  have t1 := move_eq q (hq 7) (hq 5) t0
  exact short4 p q G sep e₀ e₁ e₂ no ![0,2,0,1] (by decide)
    (v 1) (v 1) (v 5) (v 5)
    (rfl) (Eq.trans (hq 5) (Eq.symm t1)) (rfl) (hp 1)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep in
private theorem branch72 (h0 : v 77 = v 7) : False := by
  have t0 := move_eq q (hq 77) (hq 7) h0
  have t1 := move_eq q (hq 134) (hq 1) t0
  have t2 := move_eq q (hq 64) (hq 6) t1
  exact (sep (v 6)).2.2 (Eq.trans (hp 6) (Eq.symm (Eq.trans (hq 6) (Eq.symm t2))))

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
include p q v hp hq sep G e₀ e₁ e₂ no in
theorem chart_forces_cycle : False := by
  rcases collision32 (fun h => no (.inr (.inr (.inr h))))
    (v 0) (v 0) (v 3) (v 3) (v 12) (v 12) (v 39) (v 39) (v 106) (v 106) (v 227) (v 111) (v 111) (v 42) (v 42) (v 13) (v 13) (v 41) (v 41) (v 60) (v 60) (v 19) (v 19) (v 59) (v 142) (v 142) (v 77) (v 77) (v 25) (v 7) (v 7) (v 1)
    (e₀ (v 0))
    ((hp 3) ▸ e₁ (v 3))
    (e₀ (v 3))
    ((hp 12) ▸ e₁ (v 12))
    (e₀ (v 12))
    ((hp 39) ▸ e₁ (v 39))
    (e₀ (v 39))
    ((hp 106) ▸ e₁ (v 106))
    (e₀ (v 106))
    ((hq 154) ▸ e₂ (v 227))
    ((hp 159) ▸ e₁ (v 227))
    (e₀ (v 111))
    ((hp 111) ▸ e₁ (v 111))
    (e₀ (v 42))
    ((hp 42) ▸ e₁ (v 42))
    (e₀ (v 13))
    ((hp 13) ▸ e₁ (v 13))
    (e₀ (v 41))
    ((hp 41) ▸ e₁ (v 41))
    (e₀ (v 60))
    ((hp 60) ▸ e₁ (v 60))
    (e₀ (v 19))
    ((hp 19) ▸ e₁ (v 19))
    ((hq 131) ▸ e₂ (v 142))
    (e₀ (v 142))
    ((hp 77) ▸ e₁ (v 77))
    (e₀ (v 77))
    ((hp 25) ▸ e₁ (v 25))
    ((hq 25) ▸ e₂ (v 25))
    (e₀ (v 7))
    ((hq 7) ▸ e₂ (v 7))
    ((hp 0) ▸ e₁ (v 0)) with hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit|hit
  · exact branch1 p q v hp sep hit
  · exact branch2 p q v hp sep G e₀ e₁ e₂ no hit
  · exact branch3 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch16 p q v hp sep G e₀ e₁ e₂ no hit
  · exact branch17 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch25 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch26 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq q (hq 13) (hq 0) (Eq.symm hit)
    exact branch10 p q v hp hq sep G e₀ e₁ e₂ no t0
  · exact branch27 p q v hp hq sep hit
  · exact branch28 p q v hp hq sep hit
  · exact branch29 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch30 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch31 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq q (hq 25) (hq 0) (Eq.symm hit)
    exact branch13 p q v hp hq sep G e₀ e₁ e₂ no t0
  · exact branch4 p q v hp hq sep hit
  · exact branch1 p q v hp sep hit
  · exact branch2 p q v hp sep G e₀ e₁ e₂ no hit
  · exact branch3 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch16 p q v hp sep G e₀ e₁ e₂ no hit
  · exact branch25 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch26 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq q (hq 13) (hq 0) (Eq.symm hit)
    exact branch10 p q v hp hq sep G e₀ e₁ e₂ no t0
  · exact branch27 p q v hp hq sep hit
  · exact branch28 p q v hp hq sep hit
  · exact branch29 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch32 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch30 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch31 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch4 p q v hp hq sep hit
  · have t0 := move_eq p.symm (reverse_move p (hp 0)) (reverse_move p (hp 3)) (Eq.symm hit)
    exact branch1 p q v hp sep t0
  · have t0 := move_eq p (hp 12) (hp 3) (Eq.symm hit)
    exact branch1 p q v hp sep (Eq.symm t0)
  · have t0 := move_eq p (hp 39) (hp 3) (Eq.symm hit)
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 106) (hp 3) (Eq.symm hit)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 159) (hp 3) (Eq.symm hit)
    exact branch25 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 111) (hp 3) (Eq.symm hit)
    exact branch26 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq q.symm (reverse_move q (hq 112)) (reverse_move q (hq 13)) (Eq.symm hit)
    have t1 := move_eq p (hp 42) (hp 3) (Eq.symm hit)
    have t2 := move_eq q (hq 112) (hq 0) (Eq.trans t0 t1)
    exact branch10 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans hit t2)
  · have t0 := move_eq p (hp 13) (hp 3) (Eq.symm hit)
    exact branch27 p q v hp hq sep (Eq.symm t0)
  · have t0 := move_eq p (hp 41) (hp 3) (Eq.symm hit)
    exact branch28 p q v hp hq sep (Eq.symm t0)
  · have t0 := move_eq p (hp 60) (hp 3) (Eq.symm hit)
    exact branch29 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 19) (hp 3) (Eq.symm hit)
    exact branch32 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · exact branch33 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p (hp 77) (hp 3) (Eq.symm hit)
    exact branch30 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 25) (hp 3) (Eq.symm hit)
    exact branch31 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 7) (hp 3) (Eq.symm hit)
    exact branch6 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 12) (hp 3) (Eq.symm hit)
    exact branch1 p q v hp sep (Eq.symm t0)
  · have t0 := move_eq p (hp 39) (hp 3) (Eq.symm hit)
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 106) (hp 3) (Eq.symm hit)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 111) (hp 3) (Eq.symm hit)
    exact branch26 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq q.symm (reverse_move q (hq 112)) (reverse_move q (hq 13)) (Eq.symm hit)
    have t1 := move_eq p (hp 42) (hp 3) (Eq.symm hit)
    have t2 := move_eq q (hq 112) (hq 0) (Eq.trans t0 t1)
    exact branch10 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans hit t2)
  · have t0 := move_eq p (hp 13) (hp 3) (Eq.symm hit)
    exact branch27 p q v hp hq sep (Eq.symm t0)
  · have t0 := move_eq p (hp 41) (hp 3) (Eq.symm hit)
    exact branch28 p q v hp hq sep (Eq.symm t0)
  · have t0 := move_eq p (hp 60) (hp 3) (Eq.symm hit)
    exact branch29 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 19) (hp 3) (Eq.symm hit)
    exact branch32 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · exact branch34 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch33 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p (hp 77) (hp 3) (Eq.symm hit)
    exact branch30 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 7) (hp 3) (Eq.symm hit)
    exact branch6 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 12)) (reverse_move p (hp 0)) hit
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 39) (hp 12) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 12)) (Eq.trans (Eq.symm hit) t0)
    have t2 := move_eq p (hp 106) (hp 3) (Eq.trans t1 t0)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq p.symm (reverse_move p (hp 158)) (reverse_move p (hp 39)) (Eq.symm hit)
    have t1 := move_eq p (hp 106) (hp 12) (Eq.symm hit)
    have t2 := move_eq p (hp 158) (hp 3) (Eq.trans t0 t1)
    exact branch16 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq p (hp 159) (hp 12) (Eq.symm hit)
    have t1 := move_eq p (hp 111) (hp 3) t0
    exact branch26 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p (hp 111) (hp 12) (Eq.symm hit)
    have t1 := move_eq q.symm (reverse_move q (hq 112)) (reverse_move q (hq 13)) t0
    have t2 := move_eq p (hp 42) (hp 3) t0
    have t3 := move_eq q (hq 112) (hq 0) (Eq.trans t1 t2)
    exact branch10 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t0) t3)
  · have t0 := move_eq p (hp 42) (hp 12) (Eq.symm hit)
    have t1 := move_eq p (hp 13) (hp 3) t0
    exact branch27 p q v hp hq sep (Eq.symm t1)
  · have t0 := move_eq p (hp 13) (hp 12) (Eq.symm hit)
    have t1 := move_eq p (hp 41) (hp 3) t0
    exact branch28 p q v hp hq sep (Eq.symm t1)
  · have t0 := move_eq p (hp 41) (hp 12) (Eq.symm hit)
    have t1 := move_eq p (hp 60) (hp 3) t0
    exact branch29 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p (hp 60) (hp 12) (Eq.symm hit)
    have t1 := move_eq p (hp 19) (hp 3) t0
    exact branch32 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p (hp 19) (hp 12) (Eq.symm hit)
    exact branch34 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · exact branch35 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p (hp 77) (hp 12) (Eq.symm hit)
    exact branch33 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 25) (hp 12) (Eq.symm hit)
    have t1 := move_eq p (hp 77) (hp 3) t0
    exact branch30 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · exact branch39 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p (hp 39) (hp 12) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 12)) (Eq.trans (Eq.symm hit) t0)
    have t2 := move_eq p (hp 106) (hp 3) (Eq.trans t1 t0)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq p.symm (reverse_move p (hp 158)) (reverse_move p (hp 39)) (Eq.symm hit)
    have t1 := move_eq p (hp 106) (hp 12) (Eq.symm hit)
    have t2 := move_eq p (hp 158) (hp 3) (Eq.trans t0 t1)
    exact branch16 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq p (hp 111) (hp 12) (Eq.symm hit)
    have t1 := move_eq q.symm (reverse_move q (hq 112)) (reverse_move q (hq 13)) t0
    have t2 := move_eq p (hp 42) (hp 3) t0
    have t3 := move_eq q (hq 112) (hq 0) (Eq.trans t1 t2)
    exact branch10 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans (Eq.symm t0) t3)
  · have t0 := move_eq p (hp 42) (hp 12) (Eq.symm hit)
    have t1 := move_eq p (hp 13) (hp 3) t0
    exact branch27 p q v hp hq sep (Eq.symm t1)
  · have t0 := move_eq p (hp 13) (hp 12) (Eq.symm hit)
    have t1 := move_eq p (hp 41) (hp 3) t0
    exact branch28 p q v hp hq sep (Eq.symm t1)
  · have t0 := move_eq p (hp 41) (hp 12) (Eq.symm hit)
    have t1 := move_eq p (hp 60) (hp 3) t0
    exact branch29 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p (hp 60) (hp 12) (Eq.symm hit)
    have t1 := move_eq p (hp 19) (hp 3) t0
    exact branch32 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p (hp 19) (hp 12) (Eq.symm hit)
    exact branch34 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · exact branch40 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch35 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p (hp 77) (hp 12) (Eq.symm hit)
    exact branch33 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · exact branch39 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 0)) hit
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 106) (hp 39) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 158)) (reverse_move p (hp 39)) (Eq.trans (Eq.symm hit) t0)
    have t2 := move_eq p (hp 158) (hp 12) (Eq.trans t1 t0)
    have t3 := move_eq p (hp 12) (hp 3) (Eq.trans (Eq.trans (Eq.symm t0) hit) t2)
    exact branch1 p q v hp sep (Eq.symm t3)
  · have t0 := move_eq p (hp 159) (hp 39) (Eq.symm hit)
    have t1 := move_eq q (hq 154) (hq 39) (Eq.symm hit)
    have t2 := move_eq p (hp 106) (hp 96) t1
    have t3 := move_eq p (hp 159) (hp 33) (Eq.trans (Eq.symm hit) t2)
    have t4 := move_eq p (hp 12) (hp 10) (Eq.trans (Eq.symm t0) t3)
    exact branch10 p q v hp hq sep G e₀ e₁ e₂ no t4
  · have t0 := move_eq p (hp 111) (hp 39) (Eq.symm hit)
    have t1 := move_eq p (hp 42) (hp 12) t0
    have t2 := move_eq p (hp 13) (hp 3) t1
    exact branch27 p q v hp hq sep (Eq.symm t2)
  · have t0 := move_eq p (hp 42) (hp 39) (Eq.symm hit)
    have t1 := move_eq p (hp 13) (hp 12) t0
    have t2 := move_eq p (hp 41) (hp 3) t1
    exact branch28 p q v hp hq sep (Eq.symm t2)
  · have t0 := move_eq p (hp 39) (hp 13) hit
    have t1 := move_eq p (hp 41) (hp 12) (Eq.symm t0)
    have t2 := move_eq p (hp 60) (hp 3) t1
    exact branch29 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq p (hp 41) (hp 39) (Eq.symm hit)
    have t1 := move_eq p (hp 60) (hp 12) t0
    have t2 := move_eq p (hp 19) (hp 3) t1
    exact branch32 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq p (hp 60) (hp 39) (Eq.symm hit)
    have t1 := move_eq p (hp 19) (hp 12) t0
    exact branch34 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p (hp 39) (hp 19) hit
    exact branch40 p q v hp hq sep G e₀ e₁ e₂ no t0
  · exact branch44 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p (hp 77) (hp 39) (Eq.symm hit)
    exact branch35 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 39) (hp 25) hit
    have t1 := move_eq p (hp 77) (hp 12) (Eq.symm t0)
    exact branch33 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · exact branch46 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p (hp 106) (hp 39) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 158)) (reverse_move p (hp 39)) (Eq.trans (Eq.symm hit) t0)
    have t2 := move_eq p (hp 158) (hp 12) (Eq.trans t1 t0)
    have t3 := move_eq p (hp 12) (hp 3) (Eq.trans (Eq.trans (Eq.symm t0) hit) t2)
    exact branch1 p q v hp sep (Eq.symm t3)
  · have t0 := move_eq p (hp 111) (hp 39) (Eq.symm hit)
    have t1 := move_eq p (hp 42) (hp 12) t0
    have t2 := move_eq p (hp 13) (hp 3) t1
    exact branch27 p q v hp hq sep (Eq.symm t2)
  · have t0 := move_eq p (hp 42) (hp 39) (Eq.symm hit)
    have t1 := move_eq p (hp 13) (hp 12) t0
    have t2 := move_eq p (hp 41) (hp 3) t1
    exact branch28 p q v hp hq sep (Eq.symm t2)
  · have t0 := move_eq p (hp 39) (hp 13) hit
    have t1 := move_eq p (hp 41) (hp 12) (Eq.symm t0)
    have t2 := move_eq p (hp 60) (hp 3) t1
    exact branch29 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq p (hp 41) (hp 39) (Eq.symm hit)
    have t1 := move_eq p (hp 60) (hp 12) t0
    have t2 := move_eq p (hp 19) (hp 3) t1
    exact branch32 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq p (hp 60) (hp 39) (Eq.symm hit)
    have t1 := move_eq p (hp 19) (hp 12) t0
    exact branch34 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p (hp 39) (hp 19) hit
    exact branch40 p q v hp hq sep G e₀ e₁ e₂ no t0
  · exact branch47 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch44 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p (hp 77) (hp 39) (Eq.symm hit)
    exact branch35 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · exact branch46 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 106)) (reverse_move p (hp 0)) hit
    exact branch16 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 159) (hp 106) (Eq.symm hit)
    have t1 := move_eq p (hp 111) (hp 39) t0
    have t2 := move_eq p (hp 42) (hp 12) t1
    have t3 := move_eq p (hp 13) (hp 3) t2
    exact branch27 p q v hp hq sep (Eq.symm t3)
  · have t0 := move_eq p (hp 111) (hp 106) (Eq.symm hit)
    have t1 := move_eq p (hp 42) (hp 39) t0
    have t2 := move_eq p (hp 13) (hp 12) t1
    have t3 := move_eq p (hp 41) (hp 3) t2
    exact branch28 p q v hp hq sep (Eq.symm t3)
  · have t0 := move_eq p (hp 106) (hp 42) hit
    have t1 := move_eq p (hp 39) (hp 13) t0
    have t2 := move_eq p (hp 41) (hp 12) (Eq.symm t1)
    have t3 := move_eq p (hp 60) (hp 3) t2
    exact branch29 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t3)
  · have t0 := move_eq p (hp 106) (hp 13) hit
    have t1 := move_eq p (hp 41) (hp 39) (Eq.symm t0)
    have t2 := move_eq p (hp 60) (hp 12) t1
    have t3 := move_eq p (hp 19) (hp 3) t2
    exact branch32 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t3)
  · have t0 := move_eq p (hp 106) (hp 41) hit
    have t1 := move_eq p (hp 60) (hp 39) (Eq.symm t0)
    have t2 := move_eq p (hp 19) (hp 12) t1
    exact branch34 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq p (hp 106) (hp 60) hit
    have t1 := move_eq p (hp 39) (hp 19) t0
    exact branch40 p q v hp hq sep G e₀ e₁ e₂ no t1
  · have t0 := move_eq p (hp 106) (hp 19) hit
    exact branch47 p q v hp hq sep G e₀ e₁ e₂ no t0
  · exact branch49 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p (hp 106) (hp 77) hit
    exact branch44 p q v hp hq sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq p (hp 106) (hp 25) hit
    have t1 := move_eq p (hp 77) (hp 39) (Eq.symm t0)
    exact branch35 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · exact branch50 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p (hp 111) (hp 106) (Eq.symm hit)
    have t1 := move_eq p (hp 42) (hp 39) t0
    have t2 := move_eq p (hp 13) (hp 12) t1
    have t3 := move_eq p (hp 41) (hp 3) t2
    exact branch28 p q v hp hq sep (Eq.symm t3)
  · have t0 := move_eq p (hp 106) (hp 42) hit
    have t1 := move_eq p (hp 39) (hp 13) t0
    have t2 := move_eq p (hp 41) (hp 12) (Eq.symm t1)
    have t3 := move_eq p (hp 60) (hp 3) t2
    exact branch29 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t3)
  · have t0 := move_eq p (hp 106) (hp 13) hit
    have t1 := move_eq p (hp 41) (hp 39) (Eq.symm t0)
    have t2 := move_eq p (hp 60) (hp 12) t1
    have t3 := move_eq p (hp 19) (hp 3) t2
    exact branch32 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t3)
  · have t0 := move_eq p (hp 106) (hp 41) hit
    have t1 := move_eq p (hp 60) (hp 39) (Eq.symm t0)
    have t2 := move_eq p (hp 19) (hp 12) t1
    exact branch34 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq p (hp 106) (hp 60) hit
    have t1 := move_eq p (hp 39) (hp 19) t0
    exact branch40 p q v hp hq sep G e₀ e₁ e₂ no t1
  · have t0 := move_eq p (hp 106) (hp 19) hit
    exact branch47 p q v hp hq sep G e₀ e₁ e₂ no t0
  · exact branch51 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch49 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p (hp 106) (hp 77) hit
    exact branch44 p q v hp hq sep G e₀ e₁ e₂ no t0
  · exact branch50 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch52 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p (hp 159) (hp 111) hit
    have t1 := move_eq p (hp 111) (hp 42) t0
    have t2 := move_eq q (hq 154) (hq 13) (Eq.trans (Eq.trans hit t0) t1)
    have t3 := move_eq p (hp 106) (hp 3) t2
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t3)
  · exact branch55 p q v hp sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq q (hq 154) (hq 13) hit
    have t1 := move_eq p (hp 106) (hp 3) t0
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · exact branch56 p q v hp sep G e₀ e₁ e₂ no hit
  · exact branch57 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch58 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq q (hq 154) (hq 131) hit
    exact branch51 p q v hp hq sep G e₀ e₁ e₂ no t0
  · exact branch65 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq q (hq 154) (hq 25) hit
    exact branch50 p q v hp hq sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq q (hq 154) (hq 7) hit
    exact branch52 p q v hp hq sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq p (hp 111) (hp 42) hit
    have t1 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 42)) (Eq.trans hit t0)
    exact branch55 p q v hp sep G e₀ e₁ e₂ no t1
  · have t0 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 42)) hit
    exact branch55 p q v hp sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 13)) hit
    have t1 := move_eq q (hq 154) (hq 13) t0
    have t2 := move_eq p (hp 106) (hp 3) t1
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 41)) hit
    exact branch56 p q v hp sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 60)) hit
    exact branch57 p q v hp hq sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 19)) hit
    exact branch58 p q v hp hq sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 159)) (Eq.symm hit)
    exact branch65 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 25)) hit
    have t1 := move_eq q (hq 154) (hq 25) t0
    exact branch50 p q v hp hq sep G e₀ e₁ e₂ no t1
  · exact branch66 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 0)) hit
    exact branch17 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p (hp 111) (hp 42) hit
    have t1 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 42)) (Eq.trans hit t0)
    exact branch55 p q v hp sep G e₀ e₁ e₂ no t1
  · have t0 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 42)) hit
    exact branch55 p q v hp sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 13)) hit
    have t1 := move_eq q (hq 154) (hq 13) t0
    have t2 := move_eq p (hp 106) (hp 3) t1
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 41)) hit
    exact branch56 p q v hp sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 60)) hit
    exact branch57 p q v hp hq sep G e₀ e₁ e₂ no t0
  · have t0 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 159)) (Eq.symm hit)
    exact branch65 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 25)) hit
    have t1 := move_eq q (hq 154) (hq 25) t0
    exact branch50 p q v hp hq sep G e₀ e₁ e₂ no t1
  · have t0 := move_eq p (hp 111) (hp 25) hit
    have t1 := move_eq p (hp 77) (hp 42) (Eq.symm t0)
    have t2 := move_eq q (hq 131) (hq 13) t1
    exact branch34 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · exact branch66 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 111)) (reverse_move p (hp 42)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 42)) (Eq.trans t0 hit)
    exact branch55 p q v hp sep G e₀ e₁ e₂ no t1
  · have t0 := move_eq p.symm (reverse_move p (hp 111)) (reverse_move p (hp 13)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 42)) t0
    exact branch55 p q v hp sep G e₀ e₁ e₂ no t1
  · have t0 := move_eq p.symm (reverse_move p (hp 41)) (reverse_move p (hp 111)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 13)) (Eq.symm t0)
    have t2 := move_eq p (hp 60) (hp 42) (Eq.symm hit)
    exact branch58 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans t1 (Eq.symm t2))
  · have t0 := move_eq p.symm (reverse_move p (hp 111)) (reverse_move p (hp 60)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 41)) t0
    exact branch56 p q v hp sep G e₀ e₁ e₂ no t1
  · have t0 := move_eq p.symm (reverse_move p (hp 19)) (reverse_move p (hp 111)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 60)) (Eq.symm t0)
    exact branch57 p q v hp hq sep G e₀ e₁ e₂ no t1
  · have t0 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 111)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 25)) (Eq.symm t0)
    have t2 := move_eq q (hq 154) (hq 25) t1
    exact branch50 p q v hp hq sep G e₀ e₁ e₂ no t2
  · have t0 := move_eq p (hp 77) (hp 42) (Eq.symm hit)
    have t1 := move_eq q (hq 131) (hq 13) t0
    exact branch34 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · exact branch67 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 111)) (reverse_move p (hp 0)) hit
    exact branch25 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 111)) (reverse_move p (hp 42)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 42)) (Eq.trans t0 hit)
    exact branch55 p q v hp sep G e₀ e₁ e₂ no t1
  · have t0 := move_eq p.symm (reverse_move p (hp 111)) (reverse_move p (hp 13)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 42)) t0
    exact branch55 p q v hp sep G e₀ e₁ e₂ no t1
  · have t0 := move_eq p.symm (reverse_move p (hp 41)) (reverse_move p (hp 111)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 13)) (Eq.symm t0)
    have t2 := move_eq p (hp 60) (hp 42) (Eq.symm hit)
    exact branch58 p q v hp hq sep G e₀ e₁ e₂ no (Eq.trans t1 (Eq.symm t2))
  · have t0 := move_eq p.symm (reverse_move p (hp 111)) (reverse_move p (hp 60)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 41)) t0
    exact branch56 p q v hp sep G e₀ e₁ e₂ no t1
  · have t0 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 111)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 25)) (Eq.symm t0)
    have t2 := move_eq q (hq 154) (hq 25) t1
    exact branch50 p q v hp hq sep G e₀ e₁ e₂ no t2
  · have t0 := move_eq p (hp 77) (hp 42) (Eq.symm hit)
    have t1 := move_eq q (hq 131) (hq 13) t0
    exact branch34 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · exact branch68 p q v hp hq sep G e₀ e₁ e₂ no hit
  · exact branch67 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 13)) (reverse_move p (hp 42)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 111)) (reverse_move p (hp 42)) (Eq.symm t0)
    have t2 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 42)) (Eq.trans t1 (Eq.symm t0))
    exact branch55 p q v hp sep G e₀ e₁ e₂ no t2
  · have t0 := move_eq p.symm (reverse_move p (hp 41)) (reverse_move p (hp 42)) (Eq.symm hit)
    have t1 := move_eq p (hp 60) (hp 13) (Eq.symm hit)
    have t2 := move_eq p.symm (reverse_move p (hp 111)) (reverse_move p (hp 60)) (Eq.trans (Eq.symm t0) (Eq.symm t1))
    have t3 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 42)) (Eq.trans t2 (Eq.symm hit))
    exact branch55 p q v hp sep G e₀ e₁ e₂ no t3
  · have t0 := move_eq q (hq 19) (hq 13) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 1)) (reverse_move p (hp 12)) t0
    have t2 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 0)) (Eq.symm t1)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq p.symm (reverse_move p (hp 19)) (reverse_move p (hp 42)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 111)) (reverse_move p (hp 60)) (Eq.symm t0)
    have t2 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 41)) t1
    exact branch56 p q v hp sep G e₀ e₁ e₂ no t2
  · have t0 := move_eq q (hq 131) (hq 13) (Eq.symm hit)
    exact branch34 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 42)) (Eq.symm hit)
    exact branch68 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq q (hq 13) (hq 7) hit
    have t1 := move_eq p.symm (reverse_move p (hp 12)) (reverse_move p (hp 0)) t0
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p.symm (reverse_move p (hp 42)) (reverse_move p (hp 0)) hit
    exact branch26 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 13)) (reverse_move p (hp 42)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 111)) (reverse_move p (hp 42)) (Eq.symm t0)
    have t2 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 42)) (Eq.trans t1 (Eq.symm t0))
    exact branch55 p q v hp sep G e₀ e₁ e₂ no t2
  · have t0 := move_eq p.symm (reverse_move p (hp 41)) (reverse_move p (hp 42)) (Eq.symm hit)
    have t1 := move_eq p (hp 60) (hp 13) (Eq.symm hit)
    have t2 := move_eq p.symm (reverse_move p (hp 111)) (reverse_move p (hp 60)) (Eq.trans (Eq.symm t0) (Eq.symm t1))
    have t3 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 42)) (Eq.trans t2 (Eq.symm hit))
    exact branch55 p q v hp sep G e₀ e₁ e₂ no t3
  · have t0 := move_eq q (hq 19) (hq 13) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 1)) (reverse_move p (hp 12)) t0
    have t2 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 0)) (Eq.symm t1)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq q (hq 131) (hq 13) (Eq.symm hit)
    exact branch34 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 42)) (Eq.symm hit)
    exact branch68 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq q (hq 25) (hq 13) (Eq.symm hit)
    have t1 := move_eq p (hp 7) (hp 3) t0
    exact branch6 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq q (hq 13) (hq 7) hit
    have t1 := move_eq p.symm (reverse_move p (hp 12)) (reverse_move p (hp 0)) t0
    exact branch2 p q v hp sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p (hp 60) (hp 41) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 13)) (reverse_move p (hp 60)) (Eq.trans hit (Eq.symm t0))
    have t2 := move_eq q (hq 60) (hq 13) (Eq.symm t1)
    have t3 := move_eq p.symm (reverse_move p (hp 101)) (reverse_move p (hp 12)) t2
    have t4 := move_eq q (hq 60) (hq 19) (Eq.symm t0)
    have t5 := move_eq p.symm (reverse_move p (hp 101)) (reverse_move p (hp 1)) t4
    have t6 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 0)) (Eq.trans (Eq.symm t3) t5)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t6)
  · have t0 := move_eq p (hp 41) (hp 19) hit
    have t1 := move_eq p.symm (reverse_move p (hp 13)) (reverse_move p (hp 60)) hit
    have t2 := move_eq p.symm (reverse_move p (hp 19)) (reverse_move p (hp 42)) (Eq.trans (Eq.symm t0) (Eq.symm t1))
    have t3 := move_eq p.symm (reverse_move p (hp 111)) (reverse_move p (hp 60)) (Eq.symm t2)
    have t4 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 42)) (Eq.trans t3 (Eq.symm t1))
    exact branch55 p q v hp sep G e₀ e₁ e₂ no t4
  · have t0 := move_eq p.symm (reverse_move p (hp 19)) (reverse_move p (hp 13)) (Eq.symm hit)
    have t1 := move_eq q (hq 19) (hq 13) t0
    have t2 := move_eq p.symm (reverse_move p (hp 1)) (reverse_move p (hp 12)) t1
    have t3 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 0)) (Eq.symm t2)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t3)
  · have t0 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 13)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 42)) t0
    exact branch68 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 13)) (Eq.symm hit)
    have t1 := move_eq q (hq 25) (hq 13) t0
    have t2 := move_eq p (hp 7) (hp 3) t1
    exact branch6 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq p.symm (reverse_move p (hp 13)) (reverse_move p (hp 24)) hit
    have t1 := move_eq q (hq 24) (hq 13) (Eq.symm t0)
    have t2 := move_eq p.symm (reverse_move p (hp 130)) (reverse_move p (hp 12)) t1
    have t3 := move_eq q (hq 41) (hq 7) hit
    have t4 := move_eq q (hq 70) (hq 1) t3
    have t5 := move_eq p.symm (reverse_move p (hp 69)) (reverse_move p (hp 22)) t4
    have t6 := move_eq q.symm (reverse_move q (hq 136)) (reverse_move q (hq 1)) (Eq.trans t5 t4)
    have t7 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 0)) (Eq.trans (Eq.symm t2) t6)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t7)
  · have t0 := move_eq p.symm (reverse_move p (hp 13)) (reverse_move p (hp 0)) hit
    have t1 := move_eq q (hq 13) (hq 0) t0
    exact branch10 p q v hp hq sep G e₀ e₁ e₂ no t1
  · have t0 := move_eq p (hp 60) (hp 41) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 13)) (reverse_move p (hp 60)) (Eq.trans hit (Eq.symm t0))
    have t2 := move_eq q (hq 60) (hq 13) (Eq.symm t1)
    have t3 := move_eq p.symm (reverse_move p (hp 101)) (reverse_move p (hp 12)) t2
    have t4 := move_eq q (hq 60) (hq 19) (Eq.symm t0)
    have t5 := move_eq p.symm (reverse_move p (hp 101)) (reverse_move p (hp 1)) t4
    have t6 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 0)) (Eq.trans (Eq.symm t3) t5)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t6)
  · have t0 := move_eq p (hp 41) (hp 19) hit
    have t1 := move_eq p.symm (reverse_move p (hp 13)) (reverse_move p (hp 60)) hit
    have t2 := move_eq p.symm (reverse_move p (hp 19)) (reverse_move p (hp 42)) (Eq.trans (Eq.symm t0) (Eq.symm t1))
    have t3 := move_eq p.symm (reverse_move p (hp 111)) (reverse_move p (hp 60)) (Eq.symm t2)
    have t4 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 42)) (Eq.trans t3 (Eq.symm t1))
    exact branch55 p q v hp sep G e₀ e₁ e₂ no t4
  · have t0 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 13)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 42)) t0
    exact branch68 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 13)) (Eq.symm hit)
    have t1 := move_eq q (hq 25) (hq 13) t0
    have t2 := move_eq p (hp 7) (hp 3) t1
    exact branch6 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq p.symm (reverse_move p (hp 13)) (reverse_move p (hp 78)) hit
    have t1 := move_eq q (hq 78) (hq 13) (Eq.symm t0)
    have t2 := move_eq p (hp 25) (hp 3) (Eq.trans (Eq.symm hit) t1)
    exact branch31 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq p.symm (reverse_move p (hp 13)) (reverse_move p (hp 24)) hit
    have t1 := move_eq q (hq 24) (hq 13) (Eq.symm t0)
    have t2 := move_eq p.symm (reverse_move p (hp 130)) (reverse_move p (hp 12)) t1
    have t3 := move_eq q (hq 41) (hq 7) hit
    have t4 := move_eq q (hq 70) (hq 1) t3
    have t5 := move_eq p.symm (reverse_move p (hp 69)) (reverse_move p (hp 22)) t4
    have t6 := move_eq q.symm (reverse_move q (hq 136)) (reverse_move q (hq 1)) (Eq.trans t5 t4)
    have t7 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 0)) (Eq.trans (Eq.symm t2) t6)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t7)
  · have t0 := move_eq p.symm (reverse_move p (hp 41)) (reverse_move p (hp 60)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 13)) (reverse_move p (hp 60)) (Eq.trans t0 hit)
    have t2 := move_eq q (hq 60) (hq 13) (Eq.symm t1)
    have t3 := move_eq p.symm (reverse_move p (hp 101)) (reverse_move p (hp 12)) t2
    have t4 := move_eq q (hq 60) (hq 19) hit
    have t5 := move_eq p.symm (reverse_move p (hp 101)) (reverse_move p (hp 1)) t4
    have t6 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 0)) (Eq.trans (Eq.symm t3) t5)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t6)
  · have t0 := move_eq p.symm (reverse_move p (hp 41)) (reverse_move p (hp 19)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 13)) (reverse_move p (hp 60)) t0
    have t2 := move_eq p.symm (reverse_move p (hp 19)) (reverse_move p (hp 42)) (Eq.trans (Eq.symm hit) (Eq.symm t1))
    have t3 := move_eq p.symm (reverse_move p (hp 111)) (reverse_move p (hp 60)) (Eq.symm t2)
    have t4 := move_eq p.symm (reverse_move p (hp 159)) (reverse_move p (hp 42)) (Eq.trans t3 (Eq.symm t1))
    exact branch55 p q v hp sep G e₀ e₁ e₂ no t4
  · have t0 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 41)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 13)) t0
    have t2 := move_eq q (hq 25) (hq 13) t1
    have t3 := move_eq p (hp 7) (hp 3) t2
    exact branch6 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t3)
  · have t0 := move_eq p (hp 77) (hp 60) (Eq.symm hit)
    have t1 := move_eq q (hq 131) (hq 19) t0
    have t2 := move_eq p.symm (reverse_move p (hp 19)) (reverse_move p (hp 1)) t1
    have t3 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 0)) (Eq.trans t0 t2)
    exact branch31 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t3)
  · exact branch69 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 41)) (reverse_move p (hp 0)) hit
    exact branch27 p q v hp hq sep (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 41)) (reverse_move p (hp 60)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 13)) (reverse_move p (hp 60)) (Eq.trans t0 hit)
    have t2 := move_eq q (hq 60) (hq 13) (Eq.symm t1)
    have t3 := move_eq p.symm (reverse_move p (hp 101)) (reverse_move p (hp 12)) t2
    have t4 := move_eq q (hq 60) (hq 19) hit
    have t5 := move_eq p.symm (reverse_move p (hp 101)) (reverse_move p (hp 1)) t4
    have t6 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 0)) (Eq.trans (Eq.symm t3) t5)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t6)
  · have t0 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 41)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 13)) t0
    have t2 := move_eq q (hq 25) (hq 13) t1
    have t3 := move_eq p (hp 7) (hp 3) t2
    exact branch6 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t3)
  · have t0 := move_eq p (hp 77) (hp 60) (Eq.symm hit)
    have t1 := move_eq q (hq 131) (hq 19) t0
    have t2 := move_eq p.symm (reverse_move p (hp 19)) (reverse_move p (hp 1)) t1
    have t3 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 0)) (Eq.trans t0 t2)
    exact branch31 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t3)
  · exact branch70 p q v hp hq sep hit
  · exact branch69 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq p.symm (reverse_move p (hp 19)) (reverse_move p (hp 60)) (Eq.symm hit)
    have t1 := move_eq q (hq 60) (hq 19) (Eq.symm t0)
    have t2 := move_eq q (hq 59) (hq 19) (Eq.symm hit)
    have t3 := move_eq p.symm (reverse_move p (hp 41)) (reverse_move p (hp 60)) (Eq.symm t0)
    have t4 := move_eq p.symm (reverse_move p (hp 13)) (reverse_move p (hp 60)) (Eq.trans t3 (Eq.symm t0))
    have t5 := move_eq q (hq 59) (hq 13) (Eq.trans (Eq.trans (Eq.symm hit) t0) (Eq.symm t4))
    have t6 := move_eq p.symm (reverse_move p (hp 101)) (reverse_move p (hp 12)) (Eq.trans (Eq.trans t1 (Eq.symm t2)) t5)
    have t7 := move_eq p.symm (reverse_move p (hp 101)) (reverse_move p (hp 1)) t1
    have t8 := move_eq p.symm (reverse_move p (hp 39)) (reverse_move p (hp 0)) (Eq.trans (Eq.symm t6) t7)
    exact branch3 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t8)
  · have t0 := move_eq q (hq 131) (hq 19) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 19)) (reverse_move p (hp 1)) t0
    have t2 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 0)) (Eq.trans (Eq.symm hit) t1)
    exact branch31 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 60)) (Eq.symm hit)
    exact branch70 p q v hp hq sep (Eq.symm t0)
  · have t0 := move_eq q (hq 19) (hq 7) hit
    have t1 := move_eq p.symm (reverse_move p (hp 1)) (reverse_move p (hp 0)) t0
    have t2 := move_eq p (hp 5) (hp 1) t0
    have t3 := move_eq p.symm (reverse_move p (hp 5)) (reverse_move p (hp 3)) (Eq.trans (Eq.trans t2 t0) t1)
    exact branch1 p q v hp sep (Eq.trans (Eq.trans (Eq.symm t1) (Eq.symm t0)) t3)
  · have t0 := move_eq p.symm (reverse_move p (hp 60)) (reverse_move p (hp 0)) hit
    exact branch28 p q v hp hq sep (Eq.symm t0)
  · have t0 := move_eq q (hq 131) (hq 19) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 19)) (reverse_move p (hp 1)) t0
    have t2 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 0)) (Eq.trans (Eq.symm hit) t1)
    exact branch31 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t2)
  · have t0 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 60)) (Eq.symm hit)
    exact branch70 p q v hp hq sep (Eq.symm t0)
  · exact branch71 p q v hp hq sep G e₀ e₁ e₂ no hit
  · have t0 := move_eq q (hq 19) (hq 7) hit
    have t1 := move_eq p.symm (reverse_move p (hp 1)) (reverse_move p (hp 0)) t0
    have t2 := move_eq p (hp 5) (hp 1) t0
    have t3 := move_eq p.symm (reverse_move p (hp 5)) (reverse_move p (hp 3)) (Eq.trans (Eq.trans t2 t0) t1)
    exact branch1 p q v hp sep (Eq.trans (Eq.trans (Eq.symm t1) (Eq.symm t0)) t3)
  · have t0 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 19)) (Eq.symm hit)
    have t1 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 60)) t0
    exact branch70 p q v hp hq sep (Eq.symm t1)
  · have t0 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 19)) (Eq.symm hit)
    exact branch71 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq q.symm (reverse_move q (hq 131)) (reverse_move q (hq 25)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 78)) t0
    have t2 := move_eq q (hq 78) (hq 77) (Eq.symm t1)
    have t3 := move_eq p.symm (reverse_move p (hp 19)) (reverse_move p (hp 24)) hit
    have t4 := move_eq p.symm (reverse_move p (hp 75)) (reverse_move p (hp 60)) (Eq.symm t3)
    have t5 := move_eq p.symm (reverse_move p (hp 40)) (reverse_move p (hp 41)) t4
    have t6 := move_eq q.symm (reverse_move q (hq 77)) (reverse_move q (hq 109)) (Eq.trans (Eq.symm t2) (Eq.symm t5))
    have t7 := move_eq p.symm (reverse_move p (hp 163)) (reverse_move p (hp 25)) (Eq.symm t6)
    have t8 := move_eq q (hq 157) (hq 25) t7
    exact branch66 p q v hp hq sep G e₀ e₁ e₂ no t8
  · have t0 := move_eq p.symm (reverse_move p (hp 19)) (reverse_move p (hp 0)) hit
    exact branch29 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 25)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 78)) t0
    have t2 := move_eq p.symm (reverse_move p (hp 134)) (reverse_move p (hp 78)) (Eq.symm t1)
    have t3 := move_eq p.symm (reverse_move p (hp 109)) (reverse_move p (hp 78)) (Eq.trans t2 (Eq.symm t1))
    have t4 := move_eq p.symm (reverse_move p (hp 163)) (reverse_move p (hp 78)) (Eq.trans t3 (Eq.symm t1))
    have t5 := move_eq q (hq 157) (hq 25) (Eq.trans t4 (Eq.symm t1))
    exact branch66 p q v hp hq sep G e₀ e₁ e₂ no t5
  · have t0 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 78)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 134)) (reverse_move p (hp 25)) (Eq.symm t0)
    have t2 := move_eq p.symm (reverse_move p (hp 109)) (reverse_move p (hp 78)) t1
    have t3 := move_eq p.symm (reverse_move p (hp 163)) (reverse_move p (hp 25)) (Eq.trans t2 (Eq.symm t0))
    have t4 := move_eq q (hq 157) (hq 25) t3
    exact branch66 p q v hp hq sep G e₀ e₁ e₂ no t4
  · have t0 := move_eq q (hq 131) (hq 7) hit
    have t1 := move_eq p.symm (reverse_move p (hp 19)) (reverse_move p (hp 0)) t0
    exact branch29 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 25)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 78)) t0
    have t2 := move_eq p.symm (reverse_move p (hp 134)) (reverse_move p (hp 78)) (Eq.symm t1)
    have t3 := move_eq p.symm (reverse_move p (hp 109)) (reverse_move p (hp 78)) (Eq.trans t2 (Eq.symm t1))
    have t4 := move_eq p.symm (reverse_move p (hp 163)) (reverse_move p (hp 78)) (Eq.trans t3 (Eq.symm t1))
    have t5 := move_eq q (hq 157) (hq 25) (Eq.trans t4 (Eq.symm t1))
    exact branch66 p q v hp hq sep G e₀ e₁ e₂ no t5
  · have t0 := move_eq q (hq 131) (hq 7) hit
    have t1 := move_eq p.symm (reverse_move p (hp 19)) (reverse_move p (hp 0)) t0
    exact branch29 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t1)
  · have t0 := move_eq p.symm (reverse_move p (hp 77)) (reverse_move p (hp 0)) hit
    exact branch31 p q v hp hq sep G e₀ e₁ e₂ no (Eq.symm t0)
  · have t0 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 78)) hit
    have t1 := move_eq p.symm (reverse_move p (hp 134)) (reverse_move p (hp 78)) (Eq.symm t0)
    have t2 := move_eq p.symm (reverse_move p (hp 109)) (reverse_move p (hp 78)) (Eq.trans t1 (Eq.symm t0))
    have t3 := move_eq p.symm (reverse_move p (hp 163)) (reverse_move p (hp 78)) (Eq.trans t2 (Eq.symm t0))
    have t4 := move_eq q (hq 157) (hq 25) (Eq.trans t3 (Eq.symm t0))
    exact branch66 p q v hp hq sep G e₀ e₁ e₂ no t4
  · exact branch72 p q v hp hq sep hit
  · exact branch72 p q v hp hq sep hit
  · have t0 := move_eq p.symm (reverse_move p (hp 25)) (reverse_move p (hp 0)) hit
    have t1 := move_eq q (hq 25) (hq 0) t0
    exact branch13 p q v hp hq sep G e₀ e₁ e₂ no t1
  · have t0 := move_eq q (hq 25) (hq 7) hit
    have t1 := move_eq p.symm (reverse_move p (hp 24)) (reverse_move p (hp 0)) t0
    exact branch5 p q v hp hq sep (Eq.symm t1)
  · have t0 := move_eq p.symm (reverse_move p (hp 24)) (reverse_move p (hp 0)) hit
    exact branch5 p q v hp hq sep (Eq.symm t0)

end Erdos64.IndexThreeCore

/-
# Short cycles with an abelian normal subgroup of index three

When the three labels are distinct modulo the kernel, put t = q p. The
three conjugates of t under powers of p belong to the abelian kernel and
are cyclically permuted by p. Their integer powers give the chart to which
the finite collision proof applies. Repeated labels modulo the kernel are
handled by the conjugate-square theorem from PR 23343.
Formalization by @bmander.
-/
namespace Erdos64.IndexThree
open SimpleGraph
variable {X : Type*}

set_option maxHeartbeats 2800000 in
set_option maxRecDepth 5000 in
theorem chart_on_action (p q : Equiv.Perm X) (v : ℤ → ℤ → ℤ → ℤ → X)
    (hp : ∀ a b c z, p (v a b c z)=v c a b (z+1))
    (hq : ∀ a b c z, q (v a b c z)=v (b+1) c a (z-1))
    (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x) (G : SimpleGraph (Bool × X))
    (e₀ : ∀ x, G.Adj (false,x) (true,x)) (e₁ : ∀ x, G.Adj (false,x) (true,p x))
    (e₂ : ∀ x, G.Adj (false,x) (true,q x)) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G := by
  classical
  let W : List (ℤ × ℤ × ℤ × ℤ) := [
    (0,0,0,0),(0,0,0,1),(1,0,0,-1),(0,0,0,-1),(0,-1,0,1),(0,0,0,2),
    (1,0,0,0),(0,-1,0,2),(0,1,0,0),(1,0,1,-2),(0,0,1,-2),(1,0,0,-2),
    (0,0,0,-2),(0,-1,0,0),(0,0,-1,2),(-1,0,0,0),(0,-1,-1,2),(0,0,0,3),
    (1,0,0,1),(0,-1,0,3),(0,1,0,1),(1,0,1,-1),(0,0,1,-1),(0,0,-1,3),
    (-1,0,0,1),(0,-1,-1,3),(0,0,1,1),(2,0,0,-1),(0,-1,1,1),(1,1,0,-1),
    (1,1,1,-3),(0,1,1,-3),(1,1,0,-3),(0,1,0,-3),(1,-1,0,-1),(0,1,0,-1),
    (1,0,1,-3),(0,0,1,-3),(1,0,0,-3),(0,0,0,-3),(0,-1,0,-1),(0,0,-1,1),
    (-1,0,0,-1),(0,-1,-1,1),(-1,0,0,3),(1,-1,0,1),(-1,-1,0,3),(1,0,-1,-1),
    (0,0,-1,-1),(0,-2,0,1),(-1,0,-1,3),(-1,-1,0,1),(-1,-1,-1,3),(0,0,0,4),
    (1,0,0,2),(0,-1,0,4),(0,1,0,2),(1,0,1,0),(0,0,1,0),(0,0,-1,4),
    (-1,0,0,2),(0,-1,-1,4),(0,0,1,2),(2,0,0,0),(0,-1,1,2),(1,1,0,0),
    (1,1,1,-2),(0,1,1,-2),(1,1,0,-2),(0,1,0,-2),(1,-1,0,0),(-1,0,0,4),
    (1,-1,0,2),(-1,-1,0,4),(1,0,-1,0),(0,0,-1,0),(0,-2,0,2),(-1,0,-1,4),
    (-1,-1,0,2),(-1,-1,-1,4),(0,2,0,0),(1,0,2,-2),(0,0,2,-2),(1,0,-1,2),
    (-1,1,0,0),(1,-1,-1,2),(0,1,1,0),(2,0,1,-2),(2,1,1,-4),(1,1,1,-4),
    (2,1,0,-4),(1,1,0,-4),(1,-1,1,-2),(2,0,1,-4),(1,0,1,-4),(2,0,0,-4),
    (1,0,0,-4),(0,-1,1,-2),(0,1,-1,0),(-1,0,1,-2),(2,0,0,-2),(0,-1,1,0),
    (0,1,1,-4),(0,1,0,-4),(1,-1,0,-2),(0,0,1,-4),(0,0,0,-4),(0,-1,0,-2),
    (-1,0,0,-2),(0,-1,-1,0),(1,0,-1,-2),(0,0,-1,-2),(0,-2,0,0),(-1,0,-1,2),
    (-1,-1,0,0),(-1,-1,-1,2),(0,-2,0,4),(0,1,-1,2),(-1,0,1,0),(0,-2,-1,4),
    (0,0,-2,2),(-2,0,0,0),(0,-1,-2,2),(-1,-2,0,4),(-1,0,-1,0),(0,-2,-1,2),
    (-1,-2,-1,4),(0,0,0,5),(1,0,0,3),(0,-1,0,5),(0,1,0,3),(1,0,1,1),
    (0,0,-1,5),(0,-1,-1,5),(0,0,1,3),(2,0,0,1),(0,-1,1,3),(1,1,0,1),
    (1,1,1,-1),(0,1,1,-1),(-1,0,0,5),(1,-1,0,3),(-1,-1,0,5),(1,0,-1,1),
    (0,-2,0,3),(-1,0,-1,5),(-1,-1,-1,5),(0,2,0,1),(1,0,2,-1),(0,0,2,-1),
    (1,0,-1,3),(-1,1,0,1),(1,-1,-1,3),(0,1,1,1),(2,0,1,-1),(2,1,1,-3),
    (2,1,0,-3),(1,-1,1,-1),(2,0,1,-3),(2,0,0,-3),(0,-1,1,-1),(0,1,-1,1),
    (-1,0,1,-1),(0,-2,0,5),(0,1,-1,3),(-1,0,1,1),(0,-2,-1,5),(0,0,-2,3),
    (-2,0,0,1),(0,-1,-2,3),(-1,-2,0,5),(-1,0,-1,1),(0,-2,-1,3),(-1,-2,-1,5),
    (0,0,2,1),(3,0,0,-1),(0,-1,2,1),(2,1,0,-1),(1,2,1,-3),(0,2,1,-3),
    (1,2,0,-3),(0,2,0,-3),(2,-1,0,-1),(-1,1,0,3),(1,-1,1,1),(2,0,-1,-1),
    (0,-2,1,1),(-1,1,-1,3),(-1,-1,1,1),(1,2,0,-1),(1,1,2,-3),(0,1,2,-3),
    (2,1,2,-5),(1,1,2,-5),(2,1,1,-5),(1,1,1,-5),(2,0,2,-5),(1,0,2,-5),
    (2,0,1,-5),(1,0,1,-5),(1,1,-1,-1),(-1,1,1,-3),(0,1,2,-5),(0,1,1,-5),
    (0,0,2,-5),(0,0,1,-5),(-1,1,0,-3),(1,-1,-1,-1),(1,1,-1,-3),(0,1,-1,-3),
    (1,-2,0,-1),(0,2,0,-1),(1,0,2,-3),(0,0,2,-3),(-1,1,0,-1),(1,-1,-1,1),
    (2,1,0,-5),(1,1,0,-5),(1,-1,1,-3),(2,0,0,-5),(1,0,0,-5),(0,-1,1,-3),
    (0,1,-1,-1),(-1,0,1,-3),(0,1,0,-5),(1,-1,0,-3),(0,0,0,-5),(0,-1,0,-3),
    (-1,0,0,-3),(0,-1,-1,-1),(1,0,-1,-3),(0,0,-1,-3),(0,-2,0,-1),(-1,-1,0,-1),
    (-1,-1,-1,1),(0,0,-2,1),(-2,0,0,-1),(0,-1,-2,1),(-1,-2,0,3),(-1,0,-1,-1),
    (0,-2,-1,1),(-1,-2,-1,3),(0,0,-2,5),(-2,0,0,3),(0,-1,-2,5),(-1,0,1,3),
    (2,-1,0,1),(-1,-1,1,3),(1,-2,0,1),(-1,0,-2,5),(-2,-1,0,3),(-1,-1,-2,5),
    (1,0,-2,-1),(0,0,-2,-1),(0,-3,0,1),(-2,0,-1,3),(-1,-2,0,1),(-2,-1,-1,3),
    (0,-2,-2,5),(-1,0,-2,3),(-2,-1,0,1),(-1,-1,-2,3),(-1,-2,-2,5)]
  let pos (i : ℕ) := W.getD i (0,0,0,0)
  let eval (r : ℤ × ℤ × ℤ × ℤ) := v r.1 r.2.1 r.2.2.1 r.2.2.2
  let f (i : ℕ) := eval (pos i)
  let tab0 : List (ℕ × ℕ) := [(0,1),(1,5),(2,8),(3,0),(4,14),(5,17),(6,20),(7,23),(8,26),(9,29),(10,2),(11,35),(12,3),(13,41),(14,44),(15,4),(16,50),(17,53),(18,56),(19,59),(20,62),(21,65),(22,6),(23,71),(24,7),(25,77),(26,54),(27,80),(28,83),(29,86),(30,66),(31,9),(32,67),(33,10),(34,98),(35,58),(36,68),(37,11),(38,69),(39,12),(40,75),(41,60),(42,13),(43,113),(44,55),(45,117),(46,61),(47,84),(48,15),(49,120),(50,73),(51,16),(52,79),(53,127),(54,130),(55,132),(56,134),(57,137),(58,18),(59,140),(60,19),(61,145),(62,128),(63,147),(64,150),(65,153),(66,138),(67,21),(68,139),(69,22),(70,161),(71,129),(72,164),(73,133),(74,151),(75,24),(76,167),(77,142),(78,25),(79,146),(80,174),(81,177),(82,27),(83,183),(84,28),(85,187),(86,131),(87,189),(88,178),(89,30),(90,179),(91,31),(92,200),(93,180),(94,32),(95,181),(96,33),(97,47),(98,165),(99,34),(100,211),(101,143),(102,36),(103,37),(104,222),(105,38),(106,39),(107,48),(108,40),(109,171),(110,214),(111,42),(112,235),(113,46),(114,43),(115,52),(116,242),(117,245),(118,45),(119,249),(120,243),(121,49),(122,255),(123,244),(124,51),(125,259),(126,251),(139,57),(149,63),(151,64),(160,74),(162,70),(165,72),(168,76),(171,78),(179,81),(181,82),(188,85),(191,87),(193,88),(195,89),(197,90),(199,91),(201,92),(202,93),(203,94),(204,95),(205,96),(206,97),(209,99),(213,100),(214,101),(217,102),(220,103),(221,110),(222,118),(223,104),(224,105),(226,106),(227,111),(228,107),(229,124),(231,108),(233,109),(234,115),(236,112),(239,114),(243,116),(250,119),(253,121),(255,123),(256,122),(257,126),(260,125)]
  let step0 (r : ℤ × ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ × ℤ := (r.2.2.1,r.1,r.2.1,r.2.2.2+1)
  have check0 : ∀ i : Fin 174, pos (tab0.get i).2=step0 (pos (tab0.get i).1) := by
    dsimp only [pos,W,tab0,step0]
    decide
  have move0 (i : Fin 174) : p (f (tab0.get i).1)=f (tab0.get i).2 :=
    (hp _ _ _ _).trans (congrArg eval (check0 i).symm)
  let tab1 : List (ℕ × ℕ) := [(0,2),(1,6),(2,9),(3,11),(4,0),(5,18),(6,21),(7,1),(8,27),(9,30),(10,32),(11,36),(12,38),(13,3),(14,45),(15,47),(16,4),(17,54),(18,57),(19,5),(20,63),(21,66),(22,68),(23,72),(24,74),(25,7),(26,65),(27,81),(28,8),(29,87),(30,88),(31,90),(32,93),(33,95),(34,10),(35,100),(36,89),(37,91),(38,94),(39,96),(40,12),(41,70),(42,110),(43,13),(44,83),(45,58),(46,14),(47,92),(48,104),(49,15),(50,85),(51,75),(52,16),(53,128),(54,131),(55,17),(56,135),(57,138),(58,29),(59,141),(60,143),(61,19),(62,137),(63,148),(64,20),(65,154),(66,155),(67,156),(68,158),(69,159),(70,22),(71,150),(72,26),(73,23),(74,157),(75,34),(76,24),(77,152),(78,41),(79,25),(80,175),(81,178),(82,180),(83,184),(84,185),(85,28),(86,177),(87,190),(88,192),(89,194),(90,196),(91,198),(92,31),(93,193),(94,195),(95,197),(96,199),(97,33),(98,182),(99,208),(100,212),(101,35),(102,216),(103,219),(104,37),(105,217),(106,220),(107,39),(108,230),(109,40),(110,218),(111,225),(112,42),(113,215),(114,48),(115,43),(116,44),(117,246),(118,200),(119,46),(120,248),(121,252),(122,49),(123,50),(124,207),(125,51),(126,52),(129,53),(133,55),(136,56),(141,62),(142,59),(144,60),(146,61),(152,64),(157,67),(160,69),(163,71),(166,73),(169,76),(170,77),(172,78),(173,79),(176,80),(182,82),(184,86),(186,84),(188,98),(207,97),(210,99),(215,101),(218,102),(221,103),(225,105),(227,106),(229,107),(232,108),(233,111),(234,109),(237,112),(238,113),(240,114),(241,115),(244,116),(247,117),(248,118),(250,120),(251,119),(254,121),(256,124),(257,122),(258,123),(261,125),(262,126)]
  let step1 (r : ℤ × ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ × ℤ := (r.2.1+1,r.2.2.1,r.1,r.2.2.2-1)
  have check1 : ∀ i : Fin 174, pos (tab1.get i).2=step1 (pos (tab1.get i).1) := by
    dsimp only [pos,W,tab1,step1]
    decide
  have move1 (i : Fin 174) : q (f (tab1.get i).1)=f (tab1.get i).2 :=
    (hq _ _ _ _).trans (congrArg eval (check1 i).symm)
  by_contra no
  exact Erdos64.IndexThreeCore.chart_forces_cycle p q f move0 move1 sep G e₀ e₁ e₂ no

/-- The conjugates t,u,v commute and conjugation by p cycles them. -/
theorem cyclic_translation_cycle [Nonempty X] (p q t u v : Equiv.Perm X)
    (tq : q*p=t) (tu : Commute t u) (tv : Commute t v)
    (rot0 : SemiconjBy p t u) (rot1 : SemiconjBy p u v) (rot2 : SemiconjBy p v t)
    (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x) (G : SimpleGraph (Bool × X))
    (e₀ : ∀ x, G.Adj (false,x) (true,x)) (e₁ : ∀ x, G.Adj (false,x) (true,p x))
    (e₂ : ∀ x, G.Adj (false,x) (true,q x)) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G := by
  classical
  let x : X := Classical.choice inferInstance
  let f (a b c z : ℤ) := (t^a*u^b*v^c*p^z) x
  have h0 (a b c z : ℤ) : t (f a b c z)=f (a+1) b c z := by
    change (t*(t^a*u^b*v^c*p^z)) x=(t^(a+1)*u^b*v^c*p^z) x
    rw [add_comm a 1,zpow_add,zpow_one]
    simp only [mul_assoc]
  have hp (a b c z : ℤ) : p (f a b c z)=f c a b (z+1) := by
    change (p*(t^a*u^b*v^c*p^z)) x=(t^c*u^a*v^b*p^(z+1)) x
    apply congrArg (fun g : Equiv.Perm X => g x)
    have rearr : Commute (u^a*v^b) (t^c) := (tu.zpow_zpow c a).symm.mul_left (tv.zpow_zpow c b).symm
    calc
      _ = (p*t^a)*u^b*v^c*p^z := by group
      _ = (u^a*p)*u^b*v^c*p^z := by rw [(rot0.zpow_right a).eq]
      _ = u^a*(p*u^b)*v^c*p^z := by group
      _ = u^a*(v^b*p)*v^c*p^z := by rw [(rot1.zpow_right b).eq]
      _ = (u^a*v^b)*(p*v^c)*p^z := by group
      _ = (u^a*v^b)*(t^c*p)*p^z := by rw [(rot2.zpow_right c).eq]
      _ = ((u^a*v^b)*t^c)*(p*p^z) := by group
      _ = _ := by rw [rearr.eq,add_comm z 1,zpow_add,zpow_one]; simp only [mul_assoc]
  have hq (a b c z : ℤ) : q (f a b c z)=f (b+1) c a (z-1) := by
    have prev : p (f b c a (z-1))=f a b c z := by simpa using hp b c a (z-1)
    calc
      _ = (q*p) (f b c a (z-1)) := congrArg q prev.symm
      _ = _ := tq ▸ h0 b c a (z-1)
  exact chart_on_action p q f hp hq sep G e₀ e₁ e₂

private theorem quotient_three {Q : Type*} [Group Q] (card : Nat.card Q=3) (a b : Q) :
    a=1 ∨ b=1 ∨ a=b ∨ b*a=1 := by
  classical
  by_contra! h
  let : Finite Q := Nat.finite_of_card_ne_zero (by omega)
  let l := [1,a,b,b*a]
  have ba : b*a ≠ a := fun e => h.2.1 (mul_right_cancel (show b*a=1*a by simpa using e))
  have bb : b*a ≠ b := fun e => h.1 (mul_left_cancel (show b*a=b*1 by simpa using e))
  have nd : l.Nodup := by
    obtain ⟨a1,b1,ab,pair⟩ := h
    simp [l,a1.symm,b1.symm,pair.symm,ab,ba.symm,bb.symm]
  have bound := Nat.card_le_card_of_injective l.get (List.nodup_iff_injective_get.mp nd)
  simp only [Nat.card_fin] at bound
  change 4 ≤ Nat.card Q at bound
  omega

/-- All index-three abelian extensions, including actions with nontrivial stabilizers. -/
theorem index_three_matching_cycle [Nonempty X] (p q : Equiv.Perm X)
    (idx : ∃ N : Subgroup (Subgroup.closure ({p,q} : Set (Equiv.Perm X))),
      N.Normal ∧ IsMulCommutative N ∧ N.index=3)
    (sep : ∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x) (G : SimpleGraph (Bool × X))
    (e₀ : ∀ x, G.Adj (false,x) (true,x)) (e₁ : ∀ x, G.Adj (false,x) (true,p x))
    (e₂ : ∀ x, G.Adj (false,x) (true,q x)) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G := by
  classical
  let K := Subgroup.closure ({p,q} : Set (Equiv.Perm X))
  let a : K := ⟨p,Subgroup.subset_closure (by simp)⟩
  let b : K := ⟨q,Subgroup.subset_closure (by simp)⟩
  obtain ⟨N,normal,abelian,idx⟩ := idx
  let : N.Normal := normal
  have comm {g h : K} (hg : g∈N) (hh : h∈N) : Commute (g:Equiv.Perm X) (h:Equiv.Perm X) :=
    congrArg (fun z : N => ((z:K):Equiv.Perm X)) (abelian.is_comm.comm (⟨g,hg⟩ : N) (⟨h,hh⟩ : N))
  have rels {g : K} (hg : g ∈ N) (h : K) :
      Commute (g : Equiv.Perm X) ((h:Equiv.Perm X)*g*(h:Equiv.Perm X)⁻¹) :=
    comm hg (normal.conj_mem _ hg h)
  have short := fun ok => Erdos64.MatchingConjugate.matching_cycle_after_relabel p q sep ok G e₀ e₁ e₂
  let f := QuotientGroup.mk' N
  have mem (g : K) : f g=1 ↔ g∈N := QuotientGroup.eq_one_iff g
  have card : Nat.card (K ⧸ N)=3 := N.index_eq_card.symm.trans idx
  rcases quotient_three card (f a) (f b) with ha|hb|hab|ht
  · exact (short (.inl (rels ((mem a).mp ha) b))).imp_right (Or.imp_right Or.inl)
  · exact (short (.inr (.inl (rels ((mem b).mp hb) a)))).imp_right (Or.imp_right Or.inl)
  · have h : a⁻¹*b∈N := (mem _).mp (by simp [map_mul,map_inv,hab])
    exact (short (.inr (.inr (rels h a⁻¹)))).imp_right (Or.imp_right Or.inl)
  let t := b*a
  let u := a*t*a⁻¹
  let v := a*u*a⁻¹
  have tn : t∈N := (mem _).mp (by simpa only [t,map_mul] using ht)
  have un : u∈N := normal.conj_mem _ tn a
  have vn : v∈N := normal.conj_mem _ un a
  have an : a^3∈N := idx ▸ N.pow_index_mem a
  have central := comm an tn
  have last : SemiconjBy p (v:Equiv.Perm X) (t:Equiv.Perm X) := by
    change p*(p*(p*(t:Equiv.Perm X)*p⁻¹)*p⁻¹)=(t:Equiv.Perm X)*p
    change p^3*(t:Equiv.Perm X)=(t:Equiv.Perm X)*p^3 at central
    calc
      _ = (p^3*(t:Equiv.Perm X))*p⁻¹*p⁻¹ := by simp only [pow_succ,pow_zero,one_mul,mul_assoc]
      _ = ((t:Equiv.Perm X)*p^3)*p⁻¹*p⁻¹ := by rw [central]
      _ = _ := by group
  exact cyclic_translation_cycle p q t u v rfl (comm tn un) (comm tn vn)
    (by change p*(t:Equiv.Perm X)=(p*(t:Equiv.Perm X)*p⁻¹)*p; group)
    (by change p*(u:Equiv.Perm X)=(p*(u:Equiv.Perm X)*p⁻¹)*p; group)
    last sep G e₀ e₁ e₂

end Erdos64.IndexThree

namespace OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1_H2_R1_H1_R1
open scoped commutatorElement
open SimpleGraph

/-- A nontrivial abelian normal subgroup survives. The three matching labels are
distinct modulo this kernel, its index exceeds three, and each indicated
conjugate square has large defect. -/
def H1 : Prop :=
  ∀ (X : Type) [Fintype X] [Nonempty X] (p q : Equiv.Perm X),
    (∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x) →
    Fintype.card X ≤ 3 * {x : X | p (q x) ≠ q (p x)}.ncard →
    ¬ (Commute p ⁅p,q⁆ ∧ Commute q ⁅p,q⁆) →
    (∃ g ∈ Subgroup.closure ({p,q} : Set (Equiv.Perm X)), g ≠ 1 ∧ ∃ x : X, g x=x) →
    (∀ N : Subgroup (Subgroup.closure ({p,q} : Set (Equiv.Perm X))), N.Normal → IsMulCommutative N → N.index ≠ 11) →
    (∀ (a b : Equiv.Perm X), (a=p ∧ b=q) ∨ (a=q ∧ b=p) ∨ (a=p⁻¹*q ∧ b=p⁻¹) →
      Fintype.card X ≤ 3 * {y : X | (a*(b*a*b⁻¹)) y ≠ ((b*a*b⁻¹)*a) y}.ncard) →
    (∀ N : Subgroup (Subgroup.closure ({p,q} : Set (Equiv.Perm X))), N.Normal → IsMulCommutative N → N.index ≠ 3) →
    (∃ N : Subgroup (Subgroup.closure ({p,q} : Set (Equiv.Perm X))), N.Normal ∧ IsMulCommutative N ∧ N ≠ ⊥ ∧
      ∀ g : Subgroup.closure ({p,q} : Set (Equiv.Perm X)), g ∈ N → (g : Equiv.Perm X) ≠ p ∧ (g : Equiv.Perm X) ≠ q ∧ (g : Equiv.Perm X) ≠ p⁻¹*q) →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ SimpleGraph.fromRel (fun u v : Bool × X =>
      u.1 = false ∧ v.1 = true ∧ (v.2 = u.2 ∨ v.2 = p u.2 ∨ v.2 = q u.2))

/-- The generated group has no nontrivial abelian normal subgroup. -/
def H2 : Prop :=
  ∀ (X : Type) [Fintype X] [Nonempty X] (p q : Equiv.Perm X),
    (∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x) →
    Fintype.card X ≤ 3 * {x : X | p (q x) ≠ q (p x)}.ncard →
    ¬ (Commute p ⁅p,q⁆ ∧ Commute q ⁅p,q⁆) →
    (∃ g ∈ Subgroup.closure ({p,q} : Set (Equiv.Perm X)), g ≠ 1 ∧ ∃ x : X, g x=x) →
    (∀ N : Subgroup (Subgroup.closure ({p,q} : Set (Equiv.Perm X))), N.Normal → IsMulCommutative N → N.index ≠ 11) →
    (∀ (a b : Equiv.Perm X), (a=p ∧ b=q) ∨ (a=q ∧ b=p) ∨ (a=p⁻¹*q ∧ b=p⁻¹) →
      Fintype.card X ≤ 3 * {y : X | (a*(b*a*b⁻¹)) y ≠ ((b*a*b⁻¹)*a) y}.ncard) →
    (∀ N : Subgroup (Subgroup.closure ({p,q} : Set (Equiv.Perm X))), N.Normal → IsMulCommutative N → N = ⊥) →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ SimpleGraph.fromRel (fun u v : Bool × X =>
      u.1 = false ∧ v.1 = true ∧ (v.2 = u.2 ∨ v.2 = p u.2 ∨ v.2 = q u.2))

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1_H2_R1.H1 := by
  classical
  intro withKernel withoutKernel X _ _ p q sep density central fixed noEleven
  let G := SimpleGraph.fromRel (fun u v : Bool × X =>
    u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=p u.2 ∨ v.2=q u.2))
  have e₀ (x : X) : G.Adj (false,x) (true,x) := ⟨by simp,Or.inl ⟨rfl,rfl,Or.inl rfl⟩⟩
  have e₁ (x : X) : G.Adj (false,x) (true,p x) := ⟨by simp,Or.inl ⟨rfl,rfl,Or.inr (Or.inl rfl)⟩⟩
  have e₂ (x : X) : G.Adj (false,x) (true,q x) := ⟨by simp,Or.inl ⟨rfl,rfl,Or.inr (Or.inr rfl)⟩⟩
  by_cases three : ∃ N : Subgroup (Subgroup.closure ({p,q} : Set (Equiv.Perm X))),
      N.Normal ∧ IsMulCommutative N ∧ N.index=3
  · obtain h|h|h|h := Erdos64.IndexThree.index_three_matching_cycle p q three sep G e₀ e₁ e₂
    · exact ⟨2,by decide,h⟩
    · exact ⟨3,by decide,h⟩
    · exact ⟨4,by decide,h⟩
    · exact ⟨5,by decide,h⟩
  by_cases short : cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G
  · rcases short with h|h|h
    · exact ⟨2,by decide,h⟩
    · exact ⟨3,by decide,h⟩
    · exact ⟨4,by decide,h⟩
  have bounds := Erdos64.MatchingConjugate.relabel_defect_bounds p q sep G e₀ e₁ e₂ short
  let K := Subgroup.closure ({p,q} : Set (Equiv.Perm X))
  by_cases pos : ∃ N : Subgroup K, N.Normal ∧ IsMulCommutative N ∧ N ≠ ⊥
  · obtain ⟨N,normal,abelian,nt⟩ := pos
    apply withKernel X p q sep density central fixed noEleven bounds
    · exact fun M nm cm im => three ⟨M,nm,cm,im⟩
    refine ⟨N,normal,abelian,nt,?_⟩
    intro g hg
    let a : K := ⟨p,Subgroup.subset_closure (by simp)⟩
    let b : K := ⟨q,Subgroup.subset_closure (by simp)⟩
    have localComm (h : K) : Commute (g:Equiv.Perm X) ((h:Equiv.Perm X)*g*(h:Equiv.Perm X)⁻¹) :=
      congrArg (fun z : N => ((z:K):Equiv.Perm X))
        (abelian.is_comm.comm (⟨g,hg⟩ : N) (⟨h*g*h⁻¹,normal.conj_mem _ hg h⟩ : N))
    have impossible := fun ok => short (Erdos64.MatchingConjugate.matching_cycle_after_relabel p q sep ok G e₀ e₁ e₂)
    refine ⟨fun h => impossible (.inl ?_), fun h => impossible (.inr (.inl ?_)),fun h => impossible (.inr (.inr ?_))⟩
    · simpa only [← h] using localComm b
    · simpa only [← h] using localComm a
    · have raw : Commute (g:Equiv.Perm X) (p⁻¹*(g:Equiv.Perm X)*(p⁻¹)⁻¹) := localComm a⁻¹
      exact h ▸ raw
  · apply withoutKernel X p q sep density central fixed noEleven bounds
    intro N normal abelian
    by_contra nt
    exact pos ⟨N,normal,abelian,nt⟩

end OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1_H2_R1_H1_R1
