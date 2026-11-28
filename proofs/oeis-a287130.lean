import OMAStatements.S_oeis_a287130
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

-- Problem: A287130, decimal readout of the Rule 245 diagonal.
-- Source: https://oeis.org/A287130
-- Statement credit: @clementtrecourt
-- Canonical diagonal bridge and readout algebra: @CubeJerry.
-- Published geometry: Alexander R. Cohen and Other Mindset Lab, Certified Digit
-- Automata for Nonlinear Two-Dimensional Cellular Automata, doi:10.5281/zenodo.24384895.
-- Generic definitions and full-plane Rule 245 geometry are adapted from:
-- https://github.com/OtherMindset/congress-lean/tree/ca6b7eef533a5a8a0f1bb02780c1793b0f3568a4/lake/LT2D
-- Source license: CC BY 4.0, https://creativecommons.org/licenses/by/4.0/
-- Changes: import adaptation; kernel-reduced finite checks; omission of unrelated
-- whole-window counts; new canonical-recursion bridge, diagonal classification,
-- decimal closed forms and exact rational generating function.
-- The published full-plane geometry is reused and is not claimed as new.

-- Component: A269708Defs

/- Generic certificate infrastructure by Alexander R. Cohen and Other Mindset Lab,
CC BY 4.0; source: congress-lean commit ca6b7eef533a5a8a0f1bb02780c1793b0f3568a4,
lake/LT2D/Defs.lean. Import paths adapted; unused chunked theorems omitted in M4. -/
/-!
  LT2D definitions: the seven plane-wide definitions that every result in this project is about.
  Copied verbatim from post #mwmovuz3-8p5t1y (VN library, file M1). No other file declares them.
-/

namespace LT2D

/-- A cell of the plane. -/
abbrev Cell := Int × Int

/-- Outer totalistic von Neumann rule: new state = bit (c + 2k) of the rule number, where c is the
cell's own state (0/1) and k the number of ON cells among its four axial neighbours. -/
def ruleOut (rule : Nat) (c : Bool) (k : Nat) : Bool :=
  Nat.testBit rule (c.toNat + 2 * k)

/-- k = number of ON cells among the four axial neighbours of p. -/
def nbrOn (s : Cell → Bool) (p : Cell) : Nat :=
  (s (p.1 + 1, p.2)).toNat + (s (p.1 - 1, p.2)).toNat +
  (s (p.1, p.2 + 1)).toNat + (s (p.1, p.2 - 1)).toNat

/-- One synchronous step of the rule on the whole plane. -/
def step (rule : Nat) (s : Cell → Bool) : Cell → Bool :=
  fun p => ruleOut rule (s p) (nbrOn s p)

/-- Stage g of the rule on the whole plane, from one ON cell at the origin at stage 0.
For an odd rule (bit 0 = 1) every cell far from the seed is ON at stage 1. -/
def caState (rule : Nat) : Nat → Cell → Bool
  | 0 => fun p => decide (p = (0, 0))
  | g + 1 => step rule (caState rule g)

/-- The window [-g,g]^2 around the seed. -/
noncomputable def window (g : Nat) : Finset Cell :=
  Finset.Icc (-(g : Int)) g ×ˢ Finset.Icc (-(g : Int)) g

/-- The OEIS count: number of ON cells of stage g inside the (2g+1) x (2g+1) square around the seed. -/
noncomputable def onCount (rule g : Nat) : Nat :=
  ((window g).filter (fun p => caState rule g p = true)).card

end LT2D

-- Component: A269708Basic

/- Generic certificate infrastructure by Alexander R. Cohen and Other Mindset Lab,
CC BY 4.0; source: congress-lean commit ca6b7eef533a5a8a0f1bb02780c1793b0f3568a4,
lake/LT2D/Basic.lean. Import paths adapted; unused chunked theorems omitted in M4. -/
/-!
  LT2D basic lemmas: one copy of each lemma that several posted files declared.
  Each declaration is copied verbatim from the post named above it.
-/

namespace LT2D

-- from #mwmbjanx-5lciqx
/-- A and B have the same members. -/
def sameSet (A B : List Cell) : Bool :=
  A.all (fun p => B.contains p) && B.all (fun p => A.contains p)

-- from #mwmbjanx-5lciqx
theorem sameSet_contains {A B : List Cell} (h : sameSet A B = true) (q : Cell) :
    A.contains q = B.contains q := by
  simp only [sameSet, Bool.and_eq_true, List.all_eq_true] at h
  cases hA : A.contains q <;> cases hB : B.contains q
  · rfl
  · have := h.2 q (by simpa using hB)
    simp_all
  · have := h.1 q (by simpa using hA)
    simp_all
  · rfl

-- from #mwmbjanx-5lciqx
/-- The configuration that is ON everywhere except on D. -/
def coFin (D : List Cell) : Cell → Bool := fun p => !(D.contains p)

-- from #mwmbjanx-5lciqx
theorem coFin_congr {A B : List Cell} (h : ∀ q, A.contains q = B.contains q) :
    coFin A = coFin B := by
  funext q
  simp only [coFin, h q]

-- from #mwmbjanx-5lciqx
/-- The configuration that is ON exactly on L. -/
def finOn (L : List Cell) : Cell → Bool := fun p => L.contains p

-- from #mwmezycj-p4n3xa
theorem finOn_congr {A B : List Cell} (h : ∀ q, A.contains q = B.contains q) :
    finOn A = finOn B := by
  funext q
  simp only [finOn, h q]

-- from #mwmbjanx-5lciqx
/-- Each cell of L together with its four axial neighbours. -/
def cands (L : List Cell) : List Cell :=
  L.flatMap (fun p => [p, (p.1 + 1, p.2), (p.1 - 1, p.2), (p.1, p.2 + 1), (p.1, p.2 - 1)])

-- from #mwmbjanx-5lciqx
theorem contains_cands_false {L : List Cell} {p : Cell} (h : (cands L).contains p = false) :
    L.contains p = false ∧ L.contains (p.1 + 1, p.2) = false ∧ L.contains (p.1 - 1, p.2) = false ∧
      L.contains (p.1, p.2 + 1) = false ∧ L.contains (p.1, p.2 - 1) = false := by
  have key : ∀ q, q ∈ L → ∀ r, r ∈ [q, (q.1 + 1, q.2), (q.1 - 1, q.2), (q.1, q.2 + 1), (q.1, q.2 - 1)] →
      (cands L).contains r = true := by
    intro q hq r hr
    simp only [cands, List.contains_iff_mem, List.mem_flatMap]
    exact ⟨q, hq, hr⟩
  obtain ⟨x, y⟩ := p
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (rw [Bool.eq_false_iff]; intro hc; rw [List.contains_iff_mem] at hc)
  · have := key _ hc (x, y) (by simp); simp_all
  · have := key _ hc (x, y) (by simp); simp_all
  · have := key _ hc (x, y) (by simp); simp_all
  · have := key _ hc (x, y) (by simp); simp_all
  · have := key _ hc (x, y) (by simp); simp_all

-- from #mwmbjanx-5lciqx
/-- The cells of C that are OFF after one step from s. -/
def offAfter (rule : Nat) (s : Cell → Bool) (C : List Cell) : List Cell :=
  C.filter (fun p => !(step rule s p))

-- from #mwmbjanx-5lciqx
theorem contains_offAfter (rule : Nat) (s : Cell → Bool) (C : List Cell) (p : Cell) :
    (offAfter rule s C).contains p = (C.contains p && !(step rule s p)) := by
  simp only [offAfter]
  cases hs : step rule s p <;> cases hc : C.contains p <;>
    simp_all [List.contains_iff_mem, List.mem_filter]

-- from #mwmezycj-p4n3xa
/-- The cells of C that are ON after one step from s. -/
def onAfter (rule : Nat) (s : Cell → Bool) (C : List Cell) : List Cell :=
  C.filter (fun p => step rule s p)

-- from #mwmezycj-p4n3xa
theorem contains_onAfter (rule : Nat) (s : Cell → Bool) (C : List Cell) (p : Cell) :
    (onAfter rule s C).contains p = (C.contains p && step rule s p) := by
  simp only [onAfter]
  cases hs : step rule s p <;> cases hc : C.contains p <;>
    simp_all [List.contains_iff_mem, List.mem_filter]

-- from #mwmbjanx-5lciqx
theorem caState_zero (rule : Nat) : caState rule 0 = finOn [(0, 0)] := by
  funext p
  simp [caState, finOn]

-- from #mwmbjanx-5lciqx
/-- Odd rule: from a finite ON set, the next stage is ON except on finitely many candidates. -/
theorem step_finOn {rule : Nat} (h0 : Nat.testBit rule 0 = true) (L : List Cell) :
    step rule (finOn L) = coFin (offAfter rule (finOn L) (cands L)) := by
  funext p
  simp only [coFin, contains_offAfter]
  cases hc : (cands L).contains p
  · obtain ⟨h1, h2, h3, h4, h5⟩ := contains_cands_false hc
    simp only [step, ruleOut, nbrOn, finOn, h1, h2, h3, h4, h5, Bool.toNat_false, Bool.false_and, Bool.not_false]
    exact h0
  · simp

-- from #mwmbjanx-5lciqx
/-- Bit 9 set: from ON-except-D, the next stage is ON except on candidates near D. -/
theorem step_coFin {rule : Nat} (h9 : Nat.testBit rule 9 = true) (D : List Cell) :
    step rule (coFin D) = coFin (offAfter rule (coFin D) (cands D)) := by
  funext p
  simp only [coFin, contains_offAfter]
  cases hc : (cands D).contains p
  · obtain ⟨h1, h2, h3, h4, h5⟩ := contains_cands_false hc
    simp only [step, ruleOut, nbrOn, coFin, h1, h2, h3, h4, h5, Bool.not_false, Bool.toNat_true, Bool.false_and]
    exact h9
  · simp

-- from #mwmezycj-p4n3xa
/-- Bit 9 clear: from ON-except-D, the next stage is ON only on candidates near D. -/
theorem step_coFin0 {rule : Nat} (h9 : Nat.testBit rule 9 = false) (D : List Cell) :
    step rule (coFin D) = finOn (onAfter rule (coFin D) (cands D)) := by
  funext p
  simp only [finOn, contains_onAfter]
  cases hc : (cands D).contains p
  · obtain ⟨h1, h2, h3, h4, h5⟩ := contains_cands_false hc
    simp only [step, ruleOut, nbrOn, coFin, h1, h2, h3, h4, h5, Bool.not_false, Bool.toNat_true,
      Bool.false_and]
    exact h9
  · simp

-- from #mwmbjanx-5lciqx
/-- Bit 9 set: the all-ON plane is a fixed point. -/
theorem step_allOn {rule : Nat} (h9 : Nat.testBit rule 9 = true) :
    step rule (fun _ => true) = fun _ => true := by
  funext p
  simp only [step, ruleOut, nbrOn, Bool.toNat_true]
  exact h9

-- from #mwmbjanx-5lciqx
theorem card_window (g : Nat) : (window g).card = (2 * g + 1) ^ 2 := by
  rw [window, Finset.card_product, Int.card_Icc, sq]
  congr 1 <;> omega

-- from #mwmovuz3-8p5t1y
/-- B3: the neighbour count of a state that depends only on (|x|, |y|) -/
theorem nbrOn_abs (s : Cell → Bool) (W : Nat → Nat → Bool)
    (hs : ∀ x y : Int, s (x, y) = W x.natAbs y.natAbs) (x y : Int) :
    nbrOn s (x, y) =
      (W (x.natAbs + 1) y.natAbs).toNat +
      (if x.natAbs = 0 then W 1 y.natAbs else W (x.natAbs - 1) y.natAbs).toNat +
      (W x.natAbs (y.natAbs + 1)).toNat +
      (if y.natAbs = 0 then W x.natAbs 1 else W x.natAbs (y.natAbs - 1)).toNat := by
  have hx : (W (x + 1).natAbs y.natAbs).toNat + (W (x - 1).natAbs y.natAbs).toNat =
      (W (x.natAbs + 1) y.natAbs).toNat +
      (if x.natAbs = 0 then W 1 y.natAbs else W (x.natAbs - 1) y.natAbs).toNat := by
    rcases lt_trichotomy x 0 with h | h | h
    · rw [show (x + 1).natAbs = x.natAbs - 1 by omega, show (x - 1).natAbs = x.natAbs + 1 by omega,
        if_neg (by omega)]
      omega
    · subst h
      rfl
    · rw [show (x + 1).natAbs = x.natAbs + 1 by omega, show (x - 1).natAbs = x.natAbs - 1 by omega,
        if_neg (by omega)]
  have hy : (W x.natAbs (y + 1).natAbs).toNat + (W x.natAbs (y - 1).natAbs).toNat =
      (W x.natAbs (y.natAbs + 1)).toNat +
      (if y.natAbs = 0 then W x.natAbs 1 else W x.natAbs (y.natAbs - 1)).toNat := by
    rcases lt_trichotomy y 0 with h | h | h
    · rw [show (y + 1).natAbs = y.natAbs - 1 by omega, show (y - 1).natAbs = y.natAbs + 1 by omega,
        if_neg (by omega)]
      omega
    · subst h
      rfl
    · rw [show (y + 1).natAbs = y.natAbs + 1 by omega, show (y - 1).natAbs = y.natAbs - 1 by omega,
        if_neg (by omega)]
  unfold nbrOn
  simp only [hs]
  omega

section
open Finset

-- from #mwmowkxn-5swdpn
/-- S2: a sum over [-g, g] of a function of |x| -/
theorem sum_Icc_natAbs (h : Nat → Int) (g : Nat) :
    ∑ x ∈ Icc (-(g : Int)) g, h x.natAbs = 2 * ∑ a ∈ range (g + 1), h a - h 0 := by
  induction g with
  | zero => simp <;> ring
  | succ g ih =>
    have e : Icc (-((g + 1 : Nat) : Int)) ((g + 1 : Nat) : Int) =
        insert (-((g : Int) + 1)) (insert ((g : Int) + 1) (Icc (-(g : Int)) g)) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      push_cast
      omega
    have n1 : ((g : Int) + 1) ∉ Icc (-(g : Int)) g := by
      simp only [Finset.mem_Icc]
      omega
    have n2 : -((g : Int) + 1) ∉ insert ((g : Int) + 1) (Icc (-(g : Int)) g) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [e, Finset.sum_insert n2, Finset.sum_insert n1, ih, Finset.sum_range_succ h (g + 1)]
    rw [show (-((g : Int) + 1)).natAbs = g + 1 by omega, show ((g : Int) + 1).natAbs = g + 1 by omega]
    ring

-- from #mwmowkxn-5swdpn
/-- S3: the window count of a stage that depends only on (|x|, |y|) -/
theorem onCount_fold (rule g : Nat) (W : Nat → Nat → Bool)
    (hW : ∀ x y : Int, caState rule g (x, y) = W x.natAbs y.natAbs) :
    (onCount rule g : Int) =
      4 * ∑ a ∈ range (g + 1), ∑ b ∈ range (g + 1), ((W a b).toNat : Int)
      - 2 * ∑ a ∈ range (g + 1), ((W a 0).toNat : Int)
      - 2 * ∑ b ∈ range (g + 1), ((W 0 b).toNat : Int) + ((W 0 0).toNat : Int) := by
  have h1 : (onCount rule g : Int) = ∑ x ∈ Icc (-(g : Int)) g, ∑ y ∈ Icc (-(g : Int)) g,
      ((W x.natAbs y.natAbs).toNat : Int) := by
    unfold onCount window
    rw [Finset.card_filter, Nat.cast_sum, Finset.sum_product]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    rw [hW x y]
    cases W x.natAbs y.natAbs <;> simp
  have inner : ∀ x : Int, ∑ y ∈ Icc (-(g : Int)) g, ((W x.natAbs y.natAbs).toNat : Int) =
      2 * ∑ b ∈ range (g + 1), ((W x.natAbs b).toNat : Int) - ((W x.natAbs 0).toNat : Int) :=
    fun x => sum_Icc_natAbs (fun b => ((W x.natAbs b).toNat : Int)) g
  rw [h1, Finset.sum_congr rfl (fun x _ => inner x), Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_Icc_natAbs (fun a => ∑ b ∈ range (g + 1), ((W a b).toNat : Int)) g,
    sum_Icc_natAbs (fun a => ((W a 0).toNat : Int)) g]
  ring

end

end LT2D

-- Component: A287130Core

/- Attributed plane-shape result by Alexander R. Cohen and Other Mindset Lab, CC BY4.0.
Source: congress-lean ca6b7eef533a5a8a0f1bb02780c1793b0f3568a4/lake/LT2D/Early/R245_A.lean.
Import paths adapted; unrelated window counts omitted. -/
/- R245_A (Claude congress Leader, 18 Nov 2026): core part for A271005 (Rules 245, 501); no imports. -/
namespace LT2D

/-! ## Finite-list device: a finite ON list (`finOn`) or ON except a finite list (`coFin`) -/

theorem step_coFin_off {rule : Nat} (h9 : Nat.testBit rule 9 = false) (D : List Cell) :
    step rule (coFin D) = finOn (onAfter rule (coFin D) (cands D)) := by
  funext p
  simp only [finOn, contains_onAfter]
  cases hc : (cands D).contains p
  · obtain ⟨h1, h2, h3, h4, h5⟩ := contains_cands_false hc
    simp only [step, ruleOut, nbrOn, coFin, h1, h2, h3, h4, h5, Bool.not_false, Bool.toNat_true, Bool.false_and]
    exact h9
  · simp

/-! ## Stages 1..6 of Rules 245 and 501 -/

private def D1 : List Cell := [(0, 0)]
def L2 : List Cell := [(-1, 0), (0, -1), (0, 1), (1, 0)]
def L2' : List Cell := [(-1, 0), (0, -1), (0, 0), (0, 1), (1, 0)]
private def D3 : List Cell := [(-1, 0), (0, -1), (0, 0), (0, 1), (1, 0)]
def L4 : List Cell := [(-2, 0), (-1, -1), (-1, 0), (-1, 1), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2),
  (1, -1), (1, 0), (1, 1), (2, 0)]
def D5 : List Cell := [(-2, 0), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (2, 0)]
def L6 : List Cell := [(-3, 0), (-2, -1), (-2, 0), (-2, 1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2),
  (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2),
  (2, -1), (2, 0), (2, 1), (3, 0)]

abbrev Stages (r : Nat) : Prop := caState r 1 = coFin D1 ∧ caState r 3 = coFin D3 ∧
  caState r 4 = finOn L4 ∧ caState r 5 = coFin D5 ∧ caState r 6 = finOn L6

private theorem stages {r : Nat} (M : List Cell) (b0 : Nat.testBit r 0 = true) (b9 : Nat.testBit r 9 = false)
    (e : (sameSet (offAfter r (finOn [(0, 0)]) (cands [(0, 0)])) D1 &&
      sameSet (onAfter r (coFin D1) (cands D1)) M && sameSet (offAfter r (finOn M) (cands M)) D3 &&
      sameSet (onAfter r (coFin D3) (cands D3)) L4 && sameSet (offAfter r (finOn L4) (cands L4)) D5 &&
      sameSet (onAfter r (coFin D5) (cands D5)) L6) = true) : Stages r := by
  simp only [Bool.and_eq_true] at e
  obtain ⟨⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩, e6⟩ := e
  have s1 : caState r 1 = coFin D1 := by
    show step r (caState r 0) = _
    rw [caState_zero, step_finOn b0]; exact coFin_congr (sameSet_contains e1)
  have s2 : caState r 2 = finOn M := by
    show step r (caState r 1) = _
    rw [s1, step_coFin_off b9]; exact finOn_congr (sameSet_contains e2)
  have s3 : caState r 3 = coFin D3 := by
    show step r (caState r 2) = _
    rw [s2, step_finOn b0]; exact coFin_congr (sameSet_contains e3)
  have s4 : caState r 4 = finOn L4 := by
    show step r (caState r 3) = _
    rw [s3, step_coFin_off b9]; exact finOn_congr (sameSet_contains e4)
  have s5 : caState r 5 = coFin D5 := by
    show step r (caState r 4) = _
    rw [s4, step_finOn b0]; exact coFin_congr (sameSet_contains e5)
  refine ⟨s1, s3, s4, s5, ?_⟩
  show step r (caState r 5) = _
  rw [s5, step_coFin_off b9]; exact finOn_congr (sameSet_contains e6)

theorem st245 : Stages 245 := stages L2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem st501 : Stages 501 := stages L2' (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ## Closed forms through coordinate features -/

/-- Features of a coordinate z relative to h: z = 0, |z| ≤ 1, |z| = 1, |z| ≤ h-1, |z| = h, |z| = h+1. -/
structure Feat where
  o : Bool
  a : Bool
  d : Bool
  b : Bool
  t : Bool
  u : Bool
  deriving DecidableEq

def fe (h z : Int) : Feat :=
  ⟨decide (z = 0), decide (-1 ≤ z) && decide (z ≤ 1), decide (z = 1) || decide (z = -1),
   decide (1 - h ≤ z) && decide (z ≤ h - 1), decide (z = h) || decide (z = -h),
   decide (z = h + 1) || decide (z = -h - 1)⟩

def fe3 (h z : Int) : Feat × Feat × Feat := (fe h (z - 1), fe h z, fe h (z + 1))

/-- E-shape (stage 2h for h ≥ 3): ON iff (|y|≤1, |x|≤h-1) or (|x|≤1, |y|≤h-1) or (y=0, |x|=h) or (x=0, |y|=h). -/
def EF (fx fy : Feat) : Bool := (fy.a && fx.b) || (fx.a && fy.b) || (fy.o && fx.t) || (fx.o && fy.t)
/-- O-shape (stage 2h+1 for h ≥ 3): OFF iff (x=0, |y|≤h) or (y=0, |x|≤h) or (|x|=1, |y|=1). -/
def OF (fx fy : Feat) : Bool := !((fx.o && (fy.b || fy.t)) || (fy.o && (fx.b || fx.t)) || (fx.d && fy.d))
def EF1 (fx fy : Feat) : Bool :=
  (fy.a && (fx.b || fx.t)) || (fx.a && (fy.b || fy.t)) || (fy.o && fx.u) || (fx.o && fy.u)

def Ecf (h : Int) (p : Cell) : Bool := EF (fe h p.1) (fe h p.2)
def Ocf (h : Int) (p : Cell) : Bool := OF (fe h p.1) (fe h p.2)

def F (n : Nat) : Feat := ⟨n.testBit 0, n.testBit 1, n.testBit 2, n.testBit 3, n.testBit 4, n.testBit 5⟩
/-- The 17 feature triples (z-1, z, z+1) that occur for h ≥ 3. -/
def T17 : List (Feat × Feat × Feat) :=
  [(0, 0, 0), (0, 0, 32), (0, 32, 16), (32, 0, 0), (32, 16, 8), (16, 32, 0), (16, 8, 8), (16, 8, 14), (8, 16, 32), (8, 8, 16), (8, 8, 8), (8, 8, 14), (8, 14, 11), (14, 8, 16), (14, 8, 8), (14, 11, 14), (11, 14, 8)].map fun (a, b, c) => (F a, F b, F c)

def stepF (r : Nat) (F : Feat → Feat → Bool) (X Y : Feat × Feat × Feat) : Bool :=
  ruleOut r (F X.2.1 Y.2.1)
    ((F X.2.2 Y.2.1).toNat + (F X.1 Y.2.1).toNat + (F X.2.1 Y.2.2).toNat + (F X.2.1 Y.1).toNat)
def check1 (r : Nat) : Bool := T17.all (fun X => T17.all (fun Y => stepF r EF X Y == OF X.2.1 Y.2.1))
def check2 (r : Nat) : Bool := T17.all (fun X => T17.all (fun Y => stepF r OF X Y == EF1 X.2.1 Y.2.1))

theorem check1_245 : check1 245 = true := by decide +kernel
theorem check2_245 : check2 245 = true := by decide +kernel
theorem check1_501 : check1 501 = true := by decide +kernel
theorem check2_501 : check2 501 = true := by decide +kernel

theorem fe3_mem (h z : Int) (hh : 3 ≤ h) : fe3 h z ∈ T17 := by
  by_cases hs : h ≤ 6 ∧ -9 < z ∧ z < 9
  · have hh' : h = 3 ∨ h = 4 ∨ h = 5 ∨ h = 6 := by omega
    have hz' : z = -8 ∨ z = -7 ∨ z = -6 ∨ z = -5 ∨ z = -4 ∨ z = -3 ∨ z = -2 ∨ z = -1 ∨ z = 0 ∨
        z = 1 ∨ z = 2 ∨ z = 3 ∨ z = 4 ∨ z = 5 ∨ z = 6 ∨ z = 7 ∨ z = 8 := by omega
    rcases hh' with rfl | rfl | rfl | rfl <;>
    rcases hz' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> decide
  have key : (h ≤ 6 ∧ (z ≤ -9 ∨ 9 ≤ z)) ∨ (7 ≤ h ∧ (z < -h-2 ∨ z = -h-2 ∨ z = -h-1 ∨ z = -h ∨
      z = -h+1 ∨ z = -h+2 ∨ (-h+2 < z ∧ z < -2) ∨ z = -2 ∨ z = -1 ∨ z = 0 ∨ z = 1 ∨ z = 2 ∨
      (2 < z ∧ z < h-2) ∨ z = h-2 ∨ z = h-1 ∨ z = h ∨ z = h+1 ∨ z = h+2 ∨ h+2 < z)) := by omega
  rcases key with ⟨h6, hz | hz⟩ | ⟨h7, hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz |
      hz | hz | hz | hz | hz | hz⟩ <;>
  simp (disch := omega) only [fe3, fe, decide_eq_true, decide_eq_false, Bool.and_true,
    Bool.and_false, Bool.true_and, Bool.false_and, Bool.or_true, Bool.or_false, Bool.true_or,
    Bool.false_or] <;>
  decide

theorem S1 {r : Nat} (c1 : check1 r = true) {h : Int} (hh : 3 ≤ h) : step r (Ecf h) = Ocf h := by
  funext ⟨x, y⟩
  have := List.all_eq_true.mp (List.all_eq_true.mp c1 _ (fe3_mem h x hh)) _ (fe3_mem h y hh)
  exact beq_iff_eq.mp this

theorem fe_succ_o (h z : Int) : (fe (h + 1) z).o = (fe h z).o := rfl
theorem fe_succ_a (h z : Int) : (fe (h + 1) z).a = (fe h z).a := rfl
theorem fe_succ_b {h : Int} (hh : 0 ≤ h) (z : Int) : (fe (h + 1) z).b = ((fe h z).b || (fe h z).t) := by
  rw [Bool.eq_iff_iff]
  simp only [fe, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  omega
theorem fe_succ_t (h z : Int) : (fe (h + 1) z).t = (fe h z).u := by
  rw [Bool.eq_iff_iff]
  simp only [fe, Bool.or_eq_true, decide_eq_true_eq]
  omega

theorem Ecf_succ {h : Int} (hh : 0 ≤ h) (p : Cell) : Ecf (h + 1) p = EF1 (fe h p.1) (fe h p.2) := by
  simp only [Ecf, EF, EF1, fe_succ_o, fe_succ_a, fe_succ_b hh, fe_succ_t]

theorem S2 {r : Nat} (c2 : check2 r = true) {h : Int} (hh : 3 ≤ h) : step r (Ocf h) = Ecf (h + 1) := by
  funext ⟨x, y⟩
  rw [Ecf_succ (by omega)]
  have := List.all_eq_true.mp (List.all_eq_true.mp c2 _ (fe3_mem h x hh)) _ (fe3_mem h y hh)
  exact beq_iff_eq.mp this

end LT2D

-- Component: A287130Shape

/- Attributed plane-shape result by Alexander R. Cohen and Other Mindset Lab, CC BY4.0.
Source: congress-lean ca6b7eef533a5a8a0f1bb02780c1793b0f3568a4/lake/LT2D/Early/R245_B.lean.
Import paths adapted; unrelated window counts omitted. -/

/- R245_B (Claude congress Leader, 18 Nov 2026): Mathlib part for A271005; imports the core part R245_A. -/
/-! ## Mathlib part: the OEIS count and the main theorems for A271005 (Rules 245 and 501) -/
namespace LT2D

/-! ## Base: stage 6 is the E-shape for h = 3 -/

private def box9 : List Int := [-4, -3, -2, -1, 0, 1, 2, 3, 4]
private theorem base_box : box9.all (fun x => box9.all (fun y => finOn L6 (x, y) == Ecf 3 (x, y))) = true := by
  decide
theorem L6_small : L6.all (fun p => decide (-4 < p.1 ∧ p.1 < 4 ∧ -4 < p.2 ∧ p.2 < 4)) = true := by
  decide

theorem finOn_L6 : finOn L6 = Ecf 3 := by
  funext ⟨x, y⟩
  by_cases hb : -4 ≤ x ∧ x ≤ 4 ∧ -4 ≤ y ∧ y ≤ 4
  · have hx : x ∈ box9 := by simp only [box9, List.mem_cons, List.not_mem_nil]; omega
    have hy : y ∈ box9 := by simp only [box9, List.mem_cons, List.not_mem_nil]; omega
    exact beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp base_box x hx) y hy)
  · have e2 : finOn L6 (x, y) = false := by
      rw [finOn, Bool.eq_false_iff]
      intro hc
      rw [List.contains_iff_mem] at hc
      have := List.all_eq_true.mp L6_small _ hc
      simp only [decide_eq_true_eq] at this
      omega
    rw [e2]
    rcases (show x < -4 ∨ 4 < x ∨ y < -4 ∨ 4 < y by omega) with hz | hz | hz | hz <;>
    simp (disch := omega) only [Ecf, EF, fe, decide_eq_true, decide_eq_false, Bool.and_true,
      Bool.and_false, Bool.true_and, Bool.false_and, Bool.or_true, Bool.or_false, Bool.true_or,
      Bool.false_or]

/-! ## Induction: stage 2m+6 = E-shape (m+3), stage 2m+7 = O-shape (m+3) -/

theorem closed_of {r : Nat} (c1 : check1 r = true) (c2 : check2 r = true) (base : caState r 6 = Ecf 3)
    (m : Nat) : caState r (2 * m + 6) = Ecf ((m : Int) + 3) ∧
      caState r (2 * m + 7) = Ocf ((m : Int) + 3) := by
  have odd : ∀ m : Nat, caState r (2 * m + 6) = Ecf ((m : Int) + 3) →
      caState r (2 * m + 7) = Ocf ((m : Int) + 3) := by
    intro m hm
    show step r (caState r (2 * m + 6)) = _
    rw [hm, S1 c1 (by omega)]
  induction m with
  | zero => exact ⟨base, odd 0 base⟩
  | succ m ih =>
    have he : caState r (2 * (m + 1) + 6) = Ecf (((m + 1 : Nat) : Int) + 3) := by
      rw [show 2 * (m + 1) + 6 = (2 * m + 7) + 1 by omega,
        show (((m + 1 : Nat) : Int) + 3) = ((m : Int) + 3) + 1 by omega]
      show step r (caState r (2 * m + 7)) = _
      rw [ih.2, S2 c2 (by omega)]
    exact ⟨he, odd (m + 1) he⟩

theorem r245_closed (m : Nat) : caState 245 (2 * m + 6) = Ecf ((m : Int) + 3) ∧
    caState 245 (2 * m + 7) = Ocf ((m : Int) + 3) :=
  closed_of check1_245 check2_245 (st245.2.2.2.2.trans finOn_L6) m

end LT2D

-- Component: A287130Diagonal

/- The diagonal readout below is derived here from the attributed, general
   full-plane theorem r245_closed in A287130Shape. -/
namespace A287130Proof
open OMA.S_oeis_a287130

lemma cell_eq (code t : ℕ) (i j : ℤ) :
    LT2D.caState code t (i, j) = cell code t i j := by
  induction t generalizing i j with
  | zero => simp [LT2D.caState, cell, Prod.mk.injEq]
  | succ t ih =>
    simp only [LT2D.caState, LT2D.step, LT2D.ruleOut, LT2D.nbrOn, cell, ih]

lemma even_diagonal (m k : ℕ) :
    cell 245 (2 * m + 6) k k = decide (k ≤ 1) := by
  rw [← cell_eq, (LT2D.r245_closed m).1]
  apply Bool.eq_iff_iff.mpr
  simp only [LT2D.Ecf, LT2D.EF, LT2D.fe, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq]
  omega

lemma odd_diagonal (m k : ℕ) :
    cell 245 (2 * m + 7) k k = decide (2 ≤ k) := by
  rw [← cell_eq, (LT2D.r245_closed m).2]
  apply Bool.eq_iff_iff.mpr
  simp only [LT2D.Ocf, LT2D.OF, LT2D.fe, Bool.not_eq_true', Bool.and_eq_false_iff,
    Bool.or_eq_false_iff, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    decide_eq_false_iff_not]
  omega

lemma diagonal (n k : ℕ) (hn : 6 ≤ n) (_hk : k ≤ n) :
    cell 245 n k k = decide ((n % 2 = 0 ∧ k ≤ 1) ∨ (n % 2 = 1 ∧ 2 ≤ k)) := by
  by_cases he : n % 2 = 0
  · obtain ⟨m, hm⟩ : ∃ m, n = 2 * m + 6 := ⟨(n - 6) / 2, by omega⟩
    rw [hm, even_diagonal]
    simp [Nat.add_mod, Nat.mul_mod]
  · obtain ⟨m, hm⟩ : ∃ m, n = 2 * m + 7 := ⟨(n - 7) / 2, by omega⟩
    rw [hm, odd_diagonal]
    simp [Nat.add_mod, Nat.mul_mod]

end A287130Proof

-- Component: A287130Algebra

namespace A287130Algebra

open OMA.S_oeis_a287130 PowerSeries

def digits (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), if cell 245 n k k then (10 : ℚ) ^ (n - k) else 0

lemma a_cast (n : ℕ) : (a n : ℚ) = digits n := by
  simp [a, digits]

lemma initial : a 0 = 1 ∧ a 1 = 1 ∧ a 2 = 0 ∧ a 3 = 111 ∧
    a 4 = 11000 ∧ a 5 = 11111 := by decide +kernel

lemma geom_scaled (m : ℕ) :
    9 * (∑ k ∈ Finset.range m, (10 : ℚ) ^ k) = 10 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, pow_succ]
    linarith

def Diagonal : Prop := ∀ n k : ℕ, 6 ≤ n → k ≤ n →
  cell 245 n k k = decide ((n % 2 = 0 ∧ k ≤ 1) ∨ (n % 2 = 1 ∧ 2 ≤ k))

lemma even_formula (hdiag : Diagonal) (n : ℕ) (hn : 6 ≤ n) (he : Even n) :
    (a n : ℚ) = 11 * (10 : ℚ) ^ (n - 1) := by
  have hm : n % 2 = 0 := Nat.even_iff.mp he
  rw [a_cast]
  unfold digits
  calc
    _ = ∑ k ∈ Finset.range (n + 1), if k ≤ 1 then (10 : ℚ) ^ (n - k) else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      rw [hdiag n k hn (by omega)]
      simp [hm]
    _ = (10 : ℚ) ^ n + 10 ^ (n - 1) := by
      rw [show n + 1 = 2 + (n - 1) by omega, Finset.sum_range_add]
      have hz : (∑ k ∈ Finset.range (n - 1),
          if 2 + k ≤ 1 then (10 : ℚ) ^ (n - (2 + k)) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro k _
        simp only [if_neg (by omega : ¬ 2 + k ≤ 1)]
      rw [hz]
      norm_num [Finset.sum_range_succ]
    _ = _ := by
      have hp : (10 : ℚ) ^ n = 10 ^ (n - 1) * 10 := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hp]
      ring

lemma odd_formula (hdiag : Diagonal) (n : ℕ) (hn : 6 ≤ n) (ho : Odd n) :
    (a n : ℚ) = ((10 : ℚ) ^ n - 10) / 90 := by
  have hm : n % 2 = 1 := Nat.odd_iff.mp ho
  have hs : digits n = ∑ k ∈ Finset.range (n - 1), (10 : ℚ) ^ k := by
    unfold digits
    calc
      _ = ∑ k ∈ Finset.range (n + 1), if 2 ≤ k then (10 : ℚ) ^ (n - k) else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk' := Finset.mem_range.mp hk
        rw [hdiag n k hn (by omega)]
        simp [hm]
      _ = ∑ k ∈ Finset.range (n - 1), (10 : ℚ) ^ (n - 2 - k) := by
        rw [show n + 1 = 2 + (n - 1) by omega, Finset.sum_range_add]
        simp [Finset.sum_range_succ, Nat.sub_sub]
      _ = _ := by
        simpa [show n - 1 - 1 = n - 2 by omega] using
          Finset.sum_range_reflect (fun k => (10 : ℚ) ^ k) (n - 1)
  rw [a_cast, hs]
  have hg := geom_scaled (n - 1)
  have hp : (10 : ℚ) ^ n = 10 ^ (n - 1) * 10 := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hp]
  linarith

lemma recurrence (hdiag : Diagonal) (n : ℕ) (hn : 10 ≤ n) :
    (a n : ℚ) = 101 * a (n - 2) - 100 * a (n - 4) := by
  have hn2 : 6 ≤ n - 2 := by omega
  have hn4 : 6 ≤ n - 4 := by omega
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · rw [even_formula hdiag n (by omega) (Nat.even_iff.mpr he),
      even_formula hdiag (n - 2) hn2 (Nat.even_iff.mpr (by omega)),
      even_formula hdiag (n - 4) hn4 (Nat.even_iff.mpr (by omega))]
    have h1 : n - 1 = (n - 4 - 1) + 4 := by omega
    have h2 : n - 2 - 1 = (n - 4 - 1) + 2 := by omega
    rw [h1, h2, pow_add, pow_add]
    ring
  · rw [odd_formula hdiag n (by omega) (Nat.odd_iff.mpr ho),
      odd_formula hdiag (n - 2) hn2 (Nat.odd_iff.mpr (by omega)),
      odd_formula hdiag (n - 4) hn4 (Nat.odd_iff.mpr (by omega))]
    have hp : (10 : ℚ) ^ n = 10 ^ (n - 4) * 10 ^ 4 := by
      rw [← pow_add]
      congr 1
      omega
    have hp2 : (10 : ℚ) ^ (n - 2) = 10 ^ (n - 4) * 10 ^ 2 := by
      rw [← pow_add]
      congr 1
      omega
    rw [hp, hp2]
    ring

lemma coeff_mk_mul_monomial (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then f (n - k) * c else 0 := by
  rw [← mul_assoc, coeff_mul_X_pow']
  split_ifs with h
  · rw [coeff_mul_C, coeff_mk]
  · rfl

lemma denominator_expansion :
    ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) : PowerSeries ℚ) =
      C 1 * X ^ 0 + C (-101) * X ^ 2 + C 100 * X ^ 4 := by
  simp only [map_one, map_neg, map_ofNat]
  ring

lemma numerator_expansion :
    (1 + X - 101 * X ^ 2 + 10 * X ^ 3 + 11100 * X ^ 4 - 11000 * X ^ 6 -
      1000000 * X ^ 7 + 1000000 * X ^ 9 : PowerSeries ℚ) =
      C 1 * X ^ 0 + C 1 * X ^ 1 + C (-101) * X ^ 2 + C 10 * X ^ 3 +
      C 11100 * X ^ 4 + C (-11000) * X ^ 6 + C (-1000000) * X ^ 7 +
      C 1000000 * X ^ 9 := by
  simp only [map_one, map_neg, map_ofNat]
  ring

lemma generating_function (hdiag : Diagonal) :
    mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X)) =
      1 + X - 101 * X ^ 2 + 10 * X ^ 3 + 11100 * X ^ 4 - 11000 * X ^ 6 -
      1000000 * X ^ 7 + 1000000 * X ^ 9 := by
  rw [denominator_expansion, numerator_expansion]
  ext n
  simp only [mul_add, map_add, coeff_mk_mul_monomial, coeff_C_mul_X_pow]
  by_cases hn : 10 ≤ n
  · have h := recurrence hdiag n hn
    simp (disch := omega) only [if_pos, if_neg]
    simp only [Nat.sub_zero]
    linarith
  · rcases initial with ⟨h0, h1, h2, h3, h4, h5⟩
    have h6 := even_formula hdiag 6 (by omega) (by decide)
    have h7 := odd_formula hdiag 7 (by omega) (by decide)
    have h8 := even_formula hdiag 8 (by omega) (by decide)
    have h9 := odd_formula hdiag 9 (by omega) (by decide)
    norm_num at h6 h7 h8 h9
    interval_cases n <;> norm_num [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]

lemma solution_of_diagonal (hdiag : Diagonal) : type_of% @OMA.S_oeis_a287130.main := by
  exact ⟨generating_function hdiag, even_formula hdiag, odd_formula hdiag⟩

end A287130Algebra

-- Component: A287130Finish

theorem OMA.solution : type_of% @OMA.S_oeis_a287130.main :=
  A287130Algebra.solution_of_diagonal A287130Proof.diagonal
