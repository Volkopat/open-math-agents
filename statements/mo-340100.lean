import Mathlib

/-!
# Counting cycles with bounded interleaving

Source: H. A. Helfgott, https://mathoverflow.net/questions/340100 (CC BY-SA 4.0).
Credit: @connoranderson. The argument uses exposed edges across successive prefix cuts.

There are n+1 distinct labels. A rooted word gives the orbit position of each label,
with label zero at position zero. Thus each directed cycle is represented once.
The interleaving is the largest number of ordinary integer runs among the labels
in a cyclic interval of orbit positions. The question and comments allow either
endpoint convention; this formulation counts the largest label as a run end.

The candidate enumeration decodes pairs of bounded column and row ranks, then checks
the resulting words. Its search space is exponential in the number of labels for fixed r.
An explicit family with at most three runs supplies an exponential lower bound on odd lengths.
-/

namespace OMA.S_mo_340100
open Finset

abbrev Pos (n : ℕ) := Fin (n+1)
abbrev Word (n : ℕ) := Pos n → Pos n
abbrev Board (n : ℕ) := Pos n → Pos n → Bool
abbrev Code (n r : ℕ) := Pos n → Fin (r+2) × Fin (r+2)

/-- Stored positions are measured from the least label in the directed cycle. -/
def rooted {n : ℕ} (w : Word n) : Prop := w 0 = 0 ∧ Function.Bijective w
instance {n} (w : Word n) : Decidable (rooted w) := by unfold rooted; infer_instance

def initial (n k : ℕ) : Finset (Pos n) := univ.filter fun i => i.val < k
def arc {n : ℕ} (a : Pos n) (k : ℕ) : Finset (Pos n) := (initial n k).image (fun i => a+i)

/-- Use the literal convention that the largest label has no successor in the line. -/
def runs {n : ℕ} (s : Finset (Pos n)) : ℕ :=
  (s.filter (fun i => i.val=n ∨ i+1∉s)).card

def interleaving {n : ℕ} (w : Word n) : ℕ := univ.sup (fun a : Pos n =>
  (range (n+2)).sup fun k => runs (univ.filter (fun i => w i ∈ arc a k)))

def eligible (n r : ℕ) : Finset (Word n) :=
  univ.filter fun w => rooted w ∧ interleaving w ≤ r
def exactCount (n d : ℕ) : ℕ :=
  (univ.filter (fun w : Word n => rooted w ∧ interleaving w = d)).card

/-- Columns of the exposed k by k square whose matching row is still unseen. -/
def gaps {n : ℕ} (B : Board n) (k : ℕ) : Finset (Pos n) :=
  (initial n k).filter fun j => ∀ i ∈ initial n k, B i j = false

/-- Ranks 0 and 1 mark a diagonal match and a match beyond the frontier.
    Ranks starting at 2 mark an earlier unused index in increasing order. -/
def rankMatch {n : ℕ} (g : Finset (Pos n)) (j : Pos n) (a : ℕ) : Bool :=
  decide (j ∈ g ∧ a = (g.sort.idxOf j)+2)

def expose {n r : ℕ} (c : Code n r) : ℕ → Board n
  | 0 => fun _ _ => false
  | k+1 => fun i j =>
    let B := expose c k
    if i.val=k ∧ j.val=k then decide ((c i).1.val=0)
    else if i.val=k ∧ j.val<k then rankMatch (gaps B k) j (c i).1.val
    else if j.val=k ∧ i.val<k then rankMatch (gaps (fun x y => B y x) k) i (c j).2.val
    else B i j

def nextOn {n : ℕ} (B : Board n) (i : Pos n) : Pos n :=
  ((univ.filter (fun j => B i j = true)).min).getD 0

def recover {n r : ℕ} (c : Code n r) : Word n :=
  fun j => (nextOn (expose c (n+1)))^[j.val] 0

def candidates (n r : ℕ) : Finset (Word n) :=
  (univ.image (recover (n:=n) (r:=r))).filter (fun w => rooted w ∧ interleaving w ≤ r)

theorem main : (∀ n r : ℕ,
    eligible n r = candidates n r ∧
    (eligible n r).card ≤ (r+2)^(2*(n+1)) ∧
    exactCount n (r+1) = (eligible n (r+1)).card - (eligible n r).card) ∧
    (∀ (r : ℕ) (C : ℝ), 0 ≤ C → Filter.Tendsto
      (fun n : ℕ => C^n*((eligible n r).card:ℝ)/(n.factorial:ℝ)) Filter.atTop (nhds 0)) ∧
    (∀ m : ℕ, 2^m ≤ (eligible (2*m) 3).card) := by
  sorry

end OMA.S_mo_340100
