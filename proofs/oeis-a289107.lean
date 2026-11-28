import OMAStatements.S_oeis_a289107
import Mathlib

/-!
Kimberling's replacement rule is a transducer with one pending bit. The table
below records both pending bits in two successive passes and the accumulated
difference (second output length minus first output length minus input length).
Its edge identities, terminal values, and closure under rewriting are finite
claims checked in the kernel. Induction on a word then proves the length
identity for every word accepted by the table.
-/

namespace BinaryLengths
open OMA.S_oeis_a289107

abbrev Buffer := Option Bool

def tick : Buffer → Bool → Buffer × List Bool
  | none, b => (some b, [])
  | some false, false => (none, [false,false,true,false])
  | some false, true => (none, [false,true,true])
  | some true, false => (none, [false,false,false])
  | some true, true => (some true, [true])

def advance (p : Buffer) : List Bool → Buffer
  | [] => p
  | b::w => advance (tick p b).1 w

def emit (p : Buffer) : List Bool → List Bool
  | [] => []
  | b::w => (tick p b).2 ++ emit (tick p b).1 w

def pass (p : Buffer) : List Bool → List Bool
  | [] => p.toList
  | b::w => (tick p b).2 ++ pass (tick p b).1 w

lemma pass_append (p : Buffer) (u v : List Bool) :
    pass p (u++v) = emit p u ++ pass (advance p u) v := by
  induction u generalizing p with
  | nil => rfl
  | cons b u ih => simp only [List.cons_append,pass,emit,advance,ih,List.append_assoc]

lemma pass_rule (w : List Bool) :
    pass none w = rewrite w ∧ ∀ b, pass (some b) w = rewrite (b::w) := by
  induction w with
  | nil =>
    constructor
    · rfl
    · intro b; cases b <;> rfl
  | cons b w ih =>
    constructor
    · exact ih.2 b
    · intro c
      cases c <;> cases b <;> simp [pass,tick,rewrite,ih.1,ih.2]

abbrev State := Fin 16

structure Vertex where
  first : Buffer
  second : Buffer
  balance : ℤ
  onZero : Option State
  onOne : Option State

def info : State → Vertex :=
  ![
    ⟨none, none, 0, some 1, none⟩,
    ⟨some false, none, -1, some 2, none⟩,
    ⟨none, none, 1, none, some 3⟩,
    ⟨some true, none, 0, some 4, none⟩,
    ⟨none, some false, 0, some 5, none⟩,
    ⟨some false, some false, -1, some 6, none⟩,
    ⟨none, some false, 1, some 7, none⟩,
    ⟨some false, some false, 0, some 8, some 9⟩,
    ⟨none, some false, 2, some 10, some 11⟩,
    ⟨none, some true, 1, some 12, none⟩,
    ⟨some false, some false, 1, none, some 13⟩,
    ⟨some true, some false, 1, none, some 14⟩,
    ⟨some false, some true, 0, some 6, none⟩,
    ⟨none, some true, 2, some 15, none⟩,
    ⟨some true, none, 2, some 8, none⟩,
    ⟨some false, some true, 1, some 8, some 9⟩]


def edge (q : State) (b : Bool) : Option State :=
  if b then (info q).onOne else (info q).onZero

def walk (s : Option State) (w : List Bool) : Option State :=
  w.foldl (fun t b => t.bind (fun q => edge q b)) s

lemma gone (w : List Bool) : walk none w = none := by
  induction w with
  | nil => rfl
  | cons b w ih => exact ih

lemma walk_append (s : Option State) (u v : List Bool) :
    walk s (u++v) = walk (walk s u) v := by simp only [walk,List.foldl_append]

def terminal (q : State) : Bool := decide (q=7 ∨ q=8 ∨ q=15)
def accepting : Option State → Bool
  | none => false
  | some q => terminal q

def partners : State → List State :=
  ![[0], [0], [4], [4], [7], [7], [15], [15], [15, 7], [14], [15, 7], [15, 7], [14], [14], [9], [14]]


def edgeBalance (q : State) (b : Bool) : Bool :=
  match edge q b with
  | none => true
  | some t =>
    let out := (tick (info q).first b).2
    decide ((tick (info q).first b).1 = (info t).first ∧
      advance (info q).second out = (info t).second ∧
      (info t).balance = (info q).balance + (emit (info q).second out).length -
        (out.length : ℤ) - 1)

lemma checkedBalance : ∀ (q : State) (b : Bool), edgeBalance q b = true := by decide

lemma edgeCheck : ∀ (q : State) (b : Bool),
    match edge q b with
    | none => True
    | some t =>
      let out := (tick (info q).first b).2
      (tick (info q).first b).1 = (info t).first ∧
      advance (info q).second out = (info t).second ∧
      (info t).balance = (info q).balance + (emit (info q).second out).length -
        (out.length : ℤ) - 1 := by
  intro q b
  cases h : edge q b with
  | none => trivial
  | some t => simpa only [edgeBalance,h,decide_eq_true_eq] using checkedBalance q b

def coupled (q r : State) (b : Bool) : Bool :=
  match edge q b with
  | none => true
  | some t =>
    match walk (some r) (tick (info q).first b).2 with
    | none => false
    | some u => decide (u ∈ partners t)

lemma checkedPairs : ∀ (q r : State) (b : Bool), r ∈ partners q →
    coupled q r b = true := by decide

lemma pairCheck : ∀ (q r : State) (b : Bool), r ∈ partners q →
    match edge q b with
    | none => True
    | some t =>
      match walk (some r) (tick (info q).first b).2 with
      | none => False
      | some u => u ∈ partners t := by
  intro q r b hr
  have hc := checkedPairs q r b hr
  cases h : edge q b with
  | none => trivial
  | some t =>
    cases hy : walk (some r) (tick (info q).first b).2 with
    | none => simp [coupled,h,hy] at hc
    | some u => simpa only [coupled,h,hy,decide_eq_true_eq] using hc

lemma finalPair : ∀ (q r : State), r ∈ partners q → terminal q = true →
    accepting (walk (some r) (info q).first.toList) = true := by decide

lemma finalCount : ∀ (q : State), terminal q = true →
    ((pass (info q).second (info q).first.toList).length : ℤ) -
      (info q).first.toList.length + (info q).balance = 3 := by decide

theorem preserved (w : List Bool) (q r : State) (hr : r ∈ partners q)
    (old : accepting (walk (some q) w) = true) :
    accepting (walk (some r) (pass (info q).first w)) = true := by
  induction w generalizing q r with
  | nil => exact finalPair q r hr old
  | cons b w ih =>
    change accepting (walk (edge q b) w) = true at old
    cases h : edge q b with
    | none => simp [h, gone, accepting] at old
    | some t =>
      rw [h] at old
      have ce := edgeCheck q b
      have cp := pairCheck q r b hr
      rw [h] at ce cp
      cases hy : walk (some r) (tick (info q).first b).2 with
      | none => rw [hy] at cp; exact cp.elim
      | some u =>
        rw [hy] at cp
        rw [pass,walk_append,hy,ce.1]
        exact ih t u cp old

theorem lengthBalance (w : List Bool) (q : State)
    (hw : accepting (walk (some q) w) = true) :
    ((pass (info q).second (pass (info q).first w)).length : ℤ) -
        (pass (info q).first w).length - w.length + (info q).balance = 3 := by
  induction w generalizing q with
  | nil => simpa only [pass,List.length_nil, Nat.cast_zero, sub_zero] using finalCount q hw
  | cons b w ih =>
    change accepting (walk (edge q b) w) = true at hw
    cases h : edge q b with
    | none => simp [h,gone,accepting] at hw
    | some t =>
      rw [h] at hw
      have ce := edgeCheck q b
      rw [h] at ce
      have hi := ih t hw
      rw [pass,pass_append,ce.1,ce.2.1]
      simp only [List.length_append, List.length_cons, Nat.cast_add, Nat.cast_one]
      have balance := ce.2.2
      omega

def good (w : List Bool) : Prop := accepting (walk (some 0) w) = true

lemma iterates (k : ℕ) : good (word (k+2)) := by
  induction k with
  | zero => unfold good; decide
  | succ k ih =>
    change good (rewrite (word (k+2)))
    have h := preserved (word (k+2)) 0 0 (by decide) ih
    change good (pass none (word (k+2))) at h
    rwa [(pass_rule _).1] at h

lemma successive (k : ℕ) :
    ((word (k+4)).length : ℤ) = (word (k+3)).length + (word (k+2)).length + 3 := by
  have h := lengthBalance (word (k+2)) 0 (iterates k)
  change ((pass none (pass none (word (k+2)))).length : ℤ) -
    (pass none (word (k+2))).length - (word (k+2)).length + 0 = 3 at h
  simp only [(pass_rule _).1, add_zero] at h
  change ((rewrite (rewrite (word (k+2)))).length : ℤ) =
    (rewrite (word (k+2))).length + (word (k+2)).length + 3
  omega

theorem lengths (n : ℕ) : ((word n).length : ℤ) = reference n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | 3 => decide
    | 4 => decide
    | k+5 =>
      rw [reference, ← ih (k+4) (by omega), ← ih (k+2) (by omega)]
      have h := successive k
      have g := successive (k+1)
      rw [show k+1+4=k+5 by omega, show k+1+3=k+4 by omega,
        show k+1+2=k+3 by omega] at g
      omega

end BinaryLengths

theorem OMA.solution : type_of% @OMA.S_oeis_a289107.main := BinaryLengths.lengths
