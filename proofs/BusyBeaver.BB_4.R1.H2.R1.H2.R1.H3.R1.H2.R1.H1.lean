/- Component: both later writes are zero and the return state is two or three.
This is one family within the four-state initial-sweep bound. -/
import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H2_R1

/-!

New certificate construction and assembly: Hanan Beer (@hananzlt).
The generic finite-automata verifier is reused from James Halldon (@Halldon),
merged PR1292. The tape-reader soundness lemmas and target reduction are by
@marcusbuffett (PR4876 and PR4509). Their attribution is retained.
The untrusted certificate search follows the direct FAR and n-gram CPS methods
from bbchallenge. Every resulting certificate is checked by Lean.

The following verifier originally established the three-state upper bound.

That original search branches on the first unassigned transition in 21 steps.
The present four-state application uses the first unassigned transition in
107 steps. The new bit-mask tests imply the original verifier checks. Nonhalting leaves use finite-automata reduction: a DFA summarizes
one half of the tape and an NFA recognizes a superset of configurations that
can reach an unassigned transition. The NFA excludes the entirely blank tape.
See Blanchard et al., *Determination of the fifth Busy Beaver value*, for the
finite-automata reduction method. Every certificate is checked by Lean.
-/

namespace BeaverBound

open Turing Turing.BusyBeaver

abbrev Symbol := Fin 2
abbrev Key (n : ℕ) := Fin n × Symbol
abbrev MachineOf (n : ℕ) [NeZero n] := Machine Symbol (Fin n)

structure Move (n : ℕ) where
  state : Fin n
  write : Symbol
  left : Bool
  deriving DecidableEq

structure Position (n : ℕ) where
  state : Fin n
  ls : List Symbol
  head : Symbol
  rs : List Symbol
  deriving DecidableEq

def start (n : ℕ) [NeZero n] : Position n := ⟨0, [], 0, []⟩

def push (a : Symbol) (xs : List Symbol) : List Symbol :=
  if a = 0 ∧ xs = [] then [] else a :: xs

def Position.move (c : Position n) (m : Move n) : Position n :=
  if m.left then ⟨m.state, c.ls.tail, c.ls.headI, push m.write c.rs⟩
  else ⟨m.state, push m.write c.ls, c.rs.headI, c.rs.tail⟩

def Move.flip (m : Move n) : Move n := { m with left := !m.left }

def Position.flip (c : Position n) : Position n := ⟨c.state, c.rs, c.head, c.ls⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem flip_move (c : Position n) (m : Move n) :
    (c.move m).flip = c.flip.move m.flip := by
  cases m with
  | mk q a d => cases d <;> rfl

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem mk_push (a : Symbol) (xs : List Symbol) :
    ListBlank.mk (push a xs) = (ListBlank.mk xs).cons a := by
  unfold push
  split
  · rename_i h
    rcases h with ⟨rfl, rfl⟩
    exact (ListBlank.cons_head_tail (ListBlank.mk ([] : List Symbol))).symm
  · exact (ListBlank.cons_mk a xs).symm

def Position.view [NeZero n] (c : Position n) : Cfg Symbol (Fin n) :=
  ⟨some c.state, ⟨c.head, ListBlank.mk c.ls, ListBlank.mk c.rs⟩⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem view_start (n : ℕ) [NeZero n] : (start n).view = Machine.init [] := rfl

def Move.command (m : Move n) : Option (Option (Fin n) × Stmt Symbol) :=
  some (some m.state, Stmt.write m.write (if m.left then Dir.left else Dir.right))

def ongoing [NeZero n] (M : MachineOf n) (k : Key n) : Option (Move n) :=
  match M k.1 k.2 with
  | some (some q, ⟨b, .left⟩) => some ⟨q, b, true⟩
  | some (some q, ⟨b, .right⟩) => some ⟨q, b, false⟩
  | _ => none

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem ongoing_command [NeZero n] (M : MachineOf n) (k : Key n) (m : Move n)
    (h : ongoing M k = some m) : M k.1 k.2 = m.command := by
  rcases m with ⟨q, a, d⟩
  unfold ongoing at h
  split at h <;> simp_all [Move.command, Move.mk.injEq]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem step_move [NeZero n] (M : MachineOf n) (c : Position n) (m : Move n)
    (h : ongoing M (c.state, c.head) = some m) :
    M.step c.view = some (c.move m).view := by
  have he := ongoing_command M (c.state, c.head) m h
  change M c.state c.head = m.command at he
  cases m with
  | mk q a d =>
    cases d <;> simp [Position.view, Machine.step, he, Move.command, Position.move,
      Tape.write, Tape.move, mk_push]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem step_stop [NeZero n] (M : MachineOf n) (c : Position n)
    (h : ongoing M (c.state, c.head) = none) : M.HaltsAfter c.view 1 := by
  unfold ongoing at h
  split at h
  all_goals try contradiction
  cases hc : M c.state c.head with
  | none => simp [Machine.HaltsAfter, Machine.multiStep_succ, Position.view, Machine.step, hc]
  | some pair =>
    obtain ⟨q, b, d⟩ := pair
    cases q with
    | none => simp [Machine.HaltsAfter, Machine.multiStep_succ, Position.view, Machine.step, hc]
    | some q => cases d <;> simp_all

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem multi_succ_front [NeZero n] (M : MachineOf n) (c : Cfg Symbol (Fin n)) (k : ℕ) :
    M.multiStep c (k+1) = (M.step c).bind (fun c' => M.multiStep c' k) := by
  induction k with
  | zero => rw [Machine.multiStep_one]; cases M.step c <;> rfl
  | succ k ih =>
    rw [Machine.multiStep_succ, ih]
    cases h : M.step c with
    | none => rfl
    | some d => simp [Machine.multiStep_succ]

abbrev Program (n : ℕ) := List (Key n × Move n)

def Program.get : Program n → Key n → Option (Move n)
  | [], _ => none
  | (a, m) :: rest, k => if k = a then some m else Program.get rest k

def Program.flip (tb : Program n) : Program n := tb.map fun (k, m) => (k, m.flip)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem get_flip (tb : Program n) (k : Key n) : tb.flip.get k = (tb.get k).map Move.flip := by
  induction tb with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨k', m⟩ := x
    by_cases h : k = k' <;> simp [Program.flip, Program.get, h] at ih ⊢
    exact ih

inductive CanStop (tb : Program n) : Position n → Prop
  | missing {c} : tb.get (c.state, c.head) = none → CanStop tb c
  | move {c m} : tb.get (c.state, c.head) = some m → CanStop tb (c.move m) → CanStop tb c

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem canStop_flip {tb : Program n} {c : Position n} (h : CanStop tb c) :
    CanStop tb.flip c.flip := by
  induction h with
  | missing h => exact .missing (by simpa [Position.flip, get_flip] using h)
  | @move c m h _ ih =>
    refine .move (m := m.flip) ?_ ?_
    · change tb.flip.get (c.state, c.head) = some m.flip
      simp [get_flip, h]
    · rwa [← flip_move]

def Matches [NeZero n] (M : MachineOf n) (tb : Program n) : Prop :=
  ∀ k m, tb.get k = some m → ongoing M k = some m

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem matches_empty [NeZero n] (M : MachineOf n) : Matches M [] := by
  intro k m h
  contradiction

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem matches_add [NeZero n] {M : MachineOf n} {tb : Program n} {k : Key n} {m : Move n}
    (hm : Matches M tb) (h : ongoing M k = some m) : Matches M ((k, m) :: tb) := by
  intro k' m' hh
  by_cases e : k' = k
  · subst k'
    simp [Program.get] at hh
    simpa [← hh] using h
  · apply hm k' m'
    simpa [Program.get, e] using hh

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cannot_stop_run [NeZero n] {M : MachineOf n} {tb : Program n}
    (hm : Matches M tb) (c : Position n) (hc : ¬ CanStop tb c) (k : ℕ) :
    M.multiStep c.view k ≠ none := by
  induction k generalizing c with
  | zero => simp
  | succ k ih =>
    cases h : tb.get (c.state, c.head) with
    | none => exact (hc (.missing h)).elim
    | some m =>
      rw [multi_succ_front, step_move M c m (hm _ _ h), Option.bind_some]
      exact ih _ (fun hs => hc (.move h hs))

end BeaverBound


namespace BeaverBound

open Turing Turing.BusyBeaver

-- A DFA reads a left half-tape from the far end toward the head. Its initial
-- state is fixed by the blank symbol, so appending blank cells changes nothing.
structure TapeDFA where
  extraStates : ℕ
  code : ℕ

abbrev TapeDFA.size (D : TapeDFA) : ℕ := D.extraStates + 1

def TapeDFA.next (D : TapeDFA) (a : Symbol) (l : Fin D.size) : Fin D.size :=
  ⟨(D.code * D.size / D.size ^ (2 * l.val + a.val)) % D.size,
    Nat.mod_lt _ (Nat.succ_pos _)⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem TapeDFA.blank (D : TapeDFA) : D.next 0 0 = 0 := by
  apply Fin.ext
  simp [TapeDFA.next]

def TapeDFA.read (D : TapeDFA) (xs : List Symbol) : Fin D.size :=
  xs.foldr D.next 0

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem TapeDFA.read_push (D : TapeDFA) (a : Symbol) (xs : List Symbol) :
    D.read (push a xs) = D.next a (D.read xs) := by
  unfold push
  split
  · rename_i h
    rcases h with ⟨rfl, rfl⟩
    exact D.blank.symm
  · rfl

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem TapeDFA.read_pop (D : TapeDFA) (xs : List Symbol) :
    D.next xs.headI (D.read xs.tail) = D.read xs := by
  cases xs
  · exact D.blank
  · rfl

-- Each NFA state records a control state and a left DFA state. The extra state
-- is accepting. The NFA reads the other half of the tape, starting at the head.
structure Certificate (n : ℕ) where
  mirror : Bool
  dfa : TapeDFA
  edges : ℕ
  blankReach : ℕ

abbrev Node (cert : Certificate n) := Option (Fin n × Fin cert.dfa.size)

def nodeId (cert : Certificate n) : Node cert → ℕ
  | none => n * cert.dfa.size
  | some (q, l) => q.val * cert.dfa.size + l.val

def Certificate.edge (cert : Certificate n) (p : Node cert) (a : Symbol)
    (q : Node cert) : Bool :=
  match p with
  | none => q.isNone
  | some _ => cert.edges.testBit ((2 * nodeId cert p + a.val) *
      (n * cert.dfa.size + 1) + nodeId cert q)

def Certificate.onBlank (cert : Certificate n) (p : Node cert) : Bool :=
  cert.blankReach.testBit (nodeId cert p)

def unpack (n val : ℕ) : Certificate n :=
  let extra := val / 2 % 8
  let size := extra + 1
  let dfaBase := size ^ (2 * size - 1)
  let payload := val / 16 / dfaBase
  let width := n * size + 1
  let initialBase := 2 ^ width
  ⟨val % 2 == 1, ⟨extra, val / 16 % dfaBase⟩, payload / initialBase, payload % initialBase⟩

def nodes (cert : Certificate n) : List (Node cert) :=
  none :: (List.finRange n).flatMap fun q =>
    (List.finRange cert.dfa.size).map fun l => some (q, l)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem allFin {n : ℕ} {p : Fin n → Bool} (h : (List.finRange n).all p = true)
    (a : Fin n) : p a = true := (List.all_eq_true.mp h) a (by simp)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem allNodes {cert : Certificate n} {p : Node cert → Bool}
    (h : (nodes cert).all p = true) (a : Node cert) : p a = true := by
  refine (List.all_eq_true.mp h) a ?_
  rcases a with _ | ⟨q, l⟩
  · simp [nodes]
  · simp [nodes]

def checkBlank (cert : Certificate n) [NeZero n] : Bool :=
  cert.onBlank (some (0, 0)) && !cert.onBlank none &&
    (nodes cert).all (fun p => if cert.onBlank p then
      (nodes cert).all fun q => !cert.edge p 0 q || cert.onBlank q
    else true)

def checkAt (tb : Program n) (cert : Certificate n) (q : Fin n) (a : Symbol)
    (l : Fin cert.dfa.size) : Bool :=
  let p : Node cert := some (q, l)
  match tb.get (q, a) with
  | none => cert.edge p a none
  | some m =>
    if m.left then
      (List.finRange cert.dfa.size).all fun l' => (List.finRange 2).all fun a' =>
        if cert.dfa.next a' l' = l then
          (nodes cert).all fun s => if cert.edge (some (m.state, l')) a' s then
            (nodes cert).all fun t => !cert.edge s m.write t || cert.edge p a t
          else true
        else true
    else cert.edge p a (some (m.state, cert.dfa.next m.write l))

def checkMachine (tb : Program n) (cert : Certificate n) : Bool :=
  (List.finRange n).all fun q => (List.finRange 2).all fun a =>
    (List.finRange cert.dfa.size).all fun l => checkAt tb cert q a l

inductive Reads (cert : Certificate n) : Node cert → ListBlank Symbol → Prop
  | done (t) : Reads cert none t
  | step {p q t} : cert.edge p t.head q = true → Reads cert q t.tail → Reads cert p t

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem Reads.push {cert : Certificate n} {p q : Node cert} {a : Symbol} {xs : ListBlank Symbol}
    (he : cert.edge p a q = true) (h : Reads cert q xs) : Reads cert p (xs.cons a) :=
  .step (by simpa using he) (by simpa using h)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem Reads.pop {cert : Certificate n} {p : Node cert} {xs : ListBlank Symbol} {a : Symbol}
    (h : Reads cert p (xs.cons a)) : ∃ q, cert.edge p a q = true ∧ Reads cert q xs := by
  cases h with
  | done => exact ⟨none, rfl, .done _⟩
  | step he hr => exact ⟨_, by simpa using he, by simpa using hr⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem no_read_blank [NeZero n] {cert : Certificate n} (hb : checkBlank cert = true) :
    ¬ Reads cert (some (0, 0)) (ListBlank.mk []) := by
  simp only [checkBlank, Bool.and_eq_true_iff, Bool.not_eq_true_eq_eq_false] at hb
  obtain ⟨⟨hstart, hsink⟩, hclosure⟩ := hb
  have each {p : Node cert} {t : ListBlank Symbol} (hr : Reads cert p t) :
      t = ListBlank.mk [] → cert.onBlank p = true → False := by
    induction hr with
    | done _ => intro _ hp; exact Bool.noConfusion (hp.symm.trans hsink)
    | @step p q t he _ ih =>
      rintro rfl hp
      have ht := allNodes hclosure p
      simp only [hp, if_true] at ht
      have hn := allNodes ht q
      have he0 : cert.edge p 0 q = true := he
      simp [he0] at hn
      exact ih rfl hn
  exact fun hr => each hr rfl hstart

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem reads_of_canStop {tb : Program n} {cert : Certificate n} (hchk : checkMachine tb cert = true)
    {c : Position n} (hs : CanStop tb c) :
    Reads cert (some (c.state, cert.dfa.read c.ls)) ((ListBlank.mk c.rs).cons c.head) := by
  induction hs with
  | @missing c hh =>
    have h := allFin (allFin (allFin hchk c.state) c.head) (cert.dfa.read c.ls)
    rw [checkAt, hh] at h
    exact Reads.push h (.done _)
  | @move c m hh _ ih =>
    have h := allFin (allFin (allFin hchk c.state) c.head) (cert.dfa.read c.ls)
    rw [checkAt, hh] at h
    cases hd : m.left with
    | false =>
      have hstep : cert.edge (some (c.state, cert.dfa.read c.ls)) c.head
          (some (m.state, cert.dfa.next m.write (cert.dfa.read c.ls))) = true := by
        simpa [hd] using h
      refine Reads.push hstep ?_
      simpa [Position.move, hd, TapeDFA.read_push, ← ListBlank.head_mk, ← ListBlank.tail_mk]
        using ih
    | true =>
      have hr : Reads cert (some (m.state, cert.dfa.read c.ls.tail))
          (((ListBlank.mk c.rs).cons m.write).cons c.ls.headI) := by
        simpa [Position.move, hd, mk_push] using ih
      obtain ⟨s, he, hr⟩ := Reads.pop hr
      obtain ⟨t, hf, ht⟩ := Reads.pop hr
      simp only [hd, if_true] at h
      have h' := allFin (allFin h (cert.dfa.read c.ls.tail)) c.ls.headI
      simp only [TapeDFA.read_pop, if_true] at h'
      have h'' := allNodes h' s
      simp only [he, if_true] at h''
      have h''' := allNodes h'' t
      simp [hf] at h'''
      exact Reads.push h''' ht

def checkCertificate [NeZero n] (tb : Program n) (val : ℕ) : Bool :=
  let C := unpack n val
  checkBlank C && checkMachine (if C.mirror then tb.flip else tb) C

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem certificate_sound [NeZero n] {tb : Program n} {val : ℕ}
    (h : checkCertificate tb val = true) : ¬ CanStop tb (start n) := by
  intro hs
  unfold checkCertificate at h
  have ⟨hb, hm⟩ := Bool.and_eq_true_iff.mp h
  apply no_read_blank hb
  have blank : (ListBlank.mk ([] : List Symbol)).cons 0 = ListBlank.mk [] :=
    ListBlank.cons_head_tail (ListBlank.mk [])
  split at hm
  · simpa only [Position.flip, start, TapeDFA.read, List.foldr_nil, blank] using
      (reads_of_canStop hm (canStop_flip hs))
  · simpa only [start, TapeDFA.read, List.foldr_nil, blank] using (reads_of_canStop hm hs)

end BeaverBound

namespace BeaverBound

open Turing Turing.BusyBeaver

def firstMissing (tb : Program n) : ℕ → Position n → Option (Key n)
  | 0, _ => none
  | fuel + 1, c =>
    match tb.get (c.state, c.head) with
    | none => some (c.state, c.head)
    | some m => firstMissing tb fuel (c.move m)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem firstMissing_stops [NeZero n] {M : MachineOf n} {tb : Program n}
    (hm : Matches M tb) (fuel : ℕ) (c : Position n) {k : Key n}
    (h : firstMissing tb fuel c = some k) (halt : ongoing M k = none) : M.HaltsAfter c.view fuel := by
  induction fuel generalizing c with
  | zero => simp [firstMissing] at h
  | succ fuel ih =>
    cases ht : tb.get (c.state, c.head) with
    | none =>
      simp [firstMissing, ht] at h
      subst k
      exact Machine.multiStep_eq_none_mono (step_stop M c halt) (by omega)
    | some m =>
      have htail : firstMissing tb fuel (c.move m) = some k := by
        simpa [firstMissing, ht] using h
      unfold Machine.HaltsAfter
      rw [multi_succ_front, step_move M c m (hm _ _ ht), Option.bind_some]
      exact ih _ htail

def holes (tb : Program n) : Finset (Key n) :=
  Finset.univ.filter fun k => tb.get k = none

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem missing_is_hole {tb : Program n} {c : Position n} {k : Key n} {fuel : ℕ}
    (h : firstMissing tb fuel c = some k) : k ∈ holes tb := by
  induction fuel generalizing c with
  | zero => simp [firstMissing] at h
  | succ fuel ih =>
    cases he : tb.get (c.state, c.head) with
    | none =>
      simp [firstMissing, he] at h
      subst k
      simp [holes, he]
    | some m =>
      exact ih (by simpa [firstMissing, he] using h)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem holes_add (tb : Program n) (k : Key n) (m : Move n) :
    holes ((k, m) :: tb) = (holes tb).erase k := by
  ext k'
  simp only [holes, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  rw [Program.get]
  by_cases e : k' = k <;> simp [e]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem no_holes_cannot_stop {tb : Program n} (h : (holes tb).card = 0) {c : Position n} :
    ¬ CanStop tb c := by
  intro hs
  induction hs with
  | @missing c hm =>
    have he : (c.state, c.head) ∈ holes tb := by simp [holes, hm]
    have := Finset.card_pos.mpr ⟨_, he⟩
    omega
  | move _ _ ih => exact ih

def moves (n : ℕ) : List (Move n) := (List.finRange n).flatMap fun q =>
  (List.finRange 2).flatMap fun a => [⟨q, a, false⟩, ⟨q, a, true⟩]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem mem_moves (m : Move n) : m ∈ moves n := by
  obtain ⟨q, a, d⟩ := m
  rw [moves, List.mem_flatMap]
  refine ⟨q, by simp, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨a, by simp, ?_⟩
  cases d <;> simp

def checkTree [NeZero n] (limit : ℕ) : ℕ → Program n → List ℕ → Option (List ℕ)
  | 0, _, certs => some certs
  | fuel + 1, tb, certs =>
    match firstMissing tb limit (start n) with
    | none => match certs with
      | [] => none
      | v :: rest => if checkCertificate tb v then some rest else none
    | some k => (moves n).foldlM (fun rest m => checkTree limit fuel ((k, m) :: tb) rest) certs

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem succeeds_each {α β : Type*} {items : List α} {f : β → α → Option β}
    {a b : β} (h : items.foldlM f a = some b) {i : α} (hi : i ∈ items) :
    ∃ x y, f x i = some y := by
  induction items generalizing a with
  | nil => simp at hi
  | cons head tail ih =>
    rw [List.foldlM_cons] at h
    cases hh : f a head with
    | none => simp [hh] at h
    | some mid =>
      simp only [hh] at h
      rcases List.mem_cons.mp hi with rfl | ht
      · exact ⟨_, _, hh⟩
      · exact ih h ht

def Upper [NeZero n] (M : MachineOf n) (limit : ℕ) : Prop :=
  M.HaltsAfter (Machine.init []) limit ∨ ¬ M.IsHalting

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem upper_cannot_stop [NeZero n] {M : MachineOf n} {tb : Program n} {limit : ℕ}
    (hm : Matches M tb) (h : ¬ CanStop tb (start n)) : Upper M limit := by
  right
  intro halts
  obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp halts
  apply cannot_stop_run hm (start n) h (k + 1)
  rwa [view_start]

abbrev TreeBound [NeZero n] (limit : ℕ) (tb : Program n) : Prop :=
  ∀ M : MachineOf n, Matches M tb → Upper M limit

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem branch_bound [NeZero n] {limit : ℕ} {tb : Program n} {k : Key n}
    (h : firstMissing tb limit (start n) = some k)
    (children : ∀ m, TreeBound limit ((k, m) :: tb)) : TreeBound limit tb := by
  intro M hm
  cases hs : ongoing M k with
  | none =>
    left
    simpa only [view_start] using firstMissing_stops hm limit (start n) h hs
  | some m => exact children m M (matches_add hm hs)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem subtree_bound [NeZero n] {limit fuel : ℕ} {tb : Program n} {a b : List ℕ}
    (hCount : (holes tb).card ≤ fuel) (h : checkTree limit fuel tb a = some b) :
    TreeBound limit tb := by
  induction fuel generalizing tb a b with
  | zero =>
    intro M hm
    exact upper_cannot_stop hm (no_holes_cannot_stop (by omega))
  | succ fuel ih =>
    rw [checkTree.eq_def] at h
    cases hFirst : firstMissing tb limit (start n) with
    | none =>
      simp only [hFirst] at h
      intro M hm
      cases a with
      | nil => contradiction
      | cons v rest =>
        by_cases hc : checkCertificate tb v = true
        · exact upper_cannot_stop hm (certificate_sound hc)
        · simp [hc] at h
    | some k =>
      simp only [hFirst] at h
      apply branch_bound hFirst
      intro m
      obtain ⟨x, y, hy⟩ := succeeds_each h (mem_moves m)
      refine ih ?_ hy
      rw [holes_add, Finset.card_erase_of_mem (missing_is_hole hFirst)]
      omega

end BeaverBound

/- Tape-reader invariant lemmas below are reused from @marcusbuffett's
BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H3.R1 reduction. The sparse certificate
adapter is new work credited to Hanan Beer (@hananzlt). -/
namespace BeaverBound.SparseReaders
open Turing Turing.BusyBeaver
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem reader {X : Type} (f : Fin 2 → X → X) (x : X) (blank : f 0 x=x) :
    ∃ g : ListBlank (Fin 2) → X, g (ListBlank.mk [])=x ∧
      ∀ (a : Fin 2) (l : ListBlank (Fin 2)),g (ListBlank.cons a l) = f a (g l) := by
  have zeros (m : ℕ) : (List.replicate m (0 : Fin 2)).foldr f x=x := by
    induction m with
    | zero => rfl
    | succ m ih => simp [List.replicate_succ,ih,blank]
  let g (l : ListBlank (Fin 2)) := l.liftOn (fun a => a.foldr f x) (by
    rintro a _ ⟨i,rfl⟩
    simp [List.foldr_append,zeros])
  refine ⟨g,rfl,?_⟩
  intro a l
  induction l using ListBlank.induction_on with | h l => rfl

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem certified (M : Machine (Fin 2) (Fin 4))
    {X Y : Type} (x : X) (y : Y) (L : Fin 2 → X → X) (R : Fin 2 → Y → Y)
    (S : Fin 4 → Fin 2 → X → Y → Bool)
    (hl : L 0 x=x) (hr : R 0 y=y) (start : S 0 0 x y=true)
    (closed : ∀ q a s t i j, S q a (L s i) (R t j)=true →
        ∃ r w d, M q a=some (some r,Stmt.write w d) ∧
          (match d with
           | .left => S r s i (R w (R t j))
           | .right => S r t (L w (L s i)) j) = true) : ¬ M.IsHalting := by
  obtain ⟨fl,bl,cl⟩ := reader L x hl
  obtain ⟨fr,br,cr⟩ := reader R y hr
  have decompL (s : ListBlank (Fin 2)) : L s.head (fl s.tail)=fl s :=
    (cl _ _).symm.trans (congrArg fl (ListBlank.cons_head_tail s))
  have decompR (s : ListBlank (Fin 2)) : R s.head (fr s.tail)=fr s :=
    (cr _ _).symm.trans (congrArg fr (ListBlank.cons_head_tail s))
  have run (n : ℕ) : ∃ q t, M.multiStep (Machine.init []) n = some ⟨some q,t⟩ ∧
      S q t.head (fl t.left) (fr t.right)=true := by
    induction n with
    | zero =>
      refine ⟨0,Tape.mk₁ [],rfl,?_⟩
      change S 0 0 (fl (ListBlank.mk [])) (fr (ListBlank.mk []))=true
      simpa only [bl,br] using start
    | succ n ih =>
      obtain ⟨q,t,ht,hs⟩ := ih
      obtain ⟨r,w,d,move,next⟩ := closed q t.head t.left.head t.right.head (fl t.left.tail) (fr t.right.tail) (by
        rwa [decompL,decompR])
      refine ⟨r,(t.write w).move d,?_,?_⟩
      · simp [Machine.multiStep_succ,ht,Machine.step,move]
      · cases d <;> simp only [decompL,decompR] at next <;> simpa [Tape.move,Tape.write,cl,cr] using next
  intro hh
  obtain ⟨n,hn⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp hh
  obtain ⟨_,_,he,_⟩ := run (n+1)
  rw [Machine.HaltsAfter,he] at hn
  contradiction


inductive Tree (α : Type) where
  | nil : Tree α
  | node : α → Tree α → Tree α → Tree α

def member [DecidableEq α] (code : α → ℕ) (x : α) : Tree α → Bool
  | .nil => false
  | .node a l r => if x = a then true else
      if code x < code a then member code x l else member code x r

def every (p : α → Bool) : Tree α → Bool
  | .nil => true
  | .node a l r => p a && every p l && every p r

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem every_member [DecidableEq α] {code : α → ℕ} {p : α → Bool}
    (t : Tree α) {x : α} (h : every p t = true) (hx : member code x t = true) :
    p x = true := by
  induction t with
  | nil => simp [member] at hx
  | node a l r ihl ihr =>
    have hh : p a = true ∧ every p l = true ∧ every p r = true := by
      simpa only [every, Bool.and_eq_true, and_assoc] using h
    by_cases ha : x = a
    · simpa only [ha] using hh.1
    · simp only [member, ha, if_false] at hx
      split at hx
      · exact ihl hh.2.1 hx
      · exact ihr hh.2.2 hx

abbrev Context (n m : ℕ) := Fin 4 × Fin 2 × Fin n × Fin m

def code (c : Context n m) : ℕ :=
  ((2 * c.1.val + c.2.1.val) * n + c.2.2.1.val) * m + c.2.2.2.val

def marked (t : Tree (Context n m)) (q : Fin 4) (a : Fin 2) (l : Fin n) (r : Fin m) : Bool :=
  member code (q,a,l,r) t

def checkContext (tb : Program 4)
    (L : Fin 2 → Fin n → Fin n) (R : Fin 2 → Fin m → Fin m)
    (preL : Fin n → List (Fin 2 × Fin n)) (preR : Fin m → List (Fin 2 × Fin m))
    (t : Tree (Context n m)) (c : Context n m) : Bool :=
  match tb.get (c.1,c.2.1) with
  | none => false
  | some cmd => if cmd.left then
      (preL c.2.2.1).all fun (s,l) => marked t cmd.state s l (R cmd.write c.2.2.2)
    else (preR c.2.2.2).all fun (s,r) => marked t cmd.state s (L cmd.write c.2.2.1) r

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem sparse_bound {n m : ℕ} [NeZero n] [NeZero m] (tb : Program 4)
    (L : Fin 2 → Fin n → Fin n) (R : Fin 2 → Fin m → Fin m)
    (preL : Fin n → List (Fin 2 × Fin n)) (preR : Fin m → List (Fin 2 × Fin m))
    (t : Tree (Context n m))
    (left_complete : ∀ s l, (s,l) ∈ preL (L s l))
    (right_complete : ∀ s r, (s,r) ∈ preR (R s r))
    (hl : L 0 0 = 0) (hr : R 0 0 = 0) (start : marked t 0 0 0 0 = true)
    (closed : every (checkContext tb L R preL preR t) t = true) : TreeBound 107 tb := by
  intro M hm
  right
  apply certified M (0 : Fin n) (0 : Fin m) L R (marked t) hl hr start
  intro q a s u l r h
  have good := every_member t closed h
  change checkContext tb L R preL preR t (q,a,L s l,R u r) = true at good
  cases hc : tb.get (q,a) with
  | none => simp [checkContext,hc] at good
  | some cmd =>
    have transition := hm (q,a) cmd hc
    have command := ongoing_command M (q,a) cmd transition
    by_cases hd : cmd.left = true
    · refine ⟨cmd.state,cmd.write,.left,?_,?_⟩
      · simpa [Move.command,hd] using command
      · have hgood : (preL (L s l)).all (fun (a,i) => marked t cmd.state a i (R cmd.write (R u r))) = true := by
          simpa [checkContext,hc,hd] using good
        exact List.all_eq_true.mp hgood (s,l) (left_complete s l)
    · have hd' : cmd.left = false := Bool.eq_false_iff.mpr hd
      refine ⟨cmd.state,cmd.write,.right,?_,?_⟩
      · simpa [Move.command,hd'] using command
      · have hgood : (preR (R u r)).all (fun (a,j) => marked t cmd.state a (L cmd.write (L s l)) j) = true := by
          simpa [checkContext,hc,hd'] using good
        exact List.all_eq_true.mp hgood (u,r) (right_complete u r)

end BeaverBound.SparseReaders

namespace BeaverBound.SparseReaders

/-- Read a finite balanced tree from packed node indices. Zero denotes an empty node. -/
def packedTree {n m : ℕ} [NeZero n] [NeZero m] (bits data : ℕ) :
    ℕ → ℕ → Tree (Context n m)
  | 0, _ => .nil
  | fuel + 1, index =>
    match (data >>> (bits * index)) % 2^bits with
    | 0 => .nil
    | v + 1 => .node
        (Fin.ofNat 4 (v / (2*n*m)), Fin.ofNat 2 (v / (n*m)),
          Fin.ofNat n (v/m), Fin.ofNat m v)
        (packedTree bits data fuel (2*index+1))
        (packedTree bits data fuel (2*index+2))

end BeaverBound.SparseReaders

namespace BeaverBound.SparseReaders
private def L15 (a : Fin 2) (x : Fin 63) : Fin 63 :=
  Fin.ofNat 63 (((372920846425167877697465717123015410340671201373677019022608039741496877148095105677818486578237575708581759842363861979724742745865745275898634579973035387956825526361576823880713251702271952908883043990820492742426174740504640 : ℕ) >>> (6*(2*x.val+a.val))) % 64)
private def preL15 (x : Fin 63) : List (Fin 2 × Fin 63) :=
  match x.val with
  | 0 => [(0,0)]
  | 1 => [(1,0)]
  | 2 => [(0,1)]
  | 3 => [(1,1)]
  | 4 => [(0,2),(0,33)]
  | 5 => [(1,2),(1,33)]
  | 6 => [(0,3),(0,34)]
  | 7 => [(1,3),(1,34)]
  | 8 => [(0,4),(0,35)]
  | 9 => [(1,4),(1,35)]
  | 10 => [(0,5),(0,36)]
  | 11 => [(1,5),(1,36)]
  | 12 => [(0,6),(0,37)]
  | 13 => [(1,6),(1,37)]
  | 14 => [(0,7),(0,38)]
  | 15 => [(1,7),(1,38)]
  | 16 => [(0,8),(0,39)]
  | 17 => [(1,8),(1,39)]
  | 18 => [(0,9),(0,40)]
  | 19 => [(1,9),(1,40)]
  | 20 => [(0,10),(0,41)]
  | 21 => [(1,10),(1,41)]
  | 22 => [(0,11),(0,42)]
  | 23 => [(1,11),(1,42)]
  | 24 => [(0,12),(0,43)]
  | 25 => [(1,12),(1,43)]
  | 26 => [(0,13),(0,44)]
  | 27 => [(1,13),(1,44)]
  | 28 => [(0,14),(0,45)]
  | 29 => [(1,14),(1,45)]
  | 30 => [(0,15),(0,46)]
  | 31 => [(1,15),(1,46)]
  | 32 => [(0,16),(1,16),(0,32),(1,32),(0,47),(1,47)]
  | 33 => [(0,17),(0,48)]
  | 34 => [(1,17),(1,48)]
  | 35 => [(0,18),(0,49)]
  | 36 => [(1,18),(1,49)]
  | 37 => [(0,19),(0,50)]
  | 38 => [(1,19),(1,50)]
  | 39 => [(0,20),(0,51)]
  | 40 => [(1,20),(1,51)]
  | 41 => [(0,21),(0,52)]
  | 42 => [(1,21),(1,52)]
  | 43 => [(0,22),(0,53)]
  | 44 => [(1,22),(1,53)]
  | 45 => [(0,23),(0,54)]
  | 46 => [(1,23),(1,54)]
  | 47 => [(0,24),(0,55)]
  | 48 => [(1,24),(1,55)]
  | 49 => [(0,25),(0,56)]
  | 50 => [(1,25),(1,56)]
  | 51 => [(0,26),(0,57)]
  | 52 => [(1,26),(1,57)]
  | 53 => [(0,27),(0,58)]
  | 54 => [(1,27),(1,58)]
  | 55 => [(0,28),(0,59)]
  | 56 => [(1,28),(1,59)]
  | 57 => [(0,29),(0,60)]
  | 58 => [(1,29),(1,60)]
  | 59 => [(0,30),(0,61)]
  | 60 => [(1,30),(1,61)]
  | 61 => [(0,31),(0,62)]
  | 62 => [(1,31),(1,62)]
  | _ => []
private def R15 (a : Fin 2) (x : Fin 13) : Fin 13 :=
  Fin.ofNat 13 (((10817366119977471775876817629712 : ℕ) >>> (4*(2*x.val+a.val))) % 16)
private def preR15 (x : Fin 13) : List (Fin 2 × Fin 13) :=
  match x.val with
  | 0 => [(0,0)]
  | 1 => [(1,0)]
  | 2 => [(0,1)]
  | 3 => [(1,1)]
  | 4 => [(0,2)]
  | 5 => [(1,2)]
  | 6 => [(0,3)]
  | 7 => [(1,3)]
  | 8 => [(0,4),(1,4),(0,6),(1,6),(0,7),(1,7),(0,8),(1,8),(0,9),(1,9),(0,11),(1,11),(0,12),(1,12)]
  | 9 => [(0,5)]
  | 10 => [(1,5)]
  | 11 => [(0,10)]
  | 12 => [(1,10)]
  | _ => []
private def contexts15 : Tree (Context 63 13) :=
packedTree 13 0x32dc000c9d000320d8ecc4f00030d4000c1b0002feb7d4bd38002ee6000b928002de36d0b518002cde000b0d0002c195b2ad40002ae8000a9e8002a194e2a5880028f4000a0f80028253e19d680027360009a7800268534098480025de0009670002539287929800246400090000023d71cc8db80022e20008a1000225110987a000214c00084600020d705881c80020140008008001f4cf657a10001db400074a8001c96e136e90001b560006a38001a26d016738001994000655800192cc8163e00018c40006218001862c1c60c00017d00005ec8001768bb05d380017240005b980016c2b3758e800161000057700015c8acf55a800154000054480014eea55524000146600050e80014249ff4f280013a00004dc80013689ac4d400010c600040a0000ea26cf34d800064c00018c800060e2f2176800059600015c800054429914500004fa00012a0000478237111000042a0000f700003c21d20e480003700000c9800030c1770b600002b400009c000024c11108600001ee00007500001820b6053800011e00004100000b6056020800006c000012800001a008000e6232a9920c5c62130a181cbe0de36eb3704b5eda26c8960dad85692a8152ea7051f68934159dbcea66cf345991cc0a5a12a1931c8d240b1fb8e545da2b913b883c30213f06d81f4092006faa7a5bc39d4ce7b6f1b6bdaf6d35674336d960c9b64031d5890c3360cafe97b6bc65d62e896f0b63592ac595e2ae955eaab9536a85526a8e143ca144f6a7793969b54d523fd05e76c34e0ccc64230a1780b345782a414b8a144ac24911788743f61e90e786e834018e0ba057427412908784101e40c3054827011406802700f004e01a002659f1ff863bedddb2daf668aee552a9f5479a08cde66832d594d487e3a316f88742860d10057bb3b59c2ed9d68132e1908c506172f81762b805af2c0d5c4a9e533a88541e9ce4d8a188da032417f8af853e26311d07f43a81b50bc854823c0f505f02340b2034005e4cf05f70bb0854f283b34d95dc7fa27b0727ef3a51a86ca9620af2d6e2aed543286536c7a01860ac44a21ec0c884ac1a006a011625ed39487982464206edb863bae955609e033a0a2038e10601fde827550d066fac612662200525695e7ca460afc8e45cac0a 9 0
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem exceptional15 : TreeBound (n := 4) 107 [((3,1),⟨3,1,false⟩),((1,1),⟨1,0,false⟩),((2,1),⟨0,1,true⟩),((3,0),⟨2,1,true⟩),((0,0),⟨1,1,false⟩),((1,0),⟨2,0,false⟩),((2,0),⟨3,0,true⟩)] := by
  apply sparse_bound _ L15 R15 preL15 preR15 contexts15
  all_goals decide +kernel

end BeaverBound.SparseReaders
namespace BeaverBound

def forceNat {α : Type} (v : ℕ) (f : ℕ → α) : α :=
  match v with
  | 0 => f 0
  | k + 1 => f (k + 1)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem forceNat_eq {α : Type} (v : ℕ) (f : ℕ → α) : forceNat v f = f v := by
  cases v <;> rfl

/-- Normalize packed fields once before the kernel checks repeated edge lookups. -/
def checkCertificateFast [NeZero n] (tb : Program n) (val : ℕ) : Bool :=
  forceNat (val / 2 % 8) fun extra =>
  let size := extra + 1
  forceNat (size ^ (2 * size - 1)) fun dfaBase =>
  forceNat (val / 16 % dfaBase) fun dfaCode =>
  forceNat (val / 16 / dfaBase) fun payload =>
  forceNat (2 ^ (n * size + 1)) fun initialBase =>
  forceNat (payload / initialBase) fun edges =>
  forceNat (payload % initialBase) fun blankReach =>
  let C : Certificate n := ⟨val % 2 == 1, ⟨extra,dfaCode⟩, edges,blankReach⟩
  checkBlank C && checkMachine (if C.mirror then tb.flip else tb) C

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checkCertificateFast_eq [NeZero n] (tb : Program n) (val : ℕ) :
    checkCertificateFast tb val = checkCertificate tb val := by
  simp only [checkCertificateFast, forceNat_eq]
  rfl
end BeaverBound
namespace BeaverBound

def Certificate.row (cert : Certificate n) (p : Node cert) (a : Symbol) : ℕ :=
  match p with
  | none => 2 ^ (n * cert.dfa.size)
  | some _ => (cert.edges >>> ((2 * nodeId cert p + a.val) *
      (n * cert.dfa.size + 1))) % 2 ^ (n * cert.dfa.size + 1)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem state_nodeId_lt (cert : Certificate n) (q : Fin n) (l : Fin cert.dfa.size) :
    nodeId cert (some (q,l)) < n * cert.dfa.size := by
  have hh := Nat.mul_le_mul_right cert.dfa.size (Nat.succ_le_of_lt q.isLt)
  simp only [Nat.succ_mul] at hh
  have hl := l.isLt
  simp only [nodeId]
  omega

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem nodeId_lt (cert : Certificate n) (p : Node cert) :
    nodeId cert p < n * cert.dfa.size + 1 := by
  rcases p with _ | ⟨q,l⟩
  · simp [nodeId]
  · exact Nat.lt_succ_of_lt (state_nodeId_lt cert q l)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem row_bit (cert : Certificate n) (p q : Node cert) (a : Symbol) :
    (cert.row p a).testBit (nodeId cert q) = cert.edge p a q := by
  cases p with
  | none =>
    cases q with
    | none => simp [Certificate.row,Certificate.edge,nodeId]
    | some q =>
      have hh := state_nodeId_lt cert q.1 q.2
      simp [Certificate.row,Certificate.edge,ne_of_gt hh]
  | some p =>
    have hq := nodeId_lt cert q
    simp only [Certificate.row,Certificate.edge,Nat.testBit_mod_two_pow,
      Nat.testBit_shiftRight,hq,decide_true,Bool.true_and]

def rowsIncluded (a b : ℕ) : Bool := decide (a &&& b = a)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem rowsIncluded_bit {a b i : ℕ} (h : rowsIncluded a b = true)
    (ha : a.testBit i = true) : b.testBit i = true := by
  have he : a &&& b = a := of_decide_eq_true h
  have hh := congrArg (fun v => v.testBit i) he
  simpa only [Nat.testBit_and,ha,Bool.true_and] using hh

def checkAtBits (tb : Program n) (cert : Certificate n) (q : Fin n) (a : Symbol)
    (l : Fin cert.dfa.size) : Bool :=
  let p : Node cert := some (q,l)
  match tb.get (q,a) with
  | none => cert.edge p a none
  | some m =>
    if m.left then
      forceNat (cert.row p a) fun target =>
      (List.finRange cert.dfa.size).all fun l' => (List.finRange 2).all fun a' =>
        if cert.dfa.next a' l' = l then
          (nodes cert).all fun s => if cert.edge (some (m.state,l')) a' s then
            rowsIncluded (cert.row s m.write) target
          else true
        else true
    else cert.edge p a (some (m.state,cert.dfa.next m.write l))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checkAtBits_sound {tb : Program n} {cert : Certificate n} {q : Fin n}
    {a : Symbol} {l : Fin cert.dfa.size} (h : checkAtBits tb cert q a l = true) :
    checkAt tb cert q a l = true := by
  unfold checkAtBits checkAt at *
  cases hg : tb.get (q,a) with
  | none => simpa [hg] using h
  | some m =>
    simp only [hg] at h ⊢
    cases hd : m.left with
    | false => simpa [hd] using h
    | true =>
      simp only [hd,if_true,forceNat_eq] at h ⊢
      apply List.all_eq_true.mpr
      intro l' _
      apply List.all_eq_true.mpr
      intro a' _
      have hh := allFin (allFin h l') a'
      by_cases he : cert.dfa.next a' l' = l
      · simp only [he,if_true] at hh ⊢
        apply List.all_eq_true.mpr
        intro s _
        have hs := allNodes hh s
        by_cases hed : cert.edge (some (m.state,l')) a' s = true
        · simp only [hed,if_true] at hs ⊢
          apply List.all_eq_true.mpr
          intro t _
          by_cases het : cert.edge s m.write t = true
          · have hrow : (cert.row s m.write).testBit (nodeId cert t) = true := by
              rwa [row_bit]
            have ht := rowsIncluded_bit hs hrow
            rw [row_bit] at ht
            simp only [het,ht,Bool.not_true,Bool.false_or]
          · simp [het]
        · simp [hed]
      · simp [he]

def checkMachineBits (tb : Program n) (cert : Certificate n) : Bool :=
  (List.finRange n).all fun q => (List.finRange 2).all fun a =>
    (List.finRange cert.dfa.size).all fun l => checkAtBits tb cert q a l

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checkMachineBits_sound {tb : Program n} {cert : Certificate n}
    (h : checkMachineBits tb cert = true) : checkMachine tb cert = true := by
  unfold checkMachineBits at h
  unfold checkMachine
  apply List.all_eq_true.mpr
  intro q _
  apply List.all_eq_true.mpr
  intro a _
  apply List.all_eq_true.mpr
  intro l _
  exact checkAtBits_sound (allFin (allFin (allFin h q) a) l)

end BeaverBound

namespace BeaverBound

def checkBlankBits (cert : Certificate n) [NeZero n] : Bool :=
  cert.onBlank (some (0,0)) && !cert.onBlank none &&
    (nodes cert).all fun p => if cert.onBlank p then
      rowsIncluded (cert.row p 0) cert.blankReach
    else true

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checkBlankBits_sound {cert : Certificate n} [NeZero n]
    (h : checkBlankBits cert = true) : checkBlank cert = true := by
  simp only [checkBlankBits,Bool.and_eq_true_iff] at h
  unfold checkBlank
  apply Bool.and_eq_true_iff.mpr
  refine ⟨Bool.and_eq_true_iff.mpr h.1,?_⟩
  apply List.all_eq_true.mpr
  intro p _
  have hp := allNodes h.2 p
  by_cases hb : cert.onBlank p = true
  · simp only [hb,if_true] at hp ⊢
    apply List.all_eq_true.mpr
    intro q _
    by_cases he : cert.edge p 0 q = true
    · have hrow : (cert.row p 0).testBit (nodeId cert q) = true := by rwa [row_bit]
      have hq := rowsIncluded_bit hp hrow
      change cert.onBlank q = true at hq
      simp only [he,hq,Bool.not_true,Bool.false_or]
    · simp [he]
  · simp [hb]

def checkCertificateBits [NeZero n] (tb : Program n) (val : ℕ) : Bool :=
  forceNat (val / 2 % 8) fun extra =>
  let size := extra + 1
  forceNat (size ^ (2 * size - 1)) fun dfaBase =>
  forceNat (val / 16 % dfaBase) fun dfaCode =>
  forceNat (val / 16 / dfaBase) fun payload =>
  forceNat (2 ^ (n * size + 1)) fun initialBase =>
  forceNat (payload / initialBase) fun edges =>
  forceNat (payload % initialBase) fun blankReach =>
  let C : Certificate n := ⟨val % 2 == 1, ⟨extra,dfaCode⟩, edges,blankReach⟩
  checkBlankBits C && checkMachineBits (if C.mirror then tb.flip else tb) C

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checkCertificateBits_sound [NeZero n] {tb : Program n} {val : ℕ}
    (h : checkCertificateBits tb val = true) : ¬ CanStop tb (start n) := by
  apply certificate_sound (val := val)
  rw [← checkCertificateFast_eq]
  unfold checkCertificateBits at h
  unfold checkCertificateFast
  simp only [forceNat_eq] at h ⊢
  exact Bool.and_eq_true_iff.mpr ⟨checkBlankBits_sound (Bool.and_eq_true_iff.mp h).1,
    checkMachineBits_sound (Bool.and_eq_true_iff.mp h).2⟩

end BeaverBound

namespace BeaverBound

/- The constructor is an untrusted finite calculation following direct FAR
saturation from bbchallenge. Its output must pass `checkCertificateFast`, whose
soundness is inherited from James Halldon's verifier. -/

def nfaRow (size edges p : ℕ) (a : Fin 2) : ℕ :=
  let width := 4 * size + 1
  if p = 4 * size then 1 <<< (4 * size)
  else (edges >>> ((2 * p + a.val) * width)) % (2 ^ width)

def nfaInsert (size edges p : ℕ) (a : Fin 2) (row : ℕ) : ℕ :=
  edges ||| (row <<< ((2 * p + a.val) * (4 * size + 1)))

def nfaInitial (tb : Program 4) (D : TapeDFA) : ℕ :=
  (List.finRange 4).foldl (fun e q =>
    (List.finRange 2).foldl (fun e a =>
      (List.finRange D.size).foldl (fun e l =>
        match tb.get (q,a) with
        | none => nfaInsert D.size e (q.val * D.size + l.val) a (1 <<< (4 * D.size))
        | some cmd => if cmd.left then e else
            nfaInsert D.size e (q.val * D.size + l.val) a
              (1 <<< (cmd.state.val * D.size + (D.next cmd.write l).val))) e) e) 0

def nfaCompose (size edges mask : ℕ) (a : Fin 2) : ℕ :=
  forceNat mask fun mask =>
  (List.range (4 * size + 1)).foldl (fun out p =>
    if mask.testBit p then out ||| nfaRow size edges p a else out) 0

def nfaIteration (tb : Program 4) (D : TapeDFA) (edges : ℕ) : ℕ :=
  (List.finRange 4).foldl (fun out q =>
    (List.finRange 2).foldl (fun out a =>
      match tb.get (q,a) with
      | none => out
      | some cmd => if cmd.left then
          (List.finRange D.size).foldl (fun out l =>
            (List.finRange 2).foldl (fun out b =>
              nfaInsert D.size out (q.val * D.size + (D.next b l).val) a
                (nfaCompose D.size edges (nfaRow D.size edges
                  (cmd.state.val * D.size + l.val) b) cmd.write)) out) out
        else out) out) edges

def nfaSaturate (tb : Program 4) (D : TapeDFA) : ℕ → ℕ → ℕ
  | 0, edges => edges
  | fuel + 1, edges => forceNat (nfaIteration tb D edges) fun next =>
      if next = edges then next else nfaSaturate tb D fuel next

def nfaBlankStep (size edges reach : ℕ) : ℕ :=
  reach ||| nfaCompose size edges reach 0

def nfaBlankReach (size edges : ℕ) : ℕ → ℕ → ℕ
  | 0, reach => reach
  | fuel + 1, reach => forceNat (nfaBlankStep size edges reach) fun next =>
      if next = reach then next else nfaBlankReach size edges fuel next

def constructCertificate (tb : Program 4) (choice : ℕ) : ℕ :=
  forceNat (choice / 2 % 8) fun extra =>
  let size := extra + 1
  forceNat (size ^ (2 * size - 1)) fun dfaBase =>
  forceNat (choice / 16 % dfaBase) fun code =>
  let D : TapeDFA := ⟨extra,code⟩
  let oriented := if choice % 2 == 1 then tb.flip else tb
  forceNat (nfaInitial oriented D) fun initial =>
  forceNat (nfaSaturate oriented D (2 * (4 * size + 1) ^ 2) initial) fun edges =>
  forceNat (nfaBlankReach size edges (4 * size + 1) 1) fun reach =>
  choice % 2 + 2 * extra + 16 * (code + dfaBase * (reach + 2^(4 * size + 1) * edges))

def checkChoice (tb : Program 4) (choice : ℕ) : Bool :=
  forceNat (constructCertificate tb choice) fun cert => checkCertificateBits tb cert

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem choice_sound {tb : Program 4} {choice : ℕ}
    (h : checkChoice tb choice = true) : ¬ CanStop tb (start 4) := by
  apply checkCertificateBits_sound (val := constructCertificate tb choice)
  simpa only [checkChoice, forceNat_eq] using h

end BeaverBound
namespace BeaverBound

def chunkBytes : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, data => forceNat (data / 256) fun next =>
      data % 256 :: chunkBytes fuel next

def varints : List ℕ → ℕ → ℕ → List ℕ
  | [], _, _ => []
  | b :: rest, acc, shift =>
    let next := acc + (b % 128) * 2^shift
    if b < 128 then next :: varints rest 0 0 else varints rest next (shift+7)

def decodeTokens (chunks : List (ℕ × ℕ)) : List ℕ :=
  varints (chunks.flatMap fun (count,data) => chunkBytes count data) 0 0

def checkGenerated (special : ℕ → Program 4 → Bool) :
    ℕ → Program 4 → List ℕ → Option (List ℕ)
  | 0, _, certs => some certs
  | _ + 1, _, [] => none
  | fuel + 1, tb, v :: rest =>
    if v = 0 then
      match firstMissing tb 107 (start 4) with
      | none => none
      | some k => (moves 4).foldlM (fun xs m => checkGenerated special fuel ((k,m)::tb) xs) rest
    else if v < 17 then if special v tb then some rest else none
    else if checkChoice tb (v-17) then some rest else none

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem generated_bound (special : ℕ → Program 4 → Bool)
    (hspecial : ∀ v tb, special v tb = true → TreeBound 107 tb)
    {fuel : ℕ} {tb : Program 4} {a b : List ℕ}
    (hCount : (holes tb).card ≤ fuel) (h : checkGenerated special fuel tb a = some b) :
    TreeBound 107 tb := by
  induction fuel generalizing tb a b with
  | zero =>
    intro M hm
    exact upper_cannot_stop hm (no_holes_cannot_stop (by omega))
  | succ fuel ih =>
    cases a with
    | nil => simp [checkGenerated] at h
    | cons v rest =>
      by_cases hv : v = 0
      · simp only [checkGenerated, hv, if_true] at h
        cases hFirst : firstMissing tb 107 (start 4) with
        | none => simp [hFirst] at h
        | some k =>
          simp only [hFirst] at h
          apply branch_bound hFirst
          intro m
          obtain ⟨x,y,hy⟩ := succeeds_each h (mem_moves m)
          refine ih ?_ hy
          rw [holes_add, Finset.card_erase_of_mem (missing_is_hole hFirst)]
          omega
      · simp only [checkGenerated, hv, if_false] at h
        by_cases small : v < 17
        · simp only [small,if_true] at h
          by_cases hs : special v tb = true
          · exact hspecial v tb hs
          · simp [hs] at h
        · simp only [small,if_false] at h
          by_cases hc : checkChoice tb (v-17) = true
          · intro M hm
            exact upper_cannot_stop hm (choice_sound hc)
          · simp [hc] at h
end BeaverBound

namespace BeaverBound

private def exceptionalCheck (v : ℕ) (tb : Program 4) : Bool :=
  v == 16 && decide (tb = [((3,1),⟨3,1,false⟩),((1,1),⟨1,0,false⟩),((2,1),⟨0,1,true⟩),((3,0),⟨2,1,true⟩),((0,0),⟨1,1,false⟩),((1,0),⟨2,0,false⟩),((2,0),⟨3,0,true⟩)])

private theorem exceptionalCheck_sound (v : ℕ) (tb : Program 4)
    (h : exceptionalCheck v tb = true) : TreeBound 107 tb := by
  have ht : tb = [((3,1),⟨3,1,false⟩),((1,1),⟨1,0,false⟩),((2,1),⟨0,1,true⟩),((3,0),⟨2,1,true⟩),((0,0),⟨1,1,false⟩),((1,0),⟨2,0,false⟩),((2,0),⟨3,0,true⟩)] :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp h).2
  rw [ht]
  exact SparseReaders.exceptional15
end BeaverBound
namespace BeaverBound

/- This is only a data preparation pass. The result is checked again by
`checkPrepared`, including every branch and every certificate. No correctness
assumption about this pass is used by the soundness theorem. -/
def prepareCertificates : ℕ → Program 4 → List ℕ → List ℕ →
    Option (List ℕ × List ℕ)
  | 0, _, rest, acc => some (rest, acc)
  | _ + 1, _, [], _ => none
  | fuel + 1, tb, v :: rest, acc =>
    if v = 0 then
      match firstMissing tb 107 (start 4) with
      | none => none
      | some k => (moves 4).foldlM
          (fun st m => prepareCertificates fuel ((k,m)::tb) st.1 st.2)
          (rest, 0 :: acc)
    else if v < 17 then some (rest, v :: acc)
    else forceNat (constructCertificate tb (v-17)) fun cert =>
      some (rest, (cert+17) :: acc)

def preparedTokens (fuel : ℕ) (tb : Program 4) (xs : List ℕ) : List ℕ :=
  match prepareCertificates fuel tb xs [] with
  | some ([], acc) => acc.reverse
  | _ => []

def checkPrepared (special : ℕ → Program 4 → Bool) :
    ℕ → Program 4 → List ℕ → Option (List ℕ)
  | 0, _, certs => some certs
  | _ + 1, _, [] => none
  | fuel + 1, tb, v :: rest =>
    if v = 0 then
      match firstMissing tb 107 (start 4) with
      | none => none
      | some k => (moves 4).foldlM (fun xs m => checkPrepared special fuel ((k,m)::tb) xs) rest
    else if v < 17 then if special v tb then some rest else none
    else if checkCertificateBits tb (v-17) then some rest else none

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem prepared_bound (special : ℕ → Program 4 → Bool)
    (hspecial : ∀ v tb, special v tb = true → TreeBound 107 tb)
    {fuel : ℕ} {tb : Program 4} {a b : List ℕ}
    (hCount : (holes tb).card ≤ fuel) (h : checkPrepared special fuel tb a = some b) :
    TreeBound 107 tb := by
  induction fuel generalizing tb a b with
  | zero =>
    intro M hm
    exact upper_cannot_stop hm (no_holes_cannot_stop (by omega))
  | succ fuel ih =>
    cases a with
    | nil => simp [checkPrepared] at h
    | cons v rest =>
      by_cases hv : v = 0
      · simp only [checkPrepared, hv, if_true] at h
        cases hFirst : firstMissing tb 107 (start 4) with
        | none => simp [hFirst] at h
        | some k =>
          simp only [hFirst] at h
          apply branch_bound hFirst
          intro m
          obtain ⟨x,y,hy⟩ := succeeds_each h (mem_moves m)
          refine ih ?_ hy
          rw [holes_add, Finset.card_erase_of_mem (missing_is_hole hFirst)]
          omega
      · simp only [checkPrepared, hv, if_false] at h
        by_cases small : v < 17
        · simp only [small,if_true] at h
          by_cases hs : special v tb = true
          · exact hspecial v tb hs
          · simp [hs] at h
        · simp only [small,if_false] at h
          by_cases hc : checkCertificateBits tb (v-17) = true
          · intro M hm
            exact upper_cannot_stop hm (checkCertificateBits_sound hc)
          · simp [hc] at h
end BeaverBound

namespace BeaverBound

/-- This decoder supplies data only; every decoded program is checked by the proof. -/
private def decodeProgram : ℕ → ℕ → Program 4
  | 0, _ => []
  | fuel+1, data => if data = 0 then [] else
      let v := data % 256 - 1
      ((⟨v/32%4, Nat.mod_lt _ (by decide)⟩, ⟨v/16%2, Nat.mod_lt _ (by decide)⟩),
        ⟨⟨v/4%4, Nat.mod_lt _ (by decide)⟩,
          ⟨v/2%2, Nat.mod_lt _ (by decide)⟩, v%2 == 1⟩) ::
        decodeProgram fuel (data/256)

private def programCode (data : ℕ) : Program 4 := decodeProgram 8 data

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem branchFour {tb : Program 4} {k : Key 4}
    (h : firstMissing tb 107 (start 4) = some k)
    (p0 : TreeBound (n := 4) 107 ((k,⟨0,0,false⟩)::tb))
    (p1 : TreeBound (n := 4) 107 ((k,⟨0,0,true⟩)::tb))
    (p2 : TreeBound (n := 4) 107 ((k,⟨0,1,false⟩)::tb))
    (p3 : TreeBound (n := 4) 107 ((k,⟨0,1,true⟩)::tb))
    (p4 : TreeBound (n := 4) 107 ((k,⟨1,0,false⟩)::tb))
    (p5 : TreeBound (n := 4) 107 ((k,⟨1,0,true⟩)::tb))
    (p6 : TreeBound (n := 4) 107 ((k,⟨1,1,false⟩)::tb))
    (p7 : TreeBound (n := 4) 107 ((k,⟨1,1,true⟩)::tb))
    (p8 : TreeBound (n := 4) 107 ((k,⟨2,0,false⟩)::tb))
    (p9 : TreeBound (n := 4) 107 ((k,⟨2,0,true⟩)::tb))
    (p10 : TreeBound (n := 4) 107 ((k,⟨2,1,false⟩)::tb))
    (p11 : TreeBound (n := 4) 107 ((k,⟨2,1,true⟩)::tb))
    (p12 : TreeBound (n := 4) 107 ((k,⟨3,0,false⟩)::tb))
    (p13 : TreeBound (n := 4) 107 ((k,⟨3,0,true⟩)::tb))
    (p14 : TreeBound (n := 4) 107 ((k,⟨3,1,false⟩)::tb))
    (p15 : TreeBound (n := 4) 107 ((k,⟨3,1,true⟩)::tb))
    : TreeBound (n := 4) 107 tb := by
  apply branch_bound h
  rintro ⟨q,a,b⟩
  fin_cases q <;> fin_cases a <;> cases b
  · exact p0
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5
  · exact p6
  · exact p7
  · exact p8
  · exact p9
  · exact p10
  · exact p11
  · exact p12
  · exact p13
  · exact p14
  · exact p15

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_1 : TreeBound (n := 4) 107 (programCode 0x4e290761) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 4)
    (a := List.flatten [
[0x8000600018040200088004200108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_3 : TreeBound (n := 4) 107 (programCode 0x4e29076211) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8002200108040200108004200100082002080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_4 : TreeBound (n := 4) 107 (programCode 0x4e29076212) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8000200108040200008004200100002020080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_5 : TreeBound (n := 4) 107 (programCode 0x4e29076213) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8002200108040200108004200100102004080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_6 : TreeBound (n := 4) 107 (programCode 0x4e29076214) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x8002200108040200100084002100082002080ce3,0x8000200108040200000004020100002000080ce3,0x8002200108040200100104004100002004080ce3,0x8000200108040200000004000100002000080ce3,0x8004200108040200000204008100202008080ce3,0x8000200108040200000004000100002000080ce3,0x8004200108040200000404010100402010080ce3,0x0,0x1008d02184642,0x1008502184642,0x1008d02184642,0x1008502184642,0x1008d02184642,0x1008902084642,0x1008d02184642,0x1008902084642,0x1008d02184642,0xf30000b6400088b00007a733cc0f33cc00f33cc00f30079bcfcc00f30079897e0001e679807983eb86b6,0x0,0xf30000b6400088b00007b663cc079bcc01e63cc00f30079bdb3000f30079897e0001e67980798446a6b6,0x0,0x100a102084642,0x0,0x100a102084642,0xf3000222c00088b0000b640f30f303cc3cc03ccf3445a22c1e60000f307991167983cc0f307983cc3cb6,0x0,0x1008504084222,0x1008504084222,0x1008504084222,0x1008504084222,0x8000600012010004400800c200101008040201e4],
[0x1008904084642,0x1008504084222,0x1008904084642,0x1008504084222,0xf30000b6400088b00007a733cc0f33cc00f33cc03cc007d4c3cc03cc0079897e0001e7e6007983ee5fb6,0x0,0xf30000b6400088b00007b663cc079bcc01e63cc03cc007d4cf3003cc0079897e0001e9cc0079844d4bb6,0xf3000222c00088b0000b650230f303cc0007d4c0f3799e9cc003cfcc007991167983cc0f307983cc3cb6,0x100a1040852a2,0x8000200104040100000004200100002000080ce3,0x100a1040852a2,0x0,0xf33cc1e600007980000b640f30f303cc3cc03ccf3445a22c1e600000007991167983cc00007983cc3cb6,0x3cc1e60f307980f30b640f30f303cc3cc03ccf3445a22c1e60000f307991167983cc0f307983cc3cb6,0x0,0x0,0x0,0x1e601e679807987980b640f30f303cc3cc03ccf4ed9a22c1e6000798079911a4583cc3cc07983ccb636,0x0,0x0,0xf33cc222c0007980f30b640f30f303cc3cc03ccf3445a22c1e60000f307991167983cc0f307983cc3cb6,0x0,0xf37b663cc0000798981cc0000f300003cc1e600f301e63cc1e607981ea08c03db3000f33cc01e703df5,0x0,0x0,0x7980020460007b66000b640f30f303cc3cc03cd6c879a22c1e601e60007992097983db30007983ea9cb6,0x0,0x0,0x0,0x1008504084222,0x1008504084222,0x1008504084222],
[0x1008504084222,0xf30000b6400088b00009f83a0c7983cc079fd4c0798007a74301b9980079897e5b212fc0007d50641326,0x1008904084642,0x1008504084222,0x1008904084642,0x1008504084222,0xf30000b6400088b00007a733cc0f33cc00f33cc0798007b663cc07980079897e0001ed98007983f9c3b6,0x0,0xf30000b6400088b00007b663cc079bcc01e63cc0798007b66f3007980079897e0001e9cc0079844d4bb6,0x0,0x100a1040852a2,0x0,0x100a1040852a2,0x0,0x1340c8224481,0x1000080004000200010000800010000c000080010000200040000800100000800400120001000480020000a00000002000080010001000048002000200010000200010002eaba8,0x1340c8224481,0x824088220481,0x224088228481,0x804000108000200002004080100002080080ce3,0x224088228481,0x0,0x4000000090004000240000000800010000c000080010000200040000800100000800400020001000480020000a00000002000080010001000048002000200010000200010002eaba8,0x100000080100000081000000801000000c00008001000008004000080010000080004002000100000000840020000000200008000a000000088000000080204000200010440db1a8,0x4000000090000000240000000800000000c000080010000200040000800100000800400020001000480020000200000002000080010000000048002000200010000200010002eaba8,0x80000080800000080800000802000000c00008001000008004000080010000080010002000100000000900020000000200008000a000000088000000081004000200011200db1a8,0x824088220481,0x24008220481,0x824088220481,0x0,0x0,0x124042208481],
[0x424000200481,0x124042208481,0x24000200481,0xf33cc1e603cc7981e60b640f30f303cc3cc03cc79879a0461e601e60007991167983cc0f307983cc3cb6,0x24000200481,0xf33cc1e607987981e60b640f30f303cc3cc03cc79879a0461e601e60007991167983cc0f307983cc3cb6,0x0,0x424000200481,0x3cc007d4c0079bcc00b6403ccf303cc3cc03cc1e600097e1e601e600079897e0001e7e6007983ee5fb6,0x424000200481,0x798007b660079f9800b6403ccf303cc3cc03cc1e600097e1e601e600079897e0001e9cc0079844d4bb6,0xf35b21e607987981e60b640f30f303cc3cc03cc79879a0461e601e6000799116b643cc0f307983cc3cb6,0x24000200481,0x4000100108000200000004000100002000080ce3,0x0,0x0,0x1340c8224481,0x20108000200004004100100002100080ce3,0x1340c8224481,0x824088220481,0x224088228481,0x108000200004004100100002100080ce3,0x224088228481,0x200108040200004004100100002100080ce3,0x4000000090004000240000000800010000c000080010000200040000800100000800400020001000480020000a00000002000080010001000048002000200010000200010002eaba8,0x0,0x4000000090000000240000000800000000c000080010000200040000800100000800400020001000480020000200000002000080010000000048002000200010000200010002eaba8,0x0,0x824088220481,0x24008220481,0x824088220481,0x0],
[0x0,0x80002108002200000004200100002000080ce3,0x0,0x100004108002200000004200100002000080ce3,0x108000200000004200100002000080ce3,0x0,0x798079f9807987980b6403ccf303cc3cc03cc3cc00088b1e603cc00079897e0001e6f3007983ce19b6,0x400010108004200000004200100002000080ce3,0x0,0x0,0x3cc007d4c0079bcc00b6403ccf303cc3cc03cc3cc00088b1e603cc00079897e0001ed98007983f9c3b6,0x0,0x798007b660079f9800b6403ccf303cc3cc03cc3cc00088b1e603cc00079897e0001e9cc0079844d4bb6,0x2004080108004200002004200102002080080ce3,0x108000200000004200100002000080ce3,0x4000100108000200004004200104002100080ce3,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_151 : TreeBound (n := 4) 107 (programCode 0x4e29076215) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8004200108040200008004200100202008080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_152 : TreeBound (n := 4) 107 (programCode 0x4e29076216) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8000a00018020200408040a00010442008040304]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_153 : TreeBound (n := 4) 107 (programCode 0x4e29076217) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8004200108040200008004200100402010080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_154 : TreeBound (n := 4) 107 (programCode 0x4e29076218) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0xf3000222c00088b0000b6c9a300003cc00003ccf307a952c0000f3000079fb69cc0fa98003cc1e6110c6,0xf3000222c00088b0000799023000408c000408cf307a952c001f53000079fb69cc1ed98003cc1e611156,0x0,0x1008d03188642,0x1008d01188642,0x1008100088442,0x1008d01188642,0x1008d03188642,0x1008902088442,0x1008902088442,0x1008902088442,0x1008d03188642,0x1dcd650000430e234000059682f00007ea8ed400010c388d00000eee25e0b35b1cd65077360b3594ee6b281dcd82cd6507735b1cd651dce536b2801dcd65003bd664ca00773d076826b28077359400ee6d0893b64ca3b9acbdcd65eea6c2ca0007824ed93281dcd65eee2652e7e64a,0x8002200100140004101004040100102004080ce3,0x0,0x0,0x40000001100000000c0000000900000000e0001000100000800100008000400008002000200101000000090000000210000000802020100008000100008200000020001000087f1a8,0x0,0x0,0x0,0x1008503188642,0x1008501188642,0x1008500188442,0x1008501188642,0x1008503188642,0x1008502188442,0x1008502188442,0x1008502188442,0x1008503188642,0x1008504388f02,0x0],
[0x1008504388f02,0x0,0x0,0x0,0x0,0xf300012fc0002d90000b640798f300f3003cfccf307983cc0002d9000079fb66001ed98003cc1e610f46,0x80006000102100084080006000104400100804e4,0xf300012fc0002d90000b640798f300f3003cfccf307983cc0002d9000079fb66001ed98003cc1e610f46,0x80006000104100104080002000104400100804e4,0xf30000b6400088b0000798408c00f6cc000408cf30000b64001f53000079bea6000fa98003cc1e610856,0xf30000b6400088b00007a733cc0f33cc00f33ccf30000b6403ccf3000079bea6000fa98003cc1e7f6856,0x0,0xf522c1e600007980000b6c9a300003cc00003ccf307a952c0000f3000079fb69cc0fa98003cc1e6110c6,0x3cc1e60f307980f30b6c9a3000f6cc000408cf307b0eac001f53000079fb69cc1ed98003cc1e611156,0x0,0x0,0xf300012fc0001e6f300b640798f300f3003cfccf307983cc0002d9000079fb66001ed98003cc1e610f46,0xf300f31e601e67980b640798f37a73001e9ccf30798b640002d9000079fb66001ed9f983cc1e610f46,0xf300012fc0001e6f300b640798f300f3003cfccf307983cc0002d9000079fb66001ed98003cc1e610f46,0x1e600f379801e6f300b640798f4e6f3003cfccf307983cc0002d9000079fb66001ed98003cc1e610f46,0xf615c1e63cc07980f30b70663000f6cc000408cf307b0eac001f53000079fb69cc1ed98003cc1e611156,0x800420010810020408010200010440010182ce4,0x4000100100004080002000104400100804e4,0x10004400100100404080102000104400102834e4,0xf4023130008c1e6f300b67d398f40323003cfccf307a04e40002d9000079fb66001ed9f983cc1e610f46,0x20004800120100804080006000104400100804e4,0xf300013039801e6f300b640798f4e6f3003cfccf307983cc0002d9000079fb66001ed98003cc1e610f46,0x40005000140101004080006000104400100804e4,0xf30000b6400088b00007b663cc079bcc01e63ccf30000b640f30f3000079bea6000fa98003cc1eda8856,0xf300012fc0002d90000b640798f300f3003cfccf307983cc0002d9000079fb66001ed98003cc1e610f46,0x80006000120100804080006000104400100804e4,0xf300012fc0002d90000b640798f4e6f3003cfccf307983cc0002d9000079fb66001ed98003cc1e610f46],
[0x80006000140101004080006000104400100804e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_219 : TreeBound (n := 4) 107 (programCode 0x4e29076219) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8000200108040200008004200100802020080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_220 : TreeBound (n := 4) 107 (programCode 0x4e2907621a) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8000a00018020200408040a00011048020102904]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_221 : TreeBound (n := 4) 107 (programCode 0x4e2907621b) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1340d0210481,0x424010210481,0x1340d0210481,0x0,0x3cc1e60f307981e60b640f30f303cc3cc03ccf34459e601e60000000b6511688b00000007983cc3cb6,0x1e607987987981e60b6403ccf303cc3cc03cc000f307991160000f3079897e0f30000f307983cc33b6,0x0,0x0,0x0,0x1e607987987981e60b6403ccf303cc3cc03cc00798079fb66000798079897e0f30003cc07983ccad36,0x0,0x0,0x3cc1e60f307981e60b640f30f303cc3cc03ccf3445a22c1e60000f30b6511688b0000f307983cc3cb6,0x0,0x0,0x0,0x0,0x1e607987987981e60b6403ccf303cc3cc03cc1e600097e1e601e600079897e0f30000f307983cc33b6,0x0,0x1e607987987981e60b6403ccf303cc3cc03cc3cc00088b1e603cc00079897e0f30000f307983cc33b6,0x224090210481,0x400808018020200408040a00018442008040304,0x224090210481,0x0,0x1e601e63cc0798f300b6c9a300003cc00003ccf307a952c0000f30000b6bb69cc00798003cc1e6110c6,0x1e601e67980798f300799023000408c000408cf307a952c001f53000079fb69cc0fa98003cc1e611156,0x0,0x0,0x1e600f379801e6f300b640798f300f3003cfccf307983cc0002d90000b641e60f4ed98003cc1e610f46,0x4004100102100084080006000180400100804e4,0x1e600f379801e6f300b640798f300f3003cfccf307983cc0002d90000b641e60f4ed98003cc1e610f46],
[0x4004100104100104080002000180400100804e4,0xf30079bcc0798f300798408c00f6cc000408cf30000b64001f53000079bea60f3fa98003cc1e610856,0x4004100108100204080102000108400100824e4,0x1e600f379801e6f300b640798f4e6f3003cfccf307983cc0002d90000b641e60f4ed98003cc1e610f46,0x4004100110100404080102000110400100824e4,0x4004100100100104080002000180400100804e4,0x4004100120100804080006000104400100804e4,0x1e600f379801e6f300b640798f4e6f3003cfccf307983cc0002d90000b641e60f4ed98003cc1e610f46,0x4004100140101004080006000104400100804e4,0x424010210481,0x1000820018020200408040a00019048020102904,0x424010210481,0x798007b660079f9800b6403ccf303cc3cc03ccf30000b641e60f300007b67e60f3079801e60f3812d56,0x824090210481,0x24010210481,0x824090210481,0x0,0x20000001080000000a0000000820000000c00210001000008000001080000004080040003001100000000c0000000100000000e00030000800000002000200002000100008017f3a8,0x421010210481,0x0,0x0,0x798001116000222c000b640798f300f30f303ccf307983cc0002d90000b641e607987980f307983cdc46,0x108000000008004200101002040080ce3,0x798001116000222c000b640798f300f30f303ccf307983cc0002d90000b641e607987980f307983cdc46,0x108000000008004200101002040080ce3,0x421010210481,0x20010210481,0x421010210481,0x20010210481,0x822090210481,0x20010210481,0x822090210481],
[0x20010210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_286 : TreeBound (n := 4) 107 (programCode 0x4e2907621c) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0xf30000b6400088b0000b6403ccf303cc3cc03ccf30000b641e60f300007b67e60079f9801e60f3812d56]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_287 : TreeBound (n := 4) 107 (programCode 0x4e2907621d) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8004200108040200008004200102002080080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_288 : TreeBound (n := 4) 107 (programCode 0x4e2907621e) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8000a00018020200408040a00014060080402104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_289 : TreeBound (n := 4) 107 (programCode 0x4e2907621f) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8000200108040200008004200104002100080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_290 : TreeBound (n := 4) 107 (programCode 0x4e29076220) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x40000001100000000c0000000900000000c00210001000008000001080000004080040003001100000000c0000000100000000a00030000800000000800200002000100008017f1a8,0x0,0x80002100002020008004200100802020080ce3,0x421010210481,0x100004100002020008004200100002020080ce3,0x0,0x0,0x8000040010000080100000800100000800084000000108000001080000001080040002408100000000c0000400900000000a0002000020001020200020080200010000811753a8,0x0,0x3b9aca01dce536b28077360b35940ee729b5940ee6b9f35940ee6b37224d4a0003c89352800079126a500079126a5000079126c2cd65ee7a1625d943bd68297650000165a0bc3b9bd6388d000012a05f5b9acaee6b36e6b28773597bd66c3d5a2e7a0f29b597b9acbdebe173cba,0x421010210481,0x21010210481,0x421010210481,0x421010210481,0x821090230481,0x21010210481,0x821090230481,0x421010210481,0x0,0x6002000110000000080010000800040000e00210001000008000001080000004080040003001100000000c0000000100000000a00030010800000000800200002000100008017f1a8,0x2000100001000080010000800010000e00210001000008000001080000004080040003001100000000c0000000100000000a00030010800000000800200002000100008017f1a8,0xa004000080100000200840000203000000800400008020000022090000028240400000401000000804000008010000008000000004100080040400000100000800100108573a7,0x0,0x0,0x20000100010000080100000800100000c02010001000008000010080000040080040002001100000000c0000000300000000a00030000800010000800200002000100008017f1a8,0x0,0x20000100080000080080000800200000c02010001000008000008080000020080040002001100000000c0000000100000000a00030000800000000800200002000100008017f1a8,0x6002000100001000080000000800010000e00210001000008000000080000000080040003001100000000c0000000100000000a00030010800000000800200002000100008017f1a8,0x200000100100000081000000801000000c20010001000008000100080000400080040003001100000000c0000200100000000a0003100080000080080020000200010000c417f1a8,0x4000000100000000080000000800000000c00010001000008000000080000000080040002001100000000c0000000100000000a00030000800000000800200002000100008017f1a8,0x0],
[0x6002000100000000080010000820000000e00210001000008000001080000004080040003001100000000c0000000100000000a00030010800000000800200002000100008017f1a8,0x2000000101000000090000000810000000e00010001000008001000080004000080040002001100000000c0000000300000000a00030000800010000800200002000100008017f1a8,0x8002004080000100200000840200003000000a00400008020000022084000028210400000401000000804000008010000008008000004100080040600000100000800100108573a7,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x80006000101100044002010080140011008442e4,0x0,0x80006000101100044004020100140021008844e4,0x0,0x80006000101100044008008200140009008040e4,0x0,0x80006000101100044010008400140009008040e4,0x0,0x0,0x0,0x0,0xf300012fc0002d90000b640798f300f30f303ccf307983cc0002d9000097e1e607987980f307983cdc46,0x80006000102100084080006000140401008040e4,0xf300012fc0002d90000b640798f300f30f303ccf307983cc0002d9000097e1e607987980f307983cdc46,0x80006000104100104080002000140401008040e4,0x0,0x80002100802020008004200100802020080ce3,0x421010210481,0x100004100802020008004200100002020080ce3,0x0,0x0,0x8000040010000080100000800100000881144000000108000801080000001080040000408b00000000c0000400900000000a0002000020001020200024080200010000811753a8],
[0x0,0x20000040020000080200000800200000882104000000108000801080000001080040000410900000000c0000400900000000a0002000020001040200024100200010000821753a8,0x421010210481,0x21010210481,0x421010210481,0x421010210481,0x821090230481,0x21010210481,0x821090230481,0x421010210481,0x0,0x80002100002020008004200100802020080ce3,0x420010200481,0x100004100002020008004200100002020080ce3,0x0,0x80005020108100204080102000140401008140e4,0x2004080108100204080102000140401008442e4,0x80005000108100204080102000140401008040e4,0x4004100108100204080102000140401008864e4,0x420010200481,0x20010200481,0x420010200481,0x20010200481,0x821090230481,0x20010200481,0x821090230481,0x20010200481,0x0,0x6002000110000000080010000800040000e00210001000008002000080000004080040003001100000000c0000000100000000a00030010800000002000200002000100008017f3a8,0x421010210481,0xa004000080100000200840000203000080000400800020002002090002008240400000401000000804000008010000008000000004108000040400000100080000100108573a7,0x0],
[0xf300012fc000222c000b640798f300f30f303ccf307983cc0002d9000097e1e607987980f307983cdc46,0xf300f31e601e67980b640798f37a73001e9ccf30798b640002d9000097e1e6079897e0f307983cdc46,0xf300012fc000222c000b640798f300f30f303ccf307983cc0002d9000097e1e607987980f307983cdc46,0x1e600f379801e6f300b640798f4e6f3003cfccf307983cc0002d9000097e1e607987980f307983cdc46,0x421010210481,0x21010210481,0x421010210481,0x421010210481,0x821090230481,0x21010210481,0x821090230481,0x421010210481,0x0,0x0,0x420010200481,0x0,0x0,0x80005020110100404080102000140401008140e4,0x2004080110100404080102000140401008442e4,0x80005000110100404080102000140401008040e4,0x4004100110100404080102000140401008864e4,0x420010200481,0x20010200481,0x420010200481,0x20010200481,0x820090220481,0x20010200481,0x820090220481,0x20010200481,0xf300012fc0002d90000b640798f300f30f303ccf307983cc0002d9000097e1e607987980f307983cdc46,0x80006000120100804080006000140401008040e4,0xf300012fc0002d90000b6407996c80f30f303ccf307992fc0002d9000097e1e60798b640f307983cdc46],
[0x80006000140101004080006000140401008040e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_2 : TreeBound (n := 4) 107 (programCode 0x4e290762) := by
  conv in programCode _ => reduce
  exact branchFour (k := (0,1)) (by decide +kernel) part003_3 part003_4 part003_5 part003_6 part003_151 part003_152 part003_153 part003_154 part003_219 part003_220 part003_221 part003_286 part003_287 part003_288 part003_289 part003_290

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_419 : TreeBound (n := 4) 107 (programCode 0x4e290763) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 4)
    (a := List.flatten [
[0x8000a00028040200088004200108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_421 : TreeBound (n := 4) 107 (programCode 0x4e29076411) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0xf307983cc0002d90798b64001f5307983cc1e7f53001e9cc01e6f3001e6003ccf303cc3cc03cde7032b5]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_422 : TreeBound (n := 4) 107 (programCode 0x4e29076412) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x40002000300008000400000003000080000000600000001001000012000000018010400000201000000804000008010000008041080010001000010400800100050000100108713a7,0x8000a000200900024080006000200c00020100e4,0x0,0x1008501084222,0x1008501084222,0x1008501084222,0x1008501084222,0x1008501084222,0x1008d02184642,0x1008501084222,0x1008d02184642,0x1008501084222,0x1008504084222,0x0,0x1008504084222,0x0,0x0,0x200000000000000008000000050101010200000000c0000000800000000000001020000000080000000800000001000000020000000000000010800000000200000000000010100000000000000205010101000000008000000000000000404000000000000008140404040000000080000200000000001100000000000000012000000010000000000200000200000000010000008000000000400000400000000002000008000000000200000080000000002000001000000000040000010000000000400000000000000008000a020202000001000000c00000000040000000000000002000000500000000040000010000000000400000010000000008000002000000000080000490403eedb77ac6d2f,0x0,0x0,0x1008501084222,0x1008501084222,0x1008501084222,0x1008501084222,0x1008501084222,0x1008502184642,0x1008501084222,0x1008502184642,0x1008501084222,0x1008504084222,0x0],
[0x1008504084222,0xf30a713cc0b64f302d95389e605b2a7116c8b643cc03cc7980799e601eb38803e15b80f32d901ebffb45,0x0,0xf300003cc0f30f303cc0001e607987981e6000079801e7e60079bcc01e600003cc0000f30f301e64d995,0x0,0x0,0x1008501084222,0x1008501084222,0x1008501084222,0x1008501084222,0x1008501084222,0x1008d02184642,0x1008501084222,0x1008d02184642,0x1008501084222,0x8001200100240008100804220100802020080ce3,0x0,0x80006000220100804008008400200900024121a4,0xf3088f08c07a82302d9003ea6000840f601f1ececc03cc7980799e601eb49963e19fd8f32d901ec074c5,0x0,0x159fd80000015f657600000057d95d80000015f657600000016f9d580000005be75600000006c1f3c69dfd60567f704d81d8159fdc0ea57ec00000572c5ec0000015aaa7ec00000568a2fed59fdabecaee323bf0159fd857d95d80000002b3fb0c29e9816f9d580000002b3fb0159fd80567f62becaee06fc40acfec00acfec0614f4e06fc40567f602b3fb00567f60acfec00567f60acfec1dbbc298ac,0x0,0x8000a00020210008408000a000200c00020100e4,0xf307983cc001f530798003cde600fa98003ea60f3001e9cc01e6f3001e63cc01e6f30079bcc01e703855,0x8000a000204100104080002000200c00020100e4,0x0,0x1008501084222,0x1008501084222,0x1008501084222,0x1008501084222,0x1008501084222,0x1008d02184642],
[0x1008501084222,0x1008d02184642,0x1008501084222,0x1008504084222,0x0,0x1008504084222,0xf307b69cc08127302d901e7e6003d68f60f3bddbcc03cc7980799e601eb47b03e19840f32d901ebffb45,0x0,0x8004200800840020104004100100802020080ce3,0x0,0x0,0x16c8000f4e60016c803cc000f30007d4c1e60f3001e9cc01e6f3001e63cc01e6000079bcc01e703855,0x808020208100204080102000200c00020100e4,0x25f80007b660025f803cc000f30007d4c1e60f3001e9cc01e6f3001e63cc01e6000079bcc01e703855,0x0,0x0,0x0,0x80008020208100204080102000200c00020100e4,0x0,0x0,0x0,0x8008000208100204080102000200c00020100e4,0x0,0x0,0x0,0x808020208100204080102000200c00020100e4,0x0,0x0,0x6040000018000000100400000180000200000400200001002000004002008010400000201000000804000008010000008041080010001000010400800100050000100108713a7,0x808020200900024080006000200c00020100e4,0x0,0x0],
[0x0,0x1e601e61e607987981303a730f300f3001e9ccf3079a22c0004bf0000f3111679816c80003cc1e61df6,0x80008020200900024080006000200c00020100e4,0x1e601e67980798f301303a730f300f3003cfccf3079a22c0000f30000f3111679816c80003cc1e61df6,0x0,0x0,0x8000200100004080002000200c00020100e4,0x0,0x0,0x2000880022010080408000a000200c00020100e4,0x808020200900024080006000200c00020100e4,0x4000900024010100408000a000200c00020100e4,0x0,0x0,0x808020210100404080102000200c00020100e4,0x0,0x0,0x0,0x0,0x80008020210100404080102000200c00020100e4,0x0,0x0,0x0,0x10008000210100404080102000200c00020100e4,0x0,0x0,0x0,0x808020210100404080102000200c00020100e4,0x0,0x0,0x8014600012040080090084002100c82020080ce3,0x8010200002040080000004020100002020080ce3],
[0x8016a000220400801a0104004100d02020080de3,0x400000011000000044000000110000000140021000100084000400008000000408000002200100008000400020000000020001000220010000800000001000080001000200017ffa8,0x8011200042040080140204008100a02020080ee3,0x8010200002040080000004000100002020080ce3,0x8012200082040080180404010100c02020080ce3,0x0,0x8010200102040080100804020100802020080ce3,0x8010200002040080000004200100002020080ce3,0x0,0x0,0xf3088b3cc0b64f302d90f31e601e6a710798b643cc03cc7980799e601eb38803e15b80f32d901ebffb45,0x0,0x0,0x0,0x8000a00022010080408000a000200c00020100e4,0x40002000100008000400004001000080002000200002000100020002000020008000400000201000000804000008010000008048000010001000010480000100050000100908713a7,0x8000a00024010100408000a000200c00020100e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_567 : TreeBound (n := 4) 107 (programCode 0x4e29076413) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0xf307983cc0002d907992fc001f5307983cc1e7023001e9cc01e6f3001e6003ccf300f33cc0799e7032b5]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_568 : TreeBound (n := 4) 107 (programCode 0x4e29076414) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x8000600018040200080084002100082002080ce3,0x8000200008040200000004020100002000080ce3,0x8000200028040200080104004100002004080ce3,0x8000200008040200000004000100002000080ce3,0x8001200048040200100204008100202008080ce3,0x8000200008040200000004000100002000080ce3,0x8002200088040200100404010100402010080ce3,0x0,0x1008d02184642,0x1008502184642,0x1008d02184642,0x1008502184642,0x1008d02184642,0x1008902084642,0x1008d02184642,0x1008902084642,0x1008d02184642,0xf3000222c00088b0000f4e67980799e600f33cc01e7e60079bd398f300f30f33cc044691607987d6ff36,0x0,0xf300012fc00088b0000f4e67980f31e601e63cc00f4e60079f9f98f300f30799e6044682307987d60726,0x0,0x100a102084642,0x0,0x100a102084642,0x0,0x1008501084222,0x1008501084222,0x1008501084222,0x1008501084222,0x1008501084222,0x1008901084222],
[0x1008501084222,0x1008901084222,0x1008501084222,0x0,0x0,0x0,0x400000011000000044000000090000000140021000100004000400002000000408004002200110000800000000000000020001000220010000800000001000080002000200017fe28,0x100a101084222,0x40002000100000080400004001000002802000200002000100020002000020009000004000200010000800100008000100008040000010001000010080000100050000100908713a7,0x100a101084222,0x0,0x1008504084222,0x1008504084222,0x1008504084222,0x1008504084222,0x80006000220100804008008200200900044121a4,0x1008904084642,0x1008504084222,0x1008904084642,0x1008504084222,0xf300012fc00088b0000f4e67980799e600f33cc0799e601e6b6b9bcc00f307a730044b41307987dcac26,0x0,0xf300012fc00088b0000f4e67980f31e601e63cc0799e601e679f9bcc00f307b6600450f3307987e44426,0x8000200002040080000004200100002000080ce3,0x100a1040852a2,0x8000200004040100000004200100002000080ce3,0x100a1040852a2,0x0,0xf3003cfcc000a71005b2003cde6044580005b2007981e60f31e607981e61e601e604bf3ced901e7037c5,0xf3000222c00088b0000f30408c001023000408c001e61e6079888b0000f30f3079844580007987985756,0xf3003cfcc0004bf003db303cde6025f800097fe63cc1e61e61e607981e61e600f301e6799ed99e703345,0xf3003cfcc0000f3003cc1e600000079801e7e6003cc1e61e61e607981e61e600f30000799e601e703345],
[0x0,0x0,0x40000152100000100400000041000000800020212000080020000042000000208000020001000080004000040008000200008002a400100020000400008000200100001001087fca7,0x80006000202100104000002000200c00040100a4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1008504084222,0x1008504084222,0x1008504084222,0x1008504084222,0x80006000220100804008008400200900044121a4,0x1008904084642,0x1008504084222,0x1008904084642,0x1008504084222,0xf300012fc00088b0000f4e67980799e600f33cc0799e603ccb6b9f9800f307a73004495b307987dcac26,0x0,0xf300012fc00088b0000f4e67980f31e601e63cc0799e603cc79f9f9800f307a730044d27307987dcac26,0x0,0x100a1040852a2,0x0,0x100a1040852a2,0x0,0x14c168224501,0x0],
[0x14c168224501,0x844108220501,0x2541c8228501,0x844108220501,0x2541c8228501,0x0,0x79fb660f381183ced93cc2a3e730a8f9cc0bddbcc03cc7980799e601e9db303d008c0f46c801ebffb45,0x1000000804000002010000010010000014000080010000200040000800100000800100020001450480020400200000000000100010020000048202000200000000200040442eaba8,0xf37d4c3cc6a5079ad93cc0000f302d93cc2c9d1e601e6f300f31e601e9ea603cf5280f46c801ed2f5c5,0x0,0x844108220501,0x844108220501,0x844108220501,0x44108220501,0x0,0x82002088002200100404020100402010080ce3,0x404000200481,0x102004088002200100404020100402010080ce3,0x4000200481,0x0,0x4000200481,0x0,0x0,0x404000200481,0x79800f4e60079bcc012fc0798f301e63cc03cc3cc7980f31e67b66000f307a730044b41307987dcac26,0x404000200481,0x79800f6cc0079f98012fc0798f301e63cc03cc3cc7980f31e67b66000f307b6600450f3307987e44426,0x804000200481,0x4000200481,0x804000200481,0x4000200481,0x0],
[0x14c168224501,0x20808000200004004100100002100080ce3,0x14c168224501,0x844108220501,0x2541c8228501,0x844108220501,0x2541c8228501,0x200808040200004004100100002100080ce3,0x0,0x0,0xf3bdd83cc1e6079bcc3cc0000f300003cc2f7679801e7e601e63cc01ebeec03ccf300f4e6001e703df5,0x0,0x844108220501,0x844108220501,0x844108220501,0x44108220501,0x0,0x104040200481,0x0,0x104040200481,0x4000200481,0x204080200481,0x4000200481,0x204080200481,0x0,0x0,0x79800f4e60079bcc012fc0798f301e63cc03cc3cc7981e61e67d4c000f307a73004495b307987dcac26,0x0,0x79800f6cc0079f98012fc0798f301e63cc03cc3cc7981e61e67d4c000f307a730044d27307987dcac26,0x844108220501,0x4000200481,0x844108220501],
[0x4000200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_729 : TreeBound (n := 4) 107 (programCode 0x4e29076415) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x8000600018040200080084002100202008080ce3,0x8004200108040200000804020100202008080ce3,0x8000a00028040200080104004100202008080ce3,0x8000200008040200000004000100202008080ce3,0x8001200048040200100204008100202008080ce3,0x8000200008040200000004000100202008080ce3,0x8002200088040200100404010100202008080ce3,0x0,0x1008d0218c642,0x100850218c642,0x1008d0218c642,0x100850218c642,0x1008d0218c642,0x100890208c642,0x1008d0218c642,0x100890208c642,0x1008d0218c642,0xf300012fc0004bf0000f3f33cc0f33cc00f33cc00f300f33cfcc00f300f3097e01e6007983cfcc1f86b6,0x0,0xf300012fc00088b0000f4e67980f31e601e63cc00f4e60079f9f98f301023001e9df94d7c69fbe360726,0x0,0x100a10208c642,0xf307983cc0798f307980f307983cc7980f31e603cc01e9cc01e63cc01e601e61e61e607981e61eacf855,0x100a10208c642,0x8004200108040200000804020100202008080ce3,0x0,0x80006000201100044008008200220008844221a4,0xf300012fc0004bf0000f30408c00408c000408c03cc00f6ce22c03cc012fc97e01e6000798408c1e93b6,0x0,0x8000a000201100044008008200220008044021e4,0x100a1040a10a2],
[0x10089040a94c2,0x100a1040a10a2,0x10089040a94c2,0x80006000201100044008008200220008844221a4,0xf300012fc0004bf0000f3f33cc0f33cc00f33cc03cc00f6cc3cc03cc00f3097e01e601e60f33cc225fb6,0x0,0xf300012fc0004bf0000f4e63cc079bcc01e63cc03cc00f6ccf3003cc00f3097e01e603cc1e63cc9fabb6,0xf300012fc0004bf0000f3003ccf303cc00003cc03cc00f6cde6003cc012fc1e601e600000003cc1e93b6,0x100a1040a10a2,0xf300012fc0004bf0000fa983ccf303cc07983cc03cc00f6cde63cfcc01375a22c1e60f307983cc1e93b6,0x100a1040a10a2,0x0,0x124044208481,0x424004208481,0x124044208481,0x424004208481,0x224084208481,0x24004208481,0x224084208481,0x0,0x424004208481,0x0,0x424004208481,0x0,0x824084208481,0x24004208481,0x824084208481,0x0,0x0,0x80006000201100044008008400220008844221a4,0x0,0x0],
[0x8000a000201100044010008400220008044021e4,0x100a1040a10a2,0x10089040a94c2,0x100a1040a10a2,0x10089040a94c2,0x80006000200100044008000400220000804221a4,0xf300012fc0004bf0000f3f33cc0f33cc00f33cc079800f4e63cc079800f3097e079807983ccf30a743b6,0x0,0xf300012fc00088b0000f4e67980f31e601e63cc0799e603cc79f9f980102300f3449eb7cfbc892dcac26,0x0,0x100a1040a10a2,0x0,0x100a1040a10a2,0x8010200408040200402004080100202008082ce3,0x0,0x1340c6208481,0x404000208481,0x1340c6208481,0x4000208481,0x224084208481,0x4000208481,0x224084208481,0x0,0x404000208481,0x3cc00f6cc003cfcc012fc03ccf303cc3cc03cc1e60011161e601e60012fc1e60001e7e60f3003ee5fb6,0x404000208481,0x79800f4e6003d398012fc03ccf303cc3cc03cc1e60011161e601e60012fc1e60001e9cc1e60044d4bb6,0x804000208481,0x4000208481,0x804000208481,0x4000208481,0x8020200808040200804004100100202008084ce3],
[0x0,0x1140c2208481,0x0,0x1140c2208481,0x4000208481,0x204080208481,0x4000208481,0x204080208481,0x0,0x0,0x3cc00f6cc003cfcc012fc03ccf303cc3cc03cc3cc0010231e603cc0012fc1e60001ed983cc003f9c3b6,0x0,0x79800f4e6003d398012fc03ccf303cc3cc03cc3cc0010231e603cc0012fc1e60001e9cc1e60044d4bb6,0x844108208501,0x4000208481,0x844108208501,0x4000208481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_842 : TreeBound (n := 4) 107 (programCode 0x4e29076416) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x8000600018040200080084002100402010080ce3,0x8000200008040200000004020100002000080ce3,0x8000a00028040200080104004100402010080ce3,0x8000200008040200000004000100002000080ce3,0x0,0x1008d03188642,0x1008503188642,0x1008d03188642,0x1008503188642,0x1008d03188642,0x1008903088642,0x1008d03188642,0x1008903088642,0x1008d03188642,0xf3000f6cc007a73000f6cc007a76d39800f307980799e60799e600799e60f301e63cc0798f301e740455,0x0,0xf3000f6cc0000f3000f6cc0000f30798000007980799e60799e600799e600001e63cc0798f301e703855,0x8011200042040080140204008100802028080ee3,0x100a103088642,0x1dcd6500077acc997b9acbdcd6500077acc9943b9ae7cd650025429b168b9aca1dcd73e6b29dcd653b9acbdcd73e6b287735940ee6b283b9b059acaee6c166b2803b9b059aca3b9b059aca03b9b05a23d594003b9ad1735943ba23d59403b9ad1735943b9ae7cd650ee8ad9decd9d9,0x100a103088642,0x8000200008040200000004000100002000080ce3,0x0,0x1008d02188442,0x1008502188442,0x1008902088442,0x1008502188442,0x1008d02188442,0x1008902088442,0x1008902088442,0x1008902088442],
[0x1008d02188442,0x0,0x0,0x0,0x8012200082040080180404010100802030080ce3,0x100a102088442,0x400000001000000104000100010000001008002000080000000080020000200002000008008000080008000080080000200080010000040000000400100000400400001001085b1a7,0x100a102088442,0x0,0x1008d02188442,0x1008502188442,0x1008902088442,0x1008502188442,0x1008d02188442,0x1008902088442,0x1008902088442,0x1008902088442,0x1008d02188442,0xf300012fc0004bf0000f3f33cc0f33cc00f33cc00f300f33cfcc00f300f32046001e607981e63ce16cb6,0x0,0xf300012fc00088b0000f4e67980f31e601e63cc00f4e60079f9f98f300f33cc1e60faaec81e61e9e0726,0x0,0x100a102088442,0x0,0x100a102088442,0x8000200108040200000804020100002000080ce3,0x0,0x80006000201100044008008200202008080603a4,0x1008504388f02,0x0,0x1008504388f02,0x100a9040894c2],
[0x1008904088442,0x1008904088442,0x1008904088442,0x80006000201100044008008200202008080603a4,0xf300012fc0004bf0000f3f33cc0f33cc00f33cc03cc00f6cc3cc03cc00f32046001e61e601e63ce445b6,0x0,0xf300012fc00088b0000f4e67980f31e601e63cc0799e601e679f9bcc00f33cde600fb55d81e61ead3726,0xf300012fc0004bf0000f3003ccf303cc00003cc03cc00f6cde6003cc00f32046001e600001e63cc219b6,0x100a1040894c2,0xf300012fc0004bf0000f379bccf303cc0079bcc03cc00f6cde63cfcc00f32049cc1e60f301e63cc219b6,0x100a1040894c2,0x0,0x124044208481,0x424004200481,0x124044208481,0x424004200481,0x0,0x24004200481,0x0,0x0,0x424004200481,0x0,0x424004200481,0x0,0x0,0x24004200481,0x4000100208000200001004040100002000080ce3,0x0,0x0,0x80006000201100044008008400202008080603a4,0x1008504388f02,0xf300012fc00088b0000f6cc79909c9e603cc3cc07a17e03cc79f9f9800f33cde600fb55d81e61ead3726],
[0x1008504388f02,0x100a9040894c2,0x1008904088442,0x1008904088442,0x1008904088442,0x80006000200100044008000400202000080603a4,0xf300012fc0004bf0000f3f33cc0f33cc00f33cc079800f4e63cc079800f32046001e679801e63cefa9b6,0x0,0xf300012fc00088b0000f4e67980f31e601e63cc0799e603cc79f9f9800f33ccf300fb19181e61ea59f26,0x0,0x100a1040894c2,0x0,0x100a1040894c2,0x0,0x90402408002200482004080102002090082ce3,0x2004020408010200402004080102002080082ce3,0x908044280012004e200408010210109c082fa3,0x844108220501,0x4040000080981800081606000105000400036661000001804000166610000581804000020080000400080000400100000806ccc00080b03000102ccc00080b03000102ccc61e67,0x844108220501,0x0,0x0,0x804020408010200402004080102002080082ce3,0x0,0x1008040408000200402004080102002080082ce3,0x0,0x844108220501,0x844108220501,0x844108220501,0x44108220501,0x0,0x0],
[0x404000200481,0x0,0x4000200481,0x200008108004200000804000100002000080ce3,0x4000200481,0x400010108004200000804000100002000080ce3,0x0,0x404000200481,0x3cc00f6cc003cfcc012fc03ccf303cc3cc03cc1e60011161e601e6000f32046001e61e601e63ce445b6,0x404000200481,0x79800f4e6003d398012fc03ccf303cc3cc03cc1e60011161e601e6000f32046001e63cc01e63d4331b6,0x804000200481,0x4000200481,0x804000200481,0x4000200481,0x8000200808040200004004100100002000080ce3,0x0,0x80002008002200000004000100002000080ce3,0x0,0x100004008002200000004000100002000080ce3,0x4000200481,0x200008008004200000004000100002000080ce3,0x4000200481,0x400010008004200000004000100002000080ce3,0x0,0x0,0x3cc00f6cc003cfcc012fc03ccf303cc3cc03cc3cc0010231e603cc000f32046001e679801e63cefa9b6,0x0,0x79800f4e6003d398012fc03ccf303cc3cc03cc3cc0010231e603cc000f32046001e63cc01e63d4331b6,0x844108220501,0x4000200481,0x844108220501],
[0x4000200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_1003 : TreeBound (n := 4) 107 (programCode 0x4e29076417) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x8000600018040200080084002100402010080ce3,0x8004200108040200000804020100402010080ce3,0x8000a00028040200080104004100402010080ce3,0x8000200008040200000004000100402010080ce3,0x8001200048040200100204008100402010080ce3,0x8000200008040200000004000100402010080ce3,0x8002200088040200100404010100402010080ce3,0x0,0x1008d02188442,0x1008502188442,0x1008902088442,0x1008502188442,0x1008d02188442,0x1008902088442,0x1008902088442,0x1008902088442,0x1008d02188442,0xf300012fc0004bf0000f3f33cc0f33cc00f33cc00f300f33cfcc00f3012fc1e6000f307983cc1e7f86b6,0x0,0xf300012fc0004bf0000f4e63cc079bcc01e63cc00f300f33db3000f3012fc1e6000f307983cc1edaa6b6,0x0,0x100a102088442,0x0,0x100a102088442,0x8004200108040200000804020100402010080ce3,0x0,0x1008104080022,0x1008504084222,0x1008104080022,0x1008504084222,0x100a1040a10a2],
[0x1008904088442,0x1008104080022,0x1008904088442,0x1008504084222,0xf300012fc0004bf0000f3f33cc0f33cc00f33cc03cc00f6cc3cc03cc012fc1e6003cc1e60f3079a25fb6,0x0,0xf300012fc0004bf0000f4e63cc079bcc01e63cc03cc00f6ccf3003cc012fc1e6007983cc1e60f3814bb6,0x8000200002040080000004200100402010080ce3,0x100a1040a10a2,0x8000200004040100000004200100402010080ce3,0x100a1040a10a2,0x0,0x124044208481,0x424004208481,0x124044208481,0x424004208481,0x224084208481,0x24004208481,0x224084208481,0x0,0x424004208481,0x0,0x424004208481,0x0,0x824084208481,0x24004208481,0x824084208481,0x0,0x0,0x1008104080022,0x1008504084222,0x1008104080022],
[0x1008504084222,0x100a1040a10a2,0x1008904088442,0x1008104080022,0x1008904088442,0x1008504084222,0xf300012fc0004bf0000f3f33cc0f33cc00f33cc079800f4e63cc0798012fc1e600f307983cc1e62dc3b6,0x0,0xf300012fc0004bf0000f4e63cc079bcc01e63cc079800f4e6f300798012fc1e6007983cc1e60f3814bb6,0x0,0x100a1040a10a2,0x0,0x100a1040a10a2,0x8010200408040200402004080100402010082ce3,0x0,0x1340c6208481,0x404000208481,0x1340c6208481,0x4000208481,0x224084208481,0x4000208481,0x224084208481,0x0,0x404000208481,0x3cc00f6cc003cfcc012fc03ccf303cc3cc03cc1e60011161e601e60012fc1e6003cc1e60f3079a25fb6,0x404000208481,0x79800f4e6003d398012fc03ccf303cc3cc03cc1e60011161e601e60012fc1e6007983cc1e60f3814bb6,0x804000208481,0x4000208481,0x804000208481,0x4000208481,0x8020200808040200804004100100402010084ce3],
[0x0,0x1140c2208481,0x0,0x1140c2208481,0x4000208481,0x204080208481,0x4000208481,0x204080208481,0x0,0x0,0x3cc00f6cc003cfcc012fc03ccf303cc3cc03cc3cc0010231e603cc0012fc1e600f307983cc1e62dc3b6,0x0,0x79800f4e6003d398012fc03ccf303cc3cc03cc3cc0010231e603cc0012fc1e6007983cc1e60f3814bb6,0x844108208501,0x4000208481,0x844108208501,0x4000208481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_1116 : TreeBound (n := 4) 107 (programCode 0x4e29076418) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0xf3000222c0004bf00013049a300003cc00003ccf307a952c0000f30000f37b69cc0fa98003cc1e6110c6,0x0,0x1008503188642,0x1008501188642,0x1008500188442,0x1008501188642,0x1008503188642,0x1008502188442,0x1008502188442,0x1008502188442,0x1008503188642,0x1008504388f02,0x8000a000200900024004022000204420100804e4,0x1008504388f02,0x0,0x0,0x0,0x0,0x0,0x1008d03188642,0x1008d01188642,0x1008100088442,0x1008d01188642,0x1008d03188642,0x1008902088442,0x1008902088442,0x1008902088442,0x1008d03188642,0x1dcd65f24397e381400001dcd65f242a97859400001dcd65000ee6b287afe9e88141ebbd02800077359400000fd51da80000eea6c4ae8544459aca0ee6b639ca6d6503b9aca07735cf9aca000003ba25c1c8388b3597b9acbdcd65077360b359400000ee6b280ee6c166d0c852b7a9,0xf3003cfcc0002d9005c1303cde6016c800097ef33cc1e60f31e607981e6003ccf300f33cc0799e7032b5,0xf300012fc00088b00013572f300f33cc01e63cc079bccf6ced90079800f33ed75c1e679803cc3d4acda6],
[0x0,0x0,0x0,0x0,0x0,0x1008503188642,0x1008501188642,0x1008500188442,0x1008501188642,0x1008503188642,0x1008502188442,0x1008502188442,0x1008502188442,0x1008503188642,0x1008504388f02,0xf3003cfcc0000f3003cc1e600000079801e7e6003cc1e61e61e607981e61e600f30000799e601e703345,0x1008504388f02,0x0,0x0,0x0,0x0,0x0,0x1008901088442,0x1008901088442,0x1008900088442,0x1008901088442,0x1008d03188642,0x1008d02188442,0x1008d02188442,0x1008d02188442,0x1008901088442,0x100a9040894c2],
[0x0,0x100a9040894c2,0xf3088b3cc0b64f302d9003ea600083f1001f1643cc03cc7980799e601e9cc003db3798f301e61ebffb45,0x0,0x40002000100004000400004001000040000004200000010100000102000000108000200000200200000802000008002000008040000010000100010400000100001000100908713a7,0x0,0x0,0x1008901088442,0x1008901088442,0x1008900088442,0x1008901088442,0x1008903088642,0x1008902088442,0x1008902088442,0x1008902088442,0x1008901088442,0x1008904088442,0x0,0x1008904088442,0x0,0x0,0x0,0x0,0x0,0x1008901088442,0x1008901088442,0x1008900088442,0x1008901088442,0x1008d03188642,0x1008902088442,0x1008902088442,0x1008902088442],
[0x1008901088442,0x1008904088442,0x0,0x1008904088442,0xf3097e3cc0b64f302d9007b66001f071003d7643cc03cc7980799e601e9cc003db4e60f303cc1ebffb45,0x0,0x0,0x0,0x8000a000204100104080002000204400100804e4,0x0,0x1008d03188642,0x1008d01188642,0x1008d00188442,0x1008d01188642,0x1008d03188642,0x1008d02188442,0x1008d02188442,0x1008d02188442,0x1008d03188642,0x80006000201100044008008200202008100603a4,0x0,0x80006000200100044008000400202000100603a4,0xf307b69cc08127302d901e7e6003d68f60f3bddbcc03cc7980799e601e9cc003db6cc0f30f301ebffb45,0x0,0x0,0x0,0x0,0x0,0xf300012fc00088b0000f4e67980799e600f33cc00204600084eb980f30f33cc3cc1edaec83cc3cfefa26,0x0,0xf3000222c00088b0000f4e67980799e600f33cc003ea6000f6d3981e60f37983cc1eda7303cc3cfeff36,0x159fd80000015f657600000057d95d8000000b266b60000002c99ad80000005be756000000056aa9fb567f6000acfed59fd8002b3fb567f6000159fdab3fb000567f6acfec000567f6acfee1ca9dd1d0775a53ff61853d300000000acfec0000adabbec2b3fb00002b3fb00000000000056800d0fa54ee6346b3fb00567f60567f6000000015a28c109fd802b3fb000000002b3fb05680ba2a44ec71cac],
[0xf300012fc0004bf0000f3f33cc0f33cc00f33cc007980f379bcc007980f33ea6000f303cc3cc1e800036,0x0,0xf3000222c00088b0000f4e67980799e600f33cc01e7e60079bd398f300f37983cc1eda7303cc3cfeff36,0x400021001000004004000000010000020040002000100000000000020000000000000200010000800040001000080001000080400000101000000400000001000000001001087ffa7,0xf300012fc00088b0000f4e67980799e600f33cc0799e601e6b6b9bcc00f33ccf301edfab83cc3d069226,0x0,0xf300012fc00088b0000f4e67980799e600f33cc0799e603ccb6b9f9800f33ccf301eddc583cc3d069226,0x0,0x0,0x0,0x0,0x0,0xf522c1e600003cc00013049a300003cc00003ccf307a952c0000f30000f37b69cc0fa98003cc1e6110c6,0x420021001080080000000008000400800002002000008000000010000000020080004000010010000040040000080100000080420000101080000404000000800200001001087fea7,0x0,0x42002100100008000010000801000080000200200000800000001002000002008000400000201000000804000008010000008040000010108000040400000080020000100108732a7,0x0,0x0,0x0,0x0,0x402100001008000010000800010080000200200000800000001002000002008000400000201000000804000008010000008040000010108000040400000080020000100108732a7,0x0,0x8000200100004080002000204400100804e4,0x1002080108008000010000801000080000100200000800000001002000002008000400000201000000804000008010000008040000008108000040400000080020000100108632a7,0x0,0x0,0x0,0x0,0x0,0x0,0xf300012fc00088b0000f4e67980f31e601e63cc002046000811f980f30f33cc3cc1edaec83cc3cfefa26,0x40002001500000001400000001000000014002a014100000000000020000000200100002010000008040000008080000020080400280101000000400000000400002001001087fda7],
[0xf300012fc00088b0000f4e67980f31e601e63cc002046000fa9f981e60f33cc1e61edaec83cc3cffed26,0x4000000050000000440000000500000001008008000080008000080080000200080000080800000080004500a08001402800010008000400080800000082805000200010100a5b1a8,0xf300012fc00088b0000f4e67980f31e601e63cc00f4e6003d39f987980f33cc1e61eda3643cc3cffed26,0x0,0xf300012fc00088b0000f4e67980f31e601e63cc00f4e60079f9f98f300f33cc1e61edaec83cc3cffed26,0x400021001000004004000000010000020040002000100000000000020000000000000200010000800040001000080001000080400000101000000400000001000000001001087ffa7,0xf300012fc00088b0000f4e67980f31e601e63cc0799e601e679f9bcc00f33cde601ee55d83cc3d0e2a26,0x0,0xf300012fc00088b0000f4e67980f31e601e63cc0799e603cc79f9f9800f33ccf301ee19183cc3d069226,0x0,0x0,0x0,0x0,0x0,0x6000000018000000100002000180000400000401000001010000004010008000400000201000000804000008010000008040000010010000010400000100100000100108713a7,0x420021000080080004000008000400800020002000010000000100020000100080004000010010000008040000080100000080600000100100000104000001001000001001087d3a7,0x0,0x0,0x0,0x0,0x202000000208000002000040002080000400002001000020010000080010008000400000201000000804000008010000008040000010010000010400000100100000100108713a7,0x0,0x0,0x0,0xf37d4c3cc0f3079f9807980007980000799e60f3001e9cc01e6f3001ea45803db3000f379801e703df5,0x0,0x0,0x0,0x20002000020008000200004000200080000400200001000100010000400010008000400000201000000804000008010000008040000010010000010400000100100000100908713a7,0x0,0x0,0x100a101088442],
[0x100a101088442,0x100a100088442,0x100a101088442,0x100a103088642,0x100a102088442,0x100a102088442,0x100a102088442,0x100a101088442,0x100a1040894c2,0x0,0x100a1040894c2,0x0,0x0,0x0,0x0,0x0,0xf33cc1e600003cc000130773300003cc003cfccf3079a22c0000f30000f37b69cc0fa98003cc1e6110c6,0x808020204100104080002000204400100804e4,0x0,0x1008040204100104080002000204400100804e4,0x0,0x0,0x0,0x0,0x8040204100104080002000204400100804e4,0x8008200204100104080002000204400100804e4,0xf381183cc1e6079f981e600007980000f31e60f3001e9cc01e6f3001ebb2003db3000f3f3001e703df5,0x10008400200100104080002000204400100804e4,0x0,0x0,0x0,0x0],
[0x0,0x100a101088442,0x100a101088442,0x100a100088442,0x100a101088442,0x100a103088642,0x100a102088442,0x100a102088442,0x100a102088442,0x100a101088442,0x100a1040894c2,0x0,0x100a1040894c2,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_1357 : TreeBound (n := 4) 107 (programCode 0x4e29076419) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0xf307983cc0002d907987983cde6044580005b3f53001e9cc01e6f3001e60f300f3f3003ccf301e7032b5,0x8000a000200900024080002000200400040000e4,0xf307983cc0006a50798f303cde6025f800097ff53001e9cc01e6f3001e60f300f3f300798f301e703345,0x0,0x1008501084222,0x1008501084222,0x1008501084222,0x1008501084222,0x1008501084222,0x100850218c642,0x1008501084222,0x100850218c642,0x1008501084222,0x1008504084222,0x0,0x1008504084222,0x8010200402040080402004080100802020082ce3,0x0,0x8020200804040100804004100100802020084ce3,0x0,0x0,0x1008501084222,0x1008501084222,0x1008501084222,0x1008501084222,0x1008501084222,0x1008d0218c642,0x1008501084222,0x1008d0218c642,0x1008501084222,0x8001200100240008100804220100802020080ce3],
[0x0,0x80006000220100804008008400201100044221a4,0x8001200400240008502004080100802020082ce3,0x0,0x8001200800240008144004100100802020080ee3,0x0,0x0,0x1008901084222,0x1008901084222,0x1008901084222,0x1008901084222,0x1008901084222,0x1008902084642,0x1008901084222,0x1008902084642,0x1008901084222,0x1008904084642,0x0,0x1008904084642,0x8010200402040080402004080100802020082ce3,0x0,0x8000200800040000004004100100802020080ce3,0x0,0xf307983cc001f5307a3641e7e6008118003ecc073001e9cc01e6f3001e60f300f3f3003ccf301e7032b5,0x8000a000204100104080002000200400040000e4,0x0,0x1008501084222,0x1008501084222,0x1008501084222,0x1008501084222,0x1008501084222,0x1008d0218c642],
[0x1008501084222,0x1008d0218c642,0x1008501084222,0x1008504084222,0x0,0x1008504084222,0x8004200400840020402004080100802020082ce3,0x0,0x8004200800840020104004100100802020080ce3,0x0,0x0,0xf3000222c00088b0000f6ccf300f33cc00f33cd8b3eeded983cc001e611172463b660f30007d4c1e9cb6,0xf300012fc0004bf0000f3f33cc0f33cc00f33cc000f30f30f6cc000f30f3097e01e6000f307d4c1e93b6,0x0,0xf300012fc0004bf0000f3f33cc0f33cc00f33cc001e60f307d4c001e60f3097e01e60f30007d4c1e93b6,0xf3000222c00088b0000f6ccf300f33cc00f33cd8b3eede6003cc0000011172463b660000007d4c1e9cb6,0xf300012fc0004bf0000f3f33cc0f33cc00f33cc007980f379bcc007980f3097e01e6003cc07d4c1f0d36,0x0,0xf300012fc0004bf0000f3f33cc0f33cc00f33cc00f300f33cfcc00f300f3097e01e60079807d4c1f86b6,0xf3000222c00088b0000f6ccf300f33cc00f33cc79c08ded983cc001e611172097b660f30007d4c1e9cb6,0xf300012fc0004bf0000f3f33cc0f33cc00f33cc03cc00f6cc3cc03cc00f3097e01e601e6007d4c225fb6,0x0,0xf300012fc0004bf0000f3f33cc0f33cc00f33cc079800f4e63cc079800f3097e01e60798007d4c2dc3b6,0xf3000222c00088b0000f6ccf300f33cc00f33cd6cc08e22c03cc0000011172097b660000007d4c1e9cb6,0x0,0x0,0x0,0x0,0x16c8000f3f300172320f301e63cc0799e7e8e83001e9cc01e6f3001e60f300f3f3003ccf301e7032b5,0x3cc1e603cc7980f312fd0230001f53000408cf3079a22c0000f300012fd11679807980007980001df6,0x25f80007a730025f801e601e67980799e7e60f3001e9cc01e6f3001e60f301e6f300798f301e703855,0x0],
[0x0,0x0,0x80008000200100004080002000200400040000e4,0x1e601e67980798f301303a730f300f3003cfccf3079a22c0000f300012fd11679807980007980001df6,0x0,0x0,0x8000200100004080002000200400040000e4,0x0,0x0,0x0,0x8000200100004080002000200400040000e4,0x0,0x0,0x4000000110000000140000000900000001020010000020040000100080000200080070029001000024001100208000000200012002380108002c004100008000000220001000fdea8,0xf300012fc00088b0000f4e67980f31e601e63cc002046000811f980f31023079fd50640d90811fd51426,0x0,0xf300012fc00088b0000f4e67980f31e601e63cc002046000fa9f981e6102307983d063fe60811fd51426,0x400000005000000044000000050000000100800800008000800008008000020008001000080000008000450020800140000001100008000000880001000280000002200010025b1a8,0xf300012fc00088b0000f4e67980f31e601e63cc00f4e6003d39f987981023001e9d0649640811fd60726,0x0,0xf300012fc00088b0000f4e67980f31e601e63cc00f4e60079f9f98f301023001e9d064d300811fd60726,0x400021001000004004000000010000020040002000100000000000020000000000000200010000800040001000080001000080020000100080000400100001000100001001087ffa7,0xf300012fc00088b0000f4e67980f31e601e63cc0799e601e679f9bcc0102301e63d06f4400811fe44426,0x0,0xf300012fc00088b0000f4e67980f31e601e63cc0799e603cc79f9f980102300f33d06b7800811fdcac26,0x0,0x0,0x0,0x0,0x0,0x8010200012040080090084002100802020080ce3,0x8010200002040080000004020100802020080ce3],
[0x80102000220400800a0104004100802020080de3,0x8010200402040080402004080100802020082ce3,0x8010200042040080140204008100802020080ee3,0x8010200002040080000004000100802020080ce3,0x8010200082040080180404010100802020080ce3,0x0,0x8010200102040080100804020100802020080ce3,0x8010200002040080000004200100802020080ce3,0x0,0x0,0x8010200402040080402004080100802020082ce3,0x0,0x8010200802040080c04004100100802020086ce3,0x0,0x0,0x100a101084222,0x100a101084222,0x100a101084222,0x100a101084222,0x100a101084222,0x100a102084642,0x100a101084222,0x100a102084642,0x100a101084222,0x100a1040852a2,0x0,0x100a1040852a2,0x8010200408040080402004080100802020082ce3,0x0,0x8000200808040000004004100100802020080ce3,0x0,0xf307983cc0798f30a7107987981e67980f329c4f3001e9cc01e6f3001e60f300f3f3003ccf301eacf2b5],
[0x0,0x100a101084222,0x100a101084222,0x100a101084222,0x100a101084222,0x100a101084222,0x100a102084642,0x100a101084222,0x100a102084642,0x100a101084222,0x100a1040852a2,0x0,0x100a1040852a2,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_1534 : TreeBound (n := 4) 107 (programCode 0x4e2907641a) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x0,0x159fd80000005be75600000057d95d80000005be75600000006c1f380000005be7560000000567f60572c5ec000000572c5ec00000ae58bd800000572c5ec000000572c5ec000000572c5ec0567f6002b3fb0159fd800058619dc66f21a08775bfd8000056d5df6002b3fc59fd80000005684c7f60000acff167f60acfec0acff6d602031373f600002b4006800cfecacff167f60acff16d62261e7bcac,0x0,0x0,0x0,0x0,0x0,0x1dcd650000f5de817b9b0777a050000f5de81400001dcd6500012a05f23b9e859107858ca0eb28000000007736826b2800000003b9aca0ee88f5650077447ab28001dd11eaca01dd11eaca001dd11f25b26a503bb910776a5eee25d94003b9aca00000ee6d04d6500ee6d0c7ddb689,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xf300012fc00088b00012fc0798f301e63cc03cc0025f800097e7980f30f4e60f3079ff320f30f344ac26,0x0,0x40000001100000001400000011000000016400100000000080004000800010000800640020014000000010400000040000000102002180001000200010000000010002000500fd3a8,0x1008505290ae2,0x10081000908e2,0x1008505290ae2,0x80006000200100004000000000208000201029a4,0x1008902090d02,0x0,0x1008902090d02,0xf3000222c00088b00015a8ebb003eb530007d4d9e4411b9079fd4fea60f6cf3c6e7cc1f53f307d6e6856,0x0,0x0,0x0],
[0x40000001100000004400000009000000014200100010000400040000200000000800420030010000080000000000000000000102002100008000000004000000010000800440ffe28,0x0,0x0,0x0,0xf300012fc00088b00012fc0798f301e63cc03cc0025f80011167981e60f4e60f3079fd4c0f30f344ac26,0x0,0x80006000220100804000008000208000201029a4,0x0,0x80006000200100004000000000208000201029a4,0x8000a000201100044000000000208000201029e4,0x80006000200100004000000000208000201029a4,0x80006000202100084000008000208000201029a4,0x0,0x80006000202100104000000000208000201029a4,0x80006000200100044000000000208000201029a4,0x40000000500000004400000005000000010100080000400200001000800001000800510008000040a000451020a00104000001010000800040082000100208000100020011025b9a8,0x0,0x400000005000000044000000050000000100800800008002000008008000020008001380080000e0800045382080010e000001010001c0004008200010021c000100020013825b9a8,0x4000220a1000000104000020a100000030080020000100000b01000202c010000280000800400001000800010008000010008000180004105000040441c00100056000100158573a7,0x80006000220100804000008000208000201029a4,0x0,0x8000a000240101004000008000208000201029e4,0xf300012fc0004bf00012fc03ccf303cc3cc03cc007980f37b660007980f3f4e600f3003ccf31e62e3d36,0x0,0xf300012fc0002d90000f3003cc1e63cc07983cc0f3000f300003db3000f3f31e60f300000f31e62dc326,0x1008505290ae2,0x10081040908e2,0x1008505290ae2,0x80006000220100004000000200208000201029a4,0x1008906090d02,0x0,0x1008906090d02],
[0x80006000201100044001008200208008201029a4,0x400021901000000104000000010000001043002180100000000000020000000002000020010000080040000080080000200080430000101000000400000000400000001001087fda7,0x0,0x0,0x40000001100000002400000009000000014200100010000400040000200000000800420030010000080000000000000100000102002100008000000004000000010000800440fee28,0xf3000222c00088b0000fa983cc1e60f307983ccf30000fa98003cfcc00f3f4e6003ccf300f3079a264f6,0x400030101000000104000000010000001020003190080000000080020000200002000020010000080040000080080000200080632000101000000400000000400000001001087fda7,0x0,0x0,0x800060002201008c400201810020801020182fa4,0x1008502390f02,0x1008902090d02,0x1008502390f02,0x800060002031000c400201810060801020182fa4,0x1008902090d02,0xf300012fc00088b0000f33d398fc7fe601e63cc00fc7e0079f9f98f300f4e601e679fe3f0f30f3459f26,0x1008902090d02,0x8000600020210004400201010020801020182fa4,0xf3000222c00088b0000f4e67980799e600f33cc01e7e60079bd398f300f4e603cc79fe3f0f30f3469736,0x0,0xf300012fc00088b0000f4e67980f31e601e63cc00f4e60079f9f98f300f4e601e679fe3f0f30f3459f26,0x0,0x100a102090d02,0x0,0x100a102090d02,0x400021001000004004000000010000020040002000100000000400020001000000000200010000800040001000080001000080400000101000000404000001000000001001087ffa7,0x0,0x400021951000086404000000010000001000022190000080000000120000000102004320010010000040000080080000000080432000101000000400008001000000001001087ffa7,0x1008504290ae2,0x10081040908e2,0x1008504290ae2,0x80006000220100804008008200208100205029a4],
[0x1008904090d02,0x400021101000084004000000010000020000202100000800000002020000002000004200010010000040001000080000000080420000101000000400100001000000001001087ffa7,0x1008904090d02,0x80006000201100044008008200208008201229a4,0xf300012fc00088b0000f4e67980799e600f33cc0799e601e6b6b9bcc00f4e60f3079ff320f30f344ac26,0x0,0xf300012fc00088b0000f4e67980f31e601e63cc0799e601e679f9bcc00f4e61e607a04e40f30f353dc26,0xf300012fc0004bf0000f3003ccf303cc00003cc03cc00f6cde6003cc00f3f4e600f300000f31e62dc3b6,0x100a1040918e2,0xf300012fc0004bf0000f6cc3ccf303cc03cc3cc03cc00f6ce22c03cc00f3f4e600f307980f31e62dc3b6,0x100a1040918e2,0x0,0x0,0x420021001080084000000000000400020040002000100000000400000001000000000200010000800040001000080002000080400000101000000404000000800000001001087fea7,0x0,0x420021001080084000000000000400020040002000100000000400000001000000000200010000800040001000080002000080400000101000000404000000800000001001087fea7,0x0,0x400021800000080000000000000000020040002000100000000400000001000000000200010000400040001000020002000080400000101000000204000000800000001000487ee27,0x0,0x0,0x20021000080084000100000000100020040002000100000000400000001000000000200010000800040001000080002000080400000101000000404000000800000001001087fea7,0x0,0xf381183cc1e6079879bcc0000f307983cc00000f303cc3cc1e607981e9cc003db3000f300001e703fa5,0x0,0x0,0x400021800000080000000000000000020040002000100000000400000001000000000200010000400040001000020002000080400000101000000204000000800000001000487ee27,0x0,0x0,0x0,0xf30000b6400088b000102307995615060f3f6cc03d6b09ccc79f9f9802dae679807a2b099f3892dca716,0x1008504290ae2,0x10081040908e2],
[0x1008504290ae2,0x80006000220100804008008400208100205029a4,0x1008904090d02,0xf30000b6400088b0000f300798fa99e601e63cc03d57e03cc79f9f9800f4e6000079fd4c0f30f344a716,0x1008904090d02,0x80006000200100044008000400208000201229a4,0xf300012fc00088b0000f4e67980799e600f33cc0799e603ccb6b9f9800f4e60f3079fd4c0f30f344ac26,0x0,0xf300012fc00088b0000f4e67980f31e601e63cc0799e603cc79f9f9800f4e60f307a04e40f30f344ac26,0x0,0x100a1040918e2,0x0,0x100a1040918e2,0x0,0x0,0x0,0x0,0x1e60f307983cc1e612fc03ccf303cc3cc03cc000000f301e60000000f3f4e600f300000f31e62dc3b6,0x8280800040100000100c0800010200040000080100003220400024a010000100008000040040000200100000800100000804000001016440004059100010060400010191877ba7,0x0,0x0,0x0,0x801000008008180004010600010048004000320010000c8004000120010000480008000040080000400040000200100000806400000810000002064000008090000010244866e27,0x0,0x80100000400800001000240002004800400020001000000004000100010000480008000040080000400040000200100000800000000410000002040000008090000010244856e27,0x0,0xf300003cc00012fc03ccf303cc3cc03cc000000f301e60000000f3f4e600f300000f31e62dc3b6,0x0,0x0,0x0,0x0,0x221100000884400001000000001001040002110100000000400000041000002004220010000000040000080080004000080422000100040000404000001000000001001087ffa7],
[0xf30f30f303cc0f312fc03ccf303cc3cc03cc1e60011161e601e6000f3f4e600f30007a731e62dc3b6,0x0,0x1e60f30f307981e612fc0798f301e63cc03cc3cc7980f31e67b66000f4e60079f9fd799f30f344ac26,0x2021000008080000004000000010008040002100100000080400000201000000004200010000100040000400020000000080420000101000000404000000800000001000487fe27,0x7980f379803cc79812fc03ccf303cc3cc03cc1e60011161e601e6000f3f4e600f3003ccf31e62e3d36,0x2021800002084000020000000020020040002100100000000400000801000000004200010000000040001000080000000080420000100000000104000001000000001001087dfa7,0x0,0x1e612fc0003cc1e612fc03ccf303cc3cc03cc1e60011161e601e6000f3f4e600f3000f3f31e62dc3b6,0x79800f4e60079bcc012fc0798f301e63cc03cc3cc7980f31e67b66000f4e60f3079ff320f30f344ac26,0x12fc0003cc00012fc03ccf303cc3cc03cc1e60011161e601e6000f3f4e600f300000f31e62dc3b6,0x79800f6cc0079f98012fc0798f301e63cc03cc3cc7980f31e67b66000f4e61e607a04e40f30f353dc26,0xf300003cc00012fc03ccf303cc3cc03cc1e60011161e601e6000f3f4e600f300000f31e62dc3b6,0x3cc0010230007b660012fc0798f301e63cc03cc3cc7980f31e67b66000f4e679807a2adc0f30f344ac26,0xf30012fc0003db30012fc03ccf303cc3cc03cc1e60011161e601e6000f3f4e600f307980f31e62dc3b6,0x7980020460007d4c0012fc0798f301e63cc03cc3cc7980f31e67b66000f4e6f3007a1bac0f30f3be3136,0x0,0x0,0xf3000222c00088b0000f30408c001023000408cf3001f164007b69cc00f3f4e6003cc007a7307b8864f6,0x0,0x400030001000010004000000010000100060003000020000000000020000200000002000010008000040008000080020000080600000101000000400000000400000001001087fda7,0x1dcd650ee6b9f3598e3d7f08ba50ee6b9f359400255e8ba50ee6b2803be951fea89fa9b0b28003b9b16d58872f599328000ee6b4d48319940ee6b9f3594ee6b9f35940ee6b9f35943b9ae7cd6503ba23d594003b9ae7cd6503c37d9fd51039aef40be43b9b5f02f90ee6d965224119,0xf3000222c00088b0000f31e9cc007a73001e9ccf300012fc0003cfcc00f3f4e6003cc03ccf3079a2de76,0x0,0xf3000222c00088b0000f379bcc01e6f3003cfccf300003cc000003cc00f3f4e6003cc0798f3079a357f6,0xf3000222c00088b0000f307d4c001f530007d4cf300012fc0003cfcc00f3f4e6003cc00f3f3079a264f6,0x400030001000010004000000010000100060003000100000000000020000000000002000010008000040008000080020000080600000101000000400000000400000001001087fda7,0x0,0x400030001000010004000000010000100040003000100000000000020000000000002000010008000040008000080020000080600000101000000400000000400000001001087fda7,0x0,0xf3000222c00088b0000fa983cc1e60f307983ccf300012fc0003cfcc00f3f4e6003ccf300f3079a264f6,0x400030001000010004000000010000100020003000080000000080020000200000002000010008000040008000080020000080600000101000000400000000400000001001087fda7,0x0],
[0x0,0x3cc0014884c87d4c0012fc0798f301e63cc03cc3cc7981e61e67d4c000f4e679807a2b099f30f344ac26,0x0,0x0,0x3cc1e60f307981e612fc0798f301e63cc03cc7987981e61e67d4c000f4e60079f9fd6a6f30f344b136,0x3cc222cf30892d4c12fc0798f301e63cc03cc7987981e61e67d4c000f4e60079f9fd6a6f30f344b136,0x7980f379803cc79812fc03ccf303cc3cc03cc3cc0010231e603cc000f3f4e600f300f30f31e62fa9b6,0x131a60079f98012fc0798f301e63cc03cc3cc7981e61e67d4c000f4e6000079fd4c0f30f344ac26,0x0,0x0,0x79800f4e60079bcc012fc0798f301e63cc03cc3cc7981e61e67d4c000f4e60f3079fd4c0f30f344ac26,0x0,0x79800f6cc0079f98012fc0798f301e63cc03cc3cc7981e61e67d4c000f4e60f307a04e40f30f344ac26,0xf300003cc00012fc03ccf303cc3cc03cc3cc0010231e603cc000f3f4e600f300000f31e62dc3b6,0x3cc0010230007b660012fc0798f301e63cc03cc3cc7981e61e67d4c000f4e679807a1bac0f30f344ac26,0x0,0x3cc0011160007d4c0012fc0798f301e63cc03cc3cc7981e61e67d4c000f4e679807a3a0c0f30f344ac26]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_1743 : TreeBound (n := 4) 107 (programCode 0x4e2907641b) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0xf307983cc00088b07987983cde6044580005b3f53001e9cc01e6f3001e61e601e63cc03cde601e7037c5,0x0,0x16c8000f31e60176b44f31e600f307d9dc2ee03001e9cc01e6f3001e60f300f33cc03cde601e7032b5,0x808020200900024080006000200c00020100e4,0x16c8000799e6026977bcc1e600f307d9bdc6553001e9cc01e6f3001e60f300f37980799e601e703345,0x0,0x0,0x0,0x80008000200900024080002000200400000000e4,0x1e601e67980798f300f31023000408c000408cf307a952c001f530000f37b69cc0fa98003cc1e611156,0x0,0x0,0x8000200900024080002000200400000000e4,0x0,0x0,0x0,0x8000200900024080002000200400000000e4,0x0,0xf307983cc0002d90798f303cde6016c800097f023001e9cc01e6f3001e60f300f33cc03cde601e7032b5,0xf307983cc0000f307983cc00000007983cc1e60f3001e9cc01e6f3001e60f300f33cc03cde601e7032b5,0x0,0x8001200010240008180084002101002040080ce3,0x0,0x8001200020240008180104004101002040080ce3,0x8001200040240008100204008101002040080ce3,0x8001200040240008100204008101002040080ce3,0x8001200100240008100804020101002040080ce3,0x8001200080240008100404010101002040080ce3,0x8001200040240008100204008101002040080ce3,0x8001200100240008100804020101002040080ce3,0x8001200100240008100804220101002040080ce3],
[0x0,0x0,0x8001200400240008502004080101002040082ce3,0x0,0x8001200800240008144004100101002040080ee3,0x0,0x0,0x8002200010440030180084002101002040080ce3,0x8000a000202100084000808020200c02000100e4,0x8002200020440030180104004101002040080ce3,0x8000200000040000000004000101002040080ce3,0x8004200040840020100204008101002040080ce3,0x8000200000040000000004000101002040080ce3,0x8004200080840020100404010101002040080ce3,0x8000200000040000000004000101002040080ce3,0x8000200100040000000804020101002040080ce3,0x8000600020210008400800820020801220142ba4,0x0,0x80006000202100084008008400210012402433a4,0x8010200402040080402004080101002040082ce3,0x0,0x8000200800040000004004100101002040080ce3,0x0,0xf307983cc001f53079f981e7e600fa98003ec46f3001e9cc01e6f3001e60f300f37980799e601e703345,0x0,0x0,0x8000a000204100104000800020200c02000100e4,0x0,0x8000200000040000000004000101002040080ce3,0x8001200040240000100204008101002040080ce3,0x8000200000040000000004000101002040080ce3,0x8002200080440000100404010101002040080ce3],
[0x8000200000040000000004000101002040080ce3,0x8000200100040000000804020101002040080ce3,0x8000600020210010400800020020802220182da4,0x80006000202100104000002000200402000000a4,0x8000600020210010400800040020801240182fa4,0x0,0x0,0x0,0x0,0xf307983cc01e6f307b660f30000f379800f4e60f3001e9cc01e6f3001e60f300f33cc03cde601e7032b5,0x0,0x0,0x0,0xf3000222c00088b0000f6ccf300f33cc00f33cd05ffce22c03cc03cc01338e0bf83cc1e9cc0079a268b6,0xf300012fc0004bf0000f3f33cc0f33cc00f33cc001e60f307d4c001e612fc1e6003cc1e9cc0079a25fb6,0xf3000222c00088b0000f6ccf300f33cc00f33cd9e3aede6003cc000001338e0bf83cc003cc0079a268b6,0xf300012fc0004bf0000f3f33cc0f33cc00f33cc007980f379bcc0079812fc1e6003cc0408c0079a2d936,0xf3000222c00088b0000f6ccf300f33cc00f33cd05ffcde6f33cc03cc01338e0bf83cc1e9cc0079a268b6,0xf300012fc0004bf0000f3f33cc0f33cc00f33cc00f300f33cfcc00f3012fc1e6003cc07d4c0079a352b6,0xf3000222c00088b0000f6ccf300f33cc00f33cc79c08ded983cc001e61338e04603cc1e9cc0079a268b6,0xf300012fc0004bf0000f3f33cc0f33cc00f33cc03cc00f6cc3cc03cc012fc1e6003cc1e9cc0079a25fb6,0x0,0xf300012fc0004bf0000f3f33cc0f33cc00f33cc079800f4e63cc0798012fc1e6003cc79bcc0079b18fb6,0xf3000222c00088b0000f6ccf300f33cc00f33cd0233ce22c03cc000001338e04603cc003cc0079a268b6,0x0,0xf3000222c00088b0000f6ccf300f33cc00f33cd0233ce22c03cc03cc01338e04603cc1e9cc0079a268b6,0x0,0x0,0x16c8000f3f30016c801e601e67980799e7e60f3001e9cc01e6f3001e61e601e67980799e601e703855,0x808020200900024080006000200c00020100e4,0x16c80007a73002634c0f301e67980799e7e7f53001e9cc01e6f3001e60f300f37980799e601e703345,0xf6d3b663cc1e6fa9fd4c0f30000f379801e7e60f3001e9cc01e6f3001e60f300f3f300f31e601e7033d5],
[0x0,0x0,0x80008000200100004080002000200400000000e4,0x0,0x3d3b663cc1e603d3d4c0f30000f379801e7e60f3001e9cc01e6f3001e60f300f3f300f31e601e7033d5,0x0,0x8000200100004080002000200400000000e4,0xf6d3b663cc1e6fa9fd4c0f30000f379801e7e60f3001e9cc01e6f3001e60f300f3f300f31e601e7033d5,0x0,0x0,0x8000200100004080002000200400000000e4,0x0,0x0,0x0,0x0,0x0,0xf300012fc0004bf0000f4e63cc079bcc01e63cc001e60f3088b0001e612fc1e6007983cfcc00f3814bb6,0x400000005000000044000000050000000100800800008000800008008000020008000080080000008000450820800102000001008000401000080000080204010000010010825b1a8,0xf300012fc0004bf0000f4e63cc079bcc01e63cc007980f37a7300079812fc1e6007980408c00f381c536,0x0,0xf300012fc0004bf0000f4e63cc079bcc01e63cc00f300f33db3000f3012fc1e60079807d4c00f3823eb6,0x400021001000002004000000010000020040002000100000000000020000000000000200010000800040001000080001000080020000100080000400080000400200001001087fda7,0xf300012fc0004bf0000f4e63cc079bcc01e63cc03cc00f6ccf3003cc012fc1e6007983cfcc00f3814bb6,0x0,0xf300012fc0004bf0000f4e63cc079bcc01e63cc079800f4e6f300798012fc1e6007983cfcc00f3814bb6,0x0,0x0,0x400030001000010004000000010000100040003000100000000000020000000000002000010008000040008000080020000080020000100080000400080000400200001001087fda7,0x0,0x0,0x8010200012040080090084002101002040080ce3,0x0],
[0x80102000220400800a0104004101002040080de3,0x8010200402040080402004080101002040082ce3,0x8010200042040080140204008101002040080ee3,0x8010200002040080000004000101002040080ce3,0x8010200082040080180404010101002040080ce3,0x0,0x8010200102040080100804020101002040080ce3,0x8010200002040080000004200101002040080ce3,0x0,0x0,0x8010200402040080402004080101002040082ce3,0x0,0x8010200802040080c04004100101002040086ce3,0x0,0x0,0x16c8000f31e60176b47cc1e600f307d9dc2ee03001e9cc01e6f3001e60f300f33cc03cde601e7032b5,0x80802022010080408000a000200c00020100e4,0x16c8000799e6026791bcc1e600f307d8cac6553001e9cc01e6f3001e60f300f37980799e601e703345,0x0,0x0,0x0,0x8000800022010080408000a000200400000000e4,0x0,0x0,0x0,0x800022010080408000a000200400000000e4,0x0,0x0,0x0,0x800022010080408000a000200400000000e4,0x0,0xf307983cc0798f3097e07987983cc7980f325f8f3001e9cc01e6f3001e60f300f37980799e601eacf345],
[0x0,0x16c8000f3f300172321e601e679807d79ae8e83001e9cc01e6f3001e60f300f33cc03cde601e7032b5,0x80802024010100408000a000200c00020100e4,0x16c80007a73002634c1e601e679807d6a7e7f53001e9cc01e6f3001e60f300f37980799e601e703345,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x800024010100408000a000200400000000e4,0x0,0x0,0x0,0x800024010100408000a000200400000000e4,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_1920 : TreeBound (n := 4) 107 (programCode 0x4e2907641c) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x800100008800000004001200010004c00020001000000104000000c10000001000008040000080400000040200000100800000400410000002040000008000090010004856e27,0x0,0x800100004800000010001200020004c00020001000000204000000c10000001000008040000080400000040200000100800002000410000002040000008000090010004856e27,0x3b9acbdcd68b9acbdcd66dcd65ee6b28ee6b2f73597b9acc540be47735b1cd653b9ad173594ee6b45cd651dcd6c735941dcd68b9ad8e6b3251467fc0c7cd6500000ef5993639aca3b9aca0001dd11eaca00003b9bbac099a289a09aca00ee6b280ee6ee1acbdcda18b390b0aa,0x0,0x159fd8000000567f6ad29ffb015dbdc2bcbeddbbc90000000159fdb60f9c000000159fd8000c29e980acfec0567f60000000159fd80aedee15e5f60000000159fd80ae58bdd67f600000acfec000ad0427f60000ad0427f600000ad0427f600002b4109fd80000568213fb00000568213fb00000000056d5df6000005694ffdbb77935a53ff600000ad145fd80000159fd800acfec159fdd72e158a1a2b,0x0,0x0,0x1dcd6500002540c1f9acbdcd66dcd65f5de8140000773597b9acc540be47735b1cd653b9ad173594ee6b45cd651dcd6c735941dcd68b9ad8e6b3251467fc0c7cd6500000ef5993639aca3b9aca0001dd11eaca00003b9bbac099a289a09aca00ee6b280ee6ee1acbdcda18b390b0aa,0x430020018000000044000000000400000240002014100000000400000001000000100002010000008040000010080000010080400300100000000104000001000004001001087dfa7,0x80000100400800001000000202000004c00020001000000004000000410000001000008040000080400000040200000100800000000410000002040000008000010010004856e27,0x400320018000400044000000080004000240002014100000010400000041000000100002010000008040000010080000010080400300100000400104000001000004001001087dfa7,0x800000108000800004000000210000004c0002000100000004c000000530000001000008040000080400000040200000100800000400410000002040000008000010010004856e27,0x1dcf41d650f613798a1e324ee18ee6ba6d5a1578000000ee6b28430e237b9e8589765f50a3143b9400001dcd65f401b263594001dcd650ee88f565003ba23d59401dd11eaca001dd11eaca001dd11eaca000000f048019277fae25d94001deb3265000ee6b287735a2e6d0c71e2f49,0x200020018200000042000000002000000240002015900000000400000001000000100002010000008040000010080000010080400300100000000104000001000004001001087dfa7,0x400320018000000040000000000000000240002014100000000400000001000000100002010000008040000010080000010080400300100000000104000001000004001001087dfa7,0xf300012fc00088b00012fc0798f301e63cc03cc0025f800097e7980f30f4e61e60f384e41e61e64c4426,0x0,0x0,0x1008505290ae2,0x10081000908e2,0x1008505290ae2,0x80006000200100004000000000208000401029a4,0x1008902090d02,0x400020015000000014000000050000000100202014000800010000820000002000100002010000008040000008080000020080400280101000000400000800400002001001087fda7,0x1008902090d02,0x8000a000200100044000000000210000402031e4,0x1dcd65f345386d9a7b9b0777a0500002540be400001dcd6500007ecfb1a931eb63080ee7a1625d940000000000ee6b2807735940ee6b29dd11eaca000ef59932801dcf41d65003b9e83aca003b9e842642987d97b594000003c11ff940077536165000ee6b283b9ad8e6d0c848c4c9,0x0,0x40002001500000001400000001000000014002a014100000000000020000000200100002010000008040000008080000020080400280101000000400000000400002001001087fda7],
[0x0,0x0,0x0,0x0,0xf300012fc00088b00012fc0798f301e63cc03cc0025f80011167981e60f4e60f30f384e41e61e653dc26,0x0,0x80006000220100804000008000208000401029a4,0x0,0x80006000200100004000000000208000401029a4,0x8000a000201100044000000000210000402031e4,0x80006000200100004000000000208000401029a4,0x80006000202100084000008000208000401029a4,0xf3000222c0002d90001347ff300003cc00f33cd9e4378e6003cc000000f6ce0bf83cc0001e6079a26796,0x80006000202100104000000000208000401029a4,0x80006000200100044000000000208000401029a4,0x4000000050000000440000000500000001010008000010008000100080000100080041c0020000002000455c2820010700000100800040008008000008020e000200010010825b1a8,0x0,0x400000005000000044000000050000000100800800008000800008008000020008000080080000008000450820800102000001008000400080080000080204000200010010825b1a8,0x0,0x80006000220100804000008000208000401029a4,0x0,0x8000a000240101004000008000210000402031e4,0xf300012fc0004bf00012fc03ccf303cc3cc03cc007980f37b660007980f4e7e60079803cde60f381c536,0x0,0x1dcd6500007ea8ed400010c388d00007ea8ed400010c388d0000257c59fa47ff3e6b2f735943b9bba47fe8b9acbdcd6caef40bdcd82eb3265007ee48935e2d1a20c6650077712ff405f97536165001ddc4bee5664cbdce5ade9f1c4bee5664cbdcd6c7377111eacdb9adac3f4cc49a,0x1008505290ae2,0x10081040908e2,0x1008505290ae2,0x80006000220100004000000200208000401029a4,0x1008906090d02,0x400000003000000024000000110000000100000200104002000000008000080008000000000010400a0020000020000800000100400000004008200020000000020004000600c2ba8,0x1008906090d02],
[0x80006000201100044001008200208008401029a4,0x0,0x0,0x0,0x0,0xf3000222c00088b0000fa983cc1e60f307983ccf30000fa98003db3000f6cde600f30f301e61e62dc8f6,0x0,0x0,0x0,0x800060002201008c400201810020801040182fa4,0x1008502390f02,0x1008902090d02,0x1008502390f02,0x800060002031000c400201810060801040182fa4,0x1008902090d02,0xf300012fc00088b0000f33d398fc7fe603cc3cc00fc7e0079f9f98f300f4e601e6f37e3f1e61e64d3726,0x1008902090d02,0x8000600020210004400201010020801040182fa4,0xf3000222c00088b0000f4e67980799e600f33cc01e7e60079bd398f300f6cc03ccf3820b1e61e64e2f36,0x0,0xf300012fc00088b0000f4e67980f31e601e63cc00f4e60079f9f98f300f4e601e6f37e3f1e61e64d3726,0x0,0x100a102090d02,0x0,0x100a102090d02,0x400021001000004004000000010000020040002000100000000400020001000000000200010000800040001000080001000080400000101000000404000001000000001001087ffa7,0x0,0x1dcd65f056ec75d97c15d8eadb5f056ec75d9400001dcd650003b9aca3f5c25940a0fd7096502877359400000861c468000077712eca00001dcddd2b7288b3770d6503b9aca01dcda09aca000003b9aca000003bb8d4eb87116e25d94003b9aca1dcd73e6b287735a2e6d0c7dd1279,0x1008504290ae2,0x10081040908e2,0x1008504290ae2,0x80006000220100804008008200208100405029a4],
[0x1008904090d02,0x400021101000084004000000010000020000202100000800000002020000002000004200010010000040001000080000000080422000101000000400100001000000001001087ffa7,0x1008904090d02,0x80006000201100044008008200208008401229a4,0xf300012fc00088b0000f4e67980799e600f33cc0799e601e6b6b9bcc00f4e60f30f37f321e61e653dc26,0x0,0xf300012fc00088b0000f4e67980f31e601e63cc0799e601e679f9bcc00f4e61e60f384e41e61e64c4426,0xf300012fc0004bf0000f3003ccf303cc00003cc03cc00f6cde6003cc00f4e7e6007980001e60f3814bb6,0x100a1040918e2,0xf300012fc0004bf0000f4e63ccf303cc01e63cc03cc00f6ced9003cc00f4e7e6007983cc1e60f3814bb6,0x100a1040918e2,0x0,0x0,0x420021001080084000000000000400020040002000100000000400000001000000000200010000800040001000080002000080400000101000000404000000800000001001087fea7,0x0,0x420021001080084000000000000400020040002000100000000400000001000000000200010000800040001000080002000080400000101000000404000000800000001001087fea7,0x0,0x400021800000080000000000000000020040002000100000000400000001000000000200010000400040001000020002000080400000101000000204000000800000001000487ee27,0x0,0x0,0x20021000080084000100000000100020040002000100000000400000001000000000200010000800040001000080002000080400000101000000404000000800000001001087fea7,0x0,0xf381183cc1e6079879bcc0000f307983cc00000f303cc3cc1e607981e9cc003db3000f300001e703fa5,0x0,0x0,0x400021800000080000000000000000020040002000100000000400000001000000000200010000400040001000020002000080400000101000000204000000800000001000487ee27,0x0,0x0,0x0,0xf300012fc00088b000102307992ffea60f303cc07a17fe9cc0079f9800f4e67980f39bca7e61e64c4426,0x1008504290ae2,0x10081040908e2],
[0x1008504290ae2,0x80006000220100804008008400208100405029a4,0x1008904090d02,0xf30000b6400088b0000f300798f6cde603cc3cc03d48b03cc79f9f9800f3f30000f37b661e61e64c3f16,0x1008904090d02,0x80006000200100044008000400208000401229a4,0xf300012fc00088b0000f4e67980799e600f33cc0799e603ccb6b9f9800f4e60f30f37d4c1e61e653dc26,0x0,0xf300012fc00088b0000f4e67980f31e601e63cc0799e603cc79f9f9800f4e60f30f384e41e61e653dc26,0x0,0x100a1040918e2,0x0,0x100a1040918e2,0x0,0x0,0x0,0x0,0x1e60f307983cc1e612fc03ccf303cc3cc03cc000000f301e60000000f4e7e6007980001e60f3814bb6,0x810000008090000008140000010100040003400100000100400014201000050000800004008000040008000040010000080400000081000000204008000800020001028c866e67,0x0,0x10100000040c00000101000000201000400030001000004004000104010000400008000040080000400080000400100000804000000810000002040100008000400010208866e67,0x0,0x0,0x0,0x0,0x0,0xf300003cc00012fc03ccf303cc3cc03cc000000f301e60000000f4e7e6007980001e60f3814bb6,0x0,0x0,0x0,0x0,0x0],
[0xf30f30f303cc0f312fc03ccf303cc3cc03cc1e60011161e601e6000f4e7e600798007b660f3814bb6,0x0,0x1e60f30f307981e612fc0798f301e63cc03cc3cc7980f31e67b66000f4e6007a737d79ae61e64c4426,0x800400008080000008004000010008040002000100000100400000201000000004000004000200040000400040000000080400000081000000204000000800000001000c866e67,0x7980f379803cc79812fc03ccf303cc3cc03cc1e60011161e601e6000f4e7e60079803cde60f381c536,0x2021000008084000020000000020020040002100100000000400000801000000004200010000000040001000080000000080400000101000000404000001000000001001087ffa7,0x0,0x1e612fc0003cc1e612fc03ccf303cc3cc03cc1e60011161e601e6000f4e7e60079800f4e60f3814bb6,0x79800f4e60079bcc012fc0798f301e63cc03cc3cc7980f31e67b66000f4e60f30f37f321e61e653dc26,0x12fc0003cc00012fc03ccf303cc3cc03cc1e60011161e601e6000f4e7e6007980001e60f3814bb6,0x79800f6cc0079f98012fc0798f301e63cc03cc3cc7980f31e67b66000f4e61e60f384e41e61e64c4426,0xf300003cc00012fc03ccf303cc3cc03cc1e60011161e601e6000f4e7e6007980001e60f3814bb6,0x3cc0010230007b660012fc0798f301e63cc03cc3cc7980f31e67b66000f4e67980f3aadc1e61e64c4426,0x798012fc0003d398012fc03ccf303cc3cc03cc1e60011161e601e6000f4e7e6007983cc1e60f3814bb6,0x7980020460007d4c0012fc0798f301e63cc03cc3cc7980f31e67b66000f6ccf300f39f781e61e6c5c936,0x0,0x40000000500000004400000005000000010800040014008080010020800140000800400028010020000044080280140200000100800801008008100008028410020001001082571a8,0xf3000222c00088b0000f30408c001023000408cf300b6f6402daf53000f6cde600f30007b662db1b60f6,0xf3000222c00088b0000f3003cc0003cc3cc03cd02300222c1e600f3000f6cde600f300001e61e62dc956,0x0,0x0,0xf3000222c00088b0000f31e9cc007a73001e9ccf300012fc0003db3000f6cde600f3003cde61e62e4276,0x0,0xf3000222c00088b0000f379bcc01e6f3003cfccf300003cc00000f3000f6cde600f300f31e61e62faef6,0xf3000222c00088b0000f3003cc0000f30007d4cf300003cc00000f3000f6cde600f300001e61e62dc8f6,0x400030001000010004000000010000100060003000100000000000020000000000002000010008000040008000080020000080400000101000000400000000400000001001087fda7,0x0,0x400030001000010004000000010000100040003000100000000000020000000000002000010008000040008000080020000080400000101000000400000000400000001001087fda7,0x0,0xf3000222c00088b0000fa983cc1e60f307983ccf300012fc0003db3000f6cde600f30f301e61e62dc8f6,0x0,0x0],
[0x0,0x3cc0013eff307d4c0012fc0798f301e63cc03cc3cc7981e61e67d4c000f4e67980f39bca7e61e64c4426,0x0,0x0,0x3cc1e60f307981e612fc0798f301e63cc03cc7987981e61e67d4c000f6cc007a7381367e61e64c4936,0x3cc222cf3089a6cc12fc0798f301e63cc03cc7987981e61e67d4c000f6cc007a7381367e61e64c4936,0x7980f379803cc79812fc03ccf303cc3cc03cc3cc0010231e603cc000f4e7e6007980f31e60f38331b6,0x131a6007a730012fc0798f301e63cc03cc3cc7981e61e67d4c000f4e60000f37d4c1e61e64c4426,0x0,0x0,0x79800f4e60079bcc012fc0798f301e63cc03cc3cc7981e61e67d4c000f4e60f30f37d4c1e61e653dc26,0x0,0x79800f6cc0079f98012fc0798f301e63cc03cc3cc7981e61e67d4c000f4e60f30f384e41e61e653dc26,0xf300003cc00012fc03ccf303cc3cc03cc3cc0010231e603cc000f4e7e6007980001e60f3814bb6,0x3cc0010230007b660012fc0798f301e63cc03cc3cc7981e61e67d4c000f4e67980f39bac1e61e64c4426,0x0,0x3cc0011160007d4c0012fc0798f301e63cc03cc3cc7981e61e67d4c000f4e67980f3ba0c1e61e64c4426]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_2129 : TreeBound (n := 4) 107 (programCode 0x4e2907641d) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x16c8000f301e616c8b64001f530007d4c1e8e83001e9cc01e6f3001e679800fa98003d39801e7032b5,0xf37983cc01e60f37983cc0000f307983cc1e60f3001e9cc01e6f3001e679801ed980079f9801e703855,0x16c80007985b225f92fc001f530007d4c1e7f53001e9cc01e6f3001e679800fa980079f9801e703345,0x0,0x10c041220481,0x424004220481,0x10c041220481,0x4000220481,0x214082220481,0x4000220481,0x214082220481,0x0,0x424004220481,0x0,0x424004220481,0x0,0x844108220501,0x4000220481,0x844108220501,0x4000220481,0x0,0x21c0c1220481,0x234086220481,0x21c0c1220481,0x214082220481,0x214082220481,0x234084220481,0x214082220481,0x0,0x234084220481,0x0],
[0x234084220481,0x0,0x2541c8220501,0x234084220481,0x2541c8220501,0x214080220481,0x0,0x63c0c1220481,0x24004220481,0x63c0c1220481,0x4000220481,0x434082220481,0x4000220481,0x434082220481,0x0,0x24004220481,0x0,0x24004220481,0x0,0x844108220501,0x4000220481,0x844108220501,0x4000220481,0x8118001e61e60faa3a0c01e6f30079bcc20c073001e9cc01e6f3001e679800fa98003d39801e7032b5,0x0,0x16c83cc0001e616c80003cde60445f9805b20f3001e9cc01e6f3001e679801ed980079f9801e703855,0x4008100200900024080002000200402000000e4,0x25f83cc0003cc25f8000799e6025ff98097e0f3001e9cc01e6f3001e679801ed980079f9801e703855,0x0,0x0,0x0,0xfa983cc001e60fa98003cde600fb11803ea60f3001e9cc01e6f3001e679801ed980079f9801e703855],
[0x4008100204100104080002000200402000000e4,0x0,0x0,0x1e601e67980798f301303a730f300f3003cfccf3079a22c0000f300012fd11679807983ccf300001df6,0x0,0x0,0x0,0x3cc7983cc07983cc7980f307983cc97e0f31e60f3001e9cc01e6f3001e679801ed980079f9801eacf855,0x0,0x0,0x42c041220481,0x424004220481,0x42c041220481,0x424004220481,0x434082220481,0x424000220481,0x434082220481,0x0,0x424004220481,0x0,0x424004220481,0x0,0x464188220501,0x424000220481,0x464188220501,0x0,0x0,0xf3001e9cc0079bcc012fc0f30f303cc3cc03ccf362b9e6097e0001e6155bb15c1e60f307983cc1e9cb6,0x3cc00f6cc003cfcc012fc03ccf303cc3cc03cc000f30f311160000f30f301e601e600000003cc1e93b6,0x0,0x3cc00f6cc003cfcc012fc03ccf303cc3cc03cc001e60f3097e0001e60fa99e601e60f307983cc1e93b6,0xf3001e9cc0079bcc012fc0f30f303cc3cc03cd7bf459e601e6000000151eef761e600000003cc1e9cb6],
[0x3cc00f6cc003cfcc012fc03ccf303cc3cc03cc007980f37b660007980f3204601e6003cc1e9cc1f0d36,0xf3001e9cc0079bcc012fc0f30f303cc3cc03cd7bb799e6f4e601e600151eef761e601e60f33cc2268b6,0x0,0xf3001e9cc0079bcc012fc0f30f303cc3cc03ccf3445a22c1e60001e614e22d901e60f307983cc1e9cb6,0x0,0x0,0x0,0xf3001e9cc0079bcc012fc0f30f303cc3cc03cd7f8399ed99e6000000152e1fef9e600000003cc1e9cb6,0x3cc00f6cc003cfcc012fc03ccf303cc3cc03cc1e60011161e601e6000f3f4e601e601e60f33cc225fb6,0xf3001e9cc0079bcc012fc0f30f303cc3cc03cd7bb79a22c1e601e600151eef761e601e60f33cc2268b6,0x3cc00f6cc003cfcc012fc03ccf303cc3cc03cc3cc0010231e603cc000f6cde601e607983cc3cc2dc3b6,0x3d39800f30f3079ff35cc0000f300003cc1e60f3001e9cc01e6f3001e679800fa98003d39801e7032b5,0x0,0x20000010020000010080000040200000140001000100004000400008001000008004002a0010000200010000a00000002000170003800040008000100008000400020001000fdda8,0xf3001e9cc0079f98012fc0798f301e63cc03cc0025f800097e7980f3102307983cc97e4bf07983d1936,0x0,0xf3001e9cc0079f98012fc0798f301e63cc03cc0044580011167981e6102307983cc97e4bf07983d1936,0x0,0x79800f4e6003d398012fc03ccf303cc3cc03cc007980f37b660007980f320460798003cc1f5307a2d36,0x0,0x0,0x400021000000004004000000000000020040002000100000000400000001000000000200010000800040001000080001000080200000100800000401000001001000001001087ffa7,0x0,0x0,0x0,0x0,0xf3001e9cc0079f98012fc0798f301e63cc03cc3cc7980f31e67b6600102301e64bf9bb0dd697e4c4936,0x8000004080000040080000040200000140000800100000800400008001000008004000200004000000440002000040000001100001001080080001000210010800200012025b1a8,0xf3001e9cc0079f98012fc0798f301e63cc03cc7987981e61e67d4c00102301e64bf9f7cfbc97e4c4936,0x0,0x84c161220501,0x86418c220501],
[0x84c161220501,0x844108220501,0x8541c2220501,0x844108220501,0x8541c2220501,0x0,0x864184220501,0x0,0x864184220501,0x0,0x844108220501,0x844108220501,0x844108220501,0x844108220501,0x0,0x63c0c1220481,0x24004220481,0x63c0c1220481,0x4000220481,0x434082220481,0x4000220481,0x434082220481,0x0,0x24004220481,0x0,0x24004220481,0x0,0x844108220501,0x4000220481,0x844108220501,0x4000220481,0x1e679807987983cca713cc0798f301e63cc29c4f3001e9cc01e6f3001e679800fa98003d39801eacf2b5],
[0x0,0x84c161220501,0x8000200000004020102002080080ce3,0x84c161220501,0x4000220481,0x214082220481,0x4000220481,0x214082220481,0x0,0x0,0x0,0x0,0x0,0x44108220501,0x4000220481,0x44108220501,0x4000220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_2306 : TreeBound (n := 4) 107 (programCode 0x4e2907641e) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x400020011000000044000000090000000240002010100000010400020101000000100002010000002010000010080000010080402000100002000104020001000020001001087d7a7,0xf300012fc00088b00012fc0798f301e63cc03cc0025f800097e7980f3102307983cca7107987983d1426,0x0,0x10c041208481,0x40c041208481,0x10c041208481,0x10c041208481,0x0,0x0,0x0,0x0,0x40c041208481,0x0,0x40c041208481,0x0,0x2000880028000a00080104004100102010080ce3,0x43382001c00208001010000008002000024000219c100000010400000801000000100002010000002040000010080000020080433800100002000100100000800020001001087dea7,0x4000900028000a00080104004100102010080ce3,0x800028000200080104004100002010080ce3,0xf300012fc00088b00012fc0798f301e63cc03cc0025f80011167981e6102307983cc97e07987983d1426,0x0,0x80006000201100044000000000220000804021a4,0x1dcd6500077acc997d3fc10f765000eee25d9403b9ca6d6500077360b359b7377c0365201aafee6b2800003b9bb86b2807735a2e6b281dcd82cd65077360b35943b9b059aca03b9b059aca03b9b059ad8e6b283bb94a355e0ee6b2800000f047fe5000ee6d04d6500ee6d0c7dcc459,0x0,0x8000a000201100044000000000220000804021e4,0x80006000200100004000000000220000804021a4,0x80006000202100084000008000220000804021a4,0x80006000200100804000008000220000804021a4,0x80006000202100104000000000220000804021a4,0x80006000200100044000000000220000804021a4,0x400000005000000044000000050000000101000800001000800010008000010008005000020000002000450020200140000001100008000100080001000280001000200010025b1a8],
[0x0,0x400000005000000044000000050000000100800800008000800008008000020008001000080000008000450020800140000001100008000100080001000280001000200010025b1a8,0xf307983cc03fa83000b7331e601e679807980a710f33cc01e67980799e9cc003db3000f314e21e6554c5,0x80006000220100804000008000220000804021a4,0x1dcd65001dd4d8597b9acbdcd65001dd4d85943b9ae7cd650025429b168b9aca7735a2e6b29dcd653b9ad1735a2e6b287735940ee6b283b9b059acaee6c166b2803b9b059aca3b9b059aca03b9b05a23d594003bb89765000ee729b59403bb89765000ee6b45cd650ee8ad9df47e19,0x8000a000240101004000008000220000804021e4,0xf300012fc0004bf00012fc03ccf303cc3cc03cc007980f37b660007980fa99e60798003d398f307a2d36,0x0,0x400000011000000024000000110000000140031000100084000000088000000408006000300100000c00240000000040000001200030000800000001000200001000200010017efa8,0x0,0x0,0x0,0x0,0x0,0x0,0x400000003000000044000000050000000100040800000800800000808000002008000000000000000000440000000040000001100000000100000001000200001000200010024b1a8,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x800060002011000c4002018100620010804827a4,0x0,0x0,0x8000a000201100044004020100220020804825e4,0x800060002031000c4002018100620010804827a4,0x10089020a14c2,0x100a9020a14c2],
[0x10089020a14c2,0x80006000202100044002010100220010804827a4,0xf3000222c00088b0000f4e67980799e600f33cc01e7e60079bd398f301023003cfcc98d37987983eff36,0x0,0xf300012fc00088b0000f4e67980f31e601e63cc00f4e60079f9f98f301023001e9cc98d37987983e0726,0x0,0x100a1020a14c2,0x0,0x100a1020a14c2,0x400021001000004004000008010000020040002000100000000400020001000000000200010000200010001000080001000080400000100000000104000001000000001001087d7a7,0x0,0x80006000201100044008008200220008804221a4,0xf300012fc0004bf0000f30408c00408c000408c03cc00f6ced9003cc00fa99e607980008118f3079b3b6,0x0,0x8000a000201100044008008200220008804021e4,0x100a1040a10a2,0x10089040a14c2,0x100a1040a10a2,0x10089040a14c2,0x80006000201100044008008200220008804221a4,0xf300012fc00088b0000f4e67980799e600f33cc0799e601e6b6b9bcc0102300f33cc9d9279879844ac26,0x0,0xf300012fc00088b0000f4e67980f31e601e63cc0799e601e679f9bcc0102301e63cca3447987984c4426,0xf300012fc0004bf0000f3003ccf303cc00003cc03cc00f6cde6003cc00fa99e607980000798f3079b3b6,0x100a1040a10a2,0xf300012fc0004bf000111603ccf303cc1e603cc03cc00f6cde63cfcc00fa9ad907983cc0798f3079b3b6,0x100a1040a10a2,0x0,0x124044208481,0x424004200481,0x124044208481,0x424004200481],
[0x0,0x24004200481,0x0,0x0,0x424004200481,0x0,0x424004200481,0x0,0x0,0x24004200481,0x4000100208000200001004040100002000080ce3,0x0,0x0,0x80006000201100044008008400220008804221a4,0x0,0x0,0x8000a000201100044010008400220008804021e4,0x100a1040a10a2,0x10089040a14c2,0x100a1040a10a2,0x10089040a14c2,0x80006000200100044008000400220000804221a4,0xf300012fc00088b0000f4e67980799e600f33cc0799e603ccb6b9f980102300f33cc9bac79879844ac26,0x0,0xf300012fc00088b0000f4e67980f31e601e63cc0799e603cc79f9f980102300f33cc9f7879879844ac26,0x0,0x100a1040a10a2,0x0,0x100a1040a10a2,0x0,0x90402408002200482004080100401090082ca3,0x2004020408010200402004080102002080082ce3],
[0x908044080012004c2004080100201098082ea3,0x844108220501,0x41000000808018000812020001050004000206010000018040001420100004808040000200800004000800004001000008040c00008003000020284000080901000102ccc62e67,0x844108220501,0x0,0x0,0x804020408010200402004080102002080082ce3,0x0,0x808040408000200402004080100001080082ca3,0x0,0x844108220501,0x844108220501,0x844108220501,0x44108220501,0x0,0x0,0x404000200481,0x0,0x4000200481,0x4002000080800000040000000100080400020001000000804000002010000000040000020001000400004000200000000804000000800100002000400008000000010004862e27,0x4000200481,0x2021800002084000020000000020020040002100100000000400000801000000004200010000000040001000080000000080420000100000000100100001000000001001087dfa7,0x0,0x404000200481,0x79800f4e60079bcc012fc0798f301e63cc03cc3cc7980f31e67b6600102300f33cc9d9279879844ac26,0x404000200481,0x79800f6cc0079f98012fc0798f301e63cc03cc3cc7980f31e67b6600102301e63cca3447987984c4426,0x804000200481,0x4000200481,0x804000200481,0x4000200481,0x0],
[0x12fc0004bf1e612fc3cc001f530007d4c0f4ed9801e7e60079bcc01e603cc3cc0f30f4e9cc1ede5995,0x20808000200004004100100002000080ce3,0x408c001023798222c3cc003db3000f6cc0f6d39801e7e60079bcc01e607983cc1e60f4ed981ee03f95,0x844108220501,0x0,0x844108220501,0x0,0x0,0x800020808000200004004100100002000080ce3,0x80000040200000401000000401000001400004001000010004000080010000080040002000040000004580020004400000010800004002000a000100024c00100020001082575a8,0x1000040808000200004004100100002000080ce3,0x8000004080000040080000040200000140000800100000800400008001000008004000200004000000440002000040000001100001000100080001000210001000200012025b1a8,0x844108220501,0x844108220501,0x844108220501,0x44108220501,0x0,0x80002008002200000004000100402000080ce3,0x0,0x0,0x4000200481,0x3cc222cf308c7fcc12fc0798f301e63cc03cc7987981e61e67d4c0010230007d4c97fed987983d1936,0x4000200481,0x13ef0007d4c0012fc0798f301e63cc03cc3cc7981e61e67d4c00102300003cc97e07987983d1426,0x0,0x0,0x79800f4e60079bcc012fc0798f301e63cc03cc3cc7981e61e67d4c00102300f33cc9bac79879844ac26,0x0,0x79800f6cc0079f98012fc0798f301e63cc03cc3cc7981e61e67d4c00102300f33cc9f7879879844ac26,0x844108220501,0x4000200481,0x844108220501],
[0x4000200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_2499 : TreeBound (n := 4) 107 (programCode 0x4e2907641f) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x16c8000f3079816c8b64001f530007d4c1e7f53001e9cc01e6f3001e6f3001e7e6003db3001e7037c5,0x100802028020200408040a00020040000000104,0x16c80003cc1e625f92fc001f53000408c1e8e83001e9cc01e6f3001e679800f4e6003db3001e7032b5,0x100804028020200408040a00020040000000104,0x0,0x21c0c1220481,0x234086220481,0x21c0c1220481,0x214082220481,0x214082220481,0x234084220481,0x214082220481,0x0,0x234084220481,0x0,0x234084220481,0x0,0x2541c8220501,0x234084220481,0x2541c8220501,0x214080220481,0x0,0x63c0c1220481,0x24004220481,0x63c0c1220481,0x4000220481,0x434082220481,0x4000220481,0x434082220481,0x0,0x24004220481],
[0x0,0x24004220481,0x0,0x844108220501,0x4000220481,0x844108220501,0x4000220481,0x8118003cc1e60fa9fd4c01e6f30079bcc20c073001e9cc01e6f3001e679800f6cc007a73001e703345,0x0,0x4020200018060200880084002104002100084ce3,0x0,0x4020200028060200880104004104002100084ce3,0x200008040200000004000104002100080ce3,0x201200048044200100204008104002100080ce3,0x200008040200000004000104002100080ce3,0x402200088044200100404010104002100080ce3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x200808040200004004100104002100080ce3,0x0,0x3d39803cc1e603d3b69cc0000f307983cc1e60f3001e9cc01e6f3001e679800f4e6003db3001e7032b5,0x0,0x1060398003cc1f6770bb4403ea60044efe005d8073001e9cc01e6f3001e679800f4e6003db3001e7032b5,0x8008200200900024080006000200c00020100e4,0x1023798003cc1f632b191803ea600267180099c6f3001e9cc01e6f3001e679800f6cc007a73001e703345,0x0,0x0],
[0x0,0xf3079803cc1e6f6d3b6601e600008118003ea60f3001e9cc01e6f3001e679800f4e6003db3001e7032b5,0x8008200204100104080002000204400100804e4,0x0,0x0,0x0,0x0,0x0,0x0,0x8008200200100004080002000200400000000e4,0x0,0x3d39801e60f3079fd4fcc0000f300003cc1e60f3001e9cc01e6f3001e679800f6cc007a73001e703345,0x0,0x14e27980f307994e2a7100044580047310006684f3001e9cc01e6f3001e679800f4e6003db3001eacf2b5,0x10008400200900024080006000200c00020100e4,0x12fc7980f307992fc97e00044580027de0009f78f3001e9cc01e6f3001e679800f6cc007a73001eacf345,0x0,0x0,0x0,0x0,0x10008400204100104080002000204400100804e4,0x0,0x0,0xf6d3b663cc1e6fa9fd4c0f30000f379801e7e60f3001e9cc01e6f3001e679800fa9800f3f3001e7033d5,0x0,0x0,0x0,0x10008400200100004080002000200400000000e4,0x0,0x0,0x84c161220501,0x86418c220501],
[0x84c161220501,0x844108220501,0x8541c2220501,0x844108220501,0x8541c2220501,0x0,0x864184220501,0x0,0x864184220501,0x0,0x844108220501,0x844108220501,0x844108220501,0x844108220501,0x0,0x63c0c1220481,0x24004220481,0x63c0c1220481,0x4000220481,0x434082220481,0x4000220481,0x434082220481,0x0,0x24004220481,0x0,0x24004220481,0x0,0x844108220501,0x4000220481,0x844108220501,0x4000220481,0x800028020200408040a00020040000000104],
[0x0,0x84c161220501,0x8000200000004020104002100080ce3,0x84c161220501,0x4000220481,0x214082220481,0x4000220481,0x214082220481,0x0,0x0,0x0,0x0,0x0,0x44108220501,0x4000220481,0x44108220501,0x4000220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_2644 : TreeBound (n := 4) 107 (programCode 0x4e29076420) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0xf3000222c0004bf00012fc0f30f303cc3cc03ccf362b9e6097e0001e6111635283cc1e60f307983cfc26,0xf3000222c00088b00012fc0798f301e63cc03cc0025f800097e7980f311160f30798d4a0f30f3079d936,0x0,0x10c041200481,0x43002001908008001000000000040000024000201c1000000004000201c1000000100002010000002040000010080000020080400000100000000104000000800000001001087dea7,0x10c041200481,0x10c041200481,0x20c0c1204481,0x400810028004200080104004100102004080ce3,0x20c0c1204481,0x0,0x0,0x0,0x0,0x0,0x84c161220501,0x0,0x84c161220501,0xc041200481,0xf3000222c00088b00012fc0798f301e63cc03cc0044580011167981e611160f30798b640f30f3079d936,0xf307983cc002e83000ba0c1e60f307983cc007980f33cc01e67980799e9cc003db3000f301e61e64db45,0xf300012fc0004bf00012fc03ccf303cc3cc03cc007980f37b6600079810231e603cc003db307983d6d36,0x0,0x1140c2208481,0x0,0x1140c2208481,0x214082208481,0x214082208481,0x0,0x214082208481,0x20000100040000200200001000200001400008001000020004000080010000080000002000140408002002020000800000012000000004000a0202000001002000400020027aba8],
[0x0,0x0,0x0,0x0,0x8541c2228501,0x0,0x8541c2228501,0x214082208481,0x0,0x8000a000201100144004020100240021008845e4,0x0,0x0,0x8000a000201100044004020100240021008845e4,0x800060002031000c4002018100620011004827a4,0x10089020a14c2,0x100a9020a14c2,0x10089020a14c2,0x80006000202100044002010100220011004827a4,0xf3000222c00088b0000f4e67980799e600f33cc01e7e60079bd398f301116003d398b733f30f30b87f36,0x0,0xf3000222c00088b0000f6cc7980f31e601e63cc01e7e60079f9f98f301116003d398b733f30f30b87f36,0x0,0x100a1020a14c2,0x0,0x100a1020a14c2,0x0,0xf3000222c00088b0000f30f6cc003db3000f6cc0000000000000001e6111600007983cc0f30f3079d756,0x0,0x0,0x0,0x100a1010a10a2,0x10089010a10a2],
[0x100a1010a10a2,0x10089010a10a2,0xf300012fc00088b0000f307d4c7983cc0007d4c001e611160f30001e610231e607983cc0f30f3079b446,0x0,0x0,0x0,0x0,0x100a1010a10a2,0x0,0x100a1010a10a2,0x0,0x8000a000201100044008008200240009008041e4,0xf300012fc0004bf0000f30408c00408c000408c03cc00f6ce5f803cc010231e603cc00088b07983cf3b6,0x0,0x8000a000201100044008008200240009008041e4,0x100a1040a10a2,0x10089040a14c2,0x100a1040a10a2,0x10089040a14c2,0x80006000201100044008008200220009004221a4,0xf3000222c00088b0000f4e67980799e600f33cc0799e601e63d39bcc0111600f3798b826f30f30be3136,0x0,0xf3000222c00088b0000f6cc7980f31e601e63cc0799e601e679f9bcc0111601e6798ba0cf30f30c5c936,0xf300012fc0004bf0000f3003ccf303cc00003cc03cc00f6cde6003cc010231e603cc0000f307983cf3b6,0x100a1040a10a2,0xf300012fc0004bf000102303ccf303cc0f303cc03cc00f6cde63cfcc0102325f83cc1e60f307983cf3b6,0x100a1040a10a2,0x0,0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0xf30000b6400088b0000f31e9cc01e6f3003cfcc0000000000000f30000fa980007987980f30f30799076,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8000a000201100044010008400240009008041e4,0x0,0x0,0x8000a000201100044010008400240009008041e4,0x100a1040a10a2,0x10089040a14c2,0x100a1040a10a2,0x10089040a14c2,0x80006000200100044008000400220001004221a4,0xf3000222c00088b0000f4e67980799e600f33cc0f31e603cc3d39f980111600f3798ba0cf30f30be3136,0x0,0xf3000222c00088b0000f6cc7980f31e601e63cc0f31e603cc79f9f980111601e6798bdd8f30f30c5c936,0x0,0x100a1040a10a2,0x0,0x100a1040a10a2,0x0,0x14c168204501,0x0],
[0x14c168204501,0x844108220501,0x2541c8228501,0x844108220501,0x2541c8228501,0x0,0x0,0x0,0x0,0x0,0x844108220501,0x844108220501,0x844108220501,0x44108200501,0x0,0x82002088002200100404020100402010080ce3,0xf30f30f303cc0f312fc03ccf303cc3cc03cc1e60011161e601e60010231e603cc00088b07983cf3b6,0x102004088002200100404020100002010080ce3,0x4000200481,0x0,0x4000200481,0x0,0x0,0x1e612fc0003cc1e612fc03ccf303cc3cc03cc1e60011161e601e60010231e603cc00102307983cf3b6,0x79801e7e60079bcc012fc0798f301e63cc03cc3cc7980f31e67b6600111600f3798b826f30f30be3136,0x12fc0003cc00012fc03ccf303cc3cc03cc1e60011161e601e60010231e603cc0000f307983cf3b6,0xf3001e9cc0079f98012fc0798f301e63cc03cc3cc7980f31e67b6600111601e6798ba0cf30f30c5c936,0x844108220501,0x4000200481,0x844108220501,0x4000200481,0x0],
[0x14c168204501,0x0,0x14c168204501,0x844108220501,0x2541c8228501,0x844108220501,0x2541c8228501,0x8000040080000400100000800200001400004001000010004000040010000080000002000000008000380020008400000010800000008000007010003010020002000100257668,0x0,0x0,0x0,0x0,0x844108220501,0x844108220501,0x844108220501,0x44108200501,0x0,0x104040200481,0x0,0x104040200481,0x4000200481,0x204080200481,0x4000200481,0x204080200481,0x0,0x0,0x79801e7e60079bcc012fc0798f301e63cc03cc7987981e61e67d4c00111600f3798ba0cf30f30be3136,0x0,0xf3001e9cc0079f98012fc0798f301e63cc03cc7987981e61e67d4c00111601e6798bdd8f30f30c5c936,0x844108220501,0x4000200481,0x844108220501],
[0x4000200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_420 : TreeBound (n := 4) 107 (programCode 0x4e290764) := by
  conv in programCode _ => reduce
  exact branchFour (k := (0,1)) (by decide +kernel) part003_421 part003_422 part003_567 part003_568 part003_729 part003_842 part003_1003 part003_1116 part003_1357 part003_1534 part003_1743 part003_1920 part003_2129 part003_2306 part003_2499 part003_2644

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_2837 : TreeBound (n := 4) 107 (programCode 0x4e290765) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 4)
    (a := List.flatten [
[0x8001200048040200108004200108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_2838 : TreeBound (n := 4) 107 (programCode 0x4e290766) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 4)
    (a := List.flatten [
[0x0,0x8002200108040200100084002108002200080ce3,0x8002200048020200400142002048040a00010104,0x8002200108040200100104004108002200080ce3,0x0,0x8002200108040200100084002100082002080ce3,0x0,0x1010501184222,0x1010501184222,0x1010501184222,0x1010501184222,0x1010d01184222,0x1010901104222,0x1010501184222,0x1010901104222,0x1010901104222,0x0,0x0,0x0,0x8000200002040080002004080100002020080ce3,0x1012101104222,0x8000200004040100004004100100002020080ce3,0x1012101104222,0x8002200108040200100104004100102004080ce3,0x8000200008040200000004000100002000080ce3,0x8000200008040200000004000100202008080ce3,0x8000200008040200000004000100002000080ce3,0x8000200008040200000004000100402010080ce3,0x0,0x1010d01188642,0x1010501188642,0x1010d01188642],
[0x1010501188642,0x1010d01188642,0x1010901108642,0x1010d01188642,0x1010901108642,0x1010901108642,0xf3000408c003db30003ccf33cc0f33cc00f33cc001e63cc07d4c001e63cc3ea6000f307983cc03ec0036,0x0,0xf3000408c003db30003cde63cc079bcc01e63cc001e63cc088b0001e63cc3ea6000f307983cc04472036,0x0,0x1012101108642,0x0,0x1012101108642,0x0,0x1010d0118c642,0x101050118c642,0x1010d0118c642,0x101050118c642,0x1010d0118c642,0x1010901108642,0x1010d0118c642,0x1010901108642,0x1010901108642,0xf3000408c003db30003ccf33cc0f33cc00f33cc001e63cc07d4c001e63cc204601e60f3001e603eb0d36,0x0,0xf3000408c003db30003cde63cc079bcc01e63cc001e63cc088b0001e63cc204607983cc001e604462d36,0x8000200002040080002004080100802020080ce3,0x1012101108642,0x8000200004040100004004100100802020080ce3,0x1012101108642,0xf3000408c003db3000408c03ccf303cc3cc03cc001e63cc097e0001e63ccf4e600f307980f3003fa3d36,0x0],
[0x80022001000c0002100084002101002040080ce3,0x0,0x8002200100140004100104004101002040080ce3,0x8000200000040000000004000101002040080ce3,0x8004200000240008000204008101002040080ce3,0x8000200000040000000004000101002040080ce3,0x8004200000440010000404010101002040080ce3,0x8000200000040000000004000101002040080ce3,0x8000200000840020000804020101002040080ce3,0xf3000408c003db30003ccf33cc0f33cc00f33cc001e63cc07d4c001e6408c1e6003cc1e9cc0003eed936,0x0,0xf3000408c003db30003cde63cc079bcc01e63cc001e63cc088b0001e6408c1e6007983cfcc00044dc536,0x8000200002040080002004080101002040080ce3,0x0,0x8000200004040100004004100101002040080ce3,0x0,0xf3000408c003db3000408c03ccf303cc3cc03cc001e63cc097e0001e63cde7e6007983cc1e60044dc536,0x0,0x1340c1220481,0x404004220481,0x1340c1220481,0x4000220481,0x224082220481,0x4000220481,0x224082220481,0x0,0x404004220481,0x3cc03cfcc03cc3cc0408c03ccf303cc3cc03cc001e63cc097e0001e63cc204601e60f3001e603eb0d36,0x404004220481,0x79803cde603cc7980408c03ccf303cc3cc03cc001e63cc097e0001e63cc204607983cc001e604462d36,0x804008220481,0x4000220481],
[0x804008220481,0x4000220481,0xf3000408c003db3000408c03ccf303cc3cc03cc001e63cc097e0001e63d399e607983cc0798004462d36,0x0,0x1340c1220481,0x404004220481,0x1340c1220481,0x4000220481,0x224082220481,0x4000220481,0x224082220481,0x200008040200000004000104002100080ce3,0x404004220481,0x0,0x404004220481,0x0,0x804008220481,0x4000220481,0x804008220481,0x4000220481,0xf3000408c003db3000408c03ccf303cc3cc03cc001e63cc097e0001e63db31e603cc1e60f300040b5336,0x8004200008040200000204008108002200080ce3,0x8000200008040200000004000108002200080ce3,0x8004200008040200000404010108002200080ce3,0x0,0xf30820ecc001f53001e60113460016c80003d3a733d39bcc0079800f4e9cc003db3000f6cc001e64dcf5,0x1010502140442,0x0,0x1010902108442,0x1010d02104442,0x1010902108442,0x1010d02104442],
[0x1010902108442,0x1010902108442,0x1010902108442,0x1010902108442,0x1010902108442,0x1010902110442,0x0,0x1010902110442,0x400021101000000804000000810000008000022100000088000000120000000200806002010010000008004000020000020080200000100100000400400000801000001000487f227,0x0,0x400021101000000004000000810000008000022100000088000000120000000200806002010010000008010000020000020080200000100800000401000000802000001000487f227,0x0,0x1010502140442,0x1010902140442,0x1010902140442,0x1010902140442,0x1010902140442,0x1010902140442,0x8002200041020020400432010048042200086704,0x0,0x1310c4240481,0x1023798408c00007980003cde600f300001e60000f307983cc0f307981e9cc003db3000f6cc001e68a925,0x1310c4240481,0x0,0x221084240481,0x1004240481,0x221084240481,0x401004240481,0x401004240481,0x1004240481,0x401004240481,0x401004240481],
[0x801004240481,0x1004240481,0x801004240481,0x1004240481,0x8002200041020040400422010048042200084504,0xf307983cc0000f300001e61e601e679807980016c8079bcc00799e601e9cc003db3000f6cc001e64dcf5,0x1012102140442,0xf307983cc0000f300001e61e607987980f300016c8079bcc0079bcc01e9cc003db3000f6cc001e64dcf5,0x1012102140442,0x8000200008040200000804020108002200080ce3,0x8002200048020200401042020048048200102b04,0x0,0x1340c4240481,0x102002048020200408142002048040a00010104,0x1340c4240481,0x0,0x5340c4204481,0x0,0x5340c4204481,0x0,0x404004208481,0x404004200481,0x404004208481,0x0,0x0,0x420020001080000000000000000400000040002000100000000400000001000000000200010000800020001000080002000080400000101000000404000000800000001001087faa7,0x0,0x420020001080000000000000000400000040002000100000000400000001000000000200010000800020001000080002000080400000101000000404000000800000001001087faa7,0x404004220481,0x404004200481,0x404004220481,0x420020001080000000000000000400000040002000100000000400000001000000000200010000800020001000080002000080400000100000000404000000800000001001087faa7],
[0x224084240481,0x4004240481,0x224084240481,0x0,0x1304c4240481,0x1023798408c000079800408de6102300001e60000f307983cc0f307981e9cc003db3000f6cc001e68a925,0x1304c4240481,0x0,0x220884240481,0x4240481,0x220884240481,0x4240481,0x401004240481,0x4240481,0x401004240481,0x4240481,0x802004240481,0x4240481,0x802004240481,0x4240481,0x404004240481,0x1002020048020200409042020048048200102b04,0x404004240481,0xf307983cc00000000003cc1e60f300003cc00000f307983cc07987981e9cc003db3000f6cc001e64dcf5,0x804004240481,0x4004240481,0x804004240481,0x4004240481,0xf3000408c003db3000408c03ccf303cc3cc03cc079803cde7e6007980408c1e60f307983cc00f381a6d6,0x8000200008040200002004080108002200080ce3,0x8002200048020200404042080048060200402304,0x8000200008040200004004100108002200080ce3],
[0xf307983cc0000f300003cc1e60f307983cc0000f30079bcc007980001e9cc003db3000f6cc001e64dcf5]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_3063 : TreeBound (n := 4) 107 (programCode 0x4e290767) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 4)
    (a := List.flatten [
[0x8002200088040200108004200108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_3065 : TreeBound (n := 4) 107 (programCode 0x4e29076831) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0xf307983cc0002d90798b64001f5307983cc1e7e600f4e600f4e6000f4e6003ccf303cc3cc03cde7032b5,0xf307983cc01e6f307983cc0000f307983cc1e60000f4e600f4e6000f4e63cc01e6000079bcc01e703855,0xf307983cc0006a507992fc001f5307983cc1e7e600f4e600f4e6000f4e6003ccf301e67980799e703345,0xf307983cc000a710798b64001f5307983cc1e7e600f4e600f4e6000f4e6003cde604bf3cc12fde7037c5,0x0,0x1010902108442,0x1010502108442,0x1010902108442,0x1010502108442,0x1010902108442,0x1010902108442,0x1010902108442,0x1010902108442,0x1010902108442,0xf3000f6cc001f5300079bccf300f33cc00f33cd8dbcdb56af6fc9ab907fb715b7bac56dedf9357bad6c6,0x0,0xf3000f6cc001f5300079bccf30079bcc01e63cd6e69db4eda7307b6607f39c5cd3b71734e60f6d3b83c6,0x8001200402040080500084002100202008082ce3,0x1012102108442,0x8001200804040100140084002100202008080ee3,0x1012102108442,0x0,0x1010902108442,0x1010502108442,0x1010902108442,0x1010502108442,0x1010902108442,0x1010902108442,0x1010902108442,0x1010902108442,0x1010902108442],
[0xf30007d4c001f53000798f33cc0f33cc00f33cd116007983cfcd116007982046001ed9f981e61e7f6856,0x0,0xf30007d4c001f53000799e63cc079bcc01e63cd6c8007983db316c8007982046001ed9f981e61eda8856,0x8010200402040080400084002100402080082ce3,0x1012102108442,0x8000200804040100000084002100402000080ce3,0x1012102108442,0xf307983cc001f5307a3a0c01e6f307983cc20bf800f4e600f4e6000f4e601e60f307983cc3cc1e7032b5,0x0,0x1010902108442,0x1010502108442,0x1010902108442,0x1010502108442,0x1010902108442,0x1010902108442,0x1010902108442,0x1010902108442,0x1010902108442,0xf30007d4c001f53000798f33cc0f33cc00f33ccf3f3079f983ccf3f307983ea6000fb8b003cfcc1f6856,0x0,0xf30007d4c001f53000799e63cc079bcc01e63ccf3f307b660f30f3f307983ea6000fe64003db307a8856,0x8010200402040080400084002102002080082ce3,0x1012102108442,0x8020200804040100800084002104002100084ce3,0x1012102108442,0x0,0x1010902108442,0x1010502108442,0x1010902108442,0x1010502108442,0x1010902108442,0x1010902108442],
[0x1010902108442,0x1010902108442,0x1010902108442,0xf30007d4c001f53000798f33cc0f33cc00f33cd1253079fd4fcd125307983ea601e6892983cfea7f6856,0x0,0xf30007d4c001f53000799e63cc079bcc01e63cd6d7307b69db316d7307983ea60798b6b983db4eda8856,0x8004200402040080400084002100802020082ce3,0x1012102108442,0x8004200804040100100084002100802020080ce3,0x1012102108442,0x0,0xf3000f6cc003db30007fb6f3301e60f3003cfcd8dc0aecf9800000f3079bcf1b723ccf300f33cc1f70f6,0xf3000f6cc003db30007981023000408c000408d8dc56dcf983cc00f3079bcf1b72f30f300f33cc1f7156,0x0,0xf3000f6cc003db30007981023000408c0007d4d8dc56dcf983cc00f3079bcf1b72f30f300f33cc1f7156,0xf3000f6cc003db30007d5773300000f300003cd8dc0a7379800000f3079bcf1b723ccf300f33cc1f70f6,0x80022000802100084020022100808500204024e4,0xf3000f6cc003db30007fb6f3301e60f307983cd8dc0aecf9801e60f3079bcf1b723ccf300f33cc1f70f6,0x80022000804100104020002100808500204024e4,0x80022000800100104020002100808500204024e4,0xf30007d4c001f53000798f33cc0f33cc00f33ccf3f3079f983ccf3f30798f4e600f388b00f33cc1f6856,0x0,0xf30007d4c001f53000799e63cc079bcc01e63ccf3f3079f98f30f3f30798f4e600f388b00f33cc98e856,0xf3000f6cc003db30007d53a730f303cc00003cd6f60a7379800000f3079bcf1b72f30f300f33cc1f7156,0x80022000820100804020022100808500204024e4,0xf3000f6cc003db30007f3d7330f303cc07983cd6f60aecf9801e60f3079bcf1b72f30f300f33cc1f7156,0x80022000840101004020022100808500204024e4,0x0,0x16c8000f3f30017235cc001f530007d4c1e8d900f4e600f4e6000f4e60f300f33cc03cde601e7032b5,0xf379800000f30f37983cc0000f300003cc1e60000f4e600f4e6000f4e61e601e67980799e601e703855,0x25f80007a730025f83cc001f530007d4c1e60000f4e600f4e6000f4e61e601e67980799e601e703855,0x3ccf300f33cc01e67d4c0f30f303cc3cc03ccf307a73001e60000007d4d1160f300000007980001e56],
[0x0,0x0,0x8118001e6f300faf35cc01e6f30079bcc20bf800f4e600f4e6000f4e60f300f33cc03cde601e7032b5,0x0,0x0,0x0,0x3d39800f30f3079ff35cc0000f300003cc1e60000f4e600f4e6000f4e60f300f33cc03cde601e7032b5,0x0,0x0,0x0,0x1e679807980f33cc7f35cc00f3f3003cfcc1fcc800f4e600f4e6000f4e60f300f33cc03cde601e77cab5,0x0,0x0,0xf3000f6cc003db30007f3d73301e60f3003cfcd6f60aecf9800000f3079bcf1b72f30f301e63cc1f70f6,0x400021001000004004000000010000020042002000008000000000020000040000000002010000008040000010080000010080420000101000000400200001000000001001087ffa7,0x0,0x400000101000000104000001010000001000021000000024000000208000000208007028381400020001010000800000200010020038140020080000200080000200200010087dfa8,0xf3000f6cc003db30007d5773300000f300003cd6e6da7379800000f3079bcedcccf30f301e63cc1f70f6,0x80022000802100084020022100810500404024e4,0xf3000f6cc003db30007fb6f3301e60f307983cd6f60aecf9801e60f3079bcf1b72f30f301e63cc1f70f6,0x80022000804100104020002100810500404024e4,0x80022000800100104020002100810500404024e4,0xf30007d4c001f53000798f33cc0f33cc00f33ccf3f307b6603ccf3f30799e7e6007a36401e6f3098e856,0x0,0xf30007d4c001f53000799e63cc079bcc01e63ccf3f307b660f30f3f30799e7e6007a36401e6f307a8856,0x0,0x80022000820100804020022100810500404024e4,0x400030001000010004000000010000100020003000020000000200020000200000000002010000001008000010080000010080400000101000000104000001000000001001087d3a7,0x80022000840101004020022100810500404024e4,0x0,0x80102000100c0002090084002102002080080ce3,0x8010200100840020100084002102002080080ce3],
[0x80102000201400040a0084002102002080080de3,0x8010200018040002090084002102002080080ce3,0x8010200040240008140084002102002080080ee3,0x8010200000440000000084002102002080080ce3,0x8010200080440010180084002102002080080ce3,0x8010200002040000000084002102002080080ce3,0x8010200100840020100084002102002080080ce3,0xf3000f6cc003db300079bccf300f33cc00f33cd8dbcdb303cfcc1e6007f39c9b8130798079801e7f7156,0x0,0xf3000f6cc003db300079bccf300f33cc01e63cd6e69db307a7307b6607f39c5cdb30b734e6003d3b8456,0x8010200402040080400084002102002080082ce3,0x8010200008040000000084002102002080080ce3,0x8010200804040100c00084002102002080086ce3,0xf3000f6cc003db30007b660f307983cc0f303ccf4e60f307983cc1e607d53b69db307a7307983cc20456,0x0,0x1010902120442,0x1010502120442,0x8006200020140004180084002108002030080ce3,0x1010502120442,0x1010902120442,0x1010902120442,0x1010902120442,0x1010902120442,0x1010902120442,0xf30007d4c001f53000798f33cc0f33cc00f33cd116007983cfcd1160079f99e6079879f9f9801e7f6856,0x0,0xf30007d4c001f53000799e63cc079bcc01e63cd6c8007983db316c80079f99e6079879f9f9801eda8856,0x8010200402040080400084002108002080082ce3,0x1012102120442,0x8000200804040100000084002108002000080ce3,0x1012102120442,0xf307983cc0798f30a713cc0798f307983cc29c4000f4e600f4e6000f4e679800f4e6003db3001eacf2b5],
[0x0,0x1010902120442,0x1010502120442,0x0,0x1010502120442,0x1010902120442,0x1010902120442,0x1010902120442,0x1010902120442,0x1010902120442,0xf30007d4c001f53000798f33cc0f33cc00f33cd116007983cfcd116007a731e603cc79fa73001e7f6856,0x0,0xf30007d4c001f53000799e63cc079bcc01e63cd6c8007983db316c8007a731e603cc79fa73001eda8856,0x0,0x1012102120442,0x0,0x1012102120442]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_3242 : TreeBound (n := 4) 107 (programCode 0x4e29076832) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0xf30798b640002d9000079897e00016cf9803cdf53003cfea60798b641e9cc003db3000f6cc001e64db45,0x0,0x1010501184222,0x1010501184222,0x1010501180222,0x1010501184222,0x101050118c642,0x1010501188642,0x1010501184222,0x1010501188642,0x101050118c642,0x1010501390b02,0x0,0x1010501390b02,0x8004200100840020000804020102002080080ce3,0x400000041000000204000000810000001000004200000084000000108000000108000000400400008c824000100008000100100400220108000480010000200010000002240952ea8,0x8004200100840020000804020104002100080ce3,0x1dcd65001dd4d859400775361650003c11ff94003bb897650003b9aca79126a50001e449a94000079126a500079126a5000079126a5001f332477d02f7712eca0001dcda09aca1dcd65ee6b29dcda0d664cf9686b893528ee6b2f73597b9ad173594ee6b2f73594000f049e652bf1a,0x0,0x1010501184222,0x1010501184222,0x1010101100222,0x1010501184222,0x1010d0118c642,0x1010d01188642,0x1010501184222,0x1010d01188642,0x1010d0118c642,0x0,0x0,0x0],
[0x8010a000201400040a0104020102002080080de3,0x40002001100000000c000000030000000500022010000010010000220000000280404200010000900020042000080004000080402000100002000084000001010080001001087cba7,0x1dcd6500002540be7b9acbdcd651dcd6c7359400009502f900001dcd662a05f20000fd51da80003f5476a0000861c4680000f5e05e1dc35943ba23d5940ee6b639aca03b9aca00ee7a0eba6a8ed7b9b41359400eee25d9400ee88f565003b9e83aca00773d0759400eea7507e527c9,0x0,0x0,0x1010501184222,0x1010501184222,0x1010501180222,0x1010501184222,0x101050118c642,0x1010501188642,0x1010501184222,0x1010501188642,0x101050118c642,0x1010501390b02,0x0,0x1010501390b02,0x8000200008040000000004020102002080080ce3,0x0,0x8000200008040000000004020104002100080ce3,0x0,0xf3079c08c0010230003cc3ea60008136601e67a73003cfea60798b641e9cc003db3000f6cc001e64db45,0x80022000802100084000820020880402000100e4,0x4000000410000800040000004100000010000820000004080000010200000020008002000020100000400400000200090000804000000410000002040000008100000010004852e27,0x80022000804100104000800020880402000100e4,0x80022000800100104000800020880402000100e4,0x0,0x45250807a73000f30432a5942798079800001023079c08c0f307981e9cc003db3000f6cc001e68a925,0x820020808100204000900020880402000100e4,0x0,0x0,0x24820900808100204000900020880402004924e4],
[0x2020080808100204000900020880402000526e4,0x80020020808100204000900020880402000100e4,0x4020100808100204000900020880402000924e4,0x20020100808100204000900020880402000924e4,0x802020080810020400090002088040200112ce4,0x8020000808100204000900020880402000100e4,0x10020400808100204000900020880402002134e4,0x24020800808100204000900020880402004124e4,0x20020800808100204000900020880402004124e4,0x80020020808100204000900020880402000100e4,0x40021000808100204000900020880402008164e4,0x0,0x404000008800000004040000010100008020000040000100100000400200001002000020100000400400000200090000804000000410000002040000008100000010004852e27,0x0,0x0,0x0,0x820000800100004000800020880402000100e4,0x1e60f301e63cc07987d549a30001023001e9cc0044698f83cde600f37d4c1e688b07983cc0001e61df6,0x8004000040800000100040000200100008020000040004000100002000200008002000020100000400400000200090000804000000410000002040000008100000010004852e27,0x1e60f307983cc0f307d549a30001023003cfcc0044698f83cc0000f37d4c1e688b07983cc0001e61df6,0xf531ff300003cc0f307d54d6f0001023003cfcc0044698f83cc0000f37d4c1e688b07983cc0001e61df6,0x802020080810020400090002088040200112ce4,0x20000800100004000800020880402000100e4,0x10020400800100404000900020880402002134e4,0x20000800100004000800020880402000100e4,0x20020800820100804000820020880402000100e4,0x80000400400080001000004002000010000802000004008000010000400020001000200002010000040040000020009000080400000041000000204000000810000001000c852e27,0x40021000840101004000820020880402000100e4,0x0,0x0,0x820020810100404000900020880402000100e4,0x0],
[0x0,0x24820900810100404000900020880402004924e4,0x2020080810100404000900020880402000526e4,0x80020020810100404000900020880402000100e4,0x4020100810100404000900020880402000924e4,0x20020100810100404000900020880402000924e4,0x802020081010040400090002088040200112ce4,0x10020000810100404000900020880402000100e4,0x10020400810100404000900020880402002134e4,0x24020800810100404000900020880402004124e4,0x20020800810100404000900020880402004124e4,0x80020020810100404000900020880402000100e4,0x40021000810100404000900020880402008164e4,0xf3088b3cc03ccf300f30f31e601e688b07983ccf3003cfea60798b641e9cc003db3000f6cc001e833b45,0x80022000820100804000820020880402000100e4,0x4000040010000800040000400100001000080020000400080001000200002000100002000020100000400400000200090000804000000410000002040000008100000010084852e27,0x80022000840101004000820020880402000100e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_3355 : TreeBound (n := 4) 107 (programCode 0x4e29076833) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0xf307983cc00088b0798b64001f5307983cc1e7e601e7e6003ea6001e7e6003cde603cc3cc03cde7037c5,0xf307983cc0000f307983cc0000f307983cc1e60001e7e6007b66001e7e63cc01e6000079bcc01e703855,0xf307983cc0002d907992fc001f5307983cc1e6f300f4e6003ea6001e7e6003ccf300f33cc0799e7032b5,0xf307983cc0002d90798b64001f5307983cc1e7e601e7e6003ea6001e7e600799e600f33cc03cde7037c5,0x0,0x1010900108022,0x1010500108022,0x1010100108022,0x1010500108022,0x1010900108022,0x1010900108022,0x1010100108022,0x1010900108022,0x1010900108022,0x0,0x0,0x0,0x8001200402040080500104004100202008082ce3,0x1012100108022,0x8001200804040100140104004100202008080ee3,0x1012100108022,0xf307983cc001f53081954c01e6f307983cc2046000f4e6007b66001e7e63cc00f30f307d8c8c1e703345,0xf307983cc001f53079fd4c01e6f307983cc2046000f4e6007b66001e7e601e60f30f307983cc1e703345,0xf307983cc0000f307983cc0000f307983cc1e60000f4e6003ea6001e7e9cc000f30000408c001e7032b5,0xf307983cc01e6f307b69cc0000f307983cc1e60000f4e6003ea6001e7e60f300f3f3003ccf301e7032b5,0x0,0x80022000100c0002180104004100402230080ce3,0x1010505390b02,0x1010100110022,0x1010505390b02,0x1010902110442],
[0x1010902110442,0x1010100110022,0x1010902110442,0x1010902110442,0xf30007d4c001f53000798f33cc0f33cc00f33ccf6cc0798f33ccf6cc0798f4e600f37b660f3079a33456,0x0,0xf30007d4c001f53000799e63cc079bcc01e63ccfa980799e6f30fa980798f4e600f37d4c0f30f3822056,0x8010200402040080400104004102002280082ce3,0x80022000820100804020022000808400204024e4,0x8000200804040100000104004100002200080ce3,0x80022000840101004040022000808400208044e4,0x0,0x16c8000f3f30016c83cc001f530007d4c1e60001e7e6007b66001e7e61e601e67980799e601e703855,0xf379800000f30f37983cc0000f300003cc1e60001e7e6007b66001e7e61e601e67980799e601e703855,0x16c80007a73002634fcc001f530007d4c1e7e600f4e6007b66001e7e60f300f37980799e601e703345,0x0,0x0,0x1e60f307983cc07987d4c0f30f303cc3cc03ccf307a73001e60000007d53b660f30000001e600001e56,0x8118003ccf300fad4fcc01e6f30079bcc20bf800f4e6007b66001e7e60f300f37980799e601e703345,0xf6d3b663cc1e6fa9fd4fcc0000f307983cc1e60000f4e600f4e6001e7e60f300f3f300f31e601e7033d5,0x3d3b663cc1e603d3d4fcc0000f307983cc1e60000f4e600f4e6001e7e60f300f3f300f31e601e7033d5,0x0,0x3d39801e60f3079fd4fcc0000f300003cc1e60000f4e6007b66001e7e60f300f37980799e601e703345,0x0,0x0,0x0,0x1e67980f300f33cc7d4fcc00f3f3003cfcc1f53000f4e6007b66001e7e60f300f37980799e601e77cb45,0x0,0x0,0x0,0x1010505390b02,0x1010100110022],
[0x1010505390b02,0x1010902110442,0x1010902110442,0x1010100110022,0x1010902110442,0x1010902110442,0xf30007d4c001f53000798f33cc0f33cc00f33ccf6cc079bcc3ccf6cc0799e7e60079fb661e61e62e9856,0x0,0xf30007d4c001f53000799e63cc079bcc01e63ccfa980799e6f30fa980799e7e60079fd4c1e60f3822056,0x0,0x80022000820100804020022000810400404024e4,0x0,0x80022000840101004040022000810400408044e4,0x0,0x80102000100c0002090104004102002080080ce3,0x8010200100840020100104004102002080080ce3,0x80102000201400040a0104004102002080080de3,0x80102000280400040a0104004102002080080de3,0x8010200040240008140104004102002080080ee3,0x8010200000440000000104004102002080080ce3,0x8010200080440010180104004102002080080ce3,0x8010200002040000000104004102002080080ce3,0x8010200100840020100104004102002080080ce3,0x0,0x0,0x0,0x8010200402040080400104004102002080082ce3,0x8010200008040000000104004102002080080ce3,0x8010200804040100c00104004102002080086ce3,0x0,0x0,0x16c8000f31e60176b80c01e6f30007d4c20ed100f4e6003ea6001e7e63cc00f30f3040dda21e7032b5],
[0xf37980f31e600f37d4c03ccf303cc3cc03cd116f379805b211160079f99e6079888b8118001e61556,0x16c8000799e60267954c01e6f30007d4c2064600f4e6007b66001e7e63cc00f30f307d8c8c1e703345,0x4002a1320000280004000000400001800040002132100000200400000041000080000002010000008040000004080000020080426400100040000400008000210000001001087fca7,0x0,0x0,0x8118001e7e600fab69cc0000f30079bcc1ed9800f4e6003ea6001e7e600000f3f300409b301e7032b5,0x0,0x0,0x0,0x3d39800f3000079f983cc0000f300003cc1e60000f4e6003ea6001e7e600000f30000408c001e7032b5,0x0,0x0,0x0,0x1e679807980003cc7983cc0000f300003cc1e60000f4e6003ea6001e7e600000f30000408c001e7032b5,0x0,0xf307983cc0798f3097e3cc0798f307983cc25f8000f4e6007b66001e7e679800f6cc007a73001eacf345,0x0,0x0,0x0,0x16c80003cc00025f83cc0000f3000408c1e7e600f4e6003ea6001e7e600000f30000408c001e7032b5,0x0,0x81180079805b28119a94001f53001e9cc1ef7e00f4e6007b66001e7e9ccb64f302d97d4cb65e703345,0x0,0x8118001e601e6fa99a94001f530079bcc1f07100f4e6003ea6001e7e9ccb64f300f3408cb65e7032b5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1e67980f307983cc97e3cc0798f301e63cc25f8000f4e6007b66001e7e6f3000f6cc007e3f001eacf345],
[0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_3484 : TreeBound (n := 4) 107 (programCode 0x4e29076834) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0xf307983cc0002d90798b64001f5307983cc1e7e600f4e6003ea6000f4e6003ccf303cc3cc03cde7032b5,0x0,0x1010501184222,0x1010501184222,0x1010501184222,0x1010501184222,0x1010d01184222,0x1010901104222,0x1010501184222,0x1010901104222,0x1010901104222,0x0,0x0,0x0,0x0,0x1012101104222,0x0,0x1012101104222,0xf307983cc0004bf07992fc001f5307983cc1e7e601e7e6007b66001e7e6003ccf301e67980799e703345,0xf307983cc0000f307983cc0000f307983cc1e6000001e60001e600001e600000f300003cc0001e7032b5,0xf307983cc0000f307983cc0000f307983cc1e6000001e60001e600001e601e60f31e603cc1e61e7032b5,0x0,0x1010d01188642,0x1010501188642,0x1010d01188642,0x1010501188642,0x1010d01188642,0x1010901108642,0x1010d01188642,0x1010901108642,0x1010901108642],
[0xf30007d4c003db3000799e67980799e600f33cc002046000fea0c01e67983cc1e60faa08b1e607f64d26,0x0,0xf30007d4c003db3000799e67980f31e601e63cc002046000fad4c01e67983cc1e60faa08b1e607d7ed26,0x0,0x1012101108642,0x8000200804040100000004000100002000080ce3,0x1012101108642,0xf307983cc0000f307983cc0000f307983cc1e6000001e60001e600001e601e60f307983cc3cc1e7032b5,0x0,0x1010d01188642,0x1010501188642,0x1010d01188642,0x1010501188642,0x1010d01188642,0x1010901108642,0x1010d01188642,0x1010901108642,0x1010901108642,0xf30007d4c003db3000799e67980799e600f33cc002046000fea0c01e67983cc1e61eda8233cc07f64d26,0x0,0xf30007d4c003db3000799e67980f31e601e63cc002046000fad4c01e67983cc1e61eda8233cc07d7ed26,0x0,0x1012101108642,0x0,0x1012101108642,0x0,0x1010d0118c642,0x101050118c642,0x1010d0118c642,0x101050118c642,0x1010d0118c642,0x1010901108642],
[0x1010d0118c642,0x1010901108642,0x1010901108642,0xf30007d4c003db3000799e67980799e600f33cc002046000fea0c01e67a7307985d1081233cc07d6fa26,0x0,0xf30007d4c003db3000799e67980f31e601e63cc002046000fad4c01e67a7307983eaf8e233cc07d6fa26,0x0,0x1012101108642,0x0,0x1012101108642,0x0,0x4000000810000002040000010100000010100002001556c2000040008000110008000001000400004aab6000202040000200100040002000400aab601000080001000004044a62ba8,0x1010501390b02,0x0,0x1010501390b02,0xf30007d4c001f5300079fd4fcc0f33cc07d4fcc001e679807d6a601e6798f4e63db307980f3003fab6b6,0x1010901110b02,0x400020101000000404000000010000001000202100000800000002020000002002004020010010080040000000080000000080420000101000000400100001000000001001087ffa7,0x1010901110b02,0x1010901110b02,0xf30007d4c003db3000799e67980799e600f33cc002046000fea0c01e6799e60f3079fd5b3f3007de9226,0x0,0xf30007d4c003db3000799e67980f31e601e63cc002046000fad4c01e6799e60f3079fd5b3f3007de9226,0x0,0x1012101110b02,0x400030001000040004000000010000100020003000080000000080020000200000004000010000000040000000080000000080600000101000000400000000400000001001087fda7,0x1012101110b02,0x0,0x0,0x0,0x0,0x8000200000040000000004000101002040080ce3],
[0x8001200040240008100204008101002040080ce3,0x8000200000040000000004000101002040080ce3,0x8002200080440010100404010101002040080ce3,0x8000200000040000000004000101002040080ce3,0x8004200100840020000804020101002040080ce3,0xf30007d4c003db3000799e67980799e600f33cc002046000fea0c01e6799e60f3fe6bf44fc0007de9226,0x0,0xf30007d4c003db3000799e67980f31e601e63cc002046000fad4c01e6799e60f4023812afc0007de9226,0x0,0x0,0x0,0x0,0x0,0x400020011000000044000000010000000080022010000080000000120000000100104000010010000040000000080000000080400000101000000400000001000000001001087ffa7,0x1010501390b02,0x4000200110000000440000000100000001000220100000800000000a0000000200104000010000000040000000080000000080400000101000000400000000400000001001087fda7,0x1010501390b02,0xf30007d4c001f530007b69cfcc079bcc1e9cfcc001e6798088ce601e6799e7e63d3983cc1e60044e3eb6,0x1010901110b02,0x0,0x1010901110b02,0x1010901110b02,0xf30007d4c003db3000799e67980799e600f33cc002046000fea0c01e6799e60f30f381274e6007de9226,0x0,0xf30007d4c003db3000799e67980f31e601e63cc002046000fad4c01e6799e60f30f381274e6007de9226,0x0,0x1012101110b02,0x400030001000040004000000010000100020003000080000000200020000200000004000010010000040000000080000000080400000101000000404000001000000001001087ffa7,0x1012101110b02,0x0,0x0,0x0],
[0x0,0x79800000000007983cc0000f300003cc1e6000001e60001e600001e679800fa98003d39801e7032b5,0x0,0x0,0xfa98001e61e60fa9fd4c01e6f30079bcc20bf80f31e603cde600f31e679801ed98003d39801e7037c5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1e67980f307983cc97e3cc0798f301e63cc25f85b201e76c81e65b201e679800fa980079f9801eacf345,0x0,0x0,0x80022000804100904001020040820100800225e4,0x400021001000004004000000010000020042002000008000000000020000040000004000010010000040000000080000000080400000100000000404000001000000001001087ffa7,0x0,0xf30007d4c003db300079808118003ea60007d4c00204600119388c1e67a7307983cc97efa98007d6fa26,0x80022000820100104001020040820100800225e4,0x10109011212c2,0x400000021000000404000000210000001010000800110010800100008000100108000000620420008004000004204200020050100008000100088009000080001000080084084b0a8,0x10109011212c2,0x10109011212c2,0xf30007d4c003db3000799e67980799e600f33cc002046000fea0c01e67a7307983cc97efa98007d6fa26,0x0,0xf30007d4c003db3000799e67980f31e601e63cc002046000fad4c01e67a7307983cc97efa98007d6fa26,0x0,0x10121011212c2,0x400030001000040004000000010000100020003000080000000200020000200000004000010010000040000000080000000080600000100000000404000001000000001001087ffa7,0x10121011212c2,0x0],
[0x16c8000fa980018ae3cc0798f30007d4c2616604c0e600f4e6004c0e6f3001e7e6003db3001eacf7c5,0xf379800000000f37983cc0000f300003cc1e6000001e60001e600001e6f3001e9cc007a73001e703855,0x16c800081180027de3cc0798f30007d4c2616601e7e6007b66001e7e679800f6cc007a73001eacf345,0x79800000000007983cc0000f300003cc1e6000001e60001e600001e679800f4e6003db3001e7032b5,0x0,0x7980000000f307983cc0000f307983cc1e6000001e60001e600001e6f3001e9cc007a73001e703855,0x8118003cc1e60fa9fd4c01e6f30079bcc20bf80f31e603cde600f31e679800f6cc007a73001e703345,0xf307980000000f307983cc0000f307983cc1e6000001e60001e600001e6f3001e9cc007a73001e703855,0x0,0x0,0x0,0x0,0x0,0x0,0x1e67980f307983cc97e3cc0798f301e63cc25f83cc01e6f301e63cc01e679800f6cc007a73001eacf345,0x0,0x0,0x80022000804101104001020040840201000245e4,0x0,0x0,0xf30007d4c003db300079808118003ea60007d4c00204600120d08c1e67a730798798b650230007d6fa26,0x80022000840100104001020040840201000245e4,0x10109011212c2,0xf3000f6cc00102300080a038701e63cc0f3408c004b1ae684469161e67b6639016860f30f3079a2449b6,0x10109011212c2,0x10109011212c2,0xf30007d4c003db3000799e67980799e600f33cc002046000fea0c01e67a730798798b650230007d6fa26,0x0,0xf30007d4c003db3000799e67980f31e601e63cc002046000fad4c01e67a730798798b650230007d6fa26,0x0,0x10121011212c2,0x0],
[0x10121011212c2]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_3677 : TreeBound (n := 4) 107 (programCode 0x4e29076835) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x80012000100c0002180204008108002200080ce3,0x1010502140442,0x8001200020140004180204008108002200080ce3,0x1010502140442,0x1010902140442,0x1010902140442,0x1010902140442,0x1010902140442,0x1010902140442,0x8002200081020020406432190088072200c86504,0x0,0x1310c2240481,0xf3000408c000f33cc3cc3cde600f301e61e607980799e601e67980799e9cc003db3000f6cc001e64d995,0x1310c2240481,0xf3000408c000f3079bcc3cde600f301e61e607980799e601e67980799e9cc003db3000f6cc001e64d995,0x231082240481,0x431082240481,0x231082240481,0x631082240481,0x431082240481,0x431082240481,0x431082240481,0x431082240481,0x8310c2240481,0x431082240481,0x8310c2240481,0x631082240481,0x8002200081020040404422110088062200884504,0x8001200402040080500204008108002200082ce3,0x1012102140442,0x8001200804040100140204008108002200080ee3],
[0x1012102140442]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_3710 : TreeBound (n := 4) 107 (programCode 0x4e29076836) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x80066000100c0002180c04030108002200080ce3,0x1010502140442,0x8006a00020140004180c04030108002200080ce3,0x1010502140442,0x1010902140442,0x1010902140442,0x1010902140442,0x1010902140442,0x1010902140442,0x8002200081020020400432008088043200086504,0x0,0x1310c6240481,0xf300003cc000003cc3cc3cde600f300001e600000001e600007980001e9cc003db3000f6cc001e64d995,0x1310c6240481,0xf300003cc000000003cc3cde600f300001e600000001e600007980001e9cc003db3000f6cc001e64d995,0x221084240481,0x21000240481,0x221084240481,0x421000240481,0x421000240481,0x21000240481,0x421000240481,0x421000240481,0x821084240481,0x21000240481,0x821084240481,0x421000240481,0x8002200081020040400422008088043200084504,0x0,0x96402402002080582c040b0108002200082ce3,0x110902140442],
[0x116804402002080582c040b0108002200082ce3,0x110902140442,0x2721ce240501,0x842108240501,0x2721ce240501,0x842108240501,0x46218c240501,0x842108240501,0x46218c240501,0x42108240501,0x842108240501,0x842108240501,0x842108240501,0x42108240501,0x1012102140442,0x8000200804040100000004000108002200080ce3,0x1012102140442]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_3759 : TreeBound (n := 4) 107 (programCode 0x4e29076837) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0xf307983cc001f53079fd4c01e6f307983cc204600799e603cde600f31e9cc0010230007d4c001e703345]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_3760 : TreeBound (n := 4) 107 (programCode 0x4e29076838) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x1010902108442,0x1010902104442,0x1010902108442,0x1010902104442,0x1010902108442,0x1010902108442,0x1010902108442,0x1010902108442,0x1010902108442,0x1012902110442,0x0,0x1012902110442,0xf3088b3cc03ced9000079897e00016c87983ce157603cc79bd39800f4e6f3003cde600f379801e64db45,0x1010902120442,0xf3097e3cc079ad9000079897e00018ae798447975c03ccf33d39800f4e7e6003d39800f3f3001ea19b45,0x1010902120442,0x1010502140442,0x0,0x1010902108442,0x1010d02104442,0x1010902108442,0x1010d02104442,0x1010902108442,0x1010902108442,0x1010902108442,0x1010902108442,0x1010902108442,0x1010902110442,0x0,0x1010902110442],
[0x0,0x0,0x0,0x0,0x1010502140442,0x1010902140442,0x1010902140442,0x1010902140442,0x1010902140442,0x1010902140442,0x8002200081020020400432010088042200086504,0x0,0x121044240481,0x0,0x121044240481,0x0,0x221084240481,0x21004240481,0x221084240481,0x421004240481,0x421004240481,0x21004240481,0x421004240481,0x421004240481,0x821084240481,0x21004240481,0x821084240481,0x421004240481,0x8002200081020040400422010088042200084504,0x0,0x25f8798408de610230f3005b3e679f9f983eb530f6cc79bd399e601e9cc003db3000f6cc001e833b45,0x110902140442],
[0x0,0x110902140442,0x2521ca240501,0x842108240501,0x2521ca240501,0x842108240501,0x46218c240501,0x842108240501,0x46218c240501,0x42108240501,0x842108240501,0x842108240501,0x842108240501,0x42108240501,0x1012102140442,0x0,0x4825e603cc1e611161e62df3318007a730021b2bd398003d39bcc01e9cc003db3000f6cc001e64dcf5,0x0,0x0,0x0,0x2521ca240501,0x842108240501,0x2521ca240501,0x842108240501,0x46218c240501,0x842108240501,0x46218c240501,0x42108240501,0x842108240501,0x842108240501,0x842108240501,0x42108240501],
[0x1012102140442]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_3857 : TreeBound (n := 4) 107 (programCode 0x4e29076839) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x80006000100c0002080804020108002200080ce3,0x1010502140442,0x8000a00020140004080804020108002200080ce3,0x1010502140442,0x1010902140442,0x1010902140442,0x1010902140442,0x1010902140442,0x1010902140442,0x8002200081020020406432010088072200c86504,0x0,0x121044240481,0xf3003cfcc00f303cc3cc3cde600f300001e600003cc1e60f307983cc1e9cc003db3000f6cc001e64d995,0x121044240481,0xf3003cfcc00f303cc3cc3cde600f300001e600003cc1e60f307983cc1e9cc003db3000f6cc001e64d995,0x221084240481,0x21004240481,0x221084240481,0x421004240481,0x421004240481,0x21004240481,0x421004240481,0x421004240481,0x821084240481,0x21004240481,0x821084240481,0x421004240481,0x8002200081020040404422010088062200884504,0x8010200402040080400804020108002200082ce3,0x1012102140442,0x8020200804040100800804020108002200084ce3],
[0x1012102140442]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_3890 : TreeBound (n := 4) 107 (programCode 0x4e2907683a) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0xf3000f6cc003db30007fb6f330f300f307d4fcc0f37aec8f301e63cc07d4c34179300fad4c0079a33cf6,0x400021001000004004000000010000020042002000008000000400020000040000004000010010000040000000080000000080400000101000000404000001010000001001087ffa7,0xf3000f6cc003db30007d4c0f30f300f300003cc0f37a730f300003cc07d4c2046f300003cc0079a33cf6,0xf30007d4c003db300079808118003ea60007d4c079801e7e7f9b27cc07d4c00088b07d7d5c00f3469226,0x1012904141d02,0x1010904140d02,0x400020101000000404000000010000001000202100000800000002020000002002004200010010000040001000080000000080400000101000000404000001010000001001087ffa7,0x1010904140d02,0x1010904140d02,0x800220008102002040103202008804c200207504,0x0,0x1310c6240481,0x420021000080004004000000000400010002002000008000000020000000020000004000010000000040000000080000000080400000101000000404000001010000001001087ffa7,0x1310c6240481,0x400021001000004004000000000000010002002000008000000020000000020000004000010000000040000000080000000080400000101000000404000001010000001001087ffa7,0x221084240481,0x21000240481,0x221084240481,0x421000240481,0x421000240481,0x21000240481,0x421000240481,0x421000240481,0x821084240481,0x21000240481,0x821084240481,0x421000240481,0x8002200081020040401022020088048200205504,0x0,0x904024020020804820040a0108002200082ce3,0x1023e00808c88b0798f31e638013cc222c7983cdc0087998ae0f31e601e9cc003db3000f6cc001ea56925],
[0x1108044020020804820040a0108002200082ce3,0x102004080010000400800020088000200102ce4,0x2721ce240501,0x842108240501,0x2721ce240501,0x842108240501,0x46218c240501,0x842108240501,0x46218c240501,0x42108240501,0x842108240501,0x842108240501,0x842108240501,0x42108240501,0x1012104141902,0x400030001000040004000000010000100020003000080000000080020000200000006000010010000040000000080000000080400000101000000404000000410000001001087fda7,0x1012104141902]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_3939 : TreeBound (n := 4) 107 (programCode 0x4e2907683b) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x80006000100c0002081004040108002200080ce3,0x0,0x8002200100440020101004040100082002080ce3,0x8000200100040020001004040100002020080ce3,0x8002200100440020101004040100102004080ce3,0x0,0x8004200100840020001004040100202008080ce3,0xf3000f6cc003db30007981023000408c000408cf4eda7301e610230007987b69cc1ed98001e60f318ad6,0x8004200100840020001004040100402010080ce3,0x8000200100040020001004040100002020080ce3,0x8000200100040020001004040100802020080ce3,0x8001200080090002400804620190840420112ca4,0x0,0x80012000800900024010086402908404402134a4,0x8004200100840020001004040102002080080ce3,0xf3000f6cc003db30007981023000408c000408d6c8b7337983ccf30007b662d9079879807983cc1f7156,0x8000200100040020001004040104002100080ce3,0x0,0x8000a00020140004081004040108002200080ce3,0x0,0xf3003cfcc0002d9005b9b6601e6016c802deb3e63cc1e60f31e607981e6003ccf303cc3cc03cde7032b5,0x0,0xf3003cfcc0002d9005c14e601e6016c802e27ef33cc1e60f31e607981e6003ccf300f33cc0799e7032b5,0xf3003cfcc0000f3003cc1e600000079801e7e6003cc1e61e61e607981e61e600f30000799e601e703345,0x0,0x0,0x0,0xf3003cfcc0000f3003cc1e600000079801e7e6003cc1e61e61e607981e61e600f30000799e601e703345,0x0,0x0,0xf3003cfcc0000f3005b21e600000079802dae6003cc1e60f31e607981e60f300f33cc03cde601e7032b5],
[0x0,0x0,0x0,0x0,0x0,0x8001200040240008101004040108002200080ce3,0x0,0x1318c4240481,0x820020802100084000820020880402000100e4,0x1318c4240481,0x0,0x221084240481,0x4240481,0x221084240481,0x4240481,0x400004240481,0x4240481,0x400004240481,0x4240481,0x800004240481,0x4240481,0x800004240481,0x4240481,0x8002200080440010101004040108002200080ce3,0x8000200000040000001004040108002200080ce3,0x8004200100840020001004040108002200080ce3,0xf30007d4c001f53000798f33cc0f33cc00f33ccf3000798f33ccf30007d4c1e60f307b69cc0079a33456,0x0,0x121044240481,0x0,0x121044240481,0x0],
[0x221084240481,0x21004240481,0x221084240481,0x421004240481,0x421004240481,0x21004240481,0x421004240481,0x421004240481,0x821084240481,0x21004240481,0x821084240481,0x421004240481,0xf30007d4c001f53000799e63cc079bcc01e63ccf3000799e6f30f30007d4c1e60f307d4fcc00f3822056,0x8010200402040080401004040108002200082ce3,0x0,0x1318c4240481,0x820020820100804000820020880402000100e4,0x1318c4240481,0x0,0x221084240481,0x4240481,0x221084240481,0x4240481,0x400004240481,0x4240481,0x400004240481,0x4240481,0x800004240481,0x4240481,0x800004240481,0x4240481,0x8020200804040100801004040108002200084ce3],
[0x0,0x0,0x820020840101004000820020880402000100e4,0x0,0x0,0x221084240481,0x4240481,0x221084240481,0x4240481,0x400004240481,0x4240481,0x400004240481,0x4240481,0x842104240501,0x4240481,0x842104240501,0x4240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_4052 : TreeBound (n := 4) 107 (programCode 0x4e2907683c) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x1012904129d02,0x1dcd65f33633edb54000059682f00007ea8ed40001faa3b500000ee6ba302671b6681dcda09aca3b9ad8e6b28861c46800007736845194593052ca773594ee88f56501dcd65773597b9acbdcd653ba263a636d47360b359403b9b4135947753fa98db37b9b4135940ee6d0c845b469,0x80022000800100804010020400800000002034e4,0x80022000800100804010020400801000042034e4,0x1012904129d02,0x1012904109d02,0x1012904139d02,0x1012904109d02,0x1012904109d02,0x1012904111d02,0x0,0x1012904111d02,0x0,0x1012904121d02,0x0,0x1012904121d02,0x400021001000004004000000010000020042002000008000000400020000040000004200010010000040002000080000000080400000101000000404000001010000001001087ffa7,0x0,0x4000200110000000440000000500000001000220100000800100000a0100000200104002010010008010000010080000040080000200100000200400001000400001001001087f5a7,0x1010504384b02,0x1010104100902,0x1010504384b02,0x0,0x4000211110000000440000000100000001000221100000800000000a0000000200104222010010000040000000080000000080422000100000000400000000400020001001087fda7,0x1010104110902,0x4000200110000000440000000500000001000220100000800100000a0100000200104002010010008010000008080000020080400200100000800400000800400002001001087f5a7,0x40002001100000004400000011000000010000a00000008001000022004000020040008000401040001004100008000200008000800004002000040010000100010000100108577a7,0x1010104110902,0x4000200110000000440000000500000001000220100000800100000a0100000200104200010010800010000800080002000080020000100080000400080000400200001001087f5a7,0x1010104110902],
[0x0,0x0,0x0,0x0,0xf3000f6cc003db30007980fa98003ea60007d4c0f3001e9ce08a5f9807d4c00088b0813a2c01e64e2f36,0x1012904141d02,0x1010904140d02,0xf3000f6cc0010230007d88cf300003cc00f33cc0f3b7330f33cc079807d4c2046f300003cc0079a33c36,0x1010904140d02,0x1010904140d02,0x8002200081020020401032040088048200207504,0x0,0x121044240481,0x420021000080004004000000000400010002002000008000000020000000020000004200010000000040002000080000000080400000101000000404000001010000001001087ffa7,0x121044240481,0x0,0x221084240481,0x21004240481,0x221084240481,0x421004240481,0x421004240481,0x21004240481,0x421004240481,0x421004240481,0x821084240481,0x21004240481,0x821084240481,0x421004240481,0x8002200081020040401022040088048200205504,0x0,0x0,0x1023d4a408c7980798f31e635283cc1e607983cd023079c2720f307981e9cc003db3000f6cc001ea56925],
[0x0,0x810040800100b44008120400880002005a2da4,0x2521ca240501,0x842108240501,0x2521ca240501,0x842108240501,0x442104240501,0x842108240501,0x442104240501,0x42100240501,0x842108240501,0x842108240501,0x842108240501,0x42100240501,0x1012104141902,0x400030001000040004000000010000100020003000080000000200020000200000004000010010000040040000080000000080400000101000000404000001010000001001087ffa7,0x1012104141902]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_4133 : TreeBound (n := 4) 107 (programCode 0x4e2907683d) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x16c8000f301e616c8b64001f530007d4c1e8dae601e7e601e61e601e9cc001023000408c001e7032b5,0xf37983cc01e60f37983cc0000f307983cc1e601e601e7e601e61e601e9cc001f530007d4c001e703855,0x16c80007985b225f92fc001f530007d4c1e7e7e601e7e601e61e601e9cc0010230007d4c001e703345,0x0,0x80100800100c0402092004080108002200080ce3,0x110502140442,0x80100800201408040a2004080108002200080de3,0x110502140442,0x110902140442,0x110902140442,0x110902140442,0x110902140442,0x110902140442,0x16c8d4a5b207983cc0006a535283cc1e600000007980798f300f31e601e9cc003db3000f6cc001ea56925,0xf300f33cc03cc1e603cc3cde600f303cc1e60f31e601e67980799e601e9cc003db3000f6cc001e6c7195,0x3ccf300f33cc01e679bcc3cc0f30f301e63ccf300f30007d4c1e6007d4c1e60f300012fc0003cc38f6,0x110902140442,0x112102140442,0x8010080804060100c02004080108002200086ce3,0x112102140442,0x0,0x2184c8240481,0x210502140442,0x2184c8240481,0x210502140442,0x210888240481,0x231888240481,0x210888240481,0x210888240481,0x231088240481,0x231088240481],
[0x231088240481,0x210088240481,0x2521c8240501,0x231088240481,0x2521c8240501,0x2529c8240501,0x0,0x7384c8240481,0x210502140442,0x7384c8240481,0x210502140442,0x630888240481,0x8240481,0x630888240481,0x8240481,0x421008240481,0x8240481,0x421008240481,0x8240481,0x842108240501,0x8240481,0x842108240501,0x8240481,0x8118001e61e60faa3a0c01e6f30079bcc20bf9e601e7e601e61e601e9cc001023000408c001e7032b5,0x0,0x108448240481,0x210502140442,0x108448240481,0x210502140442,0x210888240481,0x8240481,0x210888240481],
[0x8240481,0x421008240481,0x8240481,0x421008240481,0x8240481,0x842108240501,0x8240481,0x842108240501,0x8240481,0x0,0x428448240481,0x210502140442,0x428448240481,0x210502140442,0x430888240481,0x421008240481,0x430888240481,0x421008240481,0x421008240481,0x420008240481,0x421008240481,0x420008240481,0x462188240501,0x420008240481,0x462188240501,0x420008240481,0x0,0x6384c8240481,0xf300f33cc03cc3cc07981023000408c000408d81b9fd77183cc1e6007d4c3036b1001e9cc03cc1f7156,0x6384c8240481,0xf300f33cc03cc3cc07981023000408c0007d4d81c92df098000000007d4c30389700003cc03cc1f7156,0x430888240481],
[0x8240481,0x430888240481,0x8240481,0x21008240481,0x8240481,0x21008240481,0x8240481,0x842108240501,0x8240481,0x842108240501,0x8240481,0x3d39800f30f3079ff35cc0000f300003cc1e601e601e7e601e61e601e9cc001023000408c001e7032b5,0x0,0x1dcd6500001836e25a819c2a3b50000f5de814773597b9aca0000ee6b2f736826b29010c7cfe81b73597b9aca861c5566b287736827a0eb283b9ca6d6507736826b283b9ad8e6b283b9ad8e6b283ba23d594000f047fe5000eee25d94003bb89765000eee25d94000ee6d0e4b282e9,0x420021000000004000200000000000020042002000008000000400000000040000002000010008000040010000080010000080400000101000000404000001010000001001087ffa7,0x0,0x3b9aca0ee6b639aca0ee729b5941dcd73e6b283b9ad8e6b283b9aca3c11ff940003c11ff940077536165000f047fe50000f047fe8b9aca00077712ecaee6b2f735941dce536b63b8b7102aa9936411ff940001faa3b503b9b413597b9ae9aa3b5eee2dc3ced47737750afdecdaea,0xa509c8240501,0x8240481,0xa509c8240501,0x8240481,0x421008240481,0x8240481,0x421008240481,0x8240481,0x42108240501,0x8240481,0x42108240501,0x8240481,0x0,0x848568240501,0x210502140442],
[0x848568240501,0x210502140442,0x8509c8240501,0x842108240501,0x8509c8240501,0x842108240501,0x861188240501,0x842108240501,0x861188240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x0,0x6384c8240481,0x810502140442,0x6384c8240481,0x810502140442,0x430888240481,0x8240481,0x430888240481,0x8240481,0x21008240481,0x8240481,0x21008240481,0x8240481,0x842108240501,0x8240481,0x842108240501,0x8240481,0x1e679807987983cca713cc0798f301e63cc29c41e601e7e601e61e601e9cc001023000408c001eacf2b5],
[0x0,0x0,0x810502140442,0x0,0x810502140442,0x8509c8240501,0x8240481,0x8509c8240501,0x8240481,0x421008240481,0x8240481,0x421008240481,0x8240481,0x42108240501,0x8240481,0x42108240501,0x8240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_4310 : TreeBound (n := 4) 107 (programCode 0x4e2907683e) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x1384c6240481,0x3ccf3003cfcc00f37fb822f0f300f307d4fcc798c702f1801e7e6007d4c3166710000b6403cc1f70f6,0x1384c6240481,0x422021111088000044000000000000000080022110000080000000100000000100104220010000000040000000080000200080400000101000000404000001010000001001087ffa7,0x2384c6240481,0x6384c6240481,0x2384c6240481,0x7384c6240481,0x4384c6240481,0x6384c6240481,0x4384c6240481,0x1045ae2d2c00000000007991382c00f300003cdf641679800007980f31e9cc003db3000f6cc001e64dcf5,0x7988490f1800204600079914241e0f307983cdf6921698003d3980f31e9cc003db3000f6cc001e64dcf5,0x6384c6240481,0x4000100010080002080004010108002200080ce3,0x0,0x400021801000004004000000010000020043002000008000000400020000040000004000010000000040040000080000000080400000101000000104000001010000001001087dfa7,0x0,0x1384c6240481,0x0,0x1384c6240481,0x0,0x2384c6240481,0x6384c6240481,0x2384c6240481,0x7384c6240481,0x4384c6240481,0x6384c6240481,0x4384c6240481,0x0],
[0x0,0x6384c6240481,0x4000100020100004080004010108002200080ce3,0x0,0x0,0x82002088002010100404020108002200080ce3,0xf37980f31e600f379807d4c00222c0007d4c1e6007b660002046007d4c1e60f30000b640f307a8856,0x102004088002010100404020108002200080ce3,0x1e67980f33cc01e679808118003ea60007d4c3cc001f532640426007d4c00088b098115c07983efa26,0xa105085414c2,0x2105085414c2,0x8105085410c2,0x2105085414c2,0xa105085414c2,0x802020080110004402004080088004200422de4,0x1000040008000000000004000108002200080ce3,0x10020400801100044020080800880082004235e4,0xa105085414c2,0x8105085410c2,0x8105085410c2,0x8105085410c2,0x80022000804100004020000800880402004024e4,0x80022000802100084020020800880402004024e4,0xf307a76cc001f530007987b84601ed98003cc7a823079bcc007983cc1e9cc003db3000f6cc001e64dcf5,0x80022000804100104020000800880402004024e4,0x80022000800100104020000800880402004024e4,0x8002200081020020404032080088060200806504,0x0,0x1310c6240481,0x420021000080004004000000000400010002002000008000000020000000020000004000010000000040000000080000000080400000101000000404000001010000001001087ffa7,0x1310c6240481,0x400021001000004004000000000000010002002000008000000020000000020000004000010000000040000000080000000080400000101000000404000001010000001001087ffa7],
[0x221084240481,0x21000240481,0x221084240481,0x421000240481,0x421000240481,0x21000240481,0x421000240481,0x421000240481,0x821084240481,0x21000240481,0x821084240481,0x421000240481,0x8002200081020040404022080088060200804504,0x0,0x924024820020805804040b0108001200082ca3,0x820020820100104020020800880006004024e4,0x978045c20010805c02040b8108001200082ea3,0x16c8b645b207983cc0f31e62d903cc1e607983cd6c80798f300f31e601e9cc003db3000f6cc001ea56925,0x2721ce240501,0x842108240501,0x2721ce240501,0x842108240501,0x46218c240501,0x842108240501,0x46218c240501,0x42108240501,0x842108240501,0x842108240501,0x842108240501,0x42108240501,0x80022000820100804020020800880402004024e4,0xf30b643cc0000f301e61e62d907987980f300016c8079bcc007980001e9cc003db3000f6cc001e64dcf5],
[0x80022000840101004020020800880402004024e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_4407 : TreeBound (n := 4) 107 (programCode 0x4e2907683f) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x16c8000f3079816c8b64001f530007d4c1e7e9cc01e67981e63cc01e9cc001f53000408c001e7037c5,0x0,0x3d398003cc1e7470bb80c01e6f308301cc20bf9e601e67981e63cc01e6003ccf303cc3cc03cde7032b5,0xf379800000000f37983cc0000f300003cc1e603cc01e6f301e63cc01e63cc01e6000079bcc01e703855,0xf3798003cc1e73f737b4c01e6f30811bcc20461e601e6f301e63cc01e6003ccf301e67980799e703345,0xf379800000001304301cc0000f307983cc1e601e601e6f301e63cc01e6f3000f300007a73001e703345,0x0,0x0,0x3d39803cc1e61304301cc0000f307983cc1e601e601e67981e63cc01e601e60f307983cc3cc1e7032b5,0x0,0x0,0x0,0xf379800000000f37983cc0000f300003cc1e603cc01e6f301e63cc01e61e601e67980799e601e703855,0x0,0x0,0x0,0x102002088020200400042000080040000000104,0x0,0x16c80003cc1e625f92fc001f53000408c1e8dae601e67981e63cc01e9cc001023000408c001e7032b5,0x0,0x3cc7980003cc24139a1b64001f530a794e429e464601e67981e63cc01e6003ccf303cc3cc03cde7032b5,0x0,0x3cc7980003cc24148d22fc001f530a7675429f760601e67981e63cc01e6003ccf300f33cc0799e7032b5,0x3cc79800000003cc97e3cc0000f300003cc1e601e601e6f301e63cc01e6f3000f300007a73001e703345,0x3cc7980f307985b2a713cc0798f30a713cc29c41e601e67981e63cc01e601e60f31e603cc1e61eacf2b5,0x0,0x3cc7980f307983cc97e3cc0798f301e63cc25f81e601e6f301e63cc01e601e60f30f307983cc1eacf345,0x0,0x0,0x0,0x0],
[0x0,0x3cc7980f307983cc97e3cc0798f301e63cc25f81e601e6f301e63cc01e679800fa980079f9801eacf345,0x0,0x102004088020200400042000080040000000104,0x0,0x0,0x2184c8240481,0x210500140022,0x2184c8240481,0x210500140022,0x210888240481,0x231888240481,0x210888240481,0x210888240481,0x231088240481,0x231088240481,0x231088240481,0x210088240481,0x2521c8240501,0x231088240481,0x2521c8240501,0x2529c8240501,0x402008088020200400042000088040200000104,0x8118003cc1e60fa9fd4c01e6f30079bcc20bf9e601e6f301e63cc01e9cc0010230007d4c001e703345,0x402010088020200400042000088040200000104,0x3d39803cc1e603d3b69cc0000f307983cc1e601e601e67981e63cc01e9cc001023000408c001e7032b5,0x0,0x6384c8240481,0x3cc079bcc01e63cc07980408c00408c000408c000f379805b21e60f37d4c1e60f307983cc0001e61556,0x6384c8240481,0x0,0x430888240481],
[0x8240481,0x430888240481,0x8240481,0x21008240481,0x8240481,0x21008240481,0x8240481,0x842108240501,0x8240481,0x842108240501,0x8240481,0x3d39801e60f3079fd4fcc0000f300003cc1e601e601e6f301e63cc01e9cc0010230007d4c001e703345,0x0,0x0,0x0,0x0,0x0,0xa509c8240501,0x8240481,0xa509c8240501,0x8240481,0x421008240481,0x8240481,0x421008240481,0x8240481,0x42108240501,0x8240481,0x42108240501,0x8240481,0x0,0x848568240501,0x210500140022],
[0x848568240501,0x210500140022,0x8509c8240501,0x842108240501,0x8509c8240501,0x842108240501,0x861188240501,0x842108240501,0x861188240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x0,0x6384c8240481,0x8105085410c2,0x6384c8240481,0x8105085410c2,0x430888240481,0x8240481,0x430888240481,0x8240481,0x21008240481,0x8240481,0x21008240481,0x8240481,0x842108240501,0x8240481,0x842108240501,0x8240481,0x2000088020200400042000088040200000104],
[0x0,0x0,0x8105085410c2,0x0,0x8105085410c2,0x8509c8240501,0x8240481,0x8509c8240501,0x8240481,0x421008240481,0x8240481,0x421008240481,0x8240481,0x42108240501,0x8240481,0x42108240501,0x8240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_4552 : TreeBound (n := 4) 107 (programCode 0x4e29076840) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0xf307983cc0002d9000079897e00016c80003cdf53003cfcc0079800f4e60079bcc00f3f3003cde64db45,0xf307983cc0002d9000079897e00016c80003cdf53003cfcc00798b641e9defc3dbb8b0f32d901e64db45,0x0,0x0,0xf307983cc001209000079897e00016c80003d58d3003cfcc007980799e603cc3cc0798f301e61e64db45,0x0,0x0,0xf307983cc0002d9000079897e00016c80003cdf53003cfcc0079800f4e9cc003cc00f3f3003cde64db45,0xf307983cc0002d9000079897e00016c80003cdf53003cfcc007983cc1e61e603cc3cc0f30f301e64db45,0x40002195300000000c00000003000000008002219400001001000012000000010010432a410000400008040000080004000080432800101000000100008001000400001001087d3a7,0xf307983cc0002d9000079897e00016c80003cdf53003cfcc007987981e63cc03ccf300f31e601e64db45,0x0,0x0,0x0,0x0,0xf307983cc0002d9000079897e00016c80003cdf53003cfcc007980001e9cc003db3000f300001e64db45,0x0,0x0,0x0,0x0,0x0,0xa105085414c2,0x2105085414c2,0x8105085410c2,0x2105085414c2,0xa105085414c2,0x168f08f8e70000000000000005a3c3a72a4f99c16310baa133e67058c418194400005a3c23e39c000005a3c23e39c00000b478a2035be66de11f1ce2d1e1d39527ccdffd10158961f3374acbb2539c00002d1e11f1ce00168f08f8e7000000005a3c23e39c0168f08f8e7168f0ea19888303dcf85e69fe20c0f73e11f1ce0000168f0a6231cbb2566de11f1ce000002d1e11fd15847c7651e6c2df1e39c0169071e9768e7002d23b5b40c39c0169071e9768e70168f63350ae39c00b48ed6d030e7002d23b5b40c39c002d1e135c29d1440d2cad,0x0,0x0,0xa105085414c2],
[0x8105085410c2,0x8105085410c2,0x8105085410c2,0x0,0x400020011000000014000000030000000100022010000020010000220000000200404002010000001008040000080000040080000200100000100100001001000001001001087d3a7,0x400021111000000044000000010000000100022110000080000000220000000200404222010000000040040000080000000080422000100080000400000001000400001001087ffa7,0x0,0x0,0x400020111000000014000000010000000100022110000020000000220000000200404020010000000008040000080000400080002000100001000100010001000010001001087d3a7,0x400021111000000014000000010000000100022110000020000000220000000200404222010000000008040000080000000080422000100000000100000001000080001001087d3a7,0x0,0x400020011000000014000000010000000100022010000020000000220000000200404002010000000008040000080000000080400200100000200100000001000002001001087d3a7,0x0,0x0,0x0,0x400020011000000014000000010000000100022010000020000000220000000200404000010000000008040000080000000080400000101000000100000001010000001001087d3a7,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3ccf300f33cc01e67980fa98003ea60007d4c7980020462dd494c007d4c00088b0b6622c0f307bbf36,0xa105085414c2,0x2105085414c2,0x8105085410c2,0x2105085414c2,0xa105085414c2,0x802020080110004404004100088004200826de4,0x0],
[0x10020400801100044040081000880082008275e4,0xa105085414c2,0x8105085410c2,0x8105085410c2,0x8105085410c2,0x80022000804100004040001000880402008044e4,0x80022000802100084040021000880402008044e4,0x0,0x0,0x0,0x0,0x3ccf300799e601e680267bb000222c0f303cc798d63b03002268c007d4c35345700012fc07983def26,0x210880240481,0x410882240481,0x210880240481,0x210880240481,0x410882240481,0x410882240481,0x410882240481,0x210880240481,0x8509c8240501,0x410882240481,0x8509c8240501,0x10880240481,0x80022000804100104040001000880402008044e4,0x80022000800100104040001000880402008044e4,0x8002200081020020404032100088060200806504,0x0,0x0,0x0,0x0,0x0],
[0x221084240481,0x21004240481,0x221084240481,0x421004240481,0x421004240481,0x21004240481,0x421004240481,0x421004240481,0x86118c240501,0x21004240481,0x86118c240501,0x421004240481,0x8002200081020040404022100088060200804504,0x0,0x0,0x820020840100104040021000880006008044e4,0x0,0x1e67980799e601e679807d4c00222c0007d4c3cc007a73000408c007d4c1e60f300012fc07983de6b6,0x2521c2240501,0x842108240501,0x2521c2240501,0x842108240501,0x46218c240501,0x842108240501,0x46218c240501,0x42100240501,0x842108240501,0x842108240501,0x842108240501,0x42100240501,0x80022000820100804040021000880402008044e4,0x0],
[0x0,0x0,0x0,0x0,0x2521c2240501,0x842108240501,0x2521c2240501,0x842108240501,0x46218c240501,0x842108240501,0x46218c240501,0x42100240501,0x842108240501,0x842108240501,0x842108240501,0x42100240501,0x80022000840101004040021000880402008044e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_3064 : TreeBound (n := 4) 107 (programCode 0x4e290768) := by
  conv in programCode _ => reduce
  exact branchFour (k := (1,1)) (by decide +kernel) part003_3065 part003_3242 part003_3355 part003_3484 part003_3677 part003_3710 part003_3759 part003_3760 part003_3857 part003_3890 part003_3939 part003_4052 part003_4133 part003_4310 part003_4407 part003_4552

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_4697 : TreeBound (n := 4) 107 (programCode 0x4e290769) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 4)
    (a := List.flatten [
[0x8004200108040200008004200108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_4698 : TreeBound (n := 4) 107 (programCode 0x4e29076a) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 4)
    (a := List.flatten [
[0x0,0x8008200108020000408048200108040200000104,0x8008200100120002408048e00108040a00010104,0x8008200108020000408048200108040200000104,0x0,0xf30079bcc007a73001e6010230003db30007d4cf344d3a2c000000001e9cc1e688b00003cc0003cc3c56,0x0,0x1020501284222,0x1020501284222,0x1020501280222,0x1020501284222,0xf3001e9cc01e6f3001e6007d4c00222c0007d4c000f4e600f745800f4e688ce64bf1f716798003ee5fb6,0x1020501388702,0x1020501284222,0x1020501388702,0x1020501294ae2,0x1020501290ae2,0x0,0x1020501290ae2,0xf3001e9cc01e6f3001e6007d4c00222c0007d4c000f4e600f6cc000f4e6799e60f300f30798003ee5fb6,0xf3001e9cc01e6f3001e6007d4c00222c0007d4c000f4e600f6cc000f4e6799e607980f30798003ee5fb6,0xf3001e9cc01e6f3001e6007d4c00222c0007d4c000f4e600f303cc0f4e60097e0f30000f307983cc33b6,0xf3001e9cc01e6f3001e6007d4c00222c0007d4c000f4e600fa98000f4e6f31e603cc1e60f300043a4fb6,0x0,0x1020501284222,0x1020501284222,0x1020500280222,0x1020501284222,0xf307983cc02055307ba2c07b660025f80005b99800f6cc003ea6001e7e603cc0f31e603cc1e61e703465,0x1020502388702,0x1020501284222,0x1020502388702],
[0x1020505294ae2,0x1020505290ae2,0xf307983cc02055307ba2c07b660025f80005b99800f6cc003ea6001e7e60f300f33cc03cde601e703465,0x1020505290ae2,0x0,0x0,0x0,0x0,0x0,0x1020501284222,0x1020501284222,0x1020501280222,0x1020501284222,0x80042001001100044001000041000000800201e4,0x1020501388702,0x1020501284222,0x1020501388702,0x1020501294ae2,0x1020501290ae2,0x80042001001100044001000041000002000201e4,0x1020501290ae2,0x0,0xf3001e9cc01e6f3001e6007d4c00222c0007d4c001e7e60088b0001e7e6799e607983cc079800467dfb6,0x0,0xf3001e9cc01e6f3001e6007d4c00222c0007d4c001e7e6008118001e7e6f31e603cc1e60f300043a4fb6,0x0,0x44d18007a73000f303d3b69db4e607983cc0001e679803ccf300799e9cc003db3000f6cc001e68a925,0x1023811c08c0f30798003d3b660f4e600003cc0001e679803ccf300799e9cc003db3000f6cc001e68a925,0x0,0xf4ee11bd398f300f3003d3b846f4e63cc03cc0001e679803ccf300799e9cc003db3000f6cc001e68a925,0x1ee6ca03ccf30079803d3b9b374e61e603cc0001e679803ccf300799e9cc003db3000f6cc001e6c7525,0x109d01180f30f30000003d3b660f4e600003cc0001e679803ccf300799e9cc003db3000f6cc001e68a925],
[0x1ee1180798f300f3003d3b846f4e63cc03cc0001e679803ccf300799e9cc003db3000f6cc001e68a925,0xf5e16cdd57ef300f3003d3b9b374e63cc03cc0001e679803ccf300799e9cc003db3000f6cc001e68a925,0xf381181e60f303cc003d3b660f4e600003cc0001e679803ccf300799e9cc003db3000f6cc001e68a925,0x102381181e60f30000003d3b660f4e600003cc0001e679803ccf300799e9cc003db3000f6cc001e68a925,0xf381183cc0f30798003d3b660f4e600003cc0001e679803ccf300799e9cc003db3000f6cc001e68a925,0xf4ee4e403ccf30000003d3b939f4e600003cc0001e679803ccf300799e9cc003db3000f6cc001e68a925,0x79884e4f300f31e60003d3b939f4e600003cc0001e679803ccf300799e9cc003db3000f6cc001e68a925,0xf3081180000f30000003d3b660f4e600003cc0001e679803ccf300799e9cc003db3000f6cc001e68a925,0x7988119e600f33cc0003d3b846f4e63cc03cc0001e679803ccf300799e9cc003db3000f6cc001e68a925,0xf4ee11bd398f30000003d3b846f4e600003cc0001e679803ccf300799e9cc003db3000f6cc001e68a925,0x8004200100110004400201008108001200062be4,0x0,0x1020501284222,0x1020501284222,0x1020501280222,0x1020501284222,0x80042001000900044000000041200000800201a4,0x1020503388702,0x1020501284222,0x1020503388702,0x1020505294ae2,0x1020505290ae2,0x80042001000900044000000041200002000201a4,0x1020505290ae2,0x0,0xf30079bcc01e6f3001e601023000408c0007d4d6cc89f8460f30001e7e7e62d981183cc079800454ecb6,0x0,0xf30079bcc01e6f3001e601023000408c0007d4d6cc89f8460f30001e7e7e62d981183cc0f3000454ecb6,0x80042001001100044004020101080022000a05e4,0xf30079bcc01e6f3001e601023000408c0007d4d0274d36607983cfcc1e9cc1e688b00012fc0003cc3cb6,0xf3001e9cc01e6f3001e6007d4c00222c0007d4c03cc1e63cc003cfcc1e9cc1e60f300012fc0003cc33b6,0x0],
[0xf33d39bcc007980001e6010230003db30007d4cf344d3a2c000000001e9cc1e688b00003cc0003cc3c56,0x0,0x0,0x0,0x19e379980f31e61e601e601023000408c0007d4d9e4411f5c03cc1e601e9cc33c7d700f33cc0003ee68b6,0x1e679801e67980799e6010230003db30007d4cf4ee22d2c000f30799e9cc1ea54b000408c00131ee1d6,0x0,0x0,0x1026d398007b6603cc1e601023000408c0007d4d0274d3a2c0003cfcc1e9cc1e688b00012fc0003cc3cb6,0xf307983cc1e603cc1e601023000408c0007d4d023813a2c0003cfcc1e9cc1e688b00012fc0003cc3cb6,0xf379803cc000079f983cc000102300003cde600f301e63cc0f307981e9cc003db3000f6cc001e68a5c5,0x0,0xaadc7980f30799e601e6010230003db30007d4d9de8f1f5c03cc1e601e9cc33c7d700f33cc03cfee6856,0x79807987980799e601e6010230003db30007d4d6c8bdfa2c03cc1e601e9cc2d988b00f33cc03cfee6856,0x0,0x7980799e60079bcc01e6010230003db30007d4d6c8bdfa2c0f303cc01e9cc2d988b03cc3cc0f3454ec56,0xf3001e9cc01e6f3001e6007d4c00222c0007d4c07981e61e6003d3981e9cc1e60f300012fc0003cc33b6,0x0,0x44d18007a73000f305b21e9e2c8007a7300007980798f300f31e601e9cc003db3000f6cc001e68a925,0x1023798408c0000798005b21e616c80000f300007980798f300f31e601e9cc003db3000f6cc001e68a925,0x0,0x16c87985b200003cc0005b21e616c80000f300007980798f300f31e601e9cc003db3000f6cc001e68a925,0x1ee6ca03cc000079805b221b3ec801e6f300007980798f300f31e601e9cc003db3000f6cc001e6c7525,0xf3079800000000000005b21e616c80000f300007980798f300f31e601e9cc003db3000f6cc001e68a925,0x1ee1180798f300f3005b220476c803ccf300007980798f300f31e601e9cc003db3000f6cc001e68a925,0x4040101001100044004020801080022000a05e4,0x8040201001100044020040801080042000229e4,0x8040201001100044020040801080042000229e4,0xf379803cc0000798005b21e616c80000f300007980798f300f31e601e9cc003db3000f6cc001e68a925,0x10040401001100044020080801080082000239e4,0x7987980f300001e60005b21e616c80000f300007980798f300f31e601e9cc003db3000f6cc001e68a925,0xf3079800000000000005b21e616c80000f300007980798f300f31e601e9cc003db3000f6cc001e68a925],
[0x7987981e600003cc0005b21e616c80000f300007980798f300f31e601e9cc003db3000f6cc001e68a925,0xf3079800000000000005b21e616c80000f300007980798f300f31e601e9cc003db3000f6cc001e68a925,0x0,0x80040001001100044020000801080002000201e4,0x1023798408c0000798003cc1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0,0xf307983cc00000000003cc1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925,0x8040a01001100044020140801080142005229e4,0x204008100110004402001080108001200422be4,0x1ee1180798f300f300408e04702303cc1e600102307981e60f300001e9cc003db3000f6cc001e68a925,0x404010100110004402002080108002200422de4,0x8040201001100044020040801080042000229e4,0x8040201001100044020040801080042000229e4,0x80040001001100044020000801080002000201e4,0x10040401001100044020080801080082000239e4,0x28040801001100044020100801080102004229e4,0x20040801001100044020100801080102004229e4,0x7987981e600003cc0003cc1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925,0x40041001001100044020200801080202008269e4,0x0,0xf307983cc001f53081927301e60016c80f35d061e601e6f301e63cc01e6003ccf303cc79803cde703345,0xf307983cc0000f307980f300003cc7980f31e603cc01e6f301e63cc01e63cc01e6000079bcc01e703855,0xf307983cc001f53081927301e60025f80f399c61e601e6f301e63cc01e6003ccf301e67980799e703345,0x0,0xf307983cc0000f307980f300003cc7980f31e603cc01e6f301e63cc01e601e61e61e607981e61e703855,0xf30079bcc007a73001e6010230003db30007d4cf344e2d2c000f301e7e607b6a4587983cc1e603eee1d6,0xf307983cc0000f307980f300003cc7980f31e601e601e6f301e63cc01e601e60f30f307983cc1e703345,0x0,0xf307983cc0000f307980f300003cc7980f31e601e601e6f301e63cc01e60f300f3f300798f301e703345,0xf30079bcc007a73001e6010230003db30007d4cf344d3a2c0079801e7e63ce04d9bcc1e60f3003ee6856,0xf307983cc0000f307980f300000007980f31e601e601e6f301e63cc01e60f300f37980799e601e703345,0xf30079bcc01e6f3001e601023000408c0007d4cf344d3a2c01e6001e7e63ce04da7307981e600454ecb6],
[0x0,0xf30079bcc01e6f3001e601023000408c0007d4cf3489fa2c0f30001e7e7e62d981183cc079800454ecb6,0x0,0xf30079bcc01e6f3001e601023000408c0007d4cf3489fa2c0f30001e7e7e62d981183cc0f3000454ecb6,0x0,0x0,0x0,0x0,0xf307983cc00000000003cc1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925,0x8040801001100044040041001080042000229e4,0x204008100110004404001100108001200826be4,0x40041001100044040001001080002000201e4,0x404010100110004404002100108002200826de4,0x40201001100044040001001080002000201e4,0x8040201001100044040041001080042000229e4,0x0,0x10040401001100044040081001080082000239e4,0x28040801001100044040141001080142004229e4,0x20040801001100044040101001080102004229e4,0x0,0x40041001001100044040201001080202008269e4,0x800820010e02008040804c200108070200402904,0x8004200100210008408004200108040200042ae4,0x8008200108020000408048200108040200000104,0x80042001004100104080002001080402000804e4,0x800820010782002040803c20010807c200102904,0x8008200101020020408038200108048200102904,0x0,0x1310d0240481,0x108002108120002408048e00108040a00010104,0x1310d0240481,0x0],
[0x3d39800f379801e7e9cd0230f300f30007d4cf344d3a2c000000001e9cc1e688b00003cc0003cc3c56,0x0,0x0,0x0,0xf4ee11bd398f300f30003ce0460f303cc1e600001e679803ccf300799e9cc003db3000f6cc001e68a925,0xf307983cc000000000003cde600f300001e6000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0,0x0,0x1023798408c00007980003cde600f300001e60000f307981e60f303cc1e9cc003db3000f6cc001e68a925,0xf307983cc000000000003cde600f300001e6000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0,0x0,0x16c87985b200003cc00003cde600f300001e60007980798f300f31e601e9cc003db3000f6cc001e68a925,0xf307983cc000000000003cde600f300001e6000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0,0xf307983cc000000000003cde600f300001e6000f3007980000f300001e9cc003db3000f6cc001e68a925,0x221090240481,0x40800810842000840804c200108043200042b04,0x221090240481,0x10237983cc000007980003cde600f300001e6000f30079bcc007a73001e9cc003db3000f6cc001e64dcf5,0x401010240481,0x1010240481,0x401010240481,0x401010240481,0x801010240481,0x1010240481,0x801010240481,0x1010240481,0x8008200101020040408028200108048200205104,0x800820010c02008040804c200108070200402904,0x80042001020100804080042001080402004028e4,0x8008200108020000408048200108040200000104],
[0x80042001040101004080042001080402008068e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_4924 : TreeBound (n := 4) 107 (programCode 0x4e29076b71) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x124050240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_4925 : TreeBound (n := 4) 107 (programCode 0x4e29076b72) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x624090204481,0x424010210481,0x624090204481,0x0,0x624081204481,0x8020208000200000004020100002000080ce3,0x624081204481,0x424000200481,0x424002208481,0x424000200481,0x424002208481,0x0,0x4459e611160000f30b640f30f303cc3cc03ccf3445a22c1e60000f307991167983cc0f307983cc3cb6,0x0,0x4459e611160000f30b640f30f303cc3cc03ccf3445a22c1e60000f307991167983cc0f307983cc3cb6,0x0,0x1200000004800200012000000010000c000080010000200040000800100000800400120001000480020000a00000002000080010001000048002000200010000200010002eaba8,0x424000200481,0x7983cc1e603cc3cfcc0000f300003cc000079801e7e60079bcc01e600003cc0000f4e6001e64d995,0x0,0x424010208481,0x140802018020200408040a00010442008040304,0x424010208481,0x0,0x4469160f300000f30b6c9a300003cc00003ccf307a952c0000f3000079fb69cc0fa98003cc1e6110c6,0x3cd1160f31e600f30799023000408c000408cf307a952c001f53000079fb69cc1ed98003cc1e611156,0x0,0x0,0x4459e605b20000f30b6ba730f300f3003cfccf3079a22c0000f3000079fb69cc1ed98003cc1e6110f6,0xc00020102100084080006000104400100804e4,0x4459e605b20000f30b6ba730f300f3003cfccf3079a22c0000f3000079fb69cc1ed98003cc1e6110f6],
[0xc00020104100104080002000104400100804e4,0xf30799117e600f30798408c00f6cc000408cf30000b64001f53000079bea6000fa98003cc1e610856,0x840020108100204080102000104400100924e4,0x4469160f31e600f30b6c9a3000f6cc000408cf307b0eac001f53000079fb69cc1ed98003cc1e611156,0x880020110100404080102000104400100924e4,0x4459e611160000f30b6ba73000f6cc003cfccf3079a22c0000f3000079fb69cc1ed98003cc1e611156,0x804020120100804080006000104400100804e4,0x4459e611160000f30b6ba73000f6cc003cfccf3079a22c0000f3000079fb69cc1ed98003cc1e611156,0x804020140101004080006000104400100804e4,0x424010210481,0x140802018020200408040a00011048020102904,0x424010210481,0xf307991160000f30b6403ccf303cc3cc03ccf30000b641e60f300007b67e60079f9801e60f3812d56,0x424010220481,0x424010200481,0x424010220481,0x0,0x4825e60f300000f30d4b02300003cc00003ccf30b6622c0000f3000097e2d97d4c7980f307983cddc6,0x421010210481,0x0,0xf30798fa98000f307987d4c00222c0007d4cf30000b641e60f3000088b1e603cc7980f307983cd556,0x420810208481,0x0,0x420810208481,0x0,0x421010210481,0x420010200481,0x421010210481,0x420010200481,0x422010220481,0x420010200481,0x422010220481],
[0x420010200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_4990 : TreeBound (n := 4) 107 (programCode 0x4e29076b73) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x124050240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_4991 : TreeBound (n := 4) 107 (programCode 0x4e29076b74) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0xf30f4e6003ea6f30f6cfcc001f53079fd4c1e7f53001e9cc01e6f3001e6003ccf303ccf3003cde7033d5,0x0,0x40004100100000400000040801000001000000600400001001000012000000018010400000201000000804000008010000008041080010105000040400800080050000100108732a7,0x1004040200900024080006000200c00020100e4,0x0,0x0,0x0,0x140004020210008408000a000200c00020100e4,0x4459e60f301e61e612fd0230f300f3000408cf3079a22c0002d90000f3111679816c80003cc1e61df6,0x1400040204100104080002000200c00020100e4,0x0,0x0,0x0,0x0,0x0,0x100804022010080408000a000200c00020100e4,0x1004040200900024080006000200c00020100e4,0x100804024010100408000a000200c00020100e4,0xf31e9cc00f4e6f3003cfcc001f5307a76cc1e9db3001e9cc01e6f3001e600799e603ccf300799e7038e5,0x0,0x124041204481,0x8000208000200000004020100002000080ce3,0x124041204481,0x24000200481,0x224082208481,0x24000200481,0x224082208481,0x0,0x0,0x0,0x0],
[0x0,0x824088220481,0x24000200481,0x824088220481,0x8000208000200000004200100002000080ce3,0x0,0x124041208481,0x424004208481,0x124041208481,0x24000208481,0x224082208481,0x24000208481,0x224082208481,0x0,0x424004208481,0x0,0x424004208481,0x0,0x824088208481,0x24000208481,0x824088208481,0x0,0x0,0x124041208481,0x424004200481,0x124041208481,0x24000200481,0x0,0x24000200481,0x0,0x0,0x424004200481],
[0x0,0x424004200481,0x0,0x0,0x24000200481,0x0,0x1e60f3097e0001e612fc03ccf303cc3cc03cc3cc0010231e603cc000f32046001e600f31e63cc219b6,0x0,0x124041208481,0x424004208481,0x124041208481,0x24000208481,0x224082208481,0x24000208481,0x224082208481,0x0,0x424004208481,0x0,0x424004208481,0x0,0x824088208481,0x24000208481,0x824088208481,0x8000208000200000004200100402010080ce3,0x0,0x44691607980001e613049a300003cc00003ccf307a952c0000f30000f37b69cc0fa98003cc1e6110c6,0x0,0x0,0x0,0x0,0x0,0x0],
[0x1400040204100104080002000204400100804e4,0x0,0x0,0x42000100100000400010000801000001000200200000800000001002000002008000400000201000000804000008010000008040000010108000040400000080020000100108732a7,0x0,0x0,0x0,0x4459e6097e0001e61303a73000f6cc003cfccf3079a22c0000f30000f37b69cc0fa98003cc1e6110c6,0x0,0x0,0xf30f4e6003ea6f30f6cc003cde60445f9805b3f53001e9cc01e6f3001e60f300f3f300f30f301e7033d5,0x1008040200900024080002000200400040000e4,0x4459e607980001e612fd02300003cc00003ccf3079a22c0000f300012fd11679807980007980001dc6,0x0,0x0,0x0,0xf3799e603cde6f3f33cc01e7e601ee11803ecc073001e9cc01e6f3001e60f300f3f300f30f301e7033d5,0x1400040204100104080002000200400040000e4,0x0,0x0,0x0,0x0,0x0,0x0,0x1000040200100004080002000200400040000e4,0x0,0x0,0x0,0x1e60f3097e0001e612fc03ccf303cc3cc03cc000f30f311160000f30f3f4e600f301e60f31e6318fb6,0x0,0x1e60f3097e0001e612fc03ccf303cc3cc03cc001e60f3097e0001e60f3f4e600f307980f31e62dc3b6,0x0],
[0x1e60f3097e0001e612fc03ccf303cc3cc03cc007980f37b660007980f3f4e600f3003ccf31e62e3d36,0x0,0x0,0x420001001080004000000008000400010040002000100000000400000001000000000200010000800040001000080001000080400000101000000404000000800000001001087fea7,0x0,0x420001001080004000000008000400010040002000100000000400000001000000000200010000800040001000080002000080400000101000000404000000800000001001087fea7,0x0,0x0,0x1e60f3097e0001e612fc03ccf303cc3cc03cc1e60011161e601e6000f3f4e600f3000f3f31e62dc3b6,0x0,0x1e60f3097e0001e612fc03ccf303cc3cc03cc3cc0010231e603cc000f3f4e600f3000f3f31e62dc3b6,0x0,0xf30f6cc00f4e6f3003cc003cde60445f9805b3f53001e9cc01e6f3001e61e601e6f300f31e601e7038e5,0x0,0xf31e9cc00f4e6f3003cc00799e604467300981db3001e9cc01e6f3001e61e601e6f300f31e601e7038e5,0xf3001e60001e6f3003cfcc00000007983cc1e60f3001e9cc01e6f3001e60f300f3f300f31e601e7033d5,0x0,0x0,0x4459e60f300001e612fd0230f300f300003ccf3079a22c0000f300012fd11679807980007980001df6,0x0,0xf6cc1e63cc1e6f6cc3cc0f30000f379800f4e60f3001e9cc01e6f3001e60f300f3f300f31e601e7033d5,0x0,0xf6cc1e63cc1e6fa983cc0f30000f379801e7e60f3001e9cc01e6f3001e60f300f3f300f31e601e7033d5,0x0,0x0,0x0,0x1000040200100004080002000200400040000e4,0x0,0x0,0x4a817c80003f54787cd66dcd65ee6b292a05f200003b9acc540be47735b1cd653b9ad173594ee6b45cd651dcd6c735941dcd68b9ad8e6b3251467fc0c7cd6500000ef5993639aca3b9aca0001dd11eaca00003b9bbac099a289a09aca00ee6b280ee6ee1acbdcda18b390b0aa,0x1e60f3097e0001e612fc03ccf303cc3cc03cc000f30f311160000f30f4e7e6007983cc1e60f3814bb6,0x0],
[0x1e60f3097e0001e612fc03ccf303cc3cc03cc001e60f3097e0001e60f4e7e6007983cc1e60f3814bb6,0x0,0x1e60f3097e0001e612fc03ccf303cc3cc03cc007980f37b660007980f4e7e60079803cde60f381c536,0x0,0x0,0x420001001080004000000008000400010040002000100000000400000001000000000200010000800040001000080001000080400000101000000404000000800000001001087fea7,0x0,0x420001001080004000000008000400010040002000100000000400000001000000000200010000800040001000080002000080400000101000000404000000800000001001087fea7,0x0,0x0,0x1e60f3097e0001e612fc03ccf303cc3cc03cc1e60011161e601e6000f4e7e60079800f4e60f3814bb6,0x0,0x1e60f3097e0001e612fc03ccf303cc3cc03cc3cc0010231e603cc000f4e7e60079800f4e60f3814bb6,0x0,0x124041220481,0x424004220481,0x124041220481,0x24000220481,0x224082220481,0x24000220481,0x224082220481,0x0,0x424004220481,0x0,0x424004220481,0x0,0x824088220481,0x24000220481,0x824088220481,0x8000208000200000004200102002080080ce3,0x0,0x124041208481],
[0x424004200481,0x124041208481,0x24000200481,0x0,0x24000200481,0x0,0x0,0x424004200481,0x0,0x424004200481,0x0,0x0,0x24000200481,0x0,0x8000208000200000004200100002000080ce3,0xf3001e60001e6f3003cfcc0000f307983cc1e60f3001e9cc01e6f3001e679800fa9800f3f3001e7033d5,0x0,0xf3003cc0131a6f3003cc003cde6044580005b20f3001e9cc01e6f3001e6012fdf53000f300f31e7038e5,0x222c00109cf981e60f308118002046000408cf30d4d15c35345700010231e60798d4ce830f30799766,0x4825e608118001e614e3023000222c0007d4cf30b6622c1e60f300011162d97d4c7980f307983cddc6,0x408c0010237981e60f30fa98003ea60007d4cf307983cc2d988b00011161e60798b65f530f30799c76,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0],
[0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_5216 : TreeBound (n := 4) 107 (programCode 0x4e29076b75) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x224090240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_5217 : TreeBound (n := 4) 107 (programCode 0x4e29076b76) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x624081240481,0x442008048020200400142002048040a00010104,0x624081240481,0x0,0x624081204481,0x0,0x624081204481,0x24000200481,0x24000208481,0x24000200481,0x24000208481,0x0,0x0,0x7983cc7b66000798408c03ccf303cc3cc03cc001e63cc097e0001e63ccf4e600f307980f3003fa3d36,0x0,0x7983cc7b66000798408c03ccf303cc3cc03cc001e63cc097e0001e63cde7e6007983cc1e60044dc536,0x24000220481,0x24000200481,0x24000220481,0x0,0x424002240481,0x24000240481,0x424002240481,0x0,0x1eda73079800007984093a730f303cc00003cc01eda7307980000f30408c1e9db3000f6cc001e611156,0x8000208000020000804020108002200080ce3,0x0,0x8000208000000000004000108002200080ce3,0x420802240481,0x20000240481,0x420802240481],
[0x20000240481,0x21004240481,0x20000240481,0x21004240481,0x20000240481,0x42200c240481,0x20000240481,0x42200c240481,0x20000240481,0x24004240481,0x442008048020200401042020048048200102b04,0x24004240481,0x7983cc7b66000798408c03ccf303cc3cc03cc079803cde7e6007980408c1e60f307983cc00f381a6d6,0x424008240481,0x24000240481,0x424008240481,0x0,0x620481240481,0x0,0x620481240481,0x0,0x420802240481,0x20000240481,0x420802240481,0x20000240481,0x21004240481,0x20000240481,0x21004240481,0x20000240481,0x422008240481,0x20000240481,0x422008240481],
[0x20000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_5282 : TreeBound (n := 4) 107 (programCode 0x4e29076b77) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x224090240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_5283 : TreeBound (n := 4) 107 (programCode 0x4e29076b78) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0xf30f4e6003ea6f30f6cfcc001f53079fd4c1e7e600f4e600f4e6000f4e6003ccf303ccf3003cde7033d5,0xf6cc3cc3cc1e6f3003cfcc0000f307983cc1e60000f4e600f4e6000f4e9db301f53000f33cc01e7038e5,0x1eda7303ea6000f307d4c0f30f303cc3cc03ccf307a73001e60000007d4c1e600000000000000001dc6,0xf34c2cc00f4e6f3003cfcc001f53079fd4c1e7e600f4e600f4e6000f4e6012fde604bff300f31e7038e5,0x0,0x0,0xf3799e603cde6f3f33cfcc01e6f30811bcc20bf800f4e600f4e6000f4e601e60f31e60f303cc1e7033d5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x111601e6f301e72fc03cfcc01e6f30811bcc2139000f4e600f4e6000f4e679800fa9800f3f3001e7033d5,0x0,0x0,0x40004100100010400000040800000101000000600400001001000010004000018010400000201010000804000008000500008040000010100000040400000081000000100108732a7,0x0,0x0,0x0,0x1eda9167980000f307d54d6f000102300003cc0044698f83cc0000f37d4c1e688b07983cc0001e61df6,0x4004100802100084000820020880402000100e4,0x2020100002000100020200000020001040021000000000800400008000000408000002201100001001000010000000010010400020011000000004000200010000000200017d3a8,0x4004100804100104000800020880402000100e4,0x4004100800100104000800020880402000100e4,0x4040100808100204000900020880402000924e4,0x1eda91679801e6f307d549a30001023003cfcc0044698f83cc0000f37d4c1e688b07983cc0001e61df6,0x4080100810100404000900020880402000924e4,0x4000100800100004000800020880402000100e4],
[0x4020100820100804000820020880402000100e4,0x2020100008000400008200000020001040021000100004000000108000000408000002201100008004000010000000010010400020011000000004000200010000000200017fda8,0x4020100840101004000820020880402000100e4,0x0,0xf30f6cc00f4e6f3003cfcc001f53079fd4c1e7e601e7e600f4e6001e7e6003cde603ccf3003cde7038e5,0xf307983ea6000f307d4c03ccf303cc3cc03ccf30f379805b20f30f379805b200044587983cc1e61556,0xf31e9cc00f4e6f3003cfcc001f5307a76cc1e9cc01e7e600f4e6001e7e600799e603ccf300799e7038e5,0x1eda7303ea6000f307d4c0f30f303cc3cc03ccf362c730097e0001e67981116b641e60f307983cc3c26,0x0,0x1eda7307b66000f307d4c0f30f303cc3cc03ccf307a73001e60000007987b66001e600001e600001e56,0x1eda7303ea6000f307d4c0f30f303cc3cc03ccf307a73001e60000007d4c1e600000000000000001dc6,0xf3001e60001e6f3003cfcc0000f307983cc1e60000f4e600f4e6001e7e9cc000f30000f6cc001e7033d5,0xf6cc1e63cc1e6f6cc3cfcc0000f307983cc1e60000f4e600f4e6001e7e60f300f3f300f30f301e7033d5,0x0,0xf6cc1e63cc1e6fa983cfcc0000f307983cc1e60000f4e600f4e6001e7e60f300f3f300f31e601e7033d5,0x0,0x0,0x0,0x1eda7303ea6000f307d4c0f30f303cc3cc03ccf307a73001e60000007d4c1e600000000000000001dc6,0x0,0x0,0xf30f4e6003ea6f30f6cfcc001f53079fd4c1e7e600f4e6003ea6000f4e6003ccf303ccf3003cde7033d5,0x0,0x1eda7303ea6000f307d4c0f30f303cc3cc03cc00446730097e0001e67d4c1e679800000000003cc3c26,0xf3001e60001e6f3003cfcc0000f307983cc1e6000001e60001e600001e600000f30000f300001e7033d5,0xf3001e60001e6f3003cfcc0000f307983cc1e6000001e60001e600001e601e60f31e60f301e61e7033d5,0x0,0xf3001e60001e6f3003cfcc0000f307983cc1e6000001e60001e600001e601e60f31e60f303cc1e7033d5,0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x1ed98007b69cc0f307d4c0798f301e63cc03cc004458001119cc01e67980f3088b4459e60f307985936,0x0,0x0,0x3204c2240481,0x208020208004020100204008108002200080ce3,0x3204c2240481,0x208008208004008100204008108002200080ce3,0x220882240481,0x621082240481,0x220882240481,0x220882240481,0x621082240481,0x621082240481,0x621082240481,0x220082240481,0xa22082240481,0x621082240481,0xa22082240481,0x220882240481,0x0,0x7204c6240481,0x8020208000020000004000108002200080ce3,0x7204c6240481,0x8000208000000000004000108002200080ce3,0x220884240481,0x20000240481,0x220884240481,0x20000240481,0x421000240481],
[0x20000240481,0x421000240481,0x20000240481,0x822084240481,0x20000240481,0x822084240481,0x20000240481,0x1eda7303ea6000f307d4c0f30f303cc3cc03ccf307a73001e60000007d4c1e60f300003cc0000001dc6,0x0,0x0,0x808020208000020000804020108002200080ce3,0x0,0x8000208000000000004000108002200080ce3,0x220882240481,0x20000240481,0x220882240481,0x20000240481,0x421004240481,0x20000240481,0x421004240481,0x20000240481,0x822088240481,0x20000240481,0x822088240481,0x20000240481,0x0,0x120444240481,0x808020208000020000804020108002200080ce3,0x120444240481,0x808020208000020000804020108002200080ce3,0x220884240481,0x20004240481],
[0x220884240481,0x20004240481,0x421004240481,0x20004240481,0x421004240481,0x20004240481,0x822084240481,0x20004240481,0x822084240481,0x20004240481,0x0,0x7204c6240481,0x420001001080004000000008000400010042002000108000000400000000040000004000010010000040000000080000000080400000101000000404000000810000001001087fea7,0x7204c6240481,0xf307983ea6000f3079807d4c00222c0007d4c03cc079bcc003cfcc07d4c1e60f300012fc01e62eb6b6,0x220884240481,0x20000240481,0x220884240481,0x20000240481,0x421000240481,0x20000240481,0x421000240481,0x20000240481,0x822084240481,0x20000240481,0x822084240481,0x20000240481,0x0,0x120444240481,0x0,0x120444240481,0x0],
[0x220884240481,0x20004240481,0x220884240481,0x20004240481,0x421004240481,0x20004240481,0x421004240481,0x20004240481,0x822084240481,0x20004240481,0x822084240481,0x20004240481,0x0,0x0,0x420001001080004000000008000400010042002000108000000400000000040000004200010010000040042000080000000080400000101000000404000000810000001001087fea7,0x0,0xf307983ea6000f3079807d4c00222c0007d4c07980799e6003d39807d4c1e60f300012fc00f3823eb6,0x220882240481,0x20000240481,0x220882240481,0x20000240481,0x421004240481,0x20000240481,0x421004240481,0x20000240481,0x822088240481,0x20000240481,0x822088240481,0x20000240481,0x0,0x120448240481,0x808020208000020002004080108002200080ce3],
[0x120448240481,0x2008080208008080202004080108002200081ce3,0x220888240481,0x421008240481,0x220888240481,0x20008240481,0x421008240481,0x20008240481,0x421008240481,0x20008240481,0x822088240481,0x20008240481,0x822088240481,0x20008240481,0x0,0x7204c6240481,0x8020208000020000004000108002200080ce3,0x7204c6240481,0x8000208000000000004000108002200080ce3,0x220884240481,0x20000240481,0x220884240481,0x20000240481,0x421000240481,0x20000240481,0x421000240481,0x20000240481,0x822084240481,0x20000240481,0x822084240481,0x20000240481,0xf3001e60001e6f3003cfcc0000f307983cc1e601e601e7e601e63cc01e9cc001023000f6cc001e7033d5],
[0x0,0x0,0x0,0x0,0x0,0x220882240481,0x20000240481,0x220882240481,0x20000240481,0x421004240481,0x20000240481,0x421004240481,0x20000240481,0x822088240481,0x20000240481,0x822088240481,0x20000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_5524 : TreeBound (n := 4) 107 (programCode 0x4e29076b79) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x424010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_5525 : TreeBound (n := 4) 107 (programCode 0x4e29076b7a) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x620490240481,0x1048020100120002408048e00108040a00010104,0x620490240481,0x0,0xf381180f4e6003cc1e6010230003db30007d4cf344d3a2c000000001e9cc1e688b00003cc0003cc3c56,0x0,0x0,0x0,0xf381180f4e6003cc1e6010230003db30007d4d9e3f52b9f30799e601e9cc20cbd7001e9cc0003ee6856,0x840020100110004400201008108001200062be4,0x0,0x8400201001100044004020101080022000a05e4,0xf381183cde6003cc1e601023000408c0007d4d0274d36607983cfcc1e9cc1e688b00012fc0003cc3cb6,0x3cc1e63cde6003cc1e6007d4c00222c0007d4c03cc1e63cc003cfcc1e9cc1e60f300012fc0003cc33b6,0xf381183cde6003cc1e601023000408c0007d4d023813a2c0003cfcc1e9cc1e688b00012fc0003cc3cb6,0x3cc1e63cde6003cc1e6007d4c00222c0007d4c07981e61e6003d3981e9cc1e60f300012fc0003cc33b6,0xf381183cde6003cc1e601023000408c0007d4d6c8832c0980799e601e9cc20cbd7001e9cc0003ee68b6,0x8400201001100044020040801080042000229e4,0x0,0x8400201001100044040041001080042000229e4,0x420810240481,0x840020100210008408004200108040200042ae4,0x420810240481,0x8400201004100104080002001080402000804e4,0x21010240481,0x20010240481,0x21010240481,0x20010240481,0x422010240481,0x20010240481,0x422010240481],
[0x20010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_5558 : TreeBound (n := 4) 107 (programCode 0x4e29076b7b) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x424010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_5559 : TreeBound (n := 4) 107 (programCode 0x4e29076b7c) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0xf30f4e6003ea6f30f6cc003cde60445f9805b3f53001e9cc01e6f3001e6003ccf303ccf3003cde7033d5,0x420410210481,0xf381181e600007983cfcc0f300003cc00003ccf30811bcc0000f3003cfcc1e600007980000000001dc6,0x0,0x402241000008004000004008000000010000022114000080080000100000000100004000010010000040040000080100000080002000100008000400010000800010001001487fea7,0x8000200080002008004200108002000080ce3,0xf388ce603cde6f4026cc003ea60044d91805d9ed3001e9cc01e6f3001e601e60f31e60f303cc1e7033d5,0xf30f6cc003ea6f3003cc003cde60445f9805b3f53001e9cc01e6f3001e9cc3cdf53000f3003cde7038e5,0x420410210481,0x8000200080002008004200100402000080ce3,0x420410210481,0x20410200481,0x600301000800004000400008000000010000022110000080100000100000000100004000010010000040040000080100000080200000100800000401000000801000001001887fea7,0x20410200481,0x1116f4e6f301e7300c2cc003ea60044dce405e2783001e9cc01e6f3001e679800fa9800f3f3001e7033d5,0xf30f6cc00f4e6f3003cc003cde60445f9805b3f53001e9cc01e6f3001e6003cdf533ccf300f31e7038e5,0x0,0x0,0x421010210481,0x0,0x0,0x421010208481,0x20001120020001000200000200200010000021000000010800000108000000108004000211310000010040000000900000100002020110001000080010200000010000210857d3a8,0x421010208481,0x20001140020001000200000400200010000021000000010800000108000000108004000211510000010040000000900000100002020110002000100020200000020000200097d3a8,0x421010210481,0x421010200481,0x421010210481,0x421010210481,0x421010220481],
[0x421010200481,0x421010220481,0x421010210481,0x0,0xf30f6cc00f4e6f3003cc00799e60445f98097ff53001e9cc01e6f3001e6003cde603ccf3003cde7038e5,0x420410210481,0xf31e9cc00f4e6f3003cc00799e604467300981db3001e9cc01e6f3001e600799e603ccf300799e7038e5,0x0,0x10000800040082000100208000200010041000800104004000010008001040008004000008010000c20040003000100000100610020801840082004000200004000020021006aea8,0x0,0xf381183cc00007983cfcc0f300003cc00003ccf30811bcc0000f3003cfcc1e60f307980000000001e56,0x0,0x420410210481,0xf381183cc00007983cfcc0f300003cc00003ccf30811bcc0000f3003cc3cde600f379800f3000001e56,0x420410210481,0x20410200481,0x8021000080004000080210000200010042000800108002000020008001080008004000280010000040040002800100000100100020001400084001000200004000040012005b9a8,0x20410200481,0xf381181e600007983cfcc0f300003cc00003ccf30811bcc0000f3003cfcc1e600007980000000001dc6,0x8000200100004008004200100002004080ce3,0x0,0x0,0x0,0x0,0x0,0x20021000020080000100200000200010000021000000024000000102000000208006203210101000000200800040010000100400021011000000024000004010000000200017de28,0x10400402001100044002010082080012000633e4,0x0,0x10400402001100044004020102080022000a05e4,0x0,0x79f9803ce04607983cc008118003ea60007d4c079801e7e805167cc3cfcc00088b079b15c0007985426,0x0],
[0xf379803ce04607983cc00fa98003ea60007d4c0f3001e9ce04d9f983cfcc00088b079a22c0007985936,0x400001001000004000000008000000010060002000100000000600000000200000002000010008000040008000040010000080400000101000000404000000810000001000887fe67,0x10400402001100044020080802080082000231e4,0x0,0x10400402001100044040081002080082000231e4,0x0,0x120841240481,0x808000200200008008004020108002200080ce3,0x120841240481,0x0,0x220882240481,0x20800240481,0x220882240481,0x220882240481,0x420804240481,0x420804240481,0x420804240481,0x20800240481,0xa20888240481,0x20800240481,0xa20888240481,0x220882240481,0x10400402002100084080082002080402000432e4,0x0,0x120841240481,0x0,0x120841240481,0x0,0x220882240481,0x20800240481,0x220882240481,0x220882240481],
[0x420804240481,0x420804240481,0x420804240481,0x20800240481,0xa20888240481,0x20800240481,0xa20888240481,0x220882240481,0x10400402004100104080002002080402000804e4,0x421010240481,0x20010240481,0x421010240481,0x20010240481,0x22010240481,0x20010240481,0x22010240481,0x20010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_5672 : TreeBound (n := 4) 107 (programCode 0x4e29076b7d) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x824090240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_5673 : TreeBound (n := 4) 107 (programCode 0x4e29076b7e) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x24010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_5674 : TreeBound (n := 4) 107 (programCode 0x4e29076b7f) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x824090240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_5675 : TreeBound (n := 4) 107 (programCode 0x4e29076b80) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x120450204481,0x804002200082002088004200100401020080ca3,0x120450204481,0x0,0x1000000004000a0002000000002000100040000800140002000000008000000008004000000010000a000400000001000010004000200014000a0004000200000000400020006aba8,0x100000040100000001000000401000001000000001000000010004000010010400000801000000804000008010000008040000010000000010400000100002000100108793a7,0x1000000004000a0002000200002000100040000200140002000000008001000008004000000010000a000400020001000010004000200014000a00040002000080004000200062ba8,0x88002200082002088004200108002002080ce3,0x520450210481,0x888002200082002088004200100402020080ce3,0x520450210481,0x0,0x9204d0220481,0x422201000000804000000008000004010000022110000080000000100100000100404000010010000040040000080100000080422000100000000400020000800080001001087fea7,0x9204d0220481,0x120450204481,0x0,0x0,0x421010210481,0x0,0x0,0x421010208481,0x40011008000900024080202008002400088042e4,0x421010208481,0x40021008000900024080202008004400108044e4,0x421010210481,0x421010200481,0x421010210481,0x421010210481,0x421010220481],
[0x421010200481,0x421010220481,0x421010210481,0x0,0x120450204481,0x100000080100000001000000801000002000000002000000020010000020040400000801000000804000008010000008000000010004000010000000100040000100108793a7,0x120450204481,0x0,0x0,0x0,0x0,0x0,0x520450210481,0x0,0x520450210481,0x8004200102004088004200100002200080ce3,0x9204d0220481,0x7980001e6003cfcc00f300003ccf30079bdb3001e9cc007a73001e600003cc1e60f307981e66bf95,0x9204d0220481,0x120450204481,0x0,0x88002200082200088004200100082002080ce3,0x0,0x108004200102200088004200100102004080ce3,0x0,0x0,0x3cc1e60f3003cfcc1e60007d4c00222c0007d4cf301e63cc1e60f301e6002046001ed98001ed983ebb56,0x0,0x0,0x0,0x4028100800120004408068a00801068820805104,0x8000200000200008004200101002040080ce3],
[0x4028100800120004408068a00801068840805104,0x8000200000200008004200102002080080ce3,0x8000200000200008004200100002000080ce3,0x8000200000200008004200104002100080ce3,0x8000200000200008004200100002000080ce3,0x0,0x40004100100100400000040800005001000004202400010001000100020000108090000040200000100800001008000001008040000010100000040400000081000000100108732a7,0xa08008200204008108004020108002200080ce3,0x0,0x0,0x220882240481,0x620884240481,0x220882240481,0x220882240481,0x620884240481,0x620884240481,0x620884240481,0x220882240481,0xa20888240481,0x620884240481,0xa20888240481,0x220882240481,0x0,0x422201001000004000000408000020010042202110000200010000800200012000900002010000008040000004020000010080400000101000000404000000810000001000487fe27,0x40005008002100084000a00028080402008040e4,0x0,0x0,0x421002240481,0x20000240481,0x421002240481,0x20000240481,0x20004240481],
[0x20000240481,0x20004240481,0x20000240481,0x421008240481,0x20000240481,0x421008240481,0x20000240481,0x0,0x4000410010080040000004080000c001000020202400080001000100020000208090000040200000100800001008000001008040000010100000040400000081000000100108732a7,0x0,0x0,0x0,0x220882240481,0x620884240481,0x220882240481,0x220882240481,0x620884240481,0x620884240481,0x620884240481,0x220882240481,0xa20888240481,0x620884240481,0xa20888240481,0x220882240481,0x0,0x0,0x40005008004100104000800028080402008040e4,0x0,0x0,0x220882240481,0x20000240481,0x220882240481],
[0x20000240481,0x20004240481,0x20000240481,0x20004240481,0x20000240481,0x20008240481,0x20000240481,0x20008240481,0x20000240481,0x421010240481,0x20010240481,0x421010240481,0x20010240481,0x822090240481,0x20010240481,0x822090240481,0x20010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_4923 : TreeBound (n := 4) 107 (programCode 0x4e29076b) := by
  conv in programCode _ => reduce
  exact branchFour (k := (3,1)) (by decide +kernel) part003_4924 part003_4925 part003_4990 part003_4991 part003_5216 part003_5217 part003_5282 part003_5283 part003_5524 part003_5525 part003_5558 part003_5559 part003_5672 part003_5673 part003_5674 part003_5675

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_5821 : TreeBound (n := 4) 107 (programCode 0x4e29076c51) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0xf307983cc0002d907987983cde6044580005b3f53001e9cc01e6f3001e6003ccf303cc3cc03cde7032b5,0xf307983cc01e6f307980003cc00044580005b20f3001e9cc01e6f3001e63cc01e6000079bcc01e703855,0xf307983cc0006a50798f303cde6044580005b3f53001e9cc01e6f3001e6003ccf301e67980799e703345,0x0,0x1020100204022,0x1020501284222,0x1020501284222,0x1020501284222,0x0,0xf3003cfcc007a73003cc1e63cc007d4c3ec49cc0079bcc07c6830079bcc0097ef300f33cc0798fb1a646,0x1020100204022,0x80082002004100004004000102001020040804e4,0x1020104204022,0x1020104204022,0x0,0x1020104204022,0x0,0x0,0xf307983cc0798f3079800044580044580005b203cc01e6f301e63cc01e6f3001f530007a73001eacf855,0x0,0xf30079bcc01e6f3003d1eecf300f33cc1e603ccf30bddbcc01e6f3003d1eeef76f307981e601e688ce56,0xf3003cfcc00f3f3003cfcc03cc079bcc5b203ccf3003cfcc2e83f3003cc02055301ed98001e6f3812d56,0xf307983cc001f5307a3dd83ea60044580005d9ed3001e9cc01e6f3001e601e60f307983cc3cc1e7032b5,0xf307983cc0002d907980003cde6044580005b20f3001e9cc01e6f3001e6003cdf5300079803cde703855,0xf30079bcc00f3f3003d1eecf3088b3cc222c3ccf30bddbcc1116f3003d1eeef7688b79801e711688cdc6,0xf3003cfcc00f3f3003cfcc03cc1e63cc3ea63ccf3003cfcc2e83f3003cc0f522c0f379800f33cc9f8d56,0x0,0x16c8000f3f30017232003cde603cc79805b4e83001e9cc01e6f3001e60f300f33cc03cde601e7032b5,0x420410210481,0x25f80007a730025f80003cde603cc79805b20f3001e9cc01e6f3001e61e601e67980799e601e703855,0x0],
[0x17bb079bcc01e679803d1eecf300f33cc1e603ccf30bddbcc01e6f3003d1eeef777bb7981e601e688ce56,0xf3084e7cc00f30000000011160000f300003cc0f30079bcc007a73001e63cc03ccf300f31e601e64dcf5,0x7980799e6f300faf39983ea6003d398005d9ed3001e9cc01e6f3001e60f300f33cc03cde601e7032b5,0x1e679803ccf300f33d1eecf300003cc00003ccf30bddbcc0000f3003d1f687b2c00798003cc00001dc6,0x420410210481,0x108dd509fbccf3000000001141aa00f300003cc0f30079bcc007a73001e63cc03ccf300f31e601e64dcf5,0x420410210481,0x420410210481,0x2008080000080002008004200101002040080ce3,0x20410210481,0x1e6001ed980f33cc7f57f83db3003cfcc005cc481001e9cc01e6f3001e60f300f33cc03cde601e77cab5,0x10274d18007a73000000001119cc01e600003cc0f30079bcc00f3f3001e63cc03ccf300f31e601e68a925,0xf3003cfcc00f3f3003cfcc03cc7983cc3ea63ccf3003cfcc2e83f3003cc1e8d90079f9801e6f30812d56,0xf30079bcc01e6f3003d1eecf300f33cc1e603ccf30bddbcc01e6f3003d1b22f76f307981e601e688ce56,0xf3003cfcc00f3f3003cfcc03cc079bcc5b203ccf3003cfcc2e83f3003cc799f5379879807980f3812d56,0xf307983cc0798f30a7100044580044580006684f3001e9cc01e6f3001e679800f4e6003db3001eacf2b5,0xf3003cfcc00f3f3003cfcc03cc079bcc5b203ccf3003cfcc2e83f3003ccf31f533cc7980f300f3812d56]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_5870 : TreeBound (n := 4) 107 (programCode 0x4e29076c52) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x1020501284222,0x1020501284222,0x1020501284222,0x1020501284222,0x0,0xf3003cfcc007a73003cc00408c00408c000408c0079bcc079816c879c08e04702b19183ec6461749e306,0x1020501284222,0x80082002000900024004004102000820020100e4,0x1020505284222,0x1020504284222,0x0,0x1020504284222,0x0,0x0,0xf307983cc097ef3081183cc97e00fa9803ce7de3cc01e6f301e63cc01e6003cde603cc79803cdeacf855,0x0,0x80082002000900024080006002000c00020100e4,0x0,0x1020501280222,0x1020501280222,0x1020500280222,0x1020501280222,0x0,0x1020502388702,0x1020501280222,0x1020502388702,0x1020505280222,0x1020504280222,0x0,0x1020504280222],
[0x0,0x0,0xf307983cc097ef3081183cc97e00fa9803ce7de3cc01e6f301e63cc01e600799e601e67980799eacf855,0x0,0x0,0x1020501284222,0x1020501284222,0x1020501284222,0x1020501284222,0xf307983cc01e6f3079803cc00003d39803cde6000799e60799e600799e607981e607987987981e703855,0x1020502384702,0x1020501284222,0x1020502384702,0x1020505284222,0x1020504284222,0x0,0x1020504284222,0x0,0x0,0x1dcd6500773d075940773770d6500773d075940773770d65007735940079126a5001e449a94000079126a500079126a5000079126a5001dcddc3d075940002540c01cddc3d075940000ee6b2f73d0759400ee6b45cd65fd51da80000ee6b2f735a2e6b29dcd65ee6b36e6b3577e5ba,0x0,0xf307983cc01e6f3079803cc00003d39803cde60f3001e9cc01e6f3001e601e61e61e607981e61e703855,0x400001001000001004000010010000010000021000000010800000108000000108004000211310000010040000000900000100002020110001000080010200000010000210857d3a8,0x80082002000900024080006002080400020100e4,0x400001001000001004000010010000010000021000000010800000108000000108004000211510000010040000000900000100002020110002000100020200000020000200097d3a8,0x80082002000900024080086002010c00402130e4,0x80082002000900024080046002008400201138e4,0x0,0x0,0x421010210481,0x0,0x0],
[0x221090210481,0x2001000001001000010010000010010000021000000010800000108000000108004000211310000010040000000900000100002420130001000080004200000010000210857d3a8,0x221090210481,0x2001000002001000020010000020010000021000000010800000108000000108004000211510000010040000000900000100002820150002000100008200000020000200097d3a8,0x421010210481,0x21010210481,0x421010210481,0x421010210481,0x821090210481,0x21010210481,0x821090210481,0x421010210481,0x80082002000900024080086002010400402130e4,0x400001001000001004000010010000010000021000000010800000108000000108004000310110000010040000000900000100600030010800040004000200004000000222017d3a8,0x400001001000001004000010010000010000021000000010800000108000000108004000330110000010040000000900000100200030010100008001000200001000000214817d3a8,0x80082002000900024080006002080400020100e4,0x40000100100000100400001001000001000002100000001080000010800000010800400035011000001004000000090000010020003001020001000200020000200000022a017d3a8]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_5951 : TreeBound (n := 4) 107 (programCode 0x4e29076c53) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0xf307983cc00088b0798798799e6016c800097ff53001e9cc01e6f3001e6003cde603cc3cc03cde7037c5,0xf307983cc0000f3079800079800025f800097e0f3001e9cc01e6f3001e63cc01e6000079bcc01e703855,0xf307983cc0002d90798f303cde6016c800097f023001e9cc01e6f3001e6003ccf300f33cc0799e7032b5,0x0,0x1020501284222,0x1020501284222,0x1020501284222,0x1020501284222,0x0,0x1020d02384702,0x1020501284222,0x1020d02384702,0x1020505284222,0x1020504284222,0xf307983cc0004bf07d5b303cde6025f800097fe63cc1e61e61e607981e61e600f301e6799ed99e703345,0x1020504284222,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4000020080000180100008000108009000040040000104000000812000002809040000020100000400400000801000000800004000200080000800100004000100010030840da7,0x1001000004004000010008000010010040100800100002000001008001000008004000210010000040040002000100000100400020001400080204000200004000002012107baa8,0x4000020010000080040008000208009000040040000104000000408000002809840000020100000400400000801000000800004000200080000800100002000100010030840ca7,0x0,0x5200010004800040052000080002000100520008001480020001200080014800080040002900100002400400029001000001004000200014800a4004000200004000240012007baa8,0xf307983cc1e603cc3d008cf300f33cc408c3ccf30bddbcc2d90f3003d1eee046f307981e601e688ce56],
[0x40000020100000000400008002008009000040000000104000000400000002809840000020100000400400000801000000800004000200080000800100002000100010030840ca7,0xf307983cc1e607983d008cf300f33cc408c3ccf30bddbcc2d90f3003d1eee046f307981e601e688ce56,0x88b07983cc1e679803d1eecf3088b3cc5eec3ccf30bddbcc2f76f3003d1eeef76f307981e6111688ce56,0x7980799e601e61e603d1b20f307983cc1e603ccf30811bcc01e6f3003d1b22d90f307981e60f3088ce56,0x0,0x7980799e601e63cc03d1b20f307983cc1e603ccf30811bcc01e6f3003d1b22d90f307981e60f3088ce56,0x0,0x80082002000100004010000002002000080000e4,0x1020d01388702,0x1020100208022,0x1020d01388702,0xf3003cfcc01e6f3003d1b203cc7983cc3cc03cd6c803cfea7f5379803cc02139001ed98001f530812de6,0x1020902208502,0x1020100208022,0x1020902208502,0xf3003cfcc00f3f3003cfea63cc079bcc3ea63cc07983d1b22d9007983cc02046001edd4c01e6f3812d56,0xf30079bcc01e6f3003d017ff3003ccf300003cc0f3cd080f300003cc3cc07b8bf807980001e679a9e1f6,0x0,0xf3003cfcc00f3f3003cc1e63cc079bcc3ea63cc07983cc1e8d9007983cc02046001e63cc01e6f3812d56,0xf3003cfcc00f3f3003cfcc03cc7983cc3cc03cc79803cfcc1f5379803cc02139001ed98001f530812d56,0xf3003cfcc00f3f3003cfcc03cc1e63cc3cc03cc1e603cde61f531e603cc02082c01ed98001e9cc9f8d56,0xf307983cc0000f307980003cc00016c800097e01e601e67981e63cc01e600000f30000408c001e7032b5,0xf3003cfcc00f3f3003cfcc03cc3cc3cc3cc03cc3cc03ccf31f533cc03cc020bf801ed98001ed98bded56,0xf307983cc001f5307a01183ea60025f800099e553001e9cc01e6f3001e601e60f30f307983cc1e703345,0x0,0x80082002000100004000000002004000100000e4,0x1020d01388702,0x1020100208022,0x1020d01388702,0xf30079bcc00f3f3003d1eecf3088b3cc5eec3cd7bbbdda22ef7679803cc07c77600fedd803dd1688cdc6,0x1020902208502,0x1020100208022],
[0x1020902208502,0x80082002000100004000000402004000100000e4,0xf30079bcc01e6f3003d008cf3003ccf300003cc0f3cd080f300003cc3cc07b84601e600003cc79a9e1f6,0xf307983cc0002d907f41303cde6016c800097ef33cc1e60f31e607981e6003ccf300f33cc0799e7032b5,0xf3003cfcc00f3f3003cc1e63cc079bcc3ea63cc07983cc1e8d9007983cc03ea6000f33cc03ccf3812d56,0x0,0xf3003cfcc00f3f3003cfcc03cc7983cc3cc03cc1e603cde61f531e603cc03f99000fa98003db30812d56,0x0,0xf3003cfcc00f3f3003cfcc03cc3cc3cc3cc03cc3cc03ccf31f533cc03cc03f1f800fa98003d398bded56,0xf307983cc01e6f307b66003cc00016c800097e0f3001e9cc01e6f3001e60f300f3f3003ccf301e7032b5,0xf307983cc001f5308199183ea60025f800099e553001e9cc01e6f3001e9cc000f30f307d8c8c1e703345,0x0,0x16c8000f3f30016c8000799e601e6798097e0f3001e9cc01e6f3001e61e601e67980799e601e703855,0x420410210481,0x16c80007a73002634c003cde601e6798097ff53001e9cc01e6f3001e60f300f37980799e601e703345,0xf32634c00f4e6f30798000799e604467300981db3001e9cc01e6f3001e61e601e6f300f31e601e7038e5,0x600001000000004004000004004000010060001000100004000000008000000008004000210010000040040000000100000100600030000000000000000200004000000000007fda8,0x0,0x798079bccf300fad62c83ea6001ed98009a5ed3001e9cc01e6f3001e60f300f37980799e601e703345,0x0,0x420410210481,0xf307983cc0f303cc3cfcc0f300003cc00003ccf30811bcc0000f3003d008de6000079800f3000001dc6,0x420410210481,0x420410210481,0x2008080000100004008004200101002040080ce3,0x20410210481,0x1e600102300f33cc7d5b303db3001e9cc0098f61f001e9cc01e6f3001e60f300f37980799e601e77cb45,0x7980798f300f33cc03d2a50f303cc3cc0f303ccf3084e7cc00f3f3003d2a535283cc7980f30798cd25c6,0xf307983cc0000f307980003cc00016c800097e0f3001e9cc01e6f3001e9cc000f30000408c001e7032b5,0x0,0x0,0x10020000100004008004200102002080080ce3],
[0x0,0x0,0x7980f37a7300085dbbf03cc3cc1e7e600ab87cf001e9cc01e6f3001e679800fa980079f9801e7051a5,0x16c8b643cc03cc0000000012090003cc00007980f30079bcc007a73001e7e6003cde600f379801e64dcf5,0x7980799f53000ff63d083cc1e60fa9800ad6fb5001e9cc01e6f3001e679800fa98003d39801e7032b5,0x0,0x810020000100004008004200102002080080ce3,0x17ddeae9679bcc00000000122ba583cc00007980f30079bcc007a73001e7e6003cde600f379801e64dcf5,0x1010040000100004008004200102002080080ce3,0x840510220501,0x840510220501,0x840510220501,0x840510220501,0x40510220501,0x0,0x16c8000f31e60176cb083ea6000f379809a6e03001e9cc01e6f3001e63cc00f30f3040dda21e7032b5,0x400410200481,0x16c8000799e6026799183ea6001e6798099e553001e9cc01e6f3001e63cc00f30f307d8c8c1e703345,0x0,0xf3003cfcc01e679803cfcc03cc7983cc3cc03ccf3003cfcc1e60f3003cc799e607987980798f30812de6,0xf307983cc00000000000011160003cc00007980f30079bcc007a73001e9cc003cc0000f300001e64dcf5,0x7980799e7e600fb3cb083cc0000fa98009a6e03001e9cc01e6f3001e600000f3f30040dda21e7032b5,0x0,0x400410200481,0x1041e2296798000000000011382c03cc00007980f30079bcc007a73001ea10583cc0000f300001e64dcf5,0x400410200481,0x410200481,0x800410200481,0x410200481,0x800410200481,0x410200481,0xf307983cc0798f3097e00044580025f80009f78f3001e9cc01e6f3001e679800f6cc007a73001eacf345],
[0x0,0xf3003cc1e60f46c803cfcc03cc079bcc3ea63ccf3003cfcc2d90f3003ccf31e603cc7980f300f3812d56,0x0,0x16c80003cc00025f80003cc0000f33cc097ff53001e9cc01e6f3001e600000f30000408c001e7032b5,0x0,0x0,0xf307983cc00000000000011160003cc00007980f30079bcc007a73001e9cc003cc0000f300001e64dcf5,0x0,0xf33cc0799e600f33cfcfcfcc01e9cc3cc03ccf3003cfcc1e60f3003ccf31e607987980f3003d4313e6,0x3d39803cc005b5d3996c83cde6025ff98097ff53001e9cc01e6f3001e9ccb64f302d97d4cb65e703345,0x1041d99e6798000000000011382c03cc00007980f30079bcc007a73001e9ccf33cc0000f300001e64dcf5,0x3cc0000f3001ed9f996c83cde600f30000980e83001e9cc01e6f3001e9ccb64f300f3408cb65e7032b5,0x410200481,0x840510220501,0x410200481,0x840510220501,0x410200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_6096 : TreeBound (n := 4) 107 (programCode 0x4e29076c54) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x1020501284222,0x1020501284222,0x1020501280222,0x1020501284222,0x40000080100000400400000401000001000001080000008080000008800000020800000000000000004000200000080004010000000000000000000100000008400000030001eb1a8,0x400021b7b00008000400000001000086dec00361b6000010000400360000000486d80002010000008040000010080000010080436c00100000000080008000210db0001001087cca7,0x1020501284222,0x80042002000900044004824522902024100904a4,0x0,0x0,0x0,0x0,0x1dcd6500000773598a817e5cd65ee6b2f73595dcd66dcd650000000003f5476bdcd7510b8720003b9aca1dcd65ee6b280001dcd650000077447ab2803ba23d59401dd11eaca001dd11eaca001dd11ebb86b2803ba23d59400eea6c2ca003b9e83aca00ee6ee1aca00ee6d0c7c9ffa9,0x400020001000080004000000010000800040022000000080000400060000000480000002010000002010000010080000010080400000100000000084000001010000001001087c7a7,0x40002000100008000400004001000080004000200000001100040002000000058000000040200000100800001008000001008020000010020000010200000100200000100908713a7,0x400020001000080004000000010000800040022000000080000400060000000480000002010000002010000010080000010080400000100000000084000001010000001001087c7a7,0x0,0x1020501284222,0x1020501284222,0x1020501280222,0x1020501284222,0xf3003cfcc00f3f3003cc007d4c00222c0007d4c000f6cc010323000f6ce047e64bf2268de600044d4bb6,0x1020501388702,0x1020501284222,0x1020501388702,0x1020501294ae2,0x1020501290ae2,0x0,0x1020501290ae2,0xf3003cfcc00f3f3003cc007d4c00222c0007d4c000f6cc010230000f6cde61e60f303cc1e600044d4bb6],
[0xf3003cfcc01e6f3003cc008118003ea60007d4c002046000a52dcc0f6ccf307983cca71fa98007e44426,0xf3003cfcc00f3f3003cc007d4c00222c0007d4c000f6cc00f303cc0f6cc0097e0f30000f307983cc33b6,0xf3003cfcc01e6f3003cc008118003ea60007d4c00222c000b091cc0f6ccf30f30798d4b0230008655c26,0x0,0x1020501284222,0x1020501284222,0x1020500280222,0x1020501284222,0x0,0x1020502388702,0x1020501284222,0x1020502388702,0x1020505294ae2,0x1020505290ae2,0x0,0x1020505290ae2,0x0,0x0,0x0,0x0,0x0,0x1020501284222,0x1020501284222,0x1020501280222,0x1020501284222,0x80082002001100044001000042000000800201e4,0x1020501388702,0x1020501284222,0x1020501388702,0x1020501294ae2,0x1020501290ae2,0x80082002001100044001000042000002000201e4],
[0x1020501290ae2,0x0,0xf3003cfcc01e6f3003cc008118003ea60007d4c0020460011ae1cc1e9ccf307983cc97efa98007e44426,0x0,0xf3003cfcc01e6f3003cc008118003ea60007d4c0020460012279cc1e9ccf30798798b650230007e44426,0x0,0xa0080000280300001000400001000040000010000200200400820c4000400000000800400002001000010008000010008040000010100000040400000101000000100108777a7,0x168f63350ae39cb479b0b7c78e702d1ec66a15c7380b479b0b7c78e700b47b19a8571ce0168f63350ae39c0168f63350ae39c0b4d283eb1b9c02d4b3003bfce00169a507d63738002d4b3003bfce0005a6941f58dce000b4d283eb1b9c000b4d283eb1b9c000000000070f84ba5c05fdc8830ae3a747847c8a0f08f8e868fbd712eccdbc5101adf336f08f8e70169a507d6373da3c7e1fbfe39c0000168f08f99b784935cc51ccd6de11f336f08f8e70002d784e15b46de11f336f08f8e700005fdfe621d5c000168f08ff59651f2eb5e,0x220080000880100002000400002000040000010000200200400820d0000400000000800400002001000010008000010008040000010100000040400000101000000100108777a7,0x20100000080400000080400000201000002080000008080000008800000020800000000000000004001200000104000010040000000100008000400000011000000050002fb1a8,0x100000000400120000400400001000002080000008080000008800000020800000000000000004001200000104000010040000000100008000400000011000000050002fb1a8,0xb478530ebc7c73ad1e124c0a23e3a7478530ebc7c73ad1e14c3af1f1ceb4784d6afa3e39cb4784d6afa3e39cb4784d6afa3e39d694acbb2539c000b5e13856c67001694acbb2539c005a52b2ec94e7000b4d283eb1b9c000b4d283eb1b9c000b4d283ecb3144ced0a7fa005bd6e4433800b60fc014185a04bd801540a0571d6a5996ad0769413c23e66de11f1cf68f14406b7c73da3c7e1fbfe6caf099d72c836ad70002d784e15b4caf099d72c836ad7005a9c03c9be08af099d72c836ad7005a41c7a5da39c00016bd90b0c1176dd678e,0x1dcd66dcd65777130a6d66ddc4d8f56577359c61c46f735940000eea6e09941d6503b9aca0ee6b639ca711f9bf993283b9aca00000ee6c166b28ee6c166b28077360b35943b9b059aca03b9b05a23d594003bb89765000eee25d94003bb89765000eee25d94000ee6d0c7caab89,0x200100000800400000800400002001000002080000008080000008800000020800000000000000004001200001104000010040000000100008000400000111000000050022fb1a8,0x420201000000401000080008000200010000021000000024000000102000000208006203210101000000200800040010000100400021011000000024000004010000000200017de28,0x20001000080001000040008000100010000021000000024000000102000000208006203210101000000200800020010000100400021011000000024000002010000000304c1fde28,0x20020080080080100200000400200000040000000000200200400820c0000400000000800400002001000010008000010008040000010100000040400000101000000100108777a7,0x20001000020001000100008000200010000021000000024000000102000000208006203210101000000200800040010000100400021011000000024000004010000000200017de28,0xafb2bb0159fd80acfec0159fe2cfec00159fdab3fb0002b3fb0159fd80567f6567f6000567f60002b962f60000002c99ad8000002b962f600000056d5df6000000adabbec000000adabbee09b0721474334b17b000000572f12bb57d962e8a2fec02b3fb0159fdd67f600567f60005680b9fd8104d8337657600000057d95d8057d9633e756015f657759fd80567f60567f6000000164f8ac880b26e2c,0xacfec00159fdab3fb0000acff6cfec00159fd8acfec002b3fb159fd800567f6159fd800567f60002b962f600000016f9d58000002b962f600000056d5df6000000adabbec000000adabbee09b0674488334b17b000000572f12bb57d96034a7fed5cb17b0159fd959fd80567f60005680b9fd81037e35f657600000057d95d80567f630a7a60159fd8159fd80159fd8567f6000000164f8acde70e5e2c,0x10,0xacfec00159fd82b3fb00056800cfec00159fd959fd8002b3fb2b3fb000567f62b3fb000567f60002b962f60000000c29e98000002b962f600000056d5df6000000adabbec000000adabbeeae1184feb6b7e7337600000164cd6c00159feda084fec2b3fb0159fdab3fb00567f60005680b9fd8149c5bab84ae00000016f9d580000001b07ce00159fd959fd802b3fb0567f600000016bd2f4061794e2c,0x80082002001100044002010082080012000633e4,0x0,0x1020501284222,0x1020501284222,0x1020501280222,0x1020501284222,0x80082002001100044000000042000000800201e4,0x1020503388702,0x1020501284222,0x1020503388702],
[0x1020505294ae2,0x1020505290ae2,0x80082002001100044000000042000002000201e4,0x1020505290ae2,0x0,0x0,0x0,0x0,0x80082002001100044004020102080022000a05e4,0x0,0x1020505284222,0x1020505284222,0x1020505280222,0x1020505284222,0xf307983cc01e6f3079803cc00003d39803cde6003cc1e63cc1e603cc1e601e61e61e607981e61e703855,0x1020507388f02,0x1020505284222,0x1020507388f02,0x1020505294ae2,0x1020505290ae2,0x8008200200110004400100840200000a000201e4,0x1020505290ae2,0x0,0x400001001000004004000008010000010000021000000084000000102000000208006202310108000400000010000802000100200030010800040000400000081000400222017fe28,0x0,0x400001001000004004000008010000010000021000000084000000102000000208006202310108000400000010000802000100200030010800040001000000082000400222017fe28,0xf3003cfcc01e6f3003cc008118003ea60007d4c079801e7e805167cc3cfcc00088b079b15c0007985426,0x0,0xf307983cc0002d907d53b6601e6016c801ebb3e63cc1e61e61e607981e6003ccf303cc79803cde703345,0xf3003cfcc007a73003cc007d4c0012fc0007d4cf3003cc011162d90f6d3985b21e644587983cc1e614c6,0xf307983cc0004bf07d5b4e601e6025f801ef7fe63cc1e61e61e607981e6003ccf301e67980799e703345,0xf307983cc0000f3079801e600000079801e7e6003cc1e61e61e607981e61e600f30000799e601e703345],
[0x0,0x0,0x0,0xf307983cc0000f3079801e600000079801e7e6003cc1e61e61e607981e61e600f30000799e601e703345,0x0,0x0,0xf307983cc0000f3079801e600000079801e7e6003cc1e61e61e607981e60f300f37980799e601e703345,0x400021001000080004000000010000000042002000002000000000020000020000000200010000800040000800080002000080420000101000000400000000400000001001087fda7,0x0,0x0,0x0,0x0,0xf30079bcc01e6f3003cc00fa98003ea60007d4c0f3001e9ce04d9f983cfcc00088b079a22c0007985936,0x0,0x60000000120000001000020001a000c00000040100000104000000405000a010040000200100000801000008001000008040000010100000010400000101000000100108713a7,0x0,0x0,0x0,0x2000100000000400120000400400001000002080000008080000008800000020800100000000400004001200000104000010040000000100008000400000011000000050002fb1a8,0xf3079800000000000005b21e616c80000f300007980798f300f31e601e9cc003db3000f6cc001e68a925,0x3cc0000f3001e9cc007d4c00222c0007d4c79803cc00000079803cfcc0000f300003cc0003cc33b6,0x4080102001100044004020802080022000a05e4,0x10080402001100044020080802080082000231e4,0x8080202001100044020040802080042000239e4,0xf37d4c3cc2d9079f983cc000111600016c9e601e601e6f300f31e601e9cc003db3000f6cc001e68a5c5,0x10080402001100044020080802080082000231e4,0x798d4a0f307981e60005b235296c81e60f300007980798f300f31e601e9cc003db3000f6cc001ea56925,0xf3079800000000000005b21e616c80000f300007980798f300f31e601e9cc003db3000f6cc001e68a925,0x200020000200040002000040002000c0004000200001000100040000400050008000040000200100000801000008001000008040000010100000010400000101000000100908713a7,0xf3079800000000000005b21e616c80000f300007980798f300f31e601e9cc003db3000f6cc001e68a925,0x0,0x80080002001100044020000802080002000201e4],
[0x1023798408c0000798003cc1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0,0xf307983cc00000000003cc1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925,0x10080c02001100044020180802080182006231e4,0x2080082001100044020010802080012004233e4,0x0,0x4080102001100044020020802080022004235e4,0x10080402001100044020080802080082000231e4,0x8080202001100044020040802080042000239e4,0x80080002001100044020000802080002000201e4,0x10080402001100044020080802080082000231e4,0x30080802001100044020100802080102004231e4,0x20080802001100044020100802080102004231e4,0x7987981e600003cc0003cc1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925,0x40081002001100044020200802080202008271e4,0x0,0x60000000140000001000020001c0004000000408000001040000004080008000200000200200000802000008002000008040000010100000010400000101000000100108713a7,0x0,0x0,0x0,0x0,0x0,0x0,0x2000080008000000000000800080004000000008000000040002000080008000200000200200000802000008002000008040000010100000010400000101000000100108713a7,0x0,0x0,0xf381183cc1e6079f983cc00016c80001e61e6079801e7e600f33cc01e9cc003db3000f6cc001e68a5c5,0x0,0x1000004001000010000800100040000100000082000000208000002080000002080000020a000000201001400200000008010040000a00100008000400020001000028041482513a8,0x400020000000080000000000000000000070002000100000000400000000400000002000010004000040010000020020000080400000101000000204000000810000001000487ee27,0x0,0x400020000000080000000000000000000070002000100000000400000000400000002000010004000040010000020020000080400000101000000204000000810000001000487ee27],
[0x0,0x0,0x0,0x0,0xf307983cc00000000003cc1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925,0x10080802001100044040081002080082000231e4,0x2080082001100044040011002080012008273e4,0x80042001100044040001002080002000201e4,0x4080102001100044040021002080022008275e4,0x80402001100044040001002080002000201e4,0x8080202001100044040041002080042000239e4,0x0,0x10080402001100044040081002080082000231e4,0x30080802001100044040181002080182004231e4,0x20080802001100044040101002080102004231e4,0x0,0x40081002001100044040201002080202008271e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_6305 : TreeBound (n := 4) 107 (programCode 0x4e29076c55) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0xf307983cc0002d9079a5f9e61e61ed98002048d900f4e600f4e6000f4e9cc001023000408c001e7032b5,0x80082002000100804000880022080402000000e4,0xf307983cc0006a50798f31e61e61ed98002047e600f4e6007b66001e7e9cc0010230007d4c001e703345,0x0,0x80042002000100804000880042000000000000a4,0x80042002000900824000884042100804020100a4,0x80042002000100804000880042000000000000a4,0x8004200200090086400088c042300804040301a4,0x10221012210e2,0x1022901209502,0x10221012210e2,0x1022901209502,0xf30079bcc01e6f3003d286af300798f307983cc0049cd400f3f3001e9d286d43507983cc1e60f32615f6,0xf30079bcc01e6f3003d20d2f3003ccf307983cc004990800f3f3001e9cc3cf06903cc1e60f3079a9e1f6,0x0,0xf30079bcc01e6f3003d1eecf300f30f307983cc00489d800f3f3001e9cc3cef760f307981e61e688cdf6,0x0,0x10221012210e2,0x0,0x10221012210e2,0x8008200205020100405028100208068200a05104,0x800820020502010040042800820806b200a05104,0x80042002000100804000080002080002000000a4,0x800820020502010040042801020806a200a05104,0x10221042410e2,0x10221042410e2,0x0,0x120844240481,0x880022000100804000880022080402000000e4,0x120844240481,0x0],
[0x230884240481,0x20804240481,0x230884240481,0x230884240481,0x420804240481,0x420804240481,0x420804240481,0x420804240481,0x8308c4240481,0x20804240481,0x8308c4240481,0x630884240481,0x10221042410e2,0xf30079bcc01e6f3003d20d2f3016c8f307983cd6c8cd0bcc00f397e03cfcc3069f307983cc02d9aec5f6,0x8008200205020100404028080208068200a05104,0xf307983cc0798f30a71001ed9801ed980020fc41e601e67981e63cc01e9cc001023000408c001eacf2b5,0x8008200205020100404028100208068200a05104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_6354 : TreeBound (n := 4) 107 (programCode 0x4e29076c56) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x80082002002100084080082002080402000432e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_6355 : TreeBound (n := 4) 107 (programCode 0x4e29076c57) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0xf307983cc00088b079a5fbcc1e608118003ea7e600f4e600f4e6000f4e9cc001f53000408c001e7037c5,0x0,0x1020101200022,0x1020501284222,0x1020101200022,0x1020501284222,0x10221012210e2,0x1020901208502,0x1020101200022,0x1020901208502,0xf3003cfcc00f3f3003cfcc03cc079bcc01e63cc000f6cc012090000f6cc1e7e616c803cc1e60f3812d56,0xf3003cfcc00f3f3003cfcc03cc03cfcc00f33cc000f6cc01152c000f6cc0f4e600f301e60f307a235956,0x0,0xf3003cfcc00f3f3003cfcc03cc079bcc01e63cc000f6cc012090000f6cc1e7e6007983cc1e60f3812d56,0x80082002020100804000880022080100804030e4,0x10221012210e2,0x80082002000100004000800022080000000000e4,0x10221012210e2,0xf307983cc0002d907996c9e61e608118003ea8d900f4e6003ea6001e7e9cc001023000408c001e7032b5,0x0,0x1020101200022,0x1020501284222,0x1020101200022,0x1020501284222,0x10221012210e2,0x1020901208502,0x1020101200022,0x1020901208502,0x80082002000100004001000042000000400000e4,0xf3003cfcc00f3f3003cfcc03cc0f33cc03cc3cc001e9cc009bac001e9cc0f4e600f307980f31e6aebd56,0x80082002000100004001000042000002000000e4],
[0xf3003cfcc00f3f3003cfcc03cc079bcc01e63cc001e9cc00a710001e9cc1e7e6007983cc1e60f3812d56,0x0,0x10221012210e2,0x0,0x10221012210e2,0x0,0x1108c2240481,0x7735943b9bd63c46acbdcd65000eee25d940007739c4e2343b9acbe08ffca000773989476a3bd664ca000ee6f1d476a1dcd73e6b29dcd82cd650ee6c166b281dcd82cd6500ee6c166b283b9b05a23d594000f047fe50003c11ff94001deb326500077acc994000ee6ba6d0b8779,0x1108c2240481,0x2420041000000404000000200090001000082120000408000001001200002000800020010000080040000040020000100080400000041000000204000000810000001000485ee27,0x210882240481,0x410882240481,0x210882240481,0x210882240481,0x410882240481,0x410882240481,0x410882240481,0x210882240481,0x8108c2240481,0x410882240481,0x8108c2240481,0x210882240481,0x1020902240502,0x1020100240022,0x1020902240502,0x1020104240022,0x1020104240022,0x0,0x120844240481,0x0,0x120844240481,0x0],
[0x230884240481,0x20804240481,0x230884240481,0x230884240481,0x420804240481,0x420804240481,0x420804240481,0x420804240481,0x8308c4240481,0x20804240481,0x8308c4240481,0x630884240481,0x1020104240022,0x0,0x12fc0010230001b87799f530007987983fd8b94601e7e601e61e601e9cc001023000408c001ee9b2b5,0x420031100080000004200080000400000000203110000800000002000000002000002000010002000010010000080010000080400000101000000404000001010000001001087f7a7,0x12fc00088b0002ab86c9f53000f307983fd8030601e7e601e61e601e9cc0010230007d4c001ee9b345,0x600030000800000006000080004000000000203000000800000002000000002000002000010002000010010000080010000080400000101000000404000001010000001001087f7a7,0x2509c8240501,0x840908240501,0x2509c8240501,0x2509c8240501,0x4709c8240501,0xe709c8240501,0x4709c8240501,0x840908240501,0x840908240501,0x840908240501,0x840908240501,0x40908240501,0x0,0x1308c6240481],
[0x1023798408c000079800007b66001e600003cc00f3007980000f300001e9cc003db3000f6cc001e68a925,0x1308c6240481,0xf307983cc0000000000007b66001e600003cc00f3007980000f300001e9cc003db3000f6cc001e68a925,0x230884240481,0x800240481,0x230884240481,0x230884240481,0x400800240481,0x400800240481,0x400800240481,0x800240481,0x800800240481,0x800240481,0x800800240481,0x800240481,0xf307983cc0798f3097e001ed9800fa98003f1f81e601e6f301e63cc01e9cc0010230007d4c001eacf345,0x0,0x0,0xf6cc00f3f3000f6cc0003cc00408c000f6cc3cc03ccf300003cc03cfcc0000f3000222c0007985216,0x0,0xf307983cc0000000000007b66001e600003cc00f3007980000f300001e9cc003db3000f6cc001e68a925,0x210880240481,0x800240481,0x210880240481,0x210880240481,0x410882240481,0x410882240481,0x410882240481,0x800240481,0x840908240501,0x800240481,0x840908240501],
[0x800240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_6484 : TreeBound (n := 4) 107 (programCode 0x4e29076c58) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x80082002004100104080002002080402000804e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_6485 : TreeBound (n := 4) 107 (programCode 0x4e29076c59) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8008200205020040408028200208068200a05104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_6486 : TreeBound (n := 4) 107 (programCode 0x4e29076c5a) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8008200201020020408038200208048200205104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_6487 : TreeBound (n := 4) 107 (programCode 0x4e29076c5b) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x16c8000f3f30016c801e601e67980799e7e60f3001e9cc01e6f3001e9cc001f530007d4c001e703855,0x0,0x621090204481,0x421010210481,0x621090204481,0x0,0x421010208481,0x3d39800f4e6000f6cfd49a30007d4c000408cf308635ec001023003cc07b6b389ed98001e60fc0dfd6,0x421010208481,0x3d39800f4e6000f6cfd49a3000f6cc000408cf3082a6ac001f53003cc07b6a459ed98003cc1e611156,0x421010210481,0x421010200481,0x421010210481,0x421010210481,0x421010220481,0x421010200481,0x421010220481,0x421010210481,0x16c80007a73002634c0f301e67980799e7e7f53001e9cc01e6f3001e9cc0010230007d4c001e703345,0x0,0xf316e66003ea6f31704c0f301e6f379f99e7e7f53001e9cc01e6f3001e6003ccf303ccf3003cde7033d5,0x0,0xf32634c00f4e6f3079801e601e6f37a731e7e9db3001e9cc01e6f3001e600799e603ccf300799e7038e5,0x0,0x0,0x400021001000084000000008010000000002002000008000000010020000020000004000010010000040040000080100000080400000101000000404000000800000001001087fea7,0x0,0x42000100100008400010000801000080000200200000800000001002000002008000400000201000000804000008010000008040000010108000040400000080020000100108732a7,0x0,0x1e9cc00f4e6001e9cc0088b00f33cc0007d4cf30408fcc1e60f3003cc3ce049db379800f31e6906146,0xf6d3b663cc1e6fa9fd4c0f30000f379801e7e60f3001e9cc01e6f3001e60f300f3f300f31e601e7033d5],
[0x1e9cc007a73001e9cc007d4c079bcc0007d4cf3003cfcc2d90f3003cc1e7e63d39f9801e60f3812d56,0x0,0x1e9cc00f4e6001e9cc007d4c7983cc0007d4cf3003cfcc1e60f3003cc799e607987980798f30812de6,0xf307b660001e6f307d4c0f30000f379801e7e60f3001e9cc01e6f3001e679800fa9800f3f3001e7033d5,0x1e9cc00f4e6001e9cc007d4c7983cc0007d4cf3003cfcc1e60f3003ccf31e607987980f30f30812de6,0x221090240481,0x0,0x621081240481,0x1e679801e7e60079bcfd49a30001023001e9cc0044e30f83db3000f6cfcc1ea54b07983cc0001e61df6,0x621081240481,0x0,0x421002240481,0x21000240481,0x421002240481,0x21004240481,0x21004240481,0x21000240481,0x21004240481,0x21004240481,0x421008240481,0x21000240481,0x421008240481,0x21004240481,0x221090240481,0x0,0x0,0x1e67980799e600f33cfd49a30001023003cfcc0044e30f83cc0000f6cfcc1ea54b07983cc0001e61df6,0x0,0x0,0x621082240481,0x421000240481,0x621082240481],
[0x421004240481,0x421004240481,0x421000240481,0x421004240481,0x421004240481,0x421008240481,0x421000240481,0x421008240481,0x421004240481,0x421010240481,0x21010240481,0x421010240481,0x421010240481,0x821090240481,0x21010240481,0x821090240481,0x421010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_6568 : TreeBound (n := 4) 107 (programCode 0x4e29076c5c) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8008200201020040408028200208048200205104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_6569 : TreeBound (n := 4) 107 (programCode 0x4e29076c5d) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x16c8000f301e616c8811801ed980079f99e8e83001e9cc01e6f3001e9cc001023000408c001e7032b5,0x880022000100804080082002080402000000e4,0x16c80007985b225f8fa9801ed980079f99e7f53001e9cc01e6f3001e9cc0010230007d4c001e703345,0x0,0x445a22c0007984459ed9801ed9879f9f99e7e600f4e600f4e6000f4e9cc001f530007d4c001e703855,0x0,0x25f92fc0003cc25f8fa9801ed9879f9f99e7e601e7e6007b66001e7e9cc001f530007d4c001e703855,0x0,0x2b3fb00000000ad145fd815a0034bd9ff1fd80ad145fd815a0033fb00acfec0567f600000acfec0000002b3fb000000002b3fb0c2f671731fd8002b3fb159fd800acfec159fd80000000000acfed59fd802b3fb567f60002b3fb567f600159fdab3fb000159fdab3fb000159fdab4109fd8000015a53ff6000005694ffd8000015a53ff6000005694ffd8000015a53ff600000159ff312bf5a596ab,0x122902241502,0x840042000100804000080002080002000000a4,0x122902241502,0x1221042410e2,0x1221042410e2,0x0,0x1221042410e2,0x600030000800000006000080004000000020003000020000000100000000100000002000010002000010010000080010000080400000101000000404000001010000001001087f7a7,0xf307983cc00000000001e61e603cc0000798000f3007980000f300001e9cc003db3000f6cc001e68a925,0x3cc7983cc07983cc798079879879897e0799e603cc01e6f301e63cc01e9cc001f530007d4c001eacf855,0xf307983cc00000000001e61e603cc0000798000f3007980000f300001e9cc003db3000f6cc001e68a925,0x1f457943cfdb3079801e63cb10cc01e6798000f30079bcc00f3f3001e9cc003db3000f6cc001e6c7525,0x2080082010100804080182002080402002432e4,0x7a73001e61e60fb966b981e6798079879a4ba03001e9cc01e6f3001e9cc001023000408c001e7032b5,0x4080102030100804080182002080402006834e4,0x422010240481,0x2010240481,0x422010240481,0x2010240481,0x842110240501,0x2010240481,0x842110240501],
[0x2010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_6602 : TreeBound (n := 4) 107 (programCode 0x4e29076c5e) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x80082002020100804080082002080402004030e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_6603 : TreeBound (n := 4) 107 (programCode 0x4e29076c5f) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x16c8000f3079816c888b001e7e6007a731e7f53001e9cc01e6f3001e9cc001f53000408c001e7037c5,0x0,0x3d714443cc1e7473944b981e61e6b145332c5203001e9cc01e6f3001e6003ccf303cc3cc03cde7032b5,0x422010210481,0xf3b10783cc1e73fa107f981e63ccb108732c42d3001e9cc01e6f3001e6003ccf301e67980799e703345,0x0,0x422010208481,0x880022002100084080082002002400080432e4,0x422010208481,0x880022004100104080002002004400100804e4,0x422010210481,0x422010210481,0x422010210481,0x422010210481,0x422010220481,0x422010200481,0x422010220481,0x422010220481,0x16c80003cc1e625f8fa9801e7e6003db31e8e83001e9cc01e6f3001e9cc001023000408c001e7032b5,0x0,0xf307980003cc2d916c8811801e7e679fa731e7f53001e9cc01e6f3001e6003ccf303cc3cc03cde7032b5,0x1080042000900024080006002000c00020100e4,0xf307980003cc2d925f8fa9801e7e679bdb31e8e83001e9cc01e6f3001e6003ccf300f33cc0799e7032b5,0x0,0x0,0x1080042002100084080082002002400080432e4,0x0,0x1080042004100104080002002004400100804e4,0x1080042000100004080002002000400400000e4,0x108004201020040408028200201048820205104,0x1080042000100004080002002000400040000e4],
[0x108004201020040408028200201048840205104,0x0,0x1080042020100804080082002020400804030e4,0x1080042000100004080002002000400000000e4,0x1080042040101004080082002040401008070e4,0x40200000801000001000080001098280400000801000040004000020020009ca840000020100000400400000801000000804000000210000000840000002100000010031840ca7,0x0,0x402030992006100180084002108001200080ca3,0xf3079800000000000001e61e607980000f30001023079c08c0f307981e9cc003db3000f6cc001e68a925,0x2010389e2005100140084004108001200080ea3,0x0,0x422002240481,0x2000240481,0x422002240481,0x2008240481,0x2004240481,0x2000240481,0x2004240481,0x2000240481,0x2008240481,0x2000240481,0x2008240481,0x2000240481,0x7a73003cc1e60fd789f981e63cc0798f32c42d3001e9cc01e6f3001e9cc0010230007d4c001e703345,0x0,0x0,0xf33cc03ccf300f33cc00f6cc00408c000f6cc000f6cc00f300000f6cfcc0000f307983cc0007985216,0x0,0x0,0xa521c2240501,0x842108240501,0xa521c2240501],
[0x842108240501,0x842104240501,0x842108240501,0x842104240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x422010240481,0x2010240481,0x422010240481,0x2010240481,0x842110240501,0x2010240481,0x842110240501,0x2010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_6684 : TreeBound (n := 4) 107 (programCode 0x4e29076c60) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x80082002040101004080082002080402008070e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_5820 : TreeBound (n := 4) 107 (programCode 0x4e29076c) := by
  conv in programCode _ => reduce
  exact branchFour (k := (2,1)) (by decide +kernel) part003_5821 part003_5870 part003_5951 part003_6096 part003_6305 part003_6354 part003_6355 part003_6484 part003_6485 part003_6486 part003_6487 part003_6568 part003_6569 part003_6602 part003_6603 part003_6684

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_6685 : TreeBound (n := 4) 107 (programCode 0x4e29076d) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 4)
    (a := List.flatten [
[0x8010200408040200408004200108002200082ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_6686 : TreeBound (n := 4) 107 (programCode 0x4e29076e) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 4)
    (a := List.flatten [
[0x0,0x1340d0240481,0x120002408020200408060200408040a00010104,0x1340d0240481,0x0,0x408c0010230001f533cc0f30f303cc3cc03ccf348243cc1e600000f33cc1e688b00003cc0003cc3cb6,0x0,0x7340c6204481,0x1f5300088b0001f533cc03ccf303cc3cc03cc00102300111600010230005b20003cc07983cc3cc33b6,0x7340c6204481,0x8000200000004020100002000080ce3,0x404004208481,0x404004200481,0x404004208481,0x0,0x1f5300088b0001f533cc03ccf303cc3cc03cc00102300111600010230799e60f300f30798003ea93b6,0x1f5300088b0001f533cc03ccf303cc3cc03cc001023001116000102300f4e600f301e60f3003ee5fb6,0x1f5300088b0001f533cc03ccf303cc3cc03cc001023001116000102300097e0f30000f307983cc33b6,0x1f5300088b0001f533cc03ccf303cc3cc03cc001023001116000102301e7e6007983cc1e60046babb6,0x404004220481,0x404004200481,0x404004220481,0x8000200000004020100002000080ce3,0x0,0x1340c1204481,0x0,0x1340c1204481,0x1340c1204481,0x1340c1208481,0x4002a1940000a02000000800400002000040002194100000200400000041000000000002010000008020000008080000020080432800100040000400008000400000001001087f9a7,0x1340c1208481,0x408c00088b0001f533cc0f30f303cc3cc03ccf4f1640001e6000f3f3007b6a458f300003cc03cc3c26],
[0x0,0x0,0x0,0x0,0x1340c1220481,0x4002a1320000a02000000000400001000040002132100000200400000041000000000002010000008020000004080000020080426400100040000400008000200000001001087f8a7,0x1340c1220481,0x408c00088b0001f533cc0f30f303cc3cc03cda9a68400097e03cc0f31e63533a0c1e70230004827c26,0x0,0x1340c1204481,0x0,0x1340c1204481,0x4000200481,0x4000208481,0x4000200481,0x4000208481,0x0,0x0,0x1f5300088b0001f533cc03ccf303cc3cc03cc001f5300097e0001f5300f4e600f307980f3003f9c3b6,0x0,0x1f5300088b0001f533cc03ccf303cc3cc03cc001f5300097e0001f5301e7e6007983cc1e60046babb6,0x4000220481,0x4000200481,0x4000220481,0x4000200481,0xf4ee11bd398f300f3003cc2046f3003cfcc000001e679803ccf300799e9cc003db3000f6cc001e68a925,0xf307983cc00000000003cc1e60f300003cc0000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0,0x3340c2204481,0x0,0x3340c2204481,0x224082208481],
[0x224082208481,0x402021001008000000000008000040000040002100100000000400000801000000000020010000080020000100080000200080420000100040000400100000800000001001087faa7,0x224082208481,0x0,0x0,0x408c0010230001f533cc0f30f303cc3cc03cd02782403cde60001f5303ce04da7307980f300454ecb6,0x0,0x408c0010230001f533cc0f30f303cc3cc03cd02782403cde60001f5303ce04da7307981e600454ecb6,0x224082220481,0x408c0010230001f533cc0f30f303cc3cc03cd6cc8241e61e60001f531e62d981183cc079800445bcb6,0x224082220481,0x408c00088b0001f533cc0f30f303cc3cc03cd6cc8240f397e0001f531e62d97d4c1e70230004827c26,0x0,0x0,0x0,0x0,0x1100044001100044004020104080022000a05e4,0x1421024406c2,0x1409024406c2,0x900044002100144002010104080012000a27a4,0x1409024406c2,0x1421024406c2,0x1411024406c2,0x0,0x1411024406c2,0x900044002100944002110104080012000a27a4,0x1421024406c2,0x0,0x1421024406c2,0x1023798408c0000798003cc1e60f300003cc00000f307981e60f303cc1e9cc003db3000f6cc001e68a925,0x0,0x1041e11c1058f3088b000011346001e9cc003cc10416798222cf300001e9cc003db3000f6cc001e68a925],
[0xf307983cc0000000000408de6102300001e6000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0,0xf307983cc00000000003cc1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925,0x1421044412a2,0x1409044406c2,0x1023798408c000079800007b66001e600003cc0102307981e60f300001e9cc003db3000f6cc001e68a925,0x1409044406c2,0x1421044412a2,0x141104440ae2,0xf307983cc000000000003cde600f300001e6000f3007980000f300001e9cc003db3000f6cc001e68a925,0x141104440ae2,0x1100044020100804008100204080102000221e4,0x1421044412a2,0xf307983cc00000000001e61e607980000f30000f3007980000f300001e9cc003db3000f6cc001e68a925,0x1421044412a2,0x0,0x5340c4204481,0x0,0x5340c4204481,0x0,0x404004208481,0x404004200481,0x404004208481,0x0,0x0,0x408c0010230001f533cc0f30f303cc3cc03ccf348243cc1e60001f5303ce04da7307980f300454ecb6,0x0,0x408c0010230001f533cc0f30f303cc3cc03ccf348243cc1e60001f5303ce04da7307981e600454ecb6,0x404004220481,0x404004200481,0x404004220481,0x408c0010230001f533cc0f30f303cc3cc03ccf348243cc1e60001f531e62d981183cc0f3000445bcb6],
[0x0,0x0,0x0,0x0,0xf307983cc00000000003cc1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925,0x1421044412a2,0x1409044406c2,0x900044000100044008000404080002000201a4,0x1409044406c2,0x1421044412a2,0x141104440ae2,0x0,0x141104440ae2,0x900044000100844008100404080002004221a4,0x1421044412a2,0x0,0x1421044412a2,0x16c87985b200003cc0003cc1e60f300003cc00007980798f300f31e601e9cc003db3000f6cc001e68a925,0xf307983cc00000000003cc1e60f300003cc0000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0,0x9340c8204481,0x0,0x9340c8204481,0x804008220481,0x804008208481,0x804008200481,0x804008208481,0x0,0x0,0x408c0010230001f533cc0f30f303cc3cc03cc0f782403cde60001f5303ce04da7307980f300454ecb6,0x0,0x408c0010230001f533cc0f30f303cc3cc03cc0f782403cde60001f5303ce04da7307981e600454ecb6],
[0x804008220481,0x804008200481,0x804008220481,0x804008220481,0xf307983cc00000000003cc1e60f300003cc0000f3007980000f300001e9cc003db3000f6cc001e68a925,0x224090240481,0x420008408020200408060200408042200042304,0x224090240481,0x0,0xf344e0ecc001e600f4e6011382c00f379803d3a730079bcc007a73001e9cc003db3000f6cc001e64dcf5,0x1023798408c000079800408de6102300001e6000f30079bcc00f3f3001e9cc003db3000f6cc001e68a925,0x0,0x0,0x2010000008008000020080000020080040021000100000800400008000000408000002301100001080000010000000010800400020111000000004000200010000001000087f3a8,0x0,0x0,0x3304c2240481,0x7304c6240481,0x3304c2240481,0x0,0x1304c4240481,0x7304c6240481,0x1304c4240481,0x1e7e60079f9800f3f33cc07990231e603cc3cc0f397e03cc7980798f33cc1e60f30820ecc001e9dcf76,0x1304c8240481,0x7304c6240481,0x1304c8240481,0x1e7e60079f9800f3f33cc07996c81e61e603cc79897e1e607983cc0f33cc003db307a76cc001e9dcf76,0x0,0x1e9cc0079bcc00f3f30010230003db30007d4d6e71736cc00000000f33cc2dcdb300003cc001e6110f6,0x0,0x0],
[0x0,0x24050a5414c2,0x2405025404c2,0x2405025404c2,0x2405025404c2,0x24050a5414c2,0xf307983cc00000000003cc1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0,0xf307983cc00000000003cc1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925,0x24050a5414c2,0x2405085414c2,0x2405025404c2,0x2405085414c2,0xf4ee11bcc0079807980007b84600799e601e600f30079bcc007a73001e9cc003db3000f6cc001e64dcf5,0x4100104002100084080102004080402000824e4,0xf4ee11bcc007980f300007b84601e61e603cc00f30079bcc007a73001e9cc003db3000f6cc001e64dcf5,0x4100104004100104080002004080402000804e4,0x4100104020100804080102004080402000824e4,0x4100104008100204080102004080402000824e4,0x10237983cc000007980003cde600f300001e6000f30079bcc007a73001e9cc003db3000f6cc001e64dcf5,0x4100104010100404080102004080402000824e4,0x4100104020100804080102004080402000824e4,0x4100104020100804080102004080402000824e4,0x16c87983cc00003cc0001e61e607980000f30000f30079bcc007a73001e9cc003db3000f6cc001e64dcf5,0x4100104040101004080102004080402000824e4,0x404010240481,0x1020020408020200408060200408048200102904,0x404010240481,0x1020040408020200408060200408048200205104,0x804010240481,0x4010240481,0x804010240481],
[0x4010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_6911 : TreeBound (n := 4) 107 (programCode 0x4e29076f) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 4)
    (a := List.flatten [
[0x8020200808040200808004200108002200084ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_6913 : TreeBound (n := 4) 107 (programCode 0x4e29077071) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x10c050204481,0x16c8000f4e60016c83cc0000f30007d4c1e60f3001e9cc01e6f3001e63cc01e6000079bcc01e703855,0x10c050204481,0x0,0x10c041204481,0x80002008002200000004020100002000080ce3,0x10c041204481,0x104040200481,0x1140c2208481,0x80002008002200000004000100002000080ce3,0x1140c2208481,0x0,0x16c8000f4e60016c83cc0000f30007d4c1e6003cc1e63cc1e603cc1e63cc01f5300079bcc01e703855,0x0,0x16c8000f3f30016c83cc001f530007d4c1e6007981e61e61e607981e61e601f53000799e601e703855,0x0,0x14c168224501,0x82002088002200100404020100402010080ce3,0x14c168224501,0x104040200481,0x16c83cc1e60f307981e63cc0f30f303cc3cc03ccf30b643cc1e60f301e65b22d90f307981e60f30799e56,0x80002008002200008004200108002000080ce3,0x16c8000f31e6016d3a0c01e6f30007d4c20ee03001e9cc01e6f3001e601e60f307983cc3cc1e7032b5,0x0,0x80402010082002088004200108002002080ce3,0x84002108002020008004200108002020080ce3,0x16c8000f303cc16c8000799e601e6798097e0f3001e9cc01e6f3001e600799f530007980799e703855,0x0,0x16c83cc1e60f307981e65b20f30f303cc1e603ccf30b643cc0f30f301e6007c59001ed98003db30799e56,0x80002008002000008004200108002000080ce3,0x16c8000f31e6016c8003cde600f307983ea60f3001e9cc01e6f3001e603cc1f530007983cc1e703855],
[0x80002008002000008004200108002000080ce3,0x84002100802020008004200108002020080ce3,0x84002100002020008004200108002020080ce3,0x88002201002040088004200108002040080ce3,0x44580007980000f303cc1e9db300079800000f30079bcc00f3f3001e9cc003db3000f300001e68a925,0x90002412002080498004200108002080082ce3,0x80002000402000008004200108002000080ce3,0xa0002814002100888004200108002100084ce3,0x80002000002000008004200108002000080ce3,0x16c83cc1e60f307981e63cc0f30f303cc3cc03ccf30b643cc1e60f301e65b22d90f307980f30f30799e56,0x450e4007980000f303cc1ebc130007d4c0000f30079bcc00f3f3001ea27203dba980f300001e68a925,0x16c8000f3f30017235cc001f530007d4c1e8e83001e9cc01e6f3001e60f300f33cc03cde601e7032b5,0x44580007980000f303cc1e9db30007d4c0000f30079bcc00f3f3001e9cc003db3000f300001e68a925,0x14c170220501,0x80002008002200008004200100402000080ce3,0x14c170220501,0x104050200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_6962 : TreeBound (n := 4) 107 (programCode 0x4e29077072) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x40002000001008000400000002050080000000600000001001000012004000018000400000201000000804000008010000008040000010100000010400000101000000100108713a7,0x0,0x0,0x421010210481,0x0,0x0,0x421010208481,0x210000000110000001100000001100000021000000010800000108000000108004000301310000100040000000900001000002020110001000080010200000010000228057d3a8,0x421010208481,0x210000000110000001100000001100000021000000010800000108000000108004000301510000100040000000900001000002020110002000100020200000020000200097d3a8,0x421010210481,0x421010200481,0x421010210481,0x421010210481,0x421010220481,0x421010200481,0x421010220481,0x421010210481,0x0,0x0,0x0,0x0,0x0,0xf3012fcf3005c5039c4583cde60261df809878d3001e9cc01e6f3001e601e60f31e607981e61e703345,0x426021114080084404220000020400844400022110000010010000200040000284404000010010000040040000080100000080422000100002000084000001010880001001087cfa7,0xf30079bcc005c503a01183cde60267918099e553001e9cc01e6f3001e601e60f30f307983cc1e703345,0x0,0x0,0x360f9c00000000000000002c9d1bfe55b6043b8b9fd80159fd8567f60000ad0019fd80000000000acfec0000000acfed59fd8000b7ea1fed3800567f759fd80002b40067f60000acfec0159fd800159fdd67f6000159fed9fd8000567fb67f6000159fed9fd80002b40067f600002b3fb002b3fb0159fd82b3fb015a1356bfda70159fe2cfec000acfec00acfec0567f6000000015a0095f98ac2c5ab,0x0,0x0],
[0xd685f0220501,0x436c21b760100820840480000204008011000221b6000010010000040040000282084000010010000040040000080100000080436c00100002000080008000210410001001087cca7,0xd685f0220501,0x0,0x0,0x4000200000100800040000000a050080004000200000001001040002004000058000000040200000100800001008000001008040000010100000010400000101000000100108713a7,0x0,0x0,0x0,0x0,0xa00028001100044002010088080012000542e4,0x0,0xa00028001100044004020108080022000904e4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x16bc270ad8ce01691dada061ce0016a59801dfe70005af09c2b633800016bc270ad8ce0016bc270ad8ce00016bc270ad8ce000005a3c254c8c90fd0451cd0f43a8baa5e0077f9c005a52b2ec95413c23e3f63c23e39c005a966007853fc23e3f63c23e39c0016bc270ad8ce0168f08f8e700000175a104a5b9747cd08e0510d2459b91cbc270ad8ce0017438140ae3800016bc270b330a23e39c0000168f08f99b7847ccdbc23e66de122055028167b7847ccdbc23e39c000b5e13856d1b7847ccdbc23e39c0000b4784828b88f9b436e,0x0,0x0,0x142108440222,0x1421024406c2,0x0,0x1421024406c2,0x142108440222,0x1421044412a2],
[0x0,0x1421044412a2,0x15f657600000adabbec0000001853d3000000057d95d80000057d95d800000057d95d800000002b3fb00000ae58bd8000002b4263fb159fd800acfec567f600acfec206fc400acfec567f600567f600000c29e980000002b6aefb0159fd80159fd8000030d2e5b0206fc40159fd959fd80000000567f602b3fb0159fd80acfec0567f600000057d95d80000016a3562000000614f4c324339a0ac,0x142108440222,0x0,0x142108440222,0xa00028002100084080202008080402000100e4,0x40002000001008000400000040050080000020200000020020000202080000208000400000201000000804000008010000008040000010100000010400000101000000100108713a7,0xa00028004100104080002008080402000100e4,0xa00028040101004080202008080402000100e4,0xa00028008100204080102008080402000100e4,0x0,0x0,0x421010210481,0x0,0x0,0x421010208481,0x210000000110000001100000001100040221000000010800000408000000108004000341390000100040000000900001000002020138001000080010200000010000228057d3a8,0x421010208481,0x210000000110000001100000001100040221000000010800000808000000108004000301590000100040000000900001000002020150002000100020200000020000200097d3a8,0x421010210481,0x421010200481,0x421010210481,0x421010210481,0x421010220481,0x421010200481,0x421010220481,0x421010210481,0xa00028010100404080102008080402000100e4,0x16a59801dfe7001691dada061ce0016a59801dfe70005af09c2b63380016a59801dfe700016bc270ad8ce00016bc270aef5d08f9413c23fa2b096a0c69006d4e76c61d02f95ef9c005a52b2ec964ff08f9413c23e39c0005a966007853fc23e3f63c254c8c8f8fd8f08fe8ac23e39c0000168f08f9ea6ceaba5da9227ede12d4cd4a4895d8f08fe8ac23e4507847ddc708f8e9d1e124c0a23e39c0000168f08f99b7847ccdbc23e66de12d4cd4a489fb7847ccdbc23e39c000b5e13856d1b7847ccdbc23e39c0000b478482970b6c2074e,0xa00028020100804080202008080402000100e4,0x40002000001008000400004000050080002000200002000100020002400020008000400000201000000804000008010000008040000010100000010400000101000000100908713a7],
[0xa00028040101004080202008080402000100e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_7059 : TreeBound (n := 4) 107 (programCode 0x4e29077073) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x10c050204481,0x100004008002200008004200100002020080ce3,0x10c050204481,0x0,0x10c041204481,0x100004008002200000004020100002000080ce3,0x10c041204481,0x104040200481,0x1140c2208481,0x100004008002200000004000100002000080ce3,0x1140c2208481,0x0,0x0,0x0,0x0,0x0,0x14c168224501,0x102004088002200100404020100402010080ce3,0x14c168224501,0x104040200481,0x0,0x11c0c1208481,0x600000001020000008008000028288400001001000004004000000410000849000400020004000400024000800050000800004000200080000800100004000100010030840da7,0x11c0c1208481,0x1140c0208481,0x1140c2208481,0x6000000010400000040080000286984000000010000040040000002100008690000000200080004004348008010d2000800004000200080000800100002000100010030840ca7,0x1140c2208481,0x0,0x600000001040000004008000028088400000001000004004000000210000809000400020008000400010000800010000800004000200080000800100002000100010030840ca7,0x6000000010200000080080000286984000010010000040040000004100008690020000200040004004000008010d2000800004000200080000800100004000100010030840da7],
[0xa00200008040000004008000028108400000041000004004000000210000809800800020008000400004000800020000800004000400080004000100002000100010030853ca7,0x0,0x15c1e8208501,0x6000000010400000040080000286984000000010000040040000002100008690000000200080004000004008010d2000800004000200080000800100002000100010030840ca7,0x15c1e8208501,0x1140c2208481,0x0,0xf31e603cde60269de0401e6f3000408c20ed100f4e600f4e6000f4e63cc00f30f3040dda21e7032b5,0x100004008002200000004020100002000080ce3,0x1020040a8002200180104004100402030080ce3,0x100004008002200000004000100002000080ce3,0x16c83cc1e60f316c81e63cc0f30f303cc3cc03cd6c8b641e61e607981e6007c59001f164001f530799e56,0x100004008002200000004000100002000080ce3,0x16c80003ea600269b80c0000f3000408c20dde0799e601e7e600f31e600000f3f30040dbbc1e7032b5,0x0,0x100004008002200000804020100002000080ce3,0xf301e600f3798f301e63cc03ccf303cc3cc03cc03cde603cde6003cde6002046001ed98001e679df0156,0xf6cc00799e6026b614c01e6f30007d4c206463cc1e61e61e607981e63cc00f30f307d8c8c1e703345,0xf301e601e6798f301e63cc03ccf303cc3cc03cc0799e601e7e600799e6002046001ed98001e6f3bded56,0x100004008002200002004080100002000080ce3,0x44e0b00f300001e603cc2083b3000f6cc0001041679807987980001ea10583cc0000f300001e64dcf5,0x100004008002200004004100100002000080ce3,0x100004008002200000004000100002000080ce3,0x16c8000799e6025ffd4c01e6f30007d4c206553001e9cc01e6f3001e601e60f30f307983cc1e703345,0x0,0x0,0x0,0x100004008002200000104004100002200080ce3,0x0,0x101004048002200100204008100202200080ce3,0x100004008002200000004000100002200080ce3,0x102004088002200100404010100402200080ce3],
[0x0,0x0,0xf301e603cc798f301e63cc03ccf303cc3cc03cc03cde603cde6003cde6003ea6000fa98003cde66a6556,0x0,0xf301e601e6798f301e63cc03ccf303cc3cc03cc0799e601e7e600799e6003ea6000fa98003ccf3bded56,0x100804028002200082004080100102200080ce3,0x44e0b00f300001e603cc2083b3000f6cc0001041679807987980001ea10583cc0000f6cc001e64dcf5,0x100804028002200084004100100102200080ce3,0x100004008002200000004000100002200080ce3,0x16c80003ea60026169cc0000f3000408c1e7f53001e9cc01e6f3001e60f300f3f3003ccf301e7032b5,0x0,0x16c80003cde60269bbd83ea6003cc3cc05d9ed3001e9cc01e6f3001e60f300f30f3040dda21e7032b5,0x100004000002020008004200100002020080ce3,0x16c8000799e6026799183ea6001e6798099e553001e9cc01e6f3001e63cc00f30f307d8c8c1e703345,0x0,0x16c83cc1e60f316c81e65b20f30f303cc1e603ccf30b643cc0f30f301e603ced900f379800f3f30799e56,0x2202008002100084080202008008400200442e4,0xf33cc03ea600269b441e600007983cc3ecded3001e9cc01e6f3001e60f300f3f30040dbbc1e7032b5,0x4202008004100104080002008008400200804e4,0x100004000802020008004200100002020080ce3,0x100004000002020008004200100002020080ce3,0x16c8000799e6026d438f31e607980799e806553001e9cc01e6f3001e63cc00f30f307d8c8c1e703345,0xf301e601e6798fa99e601e63cc079bcc01e63ccf301e63cc0f30f301e600f4e600f379800f30f3bded56,0x100004002002080008004200100002020080ce3,0x104004000402000008004200100802020080ce3,0x80004912001100088004200100001122080ca3,0x100004000002000008004200100002020080ce3,0x16c80007a73002634fcc001f530007d4c1e7f53001e9cc01e6f3001e60f300f37980799e601e703345,0x0,0xf301e61e60798f301e63cc03cc7983cc4bf03ccf301e63cc25f8f301e601e8d90079f9801e6f30b65556,0xa02428000900024080086008010400402170e4,0x100004000102004008004200100002200080ce3],
[0x0,0x0,0x2202008002100084080202008010400400442e4,0x0,0x4202008004100104080002008010400400804e4,0x104004100802020008004200100802200080ce3,0x104004100002020008004200100802200080ce3,0x108004201002040088004200101002200080ce3,0xf301e601e6798fa99e601e63cc079bcc01e63ccf301e63cc0f30f301e601e7e60079f9801e60f3bded56,0x100804022002080088004200100102200080ce3,0x20202008020100804080202008010400404060e4,0x100804024002100088004200100102200080ce3,0x100004000002000008004200100002200080ce3,0x14c170220501,0x16c8000799e60267954c01e6f30007d4c206553001e9cc01e6f3001e63cc00f30f307d8c8c1e703345,0x14c170220501,0x104050200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_7172 : TreeBound (n := 4) 107 (programCode 0x4e29077074) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x10c041204481,0x0,0x10c041204481,0x10c041204481,0x11c0c1208481,0x80002008002200000084002100402000080ce3,0x11c0c1208481,0x0,0x0,0x108000000420000002100000002100040000800100002000400008001000008001000200014404a0000400200000002100001000000404008202010000800010000041102eaba8,0x40002000000018000400000400000580004000200010000001040000004100008000000040200000100800001008000001008002000010002000010020000100020000100108713a7,0x201000000000000040200000000000000402000000000000008040000000000000402000000000000008040000000000000100800000000000001008000002000000004000000080000000020000002000000002000000080000000100000002000000002000000080000000020000002000000000400000080000000004000000800000010000000000000000200000002c0600141200000002000000040000000240000001200000002000000004000000008000001000000000000000800800000000200000000000000040000040000000000400001003000a000080000000000200004000000000001000080000400000000001000000010000000010000000000020000001333776cd6c6d30,0x14c161220501,0x2008002200000084002100401000080ca3,0x14c161220501,0x104041200481,0x0,0x82410098006200180404020100082002080ce3,0x204600081180020463cc03ccf303cc3cc03cc00111600111600011160005b20003cc07983cc3cc33b6,0x1028100a8006200180404020100102004080ce3,0x8000200000004020100002000080ce3,0x0,0x8000200000004020100002000080ce3,0x0,0x0,0x204600081180020463cc03ccf303cc3cc03cc00111600111600011160f31e60f301e60f3000408f3b6,0x204600102300020463cc0798f301e63cc03cc0025f8000a71000111601e60f3079ff413f3008562c26,0x204600081180020463cc03ccf303cc3cc03cc001116001116000111600097e0f30000f307983cc33b6,0x204600102300020463cc0798f301e63cc03cc0025f8000a71000111601e61e60f384f34e60085dc426,0x8000200000004020102002080080ce3],
[0x8000200000004020100002000080ce3,0x8000200000004020104002100080ce3,0x8000200000004020100002000080ce3,0x0,0x10c041204481,0x4002a1334000280004000008000001800040002132100000000400000041000080000002010000008040000004080000020080426400100010000400000000200400001001087fca7,0x10c041204481,0x10c041204481,0x11c0c1208481,0x4002a1954000a00110000800400002000040002194100000210400000041000000000002010000008020000008080000020080432800100042000400008000400000001001087f9a7,0x11c0c1208481,0x408c00081180020463cc0f30f303cc3cc03ccf4f1640001e6000f4e6007b6a458f300003cc03cc3c26,0x0,0x0,0x0,0x0,0x14c161220501,0x4002e1b76000a000000000000000010000400021b6100000000400000041000000000002010000008020000004080000020080436c00100000000400008000200000001001087f8a7,0x14c161220501,0x104041200481,0x0,0x10c041204481,0x0,0x10c041204481,0x4000200481,0x4000208481,0x4000200481,0x4000208481,0x0,0x0,0x204600102300020463cc0798f301e63cc03cc0025f8001209000204601e60f3079fd5b3f3008562c26,0x0],
[0x204600102300020463cc0798f301e63cc03cc0025f8001209000204601e60f30f381274e6008562c26,0x4000220481,0x4000200481,0x4000220481,0x4000200481,0xf4eda76d3981e60f3003cc2046f3003cfcc000001e679803ccf300799e9cc003db3000f6cc001e68a925,0xf307983cc00000000003cc1e60f300003cc0000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0,0x31c0c2204481,0x0,0x31c0c2204481,0x214082208481,0x214082208481,0x0,0x214082208481,0x210000000420000002100000002100040000800100002000400008001000008000000200010044a00000202000000081000002000000004080220020001000020000400027aba8,0x0,0x0,0x0,0x0,0x214082220481,0x0,0x214082220481,0x214082208481,0x0,0x0,0x0,0x0,0x1200048001100044004020108080022000a05e4,0x1421024406c2,0x1409024406c2,0x1200048004100144004020108080022000a05e4],
[0x1409024406c2,0x1421024406c2,0x1411024406c2,0x0,0x1411024406c2,0x1200048004101004004200108080022000245e4,0x1421024406c2,0x0,0x1421024406c2,0x0,0x40002000001008000400000002050080000000600000001001000012004000018000004000200010000800100008000100008040000010100000010400000101000000100108713a7,0x0,0x0,0x0,0x142108440222,0x140908440222,0x1023001023000204600003cc003db3000f6cc00000000000003cc1e63cc0000f3000222c0007984d36,0x140908440222,0x142108440222,0x141108440222,0x0,0x141108440222,0x2b962f600000ae58bd80000015cb17b00000015cb17b000000ae58bd8000000ae58bd80000000acfec567f6002b3fb000002b4a7fecaa4ad9f58d3b159fd8adabbec0acfec00acfed59fd80acfec0000000000000159fdabecaed64a22da47feacfed49602b3fb002b3fb0159fd959fd80000000567f602b3fb0159fd80000015f657602b3fba8f0c780acfec5be756000000159fd837bf39a0ac,0x142108440222,0x40002000001008000400004000050080002000200002000100020002400020008000004000200010000800100008000100008040000010100000010400000101000000100908713a7,0x142108440222,0x0,0x820001000080004000000400020001000022000000088000000040200000100804000010000020040000080020001000080400000041000000204000000810000001000485ee27,0xf307983cc0000000000408de6102300001e6000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0,0xf307983cc00000000003cc1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925,0x1421044412a2],
[0x1409044406c2,0x2046001023000204600003cc00408c000f6cc03cde603cc00003cde63cc0000f3000222c00079852a6,0x1409044406c2,0x1421044412a2,0x141104440ae2,0xf307983cc000000000003cde600f300001e6000f3007980000f300001e9cc003db3000f6cc001e68a925,0x141104440ae2,0x1200048040101004008200208080202000241e4,0x1421044412a2,0xf307983cc00000000001e61e607980000f30000f3007980000f300001e9cc003db3000f6cc001e68a925,0x1421044412a2,0x0,0x40002000008008000400000002080080000000600000001001000012000000018000020000200020000800200008000200008040000010100000010400000101000000100108713a7,0x0,0x0,0x0,0x0,0x0,0x0,0x900048002100104000000048080402000100a4,0x0,0x8400000021000000210000000210000100080000100080001000800001000800004002000000210000040020000002100040000020100000001400020201000000042c42593a8,0x0,0x8400000021000000210000000210000080080000200080002000800002000800008008000000210000200080000002100040000040100000001400021001000000043882593a8,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0],
[0xf307983cc00000000003cc1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925,0x1421044412a2,0x1409044406c2,0x1200048000100044010000408080002000201e4,0x1409044406c2,0x1421044412a2,0x141104440ae2,0x0,0x141104440ae2,0x1200048000101004010200408080002000201e4,0x1421044412a2,0x0,0x1421044412a2,0x0,0x94c168204501,0x0,0x94c168204501,0x844108220501,0x844108208501,0x844108220501,0x844108208501,0x0,0x0,0x108000000420000002100000002100040000800100002000400008001000008000100200014404a00000012000080001000010000800040082020100000080100000411026aba8,0x0,0x108000000420000002100000002100040000800100002000400008001000008000100200014404a00000012000080001000010000800040082020200000080200000411026aba8,0x844108220501,0x844108220501,0x844108220501,0x844108220501,0xf307983cc00000000003cc1e60f300003cc0000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0],
[0x94c168204501,0x8400000021000000210000000210004000080010000080040000800100000800000120000000a1000000120000000810000001000020001800000010000a000100040002593a8,0x94c168204501,0x844108220501,0x844108208501,0x844108220501,0x844108208501,0x0,0x0,0x0,0x0,0x0,0x844108220501,0x844108220501,0x844108220501,0x844108220501,0xf307983cc00000000003cc1e60f300003cc0000f3007980000f300001e9cc003db3000f6cc001e68a925]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_7381 : TreeBound (n := 4) 107 (programCode 0x4e29077075) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x81180079801e68118b64001f53001e9cc1ef7e00f4e600f4e6000f4e9cc001023000408c001e7032b5,0x811800799e60081183cc0000f3001e9cc1e600f301e9cc01e60f301e9cc001f530007d4c001e703855,0x81180079805b281192fc001f53001e9cc1ef7e00f4e6007b66001e7e9cc0010230007d4c001e703345,0x0,0x20c0c1204481,0x0,0x20c0c1204481,0x204080200481,0x204080208481,0x200008008004200000004000100002000080ce3,0x204080208481,0x0,0x0,0xf301e603cc7983cc1e63cc03ccf303cc3cc03cc00204600097e000204600f4e600f307980f31e66a6556,0x0,0xf301e601e67983cc1e63cc03ccf303cc3cc03cc00204600097e000204601e7e6007983cc1e60f3bded56,0x214082220481,0xf301e61e607983cc1e63cc03ccf303cc3cc03cc00204600097e00020460799e607983cc0798f30b65556,0x214082220481,0x204080200481,0x214082240481,0x200008008004200000004000108002200080ce3,0x214082240481,0x0,0x81180079801e681180003cde603cde6005b20000f4e9cc01e6000f4e9cc001f530007d4c001e703855,0xa405025414c2,0x81180079803cc8118000799e601e7e60097e0001e7e9cc01e6001e7e9cc001f530007d4c001e703855,0xa405025414c2,0x210882240481,0x221084240481,0x210882240481],
[0x200080240481,0x221084240481,0x221084240481,0x221084240481,0x200080240481,0x2521ca240501,0x221084240481,0x2521ca240501,0x200080240481,0x16c83cc1e60f307981e63cc0f30f303cc3cc03cd6c8b643cc1e603cc1e63cc2d90f303cc3cc0f30799e56,0x200008008004200008004000108002200080ce3,0x16c83cc1e60f307981e63cc0f30f303cc3cc03cd6c8b643cc1e607981e63cc2d90f30b643cc0f30799e56,0x1ed98003cc000079803cc2139f3001e9cc0000f30079bcc00f300001e9cc003db3000f6cc001e6c7525,0x2541c8240501,0x200008008004200000804000108002200080ce3,0x2541c8240501,0x204080240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_7430 : TreeBound (n := 4) 107 (programCode 0x4e29077076) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0xf307983cc00000000003cc1e60f300003cc0000f30079bcc007a73001e9cc003db3000f6cc001e64dcf5]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_7431 : TreeBound (n := 4) 107 (programCode 0x4e29077077) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0xfa98001e60798fa98b64001f530079bcc1ef7e00f4e600f4e6000f4e9cc001f53000408c001e7037c5,0x0,0x402010088004200100404020100082002080ce3,0x400010008004200000004020100002020080ce3,0x402010088004200100404020100102004080ce3,0x400010008004200000004020100002000080ce3,0x16c83cc1e60f307981e63cc0f30f303cc3cc03cc00482400111600011165b22d907983cc1e60f30799e56,0x400010008004200000004020100002000080ce3,0x8118001e7e600fb301cc0000f30079bcc1ed983cc1e63cc1e612fc1e601e60f307983cc3cc1e7032b5,0x0,0x400010008004200000004020100802020080ce3,0x1ee11807980000f3003cc2046f3001e9cc0001023079800007992fc1ea08c03db3000f300001e64dcf5,0x8118001e7e600fb301cc0000f30079bcc1ed983cc1e63cc1e705fc1e60f300f33cc03cde601e7032b5,0xf301e601e67980799e63cc03ccf303cc3cc03cc001116001116000111601e7e6007983cc1e60f3bded56,0x400010008004200000004020102002080080ce3,0x400010008004200000004020100802000080ce3,0x400010008004200000004020104002100080ce3,0x400010008004200000004020100002000080ce3,0x8118001e601e6fa992fc001f530079bcc1ee8b00f4e6003ea6001e7e9cc001023000408c001e7032b5,0x0,0x20c0c1204481,0x0,0x20c0c1204481,0x204080200481,0x204080208481,0x400010008004200000004000100002000080ce3,0x204080208481,0x0,0x0,0x1ed98007980000f3003cc2046f3001e9cc0000f30079800007a73001ea08c03db3000f300001e64dcf5,0x0],
[0xf301e601e67980799e63cc03ccf303cc3cc03cc00204600097e000204601e7e6007983cc1e60f3bded56,0x214082220481,0x1ed98007980000f3003cc2046f3001e9cc0000f30079800007a73001ea08c03cc3cc0f300001e64dcf5,0x214082220481,0x204080200481,0x214082240481,0x400010008004200000004000108002200080ce3,0x214082240481,0x0,0x0,0x2405025404c2,0x0,0x2405025404c2,0x210882240481,0x221084240481,0x210882240481,0x200080240481,0x221084240481,0x221084240481,0x221084240481,0x200080240481,0x2521ca240501,0x221084240481,0x2521ca240501,0x200080240481,0x8118001e7e600fab69cc0000f30079bcc1ed983cc1e63cc1e603cc1e9cc001023000408c001e7032b5,0x0,0x402010080084002100404020108002200080ce3,0xf301e60004458001116000408c00408c000408c03cde603cde61e9cde63cc1e60f30000b640001e61556,0x402010080104004100404020108002200080ce3,0xf301e600081180020460007d4c00222c0007d4c03cde603cc003cfcde63cc1e60f300012fc0003cc33b6,0x230884240481],
[0x221084240481,0x230884240481,0x220084240481,0x221084240481,0x221084240481,0x221084240481,0x220084240481,0x2721ce240501,0x221084240481,0x2721ce240501,0x221084240481,0x8118003ccf300fad4fcc01e6f30079bcc20bf83cc1e61e61e607981e9cc0010230007d4c001e703345,0x0,0x0,0x0,0x0,0xf301e600081180020460007d4c00222c0007d4c0799e601e6003d399e63cc1e60f300012fc0003cc33b6,0x210882240481,0x221084240481,0x210882240481,0x200080240481,0x221084240481,0x221084240481,0x221084240481,0x200080240481,0x2521ca240501,0x221084240481,0x2521ca240501,0x200080240481,0x2541c8240501,0x8118001e7e600fab69cc0000f30079bcc1ed980001e63cc1e6f6cc1e9cc001023000408c001e7032b5,0x2541c8240501],
[0x204080240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_7528 : TreeBound (n := 4) 107 (programCode 0x4e29077078) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0xf3445a22c0001e60f30799119cc00f379803cdf530079bcc007a73001e600f33cc00f3f3003cde64dcf5,0xf4e6007a73000f4e63d767cc01e9cc6a503ccf301e63cc3528f301e60005b7b2044580003cfd783be6,0x0,0x0,0x400220100000880004000000200001000000022110000080080000100040000100004000010010000040040000080100000080002000100008000400010001000010001001487ffa7,0xf344e2d2c0000000f300011382c00f379803cc0f30079bcc007a73001ea10583db3000f300001e64dcf5,0x40002000000018000400000040000180000000600000001020000010004000018000400000201000000804000008010000008000200010000200010002000100002000100108713a7,0xf3445a22c0001e60f30799119cc00f379803cdf530079bcc007a73001e9ccf33db3000f3003cde64dcf5,0xf344d3a2c0079800f4ed99119cc00f379803cdf530079bcc007a73001e63cc03cc3cc0f30f301e64dcf5,0xf345094440079800f4ed99141aa00f379803cdf530079bcc007a73001ea23543cc0f30f30f301e64dcf5,0xf344d3a2c00f3000f6d399119cc00f379803cdf530079bcc007a73001e63cc03ccf300f31e601e64dcf5,0xf344583cc7980000f30001119cc01e679803cc0f30079bcc00f3f3001e9cc003db3000f300001e68a925,0xf3482622c03cc00102379920d4580f3798040ad390079bcc007a73001e7e6003cde600f379801e833cf5,0xf344e2d2c0000000f300011382c00f379803cc0f30079bcc007a73001ea10583cc0f30f300001e64dcf5,0x40002000000018000400004000000180000000600000001100000010004000018000400000201000000804000008010000008020000010020000010200000100200000100908713a7,0xf344583cc0000000f30001119cc00f379803cc0f30079bcc007a73001e9cc003cc0000f300001e64dcf5,0x0,0x0,0x0,0x0,0x0,0x24050a5414c2,0x2405025404c2,0x2405025404c2,0x2405025404c2,0x24050a5414c2,0x1e449b8624dc3126a5000003b9bbc24d4a00000773595dcd6500079126e09acbe449a9400000ee6b28001dcd650000000773594001dcd6503b9b413594077359400003b9aca000003b9aca000003ba23d5940077536165001dd4d85940077536165000eee25d94000ee6d0c8537af9,0x0,0x1e449b8624dc3126a5000003b9bbc24d4a00000773595dcd6500079126e09acbe449a9400000ee6b28001dcd650000000773594001e449a97b9b413594077359400003b9acaee6b2bb9aca000003ba23d5940077536165001dd4d85940077536165000eee25d94000ee6d0c8537af9,0x24050a5414c2],
[0x2405085414c2,0x2405025404c2,0x2405085414c2,0x0,0xf3445a22c0001e61e60799119cc03ccf300799f530079bcc007a73001e600f33cc00f3f3003cde64dcf5,0x400221110000800004000000000002000000022110000080000000200100000200004000010010000020040000080100000080422000100080000400000001000400001001087fba7,0x0,0x0,0x0,0x0,0x0,0x0,0xf4e6007a73000f4e63cc03cc01e9cc3cc03ccf301e63cc1e60f301e60f31e60f307980f3003d783be6,0x0,0x0,0xf344583cc0000001e60001119cc03ccf3007980f30079bcc007a73001e9cc003cc0000f6cc001e64dcf5,0x0,0x0,0x0,0xf344583cc0000001e60001119cc03ccf3007980f30079bcc007a73001e9cc003cc0000f300001e64dcf5,0x0,0x0,0x0,0x0,0x0,0x24050a5414c2,0x2405025404c2,0x2405025404c2,0x2405025404c2,0x24050a5414c2,0xf307983cc00000000003cc1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0],
[0xf307983cc00000000003cc1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925,0x24050a5414c2,0x2405085414c2,0x2405025404c2,0x2405085414c2,0x0,0x40002000000108000400000002001080000004200000010001000100020000108000000040200000100800001008000001008040000010100000010400000101000000100108713a7,0x4200108004101004000a00028080402000844e4,0x0,0x0,0x210882240481,0x230884240481,0x210882240481,0x210882240481,0x230884240481,0x230884240481,0x230884240481,0x210882240481,0x2509c8240501,0x230884240481,0x2509c8240501,0x200880240481,0x4200108002100084080202008080402000844e4,0x0,0x40002000000208000400000008002080000020200000020001000200080000208000000040200000100800001008000001008040000010100000010400000101000000100108713a7,0x0,0x0,0x0,0x210882240481,0x230884240481,0x210882240481,0x210882240481],
[0x230884240481,0x230884240481,0x230884240481,0x210882240481,0x2509c8240501,0x230884240481,0x2509c8240501,0x200880240481,0x4200108004100104080002008080402000804e4,0x4200108040101004080202008080402000844e4,0x4200108008100204080102008080402000864e4,0x0,0x0,0x2010000008040000010080000020100040010800100802000000042000002008000001201080004402000004000000011000400020001000080424000200010000002020107ba28,0x0,0x0,0x631082240481,0x421000240481,0x631082240481,0x421004240481,0x421004240481,0x421000240481,0x421004240481,0x421004240481,0x421008240481,0x421000240481,0x421008240481,0x421004240481,0x4200108010100404080102008080402000864e4,0x4200108040101004080202008080402000844e4,0x4200108020100804080202008080402000844e4,0x0],
[0x0,0xf4e6003d39800f4e6003cfcc00408c003cfcc001116000f3000011163cc0000f307983cc001e610856,0x0,0x0,0xa521c2240501,0x842108240501,0xa521c2240501,0x842108240501,0x842104240501,0x842108240501,0x842104240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x4200108040101004080202008080402000844e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_7673 : TreeBound (n := 4) 107 (programCode 0x4e29077079) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x3d39803cc001e9d3987983cde60445f9805b3f53001e9cc01e6f3001e9cc001023000408c001e7032b5,0x804020108000020008004200108002200080ce3,0x3d39803cc005b5d398f303cde6025ff98097ff53001e9cc01e6f3001e9cc0010230007d4c001e703345,0x0,0x3d39803cc0079bd398000f31f53079f9811160000f4e600f4e6000f4e9cc001f530007d4c001e703855,0x0,0x3d39803cc003cfd398000799f53079f98097e0001e7e6007b66001e7e9cc001f530007d4c001e703855,0x0,0x8405084410a2,0xa405025414c2,0x8405084410a2,0xa405025414c2,0x8405084410a2,0xf379801e600003cc003cc1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925,0x3d3d4c3cc1e603d3983ea6000f3079803cde6007981e63cc1e607981e9cc001f53000f6cc001e7038e5,0xf379801e600003cc003cc1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925,0x8405084410a2,0x8405084410a2,0x8405084410a2,0x8405084410a2,0x16c83cc1e60f303cc1e63cc07996c81e61e603ccf30b643cc0f30f301e63cc1e60f30b643cc0f30799c76,0x800020008000000008004200108002200080ce3,0x3d39803cc01e63d3a3641e7e60081afe03ecc073001e9cc01e6f3001e9cc001023000408c001e7032b5,0x800020008000000008004200108002200080ce3,0x421010240481,0x400010240481,0x421010240481,0x400010240481,0x462190240501,0x400010240481,0x462190240501],
[0x400010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_7706 : TreeBound (n := 4) 107 (programCode 0x4e2907707a) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1020020808020200408060200808048200205104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_7707 : TreeBound (n := 4) 107 (programCode 0x4e2907707b) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x79f9800f30079f9f987983cde603cc00005b3f53001e9cc01e6f3001e9cc001f53000408c001e7037c5,0x0,0x3d39800f301e67a03b44f31e600f300051c2c073001e9cc01e6f3001e6003ccf303cc3cc03cde7032b5,0x421010210481,0x3d39801e601e67a0377bcc1e600f30004fdc46f3001e9cc01e6f3001e6003ccf301e67980799e703345,0x0,0x421010208481,0xf381183cc000079800408de6000000004bf000f30079bcc007a73001e9cc003db3000f300001e64dcf5,0x421010208481,0x1e9cc003db300001e60008118002046000408cf307a76cc0f4f5301e6007b66001eda7303cc1eda8f76,0x421010210481,0x421010200481,0x421010210481,0x421010210481,0x421010220481,0x421010200481,0x421010220481,0x421010210481,0x3d39800f3001ed9f98f303cde600f3000097f023001e9cc01e6f3001e9cc001023000408c001e7032b5,0x0,0x1000440010080200088004200100082002080ce3,0x0,0x1000840020100200088004200100102004080ce3,0x0,0x0,0xf379803cc0000798003cc1e600000003cc0000f30079bcc007a73001e9cc003db3000f300001e64dcf5,0x0,0x0,0x0,0x1020000800120004408068a00801048820205104,0x1000040000000200008004200101002040080ce3],
[0x1020000800120004408068a00801048840205104,0x1008040201000200008004200102002080080ce3,0x1000040000000200008004200100002000080ce3,0x1008040201000200008004200104002100080ce3,0x1000040000000200008004200100002000080ce3,0x0,0x80200000100000400400008002008008800400040008004000010000000010809000004020000080400000100800000100804000000410000000840000002100000010030850ca7,0x1001040140200008108004020108002200080ce3,0x40200000100000080400008002008009000400040008004000010000000010808800004020000010400000040800000200804000000210000000840000002100000010030840ca7,0x0,0x410882240481,0x430884240481,0x410882240481,0x410882240481,0x430884240481,0x430884240481,0x430884240481,0x410882240481,0x4709c8240501,0x430884240481,0x4709c8240501,0x410882240481,0x0,0x3cc01e6f301e67a03da74c1e600f30041dc2ed100f4e600f4e6000f4e9cc001023000408c001e7032b5,0xa00008002100084000a00028080402000100e4,0x3cc00f4e601e67a01a0ecc1e600f30040cac64600f4e6007b66001e7e9cc0010230007d4c001e703345,0x0,0x421002240481,0x400000240481,0x421002240481,0x400000240481,0x400004240481],
[0x400000240481,0x400004240481,0x400000240481,0x400008240481,0x400000240481,0x400008240481,0x400000240481,0x3d39801e601e679f9f981e7e600f300003ec46f3001e9cc01e6f3001e9cc0010230007d4c001e703345,0x0,0x0,0xa00008004100104000800028080402000100e4,0x0,0x0,0x410882240481,0x400000240481,0x410882240481,0x400000240481,0x400004240481,0x400000240481,0x400004240481,0x400000240481,0x421008240481,0x400000240481,0x421008240481,0x400000240481,0x421010240481,0x400010240481,0x421010240481,0x400010240481,0x462190240501,0x400010240481,0x462190240501],
[0x400010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_7804 : TreeBound (n := 4) 107 (programCode 0x4e2907707c) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1020040808020200408060200808048200205104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_7805 : TreeBound (n := 4) 107 (programCode 0x4e2907707d) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x844110240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_7806 : TreeBound (n := 4) 107 (programCode 0x4e2907707e) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x4010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_7807 : TreeBound (n := 4) 107 (programCode 0x4e2907707f) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x844110240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_7808 : TreeBound (n := 4) 107 (programCode 0x4e29077080) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x4010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_6912 : TreeBound (n := 4) 107 (programCode 0x4e290770) := by
  conv in programCode _ => reduce
  exact branchFour (k := (3,1)) (by decide +kernel) part003_6913 part003_6962 part003_7059 part003_7172 part003_7381 part003_7430 part003_7431 part003_7528 part003_7673 part003_7706 part003_7707 part003_7804 part003_7805 part003_7806 part003_7807 part003_7808

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part003_0 : TreeBound (n := 4) 107 (programCode 0x4e2907) := by
  conv in programCode _ => reduce
  exact branchFour (k := (3,0)) (by decide +kernel) part003_1 part003_2 part003_419 part003_420 part003_2837 part003_2838 part003_3063 part003_3064 part003_4697 part003_4698 part003_4923 part003_5820 part003_6685 part003_6686 part003_6911 part003_6912

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem partitioned003 : TreeBound (n := 4) 107 [((0,0),⟨1,1,false⟩),((1,0),⟨2,0,false⟩),((2,0),⟨3,0,true⟩)] := part003_0

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_1 : TreeBound (n := 4) 107 (programCode 0x4a290751) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x10804d0240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_2 : TreeBound (n := 4) 107 (programCode 0x4a290752) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x8040201000108002108048e00108040a00010104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_3 : TreeBound (n := 4) 107 (programCode 0x4a290753) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x10804d0240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_5 : TreeBound (n := 4) 107 (programCode 0x4a29075431) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0xf307983cc1e60f30798000f4e6003cde60079fa7344d3a2c000000001e9cc1e688b00003cc0003cc3c56]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_6 : TreeBound (n := 4) 107 (programCode 0x4a29075432) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1081cc6204481,0x1081004210481,0x1081cc6204481,0x1081004210481,0x1081004208481,0x1081004200481,0x1081004208481,0x1081004210481,0x1081004210481,0x1081004200481,0x1081004210481,0x1081004210481,0x0,0xf3079a22c0000f30000000f4e6003cde60079f98044d36603cc0000f4e9cd11688b00000000003cc3c56,0xf3000222c00088b0000798f4e6003d3980079f98044d3660f303cc0f4e9cd11688b0000f307983cc3cb6,0x0,0x8000a000201040041000800021080000000201e4,0x8000a001001040041000840021080040200209e4,0x80012000401040041000840021080040200209e4,0x80002000201040041000800021080000000201e4,0x80022000801040041000800021080000000201e4,0x80042001001040041000840021080040200209e4,0x80042001001040041000840021080040200209e4,0xf3079a22c1e60f30000f30f4e6003d3980079f98044d3660f300000f4e9cd11688b00000000003cc3cb6,0x80082002001040041000840021080040200209e4,0xf307983cc1e60f30000000f4e6003d3980079f98044d3660f300000f4e9cc1e688b00000000003cc3cb6,0xf300f33cc0f30f300f300079f9801ed980079f9800f4e600f6cc000f4e6799e60f300f30798003ea93b6,0xf307983cc1e60f30000000f4e6003d3980079f98044d3660f300000f4e9cc1e688b00000000003cc3cb6,0xf301e63cc0798f301e600079f9801ed980079f9800f4e600fa98000f4e6f31e60f301e60f3000408f3b6,0x0,0xf30c5922c03ccf300f3000f4e6003d3980079f980489f660f6cc000f4e7e62d981180f30798003ea9cb6],
[0xf30000b6400088b000079879f9801ed980079f9800f4e600f6cc000f4e6799e607980f30798003ea93b6,0x0,0xf300012fc0004bf0000f3079f9801ed980079f9800f4e600f6cc000f4e6799e607980f30798003ea93b6,0xf3001e9cc1e64bf001e60079f9801ed980079f9800f4e600f6cc000f4e6799e607980f30798003ee5fb6,0xf3000408c003db30003cc079f9801ed980079f9800f4e600f6cc000f4e6799e607980f30798003eed936,0xf307983cc03ccf30000f3079f9801ed980079f9800f4e600f6cc000f4e6799e607980f30798003ea93b6,0xf30007d4c001f53000798079f9801ed980079f9800f4e600f6cc000f4e6799e607980f30798003eb86b6,0xf3001e9cc03ccf3001e60079f9801ed980079f9800f4e600f6cc000f4e6799e607980f30798003ee5fb6,0xf3001e9cc01e6f3001e60079f9801ed980079f9800f4e600f6cc000f4e6799e607980f30798003ee5fb6,0xf300012fc0f30f30000f3079f9801ed980079f9800f4e600f6cc000f4e6799e607980f30798003ea93b6,0xf3003cfcc00f3f3003cc0079f9801ed980079f9800f4e600f6cc000f4e6799e607980f307980040527b6,0xf307983cc1e60f30000000f4e6003d3980079f980489f660f6cc000f4e7e62d981180f30798003ea9cb6,0xf300f33cc0f30f300f300079f9801ed980079f9800f4e600f6cc000f4e6799e607980f30798003ea93b6,0xf307983cc1e60f30000000f4e6003d3980079f980489f660f6cc000f4e7e62d981180f30798003ea9cb6,0xf301e63cc0798f301e600079f9801ed980079f9800f4e600f6cc000f4e6799e607980f307980042753b6,0x0,0xf3079a22c0000f30000000f4e6003cde60079f98044d36603cc0000f4e9cc1e688b00000000003cc3c56,0x80006000101040041000800021080000000201e4,0x0,0x0,0xf3081495c0004bf001e600f4e6003d3980079f98044d3660f303cc0f4e9cd11688b0000f307983cc3cb6,0x80012000401040041000804021080004020301e4,0x0,0x80022000801040041000804021080004020301e4,0xf30813a2c0004bf001e600f4e6003d3980079f98044d3660f303cc0f4e9cd11688b0000f307983cc3cb6,0xf3001e9cc01e6f3001e60079f9801ed980079f9800f4e600f303cc0f4e60097e0f30000f307983cc33b6,0x0,0xf3003cfcc00f3f3003cc0079f9801ed980079f9800f4e600f303cc0f4e60097e0f30000f307983cc33b6,0xf307983cc1e60f30000000f4e6003d3980079f98044d3660f300000f4e9cc1e688b00000000003cc3cb6,0x0,0xf307983cc1e60f30000000f4e6003d3980079f98044d3660f300000f4e9cc1e688b00000000003cc3cb6,0x0],
[0x0,0xf300003cc0000f3097e00079f9801ed980079f9800f4e600fa98000f4e6f31e603cc1e60f3000408f3b6,0x0,0x0,0xf300012fc0004bf0000f3079f9801ed980079f9800f4e600fa98000f4e6f31e603cc1e60f3000408f3b6,0xf30be095c0004bf001e600f4e6003d3980079f980489f660fa98000f4e7e62d981181e60f3000408fcb6,0xf3000408c003db30003cc079f9801ed980079f9800f4e600fa98000f4e6f31e603cc1e60f300040ea5b6,0xf307983cc0798f30000f3079f9801ed980079f9800f4e600fa98000f4e6f31e603cc1e60f3000408f3b6,0xf30007d4c001f53000798079f9801ed980079f9800f4e600fa98000f4e6f31e603cc1e60f3000409e6b6,0xf3001e9cc0798f3001e60079f9801ed980079f9800f4e600fa98000f4e6f31e603cc1e60f3000408f3b6,0xf3001e9cc01e6f3001e60079f9801ed980079f9800f4e600fa98000f4e6f31e603cc1e60f300041befb6,0xf300012fc0798f30000f3079f9801ed980079f9800f4e600fa98000f4e6f31e603cc1e60f3000408f3b6,0xf3003cfcc00f3f3003cc0079f9801ed980079f9800f4e600fa98000f4e6f31e603cc1e60f300042387b6,0x0,0xf300f33cc0f30f300f300079f9801ed980079f9800f4e600fa98000f4e6f31e603cc1e60f30004a0d3b6,0x0,0xf301e63cc0798f301e600079f9801ed980079f9800f4e600fa98000f4e6f31e603cc1e60f3000408f3b6]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_87 : TreeBound (n := 4) 107 (programCode 0x4a29075433) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10804c1204481,0x10804c1218481,0x10804c1204481,0x10804c1204481,0x10804c1208481,0x10804c1218481,0x10804c1208481,0x10804c1204481,0x10804c1210481,0x10804c1218481,0x10804c1210481,0x10804c1204481,0x0,0x1804c1220481,0x8040021000806004100104004102002080080ce3,0x1804c1220481,0x1804c1220481,0x280cc1220481,0x681cc1220481,0x280cc1220481,0x2040005000102004100104004102002080080ce3,0x4814c1220481,0x681cc1220481,0x4814c1220481,0x2040005000102004100104004102002080080ce3,0x0,0x0,0x0,0x0,0x0,0x80400010001040041000000801020000800201e4],
[0x0,0x7981e61e6079879800079f9801ed980079f980001e7e6000079801e67980007980000798003cc33b6,0x4002a0000000a8000400020000000180004002a1320000a0200400000040000180000002010000008020000004080000020080402400101000000400008000210000001001087f8a7,0x202000000808000000420000001080004002a1180000580604002800600005009800020100000010400000100200000200804200001000100000800400008108000010004c7ce27,0x42000000808000001020000001080000000802000002040000010080000020080002000200008024400004001004080008004000010480002040100000100100000010060d1ea8,0x10002000000008000000020000000280000000802000002008000020080000020080000008000000000800000800004000008004000800010000000100000000100000010000d13a8,0x4400110001040041004020901020020800a05e4,0x3242a0000010080000040a0000010080000002010000008008000008080000020080324299214400200800040002044100008020001921410002001100000204100000010040ff1a8,0xf379803cde6003d398000f4e6003d3980079fa08f10859f31e679801e7e61121dd80798798003db6cb6,0x2002000008008000004020000020080004002e1b60000a0200400000040000180000002010000008020000004080000020080436c00101000000400008000210000001001087f8a7,0xf379803cde60079f98000f4e6003d3980079fa08f10767e61e679801e7e6111e1180798798003db6cb6,0x0,0x0,0x0,0x0,0x0,0x1804c1220481,0x0,0x1804c1220481,0x1804c1220481,0x280cc1220481,0x681cc1220481,0x280cc1220481,0x0,0x4814c1220481,0x681cc1220481,0x4814c1220481,0xee6b2f73597b9aca00000ee6b2bb9acdb9aca000262f29680000000000000262f296800003b9acaee6b2801dcd6509503e76b281dcda09aca00eee25d9401dcf41d65001dce536b2803b9e83e83aca00773770d65003bd664ca0077394daca00773d0759400ee6ba6deff409,0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x401010001040041000001001040001000201e4,0x0,0x0,0x8118007b66000811800079f9801ed980079f980001e607983cfcc01e6f300003cc00f3f30003d1e5b6,0x400050001040041000001001040001000201e4,0x4400110001040041004021101040021000a05e4,0x400210001040041000001001040001000201e4,0xf379803cde6003d398000f4e6003d3980079fa08f10769cc1e679801e7e6111e1180798f30003db6cb6,0x0,0xf379801e7e60079f98000f4e6001ed980079fa4d698b1ae60f708c01e7e619aca0c03dc230003e30426,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_168 : TreeBound (n := 4) 107 (programCode 0x4a29075434) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10804c1204481,0x1080000210481,0x10804c1204481,0x1080000200481,0x1080000208481,0x1080000200481,0x1080000208481,0x1080000200481,0x1080000210481,0x1080000200481,0x1080000210481,0x1080000200481,0x0,0x1804c1220481,0x8040021000800020000804020102002080080ce3,0x1804c1220481,0x80000220481,0x280882220481,0x80000220481,0x280882220481,0x80000220481,0x481004220481,0x80000220481,0x481004220481,0x80000220481,0x0,0x0,0x0,0x0,0x0,0xf300003cc2d90f30b6400079f9801ed980079f9801e7e60088b0001e7e6799e607983cc079800445b3b6],
[0xf30000b6400088b000079879f9801ed980079f9801e7e60088b0001e7e6799e607983cc079800445b3b6,0x0,0xf300012fc0004bf0000f3079f9801ed980079f9801e7e60088b0001e7e6799e607983cc079800445b3b6,0xf300003cc0f30f3001e60079f9801ed980079f9801e7e60088b0001e7e6799e607983cc079800445b3b6,0xf3000408c003db30003cc079f9801ed980079f9801e7e60088b0001e7e6799e607983cc079800449f936,0x0,0xf30007d4c001f53000798079f9801ed980079f9801e7e60088b0001e7e6799e607983cc079800446a6b6,0xf3001e9cc0f30f3001e60079f9801ed980079f9801e7e60088b0001e7e6799e607983cc0798004497fb6,0xf3001e9cc01e6f3001e60079f9801ed980079f9801e7e60088b0001e7e6799e607983cc0798004497fb6,0xf300012fc0f30f30000f3079f9801ed980079f9801e7e60088b0001e7e6799e607983cc079800445b3b6,0xf3003cfcc00f3f3003cc0079f9801ed980079f9801e7e60088b0001e7e6799e607983cc07980046047b6,0x0,0xf300f33cc0f30f300f300079f9801ed980079f9801e7e60088b0001e7e6799e607983cc07980046413b6,0x0,0xf301e63cc0798f301e600079f9801ed980079f9801e7e60088b0001e7e6799e607983cc07980048273b6,0x0,0x1804c1220481,0x0,0x1804c1220481,0x80000220481,0x280882220481,0x80000220481,0x280882220481,0x80000220481,0x481004220481,0x80000220481,0x481004220481,0x80000220481,0x0,0x0,0x0,0x0],
[0x0,0xf300003cc0000f3097e00079f9801ed980079f9801e7e6008118001e7e6f31e603cc1e60f3000408f3b6,0x0,0x0,0xf300012fc0004bf0000f3079f9801ed980079f9801e7e6008118001e7e6f31e603cc1e60f3000408f3b6,0xf301e63cc0798f3001e60079f9801ed980079f9801e7e6008118001e7e6f31e603cc1e60f3000408f3b6,0xf3000408c003db30003cc079f9801ed980079f9801e7e6008118001e7e6f31e603cc1e60f300040ea5b6,0xf307983cc0798f30000f3079f9801ed980079f9801e7e6008118001e7e6f31e603cc1e60f3000408f3b6,0xf30007d4c001f53000798079f9801ed980079f9801e7e6008118001e7e6f31e603cc1e60f3000409e6b6,0xf3001e9cc0798f3001e60079f9801ed980079f9801e7e6008118001e7e6f31e603cc1e60f3000408f3b6,0xf3001e9cc01e6f3001e60079f9801ed980079f9801e7e6008118001e7e6f31e603cc1e60f300041befb6,0xf300012fc0798f30000f3079f9801ed980079f9801e7e6008118001e7e6f31e603cc1e60f3000408f3b6,0xf3003cfcc00f3f3003cc0079f9801ed980079f9801e7e6008118001e7e6f31e603cc1e60f300042387b6,0x0,0xf300f33cc0f30f300f300079f9801ed980079f9801e7e6008118001e7e6f31e603cc1e60f30004a0d3b6,0x0,0xf301e63cc0798f301e600079f9801ed980079f9801e7e6008118001e7e6f31e603cc1e60f3000408f3b6]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_249 : TreeBound (n := 4) 107 (programCode 0x4a29075435) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0xf307983cc1e60f307983d3b846f4e63cc03cc0001e679803ccf300799e9cc003db3000f6cc001e68a925]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_250 : TreeBound (n := 4) 107 (programCode 0x4a29075436) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8040201000104004100201008108001200060be4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_251 : TreeBound (n := 4) 107 (programCode 0x4a29075437) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1080cc2204481,0x1080882210481,0x1080cc2204481,0x1080882208481,0x1080882208481,0x1080882210481,0x1080882208481,0x1080882208481,0x1080882210481,0x1080882210481,0x1080882210481,0x1080882208481,0x0,0x180cc2220481,0x8040021000804010000404010102002080080ce3,0x180cc2220481,0x280882220481,0x280882220481,0x481882220481,0x280882220481,0x280882220481,0x481882220481,0x481882220481,0x481882220481,0x280882220481,0x0,0x0,0x0,0x0,0x0,0x4000000110000000240000000900000000c0202100100800200001000800004000000020010000080020000100080000200080402000101008000404000000800020001001087faa7],
[0x400021001000086004000000010000020040202100100800000000000800004000000020010000080020000100080000200080420000101080000404000000800000001001087faa7,0x0,0x0,0x400000101000000204000000810000000840202100100800200001000800004000000020010000080020000100080000200080420000101040000404000000800100001001087faa7,0x400021001000002004000008010000000040202100100800000000000800004000000020010000080020000100080000200080420000101000000404000000800000001001087faa7,0x0,0x0,0x400001001000002004000008010000008040202100100800000000000800004000000020010000080020000100080000200080420000101000000404000000800000001001087faa7,0xf30079bcc01e6f3001e600f4e6003d3980079faecc89f8460f30001e7e7e62d981183cc079800454ecb6,0x0,0xf30079bcc01e6f3003cc00f4e6003d3980079faecc89f8460f30001e7e7e62d981183cc079800454ecb6,0x0,0xf303cc3cc0f30f300f3000f4e6003d3980079faecc89f8460f30001e7e7e62d981183cc079800445bcb6,0x0,0xf303cc3cc0f30f301e6000f4e6003d3980079faecc89f8460f30001e7e7e62d981183cc079800445bcb6,0x0,0x180cc2220481,0x0,0x180cc2220481,0x280882220481,0x280882220481,0x481882220481,0x280882220481,0x280882220481,0x481882220481,0x481882220481,0x481882220481,0x280882220481,0x0,0x0,0x0,0x0],
[0x0,0x4000000110000000240000000900000000c0202100100800000000000800004000000020010000080020000100080000200080400000101000000404000000800000001001087faa7,0x0,0x0,0x0,0x400000101000000204000000810000000840202100100800200001000800004000000020010000080020000100080000200080402000101008000404000000800020001001087faa7,0x400021001000002004000008010000000040202100100800000000000800004000000020010000080020000100080000200080402000101008000404000000800000001001087faa7,0x0,0x0,0x0,0xf30079bcc01e6f3001e600f4e6003d3980079faecc89f8460f30001e7e7e62d981183cc0f3000454ecb6,0x400001001000004004000008010000010040202100100800000000000800004000000020010000080020000100080000200080402000101008000404000000800000001001087faa7,0xf30079bcc01e6f3003cc00f4e6003d3980079faecc89f8460f30001e7e7e62d981183cc0f3000454ecb6,0x0,0xf303cc3cc0f30f300f3000f4e6003d3980079faecc89f8460f30001e7e7e62d981183cc0f3000445bcb6,0x0,0xf303cc3cc0f30f301e6000f4e6003d3980079faecc89f8460f30001e7e7e62d981183cc0f3000445bcb6]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_332 : TreeBound (n := 4) 107 (programCode 0x4a29075438) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x80402010001040041004020101080022000a05e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_333 : TreeBound (n := 4) 107 (programCode 0x4a29075439) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0xf307983cc1e60f30798408de6102300001e60000f307981e60f303cc1e9cc003db3000f6cc001e68a925]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_334 : TreeBound (n := 4) 107 (programCode 0x4a2907543a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0xf307983cc1e60f307983cc1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_335 : TreeBound (n := 4) 107 (programCode 0x4a2907543b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10814c4204481,0x1081004210481,0x10814c4204481,0x1081004210481,0x1081004208481,0x1081004200481,0x1081004208481,0x1081004210481,0x1081004210481,0x1081004200481,0x1081004210481,0x1081004210481,0x0,0x1814c4220481,0x8040021000800040001004040102002080080ce3,0x1814c4220481,0x481004220481,0x281884220481,0x81004220481,0x281884220481,0x481004220481,0x481004220481,0x81004220481,0x481004220481,0x481004220481,0x0,0x0,0x0,0x0,0x0,0x4000000110000000240000000900000000c2002000108000000010000000040000000200010000800020001000080002000080402000101008000404000000800020001001087faa7],
[0x400021001000086004000000010000020042002000108000000000000000040000000200010000800020001000080002000080400000101000000404000000800000001001087faa7,0x0,0x400021001000084004000000010000020042002000108000000000000000040000000200010000800020001000080002000080400000101000000404000000800000001001087faa7,0x400000101000000204000000810000000842002000108000000010000000040000000200010000800020001000080002000080420000101040000404000000800100001001087faa7,0x400020001000000004000000010000000042002000108000000000000000040000000200010000800020001000080002000080400000101000000404000000800000001001087faa7,0x0,0x400021001000084004000000010000020042002000108000000000000000040000000200010000800020001000080002000080400000101000000404000000800000001001087faa7,0x400001001000002004000008010000008042002000108000000000000000040000000200010000800020001000080002000080400000101000000404000000800000001001087faa7,0xf30079bcc01e6f3001e600f4e6003d3980079f9f9c89f8460f30001e7e7e62d981183cc079800454ecb6,0x400001001000004004000008010000010042002000108000000000000000040000000200010000800020001000080002000080400000101000000404000000800000001001087faa7,0xf30079bcc01e6f3003cc00f4e6003d3980079f9f9c89f8460f30001e7e7e62d981183cc079800454ecb6,0x0,0xf303cc3cc0f30f300f3000f4e6003d3980079f9f9c89f8460f30001e7e7e62d981183cc079800445bcb6,0x0,0xf303cc3cc0f30f301e6000f4e6003d3980079f9f9c89f8460f30001e7e7e62d981183cc079800445bcb6,0x0,0x1814c4220481,0x0,0x1814c4220481,0x481004220481,0x281884220481,0x81004220481,0x281884220481,0x481004220481,0x481004220481,0x81004220481,0x481004220481,0x481004220481,0x0,0x0,0x0,0x0],
[0x0,0x4000000110000000240000000900000000c2002000108000000000000000040000000200010000800020001000080002000080400000101000000404000000800000001001087faa7,0x0,0x0,0x0,0x400000101000000204000000810000000842002000108000000000000000040000000200010000800020001000080002000080420000101080000404000000800200001001087faa7,0x400020001000000004000000010000000042002000108000000000000000040000000200010000800020001000080002000080400000101000000404000000800000001001087faa7,0x0,0x0,0x0,0xf30079bcc01e6f3001e600f4e6003d3980079f9f9c89f8460f30001e7e7e62d981183cc0f3000454ecb6,0x400001001000004004000008010000010042002000108000000000000000040000000200010000800020001000080002000080420000101080000404000000800000001001087faa7,0xf30079bcc01e6f3003cc00f4e6003d3980079f9f9c89f8460f30001e7e7e62d981183cc0f3000454ecb6,0x0,0xf303cc3cc0f30f300f3000f4e6003d3980079f9f9c89f8460f30001e7e7e62d981183cc0f3000445bcb6,0x0,0xf303cc3cc0f30f301e6000f4e6003d3980079f9f9c89f8460f30001e7e7e62d981183cc0f3000445bcb6]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_416 : TreeBound (n := 4) 107 (programCode 0x4a2907543c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0xf307983cc1e60f307983cc1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_417 : TreeBound (n := 4) 107 (programCode 0x4a2907543d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0xf3079a22c1e60f30000000f4e6003d3980079fa7344d3a2c000000001e9cc1e688b00003cc0003cc3cb6,0x0,0x10324c8204481,0x1022088210481,0x10324c8204481,0x0,0x1022088208481,0x1022088210481,0x1022088208481,0x0,0x1022088210481,0x1022088210481,0x1022088210481,0xf3000222c00088b0000798f4e6003d3980079fa8274d3a2c01e6001e7e63ce04da7307981e6003db6cb6,0x0,0x40000000900000000c00000009000000008002008000008008000020080000020080400020001000000804000080000002008010002000010008000100008000100000011000fb3a8,0x0,0x0,0x0,0x100a4e8204481,0x100bce821c481,0x100a4e8204481,0x0,0x100a0e8208481,0x100bce821c481,0x100a0e8208481,0x0,0x100a0e8210481,0x100bce821c481,0x100a0e8210481,0x0],
[0x0,0x40003000100000000400020001000020000002010000008008000020080000020080600031011000000804000000000000008020003001010000000100000000100000010000ff3a8,0x0,0x0,0xf3000222c00088b0000f30f4e6003d3980079fa7344d3a2c000000001e9cc1e688b00003cc0003cc3cb6,0xf3000f6cc001f53000427220842c804467300007980798f300f31e601e9cc003db3000f6cc001e68a925,0xf307983cc0000f300005b21e616c80000f300007980798f300f31e601e9cc003db3000f6cc001e68a925,0xf3079a22c0000f30000f30f4e6003cde60079fa7344d3a2c000000001e9cc1e688b00003cc0003cc3c56,0xf3000f6cc003db30007980f4e6003d3980079fa8274d3a2c000000001e9cc1e688b00003cc0003cc3cb6,0xf30079bcc00f3f3001ebb220476c803ccf300007980798f300f31e601e9cc003db3000f6cc001e68a925,0xf307983cc0000f300005b21e616c80000f300007980798f300f31e601e9cc003db3000f6cc001e68a925,0xf3079a22c1e60f30000f30f4e6003d3980079fa7344d3a2c000000001e9cc1e688b00003cc0003cc3cb6,0x400020001000000004000200010000000060002000080000000600000000400000002000010002000010010000080010000080400000101000000404000001010000001001087f7a7,0xf303cc3cc03ccf300f35b22d90f304bf25f92fc79807987980799e601e9cc003db3000f6cc001efcbcf5,0x0,0x44e0b007a91600f305b220842c804467300007980798f300f31e601e9cc003db3000f6cc001e68a925,0x1023798408c0000798005b21e616c80000f300007980798f300f31e601e9cc003db3000f6cc001e68a925,0x0,0x16c87985b200003cc0005b21e616c80000f300007980798f300f31e601e9cc003db3000f6cc001e68a925,0x1ee6ca03cc798079805b221b3ec801e6f300007980798f300f31e601e9cc003db3000f6cc001e6c7525,0xf3079800000000000005b21e616c80000f300007980798f300f31e601e9cc003db3000f6cc001e68a925,0x1ee1180798f300f3005b220476c803ccf300007980798f300f31e601e9cc003db3000f6cc001e68a925,0x4100104001040041004020801080022000a05e4,0xf379801e600003cc005b21e616c80000f300007980798f300f31e601e9cc003db3000f6cc001e68a925,0xf3079800000000000005b21e616c80000f300007980798f300f31e601e9cc003db3000f6cc001e68a925,0xf379803cc0000798005b21e616c80000f300007980798f300f31e601e9cc003db3000f6cc001e68a925,0xf3079800000000000005b21e616c80000f300007980798f300f31e601e9cc003db3000f6cc001e68a925,0x20100804001040041020100801080102004221e4,0x20100804001040041020100801080102004221e4,0x100004001040041000000801080002000201e4,0x40101004001040041020200801080202008261e4,0xf303cc3cc0f30f301e65b22d90f305b225f8f3079807987980799e601e9cc003db3000f6cc001ede5cf5],
[0x0,0x0,0x0,0x0,0x0,0x1ebc8c83cfdb3079805b23cb23c81153b300007980798f300f31e601e9cc003db3000f6cc001e8b4ea5,0xf3079800000000000005b21e616c80000f300007980798f300f31e601e9cc003db3000f6cc001e68a925,0x200048001040041000001001080002000201e4,0x4200108001040041004021001080022000a05e4,0x8800104042000000090000010010000001008000004020000020080000020080000080005440682020040000048000008040000000500008202400000005000000010000eaba8,0xf3079800000000000005b21e616c80000f300007980798f300f31e601e9cc003db3000f6cc001e68a925,0x0,0xf3079800000000000005b21e616c80000f300007980798f300f31e601e9cc003db3000f6cc001e68a925,0x40201008001040041040201001080202008241e4,0x20200808001040041040101001080102004261e4,0x200008001040041000001001080002000201e4,0x40201008001040041040201001080202008241e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_498 : TreeBound (n := 4) 107 (programCode 0x4a2907543e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x80400010001040041020000801080002000201e4,0x16c800111600016c800079f9801ed980079f99e601e7e6000204601e9cc1e60f30000b640003cc33b6,0x0,0x180488284222,0x180488284222,0x80488280222,0x180488284222,0x0,0x220000000880000001200000002800040202100100800000000000800004000004020010010080020000100080100000080420000100040000404000000800000001001087faa7,0x180488284222,0x0,0x580488294a62,0x580488290a62,0x180488284222,0x580488290a62,0x140005000106010100404200102002080080ce3,0x0,0x140005000106010100404200104002100080ce3,0x0,0x25f800097e00025f800079f9801ed980079f99e601e7e60003ea601e9cc1e60f300012fc0003cc33b6,0x80400210001040041020040801080042000209e4,0x8118007b66000811800079f9801ed980079f99e601e7e6000f4e601e9cc03ccf3000408c0003d07936,0xf3445800097e00025f8000f4e6003d3980079f9f988138460003ea601e9cc1e688b00012fc0003cc3cb6,0xfa98003ea6000fa9800079f9801ed980079f99e601e7e6001e7e601e9cc0f30f30007d4c0003cd26b6,0x8400210001040041020040801080042000209e4,0x8400210001040041020040801080042000209e4,0x25f83cc1e600025f800079f9801ed980079f99e601e7e60003ea601e9cc1e60f300012fc0003cc33b6,0x10400410001040041020080801080082000219e4,0x0,0xf34459e601e60000000000f4e6003d3980079f9f9881384600001e601e9cc1e688b00003cc0003cc3cb6,0xf35b21e607987981e60798f4e6003d3980079f9f988147760003ea601e9cc1e6c5700012fc0003cc3cb6],
[0x0,0x8000201040041020000801080002000201e4,0x8040201001040041020040801080042000209e4,0x8010200401040041020040801080042000209e4,0x201040041020000801080002000201e4,0x20000801040041020000801080002000201e4,0x8040201001040041020040801080042000209e4,0x8040201001040041020040801080042000209e4,0xf34459e601e60000000f30f4e6003d3980079f9f9881384600001e601e9cc1e688b00003cc0003cc3cb6,0x8080202001040041020040801080042000209e4,0x1040041020000801080002000201e4,0x20100804001040041020100801080102004221e4,0x1040041020000801080002000201e4,0x40201008001040041020200801080202008241e4,0x0,0x20400804001040041020100801080102004221e4,0x20004800101040041020100801080102004221e4,0x0,0x20008800201040041020100801080102004221e4,0x20040801001040041020100801080102004229e4,0x2001080040104004102010080108010200422be4,0x20100804201040041020100801080102004221e4,0x20020800801040041020100801080102004225e4,0x20100801001040041020100801080102004229e4,0x20040801001040041020100801080102004229e4,0x20400800201040041020100801080102004221e4,0x20080802001040041020100801080102004239e4,0x20000800001040041020100801080102004221e4,0x20100804001040041020100801080102004221e4,0x20100804001040041020100801080102004221e4,0x20200808001040041020100801080102004261e4,0x0],
[0xf30799e601e60000000000f4e6003d3980079f9f9881384600001e601e9cc1e688b00003cc0003cc3cb6,0x0,0x0,0x0,0x79800f4e6001e9cc0040d0784704163cc222c001116798222cf303cc1e9cc003db3000f6cc001e68a925,0x2001080040104004102010080108010200422be4,0x0,0x20020800801040041020100801080102004225e4,0x7980799e600f33cc01ea08de6102300001e600102307981e60f300001e9cc003db3000f6cc001e68a925,0x7987981e600003cc0003cc1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0,0x7987981e600003cc0003cc1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925,0x1040041020000801080002000201e4,0x100004001040041020000801080002000201e4,0x1040041020000801080002000201e4,0x200008001040041020000801080002000201e4,0x0,0x0,0x40005000101040041020200801080202008241e4,0x0,0x40009000201040041020200801080202008241e4,0x40041001001040041020200801080202008249e4,0x4001100040104004102020080108020200824be4,0x40201008201040041020200801080202008241e4,0x40021000801040041020200801080202008245e4,0x40201001001040041020200801080202008241e4,0x40041001001040041020200801080202008249e4,0x0,0x40081002001040041020200801080202008259e4,0x40001000001040041020200801080202008241e4,0x40101004001040041020200801080202008261e4,0x40201008001040041020200801080202008241e4],
[0x40201008001040041020200801080202008241e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_595 : TreeBound (n := 4) 107 (programCode 0x4a2907543f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0xf30000b640004bf0000b641e63528044efe1f73bf801e7e600f33cc01e9cc003db3000f6cc001e68a5c5,0x0,0x10324c8204481,0x1022088210481,0x10324c8204481,0x0,0x1022088208481,0x1022088210481,0x1022088208481,0x0,0x1022088210481,0x1022088210481,0x1022088210481,0x0,0x0,0x0,0xf300003cc007a73005b5cc1e616c80001e61e6079801e7e600f33cc01e7e6003d39800f3f3001e68a5c5,0x0,0x0,0x100a4e8204481,0x100bce821c481,0x100a4e8204481,0x0,0x100a0e8208481,0x100bce821c481,0x100a0e8208481,0x0,0x100a0e8210481,0x100bce821c481,0x100a0e8210481,0xf30813a2c00088b0079800f4e6003d3980079fa8274d3a2c01e6003cde63ce04da7307981e6003db6cb6],
[0x0,0x0,0x0,0x0,0x0,0x104a5e8204501,0xf300003cc0f30f303cc00000007980001e6000079801e7e60079bcc01e600003cc0000f30f301e64d995,0x104a5e8204501,0x0,0x1042108208501,0x8000200800000100004004100100002000080ce3,0x1042108208501,0x0,0x1042108210501,0x8000200800000100004004100100002000080ce3,0x1042108210501,0x0,0x0,0x0,0x0,0x0,0x0,0x10124c8204481,0x10120c8218481,0x10124c8204481,0x0,0x10120c8208481,0x10120c8218481,0x10120c8208481,0x0,0x10120c8210481,0x10120c8218481],
[0x10120c8210481,0xf30813a2c01e6f3001e600f4e6003d3980079fa8274d3a2c01e6001e7e63ce04da7307981e6003db6cb6,0x0,0x400000101000000204000000810000000860002110180000220100000080400000002000010008000020010000080020000080420000101040000404000000800100001001187faa7,0x0,0x0,0xf300003cc0000f307983cc1e616c80001e61e6079801e7e600f33cc01e9cc003db3000f6cc001e68a5c5,0x0,0x10124c8204481,0x10120c8218481,0x10124c8204481,0x0,0x10120c8208481,0x10120c8218481,0x10120c8208481,0x0,0x10120c8210481,0x10120c8218481,0x10120c8210481,0x0,0x0,0x0,0x0,0x0,0x0,0xf30798a713cc12fc3cc1e63528044efe1f73bf801e7e600f33cc01e9cc003db3000f6cc001e68a5c5,0x0,0x0,0x0,0x0,0x2020080801040041000000001080002000201e4,0x0],
[0x4020100801040041000000001080002000201e4,0x0,0x0,0x0,0x0,0x20000801040041000000001080002000201e4,0x20020800801040041020100801080102004225e4,0x20000801040041000000001080002000201e4,0x40021000801040041040201001080202008245e4,0x0,0x10224c8204481,0x1022088210481,0x10224c8204481,0x0,0x1022088208481,0x1022088210481,0x1022088208481,0x0,0x1022088210481,0x1022088210481,0x1022088210481,0xf30813a2c01e6f3001e600f4e6003d3980079fa8274d3a2c01e6001e7e63ce04da7307981e6003db6cb6,0x0,0x400001001000002004000008010000008060002100180000000000000800400000002000010008000020010000080020000080420000101000000404000000800000001001087faa7,0x0,0x0,0x0,0x10324c8204481,0x1002008210481,0x10324c8204481,0x0,0x1002008208481],
[0x1002008200481,0x1002008208481,0x0,0x1002008210481,0x1002008200481,0x1002008210481,0xf30079bcc01e6f3001e600f4e6003d3980079fa7344d3a2c01e6001e7e63ce04da7307981e6003db6cb6,0x0,0xf30079bcc01e6f3001e600f4e6003d3980079fa73489fa2c0f30001e7e7e62d981183cc079800454ecb6,0x0,0xf30079bcc01e6f3001e600f4e6003d3980079fa73489fa2c0f30001e7e7e62d981183cc0f3000454ecb6,0x0,0x10224c8204481,0x1022088210481,0x10224c8204481,0x0,0x1022088208481,0x1022088210481,0x1022088208481,0x0,0x1022088210481,0x1022088210481,0x1022088210481,0x0,0x0,0x0,0x0,0x0,0x0,0xf30000b641e60f303cc7983cde600f3097e009859801e7e60079bcc01e6003cfcc00f3f3003cde64d995,0x0,0xf3000222c1e60f303cde60f33cc03cc204600b6b9801e7e60079bcc01e600f33cc03ccf300799e66bf95],
[0x0,0x0,0x400020001000000004000200010000000060002000180000000000000000400000002000010008000020010000080020000080400000100000000404000000800000001001087faa7,0x0,0x0,0x0,0xf300003cc1e60f3000000000000000001e6000079801e7e60079bcc01e600003cc0000f300001e64d995,0xf300003cc1e60f3000000000000000001e6000079801e7e60079bcc01e63cc03ccf300f31e601e64d995,0xf30079bcc01e6f3003cc00f4e6003d3980079fa7344d3a2c01e6003cde63ce04da7307981e6003db6cb6,0x0,0xf30079bcc01e6f3003cc00f4e6003d3980079fa73489fa2c0f30003cde7e62d981183cc079800454ecb6,0x0,0xf30079bcc01e6f3003cc00f4e6003d3980079fa73489fa2c0f30003cde7e62d981183cc0f3000454ecb6,0xf303cc3cc03ccf300f35b22d90f303cc1e60f307980799e60079bcc01e9cc003db3000f6cc001ede5cf5,0x0,0xf3408c3cc03cc0000f3000f4e6003cde60079fa7344d3660000000001e9cc1e688b00003cc0003cc3c56,0x0,0x0,0x0,0x1028eec00f3f3003ccf3000f4e6003d3980079fa8293336607983cfcc1e9cc1e688b00012fc0003cc3cb6,0x210008400104004100201008108001200060be4,0x0,0x4100104001040041000000101080002000201e4,0x102708c00088b003ccf3000f4e6003d3980079fa8274d36607983cfcc1e9cc1e688b00012fc0003cc3cb6,0xf33cc03ccf3003ccf3000f4e6003d3980079f98f74d36607983cfcc1e9cc1e688b00012fc0003cc3cb6,0x0,0x0,0x20100804001040041020100801080102004221e4,0x20100804001040041020100801080102004221e4,0x100004001040041000000001080002000201e4,0x40101004001040041040201001080202008261e4,0xf303cc3cc0f30f301e65b22d90f303cc1e60f307980799e60079bcc01e9cc003db3000f6cc001ede5cf5],
[0x0,0x0,0x0,0x0,0x0,0x102708c0000f3003cde6000f4e6003d3980079fa8274d3660798000001e9cc1e688b00003cc0003cc3cb6,0x220008800104004100201008108001200060be4,0x1e9cc007a76cc0f6db6cc2d916c83cc1e62d9079801e7e600f33cc01e9cc003db3000f6cc001ee225c5,0x4200108001040041000000101080002000201e4,0x102708c0000f3003cde6000f4e6003d3980079fa8274d3660798000001e9cc1e688b00003cc0003cc3cb6,0x400020001000000000000000000000000060002000180008000600000000400000002000010008000020010000040020000080400000101000000404000000810000001000887fa67,0x0,0x0,0x40201008001040041040201001080202008241e4,0x20200808001040041020100801080102004261e4,0x200008001040041000000001080002000201e4,0x40201008001040041040201001080202008241e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_804 : TreeBound (n := 4) 107 (programCode 0x4a29075440) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x180488284222,0x180488284222,0x180488280222,0x180488284222,0x102745800f4e6003d398000f4e6003cde60079f9f988138460079bcc01ea09d34e8b001e60f3003d00856,0x8400210001040041040041001002040080209e4,0x180488284222,0x400010001040041040001001004000100201e4,0x580488294a62,0x580488290a62,0x180488284222,0x580488290a62,0x0,0x0,0x0,0x0,0x0,0x180488284222,0x180488284222,0x180488280222,0x180488284222,0xc00030001040041040005001080004241209e4,0xc0003000104004104000500100200408060be4,0x180488284222,0xc00030001040041040005001004004100a05e4,0x180488294a62,0x180488290a62,0x180488284222,0x180488290a62,0x0],
[0x0,0x0,0x0,0x0,0x180488284222,0x180488284222,0x80488280222,0x180488284222,0x10292b800097e0f30798000f4e6003d3980079f9f98814776000408c01ea0a4cd2570000f3f3003cc3cb6,0x0,0x180488284222,0x0,0x580488294a62,0x580488290a62,0x180488284222,0x580488290a62,0x0,0x0,0x0,0x401010001040041040001001040001000201e4,0x25f800097e00025f800079f9801ed980079f9bcc01e6f3000408c01e9cc1e60f300012fc0003cc33b6,0x0,0x0,0x0,0x0,0x1e60f307983cfcc00f3079f9801ed980079f9bcc01e6f3000408c01e9cc1e60f300012fc0003cc33b6,0x201001040041040001001080002000201e4,0x201020040104004104001100108001200824be4,0x200201040041040001001080002000201e4,0x4020300801040041040021001080022008245e4,0x201001040041040001001080002000201e4,0x8040201001040041040041001080042000209e4],
[0x0,0x10080202001040041040081001080082000219e4,0x8040201001040041040041001080042000209e4,0x20100a04001040041040101001080102005229e4,0x10292b9e607983cfcc00000f4e6003d3980079f9f98814776000408c01e9cc20525700012fc0003cc3cb6,0x40201208001040041040201001080202008241e4,0x8118007b66000811800079f9801ed980079f9bcc01e6f3003cfcc01e9cc0798f3000f6cc0003d1e5b6,0x400050001040041040001001080002000201e4,0xfa98003ea6000fa9800079f9801ed980079f9bcc01e6f3001e9cc01e9cc0798f30007d4c0003cd26b6,0x400210001040041040001001080002000201e4,0x8400210001040041040041001080042000209e4,0x0,0x180488284222,0x180488284222,0x180488280222,0x180488284222,0x0,0x25f8007b6600025f800079f9801ed980079f9bcc01e6f3003cfcc01e601ed9801e60f301e603d1e5b6,0x180488284222,0x25f8003ea600025f800079f9801ed980079f9bcc01e6f3001e9cc01e603d39800f307983cc03cd26b6,0x580488294a62,0x580488290a62,0x180488284222,0x580488290a62,0x1040041001000040001004200102002080080ce3,0x0,0x1040041001000040001004200104002100080ce3,0x0,0x10400410001040041040081001080082000219e4,0x0,0xf34459e601e60000000000f4e6001ed980079f9f9881375300003cc01e9cc1e688b00003cc0003cc3c26,0x4040101040041040001001080002000201e4],
[0x0,0x8000201040041040001001080002000201e4,0x8000201001040041040041001080042000209e4,0x8010200401040041040041001080042000209e4,0x201040041040001001080002000201e4,0x20000801040041040001001080002000201e4,0x8040201001040041040041001080042000209e4,0x8040201001040041040041001080042000209e4,0xf34459e601e60000000f30f4e6001ed980079f9f9881375300003cc01e9cc1e688b00003cc0003cc3c26,0x8080202001040041040041001080042000209e4,0x1040041040001001080002000201e4,0x20100804001040041040101001080102004221e4,0x1040041040001001080002000201e4,0x40201008001040041040201001080202008241e4,0x0,0x20400804001040041040101001080102004221e4,0x20004800101040041040101001080102004221e4,0x0,0x20008800201040041040101001080102004221e4,0x20000801001040041040101001080102004229e4,0x2001080040104004104010100108010200422be4,0x20100804201040041040101001080102004221e4,0x20020800801040041040101001080102004225e4,0x20100801001040041040101001080102004229e4,0x20040801001040041040101001080102004229e4,0x20400800201040041040101001080102004221e4,0x20080802001040041040101001080102004239e4,0x20000800001040041040101001080102004221e4,0x20100804001040041040101001080102004221e4,0x20100804001040041040101001080102004221e4,0x20200808001040041040101001080102004261e4,0x0],
[0xf30799e601e60000000000f4e6001ed980079f9f9881375300003cc01e9cc1e688b00003cc0003cc3c26,0x0,0x0,0x0,0x0,0x11000401040041040001001080002000201e4,0x0,0x21000801040041040001001080002000201e4,0x0,0x0,0x0,0x0,0x1040041040001001080002000201e4,0x100004001040041040001001080002000201e4,0x1040041040001001080002000201e4,0x200008001040041040001001080002000201e4,0x0,0x0,0x40005000101040041040201001080202008241e4,0x0,0x40009000201040041040201001080202008241e4,0x40001001001040041040201001080202008241e4,0x4001100040104004104020100108020200824be4,0x40201008201040041040201001080202008241e4,0x40021000801040041040201001080202008245e4,0x40201001001040041040201001080202008241e4,0x40041001001040041040201001080202008249e4,0x0,0x40081002001040041040201001080202008259e4,0x40001000001040041040201001080202008241e4,0x40101004001040041040201001080202008261e4,0x40201008001040041040201001080202008241e4],
[0x40201008001040041040201001080202008241e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_4 : TreeBound (n := 4) 107 (programCode 0x4a290754) := by
  conv in programCode _ => reduce
  exact branchFour (k := (1,1)) (by decide +kernel) part002_5 part002_6 part002_87 part002_168 part002_249 part002_250 part002_251 part002_332 part002_333 part002_334 part002_335 part002_416 part002_417 part002_498 part002_595 part002_804

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_965 : TreeBound (n := 4) 107 (programCode 0x4a290755) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x1080890240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_966 : TreeBound (n := 4) 107 (programCode 0x4a290756) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x8040201000204008108004200108040200040ae4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_967 : TreeBound (n := 4) 107 (programCode 0x4a290757) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x1080890240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_968 : TreeBound (n := 4) 107 (programCode 0x4a290758) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x80402010004040101080002001080402000804e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_969 : TreeBound (n := 4) 107 (programCode 0x4a290759) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x1081010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_970 : TreeBound (n := 4) 107 (programCode 0x4a29075a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x1080010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_971 : TreeBound (n := 4) 107 (programCode 0x4a29075b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x1081010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_972 : TreeBound (n := 4) 107 (programCode 0x4a29075c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x1080010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_973 : TreeBound (n := 4) 107 (programCode 0x4a29075d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x0,0x100a0f0240481,0x8040200102004080008004200108002200080ce3,0x100a0f0240481,0x0,0x8040200012000480180084002108002200080ce3,0x0,0x103a0e6204481,0x8010200002000080000004020100002020080ce3,0x103a0e6204481,0x8000200002000080000004020100002000080ce3,0x1022084208481,0x8000200002000080000004020100002000080ce3,0x1022084208481,0x8040200002000080000004020102002080080ce3,0x106218c210501,0x8000200002000080000004020100002000080ce3,0x106218c210501,0xf300012fc0004bf0000f4e607a73007981e6079800f4e6011346000f4e61e7f5307983cc1e60f31aa956,0x8040200002000080000004020102002080080ce3,0xf300012fc0004bf0000fa9807a7300798798079800f4e6011163cc0f4e679ad907980f307983cc1e93b6,0x0,0xf300012fc0004bf0001023007a7300798f30079800f4e6011163cc0f4e6f325f83cc1e60f307983cf3b6,0x8040200022000880180104004108002200080ce3,0x0,0x100a0e1204481,0x400000011000000044000000110000000140020100100080400400000800000400800002210100008040000020000000020080000220010000800000001000080001000200017ffa8,0x100a0e1204481,0x1002000200481,0x1002000208481,0x1002000200481,0x1002000208481],
[0x0,0x1042108210501,0x1002000200481,0x1042108210501,0xf300012fc0004bf0000f4e607a73007981e6079801e7e60099c6001e7e61e7f5307983cc1e60f31aa956,0x0,0xf300012fc0004bf0001116007a7300799e60079801e7e60097e3cc1e7e679ad907983cc0798f3079b3b6,0x0,0xf300012fc0004bf0001023007a7300798f30079801e7e60097e3cc1e7e6f325f83cc1e60f307983cf3b6,0x8040200042001080100204008108002200080ce3,0x8040200002000080000004000108002200080ce3,0x8040200082002080100404010108002200080ce3,0x0,0x2300100001c00400012000000010000a0003111010000010100000002100002106002010001000008000004080010000080400000101000000104000001010000001001087d3a7,0x108882240482,0x0,0x108882240482,0x409882240c82,0x209882240c82,0x609882240c82,0x209882240c82,0x409882240c82,0x409882240c82,0x609882240c82,0x409882240c82,0x609882240c82,0x200048002010401c1002050101480012000e0fa4,0x0,0x40009000201040101004020101080022000804e4,0x8040200102004080000804020108002200080ce3,0x8040200002000080000004000108002200080ce3,0x8040200202008080201004040108002200081ce3],
[0x0,0xc0002012000480180084282108002200080ce3,0x108084240022,0x140004022000880180104284108002200080ce3,0x108084240022,0x409084240862,0x209084240862,0x8084240022,0x209084240862,0x409084240862,0x409084240862,0x8084240022,0x409084240862,0x8084240022,0xf307983cc1e600000001e61e603cc0000798000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0,0xf307983cc1e600000001e61e603cc0000798000f3007980000f300001e9cc003db3000f6cc001e68a925,0x8040200402010080402004080108002200082ce3,0x0,0xc0002082002080100404220108002200080ce3,0xf30f30f303cc0f30f303d3a730fa98003d399e601e7e61e6204601e9cc1e60f30000b640001e61556,0x140004082002080100404220108002200080ce3,0x1e60f307983cc1e60f3079f9801ed980079f99e601e7e60003ea601e9cc1e60f300012fc0003cc33b6,0x240008102004080000804200108002200080ce3,0x209888240c82,0x8088240022,0x209888240c82,0x409088240862,0x409088240862,0x8088240022,0x409088240862,0x8088240022],
[0x1e60011160002046000fa9f9f9801ed9879f9f99e601e7e603cfea61119cc222cf300f33cc03cfea9326,0x0,0x3cc001023000408c0010230079801ed98f300799e601e7e6079bea601e9cc25f8f301e63cc07983cf3b6,0x0,0x104a1e8204501,0xf300003cc03ccf303cc0798f301e63cc079800079801e7e60079bcc01e600003cc0000f30f301e64d995,0x104a1e8204501,0x0,0x1042108208501,0x8000200802020080004004100100002000080ce3,0x1042108208501,0x0,0x1042108210501,0x0,0x1042108210501,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xf30f30f303cc0f30f30f379803d39800f379bcc01e6f300003cc01e9cc0000f3000222c0007985216,0x0,0x1e60f307983cc1e60f3079f9801ed980079f9bcc01e6f3000408c01e9cc1e60f300012fc0003cc33b6,0x3ea60f307983cfcc00f3079f983ead980079f9bcc01e6f3007d88c01e9cc1e64bf00012fc0003cc33b6,0x209888240c82,0x8088240022,0x209888240c82,0x409088240862,0x409088240862,0x8088240022],
[0x409088240862,0x8088240022,0x1e6001116000204600118ff9f9801ed99e679f9bcc01e6798f3408c3ea9cc222cf303cc3cc1300641326,0x0,0x3cc001023000408c0010230079801ed98f30079bcc01e6f3079c08c01e9cc25f8f301e63cc07983cf3b6,0x10120d0240481,0x8040200002000080008004200108002200080ce3,0x10120d0240481,0x8040200402010080408004200108002200082ce3,0x1022090240481,0x1002010240481,0x1022090240481,0x8040200002000080008004200108002200080ce3,0x1042110240501,0x802020040c008080108078200108060200402104,0x1042110240501,0x802020080c008100108068200108060200804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_1118 : TreeBound (n := 4) 107 (programCode 0x4a29075e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x0,0x8040200004008080108048200108060200402104,0x8000a00014008080108008e00108060200402104,0x0,0x108890240481,0x140802014008080108048e00108060200402104,0x108890240481,0x0,0x0,0x0,0x0,0x0,0x445ad9097e0001e6111601e6798079879807b1a733459f4e6b67cc1e9cc2d9c5700f33cc03cc1e9c26,0x260bef097e0001e6111601e6798079879807981e679807b6afbc799e9cc2ddce3001338c03cc33f296,0x4459e611160001e6111601e6798079879807aecc4d36607983ea601e9cc2d988b00012fc03cc1e9cb6,0xa0000000800140000a004400020001100000800200001001000008001000008000082004400800100000800854002000804000000410000901040000804100000800158adb5a8,0x445ad911160001e6111601e6798079879807a8293345907983cfcc1e9cc2d90f300f33cc03cc1e9cb6,0x445ad911160001e6111601e679807987980798f38145ccc003cfcc1e9cc2d90f300f33cc03cc1e9cb6,0x4459e611160001e6111601e67980798798079f9c4d36607983ea601e9cc2d988b00012fc03cc1e9cb6,0x1e60f3097e3cc1e6102300f3798079879807987983cc1e8049d3981e9cc25f8f303cc3cc03cc981566,0x4459e6097e0001e6111601e6798079879807aecc4d36601e6b64001e9cc2d988b00003cc03cc1e9c26,0x25f8f3097e0001e6111601e67980798798079f980799e61e63ea601e9cc2d90f300012fc03cc1e9716,0x0,0x25f8f3097e0001e6111601e67980798798079bcc0798f31e6408c01e9cc2d90f300012fc03cc1e9716,0x209890240481,0x44200804400808010804b200108060200402b04,0x209890240481,0x1ed98007b69cc0f307a7300f33cc03cc79807a7307a76cc011253001e9cc1e60f3097e3cc03cc270776,0x409890240481,0x409890240481,0x409890240481,0x1048040204008080108048200108060200403104],
[0x808cd0240481,0x609890240481,0x808cd0240481,0x0,0x108890204481,0x800020004010008004200100002020080ce3,0x108890204481,0x0,0x798d4a1e603cc3cc1e61e601e6798079879807a730dc3bcc0798f3001ed5b6d90f3079800f33cc5b3e56,0x0,0x798b641e607983cc1e61e601e6798079879807a730bddbcc0798f3001ebb22d90f3079807983cc5b3e56,0x0,0x798b641e603cc3cc1e61e601e6798079879807a730bddbcc0798f3001ebeeed903cc79800f33cc5b3e56,0x798b641e603cc3cc1e61e601e6798079879807a730bddbcc0798f3001e63ced900f379800f33cc5b3e56,0x1e600007a73000f30000000001e6079800f3001e9cc007a73001e63cc03ccf300f31e601e64d995,0x0,0x808cd0220481,0x800020004010008004200100002010080ce3,0x808cd0220481,0x8890200481,0x0,0x0,0x80006000220040801000008041200000044021a4,0x4000000110000000440000001100000001100000800100000801000008001000008004010001510040080040000004000600800001200020001000200010000a000108000401fb3a8,0x0,0x8000a000220040801001008041001008044221e4,0x100a0852b18e2,0x100a085289502,0x100a0812a10a2,0x100a085289502,0x80006000220040801009008041201008244221a4,0x100a0852918e2],
[0x0,0x100a0852918e2,0x0,0x100a0812a10a2,0x0,0x100a0812a10a2,0x0,0x100a0812a52a2,0x100a0812852a2,0x0,0x100a0812852a2,0x100a0812b18e2,0x100a081289502,0x100a0812a10a2,0x100a081289502,0x100a081295ae2,0x100a0812918e2,0xf300012fc0004bf0000fa98079f980798798079800f4e600f303cc0f4e6799e60f300f307983cc1e93b6,0x100a0812918e2,0xf300012fc0004bf0000fa98079f980798798079800f4e600f303cc0f4e6001e60f3000000003cc1e93b6,0x100a0812a10a2,0x0,0x100a0812a10a2,0x0,0x0,0x0,0xf3000222c000798000111601e6798079879807a73007ba2c0003cc001e9cc2d90f300003cc03cc1e9cb6,0x0,0x19e3721e6f30079bcc0111601e6798079879807b1e379ba2c0003cfcc1e9cc33c7d700f33cc03cc1e9cb6,0x1e601e67980798798111601e6798079879807a755ffba2c0003cc799e9cc2ddce3000408c03cc22e236,0x18ae001ed98007b6600111601e6798079879807b0ae07ba2c0003ea601e9cc315cf300f33cc03cc1e9cb6,0x0],
[0xf6cc1e6079879bcc0111601e6798079879807a86393ba2c0003cfcc1e9cc315cf300f33cc03cc1e9cb6,0xf3001e9cc0079bcc0111601e6798079879807a85fc7ba2c0003cfcc1e9cc315cf300f33cc03cc1e9cb6,0x798001ed98007b6600111601e6798079879807b0ae07ba2c0003ea601e9cc315cf300f33cc03cc1e9cb6,0x422220011008000010000a00100000000142202100100800000000800800002000000002010000008010000008080000020080400000101000000404000000410000001001087f5a7,0x16cbcc1e60000798000111601e6798079879807aecbd3ba2c0003cc001e9cc2d988b00003cc03cc1e9cb6,0x7980020460007b6600111601e6798079879807b0ae07ba2c0003ea601e9cc315cf300f33cc03cc1e9cb6,0x0,0x0,0x0,0x100a0812a52a2,0x100a0812852a2,0x0,0x100a0812852a2,0x100a0812b18e2,0x100a081289502,0x100a0812a10a2,0x100a081289502,0x100a081295ae2,0x100a0812918e2,0x0,0x100a0812918e2,0x0,0x100a0812a10a2,0x0,0x100a0812a10a2,0xf307a76cc1e9db30007d88de6102300001e600001e679803ccf300799e9cc003db3000f6cc001e68a925,0xf307983cc1e60f300003cc1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0,0x16cdb2222c0007981e6111601e6798079879807aecdb9b6607983ea601e9cc2d9c5700012fc03cc1e9cb6,0x3cc1e60f307980f3111601e6798079879807aecbd3b6603cc3ea601e9cc2d988b0000b6403cc1e9cb6,0xf3000222c0003cc000111601e6798079879807aec807b660000b82601e9cc2d90f300003cc03cc1e9c26,0x3cc1e60f307981e6111601e6798079879807aecbd3b6607983ea601e9cc2d988b00012fc03cc1e9cb6],
[0x19e3721e6fa983cfcc0111601e6798079879807b1e379b6e8b00b82601e9cc33c7d701119cc03cc226826,0x1e601e679803cc798111601e6798079879807aee667b6db660b82601e9cc2dcdb300f708c03cc22e1a6,0x16c8001ed98003ea600111601e6798079879807aec807b6d9800b82601e9cc2d90f300f33cc03cc1e9c26,0x1e601e67980798f30111601e6798079879807aef597b663cc03ea601e9cc2dec130007d4c03cc1f8fb6,0xf6cc1e616c83cfcc0111601e6798079879807afbed3b6e8b00b82601e9cc2f7e8b01119cc03cc226826,0xf3001e9cc003cfcc0111601e6798079879807afbb07b6e8b00b82601e9cc2f76f301119cc03cc226826,0x7980020bf8003ea600111601e6798079879807aec807b6d9800b82601e9cc2d90f300f33cc03cc1e9c26,0xf3001e9cc0079f980111601e6798079879807afbb07b67e6003ea601e9cc2f76f3003cfcc03cc3564b6,0x16cbcc1e600003cc000111601e6798079879807aecbd3b660000b82601e9cc2d988b00003cc03cc1e9c26,0x7980020460003ea600111601e6798079879807aec807b6d9800b82601e9cc2d90f300f33cc03cc1e9c26,0x0,0x798001f53000408c00111601e6798079879807aec807b753000b82601e9cc2d90f301e63cc03cc5b5c26,0xf300012fc0004bf0000fa98079f98079879807980f31e603cc03ccf31e9cc1e60f30007d4c03cc1f86b6,0xf30811bcc2046f3003cfcc1e60f3000000000000f307981e60f303cc1e9cc003db3000f6cc001e68a925,0xf307983cc1e60f300003cc1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0,0x16cdb2222c0007981e6111601e6798079879807aecdb9b6607983ea601e9cc2d9c5700012fc03cc1e9cb6,0x3cc1e60f307980f3111601e67980798798079f9bd3b6603cc3ea601e9cc2d988b0000b6403cc1e9cb6,0xf3000222c000798000111601e6798079879807aec807b6600003ea601e9cc2d90f300003cc03cc1e9cb6,0x3cc1e60f307981e6111601e67980798798079f9bd3b6607983ea601e9cc2d988b00012fc03cc1e9cb6,0x222c00f3fa983cfcc00fa98079f9807987980799e601e688b003ea601e9cc1e60f301119cc03cc225fb6,0x7980f379803cc7980fa98079f9807987980799e601e601e603ea601e9cc1e60f300f708c03cc22d936,0x18ae001ed98007b6600111601e6798079879807b0ae07b6d98003ea601e9cc315cf300f33cc03cc1e9cb6,0xf300f33cc03ccf300fa98079f9807987980799e601e603cc03ea601e9cc1e60f30007d4c03cc1f86b6,0x3cc00f307983cfcc00fa98079f9807987980799e601e60f3003ea601e9cc1e60f301119cc03cc225fb6,0x3cc00f6cc003cfcc00fa98079f9807987980799e601e60f3003ea601e9cc1e60f301119cc03cc225fb6,0x1e6000fa98003ea6000fa98079f9807987980799e601e6798003ea601e9cc1e60f300f33cc03cc1e93b6,0x79800f4e6003d39800fa98079f9807987980799e601e61e6003ea601e9cc1e60f30408fcc03ccb2a7b6,0xf300003cc0000fa98079f9807987980799e601e6000003ea601e9cc1e60f300003cc03cc1e93b6,0x1e60011160003ea6000fa98079f9807987980799e601e6798003ea601e9cc1e60f300f33cc03cc1e93b6,0x0,0x3cc001023000408c000fa98079f9807987980799e601e6f30003ea601e9cc1e60f301e63cc03cc5b53b6],
[0xf307983cc1e60f300003cc1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925,0xf3000222c00088b000111601e6798079879807aec807ba2c0003cc001e9cc2d90f300003cc03cc1e9cb6,0x0,0x16cdb2222c0007981e6111601e67980798798079f9807b8460003ea601e9cc2d9c5700012fc03cc1e9cb6,0xf30f30f303cc0f30fa98079f9807987980799e601e7e60003ea601e9cc1e60f30000b6403cc1e93b6,0xf3000222c000798000111601e67980798798079f9807b8460003ea601e9cc2d90f300003cc03cc1e9cb6,0x1e60f307983cc1e60fa98079f9807987980799e601e7e60003ea601e9cc1e60f300012fc03cc1e93b6,0x3cc00f307983cfcc00fa98079f9807987980799e601e7e60003ea601e9cc1e60f3001e9cc03cc225fb6,0x7980f379803cc7980fa98079f9807987980799e601e7e60003ea601e9cc1e60f3000408c03cc22d936,0x16c8001ed98007b6600111601e67980798798079f9807b8460003ea601e9cc2d90f300f33cc03cc1e9cb6,0xf300f33cc03ccf300fa98079f9807987980799e601e7e60003ea601e9cc1e60f30007d4c03cc1f86b6,0x3cc00f307983cfcc00fa98079f9807987980799e601e7e60003ea601e9cc1e60f3001e9cc03cc225fb6,0x3cc00f6cc003cfcc00fa98079f9807987980799e601e7e60003ea601e9cc1e60f3001e9cc03cc225fb6,0x1e6000fa98003ea6000fa98079f9807987980799e601e7e60003ea601e9cc1e60f300f33cc03cc1e93b6,0x79800f4e6003d39800fa98079f9807987980799e601e7e60003ea601e9cc1e60f3003cfcc03cc3927b6,0xf300003cc0000fa98079f9807987980799e601e7e60003ea601e9cc1e60f300003cc03cc1e93b6,0x1e60011160003ea6000fa98079f9807987980799e601e7e60003ea601e9cc1e60f300f33cc03cc1e93b6,0x0,0x3cc001023000408c000fa98079f9807987980799e601e7e60003ea601e9cc1e60f301e63cc03cc5b53b6,0x0,0xf3000222c00088b000111601e6798079879807aecbd3ba2c0003cc001ebb320979800000007d4c1e9cb6,0xf3000222c00088b0000fa980799e601e679807a7300012fc0003cc0f4e6005b20000f30798408e0498f6,0x0,0x0,0xf305b23cc0798f303cc6a53528f305b22d916c87980799e60079bcc01e607983cc0798f301e61f1b1cf5,0xf3000222c00088b0000fa980799e601e679807a7300012fc0003cc799e6020460007983cc1e9db52de76,0xf303cc3cc0f30f303cc5b22d90f303cc1e60f307980799e60079bcc01e607983cc1e60f303cc1ede5cf5,0x0,0xf3000222c00088b0000fa980799e601e679807a7300012fc0003cc1e7e60097e0001e60f3f33cfea98f6,0xf3000222c00088b0000fa980799e601e679807a7300012fc0003cfcc1e60f4e6003ccf300f3445a264f6,0x0,0xf3000222c00088b0000fa980799e601e679807a7300012fc0003db301e63cde600f30f301e65b23194f6],
[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1e60f307983cc1e60fa98079f980798798079bcc01e6f3000408c01e9cc1e60f300012fc03cc1e93b6,0x1e60f307983cfcc00fa98079f980798798079bcc01e6f3000408c01e9cc1e60f300012fc03cc1e93b6,0x7980f379803cc7980fa98079f980798798079bcc01e6f3000408c01e9cc1e60f3000f6cc03cc2445b6,0xf30000f300003ea6000fa98079f980798798079bcc01e6f3000408c01e9cc1e60f300003cc03cc1e93b6,0xf300f33cc03ccf300fa98079f980798798079bcc01e6f3000408c01e9cc1e60f30007d4c03cc1f86b6,0x3cc00f307983cfcc00fa98079f980798798079bcc01e6f3000408c01e9cc1e60f300012fc03cc1e93b6,0x3cc00f6cc003cfcc00fa98079f980798798079bcc01e6f3000408c01e9cc1e60f30079bcc03cc318fb6,0x1e6000fa98003ea6000fa98079f980798798079bcc01e6f3000408c01e9cc1e60f300f33cc03cc1e93b6,0x79800f4e6003d39800fa98079f980798798079bcc01e6f3000408c01e9cc1e60f3003cfcc03cc3927b6,0xf300003cc0000fa98079f980798798079bcc01e6f3000408c01e9cc1e60f300003cc03cc1e93b6,0x1e60011160003ea6000fa98079f980798798079bcc01e6f3000408c01e9cc1e60f303cc3cc03cc9813b6,0x0,0x3cc001023000408c000fa98079f980798798079bcc01e6f3000408c01e9cc1e60f301e63cc03cc5b53b6,0x80402001020040801080042001080402004028e4,0x800220004400808010800b200108060200402b04,0x8060200404008080108078200108060200402104,0x800220008400808010800a200108060200403504,0x80042001020040801080042001080402004028e4,0x80042001020040801080042001080402004028e4,0x8060200404008080108078200108060200402104,0x80082002020040801080082001080402004038e4,0x8040200004008080108048200108060200402104,0x8020200404008080108038200108060200402104,0x8040200004008080108048200108060200402104],
[0x8020200804008080108028200108060200406104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_1344 : TreeBound (n := 4) 107 (programCode 0x4a29075f61) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x100a0f0240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_1345 : TreeBound (n := 4) 107 (programCode 0x4a29075f62) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10320d0204481,0x1022090210481,0x10320d0204481,0x0,0x10320c1204481,0x8000200104000100000004020100002000080ce3,0x10320c1204481,0x1022080200481,0x1022082208481,0x8000200104000100000004000100002000080ce3,0x1022082208481,0x0,0xf3000222c00088b0000b64f4e6f3007980079fa8274d36607983cfcc1e6011167983cc0f307983cc3cb6,0x8000200104000100000004000100002000080ce3,0x0,0x0,0x0,0x0,0x0,0x0,0x1022090208481,0x8000a0001840800810804c200100443008040b04,0x1022090208481,0xf30811bcc0000f30097fe620467980000f30000f30079bcc007a73001ebb2003db3000f3f3001e64dcf5,0x1022090210481,0x1022090210481,0x1022090210481,0x8000a00019008040108048200101048040201104,0x1022090220481,0x8000a0001c008080108048e00104070080402104,0x1022090220481],
[0xf300012fc0002d90000b6400f46c801e6f3007a7307992fc007c59001e7e61e60798b640f307983cdc46]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_1378 : TreeBound (n := 4) 107 (programCode 0x4a29075f63) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x100a0f0240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_1379 : TreeBound (n := 4) 107 (programCode 0x4a29075f64) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x8000601004000500188004200100082002080ce3,0x400020001000090004000040010000800008002400040009000100004000200010004000008010000040040000020100000080020000041210000204800000800900001008485ae27,0x8000a01004000900188004200100102004080ce3,0x0,0x100a0e1204481,0x8000200004000100000004020100002000080ce3,0x100a0e1204481,0x1002000200481,0x10120c2208481,0x1002000200481,0x10120c2208481,0x0,0x400001001000090804000040010000048008002400040009080100004000200010000100008000800040000400020001000080020000041210000200800000800900001008485ae27,0x1002000200481,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100a0e1208481,0x1022084208481,0x100a0e1208481,0x1002000208481,0x10120c2208481,0x1002000208481,0x10120c2208481,0x8020201004020100808004100100202008084ce3,0x1022084208481,0x1002000208481],
[0x1022084208481,0x8000201004000100008004000100202008080ce3,0x1042108208501,0x0,0x1042108208501,0x0,0xf307983cc0000f307981e61e607980000f30000f30079bcc007a73001e9cc003db3000f300001e64dcf5,0x0,0x100a0e1208481,0x1022084208481,0x100a0e1208481,0x1002000208481,0x10120c2208481,0x1002000208481,0x10120c2208481,0x0,0x1022084208481,0x1002000208481,0x1022084208481,0x0,0x1042108208501,0x0,0x1042108208501,0x0,0x0,0x4459e603cc1e616c81e6208ad1800088b0098d30079bcc007a73001ebb2003db3000f3f3001e64dcf5,0x808020204040101080002001004400100804e4,0x0,0x1008040204040101080002001004400100804e4,0x1eda7301e60f3081181e62083398003db3007a730079bcc007a73001ebb2003db3000f3f3001e64dcf5,0x0,0x0],
[0x0,0x8200204040101080002001004400100804e4,0x8008200204040101080002001004400100804e4,0x0,0x10008400200040101080002001004400100804e4,0x0,0x0,0x0,0x0,0x8020201004020100808004200100802020084ce3,0x8000201004000100008004200100002000080ce3,0x8020201004020100808004200101002040084ce3,0x8000a00029008040108048200101048040201104,0x0,0x80403004000500188004200102002080080ce3,0x8004021004004100008004200102002080080ce3,0x100805004000900188004200102002080080ce3,0x0,0x201009004001100108004200102002080080ce3,0x8000001004000100008004200102002080080ce3,0x402011004002100108004200102002080080ce3,0x8020101004020100808004200102002080084ce3,0x804021004004100008004200102002080080ce3,0x1004000100008004200102002080080ce3,0x1008041004008100208004200102002080081ce3,0x1004000100008004200102002080080ce3,0x0,0x0,0x4020101004020100808004200102002080084ce3,0x0,0x0,0x400020011000000044000000090000000220002111020000010200000808200000000002010000002010000010080000010080402000100002000104020001000020001001087d7a7],
[0xf300012fc00088b00012fc00f42fc03ccf300798025f9e6098da980f4e6f307983cca7107987983d1426,0x0,0xf300012fc00088b00012fc00f42fc03ccf300798025f9e61125a981e7e6f307983cc97e07987983d1426,0x1dcd65001dd4d8597b9acbdcd65001dd4d85943b9ae7cd650025429b168b9aca7735a2e6b29dcd653b9ad173594ee6b2f735d35476a003b9b059acaee6c166b2803b9b059aca3b9b059aca03b9b05a23d594003bb89765000ee729b59403bb89765000ee6b45cd650ee8ad9df47e19,0xf3000222c00088b00012fc00f42fc03ccf3007980fa99e63ccfa98799e6f3001e9cc981d39879845a436,0x0,0x0,0x400031001000004004000008010000020020003100020000000200000800200000000200010000200010001000080001000080620000100000000106200001000000001001087d7a7,0xf300012fc0004bf0001116007a7300799e6007983cc1e63cde63cfcc1e679ad907983cc0798f3079b3b6,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x80403004000500188004200104002100080ce3,0x21004000100008004200104002100080ce3,0x100805004000900188004200104002100080ce3,0x201004000100008004200104002100080ce3,0x201009004001100108004200104002100080ce3,0x0,0x402011004002100108004200104002100080ce3,0x0,0x804021004004100008004200104002100080ce3,0x1004000100008004200104002100080ce3,0x1008041004008100208004200104002100081ce3,0x1004000100008004200104002100080ce3,0x0,0x0,0x4020101004020100808004200104002100084ce3,0x0],
[0x0,0xf3000222c00088b00012fc00f46c801e7e60079804459e60f3820b3cde7e60f30798b640f30f3079d906,0xf3000222c00088b00012fc00f46c801e7e600798025f9e603d41180f4e7e616c8798d4a0f30f30b69906,0x0,0xf3000222c00088b00012fc00f46c801e7e60079804459e60f381181e7e7e60f30798b640f30f3079d906,0xf3000222c0004bf00015d501e6f300798f3007b38d33459f4e63cfcc1e7e635283cc1e60f307983cfc26,0xf3000222c00088b00012fc00f46c801e7e6007980fa99e61e68118799e7e6000fa98b67db30f307e1e86,0x0,0x0,0x0,0xf300012fc0004bf0001023007a7300798f3007983cc1e63cde63cfcc1e6f325f83cc1e60f307983cf3b6,0x0,0x0,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_1524 : TreeBound (n := 4) 107 (programCode 0x4a29075f65) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x10120d0240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_1525 : TreeBound (n := 4) 107 (programCode 0x4a29075f66) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10320c1240481,0x8002200048108002100148c02108040a00010104,0x10320c1240481,0x0,0x10320c1204481,0x1002008210481,0x10320c1204481,0x1002000200481,0x1002000208481,0x1002000200481,0x1002000208481,0x0,0x1002008210481,0x1002000200481,0x1002008210481,0xf3000408c003db30003cc079fa73007980079f9801e7e60098d3001e7e61e7e6007983cc1e6003e6c7b6,0x0,0xf3000408c003db30003cc079fa73007980079f9801e7e600a710001e7e6799e607983cc079800449f936,0x0,0xf3000408c003db30003cc079fa73007980079f9801e7e6009f78001e7e6f31e603cc1e60f300040ea5b6,0x1022082240481,0x1002000240481,0x1022082240481,0xf307983cc0000f300001e61e607980000f300016c8079bcc0079bcc01e9cc003db3000f6cc001e64dcf5,0x1002004240481,0x1002000240481,0x1002004240481,0x8002200049008040101048040108048200201104,0x1002008240481,0x800220004c00808010404b080108070200402b04,0x1002008240481],
[0xf307983cc0000f300001e61e607980000f30000f30079bcc007980001e9cc003db3000f6cc001e64dcf5]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_1558 : TreeBound (n := 4) 107 (programCode 0x4a29075f67) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x10120d0240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_1559 : TreeBound (n := 4) 107 (programCode 0x4a29075f68) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x104a1e1204501,0x1062181230501,0x104a1e1204501,0x104a1e1204501,0x10521c1208501,0x10721c1238501,0x10521c1208501,0x1042101220501,0x1062181210501,0x1042101220501,0x1062181210501,0x8000200804000100000084002108002000080ce3,0x1042101220501,0x8000200804000100000084002108002000080ce3,0x1042101220501,0x0,0x4000040010000b0004000040010000100008002c0004000b000100004000200010000200008010100040040000020009000080400000041000000204000000810000001008485ae27,0x0,0x104a1e1204501,0x1062181230501,0x104a1e1204501,0x104a1e1204501,0x10521c1208501,0x10721c1238501,0x10521c1208501,0x1042101220501,0x1062181210501,0x1042101220501,0x1062181210501,0x0],
[0x1042101220501,0x0,0x1042101220501,0x0,0x0,0x104a1e1204501,0x0,0x104a1e1204501,0x1042100200501,0x1042100208501,0x8000200804000100000004000100002000080ce3,0x1042100208501,0x0,0x0,0x8000200804000100000004000100002000080ce3,0x0,0xf30007d4c003db30007d4c00f3f35b5cc00f3798026b11911253001e7e61e60f30f38511ae60079fec26,0x0,0x400030001000040004000000010000100020003000080000000200000000200000004000010010000020000000080000000080600000101800000404000001000000001001087fba7,0x0,0x0,0x10521c2240501,0x8000200804000100000004000108002200080ce3,0x10521c2240501,0x0,0x4825e603cc1e611161e62fbad1800088b00994cbd398003d39bcc01e9cc003db3000f6cc001e64dcf5,0x0,0x0,0x0,0x2521ca240501,0x842108240501,0x2521ca240501],
[0x842108240501,0x46218c240501,0x842108240501,0x46218c240501,0x42108240501,0x842108240501,0x842108240501,0x842108240501,0x42108240501,0x1042104240501,0x8000200804000100000004000108002200080ce3,0x1042104240501,0x8002200089008040101048040108048200201104,0x0,0x14a1e8240501,0x8004020804004100002004080108002200080ce3,0x14a1e8240501,0x8010080804010100c02004080108002200086ce3,0x2521c8240501,0x842108240501,0x2521c8240501,0x842108240501,0x462188240501,0x842108240501,0x462188240501,0x42108240501,0x842108240501,0x842108240501,0x842108240501,0x42108240501,0xf30b643cc0000f301e61e62d907980000f300016c8079bcc007980001e9cc003db3000f6cc001e64dcf5,0x0],
[0x14a1e8240501,0x0,0x14a1e8240501,0x0,0x2521c8240501,0x842108240501,0x2521c8240501,0x842108240501,0x462188240501,0x842108240501,0x462188240501,0x42108240501,0x842108240501,0x842108240501,0x842108240501,0x42108240501,0x0,0x0,0x0,0x0,0x0,0x2521c2240501,0x842108240501,0x2521c2240501,0x842108240501,0x46218c240501,0x842108240501,0x46218c240501,0x42100240501,0x842108240501,0x842108240501,0x842108240501],
[0x42100240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_1688 : TreeBound (n := 4) 107 (programCode 0x4a29075f69) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1022090240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_1689 : TreeBound (n := 4) 107 (programCode 0x4a29075f6a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1002010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_1690 : TreeBound (n := 4) 107 (programCode 0x4a29075f6b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1022090240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_1691 : TreeBound (n := 4) 107 (programCode 0x4a29075f6c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x80403804000500188004200108002200080ce3,0x0,0x402021804002100108004200100082002080ce3,0xc62190230501,0x402021804002100108004200100102004080ce3,0x0,0x462190208501,0x88002200204008108004200100240008040ae4,0x462190208501,0x880022004040101080002001004400100804e4,0xc62190210501,0xc62190230501,0xc62190210501,0xc62190230501,0xc62190220501,0xc62190230501,0xc62190220501,0xc62190230501,0x100805804000900188004200108002200080ce3,0x0,0x80601814000500188004200100082002080ce3,0x4020200804020100808004200104002020084ce3,0x100a01824000900188004200100102004080ce3,0x0,0x0,0x108004200204008108004200100240008040ae4,0x0,0x1080042004040101080002001004400100804e4,0x4020200804020100808004200100802020084ce3,0x200004000100008004200100002000080ce3,0x4020200804020100808004200101002040084ce3],
[0x200004000100008004200100002000080ce3,0x0,0x1080042020040801080082001020400804038e4,0x200004000100008004200104002100080ce3,0x1080042040041001080082001040401008058e4,0x201009804001100108004200108002200080ce3,0x0,0x402020814002100100084002108002200080ce3,0xf3079800000000000001e61e607980000f30001023079c08c0f307981e9cc003db3000f6cc001e68a925,0x402020824002100100104004108002200080ce3,0x0,0xc62182240501,0x2000240481,0xc62182240501,0x2008240481,0x2004240481,0x2000240481,0x2004240481,0x2000240481,0x2008240481,0x2000240481,0x2008240481,0x2000240481,0x402011804002100108004200108002200080ce3,0x0,0x0,0xf33cc03ccf300f33cc00f379803d39800f379800f4e600f300000f4e9cc0000f307983cc0007985216,0x0,0x0,0xa521c2240501,0x842108240501,0xa521c2240501],
[0x842108240501,0x842104240501,0x842108240501,0x842104240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x462190240501,0x2010240481,0x462190240501,0x2010240481,0x842110240501,0x2010240481,0x842110240501,0x2010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_1772 : TreeBound (n := 4) 107 (programCode 0x4a29075f6d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1042110240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_1773 : TreeBound (n := 4) 107 (programCode 0x4a29075f6e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1320d0240481,0x120002408108002108048e00108040a00010104,0x1320d0240481,0x0,0x408c000f6cc001f533ccf4e6f3001e60079fa7344d3a2c000000001e9cc1e688b00003cc0003cc3c56,0x0,0x0,0x0,0xf4ee11bd398f300f3001e6204679803ccf3000001e679803ccf300799e9cc003db3000f6cc001e68a925,0xf307983cc00000000001e61e607980000f30000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0,0x0,0x1023798408c0000798001e61e607980000f300000f307981e60f303cc1e9cc003db3000f6cc001e68a925,0xf307983cc00000000001e61e607980000f30000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0,0x0,0x16c87985b200003cc0001e61e607980000f300007980798f300f31e601e9cc003db3000f6cc001e68a925,0xf307983cc00000000001e61e607980000f30000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0,0xf307983cc00000000001e61e607980000f30000f3007980000f300001e9cc003db3000f6cc001e68a925,0x222090240481,0x42000840840800810804c200108043200040b04,0x222090240481,0x16c87983cc00003cc0001e61e607980000f30000f30079bcc007a73001e9cc003db3000f6cc001e64dcf5,0x402010240481,0x2010240481,0x402010240481,0x2010240481,0x802010240481,0x2010240481,0x802010240481],
[0x2010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_1806 : TreeBound (n := 4) 107 (programCode 0x4a29075f6f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1042110240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_1807 : TreeBound (n := 4) 107 (programCode 0x4a29075f70) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x10a0f0204481,0x84002914004100008004200100002020080ce3,0x10a0f0204481,0x0,0x81003004001100108004200100202008080ce3,0x80002004000100008004200108002000080ce3,0x82003004002100108004200100402010080ce3,0xa0002814020100808004200108002100084ce3,0x16a1f0210501,0x102010200481,0x16a1f0210501,0x80002004000100008004200100082000080ce3,0x14a1f0220501,0x80002004000100008004200100402000080ce3,0x14a1f0220501,0x102010200481,0x20020001010090004000040000900800008002400040009000100004000200010004000008010000040040000020100000080400000041000000204000000810000001008485ae27,0x0,0x10a0f0204481,0x100004004000100008004200100002020080ce3,0x10a0f0204481,0x0,0x101005004001100108004200100202008080ce3,0x0,0x102005004002100108004200100402010080ce3,0x0,0x16a1f0210501,0x102010200481,0x16a1f0210501,0x100804024000900188004200100102304080ce3],
[0x14a1f0220501,0x102005004002100108004200100402220080ce3,0x14a1f0220501,0x102010200481,0x0,0x0,0x0,0x0,0x0,0xf4eda76d3981e60f3001e62083398044673000001e679803ccf300799e9cc003db3000f6cc001e68a925,0xf307983cc00000000001e61e607980000f30000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0,0x0,0x20020001010090004000040000900800008002400040009000100004000200010000100008000800040000400020001000080400000041000000204000000810000001008485ae27,0xf307983cc00000000001e61e607980000f30000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0,0x0,0x0,0xf307983cc00000000001e61e607980000f30000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0,0xf307983cc00000000001e61e607980000f30000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0,0x200409004000500180084002108002200080ce3,0x204008944004100008004020108002200080ce3,0x200809004000900180104004108002200080ce3,0x0,0x2120c2240481,0x202000240481,0x2120c2240481,0x2521ca240501,0x2721c4240501,0x202000240481],
[0x2721c4240501,0x2521ca240501,0x2521c8240501,0x2721ce240501,0x2521c8240501,0x202000240481,0xf307983cc00000000001e61e607980000f30000f30079bcc007a73001e9cc003db3000f6cc001e64dcf5,0x0,0x400411004000500180084002108002200080ce3,0x0,0x400811004000900180104004108002200080ce3,0x0,0x2120c2240481,0x202000240481,0x2120c2240481,0x2521ca240501,0x2721c4240501,0x202000240481,0x2721c4240501,0x2521ca240501,0x2521c8240501,0x2721ce240501,0x2521c8240501,0x202000240481,0x0,0x0,0xf4e6003d39800f4e6003cc79803d39803cc79800f4e600f300000f4e9cc0000f307983cc001e610856,0x0,0x0,0xa521c2240501,0x842108240501,0xa521c2240501],
[0x842108240501,0x842104240501,0x842108240501,0x842104240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x462190240501,0x2010240481,0x462190240501,0x2010240481,0x842110240501,0x2010240481,0x842110240501,0x2010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_1343 : TreeBound (n := 4) 107 (programCode 0x4a29075f) := by
  conv in programCode _ => reduce
  exact branchFour (k := (3,0)) (by decide +kernel) part002_1344 part002_1345 part002_1378 part002_1379 part002_1524 part002_1525 part002_1558 part002_1559 part002_1688 part002_1689 part002_1690 part002_1691 part002_1772 part002_1773 part002_1806 part002_1807

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_1921 : TreeBound (n := 4) 107 (programCode 0x4a29076061) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0xf3000222c0002d90000b651383b300079803d3a730079bcc007a73001e600f33cc00f3f3003cde64dcf5,0xf3000222c0004bf0000ba0de6102300001e6000f30079bcc00f3f3001ea08c03ccf300f31e601e68a925,0x0,0x1084d0204481,0x230010000180000001000000001000020000100080000080200000800200000804000310110000008040000000100000080400230011000000004000200000004100008007f3a8,0x1084d0204481,0x0,0x0,0x42200001100000000c0000000201000000c0022110100000020000080080000200804000010010000008040000020100000080000200100000800400001000800002001000487f227,0x0,0x0,0x4084d0204481,0xf381183cc1e603cc799e601e67980798f3007a730811bcc01e6f3001ebeeed9079879803cc7984c0e56,0x4084d0204481,0xf381181e61e60798799e601e63cc0798f3007a730811bcc01e6f3001ebeeed90445f9801e67984c0dc6,0x80a4f0204481,0x0,0x80a4f0204481,0x1084d0204481,0x0,0x80002000040041001000000001001000048040e4,0x8000a000240041001000808021001008048241e4,0x0,0x8000a000240041001001008041001008048241e4,0xf3000222c0004bf0000b6f8539f5d93cc03cc0001e679803ccf300799e60b643cc2d90f303cc1e68a925,0x8001200144004100100201008100101004844ae4,0x0,0x80022000840041001004020101001020048844e4,0xf3000222c0004bf0000ba0de6102300001e60000f307981e60f303cc1ea08c03dc2300f31e601e68a925,0xf3000222c0004bf0000b641e60f300000000000f3007980000f300001e9cc003db3000f300001e68a925,0x0],
[0xf3000222c0004bf0000b641e60f300000000000f3007980000f300001e9cc003db3000f300001e68a925,0xf30b643cc0000f300001e601e679801e6f3007aec8bddbcc000000001e6012090003cc000081183cddf6,0x0,0xf30000b640004bf0000b641e63528044efe1f73bf801e7e600f33cc01e9cc003e2c800f4e6001e68a5c5,0x0,0xf3000222c0002d90000b6bb846f3001e601e600f30079bcc007a73001e607983cc0798f301e61e64dcf5,0x80042011040041001080042001002400088048e4,0xf3000222c0002d90000b6bb846f3001e603cc00f30079bcc007a73001e607983cc1e60f303cc1e64dcf5,0x80002010040041001080002001004400108040e4,0x80042011040041001080042001008400208048e4,0x80042011040041001080042001008400208048e4,0xf3000222c0002d90000ba0de60f3000001e6000f30079bcc007a73001e63cc03ccf300f31e601e64dcf5,0x80042011040041001080042001010400408048e4,0xf3000222c0002d90000d4a208b4b00008118098d30079bcc007a73001e7e6003cde600f379801e64dcf5,0xf3000222c0002d90000b6bb846f3001e603cc00f30079bcc007a73001e9d3983db3000f303cc1e64dcf5,0xf3000222c0002d90000d4a208b4b000088b0098d30079bcc007a73001e7e6003d39800f3f3001e64dcf5,0x80002010040041001080002001040401008040e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_1970 : TreeBound (n := 4) 107 (programCode 0x4a29076062) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0xf30000b6400088b000081180799e60798f3007980001e6000007983cded980000000000000fa9fd50c76,0x100a0812a52a2,0x0,0x100a0812a52a2,0xf30000b6400088b000088b0079bcc0798f30079803cde61023079bcc1e600f307983ea7e60fa983d1216,0x100a0822bdf02,0x0,0x100a0822bdf02,0x100a0852a52a2,0x100a0842a52a2,0x0,0x100a0842a52a2,0x0,0x0,0x400001001000000904000000c10000048010002020140008090400000240400000800800008004000040010000020020000080000100040000800200000400800001001000485ae27,0x0,0x80006000140041001080006001000c00028140e4,0x0,0x400001001000000a04000000810000048000022020100088090400000040000800800001008000008040000004020000010080000080040000400200001000800002001000485ae27,0x0,0x0,0x0,0x0,0xf30000b6400088b000088b0079bcc0798f3007980799e607980798799e601e61023798408ded98415796,0x0,0xf30000b6400088b000088b0079bcc0798f3007980f31e603cc0798f31e603cc1f53f307d4fd3983e0516,0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0,0x0,0x80006000140041001001004061001008048241e4,0x100a0812852a2,0x0,0x100a0812852a2,0x400001201000004804000012010000048000002000100008000400000000000000000020010000080040000040020000100080002400040009000200024000800090001000485ee27,0x100a082285702,0x400001001000004804000010010000048000002000100008000400000000000000000008008000040040000100020000200080001000040004000200010000800040001000485ae27,0x100a082285702,0x100a0852852a2,0x100a0842852a2,0x0,0x100a0842852a2,0x0,0x0,0x0,0x0,0x80006000140041001080006001080401209048e4,0x8000600014004100108000600100240008844ae4,0x80006000140041001080006001080401008040e4,0x80006000140041001080006001004400108844e4,0x80006000140041001080006001000c00209048e4,0x80006000140041001080006001008400209048e4,0x80006000140041001080006001080401008040e4,0x8000600014004100108000600101040040a058e4,0x80006000140041001080006001080401008040e4,0x8000600014004100108000600102040080c060e4,0x80006000140041001080006001080400008040e4],
[0x80006000140041001080006001040401008040e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_2035 : TreeBound (n := 4) 107 (programCode 0x4a29076063) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0xf307983cc0000f307981e601e63cc0798f3007a730811bcc0000f3001e9cc2d9000079800007983cddc6,0x80006010140041001080006001000c00028140e4,0x0,0x1084d0204481,0x0,0x1084d0204481,0x4459e607980001e6111601e63cc0798f3007a730813a2c0000f3001e9cd209798079800081183cddc6,0x0,0x0,0x0,0x0,0x4084d0204481,0x0,0x4084d0204481,0xf3e0041e688b07983cde601e63cc0798f3007a730e007cc088bf3001ed005801445f9801e679853a5c6,0x80a4f0204481,0x0,0x80a4f0204481,0x1084d0204481,0x0,0x8000a010240041001001008041001008048241e4,0x8000a010240041001000808021001008048241e4,0xf3000222c00088b079a0460079f9801e6f30079803cc1e60f3088b3cde600f307984459e60811fd51756,0x8000a010240041001001008041001008048241e4,0xf3079b15c0004bf07981e601e63cc0798f3007b38d33459f3003cfcc1e601209b64204600081183cfc26,0x8000a01064004100100200808100101004824be4,0x0,0x8000a010a40041001004008101001020048245e4,0x8000a010240041001001008201001208048241e4,0x8000a010240041001008008201001200048241e4,0x0],
[0x8000a010240041001010008401001200048241e4,0x0,0x0,0x0,0x0,0xf3000222c00088b0001303b846f4e63cc03cc00f30079bcc00f3f3001e607983cc0f30f301e61e68a925,0x0,0x80002010040041001008000001002200088040e4,0x8000601014004100100080402100201008844ae4,0x0,0x8000a01024004100100100804100201008844be4,0x80042010040041001008040201002200088048e4,0x8001201044004100100201008100201008844ae4,0xf3000222c00088b0001338de6102300001e600001e67980798f300f31ea08c03cc7980f300001e68a925,0x80022010840041001004020101002020088844e4,0x80042010040041001008040201002200088048e4,0x80042010040041001008040201002200088048e4,0xf3000222c00088b00012fc1e60f3000000000000f307983cc0f307981e9cc003cc0000f300001e68a925,0x80082010040041001010080401002200088058e4,0x0,0x0,0x0,0xf3000222c00088b00012fc1e60f300000000000f30079bcc00f300001e9cc003cc0000f300001e68a925,0x0,0x108890208481,0x408890208481,0x108890208481,0x0,0x0,0x420000011000000044000000080000000140202100100800000000000800004000004000010010000020040000080100000080002000100008000400010000800020001001087faa7,0x0,0x0],
[0x408890208481,0x408890208481,0x408890208481,0xf381183cc1e60798799e601e67980798f3007a730811bcc01e6f3001ebb22d90f307980f307984c0e56,0x80a8f0208481,0x0,0x80a8f0208481,0x0,0x0,0x80002010040041001000000001004000108040e4,0x80006010140041001000804021004020108844e4,0x80002010040041001000002001004400108040e4,0x8000a010240041001001008041004020108845e4,0x80042010040041001008040201004200108048e4,0x8001201044004100100201008100401010844ae4,0x0,0x80022010840041001004020101004020108844e4,0x80002010040041001000000201004200108040e4,0x80042010040041001008040201004200108048e4,0x0,0x80082010040041001010080401004200108058e4,0x0,0x0,0x0,0xf307983cc0798f307980f30079bcc0798f30079bcc01e6f307983cc01e603ea6000fa98003d3983cd556,0xf3000222c00088b0001338de6102300001e6000f30079bcc00f3f3001e63cc03cc7980f30f301e68a925,0xf3000222c00088b00012fc1e60f300000000000f30079bcc00f3f3001e9cc003cc0000f300001e68a925,0x0,0x109010210481,0x409010210481,0x109010210481,0x0],
[0x0,0x400000011000000044000000080000000142002000108000000000000000040000004000010010000020040000080100000080020000100080000400100000800200001001087faa7,0x0,0x0,0x409010210481,0x9010210481,0x409010210481,0x409010210481,0x80b0f0210481,0x0,0x80b0f0210481,0x409010210481,0xf3000222c00088b00012fc1e60f300000000000f30079bcc00f3f3001e9cc003cc0000f300001e68a925,0x0,0x10a0f0220481,0x50a0f0220481,0x10a0f0220481,0x0,0x0,0x0,0x0,0x1f173303cc0000f307b6601e63cc0798f3007a730bececc0000f3001ebf685ccc0079800007983cddc6,0x40a0f0220481,0x0,0x40a0f0220481,0x700000010400000011000000040000000170002195440000010100000004400000004000010010000040040000080100000080200000100800000101000000401000001001087dda7,0x80a0f0220481,0x0,0x80a0f0220481,0x80a0f0220481,0x0,0x108890208481],
[0x409890218481,0x108890208481,0x0,0x80040210040041001080042001020400808048e4,0x8118007980f3081273f30079bcc0798f3007a73001e9cc001023001e6799e607987980798798411ad6,0x16c8b643cc07983cc7981e601e67980798f3007a730bddbcc0798f3001e7e62d9079879807987983cde56,0xfa98003cc1e60fa9fa730079bcc0798f3007a73001e9cc001f53001e6799e6079879807987983dc856,0x409890218481,0x409890218481,0x409890218481,0x800020000000008004200100002010080ce3,0x80acf020c481,0x0,0x80acf020c481,0x800020000000008004200100002010080ce3,0x0,0x10a0f0220481,0x50a0f0220481,0x10a0f0220481,0x4459e607980001e6111601e63cc0798f3007a730813a2c0000f3001e9cc2d9000079800007983cddc6,0x0,0x0,0x0,0x0,0x40a0f0220481,0xf381183cc1e603cc799e601e63cc0798f3007a730811bcc01e6f3001ebb22d90b647981e607984c0dc6,0x40a0f0220481,0xf384e41e60f307983cde601e63cc0798f3007a73084e7cc00f3f3001eca535283cc7980f3079853a5c6,0x80a0f0220481,0x0,0x80a0f0220481,0x80a0f0220481],
[0x0,0x108010200481,0x408010200481,0x108010200481,0x0,0x0,0x8118007983cc081273f30079bcc0798f3007a73001e9cc003db3001e6f31e603cc7980f30798428756,0x0,0xfa98003cc1e60fa9fa730079bcc0798f3007a73001e9cc001f53001e6f31e603cc7980f307983dc856,0x408010200481,0x8010200481,0x408010200481,0x8010200481,0x80a0f0220481,0x0,0x80a0f0220481,0x8010200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_2212 : TreeBound (n := 4) 107 (programCode 0x4a29076064) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x8000a000240041001000008041000000048041e4,0x0,0x0,0x8000a000240041001001008041001008048241e4,0x100a0852b18e2,0x100a085289502,0x100a0812a10a2,0x100a085289502,0xf30813a2c00fb8b0001338de6102300001e6000003d398007a73000f4e63cc03cc7980f30f301e68a925,0x100a0852918e2,0x0,0x100a0852918e2,0x0,0x100a0812a10a2,0x0,0x100a0812a10a2,0x0,0x100a0812a52a2,0x100a0812852a2,0x0,0x100a0812852a2,0x100a0812b18e2,0x100a081289502,0x100a0812a10a2,0x100a081289502,0x100a081295ae2,0x100a0812918e2,0xf300012fc0004bf00010230079bcc0798f30079800f4e600f303cc0f4e6f31e60f301e60f307983cf3b6,0x100a0812918e2,0xf300012fc0004bf00010230079bcc0798f30079800f4e600f303cc0f4e6001e60f3000000007983cf3b6],
[0x100a0812a10a2,0x0,0x100a0812a10a2,0x0,0x40000000900000004c000000130000000200026000100008000400000040000900800000810000004040000010020000020080000200040000800200000400800001001000485ee27,0x80006000220041001000806021200c04028140a4,0x0,0xf300003cc00088b000222c1e60f300000001e60003cde600f3f3001e7e600003cc03ccf300f31e68a5c5,0x0,0x0,0x0,0xf3000222c00088b00011160079f9801e6f30079800001e6000088b001e607980001ed98003d3d4fefd56,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100a0812a52a2,0x100a0812852a2,0x0,0x100a0812852a2,0x100a0812b18e2,0x100a081289502,0x100a0812a10a2,0x100a081289502,0x100a081295ae2,0x100a0812918e2,0x0],
[0x100a0812918e2,0x0,0x100a0812a10a2,0x0,0x100a0812a10a2,0xf307a76cc1e9db30007d53b846f4e63cc03cc0001e679803ccf300799e9cc003db3000f6cc001e68a925,0xf307983cc1e60f300003cc1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x16c8001e60000408c00111601e63cc0798f3007aec807b660000408c01e9cc2d90f300003cc07983cfc26,0x1e601e63cc03ccf30111601e63cc0798f3007aee667b663cc0408c01e9cc2dcdb30007d4c07983def26,0x0,0x0,0x798001e60000408c00111601e63cc0798f3007aec807b660000408c01e9cc2d90f300003cc07983cfc26,0xf3001e7e6003d3980111601e63cc0798f3007afbb07b771600408c01e9cc2f76f30222fcc079853c426,0x16cbcc1e600003cc000111601e63cc0798f3007aecbd3b660000408c01e9cc2d988b00003cc07983cfc26,0x0,0x0,0x798001f53000408c00111601e63cc0798f3007aec807b753000408c01e9cc2d90f301e63cc07983cfc26,0xf300012fc00088b000102300f379803ccf3007980f300f3798fa98f31e9cc001f530b736cc0798459f26,0x0,0x100a0852a52a2,0x100a0852852a2,0x0,0x100a0852852a2,0x100a0852b18e2,0x100a085289502],
[0x100a0852a10a2,0x100a085289502,0x100a085295ae2,0x100a0852918e2,0x0,0x100a0852918e2,0x0,0x100a0852a10a2,0x0,0x100a0852a10a2,0xf307983cc1e60f300003cc1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0,0x0,0x0,0x0,0x0,0x0,0xf301e63cc0798798111600f379803ccf3007980f302049ccfad4c01e9cc0f4f530b6bd4c0798bf2436,0xf30000f30000408c0010230079bcc0798f30079bcc01e600000408c01e9cc1e60f300003cc07983cf3b6,0xf300f37980798f30102300f379803ccf3007980f30111d98fad4c01e9cc001f530b736cc0798459f26,0x0,0x79801e7e60079bcc0111600f379803ccf3007987980206460fad4c01e9cc1023f30ba0fcc0798be3136,0x11160007d4c00102300f379803ccf3007980000111600fad4c01e9cc0000f30b643cc07983d1426,0x79800f6cc0079f980102300f379803ccf30079879801152c0fad4c01e9cc088bf30bddbcc079844ac26,0xf300003cc00010230079bcc0798f30079bcc01e600000408c01e9cc1e60f300003cc07983cf3b6,0x3cc0010230007b6600102300f379803ccf30079bcc00120900fad4c01e9cc0798f30d4a3cc07983d1426,0x0,0x3cc0011160007d4c00102300f379803ccf30079bcc00111600fad4c01e9cc0798f30b643cc07983d1426,0xf307983cc1e60f300003cc1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0,0x600200011000000044002000080004000120000100080000400100000400200000806002010118008000400000040940000080400030011000000004000280010000100008017fe68,0x0],
[0x0,0x1e60f307983cc1e610230079bcc0798f3007980001e6000003cc001e9cc1e60f300003cc07983cf3b6,0x1f164003f990007b666accf0f13463cc03cc007980798f300f31e601e9cc003db3000f6cc001e68a925,0x7980f379803cc79810230079bcc0798f30079bea61e60f30040aa61e9cc1e60f301f56cc079842a5b6,0x0,0x0,0xf3b6401e8d9003cde64273e6109c80001e60007980798f300f31e601e9cc003db3000f6cc001e68a925,0xf30b640002d900001e63cc1e60f3000000000007980798f300f31e601e9cc003db3000f6cc001e68a925,0x0,0xf30b640002d900001e63cc1e60f3000000000007980798f300f31e601e9cc003db3000f6cc001e68a925,0xf300003cc00010230079bcc0798f3007980001e6000003cc001e9cc1e60f300003cc07983cf3b6,0x0,0x0,0x0,0x0,0x221100000484400001200000001001042202100108800000400000800002000004220010010800020000080080004000080400000101000000404000001010000001001087fba7,0xf30f30f303cc0f310230079bcc0798f300799e601e7e60003ea601e9cc1e60f30000b6407983cf3b6,0x0,0x1e60f30f307981e6102300f379803ccf30079bcc00102300fab6601e9cc00088b0b6715c07983d1426,0x3cc00f307983cfcc010230079bcc0798f300799e601e7e60003ea601e9cc1e60f3001e9cc079840bfb6,0xf300f33cc0798798102300f379803ccf30079bcc00102300fab6601e9cc001f530b6fa0c0798459f26,0x0,0x1e601e67980798f30111600f379803ccf30079bcc001f5300fab6601e9cc003db30b6bd4c07983eff36,0x1e60f4f53079bcc0102300f379803ccf30079bcc00102300fab6601e9cc00fb8b0bc142c079844ac26,0x79800f4e60079bcc0102300f379803ccf30079bcc00102300fab6601e9cc00f3f30bbf5cc079844ac26,0x20460007d4c00111600f379803ccf30079bcc001f5300fab6601e9cc0f30f30d4a3cc0798b69936,0x79800f6cc0079f980102300f379803ccf30079bcc00102300fab6601e9cc01e6f30c1a7cc079853dc26,0xf300003cc00010230079bcc0798f300799e601e7e60003ea601e9cc1e60f300003cc07983cf3b6,0x3cc0010230007b6600102300f379803ccf30079bcc00102300fab6601e9cc0798f30e3d3cc07983d1426,0x0,0x7980020460007d4c00111600f379803ccf30079bcc001f5300fab6601e9cc0f30f30d4a3cc0798b69936,0x0],
[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4000080000000800040002800000002000400020001000080004000000000000800010000020040000400100000400200000804000000810000002040000008100000010008862e67,0x200300000400c0000100200000100200042002000108000000010000000040000002000010008000020010000080020000080400000101000000404000000810000001001087faa7,0x400030000000010000000300000000100040002000100000000000000000000000002000010008000010008000080020000080400000101000000404000000410000001001087f5a7,0x100080000200900001002400002002000410020000020080004100000000200000010000080020000400100000400200000804000000810000001040000008100000010008869e67,0x400030000000010000000300000000100040002000100000000000000000000000002000010008000010008000080020000080400000101000000404000000410000001001087f5a7,0x0,0x0,0x0,0x400030001000010000000300000000100040002000100000000000000000000000002000010008000010008000080020000080400000101000000404000000410000001001087f5a7,0x0,0x0,0x0,0x0,0x3cc1e60f307981e6111600f379803ccf30079f9800204600fad4c01e9cc00088b0b6622c07983d1936,0x3cc1e7f53079bcc0111600f379803ccf30079f9800204600fad4c01e9cc00088b0ba2e2c07983d1936,0xf300f33cc0798798102300f379803ccf30079bcc00111600fad4c01e9cc001f530b6bd4c0798459f26,0x14e20007d4c00102300f379803ccf30079bcc00111600fad4c01e9cc0000f30b643cc07983d1426,0xf300f37980798f30102300f379803ccf30079bcc00111600fad4c01e9cc001f530b736cc0798459f26,0x3cc1e7f53079bcc0111600f379803ccf30079f9800204600fad4c01e9cc00088b0ba2e2c07983d1936,0x79800f4e60079bcc0102300f379803ccf30079bcc00111600fad4c01e9cc00f3f30ba0fcc079844ac26,0x11160007d4c00102300f379803ccf30079bcc00111600fad4c01e9cc0000f30b643cc07983d1426,0x79800f6cc0079f980102300f379803ccf30079bcc00111600fad4c01e9cc00f3f30bddbcc079844ac26,0xf300003cc00010230079bcc0798f30079bcc01e6f3000408c01e9cc1e60f300003cc07983cf3b6,0x3cc0010230007b6600102300f379803ccf30079bcc00111600fad4c01e9cc0798f30d4a3cc07983d1426,0x0],
[0x3cc0011160007d4c00102300f379803ccf30079bcc00111600fad4c01e9cc0798f30b643cc07983d1426]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_2405 : TreeBound (n := 4) 107 (programCode 0x4a29076065) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0xf3000f6cc001023000408d1383b300079803d39803d398003d39800f4e9cc003db3000f6cc001e64dcf5,0xf3000f6cc001f5300040c8de6102300001e6001023079c08c0f307981e9cc003db3000f6cc001e68a925,0x0,0x0,0x231010000100000001000000001008020000100080000080200000800200000804002310110000008040000000000040080400030011000000004000200010000100008007f3a8,0x0,0x0,0x2104c1240481,0x6104c1240481,0x2104c1240481,0x0,0x4104c1240481,0x6104c1240481,0x4104c1240481,0xf381183cc2d907981e7e601e679803ccf3007a823811c08c2d90f301e9cc2d90f303cc3cc079853a626,0x8124c1240481,0x6104c1240481,0x8124c1240481,0x0,0x0,0x80002001040041001001000041000000008040e4,0x80006009140041001001004041000804028140e4,0x0,0x8000a001240041001001008041001008048241e4,0x80002001040041001001000041000000208040e4,0x8001200104004100100101004100201008824be4,0x80002001040041001001000041000001008040e4,0x80022001840041001001020041004020108245e4,0x80002001040041001001000041000000208040e4,0x80042001040041001001040041008040208048e4,0x0],
[0x80082001040041001001080041010080408058e4,0x0,0xf300003cc0f30f3001e6f30079bcc0798f30079801e7e60088b0001e7e6799e607983cc0798798b65556,0x0,0xf301e63cc0798f3001e6f30079bcc0798f30079801e7e6008118001e7e6f31e603cc1e60f307983cd556,0x10220842410e2,0x1022082241502,0xf3000f6cc0010230004093b846f3001e603cc0001e679807987980f31e9cc003db3000f6cc001e64dcf5,0x1022082241502,0x10220842410e2,0x10220842410e2,0xf3000f6cc00102300040c8de60f3000001e60000f307983cc07987981e9cc003db3000f6cc001e64dcf5,0x10220842410e2,0xf3000f6cc00102300042722083b30003d398079f9807987980799e601e9cc003db3000f6cc001e64dcf5,0x80042001040041001020040801080402008048e4,0xf3000f6cc00102300042722083b30003db30079f980799e60079bcc01e9cc003db3000f6cc001e64dcf5,0x80002001040041001040001001080402008040e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_2454 : TreeBound (n := 4) 107 (programCode 0x4a29076066) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x800220004400810010800a200108060200805504]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_2455 : TreeBound (n := 4) 107 (programCode 0x4a29076067) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0xf30b643cc0000f301e61e601e679801e6f3007aec8bddbcc000000001e9cc2d90f300003cc07983cddf6,0x0,0x80002008040041001000800021000000008040e4,0x80006008140041001000804021000804028140e4,0x0,0x8000a008240041001000808021001008048241e4,0x80042008040041001000840021040040208048e4,0x8001200814004100100081002100201008814ae4,0xf30b643cc0798f301e61e601e67980798f3007980489d800fa98000f4ebb22d903cc1e60f307983cde56,0x80022008140041001000820021004020108144e4,0x80042008040041001000840021008040208048e4,0x80042008040041001000840021008040208048e4,0xf307983cc0798f301e60f30079bcc0798f30079800f4e600fa98000f4e6f31e60f301e60f307983cd556,0x80082008040041001000880021010080408058e4,0x80002008040041001000800021080000008040e4,0xf307983cc03ccf301e60f30079bcc0798f30079800f4e600f6cc000f4e6799e607980f307987985b3556,0x0,0xf307983cc0798f301e60f30079bcc0798f30079800f4e600fa98000f4e6f31e603cc1e60f307983cd556,0x0,0x0,0x0,0x0,0x0,0x2104c1240481,0x6104c1240481,0x2104c1240481,0x0,0x4104c1240481,0x6104c1240481,0x4104c1240481,0x0],
[0x8124c1240481,0x6104c1240481,0x8124c1240481,0x0,0x0,0x80002008040041001001000041000000008040e4,0x80006008140041001001004041000804028140e4,0x0,0x8000a008240041001001008041001008048241e4,0x80002008040041001001000041000000208040e4,0x8001200824004100100101004100201008824be4,0x80002008040041001001000041000001008040e4,0x80022008240041001001020041004020108245e4,0x80002008040041001001000041000000208040e4,0x80042008040041001001040041008040208048e4,0x0,0x80082008040041001001080041010080408058e4,0x0,0x0,0x0,0xf307983cc0798f301e60f30079bcc0798f30079801e7e6008118001e7e6f31e603cc1e60f307983cd556,0xf3000f6cc003db30007d53b846f4e63cc03cc0001e679803ccf300799e9cc003db3000f6cc001e68a925,0x8001200844004100100201008108001200844ae4,0x0,0x0,0x0,0x0,0x0,0x210882240481,0x410882240481,0x210882240481,0x210882240481],
[0x410882240481,0x410882240481,0x410882240481,0x210882240481,0x8128c2240481,0x410882240481,0x8128c2240481,0x210882240481,0x80022008840041001004020101080022008844e4,0xf3000f6cc003db30007d88de6102300001e60000f307981e60f303cc1e9cc003db3000f6cc001e68a925,0xf3000f6cc003db30007d4c1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0,0x0,0x0,0x0,0x0,0x211004240481,0x11004240481,0x211004240481,0x411004240481,0x411004240481,0x11004240481,0x411004240481,0x411004240481,0x8130c4240481,0x411004240481,0x8130c4240481,0x411004240481,0xf3000f6cc003db30007d4c1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925,0xf30b643cc0000f301e61e601e679801e6f3007aec8bddbcc000000001e9cc2d90f300003cc07983cddf6,0x0,0x80000008040041001020000801080002008040e4],
[0x16c8000f301e611160f30079bcc0798f300799e601e7e6000204601e9cc1e60f30000b6407983cd556,0x0,0x25f80007983cc20460f30079bcc0798f300799e601e7e60003ea601e9cc1e60f300012fc07983cf3b6,0x211004240481,0x11004240481,0x211004240481,0x411004240481,0x411004240481,0x11004240481,0x411004240481,0x411004240481,0x8138c6240481,0x411004240481,0x8138c6240481,0x411004240481,0x0,0x0,0x0,0x0,0x0,0x2120c8240481,0x6120c8240481,0x2120c8240481,0x8120c8240481,0x4120c8240481,0x6120c8240481,0x4120c8240481,0x8120c8240481,0x8120c8240481,0x6120c8240481,0x8120c8240481,0x8120c8240481],
[0x0,0x0,0x0,0x0,0x25f80007983cc20460f30079bcc0798f30079bcc01e6f3000408c01e9cc1e60f300012fc07983cf3b6,0x210000240481,0x10000240481,0x210000240481,0x10000240481,0x410000240481,0x10000240481,0x410000240481,0x10000240481,0x8120c8240481,0x410000240481,0x8120c8240481,0x10000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_2600 : TreeBound (n := 4) 107 (programCode 0x4a29076068) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x800220008400810010800a200108060200805504]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_2601 : TreeBound (n := 4) 107 (programCode 0x4a29076069) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x80002001040041001080002001080402008040e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_2602 : TreeBound (n := 4) 107 (programCode 0x4a2907606a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x80042001040041001080042001080402008048e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_2603 : TreeBound (n := 4) 107 (programCode 0x4a2907606b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x1204d0204481,0x121010210481,0x1204d0204481,0x0,0x120890208481,0x88002200000000008004200108002000080ce3,0x120890208481,0x88002200000000008004200108002000080ce3,0x121010210481,0x120010200481,0x121010210481,0x120010200481,0x122090220481,0x121890218481,0x122090220481,0x120010200481,0x0,0x0,0x420010210481,0x0,0x0,0x420010208481,0x80402804004100108000600100240008844ae4,0x420010208481,0x804028040041001080006001004400108844e4,0x420010210481,0x420010200481,0x420010210481,0x420010200481,0x420010220481],
[0x420010200481,0x420010220481,0x420010200481,0x0,0x1204d0204481,0x121010210481,0x1204d0204481,0x0,0x120890208481,0x0,0x120890208481,0x0,0x121010210481,0x120010200481,0x121010210481,0x120010200481,0x122090220481,0x121890218481,0x122090220481,0x120010200481,0x0,0x0,0x0,0x0,0x0,0x408de607983cc20461e601e63cc0798f3007b38cf6766f3003cfcc1e9cc2d9c5701e63cc07983cfc26,0x3cc1e6102379820461e600f379803ccf3007980f301e63dc2a98799e9cc001f530b69eec0798bf2436,0x0,0x3cc1e6102379820461e600f379803ccf3007981e601e67a82a98f31e9cc003db30b7552c0798b87f36,0x0,0x3cc1e6102379820461e600f379803ccf30079879801e7e702a9bcc1e9cc0f30f30d4c22c0798b69936,0x0],
[0x3cc1e6102379820461e600f379803ccf300798f3001e9cd02a9f981e9cc0f30f30b6622c0798b69936,0x0,0x3cc1e6102379820461e600f379803ccf30079bcc001f53102ab6601e9cc00088b0b6715c0798b69936,0x0,0x3cc1e6102379820461e600f379803ccf30079f98002046102ad4c01e9cc00088b0b6622c0798b69936,0x0,0x2204c1240481,0x208008200800020008004020108002200080ce3,0x2204c1240481,0x0,0x220882240481,0x220000240481,0x220882240481,0x220000240481,0x221004240481,0x220000240481,0x221004240481,0x220000240481,0x222088240481,0x221004240481,0x222088240481,0x220000240481,0x42200880400810010802a200108062200805504,0x0,0x2204c1240481,0x0,0x2204c1240481,0x0,0x220882240481,0x220000240481,0x220882240481,0x220000240481],
[0x221004240481,0x220000240481,0x221004240481,0x220000240481,0x222088240481,0x221004240481,0x222088240481,0x220000240481,0x42201080400810010802a200108062200805504,0x420010240481,0x20010240481,0x420010240481,0x20010240481,0x822090240481,0x20010240481,0x822090240481,0x20010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_2716 : TreeBound (n := 4) 107 (programCode 0x4a2907606c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x80082002040041001080082001080402008058e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_2717 : TreeBound (n := 4) 107 (programCode 0x4a2907606d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x408c000408c0010233cd1383b300079803d3a730079bcc007a73001e9cc003db3000f6cc001e64dcf5,0x10233cc408c7980798f3408de6102300001e6000f30079bcc00f3f3001e9cc003db3000f6cc001e68a925,0x0,0x1404d0204481,0x141cd0218481,0x1404d0204481,0x0,0x140cd0208481,0x0,0x140cd0208481,0x0,0x1414d0210481,0x141cd0218481,0x1414d0210481,0x110004400002004108004200100002204080ce3,0x1425d0220501,0x142dd0228501,0x1425d0220501,0x1404d0204481,0x0,0x4825e60f300001e601e601e679801e6f3007aecc89fa2c000000001e9cc2d988b00003cc07983cddf6,0x0,0x0,0x0,0xf4e9cc3d39f9800f3f33d3b939f5d93cc03cc0001e679803ccf300799e9cc003db3000f6cc001e68a925,0x101004104004100100201008108001200844ae4,0x0,0x1020040840041001004020101080022008844e4,0x10233cc408c7980798f3408de6102300001e60000f307981e60f303cc1e9cc003db3000f6cc001e68a925,0x1200048040041001008200201080202008241e4,0x0],
[0x1200048040041001010200401080202008241e4,0x1000040040041001000000001080002008040e4,0x16c83cc5b207983cc0f35b22d916c81e60f300016c80798f300f31e601e9cc003db3000f6cc001ea56925,0x16c83cc3cc03cc7980f35b22d916c83cc1e60f307980799e60079bcc01e9cc003db3000f6cc001ede5cf5,0x1e60f307983cc1e610230079bcc0798f30079bcc01e6f3000408c01e9cc1e60f300012fc07983cf3b6,0x1e9cc001e9cc007a733d3b846f3001e601e600f30079bcc007a73001e9cc003db3000f6cc001e64dcf5,0x2040081040041001080042001080402008048e4,0x1e9cc0079bcc00f3f33d3b846f3001e603cc00f30079bcc007a73001e9cc003db3000f6cc001e64dcf5,0x4000100040041001080002001080402008040e4,0x441010240481,0x40010240481,0x441010240481,0x40010240481,0x842110240501,0x842110240501,0x842110240501,0x40010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_2766 : TreeBound (n := 4) 107 (programCode 0x4a2907606e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8020200404008100108028200108060200804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_2767 : TreeBound (n := 4) 107 (programCode 0x4a2907606f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0xf307983cc00000000001e601e679803ccf3007a730811bcc00f3f3001e9cc2d90f30b643cc07983cde26,0x0,0x44580007980000f301e601e679803ccf3007a730811bcc00f3f3001e9cc2d90f30b6400007983cde26,0x441010210481,0x0,0x0,0x441010208481,0x16c8000f30f3016c80f30079bcc0798f3007a73001e9cc001023001e602046001ed98001ed98411ad6,0x441010208481,0x16c8000f31e6016c80f30079bcc0798f3007a73001e9cc001f53001e603ea6000fa98003d3983dc856,0x441010210481,0x441010200481,0x441010210481,0x441010210481,0xc43110220501,0xc43110220501,0xc43110220501,0x441010210481,0x0,0x1404d0204481,0x141cd0218481,0x1404d0204481,0x0,0x140cd0208481,0x0,0x140cd0208481,0x0,0x1414d0210481,0x141cd0218481,0x1414d0210481,0x120004800002004108004200100002204080ce3],
[0x1425d0220501,0x142dd0228501,0x1425d0220501,0x1404d0204481,0x0,0x44580007980001e601e601e63cc0798f3007a730811bcc0000f3001e9cc2d9000079800007983cddc6,0x1004040140041001080006001000c00028140e4,0x4459e607980001e601e601e63cc0798f3007a730813a2c0000f3001e9cd209798079800081183cddc6,0x0,0x0,0x25f800079bcc025f80f30079bcc0798f3007a73001e9cc003db3001e602046001ed98001ed98428756,0x0,0x25f8000799e6025f80f30079bcc0798f3007a73001e9cc001f53001e603ea6000fa98003d3983dc856,0x1000040040041001080002001000400208040e4,0x1040049240041001080042001008400208048e4,0x0,0x108004a240041001080082001010400408058e4,0x0,0x0,0x1000040040041001080002001000400008040e4,0x1e60f3081180020470230079bcc0798f3007a73001e9cc0798f3001e6f3000408c7980f307983cd556,0x1e9cc003db30007b663d3b846f4e63cc03cc00f30079bcc00f3f3001e9cc003db3000f6cc001e68a925,0x0,0x641cc1240481,0xf303cc0000f300001e63cc1e60f300000000001023079c08c0f307981e9cc003db3000f6cc001e68a925,0x641cc1240481,0x0,0x441002240481,0x40000240481,0x441002240481,0x40000240481,0x40004240481],
[0x40000240481,0x40004240481,0x40000240481,0x842108240501,0x842108240501,0x842108240501,0x40000240481,0x0,0x240cc1240481,0x0,0x240cc1240481,0x0,0x240882240481,0x241884240481,0x240882240481,0x240882240481,0x241884240481,0x241884240481,0x241884240481,0x240882240481,0x242988240501,0x24398c240501,0x242988240501,0x240882240481,0x0,0x0,0x0,0x0,0x0,0x240882240481,0x40000240481,0x240882240481],
[0x40000240481,0x40004240481,0x40000240481,0x40004240481,0x40000240481,0x40008240481,0x40008240481,0x40008240481,0x40000240481,0x441010240481,0x40010240481,0x441010240481,0x40010240481,0x842110240501,0x842110240501,0x842110240501,0x40010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_2880 : TreeBound (n := 4) 107 (programCode 0x4a29076070) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8020200804008100108028200108060200804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_1920 : TreeBound (n := 4) 107 (programCode 0x4a290760) := by
  conv in programCode _ => reduce
  exact branchFour (k := (3,0)) (by decide +kernel) part002_1921 part002_1970 part002_2035 part002_2212 part002_2405 part002_2454 part002_2455 part002_2600 part002_2601 part002_2602 part002_2603 part002_2716 part002_2717 part002_2766 part002_2767 part002_2880

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part002_0 : TreeBound (n := 4) 107 (programCode 0x4a2907) := by
  conv in programCode _ => reduce
  exact branchFour (k := (2,1)) (by decide +kernel) part002_1 part002_2 part002_3 part002_4 part002_965 part002_966 part002_967 part002_968 part002_969 part002_970 part002_971 part002_972 part002_973 part002_1118 part002_1343 part002_1920

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem partitioned002 : TreeBound (n := 4) 107 [((0,0),⟨1,1,false⟩),((1,0),⟨2,0,false⟩),((2,0),⟨2,0,true⟩)] := part002_0


set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem zero_write_tree (q : Fin 4) (hq : 2 ≤ q.val) :
    TreeBound (n := 4) 107
      [((0,0), ⟨1,1,false⟩),((1,0), ⟨2,0,false⟩),((2,0), ⟨q,0,true⟩)] := by
  fin_cases q
  · change 2 ≤ 0 at hq
    omega
  · change 2 ≤ 1 at hq
    omega
  · exact partitioned002
  · exact partitioned003

open Turing Turing.BusyBeaver in
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem zero_write_machine (M : Machine (Fin 2) (Fin 4)) (q : Fin 4)
    (hq : 2 ≤ q.val)
    (h0 : M 0 0 = some (some 1, Stmt.write 1 .right))
    (h1 : M 1 0 = some (some 2, Stmt.write 0 .right))
    (h2 : M 2 0 = some (some q, Stmt.write 0 .left))
    (halts : M.IsHalting) : M.HaltsAfter (Machine.init []) 107 := by
  have hm : Matches M
      [((0,0), ⟨1,1,false⟩),((1,0), ⟨2,0,false⟩),((2,0), ⟨q,0,true⟩)] := by
    intro k m h
    simp only [Program.get] at h
    split at h
    next hk =>
      subst k
      cases Option.some.inj h
      simp [ongoing,h0]
    next =>
      split at h
      next hk =>
        subst k
        cases Option.some.inj h
        simp [ongoing,h1]
      next =>
        split at h
        next hk =>
          subst k
          cases Option.some.inj h
          simp [ongoing,h2]
        next => contradiction
  rcases zero_write_tree q hq M hm with h | h
  · exact h
  · exact (h halts).elim

end BeaverBound

/-- Exact zero-write child of the merged initial-sweep reduction. -/
theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H2_R1.H1 := BeaverBound.zero_write_machine
