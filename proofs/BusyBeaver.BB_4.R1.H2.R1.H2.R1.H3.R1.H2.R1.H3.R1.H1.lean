/- Standalone proof component for the one/zero-write Busy Beaver family.
This proves only return states 0. -/
import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H2_R1_H3_R1

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

theorem flip_move (c : Position n) (m : Move n) :
    (c.move m).flip = c.flip.move m.flip := by
  cases m with
  | mk q a d => cases d <;> rfl

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

theorem view_start (n : ℕ) [NeZero n] : (start n).view = Machine.init [] := rfl

def Move.command (m : Move n) : Option (Option (Fin n) × Stmt Symbol) :=
  some (some m.state, Stmt.write m.write (if m.left then Dir.left else Dir.right))

def ongoing [NeZero n] (M : MachineOf n) (k : Key n) : Option (Move n) :=
  match M k.1 k.2 with
  | some (some q, ⟨b, .left⟩) => some ⟨q, b, true⟩
  | some (some q, ⟨b, .right⟩) => some ⟨q, b, false⟩
  | _ => none

theorem ongoing_command [NeZero n] (M : MachineOf n) (k : Key n) (m : Move n)
    (h : ongoing M k = some m) : M k.1 k.2 = m.command := by
  rcases m with ⟨q, a, d⟩
  unfold ongoing at h
  split at h <;> simp_all [Move.command, Move.mk.injEq]

theorem step_move [NeZero n] (M : MachineOf n) (c : Position n) (m : Move n)
    (h : ongoing M (c.state, c.head) = some m) :
    M.step c.view = some (c.move m).view := by
  have he := ongoing_command M (c.state, c.head) m h
  change M c.state c.head = m.command at he
  cases m with
  | mk q a d =>
    cases d <;> simp [Position.view, Machine.step, he, Move.command, Position.move,
      Tape.write, Tape.move, mk_push]

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

theorem matches_empty [NeZero n] (M : MachineOf n) : Matches M [] := by
  intro k m h
  contradiction

theorem matches_add [NeZero n] {M : MachineOf n} {tb : Program n} {k : Key n} {m : Move n}
    (hm : Matches M tb) (h : ongoing M k = some m) : Matches M ((k, m) :: tb) := by
  intro k' m' hh
  by_cases e : k' = k
  · subst k'
    simp [Program.get] at hh
    simpa [← hh] using h
  · apply hm k' m'
    simpa [Program.get, e] using hh

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

theorem TapeDFA.blank (D : TapeDFA) : D.next 0 0 = 0 := by
  apply Fin.ext
  simp [TapeDFA.next]

def TapeDFA.read (D : TapeDFA) (xs : List Symbol) : Fin D.size :=
  xs.foldr D.next 0

theorem TapeDFA.read_push (D : TapeDFA) (a : Symbol) (xs : List Symbol) :
    D.read (push a xs) = D.next a (D.read xs) := by
  unfold push
  split
  · rename_i h
    rcases h with ⟨rfl, rfl⟩
    exact D.blank.symm
  · rfl

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

theorem allFin {n : ℕ} {p : Fin n → Bool} (h : (List.finRange n).all p = true)
    (a : Fin n) : p a = true := (List.all_eq_true.mp h) a (by simp)

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

theorem Reads.push {cert : Certificate n} {p q : Node cert} {a : Symbol} {xs : ListBlank Symbol}
    (he : cert.edge p a q = true) (h : Reads cert q xs) : Reads cert p (xs.cons a) :=
  .step (by simpa using he) (by simpa using h)

theorem Reads.pop {cert : Certificate n} {p : Node cert} {xs : ListBlank Symbol} {a : Symbol}
    (h : Reads cert p (xs.cons a)) : ∃ q, cert.edge p a q = true ∧ Reads cert q xs := by
  cases h with
  | done => exact ⟨none, rfl, .done _⟩
  | step he hr => exact ⟨_, by simpa using he, by simpa using hr⟩

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

theorem holes_add (tb : Program n) (k : Key n) (m : Move n) :
    holes ((k, m) :: tb) = (holes tb).erase k := by
  ext k'
  simp only [holes, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  rw [Program.get]
  by_cases e : k' = k <;> simp [e]

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

theorem upper_cannot_stop [NeZero n] {M : MachineOf n} {tb : Program n} {limit : ℕ}
    (hm : Matches M tb) (h : ¬ CanStop tb (start n)) : Upper M limit := by
  right
  intro halts
  obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp halts
  apply cannot_stop_run hm (start n) h (k + 1)
  rwa [view_start]

abbrev TreeBound [NeZero n] (limit : ℕ) (tb : Program n) : Prop :=
  ∀ M : MachineOf n, Matches M tb → Upper M limit

theorem branch_bound [NeZero n] {limit : ℕ} {tb : Program n} {k : Key n}
    (h : firstMissing tb limit (start n) = some k)
    (children : ∀ m, TreeBound limit ((k, m) :: tb)) : TreeBound limit tb := by
  intro M hm
  cases hs : ongoing M k with
  | none =>
    left
    simpa only [view_start] using firstMissing_stops hm limit (start n) h hs
  | some m => exact children m M (matches_add hm hs)

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

namespace BeaverBound

def forceNat {α : Type} (v : ℕ) (f : ℕ → α) : α :=
  match v with
  | 0 => f 0
  | k + 1 => f (k + 1)

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

theorem state_nodeId_lt (cert : Certificate n) (q : Fin n) (l : Fin cert.dfa.size) :
    nodeId cert (some (q,l)) < n * cert.dfa.size := by
  have hh := Nat.mul_le_mul_right cert.dfa.size (Nat.succ_le_of_lt q.isLt)
  simp only [Nat.succ_mul] at hh
  have hl := l.isLt
  simp only [nodeId]
  omega

theorem nodeId_lt (cert : Certificate n) (p : Node cert) :
    nodeId cert p < n * cert.dfa.size + 1 := by
  rcases p with _ | ⟨q,l⟩
  · simp [nodeId]
  · exact Nat.lt_succ_of_lt (state_nodeId_lt cert q l)

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
private theorem part100_1 : TreeBound (n := 4) 107 (programCode 0x422b0711) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x10840d0204481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_2 : TreeBound (n := 4) 107 (programCode 0x422b0712) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x1084090210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_3 : TreeBound (n := 4) 107 (programCode 0x422b0713) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x10840d0204481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_5 : TreeBound (n := 4) 107 (programCode 0x422b071431) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x10840c1204481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_6 : TreeBound (n := 4) 107 (programCode 0x422b071432) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x80402010080002002000080402000020000814e3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_7 : TreeBound (n := 4) 107 (programCode 0x422b071433) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x10840c1204481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_8 : TreeBound (n := 4) 107 (programCode 0x422b071434) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1084080200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_9 : TreeBound (n := 4) 107 (programCode 0x422b071435) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1084082208481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_10 : TreeBound (n := 4) 107 (programCode 0x422b071436) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x80402010080002002000080002000020000814e3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_11 : TreeBound (n := 4) 107 (programCode 0x422b071437) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1084082208481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_12 : TreeBound (n := 4) 107 (programCode 0x422b071438) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10804c1204481,0x1081084210481,0x10804c1204481,0x1080080200481,0x1080882208481,0x1081084210481,0x1080882208481,0x1080080200481,0x1081084210481,0x1081084210481,0x1081084210481,0x1080080200481,0x0,0xc00030020020802000880802000820020814e3,0x0,0x1400050020020802001080802000020040814e3,0x400010020000802000080802000020000814e3,0x0,0x80400010020000802000080802000020000814e3,0x4400110020080802004080802004020100814e3,0x0,0x0,0x80400010020000802000080802000020000814e3,0x0,0x7981e61e6079879807980f379800007980f379803cc0000f379803cc00001e600007980001e68a055,0x0,0x0,0x0,0x0,0x0,0x382022184642],
[0x182022084642,0x382022184642,0x182022084642,0x382022184642,0x282022184642,0x382022184642,0x282022184642,0x8400210010002002010080402010020400814e3,0x3d39803cde6003d39807980025f8001ed98001e6f300f33cc7980f300f307d4c001e679807983d0f2b6,0x182022084642,0x0,0x0,0x0,0x0,0x0,0x0,0xc00030040021002000881002000820020814e3,0x400410040001002000081002000020000814e3,0x1400050040021002001081002000020040814e3,0x400010040001002000081002000020000814e3,0x0,0x7983cc1e600007981e600007980000f301e600007980001e679803cc00003cc0000f300001e703d95,0x4400110040081002004081002004020100814e3,0x401010040001002000081002000020000814e3,0x0,0x0,0x0,0x401010040001002000081002000020000814e3,0x0,0x0,0x0,0x0],
[0x0,0x382022184642,0x182022084642,0x382022184642,0x182022084642,0x382022184642,0x282022184642,0x382022184642,0x282022184642,0x0,0x3d39803cde6003d3980f3000222c001f530001e6f300f33cde600f300f308118001e679807983dc56b6,0x182022084642,0x0,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_93 : TreeBound (n := 4) 107 (programCode 0x422b071439) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10804c4214481,0x1081084210481,0x10804c4214481,0x1081084210481,0x1080884218481,0x1081084210481,0x1080884218481,0x1080084210481,0x1081084210481,0x1081084210481,0x1081084210481,0x1080084210481,0x0,0x40000000300000000c0000000300000000840020000100000008400018001000060000400100001000400004000800010001004000001010000004004000008001000010010873227,0x4000000090000000240000000900000000c000000090004000240000000800080000c000200010004800200000000800080001000100000000480020002000080002000400026aba8,0x0,0x0,0x0,0x0,0x4000001010000004040000008100000010040020000100000100400018001000060000400100001000400004000800010001004000001010000004004000008001000010010873227,0x4000020010000080040000200100000800040020000100008000400018001000060000400100001000400004000800010001004000001010000004004000008001000010050873227,0x40002001100008000400000001000000024002000110000000440000000200000000c002200110000800000000000000040001000220010000800000001000100002000200017fe28,0x0,0x0,0x0,0x4000020010000080040000200100000800040020000100008000400018001000060000400100001000400004000800010001004000001010000004004000008001000010050873227,0x0,0x4000100010000400040000800100001000040020000100010000400018001000060000400100001000400004000800010001004000001010000004004000008001000010390873227,0x0,0x0,0x8000600018008010200808020200c020200814e3],
[0xf300003cc01e6f30079bcc0000f3007980001e603cc7980f31e603cc3cc00003cc0000f30f301e703d95,0x8000a00028008010200808020200c020200814e3,0xf30079bcc0000f3007980000f3f3003cc1e60f303cc3cc3cc0f303cc3cc3cc01e6000079bcc01e68a055,0x0,0xf30079bcc01e6f30079bcc0000f3007980001e603cc7980f31e603cc3cc00003cc0000f30f301e703d95,0x0,0x0,0x0,0x4000008010000008040000080100000080100000008100000009000000081000000080402000100000004004020000000200010000a000000088000000082004000200010440db1a8,0x40000100100000100400001001000001004000000000000040040000100008000400010001000010001000100010000100010000000010004000010000000100040000100208793a7,0x0,0x4000020010000080040000200100000800400020001000008004000018001000060000400100001000400004000800010001004000001010000004004000008001000010050873227,0x0,0x400010001000040004000080010000100040002000100004000400001800c000060000400100001000400004000800010001004000001010000004030000008001000010210873227,0x0,0x0,0x40000000300000000c0000000300000000a00020000800000009000018002000060000400100001000400004000800010001004000001010000004008000008001000010010873227,0x0,0x0,0x4000200010000800040000400100000080200020000800010001000018002000060000400100001000400004000800010001004000001010000004008000008001000010090873227,0x0,0x40000008100000020400000081000000084000000090004000240000000800080000c000200010004800200000000800080001000100000000480020002000080002000400026aba8,0x0,0x4000040010000100040000400100006000200020000800010001000018002000060000400100001000400004000800010001004000001010000004008000008001000010090873227,0x0,0x4000000010000000040000000100008000200020000800000001000018002000060000400100001000400004000800010001004000001010000004008000008001000010010873227,0x4000010010000040040000080100000100200020000800002001000018002000060000400100001000400004000800010001004000001010000004008000008001000010010873227,0x0,0x4000020010000080040000200100000800200020000800008001000018002000060000400100001000400004000800010001004000001010000004008000008001000010050873227,0x0,0x4000100010000400040000800100001000200020000800020001000018002000060000400100001000400004000800010001004000001010000004008000008001000010310873227,0x0],
[0x0,0x80006000180080202008080202008020200814e3,0x0,0x8000a000280080002008080202000020200814e3,0x80002001080080002008080202000020200814e3,0x80012000480080202008080202008020200814e3,0x0,0x80022000880080202008080202008020200814e3,0x0,0x80042001080080002008080202000020200814e3,0x4000008010000008040000080100000080080000008800000008800000082000000081002000100000004010020000000200010000a000000088000000090004000200012100db1a8,0x0,0x0,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_174 : TreeBound (n := 4) 107 (programCode 0x422b07143a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10804c621c481,0x1081084210481,0x10804c621c481,0x1081084210481,0x1080884218481,0x1081084210481,0x1080884218481,0x1080084210481,0x1081084210481,0x1081084210481,0x1081084210481,0x1080084210481,0x0,0x80006000120020802000880502000820020814e3,0x0,0x8000a000220020802001080502000020040814e3,0x80002000020000802000080002000020000814e3,0x40000002100000008400000081000000080400000001000040010000040010000400000401000020001000004010000000010000000010000100010000000100001000100208713a7,0x80002000020000802000080002000020000814e3,0x80022000820080802004080402004020100814e3,0x0,0x400000801000002004000008010000008010000020040008680100001000100004000100008010d000200004001000010001004000000815d0000200400001000100001002486aba7,0x80002000020000802000080002000020000814e3,0x4000010010000040040000080100000100040020000100001000400000001000060000800100002000400008000801020001004000001010000004004000008002000010018873227,0x0,0x0,0xf300f33cc0f30f300f30798002d90001ed98001e9cc00f6cde6003cc00f3097e0001f530007983ea93b6,0x0,0xf301e63cc0798f301e60f30002d90001f530001e9cc00f6cde6003cc00f3097e0002046000798408f3b6,0x0,0x0],
[0xf30000b6400088b000081180025f8001ed98001e9cc00f6cde6003cc00f3097e0001f530007983ea93b6,0x0,0xf300012fc00088b0001023000408c000fa98001ed9f9801e7e679bcc00f308118004731f307987d51426,0xf307983cc0002d900f307980025f8001ed98001e9cc00f6cde6003cc00f3097e0001f530007983ea93b6,0xf3000408c003db30003d3980025f8001ed98001e9cc00f6cde6003cc00f3097e0001f530007983eb0d36,0xf307983cc03ccf30000fa980025f8001ed98001e9cc00f6cde6003cc00f3097e0001f530007983ea93b6,0x0,0xf307983cc1e64bf0000fa980025f8001ed98001e9cc00f6cde6003cc00f3097e0001f530007983ea93b6,0xf3001e9cc01e6f3001e67980025f8001ed98001e9cc00f6cde6003cc00f3097e0001f530007983ee5fb6,0xf300012fc1e60f30000fa980025f8001ed98001e9cc00f6cde6003cc00f3097e0001f530007983ea93b6,0x0,0x0,0xf301e63cc0798f300f30f3000408c000fa98001ed9f9801e7e679bcc00f308118004731f307987d51426,0x0,0xf301e63cc0f30f301e60f3000408c000fa98001ed9f9801e7e679bcc00f308118004731f3079884e9426,0x0,0x80006000140021002000880502000820020814e3,0x80002002040001002000080002000020000814e3,0x8000a000240021002001080502000020040814e3,0x80002000040001002000080002000020000814e3,0x1dcd65ee6cb2e17a40003d77a0500000773594000059682f00000773646d061d77a050000ee6b28ee6b6577a0500003b9aca000003c1200826c8dbe89a09aca077359400ee729b5940000077359401dcd6caef4636830dcd651dcd6c7359400000ee6b2800000ee6b45cd6665a096a,0x80002000040001002000080002000020000814e3,0x80022000840081002004080402004020100814e3,0x80002008040001002000080002000020000814e3,0x0,0x80002000040001002000080002000020000814e3,0x0,0x0,0x0,0x0,0x0,0x0],
[0x0,0xf303cc3cc352cbf03cc0f300044580010230001ed9f9801e7e679bcc00f3088b0004a0af30798811d426,0x0,0xf3000222c1e688b000204600044580010230001ed9f9801e7e679bcc00f31023000463fe60798811d936,0xf3000222c00088b000111600044580010230001ed9f9801e7e679bcc00f31023000463fe60798811d936,0xf307983cc0002d901e60f3000222c001f530001e9cc00f6cde6003cc00f3097e0002046000798408f3b6,0xf3000408c003db30003db3000222c001f530001e9cc00f6cde6003cc00f3097e000204600079840ad9b6,0xf303cc3cc352cbf0001f5300044580010230001ed9f9801e7e679bcc00f3088b0004a0af30798811d426,0x0,0xf300003cc352cbf0001f5300044580010230001ed9f9801e7e679bcc00f3088b0004a0af30798811d426,0xf3001e9cc01e6f3001e6f3000222c001f530001e9cc00f6cde6003cc00f3097e000204600079841823b6,0x0,0x0,0x0,0xf301e63cc0798f300f30f300044580010230001ed9f9801e7e679bcc00f3088b0004a0af3079884e9426,0x0,0xf301e63cc0f30f301e60f300044580010230001ed9f9801e7e679bcc00f3088b0004a0af3079884e9426]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_255 : TreeBound (n := 4) 107 (programCode 0x422b07143b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10804c4214481,0x1081084210481,0x10804c4214481,0x1081084210481,0x1080884218481,0x1081084210481,0x1080884218481,0x1080084210481,0x1081084210481,0x1081084210481,0x1081084210481,0x1080084210481,0x0,0x40000000300000000c000000030000000084002000010000000840020002100006000200010000800040001000080002000100400000101000000400400000800c000010010873227,0x0,0x0,0x0,0x40002001100000000400000009000000024002000110000000440000000200000000c002200110000800000000000000020001000220010000800000001000080002000200017fe28,0x0,0x400000101000000404000000810000001004002000010000010040020040100006000200010000800040001000080002000100400000101000000400400000800c000010010873227,0x400002001000008004000020010000080004002000010000800040022000100006000200010000800040001000080002000100400000101000000400400000800c000010050873227,0x40002001100008000400000001000000024002000110000000440000000200000000c002200110000800000000000000020001000220010000800000001000080002000200017fe28,0x40000100100000400400000201000000804002000110000000440000000200010000c002200110000800000008000400020001000220010000800020001000080002000200017fe28,0x0,0x1dcd6500000773597b9acbdcd660c389473597b9acbdcd65773594ee6b283b9bb86b2800000ee6b6b49be459aca000003b9aca773595dcd65ee6b2f73597b9acbdcd65ee6b36e6b2f73594ee6b2f7359b735941deb326500077bc277c141ddc4bb2800ee6c166b280ee6ee94cc5da9,0x400002001000008004000020010000080004002000010000800040022000100006000200010000800040001000080002000100400000101000000400400000800c000010050873227,0x0,0x400010001000040004000080010000100004002000010001000040024000100006000200010000800040001000080002000100400000101000000400400000800c000010390873227,0x0,0x0,0x182021084222],
[0x182021084222,0x182021084222,0x182021084222,0x182021084222,0x282023184642,0x182021084222,0x282023184642,0x8400210010002002010080402010020400814e3,0x0,0x182021084222,0x0,0x0,0x0,0x0,0x0,0x0,0x40000000300000000c0000000300000000a0002000080000000900020002200006000200010000800040001000080002000100400000101000000402000000800c000010010873227,0x0,0x0,0x0,0x0,0x0,0x0,0x400010001000040004000080010000600020002000080004000100030000200006000200010000800040001000080002000100400000101000000402000000800c000010210873227,0x0,0x400000001000000004000000010000800020002000080000000100020000200006000200010000800040001000080002000100400000101000000402000000800c000010010873227,0x0,0x0,0x400002001000008004000020010000080020002000080000800100022000200006000200010000800040001000080002000100400000101000000402000000800c000010050873227,0x0,0x400010001000040004000080010000100020002000080004000100030000200006000200010000800040001000080002000100400000101000000402000000800c000010210873227,0x0],
[0x0,0x182021084222,0x182021084222,0x182021084222,0x182021084222,0x182021084222,0x282023184642,0x182021084222,0x282023184642,0x0,0x0,0x182021084222,0x0,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_336 : TreeBound (n := 4) 107 (programCode 0x422b07143c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10804c1204481,0x1081084210481,0x10804c1204481,0x1080080200481,0x1080882208481,0x1081084210481,0x1080882208481,0x1080080200481,0x1081084210481,0x1081084210481,0x1081084210481,0x1080080200481,0x0,0xc00030020020802000880822000820020814e3,0x0,0x1400050020020802001080842000020040814e3,0x400010020000802000080802000020000814e3,0x0,0x80400010020000802000080802000020000814e3,0x4400110020080802004080802004020100814e3,0x0,0x0,0x80400010020000802000080802000020000814e3,0x0,0x802000002008000020020000020080000000400030000000080010000900000000808000004020000010200200040200000100008000200028004000200008000200040002513a8,0x0,0x0,0x0,0x0,0x0,0xf300003cc0f30f30b6407980025f8001ed98001ed9800f4e7e60079800f3097e000222c000798445b3b6],
[0xf30000b6400088b000081180025f8001ed98001ed9800f4e7e60079800f3097e000222c000798445b3b6,0x0,0xf300012fc00088b0001023000408c000fa98001ed9f9803cde679f9800f30811800463ef307987d51426,0x0,0xf3000408c003db30003d3980025f8001ed98001ed9800f4e7e60079800f3097e000222c0007984462d36,0x0,0x0,0x0,0xf3001e9cc01e6f3001e67980025f8001ed98001ed9800f4e7e60079800f3097e000222c0007984497fb6,0xf300012fc1e60f30000fa980025f8001ed98001ed9800f4e7e60079800f3097e000222c000798445b3b6,0x0,0x0,0xf301e63cc0798f300f30f3000408c000fa98001ed9f9803cde679f9800f30811800463ef307987d51426,0x0,0xf301e63cc0f30f301e60f3000408c000fa98001ed9f9803cde679f9800f30811800463ef3079884e9426,0x0,0xc00030040021002000881022000820020814e3,0x400410040001002000081002000020000814e3,0x1400050040021002001081042000020040814e3,0x400010040001002000081002000020000814e3,0x0,0x0,0x4400110040081002004081002004020100814e3,0x401010040001002000081002000020000814e3,0x0,0x0,0x0,0x401010040001002000081002000020000814e3,0x0,0x0,0x0,0x0],
[0x0,0xf303cc3cc2d988b03cc1e600044580010230001f5379803cde679f9800f310230004825e60798811d936,0x0,0xf3000222c1e688b000204600044580010230001f5379803cde679f9800f310230004825e60798811d936,0xf300012fc00088b000102300044580010230001ed9f9803cde679f9800f308118004824f307987d51426,0x0,0xf3000408c003db30003db3000222c001f530001ed9800f4e7e60079800f3097e000204600079840ad9b6,0xf303cc3cc2d988b000204600044580010230001f5379803cde679f9800f310230004825e60798811d936,0x0,0xf300003cc2d988b000204600044580010230001f5379803cde679f9800f310230004825e60798811d936,0xf3001e9cc01e6f3001e6f3000222c001f530001ed9800f4e7e60079800f3097e000204600079841823b6,0x0,0x0,0x0,0xf301e63cc0798f300f30f300044580010230001ed9f9803cde679f9800f308118004824f307987d51426,0x0,0xf301e63cc0f30f301e60f300044580010230001ed9f9803cde679f9800f308118004824f3079884e9426]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_417 : TreeBound (n := 4) 107 (programCode 0x422b07143d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x16c80005b200016c83cc001f5307983cc02d91e603cc7981e61e603cc79801e600f3f379801e703885,0x0,0x1e934de11f280f04bb7fca0077447ab2f73597b9aca03c12edff280007b07fd9e569dcf458ffca7736826b280861c468000077adb8ed93283b9b059aca00ee7a0eb283b9ad8e6b287735a2e6b2877421e6c6c699759401dcd8308ffca0077359b73594ee7a0eb2800ee6ee95a9fc09,0x7983cc1e600f37980000000f3079803cc1e61e607987981e61e603cc00003ccf300f379801e703d95,0x1ed983cc1e600f3798000f33cc044580007b661e607987981e61e603cc00f33ccf300f379801e722395,0x7983cc1e600f379800000000f379807981e61e607987981e61e603cc00003ccf300f379801e703d95,0x0,0x0,0x1e9690582b280ee6ee1aca0077447ab2f73597b9aca03b9bb86b2800eea8551ed383b9ca6d650ee6b36e6b29ddc4bb28001dcddc36826b283b9b059aca00ee7a0eb283b9ad8e6b287735a2e6b2877421ee8c14af3594773595e08ffca0077359b73594ee7a0eb2800ee6ee95a9fc09,0x7983cc1e600f379803cc0000f379803cc1e61e607987981e61e603cc3cc03ccf300f379801e703d95,0xf37983cc1e600f379800f31e603d39800f31e61e607987981e61e603cc0f303ccf300f379801e703d95,0x16c80005b200016c800f3001e9cc007a73001ea08de610237a730000f30f3811844580007a011c2356,0x7983cc1e600f379803cc0000f379801e61e61e607987981e61e603cc3cc03ccf300f379801e703d95,0x16c80005b200016c803cc001f530007b66001f56d3983db4e6f30000f30f4ed9844580007b6da78756,0x0,0x12000000018000000120000000180001000000081000000090000000810000000800080003000000010002000030000000100020001000020001000220000000200040002793a8,0x0,0x120000000180000001200000001800020000000820000000a0000000820000000800080009000000010002000090000000100020001000020001000220000000200040002793a8,0x445800111600025f83cc003db307983cc01e61e607987981e61e603cc0079bcc01e6f379801e722395,0x0,0x80c0a8220481,0x824088220481,0x80c0a8220481,0x844188220501,0x8140c8220481,0x824088220481,0x8140c8220481,0x0,0x824088220481,0x20400800080002002020080802020020800814e3,0x824088220481],
[0x7980001e61e607987983cc00f3f300003cc00f31e603cde600f31e603cde6001ed98007b66001e68a055,0x844188220501,0x804088220481,0x844188220501,0x844188220501,0x0,0x20c0a8228481,0x224088228481,0x20c0a8228481,0x2541c8228501,0x2140c8228481,0x224088228481,0x2140c8228481,0x0,0x224088228481,0x2400082080082002020080802022020800814e3,0x224088228481,0x0,0x244188228501,0x224088228481,0x244188228501,0x2541c8228501,0x40002000000008000400020001000080004000000010000040040002000100000400100001000100001001000010001000010000000010040000010000000100400000100208793a7,0xfa98007b66000fa983cc01e6f307983cc02d91e603cc7981e61e603cc79801e60f30f379801e703885,0x0,0x16c80005b200016c80003cde6016c80003f991e603cc7981e61e603cc79801e600f3f379801e703885,0x240011000080402010100a040200c04040100a4,0x44580011160004458000f33cc044580007b661e607987981e61e603cc00003cc03ccf379801e722395,0x7980001e60000798000000000079807982d91e603cc7981e61e603cc00001e60000f379801e703885,0x0,0x0,0x202000000208000000c200000030800000202160000800100000420000002000802000010008000040010000020010000100342c00100100000400008000204000001000487fca7],
[0x7980001e60000798000000000079800003529e601e67981e61e603cc00000f30000f379801e703375,0x240011000080402010100a040200c04040100a4,0x2400110008004200108042241200c44041108a4,0xf379803cde600f379803cc0000f379801e61e61e607987981e61e603cc3cc03ccf300f379801e703d95,0x2400110008004400108042442200c44043118a4,0x0,0x2400110020004800104022140a00c24040904a4,0x0,0x7980001e6000079800000000007983cc02d91e603cc7981e61e603cc00001e60000f379801e703885,0x40002000100048000400020000000880004000000090000000240000000900000000c000200010004800200002000100000001000100000000480020002200000002000400026aba8,0x0,0x1000000404008002010000000010000014000000090000000240000000900000000800120001000480020000600000000000100010000400048002000200000000200040002eaba8,0xf300003cc01e6000079bcc0000f30079bcc01e61e607987981e61e603cc00003cc0000f379801e703d95,0x200000000000000808020202000000010000000000000000408000000000000020200808080000000400000400000000004200000000000000080040000000000000a0000000000000000800000004010101020000000000400000800000000000001020000000000800000800000000010000020000000000000010800000000002000001000000000800000200000000010000008000000000400000040000000020000004000000000400000040000000004000000800000000080000008000000000800000000000000008000a020202000001000080000000000040000000000000002000010000000000040001000000000000400000010000000008000200000000000080001100403dedb77ac6d2f,0x80100804080102002020080802020020800834e3,0x1000001004008007010000000010000004000000090000000240000000900000000800120001000e80020000600000000000100010000400048006000200000000200040002eaba8,0x80000000080002002020080802000020800814e3,0x1000000404008006010000010010000044000000090000000240000000900000000800120001000e80020000600000002000100010000400048006000200010000200040002eaba8,0x0,0x1002000004008002010020000010000044000000090000000240000000900000000800120001000480020000600000002000100010000400048002000200010000200040002eaba8,0x80400000080002002020080802000020800814e3,0x1002000004008002010020000010000014000000090000000240000000900000000800120001000480020000600000000000100010000400048002000200000000200040002eaba8,0x3cc1e600007983cc00f3f300003cc00f31e603cde600f31e603cde6001e600007b66001e68a055,0x80100804080102002020080802020020800834e3,0x3ccf303ccf3003ccf33cc0002d9000222c0002046000f305b201e6000f3097e0001e7f5307983cfffb6,0x1002000004008000010020000010000004000000090000000240000000900000000800120001000480020000600000000000100010000400048002000200000000200040002eaba8,0x3cde603cc79803cde63cc0002d9000222c000222c000f305b203cc000f3097e0001eda7307983db63b6,0x0,0x200000020800000081000000202000000c0002000100000000c000000030000060004000100010000400040000800100001004000001010000004000800008010000010010873227,0x0,0x0,0x200200000800800001000040002000800400020001000008004000020010000060004000100010000400040000800100001004000001010000004000800008010000010050873227],
[0x200000200800000801000002002000008400020001000000084000000210000060004000100010000400040000800100001004000001010000004000800008010000010018c73227,0x0,0x200001000800004001000008002000010400020001000000104000000410000060004000100010000400040000800100001004000001010000004000800008010000010010873227,0x0,0x40002000100048002400020000000200044000000090000000240000000900000000c000200010004800200002000000000001000100000000480020002000000002000400026aba8,0x40000080100040200400000800000200804000000090000000240000000900000000c00020001000480020000a000000010001000100010000480020002000040002000400026aba8,0x200010000800040001000080002000100400020001000001004000004010000060004000100010000400040000800100001004000001010000004000800008010000010018873227,0x7736826b281dcd65000007736826b28077394daca00ee7a0eb2f73597c893704d6503b9b41359400001dcd65f224dc1359403b9bb86b283b9b059aca0ee6b9f35943b9ad1735943b9ad8e6b287740ded345077447ab2801dd4f626a50773d2526a50773d0759400ee6d0c8543499,0x200020000800080001000200002000800400020001000008004000020010000060004000100010000400040000800100001004000001010000004000800008010000010050873227,0x40000800100042000400008000000208004000000090000000240000000900000000c00020001400480020000a000010000001000100010000480020002000040002000400026aba8,0x200100000800400001000800002001000400020001000010004000040010000060004000100010000400040000800100001004000001010000004000800008010000010390873227,0x0,0x0,0x798000b6400088b0000b6400f3f30000b6400f31e603cde600f31e603cde6001ed98007b66001e68a055,0x0,0x12fc0004bf00012fc00f3f300012fc00f31e603cde600f31e603cde6001e600007b66001e68beb5,0x3cc3cc0000f303cc3cc00f3f303cc3cc00f31e603cde600f31e603cde6001e600007b66001ee22055,0x7736826c1688f5a09aca00ee7a0eb280ee6b2800000ee6b28007735940003d77a050000f5de8140001faa3b50000430e234000059684dbbd11dde88eef4459aca000001dcd6718711a0000000001dcd6caef4459acbdcd659502fa2a05f20000ee6b2800000ee6b45cd666598c6a,0x3cc0000f300003cc00f3f300003cc00f31e603cde600f31e603cde6001e600007b66001e68a055,0x798007d4c001f530007d4c00f3f30007d4c00f31e603cde600f31e603cde6001ed98007b66001e68a055,0x0,0x0,0x3cc1e60f300003cc00f3f300003cc00f31e603cde600f31e603cde6001e600007b66001e68a055,0x0,0x3cc1e60f307983cc00f3f300003cc00f31e603cde600f31e603cde6001e600007b66001e68a055,0x0,0x0,0x0,0x0,0x0,0x80c0a8220481,0x824088220481],
[0x80c0a8220481,0x844188220501,0x8140c8220481,0x824088220481,0x8140c8220481,0x0,0x824088220481,0x20400800080002002020080802020020800814e3,0x824088220481,0x0,0x844188220501,0x804088220481,0x844188220501,0x844188220501,0x0,0x14804100180086002020080802024020800814e3,0x1e6000079bcc0000f30079bcc01e61e607987981e61e603cc00003cc0000f379801e703d95,0x1500810028008a002020080802024020800815e3,0x844188220501,0x84000200200000800040002002000008400020001000000084000000210000060004000100010000400040000800100001004000001010000004000800008010000010018c73227,0x80002002020080802000020800814e3,0x0,0x0,0x0,0x0,0x800100000000100008001000020001004000000010000040040000040100000400100001000100001001000010001000010000000010040000010000000100400000100208793a7,0x0,0x844188220501,0x4088220481,0x844188220501,0x4088220481,0x0],
[0x80c0a8220481,0x824088220481,0x80c0a8220481,0x844188220501,0x8140c8220481,0x824088220481,0x8140c8220481,0x1e61e61e607983cc97e3cc0798f3097e3cc0aea9e601e67981e61e603cde6000f6cc00f379801eacf375,0x824088220481,0x0,0x824088220481,0x0,0x844188220501,0x804088220481,0x844188220501,0x844188220501,0x0,0x80c0a8220481,0x0,0x80c0a8220481,0x44188220501,0x8140c8220481,0x80002002020080802000020800814e3,0x8140c8220481,0x0,0x0,0x0,0x0,0x0,0x44188220501,0x4088220481,0x44188220501],
[0x4088220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_610 : TreeBound (n := 4) 107 (programCode 0x422b07143e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0xc00030080082002004082002004020100814e3,0x400410080002002000082002000020000814e3,0x1400050080082002004082002004020100814e3,0x400010080002002000082002000020000814e3,0x0,0x2400090000820022010082002010820400814e3,0x2400090000000402010082002000020400814e3,0x2400090001020042010082002001020400814e3,0x2400090000000402010082002000020400814e3,0x4200000010800000042000000108000000420000001001000004000000010060000800100002000400008000801000001004000001010000004000040008002000010018873227,0x0,0x2400090004080102010082002014020400814e3,0x0,0x2400090008080202010082002008020400814e3,0x2400090000000002010082002000020400814e3,0x2400090010000402010082002010020400814e3,0x2400090000000002010082002000020400814e3,0x0,0x2400090010002002010082002010020400814e3,0x0,0x0,0x10d9b983cc1e600007983cc21b37300003cc007a8d9479800007a73003d036503cc00003cc0001e64dc35,0x0,0x180428084222,0x180428084222,0x180428084222,0x180428084222,0x0,0x180828484222,0x180428084222,0x180828484222],
[0x180428084222,0x581028284a62,0x180428084222,0x581028284a62,0x0,0x182028084222,0x0,0x182028084222,0x0,0x800100000000000020004000000000000800100000000000040004000000000000800100000000000010004000000000000100100000000000001004000000000000800000000008ac007020000000100000100000000001000000000000000102b001c0800000004008000000000000040000004000000000400001000000000004100000000000000020000000560030100200000000000800020000000000000200800000000400004008000000000000080080000001000000000800000000000008000000800000400000000020520038100000000800000800000000040020000100000000800000200000000010000020000000000100000020000000001000000020000140139eda7db58d30,0x280428084642,0xfa98002046000fa9825ff983cd0232046798222c00111600206463ccf3088b3cc0f3bdd879a0470976,0x280428084642,0x0,0x0,0x0,0x0,0x0,0x281028284e82,0x280428084642,0x281028284e82,0x0,0xf307983cc1e600007983cc21390000003cc007a730079800007a73003cfcc003cc00003cc0001e64dc35,0x0,0xf307983cc1e600007983cc21390000003cc007a730079800007a73003cfcc003cc00003cc0001e64dc35,0x0,0x180428084222,0x180428084222,0x180428084222,0x180428084222,0x0,0x1400050002004080120100800201008040201e4],
[0x180428084222,0x20400050004004100120100800201008040201e4,0x180428084222,0x581028284a62,0x180428084222,0x581028284a62,0x0,0x8400210010002002010082002010020400814e3,0x0,0x0,0x3d39803cde6003d3983cc0002d9000222c00020460011161e601e6000f3097e0001e7e6007983cfffb6,0x10400410080002002000082002000020000814e3,0x0,0x481428284a62,0x480428084a62,0x480428084a62,0x480428084a62,0x0,0x480828484a62,0x481428284a62,0x480828484a62,0x481428284a62,0x481028284a62,0x480428084a62,0x481028284a62,0x0,0x0,0x0,0x0,0x0,0x80c0c320c481,0x0],
[0x80c0c320c481,0x804080200481,0x400000201000000804000002010000008400020001000001004000004010000060000040100000100400000400800020001004000001010000004000800008000100010018873227,0x20000800080002002000080002000020000814e3,0x20020800880082002004080402004020100814e3,0x0,0x0,0x20400800080002002000082002000020000814e3,0x0,0x0,0x844188220501,0x804080200481,0x844188220501,0x844188220501,0x0,0x0,0x2080002002000080002000020000814e3,0x0,0x4080200481,0x10400480002002000080402000020000814e3,0x80002002000080002000020000814e3,0x20400880002002000080402000020000814e3,0x0,0x40401080002002000080402000020000814e3,0x109d04e4001e600000003cc2139f300003cc00f409c87980000f300003d027203cc00007980001e68a8c5,0x80002080002002000080002000020000814e3,0x0,0x844188220501,0x4080200481,0x844188220501,0x4080200481,0x0],
[0x80c0c320c481,0x40001002080002002000080002000020000814e3,0x80c0c320c481,0x804080200481,0x2000000208000000810000002020000008400020001000001004000004010000060000040100000100400000400800020001004000001010000004000800008000100010018873227,0x40001000080002002000080002000020000814e3,0x40021000880082002004080402004020100814e3,0x0,0x0,0x0,0x0,0x0,0x844188220501,0x804080200481,0x844188220501,0x844188220501,0x0,0x4000180002002000080102000020000814e3,0x0,0x8000280002002000080102000020000814e3,0x4080200481,0x400000081040000204000000800200000840000000100008200400000001000004004000008010400020000000100002000100000000081040000200000001000000001002086aba7,0x80002002000080002000020000814e3,0x20000880002002000080402000020000814e3,0x0,0x0,0xf3084e4001e600000003cc2139f300003cc00f409c87980000f300003d027203cc00007980001e68a8c5,0x0,0x0,0x44188220501,0x4080200481,0x44188220501],
[0x4080200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_771 : TreeBound (n := 4) 107 (programCode 0x422b07143f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x16c80005b200016c83cc001f5307983cc02d93cc03cde601e63cc03ced9001e600f3f5d9001e703885,0x7983cc1e600f37983cc0000f307983cc01e67980799e601e63cc03cc00003cc0000f4e6001e703d95,0x445800111600025f83cc003db307983cc01e67980799e601e63cc03cc00003cc03ccf4e6001e722395,0x7980001e60b647983cc0000f307983cc02d93cc03cde601e63cc03cc00001e60000f5d9001e703885,0x0,0x20c0a8228481,0x224088228481,0x20c0a8228481,0x2541c8228501,0x2140c8228481,0x224088228481,0x2140c8228481,0x2010090080092002040081002042021000816e3,0x224088228481,0x0,0x224088228481,0x0,0x244188228501,0x224088228481,0x244188228501,0x2541c8228501,0x0,0x804120180026002040081002040821000814e3,0x2080002002040081002000021000814e3,0x100814028002a002040081002001021000815e3,0x8080002002040081002000021000814e3,0x2010480480092002040081002042021000816e3,0x80002002040081002000021000814e3,0x40205008800a2002040081002044021000814e3,0x10080002002040081002000021000814e3,0x0],
[0x0,0x0,0x0,0x20100804080102002040081002020021000834e3,0x80002002040081002000021000814e3,0x40201008080202002040081002040021000854e3,0x80002002040081002000021000814e3,0x1ed98002046000fa983cc2139f307983cc0079f980798798079bcc03cee27e3cc0f303d39801e64dc35,0x7980001e60f307983cc0000f307983cc02d93cc03cde601e63cc03cc00001e60000f5d9001e703885,0x0,0x0,0xc0003000080402010100a040200c04040100a4,0x3d39800f4e6003d398000f522c044580007b667980799e601e63cc03cc0fa9bcc3cc0f4e6001e722395,0xf379803cde6003d398315e13903d3980798079f980798798079bcc03cf15c03cc3cc03d39801e64dc35,0x0,0x3b9bb86b2801dd11eaca03b9bb86b2801dd11eaca0077447ab2f73594000000000003b9b4135940ee6d04d65ee6b2f9126a62a06e06b283b9ad1735941dce536b283b9ad8e6b283b9ae7cd6507735940000077447ab28003b9aca00007735cf9aca07780157c800ee747fdc6a289,0x0,0x3d39800f4e6003d39800f31e603d39800f31e67980799e601e63cc03cc0f303cc3cc0f4e6001e703d95,0xc0003000080402010100a040200c04040100a4,0xc00230008004200109042041200c04041108a4,0xf379803cde6003d39803ce13903d39801e6079f980798798079bcc03cf15c03cc3cc03d57e01e64dc35,0xc00630008004400119042042200c04043118a4,0xf379803cde6003d3981e621397987980798079f980798798079bcc03cf15c03cc3cc03d39801e64dc35,0x0,0x0,0x0,0x0,0xfa98003ea610237980003ea60016c80003f993cc03cde601e63cc03cde6001e60f30f5d9001e703885,0x0,0x110ee18002046004c698001151cd016cbcc079f9f980798798079bcc03d397c37cc4bf03d39f99e64dc35,0x7983cc1e60f3079800000000007981e601e67980799e601e63cc03cc00003cc0000f4e6001e703d95,0x0],
[0x0,0x40200010f0080000200200000a00800000040100000408780002020000002004000400002004000020020000100020000100000800021fff000200040001008000001002084aba7,0x7980001e60f30798000000000079800002d93cc03cde601e63cc03cc00001e60000f5d9001e703885,0xf379803cde6102379800f31e603d39800f31e67980799e601e63cc03cc0f303ccf300f4e6001e703d95,0x8400210008004200108042201200c40041108a4,0x7983cc1e60f3079803cc0000f379801e61e67980799e601e63cc03cc00003cc0000f4e6001e703d95,0x8400210008004400110042402200c40043118a4,0x0,0x200010600800040002000000008000400000001060083000000200010000040008000040040000200200001000200001000000000416600002000000010080000010020852ba7,0x0,0x200010600800040002000000008000400000001000083000000200010000040008000040040000200200001000200001000000000416600002000000010080000010020852ba7,0x0,0x40200000400800002002000002008000000101040000487b00001200000001041004000020040000200200001000200001000000400207e0400200040001008000001002084aba7,0xf379803cde60079f980000000f3079803cc1e67980799e601e63cc03cc00003ccf300f4e6001e703d95,0xf379803cde60079f98000f33cc044580007b667980799e601e63cc03cc00f33ccf300f4e6001e722395,0xf379803cde60079f9800000000f37981e601e67980799e601e63cc03cc00003ccf300f4e6001e703d95,0x0,0x0,0x40200000400800002002000002008000000401000004087800020200000020040004000020040000200200001000200001000008000207ed000200040001008000001002084aba7,0xf379803cde60079f9803cc0000f379803cc1e67980799e601e63cc03cc3cc03ccf300f4e6001e703d95,0xf379803cde60079f9800f31e603d39800f31e67980799e601e63cc03cc0f303ccf300f4e6001e703d95,0x3d39800f4e6003f1f800f3001e9cc007a73001e9cc1e610237a76cc1f5303d3b6644766007a011c1936,0xf379803cde60079f9803cc0000f379801e61e67980799e601e63cc03cc3cc03ccf300f4e6001e703d95,0x3d39803cde6007bdf800f3001f530007b66001e9cc1e63db4e6fa983db303d3b6644d18007cda32e136,0x0,0xf379803cde60079f980000000f307983cc01e67980799e601e63cc03cc00003ccf300f4e6001e703d95,0x0,0xf379803cde60079f9800000000007983cc01e67980799e601e63cc03cc00003ccf300f4e6001e703d95,0x0,0x0,0x0,0x7980001e60f362b800079800044580007c593cc03cde601e63cc03cc00001e60000f5d9001e703885],
[0x7980001e60f3079800000000007982d902d93cc03cde601e63cc03cc00001e60000f5d9001e703885,0x0,0x0,0x0,0x7980001e60f30798000000000079800002d93cc03cde601e63cc03cc00001e60000f5d9001e703885,0x3d39800f4e60f6d39800f31e603d39800f31e67980799e601e63cc03cc0f303cc3cc0f4e6001e703d95,0x8400410008004200108042201200c40041108a4,0xf379803cde6102379803cc0000f379801e61e67980799e601e63cc03cc3cc03ccf300f4e6001e703d95,0x8400410008004400108042402200c40043118a4,0x0,0x0,0x7980001e61a947980f300007987980f302d93cc03cde601e63cc03cc00001e60000f5d9001e703885,0x0,0x0,0x80c0a8220481,0x824088220481,0x80c0a8220481,0x844188220501,0x8140c8220481,0x824088220481,0x8140c8220481,0x0,0x824088220481,0x200000000800080000400200001000800040000080100000000400020001000002000800004004000020010000080020000100100000040800000202000000804000001001085ee27,0x824088220481,0x3b9aca00003b9acdb9aca3b9ad8e6b28ee6b639aca0ee6c166b2f7359403b9ca6d6500000773597bd666a6d65ee6b2f7359407735cf9aca0ee6c166b283b9b059aca0ee6d04d6507735b1cd6507736826b2801dd11eaca0077447ab2801ddc4bb2800ee88f565000ee6ee94cc5da9,0x844188220501,0x804088220481,0x844188220501,0x844188220501,0x0,0x7d4c001e6f300b640000f30000b6401e67980799e601e63cc03cc00003cc0000f4e6001e703d95],
[0x2080002002040081002000021000814e3,0x1e9cc00799e6012fc0000f3000222c01e67980799e601e63cc03cc00003cc0000f4e6001e703d95,0x844188220501,0x840002002000008000400020020000084000204210000010840000002100000600200001000800004001000008002000010048040010120000040008400080c0000010018c73227,0x80002002040081002000021000814e3,0xf300003ccf3007d4c0000f3000f6cc01e67980799e601e63cc03cc00003cc0000f4e6001e703d95,0x0,0x1e60000798f301e9cc0000f3001e9cc01e67980799e601e63cc03cc00003cc0000f4e6001e703d95,0x200010e0087000000200000000000040000000100008700400020001000004000800004004000020020000100020000100000000041ee0000200000001008000001002085aba7,0x7980001e60f303cfcc0000f30079bcc01e67980799e601e63cc03cc00003cc0000f4e6001e703d95,0x0,0x844188220501,0x4088220481,0x844188220501,0x4088220481,0x0,0x80c0a8220481,0x824088220481,0x80c0a8220481,0x844188220501,0x8140c8220481,0x824088220481,0x8140c8220481,0x40201010080202002040081002040021000854e3,0x824088220481,0x0,0x824088220481,0x0,0x844188220501,0x804088220481,0x844188220501,0x844188220501],
[0x0,0x80c0a8220481,0x0,0x80c0a8220481,0x44188220501,0x8140c8220481,0x80002002040081002000021000814e3,0x8140c8220481,0x0,0x0,0x20001000087000000200000000000040000000100008700400020001000004000800004004000020020000100020000100000000041e00000200000001008000001002085aba7,0x0,0x0,0x44188220501,0x4088220481,0x44188220501,0x4088220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_948 : TreeBound (n := 4) 107 (programCode 0x422b071440) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0xc00030080002002000082002000020000814e3,0x0,0x180428084222,0x180428084222,0x180428084222,0x180428084222,0x0,0x180828484222,0x180428084222,0x180828484222,0x180428084222,0x181028284a62,0x180428084222,0x181028284a62,0x109cf983cc1e6003d3981e62139798798079807aec8079879807a73003d20d203cc3cc03d39801e64dc35,0x182028084222,0x200010c008000400020000080080002000000004000860020002000020000400400001001c000020020000100100000100000000101cc0000200000001008000001002087aba7,0x182028084222,0x1400050080002002000082002000020000814e3,0x400010080002002000082002000020000814e3,0x0,0x20c080200481,0x0,0x20c080200481,0x204080200481,0x214080200481,0x2000080080002002000080002000020000814e3,0x214080200481,0x0,0x0,0xf3001e63cc1e60f301e9cc0002d9000222c000222c0010231e603cc000f3097e0001ed98007983db63b6],
[0x0,0x0,0x244082208481,0x3cc1e64bf07992fdf533cc0004bf00012fc000222c7981e61e67d4c000f30811800463ef307987d51426,0x244082208481,0x204080200481,0x10d9b983cc1e600007983cc2139f300003cc007a730079800007a73003cfcc003cc00003cc0001e64dc35,0x4400110080002002000082002000020000814e3,0x0,0x0,0x280428084642,0xf362b83cc1e600016c80011439000f3000079fa730079800007a73003cfcc003cc00003cc0001e64dc35,0x280428084642,0x0,0x0,0x0,0x0,0x10200000080800000102000000208000000000002000000008020000020084000090000000080002000100008010200000010001000800008004000010008000020042002163228,0x281028284e82,0x280428084642,0x281028284e82,0x0,0xf307983cc1e600007983cc21390000003cc007a730079800007a73003cfcc003cc00003cc0001e64dc35,0x200016000800040002000080008000080000000400083002000000002000040040000040160000200000001001000001000000000416000002000000010000000010020852ba7,0xf307983cc1e600007983cc21390000003cc007a730079800007a73003cfcc003cc00003cc0001e64dc35,0x0,0x180428084222,0x180428084222,0x180428084222,0x180428084222,0x0,0x8400210080000002000082002000020000814e3],
[0x180428084222,0x0,0x180428084222,0x581028284a62,0x180428084222,0x581028284a62,0xf379803cde6003d3981e62139798798079807aec8079879807aec803d1eec03cc3cc03d39801e64dc35,0x0,0x0,0x0,0x3d39803cde6003d3983cc0002d9000222c000222c0010231e603cc000f3097e0001ed98007983db63b6,0x0,0x180428084222,0x180428084222,0x180428084222,0x180428084222,0x0,0x0,0x180428084222,0x0,0x180428084222,0x581028284a62,0x180428084222,0x581028284a62,0x0,0x182028084222,0x0,0x182028084222,0x0,0x481428284a62,0x480428084a62,0x480428084a62],
[0x480428084a62,0x0,0x480828484a62,0x481428284a62,0x480828484a62,0x481428284a62,0x481028284a62,0x480428084a62,0x481028284a62,0x7981e61e6079879807980f379800007980f3f3003cc0000f3f3003cc00001e600007980001e68a055,0x0,0x401010040001002000082002000020000814e3,0x0,0x0,0x80c0a8220481,0x20080802080082002020082002020020800814e3,0x80c0a8220481,0x844188220501,0x8140c8220481,0x20000800080002002020080002020020800814e3,0x8140c8220481,0x0,0x2004080108004200202008200202002080081ce3,0x20400800080002002020082002020020800814e3,0x20080802080082002020082002020020800814e3,0x0,0x844188220501,0x804088220481,0x844188220501,0x844188220501,0x0,0x1e60001e60f301e6b643cc0002d9000222c000222c0010231e603cc000f3097e000222c000798445b3b6],
[0x2080002002000082002000020000814e3,0x0,0x4080200481,0x0,0x80002002000080002000020000814e3,0x0,0x0,0x0,0x109d04e4001e600000003cc2139f300003cc00f3f3007980000f300003cfcc003cc00007980001e68a8c5,0x80002080002002000082002000020000814e3,0x0,0x844188220501,0x4080200481,0x844188220501,0x4080200481,0x0,0x80c0a8220481,0x40001002080002002040082002040021000814e3,0x80c0a8220481,0x844188220501,0x8140c8220481,0x40001000080002002040080002040021000814e3,0x8140c8220481,0x7983cc1e62d903cc7983cc0f30f303cc3cc01e67980799e601e76c803cde6003d39800f4e6001ee9bd95,0x4004100108004200204008200204002100081ce3,0x0,0x40081002080082002040082002040021000814e3,0x0,0x844188220501,0x804088220481,0x844188220501,0x844188220501],
[0x0,0xc080200481,0x0,0xc080200481,0x4080200481,0x14080200481,0x80002002000080002000020000814e3,0x14080200481,0x0,0x0,0xf3084e4001e600000003cc2139f300003cc00f3f3007980000f300003cfcc003cc00007980001e68a8c5,0x0,0x0,0x44080200481,0x4080200481,0x44080200481,0x4080200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_4 : TreeBound (n := 4) 107 (programCode 0x422b0714) := by
  conv in programCode _ => reduce
  exact branchFour (k := (1,1)) (by decide +kernel) part100_5 part100_6 part100_7 part100_8 part100_9 part100_10 part100_11 part100_12 part100_93 part100_174 part100_255 part100_336 part100_417 part100_610 part100_771 part100_948

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_1125 : TreeBound (n := 4) 107 (programCode 0x422b0715) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x1084090208481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_1127 : TreeBound (n := 4) 107 (programCode 0x422b071631) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1084081218481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_1128 : TreeBound (n := 4) 107 (programCode 0x422b071632) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1084084210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_1129 : TreeBound (n := 4) 107 (programCode 0x422b071633) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1084081218481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_1130 : TreeBound (n := 4) 107 (programCode 0x422b071634) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x80402010080002002000080002000020000814e3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_1131 : TreeBound (n := 4) 107 (programCode 0x422b071635) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1084082210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_1132 : TreeBound (n := 4) 107 (programCode 0x422b071636) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1084084210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_1133 : TreeBound (n := 4) 107 (programCode 0x422b071637) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1084082210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_1134 : TreeBound (n := 4) 107 (programCode 0x422b071638) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1080487218481,0x1081084210481,0x1080487218481,0x1080080210481,0x1080882210481,0x1081084210481,0x1080882210481,0x1080080210481,0x1081084210481,0x1081084210481,0x1081084210481,0x1080080210481,0x0,0xf307af04c00102300003d94a088b0001e600001e7edaec87980000f303cc7b69cc1e60f301e61e611156,0x0,0x0,0x0,0xf307a76cc1ebc13000408c0004c1d900f31e601e7eda7307981e60f303cc3cc3cc0faa7301e61e610f76,0xf30007d4c001f53000408c0004bff300f31e601e7eda7307981e60f303cc3cc3cc0faa7301e61e610f76,0xf307a76cc003db30007d5398088b0001e600001e7eda7307980000f303cc7b69cc1e60f301e61e611156,0xf3000f6cc003db30007d5398088b0001e600001e7eda7307980000f303cc7b69cc1e60f301e61e611156,0xf307a76cc0000f30007d5398088b00007980001e7eda7307980000f303cc7b69cc0798f301e61e6110f6,0xf3003cfcc007a73001e9cc0004bf0f307983cc1e7ed9bcc7980f30f303cc3cc3cc0812ec81e61e6188c6,0xf307a76cc001f53000408c0004c1d900f31e601e7eda7307981e60f303cc3cc3cc0faa7301e61e610f76,0xf30079bcc01e6f3003cfcc0004bf1e60798b641e7ed9bcc7980f30f303cc3cc3cc0812ec81e61e6188c6,0xf307983cc1e60f300003cc0004bf0000f300001e7ed98007981e60f303cc3cc3cc0faa7301e61e610f76,0x0,0xf307983cc1e60f300003cc0004bf0000f300001e7ed98007981e60f303cc3cc3cc0faa7301e61e610f76,0x0,0x0,0x282022108442],
[0x182022188442,0x282022108442,0x182022188442,0x282022108442,0x282022108442,0x282022108442,0x282022108442,0x8400210010002002010080402000020000814e3,0x79f9801e7e6003d3980f3000408c000fa98001e7e63cc079897e0f303cc3cc3cc0f5e8301e61e64db76,0x282022108442,0x0,0x0,0x0,0x0,0x0,0x0,0xf307a76cc00102300003d764088b0001e600001e7eda7307980000f303cc7b69cc1e60f301e61e611156,0xf300012fc0004bf0000b640004bff300f31e601e7eda7307981e60f303cc3cc3cc0faa7301e61e610f76,0x0,0x400030001000000004000300010000c00020003100080000000100031000200002006000010010000040060000080040000100620000101800000400000000818800001001087fe67,0x0,0x0,0x0,0x0,0x0,0xf3003cfcc007a73001e9cc0004bf00007980001e7ed98007980f30f303cc3cc3cc08127301e61e6188c6,0x0,0x0,0xf307983cc1e60f300003cc0004bf0000f300001e7ed98007981e60f303cc3cc3cc0faa7301e61e610f76,0x0,0xf307983cc1e60f300003cc0004bf0000f300001e7ed98007981e60f303cc3cc3cc0faa7301e61e610f76,0x0],
[0x0,0x282022108442,0x182022188442,0x282022108442,0x182022188442,0x282022108442,0x282022108442,0x282022108442,0x282022108442,0x0,0x3d39803cde6003d3980f3000222c001f530001e6f303cc3cde600f303cc1ed9801e607981e61e703856,0x282022108442,0x0,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_1215 : TreeBound (n := 4) 107 (programCode 0x422b071639) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1084084210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_1216 : TreeBound (n := 4) 107 (programCode 0x422b07163a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8040201008000a00011042020040448008100904]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_1217 : TreeBound (n := 4) 107 (programCode 0x422b07163b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1084084210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_1218 : TreeBound (n := 4) 107 (programCode 0x422b07163c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1080487218481,0x1081084210481,0x1080487218481,0x1080080210481,0x1080882210481,0x1081084210481,0x1080882210481,0x1080080210481,0x1081084210481,0x1081084210481,0x1081084210481,0x1080080210481,0x0,0x400021519000080004000000210000000242a30001000100004400000008000000008200215180800004002000000002000008002021518008000000010200000010010000817ffa8,0x0,0x0,0x0,0x0,0x0,0x400021111000001004000200010000010042220001100000000c00000008000400008200211100800000802000002002000008002021110001001000010200000010010000817f3a8,0x400000101000000404000001010000001042200001108800004400000008000000008200211000800004002000000002000008002021100008000000010200000010010000817ffa8,0xf30822d2c00f3f3003d0114b088b00007983cc1f5382299cc00f379803cc7b88a588118001e6f307b5f6,0xf3003cfcc007a73001e9cc0004bf0f307983cc1f5379bcfcc00f379803cc3ea60008155399e6f307b446,0x0,0xf30079bcc01e6f3003cfcc0004bf1e60798b641f5379bcfcc00f379803cc3ea60008155b31e6f307b446,0x400010001000040004000040010000080020003100080004000080031000100002006000010010000040060000080080000100620000101800000402000000818800001021087fe67,0x0,0x400010001000040004000080010000100020003100080004000080031000100002006000010010000040060000080080000100620000101800000402000000818800001021087fe67,0x0,0x0,0x152000100148000400420000001480000800000041000000090000000810000000820020028020000080200000a80200000800080400000100108001028420001001000085753a8],
[0xc00030020004800110004400402100082412e4,0x79801e7e6079879807980025f8001ed98001ed9803cde6f30079803cc1e60001e9cc001e6f307ea16,0x1400050020004800110008400402100082412e4,0xc00090020004800110010400402100082010e4,0x2400090020004800110010400402100082010e4,0x0,0x4400110020004800110020400402100082010e4,0x0,0x0,0x2400090020004800110010400402100082010e4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xf3003cfcc007a73001e9cc0004bf00007980001f5379803cc00f379803cc3ea60008118001e6f307b446,0x0,0x0,0x400010001000040004000040010000080020003100080004000100031000200002006000010010000040060000080080000100620000101800000402000000818800001021087fe67,0x0,0x400010001000040004000080010000100020003100080004000100031000200002006000010010000040060000080080000100620000101800000402000000818800001021087fe67,0x0],
[0x0,0x2402030040005000110010400402200082010e4,0xc00030040005000110004400402200082412e4,0x0,0x1400050040005000110008400402200082412e4,0xc00490040005000110004400402200082412e4,0x2400090040005000110010400402200082010e4,0x0,0x4400110040005000110020400402200082010e4,0x0,0x0,0x400090040005000110000400402200082010e4,0x0,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_1299 : TreeBound (n := 4) 107 (programCode 0x422b07163d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x100c0c821c481,0x1024088210481,0x100c0c821c481,0x80402004080102002020080802020020800834e3,0x1014088218481,0x1024088210481,0x1014088218481,0x0,0x804020001008a0022020080802000820500814e3,0x80402000000000402020080802000020000814e3,0x804020002010a0042020080802001020500814e3,0x80402000000000802020080802000020000814e3,0x80402000402080082020080802002020400814e3,0x80402000000000002020080802000020000814e3,0x80402000804080102020080802004020400814e3,0x0,0x80402001008080202020080802008020400814e3,0x80402000000000002020080802000020000814e3,0x80402002010000402020080802010020000814e3,0x80402000000000002020080802000020000814e3,0x80402004020100802020080802020020800834e3,0x0,0x0,0x0,0x1024088210481,0x80402000080002002020080802000020000814e3,0x1024088210481,0x0,0x40003935b000000004000000010000209080023935a00080100000100000000100902000010008000040010000020010000100726b40100012000401048400200000001000487fca7,0x1021088210481,0x1dcd6500ee729b5940773770d6501dcddc35940773770d6500773d084f1e817d77a22cd65ee6b2f73597b9aca773597b9bb86b2803b9ae7cd82d4d8597ba23f36183bbeeeb438140003b9aca7735b1cd73ea6ca78f445a9b28f565ee6b2f73594ee6b45cd650ee6b28ee6eec16efca],
[0x80402000000000802020080802000020000814e3,0x80102000402080082020080802002020400814e3,0x1021088210481,0x80102000804080102020080802004020400814e3,0x0,0x1021088210481,0x1021088210481,0x1021088210481,0x1000088210481,0xf300003cc1e60f303cc07980f379800007980f31e603cde600f31e603cc00001ed98007980001e68a055,0x0,0x0,0x0,0x1044188230501,0x8020200408000a0001c042080040460008402104,0x1044188230501,0x8020200808000a0001c042100040460008804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_1348 : TreeBound (n := 4) 107 (programCode 0x422b07163e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x8043200008000a00014042080040460008402104,0x8000a00018000a00014042080040460008402104,0x0,0x10c082210481,0x40c086210481,0x10c082210481,0x26082308c7c001e612fc00088b000222c00025f800f4e61e601e6003cc7c59001e600f31e9cc1e9716,0x20c086210481,0x40c086210481,0x20c086210481,0x0,0x40c086210481,0x1078020108000a0001404208004046c008402904,0x40c086210481,0x0,0x80c083218481,0x60c086210481,0x80c083218481,0x798b641e603cc3cc1e63cc00088b000222c00025f87a74e61e601e6003cc7c59001e7e6001e9cc5b3e56,0x0,0x16ec121e61e607981e612fc00088b000222c00025f87a74e61e601e6003cc7c5d825e600f31e9cc1e9cb6,0x400080002002000080002000020000814e3,0x452508097e0001e67d4c2139f300003cc00f40bae79803ccf307983d027203cc79807980001e68a8c5,0x80002002000080002000020000814e3,0x2000082080002002010080002000020000814e3,0x80002002000080002000020000814e3,0x4000102080002002010080002000020000814e3,0x0,0x8000202080002002010080002000020000814e3,0x3cc00f6cc003cfcc012fc0002d9000222c0002046003ea61e601e6003cc2046001e61e601e9cc225fb6,0x10000400080002002000080002000020000814e3],
[0x0,0x20000800080002002000080002000020000814e3,0x80002002000080002000020000814e3,0x40001000080002002000080002000020000814e3,0x80002002000080002000020000814e3,0x8043200048000a00014042080040460008402304,0x8002200048000a00014042080040460008402304,0x8060200408000a00014042080040460008402104,0x0,0x0,0x80022000800804020120010800402400084026e4,0x0,0x80022000801004040120010800402400084026e4,0xf3000f6cc003db300079879804e03900f31e60222c97e0f303ea7e6003cc3ea6000fc7e001e9cc1f6f76,0x8002200080400808014032080040460008406504,0x0,0x8002200080400810014022080040460008406504,0x0,0x8002200080800420012004080040240008502ce4,0xf3000f6cc003db30007e3f0003eb5300f31e60222c97e0f303ea7e6003cc3ea6000fc7e001e9cc1f6f76,0x80022000810004400120080800402400086034e4,0xf3000f6cc003db30007f3998088b0001e6000025f8b734e600001e6003cc7c59001ed98001e9cc1f7156,0x0,0x0,0x0,0x8060200408000a00014042080040460008402104,0x8008200108000a00014042080040460008402904,0x8042200048000a00014042080040460008402304,0x0,0x400001001000004004000010010000010066a7000110000000080040000802000000a000335381000000810000002010000008002033538001008000010200000010080004817f3a8,0x80082002000804020120010800402400084030e4,0x0],
[0x80082002001004040120010800402400084030e4,0x0,0x0,0x0,0x0,0x0,0x80082002008004200120040800402400085038e4,0x0,0x80082002010004400120080800402400086030e4,0xf30079bcc01e6f3003cfcc0004bf1e60798b64222c79bd39800f4e6003cc3ea6000820b001e9cc261446,0x0,0x0,0x0,0x8040200008000a00014042080040460008402104,0x8020200408000a00014042080040460008402104,0x8040200008000a00014042080040460008402104,0x8020200808000a00014042080040460008406104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_1429 : TreeBound (n := 4) 107 (programCode 0x422b07163f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x100c0c821c481,0x1024088210481,0x100c0c821c481,0x80002008080002002040081002000020000814e3,0x1014088218481,0x1024088210481,0x1014088218481,0x0,0x8040300800a2002040081002000820500814e3,0x410080002002040081002000020000814e3,0x10080500800a2002040081002001020500814e3,0x1010080002002040081002000020000814e3,0x2010090080082002040081002002020400814e3,0x10080002002040081002000020000814e3,0x4020110080082002040081002004020400814e3,0x2010080002002040081002000020000814e3,0x8040210080082002040081002008020400814e3,0x0,0x10080410080002002040081002010020000814e3,0x0,0x0,0x0,0x40201010080202002040081002040021000854e3,0x0,0x1024088210481,0x0,0x1030488218481,0x1021088210481,0x1030488218481,0x1022088210481,0x1020888210481],
[0x1021088210481,0x1020888210481,0x0,0x1021088210481,0x1021088210481,0x1021088210481,0x1020088210481,0x1022088210481,0x800820010400088001c042080040460008402904,0x1022088210481,0xf3001e9cc01e6f3001e6f3000222c001f53000222c00408c1e603cc003cc2046001ed98001ed984c0556,0x1024088210481,0x0,0x80002000100800022040081002000020000814e3,0x1021088210481,0x80002000201000042040081002000020000814e3,0x0,0x80202010402200082040081002040021000854e3,0x1021088210481,0x80202010804200102040081002040021000854e3,0x0,0x1021088210481,0x1021088210481,0x1021088210481,0x1000088210481,0x0,0x0,0x0,0x0,0x1044188230501,0x0,0x134088218481],
[0x424088210481,0x134088218481,0x1000080002002040081002000020000814e3,0x224088210481,0x424088210481,0x224088210481,0x0,0x424088210481,0x1020020408000a00019042020040448008100904,0x424088210481,0x0,0x804088210481,0x4088210481,0x804088210481,0x4088210481,0x1044188230501,0x0,0x800020080002002040081002000020000814e3,0x0,0x1000040080002002040081002000020000814e3,0x1000080002002040081002000020000814e3,0x2541c8238501,0x80002002040081002000020000814e3,0x2541c8238501,0x0,0x0,0x3cde603cc79803cde63cc0002d9000222c0001f5300408c1e600f3003cc2046001ed98001e7e60f4556,0x0,0x0,0x844188230501,0x4088210481,0x844188230501],
[0x4088210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_1526 : TreeBound (n := 4) 107 (programCode 0x422b071640) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0xf307983cc001023079c08c0002d9000222c000222c003db31e603cc003cc2046001ed98001ed983d4ed6,0x0,0x40000001100000000c0000000900000000e826000110000000080040000800040000a000341008000000820000002020000008002030000001010000010200000010100008017f3a8,0x80006000100804020140011000402400088040e4,0x0,0x80006000101004040140011000402400088040e4,0x0,0x0,0x0,0x0,0x0,0x80006000108004200140041000402400089048e4,0x0,0x8000600011000440014008100040240008a050e4,0x0,0x0,0x0,0x0,0xf307983cc0798f307983cc0002d9000222c000222c003db31e603cc003cc2046001ed98001ed983cd556,0x0,0x800020080002002000080002000020000814e3,0x0,0x1000040080002002000080002000020000814e3,0x80002002000080002000020000814e3,0x2000080080002002000080002000020000814e3,0x80002002000080002000020000814e3,0x4000100080002002000080002000020000814e3,0x0,0x0,0x3cc00f6cc003cfcc012fc0002d9000222c000222c003db31e603cc003cc2046001e679801ed984c23b6,0x0],
[0x0,0x20100804080102002020080802020020800834e3,0x80002002000080002000020000814e3,0x40001008080002002040081002000020000814e3,0x80002002000080002000020000814e3,0xf307983cc0000f3000408c0002d9000222c000222c003db31e603cc003cc2046001ed98001ed983cd556,0xf3000408c003db3000408c0002d9000222c000222c003db31e603cc003cc2046001ed98001ed983f34d6,0x0,0x114084210481,0x0,0x114084210481,0x20000880002002000080002000020000814e3,0x214080210481,0x20000880002002000080002000020000814e3,0x214080210481,0x0,0x0,0x3d39803cc1e603cde63cc0002d9000222c000222c003db31e603cc003cc2046001e679801ed984c0556,0x0,0x0,0x814088218481,0x0,0x814088218481,0x14080210481,0x0,0x4000200110000800440000001100000001000221000000800000000a1000000102004200010010000040042000080000000100420000101080000400000000810800001001087fe67,0x80022000800804020140011000402400088046e4,0x0,0x80022000801004040140011000402400088046e4,0xf30007d4c001f530007983cc01e6f301e61e60222c003db307983cc003cc2046001ed98001ed983dc856,0x8002200080400808014022100040460008804504,0x0],
[0x8002200080400810014022100040460008804504,0x400000041000000204000001010000001008000000940400002002000008200000008800040004000a020200020000200000080010200000040a0000010200000010100008205aba8,0x8002200080800420014004100040240008904ce4,0x0,0x8002200081000440014008100040240008a054e4,0x0,0x0,0x0,0x0,0x0,0xf30d5d38c0000f301e66ae7e07987981e6000025f8d594e600003cc003cc7c59001ed98001ed983cde56,0x80202008000804020140011000402400088040e4,0x0,0x0,0xf307983cc00102301e6001e601e67981e61e60222c003db307983cc003cc2046001ed98001ed983d4ed6,0xf307983cc00102301e6001e601e7e601e61e60222c003db307983cc003cc2046001ed98001ed983d4ed6,0xf30b643cc0000f301e65b200088b0001f5300025f87a74e61e603cc003cc7c59001ed98001ed983cde56,0xf307983cc0798f301e6003cc01e6f301e63cc0222c003db307983cc003cc2046001ed98001ed983cd556,0xf30b643cc0000f301e65b20007980001f5300025f87a73f31e603cc003cc7c59001ed98001ed983cddc6,0x80006009008004200140041000402400089048e4,0xf30b7738c00102301e65b99807d4c001e61e6025f8b734e607983cc003cc7c59001ed98001ed983d57d6,0x8000600a01000440014008100040240008a050e4,0xf30b643cc0000f301e65b200088b000079800025f87a74e600003cc003cc7c590008118001ed983cddf6,0xf30b643cc0798f301e61e60008118001ed980025f87a74e61e603cc003cc7c59001ed98001ed983cde56,0x0,0xf307983cc0000f301e60f3000222c001f53000222c003db31e603cc003cc2046001ed98001ed983cd556,0xf3001e9cc01e6f3001e9cc0002d9000222c000222c003db31e603cc003cc2046001ed98001ed984c0556,0x0,0xf30d596cc0000f3000436c9807987981e6000025f8d594e600003cc003cc7c59001ed98001ed983cde56,0x80012000400804020140011000402400088042e4,0x0,0x80012000401004040140011000402400088042e4],
[0xf30b643cc07b75300042720005763300f31e6025f8b641e607b69cc003cc3ea6000fe64001ed983dcf76,0x8022200040400808014022100040460008804504,0x0,0x8022200040400810014022100040460008804504,0x0,0x80042000408004200140041000402400089048e4,0xf30b643cc07b7530004272000409b300f31e6025f8b641e607b69cc003cc3ea6000fe64001ed983dcf76,0x8008200041000440014008100040240008a050e4,0xf30b643cc07b753000408c0005763300f31e6025f8b641e607b69cc003cc3ea6000fe64001ed983dcf76,0x0,0x0,0x0,0x0,0x0,0x80082002000804020140011000402400088050e4,0x0,0x80082002001004040140011000402400088050e4,0x40000040100000100400001001000001000080000020815000082000000800140000880000400200000082000054202000000800042000000109500001020000001014000a00513a8,0x0,0x0,0x0,0x1dcd6500ee729b59403b9ca6d6500ee729b5940773770d65007735940ee6b283b9ae7cd65f75acfd96c1eea6c2ca003c11ff940003f5476a001ddc4bb28003bd664dbdf4fd0a588b9aca1dcd65001dcd65ee6b2f735cfa9b0b28003be2473ecb6f7599328000eea6c2cc18cd28d30a,0x80082002008004200140041000402400089058e4,0x0,0x8008200201000440014008100040240008a050e4,0x0,0x0,0x0,0x0,0x0,0x144087218481,0x4826d908118000f303cc00088b00012fc00025f87a74e61e7e9cc003cc7c59798fe64f31ed983cde26],
[0x144087218481,0x100004080002002000080002000020000814e3,0x244082210481,0x100004080002002000080002000020000814e3,0x244082210481,0x0,0x16c87985b200003cc0003cc00088b00012fc00025f87a74e61e7e9cc003cc7c59000fe64001ed983cde26,0xf3c1d1ae6799e9cc003cc00088b00012fc00025f87a74e61e7e9cc003cc7c77600fea0c01ed983cde26,0xf4edaf04fcc0f3079803cc00088b00012fc00025f87a74e61e7e9cc003cc7c5ccc0fe6b981ed983d57a6,0x0,0x844188230501,0x844188230501,0x844188230501,0x44080210481,0x8020200408000a00014042100040460008804104,0x0,0x144087218481,0x1116000f30f30111beec0002d9000222c000222c003db31e603cc003cc2046001e601e61ed983d4ed6,0x144087218481,0x200008080002002000080002000020000814e3,0x244082210481,0x200008080002002000080002000020000814e3,0x244082210481,0xf303cc00003ccf301e63cc21b37307983cc007a730079bcc007980003d036503cc0000408c001e64dc35,0x0,0x0,0xf4f1736cc07980079803cc00088b000222c00025f87a74e61e603cc003cc7c5ccc1ed98001ed983cde56,0x0,0x844188230501,0x844188230501,0x844188230501,0x44080210481],
[0x8020200808000a00014042100040460008804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_1126 : TreeBound (n := 4) 107 (programCode 0x422b0716) := by
  conv in programCode _ => reduce
  exact branchFour (k := (1,1)) (by decide +kernel) part100_1127 part100_1128 part100_1129 part100_1130 part100_1131 part100_1132 part100_1133 part100_1134 part100_1215 part100_1216 part100_1217 part100_1218 part100_1299 part100_1348 part100_1429 part100_1526

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_1687 : TreeBound (n := 4) 107 (programCode 0x422b0717) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x1084090208481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_1689 : TreeBound (n := 4) 107 (programCode 0x422b071831) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10804c1204481,0x1081081210481,0x10804c1204481,0x10804c1204481,0x1080881208481,0x1081881218481,0x1080881208481,0x1080081200481,0x1081081210481,0x1081081210481,0x1081081210481,0x1080081200481,0x0,0x100a0a1220481,0x1022081220481,0x100a0a1220481,0x80402000120004802000880022020020800814e3,0x10120c1220481,0x10320c1220481,0x10120c1220481,0x1042181220501,0x1022081220481,0x1022081220481,0x1022081220481,0xf300003cc1e60f303cc07980f379800007980f3000f6cc00f3f3000f6cde6001ed98007b66001e68a055,0x1042181220501,0x0,0x1042181220501,0x0,0x0,0x282022108442],
[0x182023188642,0x282022108442,0x182023188642,0x282022108442,0x282022108442,0x282022108442,0x282022108442,0x8400210010002002000880022010020400814e3,0x3d39803cde6003d39807980025f8001ed98002dccc0798f307a730f37983cfcc00fb92983cc7983e156,0x282022108442,0x0,0x0,0x0,0x0,0x0,0x0,0x100a0a1220481,0x1022081220481,0x100a0a1220481,0x0,0x10120c1220481,0x10320c1220481,0x10120c1220481,0x1042181220501,0x1022081220481,0x1022081220481,0x1022081220481,0x0,0x1042181220501,0x0,0x1042181220501,0x0],
[0x0,0x282022108442,0x182023188642,0x282022108442,0x182023188642,0x282022108442,0x282022108442,0x282022108442,0x282022108442,0x0,0x3d39803cde6003d3980f3000222c001f530002e830079bcc1e6f30f37983d39800fc85983cde60f4556,0x282022108442,0x0,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_1770 : TreeBound (n := 4) 107 (programCode 0x422b071832) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10804c621c481,0x1081084210481,0x10804c621c481,0x1081084210481,0x1080884208481,0x1081084210481,0x1080884208481,0x1080084200481,0x1081084210481,0x1081084210481,0x1081084210481,0x1080084200481,0x0,0x100a0a5220481,0x1022084220481,0x100a0a5220481,0x80402000020000802000080402020020800814e3,0x10120c6238481,0x1022084220481,0x10120c6238481,0x40002000100008000400002001000008000400200001000080004000200010000600400001000100004000400008000c0001004000001010000004004000008010000010050873227,0x1022084220481,0x1022084220481,0x1022084220481,0xf300003cc1e60f303cc07980f379800007980f307983cc0000f307983cde6001ed98007b66001e68a055,0x40000200100000800400002001000008000400200001000080004000200010000600400001000100004000400008000c0001004000001010000004004000008010000010050873227,0x0,0x40001000100004000400008001000010000400200001000100004000400010000600400001000200004000800008000c0001004000001010000004004000008010000010390873227,0x0,0x0,0x382021188642],
[0x182021188642,0x382021188642,0x182021188642,0x382021188642,0x282021108642,0x382021188642,0x282021108642,0x8400210010002002000080402010020400814e3,0x0,0x282021108642,0x0,0x0,0x0,0x0,0x0,0x0,0x100a0a5220481,0x1022084220481,0x100a0a5220481,0x0,0x10120c6238481,0x1022084220481,0x10120c6238481,0xf300003cc0f30f303cc1e600007980000f301e600007980001e60f303cc00003d39800f4e6001e703d95,0x1022084220481,0x1022084220481,0x1022084220481,0x0,0x40000200100000800400002001000008002000200008000080010000200020000600400001000100004000400008000c00010040000010100000040200000080c0000010050873227,0x0,0x40001000100004000400008001000010002000200008000400010001000020000600400001000800004002000008000c00010040000010100000040200000080c0000010210873227,0x0],
[0x0,0x382021188642,0x182021188642,0x382021188642,0x182021188642,0x382021188642,0x282021108642,0x382021188642,0x282021108642,0x0,0x0,0x282021108642,0x0,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_1851 : TreeBound (n := 4) 107 (programCode 0x422b071833) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0xf307983cc1e60f307983cc0000f307983cc0352800f4e600f4e6001e9cc00000f30000f6cc001e703375]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_1852 : TreeBound (n := 4) 107 (programCode 0x422b071834) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10804c1204481,0x1081084210481,0x10804c1204481,0x1080080200481,0x1080880208481,0x1081084210481,0x1080880208481,0x1080080200481,0x1081084210481,0x1081084210481,0x1081084210481,0x1080080200481,0x0,0x0,0x0,0x16c800111600025f807980001e6798079835280001e6007b66001e9cc00000f30000f379801e703375,0x7980001e6000079807980001e6798079835280001e60001e600003cc00000f30000f379801e703375,0x0,0x2000000008000000020001000080001000000001000040010002000010000400000001000000001000000010000000010000000010040000010000000100400000100208793a7,0x8118007b66000fa9807981e61e6811879835280f31e603cde600f33cc03cc0f30f30f37d4c1e703375,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x382021188642],
[0x182021188642,0x382021188642,0x182021188642,0x382021188642,0x282021108642,0x382021188642,0x282021108642,0x8400210010002002010080402010020400814e3,0x3d39803cde6003d39807980025f8001ed98001e61e6798079f9801e67983cfcc00f307983cc03d0f2b6,0x282021108642,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x7983cc1e600f37981e600007987980f301e600007980001e600003cc00003cc0000f4e6001e703d95,0x25f800111600025f80f300007987980f302d900003cc016e66005b5cc00001e60000f5d9001e703885,0x7980001e6000079807980007987980f3035280001e60001e600003cc00000f30000f652801e703375,0x4200000080800000042000000108000080000800400000001000200002000020000000040000000200002000800008001001000000400000002000000008040000010010852e27,0x7980001e60f307980f300007987980f302d900003cc0001e600003cc00001e60000f5d9001e703885,0x1ed98007b66000fa981e600007987980f301e600007980799e601e63cc00003cc0000f4e6001e703d95,0x7980001e60b647980f300007987980f302d900003cc0001e600003cc00001e60000f5d9001e703885,0x0,0x0,0x0,0x7980001e61a947980f300007987980f302d900003cc0001e600003cc00001e60000f5d9001e703885,0x0,0x0,0x0,0x0],
[0x0,0x382021188642,0x182021188642,0x382021188642,0x182021188642,0x382021188642,0x282021108642,0x382021188642,0x282021108642,0x0,0x3d39803cde6003d3980f3000222c001f530001e61e679807b66001e67983d39800f307983cc03dc56b6,0x282021108642,0x0,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_1933 : TreeBound (n := 4) 107 (programCode 0x422b071835) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10804c220c481,0x1081082218481,0x10804c220c481,0x1080882208481,0x1080882208481,0x1081082218481,0x1080882208481,0x1080882208481,0x1081082218481,0x1081082218481,0x1081082218481,0x1080082208481,0x0,0x100a0a2228481,0x1022082228481,0x100a0a2228481,0x8041200042009080300204008200201088081ea3,0x10120c2228481,0x1022082228481,0x10120c2228481,0x10521c2228501,0x1022082228481,0x1022082228481,0x1022082228481,0x1dcd66836e2873597b9acbdcd6500000773597b9acbdcd65773597b9ad01c9f4566b28077394daca0ee6b639aca000003b9aca7735943b9b059aca0ee6c166b283b9b059aca03b9b41359403b9b41394e9b0b2f73597b9acbdd11eaca007735943b9ad8e7a0eb2800ee6fd7c6bbe49,0x1042182228501,0x0,0x1042182228501,0x0,0x0,0x282022108442],
[0x182023188642,0x282022108442,0x182023188642,0x282022108442,0x282022108442,0x282022108442,0x282022108442,0x8400210010082002002080082002020400814e3,0x3d39803cde6003d39807980025f8001ed98001e60f379803d3983cc07983cfcc00f3fa983cc01e61556,0x282022108442,0x0,0x0,0x0,0x0,0x0,0x0,0x100a0a2228481,0x1022082228481,0x100a0a2228481,0xf3000408c1e60f30003ea600f3798003db301e60079f9801e7e60079bcc01e63cc0798f4e6001e784f15,0x10120c2228481,0x1022082228481,0x10120c2228481,0x10521c2228501,0x1022082228481,0x1022082228481,0x1022082228481,0x0,0x1042182228501,0x0,0x1042182228501,0x0],
[0x0,0x282022108442,0x182023188642,0x282022108442,0x182023188642,0x282022108442,0x282022108442,0x282022108442,0x282022108442,0x0,0x3d39803cde6003d3980f3000222c001f530001e60f379803ea60f3007983d39800f4ed983cc01e61556,0x282022108442,0x0,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_2014 : TreeBound (n := 4) 107 (programCode 0x422b071836) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10804c621c481,0x1081084210481,0x10804c621c481,0x1081084210481,0x1080884208481,0x1081084210481,0x1080884208481,0x1080084200481,0x1081084210481,0x1081084210481,0x1081084210481,0x1080084200481,0x0,0x100a0e723c481,0x1022084220481,0x100a0e723c481,0x80402000020000802000080002000020800814e3,0x10120c6238481,0x1022084220481,0x10120c6238481,0x0,0x1022084220481,0x1022084220481,0x1022084220481,0xf300003cc1e60f303cc07980f379800007980f300003cc0000f300003cde6001e600007b66001e68a055,0x0,0x0,0x0,0x0,0x0,0x282022108442],
[0x182022188442,0x282022108442,0x182022188442,0x282022108442,0x282022108442,0x282022108442,0x282022108442,0x8400210010002002000080002000020400814e3,0x3d39803cde6003d39807980025f8001ed98001e679879879879807987983cfcc00f303cc3cc3cc6ba56,0x282022108442,0x0,0x0,0x0,0x0,0x0,0x0,0x100a0e723c481,0x1022084220481,0x100a0e723c481,0xf300003cc1e60f300001e600007980000f301e600007980001e600003cc00003cc0000f4e6001e703d95,0x10120c6238481,0x1022084220481,0x10120c6238481,0x80002008040001002000080002000021000814e3,0x1022084220481,0x1022084220481,0x1022084220481,0x0,0x0,0x0,0x0,0x0],
[0x0,0x282022108442,0x182022188442,0x282022108442,0x182022188442,0x282022108442,0x282022108442,0x282022108442,0x282022108442,0x0,0x3d39803cde6003d3980f3000222c001f530001e6798798799e6007987983d39800f303cc3cc3cd21e56,0x282022108442,0x0,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_2095 : TreeBound (n := 4) 107 (programCode 0x422b071837) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0xf307983cc1e60f307983cc01e6f307983cc01e601e67980799e600f33cc07983cc1e60f6cc001e703d95]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_2096 : TreeBound (n := 4) 107 (programCode 0x422b071838) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10804c1204481,0x1081084210481,0x10804c1204481,0x1080080200481,0x1080882208481,0x1081084210481,0x1080882208481,0x1080080200481,0x1081084210481,0x1081084210481,0x1081084210481,0x1080080200481,0x0,0x16c80005b200016c8079801e7e679807982d91e603cc003ea61e603cc79801e600f3f379801e703885,0x0,0x445800111600025f8079803cde679807981e6001ed98007b661e603cc0079bcc01e6f379801e722395,0x7980001e6000079807980001e679807982d900003cc0001e61e603cc00001e60000f379801e703885,0x0,0x2000000008000400020001000080001000000001000040010002000010000400000001000400001000000010004000010000000010040000010000000100400000100208793a7,0x8118007b66000fa9807981e61e6811879835280f31e603cde61f533cc03cc0f30f30f37d4c1e703375,0x0,0x3d39803cde6003d39807980f379879807980799e603cc0f307a17e03cc79801e63cc03f1f801e64d3c5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x282022108442],
[0x182022188442,0x282022108442,0x182022188442,0x282022108442,0x282022108442,0x282022108442,0x282022108442,0x8400210010002002010080402010020400814e3,0x3d39803cde6003d39807980025f8001ed98001e6f307983cc7980f307983cfcc00f307983cc1e64d456,0x282022108442,0x0,0x0,0x0,0x0,0x0,0x0,0x16c80005b200016c80f3001ed987980f302d9b6403cc003ea6b6403ced9001e600f3f5d9001e703885,0x7983cc1e600f37981e600007987980f301e600007980001e679803cc00003cc0000f4e6001e703d95,0x445800111600025f81e6003d3987980f301e6000079800f4e679803cc00003cc03ccf4e6001e722395,0x7980001e600007980f300007987980f302d900003cc0001e6b6403cc00001e60000f5d9001e703885,0x0,0x7983cc1e60f307981e600007987980f301e600007980001e679803cc00003cc0000f4e6001e703d95,0x1ed98007b66000fa981e601e67987980f301e600007980799e679803cc00003cc1e60f4e6001e703d95,0x7980001e60b647980f300007987980f302d900003cc0001e6b6403cc00001e60000f5d9001e703885,0x0,0x0,0x0,0x7980001e61a947980f300007987980f302d900003cc0001e6b6403cc00001e60000f5d9001e703885,0x0,0x0,0x0,0x0],
[0x0,0x282022108442,0x182022188442,0x282022108442,0x182022188442,0x282022108442,0x282022108442,0x282022108442,0x282022108442,0x0,0x3d39803cde6003d3980f3000222c001f530001e6f307983cde600f307983d39800f307983cc1e703856,0x282022108442,0x0,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_2177 : TreeBound (n := 4) 107 (programCode 0x422b071839) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10804c4204481,0x1081084210481,0x10804c4204481,0x1081084210481,0x1080884208481,0x1081084210481,0x1080884208481,0x1080084200481,0x1081084210481,0x1081084210481,0x1081084210481,0x1080084200481,0x0,0x100a0a4220481,0x1022084220481,0x100a0a4220481,0x8040200102004080200808020202002080081ce3,0x10120c4220481,0x1022084220481,0x10120c4220481,0x1042184220501,0x1022084220481,0x1022084220481,0x1022084220481,0x0,0x1042184220501,0xf303cc3cc0f30f300f35b200088b0001ed980035287a73799e601e6007987c59001ed98003cfcc1e7e56,0x1042184220501,0xf303cc3cc0f30f301e65b200088b000204600035287a74e61e60798007987c59001ed98003db30799e56,0x0,0xf30000b640002d90000b6401e6f30811803ced903cc3cc0f31e603cc3cc03cc1e60f30f6cc001e703885],
[0xf30000b6400088b000081180025f8001ed98002d900079805b20000f37983ea6000fa9f983cc01e61556,0xf3000222c00088b00012fc01e6f3079800799e603cc7980f31e603cc3cc07983cc1e60f6cc001e703d95,0x0,0x0,0x0,0xf3000f6cc003db30007d4c0000f3079803cc1e603cc7980f31e603cc3cc3cc03ccf300f6cc001e703d95,0x0,0xf3001e9cc007a73001e9cc0000f3079803cc1e603cc7980f31e603cc3cc3cc03ccf300f6cc001e703d95,0xf3001e9cc01e6f3001e67980025f8001ed98002d9000798f4e6003cc07983ea6000fb8b003cc7983e156,0x0,0x0,0xf300f33cc03ccf300f33cc03ccf3088b07982d903cc3cc0f31e603cc3cc79801e7e600f6cc001e8e9885,0xf300f33cc0f30f300f307980025f8001ed98002d900079f99e601e6007983ea6000fa98003cfcc1e7556,0xf301e63cc0f30f301e63cc16c8f30d4a2d902d903cc3cc0f31e603cc3ced9001f16400f6cc001f267885,0xf301e63cc0798f301e607980025f8001ed98002d90007a731e603cc007983ea6000fa98003d3983cd556,0x0,0x100a0a4220481,0x1022084220481,0x100a0a4220481,0x0,0x10120c4220481,0x1022084220481,0x10120c4220481,0x1042184220501,0x1022084220481,0x1022084220481,0x1022084220481,0x0,0x1042184220501,0x0,0x1042184220501,0x0],
[0x0,0x0,0x0,0xf300012fc00088b00012fc0000f3079800002d903cc3cc0f31e603cc3cc00001e60000f6cc001e703885,0x0,0xf3000408c001023000408c01e6f3079800f31e603cc7980f31e603cc3cc0f303cc3cc0f6cc001e703d95,0x0,0xf3000f6cc003db30007d4c01e6f3079800f31e603cc7980f31e603cc3cc0f303cc3cc0f6cc001e703d95,0x0,0xf3001e9cc007a73001e9cc0000f3079800002d903cc3cc0f31e603cc3cc00001e60000f6cc001e703885,0xf3001e9cc01e6f3001e6f3000222c001f530002d900079bcde600f3007983ea6000fc7e003cde60f4556,0x0,0x0,0x0,0xf300f33cc0f30f300f30f3000222c001f530002d90007b661e60798007983ea6000fa98003db3097f556,0x0,0xf301e63cc0798f301e60f3000222c001f530002d90007a731e603cc007983ea6000fa98003d3983cd556]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_2258 : TreeBound (n := 4) 107 (programCode 0x422b07183a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0xf307983cc1e60f307983cc0002d9000222c0001e9cc079bcde6003cc07983ea6000fa98003cde60f4556]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_2259 : TreeBound (n := 4) 107 (programCode 0x422b07183b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10804c4204481,0x1081084210481,0x10804c4204481,0x1081084210481,0x1080884208481,0x1081084210481,0x1080884208481,0x1080084200481,0x1081084210481,0x1081084210481,0x1081084210481,0x1080084200481,0x0,0x100a0a4220481,0x1022084220481,0x100a0a4220481,0x80402002020080802010080402020020800814e3,0x10120c4220481,0x1022084220481,0x10120c4220481,0x1042184220501,0x1022084220481,0x1022084220481,0x1022084220481,0xf300003cc1e60f303cc07980f379800007980f307983cc1e60f307983cde6001ed98007b66001e68a055,0x1042184220501,0x0,0x1042184220501,0x0,0x0,0x282022108442],
[0x182023188642,0x282022108442,0x182023188642,0x282022108442,0x282022108442,0x282022108442,0x282022108442,0x8400210010002002010080402010020400814e3,0x10d9b983cc1e6003d39843671b283d3b69cc00798f307980f307987983d036503cc3cc0409b301e64dc35,0x282022108442,0x0,0x0,0x0,0x0,0x0,0x0,0x100a0a4220481,0x1022084220481,0x100a0a4220481,0x0,0x10120c4220481,0x1022084220481,0x10120c4220481,0x1042184220501,0x1022084220481,0x1022084220481,0x1022084220481,0x0,0x1042184220501,0x0,0x1042184220501,0x0],
[0x0,0x282022108442,0x182023188642,0x282022108442,0x182023188642,0x282022108442,0x282022108442,0x282022108442,0x282022108442,0x0,0x3d39803cde6003d3980f3000222c001f530001e6f3079bcc1e600f307983d39800f55f803cde60f4556,0x282022108442,0x0,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_2340 : TreeBound (n := 4) 107 (programCode 0x422b07183c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10804c1204481,0x1081084210481,0x10804c1204481,0x1080080200481,0x1080882208481,0x1081084210481,0x1080882208481,0x1080080200481,0x1081084210481,0x1081084210481,0x1081084210481,0x1080080200481,0x0,0x861c468000218711a00002cb4178000218711a00002cb4178ee6b639aca3b9aca003b9e83acaee6b639ad8e6b283b9acb65a0bc001e08ffca00078240104d66e08ffca00077acc9cf9aca0773df5c468077394daca01dce536b28077359401dce537a0eb2800ee6ee959172c9,0x0,0xef599328077394dacbdec2931ec680ee6ee1aca0001ebbd02f735940000ee6b45cd65f5e63210e05ee6b280000430e23400003bb89765077360b359400001dce5461422af0ee1aca00ee6b283b9acdb9aca00000ee6b28ee6b63d6a25087204d65000001dcddc3597bbb642eaa,0x25f800111600025f83cc0001e6000222c0001ed98079bcde60079807983ea6001e600003cde60f45e6,0x0,0x0,0x200200010c658000000060000080080000200000030c6500020000400090000000080800004004008632820021000020000100008010000040863280200000200200400020052ba8,0x0,0x200200010444800040002000008008000400000003044400020000400090000000080800004004008222020020000020000100008200000040822200200000200200400020052ba8,0x3d39803cde6003d3983cc3cc1e60f3222c0001ed98079bcde7e679807983ec47e7e60079bcde60f45e6,0x0,0x79f9803cde60079f983cc3cc1e63cc222c0001ed98079bcde7e679807983ec47e7e601e63cde60f45e6,0x0,0x0,0x0,0x0,0x0,0x0],
[0xc00030020004800110004400804100102814e4,0x79801e7e6079879807980025f8001ed98001ed980799e6f30079807983cc0000f6cc003ccf307ea16,0x0,0xc00010020004800110000400804100102010e4,0x2400090020004800110010400804100102010e4,0x1e67981e61e600f379807980025f8001ed98001ed98fa9bcc1e6079807983cfcc01e9cc003cde60f45e6,0x4400110020004800110020400804100102010e4,0x40002000010008000400020000080080000400000021000000090000000810000000808002000020000100200010000200001000080200000200800002008000002004000200513a8,0x0,0x4400110020004800110020400804100102010e4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa000000048000000220000000280000800000404000837020002000020000400000080401c00e020000020100020080100000000041600e002000020010080000010020852ba7,0x1c7a7980001e600007981e621391e67980f3007b47a0798000079bcc03d31e803cc00003d39801e64dc35,0x0,0x0,0x202000000408000002020000002080002000010004000860020002000020000400002001001c040020000200100080000100002000101c0c0002000200010080000010020872ba7,0x2000160008000000020000800080000800000004000830020002000020000400000000401e0000200000001000200001000000000416000002000000010080000010020852ba7,0x0,0x0,0x0,0x18ae7980001e603cc7981e621391e67980f3007b0ae0798000079bcc03d31e803cc00003d39801e64dc35,0x0,0x0,0x0,0x0],
[0x0,0x402030040005000110000400804200102010e4,0xc00030040005000110004400804200102814e4,0x0,0x0,0xc00530040005000110004400804200102814e4,0x2400090040005000110010400804200102010e4,0x0,0x4400110040005000110020400804200102010e4,0x0,0x0,0x400110040005000110000400804200102010e4,0x0,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_2421 : TreeBound (n := 4) 107 (programCode 0x422b07183d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x16c80005b200016c83cc001f53079fd4c0370fe601e67981e61e603cc003ccf300f3f6cc3cde703375,0x7983cc1e600f37983cc0000f307983cc01e61e607987981e61e603cc3cc03ccf300f6cc001e703d95,0x445800111600025f83cc003db307983cc01e61e607987981e61e603cc0079bcc01e6f6cc001e722395,0x0,0x1e6000bdd8002046000b640002d90798b64035484601e67981e61e603cc79800f4e600f745801e703375,0x1e6079bcc1e601e6079bcc01e6f307983cc01e61e607987981e61e603cc79803cde600f6cc001e703d95,0x1e600222c0007b660012fc0004bf07983cc01e61e607987981e61e603cc79803cde600f6cc001e7241f5,0x1e60f3445a22c1e60f33cc03ccf3088b3cc071e9e601e67981e61e603cc79800f4e600f745801e8e9375,0x0,0x1e63cc079bcc01e6408c0002d9000222c0001e6f3079801e6000f307983ea6000f300003cc00001556,0x1e6004105803cde6007d4c001f53079fd4c0370fe601e67981e61e603cc79800f4e600f745801e703375,0x0,0x1e601e9cc00799e601e9cc007a7307983cc01e61e607987981e61e603cc79803cde600f6cc001e740995,0x0,0x0,0x0,0x1e60f344583cc1e60f33cc03ccf3088b3cc071e9e601e67981e61e603cc79800f4e600f745801e8e9375,0x408c0010230001f533cc00088b000222c000354aa6730097e01e6007987c5d459e600f33cc03cc3cb6,0x1e60f34458f301e61e63cc0798f3097e3cc0aea9e601e67981e61e603cc79800f4e600f745801f44d375,0x1e449a9400079126a500003c893528003c8935280003c89359f359400010c388d0000430e234000059682f0000430e23400003b9acaee6b2800eea6c2caee6b28003b9aca7aef40a773594003b9ad8e6b2800003b9acbdcd651e08ffca001dcd650ee6b45cd653b9acc15ece9a,0x0,0x2804c820c481,0x281088218481,0x2804c820c481,0xf5e0983cc1e60008118000f307980f31e607982db5f8f303cc10230007987b6abf08118003cc1e6189b6,0x280888208481,0x0,0x280888208481,0x280888208481,0x281088218481,0x281088218481],
[0x281088218481,0x280088208481,0x0,0x2400090010082002020080802002020400814e3,0x0,0x0,0x0,0x804005100008a0022020080802014020020814e3,0x80400010000000402020080802000020000814e3,0x804005100010a0042020080802014020040814e3,0x80400010000000802020080802000020000814e3,0x80400410002080082020080802010020080814e3,0x0,0x80400410004080102020080802010020100814e3,0x80400010000000002020080802000020000814e3,0x80400410008080202020080802010020200814e3,0x80400010000000002020080802000020000814e3,0x80400010010000402020080802000020400814e3,0x80400010000000002020080802000020000814e3,0x0,0x8118007b66000811807980025f8001ed98002d90007983cc10230007983ea6000fa9f983cc1e6181d6,0x0,0x8118007b6600081180f3000222c001f530002d90007983cc3db30007983ea6000fa9f983cc1e62ee56,0x8118007b66000fa983cc01e6f30811bcc03529e601e67981e61e603cc03cc0f30f30f6cfcc1e703375,0x0,0x1804c8204481,0x481088210481,0x1804c8204481,0x400010000000802020080802000020000814e3,0x280888208481,0x0,0x280888208481],
[0x80088200481,0x481088210481,0x481088210481,0x481088210481,0x80088200481,0x0,0x400010000002002020080802000020000814e3,0x0,0x400010000002002020080802000020000814e3,0x3d39800f4e6003d3983cc01e6f307983cc01e61e607987981e61e603cc0f303cc3cc0f6cc001e703d95,0x3d39803cde6003d3983cc0002d9000222c0002d900079805b20f30007983ea6000fa9f983cc01e61556,0x0,0x4804c8214481,0x481088210481,0x4804c8214481,0x10400410000000802020080802010020000814e3,0x480888218481,0x0,0x480888218481,0x481088210481,0x481088210481,0x481088210481,0x481088210481,0x480088210481,0x0,0x10400410000002002020080802010020000814e3,0x0,0x10400410000002002020080802010020000814e3,0x0,0x2002000008008000008020000020080004022000110088000400000000800000000c002201110000004000010000100000010002020110008000000008201000020000200017fda8,0x481088210481,0x0],
[0x400010000000802020080802000020000814e3,0x20400090002080082020080802002020080814e3,0x0,0x20400110004080102020080802004020100814e3,0x80088200481,0x481088210481,0x481088210481,0x481088210481,0x80088200481,0x0,0x0,0x0,0x0,0x0,0x1e60008118002046000b640002d90798b64035484601e67981e61e603cc79800f4e600f745801e703375,0x1e60798799e601e6079bcc01e6f307983cc01e61e607987981e61e603cc79803cde600f6cc001e703d95,0x1e6001ed98007b660012fc0004bf07983cc01e61e607987981e61e603cc79803cde600f6cc001e7241f5,0x1e60f3079a22c1e60f33cc03ccf3088b3cc071e9e601e67981e61e603cc79800f4e600f745801e8e9375,0x0,0x0,0x1e6003d39803cde6007d4c001f53079fd4c0370fe601e67981e61e603cc79800f4e600f745801e703375,0x0,0x1e601e67980799e601e9cc007a7307983cc01e61e607987981e61e603cc79803cde600f6cc001e740995,0xf4e60001e6000f4e9cc0002d9000222c0001e60f379801e60000f37983ea6000f307983cc00001556,0x0,0x0,0x8000a00010042000080440010000104,0x6020080408000a00016042080080470010c06104,0x8000a00010042000080440010000104,0x4020100808000a00014042100080460010804104,0x0,0xf30007d4c001f62300b6401e6f30811bcc03529e601e67981e61e603cc408c0f40230f70c8c1e703375],
[0x109d04e40f513903cc1e9cc2139f3084e7cc0079f980799e600799e603d027203cc3cc040e7201e64dc35,0xf3001e9cc00799e6012fc01e6f307983cc01e61e607987981e61e603cc07983cc1e60f6cc001e703d95,0x7980020460007b660012fc00088b000222c0002db2a6730097e0000007987b6a459e600003cc03cc3cb6,0x0,0x0,0xf300003ccf3007d4c0000f307983cc01e61e607987981e61e603cc3cc03ccf300f6cc001e703d95,0x0,0x1e60000798f301e9cc0000f307983cc01e61e607987981e61e603cc3cc03ccf300f6cc001e703d95,0x1e601e7e601e61e601e9cc0002d9000222c0001e60f3798f4e60000f37983ea6000fa9f983cc7983e156,0x0,0x0,0x4000080008000a00010042000080440010000104,0x4020080408000a00016042080080470010c06104,0x4030080008000a00016042000080470010c06104,0x4020080808000a00014042100080460010804104,0x0,0x1e600097e000222c000b640002d90798b64035484601e67981e61e603ccf3000f6cc00f7bf001e703375,0x0,0x3cc0011160007d4c0012fc00088b079a22c02d91e603cc7981e61e603ccf3001e9cc00f6cc001e707545,0x0,0x0,0x0,0x79800f4e6003cfcc007d4c003db307983cc01e61e607987981e61e603ccf3003cfcc00f6cc001e722395,0x1e61e61e607983cc97e3cc0798f3097e3cc0aea9e601e67981e61e603ccf3000f6cc00f7bf001eacf375,0x79801e7e60079bcc01e9cc007a7307983cc01e61e607987981e61e603ccf3003cfcc00f6cc001e740995,0x0,0x1e601e7e601e63cc03cfcc01e6f30811bcc03529e601e67981e61e603ccf3000f6cc00f7bf001e703375,0x0,0x8000a00010042000080440010000104,0x20000408000a00014042080080460010804104,0x8000a00010042000080440010000104,0x20000808000a00014042100080460010804104],
[0x0,0x0,0x0,0xf3000079800012fc0000f307983cc02d91e603cc7981e61e603cc00001e60000f6cc001e703885,0x0,0x0,0x0,0x1e6003d39803cde6007d4c001f53079fd4c0370fe601e67981e61e603cc79800f4e600f745801e703375,0x0,0x0,0x3cc01e6f301e63cc01e9cc0002d9000222c0001e60f379bcde60000f37983ea6000fa9f983cde60f4556,0x0,0x0,0x4000100008000a00010042000080440010000104,0x4020100408000a00014042080080460010804104,0x4020100008000a00014042000080460010804104,0x4020100808000a00014042100080460010804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_2598 : TreeBound (n := 4) 107 (programCode 0x422b07183e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0xf307983cc1e60f30b6401e6f30811bcc035280f31e603cde600f33cc03cc0f30f30f6cfcc1e703375,0x12fc0011160001a943cc0002d9000222c0002046007b661e601e6007983ea6000f30079bdb30799556,0x3cc0798f301e61e60b6401e6f307983cc01e601e67980799e600f33cc07983cc1e60f6cc001e703d95,0x1e60f3097e00025f92fc0002d9000222c0002046007b661e601e6007983ea6000f300f33db3079b3b6,0x0,0x0,0x20000020080000080100000200200000c00020001000000004000200010000060002000100008000400010000800002001004000001010000004001000008100000010010873227,0x0,0x100000080400000201000000801000000c0000000100008200400020001000004004100008010440020002000100000200100400000081044000200200001010000001002086aba7,0x3cc007d4de6003d398b640002d9000222c0002046007b661e601e6007983ea6000f31e603db30799556,0x0,0x0,0x400000021000000084000000210000000c00020001000000104000200010000060000004100000010400000040800002001004000001010000004000004008100000010010873227,0x7d4c001e6f300b640000f307983cc21b280001e63cc1e600f33cfcc000f3f300f6cc001e703375,0x2000000028000000090000000220000000c00020001000000104000200010000060000004100000010400000040800002001004000001010000004000004008100000010010873227,0x0,0xf30000b6400088b0000b640002d9000222c0002046007b661e601e6007983ea6000fa98003db30799556,0x0,0xf30f303cc7980f312fc01e6f30811bcc02d900f33cc03cde602d93cc03cc1e60f30f6cc001e703885,0x0,0x3cc1e60f307981e612fc01e6f307983cc01e601e67980799e601e63cc07983cc1e60f6cc001e703d95,0x0,0x0,0x0,0x0,0xf6cc003db3000fa9fd4c0002d9000222c0002046007b661e601e6007983ea6000f307983db30799556,0x0,0x0,0xf6cc3cc0f3000fa9fd4c0002d9000222c0002046007b661e601e6007983ea6000f307983db30799556,0x0],
[0x1e6001ed98007b660012fc003db307983cc01e6001ed98007b6601e63cc0079bcc01e6f6cc001e722395,0x0,0x7980020460007d4c0012fc003db307983cc01e6003d39800f4e601e63cc00003cc03ccf6cc001e722395,0xf3000079800012fc0000f307983cc02d900003cc0001e602d93cc00001e60000f6cc001e703885,0x0,0x0,0xf30f30f303cc0f312fc0002d9000222c0002046007b661e601e6007983ea6000f30079bdb3079b3b6,0x0,0x1e60f30f307981e612fc0004bf00012fc000222c7980f31e9cde6007983cc0799ef80d93d3983d1426,0x0,0x0,0x1000000004082000020200000020040040000000100008200400020001000004000100008010400020002000100000000100400000081000000200000001010000001002086aba7,0x0,0x10000000040082000100200000100040040000000100008200400020001000004004100008010400020002000100000000100400000081000000200000001010000001002086aba7,0x3cc00f6cc003cfcc012fc0002d9000222c0002046007b661e601e6007983ea6000f31e603db307d7fb6,0x0,0x0,0xf300003cc00012fc0002d9000222c0002046007b661e601e6007983ea6000f300003db3079b3b6,0xf307980001e600000003cc2139f307983cc007a730079800007980003cfcc003cc0000408c001e64dc35,0x0,0xf307980001e600000003cc2139f307983cc007a730079800007980003cfcc003cc0000408c001e64dc35,0x0,0x4000000210000000840000002100000008000060000000100100000400400001060040000100100000400400000800020001004000001010000004000004008000010010010873227,0x80022000800804020120020800804400104024e4,0x0,0x80022000801004040120020800804400104024e4,0x80002000000004000120000800804400104020e4,0x8032200c80400808014032080080460010806504,0x0,0x8022200880400810014022080080460010804504,0x0,0x80046001108004200120040800804400105028e4],
[0x400000021000000084000000210000000802002000008000000010020000020006004000010010000040040000080002000100400000101000000400100000800c000010010873227,0x80086002110004400120080800804400106030e4,0xf30b736cc0000f300005b998088b000079800025f8b7337980001e6007987c59001ed98003cfcc1e7df6,0x0,0xf307a76cc0000f300005b200088b000079800025f87a737980001e6007987c59001ed98003cfcc1e7df6,0x0,0x0,0x0,0x80012000400804020120020800804400104026e4,0x0,0x80012000401004040120020800804400104026e4,0xf3000f6cc00102300042f4fe0798798079800025f8c6637980001e6007987c59001ed98003cfcc1fea76,0x8002200040400808014032080080460010806704,0x0,0x8002200040400810014022080080460010804504,0x0,0x8001200040800420012004080080440010502ee4,0x400020001000082004000000010000000001000000004008200020000000020004004000008010400020040000100000000100400000081040000200000001000800001002086aba7,0x80012000410004400120080800804400106036e4,0x4000000410000002040000008100000008400000004008000025008000080020000088000400040000040100028040100000100008200000080b000000820000002020001830579a8,0x0,0x0,0x0,0x0,0x40000010100000040400000081000000100000600000001001000004004000010600400001001000004004000008000c0001004000001010000004000004008000010010010873227,0x80402004000804020120020800804400104020e4,0x0,0x80402004001004040120020800804400104020e4,0xf30b643cc1e60f300f36331807b6600079800025f8b7337980001e6007987c59001ed98003cfcc1e7df6,0x0,0x0,0x0],
[0x0,0x80402005008004200120040800804400105028e4,0x0,0x80402006010004400120080800804400106030e4,0x40000010100000040400000081000000100400200001000001004000004010000600400001001000004004000008000c0001004000001010000004004000008010000010010873227,0x0,0x0,0x0,0x0,0x0,0x80022000800804020120020800804400104024e4,0x0,0x80022000801004040120020800804400104024e4,0xf3000f6cc003db30007fb6e40798f30079800025f8c6637980001e6007987c59001ed98003cfcc1f70f6,0x8002200080400808014032080080460010806504,0x0,0x8002200080400810014022080080460010804504,0x0,0x8002200080800420012004080080440010502ce4,0x400020001000082004000000010000040001000000004008200020000000020004004000008010400020040000100000000100400000081040000200000001000800001002086aba7,0x80022000810004400120080800804400106034e4,0x0,0x0,0x0,0x0,0x0,0x40000020100000080400000201000000800000600000001001000004004000010600400001001000004004000008000c0001004000001010000004000004008000010010010873227,0x80102004000804020120020800804400104020e4,0x0,0x80402004001004040120020800804400104020e4,0xf30c666cc0000f300f36331807b6600079800025f8b7337980001e6007987c59001ed98003cfcc1e7df6,0x0],
[0x0,0x0,0x0,0x80006005008004200120040800804400105028e4,0x0,0x80006006010004400120080800804400106030e4,0x400030001000000004000000010000200060000001000000000c0000000800000000a000201001000001010000000010000010002030000002000000020200000020200010007d3a8,0x0,0x0,0x0,0xf3001e9cc01e6f3001e9cc0002d9000222c0002046007b661e601e6007983ea6000fa98003db307d6156,0x0,0x0,0x80022000800804020120020800804400104024e4,0x0,0x80022000801004040120020800804400104024e4,0xf30c666cc0000f30007fb6e40798f30079800025f8c6637980001e6007987c59001ed98003cfcc1f70f6,0x8032200080400808014032080080460010806504,0x0,0x8022200080400810014022080080460010804504,0x0,0x8004200080800420012004080080440010502ce4,0x400000801000002004000010010000010001000000004008200020000000020004004000008010400020040000100000000100400000081040000200000001000800001002086aba7,0x80082000810004400120080800804400106034e4,0xf30b736cc0000f30007f3998088b000079800025f8b7337980001e6007987c59001ed98003cfcc1f70f6,0x0,0x0,0x0,0x0,0x0,0x80082002000804020120020800804400104030e4,0x0],
[0x80082002001004040120020800804400104030e4,0xf30079bcc01e6f3003d29333c79f980079800025f8d266f180001e6007987cc999fed98003cfcc2615f6,0x0,0x0,0x0,0x0,0x80082002008004200120040800804400105038e4,0x0,0x80082002010004400120080800804400106030e4,0x4000004010000020040000080100000100000200003000000044000000020009000084000004080008000040000040100000100008200000040800000102000000200800048052e28,0x0,0x0,0x0,0x0,0x1023000408c0010233cc0205530811bcc035280f31e603cde61f533cc03cc0f31023f6cfcc1e703375,0x4a0d5288118000f303cc00088b00012fc00025f87a73f31e9cde6007987c59b65f16479bd3983cde26,0x3db3000f6cc001f533cc0223b307983cc01e601e67980799e61e603cc07983cc01e6f6cc001e722395,0x1e60f307983cc1e612fc0002d9000222c0002046007b661e601e6007983ea6000f300f33db3079b3b6,0x0,0x0,0x1a947986a500003cc0003cc00088b00012fc00025f87a73f31e9cde6007987cd2801f34a003d3983cde26,0x0,0x1a947986a500003cc0003cc00088b00012fc00025f87a73f31e9cde6007987cd2801f34a003d3983cde26,0xf3e21f466799e9cc003cc00088b00012fc00025f87a73f31e9cde6007987c86901f182603d3983cde26,0x0,0x0,0x8000a00014042080080460010804104,0x4000080008000a00014042080080470010804104,0x8000a00014042080080460010804104,0x4000100008000a00014042080080460010804104,0x8020200408000a00014042080080460010804104,0x0],
[0x10230004bf00011163cc0205530811bcc035280f31e603cde6d5933cc03cc0f31023f6cfcc1e703375,0x12fc000f31e6013044e40002d9000222c0002046007b661e601e6007983ea6000f30079bdb30799556,0x408c00102300020463cc0223b307983cc01e601e67980799e679803cc07983cc03ccf6cc001e722395,0x222c000799e602234c7c0002d9000222c0002046007b661e601e6007983ea6000f300f33db30799556,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8000a00014042080080460010804104,0x4030080008000a00014042080080470010806104,0x8000a00014042080080460010804104,0x4020100008000a00014042080080460010804104,0x8020200808000a00014042080080460010804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_2807 : TreeBound (n := 4) 107 (programCode 0x422b07183f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x16c80005b200016c83cc001f53079fd4c0370fe601e7e601e63cc03cc003ccf300f3f6cc3cde703375,0x0,0x6804c821c481,0x481088210481,0x6804c821c481,0x400410000001002040081002000020000814e3,0x480888218481,0x0,0x480888218481,0x481088210481,0x481088210481,0x481088210481,0x481088210481,0x480088210481,0x0,0x400410000002002040081002000020000814e3,0x0,0x400410000002002040081002000020000814e3,0x25f800111600025f83cc001f5307a76cc02d93cc03cde601e63cc03cc00799e603ccf6cc001e703885,0x0,0xc01010000820022040081002000820020814e3,0x401010000000402040081002000020000814e3,0x401010001020042040081002000020040814e3,0x401010000001002040081002000020000814e3,0x0,0x0,0x0,0x401010000000002040081002000020000814e3,0x8401010008080202040081002008020200814e3,0x401010000000002040081002000020000814e3,0x10401010010000402040081002010020400814e3],
[0x401010000000002040081002000020000814e3,0x0,0x0,0x7980001e60b647980f300007987980f302d93cc03cde601e63cc03cc00001e60000f5d9001e703885,0x401010000002002040081002000020000814e3,0x0,0x2804c820c481,0x281088218481,0x2804c820c481,0x0,0x280888208481,0x0,0x280888208481,0x280888208481,0x281088218481,0x281088218481,0x281088218481,0x280088208481,0x0,0x2400090010082002040081002002020400814e3,0x0,0x0,0x0,0xf307983cc2f49630b64001f53087474c0370fe601e7e601e63cc03cc003ccf300f3f73a58de703375,0x0,0x1e60f30f3088dd9012fc001f5307a76cc02d93cc03cde601e63cc03cc00799e603ccf6cc001e703885,0x0,0x0,0x402008048000a00010042000080440010000104,0x1e60f307983dc23007d4c01e6f307983cc01e67980799e601e63cc03cc07983cc1e60f6cc001e703d95,0x402008088000a00010042000080440010000104,0x3cc1e60f307a82301e9cc01e6f307983cc01e67980799e601e63cc03cc0f303cc3cc0f6cc001e703d95],
[0x0,0x3cc1e63cc1e70d943cfcc0000f3086cdcc03529e601e7e601e63cc03cc0f300f3f300f736501e703375,0x0,0x1e60f307983cd2bf4f33cc03ccf3095fdcc071e9e601e7e601e63cc03cc79800f4e600f7afd01e8e9375,0x0,0x400008008000a00010042000080440010000104,0x0,0x1ed98007b66000fa983cc01e6f307983cc01e67980799e601e63cc03cc07983cc1e60f6cc001e703d95,0x7980001e60f307983cc0000f307983cc03529e601e7e601e63cc03cc00000f30000f6cc001e703375,0x3d39800f4e6003d3983cc01e6f307983cc01e67980799e601e63cc03cc0f303cc3cc0f6cc001e703d95,0x0,0x6804c821c481,0x481088210481,0x6804c821c481,0x0,0x480888218481,0x0,0x480888218481,0x481088210481,0x481088210481,0x481088210481,0x481088210481,0x480088210481,0x0,0x0,0x0,0x0,0x3d39803cde60079f983cc0000f307983cc03529e601e7e601e63cc03cc0f300f3f300f6ea601e703375,0x0,0xc01030000820022040081002000820020814e3,0x481088210481,0x401050001020042040081002000020040814e3],
[0x400010000001002040081002000020000814e3,0x0,0x0,0x0,0x80088200481,0x481088210481,0x481088210481,0x481088210481,0x80088200481,0x0,0x0,0x7980001e61c7a79807980007987980f303529e601e7e601e63cc03cc00000f30000fa1e801e703375,0x0,0x0,0x1e60008118002046000b640002d90798b64035484601e7e601e63cc03cc79800f4e600f745801e703375,0x1e60798799e601e6079bcc01e6f307983cc01e67980799e601e63cc03cc79803cde600f6cc001e703d95,0x1e6001ed98007b660012fc0004bf07983cc01e67980799e601e63cc03cc79803cde600f6cc001e7241f5,0x1e60f30799e601e63cc3cc0f30f307983cc01e67980799e601e63cc03cc79803cde600f6cc001f081d95,0x0,0x1e601e7e600001e67983cc00f3f307983cc0079bcc03cc798079bcc03cfcc001ed98004105801e64d3c5,0x1e6003d39803cde6007d4c001f53079fd4c0370fe601e7e601e63cc03cc79800f4e600f745801e703375,0x0,0x1e601e67980799e601e9cc007a7307983cc01e67980799e601e63cc03cc79803cde600f6cc001e740995,0x0,0x0,0x0,0x8000a00010042000080440010000104,0x6020080408000a00016042080080470010c06104,0x8000a00010042000080440010000104,0x4020100808000a00014042100080460010804104,0x0,0x7d4c001e6f300b640000f30811bcc03529e601e7e601e63cc03cc00000f3f300f6cfcc1e703375],
[0x10d9c6ca0f4ed983cc1e9cc21b37307b69cc0079f980798798079bcc03d036503cc3cc0409b301e64dc35,0x1e9cc00799e6012fc0000f307983cc01e67980799e601e63cc03cc00003ccf300f6cc001e703d95,0x1c7ae3d079a22c1e60f33cc3bcdf3088b3cc0445f980798798079bcc03d31e803cde6004105801e833c35,0x0,0x0,0xf300003ccf3007d4c0000f307983cc01e67980799e601e63cc03cc00003cc0000f6cc001e703d95,0x0,0x1e60000798f301e9cc0000f307983cc01e67980799e601e63cc03cc00003cc0000f6cc001e703d95,0x1e601e7e601e61e601e9cc0002d9000222c0002d900079f99e60f30007983ea6000fb8b003cfcc224156,0x0,0x0,0x4000080008000a00016042000080470010c06104,0x4020080408000a00016042080080470010c06104,0x4030080008000a00016042000080470010c06104,0x4020080808000a00016042100080470010c06104,0x0,0x1e600097e000222c000b640002d90798b64035484601e7e601e63cc03cc79800fa9800f7bf001e703375,0x1e60001e61e603cc0d4dcc0000f307983cc03529e601e7e601e63cc03cc79800fa9800f7bf001e703375,0x1e600097e0007d4c0012fc0002d9079a22c03566a601e7e601e63cc03cc79800fa9800f7bf001e703375,0x7983cc1e61e603cc3cc3cc0f30f307983cc01e67980799e601e63cc03cde6003d39800f6cc001ee9bd95,0x0,0x2000048000a00010042000080440010000104,0x3cc007b66003cfcc007d4c001f5307a76cc02d93cc03cde601e63cc03ccf3001ed9800f6cc001e703885,0x2000088000a00010042000080440010000104,0x79801e7e60079bcc01e9cc007a7307983cc01e67980799e601e63cc03cde6003d39800f6cc001e740995,0x0,0x7980799e601e63cc03cfcc01e6f307983cc01e67980799e601e63cc03cde6003d39800f6cc001e703d95,0x0,0x8000a00010042000080440010000104,0x20000408000a00010042000080440010000104,0x8000a00010042000080440010000104,0x20000808000a00010042000080440010000104],
[0x0,0x0,0x0,0xf3000079800012fc0000f307983cc02d93cc03cde601e63cc03cc00001e60000f6cc001e703885,0xf30d4a0001e600000f33cc2139f307983cc0079f980798798079bcc03cfcc003cc0000408c001e64dc35,0x3cc0000f6cc00408c0000f3079c08c03529e601e7e601e63cc03cc00000f30000f7bf001e703375,0x0,0x7980003d764007d4c0000f307983cc02d93cc03cde601e63cc03cc00001e60000f6cc001e703885,0x0,0x0,0x3cc01e6f301e63cc01e9cc0002d9000222c0002d90007a731e60f30007983ea6000fc7e003d3984c0556,0x0,0x0,0x4000100008000a00014042000080460010804104,0x4020100408000a00014042100080460010804104,0x4020100008000a00014042000080460010804104,0x4020100808000a00014042100080460010804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_2984 : TreeBound (n := 4) 107 (programCode 0x422b071840) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0xf30b736cc0000f300005b99807980001e6000025f8b733f300003cc007987c59000fa98003d3983cddc6,0x80022010800804020140021000804400108044e4,0x0,0x80022010801004040140021000804400108044e4,0x80002010000004000140001000804400108040e4,0xf303cc3cc3565b303cc003cc03ccf300f31e60222c3cc1e61704fcc007983ea6001ef7e003db30799766,0x0,0xf303cc3cc2dcdb303cc0079803cde600f33cc025f83cc1e60f6cfcc007987b66001f164003db30799c76,0x4000000010000a0204000200010000800000000000340400002000000008800000008800000004000a020200020000200000100008200000040a00000202000000204000200052ba8,0x80042011108004200140041000804400109048e4,0x0,0x8008201211000440014008100080440010a050e4,0x0,0x0,0x0,0x0,0x0,0x0,0x80006000100804020140021000804400108040e4,0x0,0x80006000101004040140021000804400108040e4,0xf30000b640002d900007983cc1e60f3079800025f8007b6600003cc007987b66001ed98003db30799a96,0x0,0x0,0x0,0x4000000030000000240000000900000000a00000003400400020000400088000000088000004040008020200020000200000100008200000040a00000202000000204000200052ba8,0x80006000108004200140041000804400109048e4,0x0,0x8000600011000440014008100080440010a050e4,0x0],
[0x0,0x0,0x0,0xf303cc3cc2d90f307983cc0004bf00012fc00025f87981e61e9cfcc007987b66001f164003db30799c76,0x0,0x0,0x0,0x79800241200081180012fc0004bf00012fc00025f87981e61e9cfcc007987a73001f164003db3079d936,0x3cc1e60f307981e612fc0004bf00012fc00025f87981e61e9cfcc007987980799f165e63db3079d936,0x3cc222cf3088ce6012fc0004bf00012fc00025f87981e61e9cfcc007987980799f165e63db3079d936,0x0,0x1ed98002046000f3003cc2139f307983cc007a730079800007980003cfcc003cc0000408c001e64dc35,0x0,0x0,0x3cc00f6cc003cfcc012fc0002d9000222c000222c007a731e603cc007983ea6000f379803d3984c23b6,0x0,0x0,0xf300003cc00012fc0002d9000222c000222c007a731e603cc007983ea6000f300003d3983cf3b6,0xf307980001e600000003cc2139f307983cc007a730079800007980003cfcc003cc0000408c001e64dc35,0x79800204d980799e6012fc0004bf00012fc00025f87981e61e9cfcc007987a73001f173303db3079d936,0xf307980001e600000003cc2139f307983cc007a730079800007980003cfcc003cc0000408c001e64dc35,0xf300003cc1e60f307a76cc0004bf00012fc000222c7981e61e9cfcc007983ea6001ef7e003db30799766,0x0,0x0,0x80012000400804020140021000804400108046e4,0x0,0x80012000401004040140021000804400108046e4,0x1dcd65001dd4d85940077536165000eee25d9400079126a50001e969e507283b9aeb8711aee6b9f35941dcd68b9aca0ee6b2800004a817de5be8a536b2801dd11eacccb4186e6b2800001dcd65003b9ad8ecc0388400ef599328003bd664ca000ef599328001dd4d85999a04b3870a,0x8002200040400808014022100080460010804504,0x0,0x8002200040400810014022100080460010804504,0x0],
[0x8001200040800420014004100080440010904ee4,0x400020001000082004000000010000000001000000004008200020000000020004004000008010400020040000100000000100400000081040000200000001000800001002086aba7,0x8001200041000440014008100080440010a056e4,0x400000041000000084000000810000000840000000400800000c8080000800200000880004000800000400800240402000001000082000000809000000820000002010000830571a8,0x0,0x0,0x0,0x0,0x0,0x0,0x1e67980f33cc01e67d4c0000f307983cc02d900003cc0001e600003cc00001e60000f6cc001e703885,0x3cc1e61209798222c3cc0004bf00012fc00025f87981e61e9cfcc007987980799f165e63db3079d936,0x7983cc1e63cc07987d4c0000f307983cc035280001e60001e600003cc00000f30000f6cc001e703375,0x0,0x7983cc7983cc0f307d4c0000f307983cc035280001e60001e600003cc00000f30000f6cc001e703375,0x0,0x0,0x3d39803cc1e603cde63cc0002d9000222c000222c007a731e603cc007983ea6000f379803d3984c0556,0x0,0x0,0x1e6003d39803cde6007d4c001f53079fd4c0370fe601e67981e61e603cc79800f4e600f745801e703375,0x0,0x79800f4e6003cfcc007d4c003db307983cc01e67980799e601e679803cde6003d39800f6cc001e722395,0x3cc0003cc00007d4c0000f307983cc035280001e60001e600003cc00000f30000f6cc001e703375,0x0,0x0,0x80022000800804020140021000804400108044e4,0x0,0x80022000801004040140021000804400108044e4,0x40000010100000020400000081000000107030000100040000400100000200000000a000381004000200010000000020000010002030000004080000010200000020200010107ee28,0x8002200080400808014022100080460010804504,0x0],
[0x8002200080400810014022100080460010804504,0x1dcd650003c11ff94007753616500077acc994003bb897650003b9aca0000003b9aca000043fcca02ca0ee6ee1aca03d77a0500003d77a0500003b9aca3b9acdb9adac400236168b9aca1dcd65003b9acbe08ffca003ba9b0b28003bddd823401ddc4bb28001ddc4bb2f77153a007a,0x8002200080800420014004100080440010904ce4,0x0,0x8002200081000440014008100080440010a054e4,0x0,0x0,0x0,0x0,0x0,0xf30b736cc0000f301e65b99807980001e6000025f8b733f300003cc007987c59000fa98003d3983cddc6,0x80202008000804020140021000804400108040e4,0x40000020100000080400000201000000800002200000008000000010010000020600400001001000004004000008000002010040000010100000040000000080000c0010010873227,0x0,0x80002008000004000140001000804400108040e4,0xf307983cc001f5301e6001e601e7e601e61e60222c007a7307983cc007983ea6000fa98003d3983dc856,0x0,0xf303cc3cc2dcdb303cc0079803cde600f33cc025f83cc1e60f6cfcc007987b66001f164003db30799c76,0xf30b643cc0000f301e65b20007980001f5300025f87a73f31e603cc007987c59000fa98003d3983cddc6,0x80006009008004200140041000804400109048e4,0x400000201000000804000002010000008002002000008000000010020000020006004000010010000040040000080002000100400000101000000400100000800c000010010873227,0x8000600a01000440014008100080440010a050e4,0x0,0x0,0x0,0xf300003cc25f8f303cc0f30004458001023000222c7981e61e9cfcc007983ea6001ef7e003db30799766,0xf3001e9cc01e6f3001e9cc0002d9000222c000222c007a731e603cc007983ea6000fa98003d3984c0556,0x0,0xf30b736cc0000f30007f399807980001e6000025f8b733f300003cc007987c59000fa98003d3983cddc6,0x80022000800804020140021000804400108044e4,0x0,0x80022000801004040140021000804400108044e4],
[0x80002000800004000140001000804400108040e4,0x8022200080400808014022100080460010804504,0x0,0x8022200080400810014022100080460010804504,0x4000000010000a0204000200010000001000000000340400002000000008800000008800000004000a020200020000200000100008200000040a00000202000000204000200052ba8,0x80042000808004200140041000804400109048e4,0x0,0x8008200081000440014008100080440010a050e4,0x0,0x0,0x0,0x0,0x0,0x40000100100000400400000401000001006222000110000000400000000802000000a000311108000004008000000020000010002031110008000000008200000020100008817fda8,0x80082002000804020140021000804400108050e4,0x0,0x80082002001004040140021000804400108050e4,0x4000008010000040040000080100000100010000002080000017318c0005804200009000008008000e630100030080200000100010200000080800000103980000202400120063668,0x0,0x0,0x0,0x1dcd6500773d075940ee6d04d6500ee729b5940773770d6500773770d6500003b9acbdcd694043f38e05eee25d94003d77a0500003d77a05003bd664caee6b2bb9adad2ea8f8e08b9aca1dcd65003b9acbe08ffca003ba9b0b28003bde15a9c7205c4bb28001ddc4bb2fea9121607a,0x80082002008004200140041000804400109058e4,0x0,0x8008200201000440014008100080440010a050e4,0x0,0x0,0x0,0x0,0x0,0x0,0x0],
[0x1f53000f6cc001f533cc0000f307983cc02d900003cc0001e6001e9cc00001e60000f6cc001e703885,0x3cc1e612097981e603cc0004bf00012fc00025f87981e61e9cfcc007987980799f165e63db3079d936,0x0,0x0,0x7a730079bcc00f3f33cc0000f307983cc035280001e60001e600f33cc00000f30000f6cc001e703375,0x0,0x0,0x3cde603cc001e9cde6b640002d9000222c000222c007a731e603cc007983ea6000f379803d3983cd556,0x0,0x0,0x8000a00014042100080460010804104,0x4000080008000a00014042100080460010804104,0x8000a00014042100080460010804104,0x4000100008000a00014042100080460010804104,0x8020200408000a00014042100080460010804104,0x0,0x0,0x0,0x204600102300020463cc0000f307983cc02d900003cc0001e6005b5cc00001e60000f6cc001e703885,0x0,0x0,0x10d97cc00003ccf301e63cc2139f307983cc007a8d9479bcc007980003cfcc003cc0000408c001e64dc35,0xf4e6007a73000f4e63cc0000f307983cc02d900003cc0001e602d93cc00001e60000f6cc001e703885,0xf303cc00003ccf301e63cc2139f307983cc007a730079bcc007980003cfcc003cc0000408c001e64dc35,0x0,0x0,0x0,0x0,0x8000a00014042100080460010804104,0x4030080008000a00014042100080460010806104,0x8000a00014042100080460010804104,0x4020100008000a00014042100080460010804104],
[0x8020200808000a00014042100080460010804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_1688 : TreeBound (n := 4) 107 (programCode 0x422b0718) := by
  conv in programCode _ => reduce
  exact branchFour (k := (1,1)) (by decide +kernel) part100_1689 part100_1770 part100_1851 part100_1852 part100_1933 part100_2014 part100_2095 part100_2096 part100_2177 part100_2258 part100_2259 part100_2340 part100_2421 part100_2598 part100_2807 part100_2984

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_3177 : TreeBound (n := 4) 107 (programCode 0x422b0719) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x1084090210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_3179 : TreeBound (n := 4) 107 (programCode 0x422b071a51) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080490218481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_3180 : TreeBound (n := 4) 107 (programCode 0x422b071a52) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1081090210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_3181 : TreeBound (n := 4) 107 (programCode 0x422b071a53) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080490218481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_3182 : TreeBound (n := 4) 107 (programCode 0x422b071a54) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1080481218481,0x1081084210481,0x1080481218481,0x1080080210481,0x1080882210481,0x1081084210481,0x1080882210481,0x1080080210481,0x1081084210481,0x1081084210481,0x1081084210481,0x1080080210481,0x0,0x100bcc821c481,0x1022088210481,0x100bcc821c481,0xf3000222c00088b0000f30f307983cc1e607982e86d39bcc01e600001e63ce04da7300000f3003cc3cb6,0x1012088218481,0x1022088210481,0x1012088218481,0x80402000000000802020080802000020000814e3,0x1022088210481,0x1022088210481,0x1022088210481,0x80402000000000802020080802000020000814e3,0xf307983cc1e60f30000000f307983cc1e607982d90079bcc01e600001e63cde67a7300000f3003cc3cb6,0x0,0xf307983cc1e60f30000000f307983cc1e607982d90079bcc01e600001e63cde67a7300000f3003cc3cb6,0x0,0x0,0x180428210222],
[0x180428210222,0x580428210a62,0x180428210222,0x2400090000000402010082002000020000814e3,0x280428210682,0x180428210222,0x280428210682,0x180428210222,0x480428210a62,0x480428210a62,0x480428210a62,0x0,0x0,0x0,0x0,0x0,0x100bcc821c481,0x1022088210481,0x100bcc821c481,0x80002008000001002040081002000020000814e3,0x1012088218481,0x1022088210481,0x1012088218481,0x0,0x1022088210481,0x1022088210481,0x1022088210481,0xf300003cc1e60f3000000000000000001e601e67980799e601e63cc03cc00003cc0000f300001e703d95,0xf307983cc1e60f30000000f307983cc1e607982d90079bcc01e600001e63cde67a7300000f3003cc3cb6,0x0,0xf307983cc1e60f30000000f307983cc1e607982d90079bcc01e600001e63cde67a7300000f3003cc3cb6,0x0],
[0x0,0x180428210222,0x180428210222,0x580428210a62,0x180428210222,0x0,0x280428210682,0x180428210222,0x280428210682,0x180428210222,0x480428210a62,0x480428210a62,0x480428210a62,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_3263 : TreeBound (n := 4) 107 (programCode 0x422b071a55) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080890210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_3264 : TreeBound (n := 4) 107 (programCode 0x422b071a56) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8040201000400808018048200101042020040b04]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_3265 : TreeBound (n := 4) 107 (programCode 0x422b071a57) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080890210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_3266 : TreeBound (n := 4) 107 (programCode 0x422b071a58) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1081081210481,0x1080084210481,0x1081081210481,0x1080080210481,0x1080882210481,0x1080084210481,0x1080882210481,0x1080080210481,0x1080084210481,0x1080084210481,0x1080084210481,0x1080080210481,0x0,0x180488218481,0x481088210481,0x180488218481,0x0,0x280888210481,0x80400010000000002020080802000020000814e3,0x280888210481,0x80088210481,0x481088210481,0x481088210481,0x481088210481,0x80088210481,0x0,0x0,0x0,0x0,0x0,0x0],
[0xf30000b6400088b000079bcc01e6f301e63cc0204601e7e60f301e601e60f4e600f379800f301eda8856,0x0,0x0,0xf300003cc0002d9000079bcc01e6f301e63cc0204601e7e60f301e601e60f4e600f379800f301eda8856,0xf3000408c003db30003cc3cc01e6f301e63cc0204601e7e60f301e601e60f4e600f379800f301edecdd6,0x0,0xf30007d4c001f530007983cc01e6f301e63cc0204601e7e60f301e601e60f4e600f379800f301eda8856,0x0,0xf3001e9cc01e6f3001e603cc01e6f301e63cc0204601e7e60f301e601e60f4e600f379800f301ede5456,0xf3001e9cc0f30f3001e603cc01e6f301e63cc0204601e7e60f301e601e60f4e600f379800f301ede5456,0x0,0x0,0xf300f33cc0f30f300f3003cc01e6f301e63cc0204601e7e60f301e601e60f4e600f379800f301ef8e856,0x0,0xf301e63cc0798f301e6003cc01e6f301e63cc0204601e7e60f301e601e60f4e600f379800f301f174856,0x0,0x180488218481,0x481088210481,0x180488218481,0x401010000000002040081002000020000814e3,0x280888210481,0x0,0x280888210481,0x80088210481,0x481088210481,0x481088210481,0x481088210481,0x80088210481,0x0,0x0,0x0,0x0],
[0x0,0xf307983cc0002d9097e003cc01e6f301e63cc0222c01e6f307983cc01e60f4e600f379800f301e9dc856,0x0,0xf307983cc001f53097e003cc01e6f301e63cc0222c01e6f307983cc01e60f4e600f379800f301e9dc856,0x0,0xf300003cc0000f3000079bcc01e6f301e63cc0222c01e6f307983cc01e60f4e600f379800f301e9dc856,0xf3000408c003db30003cc3cc01e6f301e63cc0222c01e6f307983cc01e60f4e600f379800f301ea37a56,0x0,0xf30007d4c001f530007983cc01e6f301e63cc0222c01e6f307983cc01e60f4e600f379800f301e9dc856,0xf307983cc0798f30007983cc01e6f301e63cc0222c01e6f307983cc01e60f4e600f379800f301e9dc856,0xf3001e9cc01e6f3001e603cc01e6f301e63cc0222c01e6f307983cc01e60f4e600f379800f301eacf856,0xf3001e9cc0798f3001e603cc01e6f301e63cc0222c01e6f307983cc01e60f4e600f379800f301e9dc856,0x0,0x0,0xf300f33cc0f30f300f3003cc01e6f301e63cc0222c01e6f307983cc01e60f4e600f379800f301f35a856,0x0,0xf301e63cc0798f301e6003cc01e6f301e63cc0222c01e6f307983cc01e60f4e600f379800f301e9dc856]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_3347 : TreeBound (n := 4) 107 (programCode 0x422b071a59) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1081090210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_3348 : TreeBound (n := 4) 107 (programCode 0x422b071a5a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1081090210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_3349 : TreeBound (n := 4) 107 (programCode 0x422b071a5b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1081090210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_3350 : TreeBound (n := 4) 107 (programCode 0x422b071a5c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080090210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_3351 : TreeBound (n := 4) 107 (programCode 0x422b071a5d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x100a0d021c481,0x1022090210481,0x100a0d021c481,0x0,0x801a60001200a0802000880022000820500814e3,0x80002000020000802000080402000020000814e3,0x8010a0002200a0802001080042001020500814e3,0x80002000020000802000080002000020000814e3,0x801120004200c080300204008200201068081ca3,0x80002000020000802000080002000020000814e3,0x80132000c200c080300204010200601078081ca3,0x0,0x80102001020080802008080202008020400814e3,0x80002000020000802000080002000020000814e3,0x80102002020000802010080402010020000814e3,0x0,0x80402004020100802020080802020020800834e3,0x0,0x0,0x0,0x1012090218481,0x80402000020000802080082002000020000814e3,0x1012090218481,0x80402004020100802080082002020020800834e3,0x1022090210481,0x1022090210481,0x1022090210481,0xf300003cc1e60f303cc07980f379800007980f3f3003cfcc00f3f3003cc00001ed98007980001e68a055,0x1042190230501,0x802020040c000880018048200101060020402104,0x1042190230501],
[0x802020080c000900018048200101060020804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_3384 : TreeBound (n := 4) 107 (programCode 0x422b071a5e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x8040e00004000880018048200101060020402104,0x8000a00014000880018048200101060020402104,0x0,0x108890210481,0x409890210481,0x108890210481,0x0,0x209890210481,0x47200804400088001800b200101060020402b04,0x209890210481,0xfa9f983defc00f307b660008118001ed98002d90079bcc001f53001e63ced900f379800f33cc1f6bb6,0x409890210481,0x409890210481,0x409890210481,0x0,0x808c90218481,0x609890210481,0x808c90218481,0x8400200000102080082002010020000814e3,0x0,0x40000001100000001400000011000000012000000102000000110000000810000000c003e10000002010040036080000020080020031e0002009000010008800010008001500fd7a8,0xf300012fc0004bf0000fa980025f8001ed98001e60f4e6011160000f4e60f4e600f301e60f33cc225fb6,0x0,0xf300012fc0004bf0000fa980025f8001ed98001e61e7e60097e0001e7e60f4e600f307980f33cc2dc3b6,0xf3000222c00088b00011160008118001ed98003844e618799e60000f4e63cf3bb8f301e60f33cc2268b6,0xf300012fc0004bf0000fa980025f8001ed98001e6799e607b66000799e60f4e600f3003ccf33cc22d936,0x0,0x0,0x0,0xf300012fc0004bf0000fa980025f8001ed98001e9cc1e63cde6003cc1e60f4e600f30f300f33cc1e93b6,0xf3000222c00088b00011160008118001ed98002e83811bcc1e6003cc1e63ced900f30f300f33cc1e9cb6],
[0xf300012fc0004bf0000fa980025f8001ed98001ed981e61e7e6007981e60f4e600f33cc00f33cc9813b6,0xf3000222c00088b00011160008118001ed98003528811bcc1e6000001e63ced900f300000f33cc1e9cb6,0x0,0x4000000010000a000400008001000040004000000014000a2004000008000000040010000080040000200200001000200001004000000814400002000000010000000010020866ba7,0x0,0x8040a00014000880018048200101060020402104,0x8002200044000880018048200101060020402b04,0x8060200404000880018048200101060020402104,0x0,0xf522cf3003cfcc0f307b660008118001ed98002d90822d2c001f53001e63cef760f379800f33cc1f7156,0x82002082000480018000600100840020502ce4,0x452508097e0001e67daed93900f30001e60f3f30079bcc00f3f3003d027203cc79807980001e68a8c5,0x0,0x1f6237d4c001e600f379f980025f8001ed98002d9001e9cc03ed39001e60f4edb75379800f33cc1f6856,0x7987987981e6079879f980025f8001ed98002d9001e9cc001023001e60f4e600f379800f33cc23add6,0x80020800820004800180102001008400204024e4,0xf307983cc1e60f3079f980025f8001ed98002d9001e9cc001f53001e60f4e600f379800f33cc1f6856,0x4020800820004800180102001008400204024e4,0x802020082000480018004200100840020402ce4,0x802020082000480018004200100840020402ce4,0x10020400820004800180082001008400204034e4,0x20000820004800180002001008400204024e4,0x20020800820004800180102001008400204024e4,0x0,0x4002100082000480018020200100840020c064e4,0x8070200404000880018048200101060020402104,0x8008200104000880018048200101060020402904,0x8048200104000880018048200101060020402904,0x0,0x14100100010100400041000020001000800000041000000090000000810000000c0002000300000080400000c010000008000802000001002800010020200010008001481753a8,0x421090210481,0x452508097fe601e67daed93900f30001e60f3f30079bcc00f3f3003d027203cc79807980001e68a8c5],
[0x108004202000480018000a001008400205038e4,0x221090210481,0x0,0x221090210481,0x0,0x421090210481,0x421090210481,0x421090210481,0x90210481,0x800090210481,0x90210481,0x800090210481,0x90210481,0x8040200004000880018048200101060020402104,0x8020200404000880018048200101060020402104,0x8040200004000880018048200101060020402104,0x8020200804000880018048200101060020406104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_3465 : TreeBound (n := 4) 107 (programCode 0x422b071a5f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x100a0d021c481,0x1022090210481,0x100a0d021c481,0x80002010040001002080082002000020000814e3,0x1012090218481,0x0,0x1032081218481,0x1022084210481,0x1032081218481,0x1022088210481,0x1022082210481,0x1022084210481,0x1022082210481,0x0,0x1022084210481,0x1022084210481,0x1022084210481,0x0,0x1022088210481,0x800220004c000880014048080101060020402b04,0x1022088210481,0xf3000408c003db30003db30002d90001f53000222c01e6f31e603cc01e60f4e600f379800f3798428756,0x1012090218481,0x0,0x1062181230501,0xf300003cc0f30f303cc1e600007980000f301e600007980001e60f303cc00003d39800f300001e703d95,0x1062181230501,0x80002008040001002000080002000020000814e3,0x10521c2238501,0x80002008040001002000080002000020000814e3,0x10521c2238501],
[0x0,0x1042184230501,0x80002008040001002000080002000020000814e3,0x1042184230501,0x0,0x0,0x0,0x0,0x0,0x1022090210481,0x1022090210481,0x1022090210481,0x0,0x8040380400a1002080082002000820500814e3,0xc62190230501,0x10080580400a1002080082002001020500814e3,0x2008040001002080082002000020000814e3,0x2010088040081002080082002002020400814e3,0x0,0x4020108040081002080082002004020400814e3,0x0,0x462190230501,0xc62190230501,0x462190230501,0x842190230501,0x842190230501,0x842190230501,0x842190230501,0x42190230501,0x1042190230501,0x0,0x132090218481],
[0x422090210481,0x132090218481,0x0,0x222090210481,0x420008408400808018048200101042020040b04,0x222090210481,0x0,0x422090210481,0x422090210481,0x422090210481,0x802090210481,0x802090210481,0x2090210481,0x802090210481,0x2090210481,0x1042190230501,0x0,0x800020040001002080082002000020000814e3,0xc62190230501,0x1000040040001002080082002000020000814e3,0x0,0x0,0x7b660079f98007b660079802d90001e679802d9001e9cc1e60f3001e60f4e600f379800f303cc5c756,0x0,0x0,0x462190230501,0xc62190230501,0x462190230501,0x842190230501,0x842190230501,0x2090210481,0x842190230501],
[0x2090210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_3562 : TreeBound (n := 4) 107 (programCode 0x422b071a60) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0xf307983cc0002d9079888b000222c001f530002d9001e9cc1e60f3001e60f4e600f379800f37983cd556,0x0,0x121090210481,0x420090210481,0x121090210481,0x100404014000500018000a001008400209048e4,0x0,0x0,0x0,0x0,0x420090210481,0x420090210481,0x420090210481,0x20090210481,0x822090210481,0x420090210481,0x822090210481,0x20090210481,0xf307983cc0798f307980f3000222c001f530002d9001e9cc1e60f3001e60f4e600f379800f37983cd556,0x0,0x400000005000000014000000110000000108000000420000000a0000000820000000800060001000500800001608010008008000800020001009000010020600010010000842553a8,0xf300012fc0004bf0001023000222c001f530001e60f4e6011160000f4e60f4e600f301e60f379840bfb6,0x0,0xf300012fc0004bf0001023000222c001f530001e61e7e60097e0001e7e60f4e600f307980f37984c23b6,0x0,0xf300012fc0004bf0001023000222c001f530001e6799e607b66000799e60f4e600f3003ccf3798413936,0x0,0x0,0x400000005000000014000000110000000108000000820000000a00000008200000008000a0001000000800002200002000008001000080001008000010020800010010000902593a8,0xf3000222c00088b000111600044580010230001ed9f9801e7f5303cc1e61e6f3007a54a00f3798b69936,0x0],
[0xf300012fc00088b000102300044580010230001ed9f9803cdf5307981e61e679807a36400f37983d1426,0x0,0x0,0x0,0x0,0x0,0xf30de47c40000f3000097e0008118001f530003a290018005b2000001e63cf7878f300000f37983cde56,0xf30bdfa2c0798f3000097e0008118001f530001e644d18011160000f4e63cef760f301e60f37983cde56,0x0,0xf307983cc01e6f3000088b000222c001f530001e61e7e60097e0001e7e60f4e600f307980f37984c0556,0xf30bdfa2c0798f3000097e0007d4c001f53000361f4d18f31e60000f4e63cef760f37b660f37983cddc6,0xf307983cc007a73000088b000222c001f530001e6799e607b66000799e60f4e600f3003ccf379840a156,0xf3079a22c0000f3000097e0008118001f530003528811bcc1e603cc01e63ced900f379800f37983cde56,0x0,0xf30bdfa2c0000f3000097e0007d4c001f53000361f4d18001e603cc01e63cef760f379800f37983cddc6,0xf307983cc0002d9000088b000222c001f530001e9cc1e63cde6003cc1e60f4e600f31e600f37983cd556,0xf3079a22c0002d9000097e0008118001f530002e83811bcc1e6003cc1e63ced900f31e600f37983cde56,0x0,0xf3079a22c0000f3000097e0008118001f530003528811bcc1e603cc01e63ced900f379800f37983cde56,0xf3079a22c0002d9000097e0008118001f5300025f88119e61e601e601e63ced900f379800f37983cde56,0xf3079a9c40002d9000097e0008118001f530002ec0411bcc1e6003cc1e63cf5280f31e600f37983cde56,0xf307983cc0000f3000088b000222c001f53000222c01e6f31e603cc01e60f4e600f379800f37983cd556,0xf3000408c003db30003db3000222c001f530002d9001e9cc1e60f3001e60f4e600f379800f3798428756,0x0,0xf30de21cc0000f301e61e60008118001f530003a290018005b2000001e63cf7878f300000f37983cde56,0xf307983cc007a7301e60f3000222c001f530001e60f4e6011160000f4e60f4e600f301e60f379840a156,0x0,0xf307983cc01e6f301e60f3000222c001f530001e61e7e60097e0001e7e60f4e600f307980f37984c0556,0xf30de21cc007a7301e61e60008118001f530003a290018f31e60000f4e63cf7878f301e60f379840aa56,0xf307983cc00102301e60f3000222c001f530001e6799e607b66000799e60f4e600f3003ccf3798411ad6,0x0,0x0],
[0x0,0xf307983cc0798f301e60f3000222c001f530001e9cc1e63cde6003cc1e60f4e600f31e600f37983cd556,0xf30b643cc0798f301e61e60008118001f530002e83811bcc1e6003cc1e63ced900f31e600f37983cde56,0xf307983cc0798f301e60f3000222c001f530001ed981e61e7e6007981e60f4e600f31e600f37983cd556,0xf30b643cc0000f301e61e60008118001f530003528811bcc1e6000001e63ced900f300000f37983cde56,0x0,0x0,0x0,0x0,0x82212084000500018000600100840020904ce4,0x82002084000500018000600100840020904ce4,0x40023000840005000180202001008400208044e4,0x0,0x0,0x7987987981e607987a73000222c001f530002d9001e9cc003db3001e60f4e600f379800f3798437a56,0x0,0x1e60f307983cc0f307b6600044580010230002d9000f6cc0130b3001e61e7e6007a36400f37983ec276,0x1e60f8b9983cfcc007b6600044580010230002d9000f6cc2ec0b3001e61e7e6007a37330f37983ec276,0x802020084000500018004200100840020804ce4,0x20200840005000180002001008400208044e4,0x10020400840005000180082001008400208054e4,0x20000840005000180002001008400208044e4,0x2002080084000500018010200100840020c064e4,0x0,0x40021000840005000180202001008400208044e4,0xf307983cc0000f301e60f3000222c001f530002d9001e9cc1e60f3001e60f4e600f379800f37983cd556,0xf3001e9cc01e6f3001e6f3000222c001f530002d9001e9cc1e60f3001e60f4e600f379800f37984c0556,0x0,0x121090210481,0x420090210481,0x121090210481,0x0],
[0x0,0x799e607983cc0799e6f3000222c001f530002d9001e9cc003db3001e60f4e600f379800f3798428756,0x0,0xf31e603cc1e60f31e6f3000222c001f530002d9001e9cc001f53001e60f4e600f379800f37983dc856,0x420090210481,0x420090210481,0x420090210481,0x20090210481,0x822090210481,0x420090210481,0x822090210481,0x20090210481,0x0,0x121090210481,0x400090210481,0x121090210481,0x108004204000500018000a001008400209058e4,0x0,0x0,0x0,0x0,0x400090210481,0x400090210481,0x400090210481,0x90210481,0x842190230501,0x90210481,0x842190230501,0x90210481,0x0,0x141c90218481,0x441090210481],
[0x141c90218481,0x0,0x183af3d79e9418000f301e600081180010230002d90c1d55c307557001e63cf0746ba41d19f37983cde26,0x1f233e13d4136679801e600081180010230002d90088ecc011253001e63ced9007a36400f379840aa26,0x16c87985b200003cc0001e600081180010230002d90bddbcc2e83f3001e63ced9007a36400f37983cde26,0xf307983cc1e60f307a73000222c001f530002d9001e9cc001f53001e60f4e600f379800f37983dc856,0x441090210481,0x441090210481,0x441090210481,0x40090210481,0x842190230501,0x842190230501,0x842190230501,0x40090210481,0x8020200404000900018048200101060020804104,0x0,0x141c90218481,0x441090210481,0x141c90218481,0x104004924000500018000a001008400209048e4,0x1bc95d47c40079800f301e60008118001f530002d90de47c41e60f3001e63cf7910d379800f379840aa56,0x0,0x0,0x0,0x441090210481,0x441090210481,0x441090210481,0x40090210481,0x842190230501,0x842190230501,0x842190230501,0x40090210481],
[0x8020200804000900018048200101060020804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_3178 : TreeBound (n := 4) 107 (programCode 0x422b071a) := by
  conv in programCode _ => reduce
  exact branchFour (k := (2,1)) (by decide +kernel) part100_3179 part100_3180 part100_3181 part100_3182 part100_3263 part100_3264 part100_3265 part100_3266 part100_3347 part100_3348 part100_3349 part100_3350 part100_3351 part100_3384 part100_3465 part100_3562

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_3723 : TreeBound (n := 4) 107 (programCode 0x422b071b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x1084090210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_3725 : TreeBound (n := 4) 107 (programCode 0x422b071c51) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x40002000100008000400020001000080004002000110000000400010000800000000c000210010000040040000000100000100020020010080000000200200000200000200017ffa8]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_3726 : TreeBound (n := 4) 107 (programCode 0x422b071c52) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1081090210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_3727 : TreeBound (n := 4) 107 (programCode 0x422b071c53) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0xf307983cc1e60f307980003cc00044729407cd373001e9cc01e6f3003cc00000f30000f6cda95e703375]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_3728 : TreeBound (n := 4) 107 (programCode 0x422b071c54) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10804c1204481,0x1081084210481,0x10804c1204481,0x1080080200481,0x1080882208481,0x1081084210481,0x1080882208481,0x1080080200481,0x1081084210481,0x1081084210481,0x1081084210481,0x1080080200481,0x0,0x600000001800000006000000018000440060041100100104400600401000060004000100010000400040000800100001004400401011001004000004008110010010010873227,0x400410000000802020080802010020000814e3,0x4a817c80003f5476a0001ebbd02800012a05f200004a817c80007aef40c8fa9884e955318b281dcd6501dcd68ba9b0b281dcddc35940773770d65077360b35943b9ad8e6b281dcd73e6b2877359407735a30fad17942667a0eb2807735941dcd68b9aca7735a2e6c1e06bf279,0x0,0x0,0x80400010000000802020080802000020000814e3,0xfa98007b66000fa9807981e7125b1187982d91e603cc7981e61e603d0494c1e60f30f7494c1e703885,0x400010000000802020080802000020000814e3,0x3d39803cde6003d39807980f47053b67e600799e603cde600799e603d1b2001e63cc04281301e64d3c5,0x80400010000000802020080802000020000814e3,0x10400410000000802020080802010020000814e3,0x400010000000802020080802000020000814e3,0x0,0x0,0x0,0x0,0x0,0x180428210222],
[0x180428210222,0x580428210a62,0x180428210222,0x2400090000000402010082002000020000814e3,0x280428210682,0x180428210222,0x280428210682,0x180428210222,0x480428210a62,0x480428210a62,0x480428210a62,0x0,0x0,0x0,0x0,0x0,0x445800111600016c871fd1542016c807980985980798798079bcc03d31faffcc00f33d39801e64dc35,0x400410000001002040081002000020000814e3,0x445800097e00025f86a68e14201e67a7300f37980798f300f33cc03d2a66cbcc01e67980799e68a8c5,0x401010000001002040081002000020000814e3,0x16c83cc1e600044580007981e60f31e607982d9003cc1e607a73003cc1e6003cfd39801e6001e614c6,0x0,0x1ed98002046000fa9872bebb280fa980798079f980798798079bcc03d32bca3cc0f303d39801e64dc35,0x400010000001002040081002000020000814e3,0xf379803cde6003d39876a91b283d3980798079f980798798079bcc03d36a703cc3cc03d39801e64dc35,0x7983cc1e6000079800000000000001e601e67980799e601e63cc03cc00003cc0000f300001e703d95,0x10400410000001002040081002010020000814e3,0x400010000001002040081002000020000814e3,0x0,0x0,0x0,0x0],
[0x0,0x180428210222,0x180428210222,0x580428210a62,0x180428210222,0x0,0x280428210682,0x180428210222,0x280428210682,0x180428210222,0x480428210a62,0x480428210a62,0x480428210a62,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_3809 : TreeBound (n := 4) 107 (programCode 0x422b071c55) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10808c120c481,0x1080884218481,0x10808c120c481,0x1080880208481,0x1080882208481,0x1080884218481,0x1080882208481,0x1080882208481,0x1080884218481,0x1080884218481,0x1080884218481,0x1080882208481,0x0,0x10088a8228481,0x1020888228481,0x10088a8228481,0xf307983cc222cf300f3001e9cc008247c01e8d91e603cc7981e61e603cc79801e7e600f6cde61e8e9885,0x10108c8228481,0x1020888228481,0x10108c8228481,0x80402000402090082020080802020020880816e3,0x1020888228481,0x1020888228481,0x1020888228481,0xf300f33cc03ccf30007983cc1e6079f9801e7e63cc07987981e61e603cc79803cde600f303cc1e703f45,0xf300f33cc03ccf300f3001e9cc008247c01ed1e9e601e67981e61e603cc79800f4e600f747661e8e9375,0xf303cc3cc03ccf300f35b2f307b660007983cc3528811bcc00f31e603cc3ced97a7379801e63cc1e7df6,0xf300f33cc0f30f301e6001ed9800833ac01f0ea9e601e67981e61e603cc79800f4e600f747661f44d375,0xf303cc3cc0f30f301e65b2f3081180007983cc3528811bcc00f379803cc3ced97a7379801e6f30799df6,0x0,0x80006000102080082080080102004020080814e3],
[0x80082002002080082080080402010020080814e3,0x8000a000202080082080080102004020080814e3,0x0,0x80012000402080082080080402010020080814e3,0xf30007d4c0010230003cc1e603cc7980798b64222c0f307982d91e603cc3cde600f379801e600f382dc6,0x80022000802080082080080402010020080814e3,0xf3000f6cc003db3000798c570798f3007983cc25f853887980f31e603cc3cdec2c7379801e601e68a8f6,0x80042001002080082080080402010020080814e3,0x80082002002080082080080402010020080814e3,0x80082002002080082080080402010020080814e3,0x80082000402080082080080402010020080814e3,0xf300f33cc03ccf300f3001e9cc008247c01e8d9f3003cfcc01e61e603cc79801e7e600f6cde61e8e9885,0xf303cc3cc03ccf300f362c7307b660007983cc25f881187980f31e603cc3cf163a7379801e63cc1e7df6,0xf301e63cc0f30f301e6001fcc8008706c01e8d9f3003cfcc01e6b6403ced9001f16400f6cde61f267885,0xf303cc3cc0f30f301e66a5f307d4c0007983cc25f881187980f31e603cc3cf52fa7379801e6798b65df6,0x0,0x10088a8228481,0x1020888228481,0x10088a8228481,0x0,0x10108c8228481,0x1020888228481,0x10108c8228481,0x0,0x1020888228481,0x1020888228481,0x1020888228481,0xf301e63cc0798f30981cc1ed9800833ac01f0ea9e601e7e601e63cc03ccf3000f6cc00f7c0e61eacf375,0xf300f33cc03ccf300f3001e9cc008247c01ed1e9e601e7e601e63cc03ccf3000f6cc00f7c0e61e8e9375,0x0,0xf300f33cc0f30f301e6001f530008520c01f8829e601e7e601e63cc03ccf3000f6cc00f7c0e61f44d375,0x0],
[0x0,0x80006000102080082080080082002020080814e3,0x80082002002080082080080082002020080814e3,0x8000a000202080082080080002000020080814e3,0x0,0x80012000402080082080080002000020080814e3,0xf3000f6cc0010230003cca71079879807983cc25f862b9e600f33cc03cc3cdeb397379801e600f382f76,0x0,0xf3000f6cc003db300079879803cde600798b6425f83cc1e602d93cc03cc3cde600f379801e603d3b8246,0x80042001002080082080080082002020080814e3,0x80082002002080082080080082002020080814e3,0x80082002002080082080080082002020080814e3,0x80002000402080082080080002000020080814e3,0x0,0xf303cc3cc03ccf300f35b2f307b660007983cc25f88119e600f33cc03cc3ced97a7379801e63cc1e7df6,0x0,0xf303cc3cc0f30f301e65b2f3081180007983cc25f88119e600f33cc03cc3ced97a7379801e6f30799df6]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_3890 : TreeBound (n := 4) 107 (programCode 0x422b071c56) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10818c121c481,0x1081084210481,0x10818c121c481,0x1081084210481,0x1081082210481,0x1081084210481,0x1081082210481,0x1081084210481,0x1081084210481,0x1081084210481,0x1081084210481,0x1081084210481,0x0,0x1009ce823c481,0x1021088210481,0x1009ce823c481,0x0,0x10118c8238481,0x1021088210481,0x10118c8238481,0x80402000000000002020080802000020000814e3,0x1021088210481,0x1021088210481,0x1021088210481,0x1021088210481,0x0,0x0,0x0,0x0,0x0,0xc004b0002004080120100802010094402512e4],
[0xc00030002004080120100802010004400512e4,0x0,0x1400050002004080120100802010008400613e4,0xf307983cc1e60004458001e601e7e601e61e60204603cde603cc1e603cc1e60079f9f99e7e603cc9d016,0x2400090002004080120100802010010400412e4,0x2400090002004080120100802010010400412e4,0x0,0x10400090002004080120100802010010400412e4,0x840021000200408012010080201004040141ae4,0x20400410002004080120100802010080402412e4,0x10400410002004080120100802010080402412e4,0x0,0x0,0x0,0x0,0x0,0x1009ce823c481,0x1021088210481,0x1009ce823c481,0x80002008000000002040081002000020000814e3,0x10118c8238481,0x1021088210481,0x10118c8238481,0x0,0x1021088210481,0x1021088210481,0x1021088210481,0x1021088210481,0x0,0x0,0x0,0x0],
[0x0,0xc004b0002004080140201002010004400512e4,0xc00030002004080140201002010004400512e4,0x2401010002004080140201002010010400412e4,0x1400050002004080140201002010008400613e4,0x0,0x2400090002004080140201002010010400412e4,0x400090002004080140201002010000400412e4,0x0,0x10400490002004080140201002010080402412e4,0x840021000200408014020100201004040141ae4,0x0,0x10400410002004080140201002010080402412e4,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_3971 : TreeBound (n := 4) 107 (programCode 0x422b071c57) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10808c120c481,0x1080884218481,0x10808c120c481,0x1080880208481,0x1080882208481,0x1080884218481,0x1080882208481,0x1080882208481,0x1080884218481,0x1080884218481,0x1080884218481,0x1080882208481,0x0,0x10088a8228481,0x1020888228481,0x10088a8228481,0xf307983cc222cf300f3003cfcc01ef41403ced91e603cc7981e61e603cc79801e7e600f6d7641e8e9885,0x10108c8228481,0x1020888228481,0x10108c8228481,0x804020008040a0102020080802020020900814e3,0x1020888228481,0x1020888228481,0x1020888228481,0x0,0xf300f33cc03ccf300f3001e9cc01ef5fa03d31e9e601e67981e61e603cc79800f4e600f752ca1e8e9375,0x0,0xf300f33cc0f30f301e6001ed9801f052a03d6ea9e601e67981e61e603cc79800f4e600f752ca1f44d375,0x0,0x0,0x180428210222],
[0x180428210222,0x80028210022,0x180428210222,0x2400090004080102010082002010020100814e3,0x2400090002004080120100802010010400412e4,0x80028210022,0x0,0x80028210022,0x481028210862,0x481028210862,0x481028210862,0x0,0x0,0x0,0x0,0x0,0x10088a8228481,0x1020888228481,0x10088a8228481,0x0,0x10108c8228481,0x1020888228481,0x10108c8228481,0x0,0x1020888228481,0x1020888228481,0x1020888228481,0xf301e63cc0f30f307aec83d39801f21a403ced93cc03cde601e63cc03ccf3001ed9800f6d7641f267885,0xf300f33cc03ccf300f3001e9cc01ef5fa03d31e9e601e7e601e63cc03cc79800fa9800f7cc4a1e8e9375,0x0,0xf300f33cc0f30f301e6001e9cc01f238a03d6ea9e601e7e601e63cc03cc79800fa9800f7cc4a1f44d375,0x0],
[0x0,0x180428210222,0x180428210222,0x80028210022,0x180428210222,0x0,0x2400090002004080140201002010010400412e4,0x80028210022,0x0,0x80028210022,0x481028210862,0x481028210862,0x481028210862,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_4052 : TreeBound (n := 4) 107 (programCode 0x422b071c58) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1080081200481,0x1080084200481,0x1080081200481,0x1080080200481,0x1080882208481,0x1080084200481,0x1080882208481,0x1080080200481,0x1080084200481,0x1080084200481,0x1080084200481,0x1080080200481,0x0,0x120000000180000001200000001800000006000000010100000040040000101001000004001000040010000040010000100000040041400000400000400400001001000885b1a7,0x481088210481,0x16c800111600025f800079800026073007cd29e601e67981e61e603cc00000f30000f745f99e703375,0x0,0x0,0x80400010000000002020080802000020000814e3,0x0,0x80088200481,0x481088210481,0x481088210481,0x481088210481,0x80088200481,0x0,0x0,0x0,0x0,0x0,0x0],
[0xf30000b6400088b000079bcc01e6f301e63cc0204603cde60f301e603cc1e7e60079f9801e601eda8856,0x0,0x0,0xf300003cc00088b0001e63cc01e6f301e63cc0204603cde60f301e603cc1e7e60079f9801e601eda8856,0x0,0x0,0xf30007d4c003db30007983cc03cde600f33cc0222c1e60f3097e1e603cc1e7e600f379f99e603cfebd66,0x0,0xf3001e9cc01e6f3001e603cc01e6f301e63cc0204603cde60f301e603cc1e7e60079f9801e601ede5456,0x0,0x0,0x0,0xf301e63cc0798f300f3003cc03cde600f33cc0222c1e60f3097e1e603cc1e7e600f379f99e603cfebd66,0x0,0xf301e63cc0f30f301e6003cc03cde600f33cc0222c1e60f3097e1e603cc1e7e600f379f99e603d783d66,0x0,0x0,0x481088210481,0x25f800111600025f8000798000446ec816f593cc03cde601e63cc03cc00001e60000f9a66c9e703885,0x401010000000002040081002000020000814e3,0x0,0x0,0x0,0x80088200481,0x481088210481,0x481088210481,0x481088210481,0x80088200481,0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0xf3000f6cc2dcdb303cc0079803cde600f33cc025f83cc1e611163cc03cc3cde600f37a731e603d3b8276,0x0,0xf300003cc0004bf0000f379803cde600f33cc025f83cc1e611163cc03cc3cde600f37a731e603d3b8276,0x0,0x0,0xf30007d4c003db30007983cc03cde600f33cc0222c1e61e611163cc03cc1e7e600f379f99e603cfebd66,0xf303cc3cc2fb3b3000f3079803cde600f33cc025f83cc1e611163cc03cc3cde600f37a731e603d3b8276,0xf3001e9cc01e6f3001e603cc01e6f301e63cc0222c03ccf307983cc03cc1e7e60079f9801e601eacf856,0xf303cc3cc1116f3003cc079803cde600f33cc025f83cc1e611163cc03cc3cde600f37a731e603d3b8276,0x0,0x0,0xf301e63cc0798f300f3003cc03cde600f33cc0222c1e61e611163cc03cc1e7e600f379f99e603cfebd66,0x0,0xf301e63cc0f30f301e6003cc03cde600f33cc0222c1e61e611163cc03cc1e7e600f379f99e603d783d66]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_4133 : TreeBound (n := 4) 107 (programCode 0x422b071c59) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1081090210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_4134 : TreeBound (n := 4) 107 (programCode 0x422b071c5a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1081090210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_4135 : TreeBound (n := 4) 107 (programCode 0x422b071c5b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1081090210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_4136 : TreeBound (n := 4) 107 (programCode 0x422b071c5c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1080090200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_4137 : TreeBound (n := 4) 107 (programCode 0x422b071c5d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x16c80005b200016c8079801e7e679f9f98371d3001e9cc01e6f3003cc003ccf300f3f745bcde703375,0x7983cc1e600f379807980001e679807981e6f30079bcc01e6f3003cc3cc03ccf300f745801e703d95,0x445800111600025f8079803cde679807981e6f30079bcc01e6f3003cc0079bcc01e6f745801e722395,0x0,0x11176c8445db200016c8079801e7e679f9f982d9000f6cc003ea6000f6cc003cde600f3f745bcde703885,0x0,0x44583cd1160004458079803cde67a737981e6003d39800f4e6001e9cc00f33cc03ccf746731e722395,0x400020000000080000000200000000800020002100080000100100020000100000804000010000000040000000020000000100700000101000000400000000201000001000487fca7,0x0,0x0,0x1ed983d3b66001ed9807981e61e679807981e601e67980799e600f33cc07983cc1e60f745801e703d95,0x7983cc1e6000079807980001e679807982d900003cc0001e61e603cc00001e60000f745801e703885,0x1e67983db4e6003d39807981e61e679807981e603cc7980f31e603cc3cc0f303cc3cc0f745801e703d95,0x0,0x1e6798408de600f379807980001e679807981e60f307983cc1e607983cc3cc03ccf300f745801e703d95,0x7983cc1e6000079807980001e679807982d900003cc0001e711603cc00001e60000f745801e703885,0x0,0xf307983cc1e600007981e62139798798079807a730079800007a73003d1b2003cc00004105801e64dc35,0x0,0xf307983cc1e600007981e62139798798079807a730079800007a73003d1b2003cc00004105801e64dc35,0x0,0x20a0b0228481,0x222090228481,0x20a0b0228481,0x0,0x1000080001000080010000800010000810002002010000100100000420100001804000002010000040040000020100000100000400021400000400004000205010001000cc4b0a7,0x2400082020080802080082002002020800814e3,0x1000020001000400010000200010001010002010010000100100000540100001804000002010000040040000020100000100000400021400000400004000205010001000e84b0a7,0x2400084020180802080082002002020880834e3,0x222090228481,0x222090228481],
[0x222090228481,0xb52cc00eff380b47847c74e8f08f99b7deb897639c2d1e11f1e48f08f99b7847ccdbc23eee3847c8a0f08f99b8ed6d030f247847c7923c2f2b207d27f84d6b0585be3c7923c26b57d1f1ce5a3c24981447c7923c24981447ccdbc23e4507847c7923c3a72a4f8e75a3c29875e3e39c5a3c3a72a4f8e75a3c29875e3e39c5a3c3a72a4f8e7168f0e9ca93e39c5a3c3a72a4f8e705a3c7e1fbfe39c02d1e11f1d947847f4563f0fdff1ce2d1e11f1d947847f45611f1fb1e11fd15847c7ec7847f456c66a15c73802d1ec9f28f05df5c063d,0x242190228501,0x222090228481,0x242190228501,0x0,0x0,0x202001800808000001000008001000024280000100000000400800000800000000c000214010000040040000000100000100020021400080000000200200000200010000817ffa8,0x80080402020080802080082002010020800814e3,0x0,0x0,0x202001800800000001020000001000024280000110000000400800000800000000c000214010000040040000000100000100020021400080000000200200000200010000817ffa8,0x80400000020000802080082002000020800814e3,0x1e84664051d4d8594000ee6ee1aca1dd4d8594003b9b0611ff97bd664cdd08cc8f4eb29dcda09aca01dcda09aca1e090383aca773770d6503b9b41359401dcf41d6503b9b4135940773770d6500774218cc2214735cf9aca03c15b940a07735d011ffa2e6ee1aca00ee6ee95aabf59,0x80400804020100802080082002020020800834e3,0x800406010200c080208008200201802080081ce3,0x80000000020000802080082002000020800814e3,0x80080402020080802080082002010020800814e3,0x80100804020100802080082002020020800834e3,0x80100804020100802080082002020020800834e3,0x0,0x620010000800040004000040008000100020003100080000100100010000100001004000010010000040040000040100000100720000101880000402000000404000001020887fda7,0x0,0x8118007b66000fa9807981e61e6811879835373001e9cc01e6f3003cc03cc0f30f30f7494c1e703375,0x0,0x80004800120004802080082002020020800814e3,0x80080802020080802080082002020020800814e3,0x80008800220008802080082002020020800815e3,0x0,0x4000000804000000840000008040000008100020000100001001000000201000010040000040100000400400000401000001001000000410000004010000004040000010008c5b1a7,0x80400800020000802080082002020020800814e3,0xf30007d4c003cde60079f9801e7e679f9f982d9f3003cfcc01e6f3003cc79801e7e600f745801e703885],
[0x80400804020100802080082002020020800834e3,0x8004080102004080208008200202002080081ce3,0x80000800020000802080082002020020800814e3,0x80080802020080802080082002020020800814e3,0x80100804020100802080082002020020800834e3,0x80100804020100802080082002020020800834e3,0x1e9cc007a73000f3f35f6580798f301ed98002d90bececc001f53003cc3cefb2cf379801e601e611156,0xf301e63cc0f301e61e607987981e697e07982d9f3003cfcc01e6f3003cc79801e7e600f745801f267885,0x0,0x3d39800f4e6003d39807981e61e679807981e6f30079bcc01e6f3003cc0f303cc3cc0f745801e703d95,0x3d39803cde6003d3983cc0001e60f3222c0002d9003cfcc1f53f3003cc1e7e61ed9f9801e6001e61556,0x0,0x40a0b0230481,0x422090230481,0x40a0b0230481,0x0,0x42002001008000000000020000020000024002000110000000400010000800000000c000210010000040040000000100000100020020010080000000200200000200000200017ffa8,0x10400400020000802080082002010020800814e3,0x42002001008000000000020000020000024002000110000000400010000800000000c000210010000040040000000100000100020020010080000000200200000200000200017ffa8,0x10400404020100802080082002010020c00834e3,0x422090230481,0x422090230481,0x422090230481,0x462190230501,0x442190230501,0x422090230481,0x442190230501,0x462190230501,0x0,0x80a0b0220481,0x822090220481,0x80a0b0220481],
[0x0,0x2002001008000000020020000020000024002000110000000400010000800000000c000210010000040040000000100000100020020010080000000200200000200000200017ffa8,0x20400800020000802080082002020020800814e3,0x2002001008000000020020000020000024002000110000000400010000800000000c000210010000040040000000100000100020020010080000000200200000200000200017ffa8,0x20400804020100802080082002020020800834e3,0x822090220481,0x822090220481,0x822090220481,0x842190220501,0x842190220501,0x802090220481,0x842190220501,0x842190220501,0x0,0x80a0b0220481,0x822090220481,0x80a0b0220481,0x0,0x1000000801000000810000008010000008100020000100001001000000201000010040000040100000400400000401000001000400000410000004004000004040000010008c5b1a7,0x20400800020000802080082002020020800814e3,0x1e6003d39803cde60079f9801e7e679f9f98371d3001e9cc01e6f3003cc79800f4e600f745801e703375,0x20400804020100802080082002020020800834e3,0x822090220481,0x822090220481,0x822090220481,0x842190220501,0x842190220501,0x802090220481,0x842190220501,0x842190220501,0x0,0x14804100120084802080082002004020800814e3],
[0x422090230481,0x15008100220088802080082002004020900815e3,0x0,0x20002001080000000100020000100000024002000110000000400010000800000000c000210010000040040000000100000100020020010080000000200200000200000200017ffa8,0x0,0xf300003ccf30079f980001e679f9f981e6f30079bcc01e6f3003cc3cc03ccf300f745801e703d95,0x79800f4e6003cde6007d90580798f301e600002d90820ecc0000f3003cc3ce082cf379801e601e611156,0x422090230481,0x422090230481,0x422090230481,0x842190220501,0x842190220501,0x2090220481,0x842190220501,0x2090220481,0x0,0x80a0b0220481,0x822090220481,0x80a0b0220481,0x1008000001000000010080000010000000030000000080004000900000000c00000401000001004000200010000010002002000002008000020020000020000008000713a8,0x0,0x0,0x79800f4e6003cfcc0079f9803cde679f9f981e6f30079bcc01e6f3003ccf3003cfcc00f745801e722395,0x0,0x822090220481,0x822090220481,0x822090220481,0x842190220501,0x842190220501,0x802090220481,0x842190220501,0x842190220501],
[0x0,0x80a0b0220481,0x822090220481,0x80a0b0220481,0x0,0x0,0x0,0x0,0x0,0x822090220481,0x822090220481,0x822090220481,0x42190220501,0x42190220501,0x2090220481,0x42190220501,0x2090220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_4314 : TreeBound (n := 4) 107 (programCode 0x422b071c5e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x40000000300000000c0000000300000000c00020001000000104000200400020060000004100000010400000040800000101004000001010000004000004008100010010010873227,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x40000000300000000c0000000300000000c00020001000000004000200000020060040000100100000400010000801000001004000001010000004001000008100000010010873227,0x40000000300000000c0000000300000000c00020001000000004000200000020060002000100008000400010000800020001004000001010000004001000008100000010010873227,0xf300003cc00088b079807980025f8001ed98001ed983cc1e7e6007983cc1e7e60079bcc01e6f30799556,0x40000000300000000c0000000300000000c0002000100000000c000200000020060004000100010000400040000800100001004000001010000004004000008100000010010873227,0x0,0x40000000300000000c0000000300000000c0002000100000000c000200000020060020000100080000400100000800200001004000001010000004010000008100000010010873227,0x0,0xf30000b6400088b000081180025f8001ed98002d9003cfcc1e60f3003cc1e7e60079f9801e6f30799556,0x0,0x40000001100000004400000009000000014000200010000001040002004000c0060000004100000010400000040800000101004000001010000004000004008100010010010873227,0xf303cc3cc0f30f3079807980025f8001ed98001e60f6cc011160000f6cc1e7e6007983cc1e6f30799556,0x0,0xf303cc3cc0f30f3079807980025f8001ed98001e61e9cc0097e0001e9cc1e7e6007983cc1e6f30799556,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xf300012fc00088b0001023000408c000fa98001ed9f9801e804603cc3cc1e67980f3a7101e67983d1426,0x4000000010000820040002080100000400400000001040082004000208000000040001000080004000200020001000020001004000000810400002000000010100000010020866ba7,0xf300012fc00088b0001023000408c000fa98001ed9f9803ce04607983cc1e67980f397e01e67983d1426,0x0,0x0,0x4000000010000a000400028001000040004000000014000a2004000208000000040010000080040000200200001000200001004000000814000002000000010100000010020866ba7,0x0,0x0,0x400200001000800004002000010008000820000002002000008208000200060040000100100000400400000801000001004000001010000004000080008100200010010873227,0x411090210481,0x0,0x0,0x211090210481,0x0,0x211090210481,0xf307983ea6000f301ed980025f8001ed98002d9003cfcc001f53003cc1e7e60079f9801e6f307a8856,0x411090210481,0x411090210481],
[0x411090210481,0x411090210481,0x62023101100000000400020000000000022000000101000000090000000810000000c000310110000010040000000100000100020031010020000000200200000200200010007d3a8,0x411090210481,0x62002001100000002500020000020000022000000101000000090000000810000000c000310010000010040000040100000100020031000020020000200200000200200010017d3a8,0x0,0x0,0x0,0x810020420004800180006002010400406032e4,0x0,0x101004042000480018000a002010400406032e4,0x40000002002000008400000080000400080400000021000000090000000810000000c00000401000001004000000090000010000802000002000100020020000020020001085513a8,0x0,0x80010800420004800180102002010400404032e4,0x0,0x2010800420004800180102002010400404032e4,0x8010200420004800180042002010400404032e4,0x10010400420004800180082002010400404032e4,0x10010400420004800180082002010400404032e4,0x32810400420004800180082002010400404032e4,0x20010800420004800180102002010400404032e4,0x0,0x4001100042000480018020200201040040c072e4,0x0,0x401000001004000004008000010010000820000002002000008208000c00060040000100100000400400000801000001004000001010000004000080008100200010010873227,0x411090210481,0x0,0x140004602000480018000a002010400406030e4,0x211090210481,0x0,0x211090210481,0x0],
[0x411090210481,0x411090210481,0x411090210481,0x411090210481,0x400001001000004004000008010000010000820000002002000008208000c00060040000100100000400400000801000001004000001010000004000080008100200010010873227,0x411090210481,0x0,0x0,0x0,0x0,0x820020820004800180006002010400406034e4,0x0,0x0,0x40000004002000010400000100000400100400000021000000090000000810000000c00000401000001004000000090000010000802000002000100020020000020020001089513a8,0x0,0x80020800820004800180102002010400404024e4,0xf307987983cc0f307a73000408c000fa98002d9000f6cc024213003cc1e7e600f397e01e67983ebd66,0x4020800820004800180102002010400404024e4,0x802020082000480018004200201040040402ce4,0x10020400820004800180082002010400404034e4,0x10020400820004800180082002010400404034e4,0x20000820004800180002002010400404024e4,0x20020800820004800180102002010400404024e4,0x0,0x4002100082000480018020200201040040c064e4,0x0,0x402000001008000004020000010080000820000002002000008208000c00060040000100100000400400000801000001004000001010000004000080008100200010010873227,0x421090210481,0x0,0x118004602000480018000a002010400406030e4,0x221090210481,0x0],
[0x221090210481,0x0,0x421090210481,0x421090210481,0x421090210481,0x421090210481,0x821090210481,0x421090210481,0x821090210481,0x421090210481,0xf3001e9cc01e6f3001e67980025f8001ed98002d9003cfcc1e60f3003cc1e7e60079f9801e6f307d6156,0x0,0x42022101100000100000100400020001002000000101000000090000000810000000c000210110000010040000040100000100020031000020020000200200000200200010817d3a8,0x421090210481,0x0,0x100804202000480018000a002010400406030e4,0x221090210481,0x0,0x221090210481,0x0,0x421090210481,0x421090210481,0x421090210481,0x421090210481,0x821090210481,0x421090210481,0x821090210481,0x421090210481,0x0,0x42020100100000100000101000020001002000000101000000090000000810000000c000210110000010040000040100000100020031000020020000200200000200200010817d3a8,0x421090210481,0x0],
[0x108004202000480018000a002010400406030e4,0x221090210481,0x0,0x221090210481,0x0,0x421090210481,0x421090210481,0x421090210481,0x90200481,0x800090200481,0x90200481,0x800090200481,0x90200481,0x0,0x17bf89fc502c800000001e60007d4c000fa98002d90be095c01e6f3003cc3cef7da73b6401e67983cde26,0xc43190230501,0x0,0x0,0x243190238501,0x0,0x243190238501,0xf307983cc1e60f3079f980025f8001ed98002d9003cfcc001f53003cc1e7e60079f9801e6f307a8856,0x443190230501,0xc43190230501,0x443190230501,0x842190220501,0x842190220501,0x842190220501,0x842190220501,0x42190220501,0x8020200404000880018048200201060040804104,0x0],
[0x17bf89fc502c800000001e60007d4c000fa98002d90be095c01e6f3003cc3cef7da73b6401e67983cde26,0xc43190230501,0x0,0x222c0007a73002269ba980025f8001ed98002d9003cfcc0004bf003cc1e60f3079f9801e6f30799556,0x243190238501,0x0,0x243190238501,0x0,0x443190230501,0xc43190230501,0x443190230501,0x842190220501,0x842190220501,0x842190220501,0x842190220501,0x42190220501,0x8020200804000880018048200201060040804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_4523 : TreeBound (n := 4) 107 (programCode 0x422b071c5f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x16c80005b200016c8079801ed9879fa730371d3001e9cc01e6f3003cc003ccf300f3fa1ebcde703375,0x0,0x43ab000100220000401010000804000000a00021d58200001101000008082000020040000100100000100400000801000001007bab00100222000100101000802000001001897dea7,0x422090230481,0x10cfc21e82a583d39801116219fc0c0455a300f3f30079bcc00f3f3003d30cf0bcc8a967a73001e68c725,0x410040001002080082002000021000814e3,0xee6d04d6500791be733a7f7359b73595dce17d05e01e08ffca00000ee6b283b9ad8e6b64ca66ec259400ee729b59565a298d6503b9b4135940ee6d04d6500ee729b5940773770d65007735940000077360b35941dd9a664969fdcd66dcd65eea6c2ca000ee765cb36c079,0x0,0x10ca10f3222c1e679807b6621945cc04467300f3f30079bcc00f3f3003d30b843cc88b07a73001e68a8c5,0x0,0x422090230481,0x422090230481,0x422090230481,0xc62190230501,0xc42190230501,0x422090230481,0xc42190230501,0xc62190230501,0x25f800111600025f80f3001ed987a73f302d9f3003cfcc01e6f3003cc00799e603ccf9a5001e703885,0x20001000080000000200010000800008000000040008300200020000200004004000004010000020040000100100000100000000041c000002000000010020000010020852ba7,0x0,0x20a0b0228481,0x222090228481,0x20a0b0228481,0x0,0x0,0x0,0x0,0x0,0x222090228481,0x222090228481],
[0x222090228481,0x0,0x242190228501,0x222090228481,0x242190228501,0x0,0x0,0xfa98003ea610e8e9807981e679886caf30352800f4e6003ea6000f6cc03cc0f30f30fa8c9c1e703375,0x10d9b9800f4e60f307981e621b29e67980f3007a8d9479bcc007983cc3d388d03cc3cc0417f001e64dc35,0x1ed98007b6610237981e601e67987980f301e6003d39800f4e6001e9cc07983cc1e60f8b2001e703d95,0x2000106008000000020001000080000800000004000830020002000020000400000000401c600020000000100000000100000000041c600002000000010020000010020852ba7,0x0,0x0,0x3d39803cde610d9b98079800079886caf3035280799e60799e600f33cc0f300f3f300fa88d01e703375,0x0,0xf379803cde60f307981e600007987980f301e603cc7980f31e603cc3cc3cc03ccf300f8b2001e703d95,0x8118007b6600081183cc0001e9cc0222c0001e9cc3cc3cde6003cc3cc1e7e60079f9801e607983e156,0x0,0x0,0x0,0x0,0x0,0x0,0x1ed98007b66000fa981e601e67987980f301e6f30079bcc01e6f3003cc07983cc1e60f8b2001e703d95,0x0,0x0,0x0,0x7980001e61c7a79807980007987980f30352800f4e600f4e6001e9cc00000f30000fa1e801e703375,0x20001f0008000000020000a00080000400000004000828020002000020000500000000201f0000200280001000a0000100000000021f0000020000000100b0000010020842ba7,0x0,0x0,0x1ed98007b6607987981e601e67987980f301e601e67980799e600f33cc07983cc1e60f8b2001e703d95],
[0x7980001e60b647980f300007987980f302d900003cc0001e6b6403cc00001e60000f9a5001e703885,0x0,0xfa98003ea6000fa983cc0001f5300222c0001e9cc3cc3cde6003cc3cc1e7e60079f9801e61e60f4556,0x0,0x2000160008000000020000800080000800000004000830020002000020000400000000401e000020000000100020000100000000041e000002000000010020000010020852ba7,0x0,0x0,0x7980001e60d4a79807980007987980f303529e601e7e601e63cc03cc00000f30000fa1e801e703375,0x0,0x3d39800f4e6003d3981e601e67987980f301e6f30079bcc01e6f3003cc0f303cc3cc0f8b2001e703d95,0x0,0xf307983cc2f49630811801ed98874c0b0371d3001e9cc01e6f3003cc003ccf300f3fa8cd8de703375,0x422090230481,0x1e60f30f308a4fc21023001ed987b1b0302d9f3003cfcc01e6f3003cc00799e603ccf9a66c9e703885,0x10040001002080082002000021000814e3,0x0,0x0,0x1e60f307983dc23007b6601e67987a73f301e6f30079bcc01e6f3003cc07983cc1e60f8b2001e703d95,0x0,0x422090230481,0x422090230481,0x422090230481,0xc62190230501,0xc42190230501,0x422090230481,0xc42190230501,0xc62190230501,0x3d39803cde60079f9807980007987980f3035373001e9cc01e6f3003cc0f300f3f300fa3ce01e703375,0x7980001e61c7a79807980007987980f3035373001e9cc01e6f3003cc00000f30000fa1e801e703375,0x0,0x80a0b0220481,0x822090220481],
[0x80a0b0220481,0x0,0x0,0x1e601e7e61e601e67980f300f31e67980f3007a73003cfcc007a73003cfcc001ed98003e2c801e64d3c5,0x1e6003d39803cde60079f9801ed987b2a330371d3001e9cc01e6f3003cc79800f4e600fa1e801e703375,0x0,0x822090220481,0x822090220481,0x822090220481,0x842190220501,0x842190220501,0x802090220481,0x842190220501,0x842190220501,0x0,0x7d4c001e6f300811800079807a08b035373001e9cc01e6f3003cc00000f3f300f6564c1e703375,0x422090230481,0x1e9cc00799e6011160000798001f5301e6f30079bcc01e6f3003cc00003ccf300f4e6001e703d95,0x0,0xee6d04d6500791be733a7f7359b73595dcd73e6b281e08ffca00000ee6b283b9ad8e6b64ca66ec259400ee729b59565a298d6503b9b4135940ee6d04d6500ee729b5940773770d65007735940000077360b35941dd9a664969fdcd66dcd65eea6c2ca000ee765cb36c079,0x0,0xf300003ccf3007b6600007987a73f301e6f30079bcc01e6f3003cc00003cc0000f8b2001e703d95,0x0,0x422090230481,0x422090230481,0x422090230481,0x842190220501,0x842190220501,0x2090220481,0x842190220501,0x2090220481,0x0],
[0x80a0b0220481,0x822090220481,0x80a0b0220481,0x40201010040201002080082002040021000854e3,0x0,0x0,0x3cc007b66003cfcc007a73001ed987aed7302d9f3003cfcc01e6f3003ccf3001ed9800f9a5001e703885,0x0,0x822090220481,0x822090220481,0x822090220481,0x842190220501,0x842190220501,0x802090220481,0x842190220501,0x842190220501,0x0,0x80a0b0220481,0x822090220481,0x80a0b0220481,0x0,0x0,0x0,0x0,0x200010000f000000020000000040000800000004000f700200020000200004004000004010000020040000100100000100000000041e00000200000001002000001002085aba7,0x822090220481,0x822090220481,0x822090220481,0x42190220501,0x42190220501,0x2090220481,0x42190220501],
[0x2090220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_4684 : TreeBound (n := 4) 107 (programCode 0x422b071c60) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x108090200481,0x408090200481,0x108090200481,0x100405014000500018000a00201040040a050e4,0x0,0x0,0x0,0x0,0x408090200481,0x408090200481,0x408090200481,0x8090200481,0x80a0b0220481,0x1e67981e60007b66001f53000222c001f530002d9003cfcc0f30f3003cc1e63cc079f9801e67985b7216,0x80a0b0220481,0x8090200481,0x0,0x120090200481,0x420090200481,0x120090200481,0x100404014000500018000a00201040040a050e4,0x0,0x0,0x0,0x0,0x420090200481,0x420090200481,0x420090200481,0x20090200481,0x822090220481],
[0x420090200481,0x822090220481,0x20090200481,0xf303cc3cc2d90f307981e600044580010230002d907983cc2046f3003cc3cde600f3b6401e6f30799c76,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xf3000222c00088b000111600044580010230001ed9f9801e804603cc3cc3ccf300f3d4a01e6f3079d936,0x0,0xf3000222c00088b000111600044580010230001f5379803ce04607983cc3ccf300f3b6401e6f3079d936,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4000000210000000840000002100000008400020001000000004000200000002060000020100000080400000100800000201004000001010000004000000008100000010010873227,0x0,0x0,0x0,0x0,0x0,0xf30bdfa2c0000f300020460007d4c001f53000361f4d18001e603cc03cc3cef76079f9801e67983cddc6,0xf307983cc0002d90001f53000222c001f530001e9cc3cc3cde6003cc3cc1e7e600799e601e67983cd556],
[0x0,0x0,0x0,0x0,0x0,0xf300003cc1e64bf00010230004458001023000222c7981e620463cc03cc1e7e600f397e01e6f30799766,0x0,0x8120a044000500018000600201040040a052e4,0x81002044000500018000600201040040a052e4,0x40013000440005000180202002010400408052e4,0x101004044000500018000a00201040040a052e4,0x0,0x0,0x0,0x0,0x0,0x8010200440005000180042002010400408052e4,0x10400440005000180002002010400408052e4,0x10010400440005000180082002010400408052e4,0x72a64010042000008000040020020000082000000108000000090000000220000000c000395330000210040000000300000100020039532080080000100200000200210010847f228,0x2001080044000500018010200201040040c072e4,0x0,0x40011000440005000180202002010400408052e4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0],
[0x0,0xf303cc3cc3528f303cc0f300044580010230001ed9f9801e804603cc3cc1e6f300f3d4a01e6f30799766,0x0,0xf303cc3cc2d90f303cc1e600044580010230001f5379803ce04607983cc3ccf300f3b6401e6f30799c76,0x0,0x0,0x0,0x0,0x0,0x82212084000500018000600201040040a054e4,0x82002084000500018000600201040040a054e4,0x40023000840005000180202002010400408044e4,0x0,0x0,0x0,0x0,0x1e60f307983cc0f307b6600044580010230002d9000f6cc0223b3003cc3cde600f3b6401e6f307b8276,0x1e60f8b9983d398007b6600044580010230002d9000f6cc2fb3b3003cc3cde600f3b7331e6f307b8276,0x802020084000500018004200201040040804ce4,0x20400840005000180002002010400408044e4,0x10020400840005000180082002010400408054e4,0x20000840005000180002002010400408044e4,0x2002080084000500018010200201040040c064e4,0x0,0x40021000840005000180202002010400408044e4,0xf300003cc25f8f303cc0f300044580010230002d907983cc2046f3003cc1e7e600f397e01e6f30799766,0xf3001e9cc01e6f3001e6f3000222c001f530002d9003cfcc1e60f3003cc1e7e60079f9801e67984c0556,0x0,0x120090200481,0x420090200481,0x120090200481,0x0],
[0x0,0x0,0x0,0x1e60f3079a22c0f33cde600044580010230002d9000f6cc0223b3003cc3cde600f3b6401e6f307b8276,0x420090200481,0x420090200481,0x420090200481,0x20090200481,0x822090220481,0x420090200481,0x822090220481,0x20090200481,0x0,0x100090200481,0x400090200481,0x100090200481,0x108004204000500018000a00201040040a050e4,0x0,0x0,0x0,0x0,0x400090200481,0x400090200481,0x400090200481,0x90200481,0x842190220501,0x90200481,0x842190220501,0x90200481,0x0,0x900024000000022080082002000020000814e3,0x441090210481],
[0x1100044000000042080082002000020000814e3,0x0,0x0,0x0,0x0,0x1e60f307c7b68cf3001e600044580010230002d9000f6cc0223b3003cc3cde600f3b6401e6f307b8276,0x441090210481,0x441090210481,0x441090210481,0x40090200481,0x842190220501,0x842190220501,0x842190220501,0x40090200481,0x8020200404000900018048200201060040804104,0x0,0xa00028000000022080082002000020000814e3,0x441090210481,0x1200048000000042080082002000020000814e3,0x108004a24000500018000a00201040040a050e4,0x0,0x0,0x0,0x0,0x441090210481,0x441090210481,0x441090210481,0x40090200481,0x842190220501,0x842190220501,0x842190220501,0x40090200481],
[0x8020200804000900018048200201060040804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_3724 : TreeBound (n := 4) 107 (programCode 0x422b071c) := by
  conv in programCode _ => reduce
  exact branchFour (k := (2,1)) (by decide +kernel) part100_3725 part100_3726 part100_3727 part100_3728 part100_3809 part100_3890 part100_3971 part100_4052 part100_4133 part100_4134 part100_4135 part100_4136 part100_4137 part100_4314 part100_4523 part100_4684

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_4878 : TreeBound (n := 4) 107 (programCode 0x422b071d61) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x100c0b0220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_4879 : TreeBound (n := 4) 107 (programCode 0x422b071d62) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1024090220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_4880 : TreeBound (n := 4) 107 (programCode 0x422b071d63) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x100c0b0220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_4881 : TreeBound (n := 4) 107 (programCode 0x422b071d64) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x80402000180006002000880022020020800814e3,0x80402000080002002000080402020020800814e3,0x8040200028000a002001080042020020800815e3,0x0,0x10c0a1220481,0x424084220481,0x10c0a1220481,0x4080220481,0x2140c2220481,0x424084220481,0x2140c2220481,0x0,0x424084220481,0x80000000080002002000080002020020800814e3,0x424084220481,0x0,0x844188220501,0x4080220481,0x844188220501,0x4080220481,0x80402000480012002002080082020020800816e3,0x80402000080002002000080002020020800814e3,0x80402000880022002004080102020020800814e3,0x0,0x0,0x80402000000000402000080002020020800814e3,0x0,0x0,0x80402000402010082002080082020020800816e3,0x80402000000000002000080002020020800814e3,0x80402000004000102000080102020020800814e3],
[0x80402000000000002000080002020020800814e3,0x8040200100804020200808020202002080081ce3,0x80402000000000002000080002020020800814e3,0x80402002010080402010080402020020800814e3,0x80402000000000002000080002020020800814e3,0x0,0x0,0x0,0x0,0x8040200108004200200808020202002080081ce3,0x0,0x80402000800820022004080502020020800814e3,0x80402000000000402000080002020020800814e3,0x80402000801020042004080502020020800814e3,0x0,0x80402002002080082010080402020020800814e3,0x80402000000000002000080002020020800814e3,0x80402002004080102010080402020020800814e3,0x80402000000000002000080002020020800814e3,0x80402002008080202010080402020020800814e3,0x80402000000000002000080002020020800814e3,0x80402000010000402000080002020020800814e3,0x80402000000000002000080002020020800814e3,0x80402000020000802000080002020020800814e3,0x0,0x0,0x0,0x80402002080082002010080402020020800814e3,0x0,0x80402004000900022020082022020020800834e3,0x80402000000000402000080002020020800814e3,0x80402004001100042020082042020020800834e3],
[0x0,0x80402000402010082002080082020020800816e3,0x80402000000000002000080002020020800814e3,0x80402000004000102000080102020020800814e3,0x80402000000000002000080002020020800814e3,0x8040200100804020200808020202002080081ce3,0x80402000000000002000080002020020800814e3,0x80402002010080402010080402020020800814e3,0x80402000000000002000080002020020800814e3,0x0,0x0,0x0,0x0,0x80402004080102002020080802020020800834e3,0x0,0x13c0e7220481,0x424084220481,0x13c0e7220481,0x4080220481,0x2340c6220481,0x424084220481,0x2340c6220481,0x0,0x424084220481,0x0,0x424084220481,0x0,0x844188220501,0x4080220481,0x844188220501,0x4080220481,0x0],
[0x14c1a8220501,0xc64188220501,0x14c1a8220501,0x844188220501,0x2541c8220501,0xc64188220501,0x2541c8220501,0x0,0x464188220501,0x80201008080202002040081002020020800854e3,0x464188220501,0x0,0x844188220501,0x844188220501,0x844188220501,0x44188220501,0x0,0x14c1a9220501,0x0,0x14c1a9220501,0x4080220481,0x2140c0220481,0x80002002000080002020020800814e3,0x2140c0220481,0x0,0x0,0x0,0x0,0x0,0x844188220501,0x4080220481,0x844188220501],
[0x4080220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_5010 : TreeBound (n := 4) 107 (programCode 0x422b071d65) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x10140d0220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_5011 : TreeBound (n := 4) 107 (programCode 0x422b071d66) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x80402000080002002080082002020020800814e3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_5012 : TreeBound (n := 4) 107 (programCode 0x422b071d67) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x10140d0220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_5013 : TreeBound (n := 4) 107 (programCode 0x422b071d68) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x80402000100804022080082002020020800814e3,0x80402000000000402080082002020020800814e3,0x80402000201008042080082002020020800815e3,0x0,0xc00020100806002080082002020020800814e3,0x10400402010082002080082002020020800814e3,0x140004020100a002080082002020020800815e3,0x0,0x2400080402012002080082002020020800816e3,0x80400000000002002080082002020020800814e3,0x4400100804022002080082002020020800814e3,0x80400000000002002080082002020020800814e3,0x840020100804200208008200202002080081ce3,0x80400000000002002080082002020020800814e3,0x10400402010082002080082002020020800814e3,0x80400000000002002080082002020020800814e3,0x20400804020102002080082002020020800834e3,0x0,0x0,0x0,0x80402000402010082080082002020020800816e3,0x0,0x10739c1220501,0x1021084220481,0x10739c1220501,0x0,0x10318c2220481,0x1021084220481,0x10318c2220481,0x1021084220481,0x1021084220481],
[0x1021084220481,0x1021084220481,0x1021084220481,0x80402000000000002020080802020020800814e3,0x0,0x0,0x0,0x80402000804020102080082002020020800814e3,0x0,0x1042181220501,0x1000084220481,0x1042181220501,0x0,0x10108c2220481,0x1000084220481,0x10108c2220481,0x1000080220481,0x1000084220481,0x1000084220481,0x1000084220481,0x1000080220481,0x0,0x0,0x0,0x0,0x8040200100804020208008200202002080081ce3,0x80402000000000002080082002020020800814e3,0x80402002010080402080082002020020800814e3,0x80402000000000002080082002020020800814e3,0x80402004020100802080082002020020800834e3,0x0,0xc00020804022402080082002020020800814e3],
[0x400400000002002080082002020020800814e3,0x1400040804022402080082002020020800814e3,0x0,0x2400082010082402080082002020020800814e3,0x0,0x4400102010082402080082002020020800814e3,0x0,0x8400202010082402080082002020020800814e3,0x8020200820004800180042001000c0020402ce4,0x10400400000002002080082002020020800814e3,0x10020400820004800180082002000c00404034e4,0x20400800000002002080082002020020800814e3,0x20020800820004800180102004004400804024e4,0x0,0x40021000820004800180202008004401008044e4,0x0,0x1042181220501,0x0,0x1042181220501,0x0,0x10521c2220501,0xf300003cc1e60f303cc1e60f307983cc0f301e600007980001e679803cc79803cde600f379801ee9bd95,0x10521c2220501,0x0,0x1042184220501,0x0,0x1042184220501,0x0,0x0,0x0,0x0,0x0],
[0x0,0xc00024020102022080082002020020800834e3,0x400400000002002080082002020020800814e3,0x1400044020102042080082002020020800834e3,0x0,0x0,0x0,0x0,0x0,0x0,0x8020200840005000180042001000c0020804ce4,0x10400400000002002080082002020020800814e3,0x10020400840005000180082002000c00408054e4,0x20400804020102802080082002020020800834e3,0x20020800840005000180102004004400804024e4,0x0,0x40021000840005000180202008004401008044e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_5126 : TreeBound (n := 4) 107 (programCode 0x422b071d69) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1024090220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_5127 : TreeBound (n := 4) 107 (programCode 0x422b071d6a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x80402000080002002080082002020020800814e3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_5128 : TreeBound (n := 4) 107 (programCode 0x422b071d6b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1024090220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_5129 : TreeBound (n := 4) 107 (programCode 0x422b071d6c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1dcd65077360b3597d77a22cd650ee6b9f35941dcf5fa3b50000773597f7244050001e08ffca003bb89941d653bd66c3d594777130a6d6503b9b41359401dcf41d6503b9b41359403b9ca6d6500773770d65007736826b2803bb8976500773770d650077394daca00ee7bf42415559,0x1021090220481,0x0,0x1485b0220501,0xd685b0220501,0x1485b0220501,0x0,0x0,0x80100844201108042080082002020020800835e3,0x0,0x80100044201108042080082002020020800835e3,0x4685b0220501,0x77536165001dd4d859400773d075a2e6b28000773594eee25d9400f5de8140000eee25d9400ee6b2f73594eee25f70d6500773d075940773770d6500773d075940773770d65007735cf9aca00ef59932800ee6ee1aca00eea6c2ca00ee6ee1aca00ef5d546ca73d9,0x4685b0220501,0x9485b0220501,0x8485b0220501,0x7983cc208b4b07a7300f307a7300222cf307a73f3003cfcc00f3f3003cc79801ed980079f9801ee23eb5,0x8485b0220501,0x8485b0220501,0x0,0xd00024100906002080082002020020800834e3,0x10480402010082002080082002020020800814e3,0x150004420110a002080082002020020800835e3,0x0,0x0,0x80400000000002002080082002020020800814e3,0x0,0x80400000000002002080082002020020800814e3,0x0,0x80400000000002002080082002020020800814e3,0x10480402010082002080082002020020800814e3],
[0x80400000000002002080082002020020800814e3,0x20500804020102002080082002020020800834e3,0x0,0x8001000020004000200030000200010000800100010000010008000400100000400400000401000001004000010010000010004000004010000010100000100100000102208513a7,0x0,0x0,0x1dcd650000165a0bfd77a5e682f0000342770c003bf4322f000ee6b2f7730ba409b059e83aca0773597bd66541395c93528ee7dc85f200eea6c2ca00077712eca00eea6c2ca000eea6c2ca001dd4d8770d65007736826b2807753616500773770d650077394daca00ee6d2a50cc369,0x10308c6220481,0x168f08f8e700001c32cb374e928a3afe288f8e700001c32cb372174784ed3eacdc83000032c1d43007c02d251ea49bc8300e19659bea9f010c3f995380b478fc3f7fc73da3c2f2b20d6afa49814fc3f7fc73968f08fbb93b5b422c8cbd8e184b87331e14c3af1f1ce5a3cd85be3c73800b479b0b7c78e75a3cd85be3c73800b479b0b7c78e7168f3616f8f1ce0168f3616f8f1ce02d1e6c2e0872a4f8e705a3c26b57d1f1ce0b48ed6d030e705a3c26b57d1f1ce0b47deb897639c168f0e9ca93e39c168f14406b7c7382d1e740f902c4a6b93dd,0x0,0x10108c2220481,0x10308c6220481,0x10108c2220481,0x10108c2220481,0x10308c4220481,0x10308c6220481,0x10308c4220481,0x10108c2220481,0x4000040010000201040002a041000000100008080400020aa1000100084000100400080000800200002001000010001000010008000008020000020100000100100000101208667a7,0x80092002402090082080080482020020800816e3,0x40000800100004010400034041000000100008100400020d21000100084000100400100000800400002002000010002000010008000008020000020100000100100000103208667a7,0x80002000402010082080080002020020800816e3,0x0,0x1dcd6503b9b4135940ee6d04d6500773d075940773770d6500773594ee6b283b9ad1735941dce536b283b9ad8e6b283b9ad8e6b28596858e8d75746ba7e9ab80000000002540c8ba35d3f4d5c0000430e2ccbcaadd1ac1ee6c6fd3582a0645d1adecd65000001dcd6577359b7097ca,0x1021084220481,0x0,0x0,0x1021082220481,0x1021084220481,0x1021082220481,0x1021084220481,0x1021084220481],
[0x1021084220481,0x1021084220481,0x1021084220481,0x1021088220481,0x0,0x1021088220481,0x0,0x0,0x1dcd65f5e6ea77c140003d77a050000f5de81400010c388d000773595dcda09aca0ee6b28ee6b63d87f538b37cd65773595dcddc3594001dd4d8594077394daca01dce536b2801dd4d8594001dd4d85cf9aca00ef5993280077712eca001dd11eaca00ee6ee1aca00ee6eeb2144e99,0x10308c6220481,0x0,0x0,0x10108c2220481,0x10308c6220481,0x10108c2220481,0x10108c2220481,0x10308c4220481,0x10308c6220481,0x10308c4220481,0x10108c2220481,0x0,0x0,0x1dcd660c4007cc9947735b1cd651dcd6c73594ee6b45cd65000773595dcda09aca0ee88f565003bde159ae06dcd65773595dcddc35b1cd6507736826b283b9b059aca0ee6d04d6507735b1cd6507735cf9aca00ef5993280077712eca001dd11eaca00ee6ee1aca00eeaa840e6e999,0x0,0x0,0x0,0x1000084220481,0x0,0x0,0x10108c2220481,0x1000084220481,0x10108c2220481],
[0x1000080220481,0x1000084220481,0x1000084220481,0x1000084220481,0x1000080220481,0x0,0x0,0x0,0x0,0x1021090220481,0x1021090220481,0x1021090220481,0x1000090220481,0x0,0x14a1b0220501,0xc62190220501,0x14a1b0220501,0x0,0x0,0x80100804020100802080082002020020800834e3,0x789b3875acdb9acbdcd65ee6b2bb9ad173594ee6b2f7acc9943b9aca3b9bb86b28003bd664cf9a4b870c2d1735943b9aca773770d6500773d0759403b9ca6d6500ee729b5940773770d65007735cf9aca00ef5993280077712eca001dd11eaca00ee6ee1aca00ee6ee9446e999,0x80100804020100802080082002020020800834e3,0x462190220501,0xc62190220501,0x462190220501,0x842190220501,0x842190220501,0x842190220501,0x842190220501,0x42190220501,0x0,0x0],
[0x421090220481,0x0,0x0,0x221090220481,0x0,0x221090220481,0x0,0x421090220481,0x421090220481,0x421090220481,0x90220481,0x800090220481,0x90220481,0x800090220481,0x90220481,0x0,0x14a1b0220501,0xc62190220501,0x14a1b0220501,0x0,0x800040002020100010280c0001020001000080404000a23020000880020000400400000801000002004000010010000010008000008020000020100000100100000101208667a7,0x0,0x0,0x0,0x462190220501,0xc62190220501,0x462190220501,0x842190220501,0x842190220501,0x842190220501,0x842190220501,0x42190220501],
[0x0,0x14a5b0220501,0x400090220481,0x14a5b0220501,0x0,0x0,0x0,0x0,0x0,0x400090220481,0x400090220481,0x400090220481,0x90220481,0x842190220501,0x90220481,0x842190220501,0x90220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_5306 : TreeBound (n := 4) 107 (programCode 0x422b071d6d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1044190220501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_5307 : TreeBound (n := 4) 107 (programCode 0x422b071d6e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1340d0220481,0x424090220481,0x1340d0220481,0x0,0x1340c1220481,0x424084220481,0x1340c1220481,0x4080220481,0x224082220481,0x424084220481,0x224082220481,0x0,0x424084220481,0x0,0x424084220481,0x0,0x804088220481,0x4080220481,0x804088220481,0x4080220481,0x224090220481,0x420008408000a0001807020040e043080042304,0x224090220481,0x0,0x1e9cc007a73000f3f35bd6407b66001e600002d90b7b04c0000f300f35bd829cc00798079801e611156,0x4100104000804020180102004020400800824e4,0x0,0x4100104001004040180002004000400800804e4,0x1e7e60079f9800f3f33cc0004fe9900fa98002d907a76cc07b75300f33d3b6603dbaa7379801e9dcf76,0x0,0x0],
[0x0,0x0,0x410010400800420018004200400840080180ce4,0x1e7e60079f9800f3f33d3980409b300fa98002d907a76cc07b75300f33d3b6603dbaa7379801e9dcf76,0x4100104010004400180082004010400802814e4,0x1e7e60079f9800f3f33d3980409b300fa98002d907a76cc07b75300f33d3b6603dbaa7379801e9dcf76,0x420010404000880018022200404442080084504,0x0,0x420010404000900018022200404442080084504,0x424090220481,0x1020020408000a00018060e004041f8c80100904,0x424090220481,0x0,0x200e08230008c002308004200202001080081ca3,0x421090220481,0x200f08630008c004308004200202001080081ca3,0x10100404001004040180006004000c00806030e4,0x0,0x0,0x0,0x0,0x421090220481,0x421090220481,0x421090220481,0x90220481,0x802090220481,0x90220481,0x802090220481,0x90220481,0x804090220481,0x4090220481,0x804090220481],
[0x4090220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_5372 : TreeBound (n := 4) 107 (programCode 0x422b071d6f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1044190220501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_5373 : TreeBound (n := 4) 107 (programCode 0x422b071d70) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x14c1b0220501,0x0,0xd685b0220501,0x421090220481,0xd685b0220501,0x10080402010082002080082002020020800814e3,0x0,0x0,0x0,0x0,0x421090220481,0x421090220481,0x421090220481,0x400090220481,0xc62190220501,0x421090220481,0xc62190220501,0x400090220481,0x14c1b0220501,0x0,0x14c1a1220501,0x80002002000080402020020800814e3,0x14c1a1220501,0x4080220481,0x2140c2220481,0x80002002000080002020020800814e3,0x2140c2220481,0x0,0x0,0x0,0x0],
[0x0,0x844188220501,0x4080220481,0x844188220501,0x4080220481,0x0,0x25c1e1220501,0x0,0x25c1e1220501,0x2140c2220481,0x2140c2220481,0x2000080080002002000080002020020800814e3,0x2140c2220481,0x0,0x0,0x2000080080002002080080002020020800814e3,0x0,0x0,0x2541c8220501,0x2000080080002002010080002020020800814e3,0x2541c8220501,0x204080220481,0x7b660079f98007b663cc0002d9000222c0002d901e63cc1e60f301e60f31e603cc7980f3003cfebb56,0x0,0x25c1e1220501,0x4000100080002002000080402020020800814e3,0x25c1e1220501,0x2140c2220481,0x2140c2220481,0x4000100080002002000080002020020800814e3,0x2140c2220481,0x0],
[0x0,0x0,0x0,0x0,0x2541c8220501,0x0,0x2541c8220501,0x204080220481,0x0,0x8040000040200000201000000201000000000009e0e0000248200000800000000c000201010000f07040000000100004000402020001e0e080700000200008000001000085aba8,0x4200108000804020180202008040401000844e4,0x0,0x4200108001004040180002008000401000804e4,0x0,0x0,0x0,0x0,0x20100000040200000201000000201000000000003c0c0000200000000800800000c000000010000e06040002000100004000000020001c0c0806040002000080000040002072ba8,0x420010800800420018004200800840100180ce4,0x0,0x4200108010004400180082008010401002814e4,0x0,0x420010804000880018022200804442100084504,0x0,0x420010804000900018022200804442100084504,0x0,0x4685b0220501,0x421090220481,0x4685b0220501,0x0,0x0,0x8000200080000002080082002020020800814e3],
[0x0,0x0,0x421090220481,0x421090220481,0x421090220481,0x400090220481,0x462190220501,0x421090220481,0x462190220501,0x400090220481,0x3cde603cc79803cde63cc0002d9000222c0002d901e63cc1e60f301e60f31e600016c80f301e60f4556,0x0,0x4685b0220501,0x421090220481,0x4685b0220501,0x10080402010082002080082002020020800814e3,0x0,0x0,0x0,0x0,0x421090220481,0x421090220481,0x421090220481,0x400090220481,0x462190220501,0x421090220481,0x462190220501,0x400090220481,0x0,0x9485b0220501,0x421090220481,0x9485b0220501],
[0x10200408001004040180006008000c0100a050e4,0x0,0x0,0x0,0x0,0x421090220481,0x421090220481,0x421090220481,0x90220481,0x842190220501,0x90220481,0x842190220501,0x90220481,0x844190220501,0x4090220481,0x844190220501,0x4090220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_4877 : TreeBound (n := 4) 107 (programCode 0x422b071d) := by
  conv in programCode _ => reduce
  exact branchFour (k := (3,0)) (by decide +kernel) part100_4878 part100_4879 part100_4880 part100_4881 part100_5010 part100_5011 part100_5012 part100_5013 part100_5126 part100_5127 part100_5128 part100_5129 part100_5306 part100_5307 part100_5372 part100_5373

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_5519 : TreeBound (n := 4) 107 (programCode 0x422b071e71) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8040001008000a00018060200404040080000104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_5520 : TreeBound (n := 4) 107 (programCode 0x422b071e72) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x140003008000a00018060200404040880010104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_5521 : TreeBound (n := 4) 107 (programCode 0x422b071e73) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8040001008000a00018060200404040080000104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_5522 : TreeBound (n := 4) 107 (programCode 0x422b071e74) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x16c83cc1e600016c83cc01e6f307983cc02d9000f6cc003ea6000f6cfcc001e60f30f6cc001e703885,0x0,0x7d4c001f53000b640000f30079bcc02d900003cc3cc1e616c83cc00001e60000f303cc1e703885,0x2080002002000080402000020000814e3,0x1e600007a730012fc0000f30079bcc01e600007983cc1e60f303cc00003cc0000f307981e703d95,0x80002002000080402000020000814e3,0x25f800097e3cc1e603cc0002d9000222c0001e6102300111600010230799e607980f30798003ea93b6,0x80002002000080402000020000814e3,0x25f80007d4c001e612fc0002d9000222c0001e6102300111600010230799e607980f30798003ea93b6,0x0,0x25f800097e0001e612fc0002d9000222c0001e6102300111600010230799e607980f30798003ea93b6,0x109d04e4001e600000003cc2139f300003cc00f409c87980000f307983d027203cc00007980001e68a8c5,0x80002080002002000080402000020000814e3,0x0,0x20100804080102002020080402020020800834e3,0x80002002000080402000020000814e3,0x201008080202002040080402040021000854e3,0x80002002000080402000020000814e3,0xf362b83cc1e600016c83cc2139f307983cc0079803d398003d39801e9cfd57e3cc0f30408c001e64dc35,0x0,0xc080208481,0x2080002002000080002000020000814e3,0xc080208481,0x4080200481,0x0,0x80002002000080002000020000814e3,0x0,0x0,0x0,0xf3084e4001e600000003cc2139f300003cc00f3f3007980000f300003d027203cc00007980001e68a8c5,0x80002080002002000080002000020000814e3],
[0x0,0x44180220501,0x4080200481,0x44180220501,0x4080200481,0x0,0x4825e60a717981e603cc00088b000222c000352c8240001e600000f31e62d981180000798003cc3c26,0x3cc1e60f307981e60b6400088b000222c00037155b400097e00010231e63167dd80f30798003ea9cb6,0x0,0x0,0x44580007980001e603cc00088b000222c0002d90b640001e600000f31e61e681180000798003cc3c26,0x3ccf30079bcc01e6408c00088b000222c000354716407b8460007a731e62dd4d18004c698003eb15a6,0x0,0x0,0x0,0x0,0x482400097e0001f533cc00088b000222c0003528b640799e601e60f31e61e68118000fa98003cc3c26,0x0,0x4825e607980001e603cc00088b000222c000352c8240001e600000f31e62d981180000798003cc3c26,0x408c00088b0001f533cc00088b000222c0003528b640799e601e60f31e61e68118000fa98003cc3c26,0x408de6088b0001e603cc00088b000222c000352c8240001e600000f31e62d981180000798003cc3c26,0x408c00081180020463cc00088b000222c0003528b640f31e603cc0f31e61e68118000fa98003cc3c26,0x0,0x7980001e60000b640000f30079bcc02d900003cc0001e60f303cc00001e60000f303cc1e703885,0x2080002002000080002000020000814e3,0x1e6000079800012fc0000f30079bcc01e600007980001e60f303cc00003cc0000f307981e703d95,0x80002002000080002000020000814e3,0x25f80007d4c001e603cc0002d9000222c0001e67a73007b660007a730799e60798003d398003eb0d36,0x80002002000080002000020000814e3,0x25f8000798f301e612fc0002d9000222c0001e67a73007b660007a730799e60798003d398003eb0d36,0x0,0x25f800097e0001e612fc0002d9000222c0001e67a73007b660007a730799e60798003d398003eb0d36],
[0x109d04e4001e600000003cc2139f300003cc00f409c87980000f300003d027203cc00007980001e68a8c5,0x80002080002002000080002000020000814e3,0x0,0x20100804080102002020080802020020800834e3,0x80002002000080002000020000814e3,0x201008080202002040081002040021000854e3,0x80002002000080002000020000814e3,0x0,0x23001000080000000108000000220004000000110000000440000000900000000e002300010008c0001000200000002080020003001080008004100008000100000011000ffea8,0x2000080008000080020000800020000c0000000900000000c0000000900000000d00220001000008001000200000002080010002801010008000100008000100000011000fb3a8,0x0,0x0,0x0,0x10002000040040000100080000200084000000030000000440000000900000000c001020018004c000100020000000208000400200088000c002100008000100000011424e2ea8,0x0,0x0,0x0,0x10020000040400000100800000200804000000030000000440000000900000000c001020018004c000100020000000208000400200088000c002100008000100000011200e2ea8,0x220000000808000002200000002080040000000900000000c0000000900000000d00220001000008001000200000002080010002801010008000100008000100000011400fb3a8,0x0,0x230010000800000002080000002000040000001100000000c0000000900000000e00230001000008001000200000002080020003001010008000100008000100000011000ff3a8,0x408c0010230001f533cc00088b000222c000352c8241e61e60001f531e62d981183cc079800445bcb6,0x0,0x408c00102300020463cc00088b000222c000352c8241e61e60001f531e62d981183cc079800445bcb6,0x0,0x0,0x0,0x0,0x0,0x0,0x1400050002004080104020104020020800a05e4,0x7983cc1e60000798003cc0001ed98003ced900003cc0001e602d93cfcc001e60000f6cc001e703885],
[0x1400050004004100104020104020020800a05e4,0x445800111600025f80079801e7e6007a01181e7e60f3079c08c0f3f3079803cde600f37980408e1ef6,0x140005000800420010404010402002080120de4,0x0,0x1400050010004400104080104020020802215e4,0x7983cc1e6000079807980001e679807982d900003cc0001e61e603cfcc001e60000f6cc001e703885,0xf307983cc1e600007983cc21390007983cc007a730079800007980003cfcc003cc0000408c001e64dc35,0x1c7a7983cc1e600007981e621391e67980f3007b47a07980000799e603cfcc003cc0000408c001e64dc35,0xf307983cc1e600007983cc21390007983cc007a730079800007980003cfcc003cc0000408c001e64dc35,0x0,0x23001000080000000108000000220004000000110000000440000000900000000e002300010000c0004000200000002080020003001080008000100008000100000011000ffea8,0x2000080008000080020000800020000c0000000900000000c0000000900000000c00020001000008004000200000002080010002000010008000100008000100000011000fb3a8,0x0,0x0,0x0,0x10002000040040000100080000200084000000030000000440000000900000000c001020018004c000400020000000208000400200088000c002100008000100000011424e2ea8,0x0,0x0,0x0,0x10020000040400000100800000200804000000030000000440000000900000000c001020018004c000400020000000208000400200088000c002100008000100000011200e2ea8,0x220000000808000002200000002080040000000900000000c0000000900000000c00020001000008004000200000002080010002000010008000100008000100000011400fb3a8,0x0,0x230010000800000002080000002000040000001100000000c0000000900000000e00230001000008004000200000002080020003001010008000100008000100000011000ff3a8,0x408c0010230001f533cc00088b000222c000352c8243cc1e60001f531e62d981183cc079800445bcb6,0x0,0x408c00102300020463cc00088b000222c000352c8243cc1e60001f531e62d981183cc079800445bcb6,0x0,0x109c83cc1e6000fa980003ea60016c80003f9900f33cc03cde702303cfcc001e70230f6cc001e703885,0x180424420222,0x0,0x180424420222,0x0],
[0x0,0x180424420222,0xc00050002004100108040205020020800a0da4,0x180424420222,0x181024620a62,0x0,0x181024620a62,0x0,0x0,0x0,0x0,0x445800111600025f83cc00088b000222c0003528b643cc1e601e60f31e61e68118000fa98003cc3cb6,0x0,0x0,0x180424420222,0x11158683cc1e6000079800114b28016c800079fa915149800007a731e9d0439a3cc0000408c001e64dc35,0x180424420222,0x0,0x0,0x180424420222,0x1400050004004100110080404020020800a15e4,0x180424420222,0x181024620a62,0x25f800111600025f825f8001e61e61ed98001ed9cbf03cc003d398f307992fc798000fa98003cc3446,0x181024620a62,0x7983cc1e6000079807980001e679807982d900003cc0001e711603cfcc001e60000f6cc001e703885,0x0,0x0,0x0,0x0,0x4825e60a717981e603cc00088b000222c000352c8240001e600000f31e62d981180000798003cc3c26,0x2000080008000080020000800020000c0000000900000000c0000000900000000d00220001000008001000200000002080010002801010008000100008000100000011000fb3a8],
[0x1e7e61ed98007b660012fc0223b30079bcc01e61e607987981e61e603cc0811bcc01e6f307981e722395,0x844188220501,0x4825e607980001e603cc00088b000222c000352c8240001e600000f31e62d981180000798003cc3c26,0x800080002002020080802000020000814e3,0x1e6007d4c003cde6007d4c01e6f30811bcc02d91e603cc7981e61e603cfcc001e60f30f35b201e703885,0x0,0x4825e6097e0001e612fc00088b000222c000352c8240001e600000f31e62d981180000798003cc3c26,0x1e7e6007b66001e7e9cc0002d9000222c0001e6102326017e00010230799e607984bffa9800467dfb6,0x48240011160001f533cc00088b000222c000352c82400097e01e60f31e62d98118000fa98003cc3cb6,0x0,0x844188220501,0x804088200481,0x844188220501,0x844188220501,0xf307983cc1e600007983cc2139f307983cc007a730079800007a73003cfcc003cc0000408c001e64dc35,0x0,0x4459e60f300001e603cc00088b000222c0003528b641e61e600000f31e61e681180000798003cc3cb6,0x1002080002002040081002000020000814e3,0x1000000004200000008c0000001400000101000000404000010010000060020000100080000400100000800200001000000001000008004000020008000c00010032873227,0x844188220501,0x4458000f300001e603cc00088b000222c0003528b641e61e600000f31e61e681180000798003cc3cb6,0x1000080002002040081002000020000814e3,0x1a9400f6cc000f4e6007d4c21b37307b69cc0079f980798798079bcc03d0309e3cc0f30409b301e64dc35,0x1e67980799e601e67d4c0002d9000222c00025f80f31e61e607980f30799e60798000fa98003cc33b6,0x0,0x0,0x220000000808000002200000002080040000000900000000c0000000900000000900020001000008001000200000002080010002001010008000100008000100000011400fb3a8,0x0,0x844188220501,0x804088200481,0x844188220501,0x844188220501],
[0xf307983cc1e600007983cc2139f307983cc007a730079800007a73003cfcc003cc0000408c001e64dc35]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_5715 : TreeBound (n := 4) 107 (programCode 0x422b071e75) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x20c090218481,0x224090210481,0x20c090218481,0x0,0x16cbcc1e600007981e612fc00088b000222c000352c82400097e00000f31e62d981180000798003cc3cb6,0xf300012fc7983cc1e612fc0002d9000222c0001e6102300111600010230799e607980f30798003ea93b6,0x0,0xf300011160003cc1e612fc0002d9000222c0001e61f5300097e0001f530799e607983cc079800445b3b6,0x0,0xf30000fa98003cc1e612fc0002d9000222c0001e67a73007b660007a730799e60798003d398003eb0d36,0x0,0x0,0x0,0x0,0xf33cc1e607987981e612fc00088b000222c0003528b643cc1e601e60f31e61e68118000fa98003cc3cb6,0x0,0x16cbcc1e600003cc1e612fc00088b000222c000352c8240001e600000f31e62d981180000798003cc3c26,0xf33cc1e607987981e612fc00088b000222c00025f8b641e61e601e60f31e61e68118000fa98003cc3cb6,0x0,0xf30000f307983cc1e612fc0002d9000222c000222c0f30f31e603cc0f30799e60798000fa98003cc33b6,0x214090210481,0x8402008048000a00018060200404042080042304,0x214090210481,0x0,0x16e660f6cc003cc0f307f39980798f301e600002d90b736cc0000f300f31e62dcd398798079801e611156,0x80020100800804020180102004020400800824e4,0x0,0x80020100801004040180102004020400800824e4,0x0,0x0,0x0],
[0x0,0x0,0x8002012080800420018004200402040080190ce4,0x16f590f6cc003cc0f307f3d640798f301ed98002d90b7b04c001f5300f31e62deb998798079801e611156,0x80020120810004400180082004020400802914e4,0x16e660f6cc003cc0f307f399807980001e600002d90b736cc0000f300f31e62dcd398798079801e611156,0xf307d4c001e60f3079f980025f8001ed98002d900f33cc001f5300f30799e60798798079801e610856,0x0,0x0,0x224090210481,0x9008020108000a00018060200404048080100904,0x224090210481,0x0,0x238490218481,0x221090210481,0x238490218481,0x80080402001004040180102004020400802010e4,0x0,0x0,0x0,0x0,0x221090210481,0x221090210481,0x221090210481,0x200090210481,0x7980007980f307d4c07980f379800007980f3f3003cfcc00f3f3003cc1e601e679807980001e68a055,0x221090210481,0x2010088040081002080082002010020480814e3,0x0,0x244190230501,0x224090210481,0x244190230501],
[0xc020100808000a00018060200404060080804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_5780 : TreeBound (n := 4) 107 (programCode 0x422b071e76) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x470008408000a00018060200404042080042304,0x400808018000a00018060200404042080042304,0x0,0x60c081218481,0x40c084218481,0x60c081218481,0x1e600007a730012fc0000f30079bcc01e600007980001e600003cc00003cc0000f307981e703d95,0x40c082218481,0x40c084218481,0x40c082218481,0x0,0x40c084218481,0x44b008108000a00011060020404042080042b04,0x40c084218481,0x0,0x50c088218481,0x40c086218481,0x50c088218481,0x1f173307980f307b663cc00088b000222c00025f8b641e61e603cc0f31e61e9d39800f379800f8bb7d6,0x0,0x1e601e6798079879812fc00088b000222c000371282400097e01e60f31e62ddc698003d39800f4f1636,0x80002002000080402000020000814e3,0x10bb59ad93ea63d398012fc2139f3003cfcc00f3003d398007a73001e9d032843cc79807983cc1e68a8c5,0x80002002000080002000020000814e3,0x0,0x80002002000080002000020000814e3,0x109cfaec9e7e60000007d4c2139f300003cc00f301e679803ccf300f33d027203cc0000799e601e68a8c5,0x0,0x1e601e6798079879812fc00088b000222c0002daf1643cc1e60007a731e61e9d398003d39800f4f1636,0x0,0x2080002002010080402000020000814e3],
[0x0,0x20100804080102002020080802020020800834e3,0x80002002000080002000020000814e3,0x8080002002040081002000020000814e3,0x80002002000080002000020000814e3,0x440008008000a00018060200404042080042304,0x402008048000a00018060200404042080042304,0x442008048000a00018060200404042080042304,0x0,0x1e60f307983cc07987f39980798f301ed98002d90b736cc00102300f31e61e9d398798079800f4fead6,0x2020080800804020180102004020400800426e4,0x0,0x2020080801004040180102004020400800426e4,0x0,0x0,0x0,0x0,0x0,0x202008080800420018004200402040080142ee4,0x1e60f307983cc07987f399807987981ed98002d90b736cc00102300f31e61e9d398798079800f4fead6,0x2020080810004400180082004020400802436e4,0x1e60f307983cc07987f3b7e07b66001e600002d90b7738c0000f300f31e61e9d398798079800f4fead6,0x402008084000880018023200404042080046704,0x0,0x402008084000900018022200404042080046704,0x442008048000a00018060200404042080042304,0x408008108000a00018060200404042080042b04,0x460008408000a00018060200404042080042304,0x0,0x0,0x2080082000804020180102004020400800432e4,0x0],
[0x2080082001004040180102004020400800432e4,0x0,0x0,0x0,0x0,0x0,0x208008200800420018004200402040080143ae4,0x0,0x2080082010004400180082004020400802432e4,0xf379801e7e60079bcc798003ea7e60798b642d900f708c03ccf300f30f31e601e679bd39800f568dc6,0x0,0x0,0x0,0x470008008000a00018060200404042080042304,0x420008408000a00018060200404042080042304,0x440008008000a00018060200404042080042304,0x420008808000a00018060200404042080046304]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_5861 : TreeBound (n := 4) 107 (programCode 0x422b071e77) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8040001008000a00018060200404040080000104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_5862 : TreeBound (n := 4) 107 (programCode 0x422b071e78) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1ed98007b66000fa985b998088b0001e600002d90b736cc0000f300f31e61e9d398798079801e611156,0x0,0xfa98003ee2c00f3f30003cc1e63cc1e603cc2d900f33cc03ccf300f3079801ed98798079801e7f6856,0x4004100100804020180102004020400800824e4,0x0,0x0,0x4400100000804020180102004020400800824e4,0x4010100400804020180102004020400800826e4,0x4400100800804020180102004020400800824e4,0x4020100800804020180102004020400800824e4,0x4020100800804020180102004020400800824e4,0x404010100080402018010200402040080082ce4,0x4100104000804020180102004020400800824e4,0x4080102000804020180102004020400800834e4,0x4100100000804020180102004020400800824e4,0x4100104000804020180102004020400800824e4,0x1ed98007b66000f300000f307983cc1e603cc2d903cc3cc03ccf300f31e61ebb998798079801e7f7156,0x4200108000804020180102004020400800864e4,0x0,0x0,0x0,0x2400110004004100104020104820020800804a4,0x0,0x0,0x0,0x2400110004004100100000104020000800804a4,0x4400110004004100104020104020020800804e4,0x2400110004004100100000104020000800804a4,0x240011000400430010806020502006080180ca4,0x2400110004004100100000804020020800804a4,0x240011000400430010806040502002080180ca4],
[0x44580011160004458000f4e60044580007b661e607987981e61e603cc07983cc1e60f6cc001e703d95,0x20200000020800000202000000208000000800002500000040028000085000000084000a00080004000100000040100008000400001408000200010000014010000010000871fa8,0x7980001e60004458000f4e60044580007b667980799e601e63cc03cc00003cc1e60f6cc001e703d95,0x0,0x0,0x0,0x4004100101004040180102004020400800824e4,0x0,0x0,0x4400100001004040180102004020400800824e4,0x4010100401004040180102004020400800826e4,0x4400100801004040180102004020400800824e4,0x4020100801004040180102004020400800824e4,0x4400100801004040180102004020400800824e4,0x404010100100404018010200402040080082ce4,0x4100104001004040180102004020400800824e4,0x4080102001004040180102004020400800834e4,0x4100100001004040180102004020400800824e4,0x4100104001004040180102004020400800824e4,0x0,0x4200108001004040180102004020400800864e4,0x0,0x1f173307980000f3005b998088b0001e600002d90b736cc0000f300f31e61e9d398798079801e611156,0x1e600f379801e6f300b640004bf00007983cc2d907983cc03ccf300f30f31e601e6798079801e7f6f46,0x0,0x0,0x1ed98007b66000f3003cc0004bf00007980002d907983cc03ccf300f30f31e601e6798079801e7f6f46,0x0,0x0,0x0,0x0,0x1e67980799e600f31ec8403c88b0001e6f3002d90d08444007a7300f31e63420978798079801e64dd56],
[0x1eda73079fb660f3f33cc0004fe9900fa98002d907a76cc07b75300f30f31e603cc7a7379801e9dcf76,0x0,0x1f173307980000f3005b998088b00007980002d90b736cc0000f300f31e61e9cde6798079801e6110f6,0x1e7e60079f9800f3f33cc0004fe9900fa98002d907a76cc07b75300f30f31e603cc7a7379801e9dcf76,0x1ed98007b66000f3003cc00088b0001e600002d90b643cc0000f300f31e61e9d398798079801e611156,0x0,0x0,0x1ed98007b66000fa980079807987980799e603528b643cc00000000f31e61e9cde6000079801e6110f6,0xfa98003ea6000fa98001e601e7e601e61e601e61023000f301e6102307983cc7980f3079801e610856,0x2400110002004080104020104820020800804a4,0x0,0x0,0x0,0x2400110002004080100020104820000800804a4,0x4400110002004080104020104020020800804e4,0x1ed98007b66000fa98007980799e601e61e60280bdd5cf9801e60f3f31e613579980f3079801e611156,0xfa98003ea6000fa98001e601e7e601e61e601e9ccf303cc07983ccf3079800fa98003d39801e64d456,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2400110004004100104020104820020800804a4,0x0,0x0,0x0,0x2400110000004100100000104020000800804a4,0x4400110004004100104020104020020800804e4],
[0x2400110000004100100000104020000800804a4,0x240011000400410010804020502002080080ca4,0x2400110004004100100000804020020800804a4,0x240011000000410010804040402000080080ca4,0x1ed98007b66001ed98007980001ed98003cde61e607987981e61e603cc3cc03ccf300f6cc001e703d95,0x0,0x7980001e6001ed98007980001ed98003cde67980799e601e63cc03cc00003ccf300f6cc001e703d95,0x0,0x0,0x0,0x0,0x2400110002004100104020104820020800804a4,0x0,0x0,0x0,0x2400110002004100100000104820000800804a4,0x4400110004004100104020104020020800804e4,0x2400110002004100100000904820020800804a4,0x240011000200410010804020502002080080ca4,0x2400110002004100100000804020020800804a4,0x4400110004004100110080404020020800814e4,0x4400110004004100100002004020400800804e4,0x0,0x4400110004004100100002004020400800804e4,0x0,0x0,0x0,0x0,0x2400110004004100104020104820020800804a4,0x0,0x0,0x0],
[0x2400110000004100100000104020000800804a4,0x4400110004004100104020104020020800804e4,0x2400110000004100100000104020000800804a4,0x1ed98007b66000fa9801338c1eace307aafc01e9cd18f8f3097e3ccf30798097fe6025ff98097e4d996,0x2400110000004100100000804020020800804a4,0x0,0x2400110000004100100002804020420800804a4,0x0,0x2400110000004100100002004020400800804a4,0x0,0x440011000800420018004200402040080180ce4,0x1ed98007b66000fa985b9980798f301ed98002d90b736cc001f5300f31e61e9d398798079801e611156,0x4400110010004400180082004020400802814e4,0x0,0x1f173303f9ccc0f3005b99807980001e600002d90b736cc0000f300f31e61e9d398798079801e6110c6,0x0,0x0,0x0,0x1f173303ea6000f3005b99807980001e600002d90b736cc0000f300f31e61e9d398798079801e6110c6,0x1e607987981e60f304093980409b300fa98002d907a76cc07b75300f30f31e603cc7a7379801e9dcf76,0x1eda7303ea6000f307f399807980001e600002d90b736cc0000f300f31e61e9d398798079801e6110c6,0x4020100800004000180002004020400800804e4,0x4000100800004000180002004020400800804e4,0x1e63cc07987980f31ea494c03ea6f307983cc2d90892d4c03ccf300f30f31e601e679f9f9801e833b46,0x1eda73079fb660f3f33d39804fe9900fa98002d907a76cc07b75300f30f31e603cc7a7379801e9dcf76,0x1e67980799e600f33d0494c03ea7e60798b642d90892d4c03ccf300f30f31e601e679f9f9801e870746,0x4000100000004000180002004020400800804e4,0x1e7e60079f9800f3f33d3980409b300fa98002d907a76cc07b75300f30f31e603cc7a7379801e9dcf76,0x1ed98003ea6000f3005b99807980001e600002d90b736cc0000f300f31e61e9d398798079801e6110c6,0x0,0xfa98003ea6000fa9807980025f8001ed98002d900f33cc001f5300f30799e60798798079801e610856,0x0],
[0x1f164007980000f3003d398088b0001e600002d90b643cc0000f300f31e61e9d398798079801e611156,0x1e601e67980798f300d4a00088b0001ed98002d90b736cc001f5300f31e61e9d398798079801e611156,0x0,0x4000000014000800050002000080008000100000000400082002000208002000040040000080100000200400001001000001004000000810000002000000010100000010020866ba7,0x1ed98007b66000f3003cc00088b0001e600002d90b643cc0000f300f31e61e9d398798079801e611156,0x0,0x0,0x0,0x0,0x1e63cc07987980f31e9cc0004bf00007980002d907983cc03ccf300f30f31e601e6798079801e833b46,0x0,0x0,0x1f164007980000f3003d398088b00007980002d90b643cc0000f300f31e61e9cde6798079801e6110f6,0x0,0x1ed98007b66000f3003cc00088b0001e600002d90b643cc0000f300f31e61e9d398798079801e611156,0x0,0xfa98003ea6000fa980f3000222c001f530002d900f33cc001f5300f30799e60798798079801e610856]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_6039 : TreeBound (n := 4) 107 (programCode 0x422b071e79) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8040001008000a00018060200404040080000104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_6040 : TreeBound (n := 4) 107 (programCode 0x422b071e7a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1040021008000a00018060200404048080100904]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_6041 : TreeBound (n := 4) 107 (programCode 0x422b071e7b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x40c090218481,0x424090210481,0x40c090218481,0x0,0x60000001180000001400000008100000014000000110000000440000000900000000c002b00000002c0000002a0000000208002000380008000e000100008000100008001400fdea8,0x10000400080002002000080402000020000814e3,0xf379adae7e63d398012fc2139f3003cfcc00f3003d398007a73001e9d032843cc79807983cc1e68a8c5,0x10000400080002002000080002000020000814e3,0x0,0x10000400080002002000080002000020000814e3,0xf37aec9e7e60079807d4c2139f300003cc00f301e679803ccf300f33d027203cc0000799e601e68a8c5,0x0,0x16c800222c0007b660012fc00088b000222c0003528b643cc1e601e60f31e62d907980f307983cc1e9cb6,0x0,0x10000402080002002010080402000020000814e3,0x0,0x10080404080102002020080802020020800834e3,0x10000400080002002000080002000020000814e3,0x10000408080002002040081002000020000814e3,0x0,0x414090210481,0xc002080048000a00018060200404060080402304,0x414090210481,0x0,0x0,0x20020800800804020180102004020400804024e4,0xf379adae7e60079800f311439001e9cc007a73f30079bcc00f3f3003d032843cc79807983cc1e68a8c5,0x20020800801004040180102004020400804024e4,0x0,0x0,0xf37aec9e7e60079807987b93900f300003ccf3f30079bcc00f3f3003d027203cc0000799e601e68a8c5],
[0x0,0x111600f379803cde6007dc94c04de53008118002d9088b3cc03ccf300f30f31e601e688b07983cc1f6f46,0x802080080800420018004200402040080502ce4,0x20020800820004800180102004020400804024e4,0x10020800810004400180082004020400806034e4,0x16c800f300003cde6007f39980798f301e600002d90b643cc0000f300f31e62d9079879807983cc1f7156,0x20020800820004800180102004020400804024e4,0x0,0x20800840005000180002004020400804024e4,0x424090210481,0xc008080108000a00018060200404060080402904,0x424090210481,0x0,0x438490218481,0x421090210481,0x438490218481,0x20080802001004040180102004020400804030e4,0x0,0x0,0xf37aec9e7e60079807987b93900f300003ccf3f30079bcc00f3f3003d027203cc0000799e601e68a8c5,0x0,0x421090210481,0x421090210481,0x421090210481,0x400090210481,0x462190230501,0x421090210481,0x462190230501,0x400090210481,0x444190230501,0x424090210481,0x444190230501],
[0xc020080808000a00018060200404060080406104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_6106 : TreeBound (n := 4) 107 (programCode 0x422b071e7c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x20020000080080000200200000200800040020001100000000c0000000800040000c000300010000080040000200100000800200021000100001001000200001000010000817f3a8,0x10400410000804020180102004020400802010e4,0x200200010ccc800000202000000088000000201000000486000002200000002040040000100100000200400001001000001000200001010cc0002000200010100000010020872ba7,0x10400410001004040180102004020400802010e4,0x0,0x20020010020080000200000080200000240020001000040000c0000000800040000c000300010000080040000200100000800200021000100001001000200001000010000817d3a8,0xf3000f6cc001ed9800b640004bf00007983cc2d907983cc03ccf300f30f31e601e679807980f307b446,0x0,0xf3001e9cc0079f98012fc0004bf00007987982d907983cc03ccf300f30f31e601e679807980f307b446,0xf379803cde600798003cc0004bf00007980002d907983cc03ccf300f30f31e601e679807980f307b446,0x0,0x0,0x0,0x0,0x20000400020000800200008000200008040000000401010000c0000000801000000c000200010000080040000a20100000800080020000100001801000200001000010000c1753a8,0x0,0x0,0x4000040010000100040080200000200800000822000002008000004030000010060040000100100000400400000801000001004000001010400004005000008010000010050877627,0x0,0x4000100010000400040080800000201000000830000002040000008110000010020040000100100000400400000801000001004000001010400004021000008040000010210877667,0x0,0x0,0x0,0x0,0x79f9801e7e60079f98001e601e7e601e61e601e600f301e603cc1e6f3079800079800f37980f307ea16,0x0,0x0,0x0,0x0,0x10400410002004080104020104020020802814e4,0x0],
[0x0,0x480828420862,0x0,0x0,0x480828420862,0x0,0x480828420862,0x0,0xf5a3d800111600109c8007b939008191803cc79803d39800f379800f6d02eb83cc4bf04093981e64dc35,0x10c2f183cc1e6004c698007b939008118003cc7a89c879bcc007983cc3d027203cc3cc0408c001e64dc35,0x481024620862,0xf379803cde60079f982baa007b660007b66001e64235400f6cc001f531e615d51e60f307980f307b5f6,0x0,0x0,0x481024620862,0x10400410004004500104020104020020802814e4,0x104971803cde6004c698007b9390081ce403cc798f307983cc07983cc3d027203cc3cc040e7201e64dc35,0x481024620862,0x48102c620862,0x481024620862,0x0,0x481028620862,0x0,0x481028620862,0x0,0x0,0x0,0x104004100040041001100805040200a0802814e4,0x0,0x0,0x0,0x10400410004004100104020504020020802814e4],
[0x10400410004004100104020104020020802814e4,0x10400410004004100100000404020020802010e4,0x840041000200410010804020502002080281ca4,0x480828420862,0x10400410004004100110080404020020802814e4,0x0,0x480828420862,0x10400410004004100104022004020420802814e4,0x480828420862,0x0,0x409090218481,0x421090210481,0x409090218481,0x0,0x411090210481,0x20000100080000080200000800200000866a7000101000000080010000802000000c000335390000080040000000900000800200033538100008001000200001000010004857f3a8,0x411090210481,0x20000100080000400200001000200001066ab000101000000080010000802000000c000335590000080040000000900000800200033558100008001000200001000010004897f3a8,0x421090210481,0x421090210481,0x421090210481,0x421090210481,0x441190230501,0x421090210481,0x441190230501,0x421090210481,0x10400410008004200180042004020400803018e4,0x10400410010004800180082004020400802010e4,0x10400410010004400180082004020400802010e4,0x0,0x2003101008008000020000008020000026202000100000000400010000800000000c000310110000400040000000100000800200031010800000001000200001000010000817ffa8,0x822090210481],
[0x2003101008008000020000400020000026202000100004000400010000800000000c000310110000400040000000100000800200031010800000001000200001000010000817ffa8,0x0,0x812090218481,0x10010400400804800180182004020400802110e4,0x812090218481,0x10020400800804c20180186004020400806134e4,0x822090210481,0x822090210481,0x822090210481,0x842190220501,0x842190220501,0x802090200481,0x842190220501,0x842190220501,0x0,0x0,0x421090210481,0x0,0x0,0x411090210481,0x10010400420004800180082004020400806032e4,0x411090210481,0x10020400820004800180082004020400806034e4,0x421090210481,0x421090210481,0x421090210481,0x90200481,0x842190220501,0x90200481,0x842190220501,0x90200481,0x0],
[0x7000000100000000400000000230000000a0002150010000010100000800200002804000010010000008040000080100000100402200100000000080000400800020001001087ce27,0x822090210481,0x1a94001e60000408c00111621945cc04467300f3f30079bcc00f3f3003cfd8d0bcc01e67983cc1e68a8c5,0x10008400200004800180082004020400802010e4,0x812090218481,0x0,0x812090218481,0x0,0x822090210481,0x822090210481,0x822090210481,0x842190220501,0x842190220501,0x802090200481,0x842190220501,0x842190220501,0x0,0x0,0x20090210481,0x8000200080002080082002000020100814e3,0x0,0x0,0x1001040044000500018008200402040080a072e4,0x0,0x1002040084000500018008200402040080a054e4,0x20090210481,0x20090210481,0x20090210481,0x90200481,0x40190220501,0x90200481,0x40190220501],
[0x90200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_6267 : TreeBound (n := 4) 107 (programCode 0x422b071e7d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x80c0d020c481,0x824090210481,0x80c0d020c481,0x0,0x1e68191f9a066646000b64001f53081954c02d9000f6cc003ea6000f6cc003cde600f3f70c8c1e703885,0x20000800080002002000080402000020000814e3,0x200088002800a2002001080042001020100814e3,0x804080200481,0x0,0x20000800080002002000080002000020000814e3,0x1e600f3799e601e600f6cc01e6f30811bcc01e601e67980799e600f33cc07983cc1e60f708c01e703d95,0x0,0x1e67980799e601e601e9cc01e6f30811bcc01e603cc7980f31e603cc3cc0f303cc3cc0f708c01e703d95,0x0,0x1e67980799e601e6079bcc0000f307983cc01e60f307983cc1e607983cc3cc03ccf300f6cc001e703d95,0x0,0x844188220501,0x804080200481,0x844188220501,0x844188220501,0x814090218481,0xe602080048000a00018060200404073080402304,0x814090218481,0x0,0x1e67980799e601e60007983cde6017491803f99f3003cfcc01e6f3003cc003cde600f3f6cfcc1e703885,0x24020800800804020180102004020400804024e4,0x1e67980799e601e6001e60f33cc044d18007b66f30079bcc01e6f3003cc00f33cc03ccf6d3981e722395,0x24020800801004040180102004020400804024e4,0x0,0x0,0x1e67980799e601e600f30799e601ee11803cde6f30079bcc01e6f3003cc07983cc1e60f708c01e703d95],
[0x0,0x20000800004000180002004020400800000e4,0x8820200808004200180042004020400801008e4,0x20000800004800180002004020400800000e4,0x10820400810004400180082004020400802010e4,0x20000800004000180002004020400800000e4,0x20000820004800180002004020400800000e4,0x0,0x20000840005000180002004020400800000e4,0x824090210481,0x8188002108000a00018060200404040c80010104,0x824090210481,0x0,0x62830100000080400000001000000401006283000110000000400800000800000000c000314190000400040000000100000800200031418800000001000200001000000200017ffa8,0x821090210481,0x0,0x880022001004040180102004020400800100e4,0x0,0x0,0x20002014080000010100020000100000100020214000080010000080040000200100400001001000004004000004010000010042a800101000000400008000400200001000887fda7,0x0,0x821090210481,0x821090210481,0x821090210481,0x800090200481,0x842190220501,0x800090200481,0x842190220501,0x842190220501,0x844190220501,0x804090200481,0x844190220501],
[0x844190220501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_6332 : TreeBound (n := 4) 107 (programCode 0x422b071e7e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x60c090218481,0x424090210481,0x60c090218481,0x0,0x20000001080000001100000008100000014000000110000000440000000900000000c002b00000002c0000002a0000000208002000380008000e000100008000100008001400fdea8,0x80002002000080402000020000814e3,0x10ca89adae7e63ccf3012fc2139f3003cfcc00f3003d398007a73001e9d032843cc79807983cc1e68a8c5,0x4080200481,0x0,0x80002002000080002000020000814e3,0x10d9baec801e6007980408c21b37300003cc007981e679801e67980f33d036503cc00003cde601e64dc35,0x0,0x7980020460007b660012fc00088b000222c0003528b643cc1e601e60f31e62d907980f307983cc1e9cb6,0x0,0x2080002002010080402000020000814e3,0x0,0x844188220501,0x4080200481,0x844188220501,0x4080200481,0x414090210481,0x4002080048000a00018060200404060080402304,0x414090210481,0x0,0x0,0x20020800800804020180102004020400804024e4,0x10ca89adae7e6000f300f311439001e9cc007a73f30079bcc00f3f3003d032843cc79807983cc1e68a8c5,0x20020800801004040180102004020400804024e4,0x0,0x0,0x109cfaec801e60079807987b93900f300003ccf3f30079bcc00f3f3003d027203cc0000799e601e68a8c5],
[0x0,0x3cc00f379803cde6007dc94c04de53008118002d9088b3cc03ccf300f30f31e601e688b07983cc1f6f46,0x2002080080800420018004200402040080502ce4,0x20020800820004800180102004020400804024e4,0x20020800810004400180082004020400806034e4,0x79800f4e6003cde6007f39980798f301e600002d90b643cc0000f300f31e62d9079879807983cc1f7156,0x20020800820004800180102004020400804024e4,0x0,0x20020800840005000180102004020400804024e4,0x424090210481,0x4008080108000a00018060200404060080402904,0x424090210481,0x0,0x638490218481,0x421090210481,0x638490218481,0x20080802001004040180102004020400804030e4,0x0,0x0,0x109cfaec801e60079807987b93900f300003ccf3f30079bcc00f3f3003d027203cc0000799e601e68a8c5,0x0,0x421090210481,0x421090210481,0x421090210481,0x90200481,0x842190220501,0x90200481,0x842190220501,0x90200481,0x844190220501,0x4090200481,0x844190220501],
[0x4090200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_6397 : TreeBound (n := 4) 107 (programCode 0x422b071e7f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x80c0d020c481,0x824090210481,0x80c0d020c481,0x0,0x300000010c0000001300000008400000014000000110000000440000000900000000c002b00000002c0000002a0000000208002000380008000e000100008000100020001000fdea8,0x40001000080002002000080402000020000814e3,0x400090002800a2002001080042001020100814e3,0x804080200481,0x0,0x40001000080002002000080002000020000814e3,0x0,0x0,0x0,0x0,0x40001002080002002010080402000020000814e3,0x0,0x844188220501,0x804080200481,0x844188220501,0x844188220501,0x814090218481,0x0,0x834081218481,0x824084210481,0x834081218481,0x40001000080002002000080002000020000814e3,0x824082210481,0x824084210481,0x824082210481,0x0,0x824084210481],
[0x9002020048000a00011060020404048080100904,0x824084210481,0x0,0x824088210481,0x824084210481,0x824088210481,0x40001000080002002040080002000020000814e3,0x814090218481,0x0,0x0,0x0,0x1e60001e600003cc7983cc0000f307983cc0352800f4e600f4e6001e9cc00000f30000f6cc001e703375,0x0,0x0,0x0,0x79800f4e6003cfcc7983cc01e6f30811bcc01e601e67980799e600f33cc07983cc1e60f708c01e703d95,0x0,0x0,0xf3007d4c001e6f3007d4c0002d9000222c0001e9ccf303cde6003ccf30799e6079879807981e60f4556,0x0,0x0,0x1e61e61e607983cc97e3cc0798f3097e3cc0aea9e601e67981e61e603ccf3000f6cc00f7bf001eacf375,0x0,0x2000088000a00010060000404040080000104,0x0,0x824090210481,0x0,0x830490218481,0x821090210481,0x830490218481,0x0,0x820890210481],
[0x8408008100400808018060200404042080042b04,0x820890210481,0x0,0x821090210481,0x821090210481,0x821090210481,0x820090210481,0x822090210481,0x821090210481,0x822090210481,0x822090210481,0x824090210481,0x0,0x400a1000100880022080082002014020500814e3,0x821090210481,0x40001000201080042080082002000020100814e3,0x0,0x0,0x0,0x0,0x0,0x821090210481,0x821090210481,0x821090210481,0x800090200481,0x842190220501,0x800090200481,0x842190220501,0x842190220501,0x844190220501,0x804090200481,0x844190220501],
[0x844190220501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_6494 : TreeBound (n := 4) 107 (programCode 0x422b071e80) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x7987981e600003cc0003cc00088b000222c0002d90b643cc1e60f300f31e62d9079879807987983cde56,0x0,0x180c00230008c002308004200200401060081ca3,0x421090210481,0x7980001e6003d39800f4e6003d398007b66f30079bcc01e6f3003cc00003cc1e60f33cc01e703d95,0x2000002002080082002000020000814e3,0x798001116000222c000b640004bf00007983cc2d907983cc03ccf300f30f31e601e679807987983cdc46,0x0,0x0,0x0,0x421090210481,0x421090210481,0x421090210481,0x20090210481,0x822090210481,0x421090210481,0x822090210481,0x20090210481,0x8000280082002080082002000020100814e3,0x0,0x43ab200180020800400010000800200002400021c010000010040000080100000200000201000000801000001008000001010043a800100002000100100000800020001001887dea7,0x80002002000080402000020000814e3,0x8000280082002001080042000020100814e3,0x4080200481,0x0,0x80002002000080002000020000814e3,0xf5e0aec83ea6000f307d4c2139f300003cc00f301e679803ccf300f33d027203cc7980799e601e68a8c5,0x0,0x0,0x0,0x0],
[0x0,0x44188220501,0x4080200481,0x44188220501,0x4080200481,0x0,0x7987981e600003cc0003cc00088b000222c0002d90b640001e600000f31e62d9079800007987983cde56,0x798b641e607983cc0003cc00088b000222c0001e6482400111600010231e62d907980f307987983cde56,0x201004048000200300084004200201040081ca3,0x0,0x214082210481,0x10000480002002000080002000020400814e3,0x214082210481,0x0,0x7987981e600003cc0003cc00088b000222c0003528b643cc1e603cc0f31e62d907983cc07987983cde56,0x10000480002002080080002000020400814e3,0x7987981e600003cc0003cc00088b000222c0003528b643cc1e601e60f31e62d907981e607987983cde56,0x0,0x814088218481,0x7987981e600003cc0003cc00088b000222c00025f8b641e61e601e60f31e62d907981e607987983cde56,0x814088218481,0x14080210481,0xf3084e4001e600000003cc2139f300003cc00f3f30079bcc00f3f3003d027203cc00007980001e68a8c5,0x0,0x798b641e600003cc1e63cc00088b000222c0003528b640f31e600000f31e62d9079800007987983cde56,0x20000880002002000080402000020400814e3,0xf300003cc03cc7d4c01e6f30079bcc01e6003d39800f4e6001e9cc00003cc1e60f33cc01e703d95,0x0,0x214082210481,0x20000880002002000080002000020400814e3,0x214082210481,0x0],
[0x0,0x0,0x798b641e607983cc1e63cc00088b000222c0003528b643cc1e601e60f31e62d907981e607987983cde56,0x0,0x814088218481,0x20000880002002000080402000020400814e3,0x814088218481,0x14080210481,0x0,0x0,0x40021000800804020180102004020400808064e4,0x10d03bad901e60000000f311439001e9cc007a73f30079bcc00f3f3003d032843cc00007983cc1e68a8c5,0x40021000801004040180102004020400808064e4,0x0,0x0,0x0,0x0,0x0,0x4002100080800420018004200402040080904ce4,0x40021000840004800180202004020400808044e4,0x4002100081000440018008200402040080a054e4,0x0,0x40021000820004800180202004020400808044e4,0x200010000f000000020000000040000800000004000f700200020000200004004000004010000020040000100100000100000000041e00000200000001010000001002085aba7,0x40021000840005000180202004020400808044e4,0x0,0x180400210008c002308004200200401060081ca3,0x421090210481,0x1000000004000a000200000000200010001000000094000000208000000880000000c000100010000a000400008001000008001000200004000a0001000200001000100008006aba8,0x0,0x798b641e600003cc1e65b200088b0001f530002d90b643cc0f30f300f31e62d9079879807987983cde56,0x40001080000002080082002000020400814e3],
[0x798b641e600003cc1e65b200088b0001f530002d90b643cc0f30f300f31e62d9079879807987983cde56,0x0,0x421090210481,0x421090210481,0x421090210481,0x20090210481,0x822090210481,0x421090210481,0x822090210481,0x20090210481,0xf3084e4001e600000003cc2139f300003cc00f3f30079bcc00f3f3003d027203cc00007980001e68a8c5,0x0,0x180400220008c002308004200200401060081ca3,0x421090210481,0x7980001e6003cfcc00f4e6003d398007b66f30079bcc01e6f3003cc00003cc1e60f33cc01e703d95,0x80002000002002080082002000020000814e3,0x798b641e607983cc0f33cc0005754000fa98002d90b643cc0798f300f30f31e603ccb6407987983cdc76,0x0,0x0,0x0,0x421090210481,0x421090210481,0x421090210481,0x20090210481,0x822090210481,0x421090210481,0x822090210481,0x20090210481,0x0,0x2b3fb015f6dab4b0935aef9292a00067fb67f6acfec056800d2a0006d5df8b3fb0000567f60015a53ff60000593768f880002b40067f60000567fb67f600005684c7f6000005694ffed9fd800015a02e7f60002b3fc59fd800015a02e7f60002b3fc59fd8000567fb67f60000567f60acfec00056d662a44d30acfecadabbec0567f8b3fb000acfecadabbec159fd802b3fb0159fe2dad59f7c3ab,0x421090210481,0x201080042080082002000020100814e3],
[0x40081002001004040180102004020400808050e4,0x0,0x0,0x0,0x0,0x421090210481,0x421090210481,0x421090210481,0x90200481,0x42190220501,0x90200481,0x42190220501,0x90200481,0x44190220501,0x4090200481,0x44190220501,0x4090200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_5518 : TreeBound (n := 4) 107 (programCode 0x422b071e) := by
  conv in programCode _ => reduce
  exact branchFour (k := (3,1)) (by decide +kernel) part100_5519 part100_5520 part100_5521 part100_5522 part100_5715 part100_5780 part100_5861 part100_5862 part100_6039 part100_6040 part100_6041 part100_6106 part100_6267 part100_6332 part100_6397 part100_6494

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_6640 : TreeBound (n := 4) 107 (programCode 0x422b071f61) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x100c0b0220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_6641 : TreeBound (n := 4) 107 (programCode 0x422b071f62) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1024090220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_6642 : TreeBound (n := 4) 107 (programCode 0x422b071f63) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x100c0b0220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_6643 : TreeBound (n := 4) 107 (programCode 0x422b071f64) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x804030080006002080082002040021000814e3,0x410080002002080082002040021000814e3,0x100805008000a002080082002040021000815e3,0x2010080002002080082002040021000814e3,0x2010090080012002080082002040021000816e3,0x0,0x73c0e1220481,0x424084220481,0x73c0e1220481,0x424084220481,0x6340c2220481,0x424084220481,0x6340c2220481,0x0,0x424084220481,0x0,0x424084220481,0x0,0xc64188220501,0x424084220481,0xc64188220501,0x80002002000080002040021000814e3,0x4020110080022002080082002040021000814e3,0x0,0x40202000180202002000880022040021000854e3,0x0,0x40202000280202002001080042040021000854e3,0x2000080002002000080002040021000814e3,0x2012000480012002002080082040021000816e3,0x2000080002002000080002040021000814e3,0x4022000880022002004080102040021000814e3],
[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2008080002002040081002040021000814e3,0x0,0x804021008004200208008200204002100081ce3,0x0,0x4020510000820022080082002040021000814e3,0x10000000402080082002040021000814e3,0x4020510001020042080082002040021000814e3,0x0,0x10080410002080082080082002040021000814e3,0x0,0x10080410004080102080082002040021000814e3,0x0,0x10080410008080202080082002040021000814e3,0x10000000002080082002040021000814e3,0x10010000402080082002040021000814e3,0x10000000002080082002040021000814e3,0x0,0x3cc00f6cc003cfcc00fa980025f8001ed98002d900f33cc007a7300f307983cc1e6798079807983e156,0x10040001002080082002040021000814e3,0x3cc00f6cc003cfcc01023000222c001f530002d901e63cc01e6f301e60f307983cc7980f301e60f4556,0x10080410080082002080082002040021000814e3,0x0,0x40201030000a00022080082002040021000854e3,0x10000000402080082002040021000814e3,0x40201050001200042080082002040021000854e3],
[0x0,0x0,0x0,0x0,0x0,0x804021000804020208008200204002100081ce3,0x10000000002080082002040021000814e3,0x10080410010080402080082002040021000814e3,0x10000000002080082002040021000814e3,0x8000100008000400080001000000001000050010000800010000400400000401000001004000010010000010008000004020000010200000100200000100208593a7,0x0,0x1010040001002080082002040021000814e3,0x0,0x0,0x84c1a1220501,0x86418c220501,0x84c1a1220501,0x844188220501,0x8541c2220501,0x86418c220501,0x8541c2220501,0x0,0x864184220501,0x0,0x864184220501,0x0,0x844188220501,0x844188220501,0x844188220501,0x844188220501,0x0,0x73c0e1220481],
[0x424084220481,0x73c0e1220481,0x4080220481,0x6340c2220481,0x424084220481,0x6340c2220481,0x0,0x424084220481,0x0,0x424084220481,0x0,0x844188220501,0x4080220481,0x844188220501,0x4080220481,0x40201010080202002080082002040021000854e3,0x0,0x84c1a1220501,0x80002002000080402040021000814e3,0x84c1a1220501,0x4080220481,0x2140c2220481,0x80002002000080002040021000814e3,0x2140c2220481,0x0,0x0,0x0,0x0,0x0,0x44188220501,0x4080220481,0x44188220501],
[0x4080220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_6772 : TreeBound (n := 4) 107 (programCode 0x422b071f65) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x10140d0220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_6773 : TreeBound (n := 4) 107 (programCode 0x422b071f66) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10340c1220481,0x1024084220481,0x10340c1220481,0x0,0x1340c1220481,0x424084220481,0x1340c1220481,0x24080220481,0x224082220481,0x424084220481,0x224082220481,0x2000080002002000080002040021000814e3,0x424084220481,0x0,0x424084220481,0x0,0x824088220481,0x424084220481,0x824088220481,0x80002002000080002040021000814e3,0x1024082220481,0x1024084220481,0x1024082220481,0x0,0x4000200010000001040000004100008010000060000000100100000400400001060040000100100000400080000800000101002000001008000004010000008020000010010873227,0x1021084220481,0x0,0x0,0x1020882220481,0x1021084220481,0x1020882220481],
[0x1020080220481,0x1021084220481,0x1021084220481,0x1021084220481,0x1020080220481,0x0,0x0,0x0,0x0,0x1024084220481,0x0,0x1020486220481,0x1021084220481,0x1020486220481,0xf3000408c003db30003cc07981e61e61e607981e9cc1e63cde6003cc1e60f4e60f30000f3f3003cc33b6,0x1020884220481,0x1021084220481,0x1020884220481,0x1020084220481,0x1021084220481,0x1021084220481,0x1021084220481,0x1020084220481,0x1022084220481,0x8002200044000880011048020109070020402b04,0x1022084220481,0xf3000408c003db30003db3000222c001f530001e9cc1e63cde6003cc1e60f4e60f301e600f3798428756,0x1024084220481,0x0,0x10304c9220481,0x1021084220481,0x10304c9220481],
[0xf30007d4c001f530003cc0f303cc3cc0f307981f5379803ce04607983cfcc00089a3799e7e6007985936,0x1020882220481,0x1021084220481,0x1020882220481,0x1020080220481,0x1021084220481,0x1021084220481,0x1021084220481,0x1020080220481,0x0,0x0,0x0,0x0,0x1024088220481,0x0,0x124086220481,0x424084220481,0x124086220481,0x424084220481,0x224084220481,0x424084220481,0x224084220481,0x0,0x424084220481,0x1002020048000a0001406008040c04c080100904,0x424084220481,0x0,0x824084220481,0x424084220481,0x824084220481,0x80002002000080002040021000814e3,0x1024088220481],
[0x0,0x800020080002002040080002040021000814e3,0x0,0x1000040080002002040080002040021000814e3,0x80002002000080002040021000814e3,0x2000080080002002000080002040021000814e3,0x80002002000080002040021000814e3,0x4000100080002002000080002040021000814e3,0x0,0x0,0x3cc03cfcc03cc3cc0408c0002d9000222c000222c1e60f31e603cc1e60f31e60f300798f301e60f4556,0x0,0x0,0x20000800080002002020080002040021000814e3,0x80002002000080002040021000814e3,0x40001000080002002040080002040021000814e3,0x80002002000080002040021000814e3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_6886 : TreeBound (n := 4) 107 (programCode 0x422b071f67) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x10140d0220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_6887 : TreeBound (n := 4) 107 (programCode 0x422b071f68) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x80202010080202002000880022040021000854e3,0x0,0x40002000100001000400000003000000008000600000001100000004000200010600400001000200004000000408000c0001002000001008000004010000008020000010090873227,0x1021084220481,0x0,0x0,0x10308c6220481,0x1021084220481,0x10308c6220481,0x1000084220481,0x1021084220481,0x1021084220481,0x1021084220481,0x1000084220481,0x0,0x0,0x0,0x0,0x80202010080202002001080042040021000854e3,0x0,0xa00030080202002000880022040021000854e3,0x410080002002000080002040021000814e3,0x1200050080202002001080042040021000854e3,0x10080002002000080002040021000814e3,0x2010090080012002002080082040021000816e3,0x10080002002000080002040021000814e3,0x4020110080022002004080102040021000814e3,0x2010080002002000080002040021000814e3,0x0,0x0,0x0],
[0x0,0x0,0x0,0x40201010080202002040081002040021000854e3,0x0,0x80012010080012002002080082040021000816e3,0x80002010080002002000080002040021000814e3,0x80022010080022002004080102040021000814e3,0x0,0x0,0x1021084220481,0x0,0x0,0x10108c2220481,0x1021084220481,0x10108c2220481,0x1000080220481,0x1021084220481,0x1021084220481,0x1021084220481,0x1000080220481,0x0,0x0,0x0,0x0,0x0,0x10084a4220481,0x1021084220481,0x10084a4220481,0x8004201008004020200808020204002100081ce3,0x10108c4220481,0x1021084220481],
[0x10108c4220481,0x1000084220481,0x1021084220481,0x1021084220481,0x1021084220481,0x1000084220481,0x1042184220501,0x0,0x1042184220501,0x0,0x0,0xf30007d4c26193900081183cde6018b61184032c6f31e603cde74b566cc79800fa9800f3f3001e703375,0x1021084220481,0xf30007d4c358f770002d90799e604a23a107c5900f33cc0799e7c33c5ccf3001ed9800f3f3001e703885,0xf30007d4c003db300079807983cc3cc0f307981ed9f9801e7f5303cc3cfcc0008929f9adae6007985426,0x10308c6220481,0x1021084220481,0x10308c6220481,0x1000084220481,0x1021084220481,0x1021084220481,0x1021084220481,0x1000084220481,0x0,0x0,0x80002008040001002000080002040021000814e3,0x0,0x0,0x10084a4220481,0x1021084220481,0x10084a4220481,0x0],
[0x10108c4220481,0x1021084220481,0x10108c4220481,0x1000084220481,0x1021084220481,0x1021084220481,0x1021084220481,0x1000084220481,0x1042184220501,0x0,0x1042184220501,0x0,0x0,0x0,0x1021084220481,0x0,0xf3000f6cc003db30007980f303cc3cc0f307981f5379803ce046079879bcc00089a3799e9cc007985936,0x10108c2220481,0x1021084220481,0x10108c2220481,0x1000080220481,0x1021084220481,0x1021084220481,0x1021084220481,0x1000080220481,0x0,0x0,0x0,0x0,0x0,0x804030080006002020080802040021000814e3,0x10080410080082002020080802040021000814e3],
[0x100805008000a002020080802040021000815e3,0x0,0x2010090080012002020080802040021000816e3,0x80000010080002002020080802040021000814e3,0x4020110080022002020080802040021000814e3,0x0,0x804021008004200202008080204002100081ce3,0x80000010080002002020080802040021000814e3,0x10080410080082002020080802040021000814e3,0x0,0x0,0x0,0x40201010080202002020080802040021000854e3,0x0,0x0,0xf379805b3e6016cfd4c001f53079fd4c21d0e0f31e603cde703233cc79800fa9800f3f3001e703375,0xf37980f31e600f37d4c0002d9000222c00020463cc1e61e601e63cc1e61e6079800097e0001e61556,0x1e67981119cc025f83cc001f5307a76cc02d900f33cc0799e709c83ccf3001ed9800f3f3001e703885,0x1e600007983cc0000f307983cc02d900003cc0001e6f3003ccf3001ed9800f3f3001e703885,0x0,0x0,0x0,0x0,0x0,0x3cc079bcc01e63cc07d4c0002d9000222c00020463cc1e61e601e63cc1e61e60f3001e7e6007983e156,0x0,0x0,0x0,0x0,0x0,0x0,0x0],
[0x804030080006002040081002040021000814e3,0x410080002002040081002040021000814e3,0x100805008000a002040081002040021000815e3,0x1010080002002040081002040021000814e3,0x2010090080012002040081002040021000816e3,0x10080002002040081002040021000814e3,0x4020110080022002040081002040021000814e3,0x2010080002002040081002040021000814e3,0x804021008004200204008100204002100081ce3,0x0,0x10080410080082002040081002040021000814e3,0x0,0x0,0x0,0x40201010080202002040081002040021000854e3,0x0,0x0,0xf307985b21e616c8b640002d90798b6421b4a2c01e6f301e72fc03cc79800fa9800f3f3001e703375,0x0,0xf30799116d4a25f92fc0002d9079b8f421b66a601e7e601e7c7a03cc79800fa9800f3f3001e703375,0x1e600007983cc0000f307983cc02d900003cc0001e6f3003ccf3001ed9800f3f3001e703885,0x0,0x0,0x7980007b66000fa983cc0000f307983cc21b280001e60001e6f3003cc79800fa9800f3f3001e703375,0x0,0x0,0x3cc079bcc01e63cc07d4c0002d9000222c000222c1e60f31e603cc1e60f31e60f300798f301e60f4556,0x0,0x0,0x0,0x0,0x7983cc1e62d903cc7983cc0f30f30b643cc01e67980799e601e76c803cde6003d39800f3f3001ee9bd95],
[0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_7080 : TreeBound (n := 4) 107 (programCode 0x422b071f69) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1024090220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_7081 : TreeBound (n := 4) 107 (programCode 0x422b071f6a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10304d0220481,0x1021090220481,0x10304d0220481,0x0,0xf379805b3e6017a43803cde6016cfd4c5e91d3001e9cc01e6f3003cc79800fa9800f3f3001e703375,0x0,0x1e67981119cc026c5080799e6044676cc02d9f3003cfcc01e6f3003ccf3001ed9800f3f3001e703885,0x1040041001004040180002000200400040000e4,0x0,0x0,0x1e679807b66000fb1180799e601ed983cc01e6f30079bcc01e6f3003cde6003d39800f3f3001e703d95,0x0,0x3cc7980f4e6003d41180f31e603d3983cc01e6f30079bcc01e6f3003cde6003d39800f3f3001e703d95,0x0,0x40041001004040180002000200400040000e4,0x0,0x0,0x20040801001004040180102000220400044028e4,0x40041001004040180002000200400040000e4,0x40041001001004040180202000240400048048e4,0x1020890220481,0x0,0x1021881220481,0x1021084220481,0x1021881220481,0x0,0x1021082220481,0x1021084220481,0x1021082220481,0x1021084220481,0x1021084220481],
[0x1021084220481,0x1021084220481,0x1021084220481,0x1021088220481,0x8008200100400808014072080048460008402904,0x1021088220481,0xf3001e9cc01e6f3001e601e601e7e601e61e60222c003db307983cc003cc20460f30798001ed984c0556,0x1020890220481,0x0,0x1022081220481,0x1020084220481,0x1022081220481,0x0,0x1020882220481,0x1020084220481,0x1020882220481,0x1020080220481,0x1020084220481,0x1020084220481,0x1020084220481,0x1020080220481,0x0,0xf3001e9cc01e6f3001e603cc01e6f301e63cc02046007b660f301e6007983ea60f30798003db307d6156,0x0,0xf3001e9cc01e6f3001e603cc01e6f301e63cc0222c007a7307983cc007983ea60f30798003d3984c0556,0x1021090220481,0x1021090220481,0x1021090220481,0x1020090220481,0x1022090220481,0x0,0x121890220481],
[0x421090220481,0x121890220481,0x0,0x221090220481,0x40800810400088001806320040c042080042b04,0x221090220481,0xf31e603cde600f31e67980025f8001ed98002d900f33cc001f5300f30799e60f30798079801e610856,0x421090220481,0x421090220481,0x421090220481,0x421090220481,0x821090220481,0x421090220481,0x821090220481,0x421090220481,0x1022090220481,0x0,0x122090220481,0x420090220481,0x122090220481,0x0,0x0,0x799e60799e600799e6f3000222c001f530002d901e63cc003db301e60f31e60f307980f3003d0deb56,0x0,0x1e63cc0798f300f31e7e600044580010230002d9000f6cc2dcdb301e63cc1e616c87a73f3003cc20276,0x420090220481,0x420090220481,0x420090220481,0x20090220481,0x822090220481,0x420090220481,0x822090220481],
[0x20090220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_7178 : TreeBound (n := 4) 107 (programCode 0x422b071f6b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1024090220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_7179 : TreeBound (n := 4) 107 (programCode 0x422b071f6c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x80202010100a00022080082002040021000854e3,0x1021090220481,0x80202010201200042080082002040021000854e3,0x0,0x0,0x0,0x408c00111600025f9e6102300044583cc01e6f30079bcc01e6f3003cde6003d39800f3f3001ee9bd95,0x1080042001004040180002000200400040000e4,0x0,0x0,0x0,0x0,0x0,0x0,0x80042001004040180002000200400040000e4,0x0,0x7980001e6000f6cc00f301e63cc07987982d900003cc00088b0001e601e60004458000f300001a96,0x20080802001004040180102000220400044030e4,0x80042001004040180002000200400040000e4,0x40081002001004040180202000240400048050e4,0x0,0x80006008402004082000880022040021000814e3,0x10308c6220481,0x8000a008402008082001080042040021000815e3,0x0,0x10108c2220481,0x10308c6220481,0x10108c2220481,0x10108c2220481,0x10308c4220481,0x10308c6220481],
[0x10308c4220481,0x10108c2220481,0xf307983cc03ccf3000f301e6f301e6f3001e6f31e603cde600f31e603ccf3001e9cc007a73001e88e655,0x80082000402080082080080402040021000814e3,0x80202010402200082040081002040021000854e3,0x80002000402000082080080002040021000814e3,0x0,0xf30000b64296bb90a5ab1bcc01e6fd5b045822ac60f4e6003ea6000f6cc79800fa9800f3f3001e703375,0x1021084220481,0xf30000b643cbf0d0f2f869e601e7f52fffffffe1a0f4e600f4e6001e9cc79800fa9800f3f3001e703375,0x0,0x1021082220481,0x1021084220481,0x1021082220481,0x1021084220481,0x1021084220481,0x1021084220481,0x1021084220481,0x1021084220481,0x1021088220481,0x0,0x1021088220481,0x0,0x0,0x80006008804004102000880022040021000814e3,0x10308c6220481,0x8000a008804008102001080042040021000815e3,0x0,0x10108c2220481,0x10308c6220481,0x10108c2220481,0x10108c2220481],
[0x10308c4220481,0x10308c6220481,0x10308c4220481,0x10108c2220481,0x0,0x0,0x80202010804200102040081002040021000854e3,0x0,0x0,0x0,0x1000084220481,0x0,0x0,0x10108c2220481,0x1000084220481,0x10108c2220481,0x1000080220481,0x1000084220481,0x1000084220481,0x1000084220481,0x1000080220481,0x0,0x0,0x0,0x0,0x1021090220481,0x1021090220481,0x1021090220481,0x1000090220481,0x0,0x14a1b0220501,0xc62190220501],
[0x14a1b0220501,0x0,0x2010094020010802080082002040021000816e3,0x80000004020000802080082002040021000814e3,0x4020114020020802080082002040021000814e3,0x80100804020100802080082002040021000834e3,0x462190220501,0xc62190220501,0x462190220501,0x842190220501,0x842190220501,0x842190220501,0x842190220501,0x42190220501,0x0,0x0,0x421090220481,0x0,0x0,0x221090220481,0x0,0x221090220481,0xf33cc0799e600f33ccf3000408c000fa98002d9000f6cc26541301e63cc1e612fc7a73f3003cc1fd66,0x421090220481,0x421090220481,0x421090220481,0x90220481,0x800090220481,0x90220481,0x800090220481,0x90220481,0x0],
[0x14a1b0220501,0xc62190220501,0x14a1b0220501,0x2008040001002080082002040021000814e3,0x2010098040011002080082002040021000816e3,0x0,0x4020118040021002080082002040021000814e3,0x0,0x462190220501,0xc62190220501,0x462190220501,0x842190220501,0x842190220501,0x842190220501,0x842190220501,0x42190220501,0x0,0x14a5b0220501,0x400090220481,0x14a5b0220501,0x0,0x0,0x0,0x0,0x1e67980799e600f33cde600044580010230002d9000f6cc2dcdb303cc3cc1e616c87a74e6003cc20276,0x400090220481,0x400090220481,0x400090220481,0x90220481,0x842190220501,0x90220481,0x842190220501],
[0x90220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_7340 : TreeBound (n := 4) 107 (programCode 0x422b071f6d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1044190220501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_7341 : TreeBound (n := 4) 107 (programCode 0x422b071f6e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1340d0220481,0x424090220481,0x1340d0220481,0x1e60f307983cc0000f307983cc21b373001e9cc01e6f3003cc79800fa9800f3f3001e703375,0x224090220481,0x0,0x624081220481,0x424084220481,0x624081220481,0x424084220481,0x424082220481,0x424084220481,0x424082220481,0x0,0x424084220481,0x420008408000a0001104e020041c48008100904,0x424084220481,0x0,0x424088220481,0x424084220481,0x424088220481,0x80002002000080002040021000814e3,0x224090220481,0x0,0x0,0x0,0x1e60001e61e612fc7983cc0000f307983cc21b2800f4e600f4e6001e9cc79800fa9800f3f3001e703375,0x1e60f307983cc0000f307983cc02d900003cc0001e600003ccf3001ed9800f3f3001e703885,0x0,0x0,0x1e679807b660f30811bcc01e6f307983cc01e601e67980799e600f33cde6003d39800f3f3001e703d95],
[0x0,0x0,0xf3f3003db3000f3f33cc0002d9000222c0001e9cc079bcde6003cc07983ea600f3798003cde60f4556,0x0,0x0,0x0,0x420010408000a00014062080084462010804104,0x1e60f307983cc0000f307983cc21b29e601e7e601e63cc03cc79800fa9800f3f3001e703375,0x420010408000a00014062100084462010804104,0x424090220481,0x0,0x620490220481,0x421090220481,0x620490220481,0x0,0x420890220481,0x102002040040080801804b200101642020040b04,0x420890220481,0x0,0x421090220481,0x421090220481,0x421090220481,0x420090220481,0x422090220481,0x421090220481,0x422090220481,0x420090220481,0x424090220481,0x0,0x2001000008004000020008000020008004202000110000000400010000800000000c000210110000040040000000100000100420221010080000000001200000200000200017ffa8,0x421090220481,0x1e60001e61ecb8032d73403cc00044729409b9dc3001e9cc01e6f3003cc79800fa9800f3f3001e703375],
[0x0,0x0,0x0,0x0,0x0,0x421090220481,0x421090220481,0x421090220481,0x90220481,0x802090220481,0x90220481,0x802090220481,0x90220481,0x804090220481,0x4090220481,0x804090220481,0x4090220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_7422 : TreeBound (n := 4) 107 (programCode 0x422b071f6f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1044190220501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_7423 : TreeBound (n := 4) 107 (programCode 0x422b071f70) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x14c1b0220501,0x0,0xd685b0220501,0x421090220481,0xd685b0220501,0x400000002002080082002040021000814e3,0x0,0x0,0x0,0x0,0x421090220481,0x421090220481,0x421090220481,0x400090220481,0xc62190220501,0x421090220481,0xc62190220501,0x400090220481,0x14c1b0220501,0x1e60f307983cc0000f307983cc21b373001e9cc01e6f3003cc79800fa9800f3f3001e703375,0x0,0x25c1e1220501,0x2080090080082002010080402040021000814e3,0x25c1e1220501,0x2140c2220481,0x2140c2220481,0x2000080080002002000080002040021000814e3,0x2140c2220481,0x0,0x204009008004200200808020204002100081ce3,0x2000080080002002080080002040021000814e3],
[0x2080090080082002010080402040021000814e3,0x0,0x2541c8220501,0x2000080080002002010080002040021000814e3,0x2541c8220501,0x204080220481,0x0,0x4225128980226002000880022040021000854e3,0x80002002000080402040021000814e3,0x4229148a8022a002001080042040021000855e3,0x80002002000080002040021000814e3,0x0,0x80002002000080002040021000814e3,0x0,0x0,0x0,0x7b660079f98007b663cc0002d9000222c0001e9cc0f33cde6003cc0f307b66003d398007987983e156,0x80002002010080402040021000814e3,0x0,0x80002002020080802040021000814e3,0x80002002000080002040021000814e3,0x80002002040081002040021000814e3,0x80002002000080002040021000814e3,0x0,0x25c1e1220501,0x4000100080002002000080402040021000814e3,0x25c1e1220501,0x2140c2220481,0x2140c2220481,0x4000100080002002000080002040021000814e3,0x2140c2220481,0x0],
[0x404011008004200200808020204002100081ce3,0x0,0x4080110080082002010080402040021000814e3,0x0,0x2541c8220501,0x4080110080082002010082402040021000814e3,0x2541c8220501,0x204080220481,0x0,0x0,0x0,0x7983cc1e61e60f30b643cc0f30f307983cc01e6003d39800f4e6001e9cde6003d39800f3f3001ee9bd95,0x1e60f307983cc0000f307983cc02d900003cc0001e600003ccf3001ed9800f3f3001e703885,0x0,0x0,0xf307987b69db307af04c001f5307a76cc02d900f33cc0799e600f33ccf3001ed9800f3f3001e703885,0x0,0x0,0xf4e6003d39800f4e63cc0002d9000222c0001e9cc079bcde6003cc07983ea600f3798003cde60f4556,0x0,0x0,0x0,0x420010808000a00014062080084462010804104,0x1e60f307983cc0000f307983cc21b29e601e7e601e63cc03cc79800fa9800f3f3001e703375,0x420010808000a00014062100084462010804104,0x0,0x4685b0220501,0x421090220481,0x4685b0220501,0x0,0x8010210002010082080082002040021000816e3,0x8000200080000002080082002040021000814e3],
[0x8020210004020102080082002040021000814e3,0x0,0x421090220481,0x421090220481,0x421090220481,0x400090220481,0x462190220501,0x421090220481,0x462190220501,0x400090220481,0x0,0x0,0x421090220481,0x0,0x0,0x0,0x3cde603cc79803cde6001e601e7e601e61e602d90079bcc1e60f3007983cde6000811803cc00f3fbed6,0x798079bcdebc2ca898003cc1e61edaec83ced9f3003cfcc01e6f3003ccf3001ed9800f3f3001e703885,0x0,0x421090220481,0x421090220481,0x421090220481,0x400090220481,0xc62190220501,0x421090220481,0xc62190220501,0x400090220481,0x0,0x4685b0220501,0x421090220481,0x4685b0220501,0x10080402010082002080082002040021000814e3],
[0x10010410002010082080082002040021000816e3,0x0,0x10020410004020102080082002040021000814e3,0x0,0x421090220481,0x421090220481,0x421090220481,0x400090220481,0x462190220501,0x421090220481,0x462190220501,0x400090220481,0x0,0x9485b0220501,0x421090220481,0x9485b0220501,0x0,0x0,0x0,0x0,0x0,0x421090220481,0x421090220481,0x421090220481,0x90220481,0x842190220501,0x90220481,0x842190220501,0x90220481,0x844190220501,0x4090220481,0x844190220501],
[0x4090220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_6639 : TreeBound (n := 4) 107 (programCode 0x422b071f) := by
  conv in programCode _ => reduce
  exact branchFour (k := (3,0)) (by decide +kernel) part100_6640 part100_6641 part100_6642 part100_6643 part100_6772 part100_6773 part100_6886 part100_6887 part100_7080 part100_7081 part100_7178 part100_7179 part100_7340 part100_7341 part100_7422 part100_7423

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_7585 : TreeBound (n := 4) 107 (programCode 0x422b072071) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10c090200481,0x0,0x4002000110000000400010000800000000c002000110000000400010000800000000c000300010000400040000000100001000200020010800000002000200002000000200017ffa8,0x121090210481,0x0,0x800022000002002080082002000020000814e3,0x120890208481,0x0,0x120890208481,0x0,0x121090210481,0x121090210481,0x121090210481,0x120090200481,0x122090220481,0x121890218481,0x122090220481,0x120090200481,0x10c090200481,0x0,0x10c081200481,0x800020080002002000080402000020000814e3,0x10c081200481,0x104080200481,0x114082208481,0x800020080002002000080002000020000814e3,0x114082208481,0x0,0x0,0x0,0x0],
[0x0,0x14c0c8204481,0x820020880082002004080402004020100814e3,0x14c0c8204481,0x104080200481,0x0,0x1140c1204481,0x114084210481,0x1140c1204481,0x114080200481,0x114082208481,0x114084210481,0x114082208481,0x0,0x114084210481,0x810020480002002080080002000020000814e3,0x114084210481,0x0,0x1140c8220481,0x114086218481,0x1140c8220481,0x114080200481,0xf30003cc7983defc00408c0002d9000222c0002d901e63cc1e60f301e60f31e603cc7980f3003cfebb56,0x0,0x1140c1204481,0x114084210481,0x1140c1204481,0x114080200481,0x114082208481,0x114084210481,0x114082208481,0x0],
[0x114084210481,0x0,0x114084210481,0x0,0x1140c8220481,0x114086218481,0x1140c8220481,0x114080200481,0x0,0x0,0x4023000800804020180202008040401000844e4,0x0,0x4023000801004040180202008040401000844e4,0x0,0x0,0x0,0x0,0x80004140400020002000101000000100000000034040000200000000800800000c000000010000a020400020001000010000800200004000a02020002000020000040002052ba8,0x402222080800420018004200804040100180ce4,0x0,0x4022420810004400180082008040401002814e4,0x16e660f303cc1e600007f399807980001e600002d90b736cc0000f301e61e62dccfcc7980f3001e6110c6,0x0,0x100008140400020002000100000000104000000094040000200000000900000000c000000010000a020400020001000010001000200004000a0202000200002000004000206aba8,0xf30007983cc1f53f307a73000222c001f530002d901e63cc001f5301e60f31e603cc7980f3001e610856,0x0,0x1204d0204481,0x121090210481,0x1204d0204481,0x0,0x120890208481,0x840021080000002080082002000020000814e3],
[0x120890208481,0x0,0x121090210481,0x121090210481,0x121090210481,0x120090200481,0x122090220481,0x121890218481,0x122090220481,0x120090200481,0xf3001e63cc1e6f30f4e9cc0002d9000222c0002d901e63cc1e60f301e60f31e603cc7980f301e60f4556,0x0,0x1204d0204481,0x121090210481,0x1204d0204481,0x880022000002002080082002000020000814e3,0x120890208481,0x0,0x120890208481,0x0,0x121090210481,0x121090210481,0x121090210481,0x120090200481,0x122090220481,0x121890218481,0x122090220481,0x120090200481,0x0,0x108490200481,0x121090210481,0x108490200481],
[0x10082022001004040180202008040401002010e4,0x0,0x0,0x0,0x0,0x121090210481,0x121090210481,0x121090210481,0x100090200481,0x1dcd6500ee6b2f73597b9ce450446acab36e6b2f7359401dcddc359401dcd65ee6b45cd65f6d469116f9ee6b2800003b9acbdcd6559682f1dcd6c7359400001dcd660d2829a14b47735b1cd650ee6b36e6b2800003b9ad8e6b28ee6b6b4a0902b222e6b28773594773597bbb642eaa,0x0,0x1dcd65ee6b68f5b402d65fd51e1f3595dcd65ee6b2a540be477359400007735a30ebebb52ca0ef59cec2d8e9b963b55943b9ca6d6500773d075940773770d6503b9b41359403b9ca6d6500773d075ed683e047ffb5a1aa6b28000077359401dcddc35940773682747fc793b99,0x100090200481,0x1440d0204481,0xf300f31e60f311160f33cc0002d9000222c0002d901e63cc1e60f301e60f31e603cc7980f30f3097f556,0x1440d0204481,0x104090200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_7730 : TreeBound (n := 4) 107 (programCode 0x422b072072) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x400020000002080004000200000c008000000060000000100100000600000001060040000100100000400400000801000001004000001010000004000004008100000010010873227,0xc00030000804020180202008040401000100e4,0x0,0x1dcf41d6500ee6b280000eeaa7c76a00ee6b280000ef002af9000ee6b6754b23aca1dcd65000003ba2b48ed4077359400000ef952fced6501dcddc35940ee6d04d6501dcddc359403b9ca6d6500773594000003bb89782cd82cd65000003b9aca0ee6b9f359400000ee7101c1d6679,0x0,0x0,0x0,0x0,0xee6c166b2877360b35940ee6c166b281dcd82cd6501dcd836267f9000202172c0d65f5de8140001dcd65773597d77a05000059682f3b9ad173598a81b9f7a053b9ad1735940003d77a050ee6b45cd69a81b891ffa2e6c1847fe5ee6b2f735a2e6b28773594000f5e245a3333a,0x0,0x1dcd73e6b2877360b35940ee6c166b281dcda09aca01dcda12fcd703597b9acbdcd65f5de8140001dcd65773597d77a05000059682f3b9ad17359a84f1ef7a053b9ad1735940003d77a050ee6b45cd69a81b9093536e6c1847fe5ee6b2f735a2e6b28773594000f5e245ba169a,0x0,0x0,0x0,0x0,0x0,0x21000000084000000108000000108006002000110000000400010000880000000c000300110000400040000001100001000200030010800040002000200002000000220017ffa8,0xf5de8140003e660d54d65ee6b2bb9acbe08ffca0001dcd6500003b9acc098a7666b2fea8ed40001dcd65773597d77a05000059683065a13aa8eda84ee35cd653b9ad1735940001faa3b50ee6b45cd68b9acaee6b3e5a135126a6dcd657735a2e6b28773594000fd51e539a07a,0x21000000084000000110000000110006002000110000000400010000880000000c000300110000400040000001100001000200030010800040002000200002000000220017ffa8,0xc00030001004040180202008040401000100e4,0x0,0x408890208481,0x420890208481,0x408890208481,0x0,0x0,0x0,0x0,0x0,0x420890208481,0x420890208481],
[0x420890208481,0x0,0x440890218481,0x420890208481,0x440890218481,0x21000000084000000110000000110006002000118008000440000000880000000c000300110000400040000001100001000200030010800040002000200002000000220017ffa8,0x0,0xf37983cc1e6016cf98003cde600fa98408c2d9000f6cc003ea6000f6cfcc001e60f30f6cc001e703885,0x0,0x44580005b200016c80079807987980799e6029c91a45f844583cc1e61e616d1f7800088b0001e61df6,0x0,0x0,0x0,0x0,0xc00030002004080104020108040021000904e4,0x0,0x0,0x180828420222,0x0,0x0,0x180828420222,0x0,0x180828420222,0x109cf983cc1e6003d398007b939008118003cc7a730079bcc007a73003cfd57e3cc0f30408c001e64dc35,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x44580005b200016c8007980799e60079bcc029c91a46eb07980011161e616d1f781e60f30001e61df6],
[0xc00030004004100104020108040021000904e4,0xc00030004004100100000028040201000100e4,0xc0003000200410010804020902002100090ca4,0x180828420222,0xc00030004004100110080408040021000914e4,0x0,0x180828420222,0xc00030004004100140202008040405000100e4,0x180828420222,0xc00030000804020180202008040401000100e4,0xc00030008004200180042008040401001108e4,0x0,0x409090210481,0x421090210481,0x409090210481,0x0,0x0,0x810020440805000180206008040401008142e4,0x0,0x820020840805000180206008040401008144e4,0x421090210481,0x421090210481,0x421090210481,0x421090210481,0x441090210481,0x421090210481,0x441090210481,0x421090210481,0xc00030010004400180082008040401002110e4,0x0,0x50a0b0220481,0x422090220481],
[0x50a0b0220481,0x0,0x0,0x810020440805000180206008040401008142e4,0x400000100002000404000000800c000010040020000100000100400200001000060040000100100000400400000801000001004000001010000004004000008100000010010873227,0x820020840805020180206008040401008144e4,0x422090220481,0x422090220481,0x422090220481,0xc62190230501,0xc42190230501,0x422090220481,0xc42190230501,0xc62190230501,0x0,0x409890218481,0x421090210481,0x409890218481,0x0,0x0,0x810020420004800180006008040401008142e4,0x0,0x820020820004800180006008040401008144e4,0x421090210481,0x421090210481,0x421090210481,0x421090210481,0xc43190230501,0x421090210481,0xc43190230501,0x421090210481,0x0],
[0x50a0b0220481,0x422090220481,0x50a0b0220481,0x0,0x0,0x0,0x0,0x0,0x422090220481,0x422090220481,0x422090220481,0xc62190230501,0xc42190230501,0x422090220481,0xc42190230501,0xc62190230501,0x0,0x408090200481,0x420090200481,0x408090200481,0x0,0x0,0x810020440005000180006008040401008142e4,0x0,0x820020840005000180006008040401008144e4,0x420090200481,0x420090200481,0x420090200481,0x400090200481,0x441090210481,0x420090200481,0x441090210481],
[0x400090200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_7891 : TreeBound (n := 4) 107 (programCode 0x422b072073) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x16c800111600025f83cc0000f307983cc035373001e9cc01e6f3003cc00000f30000f6cc001e703375]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_7892 : TreeBound (n := 4) 107 (programCode 0x422b072074) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x10c081200481,0x0,0x10c081200481,0x10c081200481,0x1140c1204481,0x820020880022002000880022000820020814e3,0x1140c1204481,0x0,0x0,0x0,0x0,0x0,0x1440c1204481,0x400321540000401000001000400004000040002154100000100400000041000001000002010000008010000010040000010100400300100000400100001000400000001000887dda7,0x1440c1204481,0x104081200481,0x0,0x4000180002002000080402000020000814e3,0x0,0x8000280002002000080402000020000814e3,0x80002002000080402000020000814e3,0x81040000204000000800000000840000000100008200400000001000004000000008010400020000000100008000100400000081040000200000001000800001002086aba7,0x80002002000080402000020000814e3,0x20000880002002000080402000020000814e3,0x0,0x0,0x109d04e4001e600000003cc2139f300003cc00f409c87980000f307983cfcc003cc00007980001e68a8c5,0x0,0x0,0x100004080002002000080402000020000814e3],
[0x80002002000080402000020000814e3,0x200008080002002000080402000020000814e3,0x80002002000080402000020000814e3,0x0,0x10c081200481,0x0,0x10c081200481,0x10c081200481,0x1140c1204481,0x20040880022002001080042000020040814e3,0x1140c1204481,0x0,0x0,0xf3636e4001e60001e603cc2139f300003cc00f3003d398007a73001e9cfcc003cc00007980001e68a8c5,0x0,0x0,0x1440c1204481,0xf372d7340001e600f303cc21a44300003cc0079803d398003d39801e9cfcda97cc00003cc0001e64dc35,0x1440c1204481,0x104081200481,0x0,0xc080200481,0x0,0xc080200481,0x4080200481,0x14080200481,0x80002002000080002000020000814e3,0x14080200481,0x0,0x0,0xf3084e4001e600000003cc2139f300003cc00f3f3007980000f300003cfcc003cc00007980001e68a8c5,0x0],
[0x0,0x44080200481,0x4080200481,0x44080200481,0x4080200481,0x0,0x20c082208481,0x0,0x20c082208481,0x214082208481,0x214082208481,0x0,0x214082208481,0x0,0x0,0x0,0x0,0x0,0x244082208481,0x0,0x244082208481,0x214082208481,0x0,0x4000180002002000080002000020000814e3,0x0,0x8000280002002000080002000020000814e3,0x80002002000080002000020000814e3,0x10000480002002000080002000020000814e3,0x80002002000080002000020000814e3,0x20000880002002000080002000020000814e3,0x0,0x0],
[0x109d04e4001e600000003cc2139f300003cc00f409c87980000f300003cfcc003cc00007980001e68a8c5,0x0,0x0,0x100004080002002000080002000020000814e3,0x80002002000080002000020000814e3,0x200008080002002000080002000020000814e3,0x80002002000080002000020000814e3,0xf5e0983cc1e600081183cc2139f307983cc007981e679801e67980f33cfd57e3cc0f30408c001e64dc35,0x0,0x0,0x0,0x0,0x0,0x0,0x1400050002004080104020108040021000a05e4,0x7983cc1e60000798003cc0001ed98003ced900003cc0001e602d93cfcc001e60000f6cc001e703885,0x1400050004004100104020108040021000a05e4,0x1303983cc1e6003d39800f30f30f379800f307983cc3cc0f307992fc3cfcc001e63cc0408c001e64d3c5,0xc0005000800420010204010902001100190ca4,0x10d9b983cc1e60079f9803ce1b283d39801e60799a947981e607983cc3d036503cc3cc0408c001e64dc35,0xc0005000800440010204010a02001100391ca4,0x7983cc1e6000079807980001e679807982d900003cc0001e61e603cfcc001e60000f6cc001e703885,0xf307983cc1e600007983cc21390007983cc007a730079800007980003cfcc003cc0000408c001e64dc35,0x1c7a7983cc1e600007981e621391e67980f3007b47a07980000799e603d31e803cc0000408c001e64dc35,0xf307983cc1e600007983cc21390007983cc007a730079800007980003cfcc003cc0000408c001e64dc35,0x0,0x4000200010000800040002000001008000000060000000100100000600000001060000400100001000400004000800010001004000001010000004000004008100000010010873227,0x0,0x0,0x44580005b200025f8000f307980f31e6079827e3eec0f303cc0011161e613078261e60f30001e61d36,0x0,0xa000000028000000220000000280000004000020010000080100000800100000880004000200010000800000100008100008000001020001000200004010200000040002513a8],
[0x3d3983cc1e6003d398003cde601ed98003ced903cc3cc0f31e603cc3cfcc001e60f30f6cc001e703885,0x7983cc1e6003d398000000000079800002d903cc3cc0f31e603cc3cfcc001e60000f6cc001e703885,0x3d3983cc1e6013039800f30f30f379800f307983cc3cc3cc07983cc3cfcc001e63cc0408c001e64d3c5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xfa983cc1e6000fa980003ea60016c80003f9900f33cc03cde702303cfcc001e60f30f6cc001e703885,0x180424420222,0x11158683cc1e60009f78001151cd016c800079fa90e6f9801e67984bf3d045437cc4bf0408c001e64dc35,0x180424420222,0x0,0x0,0x180424420222,0xc0005000200410010804020902002100090ca4,0x180424420222,0x181024620a62,0x0,0x181024620a62,0x0,0x0,0x0,0x0,0x0,0x400020001000080004000200000c008000000060000000100100000600000001060002000100008000400010000800020001004000001010000004000004008100000010010873227,0x180428420222,0x0,0x180428420222],
[0x0,0x180828420222,0x180428420222,0x180828420222,0x180428420222,0x18102c620a62,0x0,0x18102c620a62,0x0,0x0,0x0,0x0,0x0,0x0,0x180424420222,0xf371e83cc1e6000079800114390016c800079fa734c69800007a731e9cfcc003cc0000408c001e64dc35,0x180424420222,0xa000000028000000220000000280000000400030000000080010000900000000808004000020010000200240000200100008000000220008004200000008200000040002513a8,0x0,0x180424420222,0x1400050004004100110080408040021000a15e4,0x180424420222,0x181024620a62,0x0,0x181024620a62,0x7983cc1e6000079807980001e679807982d900003cc0001e711603cfcc001e60000f6cc001e703885,0x0,0x0,0x0,0x0,0x80c0a8220481,0x740021600100001004000200004000008040002160100000100400020001000000802000010008000040010000020010000100740000101000000400400000210000001000487fca7],
[0x80c0a8220481,0x844188220501,0x8140c8220481,0x20000800080002002020080802020020000814e3,0x8140c8220481,0x0,0x1e601e9cc01e697e01e9cc00f3f307983cc00799e603cde600799e603cfcc001ef7e00408c001e64d3c5,0x1e7e6007b66001e7e9cc0002d9000222c0001e611160f397e00011160f31e603cc1e702300041823b6,0x0,0x80400000201000002010000002010040000000900000000c0000000900000000800220000000410000800200000004100008000001020008000200004000200000040002593a8,0x844188220501,0x804088220481,0x844188220501,0x844188220501,0xf307983cc1e600007983cc2139f307983cc007a730079800007a73003cfcc003cc0000408c001e64dc35,0x200016000800040002000080008000400000001000083004000200010000040008000040040000200200001000200001004000000416000002000000010100000010020852ba7,0xf307983cc1e600007983cc2139f307983cc007a730079800007a73003cfcc003cc0000408c001e64dc35]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_8101 : TreeBound (n := 4) 107 (programCode 0x422b072075) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x811800204600081183cc001f53079fd4c0370e00f4e6003ea6000f6cc003ccf300f3f6cc3cde703375,0x811800204600081183cc0000f307983cc01e6000079bcc01e60f303cc3cc03ccf300f6cc001e703d95,0x811800204600081183cc003db307983cc01e6003d39800f4e6001e9cc0079bcc01e6f6cc001e722395,0x0,0x20c080200481,0x0,0x20c080200481,0x204080200481,0x214080200481,0x2000080080002002000080002000020000814e3,0x214080200481,0x0,0x0,0xf3001e6f301e60f301e9cc0002d9000222c0001e6204600097e00020460f31e603cc1e60f307984c0556,0x0,0x0,0x244080208481,0xf300f30f30f307980f33cc0002d9000222c0001e6204600097e00020460f31e603cc1e60f30798d4b556,0x244080208481,0x204080200481,0x0,0x20c082208481,0x0,0x20c082208481,0x214082208481,0x214082208481,0x1000800004083000010004000010000040000040100008200400000001000004000010008000040020000100100000100100001000081004000200004001000000001002886aba7,0x214082208481,0x0,0x0,0x0],
[0x0,0x0,0x244082208481,0x16c83cc1e60f307980f33cc00088b000222c0003528b641e61e607981e61e62d903ccb640f30f30799dc6,0x244082208481,0x214082208481,0x0,0x20c084210481,0x0,0x20c084210481,0x2000080080002002000080002000020000814e3,0x214084210481,0x2000080080002002000080002000020000814e3,0x214084210481,0x0,0x0,0xf3001e6f301e60f301e9cc0002d9000222c0001e67b66007b660007b660f31e603cc003db307984c0556,0x0,0x0,0x244084218481,0xf300f30f30f307980f33cc0002d9000222c0001e67b66007b660007b660f31e603cc003db30798d4b556,0x244084218481,0x2000080080002002000080002000020000814e3,0x811800204600081183cc01e6f30811bcc035280799e60799e600f33cc03cc0f30f30f6cfcc1e703375,0x0,0x811800204600081180003cde6016cf9803f99f3003cfcc01e6000f6cc003cde600f3f6cc001e703885,0x0,0x4402110004004100104020108040021000804e4,0x0,0x0,0x4402110002004080104020108040021000804e4,0x4402110004004100104020108040021000804e4],
[0x4402110004004100104020108040021000804e4,0x402010000004000104000108040021000000e4,0x840323000800420010204010902001100180ca4,0x403010000005000102000108020011000804a4,0x840343000800440010204010a02001100381ca4,0x0,0x0,0x0,0x402010040005000104000108040021000000e4,0x811800204600081183cc01e6f307983cc01e603cc7980f31e603cc3cc0f303cc3cc0f6cc001e703d95,0xf307980005b20f307983cc0002d9000222c0001e9cde603cde6003cde60f31e603cc7980f30001e61556,0x0,0x20c084210481,0x0,0x20c084210481,0x0,0x214084210481,0x2000080080002002010080402010020000814e3,0x214084210481,0x0,0x0,0x1020000004082000010200000010000040000000100008200400000001000004000100008000400020002000100002000100010000081040000200080001000000001002086aba7,0x0,0x0,0x244084218481,0x16c83cc1e60f307980f33cc00088b000222c0003528b643cc1e603cc1e61e62d907983cc0f30f30799e56,0x244084218481,0x16c83cc1e60f307981e63cc00088b000222c0003528b643cc1e603cc1e61e62d907983cc0f30f30799e56,0x0,0x400220000000080000001200010000800040020001100000004400000008000000008200300000800400002000000002001000200020010800000002000200002000000200017ffa8,0xc02030000804020108200408020005000100a4,0x0],
[0xc02010001004040110200408040009000100e4,0x0,0x0,0xc02030000004020108200408020001000100a4,0xc02030004004100110080408040021000914e4,0xc02030000804020108200408020005000100a4,0xc02030008004200108040409020041001108a4,0x0,0xc0203000800440010804040a020041003118a4,0x0,0x0,0x0,0x0,0x0,0x20c0a8220481,0x79f980204600079f9bcc01e6f307983cc01e61e607987981e61e603cc79803cde600f6cc001e703d95,0x20c0a8220481,0x2541c8228501,0x2140c8220481,0x2000080080002002020080802020020000814e3,0x2140c8220481,0x0,0x799e601e67980799e9cc007a7307983cc01e61e607987981e61e603cc79803cde600f6cc001e740995,0x17bed3980001e60f301e9cc00088b000222c000361f82400111600011161e62f7e1181e60f30000001e56,0x0,0x0,0x244188228501,0x16c83cc25f8f307980f33cc00088b000222c0003528b6425f9e601e61e61e62d903ccb640f312fc97fdc6,0x244188228501,0x2541c8228501,0x0,0x20c086218481],
[0xf300007983cc7983cc0b640002d9000222c00020461e61e61e601e61e60f31e603cc799f530001e61556,0x20c086218481,0x0,0x214084210481,0x2000080080002002010080002000020000814e3,0x214084210481,0x0,0x799e601e67980799e9cc0000f307983cc01e607987981e61e60f303cc3cc03ccf300f6cc001e703d95,0xf3001e60f31e60f301e9cc0002d9000222c00020461e61e61e601e61e60f31e603cc8118f3007983e156,0x0,0x0,0x24418c238501,0xf300f30798f307980f33cc0002d9000222c00020461e61e61e601e61e60f31e603ccb640f303cc1e7556,0x24418c238501,0x2000080080002002010080002000020000814e3,0x0,0x20c0a8220481,0x0,0x20c0a8220481,0x2541c8228501,0x2140c8220481,0x2000080080002002040081002040020000814e3,0x2140c8220481,0xf4e60f300001e60f307d4c00088b000222c0002d90b640001e600001e61e61e9cfcc0000f30000001dc6,0x799e601e67980799e9cc007a7307983cc01e67980799e601e63cc03ccf3003cfcc00f6cc001e740995,0x0,0x799e601e7e60079bcfcc01e6f30811bcc03529e601e7e601e63cc03ccf3000f6cc00f7bf001e703375,0x0,0x244188228501,0x16c83cc1e60f307980f33cc00088b000222c0003528b645b21e607981e61e62d90798b640f30f30799e56,0x244188228501,0x2541c8228501],
[0x0,0x20c080200481,0x0,0x20c080200481,0x204080200481,0x214080200481,0x2000080080002002000080002000020000814e3,0x214080200481,0x0,0x0,0xf3001e63cc1e60f301e9cc0002d9000222c000222c1e60f31e603cc1e60f31e603cc0798f301e60f4556,0x0,0x0,0x244082208481,0xf300f31e60f307980f33cc0002d9000222c000222c1e60f31e603cc1e60f31e603cc3cc0f30f3097f556,0x244082208481,0x204080200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_8278 : TreeBound (n := 4) 107 (programCode 0x422b072076) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x811800798000082fe3cc0002d9000222c0002d901e63cc1e60f301e60f31e603cc7980f3003cfebb56,0x0,0x0,0x2004080100804020180202008040401000442e4,0x0,0x2004080101004040180202008040401000442e4,0x1e601e61e601e67980b64f3088b00007983cc2d90b643cc0798f301e61e61e9d3987980f3000f6d5776,0x0,0x0,0x0,0x0,0x200408010800420018004200804040100144ae4,0x0,0x2004080110004400180082008040401002452e4,0x0,0x0,0x0,0x0,0x8118007983cc081183cc0002d9000222c0002d901e63cc1e60f301e60f31e603cc7980f3003cfebb56,0x0,0x4000100180022002000880022000820000814e3,0x80002002000080402000020000814e3,0x4008100280022002001080042001020040814e3,0x80002002000080002000020000814e3,0x0,0x80002002000080002000020000814e3,0x0,0x0,0x0,0x0,0x0],
[0x0,0x20000004080002002020080802000020000814e3,0x80002002000080002000020000814e3,0x8080002002040081002000020000814e3,0x80002002000080002000020000814e3,0x0,0x4010100480022002000880022000820020814e3,0x10000480002002000080402000020400814e3,0x4010100480022002001080042001020040814e3,0x10000480002002000080002000020000814e3,0x0,0x10000480002002000080002000020000814e3,0x0,0x0,0x0,0x81180079801e67980b640002d9000222c0001e9cde603cde6003cde60f31e603cc7980f3003cfebb56,0x10000480002002010080402000020400814e3,0x0,0x2010080480012002020080802020020800816e3,0x10000480002002000080402000020400814e3,0x2010080480012002040081002040021000816e3,0x10000480002002000080002000020000814e3,0x7983cc7983cc0798408c0002d9000222c0002d901e63cc1e60f301e60f31e603cc7980f3003cfebb56,0x0,0x4020100880022002000880022000820020814e3,0x20000880002002000080402000020000814e3,0x4020100880022002001080042001020040814e3,0x20000880002002000080002000020000814e3,0x0,0x20000880002002000080002000020000814e3,0x0,0x0],
[0x0,0x0,0x20000880002002010080402000020400814e3,0x0,0x4020100880022002020080802020020800814e3,0x20000880002002000080402000020000814e3,0x4020100880022002040081002040021000814e3,0x20000880002002000080002000020000814e3,0x0,0x0,0x2020080800804020180202008040401000446e4,0x0,0x2020080801004040180202008040401000446e4,0x0,0x0,0x0,0x0,0x0,0x202008080800420018004200804040100144ee4,0x0,0x2020080810004400180082008040401002456e4,0x40004000800010001000080001000104010000022040000408000000900400000c0000400100001020400020081000010000800200802000800010002000020000020081051ea8,0x402008084000880018023200804042100084704,0x0,0x402008084000900018022200804042100084504,0x0,0x0,0x2010080400804020180202008040401000442e4,0x0,0x0,0x1f173301e60000798427998088b00007980002d90b736cc0000f301e61e61e9d3987980f3000f6d5776,0x81180079f9800798f301e601e7e601e61e602d901e63cc1e60f301e60f31e603cc7980f3003cfebb56],
[0x0,0x0,0x0,0x200408140800420018004200804040100144ae4,0x420001001000004004000002000000008002002100008000000010000000020006004000010010000040040000080100000100420000101000000400000000800200001001087fe27,0x2004082410004400180082008040401002452e4,0x400000801050002004000008000100008010000020040008280100000200100004004000008010000020040000100100000100400000081500000200400001001000001002486aba7,0x400000801040002004000008000000008040000000104008200000000000080004004000008010000020040000100100000100400000081040000200000001000800001002086aba7,0x0,0xf300003ea7e607987a7300044580010230002d90007d4c0f4f5301e60f31e6079879fa73001eda8a66,0x799e60799e600799e9cc0002d9000222c0002d901e63cc1e60f301e60f31e603cc7980f3003d0deb56,0x0,0x0,0x2200088000804020180202008040401000442e4,0x0,0x2200088001004040180202008040401000442e4,0x1f173301e600007b665b998088b00007980002d90b736cc0000f301e61e61e9d3987980f3000f6d5776,0x0,0x0,0x0,0x0,0x204008800800420018004200804040100144ae4,0x400000801040002004000010000000010001000000004008200020000000020004004000008010000020040000100100000100400000081040000200000001000800001002086aba7,0x2080088010004400180082008040401002452e4,0x1f176fc1e600007b666ae7e07d4c0007980002d90b7738c0000f301e61e61e9d3987980f3000f6d5776,0x423008804000880018023200804042100084704,0x0,0x422008804000900018022200804042100084504,0x0,0x40040000100100001001000001001000080000030000000082000000920050000c00000401000010004000250810000100008002000020008120200020000200004200a10513a8,0x2080082000804020180202008040401000452e4,0x0],
[0x2080082001004040180202008040401000452e4,0x0,0x0,0x0,0x0,0x0,0x208008200800420018004200804040100145ae4,0x0,0x2080082010004400180082008040401002452e4,0x0,0x0,0x0,0x0,0x7b660079f98007b663cc0002d9000222c0002d901e63cc1e60f301e60f31e603cc7980f3003cfebb56,0x7a73007a730007a733cc0002d9000222c0002d901e63cc1e60f301e60f31e603cc7980f3003d969b56,0x0,0x0,0x200008080002002000080402000020000814e3,0x0,0x200008080002002000080002000020000814e3,0x420010000020040000080080000000100040002100100000000400000001000006000020010000080040000040080000100100420000101000000400000000800200001001087fe27,0x200008080002002000080002000020000814e3,0x10008001040020000200100000000100040000000100008200400000001000004000010008000040020000200100000200100400000081040000200000001000800001002086aba7,0x0,0x410008001040020000200100000000100040000000100008200400000001000004000100008000400020001000100001000100400000081040000200000001000800001002086aba7,0x811800798798081183cc0002d9000222c0001e9cde603cde6003cde60f31e603cc7980f3003d028756,0x200008080002002010080402000020000814e3,0x0,0x40201008080202002020080802040021000854e3,0x40201008080202002040081002040021000854e3,0x40201008080202002040081002040021000854e3,0x200008080002002000080002000020000814e3],
[0x7b660079f98007b663cc0002d9000222c0002d901e63cc1e60f301e60f31e603cc7980f3003cfebb56]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_8439 : TreeBound (n := 4) 107 (programCode 0x422b072077) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x8118007b66000fa983cc001f53079fd4c0370e00f4e6003ea6000f6cc003ccf300f3f6cc3cde703375,0x0,0x20c084210481,0x0,0x20c084210481,0x4000100080002002000080402000020000814e3,0x214084210481,0x4000100080002002000080402000020000814e3,0x214084210481,0x0,0x0,0x1ee4e403ea6000f3003cc2139f300003cc00f409c87980000f307983d027203cc00007980001e68a8c5,0x0,0x0,0x244084218481,0x1ee4e403ccf300f3003cc2139f300003cc00f409c87980000f307983d027203cc00007980001e68a8c5,0x244084218481,0x4000100080002002000080402000020000814e3,0xfa98007b66000fa983cc001f5307a76cc02d9001e9cc00f4e6001e9cc00799e603ccf6cc001e703885,0x0,0x20c080200481,0x0,0x20c080200481,0x204080200481,0x214080200481,0x4000100080002002000080002000020000814e3,0x214080200481,0x0,0x0,0x1ee4e403ea6000f3003cc2139f300003cc00f3f3007980000f300003cfcc003cc00007980001e68a8c5,0x0],
[0x0,0x244080208481,0x1ee4e403ccf300f3003cc2139f300003cc00f3f3007980000f300003cfcc003cc00007980001e68a8c5,0x244080208481,0x204080200481,0x0,0x20c082208481,0x0,0x20c082208481,0x214082208481,0x214082208481,0x0,0x214082208481,0x0,0x0,0x0,0x0,0x0,0x244082208481,0x0,0x244082208481,0x214082208481,0x0,0x20c084210481,0x0,0x20c084210481,0x4000100080002002000080002000020000814e3,0x214084210481,0x4000100080002002000080002000020000814e3,0x214084210481,0x0,0x0],
[0x1ee4e403ea6000f3003cc2139f300003cc00f409c87980000f300003d027203cc00007980001e68a8c5,0x0,0x0,0x244084218481,0x1ee4e403ccf300f3003cc2139f300003cc00f409c87980000f300003d027203cc00007980001e68a8c5,0x244084218481,0x4000100080002002000080002000020000814e3,0x1ed98007b66000fa983cc01e6f307983cc01e601e67980799e600f33cc07983cc1e60f6cc001e703d95,0x0,0x0,0x0,0x4400110004004100104020108040021000804e4,0x0,0x0,0x4400110002004080104020108040021000804e4,0x4400110004004100104020108040021000804e4,0x4400110004004100104020108040021000804e4,0x4400110004004100104020108040021000804e4,0x440031000800420010404010804002100180ce4,0x4400110004005000104020108040021000804e4,0x4400510010004400104080108040021002814e4,0x8118007b66000fa9807981e61e6811879835280f31e603cde61f533cc03cc0f30f30f7494c1e703375,0x4400110020004800104020108040021000804e4,0x1ed98007b66000fa981e601e67987980f301e600007980799e679803cc00003cc1e60f6cc001e703d95,0x4400110040005000104020108040021000804e4,0x1ed98007b66000fa983cc01e6f307983cc01e603cc7980f31e603cc3cc0f303cc3cc0f6cc001e703d95,0x0,0x8118007b66000fa980003ea600179ca00401280f31e603cde70e873cc03cc0f30f30f73a1c1e703375,0x180424420222,0x80024420022,0x180424420222,0x0],
[0x0,0x80024420022,0x440011000200410010804020902002100080ca4,0x80024420022,0x481024620862,0x0,0x481024620862,0x0,0x0,0x0,0x0,0x8118007b66000fa983cc0000f307983cc035283cc1e63cc1e607983cc0f300f3f300f6ea601e703375,0x0,0x0,0x180424420222,0x80024420022,0x180424420222,0x0,0x0,0x80024420022,0x4400110004004100110080408040021000814e4,0x80024420022,0x481024620862,0x400010000005000110000408040001000000e4,0x481024620862,0x8118007b66000fa9807981e61e6811879835280f31e603cde712533cc03cc0f30f30f7494c1e703375,0x0,0x1ed98007b66000fa981e601e67987980f301e601e67980799e76c803cc07983cc1e60f6cc001e703d95,0x0,0x0,0x20c0a8220481,0x1e679807b66000f379bcc01e6f307983cc01e61e607987981e61e603cc79803cde600f6cc001e703d95],
[0x20c0a8220481,0x2541c8228501,0x2140c8220481,0x4000100080002002020080802020020000814e3,0x2140c8220481,0x0,0x1e61e607987980f31e9cc007a7307983cc01e61e607987981e61e603cc79803cde600f6cc001e740995,0x2021000008000000008200000020000040002100100000100400000001000001002000010008000040010000040010000100600000101000000401000000400000001000887fda7,0x0,0x0,0x244188228501,0x1e67980799e600f3003cc0000f307983cc01e61e607987981e61e603cc79803cde600f6cc001e703d95,0x244188228501,0x2541c8228501,0x8118007b66000fa983cc0000f307983cc035283cc1e63cc1e6fa983cc0f300f3f300f6ea601e703375,0x0,0x20c0a8220481,0x7980007b66000f3d4dcc0000f307983cc03529e601e7e601e63cc03cc79800fa9800f7bf001e703375,0x20c0a8220481,0x2541c8228501,0x2140c8220481,0x4000100080002002040081002040020000814e3,0x2140c8220481,0xf307987983cc0fa983cc001f5307af04c02d93cc03cde601e63cc03ccf3001ed9800f9a5001e703885,0x1e61e607987980f31e9cc007a7307983cc01e67980799e601e63cc03cde6003d39800f6cc001e740995,0x0,0x1e67980799e600f33cfcc01e6f307983cc01e67980799e601e63cc03cde6003d39800f6cc001e703d95,0x0,0x244188228501,0x1e67980799e600f379bcc01e6f307983cc01e67980799e601e63cc03cde6003d39800f6cc001e703d95,0x244188228501,0x2541c8228501],
[0x8118007b66000fa983cc0000f307983cc035280001e60001e6f3003cc00000f30000f6cc001e703375]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_8600 : TreeBound (n := 4) 107 (programCode 0x422b072078) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x1f173303cc0000f3005b99807980001e600002d90b736cc0000f301e61e61e9cfcc7980f3001e6110c6,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1f173303cc0000f307f399807980001e600002d90b736cc0000f301e61e61e9cfcc7980f3001e6110c6,0x0,0x1f173303cc0000f4e65b99807980001e600002d90b736cc0000f301e61e61e9cfcc7980f3001e6110c6,0x2001000008004000008004000020010062a3000110000000400800000802000000c000315190000400040000040100001000200031518800001000800200002000001000897fda8,0x1f173303cc0000f3005b99807980001e600002d90b736cc0000f301e61e61e9cfcc7980f3001e6110c6,0x0,0x0,0x400220001000080004002000000002000000022100000080000000081000000102004000010010000040040000080100000100400000101000000400000000800000001001087fe67,0x0,0x4000118000804020180202008040401000844e4,0x4004100100804020180202008040401000844e4,0x4020110000804020180202008040401000844e4,0x0,0x0,0x4010100400804020180202008040401000846e4,0x0,0x4020100800804020180202008040401000844e4,0x4020100800804020180202008040401000844e4,0x404010100080402018020200804040100084ce4,0x4200108000804020180202008040401000844e4,0x4080102000804020180202008040401000854e4,0x4200108000804020180202008040401000844e4],
[0x4100104000804020180202008040401000864e4,0x0,0x4200108000804020180202008040401000844e4,0x0,0x0,0x0,0x4400110004004100104020108040021000804e4,0x0,0x0,0x0,0x4400110004004000100000108040001000804e4,0x4400110004004100104020108040021000804e4,0x4400110004004000100000108040001000804e4,0x440011000400420010804020804004100180ce4,0x4400110004004000100001008040021000804e4,0x44001100040045001100a0408040021002814e4,0x62b80018ae00062b800079800044580007c591e603cc7981e61e603cc00001e60000f6cc001e703885,0x0,0x7980001e600062b800079800044580007c593cc03cde601e63cc03cc00001e60000f6cc001e703885,0x0,0x0,0x4000118001004040180202008040401000844e4,0x4004100101004040180202008040401000844e4,0x4020110001004040180202008040401000844e4,0x0,0x0,0x4010100401004040180202008040401000846e4,0x0,0x4020100801004040180202008040401000844e4,0x0,0x404010100100404018020200804040100084ce4,0x4200108001004040180202008040401000844e4],
[0x4080102001004040180202008040401000854e4,0x4200108001004040180202008040401000844e4,0x4100104001004040180202008040401000864e4,0x0,0x4200108001004040180202008040401000844e4,0x0,0x4000200010000800040002000000108000000420000001000100004200000010060000004100000010400000040800000101004000001010000004000004008100000010010873227,0x0,0x25f800097e0008118001e63cc08118001e7e6003d39800f4e6001e9cc0079bcc01e6f6cc001e722395,0x2020000002080000020200000020800020000000980800000a000000090000000080020010000021000000220110000210002000100002000c004200010000200000400020793a8,0x0,0x82000000208000002020000002080000800000092080000088000000900000000801000100001010000010201800010100008000002020008028200000020200000400020593a8,0x1ed98007b660008118001e7e6008118001e7e601e67980799e600f33cc07983cc0f30f6cc001e703d95,0x0,0x81180020460008118001e7e6008118001e7e603cc7980f31e603cc3cc0f303cc3cc0f6cc001e703d95,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4000200010000800040002000000208000000820000002000100008200010020060000004100000010400000040800000101004000001010000004000004008100000010010873227,0xfa98003ea6000fa98001e601e7e601e61e601e61116000f301e611160f307983cc1e60f3001e610856,0x4400110002004080104020108040021000804e4,0x0,0x0,0x0,0x4400110002004080100020108040001000804e4,0x4400110002004080104020108040021000804e4,0x0],
[0xfa98003ea6000fa98001e601e7e601e61e601e9cde603cc07983cde60f3000f6cc003db3001e64d456,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4000200010000800040002000000c08000002020000008000100010200000020060000004100000010400000040800000101004000001010000004000004008100000010010873227,0x40002000100f080000004200000080800000040000000408780002020000002004000000002010f000200400001000080001000200000210f0000200000001010000001002084aba7,0x4400110004004100104020108040021000804e4,0x400020001007080004000200000080800000040000000408380002020000002084000000002010000020040000100100000100400000021000000200000001010000001002084aba7,0x0,0x0,0x4400110000004100100000108040001000804e4,0x4400110004004100104020108040021000804e4,0x4400110000004100100000108040001000804e4,0x440011000400410010804020804002100080ce4,0x4400110004004100100001008040021000804e4,0x4400110000004100110080408040001000814e4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4400110004004100104020108040021000804e4,0x0,0x0,0x0,0x4400110004004100100000108040001000804e4],
[0x4400110004004100104020108040021000804e4,0x4400110004004100100000108040001000804e4,0x440011000400410010804020804002100080ce4,0x4400110004004100100001008040021000804e4,0x4400110004004100110080408040021000814e4,0x4400110004004100100002008040401000804e4,0x0,0x4400110004004100100002008040401000804e4,0x0,0x82000000408000002020000002080000000000034040000200000000800800000c000000010000a020400020001000010000800200004000802020002000020000040002052ba8,0x440011000800420018004200804040100180ce4,0x0,0x0,0x0,0x4400110004005000104020108040021000804e4,0x0,0x0,0x0,0x4400110004005000100020108040001000804e4,0x4400110004005000104020108040021000804e4,0x79f9801e7e600f379803cc0000f379801e61e603cc7980f31e603cc3cc3cc03ccf300f6cc001e703d95,0x8200000080800000102000000208000080000002080000040010000022000000080400400008000400004000080010010000800040008000100010000400020000420021053e28,0x4400110004005000104021008040021000804e4,0x44001100140050001100a04080400a1002814e4,0x4400110004005000104022008040421000804e4,0x0,0x4400110004005000100022008040401000804e4,0x0,0x4400110010004400180082008040401002814e4,0x0,0x1f173303cc0000f3005b99807980001e600002d90b736cc0000f301e61e61e9cfcc7980f3001e6110c6,0x0],
[0x0,0x0,0x0,0x0,0x1eda7303ea6000f307f399807980001e600002d90b736cc0000f301e61e61e9cfcc7980f3001e6110c6,0x4020100800004000180002008040401000804e4,0x4000100800004000180002008040401000804e4,0x200100000800400001000200002000806022000100040000408000000200010000c000301010000002040000400100001000200020100800080001000200002000002000107fe28,0x4000108000004000180002008040401000804e4,0x3b9b059aca01dcd82cd653b9b059aca03b9b059aca077360b3d075940001dcd65ee6b28ee6ee1aca1deb32650000ee6b6b0e2399682fee6b2f735943b9ae7cd6500077acc9943b9ae7cd650ee6b639acdb9aca1dcd73e6b2bb9acdb9aca3b9ad8e6b2877359401dcd65f203368a,0x4000100000004000180002008040401000804e4,0x0,0x1ed98003ea6000f3005b99807980001e600002d90b736cc0000f301e61e61e9cfcc7980f3001e6110c6,0x0,0xfa98007b66000fa980f3000408c000fa98002d9000f6cc0f8c1301e60f31e6079879fa73003cc1fd66,0x0,0x0,0x0,0x7980001e60b647980f300007987980f302d9001e9cc00f4e6001e9cc00001e60000f6cc001e703885,0x0,0x0,0x0,0x1ed98007b6607987981e601e67987980f301e601e67980799e600f33cc07983cc1e60f6cc001e703d95,0x7980001e60b647980f300007987980f302d900003cc0001e6b6403cc00001e60000f6cc001e703885,0x0,0x0,0x0,0x2000160008000000020000800080000800000004000830020002000020000400000000401e0000200000001000200001000000000416000002000000010100000010020852ba7,0x0,0x0,0x7980001e60b647980f300007987980f302d93cc03cde601e63cc03cc00001e60000f6cc001e703885,0x200016000800040002000080008000080000000400083002000200002000040040000040160000200000001001000001004000000416000002000000010100000010020852ba7],
[0x1ed98007b66000fa981e600044580010230002d9000f6cc0f6db301e61e61e607987a73f3003cc20276]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_8793 : TreeBound (n := 4) 107 (programCode 0x422b072079) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x3d39800f4e6003d3980003cde6016cf9804031d3001e9cc01e6f3003cc003ccf300f3f6cc3cde703375,0x400010000804020180202008040401000000e4,0x3d39800f4e6003d398000f33cc044580007b66f30079bcc01e6f3003cc0079bcc01e6f6cc001e722395,0x0,0x3d39800f4e6003d3983cc001f53079f9803f99000f6cc003ea6000f6cc003cde600f3f6cc001e703885,0x0,0x80420420022,0x0,0x0,0x0,0x80420420022,0x0,0x80420420022,0x180424420222,0x80428420022,0x180424420222,0x0,0x80428420022,0x0,0x80428420022,0x0,0x408890208481,0x420890208481,0x408890208481,0x0,0x0,0x10020000040083000100200000100000000100040000408200001000000001004004000008010000020040000100100000100001000081004000200004001000000001002886aba7,0x0,0x0,0x420890208481,0x420890208481],
[0x420890208481,0x0,0x440890218481,0x420890208481,0x440890218481,0x16c83cc1e60f307981e65b200088b00020460002d90b643cc2d90f301e61e62d907987980f30f30799e56,0x0,0x8004200180000002080082002000020000814e3,0x0,0x8008200280000002080082002000020000814e3,0x0,0x0,0xf30003db3003cfcc003cc1e601e7e601e61e602d901e63cc1e60f301e60f31e603cc7980f307983ebb56,0x0,0x0,0x8040201080000002080082002000020000814e3,0xf3001e6f301e63cc01e601e601e7e601e61e602d901e63cc1e60f301e60f31e603cc7980f307984c0556,0x0,0x0,0x8100204080080402080082002010020200814e3,0xf300f30f30f303cc0f3001e601e7e601e61e602d901e63cc1e60f301e60f31e603cc7980f30798d4b556,0x8200208080080402080082002010020200814e3,0x8000200080000002080082002000020000814e3,0x3d39800f4e6003d398001e7e601ee11803cf5373001e9cc01e6f3003cc03cc0f30f30f6cfcc1e703375,0x0,0x0,0x0,0x401010002004100100001008020001000000a4,0x0,0x0,0x0,0x401010002004100100000008020001000000a4],
[0x4400110004004100104020108040021000804e4,0x401010002004100100001008020001000000a4,0x840131000200410010804020902002100180ca4,0x401010002004100100001008020001000000a4,0x10400510004004100110080408040021002814e4,0x400010004004100100002008040401000000e4,0x0,0x400010004004100100002008040401000000e4,0x0,0x400010000004000180002008040401000000e4,0xc00230008004200180042008040401001108e4,0x0,0x409090210481,0x421090210481,0x409090210481,0x0,0x0,0x10020000040082000100200000100000001000000004008200020000000020004004000008010000020040000100100000100010000081040000200080001000000001002086aba7,0x0,0x0,0x421090210481,0x421090210481,0x421090210481,0x421090210481,0x441090210481,0x421090210481,0x441090210481,0x421090210481,0xc00430010004400180082008040401002110e4,0x0,0x40a0b0220481,0x422090220481],
[0x40a0b0220481,0x0,0x0,0x10020000040082000100200000100000010000000040008200100000000100004004000008010000020040000100100000100100000081400000200400001000000001002086aba7,0x3cc03ccf303cc3cc079f9801e7e679f9f98371d3001e9cc01e6f3003cc79800f4e600f745801e703375,0x20000800004000180002008040401000000e4,0x422090220481,0x422090220481,0x422090220481,0x462190230501,0x442190230501,0x422090220481,0x442190230501,0x462190230501,0x0,0x409890218481,0x421090210481,0x409890218481,0x0,0x0,0xf30003cc1e63cc07983d3980025f8001ed98002d901e63cc1e702301e60f31e603cc7980f3000f6f34d6,0x400000020004800180002008040401000000e4,0xf4e60f303cc3cc0f307b660008118001ed98002d90b736cc001f5301e61e61e9d3987980f3001e611156,0x421090210481,0x421090210481,0x421090210481,0x421090210481,0x443190230501,0x421090210481,0x443190230501,0x421090210481,0x0],
[0x40a0b0220481,0x422090220481,0x40a0b0220481,0x0,0x0,0x0,0x3cc0f30f303cc3cc07b66003d3987980f301e6f30079bcc01e6f3003ccf3003cfcc00f6cc001e722395,0x0,0x422090220481,0x422090220481,0x422090220481,0x462190230501,0x442190230501,0x422090220481,0x442190230501,0x462190230501,0x0,0x408090200481,0x420090200481,0x408090200481,0x0,0x0,0xf30003cc7983cc1e603db3000222c001f530002d901e63cc003db301e60f31e603cc7980f3003cfebb56,0x0,0xf30007983cc1e60f307a73000222c001f530002d901e63cc001f5301e60f31e603cc7980f3001e610856,0x420090200481,0x420090200481,0x420090200481,0x400090200481,0x441090210481,0x420090200481,0x441090210481],
[0x400090200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_8954 : TreeBound (n := 4) 107 (programCode 0x422b07207a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x3d39803cde6003d3983cc0002d9000222c0002d901e63cc1e60f301e60f31e603cc7980f301e60f4556]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_8955 : TreeBound (n := 4) 107 (programCode 0x422b07207b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x3d39803cde60079f980003cde6016cf9804031d3001e9cc01e6f3003cc003ccf300f3f6cc3cde703375,0x0,0x409090210481,0x421090210481,0x409090210481,0x0,0x0,0x40011000400804020180202008040401008042e4,0x0,0x40021000800804020180202008040401008044e4,0x421090210481,0x421090210481,0x421090210481,0x421090210481,0x441090210481,0x421090210481,0x441090210481,0x421090210481,0x79f9803cde60079f98000799e6044673007c59f3003cfcc01e6f3003cc00799e603ccf6cc001e703885,0x0,0x10004400100002002080082002000020000814e3,0x10000402000002002080082002000020000814e3,0x10008400200002002080082002000020000814e3,0x0,0x0,0x40011000401004040180202008040401008042e4,0x0,0x40021000801004040180202008040401008044e4,0x0,0x40041001001004040180202008040401008048e4,0x10080402000002002080082002000020000814e3],
[0x40081002001004040180202008040401008050e4,0x10100404000002002080082002000020400814e3,0x10000400000002002080082002000020000814e3,0x10200408000002002080082002000020400814e3,0x10000400000002002080082002000020000814e3,0x0,0x408890208481,0x420890208481,0x408890208481,0x0,0x0,0x0,0x0,0x0,0x420890208481,0x420890208481,0x420890208481,0x0,0x440890218481,0x420890208481,0x440890218481,0x0,0x0,0x3d39803cde60079f98003cde600fb6ce3a1f52800f4e6003ea6000f6cc03cc0f30f30f73a1c1e703375,0xf379800f4e60079f9843671b283d3983cc007a8d9479bcc007983cc3d036503cc3cc0408c001e64dc35,0x401010002004080100000008040001000000e4,0x0,0x0,0x0,0x401010002004080100000008020001000000a4,0x4401010002004080104020108040021000804e4,0x401010002004080140000008040001000000e4],
[0xf379800f4e60079f9843671b283d3983cc007a8d9479bcc007983cc3d036503cc3cc0408c001e64dc35,0x0,0x0,0x0,0x0,0x0,0x0,0xf379803cde60079f9800799e601ed98003cde6f30079bcc01e6f3003cc07983cc1e60f6cc001e703d95,0x0,0x0,0x0,0x401010002004100100001008020001000000a4,0x0,0x0,0x0,0x401010002004100100000008020001000000a4,0x4401010004004100104020108040021000804e4,0x401010002004100100001008020001000000a4,0x840121000200410010804020902002100180ca4,0x401010002004100100001008020001000000a4,0x10401010004004100110080408040021002814e4,0x0,0x0,0x401010004004100100002008040401000000e4,0x0,0x401010000004000180002008040401000000e4,0x8401010008004200180042008040401001008e4,0x401010000005000180002008040401000000e4,0x10401010010004400180082008040401002010e4,0x0,0x40a0b0220481,0x422090220481],
[0x40a0b0220481,0x0,0x0,0x7981e60f4e60079f9807980f3798798079807a73003cfcc007a73003cfcc001ed98004105801e64d3c5,0x3cc03cfcc03cc798079f9801e7e679f9f98371d3001e9cc01e6f3003cc79800f4e600f745801e703375,0x79f9803cde600798f307983cc1e688b07982d9f3003cfcc01e6f3003cc79801e7e600f6ea601e8e9885,0x422090220481,0x422090220481,0x422090220481,0x462190230501,0x442190230501,0x422090220481,0x442190230501,0x462190230501,0x0,0x409890218481,0x421090210481,0x409890218481,0x0,0x0,0x40011000420004800180202008040401008042e4,0x0,0x40021000820004800180202008040401008044e4,0x421090210481,0x421090210481,0x421090210481,0x421090210481,0x443190230501,0x421090210481,0x443190230501,0x421090210481,0x0],
[0x40a0b0220481,0x422090220481,0x40a0b0220481,0x9000200005000180002008040401000000e4,0x0,0x0,0x798079bcc03cc79807a73001ed987a73f302d9f3003cfcc01e6f3003ccf3001ed9800f6cc001e703885,0x0,0x422090220481,0x422090220481,0x422090220481,0x462190230501,0x442190230501,0x422090220481,0x442190230501,0x462190230501,0x401010040005000180002008040401000000e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_9100 : TreeBound (n := 4) 107 (programCode 0x422b07207c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x108490200481,0x798007d4c0079f9800b643cc1e63cc222c3cc2d901e63cc25f8f301e60f320467987980f301e60f45e6,0x108490200481,0x79800f6cc0079f98012fc7981e63cc222d2fc2d901e63cc3528f301e60f321397987980f301e60f45e6,0x0,0x0,0x0,0x0,0x40801000000800000408000004008000012004000010500000100040000105004000010010000040040000040100000100400040100000100400000400400001001000887b1a7,0x0,0x0,0x108490200481,0x7a1f7fd4c0079fa1fa2f3fcc1e63cc2269efc2d901e63cc27e0d901e60f327e05f87980f301e60f45e6,0x798f303ccf300798f344580025f80022a5bcc2d90222fcc26ebf301e60f32f767987980f31116a725e6,0x200028000800022080082002000020000814e3,0x100490200481,0x10400410000804020180202008040401002010e4,0x20001000c800000002000000028000000080000000483000002200000002040040000040100000200400001001000001000000000410000002000000010100000010020852ba7,0x10400410001004040180202008040401002010e4,0x0,0x2cb41780000b2d05fdcd6d61c4680000b2d05e000ef599328003bd664ca000ee6b2bb9acaee7a0eb280ef599328000ee81820bc0077712eca001ddc4bb28001e08ffca001dd4d8594001dd4d8d075940077536165001dd4d85940077359401dce53e25d94000ee6ee959172c9,0x0,0x1dce536b28077394daca01dce536b280ee6ee1aca00ee7a0eb28000000000ee6b45cd65f6d4619e165ee6b280000430e23400003f5476bdcd6507735940021a4e7858073d1b0ee1aca0001ddc4bb36e6b2800003b9aca000ef59936b49cd67e815dcd65773594773597bbb642eaa,0x0,0x0,0x0,0x2020001005080000028200000090800000102000000400180001020600001000800008004000080040000040020000200100402800041000000400008000210030001000485b8a7,0x0,0x8020000040080000200200000200800040000000344040002000040009000000008200040014404a202400020000080010000800200004000a20220002000020000400020052ba8,0x79f9803cde60079f983cc3cc1e60f3222c0001e9cde603ce5f803cde60f320485f87980f301e60f45e6],
[0x0,0x79f9803cde60079f983cc3cc1e63cc222c0001ed99e603ce5f80799e60f320485f8001f5301e60f45e6,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x79f9801e7e60079f98001e601e7e601e61e601e601e601e603cc1e7e60f300003cc00f3f300f307ea16,0x0,0x0,0x0,0x80200010e00800042002000002008000008000001060083000200200010000040000080040000400200002001000002001004080000410e00002002000010100000010020852ba7,0x10400410002004080104020108040021002814e4,0x802000002008000020020000020080000004000020010000080100000800100000880000020001010000800010000800100008000100020000008200001020200004000200513a8,0x0,0x480828420862,0x0,0x0,0x480828420862,0x0,0x480828420862,0x0,0x0,0x0,0x481024620862,0x0,0x0,0x0,0x481024620862,0x10400410004004500104020108040021002814e4],
[0x7736826b28077394daca01dce536b280ee6ee1aca00ee7a0eb2800000000086937c1400f8cf0376400fdc91014003ba9b0b28003b9aca77359b735a2f5995c0f7a5281529f81a5fbc2abb9ad8e6b639aca000003b9ad1aef418e6b7b1edc29359baef41173594773597bbc0fd7fa,0x481024620862,0x48102c620862,0x481024620862,0x0,0x481028620862,0x0,0x481028620862,0x0,0x0,0x0,0x104004100040041001100805080400a1002814e4,0x0,0x0,0x0,0x840041000200410010402030982002100180ca4,0x10400410004004100104020108040021002814e4,0x840041000200410010000130982006100180ca4,0x840041000200410010804020902002100180ca4,0x480828420862,0x10400410004004100110080408040021002814e4,0x0,0x480828420862,0x10400410004004100104022008040421002814e4,0x480828420862,0x79f9803cde60079f9803cc001e60f307d4c002d901e63cc01e6f301e60f31e607987980f301e60f4586,0x10400410008004200180042008040401003018e4,0x10400410010005000180082008040401002010e4,0x10400410010004400180082008040401002010e4,0x79f9803cde60079f983cc3cc1e63cc222c0002d901e63cc25f8f301e60f320467987980f301e60f45e6,0x0,0x0],
[0x421090210481,0x0,0x0,0x79801e7e7e60079f9807980025f8001ed98002d901e63cc00f3f301e60f30f303cc7980f300f3816a16,0x10010400420004800180082008040401006072e4,0x10400406020004800180082008040401006030e4,0x10020400820004800180082008040401006034e4,0x421090210481,0x421090210481,0x421090210481,0x90200481,0x842190220501,0x90200481,0x842190220501,0x90200481,0x18ae7980001e603cc7981e621391e67980f3007a730079bcc007a73003d31e803cc0000408c001e64dc35,0x0,0x8090200481,0x20090200481,0x8090200481,0x0,0x0,0x1001040044000500018008200804040100a052e4,0x0,0x1002040084000500018008200804040100a054e4,0x20090200481,0x20090200481,0x20090200481,0x90200481,0x40090200481,0x90200481,0x40090200481],
[0x90200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_9229 : TreeBound (n := 4) 107 (programCode 0x422b07207d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x80c0b0220481,0x1e60798799e601e6079bcc01e6f307983cc01e6f30079bcc01e6f3003cc79803cde600f6cc001e703d95,0x80c0b0220481,0x0,0x84c1a1220501,0x20100800080002002000080402020020800814e3,0x84c1a1220501,0x844188220501,0x8541c2228501,0x20100800080002002000080002020020800814e3,0x8541c2228501,0x0,0x1e60f3079a22c1e601e9cc007a7307b69cc01e603cc7980f31e603cc3cc79803cde600f745801e740995,0x0,0x1e60f3079a22c1e6079bcc01e6f30811bcc01e60f307983cc1e607983cc79803cde600f745801e703d95,0x0,0x844188220501,0x844188220501,0x844188220501,0x844188220501,0x0,0x8140c1224481,0x8140c6238481,0x8140c1224481,0x8140c8220481,0x8140c2228481,0x8140c6238481,0x8140c2228481,0x0,0x8140c4230481,0x20010800480092002080080482020020480816e3],
[0x8140c4230481,0x0,0x8140c8220481,0x8140c6238481,0x8140c8220481,0x8140c8220481,0x3cc003dba983cfcc00408c0002d9000222c0002d901e63cc1e60f301e60f31e603cc7980f307d4febb56,0x1e6003d39803cde6007d4c001f53079fd4c0371d3001e9cc01e6f3003cc79800f4e600f745801e703375,0x0,0x1e67980799e601e60007983cc1e616c87983f99f3003cfcc01e6f3003cc79801e7e600f6cc001e703885,0x44021000800804020180202008040401008844e4,0x1e67980799e601e6001e60f307984459e607b66f30079bcc01e6f3003cc79803cde600f745801e726055,0x44021000801004040180202008040401008844e4,0x0,0x0,0x1e67980799e601e600f307983cc1ed98003cde6f30079bcc01e6f3003cc79803cde600f6cc001e722395,0x0,0x20000800004000180002008040401000000e4,0x8820200808004200180042008040401001108e4,0x20000800005000180002008040401000000e4,0x10820400810004400180082008040401002110e4,0x20000800004000180002008040401000000e4,0x20000820004800180002008040401000000e4,0x0,0x20000840005000180002008040401000000e4,0x1e601e67980799e601e9cc007a7307983cc01e6f30079bcc01e6f3003cc79803cde600f6cc001e740995,0xf4e60001e6000f4e9cc0002d9000222c0002d901e63cc1e60f301e60f31e603cc7980f30000001556,0x0,0x8204d0224481,0x821090230481,0x8204d0224481,0x20080802020082002080082002020020800814e3],
[0x820890228481,0x0,0x820890228481,0x0,0x821090230481,0x821090230481,0x821090230481,0x820090220481,0x822090220481,0x821090230481,0x822090220481,0x822090220481,0x0,0x8485b0220501,0x821090230481,0x8485b0220501,0x80022001004040180202008040401000000e4,0x0,0x0,0x10002000010008000100020000100000400020001000020040000202000000200400400001001000001004000010010000010004000010100000010040000101000000100228793a7,0x0,0x821090230481,0x821090230481,0x821090230481,0x800090220481,0x842190220501,0x800090220481,0x842190220501,0x842190220501,0x844190220501,0x804090220481,0x844190220501],
[0x844190220501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_9326 : TreeBound (n := 4) 107 (programCode 0x422b07207e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0xf3007d4c001e6f300b64001f5307983cc02d9000f6cc003ea6000f6cfcc001e600f3f300001e703885,0x7d4c001e6f300b640000f300003cc21b280001e60001e70d943cfcc000f30000f300001e703375,0xf3007d4c001e6f300b64001f5307983cc02d9001e9cc00f4e6001e9cfcc001e603ccf300001e703885,0x7d4c001e6f300b640000f300003cc21b280001e60001e6f3003cfcc000f30000f300001e703375,0x20200000081000000200200000c00020001000001004000000010000878000040020000100400000400800001001004000000210000004000040008000000010018843227,0x1e61e61e600001e697e3cc0002d9000222c0001e67b66007b660007b660f31e603cc003db30f30b65556,0x0,0x0,0x0,0x0,0x7d4c001e6f300b640000f300003cc21b283cc1e63cc1e607983cfcc000f3f300f300001e703375,0x0,0xf307d4c001e6f300b640002d900003cc21b29e601e67981e61e603cfcc000f4e600f300001e703375,0x7d4c001e6f300b640000f300003cc21b280001e63cc1e600f33cfcc000f3f300f300001e703375,0xf307d4c001e6f300b640002d900003cc21b29e601e7e601e63cc03cfcc000fa9800f300001e703375,0x7d4c001e6f300b640000f300003cc21b373001e60001e600003cfcc000f30000f300001e703375,0x1e600097e0007b66000b640002d9000222c0002d901e63cc1e60f301e60f31e603cc7980f30f30799556,0x0,0x4000000110000000402000000800c00001400020001000000104000200410000060000004100000010400000040800000101004000001010000004000004008100010010010873227,0x1e63cc1e60f301e688b3cc0002d9000222c0001e6111600111600011160f31e603cc1e60f30f30799556,0x0,0x1e63cc1e60f301e688b3cc0002d9000222c0001e6204600097e00020460f31e603cc1e60f30f30799556,0x0,0x1e6003ea60f301e688b3cc0002d9000222c0001e67b66007b660007b660f31e603cc003db30f30b6ced6,0x0,0x0,0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0,0x0,0x20000000880000001100000004100000014000000110000000440000000900000000c00188000000290000000a00000002100010003800020009000080004000200020001800edda8,0x80002002000080402000020000814e3,0x8200010ee080070200200000020000440000004100008770400020001000004000000804000004020000020100000020100400000041000e00200002001010000001002085aba7,0x4080200481,0x0,0x80002002000080002000020000814e3,0x0,0x0,0x0,0x0,0x10600830000002000000000400400000001000083004000200010000040000800040004000200020001000020001000000000410000002000000010100000010020852ba7,0x0,0x844188220501,0x4080200481,0x844188220501,0x4080200481,0x0,0x4000000210000000840000002002000008000060000000100100000600000001060040000100100000400400000801000001004000001010000004000004008100000010010873227,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1e600097e1e601e679800f3001f53001e6f3002d901e63cc007a7301e60f30079bcc7980f30f30799556],
[0x4000000210000000840000002002000008020020000080000000100200000200060040000100100000400400000801000001004000001010000004001000008100000010010873227,0x1e60020461e601e679801e6001ed9801e7e6002d901e63cc00f3f301e60f300f33cc7980f30f30816a16,0x0,0x0,0x0,0x1e60001e61e601e67980f3000222c001f530002d901e63cc0f30f301e60f303cc3cc7980f30f30799556,0x109d04e4001e600000003cc2139f300003cc00f3f30079bcc00f3f3003cfcc003cc00007980001e68a8c5,0x0,0x410800101040000404008000800c000010000060040000100100000600000001060040000100100000400400000801000001004000401010000004000004008100000010010873227,0x20400804000804020180202008040401004020e4,0x168f08f8e7000005a3c23e39c00000b4784d6afa3e39d69073c6314a0c0316f0909d246bab88786c6fa694776b47847c8a0f08f8e7000005a3c254c8c8f8e7b74a28e654e000168f0b164fd755a9961d1ac5bfb2367fbfcc43ab80000b4c198a5c9df4f8e7b4784d6afa3e39ed1e135abe8f8e75a3c29875e3e39cb4785e5640f8e70b478a2035be39c5a3c3a72a4f8e705a3c23e39c000005a3c23e39c0000168f08f8e868f0926067ae25d8e7005a41c7a5fd793e0a8cb23e40ccb2d09a6b5b40c39c002d1e2b97d0c83b7586fd,0x20400804001004040180202008040401004020e4,0x0,0x0,0xf300f33cc03ccf300798799e601ed98003cde6f30079bcc01e6f3003cc07983cc1e60f6cc001e703d95,0x0,0x20400804020004800180102008040401004020e4,0x20400805008004200180042008040401005028e4,0x20400804020005000180102008040401004020e4,0x20400806010004400180082008040401006030e4,0x410800101040000404008000800c000010040020040100000100400200001000060040000100100000400400000801000001004400001010000004004000008100000010010873227,0x20400804020004800180102008040401004020e4,0x2b3fb0d58a752b3fb02b3fb000acfec567f600acfec0360f9c159fd9037e200159fd82b3fb159fd800000057ae1dd00000582a74ea000001bb4ccc0000015d07fa6000002becaec00000040df8802b3fb0567f6035629d559fd802b3fb0567f600acfec159fd80081bf1567f600159fd8567f60d58a75159fd82b3fb00567f60567f60159fd80360f9c0acfed037e2002b3fb02b3fb01b07d0656a7dac,0x20400804040005000180102008040401004020e4,0x0,0x0,0x20020800800804020180202008040401004064e4,0x0,0x20020800801004040180202008040401004064e4,0x0,0x0,0x79800f379803cde6007f3200088b00008118002d90b643cc03ccf301e61e62d907987980f303cc1f70f6],
[0x0,0x79800f379803cde6007fb6e40798f3008118002d90c573cc03ccf301e61e6315c7987980f303cc1f70f6,0x2002080080800420018004200804040100502ce4,0x20020800820005000180102008040401004024e4,0x20020800810004400180082008040401006034e4,0x0,0x20020800820004800180102008040401004024e4,0x0,0x20020800840005000180102008040401004024e4,0x0,0x410800201040000804008002000c000080000060040000100100000400400001060040000100100000400400000801000001004000401010000004000004008000010010010873227,0x421090210481,0x2d1e11f1ce00000b47847c73800002d1e124c0a23e3a7479b294824a0cb62647c846b46bd7f21216766e947a31e11f1cf68f08f8e7000005a3c254c8c8f8e7b74a28e654e000168f0b164fd755a9961d1ac5bfb23674784a99191f1ceb4c198a5c9df4f8e7b4784d6afa3e39ed1e135abe8f8e75a3c29875e3e39cb4785e5640f8e70b478a2035be39c5a3c3a72a4f8e705a3c23e39c000005a3c23e39c0000168f08f8e868f0926067ae25d8e7005a41c7a5fd793e0a8cb23e40ccb2d09a111f1ceb4784a991ab97d0c83b7586fd,0x20400804001004040180202008040401004020e4,0x420890208481,0x0,0x420890208481,0x0,0x421090210481,0x421090210481,0x421090210481,0x420090200481,0x422090220481,0x421090210481,0x422090220481,0x420090200481,0x109d04e4001e600000003cc2139f300003cc00f3f30079bcc00f3f3003cfcc003cc00007980001e68a8c5,0x0,0x0,0x421090210481,0x0,0x80002000002002080082002000020000814e3],
[0x420890208481,0x0,0x420890208481,0x0,0x421090210481,0x421090210481,0x421090210481,0x420090200481,0x422090220481,0x421090210481,0x422090220481,0x420090200481,0x0,0x0,0x421090210481,0x0,0x20080802001004040180202008040401004030e4,0x0,0x0,0x79807987981e61e603d1b200088b00008118002d90b643cc03ccf301e61e62d907987980f303cc2615f6,0x0,0x421090210481,0x421090210481,0x421090210481,0x90200481,0x842190220501,0x90200481,0x842190220501,0x90200481,0x844190220501,0x4090200481,0x844190220501],
[0x4090200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_9487 : TreeBound (n := 4) 107 (programCode 0x422b07207f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x80c0b0220481,0x1e60001e61e603cc0d4dcc0000f307983cc035373001e9cc01e6f3003cc79800fa9800f7bf001e703375,0x80c0b0220481,0x7983cc1e62d903cc7983cc0f30f30b643cc01e6f30079bcc01e6f3003cde6003d39800f8b2001ee9bd95,0x0,0x8140c1224481,0x8140c6238481,0x8140c1224481,0x8140c8220481,0x8140c2228481,0x8140c6238481,0x8140c2228481,0x0,0x8140c4230481,0x40011000480092002080080482040020480816e3,0x8140c4230481,0x1000000201000004010000002020000008400000401000000404000200210000028800000080100000080400000801000001000000000801000000810000008120000010012860e27,0x8140c8220481,0x8140c6238481,0x8140c8220481,0x8140c8220481,0x0,0x40021000880022002000880022040020020814e3,0x40001000080002002000080402040020000814e3,0x40021000880022002001080042040020040814e3,0x40001000080002002040081002040020000814e3,0x0,0x40001000080002002000080002040020000814e3,0x7980799e601e63cc811bcc01e6f307983cc01e601e67980799e600f33cde6003d39800f6cc001e703d95,0x0,0x7980799e601e63cc811bcc01e6f307983cc01e603cc7980f31e603cc3cde6003d39800f6cc001e703d95],
[0x0,0x40001000080002002010080402040020000814e3,0x0,0x40001000080002002020080802040020000814e3,0x40001000080002002000080002040020000814e3,0x40001000080002002040081002040020000814e3,0x40001000080002002040080002040020000814e3,0x3cc007b66003cfcc007d4c001f5307a76cc02d9f3003cfcc01e6f3003ccf3001ed9800f6cc001e703885,0x0,0x0,0x0,0x3cc1e61e60f303cc7983cc0798f30d4a3cc02d9001e9cc00f4e6001e9ccf3001ed9800f9a5001f267885,0x0,0x0,0x0,0x3cc007b66003cfcc7983cc001f53085dacc02d900f33cc0799e600f33ccf3001ed9800f6d7641e703885,0x0,0x0,0x0,0x0,0x0,0x1e61e61e607983cc97e3cc0798f3097e3cc294a9e601e67981e61e603cc79800fa9800f9a5001eacf375,0x0,0x2000088000a00010060000804040100000104,0x7983cc1e62d903cc7983cc0f30f30b643cc01e67980799e601e76c803cde6003d39800f8b2001ee9bd95,0x79801e7e60079bcc01e9cc007a7307983cc01e6f30079bcc01e6f3003cde6003d39800f6cc001e740995,0x0,0x1e6007b66001e9cc8743803cde6016cf9805e91d3001e9cc01e6f3003cc79800fa9800f7bf3cde703375,0x821090230481,0x3cc007b66003cfcc865080799e60446ec807c59f3003cfcc01e6f3003ccf3001ed9800f6cd6c9e703885,0x40040041001004040180202008040401008048e4,0x820890228481],
[0x0,0x820890228481,0x0,0x821090230481,0x821090230481,0x821090230481,0x820090220481,0x822090220481,0x821090230481,0x822090220481,0x822090220481,0x7980799e601e63cc03cfcc01e6f307983cc01e6f30079bcc01e6f3003cde6003d39800f6cc001e703d95,0x0,0x8485b0220501,0x821090230481,0x8485b0220501,0x40080042001004040180202008040401008050e4,0x0,0x0,0x0,0x0,0x821090230481,0x821090230481,0x821090230481,0x800090220481,0x842190220501,0x800090220481,0x842190220501,0x842190220501,0x844190220501,0x804090220481,0x844190220501],
[0x844190220501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_9584 : TreeBound (n := 4) 107 (programCode 0x422b072080) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0xc090200481,0x0,0x3cc00097e0007d4c000b643cc1e63cc222c3cc2d901e63cc25f8f301e60f32d907987980f30f307995e6,0x421090210481,0xf372b8d40000f301e7e60114a3500f33cc079fa730079bcc007a73003cfcda97cc00003cc0799e64dc35,0x2000002002080082002000020000814e3,0x0,0x0,0x0,0x0,0x421090210481,0x421090210481,0x421090210481,0x20090200481,0x822090220481,0x421090210481,0x822090220481,0x20090200481,0xc090200481,0x0,0xc081200481,0x80002002000080402000020000814e3,0xc081200481,0x4080200481,0x214082208481,0x80002002000080002000020000814e3,0x214082208481,0x0,0x0,0x0,0x0],
[0x0,0x44088200481,0x4080200481,0x44088200481,0x4080200481,0x0,0x1140c1204481,0x0,0x1140c1204481,0x14080200481,0x214082208481,0x10000480002002000080002000020000814e3,0x214082208481,0x0,0x0,0x10000480002002080080002000020000814e3,0x0,0x0,0x8140c8220481,0x0,0x8140c8220481,0x14080200481,0xf3084e4001e600000003cc2139f300003cc00f3f30079bcc00f3f3003cfcc003cc00007980001e68a8c5,0x0,0x1140c1204481,0x20000880002002000080402000020000814e3,0x1140c1204481,0x14080200481,0x214082208481,0x20000880002002000080002000020000814e3,0x214082208481,0x0],
[0x0,0x0,0x0,0x0,0x8140c8220481,0x20000880002002000080402000020000814e3,0x8140c8220481,0x14080200481,0x0,0x0,0x40021000800804020180202008040401008044e4,0xf3079ad901e60000000f311439001e600007a73f30079bcc00f3f3003cfcc003cc00007980001e68a8c5,0x40021000801004040180202008040401008044e4,0x0,0x0,0x0,0x0,0x3b9aca0077536165003ba9b0b2801dce536b2801dcf41d65003b9aca00000060dd65165077359400001dcda09aca00fd51da800059682f00000773598a817e5cd65ee6b2f73595dcd66dcd650ee6b36e6b639aca7735a6a05f5b9acdb9aca3b9ad8e6b2877359b73597bd68f6a50a,0x4002100080800420018004200804040100904ce4,0x40021000840005000180202008040401008044e4,0x4002100081000440018008200804040100a054e4,0x0,0x40021000820004800180202008040401008044e4,0xf30d4a0001e600001e61e621393cc0000f300f3f30079bcc00f3f3003cfcc003cc00007980001e68a8c5,0x40021000840005000180202008040401008044e4,0x0,0x1204d0204481,0x421090210481,0x1204d0204481,0x0,0x0,0x40001080000002080082002000020000814e3],
[0x0,0x0,0x421090210481,0x421090210481,0x421090210481,0x20090200481,0x822090220481,0x421090210481,0x822090220481,0x20090200481,0xf3084e4001e600000003cc2139f300003cc00f3f30079bcc00f3f3003cfcc003cc00007980001e68a8c5,0x0,0x1204d0204481,0x421090210481,0x1204d0204481,0x80002000002002080082002000020000814e3,0x0,0x0,0x0,0x0,0x421090210481,0x421090210481,0x421090210481,0x20090200481,0x822090220481,0x421090210481,0x822090220481,0x20090200481,0x0,0x8490200481,0x421090210481,0x8490200481],
[0x40081002001004040180202008040401008050e4,0x0,0x0,0x0,0x0,0x421090210481,0x421090210481,0x421090210481,0x90200481,0x42090200481,0x90200481,0x42090200481,0x90200481,0x44090200481,0x4090200481,0x44090200481,0x4090200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_7584 : TreeBound (n := 4) 107 (programCode 0x422b0720) := by
  conv in programCode _ => reduce
  exact branchFour (k := (3,1)) (by decide +kernel) part100_7585 part100_7730 part100_7891 part100_7892 part100_8101 part100_8278 part100_8439 part100_8600 part100_8793 part100_8954 part100_8955 part100_9100 part100_9229 part100_9326 part100_9487 part100_9584

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part100_0 : TreeBound (n := 4) 107 (programCode 0x422b07) := by
  conv in programCode _ => reduce
  exact branchFour (k := (0,1)) (by decide +kernel) part100_1 part100_2 part100_3 part100_4 part100_1125 part100_1126 part100_1687 part100_1688 part100_3177 part100_3178 part100_3723 part100_3724 part100_4877 part100_5518 part100_6639 part100_7584

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem partitioned100 : TreeBound (n := 4) 107 [((0,0),⟨1,1,false⟩),((1,0),⟨2,1,false⟩),((2,0),⟨0,0,true⟩)] := part100_0
open Turing Turing.BusyBeaver in
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem one_zero_return_0_machine (M : Machine (Fin 2) (Fin 4))
    (h0 : M 0 0 = some (some 1, Stmt.write 1 .right))
    (h1 : M 1 0 = some (some 2, Stmt.write 1 .right))
    (h2 : M 2 0 = some (some 0, Stmt.write 0 .left))
    (halts : M.IsHalting) : M.HaltsAfter (Machine.init []) 107 := by
  have hm : Matches M
      [((0,0), ⟨1,1,false⟩),((1,0), ⟨2,1,false⟩),((2,0), ⟨0,0,true⟩)] := by
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
  rcases partitioned100 M hm with h | h
  · exact h
  · exact (h halts).elim

end BeaverBound


theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H2_R1_H3_R1.H1 := BeaverBound.one_zero_return_0_machine
