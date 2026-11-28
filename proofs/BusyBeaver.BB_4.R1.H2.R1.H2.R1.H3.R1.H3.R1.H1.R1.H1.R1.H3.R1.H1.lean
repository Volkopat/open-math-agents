import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H3_R1_H1_R1_H1_R1_H3_R1

/-!
FAR nonhalting certificates for write-0 transition at state 1 blank, hole at (2, 1).
Every machine in this branch either halts at the missing (1, 1) entry within
107 steps or hits a leaf certified by a finite automaton invariant.
-/

namespace OMA.BB4HoleS2A0

open Turing Turing.BusyBeaver

abbrev Symbol := Fin 2
abbrev State := Fin 4
abbrev Machine4 := Machine Symbol State

structure Move where
  state : State
  write : Symbol
  left : Bool
  deriving DecidableEq

structure Table where
  t00 : Option Move
  t01 : Option Move
  t10 : Option Move
  t11 : Option Move
  t20 : Option Move
  t21 : Option Move
  t30 : Option Move
  t31 : Option Move

def Table.get (tb : Table) (q : State) (a : Symbol) : Option Move :=
  match q.val, a.val with
  | 0, 0 => tb.t00
  | 0, _ => tb.t01
  | 1, 0 => tb.t10
  | 1, _ => tb.t11
  | 2, 0 => tb.t20
  | 2, _ => tb.t21
  | _, 0 => tb.t30
  | _, _ => tb.t31

def Table.set (tb : Table) (q : State) (a : Symbol) (m : Move) : Table :=
  match q.val, a.val with
  | 0, 0 => { tb with t00 := some m }
  | 0, _ => { tb with t01 := some m }
  | 1, 0 => { tb with t10 := some m }
  | 1, _ => { tb with t11 := some m }
  | 2, 0 => { tb with t20 := some m }
  | 2, _ => { tb with t21 := some m }
  | _, 0 => { tb with t30 := some m }
  | _, _ => { tb with t31 := some m }

def Move.flip (m : Move) : Move := { m with left := !m.left }

def Table.flip (tb : Table) : Table :=
  ⟨tb.t00.map Move.flip, tb.t01.map Move.flip,
   tb.t10.map Move.flip, tb.t11.map Move.flip,
   tb.t20.map Move.flip, tb.t21.map Move.flip,
   tb.t30.map Move.flip, tb.t31.map Move.flip⟩

theorem Table.get_set_self (tb : Table) (q : State) (a : Symbol) (m : Move) :
    (tb.set q a m).get q a = some m := by
  fin_cases q <;> fin_cases a <;> rfl

theorem Table.get_set_ne (tb : Table) {q q' : State} {a a' : Symbol} (m : Move)
    (h : (q', a') ≠ (q, a)) : (tb.set q a m).get q' a' = tb.get q' a' := by
  fin_cases q <;> fin_cases a <;> fin_cases q' <;> fin_cases a' <;>
    first | rfl | exact absurd rfl h

theorem Table.get_flip (tb : Table) (q : State) (a : Symbol) :
    tb.flip.get q a = (tb.get q a).map Move.flip := by
  fin_cases q <;> fin_cases a <;> rfl

structure Position where
  state : State
  ls : List Symbol
  head : Symbol
  rs : List Symbol
  deriving DecidableEq

def startPos : Position := ⟨0, [], 0, []⟩

def push (a : Symbol) (xs : List Symbol) : List Symbol :=
  match a.val, xs with
  | 0, [] => []
  | _, xs => a :: xs

def symHead : List Symbol → Symbol
  | [] => 0
  | x :: _ => x

theorem symHead_eq_headI (xs : List Symbol) : symHead xs = xs.headI := by
  cases xs <;> rfl

def Position.move (c : Position) (m : Move) : Position :=
  if m.left then ⟨m.state, c.ls.tail, symHead c.ls, push m.write c.rs⟩
  else ⟨m.state, push m.write c.ls, symHead c.rs, c.rs.tail⟩

theorem mk_push (a : Symbol) (xs : List Symbol) :
    ListBlank.mk (push a xs) = (ListBlank.mk xs).cons a := by
  fin_cases a
  · cases xs with
    | nil => exact (ListBlank.cons_head_tail (ListBlank.mk ([] : List Symbol))).symm
    | cons x xs => exact (ListBlank.cons_mk 0 (x :: xs)).symm
  · exact (ListBlank.cons_mk 1 xs).symm

def Position.view (c : Position) : Cfg Symbol State :=
  ⟨some c.state, ⟨c.head, ListBlank.mk c.ls, ListBlank.mk c.rs⟩⟩

theorem view_start : startPos.view = Machine.init [] := rfl

def Move.command (m : Move) : Option (Option State × Stmt Symbol) :=
  some (some m.state, Stmt.write m.write (if m.left then Dir.left else Dir.right))

def Matches (M : Machine4) (tb : Table) : Prop :=
  ∀ q a m, tb.get q a = some m → M q a = m.command

theorem matches_set {M : Machine4} {tb : Table} {q : State} {a : Symbol} {m : Move}
    (hm : Matches M tb) (h : M q a = m.command) : Matches M (tb.set q a m) := by
  intro q' a' m' hh
  by_cases e : (q', a') = (q, a)
  · rcases Prod.mk.inj e with ⟨rfl, rfl⟩
    rw [Table.get_set_self] at hh
    exact (Option.some.inj hh) ▸ h
  · rw [Table.get_set_ne tb m e] at hh
    exact hm q' a' m' hh

theorem step_move {M : Machine4} {tb : Table} (hm : Matches M tb) (c : Position) (m : Move)
    (h : tb.get c.state c.head = some m) :
    M.step c.view = some (c.move m).view := by
  have he := hm c.state c.head m h
  cases m with
  | mk q a d =>
    cases d <;> simp [Position.view, Machine.step, he, Move.command, Position.move,
      Tape.write, Tape.move, mk_push, symHead_eq_headI]

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

structure Certificate where
  mirror : Bool
  dfa : TapeDFA
  edges : ℕ
  blankReach : ℕ

abbrev Node (cert : Certificate) := Option (State × Fin cert.dfa.size)

def nodeId (cert : Certificate) : Node cert → ℕ
  | none => 4 * cert.dfa.size
  | some (q, l) => q.val * cert.dfa.size + l.val

def Certificate.edgeRow (cert : Certificate) (p : Node cert) (a : Symbol) : ℕ :=
  match p with
  | none => 2 ^ (4 * cert.dfa.size)
  | some _ => (cert.edges / 2 ^ ((2 * nodeId cert p + a.val) * (4 * cert.dfa.size + 1))) %
      2 ^ (4 * cert.dfa.size + 1)

def Certificate.edge (cert : Certificate) (p : Node cert) (a : Symbol)
    (q : Node cert) : Bool :=
  (cert.edgeRow p a).testBit (nodeId cert q)

theorem edge_none (cert : Certificate) (a : Symbol) (q : Node cert) :
    cert.edge none a q = q.isNone := by
  unfold Certificate.edge Certificate.edgeRow
  simp only [Nat.testBit_two_pow]
  rcases q with _ | ⟨q, l⟩
  · simp [nodeId]
  · have hq : q.val ≤ 3 := Nat.le_of_lt_succ q.isLt
    have hne : 4 * cert.dfa.size ≠ q.val * cert.dfa.size + l.val := by
      have : q.val * cert.dfa.size ≤ 3 * cert.dfa.size := Nat.mul_le_mul_right _ hq
      omega
    simp [nodeId, hne]

def Certificate.onBlank (cert : Certificate) (p : Node cert) : Bool :=
  cert.blankReach.testBit (nodeId cert p)

def unpack (val : ℕ) : Certificate :=
  let extra := val / 2 % 16
  let size := extra + 1
  let dfaBase := size ^ (2 * size - 1)
  let payload := val / 32 / dfaBase
  let width := 4 * size + 1
  let initialBase := 2 ^ width
  ⟨val % 2 == 1, ⟨extra, val / 32 % dfaBase⟩, payload / initialBase, payload % initialBase⟩

def nodes (cert : Certificate) : List (Node cert) :=
  none :: (List.finRange 4).flatMap fun q =>
    (List.finRange cert.dfa.size).map fun l => some (q, l)

theorem allFin {n : ℕ} {p : Fin n → Bool} (h : (List.finRange n).all p = true)
    (a : Fin n) : p a = true := (List.all_eq_true.mp h) a (by simp)

theorem allNodes {cert : Certificate} {p : Node cert → Bool}
    (h : (nodes cert).all p = true) (a : Node cert) : p a = true := by
  refine (List.all_eq_true.mp h) a ?_
  rcases a with _ | ⟨q, l⟩ <;> simp [nodes]

def checkBlank (cert : Certificate) : Bool :=
  cert.onBlank (some (0, 0)) && !cert.onBlank none &&
    (nodes cert).all fun p =>
      if cert.onBlank p then
        let row := cert.edgeRow p 0
        (nodes cert).all fun q => !row.testBit (nodeId cert q) || cert.onBlank q
      else true

def checkAt (tb : Table) (cert : Certificate) (q : State) (a : Symbol)
    (l : Fin cert.dfa.size) : Bool :=
  let p : Node cert := some (q, l)
  let pRow := cert.edgeRow p a
  match tb.get q a with
  | none => pRow.testBit (4 * cert.dfa.size)
  | some m =>
    if m.left then
      (List.finRange cert.dfa.size).all fun l' => (List.finRange 2).all fun a' =>
        if Nat.beq (cert.dfa.next a' l').val l.val then
          let sRow := cert.edgeRow (some (m.state, l')) a'
          (nodes cert).all fun s =>
            if sRow.testBit (nodeId cert s) then
              let swRow := cert.edgeRow s m.write
              (nodes cert).all fun t => !swRow.testBit (nodeId cert t) || pRow.testBit (nodeId cert t)
            else true
        else true
    else pRow.testBit (nodeId cert (some (m.state, cert.dfa.next m.write l)))

def checkMachine (tb : Table) (cert : Certificate) : Bool :=
  (List.finRange 4).all fun q => (List.finRange 2).all fun a =>
    (List.finRange cert.dfa.size).all fun l => checkAt tb cert q a l

def checkCertificate (tb : Table) (val : ℕ) : Bool :=
  let C := unpack val
  checkBlank C && checkMachine (if C.mirror then tb.flip else tb) C

def CertProp (N : Machine4) : Prop :=
  ∃ (n m : ℕ) (x : Fin n) (y : Fin m) (L : Fin 2 → Fin n → Fin n)
      (R : Fin 2 → Fin m → Fin m) (S : Fin 4 → Fin 2 → Fin n → Fin m → Bool),
      L 0 x = x ∧ R 0 y = y ∧ S 0 0 x y = true ∧
      ∀ q a s t i j, S q a (L s i) (R t j) = true →
        ∃ r w d, N q a = some (some r, Stmt.write w d) ∧
          (match d with
           | .left => S r s i (R w (R t j))
           | .right => S r t (L w (L s i)) j) = true

section CertSound
open Classical in
private def stepSubset (cert : Certificate) (a : Symbol) (B : Node cert → Bool) : Node cert → Bool :=
  fun p => decide (p = none ∨ ∃ q : Node cert, B q = true ∧ cert.edge p a q = true)

private theorem stepSubset_mono {cert : Certificate} {a : Symbol} {B₁ B₂ : Node cert → Bool}
    (hle : ∀ p, B₁ p = true → B₂ p = true) :
    ∀ p, stepSubset cert a B₁ p = true → stepSubset cert a B₂ p = true := by
  intro p hp
  simp only [stepSubset, decide_eq_true_eq] at hp ⊢
  rcases hp with rfl | ⟨q, hq, he⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨q, hle q hq, he⟩

private theorem iter_fixpoint {α : Type} [Fintype α] [DecidableEq α]
    (f : (α → Bool) → (α → Bool))
    (hmono : ∀ B₁ B₂, (∀ p, B₁ p = true → B₂ p = true) → ∀ p, f B₁ p = true → f B₂ p = true) :
    let B := f^[Fintype.card α] (fun _ => false)
    f B = B := by
  have hle_step : ∀ k p, (f^[k] (fun _ => false)) p = true → (f^[k + 1] (fun _ => false)) p = true := by
    intro k
    induction k with
    | zero => intro p hp; simp at hp
    | succ k ih =>
      intro p hp
      rw [Function.iterate_succ_apply'] at hp ⊢
      exact hmono _ _ ih p hp
  have hcard_le : ∀ k, (Finset.univ.filter fun p => (f^[k] (fun _ => false)) p = true).card ≤ Fintype.card α :=
    fun k => Finset.card_filter_le _ _ |>.trans (by simp)
  by_contra hne
  have hstrict : ∀ k ≤ Fintype.card α,
      k ≤ (Finset.univ.filter fun p => (f^[k] (fun _ => false)) p = true).card := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have hk' : k ≤ Fintype.card α := Nat.le_of_succ_le hk
      have ihk := ih hk'
      have hne_k : f^[k] (fun _ => false) ≠ f^[k + 1] (fun _ => false) := by
        intro heq
        apply hne
        have heq' : f (f^[k] (fun _ => false)) = f^[k] (fun _ => false) := by
          simpa [Function.iterate_succ_apply'] using heq.symm
        have hstay : ∀ m, f^[k + m] (fun _ => false) = f^[k] (fun _ => false) := by
          intro m
          induction m with
          | zero => rfl
          | succ m ihm =>
            rw [← Nat.add_assoc, Function.iterate_succ_apply', ihm]
            exact heq'
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hk'
        have h1 : f^[Fintype.card α] (fun _ => false) = f^[k] (fun _ => false) := by
          rw [hd]; exact hstay d
        have h2 : f^[Fintype.card α + 1] (fun _ => false) = f^[k] (fun _ => false) := by
          rw [hd, Nat.add_assoc]; exact hstay (d + 1)
        change f (f^[Fintype.card α] (fun _ => false)) = f^[Fintype.card α] (fun _ => false)
        rw [← Function.iterate_succ_apply' f (Fintype.card α), h1, h2]
      have hex : ∃ p, (f^[k] (fun _ => false)) p = false ∧ (f^[k + 1] (fun _ => false)) p = true := by
        by_contra hall
        push Not at hall
        apply hne_k
        funext p
        cases hpk : (f^[k] (fun _ => false)) p
        · cases hpk1 : (f^[k + 1] (fun _ => false)) p
          · rfl
          · exact absurd hpk1 (by simp [hall p hpk])
        · exact (hle_step k p hpk).symm
      obtain ⟨p, hp0, hp1⟩ := hex
      have hsub : (Finset.univ.filter fun q => (f^[k] (fun _ => false)) q = true) ⊂
          (Finset.univ.filter fun q => (f^[k + 1] (fun _ => false)) q = true) := by
        rw [Finset.ssubset_iff_of_subset]
        · exact ⟨p, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hp1,
            by simp only [Finset.mem_filter, Finset.mem_univ, true_and, hp0]; exact Bool.false_ne_true⟩
        · intro q hq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
          exact hle_step k q hq
      have hlt := Finset.card_lt_card hsub
      omega
  have hfull := hstrict (Fintype.card α) (le_refl _)
  have hle_full := hcard_le (Fintype.card α)
  have heq_card : (Finset.univ.filter fun p => (f^[Fintype.card α] (fun _ => false)) p = true).card = Fintype.card α :=
    le_antisymm hle_full hfull
  have hall_true : ∀ p, (f^[Fintype.card α] (fun _ => false)) p = true := by
    have hset := Finset.eq_univ_of_card _ (by simpa using heq_card)
    intro p
    have hp : p ∈ Finset.univ.filter fun q => (f^[Fintype.card α] (fun _ => false)) q = true := by
      rw [hset]; exact Finset.mem_univ p
    simpa using hp
  apply hne
  funext p
  change f (f^[Fintype.card α] (fun _ => false)) p = f^[Fintype.card α] (fun _ => false) p
  have hp' := hle_step (Fintype.card α) p (hall_true p)
  rw [Function.iterate_succ_apply'] at hp'
  rw [hall_true p, hp']

private theorem fixpoint_sub_onBlank {cert : Certificate} (hb : checkBlank cert = true) :
    let B := (stepSubset cert 0)^[Fintype.card (Node cert)] (fun _ => false)
    ∀ p, B p = true → cert.onBlank p = false := by
  simp only [checkBlank, Bool.and_eq_true_iff, Bool.not_eq_true_eq_eq_false] at hb
  obtain ⟨⟨_, hsink⟩, hclosure⟩ := hb
  intro B p hp
  have hstep : ∀ (C : Node cert → Bool), (∀ q, C q = true → cert.onBlank q = false) →
      ∀ q, stepSubset cert 0 C q = true → cert.onBlank q = false := by
    intro C hC q hq
    simp only [stepSubset, decide_eq_true_eq] at hq
    rcases hq with rfl | ⟨r, hr, he⟩
    · exact hsink
    · have hr0 := hC r hr
      cases hqb : cert.onBlank q
      · rfl
      · have ht := allNodes hclosure q
        simp only [hqb, if_true] at ht
        have hn := allNodes ht r
        have he0 : (cert.edgeRow q 0).testBit (nodeId cert r) = true := he
        simp [he0, hr0] at hn
  have hind : ∀ k q, ((stepSubset cert 0)^[k] (fun _ => false)) q = true → cert.onBlank q = false := by
    intro k
    induction k with
    | zero => intro q hq; simp at hq
    | succ k ih =>
      intro q hq
      rw [Function.iterate_succ_apply'] at hq
      exact hstep _ ih q hq
  exact hind _ p hp

private theorem cert_of_unflipped {N : Machine4} {tb : Table} {cert : Certificate}
    (hm : Matches N tb) (hb : checkBlank cert = true) (hc : checkMachine tb cert = true) :
    CertProp N := by
  classical
  have hstart_blank : cert.onBlank (some (0, 0)) = true := by
    simp only [checkBlank, Bool.and_eq_true_iff] at hb
    exact hb.1.1
  let B := (stepSubset cert 0)^[Fintype.card (Node cert)] (fun _ => false)
  have hBfix : stepSubset cert 0 B = B :=
    iter_fixpoint (stepSubset cert 0) (fun _ _ h => stepSubset_mono h)
  have hBsub : ∀ p, B p = true → cert.onBlank p = false := fixpoint_sub_onBlank hb
  have hB00 : B (some (0, 0)) = false := by
    cases h : B (some (0, 0))
    · rfl
    · have := hBsub (some (0, 0)) h
      rw [hstart_blank] at this
      exact Bool.noConfusion this
  let E := Fintype.equivFin (Node cert → Bool)
  let n := cert.dfa.size
  let m := Fintype.card (Node cert → Bool)
  let x : Fin n := ⟨0, Nat.succ_pos _⟩
  let y : Fin m := E B
  let L : Fin 2 → Fin n → Fin n := cert.dfa.next
  let R : Fin 2 → Fin m → Fin m := fun a j => E (stepSubset cert a (E.symm j))
  let S : Fin 4 → Fin 2 → Fin n → Fin m → Bool :=
    fun q a i j => decide (∀ u : Node cert, (E.symm j) u = true → cert.edge (some (q, i)) a u = false)
  refine ⟨n, m, x, y, L, R, S, ?_, ?_, ?_, ?_⟩
  · exact cert.dfa.blank
  · simp [R, y, Equiv.symm_apply_apply, hBfix]
  · simp only [S, y, Equiv.symm_apply_apply]
    rw [decide_eq_true_eq]
    intro u hu
    by_contra he
    have he1 : cert.edge (some ((0 : State), x)) 0 u = true := by
      cases h : cert.edge (some ((0 : State), x)) 0 u
      · exact absurd h he
      · rfl
    have h00 : stepSubset cert 0 B (some (0, 0)) = true := by
      simp only [stepSubset, decide_eq_true_eq]; exact Or.inr ⟨u, hu, he1⟩
    rw [hBfix] at h00
    rw [hB00] at h00
    exact Bool.noConfusion h00
  · intro q a s t i j hS
    simp only [S, R, Equiv.symm_apply_apply, decide_eq_true_eq] at hS
    let l : Fin n := L s i
    let Bj : Node cert → Bool := stepSubset cert t (E.symm j)
    have hBnone : Bj none = true := by simp [Bj, stepSubset]
    have hchk := allFin (allFin (allFin hc q) a) l
    simp only [checkAt] at hchk
    cases hget : tb.get q a with
    | none =>
      simp only [hget] at hchk
      have he : cert.edge (some (q, l)) a none = true := hchk
      have hf := hS none hBnone; rw [he] at hf; exact Bool.noConfusion hf
    | some mv =>
      simp only [hget] at hchk
      refine ⟨mv.state, mv.write, if mv.left then .left else .right, ?_, ?_⟩
      · simpa [Move.command] using hm q a mv hget
      · cases hleft : mv.left with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, S]
          rw [decide_eq_true_eq]
          intro u hu
          by_contra he_step
          have he_step1 : cert.edge (some (mv.state, L mv.write l)) t u = true := by
            cases h : cert.edge (some (mv.state, L mv.write l)) t u
            · exact absurd h he_step
            · rfl
          have huBj : Bj (some (mv.state, L mv.write l)) = true := by
            simp only [Bj, stepSubset, decide_eq_true_eq]
            exact Or.inr ⟨u, hu, he_step1⟩
          simp only [hleft, Bool.false_eq_true, ↓reduceIte] at hchk
          have he_q : cert.edge (some (q, l)) a (some (mv.state, L mv.write l)) = true := hchk
          have hf := hS _ huBj; rw [he_q] at hf; exact Bool.noConfusion hf
        | true =>
          simp only [↓reduceIte, S, R, Equiv.symm_apply_apply]
          rw [decide_eq_true_eq]
          intro u' hu'
          by_contra he_u'
          have he_u'1 : cert.edge (some (mv.state, i)) s u' = true := by
            cases h : cert.edge (some (mv.state, i)) s u'
            · exact absurd h he_u'
            · rfl
          simp only [stepSubset, decide_eq_true_eq] at hu'
          have hex : ∃ z : Node cert, Bj z = true ∧ cert.edge u' mv.write z = true := by
            rcases hu' with rfl | ⟨z, hz, hez⟩
            · exact ⟨none, hBnone, by simp [edge_none]⟩
            · exact ⟨z, by simp only [Bj, stepSubset, decide_eq_true_eq]; exact hz, hez⟩
          obtain ⟨z, hzBj, hez⟩ := hex
          simp only [hleft, ↓reduceIte] at hchk
          have h1 := allFin (allFin hchk i) s
          have hbeq : Nat.beq (cert.dfa.next s i).val l.val = true := by
            simp [l, L]
          simp only [hbeq, ↓reduceIte] at h1
          have h2 := allNodes h1 u'
          have he_u'' : (cert.edgeRow (some (mv.state, i)) s).testBit (nodeId cert u') = true := he_u'1
          simp only [he_u'', ↓reduceIte] at h2
          have h3 := allNodes h2 z
          have hez' : (cert.edgeRow u' mv.write).testBit (nodeId cert z) = true := hez
          simp only [hez', Bool.not_true, Bool.false_or] at h3
          have hf := hS z hzBj; change cert.edge (some (q, L s i)) a z = true at h3; rw [h3] at hf; exact Bool.noConfusion hf

private theorem cert_of_flipped {N : Machine4} {tb : Table} {cert : Certificate}
    (hm : Matches N tb) (hb : checkBlank cert = true) (hc : checkMachine tb.flip cert = true) :
    CertProp N := by
  classical
  have hstart_blank : cert.onBlank (some (0, 0)) = true := by
    simp only [checkBlank, Bool.and_eq_true_iff] at hb
    exact hb.1.1
  let B := (stepSubset cert 0)^[Fintype.card (Node cert)] (fun _ => false)
  have hBfix : stepSubset cert 0 B = B :=
    iter_fixpoint (stepSubset cert 0) (fun _ _ h => stepSubset_mono h)
  have hBsub : ∀ p, B p = true → cert.onBlank p = false := fixpoint_sub_onBlank hb
  have hB00 : B (some (0, 0)) = false := by
    cases h : B (some (0, 0))
    · rfl
    · have := hBsub (some (0, 0)) h
      rw [hstart_blank] at this
      exact Bool.noConfusion this
  let E := Fintype.equivFin (Node cert → Bool)
  let n := Fintype.card (Node cert → Bool)
  let m := cert.dfa.size
  let x : Fin n := E B
  let y : Fin m := ⟨0, Nat.succ_pos _⟩
  let L : Fin 2 → Fin n → Fin n := fun a i => E (stepSubset cert a (E.symm i))
  let R : Fin 2 → Fin m → Fin m := cert.dfa.next
  let S : Fin 4 → Fin 2 → Fin n → Fin m → Bool :=
    fun q a i j => decide (∀ u : Node cert, (E.symm i) u = true → cert.edge (some (q, j)) a u = false)
  refine ⟨n, m, x, y, L, R, S, ?_, ?_, ?_, ?_⟩
  · simp [L, x, Equiv.symm_apply_apply, hBfix]
  · exact cert.dfa.blank
  · simp only [S, x, Equiv.symm_apply_apply]
    rw [decide_eq_true_eq]
    intro u hu
    by_contra he
    have he1 : cert.edge (some ((0 : State), y)) 0 u = true := by
      cases h : cert.edge (some ((0 : State), y)) 0 u
      · exact absurd h he
      · rfl
    have h00 : stepSubset cert 0 B (some (0, 0)) = true := by
      simp only [stepSubset, decide_eq_true_eq]; exact Or.inr ⟨u, hu, he1⟩
    rw [hBfix] at h00
    rw [hB00] at h00
    exact Bool.noConfusion h00
  · intro q a s t i j hS
    simp only [S, L, Equiv.symm_apply_apply, decide_eq_true_eq] at hS
    let Bi : Node cert → Bool := stepSubset cert s (E.symm i)
    let r' : Fin m := R t j
    have hBnone : Bi none = true := by simp [Bi, stepSubset]
    have hchk := allFin (allFin (allFin hc q) a) r'
    simp only [checkAt, Table.get_flip] at hchk
    cases hget : tb.get q a with
    | none =>
      simp only [hget, Option.map_none] at hchk
      have he : cert.edge (some (q, r')) a none = true := hchk
      have hf := hS none hBnone; rw [he] at hf; exact Bool.noConfusion hf
    | some mv =>
      simp only [hget, Option.map_some] at hchk
      refine ⟨mv.state, mv.write, if mv.left then .left else .right, ?_, ?_⟩
      · simpa [Move.command] using hm q a mv hget
      · cases hleft : mv.left with
        | true =>
          simp only [↓reduceIte, S]
          rw [decide_eq_true_eq]
          intro u hu
          by_contra he_step
          have he_step1 : cert.edge (some (mv.state, R mv.write r')) s u = true := by
            cases h : cert.edge (some (mv.state, R mv.write r')) s u
            · exact absurd h he_step
            · rfl
          have huBi : Bi (some (mv.state, R mv.write r')) = true := by
            simp only [Bi, stepSubset, decide_eq_true_eq]
            exact Or.inr ⟨u, hu, he_step1⟩
          simp only [Move.flip, hleft, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hchk
          have he_q : cert.edge (some (q, r')) a (some (mv.state, R mv.write r')) = true := hchk
          have hf := hS _ huBi; rw [he_q] at hf; exact Bool.noConfusion hf
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, S, L, Equiv.symm_apply_apply]
          rw [decide_eq_true_eq]
          intro u' hu'
          by_contra he_u'
          have he_u'1 : cert.edge (some (mv.state, j)) t u' = true := by
            cases h : cert.edge (some (mv.state, j)) t u'
            · exact absurd h he_u'
            · rfl
          simp only [stepSubset, decide_eq_true_eq] at hu'
          have hex : ∃ z : Node cert, Bi z = true ∧ cert.edge u' mv.write z = true := by
            rcases hu' with rfl | ⟨z, hz, hez⟩
            · exact ⟨none, hBnone, by simp [edge_none]⟩
            · exact ⟨z, by simp only [Bi, stepSubset, decide_eq_true_eq]; exact hz, hez⟩
          obtain ⟨z, hzBi, hez⟩ := hex
          simp only [Move.flip, hleft, Bool.not_false, ↓reduceIte] at hchk
          have h1 := allFin (allFin hchk j) t
          have hbeq : Nat.beq (cert.dfa.next t j).val r'.val = true := by
            simp [r', R]
          simp only [hbeq, ↓reduceIte] at h1
          have h2 := allNodes h1 u'
          have he_u'' : (cert.edgeRow (some (mv.state, j)) t).testBit (nodeId cert u') = true := he_u'1
          simp only [he_u'', ↓reduceIte] at h2
          have h3 := allNodes h2 z
          have hez' : (cert.edgeRow u' mv.write).testBit (nodeId cert z) = true := hez
          simp only [hez', Bool.not_true, Bool.false_or] at h3
          have hf := hS z hzBi; change cert.edge (some (q, R t j)) a z = true at h3; rw [h3] at hf; exact Bool.noConfusion hf

theorem cert_of_checkCertificate {N : Machine4} {tb : Table} {val : ℕ}
    (hm : Matches N tb) (h : checkCertificate tb val = true) : CertProp N := by
  unfold checkCertificate at h
  have ⟨hb, hcm⟩ := Bool.and_eq_true_iff.mp h
  split at hcm
  · exact cert_of_flipped hm hb hcm
  · exact cert_of_unflipped hm hb hcm
end CertSound

def moves16 : List Move :=
  [⟨0, 0, false⟩, ⟨0, 0, true⟩, ⟨0, 1, false⟩, ⟨0, 1, true⟩,
   ⟨1, 0, false⟩, ⟨1, 0, true⟩, ⟨1, 1, false⟩, ⟨1, 1, true⟩,
   ⟨2, 0, false⟩, ⟨2, 0, true⟩, ⟨2, 1, false⟩, ⟨2, 1, true⟩,
   ⟨3, 0, false⟩, ⟨3, 0, true⟩, ⟨3, 1, false⟩, ⟨3, 1, true⟩]

theorem mem_moves16 (m : Move) : m ∈ moves16 := by
  obtain ⟨q, a, d⟩ := m
  fin_cases q <;> fin_cases a <;> cases d <;> simp [moves16]

inductive StepRes where
  | halted11
  | done
  | missing (q : State) (a : Symbol) (rem : ℕ) (cur : Position) (step : ℕ)

def stepLoop (tb : Table) : ℕ → Position → ℕ → StepRes
  | 0, _, _ => .done
  | rem + 1, cur, step =>
    match tb.get cur.state cur.head with
    | none =>
      if Nat.beq cur.state.val 2 && Nat.beq cur.head.val 1 then .halted11
      else .missing cur.state cur.head (rem + 1) cur step
    | some m => stepLoop tb rem (cur.move m) (step + 1)

def checkMoves (f : Move → List ℕ → Option (List ℕ)) : List Move → List ℕ → Option (List ℕ)
  | [], certs => some certs
  | m :: ms, certs =>
    match f m certs with
    | none => none
    | some rest => checkMoves f ms rest

def checkTree : ℕ → Table → ℕ → Position → ℕ → List ℕ → Option (List ℕ)
  | 0, _, _, _, _, _ => none
  | holesLeft + 1, tb, rem, cur, step, certs =>
    match stepLoop tb rem cur step with
    | .halted11 => some certs
    | .done =>
      match certs with
      | [] => none
      | v :: rest => if checkCertificate tb v then some rest else none
    | .missing q a rem' cur' step' =>
      if Nat.beq holesLeft 0 then none
      else checkMoves (fun m rest => checkTree holesLeft (tb.set q a m) rem' cur' step' rest) moves16 certs

theorem checkMoves_each {f : Move → List ℕ → Option (List ℕ)} {ms : List Move}
    {a b : List ℕ} (h : checkMoves f ms a = some b) {m : Move} (hm : m ∈ ms) :
    ∃ x y, f m x = some y := by
  induction ms generalizing a with
  | nil => simp at hm
  | cons head tail ih =>
    unfold checkMoves at h
    cases hh : f head a with
    | none => simp [hh] at h
    | some mid =>
      simp only [hh] at h
      rcases List.mem_cons.mp hm with rfl | ht
      · exact ⟨a, mid, hh⟩
      · exact ih h ht

theorem stepLoop_sound {N : Machine4} {tb : Table} (hm : Matches N tb)
    (h11 : N 2 1 = none)
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    {rem : ℕ} {cur : Position} {step : ℕ}
    (hsum : step + rem = 107)
    (hrun : N.multiStep (Machine.init []) step = some cur.view) :
    match stepLoop tb rem cur step with
    | .halted11 => False
    | .done => True
    | .missing q a rem' cur' step' =>
      tb.get q a = none ∧ cur'.state = q ∧ cur'.head = a ∧ ¬ (q = 2 ∧ a = 1) ∧
      step' + rem' = 107 ∧ N.multiStep (Machine.init []) step' = some cur'.view := by
  induction rem generalizing cur step with
  | zero => simp [stepLoop]
  | succ rem ih =>
    unfold stepLoop
    cases ht : tb.get cur.state cur.head with
    | none =>
      simp only []
      by_cases h0 : (Nat.beq cur.state.val 2 && Nat.beq cur.head.val 1) = true
      · rw [if_pos h0]
        simp only [Bool.and_eq_true] at h0
        have hs : cur.state = 2 := Fin.ext (Nat.beq_eq.mp h0.1)
        have ha : cur.head = 1 := Fin.ext (Nat.beq_eq.mp h0.2)
        have hnone : N.multiStep (Machine.init []) (step + 1) = none := by
          rw [Machine.multiStep_succ, hrun]
          simp [Machine.step, Position.view, hs, ha, h11]
        have hnone107 := Machine.multiStep_eq_none_mono hnone (by omega : step + 1 ≤ 107)
        obtain ⟨r0, T0, hr0⟩ := h107
        rw [hnone107] at hr0
        contradiction
      · rw [if_neg h0]
        have hne : ¬ (cur.state = 2 ∧ cur.head = 1) := by
          rintro ⟨hs, ha⟩
          apply h0
          simp [hs, ha]
        exact ⟨ht, rfl, rfl, hne, hsum, hrun⟩
    | some m =>
      simp only []
      have hnext : N.multiStep (Machine.init []) (step + 1) = some (cur.move m).view := by
        rw [Machine.multiStep_succ, hrun]
        exact step_move hm cur m ht
      exact ih (by omega) hnext

theorem checkTree_sound {holesLeft : ℕ} {tb : Table}
    {rem : ℕ} {cur : Position} {step : ℕ} {a b : List ℕ}
    (hCheck : checkTree holesLeft tb rem cur step a = some b)
    (N : Machine4)
    (h11 : N 2 1 = none)
    (hAlive : ∀ q a, ¬ (q = 2 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    (hm : Matches N tb)
    (hsum : step + rem = 107)
    (hrun : N.multiStep (Machine.init []) step = some cur.view) :
    CertProp N := by
  induction holesLeft generalizing tb rem cur step a b with
  | zero => simp [checkTree] at hCheck
  | succ holesLeft ih =>
    unfold checkTree at hCheck
    have hstep := stepLoop_sound hm h11 h107 hsum hrun
    cases hsl : stepLoop tb rem cur step with
    | halted11 => rw [hsl] at hstep; exact hstep.elim
    | done =>
      simp only [hsl] at hCheck
      cases a with
      | nil => simp at hCheck
      | cons v rest =>
        simp only [] at hCheck
        split at hCheck
        · rename_i hcert
          exact cert_of_checkCertificate hm hcert
        · simp at hCheck
    | missing q a rem' cur' step' =>
      simp only [hsl] at hCheck hstep
      obtain ⟨_, _, _, hne, hsum', hrun'⟩ := hstep
      by_cases hhl : Nat.beq holesLeft 0 = true
      · simp [hhl] at hCheck
      · simp only [hhl, Bool.false_eq_true, ↓reduceIte] at hCheck
        obtain ⟨q', w, d, hNqa⟩ := hAlive q a hne
        let m : Move := ⟨q', w, match d with | .left => true | .right => false⟩
        have hm_cmd : N q a = m.command := by
          cases d <;> simpa [m, Move.command] using hNqa
        obtain ⟨x, y, hxy⟩ := checkMoves_each hCheck (mem_moves16 m)
        exact ih hxy (matches_set hm hm_cmd) hsum' hrun'

def baseTable (b c : Symbol) (q : State) : Table :=
  ⟨some ⟨1, 1, false⟩, none,
   some ⟨2, 0, false⟩, none,
   some ⟨3, b, false⟩, none,
   some ⟨q, c, true⟩, none⟩

theorem branch_one_sound {tb : Table} {q1 : State} {a1 : Symbol} {rem1 : ℕ} {cur1 : Position} {step1 : ℕ}
    (hsl : stepLoop tb 107 startPos 0 = .missing q1 a1 rem1 cur1 step1)
    (hbranches : ∀ m ∈ moves16, ∀ (N : Machine4),
      N 2 1 = none →
      (∀ q a, ¬ (q = 2 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d)) →
      (∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩) →
      Matches N (tb.set q1 a1 m) →
      step1 + rem1 = 107 →
      N.multiStep (Machine.init []) step1 = some cur1.view →
      CertProp N)
    (N : Machine4)
    (h11 : N 2 1 = none)
    (hAlive : ∀ q a, ¬ (q = 2 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    (hm : Matches N tb) : CertProp N := by
  have hstep := stepLoop_sound hm h11 h107 (rem := 107) (cur := startPos) (step := 0) (Nat.zero_add 107) rfl
  rw [hsl] at hstep
  obtain ⟨_, _, _, hne, hsum1, hrun1⟩ := hstep
  obtain ⟨q', w, d, hNqa⟩ := hAlive q1 a1 hne
  let m : Move := ⟨q', w, match d with | .left => true | .right => false⟩
  have hm_cmd : N q1 a1 = m.command := by cases d <;> simpa [m, Move.command] using hNqa
  exact hbranches m (mem_moves16 m) N h11 hAlive h107 (matches_set hm hm_cmd) hsum1 hrun1

set_option maxHeartbeats 0 in
private theorem tv_0_0_0 : checkTree 4 (baseTable 0 0 0) 107 startPos 0 [1464361708604457318159301458966524673248591894946] = some [] := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem tv_0_0_1 : checkTree 4 (baseTable 0 0 1) 107 startPos 0 [1464361710646151519684932239746772317839201163682] = some [] := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem tv_0_0_2 : checkTree 4 (baseTable 0 0 2) 107 startPos 0 [1464361707923892584317424532039775458385055472034] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_0_3 : checkTree 4 (baseTable 0 0 3) 107 startPos 0 [51136422218208, 12845253756014580679348398458832883851408310755, 51136422218208, 275742580527299594880895463177335482441862617321122554647059734070044067339242318715840127894583621, 262242318715360, 275742580527299594880895463177335482832348559166710318341453211920408186959754514295470200903465285, 262242318715360, 21278113695528257338394793257875823010, 150092065606112, 431567310948832, 150092065606112, 133816252495993256010506885074726280924716669265480831716472155720541544709159175653129587246049093, 133816252495993256010506885074726105987013419054763475116310935092214930863914569587559695461957445, 275742580527299594880895463177335483222834503921644955298150000359320325594538626707936254260443461, 145981366161511564214147322386629602738380107292335950125345560811090779677359082611142029006577157, 431567310948832, 431567310948832, 431567310948832, 21278113695528257338394793257875823010, 51135918410208, 7446115018805182963688482605248666733912103959872825238712085276040382724995318727053263307214162951543055000745742703758766544039280757360086799031800667423371935423600191245913407185603017610375161918571401415848425755834863483317302582916468269383680749995561, 51135918410208, 51135918410208, 51135918442976, 51135918705120, 51135918442976, 275742578593706851719644999315771482782076691203762723111295285011169720903507157719124210586515493, 51135918639584, 1979003488832547858846189973905690174002435121913628464699639513488242684290738543184558534492285637002600321282993592790877831918323008289211266349805866849664587574969102630, 51135918639584, 275742578593706851719645025363609634928255361064169776197125212591699411652480059933463543967709221, 51135918410208, 51135918410208, 558349945312, 558350010848, 558350207456, 558350010848, 133816252495993256010506885074726180960314812002924060576668848856042582111383343523374423690413893, 145981366161511564214147322386629602738380107290915370512691637850895075162824637153534851676610053, 558350207456, 558349945312, 558350207456, 558349945312, 267877834424728777550606397787958930280836336678054975308008101361268067839468090805426279168533516836, 398658890834808893782269112532125432001401740271565980644248130658663915183954310339008613717639877156, 121504696142304, 121504696142304, 84121300830688, 84121300830688, 1982530864943102935002657978810122485116557024634262789374329968893270376765777726722565828672877600442984560467882065744018055802867461959071502839564940387104185513138976038, 84121300830688, 1982530864943102921273056111767687262869015400092082699637154935322567471847271841768743269609972686848755512604788303981114124401890915956174927687890026240009471873998910758, 84121301027296, 275742580527299594880895463177336282157077476881932521967051064055888234186571674029143804361800005, 84121301027296, 275742578593706851719645025363609634928255361064169787035287217891812804727551361061237063812446245, 282409062914737679354124477203977430472010270410344048456105595074363198162815930187960294112626397732, 191873507428832, 191873507428832, 150092065606112, 150092065802720, 150092065606112, 2040498456046432659423199645032461623265553282144610840042724213824041670197538033162270855322736152702773124653924737216982120647644341881325941315741193728232447605203793190, 150092065802720, 150092065802720, 150092065802720, 275742580527299594880895463177336282157077476881932543643375397027653927759289835043618369500313925, 398658890834808893782269112532125432001401740268656633640885544779124240749598645248232413665369444900, 265783407324241935627377226042670592627617269860224675659796141461739943396285282273611011396102443556, 332611130001888, 332611130001888, 282033595353568, 282033595156960, 282033595353568, 282033595156960, 2967979913699711984601897959554112466834501648834032276757759329679870576075538855751111620318488017825431255900459046997571671087481410615983031222176144451061498783655261478, 282033595353568, 282033595091424, 282033595353568, 282033595353568, 265783407324241935627377226042670592627617269860224675659796141461739943396285282273611011396102443556, 84121771051488, 47099263715181964460818972740890008150495217123, 84121771051488, 150092468718048, 184115303551770369948286087058711806107543687651, 150092468718048, 184115652000903712395555452783325302867133243875, 282033864051168, 558887340512, 282033864051168, 558887340512] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_0 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨0, 0, false⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [1464361707966427880182233562712715619175492508066] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_1 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨0, 0, true⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [571205086120416, 1464361710646151519684700124882598286899257825698, 571205086120416, 1461507212538480664554998473984245975004184861090, 567906484160992, 1464361707923892584317115045923146091181152164258, 567906484160992, 1464361710646151519684700124882597442474327693730, 1464361710646151519684700124882597723950378146210, 282360429932440921634435530475942801223390978669424096698925869592571783051915352869463821379201678469, 259554108715552098212705735227152803163177572981848817707725189664697058057628128354186541871938693, 265750998701117862827972793394626782248071493387633322046397745286803236009162338692411825011707362437, 282360429932440921634435530475942801223390978669424096698925869592571783051915352869463821379201678469, 519060720658253167091715039972044609174890420036105604973209768913999895918363743381788277199612549, 282360430056190857196755560216750876794260701953300801614131496818717315350194016830086526279843069061, 282360433892438859628676482181801219491222123753478653985505940829228816596832599609390378199726177413, 8304733559402423817928220410557931123334961367843402854527006308275509884076369150104906233437760133, 8304733435652488255608190669749855552465238083966697939321379082129977585797705189482201332796369541, 132875499350558938790059545053661143621290455862257239034328506716870277490563755634584084651636137477, 66437757595275474464755502148063856229062075598410620614139173764095941506628643509090440582955769349, 1464361707923892584317115045923146091181152164258, 265750982861125933825306182454672041096648101615824721530923611762891119907605969546911758792390618629, 41240448207328, 145694019291616, 41240448207328, 145694019291616, 77524365478368, 435965357459936, 77524365478368, 145694019291616, 145694019291616, 295227869104608, 435965357459936, 295227869104608, 21278113695528257338397045066279442850, 265750982861125933825306182414421056402165524669991231012260177378316387634455875080735287219083406853] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_2 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨0, 1, false⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [1464361708008963176047352079576068745752065629090] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_3 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨0, 1, true⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [564607848581600, 564607848581600, 563508303366624, 563508303432160, 36842267544032, 145694019291616, 36842267544032, 558350207456, 966141752000502738405095625038592681067834646187494479423280726477589068885183179702073481012278238334529789319172174971895832183671948863234191362353194883935863474551078, 290829688375776, 966141752000500378625989731872817989540801892326997825695406450743068230876865833860262219840930399978503235838004447467425403078453566542393837098367859852036595243448614, 145694019291616, 1461501637352181031899213089980890836623265126818, 145694019291616, 1461501637352181031899213089980890836623265126818, 290829688375776, 558350207456, 290829688375776, 558350207456, 563508303432160, 290665147528101184000516969446802151854884828795492908063372547094944313597392067655244301303063526245, 290665147651851119562836999187610227425754552079369612978578174321089845895670731615867006203704916837, 519060720658253167091715039972044609174890420036815894747784302408545163889929638566839449517304453, 282360430056190621162485154794023008804179236896446947009024076549877055601835601157377729609695509349, 8304733559402423817928220410557931123334961367844113144301580841770055152047935045289957405755452037, 8304733435652488255608190669749855552465238083967408229095953615624522853769271084667252505114061445, 132875499350558938790059545053661143621290455862255818454715852793910081786049221189126477474306170373, 66437757595275474464755502148063856229062075598409200034526519841135745802114109063632833405625802245, 36842267478496, 145694019291616, 36842267478496, 558350207456, 73126184749536, 290829688375776, 73126184749536, 145694019291616, 1461501637352181031899213089980891962523171969442, 145694019291616, 1461501637352181031899213089980891962523171969442, 290829688375776, 558350207456, 290829688375776, 558350207456, 265750982861125933825306182441255046198487242633878804111756479711739347580991150681200601580166147589, 36842267478496, 145694019291616, 36842267478496, 558350207456, 73126184749536, 290829688375776, 73126184749536, 5575207577746351313641194178230861817731490, 145694019291616, 145694019291616, 290829688375776, 558350207456, 290829688375776, 558350207456, 265750982861125933825306182414421056402165524669989810432647523455356191929941340635277680041753439749] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_4 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨1, 0, false⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [1464361708094033767777589113302774998905211870626] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_5 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨1, 0, true⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [1464361707923892584317115046144510397778272213410] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_6 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨1, 1, false⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [1464361708264174951238063180756187505211504351650] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_7 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨1, 1, true⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_8 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨2, 0, false⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [1464361708604457318159011315663012517824089315746] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_9 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨2, 0, true⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_10 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨2, 1, false⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [1464361709285022052000907585476662543049259252130] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_11 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨2, 1, true⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_12 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨3, 0, false⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [1464361710646151519684700125103962593499599100322] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_13 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨3, 0, true⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [8563508295867722842887770861594288508722239906, 259554108715552098212705728623475626724630521594603134533357242422868125915871867969826322575801477, 14272520844763045307182576395367144687418759586, 544817109043680, 544817109043680, 558349945312, 558350010848, 558350207456, 558350010848, 129777054357776070718133912919321818013608100917438497787858729316873097850528080041619073181599557, 129777054357776070718133912919321818013608100917438497787858729316873248260238370656545951515121477, 558350207456, 558349945312, 558350207456, 558349945312, 25690546282836057156720322554205310394492279202, 519060720658253167091715036827436429918439096505822265461197216345135704539925336824765031565503109, 48526596478417347013899544689296735109278357922, 94198698911274128253946798179068731329845680546, 185542899693599287682663686719434430188989995426, 8304733559402423817928220410557931123334961368206360961785574567001546463502684904544808777231116933, 368231298535990671172512384545565727006598912418, 544817109043680, 544817109043680, 558349945312, 558350010848, 558350207456, 558350010848, 33218888202632957985837412340677266336007317904004480388640112641589742341322082582928544778721920837, 33218888202632957985837412340677266336007317904004480388640112641589742491731792873543471657055442757, 558350207456, 558349945312, 558350207456, 558349945312, 298526504421856, 298526504421856, 282033326655968, 282033326721504, 290829688375776, 282033326721504, 290829688375776, 282033326655968, 290829688375776, 290829688375776, 3131996327880721391324013972329910978241128977832337962879771763414006837141610202428841973514113623796529680978490693167788219893122632636329398941861950100256928026681956646, 3187458479675900545055087932273128398242023104905971538811442536687278444163738842634926376355433538335402216177898492685333228645888416061972980342263266990018340567504149286, 558349945312, 558350010848, 558350207456, 558350010848, 66437757595275474464755502171543597300843578817174394835766664997736606942435614136656491954614847301, 66437757595275474464755502171543597300843578817174394835766664997736607092845324427271418832948369221, 558350207456, 558349945312, 558350207456, 558349945312] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_14 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨3, 1, false⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [573404176484832, 745730427562278567334884584652327908919488780567120412968440111809792171287347223296525385966700291563807519338472764154643566031477698183890717672540297990376603463944079331488395188914954136019299858814383559141154901318888481631402979363721536618756114534760, 989321841767319309241179085646333553917097411865766997157737729643302130324841614375473057655171778299070674054138568448791817699017769938498532132075288890278658506547078950, 7682389909087520205720087319860022064149966362099033801161057317160735648524834041372969469868650401000268772572235049035242783730090084415736793981053083148686298204798125699883500130885141979859568345649586419406008220215166273573759998405746299521300244722760, 132891705642603364504485238947015663828611762578175920572905284488246049633361855429395696446189695748, 58895940867956603604473144646427608824441873817003190844864725056639821022469272929402612668263586698103485109240941644255093906810636783521374773752469059579699957561953376631899103084463026745535366708258629378289519265524749798517876682507484718451014119722760, 33222929381011843263846615318212923150434499755858898590611871145008783065910293376324828203186746116, 409553609850050591608673572654349265370060729903786765368061691608742422381521335735441918654832094526010328828989736132761265492613872622982964185394215906998922949054035363258182442247436296351624009534207644331905756096280259061359155526556809094229525170797856909267401788456350206301452091754244726324354447279408589899936977723572604301880436620968145280887352390624554, 30916359152751189213588569716695480338831287587924043222915466751479580407552280436591103440964716258774935453871100948706333249041801285517375424745499030967393445422638886, 480481306154841411279335509504659558991302972035764887225569256679644531321060337662791643172977476792503675382467218841788637748683297475022797157693807665137316180254405856035492991600712643742158227906054773257174111120635282206652796646290190075854604548119722760, 840883020203473374071086892551471702706300091373262276212983699647066562307533676870720545154832233949881301411553328912192849804835344739436180008376603091516710998439478657225788370522134427583898499545170651348528492840387491032932494844945883910239992895420060594973747487412028684131649289535045171845580821743339094846873124370591894632689973252662061773877320944660285599118503918041871055247662020385938272668105362396094833953243711740140934631421547871532693370850872443204712020206940332771194536780092008016682306301547774516681793781615333674169111532591977185986275239912150863095054706338598387914205025260386934599039054101667380055950148014793777878978195158197512988372921606906920017229937483957096105608721836762917718464409257896872724212313197304291951965980254814641333211614228416076622571469990349653136216846645140336327352659572729789180470305624301440687821592944566272934038511548027448647456421788569769898675120852604469309495634921122493335700884499767457089001640428159830079998702003891, 1978643211784836382327486685358632508407055730645547344284018034853780840402079106044370268020564735662577470807161774573979568742394804549351056885608329872426441835071285030, 33222925916013647518885782575586807166082247807311160964854308812933878714107702478889090985227809540, 49945803616938061550529964108510766346487592166224981986030973983753770277352468346263216178283005604773820719478039062852565649010737277229598224684708178675104633038881872113756669106307083739684842012422910348370801035415956920184260542655848798347822563558378738127950194156434386780164837643570242062331207839589889476426738144977332242302745785236527421139386782924434030153963249046783413703989321374888295730132024380873146783574348716997021612413354164777789135435133369737443799329039737661011720454966049496086248244569760615570066520203803450738844433117932529558014755615176291397928074583406902874220384861049109003714698667955875761854830728700843069973781654810766003639498176697803599004934326027870333061495711874848635787129953954245076503276250888922895995604308704209717762662479213237300502436121700813963230776718558116978305757118918035182663535866037803828353012190332796894801645857290134472304553909096238081820258713546772088310693252790050319783838264587587975140523914380739328865485459680989460720176517354444816842019473816499940486663548563981607916812965255744323081296995497140677428439763235071876876684916336950698437608338569185314997479427702210943592708377852444922368537666931220287187220, 30030067315683108100875319791999476991338992933897809214604811662413119015545642512452961048364030062599549250697791832320019996797675177462387626324799895551981702958234900094336436243714305882171885819682014639589455673620752617433721147278314131632963584581738761, 573404176484832, 45638595414496, 353914939711471685002269406028903635540386, 45638595414496, 290829688375776, 81922479163872, 290829688375776, 81922479163872, 5580652095617086483799703376180863363504546, 290829688375776, 290829688375776, 290829688375776, 9354711665120, 572304664889824, 45638595414496, 45638595414496, 290829688375776, 81922479163872, 290829688375776, 81922479163872, 1461501642796698902634383248490091038424624585122, 290829688375776, 290829688375776, 290829688375776, 9354711665120, 572304664889824, 259554109198478233466675932087320615678683863904435429668183584350376361836457885333564431238281348, 2092399581890031321501161991899214891463247035319791758654726651720350933834441235101106715026354948, 483457197960390425940787168533020162085456573041731669343945604829956852281164406730617604, 33222925916013647518885782575586807166082247807311160964854308812933873900996829737332686230371529476, 132891703662604380755222862754956322400032335095051944613838314817733043354952799395335825248866628356, 45638595381728, 435965223242208, 45638595381728, 290829688375776, 81922479098336, 290829688375776, 81922479098336, 154490246531552, 1462931678082554678843334226424325740506102421922, 154490246531552, 1461501642796698902634383248490092164324531427746, 290829688375776, 290829688375776, 290829688375776, 9354711665120, 81100758978735554310785261679920616656833819512854807343365998317436465290946939567522168589349636, 617493546453218838304402869913101684275672920991142447735831702675185035833890246917063973628702687190474948924436361030648357543071907150363377574698426233039474881503781399567245269068360651570078108999118963631512762016642178623694550146118307514226329860119722760, 275742580527771666122904025377917166043790665740115384573777717531106746990872937113243259806249732, 290829688375776, 290829688375776, 4152865739932232452232386892318811504796911165409254694589269348105601470541197332130086336314569476, 16610449198791500677743858849612659212161260399919212964004268232963536748890441934683518839799980804, 30916301109114743023011203375420866404060139620424026224663806017130983584009166951143448393896011127854433430094553801169238010519444020670720346146568256905282053812876583, 290829688375776, 290829688375776, 290829688375776, 9354711665120, 45638595381728, 435965223242208, 45638595381728, 290829688375776, 81922479098336, 290829688375776, 81922479098336, 5580652095617086483799703378432663177189794, 154490246531552, 154490246531552, 290829688375776, 290829688375776, 290829688375776, 9354711665120, 45638595152352, 45638595152352, 290829688375776, 81922479163872, 290829688375776, 81922479163872, 30916301109114743023011203375420866404060139620424026224821414041916561500858283111544022856704885872947232399242155528205513909279870679513784468345334335790966998630757671, 290829688375776, 290829688375776, 290829688375776, 9354711402976] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_15 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨3, 1, true⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [36842267249120, 8574659008749355075406673590659040913791146402, 36842267249120, 35742722034144, 37941812464096, 6433789511384616779508052901454798451475765666, 37941812464096, 8563508636150089763835905657734614538293107106, 8563507955585355921939635917875787731538303394, 8563509316714823605732175397597944944675289506, 8574658370719917098628920640365238488931522978, 45638628936160, 5709012570173436159823062798380813879222491554, 45638628936160, 35742722034144, 36842267249120, 14294823971938144376961056433741387510628506018, 36842267249120, 35742722034144, 37941812464096, 11440325864267289247259404050426177686231603618, 37941812464096, 14272521185045412228130711191507470716989626786, 14272521865610146070026980931370801123371809186, 45638628936160, 14361723825557167799748719231559887124958304674, 45638628936160, 35742722034144, 36842267249120, 36842267249120, 558349945312, 558350010848, 558350207456, 558350010848, 129777054357776070718133912919321818013608101281106862370019878524050299292266414787819299839854405, 129777054357776070718133912919321818013608101281106862370019878524050449701976705402746178173376325, 558350207456, 558349945312, 558350207456, 558349945312, 72026639337952, 72026639337952, 70927094122976, 70927094188512, 73126117640672, 70927094188512, 265880740115493724881977154507710319307854123671019046007629065412487154491952639102120772797690990085, 291054431167331362635007489766708772857947820151773566364016710294677108274209157025942993979747313701, 73126117640672, 265880740115493724881977154507710319307854123671019046007629065412487158703938811211599161718775967237, 73126117640672, 70927094122976, 519060720658253167091715037456358065769729361648138919397474527811293060142614503770350416109251205, 48526595797852613172003274654285780999593810338, 8304733559402423817928220410557931123334961368570029326367735716208723664944423239291009003889371781, 368231301258249606540097463800165827907278625186, 494660803414096102862435905283959249239464672990970946399407671269808898886434704793682695368634451418862615543473843335660694288511193082532865303142823202475517139106882343, 494660803414096102862435905283959249239464672990970946399407671269808898886434704793682695368634451418862615543473843335660133071882468883580366722925396666495301848118551335, 558349945312, 558350010848, 558350207456, 558350010848, 33218888202632957985837412380928251030489894850201772451222409953900070719845055449725561256920647493, 33218888202632957985837412380928251030489894850201772451222409953900070870254765740340488135254169413, 558350207456, 558349945312, 558350207456, 558349945312, 291929233328608, 291929233328608, 290829688375776, 290829688179168, 290829688375776, 290829688179168, 290829688375776, 290829688375776, 290829688375776, 290829688375776, 36842267249120, 36842267249120, 558349945312, 558350010848, 558350207456, 558350010848, 66437757595275474464755502171543597300843578817538063200348826146943784143877352471402692181273102149, 66437757595275474464755502171543597300843578817538063200348826146943784294287062762017619059606624069, 558350207456, 558349945312, 558350207456, 558349945312] = some [] := by
  decide +kernel

private theorem solve_0_1_0 (N : Machine4) (h11 : N 2 1 = none)
    (hAlive : ∀ q a, ¬ (q = 2 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    (hm : Matches N (baseTable 0 1 0)) : CertProp N := by
  refine branch_one_sound (tb := baseTable 0 1 0) (q1 := 1) (a1 := 1) (rem1 := 102) (cur1 := ⟨1, [1, 0, 1], 1, []⟩) (step1 := 5) rfl ?_ N h11 hAlive h107 hm
  intro m hmem N h11 hAlive h107 hm' hsum1 hrun1
  simp only [moves16, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkTree_sound tv_0_1_0_0 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_0_1 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_0_2 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_0_3 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_0_4 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_0_5 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_0_6 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_0_7 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_0_8 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_0_9 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_0_10 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_0_11 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_0_12 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_0_13 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_0_14 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_0_15 N h11 hAlive h107 hm' hsum1 hrun1

set_option maxHeartbeats 0 in
private theorem tv_0_1_1 : checkTree 4 (baseTable 0 1 1) 107 startPos 0 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_2 : checkTree 4 (baseTable 0 1 2) 107 startPos 0 [8563507998120651787366428860618958746413980066, 1464356481867301412544502661532554521288863930786, 14272520589551270116778542327313640854081526690, 1464356154558199730466509840439122332718281546146, 8563660742368103423319401272822311198915582370, 1829732938589152524743782295114492920245458590114, 14272651513191942947552545150620309336699722146, 2854495406690033457644829277293783530641316258, 94198696869579926728257987557522601689129965986, 2854495406690033457644829277294909434843126178, 94198696869579926728257987557522672058142579106, 1464357529256426795192861086935421320906545322402, 1464357529256426795192861086935421602382595774882, 2854495406690033457644829277294909434843126178, 1464356176378806509271690018958450334928020200354, 8563507998120651787058151600632807583325903266, 14272520589551270116471473997758807930848697250, 2854495406690033457644829203506807235803109794, 2854495406690033457644829203506877604815722914, 2854495406690033457644829203506807240098077090, 2854495406690033457644829203506947973828336034, 2854495406690033457644829203507933140004919714, 2854495406690033457644829203509059044206729634, 1464356220020020066882050375997106339347497508258, 1464356132737592951661329662214942235687895718306, 1464356307302447182102771090074418348186452122018, 1464356481867301412544212518229042365864361351586, 1464356830997009873427095374538290401220179818914, 1464357529256426795192861087156786471931816728994, 8565406390910407837733683962760620548000078242, 14274397161734247361966827840558618685784218018, 2854495406690033457644830384098427953214413218, 130774973853020778695088269180837537095380934324019416781048743260544315259086230966655818293811013, 130774973853020778695088269180837537095380934324019416781048743260534707838551732577246819083629381, 2854495406690033457644830384098568691239639458, 130774973853020778695088269180837537095380934324019416781048743260534839447060003582183876511844165, 130774973853020778695088269180837537095380934324019416781048743260534989856770294197110754845366085, 2854495406690033457644830384099553857416223138, 130774973853020778695088269180837537095380934324019416781048743260535892315126171621680335938557765, 2854495406690033457644830384100679761618033058, 130774973853020778695088269180837537095380934324019416781048743260537095592808496541095362606733125, 8563507998120651787058152781224428300737206690, 14272520589551270116471475178350428648260000674, 2854495406690033457644830384098427953214413218, 130774973853020778695088269180837537095380934687687781363209892467721516700824565712856044952065861, 130774973853020778695088269180837537095380934687687781363209892467711909280290067323447045741884229, 2854495406690033457644830384098568691239639458, 130774973853020778695088269180837537095380934687687781363209892467712040888798338328384103170099013, 130774973853020778695088269180837537095380934687687781363209892467712191298508628943310981503620933, 2854495406690033457644830384099553857416223138, 130774973853020778695088269180837537095380934687687781363209892467713093756864506367880562596812613, 2854495406690033457644830384100679761618033058, 130774973853020778695088269180837537095380934687687781363209892467714297034546831287295589264987973, 25690545772412506775602769260703005069416619426, 1464357529256426795193093201799596196271418792354, 48526596138134980093251223127481733500086802850, 94198696869579926728548130861039190361427171746, 1464356132737592951661639148110207296294678976930, 185542898332469819999141946328154104084107917730, 1464356132737592951661639148110207296294678976930, 368231301258249606540329577262383931529469385122] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_0 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨0, 0, false⟩) 101 ⟨3, [], 1, [1, 1, 1]⟩ 6 [36842770565600, 36842770565600, 36842267249120, 5709012570173436159823062872167649436572342690, 36842267249120, 35742722034144, 37941812464096, 5709012570173436159823063093528578321086962082, 37941812464096, 45638595414496, 5798215891249925573337340615189908085787351458, 45638595414496, 35742722034144, 39041290537440, 39041290537440, 37941745355232, 37941812464096, 5753616995505912099312812002904095025360035234, 37941812464096, 5753614060570497406415619244747385302483491234, 5753614273246976732002158913968200965766012322, 47837618440672, 324395113019149124931980603344917397479069259184070931726815480083069246017018993450512616250154276, 47837618440672, 37941812464096, 6422639181320647333286707613441575483100649890, 39041290537440, 39041290537440, 37941745355232, 37941812464096, 5798215550967558652389205966619312505136109986, 37941812464096, 47837618440672, 5798215891249925573337340652083325727023323426, 47837618440672, 37941812464096, 5709012570173436160132548988798142527497591202, 5720162985307997336820624780856292637288716706, 45638863817184, 5709012570173436160132548988793779665358576034, 45638863817184, 35743258905056] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_1 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨0, 0, true⟩) 101 ⟨3, [], 1, [1, 1, 1]⟩ 6 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_2 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨0, 1, false⟩) 101 ⟨3, [], 1, [1, 1, 1]⟩ 6 [36842770565600, 67931323650302547558180874794184867073854332236446615533873089039476573943511814144042369884686146966840696755143067115012594461496201286412855165061684377782901946333990, 36842770565600, 36842267249120, 11418025119068758624117868405940505615268862370, 36842267249120, 35742722034144, 37941812464096, 11418025119068758624117868627301434499783481762, 37941812464096, 45638595414496, 11507228440145248037632146148962764264483871138, 45638595414496, 35742722034144, 39041290537440, 39041290537440, 37941745355232, 37941812464096, 11462629586936530428726134395418391762202288034, 37941812464096, 11462626609465819870710424778520241481180010914, 11462626864677595061414272385274569091860946850, 47837618440672, 47837618440672, 37941812464096, 47837383821792, 43313243129278805833213056582541302694709159502816574185556723557995823037907084202009991052288357549245220581143332302867233000483180501983863762884661783888371647326833245598132352196912011670784662784418536672864214711916630486676647041315362965935126640719206023353434382844781164778149521390899440667482158046251865972761531744013814598730063339688142603483445268071125008035629111105412545275991207846599756664999699971025112229415878032347667377818741191093648942812644833226645305244151353485488969907838280146073159827283167185753214896631775118671920153807063342775338437563154193797092591213911911701901123830434060017956546139523278821333550, 47837383821792, 47837383821792, 11418025119068758624117868627301434504078449058, 45638461164000, 310495522189437959677510375218388202358151378877762412873953662986978355638195038839924231122614724, 45638461164000, 45638595414496, 310495522189437959677510375218388202358151378877762369859997564746130807454832438077356453868763588, 45638595414496, 11418025119068758624117868332153529324725623202, 39041290537440, 39041290537440, 37941745355232, 37941812464096, 11507228099862881116684011500392168683832629666, 37941812464096, 47837618440672, 11507228440145248037632146148962764264483871138, 47837618440672, 37941812464096, 11418025119068758624120286193016130632814713250, 11462626779607003330875007222111402735659146658, 265698103389791625225870281609189589914020032401647841628444638945445491368964322726252720683302105800411732046688900338271696104598553910690944848878699470430016955737126, 11507228440145248037632146112069276133707766178, 291962731839624912023526957820894752599158001887583096102370073372024104409990087118831149166000580, 291962731839624912023526957820894752599158001890424255285341348960444101880781319742269934029666756, 11440325949337880977571391463873106187964668834, 310495522189437959677510375218388202358151378877762369859997564746130807454832438079226723147610564, 11440325949337880977648763011476347634498689954, 11418025119068758624117868332153529337610525090, 45638863817184, 30427572051881118984877301553640215190310312723837630573484920668679161892359904708215013857483496524608136222058694552691857633614954863763250687389695195107157374147366, 11507228525215839767859508395325124090467998626, 259775868603384269894548517660096560516211715971610772599190489686886316904340509957784563230339844, 11507228270004064577158078658656769811309157794, 11507228099862881116684011500392168684369500578, 11507228440145248037632146112069276117601638818, 11507231247474775135442169789062623700372708258, 11507228440145248037632146148962764265020742050, 11507233969733710503027249043662724596623268770, 11507228440145248037632146112069276117601638818, 45638863817184, 35743258905056] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_3 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨0, 1, true⟩) 101 ⟨3, [], 1, [1, 1, 1]⟩ 6 [36842267249120, 36842267249120, 36842267249120, 39041290537440, 47837383821792, 39041290537440, 1978899841229738196408284547615808827596895558787306854971418420308326844389194696181035683496727590617163488568780439483935700583318735190343443021157986171530522088524713766, 275742578472857306172466167291968257224331539308368652315585361866231234170851901891033176976422949, 45638360500704, 21799349596635591127851014133843854645538, 45638360500704, 35742755588576, 5809518752884867330457047999072064481898027426, 1345017779827760870373734425107306055177160454929620096410844802914797661596310111301879416791377286791098773902269128614839860425844829062163730211333550843634515511666280528018861226981383504778090581087602362725919586197022119474844293560378087261073949452299804232237977643934535361704008671165352034534069607374179135233067361623609786276942315151204371912714341119309239515940996885112185475906709544827494558779652242803460671342896808044989469483818515513958784467502032976797656843820989391912782428433529225206956402717361116983258671722807610948660445216861481119601493976783700334280746430554802102220066663367966185054995702704384075045423, 11529659938843268031378267668928212729406184354, 21278113695528257338394793257875823010, 21278113695528257338395919162077632930, 137871290263649813197874829377640487420955952886363971028158133040541688330184024964958918259369797, 137871290263649813197874829377640112554448988149112492599241231694127515804813556840791827442925381, 137871292318092102806703427996034758709357826268157645657343319152000018050649722111767963230996517, 21278113695528257338395919162077632930, 21278113695528257338394793257875823010, 21278113695528257338397045066279442850, 21278113695528257338394793257875823010, 36842267249120, 806059060264094537987546426806993618974215428944274236468277715964345552316046005107948145007433224074815898571026038363438967732037303757330061917820241195599157548276705119814888754912904834239284897740947786995744752410271203830385790317401431826950529284122990760, 36842267249120, 36842267249120, 39041290537440, 47837383821792, 39041290537440, 265783407328109121178528475517294553258909915220403920353668311973279156377724084821328150591263394660, 45638360500704, 249081520052720181906560410571328914015907521127779343639589134635965686759878941138523276098152047972444504563456000904661532883058638579616604873411722620094832939297959, 45638360500704, 35742755588576, 36842267249120, 36842267249120, 558349945312, 558350010848, 558350207456, 558350010848, 137871290263649813197874829377640187527750381097273078059599145457955167052282330776606555671381829, 275742580527299595781294594686447117235824022541496749000582688103159471588083700354597975101477445, 558350207456, 558349945312, 558350207456, 558349945312, 267859840193964464254131564352664027350999370047361459307387735739067009657478003316621504856334193188, 137871290263649813197874829377640090687236081877744851890776808687185710933523429371650448972503621, 109410068236768, 109410068236768, 73126184552928, 73126184552928, 73126184552928, 249081520045470955577884447220357138810008935963217523682090947992025736715941021520191222039200515900731919719915329190198449056467587198412763958648112776530466308052775, 73126184749536, 73126184749536, 73126184552928, 327113571863008, 148597187228453110840543420906485870770560803016740496283365938082967966214409212406294207499146352606521138021179010234934274849042237239357410069561690018026562272981291675574377034039554592849243088520252135368002496994323034672121349653592542791508821495092073164392119072758405836060319540007492663374865440492554807416093315938398587412409792468210157683142212180358587648259753190152313100092044800318549043011888717381452512277612674992795263848087389380149030790894333198410539967994007701684813, 327113571863008, 290829688375776, 290829688179168, 290829688375776, 290829688179168, 7446115018805182963688482271374126582454607223642578140750118501038549865137972246480558646889305187063699433720840308781792072005929295892724975540039377472873155134628546416288143111274219766630290606763699890930349315013065952417906912838438055051265119730761, 290829688375776, 290829688375776, 290829688375776, 290829688375776, 137871292318092102806703421392357432324208727234255892876498805044871605752881491887487826579728421, 327113571863008, 327113571863008, 290829688375776, 290829688179168, 290829688375776, 290829688179168, 290829688375776, 290829688375776, 290829688375776, 290829688375776, 275742580527299595781294588082769840832875852865144708743252433290097995806034301227746738907951685] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_4 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨1, 0, false⟩) 101 ⟨3, [], 1, [1, 1, 1]⟩ 6 [72026639337952, 72026639337952, 72026639337952, 74225662626272, 83021755910624, 74225662626272, 22847200589458668864279456189271370105806150050, 22847200802135148189865995853880499750929718690, 83021755845088, 2141052100604206333036000847905118624069722428278629674894131009580806713351119693802727060693242404, 83021755845088, 72026639337952, 72026639337952, 519060697455140250071177498384981466543917109402379355659016959400892970505054058259974708414607044, 72026639337952, 72026639337952, 74225662626272, 83021755910624, 74225662626272, 22858351047128525906084839918858528443042127650, 83021755845088, 83021755845088, 72026639337952, 72026639337952, 72026639337952, 70927094122976, 70927094188512, 3221099573546889726586334055259519189796480694149505382502276514916346582969801210902708481661594578770022434840158569546052863003376503228535087544385789841768442006944609063, 70927094188512, 8320943811203093963952123904625356445496435883242911841784304235004891639135329252328114895334828229, 489994558419394229894408192707556508310618565079585460006580450099149686989401290092037409562774006629, 73126184749536, 66453967847076131702655242845392415792611705150838508035102379216513151889924976244681608193341438149, 73126184749536, 70927094122976, 73126185011680, 23549676955612502321315111887108190062880251298, 73126185011680, 22836050216859403553016964409525090363355716002, 22880651877397648259769267596204434875961335202, 81922479360480, 22836050216859403552726822212817579361426233762, 81922479360480, 70927094647264] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_5 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨1, 0, true⟩) 101 ⟨3, [], 1, [1, 1, 1]⟩ 6 [398675109006424366594140062068643631235359227541975554177834674265490359425994121906920023705671596484] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_6 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨1, 1, false⟩) 101 ⟨3, [], 1, [1, 1, 1]⟩ 6 [72026639337952, 72026639337952, 72026639337952, 74225662626272, 83021755910624, 74225662626272, 45683250785039958721458678324362794820592228770, 45683251167857621507514449720659228181868337570, 83021755845088, 1038216427126421397961485240456067621322793216267842185756266372300963760557095651463392872011295812, 83021755845088, 72026639337952, 45761303733517182823400979351599778190890916258, 973682305660194520363263758815424648502453332964865601634449602116913810045036217512400919022103561022297198191982449324011650611957743470070383256559771951636970126064422, 45761303733517182823400979351599795783144069538, 45672100412440693409886701608577642687447980450, 45672100412440693409886701608578768591649790370, 46385727321334975638939387016129474884784904610, 2127120843326966636773809238949057441772450262823631707353091492400158985887104497263586681995819460, 46385727321334975638939387016129756360835357090, 45672100412440693409886701608578768591649790370, 2131809480885551818060628975316286553848229783839950577237184434730096129787432241712354089297672644, 45672100412440693409886701608579894495851600290, 45672100412440693409886701608577642687447980450, 72026639337952, 2076211109836584743639489535037054939332039759644213895609959695587119416640275851573202690603643652, 72026639337952, 72026639337952, 74225662626272, 83021755910624, 74225662626272, 45694401157639224033030655113925916066499811746, 83021755845088, 83021755845088, 72026639337952, 72026639337952, 72026639337952, 70927094122976, 70927094188512, 2108873172830577448659729529699280828317263147521515038218628592394315857553193527955625308282321348, 70927094188512, 2108619732960657543047439468418910134662617558272751842405049666850141553222870774400452466563250628, 2108619732960657543047439468418910134662617558272751842405049666850141628427728160987312516101470660, 73126184749536, 2108619732960657543047439468418910134662617558272751842405049666850142154861588666492753857774778820, 73126184749536, 70927094122976, 73126185011680, 45672100412440693409886701829943075188769839522, 73126185011680, 81922479360480, 81922479360480, 70927094647264] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_7 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨1, 1, true⟩) 101 ⟨3, [], 1, [1, 1, 1]⟩ 6 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_8 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨2, 0, false⟩) 101 ⟨3, [], 1, [1, 1, 1]⟩ 6 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_9 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨2, 0, true⟩) 101 ⟨3, [], 1, [1, 1, 1]⟩ 6 [184115306274018920761690655252432781739705803235] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_10 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨2, 1, false⟩) 101 ⟨3, [], 1, [1, 1, 1]⟩ 6 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_11 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨2, 1, true⟩) 101 ⟨3, [], 1, [1, 1, 1]⟩ 6 [184115654723162647802677241748030791870354334179] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_12 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨3, 0, false⟩) 101 ⟨3, [], 1, [1, 1, 1]⟩ 6 [290829957073376] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_13 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨3, 0, true⟩) 101 ⟨3, [], 1, [1, 1, 1]⟩ 6 [558887340512] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_14 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨3, 1, false⟩) 101 ⟨3, [], 1, [1, 1, 1]⟩ 6 [290829957073376] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_15 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨3, 1, true⟩) 101 ⟨3, [], 1, [1, 1, 1]⟩ 6 [558887340512] = some [] := by
  decide +kernel

private theorem solve_0_1_3 (N : Machine4) (h11 : N 2 1 = none)
    (hAlive : ∀ q a, ¬ (q = 2 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    (hm : Matches N (baseTable 0 1 3)) : CertProp N := by
  refine branch_one_sound (tb := baseTable 0 1 3) (q1 := 3) (a1 := 1) (rem1 := 101) (cur1 := ⟨3, [], 1, [1, 1, 1]⟩) (step1 := 6) rfl ?_ N h11 hAlive h107 hm
  intro m hmem N h11 hAlive h107 hm' hsum1 hrun1
  simp only [moves16, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkTree_sound tv_0_1_3_0 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_3_1 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_3_2 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_3_3 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_3_4 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_3_5 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_3_6 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_3_7 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_3_8 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_3_9 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_3_10 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_3_11 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_3_12 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_3_13 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_3_14 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_3_15 N h11 hAlive h107 hm' hsum1 hrun1

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0 : checkTree 4 (baseTable 1 0 0) 107 startPos 0 [570105910036960, 576702980164064, 570105910036960, 570105406720480, 1461507213219055783030206551823384419657151715746, 570105406720480, 567906349877728, 567906417052128, 1461507213219055783030206552339893253721019160994, 567906417052128, 265783407324362844182504955463973551434381688491544814997751632860369841583427312195766348172532855556, 265783407324249547732710350944557528415975740869227639664132590932559437171359956633921912990532317956, 5887419212336799620173098380553172816877361570, 349150986574618160595039293693518213585186, 11596431761232122084467903914326028995573881250, 2788294992663904911958003569091898390911266, 551485160692050606355482536602768143064914060480436050409687643195329444600983170787439833478542084, 2788294992663904911958003569091898390911266, 2108619733081507089607567533201339962700420139732636039081643377482706254887557799799095861983785732, 4192909238590278930803703089193743094009502637067176732364638685382728457057900511984441402750874372, 33251311180870641595195828513949851014597119127323989619260064549103278079759053748014915358933857028, 2788294992663904911958003569091898390911266, 730753606960454507600471444016967662847864641954, 42340060531168, 349150996959211877664694550754648310978978, 42340060531168, 286431641864672, 75325409397216, 2788295003048498783770163736825562850695586, 75325409397216, 5575888152864826676462128520906608038943138, 286431641864672, 2788295003048498783770163736825562850695586, 286431641864672, 5709013250748554635031141818110738512112294306, 11418025799643877099325947351883594690808813986, 701853232170736336284337882333415774626, 45672101093015811885094780554520731762987932066, 365555209792742114870813547444438326833423882658, 2788295003048498629028249121963378604022178, 730753606960454507600626187112176397549336304034, 567906886814176, 1461529513326246942861795011930017324569364267491, 567906886814176, 576702979901920, 576702979901920, 97320910292831125892809652641678933856277322537676324756433325765394527062773237600739650366026500, 291962731843401460462563685873434128284148042821457742787986472165973390010861281192417682105237252, 551485160578754156560878017186745124658966440708939382666475710524752987537878418291227740181050116, 1070530018041920916118661893317129147798574916344642674052477047990106436134283511360865248620000004, 2076211109836584628390139524389215144521107559237083222037439465137738071320816148121158533826702469, 2108619732968225161452646160116540921854204724696694904066423557494480359615297954977816615862874884, 2076211109836584628390139520930146147729497815775263060791932600394804390357375010658480077562420741, 4184799162934130101915219213131387488371411964034763951335183430895586253032751462317121410632463108, 32440303108063574131703991889982505849215266484985345860949904646218675464012600369814858128110340, 4184799162934130101915219213131387488371411964051810906687030509572255048767072592140684058593276676, 66470182058391535275506697067052336045409523000925410971543675271878598108459749014892000324488475396, 4184799162934130101915219213131387488371411964392750013723972136098212701659945965394182553829847812, 519052800662613212878458461982033248345087540028820952436111864000689120009820166537153867538042245, 2108619732968210639812963013785316944294472519961139371338431444812129797824453047302896292810928900, 32440303108107830557405009280379389840780089775787582998078861415157583322453713524228692887417604, 1038121394910280498307263850530188532225929374152659647976474273007705390608388883697641888989289989, 551485160578813049877370777307820144762324835464745969730085124225382937098452870455679855307731716, 32440303108107830557405009280379389840780089775077293191752061199687193315471964783062189284209412, 2108619732968269417878347177506937805845769548006674965974380639906737218854110453862751557640205060, 32440303108107830557405009280379389840780091229750816549369333941290104066022671185369599232389892, 4184799162934116271782187645196888462124047959660274946058927254727264091180303602563033114469413636, 33251311180757345145401223994533827996191171507552492951516852616432701622695948995518966272253702916, 33218880282637318031624155752624508800775898900211629981771547921575924059754008863883462019237288581, 567906887010784, 1461529513326266414012152723434563327710879302115, 567906887010784] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_0 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨0, 0, false⟩) 103 ⟨1, [0, 1], 1, []⟩ 4 [574503453723104] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_1 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨0, 0, true⟩) 103 ⟨1, [0, 1], 1, []⟩ 4 [1461596415689447448768746589210334639930076037603] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_2 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨0, 1, false⟩) 103 ⟨1, [0, 1], 1, []⟩ 4 [574503453723104] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_3 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨0, 1, true⟩) 103 ⟨1, [0, 1], 1, []⟩ 4 [574503453231584, 299853155871476305699119264854691309361606720311703030242280424837609024585662841690778918947335172976199638875495007313158689850578402397814647635246912393869079850137041641093940511461552126177386353621840646586032393251905970258536385895402020047162574268194775330063707811480031037421183447193533598068094528534513567600499707557903195702261553342497924892119349313322, 64943970054067600678300434409136454724796539274291310610535599684592247900543273202026083003411077, 392140253651666441831137460351143539799540104723828236371610104288335663392383950746391861143167723743012707597243027487527724493857253095734238488422264622944121446509499669580110797584932366000547722354077120640777975129061767230153132900960850130106220119710322457394562655018242028915650529847196406184162678795003496258997937459508319587703439350666625735667971976250674484392841180394342171128435262604087534264467119411951469216731931582666924044056795924004750182579009504740320666917420954392420326481483932540458765997153422986866536538113594296696804254081715504287517607464052800241225591787341342589950814766224485078727775602112706066395163116791614481320027755625596359587978532228349805113394561256114405516268327844417077600706338925700541132427248154001839889821951788373396722269380770676497593632625101787923410356761496503422268426570092682001422760110365492042941994315305706799374977908321188315701280324014579516444302872321248551181918210257019111569142476724104725119996728243038067890, 519108240637049612049768452334726393343488197329741907401413946489572651360706374696221919463352965, 1038153074897088932032863605732372269385291352505138363877348951204871831705807208702123092266986117, 1978884774864108052658285266367593821593352909391604809670510115265691220574203314169639153612934106872627496090783252910206613831946014641649395174676570863493445560434665255, 1978884774864108052658285266367593821593352909391604809670510115265691220574203314169639153612934106872627496090783252910206613831946014641649395174676570863493445560434665255, 1978914966563506624989103301097698224498913682673548811280285792680552932074509253797470409280002724354751823268271574122753151123503189092417840625875395146596817352526898983, 574503453231584, 572304396388832, 572304396454368, 46737872194016, 431567310948832, 46737872194016, 9354443229664, 290829688375776, 5580652095617125943137865301866629628467490, 150092065802720, 150092065802720, 290829688375776, 290829688375776, 290829688375776, 9354443229664, 572304396454368, 46737872128480, 431567310948832, 46737872128480, 9354443229664, 84121301027296, 290829688375776, 84121301027296, 150092065802720, 1461501642796709287267559656307274911220893784482, 150092065802720, 290829688375776, 290829688375776, 290829688375776, 9354443229664, 5709018014691306934452559469506701447383783714, 431567310948832, 5709039792762789874514221125481506711805139234, 9354443229664, 290829688375776, 150092065802720, 2967987461566975531121153432928173294753633979464163962638435713687250517249987990875709845212859283789037461296166708732244468614120389174445722584390291377917118198404086822, 150092065802720, 290829688375776, 290829688375776, 290829688375776, 9354443229664, 46737872128480, 431567310948832, 46737872128480, 9354443229664, 84121301027296, 290829688375776, 84121301027296, 5580652106001719660207520561179559539546530, 150092065802720, 150092065802720, 290829688375776, 290829688375776, 290829688375776, 9354443229664, 46737871899104, 46737871899104, 9354442967520, 79723187210720, 290829688375776, 79723187210720, 290829688375776, 290829688375776, 290829688375776, 9354442967520] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_4 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨1, 0, false⟩) 103 ⟨1, [0, 1], 1, []⟩ 4 [576702510533088] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_5 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨1, 0, true⟩) 103 ⟨1, [0, 1], 1, []⟩ 4 [572304665348576] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_6 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨1, 1, false⟩) 103 ⟨1, [0, 1], 1, []⟩ 4 [576702510533088] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_7 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨1, 1, true⟩) 103 ⟨1, [0, 1], 1, []⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_8 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨2, 0, false⟩) 103 ⟨1, [0, 1], 1, []⟩ 4 [572304531130848] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_9 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨2, 0, true⟩) 103 ⟨1, [0, 1], 1, []⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_10 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨2, 1, false⟩) 103 ⟨1, [0, 1], 1, []⟩ 4 [572304531130848] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_11 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨2, 1, true⟩) 103 ⟨1, [0, 1], 1, []⟩ 4 [97320910292831127581058313721749063131942283964346021257109056343344016366945970404632539034759940, 1070530018041907087673878986462700250826875873401795393921185336782167541004024271885697805436793604, 32441293107534244247159011500158175835302494556487677181002961795753768839283157083880430290285316, 2108619732968211333007863253262112024882505681751716754516150963975414145316630286793006684292985604, 4184799162934116273470436306276958591399712921086944642559602995241313048977511557819134652849533700, 64943970054067600678300437710975045677472042736234410950801470126728702553736984606417064591117701, 4184799162934116273470436306276958591399712921086944642559602995241313105381155438239054461040538372, 66470182058391521447061914160197907148437823957937815433613785131498076269930007978980722246951318276, 66470182058391521447061914160197907148437823957937815433613785131498077322798027080152714522289976068, 64943970054067600678300437710975242482388199223291437125982843343299374649003460170811092791528837, 291962731843401462150812346953504257559813004248127439288662203217070930549020181646150483258572548, 97320910292890121742271095692346471968354377510220540892406852920956000763999921043533818193195780, 291962731843460441905636554374169896577217426953087215451521587634346506463374845409021801158606596, 32440303108107832245653670360449519116445054111094036407662821606721343223912096418200553408115460, 129824574336572515676187331885680789554360111251589561328637613153761262323164485760611792972883589, 32440303108107832245653670360449519116445054111094036407662821606726137533641932111559587388404484, 551485160578754158249126678266815253934631402135609079167151442206714596388018875611413757980521220, 2108619732968210641501211674865387073570137481387809067839107180279275816546482845821801610487214852, 4184799162934116273470436306276958591399712921086944642559602995241322656398185856013564165314786052, 33251311180870641596884077175029921143872784091614547814871049204482941538591738515925425347079910148, 33218935722611754430795465746279040733141405270160937516561120920800246274342540932758696127007362437, 66437805115254270909713555563728376999745610915912846933776852868596844005879720152806271826084537989] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_12 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨3, 0, false⟩) 103 ⟨1, [0, 1], 1, []⟩ 4 [572304665348576] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_13 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨3, 0, true⟩) 103 ⟨1, [0, 1], 1, []⟩ 4 [1461596415689467893476774525164921084529287906787] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_14 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨3, 1, false⟩) 103 ⟨1, [0, 1], 1, []⟩ 4 [572304665348576] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_15 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨3, 1, true⟩) 103 ⟨1, [0, 1], 1, []⟩ 4 [46737871899104, 7225468688201773901813400858818880815276005794, 46737871899104, 46737871899104, 5798220995495814020890515097672524943053592994, 75165892372369277606330301286044813789386338622049855436427542890732956263837619173107915667812925508788156991442909975490868465462370061648499651326679611165305348417355393301341844252320017040449584603381823516838851976127428013089502146763444521501317148977162843351161414025340213177195428582114304630035260113398107263119206583734808664101597782073122800268827220307779958982518447650696259059638457147012581231145809932918193610213420310493483896241260418231734693295618653982786127292034337628844, 46738006215136, 51173900516750971133407554432584296478504953669238994138274105935887417536283483859070472665490422468435206240719581778199721379309653754104304451152087213919717956109941010243411431757601553233993251929843013738344721182274351262876542542212597281192368201528584136008570624169184625065865985043439891293568574791984023925286832995468035297821149784693915712906195272496939, 46738006215136, 5798220995495814020736980928290019532776446370, 46738140563936, 51173900516657897719065774401366008528610156190392840064730188819360531937643416780643864549161534198242506126254599226627975800318629210244392672008140997030258656446435247604043062354892642980994373678063930432816891494533787037401315665876048129020460845922356820284198774848791437680725790919271591189255937892971914497405052974037978189406275382658942385318582071359275, 46738140563936, 46737871899104, 458229454616334865219114413443657260111191497527606458374786828456532255853672900787283326165538795907592129234853092787632397500129642108069167983921809569975408317569361267457201001177458759153521685745087816833242509566581206875283501632914855038984076838761, 20818564581586153378616880972355766462771703453633729040624499815682205770134591231332197260184467908, 415284540237686997862252803045260242797679503394053491330965434691582464916534675828309785308939106756, 16658095707978891972971865177521544633798913718393614592934017852103303219658896205935593436288858564, 215971318931834520752368775525631600446829725275650484134152752623025862509483294449353585263288465860, 129887936237173152286276539250309119909776877739461675537325189857358756016325149493016153910583781, 129887936237173152286276539250308994954274556160350103699206685548467010810569772198817486523378149, 481722281992970469563627796120422596337239811129175795159883881301835156123679498458830199952043620804, 415284540237686997862252803045260242797679503394053491330965434691582464916534783409720688820393032132, 415284540237686997862252803045260242797679503394053491330965434691582455290313002066133726276085823940, 415284540237686997862252803045260242797679503394053491330965434691582465518173678362885981712735746500, 46737871899104, 60383398811643114294265332900848268826943747781430196504970730575853258694441965785443168174745650971992250370584466857516902669545039768671015503817130670982360843641638, 46737871899104, 46737871899104, 264678599123815326217986089841852684068743835982969858250185577081014754153579403841418628236563995009358355817511193583789590825111549308920370173198829169859044578401318, 11507233544391136485030577540850443518211037602, 46738006215136, 46738006215136, 46738140563936, 46738140563936, 46737871899104, 46737871899104, 46737871899104, 9354442967520, 9354443033056, 9354443229664, 9354443033056, 129824574336572515676187355365421948804714955396326161542480498293466712286546014792925719454659397, 129887934303580423531414649100114583978442800690691332871557172300279484183120419734057857315547621, 9354443229664, 9354443229664, 9354443229664, 9354442967520, 290829688637920, 265799623515798081054442861461232670445896795195103067541527664569941472998258955464357488710878706116, 16658095707978888284936390092739011560132949983119440263989784339057190394188305010008999196300097988, 290829688637920, 290829688637920, 290829688637920, 9354443491808] = some [] := by
  decide +kernel

private theorem solve_1_0_1 (N : Machine4) (h11 : N 2 1 = none)
    (hAlive : ∀ q a, ¬ (q = 2 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    (hm : Matches N (baseTable 1 0 1)) : CertProp N := by
  refine branch_one_sound (tb := baseTable 1 0 1) (q1 := 1) (a1 := 1) (rem1 := 103) (cur1 := ⟨1, [0, 1], 1, []⟩) (step1 := 4) rfl ?_ N h11 hAlive h107 hm
  intro m hmem N h11 hAlive h107 hm' hsum1 hrun1
  simp only [moves16, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkTree_sound tv_1_0_1_0 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_1_1 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_1_2 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_1_3 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_1_4 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_1_5 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_1_6 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_1_7 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_1_8 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_1_9 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_1_10 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_1_11 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_1_12 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_1_13 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_1_14 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_1_15 N h11 hAlive h107 hm' hsum1 hrun1

set_option maxHeartbeats 0 in
private theorem tv_1_0_2 : checkTree 4 (baseTable 1 0 2) 107 startPos 0 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3 : checkTree 4 (baseTable 1 0 3) 107 startPos 0 [51136422218208, 12845253755993649193642009381884802845974200803, 51136422218208, 265783407324243823925091538273394505047843838937819720671400158273792476601127160218155098115355652868, 262242318715360, 265783407324241950386722320669075691207048239042056866394313152616176204028314590994291199733403955972, 262242318715360, 21288498328859408250784023047306254754, 150092065606112, 431567310948832, 150092065606112, 265783407324241950386722320669075691207048239042784203145153799086061122787313188420967878811057337092, 431567310948832, 431567310948832, 431567310948832, 21288498328859408250784023047306254754, 265783407324245712242502084883385901909762222160078963352292357680996476865917269083047745611360567044, 51135918410208, 51135918410208, 558349945312, 558350010848, 558350207456, 558350010848, 558350207456, 558349945312, 558350207456, 558349945312, 265783407324249488848397851043530160752009262265485754001085847323501754282904276219512543467465290500, 265783407324241935634580420329945558912384384100960169067698056548913217696675172171459512767137133316, 265783407324249489194151176832728523227665446365684754799776216294026497051434311875620584610200761092, 265783407324362786104837665827003691538327928457823696385116850612398621785209140740775698502120583940, 191873507428832, 923604651371657512379460426179441747744009965215007563120894843594860126866620028319968449472037046375755128094058930095963264812920983119292228135498300925222889900920170151577448355733142352605919985590768389396808323358976720323603403707890589106176076738761, 191873507428832, 150092065606112, 150092065802720, 150092065606112, 150092065802720, 150092065802720, 150092065802720, 275742580527299594880895355841377096870226487162665943673478752717274850072201018996080941410237573, 332611130001888, 332611130001888, 282033595353568, 282033595156960, 282033595353568, 282033595156960, 2967979913699711984601897959554136855495050992523339945488638817188203483668116420391672819672048314196862724375279550176226409955431661129300709289302529033438543332336727078, 245307557617134637823643233783235856335069188133312397590485304867239234161274034729690669765177681970257873353333707800329237154345619851051995479364741474629695382173479, 282033595353568, 282033595091424, 282033595353568, 282033595353568, 543717563861472, 543717563861472, 558349945312, 558350010848, 558350207456, 558350010848, 133816252495993256010506871710141419120396685818851509584054863672362657718031875199846311085918021, 145981366161511564214147268771060146415893973878218577644733140271304227210919271663387384487043397, 558350207456, 558349945312, 558350207456, 558349945312, 332611130001888, 332611130001888, 282033595353568, 282033595156960, 282033595353568, 282033595156960, 282033595353568, 282033595091424, 282033595353568, 282033595353568, 5798222016342914783552372499000976538051058082, 11507234565238237247848386963205150956602825122, 558349945312, 558350010848, 558350207456, 558350010848, 133816252495993256010506871710141419120396686182519874166216012879539859159770209946046537744172869, 145981366161511564214147268771060146415893973150881815965924584651103515769283197368512591543886149, 558350207456, 558349945312, 558350207456, 558349945312, 84121771051488, 47099263715152108716743742955705732899067134435, 84121771051488, 150092468718048, 150092468718048, 282033864051168, 558887340512, 282033864051168, 558887340512] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_0 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨0, 0, false⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [1461518373842650967241640947978049738673375713570] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_1 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨0, 0, true⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_2 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨0, 1, false⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [1461518373885186263106758255910971564602413848866] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_3 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨0, 1, true⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [564607848581600, 1461507212538491049188329624896635204793615292834, 564607848581600, 563508303366624, 565707393796576, 1461507212538491049188329625413144038857482738082, 565707393796576, 45638595414496, 332221144624535281104793390140474964887649058535492096638969781915375446138282697189595330126813541124, 45638595414496, 290829688375776, 81922479163872, 290829688375776, 81922479163872, 4184799162820819822775432500951564837380077316478323638363224660960866487819720217089437511197078276, 1461501640074450351900129320147880167313375271330, 290829688375776, 290829688375776, 290829688375776, 9354711665120, 5798215891260310206668491527579137875217783202, 353914939711511299082936242387204262893858, 11507228440155632670963297061351994053914302882, 558349945312, 282033326655968, 4184799162820819823675831786860935572993765296269549190669657116755520029872638486955609113372078852, 282033326655968, 558349945312, 282033326655968, 558349945312, 45638595414496, 353914950096105016153181795258693065939362, 45638595414496, 290829688375776, 81922479163872, 290829688375776, 81922479163872, 5580652106001719814950615765410652793903522, 4184799162820819825476630358679677044221141255852000295282519898547732492728739045534846012906222340, 290829688375776, 290829688375776, 290829688375776, 9354711665120, 35742722034144, 35742722034144, 558349945312, 70927094122976, 290829688375776, 70927094122976, 290829688375776, 558349945312, 290829688375776, 558349945312] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_4 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨1, 0, false⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [564607848614368, 567906484160992, 564607848614368, 563508303432160, 565707393796576, 572304664889824, 565707393796576, 567906484160992, 1461507223427526790658669940660657081753097247138, 567906484160992, 5720173831818827575065297412326766384665106850, 91522617654237644213048898375139762052818573730, 11440336753313415350930870809847632762542005154, 5586096623872454985107944374062097164704162, 22880662596302590902662017604889365518295801250, 45761314282280942006124311194972831029803391394, 91522617654237644213048898375139762052818573730, 183045224398151048626898072735473624098848946594, 732180864861631475109993118897476796375031126434, 572304664889824, 51136354650592, 150092199823840, 51136354650592, 558350010848, 84121636375008, 282033326721504, 84121636375008, 150092199823840, 150092199823840, 282033326721504, 558350010848, 282033326721504, 558350010848, 572304664889824, 37941812464096, 37941812464096, 558350010848, 70927094188512, 290829688179168, 70927094188512, 290829688179168, 558350010848, 290829688179168, 558350010848] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_5 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨1, 0, true⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [97320910291060875955413333562098117151477228926011156827187844611819392524623275379948651565757188, 265783403364243998562348337395282773912969729953633502410069278720504525030982767921198917136807047940, 291962731840096987767532097260094666538434075153271734057599563825489636622120019312384304377985156, 265783403364244056648907069980607669823208658784201748090940956550980952460662808336991304258949427972, 551485160572145204080170463423771658209745667380554639902861112858619901240171280222058215444325892, 364496732621280, 732180860097667953622982818323853716400045594914, 364496732621280, 290829688375776, 4184799162820833652022133521819027045757717218649489718852456532058043777769047978659898074136261380, 290829688375776, 4184799162820833652064339738346028798989608842702203416616820520145338559095751397854345057850831620, 295227600669152, 519060720658253167091715037456358090760829825282080247153855766498769377129425588066290362833669765, 295227600669152, 290829688375776, 290829688375776, 290829688375776, 290829688375776, 2108619732964434098577120573007744053305400437198639257746154866567981854020145231681543437940096772, 777958882945976245085334988609446268101821765922, 22900252099196998489453255204573311739962105122, 5575207577746390927722451308147721337084194, 551485160572204090207537675112214711147564101394459436034423623615947495752790532333385382071903748, 5580652095617125943138455597676988334119202, 2108619732964492869495585404823734700923049128537939803862574068129912905594229727559158090024025860, 1038105554918292487074810190854004041775934373404926999315574151483350940750429300002174059458301573, 5580652106001719814950615765410652793903522, 4184799162820819829078227502317159986675893175016902504508247258833023970964555318958934726472315652, 146793430321632, 145694019291616, 146793430321632, 145694019291616, 91522972228453591236920615876025179001689512226, 145694019291616, 145694019291616, 183045216231374242524142836004692045064028862882, 16609435438851082159575856843189006132245850839463385574085299395305020014528768012272854946303742724, 291928965188064, 366090429719201051351841184356427139481712253346, 291928965188064, 290829688375776, 33251311180810216821873558265031634647239533272462118902154670025930317423735539237175770371378439684, 290829688375776, 33251311180810216821915764481558636400471424896514832599919034014017612205062242656370217355093196548, 295227600669152, 295227600669152, 290829688375776, 290829688375776, 290829688375776, 290829688375776, 544816639576544, 2788294992663904911957487062509634337151266, 544816639576544, 558350207456, 2225973642871591956277359612585725085686926947518639202102767402571254585141522509019908504579447019065086805724299682552344668458226186101689970353093887205797052942964775974, 290829688375776, 435965089024480, 435965089024480, 290829688375776, 558350207456, 290829688375776, 558350207456, 291928965188064, 732180859417113604374822960462065752307900914082, 291928965188064, 290829688375776, 290829688375776, 295227600669152, 989344249724553162061952435884023249682255214479702614332163203898054462876806807735874939488608386197812763402672696524137387756818080943725356655634760175195326511391439910, 295227600669152, 290829688375776, 290829688375776, 290829688375776, 290829688375776, 399681104710112, 21288498328859408250786274855709874594, 399681104710112, 558350207456, 1979126308574496063955547684212947643155828233043942735168773793810034175035809843163057333252889015873281643150964080168613199190441178275097667437836261650853691431603428390, 9354711665120, 9354711665120, 558350207456, 9354711665120, 558350207456] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_6 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨1, 1, false⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [564607848614368, 567906484160992, 564607848614368, 563508303432160, 565707393796576, 572304664889824, 565707393796576, 567906484160992, 567906484160992, 572304664889824, 51136354650592, 150092199823840, 51136354650592, 558350010848, 84121636375008, 282033326721504, 84121636375008, 150092199823840, 150092199823840, 282033326721504, 558350010848, 282033326721504, 558350010848, 572304664889824, 37941812464096, 37941812464096, 558350010848, 70927094188512, 290829688179168, 70927094188512, 290829688179168, 558350010848, 290829688179168, 558350010848] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_7 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨1, 1, true⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_8 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨2, 0, false⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_9 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨2, 0, true⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_10 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨2, 1, false⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_11 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨2, 1, true⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [97320910291060875955413333562098117151477228926011156827187844611819392524623275379414810753184516, 551485160571319076932315777216689011842360611971230275349948292567808881216746349765982936124044036, 551485160578754163764072304461711009568470276129396711727430750155776627605757603371820489696817924, 551485160571437094072794267323622588307186593751398013785966208554636776486475915600615025504893892, 551485160572145196891044914991139691044205703734988120706194712160690272028254799089178009288320516, 551485160692050608043731197682838272340579022588983960984246470213189281241481157998634342837072644, 551485160573089334014872835846608302762813557976330028194338040055313434186091325766234724332942084, 551485160578754156560878017186745124658966437845050883556166068903741398520322393674738594601972484, 551485160572145204080170463423771658209745667380554639902860468115542086395020162704207339254457860, 551485160631625833919542834751588593577052310725552986355936922848150410456863150359223277115667204, 551485160692050609844529769501579743567954982171435065597109908104032788558400857690853039971447556, 1070530018034485836490099653347073034981969090515570323644857859804502224909106780336742233041744644, 14663119243267510039139763549363444147027144785048368352164094943787202582333557047960150660046697515086578092734419092505093323654935708270930566601029511453786638219089083321621705920978086356878353007855702855671899925906059346258593696831305523658880076738761, 2108619732961144133234967836335535100124103938192816475106786235412952539400843925431032791502911620, 1038121394910280383057913843236597761457933780646399527947757580008692239901894544988613267538514501, 32440303108063574019154081151311163897504269056540699427571479551216047217659828714123296118092548, 66470182058512384821954275221096093931709200465069821816187430767216630854844786772666045934743008004, 33251311180870648972054628058685616555591023580189660635416658602517360171782695833876192502837621508, 519060720658253167091715039972044809103694134925598007471128372142096304993752275633564791662791237, 519060720658253167091715039972045009032497849815800493882045202077217112905272996788354409846072133, 2108619732960775560184400773815260831477866691223430264021904026855185691503320978777651488753922820, 2108619732961129611595284690004311122564371730550755054888866777793845681980833821482936010967316612, 2108619732961601680143129911589711510679711782987188109378150446448067082314829428100846561918199300, 2108619732960657543047439468418910734449031678114322000399583271271689837826098329544038588078043908, 2108619732964434091430201241102113839371752097605786436313852453957347006134932169743122739623296772, 2108619732968210639812963013785316944294472517097250872228121803191118208806897022686407147231851268, 2108619733021082317171627831350160413212558389977752975027892657135527220743437779370891829745545988, 2108619732968210639812963013785316944294472517097250872228122600603300555151584901885911403537314564, 2108619732960657543047439468418910734449031678114322000399583755775294301427934002981712060263641860, 32440303108107830446613690896999787607064576682162384165221974212264371142450203925657311533806340, 2076211109836584743643006706435463694846596845233508110235624078838978913007147677784207770584552005, 551485160572204090207537675112214711147564101394459436034423623615956971564962442878681619238233604, 32440303108107830444855098541708047889069092346632646758373636104684565069119193127370627274191620, 2108619732964492869495585404823734700923049128537939803862574068129922381406401638104466851314990852, 32440303108107834046452242179190990343821011511534855984100511886371579702958592511808021542941444, 33251311180810216821861248118544592469213564882113410740306730528668857841963444167445418056911680260, 33251311180810216821866523895610467688367551335119999952527276027179769689629282094844723929876281476, 123672748718989379644316739348933566873075661861045212379205533172177662691953166599819572401904426420389614589242587240039918237286332903708980503813646750350669677842692902, 33251311180810216821873558265031634647239533272462118902154670025930326899547711147721329615162107396, 33251311180810216822759888812098671465109257377569106555206313909506699789548573006493240721219252996, 33251311180810216821915764481558636400471424896514832599919034014017621680874414566915776598876864260, 33251311180810216821972039436927972071447280395251784196938186004022079360221846989928622081164964612, 33251311180810216822759888812098671465109257377569106555206313828756099045614933727586961809188320004, 33251311180810216821859489526189300729495569397777881002899882675064882499491948830084804844837663492, 33251311180810216822759888812098671465109257377569106555206314474760904997084047958837193105435783940, 11260833093369905533818448666900967196780355414805045947361765573719431497551184830070123213920542860971244004469963557780314620218836530975533966935488153535739281793973870102011368236712757236378731984667374658436101498953781821214800442705520871393921507469929931678886733287967225210612849135590022230361385374893719150649364426808114588109669239736317776021952468944562761897601827763726439127677120156756896423421528184110488574842792930915889155858013036107932154979875983238101098601608159423294724215259763451829825135221456835225134922947224417082783613151438520464727432219632709339211743624597855370141679636901244517641211309007363656680892209711, 66437757595275703122954957428060648617085367975018858289513570301671127746314152476871872144016443429, 66437773435267455099918764251494321238570139953553806241330651249346930633164974536086026263922774597, 33218888202632957985837412330614520361534505492204742308795964357739707373983363054828410549771782725, 52402071005664252050020803818521210155249323525874816583048300631367359452426831319690514598441697461846849608259085950783792570516184398021133684413601595354834602423207729996125168618650084784257407431163053821435867700476102643953442179092374441135908517660055393024154231492315040552481768179975299907276937118269093001336419999652028957120256320842846443771332930584682795, 494660804796162420465658986508383719028628138404404672764272614202904628376963008248083490097998683389016152475420986430722616446455188982500511131317333253321203806034143015, 66437757595275703122954957428060648617085367975744774471579725095516902207172868615713236098779588645, 66437757595275703122954957428060648617085367975744774482417887342753385797892866975126618702717003813, 132875514200551213644534064180571755713789664955398793944621437528867562847122939670112676262382741541, 132875515190550934177364707523055731321570498307621634555704926766157378439389971946454538168858448453, 132875515190550934177364707523055731321570498307623055135317580689433006178060497169798185643463021125, 247330401962586354963785471177982091766400022002322257020378953220094080759922936109852435070723139424339380084026507722043369894697872911805135412798615641821049489528149799, 66437757595275474464755502148063856628138711137956649645084560340246798522539598817512077402804193861, 132875514200551213644534064180571755713789664955394532205846980777143850355862026767659502380422658085, 989321607792759323165994675611714353092651334949145295534165252469290000325576130665864230147971896290698754003907141495102512859293333326498444067350877927093939179441024167, 132875515190550934177364707523055731321570498308347550737771081560003152900542457063292568496153801285, 1978669629521810901967586355757287956590895061152052388576793596389467800511099385150529881112960672929553490420192733387236889831166109056871005614123582945697565506897173542, 132875515190550934177364707523055731321570498309074887499449890277124555099851371691022502275354702405] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_12 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨3, 0, false⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [5720173874343738846465536865972521417711851810, 1461680402651959130029003430153460792938017626530, 5731346067549782963215274314005547160601403170, 36842267478496, 145694019291616, 36842267478496, 558350207456, 73126184749536, 290829688375776, 73126184749536, 145694019291616, 145694019291616, 290829688375776, 558350207456, 290829688375776, 558350207456, 22880662766433389769414180843465540282973461794, 1462931683527082934211835535845915172096892246434, 22925351539257566236413130635597643254531660066, 91522618334791993461208756753437615744019896610, 1461501648241227158002884557911681595915321252258, 183045224398151048626898073768492347761773033890, 291928965122528, 295227869104608, 291928965122528, 290829688375776, 293028510304736, 290829688375776, 293028510304736, 295227600669152, 295227600669152, 290829688375776, 290829688375776, 290829688375776, 290829688375776, 544816639511008, 435965357459936, 544816639511008, 558350207456, 508532789348832, 290829688375776, 508532789348832, 435965089024480, 435965089024480, 290829688375776, 558350207456, 290829688375776, 558350207456, 366805460973413231700370257067439565133136828706, 291928965122528, 21288498328859408250785148951508064674, 291928965122528, 558350207456, 73126184749536, 9354711665120, 73126184749536, 9354711665120, 558350207456, 9354711665120, 558350207456] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_13 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨3, 0, true⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [1978643213742763555902738753784692338694144220399539075897894779059690210813166100445293245307841169370503587738311706466243536316953664440676329966688912828420015224736693543, 265750982861126169859576587921005142905609947173229027932924615033240576337154407268696627781507360805, 36842267281888, 181977802410464, 36842267281888, 36842267281888, 146793430321632, 146793430321632, 365399103980858258397105531783438778888606489506, 3315255037369767036189059801613535574255268435376374138610938306481970679499079382477580991611266190787925986214190349790199124040854341174559903573645789184398521846387948838, 730775907110158896111973085944901574325183749026, 22300851557620682237977621975948267657141154, 265750982861126169859576587921005142905609947173229027932945783318879710094167532263303607625503615013, 1978665855674558273573243845568018270493058937667220385159850535411745025824366184099513072340166861691836146859998226962945294885117592254707330370254396940608093703854087206, 41240414718432, 145694019291616, 41240414718432, 145694019291616, 732180860097667953622847418041761067573772851490, 145694019291616, 145694019291616, 2788294992663904931300300174091901318764834, 732180854653160467481549072283024409795578861986, 247330401991379403299979195756193066832242287857675711093284924317354820387112840692900126093574760958837886314526540637196945376808825592633379141064378405873968415366669095, 41240414718432, 145694019291616, 41240414718432, 145694019291616, 732180855333725201323445342096674435020748790178, 145694019291616, 145694019291616, 2788975567782340544639769081178256586086818, 732180855333725201323445342096674435020748790178, 6433789511384616819122134153974155193011460386, 457611642666539547601744012881942913599119874466, 6444961662055365070754563669085284638454243106, 290829688375776, 290829688375776, 91522609487460838110293661718146285217038506402, 183045216231374242524142836004693170968230672802, 290829688375776, 290829688375776, 290829688375776, 9354711665120, 353914939711511299082936244638995486644514, 558349945312, 282033326655968, 61857661841102598531227433624719154827394347617363220056174760844180560234816675468257072952925397487576333067161607711054363727053518426365722737542869638549904917481389094, 16609451278812856858591225824071324514897159800782684831838015390572102286832947056862877996356822533, 282033326655968, 558349945312, 282033326655968, 558349945312, 81100758978735554310785301930905910925815950583284804917186127793183837396917307544077157281444612, 353914950096105016153181797510484289690018, 275742580527771666122904065628902460312772796810545382147597847006854119096843305089798248498624644, 290829688375776, 290829688375776, 30916300646626404943970615220935109247498874605638490427478360521972909152680787658586849166832954871418891592461972748460214659120331798702580104006166456147743424318763815, 290829688375776, 290829688375776, 290829688375776, 9354711665120, 5709012570183820793154213710770043668652923298, 558349945312, 259558068713490135672823184860859127550242317773606866092523171482653833667333030513300150163223109, 290829688375776, 20789989661290452104262122344494487794773699511266945094007254246537671166635354938912569698341, 16609451278812856858591225824071324514897159800055348070159206834951901575391310982294409526050409989, 290829688375776, 558349945312, 290829688375776, 558349945312] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_14 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨3, 1, false⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [5720173874343738846465536865972521422006819106, 5935226321948744131552892056902218147731746, 5720195694950517651644506454869222984143378722, 5586096613487861268039469709677223962777890, 22880662766433389769414180843465540287268429090, 364496732555744, 435965357459936, 364496732555744, 290829688375776, 438164045171168, 290829688375776, 438164045171168, 295227600669152, 295227600669152, 290829688375776, 290829688375776, 290829688375776, 290829688375776, 22880750048860504990130059199052346535814667554, 732186445534973889771885879849018642932228462882, 732183641650816141697782528160864718768743422370, 5575207588130984644792106567460651248163234, 22886237952733022424894914304345939181917216034, 5591541131358595973969283586240704823728418, 22886325405301321106080024410066793220057111842, 5594263390293963559048243038436426150615330, 91522618334791993461208756753437615748314863906, 91522967464500454344072270175784840742499817762, 291928965122528, 295227869104608, 291928965122528, 290829688375776, 293028510304736, 290829688375776, 293028510304736, 295227600669152, 295227600669152, 290829688375776, 290829688375776, 290829688375776, 290829688375776, 544816639511008, 435965357459936, 544816639511008, 558350207456, 508532789348832, 290829688375776, 508532789348832, 435965089024480, 435965089024480, 290829688375776, 558350207456, 290829688375776, 558350207456, 732180864861631475109993119487774788173127784866, 291928965122528, 21288498328859408250786274855709874594, 291928965122528, 558350207456, 73126184749536, 9354711665120, 73126184749536, 9354711665120, 558350207456, 9354711665120, 558350207456] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_15 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨3, 1, true⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [265750998701117685802269989398858668251420377042398212843533004639124712114378035594120965925587515429, 265750998701117921836540394744438816376792140896842988209478292638558127194879556699003072995151557189, 36842267216352, 60384320178204667747138974643694219704351174359414842341409638576522842203925300270960039428241483484273454684284783912074114435541875802149555317593772861851905714613415, 36842267216352, 36842267216352, 72026639337952, 364496732654048, 72026639337952, 291928965122528, 291928965122528, 1657895127520, 265750998701117921836540394744438816376792140896844408789090946561833754933550081918516408986677523013, 265783407324244827047231898728703524534822340344539422516609015803953785657168576239164245479656794468, 1978665855674558273573243845568018270493058937667220385159850535411745025824366184099513072340166861691836146859998226962943798307440965410119089796985695466795966028930079782, 37941812464096, 37941812464096, 73126184552928, 73126184552928, 73126184552928, 3864539365884821488096495488144484158101493781825233317400433120317046877157326685258037321567962902924372496705952397089132070701441874090668478075469749851648343747286823, 293028510370272, 293028510370272, 73126184552928, 45638595152352, 45638595152352, 290829688375776, 81922479163872, 290829688375776, 81922479163872, 30916302028692722547193696445359579036662340008246764252162433142162804676287782889008646637906571007607951364093780290459044667583343434339454458024614061281445391394354983, 290829688375776, 290829688375776, 290829688375776, 9354711402976, 5798215891260310206668491527579137875217783202, 64896450075271155720247045526196142585795354554485898801931214480735540452653262848523091792488261, 11507228440155632670963297061351853316425947554, 558349945312, 290829688375776, 16609451278812856858591225797237334718575441836893691152729059134188946635783137015317455295748236805, 290829688375776, 558349945312, 290829688375776, 558349945312, 45638595152352, 45638595152352, 290829688375776, 81922479163872, 290829688375776, 81922479163872, 1978669629521810901967586355757678175531825987020325816190510667618060073533203953933089526953377137130674193797573375985811438514051972597471968425414396586483160387335207974, 290829688375776, 290829688375776, 290829688375776, 9354711402976, 35742722034144, 35742722034144, 558349945312, 70927094122976, 290829688375776, 70927094122976, 16609451278812856858591225797237334718575441836166354391050250578568745924341500940748986825441824261, 290829688375776, 558349945312, 290829688375776, 558349945312] = some [] := by
  decide +kernel

private theorem solve_1_1_0 (N : Machine4) (h11 : N 2 1 = none)
    (hAlive : ∀ q a, ¬ (q = 2 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    (hm : Matches N (baseTable 1 1 0)) : CertProp N := by
  refine branch_one_sound (tb := baseTable 1 1 0) (q1 := 0) (a1 := 1) (rem1 := 103) (cur1 := ⟨0, [0, 1], 1, [1]⟩) (step1 := 4) rfl ?_ N h11 hAlive h107 hm
  intro m hmem N h11 hAlive h107 hm' hsum1 hrun1
  simp only [moves16, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkTree_sound tv_1_1_0_0 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_0_1 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_0_2 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_0_3 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_0_4 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_0_5 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_0_6 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_0_7 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_0_8 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_0_9 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_0_10 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_0_11 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_0_12 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_0_13 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_0_14 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_0_15 N h11 hAlive h107 hm' hsum1 hrun1

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_0 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨0, 0, false⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [1461518373842650967241332670718068073534841723170, 1461685630069669384891653807598942559389336246562, 1461529524257785528418020746510126223644632850210, 1461518373842650967241332670718068073534841723170, 1461551825088054650771396898094242576640773233954, 1463023679885816726094222902645918461501945977122, 1461596426748592895478149201262475177079937734946, 1461685630069669384891653807598940589064499271970, 1461507223427526790658361664581271470562589317538, 1461864035350703280628626236073629903699158546850, 5720173831818827574757021328329469175796898210, 11440336753313415350622594721238649535313517474, 22880662596302590902353741507057010254346755490, 45763927650858894813215433795678807672277211554, 45761314282280942005816035078693731692413229474, 5586096623872454676831864988450906656774562, 91522617654237644212740622221967174568546179490, 183045224398151048626589796508514060320812087714, 732180864861631475109684842227795374834407479714, 1462934476564740236680718296309454245786035460386] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_1 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨0, 0, true⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_2 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨0, 1, false⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [1461518373842650967241332670722679759553269111074, 1462934477245304970522595223240816272568979855650, 1461518373885186263106449978655601585482307246370, 1461540674672920089594708822306796094957223452450, 1461551825088054650771396898098854262659200621858, 1461551830702713704966881545244535285292234480930, 1461551825258195834231866129830541566375353163042, 1461507223427516406064644594930621591868471810338, 1461685630069669384891653807603552275082926659874, 1461685630750234118733530734530301489947536824610, 5798232905368271659866132495751541698168133922, 2193682856086185606495654607203022496634976114978, 5753653363183876814113954446868353955730070818, 1478762496994600079498892879447812944519402396962, 23014473192565994624378228506786236985464887586, 23017347898001742712517567095469820563315267874, 23014560304851926384624875130685739518127020322, 92771464829862845249964968208581574834384836898, 184115660167680518537384719916030230544509868450, 365378207836189401083988278428625246081334155554, 1462934471120232750539421159481150014555350407586, 5709045237280660609530845474518141934024825122, 22858361936164267415729752003978170240903192354, 22894687972074290764167933834679908782761352482, 22847298718386229729522938701663156929664424226, 732180864861631475109686051158224423699375757730] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_3 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨0, 1, true⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [1461518373842650967241332670718068073534841723170, 65007330019187234384353058329228940793649298448507057248289009719347533445018993518677193986419333, 3665779701565680629832471590033665978342600854656062355502477246741541989896464974466503695573406741239600345155612550738150988913541313040269200728079147871618523100916113265571312920488325070252755068268219792596261640728345375991479853566542536016132106782760, 519171600602169245755821076254818879412340956503957654039167356524327936905182095012873030446361221, 1038216434862208565738916229652464755454144111679354110515102361239627117250282929018774203249994373, 1676866322155336747872190708248606473743107024424420111245699394536482121909029459317719020670270247779153961026953592367540169914059176481581421289802951645465757513010134049411435913717193694152001679370991800001718482534591228857379531740423697346772752355729211438866025970253314241892450895608729311568279772106832894194826458704455327696870798493229817297913571747106182954, 1461540674630384793729591514378485919862240616226, 1461507223427516406064643385995578605185262459170, 1461507223427516406064643385995578675554275072290, 7225479917509497699047491533840135934333458722, 359359457582246159755845325433578191886626, 7225501695580980639109153189815011567498991906, 10910313855205173169349727423447543355682, 2798503463671533065861314511504492731603234, 5586096613487860958553279295585537919850786, 732180864861631475109838376392568305280059742626, 1461507223427516406064643385995578675554543507746, 10910313855205173169349728549343155231010, 22880662766433389769109530374777777087245753634, 2798503463671533220604409719113281411520802, 22925351539257566236113315888635082649212328226, 1461501648241227158002575071721268630129185167778, 732180864861631475109838376392567179375857932706, 7486192554555632538769818459332161892461708910188112856544348804461070846228626276237555342641262160946458188480774376512890224935119072566061363406078238230445735079, 7136276596433008285542885197375920218422941986, 359359467966839876825500584746508102965666, 12845283700820844608540553902844545166434408866, 10910313855205173169349728549347450198306, 22880662766433389769109530374777777091540720930, 2798503463671533065861904808440751344097570, 22969953199795810942860783372035968649414090018, 5586096623872454675622934554898467830929826, 732180864861631475109838376392568305280059742626, 257399869746174017364579322430269442490883625966888809884441531134919325944864923065061436569797, 29541667542207996913499858109548651071978582049177064726242843408127702854573283274764793474702481515218308196207748238482591984109614881895322605643055282747077487783] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_4 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨1, 0, false⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [1461551825088054650771400524885540911831374142754] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_5 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨1, 0, true⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [5898579793396687966191580854945041509352773922, 1038216434862209494922841823802981634066375205919161878140437038688800735570752661794456103790255812, 732181218755282688292123308646902973189976004898, 519551760406106011485462437869877345339993947085839300747753013797411872689880216824284786580712132, 359359457582246159756435621243936897538338, 91522617654227259619041687039684023984659142946, 359359457582246159756435621243936897538338, 91522617654227259619041687039684023984927578402, 732181218755282688292123308646901002856549095714, 265750963061135949740471963003120323840229201375790863699410472996098914783794537356602620745378640644, 732178425717625385822932270923380545509217311138, 5934545757214901945140365190531927180876066, 5898601571468170906253242510919917142518307106, 5901890102797390720681460496043477654930757922, 5901933701475652465922091740915054850299959586, 2798503463671533065861904807314851437254946, 732180870306138961251136722151302781618862725410, 2798503463671533065861904807314851437254946, 2798503463671533065861904807385212128368930, 265750963061135948818463094231924690571812710441972320117174414617837384189672631953177344759312888580, 732180870306138961251136722151303837154051922210, 2798503463671533065861904808440751344097570, 527154933241108587672889629050949409171781224997201203442549169656320491646010182536242366284829124, 2798503463671533065861904811818459654560034, 519551760406105089476593666674244076923503013267295718511694635535890902439711804989278063144921796, 5586096613487860958553869595899504842807586, 91522617654227259619041687039688457232453769506, 91522966103370986660028273535286467363102300450, 732180864861631475109838376392570557088463362466] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_6 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨1, 1, false⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [1461551825258195834231869756635674959620967800098] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_7 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨1, 1, true⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_8 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨2, 0, false⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_9 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨2, 0, true⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_10 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨2, 1, false⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_11 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨2, 1, true⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [97320910291060875955413333562098117151477228926011156827187198764719834261767336697692377504232196, 97320910298495955473184255148774627734367541661458308401949499747433387921975734195884165003686660, 97320910291178893090616046603156474462316757699589683042659616240635888916114460185508569944636356, 97320910291886995901832324849506618327353930341060840335494121096132183940071604200788271720310276, 97320910411792405267788774564797646140315164296843475255470276626846156914507671122984648610886404, 97320910292831132983454029177973476814070160529689050059273460903460621174848592103317811241366276, 97320910298495955473184255148774627734367541661458308401949499747430981366505744225555425448375044, 97320910291060875955413333562098117151477228926011156827187198764729458133504433345797340505780996, 97320910411792405267788774564797646140315164296843475255470276626841343803706090185583184624956164, 66470182058512370998911888029697889448419629298647569307059705031396237428285733993024588172998423300, 65007330019187234384353061631067531746324801910450157588554880161483988098212704923068175574125957, 66470182058512370998911888029697889448419629298647569307059705031396235172139978776227962833686704900, 30199070432992845049096479093568639046241667228278932948817398282954221757794785265132248093934112974449439403393398517740631371370886201252210219136692961325286471383847, 291962731839742936361923958136919594605915488832536155411181666023789986781575332973990859067568900, 291962731839624919226721245095861237295075960058957629195709248547873936827567726658346991785030404, 291962731840096987767532097260094666538434075153271734057598918451538136643705733332459484340516996, 291962731840569056308342949424328095781792190247585838919488588355202336459879600477086753283646980, 291962731843401467553208062409728671241940880813470468090826607777187535356922803344835755465178884, 291962731847178015879694879723596105188805801567983306985943967006501133886313740501853907011711748, 291962731843401467553208062409728671241940880813470468090826607777187535356922803346998254318845700, 291962731839624919226721245095861237295075960058957629195709248547873936827531866189971753355391748, 97320910291119870116626115532695525987889322471885676462484995342341442530558383986835548430086916, 291962731840155967522356304680760305555838497858231510220458302868823329379342008693082717984094340, 32440303108107837648049385816673932798572930676437065209827226166847499048845135891395529888969476, 129887934301692149382239955805773275623212870425805307966391023188516547867640206077262903955891845, 32440303108107837648049385816673932798572930676437065209827226166852293358574971584754563869258500, 551485160572145204080170463423771658209745667380554639902860468115542086395020162706340615150642692] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_12 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨3, 0, false⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [5720173874343738846233422223166174790715218210, 1461680402651959130028771315510654446311020992930, 5731346067549782962983159671199200533604769570, 22880662766433389769182066200659193655976828194, 1462931683527082934211603421203108825469895612834, 22925351539257566236181015992791296627535026466, 91522618334791993460976642110631269117023263010, 1461501648241227158002652443268875249288324618658, 183045224398151048626665959125686001134776400290, 366805460973413231700138142424633218506140195106] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_13 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨3, 0, true⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_14 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨3, 1, false⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [5720173874343738846233422518314079970068044066, 45761663752261385215977105221473862958642665762, 732181219435847422133922864321196851786331232546, 22881099178568965872761458273736644053573868834, 359359467966840031568595788977601357322658, 91522618334791993460976642405774741048581462306, 359359467966840031568595788977601357322658, 91522618334791993460976642405774741048849897762, 732181219435847422133922864321194881452904323362, 732178425717625385822932270923380545509217311138, 5935226321948743899438544395083057898494242, 5720195694950517651412392107210781532204603682, 5724363430845269440595583586476293875733403938, 5724385251452048245774553175372995437937072418, 2798503474056126937674064975048515897039266, 732182266824972804782513404588236345328421345570, 2798503474056126937674064975048515897039266, 732180864861631475109838376392566194209681349026, 732180864861631475109838376392567179375857932706, 4200466815385799612702260646395903556491554, 22880662766433389769182066495807098835329654050, 8379134281174923944032500829035725503633698, 22880750048860504989897944851393905083875892514, 5586096613487861035925122051235772024002850, 91522618334791993460976642405779174296376088866, 91522967464500454343840155828126399290561042722, 732180864861631475109838376392570557088463362466] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_15 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨3, 1, true⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

private theorem solve_1_1_1 (N : Machine4) (h11 : N 2 1 = none)
    (hAlive : ∀ q a, ¬ (q = 2 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    (hm : Matches N (baseTable 1 1 1)) : CertProp N := by
  refine branch_one_sound (tb := baseTable 1 1 1) (q1 := 1) (a1 := 1) (rem1 := 103) (cur1 := ⟨1, [0, 1], 1, [1]⟩) (step1 := 4) rfl ?_ N h11 hAlive h107 hm
  intro m hmem N h11 hAlive h107 hm' hsum1 hrun1
  simp only [moves16, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkTree_sound tv_1_1_1_0 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_1_1 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_1_2 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_1_3 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_1_4 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_1_5 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_1_6 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_1_7 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_1_8 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_1_9 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_1_10 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_1_11 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_1_12 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_1_13 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_1_14 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_1_15 N h11 hAlive h107 hm' hsum1 hrun1

set_option maxHeartbeats 0 in
private theorem tv_1_1_2 : checkTree 4 (baseTable 1 1 2) 107 startPos 0 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_0 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨0, 0, false⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [36842770565600, 5887430101362156496786673746845898960257718562, 36842770565600, 36842267249120, 5709012570183820793154213784556879226002774434, 36842267249120, 35742722034144, 37941812464096, 7136265749932562680782896467084382268556351778, 37941812464096, 5887429420807807248336673171843841602129795490, 6065835382396052233488301804925838856884894114, 45638595414496, 5798215891260310206668491527579137875217783202, 45638595414496, 35742722034144, 5753625119747422376529764242145916211694705954, 7136265749942947274654709217552412299163113890, 5798226780285667083282067410378516650859206946, 5887430101362156496786673746843928635420743970, 5709012570183820793463699901187372316928022946, 6065835382396052233759102221533243270080018850, 5720162985318381970151775693245522426719148450, 45638863817184, 5709012570183820793463699901183009454789007778, 45638863817184, 35743258905056] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_1 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨0, 0, true⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_2 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨0, 1, false⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [36842770565600, 7136299097604520932907058973004627683610499362, 36842770565600, 36842267249120, 11418025119079143257449019318329735404699294114, 36842267249120, 35742722034144, 37941812464096, 11418025119079143257449019834838569468566739362, 37941812464096, 45638595414496, 11507228440155632670963297061351994053914302882, 45638595414496, 35742722034144, 5753646897818905316591425898120791844860239138, 47837383821792, 7136287528004045620844558196848468404187732258, 47837383821792, 47837383821792, 5887457366486806036676408281046585918710913314, 5709039835298085739631529648699072638790703394, 5887457366486806036676408299493329992420464930, 45638461164000, 45638461164000, 291962731843401467553208062409728671241940880813470468090826607777197086373810899875527684168023812, 45638595414496, 310495522189437959677510375218388802144565501628696178634205255527010653863108416346337350688913860, 45638595414496, 11418025119079143257449019244542759118451022242, 5753647067960088777060657629808095561012780322, 5709045237280660609530845474518141934024825122, 5753646897818905316286775429433028666312400162, 5898601571468170906253242510915712610053691682, 5753647238101272237225238911254380172058598690, 5731346067549782962983159671194732118483705634, 310495522189437959677510375218388802144565501628696178634205255527010653863108416347940438642211268, 5720195737485813516529700040128121453868521762, 11418025119079143257449019244542759127040956834, 5887451879433639436848335402818804268586277154, 5887452559998373278725262329568019133196441890, 45638863817184, 5753653405719172679539539635160159004807699746, 45638863817184, 35743258905056] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_3 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨0, 1, true⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [36842267249120, 265783407324249488745639782539123225550097121613310819778767056479747644479607671631412475320170918660, 36842267249120, 36842267249120, 39041290537440, 47837383821792, 39041290537440, 265783407324249488745639782539123225550097121613310819778767056479747642073052201641442146580615607044, 45638360500704, 21799349596675205209108146302640626637090, 45638360500704, 35742755588576, 5809518752895251963788198911461294271328459170, 62270380013180045476745592769853717030809278337638866651302498394520658940906919913090368033944574360527602223198480025590198928706502698271545321940756573541246945606439, 11529659938853652664709418581317442518836616098, 21288498328859408250784023047306254754, 21288498328859408250786274855709874594, 21288498328859408250785148951508064674, 21288498328859408250784023047306254754, 21288498328859408250786274855709874594, 21288498328859408250784023047306254754, 36842267249120, 265783407324241935692205974628145285991660414784326669200813117882604607722059710084612144808230859524, 36842267249120, 36842267249120, 39041290537440, 47837383821792, 39041290537440, 32444263105986909759731155620163844566632266935436289902305431349585484941355802555609392353585380, 265783407324249488788858948262773020859554144625835694878603352601063234919118456098455651723457540868, 45638360500704, 3818162011083778392425342536134015205497055833034043497273758346442848773346727688557027619490357770937774071585211221086272253877653262617477488515251632328157981225765558566, 45638360500704, 35742755588576, 36842267249120, 36842267249120, 558349945312, 558350010848, 558350207456, 558350010848, 558350207456, 558349945312, 558350207456, 558349945312, 265783407324242879886927219369515813847167125572560353124456131021372286265429141445444480239235507716, 265783407324241935634580420329945558912384384100960169067698056548913217696675172171459512767137133316, 265783407324245712643967616488226578651515349987360905294730354920729640162044958713371234911715262212, 327113571863008, 327113571863008, 290829688375776, 290829688179168, 290829688375776, 290829688179168, 7446115018805182963688482271374126582454607223642578140750118501038617850801052792669190908781212104740005471510248670150511593369962171316008220527788008319626569654027524509594916731469921092676215906173909905400414296553658009482919767994757493555200119730761, 290829688375776, 290829688375776, 290829688375776, 290829688375776, 573673044117055754401209620323813143668319682718333763038400212556053357935194071052309745862052319953633874578226828147686802549389730586153226312171153815655383275030729873478226373179939032006389711142294210349559978335361540709615017605752942526724106582760, 249081520045470955577251506458283470753112027685269050996939043121766617033935846763585434375552763458754610839225781553418801111010435021318667554061487127588609769593639, 558349945312, 558350010848, 558350207456, 558350010848, 275742580527299595781294591332195943567752626212108263731310296880016256223270642065129279507653189, 275742580527299595781294594686444718090167555537033143255298964181100682461357656006753713293007045, 558350207456, 558349945312, 558350207456, 558349945312, 327113571863008, 99949021467884562941377269610573563067281407575589354826154380019894619923460008522373359401909319787301415113626887574634481270635105256624717030688482928320096397894416777042952898724728728703033245433849045288510835951710769163814056595798842237124050555833623506949528278767834335721748168135175839460381161080511047135305674883400469053610875859335975777453135943466, 327113571863008, 290829688375776, 290829688179168, 290829688375776, 290829688179168, 290829688375776, 290829688375776, 290829688375776, 290829688375776, 36842267249120, 36842267249120, 558349945312, 558350010848, 558350207456, 558350010848, 275742580527299595781294591332195943567752626939445025410119014001418455532185274181111698930262597, 275742580527299595781294594686444718090167556264369904934107681302502881770272288122736132715616453, 558350207456, 558349945312, 558350207456, 558349945312] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_4 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨1, 0, false⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [22847211521029706239041676207312802527872850210, 23014467067493774641511231969869921156254964130, 22858361936164267415729752003982638656024256290, 72026639337952, 72026639337952, 70927094122976, 70927094188512, 1947364611236912243079580690389897630843752621557509771549138938483975403546503998575058256765709578688230197542053827403906821035025105085003981152082538868715842243077926, 70927094188512, 73126184749536, 332196815882316781517054501609309928963085384223399877630966261492564623778134704092044159225600717125, 73126184749536, 70927094122976, 73126185011680, 24263303524224417669019236867172914607590250786, 73126185011680, 23014467748048123889380947044654563887764511010, 22836050216869788186348115321914320152786147746, 23192873029082019626372718406244407408006838690, 22880651877408032893100418508593664665391766946, 81922479360480, 22836050216869788186057973125206809150856665506, 81922479360480, 70927094647264] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_5 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨1, 0, true⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [45775252290554934916679733180278901733871098146, 265791514430141358644759077213584989381887065798658143568818874538143536259411256810027831825222808324, 22894687759397811438581394170075194776133606690, 364496732326368, 527154956564126909571455927133096676880636454729915367677332670897347062378626023458375868181392005, 364496732326368, 290829419678176, 290829419743712, 290829688375776, 290829419743712, 290829688375776, 290829688375776, 290829688375776, 290829688375776, 4184799162820833659211259070251659012923257179391391509784503435001346132817003178714626110588662532, 290829688637920, 4184799162820833659211259070251659012923257179408438465136350513678014928551324308538188758549476100, 290829554420192, 527154956564126909571455927133096701090765029579903256765285879597368666388635758943301977252793989, 290829554420192, 290829688637920, 290829688637920, 290829688637920, 290829688637920] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_6 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨1, 1, false⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [22847298633315637999288322831212305060534982946, 22925352219822300077990242889170165495638300962, 24263402206110824741173641319593794307879901474, 22880750899566422292171567481033713971878731042, 45672100412451078043217852520966872476878412194, 23014554860334055649627593668549633172632017186, 22836148898745810664475965109256793653179881762, 23014554860334055649627593668549633172900452642, 24263402206110824741173641319591823974452992290, 47099353889957275580384759872695929439784049058, 2108619732968210646903607390321611487252265357953152053966008059348150809645979460727797480316678916, 45672100412451078043217852520967998381080222114, 47099353889957275580384759872695647972323531170, 22836148898745810664475966289847288470684342562, 45672100412451078043217852520966872476878412194, 22847298675850933864405630768745817007933397282, 72026639337952, 72026639337952, 70927094122976, 70927094188512, 2108619732964434098577120573007744053305400437198639214732198773374047002742352100303726448642293508, 70927094188512, 73126184749536, 2108619732960657543047439468418910734449031681023685651179257357631022001269864644761467573269379524, 73126184749536, 70927094122976, 73126185011680, 22836142943804389548052855016712249469507246370, 73126185011680, 23014554860334055649627593668554066420426643746, 23014555540898789491504520669090257578801273122, 81922479360480, 23014560474993109845112242585122520120719087906, 81922479360480, 70927094647264] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_7 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨1, 1, true⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_8 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨2, 0, false⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_9 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨2, 0, true⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_10 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨2, 1, false⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_11 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨2, 1, true⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_12 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨3, 0, false⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [290829957073376] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_13 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨3, 0, true⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [558887340512] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_14 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨3, 1, false⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [290829957073376] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_15 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨3, 1, true⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [558887340512] = some [] := by
  decide +kernel

private theorem solve_1_1_3 (N : Machine4) (h11 : N 2 1 = none)
    (hAlive : ∀ q a, ¬ (q = 2 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    (hm : Matches N (baseTable 1 1 3)) : CertProp N := by
  refine branch_one_sound (tb := baseTable 1 1 3) (q1 := 3) (a1 := 1) (rem1 := 103) (cur1 := ⟨3, [0, 1], 1, [1]⟩) (step1 := 4) rfl ?_ N h11 hAlive h107 hm
  intro m hmem N h11 hAlive h107 hm' hsum1 hrun1
  simp only [moves16, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkTree_sound tv_1_1_3_0 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_3_1 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_3_2 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_3_3 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_3_4 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_3_5 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_3_6 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_3_7 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_3_8 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_3_9 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_3_10 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_3_11 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_3_12 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_3_13 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_3_14 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_3_15 N h11 hAlive h107 hm' hsum1 hrun1

end OMA.BB4HoleS2A0

open Turing Turing.BusyBeaver OMA.BB4HoleS2A0 in
theorem OMA.solution :
    OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H3_R1_H1_R1_H1_R1_H3_R1.H1 := by
  intro b c q u v N h107
  have h11 : N 2 1 = none := rfl
  have hAlive : ∀ r s, ¬ (r = 2 ∧ s = 1) →
      ∃ r' w d, N r s = some (some r', Stmt.write w d) := by
    intro r s hne
    fin_cases s
    · cases hs : (v r).2 with
      | write w d => exact ⟨(v r).1, w, d, by simp [N, hs]⟩
    · have hr : r ≠ 2 := fun h => hne ⟨h, rfl⟩
      cases hs : (u r).2 with
      | write w d => exact ⟨(u r).1, w, d, by simp [N, hr, hs]⟩
  have hm : Matches N (baseTable b c q) := by
    intro r s m hget
    fin_cases r <;> fin_cases s <;> simp [baseTable, Table.get] at hget <;> subst hget <;> rfl
  fin_cases b <;> fin_cases c <;> fin_cases q
  · exact checkTree_sound tv_0_0_0 N h11 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact checkTree_sound tv_0_0_1 N h11 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact checkTree_sound tv_0_0_2 N h11 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact checkTree_sound tv_0_0_3 N h11 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact solve_0_1_0 N h11 hAlive h107 hm
  · exact checkTree_sound tv_0_1_1 N h11 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact checkTree_sound tv_0_1_2 N h11 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact solve_0_1_3 N h11 hAlive h107 hm
  · exact checkTree_sound tv_1_0_0 N h11 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact solve_1_0_1 N h11 hAlive h107 hm
  · exact checkTree_sound tv_1_0_2 N h11 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact checkTree_sound tv_1_0_3 N h11 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact solve_1_1_0 N h11 hAlive h107 hm
  · exact solve_1_1_1 N h11 hAlive h107 hm
  · exact checkTree_sound tv_1_1_2 N h11 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact solve_1_1_3 N h11 hAlive h107 hm
