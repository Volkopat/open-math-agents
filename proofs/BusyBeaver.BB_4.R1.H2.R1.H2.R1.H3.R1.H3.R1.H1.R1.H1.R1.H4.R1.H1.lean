import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H3_R1_H1_R1_H1_R1_H4_R1

/-!
FAR nonhalting certificates for write-0 transition at state 1 blank, hole at (3, 1).
Every machine in this branch either halts at the missing (1, 1) entry within
107 steps or hits a leaf certified by a finite automaton invariant.
-/

namespace OMA.BB4HoleS3A0

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
      if Nat.beq cur.state.val 3 && Nat.beq cur.head.val 1 then .halted11
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
    (h11 : N 3 1 = none)
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    {rem : ℕ} {cur : Position} {step : ℕ}
    (hsum : step + rem = 107)
    (hrun : N.multiStep (Machine.init []) step = some cur.view) :
    match stepLoop tb rem cur step with
    | .halted11 => False
    | .done => True
    | .missing q a rem' cur' step' =>
      tb.get q a = none ∧ cur'.state = q ∧ cur'.head = a ∧ ¬ (q = 3 ∧ a = 1) ∧
      step' + rem' = 107 ∧ N.multiStep (Machine.init []) step' = some cur'.view := by
  induction rem generalizing cur step with
  | zero => simp [stepLoop]
  | succ rem ih =>
    unfold stepLoop
    cases ht : tb.get cur.state cur.head with
    | none =>
      simp only []
      by_cases h0 : (Nat.beq cur.state.val 3 && Nat.beq cur.head.val 1) = true
      · rw [if_pos h0]
        simp only [Bool.and_eq_true] at h0
        have hs : cur.state = 3 := Fin.ext (Nat.beq_eq.mp h0.1)
        have ha : cur.head = 1 := Fin.ext (Nat.beq_eq.mp h0.2)
        have hnone : N.multiStep (Machine.init []) (step + 1) = none := by
          rw [Machine.multiStep_succ, hrun]
          simp [Machine.step, Position.view, hs, ha, h11]
        have hnone107 := Machine.multiStep_eq_none_mono hnone (by omega : step + 1 ≤ 107)
        obtain ⟨r0, T0, hr0⟩ := h107
        rw [hnone107] at hr0
        contradiction
      · rw [if_neg h0]
        have hne : ¬ (cur.state = 3 ∧ cur.head = 1) := by
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
    (h11 : N 3 1 = none)
    (hAlive : ∀ q a, ¬ (q = 3 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
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
      N 3 1 = none →
      (∀ q a, ¬ (q = 3 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d)) →
      (∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩) →
      Matches N (tb.set q1 a1 m) →
      step1 + rem1 = 107 →
      N.multiStep (Machine.init []) step1 = some cur1.view →
      CertProp N)
    (N : Machine4)
    (h11 : N 3 1 = none)
    (hAlive : ∀ q a, ¬ (q = 3 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
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

set_option maxHeartbeats 0 in
private theorem tv_0_0_3 : checkTree 4 (baseTable 0 0 3) 107 startPos 0 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_0 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨0, 0, false⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [1464361707966427880182233562712715619175492508066] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_1 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨0, 0, true⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [571205086120416, 1464361710646151519684700124882598286899257825698, 571205086120416, 1461507212538480664554998473984245975004184861090, 567906484160992, 1464361707923892584317115045923146091181152164258, 567906484160992, 265751101661063955635535821985909478645430327675445094729881412099645699266863758879738895329883747076, 265750998701117921836539516307879135904457643051284028988632218947091818805818376558815853371801484421, 265750998701117921836540402473558169632674866546570818508292618875269332083041213089387667689073294469, 1461507212517212935492801405411103366250694203810, 567425447823840, 1464361707907941787520467244493289134616034171298, 567425447823840, 567356728281568, 265750998701117921836540394745264275223936489532007697985677630807903879311342398631857394406867876997, 1461507212517212935492801405411103366250694203810, 1978643213742763555983185601367469669841904409625931272476502850533042686413701493198154244954862802292630748280050408505475396685531133526011704939983096239934218991297363751, 1464361707907941787520467244493289134616034171298, 1461507212538480583425360059377564279215179717026, 1461507212538480583425360059377564279215179717026, 1464361710646151519684700124882597442474327693730, 1465264891486072091768280729938473838737508817186, 1464361707902624860325520378262921088410179361186, 1465276041858671357396764147854667442923693431074, 1461507212517212935492801405411103366250694203810, 1465298342774260302363414723143338134375253433634, 1461507212522529867758350672554389018439066868130, 1465342944434798548337822462243078594827819964706, 1461507212517212935492801405411103366250694203810, 1464361707903954088321305294135824895470459705762, 1461507212517212935492801405411103366250694203810, 1464361707905283321387692610921646308517552871842, 1461507212522529867758350672554389018439066868130, 265750982861125933825305742747877314215053889492433482579917201005125180817793871749437396504393688581, 1461507212527846800023899939697674670627439532450, 265750982861125933825305522923829627114093486625703761521443856477039251634323391908842346127315428869, 1464361710646151519684700124882597723950378146210, 1464361707923892584317115045923146091181152164258, 265750982861125933825306182454672041096648101615824721530923611762891119907605969546911758792390618629, 265750982861125933825306182414421056402165524669991231012260177378316387634455875080735287219083406853] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_2 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨0, 1, false⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [1464361708008963176047352079576068745752065629090] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_3 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨0, 1, true⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [564607848581600, 265785442763212454079992180575510284875149606133753337401739058493965786592943609053631763648515748260, 265783407324279760119771634484596936557095423600295233356482273579500736939991194317480276703635098020, 1978643213742764946560577328376242546642246914855898313018050403091264187770752922394948260327785881236252531281959343908529848451744943455153471279018298188510710799373335334, 1978643212360697238219068824983734034857829883918859015369840215625211592283253739346547688594905860554994861212200032527173887286195062965846409156116707269177661754717125415, 1978643213742763555902738753783131464418986226926579488051334378702628786106684746131799216362412491750482589219324826415921708565024444638119823260263618236278149093532875559, 1978650759824859481673266488670356688855534539089558205731018326004145438779487933943591398568755449131725103576744980103104888731475334630251786421942485869917801215217400614, 1978643219271029707449952669899732361178503615353448464308843952463386457511548422990595064105019883154246568524903777409946579276183459546523804248452176139095212343285020966, 265783407324241994635943948062762491641593488330800143288066245084967962077383675936642166785774006692, 265783407324249547732709485347119389942458306170645932158003823322969569629958669970572842982938298788, 1978643212360697238219068824983734034857829971951121844981362403485396686422284420518557502625031111889061035708639443849342312147916793202459374126586039217209274918471613223, 1978650759824859481673266488670356688855500468524356849158023725444531286390175899756223463261430600336839169539448167961629334968738273870244318011814724229817293511699495718, 1978650759824859536591647772911904924420353619529933514602335308877237801667693411393212082402625558594347070271722854321367053386125147012318828821144008420433752685506231078, 564607848581600, 563508303366624, 563508303432160, 563508303432160, 564092452506080, 1461685619164682831373572025301680717777058421154, 564092452506080, 562958547552736, 563027267095008, 563027267095008, 562958547552736, 567494167366112, 562958547552736, 567494167366112, 1461507212538480583425360059303777302920341510562, 1461507212538480583425360059303777302920341510562, 564092452604384, 576565406730720, 564092452604384, 562958547683808, 565226357524960, 572029787048416, 565226357524960, 562958547683808, 567494167366112, 562958547683808, 567494167366112, 572029787048416, 1461507212538480583425360059303777584396391963042, 572029787048416, 1461507212538480583425360059303777584396391963042, 562992907356640, 562992907356640, 562958547552736, 565226357590496, 563233425459680, 565226357590496, 562958547552736, 562958547552736, 563233425459680, 265750982861125933825305742746200189852783782119688994346221208075367788324370646205749573043721719301, 563233425459680, 265750982861125933825305522922152502751823379252959273287747863547281859141047050852237700143989149189, 564092452604384, 576565406730720, 564092452604384, 562958547683808, 565226357524960, 572029787048416, 565226357524960, 562958547683808, 567494167366112, 562958547683808, 567494167366112, 572029787048416, 572029787048416, 265750982861125933825306182441255046198487242633878804111756479711739347580991150681200601580166147589, 265750982861125933825306182414421056402165524669989810432647523455356191929941340635277680041753439749] = some [] := by
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
private theorem tv_0_1_0_7 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨1, 1, true⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [564092452506080, 1464551264959995472325285024783864470829402184098, 564092452506080, 564092452506080, 566291542903264, 1978650760055203868181810878292547842481394981037521426647705283998891453525762426510137731899959748789121860377364879837191019398342177962872401531746156107070068503930837798, 566291542903264, 564092452506080, 568490633333216, 566291542936032, 568490633333216, 1978650760055203428606827866341199860406620069960717285070031410198248248778091989749604386057347328227708403835582957119927272770017613697734374114009609705647383779509639974, 265750967021617343999857886501433901745988615839405783349710575387852956197371007260422312672192442500, 265783407324241994635945707097865515085613992648386117865297865573642573846366081696350226603802261092, 1464361708604457242099975301969248428021896993186, 564092452506080, 1978650996158199819779692912003010401002508328689057879393489943609399658212466778966624730164785621631278515354921693300047858071914656395987600334344500122519814894689852198, 564092452506080, 564092452506080, 566291542903264, 1464384008903118238452330053660692073643800289058, 566291542903264, 564092452506080, 568490633333216, 566291542936032, 568490633333216, 1464361707987778524368714450507453592692778360610, 1464361707923892503187476631242680796809914243490, 1464361708073098346981988873926087743413494504866, 1464361707903289471788111635706024078516394416546, 1464361707902624855254917977276219883845428730274, 1464361708584518822163201563875691322117691824546, 1464361707902624855254917977276219883845428730274, 1464361709266412789071485150475162760389954927010, 1461518362911079851272232027656265935834173168034, 1978643212360697238219068824983734034857831302832649680980974577456583973649236155874440906705654394370830466596687837979432903498666115963423953887704630555432534754930080551, 1461529513283679116583802795515402277607179311522, 1461507212538480583425360059303777302920341510562, 1461507212538480583425360059303777373289354123682, 1461507212538480583425360059303777443658366736802, 1461507212538480583425360059303777302920341510562, 1461507212538480583425360059303777584396391963042, 265750982861125933825305742739910973494270879471912433486823101617492558281884887213295501485428225029, 265750982861125933825305742739910973494270879471912433486823101617492562493871059322773890406513202181, 265750982861125933825305742739910973494270879471912433486823101617492560087021818117358068937881539589, 1461518362953615144918961994083324121644096575906, 1978643212360697238219068824983734034857832722439532575046206079298566622209958482088856629690784479385721092232928475392675845198623143142017909435750027889249371462325386023, 1461529513368749706412563928862870940367851641762, 1461507212538480583425360059303777302920341510562, 1461507212538480583425360059303777373289354123682, 1461507212538480583425360059303777443658366736802, 1461507212538480583425360059303777302920341510562, 1461507212538480583425360059303777584396391963042, 265750982861125933825305522915863286393310476605182712428349757089406629098855060833949983540387034117, 265750982861125933825305522915863286393310476605182712428349757089406633310841232943428372461472011269, 265750982861125933825305522915863286393310476605182712428349757089406630903991991738012550992840348677] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_8 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨2, 0, false⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [1464361708604457318159011315663012517824089315746] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_9 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨2, 0, true⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [1464361708242990299242515319482158734773457017250, 265750998701117921836539516307040573723322589464009286307112863670835762805302116086125265035871665285, 1464361708243073376309164526781272573088900340130, 579967121394144, 1978658307749708630490539362458856293955277103824779552281515434438597032477456744124331704998222164179364349975233793564504014129152409524874084239092848850614947552143867046, 579967121394144, 562958547552736, 562958547618272, 562958547618272, 562958547552736, 562958547683808, 562958547552736, 562958547683808, 265750982861125933825305303520792571476899477923267356607772416818999662174406939842798430467734597125, 265750982861125933825305303520792571476899477923267356607772416818999659767557698637382608999102934533, 1464361708583521897363411076286325262332371949986, 1464361707902624875537327580927890307792680016290, 1464361708583854205630007905482780615594145241506, 1464361707902624855254917977276219883845428730274, 1464361710626213023688890373316641397793201609122, 1464361707902624855254917977276219883845428730274, 1464361710627542256755277690102462810840294775202, 1464361707907941787520467244419505536033801394594, 265750998701117921836539955163585646274703565569167725651979510066774980086864240971244107546056735877, 1978643212360697238219068824983734034857831302930041734756573286684478007847774101721504047572366613183946542987806107744505956373091292125754541836728883320015840918117169959, 265750998701117921836539955150011420967579887035111840084753709806466538654838931339101740750835039365, 265750982861125933825305742806576666894507647538619621711877885598664229436781601392609586050582982149, 265750982861125933825305742806576666894507647538619621711877885598664245075425572465038831855852334597, 265750982861125933825305742806576666894507647538619621711877885598664245075425572465038831855852334597, 265750982861125933825305742806576666894507647538619621711877885598664229469687743362214891443333501957, 265750982861125933825305742806576666894507647538619621711877885598664239063003346875726603666172947973, 265750982861125933825305742806576666894507647538619621711877885598664230033793034269734312268916493829, 265750982861125933825305742806576666894507647538619621711877885598664234245779206379212701189985545733, 265750982861125933825305742806576666894507647538619621711877885598664231838929965173796879721369808389, 564332970674656, 1978650759824859536591647772911904924420353619529933514602335308877237801667693411393212082402625558594347070271722854321367053386125147012318828821144008420433752685506231078, 564332970674656, 563233425459680, 563233425525216, 563233425525216, 572029787048416, 563233425459680, 572029787048416, 265750982861125933825305742793166223263460122276786779201424225959929000105834799593871066690164583941, 265750982861125933825305522942287821999624844134261566261745617412754467963725083974254852796797545989, 1978643219501374545211680698385886315005604195018744582636735661504108012143727988896785246363823293423676195549699053660393038180413382585502347899121467726912200672572635430, 1978643212360697238219068824983734034857832722461109441868775732515867211889043778519612163160943517771284050700003265979506805035251702257705277437512314770537086021899270951, 1978643219501374545104418234947125975346318429262499783890770572155005532349817622185149916447962100734138660960204022963615935201434348399750285800962338369723717789095066406, 265750982861125933825305522942277995099064667726056410134741106686003570387450921752503418000858279429, 265750982861125933825305522942277995099064667726056410134741106686003582415821031016807729287227108869, 265750982861125933825305522942277995099064667726056410134741106686003582415821031016807729287227108869, 265750982861125933825305522942277995099064667726056410134741106686003570420357063722108723393608799237, 265750982861125933825305522942277995099064667726056410134741106686003580013672667235620435616448245253, 265750982861125933825305522942277995099064667726056410134741106686003570984462354629628144219191791109, 265750982861125933825305522942277995099064667726056410134741106686003575196448526739106533140276768261, 265750982861125933825305522942277995099064667726056410134741106686003572789599285533690711671637143045] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_10 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨2, 1, false⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [1464361709285022052000907585476662543049259252130] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_11 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨2, 1, true⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [1461518362932430573736139898534899631319862499746, 1464372858955871931475034223354921619748518123938, 1461529513347565134912829183252777413651014376354, 1461507212517296012559450613817021848988710623650, 1464361708072849115782041253190886671863071661474, 1464361710624966867689152264715378664486632184226, 1461596415838372501972964891560044107637925632418, 1464372858317842493498256470473803125192255363490, 1461518363570460011712917651416021503575845788066, 1461507212517296012559450613817021989726198978978, 1461518364251024745554813921155884833982227970466, 1464361710624966867689152264715374160887004813730, 265750982861125933825306182816970217346758475665343849236368118589863546228493692366434910068169469445, 265750982861125933825306182816970217346758475665343849236368118589863543821644451161019088599537806853, 1978643213742763555983185601362787047016407663205669750366770880660035202439962339008425093865467340518626591817261701292285323606638431423287340470655399583366719442944785191, 1461518362932513650802789105834013469635305822626, 1464384011370248475378943007732760647560732891554, 1461529513347648211979478390551891251966457699234, 1461507212517379089626099821116135687304153946530, 1464361708072932192848690460490000510178514984354, 1461596415838455579039614098859157945953368955298, 1461529513943142354091137626574271666072042101154, 1461596415838455579039614098859157945953368955298, 1461529514623707087933033896314134996478424283554, 1464361707902791009388216393055034677594099308962, 1464361710625049944755801472014487999202448136610, 1461518362932430573736139898534899631319862499746, 1978658307749708630490539362458856296932408518539585375971545751547863609669461241855194901026090581161034853863443296160089564091894978034209774250399524402989514837539683494, 1461529513347648211979478390551891251966457699234, 1461507212517212935492801406517908010673267300770, 1461507212517212935492801406517908151411292527010, 265750982861125933825305303520792571476899477923176439512562565749547132309385272316513761371948733445, 1461507212517212935492801406517908292149317753250, 1461507212517212935492801406517908010673267300770, 1461507212517212935492801406517908573625368205730, 265750982861125933825305303520792571476899477923176439512562565749547137085476735333511571118616702469, 265750982861125933825305303520792571476899477923176439512562565749547134678627494128095749649985039877, 1464361707903289471788111636849722211086386616738, 265750982861125933825305306526566344403230507920474919524452909458835999422518541084238751037116133701, 1464361708584518822163201564982495966540264921506, 1464361707902624855254917978456811504562840033698, 1464361709266412789071485151508180428517689817506, 1978643213742763555902738753783131464418974867428806939595507482717048034570821524014221482403833894429422915290810053457441294518781549015377785235174665233323285807726836519, 1978643212360697238219068824983734034857831302875888029790123960962625547476736494996588560276925871194970315930434797649523032479352168401815127251271458101147409316397595431, 265750982861125933825305742793159671996346788556584207777113556401020127725751112463069176666570583557, 265750982861125933825305742793159671996346788556584207777113556401020142160970462932790110965539761669, 265750982861125933825305742793159671996346788556584207777113556401020127758657254432674482059321103365, 265750982861125933825305742793159671996346788556584207777113556401020137351972857946186194282160549381, 265750982861125933825305742793159671996346788556584207777113556401020128322762545340193902884904095237, 265750982861125933825305742793159671996346788556584207777113556401020132534748717449672291805973147141, 265750982861125933825305742793159671996346788556584207777113556401020130127899476244256470337357409797, 265750998701117685802269549750917248824747092062377241203337227689624540485230015847408050823797685093, 1978643212360697238219068824983734034857832722461109441868775732515867211889043778520630681148755047516274336445520155297553947597081590709939591385813436611165505565617699623, 265750998701117685802269549750760018415784269531094476812676325646479038803334286537045763494518995813, 265750982861125933825305522942277995099064667725965493039531255616551045298520717243216558651740384773, 265750982861125933825305522942277995099064667725965493039531255616551057326890826507520869938109214213, 265750982861125933825305522942277995099064667725965493039531255616551045331426859212821864044490904581, 265750982861125933825305522942277995099064667725965493039531255616551054924742462726333576267330350597, 265750982861125933825305522942277995099064667725965493039531255616551045895532150120341284870073896453, 265750982861125933825305522942277995099064667725965493039531255616551050107518322229819673791158873605, 265750982861125933825305522942277995099064667725965493039531255616551047700669081024403852322519248389] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_12 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨3, 0, false⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [1464361710646151519684700125103962593499599100322] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_13 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨3, 0, true⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_14 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨3, 1, false⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [573404176484832, 573404176484832, 572304664889824, 572304664889824, 572888780507616, 576565272512992, 572888780507616, 572029787048416, 574022651873760, 572029787048416, 574022651873760, 1461507217982998454160530217812977786197751421346, 576290394606048, 572029787048416, 576290394606048, 572029787048416, 1461507217982998454160530217812977786197751421346, 572029787048416, 265767187173171368414397670841152599528444642605183380887845557170901382594730550724370595898703049476, 265767187173171368414397671485168364236748356702310260849026679242513340586028505865608752806701396740, 265751030381584351911314712441509517763414921667345119316077098208086772925472653949871048864292300292, 265751093741551359819169944887370327715142955789233075590807214567494973273712808889694996544762770180, 1978643212821386010860738982164749634917476594033513286639112776659119278863200494810987185891934862079790870196788694505454456823078733552084735230888955740927212340252570919, 265750967021617344003459483430399452922737396660368973332981205078247100564145625082736822400600077060, 572888780507616, 576565272512992, 572888780507616, 572029787048416, 574022651873760, 572029787048416, 574022651873760, 576290394606048, 572029787048416, 576290394606048, 572029787048416, 572029787048416, 480481077047106023417608531367588846730560739680051125337096974624586126640458648820689289517348494257461110744854502664296293496198075631307111681197209066382159870909872535521187274188508506089551913034234091081240510491110200421638447886476503446594781184124298761, 265750967021617344003459484289087139200378092414843615017054893895303940529781000619206530485678863108, 1978643212821386010860738982164749634917476594033513286639112776659118705488546497293109283187066749856206509900576193628695104574544886281867791692610890170395453325730182439, 265751473901353407266301315519279971648840947119499276812422569496732557798616403741746076996972671748, 265752994540561597054826811785921527827438361612569592374761736956198748534581959724895529562872992516] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_15 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨3, 1, true⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [] = some [] := by
  decide +kernel

private theorem solve_0_1_0 (N : Machine4) (h11 : N 3 1 = none)
    (hAlive : ∀ q a, ¬ (q = 3 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
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

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_0 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨0, 0, false⟩) 102 ⟨2, [0, 0, 1], 1, []⟩ 5 [1464361707945243228186993978698668513875979164066] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_1 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨0, 0, true⟩) 102 ⟨2, [0, 0, 1], 1, []⟩ 5 [1464361708604457242100265445272760583446399572386] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_2 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨0, 1, false⟩) 102 ⟨2, [0, 0, 1], 1, []⟩ 5 [1464361707987861601118760493930704178120393513890] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_3 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨0, 1, true⟩) 102 ⟨2, [0, 0, 1], 1, []⟩ 5 [1464361707966427799369507798163091273760663165346, 570895848475104, 1465075334497821350761140120403926990866816719266, 570895848475104, 1461507212517212935492801405411103366250694203810, 567494167300576, 1461507212538480583425360059377565405119381526946, 567494167300576, 1461507212517212935492801405411103366250694203810, 1465075334476553702828581466437465233477401074082, 1461507212517212935492801405411103366250694203810, 1465075334471236790845441802945850286712330148258, 1461507212538480583425360059377565405119381526946, 1461507212538480583425360059377566531023583336866, 1464361708008963095551538965083501750711412087714, 564092452506080, 1978643219271028827039652706902412209779451533432305415049193868118648447718643467752338376867376845879239387555600570970175735944824549821535249362519792586599602424237407015, 564092452506080, 562958547552736, 562958547618272, 562958547618272, 562958547552736, 562958547683808, 562958547552736, 562958547683808, 265751093741069849903969409613992753790897725532511886535946487505458936149916837116791260803580646405, 265751093741069849903969409587158763994576007568622892856836208231233191890414850444560999505045214213, 1461551814199018829399767798421969011063156399522, 1464361707923892503187476631537828701989267069346, 1461596415859557075374175537540156215589164046754, 1461507212538480583425360059303781806537148750242, 1461685619180633567322991015776530624641179343266, 1465342944434549343441624795118390385334310427042, 1978658307749707751796438865740812776271974821406447741793797016095504629986133968374804230098247492491730345309050756470576156019602580773259620275362440841139326289416551590, 1465342944434632420191361352360446890867831101858, 562958547552736, 562958547618272, 562958547618272, 562958547552736, 562958547683808, 562958547552736, 562958547683808, 265751093741069849903969409560377184334575230460312532265438326820548957923473221167636271001438082053, 265751093741069849903969409560377184334575230460312532265438326820548955516623979962220449532806419461, 1464361709285021981012473972695816059233879751074, 1464372858317842493498256470473798621592627992994, 1978643219271028827039652706902412209779451533432300126601443238301683423064310358613085625997218232059438663867601017095747834861172590190027869439881274208730563000161418023, 1464384008733060131741594962490790242239223192482, 1464361707902624855254917978456807000946032794018, 1464361707902624855254917978456807141684058020258, 265751093741069849903969409560377184334575230460221615170228475751096428058451553641351601905652093957, 1464361707902624855254917978456807282422083246498, 1464361707902624855254917978456807000946032794018, 1464361707902624855254917978456807563898133698978, 265751093741069849903969409560377184334575230460221615170228475751096432834543016658349411652320187397, 265751093741069849903969409560377184334575230460221615170228475751096430427693775452933590183688524805, 1464361710646151458837471314148951321657845242274] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_4 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨1, 0, false⟩) 102 ⟨2, [0, 0, 1], 1, []⟩ 5 [1464361708073098346982293524394775506609222213026] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_5 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨1, 0, true⟩) 102 ⟨2, [0, 0, 1], 1, []⟩ 5 [1464361710646151458837703428791761045997447305634] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_6 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨1, 1, false⟩) 102 ⟨2, [0, 0, 1], 1, []⟩ 5 [1464361708243571838709359585322918163586879609250] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_7 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨1, 1, true⟩) 102 ⟨2, [0, 0, 1], 1, []⟩ 5 [1464361707923892503187786117433093762596050327970] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_8 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨2, 0, false⟩) 102 ⟨2, [0, 0, 1], 1, []⟩ 5 [1464361708584518822163491707179203477542194403746] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_9 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨2, 0, true⟩) 102 ⟨2, [0, 0, 1], 1, []⟩ 5 [1464361707902624855255227463466632849631564814754] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_10 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨2, 1, false⟩) 102 ⟨2, [0, 0, 1], 1, []⟩ 5 [1464361709266412789071755950891774105452824000930] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_11 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨2, 1, true⟩) 102 ⟨2, [0, 0, 1], 1, []⟩ 5 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_12 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨3, 0, false⟩) 102 ⟨2, [0, 0, 1], 1, []⟩ 5 [1464361710630200722888284438316915361274083170722] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_13 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨3, 0, true⟩) 102 ⟨2, [0, 0, 1], 1, []⟩ 5 [1461518366654185912755568339211512460017870592418, 1461685621222327784060410865339058199762369010082, 1461529517026785178067139107070648801790876735906, 1461518366654185912755568339211512460017870592418, 1461551817431701339234040978869088074911714400674, 1462220836384833563365890411218933491877918300578, 1461596418922098400480324050305633442003738974626, 1461507212538480583425361268234208603567943604642, 1461685621222327784060410865339057355337438878114, 1461507212538480583425361268234213107167570975138, 1461864027183916029045543151085238823705537173922, 1462220836384833563365890411218934477040336787874, 1461507212538480583425361268234213107167570975138, 1462934465675704454606254176920994917315523959202, 1461507212538480583425361268234213107167570975138, 265751093741069849903969628955451174890729657689484768061452866597671800023918629345388275563213399909, 1461518366654185912755569548141943760665472686498, 1462220836384833563365891620149365777684717656482, 1461529517026785178067140316001080102438478829986, 1461507212538480583425362477164639904215679916450, 1461551817431701339234042187799519375559316494754, 1461596418922098400480325259236064742655099165090, 1461596418922098400480325259236064742651341068706, 1461507212538480583425362477164639904215545698722, 1461685621222327784060412074269488655985040972194, 265783407324241994635944827399191121606148642934800957638459412873936783063416993069695920848597580228, 1461864027183916029045544360015670124353139268002, 265783407324241994635944827399191121606148642934800957638459412873936783063416993069698058299201976772, 1462220836384833563365891620149365777687938881954, 1462934465675704454606255385851426217963126053282, 1461518366654185912755568339211512460017870592418, 1978643219271028827039652706902412209779452952346096080660328229950020829084625884280112238312006126606413559826190784231663031840217867862750963730950224956834298137404914471, 1461529517026785178067140316001080102438478829986, 1461507212538480583425360059303777302920341510562, 1461507212538480583425360059303777373289354123682, 1461507212538480583425360059303777443658366736802, 1461507212538480583425360059303777302920341510562, 1461507212538480583425360059303777584396391963042, 265751093741069849903969848779495586351946632008947666301074614889562162756054944790471840670254937093, 265751093741069849903969848779495586351946632008947666301074614889562166967527021202819731386801148933, 265751093741069849903969848779495586351946632008947666301074614889562164560971548967192766035048780805, 1461551817431701339234044605660386410102315309474, 1461596418922098400480332512818656909415735646626, 1461507212538480583425360059303781806537148750242, 1461507212538480583425379402190682616898782255522, 265783407324241994635944827399191121606148642937707463482596690906925202020431751154574505858285599172, 265783407324241994635944827399191121606148642937707463525949339572868733407577187476602920625911527876, 265783407324241994635944827399191121606148642937707463525949339572868733407577187476602920625911527876] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_14 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨3, 1, false⟩) 102 ⟨2, [0, 0, 1], 1, []⟩ 5 [573129063696864, 576427598940640, 573129063696864, 573129063696864, 574228575357408, 574228575619552, 574228575357408, 572029552298464, 576427598678496, 572029552298464, 576427598678496, 572029552298464, 1461507217972364670758916563968317217488122206626, 572029552298464, 265783407324362844184192764436707262067272322618928033760363760662637854743290679683421168160701674244, 573129063696864, 576427598940640, 573129063696864, 573129063696864, 574228575357408, 574228575619552, 574228575357408, 572029552298464, 576427598678496, 572029552298464, 576427598678496, 572029552298464, 572029552298464, 573129063696864, 573129063696864, 572029518481888, 572029518547424, 572029518547424, 1978643241384089909978371567767693047965196092892047117747637797010427268189173526238445404126191824776227778820123843426128754818964547576202825415225089214369796163774658343, 574228609370592, 574228609370592, 572029653223904, 572029653223904, 265799627475796019048683373518995713911825477452024455085589783605196154291679658348967786622480284100] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_15 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨3, 1, true⟩) 102 ⟨2, [0, 0, 1], 1, []⟩ 5 [1461518362953615144918961994083324121644096575906, 1461685618500068828410493553980390916360972032418, 1461529513368749706412562719932439639720249547682, 1461518362953615144918961994083324121644096575906, 1461551814241554125581794129620649852175702318498, 1461596415902092371556197033017111924480314202530, 1461507212538480583425361268234208603567943604642, 1461685618500068828410493553980390071936041900450, 1461507212538480583425361268234213107167570975138, 1461507212538480583425361268234213107167570975138, 1461507212538480583425361268234213107167570975138, 265751093741069849903969628955447899257234004258296899433929587261822384517897096623799897640754259813, 1461518362953615144918963203013755422291698669986, 1461529513368749706412563928862870940367851641762, 1461507212538480583425362477164639904215679916450, 1461551814284089421763825296541060329126451240866, 1461596415944627667738228199937522401434821221282, 1461596415944627667738228199937522401431063124898, 1461507212538480583425362477164639904215545698722, 1461685618500068828410494762910821372583643994530, 265783407324241994635944827399191121606148642934800957638459412873936783063416993069695920848597580228, 265783407324241994635944827399191121606148642934800957638459412873936783063416993069698058299201976772, 1461518362953615144918961994083324121644096575906, 1978643219271028827039652706902412209779454371952978974725559731792003477645348210494527961297136211621304185462431421644905973540174895041344919278995622290651134844800219943, 1461529513368749706412563928862870940367851641762, 1461507212538480583425360059303777302920341510562, 1461507212538480583425360059303777373289354123682, 1461507212538480583425360059303777443658366736802, 1461507212538480583425360059303777302920341510562, 1461507212538480583425360059303777584396391963042, 265751093741069849903969628955447899250986229142217945242601270361476233573025118411126322725213746181, 265751093741069849903969628955447899250986229142217945242601270361476237784497194823474213441759958021, 265751093741069849903969628955447899250986229142217945242601270361476235377941722587847248090007589893, 1461551814199018829399767798421969011063156399522, 1461596415859557075374175537540156215589164046754, 1461507212538480583425360059303781806537148750242, 1461507212538480583425379402190682616898782255522, 265783407324241994635944827399191121606148642937707463482596690906925202020431751154574505858285599172, 265783407324241994635944827399191121606148642937707463525949339572868733407577187476602920625911527876, 265783407324241994635944827399191121606148642937707463525949339572868733407577187476602920625911527876] = some [] := by
  decide +kernel

private theorem solve_0_1_1 (N : Machine4) (h11 : N 3 1 = none)
    (hAlive : ∀ q a, ¬ (q = 3 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    (hm : Matches N (baseTable 0 1 1)) : CertProp N := by
  refine branch_one_sound (tb := baseTable 0 1 1) (q1 := 2) (a1 := 1) (rem1 := 102) (cur1 := ⟨2, [0, 0, 1], 1, []⟩) (step1 := 5) rfl ?_ N h11 hAlive h107 hm
  intro m hmem N h11 hAlive h107 hm' hsum1 hrun1
  simp only [moves16, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkTree_sound tv_0_1_1_0 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_1_1 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_1_2 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_1_3 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_1_4 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_1_5 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_1_6 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_1_7 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_1_8 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_1_9 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_1_10 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_1_11 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_1_12 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_1_13 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_1_14 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_1_15 N h11 hAlive h107 hm' hsum1 hrun1

set_option maxHeartbeats 0 in
private theorem tv_0_1_2 : checkTree 4 (baseTable 0 1 2) 107 startPos 0 [] = some [] := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem tv_0_1_3 : checkTree 4 (baseTable 0 1 3) 107 startPos 0 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_0 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨0, 0, false⟩) 103 ⟨0, [0, 1], 1, []⟩ 4 [570105910036960] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_1 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨0, 0, true⟩) 103 ⟨0, [0, 1], 1, []⟩ 4 [576702980164064] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_2 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨0, 1, false⟩) 103 ⟨0, [0, 1], 1, []⟩ 4 [570105910036960] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_3 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨0, 1, true⟩) 103 ⟨0, [0, 1], 1, []⟩ 4 [570105406720480, 1461507213219055783030206551823384419657151715746, 570105406720480, 567906349877728, 567906417052128, 1461507213219055783030206552339893253721019160994, 567906417052128, 569590010644960, 1462934460901127842885968839928953484051945134498, 569590010644960, 567356594063840, 567425380714976, 567425380714976, 567356594063840, 576290260388320, 1461507213197788053968009483176454834608822852002, 576290260388320, 1461507213219055701900568137142915747573308365218, 265783407324362844182504955463973551434381688491544814997751632860369841583427312195766348172532855556, 1461685619159459376019800647702093893882575100322, 265750998701117921836537757714685281983604593985493160866237516476042235699445763285257753460309784901, 1461685619159542453086449855001207732198018423202, 1461507213197788053968009483176454834608822852002, 265792024279875919650814989833076326386295740617068348441429671470344812842374444226623985807006053124, 1461507213197788094532828690479795682503325424034, 1463112866852746875367413056762193266094677989794, 1461507213197788053968009483176454834608822852002, 265783407324241994636056511752742025587762136288932901612002280717362411406261730155834954936247071492, 1461507213197788053968009483176454834608822852002, 265783914204098907445346004429684184863150592815728698119841213844262360857795807297407620247590220548, 1461507213208421918499108017463026138985568180642, 578386204461536, 265750967021375644907075279929670662110849529732320726621173063550942894242923662679636518565393609476, 578386204461536, 576290260388320, 576221540977120, 576221540977120, 576152821434848, 576290260388320, 265750967021375644907075279929664110843903982941595958268894867784139247119053983407649905532074341124, 576290260388320, 1461507213197871131034658691656160293641677478306, 1461507213197954208101307898955274131957120801186, 1461507213197788053968009484357046455326234155426, 1461507213198452670501203142749957161849780738466, 1462934460891823246915474429925431479052555819426, 1461507213197788053968009484357046455326234155426, 1462934460893152479981881089524367007642494736802, 265783407324249547732710350944557528415975740869227639664132590932559437171359956633921912990532317956] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_4 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨1, 0, false⟩) 103 ⟨0, [0, 1], 1, []⟩ 4 [567906886814176] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_5 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨1, 0, true⟩) 103 ⟨0, [0, 1], 1, []⟩ 4 [1461529513326246942861795011930017324569364267491] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_6 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨1, 1, false⟩) 103 ⟨0, [0, 1], 1, []⟩ 4 [567906886814176] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_7 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨1, 1, true⟩) 103 ⟨0, [0, 1], 1, []⟩ 4 [265783407324243882910219741637067900430355570708692959242186585925149191211336193145291056725803348740, 265783407324362844182504955463963724533629319785269477978235599646050540102974630262714875243460244228, 265783407324245771184382985689740598855632717266197095622815266676375805926693985247881156529312169732, 569590010644960, 1461507213197788053968009483250241810903661058466, 569590010644960, 567356594063840, 567425380714976, 265783407324241994636057377269678808853453010789752348927844578242306544546875732545401664552134975172, 567425380714976, 567356594063840, 576290260388320, 1461507213197788053968009483176454834608822852002, 576290260388320, 265750998701117921836537757178319940477374327820394551099169841754552727591456247943089980298066285573, 265783407324249547732710350944557528415804903268397355760464036087617417322179314928145379827229340420, 265783407324249547732709473365742152567318090094580196175451448561875414976624506155199168205233009412, 265783407324241994636057377309929793547935578800981192163359425710988231983904994714800835675725968132, 265783407324249547732709478517868270233747802871595235864900425134771078606188713256198210932019770116, 265783407324241994636057377309929793547886768057886825333739838612433369169853382798864148980702589700, 265783407324362844182504089906785783474061813755259322741682462121812848518772593973211960696438469380, 576565037894112, 1461507213197788053968009483250241810903661058466, 576565037894112, 1461507213197788053968009483176454834608822852002, 576565071514080, 576565071514080, 1461507213197788053968009483176454834608822852002, 576565138557408, 1461507213197788053968009483176454834608822852002, 576565138557408, 1978643212130352852018904017765050920136864419461724790741926534646584005319498616051424761023997529619062131566744728447465426465171728882421218551664312304157195001861389095, 576290159725024, 1978658307749707971469964002707005717798711987432088834314659845754645161037077415495119913532751794733263307095534453812360397360826614026010647370036409146404449782516835366, 576290159725024, 576290260388320, 576290193344992, 576290193344992, 576290260388320, 576290260388320, 576290260388320, 265783407324249547732709581560390623562358074436973868769848883609397665558333540436095790789559530244, 265750998701117921836538196504826711816353518156512967409964036169722222339636906119481531000732918405, 265783407324241994636056937661834419345965962324427383216793149556261510803793730040173647453271307012, 265750982861126169859574169749590111374461935297371986807711930053303440997649688186694080895389961573] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_8 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨2, 0, false⟩) 103 ⟨0, [0, 1], 1, []⟩ 4 [576702979901920] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_9 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨2, 0, true⟩) 103 ⟨0, [0, 1], 1, []⟩ 4 [576187584154080, 576565541210592, 576187584154080, 265750998701117921836537757721288959160043188329772040829351748751694588456184471209062252457749936453, 1461507213197788053968009483250241810903661058466, 1978672283204312392172682839492436235413505151829294853078978532257549018085474200479832497205991568286662264991341369332178740240629211373502232708907900832610295402709637414, 1461507213197788053968009483176454834608822852002, 265750998701117921836537757721288952762321469464922948757420974899054748433593268404935175877372180517, 1461507213197788053968009483766750644967528503714, 1978643212821386010807107750444979246519135047211733565422013845751481569574969665040420172175779744346787847325785417769786183661774987193324336254084545882835626463921665831, 1461507213197788053968009483176454834608822852002, 265750998701117921836537757721288959160043188329770620075693454194473067886823895926246000466486393157, 1461507213197788053968009483176454834608822852002, 1978643212821386010807107750444979246519135047211733565422013845751481569574969664779647738517598156760570831177276143244134007243600619929386937167049768173271519846910097191, 1461507213197788053968009484357046455326234155426, 1978643212821386010807107750444979246519135047211733565422013845751481569574969665036314271292909792103048474091620664220895940753851850241861447844391898156741184197060687655, 1461507213197788094532983433575002165396393466274, 576221943826912, 1461529513305647723295212656214929827049507395043, 576221943826912, 265750998701117921836537760190016058807971673363321172025973302636721979785696359934844654601151584069, 576290663303648, 576565541210592, 576290663303648, 576428102257120, 1461529513315616952278358497989767269434469138915, 576428102257120, 1978643212130352852018904017765050920136867169950653788686607746565701118586303326976072862438787270457474568626904290274744411291619199258801852005182094551342098767638313767] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_10 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨2, 1, false⟩) 103 ⟨0, [0, 1], 1, []⟩ 4 [576702979901920] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_11 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨2, 1, true⟩) 103 ⟨0, [0, 1], 1, []⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_12 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨3, 0, false⟩) 103 ⟨0, [0, 1], 1, []⟩ 4 [567906887010784] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_13 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨3, 0, true⟩) 103 ⟨0, [0, 1], 1, []⟩ 4 [1461529513326266414012152723434563327710879302115] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_14 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨3, 1, false⟩) 103 ⟨0, [0, 1], 1, []⟩ 4 [567906887010784] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_15 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨3, 1, true⟩) 103 ⟨0, [0, 1], 1, []⟩ 4 [1978643683645312447017799426459828952920494801497795796778369202806349869621484938819680143917374685476722176337432782841288458817539974209936006822242412159951753384660065318, 3353732545142508947553908488851270102020026734266920034948015480063201624623654300155387364910189717561461360806005328793099007248996127527471797355078899745064686173797463199246306409672644532422654221337998428682929094695160466006377682321373447782217889295741515166236384873784877226013227471050166430444365193134830737676639083450934855738726665990402215847735434035189435178, 1978643683645312447017799426459828952920494801497795796778369202806349869621484939080416770317472874273031692703330953917870499698008929406917567591823936879224863997951761446, 1978643683645312447017799426659620860140718304306218019485131846374260150752043092474725868121795441259662979981411664373930298660388949163453860893105430809583788635657624614, 3353732545142508947553908488851270102020026734266920034948015480063201624623654300155387364910189717561461360806005328793099007248996127527471797355078899745064686173797463199246306504386238449210038955317798401693278433518076277924264519062208595180592238579274707074764319938640444958606161237588295328194218394653373036488629132030616314083872713756191145771549616330993748778, 1978643683645312447017799426459828952920494801497795796778369202806349869621484938819680143917373064387472853910696852847498337186830028430150687854345859753775642600845106214, 3353732545142508947553930595299638787794850888996718394267265078346475931610402163882124609028153456509413908142061972277452563261894710774761775629382270296208751694200985445726312682394986968516006941697970264036101821460716510157148761748991222528132943255526685755731165721874801048326493041975123313014759301260254220007286533101666492343917618943137229673580061152052394794, 1978643683645312447017799426659620860140718304306218019485131846374260150752043092735402815718341796918117166613167140021938486808308128818869553386419625778906901479628233766, 1978643683645312447017799426459828952920494801497795796778369202806349869621484939080416770317473105857210167335721800275202800150489540467413220971993713781598449266206727206, 3353732544361704900013196129983081852094211568669899006373081091786749743828972815413655942425020642181149451792786643938875745076577253757649525788401744873839530096245075249636986680132838629330367449832728947808384765676248298569043125337738174941260482540196102250593050581613081594144078433922795967326589834138370224027857542762961372753271417683810640046765774183242692395, 1978643683645312447017799426634646871738190410471297957765269374869976725239876258498727787712599561723829786616471190916129850259112336417520495847738355380046041024505338918, 1978643212130352852018904017765050920136864331451038827952974000003699500859553231276750358125041645449813528089619705991107998902743157835657649348666386047161802435135683367, 1978643683645312447017799426434854964517966863300160629125468978028651157147945555776045480475229516005615883006110277026361701127924553777224547494138887824819078097567243302, 1978643212360697238299515672563389617455228606509476521844309252201179523657068269683288129542439420529772696217689834145646622921615604517945630668155201262321344675092028583, 1978643212360697238299515672563389617455228606509476521803961597856071576943694532620741069005682054211618556964603025746462091701352239388297068307518765153666196189928406183, 1978643683645312447017799426634646871738190371653920920544173638361888833053258514211085849885718588994147238545463749587701149033294836889009522129966507189067955933008387110, 1978658779495010881948298537256741888660612428790846856754736034761368632129079381907195170448094574984201724017114833097411503046244424286888196104603515941618422730955140902, 1978658779495010881948298537256741888660578402588360441496349445136819933881349169300907593998375722263291069453227444836209780313388327971679761749826773667974229391404150566, 265750982861126169859573953386707878483745990046261983824140301519549841190432266497989934899258861413, 1978658779495010881948298537256741888660589715080712619039406272196067941291203723489322920947785852036464590989373698087338173754129312860628594105172228110822236927646740262, 265750982861126169859574169776008096107321612162237197640458454826472593568686553168872419754621151077, 1978658779495010881948298537256741888660589715080712619039406291435328779654413619132173496165715065369111566411535766075797004408484284219974946857314541051457138824208953126, 265750982861126169859574169776004820473825958731049329012935171614594342353850335059782654054677227365] = some [] := by
  decide +kernel

private theorem solve_1_0_0 (N : Machine4) (h11 : N 3 1 = none)
    (hAlive : ∀ q a, ¬ (q = 3 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    (hm : Matches N (baseTable 1 0 0)) : CertProp N := by
  refine branch_one_sound (tb := baseTable 1 0 0) (q1 := 0) (a1 := 1) (rem1 := 103) (cur1 := ⟨0, [0, 1], 1, []⟩) (step1 := 4) rfl ?_ N h11 hAlive h107 hm
  intro m hmem N h11 hAlive h107 hm' hsum1 hrun1
  simp only [moves16, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkTree_sound tv_1_0_0_0 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_0_1 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_0_2 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_0_3 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_0_4 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_0_5 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_0_6 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_0_7 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_0_8 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_0_9 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_0_10 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_0_11 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_0_12 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_0_13 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_0_14 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_0_15 N h11 hAlive h107 hm' hsum1 hrun1

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1 : checkTree 4 (baseTable 1 0 1) 107 startPos 0 [574503453723104, 1461596415689447448768746589210334639930076037603, 574503453723104, 574503453231584, 574503453231584, 572304396388832, 572304396454368, 572304396454368, 573988057156064, 1462934465665080979779107328416197988096700094882, 573988057156064, 571754640574944, 571823360117216, 571823360117216, 571754640574944, 571892213877216, 1461507217961741190861147971663699338653577812386, 571892213877216, 1461507217983008838793706625630160251618063325602, 573988057254368, 572167360219616, 573988057254368, 571754640706016, 576221473802720, 572029787048416, 576221473802720, 571754640706016, 571892213877216, 572029787048416, 571892213877216, 572029787048416, 1461507217983008838793706625630160533094113778082, 572029787048416, 1461507217961824267927797178962813317706509490594, 1461507217961907344994446386261927156021952813474, 1461507217961741190861147971663699338653577812386, 1461685623923661744112881922328061362873857776034, 1461507217961741231425967178967040186548080384418, 1461685623923994052379483587246241918726039443874, 1461507217961741190861147971663699338653577812386, 1461507217961741190861147971663699338653577812386, 1978665855674557394879143348849974753181909438943306421493572468288378437183053434748583651332240502924292363482002764703680869713857643288380869587242453665632277884671360038, 1461507217972375055392246505950270643030323141026, 573988057254368, 572167360219616, 573988057254368, 571754640706016, 576221473802720, 572029787048416, 576221473802720, 571754640706016, 571892213877216, 572029787048416, 571892213877216, 572029787048416, 572029787048416, 265751220461005753993829917684494971435391133190671082548246476713258932005574705490489945142966890821, 265751220461005753993829041823068070676485785745087598938548778953816245103251514289244982777762420549, 265751220461005753993829972747894443623871210758390929381838640843915396109479962005697691079537605477, 576702510533088, 572304665348576, 576702510533088, 265783407324243882911907990298147970559631235670119628938687261655727140700640365878094949614472082180, 1462934465675714803745386655399432666719699638690, 265783407324245771186071234350820668984908382227623765319315942407111471433076153369901662722142437124, 1461507217983008838793706625630164755234870565282, 576221474195936, 265783407324241994637745625970996761143131008551467653690527810062402279291809095897974322367062815492, 576221474195936, 571754641099232, 571892214270432, 1461507217961741190861147971663703842270385052066, 571892214270432, 265783407324362844184192434740886716710039687021035923633203080197447905474229329956502249864385737476, 1461507217983008838793706625630164755234870565282, 265783407324241994637745186322914489475241627285854052913293825448182945763887185941572950499189273348, 572304531130848, 576187517110752, 1461596415668350741310561062359225751496946745827, 576187517110752, 265751220461005753993829038824317256017160829254141866735554266710039513100153328857399044583949102597, 571823763229152, 572029787441632, 571823763229152, 1461507217961741190861147971663703842270385052066, 571892348488160, 572029787441632, 571892348488160, 572029787441632, 1461596415678818431742864249703605486726399677923, 572029787441632, 572304531130848, 572304665348576, 1461596415689467893476774525164921084529287906787, 572304665348576] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_2 : checkTree 4 (baseTable 1 0 2) 107 startPos 0 [565192467941856, 1461864025121151791382348477326858099428379591139, 565192467941856, 265783407324243882917339402572807689643305968769445871975796724827561534756218353760814531801384170244, 578592429869536, 265783407324241994643148021686456261190333195227858701725785974821684543364869198572226627801507377924, 578592429869536, 1461507212517223320126132556323492596040124635554, 571892213811680, 265783407324241994643148021686466088090844560892969491012327444212024338443173243614453235008149861124, 571892213811680, 1461507212517223320126132556323492596040124635554, 572167360219616, 1461507212517223320126132556323492596040124635554, 572167360219616, 265783407324245771191530783459149291195767471979406279704092760132362323224059540141706588681828499204, 565191964133856, 565191964133856, 562958547552736, 562958547618272, 562958547618272, 562958547552736, 562958547683808, 562958547552736, 562958547683808, 265783407324249547739913545231832494300690383065843068395858076063424987540027670071159623945862460164, 265783407324241994643148021686466088090844560892969491012327444363431724464270670326932566545856148228, 265783407324249547739913545231832494300691527067651389573779132214724035932966325855262940164113249028, 265783407324241994643148021686466088090844560892969491012327444201930522976403391769120008721794282244, 265783407324362844191396398412328587448374664987457872674361404242315276884560959237569485815547114244, 578867576211936, 1978658307749707751796438865740812776271974821406447741793797016095578021941847786650211697276979554295542004940818744171058115515232909346902275276597062303618274774471408806, 578867576211936, 562958547552736, 562958547618272, 562958547618272, 562958547552736, 562958547683808, 562958547552736, 562958547683808, 265752994540108411252159291935325962154590140960230209600410934428966162879870414135603605464610360837, 265752994540108411252159291935325962154590140960230209600410934428966160473021172930187783995978698245, 574125596772832, 574125596772832, 571892213877216, 571892213811680, 571892213811680, 571892213877216, 571892213877216, 571892213877216, 1461596415838382886606287579991695911877361047970, 1978658307749707751796438916887541027626322955077342578415064086589876568556739620057502519806938540100252428880123439358896120960579917349364074806923371385452108518125468838, 1461596415838465963672937996216629382414232230306, 1461507212517223320126132557430297240462697732514, 1461507212517223320126132557430297381200722958754, 265752994540108411252159291935325962154590140960139292505201083359513633014848746609318936368822506501, 1461507212517223320126132557430297521938748184994, 1461507212517223320126132557430297240462697732514, 1461507212517223320126132557430297803414798637474, 265752994540108411252159291935325962154590140960139292505201083359513637790940209626316746115492466181, 265752994540108411252159291935325962154590140960139292505201083359513635384090968420900924646860803589, 565467076921824, 565467076921824, 563233693960672, 563233693960672, 563233694026208, 563233693895136, 563233694026208, 565467076921824, 565467076921824, 563233693960672, 563233693960672, 563233694026208, 563233693895136, 563233694026208, 567425850935776, 1461864025121651226389023656289477498078922539491, 567425850935776, 265783407324241994643148021686466088090844560895878838059042679393418534749373607413174854837938107140, 571892616923616, 562959084947936, 571892616923616, 563233962854880, 1461864025131639926522527348878805181746420666851, 563233962854880, 265751980780636284726475874657056309611839796676833200885980282565267410378516828953741049368388570597] = some [] := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem tv_1_0_3 : checkTree 4 (baseTable 1 0 3) 107 startPos 0 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_0 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨0, 0, false⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [1461518373842650967241640947978049738673375713570] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_1 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨0, 0, true⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [1461696779740519264366108064517282704144594934050, 1461685629378470751024769817255180463379898734882, 265791533240010994859850449096519428268775036720933304623960112553316317258936230091097598759541357508, 265783415244245541738216665938757077672647571682497179328076114602945473009319012355479027935938291940, 265783407324362844184193204125043794662950744816165106292468212382347370970573655934000782852246156036, 265792309399607077758152348681723947464662293122959921382626954702604843832189022819949855330485631108, 1978643212360697238219068824983734034857829883918859015369840215625211592283253739346547688594905860554994861212200032527173887286195062965846409156116707269177661754717125415, 265783407324242938773040517802097861344490190736488987726375018509448182072921211554902872350615933380, 265783407324241994635944827372344029875533109841062494678725858657714247294289832091518687202720819428, 265783407324248603595614660461122819547197812125652844479419528730887225601203342572266588737051811268, 265783407324241994635944827358927034977372253838289329282459321016648089964521027000359507640019263172, 265783407324249547732710350917710640812476605026659762230051438438613782673624029970053047063431817444, 322300464588234307642837690426004949063595549388835510281272515530611924355467927806123541693793332647083941145706533320503971295070545974783635242571924250386186455668722573790363327674288008161466879881359166736279162141139460874478022297493419919143023370375560832737240753233434228960723807569750926466954097152047835365846330664611512172209401647600435421293512016217075317970424640801218387656936968360189991615823040438941521490175594014452794800499458456184552627749782451624866429955130807786110898950603970106913297953947160374214400426385751087529910903955497480441692023121254090201127961600957561237244571845741970003005750720365502544035867353307904471235810312933814811282210390016569259168840787520975240512370889555266155163694194207693200736655341668527262610791894790101212314778330658130610376194042382085270448, 265783407324302419410069015762110907167402783331386965881863572994548852427837418091174714334125224708, 2882773271902695771689261485590747524675989944279004272334056921417344718264938272224137859790976494440598841846777774125949226332243945586313878427465267692798038531089787352024618529805062280532900865967215608481382698437090476718982680024354636473410249514956731952387169513701231613815110724918756286138301193354511161841699145841726608191367557998539463657747602232542504358195931413743406662890830590544605396642720176913199340099850221247591764749541132857860776366249781727362699331579647791671499547054553420735041171431193247264097349554593672609916214824090310935751433716145811068693414515716812678030714279498354404159333853945968505397373126056494, 265783407324242938780228765771728194406386301312932315243888221525514404757201580699207889934927270340, 265783407324362844189595599840509845977193049103117615733306021987311423090143840393133747641828717316, 265783407324243882917310387476056738037534025255240470976710585285274353497093253371732568174087052996, 265783407324241994643148021659632098294522848890332507266509604434288613439348701281951051818025036004, 1461685629369166155054275406144853813957936322850, 1978643212360697238219068824983734034857829971951121844981362403485396686422284420779290150439239411898187553383340046655900073870759790136853111380575041594502694500878138151, 265787977161922864763227874245016069112521894810493895272040968623850526786077370234706974157913977604, 265783407324302419411869044949774208502503536266572933472732127105712183397845632450199651462139605764, 265796364437555536565568863030211835598041169291052817460852393361958486813124687399839569098714658948, 1978650759824859481673266488670356688855500468524356849158023725444457894434466353454887837902863328576439849011909385670192088778647839379817309985332864541790682095938992934, 265787525722157933419771689923643428757797323618623072763760787142210171701944142723377856135712269828, 265783407324302419410068246377955467031276160306990482373538344902471655302242029567931003167118979844, 265787715802058957143379578021374507366924179277294536217368570489835076695702332698987169279694323460, 265787462362190925512014943801805073896706749396539821473263163333789387425141116380113526548292694788, 265783407324302419409167847092046096295662472327199256821231913748780438756119044670428846202768323332, 265783407324302419410068246377955467031276160306990482373538344821721054558308390289024724255088046852, 265783407324362844189595160192414471775223432626563806786739745832584701910032575718506559419374056196] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_2 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨0, 1, false⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [1461518373885186263106758255910971564602413848866] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_3 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨0, 1, true⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [564607848581600, 1461507212538491049188329624896635204793615292834, 564607848581600, 563508303366624, 565707393796576, 1461507212538491049188329625413144038857482738082, 565707393796576, 564092452506080, 1461685619170010127990042839705685175807610231202, 564092452506080, 562958547552736, 565226357459424, 565226357459424, 562958547552736, 567494167366112, 562958547552736, 567494167366112, 1461507212538490968058691210216166532709771942306, 1461507212538490968058691210216166532709771942306, 568490599811552, 1461685619170010127990042839705685175807610231202, 568490599811552, 567494167366112, 569624471210464, 265783407324362844182504295991830490131280831547431001089043457332615171371105471854605670967629001476, 569624471210464, 567356728412640, 567494167366112, 1461685619169999743396325770050428114677512837410, 567494167366112, 265783407324302419409280397002784767637614183324673160015270216996987043295859312918858535295021740804, 265752994540078198865885046726481874564558149074635867910643710201184043585859768617824308556547616900, 265783407324362844182504515815878177232265639785707905562326595409978531961161104191919265078856332036, 1461507213219055701900587480029816557936015612322, 565191997721056, 480481077044047058460496032459646166403718999535435193338067811960724543778208163873725410872638755998003114358864820895611121053647057746645606216579307621279456322387848106760215224540742362281858238355938318385416724448933841464842516692685932616078327808201738761, 565191997721056, 562958547552736, 569624538319328, 563233425459680, 569624538319328, 562958547552736, 562958547552736, 563233425459680, 563233425459680, 568490599811552, 265750967021133945814517773353799160364105307796317238871185687835551836634892645479055502030898672388, 568490599811552, 567494167366112, 569624471210464, 569624471210464, 567356728412640, 567494167366112, 1461507213878352787809925095877005670197773769122, 567494167366112, 1461507212517306397192781764729411078778141055394, 1461507212517389474259430972028524917093584378274, 1461507212517223320126132557430297240462697732514, 1461507212517887936659326215823207946986244315554, 1461685619160705532019548429702163170808220916130, 1461507212517223320126132557430297240462697732514, 1461864025804187743912964301974029101153744107938] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_4 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨1, 0, false⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [564607848614368, 567906484160992, 564607848614368, 563508303432160, 565707393796576, 572304664889824, 565707393796576, 566291542903264, 567494167300576, 566291542903264, 562958547618272, 565226357459424, 1462934471130866533941188346900291995835925830050, 565226357459424, 562958547618272, 567494167300576, 562958547618272, 567494167300576, 1461507212538490968058691210216166603078784555426, 1462934471109598886008629692933831082871440316834, 1461507212538490968058691210216166603078784555426, 567906484160992, 1461507223427526790658669940660657081753097247138, 567906484160992, 572304664889824, 572304664889824] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_5 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨1, 0, true⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_6 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨1, 1, false⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [564607848614368, 567906484160992, 564607848614368, 563508303432160, 565707393796576, 572304664889824, 565707393796576, 566291542903264, 567494167300576, 566291542903264, 562958547618272, 565226357459424, 565226357459424, 562958547618272, 567494167300576, 562958547618272, 567494167300576, 1461507212538490968058691210216166673447797168546, 1461507212538490968058691210216166673447797168546, 567906484160992, 565191997721056, 571892348029408, 565191997721056, 562958547618272, 567425447823840, 563233425525216, 567425447823840, 562958547618272, 571892348029408, 562958547618272, 571892348029408, 563233425525216, 265750982861125933825305742806576666894507647538619621711877885598664245075425572465038831855852334597, 563233425525216, 265750982861125933825305522942277995099064667726056410134741106686003582415821031016807729287227108869, 567906484160992, 1461596426727408243482609803682057131892516362530, 1461685630049730888895862190948680312682775091490, 1461551825407152366013703778330978030742865485090, 1461507212517223320126132557430297381200722958754, 1461507223406580986536693748027712442276940650786, 1461507223427516324935004972569488600482949667106, 1461685630049730888895862190948680312682775091490, 1461507212517223320126132557430297381200722958754, 1461685631410860361650218445788883324691498965282, 265750982861125933825305742793159671996346788556584207777113556401020142160970462932790110965539761669, 265750982861125933825305522942277995099064667725965493039531255616551057326890826507520869938109214213, 572304664889824, 572304664889824] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_7 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨1, 1, true⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [265783407324242112660282345317988319613650770615081294074257340443995616076798043183069731886190506756, 265783407324249547739800995321083996058181165000626105536684919650156299982758881979110275890477740804, 564092452506080, 265792293559615089756086317243973067655945826283872668962928441486334827638853941355976546930559237060, 564092452506080, 564092452506080, 566291509381600, 566291509381600, 564092452506080, 568490599680480, 566291542936032, 568490599680480, 564092452506080, 1461507212517223320126132556323492596040124635554, 564092452506080, 562958547552736, 565226357459424, 265783407324241994635944827372344029875533109841062494678725858657714247294289939672930091679160150244, 565226357459424, 562958547552736, 567494167366112, 562958547552736, 567494167366112, 265750998701117921836539516306935753463176305855765991491264001425169088546373717599729358533839584837, 564126812277216, 567425447823840, 564126812277216, 563027267095008, 565226357459424, 265783407324362844184192326546238245714999702676460240753769219321563851270328108894906574807889031940, 565226357459424, 565226357459424, 567425447823840, 567425447823840, 567425447823840, 265783407324302419410068138183306996036236175964596809779140909774198812399543490887267163742167626500, 265783407324362844185993125118056987186227078636042691858382082759454694777645028594598793505023406852, 564126812277216, 567425447823840, 564126812277216, 563027267095008, 565226357459424, 1461507228851098857271709162851414784057409575202, 565226357459424, 565226357459424, 567425447823840, 567425447823840, 567425447823840, 1461507223406580986536693748027716875507823843618, 265783407324302419410068143335433113702665888741611849468589886347094476029107697988266206468954387204, 265783407324241994643148021686466088090844560895878838059042679393418534749373607413172717387333710596, 265783407324249547739800129763906054998613658970615950300131782125918608398556845689607361343455965956, 1461696769585798918887800819879526026569774569762, 1461507212517223320126132556323492596040124635554, 1461719069735835615032071573623845151390506721058, 562958547552736, 1461551814190056925061550767192253109947899878818, 1461596415850927478034904735278666336607990225314, 562958547552736, 1461685619169999743396325770050428114677512837410, 562958547552736, 1461507213878352787809925095877005670195626285474, 568593578330592, 568593578330592, 567494167366112, 569693123578336, 1461685635494248764701480006611513284156829243682, 569693123578336, 567494167366112, 567494167366112, 567494167366112, 1461685631410860361650218445788888039398969481506, 1461518362953625531770681695395114927198529690018, 1461507212538490968058691210289953509004610148770, 1461529513368760092947370980117604237218367445922, 1461507212538490968058691210216166532709771942306, 1978665855674558273573243845568018270493070294522287504016254504397958648080933046106960794928211647182654893812209658947262333723618707918697705846575676686124935165735058470, 1461507212538490968058691210216166532709771942306, 265750998701117921836539735272295754286447202224835786940833849433254135434762223362712646926347402821, 265750998701117921836539735272295754286447202224926704036043700522894310709675837693914825422375091781, 1461507212581026263923809727079519659286345062818, 1461507212538490968058691210289953509004610148770, 1461507212623561559788928243942872785862918183330, 1461507212538490968058691210216166532709771942306, 1461551814199029214033098949334353807604792204706, 1978665855674558273573243845568018270493058937667220385158589671213460398010083770460700055583519748898292696323332887104708865410774678518397578358906877303282596012660603942, 1461596415859567460007506688452541082499812465058, 1461507212538490968058691210216166532709771942306, 1461507213219055701900587480029816557934941870498, 265750998701117921836539955096343441387456415834659874828926778475875703626260973709348496327134641733, 265750998701117921836539955096343441387456415834750791924136629565515878901174588042739424242064391749] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_8 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨2, 0, false⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [1461518373821466315246093086704021232119125678370, 1463112883196259356047539652868711769857774885154, 1461529524236600876739693812553136732603025497890, 564092452604384, 576565406730720, 564092452604384, 562958547683808, 565226357524960, 572029787048416, 565226357524960, 562958547683808, 567494167366112, 562958547683808, 567494167366112, 1461507212517223320126132557430297521938748184994, 572029787048416, 572029787048416, 1461551825067119229976104935977537197394627697954, 1462934471120232709974909020507357560819426564514, 1461596426727657475950507839373999199330226968866, 1461507223427526709529031527234567217788541245858, 1461685630049730888896152333071601058496635771170, 1461507223406259061596472873268106304824055732642, 1461864035332094017699512078332111504702337759650, 573129063795168, 576427967777248, 573129063795168, 572029787048416, 574228608977376, 572029787048416, 574228608977376, 576427699341792, 572029787048416, 576427699341792, 572029787048416, 572029787048416, 1463202069216114639453289250340958473111571831202, 1461507217983008838793861368208858181923314375074, 1463202069258649935318407767204311599688144951714, 1461507212538490968058691210216166814185822394786, 1463112866362926402020777457601468456401860860322, 1461507212538490968058691210806462624544528046498, 1463112866533067585481251525054880962708153342370, 1461507212538490968058691210216166814185822394786, 1462934460911761702346464973302607182441877641634, 1462934461592326436188361243116257207667047569826, 1462220839107102903649215036107162086601944783266, 1461507217983008838793861368725367015987181820322, 1462934476548789460166788375791248533874256419106, 1461685618542614513979544413738618733641256180130, 1461685618585149809844662930601971860217829300642, 1461507212538490968058691210216166814185822394786, 1461551814199029214033098949334354018711830044066, 1461507212538490968058691210806462624544528046498, 1461596415859567460007506688452541223237837691298, 1461507212538490968058691210216166814185822394786, 1461507213219055701900587480029816839410992322978] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_9 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨2, 0, true⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [566291475827168, 265750967021133945814180123836248516640641609670518522659007761774089345632027470313438522186211209988, 566291475827168, 562992907356640, 565191997721056, 1461507212517306397192781764139115409156923759010, 565191997721056, 566291542936032, 570689623132640, 565191997721056, 570689623132640, 1461507212517306397192781764729411219515629410722, 566291475827168, 265751473900881574758128882235353615789997399804008767549559282934102847767651789708561527906503179204, 566291475827168, 562992907356640, 565191997721056, 1461507212517389474259430971438229247472367081890, 565191997721056, 566291542936032, 570689623132640, 565191997721056, 570689623132640, 1461596415838465963672945249771547175742799387042, 1461518362932440958369471048271309049555611326882, 1461507212517223320126132556323492596040124635554, 1978672341942130670649546475081896449002605241255593230946957010083531531065092373617014712715867734450891398282656800967502977207677127614245350566955050014961779879872289062, 562958547552736, 565226357590496, 1461507212517223320126132556840001430103992080802, 565226357590496, 562958547552736, 562958547552736, 1461507212517223320126132557430297240462697732514, 1461507217961741231426121922062246669441148426658, 570723882207712, 1461730226094623539201211170361442154766262115746, 570723882207712, 565226357590496, 565226357590496, 620836633680734436368365392057860095604029072735848736103068583895164997046716365623345951229902976916056624852187313495230096104437007387410782809226178865455176538789335631047979090522652929254444181352843321882205249822535013205120188950439090429141262021426140782080429476262054246133892434018311558387995884082550476243759046262422750501102358101200545247174251749235002607229852401273310656855927339288209535740328920718789059516499608128778684382980674729202267088536347405921852064721249692843934361965, 565226357590496, 565226357590496, 569624471210464, 569624538319328, 569624471210464, 1978643215585518701039197711721645447580361476843734861339016292205628364209155420799935308360598202023059685895147679076028014674250126731520659376286621557441807072310724390, 620836633680734436368365392057860095604029072735848736103068583895164997046716365623345951229902976916056624852187313495230096104437007387410782809226178865455176538789335631047979090522652929254444181352843321882205249822535013205120188950439090517847991589477596156750141578701509623428359435403629943860329663042774306800405177471473748693290953775453685977173164886208413735197507904262652508875860312212982925027805645278743641035079905028279717000126268384693418445219786556755949330006954717969935903085, 1978658307749707751796438865740812779249117592976320684341492243346386197618115472698678459782188692333676490573081145014987360975470256279891708284501771811382490665355050022, 570723882207712, 480481077938575810918990394979825615361736497958574967043041355717498465307405663477119515028243952192543027271968308427151175644808161910066264704077966908935426684781854547915824515238171414524896372171488004200905520254730130941054299787191491220595572996106782760, 570723882207712, 565226357590496, 565226357590496, 265751093741067961629778035167808798521758476144560960000580285839836902645644788827189871322266284804, 565226357590496, 565226357590496, 569624471210464, 569624538319328, 569624471210464, 1461596415498682059151892358696298821907781818786, 1978643215585518701039197721324143988353807258011288412971235063334017442358361331502383055022562903523840978347403004040445892280543392888817475372449108436878473748808206118, 1978643226642049407692750861373827766587681827311096539606668221746705377072998522998390883480239846485258218318361980612859247922596009899102301187507527529489912949486929702, 265750982861125933825305306532855560861707812428343121626970280731092492216504784129734451963440952293, 1461507223406259061596472873268106023348005280162, 564332970674656, 1461507212522540252391681823466778248228497299874, 564332970674656, 563233425459680, 565432515889632, 1461507212522540252391681823983287082292364745122, 565432515889632, 563233425459680, 480481077044047058460496429904277795385206397674184239738721957760044311357826211053943765158421622109976727197784598867962467915358608130002065950390586742946707604555072448822673843529121060275704575048329470169323448363648490793674792399029783787099668737082234761, 265750982861125933825305742746200189852783782119690414925833861998327984028885180651480773898414941701, 265750982861125933825305742746200189852783782119688994346221208075367788324370646205749573043721719301, 1978665855674557394879143348849974752809768012103955693532318678649720115593989058207047106953524630464985572026149658020142064904132785610352811933924662560491242217899293734, 265750982861125933825305742746200189852783782119698938403509785539401194614610290496475737340920550405, 1978666327419860497571812457362725006694252026601520662064510959106214417251311395056086465575833404218323596795635129271877710612671488074926223221190379609820156392434039974, 265750982861125933825305742746200189852783782119869407957028256321120970025457649350655070063700225541, 265750982861125933825305742746200189852783782119778490861818405251668444936527444839179461295676288517, 1978665855674557394879143425570067126119875944216790668851681426483106389072932420546011733268178635501819526421128796480074286844550523943310953861124028179751197584707812518, 1461507223416892926127571407554677327724750608802, 1978666358746697031734997510255206194100856704948432272454977429725159837721316784363990419110323054469331748637460888954713064733320120734906506237827160244975126948206345382, 265750982861125933825305522922152502751823379252960693867360517470242054845561585297968900998682371589, 265750982861125933825305522922152502751823379252959273287747863547281859141047050852237700143989149189, 322300464590579356914581858500626239515990306030937945507414849998038630447625122042622876300781074815800161479291664193909548529217073450355567328468382003348257159398004466300846531319020665656763628190781257593906480576918686232721433301114849142542222162273551480274456549944739699768995071277139864585996079514038850224641646591961076758281567798423593451673415560880090941861316405326003892814491664508648133975700587813864301399502821873209530926918217789326732078183721197749883315723259446034578869984645200852606001433571751370134344893535004924456537391895907088088216219398563606019372121337140588036649686188705249174933300843070493458945116110886255368621219990110556951518330316038735793471908426526389084987052448228510072688138843838474550873238261810636192039780051652700227317749793351688053903541503964149774960, 1978665855674557394879143348849974752809756655248888574674653845465221865523139782560786367608832732180623374537272886177590093168965383054640925019524564651461030739748846630, 265750982861125933825305522922152502751823379252969217345036441011315265431286695142963864441187980293, 1978643212360697238299515672563389617455276872601975388321757326585566266369243510690775327623880841684219898687975863119300611363610769263820596987038872914034631510176002855, 265750982861125933825305522922152502751823379253139686898554911793035040842134053990576948907257490949, 265750982861125933825305522922152502751823379253048769803345060723582515753203849481290089558139596293] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_10 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨2, 1, false⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [1461518373821466315246093086704021232120199420194, 1462934471109598850514412887133704143905544509858, 1461518373864001611428123044694000408423346247970, 1461507223406248758132394218219530939484037224738, 1461551825067119229976104935977537197395701439778, 575396806527456, 576565406730720, 575396806527456, 572029787048416, 578764094441952, 572029787048416, 578764094441952, 265783407324241994643148021686452985556813136428032996719329974466962396423051008070258945331023786756, 576427699341792, 572029787048416, 576427699341792, 572029787048416, 572029787048416, 1461551825237260414704224767937453902608288750882, 568593578330592, 265783407324241994639546424542815502614309573765773727680484660341218470199489983106989082644324758276, 568593578330592, 562958547683808, 565226357524960, 565226357524960, 562958547683808, 567356728412640, 562958547683808, 567356728412640, 1461685630049730888896152333071601058497709512994, 1461507223406259061596472873268106586300106185122, 1461685630730295627808631660911267879348058757410, 573129063795168, 576427967777248, 573129063795168, 572029787048416, 574228608977376, 572029787048416, 574228608977376, 576427699341792, 572029787048416, 576427699341792, 572029787048416, 572029787048416, 1462934471109598886008629693524127385813234260386] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_11 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨2, 1, true⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_12 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨3, 0, false⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_13 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨3, 0, true⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [1978643213742763555902738753784692338694144220399539075897894779059690210813166100445293245307841169370503587738311706466243536316953664440676329966688912828420015224736693543, 265750982861126169859576587921005142905609947173229027932924615033240576337154407268696627781507360805, 265750982861126169859576587921005142905609947173229027932945783318879710094167532263303607625503615013, 265783407324244945064366222574897674428007003135735057553609928133350709198774267757091841156613155172, 265783407324244827047231898728690498773208632541202124033609766337594486820501655511775706981536639332, 265783407324244827047231022867263495650754257922311471084168840025032100924185814366095030228732881252, 265783407324243882910149404597685799494107686114172711841777239873806088409817261065410231393054832228, 265783407324243882910149399445559681827677592003227247411471860276702964914518275746317941650879624804, 480481077044047058460495734376172444825748232619018177812328230302699393551292492278118464372395449933456305615320586861796606724256810119290322643294429303164804652186671087105815627461462370636071438538763875982183405206602213744146381495555330147511967745080593161, 265783407324305251820455028333580704358086887359583104594246388032027276954489887060555767490562550116, 265783407324244827047231898728703524534627478706092379938987070433941794266696906793512916563221817700, 1978665855674558273573243845568018270493058937667220385159850535411745025824366184099513072340166861691836146859998226962945294885117592254707330370254396940608093703854087206, 1978643226642050066284276303446591917069287406898711087276345203231420639315299539728550871075444842182004233914643083597903824538230944317579505970920608019106712495328091174, 1978643226642050066284276303434104922868023432427845308824417879864508605615991034357690183681215146014611824280712657485603176663782358369537672788016566472947678984813698086, 1978643211900009344325130396240532340879690722733023074645867696998700900830220514655226576793994623003378240665494043501248362934123130750045884590000374711362084650380712998, 265783407324241994635944827399178019671854821846608831020397962696114984671063308884564885204086503012, 265783407324242938773039641980921894098292897712571421184746994188597717578832359049835465609843059044, 1978643211900009344325130396240532340879690744567796916977019037915714200290963962786889072909546947196190733510414291797720798680731474149958720878158890943487507196778667046, 265783407324241994635943948103000373801995824104441421296597701927168929963030134253536325113758299748, 265750982861125933825305358101076219569602019439416287002603519149415202110702060579394175755779134469, 265750998701117921836539735272295754673809265193807213651840060254129376384874742617726920061582442053, 265750998701117921836539955096343441774818478803631301539932989296750944576079723988007665154006056517, 1978643234013070427263849257056645639402296723704030169012537896885288653215032451591172336649686834211927284950592893550409984436190633222073291212038443920589733783755578406, 480481077044047058460495734376172444825748232619018177812328230301559897273990790369348541432035555405489259061495027795104761724683127238619411218877086795379897712524849233832083298224730622188576399822308643947520844430640844545190401117762197696972595201080593161, 265750982861126169859575709054158244038066396399755167101619218684021148926010633509264917437198510117, 1978643212360697238219068824983734034857829888814343369700826644645593796531305274656637956389199655710331828475482428974545747582250650062927213651124795613331670288008100647, 265750982861126169859575712059565190794202872463209745394282349431226935984975120966664346286574924837, 1978665855674558273573243845568018270865178360599877289540960831388916859034928597409318255551433171492767764118454276273751742837725946502625456977960996714054052545096055846, 265750982861125933825305358101076219569602019439586756556121989931134977521549419423997729770860799493, 265750982861125933825305303145077400328433001919514340680284918794327023317838531512728559119657823749, 265750982861126169859575928448862081602484684857657172326927163624731373661675555100556373466707273765, 265750982861125933825305742793166223263460122276786779201424225959929000105834799593871066690164583941, 265750998701117921836539955096343441774818478803699489361340377613981076032843292402520951311796351557, 265750982861126169859575709483518465344535896700503862183434443599342876723400753997012248777157388325, 265750998701117921836539516306935753850538368824805606023678551482348821515492184696525405723121300037, 265750982861126169859575708624830772669124576004603066626371822628574139181966546069337545688647084069, 265750998701117921836539522317749557794706589509449233080046080236123940965760976843718059539310706245, 265750982861125933825305358101076219569602019439495839460912138861682452432619214914437276744379649541, 265750982861126169859575928448862081602484684857657172328281933905635934110515554893294296873297389605, 265750982861126169859575928448865357236029149031939407612014203092246863076130497326459240548243482661] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_14 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨3, 1, false⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_15 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨3, 1, true⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [265750998701117685802269989398858668251420377042398212843533004639124712114378035594120965925587515429, 265750998701117921836540394744438816376792140896842988209478292638558127194879556699003072995151557189, 265750998701117921836540394744438816376792140896844408789090946561833754933550081918516408986677523013, 265783407324244827047231898728703524534822340344539422516609015803953785657168576239164245479656794468, 1978665855674558273573243845568018270493058937667220385159850535411745025824366184099513072340166861691836146859998226962943798307440965410119089796985695466795966028930079782, 265783407324241994635945707124699505481722118776683382466605148223553365376572820601090834501428524644, 265783407324241994635944827399178019671854821846608831020397962696114984671063308884564885204086503012, 265783407324242938773039641980921894098292897712571421184746994188597717578832359049835436386885577060, 265783407324241994636000229927871199694878217528462646366655987823275096139272105534823391297305523812, 265783407324241994635943948103000373801995824104441421296597701927168929963030134253536325113758299748, 265783407324249547732709499126372536172372412969481420401792040018599230889447932623929215298776020580, 265750982861125933825305358074242229773280301475527293323493239875189457850906304937375058340364407813, 265750998701117921836539735272295755073666878581202944782073452912818793062637136111972033684772978245, 265750998701117921836539955096343442174676092191027032670166381955440361253842117482252778777196592709, 1978643683645312447017799426435635401655545861704588418247472163936798234015831412401536216883026450974957660038248356464378408747592188643458218989226609850666255829961563174, 265750998701117685802270648870982075753108016711535513520519930777437993334998739304020713056046282789, 265750998701117685802270648870982075753108016711535513520519930777437993334998739304020713056046282789, 265785434843186247687873971056203883641300662127698820544426672465559575634187008814054546892604520900, 1978643683645312447017799426634646871738190454834011782902367597299768312133821564872264400155967154212247156391574404123174117674746399703811650459344605389208755458385140774, 1978643213742763555983185601364347921291568495762436645896955412302328439714832440908095618625875586091133624161874042677364519942700051522014189764003898002991780770912070823, 265750998701117685802269549750760018415784269533826251365769604816255424949957271015235012943136028709, 1978658337233790074408831176870975446330086718475404712859338489283372777627855686068277621335181024257261618386707079139010057562398105501038356891425971781833761725489347622, 265750998701117921836539516306935754250395982212110420058703418653259875332963366387223160366564618821, 1978643213742763555983185601362787047016444570298592966523510546114338664685322540936995456014997670949318673841907680749338190627898560394390401850586332690965535259810069287, 1978643212360697238219068824983734034857829888792681887714246914356852812382890231966264354275898747016745223354327149209333908072232558213650648721980936236942283737031916327, 1978643213742763555983185601362787047016444570298593131787502743676488403224085734674206465755528982161734564534517873659448383430732291932640979574457452340544831866949073703, 265750998701117921836539522317749558194564202896754047115069621805173182368609756008881345666034925125, 265750982861125933825305358074242229773280301475697762877011710656909233261753663781978612355446072837, 265750982861125933825305303118243410532111283955625347001175962537943867666788721471183136419049238021, 265750998701117921836539735272295755073666878581271132603480841230048924519106935554507714372003770949, 265750982861125933825305522942287821999624844134261566261745617412754467963725083974254852796797545989, 265750998701117921836539955096343442174676092191095220491573770272670492710605685901143563772775084613, 265785434843186247687761421145465212299348951130270375900025449456774501132704803279857222136830835140, 1978643447772660895671464911537485559913237674582786955630894919155834184034020106511031253914792201604778039584636111411554621644777040819450307303416004131232994278930930726, 1978643213742763555902738753787814087244437853692537089500721563347923986570785854116378070540216620737397607413911850532417623583990826681347206113408251139920434437364332327, 265750998701117921836539516306948856784476312756624506653354884829164025698546031919819730175218922053, 265750998701117921836539516306935754250395982212201337153913267158880826802000523791244214061117977157, 265750998701117921836539515448267721773875639274137362868733241026309014592570491652868249266586628677, 265750998701117921836539522317749558194564202896844964210279472894813357643523370337963173162501242437, 265750998701117685802270650159010310342981418762681070680949091391305137252905678264376864783763896357, 265750982861125933825305358074242229773280301475606845781801859587456708172823459272418159328964922885, 265750998701117921836539735272295755073666878581362049698690692319689099794020549885709892868031459909, 265750998701117921836539955096343442174676092191186137586783621362310667985519300225779494012096590405] = some [] := by
  decide +kernel

private theorem solve_1_1_0 (N : Machine4) (h11 : N 3 1 = none)
    (hAlive : ∀ q a, ¬ (q = 3 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
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
private theorem tv_1_1_1_0 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨0, 0, false⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [1461518373842650967241332670718068073534841723170, 1461685630069669384891653807598942559389336246562, 1461529524257785528418020746510126223644632850210, 1461518373842650967241332670718068073534841723170, 1461551825088054650771396898094242576640773233954, 1463023679885816726094222902645918461501945977122, 1461596426748592895478149201262475177079937734946, 564092452506080, 576565037894112, 564092452506080, 564092452506080, 565226323904992, 574297295096288, 565226323904992, 562958581107168, 567494066702816, 562958581107168, 567494066702816, 572029552298464, 1461507212538490968058692419146597833357374036386, 572029552298464, 1461507212538490968058692419146597833357374036386, 1461685630069669384891653807598940589064499271970, 1461507223427526790658361664581271470562589317538, 1461864035350703280628626236073629903699158546850, 572888545757664, 576565037763040, 572888545757664, 1462220836427379244181251520121302883132914063778, 574022417123808, 574297295030752, 574022417123808, 572029552298464, 576290159856096, 572029552298464, 576290159856096, 572029552298464, 1462220836384843947999221562131323706829767236002, 572029552298464, 1463202069194930020416656995000898363721585301922, 1462934460922395490818509359938949109434566089122, 1463202069237548393348423510232934027965999651234, 1463202069216197668349215648967359276686070815138, 1463112866341991016719390397823914763008267557282, 1461507217962405845423860845833927894325450021282, 1463112866512464508446456458752057419985924954530, 1461507212517223320126133765180141423992515893666, 1462934460891823246915456294862161547048118163874, 1461507212517223320126133765180141423992515893666, 1462934461573717213823720538574732174958747752866, 1462220839091152167699719883015148683207520606626, 1461507212538490968058692419146602336957001406882, 1461507217972375055392247714880706447277552605602, 1461507212538490968058692419146602336957001406882, 1462934476564740236680718296309454245786035460386, 1461507212559841693057900280412177088236930242978, 1461685619191277775922583359715680801182714993058, 1461507212581026264240722377136581513260148234658, 1461518363060296077164770593967420405150993389986, 1461518363230769568891836654895563062128650787234, 1461507212517223320126133765180141423992515893666, 1461685619160705532019530294638893238796267067810, 1461507212517223320126133765180141423992515893666, 1461864025804187743912926824097645053600018250146, 1461507212538490968058692419146602336957001406882, 1461507212538490968058692419146602336957001406882] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_1 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨0, 0, true⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [265783407324242112653080909623068645468459262263995656150121642139896576426620405737777782594728047364, 265783407324249547732710350944557528415783548570839248938381296888640694283903264082086227370477564676, 265783407324242230670217871572480760273791811374230934085118758166876559843986172525895108810810801092, 570895848475104, 265783407324362844184193204125043794662950744816165106292468212382347370970573655934000782852246156036, 570895848475104, 1461507212517223320126132556323492596040124635554, 567494167300576, 1461507212538490968058691210289955760813013768610, 567494167300576, 1461507212517223320126132556323492596040124635554, 265783407324362844184192544652910560260556496509539548999618016805637827683403019743932737445188285188, 1461507212517223320126132556323492596040124635554, 1461507212538490968058691210289954634908811958690, 1461507212538490968058691210289955760813013768610, 265783407324242938773039640263546547133703329360509909641755786425355008152613606406237356812816098820, 265783407324362844184193204125043794662950744818347116577504638291459782556365898687355549105904628484, 265783407324243882910135335858843465576363722242392133121732714641194875491539740711175966541475951364, 265783407324241994635944827399178019671854821849518172517974168010919998030940265987597832082472252164, 265783407324249547732709485387369760455655866132623937574828940709022461960559211753913950557519950596, 578832948038112, 1978643219271028827039652706902412209779451621464568244660716055978833541857674148924344212311612208425239193748346556943445539155914132056381674044128579180399364411205761831, 578832948038112, 1461507212517223320126132556323492596040124635554, 562958681836000, 562958682032608, 562958681836000, 562958681770464, 562958681770464, 562958682032608, 562958682032608, 569693257632224, 569693257632224, 1461864025804187743912925615240996225645479508386, 567494167300576, 567494167497184, 567494167300576, 567494167497184, 3353732645091527436725600038865693512727313181452231875736022850169686985095853483560904282352800840935979156108389765710308390809756894672201877916549404656297022886523274203108032826499281575916942231747982194449921607061972339800169961163193384677373486465399810096883417263163621820878034766086132829034448225908681341000538670066465701599409612424106011472693475586506400106, 567494167497184, 265783407324302419410068246377955467031276160309536161039414174978362092424124054535326700515155243780, 1463202075638944315086011210762066517183033285026, 1463202075638944315086011210762066534775286438306, 1461507212538490968058691210289953509004610148770, 1461507212538490968058710553103067413440418060706, 1461507212538490968058691210289955760813013768610, 1461507212538490968058710553103067483809430673826, 1461507212538490968058691210289953509004610148770, 1978643219271028827039652706902412209779452952346022042391819412512510483923962356302162645978350401004329440653510075937172281436109475826838719129577014245587471469373963047, 1461507212538490968058691210289954634908811958690, 1978658307749707751796438916887541024649191540362536754725033846437653343697702333817287663292580878064348489530245954232264070868754488920558704268072452164099925238527026342, 1461507212538490968058691210289955760813013768610, 1978658307749707751796438916887541024649191540362536754725033846437653343697702333817287663292580878064348489530245954232264070868754488920558704268072452164099925238527026342, 265783407324362844184192764476958247361541304749998463757937580792113602115396650051397723149385806596, 1461596415859567460007506688489434447501459495330, 1461596415859567460007506688489434465093712648610, 1461507212538490968058691210289953509004610148770, 1461507212538490968058710553103067413440418060706, 1461507212538490968058691210289955760813013768610, 1461507212538490968058710553103067483809430673826, 1461507212538490968058691210289953509004610148770, 1978643219271028827039652706902412209779454371952904936457050914354493132484684682516578368963480486019220066289750713350415223136066503005432674677622411579404308176769268519, 1461507212538490968058691210289954634908811958690, 1978658307749707751796438916887541024649191540362536754725033846437653343697702333817287663292580878064348489530245954232264070868754488920558704268072452164099925238527026342, 1461507212538490968058691210289955760813013768610, 1978658307749707751796438916887541024649191540362536754725033846437653343697702333817287663292580878064348489530245954232264070868754488920558704268072452164099925238527026342] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_2 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨0, 1, false⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [1461518373842650967241332670722679759553269111074, 1462934477245304970522595223240816272568979855650, 1461518373885186263106449978655601585482307246370, 1461540674672920089594708822306796094957223452450, 1461551825088054650771396898098854262659200621858, 1461551830702713704966881545244535285292234480930, 1461551825258195834231866129830541566375353163042, 1461507223427516406064644594930621591868471810338, 1461685630069669384891653807603552275082926659874, 566291475827168, 576565037894112, 566291475827168, 1461641034675028755386357907626299953855861923106, 569624370547168, 578695341738464, 569624370547168, 562958581107168, 576290159987168, 562958581107168, 576290159987168, 572029552298464, 265783407324241994635944827399191122205935057057551891447233620564717662909825269047966772014696577476, 572029552298464, 265783407324241994635944827399191122205935057057551891447233620564717662909825269047966772014696577476, 1461685630750234118733530734530301489947536824610, 265783407324249547732710570768601939883248298003474595481841435371851432523759660664354625158056719108, 1461507223491402346116243999579493823662542330146, 1461529524406991291082889738869737975496592891682, 1461518374204533210499438802970518338936241166626, 1461507212517223320126134974110568221057670486434, 1461685630049730888895844055816231079393709037858, 1461507212517223320126134974110568221057670486434, 1461685630730295627808323383655897900245132024098, 265783407324241994635944827399191122205935057057551891447233620564717662909825269047966772014696577476, 265783407324241994635944827399191122205935057057551891447233620564717662909825269047966772014696577476, 572888545757664, 576565037763040, 572888545757664, 1462220836469914540363282687041713360083662986146, 574022417123808, 574297295030752, 574022417123808, 572029552298464, 576290159856096, 572029552298464, 576290159856096, 572029552298464, 1462220836384843947999222771061755007477369330082, 572029552298464, 1462934471120232750539421159481150014555350407586] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_3 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨0, 1, true⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [1461518373842650967241332670718068073534841723170, 1461540674630384793729591514378485919862240616226, 1461507223427516406064643385995578605185262459170, 1461507223427516406064643385995578675554275072290, 1461507223427516406064643385995578675554543507746, 564092452506080, 1461685619170010127990042839705685175807610231202, 564092452506080, 562958547552736, 565226290350560, 565226290350560, 562958547552736, 567494167366112, 562958547552736, 567494167366112, 1461507212538490968058691210216166532709771942306, 1461507212538490968058691210216166532709771942306, 568490499115488, 1461685619170010127990042839705685175807610231202, 568490499115488, 562958547683808, 565226357524960, 565226357524960, 562958547683808, 567494167366112, 562958547683808, 567494167366112, 1461507212538490968058691210216166814185822394786, 1461507212538490968058691210216166814185822394786, 566291542936032, 566291542936032, 562958547552736, 565226357590496, 1461507217961741231425967178967040186548080384418, 565226357590496, 562958547552736, 562958547552736, 265751093741071738178132872471021511064997493101851605982191009402853902979100509478500697268880767653, 1461507217972375055392246505950270643030323141026, 265751220461005753993843546882538582735822377511913078346522961221224406896978481252433931402483270853, 568490499115488, 568490499115488, 562958547683808, 565226357524960, 1461507217961741231425967178967040749500181289378, 565226357524960, 562958547683808, 567494167366112, 562958547683808, 567494167366112, 265751220461005753993843107234456311067884185503205463109997870330398532568804316047504691350892198085, 265751093741071738178132656081724620256715680707404176621796880237148989971857232210851222086175947429, 265751220461003865719680825556137805394395776695895804046081831923814890152582110316470974927199026021, 265751093741071738178132872471021511064997493101851605982191340157314550131287000362272338966120069797, 265751220461005753993843546882538582735822377511913078346523126598457195086694723281673884658346427589] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_4 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨1, 0, false⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [1461551825088054650771400524885540911831374142754] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_5 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨1, 0, true⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_6 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨1, 1, false⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [1461551825258195834231869756635674959620967800098] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_7 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨1, 1, true⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [564092452506080, 1461685618521419553449333630390393181637761341730, 564092452506080, 564092452506080, 566291542903264, 265783407324362844182393285064071344997448100199366488436035438708364937915684058584164105264241521412, 566291542903264, 564092452506080, 568490633333216, 566291542936032, 568490633333216, 265783407324302419409169495987049466054298261467294283008294479877452969289598913866432007021057274628, 265792158919815370842847974982173362217030433835753474516002896805929923990249248951400926494215845476, 265783407324362844182393285064071344997448100199366488436035438708364930696017820632447449396358099716, 1461507212559841693057899071486357473607755536802, 1461685619180643951956322166688919854430609775010, 564092452506080, 265783407324362844182395044300442401445469809780828187844817082318026711676302218940095828561773146884, 564092452506080, 564092452506080, 566291542903264, 1461551814092763665892499866965510596817723628834, 566291542903264, 564092452506080, 568490633333216, 566291542936032, 568490633333216, 1461507212602366604646211959825686771216784857378, 265783407324302419409171255223420522502319971048755982417076123487114752676438784405330620846723824580, 1461507212538490968058691210216171036326579181986, 565226357918176, 565226357918176, 562958548077024, 567494167759328, 562958548077024, 567494167759328, 1461507212538490968058691210216171036326579181986, 1461507212538490968058691210216171036326579181986] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_8 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨2, 0, false⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [564092553660896, 1461685619180643951956322166688919854430609775010, 564092553660896, 1461685619180643951956322166688919854430609775010, 565226425027040, 572029653223904, 565226425027040, 562958682294752, 567494167759328, 562958682294752, 567494167759328, 572029653223904, 1461507212538490968058710553103071846688212687266, 572029653223904, 1461507212538490968058710553103071846688212687266] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_9 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨2, 0, true⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [1461596415540635815550474885798286786233348692386, 1461596415583254188482241401030322450477763041698, 265751093741069849903969409567033271647334719095886582017581578503775337491395621436236552768149024261, 569624538647008, 1461507217961741231425967178967044690164887624098, 569624538647008, 562958548077024, 562958548077024, 265751093741069849903969628961740391342959187078545081150803747004652403265579087214258216081945129957, 1461507217972375055392246505950275146647130380706, 265751093741069849903969628961737115709463533647357212523280467668802987759557554481726091064975684581] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_10 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨2, 1, false⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [564092553660896, 569761910000096, 576565138557408, 569761910000096, 265750967021375644907075279929670662110849529732320726621173063550942894242923662679636518565393609476, 567494167300576, 567494167497184, 567494167300576, 576565138557408, 576565138295264, 576565138557408, 576565138295264, 567494167497184, 265751220461005753993843108146798874402623703058518165343249149513027467068433750897160765969518224005, 567494167497184, 564092553660896, 568628038633952, 322300464588234307642837690426004949063595549388835510281272515530611924355467927806123541693793332647083941145706533320503971295070545974783635242571924250386186455668722573790363327674288008161466879881359166736279162141139460874478022297493419919143023370375560832737240753233434228960723807569750926466954097152047835365846330664611512172209401647600435421293512016217075317970424640801218387656936968360189991615823040438941521490175594014452794800499458456184552627749782451624866429955130807786110898950603970106913297953947160374214400426385751087529910903955497480441692023121254090201127961600957561237244571845741970003005750720365502544035867353307904471235810312933814811282210390016569259168840787520975240512370889555266155163694194207693200736655341668527262610791894790101212314778330658130610376194042382085270448, 568628038633952, 567494167366112, 567494167300576, 567494167300576, 567494167366112, 567494167366112, 567494167366112, 565226425027040, 572029653223904, 565226425027040, 562958682294752, 567494167759328, 562958682294752, 567494167759328, 572029653223904, 572029653223904] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_11 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨2, 1, true⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_12 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨3, 0, false⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_13 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨3, 0, true⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [265783407324242938773039641980921894098292897715475085913011613050441373470331082920075674725361396068, 265799627475796019048684252815166809114430771711472694533498106294669395020026431599152152251004565956, 265783660764111914541556245033782234717557007622065650297984523127032304682238308793560386326667409860, 265783407324241994635944827399178019671854821849518178067113197241598190492564410297371637474587260516, 265751093741069849903969464140660832427277771977904772760599977763409104655856402008696054690551764805, 265783407324241994635944827399191122205935057060458397334723547263649613253985463454871634341406128580, 265799627475796019048683373518995714511611891574775388894363991295977034138087934327236500337966922180, 265783407324241994635944827399191122205935057060458397334723547263649613253985463454871634341406128580] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_14 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨3, 1, false⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_15 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨3, 1, true⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [265783407324242112653080909837740563839032958308366308039525271043771768754188663545223952493757806180, 265783407324242112653080909837740563839032958308366308039525271073895545047635941183138620975979116132, 265783407324243056790162531542069030697519674538554936249249050384683109287467889728994545195792214372, 265783407324242112653080909837740563839032958308366308039525271043771778375710105441679291878090159716, 265783407324242112653080909837740563839032958308366308039525271053707878126221501231815799230095898212, 1978643241384089911265521128967260404316730080471079489724047971369851729118757856275203614456771078500544753426361140209005531619460850630671091526044730916008339907885919015, 265783407324242112653080909837740563839032958308366308039525271063801703520032642411864739159384208996, 265783407324242112653080909837740563839032958308366308039525271043614062358632253459324603993291961956, 265783439004225616607010282506307048059130132517896671658143914630309834090147611682669323476925626820, 265783692444094474358377610672533225701499294598823275797057579626706321226632465869267452024959806660, 265801940114591807683601449563796137008929125693673972996876484633761909570862293507911885380139563460, 265783439004225498589875079793265989701819292989123093131928442212676211651687470103114410869504817604, 265783439004225498589875079793265989701819292989120251972745470937403223678972062475602979681053391300, 265783407324242938773039641980921894098292897715475085913011613040347548377339378010212389861357529444, 265783407324241994635944827399178019671854821849518178067113197241598190492564410297371637474587260516, 265783407324249547732709499126372536172372412972345308900902349024309261619988079327160862065050203748, 265751093741069849903969464113826842630956054013288442319810889933563162091174482523631528996134164293, 265783407324241994635944827399191122205935057060458397334723547263649613253985463454871634341406128580, 265783407324241994635944827399191122205935057060458397334723547263649613253985463454871634341406128580] = some [] := by
  decide +kernel

private theorem solve_1_1_1 (N : Machine4) (h11 : N 3 1 = none)
    (hAlive : ∀ q a, ¬ (q = 3 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
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

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_0 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨0, 0, false⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [1461518373821466315246093086704020968235328379170, 1461685630048484732896414223584895454089822902562, 1461529524236600876422781162496079118345119506210, 1461518373821466315245784809444039303096794388770, 1461507223406342138662812594450593872172150725026, 1461540674651735437599160961032767324519176118050, 1461507223406331754069095524721549834747215124770, 1461551825066869998775852663611507708145532181794, 1461507223406342138662812594967102706236018170274, 1461641028387946488189357269966419793835059092770, 1461518373821466315245784809444039303096794388770, 1461685630048484732896124080281381064457692682530, 1461596426387136261155388408693348035242178419106, 1461864035329518628633115851642971470928962173346, 1461507223406342138662812595557398516594723821986, 1462934471099048098544025623441467377514980612514, 1461551825066869998776157314080195471341259889954, 1462934471099048098544180366536673860408048654754, 1461596426727408243482909617248428071780424390946, 1461518373778941403974692848426360689443896072610, 1461685630048484732896414223584893483764985927970, 1461507223406342138663122080567220002400936958370, 1461864035329518628633386652059582798399645202850, 1462934476543555584685478712295407140486522116386] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_1 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨0, 0, true⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [265783407324249547739800995321093822958741341408831261663684138305536840721900898017781742209352282884] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_2 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨0, 1, false⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [1461518373821466315563005736761078318609504180514, 1462934477224120318844268289279214831625214925090, 1461518373864001611428123044694000144538542315810, 1461518373821466315562697459501096653470970190114, 1461507223406425215729461801749707710487594047906, 1461540674651735437916073611089824674893351919394, 1461507223406331754386008174778607185121390926114, 1461551825066869999092765313668565058519707983138, 1461507223406425215729461802266216544551461493154, 1461641028387946488506269920023477144209234894114, 1461507223491402346116242790653674209016321972514, 1461529524917165610581280596176373545751588937506, 1461596426387219338222037615992461873557621741986, 1461529524151623746352642023167995038464048405410, 1461507223406425215729461802856512354910167144866, 1461551825066869999093069964137252821715435691298, 1461596432171926114534529405459497546301691697442, 1462934476543555585002236619331046110162374924578, 1461551830681529053288246334027563865228362947874, 1461685635493002603948037638587256789860315339042, 1461507228850849625121023590782896714396977895714, 1461685635493002603948037638605703533934024890658, 1461551831021811420209188424268397316548192148770, 1462934476543555585002101219048953461336102181154, 1463112877060719420595662045462193653191508269474, 1462934471099131175610558773419174101860809218466, 1461507228850849625121100962035352050681338960162, 1461551825237011182553539195868940125431588232482, 1461529524236600876739385535293154821172947361570, 265792293559615089754113176621335735692354892860205248755143275971388062812410069327887704234071112644, 1461507223491402346116243999579493823645496678690, 1461507223491402346116242790644450836979467196706, 1461551825151940590822999929534408710377784253730, 1461551825322081774283469161284542758167646346530, 1461507223491402346116242790653674209016321972514, 1461529524236600876739403669249624330886978772770, 1461596426387219338222037615992461873557219088802, 1461518373864001611427832901464274965408877943074, 1461685630048484733213326873641950834139161729314, 1461551825407152366014008427600627429164920642850, 1461685630729049467055203800568700049003771894050, 1461507223406331754386317660969020150924706879778, 1462934471099131175610829573835785446923678292386] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_3 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨0, 1, true⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [1461518373821466315245784809444039303096794388770, 265783914203985611002642813885630180276479229426058846874972573576253328568931316488046530039673729796, 1461540674609200142367868953209348478135690108706, 1461518373821466315245784809444039303096794388770, 1461551825066869998775849036820213806202725899554, 1463023679885899722031233695338350604028384155938, 1461596426727408243482601339988446406641890400546, 1461518373821466315245784809444039303096794388770, 1461685630048484732896105946324911818626451937570, 1461507223406342138662813803307238337262402967970, 1461864035329435551883341817557544645319843690914, 265783407324362844189595599840509845977144286023855915239384577037011155270768592648208364579991008004, 1461785982763848690329395302019493573243138251042, 1978643329836334248168994817601263008525397925647442521471101678196673110030546013103703581178673481115450937312680666126869110230004431957536495279005744007927180637793565479, 1461852885041979579648495631689241637610874511138, 1461507223406259061596163387151480033856707402146, 1461685630049730888895862189768088691965095352610, 265783407324241994643148021686466088090844560892969491012327444212024338443173243614453235008149861124, 1461685630049730888895862189768088691965363788066, 1461507223406259061596163387151480033856707402146, 1461507223406259061596163387151480033856707402146, 1461518373821466315879610109562765689863573379362, 265783407324241994643148021686452998352207954078695520169689025586035637853954714709908945477071745796, 1461540674609200142367868953213960164154117496610, 1461540674651901591732459375630995001150062763810, 1461551825066953076159410894180996680910772411682, 1463068281376296783911342066893622217149430930722, 1461641028217805305362709711543718090131681352994, 1461540674651901591732459375630994948373504630562, 1461685630048650887029404360927751181275765971234, 1461596426387219338222030362409874069672009177506, 1461864035329435552200255676545033296341621586338, 1461518373821466315245784809444039303096794388770, 1461540674609200142367868953218571850172544884514, 1461507223406248677002446317422435996431771801890, 1461507223406248677002446317422436066800784415010, 1461507223406248677002446317422436066801052850466, 1461507223406248677002446317422435996431771801890, 1461507223406248677002446317422436277907822254370, 1461507223406259061596163387077693057561869195682, 1461507223406248677002446317422436277908895996194, 265783407324242938780229643390794554949331658457094226281358242259678686245963385547125664264541709828, 265783407324241994643148021686466088090844560892969491012327444363431724464270670326932566545856148228, 265783407324245771191474508503779955524792951149468432088450636430399719781395440653676809676783025924, 265783407324241994643148021686466088090844560892969491012327444201930522976403391769120008721794282244, 265783407324249547739800995321093822958741341405967373164573828663915829132883341993165253063773205252, 480481192508393822119689285094570129192493518869440198421762207427789362600171262044915311705782300566668111756837058050632768340470473479540306029620204561962360169218081079422262497679032183666359029859914125276951134132638838198029491516959995286419177732106082760, 1978643329836334248168994818000846822965844931264292255342463893081737461297248817457818282279636635750923796796704871195154506459355130341084212749188503479865332450217082023, 1978643683645311582053294250377614691157507250443020721544175389892123702072568687773229888016017367626378872981235030510765792690593784252539038832095909364635992994431884071, 1461507223406259061596163387077693057561869195682, 1461507223406259061596163387077693127930881808802, 1461507223406259061596163387077693198299894421922, 1461507223406259061596163387077693057561869195682, 1461507223406259061596163387077693339037919648162, 1461507223406259061596163387077693057561869195682, 1461507223406259061596163387077693620513970100642, 1461518373778941413798714199778522719973035514274, 3353732644310675729778946154946588189504491054901057860476432922163575283150134542306498841090548892140237452654932625986318997239535337771673766043163300463631759586286869772642119478889950747363647500421851562437116834680323136093341574375422577067249523565394168706835266620319615079235084782280916297948078444476600865599127559914089402174460555826666704058992105678004082474, 1461529524151623755860021524879715549687309179810, 1461507223406259071737406874677329890260909332898, 1461864035332094017699241277915499948532430846370, 1461864035332094017699241277915500018901443459490, 1461507223406259071737406874677329890260909332898, 1461864035332094017699241277915500159639468685730, 1461507223406259071737406874677330453210862754210, 1461518373778941403974384572342354472996904671650, 1978643329836334255033792478131456537947745730345685472652246847570150799487128076283474841753918954140134708051094018794947332039299547176078201831764414391486580914375023783, 1461529524151623746352605756426424267714528844706, 1461507223406259061596163388258284678279280499106, 1461507223406259061596163388258284819017305725346, 265752994540108411252271842382692025685938813880330300908492348348139586933728460174448019999258082885, 1461507223406259061596163388258284959755330951586, 1461507223406259061596163388258284678279280499106, 1461507223406259061596163388258285241231381404066] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_4 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨1, 0, false⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [1461518373821715546445732431341385304067678443810, 1461685629368179614848201987103942422696060557730, 1461529524236850107622420507138055140195829849890, 1461518373821715546445732431341380818043124357410, 1978643683645311575188496590247004976175629165071761741899287841671843864629218848511914726306790428897033722753338435334445976133368450908031567207287113840704616231211088679, 1461540674651984668799108582934720490299494276898, 1461507223406580985269043146618891349693545093410, 1461507223406580985269043146618891420062557706530, 1461507223406580985269043146618891420062826141986, 1461507223406580985269043146618891349693813528866, 1461551825067119229975800285508849434198899989794, 1461551824896988431109048123432419191612307971490, 1461551825067119229975800285508849434199973731618, 1461551825067119229975800285508853656339656776994, 1462934476543804815885271591097545550248094505250, 1461596426727657474682552588695533000852262394146, 1461551825067119229975800285508853656339656776994, 1461685630048733964096071702178727065427570104610, 1461507223406591369862779559087266748507245025698, 1461864035329767859833063473540316908947812432290, 1462934476543804815885194219845090213980913309986] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_5 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨1, 0, true⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_6 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨1, 1, false⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [1461518373821715547713383031569614705564381649186, 1461596427408222209792084951627572565999484967202, 1462934477224369550994799118326308891095842461986, 1461551825917825148545797044487748810759841291554, 1461507223406923678129357045544390740380253985186, 1461685630048733965363722302406952033676478683426, 1461507224087145720378570673847659194157026548002, 1461685630048733965363722302406952033676747118882, 1461685630048733965363722302406952104045491296546, 1462934477224369550994799118326306920762415552802, 1462934471099629638010570074018751189534565767586, 1462934471099629638010570074018751471003100027298, 1461507224087145720378570675028249688974531008802, 1461518373864250843578500339507148217511780063522, 1461518373821715547713383031569610219539827562786, 265783407324243882917338524953741405873021953004597582095135627511979370959738368330716821008150634180, 1461518373906786139443617647444677243434691500322, 1461507223406580986536693746847120751190248298786, 1461507223406580986536693746847120821559260911906, 1461507223406580986536693746847120821559529347362, 1461507223406580986536693746847120751190785169698, 1461596426727657475950208024627036638724907637026, 1461596426387717800621932859787145044187770034594, 1461551825407401598164389349237346931275864251682, 1461551825067119231243450885737083057836359982370, 1461507228851098857271709162851414784074052573474, 1461551825237260414703920117487217105625953639714, 1461507223746863353457632210347393350386242853154, 1461685630048733965363722302406956466924273309986, 1461685630048733965363722303587548087641684613410, 1461685630729298699205599229407492658082647939362, 1461507223406580986536693748027716875524466841890, 1462934471099629638010570074535264245731673807266] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_7 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨1, 1, true⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [265783407324241994643148021686466088090844560895878838059042679393418534749373607413174854837938107140] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_8 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨2, 0, false⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [1461685630049730888896152333071605280637392558370] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_9 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨2, 0, true⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [1461507223406259061596472873268110526964812519842] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_10 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨2, 1, false⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [1461685630730295627808631660911272101487741802786] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_11 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨2, 1, true⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_12 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨3, 0, false⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_13 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨3, 0, true⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_14 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨3, 1, false⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_15 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨3, 1, true⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

private theorem solve_1_1_2 (N : Machine4) (h11 : N 3 1 = none)
    (hAlive : ∀ q a, ¬ (q = 3 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    (hm : Matches N (baseTable 1 1 2)) : CertProp N := by
  refine branch_one_sound (tb := baseTable 1 1 2) (q1 := 2) (a1 := 1) (rem1 := 103) (cur1 := ⟨2, [0, 1], 1, [1]⟩) (step1 := 4) rfl ?_ N h11 hAlive h107 hm
  intro m hmem N h11 hAlive h107 hm' hsum1 hrun1
  simp only [moves16, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkTree_sound tv_1_1_2_0 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_2_1 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_2_2 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_2_3 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_2_4 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_2_5 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_2_6 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_2_7 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_2_8 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_2_9 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_2_10 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_2_11 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_2_12 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_2_13 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_2_14 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_2_15 N h11 hAlive h107 hm' hsum1 hrun1

set_option maxHeartbeats 0 in
private theorem tv_1_1_3 : checkTree 4 (baseTable 1 1 3) 107 startPos 0 [] = some [] := by
  decide +kernel

end OMA.BB4HoleS3A0

open Turing Turing.BusyBeaver OMA.BB4HoleS3A0 in
theorem OMA.solution :
    OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H3_R1_H1_R1_H1_R1_H4_R1.H1 := by
  intro b c q u v N h107
  have h11 : N 3 1 = none := rfl
  have hAlive : ∀ r s, ¬ (r = 3 ∧ s = 1) →
      ∃ r' w d, N r s = some (some r', Stmt.write w d) := by
    intro r s hne
    fin_cases s
    · cases hs : (v r).2 with
      | write w d => exact ⟨(v r).1, w, d, by simp [N, hs]⟩
    · have hr : r ≠ 3 := fun h => hne ⟨h, rfl⟩
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
  · exact solve_0_1_1 N h11 hAlive h107 hm
  · exact checkTree_sound tv_0_1_2 N h11 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact checkTree_sound tv_0_1_3 N h11 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact solve_1_0_0 N h11 hAlive h107 hm
  · exact checkTree_sound tv_1_0_1 N h11 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact checkTree_sound tv_1_0_2 N h11 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact checkTree_sound tv_1_0_3 N h11 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact solve_1_1_0 N h11 hAlive h107 hm
  · exact solve_1_1_1 N h11 hAlive h107 hm
  · exact solve_1_1_2 N h11 hAlive h107 hm
  · exact checkTree_sound tv_1_1_3 N h11 hAlive h107 hm (Nat.zero_add 107) rfl
