import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H3_R1_H1_R1_H1_R1_H2_R1

/-!
FAR nonhalting certificates for holeA 0 (write-0 transition at state 1 blank, hole at (1, 1)).
Every machine in this branch either halts at the missing (1, 1) entry within
107 steps or hits a leaf certified by a finite automaton invariant.
-/

namespace OMA.BB4HoleA0

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
      if Nat.beq cur.state.val 1 && Nat.beq cur.head.val 1 then .halted11
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
    (h11 : N 1 1 = none)
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    {rem : ℕ} {cur : Position} {step : ℕ}
    (hsum : step + rem = 107)
    (hrun : N.multiStep (Machine.init []) step = some cur.view) :
    match stepLoop tb rem cur step with
    | .halted11 => False
    | .done => True
    | .missing q a rem' cur' step' =>
      tb.get q a = none ∧ cur'.state = q ∧ cur'.head = a ∧ ¬ (q = 1 ∧ a = 1) ∧
      step' + rem' = 107 ∧ N.multiStep (Machine.init []) step' = some cur'.view := by
  induction rem generalizing cur step with
  | zero => simp [stepLoop]
  | succ rem ih =>
    unfold stepLoop
    cases ht : tb.get cur.state cur.head with
    | none =>
      simp only []
      by_cases h0 : (Nat.beq cur.state.val 1 && Nat.beq cur.head.val 1) = true
      · rw [if_pos h0]
        simp only [Bool.and_eq_true] at h0
        have hs : cur.state = 1 := Fin.ext (Nat.beq_eq.mp h0.1)
        have ha : cur.head = 1 := Fin.ext (Nat.beq_eq.mp h0.2)
        have hnone : N.multiStep (Machine.init []) (step + 1) = none := by
          rw [Machine.multiStep_succ, hrun]
          simp [Machine.step, Position.view, hs, ha, h11]
        have hnone107 := Machine.multiStep_eq_none_mono hnone (by omega : step + 1 ≤ 107)
        obtain ⟨r0, T0, hr0⟩ := h107
        rw [hnone107] at hr0
        contradiction
      · rw [if_neg h0]
        have hne : ¬ (cur.state = 1 ∧ cur.head = 1) := by
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
    (h11 : N 1 1 = none)
    (hAlive : ∀ q a, ¬ (q = 1 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
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
      N 1 1 = none →
      (∀ q a, ¬ (q = 1 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d)) →
      (∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩) →
      Matches N (tb.set q1 a1 m) →
      step1 + rem1 = 107 →
      N.multiStep (Machine.init []) step1 = some cur1.view →
      CertProp N)
    (N : Machine4)
    (h11 : N 1 1 = none)
    (hAlive : ∀ q a, ¬ (q = 1 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
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
private theorem tv_0_0_3 : checkTree 4 (baseTable 0 0 3) 107 startPos 0 [51136422218208, 12845253756014580679348398458832883851408310755, 51136422218208, 84121771051488, 47099263715181964460818972740890008150495217123, 84121771051488, 266061430859474523585696293692852176158101581907293639967096377796995765407699722950918855787767298500, 282409062914737679354124532159989352247067330843150115967300782879916166577862828878990763139875394084, 267877834393662890902574256826906000056169375740195075443506923768977155333688181672444026952784181700, 46385726960117187922632912377470430283100604835, 267877834393662891017825365423305530987382444819041920914385015486212466998212745066267542033841682884, 46385726960439111595512520802941270723568601507, 46385726965101811921585350324300729209699977635, 46385726961114112722423399966836490068420479395, 282409062667177383456259804305160573558310008875690348699606260001169395104441423455094394772020165060, 46385726962432961195093495981673390294208350627, 46385726965101811921585350324300729209699977635, 46385726965101811921585350324300729209699977635, 398658888854809924785148197031100848465441315307720584974537413345552857176497276920577294205071030724, 46385726970418744187134617467586381398072641955, 150092468718048, 184115303551770369948286087058711806107543687651, 150092468718048, 184115652000903712395555452783325302867133243875, 282033864051168, 558887340512, 282033864051168, 558887340512] = some [] := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem tv_0_1_0 : checkTree 4 (baseTable 0 1 0) 107 startPos 0 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1 : checkTree 4 (baseTable 0 1 1) 107 startPos 0 [1464361707945243228186993978698668513875979164066, 1464361708604457242100265445272760583446399572386, 1464361707987861601118760493930704178120393513890, 1464361708073098346982293524394775506609222213026, 1464361710646151458837703428791761045997447305634, 1464361708243571838709359585322918163586879609250, 1464361707923892503187786117433093762596050327970, 1464361708584518822163491707179203477542194403746, 1464361707902624855255227463466632849631564814754, 1464361709266412789071755950891774105452824000930, 8563507998120570974640664310994613331584637346, 1464356481847362916548692909745233325582466439586, 14272520589551189620965427834746645813427985314, 25690545772412426913614954882250710777114680738, 1464357529240475998396445400369739239706300799394, 48526596138134901498914008977258840704488069538, 1464356132716325222599442079537064687541188319650, 94198696849641430732738379073717994655029680546, 2854495385422304395757246820781667885255776674, 185542898311202101078149679580846707304242903458, 2854495385422304395757246820781667885255776674, 368231301242298809743681775832526974964351392162, 1464361710630200722888284438316915361274083170722] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_2_0 : checkTree 3 ((baseTable 0 1 2).set 3 1 ⟨0, 0, false⟩) 102 ⟨3, [0, 0, 1], 1, []⟩ 5 [8563507998120651787366428860618958746413980066] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_2_1 : checkTree 3 ((baseTable 0 1 2).set 3 1 ⟨0, 0, true⟩) 102 ⟨3, [0, 0, 1], 1, []⟩ 5 [1464356481867301412544502661532554521288863930786] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_2_2 : checkTree 3 ((baseTable 0 1 2).set 3 1 ⟨0, 1, false⟩) 102 ⟨3, [0, 0, 1], 1, []⟩ 5 [14272520589551270116778542327313640854081526690] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_2_3 : checkTree 3 ((baseTable 0 1 2).set 3 1 ⟨0, 1, true⟩) 102 ⟨3, [0, 0, 1], 1, []⟩ 5 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_2_4 : checkTree 3 ((baseTable 0 1 2).set 3 1 ⟨1, 0, false⟩) 102 ⟨3, [0, 0, 1], 1, []⟩ 5 [25690545772412506775602769260703005069416619426] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_2_5 : checkTree 3 ((baseTable 0 1 2).set 3 1 ⟨1, 0, true⟩) 102 ⟨3, [0, 0, 1], 1, []⟩ 5 [1464357529256426795193093201799596196271418792354] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_2_6 : checkTree 3 ((baseTable 0 1 2).set 3 1 ⟨1, 1, false⟩) 102 ⟨3, [0, 0, 1], 1, []⟩ 5 [48526596138134980093251223127481733500086802850] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_2_7 : checkTree 3 ((baseTable 0 1 2).set 3 1 ⟨1, 1, true⟩) 102 ⟨3, [0, 0, 1], 1, []⟩ 5 [1464356154537015078471270256425075227418768202146, 1464534887828889581470598933584971618378719451554, 1464356176357704934343098433313085767296348085154, 1464356219999084646086754787089106847051507850658, 1465071153102779714286393533829309671997856307618, 1464356307281844069574067494641149006561827379618, 1464356132737592870532000733503525600505673832866, 1461680392423539241771708623552515522201748789666, 1461501637330913302837325507598165697268422826402, 1461859147516165180706091739506865347135074761122, 1461501637330913302837325507598165697268422826402, 1462216657701417058574857971415564997001726679458, 46028913680790661950901273964093354513348452771, 46028913686107594216450541107379006701729522083] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_2_8 : checkTree 3 ((baseTable 0 1 2).set 3 1 ⟨2, 0, false⟩) 102 ⟨3, [0, 0, 1], 1, []⟩ 5 [94198696869579926728548130861039190361427171746] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_2_9 : checkTree 3 ((baseTable 0 1 2).set 3 1 ⟨2, 0, true⟩) 102 ⟨3, [0, 0, 1], 1, []⟩ 5 [1464356132737592951661639148110207296294678976930] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_2_10 : checkTree 3 ((baseTable 0 1 2).set 3 1 ⟨2, 1, false⟩) 102 ⟨3, [0, 0, 1], 1, []⟩ 5 [185542898332469819999141946328154104084107917730] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_2_11 : checkTree 3 ((baseTable 0 1 2).set 3 1 ⟨2, 1, true⟩) 102 ⟨3, [0, 0, 1], 1, []⟩ 5 [1464356132737592951661639148110207296294678976930] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_2_12 : checkTree 3 ((baseTable 0 1 2).set 3 1 ⟨3, 0, false⟩) 102 ⟨3, [0, 0, 1], 1, []⟩ 5 [368231301258249606540329577262383931529469385122] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_2_13 : checkTree 3 ((baseTable 0 1 2).set 3 1 ⟨3, 0, true⟩) 102 ⟨3, [0, 0, 1], 1, []⟩ 5 [544301746522592, 435450095733216, 544301746522592, 508017862838752, 713623846446441640819025165721263483240077730, 508017862838752, 502404258418587140000126635109264865566317894050, 435450095471072, 508017863231968, 435450095471072, 43490740704, 290314560735712, 43490740704, 290314560735712, 43490740704, 435828052855264, 435553174620640, 15015034105146898560754720055322421160640974050449023118978878731421289985023664753877400115120783474308878681554849761829296110228995232176206899365645336097683192533101525999518548448760569246147696995514197852083756411976879610998582972755079045201789058326922761, 435553174620640, 15015034105146898560754720055322421160640974050449023118978878731421289985023664753877400115120783474308878681554849761829296110228995232176206899366232471743376650840073896148715882705604489886665786077827446368570239825158535029017562401649601083305623556326922761, 435828052593120, 435828052855264, 435828052593120, 435828052855264, 435828052724192, 435828052855264, 435828052724192, 435828052855264, 544301746522592, 435450095733216, 544301746522592, 508017862838752, 508017862838752, 435450095471072, 508017863231968, 435450095471072, 43490740704, 290314560735712, 43490740704, 290314560735712, 43490740704, 365733616413944095952457945908543001593746302371, 365733616414276404219054699547134628941196691875, 435553175079392, 9131526624, 435553175079392, 9131526624, 284009433568, 9131526624, 284009433568, 9131526624] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_2_14 : checkTree 3 ((baseTable 0 1 2).set 3 1 ⟨3, 1, false⟩) 102 ⟨3, [0, 0, 1], 1, []⟩ 5 [291414072134112, 294712607377888, 291414072134112, 292513583794656, 731467235549565587805569548902640573264686012834, 292513583794656, 730764762075811873176611173777052149873019771298, 294712607115744, 292513584056800, 294712607115744, 290314560735712, 290314560735712, 290314560735712, 290314560735712, 290314560735712, 132907923813682560075222912397671509287678051109115462533821751657214337202297824540127040998618428164, 291414072134112, 294712607377888, 291414072134112, 292513583794656, 292513583794656, 294712607115744, 292513584056800, 294712607115744, 290314560735712, 290314560735712, 290314560735712, 290314560735712, 290314560735712, 132907923813795856525017516917087532306105353431854633188633841789711495383181377651262275403644924676, 132907923813675006978569938763043774419781270596163038929180292745096031229770533935520153627204252420, 294815686724064, 290555079166432, 294815686724064, 290555079166432, 290555079166432, 290555079166432, 290555079166432, 290555079166432] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_2_15 : checkTree 3 ((baseTable 0 1 2).set 3 1 ⟨3, 1, true⟩) 102 ⟨3, [0, 0, 1], 1, []⟩ 5 [36327374490080, 97242770388601483596998864720120385715372579106, 36327374490080, 713623846446441640819025165721263483240077730, 5720162964123345341272763506827522199241382306, 181462909454816, 93461700289882180992153048614721954, 181462909454816, 43490740704, 8839584025056, 43490740704, 8839584025056, 43490740704, 435828052855264, 145282104887776, 145282104887776, 435828052593120, 435828052855264, 435828052593120, 435828052855264, 145282105084384, 145282105084384, 145282105084384, 435828052855264, 36327374490080, 713623846529518707468232464831724095741647266, 36327374490080, 181462909454816, 181462909454816, 43490740704, 8839584025056, 43490740704, 8839584025056, 43490740704, 731110419543244733667325500070005797030323561891, 731110419543577041933922253708597424377773951395, 145282105346528, 9131526624, 145282105346528, 9131526624, 284009433568, 9131526624, 284009433568, 9131526624] = some [] := by
  decide +kernel

private theorem solve_0_1_2 (N : Machine4) (h11 : N 1 1 = none)
    (hAlive : ∀ q a, ¬ (q = 1 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    (hm : Matches N (baseTable 0 1 2)) : CertProp N := by
  refine branch_one_sound (tb := baseTable 0 1 2) (q1 := 3) (a1 := 1) (rem1 := 102) (cur1 := ⟨3, [0, 0, 1], 1, []⟩) (step1 := 5) rfl ?_ N h11 hAlive h107 hm
  intro m hmem N h11 hAlive h107 hm' hsum1 hrun1
  simp only [moves16, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkTree_sound tv_0_1_2_0 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_2_1 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_2_2 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_2_3 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_2_4 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_2_5 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_2_6 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_2_7 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_2_8 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_2_9 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_2_10 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_2_11 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_2_12 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_2_13 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_2_14 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_2_15 N h11 hAlive h107 hm' hsum1 hrun1

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_0 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨0, 0, false⟩) 101 ⟨3, [], 1, [1, 1, 1]⟩ 6 [36842770565600, 5898569606276324168281976179754686856228264226, 5887419196375602978686757493115391921439660322, 65387486926510390252780421548766828525150504259362249801391157745124326068686485196956867976920004, 5887421977120585372537966346633019930449041826, 5887418531761600015626420128294255931893504418, 5887419192387918991332009874403970740598626594, 5887419196375602978686757493115391921439660322, 6244232476693881715952836133182380240727472418, 5898569607605557234669292965576099903321430306, 5887421961169849423118975871787335207084906914, 68935648002001635180547072464930464115374436154139496809833149575177789159442712165579484835950724, 5887424688745717056175950722072098649416980898, 5887419192387918991332009874403970740598626594, 36842770565600, 6422639181320647333286707613441575483100649890, 5720162964123345341272763506827522199241382306, 5887419217643250911245411459579682723084655010, 6422639181320586486057896658430303641346791842, 5709012570173355030494134382116446738492447138, 5887419192387918991332009874407348577758108066, 5709012548905707097935480415655533774006933922, 6065825835870130884728539333159163381509290402, 5720162964123345341272763506827522199241382306, 6422639165369850536638906183584618917982656930, 5709012549570321095827938352107437304147106210, 7136265739298698110225024018591878132987386274, 5709012548905707097935480415655533774006933922, 40725421099488, 49899471243744, 40725421099488, 5887421977120585372537966346631735700867799458, 5887418531761600015626420128293411506963372450, 39728988686816, 5887419196375602978686757493114547496509528354, 39728988686816, 40862860052960, 49762032290272, 324331753058750176648982604028460120541797002397093526387420387451137022963485357964252654596991524, 49762032290272, 39728988686816, 5709012570173436160132548988798142527497591202, 40725421099488, 49899471243744, 40725421099488, 6065825833211745881592320368193810814238488866, 39728988686816, 6065824472082197068200051908013966910576155042, 39728988686816, 40862860052960, 49762032290272, 49762032290272, 39728988686816, 5720162985307997336820624780856292637288716706, 45638863817184, 5709012570173436160132548988793779665358576034, 45638863817184, 35743258905056] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_1 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨0, 0, true⟩) 101 ⟨3, [], 1, [1, 1, 1]⟩ 6 [69576771264067051486460860325573923689641567988438063569587404739639814558918284919425244846000608792580723975970738530114704060200521165381295218057347754209890450115648550, 249081520052720181906554017230291912600992619317579043318502842440517097998272499832975562620956506926226320165603348225400320547915487886866145239336305677921693138418471, 3275129437900838123297710636003927883947721195920240679690521173570622056694851853241263372269022216207576595285044710713778874013679737080914890812590294188580881793862281058492292681571057485168156368323443310871382564342811325650126053160865389114633046354662005403101359931491082348735754029056302570038429983140188579774533781363985251668503770887602220372123474718032170, 69576771379183008204334897770738577755056628802266438584137696589105397773123679014856940727789062348264031283294339830949919964165786876380481340334551738662909370360912934, 436549607098848, 91355351155017886440577538580494176088512027042, 436549607098848, 365565314839250458295894965320649610697116768674, 471733979318752, 16609435438820989630514426294703106679760135481416613777315265580047267025150668928705862665731125380, 471733979318752, 2044355447372464353901936861804625727565070216897340098632552027490021119470980518173608777392243329952042070878794786768339269356373909641591388130530203140521861501644960806, 435828052855264, 145282104887776, 145282104887776, 435828052593120, 435828052855264, 435828052593120, 435828052855264, 145282105084384, 145282105084384, 145282105084384, 435828052855264, 61847696448826812497366101547471098064380276173161016082546899770254315108168729536721887736237354703960028766728517834516273752472950962045841327977230814188128493518937126, 120120269264371590396674897914118274271992521864479825744152131764510508306026727289166223887538091697821009318587081199820650104121003973220813319231952340922486834883808352688613022136344361356257055327925175027980635175443936931271160339418765672409219332080593160, 436549607098848, 436549607098848, 365398059292796774804363405423583642676553080610, 471733979318752, 121997148471572765454167687337995588487320461762867201628321606612201166196681535216153076437183174543033147823383257565475445776787579534036253684458612317212496766614456078332947179223816647709337050276036129425660772397012528912244062491041507242904928516080593160, 471733979318752, 472541914656516886946819141369378261600366505462375812279769547586017130064134526924415513893216627535596249646772076457345204756649792325668740721583488964699067249565363446112370728151226127205742439805322601409636416740668394276922152017768776466433076922761, 72990685981144898199112073762931061439241282463498591282292304797980448741135299019899559010673669, 282394870282022164641411108182438834331598840835597544049986774028933185791131932515213885744335213092, 282392842763062805396738711853839345015064850478142829149329717590201148198975430089993746737338700324, 435553174948320, 145282104887776, 145282104887776, 435553174686176, 435553174948320, 435553174686176, 435553174948320, 145282105084384, 145282105084384, 145282105084384, 435553174948320, 435828052855264, 145282104887776, 145282104887776, 435828052593120, 435828052855264, 435828052593120, 435828052855264, 145282105084384, 145282105084384, 145282105084384, 435828052855264, 32078680625261880627239962284127814382435519284638166524612277998540471404998448037880260530368901123805007274581422323319831938979335554438633232975878018847742221769767, 137871292197242541952077247388050829783957693571081231719991538862604671553921566648148352784443237, 435690613901792, 154215636863456, 3201491998481280926669090456827455100323767876368674496560480327916803895690680021146036838125130155635577212587069668512417718349624094770814978255959258747178645675169922187142682251076128260226429221986215035063104429906620103474977246920519891655617819623851014499495367783990897923840423926426053112597603853834590184610203033361211574729464487697029554979210711208235, 154215636863456, 72990685981144898199109497699910614554316749120105396822491692015259416867067359190394495963276293, 435690613639648, 435690613901792, 435690613639648, 435690613901792, 435690613770720, 435690613901792, 435690613770720, 435690613901792, 282392842763062805396738711853839345015064850478142829149329717590201148198975430089993746737338700324] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_2 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨0, 1, false⟩) 101 ⟨3, [], 1, [1, 1, 1]⟩ 6 [36842770565600, 67931323650302547558180874794184867073854332236446615533873089039476573943511814144042369884686146966840696755143067115012594461496201286412855165061684377782901946333990, 36842770565600, 40725421099488, 49899471243744, 40725421099488, 11596434568551203701950079813326417808535346082, 11596431080656922479921225662066267685659892130, 39728988686816, 5887440974447085918748419149089423129675061538, 39728988686816, 40862860052960, 49762032290272, 133816252284506550180192558994927938338642981627186594076896941082631634756614010638801730082270532, 49762032290272, 39728988686816, 131804573452855020870133080797552756729573582661405012490571212665561161663983537594106342595490788, 291962731839624912023966605909717687357819272141004054333946258907837560715049928104671876670192068, 291962731839624912023526957820894752403915029510115777624022325157378799672656654622315665319950788, 45226546989536, 35193503091168, 45226546989536, 35468380998112, 310495522189437959678012707494375174078918858795915398511261779173921532811954074441178631798946244, 35468380998112, 35193503091168, 40725421099488, 49899471243744, 40725421099488, 11774837020977600662133272048468518878277818786, 39728988686816, 11774837020977519532494857441786823089272674722, 39728988686816, 40862860052960, 49762032290272, 49762032290272, 39728988686816, 36327374490080, 36327374490080, 291994411823128865951140604688240895053075701946574070264592218413647168411237747358127735708219844, 40828500347360, 11418025097801029562230285949423886353210300834, 40828500347360, 36327374490080, 36567892658656, 291994411823128865951147474176628582878615748452519165722398742823864534661121539673361197102954948, 36567892658656, 36327374490080, 45638863817184, 45638863817184, 35743258905056] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_3 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨0, 1, true⟩) 101 ⟨3, [], 1, [1, 1, 1]⟩ 6 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_4 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨1, 0, false⟩) 101 ⟨3, [], 1, [1, 1, 1]⟩ 6 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_5 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨1, 0, true⟩) 101 ⟨3, [], 1, [1, 1, 1]⟩ 6 [398675109006424366594140062068643631235359227541975554177834674265490359425994121906920023705671596484] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_6 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨1, 1, false⟩) 101 ⟨3, [], 1, [1, 1, 1]⟩ 6 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_7 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨1, 1, true⟩) 101 ⟨3, [], 1, [1, 1, 1]⟩ 6 [266042961429089948187858306269280749296130913452713595094112159478489647344630445957426123192945506756, 3872085448092286464180522962205367746727238634351489264051788871788227780593248716276434804157383273030895666313436276724549349092973751076202259144273555642151052671707943, 266059181580704279355785479115252165653953864922906424993657377556652183107164696568514452229481462212, 266042961429089948187858306269280749296130913452713595094112159478489656970852334847405067271575861700, 266044988948041636318855900501116250278211797798810817621116773372968536561790556918535362765287487940, 266043309908908373663925095079425206768242845836406238339342434348940583563306343085444475719942306244, 266044988948049189415621424046482656488057238637748287945340386516522166236685981273890180442736667076, 266042969349085824176340209680997585831793203620822709667272301951803724063036836713727093565213276612, 266059181580704279355785479115252165653953864922906424993657377556652173480942825573750757094102301124, 266061462539456139264447714734414546506211911142496840022388983184782358850513309223064194025469147588, 266042929749106326216793731317017053056452917767168738827655595629865363138443369412294892160480082372, 266042961429089948202264694843830690662532547087569450777971920943144061302696016381654062578077694404, 43292268188179395338646127877355719929490478731445440969345383590706631634903282346576565173948582726000335506070676273140830140950746409343458923864704564064725040776424716379305267474516902761635846370961398504586452695246913807498121604750632593002789036841642109255520977822658668033772622838567322683818136252156744069513106440910090240111764756094210804915103450450515943808449221623771537627629119666054342892527114601764561863586678843574092086087947571958364269449076745268898636248948060479372703503017926467145610963737532550726422161345308026938453989394994709759369505871710157236654660332363293872083228807181588847866453703591009654610478, 1978658366602701961295935088993641982629087197324410754539220149206332496553531181920927828111818621186525789373436366032284715572845299250248711452948096726171983853709569830, 266042961429089830185127733538434340565503712074461052804155926987776045465247520929258643616000539076, 266042929749106326231200119891566994422854551402024594511515357094519777096508939836522831545612270020, 47099353528739487864001065097885179675818363299, 47099353529051026943163452752371507294981065123, 47099353539041044128502770188001130790790400419, 47099353529736412663791552687251239461138237859, 47099353531044876542744427931103626865620814243, 47099353539041044128502770188001130790790400419, 47099353533724111862953503044715478602417736099, 47099353539041044128502770188001130790790400419] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_8 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨2, 0, false⟩) 101 ⟨3, [], 1, [1, 1, 1]⟩ 6 [141880490756576, 91355351878117916147571773440166342644628216098, 141880490756576, 91355354600376851515079481147166439201599150498, 91355351197553182305694846513420364879689177506, 146278537365984, 91355351155017886440577538580494176088512027042, 146278537365984, 146278537365984, 155074630519264, 16674244641324265049583409003448235636785714880498121999679963006611699194793969380975855884980376100, 155074630519264, 141880490756576, 91522607445756175892527830974557297178517199266, 141880490756576, 4152374699697205915595485341372377083414639446553014837019043504112553928264638224785734999466474436, 141880490756576, 146278537365984, 146278537365984, 146278537365984, 155074630519264, 91366505015511413008680206996278561849815883554, 155074630519264, 141880490756576, 92057828052779861427239598658850535269244885410, 91344200803603191994916217388709289436120111522, 145282105346528, 140746619881952, 145282105346528, 145282105346528, 154215637322208, 154353076275680, 154215637322208, 140746619881952] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_9 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨2, 0, true⟩) 101 ⟨3, [], 1, [1, 1, 1]⟩ 6 [184115306274018920761690655252432781739705803235] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_10 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨2, 1, false⟩) 101 ⟨3, [], 1, [1, 1, 1]⟩ 6 [141880490756576, 91355700327261643188558359935764352775276747042, 141880490756576, 182699556063266744785673296614281352924279896482, 182699551979878341734411735053786063738833492386, 146278537365984, 182699551937343045869294427120859874947656341922, 146278537365984, 146278537365984, 155074630519264, 155074630519264, 141880490756576, 154353076144608, 145282104887776, 16643903260873171642606067908711186653322539578072210186179789740160279967269385126023842848548747716, 145282104887776, 2815208608941454542145100114833047331147428300081729450200309017089283399406337031482191916083482791902173039837153284854765583291062843911370005852222429409807759937479589531499368941533871530981248998470487637473193938440997325344466420623160706784440726523718570718504992409161332717279696642140450069107069456406344782398514991262099900384077164443319592096349752348701753716033161477488457205912385010304613936869914414276860401713246465522867099825112579795463896231136999553083681832265361317876096079253714178699891468972449504924936623950399258703110514925885234246571372840840851605889140290982795784857843190262618920498154679840700224499258432046, 154353075882464, 154353076144608, 154353075882464, 154353076144608, 145282105084384, 145282105084384, 145282105084384, 154353076144608, 141880490756576, 16609467118804845791829911182318115869443557528810360232044470258352290765491538092628537989463962372, 141880490756576, 146278537365984, 146278537365984, 146278537365984, 155074630519264, 182710706478484383029010579705449963652545280930, 155074630519264, 141880490756576, 182699551979878422547137499603405923146221509026, 182710702395096060473562132637520578789466200994, 16643903260888277836137114999444408527383418221449510024140877563829451808006456664016100160555035076, 184115654702061072873778668053342127934658355683, 182688401564660784620712866569291830455077722530, 184115654702061072873778668053342127935732097507, 183045214851625198266301123660960811038907857314, 183045214851625198266301123660960811038907857314, 183045214851625198266301123660961936943109667234, 182688401564660784620712866569291267502976817570, 145282105346528, 140746619881952, 145282105346528, 145282105346528, 154215637322208, 154353076275680, 154215637322208, 140746619881952] = some [] := by
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

private theorem solve_0_1_3 (N : Machine4) (h11 : N 1 1 = none)
    (hAlive : ∀ q a, ¬ (q = 1 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
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
private theorem tv_1_0_0_3 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨0, 1, true⟩) 103 ⟨0, [0, 1], 1, []⟩ 4 [] = some [] := by
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
private theorem tv_1_0_0_7 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨1, 1, true⟩) 103 ⟨0, [0, 1], 1, []⟩ 4 [265783407324243882910219741637067900430355570708692959242186585925149191211336193145291056725803348740, 265783407324362844182504955463963724533629319785269477978235599646050540102974630262714875243460244228, 265783407324245771184382985689740598855632717266197095622815266676375805926693985247881156529312169732, 265783407324249547732709473365742152567318090094580196175451448561875414976624506155199168205233009412, 265783407324241994636057377309929793547935578800981192163359425710988231983904994714800835675725968132, 265783407324249547732709478517868270233747802871595235864900425134771078606188713256198210932019770116, 265783407324241994636057377309929793547886768057886825333739838612433369169853382798864148980702589700, 265783407324362844182504089906785783474061813755259322741682462121812848518772593973211960696438469380, 97320910292831125891930571122852099156404540589086495277273564647108550676869705317818081478914820, 291962731843401460462563685873434128089095737409202794737839590050252066671802726494433947664449284, 551485160578754156560878017186745124464104802261896805044530340512761597066208972639869600788591364, 2108619732968210639812963013785316944100754883305371016285695147422518004557118255931291723708445444, 11150417793027314723955711255612623761179043, 91355351200123379040299454637401798269714047395, 182699551982448538469016343177767497128858362275, 11150417793027314723955711255612623761179043, 365387953547104049623308730644288388833211337123, 730764756676415071931893505577312157843405703587, 265783407324249547732709581560390623562358074436973868769848883609397665558333540436095790789559530244, 265750998701117921836538196504826711816353518156512967409964036169722222339636906119481531000732918405, 265783407324241994636056937661834419345965962324427383216793149556261510803793730040173647453271307012, 265750982861126169859574169749590111374461935297371986807711930053303440997649688186694080895389961573] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_8 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨2, 0, false⟩) 103 ⟨0, [0, 1], 1, []⟩ 4 [576702979901920] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_9 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨2, 0, true⟩) 103 ⟨0, [0, 1], 1, []⟩ 4 [576187584154080, 576565541210592, 576187584154080, 576221943826912, 1461529513305647723295212656214929827049507395043, 576221943826912, 265750998701117921836537760190016058807971673363321172025973302636721979785696359934844654601151584069, 576290663303648, 576565541210592, 576290663303648, 7136260934139453139461667482173663497482705186, 435828052855264, 260029308588488899548219684127664386148717511741523925659473014387013090610180132970796847884088068, 5575866885135764634136650584780739026393506, 265750983232375682425704956206196734124532927331094434475847886042904461077821405109414053736874993861, 154078198237664, 435828052855264, 154078198237664, 13203270928864, 294953125546464, 435828052855264, 294953125546464, 13203270928864, 576428102257120, 1461529513315616952278358497989767269434469138915, 576428102257120, 1978643212130352852018904017765050920136867169950653788686607746565701118586303326976072862438787270457474568626904290274744411291619199258801852005182094551342098767638313767] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_10 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨2, 1, false⟩) 103 ⟨0, [0, 1], 1, []⟩ 4 [576702979901920] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_11 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨2, 1, true⟩) 103 ⟨0, [0, 1], 1, []⟩ 4 [97320910292831125892809652641678933856277322537676324756433325765394527062773237600739650366026500, 435450095733216, 435828052855264, 435450095733216, 5720162964367384224554847727046468269714711971, 5720162964699692491151601365638095617165101475, 435553174948320, 435828052855264, 435553174948320, 435828052855264, 435690613901792, 435828052855264, 435690613901792, 435828052855264, 291962731843401460462563685873434128284148042821457742787986472165973390010861281192417682105237252, 5575866968212831283343949698619054469716386, 92776675903406357070304452560950308549010954658, 5575867051289897932551248812457369913039266, 11429175513262706688849653260819324448411231651, 11429175513595014955446406899410951795861621155, 92776675894101761099810041450623659127048542626, 5575866885135764634136650584780739026393506, 184120528228612426553927660281213042378687945122, 5575866885135764634136650584780739026393506, 11429175518247330687802018010969138895521866147, 5575877519000295732670937156085115771722146, 11429175523564262953351285154254791083902935459, 551485160578754156560878017186745124658966440708939382666475710524752987537878418291227740181050116, 2108619732968210639812963013785316944294472519961139371338431444812129797824453047302896292810928900, 4184799162934116271782187645196888462124047959660274946058927254727264091180303602563033114469413636, 505818839976416, 435828052855264, 505818839976416, 4184799162934189110481942990836540818369180954132095788150565974152148530726441305889363883356009220, 4184799162934189110481948142962658484798893731147135477599542547047812160290648406888402435434558212, 435553174948320, 435828052855264, 435553174948320, 435828052855264, 435690613901792, 435828052855264, 435690613901792, 435828052855264, 153975118760416, 154353076144608, 153975118760416, 154078197975520, 154353076144608, 154078197975520, 154078197975520, 154215636928992, 154353076144608, 154215636928992, 154078197975520, 4441537251808, 435828052855264, 4441537251808, 154078197975520, 435828052855264, 154078197975520, 4407177513440, 4682055420384, 4682055420384, 4682055420384, 4407177513440, 33251311180757345145401223994533827996191171507552492951516852616432701622695948995518966272253702916, 33218880282637318031624155752624508800775898900211629981771547921575924059754008863883462019237288581, 285916514224608, 295090564499936, 285916514224608, 294815686592992, 295090564499936, 294815686592992, 286157032393184, 286157032393184, 295090564499936, 286157032393184, 286157032393184, 22458740063115559621676105332597258754466, 435828052855264, 44236894623122270490631194046545867610530, 730764756674088914080570984034732911958683591075, 730764756674421222347167508638550120128340599203, 154078197975520, 435828052855264, 154078197975520, 4407177513440, 286157032393184, 435828052855264, 286157032393184, 4407177513440] = some [] := by
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
private theorem tv_1_0_0_15 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨3, 1, true⟩) 103 ⟨0, [0, 1], 1, []⟩ 4 [435828052855264, 3469195032570890248758124643793516324010973961907721337652685541885507692006480768889031209279617668148433910590637964191706073148697622061790442544065134127285527111086464543120627770441396019051251727652684298703799721927066600620818431020376958967433693669416629968513979831088568826444116899227318692949489060619410780167417410810624542343848543460389418229966167683683181443687449101972619148094898404387887309771746589664646689014532408167125986917945542798472369892328523410506033694265450367532, 154353076144608, 435828052855264, 154353076144608, 435828052855264, 295090564499936, 435828052855264, 295090564499936, 435828052855264, 1978643683645312447017799426634646871738190371653920920544173638361888833053258514211085849885718588994147238545463749587701149033294836889009522129966507189067955933008387110, 1978658779495010881948298537256741888660612428790846856754736034761368632129079381907195170448094574984201724017114833097411503046244424286888196104603515941618422730955140902, 1978658779495010881948298537256741888660578402588360441496349445136819933881349169300907593998375722263291069453227444836209780313388327971679761749826773667974229391404150566, 265750982861126169859573953386707878483745990046261983824140301519549841190432266497989934899258861413, 435553174948320, 299847818018015821337318081736344973638949146546429470085144362657645410343595390814801096494160114484886004340891050231435968909325522932595059730022499928155771985583081670680863148696962058798582582404445253507627407063430551463892192815123945059096387099473807728706087724849333045397207592527164649980160616931171424401459876762325822692556306579127050036549102409642, 129769134362136116503998924207815394492913075563024830431293549630809373771226152522519377981613061, 483538935906084369585249006310148271516047256529882371568354279465219348161557134037809757696802900017736085962009133303550939781414020827991734882674237459866380237823014, 154078197975520, 435553174948320, 154078197975520, 154078197975520, 294815686592992, 435553174948320, 294815686592992, 154078197975520, 5709013229480825573143558254789474827346418082, 435828052855264, 11418025778376148037438363788562331006042937762, 966134611154937396483019560688312186177341101449093030734439020696015926751408549563677766554021982929134642696843852429914506708218619603559839641355674991516781178927911, 154353076144608, 435828052855264, 154353076144608, 435828052855264, 295090564499936, 435828052855264, 295090564499936, 435828052855264, 435553174948320, 299847436742768288791497489388624151041879987803762101325777226059586057329494790533898291649623149519121692014260726752905386886574001490651752115094884383638761403448154633295083215859514083891292823842818261793508831168978316225445655021261604971676116996257966259567802515344888515705868722641426352390377319268871216496186419995298884471782701020152515373988271443370, 154078197975520, 435553174948320, 154078197975520, 154078197975520, 294815686592992, 435553174948320, 294815686592992, 154078197975520, 435828052855264, 483538935906084369585242612969117224363913024304930618065614614799647947131879461286955434600338111693541841499516208333613001910280340433964593047728418208856630295813158, 154078197975520, 435828052855264, 154078197975520, 4407177513440, 286157032393184, 435828052855264, 286157032393184, 4407177513440, 1978658779495010881948298537256741888660589715080712619039406272196067941291203723489322920947785852036464590989373698087338173754129312860628594105172228110822236927646740262, 265750982861126169859574169776008096107321612162237197640458454826472593568686553168872419754621151077, 1978658779495010881948298537256741888660589715080712619039406291435328779654413619132173496165715065369111566411535766075797004408484284219974946857314541051457138824208953126, 265750982861126169859574169776004820473825958731049329012935171614594342353850335059782654054677227365] = some [] := by
  decide +kernel

private theorem solve_1_0_0 (N : Machine4) (h11 : N 1 1 = none)
    (hAlive : ∀ q a, ¬ (q = 1 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
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

set_option maxHeartbeats 0 in
private theorem tv_1_0_1 : checkTree 4 (baseTable 1 0 1) 107 startPos 0 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_2 : checkTree 4 (baseTable 1 0 2) 107 startPos 0 [565192467941856, 1461864025121151791382348477326858099428379591139, 565192467941856, 567425850935776, 1461864025121651226389023656289477498078922539491, 567425850935776, 265783407324241994643148021686466088090844560895878838059042679393418534749373607413174854837938107140, 571892616923616, 562959084947936, 571892616923616, 97320910292831133011591506862641312106802604250635985796320696830791990654985658342414945538487044, 1070530018041907093188824612657596006266234442878965232391186464114114478559606859240887474878362372, 431430006344160, 2108619732968211338522808879457007780322626919089736074698958137198824541093843082868877517926904580, 149680151398880, 149680151398880, 431430006082016, 431430006213088, 431430006082016, 431430006344160, 431430006213088, 431430006213088, 431430006213088, 431430006344160, 291962731843401467609483017779064342022744074115437843257369583582918960315203726632983498550869764, 5803769278303807927144167237212603206509566370, 5575186320401922757209723837817676377397666, 11512760049210724518026518414124439659737029026, 5575186320401922757209723835847351540423074, 5575186320401922757209723835565875489970594, 5575186320401922757209723836128827590875554, 5575186320401922757209723835565875489970594, 5575186320401922757209723837817683893590434, 551485160578754163764072304461711009373608637682354176780749546592929804832786358606262845325914884, 2108619732968210647016157301060282829010258718725828388021914353502686212323695641897672444121133828, 149680151857632, 9131526624, 149680151857632, 9131526624, 281758986144224, 9131526624, 281758986144224, 9131526624, 563233962854880, 1461864025131639926522527348878805181746420666851, 563233962854880, 265751980780636284726475874657056309611839796676833200885980282565267410378516828953741049368388570597] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3 : checkTree 4 (baseTable 1 0 3) 107 startPos 0 [51136422218208, 12845253755993649193642009381884802845974200803, 51136422218208, 84121771051488, 47099263715152108716743742955705732899067134435, 84121771051488, 265783407324243823925090659191875678213143966158779767598829906742445530519837212023373298334947291908, 265783407324362786104837665827003691538135736159753515492600036053459861043898474846393587838983811844, 265783407324245712213688429296782976243728048136481929884539370512106232307789747090805840444402368260, 265783407324249488848396973464714784903351611491196296574793493658020358536796020243867122831980704516, 265783407324241950386722320669075691206901806815683112941331464335419929045573759964697759839154287364, 265783407324249488963648087213240356728333385634938654212021977528198713490625465520294320882317472516, 265783407324241935634580420329945558912189141131492048795934943184680576725571661593957191729729975044, 265783407324362786104836800269815923578008053721538204129047679873841628720554422518221311026026197764, 398658888854809917409077246861530869467591308384273408647113751133273790493333495694141042732885555652, 265783407324241935627377226042657490493199402085131399902283520160409073529463277148678386174864341444, 265783407324241950386721881020980317004932190339129303994765188180693207865462495290070571616699626244, 265783407324241935627377226042657490493199402085131399902283520160409073529463277148678386174864341444, 150092468718048, 505818840041952, 184115303530643319966301664879636666853642863075, 505818840041952, 431086409091552, 92057827351270032050670929565772723998763259299, 431086409091552, 92057827351602989354375037836749780615416514979, 281621547190752, 9131526624, 281621547190752, 9131526624, 284009433568, 9131526624, 284009433568, 9131526624, 150092468718048, 50621025651168, 431052049222112, 50621025651168, 83606374517216, 730753606258705121763356141416311336581928622498, 83606374517216, 5798221995158262788312787304366736528567736738, 149577072249312, 505818839976416, 149577072249312, 43490740704, 281518467713504, 43490740704, 281518467713504, 43490740704, 431430006344160, 149680151398880, 149680151398880, 431430006082016, 431430006213088, 431430006082016, 431430006344160, 431430006213088, 431430006213088, 431430006213088, 431430006344160, 50621025651168, 431052049222112, 50621025651168, 83606374517216, 83606374517216, 149577072249312, 505818839976416, 149577072249312, 43490740704, 281518467713504, 43490740704, 281518467713504, 43490740704, 16625655466866657711775199725952888497956523414477107078827629260707361313859134864153038357968993125, 16625655466866657711775199725952888497956523414477107078827629260707361304458527690829681895453768549, 8320937871206159311423354899562764138051720454598169355052653822603438503290613199001885018500903237, 8320937871206159311423354899562764138051720454598169355052653822603443312288792023172650224806211909, 8320937871206159311423354899562764138051720454598169355052653822603440905439550817756828756190474565, 149680151857632, 9131526624, 149680151857632, 9131526624, 284009433568, 9131526624, 284009433568, 9131526624, 282033864051168, 558887340512, 282033864051168, 558887340512] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_0 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨0, 0, false⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [1461518373842650967241640947978049738673375713570] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_1 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨0, 0, true⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [1461696779740519264366108064517282704144594934050, 1461685629378470751024769817255180463379898734882, 265791533240010994859850449096519428268775036720933304623960112553316317258936230091097598759541357508, 265783407324242938780228765771728194406386301312932315243888221525514404757201580699207889934927270340, 265783407324362844189595599840509845977193049103117615733306021987311423090143840393133747641828717316, 265783407324243882917310387476056738037534025255240470976710585285274353497093253371732568174087052996, 265783407324241994643148021659632098294522848890332507266509604434288613439348701281951051818025036004, 1461685629369166155054275406144853813957936322850, 1978643212360697238219068824983734034857829971951121844981362403485396686422284420779290150439239411898187553383340046655900073870759790136853111380575041594502694500878138151, 45700556584217034532858933973679004577205665429046430297471300520237822026859018040421923462769326820449954632728547290234797880277163892391417914937044745256643565872166, 915222942288555477639389754598987248782808234402, 256986018011886358033644737920516732029287609700325293021402031251866906273793044238649266403520913914116847616721375450447497650580752327214005272036713720731587866158118, 183050102667553964271287849705366395778187180450, 498520534592069393526593600187544855742740896799442312448049330320790617134807150790377592353349694996940980519580042653374732013961006533028474372060257988695026347959334, 3880031408040983954877226851982195562198781235445008226138035073601917371126349607175036611086669503187496635357222984177932718906384019348274235572247438185361561657173030, 91879429558804871253891035972810023456987986338, 732538373664486156232808428969833962501653445026, 183045224379541785697475638766994253949107747234, 183045224379541785697475638766994253949107747234, 365399103964980153995087713136868075366663717283, 732537676766198702150835255978637942240356383138, 730775907099608108569221604096873583984272081315, 5898579816076564902437278123947617553046608162, 823703477721312468042306348959057936712448645410, 300864807204708041427208158211102261117651431241722274427495676444658923091393423376901052679288964, 5586075356143392788040551825255492960164258, 551548520539153111935397757158463943313205373806428647562055529359158178988962099466323478934988292, 2108873172832465729998029747946513194304968180034537243817977715228509941404757261620428431988031236, 91522618314853497465399004966117545934308022562, 10889056510737002656622257093402583669154, 183045224376883329705905807021186639828547058082, 10889046126143285586967000032272486275362, 732180864850997610578894585201203483788866263458, 3614035989260057646758262481843849714934428058654658619732538606720920613375239311495105720562763454489583342490295843727074307136143956564987314596647280304677663656960947421589929110882257419981974407143468357474864983672878271274097767849339487923695576765259857176268641461805757798968068895753776697970448152148281978897606302512947302014948376746711044015289154842955928496838549907115569553315753930056153025231459955086177646172501733171461624321755864212219425530078627197686629394542567601100, 5731313384481539343425514406969372545359413667, 11440325933376861807720319940742228724055933347, 343988952657704144478949170226801656795101084902419162864356895092109622159656534967483238400671755301835326400892044079098481234608549234533959610293044065271765830919460518768537515750339039656298936439308115287778988991613229319630635279653899310487046119430968093707562871304798500162032802679102313485991309526952399588383306524123234319006733818913406479128529636086654569574386202152808678970917572634662598760972242527123101576497981122850732620284728621609711918763869765349908588883576123170259816939754319981284086906660192690610697462780411874984068153811369471750393401660418902492125973170798918269434780569581691141784710941613955430767150, 973918178481333399043792504354160876791462631963566752450624134629032854195154672864770635205115438559372456284248622370287321555413039453280545229162689157338141716865830, 11440304155305378867658658284767353090890400163, 91366501617921598642287837855473899038964842915, 5731313384481539343425514406969372545359413667, 182710702400246758071004726395839597898109157795, 365399103964897076928438503476570995616397787555, 5731313384481539343425514406969372545359413667, 730775907094208099237023127293290852045633487267, 265783407324362844189595160192414471775223432626563806786739745832584701910032575718506559419374056196, 121002670248476751908144973998862801560225223207446273882160947630369514481362841303812306571588621636193542890651013377853605472100770795114018894008080648921943592624934, 5731313389798471608974781550255024733732077987, 60385241556628377032405210361962388068829117328462478430543549844774806165421766949451629125843312164528720342342682064160002757762780493169649321177530730313474636457766, 11440325938693794073269587084027880912428597667, 11440304160622311133207925428053005279263064483, 91366501623248915501554174654016612219995947427, 22322618974632084741637672457044188201091491, 182710702405574074930271063194382311079140262307, 365399103970214009193987770619856647804770451875, 5731313389798471608974781550255024733732077987, 730775907099525031502572394436576504234006151587] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_2 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨0, 1, false⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [1461518373885186263106758255910971564602413848866] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_3 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨0, 1, true⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_4 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨1, 0, false⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_5 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨1, 0, true⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [97320910291060875955413333562098117151477228926011156827187844611819392524623275379948651565757188, 265783403364243998562348337395282773912969729953633502410069278720504525030982767921198917136807047940, 291962731840096987767532097260094666538434075153271734057599563825489636622120019312384304377985156, 265783403364244056648907069980607669823208658784201748090940956550980952460662808336991304258949427972, 551485160572145204080170463423771658209745667380554639902861112858619901240171280222058215444325892, 2108619732964434098577120573007744053305400437198639257746154866567981854020145231681543437940096772, 4184799162820819829078227502317159986675893175016902504508247258833023970964555318958934726472315652, 1070530018036300587646615172553100906231885150909660911332207009903206815759697001262067827769291524, 91366501612677521110804442905943034473085927843, 2108619732964493337646060684824119422668784250218354548114867980364994503662189757097483792787373828, 4184799162820878837644951280022313316673662162210569613059010304334949498682111970906125704372630276, 91366501612927239088582552443374724153446760867, 4184799162820878837644956432148430983103374939225609302507986877230613128246319071905164256451179268, 91366501613260196392286698493283643727261204899, 91366501612594281784878406393465804579632316835, 91366501615257940214511650350889117460627202467, 91366501612927239088582552443374724153446760867, 66470182058512384829044040516113561639967120523977133211121421428704522046996663879308181918066094852, 182710702395002680539521331446308733332230242723, 182710702395252398517299440983740423012591075747, 182710702395585355821003587033649342586405519779, 182710702394919441213595294933831503438776631715, 182710702397583099643228538891254816319771517347, 32440303108048829079678645129239900525486731490198241942553547719923119761332959742677589841621764, 182710702394919442481245895162060904935479837091] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_6 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨1, 1, false⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_7 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨1, 1, true⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [265783407324242112660282345317988319613650770615081294074257340443995616076798043183069731886190506756, 265783407324249547739800995321083996058181165000626105536684919650156299982758881979110275890477740804, 97320910291060875955413333562098117005044999642910667968426548947230950369787527571491654448919300, 5731313379498051163743666368806278703850979747, 291962731840096987767532097260094666392001845870171245198838268160901194467284271503927307261147268, 11440325928393373628038471902579134882547499427, 551485160572145204080170463423771658063313438097454151044099817194031459085335532413601218327488004, 2108619732964434098577120573007744053158968207915538768887393570903393411865309483873086440823258884, 22300830601430625234227128126289901072155043, 91366501612927239091058432521945555072257622435, 182710702395252398519775321062311253931401937315, 265783407324241994643148021686466088090844560895878838059042679393418534749373607413172717387333710596, 265783407324249547739800129763906054998613658970615950300131782125918608398556845689607361343455965956, 97320910291060875954534252043271282451604446977421327348028083493533416138719743096493241866072836, 22300832927588491412031503313762733485195683, 91366501615257940216987530429459948379438064035, 16641875741928918598441054544287251271743938727813983231887654485639233493692013457175956640579662596, 182710702397583099645704418969825647238582378915, 97320910291060875954643949395193263533810794126561596667649728898037478149268389005568917641573124, 265783407324249489653241493351602022195076938444397635814280046559906403708173724634611972074048271108, 291962731839860953496357287011073098299088582806665121467116613159875627038981856067352137621257156, 551485160572145204079401079256866804592079232581105079743322997144837986864816393847678481520141828, 265783407324362799933169129438952544239730250074311174714674443010708768319738278583904279624648176388, 2108619732962545824413107780183905482714301542021933278139058071239543177982524130341944241355436804, 4184799162820819829077458118150255133058226740217452944348709143119242056589200432584554992548131588, 1978658307749708630490539362458466078363601984228060758547600300911401764700630451836025614956582218776327737925903969859037555738141522284480789662555798841441521955259754278, 32440303108048829079678645129239900525486731490198241942553547719923119761332959742410408516072196, 132907923813795856530419143288627837160609634605521240558518843052975606845917567878112575710235407108, 97320910291060875954973685466723915035428523089101721402150394220509770258522852944303431994258180, 5731313379830359430340495565261631965624271267, 291962731840096987767092449164720464422385369316362298632562113434180014356019596876739084806486148, 11440325928725681894635301099034488144320790947, 551485160572145204079730815328397456093696961543645204477823662467310278974070857786412995872826884, 2108619732964434098576680924912369851189351731361729822321117416176672231754044809245898218368597764, 22300830269124893938598388129739632705274275, 91366501613260196394762578571854474646072066467, 182710702394919443751372375468861137350993904035] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_8 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨2, 0, false⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [1461518373821466315246093086704021232119125678370, 1463112883196259356047539652868711769857774885154, 1461529524236600876739693812553136732603025497890, 1461551825067119229976104935977537197394627697954, 1462934471120232709974909020507357560819426564514, 1461596426727657475950507839373999199330226968866, 1461507223427526709529031527234567217788541245858, 1461685630049730888896152333071601058496635771170, 1461507223406259061596472873268106304824055732642, 1461864035332094017699512078332111504702337759650, 5720173854405238096966034222790225670525983010, 732359625388131035654576046914287996175549241634, 5742496462745844024229147576996102271491153698, 5586075356143392788040551823285168123189666, 22880662596302511040674204388582158976733453730, 45761314282280863411787098188448281911234697634, 91522618314853497465399004966115575609471047970, 10889056510737002656622255123077746694562, 183045224376883329705905807021184106553756662178, 10889046126143285586966998061947649300770, 732180864850997610578894585201201513464029288866, 1462934476548789460166788375791248533874256419106] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_9 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨2, 0, true⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [299969087376429170407296043461839222584905144017207836201931989521661768374729945471841230282937856571502527412808994684363458713456327234996568611657538719434656336140412323914919568982914928692084994138023423198289090012955247523577854386079668466313359765427286704805856615259861619066367251744623423625333619812224208964180238899084405640368637627281336099935718719274, 359338200242848591644030772709518971279778, 129792896290437860424570981760056215692542900999118210044815787871321192477903926809917407277295844, 5586075356148463390441464742861478699243938, 91522617644932972183518474677856130158088460706, 732180864850997575084677778810780241888692705698, 184472472082881564474210850806756599590584105378, 91522617644932972183518474677856130158088460706, 365399103959663221738823029344923527200171495843, 732180864850997575084677778810780241888692705698, 730775907088974244047407653161643383629407195555, 1978658307749707751796438865740812779249117592976320684341492243346386197618115472698678459782188692333676490573081145014987360975470256279891708284501771811382490665355050022, 265750982861125933825305306532855560861707812428343121626970280731092492216504784129734451963440952293, 5720173811880331579255546800987686808119712162, 359339529470844376559903676516579251624354, 12867584426080879236179406163346362312609012642, 5586076685376459175357337646668538979588514, 91522617634299148217239147694625392200868993442, 732180864841692979114183367700453592466730293666, 183223630339800797616220607727353464846256486818, 91522617634299148217239147694625392200868993442, 732180864841692979114183367700453592466730293666, 1461507223406259061596472873268106023348005280162, 5720173813209564645642863586809099855212878242, 359340858703910763876689497929626344790434, 12867584427410112302566722949167775359702178722, 5586078014609525562674123468081586072754594, 91879429558804871253891035972809179034205338018, 732180864843022212180570684486275005513823459746, 183045224379541785697475638766993691000228067746, 183045224379541785697475638766993691000228067746, 732180864843022212180570684486275005513823459746, 359338200237777989243117852851732344773026, 5586075356143392788040551823003692072737186, 91522617634299148217239147694625392200868993442, 10889056510737002656622254841601696242082, 183045224376883329705905807021186076879667378594, 10889056510737002656622254841601696242082, 730753617158291650697836299231751736851596089762, 1461507223416892926127571407554677327724750608802] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_10 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨2, 1, false⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [1461518373821466315246093086704021232120199420194, 1462934471109598850514412887133704143905544509858, 1461518373864001611428123044694000408423346247970, 1461507223406248758132394218219530939484037224738, 1461551825067119229976104935977537197395701439778, 1461551825237260414704224767937453902608288750882, 1461685630049730888896152333071601058497709512994, 1461507223406259061596472873268106586300106185122, 1461685630730295627808631660911267879348058757410, 6065835363786779480044515451255599011325852066, 732178425706991521291988479732015724025540024738, 11774847912682102261251971042085805564198173090, 5586075356143392788040551823566644173642146, 91522618314853497465399004966115575610544789794, 10889056510737002656622255404553797147042, 182688412453706839735641235528822014245711419810, 10889046126143285586966998061948723042594, 732180864850997610578894585201201794940079741346, 5798232884765285896231022393829908970906622242, 366805809411923175339896723883147122248967559458, 5753653342248585319183215604950241328577420578, 23014473172627620323334375884857564057985653026, 265783407324241950386722320669062588672968003834026005260857934090577120810956220127091828469170123524, 23014560284913552083581022508757066590647785762, 92771464819229061848813125784059975018291960098, 184115660157046735136231668565689297574218996130, 365378207814921753151737901717534593696899569954, 1462934471109598886008629693524127385813234260386, 6065835363786870433975081826715156399780837794, 5731313389798309349697952336891633155654680995, 5887453220624702395635653901512946052966160674, 91344560120515093742627476609643466727521032482, 732180864850997691708532999807883490729084885410] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_11 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨2, 1, true⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [97320910291060875955413333562098117151477228926011156827187844611819392524623275379414810753184516, 359338283314844638450416966690047788095906, 823703477721312468042306348959057936712448645410, 359338366391911287657716080528363231418786, 5731313379501945401242923519104618379438728611, 5731313379834253667839677157696245726889118115, 823703472266160732776192399258490661627598248226, 359338200237777989243117852851732344773026, 915222942288555477639389754598984996992658225570, 823703477721312468042306348959057936712448645410, 66441795803172494234761474971880478327896536625623439374660769738067316621927478326977050383264985860, 732181218739331911778039853963922923465177340194, 5742496461499692144355488832033853704835735330, 5742496333893804865916215090325673515540324130, 5920902977292939375750887192906581104649084706, 11418035986847155665592267689800553959223499170, 11774847912682111768631472753806316787458947490, 5742496461665846277653903430261530335722381090, 5742496424198251478138240743283824056608005922, 5742496466733567625665152327876056340644273954, 5586075439220459437247850936842007516060066, 91527844380759649802532356238920223257722395042, 5586075522297526086455150050680322959382946, 11440325928397267865537729052877474558135248291, 11440325928729576132134482691469101905585637795, 91527844371455053832037945128593573835759983010, 5586075356143392788040551823003692072737186, 183050102667553964271287849705364143979447237026, 5586075356143392788040551823003692072737186, 5586085990007923886574838394308068818065826, 91355362086588923815339758598535749231960955170, 92949871461381964616786324763228538770423847202, 91366512416652893578705868581807316382942011170, 4184799162814210869505997993202516128611228786503382881884818716945692809062234399309693511868360196, 22300830601430640089507599551275413937324451, 4184799162815155006587624849657100653527657793707050781057574629648684819457574607791341795276960516, 22300830933738906686336796006628675710615971, 91522618314853497465399004966115575609471047970, 91344211671381670165719545162620540461914298786, 91701023597216626268758750226626303290149747106, 91522618314853497465399004966115575609471047970, 92771464813912068736035047685763050987091695906, 823703471596240207494311868970231216176215660962, 4184799162814269071315839174926866197402218983798946510536003844704811563007512990530240132268959236, 4184799162815213323648574627780904880870709357729932357488267054690494897668091374440047913935778564, 732359619252424951140302239942230819164589693346, 10889056510737002656622254841601696242082, 732538373664486156232808428969831710709355952546, 10889056510737002656622254841601696242082, 10899690375268101190908826145978441570722, 91355710535732650856326345094134322314710391074, 184294066118634863497508733314765828244548655522, 91378011238395885931263222936541650696491015970, 16641875741929862735522677965991090685695277420520982791260464591244707291354831431403041932907390468, 16641875741932695146767548231102608927585138888101907109880779183562356063412437854849909678976466692, 91522966763997224506385591461713585742267062562, 182688412453706829594436433702986239322132355490, 183045224379541785697475638766992002150367803810, 182688412453706839735641235528821451295757998498, 17819990986512642115880798852713962645229839383340351005803266192998221594027981829070145989253, 184115660157046654006593253959007601785213852066, 25088434052803232483909376817790443747025315, 10889129203209934794266111618787042171170, 823703477721312468042306348959057936712448645410, 10889129203526847444323168969161217972514, 91522618314853497465399004966115575609471047970, 10889056510737002656622254841601696242082, 183045224379541785697475638766992002150367803810, 10889046126143285586966997780471598848290, 10894363058408834854110283432659971512610, 10894363078691244457761953856607222798626, 732180864840446823114445258213746017735080450466, 732359270813915048065594980429865517315997604258, 732180864840529900181094465512857604250710088098, 732359270803281224099315653446632809033941162402, 732180864850997610578894585201203483796382456226, 732537676766198702150835255978635690448058890658, 732180864850997610578894585201203483796382456226, 732180864845680678313345318057917831608009791906, 732180864850997610578894585201203483796382456226, 33659982948707628332269549280260643689603751189643619057757860818431180045654038033746750248197] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_12 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨3, 0, false⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [5720173874343738846465536865972521417711851810, 1461680402651959130029003430153460792938017626530, 5731346067549782963215274314005547160601403170, 22880662766433389769414180843465540282973461794, 1462931683527082934211835535845915172096892246434, 22925351539257566236413130635597643254531660066, 1461512820370713254258969126152764025291192441250, 1461680402651959053969967416459696703135825303970, 1461523992521467079577250762966989063420554288034, 1461546336822974730213814036595439139679277981090, 1462931683527082893647016328542574324202389674402, 1461591025425990031486940583852339292196725365154, 1461501648241227076873246143304999900126316108194, 1461680402632020634033193678366139597231620135330, 1461501648219959428940687489338538987161830594978, 1461859157044081839125699867393740207301409683874, 1462931683516449069680737001559343867720146917794, 91522618334791993461208756753437615744019896610, 1461501648241227158002884557911681595915321252258, 183045224398151048626898073768492347761773033890, 182710702395002680537664421387380610160234856867, 182710702395252398517299440983740423029502509475, 182710702395585355823479467112220173521859379619, 91522618314853497465399004966116420037622405410, 10889056510737002656622255967505898052002, 183045224379541785697475638766992565102468708770, 10889046126143285586966998906375800658210, 10894363058408834854110284558564173322530, 10894363078691244457761954982511424608546, 366805460973413231700370257067439565133136828706] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_13 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨3, 0, true⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_14 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨3, 1, false⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [5720173874343738846465536865972521422006819106, 5935226321948744131552892056902218147731746, 5720195694950517651644506454869222984143378722, 5586096613487861268039469709677223962777890, 22880662766433389769414180843465540287268429090, 22880750048860504990130059199052346535814667554, 91522618334791993461208756753437615748314863906, 45766889787667904993583228802328957093279734050, 732180864850997575084677778810780241888692705698, 22886412496402601187996110267235894810865868066, 91528193500156205321393901306318522346973993250, 91366501612927239088582552443374724153446760867, 91528193500156206589044501534547923843677198626, 91366501613260196394762578571854474646072066467, 732186445472500097911267097388757286435393935650, 10889056510737002656622257093410099861922, 732180864843022212180570684486275005513823459746, 10889056510737002656622257093410099861922, 5586080662711347029841691523144606096070946, 91522967464500454344072270175784840742499817762, 732180870284954309255743603972481549613367597346, 91522617634299148217239147694625392208385186210, 732180864840529900181094465512859856050523773346, 182710702395252398517299440983740423012591075747, 182710702395585355823479467112220173505216381347, 91522618314853497465399004966116420041917372706, 10889056510737002656622257093410099861922, 91523316574270424301728432723728476017100101922, 10889046126143285586966998906380095625506, 10894363058408834854110284558568468289826, 10894363078691244457761954982515719575842, 732180864861631475109993119487774788173127784866] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_15 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨3, 1, true⟩) 103 ⟨0, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

private theorem solve_1_1_0 (N : Machine4) (h11 : N 1 1 = none)
    (hAlive : ∀ q a, ¬ (q = 1 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
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

set_option maxHeartbeats 0 in
private theorem tv_1_1_1 : checkTree 4 (baseTable 1 1 1) 107 startPos 0 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_0 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨0, 0, false⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [1461518373821466315246093086704020968235328379170, 1461685630048484732896414223584895454089822902562, 1461529524236600876422781162496079118345119506210, 1461551825066869998776157314080195471341259889954, 1462934471099048098544180366536673860408048654754, 1461596426727408243482909617248428071780424390946, 1461518373778941403974692848426360689443896072610, 1461685630048484732896414223584893483764985927970, 1461507223406342138663122080567220002400936958370, 1461864035329518628633386652059582798399645202850, 36327374490080, 435450095733216, 36327374490080, 5575186403478989406417022949404190933293474, 72611258239456, 72611258239456, 145179025738208, 72611258239456, 145179025738208, 43490740704, 290314560735712, 43490740704, 290314560735712, 43490740704, 45123467741664, 435450095602144, 45123467741664, 81407351458272, 81407351458272, 153975118891488, 362882328168928, 153975118891488, 290314560735712, 290314560735712, 290314560735712, 290314560735712, 8839584025056, 51720537737696, 435450095733216, 51720537737696, 85805398165984, 85805398165984, 153975119022560, 508017863231968, 153975119022560, 43490740704, 290314560735712, 43490740704, 290314560735712, 43490740704, 1462934476543555584685478712295407140486522116386, 36327374457312, 36327374457312, 146278537267680, 146278537267680, 43490740704, 290314560735712, 43490740704, 290314560735712, 43490740704] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_1 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨0, 0, true⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [265783407324249547739800995321093822958741341408831261663684138305536840721900898017781742209352282884] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_2 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨0, 1, false⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [1461518373821466315563005736761078318609504180514, 1462934477224120318844268289279214831625214925090, 1461518373864001611428123044694000144538542315810, 1461551825066869999093069964137252821715435691298, 1461551825237011182553539195868940125431588232482, 1461685630048484733213326873641950834139161729314, 1461551825407152366014008427600627429164920642850, 1461685630729049467055203800568700049003771894050, 1461507223406331754386317660969020150924706879778, 45123467741664, 435450095602144, 45123467741664, 81407351458272, 81407351458272, 153975118891488, 362882328168928, 153975118891488, 290314560735712, 290314560735712, 290314560735712, 290314560735712, 8839584025056, 51720537737696, 435450095733216, 51720537737696, 85805398165984, 265783407324241950386721442231572629080652080360144503561892187941578189465038074625966257920920466180, 85805398165984, 265783407324245712211718805858856227759573105681484148571955248072943686313478431265589056819274645252, 153975119022560, 508017863231968, 153975119022560, 43490740704, 290314560735712, 43490740704, 290314560735712, 43490740704, 1462934471099131175610829573835785446923678292386, 36327374457312, 267859586754094781081583059578688405988113510525827571925188877564494144610568901912103594165977693124, 36327374457312, 265783407324241935663392319041542360325626240760729635733060130713714372790153897715018882018432987908, 146278537267680, 146278537267680, 43490740704, 290314560735712, 43490740704, 290314560735712, 43490740704] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_3 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨0, 1, true⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_4 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨1, 0, false⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_5 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨1, 0, true⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [97320910291060868753977638642423971813536648557272743832728880759172158669559403665954954417484548, 1070530018036242263411487666357825464020698053488922465394038450508667097203521729388850398927991556, 6065825833533750646972255558436157253929140643, 2108619732964434782936852819498838790537688071573211407044907361066864846992055924709480414946197252, 6065825833533588387695426345077251683293069731, 6065825833534237424802743198526384764719464867, 6065825833533588387695426345077251683293069731, 6065825833534886461910060051980021445773230499, 6065825833533588387695426345072748083665699235, 6065825833538780684554036730853797822571488675, 6065825833533588387695426345072748083665699235, 6065825833543972981412571558482891271001630115, 6065825833534237424802743198526384764719464867, 6065825833554357575129641213741078167861896611, 291962731840096980571372179406295740354479947788991663864705213649170650966103933769751149198932100, 97320910291119862915190420613021380649948742103147263468026677336784143066613354304856233575920388, 11774838382429073111267061092209013432625660323, 291962731840155960326196386826961379371884370493951440027564598066446226880458597532622467098966148, 11774838382429559889097548732299240943415984547, 11774838382430208926204865585752877624469750179, 11774838382428910851990231878845604262362218915, 11774838382434103148848842264626654001268008355, 11774838382439295445707377092255747449698149795, 11774838382428910851990231878845604262630654371, 11774838382449680039424446747513934346558416291, 551485160572145196891044914991139690897773477355552360112052914250738579849552242907905782890898948, 2108619732964434091430201241102113839225319871209303720367863577370726518221908483738275341140426500, 356813284638265923400620811304395521776419235, 91701014066964074389224826205123660692961886627, 183045214849289233817941714745489359552106201507, 356813284638265923400620811304395521776419235, 365733616413949288231985320186176208241487799715, 731110419543260310540569944002896064670723515811] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_6 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨1, 1, false⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [] = some [] := by
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
private theorem tv_1_1_2_11 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨2, 1, true⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [36327374490080, 5887418554358476300496721281849620890075044130, 36327374490080, 97320910291886988700396629916755529747290522075418115076934673969310392960189551052531466242369028, 7147410667473513821941527371896703615820143010, 97320910292831125782018334245247979120882211660413918881441145691692321703148872389095803330966276, 5720162964133729974603914419216751988671814050, 40862860052960, 5709012591451387913296589318019577004445178274, 40862860052960, 36327374490080, 45398345648608, 64912290066787098416287190085261056885186523403593433110074705441828653212471689680831824931713156, 45398345648608, 36327374457312, 435828052855264, 145282104887776, 145282104887776, 435828052593120, 435828052855264, 435828052593120, 435828052855264, 145282105084384, 145282105084384, 145282105084384, 435828052855264, 36327374490080, 7314688120840335451955911870463082231726381346, 36327374490080, 291962731840569049112183031557452226355858235210310734283644888509358192095600997635318208060990980, 291962731843401460357048144542929574476633303965298145697164303676503865517191200805171602945146628, 40862860052960, 259522428731576090153307638888863834382740228524613542735306953422121630836603941169699610792506116, 40862860052960, 36327374490080, 45398345648608, 291962731843401460357048144542929574476633303965298145697164303676503865517191200807350800631660292, 45398345648608, 36327374457312, 5725716372361879690327636692805552438441449890, 5575186320401922757209723837817676377397666, 11445857558403357457898063661775539001392929698, 5575186320401922757209723835847351540423074, 5575186320401922757209723835565875489970594, 5575186320401922757209723836128827590875554, 5575186320401922757209723835565875489970594, 5575186320401922757209723837817683893590434, 145282105346528, 9131526624, 145282105346528, 9131526624, 290555079166432, 9131526624, 290555079166432, 9131526624] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_12 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨3, 0, false⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [36567893150176, 1461680402636008333232355628723607214085505063330, 36567893150176, 72851776866784, 1462931683511132137415187734416061593244379683234, 72851776866784, 145419544300000, 284009433568, 145419544300000, 284009433568, 290555079166432, 284009433568, 290555079166432, 284009433568] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_13 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨3, 0, true⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [966141752224567374254238356577442174386189017009701179916489591304784739257740046314146601316481637760372640501343685320309449168278896699173332522053228002781655078676262, 435828052855264, 818783238684015318949154687307522204503904598824627694873429528211407444941277468049894857642685219561485295985389541040490563711464732046801495848924471956581385516707775927624611551209798670129493004958511622854160505796908282680940791643128653526077848134908270292108014413502538022136233512482706152218985234303745416793317523422801957259952022305131016930307242331253418, 145419543841248, 6065825838518861460893457882070048228776109475, 145419543841248, 6065825838519510498000774735523684909829876131, 435828052593120, 435828052855264, 435828052593120, 435828052855264, 145419544037856, 145419544037856, 145419544037856, 145419544037856, 130774973853020778694428850656622124308859243939713711192832054843540864022232611940895074363299685, 11774838387414183925188263415842904407472629155, 11774838387414832962295580269296541088526395811, 11774838387418727184939481390018361174848987555, 11774838392756408395127667680734788321053549027, 11774838387418727184939481390018361174848987555, 11774838387423919481798016217647454623279112611, 11774838387413534888080946562389267730713829795, 11774838387434304075515085872905641520139395491, 519298320541849883997552647440459305506057156257070955415332360905933266644714406482486105624214884, 1038216434860320291574793551587181601815865763216270824933832198995668716120758525851152255242858628, 145419544300000, 9131526624, 145419544300000, 9131526624, 290555079166432, 9131526624, 290555079166432, 9131526624] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_14 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨3, 1, false⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [36567893150176, 217987311241696, 435690613901792, 217987311241696, 145419543841248, 6065825833534237424802743198526384764719464867, 145419543841248, 6065825833867194730982769327006135257344770467, 435690613639648, 435690613901792, 435690613639648, 435690613901792, 145419544037856, 145419544037856, 145419544037856, 145419544037856, 36567893150176, 5725749044692594988012723017353042578272983330, 732186445476487817392838651397893075424905304354, 5725770907834669658309000539171570069447678242, 11774838382429559889097548732299240943415984547, 11774838382762517195277574860778991436041290147, 732186445476487817392838651397891105091478395170, 5575196954266453855744010406870252235299234, 732183646999629556171771861751992157076976605602, 5575196954266453855744010406870252235299234, 11774838387423919481798016217647454623279112611, 5586080662711347029841691523144606096070946, 11774838392751236380678434273323462505292407203, 72851776866784, 72851776866784, 145419544300000, 284009433568, 145419544300000, 284009433568, 290555079166432, 284009433568, 290555079166432, 284009433568] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_15 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨3, 1, true⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [36327374490080, 5887419234923214896063399064459091366248487202, 36327374490080, 5720162974684517439053241406674218058496645538, 5709012591451387596383939260966589492408392098, 40828500314592, 5709012591451387596383939260962085892781021602, 40828500314592, 36327374490080, 36567892888032, 46374922023309795812986947974242578698492527585361168145650251003766652607000259479598804693336352322614618718510191564806936196844482562946284571411923472108079871326842023, 36567892888032, 36293014718944, 435828052855264, 145144665934304, 6065825843835793766056806282487869213929153955, 145144665934304, 6065825843836442803164123135941505894982920611, 435828052593120, 435828052855264, 435828052593120, 435828052855264, 145144666130912, 145144666130912, 145144666130912, 145144665868768, 36327374490080, 259554108715080044080921285759485610551769036730911507280748219701506970354562170922792879764222724, 36327374490080, 40828500314592, 11418025182882005925796052727656768000448567714, 40828500314592, 36327374490080, 36567892888032, 36567892888032, 36293014718944, 261549945757342591883783087492559576928071031619484302937462706809025469995259925244566240034876261, 130774973853020778694428823819356294633880419809694374678617248822518528847959212525711235817756517, 261549945757342591883783077429813403307429029539610255737559597135300466336075211125173473382034277, 11774838392731116230351611816260725392625673635, 11774838392731765267458928669714362073679440291, 11774838392735659490102829790436182160002032035, 11774838392756428677537271332405212268304835043, 11774838392735659490102829790436182160002032035, 11774838392740851786961364618065275608432173475, 11774838392730467193244294962807088720161841571, 11774838392751236380678434273323462505292407203, 145144666393056, 9131526624, 145144666393056, 9131526624, 290555079166432, 9131526624, 290555079166432, 9131526624] = some [] := by
  decide +kernel

private theorem solve_1_1_2 (N : Machine4) (h11 : N 1 1 = none)
    (hAlive : ∀ q a, ¬ (q = 1 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
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

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_0 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨0, 0, false⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [36842770565600, 5887430101362156496786673746845898960257718562, 36842770565600, 5753625119747422376529764242145916211694705954, 7136265749942947274654709217552412299163113890, 5798226780285667083282067410378516650859206946, 5720162964133729974603914419216751988671814050, 5887419222970547527716225863584140753636465058, 5731324183316517957737412472532526372546976674, 5753624928681202714177362789032851365073821090, 7136265749942906709835501914211564404660541858, 5798226419410572227057263422033501350127507874, 5709012570183739663825285294505676527922878882, 5887419192398303624663160786796578367188539810, 5709012548916091731266631328044763563437365666, 6065825835880515518059690245548393170939722146, 5720162964133729974603914419216751988671814050, 6422639165380235169970057095973848707413105058, 5709012549580705729159089264496667093577537954, 7136265739309082743556174930981107922417785250, 5709012548916091731266631328044763563437365666, 5887430101362156496786673746843928635420743970, 5709012570183820793463699901187372316928022946, 6065835382396052233759102221533243270080018850, 5720162985318381970151775693245522426719148450, 45638863817184, 5709012570183820793463699901183009454789007778, 45638863817184, 35743258905056] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_1 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨0, 0, true⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [265783407324242054573723612732663423703411841784513048393385662613519188647118002767279481692813996804, 265783407324249489653354812646507598390454123575691460629245838900155415920467210373645046649219920644, 265783407324242172590858816089720246769026395410413506880782257102607062648417420293339687728240344004, 265783407324242880693670033226654283190629940490683565751816156133732854460646758601339214646307202564, 265783407324362786103036867255184950066954120272549370052434344156835002880130216671092665658422539012, 265783407324243824830751660083108867715546369497887233650988912046435846471042098809820862929715802884, 265783407324241936556589289101141192180605632065310592378171001562942107319693566997382467715795727108, 265783407324249489653353947089319830430326441137476149265693482720537183597123158045472769836262306564, 435828052855264, 140746619423200, 140746619423200, 435828052593120, 140746619357664, 435828052593120, 435828052855264, 140746619619808, 140746619619808, 140746619619808, 140746619357664, 435553174948320, 145282104887776, 145282104887776, 435553174686176, 435553174948320, 435553174686176, 435553174948320, 145282105084384, 145282105084384, 145282105084384, 435553174948320, 1070530018036242270586544475948123513394226064318751327615132000175141565326455442689537524887663364, 435828052855264, 2108619732964434790083772151404469004424051000906778589370462352874508389522957881282747030596681476, 145282104887776, 145282104887776, 435828052593120, 435828052855264, 435828052593120, 435828052855264, 145282105084384, 145282105084384, 145282105084384, 435828052855264, 435690613901792, 154215636863456, 3201491998481280926669090456827455100323767876368674496560480327916803895690680021146242632310252466839670479187387337821059045787790283335855889507129014684028649207917551391159679938447670579061367300063365659083011518995479748860870344928329315249445452908408788505856741402033866433982808806272729731369798187401107820555790536419005288496868476833015194460920116875563, 154215636863456, 7345878855090507576007327640794530791344928316492382818172974439225845214578171065240101642594735252354678838391038218862262137900478613059932434088563129333761257672151916055323074451034481872008711361777662792840019401852609426411519037555273088647172086938761, 435690613639648, 435690613901792, 435690613639648, 435690613901792, 435690613770720, 435690613901792, 435690613770720, 435690613901792, 435828052855264, 154353075816928, 72990685981144898199218524311773429164596206594972789224771742693786383616885394691593006596855557, 154353075816928, 72990685981144898199218524311773432288483764634538324281624575009036278411358738898334096900753925, 435828052593120, 435828052855264, 435828052593120, 435828052855264, 435828052724192, 435828052855264, 435828052724192, 435828052855264, 265783407324362786103036427607089575864984503795995561105868068002108281700018951996465477435967877892, 435828052855264, 140746619423200, 72990685981144898199328436330703529401317493178030377176525002962627716099499501981785095428740869, 140746619423200, 72990685981144898199328436330703532525205051217595912233377835277877610893972846188526185732639237, 435828052593120, 140746619357664, 435828052593120, 435828052855264, 140746619619808, 140746619619808, 140746619619808, 140746619357664] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_2 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨0, 1, false⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [36842770565600, 7136299097604520932907058973004627683610499362, 36842770565600, 5753646897818905316591425898120791844860239138, 5753647067960088777060657629808095561012780322, 5887451879433639436848335402818804268586277154, 5798248537172498027795867792324692231901452578, 7136288198599534000272552707815395007302506786, 5753647216916620558894678144523979230473657634, 5887452028639402101717327757818852510201321762, 291962731839624919226721245095861237148643730775857140336948598257237004051574275882308364075741956, 5887452198780586829837159717735557723057068322, 291962731839624919226721245095861237099832987681490310717361499702374189999962359946156031703462660, 45226546989536, 35193503091168, 45226546989536, 259522428735352645675954374056530194367127047360305962964557367163165697662316708835934480961568516, 35468380998112, 310495522189437959678012707494375773865332981546849207285469469954801379220230052713250900049869252, 35468380998112, 35193503091168, 5887452559998373278725262329568019133196441890, 36327374490080, 291994411830681969927119500283579703759756589885892171242726598387119867035763568522669790901515012, 36327374490080, 291962731840096987767532097260094666392001845870171245198838268160901194467140969701440676222695556, 291962731839624919226721245095861237099832987681490310717361499702374189999962359944020668453171972, 40828500347360, 11418025097811414195561436861813116142640732578, 40828500347360, 36327374490080, 36567892658656, 291994411823128865951147474176629182665029871203452974496606433604744381069397517942075956274608580, 36567892658656, 36327374490080, 45638863817184, 5753653405719172679539539635160159004807699746, 45638863817184, 35743258905056] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_3 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨0, 1, true⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_4 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨1, 0, false⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_5 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨1, 0, true⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_6 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨1, 1, false⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_7 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨1, 1, true⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [265783407324242053666122891128373013944532354005870239002222564185310094260723864301189603932919509764, 265783407324249488745753211960698361797066955316034130800230704911387810442630425470343487282428982020, 265783407324242171683263369618479947520997179987648275871239601216462338563577259210848780667329133508, 265783407324242879786067551527305130705990235222950469238130349569749397194335819306635579646479181316, 265783407324362785195433507977020421733803196456906251873050325725280111167310398255119841949915493124, 265783407324243823923149173231633597564476951453139097447854128909556725631570596294538109186000237316, 265783407324242053666122891128373013944532354005870239002222564185310103884595601397837708895921058564, 265783407324249488745753211960698361797066955316034130800230704911387808036074955480373158542873670404, 1978643219155861026940799969754967103147835798363388082540521366487974058203644286907427145876793022702924724421887666237018978393664386357689931517250576344443298030551591206, 266059181580704279355785479115252166253740279045657358802431585247433053327351101552019470809600883140, 266061462539456139264447714734414547105998325265247773831163190875563238696921585201332907740963748292, 265783407324362785195433507977020421733803196456906251873050325725280106354199453792620374559383827204, 266042929749106326216793731317017053656239331889919672636429803320646242984851645390563605875974683076, 265783407324249489653354812646507598390454123575691460629245838900155415920467210373645046649219920644, 265783407324242053680529280346938710422655075773838033706876124669082388629952544960743003689211605764, 265783407324362785209839897195586118211925918224874046577703886209052398316872662220923539655424684804, 265783407324242407731940164263127760713741580813163227628324106535186465028013723147272832856453773444, 265783407324242879800473940745870827184112956990918263942783910053521691563564499966188979402771277316, 265783407324245712211718805858856227759573105681484148571955248072943676762461543169056728404952809220, 265783407324249488760161359771619350014907672568336744952484786933052211821369985401983678479822172932, 265783407324245712211718805858856227759573105681484148571955248072943676762461543169058874204973629188, 265783407324241935663392319041542360325626240760729635733060130713714363163932152231901864402843022084, 2092399566058740735067635639764029708344001525553617466438525340506781011722869033805647574915365733, 265783407324245712211718805858856227759573105681484148571955248072943686313478431265589056819274645252, 265783407324241935663392319041542360325626240760729635733060130713714372790153897715018882018432987908, 265783407324241935634580420329945558912189141131492048795934943184680576725571661593957191729729975044, 265783407324249489653353947089319830430326441137476149265693482720537183597123158045472769836262306564, 398675109006424366594139622420543344182725099383239817072874441628912227873539483485450334902444620228, 265783407324241935627377226042657490493199402085131399902283520160409073529463277148678386174864341444, 265783407324241935627377226042657490493199402085131399902283520160409073529463277148678386174864341444] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_8 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨2, 0, false⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [91355362086588923815339758598539971372717742370, 91522607445766560525858981886946526967947631010, 91366512501723485308940484447655471856617561890, 91388813332241838545351607872055936648219761954, 92771454621402181651017203914631796028263668130, 91433414992780084519754511268517938583819032866, 91344200803613576628247368301098519225550543266, 145282105346528, 140746619881952, 145282105346528, 145282105346528, 154215637322208, 154353076275680, 154215637322208, 140746619881952] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_9 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨2, 0, true⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [823703466820988632637001595563301836426876852642, 290692517988832, 823703466820988632637001595563301854019130005922, 290417639754208, 290417639754208, 290692517726688, 290692517857760, 290692517726688, 290692517988832, 290692517857760, 290692517857760, 290692517857760, 290692517857760, 92771453919881947358707780257494331021100324259, 92771453920214904662411888528471387637753579939, 290417640212960, 9131526624, 290417640212960, 9131526624, 284009433568, 9131526624, 284009433568, 9131526624] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_10 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨2, 1, false⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [91355710535732650856326345094137981503366273314, 91433764122820857472166654572004235305332807970, 154353076144608, 91389162632091489226937354167232986817317870882, 145282104887776, 16641875741928918598441933840464897141593784455651199175134242673606251424090510853966888940576387844, 145282104887776, 16641875742049768145339711637466616029220364712244440647844584754451141596508298377919653922530865924, 154353075882464, 154353076144608, 154353075882464, 154353076144608, 145282105084384, 145282105084384, 145282105084384, 154353076144608, 91355710578267947038356303084117157806513101090, 91355710535732731985964759700815191267817330978, 91355710620803324033112025623716193500002294050, 91344560120515093742627476609643466727521032482, 183045214851635582899632274573350040828338289058, 183045214851635582899632274573351166732540098978, 91522968125126778390380260834812161675456715042, 182688401564671169254044017481680497292407249314, 91389161781385565586338194367653946778868292898, 91389161951526750314458026327570651991455604002, 145282105346528, 140746619881952, 145282105346528, 145282105346528, 154215637322208, 154353076275680, 154215637322208, 140746619881952] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_11 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨2, 1, true⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [36327374490080, 97242770388601483636612945977253680412051413282, 36327374490080, 732180859395928952379429842799754550626602752418, 5720162964133729974603914419216751988671814050, 146278537365984, 103846333621033093381382838045153698, 146278537365984, 43490740704, 290314560735712, 43490740704, 290314560735712, 43490740704, 435828052855264, 145282104887776, 145282104887776, 435828052593120, 435828052855264, 435828052593120, 435828052855264, 145282105084384, 145282105084384, 145282105084384, 435828052855264, 36327374490080, 732180859396012029446079050098866137134716197282, 36327374490080, 146278537365984, 146278537365984, 43490740704, 290314560735712, 43490740704, 290314560735712, 43490740704, 16625655466745808166228020861172750071810747930453556026406188681338749216434048227010698492453600101, 16625655466745808166228020861172750071810747930453556026406188681338749202333137467025663798680763237, 16625655590616593274995628745961843853826600032809825018159652387604858653002816856965933468215163077, 8312827919179082669174690324937765886580020702283344305220307088411499452534761540906448411570253477, 8312827919179082669174690324937765886580020702283344305222953124096676670026688611626769409440001701, 145282105346528, 9131526624, 145282105346528, 9131526624, 284009433568, 9131526624, 284009433568, 9131526624] = some [] := by
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

private theorem solve_1_1_3 (N : Machine4) (h11 : N 1 1 = none)
    (hAlive : ∀ q a, ¬ (q = 1 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
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

end OMA.BB4HoleA0

open Turing Turing.BusyBeaver OMA.BB4HoleA0 in
theorem OMA.solution :
    OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H3_R1_H1_R1_H1_R1_H2_R1.H1 := by
  intro b c q u v N h107
  have h11 : N 1 1 = none := rfl
  have hAlive : ∀ r s, ¬ (r = 1 ∧ s = 1) →
      ∃ r' w d, N r s = some (some r', Stmt.write w d) := by
    intro r s hne
    fin_cases s
    · cases hs : (v r).2 with
      | write w d => exact ⟨(v r).1, w, d, by simp [N, hs]⟩
    · have hr1 : r ≠ 1 := fun h => hne ⟨h, rfl⟩
      cases hs : (u r).2 with
      | write w d => exact ⟨(u r).1, w, d, by simp [N, hr1, hs]⟩
  have hm : Matches N (baseTable b c q) := by
    intro r s m hget
    fin_cases r <;> fin_cases s <;> simp [baseTable, Table.get] at hget <;> subst hget <;> rfl
  fin_cases b <;> fin_cases c <;> fin_cases q
  · exact checkTree_sound tv_0_0_0 N h11 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact checkTree_sound tv_0_0_1 N h11 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact checkTree_sound tv_0_0_2 N h11 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact checkTree_sound tv_0_0_3 N h11 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact checkTree_sound tv_0_1_0 N h11 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact checkTree_sound tv_0_1_1 N h11 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact solve_0_1_2 N h11 hAlive h107 hm
  · exact solve_0_1_3 N h11 hAlive h107 hm
  · exact solve_1_0_0 N h11 hAlive h107 hm
  · exact checkTree_sound tv_1_0_1 N h11 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact checkTree_sound tv_1_0_2 N h11 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact checkTree_sound tv_1_0_3 N h11 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact solve_1_1_0 N h11 hAlive h107 hm
  · exact checkTree_sound tv_1_1_1 N h11 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact solve_1_1_2 N h11 hAlive h107 hm
  · exact solve_1_1_3 N h11 hAlive h107 hm
