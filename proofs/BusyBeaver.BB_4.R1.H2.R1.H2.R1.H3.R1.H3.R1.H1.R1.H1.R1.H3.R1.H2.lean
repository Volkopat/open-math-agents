import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H3_R1_H1_R1_H1_R1_H3_R1

/-!
FAR nonhalting certificates for write-1 transition at state 1 blank, hole at (2, 1).
Every machine in this branch either halts at the missing (1, 1) entry within
107 steps or hits a leaf certified by a finite automaton invariant.
-/

namespace OMA.BB4HoleS2A1

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
   some ⟨2, 1, false⟩, none,
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
private theorem tv_0_0_0 : checkTree 4 (baseTable 0 0 0) 107 startPos 0 [1464361709285022052001178423672349866257365887394] = some [] := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem tv_0_0_1 : checkTree 4 (baseTable 0 0 1) 107 startPos 0 [1464361710646151519684932277525848295984438733218] = some [] := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem tv_0_0_2 : checkTree 4 (baseTable 0 0 2) 107 startPos 0 [1464361707923892584317424569818851436530293041570] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_0_3_0 : checkTree 3 ((baseTable 0 0 3).set 3 1 ⟨0, 0, false⟩) 102 ⟨3, [1], 1, []⟩ 5 [51136422218208] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_0_3_1 : checkTree 3 ((baseTable 0 0 3).set 3 1 ⟨0, 0, true⟩) 102 ⟨3, [1], 1, []⟩ 5 [224859258915296, 431567445297632, 224859258915296, 224858755598816, 714320765918547718030611167178515527440034210, 224858755598816, 150091931322848, 150091998497248, 714320765918547718030611314752468117116447138, 150091998497248, 275742580527299580474506888679813849724767681207536561036766833077832855835102621561360533316729157, 275742580527299580474506888627403713403826835989899512639079194230819330557533205414277892493834565, 275742580527299580474506888627403713403826837444572970988891834131427627380702926038468772723456325, 275742580527299580474506888627403713403826834532384830098490726809113183347825934507149534504188229, 60428461260143471412155519039941090757191644174310925091681425655546099550590220155828996, 150092468259296, 12845253756016041012839556785893446735444313571, 150092468259296, 431567445035488, 12845253756021882346805408466975966581720371683, 431567445035488, 137871290263649797891087056128804870016022273012672334540996151450880685843270750289027533889923269, 431567445166560, 431567445166560, 431567445166560, 12845253756014093901517606225534862993152573923] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_0_3_2 : checkTree 3 ((baseTable 0 0 3).set 3 1 ⟨0, 1, false⟩) 102 ⟨3, [1], 1, []⟩ 5 [51136422218208] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_0_3_3 : checkTree 3 ((baseTable 0 0 3).set 3 1 ⟨0, 1, true⟩) 102 ⟨3, [1], 1, []⟩ 5 [265834218059235537506082906778547720171301473363880697894523456802250167452037839785939610215208152452, 265899098668354856614116907810431646938409384003634254265071375781059365045797665999584641958278297508, 51135918410208, 21278113695528295191257747697951599010, 51135918410208, 558349945312, 84121300830688, 282033595353568, 84121300830688, 282033595353568, 558349945312, 282033595353568, 558349945312, 51135918442976, 150092065606112, 51135918442976, 558350010848, 84121300830688, 282033595156960, 84121300830688, 150092065606112, 145981366161511564214147322386631152186608895052135073074068296094088797631566137537793673105764677, 150092065606112, 282033595156960, 558350010848, 282033595156960, 558350010848, 51135918705120, 431567310948832, 51135918705120, 558350207456, 1978658661558769454037282317423204677151291640880488396437137277417133655426860911270410200254592184181035898947306993091437257140233093139753562917451032925797100271912774822, 282033595353568, 150092065802720, 150092065802720, 282033595353568, 558350207456, 282033595353568, 558350207456, 51135918442976, 150092065606112, 51135918442976, 558350010848, 84121300830688, 282033595156960, 84121300830688, 150092065606112, 150092065606112, 282033595156960, 558350010848, 282033595156960, 558350010848, 137871290384499358745053697512029737359381463869397769080036832911566518570386383919302141337603557, 275742578593706851719645005185706750727451194033484008626227698115214228374125182079993404487330661, 137871292197242555458725988042905334737852918546450990623067254410687051362837445941203236284173989, 267632504629437842964223556692705575717766289649404695552815035181993350343364210426164108943333573, 275742578593706851719645005185706750727451194033484008626227698115214228374125182079993404487330661, 133816252495993256010506885074726084119800512783352134937991240995806811809964162023575932395096645, 2967979913699711984603573935545306514150849714580192670066978732183843911446063478468973120222309124611019530570136261708591428605252663378134569190582610028444725424717558950, 137871292197242555458725981439228060677820416673790590040584654498427433550051886664352387794143269, 267632504629437842964223550089028400841163756256058264037306115366422769951138042654063496282444357, 51135918639584, 431567310948832, 51135918639584, 558350207456, 84121301027296, 282033595353568, 84121301027296, 150092065802720, 150092065802720, 282033595353568, 558350207456, 282033595353568, 558350207456, 12845275534085576841579267881518745821277880803, 265750963061619406012821008204620250695880425943095165996798448212980112735281692321531998863233346948, 12845275534085576841579267881518745825572848099] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_0_3_4 : checkTree 3 ((baseTable 0 0 3).set 3 1 ⟨1, 0, false⟩) 102 ⟨3, [1], 1, []⟩ 5 [84121771051488] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_0_3_5 : checkTree 3 ((baseTable 0 0 3).set 3 1 ⟨1, 0, true⟩) 102 ⟨3, [1], 1, []⟩ 5 [365596244445664, 47099263715174013755946845577214638316857721315, 365596244445664, 365596243954144, 365596243954144, 282033326655968, 282033326721504, 282033595353568, 282033326721504, 2092399581648332110653699269935118963819772347543859258438485607825916631501863561345300122594561541, 117362228257937076096905385954196810518842232317258789310741788214920185288223470729876963648413557830927707160143225898676835915287803252082641137269281996126935336610448739731187861843172732430475966160621850677531594325993634416597970991851741533979136247322761, 282033595353568, 282033326655968, 282033595353568, 282033595353568, 431566975666656, 282033595615712, 431566975666656, 282033461397984, 47099263715181315423440534275576854076784136675, 282033461397984, 1046199790824166113403043315201342329297179428665540205969990219236664407033918688690853594685627333, 282033595615712, 282033327180256, 282033595615712, 282033595615712] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_0_3_6 : checkTree 3 ((baseTable 0 0 3).set 3 1 ⟨1, 1, false⟩) 102 ⟨3, [1], 1, []⟩ 5 [84121771051488] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_0_3_7 : checkTree 3 ((baseTable 0 0 3).set 3 1 ⟨1, 1, true⟩) 102 ⟨3, [1], 1, []⟩ 5 [265834218059235537506082906778547720171301473360974192007001777028933568529427984789081146776377060740, 423589258390947393005690121716813405106752567756544619772068701338130672682865590100774604158085265476, 2092399566179590280614804256908084926070208292082617339903825305284222150370806276268216406132144997, 266093740487968057645746971143989599474508956385602200667789789116088990103634823391048579476593276836, 266807300447059094033969705005167503576067408008535491777268620018323938991285354617592009621071162756, 282409058769719146602127109841946855130332624761521996832800545462039053554256876011365878703084435524, 1054309866722027980570823599535161231951392373676978603222869339377160833932828796931970031900684613, 398658885390295200986687618248395800301509507767743983219660920403204855059025909565019852946740246596, 265783403364727454827494188309507735483497861823281113414418979054849106965759137939590976495126214724, 265783403364727454827494188309507735483497861823281113414418979054849106965759137939590976495126214724, 266028859877884774531217677851043426074518301902916250681418361573834664419196798007298629192983473540, 423589258328891116789630195795195928824844337387675981333267314657549793812842680361669112801196931140, 265899098668354856614116907810431646938409384000726327797989962798486114768511100576216359934362875812, 266028859880785163630413597127314636238630479522578910003192870555290476851357072117288619239858730916, 2092399581648332225904807974509094372428923702567205454304528708552404136638752295455595255807622277, 2092399566179590280614804256908084926070208292082617339903825305284222150370806276268216406132144997, 265750963061619406012821008204620250695880425940186529239921292411588623890110382361404198974959873412, 269919542258563977366717102984433752400374302966004767645342403001647572726223052365226326167156649348, 298969835424260383363490761971028466610761114155001169077204653166952782920916058443340964619453951364, 266093740487968057645746971143989599474508956385602910957627868506500936640295612343210014424891094948, 2092399566179590280614804257012905198712089976697777197224900638421737768100537882783756877194360869, 265750963061619406012821008204620250695880425940185818950083213021492099759033686771146032599752994180, 265750963061619406012821008204620250695880425940185818950083213021492099834238544437892814094046817668, 265750963061619406012821008204620250695880425940185818950083213021492099777834902238432456352055127428, 1054309866722027980570823599535161231951392368950710275275915388590822796485450857356702026574712325, 1046199806292908173944155618719780279602851733371070727036100630992771561265709194117788236105000997, 2084289505750470473988136167918182608080738020747693826733921633085302154161317467342783786794398277, 1046199806292908173944155618719781087127785486575899953487730998520582507389742762089858455082510373, 2092399566179590280614804256908084926070208292082617339903825305284222150370949718152271022209907557, 1046199790945015775101729974660559723407538193945665958887224166010433307525950739281403267083079141, 47099350827458809701408307799319274994452693475, 265750963061619406012821008204620250695880425940549487347179860750907535870990030551320895045829356932, 47099350827458809701408308094467180173805519331] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_0_3_8 : checkTree 3 ((baseTable 0 0 3).set 3 1 ⟨2, 0, false⟩) 102 ⟨3, [1], 1, []⟩ 5 [150092468718048] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_0_3_9 : checkTree 3 ((baseTable 0 0 3).set 3 1 ⟨2, 0, true⟩) 102 ⟨3, [1], 1, []⟩ 5 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_0_3_10 : checkTree 3 ((baseTable 0 0 3).set 3 1 ⟨2, 1, false⟩) 102 ⟨3, [1], 1, []⟩ 5 [150092468718048] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_0_3_11 : checkTree 3 ((baseTable 0 0 3).set 3 1 ⟨2, 1, true⟩) 102 ⟨3, [1], 1, []⟩ 5 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_0_3_12 : checkTree 3 ((baseTable 0 0 3).set 3 1 ⟨3, 0, false⟩) 102 ⟨3, [1], 1, []⟩ 5 [282033864051168] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_0_3_13 : checkTree 3 ((baseTable 0 0 3).set 3 1 ⟨3, 0, true⟩) 102 ⟨3, [1], 1, []⟩ 5 [558887340512] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_0_3_14 : checkTree 3 ((baseTable 0 0 3).set 3 1 ⟨3, 1, false⟩) 102 ⟨3, [1], 1, []⟩ 5 [282033864051168] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_0_3_15 : checkTree 3 ((baseTable 0 0 3).set 3 1 ⟨3, 1, true⟩) 102 ⟨3, [1], 1, []⟩ 5 [558887340512] = some [] := by
  decide +kernel

private theorem solve_0_0_3 (N : Machine4) (h11 : N 2 1 = none)
    (hAlive : ∀ q a, ¬ (q = 2 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    (hm : Matches N (baseTable 0 0 3)) : CertProp N := by
  refine branch_one_sound (tb := baseTable 0 0 3) (q1 := 3) (a1 := 1) (rem1 := 102) (cur1 := ⟨3, [1], 1, []⟩) (step1 := 5) rfl ?_ N h11 hAlive h107 hm
  intro m hmem N h11 hAlive h107 hm' hsum1 hrun1
  simp only [moves16, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkTree_sound tv_0_0_3_0 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_0_3_1 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_0_3_2 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_0_3_3 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_0_3_4 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_0_3_5 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_0_3_6 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_0_3_7 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_0_3_8 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_0_3_9 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_0_3_10 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_0_3_11 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_0_3_12 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_0_3_13 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_0_3_14 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_0_3_15 N h11 hAlive h107 hm' hsum1 hrun1

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_0 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨0, 0, false⟩) 102 ⟨1, [1, 1, 1], 1, []⟩ 5 [1464361707966427880182233600491791597320730077602] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_1 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨0, 0, true⟩) 102 ⟨1, [1, 1, 1], 1, []⟩ 5 [571205086120416, 1464361710646151519684700162735461241340407343522, 571205086120416, 1461507212538480664554998511837108929444260637090, 567906484160992, 1464361707923892584317115083776009045621227940258, 567906484160992, 1464361710646151519684700162735460396914403469730, 1464361710646151519684700162735460678390453922210, 1464361707923892584317115083776009045621227940258, 41240448272864, 145694019291616, 41240448272864, 145694019291616, 398885998696552289814372347170527764923574499761414152131002981003072405949997053070636569497520061573, 365376803150578751410395849352720543134528858530, 398626476766687641488641470996512876761450105141215470810784901186785434958022141847920209160052948101, 145694019291616, 145694019291616, 365376803150578751410395849352720543134528858530, 21278113695528295191257747697951599010, 730753606279879389125263403514183338571106118050, 21278113695528295191257747697951599010, 41240448207328, 145694019291616, 41240448207328, 145694019291616, 77524365478368, 435965357459936, 77524365478368, 145694019291616, 145694019291616, 295227869104608, 435965357459936, 295227869104608, 21278113695528295191259999506355218850, 5709012570173436159823100725030603876648118690, 259538268723564086978493398500898178459396520006036937530527097650227423822761267001621967615421957, 11418025119068758624117906258803460055344638370, 21278113695528295191257747697951599010, 398885998696552289814372347170527764923574502740585483574290921651699026730198106027654439622670302341, 366090426996931731350924992337446416606922041762, 45672100412440693409886739461440597127523756450, 366090426996931731350924992337446416606922041762, 21278113695528295191257747697951599010, 732180859417103219741491847402539476958546291106, 21278113695528295191257747697951599010] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_2 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨0, 1, false⟩) 102 ⟨1, [1, 1, 1], 1, []⟩ 5 [1464361708008963176047352117355144723897303198626] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_3 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨0, 1, true⟩) 102 ⟨1, [1, 1, 1], 1, []⟩ 5 [564607848581600, 1978643212360697238219068824983734034857852596935827151626556170206389317735969852699412692579117444647265104672358661120507433900024519919223343038582160081670004747816024871, 564607848581600, 563508303366624, 563508303432160, 36842267544032, 145694019291616, 36842267544032, 558350207456, 290829688375776, 145694019291616, 1461501637352181031899213127759966814768502696354, 145694019291616, 1461501637352181031899213127759966814768502696354, 290829688375776, 558350207456, 290829688375776, 558350207456, 563508303432160, 36842267478496, 145694019291616, 36842267478496, 558350207456, 73126184749536, 290829688375776, 73126184749536, 145694019291616, 1461501637352181031899213127759967940668409538978, 145694019291616, 1461501637352181031899213127759967940668409538978, 290829688375776, 558350207456, 290829688375776, 558350207456, 35742722099680, 145694019291616, 35742722099680, 558349945312, 282033326655968, 1038105554918292487074810243683422952750344473716705006365686453189387955786610466911912809179344389, 145694019291616, 145694019291616, 282033326655968, 558349945312, 282033326655968, 558349945312, 36842267478496, 145694019291616, 36842267478496, 558350207456, 73126184749536, 290829688375776, 73126184749536, 5575207577746351313678973254209007055301026, 145694019291616, 145694019291616, 290829688375776, 558350207456, 290829688375776, 558350207456, 35742722034144, 259538268723564086978493398500898178459396520004616357917873174690031719308226821544014790285454853, 35742722034144, 558349945312, 70927094122976, 290829688375776, 70927094122976, 1038105554918292487074810216849433156428626509827711327256730196806232305030569395155346225450053125, 290829688375776, 558349945312, 290829688375776, 558349945312] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_4 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨1, 0, false⟩) 102 ⟨1, [1, 1, 1], 1, []⟩ 5 [1464361708094033767777589151081850977050449440162] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_5 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨1, 0, true⟩) 102 ⟨1, [1, 1, 1], 1, []⟩ 5 [1464361707923892584317115083923586375923509782946] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_6 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨1, 1, false⟩) 102 ⟨1, [1, 1, 1], 1, []⟩ 5 [1464361708264174951238063218535263483356741921186] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_7 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨1, 1, true⟩) 102 ⟨1, [1, 1, 1], 1, []⟩ 5 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_8 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨2, 0, false⟩) 102 ⟨1, [1, 1, 1], 1, []⟩ 5 [1464361708604457318159011353442088495969326889378] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_9 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨2, 0, true⟩) 102 ⟨1, [1, 1, 1], 1, []⟩ 5 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_10 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨2, 1, false⟩) 102 ⟨1, [1, 1, 1], 1, []⟩ 5 [1464361709285022052000907623255738521194496813474] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_11 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨2, 1, true⟩) 102 ⟨1, [1, 1, 1], 1, []⟩ 5 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_12 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨3, 0, false⟩) 102 ⟨1, [1, 1, 1], 1, []⟩ 5 [1464361710646151519684700162883038571644836669858] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_13 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨3, 0, true⟩) 102 ⟨1, [1, 1, 1], 1, []⟩ 5 [8563508295867722842887808714457242948798015906, 228157760244192, 368587416283138642428388900080404781860561906082, 228157760244192, 150092199823840, 365732920897726722666272326960914170872532593058, 150092199823840, 1832890287777495578121806972999183915614593540500043508202349663492586319278084807391872559699791995660335778821432673036098169408644951795995546417354212315979851738784957488476256095637328734652372587461077698916961834669008466575278327239097146417153080593161, 368230604359962152458124328588041563650462345634, 368230604359962152458124328588041845126512798114, 435965357459936, 365732920897726722666272326960914170872532593058, 435965357459936, 14272520844763045307182614248230099127494535586, 544817109043680, 265783407324725333813167538658845624572673587145855387282028592761919129128005198992715330810433402948, 544817109043680, 558349945312, 558350010848, 558350207456, 558350010848, 129777054357776070718133912919321818013608100917439711662021375736021359324324139435654735046338373, 558350207456, 558349945312, 558350207456, 558349945312, 25690546963400790998616630073144337470061570466, 519060720658253167091715036827436632971130369071878569698139785856942041566645252595864428466805317, 48526597158982080855795852208235762184847649186, 94198698911274128253946835958144709475083250082, 185542899693599287682663724498510408334227564962, 368231298535990671172512422324641705151836481954, 132875499350558938790059545117391869387554536027945997225114975227899852738746164508803527960391855621, 298526504421856, 120767258290091464115549593293472339344016764799195646018310108372522943006843820700322446770383929548510390911326934494746879032934671204117614281275874362933699936926503, 298526504421856, 282033326655968, 282033326721504, 290829688375776, 282033326721504, 290829688375776, 282033326655968, 290829688375776, 290829688375776, 66437757595275474464755502171543597300843578818265755106925506111992793824087040254531420115774860805] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_14 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨3, 1, false⟩) 102 ⟨1, [1, 1, 1], 1, []⟩ 5 [573404176484832, 3353732544361657240607343334147479876368021123065900902962536684619967624146613620902284394655876924402619437592223975271872365373566497234105791886599826198114283880040660064985947750033590292937033912706604631012775294544687707231463477532744815883888283695032234067805629069055336646636565029245698509757878662883960266538508953937160387042666692299515200539646479713370905130, 573404176484832, 45638595414496, 702364083438512671626544080017179521640866, 45638595414496, 290829688375776, 81922479163872, 290829688375776, 81922479163872, 5580652095617086483837482452159008601074082, 290829688375776, 290829688375776, 290829688375776, 9354711665120, 572304664889824, 45638595414496, 45638595414496, 290829688375776, 81922479163872, 290829688375776, 81922479163872, 1461501642796698902634383286269167016569862154658, 290829688375776, 290829688375776, 290829688375776, 9354711665120, 572304664889824, 259554109198478233466675932087320615678683863904452077085519372513146546207292183311907754138173572, 2092399581890031321501161991899214891463247035319808406072062439883121118205275533079450037926247172, 483457197960390425940787168533020162085473220459067457506715789200791150259507729630509828, 33222925916013647518885782575586807166082247807311177612271644601096644085367664035311029553271421700, 498343881803501068147395315062300089632173577002802364765151552214909587572537854244630201720361089092, 132891703662604380755222862754956322400032335095051961261255650605895813539323633693314168571766520580, 265807733592058432436234267033018414595011526470973682418611014605805710607667076545393325334140975172, 45638595381728, 435965223242208, 45638595381728, 290829688375776, 81922479098336, 290829688375776, 81922479098336, 154490246531552, 1462931678082554678843334264203401718651339991458, 154490246531552, 1461501642796698902634383286269168142469768997282, 290829688375776, 290829688375776, 290829688375776, 9354711665120, 81100758978735554310785261679920616656833819512871454760701786480206649661781237545865491489241860, 30192160101404024465214560415393717424592152451834644311765938399279025560974130758701354322165882336532243900257422033174667789839194164329439811012432702207825355094823, 275742580527771666122904025377917166043790665740132031991113505693876931361707235091586582706141956, 290829688375776, 290829688375776, 1038105554918292487074810190434724450674435390577734709167733411074652246239584189754898202190950725, 4152865739932232452232386892318811504796911165409271342006605136268371654912031630108429659214959364, 16610449198791500677743858849612659212161260399919229611421604021126306933261276232661862162699873028, 290829688375776, 290829688375776, 290829688375776, 9354711665120, 45638595381728, 435965223242208, 45638595381728, 290829688375776, 81922479098336, 290829688375776, 81922479098336, 5580652095617086483837482454410808414759330, 154490246531552, 154490246531552, 290829688375776, 290829688375776, 290829688375776, 9354711665120, 45638595152352, 45638595152352, 290829688375776, 81922479163872, 290829688375776, 81922479163872, 1038105554918292487074810190434724450674435389850397958327086779688529743227917127998823851121193285, 290829688375776, 290829688375776, 290829688375776, 9354711402976] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_15 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨3, 1, true⟩) 102 ⟨1, [1, 1, 1], 1, []⟩ 5 [36842267249120, 8574659689314088917302981183385325760249096610, 36842267249120, 35742722034144, 37941812464096, 6433789511384616779508090680530776596713335202, 37941812464096, 8563508636150089763835943436810592683530680738, 8563507955585355921939673696951765876775872930, 8563509316714823605732213176673923089912850850, 8574658370719917098628958419441216634169092514, 45638628936160, 5709012570173436159823100577456792024460061090, 45638628936160, 35742722034144, 30192160101404024465214560415393717424592152438613524935191395986717389728201244961427911339146246253779221825824855398481083180879572284844836726530826378534708346239783, 1932269683111120091895213687554095614859334004857954584403287078317328030552344304419249984668428463845583277736573860990799725482147590964705528401849577936394557797985318, 30916536063988758869685986299702644542184504288051910208753318301165920263774926650799776854203923782116627621840177696801947883653361407537848799803589920746805663221046310, 30916536114376593368569785787180675828267501107392517933734784591894382677027507554320441001777179466480205221919291895897393601046389912323795337133683087742142691242826790, 30192160101404024465214560415393717424592152438613524935191395986717389728201244962422314978361526560686388873209983853809979152395822794664684668187570179295427072506663, 259538268723564086978493371771728254921952838584911651955390464137531130370338755436419581810323781, 36842267249120, 14294823971938144376961094212817365656939817378, 36842267249120, 35742722034144, 37941812464096, 11440325864267289247259441829502155831469173154, 37941812464096, 332188720656411423276014522766334594790684094387276003732892628991119568158623342881254509276747656709, 14272521185045412228130748970583448862227200418, 14272521865610146070027018710446779268609370530, 45638628936160, 14361723825557167799748757010635865271269616034, 45638628936160, 35742722034144, 36842267249120, 265783407324725333813167538658845624572673587145855387282028592761919129128005198992715330810433402948, 36842267249120, 558349945312, 558350010848, 558350207456, 558350010848, 129777054357776070718133912919321818013608101281108076244182524943198560766062474181854896466814789, 558350207456, 558349945312, 558350207456, 558349945312, 72026639337952, 483070876000690179943777856643775362310466482482215795077458450239856656887868273890823383353363863924139028835833306762388293281163541010559039261517488947627483078481702, 72026639337952, 70927094122976, 70927094188512, 73126117640672, 70927094188512, 265750978903061588574226481146481184655909413793990840341891804665648387646812079934565192647539551749, 73126117640672, 73126117640672, 70927094122976, 519060720658253167091715037456358478122887022859207106463265592050350321456341880049320318612648773, 48526595797852613172003312433361759144831379874, 368231301258249606540097501579241806052516194722, 132875499350558938790059545103974874489393677045274119230769454617902077717063191058249165242136489477, 291929233328608, 120767258290091464115549593293472339344016764812416765394884650785084578839616690201183771034056273857765605530177591194565072920604390517968262851413887763612780664077095, 291929233328608, 290829688375776, 290829688179168, 290829688375776, 290829688179168, 1038106529449035040345044425713028277808669260592636776705060906390448334527505745046508310086938117, 290829688375776, 290829688375776, 290829688375776, 290829688375776, 66437757595275474464755502171543597300843578817538418345246697556372593112645404180236545322831703557] = some [] := by
  decide +kernel

private theorem solve_0_1_0 (N : Machine4) (h11 : N 2 1 = none)
    (hAlive : ∀ q a, ¬ (q = 2 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    (hm : Matches N (baseTable 0 1 0)) : CertProp N := by
  refine branch_one_sound (tb := baseTable 0 1 0) (q1 := 1) (a1 := 1) (rem1 := 102) (cur1 := ⟨1, [1, 1, 1], 1, []⟩) (step1 := 5) rfl ?_ N h11 hAlive h107 hm
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
private theorem tv_0_1_2 : checkTree 4 (baseTable 0 1 2) 107 startPos 0 [8563507998120651787366466639694936891651549602, 1464356830997009873427366212733977724428286454178, 14272520589551270116778580106389618999319096226, 1464356154558199730466509878218198310863519115682, 8563660742368103423319439125685265638991358370, 1829732938589152524743782332967355874686608107938, 14272651513191942947552583003483263776775498146, 2854495406690033457644867130156737970717092258, 185542898332469819998871183690614303918681778594, 2854495406690033457644867130157863874918902178, 185542898332469819998871183690614374287694391714, 1464357529256426795192861124788284275346621098402, 1464357529256426795192861124788284556822671550882, 2854495406690033457644867130157863874918902178, 130774973853020778695088282545422498083130885524002306212811036378118244788087517015017200543537797, 130774973853020778695088295962417596172793581995033267596044845287782425568461936667935658954250885, 1464356176378806509271690056737526313073257769890, 8563507998120651787058189379708785728563472802, 130774973853020778695088269233247674197293678869861477284660943208024049606699516245755021014870661, 14272520589551270116471511776834786076086266786, 2854495406690033457644866982582785381040679330, 2854495406690033457644866982582855750053292450, 2854495406690033457644866982582785385335646626, 2854495406690033457644866982582926119065905570, 2854495406690033457644866982583911285242489250, 130774973853020778695088322796407792352118974937805480137086996601652445267729696400578668096805509, 2854495406690033457644866982585037189444299170, 130774973853020778695088295962417596172793581995743557370619378782327693540027831852986831271942789, 1464356220020020066882050413776182317492735077794, 1464356132737592951661329699994018213833133287842, 1464356307302447182102771127853494326331689691554, 1464356481867301412544212556008118344009598925218, 1464356830997009873427095412317366379365417380258, 1464357529256426795192861124935862450077054298530, 8565755520618868720616578051084634049056106914, 130774973853020778695088269180837537095380934324019590191643407034698744856215419283359219577531013, 14274746291442708244849721928882632186840246690, 2854495406690033457644868163174406098451982754, 130774973853020778695088269180837537095380934324022017939968699872995509869460041303189842618505029, 2854495406690033457644868163174546836477208994, 130774973853020778695088269180837537095380934324020630655211389679683100920856062976219538377578309, 2854495406690033457644868163175532002653792674, 130774973853020778695088269180837537095380934324196815819389784230362590823072826730992325029816133, 2854495406690033457644868163176657906855602594, 130774973853020778695088269180837537095380934324108029594921931858368418112418213804886590783776581, 8563507998120651787058190560300406445974776226, 130774973853020778695088269180837537095380934687687954773804556241875946297953754029559446235785861, 14272520589551270116471512957426406793497570210, 2854495406690033457644868163174406098451982754, 130774973853020778695088269180837537095380934687690382522129849080172711311198376049390101895649093, 2854495406690033457644868163174546836477208994, 130774973853020778695088269180837537095380934687688995237372538886860302362594397722419699798054725, 2854495406690033457644868163175532002653792674, 130774973853020778695088269180837537095380934687865180401550933437539792264811161477192551688070981, 2854495406690033457644868163176657906855602594, 130774973853020778695088269180837537095380934687776394177083081065545619554156548551086817442031429, 25690545772412506775602807039778983214654188962, 1464357529256426795193093239578672174416656361890, 48526596138134980093251260906557711645324372386, 94198696869579926728548168640115168506664745378, 1464356132737592951661639185889283274439916546466, 185542898332469819999141984107230082229345479074, 1464356132737592951661639185889283274439916546466, 368231301258249606540329615041459909674706954658] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_0 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨0, 0, false⟩) 102 ⟨3, [1], 1, [1, 1]⟩ 5 [36842770565600, 36842770565600, 36842267249120, 5709012570173436159823100725030603876648118690, 36842267249120, 35742722034144, 37941812464096, 5709012570173436159823100872604556466324531618, 37941812464096, 45638595414496, 5798215891249925573337378468052862525863127458, 45638595414496, 35742722034144, 39041290537440, 65894369556353814690138849561014288717040892066482103095752343110938064709130977328999494062454372, 39041290537440, 37941745355232, 37941812464096, 5753616995505912099332192595093907237392903586, 37941812464096, 5753614060570497406415657023823363447721060770, 65894369556353814690138849561014288717040892021023555490826803337762973748176267753927387501573732, 5753614273246976732002196693044179111003581858, 47837618440672, 64880610084227281564139302211295237387009669143920040466587497722908027447217533456885630516871300, 47837618440672, 37941812464096, 6422639181320647333286745392517553628338219426, 39041290537440, 130141373233139789053286338380211704618164029425600712398656240691057146293136698442458630532496996, 39041290537440, 37941745355232, 37941812464096, 5798215550967558652389243745695290650373679522, 37941812464096, 129887933365108157801202029549449576352445145940209052724455776676289068606966970586221868352137764, 47837618440672, 5798215891249925573337340652227440915099179298, 47837618440672, 37941812464096, 5709012570173436160132586767874120672735160738, 5720162985307997336820662559932270782526286242, 45638863817184, 5709012570173436160132586767869757810596145570, 45638863817184, 35743258905056] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_1 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨0, 0, true⟩) 102 ⟨3, [1], 1, [1, 1]⟩ 5 [9342815231066199569594532083186163155771506530586695556522902565271282658497388469589622594892688772, 9342934031042931000637567601229860754622836088126103324926164503838715633281133548663698472874241412, 17647556586714680793560730802909120785284626824251709771041256735024556082644823160350642109683069220, 9342815231066671638142377304771563543886846583020997741582621206192495572319033741973416270399499652, 30916307555214665017670590782646805904551543381100799826286544363919704968200991293421759771082178709287783828981067779437771542371233461687873515185335135587217404328557606, 30916536056845909444713725761622306769127764873494247613724771204789584029741106894120900138400503378195770214848443629014895226172610394797333633613272296879346495829728294, 30916536056846293873382693075766345755572513431514414702101579229892510119694821272316954541781097562812740306289769417200204774279081864944586374039517893753631613548911654, 15458157463145850454314619012180448749119844071571516366174003533223805348351043671516337963044093602172484400028758654187927948004789322926556524793526466615964128057498662, 15458150322441537977878018709296204984391961247843278275713538951137954178807638463333627705836208886132500907275653166569228785821907894020042059470206586535999447086144550, 30916314926291262419678607724826315305437173215126759646119394013442082177136388025591683977857534603743725958063237637496556309795793394191617528736592516331571321898556454, 30916301105571848329263438072799639531790604259123347679793248903455825673046365522824207165132615264880624458228030059115577374028317172155416134329174186845342763984632870, 30916301105571848329263438072799639531790604259123347679793248903455825673046365522836142922806450144292353632183556897828856014987835435268698873607818065951365797014682662, 15458157463117512784101780994891240852421324403923390052822852378201796553773805110495213389873873073664609773328780146186926085930838776183024373013004736460400703761292326, 30916536056846293873385969663047996797298689665347819616901735832887767650938357016189684092723606331529087053300369772984518756326872325067014680840936057882891687402421286, 30916314926291481235104037124745066387056301650153713587995692812899071876870198426176959639693224666487301074786324101837126865344799460257474310603568179916485687314504742, 8823762476810166474494789405474238964142700927645581332788939620216198054381764237244199049295523204, 17647564506710202730638784667858073988732393890376328792715236703059635802760853346875519879938830628, 137871290384499345239064489530668803318150495303007300495314618631982686364814275283961927091398693, 28579962494114403293188406330162031304641697414295644974023340472443005844144663049781896573364893764, 8304717596143901203390574502874110590472690174289102541978737796465295596952223755887175007581990276, 2504220315060949326403008580432503516530174277660373598477869314591218241163975239026477794892609192743978817262795717474463114716900594469779161974395088894941902317367973670, 145981366161511550708158087518869185113332760501707626542576383942673492714550575155941477696188997, 145981366161511550708158090768297685431922226191734491092370658578449491277677335315052437000317125, 145981366161511550708158141082028503552931307959471196634697286767526448062449328748979744320731333, 12845256478273029308639395189672898439030014435, 12845256478273029308639395189672898443324981731] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_2 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨0, 1, false⟩) 102 ⟨3, [1], 1, [1, 1]⟩ 5 [36842770565600, 60383398804174214440273364834078372219975991067215155539075947641598293444526900259436032249265839030362258086189737138480790990447068218321930251252892382792790563249190, 36842770565600, 36842267249120, 11418025119068758624117906258803460055344638370, 36842267249120, 35742722034144, 37941812464096, 11418025119068758624117906406377412645021051298, 37941812464096, 45638595414496, 11507228440145248037632184001825718704559647138, 45638595414496, 35742722034144, 39041290537440, 65894367625593497180142072396220453201357827162707961439440849284735680575080947320618861262550628, 39041290537440, 37941745355232, 37941812464096, 11462629586936530428745514987608203974235156386, 37941812464096, 11462626609465819870710462557596219626417580450, 130774973841691140693722296401443997035029107493851964117297190162104896416165111475292688330539140, 11462626864677595061414310164350547237098516386, 47837618440672, 130774973841691140693722296401443997035029107493851962931874152022270201269168614193605438391730308, 47837618440672, 37941812464096, 47837383821792, 130790814073253940247793646775776065267624542217514415842956868621129191008101488199151302499138884, 47837383821792, 47837383821792, 11418025119068758624117906406377412649316018594, 45638461164000, 45638461164000, 45638595414496, 45638595414496, 11418025119068758624117906111229507469963192738, 39041290537440, 259775868633596664159836999817682182968334910096965631980788425228962647718742107677369366581463652, 39041290537440, 37941745355232, 37941812464096, 11507228099862881116684049279468146829070199202, 37941812464096, 259775868633596664159836999817682182968334910096965631980788405041312461735332287950799638573730404, 47837618440672, 11507228440145248037632184001825718704559647138, 47837618440672, 37941812464096, 11418025119068758624120323972092108778052282786, 11462626779607003330875045001187380880896716194, 137890368949734192067820132956514604259499600632144573392749626605799264411897929067896204899557593023777885975482390559275729256269645509079902625449522232717949545547841156911811490314392198649930334079046039097206762260551420948572498241061766766030569963545881199826768290938752892962110364223399202540101060762958675333641773372570585769279927911748564368068413541913393947990641444780078820720566097585293916193499092138515152184205781631574785552831270038241605522268820685662384134593586948601612639895417791769806238825168034231965076640883346790772215104936920957595613883508135759161946783903286273650201324050345147495293199076404666027073092963308920925080821166378515193627294758002292908336654199591227274755570298694179840703790795746872908287766899144477495532471907893286023714233485141437439422292023515014874797274714964005762393908184665720419454315375169444693057995107499575652823746887921101476753289341818873319615767850934395929847614338421724261323422112080007075682489620135121269597904684840578447722894361015457088692727570578295778441190963060071446980981738746377425231800722801115728425753000929996763523766202300755077067727214592936207962137605849243160837514944869724208127118106595572418161579273066498858510415840677660450375722378805096169916672229329706824714394051515356661436369726555222632967404142680275722048783025044278333776035666035060351585160277949622600559682254701467268410318673772043295827622315655362120602435540588452546878356562995014383038588223649152899121413603034991292728007629457096859430691380406632937426158557478317462691150166996750926611754409049368478865079302049950540442610203239733751707119723729898529485755722706892794733065157254480634377037392985260145216827815432686627816748362550549911511796866477841284064057006543001050311712658736070426241561122145238449772694841318912058536954990235303651645638718424527031437785145668310025485490395225096420368838985165089004832661698825274, 11507228440145248037632183891145254278945335714, 11440325949337880977571429242949084333202238370, 30206441446324700867981261397071064302038244900003730714728054401528729883779407551627145738210879135862422711091418108476598933954982483303628858069036022095876366818342, 11440325949337880977648800790552325779736259490, 11418025119068758624117906111229507482848094626, 45638863817184, 259775868633832698490034565979718048001860434847570292011833129579433022074731201958390746530580260, 259775868754446212471523050470684170343225769877327738547523956219993105916792007614655511775791716, 11507228525215839767859546174401102236779309986, 259775868603384269894548517660096560516211715971627420016526277849656501275174807936228079127313156, 11507228270004064577158116437732747957620469154, 11507228099862881116684049279468146830680811938, 11507228440145248037632183891145254263912950178, 259775868633596664159836999817682182968334910096965631980788405041312461735341253071216515917662820, 11507231247474775135442207568138601846684019618, 11507228440145248037632184001825718706170259874, 11507233969733710503027286822738702742934580130, 11507228440145248037632183891145254263912950178, 45638863817184, 35743258905056] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_3 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨0, 1, true⟩) 102 ⟨3, [1], 1, [1, 1]⟩ 5 [265815851588798648142811443745152469674530559194358220971750027045841597459369824074037637917235703172, 275742578472857306172466157071993274071296719698946664741660773317193537315562439135867842443885413, 36842267249120, 21278113695528295191257747697951599010, 36842267249120, 558349945312, 73126184552928, 290829688375776, 73126184552928, 290829688375776, 558349945312, 290829688375776, 558349945312, 39041290537440, 39041290537440, 558350010848, 73126184552928, 290829688179168, 73126184552928, 137871290263649813197874829377641686993778240226959134666313217408086182657909959822620098458923333, 290829688179168, 558350010848, 290829688179168, 558350010848, 47837383821792, 21278113695528295191258873602153408930, 47837383821792, 558350207456, 1978658318806322648536321767863426169619564308304685117763537729930878308064605088711731761763147009015140086794193650501504188771438044593835913927572263888516718722582211750, 290829688375776, 290829688375776, 558350207456, 290829688375776, 558350207456, 39041290537440, 39041290537440, 558350010848, 73126184552928, 290829688179168, 73126184552928, 290829688179168, 558350010848, 290829688179168, 558350010848, 137871290263649813197874829377642186815787529270807295533738025524002867552408405259735758357925349, 275742578472857306172466167291968257224331539308102293642181804789712615362321868126694625407626085, 137871292318092102806703427996034756366442157738549823912697403280172391807943864368080689800580773, 275742580527299595781294594686447115673880243521758201170823912200820669515503656948648480291592389, 275742578472857306172466167291968257224331539308102293642181804789712615362321868126694625407626085, 137871290263649813197874829377640090687236081877656759308687611411721708756694680354047651296086597, 137871292318092102806703421392357582270811513129156484244592643726955951696362143425581249189578789, 275742580527299595781294588082769940797277710128411769655314992385250089123277489176547867630703173, 45638360500704, 21278113695528295191258873602153408930, 45638360500704, 558350207456, 73126184749536, 290829688375776, 73126184749536, 290829688375776, 558350207456, 290829688375776, 558350207456, 12845278256344512248701056845647774072195547619, 265750963061619406012821008204620250695880425943095165996798448212980112735281692321531998863233346948, 12845278256344512248701056845647774076490514915] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_4 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨1, 0, false⟩) 102 ⟨3, [1], 1, [1, 1]⟩ 5 [72026639337952, 1038097627218139787823364920921585227077724982618701364599597381636671960530368012367534994348441188, 72026639337952, 72026639337952, 74225662626272, 83021755910624, 74225662626272, 22847200589458668864279493968347348251043719586, 520058640138509706102877729712153547743401513518005180052927373039079960748086340676513376820803172, 22847200802135148189866033632956477896167288226, 83021755845088, 519044880666383172989188328849476674439338680939179252490222435448227023418146938012624607410143364, 83021755845088, 72026639337952, 72026639337952, 519060697455140250071177498384981466543917109402396003076352747563663906924462222106935225530541764, 72026639337952, 72026639337952, 74225662626272, 83021755910624, 74225662626272, 22858351047128525906084839919002643631117991714, 1038137227197637747368084692546826262700015351939273336239020231699257619436764359874756507502249764, 83021755845088, 520058640138627723011222028920577481432823563100590804714725176699444045575347278799014194963562628, 83021755845088, 72026639337952, 72026639337952, 72026639337952, 70927094122976, 70927094188512, 70927094188512, 73126184749536, 73126184749536, 70927094122976, 73126185011680, 23549676955612502321334492479298002274913119650, 73126185011680, 22836050216859403553017002188601068508593285538, 22880651877397648259769305375280413021198904738, 81922479360480, 22836050216859403552746202805007391573459102114, 81922479360480, 70927094647264] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_5 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨1, 0, true⟩) 102 ⟨3, [1], 1, [1, 1]⟩ 5 [364496732326368, 132892715457305067964066776489865015713252392586924211233640592051604222172072941603459053341534077060, 364496732326368, 364496732326368, 364496732359136, 364496732621280, 364496732359136, 11260833140563511667754565020387660806423469757560221567021428233461490288022396347225621524924128251447805892328884902174564636253607787805579804994271733149338924294433144266824799422938546718811876058921235676301993070258911085519879472667331462923800245687891329869236214017269639739076489906772024641084013550989916424314704804435843385271250362483231850982805639731823737901328078532276877207328719629384075659673322368954008536846980222010639294265509508248405908782815233433529468015554198543001705056669509640252164457813894118678813965071047760507858913807963010477430475639629817602720008296047219789084146385698085222497367707482023401817189669422, 46398096925654918672948619529753415449731688866, 132892715457305067964066776489865015713252392586924211233640592051604222172072869882518094758797394052, 46398096925654918672948619529753415449731688866, 364496732555744, 132891828417766957246925571937410192628526299609979310619978846592190732774063952163913925359548252292, 364496732555744, 364496732654048, 290829822724576, 366090429719190666718432700044442150156865923490, 290829553961440, 290829822593504, 290829553961440, 290829822462432, 290829822462432, 290829822593504, 290829822593504, 290829822593504, 290829822593504, 364496732326368, 46409247298254183984520596319317662576218761634, 364496732326368, 364496732326368, 364496732359136, 364496732621280, 364496732359136, 46409247298254183984520596319316536691344304546, 132892715457304831929796371063782898998630713529377764470984221750146935344836652500832493498282557572, 364496732555744, 132892715457304831929796371063782898998630713529377764470984221750146940195550025656628592914781716612, 364496732555744, 364496732654048, 364496732326368, 364496732326368, 290829419678176, 290829419743712, 290829688375776, 290829419743712, 2084289505750470359637426776926129495503054134679206224377156221629155976309535205288474193521823237, 9473793434779004735013301302923573888493949301891333034461473559957564284882085654109622917236137350811535755800587865277344609596564841861677778469403149956495384966263161038007248512817514416366562485578540488347414438656696431370877397911632335026625486930756428442136022170407965627866467311676385389201134031866856689476424178804179594794978598482547886972575326761541711493653172396327600221257726945618712801220538347975045336400843103028044876327153656123896256520835278886717333256544463118846093, 290829688375776, 290829688375776, 290829688375776, 290829688375776, 290829688637920, 290829554420192, 2084289505750470359637426776926129494722082245349750387860216226730416128571449513329059846216487237, 290829554420192, 290829688637920, 290829688637920, 290829688637920, 290829688637920] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_6 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨1, 1, false⟩) 102 ⟨3, [1], 1, [1, 1]⟩ 5 [72026639337952, 2076195269995540657843531920580210926465963921430735709330107063727111411869297481783921621509733988, 72026639337952, 72026639337952, 74225662626272, 83021755910624, 74225662626272, 45683250785039958721458716103438772965829798306, 519060720688347659246051001718137982796265923727262941359848111820966885174667318717252203940801060, 45683251167857621507514487499735206327105907106, 83021755845088, 2076195269878467659752336653890280049319074611732768312790335071784249815428678011679759207977831012, 83021755845088, 72026639337952, 45761303733517182823401017204462732630966692258, 966134380866787431043990236883368797567907510869655454568981530409549050445893549280957802857562390707049282982234082167546795518924840628540063834037085608694558191410214, 45761303733517182823401017204462750223219845538, 45672100412440693409886739461440597127523756450, 45672100412440693409886739461441723031725566370, 46385727321334975638939424868992429324860680610, 46385727321334975638939424868992710800911133090, 45672100412440693409886739461441723031725566370, 966141751803233124019562627846012660700055994431719029520956754135795857622343843737274700404461728236833362512438740435924329261350841514871143075553146045210652182191142, 45672100412440693409886739461442848935927376290, 45672100412440693409886739461440597127523756450, 72026639337952, 2076211109836584743639489535037054939332039759644230543027295483749889601011110149551646206500616964, 72026639337952, 72026639337952, 74225662626272, 83021755910624, 74225662626272, 45694401157639224033030692893001894211737381282, 1038105570417482860671890823085222478859246224645851244673656606209265337293237489128445744942575044, 83021755845088, 2076211109866797137904778017194640561784162953587734607924504743609532951897440773037582094228669412, 83021755845088, 72026639337952, 72026639337952, 72026639337952, 70927094122976, 70927094188512, 70927094188512, 73126184749536, 73126184749536, 70927094122976, 73126185011680, 45672100412440693409886739609019053334007409058, 73126185011680, 81922479360480, 81922479360480, 70927094647264] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_7 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨1, 1, true⟩) 102 ⟨3, [1], 1, [1, 1]⟩ 5 [265815851588798648142811443745152469674530559191451715084228347272524998536759969077179174478404611460, 2092399566058740735067625416026968662273460542170088708466199424892152152669419861175846909637573477, 266075405697513846117582201873561000038728436161385578818482406581555302419541067846068693848003178788, 266789187416475720194763557850086355667263812735586356296798001969596910924392943614355297399865568644, 1046199790824166229554551106526171766758561717760797522296901063883153804095395543401948100752421189, 2092399581648332226805207205911924146474908197052141202850904805617685605043551706909347479714740421, 2092399581648332226805207205911924146474908197052141192012742639131805164812664857652244664399640773, 266010493407446586979444916235354199729584189042205854389470562922054142574355180176151107069180865924, 2092399566058740735067625416026968662273460542170088708466199424892152152669419861175846909637573477, 266010517170334958096629963139772850170158834117144775606909351592074696613758582191963173573146964260, 1978643226526989467341667513706775083159926902543892854251060371217195030611084035106794771285448898971647111327252890597240365926443307560137794028413766421630320428641180710, 2092399566058740735067625416026968662273460542170088708466199424892152152669419861175846909637573477, 265750963061619406012821008204620250695880425940186529239921292411588623890110382361404198974959873412, 1046199790824166229554551106526171766758561717033460760618092266011150296522633293634450575679566149, 266075405697513846117582201873561000038728436161386289108320485971967248956201856798230128796300996900, 2092399566058740735067625416184199071236283070546081416527035583833343927738889396235980531421444133, 265750963061619406012821008204620250695880425940185818950083213021492099759033686771146032599752994180, 265750963061619406012821008204620250695880425940185818950083213021492099834238544437892814094046817668, 265750963061619406012821008204620250695880425940185818950083213021492099777834902238432456352055127428, 1046199790824166229554551106526171766758561714125534336868160309904820181952501931596779821009489413, 1046199806413757721292133058672909709041159867661862299459689804813321402856834487354465138945894437, 2092399581648332226805207205911924148036851974620047332351930510104399007542330441141769744078123589, 1046199806413757721292133058672909709041159867661862299462335840498498620348761557595997136201000997, 2092399566058740735067625416026968662273460542170088708466199424892152152669563303059901525715336037, 1046199790824166229554551106526172172863944259347075485340925358622869656507972760621836884103400933, 47099353549717745108530096763448303245370360291, 265750963061619406012821008204620250695880425940549487347179860750907535870990030551320895045829356932, 47099353549717745108530097058596208424723186147] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_8 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨2, 0, false⟩) 102 ⟨3, [1], 1, [1, 1]⟩ 5 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_9 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨2, 0, true⟩) 102 ⟨3, [1], 1, [1, 1]⟩ 5 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_10 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨2, 1, false⟩) 102 ⟨3, [1], 1, [1, 1]⟩ 5 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_11 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨2, 1, true⟩) 102 ⟨3, [1], 1, [1, 1]⟩ 5 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_12 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨3, 0, false⟩) 102 ⟨3, [1], 1, [1, 1]⟩ 5 [290829957073376] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_13 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨3, 0, true⟩) 102 ⟨3, [1], 1, [1, 1]⟩ 5 [558887340512] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_14 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨3, 1, false⟩) 102 ⟨3, [1], 1, [1, 1]⟩ 5 [290829957073376] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_15 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨3, 1, true⟩) 102 ⟨3, [1], 1, [1, 1]⟩ 5 [558887340512] = some [] := by
  decide +kernel

private theorem solve_0_1_3 (N : Machine4) (h11 : N 2 1 = none)
    (hAlive : ∀ q a, ¬ (q = 2 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    (hm : Matches N (baseTable 0 1 3)) : CertProp N := by
  refine branch_one_sound (tb := baseTable 0 1 3) (q1 := 3) (a1 := 1) (rem1 := 102) (cur1 := ⟨3, [1], 1, [1, 1]⟩) (step1 := 5) rfl ?_ N h11 hAlive h107 hm
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
private theorem tv_1_0_0_0 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨0, 0, false⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [570105910036960] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_1 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨0, 0, true⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [576702980164064] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_2 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨0, 1, false⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [570105910036960] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_3 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨0, 1, true⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [570105406720480, 1461507213899620516872083516602996588960763914658, 570105406720480, 567906349877728, 567906417052128, 1461507213899620516872083517045718446729793153442, 567906417052128, 42340060531168, 42340060531168, 286431641864672, 75325409397216, 75325409397216, 30916301107315177451562693102524738311359885656494414013393913800126395723055075122550670243286523464367444507944608203660834478319402246508679099212794470710464519633335079, 286431641864672, 30241891346774209584618225202593991333512676412127437128984832567538822846275233441348356, 286431641864672, 6065825854489778447182348832559552717699197346, 698280705420094741215895973957787733502370, 11774838403385100911477154366332408896395717026, 1382417966012613300399867264983484115362, 2788975567782340505992364651346028672362914, 16609467118804844869823679427616253104802928637833484915550320801681896194424704608528385554664809989, 2788975567782340505992364651346028672362914, 730753607641019241442348408722792855856638634402, 42340060531168, 698280705420094741215895973957787733502370, 42340060531168, 286431641864672, 75325409397216, 2788975567782340660734869562018571624688034, 75325409397216, 5576568717598668553426834346099616812935586, 286431641864672, 2788975567782340660734869562018571624688034, 286431641864672, 5709013931313288476908106523935931520886286754, 11418026480208610941202912057708787699582806434, 1382417966012613300990163075342189767074, 2076211109836584628390139517628307958586859465956466369784551546374158826700158551890658354909690373, 45672101773580545726971745260345924771761924514, 16609467118804844869823679427616253104802928637106148153871512246061695482983068533959917084358397445, 365733616434895093697822797896444706734245718434, 2788975567782340505992954947156387378014626, 730753607641019241442503151818001590558110296482] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_4 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨1, 0, false⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [567906886814176] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_5 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨1, 0, true⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [567906383759840, 567906484357600, 567906383759840, 40140802427360, 145694019291616, 40140802427360, 4956396718560, 2788975567782340505991774355535678556645794, 5576568717598668398683739139616723744893346, 145694019291616, 145694019291616, 2788975567782340505991774355535678556645794, 730753607641019241442503151227703528399590959522, 576702510402016, 576702845946336, 576702510402016, 567906484357600, 567906484357600, 576702711728608, 48937331722720, 435965357591008, 48937331722720, 1382417966012613300399867264992074049954, 84121636702688, 435965357591008, 84121636702688, 154490380880352, 182710353924550983818617544710976508397141120483, 154490380880352, 295227869235680, 435965357591008, 295227869235680, 576702711728608, 259538268723564101383123354280827509765955511524797017061549188253899824044458960238697879327257157, 483067420946489370694743829285009835865566783940004056656988978690593926856071143018565169545161826230609757387994146778608380499786091581239781180553154115584539262335783, 265750994741119924833730082983207179386720559314538916640949528725409992844010603945997556614103576901, 265750994741119924833730083090543136972576977621239392373516897438422148218427698042933000278751853413, 33218880282637318031624155749479900621519447574136422556371477310963949090906670224849459182648158853] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_6 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨1, 1, false⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [567906886814176] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_7 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨1, 1, true⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [265750967021617344000308965266158389046395325301287489066077182012097163596773526507026911235509811972, 265751980781089470525992601965913465611168466819256995589800726443479870660042938559680220796937218820, 3960481339868517818399629397050995783418646721946957243114047186045128534297696947052727204612, 150268045732305672584440111419958720616473688347217534133924782951909248694548266110113946242962772396868055966776260581571280786172023362901999590490664382901004156345623161775333065853167593183293032424003953831700438655753075591934055638081718556650814347608194396505840597288263957917125485146626067967428701238357434976451247770403377840675760039474662332749826495405052843964586099030874399900619680846866038246718744881800370336457064102779126791641069940185960734565771450478909784862239845492076, 3960481336180482343314846863977329819683372547618013009601001063668640912683995843108464196356, 483427690525192287248710298826384481511384962986806468713009135624638853678117842043763460, 483457194808992965508974888154094363704779594540674573081988147525611763286949396147829508, 16625655590858292366541064616251525667591997689475138620753907735534739989627131092535278951485111044, 33218880282637318031624155749689541166803210995007650876515342353336229029458246274690307961751972229, 132875483511050356341133278098443285083283145009204621803365472374261681103494934825606364562141182724, 265752994540561597051676238665668542175941608337240707909650810106357127010996068991122245132651559684, 65007327600308031691608787682725285792801823290276711344245777004900370096477080779506771888929540, 132891705642603338685085515893106120032571090633239691672633996876594829825058856270396282965436103428, 259775869083005907808573999726931333843882772942634880490519816815895911084346415406611850298083076, 33220901862067590209327944458270957740509290921908559263953744956279244293751464543258856445598464772, 520058617418676949843129038542682319851692388550602704847569134095802623499116158578869344774826756, 16609435439304295615868940556039298683716461415473795113345660539363257628849891994283288338271271684, 2078206949280259958778850734896330704260339985769468058017761452583766951402070835595709972045069060, 16625655590858292366541064616251525667591997688384133478235694538726735273943866197108494946022947588, 33220898397069394464367111715644841756157038973360821638196182624204339941948873645823119227639528196, 30427572052773918099265946674688259281268121188081189948740938282829597836660556597104294238600178567147573668731623037312429716970090775732710392952069094774900804576294, 64888530079631201506990441121475482463165325980544124287311517905316472356072418083786674886421125, 121002670260808502804912442464487476321699161605163895898094888320279692523085014913376860902512737342943665187130101933265309299303393185217918785979428144766137731408934, 129777056291368813877625785631027225051616373692799844715657363271940315945392066818780196766787621, 519052800662613212878458459047065614372399637728462875720651096697792643946610818668402527570025861, 61840148296726225674720215193571455016868438081426231739800499169265162717297055511275048813107189695065098464013091859360453412353834180028392228531363499480028173459940390, 33218880282637318031624155749689541166803210995365636954907354882529479795121212037548215667494021765, 65007327600308031691608787682725285792801824381281853862458812311703297093029389487516241380997892, 259775869083005907808573999726931333843882774033640023008732852122698842781202380816280955913717508, 520058617418676949843129038542682319851692389641607847365782169402605550495668467286878814266895108, 2078206949280259958778850734896330704260339986860473200535974487890569916001052397916996530525666052, 483457194808992965508974888154094365159453117898291684322389570408883911876698982034144004, 16625655590858292366541064616251525667591997689475138620753907574033538501759852534722721127423245060, 33220898397069394464367111715644841756157038974451826780714395659511142868945425954531128697131596548, 33218880282637318031624155749689541166803210995013333199961673420693431850018579910282806866149698181, 132875483511050356341133278098443285083283145010659295326723089485502087339489079715754622955822480132, 259538268723564101383123354700108606581257424239964680803401172167250382137955312976878597848478277, 966134841668032944390044223382309430397194568936482259003078508911706297017568290896340645723835853497375730671953320991646791523881947773428876557933195599803439873965223, 19799989926005477801951256207395412274235809875722313525934655493255122048071350868650624036517, 265750994741119924833730083090543136972576977667788944427318271511056939168118338935032354050859350885, 33218880282637318031624155749689541166803210995729305319489516031716942494428200955208587553084009093, 123665200794139242296180698065861856109474691773861889269709599184236333502155665052550023017352596013939399142376210189415300969854130792014866243439358853193384210668741670] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_8 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨2, 0, false⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [576702979901920] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_9 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨2, 0, true⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_10 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨2, 1, false⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [576702979901920] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_11 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨2, 1, true⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_12 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨3, 0, false⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [567906887010784] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_13 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨3, 0, true⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [40141305743840, 145694421944800, 40141305743840, 129769134362136116504877348293895818029162603708883541253324689883584443898980093328425764349225605, 84121770920416, 365596244314592, 435965357591008, 365596244314592, 2788975567782340505991774355535678556645794, 435965022046688, 435965357591008, 435965022046688, 295227600800224, 45694314087906761176943041732138190185791771107, 295227600800224, 2076211109836584628390139571243877065033939099764739299177129039312819200673179790490690514922201413, 435965223373280, 435965357591008, 435965223373280, 84121770920416, 2076211109836584743641248289785153869946921871910553799889602910015245611557825598865596723543948421, 2076211094367842798351244557378280912531932152379588680383778629473272219958387200599578519940381541, 966134611154937396483019560688312186199966075323658687051365290736375186775073595800138397110553309213857838509953171509520095741045631232681920391347798714199686364412711, 2076195269844596732407035871168059743916553420796208256027603461621967014662784862888581177943169221, 1038097634922652532861553625442425897793946075242193704643632485310323137987283623761252846681664133, 1038097634922652532861553625442425098078731217136055808367528119273207634150972459917959180939438725, 145694421944800, 145694421944800, 295228003453408, 435965491808736, 295228003453408] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_14 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨3, 1, false⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [567906887010784] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_15 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨3, 1, true⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [259522429214974276387664824788162192650597395996647205241791463317759333029190091953306052232182532, 519171577882454514033190334913924042648626020344068839326093365315615713500033182586421368499436292, 535265009515681028403626804124300527236274842159639693450894851985272642379487063710801360908942084, 519298297818358603906888331040242330218701170469289298754912502789929514331137044780235802516342532, 520058617418676949843129038542682319851692388192616642458780428893176174871921655501808201577442052, 519044857946550424159492338787605755078550870220268959509928473961621423106960733191412020145257220, 521072376890803475526765738297758884624833906176328962308864091770432488222622833330555448303254276, 535265009515681028403626804124300527236274840886800337481885114366218559248898300898400591987047172, 520058617418676949843129038542682319851692391096281370723399281904735110002903729609539008153692932, 521072376890803475526765738297758884624833906517268069345805718296391306790803068595643702184213252, 1040243954289889077100147949684593489998372475918436932394410153137973560773211435658544912799070980, 2078460389152097412307830212610323551624077434393578752418194915282077690318843712202895801399592708, 483427690525192287248710298826384481511384962986806468713009135624638853678117842043763460, 132875483511050371093275178437573417377946999950483153309562108282724122996648965564371031653115722500, 1038105554918292371821943007969194261148673582484085071200669989022395173154558533856761401843814053, 519052800662613212878458485461774320126590758431691028593529911536148561581800816555435300541491845, 2076306150271910997285275331512495862284132099596268827998049099602992523786607811598077397004679940, 2076432870207815087158973327638814149854207249721489287426868237077306329318015330493551467145152260, 2077193189808133433095214035141254139487198467444816631130736163180552985158496284513464230082685700, 2076179430336006907411577335386177574714056949472468948181884208248993420282590899703600658118834948, 2078206949280259958778850734896330704260339985428528950980819826057809336111626715955488565797026564, 12793523169845683504428438182472894639945152882098175794782682951149908273703358138214141764692832155986568913838586815336389322613483386834093095061035501593712082148703691261578217860962628197971199132721867417811023577212816167988903997381605244268950359784427930339606422997583567804559695668681749712085110160869889484941995815235395666295042122990959288924936030560042, 2092399581920243704961659069978342082659240603157051681734310285570849763653036678538041557806971652, 2078206949280259958778850734896330704260339985769468058017761452583768117077377697607299730689456900, 2092399581920243704961659069978342082659240603157051681734311234390408504873298205686818774170434308, 2076179430336006907411577335386177574714056950927142471539501319489399656276807510792817634536815364, 2076179430336006907411577335386177574714056949472468948181884531251396396017148015328716306242566916, 2076211094367842798351244557378280912531935131550920123671719278099893000159404294958219934820219749, 2076195269844596732407035871168060143774163829020607942973055471685070951319980857671906072048081093, 1038097634922652532861553638859420795954805057186690544198110613501900963365250366745468554576079493, 1038105570387034432363055315261160267032419572323590768987748313180774842814960522869396949505683109, 33220898397069394464367111715644841756157038975906500304072013416756350243297812334371109579265374980, 33218880282637318031624155776104249872557402118614543757398821240229834670003590046358855245813836421, 132875483511050356341133278098443285083283145012113968850080707242747294713841466095594603837956258564] = some [] := by
  decide +kernel

private theorem solve_1_0_0 (N : Machine4) (h11 : N 2 1 = none)
    (hAlive : ∀ q a, ¬ (q = 2 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    (hm : Matches N (baseTable 1 0 0)) : CertProp N := by
  refine branch_one_sound (tb := baseTable 1 0 0) (q1 := 0) (a1 := 1) (rem1 := 103) (cur1 := ⟨0, [1, 1], 1, []⟩) (step1 := 4) rfl ?_ N h11 hAlive h107 hm
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
private theorem tv_1_0_1_0 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨0, 0, false⟩) 103 ⟨1, [1, 1], 1, []⟩ 4 [574503453723104] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_1 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨0, 0, true⟩) 103 ⟨1, [1, 1], 1, []⟩ 4 [576702644259296, 572304799435232, 576702644259296, 1462934465675714879804403364132941373278365198754, 572304530672096, 572304799304160, 572304530672096, 572304799173088, 572304799173088, 572304799304160, 44539218037216, 431567310948832, 44539218037216, 431567310948832, 79723590191584, 290829822593504, 79723590191584, 150092334238176, 182777256287751489725723865381645966064889106915, 150092334238176, 290829822593504, 290829822593504, 290829822593504, 9354845882848, 572304799304160, 2972070918279654164196630419780413142243457313883850023267248466653394763023737761333663566617754262246483360540917583001270393765946676794778201714091180795748459207820574503, 323896152432070911092478851761054462487150931704855440559903620621996610857748176714515182709323844, 1427253158512328944933147487090191532056160674, 79723590257120, 290829822593504, 79723590257120, 290829822593504, 290829822593504, 290829822593504, 9354577185248] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_2 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨0, 1, false⟩) 103 ⟨1, [1, 1], 1, []⟩ 4 [574503453723104] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_3 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨0, 1, true⟩) 103 ⟨1, [1, 1], 1, []⟩ 4 [574503453231584, 687347677883307202663272245806742264519107723975518467685908356099061399176716892273660584863570429066278153276311371025976339603166299296015109953955836725994225253325273980105893942357023715490316185444219333402438263991448777692670723319955109986564114561640, 64943970054067600678300434409136454724796539274291310610535599684592247900543273202026083003411077, 1205316250024985675779068623608730739829912961008601372014265400126348333662513560759119710242043522560894810582285038197321744159822565119006762081399126993688391189565377392418491327364894540633405486353679499809398173268210274615330918764567177192528779885252470843093027568253480019652980160613465633451360543351681075132527582343669431984890041889612378002857208832060196310346769370119322736644252801868252950485312261725149857296622753727664488052504080285670098455816514453367070405755722322913173926195109013853252944283434425645589071896714645114462483420229687427814392548773724848702480756267553219091601129794834671973210116274397726895575094727043848397178388032601075238025744329900489334633403935758259485836032950370177172803941037170042039883281493245904275449984113679732207578761888969121084394248613552, 129824574336572515676187328583842190401479767936019778540117840590712182682366859920419706538568325, 519108240637049612049768452334726393343488197329741907401413946489572651360706374696221919463352965, 21994476493043252875143087619635868703495745051171754993898232258711935440573635816920096848433215880794603184155689090593427109754859947058863830638071938170788389082394550494317554170460971436644771709658317335541181118690127995349941430556044161024887045116412989141827443212650492222374586435136847095508985677710309808643227908671405719392241571339794675837900362510516780922621405097228503837199008190366555800814855276338069709683683152032193741399926207664600135876678904409026783934345887879905739945214770859910159092444277886823865979982403569913775186766686735814128551291921497764651809626171592450329610742005529300443249394799689980362348334, 1038153074897088932032863605732372269385291352505138363877348951204871831705807208702123092266986117, 1978884774864108052658285266367593821593352909391604809670510115265691220574203314169639153612934106872627496090783252910206613831946014641649395174676570863493445560434665255, 61840148296725786327669992407913822457121182321652677743612233407688005121566454131978979637673480764824325220936087858862344226276509816374614213821528134197981548991374374, 1978914966563506624989103301097698224498913682673548811280285792680552932074509253797470409280002724354751823268271574122753151123503189092417840625875395146596817352526898983, 129824577236961630418063025634031461984224852156814686946946517142400608336168373986733011625585285, 66437805115254270909713555560426538411526337025735532910725499072383166564691069995104669641065723525, 574503453231584, 572304396388832, 572304396454368, 46737872194016, 431567310948832, 46737872194016, 9354443229664, 290829688375776, 5580652106001719660245299634905904963430818, 150092065802720, 150092065802720, 290829688375776, 290829688375776, 290829688375776, 9354443229664, 572304396454368, 46737872128480, 431567310948832, 46737872128480, 9354443229664, 84121301027296, 290829688375776, 84121301027296, 150092065802720, 1461501642796709287267559694086350889366131354018, 150092065802720, 290829688375776, 290829688375776, 290829688375776, 9354443229664, 5709018014701691528169666903839740722181876130, 431567310948832, 11418030563597013992464472437612596900878395810, 9354443229664, 290829688375776, 150092065802720, 7729078735143829931115901268560157373508362890335034632896165511963062957643175145708304531248121983138425432118760427509842045819930692682210377794743384112646592073972519, 150092065802720, 290829688375776, 290829688375776, 290829688375776, 9354443229664, 46737872128480, 431567310948832, 46737872128480, 9354443229664, 84121301027296, 290829688375776, 84121301027296, 5580652106001719660245299637157704777116066, 150092065802720, 150092065802720, 290829688375776, 290829688375776, 290829688375776, 9354443229664, 46737871899104, 46737871899104, 9354442967520, 79723187210720, 290829688375776, 79723187210720, 290829688375776, 290829688375776, 290829688375776, 9354442967520] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_4 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨1, 0, false⟩) 103 ⟨1, [1, 1], 1, []⟩ 4 [576702510533088] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_5 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨1, 0, true⟩) 103 ⟨1, [1, 1], 1, []⟩ 4 [572304665348576] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_6 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨1, 1, false⟩) 103 ⟨1, [1, 1], 1, []⟩ 4 [576702510533088] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_7 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨1, 1, true⟩) 103 ⟨1, [1, 1], 1, []⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_8 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨2, 0, false⟩) 103 ⟨1, [1, 1], 1, []⟩ 4 [572304531130848] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_9 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨2, 0, true⟩) 103 ⟨1, [1, 1], 1, []⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_10 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨2, 1, false⟩) 103 ⟨1, [1, 1], 1, []⟩ 4 [572304531130848] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_11 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨2, 1, true⟩) 103 ⟨1, [1, 1], 1, []⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_12 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨3, 0, false⟩) 103 ⟨1, [1, 1], 1, []⟩ 4 [572304665348576] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_13 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨3, 0, true⟩) 103 ⟨1, [1, 1], 1, []⟩ 4 [48937331853792, 220461078186464, 431567176862176, 220461078186464, 702364093823146002776866173436610246388130, 150092199823840, 431567176731104, 150092199823840, 431567176600032, 11507206491950754676251767383924877213124548067, 431567176600032, 259775868603384255502228722203483252977133143688870629949178979302931312893921502406789141361549637, 431567176731104, 431567176731104, 431567176731104, 48937331853792, 541518540605920, 541518540605920, 290829688375776, 290829688179168, 290829688375776, 290829688179168, 60387084310841644023948213376439500493301800204898505295103883812209267943211054830741088862359597849003455517223447192264429698121673900715911644673896299972664871238439, 259649148667480180034919253667615041502878011657981562093605446081300993687444978898650920468256965, 290829688375776, 290829688375776, 290829688375776, 290829688375776, 79723590322656, 290829688637920, 79723590322656, 150092200282592, 150092200282592, 290829688637920, 290829688637920, 290829688637920, 9354711927264] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_14 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨3, 1, false⟩) 103 ⟨1, [1, 1], 1, []⟩ 4 [572304665348576] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_15 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨3, 1, true⟩) 103 ⟨1, [1, 1], 1, []⟩ 4 [46737871899104, 7225468688201773901832781524795950798197533090, 46737871899104, 46737871899104, 65894367155413212285379078563618307378100722544880718054038748332294413788998281218032899186666244, 5798220995495814020890552876748503088291162530, 66908126642645931274963047574164607938701923535279756583360463183511085300019754988049084250815236, 46738006215136, 46738006215136, 5798220995495814020737018707365997678014015906, 46738140563936, 81100758980505811338825997546781270588408882368813535986310539221612976582038606835038499984603908, 46738140563936, 46737871899104, 64943970054067600678300461190716114725573648490980481006137050318156333415066171229824561279937157, 483067190602981676921224398453982541432875383033474201630295179452340083961037047403410225472225326457068926983319024381868574783029628088461423037606664203062910273479718, 458229454617168379741452607355324838325471624237070485829486569196560426531251764297183794506725036064374245794192381253931455853382708234248500958453787053575988363246870162185273148350221741339707479067415266495401006655022215142534814292321958367240075938761, 64943970054067600678300461190716115897031482755784305170930083747801094012871018111767808527313541, 129887934301692134961782645767757249766727951629359876787596924296815351532520512117636896747589285, 64943970054067600678300461190716115897031482755784305170930083747801094012871018111767808527313541, 46737871899104, 259522428735352642075236526609795656046660385260619740657571885969633450626004891911697567279446788, 46737871899104, 46737871899104, 260536188705983546855133111795373501805971442828662136085591895206021327971072492459550843410230020, 319714395593339825169398552690892542685819892500289614731050179372476488430690044370950242588873060, 261549948193216265844717080805919802366572643830425811516144997523988045470258871089156271115565828, 11507233544391136485030615319926421663448607138, 46738006215136, 46738006215136, 46738140563936, 261549948193216265844717080805919802366572643830425811516144997523988045470258871092487688268512004, 46738140563936, 46737871899104, 46737871899104, 46737871899104, 9354442967520, 9354443033056, 9354443229664, 9354443033056, 259649148667480180034919253667615441360488420609718010717866173265535188889209847271464120885352645, 9354443229664, 9354443229664, 9354443229664, 9354442967520, 290829688637920, 2076179430366219297174869374579914620936884243505021759477419312792900346229026441062168658151963396, 290829688637920, 290829688637920, 290829688637920, 9354443491808] = some [] := by
  decide +kernel

private theorem solve_1_0_1 (N : Machine4) (h11 : N 2 1 = none)
    (hAlive : ∀ q a, ¬ (q = 2 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    (hm : Matches N (baseTable 1 0 1)) : CertProp N := by
  refine branch_one_sound (tb := baseTable 1 0 1) (q1 := 1) (a1 := 1) (rem1 := 103) (cur1 := ⟨1, [1, 1], 1, []⟩) (step1 := 4) rfl ?_ N h11 hAlive h107 hm
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
private theorem tv_1_0_3_0 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨0, 0, false⟩) 103 ⟨3, [1, 1], 1, []⟩ 4 [51136422218208] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_1 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨0, 0, true⟩) 103 ⟨3, [1, 1], 1, []⟩ 4 [224859258915296, 431567445297632, 224859258915296, 224858755598816, 1427950056799783026906320478286211793353222562, 224858755598816, 150091931322848, 150091998497248, 732178768722251242128903479784062503733114743202, 150091998497248, 732178768722251242128903479784062503733114743202, 732178768722251242128903479784062503733114743202, 150092468259296, 431566941915616, 431567310948832, 431566941915616, 431567310948832, 431566975535584, 431567176731104, 431566975535584, 431567042513376, 12845253755954057929825013057112123821304844771, 431567042513376, 275742580527299580474506727623464950312017727225180795672496154375267480884521278332060939788230725, 431567176731104, 431567176731104, 431567176731104, 12845253755954057929941259346963280439021699555, 150092468259296, 290725945376563824023234228029088749145688049407181007050315164030758555019106819012751542923164858436, 31135190019276168814610633519250245231912449702880775422466957705213925354096269579953248499351716633919037528453478735069087175116135190939957451849707848136034158787367, 275742580527299580474506728462027134570958788256754683365276762030213792450589364368783959983668069, 137871290263649797891086942922909973972735424929135055995588679576366288309446258483292186280048837, 12845253755953408892833942198397837779274858979, 12845253755953408892833942493545742924267946467, 431567445035488, 431567445035488, 431567445166560, 431567445166560, 431567445166560] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_2 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨0, 1, false⟩) 103 ⟨3, [1, 1], 1, []⟩ 4 [51136422218208] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_3 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨0, 1, true⟩) 103 ⟨3, [1, 1], 1, []⟩ 4 [65007327600367036685750478250439357481397421869627116068047781528535248425661088474816209138973444, 133816252495993256010506871710141320717938610121001559409754388005091143374346916736211348445997701, 259775869083064898424464593429381471201398450038181703350228015452945035642267500788984398730446596, 51135918410208, 21288498328859446103646977487382030754, 51135918410208, 558349945312, 84121300830688, 282033595353568, 84121300830688, 282033595353568, 558349945312, 282033595353568, 558349945312, 51135918442976, 150092065606112, 51135918442976, 558350010848, 84121300830688, 282033595156960, 84121300830688, 150092065606112, 150092065606112, 483457201561987609829255405256754212320805427258614301262948706874536986612447557119605508, 282033595156960, 558350010848, 282033595156960, 558350010848, 51135918705120, 431567310948832, 51135918705120, 558350207456, 282033595353568, 150092065802720, 150092065802720, 145981366161511564214147268771060108929243276040739602812995152990920325210429890814187128925400389, 282033595353568, 558350207456, 282033595353568, 558350207456, 51135918442976, 150092065606112, 51135918442976, 558350010848, 84121300830688, 282033595156960, 84121300830688, 150092065606112, 150092065606112, 282033595156960, 558350010848, 282033595156960, 558350010848, 137871292197242555458725981753686841047802779728570865807501743261576878905535983892172425790500517, 62270380017024332166623321123236904274457263219997494749044143598761118083426541878371643223549451651944840053031732488722994147514863084559276273543075775936205670767783, 275742578593706851719644838311832711099576806447881536648501777816494737321819713809977150430788453, 12845275534024891833514573874015403515530215907, 12845275534024891833514574169163308694883041763, 51135918639584, 431567310948832, 51135918639584, 558350207456, 84121301027296, 282033595353568, 84121301027296, 150092065802720, 150092065802720, 282033595353568, 558350207456, 282033595353568, 558350207456, 1467299870236271189863550965207566990523749144866, 431567310948832, 266269944550899610341996294908721098452459371448253039387298559764711434574805435576793240036905793604, 558349945312, 282033595091424, 150092065802720, 150092065802720, 282033595091424, 558349945312, 282033595091424, 558349945312, 483457201561987609829255405256754212320805427258614947267759452653381053556037887347358468, 1979030669470118200153928026302321407908602150307327547403999195704420012423184756006830543580446883299557313906417370976847997439056898193306281158171672332260453575436516134, 21288498328859446103646977487382030754, 266269944550899610341996294908721098452459371448253039387298559764711424983835966433318957916820289604, 558349945312, 282033595353568, 269448650735732557550881818166946417991490003296152292611595376882894918665056970036863139441751828548, 282033595353568, 558349945312, 282033595353568, 558349945312] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_4 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨1, 0, false⟩) 103 ⟨3, [1, 1], 1, []⟩ 4 [84121771051488] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_5 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨1, 0, true⟩) 103 ⟨3, [1, 1], 1, []⟩ 4 [365596244445664, 431567109392864, 282033729702368, 431567109392864, 730753606279889773758594554426572568360536549794, 282033460939232, 282033461135840, 282033460939232, 282033729440224, 47099263715111057119399001699772753076979504611, 282033729440224, 2092399581648332110653699217210520109548525283097975401773560865899650179093935289426900111001087109, 282033461135840, 282033460873696, 282033461135840, 282033461135840, 365596244445664, 365596243954144, 365596243954144, 282033326655968, 282033326721504, 282033595353568, 282033326721504, 2092399581648332110653699217105699837297129540329457687872746852591990868693155608271553978045733381, 1046199790824166113403043197488175756511293427530852629891105033752133696501093293452785473602654789, 282033595353568, 282033326655968, 282033595353568, 282033595353568, 431566975666656, 282033595615712, 431566975666656, 282033461397984, 282033461397984, 282033595615712, 282033327180256, 282033595615712, 282033595615712] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_6 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨1, 1, false⟩) 103 ⟨3, [1, 1], 1, []⟩ 4 [84121771051488] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_7 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨1, 1, true⟩) 103 ⟨3, [1, 1], 1, []⟩ 4 [65007327600367036685750478250439357481397418960990359159139551757195353329705750973694420660222724, 16625655590858349541445520218338551768971847348187784957709051662462548826710949986437345168850123524, 130014654717276867757716560079454999444444721085804776366949082597881350044534125489237899397777156, 65007327600367036685750478250439357481397418960990359159139551757195353329705750973694420660222724, 520058617418735853739313408098863483415884544120912693880292567261986784445967689048115070917323524, 132875483511050400604311973760153962484377369678202102826505306675229576255869621212960964074389338884, 1040117234354014502315042062730988619120262961119428031542768813987474758164594685172462900814772996, 8320937871447915578773646083943257576526808881388414072949326665104222023125079162638262912152730372, 483457201561987609829255405256754209412168670349706717496424370668370178553849126749174532, 966370253462994785343189305807873548535680297523948609774955934151555639140227645462806687696583944557960946474992215043530031932008232583177419161528375652483599912428582, 1042144753056509672367183149225542354729308069078897237123899039604392632418253696744153755079682693, 1932504634386032368404443214339980820593878862517531842902426823284476155451135765904020972839693154626471310757040507738063700937010964391424827919731514489086948009600038, 1046199806292908173944155511436229231348904523609011680237690166213645415599298543668048871742810149, 1042144753056509672367183149225542354729308069078897150418601707717329855777372561171265729018735237, 1046199790945015775101729948245848620069649257025312222560101826299349030092328778629549429778853349, 47099350827396826622844888083549640642269315555, 47099350827396826622844888083549638447541027299, 65007327600367036685750478250439357481397418963121228578120436591778952796495892201639751655324420, 1980482426198682463462758464539172326751441578183058723220659515116371966485687230260342651652, 259775869083064898424464593429381471201398447131675815860300670516188740013102304515807941246797572, 483457201561987609829255405256754209414299539768687602330998343913271394782861764035050244, 520058617418735853739313408098863483415884544123043563299273452096570383912757830276060401912425220, 2078206949280318747649026329530400393175892769471480261556715323491848681645609128790466294526999300, 2078206949280318747649026329530400393175892769471480261556715323491848681645609128789405918641224452, 483457201561987609829255405256754209414299539768687602330998343913271394784997127285340932, 16625655590858349541445520218338551768971847348189915827128032547297128214705663722978189737798630148, 132875483511050400604311973760153962484377369678204233695924287560064164630844926563074565344276478724, 65007327600367036685750478250439357481397418960990359159139551757195353329705750973694420660222724, 259775869083064898424464593429381471201398447131675815860300670831620774169093082949035593246918404, 483457201561987609829255405256754209411458380543379755779742866572220947001190018020768516, 483457201561987609829255405256754209411458380543379755779742885373435573807832737223244548, 483457201561987609829255405256754209411458380543379755779742866572220947002258743322966788, 483457201561987609829255405256754209411458380543379755779742941777079454227752545414249220, 2084289505750470473988136060687041696147731654746467457287494220239690022790295050963149818987221573, 47099350827396826622844888088161324461673447907, 483457201561987609829255405256754209411458380543379755779747679683165409501191771203533572, 47099350827396826622844888088161324465968415203, 520058617418735853739313408098863483415884544125884722524581299278699536986464133118614877038095108, 483457201561987609829255405256754209411458380543380078782155468528666987627377897812228868, 2078206949280318747649026329530400393175892769491368376133870249350646574049992681035603233536703236, 483457201561987609829255405256754210866131903900997190022556891411939136217127483698543364] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_8 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨2, 0, false⟩) 103 ⟨3, [1, 1], 1, []⟩ 4 [150092468718048] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_9 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨2, 0, true⟩) 103 ⟨3, [1, 1], 1, []⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_10 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨2, 1, false⟩) 103 ⟨3, [1, 1], 1, []⟩ 4 [150092468718048] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_11 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨2, 1, true⟩) 103 ⟨3, [1, 1], 1, []⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_12 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨3, 0, false⟩) 103 ⟨3, [1, 1], 1, []⟩ 4 [282033864051168] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_13 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨3, 0, true⟩) 103 ⟨3, [1, 1], 1, []⟩ 4 [558887340512] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_14 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨3, 1, false⟩) 103 ⟨3, [1, 1], 1, []⟩ 4 [282033864051168] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_15 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨3, 1, true⟩) 103 ⟨3, [1, 1], 1, []⟩ 4 [558887340512] = some [] := by
  decide +kernel

private theorem solve_1_0_3 (N : Machine4) (h11 : N 2 1 = none)
    (hAlive : ∀ q a, ¬ (q = 2 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    (hm : Matches N (baseTable 1 0 3)) : CertProp N := by
  refine branch_one_sound (tb := baseTable 1 0 3) (q1 := 3) (a1 := 1) (rem1 := 103) (cur1 := ⟨3, [1, 1], 1, []⟩) (step1 := 4) rfl ?_ N h11 hAlive h107 hm
  intro m hmem N h11 hAlive h107 hm' hsum1 hrun1
  simp only [moves16, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkTree_sound tv_1_0_3_0 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_3_1 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_3_2 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_3_3 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_3_4 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_3_5 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_3_6 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_3_7 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_3_8 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_3_9 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_3_10 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_3_11 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_3_12 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_3_13 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_3_14 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_3_15 N h11 hAlive h107 hm' hsum1 hrun1

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_0 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨0, 0, false⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [1461518373842650967241640947978193853861451569442] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_1 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨0, 0, true⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [1978643211900009344325130447387260592234061569810792723141069077064811340884380038694121845808185314919695538719846318716820182234050510663748470842289699606233639794330461222] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_2 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨0, 1, false⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [1461518373885186263106758255911115679790489704738] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_3 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨0, 1, true⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [564607848581600, 1461507212538491049188329662749498159233691068834, 564607848581600, 563508303366624, 565707393796576, 1461507212538491049188329663192220017002720307618, 565707393796576, 45638595414496, 45638595414496, 290829688375776, 81922479163872, 290829688375776, 81922479163872, 1461501640074450351900129357926956145458612840866, 290829688375776, 290829688375776, 290829688375776, 9354711665120, 5798215891260310206668529380442092315293559202, 702364093823146002776866173436610246388130, 11507228440155632670963334914214948493990078882, 558349945312, 282033326655968, 16609451278812856858591225770455755058574664728402918164399612557994039335614283634008626020390692357, 282033326655968, 558349945312, 282033326655968, 558349945312, 45638595414496, 702364093823146002777456469246968952039842, 45638595414496, 290829688375776, 81922479163872, 290829688375776, 81922479163872, 5580652106001719814988394841388798031473058, 290829688375776, 290829688375776, 290829688375776, 9354711665120, 35742722034144, 35742722034144, 558349945312, 70927094122976, 290829688375776, 70927094122976, 16609451278812856858591225770455755058574664727675581402720804002373838624172647559440157550084279813, 290829688375776, 558349945312, 290829688375776, 558349945312] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_4 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨1, 0, false⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [564607848614368, 567906484160992, 564607848614368, 563508303432160, 565707393796576, 572304664889824, 565707393796576, 567906484160992, 1461507223427526790658669978439733059898334816674, 567906484160992, 5720173831818827575065335191402744529902676386, 183045224398151048626898110514549602244086507938, 11440336753313415350930908588923610907779574690, 5586096623872454985145723450040242402273698, 22880662596302590902662055383965343663533370786, 45761314282280942006124348974048809175040960930, 91522617654237644213048936154215740198056147362, 183045224398151048626898110514549602244086507938, 732180864861631475109993156676552774520268695970, 572304664889824, 51136354650592, 150092199823840, 51136354650592, 558350010848, 84121636375008, 282033326721504, 84121636375008, 150092199823840, 16609451278812856858591225770455755058574664728402918164399612557994049709184299396332648350592427525, 150092199823840, 282033326721504, 558350010848, 282033326721504, 558350010848, 572304664889824, 37941812464096, 37941812464096, 558350010848, 70927094188512, 290829688179168, 70927094188512, 16609451278812856858591225770455755058574664727675581402720804002373848847332948548590443082376728069, 290829688179168, 558350010848, 290829688179168, 558350010848] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_5 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨1, 0, true⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [265750974941613338005477630300065905616797038484469579321684123694553741885876361654183641967388075716, 41240448272864, 145694019291616, 41240448272864, 145694019291616, 732180859417113604374822998314928706747976690082, 3959997997002809432412237676242979685601467914916812209845379777590149630630262471192940346116, 145694019291616, 145694019291616, 366090429719201051351841222209290093921788029346, 21288498328859446103649229295785650594, 732180859417113604374822998314928706747976690082, 21288498328859446103649229295785650594, 265750998701600847953793413639492216780109623921349446563386324356541859182596344895270565726966497412, 36842267544032, 145694019291616, 36842267544032, 558350207456, 290829688375776, 5575207588130984644829885641186996672047522, 145694019291616, 145694019291616, 290829688375776, 558350207456, 290829688375776, 558350207456, 265750967021617343999858765623203703678588481311570869321118360788168300582181622088246522251631098628, 41240414652896, 145694019291616, 41240414652896, 145694019291616, 77524298369504, 295227600669152, 77524298369504, 145694019291616, 145694019291616, 295227600669152, 435965089024480, 295227600669152, 41240414652896, 145694019291616, 41240414652896, 145694019291616, 77524298369504, 295227600669152, 77524298369504, 145694019291616, 145694019291616, 295227600669152, 435965089024480, 295227600669152, 45638595414496, 549134249410452952015593224947563525691440949666, 45638595414496, 290829688375776, 81922479163872, 290829688375776, 81922479163872, 91522609487460838110293699497221137458074270114, 16609451278812856858591225771241907103388777557921554829662738311254080729628609771134402191060644165, 183045216231374242524142873783768023209266424226, 290829688375776, 290829688375776, 290829688375776, 9354711665120, 702364093823146002776866173436610246388130, 558350207456, 18948459854494228631013627833752970782640611574467717521525051411810449357437460269833560843921500333622370598278425618207757373051041609114782919588291916705696218121377998076285134523142411940872918816134843152054670426962153557771744998628066594030485273147063474351208963988989274795695790405048912537301730093418441906465405759838843077306315091900846366829064329759137643186413877305507412324017047473906038097195248689398324692494832653377736148775751358533908973739604118009603065294039769962714988, 290829688375776, 966141752000551006513592284146989416041905142024517689923300548688882858064807231929358227231265939880511641796706075576137223758612249641437278464906395566149781223531558, 16609435438851082159575856843189006132245850839463402221502635183467790198899602310251732631844780804, 290829688375776, 558350207456, 290829688375776, 558350207456, 45638595414496, 702364093823146002777456469246968952039842, 45638595414496, 290829688375776, 81922479163872, 290829688375776, 81922479163872, 5580652106001719814988394841388798031473058, 290829688375776, 290829688375776, 290829688375776, 9354711665120, 7147416080006916720953463832245998351402707362, 11440325864277673880590592741891385625194572706, 558350207456, 73126117640672, 290829688375776, 73126117640672, 290829688375776, 558350207456, 290829688375776, 558350207456] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_6 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨1, 1, false⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [564607848614368, 567906484160992, 564607848614368, 563508303432160, 565707393796576, 572304664889824, 565707393796576, 567906484160992, 567906484160992, 572304664889824, 51136354650592, 150092199823840, 51136354650592, 558350010848, 84121636375008, 282033326721504, 84121636375008, 150092199823840, 150092199823840, 282033326721504, 558350010848, 282033326721504, 558350010848, 572304664889824, 37941812464096, 37941812464096, 558350010848, 70927094188512, 290829688179168, 70927094188512, 290829688179168, 558350010848, 290829688179168, 558350010848] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_7 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨1, 1, true⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [265750967021617343999865799992624870637460463248912988270745754463285590748053512468632625710095366916, 265751030381585296044809683319858212045634914752997139179161367427345092886728109835672256990035331524, 3960481339868067618756674711683188939428932943361223729413667175532143123211074180804687133444, 259522429214974275937465181833476824843753403373521572793042894452140022808120616980772145903926020, 3960481336180032143671892178609522975693658769032279495900621053155655501597373076860424125188, 535265009500574838249077035551628366096723087138038414973926996572693111488305949436991188684208900, 483427690074992644294024931019540491797606377253292768332998622639227767055351594003692292, 2076179430336006906961377692431492206907212959758690362448370507868982907297180933720536887934024452, 483457194358793322554289520347250373991001008807160872701977634540200676664183148107758340, 33222925916013647516184584758109680253510165999007930952926169735237327684365533411561814320319838980, 33218888202632957985837412327679552727561817589904427844845061529590573440151305739729889350624863813, 132891703662604380755222862795207307694301317226122391258829470896872762399296882619103281384512518916, 66437757595275474464755502145128888994166023235656379574245891438263947774566960547684239888483264069, 265751220461485375631335949753511808490757622189799487259262071596173589689207294803229869070641219332, 259538269206726253801671291176520631782021719382976271419759317773893729034953106435968866868233156, 33222929876072010283649325500738992770008581806815180825611418316300655181122253934705688406912739012, 523099895895481300568027817533491630645231655917069970180970173735671816570415128733164751176935108, 33222925916013669644397435266804878695505948410652976926591570571262263321323553603924201792703838980, 523099919098594333754141990334459958735366138371270089561532575920650465564117423584724137507890884, 33222925916074072289408373794880574502177436722760623539031347079643621636205007194779131586388240068, 33235092514920099044796285625906586049128009929356260506199922675936438381044784449304683362548459204, 30199070421569821742383410886601382247775885074152840169468076790906334960362738591102740126730323504351510543793792659956030631957761904713021244248454557817917915292710, 64896450075271155720247019111487043221771920877321092617030694159660883049131883123368063759297157, 60390769832445157117138079976556775311810231693009384549057653222103123561118933956240348419473887664311158272911986242204761381342372859189267311811055353467283331245094, 129777056291604848149789804068435685639066124752834643657020496407903925207132750412453026561304613, 519060720658253167091715037037077175131006232625239844050370272952137054639670283707983916442917445, 15839991988011238608730836402760084253131469544228901190722617674712710681637499779484213062277, 66437757595275703122954957428060648485882089234699278947690626262522869035975968837244213386412697637, 132875515190550934177364707523055731234101645379854734553033844765699269497140215813109420683246678597, 259554109198478233466675972338305909947665994974882074659339501988893918313262551288462742822305924, 2092399581890031321501162032150200185732229166390238403645882569358868490311245901056005026610379524, 483457197960390466191772462802002293155903218032887586982463161306761518236062718314642180, 33222925916013647518885782615837792460351229938381607609845464730572391457473634403287584541959535364, 33218888202632957985837412327679552727561817589910110168291392596947776260711639375322388255022589765, 132891703662604380755222862795207307694301317226122391258829470735371560911429604061290723560450652932, 132875515190550934177364707523055731234101645380582071315050022876246192487428581882402668074203591237, 132875519150548886923747559675380240981883493427918649087200635590358967375899519164636285801994629701, 259554108715552112619094196571190132245512395439274434757900636908907972462357716449280166089241157, 259558068713490135672823158865431125001520843360984378415148534406261083639765706120453589704946245, 519060720658253167091715037037077375059809947515444411388423068147192692330010326748567320894747461, 35639981914016713772793127288921076529207736522227109994887124658100383741041284440796799449285, 15839991988011238608730836402760084253131833212593483351871805137412017670548593902982621309573, 66437757595275703122954957428060648485882089234699278958531434545444529844187858397604985419962394661, 132875515221488403776807249004725434466363466727363822018853832408480456455518066501218431755714015813, 132875515190550934177364707523055731234101645380582071314711330464997797589837934264017736475891446341] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_8 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨2, 0, false⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_9 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨2, 0, true⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_10 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨2, 1, false⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_11 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨2, 1, true⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_12 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨3, 0, false⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [5720173874343738846465536866116636605787707682, 1461859157062691102055122340174315968105951570338, 11440336753313415350930909760292915123525299106, 36842267478496, 145694019291616, 36842267478496, 558350207456, 73126184749536, 290829688375776, 73126184749536, 145694019291616, 145694019291616, 290829688375776, 558350207456, 290829688375776, 558350207456, 22880662596302590902662056546111275842424319394, 1462931683527082934211835573624991150242129815970, 22925351539257566236413130635741758442607515938, 91522618334791993461208756753581730932095752482, 1461501648241227158002884595690757574060558821794, 183045224398151048626898111547568325907010595234, 291928965122528, 295227869104608, 291928965122528, 290829688375776, 293028510304736, 290829688375776, 293028510304736, 295227600669152, 295227600669152, 290829688375776, 290829688375776, 290829688375776, 290829688375776, 544816639511008, 435965357459936, 544816639511008, 558350207456, 508532789348832, 290829688375776, 508532789348832, 435965089024480, 435965089024480, 290829688375776, 558350207456, 290829688375776, 558350207456, 366805460973413231700370257067583680321212684578, 291928965122528, 21288498328859446103648103391583840674, 291928965122528, 558350207456, 73126184749536, 9354711665120, 73126184749536, 9354711665120, 558350207456, 9354711665120, 558350207456] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_13 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨3, 0, true⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [36842267281888, 41240448272864, 36842267281888, 35742722099680, 64943967634244260481872253913163714435748584893266432252055066843010244870001022505727860244761028, 5709012570183820793154252080141832172596144546, 65134047534323847008138687566760159558456021695614512352759235671506990945542109643486927991031556, 41240414718432, 41240414718432, 6433789511384616819122134154118270381087316258, 65007327600308031269546622412707753473885582581305543280904355286039173979827204923527290326055684, 81100758978735554310785301930905910925815950583301452334521915955954021767751605522420480173374212, 5709012570183820793154251489846021813890492834, 181977802410464, 145694019291616, 181977802410464, 145694019291616, 120768640351137063628834201485499588626409796981852718752999421945276018722601813919840735683643406185079880449044678234681107240723569038133267296510131555644080725649191, 696919575952410832619537567107317522016674, 120768640351137063628834196802876763152421449909456874063249963322378804725145071322881727895862228451337259839027470044865759808442603179074209604823124589749548408070951, 145694019291616, 145694019291616, 549134249410452952015593224947565777495549602210, 702364093823146002776866175688401470138786, 702364093823146002777456471498760175790498, 36842267281888, 41240448272864, 36842267281888, 35742722099680, 64943970534633389630136525513284755447015395200041447174625367116132554842848194684480757533002180, 11418025119079143257449057613914688351292664226, 259775869083005907414649312141581637012894281602139510936753702457429129833793191883221020542715652, 41240414718432, 41240414718432, 6444961662055365070754563669229399826530107170, 259775869083005907414649312141581637012894281602139510936754386314079180021800835120770556804679428, 275742580527771666122904065628902460312772796810562029564933635169624303467677603068141571390274308, 259775869083005907414649312141581637012894281602139510936754350985691354550833650599273532791146244, 36842267281888, 145694019291616, 36842267281888, 558349945312, 290829688375776, 145694019291616, 145694019291616, 290829688375776, 558349945312, 290829688375776, 558349945312, 730753606279889773758594554426572568360536549794, 282033326655968, 290829688375776, 30916536060389655292927826615324494433327442620380193091978724325985029230666246918302373780298788068682583587242726426257815156410175484325000084014101533124322307408159782, 732180854653160467481549110062100387940816431522, 732180855333725201323445379875750413165986359714, 1038105554918528406094107026406602315630740695312993327574625000430163973623839863353880748926865061, 290829688375776, 282033326655968, 290829688375776, 290829688375776, 2076211109836584743643006706435463994739806885780306457911697012507655228796872734167915632609866309, 2076211109836584743643006713039141269580811278067745345667295429720971524902812776095998297331636421, 1038105570387270466635219333698568321514486685152499014523561830256451243514128303333165704140566181, 146793430321632, 145694019291616, 146793430321632, 145694019291616, 1978884747222783456185379191100483388765130552759692159062909161175373963017227321863277949617950010003270951313115787835014128981597815416788716933638356587112307707512598311, 145694019291616, 145694019291616, 91522609487460838110293699497222263362276080034, 3353735742730344212913268685616485065195068843965832629398644274755656494294197012493249621057961729704535179703998321027555967560064566181100428662914284199404527791292980248935491295137046162985719353948945224369317601941744840427649447130313546137137183967939321705534034463266350205259371550351580081292509013605984584992862542675662778799951984375638584515513404822429659435, 16611462958278733400335040002511673749445595651139278538299857532005190985549425161256165064934914820, 310418318941457865478334339847839290301694933856894656153132022508047248406206873071151410277578774115329766118686293795570278311311991467830678953862763383931821158180195650708331544595565124021424761363521035421766769632673495391760338813936538779072205817730015608170405651985978329886756979169417030047932815584285332564427225495874204565541374989485041469577341085394539935452660335743714167621107143658124981779985814175278696691978005555085391139227394460930529995582418696616299988747725063958084732300, 365376803150589136043727000265109772923959290274, 365399103980858258397105569562514757033844059042, 282033326655968, 33218934238093093457500556369834511625850345388776313800669798318666347036715163508721386715462257092, 290829688375776, 33219124317993173044026822803488108070973052825578661880770502487494843839194348476279065591399532292, 290829688375776, 282033326655968, 290829688375776, 290829688375776, 3313262370006731767915153891581057625705838553468748832663795177904922119237756143940918289498712769128401108514909537662208346237898349847144219341044931151098065456330685734, 21288498328859446103646977487382030754, 3825377882306795734903365750319719547855020600972632112887885122636318334581218825419862282618265307825698119170012057414414673385134974419144262819313779339460310596485889318, 558349945312, 290829688375776, 494660804796162420546105834083356678800598300046567353686665572014834182265202022384359104412551400401515641022915341261380737140014108196802250608274989460602266766249255719, 2788294992663904931300300318207089394620706, 2788975567782340544677548157156401823656354, 290829688375776, 558349945312, 290829688375776, 558349945312, 240240944966451571083927400315203804225281996641348795322996955028244574510060410051726060757721437865447872244269416829412408787230263595625326119507536225815306034069963137328139211529994703831100402589223257497697282269543700790854075364727766049557070340374438760, 730753606279889773758594554426572568360536549794, 730775907110158896111973123723977552470421318562, 282033326655968, 290829688375776, 732180854653160467481549110062100387940816431522, 732180855333725201323445379875750413165986359714, 290829688375776, 282033326655968, 290829688375776, 290829688375776, 3313262369992335133506698498009525050163727392971499875495003029310042060411332870571258887043261386990638166253663210108076304657035003107070831982466730880955894184050408742, 21288498328859446103646977487382030754, 22300851557620682238015401051926412894710690, 558349945312, 9354711665120, 9354711665120, 558349945312, 9354711665120, 558349945312] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_14 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨3, 1, false⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [5720173874343738846465536866116636610082674978, 6633485738870509858579736895467394593495330, 5720195694950517651644506455013338172219234594, 5586096613487861268039469853792412038633762, 22880662596302590902662056546112401746626129314, 364496732555744, 435965357459936, 364496732555744, 290829688375776, 438164045171168, 290829688375776, 438164045171168, 295227600669152, 295227600669152, 290829688375776, 290829688375776, 290829688375776, 290829688375776, 45761314282280942006124350117749123184424167842, 732186445534973889771885879849162758120304318754, 732183641650816141697782565939940696913980991906, 5575207588130984644829885643438796485732770, 22886139951421733788334544286793164007914122658, 5575207588130984644830475939249155191384482, 45766704695255336592024258687942889219342510498, 5594263390293963559048243182551614226471202, 91522618334791993461208756753581730936390719778, 91522967464500454344072270175928955930575673634, 291928965122528, 295227869104608, 291928965122528, 290829688375776, 293028510304736, 290829688375776, 293028510304736, 295227600669152, 295227600669152, 290829688375776, 290829688375776, 290829688375776, 290829688375776, 544816639511008, 435965357459936, 544816639511008, 558350207456, 508532789348832, 290829688375776, 508532789348832, 435965089024480, 435965089024480, 290829688375776, 558350207456, 290829688375776, 558350207456, 732180864861631475109993157266850766318365354402, 291928965122528, 21288498328859446103649229295785650594, 291928965122528, 558350207456, 73126184749536, 9354711665120, 73126184749536, 9354711665120, 558350207456, 9354711665120, 558350207456] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_15 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨3, 1, true⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [36842267216352, 5709012570183820793154251637419833666078550434, 36842267216352, 35742722034144, 37941812464096, 5709012570183820793154252080141691435107789218, 37941812464096, 45638595152352, 5798215891260310206668529380442092315293559202, 45638595152352, 35742722034144, 60384320178204667747138974643694219704351174359414842341409638576522842203925300278917211212187574829742163704616881837388902242646645541116430979009618163320047136468135, 129792894349764067545957641500750489255205293509119231567479043010302618696311520636642313505059397, 60383859489432106523829374844551032659808826102429928225146409059152206751757039510602118758475226445849681503943186677488668813958711356355299744215536148507461858028711, 129792894349764067545957641500750489255205293510539811180132966285930357366836740149978305031025221, 64896450075271155720247045526196142585795354554486072212525878254899593921380483430252624656066373, 259522429214974283140659469108442709753257241703325991244496969017917027810356391294799772833250052, 36842267216352, 21288498328859446103646977487382030754, 36842267216352, 558349945312, 73126184552928, 290829688375776, 73126184552928, 290829688375776, 558349945312, 290829688375776, 558349945312, 72026639337952, 72026639337952, 70927094122976, 73126184552928, 519108218156201565382063705940754847758237172653803331594873087921605120927060859347543597028449796, 73126184552928, 519108217914502475849335981171045415966248293897839587232787329724170405475985554060009708913401348, 81922479163872, 81922479163872, 70927094122976, 364496732654048, 732180859417113604374822998314928706747976690082, 364496732654048, 290829688375776, 290829688375776, 132891703662846094597108521941742158186916619166238620830821404620609588470461687819096928467274660612, 1038105554918528406094107026406603115345961511761792701465529020555750955635612331402147858890002085, 290829688375776, 290829688375776, 290829688375776, 290829688375776, 72026639337952, 45672100412451078043217890373829826916954188194, 72026639337952, 70927094122976, 73126184552928, 45672100412451078043217890816551684685983426978, 73126184552928, 81922479163872, 81922479163872, 70927094122976, 3864539365997294386584760333147595185033724710366261600498713716781195302916416825597724744934604598380413408766561741740321574903759625125783494479405710699622705646202023, 1038105570387270466635219333750979259112592124383290182370068772776124279403138980865099171682199589, 2076211094367606764082597750485445733949963563884914698659128250363086393470395511525854428805479269, 2076211109836584743643006713039141669438424665463476475900688088410388202665206265963613017480272069, 2076211109836584743643006706330644120393594806631792548109663984962685222328537698537828796606724293, 291928965122528, 366090426996942115984256143249835646396352489890, 291928965122528, 290829688375776, 293028510370272, 290829688375776, 293028510370272, 33222925916074072288958174192176873828853160741184523599094831320618880390977675069627503712373062404, 290829688375776, 290829688375776, 290829688375776, 290829688375776, 21288498328859446103646977487382030754, 558349945312, 290829688375776, 494660804796162420546105834083356678800598300046567353690448164609688052269593626156188416798333425501717341215725993728883000597098577511889920099513032360601533894910501671, 123665201254827136216934691523756981349712542324678883886834972376134766899733481360658157941314867368088718371302477830236379576817624189854030926278704356625481430172589351, 290829688375776, 558349945312, 290829688375776, 558349945312, 132891703662846079851719616246932306409355424073576115157342709086332917882435354649661994372716264196, 1657895127520, 21288498328859446103646977487382030754, 1657895127520, 558349945312, 73126184552928, 9354711402976, 73126184552928, 9354711402976, 558349945312, 9354711402976, 558349945312] = some [] := by
  decide +kernel

private theorem solve_1_1_0 (N : Machine4) (h11 : N 2 1 = none)
    (hAlive : ∀ q a, ¬ (q = 2 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    (hm : Matches N (baseTable 1 1 0)) : CertProp N := by
  refine branch_one_sound (tb := baseTable 1 1 0) (q1 := 0) (a1 := 1) (rem1 := 103) (cur1 := ⟨0, [1, 1], 1, [1]⟩) (step1 := 4) rfl ?_ N h11 hAlive h107 hm
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
private theorem tv_1_1_1_0 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨0, 0, false⟩) 103 ⟨1, [1, 1], 1, [1]⟩ 4 [1461518373842650967241332670718212188722917579042, 1461864035350703280628626273852708133644209793442, 1461529524172725321281503238078615628654211804066, 1461518373842650967241332670718212188722917579042, 1461551824917923851904644773796888312200224091554, 1462934471120232750539419988329792580990660553122, 1461596426748592895478149201262619292268013590818, 1461685630069669384891653807599084704252575127842, 1461507223427526790658361702360347448707826887074, 1461864035350703280628626273852705881844396108194, 5720173831818827574757059107405447321034467746, 11440336753313415350622632500314627680551087010, 22880662596302590902353779286132988399584325026, 45763927650858894813215471574754785817514781090, 45761314282280942005816072857769709837650799010, 5586096623872454676869644064429051894344098, 91522617654237644212740660001043152713783753122, 183045224398151048626589834287590038466049649058, 732180864861631475109684880006871352979645049250, 1462934476564740236680718296309598360974111316258] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_1 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨0, 0, true⟩) 103 ⟨1, [1, 1], 1, [1]⟩ 4 [265751093741551359822772414497948054134094627836748524500318090669589733398622748181432153926186269444, 1978643211900009344325130447387260592234061569810792723141069077064811340884380038433381240822193995156379270470644010262427762808077107679454376881553276854600574942890058790, 265751220461485375638482869085417438704691270526505722307781601627558100615765338021528230185634580228, 265750967021617344007061959910478669563497985146991326692854579711621366186180461998037737302861773572, 265750967021617344007061959910478669563497985146991326692854579711621366186180533718979764610900654852, 64888527662168211216052256250457767961109147723905280784218460804152221140624405571907758180236036, 259554109198478237068273115975788852402417911957773998848640347532275591929926673757705684890665092, 519108217913558338767714276842578557479532061527201092472582119918010025470385300338529294488935940, 265767185193172369916595870575370420876624967010964636011661269972504071988648504825296659665437031172, 2076432870204038545585481154645227233010002175398150836987957213742996991784803445824912708169320196, 16611462958248521013723145464000734277870676282921165542102492143428768190623817622362568894398561028, 132891703662604380758824459938844790636756069143105283183018771580914937781335931034663818384234478340, 64888527662168211216052256250457767961109148451242042463027097174954127745050802132419928682363652, 132891703662604369694718034684497191415758177938010096957864879678147372558477492590121018721947581188, 259554109198478237068273115975788852402417912685110760527448983903077498534353070318217855392792708, 519108217913558338767714276842578557479532062254537854151390756288811932074811696899041464991063556, 1980482396694398662784498199949844616870700015915637164582856184511486109811023583959290444548, 2076432870204038545585481154645227233010002176125487598666765850113798898389229842385424878671447812, 3960481395195802939315687673673087899294920689190481068305553680295845706090595693923656760068, 16611462958248521013723145464000734277870676283648502303781300779799570097228244018923081064900688644, 132891703662604380758824459938844790636756069143832619944697580217285739687940357431224330554736605956, 30199070432992845049096479093568639046241665885013204288843889166692021148072897647259380050483808426263918306031208227054713521648963610275820112151732183585399543315239, 966141752000502952930022391737293721632881745687000750368084842992617830408431187039491622776208838057653836379140456685875165086818954403357362084748340364530028601041958, 130679935730358306909991853045698064876292731455851271213850193928574499636578897418882190945957, 409551510548538018375696744716266417968460409495656921790802544423831626869185720584867962178459535259252780001993166523265282879996565019248803381303356228619859286013422497273040810321195340625235389028350269944400064858502189954715414826750331160958537308642503074605412065984271298888955282313838783921015444773409562093816148723168622605612908962027784370102202529309162] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_2 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨0, 1, false⟩) 103 ⟨1, [1, 1], 1, [1]⟩ 4 [1461518373842650967241332670722823874741344966946, 1462934471120232750539421197260225992694145526178, 1461518373885186263106449978655745700670383102242, 1461507223427526790658362911290774245755935828386, 1461551824917923851904645982727319612847826185634, 1461596426408320913150929054163864979947903822242, 1461596426408320913150929054163864979939850758562, 1461507223427516406064644594930765707056547666210, 1461685630069669384891653807603696390271002515746, 1461685630750234118733530734530445605135612680482, 5798232905368271659866132495895656886243989794, 523258038055057793985227771388661002844460729470112351513606835676901181175385021463453573037489862724, 11507238988909007220048448585559510569725241762, 266269948510897548343440440901854482605200020367728054045614850207448636327489259702686194276675827780, 23192873029082019626336488272377425484097563042, 46031536593241262290915109124453926178747623842, 23014564388240329435886436691325143893863864610, 92771464829862845249964968208725690022460692770, 184115660167680518537384757695106208689747437986, 365378207836189401083988278428769361269410011426, 1462934471120232750539421197260225992700587977122, 5709045237280660609530845474662257122100680994, 22858361851104060279213452498287172287470807970, 45786228396057425436358216223454407166170016674, 22847298718386229729522938701807272117740280098, 732180864861631475109686088937300401844613327266] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_3 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨0, 1, true⟩) 103 ⟨1, [1, 1], 1, [1]⟩ 4 [1461518373842650967241332670718212188722917579042, 1205210683146446135605319137275206462574889249586267749838919655696488966013710764519300669763564866607711140942613569813380072905659850887537960146450193146525189515329359977563871360461412548608556650968249788199146044252885455980797179603745969435964943667876707236916884433754872170968215889731166391951475922443579879626924128192227725855790307203930827255980384211166915108825937512199179986745793601585160325756338411232942456377507666307681814556519306049285784183702760781415326308215907053449991164795439933250781771775544067319514202691279091344723056588968313635767322073961993140454147557094371832625947117553799686103346245339676258405844793749494682249116758163854778705913922333316377599890995252702959290643388413151701614300844194569447882285601784034782164992273599688483038999155307210738456182200275120, 65007330019187234384353058329228940793649298448507057248289009719347533445018993518677193986419333, 241533595203516446252364020477300105787742045359153083497800025755631957283405321354888395760192516634579586852500267531486990128269930295588190419235938106571030977733670, 129887934301692149382239952503934676470332527110235525177871250625467468226842580237070817521576581, 117304950450076827194378541869699265725618766016764436826870746196234556959741138251705972078155245279849345494373244087965245642738540047433710082573773472808996213047045981737817506188237815835198875001980114124365175619503983562206597810495536574267652120593640, 519171600602169245755821076254818879412340956503957654039167356524327936905182095012873030446361221, 3864537523243082728529606356060266127506924435624426097388793175998722568027131792553221075779349465754317877809435009256610268494751839985752551296157436526814856005706790, 1038216434862208565738916229652464755454144111679354110515102361239627117250282929018774203249994373, 129887937202081264124115649554123948053077611331030433584699927177155893880644094303384122608593541, 1461529524172725321281504447009046929301813898146, 1461507223427516406064643385995722720373338315042, 1461507223427516406064643385995722790742350928162, 7136271151925522144244577217714255423048034722, 707808611693880863449775256482984175380898, 11507238988909007220048448585559510558987823522, 10910313855205173169349871538639914178850, 2798503474056126782968748844543768066566562, 5586096623872454675660713628624813254814114, 732180864861631475109838414171644283425297312162, 1461507223427516406064643385995722790742619363618, 10910313855205173169349872664531231086882, 22880662596302590902357406077423512646696611234, 2798503474056126937711844052152556746484130, 22925351539257566236113315888779197837288184098, 1461501648241227158002575109500344608274422737314, 732180864861631475109838414171643157521095502242, 30191699413510130526836963941957047896394381200645470892701156344614156526999969797934624611924154492673521359551635515764557503577061183822025646406948201034391466042406, 7136276596433008285542885197520035406498797858, 707808611693880863449775258734783989066146, 12845283700820844608540591681920523311671978402, 10910313855205173169349872664535526054178, 22880662596302590902357406077424638550898421154, 2798503474056126782968748846795567880251810, 45761314282280942005824535370786562579104836002, 5586096623872454675660713630876613068499362, 732180864861631475109838414171644283425297312162, 257399869746174017364579322430269442490883625966888809884441531134919325944864923065061436569797, 989329153874855193937694278676174883603165869117429930466073268318782045895750572099551735480880124720817414137879659518961396468906588874210040105175785065103043810632295462] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_4 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨1, 0, false⟩) 103 ⟨1, [1, 1], 1, [1]⟩ 4 [1461551824917923851904648400588186647390825000354] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_5 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨1, 0, true⟩) 103 ⟨1, [1, 1], 1, [1]⟩ 4 [265750967021617344007061959910478669563497985146991326692854579994248478416170088399210785726637767428] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_6 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨1, 1, false⟩) 103 ⟨1, [1, 1], 1, [1]⟩ 4 [1461596426408320913150936307746457146704245336482] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_7 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨1, 1, true⟩) 103 ⟨1, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_8 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨2, 0, false⟩) 103 ⟨1, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_9 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨2, 0, true⟩) 103 ⟨1, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_10 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨2, 1, false⟩) 103 ⟨1, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_11 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨2, 1, true⟩) 103 ⟨1, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_12 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨3, 0, false⟩) 103 ⟨1, [1, 1], 1, [1]⟩ 4 [5720173874343738846233422223310289978791074082, 1461859157062691102054890225531509621478954936738, 11440336753313415350698795117486568496528665506, 22880662596302590902429941903304929215427685794, 1462931683527082934211603458982184803615133182370, 22925351539257566236181015992935411815610882338, 91522618334791993460976642110775384305099118882, 1461501648241227158002652481047951227433562188194, 183045224398151048626665996904761979280013961634, 366805460973413231700138142424777333694216050978] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_13 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨3, 0, true⟩) 103 ⟨1, [1, 1], 1, [1]⟩ 4 [65007327600308038444603432003005802895461668644651753408778955092466313304276069359388469876718340, 1980482370878150337191020468434182870722326122111346237657392995636758424224653440117797780228, 483401881029861338091259300267298180298843468056202039064478864299729133750138259438271236, 8305731479381068562691319441497099793272937849537604574575926320312883260240422981601211177802836740, 65007330019187234384353111944798399849545984475108307274499680890225170365151433554986537866567045, 16611462958278735244352777544902940286278577517321692179414357338789047500871156422053414236197190404, 132891703662846068787613190992584707188357532866298918647152391597455346606484419813091317430812375812, 129887934303580409139094793267024484626516857632103622543654298375691140200767115170803308218453669, 259775869083005914561568644047211850946542618308374559456284379846755624682232253029431756864308996, 37982867923217340834784540907255294086159779495354421099488438193140690255556189105157174121676486357606331013062091745578768849632592439270297384391790824456795628135462, 60390769833263542897613603242708994033385560107803080287190382799881429024659657636516913059677204884205657738453567444192101294831304882592024418605626419808619322827814, 483398192994386253308726226601334445024669117435644193046590794239389359033758206060100356, 483398192994386253308726226601334445024669117435644193046590869444247866260320733453581060, 259775868603384269922685988636267246816920015630958176195556650484565806320435855267574072446195909, 483398192994386253308726226601334445024669117435644193046591997517125474658892235018566404, 483398192994386253308726226601334445024669117435644193046595607350333821533759959242865412, 16611462958278733400335040002511673749445595649684605014942240582265995863644376032977371968339933956] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_14 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨3, 1, false⟩) 103 ⟨1, [1, 1], 1, [1]⟩ 4 [5720173874343738846233422518458195158143899938, 45762362011678306981704132066312428135088429346, 732178774166769112863918895198056222634963675554, 45761836955996532567449486765937438863431608738, 707808611693881018192870462965877243423138, 183045224398151048626743368452360787478753356194, 707808611693881018192870462965877243423138, 91523316594208915226703669250613306225295661346, 732181917695264343899649891166033446629350086946, 732178774166769112863918895198054533785103411618, 6633485738870509626465389233648234344257826, 5720195694950517651412392107354896720280459554, 5724363430845269440595583586620409063809259810, 3960481365691519138637427409083760189412727294558927200322310601798206395762474872691850705668, 5724385251452048245774553175517110626012928290, 2798503474056126937711844051026661134608802, 732182266824972804782513404588380460516497201442, 2798503474056126937711844051026661134608802, 732180864861631475109838414171642172354918918562, 732180864861631475109838414171643157521095502242, 4200466815385799612702260790511091632347426, 22880662596302590902507313450908170661961706914, 9775653115018455398086190362050890319304994, 45761314282280942005969607022544892099759745442, 5586096613487861035925122195350960099858722, 91522618334791993460976642405923289484451944738, 91522967464500454343840155828270514478636898594, 732180864861631475109838414171646535233700932002] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_15 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨3, 1, true⟩) 103 ⟨1, [1, 1], 1, [1]⟩ 4 [64888527662286228351254969291516125271948675770857335127209809255444122686230403054585023799982852, 64912287650268245202573343565200804191337766419646923060381443657497454082092327959346551885119620, 64880607666292222734148844533621232298818978887453945945267956748789105023433149861590498769337092, 64888527662286228351254969291516125271948677224820568678500443282778131297221360411269123143858948, 65007327602196312607846840659939519868894129021908172856337596855269425230618454562779988248197892, 64888527662286228351254969291516125271948675770857335127209809255453746557967499702689986801531652, 64888527662286228351254969291516125271948676133815426160287246474774917360831339282020149711043332, 64888527662286228351254969291516125271948676497483806999691645410779998815316641663743638453320452, 65007330019187234384353085110808600794426407665196227643890460352911618959541891546475672262945413, 483067190602981676921173451517641570510372655042047957783080181659812586164043361915252571466938778125806320614384077812761021941430257681745390658572927926428070941582374, 65007330019187234384353085110808601965884241930000051808683493782556379557346738428418919510321797, 129887934303580409139094793267025284341737674080903007272720565737761712932502082157431648216321701, 259530349210968288757765593866337602726386935677382333711204276041366223972052231681042027363138308, 241533595202637859414330741974559219077659612674111615614308247402376487749121121601525736372043969546060480683311099866184977678183801010210858274448324972446335867184166, 259554109198950305609083968140022281645776026327592501257029833561331276960443991260024558778302596, 259522429214974283140659469108442709753257238793978944529262423534711206309254978488047502332492548, 259775869086782462888055461361079284893407539062887398351401703747671771518767080663863953896982276, 259538269206962294374871718624232495699516632923033524119896604050680156085038286196917010739725252, 259775869086782462888055461361079284893407539062887398351401703747671771518767080666126645747730180, 259554109198950305609083968140022281645776027779424865389339582438654455658847736169231743448498308, 259522429214974283140659469108442709753257238793978944529262423534711206309254978490184952936889092, 64888527662286228351254969291516125271948675770857335127209809255444122686230403054585023799982852, 259554109198950334421861117239885821283791368009421988201906657882004108026753535117064433342857348, 483398192994386253308726226601334445024669117435644193046590794239389359033758206060100356, 483398192994386253308726226601334445024669117435644193046590869444247866260320733453581060, 259775868603384269922685988636267646674533403754026068107758026295382276836271746001170335426058437, 483398192994386253308726226601334445024669117435644193046591997517125474658892235018566404, 483398192994386253308726226601334445024669117435644193046595607350333821533759959242865412, 2076179430336006914164571979706458091816716795179147734184590036951563717020203239669144807906966276, 132891703662846079851719616246932306409355424072121441633985092136593722760530305521383201276121283332] = some [] := by
  decide +kernel

private theorem solve_1_1_1 (N : Machine4) (h11 : N 2 1 = none)
    (hAlive : ∀ q a, ¬ (q = 2 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    (hm : Matches N (baseTable 1 1 1)) : CertProp N := by
  refine branch_one_sound (tb := baseTable 1 1 1) (q1 := 1) (a1 := 1) (rem1 := 103) (cur1 := ⟨1, [1, 1], 1, [1]⟩) (step1 := 4) rfl ?_ N h11 hAlive h107 hm
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
private theorem tv_1_1_3_0 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨0, 0, false⟩) 103 ⟨3, [1, 1], 1, [1]⟩ 4 [36842770565600, 6065835382396052233759140000611473215131265442, 36842770565600, 36842267249120, 5709012570183820793154251637419833666078550434, 36842267249120, 35742722034144, 37941812464096, 5709012570183820793154252080141691435107789218, 37941812464096, 5887429420807807248336710950919819747367369122, 6065835382396052233488339584001817002122455458, 45638595414496, 5798215891260310206668529380442092315293559202, 45638595414496, 35742722034144, 5753624949616623509777639944791651771145563554, 7136265749942947274654746996628390444400683426, 5798226780285667083282067410522631838935062818, 5887430101362156496786673746988043823496599842, 5709012570183820793463737680263350462165592482, 6065835382396052233759140000609221415317580194, 5720162985318381970151813472321500571956717986, 45638863817184, 5709012570183820793463737680258987600026577314, 45638863817184, 35743258905056] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_1 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨0, 0, true⟩) 103 ⟨3, [1, 1], 1, [1]⟩ 4 [1038097635405582114847507608962799349703213641093409117541833657680545929397375920688417030177782532, 1038216435343721942102437670044723480407498427763073776046698289375115784742815059635107510749461252, 1038121395393210080293217844113308956690084145422883706441241962457330798367646501475703284320157828, 1038097635405582114847507608962799349703213641093409117541833657680545929397375920688417030177782532, 1038153075376714034233141637467697277365213208205919291510770468140484615823097259936124075772190212, 1038089715409706126363845604890671074322927988648764806974843007760100521356829987849574528931035908, 1038343155277737757841029735198775886492068866877382745118553815765389553177644195605298444661901060, 1040117234353959177731119004400824203869211024763929726391018032439223093079832372648409143602019076, 1054309866963730540931767422294046888635871943364584695809569201106436932500234712813454911444581124, 1054309866963730540931767422294046888635871944637424009780699675523736686227625761512113857988098820, 1980482370878150337191020468434182870725235469136385147869904435764686807476443847553881176836, 2076187350331886360190284837538669822348820871117427716139406971810883340793802018415505596315040516, 2076432870204042003175014001998187660547698675227304105713519478287023982961217395034104347531626244, 2076211110319514325632477887978595949899700406777263409837772200803449377631374075088551489144602756, 2076211110319514325632477887978595949899700406777263409837772201118881411787364853521779141144723588, 2076242790303018279567125904267109051420843016555840652105736092810274946887777047377611738627415556, 2076179430336010371697829871690082848378557796998686167569808632429890852421509775291062191786261252, 2076432870204042003175014001998187660547698675227304105713519440435179884242323983046786107517126404, 2078206949280263423065103271200235977924840833113851086985983657109013424144512160089896806457244420, 30916536056902530295817759617833128528644764438583690828358781394342368359579805839132126720634387126285698940393509951605792871574890397911581030351442497741506929186331686, 2078206949280263423065103271200235977924840833113851105952768397278867147240902078126105483657050884, 2092399581890034786293889166778126498179429502344456531984009906467277674353893741867524411345828612, 2076179430336010371697829871690082848378557796998686210922457621375825215301503212944592607535921924, 1038097635405582114847507608962799349703213641093409117541833657680545929397375920688417030177782532, 483401881029861338091259300267298180298843446379877100463207591224716380937770310091111172, 31711404389725537482420160624335633889673707319127047161606431814130506587098834433389446545540, 483401881029861338091259300267298180298843446379877060087907219257896741484630854075644676, 483401881029861338091259300267298180298843446379877383090310194992453857109746502199376644, 483401881029861338091259300267298180298843468056202039064478864299729133750138259438271236, 483401881029861338091259300267298181753516969737494494330711617875726005700564813387889412, 483401881029861338091259300267298180298843446379877100463207591224788101879797618129992452, 483401881029861338091259300267298180298843446379877060087907219257896741485699579377842948, 132891703662604369698319631828134674358212929854271334438825987661803928101818059360772281679687678724, 483401881029861338091259300267298180298843446379877383090310194992453857110815227501574916, 132891703662604369698319631828134674358212929854288381394177834740480597198371814519502061039556721412, 483401881029861338091259300267298180480677636799579239368262582196069862012025124160764676, 267632504629437829458234261448465281440896116231086226685390663431064434726756058489225253380956229, 145981366161511550708157980497370020379818710619514042219220958645517055107617788733033923298408645, 12845256478212993298068087894218405511289668067, 12845256478212993298067937073638858827635917283, 137871290384499345239064382876038608381651102804796960172863308325600784419177986681086882980310693, 62270380023724374682712602633091009547458738218843955625825243475804411434138497552193397249892586558424247185487543429914502598384544478329810382989899644777436566699175, 989329153874854754595671932717486990148125655550315036988968404302370717657812395892628110111561968585315965134480278598860849729572542605271046897036772480574497187192267814, 12845256478212344260960619925037387370870112739, 12845256478212344260960620220185292515863200227, 132891703662604369698319631828134674358212929857174999167090607159558565152613626581302547956448328452, 72990685981144898199987908473765029307090593778901051947958961800523114829609833092237183951202949] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_2 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨0, 1, false⟩) 103 ⟨3, [1, 1], 1, [1]⟩ 4 [36842770565600, 12845278341373565604066860463320820745812093346, 36842770565600, 36842267249120, 11418025119079143257449057171192689844775070114, 36842267249120, 35742722034144, 37941812464096, 11418025119079143257449057613914547613804308898, 37941812464096, 45638595414496, 11507228440155632670963334914214948493990078882, 45638595414496, 35742722034144, 11462637498511945974072445478564507949842083234, 47837383821792, 12845278341373565603912116925392480090157263266, 47837383821792, 47837383821792, 11774847931291374697749295065694314404728842658, 11418025119079143257449057613914547622394243490, 5887461534945800818172585725976386225025620258, 45638461164000, 45638461164000, 45638595414496, 261549948189439721119827407129535310874459640786141658489137558659385513389891230436722029435779844, 45638595414496, 11418025119079143257449057023618737263688591778, 11507238988909007220355516915109875041866656162, 5709045237280660609530845474662257122100680994, 11462626779617387964206195913576610670327147938, 259522428732048158687963417822678708888401661890192299079910583003673227683536139625894570550852356, 11507228440155632670963334803534484068375767458, 11440325949348265610902580155338314122632670114, 259775869083005914617843599416547521922398117022596882672973592394247387788520542327111622401148676, 5720195737485813516529700040272236641944377634, 11418025119079143257449057023618737272278526370, 5887451879433639436848335402962919456662133026, 5887452559998373278725262329712134321272297762, 45638863817184, 11507238988909007220355516915109875060657138082, 45638863817184, 35743258905056] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_3 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨0, 1, true⟩) 103 ⟨3, [1, 1], 1, [1]⟩ 4 [64888527662227205379023630576346916515516727786609533056464310015793043044320180216412651197266692, 137871290263649813197874802596060429124515197270809344225972630229429418220793017001882451358526085, 259554109198537216830131692817621450291804274184021850450012398259908253549970947697541158618513540, 36842267249120, 21288498328859446103646977487382030754, 36842267249120, 558349945312, 73126184552928, 290829688375776, 73126184552928, 290829688375776, 558349945312, 290829688375776, 558349945312, 39041290537440, 39041290537440, 558350010848, 73126184552928, 290829688179168, 73126184552928, 483457201561987609829255405256754212320805427258614301262948706874536986612447557119605508, 290829688179168, 558350010848, 290829688179168, 558350010848, 47837383821792, 21288498328859446103649229295785650594, 47837383821792, 558350207456, 290829688375776, 483399115003255024504359495017825378888671247276627475170318027400312381897962287011166980, 483401881029861338091259300267298180480677636799579239368262582196069862012025124160764676, 137871290263649813197874802596060440058121647590563013650374384808208614274890936697305580577172805, 290829688375776, 558350207456, 290829688375776, 558350207456, 39041290537440, 39041290537440, 558350010848, 73126184552928, 290829688179168, 73126184552928, 290829688179168, 558350010848, 290829688179168, 558350010848, 32444263105986909759731155620163844566632266935441839041582737968320560080491661259772203015729380, 62270380016804658641505534953388716671689947828823917601250539075432790110101111284426783773284042065561092887853609224932432535047234764340298144543024098890966962461863, 275742578472857306172465970229855696734528165491861928085697155461038014318985307094002018610592613, 7446115018805182963688482271374126582454607223642578140750118501038617850801052792669190908781157186358724426632528814944118942224224015833607074082219349621461564230925673620871395078305333760729254625520316367607981624655177069510554175631948840435712119722761, 12845278256283827201022281581012262969675907555, 12845278256283827201022281876160168149028733411, 45638360500704, 21288498328859446103648103391583840674, 45638360500704, 558350207456, 73126184749536, 290829688375776, 73126184749536, 290829688375776, 558350207456, 290829688375776, 558350207456, 21799349596675205209108290417828702492962, 21288498328859446103646977487382030754, 531501918202276021648443405702273815211683598819232229382605995966403737467795165292116961092165646404, 558349945312, 290829688375776, 62270380024053884970392478558385047896554226849987189735273595974512973679263500142153155366403746882083250310243933929407387567454613219669484916429071097574671426183975, 290829688375776, 558349945312, 290829688375776, 558349945312, 483457201561987609829255405256754212320805427258614947267759452653381053556037887347358468, 35742755588576, 21288498328859446103646977487382030754, 35742755588576, 558349945312, 73126184552928, 290829688375776, 73126184552928, 290829688375776, 558349945312, 290829688375776, 558349945312] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_4 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨1, 0, false⟩) 103 ⟨3, [1, 1], 1, [1]⟩ 4 [22847211521029706239041676207456917715948706082, 23192873029082019626643555568914062488378583458, 22858361851104060279213452498291640702591871906, 72026639337952, 1978675290580619558562583026428378389033899818055678423379745288953545601340742494512108539873075448685637459096356063860069585149795774575444929511038326946953902214987004711, 72026639337952, 70927094122976, 70927094188512, 70927094188512, 73126184749536, 73126184749536, 70927094122976, 73126185011680, 24263303524234802262736344301505953882925214114, 73126185011680, 23014467748048123889380947044798679075840366882, 22836050216869788186348153100990298298023717282, 23192873029082019626372756185320385553244400034, 22880651877408032893100456287669642810629336482, 81922479360480, 22836050216869788186077353717396621362889533858, 81922479360480, 70927094647264] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_5 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨1, 0, true⟩) 103 ⟨3, [1, 1], 1, [1]⟩ 4 [45775078065993455989903547366812935943881796002, 290829822724576, 732180859417113604374668255810015782405210679714, 290829553961440, 290829822593504, 290829553961440, 290829822462432, 969908343404301490781649703255445327719122803503650025410966494159654083892107771418240787558712495159589111105196597428617781742436524190195160609071681151883509578390695, 290829822462432, 14677438258231766669596087822809787907457155242994050621460896965129125772049133850571495617521567951710151873356434764062341379590093338825034381497521271607739215409999520982125809086732096575649436723543973296194931173458539640998431299688180177961088076738761, 290829822593504, 290829822593504, 290829822593504, 290829822593504, 45786228481128017166592832089302386701207907234, 364496732326368, 364496732326368, 290829419678176, 290829419743712, 290829688375776, 290829419743712, 2084289505750470359637426750930700168426008051527937260114248302313652006829541011412274938678254085, 1054309866722027866220114235481916896609791061385695615789154676089716913955899978948003312797946437, 290829688375776, 290829688375776, 290829688375776, 290829688375776, 290829688637920, 290829554420192, 290829554420192, 290829688637920, 290829688637920, 290829688637920, 290829688637920] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_6 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨1, 1, false⟩) 103 ⟨3, [1, 1], 1, [1]⟩ 4 [22847298633315637999288322831356420248610838818, 22925353580951767761744096890386663000463415586, 47099353889957275580384797725560572729720088994, 45761303733527567456732168116851980012650277282, 45672100412451078043217890373829826916954188194, 46028923224663309483551978320407377020235852194, 45672100412451078043217890373832078725357808034, 23014556221463523333381447669766130677725567266, 24263403567240292424927495320808321479278106914, 47099353889957275580384797725558883879859825058, 45672100412451078043217890373830952821155998114, 47099353889957275580384797725558883888449759650, 22836150259875278348229820291063785975509457186, 45672100412451078043217890373829826916954188194, 22847298675850933864405630768889932196009253154, 72026639337952, 3864537523242205750628524670669177189679841787640919927029199868732672425320220839411542025218690808760223376990036659652830006815137597651785587494910380194700666057155622, 72026639337952, 70927094122976, 70927094188512, 70927094188512, 73126184749536, 73126184749536, 70927094122976, 73126185011680, 45672100412451078043217890816556188302790666658, 73126185011680, 23014554860334055649627593668698181608502499618, 23014555540898789491504520669234372766877128994, 81922479360480, 23014564898663879817312268107198621911939586338, 81922479360480, 70927094647264] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_7 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨1, 1, true⟩) 103 ⟨3, [1, 1], 1, [1]⟩ 4 [64888527662227205379023630576346916515516724877972776147556080244453147948364842715290862718515972, 129792894832749186163383659467694978534850545231644923466733465404844567952237572397794659285844100, 64888527662227205379023630576346916515516724877972776147556080244453147948364842715290862718515972, 519052777942485312726710486143423485408818640709618952212025844174361759686444869923251175260650244, 132891703662604425018851758099872670463202385883378977344345201625479060340795556645119830927057582852, 1038097635405637435407771358385463290180597419563135213313680959646132306627994997994631272118582020, 483457201561987609829255405256754209412168670349706717496424370668370178553849126749174532, 966141751831791118036160528182887985014095695493420700799021596539582885995701673023327021497407967589694468458240727743129191462527269363883677799708138354781325705634854, 1046199790824166229554551080111461463135884656228705021940117281828730907264699797009824857992211077, 966141752000501672484365082609298754868193838517175535563033082009034905631557706320018903289953212883625097745695049074786101970563563171552702550807171341529470489748518, 1046199806413757721292132951389357859510045176359037995258369822603721285942766619353527194383067173, 1046199790824166229554551080111461463135884656228704935234819949941668130623818661436936831931263621, 1046199790824166229554551080111461469383659772308458549383373731721337309678077322687077111035440613, 47099353549655761990352595790546500096415007203, 47099353549655761990352595790546497901686718947, 64888527662227205379023630576346916515516724880103645566536965079036747415154983943236193713617668, 1980482426198682463462758464539172326751441578183058723220659515116371966485687230260342651652, 259554109198537216830131692817621450291804271277515962960085053323151957920805751424364701134864516, 483457201561987609829255405256754209414299539768687602330998343913271394782861764035050244, 519060697938361301210372490215551760789104293155683842391670740215121865054077753061430327961420740, 2076211110319569646220879115085927725865011934604100667217964109042786404873125860257259021449805956, 2076211110319569646220879115085927725865011934604100667217964109042786404873125860256198645564031108, 483457201561987609829255405256754209414299539768687602330998343913271394784997127285340932, 132891703662604425018851758099872670463202385883381108213764182510313648715770861995233432196944722692, 64888527662227205379023630576346916515516724877972776147556080244453147948364842715290862718515972, 259554109198537216830131692817621450291804271277515962960085053638583992076796529857592353134985348, 483457201561987609829255405256754209411458380543379755779742866572220947001190018020768516, 483457201561987609829255405256754209411458380543379755779742885373435573807832737223244548, 483457201561987609829255405256754209411458380543379755779742866572220947002258743322966788, 483457201561987609829255405256754209411458380543379755779742941777079454227752545414249220, 2092399581648332226805207098680782836246229335150862496986917935212025685048761256409498032149566021, 47099353549655761990352595795158183915819139555, 483457201561987609829255405256754209411458380543379755779747679683165409501191771203533572, 47099353549655761990352595795158183920114106851, 519108217913617232098275775805987495326854333143573545376790351497434725002046410908426288069058052, 483457201561987609829255405256754209411458380543380078782155468528666987627377897812228868, 2076432870204097323707140273736183765537154704339919039877022136127025148377929800161097187205793540, 483457201561987609829255405256754210866131903900997190022556891411939136217127483698543364] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_8 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨2, 0, false⟩) 103 ⟨3, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_9 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨2, 0, true⟩) 103 ⟨3, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_10 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨2, 1, false⟩) 103 ⟨3, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_11 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨2, 1, true⟩) 103 ⟨3, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_12 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨3, 0, false⟩) 103 ⟨3, [1, 1], 1, [1]⟩ 4 [290829957073376] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_13 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨3, 0, true⟩) 103 ⟨3, [1, 1], 1, [1]⟩ 4 [558887340512] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_14 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨3, 1, false⟩) 103 ⟨3, [1, 1], 1, [1]⟩ 4 [290829957073376] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_15 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨3, 1, true⟩) 103 ⟨3, [1, 1], 1, [1]⟩ 4 [558887340512] = some [] := by
  decide +kernel

private theorem solve_1_1_3 (N : Machine4) (h11 : N 2 1 = none)
    (hAlive : ∀ q a, ¬ (q = 2 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    (hm : Matches N (baseTable 1 1 3)) : CertProp N := by
  refine branch_one_sound (tb := baseTable 1 1 3) (q1 := 3) (a1 := 1) (rem1 := 103) (cur1 := ⟨3, [1, 1], 1, [1]⟩) (step1 := 4) rfl ?_ N h11 hAlive h107 hm
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

end OMA.BB4HoleS2A1

open Turing Turing.BusyBeaver OMA.BB4HoleS2A1 in
theorem OMA.solution :
    OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H3_R1_H1_R1_H1_R1_H3_R1.H2 := by
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
  · exact solve_0_0_3 N h11 hAlive h107 hm
  · exact solve_0_1_0 N h11 hAlive h107 hm
  · exact checkTree_sound tv_0_1_1 N h11 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact checkTree_sound tv_0_1_2 N h11 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact solve_0_1_3 N h11 hAlive h107 hm
  · exact solve_1_0_0 N h11 hAlive h107 hm
  · exact solve_1_0_1 N h11 hAlive h107 hm
  · exact checkTree_sound tv_1_0_2 N h11 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact solve_1_0_3 N h11 hAlive h107 hm
  · exact solve_1_1_0 N h11 hAlive h107 hm
  · exact solve_1_1_1 N h11 hAlive h107 hm
  · exact checkTree_sound tv_1_1_2 N h11 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact solve_1_1_3 N h11 hAlive h107 hm
